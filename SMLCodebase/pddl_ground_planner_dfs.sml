(* CLI entry point for the DFS-founded pipeline. Foundedness of the datalog
   reachability certificate is discharged by the verified directed-cycle DFS
   (`dl_acyclic_dfs`) rather than the ordered linear scan.

   Usage:
     <bin> plan   <domain.pddl> <problem.pddl> [t_max]
        -- run the verified planner `plan_by_cert_dfs`; prints a VAL-format plan.
     <bin> ground <domain.pddl> <problem.pddl>
        -- run the verified numeric grounder `ground_via_cert_numeric_dfs`
           (up to, not including, the STRIPS conversion) and print the grounded
           PDDL problem via GroundedPddlPrinter.

   Both oracle outputs (Nemo certificate, SAT assignment) are re-checked inside
   the verified kernel, so a non-error answer is correct by theorem
   (plan_by_cert_dfs_sound / ground_via_cert_numeric_dfs_eq). *)

structure E = PDDL_SAT_Planner_Exported

fun eprintln s = TextIO.output (TextIO.stdErr, s ^ "\n")

fun planActionStr pa =
  case pa of
    E.SimplePlanAction (n, args) =>
      "(" ^ n ^ String.concat (map (fn E.Obj ob => " " ^ ob) args) ^ ")"

val useBuiltin = ExternalSat.backend () = "builtin"
val solveRaw = if useBuiltin then SatSolver.solveOrEmpty else ExternalSat.solve
fun g cnf =
  map E.Int_of_integer (solveRaw (map (map E.integer_of_int) cnf))

fun parseProb domFile probFile =
  let
    val parsedDom = parse_pddl_dom domFile
    val parsedProb = parse_pddl_prob probFile
  in
    E.Problem
      (let val (p1, p2, p3) = pddlProbToIsabelle parsedProb in
         (pddlClassicalDomToIsabelle parsedDom, p1, p2, p3) end)
  end

fun withNemo thunk =
  thunk () handle NemoDriver.NemoError m =>
    (eprintln ("Nemo driver error: " ^ m); OS.Process.exit OS.Process.failure)

fun doPlan domFile probFile tMax outOpt =
  let
    val () = eprintln ("SAT oracle: " ^
               (if useBuiltin then "builtin DPLL" else ExternalSat.backend ()))
    val isaProb = parseProb domFile probFile
  in
    case withNemo (fn () =>
           E.plan_by_cert_dfs NemoDriver.certify g
             (E.nat_of_integer (IntInf.fromInt tMax)) isaProb) of
      NONE =>
        (eprintln ("No plan found within horizon " ^ Int.toString tMax ^
                   " (or the input/certificate was rejected by the kernel)");
         OS.Process.exit OS.Process.failure)
    | SOME pas =>
        (* VAL/IPC plan format: one action per line, `(name obj ...)`. The plan is of the
           ORIGINAL problem (plan_by_cert_dfs_sound), so the names are the user's action/object
           names -- valid identifiers, no sanitisation needed. *)
        let val planStr = String.concat (map (fn a => planActionStr a ^ "\n") pas)
        in case outOpt of
               NONE      => print planStr
             | SOME path =>
                 let val out = TextIO.openOut path
                 in TextIO.output (out, planStr); TextIO.closeOut out;
                    eprintln ("Wrote plan to " ^ path)
                 end
        end
  end

fun doGround domFile probFile outOpt =
  let
    val isaProb = parseProb domFile probFile
  in
    (* The verified error-monad grounder returns a specific diagnostic on the left
       (a failing well-formedness check or a rejected reachability certificate) and,
       on the right, exactly the certified grounding (`ground_via_cert_numeric_dfs_e_sound`). *)
    case withNemo (fn () => E.ground_via_cert_numeric_dfs_e NemoDriver.certify isaProb) of
      E.Inl msg =>
        (eprintln ("Grounding rejected by the verified kernel: " ^ msg);
         OS.Process.exit OS.Process.failure)
    | E.Inr gp =>
        let val pddl = GroundedPddlPrinter.problemToString gp
        in case outOpt of
               NONE      => print pddl
             | SOME path =>
                 let val out = TextIO.openOut path
                 in TextIO.output (out, pddl); TextIO.closeOut out;
                    eprintln ("Wrote grounded PDDL to " ^ path)
                 end
        end
  end

fun help () =
  eprintln ("Usage:\n  " ^ CommandLine.name () ^ " plan   <domain.pddl> <problem.pddl> [t_max (default 30)] [out.plan]\n"
            ^ "  " ^ CommandLine.name () ^ " ground <domain.pddl> <problem.pddl> [out.pddl]")

fun withTMax t k =
  case Int.fromString t of SOME tMax => k tMax | NONE => (help (); OS.Process.exit OS.Process.failure)

val _ =
  case CommandLine.arguments () of
    ["plan", d, p]         => doPlan d p 30 NONE
  | ["plan", d, p, t]      => withTMax t (fn tMax => doPlan d p tMax NONE)
  | ["plan", d, p, t, out] => withTMax t (fn tMax => doPlan d p tMax (SOME out))
  | ["ground", d, p]       => doGround d p NONE
  | ["ground", d, p, out]  => doGround d p (SOME out)
  | _                      => (help (); OS.Process.exit OS.Process.failure)

val _ = OS.Process.exit OS.Process.success
