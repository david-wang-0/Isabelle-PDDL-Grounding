(* Verified SAT-based PDDL planner -- CLI entry point.

   Usage: pddl_sat_planner <domain.pddl> <problem.pddl> [t_max]

   Parses a classical PDDL domain + problem (parser reused from
   Formal-PDDL-Semantics), builds the Isabelle `ast_classical_problem`, and
   calls the exported, *verified* `plan_by_cert` with two untrusted oracles:
     f = NemoDriver.certify     (reachability certificate via nmo)
     g = SatSolver.solveOrEmpty (naive DPLL over the DIMACS CNF)
   Both oracle outputs are re-checked inside the verified kernel
   (plan_by_cert_sound, Planner_Executable.thy), so a SOME result is a valid
   plan of the *original* problem by theorem.

   On success the plan is printed one action per line in VAL format
   ("(name arg1 ... argk)"), so it can be re-checked by the
   Formal-PDDL-Semantics classical plan validator. *)

structure E = PDDL_SAT_Planner_Exported

fun planActionStr pa =
  case pa of
    E.SimplePlanAction (n, args) =>
      "(" ^ n ^ String.concat (List.map (fn E.Obj ob => " " ^ ob) args) ^ ")"

(* SAT oracle: an external DIMACS solver by default (see external_sat.sml;
   select with SAT_SOLVER, default "z3"); SAT_SOLVER=builtin picks the
   hand-written DPLL in sat_solver.sml, which is only meant for the toy
   running example. Either way the assignment is re-checked by the verified
   model check, so the oracle is untrusted. *)
val useBuiltin = ExternalSat.backend () = "builtin"
val solveRaw = if useBuiltin then SatSolver.solveOrEmpty else ExternalSat.solve
fun g cnf =
  List.map E.Int_of_integer
    (solveRaw (List.map (List.map E.integer_of_int) cnf))

fun plan domFile probFile tMax =
  let
    val () = TextIO.output (TextIO.stdErr,
               "SAT oracle: " ^
               (if useBuiltin then "builtin DPLL (sat_solver.sml)"
                else ExternalSat.backend ()) ^ "\n")
    val parsedDom = parse_pddl_dom domFile
    val parsedProb = parse_pddl_prob probFile
    val isaProb =
      E.Problem
        (let val (p1, p2, p3) = pddlProbToIsabelle parsedProb in
           (pddlClassicalDomToIsabelle parsedDom, p1, p2, p3) end)
  in
    case (E.plan_by_cert NemoDriver.certify g
            (E.nat_of_integer (IntInf.fromInt tMax)) isaProb
          handle NemoDriver.NemoError m =>
            (println ("Nemo driver error: " ^ m);
             OS.Process.exit OS.Process.failure)) of
      NONE =>
        (println ("No plan found within horizon " ^ Int.toString tMax ^
                  " (or the input/certificate was rejected by the kernel)");
         OS.Process.exit OS.Process.failure)
    | SOME pas => List.app (println o planActionStr) pas
  end

fun print_help () =
  println ("Usage: " ^ CommandLine.name () ^ " <domain.pddl> <problem.pddl> [t_max (default 30)]")

val _ =
  case CommandLine.arguments () of
    [d, p] => plan d p 30
  | [d, p, t] =>
      (case Int.fromString t of
         SOME tMax => plan d p tMax
       | NONE => (print_help (); OS.Process.exit OS.Process.failure))
  | _ => (print_help (); OS.Process.exit OS.Process.failure)

val _ = OS.Process.exit OS.Process.success
