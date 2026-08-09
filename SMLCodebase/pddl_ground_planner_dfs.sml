(* CLI entry point for the DFS-founded pipeline. Foundedness of the datalog
   reachability certificate is discharged by the verified directed-cycle DFS
   (`dl_acyclic_dfs`) rather than the ordered linear scan.

   Usage:
     <bin> plan   <domain.pddl> <problem.pddl> [t_max]
        -- run the verified planner `plan_by_cert_dfs`; prints a VAL-format plan.
     <bin> ground <domain.pddl> <problem.pddl>
        -- run the verified numeric grounder `instantiate_all_actions_dfs`
           (up to, not including, the STRIPS conversion) and print the grounded
           PDDL problem via GroundedPddlPrinter.
     <bin> ground --folded <domain.pddl> <problem.pddl>
        -- run the verified FOLDING grounder `ground_all_actions_dfs_e` instead and
           print the fully ground, purely 0-ary product (folded nullary facts +
           nullary numeric functions).
     <bin> ground --strips <domain.pddl> <problem.pddl>
        -- run the verified STRIPS grounder `ground_strips_all_actions_dfs_e` and
           print the resulting AFP `strips_problem` as a propositional PDDL
           fragment. Numeric-free tasks only (the kernel rejects numeric ones).
           Mutually exclusive with --folded.

   Both oracle outputs (Nemo certificate, SAT assignment) are re-checked inside
   the verified kernel, so a non-error answer is correct by theorem
   (plan_by_cert_dfs_sound / instantiate_all_actions_dfs_eq). *)

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

(* Opt-in phase-timing profiling. Set the GROUND_PROFILE env var to emit a
   machine-greppable per-phase wall-clock breakdown (and coarse checkpoints) to
   stderr; normal runs are silent. Phases are timed via `Prof` (basics.sml): the
   driver brackets parse / nemo (oracle callback) / ground_total / render / write
   here, and the internal check / gcheck / enumerate sub-phases are bracketed
   INSIDE the exported kernel by the verified-transparent `time_it` combinator
   (Grounder_Timing.thy), code-printed to this same `Prof` accumulator. *)
val profOn = Option.isSome (OS.Process.getEnv "GROUND_PROFILE")
val modelSize = ref 0

(* Peak resident memory (VmHWM from /proc/self/status, KiB), sampled at phase
   boundaries. VmHWM is the monotonic high-water mark, so the value at a boundary is
   the whole-process peak up to that point; the harness reads the PROFILE_RSS line
   below into its per-stage RSS columns. Returns 0 if /proc is unavailable. *)
fun vmhwm () : IntInf.int =
  (let
     val ins = TextIO.openIn "/proc/self/status"
     fun loop () =
       case TextIO.inputLine ins of
           NONE => 0
         | SOME l =>
             if String.isPrefix "VmHWM:" l
             then (case String.tokens (fn c => c = #" " orelse c = #"\t" orelse c = #"\n") l of
                     (_ :: num :: _) => (case IntInf.fromString num of SOME v => v | NONE => 0)
                   | _ => 0)
             else loop ()
     val r = loop ()
   in TextIO.closeIn ins; r end)
  handle _ => 0
val rssParse = ref (0 : IntInf.int)
val rssNemo = ref (0 : IntInf.int)
val rssGround = ref (0 : IntInf.int)
fun profMark s = if profOn then eprintln ("CHECKPOINT " ^ s) else ()
fun printProfile () =
  if profOn then
  let
    val g = Prof.ms "ground_total"
    val n = Prof.ms "nemo"
    (* check / gcheck / enumerate are timed INSIDE the verified kernel by the
       transparent `time_it` combinator (Grounder_Timing.thy), accumulated in the
       self-contained GrounderTiming module. *)
    val kt = GrounderTiming.get ()
    fun kget k = case List.find (fn (l, _) => l = k) kt of SOME (_, v) => v | NONE => 0
    fun s l v = l ^ "=" ^ IntInf.toString v ^ "ms"
    val printRss = vmhwm ()
    fun r l v = l ^ "=" ^ IntInf.toString v ^ "kb"
  in
    eprintln (String.concatWith " "
      ["PROFILE", "model=" ^ Int.toString (!modelSize),
       s "parse" (Prof.ms "parse"), s "nemo" n, s "check" (kget "check"),
       s "chk_positive" (kget "chk_positive"), s "chk_rulevalid" (kget "chk_rulevalid"),
       s "chk_closure" (kget "chk_closure"), s "chk_bodyclosed" (kget "chk_bodyclosed"),
       s "chk_acyclic" (kget "chk_acyclic"), s "chk_acyclic_global" (kget "chk_acyclic_global"),
       s "enumerate" (kget "enumerate"),
       s "buildprog" (Prof.ms "buildprog"), s "gcheck" (kget "gcheck"),
       s "emit" (Prof.ms "emit"),
       s "render" (Prof.ms "render"), s "write" (Prof.ms "write"),
       s "ground_total" g]);
    eprintln (String.concatWith " "
      ["PROFILE_RSS", r "parse" (!rssParse), r "nemo" (!rssNemo),
       r "check" (!rssGround), r "print" printRss])
  end
  else ()

(* Which verified foundedness check re-validates the Nemo reachability certificate. *)
datatype checkMode = ChkDFS | ChkTopo

fun doGround mode domFile probFile outOpt =
  let
    val isaProb = Prof.time "parse" (fn () => parseProb domFile probFile)
    val () = rssParse := vmhwm ()
    val timedCertify = (fn prog =>
      Prof.time "nemo" (fn () =>
        let val (m, dc) = NemoDriver.certify prog
        in modelSize := length m;
           rssNemo := vmhwm ();
           profMark ("nemo-done model=" ^ Int.toString (length m));
           (m, dc) end))
    (* Streaming grounders return only the small `canon`-ed reachable-op list (`Inr ops`),
       NOT the fully-built ground-action-schema problem: the schema expansion is folded by
       the printer one action at a time (`problemToStreamOps`), so the ~10^6-action schema
       list is never materialized -- the peak-RSS bottleneck on action-list-bound domains.
       Soundness is `instantiate_all_actions_*_stream_e_sound`: on `Inr ops`, building the
       full problem from `ops` would equal the abstract certified grounding. *)
    val gres = Prof.time "ground_total"
                 (fn () => withNemo (fn () =>
                    (case mode of
                        ChkDFS  => E.instantiate_all_actions_dfs_stream_e
                      | ChkTopo => E.instantiate_all_actions_exec_stream_e)
                       timedCertify isaProb))
    val () = rssGround := vmhwm ()
  in
    (* The verified error-monad grounder returns a specific diagnostic on the left
       (a failing well-formedness check or a rejected reachability certificate) and,
       on the right, exactly the certified reachable-op list. *)
    case gres of
      E.Inl msg =>
        (eprintln ("Grounding rejected by the verified kernel: " ^ msg);
         printProfile ();
         OS.Process.exit OS.Process.failure)
    | E.Inr ops =>
        let val ptp = E.p_T isaProb in
          (Prof.time "render" (fn () =>
             case outOpt of
                 NONE      => GroundedPddlPrinter.problemToStreamOps TextIO.stdOut (ptp, ops)
               | SOME path =>
                   let val out = TextIO.openOut path
                   in GroundedPddlPrinter.problemToStreamOps out (ptp, ops);
                      TextIO.closeOut out;
                      eprintln ("Wrote grounded PDDL to " ^ path)
                   end);
           printProfile ())
        end
  end

(* `ground --folded`: instead of the variable-free instantiation (nullary action
   SCHEMAS whose bodies still mention objects), run the verified FOLDING grounder
   `E.ground_all_actions_*_e`, whose right-hand result is the fully grounded,
   purely 0-ary product -- every predicate folded to a nullary fact (at_p1_G_72)
   and every numeric fluent to a nullary function (fuel_c1_0). The folded problem
   is materialized in full (it is small per action) and printed with the
   non-streaming `GroundedPddlPrinter.problemToStream`. *)
fun doGroundFolded mode domFile probFile outOpt =
  let
    val isaProb = Prof.time "parse" (fn () => parseProb domFile probFile)
    val () = rssParse := vmhwm ()
    val timedCertify = (fn prog =>
      Prof.time "nemo" (fn () =>
        let val (m, dc) = NemoDriver.certify prog
        in modelSize := length m;
           rssNemo := vmhwm ();
           profMark ("nemo-done model=" ^ Int.toString (length m));
           (m, dc) end))
    val gres = Prof.time "ground_total"
                 (fn () => withNemo (fn () =>
                    (case mode of
                        ChkDFS  => E.ground_all_actions_dfs_e
                      | ChkTopo => E.ground_all_actions_exec_e)
                       timedCertify isaProb))
    val () = rssGround := vmhwm ()
  in
    case gres of
      E.Inl msg =>
        (eprintln ("Grounding rejected by the verified kernel: " ^ msg);
         printProfile ();
         OS.Process.exit OS.Process.failure)
    | E.Inr gprob =>
        (Prof.time "render" (fn () =>
           case outOpt of
               NONE      => GroundedPddlPrinter.problemToStream TextIO.stdOut gprob
             | SOME path =>
                 let val out = TextIO.openOut path
                 in GroundedPddlPrinter.problemToStream out gprob;
                    TextIO.closeOut out;
                    eprintln ("Wrote grounded PDDL to " ^ path)
                 end);
         printProfile ())
  end

(* `ground --strips`: run the verified numeric-free STRIPS grounder
   `E.ground_strips_all_actions_*_e`, whose right-hand result is the AFP
   `strips_problem` over string variables (the SAT planner's input format), and
   print it as a purely propositional PDDL fragment. The kernel gates this on the
   task being numeric-free (`strips_fold_checks_exec`), so a task with numeric
   content is REJECTED here rather than silently dropping its numerics. *)
fun doGroundStrips mode domFile probFile outOpt =
  let
    val isaProb = Prof.time "parse" (fn () => parseProb domFile probFile)
    val () = rssParse := vmhwm ()
    val timedCertify = (fn prog =>
      Prof.time "nemo" (fn () =>
        let val (m, dc) = NemoDriver.certify prog
        in modelSize := length m;
           rssNemo := vmhwm ();
           profMark ("nemo-done model=" ^ Int.toString (length m));
           (m, dc) end))
    val gres = Prof.time "ground_total"
                 (fn () => withNemo (fn () =>
                    (case mode of
                        ChkDFS  => E.ground_strips_all_actions_dfs_e
                      | ChkTopo => E.ground_strips_all_actions_exec_e)
                       timedCertify isaProb))
    val () = rssGround := vmhwm ()
  in
    case gres of
      E.Inl msg =>
        (eprintln ("Grounding rejected by the verified kernel: " ^ msg);
         printProfile ();
         OS.Process.exit OS.Process.failure)
    | E.Inr sprob =>
        (Prof.time "render" (fn () =>
           case outOpt of
               NONE      => GroundedPddlPrinter.stripsProblemToStream TextIO.stdOut sprob
             | SOME path =>
                 let val out = TextIO.openOut path
                 in GroundedPddlPrinter.stripsProblemToStream out sprob;
                    TextIO.closeOut out;
                    eprintln ("Wrote grounded STRIPS PDDL to " ^ path)
                 end);
         printProfile ())
  end

fun help () =
  eprintln ("Usage:\n  " ^ CommandLine.name () ^ " plan   <domain.pddl> <problem.pddl> [t_max (default 30)] [out.plan]\n"
            ^ "  " ^ CommandLine.name () ^ " ground [--dfs|--topo] [--folded|--strips] <domain.pddl> <problem.pddl> [out.pddl]\n"
            ^ "    (reachability-certificate foundedness check: --dfs (default) = linear whole-graph\n"
            ^ "     directed-cycle DFS sweep; --topo = ordered linear scan over Nemo's topological order)\n"
            ^ "    (--folded: print the FULLY GROUND 0-ary product -- folded nullary predicates and\n"
            ^ "     nullary numeric functions -- instead of the variable-free instantiation)\n"
            ^ "    (--strips: print the verified STRIPS problem (numeric-free tasks only);\n"
            ^ "     mutually exclusive with --folded)")

fun withTMax t k =
  case Int.fromString t of SOME tMax => k tMax | NONE => (help (); OS.Process.exit OS.Process.failure)

(* `ground` argument parsing: the `--`-prefixed words are options (order-insensitive,
   and independent of where they sit relative to the positional arguments), the rest are
   the positional <domain> <problem> [out]. `--dfs|--topo` select the foundedness
   check (last one wins, default --dfs); `--folded` switches to the fully-ground 0-ary
   product and `--strips` to the verified STRIPS problem. `--folded` and `--strips`
   are mutually exclusive (each may repeat, but they may not be combined); any
   unrecognised option is a usage error. *)
datatype outShape = ShVarfree | ShFolded | ShStrips

fun doGroundArgs args =
  let
    val (flags, positional) = List.partition (String.isPrefix "--") args
    (* the output shape is set at most once to a non-default value: a second,
       DIFFERENT shape flag (--folded together with --strips) is a usage error. *)
    fun setShape (ShVarfree, s) = SOME s
      | setShape (ShFolded, ShFolded) = SOME ShFolded
      | setShape (ShStrips, ShStrips) = SOME ShStrips
      | setShape _ = NONE
    fun opts acc [] = SOME acc
      | opts (_, sh) ("--dfs" :: r)  = opts (ChkDFS, sh) r
      | opts (_, sh) ("--topo" :: r) = opts (ChkTopo, sh) r
      | opts (mode, sh) ("--folded" :: r) =
          (case setShape (sh, ShFolded) of SOME sh' => opts (mode, sh') r | NONE => NONE)
      | opts (mode, sh) ("--strips" :: r) =
          (case setShape (sh, ShStrips) of SOME sh' => opts (mode, sh') r | NONE => NONE)
      | opts _ _ = NONE
    fun run (mode, ShVarfree) = doGround mode
      | run (mode, ShFolded)  = doGroundFolded mode
      | run (mode, ShStrips)  = doGroundStrips mode
  in
    case (opts (ChkDFS, ShVarfree) flags, positional) of
        (SOME cfg, [d, p])      => run cfg d p NONE
      | (SOME cfg, [d, p, out]) => run cfg d p (SOME out)
      | _ => (help (); OS.Process.exit OS.Process.failure)
  end

val _ =
  case CommandLine.arguments () of
    ["plan", d, p]         => doPlan d p 30 NONE
  | ["plan", d, p, t]      => withTMax t (fn tMax => doPlan d p tMax NONE)
  | ["plan", d, p, t, out] => withTMax t (fn tMax => doPlan d p tMax (SOME out))
  | ("ground" :: rest)     => doGroundArgs rest
  | _                      => (help (); OS.Process.exit OS.Process.failure)

val _ = OS.Process.exit OS.Process.success
