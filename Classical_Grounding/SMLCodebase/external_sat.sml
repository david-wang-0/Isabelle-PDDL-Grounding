(* External SAT oracle `g`: DIMACS printer + driver for any solver speaking the
   SAT-competition output format ("s SATISFIABLE" / "v <lits> 0" lines, or
   "s UNSATISFIABLE"). Verified by z3 (default; already DIMACS-capable), and
   the same format is spoken by kissat, cadical, cryptominisat5, glucose, ...
   (minisat is NOT supported: it uses a different file-based output format).

   Select the solver with the SAT_SOLVER environment variable:
     SAT_SOLVER="z3"                      (default)
     SAT_SOLVER="cryptominisat5 --verb 0"
     SAT_SOLVER="kissat -q"
     SAT_SOLVER="builtin"                 (the hand-written DPLL in
                                           sat_solver.sml -- intended only for
                                           the toy running example)

   Like the Nemo reachability oracle, this solver is UNTRUSTED: its assignment
   is re-checked by the executable model check inside the verified
   `try_horizon`, so a wrong answer can only lose completeness, never
   soundness. UNSAT (or any parse failure) returns [], which simply fails the
   model check and moves the horizon loop on. *)

structure ExternalSat :
sig
  (* the command being used (for the CLI banner) *)
  val backend : unit -> string
  (* g : DIMACS clauses -> assignment literals ([] on UNSAT/failure) *)
  val solve : IntInf.int list list -> IntInf.int list
end =
struct
  val tmpDir = "sat_tmp"

  fun backend () =
    case OS.Process.getEnv "SAT_SOLVER" of SOME c => c | NONE => "z3"

  fun ensureDir d = if OS.FileSys.access (d, []) then () else OS.FileSys.mkDir d

  (* ---------- DIMACS printer ---------- *)
  fun dimacsString (clauses : IntInf.int list list) : string =
    let
      val nVars =
        List.foldl (fn (c, m) =>
            List.foldl (fn (l, m') => IntInf.max (IntInf.abs l, m')) m c)
          (IntInf.fromInt 0) clauses
      fun litStr l =
        if l < 0 then "-" ^ IntInf.toString (IntInf.~ l) else IntInf.toString l
      val header =
        "p cnf " ^ IntInf.toString nVars ^ " " ^ Int.toString (length clauses) ^ "\n"
      val body =
        List.map (fn c => String.concatWith " " (List.map litStr c) ^ " 0\n") clauses
    in
      String.concat (header :: body)
    end

  (* ---------- solver output parser (SAT-competition format) ---------- *)
  fun parseOutput (out : string) : IntInf.int list =
    let
      val lines = String.fields (fn c => c = #"\n") out
      fun isS pre l = String.isPrefix pre l
      val sat = List.exists (isS "s SATISFIABLE") lines
      val unsat = List.exists (isS "s UNSATISFIABLE") lines
      fun vLits l =
        if isS "v " l orelse l = "v" then
          List.mapPartial IntInf.fromString
            (String.tokens (fn c => c = #" " orelse c = #"\r")
                           (String.extract (l, 1, NONE)))
        else []
    in
      if sat then
        List.filter (fn l => l <> IntInf.fromInt 0) (List.concat (List.map vLits lines))
      else if unsat then []
      else (TextIO.output (TextIO.stdErr,
              "external_sat: no 's' status line in solver output; treating as UNSAT\n");
            [])
    end

  (* ---------- driver ---------- *)
  fun writeFile (path, content) =
    let val out = TextIO.openOut path
    in TextIO.output (out, content); TextIO.closeOut out end

  fun readFile path =
    let val ins = TextIO.openIn path
        val s = TextIO.inputAll ins
    in TextIO.closeIn ins; s end

  fun solve clauses =
    let
      val () = ensureDir tmpDir
      val cnfPath = tmpDir ^ "/problem.cnf"
      val outPath = tmpDir ^ "/solver_out.txt"
      val () = writeFile (cnfPath, dimacsString clauses)
      (* SAT solvers exit 10 (SAT) / 20 (UNSAT) by convention, so the exit
         status is deliberately ignored; the output is what matters. *)
      val _ = OS.Process.system
                (backend () ^ " " ^ cnfPath ^ " > " ^ outPath ^ " 2>/dev/null")
    in
      parseOutput (readFile outPath)
    end
end
