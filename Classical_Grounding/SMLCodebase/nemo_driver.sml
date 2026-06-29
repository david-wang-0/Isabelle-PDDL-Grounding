(* Nemo reachability oracle `f : dl_program -> certificate`.

   This is the *untrusted* oracle handed to the exported `plan_by_cert`:
   1. serialize the dl_program to a Nemo datalog program (nemo_tmp/prog.rls),
      with injectively mangled predicate/object names (p<i> / c<i>) and a
      `dom` guard predicate making every rule safe (mirroring the HOL closure
      semantics, where every clause parameter ranges over all object names);
   2. run `nmo` once with IDB export to enumerate the derived model, and once
      with proof tracing on every derived fact;
   3. parse the trace into an ordered certificate (`Cert [CNode ...]`):
      all initial facts first (no predecessors), then the traced inferences
      topologically sorted, with `dom` premises stripped so each node's body
      is exactly the instantiated predicate preconditions of its rule.

   Any bug or format mismatch here fails *closed*: the verified kernel
   re-checks the certificate (`admissible_exec` + `grounding_checks_exec`)
   and `plan_by_cert` returns NONE rather than an unsound grounding.

   References: WIP_nemo_certificate_format.md, the Lean CertifyingDatalog
   reference checker, and its Examples/*/inputCreatorNemo.py. *)

structure NemoDriver :
sig
  exception NemoError of string
  (* reachability oracle: returns the candidate model M (a fact list) together with the
     generic datalog certificate dc, in derivation (topological) order. *)
  val certify : PDDL_SAT_Planner_Exported.dl_program ->
                (PDDL_SAT_Planner_Exported.predicate * PDDL_SAT_Planner_Exported.object list) list
                * (PDDL_SAT_Planner_Exported.predicate, PDDL_SAT_Planner_Exported.object)
                    PDDL_SAT_Planner_Exported.dl_certificate
end =
struct
  structure E = PDDL_SAT_Planner_Exported
  structure J = JsonParse

  exception NemoError of string

  val nmoBin = case OS.Process.getEnv "NMO" of SOME p => p | NONE => "nmo"
  val tmpDir = "nemo_tmp"

  (* ---------- tiny mutable string<->int dictionary ---------- *)
  type dict = (string * int) list ref * int ref
  fun newDict () : dict = (ref [], ref 0)
  fun lookupAdd ((entries, next) : dict) (s : string) : int =
    case List.find (fn (s', _) => s' = s) (!entries) of
      SOME (_, i) => i
    | NONE => let val i = !next in entries := (s, i) :: !entries; next := i + 1; i end
  fun lookupInv ((entries, _) : dict) (i : int) : string =
    case List.find (fn (_, i') => i' = i) (!entries) of
      SOME (s, _) => s
    | NONE => raise NemoError ("unknown mangled index: " ^ Int.toString i)

  (* ---------- mangled serialization ---------- *)
  (* 0-ary predicates get a reserved dummy argument `z` so that every Nemo
     predicate has arity >= 1 (avoids `p().` syntax concerns); stripped on
     the way back. *)

  fun objName (E.Obj s) = s

  fun mangleObj objDict ob = "c" ^ Int.toString (lookupAdd objDict (objName ob))
  fun manglePred predDict (E.Pred s) = "p" ^ Int.toString (lookupAdd predDict s)

  (* canonical mangled atom string, also used as trace-matching key *)
  fun atomStr predDict objDict (p, args) =
    let val args' = case args of [] => ["z"] | _ => List.map (mangleObj objDict) args
    in manglePred predDict p ^ "(" ^ String.concatWith "," args' ^ ")" end

  (* ---------- AFP Stratified_Datalog clause syntax ----------
     dl_program_of (Grounding_Pipeline_Executable.thy) hands us
     `E.Cls (p, head_ids, body)` clauses: body literals are `E.PosLit`
     (positive precondition atoms) and `E.Eql`/`E.Neql` filters (the
     `satisfies_cond` translation already dropped trivially-true literals and
     statically-false clauses; `E.NegLit` is never emitted).  Initial facts
     are the bodyless ground clauses.  id constructors: `E.Var` is the AFP
     `Datalog.id.Var` (carrying an FPS variable `E.Vara s` -- the FPS
     constructor got the mangled name), `E.Cst` carries an object. *)

  (* per-clause variable numbering, keyed by variable name *)
  fun idStr objDict varDict i =
    case i of
      E.Cst ob => mangleObj objDict ob
    | E.Var (E.Vara v) => "?v" ^ Int.toString (lookupAdd varDict v)

  fun idsStr objDict varDict ids =
    case ids of [] => ["z"] | _ => List.map (idStr objDict varDict) ids

  fun litStr predDict objDict varDict (p, ids) =
    manglePred predDict p ^ "(" ^ String.concatWith "," (idsStr objDict varDict ids) ^ ")"

  fun isGroundIds ids = List.all (fn E.Cst _ => true | _ => false) ids
  fun isFact (E.Cls (_, ids, [])) = isGroundIds ids
    | isFact _ = false

  fun factAtom (E.Cls (p, ids, _)) =
    (p, List.map (fn E.Cst ob => ob
                   | _ => raise NemoError "non-ground initial fact") ids)

  (* ---------- file/process helpers ---------- *)
  fun writeFile (path, content) =
    let val out = TextIO.openOut path
    in TextIO.output (out, content); TextIO.closeOut out end

  fun readFile path =
    let val ins = TextIO.openIn path
        val s = TextIO.inputAll ins
    in TextIO.closeIn ins; s end

  fun run cmd =
    if OS.Process.isSuccess (OS.Process.system cmd) then ()
    else raise NemoError ("command failed: " ^ cmd)

  fun ensureDir d = if OS.FileSys.access (d, []) then () else OS.FileSys.mkDir d

  fun listDir d =
    let
      val ds = OS.FileSys.openDir d
      fun go acc = case OS.FileSys.readDir ds of
                     SOME f => go (f :: acc)
                   | NONE => (OS.FileSys.closeDir ds; acc)
    in go [] end

  (* ---------- atom-string parsing (mangled names) ---------- *)
  (* "p3(c1,c2)" -> (3, [1, 2]); "p3(z)" -> (3, []) *)
  fun parseAtomStr (s : string) : int * int list =
    let
      val s = String.implode (List.filter (fn c => c <> #" " andalso c <> #"\"") (String.explode s))
      val (pname, rest) =
        case String.fields (fn c => c = #"(") s of
          [p, r] => (p, r)
        | _ => raise NemoError ("malformed atom: " ^ s)
      val rest = case String.fields (fn c => c = #")") rest of
                   r :: _ => r
                 | _ => raise NemoError ("malformed atom: " ^ s)
      fun stripPrefix (pre, str) =
        if String.isPrefix pre str then String.extract (str, String.size pre, NONE)
        else raise NemoError ("unexpected name (missing '" ^ pre ^ "' prefix): " ^ str)
      val pid = case Int.fromString (stripPrefix ("p", pname)) of
                  SOME i => i | NONE => raise NemoError ("bad predicate: " ^ pname)
      val argStrs = if rest = "" then [] else String.fields (fn c => c = #",") rest
      val args =
        case argStrs of
          ["z"] => []
        | _ => List.map (fn a => case Int.fromString (stripPrefix ("c", a)) of
                                   SOME i => i | NONE => raise NemoError ("bad constant: " ^ a))
                        argStrs
    in (pid, args) end

  fun atomOfIds predDict objDict (pid, argIds) : (E.object E.atom) E.formula =
    E.Atom (E.PredAtm (E.Pred (lookupInv predDict pid),
                       List.map (fn i => E.Obj (lookupInv objDict i)) argIds))

  fun isDomAtom s = String.isPrefix "dom(" s

  (* ---------- the oracle ---------- *)
  fun certify prog =
    let
      val allClauses = E.dl_clauses prog
      val consts = E.dl_consts prog
      val (factCls, ruleCls) = List.partition isFact allClauses

      val predDict = newDict ()
      val objDict = newDict ()

      (* --- serialize program --- *)
      val domFacts = List.map (fn ob => "dom(" ^ mangleObj objDict ob ^ ") .") consts
      val initStrs = List.map (fn c => atomStr predDict objDict (factAtom c)) factCls
      val initFactLines = List.map (fn s => s ^ " .") initStrs

      fun clauseRule (E.Cls (p, headIds, body)) =
        let
          val varDict = newDict ()
          val headStr = litStr predDict objDict varDict (p, headIds)
          val bodyAtoms =
            List.mapPartial
              (fn E.PosLit (q, ids) => SOME (litStr predDict objDict varDict (q, ids))
                | _ => NONE) body
          val filters =
            List.mapPartial
              (fn E.Eql (a, b) =>
                   SOME (idStr objDict varDict a ^ " = " ^ idStr objDict varDict b)
                | E.Neql (a, b) =>
                   SOME (idStr objDict varDict a ^ " != " ^ idStr objDict varDict b)
                | E.PosLit _ => NONE
                | E.NegLit _ =>
                   raise NemoError "negative body literal (NegLit) unsupported") body
          (* Nemo safety: dom-guard every variable of the clause (head, body
             atoms and filters all render before nVars is read) *)
          val nVars = !(#2 varDict)
          val domGuards = List.tabulate (nVars, fn i => "dom(?v" ^ Int.toString i ^ ")")
          val bodyStr = String.concatWith ", " (bodyAtoms @ domGuards @ filters)
        in headStr ^ " :- " ^ bodyStr ^ " ." end
      val ruleLines = List.map clauseRule ruleCls

      val () = ensureDir tmpDir
      val progPath = tmpDir ^ "/prog.rls"
      val () = writeFile (progPath,
                 String.concatWith "\n" (domFacts @ initFactLines @ ruleLines) ^ "\n")

      (* --- run 1: enumerate the derived model (IDB export) --- *)
      val resultsDir = tmpDir ^ "/results"
      val () = run (nmoBin ^ " -e idb -D " ^ resultsDir ^ " -o " ^ progPath ^ " > /dev/null 2>&1")

      fun modelAtomsOfFile fname =
        let
          val pname = hd (String.fields (fn c => c = #".") fname)
        in
          if String.isPrefix "p" pname then
            List.mapPartial
              (fn line =>
                 let val l = String.implode
                               (List.filter (fn c => c <> #"\r" andalso c <> #"\"")
                                            (String.explode line))
                 in if l = "" then NONE else SOME (pname ^ "(" ^ l ^ ")") end)
              (String.fields (fn c => c = #"\n") (readFile (resultsDir ^ "/" ^ fname)))
          else []   (* dom or anything else *)
        end
      val modelStrs =
        if OS.FileSys.access (resultsDir, []) then
          List.concat (List.map modelAtomsOfFile (listDir resultsDir))
        else []

      (* trace goals: derived facts not already initial *)
      fun mem (x, xs) = List.exists (fn y => y = x) xs
      val goalStrs = List.filter (fn a => not (mem (a, initStrs))) modelStrs

      (* --- run 2: trace --- *)
      val inferences =
        if List.null goalStrs then []
        else
          let
            val goalPath = tmpDir ^ "/traceGoal.txt"
            val tracePath = tmpDir ^ "/trace.json"
            val () = writeFile (goalPath, String.concatWith ";" goalStrs)
            val () = run (nmoBin ^ " --trace-input-file " ^ goalPath ^
                          " --trace-output " ^ tracePath ^ " " ^ progPath ^ " > /dev/null 2>&1")
            val trace = J.parse (readFile tracePath)
            val infs = case J.getField (trace, "inferences") of
                         SOME a => J.getArr a
                       | NONE => raise NemoError "trace JSON has no 'inferences'"
            fun infOf j =
              let
                val concl = case J.getField (j, "conclusion") of
                              SOME s => J.getStr s
                            | NONE => raise NemoError "inference without conclusion"
                val prems = case J.getField (j, "premises") of
                              SOME a => List.map J.getStr (J.getArr a)
                            | NONE => []
                fun norm s = String.implode
                               (List.filter (fn c => c <> #" " andalso c <> #"\"")
                                            (String.explode s))
              in (norm concl, List.map norm prems) end
          in List.map infOf infs end

      (* --- build the ordered certificate --- *)
      (* nodes in reverse order; index keyed by canonical mangled atom string *)
      val nodes = ref ([] : ((E.object E.atom) E.formula * int list) list)
      val nNodes = ref 0
      val index = ref ([] : (string * int) list)
      fun indexed s = List.find (fn (s', _) => s' = s) (!index)
      fun addNode (key, fact, preds) =
        (nodes := (fact, preds) :: !nodes;
         index := (key, !nNodes) :: !index;
         nNodes := !nNodes + 1)

      (* all initial facts first (closure_check needs every init' fact present) *)
      val () =
        List.app
          (fn s => case indexed s of
                     SOME _ => ()
                   | NONE => addNode (s, atomOfIds predDict objDict (parseAtomStr s), []))
          initStrs

      (* topological insertion of traced inferences, dom premises stripped *)
      val pending = ref (List.filter (fn (c, _) => not (isDomAtom c)) inferences)
      fun pass () =
        let
          val (placed, rest) =
            List.partition
              (fn (concl, prems) =>
                 case indexed concl of
                   SOME _ => true   (* duplicate: drop *)
                 | NONE =>
                     List.all (fn p => isDomAtom p orelse Option.isSome (indexed p)) prems)
              (!pending)
          val () =
            List.app
              (fn (concl, prems) =>
                 case indexed concl of
                   SOME _ => ()
                 | NONE =>
                     addNode (concl, atomOfIds predDict objDict (parseAtomStr concl),
                              List.mapPartial
                                (fn p => if isDomAtom p then NONE
                                         else Option.map #2 (indexed p))
                                prems))
              placed
        in
          pending := rest;
          if List.null placed orelse List.null rest then () else pass ()
        end
      val () = pass ()
      val () =
        if List.null (!pending) then ()
        else TextIO.output (TextIO.stdErr,
               "nemo_driver: warning: " ^ Int.toString (length (!pending)) ^
               " unplaceable trace inferences dropped (kernel will fail closed if this matters)\n")
    in
      (* Emit the generic (M, dc) pair: M is the derived fact list, dc = DLCert of one DLRule
         per node (head fact + the body facts at its predecessor indices), in topological order.
         Each node fact is a ground predicate atom Atom (PredAtm (p, args)) -> dl_fact (p, args). *)
      let
        fun toFact (E.Atom (E.PredAtm (p, args))) = (p, args)
          | toFact _ = raise NemoError "certificate node is not a ground predicate atom"
        val fwd = List.rev (!nodes)          (* (fact_formula, pred_indices), position = node index *)
        val facts = List.map (fn (f, _) => toFact f) fwd
        val factVec = Vector.fromList facts
        val rules =
          List.map
            (fn (f, ps) => E.DLRule (toFact f, List.map (fn i => Vector.sub (factVec, i)) ps))
            fwd
      in
        (facts, E.DLCert rules)
      end
    end
end
