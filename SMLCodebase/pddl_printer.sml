(* Pretty-printer for the grounded PDDL problem produced by the verified numeric
   grounder `instantiate_all_actions_dfs` (the numeric-pipeline output, before the
   STRIPS conversion). Emits *syntactically valid* PDDL (domain + problem) that
   round-trips through a standard PDDL parser.

   The numeric-fluent-retaining grounder keeps each reachable operator's real
   (object-carrying) atoms and numeric structure: grounded actions are nullary
   *schemas* (:parameters ()) whose bodies mention the instantiation's objects
   directly (promoted to constants), rather than being propositionalised into
   nullary predicates. Because the grounder retains numerics, numeric function
   declarations, numeric comparison atoms (`(>= (fuel c) 1)`), and numeric effects
   (`(decrease (fuel c) 1)`) are printed when present.

   Validity fixes over a raw AST dump: identifiers are made letter-initial (the
   grounder's `______`-prefixed synthetic names + the integer action indices are
   sanitized); a `(:requirements ...)` line is emitted; the problem gets an
   `(:objects ...)` block collected from the grounded bodies; preconditions are
   flattened and the trivially-true `(not false)` (= `¬⊥`) conjuncts are dropped. *)
structure GroundedPddlPrinter :> sig
  (* Stream the grounded PDDL straight to an outstream, so the (up to ~10^6-action)
     output is never held as one string; object de-duplication is a hash set, not the
     former O(n^2) list scan. Output is byte-identical to the former `problemToString`. *)
  val problemToStream :
    TextIO.outstream ->
    PDDL_SAT_Planner_Exported.ast_classical_action_schema
      PDDL_SAT_Planner_Exported.ast_problem -> unit
  (* Memory-optimized streaming variant: instead of a fully-built grounded problem,
     take the normalized problem `ptp` (= P_T of the input) plus the small materialized
     ops list, and expand + emit each ground action schema one at a time
     (`E.varfree_inst_ac ptp op name`), so only a single schema is ever live. The
     emitted bytes are IDENTICAL to `problemToStream` on the fully-built problem. *)
  val problemToStreamOps :
    TextIO.outstream ->
    PDDL_SAT_Planner_Exported.ast_classical_action_schema
      PDDL_SAT_Planner_Exported.ast_problem
      * PDDL_SAT_Planner_Exported.ast_classical_plan_action list -> unit
  (* `ground --strips`: print the verified AFP STRIPS problem (the output of
     `E.ground_strips_all_actions_*_e`) as a purely propositional PDDL fragment --
     one nullary predicate per STRIPS variable, one nullary `(:action ...)` per
     STRIPS operator. *)
  val stripsProblemToStream :
    TextIO.outstream ->
    (string, unit) PDDL_SAT_Planner_Exported.strips_problem_ext -> unit
end = struct
  structure E = PDDL_SAT_Planner_Exported

  (* Make any identifier a valid, letter-initial PDDL name: strip the grounder's
     leading-underscore namespace guard (______type_object -> type_object,
     __..._Defined_fuel -> Defined_fuel, _..._Goal -> Goal); prefix digit-initial
     names (grounded action indices 0,1,... -> op_0, op_1, ...). Injective on the
     grounded task's symbols, so no fresh collisions are introduced. *)
  fun pddlName s =
    let fun drop (#"_" :: cs) = drop cs
          | drop cs = cs
    in case drop (String.explode s) of
           []      => "sym"
         | (c::cs) => if Char.isAlpha c then String.implode (c :: cs)
                      else "op_" ^ String.implode (c :: cs)
    end

  fun predName (E.Pred s) = pddlName s
  fun funcName (E.Func s) = pddlName s
  fun objName  (E.Obj s)  = pddlName s
  fun varName  (E.Vara s) = s
  fun termStr (E.VAR v)    = "?" ^ varName v
    | termStr (E.CONST ob) = objName ob

  fun typeStr (E.Either [t]) = pddlName t
    | typeStr (E.Either ts)  = "(either " ^ String.concatWith " " (map pddlName ts) ^ ")"

  (* numeric expressions over element type ['a] *)
  fun pneStr elemStr (E.PNE (f, []))   = "(" ^ funcName f ^ ")"
    | pneStr elemStr (E.PNE (f, args)) =
        "(" ^ funcName f ^ " " ^ String.concatWith " " (map elemStr args) ^ ")"

  (* print a rat constant: an integer when the denominator is 1, else n/d.
     `quotient_of` gives the normalised (num, den) with den > 0 and gcd 1. *)
  fun ratStr r =
    let val (num, den) = E.quotient_of r
        val n = E.integer_of_int num
        val d = E.integer_of_int den
    in if d = 1 then IntInf.toString n
       else IntInf.toString n ^ "/" ^ IntInf.toString d
    end

  fun numExprStr elemStr e =
    case e of
        E.ConstantExpr r  => ratStr r
      | E.DurationExpr    => "?duration"
      | E.AddExpr (a, b)  => "(+ " ^ numExprStr elemStr a ^ " " ^ numExprStr elemStr b ^ ")"
      | E.SubExpr (a, b)  => "(- " ^ numExprStr elemStr a ^ " " ^ numExprStr elemStr b ^ ")"
      | E.MulExpr (a, b)  => "(* " ^ numExprStr elemStr a ^ " " ^ numExprStr elemStr b ^ ")"
      | E.DivExpr (a, b)  => "(/ " ^ numExprStr elemStr a ^ " " ^ numExprStr elemStr b ^ ")"
      | E.FunctionExpr p  => pneStr elemStr p
      | _                 => "#numexpr"

  fun atomStr elemStr a =
    let val ne = numExprStr elemStr
    in case a of
        E.PredAtm (p, [])   => "(" ^ predName p ^ ")"
      | E.PredAtm (p, args) => "(" ^ predName p ^ " "
                                    ^ String.concatWith " " (map elemStr args) ^ ")"
      | E.EqAtm (x, y)      => "(= " ^ elemStr x ^ " " ^ elemStr y ^ ")"
      | E.NumericEqAtm (l, r)      => "(= "  ^ ne l ^ " " ^ ne r ^ ")"
      | E.NumericLessAtm (l, r)    => "(< "  ^ ne l ^ " " ^ ne r ^ ")"
      | E.NumericLEAtm (l, r)      => "(<= " ^ ne l ^ " " ^ ne r ^ ")"
      | E.NumericGreaterAtm (l, r) => "(> "  ^ ne l ^ " " ^ ne r ^ ")"
      | E.NumericGEAtm (l, r)      => "(>= " ^ ne l ^ " " ^ ne r ^ ")"
    end

  fun fmlaStr elemStr f =
    case f of
        E.Atom a     => atomStr elemStr a
      | E.Bot        => "false"
      | E.Not g      => "(not " ^ fmlaStr elemStr g ^ ")"
      | E.And (g, h) => "(and " ^ fmlaStr elemStr g ^ " " ^ fmlaStr elemStr h ^ ")"
      | E.Or  (g, h) => "(or "  ^ fmlaStr elemStr g ^ " " ^ fmlaStr elemStr h ^ ")"
      | E.Imp (g, h) => "(imply " ^ fmlaStr elemStr g ^ " " ^ fmlaStr elemStr h ^ ")"

  fun sigStr []  = ""
    | sigStr tys = " " ^ String.concatWith " "
                          (List.tabulate (length tys,
                             fn i => "?a" ^ Int.toString i ^ " - " ^ typeStr (List.nth (tys, i))))

  fun predDeclStr (E.PredDecl (p, tys)) = "(" ^ predName p ^ sigStr tys ^ ")"
  fun funcDeclStr (E.FuncDecl (f, tys)) = "(" ^ funcName f ^ sigStr tys ^ ")"

  fun numEffOp E.Assigna   = "assign"
    | numEffOp E.Increase  = "increase"
    | numEffOp E.Decrease  = "decrease"
    | numEffOp E.ScaleUp   = "scale-up"
    | numEffOp E.ScaleDown = "scale-down"

  fun numEffStr elemStr (E.NumericEffect (op0, lhs, rhs)) =
    "(" ^ numEffOp op0 ^ " " ^ pneStr elemStr lhs ^ " " ^ numExprStr elemStr rhs ^ ")"

  fun effectStr (E.Effect (adds, dels, numeffs)) =
    let val a = map (fmlaStr termStr) adds
        val d = map (fn f => "(not " ^ fmlaStr termStr f ^ ")") dels
        val n = map (numEffStr termStr) numeffs
    in case a @ d @ n of
           []  => "()"
         | [x] => x
         | xs  => "(and " ^ String.concatWith " " xs ^ ")"
    end

  (* precondition helpers: flatten nested `and` into a conjunct list and drop the
     trivially-true `(not false)` (= ¬⊥) conjuncts the grounding leaves behind. *)
  fun conjuncts (E.And (g, h)) = conjuncts g @ conjuncts h
    | conjuncts f = [f]
  fun isTrivial (E.Not E.Bot) = true
    | isTrivial _ = false

  (* --- numeric-content detection -----------------------------------------
     A grounded task is *numeric-free* when nothing it prints mentions a numeric
     fluent: no numeric comparison/equality atom anywhere in the init, the goal or
     an action precondition/effect condition, and no numeric effect. For such a
     task the `:numeric-fluents` requirement and the whole `(:functions ...)`
     section are noise (the declared functions, if any, are unreachable dead
     declarations), so both are suppressed.

     The test is deliberately a *narrowing* of the former `funcs <> []` test
     (`showNumerics` below conjoins the two): it can only ever REMOVE the
     numeric requirement/section relative to the previous behaviour, never add
     one -- which is what keeps the classical benchmarks byte-identical. *)
  fun atomIsNum (E.PredAtm _) = false
    | atomIsNum (E.EqAtm _)   = false
    | atomIsNum _             = true            (* the five Numeric*Atm forms *)
  fun fmlaHasNum f =
    case f of
        E.Atom a     => atomIsNum a
      | E.Bot        => false
      | E.Not g      => fmlaHasNum g
      | E.And (g, h) => fmlaHasNum g orelse fmlaHasNum h
      | E.Or  (g, h) => fmlaHasNum g orelse fmlaHasNum h
      | E.Imp (g, h) => fmlaHasNum g orelse fmlaHasNum h
  fun effHasNum (E.Effect (adds, dels, neffs)) =
        null neffs = false
        orelse List.exists fmlaHasNum adds orelse List.exists fmlaHasNum dels
  fun actionHasNum (E.SimpleActionSchema (_, E.SimpleActionBody (pre, eff))) =
        fmlaHasNum pre orelse effHasNum eff
  (* numeric content of the whole task: init assignments, goal, action bodies *)
  fun taskHasNum (init, goal, actions) =
        List.exists fmlaHasNum init orelse fmlaHasNum goal
        orelse List.exists actionHasNum actions
  (* print the `:numeric-fluents` requirement + `(:functions ...)` section? *)
  fun showNumerics (funcs, hasNum) = (null funcs = false) andalso hasNum

  (* Collect every Obj name mentioned in the grounded task, for the problem's
     (:objects ...) block. `elemObjs` adapts to the element type: `objElem` for the
     object-typed world facts (init/goal), `trmElem` for the term-typed action bodies. *)
  fun exprObjs elemObjs e =
    case e of
        E.FunctionExpr (E.PNE (_, args)) => List.concat (map elemObjs args)
      | E.AddExpr (a, b) => exprObjs elemObjs a @ exprObjs elemObjs b
      | E.SubExpr (a, b) => exprObjs elemObjs a @ exprObjs elemObjs b
      | E.MulExpr (a, b) => exprObjs elemObjs a @ exprObjs elemObjs b
      | E.DivExpr (a, b) => exprObjs elemObjs a @ exprObjs elemObjs b
      | _ => []
  fun atomObjs elemObjs a =
    case a of
        E.PredAtm (_, args)        => List.concat (map elemObjs args)
      | E.EqAtm (x, y)             => elemObjs x @ elemObjs y
      | E.NumericEqAtm (l, r)      => exprObjs elemObjs l @ exprObjs elemObjs r
      | E.NumericLessAtm (l, r)    => exprObjs elemObjs l @ exprObjs elemObjs r
      | E.NumericLEAtm (l, r)      => exprObjs elemObjs l @ exprObjs elemObjs r
      | E.NumericGreaterAtm (l, r) => exprObjs elemObjs l @ exprObjs elemObjs r
      | E.NumericGEAtm (l, r)      => exprObjs elemObjs l @ exprObjs elemObjs r
  fun fmlaObjs elemObjs f =
    case f of
        E.Atom a     => atomObjs elemObjs a
      | E.Bot        => []
      | E.Not g      => fmlaObjs elemObjs g
      | E.And (g, h) => fmlaObjs elemObjs g @ fmlaObjs elemObjs h
      | E.Or  (g, h) => fmlaObjs elemObjs g @ fmlaObjs elemObjs h
      | E.Imp (g, h) => fmlaObjs elemObjs g @ fmlaObjs elemObjs h
  fun numEffObjs elemObjs (E.NumericEffect (_, E.PNE (_, args), rhs)) =
        List.concat (map elemObjs args) @ exprObjs elemObjs rhs
  fun effObjs elemObjs (E.Effect (adds, dels, neffs)) =
        List.concat (map (fmlaObjs elemObjs) adds)
      @ List.concat (map (fmlaObjs elemObjs) dels)
      @ List.concat (map (numEffObjs elemObjs) neffs)
  fun objElem (E.Obj s) = [s]
  fun trmElem (E.CONST (E.Obj s)) = [s]
    | trmElem (E.VAR _)           = []
  fun actionObjs (E.SimpleActionSchema (_, E.SimpleActionBody (pre, eff))) =
        fmlaObjs trmElem pre @ effObjs trmElem eff
  fun actionStr (E.SimpleActionSchema
                   (E.ActionHead (name, params), E.SimpleActionBody (pre, eff))) =
    let val preLine =
          case List.filter (fn c => isTrivial c = false) (conjuncts pre) of
              []  => ""                                   (* empty precondition -> omit *)
            | [x] => "     :precondition " ^ fmlaStr termStr x ^ "\n"
            | xs  => "     :precondition (and "
                       ^ String.concatWith " " (map (fmlaStr termStr) xs) ^ ")\n"
    in
      "  (:action " ^ pddlName name ^ "\n"
      ^ "     :parameters (" ^ String.concatWith " " (map (fn (v,_) => "?" ^ varName v) params) ^ ")\n"
      ^ preLine
      ^ "     :effect " ^ effectStr eff ^ ")"
    end

  (* Stream domain + problem straight to `out`. The domain's actions (the bulk of the
     output) are written one at a time, so only a single action string is ever live;
     object names are collected into a hash set as we go (first-occurrence order kept
     in `ord`). The emitted bytes are identical to the former `domainStr`/`problemToString`
     pair: actions separated by "\n" then "\n)\n"; objects in first-occurrence order
     (init, goal, then action bodies). *)
  fun problemToStream out (E.Problem (dom, _, init, goal)) =
    let
      val E.Domain (_, preds, funcs, _, actions) = dom
      fun w s = TextIO.output (out, s)

      (* distinct object names, first-occurrence order, via a hash set *)
      val seen : unit StringHashTable.table = StringHashTable.table 4096
      val ord  = ref ([] : string list)
      fun addObj s =
        if StringHashTable.member seen s then ()
        else (StringHashTable.insert seen s (); ord := s :: !ord)
      val _ = List.app addObj (List.concat (map (fmlaObjs objElem) init))
      val _ = List.app addObj (fmlaObjs objElem goal)

      (* Numeric-freeness is decided over the fully-built grounded task. *)
      val numerics = showNumerics (funcs, taskHasNum (init, goal, actions))
      val reqs = ":strips :typing :negative-preconditions"
                 ^ (if numerics then " :numeric-fluents" else "")
      val firstAction = ref true
    in
      w "(define (domain grounded)\n";
      w ("  (:requirements " ^ reqs ^ ")\n");
      w ("  (:predicates " ^ String.concatWith " " (map predDeclStr preds) ^ ")\n");
      (if numerics
       then w ("  (:functions " ^ String.concatWith " " (map funcDeclStr funcs) ^ ")\n")
       else ());
      w "\n";
      (* actions joined by "\n" (concatWith semantics), accumulating their objects *)
      List.app (fn a =>
        ((if !firstAction then firstAction := false else w "\n");
         w (actionStr a);
         List.app addObj (actionObjs a))) actions;
      w "\n)\n";

      w "\n(define (problem grounded-inst)\n";
      w "  (:domain grounded)\n";
      (case List.rev (!ord) of
           []    => ()
         | names => w ("  (:objects " ^ String.concatWith " " (map pddlName names) ^ " - object)\n"));
      w ("  (:init " ^ String.concatWith " " (map (fmlaStr objName) init) ^ ")\n");
      w ("  (:goal " ^ fmlaStr objName goal ^ "))\n")
    end

  (* Streaming twin of `problemToStream` that never materializes the ground-action
     list. `ptp` is the normalized problem (= P_T of the input): its domain carries the
     grounded task's predicates/functions and its problem part the init/goal (the built
     grounded problem copies exactly these). `ops` is the small `canon`-ed reachable-op
     list; each op expands to a schema via `E.varfree_inst_ac ptp op name`, printed and
     dropped one at a time. Action names are the verified `E.op_names ops` (readable
     `<schema>_<args>_<index>`). Header, objects (init/goal then per-action, first-occurrence order),
     init, and goal are emitted with the identical logic as `problemToStream`, so the
     bytes match the fully-built path exactly. *)
  fun problemToStreamOps out (ptp, ops) =
    let
      val E.Problem (dom, _, init, goal) = ptp
      val E.Domain (_, preds, funcs, _, schemas) = dom
      fun w s = TextIO.output (out, s)

      (* distinct object names, first-occurrence order, via a hash set *)
      val seen : unit StringHashTable.table = StringHashTable.table 4096
      val ord  = ref ([] : string list)
      fun addObj s =
        if StringHashTable.member seen s then ()
        else (StringHashTable.insert seen s (); ord := s :: !ord)
      val _ = List.app addObj (List.concat (map (fmlaObjs objElem) init))
      val _ = List.app addObj (fmlaObjs objElem goal)

      (* Numeric-freeness, decided WITHOUT expanding the ops. `varfree_inst_ac`
         only substitutes objects for the schema's variables, so a ground action
         carries a numeric atom/effect exactly when its SCHEMA does; hence the
         streamed task is numeric-free iff no reachable op instantiates a numeric
         schema (and init/goal are numeric-free). This agrees with the scan
         `problemToStream` does over the fully-built action list, so the two paths
         stay byte-identical. The `null numSchemas` guard short-circuits the ops
         scan in the common (fully numeric-free domain) case. *)
      val numSchemas =
        map (fn E.SimpleActionSchema (E.ActionHead (n, _), _) => n)
            (List.filter actionHasNum schemas)
      fun opIsNum (E.SimplePlanAction (n, _)) = List.exists (fn s => s = n) numSchemas
      val hasNum =
        List.exists fmlaHasNum init orelse fmlaHasNum goal
        orelse ((null numSchemas = false) andalso List.exists opIsNum ops)
      val numerics = showNumerics (funcs, hasNum)
      val reqs = ":strips :typing :negative-preconditions"
                 ^ (if numerics then " :numeric-fluents" else "")
      val firstAction = ref true

      (* Verified readable action names: `E.op_names ops` (the grounder-locale
         `op_names`) = `readable_pa <op> ^ "_" ^ <index>`, one per reachable op. This is
         the SAME function the fully-built domain uses (`varfree_inst_dom` calls
         `op_names ops`), so the streamed bytes match the built path exactly. *)
      val opNames = E.op_names ops
    in
      w "(define (domain grounded)\n";
      w ("  (:requirements " ^ reqs ^ ")\n");
      w ("  (:predicates " ^ String.concatWith " " (map predDeclStr preds) ^ ")\n");
      (if numerics
       then w ("  (:functions " ^ String.concatWith " " (map funcDeclStr funcs) ^ ")\n")
       else ());
      w "\n";
      (* actions joined by "\n", built one at a time from (op, name) and dropped after
         emission; objects accumulated exactly as the built-list path would. *)
      ListPair.app (fn (oper, name) =>
        let val a = E.varfree_inst_ac ptp oper name in
          (if !firstAction then firstAction := false else w "\n");
          w (actionStr a);
          List.app addObj (actionObjs a)
        end) (ops, opNames);
      w "\n)\n";

      w "\n(define (problem grounded-inst)\n";
      w "  (:domain grounded)\n";
      (case List.rev (!ord) of
           []    => ()
         | names => w ("  (:objects " ^ String.concatWith " " (map pddlName names) ^ " - object)\n"));
      w ("  (:init " ^ String.concatWith " " (map (fmlaStr objName) init) ^ ")\n");
      w ("  (:goal " ^ fmlaStr objName goal ^ "))\n")
    end

  (* --- verified STRIPS problem (`ground --strips`) -------------------------
     `E.ground_strips_all_actions_*_e` returns the AFP `strips_problem` over
     STRING variables (the folded nullary fact names, e.g. `at_p1_G_72`). It is
     purely propositional, so the PDDL rendering needs neither types nor objects:
     each variable becomes a nullary predicate, each operator a nullary action.

     STRIPS operators carry NO name field (a `strips_operator` is just the triple
     precondition / add-effects / delete-effects), so actions are named `op_<i>`
     by their position in `operators_of`. That order is exactly the operator order
     of the folded grounded problem (`as_strips` maps the folded action list
     positionwise), so `op_<i>` here denotes the same ground action as the i-th
     `(:action ...)` of `ground --folded` on the same task.

     Operator preconditions are POSITIVE variable lists, so the precondition is a
     plain conjunction of atoms; only the GOAL can carry a negative literal
     (`goal_of v = SOME false`), which is the sole source of the
     `:negative-preconditions` requirement. *)
  fun stripsProblemToStream out prob =
    let
      fun w s = TextIO.output (out, s)
      val vars = E.variables_of prob
      val ops  = E.operators_of prob
      val init = E.initial_of prob
      val goal = E.goal_of prob

      (* The STRIPS conversion (`as_strips`) splits each folded PDDL fact into a
         POSITIVE and a NEGATIVE state variable, named "+" ^ fact / "-" ^ fact,
         plus the two constants v_T = "+" (always true) and v_F = "-" (always
         false). Neither `+` nor a leading `-` is a legal PDDL name, so the sign
         is rendered as a `pos_`/`neg_` prefix (and the two constants spelled
         out). This stays injective on the grounded task's facts, since the
         underlying fact names are already letter-initial and distinct. *)
      fun stripsVarName v =
        case String.explode v of
            [#"+"]      => "always_true"
          | [#"-"]      => "always_false"
          | (#"+" :: cs) => "pos_" ^ pddlName (String.implode cs)
          | (#"-" :: cs) => "neg_" ^ pddlName (String.implode cs)
          | _            => pddlName v
      fun atomOf v = "(" ^ stripsVarName v ^ ")"
      fun negOf v  = "(not " ^ atomOf v ^ ")"
      (* and-list conventions of the grounded printer above: a singleton stays
         bare, a non-singleton is wrapped in `(and ...)`. *)
      fun andList []  = "(and)"
        | andList [x] = x
        | andList xs  = "(and " ^ String.concatWith " " xs ^ ")"

      (* goal literals, in `variables_of` order; NONE = unconstrained *)
      val goalLits = List.mapPartial
                       (fn v => case goal v of
                                    SOME b => SOME (if b then atomOf v else negOf v)
                                  | NONE   => NONE)
                       vars
      val negGoal = List.exists (fn v => goal v = SOME false) vars
      (* closed world: only `SOME true` variables are listed in (:init) *)
      val initVars = List.filter (fn v => init v = SOME true) vars

      val reqs = ":strips" ^ (if negGoal then " :negative-preconditions" else "")

      fun actionStr (i, oper) =
        let
          val pre  = map atomOf (E.precondition_of oper)
          val adds = map atomOf (E.add_effects_of oper)
          val dels = map negOf  (E.delete_effects_of oper)
          val preLine =
            case pre of
                [] => ""                                (* empty precondition -> omit *)
              | xs => "     :precondition " ^ andList xs ^ "\n"
        in
          "  (:action op_" ^ Int.toString i ^ "\n"
          ^ "     :parameters ()\n"
          ^ preLine
          ^ "     :effect " ^ (case adds @ dels of [] => "()" | xs => andList xs) ^ ")"
        end
      val i = ref 0
    in
      w "(define (domain grounded_strips)\n";
      w ("  (:requirements " ^ reqs ^ ")\n");
      w ("  (:predicates " ^ String.concatWith " " (map atomOf vars) ^ ")\n");
      w "\n";
      List.app (fn oper =>
        ((if !i > 0 then w "\n" else ());
         w (actionStr (!i, oper));
         i := !i + 1)) ops;
      w "\n)\n";

      w "\n(define (problem grounded_strips-inst)\n";
      w "  (:domain grounded_strips)\n";
      w ("  (:init " ^ String.concatWith " " (map atomOf initVars) ^ ")\n");
      w ("  (:goal " ^ andList goalLits ^ "))\n")
    end
end
