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

      val reqs = ":strips :typing :negative-preconditions"
                 ^ (case funcs of [] => "" | _ => " :numeric-fluents")
      val firstAction = ref true
    in
      w "(define (domain grounded)\n";
      w ("  (:requirements " ^ reqs ^ ")\n");
      w ("  (:predicates " ^ String.concatWith " " (map predDeclStr preds) ^ ")\n");
      (case funcs of
           [] => ()
         | _  => w ("  (:functions " ^ String.concatWith " " (map funcDeclStr funcs) ^ ")\n"));
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
      val E.Domain (_, preds, funcs, _, _) = dom
      fun w s = TextIO.output (out, s)

      (* distinct object names, first-occurrence order, via a hash set *)
      val seen : unit StringHashTable.table = StringHashTable.table 4096
      val ord  = ref ([] : string list)
      fun addObj s =
        if StringHashTable.member seen s then ()
        else (StringHashTable.insert seen s (); ord := s :: !ord)
      val _ = List.app addObj (List.concat (map (fmlaObjs objElem) init))
      val _ = List.app addObj (fmlaObjs objElem goal)

      val reqs = ":strips :typing :negative-preconditions"
                 ^ (case funcs of [] => "" | _ => " :numeric-fluents")
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
      (case funcs of
           [] => ()
         | _  => w ("  (:functions " ^ String.concatWith " " (map funcDeclStr funcs) ^ ")\n"));
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
end
