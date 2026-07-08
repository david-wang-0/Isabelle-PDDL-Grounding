(* Pretty-printer for the grounded PDDL problem produced by the verified numeric
   grounder `ground_via_cert_numeric_dfs` (the numeric-pipeline output, before the
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
  val problemToString :
    PDDL_SAT_Planner_Exported.ast_classical_action_schema
      PDDL_SAT_Planner_Exported.ast_problem -> string
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
  fun dedup xs =
    let fun go ([], _, acc) = List.rev acc
          | go (x :: rest, seen, acc) =
              if List.exists (fn y => y = x) seen then go (rest, seen, acc)
              else go (rest, x :: seen, x :: acc)
    in go (xs, [], []) end

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

  fun domainStr (E.Domain (_, preds, funcs, _, actions)) =
    let val reqs = ":strips :typing :negative-preconditions"
                   ^ (case funcs of [] => "" | _ => " :numeric-fluents")
    in
      "(define (domain grounded)\n"
      ^ "  (:requirements " ^ reqs ^ ")\n"
      ^ "  (:predicates " ^ String.concatWith " " (map predDeclStr preds) ^ ")\n"
      ^ (case funcs of
             [] => ""
           | _  => "  (:functions " ^ String.concatWith " " (map funcDeclStr funcs) ^ ")\n")
      ^ "\n"
      ^ String.concatWith "\n" (map actionStr actions) ^ "\n)\n"
    end

  fun problemToString (E.Problem (dom, _, init, goal)) =
    let val E.Domain (_, _, _, _, actions) = dom
        val objNames =
          map pddlName (dedup (List.concat (map (fmlaObjs objElem) init)
                               @ fmlaObjs objElem goal
                               @ List.concat (map actionObjs actions)))
        val objectsDecl =
          case objNames of
              [] => ""
            | _  => "  (:objects " ^ String.concatWith " " objNames ^ " - object)\n"
    in
      domainStr dom ^ "\n"
      ^ "(define (problem grounded-inst)\n"
      ^ "  (:domain grounded)\n"
      ^ objectsDecl
      ^ "  (:init " ^ String.concatWith " " (map (fmlaStr objName) init) ^ ")\n"
      ^ "  (:goal " ^ fmlaStr objName goal ^ "))\n"
    end
end
