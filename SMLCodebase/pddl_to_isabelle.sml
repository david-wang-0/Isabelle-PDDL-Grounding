(* Parsed-PDDL -> exported-Isabelle conversion for the SAT-based planner.

   Adapted from Formal-PDDL-Semantics codeBase/planning/pddlParser/
   pddl_validate_plan_classical.sml: builds an `ast_classical_problem`
   (`Problem (Domain types preds funcs consts actions, objs, init, goal)`)
   from the parser output, for consumption by the exported `plan_by_cert`.
   Constructor names target the PDDL_SAT_Planner_Exported module (via the
   Continuous_PDDL_Checker_Exported alias in planner_alias.sml). *)
open PDDL

  val IsabelleStringImplode = fn s => s;
  val IsabelleStringExplode = fn s => s;
  val SMLCharImplode = String.implode;
  val SMLCharExplode = String.explode;

  val stringToIsabelle = fn s => s
  fun stringListToIsabelle ss = ss

  (* FPS `variable` constructor: exported as Vara (the AFP Datalog id
     constructor Var claims the unsuffixed name) *)
  fun pddlVarToIsabelle (v:PDDL_VAR) = Vara (IsabelleStringExplode (pddl_var_name v))

  fun pddlObjConsToIsabelle (oc:PDDL_OBJ_CONS) =
    case oc of
    PDDL_OBJ_CONS n => Obj (stringToIsabelle n)

  fun pddlTermToIsabelle term =
    case term of VAR_TERM v => VAR (pddlVarToIsabelle v)
             | OBJ_CONS_TERM oc => CONST (pddlObjConsToIsabelle oc)

  fun pddlVarTermToIsabelle term =
    case term of VAR_TERM v => pddlVarToIsabelle v
             | _ => exit_fail ("Var expected, but object found: pddlVarTermToIsabelle " ^ (pddlObjConsTermToString term))

  fun pddlObjConsTermToIsabelle term =
    case term of OBJ_CONS_TERM v => pddlObjConsToIsabelle v
             | _ => exit_fail ("Object expected, but variable found: pddlObjConsTermToIsabelle " ^ (pddlVarTermToString term))

  fun pddlTypeToIsabelle (type_ :PDDL_TYPE) = Either (stringListToIsabelle (map pddl_prim_type_name type_))

  fun mk_pair x y = (x,y)

  fun type_str_cat_fun (l:string list list) = (String.concatWith ", ") (map (String.concatWith ", ") l)

  fun pddlTypedListVarsTypesToIsabelle (typedList :PDDL_VAR PDDL_TYPED_LIST) =
     (pddlTypedListXTypesConv typedList List.concat mk_pair pddlVarToIsabelle pddlTypeToIsabelle)

  fun pddlTypedListObjsConsTypesToIsabelle (typedList :PDDL_OBJ_CONS PDDL_TYPED_LIST) =
     (pddlTypedListXTypesConv typedList List.concat mk_pair pddlObjConsToIsabelle pddlTypeToIsabelle)

  fun pddlTypedListTypesToIsabelle (typedList :'a PDDL_TYPED_LIST) =
                            map (fn (vars, type_) =>
                                     (map (fn _ => (pddlTypeToIsabelle type_)) vars))
                                 typedList;

  fun extractFlatTypedListIsabelle typedList =
                 extractFlatTypedList List.concat stringToIsabelle mk_pair typedList

  fun pddlTypesDefToIsabelle (typesDefOPT :PDDL_TYPES_DEF) =
                   case typesDefOPT of
                        SOME typesDef =>
                             (extractFlatTypedListIsabelle typesDef)
                      | _ => []


  fun pddlConstsDefToIsabelle (constsDefOPT :PDDL_CONSTS_DEF) =
                   case constsDefOPT of
                        SOME constsDef =>
                             pddlTypedListObjsConsTypesToIsabelle constsDef
                      | _ => []

  fun pddlPredToIsabelle (pred, args) = PredDecl (Pred (stringToIsabelle (pddl_pred_name pred)), List.concat (pddlTypedListTypesToIsabelle args))

  fun pddlFunToIsabelle ((func, args),()) = FuncDecl (func, List.concat (pddlTypedListTypesToIsabelle args))

  fun pddlPredDefToIsabelle pred_defOPT =
                   case pred_defOPT of
                        SOME pred_def => (map pddlPredToIsabelle pred_def)
                        | _ => []

  fun pddlFunDefToIsabelle fun_defOPT =
                   case fun_defOPT of
                        SOME fun_def => (map pddlFunToIsabelle fun_def)
                        | _ => []

  fun pddlFormulaToASTPropIsabelle atom_fn phi =
      case phi of Prop_atom(atom : PDDL_TERM PDDL_ATOM) =>  Atom (map_atom atom_fn atom)
                 | Prop_not(prop: PDDL_TERM PDDL_PROP) =>  Not (pddlFormulaToASTPropIsabelle atom_fn prop)
                 | Prop_and(propList: PDDL_TERM PDDL_PROP list) => bigAnd (map (pddlFormulaToASTPropIsabelle atom_fn) propList)
                 | Prop_or(propList: PDDL_TERM PDDL_PROP list) => bigOr (map (pddlFormulaToASTPropIsabelle atom_fn) propList)
                 | Prop_imply(a, b) => Imp (pddlFormulaToASTPropIsabelle atom_fn a, pddlFormulaToASTPropIsabelle atom_fn b)
                 | _ => Bot

  fun pddlFormulaToASTPropIsabelleTerm phi = pddlFormulaToASTPropIsabelle pddlTermToIsabelle phi

  fun pddlFormulaToASTPropIsabelleObj phi = pddlFormulaToASTPropIsabelle pddlObjConsTermToIsabelle phi

  fun pddlPreGDToIsabelle PreGD =
      case PreGD of SOME (prop: PDDL_TERM PDDL_PROP) => pddlFormulaToASTPropIsabelleTerm prop
                 | _ => Not Bot

  fun strToVarAtom atom = map_atom (fn x => pddlTermToIsabelle x) atom

  fun logicOrNumericEffectToASTEffIsabelle eff =
      case eff of LOGIC_EFFECT (Prop_atom atom) => ([Atom (strToVarAtom atom)], [], [])
                 | LOGIC_EFFECT (Prop_not (Prop_atom atom)) => ([], [Atom (strToVarAtom atom)], [])
                 | NUMERIC_EFFECT e => ([], [], [map_numeric_effect pddlTermToIsabelle e])
                 | _ => ([], [], [])

  fun flatten_effects nil = Effect ([], [], [])
  |   flatten_effects (Effect (adds, dels, numerics) :: effs) =
    (let val (Effect (adds', dels', numerics')) = flatten_effects effs
     in Effect (adds @ adds', dels @ dels', numerics @ numerics')
     end)

  fun actDefBodyPreToIsabelle pre = case pre of SOME (u, pre: PDDL_PRE_GD) => pddlPreGDToIsabelle pre
                                            | _ => Not Bot
  fun actDefBodyEffToIsabelle effs = case effs of SOME (the_effs) => flatten_effects (map (Effect o logicOrNumericEffectToASTEffIsabelle) the_effs)
                                                  | _ => Effect ([], [], [])

  fun pddlIsabelleActName actName = SMLCharImplode (map (fn c => if c = #"-" then #"_" else c) (SMLCharExplode actName))

  (* Build classical action schemas from the parsed PDDL. *)
  fun pddlActToClassicalIsabelle (actName, (args, defBody: PDDL_ACTION_DEF_BODY)) =
    case defBody of
      Simple_Action_Def_Body (pre, eff) =>
        SimpleActionSchema(ActionHead(IsabelleStringExplode actName,
          pddlTypedListVarsTypesToIsabelle args),
          SimpleActionBody(actDefBodyPreToIsabelle pre,
          actDefBodyEffToIsabelle eff))
    | Durative_Action_Def_Body _ =>
        raise Fail "Durative actions not supported by the classical validator."


  fun pddlClassicalActionsDefToIsabelle (actsDef : PDDL_ACTION list) = (map pddlActToClassicalIsabelle actsDef)

  fun pddlClassicalDomToIsabelle (reqs:PDDL_REQUIRE_DEF,
                         (types_def,
                            (consts_def,
                               (pred_def,
                                   (fun_def,
                                       (actions_def,
                                          constraints_def))))))
                      = Domain
                        ((pddlTypesDefToIsabelle types_def),
                         (pddlPredDefToIsabelle pred_def),
                         (pddlFunDefToIsabelle fun_def),
                         (pddlConstsDefToIsabelle consts_def),
                         (pddlClassicalActionsDefToIsabelle actions_def))


  fun objDefToIsabelle (objs:PDDL_OBJ_DEF) = pddlTypedListObjsConsTypesToIsabelle objs


  fun initElToIsabelle (init_el:PDDL_INIT_EL) = pddlFormulaToASTPropIsabelleObj (pddl_prop_map OBJ_CONS_TERM init_el)

  fun pddlInitToIsabelle (init:PDDL_INIT) objs = (map initElToIsabelle init)


  fun pddlGoalToIsabelle (goal:PDDL_GOAL) = pddlFormulaToASTPropIsabelleObj goal

  fun pddlProbToIsabelle (reqs:PDDL_REQUIRE_DEF,
                          (objs:PDDL_OBJ_DEF,
                              (init:PDDL_INIT,
                                (goal_form:PDDL_GOAL,
                                   metric)))) =
                                   (objDefToIsabelle objs,
                                    (pddlInitToIsabelle init (List.concat (map #1 objs))),
                                    pddlGoalToIsabelle goal_form)



  fun classicalPlanActionToIsabelle ((act_name, args), tdur_opt) =
      case tdur_opt of
        SOME _ => exit_fail ("Durative plan action found in classical plan: " ^ act_name)
      | NONE => SimplePlanAction(stringToIsabelle act_name, map pddlObjConsToIsabelle args)

  fun classicalPlanToIsabelle plan = map classicalPlanActionToIsabelle plan

fun readFile file =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.openIn file
in
    next_String stream
end

fun parse_wrapper parser file =
  case (CharParser.parseString parser (readFile file ^ "#eof#")) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

val parse_pddl_dom = parse_wrapper (PDDL.end_of_file PDDL.domain)
val parse_pddl_prob = parse_wrapper (PDDL.end_of_file PDDL.problem)
val parse_pddl_plan = parse_wrapper (PDDL.end_of_file PDDL.classical_plan)
