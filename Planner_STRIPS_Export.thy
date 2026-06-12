theory Planner_STRIPS_Export
  imports Planner_STRIPS_Executable
begin

section \<open>SML code export of the executable planner\<close>

text \<open>Pattern: Formal-PDDL-Semantics \<open>Classical_Planning/Classical_PDDL_Checker_Explicit_Export.thy\<close>
  (paired with the \<open>export_files\<close> clause in \<open>./ROOT\<close>; regenerate with
  \<open>isabelle build -e -d . Tree_Decomp_Grounding\<close>, or \<open>make export\<close> in \<open>SMLCodebase/\<close>).
  Exported names: the planner entry points, the oracle-interface datatypes (\<open>dl_program\<close> over the
  AFP \<open>Stratified_Datalog\<close> clause syntax, plus \<open>certificate\<close>, consumed and produced by
  \<open>SMLCodebase/nemo_driver.sml\<close>), the integer/string bridges, and the classical subset of the
  PDDL AST constructors needed by the parser glue (\<open>SMLCodebase/pddl_to_isabelle.sml\<close>).
  \<open>id.Var\<close>/\<open>variable.Var\<close> are spelled type-qualified: the AFP \<open>Datalog.id\<close> constructor shadows
  the Formal-PDDL-Semantics \<open>variable\<close> constructor of the same name.\<close>

export_code
  plan_by_cert ground_via_cert' ground_via_cert dl_program_of sat_solve_strips
  reconstruct_plan_by_cert
  DLProgram dl_clauses dl_consts
  Cls id.Var id.Cst Eql Neql PosLit NegLit
  Cert CNode cert_facts nodes cn_fact cn_preds
  nat_of_integer integer_of_nat int_of_integer integer_of_int Inl Inr
  Rat.Fract Rat.of_int rat_of_digits_pair
  String.explode String.implode
  PNE ConstantExpr AddExpr SubExpr MulExpr DivExpr FunctionExpr
  predAtm eqAtm predicate Pred Func Either variable.Var Obj PredDecl FuncDecl BigAnd BigOr
  formula.Not formula.Bot
  Effect NumericEffect
  Assign ScaleUp ScaleDown Increase Decrease
  SimpleActionSchema ActionHead SimpleActionBody
  Domain Problem SimplePlanAction
  term.CONST term.VAR
  \<comment> \<open>temporal/continuous constructors: not used by the planner, but the reused
      Formal-PDDL-Semantics parser (\<open>pddl_refactor.sml\<close>) parses full PDDL and
      mentions them; the classical glue then keeps only the classical fragment\<close>
  At_Start At_End Over_All
  ContinuousIncrease ContinuousDecrease ContinuousEffect
  DurationConstraint LEQ EQ GEQ
  map_atom map_numeric_effect map_ast_continuous_effect map_numeric_expression map_ast_domain
  in SML
  module_name PDDL_SAT_Planner_Exported
  file "SMLCodebase/code/PDDL_SAT_Planner_Exported.sml"

end
