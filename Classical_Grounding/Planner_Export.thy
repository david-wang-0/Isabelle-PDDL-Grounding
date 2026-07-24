theory Planner_Export
  imports
    Planner_STRIPS_Executable
    Grounding_Pipeline_Numeric_Executable
begin

section \<open>SML code export (default): DFS-founded planner + numeric grounder\<close>

text \<open>\<^bold>\<open>The default SML export of the session\<close> (the only active \<open>export_files\<close> in \<open>./ROOT\<close>): the
  \<^emph>\<open>STRIPS\<close> DFS planner \<^const>\<open>plan_by_cert_dfs\<close> (for the SAT-based planner) and the \<^emph>\<open>numeric\<close> DFS
  error-monad grounder \<^const>\<open>ground_via_cert_numeric_dfs_e\<close> (for the grounded-PDDL printer),
  foundedness in both discharged by the verified directed-cycle DFS \<^const>\<open>dl_acyclic_dfs\<close> rather than
  the ordered linear scan. This drags the graph-library RBT / \<^const>\<open>find_dircycle\<close> code into the
  export alongside the PDDL planner code. Regenerate with \<open>isabelle build -e Classical_Grounding\<close> (the
  graph library and this repo are registered components, so no \<open>-d\<close> flags). This is the \<^bold>\<open>single code
  export\<close> of the development --- the SAT planner, both (propositional + numeric) error-monad grounders,
  and the plan reconstructors, all in one \<open>.sml\<close> file; the non-DFS planner \<^const>\<open>plan_by_cert\<close>
  remains proven but is not exported.\<close>

export_code
  plan_by_cert_dfs ground_via_cert'_dfs ground_via_cert_dfs
  ground_via_cert_numeric_dfs_e ground_via_cert_numeric_exec_e ground_via_cert_numeric_gdfs_e
  ground_via_cert_numeric_dfs_stream_e ground_via_cert_numeric_exec_stream_e ground_via_cert_numeric_gdfs_stream_e
  ast_classical_problem.P\<^sub>T cert_ops_of_exec_fast canon ast_classical_problem.numeric_ground_ac
  distinct_strings_lit grounder.op_names
  ground_via_cert_prop_dfs_e
  dl_program_of sat_solve_strips
  reconstruct_plan_by_cert reconstruct_plan_by_cert_numeric
  dl_acyclic_dfs dl_certified_model_dfs dl_acyclic_dfs_global dl_certified_model_gdfs
  formula.Atom formula.And
  DLProgram dl_clauses dl_consts
  Cls id.Var id.Cst Eql Neql PosLit NegLit
  DLCert DLRule gr_head gr_body
  nat_of_integer integer_of_nat int_of_integer integer_of_int Inl Inr
  Rat.Fract Rat.of_int rat_of_digits_pair Rat.quotient_of
  String.explode String.implode
  PNE ConstantExpr AddExpr SubExpr MulExpr DivExpr FunctionExpr
  predAtm eqAtm predicate Pred Func Either variable.Var Obj PredDecl FuncDecl BigAnd BigOr
  formula.Not formula.Bot
  Effect NumericEffect
  Assign ScaleUp ScaleDown Increase Decrease
  SimpleActionSchema ActionHead SimpleActionBody
  Domain Problem SimplePlanAction
  term.CONST term.VAR
  At_Start At_End Over_All
  ContinuousIncrease ContinuousDecrease ContinuousEffect
  DurationConstraint LEQ EQ GEQ
  map_atom map_numeric_effect map_ast_continuous_effect map_numeric_expression map_ast_domain
  in SML
  module_name PDDL_SAT_Planner_DFS_Exported
  file "../SMLCodebase/code/PDDL_SAT_Planner_DFS_Exported.sml"

end
