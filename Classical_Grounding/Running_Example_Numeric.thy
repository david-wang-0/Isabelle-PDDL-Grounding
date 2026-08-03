theory Running_Example_Numeric
  imports Running_Example Grounding_Pipeline_Numeric_Executable
begin

section \<open>A numeric variant of the running example: a \<open>fuel\<close> fluent\<close>

text \<open>The Helmert-2009 running example (\<^theory>\<open>Classical_Grounding.Running_Example\<close>) with a single
  numeric fluent added: each \<open>Car\<close> has a \<open>fuel\<close> function; \<open>drive\<close> now requires \<open>fuel >= 1\<close> and
  \<open>from \<noteq> to\<close> (an \<^const>\<open>eqAtm\<close> inequality guard, translated to a datalog \<open>Neql\<close>) and
  \<open>decrease\<close>s fuel by 1. Everything else is reused verbatim (types, predicates, consts, objects,
  goal, and the other operators). We then thread it through the \<^emph>\<open>same\<close> grounding pipeline and run
  the numeric-fluent-retaining grounder \<^const>\<open>instantiate_all_actions_dfs_e\<close>, stopping \<^emph>\<open>before\<close> the
  STRIPS conversion.

  What the pipeline does to the numerics (Option B --- faithful numeric-\<^emph>\<open>effect\<close> retention):
  definedness translation \<^emph>\<open>keeps\<close> \<open>P\<^sub>T\<close>'s real numerics (the \<open>fuel >= 1\<close> guard and the
  \<open>decrease (fuel ?c) 1\<close> effect) and only adds the propositional \<open>def(fuel, ...)\<close> predicates for the
  datalog. It is the \<^emph>\<open>relaxation\<close> \<open>P\<^sub>R\<close> that is numeric-free: \<open>relax_lit\<close> maps numeric comparison
  atoms to \<open>\<not>\<bottom>\<close>, and \<open>relax_eff\<close>/\<open>relax_prob\<close> drop numeric effects and init assignments. So the
  reachability datalog runs on the numeric-free \<open>P\<^sub>R\<close> (legal), while \<open>P\<^sub>T\<close> \<^emph>\<open>violates\<close>
  \<open>ops_no_num\<close>/\<open>init_props\<close> --- which is why the propositional \<open>grounding_checks_exec\<close> returns
  \<^const>\<open>False\<close> here but the numeric-fluent-retaining \<^const>\<open>numeric_grounding_checks_exec\<close> (the five
  coverage obligations, without the numeric-freeness ones) returns \<^const>\<open>True\<close>. The
  \<^const>\<open>instantiate_all_actions_dfs_e\<close> gate keys on the latter, so the grounder retains the \<open>fuel\<close>
  function declaration \<^emph>\<open>and\<close> the \<open>decrease (fuel c) 1\<close> \<^const>\<open>NumericEffect\<close> on each grounded drive.\<close>

subsection \<open>Domain and problem with the \<open>fuel\<close> fluent\<close>

definition "my_funcs_num \<equiv> [FuncDecl (Func STR ''fuel'') [Either [STR ''Car'']]]"

definition "op_drive_num \<equiv> SimpleActionSchema
  (ActionHead STR ''drive''
    [(variable.Var STR ''c'', Either [STR ''Car'']), (variable.Var STR ''from'', Either [STR ''City'']), (variable.Var STR ''to'', Either [STR ''City''])])
  (SimpleActionBody
    (And (And (And (Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''c''), term.VAR (variable.Var STR ''from'')]))
                   (Atom (numericGEAtm (FunctionExpr (PNE (Func STR ''fuel'') [term.VAR (variable.Var STR ''c'')])) (ConstantExpr 1))))
              (Not (Atom (eqAtm (term.VAR (variable.Var STR ''from'')) (term.VAR (variable.Var STR ''to''))))))
       (Or (Atom (predAtm (Pred STR ''road'') [term.VAR (variable.Var STR ''from''), term.VAR (variable.Var STR ''to'')]))
           (Atom (predAtm (Pred STR ''road'') [term.VAR (variable.Var STR ''to''), term.VAR (variable.Var STR ''from'')]))))
    (Effect
      [Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''c''), term.VAR (variable.Var STR ''to'')])]
      [Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''c''), term.VAR (variable.Var STR ''from'')])]
      [NumericEffect Decrease (PNE (Func STR ''fuel'') [term.VAR (variable.Var STR ''c'')]) (ConstantExpr 1)]))"

definition "my_actions_num \<equiv> [op_drive_num, op_choochoo, op_load, op_unload]"

definition "my_domain_num \<equiv> Domain my_types my_preds my_funcs_num my_consts my_actions_num"

text \<open>The initial fuel values: a function-assignment atom \<open>(= (fuel c) 10)\<close> for each Car.\<close>
definition "my_init_num \<equiv> my_init @ [
  Atom (numericEqAtm (FunctionExpr (PNE (Func STR ''fuel'') [Obj STR ''c1''])) (ConstantExpr 10)),
  Atom (numericEqAtm (FunctionExpr (PNE (Func STR ''fuel'') [Obj STR ''c2''])) (ConstantExpr 10)),
  Atom (numericEqAtm (FunctionExpr (PNE (Func STR ''fuel'') [Obj STR ''c3''])) (ConstantExpr 10))
]"

definition "my_problem_num \<equiv> Problem my_domain_num my_objs my_init_num my_goal"

subsection \<open>Pipeline normalization + reference certificate\<close>

definition "my_P\<^sub>T_num \<equiv> ast_classical_problem.P\<^sub>T my_problem_num"
definition "my_P\<^sub>R_num \<equiv> ast_classical_problem.relax_prob my_P\<^sub>T_num"
definition "my_cert_num \<equiv> naive_cert my_P\<^sub>R_num"
definition "my_dl_rules_num \<equiv> dl_rules my_P\<^sub>R_num"
definition "my_const_names_num \<equiv> ast_classical_problem.const_names my_P\<^sub>R_num"
text \<open>Probes: the normalized problem \<open>P\<^sub>T\<close> (retains the \<open>decrease\<close> effect + \<open>fuel >= 1\<close> guard, plus the
  added \<open>def(fuel,...)\<close> predicates), the self-computed reference certificate, and the re-checks. The
  certificate is accepted (\<^const>\<open>dl_certified_model_dfs\<close> holds on the numeric-free \<open>P\<^sub>R\<close>); the
  \<^emph>\<open>propositional\<close> re-check \<^const>\<open>grounding_checks_exec\<close> is \<^const>\<open>False\<close> (its \<open>ops_no_num\<close>/\<open>init_props\<close>
  conjuncts fail on \<open>P\<^sub>T\<close>'s retained numerics), while the numeric-fluent-retaining re-check
  \<^const>\<open>numeric_grounding_checks_exec\<close> is \<^const>\<open>True\<close>.\<close>
value "my_P\<^sub>T_num"
value "my_P\<^sub>R_num"
value "my_cert_num"

text \<open>The datalog program \<open>dl_rules P\<^sub>R\<close> that the certificate is a founded model of. The \<open>drive\<close>
  clauses now carry a \<open>Neql\<close> body guard --- the datalog image of the \<open>from \<noteq> to\<close> inequality (the
  \<open>eqAtm\<close> literal translated by \<open>dl_cond_rh\<close>), alongside the positive \<open>road\<close>/type body atoms.\<close>
value "my_dl_rules_num"
value "dl_certified_model_dfs my_dl_rules_num my_const_names_num (fst my_cert_num) (snd my_cert_num)"
text \<open>The ordered-scan (topological-order) alternative: same certificate, accepted in
  \<open>O(|rules| \<cdot> |body| \<cdot> |facts|)\<close> instead of the per-vertex DFS's \<open>O(|facts|\<^sup>2)\<close>. Both \<^const>\<open>True\<close>.\<close>
value "dl_certified_model_exec my_dl_rules_num my_const_names_num (fst my_cert_num) (snd my_cert_num)"
text \<open>The fast single-sweep global-visited DFS (\<^const>\<open>dl_acyclic_dfs_global\<close>): one \<open>O(|V|+|E|)\<close>
  pass, again accepting the same certificate. All three foundedness checks agree (\<^const>\<open>True\<close>).\<close>
value "dl_certified_model_gdfs my_dl_rules_num my_const_names_num (fst my_cert_num) (snd my_cert_num)"
value "grounding_checks_exec my_P\<^sub>T_num (fst my_cert_num)"
value "numeric_grounding_checks_exec my_P\<^sub>T_num (fst my_cert_num)"

subsection \<open>Numeric grounding, retaining the fuel fluent (before STRIPS)\<close>

text \<open>The error-monad fluent grounder returns \<^const>\<open>Inr\<close> of the grounded (pre-STRIPS) PDDL problem
  whose nullary \<open>drive\<close> schemas retain the real \<open>decrease (fuel c) 1\<close> \<^const>\<open>NumericEffect\<close> and the
  \<open>fuel >= 1\<close> guard, over the certified reachable ops (a failing check would give \<^const>\<open>Inl\<close> of a
  diagnostic string instead).\<close>
definition "my_grounded_num \<equiv> instantiate_all_actions_dfs_e (\<lambda>_. my_cert_num) my_problem_num"
value "my_grounded_num"

text \<open>The grounded (pre-STRIPS) action schemas themselves: each is nullary (empty parameters) and
  retains the real numeric \<open>fuel >= 1\<close> guard, the \<open>from \<noteq> to\<close> inequality, and the
  \<open>decrease (fuel c) 1\<close> \<^const>\<open>NumericEffect\<close>. \<^const>\<open>map_sum\<close> projects the \<^const>\<open>Inr\<close> grounded
  problem to its action list (an \<^const>\<open>Inl\<close> diagnostic would pass through unchanged).\<close>
value "map_sum id (\<lambda>P. actions (domain P)) my_grounded_num"

subsection \<open>The two-stage grounding path, concretely\<close>

text \<open>The propositional grounder factors into the two pipeline stages
  (\<^theory>\<open>Classical_Grounded_PDDL.Classical_Grounded_PDDL_Factorization\<close>,
  theorem \<open>ground_prob_factors\<close>): first the Variable_Freeness stage
  \<^const>\<open>varfree.varfree_inst_prob\<close> instantiates every certified-reachable op into a
  \<^emph>\<open>nullary schema\<close> (parameters gone, but the ground atoms and the \<open>fuel(c)\<close> numerics still
  there), then the fact folder \<^const>\<open>fact_folder.fold_prob\<close> collapses the ground atoms onto fresh
  nullary predicates and the ground fluents onto fresh nullary functions. The numeric grounder run
  above is \<^emph>\<open>exactly\<close> stage one; composing stage two on top of it reproduces the one-shot
  propositional \<^const>\<open>ground_by_cert\<close>. Both stages consume the same certified data as the pipeline
  entry points: the ops list \<^term>\<open>canon (cert_ops_of_exec_fast N M)\<close> and the fact list
  \<^term>\<open>cert_facts_of_exec N M\<close>.\<close>

definition "my_cert_facts \<equiv> cert_facts_of_exec my_P\<^sub>T_num (fst my_cert_num)"
definition "my_cert_ops \<equiv> canon (cert_ops_of_exec_fast my_P\<^sub>T_num (fst my_cert_num))"
definition "my_fluents \<equiv> grounder.fluents my_P\<^sub>T_num my_cert_ops"
definition "my_varfree \<equiv> varfree.varfree_inst_prob my_P\<^sub>T_num my_cert_ops"
definition "my_folded \<equiv> fact_folder.fold_prob my_varfree my_cert_facts my_fluents"

text \<open>The reachable fluents enumerated off the certified ops: the three ground \<open>fuel(c)\<close> PNEs, one
  per Car. These are what stage two turns into nullary function names.\<close>
value "my_fluents"

text \<open>Stage one's output is literally the numeric grounder's output: the error monad's \<^const>\<open>Inr\<close>
  payload \<^emph>\<open>is\<close> \<^const>\<open>varfree.varfree_inst_prob\<close> at the same ops list (\<^const>\<open>True\<close>).\<close>
value "my_grounded_num = Inr my_varfree"

text \<open>Stage two's output: everything is nullary --- the predicates are the fresh names of the
  certified facts, the functions are the fresh names of the \<open>fuel(c)\<close> fluents above, and each
  action's precondition/effect is stated purely over those nullary names.\<close>
value "my_folded"

text \<open>And the factorization made concrete: folding stage one's output equals the one-shot
  propositional grounder \<^const>\<open>ground_by_cert\<close> on the original problem (\<^const>\<open>True\<close>) --- the
  evaluation counterpart of \<open>ground_prob_factors\<close>.\<close>
value "my_folded = ground_by_cert my_problem_num (fst my_cert_num)"

end
