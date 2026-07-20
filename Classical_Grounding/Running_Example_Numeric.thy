theory Running_Example_Numeric
  imports Running_Example Grounding_Pipeline_Numeric_Executable
begin

section \<open>A numeric variant of the running example: a \<open>fuel\<close> fluent\<close>

text \<open>The Helmert-2009 running example (\<^theory>\<open>Classical_Grounding.Running_Example\<close>) with a single
  numeric fluent added: each \<open>Car\<close> has a \<open>fuel\<close> function; \<open>drive\<close> now requires \<open>fuel >= 1\<close> and
  \<open>decrease\<close>s fuel by 1. Everything else is reused verbatim (types, predicates, consts, objects,
  goal, and the other operators). We then thread it through the \<^emph>\<open>same\<close> grounding pipeline and run
  the numeric-fluent-retaining grounder \<^const>\<open>ground_via_cert_numeric_dfs_e\<close>, stopping \<^emph>\<open>before\<close> the
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
  \<^const>\<open>ground_via_cert_numeric_dfs_e\<close> gate keys on the latter, so the grounder retains the \<open>fuel\<close>
  function declaration \<^emph>\<open>and\<close> the \<open>decrease (fuel c) 1\<close> \<^const>\<open>NumericEffect\<close> on each grounded drive.\<close>

subsection \<open>Domain and problem with the \<open>fuel\<close> fluent\<close>

definition "my_funcs_num \<equiv> [FuncDecl (Func STR ''fuel'') [Either [STR ''Car'']]]"

definition "op_drive_num \<equiv> SimpleActionSchema
  (ActionHead STR ''drive''
    [(variable.Var STR ''c'', Either [STR ''Car'']), (variable.Var STR ''from'', Either [STR ''City'']), (variable.Var STR ''to'', Either [STR ''City''])])
  (SimpleActionBody
    (And (And (Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''c''), term.VAR (variable.Var STR ''from'')]))
              (Atom (numericGEAtm (FunctionExpr (PNE (Func STR ''fuel'') [term.VAR (variable.Var STR ''c'')])) (ConstantExpr 1))))
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

text \<open>Probes: the normalized problem \<open>P\<^sub>T\<close> (retains the \<open>decrease\<close> effect + \<open>fuel >= 1\<close> guard, plus the
  added \<open>def(fuel,...)\<close> predicates), the self-computed reference certificate, and the re-checks. The
  certificate is accepted (\<^const>\<open>dl_certified_model_dfs\<close> holds on the numeric-free \<open>P\<^sub>R\<close>); the
  \<^emph>\<open>propositional\<close> re-check \<^const>\<open>grounding_checks_exec\<close> is \<^const>\<open>False\<close> (its \<open>ops_no_num\<close>/\<open>init_props\<close>
  conjuncts fail on \<open>P\<^sub>T\<close>'s retained numerics), while the numeric-fluent-retaining re-check
  \<^const>\<open>numeric_grounding_checks_exec\<close> is \<^const>\<open>True\<close>.\<close>
value "my_P\<^sub>T_num"
value "my_cert_num"
value "dl_certified_model_dfs (dl_rules my_P\<^sub>R_num)
         (ast_classical_problem.const_names my_P\<^sub>R_num) (fst my_cert_num) (snd my_cert_num)"
text \<open>The ordered-scan (topological-order) alternative: same certificate, accepted in
  \<open>O(|rules| \<cdot> |body| \<cdot> |facts|)\<close> instead of the per-vertex DFS's \<open>O(|facts|\<^sup>2)\<close>. Both \<^const>\<open>True\<close>.\<close>
value "dl_certified_model_exec (dl_rules my_P\<^sub>R_num)
         (ast_classical_problem.const_names my_P\<^sub>R_num) (fst my_cert_num) (snd my_cert_num)"
text \<open>The fast single-sweep global-visited DFS (\<^const>\<open>dl_acyclic_dfs_global\<close>): one \<open>O(|V|+|E|)\<close>
  pass, again accepting the same certificate. All three foundedness checks agree (\<^const>\<open>True\<close>).\<close>
value "dl_certified_model_gdfs (dl_rules my_P\<^sub>R_num)
         (ast_classical_problem.const_names my_P\<^sub>R_num) (fst my_cert_num) (snd my_cert_num)"
value "grounding_checks_exec my_P\<^sub>T_num (fst my_cert_num)"
value "numeric_grounding_checks_exec my_P\<^sub>T_num (fst my_cert_num)"

subsection \<open>Numeric grounding, retaining the fuel fluent (before STRIPS)\<close>

text \<open>The error-monad fluent grounder returns \<^const>\<open>Inr\<close> of the grounded (pre-STRIPS) PDDL problem
  whose nullary \<open>drive\<close> schemas retain the real \<open>decrease (fuel c) 1\<close> \<^const>\<open>NumericEffect\<close> and the
  \<open>fuel >= 1\<close> guard, over the certified reachable ops (a failing check would give \<^const>\<open>Inl\<close> of a
  diagnostic string instead).\<close>
value "ground_via_cert_numeric_dfs_e (\<lambda>_. my_cert_num) my_problem_num"

end
