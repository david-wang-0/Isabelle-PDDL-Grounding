theory Running_Example_Numeric
  imports Running_Example Grounding_Pipeline_Numeric_Executable
begin

section \<open>A numeric variant of the running example: a \<open>fuel\<close> fluent\<close>

text \<open>The Helmert-2009 running example (\<^theory>\<open>Classical_Grounding.Running_Example\<close>) with a single
  numeric fluent added: each \<open>Car\<close> has a \<open>fuel\<close> function; \<open>drive\<close> now requires \<open>fuel >= 1\<close> and
  \<open>from \<noteq> to\<close> (an \<^const>\<open>eqAtm\<close> inequality guard, translated to a datalog \<open>Neql\<close>) and
  \<open>decrease\<close>s fuel by 1. Everything else is reused verbatim (types, predicates, consts, objects,
  goal, and the other operators). We then thread it through the \<^emph>\<open>same\<close> grounding pipeline and run
  \<^bold>\<open>both\<close> numeric grounding stages, stopping \<^emph>\<open>before\<close> the STRIPS conversion:

  \<^item> \<^bold>\<open>stage 1\<close> --- the Variable_Freeness instantiation \<^const>\<open>instantiate_all_actions_dfs_e\<close>:
    every certified-reachable op becomes a \<^emph>\<open>nullary schema\<close> whose body still mentions the
    original ground atoms and \<open>fuel(c)\<close> fluents. Its product is \<open>my_varfree_num\<close> below.
  \<^item> \<^bold>\<open>stage 2\<close> --- the fact/fluent fold \<^const>\<open>ground_all_actions_dfs_e\<close>: those ground atoms and
    fluents are re-indexed onto fresh \<^emph>\<open>nullary\<close> predicates and functions, giving the fully
    grounded numeric problem \<open>my_grounded_num\<close> (proven well-formed by
    \<open>ground_all_actions_dfs_e_wf\<close>).

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
  \<^const>\<open>numeric_grounding_checks_exec\<close> is \<^const>\<open>True\<close>, and so is the strictly stronger
  \<^const>\<open>numeric_fold_checks_exec\<close> that additionally gates the second (fold) stage --- its
  numeric-permissive \<^const>\<open>covered_num\<close> obligations on preconditions, goal and \<^emph>\<open>initial
  state\<close> all hold, the last one because the three \<open>fuel(c)\<close> assignments in \<open>init\<close> are exactly the
  fluents the reachable ops mention.\<close>
value "my_P\<^sub>T_num"
value "my_P\<^sub>R_num"
value "my_cert_num"

text \<open>The datalog program \<open>dl_rules P\<^sub>R\<close> that the certificate is a founded model of. The \<open>drive\<close>
  clauses now carry a \<open>Neql\<close> body guard --- the datalog image of the \<open>from \<noteq> to\<close> inequality (the
  \<open>eqAtm\<close> literal translated by \<open>dl_cond_rh\<close>), alongside the positive \<open>road\<close>/type body atoms.\<close>
value "my_dl_rules_num"
value "dl_certified_model_dfs my_dl_rules_num my_const_names_num (fst my_cert_num) (snd my_cert_num)"
text \<open>The ordered-scan (topological-order) alternative: same certificate, accepted by validating
  the certificate's rule order instead of the linear directed-cycle DFS sweep. Both foundedness
  checks agree (\<^const>\<open>True\<close>).\<close>
value "dl_certified_model_exec my_dl_rules_num my_const_names_num (fst my_cert_num) (snd my_cert_num)"
value "grounding_checks_exec my_P\<^sub>T_num (fst my_cert_num)"
value "numeric_grounding_checks_exec my_P\<^sub>T_num (fst my_cert_num)"
value "numeric_fold_checks_exec my_P\<^sub>T_num (fst my_cert_num)"

subsection \<open>The certified inputs both stages consume\<close>

text \<open>Both grounding stages are driven by the same certified data the pipeline entry points read
  off the certificate: the reachable ops list, the reachable facts list, and --- for the numerics
  --- the ground fluents enumerated from those ops.\<close>

definition "my_cert_facts_num \<equiv> cert_facts_of_exec my_P\<^sub>T_num (fst my_cert_num)"
definition "my_cert_ops_num \<equiv> canon (cert_ops_of_exec_fast my_P\<^sub>T_num (fst my_cert_num))"
definition "my_fluents_num \<equiv> varfree.fluents my_P\<^sub>T_num my_cert_ops_num"

value "my_cert_facts_num"
value "my_cert_ops_num"

text \<open>The reachable fluents enumerated off the certified ops: the three ground \<open>fuel(c)\<close> PNEs, one
  per Car. These are what stage two turns into nullary function names.\<close>
value "my_fluents_num"

subsection \<open>Stage 1: the variable-free instantiation (fuel fluent retained)\<close>

text \<open>Stage one instantiates every certified-reachable op into a \<^emph>\<open>nullary schema\<close> --- parameters
  gone, but the ground atoms and the \<open>fuel(c)\<close> numerics still there. Its output is a full PDDL
  problem, and it is exactly what the error-monad entry point
  \<^const>\<open>instantiate_all_actions_dfs_e\<close> returns inside its \<^const>\<open>Inr\<close> (a failing check would give
  \<^const>\<open>Inl\<close> of a diagnostic string instead).\<close>

definition "my_varfree_num \<equiv> varfree.varfree_inst_prob my_P\<^sub>T_num my_cert_ops_num"

value "my_varfree_num"

text \<open>The instantiated action schemas themselves: each is nullary (empty parameters) and retains the
  real numeric \<open>fuel >= 1\<close> guard, the \<open>from \<noteq> to\<close> inequality, and the \<open>decrease (fuel c) 1\<close>
  \<^const>\<open>NumericEffect\<close>; the domain keeps the original \<open>fuel\<close> function declaration.\<close>
value "actions (domain my_varfree_num)"

text \<open>The connecting identity: the stage-1 entry point's \<^const>\<open>Inr\<close> payload \<^emph>\<open>is\<close> this problem
  (\<^const>\<open>True\<close>).\<close>
value "instantiate_all_actions_dfs_e (\<lambda>_. my_cert_num) my_problem_num = Inr my_varfree_num"

subsection \<open>Stage 2: the fact/fluent fold --- the fully grounded numeric problem\<close>

text \<open>Stage two collapses the ground atoms onto fresh nullary predicates and the ground fluents
  onto fresh nullary functions (\<^const>\<open>fact_folder.fold_prob\<close>), yielding the \<^emph>\<open>fully grounded\<close>
  numeric problem --- the abstract \<^const>\<open>ast_classical_problem.numeric_P\<^sub>G_cert\<close>, proven
  well-formed by \<open>numeric_wf_ground_cert_problem\<close>. It is what the stage-2 entry point
  \<^const>\<open>ground_all_actions_dfs_e\<close> returns.\<close>

definition "my_grounded_num \<equiv> fact_folder.fold_prob my_varfree_num my_cert_facts_num my_fluents_num"

value "my_grounded_num"

text \<open>The numeric-specific components (the propositional counterparts --- predicates, goal, and the
  empty types/consts/objects --- are already shown for the propositional example in
  \<^theory>\<open>Classical_Grounding.Running_Example\<close>, so they are not repeated here). The function table
  is one \<^emph>\<open>nullary\<close> \<open>FuncDecl\<close> per reachable \<open>fuel(c)\<close> fluent, named by the readable encoding
  plus its index (\<open>fuel_c1_0\<close>, \<dots>).\<close>
value "functions (domain my_grounded_num)"

text \<open>Each grounded action is nullary over nullary names only: the \<open>at\<close>/\<open>road\<close> atoms have become
  nullary predicates and the \<open>decrease (fuel c) 1\<close> effect now decreases the nullary function.\<close>
value "actions (domain my_grounded_num)"

text \<open>The folded initial state: the propositional atoms are nullary predicate atoms, and each
  initial function assignment \<open>(= (fuel c) 10)\<close> has been folded onto its nullary function ---
  which is exactly the \<open>init_covered_num\<close> obligation of \<^const>\<open>numeric_fold_checks_exec\<close> at
  work.\<close>
value "init my_grounded_num"

text \<open>The connecting identity for stage 2: the stage-2 entry point's \<^const>\<open>Inr\<close> payload \<^emph>\<open>is\<close>
  the folded problem (\<^const>\<open>True\<close>).\<close>
value "ground_all_actions_dfs_e (\<lambda>_. my_cert_num) my_problem_num = Inr my_grounded_num"

text \<open>And the two-stage composite made concrete: folding stage one's output equals the executable
  grounder \<^const>\<open>ground_by_cert\<close> on the original problem (\<^const>\<open>True\<close>) --- the evaluation
  counterpart of the definitional identity behind \<open>ground_by_cert_numeric_eq\<close>.\<close>
value "my_grounded_num = ground_by_cert my_problem_num (fst my_cert_num)"

end
