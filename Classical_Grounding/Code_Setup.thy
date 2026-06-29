theory Code_Setup
  imports Grounding_Pipeline_Numeric
    "Continuous_Planning.PDDL_Checker_Common"
    "HOL-Library.AList_Mapping"
begin

text \<open>Shared code-generation setup for running the verified pipeline. Factored out of
  \<^verbatim>\<open>Running_Example\<close> so that both the running example and the
  executable pipeline (\<^verbatim>\<open>Grounding_Pipeline_STRIPS_Executable\<close>) share one copy.

  The pipeline's normalization functions live in the shared \<open>domain_signature\<close> /
  \<open>problem_signature\<close> locales, which the Formal-PDDL-Semantics development also instantiates at
  its record-based continuous/temporal problem types. Those per-interpretation code equations
  pattern-match on field selectors (e.g. \<open>predicates ?d\<close>) and are not valid code equations,
  poisoning the shared constant. We drop all code equations for each affected constant and re-add
  only the clean foundational (field-variable) equation.\<close>

declare ast_classical_problem.P\<^sub>X_def [code]
declare ast_classical_problem.P\<^sub>N_def [code]
declare ast_classical_problem.P\<^sub>T_def [code]

declare [[code drop:
  domain_signature.detyped_predicates domain_signature.detyped_consts
  domain_signature.detyped_functions problem_signature.detyped_objs
  domain_signature.param_precond
  domain_signature.def_prefix domain_signature.detype_simple_action_body]]
declare domain_signature.detyped_predicates_def[code]
declare domain_signature.detyped_consts_def[code]
declare domain_signature.detyped_functions_def[code]
declare problem_signature.detyped_objs_def[code]
declare domain_signature.param_precond_def[code]
declare domain_signature.def_prefix_def[code]
declare domain_signature.detype_simple_action_body.simps[code]

text \<open>Missing executable equations: def_translate code bundle + lifted string ops.\<close>
declare ast_classical_domain.def_translate_dom_def[code]
declare ast_classical_problem.def_translate_prob_def[code]
lemma padl_lit_code[code]: "padl_lit n s = String.implode (padl n (String.explode s))"
  by (metis padl_lit.rep_eq String.implode_explode_eq)
declare distinct_strings_lit_eq[code]

text \<open>Numeric expression valuation is not code-generable: the Formal-PDDL-Semantics
  \<^const>\<open>numeric_expression_valuation\<close> covers transcendental constructors (\<open>SinExpr\<close>/\<open>CosExpr\<close>/
  \<open>ExpExpr\<close>) via \<^const>\<open>sin\<close>/\<^const>\<open>cos\<close>/\<^const>\<open>exp\<close>, whose \<^typ>\<open>real\<close> code equations pull in
  \<open>suminf\<close>/\<open>Inf [filter]\<close> (a \<open>filter :: enum\<close> wellsortedness error). Whole-program code generation
  compiles \<^emph>\<open>every\<close> branch of \<^const>\<open>valuation\<close>, so even our numeric-free classical pipeline
  (which never evaluates a numeric expression) is poisoned.

  We override \<^const>\<open>numeric_expression_valuation\<close> with a self-referential \<^const>\<open>Code.abort\<close>:
  the equation \<open>numeric_expression_valuation x w = Code.abort \<dots> (\<lambda>_. numeric_expression_valuation x w)\<close>
  is a \<^emph>\<open>tautology\<close> (\<open>Code.abort m (\<lambda>_. e) = e\<close>), so it is sound; and its right-hand side
  references only \<^const>\<open>numeric_expression_valuation\<close> itself, cutting the code dependency on
  \<^const>\<open>sin\<close>/\<open>suminf\<close>. Code generated for a numeric-free problem never reaches the abort.\<close>
declare [[code drop: numeric_expression_valuation]]
lemma numeric_expression_valuation_code[code]:
  "numeric_expression_valuation x w =
     Code.abort (STR ''numeric_expression_valuation: not executable (numeric-free pipeline only)'')
                (\<lambda>_. numeric_expression_valuation x w)"
  by (simp add: Code.abort_def)

text \<open>Code equations for the certificate / grounding / well-formedness checks. These are locale
  \<^bold>\<open>definition\<close>s / \<^bold>\<open>fun\<close>s whose defining equations are not registered with the code generator by
  default; the executable pipeline (\<^verbatim>\<open>ground_via_cert\<close>) needs them.\<close>
text \<open>These four live in locales \<^emph>\<open>without\<close> assumptions (\<open>ast_classical_problem\<close>,
  \<open>ast_classical_domain\<close>, \<open>simple_action_instantiations\<close>), so their defining equations are
  unconditional and directly registrable.\<close>
declare ast_classical_problem.restrict_prob_def[code]
declare ast_classical_problem.wf_classical_problem_def[code]
declare ast_classical_domain.resolve_classical_action_schema_def[code]
declare simple_action_instantiations.res_inst.simps[code]

text \<open>The shared \<open>domain_signature\<close>/\<open>problem_signature\<close> well-formedness functions are poisoned by
  selector-pattern code equations from the Formal-PDDL-Semantics continuous/temporal interpretations
  (same issue as the detype cluster above; FPS itself never code-generates these specs --- it uses
  separate executable \<open>check_wf_*\<close> functions). Drop the bad equations and re-add the clean
  foundational ones so the grounder's \<open>grounding_checks\<close> (wf_fmla_atom / wf_classical_plan_action /
  \<dots>) become code-generable.\<close>
declare [[code drop:
  domain_signature.wf_type domain_signature.wf_predicate_decl domain_signature.wf_function_decl
  domain_signature.wf_types domain_signature.wf_domain_signature domain_signature.constT
  domain_signature.restrict_dom_sig domain_signature.sig domain_signature.wf_atom
  domain_signature.wf_fmla domain_signature.wf_fmla_atom
  problem_signature.wf_problem_signature problem_signature.objT problem_signature.wf_func_assign
  ast_classical_domain.wf_classical_domain ast_classical_domain.restrict_dom
  ast_classical_problem.wf_classical_plan_action]]
declare domain_signature.wf_type.simps[code]
declare domain_signature.wf_predicate_decl.simps[code]
declare domain_signature.wf_function_decl.simps[code]
declare domain_signature.wf_types_def[code]
declare domain_signature.wf_domain_signature_def[code]
declare domain_signature.constT_def[code]
declare domain_signature.restrict_dom_sig_def[code]
declare domain_signature.sig_def[code]
declare domain_signature.wf_atom.simps[code]
declare domain_signature.wf_fmla.simps[code]
declare domain_signature.wf_fmla_atom.simps[code]
declare problem_signature.wf_problem_signature_def[code]
declare problem_signature.objT_def[code]
declare problem_signature.wf_func_assign.simps[code]
declare ast_classical_domain.wf_classical_domain_def[code]
declare ast_classical_domain.restrict_dom_def[code]
declare ast_classical_problem.wf_classical_plan_action.simps[code]

text \<open>Further signature functions that simply lack a registered code equation (not poisoned).\<close>
declare domain_signature.wf_classical_action_schema.simps[code]
declare domain_signature.wf_pred_atom.simps[code]
declare domain_signature.wf_primitive_numeric_expression.simps[code]
declare domain_signature.wf_numeric_expression.simps[code]
declare domain_signature.wf_func_args.simps[code]
declare domain_signature.wf_simple_action_body.simps[code]
declare domain_signature.wf_effect.simps[code]
declare domain_signature.wf_numeric_effect.simps[code]
declare domain_signature.wf_action_head.simps[code]
declare problem_signature.action_params_match_def[code]

declare [[code drop: domain_signature.of_type domain_signature.is_of_type
  domain_signature.subtype_rel domain_signature.subtype_edge]]
declare domain_signature.is_of_type_def[code]
declare domain_signature.subtype_rel_def[code]
declare domain_signature.subtype_edge.simps[code]

text \<open>\<^const>\<open>domain_signature.of_type\<close> is genuinely non-code-generable as specified
  (\<open>set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)\<close> --- reflexive-transitive
  closure + \<^const>\<open>Code_Cardinality.subset'\<close> over the non-\<open>enum\<close> type \<^typ>\<open>String.literal\<close>). We give
  it the executable graph-reachability code equation that Formal-PDDL-Semantics' checker uses
  (\<^const>\<open>of_type_impl\<close> / \<^const>\<open>tab_succ\<close> / \<^const>\<open>dfs_reachable\<close>); cf.
  \<open>ast_cont_domain.of_type_impl_correct\<close>, re-proved here at the \<open>domain_signature\<close> level so it
  applies to the classical domains too.\<close>
text \<open>Stated at theory top level (\<^emph>\<open>not\<close> \<open>(in domain_signature)\<close>): an in-locale \<open>[code]\<close> equation
  would be re-interpreted into every sublocale (\<open>ast_cont_domain\<close>, \<dots>) with \<open>ty_decl\<close> replaced by
  the selector \<open>types D\<close>, re-introducing the selector-pattern poison. A top-level equation about the
  single constant \<^const>\<open>domain_signature.of_type\<close> (assumption-free locale \<Rightarrow> unconditional \<open>_def\<close>)
  does not propagate.\<close>
lemma of_type_code[code]:
  "domain_signature.of_type ty_decl oT T
     = of_type_impl (tab_succ (map domain_signature.subtype_edge ty_decl)) oT T"
  unfolding domain_signature.of_type_def of_type_impl_def domain_signature.subtype_rel_def
  by (auto simp: dfs_reachable_tab_succ_correct)

text \<open>NOTE: the certificate/grounding checks (\<^verbatim>\<open>pddl_datalog.admissible\<close>,
  \<open>closure_check\<close>, \<open>ordered_check\<close>, \<open>local_valid\<close>, \<open>cert_ops\<close>;
  \<^verbatim>\<open>normalized_problem_rx.grounding_checks\<close>, \<open>cert_facts_of\<close>, \<open>cert_ops_of\<close>,
  \<open>extra_eff_atoms_of\<close>) live in locales \<^emph>\<open>with\<close> assumptions, so their \<open>_def\<close> equations are
  guarded by the locale predicate (\<open>pddl_datalog ?P \<Longrightarrow> \<dots>\<close>) --- "not an equation", hence not
  directly code-registrable, exactly like \<^verbatim>\<open>P\<^sub>G_cert\<close>. They need \<^emph>\<open>unconditional executable
  mirrors\<close> (the \<^verbatim>\<open>ground_by_cert\<close> pattern), to be added in \<^verbatim>\<open>Grounding_Pipeline_STRIPS_Executable\<close>,
  with the equality-to-locale-version lemmas proved for the soundness link.\<close>

end
