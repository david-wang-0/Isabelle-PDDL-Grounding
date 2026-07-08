theory Classical_PDDL_Relaxation
  imports Classical_PDDL_Relaxation_Locales
begin

section \<open> Relaxation Preserves Well-Formedness \<close>

subsection \<open> Preserving normalization \<close>

lemmas norm_dom_defs =
  ast_classical_domain.normalized_dom_def
  ast_classical_domain.typeless_classical_domain_def
  ast_classical_domain.prec_normed_dom_def
lemmas norm_prob_defs =
  ast_classical_problem.normalized_prob_def
  ast_classical_problem.typeless_classical_problem_def

lemma (in normalized_domain_rx) rx_acs_typeless:
  "\<forall>ac \<in> set (map relax_ac (actions D)). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>"
  using normalized_dom unfolding norm_dom_defs by simp

lemma (in normalized_domain_rx) rx_acs_pos_conjs:
  "\<forall>ac\<in>set (map relax_ac (actions D)). is_pos_conj (ac_pre ac)"
  using normalized_dom unfolding norm_dom_defs
  using relax_conj_pos relax_ac_sel(3) relax_dom_sel(4)
  by fastforce

lemma (in normalized_domain_rx) rx_acs_conjs:
  "\<forall>ac\<in>set (map relax_ac (actions D)). is_conj (ac_pre ac)"
  using rx_acs_pos_conjs pos_conj_conj by blast

theorem (in normalized_domain_rx) relax_dom_normed:
  "dx.normalized_dom"
  using normalized_dom
  unfolding norm_dom_defs relax_dom_sel
  using rx_acs_typeless rx_acs_conjs by simp

theorem (in normalized_problem_rx) relax_normed:
  "px.normalized_prob"
  using normalized_prob relax_dom_normed
  unfolding ast_classical_domain.normalized_dom_def norm_prob_defs
  unfolding relax_prob_sel
  using relax_conj_pos pos_conj_conj by blast

theorem (in normalized_problem_rx) relax_relaxes:
  "px.relaxed_prob"
proof -
  have "dx.relaxed_dom"
    unfolding dx.relaxed_dom_def
    using relax_dom_normed rx_acs_pos_conjs
    by (auto simp: relaxed_action_def relax_ac_sel relax_dom_sel)
  thus ?thesis
    using relax_normed normalized_prob
    unfolding px.relaxed_prob_def norm_prob_defs relax_prob_sel
    using relax_conj_pos by auto
qed

subsection \<open> Preserving Well-Formedness \<close>

lemma (in ast_classical_domain) relax_fmla_wf:
  "wf_fmla tyt F \<Longrightarrow> wf_fmla tyt (relax_conj F)"
  apply (induction F)
  subgoal for x by (cases x) simp_all
      apply simp_all
  subgoal for F by (cases F rule: is_pos_lit.cases) simp_all
  subgoal for F G by (cases F rule: is_pos_lit.cases) simp_all
  done

lemma (in ast_classical_domain) relax_eff_wf:
  "wf_effect tyt eff \<Longrightarrow> wf_effect tyt (relax_eff eff)"
  by (cases eff) simp

text \<open>Relaxation strips the numeric init assignments (\<open>relax_prob\<close> keeps only \<^const>\<open>is_predAtom\<close>
  init facts), so the relaxed initial world model agrees with the original on the \<^emph>\<open>propositional\<close>
  part \<open>fst\<close> only --- the numeric valuation \<open>snd\<close> is emptied. Reachability uses only \<open>fst\<close>.\<close>
lemma (in ast_classical_problem_rx) rx_I: "fst px.I = fst I"
  unfolding ast_classical_problem.I_def relax_prob_sel by (simp add: filter_filter)

lemma (in ast_classical_domain) relax_ac_names:
  "map ac_name (actions D) = map ac_name (map relax_ac (actions D))"
  using relax_ac_sel(1) by simp

lemma (in ast_classical_domain_rx) relax_ac_wf:
  assumes "wf_classical_action_schema a" "is_conj (ac_pre a)"
  shows "dx.wf_classical_action_schema (relax_ac a)"
  using assms
  apply (cases a rule: ast_classical_action_schema_cases_unfold; simp)
  unfolding Let_def
  apply (intro conjI)
  using relax_fmla_wf apply metis
  using relax_eff_wf by metis

theorem (in normalized_domain_rx) relax_dom_wf:
  "dx.wf_classical_domain"
  using wf_classical_domain
  unfolding ast_classical_domain.wf_classical_domain_def
  unfolding domain_signature.wf_types_def
  unfolding domain_signature.wf_predicate_decl_alt domain_signature.wf_type_alt
  unfolding relax_dom_sel
  using relax_ac_names relax_ac_wf
  using normalized_dom unfolding norm_dom_defs by auto

lemma (in normalized_problem_rx) rx_goal_wf:
  "dx.wf_fmla px.objT (relax_conj (goal P))"
  using wf_P(5) relax_fmla_wf by metis

theorem (in normalized_problem_rx) relax_wf:
  "px.wf_classical_problem"
  using wf_classical_problem
  unfolding ast_classical_problem.wf_classical_problem_def
  unfolding relax_prob_sel relax_dom_sel
  apply (intro conjI)
  using relax_dom_wf apply blast
  apply blast
  apply (metis distinct_filter)
  apply (metis (mono_tags, lifting) mem_Collect_eq set_filter)
  using relax_fmla_wf by blast

sublocale normalized_domain_rx \<subseteq> dx: normalized_domain DX
  apply (unfold_locales)
  using relax_dom_normed relax_dom_wf by simp_all

sublocale normalized_problem_rx \<subseteq> px: normalized_problem PX
  apply (unfold_locales)
  using relax_normed relax_wf by simp_all

end
