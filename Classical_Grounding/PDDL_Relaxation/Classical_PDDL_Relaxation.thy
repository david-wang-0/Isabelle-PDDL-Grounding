theory Classical_PDDL_Relaxation
  imports Classical_PDDL_Relaxation_Locales
    Grounding_Classical_Common.Numeric_Free
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

subsection \<open> Relaxation is numeric-free \<close>

text \<open>Delete-relaxation lands in the numeric-free (propositional) fragment: \<^const>\<open>relax_lit\<close>
  sends every numeric-comparison literal (and negated \<^const>\<open>predAtm\<close>) to \<open>\<^bold>\<not>\<bottom>\<close> and keeps only
  positive-literal shapes (\<^const>\<open>predAtm\<close>/\<^const>\<open>eqAtm\<close>/\<open>\<bottom>\<close>), all of which are numeric-free;
  \<^const>\<open>relax_eff\<close> drops the delete and numeric effects and its (well-formed) adds are
  \<^const>\<open>predAtm\<close>s. Hence the whole relaxed problem satisfies \<open>num_free_prob\<close>.\<close>

text \<open>Every positive literal is numeric-free (\<^const>\<open>predAtm\<close>/\<^const>\<open>eqAtm\<close> are not numeric,
  \<open>\<bottom>\<close>/\<open>\<^bold>\<not>\<bottom>\<close> trivially).\<close>
lemma pos_lit_num_free: "is_pos_lit f \<Longrightarrow> num_free_fmla f"
  by (cases f rule: is_pos_lit.cases) simp_all

text \<open>A positive conjunction is numeric-free.\<close>
lemma pos_conj_num_free: "is_pos_conj F \<Longrightarrow> num_free_fmla F"
  by (induction F rule: pos_conj_induct) (simp_all add: pos_lit_num_free)

text \<open>Relaxing a normalized literal yields a numeric-free formula (it is a positive literal).\<close>
lemma num_free_relax_lit: "is_lit_plus f \<Longrightarrow> num_free_fmla (relax_lit f)"
  using relax_lit_pos pos_lit_num_free by blast

text \<open>Relaxing a conjunction yields a numeric-free formula (it is a positive conjunction).\<close>
lemma num_free_relax_conj: "is_conj \<phi> \<Longrightarrow> num_free_fmla (relax_conj \<phi>)"
  using relax_conj_pos pos_conj_num_free by blast

text \<open>A well-formed effect has \<^const>\<open>predAtm\<close> adds, so its relaxation is numeric-free.\<close>
lemma (in ast_classical_domain) num_free_relax_eff:
  assumes "wf_effect tyt eff"
  shows "num_free_eff (relax_eff eff)"
proof (cases eff)
  case (Effect a d n)
  have "num_free_fmla \<phi>" if "\<phi> \<in> set a" for \<phi>
  proof -
    have "wf_fmla_atom tyt \<phi>" using assms Effect that by simp
    hence "is_predAtom \<phi>" by (simp add: wf_fmla_atom_alt)
    thus ?thesis by (cases \<phi> rule: is_predAtom.cases) simp_all
  qed
  thus ?thesis using Effect by simp
qed

text \<open>Delete-relaxation of a normalized well-formed problem is numeric-free: the goal and the
  action preconditions are (positive) conjunctions, the effect adds are \<^const>\<open>predAtm\<close>s, and the
  kept init facts are exactly the \<^const>\<open>predAtm\<close>s of the original init.\<close>
theorem (in normalized_problem_rx) relax_num_free:
  "px.num_free_prob"
proof -
  \<comment> \<open>domain: every relaxed action is numeric-free\<close>
  have "num_free_ac (relax_ac a)" if a_mem: "a \<in> set (actions D)" for a
  proof -
    have "is_conj (ac_pre a)"
      using a_mem normalized_dom unfolding norm_dom_defs prec_normed_dom_def by blast
    hence pre: "num_free_fmla (relax_conj (ac_pre a))"
      using num_free_relax_conj by blast
    have "wf_classical_action_schema a"
      using a_mem wf_D by blast
    hence "wf_effect (ac_tyt a) (ac_eff a)"
      unfolding wf_classical_action_schema_alt by blast
    hence eff: "num_free_eff (relax_eff (ac_eff a))"
      using num_free_relax_eff by blast
    show ?thesis
      using pre eff unfolding num_free_ac_def by simp
  qed
  hence dom: "px.num_free_dom"
    unfolding ast_classical_domain.num_free_dom_def relax_prob_sel relax_dom_sel by auto
  \<comment> \<open>goal: the relaxed goal is a (positive) conjunction, hence numeric-free\<close>
  have goal: "num_free_fmla (goal PX)"
    unfolding relax_prob_sel
    using normalized_prob num_free_relax_conj unfolding normalized_prob_def by blast
  \<comment> \<open>init: the kept init facts are exactly the \<^const>\<open>predAtm\<close>s of the original init\<close>
  have init: "num_free_fmla f" if "f \<in> set (init PX)" for f
  proof -
    have "is_predAtom f" using that unfolding relax_prob_sel by simp
    thus ?thesis by (cases f rule: is_predAtom.cases) simp_all
  qed
  show ?thesis
    unfolding px.num_free_prob_def
    using dom goal init by blast
qed

end
