theory Numeric_Grounding_Cert
  imports Grounding_Pipeline_Numeric
    Classical_Grounded_PDDL.Numeric_Grounder_Semantics
begin

section \<open>Grounding against a certified reachability model (numeric)\<close>

text \<open>The numeric analogue of the certificate-grounding block in
  \<^theory>\<open>Classical_Grounding.Grounding_Pipeline_Numeric\<close>: the same certified reachability model
  \<open>(M, dc)\<close> now drives the \<^emph>\<open>numeric-fluent-retaining\<close> grounder \<^const>\<open>grounder.numeric_ground_prob\<close>
  instead of the propositional \<^const>\<open>grounder.ground_prob\<close>. Well-formedness and plan-preservation
  are inherited from \<open>wf_grounder_num.numeric_ground_prob_wf\<close> /
  \<open>wf_grounder_num.numeric_valid_classical_plan_iff\<close> via the \<open>cr.wfg_num\<close> interpretation of the
  \<^emph>\<open>weaker\<close> \<^locale>\<open>certified_reachability_num\<close> --- which requires only
  \<open>numeric_grounding_checks\<close> (the five coverage obligations), \<^emph>\<open>not\<close> the numeric-freeness checks
  \<open>init_props\<close>/\<open>ops_no_num\<close> that the propositional \<^locale>\<open>certified_reachability\<close> imposes. This is
  what lets a task with genuine numeric effects (whose reachable ops carry \<open>NumericEffect\<close>s) pass the
  re-check and be grounded with those effects retained. (Note \<^const>\<open>grounder.numeric_ground_prob\<close>
  takes only \<open>P\<close> and \<open>ops\<close> --- the grounder's \<open>facts\<close> parameter is unused, so the locale drops it
  from the constant's signature.)\<close>

context ast_classical_problem begin

text \<open>Interpretation helper for the numeric certified-reachability locale, mirroring
  \<open>certified_reachability_i\<close> but discharging the \<^emph>\<open>weaker\<close> \<open>numeric_grounding_checks\<close> re-check
  (so it applies to a task whose reachable ops still carry numeric effects).\<close>
lemma certified_reachability_num_i:
  assumes "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and "dl_certified_model
             (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
             (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and "normalized_problem_rx.numeric_grounding_checks P\<^sub>T M"
      and "restrict_prob" "wf_classical_problem"
  shows "certified_reachability_num P\<^sub>T M dc"
proof -
  \<comment> \<open>\<open>normalized_problem_rx P\<^sub>T\<close> holds from \<open>restrict_prob\<close>/\<open>wf\<close> alone; we cannot reuse
     \<open>P_T_normalized_problem_rx\<close> because it is stated inside the propositional cert context (whose
     assumptions include the \<^emph>\<open>full\<close> \<open>grounding_checks\<close> that we deliberately do not have here).\<close>
  have wf_N: "ast_classical_problem.wf_classical_problem P\<^sub>N" using assms(4,5) normalization_wf by simp
  have norm_N: "ast_classical_problem.normalized_prob P\<^sub>N" using assms(4,5) normalization_normalizes by simp
  have wf_T: "ast_classical_problem.wf_classical_problem P\<^sub>T"
    using wf_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_prob_wf_compact)
  have norm_T: "ast_classical_problem.normalized_prob P\<^sub>T"
    using norm_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  have rx_T: "normalized_problem_rx P\<^sub>T"
    unfolding normalized_problem_rx_def normalized_problem_def'
    using wf_T norm_T by blast
  interpret rx: normalized_problem_rx P\<^sub>T using rx_T .
  show ?thesis
    apply unfold_locales
    using assms(1,2,3)
    by simp_all
qed

context
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes nonempty: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and grounding_cert_num: "normalized_problem_rx.numeric_grounding_checks P\<^sub>T M"
begin

definition "numeric_P\<^sub>G_cert \<equiv> grounder.numeric_ground_prob P\<^sub>T
  (canon (normalized_problem_rx.cert_ops_of P\<^sub>T M))"

lemma numeric_wf_ground_cert_problem:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.wf_classical_problem numeric_P\<^sub>G_cert"
proof -
  interpret cr: certified_reachability_num P\<^sub>T M dc
    using certified_reachability_num_i[OF nonempty cert grounding_cert_num assms] .
  have pg_eq: "numeric_P\<^sub>G_cert = cr.wfg_num.numeric_ground_prob"
    unfolding numeric_P\<^sub>G_cert_def cr.cert_ops'_def by simp
  show ?thesis unfolding pg_eq using cr.wfg_num.numeric_ground_prob_wf by simp
qed

lemma numeric_ground_cert_plan_valid_iff:
  assumes "restrict_prob" "wf_classical_problem"
  shows "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>G_cert \<pi>s')"
proof -
  interpret cr: certified_reachability_num P\<^sub>T M dc
    using certified_reachability_num_i[OF nonempty cert grounding_cert_num assms] .
  have "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>N \<pi>s')"
    using assms normalization_valid_iff by simp
  also have "... \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>T \<pi>s')"
    using ast_classical_problem.def_translate_valid_iff_compact[OF normalization_wf[OF assms] P\<^sub>N_def_explicated_conj[OF assms]]
    unfolding P\<^sub>T_def by simp
  also have "... \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>G_cert \<pi>s')"
    unfolding numeric_P\<^sub>G_cert_def
    using cr.wfg_num.numeric_valid_classical_plan_iff[unfolded cr.cert_ops'_def] by simp
  finally show ?thesis .
qed

definition "numeric_reconstruct_plan_ground_cert \<pi>s \<equiv>
  reconstruct_plan_norm (restore_plan_def_translate
    (grounder.restore_ground_plan (canon (normalized_problem_rx.cert_ops_of P\<^sub>T M)) \<pi>s))"

text \<open>Plan restoration: a valid plan of the numeric grounded problem restores to a \<^emph>\<open>concrete\<close> valid
  plan of the original \<open>P\<close> (undo grounding \<open>\<rightarrow>\<close> def-translation \<open>\<rightarrow>\<close> normalization). Numeric twin of
  \<open>ground_cert_plan_reconstruct\<close>, using the numeric grounder's constructive restore
  \<open>numeric_valid_plan_left\<close> (\<^const>\<open>grounder.restore_ground_plan\<close>).\<close>
lemma numeric_ground_cert_plan_reconstruct:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>G_cert \<pi>s \<Longrightarrow>
    valid_classical_plan2 (numeric_reconstruct_plan_ground_cert \<pi>s)"
proof -
  assume p: "ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>G_cert \<pi>s"
  interpret cr: certified_reachability_num P\<^sub>T M dc
    using certified_reachability_num_i[OF nonempty cert grounding_cert_num assms] .
  let ?q = "grounder.restore_ground_plan (canon (normalized_problem_rx.cert_ops_of P\<^sub>T M)) \<pi>s"
  have "ast_classical_problem.valid_classical_plan2 P\<^sub>T ?q"
    using p[unfolded numeric_P\<^sub>G_cert_def] cr.wfg_num.numeric_valid_plan_left[unfolded cr.cert_ops'_def] by simp
  hence "ast_classical_problem.valid_classical_plan2 (ast_classical_problem.def_translate_prob P\<^sub>N) ?q"
    unfolding P\<^sub>T_def .
  hence "ast_classical_problem.valid_classical_plan2 P\<^sub>N (restore_plan_def_translate ?q)"
    using ast_classical_problem.restore_plan_def_translate_compact[OF normalization_wf[OF assms] P\<^sub>N_def_explicated_conj[OF assms]] by blast
  hence "valid_classical_plan2 (reconstruct_plan_norm (restore_plan_def_translate ?q))"
    using assms normalization_reconstruct by simp
  thus "valid_classical_plan2 (numeric_reconstruct_plan_ground_cert \<pi>s)"
    unfolding numeric_reconstruct_plan_ground_cert_def .
qed

end
end

end
