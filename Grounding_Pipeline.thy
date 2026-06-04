theory Grounding_Pipeline
  imports Type_Normalization.Type_Normalization_Semantics
    Goal_Normalization.Goal_Normalization_Semantics
    Definedness_Normalization.Definedness_Normalization_Semantics
    Precondition_Normalization.Precondition_Normalization_Semantics
    Definedness_Translation.Definedness_Translation_Semantics
    PDDL_Relaxation.PDDL_Relaxation_Semantics
    Reachability_Analysis Grounded_PDDL PDDL_to_STRIPS
begin

subsection \<open> Important theorems from individual grounding pipeline steps.
  Setting up compact notations for some of them to remove contexts. \<close>

context ast_classical_problem begin
thm detype_classical_prob_sel
thm restrict_classical_problem2.detype_classical_prob_wf
lemma detype_prob_wf_compact:
  "restrict_prob \<Longrightarrow> wf_classical_problem
  \<Longrightarrow> ast_classical_problem.wf_classical_problem detype_classical_prob"
  using restrict_classical_problem2.detype_classical_prob_wf
  using restrict_classical_problem2.intro restrict_classical_problem.intro
        restrict_classical_problem_axioms.intro wf_ast_classical_problem.intro
  by auto
lemma detyped_valid_iff_compact:
  "restrict_prob \<Longrightarrow> wf_classical_problem
  \<Longrightarrow> valid_classical_plan2 \<pi>s \<longleftrightarrow> ast_classical_problem.valid_classical_plan2 detype_classical_prob \<pi>s"
  using restrict_classical_problem2.detyped_valid_iff
  using restrict_classical_problem2.intro restrict_classical_problem.intro
        restrict_classical_problem_axioms.intro wf_ast_classical_problem.intro
  by auto

thm ast_classical_problem.degoal_prob_sel
lemma degoal_prob_wf_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.wf_classical_problem (degoal_prob)"
  using wf_ast_classical_problem3.degoal_prob_wf
  using wf_ast_classical_problem3_def wf_ast_classical_problem.intro by simp
lemma degoal_plan_restore_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.valid_classical_plan2 degoal_prob \<pi>s \<Longrightarrow> valid_classical_plan2 (restore_plan_degoal \<pi>s)"
  using wf_ast_classical_problem3.valid_classical_plan2_left
  using wf_ast_classical_problem3_def wf_ast_classical_problem.intro by simp
lemma degoaled_valid_iff_compact:
  "wf_classical_problem \<Longrightarrow> (\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 degoal_prob \<pi>s')"
  using wf_ast_classical_problem3.degoaled_valid_iff
  using wf_ast_classical_problem3_def wf_ast_classical_problem.intro by simp

thm ast_classical_problem.explicate_def_prob_sel
lemma explicate_def_prob_wf_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.wf_classical_problem explicate_def_prob"
  using wf_ast_classical_problem_de.explicate_def_prob_wf
  using wf_ast_classical_problem_de_def wf_ast_classical_problem.intro by simp
lemma explicate_def_def_explicated_conj_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.def_explicated_conj_prob explicate_def_prob"
  using def_explicated_conj_explicate_def_prob .
lemma explicate_def_valid_iff_compact:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 explicate_def_prob \<pi>s')"
  by (rule ast_classical_problem_de.explicate_valid_iff)
lemma restore_plan_explicate_valid_compact:
  "ast_classical_problem.valid_classical_plan2 explicate_def_prob \<pi>s \<Longrightarrow>
    valid_classical_plan2 (restore_plan_explicate \<pi>s)"
  by (rule ast_classical_problem_de.explicate_plan_restore)

thm ast_classical_problem.split_prob_sel
thm ast_classical_problem4.prec_normed_dom
lemma split_prob_wf_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow> ast_classical_problem.wf_classical_problem (split_prob)"
  using wf_ast_classical_problem4.split_prob_wf
  unfolding wf_ast_classical_problem4_def
            def_explicated_conj_problem_def
            def_explicated_conj_problem_axioms_def
            wf_ast_classical_problem_def
  by simp
lemma split_valid_iff_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow>
    (\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 split_prob \<pi>s')"
  using wf_ast_classical_problem4.split_valid_iff
  unfolding wf_ast_classical_problem4_def
            def_explicated_conj_problem_def
            def_explicated_conj_problem_axioms_def
            wf_ast_classical_problem_def
  by simp
lemma restore_plan_split_valid_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow>
    ast_classical_problem.valid_classical_plan2 split_prob \<pi>s \<Longrightarrow> valid_classical_plan2 (restore_plan_split \<pi>s)"
  using wf_ast_classical_problem4.restore_plan_split_valid
  unfolding wf_ast_classical_problem4_def
            def_explicated_conj_problem_def
            def_explicated_conj_problem_axioms_def
            wf_ast_classical_problem_def
  by simp

text \<open> Definedness translation preserves well-formedness and normalization. \<close>
lemma def_translate_prob_wf_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.wf_classical_problem def_translate_prob"
  using wf_ast_classical_problem_dt.def_translate_prob_wf
  using wf_ast_classical_problem_dt_def wf_ast_classical_problem.intro by simp
lemma def_translate_normed_compact:
  "normalized_prob \<Longrightarrow> ast_classical_problem.normalized_prob def_translate_prob"
  by (rule def_translate_normalized)

lemma relax_wf_relaxed_compact:
  "wf_classical_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    ast_classical_problem.relaxed_prob relax_prob \<and> ast_classical_problem.wf_classical_problem relax_prob"
  using normalized_problem_rx.relax_relaxes normalized_problem_rx.relax_wf
  unfolding normalized_problem_rx_def normalized_problem_def' by simp
lemma relax_normed_compact:
  "wf_classical_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    ast_classical_problem.normalized_prob relax_prob"
  using normalized_problem_rx.relax_normed
  unfolding normalized_problem_rx_def normalized_problem_def' by simp
lemma relax_achievables_compact:
  "wf_classical_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    {a. achievable a} \<subseteq> {a. ast_classical_problem.achievable relax_prob a}"
  using normalized_problem_rx.relax_achievables
  unfolding normalized_problem_rx_def normalized_problem_def'
  by simp
lemma relax_applicables_compact:
  "wf_classical_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    {\<pi>. applicable \<pi>} \<subseteq> {\<pi>. ast_classical_problem.applicable relax_prob \<pi>}"
  using normalized_problem_rx.relax_applicables
  unfolding normalized_problem_rx_def normalized_problem_def'    
  by simp

(* unproven *)
thm relaxed_problem.found_facts_achievable
thm relaxed_problem.found_pactions_applicable

thm grounder.ground_prob_grounded
thm wf_grounder.ground_prob_wf
lemma (in wf_grounder) ground_prob_normed:
  assumes "normalized_prob"
  shows "ast_classical_problem.normalized_prob ground_prob"
  sorry
thm wf_grounder.valid_classical_plan_iff
thm wf_grounder.valid_classical_plan_left


lemma wf_as_strips_compact:
  "wf_classical_problem \<Longrightarrow> grounded_prob \<Longrightarrow> normalized_prob \<Longrightarrow> is_valid_problem_strips as_strips"
  using grounded_normalized_problem.wf_as_strips
  unfolding grounded_normalized_problem_def grounded_normalized_problem_axioms_def
  unfolding grounded_problem_def grounded_problem_axioms_def wf_ast_classical_problem_def
  unfolding normalized_prob_def by blast
  

end

subsection \<open> Normalization correctness \<close>

context ast_classical_problem begin

text \<open>\<open>P\<^sub>X\<close>: the explicated-and-degoaled-and-detyped problem, fed to the split step.\<close>
definition "P\<^sub>X \<equiv> ast_classical_problem.explicate_def_prob
  (ast_classical_problem.degoal_prob detype_classical_prob)"

definition "P\<^sub>N \<equiv> ast_classical_problem.split_prob P\<^sub>X"

definition "reconstruct_plan_norm \<pi>s \<equiv>
  ast_domain.restore_plan_degoal detype_dom
    (restore_plan_explicate
      (ast_domain.restore_plan_split
        (ast_classical_problem.explicate_def_dom
          (ast_classical_problem.degoal_prob detype_prob))
        \<pi>s))"

text \<open> goal and precondition normalization preserve type normalization \<close>
lemma goal_norm_preserves_typeless:
  "typeless_classical_problem \<Longrightarrow> ast_classical_problem.typeless_classical_problem (degoal_prob)"
  unfolding ast_classical_problem.typeless_classical_problem_def ast_classical_domain.typeless_classical_domain_def
    domain_signature.typeless_domain_signature_def
    degoal_prob_sel degoal_dom_sel
  unfolding goal_pred_decl_def goal_ac_def by auto

lemma prec_norm_preserves_typeless:
  "typeless_classical_problem \<Longrightarrow> ast_classical_problem.typeless_classical_problem (split_prob)"
  unfolding ast_classical_problem.typeless_classical_problem_def ast_classical_domain.typeless_classical_domain_def
    domain_signature.typeless_domain_signature_def
    split_prob_sel split_dom_sel
  unfolding split_acs_def using split_ac_sel(2) by auto

text \<open> type and precondition normalization preserve goal normalization \<close>
lemma type_norm_preserves_goal_conj:
  "is_conj (goal P) \<Longrightarrow> is_conj (goal detype_classical_prob)"
  unfolding detype_classical_prob_sel .

lemma prec_norm_preserves_goal_conj:
  "is_conj (goal P) \<Longrightarrow> is_conj (goal split_prob)"
  unfolding split_prob_sel .

text \<open> Due to Either-types, type normalization can introduce disjunctions into preconditions,
  and it can thus potentially break precondition normalization. \<close>

text \<open> Goal normalization only preserves precondition normalization if the goal is a
  pure conjunction.\<close>

lemma goal_norm_preserves_prec_norm:
  assumes "prec_normed_dom"
    "is_conj (goal P)"
  shows "ast_classical_domain.prec_normed_dom (domain degoal_prob)"
  using assms(1) unfolding ast_classical_domain.prec_normed_dom_def
  unfolding degoal_prob_sel degoal_dom_sel
  unfolding goal_ac_def term_goal_def
  using map_preserves_isconj assms(2) by auto

theorem normalization_normalizes:
  "ast_classical_problem.normalized_prob P\<^sub>N"
  unfolding ast_classical_problem.normalized_prob_def P\<^sub>N_def
  using ast_classical_problem2.prob_detyped
  using ast_classical_problem.degoal_prob_sel(4) ast_classical_problem.goal_norm_preserves_typeless
  using ast_classical_problem.prec_norm_preserves_typeless ast_classical_problem.prec_norm_preserves_goal_conj
    ast_classical_problem4.prec_normed_dom
  by (simp add: ast_classical_problem.split_prob_sel(1))

theorem normalization_wf:
  "restrict_prob \<Longrightarrow> wf_classical_problem \<Longrightarrow> ast_classical_problem.wf_classical_problem P\<^sub>N"
  unfolding P\<^sub>N_def P\<^sub>X_def
  using detype_prob_wf_compact
        ast_classical_problem.degoal_prob_wf_compact
        ast_classical_problem.explicate_def_prob_wf_compact
        ast_classical_problem.explicate_def_def_explicated_conj_compact
        ast_classical_problem.split_prob_wf_compact
  by simp

theorem normalization_valid_iff:
  "restrict_prob \<Longrightarrow> wf_classical_problem \<Longrightarrow>
    (\<exists>\<pi>s. valid_classical_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan P\<^sub>N \<pi>s')"
  unfolding P\<^sub>N_def P\<^sub>X_def
  using detype_prob_wf_compact
        ast_classical_problem.degoal_prob_wf_compact
        ast_classical_problem.explicate_def_prob_wf_compact
        ast_classical_problem.explicate_def_def_explicated_conj_compact
        detyped_valid_iff_compact
        ast_classical_problem.degoaled_valid_iff_compact
        ast_classical_problem.explicate_def_valid_iff_compact
        ast_classical_problem.split_valid_iff_compact
  by simp

theorem normalization_reconstruct:
  "restrict_prob \<Longrightarrow> wf_classical_problem \<Longrightarrow>
    ast_classical_problem.valid_classical_plan P\<^sub>N \<pi>s \<Longrightarrow> valid_classical_plan (reconstruct_plan_norm \<pi>s)"
  unfolding P\<^sub>N_def P\<^sub>X_def reconstruct_plan_norm_def
  using detype_prob_wf_compact
        ast_classical_problem.degoal_prob_wf_compact
        ast_classical_problem.explicate_def_prob_wf_compact
        ast_classical_problem.explicate_def_def_explicated_conj_compact
        ast_classical_problem.restore_plan_split_valid_compact
        ast_classical_problem.restore_plan_explicate_valid_compact
        ast_classical_problem.degoal_plan_restore_compact
        detyped_valid_iff_compact
  by (metis ast_classical_problem.degoal_prob_sel(1) detype_prob_sel(1)
            ast_classical_problem.explicate_def_prob_sel(1))

end

subsection \<open> Relaxation \<close>

context ast_classical_problem begin

definition "P\<^sub>T \<equiv> ast_classical_problem.def_translate_prob P\<^sub>N"

definition "P\<^sub>R \<equiv> ast_classical_problem.relax_prob P\<^sub>T"

lemma relaxation_applicables:
  assumes "restrict_prob" "wf_classical_problem"
  shows "{\<pi>. ast_classical_problem.applicable P\<^sub>N \<pi>} \<subseteq> {\<pi>. ast_classical_problem.applicable P\<^sub>R \<pi>}"
  unfolding P\<^sub>R_def
  using assms normalization_normalizes normalization_wf ast_classical_problem.relax_applicables_compact by simp

lemma relaxation_achievables:
  assumes "restrict_prob" "wf_classical_problem"
  shows "{a. ast_classical_problem.achievable P\<^sub>N a} \<subseteq> {a. ast_classical_problem.achievable P\<^sub>R a}"
  unfolding P\<^sub>R_def
  using assms normalization_normalizes normalization_wf ast_classical_problem.relax_achievables_compact by simp

lemma relaxation_wf_relaxed_normed:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.wf_classical_problem P\<^sub>R" "ast_classical_problem.relaxed_prob P\<^sub>R" "ast_classical_problem.normalized_prob P\<^sub>R"
  unfolding P\<^sub>R_def
  using assms normalization_normalizes normalization_wf
  using ast_classical_problem.relax_wf_relaxed_compact ast_classical_problem.relax_normed_compact
  by blast+

subsection \<open> Reachability Analysis \<close>

abbreviation "all_facts \<equiv> remdups (snd (ast_classical_problem.semi_naive_eval P\<^sub>R))"
abbreviation "all_pactions \<equiv> fst (ast_classical_problem.semi_naive_eval P\<^sub>R)"


thm relaxed_problem.found_facts_achievable

lemma all_facts_solved:
  assumes "restrict_prob" "wf_classical_problem"
  shows "set all_facts = {f. ast_classical_problem.achievable P\<^sub>R f}"
  using assms relaxed_problem.found_facts_achievable
  using relaxation_wf_relaxed_normed[OF assms]
  by (simp add: normalized_problem_def' relaxed_problem.intro relaxed_problem_axioms_def)

lemma wf_grounder_args:
  assumes "restrict_prob" "wf_classical_problem"
  shows "wf_grounder P\<^sub>N all_facts all_pactions"
  unfolding wf_grounder_def apply (intro conjI)
  using assms normalization_wf apply blast
          apply simp
  using relaxation_achievables[OF assms] all_facts_solved[OF assms] apply argo
  using relaxation_achievables[OF assms] all_facts_solved[OF assms]
    wf_ast_classical_problem.achievable_wf normalization_wf[OF assms]
    wf_ast_classical_problem_def
  apply (metis P\<^sub>R_def assms ast_domain_rx.rx_wf_fmla_atom ast_classical_problem.relax_prob_sel(1) ast_classical_problem_rx.rx_objT mem_Collect_eq relaxation_wf_relaxed_normed(1))
  sorry

subsection \<open> Grounding \<close>

definition "P\<^sub>G \<equiv> grounder.ground_prob P\<^sub>N all_facts all_pactions"
definition "reconstruct_plan_ground \<pi>s =
  reconstruct_plan_norm (grounder.restore_ground_plan all_pactions \<pi>s)"

lemma wf_ground_normed_problem:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.wf_classical_problem P\<^sub>G" "ast_classical_problem.normalized_prob P\<^sub>G"
    "ast_classical_problem.grounded_prob P\<^sub>G"
  using assms wf_grounder_args normalization_normalizes
  using wf_grounder.ground_prob_wf wf_grounder.ground_prob_normed
    grounder.ground_prob_grounded
  by (simp_all add: P\<^sub>G_def)

lemma ground_plan_valid_iff:
  assumes "restrict_prob" "wf_classical_problem"
  shows "(\<exists>\<pi>s. valid_classical_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan P\<^sub>G \<pi>s')"
  using assms normalization_valid_iff wf_grounder_args
  using wf_grounder.valid_classical_plan_iff
  unfolding P\<^sub>G_def by blast

lemma ground_plan_reconstruct:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.valid_classical_plan P\<^sub>G \<pi>s \<Longrightarrow>
    valid_classical_plan (reconstruct_plan_ground \<pi>s)"
  using assms normalization_reconstruct wf_grounder_args
  using wf_grounder.valid_classical_plan_left normalization_reconstruct
  unfolding P\<^sub>G_def reconstruct_plan_ground_def by simp

subsection \<open> Conversion to STRIPS \<close>
definition "P\<^sub>S \<equiv> ast_classical_problem.as_strips P\<^sub>G"
definition "reconstruct_pipeline_plan ops \<equiv>
  reconstruct_plan_ground (ast_classical_problem.restore_pddl_plan P\<^sub>G ops)"

lemma wf_as_strips:
  assumes "restrict_prob" "wf_classical_problem"
  shows "is_valid_problem_strips P\<^sub>S"
  using assms ast_classical_problem.wf_as_strips_compact
  using wf_ground_normed_problem
  unfolding P\<^sub>S_def by blast

lemma strips_plan_reconstruct:
  assumes "restrict_prob" "wf_classical_problem"
  shows "is_serial_solution_for_problem P\<^sub>S ops \<Longrightarrow>
    valid_classical_plan (reconstruct_pipeline_plan ops)"
  oops

lemma strips_plan_iff:
  assumes "restrict_prob" "wf_classical_problem"
  shows "(\<exists>ops. is_serial_solution_for_problem P\<^sub>S ops) \<longleftrightarrow>
    (\<exists>\<pi>s. valid_classical_plan \<pi>s)"
  oops

end
end