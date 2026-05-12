theory Grounding_Pipeline
  imports "Type_Normalization/Type_Normalization_Semantics" 
    "Goal_Normalization/Goal_Normalization_Semantics" Precondition_Normalization
    PDDL_Relaxation Reachability_Analysis Grounded_PDDL PDDL_to_STRIPS
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

thm ast_problem.degoal_prob_sel
lemma degoal_prob_wf_compact:
  "wf_problem \<Longrightarrow> ast_problem.wf_problem (degoal_prob)"
  using wf_ast_problem3.degoal_prob_wf
  using wf_ast_problem3_def wf_ast_problem.intro by simp
lemma degoal_plan_restore_compact:
  "wf_problem \<Longrightarrow> ast_problem.valid_plan degoal_prob \<pi>s \<Longrightarrow> valid_plan (restore_plan_degoal \<pi>s)"
  using wf_ast_problem3.valid_plan_left
  using wf_ast_problem3_def wf_ast_problem.intro by simp
lemma degoaled_valid_iff_compact:
  "wf_problem \<Longrightarrow> (\<exists>\<pi>s. valid_plan \<pi>s) = (\<exists>\<pi>s'. ast_problem.valid_plan degoal_prob \<pi>s')"
  using wf_ast_problem3.degoaled_valid_iff
  using wf_ast_problem3_def wf_ast_problem.intro by simp

thm ast_problem.split_prob_sel
thm ast_problem4.prec_normed_dom
lemma split_prob_wf_compact:
  "wf_problem \<Longrightarrow> ast_problem.wf_problem (split_prob)"
  using wf_ast_problem4.split_prob_wf
  using wf_ast_problem4_def wf_ast_problem.intro by simp
lemma split_valid_iff_compact:
  "wf_problem \<Longrightarrow> (\<exists>\<pi>s. valid_plan \<pi>s) = (\<exists>\<pi>s'. ast_problem.valid_plan split_prob \<pi>s')"
  using wf_ast_problem4.split_valid_iff
  using wf_ast_problem4_def wf_ast_problem.intro by simp
lemma restore_plan_split_valid_compact:
  "wf_problem \<Longrightarrow> ast_problem.valid_plan split_prob \<pi>s \<Longrightarrow> valid_plan (restore_plan_split \<pi>s)"
  using wf_ast_problem4.restore_plan_split_valid
  using wf_ast_problem4_def wf_ast_problem.intro by simp

lemma relax_wf_relaxed_compact:
  "wf_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    ast_problem.relaxed_prob relax_prob \<and> ast_problem.wf_problem relax_prob"
  using normalized_problem_rx.relax_relaxes normalized_problem_rx.relax_wf
  unfolding normalized_problem_rx_def normalized_problem_def' by simp
lemma relax_normed_compact:
  "wf_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    ast_problem.normalized_prob relax_prob"
  using normalized_problem_rx.relax_normed
  unfolding normalized_problem_rx_def normalized_problem_def' by simp
lemma relax_achievables_compact:
  "wf_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    {a. achievable a} \<subseteq> {a. ast_problem.achievable relax_prob a}"
  using normalized_problem_rx.relax_achievables
  unfolding normalized_problem_rx_def normalized_problem_def'
  by simp
lemma relax_applicables_compact:
  "wf_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    {\<pi>. applicable \<pi>} \<subseteq> {\<pi>. ast_problem.applicable relax_prob \<pi>}"
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
  shows "ast_problem.normalized_prob ground_prob"
  sorry
thm wf_grounder.valid_plan_iff
thm wf_grounder.valid_plan_left


lemma wf_as_strips_compact:
  "wf_problem \<Longrightarrow> grounded_prob \<Longrightarrow> normalized_prob \<Longrightarrow> is_valid_problem_strips as_strips"
  using grounded_normalized_problem.wf_as_strips
  unfolding grounded_normalized_problem_def grounded_normalized_problem_axioms_def
  unfolding grounded_problem_def grounded_problem_axioms_def wf_ast_problem_def
  unfolding normalized_prob_def by blast
  

end

subsection \<open> Normalization correctness \<close>

context ast_problem begin

definition "P\<^sub>N \<equiv> ast_problem.split_prob (ast_problem.degoal_prob detype_prob)"

definition "reconstruct_plan_norm \<pi>s \<equiv>
  ast_domain.restore_plan_degoal detype_dom
    (ast_domain.restore_plan_split (ast_problem.degoal_dom detype_prob) \<pi>s)"

text \<open> goal and precondition normalization preserve type normalization \<close>
lemma goal_norm_preserves_typeless:
  "typeless_prob \<Longrightarrow> ast_problem.typeless_prob (degoal_prob)"
  unfolding ast_problem.typeless_prob_def ast_domain.typeless_dom_def
    degoal_prob_sel degoal_dom_sel
  unfolding goal_pred_decl_def goal_ac_def by auto

lemma prec_norm_preserves_typeless:
  "typeless_prob \<Longrightarrow> ast_problem.typeless_prob (split_prob)"
  unfolding ast_problem.typeless_prob_def ast_domain.typeless_dom_def
    split_prob_sel split_dom_sel
  unfolding split_acs_def using split_ac_sel(2) by auto

text \<open> type and precondition normalization preserve goal normalization \<close>
lemma type_norm_preserves_goal_conj:
  "is_conj (goal P) \<Longrightarrow> is_conj (goal detype_prob)"
  unfolding detype_prob_sel .

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
  shows "ast_domain.prec_normed_dom (domain degoal_prob)"
  using assms(1) unfolding ast_domain.prec_normed_dom_def
  unfolding degoal_prob_sel degoal_dom_sel
  unfolding goal_ac_def term_goal_def
  using map_preserves_isconj assms(2) by auto

theorem normalization_normalizes:
  "ast_problem.normalized_prob P\<^sub>N"
  unfolding ast_problem.normalized_prob_def P\<^sub>N_def
  using ast_problem2.prob_detyped
  using ast_problem.degoal_prob_sel(4) ast_problem.goal_norm_preserves_typeless
  using ast_problem.prec_norm_preserves_typeless ast_problem.prec_norm_preserves_goal_conj
    ast_problem4.prec_normed_dom
  by (simp add: ast_problem.split_prob_sel(1))

theorem normalization_wf:
  "restrict_prob \<Longrightarrow> wf_problem \<Longrightarrow> ast_problem.wf_problem P\<^sub>N"
  unfolding P\<^sub>N_def
  using detype_prob_wf_compact ast_problem.degoal_prob_wf_compact ast_problem.split_prob_wf_compact
  by simp

theorem normalization_valid_iff:
  "restrict_prob \<Longrightarrow> wf_problem \<Longrightarrow>
    (\<exists>\<pi>s. valid_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_problem.valid_plan P\<^sub>N \<pi>s')"
  unfolding P\<^sub>N_def
  using detype_prob_wf_compact ast_problem.degoal_prob_wf_compact
  using detyped_valid_iff_compact ast_problem.degoaled_valid_iff_compact
    ast_problem.split_valid_iff_compact by simp

theorem normalization_reconstruct:
  "restrict_prob \<Longrightarrow> wf_problem \<Longrightarrow>
    ast_problem.valid_plan P\<^sub>N \<pi>s \<Longrightarrow> valid_plan (reconstruct_plan_norm \<pi>s)"
  unfolding P\<^sub>N_def reconstruct_plan_norm_def
  using detype_prob_wf_compact ast_problem.degoal_prob_wf_compact
  using ast_problem.restore_plan_split_valid_compact ast_problem.degoal_plan_restore_compact
    detyped_valid_iff_compact
  by (metis ast_problem.degoal_prob_sel(1) detype_prob_sel(1))

end

subsection \<open> Relaxation \<close>

context ast_problem begin

definition "P\<^sub>R \<equiv> ast_problem.relax_prob P\<^sub>N"

lemma relaxation_applicables:
  assumes "restrict_prob" "wf_problem"
  shows "{\<pi>. ast_problem.applicable P\<^sub>N \<pi>} \<subseteq> {\<pi>. ast_problem.applicable P\<^sub>R \<pi>}"
  unfolding P\<^sub>R_def
  using assms normalization_normalizes normalization_wf ast_problem.relax_applicables_compact by simp

lemma relaxation_achievables:
  assumes "restrict_prob" "wf_problem"
  shows "{a. ast_problem.achievable P\<^sub>N a} \<subseteq> {a. ast_problem.achievable P\<^sub>R a}"
  unfolding P\<^sub>R_def
  using assms normalization_normalizes normalization_wf ast_problem.relax_achievables_compact by simp

lemma relaxation_wf_relaxed_normed:
  assumes "restrict_prob" "wf_problem"
  shows "ast_problem.wf_problem P\<^sub>R" "ast_problem.relaxed_prob P\<^sub>R" "ast_problem.normalized_prob P\<^sub>R"
  unfolding P\<^sub>R_def
  using assms normalization_normalizes normalization_wf
  using ast_problem.relax_wf_relaxed_compact ast_problem.relax_normed_compact
  by blast+

subsection \<open> Reachability Analysis \<close>

abbreviation "all_facts \<equiv> remdups (snd (ast_problem.semi_naive_eval P\<^sub>R))"
abbreviation "all_pactions \<equiv> fst (ast_problem.semi_naive_eval P\<^sub>R)"


thm relaxed_problem.found_facts_achievable

lemma all_facts_solved:
  assumes "restrict_prob" "wf_problem"
  shows "set all_facts = {f. ast_problem.achievable P\<^sub>R f}"
  using assms relaxed_problem.found_facts_achievable
  using relaxation_wf_relaxed_normed[OF assms]
  by (simp add: normalized_problem_def' relaxed_problem.intro relaxed_problem_axioms_def)

lemma wf_grounder_args:
  assumes "restrict_prob" "wf_problem"
  shows "wf_grounder P\<^sub>N all_facts all_pactions"
  unfolding wf_grounder_def apply (intro conjI)
  using assms normalization_wf apply blast
          apply simp
  using relaxation_achievables[OF assms] all_facts_solved[OF assms] apply argo
  using relaxation_achievables[OF assms] all_facts_solved[OF assms]
    wf_ast_problem.achievable_wf normalization_wf[OF assms]
    wf_ast_problem_def
  apply (metis P\<^sub>R_def assms ast_domain_rx.rx_wf_fmla_atom ast_problem.relax_prob_sel(1) ast_problem_rx.rx_objT mem_Collect_eq relaxation_wf_relaxed_normed(1))
  sorry

subsection \<open> Grounding \<close>

definition "P\<^sub>G \<equiv> grounder.ground_prob P\<^sub>N all_facts all_pactions"
definition "reconstruct_plan_ground \<pi>s =
  reconstruct_plan_norm (grounder.restore_ground_plan all_pactions \<pi>s)"

lemma wf_ground_normed_problem:
  assumes "restrict_prob" "wf_problem"
  shows "ast_problem.wf_problem P\<^sub>G" "ast_problem.normalized_prob P\<^sub>G"
    "ast_problem.grounded_prob P\<^sub>G"
  using assms wf_grounder_args normalization_normalizes
  using wf_grounder.ground_prob_wf wf_grounder.ground_prob_normed
    grounder.ground_prob_grounded
  by (simp_all add: P\<^sub>G_def)

lemma ground_plan_valid_iff:
  assumes "restrict_prob" "wf_problem"
  shows "(\<exists>\<pi>s. valid_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_problem.valid_plan P\<^sub>G \<pi>s')"
  using assms normalization_valid_iff wf_grounder_args
  using wf_grounder.valid_plan_iff
  unfolding P\<^sub>G_def by blast

lemma ground_plan_reconstruct:
  assumes "restrict_prob" "wf_problem"
  shows "ast_problem.valid_plan P\<^sub>G \<pi>s \<Longrightarrow>
    valid_plan (reconstruct_plan_ground \<pi>s)"
  using assms normalization_reconstruct wf_grounder_args
  using wf_grounder.valid_plan_left normalization_reconstruct
  unfolding P\<^sub>G_def reconstruct_plan_ground_def by simp

subsection \<open> Conversion to STRIPS \<close>
definition "P\<^sub>S \<equiv> ast_problem.as_strips P\<^sub>G"
definition "reconstruct_pipeline_plan ops \<equiv>
  reconstruct_plan_ground (ast_problem.restore_pddl_plan P\<^sub>G ops)"

lemma wf_as_strips:
  assumes "restrict_prob" "wf_problem"
  shows "is_valid_problem_strips P\<^sub>S"
  using assms ast_problem.wf_as_strips_compact
  using wf_ground_normed_problem
  unfolding P\<^sub>S_def by blast

lemma strips_plan_reconstruct:
  assumes "restrict_prob" "wf_problem"
  shows "is_serial_solution_for_problem P\<^sub>S ops \<Longrightarrow>
    valid_plan (reconstruct_pipeline_plan ops)"
  oops

lemma strips_plan_iff:
  assumes "restrict_prob" "wf_problem"
  shows "(\<exists>ops. is_serial_solution_for_problem P\<^sub>S ops) \<longleftrightarrow>
    (\<exists>\<pi>s. valid_plan \<pi>s)"
  oops

end
end