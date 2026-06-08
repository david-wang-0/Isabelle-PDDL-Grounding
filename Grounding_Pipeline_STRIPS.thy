theory Grounding_Pipeline_STRIPS
  imports Grounding_Pipeline_Numeric "PDDL_to_STRIPS/Classical_PDDL_to_STRIPS"
begin

text \<open>The numeric-free specialization of the grounding pipeline: it imports the general
  (with-numerics) pipeline \<^verbatim>\<open>Grounding_Pipeline_Numeric\<close> and, on top of the certificate-grounded
  problem \<^term>\<open>P\<^sub>G_cert\<close>, converts it to STRIPS. This branch requires \<^const>\<open>ast_classical_problem.num_free_prob\<close>.\<close>

context ast_classical_problem begin

lemma wf_as_strips_compact:
  "wf_classical_problem \<Longrightarrow> grounded_prob \<Longrightarrow> normalized_prob \<Longrightarrow> num_free_prob \<Longrightarrow> is_valid_problem_strips as_strips"
  using grounded_normalized_numeric_free_problem.wf_as_strips
  unfolding grounded_normalized_numeric_free_problem_def
            grounded_normalized_problem_def grounded_normalized_problem_axioms_def
            grounded_problem_def grounded_problem_axioms_def wf_ast_classical_problem_def
            numeric_free_problem_def
            normalized_prob_def by blast

context
  fixes cert :: certificate
  assumes admissible_cert: "pddl_datalog.admissible (ast_classical_problem.relax_prob P\<^sub>T) cert"
      and grounding_cert: "normalized_problem_rx.grounding_checks P\<^sub>T cert"
begin

subsection \<open> Conversion to STRIPS (Certificate-based) \<close>

definition "P\<^sub>S_cert \<equiv> ast_classical_problem.as_strips (P\<^sub>G_cert cert)"
definition "reconstruct_pipeline_plan_cert ops \<equiv>
  reconstruct_plan_ground_cert cert (ast_classical_problem.restore_pddl_plan (P\<^sub>G_cert cert) ops)"

lemma wf_as_strips_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "is_valid_problem_strips P\<^sub>S_cert"
proof -
  have nf: "ast_classical_problem.num_free_prob (P\<^sub>G_cert cert)"
    using ground_cert_num_free[OF admissible_cert grounding_cert assms] .
  show ?thesis
    unfolding P\<^sub>S_cert_def
    using assms ast_classical_problem.wf_as_strips_compact
          wf_ground_cert_problem[OF admissible_cert grounding_cert assms] nf by blast
qed

lemma strips_plan_reconstruct_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "is_serial_solution_for_problem P\<^sub>S_cert ops \<Longrightarrow>
    valid_classical_plan2 (reconstruct_pipeline_plan_cert ops)"
  oops

lemma strips_plan_iff_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "(\<exists>ops. is_serial_solution_for_problem P\<^sub>S_cert ops) \<longleftrightarrow>
    (\<exists>\<pi>s. valid_classical_plan2 \<pi>s)"
  oops

end

end
end
