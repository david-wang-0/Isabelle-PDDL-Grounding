theory Classical_Goal_Normalization_Num_Free
  imports Classical_Goal_Normalization Grounding_Classical_Common.Numeric_Free
begin

section \<open>The goal-normalization stage maintains numeric-freeness\<close>

text \<open>Stage-local preservation property, the second link of the input-side numeric-freeness chain
  composed in \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close>: degoaling adds one action whose precondition is the
  (numeric-free) goal under the \<^const>\<open>term.CONST\<close> lift and whose effect adds the fresh nullary
  goal predicate; the new goal is that same predicate atom. The initial state is untouched.\<close>

lemma (in ast_classical_problem) num_free_ac_goal_ac:
  assumes "num_free_fmla g"
  shows "num_free_ac (goal_ac g)"
  using assms unfolding num_free_ac_def goal_ac_def by simp

theorem (in ast_classical_problem) degoal_prob_num_free:
  assumes nf: num_free_prob
  shows "ast_classical_problem.num_free_prob degoal_prob"
proof -
  have tg: "num_free_fmla term_goal"
    using nf unfolding num_free_prob_def term_goal_def by simp
  have dom: "ast_classical_domain.num_free_dom D3"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions D3)"
    hence "a = goal_ac term_goal \<or> a \<in> set (actions D)" unfolding degoal_dom_sel by simp
    thus "num_free_ac a"
      using num_free_ac_goal_ac[OF tg] nf unfolding num_free_prob_def num_free_dom_def by blast
  qed
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom nf unfolding num_free_prob_def by simp
qed

end
