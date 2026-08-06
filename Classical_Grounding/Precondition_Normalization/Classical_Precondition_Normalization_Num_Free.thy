theory Classical_Precondition_Normalization_Num_Free
  imports Classical_Precondition_Normalization Grounding_Classical_Common.Numeric_Free
begin

section \<open>The precondition-splitting stage maintains numeric-freeness\<close>

text \<open>Stage-local preservation property, the fourth link of the input-side numeric-freeness chain
  composed in \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close>: splitting copies each action once per DNF disjunct of
  its precondition, keeping the effect verbatim. Every disjunct's atom set is a subset of the
  original's (\<open>dnf_list_atoms\<close>), so numeric-freeness --- an atom-set property --- is inherited by
  each copy.\<close>

lemma num_free_fmla_dnf_list:
  assumes "num_free_fmla \<phi>"
      and "c \<in> set (dnf_list \<phi>)"
  shows "num_free_fmla c"
proof (rule num_free_fmla_atomsI)
  fix a assume a: "a \<in> atoms c"
  have "atoms c \<subseteq> atoms \<phi>" using dnf_list_atoms assms(2) by fast
  hence "a \<in> atoms \<phi>" using a by blast
  thus "\<not> is_numeric_atom a" using num_free_fmla_atoms[OF assms(1)] by blast
qed

lemma (in ast_classical_domain) num_free_ac_split_ac:
  assumes nfa: "num_free_ac a"
      and mem: "a' \<in> set (split_ac a)"
  shows "num_free_ac a'"
proof -
  have "num_free_fmla (ac_pre a')"
    using num_free_fmla_dnf_list split_ac_sel(3)[OF mem] nfa
    unfolding num_free_ac_def by blast
  thus ?thesis using nfa split_ac_sel(4)[OF mem] unfolding num_free_ac_def by simp
qed

theorem (in ast_classical_problem) split_prob_num_free:
  assumes nf: num_free_prob
  shows "ast_classical_problem.num_free_prob split_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom D4"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a' assume "a' \<in> set (actions D4)"
    then obtain a where a: "a \<in> set (actions D)"
      and a': "a' \<in> set (split_ac a)"
      unfolding split_dom_sel split_acs_def by auto
    have "num_free_ac a" using nf a unfolding num_free_prob_def num_free_dom_def by blast
    thus "num_free_ac a'" using a' by (rule num_free_ac_split_ac)
  qed
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom nf unfolding num_free_prob_def by simp
qed

end
