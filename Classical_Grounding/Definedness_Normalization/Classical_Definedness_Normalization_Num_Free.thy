theory Classical_Definedness_Normalization_Num_Free
  imports Classical_Definedness_Normalization Grounding_Classical_Common.Numeric_Free
begin

section \<open>The definedness-explication stage maintains numeric-freeness\<close>

text \<open>Stage-local preservation property, the third link of the input-side numeric-freeness chain
  composed in \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close> --- the stage with actual content.
  \<^const>\<open>explicate_def_fmla\<close> conjoins one reflexive numeric equality per primitive numeric
  expression of the formula and one nonzero witness \<open>\<^bold>\<not>(y = 0)\<close> per divisor sub-expression. Both
  lists are enumerated \<^emph>\<open>from the numeric atoms\<close>
  (\<^const>\<open>atom_enumerate_primitive_numeric_expressions\<close> and
  \<^const>\<open>atom_enumerate_divisor_expressions\<close> return \<^term>\<open>[]\<close> on \<^const>\<open>predAtm\<close>/\<^const>\<open>eqAtm\<close>), so a
  numeric-free formula enumerates nothing at all and both prefixes are empty: explication is the
  \<^emph>\<open>identity\<close> on the numeric-free fragment. Preservation is then immediate --- in particular the
  division-by-zero witnesses, which sit in a second prefix segment after the \<open>f = f\<close> equalities,
  never appear.\<close>

subsection \<open>Explication is the identity on numeric-free formulas\<close>

lemma atom_enumerate_pne_num_free:
  assumes "\<not> is_numeric_atom a"
  shows "atom_enumerate_primitive_numeric_expressions a = []"
  using assms by (cases a) simp_all

lemma atom_enumerate_divisor_num_free:
  assumes "\<not> is_numeric_atom a"
  shows "atom_enumerate_divisor_expressions a = []"
  using assms by (cases a) simp_all

lemma definedness_atoms_num_free:
  assumes "num_free_fmla \<phi>"
  shows "definedness_atoms \<phi> = []"
proof -
  have "set (formula_enumerate_primitive_numeric_expressions \<phi>) = {}"
    unfolding set_formula_enumerate_primitive_numeric_expressions_conv
    using atom_enumerate_pne_num_free num_free_fmla_atoms[OF assms] by auto
  hence "formula_enumerate_primitive_numeric_expressions \<phi> = []" by simp
  thus ?thesis unfolding definedness_atoms_def Let_def by simp
qed

lemma divisor_zero_atoms_num_free:
  assumes "num_free_fmla \<phi>"
  shows "divisor_zero_atoms \<phi> = []"
proof -
  have "set (formula_enumerate_divisor_expressions \<phi>) = {}"
    unfolding set_formula_enumerate_divisor_expressions_conv
    using atom_enumerate_divisor_num_free num_free_fmla_atoms[OF assms] by auto
  hence "formula_enumerate_divisor_expressions \<phi> = []" by simp
  thus ?thesis unfolding divisor_zero_atoms_def by simp
qed

lemma explicate_def_fmla_num_free_id:
  assumes "num_free_fmla \<phi>"
  shows "explicate_def_fmla \<phi> = \<phi>"
  unfolding explicate_def_fmla_def
            definedness_atoms_num_free[OF assms] divisor_zero_atoms_num_free[OF assms]
  by simp

subsection \<open>Numeric-freeness of the explicated problem\<close>

lemma num_free_ac_explicate_def_ac:
  assumes "num_free_ac a"
  shows "num_free_ac (explicate_def_ac a)"
  using assms unfolding num_free_ac_def by (simp add: explicate_def_fmla_num_free_id)

theorem (in ast_classical_problem) explicate_def_prob_num_free:
  assumes nf: num_free_prob
  shows "ast_classical_problem.num_free_prob explicate_def_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom explicate_def_dom"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions explicate_def_dom)"
    then obtain a' where a: "a = explicate_def_ac a'"
      and a'in: "a' \<in> set (actions D)"
      unfolding explicate_def_dom_sel by auto
    have "num_free_ac a'" using nf a'in unfolding num_free_prob_def num_free_dom_def by blast
    thus "num_free_ac a" unfolding a by (rule num_free_ac_explicate_def_ac)
  qed
  have goal: "num_free_fmla (goal explicate_def_prob)"
    using nf unfolding num_free_prob_def by (simp add: explicate_def_fmla_num_free_id)
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom goal nf unfolding num_free_prob_def by simp
qed

end
