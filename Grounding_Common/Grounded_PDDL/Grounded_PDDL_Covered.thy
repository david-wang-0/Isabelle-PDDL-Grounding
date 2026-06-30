theory Grounded_PDDL_Covered
  imports Grounding_Common.Formula_Utils
begin

text \<open>Reusable, AST-agnostic notion underpinning grounding soundness: a formula is \<open>covered\<close> by a fact
  set if every predicate atom occurring in it is one of the facts, and it contains no numeric atoms
  (only predicate atoms and equalities). Mirrors the classical Grounded_PDDL stage; the \<open>grounder\<close>
  locale and the grounding functions stay in \<open>Classical_Grounding.Grounded_PDDL\<close>.\<close>

definition "covered \<phi> facts \<equiv> \<forall>a \<in> atoms \<phi>.
  (case a of predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> set facts
           | eqAtm x y \<Rightarrow> True
           | _ \<Rightarrow> False)"

lemma covered_atoms:
  assumes "covered \<phi> facts" "a \<in> atoms \<phi>"
  shows "(\<exists>p xs. a = predAtm p xs \<and> Atom a \<in> set facts) \<or> (\<exists>x y. a = eqAtm x y)"
  using assms unfolding covered_def by (cases a) auto

lemma covered_predAtm_mem:
  assumes "covered \<phi> facts" "predAtm p xs \<in> atoms \<phi>"
  shows "Atom (predAtm p xs) \<in> set facts"
  using assms unfolding covered_def by (auto split: atom.splits)

lemma covered_mono:
  assumes "covered \<phi> facts" "atoms \<psi> \<subseteq> atoms \<phi>"
  shows "covered \<psi> facts"
  using assms unfolding covered_def by blast

lemma covered_simps[simp]:
  "covered \<bottom> facts"
  "covered (\<^bold>\<not> \<phi>) facts \<longleftrightarrow> covered \<phi> facts"
  "covered (\<phi> \<^bold>\<and> \<psi>) facts \<longleftrightarrow> covered \<phi> facts \<and> covered \<psi> facts"
  "covered (\<phi> \<^bold>\<or> \<psi>) facts \<longleftrightarrow> covered \<phi> facts \<and> covered \<psi> facts"
  "covered (\<phi> \<^bold>\<rightarrow> \<psi>) facts \<longleftrightarrow> covered \<phi> facts \<and> covered \<psi> facts"
  unfolding covered_def by auto

end
