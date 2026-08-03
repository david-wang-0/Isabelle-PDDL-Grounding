theory Grounded_PDDL
  imports Grounding_Common.Formula_Utils
begin

text \<open>Reusable, AST-agnostic notion underpinning grounding soundness: a formula is \<open>covered\<close> by a fact
  set if every predicate atom occurring in it is one of the facts, and it contains no numeric atoms
  (only predicate atoms and equalities). Mirrors the classical Classical_Grounded_PDDL stage; the \<open>grounder\<close>
  locale and the grounding functions stay in \<open>Classical_Grounding.Classical_Grounded_PDDL\<close>.\<close>

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

section \<open>Numeric-permissive coverage\<close>

text \<open>\<^const>\<open>covered\<close> rejects numeric atoms outright, which makes it unusable for a task with a
  numeric precondition, goal or initial function assignment. \<open>covered_num\<close> is its
  \<^emph>\<open>numeric-permissive\<close> weakening: a numeric atom is allowed provided every ground fluent
  (primitive numeric expression) occurring in it is one of the \<open>fluents\<close> --- exactly what the
  fact folder needs in order to re-index that atom onto nullary functions. It is a
  \<^emph>\<open>bundled\<close> predicate, so per the house rule each conjunct is a named definition of its own
  (\<open>facts_covered\<close> = the predicate-atom half, i.e. \<^const>\<open>covered\<close> minus its numeric
  rejection; \<open>fluents_covered\<close> = the fluent half) and it comes with intro / elim / dest
  rules that reach down to the element level, so consuming proofs never unfold the definitions.\<close>

definition "facts_covered \<phi> facts \<equiv> \<forall>a \<in> atoms \<phi>.
  (case a of predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> set facts | _ \<Rightarrow> True)"

definition "fluents_covered \<phi> fluents \<equiv> \<forall>a \<in> atoms \<phi>.
  set (atom_enumerate_primitive_numeric_expressions a) \<subseteq> set fluents"

definition "covered_num \<phi> facts fluents \<equiv> facts_covered \<phi> facts \<and> fluents_covered \<phi> fluents"

subsection \<open>Element-level rules for the two halves\<close>

lemma facts_coveredI:
  assumes "\<And>p xs. predAtm p xs \<in> atoms \<phi> \<Longrightarrow> Atom (predAtm p xs) \<in> set facts"
  shows "facts_covered \<phi> facts"
  using assms unfolding facts_covered_def by (auto split: atom.split)

lemma facts_coveredD:
  assumes "facts_covered \<phi> facts"
      and "predAtm p xs \<in> atoms \<phi>"
  shows "Atom (predAtm p xs) \<in> set facts"
  using assms unfolding facts_covered_def by (auto split: atom.splits)

lemma fluents_coveredI:
  assumes "\<And>a fl. a \<in> atoms \<phi> \<Longrightarrow> fl \<in> set (atom_enumerate_primitive_numeric_expressions a)
             \<Longrightarrow> fl \<in> set fluents"
  shows "fluents_covered \<phi> fluents"
  using assms unfolding fluents_covered_def by blast

lemma fluents_coveredD:
  assumes "fluents_covered \<phi> fluents"
      and "a \<in> atoms \<phi>"
      and "fl \<in> set (atom_enumerate_primitive_numeric_expressions a)"
  shows "fl \<in> set fluents"
  using assms unfolding fluents_covered_def by blast

text \<open>Formula-level restatement of the fluent half: the enumerator over the whole formula is the
  union of the atoms' enumerators, so \<^const>\<open>fluents_covered\<close> is exactly the subset condition the
  folder's \<open>ground_numexp_wf\<close> consumes.\<close>
lemma fluents_covered_alt:
  "fluents_covered \<phi> fluents
     \<longleftrightarrow> set (formula_enumerate_primitive_numeric_expressions \<phi>) \<subseteq> set fluents"
  unfolding fluents_covered_def set_formula_enumerate_primitive_numeric_expressions_conv by blast

subsection \<open>Intro / elim / dest for the bundle\<close>

lemma covered_num_halvesI:
  assumes "facts_covered \<phi> facts"
      and "fluents_covered \<phi> fluents"
  shows "covered_num \<phi> facts fluents"
  unfolding covered_num_def using assms by blast

lemma covered_numI:
  assumes fa: "\<And>p xs. predAtm p xs \<in> atoms \<phi> \<Longrightarrow> Atom (predAtm p xs) \<in> set facts"
      and flu: "\<And>a fl. a \<in> atoms \<phi> \<Longrightarrow> fl \<in> set (atom_enumerate_primitive_numeric_expressions a)
             \<Longrightarrow> fl \<in> set fluents"
  shows "covered_num \<phi> facts fluents"
proof (rule covered_num_halvesI)
  show "facts_covered \<phi> facts" by (rule facts_coveredI) (rule fa)
  show "fluents_covered \<phi> fluents" by (rule fluents_coveredI) (rule flu)
qed

lemma covered_numE:
  assumes "covered_num \<phi> facts fluents"
  obtains "facts_covered \<phi> facts"
      and "fluents_covered \<phi> fluents"
  using assms unfolding covered_num_def by blast

lemma covered_num_factsD:
  assumes "covered_num \<phi> facts fluents"
  shows "facts_covered \<phi> facts"
  using assms unfolding covered_num_def by blast

lemma covered_num_fluentsD:
  assumes "covered_num \<phi> facts fluents"
  shows "fluents_covered \<phi> fluents"
  using assms unfolding covered_num_def by blast

lemma covered_num_predAtm_mem:
  assumes "covered_num \<phi> facts fluents"
      and "predAtm p xs \<in> atoms \<phi>"
  shows "Atom (predAtm p xs) \<in> set facts"
  using facts_coveredD[OF covered_num_factsD[OF assms(1)] assms(2)] .

lemma covered_num_fluent_mem:
  assumes "covered_num \<phi> facts fluents"
      and "a \<in> atoms \<phi>"
      and "fl \<in> set (atom_enumerate_primitive_numeric_expressions a)"
  shows "fl \<in> set fluents"
  using fluents_coveredD[OF covered_num_fluentsD[OF assms(1)] assms(2,3)] .

lemma covered_num_pnes:
  assumes "covered_num \<phi> facts fluents"
  shows "set (formula_enumerate_primitive_numeric_expressions \<phi>) \<subseteq> set fluents"
  using covered_num_fluentsD[OF assms] unfolding fluents_covered_alt .

subsection \<open>Weakening, monotonicity, and the connectives\<close>

text \<open>\<^const>\<open>covered\<close> is the strictly stronger notion: it admits only predicate atoms and
  equalities, whose fluent enumeration is empty, so the fluent half holds for \<^emph>\<open>any\<close> fluent
  list.\<close>
lemma covered_imp_covered_num:
  assumes "covered \<phi> facts"
  shows "covered_num \<phi> facts fluents"
proof (rule covered_numI)
  fix p xs assume "predAtm p xs \<in> atoms \<phi>"
  thus "Atom (predAtm p xs) \<in> set facts" using covered_predAtm_mem[OF assms] by blast
next
  fix a fl assume a: "a \<in> atoms \<phi>"
    and fl: "fl \<in> set (atom_enumerate_primitive_numeric_expressions a)"
  have "atom_enumerate_primitive_numeric_expressions a = []"
    using covered_atoms[OF assms a] by auto
  thus "fl \<in> set fluents" using fl by simp
qed

lemma covered_num_mono:
  assumes "covered_num \<phi> facts fluents"
      and "atoms \<psi> \<subseteq> atoms \<phi>"
  shows "covered_num \<psi> facts fluents"
  using assms unfolding covered_num_def facts_covered_def fluents_covered_def by blast

lemma facts_covered_simps[simp]:
  "facts_covered \<bottom> facts"
  "facts_covered (\<^bold>\<not> \<phi>) facts \<longleftrightarrow> facts_covered \<phi> facts"
  "facts_covered (\<phi> \<^bold>\<and> \<psi>) facts \<longleftrightarrow> facts_covered \<phi> facts \<and> facts_covered \<psi> facts"
  "facts_covered (\<phi> \<^bold>\<or> \<psi>) facts \<longleftrightarrow> facts_covered \<phi> facts \<and> facts_covered \<psi> facts"
  "facts_covered (\<phi> \<^bold>\<rightarrow> \<psi>) facts \<longleftrightarrow> facts_covered \<phi> facts \<and> facts_covered \<psi> facts"
  unfolding facts_covered_def by auto

lemma fluents_covered_simps[simp]:
  "fluents_covered \<bottom> fluents"
  "fluents_covered (\<^bold>\<not> \<phi>) fluents \<longleftrightarrow> fluents_covered \<phi> fluents"
  "fluents_covered (\<phi> \<^bold>\<and> \<psi>) fluents \<longleftrightarrow> fluents_covered \<phi> fluents \<and> fluents_covered \<psi> fluents"
  "fluents_covered (\<phi> \<^bold>\<or> \<psi>) fluents \<longleftrightarrow> fluents_covered \<phi> fluents \<and> fluents_covered \<psi> fluents"
  "fluents_covered (\<phi> \<^bold>\<rightarrow> \<psi>) fluents \<longleftrightarrow> fluents_covered \<phi> fluents \<and> fluents_covered \<psi> fluents"
  unfolding fluents_covered_def by auto

lemma covered_num_simps[simp]:
  "covered_num \<bottom> facts fluents"
  "covered_num (\<^bold>\<not> \<phi>) facts fluents \<longleftrightarrow> covered_num \<phi> facts fluents"
  "covered_num (\<phi> \<^bold>\<and> \<psi>) facts fluents
     \<longleftrightarrow> covered_num \<phi> facts fluents \<and> covered_num \<psi> facts fluents"
  "covered_num (\<phi> \<^bold>\<or> \<psi>) facts fluents
     \<longleftrightarrow> covered_num \<phi> facts fluents \<and> covered_num \<psi> facts fluents"
  "covered_num (\<phi> \<^bold>\<rightarrow> \<psi>) facts fluents
     \<longleftrightarrow> covered_num \<phi> facts fluents \<and> covered_num \<psi> facts fluents"
  unfolding covered_num_def by auto

end
