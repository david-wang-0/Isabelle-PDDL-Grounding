theory Classical_Definedness_Translation_Num_Free
  imports Classical_Definedness_Translation Grounding_Classical_Common.Numeric_Free
begin

section \<open>The definedness-translation stage maintains numeric-freeness\<close>

text \<open>Stage-local preservation property, the last link of the input-side numeric-freeness chain
  composed in \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close>: the translation rewrites a reflexive numeric equality
  \<open>f = f\<close> into the propositional \<open>Defined_f\<close> atom and leaves every other atom alone, so it maps
  non-numeric atoms to non-numeric atoms. On numeric-free input it additionally has nothing to add:
  by the explication stage the numeric-effect list of every action is empty, hence the read/written
  PNE lists are empty and neither the precondition's \<open>Defined_\<close> prefix nor the effect's \<open>Defined_\<close>
  adds are generated; and no initial fact is a function assignment, so \<^const>\<open>init_def_fact\<close>
  filters everything out.\<close>

subsection \<open>The translation maps non-numeric atoms to non-numeric atoms\<close>

lemma is_numeric_atom_def_translate_atom:
  assumes "\<not> is_numeric_atom a"
  shows "\<not> is_numeric_atom (def_translate_atom pfx a)"
  using assms by (cases a) simp_all

lemma num_free_fmla_def_translate_fmla:
  assumes "num_free_fmla \<phi>"
  shows "num_free_fmla (def_translate_fmla pfx \<phi>)"
  using assms unfolding def_translate_fmla_def
  by (induction \<phi>) (simp_all add: is_numeric_atom_def_translate_atom)

subsection \<open>On numeric-free input nothing is added\<close>

lemma init_def_fact_num_free:
  assumes "num_free_fmla f"
  shows "init_def_fact pfx f = None"
proof (cases f)
  case (Atom a)
  hence "\<not> is_numeric_atom a" using assms by simp
  thus ?thesis unfolding Atom init_def_fact_def by (cases a) simp_all
qed (simp_all add: init_def_fact_def)

lemma map_filter_init_def_fact_num_free:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> num_free_fmla f"
  shows "List.map_filter (init_def_fact pfx) fs = []"
  using assms by (induction fs) (simp_all add: init_def_fact_num_free)

lemma num_free_ac_def_translate_ac:
  assumes nfa: "num_free_ac a"
  shows "num_free_ac (def_translate_ac pfx a)"
proof -
  obtain h b where a: "a = SimpleActionSchema h b" by (cases a)
  obtain pre eff where b: "b = SimpleActionBody pre eff" by (cases b)
  obtain ads dls neffs where e: "eff = Effect ads dls neffs" by (cases eff)
  have ne: "neffs = []" using nfa unfolding a b e num_free_ac_def by simp
  have pre_nf: "num_free_fmla pre" using nfa unfolding a b num_free_ac_def by simp
  show ?thesis
    unfolding a b e ne def_translate_ac.simps Let_def num_free_ac_def
    using nfa[unfolded a b e num_free_ac_def]
    by (simp add: num_free_fmla_def_translate_fmla pre_nf)
qed

theorem (in ast_classical_problem) def_translate_prob_num_free:
  assumes nf: num_free_prob
  shows "ast_classical_problem.num_free_prob def_translate_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom DT"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions DT)"
    then obtain a' where a: "a = def_translate_ac def_prefix a'"
      and a'in: "a' \<in> set (actions D)"
      unfolding def_translate_dom_sel by auto
    have "num_free_ac a'" using nf a'in unfolding num_free_prob_def num_free_dom_def by blast
    thus "num_free_ac a" unfolding a by (rule num_free_ac_def_translate_ac)
  qed
  have goal: "num_free_fmla (goal PT)"
    using nf unfolding num_free_prob_def by (simp add: num_free_fmla_def_translate_fmla)
  have init: "\<forall>f \<in> set (init PT). num_free_fmla f"
    using nf unfolding num_free_prob_def by (simp add: map_filter_init_def_fact_num_free)
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def using dom goal init by simp
qed

end
