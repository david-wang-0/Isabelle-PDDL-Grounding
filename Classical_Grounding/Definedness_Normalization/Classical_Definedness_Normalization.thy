theory Classical_Definedness_Normalization
  imports Classical_Definedness_Normalization_Locales
begin

section \<open>Definedness Explication Well-Formedness Proofs\<close>

subsection \<open>Atom-set and PNE enumeration lemmas\<close>

lemma atoms_foldr_and:
  "atoms (foldr (\<^bold>\<and>) (map Atom as) f) = set as \<union> atoms f"
  by (induction as) auto

lemma atoms_explicate_def_fmla:
  "atoms (explicate_def_fmla f) = set (definedness_atoms f) \<union> atoms f"
  unfolding explicate_def_fmla_def by (rule atoms_foldr_and)

lemma definedness_atoms_form:
  assumes "a \<in> set (definedness_atoms f)"
  obtains p where
    "p \<in> set (formula_enumerate_primitive_numeric_expressions f)"
    and "a = numericEqAtm (FunctionExpr p) (FunctionExpr p)"
  using assms unfolding definedness_atoms_def Let_def by auto

lemma definedness_atoms_pnes:
  "(\<Union>a \<in> set (definedness_atoms f). set (atom_enumerate_primitive_numeric_expressions a))
   = set (formula_enumerate_primitive_numeric_expressions f)"
  unfolding definedness_atoms_def Let_def by auto

lemma explicate_def_fmla_pnes:
  "set (formula_enumerate_primitive_numeric_expressions (explicate_def_fmla f))
   = set (formula_enumerate_primitive_numeric_expressions f)"
proof -
  have rec:
    "set (formula_enumerate_primitive_numeric_expressions
            (foldr (\<^bold>\<and>) (map Atom as) f))
     = (\<Union>a \<in> set as. set (atom_enumerate_primitive_numeric_expressions a))
       \<union> set (formula_enumerate_primitive_numeric_expressions f)"
    for as
    by (induction as) auto
  show ?thesis
    unfolding explicate_def_fmla_def rec definedness_atoms_pnes by simp
qed

subsection \<open>Action selectors (refinement of \<open>explicate_def_ac_sel\<close>)\<close>

text \<open>Convenient unfolding when we want to reason about \<open>ac_head\<close> /
  \<open>ac_body\<close> too.\<close>

lemma explicate_def_ac_unfold:
  "explicate_def_ac a =
    SimpleActionSchema (ActionHead (ac_name a) (ac_params a))
      (SimpleActionBody (explicate_def_fmla (ac_pre a)) (ac_eff a))"
  by (cases a rule: ast_classical_action_schema_cases_unfold) simp

subsection \<open>Well-formedness of explicated formulas\<close>

text \<open>The definedness atoms produced by \<open>definedness_atoms\<close> are all well-formed
  whenever the source formula is.\<close>

lemma (in ast_classical_domain) wf_definedness_atoms:
  assumes "wf_fmla tyt f"
      and "a \<in> set (definedness_atoms f)"
    shows "wf_atom tyt a"
proof -
  from \<open>a \<in> set (definedness_atoms f)\<close>
  obtain p where p:
    "p \<in> set (formula_enumerate_primitive_numeric_expressions f)"
    "a = numericEqAtm (FunctionExpr p) (FunctionExpr p)"
    by (rule definedness_atoms_form)
  from p(1) assms(1) have "wf_primitive_numeric_expression tyt p"
    using wf_fmla_imp_wf_pnes by blast
  hence "wf_numeric_expression tyt (FunctionExpr p)" by simp
  thus ?thesis unfolding p(2) by simp
qed

lemma (in ast_classical_domain) wf_explicate_def_fmla:
  assumes "wf_fmla tyt f"
  shows "wf_fmla tyt (explicate_def_fmla f)"
proof -
  have rec: "wf_fmla tyt (foldr (\<^bold>\<and>) (map Atom as) f)"
    if "\<forall>a \<in> set as. wf_atom tyt a" for as
    using that by (induction as) (auto simp: assms)
  show ?thesis
    unfolding explicate_def_fmla_def
    using wf_definedness_atoms[OF assms] by (intro rec) blast
qed

subsection \<open>Well-formedness of explicated actions\<close>

lemma (in ast_classical_domain) wf_explicate_def_ac:
  assumes "wf_classical_action_schema a"
  shows "wf_classical_action_schema (explicate_def_ac a)"
proof -
  from assms have wf_pre: "wf_fmla (ac_tyt a) (ac_pre a)"
    unfolding wf_classical_action_schema_alt by simp
  have ac_tyt_eq: "ac_tyt (explicate_def_ac a) = ac_tyt a"
    by (simp add: ac_tyt_def)
  show ?thesis
    using assms wf_explicate_def_fmla[OF wf_pre] ac_tyt_eq
    unfolding wf_classical_action_schema_alt by simp
qed

subsection \<open>Well-formedness of explicated domain/problem\<close>

context wf_ast_classical_domain_de begin

lemma explicate_def_dom_actions_wf:
  "list_all d_de.wf_classical_action_schema (actions explicate_def_dom)"
proof (subst list_all_iff, intro ballI)
  fix a' assume "a' \<in> set (actions explicate_def_dom)"
  then obtain a where a:
    "a \<in> set (actions D)" "a' = explicate_def_ac a"
    by auto
  from a(1) wf_D have wf_a: "wf_classical_action_schema a"
    by (simp add: list_all_iff)
  thus "d_de.wf_classical_action_schema a'"
    using a(2) wf_explicate_def_ac by simp
qed

lemma explicate_def_dom_action_names_distinct:
  "distinct (map ac_name (actions explicate_def_dom))"
  using wf_D unfolding explicate_def_dom_sel
  by (simp add: list.map_comp comp_def)

theorem explicate_def_dom_wf: "d_de.wf_classical_domain"
  unfolding d_de.wf_classical_domain_def
  using wf_D explicate_def_dom_actions_wf
        explicate_def_dom_action_names_distinct
  by (simp add: list_all_iff)

end

context wf_ast_classical_problem_de begin

theorem explicate_def_prob_wf: "p_de.wf_classical_problem"
  unfolding p_de.wf_classical_problem_def explicate_def_prob_sel
  using wf_P explicate_def_dom_wf wf_explicate_def_fmla[of objT "goal P"]
  by simp

end

sublocale wf_ast_classical_domain_de \<subseteq> wf_ast_classical_domain explicate_def_dom
  using explicate_def_dom_wf wf_ast_classical_domain.intro by simp

sublocale wf_ast_classical_problem_de \<subseteq> p_de_wf: wf_ast_classical_problem explicate_def_prob
  using explicate_def_prob_wf wf_ast_classical_problem.intro by simp

subsection \<open>PNE-enumeration substitution lemmas\<close>

text \<open>Pure syntactic facts about PNE enumeration under formula substitution.
  Used by the \<open>_Semantics\<close> file in this session.\<close>

lemma enumerate_primitive_numeric_expressions_map:
  "enumerate_primitive_numeric_expressions (map_numeric_expression m e)
    = map (map_primitive_numeric_expression m) (enumerate_primitive_numeric_expressions e)"
  by (induction e) auto

lemma atom_enumerate_primitive_numeric_expressions_map:
  "atom_enumerate_primitive_numeric_expressions (map_atom m a)
    = map (map_primitive_numeric_expression m) (atom_enumerate_primitive_numeric_expressions a)"
  by (cases a) (auto simp: enumerate_primitive_numeric_expressions_map)

lemma formula_enumerate_primitive_numeric_expressions_map:
  "formula_enumerate_primitive_numeric_expressions (map_formula (map_atom m) F)
    = map (map_primitive_numeric_expression m) (formula_enumerate_primitive_numeric_expressions F)"
  by (induction F) (auto simp: atom_enumerate_primitive_numeric_expressions_map)

subsection \<open>Explication establishes \<open>def_explicated_conj\<close>\<close>

text \<open>The whole point of this normalization step: its output satisfies the
  \<open>def_explicated_conj_prob\<close> predicate that downstream steps assume on their
  input. The conjunctive-prefix shape is direct because \<open>explicate_def_fmla\<close>
  is defined as \<open>foldr (\<and>) (map Atom (definedness_atoms f)) f\<close>.\<close>

lemma conj_atom_prefix_explicate_def_fmla:
  "conj_atom_prefix (explicate_def_fmla f) = definedness_atoms f @ conj_atom_prefix f"
  unfolding explicate_def_fmla_def by (rule conj_atom_prefix_foldr_and_Atom)

lemma is_def_explicated_conj_explicate_def_fmla:
  "is_def_explicated_conj (explicate_def_fmla f)"
proof -
  have "numericEqAtm (FunctionExpr p) (FunctionExpr p)
          \<in> set (conj_atom_prefix (explicate_def_fmla f))"
    if "p \<in> set (formula_enumerate_primitive_numeric_expressions
                    (explicate_def_fmla f))" for p
  proof -
    from that have "p \<in> set (formula_enumerate_primitive_numeric_expressions f)"
      using explicate_def_fmla_pnes by blast
    hence "numericEqAtm (FunctionExpr p) (FunctionExpr p) \<in> set (definedness_atoms f)"
      unfolding definedness_atoms_def Let_def by force
    thus ?thesis unfolding conj_atom_prefix_explicate_def_fmla by simp
  qed
  thus ?thesis unfolding is_def_explicated_conj_def by blast
qed

lemma (in ast_classical_domain) def_explicated_conj_explicate_def_dom:
  "ast_classical_domain.def_explicated_conj_dom explicate_def_dom"
  unfolding ast_classical_domain.def_explicated_conj_dom_def
  using is_def_explicated_conj_explicate_def_fmla
  by auto

lemma (in ast_classical_problem) def_explicated_conj_explicate_def_prob:
  "ast_classical_problem.def_explicated_conj_prob explicate_def_prob"
  unfolding ast_classical_problem.def_explicated_conj_prob_def
  using def_explicated_conj_explicate_def_dom
        is_def_explicated_conj_explicate_def_fmla
  by simp

sublocale wf_ast_classical_domain_de \<subseteq> p_de_de: def_explicated_conj_domain explicate_def_dom
  by unfold_locales (rule def_explicated_conj_explicate_def_dom)

sublocale wf_ast_classical_problem_de \<subseteq> p_de_de: def_explicated_conj_problem explicate_def_prob
  by unfold_locales (rule def_explicated_conj_explicate_def_prob)

end
