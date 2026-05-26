theory Definedness_Normalization
  imports Definedness_Normalization_Locales
begin

section ‹Definedness Explication Well-Formedness Proofs›

subsection ‹Atom-set and PNE enumeration lemmas›

lemma atoms_foldr_and:
  "atoms (foldr (❙∧) (map Atom as) f) = set as ∪ atoms f"
  by (induction as) auto

lemma atoms_explicate_def_fmla:
  "atoms (explicate_def_fmla f) = set (definedness_atoms f) ∪ atoms f"
  unfolding explicate_def_fmla_def by (rule atoms_foldr_and)

lemma definedness_atoms_form:
  assumes "a ∈ set (definedness_atoms f)"
  obtains p where
    "p ∈ set (formula_enumerate_primitive_numeric_expressions f)"
    and "a = numericEqAtm (FunctionExpr p) (FunctionExpr p)"
  using assms unfolding definedness_atoms_def Let_def by auto

lemma definedness_atoms_pnes:
  "(⋃a ∈ set (definedness_atoms f). set (atom_enumerate_primitive_numeric_expressions a))
   = set (formula_enumerate_primitive_numeric_expressions f)"
  unfolding definedness_atoms_def Let_def by auto

lemma explicate_def_fmla_pnes:
  "set (formula_enumerate_primitive_numeric_expressions (explicate_def_fmla f))
   = set (formula_enumerate_primitive_numeric_expressions f)"
proof -
  have rec:
    "set (formula_enumerate_primitive_numeric_expressions
            (foldr (❙∧) (map Atom as) f))
     = (⋃a ∈ set as. set (atom_enumerate_primitive_numeric_expressions a))
       ∪ set (formula_enumerate_primitive_numeric_expressions f)"
    for as
    by (induction as) auto
  show ?thesis
    unfolding explicate_def_fmla_def rec definedness_atoms_pnes by simp
qed

subsection ‹Action selectors (refinement of ‹explicate_def_ac_sel›)›

text ‹Convenient unfolding when we want to reason about ‹ac_head› /
  ‹ac_body› too.›

lemma explicate_def_ac_unfold:
  "explicate_def_ac a =
    SimpleActionSchema (ActionHead (ac_name a) (ac_params a))
      (SimpleActionBody (explicate_def_fmla (ac_pre a)) (ac_eff a))"
  by (cases a rule: ast_classical_action_schema_cases_unfold) simp

subsection ‹Well-formedness of explicated formulas›

text ‹The definedness atoms produced by ‹definedness_atoms› are all well-formed
  whenever the source formula is.›

lemma (in ast_classical_domain) wf_definedness_atoms:
  assumes "wf_fmla tyt f"
      and "a ∈ set (definedness_atoms f)"
    shows "wf_atom tyt a"
proof -
  from ‹a ∈ set (definedness_atoms f)›
  obtain p where p:
    "p ∈ set (formula_enumerate_primitive_numeric_expressions f)"
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
  have rec: "wf_fmla tyt (foldr (❙∧) (map Atom as) f)"
    if "∀a ∈ set as. wf_atom tyt a" for as
    using that by (induction as) (auto simp: assms)
  show ?thesis
    unfolding explicate_def_fmla_def
    using wf_definedness_atoms[OF assms] by (intro rec) blast
qed

subsection ‹Well-formedness of explicated actions›

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

subsection ‹Well-formedness of explicated domain/problem›

context wf_ast_classical_domain_de begin

lemma explicate_def_dom_actions_wf:
  "list_all d_de.wf_classical_action_schema (actions explicate_def_dom)"
proof (subst list_all_iff, intro ballI)
  fix a' assume "a' ∈ set (actions explicate_def_dom)"
  then obtain a where a:
    "a ∈ set (actions D)" "a' = explicate_def_ac a"
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

sublocale wf_ast_classical_domain_de ⊆ wf_ast_classical_domain explicate_def_dom
  using explicate_def_dom_wf wf_ast_classical_domain.intro by simp

sublocale wf_ast_classical_problem_de ⊆ p_de_wf: wf_ast_classical_problem explicate_def_prob
  using explicate_def_prob_wf wf_ast_classical_problem.intro by simp

subsection ‹PNE-enumeration substitution lemmas›

text ‹Pure syntactic facts about PNE enumeration under formula substitution.
  Used by the ‹_Semantics› file in this session.›

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

subsection ‹Explication establishes ‹def_explicated_conj››

text ‹The whole point of this normalization step: its output satisfies the
  ‹def_explicated_conj_prob› predicate that downstream steps assume on their
  input. The conjunctive-prefix shape is direct because ‹explicate_def_fmla›
  is defined as ‹foldr (∧) (map Atom (definedness_atoms f)) f›.›

lemma conj_atom_prefix_explicate_def_fmla:
  "conj_atom_prefix (explicate_def_fmla f) = definedness_atoms f @ conj_atom_prefix f"
  unfolding explicate_def_fmla_def by (rule conj_atom_prefix_foldr_and_Atom)

lemma is_def_explicated_conj_explicate_def_fmla:
  "is_def_explicated_conj (explicate_def_fmla f)"
proof -
  have "numericEqAtm (FunctionExpr p) (FunctionExpr p)
          ∈ set (conj_atom_prefix (explicate_def_fmla f))"
    if "p ∈ set (formula_enumerate_primitive_numeric_expressions
                    (explicate_def_fmla f))" for p
  proof -
    from that have "p ∈ set (formula_enumerate_primitive_numeric_expressions f)"
      using explicate_def_fmla_pnes by blast
    hence "numericEqAtm (FunctionExpr p) (FunctionExpr p) ∈ set (definedness_atoms f)"
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

sublocale wf_ast_classical_domain_de ⊆ p_de_de: def_explicated_conj_domain explicate_def_dom
  by unfold_locales (rule def_explicated_conj_explicate_def_dom)

sublocale wf_ast_classical_problem_de ⊆ p_de_de: def_explicated_conj_problem explicate_def_prob
  by unfold_locales (rule def_explicated_conj_explicate_def_prob)

end
