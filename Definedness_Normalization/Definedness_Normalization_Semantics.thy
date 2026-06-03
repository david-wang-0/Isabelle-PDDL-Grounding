theory Definedness_Normalization_Semantics
  imports Definedness_Normalization
begin

section ‹Definedness Explication Preserves Semantics›

subsection ‹Helper lemmas on ‹foldr (❙∧) (map Atom _)››

lemma foldr_and_imp_orig:
  assumes "𝒜 ⊨⇩m foldr (❙∧) (map Atom as) F"
  shows "𝒜 ⊨⇩m F"
  using assms by (induction as) auto

lemma foldr_and_if:
  assumes "𝒜 ⊨⇩m F"
      and "∀a ∈ set as. 𝒜 a = Some True"
    shows "𝒜 ⊨⇩m foldr (❙∧) (map Atom as) F"
  using assms by (induction as) auto

subsection ‹Definedness atoms under a defined-PNE valuation›

lemma definedness_atom_valuation:
  assumes "atoms F ⊆ dom (valuation M)"
      and "a ∈ set (definedness_atoms F)"
    shows "valuation M a = Some True"
proof -
  from assms(2) obtain p where p:
    "p ∈ set (formula_enumerate_primitive_numeric_expressions F)"
    "a = numericEqAtm (FunctionExpr p) (FunctionExpr p)"
    by (rule definedness_atoms_form)
  from p(1) assms(1) have "p ∈ dom (snd M)"
    using formula_atoms_in_dom_valuation_iff by fast
  thus ?thesis unfolding p(2) valuation_def by (cases "snd M p") auto
qed

lemma definedness_atoms_subset_dom_valuation:
  assumes "atoms F ⊆ dom (valuation M)"
  shows "set (definedness_atoms F) ⊆ dom (valuation M)"
  using definedness_atom_valuation[OF assms] by (auto simp: domIff)

subsection ‹Key semantic equivalence›

theorem explicate_def_fmla_semantics:
  "valuation M ⊨⇩m explicate_def_fmla f ⟷ valuation M ⊨⇩m f"
proof
  assume "valuation M ⊨⇩m explicate_def_fmla f"
  thus "valuation M ⊨⇩m f"
    unfolding explicate_def_fmla_def using foldr_and_imp_orig by blast
next
  assume sat: "valuation M ⊨⇩m f"
  hence atoms_in: "atoms f ⊆ dom (valuation M)" by blast
  show "valuation M ⊨⇩m explicate_def_fmla f"
    unfolding explicate_def_fmla_def
    by (rule foldr_and_if[OF sat], rule ballI, rule definedness_atom_valuation[OF atoms_in])
qed

subsection ‹Substitution commutes with explication›

text ‹Needed for the action-instantiation argument: substituting parameters
  into an explicated precondition yields the same formula as explicating the
  substituted precondition. The PNE-enumeration map lemmas are inherited from
  ‹Definedness_Normalization›.›

lemma definedness_atoms_map:
  "definedness_atoms (map_formula (map_atom m) F)
    = map (map_atom m) (definedness_atoms F)"
  unfolding definedness_atoms_def Let_def
  by (simp add: formula_enumerate_primitive_numeric_expressions_map comp_def)

lemma foldr_and_map:
  "map_formula (map_atom m) (foldr (❙∧) (map Atom as) f)
    = foldr (❙∧) (map Atom (map (map_atom m) as)) (map_formula (map_atom m) f)"
  by (induction as) auto

lemma explicate_def_fmla_map:
  "map_formula (map_atom m) (explicate_def_fmla f)
    = explicate_def_fmla (map_formula (map_atom m) f)"
  unfolding explicate_def_fmla_def
  by (simp add: foldr_and_map definedness_atoms_map)

subsection ‹Plan-action enabledness is preserved›

context ast_classical_problem_de begin

lemma inst_pre_explicate_def:
  "ground_action.precondition
     (instantiate_classical_action_schema (explicate_def_ac a) args)
   = explicate_def_fmla
     (ground_action.precondition (instantiate_classical_action_schema a args))"
  unfolding instantiate_classical_action_schema_alt explicate_def_ac_unfold
  by (simp add: explicate_def_fmla_map)

lemma inst_pre_iff_explicate_def:
  "valuation M ⊨⇩m
     ground_action.precondition (instantiate_classical_action_schema a args)
   ⟷ valuation M ⊨⇩m
     ground_action.precondition
       (instantiate_classical_action_schema (explicate_def_ac a) args)"
  unfolding inst_pre_explicate_def by (rule explicate_def_fmla_semantics[symmetric])

end

subsection ‹Plan validity is preserved›

text ‹Explication only modifies precondition formulas: action names, parameters,
  and effects are unchanged. Combined with ‹explicate_def_fmla_semantics›, this
  lifts to a direct ‹iff› on plan validity. Plan restoration is the identity.›

lemma map_of_pair_map: 
  "map_of (map (λx. (f x, g x)) xs) n = map_option g (map_of (map (λx. (f x, x)) xs) n)"
  by (induction xs) auto

context ast_classical_problem_de begin

lemma ast_classical_action_schema_head_explicate [simp]:
  "ast_classical_action_schema.head (explicate_def_ac a) = ast_classical_action_schema.head a"
  by (cases a rule: ast_classical_action_schema_cases_unfold) simp

lemma d_de_resolve_classical_action_schema:
  "d_de.resolve_classical_action_schema n
   = map_option explicate_def_ac (resolve_classical_action_schema n)"
proof -
  have "d_de.resolve_classical_action_schema n
      = map_of (map (λx. (ac_name x, explicate_def_ac x)) (actions D)) n"
    unfolding d_de.resolve_classical_action_schema_def explicate_def_dom_sel index_by_def
    by (simp add: comp_def)
  also have "... = map_option explicate_def_ac (resolve_classical_action_schema n)"
    unfolding resolve_classical_action_schema_def index_by_def by (rule map_of_pair_map)
  finally show ?thesis .
qed


lemma p_de_resolve_classical_action_schema:
  "p_de.resolve_classical_action_schema n
   = map_option explicate_def_ac (resolve_classical_action_schema n)"
  using d_de_resolve_classical_action_schema by simp

lemma p_de_wf_classical_plan_action [simp]:
  "p_de.wf_classical_plan_action π ⟷ wf_classical_plan_action π"
proof (cases π)
  case (SimplePlanAction n args)
  show ?thesis
    unfolding SimplePlanAction
              p_de.wf_classical_plan_action_simple
              wf_classical_plan_action_simple
              p_de_resolve_classical_action_schema
    by (auto split: option.splits)
qed

lemma p_de_res_inst_precondition:
  assumes "wf_classical_plan_action π" "res_inst π = Some g"
  shows "∃g'. p_de.res_inst π = Some g'
    ∧ precondition g' = explicate_def_fmla (precondition g)
    ∧ effect g' = effect g"
proof (cases π)
  case (SimplePlanAction n args)
  from assms(1) obtain a where res: "resolve_classical_action_schema n = Some a"
    unfolding SimplePlanAction wf_classical_plan_action_simple
    by (cases "resolve_classical_action_schema n") auto
  with assms(2) have g_def: "g = instantiate_classical_action_schema a args"
    unfolding SimplePlanAction by simp
  have p_de_res: "p_de.res_inst (SimplePlanAction n args)
    = Some (instantiate_classical_action_schema (explicate_def_ac a) args)"
    using p_de_resolve_classical_action_schema res by simp
  have pre_eq: "precondition (instantiate_classical_action_schema (explicate_def_ac a) args)
    = explicate_def_fmla (precondition g)"
    using inst_pre_explicate_def[of a args] unfolding g_def by simp
  have eff_eq: "effect (instantiate_classical_action_schema (explicate_def_ac a) args)
    = effect g"
    unfolding g_def instantiate_classical_action_schema_alt by simp
  show ?thesis using p_de_res pre_eq eff_eq SimplePlanAction by blast
qed

lemma p_de_res_inst_None [simp]:
  "p_de.res_inst π = None ⟷ res_inst π = None"
proof (cases π)
  case (SimplePlanAction n args)
  show ?thesis
    unfolding SimplePlanAction p_de.res_inst.simps res_inst.simps
              p_de_resolve_classical_action_schema
    by (cases "resolve_classical_action_schema n") auto
qed

lemma numeric_effects_non_intrf_explicate:
  assumes "wf_classical_plan_action π" "res_inst π = Some g" "p_de.res_inst π = Some g'"
  shows "numeric_effects_non_intrf g' = numeric_effects_non_intrf g"
proof -
  from p_de_res_inst_precondition[OF assms(1,2)] assms(3)
  have "effect g' = effect g" by auto
  thus ?thesis
    unfolding numeric_effects_non_intrf_def by simp
qed

lemma p_de_plan_action_enabled_iff:
  "p_de.plan_action_enabled π M ⟷ plan_action_enabled π M"
proof (cases "wf_classical_plan_action π")
  case False
  thus ?thesis
    unfolding plan_action_enabled_def p_de.plan_action_enabled_def by simp
next
  case True
  obtain g where g: "res_inst π = Some g" using res_inst_alt by blast
  obtain g' where g': "p_de.res_inst π = Some g'" using p_de.res_inst_alt by blast
  from p_de_res_inst_precondition[OF True g] g'
  have pre: "precondition g' = explicate_def_fmla (precondition g)"
   and eff: "effect g' = effect g" by auto
  have ne: "numeric_effects_non_intrf g' = numeric_effects_non_intrf g"
    using numeric_effects_non_intrf_explicate[OF True g g'] .
  have rhs: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect g'))
           = set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect g))"
    using eff by simp
  have pre_sem: "valuation M ⊨⇩m precondition g' ⟷ valuation M ⊨⇩m precondition g"
    unfolding pre by (rule explicate_def_fmla_semantics)
  show ?thesis
    unfolding plan_action_enabled_def p_de.plan_action_enabled_def
    unfolding g g' comp_apply option.sel Let_def
    by (simp add: ne rhs pre_sem)
qed

lemma p_de_res_inst_effect:
  "effect (the (p_de.res_inst π)) = effect (the (res_inst π))"
proof -
  have l: "p_de.res_inst π = Some (instantiate_classical_action_schema
      (the (p_de.resolve_classical_action_schema (name π))) (arguments π))"
    by (rule p_de.res_inst_alt)
  have r: "res_inst π = Some (instantiate_classical_action_schema
      (the (resolve_classical_action_schema (name π))) (arguments π))"
    by (rule res_inst_alt)
  show ?thesis
    unfolding l r option.sel p_de_resolve_classical_action_schema
    by (cases "resolve_classical_action_schema (name π)")
       (simp_all add: instantiate_classical_action_schema_alt)
qed

lemma p_de_execute_plan_action:
  "p_de.execute_plan_action π M = execute_plan_action π M"
  unfolding execute_plan_action_def p_de.execute_plan_action_def comp_apply
  by (simp add: p_de_res_inst_effect action_list_numeric_update_function_def
                action_numeric_update_function_def)

lemma p_de_valid_classical_plan_alt_iff:
  "p_de.valid_classical_plan_alt M πs M' ⟷ valid_classical_plan_alt M πs M'"
proof (induction πs arbitrary: M)
  case Nil show ?case by simp
next
  case (Cons π πs)
  show ?case
    by (simp add: Cons.IH p_de_plan_action_enabled_iff p_de_execute_plan_action)
qed

lemma p_de_I [simp]: "p_de.I = I"
  unfolding p_de.I_def I_def explicate_def_prob_sel by simp

lemma p_de_valid_classical_plan2_iff:
  "p_de.valid_classical_plan2 πs ⟷ valid_classical_plan2 πs"
  unfolding p_de.valid_classical_plan2_alt valid_classical_plan2_alt
  unfolding p_de_valid_classical_plan_alt_iff p_de_I explicate_def_prob_sel
  by (simp add: explicate_def_fmla_semantics)

theorem explicate_valid_iff:
  "(∃πs. valid_classical_plan2 πs) ⟷ (∃πs'. p_de.valid_classical_plan2 πs')"
  using p_de_valid_classical_plan2_iff by blast

theorem explicate_plan_restore:
  "p_de.valid_classical_plan2 πs ⟹ valid_classical_plan2 (restore_plan_explicate πs)"
  using p_de_valid_classical_plan2_iff unfolding restore_plan_explicate_def by simp

end

text ‹Code setup.›

lemmas explicate_def_code =
  definedness_atoms_def
  explicate_def_fmla_def
  explicate_def_ac.simps
  ast_classical_domain.explicate_def_dom_def
  ast_classical_problem.explicate_def_prob_def

declare explicate_def_code[code]

end
