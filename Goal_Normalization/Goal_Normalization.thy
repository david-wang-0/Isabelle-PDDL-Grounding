theory Goal_Normalization
  imports Goal_Normalization_Locales
begin

section ‹Goal Normalization Well-Formedness Proofs›

context wf_ast_classical_problem3 begin

text ‹The goal predicate is fresh.›

lemma goal_pred_fresh: "goal_pred ∉ pred ` set (predicates D)"
proof -
  have "safe_prefix pred_names + STR ''Goal'' ∉ set pred_names"
    using safe_prefix_correct by blast
  hence "safe_prefix pred_names + STR ''Goal''
            ∉ predicate.name ` (pred ` set (predicates D))"
    by auto
  thus ?thesis unfolding goal_pred_def
    by (metis image_iff predicate.sel)
qed

lemma g_preds_dist: "distinct (map pred (predicates D3))"
proof -
  have "pred goal_pred_decl ∉ pred ` set (predicates D)"
    using goal_pred_fresh goal_pred_decl_def by simp
  thus ?thesis using wf_D_sig(2) by simp
qed

lemma g_type_wf: "wf_type T ⟹ p3.wf_type T"
  using degoal_dom_sel(1) by (cases T) simp

lemma g_preds_wf: "list_all p3.wf_predicate_decl (predicates D3)"
proof -
  have "wf_predicate_decl pd ⟹ p3.wf_predicate_decl pd" for pd
    using g_type_wf by (cases pd) simp
  hence "list_all p3.wf_predicate_decl (predicates D)"
    using wf_D_sig(3) by (simp add: list.pred_map list_all_iff)
  moreover have "p3.wf_predicate_decl goal_pred_decl"
    unfolding goal_pred_decl_def by simp
  ultimately show ?thesis by simp
qed

lemma g_funcs_dist: "distinct (map function_decl.func (functions D3))"
  using wf_D_sig(4) by simp

lemma g_funcs_wf: "list_all p3.wf_function_decl (functions D3)"
proof -
  have "wf_function_decl fd ⟹ p3.wf_function_decl fd" for fd
    using g_type_wf by (cases fd) simp
  thus ?thesis using wf_D_sig(5)
    by (simp add: list.pred_map list_all_iff)
qed

lemma g_consts_dist: "distinct (map fst (consts D3))"
  using wf_D_sig(6) wf_P_sig(2) by simp

lemma g_consts_wf: "∀(n, T) ∈ set (consts D3). p3.wf_type T"
  using wf_D_sig(7) wf_P_sig(3) g_type_wf by auto

text ‹The goal action name is fresh.›

lemma goal_ac_name_fresh: "goal_ac_name ∉ set ac_names"
  using safe_prefix_correct by blast

lemma g_acs_dist: "distinct (map ac_name (actions D3))"
proof -
  have "ac_name (goal_ac term_goal) = goal_ac_name"
    unfolding goal_ac_def by simp
  hence "ac_name (goal_ac term_goal) ∉ ac_name ` set (actions D)"
    using goal_ac_name_fresh by force
  thus ?thesis using wf_D(2) by simp
qed

lemma g_sig:
  assumes "sig p = Some xs" shows "p3.sig p = Some xs"
proof -
  have in_preds: "(p, xs) ∈ set (map split_pred (predicates D3))"
  proof -
    have "PredDecl p xs \<in> S \<longleftrightarrow> (p, xs) \<in> split_pred ` S" for p xs S
      by (force split: predicate_decl.splits)
    thus ?thesis using sig_Some assms by simp
  qed
  have dist: "distinct (map fst (map split_pred (predicates degoal_dom)))"
  proof -
    have "fst o split_pred = pred" 
      by (rule ext, rename_tac b, case_tac b, simp)
    thus ?thesis unfolding map_map 
      using g_preds_dist
      by simp
  qed
  show ?thesis 
    unfolding p3.sig_def
    apply (rule map_of_is_SomeI)
    using dist in_preds by simp+
qed

lemma g_is_of_type: "is_of_type = p3.is_of_type"
  apply (rule ext)
  unfolding is_of_type_def of_type_def subtype_rel_def degoal_prob_sel degoal_dom_sel by simp

lemma g_atom_wf:
  assumes "wf_atom tyt a" shows "p3.wf_atom tyt a"
  using assms 
proof (induction a)
  case (predAtm p xs)
  hence a: "wf_pred_atom tyt (p, xs)" using assms by simp
  then obtain Ts where sig: "sig p = Some Ts" by fastforce
  with a have "list_all2 (is_of_type tyt) xs Ts" by simp
  hence "list_all2 (p3.is_of_type tyt) xs Ts" using g_is_of_type by metis
  moreover have "p3.sig p = Some Ts" using g_sig sig by simp
  ultimately have "p3.wf_pred_atom tyt (p, xs)"
    apply (subst p3.wf_pred_atom.simps)
    by (auto simp: option.case_cong)
  then show ?case by (subst p3.wf_atom.simps, simp)
qed (subst p3.wf_atom.simps, simp)+

lemma g_fmla_wf: "wf_fmla tyt φ ⟹ p3.wf_fmla tyt φ"
  using g_atom_wf co_fmla_wf by blast

lemma g_func_sig: "p3.func_sig = func_sig"
  unfolding func_sig_def p3.func_sig_def degoal_dom_sel by simp

lemma g_pne_wf:
  assumes "wf_primitive_numeric_expression tyt p"
  shows "p3.wf_primitive_numeric_expression tyt p"
proof (cases p)
  case [simp]: (PNE f xs)
  from assms obtain Ts where sig: "func_sig f = Some Ts" by fastforce
  with assms have "list_all2 (is_of_type tyt) xs Ts" by simp
  hence "list_all2 (p3.is_of_type tyt) xs Ts" using g_is_of_type by metis
  moreover have "p3.func_sig f = Some Ts" using sig g_func_sig by simp
  ultimately show ?thesis by simp
qed

lemma g_eff_wf: "wf_effect tyt ε ⟹ p3.wf_effect tyt ε"
  using g_atom_wf g_pne_wf co_effect_wf by blast

lemma g_constT:
  "objT = p3.constT"
  using objT_def degoal_dom_sel p3.constT_def
  using constT_def map_le_iff_map_add_commute objm_le_objT by auto

lemma g_objT:
  "objT = p3.objT"
  using g_constT p3.constT_def p3.objT_def degoal_prob_sel by simp

lemma g_obj_of_type: "is_obj_of_type = p3.is_obj_of_type"
  unfolding is_obj_of_type_alt is_of_type_def of_type_def
    subtype_rel_def 
  unfolding p3.is_obj_of_type_alt p3.is_of_type_def p3.of_type_def
    p3.subtype_rel_def
  using g_objT degoal_prob_sel degoal_dom_sel by presburger

lemma g_wm_wf: "wf_world_model wm ⟹ p3.wf_world_model wm"
  using degoal_prob_sel(1) g_objT g_atom_wf co_wm_wf by metis

lemma g_fmla_atom_wf: "wf_fmla_atom tyt f ⟹ p3.wf_fmla_atom tyt f"
  using g_atom_wf co_fmla_atom_wf by blast

lemma g_func_assign_wf: "wf_func_assign f ⟹ p3.wf_func_assign f"
proof (induction f rule: wf_func_assign.induct)
  case (1 l r)
  hence "wf_primitive_numeric_expression objT l" by simp
  hence "p3.wf_primitive_numeric_expression p3.objT l" using g_pne_wf g_objT by metis
  thus ?case by (subst p3.wf_func_assign.simps(1))
qed simp_all

lemma is_of_type_term: "is_of_type tyt x t ⟷ is_of_type (ty_term xd tyt) (term.CONST x) t"
  unfolding is_of_type_def by simp

lemma list_all2_is_of_type_to_term:
  assumes "list_all2 (is_of_type tyt) xs Ts"
  shows "list_all2 (is_of_type (ty_term vart tyt)) (map term.CONST xs) Ts"
  using assms proof (induction xs Ts)
  case Cons thus ?case using is_of_type_term list_all2_Cons by simp
qed simp

lemma wf_pne_to_term:
  assumes "wf_primitive_numeric_expression tyt p"
  shows "wf_primitive_numeric_expression (ty_term vart tyt)
           (map_primitive_numeric_expression term.CONST p)"
proof (cases p)
  case [simp]: (PNE f xs)
  from assms obtain Ts where [simp]: "func_sig f = Some Ts" by fastforce
  with assms have "list_all2 (is_of_type tyt) xs Ts" by simp
  hence "list_all2 (is_of_type (ty_term vart tyt)) (map term.CONST xs) Ts"
    by (rule list_all2_is_of_type_to_term)
  thus ?thesis by simp
qed

lemma wf_numeric_expression_to_term:
  assumes "wf_numeric_expression tyt n"
  shows "wf_numeric_expression (ty_term vart tyt) (map_numeric_expression term.CONST n)"
  using assms by (induction n) (auto simp: wf_pne_to_term)

lemma wf_atom_to_term:
  assumes "wf_atom tyt a"
  shows "wf_atom (ty_term vart tyt) (map_atom term.CONST a)"
  using assms
proof (induction a)
  case (predAtm p xs)
  then obtain Ts where [simp]: "sig p = Some Ts" by fastforce
  hence match: "list_all2 (is_of_type tyt) xs Ts" using predAtm by simp
  hence "list_all2 (is_of_type (ty_term vart tyt)) (map term.CONST xs) Ts"
    by (rule list_all2_is_of_type_to_term)
  thus ?case by simp
qed (auto simp: wf_numeric_expression_to_term)

lemma wf_fmla_to_term:
  assumes "wf_fmla tyt F"
  shows "wf_fmla (ty_term vart tyt) (map_atom_fmla term.CONST F)"
  using assms by (induction F) (simp_all add: wf_atom_to_term)

lemma g_action_head_wf: "wf_action_head h ⟹ p3.wf_action_head h"
  by (cases h) simp

lemma g_simple_action_body_wf:
  assumes "tyt ⊆⇩m tyt3" and "wf_simple_action_body tyt b"
  shows "p3.wf_simple_action_body tyt3 b"
proof (cases b)
  case [simp]: (SimpleActionBody pre eff)
  from assms have "wf_fmla tyt pre" "wf_effect tyt eff" by simp_all
  hence "p3.wf_fmla tyt3 pre" "p3.wf_effect tyt3 eff"
    using assms(1) wf_fmla_mono wf_effect_mono g_fmla_wf g_eff_wf by blast+
  thus ?thesis by (simp add: domain_signature.wf_simple_action_body_alt)
qed

lemma g_acs_wf: "(∀a∈set (actions D3). p3.wf_classical_action_schema a)"
proof -
  (* carrying over original actions *)
  have 1: "p3.wf_classical_action_schema ac" if "wf_classical_action_schema ac" for ac
  proof (cases ac rule: ast_classical_action_schema_cases_unfold)
    case [simp]: (SimpleActionSchema n params pre eff)
    let ?tyt = "ty_term (map_of params) constT"
    let ?tyt3 = "ty_term (map_of params) p3.constT"
    have tyts: "?tyt ⊆⇩m ?tyt3"
      using g_constT constT_ss_objT by (auto intro: ty_term_mono)
    from that have "wf_action_head (ActionHead n params)"
              and "wf_simple_action_body ?tyt (SimpleActionBody pre eff)"
      by (simp_all add: Let_def)
    hence "p3.wf_action_head (ActionHead n params)"
      and "p3.wf_simple_action_body ?tyt3 (SimpleActionBody pre eff)"
      using g_action_head_wf g_simple_action_body_wf tyts by blast+
    thus ?thesis
      apply (subst SimpleActionSchema)
      apply (subst p3.wf_classical_action_schema.simps)
      by (simp add: Let_def)
  qed

  (* goal action well-formed *)
  let ?gac = "goal_ac term_goal"
  let ?tyt = "ty_term Map.empty p3.constT"
  have head: "p3.wf_action_head (ActionHead goal_ac_name [])" by simp
  have pre: "p3.wf_fmla ?tyt term_goal"
    unfolding term_goal_def
    using wf_P g_constT wf_fmla_to_term g_fmla_wf by metis
  have eff: "p3.wf_effect ?tyt goal_effect"
    (* g_preds_dist not needed, since goal_pred is the first in the list *)
    apply (subst p3.wf_effect.simps)
    apply (simp only: list.set Ball_def empty_iff insert_iff simp_thms)
    apply (subst p3.wf_fmla_atom.simps)
    apply (subst p3.wf_pred_atom.simps)
    by (simp add: p3.sig_def goal_pred_decl_def domain_signature.sig_def)
  from pre eff have body: "p3.wf_simple_action_body ?tyt (SimpleActionBody term_goal goal_effect)"
    apply (subst p3.wf_simple_action_body.simps) by simp
  from head body have "p3.wf_classical_action_schema ?gac"
    unfolding goal_ac_def
    apply (subst p3.wf_classical_action_schema.simps)
    by (simp add: Let_def)
  with 1 show ?thesis using wf_D(3) by simp
qed

text ‹The degoaled domain and problem are well-formed.›

lemma degoal_dom_sig_wf: "p3.wf_domain_signature"
  unfolding p3.wf_domain_signature_def
  using wf_D_sig(1) g_preds_dist g_preds_wf g_funcs_dist g_funcs_wf
        g_consts_dist g_consts_wf
  by (simp add: list_all_iff p3.wf_types_def wf_types_def)

lemma degoal_prob_sig_wf: "p3.wf_problem_signature"
  unfolding p3.wf_problem_signature_def
  using degoal_dom_sig_wf g_consts_dist by simp

lemma degoal_dom_wf: "p3.wf_classical_domain"
  unfolding p3.wf_classical_domain_def
  using degoal_dom_sig_wf g_acs_dist g_acs_wf by simp

lemma degoal_goal_fmla_wf: "p3.wf_fmla p3.objT (goal P3)"
  apply (subst degoal_prob_sel(4))
  apply (subst p3.wf_fmla.simps)
  apply (subst p3.wf_atom.simps)
  apply (subst p3.wf_pred_atom.simps)
  by (simp add: p3.sig_def goal_pred_decl_def domain_signature.sig_def)

lemma g_init_wf:
  "∀f∈set (init P3). p3.wf_fmla_atom p3.objT f ∨ p3.wf_func_assign f"
proof
  fix f assume "f ∈ set (init P3)"
  hence "f ∈ set (init P)" by simp
  with wf_P(4) have "wf_fmla_atom objT f ∨ wf_func_assign f" by blast
  thus "p3.wf_fmla_atom p3.objT f ∨ p3.wf_func_assign f"
    using g_fmla_atom_wf g_func_assign_wf g_objT by metis
qed

lemma degoal_prob_wf: "p3.wf_classical_problem"
  unfolding p3.wf_classical_problem_def
  using degoal_dom_wf degoal_prob_sig_wf wf_P(3) g_init_wf degoal_goal_fmla_wf
  by simp

end

sublocale wf_ast_classical_problem3 ⊆ p3_wf: wf_ast_classical_domain D3
  using degoal_dom_wf wf_ast_classical_domain.intro by simp

sublocale wf_ast_classical_problem3 ⊆ p3_wf: wf_ast_classical_problem P3
  using degoal_prob_wf
  by (auto intro: wf_ast_classical_problem.intro
      simp: wf_ast_classical_problem_def)

context wf_ast_classical_problem3 begin

text ‹The goal action resolves in the degoaled domain.›

lemma resolve_goal_ac:
  "p3.resolve_classical_action_schema goal_ac_name = Some (goal_ac term_goal)"
  apply (subst p3.resolve_classical_action_schema_def)
  apply (subst index_by_eq_Some_eq)
  using p3_wf.wf_D apply simp
  apply (subst degoal_prob_sel)
  apply (subst degoal_dom_sel)
  by (simp add: goal_ac_def)

lemma wf_goal_pa:
  "p3.wf_classical_plan_action π⇩g"
  apply (subst p3.wf_classical_plan_action.simps)
  apply (subst resolve_goal_ac)
  apply (subst goal_ac_def)
  apply (subst p3.action_params_match_def)
  by (force simp: p3.action_params_match_def list_all2_iff)

text ‹Mapping a closed formula through ‹term.CONST› and back is the identity.›

lemma term_to_obj: "ac_tsubst [] [] (term.CONST x) = x"
  unfolding ac_tsubst_def by simp

lemma term_to_obj_atom:
  "map_atom (ac_tsubst [] []) (map_atom term.CONST a) = a"
proof -
  have "map_atom (ac_tsubst [] []) (map_atom term.CONST a)
      = map_atom (λx. ac_tsubst [] [] (term.CONST x)) a"
    by (simp add: atom.map_comp comp_def)
  also have "... = map_atom id a"
    by (simp add: term_to_obj id_def)
  also have "... = a" by (simp add: atom.map_id)
  finally show ?thesis .
qed

lemma term_to_obj_fmla:
  "map_atom_fmla (ac_tsubst [] []) (map_atom_fmla term.CONST F) = F"
  using term_to_obj_atom by (induction F; simp)

end

end

