theory Classical_Definedness_Normalization_Semantics
  imports Classical_Definedness_Normalization
begin

section \<open>Definedness Explication Preserves Semantics\<close>

subsection \<open>Helper lemmas on \<open>foldr (\<^bold>\<and>) (map Atom _)\<close>\<close>

lemma foldr_and_imp_orig:
  assumes "\<A> \<Turnstile>\<^sub>m foldr (\<^bold>\<and>) (map Atom as) F"
  shows "\<A> \<Turnstile>\<^sub>m F"
  using assms by (induction as) auto

lemma foldr_and_if:
  assumes "\<A> \<Turnstile>\<^sub>m F"
      and "\<forall>a \<in> set as. \<A> a = Some True"
    shows "\<A> \<Turnstile>\<^sub>m foldr (\<^bold>\<and>) (map Atom as) F"
  using assms by (induction as) auto

lemma foldr_and_Not_imp_orig:
  assumes "\<A> \<Turnstile>\<^sub>m foldr (\<^bold>\<and>) (map (\<lambda>a. \<^bold>\<not>(Atom a)) as) F"
  shows "\<A> \<Turnstile>\<^sub>m F"
  using assms by (induction as) auto

lemma foldr_and_Not_if:
  assumes "\<A> \<Turnstile>\<^sub>m F"
      and "\<forall>a \<in> set as. \<A> a = Some False"
    shows "\<A> \<Turnstile>\<^sub>m foldr (\<^bold>\<and>) (map (\<lambda>a. \<^bold>\<not>(Atom a)) as) F"
  using assms by (induction as) auto

subsection \<open>Definedness atoms under a defined-PNE valuation\<close>

lemma definedness_atom_valuation:
  assumes "atoms F \<subseteq> dom (valuation M)"
      and "a \<in> set (definedness_atoms F)"
    shows "valuation M a = Some True"
proof -
  from assms(2) obtain p where p:
    "p \<in> set (formula_enumerate_primitive_numeric_expressions F)"
    "a = numericEqAtm (FunctionExpr p) (FunctionExpr p)"
    by (rule definedness_atoms_form)
  from p(1) assms(1) have "p \<in> dom (snd M)"
    using formula_atoms_in_dom_valuation_iff by fast
  thus ?thesis unfolding p(2) valuation_def by (cases "snd M p") auto
qed

lemma definedness_atoms_subset_dom_valuation:
  assumes "atoms F \<subseteq> dom (valuation M)"
  shows "set (definedness_atoms F) \<subseteq> dom (valuation M)"
  using definedness_atom_valuation[OF assms] by (auto simp: domIff)

subsection \<open>Divisor-nonzero witness atoms under a defined-divisor valuation\<close>

text \<open>The divisor-zero witness atoms are truth-neutral: whenever the original
  formula's atoms are in the valuation's domain, every divisor evaluates to a
  defined, nonzero value, so each witness atom \<open>y = 0\<close> evaluates to
  \<open>Some False\<close> — exactly what the negated literals in
  \<open>explicate_def_fmla\<close> require.\<close>

lemma divisor_zero_atom_valuation:
  assumes "atoms F \<subseteq> dom (valuation M)"
      and "a \<in> set (divisor_zero_atoms F)"
    shows "valuation M a = Some False"
proof -
  obtain y where
    y: "y \<in> set (formula_enumerate_divisor_expressions F)"
    and a: "a = numericEqAtm y (ConstantExpr 0)"
    using assms(2) by (rule divisor_zero_atoms_form)
  have PN: "set (formula_enumerate_primitive_numeric_expressions F) \<subseteq> dom (snd M)"
   and DV: "\<forall>d \<in> set (formula_enumerate_divisor_expressions F). d\<lbrakk>snd M\<rbrakk> \<noteq> Some 0"
    using assms(1) formula_atoms_in_dom_valuation_iff by blast+
  have "set (enumerate_primitive_numeric_expressions y) \<subseteq> dom (snd M)"
    using formula_divisor_pnes_subset[OF y] PN by blast
  moreover
  have "\<forall>d \<in> set (enumerate_divisor_expressions y). d\<lbrakk>snd M\<rbrakk> \<noteq> Some 0"
    using formula_enumerate_divisor_expressions_closed[OF y] DV by blast
  ultimately
  have "y\<lbrakk>snd M\<rbrakk> \<noteq> None"
    using numeric_expression_valuation_neq_None_iff by blast
  then obtain v where v: "y\<lbrakk>snd M\<rbrakk> = Some v" by blast
  hence "v \<noteq> 0" using DV y by fastforce
  thus ?thesis unfolding a valuation_def using v by simp
qed

subsection \<open>Key semantic equivalence\<close>

theorem explicate_def_fmla_semantics:
  "valuation M \<Turnstile>\<^sub>m explicate_def_fmla f \<longleftrightarrow> valuation M \<Turnstile>\<^sub>m f"
proof
  assume "valuation M \<Turnstile>\<^sub>m explicate_def_fmla f"
  thus "valuation M \<Turnstile>\<^sub>m f"
    unfolding explicate_def_fmla_def
    using foldr_and_imp_orig foldr_and_Not_imp_orig by blast
next
  assume sat: "valuation M \<Turnstile>\<^sub>m f"
  hence atoms_in: "atoms f \<subseteq> dom (valuation M)" by blast
  have div_sat: "valuation M \<Turnstile>\<^sub>m foldr (\<^bold>\<and>) (map (\<lambda>a. \<^bold>\<not>(Atom a)) (divisor_zero_atoms f)) f"
    by (rule foldr_and_Not_if[OF sat], rule ballI,
        rule divisor_zero_atom_valuation[OF atoms_in])
  show "valuation M \<Turnstile>\<^sub>m explicate_def_fmla f"
    unfolding explicate_def_fmla_def
    by (rule foldr_and_if[OF div_sat], rule ballI,
        rule definedness_atom_valuation[OF atoms_in])
qed

subsection \<open>Substitution commutes with explication\<close>

text \<open>Needed for the action-instantiation argument: substituting parameters
  into an explicated precondition yields the same formula as explicating the
  substituted precondition. The PNE-enumeration map lemmas are inherited from
  \<open>Classical_Definedness_Normalization\<close>.\<close>

lemma definedness_atoms_map:
  "definedness_atoms (map_formula (map_atom m) F)
    = map (map_atom m) (definedness_atoms F)"
  unfolding definedness_atoms_def Let_def
  by (simp add: formula_enumerate_primitive_numeric_expressions_map comp_def)

lemma enumerate_divisor_expressions_map:
  "enumerate_divisor_expressions (map_numeric_expression m e)
    = map (map_numeric_expression m) (enumerate_divisor_expressions e)"
  by (induction e) auto

lemma atom_enumerate_divisor_expressions_map:
  "atom_enumerate_divisor_expressions (map_atom m a)
    = map (map_numeric_expression m) (atom_enumerate_divisor_expressions a)"
  by (cases a) (auto simp: enumerate_divisor_expressions_map)

lemma formula_enumerate_divisor_expressions_map:
  "formula_enumerate_divisor_expressions (map_formula (map_atom m) F)
    = map (map_numeric_expression m) (formula_enumerate_divisor_expressions F)"
  by (induction F) (auto simp: atom_enumerate_divisor_expressions_map)

lemma divisor_zero_atoms_map:
  "divisor_zero_atoms (map_formula (map_atom m) F)
    = map (map_atom m) (divisor_zero_atoms F)"
  unfolding divisor_zero_atoms_def
  by (simp add: formula_enumerate_divisor_expressions_map comp_def)

lemma foldr_and_map:
  "map_formula (map_atom m) (foldr (\<^bold>\<and>) (map Atom as) f)
    = foldr (\<^bold>\<and>) (map Atom (map (map_atom m) as)) (map_formula (map_atom m) f)"
  by (induction as) auto

lemma foldr_and_Not_map:
  "map_formula (map_atom m) (foldr (\<^bold>\<and>) (map (\<lambda>a. \<^bold>\<not>(Atom a)) as) f)
    = foldr (\<^bold>\<and>) (map (\<lambda>a. \<^bold>\<not>(Atom a)) (map (map_atom m) as)) (map_formula (map_atom m) f)"
  by (induction as) auto

lemma explicate_def_fmla_map:
  "map_formula (map_atom m) (explicate_def_fmla f)
    = explicate_def_fmla (map_formula (map_atom m) f)"
  unfolding explicate_def_fmla_def
  by (simp add: foldr_and_map foldr_and_Not_map definedness_atoms_map divisor_zero_atoms_map)

subsection \<open>Plan-action enabledness is preserved\<close>

context ast_classical_problem_de begin

lemma inst_pre_explicate_def:
  "ground_action.precondition
     (instantiate_classical_action_schema (explicate_def_ac a) args)
   = explicate_def_fmla
     (ground_action.precondition (instantiate_classical_action_schema a args))"
  unfolding instantiate_classical_action_schema_alt explicate_def_ac_unfold
  by (simp add: explicate_def_fmla_map)

lemma inst_pre_iff_explicate_def:
  "valuation M \<Turnstile>\<^sub>m
     ground_action.precondition (instantiate_classical_action_schema a args)
   \<longleftrightarrow> valuation M \<Turnstile>\<^sub>m
     ground_action.precondition
       (instantiate_classical_action_schema (explicate_def_ac a) args)"
  unfolding inst_pre_explicate_def by (rule explicate_def_fmla_semantics[symmetric])

end

subsection \<open>Plan validity is preserved\<close>

text \<open>Explication only modifies precondition formulas: action names, parameters,
  and effects are unchanged. Combined with \<open>explicate_def_fmla_semantics\<close>, this
  lifts to a direct \<open>iff\<close> on plan validity. Plan restoration is the identity.\<close>

lemma map_of_pair_map: 
  "map_of (map (\<lambda>x. (f x, g x)) xs) n = map_option g (map_of (map (\<lambda>x. (f x, x)) xs) n)"
  by (induction xs) auto

lemma numeric_effects_defined_cong:
  assumes "ground_action.effect g' = ground_action.effect g"
  shows "numeric_effects_defined [g'] w \<longleftrightarrow> numeric_effects_defined [g] w"
  unfolding numeric_effects_defined_def action_list_numeric_update_function_def
            action_numeric_update_function_def
  by (simp add: assms lvalues_def image_image)

context ast_classical_problem_de begin

lemma ast_classical_action_schema_head_explicate [simp]:
  "ast_classical_action_schema.head (explicate_def_ac a) = ast_classical_action_schema.head a"
  by (cases a rule: ast_classical_action_schema_cases_unfold) simp

lemma d_de_resolve_classical_action_schema:
  "d_de.resolve_classical_action_schema n
   = map_option explicate_def_ac (resolve_classical_action_schema n)"
proof -
  have "d_de.resolve_classical_action_schema n
      = map_of (map (\<lambda>x. (ac_name x, explicate_def_ac x)) (actions D)) n"
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
  "p_de.wf_classical_plan_action \<pi> \<longleftrightarrow> wf_classical_plan_action \<pi>"
proof (cases \<pi>)
  case (SimplePlanAction n args)
  show ?thesis
    unfolding SimplePlanAction
              p_de.wf_classical_plan_action_simple
              wf_classical_plan_action_simple
              p_de_resolve_classical_action_schema
    by (auto split: option.splits)
qed

lemma p_de_res_inst_precondition:
  assumes "wf_classical_plan_action \<pi>" "res_inst \<pi> = Some g"
  shows "\<exists>g'. p_de.res_inst \<pi> = Some g'
    \<and> precondition g' = explicate_def_fmla (precondition g)
    \<and> effect g' = effect g"
proof (cases \<pi>)
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
  "p_de.res_inst \<pi> = None \<longleftrightarrow> res_inst \<pi> = None"
proof (cases \<pi>)
  case (SimplePlanAction n args)
  show ?thesis
    unfolding SimplePlanAction p_de.res_inst.simps res_inst.simps
              p_de_resolve_classical_action_schema
    by (cases "resolve_classical_action_schema n") auto
qed

lemma numeric_effects_non_intrf_explicate:
  assumes "wf_classical_plan_action \<pi>" "res_inst \<pi> = Some g" "p_de.res_inst \<pi> = Some g'"
  shows "numeric_effects_non_intrf g' = numeric_effects_non_intrf g"
proof -
  from p_de_res_inst_precondition[OF assms(1,2)] assms(3)
  have "effect g' = effect g" by auto
  thus ?thesis
    unfolding numeric_effects_non_intrf_def by simp
qed

lemma p_de_plan_action_enabled_iff:
  "p_de.plan_action_enabled \<pi> M \<longleftrightarrow> plan_action_enabled \<pi> M"
proof (cases "wf_classical_plan_action \<pi>")
  case False
  thus ?thesis
    unfolding plan_action_enabled_def p_de.plan_action_enabled_def by simp
next
  case True
  obtain g where g: "res_inst \<pi> = Some g" using res_inst_alt by blast
  obtain g' where g': "p_de.res_inst \<pi> = Some g'" using p_de.res_inst_alt by blast
  from p_de_res_inst_precondition[OF True g] g'
  have pre: "precondition g' = explicate_def_fmla (precondition g)"
   and eff: "effect g' = effect g" by auto
  have ne: "numeric_effects_non_intrf g' = numeric_effects_non_intrf g"
    using numeric_effects_non_intrf_explicate[OF True g g'] .
  have rhs: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect g'))
           = set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect g))"
    using eff by simp
  have pre_sem: "valuation M \<Turnstile>\<^sub>m precondition g' \<longleftrightarrow> valuation M \<Turnstile>\<^sub>m precondition g"
    unfolding pre by (rule explicate_def_fmla_semantics)
  have ned: "numeric_effects_defined [g'] (snd M) \<longleftrightarrow> numeric_effects_defined [g] (snd M)"
    using numeric_effects_defined_cong[OF eff] .
  show ?thesis
    unfolding plan_action_enabled_def p_de.plan_action_enabled_def
    unfolding g g' comp_apply option.sel Let_def
    by (simp add: ne rhs pre_sem ned)
qed

lemma p_de_res_inst_effect:
  "effect (the (p_de.res_inst \<pi>)) = effect (the (res_inst \<pi>))"
proof -
  have l: "p_de.res_inst \<pi> = Some (instantiate_classical_action_schema
      (the (p_de.resolve_classical_action_schema (name \<pi>))) (arguments \<pi>))"
    by (rule p_de.res_inst_alt)
  have r: "res_inst \<pi> = Some (instantiate_classical_action_schema
      (the (resolve_classical_action_schema (name \<pi>))) (arguments \<pi>))"
    by (rule res_inst_alt)
  show ?thesis
    unfolding l r option.sel p_de_resolve_classical_action_schema
    by (cases "resolve_classical_action_schema (name \<pi>)")
       (simp_all add: instantiate_classical_action_schema_alt)
qed

lemma p_de_execute_plan_action:
  "p_de.execute_plan_action \<pi> M = execute_plan_action \<pi> M"
  unfolding execute_plan_action_def p_de.execute_plan_action_def comp_apply
  by (simp add: p_de_res_inst_effect action_list_numeric_update_function_def
                action_numeric_update_function_def)

lemma p_de_valid_classical_plan_alt_iff:
  "p_de.valid_classical_plan_alt M \<pi>s M' \<longleftrightarrow> valid_classical_plan_alt M \<pi>s M'"
proof (induction \<pi>s arbitrary: M)
  case Nil show ?case by simp
next
  case (Cons \<pi> \<pi>s)
  show ?case
    by (simp add: Cons.IH p_de_plan_action_enabled_iff p_de_execute_plan_action)
qed

lemma p_de_I [simp]: "p_de.I = I"
  unfolding p_de.I_def I_def explicate_def_prob_sel by simp

lemma p_de_valid_classical_plan2_iff:
  "p_de.valid_classical_plan2 \<pi>s \<longleftrightarrow> valid_classical_plan2 \<pi>s"
  unfolding p_de.valid_classical_plan2_alt valid_classical_plan2_alt
  unfolding p_de_valid_classical_plan_alt_iff p_de_I explicate_def_prob_sel
  by (simp add: explicate_def_fmla_semantics)

theorem explicate_valid_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. p_de.valid_classical_plan2 \<pi>s')"
  using p_de_valid_classical_plan2_iff by blast

theorem explicate_plan_restore:
  "p_de.valid_classical_plan2 \<pi>s \<Longrightarrow> valid_classical_plan2 (restore_plan_explicate \<pi>s)"
  using p_de_valid_classical_plan2_iff unfolding restore_plan_explicate_def by simp

end

text \<open>Code setup.\<close>

lemmas explicate_def_code =
  definedness_atoms_def
  explicate_def_fmla_def
  explicate_def_ac.simps
  ast_classical_domain.explicate_def_dom_def
  ast_classical_problem.explicate_def_prob_def

declare explicate_def_code[code]

end
