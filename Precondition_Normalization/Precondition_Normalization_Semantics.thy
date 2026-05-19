theory Precondition_Normalization_Semantics
  imports Precondition_Normalization
begin

section \<open> Precondition Normalization Preserves Semantics \<close>

text \<open> Applying a map to dnf_list \<close>

lemma neg_of_lit_map: "map_formula m (neg_of_lit l) = neg_of_lit (map_literal m l)"
  by (cases l) simp_all

lemma neg_conj_of_clause_map: "map_formula m (neg_conj_of_clause c)
  = neg_conj_of_clause (map (map_literal m) c)"
  unfolding neg_conj_of_clause_def
  apply (induction c) apply simp using neg_of_lit_map by auto

lemma neg_conj_of_clause_map2: "map ((map_formula m) \<circ> neg_conj_of_clause) D
  = map neg_conj_of_clause (map (map (map_literal m)) D)"
  using neg_conj_of_clause_map by auto

lemma nnf_map: "map_formula m (nnf F) = nnf (map_formula m F)"
  by (induction F rule: nnf.induct) auto

(* there's gotta be some easier way to prove this *)
(* I can't overload g in this proof, so I need a second instance g' *)
lemma lin_prod_map:
  assumes "\<And>x y. f (g x y) = g' (f x) (f y)"
  shows "map f [g x y. x \<leftarrow> xs, y \<leftarrow> ys] = [g' x y. x \<leftarrow> map f xs, y \<leftarrow> map f ys]"
proof -
  have aux: "map (\<lambda>x. f (g x)) xs = map f (map g xs)"
    for g :: "'a \<Rightarrow> 'b" and f :: "'b \<Rightarrow> 'c" and xs :: "'a list" by simp

  (* "map f [g x y. x \<leftarrow> xs, y \<leftarrow> ys] = map f (concat (map (\<lambda>x. map (g x) ys) xs))" *)
  have "map f [g x y. x \<leftarrow> xs, y \<leftarrow> ys] = (concat (map (map f) (map (\<lambda>x. map (g x) ys) xs)))"
    using map_concat by blast
  also have "... = concat (map ((map f) \<circ> (\<lambda>x. map (g x) ys)) xs)" by simp
  also have "... = concat (map (\<lambda>x. map f (map (g x) ys)) xs)" by (meson comp_apply)
  also have "... = concat (map (\<lambda>x. map (f \<circ> (g x)) ys) xs)" by simp
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. f (g x y)) ys) xs)"
    by (metis fun_comp_eq_conv[of f])
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. g' (f x) (f y)) ys) xs)"
    using assms by simp
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. g' (f x) y) (map f ys)) xs)"
    using aux by metis
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. g' x y) (map f ys)) (map f xs))"
    using aux[of "(\<lambda>x. map (\<lambda>y. g' x y) (map f ys))"] by metis
  finally show ?thesis by simp
qed

lemma append_prod_map:
  shows "map (map f) [x @ y. x \<leftarrow> xss, y \<leftarrow> yss] = [x @ y. x \<leftarrow> map (map f) xss, y \<leftarrow> map (map f) yss]"
  by (rule lin_prod_map) simp

lemma cnf_lists_map:
  assumes "is_nnf F"
  shows "map (map (map_literal m)) (cnf_lists F) = cnf_lists (map_formula m F)"
  using assms proof (induction F rule: cnf_lists.induct)
  case (6 F G)
    define mp where "mp = (map (map_literal m))"
    have "map mp (cnf_lists (F \<^bold>\<or> G)) = map mp [f @ g. f \<leftarrow> (cnf_lists F), g \<leftarrow> (cnf_lists G)]" by simp
    also have "... = [f @ g. f \<leftarrow> map mp (cnf_lists F), g \<leftarrow> map mp (cnf_lists G)]"
      unfolding mp_def using append_prod_map by auto
    also have "... = [f @ g. f \<leftarrow> cnf_lists (map_formula m F), g \<leftarrow> cnf_lists (map_formula m G)]"
      using 6 unfolding mp_def by fastforce
    finally show ?case unfolding mp_def by simp
qed simp_all

lemma dnf_list_map: "map (map_formula m) (dnf_list F) = dnf_list (map_formula m F)"
proof -
  have "map (map_formula m) (dnf_list F)
    = map (map_formula m) (map neg_conj_of_clause (cnf_lists (nnf (\<^bold>\<not> F))))"
    unfolding dnf_list_def ..
  also have "... = map ((map_formula m) \<circ> neg_conj_of_clause) (cnf_lists (nnf (\<^bold>\<not> F)))"
    by simp
  also have "... = map neg_conj_of_clause (map (map (map_literal m)) (cnf_lists (nnf (\<^bold>\<not> F))))"
    using neg_conj_of_clause_map by auto
  also have "... = map neg_conj_of_clause (cnf_lists (map_formula m (nnf (\<^bold>\<not> F))))"
    using cnf_lists_map by (metis is_nnf_nnf)
  also have "... = map neg_conj_of_clause (cnf_lists (nnf (\<^bold>\<not> (map_formula m F))))"
    using nnf_map formula.map(3) by metis
  finally show ?thesis unfolding dnf_list_def by simp
qed

(* end map *)

text \<open> \<open>dnf_list\<close> under \<open>map_formula_semantics\<close>. Unlike the total-valuation version, this
  needs every atom of \<open>F\<close> to be in the domain of \<open>\<A>\<close>: \<open>\<Turnstile>\<^sub>m\<close> is \<open>False\<close> on
  atoms outside the domain, and an individual DNF clause may mention fewer atoms than \<open>F\<close>. \<close>

lemma dnf_list_map_semantics':
  assumes "atoms F \<subseteq> dom \<A>"
  shows "(\<A> \<Turnstile>\<^sub>m F) \<longleftrightarrow> (\<exists>c\<in>set (dnf_list F). \<A> \<Turnstile>\<^sub>m c)"
proof -
  have F: "(\<A> \<Turnstile>\<^sub>m F) = ((the \<circ> \<A>) \<Turnstile> F)"
    using assms by (auto simp: map_formula_semantics_def)
  have c: "(\<A> \<Turnstile>\<^sub>m c) = ((the \<circ> \<A>) \<Turnstile> c)" if "c \<in> set (dnf_list F)" for c
  proof -
    have "atoms c \<subseteq> atoms F" using that by (simp add: dnf_list_atoms)
    with assms have "atoms c \<subseteq> dom \<A>" by simp
    thus ?thesis by (auto simp: map_formula_semantics_def)
  qed
  have "(\<A> \<Turnstile>\<^sub>m F) = ((the \<circ> \<A>) \<Turnstile> F)" by (rule F)
  also have "... = (\<exists>c\<in>set (dnf_list F). (the \<circ> \<A>) \<Turnstile> c)" by (rule dnf_list_semantics)
  also have "... = (\<exists>c\<in>set (dnf_list F). \<A> \<Turnstile>\<^sub>m c)" by (auto simp: c)
  finally show ?thesis .
qed

lemma dnf_list_map_semantics:
  shows "\<A> \<Turnstile>\<^sub>m F \<longleftrightarrow> (atoms F \<subseteq> dom \<A> \<and> (\<exists>c\<in>set (dnf_list F). \<A> \<Turnstile>\<^sub>m c))"
proof (cases "atoms F \<subseteq> dom \<A>")
  case True
  thus ?thesis by (simp add: dnf_list_map_semantics')
next
  case False
  hence "\<not> \<A> \<Turnstile>\<^sub>m F" by (auto simp: map_formula_semantics_def)
  thus ?thesis using False by simp
qed


context ast_classical_domain4 begin

lemma precond_prop_iff_split:
  "(\<exists>c \<in> set (dnf_list (ac_pre a)). P c) \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). P (ac_pre a'))"
proof -
  let ?dnf = "dnf_list (ac_pre a)"
  have "(\<exists>c \<in> set ?dnf. P c) \<longleftrightarrow> (\<exists>i < length ?dnf. P (?dnf ! i))"
    using in_set_conv_nth by metis
  also have "... \<longleftrightarrow> (\<exists>i < length ?dnf. P (ac_pre (split_ac a ! i)))"
    using split_ac_nth by auto
  also have "... \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). P (ac_pre a'))"
    using in_set_conv_nth split_ac_len by metis
  finally show ?thesis by simp
qed

lemma inst_pre_iff_split:
  shows "valuation M \<Turnstile>\<^sub>m precondition (instantiate_classical_action_schema a args) \<longleftrightarrow> 
    (atoms (precondition (instantiate_classical_action_schema a args)) \<subseteq> dom (valuation M) \<and>
    (\<exists>a' \<in> set (split_ac a). valuation M \<Turnstile>\<^sub>m precondition (instantiate_classical_action_schema a' args)))"
proof -
  let ?inst_fmla = "map_atom_fmla (ac_tsubst (ac_params a) args)"

  have "valuation M \<Turnstile>\<^sub>m precondition (instantiate_classical_action_schema a args) \<longleftrightarrow>
    valuation M \<Turnstile>\<^sub>m ?inst_fmla (ac_pre a)"
    using instantiate_classical_action_schema_alt by simp
  also have "... \<longleftrightarrow> (atoms (precondition (instantiate_classical_action_schema a args)) \<subseteq> dom (valuation M)
  \<and> (\<exists>c\<in>set (dnf_list (?inst_fmla (ac_pre a))). valuation M \<Turnstile>\<^sub>m c))"
    using dnf_list_map_semantics by (cases a rule: ast_classical_action_schema_cases_unfold) simp
  also have "... \<longleftrightarrow> (atoms (precondition (instantiate_classical_action_schema a args)) \<subseteq> dom (valuation M)
    \<and> (\<exists>a' \<in> set (split_ac a). 
    valuation M \<Turnstile>\<^sub>m precondition (instantiate_classical_action_schema a' args)))"
  proof -
    have "(\<exists>c\<in>set (dnf_list (?inst_fmla (ac_pre a))). valuation M \<Turnstile>\<^sub>m c)  
              \<longleftrightarrow> (\<exists>c \<in> set (map ?inst_fmla (dnf_list (ac_pre a))). valuation M \<Turnstile>\<^sub>m c)"
      using dnf_list_map[of "map_atom (ac_tsubst (ac_params a) args)"] by auto
    also have "... \<longleftrightarrow> (\<exists>c \<in> set (dnf_list (ac_pre a)). valuation M \<Turnstile>\<^sub>m ?inst_fmla c)" by simp
    also have "... \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). valuation M \<Turnstile>\<^sub>m ?inst_fmla (ac_pre a'))"
      using precond_prop_iff_split by simp
    finally show ?thesis using instantiate_classical_action_schema_alt split_ac_sel by simp
  qed
  finally show ?thesis by simp
qed


lemma (in ast_classical_problem4) p_ac_params_match:
  assumes "a' \<in> set (split_ac a)"
  shows "action_params_match (head a) = action_params_match (head a')"
  using split_ac_sel(2)[OF assms] action_params_match_def by presburger

lemma (in ast_classical_problem4) p_effect_same:
  assumes "b' \<in> set (split_ac b)"
          "resolve_classical_action_schema n = Some b" 
          "p4.resolve_classical_action_schema n' = Some b'"
        shows "effect ((the o res_inst) (SimplePlanAction n args)) = effect ((the o p4.res_inst) (SimplePlanAction n' args))"
  using instantiate_classical_action_schema_alt
  using split_ac_sel[OF assms(1)] assms(2-) by auto
  
lemma (in ast_classical_problem4) p_exec:
  assumes "a' \<in> set (split_ac a)"
    "resolve_classical_action_schema n = Some a" "p4.resolve_classical_action_schema n' = Some a'"
  shows "execute_plan_action (SimplePlanAction n args) = p4.execute_plan_action (SimplePlanAction n' args)"
proof -
  have "effect ((the o res_inst) (SimplePlanAction n args)) = effect ((the o p4.res_inst) (SimplePlanAction n' args))"
    using assms p_effect_same by simp
  hence "apply_ground_actions [(the o res_inst) (SimplePlanAction n args)] = 
    apply_ground_actions [(the o p4.res_inst) (SimplePlanAction n' args)]"
    using apply_ground_actions_equiv_weak by auto
  thus ?thesis
    unfolding ast_classical_problem.execute_plan_action_def 
    by simp
qed

end

context wf_ast_classical_problem4 begin

lemma split_pa_enabled:
  assumes "plan_action_enabled \<pi> M"
  shows "\<exists>\<pi>'. p4.plan_action_enabled \<pi>' M \<and> (execute_plan_action \<pi> M = p4.execute_plan_action \<pi>' M)"
proof (cases \<pi>)
  case [simp]: (SimplePlanAction n args)

  obtain a where 
    a: "resolve_classical_action_schema n = Some a" 
    "action_params_match (head a) args"
    "a \<in> set (actions D)"
    using plan_action_enabled_props[OF assms] 
    using wf_pa_refs_ac by force

  have v_pre: "valuation M \<Turnstile>\<^sub>m precondition (instantiate_classical_action_schema a args)"
    using plan_action_enabled_props[OF assms] a by simp

  obtain a' where 
    a': "a' \<in> set (split_ac a)"
    "valuation M \<Turnstile>\<^sub>m precondition (instantiate_classical_action_schema a' args)"
    "atoms (ground_action.precondition (instantiate_classical_action_schema a' args)) \<subseteq> dom (valuation M)"
    using v_pre inst_pre_iff_split by metis

  let ?pi = "SimplePlanAction n args"
  let ?pi' = "SimplePlanAction (ac_name a') args"

  (* precondition satisfied *)
  from a'(1) have "a' \<in> set (actions D4)" using a(3) split_dom_sel
    unfolding split_acs_def by auto
  hence res': "d4.resolve_classical_action_schema (ac_name a') = Some a'" using res_aux by simp
  with a'(2) have sat': "valuation M \<Turnstile>\<^sub>m precondition ((the o p4.res_inst) ?pi')"
    by simp

  (* well-formed *)
  have "action_params_match (head a') args"
    using a'(1) a(2) p_ac_params_match by simp
  hence wf': "p4.wf_classical_plan_action ?pi'"
    using res'  p4.wf_classical_plan_action_simple by fastforce

  (* defined *)
  have effs_same: "effect ((the o res_inst) \<pi>) = effect ((the o p4.res_inst) ?pi')"
    using a' p_effect_same a(1) res' by auto
  
  have "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the o res_inst) \<pi>))) \<subseteq> dom (snd M)"
    using assms plan_action_enabled_props by presburger
  hence effs_defined': "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the o p4.res_inst) ?pi'))) \<subseteq> dom (snd M)"
    using effs_same by argo

  (* non-interfering *)
  have "numeric_effects_non_intrf ((the o res_inst) \<pi>)" 
    using assms plan_action_enabled_props by blast
  hence non_int': "numeric_effects_non_intrf ((the o p4.res_inst) ?pi')"
    using numeric_effects_non_intrf_def effs_same by auto

  from wf' sat' non_int' effs_defined' have enab': "p4.plan_action_enabled ?pi' M"
    using p4.plan_action_enabled_def by presburger
  thus ?thesis using p_exec a'(1) a(1) res' by auto
qed

lemma p_valid_plan_from:
  assumes "wf_world_model s" "valid_classical_plan_from2 s \<pi>s"
  shows "\<exists>\<pi>s'. p4.valid_classical_plan_from2 s \<pi>s'"
using assms proof (induction \<pi>s arbitrary: s)
  case Nil thus ?case
    unfolding p4.valid_classical_plan_from2_alt valid_classical_plan_from2_alt split_prob_sel
    apply (intro exI)
    apply (subst p4.valid_classical_plan_alt.simps(1))
    by simp
next
  case (Cons \<pi> \<pi>s)
  then obtain \<pi>' where pi': "p4.plan_action_enabled \<pi>' s" "execute_plan_action \<pi> s = p4.execute_plan_action \<pi>' s"
    using split_pa_enabled valid_plan_from_Cons by blast
  obtain \<pi>s' where "p4.valid_classical_plan_from2 (p4.execute_plan_action \<pi>' s) \<pi>s'"
  proof -
    have "valid_classical_plan_from2 (execute_plan_action \<pi> s) \<pi>s" using Cons(3) 
      unfolding valid_classical_plan_from2_alt by simp
    hence valid': "valid_classical_plan_from2 (p4.execute_plan_action \<pi>' s) \<pi>s" using pi' by simp

    have wf_wm': "p4.wf_world_model s" using Cons by simp
    
    have wf_act': "p4.wf_classical_plan_action \<pi>'" using Cons pi'(1) p4.plan_action_enabled_props by simp
    have "\<exists>\<pi>s'. p4.valid_classical_plan_from2 (p4.execute_plan_action \<pi>' s) \<pi>s'" 
      apply (rule Cons.IH)
      using  p4_wf.wf_execute_stronger[OF wf_act'] wf_wm' apply simp
      using valid' by blast
    moreover
    assume "\<And>\<pi>s'. p4.valid_classical_plan_from2 (p4.execute_plan_action \<pi>' s) \<pi>s' \<Longrightarrow> thesis"
    ultimately
    show ?thesis by blast
  qed
  then obtain M' where
    "p4.valid_classical_plan_alt (p4.execute_plan_action \<pi>' s) \<pi>s' M'" 
    "valuation M' \<Turnstile>\<^sub>m goal split_prob" unfolding p4.valid_classical_plan_from2_alt by blast
  thus ?case unfolding p4.valid_classical_plan_from2_alt 
    apply (intro exI)
    apply (subst p4.valid_classical_plan_alt.simps(2))
    using pi'(1) by force
qed

lemma (in ast_classical_domain4) restore_split_ac:
  assumes "a \<in> set (actions D)" "a' \<in> set (split_ac a)"
  shows "drop_lit split_pre_pad (ac_name a') = ac_name a"
proof -
  from assms have "ac_name a' \<in> set (map ac_name (split_ac a))" by auto
  hence "ac_name a' \<in> set (split_ac_names a)"
    unfolding split_ac_def
    using split_ac_len set_n_pre_mapsel by metis
  thus ?thesis
    using assms split_names_prefix_length drop_lit_prefix by metis
qed

lemma restore_pa_enabled:
  assumes "p4.plan_action_enabled \<pi>' M"
  defines pi: "\<pi> \<equiv> restore_pa_split \<pi>'"
  assumes atoms_pi: "atoms (precondition ((the o res_inst) \<pi>)) \<subseteq> dom (valuation M)"
  shows "plan_action_enabled \<pi> M" 
    "(execute_plan_action \<pi> M = p4.execute_plan_action \<pi>' M)"
  using assms
proof (induction \<pi>')
  case (SimplePlanAction n' args)

  have
    wf': "p4.wf_classical_plan_action (SimplePlanAction n' args)"
    and non_int': "numeric_effects_non_intrf ((the \<circ> p4.res_inst) (SimplePlanAction n' args))"
    and effs_def': "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the \<circ> p4.res_inst) (SimplePlanAction n' args)))) \<subseteq> dom (snd M)"
    and pre_sat': "valuation M \<Turnstile>\<^sub>m ground_action.precondition ((the \<circ> p4.res_inst) (SimplePlanAction n' args))"
    using p4.plan_action_enabled_props[OF SimplePlanAction(1)] by blast+

  obtain ac' where
    res': "p4.resolve_classical_action_schema n' = Some ac'" 
    and in_acts': "ac' \<in> set (actions p4.D)" 
    and name': "ac_name ac' = n'" 
    and params_match': "p4.action_params_match (ac_head ac') args"
    using wf'[THEN p4.wf_pa_res_sas]
    by auto

  obtain ac where
    ac_split: "ac' \<in> set (split_ac ac)"
    and in_acts: "ac \<in> set (actions D)"
    using in_acts'
    unfolding split_dom_sel split_prob_sel split_acs_def 
    by auto

  have name_name': "ac_name ac = drop_lit split_pre_pad (ac_name ac')"
    using restore_split_ac ac_split in_acts by presburger

  have \<pi>: "\<pi> = SimplePlanAction (ac_name ac) args" 
    using name_name' name' SimplePlanAction restore_pa_split.simps by simp

  have res: "local.resolve_classical_action_schema (ac_name ac) = Some ac"
    using wf_ast_classical_domain.resolve_classical_action_schema_name
    using in_acts wf_P wf_ast_classical_domain_def by blast

  have params_match: "action_params_match (ac_head ac) args" 
    using p_ac_params_match ac_split params_match' by presburger

  have wf: "wf_classical_plan_action \<pi>"
    using res params_match \<pi> by (cases ac) simp

  have effs_same: "effect ((the o res_inst) \<pi>) = 
    effect ((the o p4.res_inst) (SimplePlanAction n' args))" 
    unfolding \<pi> apply (rule p_effect_same)
    using res ac_split res' by blast+

  have non_int: "numeric_effects_non_intrf ((the o res_inst) \<pi>)" 
    using non_int' effs_same numeric_effects_non_intrf_equiv_weak by fast

  have effs_def: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the o res_inst) \<pi>))) \<subseteq> dom (snd M)"
    using effs_def' effs_same by simp

  have pre_atoms: "atoms (precondition (instantiate_classical_action_schema ac args)) \<subseteq> dom (valuation M)"
    using atoms_pi \<pi> res by simp 
  have pre_sat: "valuation M \<Turnstile>\<^sub>m precondition ((the o res_inst) \<pi>)"
    using pre_sat' unfolding comp_def p4.res_inst.simps res'
    unfolding \<pi> unfolding res_inst.simps res
    unfolding option.sel
    using inst_pre_iff_split
    using pre_atoms ac_split by blast

  show enabled: "plan_action_enabled \<pi> M" unfolding plan_action_enabled_def
    using wf effs_same non_int effs_def pre_sat by presburger

  show execute: "execute_plan_action \<pi> M = p4.execute_plan_action (SimplePlanAction n' args) M"
    using p_exec \<pi>
    using ac_split res res' by presburger
qed

lemma restore_plan_split_valid_from:
  assumes "p4.wf_world_model s" "p4.valid_plan_from s \<pi>s'"
  shows "valid_plan_from s (restore_plan_split \<pi>s')"
using assms proof (induction \<pi>s' arbitrary: s)
  case Nil thus ?case
  unfolding ast_classical_problem.valid_plan_def ast_classical_problem.valid_plan_from_def split_prob_sel list.map(1)
    using ast_classical_problem.plan_action_path_Nil by metis
next
  case (Cons \<pi>' \<pi>s')
  let ?pi = "restore_pa_split \<pi>'" and ?pis = "restore_plan_split \<pi>s'"
  from Cons have pi: "plan_action_enabled ?pi s" "execute_plan_action ?pi s = p4.execute_plan_action \<pi>' s"
    using restore_pa_enabled p4.wf_wm_basic p4.valid_plan_from_Cons wf_wm_basic by simp_all

  from Cons have "valid_plan_from (execute_plan_action ?pi s) ?pis"
    using p4.wf_execute p4.valid_plan_from_Cons pi(2) by simp
  thus ?case using valid_plan_from_Cons p_wf_wm pi(1) by simp
qed

theorem split_valid_iff:
  "(\<exists>\<pi>s. valid_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. p4.valid_plan \<pi>s')"
  unfolding ast_classical_problem.valid_plan_def
  using restore_plan_split_valid_from p_valid_plan_from
  by (metis I_def p4.I_def p4.wf_I wf_I split_prob_sel(3))

theorem restore_plan_split_valid:
  "p4.valid_plan \<pi>s' \<Longrightarrow> valid_plan (restore_plan_split \<pi>s')"
  unfolding ast_classical_problem.valid_plan_def
  using restore_plan_split_valid_from p4.wf_I by simp

end

(* under which conditions does the set of defined pnes not change *)

subsection \<open> Code Setup \<close>

lemmas precond_norm_code =
  n_clauses_def
  ast_classical_domain.max_n_clauses_def
  ast_classical_domain.split_pre_pad_def
  ast_classical_domain.split_ac_names_def
  ast_classical_domain.split_ac_def
  ast_classical_domain.split_acs_def
  ast_classical_domain.split_dom_def
  ast_classical_problem.split_prob_def
  ast_classical_domain.restore_pa_split.simps
declare precond_norm_code[code]

end
