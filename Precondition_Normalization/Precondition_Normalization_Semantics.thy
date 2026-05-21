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

lemma pnes_def_checks_map:
  "pnes_def_checks (map_formula (map_atom m) F) = map (map_atom m) (pnes_def_checks F)"
  unfolding pnes_def_checks_def Let_def
  by (simp add: formula_enumerate_primitive_numeric_expressions_map comp_def)

lemma prepend_atoms_to_conj_map:
  "map_formula (map_atom m) (prepend_atoms_to_conj as f)
    = prepend_atoms_to_conj (map (map_atom m) as) (map_formula (map_atom m) f)"
  unfolding prepend_atoms_to_conj_def by (induction as) auto

lemma pne_equiv_dnf_list_map:
  "map (map_formula (map_atom m)) (pne_equiv_dnf_list F)
    = pne_equiv_dnf_list (map_formula (map_atom m) F)"
proof -
  let ?h = "map_formula (map_atom m)"
  let ?ck = "pnes_def_checks F"
  have "map ?h (pne_equiv_dnf_list F)
      = map ?h (map (prepend_atoms_to_conj ?ck) (dnf_list F))"
    unfolding pne_equiv_dnf_list_def Let_def ..
  also have "... = map (\<lambda>c. prepend_atoms_to_conj (map (map_atom m) ?ck) (?h c)) (dnf_list F)"
    by (simp add: prepend_atoms_to_conj_map)
  also have "... = map (prepend_atoms_to_conj (pnes_def_checks (?h F)) \<circ> ?h) (dnf_list F)"
    by (simp add: pnes_def_checks_map comp_def)
  also have "... = map (prepend_atoms_to_conj (pnes_def_checks (?h F))) (map ?h (dnf_list F))"
    by simp
  also have "... = map (prepend_atoms_to_conj (pnes_def_checks (?h F))) (dnf_list (?h F))"
    by (simp add: dnf_list_map)
  finally show ?thesis unfolding pne_equiv_dnf_list_def Let_def .
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
  "\<A> \<Turnstile>\<^sub>m F \<longleftrightarrow> (atoms F \<subseteq> dom \<A> \<and> (\<exists>c\<in>set (dnf_list F). \<A> \<Turnstile>\<^sub>m c))"
proof (cases "atoms F \<subseteq> dom \<A>")
  case True
  thus ?thesis by (simp add: dnf_list_map_semantics')
next
  case False
  hence "\<not> \<A> \<Turnstile>\<^sub>m F" by (auto simp: map_formula_semantics_def)
  thus ?thesis using False by simp
qed

lemma prepend_atoms_to_conj_imp_orig:
  assumes  "\<A> \<Turnstile>\<^sub>m prepend_atoms_to_conj as F"
  shows "\<A> \<Turnstile>\<^sub>m F"
  using assms by (induction as arbitrary: F) (simp add: prepend_atoms_to_conj_def)+

lemma pne_equiv_dnf_list_imp_dnf_list:
  assumes "n < length (dnf_list F)"
    "\<A> \<Turnstile>\<^sub>m (pne_equiv_dnf_list F ! n)"
  shows "\<A> \<Turnstile>\<^sub>m (dnf_list F ! n)"
  using assms by (auto simp: pne_equiv_dnf_list_def intro: prepend_atoms_to_conj_imp_orig)

lemma prepend_atoms_to_conj_if:
  assumes "\<A> \<Turnstile>\<^sub>m F"
      and "\<forall>a \<in> (set as). \<A> a = Some True"
  shows "\<A> \<Turnstile>\<^sub>m prepend_atoms_to_conj as F"
  using assms 
proof (induction as)
  case Nil
  then show ?case by (simp add: prepend_atoms_to_conj_def)
next
  case (Cons a as)
  have "\<A> \<Turnstile>\<^sub>m prepend_atoms_to_conj as F" using prepend_atoms_to_conj_def Cons by auto
  moreover
  have "\<A> \<Turnstile>\<^sub>m Atom a" using Cons by simp
  moreover
  have "atoms (prepend_atoms_to_conj (a#as) F) \<subseteq> dom \<A>" using Cons by auto
  ultimately
  show ?case by (simp add: comp_def prepend_atoms_to_conj_def)
qed

lemma pnes_def_check_in_valuationI:
  assumes "atoms F \<subseteq> dom (valuation M)"
  shows "set (pnes_def_checks F) \<subseteq> dom (valuation M)"
proof -
  have "(set (formula_enumerate_primitive_numeric_expressions F) \<subseteq> dom (snd M))" (is "set ?fpnes \<subseteq> _")
    using assms formula_atoms_in_dom_valuation_iff by simp
  hence "set (concat (map enumerate_primitive_numeric_expressions (map FunctionExpr ?fpnes))) \<subseteq> dom (snd M)"
    (is "set (concat (map enumerate_primitive_numeric_expressions ?fnes)) \<subseteq> _")
    by simp
  hence "set (concat (map atom_enumerate_primitive_numeric_expressions (map (\<lambda>f. numericEqAtm f f) ?fnes))) \<subseteq> dom (snd M)"
    by simp
  hence "set (concat (map atom_enumerate_primitive_numeric_expressions (pnes_def_checks F))) \<subseteq> dom (snd M)"
    unfolding  pnes_def_checks_def Let_def by simp
  thus ?thesis using dom_valuation_iff by (cases M) auto
qed


lemma in_dom_snd_iff_valuation_eq: 
  assumes "eq_expr = Atom (numericEqAtm (FunctionExpr x) (FunctionExpr x))"
  shows "x \<in> dom (snd M) \<longleftrightarrow> valuation M \<Turnstile>\<^sub>m eq_expr"
  unfolding assms valuation_def by (cases "snd M x") auto

lemma pnes_def_check_valuation_semI:
  assumes "atoms F \<subseteq> dom (valuation M)"
      and "c \<in> set (pnes_def_checks F)"
    shows "valuation M \<Turnstile>\<^sub>m Atom c"
proof -
  obtain x where
    x: "c = numericEqAtm (FunctionExpr x) (FunctionExpr x)"
    "x \<in> set (formula_enumerate_primitive_numeric_expressions F)" 
    using assms(2) unfolding pnes_def_checks_def Let_def by auto
  thus ?thesis 
    apply (subst in_dom_snd_iff_valuation_eq[symmetric])
    using assms x formula_atoms_in_dom_valuation_iff assms by auto
qed

lemma pne_equiv_dnf_list_atoms_in_valuation_iff:
  assumes "c \<in> set (pne_equiv_dnf_list F)"
  shows "atoms F \<subseteq> dom (valuation M) \<longleftrightarrow> atoms c \<subseteq> dom (valuation M)"
  using assms by (force dest: pne_equiv_dnf_list_pnes simp: formula_atoms_in_dom_valuation_iff)

lemma pne_equiv_dnf_list_map_semantics:
  "valuation M \<Turnstile>\<^sub>m F \<longleftrightarrow> (\<exists>c\<in>set (pne_equiv_dnf_list F). valuation M \<Turnstile>\<^sub>m c)"
proof 
  assume a: "valuation M \<Turnstile>\<^sub>m F"

  have atoms_in_valuation: "atoms F \<subseteq> dom (valuation M)" using a by blast
  
  obtain c where
    c: "c \<in> set (dnf_list F)"
    "valuation M \<Turnstile>\<^sub>m c" using a dnf_list_map_semantics by metis

  have pne_checks_in_valuation: "set (pnes_def_checks F) \<subseteq> dom (valuation M)"
    using pnes_def_check_in_valuationI atoms_in_valuation by blast

  have val: "valuation M \<Turnstile>\<^sub>m prepend_atoms_to_conj (pnes_def_checks F) c" 
    apply (rule prepend_atoms_to_conj_if)
    apply (rule c(2))
    using pne_checks_in_valuation pnes_def_check_valuation_semI atoms_in_valuation by simp

  show "\<exists>c\<in>set (pne_equiv_dnf_list F). valuation M \<Turnstile>\<^sub>m c" 
    using val c unfolding pne_equiv_dnf_list_def by auto
next
  assume a: "\<exists>c\<in>set (pne_equiv_dnf_list F). valuation M \<Turnstile>\<^sub>m c"
  obtain c where
    c: "c \<in> set (pne_equiv_dnf_list F)"
    "valuation M \<Turnstile>\<^sub>m c" using a by blast

  have atoms_in_val: "atoms F \<subseteq> dom (valuation M)" using pne_equiv_dnf_list_atoms_in_valuation_iff c by blast
  
  obtain c' where
    c': "c = prepend_atoms_to_conj (pnes_def_checks F) c'"
    "c' \<in> set (dnf_list F)"
    using c unfolding pne_equiv_dnf_list_def by auto

  have val_sat: "valuation M \<Turnstile>\<^sub>m c'" using c c' prepend_atoms_to_conj_imp_orig by fast

  show "valuation M \<Turnstile>\<^sub>m F" using atoms_in_val val_sat c' dnf_list_map_semantics by blast
qed

lemma pne_equiv_dnf_list_conv_dnf_list_map_semantics:
  "(\<exists>c\<in>set (pne_equiv_dnf_list F). valuation M \<Turnstile>\<^sub>m c)
  \<longleftrightarrow> (atoms F \<subseteq> dom (valuation M) \<and> (\<exists>c \<in> set (dnf_list F). (valuation M) \<Turnstile>\<^sub>m c))" 
  apply (subst pne_equiv_dnf_list_map_semantics[symmetric])
  apply (subst dnf_list_map_semantics)
  by simp

context ast_classical_domain4 begin


lemma precond_prop_iff_split:
  "(\<exists>c \<in> set (pne_equiv_dnf_list (ac_pre a)). P c) \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). P (ac_pre a'))"
proof -
  let ?dnf = "pne_equiv_dnf_list (ac_pre a)"
  have "(\<exists>c \<in> set ?dnf. P c) \<longleftrightarrow> (\<exists>i < length ?dnf. P (?dnf ! i))"
    using in_set_conv_nth by metis
  also have "... \<longleftrightarrow> (\<exists>i < length ?dnf. P (ac_pre (split_ac a ! i)))"
    using split_ac_nth pne_equiv_dnf_list_map_semantics by auto
  also have "... \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). P (ac_pre a'))"
    using in_set_conv_nth split_ac_length pne_equiv_dnf_list_length by metis
  finally show ?thesis by simp
qed

lemma inst_pre_iff_split:
  shows "valuation M \<Turnstile>\<^sub>m precondition (instantiate_classical_action_schema a args) \<longleftrightarrow> 
    (\<exists>a' \<in> set (split_ac a). valuation M \<Turnstile>\<^sub>m precondition (instantiate_classical_action_schema a' args))"
proof -
  let ?h = "ac_tsubst (ac_params a) args"
  let ?inst_fmla = "map_atom_fmla ?h"

  have pre_eq: "ground_action.precondition (instantiate_classical_action_schema a args)
      = ?inst_fmla (ac_pre a)"
    by (simp add: instantiate_classical_action_schema_alt)

  have a'_pre: "ground_action.precondition (instantiate_classical_action_schema a' args)
      = ?inst_fmla (ac_pre a')" if "a' \<in> set (split_ac a)" for a'
    using instantiate_classical_action_schema_alt split_ac_sel(2)[OF that] by simp

  have map_dnf: "pne_equiv_dnf_list (?inst_fmla (ac_pre a))
      = map ?inst_fmla (pne_equiv_dnf_list (ac_pre a))"
    using pne_equiv_dnf_list_map[of ?h "ac_pre a"] by (simp add: comp_def)

  have "valuation M \<Turnstile>\<^sub>m ground_action.precondition (instantiate_classical_action_schema a args)
      \<longleftrightarrow> valuation M \<Turnstile>\<^sub>m ?inst_fmla (ac_pre a)"
    by (simp add: pre_eq)
  also have "... \<longleftrightarrow> (\<exists>c\<in>set (pne_equiv_dnf_list (?inst_fmla (ac_pre a))). valuation M \<Turnstile>\<^sub>m c)"
    by (rule pne_equiv_dnf_list_map_semantics)
  also have "... \<longleftrightarrow> (\<exists>c\<in>set (pne_equiv_dnf_list (ac_pre a)). valuation M \<Turnstile>\<^sub>m ?inst_fmla c)"
    unfolding map_dnf by simp
  also have "... \<longleftrightarrow> (\<exists>a'\<in>set (split_ac a). valuation M \<Turnstile>\<^sub>m ?inst_fmla (ac_pre a'))"
    by (rule precond_prop_iff_split)
  also have "... \<longleftrightarrow> (\<exists>a'\<in>set (split_ac a).
      valuation M \<Turnstile>\<^sub>m ground_action.precondition (instantiate_classical_action_schema a' args))"
    using a'_pre by metis
  finally show ?thesis .
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

lemma p_valid_classical_plan_from2:
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
    using split_pa_enabled valid_classical_plan_from2_Cons by blast
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
    unfolding split_ac_def Let_def
    using split_ac_names_length pne_equiv_dnf_list_length set_n_pre_mapsel(1) by metis
  thus ?thesis
    using assms split_names_prefix_length drop_lit_prefix by metis
qed

lemma restore_pa_execute:
  assumes "p4.wf_classical_plan_action \<pi>'"
  defines pi: "\<pi> \<equiv> restore_pa_split \<pi>'"
  shows "execute_plan_action \<pi> M = p4.execute_plan_action \<pi>' M"
  using assms
proof (induction \<pi>')
  case (SimplePlanAction n' args)

  note wf' = SimplePlanAction(1)

  obtain ac' where
    res': "p4.resolve_classical_action_schema n' = Some ac'"
    and in_acts': "ac' \<in> set (actions p4.D)"
    and name': "ac_name ac' = n'"
    using wf'[THEN p4.wf_pa_res_sas] by auto

  obtain ac where
    ac_split: "ac' \<in> set (split_ac ac)"
    and in_acts: "ac \<in> set (actions D)"
    using in_acts'
    unfolding split_dom_sel split_prob_sel split_acs_def by auto

  have name_name': "ac_name ac = drop_lit split_pre_pad (ac_name ac')"
    using restore_split_ac ac_split in_acts by presburger

  have \<pi>: "\<pi> = SimplePlanAction (ac_name ac) args"
    using name_name' name' SimplePlanAction restore_pa_split.simps by simp

  have res: "local.resolve_classical_action_schema (ac_name ac) = Some ac"
    using wf_ast_classical_domain.resolve_classical_action_schema_name
    using in_acts wf_P wf_ast_classical_domain_def by blast

  show "execute_plan_action \<pi> M = p4.execute_plan_action (SimplePlanAction n' args) M"
    using p_exec \<pi> ac_split res res' by presburger
qed

lemma restore_pa_enabled:
  assumes "p4.plan_action_enabled \<pi>' M"
  defines pi: "\<pi> \<equiv> restore_pa_split \<pi>'"
  shows "plan_action_enabled \<pi> M"
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
    using wf'[THEN p4.wf_pa_res_sas] by auto

  obtain ac where
    ac_split: "ac' \<in> set (split_ac ac)"
    and in_acts: "ac \<in> set (actions D)"
    using in_acts'
    unfolding split_dom_sel split_prob_sel split_acs_def by auto

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

  have pre_sat: "valuation M \<Turnstile>\<^sub>m precondition ((the o res_inst) \<pi>)"
    using pre_sat' unfolding comp_def p4.res_inst.simps res'
    unfolding \<pi> unfolding res_inst.simps res
    unfolding option.sel
    using inst_pre_iff_split
    using ac_split by blast

  show "plan_action_enabled \<pi> M" unfolding plan_action_enabled_def
    using wf effs_same non_int effs_def pre_sat by presburger
qed

lemma restore_plan_split_valid_from:
  assumes "p4.wf_world_model s" "p4.valid_classical_plan_from2 s \<pi>s'"
  shows "valid_classical_plan_from2 s (restore_plan_split \<pi>s')"
using assms proof (induction \<pi>s' arbitrary: s)
  case Nil thus ?case
    unfolding ast_classical_problem.valid_classical_plan_from2_alt split_prob_sel 
    by simp
next
  case (Cons \<pi>' \<pi>s')
  let ?pis = "restore_plan_split \<pi>s'"

  have enabled: "plan_action_enabled (restore_pa_split \<pi>') s" 
    using Cons restore_pa_enabled by auto

  have wf': "p4.wf_classical_plan_action \<pi>'" using Cons 
    unfolding p4.valid_classical_plan_from2_alt
    by (auto intro: p4.plan_action_enabled_props)

  have execute_equiv: "execute_plan_action (restore_pa_split \<pi>') s 
    = p4.execute_plan_action \<pi>' s"
    apply (rule restore_pa_execute)
    using wf' by presburger

  have valid: "valid_classical_plan_from2 (execute_plan_action (restore_pa_split \<pi>') s) ?pis"
  proof (rule Cons.IH)
    show "p4.wf_world_model (execute_plan_action (restore_pa_split \<pi>') s)"
      using p4_wf.wf_execute_stronger[OF wf'] \<open>p4.wf_world_model s\<close>
      using execute_equiv by auto
    show "p4.valid_classical_plan_from2 (execute_plan_action (restore_pa_split \<pi>') s) \<pi>s'"
      using \<open>p4.valid_classical_plan_from2 s (\<pi>' # \<pi>s')\<close> 
      unfolding p4.valid_classical_plan_from2_alt using execute_equiv by simp
  qed
  show ?case using valid_classical_plan_from2_Cons enabled valid by simp
qed

lemma p4_I: "p4.I = I"
  unfolding p4.I_def split_prob_sel I_def by order

theorem split_valid_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. p4.valid_classical_plan2 \<pi>s')"
  unfolding valid_classical_plan2_def p4.valid_classical_plan2_def p4_I
  using restore_plan_split_valid_from p_valid_classical_plan_from2
  using wf_I by blast

theorem restore_plan_split_valid:
  "p4.valid_classical_plan2 \<pi>s' \<Longrightarrow> valid_classical_plan2 (restore_plan_split \<pi>s')"
  unfolding valid_classical_plan2_def p4.valid_classical_plan2_def
  using restore_plan_split_valid_from wf_I by simp

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
