theory PDDL_Relaxation_Semantics
  imports PDDL_Relaxation
begin

section \<open> Relaxation Preserves Semantics \<close>

lemma (in normalized_domain_rx) rx_resolve:
  assumes "resolve_classical_action_schema n = Some a"
  shows "dx.resolve_classical_action_schema n = Some (relax_ac a)"
  using assms res_aux dx.res_aux by simp

lemma (in normalized_domain_rx) rx_resolve':
  assumes "dx.resolve_classical_action_schema n = Some a'"
  obtains a where "resolve_classical_action_schema n = Some a"
  using that assms res_aux dx.res_aux by auto

lemma (in normalized_domain_rx) rx_resolve_map:
  "dx.resolve_classical_action_schema n
      = map_option relax_ac (resolve_classical_action_schema n)"
proof (cases "resolve_classical_action_schema n")
  case None
  have "dx.resolve_classical_action_schema n = None"
  proof (rule ccontr)
    assume "dx.resolve_classical_action_schema n \<noteq> None"
    then obtain a' where "dx.resolve_classical_action_schema n = Some a'" by auto
    then obtain a where "a \<in> set (actions D)" "ac_name (relax_ac a) = n"
      using dx.res_aux relax_ac_sel by auto
    hence "resolve_classical_action_schema n = Some a"
      using res_aux relax_ac_sel by simp
    with None show False by simp
  qed
  with None show ?thesis by simp
next
  case (Some a)
  thus ?thesis using rx_resolve by simp
qed

lemma (in ast_classical_domain) relax_ac_head:
  "ac_head (relax_ac a) = ac_head a"
  by (cases a rule: ast_classical_action_schema_cases_unfold) simp

lemma (in ast_classical_problem_rx) rx_action_params_match:
  "px.action_params_match = action_params_match"
  unfolding problem_signature.action_params_match_def rx_is_obj_of_type ..

lemma (in normalized_problem_rx) rx_wf_classical_plan_action:
  "px.wf_classical_plan_action = wf_classical_plan_action"
proof (rule ext)
  fix p
  show "px.wf_classical_plan_action p = wf_classical_plan_action p"
  proof (cases p)
    case (SimplePlanAction n args)
    show ?thesis
      unfolding SimplePlanAction
      using rx_resolve_map[of n]
      by (cases "resolve_classical_action_schema n";
          simp add: px.wf_classical_plan_action_simple
                    ast_classical_problem.wf_classical_plan_action_simple
                    rx_action_params_match relax_ac_head)
  qed
qed

lemma (in wf_ast_classical_problem) valid_classical_plan_alt_single:
  assumes "valid_classical_plan_alt N [p] M"
  shows "plan_action_enabled p N" "execute_plan_action p N = M"
  using assms  execute_plan_action_def
    plan_action_enabled_def by auto

lemma (in - ) relax_cw_entailment:
  assumes "lwm_basic (fst M)" "lwm_basic (fst M')" "fst M \<subseteq> fst M'"
    "valuation M \<Turnstile>\<^sub>m \<phi>" "is_conj \<phi>"
  shows "valuation M' \<Turnstile>\<^sub>m relax_conj \<phi>"
proof -
  have "valuation M' \<Turnstile>\<^sub>m relax_conj \<phi>" if "valuation M \<Turnstile>\<^sub>m \<phi>"
    using assms(5,4) that apply (induction \<phi> rule: conj_induct_atoms)
    using assms(1-3) valuation_def by auto
  with assms show ?thesis by simp
qed

lemma (in normalized_problem_rx) rx_enabled:
  assumes "lwm_basic (fst M)" "lwm_basic (fst M')" "fst M \<subseteq> fst M'" "snd M = snd M'"
    "plan_action_enabled \<pi> M"
  shows "px.plan_action_enabled \<pi> M'"
proof (cases \<pi>)
  case (SimplePlanAction n args)
  have wf_pi: "wf_classical_plan_action \<pi>"
    using assms(5) plan_action_enabled_props(1) by blast
  then obtain a where a: "resolve_classical_action_schema n = Some a"
    unfolding SimplePlanAction
    using ast_classical_problem.wf_classical_plan_action_simple
    by (cases "resolve_classical_action_schema n") auto
  hence a': "px.resolve_classical_action_schema n = Some (relax_ac a)"
    using rx_resolve by simp

  have pre_conj: "is_conj (ac_pre a)"
    using a normalized_dom[unfolded norm_dom_defs] res_aux by fast

  \<comment> \<open>Split the assumption into the four constituents of \<open>plan_action_enabled\<close>.\<close>
  from assms(5) have
    nint: "numeric_effects_non_intrf ((the o res_inst) \<pi>)" and
    ndom: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions
                  (ground_action.effect ((the o res_inst) \<pi>))) \<subseteq> dom (snd M)" and
    sat:  "valuation M \<Turnstile>\<^sub>m ground_action.precondition ((the o res_inst) \<pi>)"
    using plan_action_enabled_props by blast+

  \<comment> \<open>Explicit forms of the unrelaxed and relaxed instantiations of \<open>\<pi>\<close>.\<close>
  have inst:
    "(the o res_inst) \<pi> = GroundAction
        (map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a))
        (map_ast_effect (ac_tsubst (ac_params a) args) (ac_eff a))"
    unfolding SimplePlanAction
    using a
    by (simp add: domain_signature.instantiate_classical_action_schema_alt
                  simple_action_instantiations.res_inst.simps)

  have rx_inst:
    "(the o px.res_inst) \<pi> = GroundAction
        (map_atom_fmla (ac_tsubst (ac_params a) args) (relax_conj (ac_pre a)))
        (map_ast_effect (ac_tsubst (ac_params a) args) (relax_eff (ac_eff a)))"
    unfolding SimplePlanAction
    using a' relax_ac_sel
    by (simp add: domain_signature.instantiate_classical_action_schema_alt
                  simple_action_instantiations.res_inst.simps)

  \<comment> \<open>Goal 1: well-formedness of the (relaxed) plan action.\<close>
  have wf_rx: "px.wf_classical_plan_action \<pi>"
    using wf_pi rx_wf_classical_plan_action by metis

  \<comment> \<open>Goal 2 & 3: numeric components are unchanged by relaxation.\<close>
  have rx_same_ne:
    "numeric_effects (ground_action.effect ((the o px.res_inst) \<pi>))
       = numeric_effects (ground_action.effect ((the o res_inst) \<pi>))"
    unfolding inst rx_inst by (cases "ac_eff a") simp

  have nint_rx: "numeric_effects_non_intrf ((the o px.res_inst) \<pi>)"
    using nint unfolding numeric_effects_non_intrf_def rx_same_ne by simp

  have rx_same_rhs:
    "ast_effect_enumerate_rhs_primitive_numeric_expressions
         (ground_action.effect ((the o px.res_inst) \<pi>))
       = ast_effect_enumerate_rhs_primitive_numeric_expressions
         (ground_action.effect ((the o res_inst) \<pi>))"
    unfolding inst rx_inst by (cases "ac_eff a") simp

  have ndom_rx:
    "set (ast_effect_enumerate_rhs_primitive_numeric_expressions
            (ground_action.effect ((the o px.res_inst) \<pi>)))
       \<subseteq> dom (snd M')"
    using ndom assms(4) rx_same_rhs by simp

  \<comment> \<open>Goal 4: the precondition is satisfied in \<open>M'\<close> via \<open>relax_cw_entailment\<close>.\<close>
  have pre_conj': "is_conj (map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a))"
    unfolding o_def using pre_conj map_preserves_isconj by simp
  have sat': "valuation M \<Turnstile>\<^sub>m
                map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a)"
    using sat inst by simp
  have "valuation M' \<Turnstile>\<^sub>m
          relax_conj (map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a))"
    using relax_cw_entailment[OF assms(1-3) sat' pre_conj'] .
  hence sat_rx:
    "valuation M' \<Turnstile>\<^sub>m ground_action.precondition ((the o px.res_inst) \<pi>)"
    using relax_conj_map[OF pre_conj] unfolding rx_inst ground_action.sel by metis

  show ?thesis
    unfolding px.plan_action_enabled_def Let_def
    using wf_rx nint_rx ndom_rx sat_rx by simp
qed

lemma (in -) map_effect_alt:
  "map_ast_effect f e =
     Effect
       (map (map_atom_fmla f) (adds e))
       (map (map_atom_fmla f) (dels e))
       (map (map_numeric_effect f) (numeric_effects e))"
  by (cases e) simp_all


(* technically, it only has to be resolvable for this lemma to hold,
  but using "enabled" is more concise and that's how it's used. *)
lemma (in normalized_problem_rx) rx_exec:
  assumes "fst M \<subseteq> fst M'" "plan_action_enabled \<pi> M"
  shows "fst (execute_plan_action \<pi> M) \<subseteq> fst (px.execute_plan_action \<pi> M')"
  using assms
proof (cases \<pi>)
  case (SimplePlanAction n args)
  then obtain a where a: "resolve_classical_action_schema n = Some a"
    using assms plan_action_enabled_def by fastforce
  hence a': "px.resolve_classical_action_schema n = Some (relax_ac a)"
    using rx_resolve by simp
  show ?thesis
    unfolding SimplePlanAction
    unfolding ast_classical_problem.execute_plan_action_def
    unfolding simple_action_instantiations.res_inst.simps a a' apply simp
    unfolding instantiate_action_schema_alt apply simp
    unfolding apply_effect_alt map_effect_alt
    unfolding ast_effect.sel relax_eff_sel
    using assms by auto
qed

lemma (in normalized_problem_rx) rx_path_right:
  assumes "fst M1 \<subseteq> fst M1'" "valid_classical_plan_alt M1 \<pi>s M2"
    "wf_world_model M1" "px.wf_world_model M1'"
  shows "\<exists>M2'. px.valid_classical_plan_alt M1' \<pi>s M2' \<and> fst M2 \<subseteq> fst M2'"
  using assms proof (induction \<pi>s arbitrary: M1 M1')
  case (Cons \<pi> \<pi>s)
  hence 1: "plan_action_enabled \<pi> M1" "valid_classical_plan_alt (execute_plan_action \<pi> M1) \<pi>s M2"
    by simp_all

  from Cons.prems have C1: "execute_plan_action \<pi> M1 \<subseteq> px.execute_plan_action \<pi> M1'"
    using rx_exec by simp
  from Cons.prems have C2: "px.plan_action_enabled \<pi> M1'"
    using rx_enabled ast_classical_problem.wf_lwm_basic by fastforce

  have "wf_world_model (execute_plan_action \<pi> M1)"
    "px.wf_world_model (px.execute_plan_action \<pi> M1')"
    using Cons.prems wf_execute 1 apply simp
    using Cons.prems px.wf_execute C2 by simp

  with C1 obtain M2' where "px.valid_classical_plan_alt (px.execute_plan_action \<pi> M1') \<pi>s M2'" "M2 \<subseteq> M2'"
    using 1 Cons by blast
  with C2 show ?case by auto
qed simp

(* TODO: re-enable when achievable/applicable are reintroduced in
   Normalization_Definitions. The proofs below are kept as outlines.

theorem (in normalized_problem_rx) relax_achievables:
  "{a. achievable a} \<subseteq> {a. px.achievable a}"
proof
  fix a assume "a \<in> {a. achievable a}"
  then obtain \<pi>s M where o: "valid_classical_plan_alt I \<pi>s M" "a \<in> M"
    using achievable_def by blast
  have "I \<subseteq> px.I" using rx_I by simp
  with o(1) obtain M' where "px.valid_classical_plan_alt px.I \<pi>s M'" "M \<subseteq> M'"
    using wf_I px.wf_I rx_path_right by blast
  thus "a \<in> {a. px.achievable a}"
    using px.achievable_def o(2) by blast
qed

theorem (in normalized_problem_rx) relax_applicables:
  "{\<pi>. applicable \<pi>} \<subseteq> {\<pi>. px.applicable \<pi>}"
proof
  fix x
  assume "x \<in> {\<pi>. applicable \<pi>}"
  then obtain \<pi>s M where o: "valid_classical_plan_alt I \<pi>s M" "x \<in> set \<pi>s"
    using applicable_def by blast
  have "I \<subseteq> px.I" using rx_I by simp
  with o(1) obtain M' where "px.valid_classical_plan_alt px.I \<pi>s M'"
    using wf_I px.wf_I rx_path_right by blast
  thus "x \<in> {\<pi>. px.applicable \<pi>}"
    using px.applicable_def o(2) by blast
qed
*)


subsection \<open> Code Setup \<close>

lemmas relax_code =
  ast_classical_domain.relax_dom_def
  ast_classical_problem.relax_prob_def

declare relax_code [code]


end
