theory Classical_PDDL_Relaxation_Semantics
  imports Classical_PDDL_Relaxation
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
                    relax_ac_head)
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

text \<open>Relaxation makes the relaxed action numeric-free (numeric preconditions become \<open>\<^bold>\<not>\<bottom>\<close> via
  \<^const>\<open>relax_lit\<close>, numeric effects are dropped by \<^const>\<open>relax_eff\<close>), so enabledness of the relaxed
  action needs only the \<^emph>\<open>propositional\<close> monotonicity \<open>fst M \<subseteq> fst M'\<close> --- the numeric valuation
  \<open>snd\<close> is irrelevant to the relaxed problem.\<close>
lemma (in normalized_problem_rx) rx_enabled:
  assumes "lwm_basic (fst M)" "lwm_basic (fst M')" "fst M \<subseteq> fst M'"
    "plan_action_enabled \<pi> M"
  shows "px.plan_action_enabled \<pi> M'"
proof (cases \<pi>)
  case (SimplePlanAction n args)
  have wf_pi: "wf_classical_plan_action \<pi>"
    using assms(4) plan_action_enabled_props(1) by blast
  then obtain a where a: "resolve_classical_action_schema n = Some a"
    unfolding SimplePlanAction
    using ast_classical_problem.wf_classical_plan_action_simple
    by (cases "resolve_classical_action_schema n") auto
  hence a': "px.resolve_classical_action_schema n = Some (relax_ac a)"
    using rx_resolve by simp

  have pre_conj: "is_conj (ac_pre a)"
    using a normalized_dom[unfolded norm_dom_defs] res_aux by fast

  \<comment> \<open>Split the assumption into the four constituents of \<open>plan_action_enabled\<close>.\<close>
  from assms(4) have
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

  \<comment> \<open>Goals 2 & 3: the relaxed action has NO numeric effects, so non-interference and the
      rhs-primitive-numeric-expressions-in-domain condition hold trivially (the valuation \<open>snd\<close>
      plays no role in the relaxed problem).\<close>
  have rx_ne_empty:
    "numeric_effects (ground_action.effect ((the o px.res_inst) \<pi>)) = []"
    unfolding rx_inst by (cases "ac_eff a") simp

  have nint_rx: "numeric_effects_non_intrf ((the o px.res_inst) \<pi>)"
    using numeric_effects_non_intrf_no_numeric_effects[OF rx_ne_empty] .

  have rx_rhs_empty:
    "ast_effect_enumerate_rhs_primitive_numeric_expressions
         (ground_action.effect ((the o px.res_inst) \<pi>)) = []"
    unfolding rx_inst by (cases "ac_eff a") simp

  have ndom_rx:
    "set (ast_effect_enumerate_rhs_primitive_numeric_expressions
            (ground_action.effect ((the o px.res_inst) \<pi>)))
       \<subseteq> dom (snd M')"
    unfolding rx_rhs_empty by simp

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
proof (cases \<pi>)
  case (SimplePlanAction n args)
  from assms(2) obtain a where a: "resolve_classical_action_schema n = Some a"
    unfolding SimplePlanAction plan_action_enabled_def
    using ast_classical_problem.wf_classical_plan_action_simple
    by (cases "resolve_classical_action_schema n") auto
  hence a': "px.resolve_classical_action_schema n = Some (relax_ac a)"
    using rx_resolve by simp
  have inst:
    "(the o res_inst) \<pi> = GroundAction
        (map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a))
        (map_ast_effect (ac_tsubst (ac_params a) args) (ac_eff a))"
    unfolding SimplePlanAction using a
    by (simp add: domain_signature.instantiate_classical_action_schema_alt
                  simple_action_instantiations.res_inst.simps)
  have rx_inst:
    "(the o px.res_inst) \<pi> = GroundAction
        (map_atom_fmla (ac_tsubst (ac_params a) args) (relax_conj (ac_pre a)))
        (map_ast_effect (ac_tsubst (ac_params a) args) (relax_eff (ac_eff a)))"
    unfolding SimplePlanAction using a' relax_ac_sel
    by (simp add: domain_signature.instantiate_classical_action_schema_alt
                  simple_action_instantiations.res_inst.simps)
  have dels_rx: "set (dels (ground_action.effect ((the o px.res_inst) \<pi>))) = {}"
    unfolding rx_inst ground_action.sel map_effect_alt by (simp add: relax_eff_sel(2))
  have adds_rx: "adds (ground_action.effect ((the o px.res_inst) \<pi>))
        = adds (ground_action.effect ((the o res_inst) \<pi>))"
    unfolding inst rx_inst ground_action.sel map_effect_alt by (simp add: relax_eff_sel(1))
  have L: "fst (execute_plan_action \<pi> M)
    = (fst M - set (dels (ground_action.effect ((the o res_inst) \<pi>))))
        \<union> set (adds (ground_action.effect ((the o res_inst) \<pi>)))"
    unfolding execute_plan_action_def
    by (metis apply_ground_action_alt fst_conv prod.collapse)
  have R: "fst (px.execute_plan_action \<pi> M')
    = (fst M' - set (dels (ground_action.effect ((the o px.res_inst) \<pi>))))
        \<union> set (adds (ground_action.effect ((the o px.res_inst) \<pi>)))"
    unfolding px.execute_plan_action_def
    by (metis apply_ground_action_alt fst_conv prod.collapse)
  show ?thesis
    unfolding L R dels_rx adds_rx using assms(1) by auto
qed

text \<open>Relaxation drops numeric effects (\<^const>\<open>relax_eff\<close>), so it no longer preserves the numeric
  valuation \<open>snd\<close> --- the old \<open>rx_exec_snd\<close> (\<open>snd\<close> preserved) is gone. Reachability only needs the
  \<^emph>\<open>propositional\<close> monotonicity, so \<open>rx_path_right\<close> tracks only \<open>fst M \<subseteq> fst M'\<close>.\<close>

lemma (in normalized_problem_rx) rx_path_right:
  assumes "fst M1 \<subseteq> fst M1'" "valid_classical_plan_alt M1 \<pi>s M2"
    "wf_world_model M1" "px.wf_world_model M1'"
  shows "\<exists>M2'. px.valid_classical_plan_alt M1' \<pi>s M2' \<and> fst M2 \<subseteq> fst M2'"
  using assms
proof (induction \<pi>s arbitrary: M1 M1')
  case (Nil M1 M1')
  then have "M1 = M2" by simp
  then show ?case using Nil.prems(1) by (intro exI[of _ M1']) auto
next
  case (Cons \<pi> \<pi>s M1 M1')
  from Cons.prems(2) have 1: "plan_action_enabled \<pi> M1"
    and 2: "valid_classical_plan_alt (execute_plan_action \<pi> M1) \<pi>s M2" by simp_all
  have lb1: "lwm_basic (fst M1)" using Cons.prems(3) wf_lwm_basic by blast
  have lb1': "lwm_basic (fst M1')" using Cons.prems(4) px.wf_lwm_basic by blast
  have C1: "fst (execute_plan_action \<pi> M1) \<subseteq> fst (px.execute_plan_action \<pi> M1')"
    using rx_exec[OF Cons.prems(1) 1] .
  have C2: "px.plan_action_enabled \<pi> M1'"
    using rx_enabled[OF lb1 lb1' Cons.prems(1) 1] .
  have wfe: "wf_world_model (execute_plan_action \<pi> M1)"
    using wf_execute_stronger plan_action_enabled_props(1)[OF 1] Cons.prems(3) by blast
  have wfe': "px.wf_world_model (px.execute_plan_action \<pi> M1')"
    using px.wf_execute_stronger px.plan_action_enabled_props(1)[OF C2] Cons.prems(4) by auto
  from Cons.IH[OF C1 2 wfe wfe'] obtain M2' where
    M2': "px.valid_classical_plan_alt (px.execute_plan_action \<pi> M1') \<pi>s M2'"
         "fst M2 \<subseteq> fst M2'" by blast
  show ?case using C2 M2' by fastforce
qed

theorem (in normalized_problem_rx) relax_achievables:
  "{a. achievable a} \<subseteq> {a. px.achievable a}"
proof
  fix f assume "f \<in> {a. achievable a}"
  then obtain \<pi>s M where o: "valid_classical_plan_alt I \<pi>s M"
    "Atom (uncurry predAtm f) \<in> fst M"
    using achievable_def by blast
  have i1: "fst I \<subseteq> fst px.I" using rx_I by simp
  from rx_path_right[OF i1 o(1) wf_I] px.wf_I obtain M' where
    M': "px.valid_classical_plan_alt px.I \<pi>s M'" "fst M \<subseteq> fst M'" by auto
  thus "f \<in> {a. px.achievable a}"
    using px.achievable_def o(2) M'(2) by blast
qed

theorem (in normalized_problem_rx) relax_applicables:
  "{\<pi>. applicable \<pi>} \<subseteq> {\<pi>. px.applicable \<pi>}"
proof
  fix x assume "x \<in> {\<pi>. applicable \<pi>}"
  then obtain \<pi>s M where o: "valid_classical_plan_alt I \<pi>s M" "x \<in> set \<pi>s"
    using applicable_def by blast
  have i1: "fst I \<subseteq> fst px.I" using rx_I by simp
  from rx_path_right[OF i1 o(1) wf_I] px.wf_I obtain M' where
    "px.valid_classical_plan_alt px.I \<pi>s M'" by auto
  thus "x \<in> {\<pi>. px.applicable \<pi>}"
    using px.applicable_def o(2) by blast
qed


subsection \<open> Code Setup \<close>

lemmas relax_code =
  ast_classical_domain.relax_dom_def
  ast_classical_problem.relax_prob_def

declare relax_code [code]


end
