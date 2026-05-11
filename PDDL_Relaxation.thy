theory PDDL_Relaxation
imports "Classical_Planning.Classical_Abstract_Syntax"
    Grounding_Utils PDDL_Sema_Supplement Formula_Utils Normalization_Definitions
begin

subsection \<open> Relaxation Procedure \<close>

fun relax_eff :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "relax_eff (Effect a b) = Effect a []"

fun relax_ac :: "ast_action_schema \<Rightarrow> ast_action_schema" where
  "relax_ac (Action_Schema n params pre eff) =
    Action_Schema n params (relax_conj pre) (relax_eff eff)"

definition (in ast_domain) "relax_dom \<equiv>
  Domain
    (types D)
    (predicates D)
    (consts D)
    (map relax_ac (actions D))"

definition (in ast_problem) "relax_prob \<equiv>
  Problem
    relax_dom
    (objects P)
    (init P)
    (relax_conj (goal P))"

subsection \<open> Contexts \<close>

text \<open> locale setup for simplified syntax \<close>

(* TODO replace with D\<^sup>+ and P\<^sup>+ *)
abbreviation (in ast_domain) (input) "DX \<equiv> relax_dom"
abbreviation (in ast_problem) (input) "PX \<equiv> relax_prob"

locale ast_domain_rx = ast_domain
sublocale ast_domain_rx \<subseteq> dx: ast_domain DX .

locale normalized_domain_rx = normalized_domain
sublocale normalized_domain_rx \<subseteq> dx: ast_domain DX .
(* this is later strengthened to "dx: normed_dom DX" *)
sublocale normalized_domain_rx \<subseteq> ast_domain_rx .

locale ast_problem_rx = ast_problem
sublocale ast_problem_rx \<subseteq> px: ast_problem PX .
sublocale ast_problem_rx \<subseteq> ast_domain_rx D .

locale normalized_problem_rx = normalized_problem
sublocale normalized_problem_rx \<subseteq> px : ast_problem PX.
(* this is later strengthened to "px: normed_prob PX" *)
sublocale normalized_problem_rx \<subseteq> ast_problem_rx .
sublocale normalized_problem_rx \<subseteq> normalized_domain_rx D
  by unfold_locales

subsection \<open> Alt definitions \<close>

lemma (in ast_domain) relax_ac_sel[simp]:
  "ac_name (relax_ac ac) = ac_name ac"
  "ac_params (relax_ac ac) = ac_params ac"
  "ac_pre (relax_ac ac) = relax_conj (ac_pre ac)"
  "ac_eff (relax_ac ac) = relax_eff (ac_eff ac)"
  apply (cases ac; simp)
  apply (cases ac; simp)
  apply (cases ac; simp)
  apply (cases ac; simp)
  done

lemma (in ast_domain) relax_eff_sel[simp]:
  "adds (relax_eff e) = adds e"
  "dels (relax_eff e) = []"
   apply (cases e; simp)
  apply (cases e; simp)
  done

lemma (in ast_domain) relax_dom_sel[simp]:
  "types DX = types D"
  "predicates DX = predicates D"
  "consts DX = consts D"
  "actions DX = map relax_ac (actions D)"
  using relax_dom_def by simp_all

lemma (in ast_problem) relax_prob_sel[simp]:
  "domain PX = relax_dom"
  "objects PX = objects P"
  "init PX = init P"
  "goal PX = relax_conj (goal P)"
  using relax_prob_def by simp_all

subsection \<open> Preserving normalization \<close>

lemmas norm_dom_defs =
  ast_domain.normalized_dom_def
  ast_domain.typeless_dom_def
  ast_domain.prec_normed_dom_def
lemmas norm_prob_defs =
  ast_problem.normalized_prob_def
  ast_problem.typeless_prob_def

lemma (in normalized_domain_rx) rx_acs_typeless:
  "\<forall>ac \<in> set (map relax_ac (actions D)). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>"
  using normalized_dom unfolding norm_dom_defs by simp

lemma (in normalized_domain_rx) rx_acs_pos_conjs:
  "\<forall>ac\<in>set (map relax_ac (actions D)). is_pos_conj (ac_pre ac)"
  using normalized_dom unfolding norm_dom_defs
  using relax_conj_pos relax_ac_sel(3) relax_dom_sel(4)
  by fastforce

lemma (in normalized_domain_rx) rx_acs_conjs:
  "\<forall>ac\<in>set (map relax_ac (actions D)). is_conj (ac_pre ac)"
  using rx_acs_pos_conjs pos_conj_conj by blast

theorem (in normalized_domain_rx) relax_dom_normed:
  "dx.normalized_dom"
  using normalized_dom
  unfolding norm_dom_defs relax_dom_sel
  using rx_acs_typeless rx_acs_conjs by simp

theorem (in normalized_problem_rx) relax_normed:
  "px.normalized_prob"
  using normalized_prob relax_dom_normed
  unfolding ast_domain.normalized_dom_def norm_prob_defs
  unfolding relax_prob_sel
  using relax_conj_pos pos_conj_conj by blast

theorem (in normalized_problem_rx) relax_relaxes:
  "px.relaxed_prob"
  using relax_normed normalized_prob
  unfolding px.relaxed_prob_def norm_prob_defs
  unfolding relax_prob_sel
  using relax_conj_pos rx_acs_pos_conjs by auto

subsection \<open> Preserving Well-Formedness \<close>

lemma (in ast_domain_rx) rx_constT: "dx.constT = constT"
  unfolding ast_domain.constT_def by simp

lemma (in ast_domain_rx) rx_wf_atom: "dx.wf_atom = wf_atom"
  apply (rule ext; rule ext)
  subgoal for tyt x
    apply (cases x; simp)
    unfolding ast_domain.sig_def ast_domain.is_of_type_def ast_domain.of_type_def
      ast_domain.subtype_rel_def relax_dom_sel by blast
  done

lemma (in ast_domain_rx) rx_wf_fmla: "dx.wf_fmla = wf_fmla"
  apply (rule ext; rule ext)
  subgoal for tyt x
    apply (induction x; simp add: rx_wf_atom)
    done
  done

lemma (in ast_domain_rx) rx_wf_fmla_atom: "dx.wf_fmla_atom = wf_fmla_atom"
  unfolding ast_domain.wf_fmla_atom_alt rx_wf_fmla ..

lemma (in ast_domain_rx) rx_wf_eff: "dx.wf_effect = wf_effect"
  apply (rule ext; rule ext)
  subgoal for tyt eff
    apply (cases eff; simp)
    unfolding rx_wf_fmla_atom ..
  done

lemma (in ast_domain) relax_fmla_wf:
  "wf_fmla tyt F \<Longrightarrow> wf_fmla tyt (relax_conj F)"
  apply (induction F)
  subgoal for x by (cases x) simp_all
      apply simp_all
  subgoal for F by (cases F rule: is_pos_lit.cases) simp_all
  subgoal for F G by (cases F rule: is_pos_lit.cases) simp_all
  done

lemma (in ast_domain) relax_eff_wf:
  "wf_effect tyt eff \<Longrightarrow> wf_effect tyt (relax_eff eff)"
  by (cases eff) simp

lemma (in ast_problem_rx) rx_I: "px.I = I"
  unfolding ast_problem.I_def relax_prob_sel ..

lemma (in ast_problem_rx) rx_objT: "px.objT = objT"
  unfolding ast_problem.objT_def rx_constT relax_prob_sel ..

lemma (in ast_problem_rx) rx_is_obj_of_type: "px.is_obj_of_type = is_obj_of_type"
  unfolding ast_problem.is_obj_of_type_def rx_objT ast_domain.of_type_def
    ast_domain.subtype_rel_def relax_prob_sel relax_dom_sel .. 

lemma (in ast_problem_rx) rx_wf_wm: "px.wf_world_model = wf_world_model"
  unfolding ast_problem.wf_world_model_def relax_prob_sel rx_wf_fmla_atom rx_objT ..

lemma (in ast_domain) relax_ac_names:
  "map ac_name (actions D) = map ac_name (map relax_ac (actions D))"
  using relax_ac_sel(1) by simp

lemma (in ast_domain_rx) relax_ac_wf:
  assumes "wf_action_schema a" "is_conj (ac_pre a)"
  shows "dx.wf_action_schema (relax_ac a)"
  using assms apply (cases a; simp) unfolding Let_def
  apply (intro conjI)
    apply blast
  using rx_wf_fmla rx_constT relax_fmla_wf apply metis
  using rx_wf_eff rx_constT relax_eff_wf by metis

theorem (in normalized_domain_rx) relax_dom_wf:
  "dx.wf_domain"
  using wf_domain
  unfolding ast_domain.wf_domain_def
  unfolding ast_domain.wf_types_def
  unfolding ast_domain.wf_predicate_decl_alt ast_domain.wf_type_alt
  unfolding relax_dom_sel
  using relax_ac_names relax_ac_wf
  using normalized_dom unfolding norm_dom_defs by auto

lemma (in normalized_problem_rx) rx_goal_wf:
  "dx.wf_fmla px.objT (relax_conj (goal P))"
  using wf_P(5) rx_objT rx_wf_fmla
    normalized_prob[unfolded norm_prob_defs] ast_domain.relax_fmla_wf
  by metis

theorem (in normalized_problem_rx) relax_wf:
  "px.wf_problem"
  using wf_problem
  unfolding ast_problem.wf_problem_def
  unfolding relax_prob_sel relax_dom_sel
  apply (intro conjI)
  using relax_dom_wf apply blast apply blast
  unfolding ast_domain.wf_type_alt apply simp apply blast
  unfolding ast_problem.wf_world_model_def
  using rx_objT rx_wf_fmla_atom relax_prob_sel(1) apply metis
  using rx_goal_wf by simp
 
sublocale normalized_domain_rx \<subseteq> dx: normalized_domain DX
  apply (unfold_locales)
  using relax_dom_normed relax_dom_wf by simp_all

sublocale normalized_problem_rx \<subseteq> px: normalized_problem PX
  apply (unfold_locales)
  using relax_normed relax_wf by simp_all

subsection \<open> Semantics \<close>

lemma (in normalized_domain_rx) rx_resolve:
  assumes "resolve_action_schema n = Some a"
  shows "dx.resolve_action_schema n = Some (relax_ac a)"
  using assms res_aux dx.res_aux by simp

lemma (in normalized_domain_rx) rx_resolve':
  assumes "dx.resolve_action_schema n = Some a'"
  obtains a where "resolve_action_schema n = Some a"
  using that assms res_aux dx.res_aux by auto

lemma (in wf_ast_problem) plan_action_path_single:
  assumes "plan_action_path N [p] M"
  shows "plan_action_enabled p N" "execute_plan_action p N = M"
  using assms plan_action_path_def execute_plan_action_def ground_action_path.simps
    plan_action_enabled_def apply simp
  using assms by (metis plan_action_path_Cons plan_action_path_Nil)

lemma (in - ) relax_cw_entailment:
  assumes "wm_basic M" "wm_basic M'" "M \<subseteq> M'" "M \<^sup>c\<TTurnstile>\<^sub>= \<phi>" "is_conj \<phi>"
  shows "M' \<^sup>c\<TTurnstile>\<^sub>= relax_conj \<phi>"
proof -
  have "valuation M' \<Turnstile> relax_conj \<phi>" if "valuation M \<Turnstile> \<phi>"
    using assms(5,4) that apply (induction \<phi> rule: conj_induct_atoms)
    using assms(1-3) valuation_def valuation_iff_close_world by auto
  with assms show ?thesis by (simp add: valuation_iff_close_world)
qed

find_theorems "(?f\<circ> ?g) ?x = ?f ( ?g ( ?x))"
  


lemma (in normalized_problem_rx) rx_enabled:
  assumes "wm_basic M" "wm_basic M'" "M \<subseteq> M'" "plan_action_enabled \<pi> M"
  shows "px.plan_action_enabled \<pi> M'"
proof (cases \<pi>)
  case (PAction n args)
  then obtain a where a: "resolve_action_schema n = Some a"
    using assms plan_action_enabled_def by fastforce
  hence a': "px.resolve_action_schema n = Some (relax_ac a)"
    using rx_resolve by simp

  have pre_conj: "is_conj (ac_pre a)"
    using a normalized_dom[unfolded norm_dom_defs] res_aux by fast

  from assms(4) have wf: "wf_plan_action \<pi>" and
    sat: "M \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate \<pi>)"
    using plan_action_enabled_def by simp_all

  show ?thesis
    unfolding px.plan_action_enabled_def
    apply (rule conjI)
    (* proving \<open>px.wf_plan_action \<pi>\<close> *)
    using wf unfolding PAction
    unfolding wf_plan_action_simple px.wf_plan_action_simple
    unfolding a a' apply simp
    unfolding ast_problem.action_params_match_def relax_ac_sel rx_is_obj_of_type apply simp
    (* proving \<open>M' \<^sup>c\<TTurnstile>\<^sub>= precondition (px.resolve_instantiate \<pi>)\<close> *)
    using sat unfolding PAction
    unfolding ast_problem.resolve_instantiate.simps a a' apply simp
    unfolding instantiate_action_schema_alt apply simp
    unfolding o_apply[symmetric, of map_formula]
    unfolding relax_conj_map[OF pre_conj]
    using assms relax_cw_entailment
      by (simp add: map_preserves_isconj pre_conj)
qed                          

lemma (in -) map_effect_alt: "map_ast_effect f e = Effect (map (map_atom_fmla f) (adds e)) (map (map_atom_fmla f) (dels e))"
  by (cases e) simp_all


(* technically, it only has to be resolvable for this lemma to hold,
  but using "enabled" is more concise and that's how it's used. *)
lemma (in normalized_problem_rx) rx_exec:
  assumes "M \<subseteq> M'" "plan_action_enabled \<pi> M"
  shows "execute_plan_action \<pi> M \<subseteq> px.execute_plan_action \<pi> M'"
  using assms
proof (cases \<pi>)
  case (PAction n args)
  then obtain a where a: "resolve_action_schema n = Some a"
    using assms plan_action_enabled_def by fastforce
  hence a': "px.resolve_action_schema n = Some (relax_ac a)"
    using rx_resolve by simp
  show ?thesis
    unfolding PAction
    unfolding ast_problem.execute_plan_action_def
    unfolding ast_problem.resolve_instantiate.simps a a' apply simp
    unfolding instantiate_action_schema_alt apply simp
    unfolding apply_effect_alt map_effect_alt
    unfolding ast_effect.sel relax_eff_sel
    using assms by auto
qed

lemma (in normalized_problem_rx) rx_path_right:
  assumes "M1 \<subseteq> M1'" "plan_action_path M1 \<pi>s M2" "wf_world_model M1" "px.wf_world_model M1'"
  shows "\<exists>M2'. px.plan_action_path M1' \<pi>s M2' \<and> M2 \<subseteq> M2'"
  using assms proof (induction \<pi>s arbitrary: M1 M1')
  case (Cons \<pi> \<pi>s)
  hence 1: "plan_action_enabled \<pi> M1" "plan_action_path (execute_plan_action \<pi> M1) \<pi>s M2"
    by simp_all

  from Cons.prems have C1: "execute_plan_action \<pi> M1 \<subseteq> px.execute_plan_action \<pi> M1'"
    using rx_exec by simp
  from Cons.prems have C2: "px.plan_action_enabled \<pi> M1'"
    using rx_enabled ast_problem.wf_wm_basic by fastforce

  have "wf_world_model (execute_plan_action \<pi> M1)"
    "px.wf_world_model (px.execute_plan_action \<pi> M1')"
    using Cons.prems wf_execute 1 apply simp
    using Cons.prems px.wf_execute C2 by simp

  with C1 obtain M2' where "px.plan_action_path (px.execute_plan_action \<pi> M1') \<pi>s M2'" "M2 \<subseteq> M2'"
    using 1 Cons by blast
  with C2 show ?case by auto
qed simp

theorem (in normalized_problem_rx) relax_achievables:
  "{a. achievable a} \<subseteq> {a. px.achievable a}"
proof
  fix a assume "a \<in> {a. achievable a}"
  then obtain \<pi>s M where o: "plan_action_path I \<pi>s M" "a \<in> M"
    using achievable_def by blast
  have "I \<subseteq> px.I" using rx_I by simp
  with o(1) obtain M' where "px.plan_action_path px.I \<pi>s M'" "M \<subseteq> M'"
    using wf_I px.wf_I rx_path_right by blast
  thus "a \<in> {a. px.achievable a}"
    using px.achievable_def o(2) by blast
qed

theorem (in normalized_problem_rx) relax_applicables:
  "{\<pi>. applicable \<pi>} \<subseteq> {\<pi>. px.applicable \<pi>}"
proof
  fix x
  assume "x \<in> {\<pi>. applicable \<pi>}"
  then obtain \<pi>s M where o: "plan_action_path I \<pi>s M" "x \<in> set \<pi>s"
    using applicable_def by blast
  have "I \<subseteq> px.I" using rx_I by simp
  with o(1) obtain M' where "px.plan_action_path px.I \<pi>s M'"
    using wf_I px.wf_I rx_path_right by blast
  thus "x \<in> {\<pi>. px.applicable \<pi>}"
    using px.applicable_def o(2) by blast
qed


subsection \<open> Code Setup \<close>

lemmas relax_code =
  ast_domain.relax_dom_def
  ast_problem.relax_prob_def

declare relax_code [code]


end