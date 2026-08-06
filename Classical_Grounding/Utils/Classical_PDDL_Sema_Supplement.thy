theory Classical_PDDL_Sema_Supplement
  imports Classical_Planning.Classical_Happening_Semantics
  Grounding_Utils.Grounding_Utils Grounding_Common.Formula_Utils Grounding_Common.PDDL_Normalization
  Grounding_Common.PDDL_Sema_Supplement
begin

subsection \<open>Formulas\<close>

(* BigOr_map_semantics, BigAnd_map_semantics moved to Grounding_Common.PDDL_Sema_Supplement *)

subsection \<open> sugar \<close>

(* not much here yet *)

(* wf_D_sig, wf_P_sig, wf_sig moved to Grounding_Common.PDDL_Sema_Supplement *)

(* wf_domain unfolded and split *)
lemmas (in wf_ast_classical_domain) wf_D =
  conj_split_3[OF wf_classical_domain[unfolded wf_classical_domain_def]]

(* wf_problem unfolded and split, but omitting the first fact "wf_domain" *)
lemmas (in wf_ast_classical_problem) wf_P =
  conj_split_5[OF wf_classical_problem[unfolded wf_classical_problem_def]]

lemmas (in wf_ast_classical_problem) wf_DP = wf_D wf_P wf_D_sig wf_P_sig

declare ast_classical_problem.I_def[simp]

subsection \<open> Accessor functions \<close>

(* get_t, get_t_alt moved to Grounding_Common.PDDL_Sema_Supplement *)

(* un_Atom, unPredAtom, is_predAtom_decomp moved to Grounding_Common.PDDL_Sema_Supplement *)

subsection \<open>Alternative definitions\<close>

text \<open>Alternative definitions. Most of these just remove pattern matching
  from functions, e.g. a function "add (x, y) = x + y" would be turned into
  "add p = fst p + snd p".
  They are often unnecessary because you can just apply "cases" in a proof.
  Others functions are only well-defined if a certain condition holds. The _cond-lemmas
  help resolve it directly. \<close>

(* map_atom_fmla moved to Grounding_Common.PDDL_Sema_Supplement *)

abbreviation "ac_head \<equiv> ast_classical_action_schema.head"
abbreviation "ac_name a \<equiv> ast_action_head.name (ac_head a)"
abbreviation "ac_params a \<equiv> ast_action_head.parameters (ac_head a)"

fun ac_body :: "ast_classical_action_schema \<Rightarrow> ast_simple_action_body" where
  "ac_body (SimpleActionSchema _ b) = b"
abbreviation "ac_pre a \<equiv> ast_simple_action_body.precondition (ac_body a)"
abbreviation "ac_eff a \<equiv> ast_simple_action_body.effect (ac_body a)"

(* apply_ground_action_alt, apply_ground_actions_equiv_weak, numeric_effects_non_intrf_equiv_weak,
   numeric_effects_non_intrf_no_numeric_effects, enumerate_rhs_pnes_no_numeric_effects
   moved to Grounding_Common.PDDL_Sema_Supplement *)

(* These two are useful to adapt to new semantics *)
context ast_classical_problem
begin
lemma classical_plan_happ_path_alt: 
  "classical_plan_happ_path M \<pi> M' \<longleftrightarrow>
  valid_classical_plan M (map (the o res_inst) \<pi>) M'"
  using classical_plan_happ_path_def ind_classical_plan_def by simp


definition "plan_action_enabled a M \<equiv>
wf_classical_plan_action a 
  \<and> (let 
     a' = (the o res_inst) a
  in numeric_effects_non_intrf a' 
   \<and> set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect a')) \<subseteq> dom (snd M)
   \<and> valuation M \<Turnstile>\<^sub>m precondition a'
   \<and> numeric_effects_defined [a'] (snd M))"

definition "execute_plan_action a M \<equiv>
  apply_ground_actions [(the o res_inst) a] M"

fun valid_classical_plan_alt where
"valid_classical_plan_alt M [] M' = (M = M')" |
"valid_classical_plan_alt M (a#as) M' = (
  plan_action_enabled a M
\<and> valid_classical_plan_alt (execute_plan_action a M) as M'
)"

lemmas plan_action_enabled_props = conj_split_5[OF plan_action_enabled_def[THEN meta_eq_to_obj_eq, THEN iffD1, simplified Let_def]]
lemmas plan_action_enabled_elims = plan_action_enabled_props[elim_format]


lemma valid_classical_plan_alt_correct:
  "valid_classical_plan_alt M \<pi> M' = (wf_classical_plan \<pi> \<and> classical_plan_happ_path M \<pi> M')"
proof (induction \<pi> arbitrary: M)
  case Nil
  then show ?case by (simp add: Let_def plan_action_enabled_def execute_plan_action_def 
        classical_plan_happ_path_def wf_classical_plan_def ind_classical_plan_def)
next
  case (Cons a as)
  have "valid_classical_plan_alt M (a # as) M' = 
    (let a' = (the o res_inst) a 
    in wf_classical_plan (a#as) 
    \<and> classical_plan_happ_path (apply_ground_actions [a'] M) as M'
    \<and> set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect a')) \<subseteq> dom (snd M)
    \<and> numeric_effects_non_intrf a' 
    \<and> valuation M \<Turnstile>\<^sub>m ground_action.precondition a'
    \<and> numeric_effects_defined [a'] (snd M))" 
    by (auto simp: Let_def Cons.IH
        wf_classical_plan_def execute_plan_action_def plan_action_enabled_def)
  also have "... = (wf_classical_plan (a#as) \<and> 
    (let a' = (the o res_inst) a 
    in classical_plan_happ_path (apply_ground_actions [a'] M) as M'
    \<and> set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect a')) \<subseteq> dom (snd M)
    \<and> numeric_effects_non_intrf a' 
    \<and> valuation M \<Turnstile>\<^sub>m ground_action.precondition a'
    \<and> numeric_effects_defined [a'] (snd M)))" by (simp add: Let_def)
  also have "... = (wf_classical_plan (a#as) \<and> classical_plan_happ_path M (a#as) M')"
    unfolding classical_plan_happ_path_alt 
    by (auto simp: Let_def classical_plan_happ_path_alt)
  finally show ?case by simp
  (* show ?case by (auto simp: Let_def Cons.IH
          wf_classical_plan_def execute_plan_action_def plan_action_enabled_def
          classical_plan_happ_path_alt) *)
qed

lemma valid_classical_plan_from2_alt:
  "valid_classical_plan_from2 M \<pi> \<longleftrightarrow>
    (\<exists>M'. valid_classical_plan_alt M \<pi> M' \<and> valuation M' \<Turnstile>\<^sub>m goal P)"
  unfolding valid_classical_plan_from2_def
  using valid_classical_plan_alt_correct
  by presburger

lemma valid_classical_plan_from2_Nil[simp]:
  "valid_classical_plan_from2 M [] \<longleftrightarrow> valuation M \<Turnstile>\<^sub>m goal P"
  by (simp add: valid_classical_plan_from2_alt)

lemma valid_classical_plan_from2_Cons[simp]:
  "valid_classical_plan_from2 M (a # as) \<longleftrightarrow>
    plan_action_enabled a M \<and> valid_classical_plan_from2 (execute_plan_action a M) as"
  by (auto simp: valid_classical_plan_from2_alt)

lemma valid_classical_plan2_alt:
  "valid_classical_plan2 \<pi> \<longleftrightarrow>
    (\<exists>M'. valid_classical_plan_alt I \<pi> M' \<and> valuation M' \<Turnstile>\<^sub>m goal P)"
  unfolding valid_classical_plan2_def
  by (rule valid_classical_plan_from2_alt)



text \<open> Semantics \<close>

lemma (in ast_classical_problem) valid_classical_plan_alt_append_intro:
  assumes "valid_classical_plan_alt M1 \<pi>s M2 \<and> valid_classical_plan_alt M2 \<mu>s M3"
  shows "valid_classical_plan_alt M1 (\<pi>s @ \<mu>s) M3"
  using assms apply (induction \<pi>s arbitrary: M1) by simp_all

lemma (in ast_classical_problem) valid_classical_plan_alt_append_elim:
  assumes "valid_classical_plan_alt M1 (\<pi>s @ \<mu>s) M3"
  shows "\<exists>M2. valid_classical_plan_alt M1 \<pi>s M2 \<and> valid_classical_plan_alt M2 \<mu>s M3"
using assms by (induction \<pi>s arbitrary: M1) auto

lemma (in wf_ast_classical_problem) valid_plan_from_Cons[simp]:
  "valid_classical_plan_from2 M (\<pi> # \<pi>s)
    \<longleftrightarrow> valid_classical_plan_from2 (execute_plan_action \<pi> M) \<pi>s \<and> plan_action_enabled \<pi> M"
  using valid_classical_plan_from2_alt by auto 

lemma (in wf_ast_classical_problem) valid_plan_from_snoc:
  "valid_classical_plan_from2 M (\<pi>s @ [\<pi>])
    \<longleftrightarrow> (\<exists>M'. valid_classical_plan_alt M \<pi>s M' \<and> plan_action_enabled \<pi> M' \<and>
    valuation (execute_plan_action \<pi> M') \<Turnstile>\<^sub>m goal P)"
  using valid_classical_plan_from2_alt apply (induction \<pi>s arbitrary: M)
  apply force
  by auto

end

context domain_signature 
begin
(* wf_fmla_alt, wf_fmla_mono_atoms, subtype_edge_swap, subtype_rel_alt,
   subtype_rel_star_alt, wf_atom_deep moved to Grounding_Common.PDDL_Sema_Supplement *)


(* wf_effect_alt moved to Grounding_Common.PDDL_Sema_Supplement *)

definition "ac_tyt a \<equiv> ty_term (map_of (ac_params a)) constT"

(* wf_action_head_alt, wf_simple_action_body_alt moved to
   Grounding_Common.PDDL_Sema_Supplement *)

lemma (in domain_signature) wf_classical_action_schema_alt: "wf_classical_action_schema ac \<longleftrightarrow>
    distinct (map fst (ac_params ac))
  \<and> wf_fmla (ac_tyt ac) (ac_pre ac)
  \<and> wf_effect (ac_tyt ac) (ac_eff ac)"
  by (cases ac, simp add: Let_def wf_action_head_alt wf_simple_action_body_alt ac_tyt_def)
  

(* wf_type_alt moved to Grounding_Common.PDDL_Sema_Supplement *)

(* wf_predicate_decl_alt, wf_function_decl_alt moved to
   Grounding_Common.PDDL_Sema_Supplement *)

end

context wf_ast_classical_domain
begin

lemma resolve_classical_action_schema_cond:
  assumes "SimpleActionSchema h b \<in> set (actions D)"
  shows "resolve_classical_action_schema (ast_action_head.name h) = Some (SimpleActionSchema h b)"
  using assms wf_D_sig wf_D
  unfolding resolve_classical_action_schema_def by simp

definition (in -) ac_tsubst :: "(variable \<times> type) list \<Rightarrow> object list \<Rightarrow> (term \<Rightarrow> object)" where
  [simp]: "ac_tsubst params args \<equiv> subst_term (the \<circ> (map_of (zip (map fst params) args)))"

lemma (in domain_signature) instantiate_classical_action_schema_alt: "instantiate_classical_action_schema ac args = 
  GroundAction
  (map_atom_fmla (ac_tsubst (ac_params ac) args) (ac_pre ac))
  (map_ast_effect (ac_tsubst (ac_params ac) args) (ac_eff ac))"
  apply (cases ac rule: ast_classical_action_schema_cases_unfold)
  by simp

end

context ast_classical_problem begin

lemma res_inst_alt: "res_inst \<pi> =
  Some (instantiate_classical_action_schema (the (resolve_classical_action_schema (name \<pi>))) (arguments \<pi>))"
  by (cases \<pi>; simp)

lemma (in wf_ast_classical_problem) res_inst_cond:
  assumes "SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff) \<in> set (actions D)"
  shows "res_inst (SimplePlanAction n args) = Some (GroundAction
    (map_atom_fmla (ac_tsubst params args) pre)
    (map_ast_effect (ac_tsubst params args) eff))"
  using assms by (auto 
      dest: resolve_classical_action_schema_cond 
      simp: instantiate_classical_action_schema_alt)

(* removing the redundant conjunct from the definition of wf_classical_plan_action *)
lemma (in ast_classical_problem) wf_classical_plan_action_simple:
  "wf_classical_plan_action (SimplePlanAction n args) \<longleftrightarrow> (case resolve_classical_action_schema n of
    None \<Rightarrow> False | Some a \<Rightarrow> action_params_match (head a) args)"
  by (auto split: option.splits ast_classical_action_schema.splits)
  

(* unnecessary? *)
lemma (in ast_classical_problem) wf_classical_plan_action_alt: "wf_classical_plan_action \<pi> \<longleftrightarrow>
  (case resolve_classical_action_schema (name \<pi>) of
    None \<Rightarrow> False |
    Some a \<Rightarrow> action_params_match (head a) (arguments \<pi>))"
  apply (induction \<pi>)
  unfolding wf_classical_plan_action_simple ast_classical_plan_action.sel by simp 

lemma (in wf_ast_classical_problem) wf_classical_plan_action_cond:
  assumes "a \<in> set (actions D)"
      and "ac_name a = n"
  shows "wf_classical_plan_action (SimplePlanAction n args) \<longleftrightarrow>
    action_params_match (ac_head a) args"
  using assms wf_classical_plan_action_simple resolve_classical_action_schema_cond
  apply (cases a rule: ast_classical_action_schema_cases_unfold)
  by force

(* wf_ground_action_alt moved to Grounding_Common.PDDL_Sema_Supplement *)

text \<open> Note to self: ground_action_path checks if preconditions are enabled,
but valid_classical_plan_alt only checks it via ground_action_path.
I don't see any redundancy. plan_action_enabled is only used in proofs. \<close>

end

subsection \<open> Further properties \<close>

(* consts_objs_disj, objm_le_objT, bigand_wf, bigor_wf, wf_fmla_atom_pred,
   wf_lwm_basic, wf_func_assign_imp_not_predAtm moved to
   Grounding_Common.PDDL_Sema_Supplement *)

lemma (in wf_ast_classical_problem) wf_I:
  "wf_world_model I" unfolding I_def
  using wf_P wf_func_assign_imp_not_predAtm by auto

lemma (in wf_ast_classical_problem) i_basic:
  "lwm_basic (fst I)"
  using wf_I wf_lwm_basic by blast

(* wf_fmla_mono, wf_numeric_effect_mono, wf_effect_mono moved to
   Grounding_Common.PDDL_Sema_Supplement *)

text \<open> Properties of sig \<close>

(* split_pred, split_pred_alt, pred_resolve, sig_Some moved to
   Grounding_Common.PDDL_Sema_Supplement *)

(* sig_None moved to Grounding_Common.PDDL_Sema_Supplement *)

text \<open> Properties of func_sig \<close>

(* split_func, split_func_alt, func_resolve, func_sig_Some moved to
   Grounding_Common.PDDL_Sema_Supplement *)

(* func_sig_None moved to Grounding_Common.PDDL_Sema_Supplement *)

text \<open> action parameters \<close>

lemma (in -) ac_tsubst_intro:
  assumes "distinct (map fst params)" "params ! i = (v, vT)" "args ! i = n" "i < length params" "i < length args"
  shows "ac_tsubst params args (term.VAR v) = n"
proof -
  have "(v, n) \<in> set (zip (map fst params) args)"
    using assms in_set_zip by fastforce
  moreover have "distinct (map fst (zip (map fst params) args))"
    using assms(1) by (simp add: map_fst_zip_take)
  ultimately have "(the \<circ> map_of (zip (map fst params) args)) v = n"
    by simp
  thus ?thesis using ac_tsubst_def by fastforce
qed

text \<open> Action resolution \<close>

lemma (in wf_ast_classical_domain) resolve_classical_action_schema_name:
  assumes "a \<in> set (actions D)"
  shows "resolve_classical_action_schema (ac_name a) = Some a"
  unfolding resolve_classical_action_schema_def
  using wf_D(2) assms by simp

text \<open> (Plan) Action instantiation \<close>

(* only first condition matters in wf_ast_classical_problem. See: res_aux*)
lemma (in ast_classical_problem) wf_pa_refs_ac:
  assumes "wf_classical_plan_action (SimplePlanAction n args)"
  obtains ac where 
    "resolve_classical_action_schema n = Some ac" 
    "ac \<in> set (actions D)"
    "ac_name ac = n" 
    "action_params_match (head ac) args"
  using assms
  apply (cases "resolve_classical_action_schema n")
   apply simp
  subgoal for a
    apply (cases a)
    by (force simp: resolve_classical_action_schema_def dest: index_by_eq_SomeD)
  done

lemma (in ast_classical_problem) wf_pa_res_sas:
  assumes "wf_classical_plan_action a"
  obtains ac where 
    "resolve_classical_action_schema (name a) = Some ac" 
    "ac \<in> set (actions D)"
    "ac_name ac = name a" 
    "action_params_match (head ac) (arguments a)"
  using assms wf_pa_refs_ac by (cases a) auto

lemma (in wf_ast_classical_domain) res_aux:
  "resolve_classical_action_schema n = Some ac \<longleftrightarrow>
     ac \<in> set (actions D) \<and> ac_name ac = n"
  by (simp add: resolve_classical_action_schema_def wf_D)


theorem (in wf_ast_classical_problem) wf_resolve_instantiate:
  assumes "wf_classical_plan_action \<pi>"
  shows "wf_ground_action (the (res_inst \<pi>))"
proof (cases \<pi>)
  case [simp]: (SimplePlanAction n args)
  with assms obtain ac where
    ac: "resolve_classical_action_schema n = Some ac" and
    "action_params_match (head ac) args" and
    "ac \<in> set (actions D)"
    using wf_pa_refs_ac by metis
  thus ?thesis 
    apply (induction ac rule: ast_classical_action_schema_induct_unfold)
    using wf_inst_action_schema wf_D by fastforce
qed

theorem (in wf_ast_classical_problem) wf_execute_stronger:
  assumes "wf_classical_plan_action \<pi>"
  assumes "wf_world_model s"
  shows "wf_world_model (execute_plan_action \<pi> s)"
proof -
  let ?a = "(the o res_inst) \<pi>"
  from assms(1) have wfa: "wf_ground_action ?a"
    using wf_resolve_instantiate by simp
  hence wf_eff: "wf_effect objT (ground_action.effect ?a)"
    using wf_ground_action_alt by simp
  have t_eq: "execute_plan_action \<pi> s =
    (fst s - set (dels (ground_action.effect ?a)) \<union> set (adds (ground_action.effect ?a)),
     action_numeric_update_function ?a (snd s))"
    using execute_plan_action_def apply_ground_action_alt
    by (cases s) simp
  have "Ball (fst s) (wf_fmla_atom objT)"
    using assms(2) by (cases s) simp
  moreover have "Ball (set (adds (ground_action.effect ?a))) (wf_fmla_atom objT)"
    using wf_eff wf_effect_alt list_all_iff by metis
  ultimately have "Ball (fst (execute_plan_action \<pi> s)) (wf_fmla_atom objT)"
    using t_eq by auto
  thus ?thesis by (cases "execute_plan_action \<pi> s") simp
qed


lemma (in wf_ast_classical_problem) wf_valid_classical_plan_alt:
  assumes "wf_world_model M" "valid_classical_plan_alt M \<pi>s M'"
  shows "wf_world_model M'"
  using assms
proof (induction \<pi>s arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons a \<pi>s)
  have "valid_classical_plan_alt (execute_plan_action a M) \<pi>s M'" using Cons by simp
  moreover
  have "wf_world_model (execute_plan_action a M)" 
    using wf_execute_stronger Cons plan_action_enabled_def 
    by auto
  ultimately
  show ?case                                                                                        
    using Cons.IH by fast
qed


lemma (in ast_classical_problem) valid_classical_plan_from2_snoc:
  "valid_classical_plan_from2 M (\<pi>s @ [\<pi>]) \<longleftrightarrow>
    (\<exists>M'. valid_classical_plan_alt M \<pi>s M' \<and> plan_action_enabled \<pi> M' \<and>
      valuation (execute_plan_action \<pi> M') \<Turnstile>\<^sub>m goal P)"
  unfolding valid_classical_plan_from2_alt
  apply (induction \<pi>s arbitrary: M)
  by auto


(* formula_atom_simps moved to Grounding_Common.PDDL_Sema_Supplement *)

(* atoms_dom_valuation_Un_eq, atoms_dom_valuation_Diff_eq moved to Grounding_Common.PDDL_Sema_Supplement *)

(* entail_adds_irrelevant, entail_dels_irrelevant moved to Grounding_Common.PDDL_Sema_Supplement *)

subsection \<open>PDDL Instance Relationships\<close>

text \<open>This subsection concerns itself mostly with relationships between two PDDL instances
  (domains or problems). They are of particular interest since the normalization steps produce
  new instances that retain some of the previous properties.\<close>

(* The well-formedness covariance lemmas co_fmla_wf, co_fmla_atom_wf,
   co_numeric_expression_wf, co_numeric_effect_wf, co_effect_wf, co_wm_wf moved to
   Grounding_Common.PDDL_Sema_Supplement (they are AST-agnostic, signature-level). *)

subsection \<open> Formula Preds \<close>

(* fmla_preds, fmla_preds_alt, map_preserves_fmla_preds, notin_fmla_preds_notin_atoms
   moved to Grounding_Common.PDDL_Sema_Supplement *)

subsection \<open> Formula PNEs \<close>

(* wf_numeric_expression_imp_wf_pnes, wf_atom_imp_wf_pnes, wf_fmla_imp_wf_pnes,
   wf_fmla_imp_wf_pred_atom, wf_fmla_imp_eqs_def, wf_numeric_expressionI, wf_atomI, wf_fmlaI
   moved to Grounding_Common.PDDL_Sema_Supplement *)

(* formula_atoms_in_dom_valuation_iff moved to Grounding_Common.PDDL_Sema_Supplement *)

section \<open>Numeric-freeness (the propositional fragment)\<close>

text \<open>Structural predicates identifying the numeric atoms / numeric-free formulas / effects /
  actions / domains / problems: the arithmetic-comparison atoms are numeric; \<^const>\<open>predAtm\<close> and
  \<^const>\<open>eqAtm\<close> are not. These identify the propositional fragment the STRIPS backend supports.
  The \<open>numeric_free_*\<close> locales and the executable-check bundle live downstream in
  \<^verbatim>\<open>Numeric_Free\<close>, and \<open>relaxed_problem\<close> (in \<^verbatim>\<open>Classical_PDDL_Normalization\<close>) carries
  numeric-freeness as an assumption.\<close>

fun is_numeric_atom :: "'ent atom \<Rightarrow> bool" where
  "is_numeric_atom (numericEqAtm _ _) = True"
| "is_numeric_atom (numericLessAtm _ _) = True"
| "is_numeric_atom (numericLEAtm _ _) = True"
| "is_numeric_atom (numericGreaterAtm _ _) = True"
| "is_numeric_atom (numericGEAtm _ _) = True"
| "is_numeric_atom _ = False"

fun num_free_fmla :: "'ent atom formula \<Rightarrow> bool" where
  "num_free_fmla (Atom a) = (\<not> is_numeric_atom a)"
| "num_free_fmla \<bottom> = True"
| "num_free_fmla (\<^bold>\<not> \<phi>) = num_free_fmla \<phi>"
| "num_free_fmla (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = (num_free_fmla \<phi>\<^sub>1 \<and> num_free_fmla \<phi>\<^sub>2)"
| "num_free_fmla (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = (num_free_fmla \<phi>\<^sub>1 \<and> num_free_fmla \<phi>\<^sub>2)"
| "num_free_fmla (\<phi>\<^sub>1 \<^bold>\<rightarrow> \<phi>\<^sub>2) = (num_free_fmla \<phi>\<^sub>1 \<and> num_free_fmla \<phi>\<^sub>2)"

lemma num_free_fmla_un_and:
  "num_free_fmla F \<Longrightarrow> \<forall>f \<in> set (un_and F). num_free_fmla f"
  by (induction F rule: un_and.induct) auto

lemma num_free_fmla_Atom_predAtom:
  assumes "num_free_fmla (Atom a)" and "\<not> is_eqAtom (Atom a)"
  shows "is_predAtom (Atom a)"
  using assms by (cases a) auto

lemma num_free_fmla_atoms:
  assumes "num_free_fmla \<phi>"
      and "a \<in> atoms \<phi>"
  shows "\<not> is_numeric_atom a"
  using assms by (induction \<phi>) auto

text \<open>The introduction rule dual to \<open>num_free_fmla_atoms\<close>: a formula all of whose atoms are
  non-numeric is numeric-free. Together the two make \<^const>\<open>num_free_fmla\<close> an atom-set property,
  which is what carries it through the atom-preserving pipeline stages (DNF splitting).\<close>
lemma num_free_fmla_atomsI:
  assumes "\<And>a. a \<in> atoms \<phi> \<Longrightarrow> \<not> is_numeric_atom a"
  shows "num_free_fmla \<phi>"
  using assms by (induction \<phi>) auto

lemma num_free_fmla_of_predAtom:
  assumes "is_predAtom \<phi>"
  shows "num_free_fmla \<phi>"
  using assms by (cases \<phi> rule: is_predAtom.cases) auto

lemma num_free_fmla_BigAnd:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> num_free_fmla f"
  shows "num_free_fmla (\<^bold>\<And> fs)"
  using assms by (induction fs) auto

lemma num_free_fmla_BigOr:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> num_free_fmla f"
  shows "num_free_fmla (\<^bold>\<Or> fs)"
  using assms by (induction fs) auto

fun num_free_eff :: "'ent ast_effect \<Rightarrow> bool" where
  "num_free_eff (Effect a d n) =
     ((\<forall>\<phi> \<in> set a. num_free_fmla \<phi>) \<and> (\<forall>\<phi> \<in> set d. num_free_fmla \<phi>) \<and> n = [])"

definition num_free_ac :: "ast_classical_action_schema \<Rightarrow> bool" where
  "num_free_ac a \<equiv> num_free_fmla (ac_pre a) \<and> num_free_eff (ac_eff a)"

definition (in ast_classical_domain) num_free_dom :: bool where
  "num_free_dom \<equiv> \<forall>a \<in> set (actions D). num_free_ac a"

definition (in ast_classical_problem) num_free_prob :: bool where
  "num_free_prob \<equiv> num_free_dom \<and> num_free_fmla (goal P) \<and> (\<forall>f \<in> set (init P). num_free_fmla f)"

subsection \<open>Term-mapping preserves numeric-freeness\<close>

text \<open>Mapping the entity type of an atom / formula / effect (e.g.\ the \<^const>\<open>term.CONST\<close> lift or
  an \<^const>\<open>ac_tsubst\<close> instantiation) cannot change the atom \<^emph>\<open>constructors\<close>, so it preserves
  numeric-freeness in both directions. Stated on \<^const>\<open>map_formula\<close>/\<^const>\<open>map_atom\<close> directly
  (the composed form \<open>map_atom_fmla\<close> normalizes to it under \<open>o_apply\<close>).\<close>

lemma is_numeric_atom_map_atom [simp]:
  "is_numeric_atom (map_atom f a) = is_numeric_atom a"
  by (cases a) simp_all

lemma num_free_fmla_map_atom_fmla [simp]:
  "num_free_fmla (map_formula (map_atom f) \<phi>) = num_free_fmla \<phi>"
  by (induction \<phi>) simp_all

lemma num_free_eff_map_ast_effect [simp]:
  "num_free_eff (map_ast_effect f \<epsilon>) = num_free_eff \<epsilon>"
  by (cases \<epsilon>) simp

subsection \<open>Numeric-freeness of resolved-and-instantiated plan actions\<close>

text \<open>A resolved action-schema name denotes a schema of the domain's action list.\<close>
lemma (in ast_classical_problem) resolve_schema_mem:
  assumes "resolve_classical_action_schema n = Some a"
  shows "a \<in> set (actions D)"
  using assms unfolding resolve_classical_action_schema_def by (meson index_by_eq_SomeD)

text \<open>A well-formed plan action resolves to a schema of the domain, and instantiation is a
  \<^const>\<open>map_atom_fmla\<close>/\<^const>\<open>map_ast_effect\<close> term-substitution, so on a numeric-free domain
  the instantiated ground action's body is numeric-free. Stated with
  \<open>wf_classical_plan_action\<close> assumed directly (rather than inside a reachable-ops locale), so
  any consumer can apply it without interpreting one.\<close>
lemma (in ast_classical_problem) num_free_resinst':
  assumes wf_pi: "wf_classical_plan_action \<pi>"
      and nfd: num_free_dom
  shows "num_free_fmla (precondition (the (res_inst \<pi>)))"
    and "num_free_eff (effect (the (res_inst \<pi>)))"
proof -
  obtain n args where pi: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  obtain a where a: "resolve_classical_action_schema n = Some a"
    using wf_pi pi wf_classical_plan_action_simple by (auto split: option.splits)
  have nfa: "num_free_ac a"
    using nfd resolve_schema_mem[OF a] unfolding num_free_dom_def by blast
  have pre: "precondition (the (res_inst \<pi>))
      = map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a)"
    using a unfolding pi by (simp add: instantiate_classical_action_schema_alt)
  have eff: "effect (the (res_inst \<pi>))
      = map_ast_effect (ac_tsubst (ac_params a) args) (ac_eff a)"
    using a unfolding pi by (simp add: instantiate_classical_action_schema_alt)
  show "num_free_fmla (precondition (the (res_inst \<pi>)))"
    using nfa unfolding pre num_free_ac_def by simp
  show "num_free_eff (effect (the (res_inst \<pi>)))"
    using nfa unfolding eff num_free_ac_def by simp
qed

end