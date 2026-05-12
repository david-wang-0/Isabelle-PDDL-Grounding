theory PDDL_Sema_Supplement                
  imports Classical_Planning.Classical_Happening_Semantics
  Grounding_Utils Formula_Utils iq.iq
begin

subsection \<open>Formulas\<close>

lemma BigOr_map_semantics[simp]: "A \<Turnstile>\<^sub>m \<^bold>\<Or>F = ((\<forall>f\<in>set F. atoms f \<subseteq> dom A) \<and> (\<exists>f \<in> set F. A \<Turnstile>\<^sub>m f))"
  by (induction F) auto

lemma BigAnd_map_semantics[simp]: "A \<Turnstile>\<^sub>m \<^bold>\<And>F = ((\<forall>f\<in>set F. A \<Turnstile>\<^sub>m f))"
  by (induction F) auto

subsection \<open> sugar \<close>

(* not much here yet *)

lemmas (in wf_domain_signature) wf_D_sig = conj_split_7[OF wf_domain_signature[unfolded wf_domain_signature_def]]

lemmas (in wf_problem_signature) wf_P_sig = conj_split_3[OF wf_problem_signature[unfolded wf_problem_signature_def]]

lemmas (in wf_problem_signature) wf_sig = wf_D_sig wf_P_sig

(* wf_domain unfolded and split *)
lemmas (in wf_ast_classical_domain) wf_D =
  conj_split_3[OF wf_classical_domain[unfolded wf_classical_domain_def]]

(* wf_problem unfolded and split, but omitting the first fact "wf_domain" *)
lemmas (in wf_ast_classical_problem) wf_P =
  conj_split_5[OF wf_classical_problem[unfolded wf_classical_problem_def]]

lemmas (in wf_ast_classical_problem) wf_DP = wf_D wf_P wf_D_sig wf_P_sig

declare ast_classical_problem.I_def[simp]

subsection \<open> Accessor functions \<close>

(* what's the builtin way? *)
fun un_Atom :: "'a formula \<Rightarrow> 'a" where
  "un_Atom (Atom x) = x" |
  "un_Atom _ = undefined"

abbreviation "unPredAtom \<equiv> predicate \<circ> un_Atom"

abbreviation (input) get_t :: "type \<Rightarrow> name" where
    "get_t T \<equiv> hd (primitives T)"
lemma get_t_alt: "get_t (Either (t # ts)) = t"
  by simp

lemma is_predAtom_decomp:
  "is_predAtom a \<longleftrightarrow> (\<exists>p xs. a = Atom (predAtm p xs))"
  apply (cases a)
  subgoal for x
    by (cases x) simp_all
  by simp_all

abbreviation (in domain_signature) pred_names :: "name list" where
    "pred_names \<equiv> map (predicate.name \<circ> pred) predicates"

abbreviation (in problem_signature) "all_consts \<equiv> consts @ objs"

subsection \<open>Alternative definitions\<close>

text \<open>Alternative definitions. Most of these just remove pattern matching
  from functions, e.g. a function "add (x, y) = x + y" would be turned into
  "add p = fst p + snd p".
  They are often unnecessary because you can just apply "cases" in a proof.
  Others functions are only well-defined if a certain condition holds. The _cond-lemmas
  help resolve it directly. \<close>

abbreviation "map_atom_fmla \<equiv> map_formula \<circ> map_atom"

abbreviation "ac_head \<equiv> ast_classical_action_schema.head"
abbreviation "ac_name a \<equiv> ast_action_head.name (ac_head a)"
abbreviation "ac_params a \<equiv> ast_action_head.parameters (ac_head a)"

fun ac_body :: "ast_classical_action_schema \<Rightarrow> ast_simple_action_body" where
  "ac_body (SimpleActionSchema _ b) = b"
abbreviation "ac_pre a \<equiv> ast_simple_action_body.precondition (ac_body a)"
abbreviation "ac_eff a \<equiv> ast_simple_action_body.effect (ac_body a)"

(* effect of a single ground action on a (logical, numeric) world model *)
lemma apply_ground_action_alt:
  "apply_ground_actions [a] (L, N) =
     ((L - set (dels (effect a))) \<union> set (adds (effect a)),
      action_numeric_update_function a N)"
  by (simp add: action_list_numeric_update_function_def)

(* These two are useful to adapt to new semantics *)
context ast_classical_problem
begin
lemma classical_plan_happ_path_alt: 
  "classical_plan_happ_path M \<pi> M' \<longleftrightarrow>
  valid_classical_plan M (map (the o res_inst) \<pi>) M'"
  using classical_plan_happ_path_def ind_classical_plan_def by simp


definition "plan_action_enabled a M \<equiv> 
let 
  a' = (the o res_inst) a
in
  numeric_effects_non_intrf a' \<and> wf_classical_plan_action a \<and> valuation M \<Turnstile>\<^sub>m precondition a'"

definition "execute_plan_action a M \<equiv>
  apply_ground_actions [(the o res_inst) a] M"

fun valid_classical_plan_alt where
"valid_classical_plan_alt M [] M' = (M = M')" |
"valid_classical_plan_alt M (a#as) M' = (
  plan_action_enabled a M
\<and> valid_classical_plan_alt (execute_plan_action a M) as M'
)"

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
    \<and> numeric_effects_non_intrf a' 
    \<and> valuation M \<Turnstile>\<^sub>m ground_action.precondition a')" 
    by (auto simp: Let_def Cons.IH
        wf_classical_plan_def execute_plan_action_def plan_action_enabled_def)
  also have "... = (wf_classical_plan (a#as) \<and> 
    (let a' = (the o res_inst) a 
    in classical_plan_happ_path (apply_ground_actions [a'] M) as M'
    \<and> numeric_effects_non_intrf a' 
    \<and> valuation M \<Turnstile>\<^sub>m ground_action.precondition a'))" by (simp add: Let_def)
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

end

context domain_signature 
begin
lemma wf_fmla_alt: "wf_fmla tyt \<phi> = (\<forall>a\<in>atoms \<phi>. wf_atom tyt a)"
      by (induction \<phi>) auto

lemma subtype_edge_swap: "subtype_edge = prod.swap"
  by (intro ext; auto)

lemma subtype_rel_alt: "subtype_rel = (set ty_decl)\<inverse>"
  unfolding subtype_rel_def
  by (subst subtype_edge_swap; auto)

lemma subtype_rel_star_alt: "subtype_rel\<^sup>* = ((set ty_decl)\<^sup>*)\<inverse>"
    using subtype_rel_alt rtrancl_converse by simp

(* useless? *)
lemmas wf_atom_deep = wf_atom.simps[unfolded wf_pred_atom.simps]


lemma wf_effect_alt:
    "wf_effect tyt \<epsilon> \<longleftrightarrow>
        (list_all (wf_fmla_atom tyt) (adds \<epsilon>))
      \<and> (list_all (wf_fmla_atom tyt) (dels \<epsilon>))
      \<and> (list_all (wf_numeric_effect tyt) (numeric_effects \<epsilon>))"
  by (cases \<epsilon>; auto simp: list_all_iff)

definition "ac_tyt a \<equiv> ty_term (map_of (ac_params a)) constT"

lemma (in domain_signature) wf_action_head_alt: "wf_action_head h \<longleftrightarrow> 
  distinct (map fst (ast_action_head.parameters h))" by (cases h) simp

lemma (in domain_signature) wf_simple_action_body_alt: "wf_simple_action_body tyt b \<longleftrightarrow>
  wf_fmla tyt (ast_simple_action_body.precondition b) \<and> wf_effect tyt (ast_simple_action_body.effect b)"
  by (cases b) simp

lemma (in domain_signature) wf_classical_action_schema_alt: "wf_classical_action_schema ac \<longleftrightarrow>
    distinct (map fst (ac_params ac))
  \<and> wf_fmla (ac_tyt ac) (ac_pre ac)
  \<and> wf_effect (ac_tyt ac) (ac_eff ac)"
  by (cases ac, simp add: Let_def wf_action_head_alt wf_simple_action_body_alt ac_tyt_def)
  

(* unnecessary? *)
lemma wf_type_alt: "wf_type T \<longleftrightarrow> set (primitives T) \<subseteq> insert (STR ''object'') (fst ` set ty_decl)"
  by (cases T; simp)

(* unnecessary? *)
lemma wf_predicate_decl_alt: "wf_predicate_decl pd \<longleftrightarrow> list_all1 wf_type (predicate_decl.argTs pd)"
  by (cases pd; simp)

lemma wf_function_decl_alt: "wf_function_decl fd \<longleftrightarrow> list_all1 wf_type (function_decl.argTs fd)"
  by (cases fd; simp)

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

find_theorems name: "ast_simple_action_body.indu"

lemma instantiate_classical_action_schema_alt: "instantiate_classical_action_schema ac args = 
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
lemma (in wf_ast_classical_problem) wf_classical_plan_action_simple:
  "wf_classical_plan_action (SimplePlanAction n args) \<longleftrightarrow> (case resolve_classical_action_schema n of
    None \<Rightarrow> False | Some a \<Rightarrow> action_params_match (head a) args)"
  by (auto split: option.splits ast_classical_action_schema.splits)
  

(* unnecessary? *)
lemma (in wf_ast_classical_problem) wf_classical_plan_action_alt: "wf_classical_plan_action \<pi> \<longleftrightarrow>
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

(* unnecessary? *)
lemma (in problem_signature) wf_ground_action_alt: "wf_ground_action ga \<longleftrightarrow>
  wf_fmla objT (precondition ga) \<and> wf_effect objT (effect ga)"
  by (cases ga; simp)

text \<open> Note to self: ground_action_path checks if preconditions are enabled,
but plan_action_path only checks it via ground_action_path.
I don't see any redundancy. plan_action_enabled is only used in proofs. \<close>

end

subsection \<open> Further properties \<close>

lemma (in wf_problem_signature) consts_objs_disj:
  "fst ` set consts \<inter> fst ` set objs = {}"
  using list.set_map wf_P_sig by auto

lemma (in wf_problem_signature) objm_le_objT: "map_of objs \<subseteq>\<^sub>m objT"
proof -
  have "dom constT \<inter> dom (map_of objs) = {}"
    using constT_def consts_objs_disj
    by (simp add: dom_map_of_conv_image_fst)
  thus ?thesis using objT_def
    by (simp add: map_add_comm map_le_iff_map_add_commute)  
qed

lemma (in domain_signature) bigand_wf:
  assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
  shows "wf_fmla tyt (\<^bold>\<And> \<phi>s)"
  using assms by (induction \<phi>s; simp)

lemma (in domain_signature) bigor_wf:
  assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
  shows "wf_fmla tyt (\<^bold>\<Or> \<phi>s)"
  using assms by (induction \<phi>s; simp)

lemma (in domain_signature) wf_fmla_atom_pred:
  "wf_fmla_atom tyt f \<Longrightarrow> is_predAtom f"
  apply (cases f)
  subgoal for a
    by (cases a) auto
  by auto

lemma (in problem_signature) wf_lwm_basic:
  "wf_world_model M \<Longrightarrow> lwm_basic (fst M)"
  using wf_fmla_atom_pred unfolding lwm_basic_def 
  by (cases M) auto

lemma (in problem_signature) wf_func_assign_imp_not_predAtm:
  "wf_func_assign x \<Longrightarrow> \<not>is_predAtom x"
  apply (cases x)
  subgoal for a
    apply (cases a)
    by auto
  by auto

lemma (in wf_ast_classical_problem) wf_I:
  "wf_world_model I" unfolding I_def
  using wf_P wf_func_assign_imp_not_predAtm by auto

lemma (in wf_ast_classical_problem) i_basic:
  "lwm_basic (fst I)"
  using wf_I wf_lwm_basic by blast

lemma (in domain_signature) wf_fmla_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_fmla tys \<phi>"
  shows "wf_fmla tys' \<phi>"
  using assms apply (induction \<phi>)
       apply (simp add: wf_atom_mono) by simp_all

find_theorems name: "wf*mono"

lemma (in domain_signature) wf_numeric_effect_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_numeric_effect tys f"
  shows "wf_numeric_effect tys' f"
  using assms(2) apply (induction f)
  using wf_numeric_expression_mono[OF assms(1)] wf_pne_mono[OF assms(1)]
  by simp

lemma (in domain_signature) wf_effect_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_effect tys eff"
  shows "wf_effect tys' eff"
  using assms apply (cases eff)
  using wf_fmla_atom_mono[OF assms(1)] wf_numeric_effect_mono[OF assms(1)]
  by simp

text \<open> Properties of sig \<close>

abbreviation "split_pred \<equiv> (\<lambda>PredDecl p n \<Rightarrow> (p, n))"

lemma split_pred_alt: "split_pred p = (pred p, predicate_decl.argTs p)"
  using predicate_decl.case_eq_if by auto

lemma (in domain_signature) pred_resolve:
  assumes "distinct (map pred predicates)"
  shows "sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set predicates"
proof -
  let ?preds = "predicates"
  have "map (fst \<circ> split_pred) ?preds = map pred ?preds"
    using split_pred_alt by simp
  hence dis: "distinct (map (fst \<circ> split_pred) ?preds)"
    using assms by metis

  have "PredDecl p Ts \<in> set ?preds
    \<longleftrightarrow> (p, Ts) \<in> set (map split_pred ?preds)"
    using split_pred_alt by force
  also have "... \<longleftrightarrow> map_of (map split_pred ?preds) p = Some Ts"
    using dis by simp

  ultimately show ?thesis using sig_def by simp
qed

lemmas (in wf_domain_signature) sig_Some = pred_resolve[OF wf_D_sig(2)]

lemma (in domain_signature) sig_None:
    "sig p = None \<longleftrightarrow> p \<notin> pred ` set predicates"
  proof -
    have "sig p = None \<longleftrightarrow> p \<notin> fst ` set (map split_pred predicates)"
      using sig_def by (simp add: map_of_eq_None_iff)
    also have "... \<longleftrightarrow> p \<notin> pred ` set predicates"
      using split_pred_alt by auto
    ultimately show ?thesis by simp
  qed

text \<open> Properties of func_sig \<close>

abbreviation "split_func \<equiv> (\<lambda>FuncDecl f n \<Rightarrow> (f, n))"

lemma split_func_alt: "split_func f = (function_decl.func f, function_decl.argTs f)"
  using function_decl.case_eq_if by auto

lemma (in domain_signature) func_resolve:
  assumes "distinct (map function_decl.func functions)"
  shows "func_sig f = Some Ts \<longleftrightarrow> FuncDecl f Ts \<in> set functions"
proof -
  let ?funcs = "functions"
  have "map (fst \<circ> split_func) ?funcs = map function_decl.func ?funcs"
    using split_func_alt by simp
  hence dis: "distinct (map (fst \<circ> split_func) ?funcs)"
    using assms by metis

  have "FuncDecl f Ts \<in> set ?funcs
    \<longleftrightarrow> (f, Ts) \<in> set (map split_func ?funcs)"
    using split_func_alt by force
  also have "... \<longleftrightarrow> map_of (map split_func ?funcs) f = Some Ts"
    using dis by simp

  ultimately show ?thesis using func_sig_def by simp
qed

lemmas (in wf_domain_signature) func_sig_Some = func_resolve[OF wf_D_sig(4)]

lemma (in domain_signature) func_sig_None:
    "func_sig f = None \<longleftrightarrow> f \<notin> function_decl.func ` set functions"
  proof -
    have "func_sig f = None \<longleftrightarrow> f \<notin> fst ` set (map split_func functions)"
      using func_sig_def by (simp add: map_of_eq_None_iff)
    also have "... \<longleftrightarrow> f \<notin> function_decl.func ` set functions"
      using split_func_alt by auto
    ultimately show ?thesis by simp
  qed

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
(*

text \<open> Semantics \<close>

lemma (in ast_classical_problem) plan_action_path_append_intro:
  assumes "plan_action_path M1 \<pi>s M2 \<and> plan_action_path M2 \<mu>s M3"
  shows "plan_action_path M1 (\<pi>s @ \<mu>s) M3"
  using assms apply (induction \<pi>s arbitrary: M1)
  using plan_action_path_def apply simp
  using plan_action_path_def plan_action_path_Cons
  sorry

lemma (in ast_classical_problem) plan_action_path_append_elim:
  assumes "plan_action_path M1 (\<pi>s @ \<mu>s) M3"
  shows "\<exists>M2. plan_action_path M1 \<pi>s M2 \<and> plan_action_path M2 \<mu>s M3"
using assms by (induction \<pi>s arbitrary: M1) auto

lemma (in wf_ast_classical_problem) valid_plan_from_Cons[simp]:
  "valid_plan_from M (\<pi> # \<pi>s)
    \<longleftrightarrow> valid_plan_from (execute_plan_action \<pi> M) \<pi>s \<and> plan_action_enabled \<pi> M"
  using valid_plan_from_def by auto

lemma (in wf_ast_classical_problem) valid_plan_from_snoc:
  "valid_plan_from M (\<pi>s @ [\<pi>])
    \<longleftrightarrow> (\<exists>M'. plan_action_path M \<pi>s M' \<and> plan_action_enabled \<pi> M' \<and>
    execute_plan_action \<pi> M' \<^sup>c\<TTurnstile>\<^sub>= goal P)"
  using valid_plan_from_def by (induction \<pi>s arbitrary: M; simp)
*)


lemma formula_atom_simps[simp]:
  "atoms (Atom a) = {a}"
  "atoms \<bottom> = {}"
  "atoms (\<^bold>\<not> F) = atoms F"
  "atoms (F \<^bold>\<and> G) = atoms F \<union> atoms G"
  "atoms (F \<^bold>\<or> G) = atoms F \<union> atoms G"
  "atoms (F \<^bold>\<rightarrow> G) = atoms F \<union> atoms G"
  by auto

lemma atoms_dom_valuation_Un_eq:
  assumes "A \<inter> Atom ` atoms \<F> = {}"
  shows "(atoms \<F> \<subseteq> dom (valuation (M, X))) = (atoms \<F> \<subseteq> dom (valuation (M \<union> A, X)))"
  using assms
proof (induction \<F>)
  case (Atom x)
  then show ?case unfolding valuation_def by (induction x) auto
next
  case Bot
  then show ?case by auto
next
  case (Not \<F>)
  then show ?case by auto
next
  case (And \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))" using And by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))" using And by fastforce
  ultimately 
  show ?case by simp
next
  case (Or \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))" using Or by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))" using Or by fastforce
  ultimately 
  show ?case by simp
next
  case (Imp \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))" using Imp by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))" using Imp by fastforce
  ultimately 
  show ?case by simp
qed

lemma atoms_dom_valuation_Diff_eq:
  assumes "D \<inter> Atom ` atoms \<F> = {}"
  shows "(atoms \<F> \<subseteq> dom (valuation (M, X))) = (atoms \<F> \<subseteq> dom (valuation (M - D, X)))"
  using assms
proof (induction \<F>)
  case (Atom x)
  then show ?case unfolding valuation_def by (induction x) auto
next
  case Bot
  then show ?case by auto
next
  case (Not \<F>)
  then show ?case by auto
next
  case (And \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))" using And by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))" using And by fastforce
  ultimately 
  show ?case by simp
next
  case (Or \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))" using Or by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))" using Or by fastforce
  ultimately 
  show ?case by simp
next
  case (Imp \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))" using Imp by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))" using Imp by fastforce
  ultimately 
  show ?case by simp
qed
  

lemma entail_adds_irrelevant:
  assumes "lwm_basic M" "lwm_basic A"
          "A \<inter> Atom ` atoms \<F> = {}"
  shows "(valuation (M \<union> A, X) \<Turnstile>\<^sub>m \<F>) \<longleftrightarrow> (valuation (M, X) \<Turnstile>\<^sub>m \<F>)"
  using assms  
proof (induction \<F>)
  case (Atom x)
  thus ?case unfolding valuation_def by (cases x) simp_all
next
  case Bot
  then show ?case by simp
next
  case (Not \<F>)
  have "(atoms \<F> \<subseteq> dom (valuation (M, X))) = (atoms \<F> \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Not(4) by simp
  thus ?case unfolding map_formula_semantics_simps using Not by simp 
next
  case (And \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using And by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using And by auto
  ultimately
  show ?case by auto
next
  case (Or \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Or by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Or by auto
  ultimately
  show ?case by auto
next
  case (Imp \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Imp by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Imp by auto
  ultimately
  show ?case by auto
qed 

lemma entail_dels_irrelevant:
  assumes "lwm_basic M" "lwm_basic D"
          "D \<inter> Atom ` atoms \<F> = {}"
        shows "(valuation (M - D , X) \<Turnstile>\<^sub>m \<F>) \<longleftrightarrow> (valuation (M, X) \<Turnstile>\<^sub>m \<F>)"
  using assms
proof (induction \<F>)
  case (Atom x)
  then show ?case unfolding valuation_def by (cases x) simp_all    
next
  case Bot
  then show ?case by simp
next
  case (Not \<F>)
  have "(atoms \<F> \<subseteq> dom (valuation (M, X))) = (atoms \<F> \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Not(4) by simp
  thus ?case unfolding map_formula_semantics_simps using Not by simp 
next
  case (And \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using And by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using And by auto
  ultimately
  show ?case by auto
next
  case (Or \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Or by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Or by auto
  ultimately
  show ?case by auto
next
  case (Imp \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Imp by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Imp by auto
  ultimately
  show ?case by auto
qed 

subsection \<open>PDDL Instance Relationships\<close>

text \<open>This subsection concerns itself mostly with relationships between two PDDL instances
  (domains or problems). They are of particular interest since the normalization steps produce
  new instances that retain some of the previous properties.\<close>

lemma co_fmla_wf:
  assumes "\<And>a. domain_signature.wf_atom ty1 preds1 funs1 tyt1 a
            \<Longrightarrow> domain_signature.wf_atom ty2 preds2 funs2 tyt2 a"
  shows "domain_signature.wf_fmla ty1 preds1 funs1 tyt1 \<phi>
       \<Longrightarrow> domain_signature.wf_fmla ty2 preds2 funs2 tyt2 \<phi>"
  apply (induction \<phi>)
  unfolding domain_signature.wf_fmla.simps
  subgoal for x apply (induction x) 
    by (auto intro: assms) 
  by auto

lemma co_fmla_atom_wf:
  assumes "\<And>a. domain_signature.wf_atom ty1 preds1 funs1 tyt1 a
            \<Longrightarrow> domain_signature.wf_atom ty2 preds2 funs2 tyt2 a"
  shows "domain_signature.wf_fmla_atom ty1 preds1 tyt1 \<phi>
       \<Longrightarrow> domain_signature.wf_fmla_atom ty2 preds2 tyt2 \<phi>"
  apply (subst domain_signature.wf_fmla_atom_alt)
  apply (subst (asm) domain_signature.wf_fmla_atom_alt)
  by (auto intro: assms co_fmla_wf)

lemma co_numeric_expression_wf:
  assumes "\<And>p. domain_signature.wf_primitive_numeric_expression ty1 funs1 tyt1 p
            \<Longrightarrow> domain_signature.wf_primitive_numeric_expression ty2 funs2 tyt2 p"
  shows "domain_signature.wf_numeric_expression ty1 funs1 tyt1 n
       \<Longrightarrow> domain_signature.wf_numeric_expression ty2 funs2 tyt2 n"
  apply (induction n)
  unfolding domain_signature.wf_numeric_expression.simps
  by (auto intro: assms)

lemma co_numeric_effect_wf:
  assumes "\<And>p. domain_signature.wf_primitive_numeric_expression ty1 funs1 tyt1 p
            \<Longrightarrow> domain_signature.wf_primitive_numeric_expression ty2 funs2 tyt2 p"
  shows "domain_signature.wf_numeric_effect ty1 funs1 tyt1 ne
       \<Longrightarrow> domain_signature.wf_numeric_effect ty2 funs2 tyt2 ne"
  apply (induction ne)
  unfolding domain_signature.wf_numeric_effect.simps
  by (blast intro: assms co_numeric_expression_wf)
  

lemma co_effect_wf:
  assumes "\<And>a. domain_signature.wf_atom ty1 preds1 funs1 tyt1 a
            \<Longrightarrow> domain_signature.wf_atom ty2 preds2 funs2 tyt2 a"
      and "\<And>p. domain_signature.wf_primitive_numeric_expression ty1 funs1 tyt1 p
            \<Longrightarrow> domain_signature.wf_primitive_numeric_expression ty2 funs2 tyt2 p"
  shows "domain_signature.wf_effect ty1 preds1 funs1 tyt1 \<epsilon>
       \<Longrightarrow> domain_signature.wf_effect ty2 preds2 funs2 tyt2 \<epsilon>"
  unfolding domain_signature.wf_effect_alt list_all_iff
  by (auto intro: assms co_fmla_atom_wf co_numeric_effect_wf)

lemma co_wm_wf:
  assumes "\<And>a. domain_signature.wf_atom ty1 preds1 funs1
                 (problem_signature.objT consts1 objs1) a
            \<Longrightarrow> domain_signature.wf_atom ty2 preds2 funs2
                 (problem_signature.objT consts2 objs2) a"
  shows "problem_signature.wf_world_model ty1 preds1 consts1 objs1 m
       \<Longrightarrow> problem_signature.wf_world_model ty2 preds2 consts2 objs2 m"
  apply (induction m)
  unfolding problem_signature.wf_world_model.simps
  by (auto intro: assms co_fmla_atom_wf)

subsection \<open> Formula Preds \<close>

fun fmla_preds :: "'ent atom formula \<Rightarrow> predicate set" where
  "fmla_preds (Atom (predAtm p xs)) = {p}" |
  "fmla_preds (Atom _) = {}" |
  "fmla_preds \<bottom> = {}" |
  "fmla_preds (\<^bold>\<not> \<phi>) = fmla_preds \<phi>" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<rightarrow> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2"

lemma fmla_preds_alt: "fmla_preds \<phi> = {p | p xs. predAtm p xs \<in> atoms \<phi>}"
  apply (induction \<phi>)
  subgoal for x
    apply (cases x; simp_all)
    done
  by auto


lemma map_preserves_fmla_preds: "fmla_preds F = fmla_preds ((map_formula \<circ> map_atom) f F)"
proof (induction F)
  case (Atom x)
  thus ?case by (cases x) simp_all
qed auto

lemma notin_fmla_preds_notin_atoms: "p \<notin> fmla_preds \<phi> \<Longrightarrow> predAtm p args \<notin> atoms \<phi>"
  using fmla_preds_alt by blast


end