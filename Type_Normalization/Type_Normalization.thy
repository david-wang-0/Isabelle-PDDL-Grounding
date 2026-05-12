theory Type_Normalization
  imports Type_Normalization_Locales
begin

section \<open>Type Normalization Proofs\<close>

text \<open> Alternate/simplified definitions\<close>

lemma single_type_alt: "single_type T \<longleftrightarrow> length (primitives T) = 1"
  by (cases T; simp)

lemma type_decomp_1: assumes "single_type T" obtains t where "T = Either [t]"
  using assms Misc.list_decomp_1 by (cases T; auto)

lemma (in domain_signature) type_precond_alt: "type_precond p =
  \<^bold>\<Or> (map (type_atom (term.VAR (fst p))) (primitives (snd p)))"
  by (cases p; cases "snd p"; simp)

lemma detype_ent_alt: "detype_ent x = (fst x, \<omega>)"
  by (cases x; simp)

lemma (in domain_signature) detype_action_head_alt: "detype_action_head h = 
  ActionHead (ast_action_head.name h) (detype_ents (ast_action_head.parameters h))"
  by (cases h) force

lemma (in domain_signature) detype_action_body_alt: "detype_simple_action_body h b =
  SimpleActionBody (param_precond (ast_action_head.parameters h) \<^bold>\<and> (ast_simple_action_body.precondition b)) 
  (ast_simple_action_body.effect b)" by (cases h, cases b, simp)

lemma (in domain_signature) detype_classical_ac_alt: "detype_classical_ac ac = 
  SimpleActionSchema
    (detype_action_head (ast_classical_action_schema.head ac))
    (detype_simple_action_body (ast_classical_action_schema.head ac) (ast_classical_action_schema.body ac))"
  by (cases ac; simp)

lemma (in domain_signature) detype_classical_ac_sel [simp]:
  "ac_name (detype_classical_ac ac) = ac_name ac"
  "ac_params (detype_classical_ac ac) = detype_ents (ac_params ac)"
  "ac_pre (detype_classical_ac ac) = param_precond (ac_params ac) \<^bold>\<and> (ac_pre ac)"
  "ac_eff (detype_classical_ac ac) = ac_eff ac"
  by (cases ac, fastforce simp: detype_action_head_alt detype_action_body_alt detype_classical_ac_alt)+

(* detype_classical_dom_sel and detype_classical_prob_sel are declared in
   Type_Normalization_Locales.thy so they are available for the locale rewrites. *)

(* just these unfolded *)
lemma (in restrict_domain_signature) restrict_D_sig: "single_types consts"
  using restrict_dom_sig unfolding restrict_dom_sig_def by simp

lemma (in restrict_problem_signature) restrict_P_sig: "single_types objs"
  using restrict_prob_sig restrict_prob_sig_def by auto

lemma (in restrict_problem_signature) single_t_consts: "single_types all_consts"
  using restrict_D_sig restrict_P_sig by auto

lemma (in restrict_classical_domain) restrict_D: "\<forall>a \<in> set (actions D). wf_action_params a"
  using restrict_dom restrict_dom_def by auto

text \<open> type system \<close>

lemma (in wf_problem_signature) objT_Some: "(n, T) \<in> set (all_consts) \<longleftrightarrow> objT n = Some T"
proof -
  have "distinct (map fst (all_consts))"
    using wf_P_sig by auto
  thus ?thesis using objT_alt
    by (metis map_of_eq_Some_iff)
qed

lemma (in domain_signature) wf_object: "wf_type \<omega>"
  unfolding wf_type.simps by simp

context domain_signature
begin

text \<open> type_names \<close>
  
lemma type_names_set[simp]: "set type_names = insert (STR ''object'') (fst ` set ty_decl)"
  by auto

lemma wf_type_iff_listed: "wf_type (Either ts) \<longleftrightarrow> (set ts \<subseteq> set (type_names))"
  by auto

text \<open> pred_for_type \<close>

  lemma type_preds_ids: "map pred type_preds = map pred_for_type type_names"
    using type_preds_def by simp

  lemma type_pred_refs_type: "p \<in> pred ` set type_preds \<longleftrightarrow> (\<exists>t \<in> set type_names. p = pred_for_type t)"
  proof -
    have "pred ` set type_preds = pred_for_type ` set type_names"
      by (metis type_preds_ids list.set_map)
    thus ?thesis by auto
  qed

  lemma pred_for_type_inj: "inj pred_for_type"
  proof (rule injI)
    fix t1 t2 :: name
    assume "pred_for_type t1 = pred_for_type t2"
    hence "safe_prefix pred_names + (STR ''type_'' + t1)
         = safe_prefix pred_names + (STR ''type_'' + t2)"
      unfolding pred_for_type_def by simp
    hence "STR ''type_'' + t1 = STR ''type_'' + t2"
      using inj_prepend by (simp add: inj_eq)
    thus "t1 = t2"
      using inj_prepend by (simp add: inj_eq)
  qed

  lemma pred_for_type_dis:
    assumes "distinct ts"
    shows "distinct (map pred_for_type ts)"
    using assms pred_for_type_inj distinct_map inj_on_subset by blast

text \<open> type_preds \<close>

  lemma type_preds_dis:
    "distinct (map pred type_preds)"
    using pred_for_type_dis type_preds_ids by force

  lemma type_pred_notin: "pred_for_type t \<notin> pred ` set predicates"
  proof -
    have "predicate.name (pred_for_type t) \<notin> set pred_names"
      using safe_prefix_correct[of pred_names "STR ''type_'' + t"]
      unfolding pred_for_type_def by simp
    thus ?thesis by force
  qed

text \<open> detyped preds \<close>

  lemma preds_detyped:
    "\<forall>p \<in> set detyped_predicates. \<forall>T \<in> set (predicate_decl.argTs p). T = \<omega>"
    unfolding detype_preds_def detyped_predicates_def type_preds_def
    by fastforce

  lemma (in -) dt_preds_ids:
    "map pred (detype_preds ps) = map pred ps"
    using detype_preds_def by simp

  lemma type_preds_dt_preds_disj:
    "pred ` set type_preds \<inter> pred ` set (detype_preds predicates) = {}"
  proof -
    have "pred ` set type_preds = pred_for_type ` set type_names"
      by (metis type_preds_ids list.set_map)
    moreover have "pred ` set (detype_preds predicates) = pred ` set predicates"
      using dt_preds_ids by (metis list.set_map)
    ultimately show ?thesis using type_pred_notin
      by (metis disjoint_iff_not_equal type_pred_refs_type)
  qed

  lemma (in wf_domain_signature) t_preds_dis:
    shows "distinct (map pred (detyped_predicates))"
  proof -
    (* Predicate names are unique because the original predicate names are unchanged
       and the additional predicate names are unique (based on unique type names)
       and distinct from the original predicates. *)

    have "distinct (map pred (detype_preds predicates))"
      using dt_preds_ids wf_D_sig by presburger
    hence "distinct (map pred (type_preds @ detype_preds predicates))"
      using type_preds_dt_preds_disj type_preds_dis by simp
    thus ?thesis using detyped_predicates_def by presburger
  qed

  (* here, _alt definition is actually needed *)
  lemma (in domain_signature2) t_preds_wf:
    "list_all sig2.wf_predicate_decl detyped_predicates"
    using preds_detyped sig2.wf_predicate_decl_alt
    unfolding list_all_iff by fastforce

text \<open> detyped funcs \<close>

  lemma funcs_detyped:
    "\<forall>f \<in> set detyped_functions. \<forall>T \<in> set (function_decl.argTs f). T = \<omega>"
  proof -
    have "function_decl.argTs (detype_fun fd) = replicate (length (function_decl.argTs fd)) \<omega>" for fd
      by (cases fd) simp
    thus ?thesis
      unfolding detyped_functions_def detype_funs_def by auto
  qed

  lemma (in -) dt_funs_ids:
    "map function_decl.func (detype_funs fs) = map function_decl.func fs"
  proof -
    have "function_decl.func (detype_fun fd) = function_decl.func fd" for fd
      by (cases fd) simp
    thus ?thesis unfolding detype_funs_def by simp
  qed

  lemma (in wf_domain_signature) t_funs_dis:
    shows "distinct (map function_decl.func (detyped_functions))"
    (* Function names are unchanged by detyping, so distinctness is inherited
       from the well-formedness of the original signature. *)
    using dt_funs_ids wf_D_sig detyped_functions_def by presburger

  lemma (in domain_signature2) t_funs_wf:
    "list_all sig2.wf_function_decl detyped_functions"
    using funcs_detyped sig2.wf_function_decl_alt
    unfolding list_all_iff by fastforce

text \<open> detype ents \<close>

  lemma (in -) ents_detyped: "\<forall>(n, T) \<in> set (detype_ents ents). T = \<omega>"
    by (auto simp add: detype_ents_def)

  lemma (in domain_signature2) consts_detyped: "\<forall>(n, T) \<in> set detyped_consts. T = \<omega>"
    unfolding detyped_consts_def by (rule ents_detyped)

  lemma (in problem_signature2) objs_detyped: "\<forall>(n, T) \<in> set detyped_objs. T = \<omega>"
    unfolding detyped_objs_def by (rule ents_detyped)

  lemma (in -) t_ents_names:
    "map fst (detype_ents ents) = map fst ents"
    unfolding detype_ents_def by auto

  lemma (in -) t_ents_dis:
    assumes "distinct (map fst ents)"
    shows "distinct (map fst (detype_ents ents))"
    using assms by (metis t_ents_names)

  lemma (in domain_signature2) t_ents_wf:
    shows "(\<forall>(n,T) \<in> set (detype_ents ents). sig2.wf_type T)"
    using ents_detyped sig2.wf_object by fast

(* stuff for formulas later *)

  lemma t_entT_Some:
    shows "map_of ents x \<noteq> None \<longleftrightarrow> map_of (detype_ents ents) x = Some \<omega>"
  proof -
    have "map_of ents x \<noteq> None \<longleftrightarrow> x \<in> fst ` set ents" using map_of_eq_None_iff by metis
    also have "... \<longleftrightarrow> x \<in> fst ` set (detype_ents ents)" using t_ents_names by (metis list.set_map)
    ultimately show ?thesis using map_of_single_val[OF ents_detyped]
      by metis
  qed

  lemma t_entT_None:
    shows "map_of ents x = None \<longleftrightarrow> map_of (detype_ents ents) x = None"
    using t_ents_names list.set_map map_of_eq_None_iff by metis

text \<open> predicate signatures \<open>sig\<close> \<close>

  lemma (in wf_domain_signature2) sig2_Some:
    "sig2.sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set type_preds \<union> set (detype_preds predicates)"
    using t_preds_dis sig2.pred_resolve
    using detyped_predicates_def by simp
    
  lemma (in wf_domain_signature2) type_pred_sig:
    assumes "t \<in> set type_names"
    shows "sig2.sig (pred_for_type t) = Some [\<omega>]"
  proof -
    let ?p = "pred_for_type t"
    from assms obtain Ts where pd: "PredDecl ?p Ts \<in> set type_preds"
      using type_preds_def by auto
    hence "PredDecl ?p Ts \<notin> set (detype_preds predicates)"
      using type_preds_dt_preds_disj by auto
    moreover have "Ts = [\<omega>]" using type_preds_def pd by auto
    ultimately show ?thesis using assms sig2_Some pd by blast
  qed

  lemma (in wf_domain_signature2) detyped_preds_arity:
    assumes "sig p = Some Ts"
    shows "sig2.sig p = Some (replicate (length Ts) \<omega>)"
  proof -
    from assms have "PredDecl p Ts \<in> set predicates "
      by (simp add: sig_Some)
    hence 1: "PredDecl p (replicate (length Ts) \<omega>) \<in> set (detype_preds predicates)"
      using detype_preds_def by force
    hence "PredDecl p (replicate (length Ts) \<omega>) \<notin> set type_preds"
      using type_preds_dt_preds_disj by auto
    thus ?thesis using sig2_Some 1 by auto
  qed

text \<open> function signatures \<open>func_sig\<close> \<close>

  lemma (in wf_domain_signature2) func_sig2_Some:
    "sig2.func_sig f = Some Ts \<longleftrightarrow> FuncDecl f Ts \<in> set (detype_funs functions)"
    using t_funs_dis sig2.func_resolve
    using detyped_functions_def by simp

  lemma (in wf_domain_signature2) detyped_funs_arity:
    assumes "func_sig f = Some Ts"
    shows "sig2.func_sig f = Some (replicate (length Ts) \<omega>)"
  proof -
    from assms have "FuncDecl f Ts \<in> set functions"
      by (simp add: func_sig_Some)
    hence "FuncDecl f (replicate (length Ts) \<omega>) \<in> set (detype_funs functions)"
      using detype_funs_def by force
    thus ?thesis using func_sig2_Some by auto
  qed

text \<open> type maps \<close>

  lemma (in domain_signature2) t_constT_Some: "constT c \<noteq> None \<longleftrightarrow> sig2.constT c = Some \<omega>"
    using t_entT_Some detyped_consts_def
    unfolding sig2.constT_def constT_def by fastforce

  lemma (in domain_signature2) t_constT_None: "constT c = None \<longleftrightarrow> sig2.constT c = None"
    using t_entT_None detyped_consts_def
    unfolding constT_def sig2.constT_def by fastforce

  lemma (in domain_signature2) t_constT_map: "sig2.constT c = map_option (\<lambda>_. \<omega>) (constT c)"
    using t_constT_Some t_constT_None
    by (cases "constT c"; force)

  lemma (in problem_signature2) t_cnsts_objs_names: "map fst all_consts
    = map fst (detype_ents consts @ detype_ents objs)"
    using t_ents_names by (metis map_append)

  lemma (in wf_problem_signature2) t_objm_le_objT:
    "map_of detyped_objs \<subseteq>\<^sub>m sig2.objT"
  proof -
    have "distinct (map fst all_consts)" using wf_P_sig(2)
      by (metis Int_commute distinct_append map_append)
    hence "distinct (map fst (detyped_consts @ detyped_objs))"
      using t_cnsts_objs_names
      unfolding detyped_consts_def detyped_objs_def
      by (metis map_append)
    hence "fst ` set detyped_objs \<inter> fst ` set detyped_consts = {}"
      by auto
    hence "dom (map_of detyped_objs) \<inter> dom sig2.constT = {}" using sig2.constT_def
      by (simp add: dom_map_of_conv_image_fst)
    thus ?thesis using map_add_comm sig2.objT_def
      by (metis map_le_iff_map_add_commute)
  qed

  lemma (in problem_signature2) t_objT_Some: "objT c \<noteq> None \<longleftrightarrow> sig2.objT c = Some \<omega>"
  proof -
    have 1: "\<forall>(x, y) \<in> set (detype_ents consts @ detype_ents objs). y = \<omega>"
      using ents_detyped by fastforce
    have "objT c \<noteq> None \<longleftrightarrow> c \<in> fst ` set all_consts" using t_cnsts_objs_names
      by (metis objT_alt map_of_eq_None_iff)
    also have "... \<longleftrightarrow> c \<in> fst ` set (detype_ents consts @ detype_ents objs)"
      using t_cnsts_objs_names by (metis image_set)
    also have "... \<longleftrightarrow> sig2.objT c = Some \<omega>" using map_of_single_val[OF 1]
      unfolding sig2.objT_alt using detyped_consts_def detyped_objs_def by simp
    ultimately show ?thesis by simp
  qed

  lemma (in problem_signature2) t_objT_Some_r: "\<forall>c. objT c \<noteq> None \<longrightarrow> sig2.objT c = Some \<omega>"
    using t_objT_Some by simp

  lemma (in problem_signature2) t_objT_None: "objT c = None \<longleftrightarrow> sig2.objT c = None"
    unfolding sig2.objT_def objT_def
    unfolding map_add_None
    using t_constT_None
    using detyped_objs_def 
    using t_entT_None[symmetric] by metis
    
   lemma t_tyt_const_Some:
    assumes "ty_term vT (map_of cnsts) (term.CONST x) \<noteq> None"
    shows "ty_term vT' (map_of (detype_ents cnsts)) (term.CONST x) = Some \<omega>"
    using assms t_entT_Some by (metis ty_term.simps(2))

  lemma t_tyt_var_Some:
    assumes "ty_term (map_of vars) cT (term.VAR x) \<noteq> None"
    shows "ty_term (map_of (detype_ents vars)) cT' (term.VAR x) = Some \<omega>"
    using assms t_entT_Some by (metis ty_term.simps(1))

  lemma t_tyt_Some:
    assumes "ty_term (map_of vars) (map_of cnsts) e \<noteq> None"
    shows "ty_term (map_of (detype_ents vars)) (map_of (detype_ents cnsts)) e = Some \<omega>"
    using assms by (induction e) (metis t_entT_Some ty_term.simps)+

  lemma t_tyt_None:
    assumes "ty_term (map_of vars) (map_of cnsts) e = None"
    shows "ty_term (map_of (detype_ents vars)) (map_of (detype_ents cnsts)) e = None"
    using assms by (induction e) (metis t_entT_None ty_term.simps)+

  (* See \<open>t_ac_tyt\<close> for where the assumption comes from. *)
  lemma (in domain_signature2) t_tyt_params:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "list_all2 (is_of_type tyt) params Ts"
    shows "list_all2 (sig2.is_of_type tyt2) params (replicate (length Ts) \<omega>)"
  proof -
    from assms(2) have
      ls: "length params = length Ts" and
      "\<forall>i < length params. is_of_type tyt (params !i) (Ts ! i)"
      by (simp_all add: list_all2_nthD list_all2_lengthD)

    hence "\<forall>i < length params. tyt (params ! i) \<noteq> None" using is_of_type_def
      by (metis option.simps(4))
    hence 2: "\<forall>i < length params. tyt2 (params ! i) = Some \<omega>" using assms(1) by simp
    hence "\<forall>i < length params. (case tyt2 (params ! i) of Some t \<Rightarrow> sig2.of_type t \<omega>)"
      by simp
    hence "\<forall>i < length params. sig2.is_of_type tyt2 (params ! i) \<omega>"
      using sig2.is_of_type_def 2 by fastforce
    thus ?thesis using ls
      by (simp add: list_all2_conv_all_nth)
  qed

  text \<open> formulas \<close>

  lemma (in wf_domain_signature2) t_primitive_numeric_expression_wf:
      assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
            "wf_primitive_numeric_expression tyt p"
          shows "sig2.wf_primitive_numeric_expression tyt2 p"
  proof -
    obtain f params where p[simp]: "p = PNE f params" by (cases p)
    obtain Ts where sigp: "func_sig f = Some Ts" using assms by fastforce
    then have 1: "list_all2 (is_of_type tyt) params Ts" using assms by simp

    let ?os = "replicate (length Ts) \<omega>"
    from assms 1 have "list_all2 (sig2.is_of_type tyt2) params ?os"
      by (simp add: t_tyt_params)
    moreover have "sig2.func_sig f = Some ?os" using sigp by (simp add: detyped_funs_arity)
    ultimately show ?thesis by simp
  qed

  lemma (in wf_domain_signature2) t_numeric_expression_wf:
      assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
            "wf_numeric_expression tyt n"
          shows "sig2.wf_numeric_expression tyt2 n"
    using assms t_primitive_numeric_expression_wf co_numeric_expression_wf by blast

  lemma (in wf_domain_signature2) t_atom_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
          "wf_atom tyt a"
    shows "sig2.wf_atom tyt2 a"
  proof (cases a)
    case [simp]: (predAtm p params)
    (* these follow from the definition of wf_pred_atom *)
    from assms obtain Ts where sigp: "sig p = Some Ts" by fastforce
    with assms have 1: "list_all2 (is_of_type tyt) params Ts" by simp

    let ?os = "replicate (length Ts) \<omega>"
    from assms 1 have "list_all2 (sig2.is_of_type tyt2) params ?os"
      by (simp add: t_tyt_params)
    moreover have "sig2.sig p = Some ?os" using sigp by (simp add: detyped_preds_arity)

    ultimately show ?thesis by simp
  qed (use assms t_numeric_expression_wf in auto)

  lemma (in wf_domain_signature2) t_fmla_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_fmla tyt \<phi>"
    shows "sig2.wf_fmla tyt2 \<phi>"
    using assms by (auto intro: t_atom_wf co_fmla_wf)

  lemma (in wf_problem_signature2) t_func_assign_wf:
      assumes "wf_func_assign \<phi>"
      shows "sig2.wf_func_assign \<phi>"
    using assms
    apply (induction \<phi> rule: wf_func_assign.induct)
    using t_primitive_numeric_expression_wf[OF t_objT_Some_r]
    by simp_all

  lemma (in wf_domain_signature2) t_eff_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_effect tyt \<epsilon>"
    shows "sig2.wf_effect tyt2 \<epsilon>"
    using assms by (auto intro: t_atom_wf t_primitive_numeric_expression_wf co_effect_wf)

  lemma (in wf_domain_signature2) t_num_eff_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_numeric_effect tyt \<epsilon>"
    shows "sig2.wf_numeric_effect tyt2 \<epsilon>"
    using assms by (auto intro: t_primitive_numeric_expression_wf co_numeric_effect_wf)

text \<open> detype ac \<close>

  lemma (in ast_classical_domain) ac_params_detyped:
    "\<forall>ac \<in> set (actions D2). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>"
    using ents_detyped by fastforce

  lemma (in wf_ast_classical_domain) t_acs_dis:
    "distinct (map ac_name (map detype_classical_ac (actions D)))"
  proof -
    have "ac_name (detype_classical_ac ac) = ac_name ac" for ac
      by (cases ac rule: ast_classical_action_schema_cases_unfold) simp
    hence "map ac_name (map detype_classical_ac acs) = map ac_name acs" for acs
      by simp
    thus ?thesis using wf_D by metis
  qed

  lemma (in domain_signature2) t_ac_tyt:
    assumes "ty_term (map_of (ac_params a)) constT x \<noteq> None"
    shows "ty_term (map_of (ac_params (detype_classical_ac a))) sig2.constT x = Some \<omega>"
    using assms t_tyt_Some sig2.constT_def domain_signature.constT_def detyped_consts_def 
    by simp

  lemma params_ts_exist: (* somehow this isn't trivial for the solver *)
    assumes "wf_action_params a" "(n, Either ts) \<in> set (ac_params a)"
    shows "set ts \<subseteq> set type_names"
    using assms wf_action_params_def wf_type_iff_listed 
    by blast

  lemma (in wf_domain_signature2) type_atom_wf:
    assumes "t \<in> set type_names" "tyt x = Some \<omega>"
    shows "sig2.wf_fmla tyt (type_atom x t)"
  proof -
    from assms(1) have "sig2.sig (pred_for_type t) = Some [\<omega>]" by (rule type_pred_sig)
    hence "sig2.wf_fmla tyt (Atom (predAtm (pred_for_type t) [x]))"
      using assms(2) sig2.of_type_refl sig2.is_of_type_def by fastforce
    thus ?thesis by simp
  qed

  text \<open>
  1. tyt p = Some T
  2. tyt2 p = Some \<omega>
  for every type in T, the type_cond is wf:
    - the corresponding type_pred exists and has signature [\<omega>]
    - the arguments are just the variable [v], due to 2 with signatures [\<omega>]
  \<close>

  (* instead of sig2.ac_tyt, we could use the same with an arbitrary value for consT *)
  lemma (in wf_domain_signature2) type_precond_wf:
    assumes "wf_action_params a" "p \<in> set (ac_params a)"
    shows "sig2.wf_fmla
      (sig2.ac_tyt (detype_classical_ac a))
      (type_precond p)"
  proof -
    (* type_precond.cases? *)
    obtain n ts where p: "p = (n, Either ts)"
      using type_precond.cases .
    let ?tyt = "ac_tyt a"
    let ?tyt2 = "sig2.ac_tyt (detype_classical_ac a)"
    let ?v = "term.VAR n"

    (* Not generally "Some (Either ts)", unless we assume wf_classical_action_schema,
       because param names may not be distinct. *)
    have "?tyt ?v \<noteq> None" using assms(2) p
      using ac_tyt_def weak_map_of_SomeI by fastforce
    hence "?tyt2 ?v = Some \<omega>" using sig2.t_tyt_var_Some 
      unfolding sig2.ac_tyt_def ac_tyt_def by simp
    hence "\<forall>t \<in> set ts. sig2.wf_fmla ?tyt2 (type_atom ?v t)"
      using assms p type_atom_wf[where tyt = ?tyt2] params_ts_exist by blast
    hence "\<forall>\<phi> \<in> set (map (type_atom ?v) ts). sig2.wf_fmla ?tyt2 \<phi>"
      by simp
    hence "sig2.wf_fmla ?tyt2 (type_precond (n, Either ts))"
      using sig2.bigor_wf unfolding type_precond.simps by blast
    thus ?thesis using p by simp
  qed

  lemma (in wf_domain_signature2) t_param_precond_wf:
    assumes "wf_action_params a"
    shows "sig2.wf_fmla
    (sig2.ac_tyt (detype_classical_ac a))
    (param_precond (ac_params a))"
  proof -
    let ?tyt2 = "sig2.ac_tyt (detype_classical_ac a)"
    have "\<forall>p \<in> set (ac_params a). sig2.wf_fmla ?tyt2 (type_precond p)"
      using assms type_precond_wf by simp
    hence "\<forall>\<phi> \<in> set (map type_precond (ac_params a)). sig2.wf_fmla ?tyt2 \<phi>" by simp
    thus ?thesis using sig2.bigand_wf param_precond_def by metis
  qed

  text \<open>Three conditions: 1. distinct parameter names, 2. wf precondition, 3. wf effect\<close>
  lemma (in restrict_classical_domain2) t_ac_wf:
    assumes "a \<in> set (actions D)"
    shows "d2.wf_classical_action_schema (detype_classical_ac a)"
  proof -
    let ?a2 = "detype_classical_ac a"
    let ?tyt = "ty_term (map_of (ac_params a)) constT"
    let ?tyt2 = "ty_term (map_of (ac_params (detype_classical_ac a))) d2.constT"

    have tyt_om: "\<forall>x. ?tyt x \<noteq> None \<longrightarrow> ?tyt2 x = Some \<omega>" using t_ac_tyt by simp
    from assms have wfa: "wf_classical_action_schema a" using wf_D by presburger

    from assms have "distinct (map fst (ac_params a))" using wfa wf_classical_action_schema_alt by metis
    hence c1: "distinct (map fst (ac_params ?a2))" using t_ents_dis by auto

    from assms have "wf_fmla ?tyt (ac_pre a)" using wfa 
      unfolding wf_classical_action_schema_alt ac_tyt_def by simp 
    hence c2b: "d2.wf_fmla ?tyt2 (ac_pre a)" unfolding ac_tyt_def 
      using t_fmla_wf tyt_om detype_classical_dom_def by auto 
    have "wf_action_params a" using restrict_D assms by metis
    note c2a = t_param_precond_wf[OF this]
    from c2a c2b have c2: "sig2.wf_fmla ?tyt2 (ac_pre ?a2)"
      using domain_signature.ac_tyt_def by auto

    from assms have wfeff: "wf_effect ?tyt (ac_eff a)" using wfa wf_classical_action_schema_alt 
      using ac_tyt_def by force
    hence "d2.wf_effect ?tyt2 (ac_eff a)" by (rule t_eff_wf[OF tyt_om])
    hence c3: "d2.wf_effect ?tyt2 (ac_eff ?a2)" by simp

    from c1 c2 c3 show ?thesis unfolding d2.wf_classical_action_schema_alt 
      using domain_signature.ac_tyt_def by presburger
  qed

  lemma (in restrict_classical_domain2) t_acs_wf:
    shows "\<forall>a \<in> set (map detype_classical_ac (actions D)). d2.wf_classical_action_schema a"
    using detype_classical_dom_def wf_D t_ac_wf by simp

  text \<open> supertype_facts (init) \<close>

  lemma superfacts_for_cond:
    assumes "single_type T"
    shows "supertype_facts_for (n, T) =
      map (type_atom n) (supertypes_of (get_t T))"
    using assms by (auto intro: type_decomp_1)
  
  lemma (in wf_domain_signature) supertypes_listed:
    assumes "t \<in> set type_names"
    shows "set (supertypes_of t) \<subseteq> set type_names"
  proof -
    have "set (supertypes_of t) \<subseteq> insert t (snd ` set ty_decl)"
      using reachable_set by simp
    also have "... \<subseteq> insert t (set type_names)"
      using  wf_D_sig wf_types_def type_names_set by auto
    also have "... \<subseteq> set type_names" using assms by simp
  
    ultimately show ?thesis by blast
  qed

  (* unfolding supertype_facts and supertype_facts_for, employing the fact that every const
     has a singular type. *)
  lemma (in restrict_problem_signature) superfacts_unfolded:
    "supertype_facts all_consts =
      concat (map (\<lambda>(n, T). map (type_atom n) (supertypes_of (get_t T))) all_consts)"
  proof -
    define sffor :: "object \<times> type \<Rightarrow> object atom formula list"
      where "sffor \<equiv> (\<lambda>(n, T). map (type_atom n) (supertypes_of (get_t T)))"
    have "\<forall>ob \<in> set all_consts. supertype_facts_for ob = sffor ob"
      using single_t_consts superfacts_for_cond sffor_def by fast
    hence "supertype_facts all_consts = concat (map sffor all_consts)"
      unfolding supertype_facts_def using map_eq_conv by (metis (mono_tags, lifting))
    thus ?thesis unfolding sffor_def by simp
  qed

  text \<open>Every supertype fact is a plain predicate atom — never an equality, numeric, or
    numeric-initialisation atom — so it survives \<open>is_predAtom\<close> filtering and is dropped by
    \<open>is_numericInitializationAtom\<close> filtering. We state these in \<open>restrict_problem_signature\<close>
    so that \<open>superfacts_unfolded\<close> sidesteps the \<open>undefined\<close> branch of \<open>supertype_facts_for\<close>.\<close>
  lemma (in restrict_problem_signature) supertype_facts_predAtom:
    "\<forall>\<phi> \<in> set (supertype_facts all_consts). is_predAtom \<phi>"
    using superfacts_unfolded by auto

  lemma (in restrict_problem_signature) supertype_facts_not_numInit:
    "\<forall>\<phi> \<in> set (supertype_facts all_consts). \<not> is_numericInitializationAtom \<phi>"
    using superfacts_unfolded by auto

  text \<open>Relating \<open>p2.I\<close> to \<open>I\<close>: detyping adds the supertype facts to the predicate-atom
    component of the initial world model, and leaves the numeric component unchanged
    (because supertype facts are predicate atoms, not numeric-initialisation atoms).\<close>
  lemma (in restrict_classical_problem2) p2_I_eq:
    "p2.I = (sf_substate \<union> fst I, snd I)"
  proof -
    have sf_pa: "\<forall>\<phi> \<in> sf_substate. is_predAtom \<phi>"
      using supertype_facts_predAtom by simp
    have sf_nn: "\<forall>\<phi> \<in> sf_substate. \<not> is_numericInitializationAtom \<phi>"
      using supertype_facts_not_numInit by simp
    have init_split: "set (init P2) = sf_substate \<union> set (init P)" by simp
    have fst_eq: "fst p2.I = sf_substate \<union> fst I"
      unfolding p2.I_def I_def using sf_pa init_split by auto
    have "distinct (init P)" using wf_P by simp
    hence filter_init2: "filter is_numericInitializationAtom (init detype_classical_prob) = 
        filter is_numericInitializationAtom (init P)"
      unfolding detype_classical_prob_sel
      apply (subst remdups_filter[symmetric])
      apply (subst filter_append)
      using supertype_facts_not_numInit by simp
    hence snd_eq: "snd p2.I = snd I"
      unfolding p2.I_def I_def 
      unfolding snd_conv by simp
    from fst_eq snd_eq show ?thesis by (cases "p2.I") simp
  qed

  (* I could do "sig2.wf_world_model (set (supertype_facts_for ent))"
     but it doesn't make it more readable imo. *)
  lemma (in wf_restrict_problem_signature2) super_facts_for_wf:
    assumes "(n, T) \<in> set all_consts"
    shows "\<forall>\<phi> \<in> set (supertype_facts_for (n, T)). sig2.wf_fmla_atom sig2.objT \<phi>"
  proof -
    from assms have "single_type T" using single_t_consts by auto
    then obtain t where t: "T = Either [t]"
        by (metis type_decomp_1)
    have "wf_type T" using assms wf_P_sig wf_D_sig by auto
    hence "t \<in> set type_names" using wf_type_iff_listed t by auto
    hence st_ss: "set (supertypes_of t) \<subseteq> set type_names"
      using supertypes_listed by simp
    have om: "sig2.objT n = Some \<omega>"
      using assms by (metis t_objT_Some objT_Some option.distinct(1))

    have "\<forall>t\<in> set (supertypes_of t). sig2.wf_fmla sig2.objT (type_atom n t)"
      using type_atom_wf[where tyt = sig2.objT] om st_ss by auto
    hence "\<forall>\<phi> \<in> set (map (type_atom n) (supertypes_of t)). sig2.wf_fmla sig2.objT \<phi>"
      by simp
    thus ?thesis using superfacts_for_cond t by simp
  qed

  lemma (in wf_restrict_problem_signature2) super_facts_wf:
      shows "sig2.wf_world_model (sf_substate, x)"
      using super_facts_for_wf supertype_facts_def by auto
  
  lemma (in wf_problem_signature2) t_wm_wf:
    assumes "wf_world_model M" shows "sig2.wf_world_model M"
  proof -
    have "wf_atom objT a \<longrightarrow> sig2.wf_atom sig2.objT a" for a
      using t_atom_wf t_objT_Some_r by auto
    with assms co_wm_wf show ?thesis by metis
  qed

  lemma (in restrict_classical_problem2) t_I_wf:
    "p2.wf_world_model p2.I"
    unfolding p2_I_eq
    using wf_I[THEN t_wm_wf] super_facts_wf by auto

end

subsection \<open>Detyping\<close>

context ast_classical_domain begin

  text \<open>The detyped signature/problem-signature satisfies \<open>typeless_domain_signature\<close> /
    \<open>typeless_problem_signature\<close>: \<open>ty_decl\<close> is empty (it's literally \<open>Nil\<close> by construction)
    and every predicate / function argument and every const/obj type is \<open>\<omega>\<close>.\<close>
  lemma (in domain_signature2) typeless_dom_sig:
    "sig2.typeless_domain_signature"
    unfolding sig2.typeless_domain_signature_def
    using preds_detyped funcs_detyped consts_detyped by blast

  lemma (in problem_signature2) typeless_prob_sig:
    "sig2.typeless_problem_signature"
    unfolding sig2.typeless_problem_signature_def
    using typeless_dom_sig objs_detyped by simp

  theorem (in ast_classical_domain2) dom_detyped:
    "d2.typeless_classical_domain"
    unfolding d2.typeless_classical_domain_def 
    using typeless_dom_sig ac_params_detyped 
    by simp

  theorem (in ast_classical_problem2) prob_detyped:
    "p2.typeless_classical_problem"
    unfolding p2.typeless_classical_problem_def 
    using dom_detyped objs_detyped by simp

  lemma (in wf_ast_classical_problem2) t_init_dis:
    "distinct (init P2)"
    unfolding detype_classical_prob_def
    by simp

  lemma (in restrict_classical_problem2) t_init_wf:
    "\<forall>f\<in>set (init detype_classical_prob). p2.wf_fmla_atom p2.objT f \<or> p2.wf_func_assign f"
  proof -
    have "\<And>f. f \<in> sf_substate \<Longrightarrow> p2.wf_fmla_atom p2.objT f \<or> p2.wf_func_assign f"
      using super_facts_for_wf unfolding supertype_facts_def
      by auto
    moreover 
    have "\<And>f. f \<in> set (init P) \<Longrightarrow> p2.wf_fmla_atom p2.objT f \<or> p2.wf_func_assign f"
      using wf_P(4) t_fmla_wf[OF t_objT_Some_r] t_func_assign_wf 
      unfolding wf_fmla_atom_alt p2.wf_fmla_atom_alt by blast
    ultimately
    show ?thesis by auto
  qed

  lemma (in wf_ast_classical_problem2) t_goal_wf:
    "p2.wf_fmla p2.objT (goal P2)"
    using t_fmla_wf[OF t_objT_Some_r] wf_P(5) by auto

  text \<open>The detyped signature is well-formed: predicates, functions, consts, and objects are
    all distinct (inherited from the well-formedness of the original signature, since detyping
    preserves names) and all argument/value types are \<open>\<omega>\<close>, which is trivially well-formed.\<close>
  lemma (in wf_domain_signature2) detype_domain_signature_wf:
    "sig2.wf_domain_signature"
    unfolding sig2.wf_domain_signature_def
    using t_preds_dis t_preds_wf t_funs_dis t_funs_wf
          t_ents_dis[OF wf_D_sig(6)] t_ents_wf
    by (simp add: detyped_consts_def list_all_iff sig2.wf_types_def)

  lemma (in wf_problem_signature2) detype_problem_signature_wf:
    "sig2.wf_problem_signature"
    unfolding sig2.wf_problem_signature_def
    using detype_domain_signature_wf t_ents_wf
          t_ents_dis[OF wf_P_sig(2)[unfolded distinct_append, THEN conjunct1]]
          (* the joint distinctness on objs ++ consts; both lists are detyped via t_ents_names *)
          wf_P_sig
    by (simp add: detyped_objs_def detyped_consts_def t_ents_names list_all_iff)

  theorem (in restrict_classical_domain2) detype_classical_dom_wf:
    shows "d2.wf_classical_domain"
    unfolding d2.wf_classical_domain_def 
    unfolding detype_classical_dom_def
    unfolding ast_classical_domain.wf_classical_domain_def
    using t_acs_dis t_acs_wf detype_domain_signature_wf by auto

  theorem (in restrict_classical_problem2) detype_classical_prob_wf:
    shows "p2.wf_classical_problem"
    unfolding p2.wf_classical_problem_def
    using detype_classical_dom_wf detype_problem_signature_wf
    using t_init_dis t_goal_wf t_init_wf by blast
end

sublocale restrict_classical_domain2 \<subseteq> d2_wf: wf_ast_classical_domain D2
  using detype_classical_dom_wf wf_ast_classical_domain.intro by simp

find_consts name: "res_inst"

text \<open>Upgrade the existing \<open>p2 : ast_classical_problem P2\<close> interpretation to
  \<open>wf_ast_classical_problem P2\<close>. We cannot reuse the \<open>p2\<close> qualifier here without
  triggering a duplicate \<open>p2.res_inst_graph\<close> declaration from \<open>simple_action_instantiations\<close>,
  so the new interpretation goes under a fresh qualifier \<open>p2_wf\<close>. The \<open>rewrites\<close> clauses
  below identify \<open>p2_wf.X\<close> with the existing \<open>p2.X\<close> for every signature/domain/problem-level
  constant, so downstream proofs never need to switch namespaces.\<close>
sublocale restrict_classical_problem2 \<subseteq> p2_wf: wf_ast_classical_problem P2
  using detype_classical_prob_wf 
  by (auto intro: wf_ast_classical_problem.intro
      simp: wf_ast_classical_problem_def)


end
