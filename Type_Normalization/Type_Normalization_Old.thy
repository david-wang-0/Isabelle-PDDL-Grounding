theory Type_Normalization_Old
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Normalization_Definitions Graph_Funs String_Utils
begin

subsection \<open>Type Normalization\<close>

text \<open>Even before performing normalization, we place a two restrictions on the input PDDL task.
* Restrict consts/objects to primitive types only. This greatly simplifies type normalization.
  I couldn't find any PDDL planning task that makes use of constants with Either types, anyway.
* Ensure that action signature types are well-formed. This not being ensured in wf_domain may be an
  oversight. In practice, PDDL domains should adhere to this, anyway.\<close>

context domain_signature
begin

  (* TODO: maybe better name, e.g. "____is_Car" *)
  (* TODO: implement prefix or suffix *)
  definition pred_for_type :: "name \<Rightarrow> predicate" where
      "pred_for_type t \<equiv> Pred t"
  
  fun type_pred :: "name \<Rightarrow> predicate_decl" where
      "type_pred t = PredDecl (pred_for_type t) [\<omega>]"

  (* if multiple inheritance exists, there are duplicates *)
  abbreviation "type_names \<equiv> remdups (STR ''object'' # map fst ty_decl)"

  definition type_preds :: "predicate_decl list" where
    "type_preds \<equiv> map type_pred type_names"

  abbreviation supertypes_of :: "name \<Rightarrow> name list" where
    "supertypes_of \<equiv> reachable_nodes ty_decl"

  abbreviation (input) type_predatm :: "'a \<Rightarrow> name \<Rightarrow> 'a atom" where
    "type_predatm x t \<equiv> predAtm (pred_for_type t) [x]"

  fun type_atom :: "'a \<Rightarrow> name \<Rightarrow> 'a atom formula" where
    "type_atom x t = Atom (type_predatm x t)"

  fun type_precond :: "variable \<times> type \<Rightarrow> term atom formula" where
    "type_precond (v, (Either ts)) = \<^bold>\<Or> (map (type_atom (term.VAR v)) ts)"

  definition param_precond :: "(variable \<times> type) list \<Rightarrow> term atom formula" where
    "param_precond params = \<^bold>\<And> (map type_precond params)"

  abbreviation (in -) detype_pred :: "predicate_decl \<Rightarrow> predicate_decl" where
    "detype_pred p \<equiv> PredDecl (pred p) (replicate (length (predicate_decl.argTs p)) \<omega>)"

  definition detype_preds :: "predicate_decl list \<Rightarrow> predicate_decl list" where
    "detype_preds preds \<equiv> map detype_pred preds"

  fun (in -) detype_fun :: "function_decl \<Rightarrow> function_decl" where
    "detype_fun (FuncDecl n as) = FuncDecl n (replicate (length as) \<omega>)"

  definition  detype_funs :: "function_decl list \<Rightarrow> function_decl list" where
    "detype_funs funs \<equiv> map detype_fun funs"

  fun (in -) detype_ent :: "('ent \<times> type) \<Rightarrow> ('ent \<times> type)" where
    "detype_ent (n, T) = (n, \<omega>)"

  definition (in -) detype_ents :: "('ent \<times> type) list \<Rightarrow> ('ent \<times> type) list" where
    "detype_ents params \<equiv> map detype_ent params"

  fun (in -) detype_action_head::"ast_action_head \<Rightarrow> ast_action_head" where
    "detype_action_head (ActionHead n params) = ActionHead n (detype_ents params)"

  fun detype_simple_action_body::"ast_action_head \<Rightarrow> ast_simple_action_body \<Rightarrow> ast_simple_action_body" where
    "detype_simple_action_body h (SimpleActionBody pre eff) = SimpleActionBody (param_precond (parameters h) \<^bold>\<and> pre) eff" 

  primrec detype_classical_ac :: "ast_classical_action_schema \<Rightarrow> ast_classical_action_schema" where
    "detype_classical_ac (SimpleActionSchema h b) = SimpleActionSchema (detype_action_head h) (detype_simple_action_body h b)"


  text \<open>This only works for single types on purpose.\<close>
  fun supertype_facts_for :: "(object \<times> type) \<Rightarrow> object atom formula list" where
    "supertype_facts_for (n, Either [t]) =
      map (type_atom n) (supertypes_of t)" |
    "supertype_facts_for (n, _) = undefined"

  definition supertype_facts :: "(object \<times> type) list \<Rightarrow> object atom formula list" where
    "supertype_facts objs \<equiv> concat (map supertype_facts_for objs)"
end

definition (in ast_classical_domain) detype_classical_dom :: "ast_classical_domain" where
"detype_classical_dom \<equiv>
  Domain
    []
    (type_preds @ detype_preds (predicates D))
    (detype_funs (functions D))
    (detype_ents (consts D))
    (map detype_classical_ac (actions D))"

(* TODO remove remdups lmao *)
definition (in ast_classical_problem) detype_classical_prob :: "ast_classical_problem" where
"detype_classical_prob \<equiv> Problem
    detype_classical_dom
    (detype_ents (objects P))
    (remdups (supertype_facts (all_consts) @ (init P)))
    (goal P)"

(* typeless_dom and prob taken from here *)

(* This will be referenced a lot in proofs. *)
abbreviation (in problem_signature) "sf_substate \<equiv> set (supertype_facts all_consts)"

(* ------------------------------------- PROOFS ------------------------------------------------- *)
section \<open>Type Normalization Proofs\<close>

text \<open>This is only to simplify the syntax. So I can just do
   \<open>d2.some_function\<close> instead of \<open>ast_classical_domain.some_function detype_classical_dom\<close>.\<close>
abbreviation (in ast_classical_domain) (input) "D2 \<equiv> detype_classical_dom"
abbreviation (in ast_classical_problem) (input) "P2 \<equiv> detype_classical_prob"

locale ast_classical_domain2 = ast_classical_domain
sublocale ast_classical_domain2 \<subseteq> d2: ast_classical_domain D2 .

locale wf_ast_classical_domain2 = wf_ast_classical_domain
sublocale wf_ast_classical_domain2 \<subseteq> d2: ast_classical_domain D2 .
sublocale wf_ast_classical_domain2 \<subseteq> ast_classical_domain2 .

locale restrict_domain2 = restrict_domain
sublocale restrict_domain2 \<subseteq> d2 : ast_classical_domain D2 .
sublocale restrict_domain2 \<subseteq> wf_ast_classical_domain2
  by unfold_locales

locale ast_classical_problem2 = ast_classical_problem
sublocale ast_classical_problem2 \<subseteq> p2: ast_classical_problem P2 .
sublocale ast_classical_problem2 \<subseteq> ast_classical_domain2 D .

locale wf_ast_classical_problem2 = wf_ast_classical_problem
sublocale wf_ast_classical_problem2 \<subseteq> p2 : ast_classical_problem P2.
sublocale wf_ast_classical_problem2 \<subseteq> ast_classical_problem2 .
sublocale wf_ast_classical_problem2 \<subseteq> wf_ast_classical_domain2 D
  by unfold_locales

locale restrict_problem2 = restrict_problem
sublocale restrict_problem2 \<subseteq> p2 : ast_classical_problem P2 .
sublocale restrict_problem2 \<subseteq> wf_ast_classical_problem2
  by unfold_locales
sublocale restrict_problem2 \<subseteq> restrict_domain2 D
  by unfold_locales

(* Note (David): Extend a locale loc with a new name loc2 and then in loc2 obtain a new instance of loc
  named l2 using the constants L2, which are present in loc *)

sublocale wf_ast_classical_problem \<subseteq> ast_classical_problem
  by (unfold_locales)



text \<open> Alternate/simplified definitions\<close>

lemma single_type_alt: "single_type T \<longleftrightarrow> length (primitives T) = 1"
  by (cases T; simp)

lemma type_decomp_1: assumes "single_type T" obtains t where "T = Either [t]"
  using assms Misc.list_decomp_1 by (cases T; auto)

lemma (in ast_classical_domain) type_precond_alt: "type_precond p =
  \<^bold>\<Or> (map (type_atom (term.VAR (fst p))) (primitives (snd p)))"
  by (cases p; cases "snd p"; simp)

lemma detype_ent_alt: "detype_ent x = (fst x, \<omega>)"
  by (cases x; simp)

lemma (in ast_classical_domain) detype_classical_ac_alt: "detype_classical_ac ac = Action_Schema
  (ac_name ac) (detype_ents (ac_params ac)) (param_precond (ac_params ac) \<^bold>\<and> (ac_pre ac)) (ac_eff ac)"
  by (cases ac; simp)

lemma (in ast_classical_domain) detype_classical_ac_sel [simp]:
  "ac_name (detype_classical_ac ac) = ac_name ac"
  "ac_params (detype_classical_ac ac) = detype_ents (ac_params ac)"
  "ac_pre (detype_classical_ac ac) = param_precond (ac_params ac) \<^bold>\<and> (ac_pre ac)"
  "ac_eff (detype_classical_ac ac) = ac_eff ac"
  by (cases ac) (simp_all add: detype_classical_ac_alt)

lemma (in ast_classical_domain) detype_classical_dom_sel [simp]:
  "types D2 = []"
  "predicates D2 = type_preds @ detype_preds (predicates D)"
  "consts D2 = detype_ents (consts D)"
  "actions D2 = map detype_classical_ac (actions D)"
  using ast_classical_domain.detype_classical_dom_def by simp_all

lemma (in ast_classical_problem) detype_classical_prob_sel [simp]:
  "domain P2 = D2"
  "objects P2 = detype_ents (objects P)"
  "init P2 = remdups (supertype_facts (all_consts) @ (init P))"
  "goal P2 = goal P"
  using ast_classical_problem.detype_classical_prob_def by simp_all

(* just restrict_dom unfolded *)
lemma (in restrict_domain) restrict_D: "single_types (consts D)" "list_all1 wf_action_params (actions D)"
  using restrict_dom restrict_dom_def by auto

(* just restrict_prob unfolded *)
lemma (in restrict_problem) restrict_P: "single_types (objects P)"
  using restrict_prob restrict_prob_def by auto

lemma (in restrict_problem) single_t_consts: "single_types (all_consts)"
  using restrict_D(1) restrict_P(1) by auto

text \<open> type system \<close>

lemma (in wf_ast_classical_problem) objT_Some: "(n, T) \<in> set (all_consts) \<longleftrightarrow> objT n = Some T"
proof -
  have "distinct (map fst (all_consts))"
    using wf_P(1) by auto
  thus ?thesis using objT_alt
    by (metis map_of_eq_Some_iff)
qed

lemma (in -) wf_object: "ast_classical_domain.wf_type d \<omega>"
  unfolding ast_classical_domain.wf_type.simps by simp

context ast_classical_domain
begin

text \<open> type_names \<close>
  
lemma (in ast_classical_domain) type_names_set[simp]: "set type_names = insert ''object'' (fst ` set (types D))"
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
    using pred_for_type_def inj_def by force

  lemma pred_for_type_dis:
    assumes "distinct ts"
    shows "distinct (map pred_for_type ts)"
    using assms pred_for_type_inj distinct_map subset_inj_on by blast

text \<open> type_preds \<close>

  lemma type_preds_dis:
    "distinct (map pred type_preds)"
    using pred_for_type_dis type_preds_ids by force

  lemma type_pred_notin: "pred_for_type t \<notin> pred ` set (predicates D)"
  proof -
    have "predicate.name (pred_for_type t) \<notin> set pred_names"
      using safe_prefix_correct predicate.sel pred_for_type_def by presburger
    thus ?thesis by force
  qed

text \<open> detyped preds \<close>

  lemma preds_detyped:
    "\<forall>p \<in> set (predicates D2). \<forall>T \<in> set (argTs p). T = \<omega>"
    using type_preds_def detype_preds_def by auto

  lemma (in -) dt_preds_ids:
    "map pred (detype_preds ps) = map pred ps"
    using detype_preds_def by simp

  lemma type_preds_dt_preds_disj:
    "pred ` set type_preds \<inter> pred ` set (detype_preds (predicates D)) = {}"
  proof -
    have "pred ` set type_preds = pred_for_type ` set type_names"
      by (metis type_preds_ids list.set_map)
    moreover have "pred ` set (detype_preds (predicates D)) = pred ` set (predicates D)"
      using dt_preds_ids by (metis list.set_map)
    ultimately show ?thesis using type_pred_notin
      by (metis disjoint_iff_not_equal type_pred_refs_type)
  qed

  lemma (in wf_ast_classical_domain) t_preds_dis:
    shows "distinct (map pred (predicates D2))"
  proof -
    (* Predicate names are unique because the original predicate names are unchanged
       and the additional predicate names are unique (based on unique type names)
       and distinct from the original predicates. *)

    have "distinct (map pred (detype_preds (predicates D)))"
      using dt_preds_ids wf_D(2) by simp
    hence "distinct (map pred (type_preds @ detype_preds (predicates D)))"
      using type_preds_dt_preds_disj type_preds_dis by simp
    thus ?thesis by simp
  qed

  (* here, _alt definition is actually needed *)
  lemma (in ast_classical_domain2) t_preds_wf:
    "list_all1 d2.wf_predicate_decl (predicates D2)"
    using preds_detyped wf_object d2.wf_predicate_decl_alt by metis

text \<open> detype ents \<close>

  lemma (in -) ents_detyped: "\<forall>(n, T) \<in> set (detype_ents ents). T = \<omega>"
    by (auto simp add: detype_ents_def)

  lemma (in -) t_ents_names:
    "map fst (detype_ents ents) = map fst ents"
    unfolding detype_ents_def by auto

  lemma (in -) t_ents_dis:
    assumes "distinct (map fst ents)"
    shows "distinct (map fst (detype_ents ents))"
    using assms by (metis t_ents_names)

  lemma (in ast_classical_domain2) t_ents_wf:
    shows "(\<forall>(n,T) \<in> set (detype_ents ents). d2.wf_type T)"
    using ents_detyped wf_object by fast

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

  lemma (in wf_ast_classical_domain2) sig2_Some:
    "d2.sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set type_preds \<union> set (detype_preds (predicates D))"
    using t_preds_dis d2.pred_resolve
    by (metis detype_classical_dom_sel(2) set_union_code)

  lemma (in wf_ast_classical_domain2) type_pred_sig:
    assumes "t \<in> set type_names"
    shows "d2.sig (pred_for_type t) = Some [\<omega>]"
  proof -
    let ?p = "pred_for_type t"
    from assms obtain Ts where pd: "PredDecl ?p Ts \<in> set type_preds"
      using type_preds_def by auto
    hence "PredDecl ?p Ts \<notin> set (detype_preds (predicates D))"
      using type_preds_dt_preds_disj by auto
    moreover have "Ts = [\<omega>]" using type_preds_def pd by auto
    ultimately show ?thesis using assms sig2_Some pd by blast
  qed


  lemma (in wf_ast_classical_domain2) detyped_preds_arity:
    assumes "sig p = Some Ts"
    shows "d2.sig p = Some (replicate (length Ts) \<omega>)"
  proof -
    from assms have "PredDecl p Ts \<in> set (predicates D)"
      by (simp add: sig_Some)
    hence 1: "PredDecl p (replicate (length Ts) \<omega>) \<in> set (detype_preds (predicates D))"
      using detype_preds_def by force
    hence "PredDecl p (replicate (length Ts) \<omega>) \<notin> set type_preds"
      using type_preds_dt_preds_disj by auto
    thus ?thesis using sig2_Some 1 by auto
  qed

text \<open> type maps \<close>

  lemma (in ast_classical_domain2) t_constT_Some: "constT c \<noteq> None \<longleftrightarrow> d2.constT c = Some \<omega>"
    using t_entT_Some ast_classical_domain.constT_def detype_classical_dom_def by fastforce

  lemma (in ast_classical_domain2) t_constT_None: "constT c = None \<longleftrightarrow> d2.constT c = None"
    using t_entT_None ast_classical_domain.constT_def detype_classical_dom_def by fastforce

  lemma (in ast_classical_problem2) t_cnsts_objs_names: "map fst (all_consts)
    = map fst (detype_ents (consts D) @ detype_ents (objects P))"
    using t_ents_names by (metis map_append)

  lemma (in wf_ast_classical_problem2) t_objm_le_objT:
    "map_of (objects P2) \<subseteq>\<^sub>m p2.objT"
  proof -
    have "distinct (map fst (all_consts))" using wf_P(1) by auto
    hence "distinct (map fst (consts D2 @ objects P2))" using t_cnsts_objs_names
      by (metis detype_classical_dom_sel(3) detype_classical_prob_sel(2))
    hence "fst ` set (objects P2) \<inter> fst ` set (consts D2) = {}"
      by auto
    hence "dom (map_of (objects P2)) \<inter> dom d2.constT = {}" using d2.constT_def
      by (simp add: dom_map_of_conv_image_fst)
    thus ?thesis using map_add_comm p2.objT_def
      by (metis detype_classical_prob_sel(1) map_le_iff_map_add_commute)
  qed

  lemma (in ast_classical_problem2) t_objT_Some: "objT c \<noteq> None \<longleftrightarrow> p2.objT c = Some \<omega>"
  proof -
    have 1: "\<forall>(x, y) \<in> set (detype_ents (consts D) @ detype_ents (objects P)). y = \<omega>"
      using ents_detyped by fastforce
    have "objT c \<noteq> None \<longleftrightarrow> c \<in> fst ` set (all_consts)" using t_cnsts_objs_names
      by (metis objT_alt map_of_eq_None_iff)
    also have "... \<longleftrightarrow> c \<in> fst ` set (detype_ents (consts D) @ detype_ents (objects P))"
      using t_cnsts_objs_names by (metis image_set)
    also have "... \<longleftrightarrow> p2.objT c = Some \<omega>" using map_of_single_val[OF 1]
      using p2.objT_alt
      by (simp add: detype_classical_dom_def detype_classical_prob_def)
    ultimately show ?thesis by simp
  qed

lemma (in ast_classical_problem2) t_objT_Some_r: "\<forall>c. objT c \<noteq> None \<longrightarrow> p2.objT c = Some \<omega>"
  using t_objT_Some by simp

  lemma (in ast_classical_problem2) t_objT_None: "objT c = None \<longleftrightarrow> p2.objT c = None"
    using t_entT_None ast_classical_problem.objT_def
    by (metis detype_classical_prob_sel(1-2) map_add_None t_constT_None)

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
  lemma (in ast_classical_domain2) t_tyt_params:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "list_all2 (is_of_type tyt) params Ts"
    shows "list_all2 (d2.is_of_type tyt2) params (replicate (length Ts) \<omega>)"
  proof -
    from assms(2) have
      ls: "length params = length Ts" and
      "\<forall>i < length params. is_of_type tyt (params !i) (Ts ! i)"
      by (simp_all add: list_all2_nthD list_all2_lengthD)

    hence "\<forall>i < length params. tyt (params ! i) \<noteq> None" using is_of_type_def
      by (metis option.simps(4))
    hence 2: "\<forall>i < length params. tyt2 (params ! i) = Some \<omega>" using assms(1) by simp
    hence "\<forall>i < length params. (case tyt2 (params ! i) of Some t \<Rightarrow> d2.of_type t \<omega>)"
      by simp
    hence "\<forall>i < length params. d2.is_of_type tyt2 (params ! i) \<omega>"
      using d2.is_of_type_def 2 by fastforce
    thus ?thesis using ls
      by (simp add: list_all2_conv_all_nth)
  qed

text \<open> formulas \<close>

  lemma (in wf_ast_classical_domain2) t_atom_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_atom tyt a"
    shows "d2.wf_atom tyt2 a"
    using assms
  proof (cases a)
    case [simp]: (predAtm p params)
    (* these follow from the definition of wf_pred_atom *)
    from assms obtain Ts where sigp: "sig p = Some Ts" by fastforce
    with assms have 1: "list_all2 (is_of_type tyt) params Ts" by simp

    let ?os = "replicate (length Ts) \<omega>"
    from assms 1 have "list_all2 (d2.is_of_type tyt2) params ?os"
      by (simp add: t_tyt_params)
    moreover have "d2.sig p = Some ?os" using sigp by (simp add: detyped_preds_arity)

    ultimately show ?thesis by simp
  qed simp

  lemma (in wf_ast_classical_domain2) t_fmla_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_fmla tyt \<phi>"
    shows "d2.wf_fmla tyt2 \<phi>"
    using assms t_atom_wf co_fmla_wf by blast

  lemma (in wf_ast_classical_domain2) t_eff_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_effect tyt \<epsilon>"
    shows "d2.wf_effect tyt2 \<epsilon>"
    using assms t_atom_wf co_effect_wf by blast

text \<open> detype ac \<close>

  lemma ac_params_detyped:
    "\<forall>ac \<in> set (actions D2). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>"
    using ents_detyped by fastforce

  lemma (in wf_ast_classical_domain) t_acs_dis:
    "distinct (map ac_name (map detype_classical_ac (actions D)))"
  proof -
    have "ac_name (detype_classical_ac ac) = ac_name ac" for ac
      by (cases ac; simp)
    hence "map ac_name (map detype_classical_ac acs) = map ac_name acs" for acs
      by simp
    thus ?thesis using wf_D by metis
  qed

  lemma (in ast_classical_domain2) t_ac_tyt:
    assumes "ty_term (map_of (ac_params a)) constT x \<noteq> None"
    shows "ty_term (map_of (ac_params (detype_classical_ac a))) d2.constT x = Some \<omega>"
    using assms t_tyt_Some ast_classical_domain.constT_def by auto

  lemma params_ts_exist: (* somehow this isn't trivial for the solver *)
    assumes "wf_action_params a" "(n, Either ts) \<in> set (ac_params a)"
    shows "set ts \<subseteq> set type_names"
    using assms wf_action_params_def wf_type_iff_listed by blast

  lemma (in wf_ast_classical_domain2) type_atom_wf:
    assumes "t \<in> set type_names" "tyt x = Some \<omega>"
    shows "d2.wf_fmla tyt (type_atom x t)"
  proof -
    from assms(1) have "d2.sig (pred_for_type t) = Some [\<omega>]" by (rule type_pred_sig)
    hence "d2.wf_fmla tyt (Atom (predAtm (pred_for_type t) [x]))"
      using assms(2) d2.of_type_refl d2.is_of_type_def by fastforce
    thus ?thesis by simp
  qed

  text \<open>
  1. tyt p = Some T
  2. tyt2 p = Some \<omega>
  for every type in T, the type_cond is wf:
    - the corresponding type_pred exists and has signature [\<omega>]
    - the arguments are just the variable [v], due to 2 with signatures [\<omega>]
  \<close>

  (* instead of d2.ac_tyt, we could use the same with an arbitrary value for consT *)
  lemma (in wf_ast_classical_domain2) type_precond_wf:
    assumes "wf_action_params a" "p \<in> set (ac_params a)"
    shows "d2.wf_fmla
      (d2.ac_tyt (detype_classical_ac a))
      (type_precond p)"
  proof -
    (* type_precond.cases? *)
    obtain n ts where p: "p = (n, Either ts)"     
      using type_precond.cases .
    let ?tyt = "ac_tyt a"
    let ?tyt2 = "d2.ac_tyt (detype_classical_ac a)"
    let ?v = "term.VAR n"
    
    (* Not generally "Some (Either ts)", unless we assume wf_action_schema,
       because param names may not be distinct. *) 
    have "?tyt ?v \<noteq> None" using assms
      by (simp add: p weak_map_of_SomeI)
    hence "?tyt2 ?v = Some \<omega>" using t_tyt_var_Some by simp
    hence "\<forall>t \<in> set ts. d2.wf_fmla ?tyt2 (type_atom ?v t)"
      using assms p type_atom_wf[where tyt = ?tyt2] params_ts_exist by blast
    hence "\<forall>\<phi> \<in> set (map (type_atom ?v) ts). d2.wf_fmla ?tyt2 \<phi>"
      by simp
    hence "d2.wf_fmla ?tyt2 (type_precond (n, Either ts))"
      using d2.bigor_wf type_precond.simps by metis
    thus ?thesis using p by simp
  qed

  lemma (in wf_ast_classical_domain2) t_param_precond_wf:
    assumes "wf_action_params a"
    shows "d2.wf_fmla
    (d2.ac_tyt (detype_classical_ac a))
    (param_precond (ac_params a))"
  proof -
    let ?tyt2 = "d2.ac_tyt (detype_classical_ac a)"
    have "\<forall>p \<in> set (ac_params a). d2.wf_fmla ?tyt2 (type_precond p)"
      using assms type_precond_wf by simp
    hence "\<forall>\<phi> \<in> set (map type_precond (ac_params a)). d2.wf_fmla ?tyt2 \<phi>" by simp
    thus ?thesis using d2.bigand_wf param_precond_def by metis
  qed

  text \<open>Three conditions: 1. distinct parameter names, 2. wf precondition, 3. wf effect\<close>
  lemma (in restrict_domain2) t_ac_wf:
    assumes "a \<in> set (actions D)"
    shows "d2.wf_action_schema (detype_classical_ac a)"
  proof -
    let ?a2 = "detype_classical_ac a"
    let ?tyt = "ty_term (map_of (ac_params a)) constT"
    let ?tyt2 = "ty_term (map_of (ac_params (detype_classical_ac a))) d2.constT"

    have tyt_om: "\<forall>x. ?tyt x \<noteq> None \<longrightarrow> ?tyt2 x = Some \<omega>" using t_ac_tyt by simp
    from assms have wfa: "wf_action_schema a" using wf_D(7) by simp

    from assms have "distinct (map fst (ac_params a))" using wfa wf_action_schema_alt by metis
    hence c1: "distinct (map fst (ac_params ?a2))" using t_ents_dis by auto

    from assms have "wf_fmla ?tyt (ac_pre a)" using wfa wf_action_schema_alt by metis
    hence c2b: "d2.wf_fmla ?tyt2 (ac_pre a)" using tyt_om t_fmla_wf by blast
    have "wf_action_params a" using restrict_D(2) assms by simp
    note c2a = t_param_precond_wf[OF this]
    from c2a c2b have c2: "d2.wf_fmla ?tyt2 (ac_pre ?a2)" by simp

    from assms have wfeff: "wf_effect ?tyt (ac_eff a)" using wfa wf_action_schema_alt by metis
    hence "d2.wf_effect ?tyt2 (ac_eff a)" by (rule t_eff_wf[OF tyt_om])
    hence c3: "d2.wf_effect ?tyt2 (ac_eff ?a2)" by simp

    from c1 c2 c3 show ?thesis using d2.wf_action_schema_alt by simp
  qed

  lemma (in restrict_domain2) t_acs_wf:
    shows "\<forall>a \<in> set (map detype_classical_ac (actions D)). d2.wf_action_schema a"
    using detype_classical_dom_def wf_D t_ac_wf by simp

  text \<open> supertype_facts (init) \<close>

lemma superfacts_for_cond:
  assumes "single_type T"
  shows "supertype_facts_for (n, T) =
    map (type_atom n) (supertypes_of (get_t T))"
  using assms by (auto intro: type_decomp_1)
  
  lemma (in wf_ast_classical_domain) supertypes_listed:
    assumes "t \<in> set type_names"
    shows "set (supertypes_of t) \<subseteq> set type_names"
  proof -
    have "set (supertypes_of t) \<subseteq> insert t (snd ` set (types D))"
      using reachable_set by simp
    also have "... \<subseteq> insert t (set type_names)"
      using  wf_D(1) wf_types_def type_names_set by auto
    also have "... \<subseteq> set type_names" using assms by simp
  
    ultimately show ?thesis by blast
  qed

  (* unfolding supertype_facts and supertype_facts_for, employing the fact that every const
     has a singular type. *)
  lemma (in restrict_problem) superfacts_unfolded:
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

  (* I could do "p2.wf_world_model (set (supertype_facts_for ent))"
     but it doesn't make it more readable imo. *)
  lemma (in restrict_problem2) super_facts_for_wf:
    assumes "(n, T) \<in> set (all_consts)"
    shows "\<forall>\<phi> \<in> set (supertype_facts_for (n, T)). d2.wf_fmla_atom p2.objT \<phi>"
  proof -
    from assms have "single_type T" using single_t_consts by auto
    then obtain t where t: "T = Either [t]"
        by (metis type_decomp_1)
    have "wf_type T" using assms wf_DP(5, 10) by auto
    hence "t \<in> set type_names" using wf_type_iff_listed t by auto
    hence st_ss: "set (supertypes_of t) \<subseteq> set type_names"
      using supertypes_listed by simp
    have om: "p2.objT n = Some \<omega>"
      using assms by (metis t_objT_Some objT_Some option.distinct(1))
  
    have "\<forall>t\<in> set (supertypes_of t). d2.wf_fmla (p2.objT) (type_atom n t)"
      using type_atom_wf[where tyt = p2.objT] om st_ss by auto
    hence "\<forall>\<phi> \<in> set (map (type_atom n) (supertypes_of t)). d2.wf_fmla p2.objT \<phi>"
      by simp
    thus ?thesis using superfacts_for_cond t by simp
  qed

  lemma (in restrict_problem2) super_facts_wf:
    shows "p2.wf_world_model sf_substate"
    using p2.wf_world_model_def super_facts_for_wf supertype_facts_def by auto

lemma (in wf_ast_classical_problem2) t_wm_wf:
  assumes "wf_world_model M" shows "p2.wf_world_model M"
proof -
  have "wf_atom objT a \<longrightarrow> p2.wf_atom p2.objT a" for a
    using t_atom_wf t_objT_Some_r by auto
  with assms co_wm_wf show ?thesis by metis
qed

lemma (in restrict_problem2) t_init_wf:
  "p2.wf_world_model p2.I"
  using wf_I t_wm_wf super_facts_wf p2.wf_world_model_def by auto

end


context ast_classical_domain begin

text \<open> init cond \<close>

(* super simple because of remdups *)
lemma (in restrict_problem) t_init_dis: "distinct (init P2)"
  by simp

(* If I remove remdups
lemma (in restrict_problem) "distinct (init P2)"
proof -
  have "distinct (supertype_facts (all_consts))"
    using reachable_dis sorry (* I'm not doing that *)
  moreover have "distinct (init P)" using wf_P by simp
  moreover have "sf_substate \<inter> set (init P) = {}" sorry

  ultimately show ?thesis by simp
qed*)

text \<open> goal \<close>

lemma (in wf_ast_classical_problem2) t_goal_wf:
  "p2.wf_fmla p2.objT (goal P2)"
  using t_fmla_wf[OF t_objT_Some_r] wf_P(5) by auto

  theorem (in ast_classical_domain2) dom_detyped:
    "d2.typeless_dom"
  proof -
    have c1: "types D2 = []" using detype_classical_dom_def by simp
    note c2 = preds_detyped
    have c3: "\<forall>(n, T) \<in> set (consts D2). T = \<omega>"
      by (simp add: detype_classical_dom_def ents_detyped)
    note c4 = ac_params_detyped
  
    from c1 c2 c3 c4 show ?thesis
      using d2.typeless_dom_def by simp
  qed

  theorem (in ast_classical_problem2) prob_detyped:
    "p2.typeless_prob"
  proof -
    have "\<forall>(n, T) \<in> set (objects P2). T = \<omega>"
      by (simp add: detype_classical_prob_def ents_detyped)
    thus ?thesis using dom_detyped p2.typeless_prob_def detype_classical_prob_def by simp
  qed

  theorem (in restrict_domain2) detype_classical_dom_wf:
    shows "d2.wf_domain"
  proof -
    (* Types are well-formed because they are simply empty. *)
    have c1: "d2.wf_types" using d2.wf_types_def detype_classical_dom_def by simp
    note c2 = t_preds_dis
    note c3 = t_preds_wf
    note c4 = t_ents_dis[OF wf_D(4)]
    note c5 = t_ents_wf[of "consts D"]
    note c6 = t_acs_dis
    note c7 = t_acs_wf

    from c1 c2 c3 c4 c5 c6 c7 show ?thesis
      using d2.wf_domain_def detype_classical_dom_def by auto
  qed

  theorem (in restrict_problem2) detype_classical_prob_wf:
    shows "p2.wf_problem"
  proof -
    note c1 = detype_classical_dom_wf
    have c2: "distinct (map fst (objects P2) @ map fst (consts D2))"
      using t_ents_names wf_P(1) by (metis detype_classical_prob_sel(2) detype_classical_dom_sel(3))
    have c3: "\<forall>(n, y) \<in> set (objects P2). p2.wf_type y"
      using t_ents_wf detype_classical_prob_def by fastforce
    note c4 = t_init_dis
    note c5 = t_init_wf
    note c6 = t_goal_wf
    
    from c1 c2 c3 c4 c5 c6 show ?thesis
      using p2.wf_problem_def detype_classical_prob_def detype_classical_dom_def by simp
  qed
end

sublocale restrict_domain2 \<subseteq> d2: wf_ast_classical_domain D2
  using detype_classical_dom_wf wf_ast_classical_domain.intro by simp

sublocale restrict_problem2 \<subseteq> p2: wf_ast_classical_problem P2
  using detype_classical_prob_wf wf_ast_classical_problem.intro by simp

subsubsection \<open> Type Normalization Preserves Semantics \<close>

context ast_classical_domain
begin

text \<open> Supertype Facts logic \<close>

  lemma of_type_iff_reach:
    shows "of_type (Either oT) (Either T) \<longleftrightarrow> (
      \<forall>ot \<in> set oT.
      \<exists>t \<in> set T.
        t \<in> set (supertypes_of ot))"
  proof -
    have "of_type (Either oT) (Either T) \<longleftrightarrow>
      set oT \<subseteq> ((set (types D))\<^sup>*)\<inverse> `` set T"
      using subtype_rel_star_alt of_type_def by simp
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set oT. ot \<in> ((set (types D))\<^sup>*)\<inverse> `` set T)"
      by auto
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set oT. \<exists>t. (ot, t) \<in> (set (types D))\<^sup>* \<and> t \<in> set T)"
      by auto
    finally show ?thesis using reachable_iff_in_star describes_rel_def by metis
  qed

lemma single_of_type_iff:
  shows "of_type (Either [ot]) (Either T) \<longleftrightarrow> (
    \<exists>t \<in> set T.
      t \<in> set (supertypes_of ot))"
  using of_type_iff_reach by simp

end
context ast_classical_problem
begin

  

lemma obj_of_type_iff_reach:
  assumes "objT n = Some (Either oT)"
  shows  "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<forall>ot \<in> set oT.
      \<exists>t \<in> set T.
    t \<in> set (supertypes_of ot))"
  using assms is_obj_of_type_def of_type_iff_reach by auto

lemma type_atom_inj: "inj (type_atom n)"
  using type_atom.simps pred_for_type_inj
  by (simp add: inj_def)

lemma simple_obj_of_type_iff:
  assumes "objT n = Some (Either [ot])"
  shows  "is_obj_of_type n (Either T) \<longleftrightarrow>
      (\<exists>t \<in> set T.
    t \<in> set (supertypes_of ot))"
  using assms is_obj_of_type_def single_of_type_iff by auto

lemma simple_obj_of_type_iff_fact:
  assumes "objT n = Some oT" "single_type oT"
  shows "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T.
    (type_atom n t) \<in> set (supertype_facts_for (n, oT)))"
proof -
  from assms(2) obtain ot where [simp]: "oT = Either [ot]"
    by (auto intro: type_decomp_1)
  hence "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T.
    (type_atom n t) \<in> (type_atom n) ` set (supertypes_of ot))"
    using assms simple_obj_of_type_iff type_atom_inj inj_image_mem_iff by metis
  thus ?thesis using assms(1) by simp
qed
end

context restrict_problem
begin
lemma (in restrict_problem2) sf_basic: "wm_basic sf_substate"
  using p2.i_basic unfolding wm_basic_def by simp

lemma typeatm_iff_obj_listed:
  assumes "type_atom n t \<in> sf_substate"
  obtains oT where "(n, oT) \<in> set (all_consts)"
  using assms supertype_facts_def superfacts_for_cond single_t_consts by fastforce

theorem obj_of_type_iff_typeatom:
  shows "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T.
     type_atom n t \<in> sf_substate)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L: ?L
  moreover obtain oT where ot: "(n, oT) \<in> set (all_consts)"
    using L objT_Some is_obj_of_type_def by (cases "objT n"; simp)
  moreover have "set (supertype_facts_for (n, oT)) \<subseteq> sf_substate"
    using supertype_facts_def ot by auto
  ultimately show ?R
    using simple_obj_of_type_iff_fact single_t_consts objT_Some
    by (metis case_prod_conv subset_code(1))
next
  assume R: ?R
  then obtain oT where ot: "(n, oT) \<in> set (all_consts)"
    using typeatm_iff_obj_listed by auto
  from R  obtain t where tin: "t \<in> set T" and "type_atom n t \<in> sf_substate" ..
  then obtain n' T' where
    1: "type_atom n t \<in> set (supertype_facts_for (n', T'))" and
    2: "(n', T') \<in> set (all_consts)"
    using supertype_facts_def by auto
  from 2 have "single_type T'" using single_t_consts by auto
  hence "n = n'" using 1 superfacts_for_cond by auto
  moreover hence "oT = T'" using 2 ot
    by (metis objT_Some option.inject)
  ultimately have "type_atom n t \<in> set (supertype_facts_for (n, oT))" using 1 by simp
  thus ?L
    using ot objT_Some single_t_consts tin simple_obj_of_type_iff_fact by blast
qed

theorem (in restrict_problem2) obj_of_type_iff2:
  shows "is_obj_of_type n (Either T) \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<^bold>\<Or>(map (type_atom n) T)"
proof -
  have "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T. valuation sf_substate \<Turnstile> type_atom n t)"
    using obj_of_type_iff_typeatom valuation_def by simp
  also have "... \<longleftrightarrow> valuation sf_substate \<Turnstile> (\<^bold>\<Or>(map (type_atom n) T))" (* type_precond uses variables instead of objects... *)
    using BigOr_semantics by simp
  also have "... \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<^bold>\<Or>(map (type_atom n) T)"
    using sf_basic valuation_iff_close_world by blast
  finally show ?thesis by auto
qed

lemma (in restrict_problem2) obj_of_vartype_iff:
  assumes "tsubst (term.VAR v) = n"
  shows "is_obj_of_type n vT \<longleftrightarrow>
    sf_substate \<^sup>c\<TTurnstile>\<^sub>= map_atom_fmla tsubst (type_precond (v, vT))"
proof -
  let ?map_subst = "map_atom_fmla tsubst"
  have 1: "map (type_atom n) (primitives vT) = map (?map_subst \<circ> type_atom (term.VAR v)) (primitives vT)"
    using assms by simp
  have 2: "\<^bold>\<Or>(map (?map_subst \<circ> (type_atom (term.VAR v))) (primitives vT))
    = ?map_subst \<^bold>\<Or>(map ((type_atom (term.VAR v))) (primitives vT))"
    using map_formula_bigOr by (metis comp_apply list.map_comp)
  have "is_obj_of_type n vT \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<^bold>\<Or>(map (type_atom n) (primitives vT))"
    using obj_of_type_iff2 by force
  thus ?thesis using 1 2 type_precond.simps
    by (metis type.exhaust_sel)
qed

lemma (in restrict_problem2) obj_of_vartype_iff2:
  assumes
    "distinct (map fst params)"
    "params ! i = (v, vT)" "args ! i = n"
    "i < length params" "i < length args"
  shows "is_obj_of_type n vT \<longleftrightarrow>
    sf_substate \<^sup>c\<TTurnstile>\<^sub>= map_atom_fmla (ac_tsubst params args) (type_precond (v, vT))"
  using obj_of_vartype_iff ac_tsubst_intro[OF assms] by blast

(* using this logic for the next lemma *)
lemma "(b \<Longrightarrow> (c \<longleftrightarrow> d)) \<Longrightarrow> b \<and> c \<longleftrightarrow> b \<and> d" by auto

(* forgive me, father, for I have sinned; TODO: simplify *)
theorem (in restrict_problem2) params_match_iff_type_precond:
  assumes "wf_action_schema ac"
  defines "params \<equiv> ac_params ac"
  shows "action_params_match ac args \<longleftrightarrow>
    length params = length args \<and>
    sf_substate \<^sup>c\<TTurnstile>\<^sub>= map_atom_fmla (ac_tsubst params args) (param_precond params)"
proof -
  let ?leq = "length params = length args"
  define el_map where "el_map \<equiv> map_atom_fmla (ac_tsubst params args)"

  have dis: "distinct (map fst params)" using assms wf_action_schema_alt by metis

  have 1: "action_params_match ac args \<longleftrightarrow>
    ?leq \<and>
    (\<forall>i < (length params). is_obj_of_type (args ! i) (snd (params ! i)))"
    using assms(2) action_params_match_def
    by (smt (verit) length_map list_all2_all_nthI list_all2_lengthD list_all2_nthD nth_map)
  {
    assume ?leq
    {
      fix i assume l: "i < length params"
      
      hence "is_obj_of_type (args ! i) (snd (params ! i))
      \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= el_map (type_precond (params ! i))"
        using obj_of_vartype_iff2 dis \<open>?leq\<close> is_obj_of_type_def
        by (metis el_map_def prod.exhaust_sel)
    }
    hence "(\<forall>i < length params. is_obj_of_type (args ! i) (snd (params ! i))) \<longleftrightarrow>
      (\<forall>\<phi> \<in> {el_map (type_precond (params ! i)) | i. i < length params}. sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<phi>)"
      by blast
    also have "... \<longleftrightarrow>
      (\<forall>\<phi> \<in> set (map (el_map \<circ> type_precond) params). sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<phi>)"
      using map_set_comprehension[where f="el_map \<circ> type_precond"] by fastforce
    also have "... \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<^bold>\<And>(map (el_map \<circ> type_precond) params)"
      using bigAnd_entailment by blast
    also have "... \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= el_map (\<^bold>\<And>(map type_precond params))"
      using el_map_def bigAnd_map_atom
      by (metis list.map_comp)
    note calculation
  }
  thus ?thesis using 1 el_map_def bigAnd_map_atom
    by (metis (no_types, opaque_lifting) map_map param_precond_def)
qed

end


(* INSTANTIATE STUFF *)

lemma (in restrict_problem2) t_resinst:
  assumes "resolve_action_schema n = Some ac"
  shows "d2.resolve_action_schema n = Some (detype_classical_ac ac)"
proof -
  from assms have a: "ac \<in> set (actions D)"
    by (metis index_by_eq_SomeD resolve_action_schema_def)
  from assms have b: "ac_name ac = n"
    by (metis resolve_action_schema_def index_by_eq_SomeD)
  hence "ac_name (detype_classical_ac ac) = n" by simp
  moreover have "detype_classical_ac ac \<in> set (actions D2)"
    using a by auto
  ultimately show ?thesis using d2.wf_D(6)
    by (simp add: d2.resolve_action_schema_def)
qed

lemma (in restrict_problem2) t_resinst_inv:
  assumes "p2.resolve_action_schema n = Some ac2"
  obtains ac where
    "detype_classical_ac ac = ac2"
    "ac \<in> set (actions D)"
    "resolve_action_schema n = Some ac"
proof -
  from assms obtain ac where ac: "detype_classical_ac ac = ac2" and ac_in: "ac \<in> set (actions D)"
    using p2.res_aux by auto
  hence "ac_name (detype_classical_ac ac) = n"
    using p2.resolve_action_schema_def index_by_eq_SomeD assms by metis
  hence "ac_name ac = n" by simp
  thus ?thesis using that ac ac_in resolve_action_schema_def wf_DP(6) by simp
qed

subsubsection \<open> Semantics \<close>


text \<open> Type atom/Supertype facts inclusion/exclusion/overlap \<close>
(* TODO: reevaluate what is necessary, maybe use fmla_preds in proofs *)

context ast_classical_domain begin
lemma wf_patm_neq_type_patm:
  assumes "wf_pred_atom tyt (p, xs)"
  shows "type_predatm x t \<noteq> map_atom f (predAtm p xs)"
proof -
  from assms have "p \<in> pred ` set (predicates D)"
    using sig_None wf_pred_atom.simps by (metis option.simps(4))
  thus ?thesis using type_pred_notin by auto
qed

lemma wf_fmla_atom_neq_type_atom:
  assumes "wf_fmla_atom tyt \<phi>"
  shows "map_atom_fmla f \<phi> \<noteq> type_atom x t"
  using assms apply (cases rule: wf_fmla_atom.cases[of \<phi>])
  using wf_patm_neq_type_patm by fastforce+

(*lemma wf_fmla_atom_neq_type_atom_unatm:
  assumes "wf_fmla_atom tyt \<phi>"
  shows "un_Atom (map_atom_fmla f \<phi>) \<noteq> type_predatm x t"
  using assms apply (cases rule: wf_fmla_atom.cases[of \<phi>])
  using wf_patm_neq_type_patm by fastforce+*)

lemma wf_fmla_no_type_patms:
  assumes "wf_fmla tyt \<phi>"
  shows "type_predatm n t \<notin> atoms (map_atom_fmla f \<phi>)"
proof -
  have "atoms (map_atom_fmla f \<phi>) = (map_atom f) ` (atoms \<phi>)"
    by (simp add: formula.set_map)
  moreover have "type_predatm n t \<notin> (map_atom f) ` (atoms \<phi>)"
  using assms proof (induction \<phi>)
    case (Atom a)
    thus ?case
    proof (cases a)
      case (predAtm p vs)
      thus ?thesis using wf_patm_neq_type_patm Atom predAtm by fastforce
    qed simp (* Obviously, type_predatm n t \<noteq> Eq a b. *)
  qed auto
  ultimately show ?thesis by simp
qed

lemma (in restrict_problem) sf_typeatms:
  assumes "\<psi> \<in> sf_substate"
  shows "\<exists>n t. \<psi> = type_atom n t"
  using assms superfacts_unfolded by auto

lemma (in restrict_problem) sf_disj_wf_fmla:
  assumes "wf_fmla tyt \<phi>"
  shows "sf_substate \<inter> Atom ` atoms (map_atom_fmla f \<phi>) = {}"
  using assms sf_typeatms wf_fmla_no_type_patms by fastforce

lemma fmla_map_id: "map_atom_fmla id \<phi> = \<phi>"
  by (simp add: atom.map_id0 formula.map_id)

lemma (in restrict_problem) sf_disj_wf_fmla0:
  assumes "wf_fmla tyt \<phi>"
  shows "sf_substate \<inter> Atom ` atoms \<phi> = {}"
  using assms sf_disj_wf_fmla[where f=id] fmla_map_id by metis

lemma (in -) "map_ast_effect f (Effect A D) =
  Effect (map (map_atom_fmla f) A) (map (map_atom_fmla f) D)"
  by simp

lemma wf_eff_no_type_atoms:
  assumes "wf_effect tyt \<epsilon>"
  shows
    "type_atom n t \<notin> set (adds (map_ast_effect f \<epsilon>))" (is ?a) and
    "type_atom n t \<notin> set (dels (map_ast_effect f \<epsilon>))" (is ?d)
proof -
  from assms have "\<forall>\<phi> \<in> set (adds \<epsilon>). wf_fmla_atom tyt \<phi>"
    using assms by (cases \<epsilon>) simp
  hence "\<forall>\<phi> \<in> (map_atom_fmla f) ` set (adds \<epsilon>). \<phi> \<noteq> type_atom n t"
    using wf_fmla_atom_neq_type_atom by fast
  thus ?a by (cases \<epsilon>) auto

  from assms have "\<forall>\<phi> \<in> set (dels \<epsilon>). wf_fmla_atom tyt \<phi>"
    using assms by (cases \<epsilon>) simp
  hence "\<forall>\<phi> \<in>(map_atom_fmla f) ` set (dels \<epsilon>). \<phi> \<noteq> type_atom n t"
    using wf_fmla_atom_neq_type_atom by fast
  thus ?d by (cases \<epsilon>) auto
qed


abbreviation "is_type_patm a \<equiv> \<exists>x t. a = type_predatm x t"


lemma map_atom_preserves_istypeatm: "is_type_patm a \<longleftrightarrow> is_type_patm (map_atom f a)"
  by (cases a) auto

lemma map_fmla_preserves_istypeatm:
  assumes "\<forall>a \<in> atoms F. is_type_patm a"
  shows "\<forall>a \<in> atoms (map_atom_fmla f F). is_type_patm a"
proof -
  have "atoms (map_atom_fmla f F) = (map_atom f) ` (atoms F)"
    by (simp add: formula.set_map)
  thus ?thesis using assms
    apply (induction F)
    apply simp_all
       apply (metis map_atom_preserves_istypeatm)+
    done
qed

lemma map_fmla_preserves_nistypeatm:
  assumes "\<forall>a \<in> atoms F. \<not> is_type_patm a"
  shows "\<forall>a \<in> atoms (map_atom_fmla f F). \<not> is_type_patm a"
proof -
  have "atoms (map_atom_fmla f F) = (map_atom f) ` (atoms F)"
    by (simp add: formula.set_map)
  thus ?thesis using assms
    apply (induction F)
    apply simp_all
       apply (metis map_atom_preserves_istypeatm)+
    done
qed

lemma param_pre_typeatms:
  "\<forall> a \<in> atoms (map_atom_fmla f (param_precond params)). \<exists>x t. a = type_predatm x t"
proof -
  let ?is_typatm = "\<lambda>a. (\<exists>x t. a = type_predatm x t)"
  have "\<forall> f \<in> set (map (type_atom (term.VAR v)) ts).
    \<forall>a \<in> atoms f. \<exists>x t. a = type_predatm x t" for v ts by auto
  hence "\<forall>a \<in> atoms (type_precond (v, (Either ts))). \<exists>x t. a = type_predatm x t"
    for v ts
    by (induction ts) auto
  hence "\<forall>a \<in> atoms (type_precond param). \<exists>x t. a = type_predatm x t" for param
    by (cases rule: type_precond.cases[of param]) simp
  hence "\<forall> f \<in> set (map type_precond params).
    \<forall>a \<in> atoms f. \<exists>x t. a = type_predatm x t" by simp
  hence "\<forall> a \<in> atoms (param_precond params). \<exists>x t. a = type_predatm x t"
    unfolding param_precond_def by (induction params) auto
  with map_fmla_preserves_istypeatm show ?thesis by blast
qed

lemma (in ast_classical_problem) wf_wm_no_typeatms:
  "wf_world_model wm \<Longrightarrow> type_atom x t \<notin> wm"
  unfolding wf_world_model_def using wf_fmla_atom_neq_type_atom by fastforce

lemma (in ast_classical_problem) wf_wm_disj_param_pre:
  assumes "wf_world_model wm"
  shows "wm \<inter> Atom ` atoms (map_atom_fmla f (param_precond params)) = {}"
  using assms wf_wm_no_typeatms param_pre_typeatms by force

(* for wf init, since sf and init don't overlap *)
lemma (in restrict_problem) sf_disj_wf_wm:
  assumes "wf_world_model wm"
  shows "sf_substate \<inter> wm = {}"
proof -
  from assms have "\<forall>\<phi> \<in> wm. wf_fmla_atom objT \<phi>"
    using wf_world_model_def by simp
  hence "type_atom x t \<notin> wm" for x t
    using wf_fmla_atom_neq_type_atom by fastforce
  thus ?thesis using sf_typeatms by blast
qed

lemma (in restrict_problem) sf_disj_wf_eff:
  assumes "wf_effect tyt \<epsilon>"
  shows
    "sf_substate \<inter> set (adds (map_ast_effect f \<epsilon>)) = {}"
    "sf_substate \<inter> set (dels (map_ast_effect f \<epsilon>)) = {}"
  using assms sf_typeatms wf_eff_no_type_atoms by fast+

lemmas in_ex_clusion_helpers =
  wf_patm_neq_type_patm
  wf_fmla_no_type_patms

end

(* All of these could maybe be intelligently moved somewhere else... *)
hide_fact
  ast_classical_domain.wf_patm_neq_type_patm
  ast_classical_domain.wf_fmla_no_type_patms
  restrict_problem.sf_typeatms
  ast_classical_domain.wf_fmla_atom_neq_type_atom
  ast_classical_problem.wf_wm_no_typeatms
  ast_classical_domain.param_pre_typeatms
  ast_classical_domain.map_atom_preserves_istypeatm
  ast_classical_domain.map_fmla_preserves_istypeatm
  ast_classical_domain.map_fmla_preserves_nistypeatm
  (* ast_classical_domain.wf_fmla_atom_neq_type_atom_unatm *)

(* ------ end inclusion/exclusion *)

context restrict_problem2
begin

lemma t_params_match:
  assumes "action_params_match ac args"
  shows "p2.action_params_match (detype_classical_ac ac) args"
proof -
  from assms have len: "length (ac_params ac) = length args"
    by (simp add: list_all2_lengthD action_params_match_def)
  hence len2: "length (ac_params (detype_classical_ac ac)) = length args"
    by (cases ac; simp; metis length_map detype_ents_def)

  have "p2.is_obj_of_type (args ! i) (snd (ac_params (detype_classical_ac ac) ! i))"
    if "i < length args" for i
  proof -
    have "is_obj_of_type (args ! i) (snd ((ac_params ac) ! i))"
      using that assms len
      by (simp add: action_params_match_def list_all2_conv_all_nth)
    hence "objT (args ! i) \<noteq> None" using is_obj_of_type_def by (metis option.simps(4))
    hence "p2.is_obj_of_type (args ! i) \<omega>" using t_objT_Some p2.is_obj_of_type_def by simp
    thus ?thesis using that len2 by (simp add: detype_ent_alt detype_ents_def)
  qed
  thus "?thesis"
    by (simp add: len2 list_all2_conv_all_nth p2.action_params_match_def del: detype_classical_ac_sel)
qed

(* TODO clean this up, if possible *)
theorem detyped_planaction_enabled_iff:
  assumes "wf_world_model s"
  shows "plan_action_enabled \<pi> s \<longleftrightarrow> p2.plan_action_enabled \<pi> (s \<union> sf_substate)"
proof -
  obtain n args where pi: "\<pi> = PAction n args" by (cases \<pi>; simp)
  let ?pi = "PAction n args"

  from assms have s_basic: "wm_basic s" using wf_wm_basic by simp

  {
    assume assm: "plan_action_enabled ?pi s"
    hence wf: "wf_plan_action ?pi" and entail: "s \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate ?pi)"
      using plan_action_enabled_def by simp_all

    (* actions *)
    from wf obtain ac where res: "resolve_action_schema n = Some ac"
      by fastforce
    hence res2: "d2.resolve_action_schema n = Some (detype_classical_ac ac)"
      by (rule t_resinst)

    (* parameter mappings *)
    let ?pre_map = "map_atom_fmla (ac_tsubst (parameters ac) args)"
    let ?pre_map2 = "map_atom_fmla (ac_tsubst (parameters (detype_classical_ac ac)) args)"
    have "map fst (parameters (detype_classical_ac ac)) = map fst (parameters ac)"
      by (cases ac; simp add: t_ents_names)
    hence premaps: "?pre_map2 = ?pre_map" using ac_tsubst_def by simp

    (* "left" side: from wf_plan_action \<pi> show p2.wf_plan_action \<pi> *)
    from wf res have match: "action_params_match ac args" by simp
    hence "p2.action_params_match (detype_classical_ac ac) args"
      using t_params_match by simp
    with res2 have wf2: "p2.wf_plan_action ?pi"
      using p2.wf_plan_action_simple by fastforce

    (* "middle": from action_params_match ac args show s \<union> sf_substate satisfy the param precond of the instantiated action.*)
    from match have entail_typ: "sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac))"
      using params_match_iff_type_precond res res_aux wf_D(7) by simp
    (* Since init doesn't interfere with the type predicates,
       we can add it to sf_substate here and still satisfy them. *)
    from assms have "s \<inter> Atom ` atoms (?pre_map (param_precond (ac_params ac))) = {}"
      using wf_wm_disj_param_pre by simp
    with entail_typ have entail_L: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac))"
      using entail_adds_irrelevant[OF sf_basic s_basic] Un_commute by metis
    
    (* "right" side: show s satisfies action precond \<Longrightarrow> s \<union> sf_substate satisfies instantiated action precond in P2 *)
    have entail_pre: "s \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (ac_pre ac)"
      using entail res instantiate_action_schema_alt by force
    (* Since sf_substate doesn't interfere with the precondition,
       we can add it to init here and still satisfy it. *)
    have "wf_action_schema ac" using res wf_D(7) res_aux by simp
    hence "wf_fmla (ty_term (map_of (ac_params ac)) constT) (ac_pre ac)"
      using wf_action_schema_alt by simp
    hence "sf_substate \<inter> Atom ` atoms (?pre_map (ac_pre ac)) = {}"
      using sf_disj_wf_fmla by blast
    with entail_pre have entail_R: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (ac_pre ac)"
      using entail_adds_irrelevant[OF s_basic sf_basic] by simp

    (* putting it together *)
    from entail_L entail_R have entail_map2:
      "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map2 ((param_precond (ac_params ac)) \<^bold>\<and> (ac_pre ac))"
      using entail_and premaps by auto
    hence entail2: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= precondition (p2.resolve_instantiate ?pi)"
      using entail_map2 res2 by (simp add: p2.instantiate_action_schema_alt)
    with wf2 have "p2.plan_action_enabled ?pi (s \<union> sf_substate)"
      by (simp add: p2.plan_action_enabled_def)
  }
  moreover {
    assume "p2.plan_action_enabled ?pi (s \<union> sf_substate)"
    hence wf2: "p2.wf_plan_action ?pi" and entail2: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= precondition (p2.resolve_instantiate ?pi)"
      using p2.plan_action_enabled_def by simp_all

    (* actions *)
    from wf2 obtain ac2 where res2: "p2.resolve_action_schema n = Some ac2"
      using p2.wf_pa_refs_ac by metis
    then obtain ac where ac[simp]: "ac2 = detype_classical_ac ac" and ac_in: "ac \<in> set (actions D)"
      and res: "resolve_action_schema n = Some ac" by (metis t_resinst_inv)

    (* parameter mappings *)
    let ?pre_map2 = "map_atom_fmla (ac_tsubst (ac_params ac2) args)"
    let ?pre_map = "map_atom_fmla (ac_tsubst (ac_params ac) args)"
    have t_param_names: "map fst (parameters ac) = map fst (parameters (detype_classical_ac ac))"
      by (cases ac; simp add: t_ents_names)
    hence premaps: "?pre_map = ?pre_map2" using ac_tsubst_def by simp

    (* "right" side *)
    have "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map2 (ac_pre ac2)"
      using entail2 res2 instantiate_action_schema_alt by force
    hence entail2: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac)) \<^bold>\<and> ?pre_map (ac_pre ac)"
      using premaps by force
    hence entail_a: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (ac_pre ac)"
      using entail_and by blast
    (* Since sf_substate doesn't interfere with the precondition,
       we can remove it from init here and still satisfy it. *)
    from ac_in have wf_ac: "wf_action_schema ac" using wf_D(7) by simp
    hence "wf_fmla (ty_term (map_of (ac_params ac)) constT) (ac_pre ac)"
      using wf_action_schema_alt by simp
    hence "sf_substate \<inter> Atom ` atoms (?pre_map (ac_pre ac)) = {}"
      using sf_disj_wf_fmla by simp
    with entail_a have "s \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (ac_pre ac)"
      using entail_adds_irrelevant[OF s_basic sf_basic] by simp
    hence entail: "s \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate ?pi)"
      using res instantiate_action_schema_alt by simp

    (* "middle" *)
    from wf2 res2 have match2: "p2.action_params_match ac2 args" by simp
    (* Since init doesn't interfere with the type predicates,
       we can remove it from i2 here and still satisfy them. *)
    have "\<forall>\<phi> \<in> s. wf_fmla_atom objT \<phi>"
      using assms wf_fmla_atom_alt wf_world_model_def by simp
    from assms have "s \<inter> Atom ` atoms (?pre_map (param_precond (ac_params ac))) = {}"
      using wf_wm_disj_param_pre by simp
    moreover from entail2 have "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac))"
      using entailment_def entail_and by blast
    ultimately have entail_typ: "sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac))"
      using entail_adds_irrelevant[OF sf_basic s_basic] by (simp add: Set.Un_commute)

    (* "left" side *)
    hence "length (ac_params ac2) = length args"
      using match2 p2.action_params_match_def by (simp add: list_all2_lengthD)
    moreover have "length (ac_params ac) = length (ac_params (detype_classical_ac ac))"
      using t_param_names map_eq_imp_length_eq by blast (*weird way to prove this*)
    ultimately have "length (ac_params ac) = length args"
      using detype_ents_def by simp
    hence "action_params_match ac args"
      using params_match_iff_type_precond[OF wf_ac] entail_typ by simp
    with res have wf: "wf_plan_action ?pi" using wf_plan_action_simple by fastforce

    from entail wf have "plan_action_enabled ?pi s"
      by (simp add: plan_action_enabled_def)
  }
  ultimately show ?thesis using pi by auto
qed

abbreviation "states_match s s' \<equiv> wf_world_model s \<and> s \<union> sf_substate = s'"

lemma match_state_step:
  assumes "states_match s s'" "execute_plan_action \<pi> s = t" "wf_plan_action \<pi>"
  shows "states_match t (p2.execute_plan_action \<pi> s')"
proof -
  obtain n args where pi: "\<pi> = PAction n args" by (cases \<pi>) simp
  then obtain ac where res: "resolve_action_schema n = Some ac"
    using assms(3) plan_action_enabled_def by fastforce
  hence 1: "effect (resolve_instantiate \<pi>) = map_ast_effect (ac_tsubst (ac_params ac) args) (ac_eff ac)"
    using pi instantiate_action_schema_alt by simp

  from pi obtain ac2 where res2: "p2.resolve_action_schema n = Some ac2" and t_ac: "ac2 = detype_classical_ac ac"
    using res t_resinst by simp
  hence 2: "effect (p2.resolve_instantiate \<pi>) = map_ast_effect (ac_tsubst (ac_params ac2) args) (ac_eff ac2)"
    using pi instantiate_action_schema_alt by simp

  from t_ac have "map fst (ac_params ac) = map fst (ac_params ac2)"
    by (simp add: t_ents_names)
  moreover from t_ac have "ac_eff ac = ac_eff ac2" by simp
  ultimately have effeq: "effect (resolve_instantiate \<pi>) = effect (p2.resolve_instantiate \<pi>)"
    using ac_tsubst_def 1 2 by force

  note wf_resolve_instantiate[OF assms(3)]
  hence "wf_effect objT (effect (resolve_instantiate \<pi>))"
    by (simp add: wf_ground_action_alt)
  with sf_disj_wf_eff[OF this, where f = id] have
    "sf_substate \<inter> set (adds (effect (resolve_instantiate \<pi>))) = {}"
    "sf_substate \<inter> set (dels (effect (resolve_instantiate \<pi>))) = {}"
    by (simp_all add: ast_effect.map_id)

  hence "apply_effect (effect (resolve_instantiate \<pi>)) (s \<union> sf_substate) =
    apply_effect (effect (resolve_instantiate \<pi>)) s \<union> sf_substate"
    using 1 apply_effect_alt sf_disj_wf_wm by auto
  hence "p2.execute_plan_action \<pi> s' = execute_plan_action \<pi> s \<union> sf_substate"
    using effeq execute_plan_action_def
    using p2.execute_plan_action_def assms(1) by simp
  moreover have "wf_world_model (execute_plan_action \<pi> s)" using wf_execute_stronger assms by auto
  ultimately show ?thesis using assms(2) by simp
qed

lemma goal_sem:
  assumes "wm_basic s"
  shows "s \<^sup>c\<TTurnstile>\<^sub>= goal P \<longleftrightarrow> s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= goal P2"
proof -  
  have 1: "s \<^sup>c\<TTurnstile>\<^sub>= goal P \<longleftrightarrow> s \<^sup>c\<TTurnstile>\<^sub>= goal P2" by simp
  have c3: "sf_substate \<inter> Atom ` atoms (goal P2) = {}"
    using detype_classical_prob_sel(4) fmla_map_id sf_disj_wf_fmla[where f = id] wf_P(5) by metis
  note entail_adds_irrelevant[OF assms sf_basic c3]
  with 1 show ?thesis by simp
qed
lemma match_goal:
  assumes "states_match s s'"
  shows "s \<^sup>c\<TTurnstile>\<^sub>= goal P \<longleftrightarrow> s' \<^sup>c\<TTurnstile>\<^sub>= goal P2"
  using assms goal_sem wf_wm_basic by simp

lemma match_valid_plan_from:
  assumes "states_match s s'" "valid_plan_from s \<pi>s"
  shows "p2.valid_plan_from s' \<pi>s"
using assms proof (induction \<pi>s arbitrary: s s')
  case Nil
  hence "s \<^sup>c\<TTurnstile>\<^sub>= goal P"
    using valid_plan_from_def by simp
  hence "s' \<^sup>c\<TTurnstile>\<^sub>= goal P2" using assms match_goal Nil.prems by simp
  thus ?case using p2.valid_plan_from_def by auto
next
  case (Cons p ps)
  let ?t = "execute_plan_action p s"
  let ?t' = "p2.execute_plan_action p s'"
  from Cons have enab1: "plan_action_enabled p s" and valid1: "valid_plan_from ?t ps"
    using valid_plan_from_def plan_action_path_Cons by auto
  from enab1 have enab2: "p2.plan_action_enabled p s'"
    using detyped_planaction_enabled_iff assms(1) Cons.prems by simp
  
  have "states_match ?t ?t'"
    using assms(1) enab1 Cons.prems match_state_step plan_action_enabled_def
    by blast

  hence "p2.valid_plan_from ?t' ps"
    using Cons.IH[OF _ valid1] by simp
  with enab2 show ?case using p2.valid_plan_from_def plan_action_path_Cons by simp
qed

lemma inits_match:
  shows "states_match I p2.I" using wf_I by auto

lemma match_valid_plan:
  assumes "valid_plan \<pi>s" shows "p2.valid_plan \<pi>s"
  using assms unfolding ast_classical_problem.valid_plan_def
  using match_valid_plan_from inits_match by blast

text \<open>Proving: p2.valid_plan \<pi>s \<Longrightarrow> valid_plan \<pi>s \<close>


abbreviation reachable_prop :: "world_model \<Rightarrow> bool" where
  "reachable_prop s' \<equiv> \<exists>s. states_match s s'"
abbreviation (input) "RP \<equiv> reachable_prop"

lemma rp_props:
  assumes "RP M"
  shows
    "p2.wf_world_model M"
    "\<forall>x t. type_atom x t \<in> M \<longleftrightarrow> type_atom x t \<in> sf_substate"
    "wf_world_model (M - sf_substate)"
proof -
  from assms show "p2.wf_world_model M" using t_wm_wf
    using p2.wf_world_model_def super_facts_wf by auto
  (* if problem: super_facts_wf might need wf_wm_def *)
  from assms show "\<forall>x t. type_atom x t \<in> M \<longleftrightarrow> type_atom x t \<in> sf_substate"
    using wf_wm_no_typeatms by force
  from assms obtain s where "states_match s M" by blast
  thus "wf_world_model (M - sf_substate)"
    using wf_world_model_def by auto
qed

lemma rp_init: "RP p2.I"
proof -
  have "p2.I = I \<union> sf_substate" by auto
  thus ?thesis using wf_P(4) by auto
qed

lemma rp_sf: "RP (sf_substate)"
  using wf_world_model_def by auto

lemma rp_enabled_iff:
  assumes "RP M"
  shows "plan_action_enabled \<pi> (M - sf_substate) \<longleftrightarrow> p2.plan_action_enabled \<pi> M"
  using assms detyped_planaction_enabled_iff rp_props by auto

(* TODO: lots of duplication from match_state_step*)
lemma match_state_step':
  assumes "states_match s s'" "p2.execute_plan_action \<pi> s' = t'" "p2.plan_action_enabled \<pi> s'"
  shows "states_match (execute_plan_action \<pi> s) t'"
proof -
  obtain n args where pi: "\<pi> = PAction n args" by (cases \<pi>) simp
  then obtain ac' where res': "p2.resolve_action_schema n = Some ac'"
    using assms(3) p2.plan_action_enabled_def by fastforce
  then obtain ac where res: "resolve_action_schema n = Some ac" and t_ac: "detype_classical_ac ac = ac'"
    using t_resinst_inv by metis
  hence 1: "effect (resolve_instantiate \<pi>) = map_ast_effect (ac_tsubst (ac_params ac) args) (ac_eff ac)"
    using pi instantiate_action_schema_alt by simp
  from res' have 2: "effect (p2.resolve_instantiate \<pi>) = map_ast_effect (ac_tsubst (ac_params ac') args) (ac_eff ac')"
    using pi instantiate_action_schema_alt by simp

  from t_ac have "map fst (ac_params ac) = map fst (ac_params ac')"
    using t_ents_names detype_classical_ac_sel by metis
  moreover from t_ac have "ac_eff ac = ac_eff ac'" by auto
  ultimately have effeq: "effect (resolve_instantiate \<pi>) = effect (p2.resolve_instantiate \<pi>)"
    using ac_tsubst_def 1 2 by force

  from assms(1,3) have wf: "wf_plan_action \<pi>"
    using detyped_planaction_enabled_iff plan_action_enabled_def by auto
  hence "wf_ground_action (resolve_instantiate \<pi>)"
    using wf_resolve_instantiate by simp
  hence "wf_effect objT (effect (resolve_instantiate \<pi>))"
    by (simp add: wf_ground_action_alt)
  with sf_disj_wf_eff[OF this, where f = id] have
    "sf_substate \<inter> set (adds (effect (resolve_instantiate \<pi>))) = {}"
    "sf_substate \<inter> set (dels (effect (resolve_instantiate \<pi>))) = {}"
    by (simp_all add: ast_effect.map_id)

  hence "apply_effect (effect (resolve_instantiate \<pi>)) (s \<union> sf_substate) =
    apply_effect (effect (resolve_instantiate \<pi>)) s \<union> sf_substate"
    using 1 apply_effect_alt sf_disj_wf_wm by auto
  hence "p2.execute_plan_action \<pi> s' = execute_plan_action \<pi> s \<union> sf_substate"
    using effeq execute_plan_action_def
    using p2.execute_plan_action_def assms(1) by simp
  moreover have "wf_world_model (execute_plan_action \<pi> s)"
    using wf_execute_stronger wf assms(1) by auto
  ultimately show ?thesis using assms(2) by simp
qed

lemma match_valid_plan_from':
  assumes "states_match s s'" "p2.valid_plan_from s' \<pi>s"
  shows "valid_plan_from s \<pi>s"
using assms proof (induction \<pi>s arbitrary: s s')
  case Nil
  hence "s' \<^sup>c\<TTurnstile>\<^sub>= goal P2"
    using p2.valid_plan_from_def by simp
  hence "s \<^sup>c\<TTurnstile>\<^sub>= goal P" using assms match_goal Nil.prems by simp
  thus ?case using valid_plan_from_def by auto
next
  case (Cons p ps)
  let ?t = "execute_plan_action p s"
  let ?t' = "p2.execute_plan_action p s'"
  from Cons have enab2: "p2.plan_action_enabled p s'" and valid2: "p2.valid_plan_from ?t' ps"
    using p2.valid_plan_from_def p2.plan_action_path_Cons by simp_all
  from enab2 have enab1: "plan_action_enabled p s"
    using detyped_planaction_enabled_iff assms(1) Cons.prems by simp
  
  have "states_match ?t ?t'"
    using assms(1) enab2 match_state_step' Cons.prems by blast
  hence "valid_plan_from ?t ps"
    using Cons.IH[OF _ valid2] by simp
  with enab1 show ?case using valid_plan_from_def plan_action_path_Cons by simp
qed

lemma match_valid_plan':
  assumes "p2.valid_plan \<pi>s" shows "valid_plan \<pi>s"
  using assms unfolding ast_classical_problem.valid_plan_def
  using match_valid_plan_from' inits_match by blast

(* putting it together: *)

theorem detyped_valid_iff:
  "valid_plan \<pi>s \<longleftrightarrow> p2.valid_plan \<pi>s"
  using match_valid_plan match_valid_plan' by blast

end

subsection \<open> Code Setup \<close>

lemmas type_norm_code =
  ast_classical_domain.wf_action_params_def
  ast_classical_domain.restrict_dom_def
  ast_classical_domain.pred_for_type_def
  ast_classical_domain.type_pred.simps
  ast_classical_domain.type_preds_def
  ast_classical_domain.type_atom.simps
  ast_classical_domain.type_precond.simps
  ast_classical_domain.param_precond_def
  ast_classical_domain.detype_classical_ac.simps
  ast_classical_domain.detype_classical_dom_def
  ast_classical_domain.supertype_facts_for.simps
  ast_classical_domain.supertype_facts_def
  ast_classical_problem.detype_classical_prob_def
  ast_classical_domain.typeless_dom_def
  ast_classical_problem.typeless_prob_def
declare type_norm_code[code]


end