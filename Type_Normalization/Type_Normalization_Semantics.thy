theory Type_Normalization_Semantics
  imports Type_Normalization
begin

subsubsection \<open> Type Normalization Preserves Semantics \<close>

context domain_signature
begin

text \<open> Supertype Facts logic \<close>

  lemma of_type_iff_reach:
    shows "of_type (Either oT) (Either T) \<longleftrightarrow> (
      \<forall>ot \<in> set oT.
      \<exists>t \<in> set T.
        t \<in> set (supertypes_of ot))"
  proof -
    have "of_type (Either oT) (Either T) \<longleftrightarrow>
      set oT \<subseteq> ((set ty_decl)\<^sup>*)\<inverse> `` set T"
      using subtype_rel_star_alt of_type_def by simp
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set oT. ot \<in> ((set ty_decl)\<^sup>*)\<inverse> `` set T)"
      by auto
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set oT. \<exists>t. (ot, t) \<in> (set ty_decl)\<^sup>* \<and> t \<in> set T)"
      by auto
    finally show ?thesis using reachable_iff_in_star describes_rel_def by metis
  qed

lemma single_of_type_iff:
  shows "of_type (Either [ot]) (Either T) \<longleftrightarrow> (
    \<exists>t \<in> set T.
      t \<in> set (supertypes_of ot))"
  using of_type_iff_reach by simp

end
context problem_signature
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


context wf_restrict_problem_signature
begin
lemma (in restrict_problem_signature2) sf_basic: "lwm_basic sf_substate"
  unfolding lwm_basic_def 
  using supertype_facts_predAtom by argo

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

theorem obj_of_type_iff2:
  assumes "wf_type (Either T)"
  shows "is_obj_of_type n (Either T) \<longleftrightarrow> valuation (sf_substate, x) \<Turnstile>\<^sub>m \<^bold>\<Or>(map (type_atom n) T)"
proof -
  have "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T. valuation (sf_substate, x) \<Turnstile>\<^sub>m type_atom n t)"
    using obj_of_type_iff_typeatom valuation_def by simp
  also have "... \<longleftrightarrow> valuation (sf_substate, x) \<Turnstile>\<^sub>m \<^bold>\<Or>(map (type_atom n) T)"
  proof -
    have "\<forall>f \<in> set (map (type_atom n) T). atoms f \<subseteq> dom (valuation (sf_substate, x))"
      by auto
    thus ?thesis by auto
  qed
  finally show ?thesis by auto
qed

lemma obj_of_vartype_iff:
  assumes "subst_term f (term.VAR v) = n"
      and "wf_type vT"
  shows "is_obj_of_type n vT \<longleftrightarrow>
    valuation (sf_substate, x) \<Turnstile>\<^sub>m map_atom_fmla (subst_term f) (type_precond (v, vT))"
proof -
  let ?map_subst = "map_atom_fmla (subst_term f)"
  have 1: "map (type_atom n) (primitives vT) = map (?map_subst \<circ> type_atom (term.VAR v)) (primitives vT)"
    using assms by simp
  have 2: "\<^bold>\<Or>(map (?map_subst \<circ> (type_atom (term.VAR v))) (primitives vT))
    = ?map_subst \<^bold>\<Or>(map ((type_atom (term.VAR v))) (primitives vT))"
    using map_formula_bigOr by (metis comp_apply list.map_comp)
  have "is_obj_of_type n vT \<longleftrightarrow> valuation (sf_substate, x) \<Turnstile>\<^sub>m \<^bold>\<Or>(map (type_atom n) (primitives vT))"
    using obj_of_type_iff2 assms(2) by (cases vT) force
  thus ?thesis using 1 2 type_precond.simps
    by (metis type.exhaust_sel)
qed

lemma obj_of_vartype_iff2:
  assumes a:
    "distinct (map fst params)"
    "params ! i = (v, vT)" "args ! i = n"
    "i < length params" "i < length args"
  and wf: "wf_type vT"
  shows "is_obj_of_type n vT \<longleftrightarrow>
    valuation (sf_substate, x) \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst params args) (type_precond (v, vT))"
  using ac_tsubst_intro assms obj_of_vartype_iff by simp

(* using this logic for the next lemma *)
lemma "(b \<Longrightarrow> (c \<longleftrightarrow> d)) \<Longrightarrow> b \<and> c \<longleftrightarrow> b \<and> d" by auto

(* forgive me, father, for I have sinned; TODO: simplify *)
theorem (in restrict_classical_problem2) params_match_iff_type_precond:
  assumes "wf_classical_action_schema ac"
  assumes "wf_action_params ac"
  defines "params \<equiv> ac_params ac"
  defines "h \<equiv> ac_head ac"
  shows "action_params_match h args \<longleftrightarrow>
    length params = length args \<and>
    valuation (sf_substate, x) \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst params args) (param_precond params)"
proof -
  let ?leq = "length params = length args"
  define el_map where "el_map \<equiv> map_atom_fmla (ac_tsubst params args)"

  have dis: "distinct (map fst params)" using assms wf_classical_action_schema_alt by metis

  have 1: "action_params_match h args \<longleftrightarrow>
    ?leq \<and>
    (\<forall>i < (length params). is_obj_of_type (args ! i) (snd (params ! i)))"
    unfolding params_def h_def action_params_match_def list_all2_conv_all_nth
    by force
  {
    assume ?leq
    {
      fix i assume l: "i < length params"

      obtain v vT where
        pi: "params ! i = (v, vT)" using l apply (cases "params ! i") by auto

      have "params ! i \<in> set (ac_params ac)" using l params_def by simp
      hence wft: "wf_type vT" using assms wf_action_params_def pi by auto
      
      have "is_obj_of_type (args ! i) (snd (params ! i))
      \<longleftrightarrow> valuation (sf_substate, x) \<Turnstile>\<^sub>m  el_map (type_precond (params ! i))"
        unfolding el_map_def pi
        apply (subst obj_of_vartype_iff2[symmetric])
        using dis \<open>?leq\<close> assms l pi wft
        unfolding is_obj_of_type_def el_map_def snd_conv by simp_all
    }
    hence "(\<forall>i < length params. is_obj_of_type (args ! i) (snd (params ! i))) \<longleftrightarrow>
      (\<forall>\<phi> \<in> {el_map (type_precond (params ! i)) | i. i < length params}. valuation (sf_substate, x) \<Turnstile>\<^sub>m  \<phi>)"
      by blast
    also have "... \<longleftrightarrow>
      (\<forall>\<phi> \<in> set (map (el_map \<circ> type_precond) params). valuation (sf_substate, x) \<Turnstile>\<^sub>m  \<phi>)"
      using map_set_comprehension[where f="el_map \<circ> type_precond"] by fastforce
    also have "... \<longleftrightarrow> valuation (sf_substate, x) \<Turnstile>\<^sub>m  \<^bold>\<And>(map (el_map \<circ> type_precond) params)"
      using BigAnd_map_semantics by blast
    also have "... \<longleftrightarrow> valuation (sf_substate, x) \<Turnstile>\<^sub>m  el_map (\<^bold>\<And>(map type_precond params))"
      by (simp add: bigAnd_map_atom[simplified comp_def, symmetric] comp_def el_map_def)
    note calculation
  }
  thus ?thesis using 1 el_map_def bigAnd_map_atom
    by (metis (no_types, opaque_lifting) map_map param_precond_def)
qed

end


(* INSTANTIATE STUFF *)

lemma (in restrict_classical_problem2) t_resinst:
  assumes "resolve_classical_action_schema n = Some ac"
  shows "d2.resolve_classical_action_schema n = Some (detype_classical_ac ac)"
proof -
  from assms have a: "ac \<in> set (actions D)"
    by (metis index_by_eq_SomeD resolve_classical_action_schema_def)
  from assms have b: "ac_name ac = n"
    by (metis resolve_classical_action_schema_def index_by_eq_SomeD)
  hence "ac_name (detype_classical_ac ac) = n" by simp
  moreover have "detype_classical_ac ac \<in> set (actions D2)"
    using a by auto
  ultimately show ?thesis using wf_D
    by (simp add: d2.resolve_classical_action_schema_def)
qed

lemma (in restrict_classical_problem2) t_resinst_inv:
  assumes "p2.resolve_classical_action_schema n = Some ac2"
  obtains ac where
    "detype_classical_ac ac = ac2"
    "ac \<in> set (actions D)"
    "resolve_classical_action_schema n = Some ac"
proof -
  from assms obtain ac where ac: "detype_classical_ac ac = ac2" and ac_in: "ac \<in> set (actions D)"
    using res_aux by auto
  hence "ac_name (detype_classical_ac ac) = n"
    using p2.resolve_classical_action_schema_def index_by_eq_SomeD assms by metis
  hence "ac_name ac = n" by simp
  thus ?thesis using that ac ac_in resolve_classical_action_schema_def wf_DP
    by simp
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
    qed auto (* Obviously, type_predatm n t \<noteq> Eq a b. *)
  qed auto
  ultimately show ?thesis by simp
qed

lemma (in restrict_classical_problem) sf_typeatms:
  assumes "\<psi> \<in> sf_substate"
  shows "\<exists>n t. \<psi> = type_atom n t"
  using assms superfacts_unfolded by auto

lemma (in restrict_classical_problem) sf_disj_wf_fmla:
  assumes "wf_fmla tyt \<phi>"
  shows "sf_substate \<inter> Atom ` atoms (map_atom_fmla f \<phi>) = {}"
  using assms sf_typeatms wf_fmla_no_type_patms by fastforce

lemma fmla_map_id: "map_atom_fmla id \<phi> = \<phi>"
  by (simp add: atom.map_id0 formula.map_id)

lemma (in restrict_classical_problem) sf_disj_wf_fmla0:
  assumes "wf_fmla tyt \<phi>"
  shows "sf_substate \<inter> Atom ` atoms \<phi> = {}"
  using assms sf_disj_wf_fmla[where f=id] fmla_map_id by metis

lemma (in -) "map_ast_effect f (Effect A D N) =
  Effect (map (map_atom_fmla f) A) (map (map_atom_fmla f) D) (map (map_numeric_effect f) N)"
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
  "wf_world_model wm \<Longrightarrow> type_atom x t \<notin> fst wm"
  using wf_fmla_atom_neq_type_atom by (cases wm) fastforce

lemma (in ast_classical_problem) wf_wm_disj_param_pre:
  assumes "wf_world_model wm"
  shows "fst wm \<inter> Atom ` atoms (map_atom_fmla f (param_precond params)) = {}"
  using assms wf_wm_no_typeatms param_pre_typeatms by (cases wm) force

(* for wf init, since sf and init don't overlap *)
lemma (in restrict_classical_problem) sf_disj_wf_wm:
  assumes "wf_world_model wm"
  shows "sf_substate \<inter> fst wm = {}"
proof -
  from assms have "\<forall>\<phi> \<in> fst wm. wf_fmla_atom objT \<phi>" by (cases wm) force
  hence "type_atom x t \<notin> fst wm" for x t
    using wf_fmla_atom_neq_type_atom by fastforce
  thus ?thesis using sf_typeatms by blast
qed

lemma (in restrict_classical_problem) sf_disj_wf_eff:
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
  restrict_classical_problem.sf_typeatms
  ast_classical_domain.wf_fmla_atom_neq_type_atom
  ast_classical_problem.wf_wm_no_typeatms
  ast_classical_domain.param_pre_typeatms
  ast_classical_domain.map_atom_preserves_istypeatm
  ast_classical_domain.map_fmla_preserves_istypeatm
  ast_classical_domain.map_fmla_preserves_nistypeatm
  (* ast_classical_domain.wf_fmla_atom_neq_type_atom_unatm *)

(* ------ end inclusion/exclusion *)

context restrict_classical_problem2
begin

lemma t_params_match:
  assumes "action_params_match (ac_head ac) args"
  shows "p2.action_params_match (head (detype_classical_ac ac)) args"
proof -
  from assms have len: "length (ac_params ac) = length args"
    by (simp add: list_all2_lengthD action_params_match_def)
  hence len2: "length (ac_params (detype_classical_ac ac)) = length args"
    apply (cases ac rule: ast_classical_action_schema_cases_unfold)
    by (simp add: detype_ents_def)

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
end


context restrict_classical_problem2
begin
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
    have "wf_classical_action_schema ac" using res wf_D(7) res_aux by simp
    hence "wf_fmla (ty_term (map_of (ac_params ac)) constT) (ac_pre ac)"
      using wf_classical_action_schema_alt by simp
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
    from ac_in have wf_ac: "wf_classical_action_schema ac" using wf_D(7) by simp
    hence "wf_fmla (ty_term (map_of (ac_params ac)) constT) (ac_pre ac)"
      using wf_classical_action_schema_alt by simp
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

lemma match_valid_classical_plan_from2:
  assumes "states_match s s'" "valid_classical_plan_from2 s \<pi>s"
  shows "p2.valid_classical_plan_from2 s' \<pi>s"
using assms proof (induction \<pi>s arbitrary: s s')
  case Nil
  hence "s \<^sup>c\<TTurnstile>\<^sub>= goal P"
    using valid_classical_plan_from2_def by simp
  hence "s' \<^sup>c\<TTurnstile>\<^sub>= goal P2" using assms match_goal Nil.prems by simp
  thus ?case using p2.valid_classical_plan_from2_def by auto
next
  case (Cons p ps)
  let ?t = "execute_plan_action p s"
  let ?t' = "p2.execute_plan_action p s'"
  from Cons have enab1: "plan_action_enabled p s" and valid1: "valid_classical_plan_from2 ?t ps"
    using valid_classical_plan_from2_def plan_action_path_Cons by auto
  from enab1 have enab2: "p2.plan_action_enabled p s'"
    using detyped_planaction_enabled_iff assms(1) Cons.prems by simp
  
  have "states_match ?t ?t'"
    using assms(1) enab1 Cons.prems match_state_step plan_action_enabled_def
    by blast

  hence "p2.valid_classical_plan_from2 ?t' ps"
    using Cons.IH[OF _ valid1] by simp
  with enab2 show ?case using p2.valid_classical_plan_from2_def plan_action_path_Cons by simp
qed

lemma inits_match:
  shows "states_match I p2.I" using wf_I by auto

lemma match_valid_classical_plan:
  assumes "valid_classical_plan \<pi>s" shows "p2.valid_classical_plan \<pi>s"
  using assms unfolding ast_classical_problem.valid_classical_plan_def
  using match_valid_classical_plan_from2 inits_match by blast

text \<open>Proving: p2.valid_classical_plan \<pi>s \<Longrightarrow> valid_classical_plan \<pi>s \<close>


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

lemma match_valid_classical_plan_from2':
  assumes "states_match s s'" "p2.valid_classical_plan_from2 s' \<pi>s"
  shows "valid_classical_plan_from2 s \<pi>s"
using assms proof (induction \<pi>s arbitrary: s s')
  case Nil
  hence "s' \<^sup>c\<TTurnstile>\<^sub>= goal P2"
    using p2.valid_classical_plan_from2_def by simp
  hence "s \<^sup>c\<TTurnstile>\<^sub>= goal P" using assms match_goal Nil.prems by simp
  thus ?case using valid_classical_plan_from2_def by auto
next
  case (Cons p ps)
  let ?t = "execute_plan_action p s"
  let ?t' = "p2.execute_plan_action p s'"
  from Cons have enab2: "p2.plan_action_enabled p s'" and valid2: "p2.valid_classical_plan_from2 ?t' ps"
    using p2.valid_classical_plan_from2_def p2.plan_action_path_Cons by simp_all
  from enab2 have enab1: "plan_action_enabled p s"
    using detyped_planaction_enabled_iff assms(1) Cons.prems by simp
  
  have "states_match ?t ?t'"
    using assms(1) enab2 match_state_step' Cons.prems by blast
  hence "valid_classical_plan_from2 ?t ps"
    using Cons.IH[OF _ valid2] by simp
  with enab1 show ?case using valid_classical_plan_from2_def plan_action_path_Cons by simp
qed

lemma match_valid_classical_plan':
  assumes "p2.valid_classical_plan2 \<pi>s"
  shows "valid_classical_plan2 \<pi>s"
  using assms unfolding valid_classical_plan2_def
  using match_valid_classical_plan_from2' inits_match by blast

(* putting it together: *)

theorem detyped_valid_iff:
  "valid_classical_plan2 \<pi>s \<longleftrightarrow> p2.valid_classical_plan2 \<pi>s"
  using match_valid_classical_plan match_valid_classical_plan' by blast

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
