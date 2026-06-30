theory Classical_Type_Normalization_Semantics
  imports Classical_Type_Normalization
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
(* sf_basic moved to Grounding_Type_Normalization.Type_Normalization_Proofs *)

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
  ultimately show ?thesis using d2_wf.wf_D
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
    using d2_wf.res_aux by auto
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
  shows "plan_action_enabled \<pi> s \<longleftrightarrow> p2.plan_action_enabled \<pi> (fst s \<union> sf_substate, snd s)"
proof -
  obtain n args where pi: "\<pi> = SimplePlanAction n args" by (cases \<pi>; simp)
  let ?pi = "SimplePlanAction n args"

  have s_basic: "lwm_basic (fst s)" using wf_lwm_basic[OF assms] .

  {
    assume assm: "plan_action_enabled ?pi s"
    hence wf: "wf_classical_plan_action ?pi" 
      and entail: "valuation s \<Turnstile>\<^sub>m precondition ((the o res_inst) ?pi)"
      and nintrf: "numeric_effects_non_intrf ((the o res_inst) ?pi)"
      and pnesdef: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the o res_inst) ?pi))) \<subseteq> dom (snd s)"
      using plan_action_enabled_def by (auto simp: Let_def)

    (* actions *)
    from wf obtain ac where res: "resolve_classical_action_schema n = Some ac"
      by fastforce
    hence res2: "d2.resolve_classical_action_schema n = Some (detype_classical_ac ac)"
      by (rule t_resinst)

    (* parameter mappings *)
    let ?pre_map = "map_atom_fmla (ac_tsubst (ac_params ac) args)"
    let ?pre_map2 = "map_atom_fmla (ac_tsubst (ac_params (detype_classical_ac ac)) args)"

    have params_fst_match: "map fst (ac_params (detype_classical_ac ac)) = map fst (ac_params ac)"
      by (cases ac rule: ast_classical_action_schema_cases_unfold; simp add: t_ents_names)
    hence premaps: "?pre_map2 = ?pre_map" using ac_tsubst_def by simp

    (* effect mappings *)
    let ?eff_map = "map_ast_effect (ac_tsubst (ac_params ac) args)"
    let ?eff_map2 = "map_ast_effect (ac_tsubst (ac_params (detype_classical_ac ac)) args)"
    have effmaps: "?eff_map2 = ?eff_map" using params_fst_match by simp

    (* "left" side: from wf_classical_plan_action \<pi> show p2.wf_classical_plan_action \<pi> *)
    from wf res have match: "action_params_match (head ac) args" by (cases ac) simp
    hence "p2.action_params_match (head (detype_classical_ac ac)) args"
      using t_params_match by simp
    with res2 have wf2: "p2.wf_classical_plan_action ?pi" by (cases ac) simp

    have wf_params: "wf_action_params ac"
      using res restrict_D res_aux 
      by blast

    have wf_ac: "wf_classical_action_schema ac"
      using res wf_D(3) res_aux by blast

    (* "middle": from action_params_match ac args show s \<union> sf_substate satisfy the param precond of the instantiated action.*)
    have entail_typ: "valuation (sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map (param_precond (ac_params ac))"
      using params_match_iff_type_precond
      using match using wf_params wf_ac by auto
    (* Since init doesn't interfere with the type predicates,
       we can add it to sf_substate here and still satisfy them. *)
    from assms have "fst s \<inter> Atom ` atoms (?pre_map (param_precond (ac_params ac))) = {}"
      using wf_wm_disj_param_pre by simp
    with entail_typ have entail_L: "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map (param_precond (ac_params ac))"
      using sf_basic s_basic Un_commute entail_adds_irrelevant
      by metis
    
    (* "right" side: show s satisfies action precond \<Longrightarrow> s \<union> sf_substate satisfies instantiated action precond in P2 *)
    have entail_pre: "valuation s \<Turnstile>\<^sub>m ?pre_map (ac_pre ac)"
      using entail comp_def res res_inst_alt
      by (cases ac rule: ast_classical_action_schema_cases_unfold) auto
    (* Since sf_substate doesn't interfere with the precondition,
       we can add it to init here and still satisfy it. *)
    have "wf_classical_action_schema ac" using res wf_D res_aux by simp
    hence "wf_fmla (ty_term (map_of (ac_params ac)) constT) (ac_pre ac)"
      using wf_classical_action_schema_alt ac_tyt_def by simp
    hence "sf_substate \<inter> Atom ` atoms (?pre_map (ac_pre ac)) = {}"
      using sf_disj_wf_fmla by blast
    with entail_pre have entail_R: "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map (ac_pre ac)"
      using entail_adds_irrelevant[OF s_basic sf_basic] by simp

    (* pnes are defined *)
    have "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (?eff_map (ac_eff ac))) \<subseteq> dom (snd s)"
      using pnesdef res
      by (cases ac rule: ast_classical_action_schema_cases_unfold; cases "ac_eff ac") simp
    hence pnesdef2: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the o p2.res_inst) ?pi))) \<subseteq> dom (snd s)"
      using res2 p2.res_inst_alt
      by (cases ac rule: ast_classical_action_schema_cases_unfold; cases "ac_eff ac")
         (simp add: t_ents_names)
    
    (* putting it together *)
    from entail_L entail_R have entail_map2:
      "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map2 ((param_precond (ac_params ac)) \<^bold>\<and> (ac_pre ac))"
      using entail_and premaps by auto
    hence entail2: "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m precondition ((the o p2.res_inst) ?pi)"
      using entail_map2 res2 p2.res_inst_alt by (cases ac rule: ast_classical_action_schema_cases_unfold) auto
   
    have nintrf2: "numeric_effects_non_intrf ((the o p2.res_inst) ?pi)"
      using nintrf res res2 res_inst_alt p2.res_inst_alt
      by (cases ac rule: ast_classical_action_schema_cases_unfold; cases "ac_eff ac")
         (simp add: numeric_effects_non_intrf_def t_ents_names)

    from nintrf2 wf2 entail2 pnesdef2 have "p2.plan_action_enabled ?pi (fst s \<union> sf_substate, snd s)"
      by (simp add: p2.plan_action_enabled_def Let_def)
  }
  moreover {
    assume p2en: "p2.plan_action_enabled ?pi (fst s \<union> sf_substate, snd s)"
    hence wf2: "p2.wf_classical_plan_action ?pi"
      and entail2: "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m precondition ((the o p2.res_inst) ?pi)"
      and nintrf2: "numeric_effects_non_intrf ((the o p2.res_inst) ?pi)"
      and pnesdef2: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the o p2.res_inst) ?pi))) \<subseteq> dom (snd s)"
      using p2.plan_action_enabled_def by (auto simp: Let_def)

    (* actions *)
    from wf2 obtain ac2 where res2: "p2.resolve_classical_action_schema n = Some ac2"
      using p2.wf_pa_refs_ac by metis
    then obtain ac where ac[simp]: "ac2 = detype_classical_ac ac" and ac_in: "ac \<in> set (actions D)"
      and res: "resolve_classical_action_schema n = Some ac" by (metis t_resinst_inv)

    (* parameter mappings *)
    let ?pre_map2 = "map_atom_fmla (ac_tsubst (ac_params ac2) args)"
    let ?pre_map = "map_atom_fmla (ac_tsubst (ac_params ac) args)"
    have t_param_names: "map fst (ac_params ac) = map fst (ac_params (detype_classical_ac ac))"
      by (cases ac rule: ast_classical_action_schema_cases_unfold; simp add: t_ents_names)
    hence premaps: "?pre_map = ?pre_map2" using ac_tsubst_def by simp

    (* effect mappings *)
    let ?eff_map = "map_ast_effect (ac_tsubst (ac_params ac) args)"
    let ?eff_map2 = "map_ast_effect (ac_tsubst (ac_params ac2) args)"
    have effmaps: "?eff_map2 = ?eff_map" using t_param_names by simp

    (* "right" side *)
    have "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map2 (ac_pre ac2)"
      using entail2 res2 p2.res_inst_alt
      by (cases ac2 rule: ast_classical_action_schema_cases_unfold) auto
    hence "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map (ac_pre ac2)"
      using premaps by simp
    moreover have "ac_pre ac2 = param_precond (ac_params ac) \<^bold>\<and> (ac_pre ac)"
      by (cases ac rule: ast_classical_action_schema_cases_unfold) simp
    ultimately have entail2': "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map (param_precond (ac_params ac)) \<^bold>\<and> ?pre_map (ac_pre ac)"
      by simp
    hence entail_a: "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map (ac_pre ac)"
      by simp
    (* Since sf_substate doesn't interfere with the precondition,
       we can remove it from init here and still satisfy it. *)
    from ac_in have wf_ac: "wf_classical_action_schema ac" using wf_D(3) by simp
    hence "wf_fmla (ty_term (map_of (ac_params ac)) constT) (ac_pre ac)"
      using wf_classical_action_schema_alt ac_tyt_def by simp
    hence "sf_substate \<inter> Atom ` atoms (?pre_map (ac_pre ac)) = {}"
      using sf_disj_wf_fmla by simp
    with entail_a have entail_s: "valuation s \<Turnstile>\<^sub>m ?pre_map (ac_pre ac)"
      using entail_adds_irrelevant[OF s_basic sf_basic] by simp
    hence entail: "valuation s \<Turnstile>\<^sub>m precondition ((the o res_inst) ?pi)"
      using res res_inst_alt by (cases ac rule: ast_classical_action_schema_cases_unfold) auto

    (* "middle" *)
    from wf2 res2 have match2: "p2.action_params_match (head ac2) args"
      by (cases ac2) simp
    (* Since init doesn't interfere with the type predicates,
       we can remove it from i2 here and still satisfy them. *)
    from assms have "fst s \<inter> Atom ` atoms (?pre_map (param_precond (ac_params ac))) = {}"
      using wf_wm_disj_param_pre by simp
    moreover from entail2' have "valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map (param_precond (ac_params ac))"
      by simp
    ultimately have entail_typ: "valuation (sf_substate, snd s) \<Turnstile>\<^sub>m ?pre_map (param_precond (ac_params ac))"
      using entail_adds_irrelevant[OF sf_basic s_basic] by (simp add: Set.Un_commute)

    (* "left" side *)
    have wf_params: "wf_action_params ac"
      using res restrict_D res_aux by blast
    have len: "length (ac_params ac) = length args"
      using match2 p2.action_params_match_def t_param_names
      by (cases ac2) (auto simp: list_all2_lengthD detype_ents_def)
    hence match: "action_params_match (ac_head ac) args"
      using params_match_iff_type_precond[OF wf_ac wf_params] entail_typ by metis
    with res have wf: "wf_classical_plan_action ?pi"
      by (cases ac) simp

    have nintrf: "numeric_effects_non_intrf ((the o res_inst) ?pi)"
      using nintrf2 res res2 res_inst_alt p2.res_inst_alt
      by (cases ac rule: ast_classical_action_schema_cases_unfold; cases "ac_eff ac")
         (simp add: numeric_effects_non_intrf_def t_ents_names)

    (* pnes are defined *)
    have "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (?eff_map (ac_eff ac))) \<subseteq> dom (snd s)"
      using pnesdef2 res2 p2.res_inst_alt effmaps
      by (cases ac rule: ast_classical_action_schema_cases_unfold; cases "ac_eff ac")
         (simp add: t_ents_names)
    hence pnesdef: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the o res_inst) ?pi))) \<subseteq> dom (snd s)"
      using res res_inst_alt
      by (cases ac rule: ast_classical_action_schema_cases_unfold; cases "ac_eff ac") simp

    from entail wf nintrf pnesdef have "plan_action_enabled ?pi s"
      by (simp add: plan_action_enabled_def Let_def)
  }
  ultimately show ?thesis using pi by auto
qed

abbreviation "logical_states_match s s' \<equiv> wf_world_model s \<and> fst s \<union> sf_substate = fst s'"

lemma match_state_step:
  assumes "logical_states_match s s'" "execute_plan_action \<pi> s = t" "wf_classical_plan_action \<pi>"
  shows "logical_states_match t (p2.execute_plan_action \<pi> s')"
proof -
  obtain n args where pi: "\<pi> = SimplePlanAction n args" by (cases \<pi>) simp
  let ?a = "(the o res_inst) \<pi>"
  let ?a2 = "(the o p2.res_inst) \<pi>"

  from assms(3) have wfa: "wf_ground_action ?a"
    using wf_resolve_instantiate by simp
  hence wf_eff: "wf_effect objT (ground_action.effect ?a)"
    using wf_ground_action_alt by simp

  from assms(3) obtain ac where res: "resolve_classical_action_schema n = Some ac"
    and ac_in: "ac \<in> set (actions D)"
    using wf_pa_refs_ac pi by metis
  from res have res2: "p2.resolve_classical_action_schema n = Some (detype_classical_ac ac)"
    by (rule t_resinst)

  have a_eq: "?a = instantiate_classical_action_schema ac args"
    using pi res res_inst_alt by simp
  have a2_eq: "?a2 = instantiate_classical_action_schema (detype_classical_ac ac) args"
    using pi res2 p2.res_inst_alt by simp

  have eff_eq: "ground_action.effect ?a = ground_action.effect ?a2"
  proof -
    have "map fst (ac_params ac) = map fst (ac_params (detype_classical_ac ac))"
      by (cases ac rule: ast_classical_action_schema_cases_unfold; simp add: t_ents_names)
    moreover have "ac_eff ac = ac_eff (detype_classical_ac ac)" by simp
    ultimately show ?thesis
      unfolding a_eq a2_eq
      by (cases ac rule: ast_classical_action_schema_cases_unfold) (simp add: ac_tsubst_def)
  qed

  have t_eq: "t = (fst s - set (dels (ground_action.effect ?a)) \<union> set (adds (ground_action.effect ?a)),
                  action_numeric_update_function ?a (snd s))"
    using assms(2) execute_plan_action_def apply_ground_action_alt
    by (cases s) auto
  have p2t_eq: "p2.execute_plan_action \<pi> s' =
    (fst s' - set (dels (ground_action.effect ?a)) \<union> set (adds (ground_action.effect ?a)),
     action_numeric_update_function ?a2 (snd s'))"
    using p2.execute_plan_action_def apply_ground_action_alt eff_eq
    by (cases s') auto

  have sf_disj_dels: "sf_substate \<inter> set (dels (ground_action.effect ?a)) = {}"
    using sf_disj_wf_eff(2)[OF wf_eff, where f=id]
    by (simp add: ast_effect.map_id)
  have sf_disj_adds: "sf_substate \<inter> set (adds (ground_action.effect ?a)) = {}"
    using sf_disj_wf_eff(1)[OF wf_eff, where f=id]
    by (simp add: ast_effect.map_id)

  have "fst t \<union> sf_substate = fst (p2.execute_plan_action \<pi> s')"
  proof -
    have "fst t \<union> sf_substate
      = (fst s - set (dels (ground_action.effect ?a)) \<union> set (adds (ground_action.effect ?a))) \<union> sf_substate"
      using t_eq by simp
    also have "... = (fst s \<union> sf_substate) - set (dels (ground_action.effect ?a)) \<union> set (adds (ground_action.effect ?a))"
      using sf_disj_dels sf_disj_adds by blast
    also have "... = fst s' - set (dels (ground_action.effect ?a)) \<union> set (adds (ground_action.effect ?a))"
      using assms(1) by simp
    also have "... = fst (p2.execute_plan_action \<pi> s')" using p2t_eq by simp
    finally show ?thesis .
  qed
  moreover have "wf_world_model t"
    using assms wf_execute_stronger by blast
  ultimately show ?thesis by simp
qed

abbreviation "numeric_states_match s s' \<equiv> snd s = snd s'"

lemma goal_sem:
  assumes "lwm_basic (fst s)"
  shows "valuation s \<Turnstile>\<^sub>m goal P \<longleftrightarrow> valuation (fst s \<union> sf_substate, snd s) \<Turnstile>\<^sub>m goal P2"
proof -  
  have 1: "valuation s \<Turnstile>\<^sub>m goal P \<longleftrightarrow> valuation s \<Turnstile>\<^sub>m goal P2" by simp
  have c3: "sf_substate \<inter> Atom ` atoms (goal P2) = {}"
    using detype_classical_prob_sel(4) fmla_map_id sf_disj_wf_fmla[where f = id] wf_P(5) by metis
  note entail_adds_irrelevant[OF assms sf_basic c3]
  with 1 show ?thesis by simp
qed

lemma match_goal:
  assumes "logical_states_match s s'"
      and "numeric_states_match s s'"
  shows "valuation s \<Turnstile>\<^sub>m goal P \<longleftrightarrow> valuation s' \<Turnstile>\<^sub>m goal P2"
  using assms wf_lwm_basic[THEN goal_sem] by auto

lemma match_valid_classical_plan_from2:
  assumes "logical_states_match s s'"
      and "numeric_states_match s s'"
      and "valid_classical_plan_from2 s \<pi>s"
  shows "p2.valid_classical_plan_from2 s' \<pi>s"
using assms proof (induction \<pi>s arbitrary: s s')
  case Nil
  hence "valuation s \<Turnstile>\<^sub>m goal P" by simp
  hence "valuation s' \<Turnstile>\<^sub>m goal P2" using Nil match_goal by simp
  thus ?case by simp
next
  case (Cons p ps)
  let ?t = "execute_plan_action p s"
  let ?t' = "p2.execute_plan_action p s'"
  from Cons have enab1: "plan_action_enabled p s" and valid1: "valid_classical_plan_from2 ?t ps"
    by simp_all
  from enab1 Cons.prems have enab2: "p2.plan_action_enabled p s'"
    using detyped_planaction_enabled_iff by simp
  from enab1 have wf_pa: "wf_classical_plan_action p"
    using plan_action_enabled_def by (simp add: Let_def)
  from Cons.prems wf_pa have logmatch': "logical_states_match ?t ?t'"
    using match_state_step by blast
  have nummatch': "numeric_states_match ?t ?t'"
  proof -
    obtain n args where pi: "p = SimplePlanAction n args" by (cases p) simp
    from wf_pa obtain ac where res: "resolve_classical_action_schema n = Some ac"
      using wf_pa_refs_ac pi by metis
    from res have res2: "p2.resolve_classical_action_schema n = Some (detype_classical_ac ac)"
      by (rule t_resinst)
    have a_eq: "(the o res_inst) p = instantiate_classical_action_schema ac args"
      using pi res res_inst_alt by simp
    have a2_eq: "(the o p2.res_inst) p = instantiate_classical_action_schema (detype_classical_ac ac) args"
      using pi res2 p2.res_inst_alt by simp
    have eff_eq: "ground_action.effect ((the o res_inst) p) = ground_action.effect ((the o p2.res_inst) p)"
    proof -
      have "map fst (ac_params ac) = map fst (ac_params (detype_classical_ac ac))"
        by (cases ac rule: ast_classical_action_schema_cases_unfold; simp add: t_ents_names)
      moreover have "ac_eff ac = ac_eff (detype_classical_ac ac)" by simp
      ultimately show ?thesis
        unfolding a_eq a2_eq
        by (cases ac rule: ast_classical_action_schema_cases_unfold) (simp add: ac_tsubst_def)
    qed
    have "snd ?t = action_numeric_update_function ((the o res_inst) p) (snd s)"
      using execute_plan_action_def apply_ground_action_alt by (cases s) auto
    also have "... = action_numeric_update_function ((the o p2.res_inst) p) (snd s')"
      using eff_eq Cons.prems(2) action_numeric_update_function_def by simp
    also have "... = snd ?t'"
      using p2.execute_plan_action_def apply_ground_action_alt by (cases s') auto
    finally show ?thesis .
  qed
  from logmatch' nummatch' valid1 have "p2.valid_classical_plan_from2 ?t' ps"
    using Cons.IH by simp
  with enab2 show ?case by simp
qed

lemma inits_match:
  shows "logical_states_match I p2.I"
  using wf_I p2_I_eq by (metis fst_conv Un_commute)

lemma inits_num_match:
  shows "numeric_states_match I p2.I"
  using p2_I_eq by simp

lemma match_valid_classical_plan:
  assumes "valid_classical_plan2 \<pi>s" shows "p2.valid_classical_plan2 \<pi>s"
  using assms unfolding valid_classical_plan2_def p2.valid_classical_plan2_def
  using match_valid_classical_plan_from2 inits_match inits_num_match by presburger

text \<open>Proving: p2.valid_classical_plan2 \<pi>s \<Longrightarrow> valid_classical_plan2 \<pi>s\<close>

lemma match_state_step':
  assumes logmatch: "logical_states_match s s'"
      and nummatch: "numeric_states_match s s'"
      and p2en: "p2.plan_action_enabled \<pi> s'"
  shows "logical_states_match (execute_plan_action \<pi> s) (p2.execute_plan_action \<pi> s')"
    and "numeric_states_match (execute_plan_action \<pi> s) (p2.execute_plan_action \<pi> s')"
proof -
  from logmatch nummatch have s'_eq: "s' = (fst s \<union> sf_substate, snd s)"
    by (cases s'; cases s) simp
  with p2en have p2en': "p2.plan_action_enabled \<pi> (fst s \<union> sf_substate, snd s)" by simp
  from logmatch have wfs: "wf_world_model s" by simp
  from wfs p2en' have en: "plan_action_enabled \<pi> s"
    using detyped_planaction_enabled_iff by simp
  hence wf_pa: "wf_classical_plan_action \<pi>"
    using plan_action_enabled_def by (simp add: Let_def)

  from logmatch wf_pa
  show logmatch': "logical_states_match (execute_plan_action \<pi> s) (p2.execute_plan_action \<pi> s')"
    using match_state_step by blast

  show "numeric_states_match (execute_plan_action \<pi> s) (p2.execute_plan_action \<pi> s')"
  proof -
    obtain n args where pi: "\<pi> = SimplePlanAction n args" by (cases \<pi>) simp
    from wf_pa obtain ac where res: "resolve_classical_action_schema n = Some ac"
      using wf_pa_refs_ac pi by metis
    from res have res2: "p2.resolve_classical_action_schema n = Some (detype_classical_ac ac)"
      by (rule t_resinst)
    have a_eq: "(the o res_inst) \<pi> = instantiate_classical_action_schema ac args"
      using pi res res_inst_alt by simp
    have a2_eq: "(the o p2.res_inst) \<pi> = instantiate_classical_action_schema (detype_classical_ac ac) args"
      using pi res2 p2.res_inst_alt by simp
    have eff_eq: "ground_action.effect ((the o res_inst) \<pi>) = ground_action.effect ((the o p2.res_inst) \<pi>)"
    proof -
      have "map fst (ac_params ac) = map fst (ac_params (detype_classical_ac ac))"
        by (cases ac rule: ast_classical_action_schema_cases_unfold; simp add: t_ents_names)
      moreover have "ac_eff ac = ac_eff (detype_classical_ac ac)" by simp
      ultimately show ?thesis
        unfolding a_eq a2_eq
        by (cases ac rule: ast_classical_action_schema_cases_unfold) (simp add: ac_tsubst_def)
    qed
    have "snd (execute_plan_action \<pi> s) = action_numeric_update_function ((the o res_inst) \<pi>) (snd s)"
      using execute_plan_action_def apply_ground_action_alt by (cases s) auto
    also have "... = action_numeric_update_function ((the o p2.res_inst) \<pi>) (snd s')"
      using eff_eq nummatch action_numeric_update_function_def by simp
    also have "... = snd (p2.execute_plan_action \<pi> s')"
      using p2.execute_plan_action_def apply_ground_action_alt by (cases s') auto
    finally show ?thesis .
  qed
qed

lemma match_valid_classical_plan_from2':
  assumes "logical_states_match s s'"
      and "numeric_states_match s s'"
      and "p2.valid_classical_plan_from2 s' \<pi>s"
  shows "valid_classical_plan_from2 s \<pi>s"
using assms proof (induction \<pi>s arbitrary: s s')
  case Nil
  hence "valuation s' \<Turnstile>\<^sub>m goal P2" by simp
  hence "valuation s \<Turnstile>\<^sub>m goal P" using Nil match_goal by simp
  thus ?case by simp
next
  case (Cons p ps)
  let ?t = "execute_plan_action p s"
  let ?t' = "p2.execute_plan_action p s'"
  from Cons have enab2: "p2.plan_action_enabled p s'" and valid2: "p2.valid_classical_plan_from2 ?t' ps"
    by simp_all
  from Cons.prems(1,2) enab2 have logmatch': "logical_states_match ?t ?t'"
    and nummatch': "numeric_states_match ?t ?t'"
    using match_state_step' by blast+
  from Cons.prems(1,2) have s'_eq: "s' = (fst s \<union> sf_substate, snd s)"
    by (cases s'; cases s) simp
  with enab2 have "p2.plan_action_enabled p (fst s \<union> sf_substate, snd s)" by simp
  with Cons.prems(1) have enab1: "plan_action_enabled p s"
    using detyped_planaction_enabled_iff by simp
  from logmatch' nummatch' valid2 have "valid_classical_plan_from2 ?t ps"
    using Cons.IH by blast
  with enab1 show ?case by simp
qed

lemma match_valid_classical_plan':
  assumes "p2.valid_classical_plan2 \<pi>s"
  shows "valid_classical_plan2 \<pi>s"
  using assms unfolding valid_classical_plan2_def p2.valid_classical_plan2_def
  using match_valid_classical_plan_from2' inits_match inits_num_match by blast

(* putting it together: *)

theorem detyped_valid_iff:
  "valid_classical_plan2 \<pi>s \<longleftrightarrow> p2.valid_classical_plan2 \<pi>s"
  using match_valid_classical_plan match_valid_classical_plan' by blast

end

subsection \<open> Code Setup \<close>

lemmas type_norm_code =
  domain_signature.wf_action_params_def
  ast_classical_domain.restrict_dom_def
  domain_signature.pred_for_type_def
  domain_signature.type_pred.simps
  domain_signature.type_preds_def
  domain_signature.type_atom.simps
  domain_signature.type_precond.simps
  domain_signature.param_precond_def
  domain_signature.detype_classical_ac.simps
  ast_classical_domain.detype_classical_dom_def
  domain_signature.supertype_facts_for.simps
  domain_signature.supertype_facts_def
  ast_classical_problem.detype_classical_prob_def
  ast_classical_domain.typeless_classical_domain_def
  ast_classical_problem.typeless_classical_problem_def
declare type_norm_code[code]




end
