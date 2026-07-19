theory Classical_Type_Normalization
  imports Classical_Type_Normalization_Locales
    Grounding_Type_Normalization.Type_Normalization_Proofs
begin

section \<open>Type Normalization Proofs (classical)\<close>

text \<open>The classical-AST proofs about \<open>detype_classical_ac\<close>, \<open>detype_classical_dom\<close>/\<open>prob\<close> and the
  \<open>ast_classical_*2\<close> locales: detyping an action schema, the action-level type preconditions, and the
  well-formedness of the detyped classical domain/problem. The reusable, signature-level proofs (the
  detyping infrastructure, the detyped-signature well-formedness, the supertype facts) live in
  \<open>Grounding_Type_Normalization.Type_Normalization_Proofs\<close>.\<close>

subsection \<open>Detyping a classical action schema\<close>

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
   Classical_Type_Normalization_Locales.thy so they are available for the locale rewrites. *)

lemma (in restrict_classical_domain) restrict_D: "\<forall>a \<in> set (actions D). wf_action_params a"
  using restrict_dom restrict_dom_def by auto

subsection \<open>Detyping the action type preconditions\<close>

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

lemma (in domain_signature) params_ts_exist: (* somehow this isn't trivial for the solver *)
  assumes "wf_action_params a" "(n, Either ts) \<in> set (ac_params a)"
  shows "set ts \<subseteq> set type_names"
  using assms wf_action_params_def wf_type_iff_listed
  by blast

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
  have wfa: "wf_classical_action_schema a" using assms wf_D by blast

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

subsection \<open>The initial state of the detyped problem\<close>

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

lemma (in restrict_classical_problem2) t_I_wf:
  "p2.wf_world_model p2.I"
  unfolding p2_I_eq
  using wf_I[THEN t_wm_wf] super_facts_wf by auto

subsection \<open>Detyping the classical domain/problem\<close>

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

sublocale restrict_classical_domain2 \<subseteq> d2_wf: wf_ast_classical_domain D2
  using detype_classical_dom_wf wf_ast_classical_domain.intro by simp

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
