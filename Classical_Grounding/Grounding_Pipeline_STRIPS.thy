theory Grounding_Pipeline_STRIPS
  imports Grounding_Pipeline_Numeric "PDDL_to_STRIPS/Classical_PDDL_to_STRIPS"
    Classical_Variable_Freeness.Classical_Variable_Freeness_Num_Free
begin

text \<open>The numeric-free specialization of the grounding pipeline: it imports the general
  (with-numerics) pipeline \<^verbatim>\<open>Grounding_Pipeline_Numeric\<close> and, on top of the certificate-grounded
  problem \<^term>\<open>P\<^sub>G_cert\<close>, converts it to STRIPS. This branch requires \<^const>\<open>ast_classical_problem.num_free_prob\<close>.\<close>

subsection \<open>The grounder's predicate names are nonempty\<close>

text \<open>The folded predicate names carry a trailing \<open>_<index>\<close> suffix
  (\<^const>\<open>fact_folder.fact_names\<close>, built with \<^const>\<open>idx_name\<close>), hence are nonempty
  unconditionally (\<open>fact_names_nonempty\<close>). This discharges the \<open>nonempty_pred_names\<close>
  side-condition for the grounded problem.\<close>

section \<open>Numeric-freeness bridges the numeric fold re-check to the propositional one\<close>

text \<open>The numeric-free (STRIPS) branch is the numeric branch plus a decidable numeric-freeness
  gate. The two grounding re-checks differ only in their coverage conjuncts ---
  \<^const>\<open>normalized_problem_rx.numeric_fold_checks\<close> uses the numeric-permissive
  \<^const>\<open>covered_num\<close> where \<^const>\<open>normalized_problem_rx.grounding_checks\<close> uses
  \<^const>\<open>covered\<close> --- and in the two numeric-freeness conjuncts, which the numeric re-check
  drops. Numeric-freeness of the input closes both gaps: it turns \<^const>\<open>facts_covered\<close> into
  \<^const>\<open>covered\<close> and forces every reachable operator's numeric-effect list to be empty. The
  remaining conjunct, \<open>init_props\<close>, is \<^emph>\<open>not\<close> derivable --- an object equality
  \<open>Atom (eqAtm a b)\<close> in the initial state is numeric-free but is not a predicate atom --- so it
  stays an explicit assumption of the bridge.\<close>

lemma num_free_fmla_atoms:
  assumes "num_free_fmla \<phi>"
      and "a \<in> atoms \<phi>"
  shows "\<not> is_numeric_atom a"
  using assms by (induction \<phi>) auto

text \<open>\<^const>\<open>covered\<close> is \<^const>\<open>facts_covered\<close> plus the outright rejection of numeric atoms, so
  on a numeric-free formula the two coincide. This is the converse of \<open>covered_imp_covered_num\<close>
  under numeric-freeness.\<close>
lemma covered_of_facts_covered:
  assumes "facts_covered \<phi> facts"
      and "num_free_fmla \<phi>"
  shows "covered \<phi> facts"
  unfolding covered_def
proof
  fix a assume a: "a \<in> atoms \<phi>"
  have nn: "\<not> is_numeric_atom a" using num_free_fmla_atoms[OF assms(2) a] .
  show "(case a of predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> set facts
          | eqAtm x y \<Rightarrow> True | _ \<Rightarrow> False)"
    using nn facts_coveredD[OF assms(1)] a by (cases a) auto
qed

text \<open>\<open>num_free_resinst\<close> of \<^verbatim>\<open>Classical_Variable_Freeness_Num_Free\<close> generalized off
  \<^locale>\<open>varfree_instantiator\<close>: its proof uses the reachable-op well-formedness only, so it is
  stated here with \<open>wf_classical_plan_action\<close> assumed directly. This is what lets the certificate
  layer use it without interpreting \<^locale>\<open>varfree_instantiator\<close> --- which would deduplicate the
  shared \<open>grounder\<close> interpretation of the sibling certificate locales.\<close>
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

context certified_reachability_base
begin

text \<open>\<^bold>\<open>The gate bridge\<close>: the numeric-permissive fold re-check plus numeric-freeness of the
  problem plus a purely propositional initial state give the full propositional re-check. Stated
  in the \<^emph>\<open>shared base\<close> locale and as a plain predicate-level implication, so that no proof ever
  interprets two of the sibling certificate locales at the same parameters.\<close>
lemma grounding_checks_of_num_free:
  assumes nfc: "numeric_fold_checks M"
      and nf: num_free_prob
      and ip: "\<forall>f \<in> set (init P). is_predAtom f"
  shows "grounding_checks M"
proof (unfold grounding_checks_def, intro conjI)
  have nfd: num_free_dom using nf unfolding num_free_prob_def by blast
  show "\<forall>a \<in> set (cert_facts_of M). px.wf_fmla_atom px.objT a"
    using nfc unfolding numeric_fold_checks_def by blast
  show ops_wf: "\<forall>\<pi> \<in> set (cert_ops_of M). wf_classical_plan_action \<pi>"
    using nfc unfolding numeric_fold_checks_def by blast
  show "\<forall>\<pi> \<in> set (cert_ops_of M). let eff = effect (the (res_inst \<pi>))
      in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> (cert_facts_of M)"
    using nfc unfolding numeric_fold_checks_def by blast
  show "\<forall>\<pi> \<in> set (cert_ops_of M). covered (precondition (the (res_inst \<pi>))) (cert_facts_of M)"
  proof
    fix \<pi> assume pi: "\<pi> \<in> set (cert_ops_of M)"
    have fc: "facts_covered (precondition (the (res_inst \<pi>))) (cert_facts_of M)"
      using nfc pi unfolding numeric_fold_checks_def by (blast dest: covered_num_factsD)
    have nfp: "num_free_fmla (precondition (the (res_inst \<pi>)))"
      using num_free_resinst'(1)[OF _ nfd] ops_wf pi by blast
    show "covered (precondition (the (res_inst \<pi>))) (cert_facts_of M)"
      by (rule covered_of_facts_covered[OF fc nfp])
  qed
  show "covered (goal P) (cert_facts_of M)"
  proof (rule covered_of_facts_covered)
    show "facts_covered (goal P) (cert_facts_of M)"
      using nfc unfolding numeric_fold_checks_def by (blast dest: covered_num_factsD)
    show "num_free_fmla (goal P)" using nf unfolding num_free_prob_def by blast
  qed
  show "\<forall>f \<in> set (init P). is_predAtom f" by (rule ip)
  show "\<forall>\<pi> \<in> set (cert_ops_of M). numeric_effects (effect (the (res_inst \<pi>))) = []"
  proof
    fix \<pi> assume pi: "\<pi> \<in> set (cert_ops_of M)"
    have "num_free_eff (effect (the (res_inst \<pi>)))"
      using num_free_resinst'(2)[OF _ nfd] ops_wf pi by blast
    thus "numeric_effects (effect (the (res_inst \<pi>))) = []"
      by (cases "effect (the (res_inst \<pi>))") simp
  qed
qed

end

context ast_classical_problem begin

lemma wf_as_strips_compact:
  "wf_classical_problem \<Longrightarrow> grounded_prob \<Longrightarrow> normalized_prob \<Longrightarrow> num_free_prob \<Longrightarrow> is_valid_problem_strips as_strips"
  using grounded_normalized_numeric_free_problem.wf_as_strips
  unfolding grounded_normalized_numeric_free_problem_def
            grounded_normalized_problem_def grounded_normalized_problem_axioms_def
            grounded_problem_def grounded_problem_axioms_def wf_ast_classical_problem_def
            numeric_free_problem_def
            normalized_prob_def by blast

text \<open>Goal normalization collapses the goal to a single nullary predicate atom, and the
  subsequent stages (definedness explication, precondition splitting, definedness translation)
  leave a non-numeric atom untouched. Hence \<^term>\<open>P\<^sub>T\<close>'s goal is still a single predicate atom.\<close>
lemma goal_P\<^sub>T_single: "\<exists>gp. goal P\<^sub>T = Atom (predAtm gp [])"
proof -
  obtain gp where g3: "goal (ast_classical_problem.degoal_prob detype_classical_prob)
      = Atom (predAtm gp [])"
    using ast_classical_problem.degoal_prob_sel(4) by metis
  have "goal P\<^sub>X = explicate_def_fmla (goal (ast_classical_problem.degoal_prob detype_classical_prob))"
    unfolding P\<^sub>X_def by (simp add: ast_classical_problem.explicate_def_prob_sel(4))
  also have "\<dots> = Atom (predAtm gp [])"
    unfolding g3 explicate_def_fmla_def definedness_atoms_def divisor_zero_atoms_def by simp
  finally have gX: "goal P\<^sub>X = Atom (predAtm gp [])" .
  hence gN: "goal P\<^sub>N = Atom (predAtm gp [])"
    unfolding P\<^sub>N_def using ast_classical_problem.split_prob_sel(4) by metis
  hence "goal P\<^sub>T = Atom (predAtm gp [])"
    unfolding P\<^sub>T_def
    using ast_classical_problem.def_translate_prob_sel(4)[of P\<^sub>N]
    by (simp add: def_translate_fmla_def)
  thus ?thesis by blast
qed

text \<open>Assembling the \<^locale>\<open>strips_encodable_problem\<close> interpretation from the four normalization
  invariants plus the two STRIPS-specific side-conditions.\<close>
lemma strips_encodable_compact:
  assumes "wf_classical_problem" "grounded_prob" "normalized_prob" "num_free_prob"
    and np: "\<And>p. wf_pred p \<Longrightarrow> predicate.name p \<noteq> STR ''''"
    and gnc: "\<And>l1 l2. l1 \<in> set (un_and (goal P)) \<Longrightarrow> l2 \<in> set (un_and (goal P))
       \<Longrightarrow> fst (lit_as_goal l1) = fst (lit_as_goal l2)
       \<Longrightarrow> snd (lit_as_goal l1) = snd (lit_as_goal l2)"
  shows "strips_encodable_problem P"
proof unfold_locales
  show "wf_classical_problem" by (rule assms(1))
  show "grounded_prob" by (rule assms(2))
  show "prec_normed_dom \<and> is_conj (goal P)"
    using assms(3) unfolding normalized_prob_def by blast
  show "num_free_prob" by (rule assms(4))
  show "\<And>p. wf_pred p \<Longrightarrow> predicate.name p \<noteq> STR ''''" using np by blast
  show "\<And>l1 l2. l1 \<in> set (un_and (goal P)) \<Longrightarrow> l2 \<in> set (un_and (goal P))
       \<Longrightarrow> fst (lit_as_goal l1) = fst (lit_as_goal l2)
       \<Longrightarrow> snd (lit_as_goal l1) = snd (lit_as_goal l2)" using gnc by blast
qed

context
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes nonempty: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and grounding_cert: "normalized_problem_rx.grounding_checks P\<^sub>T M"
begin

subsection \<open> Conversion to STRIPS (Certificate-based) \<close>

definition "P\<^sub>S_cert \<equiv> ast_classical_problem.as_strips (P\<^sub>G_cert M)"

lemma wf_as_strips_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "is_valid_problem_strips P\<^sub>S_cert"
proof -
  have nf: "ast_classical_problem.num_free_prob (P\<^sub>G_cert M)"
    using ground_cert_num_free[OF nonempty cert grounding_cert assms] .
  show ?thesis
    unfolding P\<^sub>S_cert_def
    using assms ast_classical_problem.wf_as_strips_compact
          wf_ground_cert_problem[OF nonempty cert grounding_cert assms] nf by blast
qed

text \<open>The grounded goal is a single nullary predicate atom: \<^const>\<open>fact_folder.ground_fmla\<close> maps the
  single-atom goal of \<^term>\<open>P\<^sub>T\<close> (\<open>goal_P\<^sub>T_single\<close>) to one nullary \<^const>\<open>predAtm\<close>.\<close>
lemma goal_P\<^sub>G_cert_single:
  assumes "restrict_prob" "wf_classical_problem"
  shows "\<exists>q. goal (P\<^sub>G_cert M) = Atom (predAtm q [])"
proof -
  interpret cr: certified_reachability P\<^sub>T M dc
    using certified_reachability_i[OF nonempty cert grounding_cert assms] .
  have pg_eq: "P\<^sub>G_cert M = cr.wfg.ground_prob"
    unfolding P\<^sub>G_cert_def[OF nonempty cert grounding_cert]
              cr.cert_facts'_def cr.cert_ops'_def by simp
  obtain gp where g: "goal P\<^sub>T = Atom (predAtm gp [])" using goal_P\<^sub>T_single by blast
  have "goal (P\<^sub>G_cert M) = cr.wfg.ground_fmla (goal P\<^sub>T)"
    unfolding pg_eq using cr.wfg.ground_prob_sel(4) by simp
  also have "\<dots> = Atom (predAtm (the (cr.wfg.fact_map (Atom (predAtm gp [])))) [])"
    unfolding g by simp
  finally show ?thesis by blast
qed

text \<open>Every well-formed predicate of the grounded problem has a nonempty name: the grounder's
  fact names end in an underscore-separated index (\<open>fact_names_nonempty\<close>).\<close>
lemma pg_cert_pred_nonempty:
  assumes "restrict_prob" "wf_classical_problem"
    and "ast_classical_domain.wf_pred (ast_problem.domain (P\<^sub>G_cert M)) n"
  shows "predicate.name n \<noteq> STR ''''"
proof -
  interpret cr: certified_reachability P\<^sub>T M dc
    using certified_reachability_i[OF nonempty cert grounding_cert assms(1,2)] .
  have pg_eq: "P\<^sub>G_cert M = cr.wfg.ground_prob"
    unfolding P\<^sub>G_cert_def[OF nonempty cert grounding_cert]
              cr.cert_facts'_def cr.cert_ops'_def by simp
  from assms(3) have "PredDecl n [] \<in> set (predicates (ast_problem.domain (P\<^sub>G_cert M)))"
    unfolding ast_classical_domain.wf_pred_def .
  hence "PredDecl n [] \<in> set (map (\<lambda>p. PredDecl p []) cr.wfg.fact_names)"
    unfolding pg_eq using cr.wfg.ground_prob_sel(1) cr.wfg.ground_dom_sel(2) by simp
  hence nfn: "n \<in> set cr.wfg.fact_names" by auto
  thus ?thesis using cr.wfg.fact_names_nonempty by blast
qed

lemma strips_encodable_P\<^sub>G_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "strips_encodable_problem (P\<^sub>G_cert M)"
proof -
  note wfg = wf_ground_cert_problem[OF nonempty cert grounding_cert assms]
  obtain q where q: "goal (P\<^sub>G_cert M) = Atom (predAtm q [])"
    using goal_P\<^sub>G_cert_single[OF assms] by blast
  show ?thesis
  proof (rule ast_classical_problem.strips_encodable_compact)
    show "ast_classical_problem.wf_classical_problem (P\<^sub>G_cert M)" using wfg by blast
    show "ast_classical_problem.grounded_prob (P\<^sub>G_cert M)" using wfg by blast
    show "ast_classical_problem.normalized_prob (P\<^sub>G_cert M)" using wfg by blast
    show "ast_classical_problem.num_free_prob (P\<^sub>G_cert M)"
      using ground_cert_num_free[OF nonempty cert grounding_cert assms] .
    show "\<And>p. ast_classical_domain.wf_pred (ast_problem.domain (P\<^sub>G_cert M)) p
              \<Longrightarrow> predicate.name p \<noteq> STR ''''"
      using pg_cert_pred_nonempty[OF assms] by blast
    show "\<And>l1 l2. l1 \<in> set (un_and (goal (P\<^sub>G_cert M)))
       \<Longrightarrow> l2 \<in> set (un_and (goal (P\<^sub>G_cert M)))
       \<Longrightarrow> fst (lit_as_goal l1) = fst (lit_as_goal l2)
       \<Longrightarrow> snd (lit_as_goal l1) = snd (lit_as_goal l2)"
      using q by simp
  qed
qed

text \<open>Soundness of the STRIPS encoding (existence form). The literal whole-plan restoration
  \<open>valid_classical_plan2 (reconstruct_plan_ground_cert M (restore_pddl_plan ops))\<close>
  is \<^emph>\<open>not\<close> provable for the same reason as \<open>restore_pddl_plan_valid\<close>: \<open>execute_serial_plan\<close> halts at
  the first non-applicable operator, so a STRIPS solution may carry trailing non-enabled operators
  that \<^const>\<open>ast_classical_problem.valid_classical_plan2\<close> rejects. We therefore conclude existence
  of a valid plan (the restored \<^emph>\<open>applicable prefix\<close> witnesses it).\<close>
lemma strips_plan_sound_cert:
  assumes "restrict_prob" "wf_classical_problem"
    and "is_serial_solution_for_problem P\<^sub>S_cert ops"
  shows "\<exists>\<pi>s. valid_classical_plan2 \<pi>s"
proof -
  from assms(3) have "is_serial_solution_for_problem (ast_classical_problem.as_strips (P\<^sub>G_cert M)) ops"
    unfolding P\<^sub>S_cert_def .
  with strips_encodable_problem.restore_pddl_plan_valid[OF strips_encodable_P\<^sub>G_cert[OF assms(1,2)]]
  have "\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 (P\<^sub>G_cert M) \<pi>s" by blast
  thus ?thesis using ground_cert_plan_valid_iff[OF nonempty cert grounding_cert assms(1,2)] by blast
qed

text \<open>Solvability equivalence: the grounded problem has a STRIPS serial solution iff the original
  classical problem has a valid plan. This is the end-to-end correctness theorem of the
  numeric-free grounding-to-STRIPS pipeline.\<close>
lemma strips_plan_iff_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "(\<exists>ops. is_serial_solution_for_problem P\<^sub>S_cert ops) \<longleftrightarrow>
    (\<exists>\<pi>s. valid_classical_plan2 \<pi>s)"
proof -
  have "(\<exists>ops. is_serial_solution_for_problem P\<^sub>S_cert ops)
      \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 (P\<^sub>G_cert M) \<pi>s)"
    unfolding P\<^sub>S_cert_def
    using strips_encodable_problem.valid_plan_iff[OF strips_encodable_P\<^sub>G_cert[OF assms]] by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>\<pi>s. valid_classical_plan2 \<pi>s)"
    using ground_cert_plan_valid_iff[OF nonempty cert grounding_cert assms] by blast
  finally show ?thesis .
qed

subsection \<open> Concrete plan reconstruction (STRIPS solution \<open>\<rightarrow>\<close> original PDDL plan) \<close>

text \<open>End-to-end \<^emph>\<open>executable\<close> reconstruction: decode a STRIPS serial solution of \<^term>\<open>P\<^sub>S_cert\<close>
  into a concrete valid plan of the \<^emph>\<open>original\<close> problem \<^term>\<open>P\<close>. Two concrete stages compose:
  \<^const>\<open>ast_classical_problem.restore_prefix\<close> turns the STRIPS solution into a valid plan of the
  grounded problem \<^term>\<open>P\<^sub>G_cert M\<close> (its applicable prefix), and \<^const>\<open>reconstruct_plan_ground_cert\<close>
  lifts that back through grounding + the normalization chain to \<^term>\<open>P\<close>.\<close>
definition "reconstruct_pipeline_plan_cert ops \<equiv>
  reconstruct_plan_ground_cert M
    (ast_classical_problem.restore_prefix (P\<^sub>G_cert M)
       (ast_classical_problem.I (P\<^sub>G_cert M)) ops)"

theorem strips_plan_reconstruct_cert:
  assumes "restrict_prob" "wf_classical_problem"
    and "is_serial_solution_for_problem P\<^sub>S_cert ops"
  shows "valid_classical_plan2 (reconstruct_pipeline_plan_cert ops)"
proof -
  from assms(3) have ser:
    "is_serial_solution_for_problem (ast_classical_problem.as_strips (P\<^sub>G_cert M)) ops"
    unfolding P\<^sub>S_cert_def .
  have v: "ast_classical_problem.valid_classical_plan2 (P\<^sub>G_cert M)
            (ast_classical_problem.restore_prefix (P\<^sub>G_cert M)
               (ast_classical_problem.I (P\<^sub>G_cert M)) ops)"
    using strips_encodable_problem.restore_prefix_valid[OF strips_encodable_P\<^sub>G_cert[OF assms(1,2)] ser] .
  show ?thesis
    unfolding reconstruct_pipeline_plan_cert_def
    using ground_cert_plan_reconstruct[OF nonempty cert grounding_cert assms(1,2) v] .
qed

end

subsection \<open>Pipeline-level form of the numeric-free gate bridge\<close>

text \<open>\<open>P\<^sub>T\<close> is a \<^locale>\<open>normalized_problem_rx\<close> as soon as the input problem is restricted and
  well-formed --- the re-checks play no part in it. Hoisted out of the certificate contexts so
  that the numeric-free bridge below can use it without assuming either gate.\<close>
lemma normalized_problem_rx_P\<^sub>T:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "normalized_problem_rx P\<^sub>T"
proof -
  have wf_N: "ast_classical_problem.wf_classical_problem P\<^sub>N" using rp wf normalization_wf by simp
  have norm_N: "ast_classical_problem.normalized_prob P\<^sub>N" using rp wf normalization_normalizes by simp
  have wf_T: "ast_classical_problem.wf_classical_problem P\<^sub>T"
    using wf_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_prob_wf_compact)
  have norm_T: "ast_classical_problem.normalized_prob P\<^sub>T"
    using norm_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  show ?thesis
    unfolding normalized_problem_rx_def normalized_problem_def'
    using wf_T norm_T by blast
qed

text \<open>The gate bridge at the pipeline level: a certified reachability model that passes the
  \<^emph>\<open>numeric\<close> fold re-check on a numeric-free \<open>P\<^sub>T\<close> with a purely propositional initial state
  passes the \<^emph>\<open>propositional\<close> re-check as well.\<close>
lemma grounding_checks_P\<^sub>T_of_num_free:
  assumes ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
             (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
             (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and fold_cert: "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and nf: "ast_classical_problem.num_free_prob P\<^sub>T"
      and ip: "\<forall>f \<in> set (init P\<^sub>T). is_predAtom f"
      and rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "normalized_problem_rx.grounding_checks P\<^sub>T M"
proof -
  have crb: "certified_reachability_base P\<^sub>T M dc"
  proof -
    interpret rx: normalized_problem_rx P\<^sub>T using normalized_problem_rx_P\<^sub>T[OF rp wf] .
    show ?thesis by unfold_locales (use ne cert in simp_all)
  qed
  show ?thesis
    using certified_reachability_base.grounding_checks_of_num_free[OF crb fold_cert nf ip] .
qed

text \<open>Interpretation helper for the \<^emph>\<open>propositional\<close> certified-reachability locale from the
  numeric-free gate --- the numeric-free counterpart of \<open>certified_reachability_i\<close>, mirroring
  \<open>certified_reachability_fold_num_i\<close> of \<^verbatim>\<open>Grounding_Pipeline_Numeric\<close>.\<close>
lemma certified_reachability_i_num_free:
  assumes ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
             (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
             (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and fold_cert: "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and nf: "ast_classical_problem.num_free_prob P\<^sub>T"
      and ip: "\<forall>f \<in> set (init P\<^sub>T). is_predAtom f"
      and rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "certified_reachability P\<^sub>T M dc"
  by (rule certified_reachability_i[OF ne cert
        grounding_checks_P\<^sub>T_of_num_free[OF ne cert fold_cert nf ip rp wf] rp wf])

subsection \<open>The grounded numeric product \<^emph>\<open>is\<close> the grounded propositional product\<close>

text \<open>The numeric-free certificate context: the same nonempty-universe / certificate pair as the
  propositional block above, but gated on the \<^emph>\<open>numeric\<close> fold re-check plus the numeric-freeness
  triple. It is a strictly different (overlapping) input set --- \<open>grounding_checks\<close> does not imply
  \<open>num_free_prob P\<^sub>T\<close> (it only constrains the \<^emph>\<open>reachable\<close> operators, goal and initial state), and
  \<open>num_free_prob P\<^sub>T\<close> does not imply \<open>grounding_checks\<close> without the fold re-check --- so this block is
  added \<^emph>\<open>alongside\<close> the propositional one, not in place of it.\<close>

context
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes nonempty: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and fold_cert: "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and num_free_T: "ast_classical_problem.num_free_prob P\<^sub>T"
      and init_props: "\<forall>f \<in> set (init P\<^sub>T). is_predAtom f"
begin

text \<open>The propositional gate, re-derived inside this context by the bridge.\<close>
lemma grounding_cert_nf:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "normalized_problem_rx.grounding_checks P\<^sub>T M"
  by (rule grounding_checks_P\<^sub>T_of_num_free[OF nonempty cert fold_cert num_free_T init_props rp wf])

text \<open>\<^bold>\<open>The product identity\<close>: the folded \<^emph>\<open>numeric\<close> product and the one-shot \<^emph>\<open>propositional\<close>
  product are the same term. \<^const>\<open>ast_classical_problem.numeric_P\<^sub>G_cert\<close> reduces to
  \<^const>\<open>grounder.ground_prob\<close> at the certified ops/facts by \<open>numeric_P\<^sub>G_cert_ground_prob\<close>
  (the pipeline form of \<open>ground_prob_factors\<close>), and that is verbatim the body of
  \<open>P\<^sub>G_cert_def\<close>. Hence the whole propositional STRIPS block transfers to the numeric product by
  rewriting, with no re-derivation of the grounder's semantics chain.\<close>
lemma numeric_P\<^sub>G_cert_eq_P\<^sub>G_cert:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "numeric_P\<^sub>G_cert M = P\<^sub>G_cert M"
proof -
  have gcn: "normalized_problem_rx.numeric_grounding_checks P\<^sub>T M"
    by (rule numeric_fold_checks_imp_grounding_checks[OF normalized_problem_rx_P\<^sub>T[OF rp wf] fold_cert])
  show ?thesis
    unfolding numeric_P\<^sub>G_cert_ground_prob[OF nonempty cert gcn fold_cert rp wf]
              P\<^sub>G_cert_def[OF nonempty cert grounding_cert_nf[OF rp wf]]
    by (rule refl)
qed

text \<open>Numeric-freeness of the grounded product --- \<open>ground_cert_num_free\<close> through the identity.
  Together with the input-side stage lemmas (\<open>varfree_inst_prob_num_free\<close>, \<open>fold_prob_num_free\<close>)
  this is the numeric-freeness preservation statement of the grounding stage.\<close>
lemma numeric_ground_cert_num_free:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "ast_classical_problem.num_free_prob (numeric_P\<^sub>G_cert M)"
  unfolding numeric_P\<^sub>G_cert_eq_P\<^sub>G_cert[OF rp wf]
  using ground_cert_num_free[OF nonempty cert grounding_cert_nf[OF rp wf] rp wf] .

subsection \<open>Conversion to STRIPS from the folded numeric product\<close>

text \<open>The final stage applied to the \<^emph>\<open>folded numeric\<close> product. Note
  \<^const>\<open>ast_classical_problem.as_strips\<close> reads only predicates, actions, init and goal --- it
  ignores the declared functions --- which loses nothing here: on a numeric-free domain every
  reachable operator has an empty fluent list, so the fold declares no functions at all.\<close>
definition "numeric_P\<^sub>S_cert \<equiv> ast_classical_problem.as_strips (numeric_P\<^sub>G_cert M)"

lemma numeric_P\<^sub>S_cert_eq_P\<^sub>S_cert:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "numeric_P\<^sub>S_cert = P\<^sub>S_cert M"
  unfolding numeric_P\<^sub>S_cert_def P\<^sub>S_cert_def[OF nonempty cert grounding_cert_nf[OF rp wf]]
            numeric_P\<^sub>G_cert_eq_P\<^sub>G_cert[OF rp wf]
  by (rule refl)

lemma numeric_wf_as_strips_cert:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "is_valid_problem_strips numeric_P\<^sub>S_cert"
  unfolding numeric_P\<^sub>S_cert_eq_P\<^sub>S_cert[OF rp wf]
  using wf_as_strips_cert[OF nonempty cert grounding_cert_nf[OF rp wf] rp wf] .

lemma numeric_goal_P\<^sub>G_cert_single:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "\<exists>q. goal (numeric_P\<^sub>G_cert M) = Atom (predAtm q [])"
  unfolding numeric_P\<^sub>G_cert_eq_P\<^sub>G_cert[OF rp wf]
  using goal_P\<^sub>G_cert_single[OF nonempty cert grounding_cert_nf[OF rp wf] rp wf] .

lemma numeric_pg_cert_pred_nonempty:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
      and n: "ast_classical_domain.wf_pred (ast_problem.domain (numeric_P\<^sub>G_cert M)) n"
  shows "predicate.name n \<noteq> STR ''''"
  by (rule pg_cert_pred_nonempty[OF nonempty cert grounding_cert_nf[OF rp wf] rp wf
        n[unfolded numeric_P\<^sub>G_cert_eq_P\<^sub>G_cert[OF rp wf]]])

lemma numeric_strips_encodable_P\<^sub>G_cert:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "strips_encodable_problem (numeric_P\<^sub>G_cert M)"
  unfolding numeric_P\<^sub>G_cert_eq_P\<^sub>G_cert[OF rp wf]
  using strips_encodable_P\<^sub>G_cert[OF nonempty cert grounding_cert_nf[OF rp wf] rp wf] .

text \<open>Soundness, solvability equivalence and concrete plan reconstruction for the numeric-free
  STRIPS encoding of the folded numeric product. The restorer is the existing
  \<^const>\<open>ast_classical_problem.reconstruct_pipeline_plan_cert\<close> --- the two products are the same
  term, so no new restore map is needed.\<close>
lemma numeric_strips_plan_sound_cert:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
      and ser: "is_serial_solution_for_problem numeric_P\<^sub>S_cert ops"
  shows "\<exists>\<pi>s. valid_classical_plan2 \<pi>s"
  using strips_plan_sound_cert[OF nonempty cert grounding_cert_nf[OF rp wf] rp wf
        ser[unfolded numeric_P\<^sub>S_cert_eq_P\<^sub>S_cert[OF rp wf]]] .

lemma numeric_strips_plan_iff_cert:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "(\<exists>ops. is_serial_solution_for_problem numeric_P\<^sub>S_cert ops) \<longleftrightarrow>
    (\<exists>\<pi>s. valid_classical_plan2 \<pi>s)"
  unfolding numeric_P\<^sub>S_cert_eq_P\<^sub>S_cert[OF rp wf]
  using strips_plan_iff_cert[OF nonempty cert grounding_cert_nf[OF rp wf] rp wf] .

theorem numeric_strips_plan_reconstruct_cert:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
      and ser: "is_serial_solution_for_problem numeric_P\<^sub>S_cert ops"
  shows "valid_classical_plan2 (reconstruct_pipeline_plan_cert M ops)"
  using strips_plan_reconstruct_cert[OF nonempty cert grounding_cert_nf[OF rp wf] rp wf
        ser[unfolded numeric_P\<^sub>S_cert_eq_P\<^sub>S_cert[OF rp wf]]] .

end

end

section \<open>Input-side numeric-freeness preservation through the normalization pipeline\<close>

text \<open>The user-facing guarantee behind the numeric-free (STRIPS) branch: a numeric-free PDDL task
  stays numeric-free all the way through the normalization chain, so \<^term>\<open>P\<^sub>T\<close> --- the problem the
  grounding gate is checked against --- inherits \<^const>\<open>ast_classical_problem.num_free_prob\<close> from the
  input. The chain follows \<^term>\<open>P\<^sub>T\<close>'s own assembly in
  \<^theory>\<open>Classical_Grounding.Grounding_Pipeline_Numeric\<close>:
  \<^const>\<open>ast_classical_problem.detype_classical_prob\<close> \<open>\<rightarrow>\<close>
  \<^const>\<open>ast_classical_problem.degoal_prob\<close> \<open>\<rightarrow>\<close>
  \<^const>\<open>ast_classical_problem.explicate_def_prob\<close> (\<open>P\<^sub>X\<close>) \<open>\<rightarrow>\<close>
  \<^const>\<open>ast_classical_problem.split_prob\<close> (\<open>P\<^sub>N\<close>) \<open>\<rightarrow>\<close>
  \<^const>\<open>ast_classical_problem.def_translate_prob\<close> (\<open>P\<^sub>T\<close>).

  \<^bold>\<open>Placement.\<close> These lemmas belong stage-locally, next to each stage's well-formedness
  preservation (mirroring \<^verbatim>\<open>Classical_Variable_Freeness_Num_Free\<close>). They are collected here in the
  top session instead, because every stage theory sits inside a prebuilt session image; the
  relocation into \<open>Classical_<Stage>/Classical_<Stage>_Num_Free.thy\<close> is deferred to the next heap
  rebuild.\<close>

subsection \<open>Numeric-freeness of a formula, atom-wise\<close>

text \<open>The introduction rule dual to \<open>num_free_fmla_atoms\<close> above: a formula all of whose atoms are
  non-numeric is numeric-free. Together the two make \<^const>\<open>num_free_fmla\<close> an atom-set property,
  which is what carries it through the atom-preserving stages (DNF splitting).\<close>
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

subsection \<open>Stage 1: type normalization (detyping)\<close>

text \<open>Detyping rewrites types and parameters only: it conjoins the generated type preconditions onto
  every action's precondition and appends the supertype facts to the initial state. Both are built
  from \<^const>\<open>domain_signature.type_atom\<close>, i.e.\ plain \<^const>\<open>predAtm\<close>s, so nothing numeric enters.\<close>

lemma (in domain_signature) num_free_fmla_type_precond: "num_free_fmla (type_precond p)"
proof (cases p rule: type_precond.cases)
  case (1 v ts)
  show ?thesis
    unfolding 1 type_precond.simps
    by (rule num_free_fmla_BigOr) auto
qed

lemma (in domain_signature) num_free_fmla_param_precond: "num_free_fmla (param_precond ps)"
  unfolding param_precond_def
  by (rule num_free_fmla_BigAnd) (auto simp: num_free_fmla_type_precond)

lemma (in domain_signature) num_free_ac_detype_classical_ac:
  assumes "num_free_ac a"
  shows "num_free_ac (detype_classical_ac a)"
  using assms unfolding num_free_ac_def by (simp add: num_free_fmla_param_precond)

text \<open>The restriction assumption \<open>restrict_prob\<close> is what makes the supertype facts well defined ---
  \<^const>\<open>domain_signature.supertype_facts_for\<close> is \<^const>\<open>undefined\<close> on a non-primitive constant type
  --- so it is needed even though detyping itself is numeric-blind.\<close>
lemma (in ast_classical_problem) restrict_prob_sigD:
  assumes restrict_prob
  shows restrict_prob_sig
  using assms unfolding restrict_prob_def restrict_dom_def restrict_prob_sig_def by blast

lemma (in ast_classical_problem) supertype_facts_predAtom':
  assumes rp: restrict_prob
  shows "\<forall>\<phi> \<in> set (supertype_facts all_consts). is_predAtom \<phi>"
proof -
  interpret rp2: restrict_problem_signature
      "types D" "predicates D" "functions D" "consts D" "objects P"
    using restrict_prob_sigD[OF rp] by unfold_locales
  show ?thesis by (rule rp2.supertype_facts_predAtom)
qed

theorem (in ast_classical_problem) detype_prob_num_free:
  assumes rp: restrict_prob
      and nf: num_free_prob
  shows "ast_classical_problem.num_free_prob detype_classical_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom D2"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions D2)"
    then obtain a' where a: "a = detype_classical_ac a'"
      and a'in: "a' \<in> set (actions D)"
      unfolding detype_classical_dom_sel by auto
    have "num_free_ac a'" using nf a'in unfolding num_free_prob_def num_free_dom_def by blast
    thus "num_free_ac a" unfolding a by (rule num_free_ac_detype_classical_ac)
  qed
  have init: "\<forall>f \<in> set (init P2). num_free_fmla f"
  proof
    fix f assume "f \<in> set (init P2)"
    hence "f \<in> set (supertype_facts all_consts) \<or> f \<in> set (init P)"
      unfolding detype_classical_prob_sel by auto
    thus "num_free_fmla f"
      using supertype_facts_predAtom'[OF rp] num_free_fmla_of_predAtom
            nf[unfolded num_free_prob_def] by blast
  qed
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom init nf unfolding num_free_prob_def by simp
qed

subsection \<open>Stage 2: goal normalization (degoaling)\<close>

text \<open>Degoaling adds one action whose precondition is the (numeric-free) goal under the
  \<^const>\<open>term.CONST\<close> lift and whose effect adds the fresh nullary goal predicate; the new goal is
  that same predicate atom. The initial state is untouched.\<close>

lemma (in ast_classical_problem) num_free_ac_goal_ac:
  assumes "num_free_fmla g"
  shows "num_free_ac (goal_ac g)"
  using assms unfolding num_free_ac_def goal_ac_def by simp

theorem (in ast_classical_problem) degoal_prob_num_free:
  assumes nf: num_free_prob
  shows "ast_classical_problem.num_free_prob degoal_prob"
proof -
  have tg: "num_free_fmla term_goal"
    using nf unfolding num_free_prob_def term_goal_def by simp
  have dom: "ast_classical_domain.num_free_dom D3"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions D3)"
    hence "a = goal_ac term_goal \<or> a \<in> set (actions D)" unfolding degoal_dom_sel by simp
    thus "num_free_ac a"
      using num_free_ac_goal_ac[OF tg] nf unfolding num_free_prob_def num_free_dom_def by blast
  qed
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom nf unfolding num_free_prob_def by simp
qed

subsection \<open>Stage 3: definedness explication\<close>

text \<open>The stage with actual content. \<^const>\<open>explicate_def_fmla\<close> conjoins one reflexive numeric
  equality per primitive numeric expression of the formula and one nonzero witness \<open>\<^bold>\<not>(y = 0)\<close> per
  divisor sub-expression. Both lists are enumerated \<^emph>\<open>from the numeric atoms\<close>
  (\<^const>\<open>atom_enumerate_primitive_numeric_expressions\<close> and
  \<^const>\<open>atom_enumerate_divisor_expressions\<close> return \<^term>\<open>[]\<close> on \<^const>\<open>predAtm\<close>/\<^const>\<open>eqAtm\<close>), so a
  numeric-free formula enumerates nothing at all and both prefixes are empty: explication is the
  \<^emph>\<open>identity\<close> on the numeric-free fragment. Preservation is then immediate --- in particular the
  division-by-zero witnesses, which sit in a second prefix segment after the \<open>f = f\<close> equalities,
  never appear.\<close>

lemma atom_enumerate_pne_num_free:
  assumes "\<not> is_numeric_atom a"
  shows "atom_enumerate_primitive_numeric_expressions a = []"
  using assms by (cases a) simp_all

lemma atom_enumerate_divisor_num_free:
  assumes "\<not> is_numeric_atom a"
  shows "atom_enumerate_divisor_expressions a = []"
  using assms by (cases a) simp_all

lemma definedness_atoms_num_free:
  assumes "num_free_fmla \<phi>"
  shows "definedness_atoms \<phi> = []"
proof -
  have "set (formula_enumerate_primitive_numeric_expressions \<phi>) = {}"
    unfolding set_formula_enumerate_primitive_numeric_expressions_conv
    using atom_enumerate_pne_num_free num_free_fmla_atoms[OF assms] by auto
  hence "formula_enumerate_primitive_numeric_expressions \<phi> = []" by simp
  thus ?thesis unfolding definedness_atoms_def Let_def by simp
qed

lemma divisor_zero_atoms_num_free:
  assumes "num_free_fmla \<phi>"
  shows "divisor_zero_atoms \<phi> = []"
proof -
  have "set (formula_enumerate_divisor_expressions \<phi>) = {}"
    unfolding set_formula_enumerate_divisor_expressions_conv
    using atom_enumerate_divisor_num_free num_free_fmla_atoms[OF assms] by auto
  hence "formula_enumerate_divisor_expressions \<phi> = []" by simp
  thus ?thesis unfolding divisor_zero_atoms_def by simp
qed

lemma explicate_def_fmla_num_free_id:
  assumes "num_free_fmla \<phi>"
  shows "explicate_def_fmla \<phi> = \<phi>"
  unfolding explicate_def_fmla_def
            definedness_atoms_num_free[OF assms] divisor_zero_atoms_num_free[OF assms]
  by simp

lemma num_free_ac_explicate_def_ac:
  assumes "num_free_ac a"
  shows "num_free_ac (explicate_def_ac a)"
  using assms unfolding num_free_ac_def by (simp add: explicate_def_fmla_num_free_id)

theorem (in ast_classical_problem) explicate_def_prob_num_free:
  assumes nf: num_free_prob
  shows "ast_classical_problem.num_free_prob explicate_def_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom explicate_def_dom"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions explicate_def_dom)"
    then obtain a' where a: "a = explicate_def_ac a'"
      and a'in: "a' \<in> set (actions D)"
      unfolding explicate_def_dom_sel by auto
    have "num_free_ac a'" using nf a'in unfolding num_free_prob_def num_free_dom_def by blast
    thus "num_free_ac a" unfolding a by (rule num_free_ac_explicate_def_ac)
  qed
  have goal: "num_free_fmla (goal explicate_def_prob)"
    using nf unfolding num_free_prob_def by (simp add: explicate_def_fmla_num_free_id)
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom goal nf unfolding num_free_prob_def by simp
qed

subsection \<open>Stage 4: precondition splitting\<close>

text \<open>Splitting copies each action once per DNF disjunct of its precondition, keeping the effect
  verbatim. Every disjunct's atom set is a subset of the original's (\<open>dnf_list_atoms\<close>), so
  numeric-freeness --- an atom-set property --- is inherited by each copy.\<close>

lemma num_free_fmla_dnf_list:
  assumes "num_free_fmla \<phi>"
      and "c \<in> set (dnf_list \<phi>)"
  shows "num_free_fmla c"
proof (rule num_free_fmla_atomsI)
  fix a assume a: "a \<in> atoms c"
  have "atoms c \<subseteq> atoms \<phi>" using dnf_list_atoms assms(2) by fast
  hence "a \<in> atoms \<phi>" using a by blast
  thus "\<not> is_numeric_atom a" using num_free_fmla_atoms[OF assms(1)] by blast
qed

lemma (in ast_classical_domain) num_free_ac_split_ac:
  assumes nfa: "num_free_ac a"
      and mem: "a' \<in> set (split_ac a)"
  shows "num_free_ac a'"
proof -
  have "num_free_fmla (ac_pre a')"
    using num_free_fmla_dnf_list split_ac_sel(3)[OF mem] nfa
    unfolding num_free_ac_def by blast
  thus ?thesis using nfa split_ac_sel(4)[OF mem] unfolding num_free_ac_def by simp
qed

theorem (in ast_classical_problem) split_prob_num_free:
  assumes nf: num_free_prob
  shows "ast_classical_problem.num_free_prob split_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom D4"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a' assume "a' \<in> set (actions D4)"
    then obtain a where a: "a \<in> set (actions D)"
      and a': "a' \<in> set (split_ac a)"
      unfolding split_dom_sel split_acs_def by auto
    have "num_free_ac a" using nf a unfolding num_free_prob_def num_free_dom_def by blast
    thus "num_free_ac a'" using a' by (rule num_free_ac_split_ac)
  qed
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom nf unfolding num_free_prob_def by simp
qed

subsection \<open>Stage 5: definedness translation\<close>

text \<open>The translation rewrites a reflexive numeric equality \<open>f = f\<close> into the propositional
  \<open>Defined_f\<close> atom and leaves every other atom alone, so it maps non-numeric atoms to non-numeric
  atoms. On numeric-free input it additionally has nothing to add: by stage 3 the numeric-effect
  list of every action is empty, hence the read/written PNE lists are empty and neither the
  precondition's \<open>Defined_\<close> prefix nor the effect's \<open>Defined_\<close> adds are generated; and no initial
  fact is a function assignment, so \<^const>\<open>init_def_fact\<close> filters everything out.\<close>

lemma is_numeric_atom_def_translate_atom:
  assumes "\<not> is_numeric_atom a"
  shows "\<not> is_numeric_atom (def_translate_atom pfx a)"
  using assms by (cases a) simp_all

lemma num_free_fmla_def_translate_fmla:
  assumes "num_free_fmla \<phi>"
  shows "num_free_fmla (def_translate_fmla pfx \<phi>)"
  using assms unfolding def_translate_fmla_def
  by (induction \<phi>) (simp_all add: is_numeric_atom_def_translate_atom)

lemma init_def_fact_num_free:
  assumes "num_free_fmla f"
  shows "init_def_fact pfx f = None"
proof (cases f)
  case (Atom a)
  hence "\<not> is_numeric_atom a" using assms by simp
  thus ?thesis unfolding Atom init_def_fact_def by (cases a) simp_all
qed (simp_all add: init_def_fact_def)

lemma map_filter_init_def_fact_num_free:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> num_free_fmla f"
  shows "List.map_filter (init_def_fact pfx) fs = []"
  using assms by (induction fs) (simp_all add: init_def_fact_num_free)

lemma num_free_ac_def_translate_ac:
  assumes nfa: "num_free_ac a"
  shows "num_free_ac (def_translate_ac pfx a)"
proof -
  obtain h b where a: "a = SimpleActionSchema h b" by (cases a)
  obtain pre eff where b: "b = SimpleActionBody pre eff" by (cases b)
  obtain ads dls neffs where e: "eff = Effect ads dls neffs" by (cases eff)
  have ne: "neffs = []" using nfa unfolding a b e num_free_ac_def by simp
  have pre_nf: "num_free_fmla pre" using nfa unfolding a b num_free_ac_def by simp
  show ?thesis
    unfolding a b e ne def_translate_ac.simps Let_def num_free_ac_def
    using nfa[unfolded a b e num_free_ac_def]
    by (simp add: num_free_fmla_def_translate_fmla pre_nf)
qed

theorem (in ast_classical_problem) def_translate_prob_num_free:
  assumes nf: num_free_prob
  shows "ast_classical_problem.num_free_prob def_translate_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom DT"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions DT)"
    then obtain a' where a: "a = def_translate_ac def_prefix a'"
      and a'in: "a' \<in> set (actions D)"
      unfolding def_translate_dom_sel by auto
    have "num_free_ac a'" using nf a'in unfolding num_free_prob_def num_free_dom_def by blast
    thus "num_free_ac a" unfolding a by (rule num_free_ac_def_translate_ac)
  qed
  have goal: "num_free_fmla (goal PT)"
    using nf unfolding num_free_prob_def by (simp add: num_free_fmla_def_translate_fmla)
  have init: "\<forall>f \<in> set (init PT). num_free_fmla f"
    using nf unfolding num_free_prob_def by (simp add: map_filter_init_def_fact_num_free)
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def using dom goal init by simp
qed

subsection \<open>Composition: the normalized problem \<^term>\<open>P\<^sub>T\<close> is numeric-free\<close>

lemma (in ast_classical_problem) P\<^sub>X_num_free:
  assumes rp: restrict_prob
      and nf: num_free_prob
  shows "ast_classical_problem.num_free_prob P\<^sub>X"
  unfolding P\<^sub>X_def
  using detype_prob_num_free[OF rp nf]
        ast_classical_problem.degoal_prob_num_free
        ast_classical_problem.explicate_def_prob_num_free
  by blast

lemma (in ast_classical_problem) P\<^sub>N_num_free:
  assumes rp: restrict_prob
      and nf: num_free_prob
  shows "ast_classical_problem.num_free_prob P\<^sub>N"
  unfolding P\<^sub>N_def
  using P\<^sub>X_num_free[OF rp nf] ast_classical_problem.split_prob_num_free by blast

text \<open>\<^bold>\<open>The tier-4 headline\<close>: a numeric-free input problem normalizes to a numeric-free \<^term>\<open>P\<^sub>T\<close>.\<close>
theorem (in ast_classical_problem) P\<^sub>T_num_free:
  assumes rp: restrict_prob
      and nf: num_free_prob
  shows "ast_classical_problem.num_free_prob P\<^sub>T"
  unfolding P\<^sub>T_def
  using P\<^sub>N_num_free[OF rp nf] ast_classical_problem.def_translate_prob_num_free by blast

subsection \<open>The initial state stays purely propositional\<close>

text \<open>The remaining conjunct of the numeric-free gate, \<open>init_props\<close>, is not implied by
  numeric-freeness (an object equality \<open>Atom (eqAtm a b)\<close> is numeric-free but not a predicate atom).
  It is, however, \<^emph>\<open>preserved\<close>: the only facts normalization adds to the initial state are the
  supertype facts of detyping --- plain predicate atoms --- since on numeric-free input the
  definedness translation's \<^const>\<open>init_def_fact\<close> filter yields nothing.\<close>

lemma (in ast_classical_problem) init_P\<^sub>N_eq: "init P\<^sub>N = init detype_classical_prob"
  unfolding P\<^sub>N_def P\<^sub>X_def
  by (simp add: ast_classical_problem.split_prob_sel(3)
                ast_classical_problem.explicate_def_prob_sel(3)
                ast_classical_problem.degoal_prob_sel(3))

lemma (in ast_classical_problem) init_P\<^sub>T_eq:
  assumes rp: restrict_prob
      and nf: num_free_prob
  shows "init P\<^sub>T = init detype_classical_prob"
proof -
  have nf2: "\<forall>f \<in> set (init detype_classical_prob). num_free_fmla f"
    using detype_prob_num_free[OF rp nf]
    unfolding ast_classical_problem.num_free_prob_def by blast
  have mf: "List.map_filter (init_def_fact pfx) (init detype_classical_prob) = []" for pfx
    using nf2 by (blast intro: map_filter_init_def_fact_num_free)
  show ?thesis
    unfolding P\<^sub>T_def
    by (simp only: ast_classical_problem.def_translate_prob_sel(3) init_P\<^sub>N_eq mf
                   remdups.simps(1) append_Nil2)
qed

theorem (in ast_classical_problem) init_P\<^sub>T_props:
  assumes rp: restrict_prob
      and nf: num_free_prob
      and ip: "\<forall>f \<in> set (init P). is_predAtom f"
  shows "\<forall>f \<in> set (init P\<^sub>T). is_predAtom f"
  unfolding init_P\<^sub>T_eq[OF rp nf] detype_classical_prob_sel
  using supertype_facts_predAtom'[OF rp] ip by auto

subsection \<open>The input-side form of the numeric-free gate\<close>

text \<open>Tier 4 composed with the tier-1 gate bridge: the two numeric-freeness conjuncts of the
  numeric-free gate are discharged from \<^emph>\<open>input-side\<close> hypotheses, so all that is left to check on
  the normalized problem is the numeric fold re-check. This is the user-facing statement ``a
  numeric-free PDDL task with a purely propositional initial state passes the numeric-free grounding
  gate''.\<close>

theorem (in ast_classical_problem) grounding_checks_P\<^sub>T_of_num_free_input:
  assumes ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
             (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
             (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and fold_cert: "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and rp: restrict_prob
      and wf: wf_classical_problem
      and nf: num_free_prob
      and ip: "\<forall>f \<in> set (init P). is_predAtom f"
  shows "normalized_problem_rx.grounding_checks P\<^sub>T M"
  by (rule grounding_checks_P\<^sub>T_of_num_free[OF ne cert fold_cert
        P\<^sub>T_num_free[OF rp nf] init_P\<^sub>T_props[OF rp nf ip] rp wf])

theorem (in ast_classical_problem) certified_reachability_i_num_free_input:
  assumes ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
             (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
             (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and fold_cert: "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and rp: restrict_prob
      and wf: wf_classical_problem
      and nf: num_free_prob
      and ip: "\<forall>f \<in> set (init P). is_predAtom f"
  shows "certified_reachability P\<^sub>T M dc"
  by (rule certified_reachability_i_num_free[OF ne cert fold_cert
        P\<^sub>T_num_free[OF rp nf] init_P\<^sub>T_props[OF rp nf ip] rp wf])

text \<open>\<^bold>\<open>Executable corollary (deferred).\<close> The executable twin --- from \<open>num_free_prob P\<close> plus
  \<open>numeric_fold_checks_exec\<close> plus the input \<open>is_predAtom\<close> check conclude \<open>strips_fold_checks_exec\<close>
  --- is a one-line assembly of \<open>P\<^sub>T_num_free\<close> and \<open>init_P\<^sub>T_props\<close> against
  \<open>strips_fold_checks_exec_def\<close>, but that gate is defined \<^emph>\<open>downstream\<close> in
  \<^verbatim>\<open>Grounding_Pipeline_STRIPS_Executable\<close>, so it cannot be stated here. It belongs next to that
  definition.\<close>

end
