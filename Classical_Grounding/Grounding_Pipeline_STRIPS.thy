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
end
