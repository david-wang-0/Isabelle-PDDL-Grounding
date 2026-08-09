theory Grounding_Pipeline_Numeric
  imports Grounding_Pipeline_Common
begin

text \<open>The \<^emph>\<open>numeric-fluent-retaining\<close> grounding branch: on top of the shared transformation
  chain of \<^verbatim>\<open>Grounding_Pipeline_Common\<close> it grounds \<^term>\<open>P\<^sub>T\<close> against a certified
  reachability model with the numeric grounder, ending at \<^term>\<open>numeric_P\<^sub>G_cert\<close>. The
  propositional grounder and the STRIPS conversion live downstream in
  \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close>.

  \<^bold>\<open>The two grounding stages.\<close> Grounding is not one step but two, and both are proven
  well-formedness- and plan-preserving separately, so a caller may stop after either:
  \<^item> \<^emph>\<open>grounding stage 1, instantiation\<close> --- \<open>numeric_P\<^sub>V_cert\<close>: every reachable operator of the
    certificate is instantiated into a parameterless action, so the domain becomes variable-free
    while its atoms keep their arguments (\<open>at(ball1, roomA)\<close> stays a binary atom);
  \<^item> \<^emph>\<open>grounding stage 2, folding\<close> --- \<open>numeric_P\<^sub>G_cert\<close>: the certified facts and the reachable ground
    fluents are folded to \<^emph>\<open>fresh nullary names\<close>, so the result is purely propositional in its
    predicates while genuine numeric effects survive on the nullary fluents.

  Each stage is gated by its own re-check of the untrusted reachability model --- the coverage
  obligations \<open>numeric_grounding_checks\<close> for the instantiation, the stronger
  \<open>numeric_fold_checks\<close> for the fold --- which is what keeps the reachability oracle out of the
  trusted base.\<close>

context ast_classical_problem begin

subsection \<open>Grounding against a certified reachability model (numeric)\<close>

text \<open>The numeric analogue of the propositional certificate-grounding block above: the same certified
  reachability model
  \<open>(M, dc)\<close> now drives the \<^emph>\<open>numeric-fluent-retaining\<close> grounder \<^const>\<open>varfree.varfree_inst_prob\<close>
  instead of the propositional fold of the STRIPS branch. Well-formedness and plan-preservation
  are inherited from \<open>varfree_instantiator.varfree_inst_prob_wf\<close> /
  \<open>varfree_instantiator.varfree_valid_classical_plan_iff\<close> via the \<open>cr.vfi\<close> interpretation of the
  \<^emph>\<open>weaker\<close> \<^locale>\<open>certified_reachability_num\<close> --- which requires only
  \<open>numeric_grounding_checks\<close> (the five coverage obligations), \<^emph>\<open>not\<close> the numeric-freeness checks
  \<open>init_props\<close>/\<open>ops_no_num\<close> that the propositional \<^locale>\<open>certified_reachability\<close> imposes. This is
  what lets a task with genuine numeric effects (whose reachable ops carry \<open>NumericEffect\<close>s) pass the
  re-check and be grounded with those effects retained. (Note \<^const>\<open>varfree.varfree_inst_prob\<close>
  takes only \<open>P\<close> and \<open>ops\<close> --- the grounder's \<open>facts\<close> parameter is unused, so the locale drops it
  from the constant's signature.)\<close>

text \<open>Interpretation helper for the numeric certified-reachability locale, mirroring
  \<open>certified_reachability_i\<close> but discharging the \<^emph>\<open>weaker\<close> \<open>numeric_grounding_checks\<close> re-check
  (so it applies to a task whose reachable ops still carry numeric effects).\<close>
lemma certified_reachability_num_i:
  assumes "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and "dl_certified_model
             (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
             (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and "normalized_problem_rx.numeric_grounding_checks P\<^sub>T M"
      and "restrict_prob" "wf_classical_problem"
  shows "certified_reachability_num P\<^sub>T M dc"
proof -
  interpret rx: normalized_problem_rx P\<^sub>T using normalized_problem_rx_P\<^sub>T[OF assms(4) assms(5)] .
  show ?thesis
    apply unfold_locales
    using assms(1,2,3)
    by simp_all
qed

text \<open>Interpretation helper for the \<^emph>\<open>folded\<close> numeric certified-reachability locale --- the
  sibling that additionally re-checks the numeric-permissive coverage obligations
  (\<open>numeric_fold_checks\<close>), so that the fact/fluent fold may run on top of the instantiation.
  Verbatim mirror of \<open>certified_reachability_num_i\<close> with the stronger check.\<close>
lemma certified_reachability_fold_num_i:
  assumes "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and "dl_certified_model
             (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
             (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and "restrict_prob" "wf_classical_problem"
  shows "certified_reachability_fold_num P\<^sub>T M dc"
proof -
  interpret rx: normalized_problem_rx P\<^sub>T using normalized_problem_rx_P\<^sub>T[OF assms(4) assms(5)] .
  show ?thesis
    apply unfold_locales
    using assms(1,2,3)
    by simp_all
qed

text \<open>The fold re-check subsumes the instantiation re-check (its first conjunct), so a task that
  passes \<open>numeric_fold_checks\<close> also passes \<open>numeric_grounding_checks\<close> and both stage-1 and
  stage-2 products are available for it.\<close>
lemma numeric_fold_checks_imp_grounding_checks:
  assumes "normalized_problem_rx P\<^sub>T"
      and "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
  shows "normalized_problem_rx.numeric_grounding_checks P\<^sub>T M"
  using assms(2)
  unfolding normalized_problem_rx.numeric_fold_checks_def[OF assms(1)]
            normalized_problem_rx.numeric_grounding_checks_def[OF assms(1)]
  by blast

context
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes nonempty: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and grounding_cert_num: "normalized_problem_rx.numeric_grounding_checks P\<^sub>T M"
begin

text \<open>The certificate context, shared by both grounding stages. It fixes an \<^emph>\<open>untrusted\<close>
  reachability answer --- a fact list \<open>M\<close> and a datalog certificate \<open>dc\<close> justifying it --- and
  assumes exactly three things about it: the object universe of \<open>P\<^sub>R\<close> is nonempty, \<open>dc\<close> passes
  the verified certificate checker for the rules read off \<open>P\<^sub>R\<close>, and \<open>M\<close> passes the
  instantiation's coverage re-check. Nothing assumes where \<open>M\<close> came from: an external datalog engine, the verified
  evaluator, or a hostile source all lead to the same theorems, because everything about \<open>M\<close> that
  the proofs use is re-established by the checks.\<close>

subsubsection \<open>Stage 1: the variable-free instantiation\<close>

text \<open>The instantiation product: one parameterless action per certified reachable operator. This is
  where the combinatorial work of grounding happens --- \<open>cert_ops_of\<close> enumerates the operators the
  certificate justifies, \<open>canon\<close> deduplicates them into a canonical order --- and it is already a
  legitimate PDDL problem, so a caller wanting variable-free-but-not-propositional output can stop
  here. Atoms are still applied to object arguments; only the \<^emph>\<open>actions\<close> have lost their
  parameters.\<close>
definition "numeric_P\<^sub>V_cert \<equiv> varfree.varfree_inst_prob P\<^sub>T
  (canon (normalized_problem_rx.cert_ops_of P\<^sub>T M))"

lemma numeric_wf_varfree_cert_problem:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.wf_classical_problem numeric_P\<^sub>V_cert"
proof -
  interpret cr: certified_reachability_num P\<^sub>T M dc
    using certified_reachability_num_i[OF nonempty cert grounding_cert_num assms] .
  have pg_eq: "numeric_P\<^sub>V_cert = cr.vfi.varfree_inst_prob"
    unfolding numeric_P\<^sub>V_cert_def cr.cert_ops'_def by simp
  show ?thesis unfolding pg_eq using cr.vfi.varfree_inst_prob_wf by simp
qed

lemma varfree_inst_cert_plan_valid_iff:
  assumes "restrict_prob" "wf_classical_problem"
  shows "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>V_cert \<pi>s')"
proof -
  interpret cr: certified_reachability_num P\<^sub>T M dc
    using certified_reachability_num_i[OF nonempty cert grounding_cert_num assms] .
  have "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>N \<pi>s')"
    using assms normalization_valid_iff by simp
  also have "... \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>T \<pi>s')"
    using ast_classical_problem.def_translate_valid_iff_compact[OF normalization_wf[OF assms] P\<^sub>N_def_explicated_conj[OF assms]]
    unfolding P\<^sub>T_def by simp
  also have "... \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>V_cert \<pi>s')"
    unfolding numeric_P\<^sub>V_cert_def
    using cr.vfi.varfree_valid_classical_plan_iff[unfolded cr.cert_ops'_def] by simp
  finally show ?thesis .
qed

definition "numeric_reconstruct_plan_varfree_cert \<pi>s \<equiv>
  reconstruct_plan_norm (restore_plan_def_translate
    (varfree.restore_ground_plan (canon (normalized_problem_rx.cert_ops_of P\<^sub>T M)) \<pi>s))"

text \<open>Plan restoration: a valid plan of the variable-free instantiation restores to a
  \<^emph>\<open>concrete\<close> valid plan of the original \<open>P\<close> (undo instantiation \<open>\<rightarrow>\<close> def-translation \<open>\<rightarrow>\<close>
  normalization). Numeric twin of \<open>ground_cert_plan_reconstruct\<close>, using the numeric grounder's
  constructive restore \<open>varfree_valid_plan_left\<close> (\<^const>\<open>varfree.restore_ground_plan\<close>).\<close>
lemma varfree_inst_cert_plan_reconstruct:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>V_cert \<pi>s \<Longrightarrow>
    valid_classical_plan2 (numeric_reconstruct_plan_varfree_cert \<pi>s)"
proof -
  assume p: "ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>V_cert \<pi>s"
  interpret cr: certified_reachability_num P\<^sub>T M dc
    using certified_reachability_num_i[OF nonempty cert grounding_cert_num assms] .
  let ?q = "varfree.restore_ground_plan (canon (normalized_problem_rx.cert_ops_of P\<^sub>T M)) \<pi>s"
  have "ast_classical_problem.valid_classical_plan2 P\<^sub>T ?q"
    using p[unfolded numeric_P\<^sub>V_cert_def] cr.vfi.varfree_valid_plan_left[unfolded cr.cert_ops'_def] by simp
  hence "ast_classical_problem.valid_classical_plan2 (ast_classical_problem.def_translate_prob P\<^sub>N) ?q"
    unfolding P\<^sub>T_def .
  hence "ast_classical_problem.valid_classical_plan2 P\<^sub>N (restore_plan_def_translate ?q)"
    using ast_classical_problem.restore_plan_def_translate_compact[OF normalization_wf[OF assms] P\<^sub>N_def_explicated_conj[OF assms]] by blast
  hence "valid_classical_plan2 (reconstruct_plan_norm (restore_plan_def_translate ?q))"
    using assms normalization_reconstruct by simp
  thus "valid_classical_plan2 (numeric_reconstruct_plan_varfree_cert \<pi>s)"
    unfolding numeric_reconstruct_plan_varfree_cert_def .
qed

subsubsection \<open>Stage 2: the fully grounded (folded) numeric problem\<close>

text \<open>The \<^emph>\<open>grounded\<close> numeric product: stage one's variable-free instantiation
  \<^const>\<open>ast_classical_problem.numeric_P\<^sub>V_cert\<close> put through the fact/fluent fold
  \<^const>\<open>fact_folder.fold_prob\<close> at the certified facts and the ops-derived fluents. Everything in
  it is nullary --- the predicates are fresh names for the certified facts, the functions fresh
  names for the reachable ground fluents (\<open>fuel(c1) \<mapsto> fuel_c1_2\<close>), and each action's
  precondition/effect and the initial function assignments are stated over those names. This is the
  numeric counterpart of the propositional \<open>P\<^sub>G_cert\<close> (defined downstream in
  \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close>) --- indeed \<^emph>\<open>the same term\<close>: with the grounder
  being the two-stage composite, the propositional product is this very construction fed a
  numeric-free input, so the two branches share one executable \<open>ground_by_cert\<close>.\<close>

text \<open>The ground fluents the fold has to name: those actually mentioned by the instantiated
  reachable operators (plus the initial assignments), read off the same certified operator list.
  On a numeric-free task this list is empty and the fold declares no functions at all --- which is
  precisely why the same construction serves the STRIPS branch downstream.\<close>
definition "numeric_cert_fluents \<equiv>
  varfree.fluents P\<^sub>T (canon (normalized_problem_rx.cert_ops_of P\<^sub>T M))"

definition "numeric_P\<^sub>G_cert \<equiv> fact_folder.fold_prob numeric_P\<^sub>V_cert
  (normalized_problem_rx.cert_facts_of P\<^sub>T M) numeric_cert_fluents"

text \<open>\<^bold>\<open>Well-formedness of the grounded numeric problem\<close>: under the fold re-checks the folded
  product is a well-formed classical problem --- nullary predicate declarations for the certified
  facts, nullary function declarations for the reachable fluents, a distinct and well-formed
  initial state (predicate atoms \<^emph>\<open>and\<close> function assignments), and a well-formed goal. This is
  the numeric twin of \<open>wf_ground_cert_problem\<close>. Plan equivalence for the fold is
  \<open>numeric_ground_cert_plan_valid_iff\<close> / \<open>numeric_ground_cert_plan_reconstruct\<close> below.\<close>
lemma numeric_wf_ground_cert_problem:
  assumes fold_cert: "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.wf_classical_problem numeric_P\<^sub>G_cert"
proof -
  interpret cr: certified_reachability_fold_num P\<^sub>T M dc
    using certified_reachability_fold_num_i[OF nonempty cert fold_cert assms(2,3)] .
  have pg_eq: "numeric_P\<^sub>G_cert = cr.wfg_num.P\<^sub>G"
    unfolding numeric_P\<^sub>G_cert_def numeric_P\<^sub>V_cert_def numeric_cert_fluents_def
              cr.cert_ops'_def cr.cert_facts'_def by simp
  show ?thesis
    unfolding pg_eq using cr.wfg_num.ground_prob_wf_num by simp
qed

text \<open>\<^bold>\<open>Plan-existence equivalence for the grounded numeric problem\<close>: under the fold
  re-checks the folded product has a valid plan iff the original problem does --- the numeric
  grounder's \<open>valid_classical_plan_iff_num\<close> composed with the normalization and
  definedness-translation equivalences. This completes the plan-preservation story for the
  numeric pipeline's \<^emph>\<open>second\<close> stage.\<close>
lemma numeric_ground_cert_plan_valid_iff:
  assumes fold_cert: "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and "restrict_prob" "wf_classical_problem"
  shows "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow>
    (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>G_cert \<pi>s')"
proof -
  interpret cr: certified_reachability_fold_num P\<^sub>T M dc
    using certified_reachability_fold_num_i[OF nonempty cert fold_cert assms(2,3)] .
  have pg_eq: "numeric_P\<^sub>G_cert = cr.wfg_num.P\<^sub>G"
    unfolding numeric_P\<^sub>G_cert_def numeric_P\<^sub>V_cert_def numeric_cert_fluents_def
              cr.cert_ops'_def cr.cert_facts'_def by simp
  have "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>N \<pi>s')"
    using assms(2,3) normalization_valid_iff by simp
  also have "... \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>T \<pi>s')"
    using ast_classical_problem.def_translate_valid_iff_compact[OF normalization_wf[OF assms(2,3)] P\<^sub>N_def_explicated_conj[OF assms(2,3)]]
    unfolding P\<^sub>T_def by simp
  also have "... \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>G_cert \<pi>s')"
    unfolding pg_eq using cr.wfg_num.valid_classical_plan_iff_num by simp
  finally show ?thesis .
qed

text \<open>Plan restoration for the grounded numeric problem: the fold keeps the nullary plan-action
  list verbatim, so the \<^emph>\<open>same\<close> restorer as for the instantiation
  (\<^const>\<open>numeric_reconstruct_plan_varfree_cert\<close>) applies --- no new restore map.\<close>
lemma numeric_ground_cert_plan_reconstruct:
  assumes fold_cert: "normalized_problem_rx.numeric_fold_checks P\<^sub>T M"
      and "restrict_prob" "wf_classical_problem"
      and p: "ast_classical_problem.valid_classical_plan2 numeric_P\<^sub>G_cert \<pi>s"
  shows "valid_classical_plan2 (numeric_reconstruct_plan_varfree_cert \<pi>s)"
proof -
  interpret cr: certified_reachability_fold_num P\<^sub>T M dc
    using certified_reachability_fold_num_i[OF nonempty cert fold_cert assms(2,3)] .
  have pg_eq: "numeric_P\<^sub>G_cert = cr.wfg_num.P\<^sub>G"
    unfolding numeric_P\<^sub>G_cert_def numeric_P\<^sub>V_cert_def numeric_cert_fluents_def
              cr.cert_ops'_def cr.cert_facts'_def by simp
  let ?q = "varfree.restore_ground_plan (canon (normalized_problem_rx.cert_ops_of P\<^sub>T M)) \<pi>s"
  have "ast_classical_problem.valid_classical_plan2 P\<^sub>T ?q"
    using cr.wfg_num.valid_classical_plan_left_num[OF p[unfolded pg_eq]]
    unfolding cr.cert_ops'_def by simp
  hence "ast_classical_problem.valid_classical_plan2 (ast_classical_problem.def_translate_prob P\<^sub>N) ?q"
    unfolding P\<^sub>T_def .
  hence "ast_classical_problem.valid_classical_plan2 P\<^sub>N (restore_plan_def_translate ?q)"
    using ast_classical_problem.restore_plan_def_translate_compact[OF normalization_wf[OF assms(2,3)] P\<^sub>N_def_explicated_conj[OF assms(2,3)]] by blast
  hence "valid_classical_plan2 (reconstruct_plan_norm (restore_plan_def_translate ?q))"
    using assms(2,3) normalization_reconstruct by simp
  thus ?thesis
    unfolding numeric_reconstruct_plan_varfree_cert_def .
qed

end

end

end
