theory Classical_Certified_Grounding_Locales
  imports Classical_PDDL_Reachability_Certificate "Classical_PDDL_Relaxation.Classical_PDDL_Relaxation_Semantics"
begin

section \<open>Certificate-to-grounder bridge: locale and definitions\<close>

text \<open>This connects the relaxed-problem reachability certificate --- the generic
  \<^const>\<open>dl_certified_model\<close> of the translated program \<^const>\<open>dl_rules\<close>, related to PDDL
  reachability by \<open>certified_facts_eq_achievable\<close> --- to the grounder \<^locale>\<open>wf_grounder\<close>, so
  that the grounder targets the \<^emph>\<open>un-relaxed\<close> problem \<open>P\<close> (real add+delete effects), using the
  relaxed reachable set only as the pruning oracle.\<close>

subsection \<open>Step 1: the relaxation \<open>PX\<close> is a \<^locale>\<open>pddl_datalog\<close>\<close>

text \<open>\<open>PX\<close> (the delete-relaxation of a normalized problem) is a \<^locale>\<open>normalized_problem\<close> (the
  existing \<open>px\<close> sublocale) and satisfies \<open>relax_relaxes\<close>; since \<^locale>\<open>pddl_datalog\<close> adds nothing
  to \<^locale>\<open>relaxed_problem\<close>, \<open>PX\<close> is a \<^locale>\<open>pddl_datalog\<close>. This exposes the reachability kernel
  (\<open>achievable\<close>, \<open>enabled_clause_body\<close>, \<dots>) instantiated at \<open>PX\<close> under the \<open>px\<close> prefix.\<close>

sublocale normalized_problem_rx \<subseteq> px: pddl_datalog PX
  unfolding pddl_datalog_def
  by (simp add: normalized_problem_def' relaxed_problem.intro relaxed_problem_axioms_def
                relax_wf relax_normed relax_relaxes)

subsection \<open>Step 2/3: certificate-derived facts/ops and the grounding well-formedness check\<close>

context normalized_problem_rx
begin

text \<open>The applicable-ops over-approximation read off the certified reachable facts \<open>M\<close>: for every
  action clause of \<open>PX\<close> and every object-tuple over the universe whose substituted positive
  precondition atoms all lie in \<open>M\<close> and whose equality guards hold, the corresponding ground plan
  action. By \<open>px.enabled_clause_body\<close> every action enabled in a reachable state of the relaxed
  problem is enumerated here, which is what makes \<open>cert_ops'\<close> an over-approximation of the
  applicable actions.\<close>
definition cert_ops_of :: "fact list \<Rightarrow> ast_classical_plan_action list" where
  "cert_ops_of M \<equiv> concat (map (\<lambda>c.
      map (SimplePlanAction (cl_name c))
        (all_combos (\<lambda>args.
            (\<forall>a \<in> set (cl_pred_pre c).
                map_atom_fmla (ac_tsubst (cl_params c) args) a \<in> set (map fact_to_facty M))
            \<and> satisfies_conds (cl_params c) (cl_cond_pre c) args)
          (replicate (length (cl_params c)) px.const_names)))
      px.a_clauses)"

text \<open>Augment the reachable facts with the add/delete atoms of the certified ops (read off \<open>P\<close>'s
  real schemas via \<open>res_inst\<close>) so that the grounder's effect-coverage obligation can hold at all.\<close>
definition extra_eff_atoms_of :: "fact list \<Rightarrow> facty list" where
  "extra_eff_atoms_of M \<equiv>
     remdups (concat (map (\<lambda>\<pi>. let eff = effect (the (res_inst \<pi>)) in adds eff @ dels eff)
                          (cert_ops_of M)))"

definition cert_facts_of :: "fact list \<Rightarrow> facty list" where
  "cert_facts_of M \<equiv> remdups (map fact_to_facty M @ extra_eff_atoms_of M)"

text \<open>The decidable grounding obligations, phrased to match the \<^locale>\<open>wf_grounder\<close> goals exactly.
  The semantic supersets (\<open>all_facts\<close>/\<open>all_ops\<close>) are \<^emph>\<open>not\<close> here --- they are proven from the
  certificate, not re-checked.\<close>
definition grounding_checks :: "fact list \<Rightarrow> bool" where
  "grounding_checks M \<equiv>
     (\<forall>a \<in> set (cert_facts_of M). px.wf_fmla_atom px.objT a) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of M). wf_classical_plan_action \<pi>) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of M). let eff = effect (the (res_inst \<pi>))
        in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> (cert_facts_of M)) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of M). covered (precondition (the (res_inst \<pi>))) (cert_facts_of M)) \<and>
     covered (goal P) (cert_facts_of M) \<and>
     (\<forall>f \<in> set (init P). is_predAtom f) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of M). numeric_effects (effect (the (res_inst \<pi>))) = [])"

end

text \<open>The grounding-input locale: a relaxed-problem certificate \<open>M\<close>/\<open>dc\<close> accepted by the generic
  checker, plus the (numeric-free, nonempty-universe) side conditions that make the
  \<^locale>\<open>num_free_relaxed_problem\<close> reachability bridge available at \<open>PX\<close>, and the decidable
  grounding re-check.\<close>
locale certified_reachability = normalized_problem_rx +
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes px_numfree: "numeric_free_problem PX"
      and nonempty: "ast_classical_problem.const_names PX \<noteq> []"
      and cert: "dl_certified_model (set (dl_rules PX)) (set (ast_classical_problem.const_names PX)) M dc"
      and grounding_cert: "grounding_checks M"
begin

text \<open>\<open>PX\<close> is numeric-free, delete-relaxed and has a nonempty object universe, so the full
  reachability bridge of \<^locale>\<open>num_free_relaxed_problem\<close> --- in particular
  \<open>certified_facts_eq_achievable\<close> --- applies to it.\<close>
lemma px_nfr: "num_free_relaxed_problem PX"
proof -
  have "pddl_datalog PX"
    unfolding pddl_datalog_def
    by (simp add: normalized_problem_def' relaxed_problem.intro relaxed_problem_axioms_def
                  relax_wf relax_normed relax_relaxes)
  thus ?thesis
    using px_numfree nonempty
    by (simp add: num_free_relaxed_problem_def num_free_relaxed_problem_axioms_def)
qed

definition cert_ops' :: "ast_classical_plan_action list" where
  "cert_ops' \<equiv> remdups (cert_ops_of M)"

definition cert_facts' :: "facty list" where
  "cert_facts' \<equiv> cert_facts_of M"

end

end

