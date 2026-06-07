theory Certified_Grounding_Locales
  imports Reachability_Certificate "PDDL_Relaxation.PDDL_Relaxation_Semantics"
begin

section \<open>Certificate-to-grounder bridge (Option 1): locale and definitions\<close>

text \<open>This connects the relaxed-problem certificate kernel (Locale A = \<^locale>\<open>pddl_datalog\<close>,
  theory \<open>Reachability_Certificate\<close>) to the grounder (\<^locale>\<open>wf_grounder\<close>, theory
  \<open>Grounded_PDDL\<close>) so that the grounder targets the \<^emph>\<open>un-relaxed\<close> problem \<open>P\<close> (real add+delete
  effects), using the relaxed reachable set only as the pruning oracle.\<close>

subsection \<open>Step 1: expose the certificate kernel at the relaxation \<open>PX\<close>\<close>

text \<open>\<open>PX\<close> (the delete-relaxation of a normalized problem) is already a
  \<^locale>\<open>normalized_problem\<close> (existing \<open>px\<close> sublocale, theory \<open>PDDL_Relaxation\<close>) and satisfies
  \<open>px.relaxed_prob\<close> (\<open>relax_relaxes\<close>); since \<^locale>\<open>pddl_datalog\<close> adds nothing to
  \<^locale>\<open>relaxed_problem\<close>, \<open>PX\<close> is a \<^locale>\<open>pddl_datalog\<close>. This exposes \<open>px.closure_check\<close>,
  \<open>px.cert_facts\<close>, \<open>px.cert_ops\<close>, \<open>px.closure_sound\<close>, \<dots> instantiated at \<open>PX\<close>.\<close>

sublocale normalized_problem_rx \<subseteq> px: pddl_datalog PX
  unfolding pddl_datalog_def
  by (simp add: normalized_problem_def' relaxed_problem.intro relaxed_problem_axioms_def
                relax_wf relax_normed relax_relaxes)

subsection \<open>Step 2/3: certificate-derived facts/ops and the grounding well-formedness check\<close>

text \<open>The certificate is checked against the relaxation (\<open>px.admissible\<close>) for the \<^emph>\<open>semantic\<close>
  content (the facts/ops supersets). The grounder additionally needs \<^emph>\<open>syntactic\<close>
  well-formedness/coverage of the certificate-derived facts and ops; since those are all
  decidable, we bundle them into an executable \<open>grounding_checks\<close> predicate that the
  certifying kernel re-checks (Route 2: strengthen the checked conditions). The relaxed reachable
  facts (\<open>px.cert_facts\<close>) are augmented with the add+delete atoms of the ops (read off \<open>P\<close>'s real
  schemas via \<open>res_inst\<close>) so that \<open>effs_covered\<close> can be re-checked at all.\<close>

context normalized_problem_rx
begin

definition cert_ops_of :: "certificate \<Rightarrow> ast_classical_plan_action list" where
  "cert_ops_of cert \<equiv> px.cert_ops cert"

definition extra_eff_atoms_of :: "certificate \<Rightarrow> facty list" where
  "extra_eff_atoms_of cert \<equiv>
     remdups (concat (map (\<lambda>\<pi>. let eff = effect (the (res_inst \<pi>)) in adds eff @ dels eff)
                          (cert_ops_of cert)))"

definition cert_facts_of :: "certificate \<Rightarrow> facty list" where
  "cert_facts_of cert \<equiv> remdups (cert_facts cert @ extra_eff_atoms_of cert)"

text \<open>The decidable grounding obligations, phrased to match the \<^locale>\<open>wf_grounder\<close> goals
  exactly. \<open>all_facts\<close>/\<open>all_ops\<close> (the semantic supersets) are \<^emph>\<open>not\<close> here --- they are proven
  from soundness, not re-checked.\<close>
definition grounding_checks :: "certificate \<Rightarrow> bool" where
  "grounding_checks cert \<equiv>
     (\<forall>a \<in> set (cert_facts_of cert). px.wf_fmla_atom px.objT a) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of cert). wf_classical_plan_action \<pi>) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of cert). let eff = effect (the (res_inst \<pi>))
        in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> (cert_facts_of cert)) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of cert). covered (precondition (the (res_inst \<pi>))) (cert_facts_of cert)) \<and>
     covered (goal P) (cert_facts_of cert) \<and>
     (\<forall>f \<in> set (init P). is_predAtom f) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of cert). numeric_effects (effect (the (res_inst \<pi>))) = [])"

end

locale certified_reachability = normalized_problem_rx +
  fixes cert :: certificate
  assumes admissible_cert: "px.admissible cert"      \<comment> \<open>semantic: facts/ops supersets\<close>
      and grounding_cert: "grounding_checks cert"    \<comment> \<open>syntactic: grounder well-formedness\<close>
begin

definition cert_ops' :: "ast_classical_plan_action list" where
  "cert_ops' \<equiv> cert_ops_of cert"

definition cert_facts' :: "facty list" where
  "cert_facts' \<equiv> cert_facts_of cert"

end

end

