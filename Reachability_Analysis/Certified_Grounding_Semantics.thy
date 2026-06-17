theory Certified_Grounding_Semantics
  imports Certified_Grounding
begin

section \<open>Certificate-to-grounder bridge: the \<open>wf_grounder\<close> plug-in at \<open>P\<close>\<close>

text \<open>Interpret \<^locale>\<open>wf_grounder\<close> at the \<^emph>\<open>un-relaxed\<close> problem \<open>P\<close>, with the certificate-derived
  facts/ops \<open>cert_facts'\<close> / \<open>cert_ops'\<close>. The semantic supersets are
  \<open>all_facts_super\<close> / \<open>all_ops_super\<close>; the syntactic well-formedness / coverage obligations are
  re-checked by \<open>grounding_checks\<close> and discharged below.\<close>

context certified_reachability
begin

text \<open>Each decidable grounder obligation is read off the \<open>grounding_cert\<close> assumption (the kernel's
  re-check of the certificate). Phrasings match the \<^locale>\<open>wf_grounder\<close> goals exactly.
  \<open>set\<close>-of-\<open>remdups\<close> rewriting (for \<open>cert_ops'\<close>) is handled by \<open>simp\<close>.\<close>

lemma facts_wf_l: "\<forall>a \<in> set cert_facts'. px.wf_fmla_atom px.objT a"
  using grounding_cert unfolding grounding_checks_def cert_facts'_def by simp

lemma ops_wf_l: "\<forall>\<pi> \<in> set cert_ops'. wf_classical_plan_action \<pi>"
  using grounding_cert unfolding grounding_checks_def cert_ops'_def by simp

lemma effs_covered_l:
  "\<forall>\<pi> \<in> set cert_ops'. let eff = effect (the (res_inst \<pi>))
      in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> cert_facts'"
  using grounding_cert unfolding grounding_checks_def cert_ops'_def cert_facts'_def by simp

lemma pres_covered_l: "\<forall>\<pi> \<in> set cert_ops'. covered (precondition (the (res_inst \<pi>))) cert_facts'"
  using grounding_cert unfolding grounding_checks_def cert_ops'_def cert_facts'_def by simp

lemma goal_covered_l: "covered (goal P) cert_facts'"
  using grounding_cert unfolding grounding_checks_def cert_facts'_def by simp

lemma init_props_l: "\<forall>f \<in> set (init P). is_predAtom f"
  using grounding_cert unfolding grounding_checks_def by simp

lemma ops_no_num_l: "\<forall>\<pi> \<in> set cert_ops'. numeric_effects (effect (the (res_inst \<pi>))) = []"
  using grounding_cert unfolding grounding_checks_def cert_ops'_def by simp

end

sublocale certified_reachability \<subseteq> wfg: wf_grounder P cert_facts' cert_ops'
proof unfold_locales
  show "wf_classical_problem" by (rule wf_classical_problem)
  show "distinct cert_facts'" by (simp add: cert_facts'_def cert_facts_of_def)
  show "fact_to_facty ` {a. achievable a} \<subseteq> set cert_facts'" by (rule all_facts_super)
  show "\<forall>a \<in> set cert_facts'. px.wf_fmla_atom px.objT a" by (rule facts_wf_l)
  show "distinct cert_ops'" by (simp add: cert_ops'_def)
  show "set cert_ops' \<supseteq> {\<pi>. applicable \<pi>}" by (rule all_ops_super)
  show "\<forall>\<pi> \<in> set cert_ops'. wf_classical_plan_action \<pi>" by (rule ops_wf_l)
  show "\<forall>\<pi> \<in> set cert_ops'. let eff = effect (the (res_inst \<pi>))
          in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> cert_facts'" by (rule effs_covered_l)
  show "\<forall>\<pi> \<in> set cert_ops'. covered (precondition (the (res_inst \<pi>))) cert_facts'"
    by (rule pres_covered_l)
  show "covered (goal P) cert_facts'" by (rule goal_covered_l)
  show "\<forall>f \<in> set (init P). is_predAtom f" by (rule init_props_l)
  show "\<forall>\<pi> \<in> set cert_ops'. numeric_effects (effect (the (res_inst \<pi>))) = []" by (rule ops_no_num_l)
qed

end
