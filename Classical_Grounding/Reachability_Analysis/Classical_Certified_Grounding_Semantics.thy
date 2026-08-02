theory Classical_Certified_Grounding_Semantics
  imports Classical_Certified_Grounding
begin

section \<open>Certificate-to-grounder bridge: the \<open>wf_grounder\<close> / \<open>varfree_instantiator\<close> plug-in at \<open>P\<close>\<close>

text \<open>Interpret the grounder at the \<^emph>\<open>un-relaxed\<close> problem \<open>P\<close>, with the certificate-derived
  facts/ops \<open>cert_facts'\<close> / \<open>cert_ops'\<close>. The semantic supersets are \<open>all_facts_super\<close> /
  \<open>all_ops_super\<close> (proven in the shared base from the certificate); the syntactic well-formedness /
  coverage obligations are re-checked and discharged below. Two sibling interpretations:
  \<^locale>\<open>certified_reachability_num\<close> interprets the weaker \<^locale>\<open>varfree_instantiator\<close> (numeric-fluent
  retention), \<^locale>\<open>certified_reachability\<close> the full \<^locale>\<open>wf_grounder\<close> (propositional).\<close>

subsection \<open>Numeric-fluent-retaining path: interpret \<^locale>\<open>varfree_instantiator\<close>\<close>

context certified_reachability_num
begin

text \<open>The single decidable obligation the numeric grounder needs, read off the
  \<open>numeric_grounding_checks\<close> assumption: every certified op is a well-formed plan action. The other
  three \<^locale>\<open>varfree_instantiator\<close> goals (\<open>wf_problem\<close>, \<open>distinct cert_ops'\<close>, \<open>all_ops\<close>) come from the
  problem and the certificate (the base's \<open>all_ops_super\<close>), not from a re-check.\<close>

lemma ops_wf_l: "\<forall>\<pi> \<in> set cert_ops'. wf_classical_plan_action \<pi>"
  using grounding_cert_num unfolding numeric_grounding_checks_def cert_ops'_def by simp

end

sublocale certified_reachability_num \<subseteq> vfi: varfree_instantiator P cert_ops'
proof unfold_locales
  show "wf_classical_problem" by (rule wf_classical_problem)
  show "distinct cert_ops'" by (simp add: cert_ops'_def)
  show "set cert_ops' \<supseteq> {\<pi>. applicable \<pi>}" by (rule all_ops_super)
  show "\<forall>\<pi> \<in> set cert_ops'. wf_classical_plan_action \<pi>" by (rule ops_wf_l)
qed

subsection \<open>Propositional path: interpret the full \<^locale>\<open>wf_grounder\<close>\<close>

context certified_reachability
begin

text \<open>The same five coverage obligations (from \<open>grounding_checks\<close>, which subsumes
  \<open>numeric_grounding_checks\<close>) plus the two numeric-freeness obligations. Proven independently of the
  sibling \<^locale>\<open>certified_reachability_num\<close> (they share only the base).\<close>

lemma facts_wf_l: "\<forall>a \<in> set cert_facts'. px.wf_fmla_atom px.objT a"
  using grounding_cert unfolding grounding_checks_def numeric_grounding_checks_def cert_facts'_def by simp

lemma ops_wf_l: "\<forall>\<pi> \<in> set cert_ops'. wf_classical_plan_action \<pi>"
  using grounding_cert unfolding grounding_checks_def numeric_grounding_checks_def cert_ops'_def by simp

lemma effs_covered_l:
  "\<forall>\<pi> \<in> set cert_ops'. let eff = effect (the (res_inst \<pi>))
      in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> cert_facts'"
  using grounding_cert unfolding grounding_checks_def numeric_grounding_checks_def cert_ops'_def cert_facts'_def by simp

lemma pres_covered_l: "\<forall>\<pi> \<in> set cert_ops'. covered (precondition (the (res_inst \<pi>))) cert_facts'"
  using grounding_cert unfolding grounding_checks_def numeric_grounding_checks_def cert_ops'_def cert_facts'_def by simp

lemma goal_covered_l: "covered (goal P) cert_facts'"
  using grounding_cert unfolding grounding_checks_def numeric_grounding_checks_def cert_facts'_def by simp

lemma init_props_l: "\<forall>f \<in> set (init P). is_predAtom f"
  using grounding_cert unfolding grounding_checks_def by simp

lemma ops_no_num_l: "\<forall>\<pi> \<in> set cert_ops'. numeric_effects (effect (the (res_inst \<pi>))) = []"
  using grounding_cert unfolding grounding_checks_def cert_ops'_def by simp

end

sublocale certified_reachability \<subseteq> wfg: wf_grounder P cert_ops' cert_facts'
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
