theory PDDL_Reachability_Certificate
  imports PDDL_Reachability_Analysis
begin

context num_free_relaxed_problem
begin

subsection \<open>Relating an admissible certificate to PDDL reachability\<close>

text \<open>The capstone: any list \<open>M\<close> that the \<^emph>\<open>generic\<close> checker certifies to be the minimal model of
  the translated program \<^const>\<open>dl_rules\<close> (over the object universe) is \<^emph>\<open>exactly\<close> the set of
  PDDL-achievable facts of the relaxed problem. An accepted \<^const>\<open>dl_admissible\<close> certificate
  thus yields the reachable-fact set by theorem, with no PDDL-specific check.\<close>
theorem certified_facts_eq_achievable:
  assumes cert: "dl_certified_model (set (dl_rules P)) (set const_names) M dc"
  shows "set M = {f. achievable f}"
proof -
  have "{f. achievable f} = {f. dl_prog.derivable f}"
    by (rule achievable_eq_minimal_model)
  thus ?thesis using dl_certified_model_correct[OF cert] by simp
qed

text \<open>The facts requirement, discharged by a certified minimal model: the facts of any certified
  minimal model capture exactly the achievable facts --- the facts-soundness direction,
  established without any PDDL-specific closure check.\<close>
theorem minimal_model_facts_requirement:
  assumes model: "set M = {f. dl_prog.derivable f}"
  shows "fact_to_facty ` {f. achievable f} \<subseteq> fact_to_facty ` set M"
proof -
  have "{f. achievable f} \<subseteq> set M"
    using achievable_imp_dl_derivable model by blast
  thus ?thesis by (rule image_mono)
qed

end

context certified_pddl
begin

text \<open>The certified list enumerates exactly the achievable facts --- the capstone
  \<open>certified_facts_eq_achievable\<close> with the certificate assumption discharged in the
  locale context.\<close>
lemma certified_facts_eq_reachable: "set M = {f. achievable f}"
  using certified_facts_eq_achievable[OF cert] .

end

end
