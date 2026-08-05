theory Classical_Variable_Freeness_Num_Free
  imports Classical_Variable_Freeness Grounding_Classical_Common.Numeric_Free
begin

section \<open>The variable-freeness stage maintains numeric-freeness\<close>

text \<open>Stage-local preservation property: if the input problem is numeric-free, so is the
  variable-free grounded problem \<^const>\<open>varfree.varfree_inst_prob\<close> --- the nullary schemas'
  bodies are the instantiated originals under a \<^const>\<open>term.CONST\<close> lift, and neither
  instantiation nor the lift introduces a numeric atom or effect; types, predicates, functions,
  init and goal are kept verbatim.\<close>

subsection \<open>Numeric-freeness of the instantiated reachable ops\<close>

text \<open>Every reachable op is well-formed (\<open>ops_wf\<close>), so the general
  \<open>num_free_resinst'\<close> of \<^verbatim>\<open>Classical_PDDL_Sema_Supplement\<close> applies (the term-mapping
  preservation lemmas live there too).\<close>
lemma (in varfree_instantiator) num_free_resinst:
  assumes "\<pi> \<in> set ops"
      and num_free_dom
  shows "num_free_fmla (precondition (the (res_inst \<pi>)))"
    and "num_free_eff (effect (the (res_inst \<pi>)))"
proof -
  have wf: "wf_classical_plan_action \<pi>" using assms(1) ops_wf by blast
  show "num_free_fmla (precondition (the (res_inst \<pi>)))"
    using num_free_resinst'(1)[OF wf assms(2)] .
  show "num_free_eff (effect (the (res_inst \<pi>)))"
    using num_free_resinst'(2)[OF wf assms(2)] .
qed

subsection \<open>The stage theorem\<close>

theorem (in varfree_instantiator) varfree_inst_prob_num_free:
  assumes num_free_prob
  shows "ast_classical_problem.num_free_prob varfree_inst_prob"
proof -
  have nfd: num_free_dom using assms unfolding num_free_prob_def by blast
  have dom: "ast_classical_domain.num_free_dom varfree_inst_dom"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions varfree_inst_dom)"
    then obtain \<pi> n where a: "a = varfree_inst_ac \<pi> n" and pi: "\<pi> \<in> set ops"
      unfolding varfree_inst_dom_sel using map2_obtain by metis
    have "num_free_fmla (ac_pre (varfree_inst_ac \<pi> n))"
      using num_free_resinst(1)[OF pi nfd] by simp
    moreover
    have "num_free_eff (ac_eff (varfree_inst_ac \<pi> n))"
      using num_free_resinst(2)[OF pi nfd] by simp
    ultimately
    show "num_free_ac a" unfolding a num_free_ac_def by blast
  qed
  have goal: "num_free_fmla (goal varfree_inst_prob)"
    using assms unfolding num_free_prob_def by simp
  have init: "\<forall>f \<in> set (init varfree_inst_prob). num_free_fmla f"
    using assms unfolding num_free_prob_def by simp
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom goal init by simp
qed

end
