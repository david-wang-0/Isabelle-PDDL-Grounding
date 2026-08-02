theory Classical_Variable_Freeness_Num_Free
  imports Classical_Variable_Freeness Grounding_Classical_Common.Numeric_Free
begin

section \<open>The variable-freeness stage maintains numeric-freeness\<close>

text \<open>Stage-local preservation property: if the input problem is numeric-free, so is the
  variable-free grounded problem \<^const>\<open>varfree.varfree_inst_prob\<close> --- the nullary schemas'
  bodies are the instantiated originals under a \<^const>\<open>term.CONST\<close> lift, and neither
  instantiation nor the lift introduces a numeric atom or effect; types, predicates, functions,
  init and goal are kept verbatim.\<close>

subsection \<open>Term-mapping preserves numeric-freeness\<close>

text \<open>Mapping the entity type of an atom / formula / effect (e.g.\ the \<^const>\<open>term.CONST\<close> lift or
  an \<^const>\<open>ac_tsubst\<close> instantiation) cannot change the atom \<^emph>\<open>constructors\<close>, so it preserves
  numeric-freeness in both directions. Stated on \<^const>\<open>map_formula\<close>/\<^const>\<open>map_atom\<close> directly
  (the composed form \<open>map_atom_fmla\<close> normalizes to it under \<open>o_apply\<close>).\<close>

lemma is_numeric_atom_map_atom [simp]:
  "is_numeric_atom (map_atom f a) = is_numeric_atom a"
  by (cases a) simp_all

lemma num_free_fmla_map_atom_fmla [simp]:
  "num_free_fmla (map_formula (map_atom f) \<phi>) = num_free_fmla \<phi>"
  by (induction \<phi>) simp_all

lemma num_free_eff_map_ast_effect [simp]:
  "num_free_eff (map_ast_effect f \<epsilon>) = num_free_eff \<epsilon>"
  by (cases \<epsilon>) simp

subsection \<open>Numeric-freeness of the instantiated reachable ops\<close>

text \<open>A resolved action-schema name denotes a schema of the domain's action list.\<close>
lemma (in ast_classical_problem) resolve_schema_mem:
  assumes "resolve_classical_action_schema n = Some a"
  shows "a \<in> set (actions D)"
  using assms unfolding resolve_classical_action_schema_def by (meson index_by_eq_SomeD)

text \<open>Every reachable op resolves (it is well-formed, by \<open>ops_wf\<close>) to a schema of a numeric-free
  domain, and instantiation is a \<^const>\<open>map_atom_fmla\<close>/\<^const>\<open>map_ast_effect\<close> term-substitution,
  so the instantiated ground action's body is numeric-free.\<close>
lemma (in varfree_instantiator) num_free_resinst:
  assumes "\<pi> \<in> set ops"
      and num_free_dom
  shows "num_free_fmla (precondition (the (res_inst \<pi>)))"
    and "num_free_eff (effect (the (res_inst \<pi>)))"
proof -
  obtain n args where pi: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  have "wf_classical_plan_action \<pi>" using assms(1) ops_wf by blast
  then obtain a where a: "resolve_classical_action_schema n = Some a"
    using pi wf_classical_plan_action_simple by (auto split: option.splits)
  have nfa: "num_free_ac a"
    using assms(2) resolve_schema_mem[OF a] unfolding num_free_dom_def by blast
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
