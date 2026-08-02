theory Classical_Grounded_PDDL_Num_Free
  imports Classical_Grounded_PDDL_Semantics Grounding_Classical_Common.Numeric_Free
begin

section \<open>The fact folder maintains numeric-freeness\<close>

text \<open>Stage-local preservation property: under \<^locale>\<open>wf_fact_folder\<close> (covered preconditions,
  effects and goal --- \<^const>\<open>covered\<close> rejects numeric atoms outright --- plus \<open>init_props\<close> and
  \<open>acs_no_num\<close>), the folded problem \<^const>\<open>fact_folder.fold_prob\<close> is numeric-free: every folded
  atom is a nullary \<^const>\<open>predAtm\<close> or a resolved equality, and no numeric effect survives.\<close>

subsection \<open>Numeric-freeness of the folded formulas\<close>

text \<open>\<^const>\<open>fact_folder.ground_fmla\<close> maps a covered predicate atom to a nullary
  \<^const>\<open>predAtm\<close> and an equality to \<open>\<bottom>\<close>/\<open>\<^bold>\<not>\<bottom>\<close>; \<^const>\<open>covered\<close> rejects numeric atoms outright,
  so the folded formula is numeric-free.\<close>
lemma (in fact_folder) num_free_ground_fmla:
  "covered \<phi> facts \<Longrightarrow> num_free_fmla (ground_fmla \<phi>)"
  by (induction \<phi> rule: ground_fmla.induct) (auto split: if_splits simp: covered_def)

text \<open>A \<^const>\<open>predAtm\<close> formula is re-indexed to a nullary \<^const>\<open>predAtm\<close>, hence numeric-free
  unconditionally --- the initial state (\<open>init_props\<close>) is exactly such a formula, so it needs no
  coverage assumption.\<close>
lemma (in fact_folder) num_free_ground_predAtom:
  "is_predAtom \<phi> \<Longrightarrow> num_free_fmla (ground_fmla \<phi>)"
  by (cases \<phi> rule: is_predAtom.cases) auto

subsection \<open>Numeric-freeness of the folded actions and problem\<close>

lemma (in wf_fact_folder) num_free_fold_ac:
  assumes "a \<in> set (actions (domain P))"
  shows "num_free_ac (fold_ac a)"
proof -
  let ?ga = "the (res_inst (ac_pa a))"
  have pre_cov: "covered (precondition ?ga) facts" using pres_covered assms by blast
  have ad_cov: "\<forall>\<phi> \<in> set (adds (effect ?ga) @ dels (effect ?ga)). covered \<phi> facts"
    using effs_covered assms unfolding Let_def by blast
  have ne0: "numeric_effects (effect ?ga) = []" using acs_no_num assms by blast
  have pre: "num_free_fmla (ground_fmla (precondition ?ga))"
    using num_free_ground_fmla[OF pre_cov] .
  have ad: "\<forall>\<phi> \<in> set (adds (effect ?ga)) \<union> set (dels (effect ?ga)). num_free_fmla (ground_fmla \<phi>)"
    using ad_cov by (auto simp: num_free_ground_fmla)
  show ?thesis
    unfolding num_free_ac_def fold_ac_sel ga_pre_alt ga_eff_alt num_free_eff.simps
    using pre ad ne0 by (auto simp: ne0)
qed

theorem (in wf_fact_folder) fold_prob_num_free: "ast_classical_problem.num_free_prob fold_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom (domain fold_prob)"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions (domain fold_prob))"
    then obtain b where a: "a = fold_ac b" and bmem: "b \<in> set (actions (domain P))"
      unfolding fold_prob_sel fold_dom_sel by auto
    show "num_free_ac a" unfolding a using num_free_fold_ac[OF bmem] .
  qed
  have goal: "num_free_fmla (goal fold_prob)"
    by (simp add: num_free_ground_fmla goal_covered)
  have init: "\<forall>f \<in> set (init fold_prob). num_free_fmla f"
    using init_props by (auto simp: num_free_ground_predAtom)
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def using dom goal init by blast
qed

end
