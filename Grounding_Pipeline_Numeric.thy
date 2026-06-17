theory Grounding_Pipeline_Numeric
  imports Type_Normalization.Type_Normalization_Semantics
    Goal_Normalization.Goal_Normalization_Semantics
    Definedness_Normalization.Definedness_Normalization_Semantics
    Precondition_Normalization.Precondition_Normalization_Semantics
    Definedness_Translation.Definedness_Translation_Semantics
    PDDL_Relaxation.PDDL_Relaxation_Semantics
    Reachability_Analysis.Certified_Grounding_Semantics
    Grounded_PDDL.Grounded_PDDL
    Tree_Decomp_Grounding_Common.Numeric_Free
begin

text \<open>This theory assembles the verified grounding pipeline that applies to PDDL problems
  \<^emph>\<open>with\<close> numerics: type/goal/definedness/precondition normalization, definedness translation,
  delete-relaxation, and certificate-based reachability grounding, ending at the grounded PDDL
  problem \<^term>\<open>P\<^sub>G_cert\<close>. The numeric-free specialization that converts the grounded problem
  to STRIPS lives downstream in \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close>.\<close>

subsection \<open> Grounding preserves numeric-freeness and normalization \<close>

text \<open>The grounder emits purely propositional output: \<^const>\<open>grounder.ground_fmla\<close> maps every
  atom to either \<open>\<bottom>\<close>/\<open>\<^bold>\<not>\<bottom>\<close> (equalities) or a nullary \<^const>\<open>predAtm\<close> (predicate and numeric
  atoms alike), so it never produces a numeric atom and preserves the conjunctive literal
  structure. Hence the grounded problem is unconditionally numeric-free, and \<^emph>\<open>normalized\<close>
  whenever its input is.\<close>

lemma (in grounder) num_free_ground_fmla: "num_free_fmla (ground_fmla \<phi>)"
  by (induction \<phi> rule: ground_fmla.induct) auto

lemma (in grounder) is_lit_plus_ground_fmla: "is_lit_plus L \<Longrightarrow> is_lit_plus (ground_fmla L)"
  apply (cases L rule: is_lit_plus.cases; simp)
  subgoal for a by (cases a) auto
  subgoal for a by (cases a) auto
  done

lemma is_lit_plus_imp_is_conj: "is_lit_plus X \<Longrightarrow> is_conj X"
  by (cases X rule: is_lit_plus.cases) auto

lemma (in grounder) is_conj_ground_fmla: "is_conj F \<Longrightarrow> is_conj (ground_fmla F)"
  by (induction F rule: is_conj.induct)
     (auto simp: is_lit_plus_ground_fmla is_lit_plus_imp_is_conj)

lemma (in grounder) num_free_ac_ground_ac: "num_free_ac (ground_ac \<pi> n)"
proof -
  obtain pre a d ne where ga: "the (res_inst \<pi>) = GroundAction pre (Effect a d ne)"
    by (cases "the (res_inst \<pi>)"; cases "ground_action.effect (the (res_inst \<pi>))") auto
  show ?thesis
    unfolding num_free_ac_def ground_ac_def Let_def ga
    by (auto simp: num_free_ground_fmla)
qed

lemma (in grounder) ac_pre_ground_ac:
  "ac_pre (ground_ac \<pi> n) = ground_fmla (ground_action.precondition (the (res_inst \<pi>)))"
  unfolding ground_ac_def Let_def by (cases "the (res_inst \<pi>)") simp

lemma (in grounder) ac_params_ground_ac: "ac_params (ground_ac \<pi> n) = []"
  unfolding ground_ac_def Let_def by (cases "the (res_inst \<pi>)") simp

lemma (in grounder) ground_prob_num_free: "ast_classical_problem.num_free_prob ground_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom (domain ground_prob)"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions (domain ground_prob))"
    then obtain \<pi> n where "a = ground_ac \<pi> n"
      unfolding ground_prob_def ground_dom_def by (auto simp: map2_map_map set_zip)
    thus "num_free_ac a" by (simp add: num_free_ac_ground_ac)
  qed
  have goal: "num_free_fmla (goal ground_prob)"
    unfolding ground_prob_def ground_dom_def by (simp add: num_free_ground_fmla)
  have init: "\<forall>f \<in> set (init ground_prob). num_free_fmla f"
    unfolding ground_prob_def ground_dom_def by (auto simp: num_free_ground_fmla)
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def using dom goal init by blast
qed

lemma (in grounder) ground_prob_typeless: "ast_classical_problem.typeless_classical_problem ground_prob"
  unfolding ast_classical_problem.typeless_classical_problem_def
            ast_classical_domain.typeless_classical_domain_def
            domain_signature.typeless_domain_signature_def
  by (auto simp: ground_prob_def ground_dom_def map2_map_map ac_params_ground_ac)

lemma (in wf_grounder) resolve_mem:
  "resolve_classical_action_schema n = Some a \<Longrightarrow> a \<in> set (actions D)"
  unfolding resolve_classical_action_schema_def by (meson index_by_eq_SomeD)

lemma (in wf_grounder) op_pre_is_conj:
  assumes "normalized_prob" "\<pi> \<in> set ops"
  shows "is_conj (ground_fmla (ground_action.precondition (the (res_inst \<pi>))))"
proof -
  obtain n args where pi: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  have "wf_classical_plan_action \<pi>" using assms(2) ops_wf by blast
  then obtain a where a: "resolve_classical_action_schema n = Some a"
    using pi wf_classical_plan_action_simple by (auto split: option.splits)
  hence amem: "a \<in> set (actions D)" by (rule resolve_mem)
  have conj: "is_conj (ac_pre a)"
    using amem assms(1)[unfolded normalized_prob_def] prec_normed_dom_def by blast
  have inst: "ground_action.precondition (the (res_inst \<pi>))
      = map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a)"
    using a unfolding pi by (simp add: instantiate_classical_action_schema_alt)
  have "is_conj (map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a))"
    using conj map_preserves_isconj by (simp add: comp_def)
  thus ?thesis unfolding inst by (rule is_conj_ground_fmla)
qed

lemma (in wf_grounder) ground_prob_prec_normed:
  assumes "normalized_prob"
  shows "ast_classical_domain.prec_normed_dom (domain ground_prob)"
  unfolding ast_classical_domain.prec_normed_dom_def
proof
  fix ac assume "ac \<in> set (actions (domain ground_prob))"
  then obtain \<pi> n where ac: "ac = ground_ac \<pi> n" and pin: "(\<pi>,n) \<in> set (zip ops op_names)"
    unfolding ground_prob_def ground_dom_def by (auto simp: map2_map_map)
  from pin have "\<pi> \<in> set ops" using set_zip_leftD by fastforce
  from op_pre_is_conj[OF assms this] show "is_conj (ac_pre ac)"
    unfolding ac ac_pre_ground_ac .
qed

subsection \<open> Important theorems from individual grounding pipeline steps.
  Setting up compact notations for some of them to remove contexts. \<close>

context ast_classical_problem begin
thm detype_classical_prob_sel
thm restrict_classical_problem2.detype_classical_prob_wf
lemma detype_prob_wf_compact:
  "restrict_prob \<Longrightarrow> wf_classical_problem
  \<Longrightarrow> ast_classical_problem.wf_classical_problem detype_classical_prob"
  using restrict_classical_problem2.detype_classical_prob_wf
  using restrict_classical_problem2.intro restrict_classical_problem.intro
        restrict_classical_problem_axioms.intro wf_ast_classical_problem.intro
  by auto
lemma detyped_valid_iff_compact:
  "restrict_prob \<Longrightarrow> wf_classical_problem
  \<Longrightarrow> valid_classical_plan2 \<pi>s \<longleftrightarrow> ast_classical_problem.valid_classical_plan2 detype_classical_prob \<pi>s"
  using restrict_classical_problem2.detyped_valid_iff
  using restrict_classical_problem2.intro restrict_classical_problem.intro
        restrict_classical_problem_axioms.intro wf_ast_classical_problem.intro
  by auto

thm ast_classical_problem.degoal_prob_sel
lemma degoal_prob_wf_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.wf_classical_problem (degoal_prob)"
  using wf_ast_classical_problem3.degoal_prob_wf
  using wf_ast_classical_problem3_def wf_ast_classical_problem.intro by simp
lemma degoal_plan_restore_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.valid_classical_plan2 degoal_prob \<pi>s \<Longrightarrow> valid_classical_plan2 (restore_plan_degoal \<pi>s)"
  using wf_ast_classical_problem3.valid_classical_plan2_left
  using wf_ast_classical_problem3_def wf_ast_classical_problem.intro by simp
lemma degoaled_valid_iff_compact:
  "wf_classical_problem \<Longrightarrow> (\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 degoal_prob \<pi>s')"
  using wf_ast_classical_problem3.degoaled_valid_iff
  using wf_ast_classical_problem3_def wf_ast_classical_problem.intro by simp

thm ast_classical_problem.explicate_def_prob_sel
lemma explicate_def_prob_wf_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.wf_classical_problem explicate_def_prob"
  using wf_ast_classical_problem_de.explicate_def_prob_wf
  using wf_ast_classical_problem_de_def wf_ast_classical_problem.intro by simp
lemma explicate_def_def_explicated_conj_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.def_explicated_conj_prob explicate_def_prob"
  using def_explicated_conj_explicate_def_prob .
lemma explicate_def_valid_iff_compact:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 explicate_def_prob \<pi>s')"
  by (rule ast_classical_problem_de.explicate_valid_iff)
lemma restore_plan_explicate_valid_compact:
  "ast_classical_problem.valid_classical_plan2 explicate_def_prob \<pi>s \<Longrightarrow>
    valid_classical_plan2 (restore_plan_explicate \<pi>s)"
  by (rule ast_classical_problem_de.explicate_plan_restore)

thm ast_classical_problem.split_prob_sel
thm ast_classical_problem4.prec_normed_dom
lemma split_prob_wf_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow> ast_classical_problem.wf_classical_problem (split_prob)"
  using wf_ast_classical_problem4.split_prob_wf
  unfolding wf_ast_classical_problem4_def
            def_explicated_conj_problem_def
            def_explicated_conj_problem_axioms_def
            wf_ast_classical_problem_def
  by simp
lemma split_valid_iff_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow>
    (\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 split_prob \<pi>s')"
  using wf_ast_classical_problem4.split_valid_iff
  unfolding wf_ast_classical_problem4_def
            def_explicated_conj_problem_def
            def_explicated_conj_problem_axioms_def
            wf_ast_classical_problem_def
  by simp
lemma restore_plan_split_valid_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow>
    ast_classical_problem.valid_classical_plan2 split_prob \<pi>s \<Longrightarrow> valid_classical_plan2 (restore_plan_split \<pi>s)"
  using wf_ast_classical_problem4.restore_plan_split_valid
  unfolding wf_ast_classical_problem4_def
            def_explicated_conj_problem_def
            def_explicated_conj_problem_axioms_def
            wf_ast_classical_problem_def
  by simp

text \<open> Definedness translation preserves well-formedness and normalization. \<close>
lemma def_translate_prob_wf_compact:
  "wf_classical_problem \<Longrightarrow> ast_classical_problem.wf_classical_problem def_translate_prob"
  using wf_ast_classical_problem_dt.def_translate_prob_wf
  using wf_ast_classical_problem_dt_def wf_ast_classical_problem.intro by simp
lemma def_translate_normed_compact:
  "normalized_prob \<Longrightarrow> ast_classical_problem.normalized_prob def_translate_prob"
  by (rule def_translate_normalized)
lemma def_translate_valid_plan_iff_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow>
   ast_classical_problem.valid_classical_plan2 def_translate_prob \<pi>s \<longleftrightarrow> valid_classical_plan2 \<pi>s"
proof -
  assume "wf_classical_problem" "def_explicated_conj_prob"
  hence "def_explicated_conj_problem_dt P"
    by (simp add: def_explicated_conj_problem_dt_def wf_ast_classical_problem_dt_def
                  def_explicated_conj_problem_def def_explicated_conj_problem_axioms_def
                  wf_ast_classical_problem_def)
  from def_explicated_conj_problem_dt.def_translate_valid_plan_iff[OF this]
  show ?thesis .
qed
lemma def_translate_valid_iff_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow>
   (\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 def_translate_prob \<pi>s')"
proof -
  assume "wf_classical_problem" "def_explicated_conj_prob"
  hence "def_explicated_conj_problem_dt P"
    by (simp add: def_explicated_conj_problem_dt_def wf_ast_classical_problem_dt_def
                  def_explicated_conj_problem_def def_explicated_conj_problem_axioms_def
                  wf_ast_classical_problem_def)
  from def_explicated_conj_problem_dt.def_translate_valid_iff[OF this]
  show ?thesis .
qed

lemma restore_plan_def_translate_compact:
  "wf_classical_problem \<Longrightarrow> def_explicated_conj_prob \<Longrightarrow>
   ast_classical_problem.valid_classical_plan2 def_translate_prob \<pi>s \<Longrightarrow>
   valid_classical_plan2 (restore_plan_def_translate \<pi>s)"
  unfolding restore_plan_def_translate_def
  using def_translate_valid_plan_iff_compact by blast

lemma relax_wf_relaxed_compact:
  "wf_classical_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    ast_classical_problem.relaxed_prob relax_prob \<and> ast_classical_problem.wf_classical_problem relax_prob"
  using normalized_problem_rx.relax_relaxes normalized_problem_rx.relax_wf
  unfolding normalized_problem_rx_def normalized_problem_def' by simp
lemma relax_normed_compact:
  "wf_classical_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    ast_classical_problem.normalized_prob relax_prob"
  using normalized_problem_rx.relax_normed
  unfolding normalized_problem_rx_def normalized_problem_def' by simp
lemma relax_achievables_compact:
  "wf_classical_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    {a. achievable a} \<subseteq> {a. ast_classical_problem.achievable relax_prob a}"
  using normalized_problem_rx.relax_achievables
  unfolding normalized_problem_rx_def normalized_problem_def'
  by simp
lemma relax_applicables_compact:
  "wf_classical_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    {\<pi>. applicable \<pi>} \<subseteq> {\<pi>. ast_classical_problem.applicable relax_prob \<pi>}"
  using normalized_problem_rx.relax_applicables
  unfolding normalized_problem_rx_def normalized_problem_def'    
  by simp

thm grounder.ground_prob_grounded
thm wf_grounder.ground_prob_wf
lemma (in wf_grounder) ground_prob_normed:
  assumes "normalized_prob"
  shows "ast_classical_problem.normalized_prob ground_prob"
proof -
  have g: "is_conj (goal ground_prob)"
    using assms[unfolded normalized_prob_def]
    by (simp add: ground_prob_def ground_dom_def is_conj_ground_fmla)
  show ?thesis
    unfolding ast_classical_problem.normalized_prob_def
    using ground_prob_typeless ground_prob_prec_normed[OF assms] g by blast
qed
thm wf_grounder.valid_classical_plan_iff
thm wf_grounder.valid_classical_plan_left

end

subsection \<open> Normalization correctness \<close>

context ast_classical_problem begin

text \<open>\<open>P\<^sub>X\<close>: the explicated-and-degoaled-and-detyped problem, fed to the split step.\<close>
definition "P\<^sub>X \<equiv> ast_classical_problem.explicate_def_prob
  (ast_classical_problem.degoal_prob detype_classical_prob)"

definition "P\<^sub>N \<equiv> ast_classical_problem.split_prob P\<^sub>X"

definition "reconstruct_plan_norm \<pi>s \<equiv>
  ast_classical_domain.restore_plan_degoal detype_classical_dom
    (restore_plan_explicate
      (ast_classical_domain.restore_plan_split
        (ast_classical_domain.explicate_def_dom
          (domain (ast_classical_problem.degoal_prob detype_classical_prob)))
        \<pi>s))"

text \<open> goal and precondition normalization preserve type normalization \<close>
lemma goal_norm_preserves_typeless:
  "typeless_classical_problem \<Longrightarrow> ast_classical_problem.typeless_classical_problem (degoal_prob)"
  unfolding ast_classical_problem.typeless_classical_problem_def ast_classical_domain.typeless_classical_domain_def
    domain_signature.typeless_domain_signature_def
    degoal_prob_sel degoal_dom_sel
  unfolding goal_pred_decl_def goal_ac_def by auto

lemma goal_norm_preserves_typeless_gen:
  "ast_classical_problem.typeless_classical_problem P' \<Longrightarrow> ast_classical_problem.typeless_classical_problem (ast_classical_problem.degoal_prob P')"
  unfolding ast_classical_problem.typeless_classical_problem_def ast_classical_domain.typeless_classical_domain_def
    domain_signature.typeless_domain_signature_def
    Goal_Normalization_Locales.ast_classical_problem.degoal_prob_sel Goal_Normalization_Locales.ast_classical_problem.degoal_dom_sel
  unfolding Goal_Normalization_Locales.domain_signature.goal_pred_decl_def
    Goal_Normalization_Locales.ast_classical_domain.goal_ac_def by auto

lemma explicate_def_preserves_typeless_gen:
  "ast_classical_problem.typeless_classical_problem P' \<Longrightarrow> ast_classical_problem.typeless_classical_problem (ast_classical_problem.explicate_def_prob P')"
  unfolding ast_classical_problem.typeless_classical_problem_def ast_classical_domain.typeless_classical_domain_def
    domain_signature.typeless_domain_signature_def
    ast_classical_problem.explicate_def_prob_sel ast_classical_domain.explicate_def_dom_sel
  by (auto simp: explicate_def_ac_unfold)

lemma prec_norm_preserves_typeless:
  "typeless_classical_problem \<Longrightarrow> ast_classical_problem.typeless_classical_problem (split_prob)"
  unfolding ast_classical_problem.typeless_classical_problem_def ast_classical_domain.typeless_classical_domain_def
    domain_signature.typeless_domain_signature_def
    split_prob_sel split_dom_sel
  unfolding split_acs_def using split_ac_sel(2) by auto

lemma prec_norm_preserves_typeless_gen:
  "ast_classical_problem.typeless_classical_problem P' \<Longrightarrow> ast_classical_problem.typeless_classical_problem (ast_classical_problem.split_prob P')"
  unfolding ast_classical_problem.typeless_classical_problem_def ast_classical_domain.typeless_classical_domain_def
    domain_signature.typeless_domain_signature_def
    ast_classical_problem.split_prob_sel ast_classical_domain.split_dom_sel
  unfolding ast_classical_domain.split_acs_def
  using Precondition_Normalization.ast_classical_domain.split_ac_sel(2)
  by auto

text \<open> type and precondition normalization preserve goal normalization \<close>
lemma type_norm_preserves_goal_conj:
  "is_conj (goal P) \<Longrightarrow> is_conj (goal detype_classical_prob)"
  unfolding detype_classical_prob_sel .

lemma prec_norm_preserves_goal_conj:
  "is_conj (goal P) \<Longrightarrow> is_conj (goal split_prob)"
  unfolding split_prob_sel .

text \<open> Due to Either-types, type normalization can introduce disjunctions into preconditions,
  and it can thus potentially break precondition normalization. \<close>

text \<open> Goal normalization only preserves precondition normalization if the goal is a
  pure conjunction.\<close>

lemma goal_norm_preserves_prec_norm:
  assumes "prec_normed_dom"
    "is_conj (goal P)"
  shows "ast_classical_domain.prec_normed_dom (domain degoal_prob)"
  using assms(1) unfolding ast_classical_domain.prec_normed_dom_def
  unfolding degoal_prob_sel degoal_dom_sel
  unfolding goal_ac_def term_goal_def
  using map_preserves_isconj assms(2) by auto

theorem normalization_normalizes:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.normalized_prob P\<^sub>N"
  unfolding ast_classical_problem.normalized_prob_def P\<^sub>N_def P\<^sub>X_def
  apply (intro conjI)
  using prec_norm_preserves_typeless_gen explicate_def_preserves_typeless_gen goal_norm_preserves_typeless_gen ast_classical_problem2.prob_detyped assms
  apply simp
  apply (simp add: ast_classical_problem.split_prob_sel(1) ast_classical_problem4.prec_normed_dom)
  apply (unfold ast_classical_problem.split_prob_sel(4)
    Definedness_Normalization_Locales.ast_classical_problem.explicate_def_prob_sel(4)
    Goal_Normalization_Locales.ast_classical_problem.degoal_prob_sel(4))
  apply (unfold explicate_def_fmla_def)
  apply (unfold Definedness_Normalization_Locales.definedness_atoms_def)
  by simp
  

text \<open>\<open>P\<^sub>N\<close> carries the definedness-explicated conjunctive structure: it is established by
  \<open>explicate_def\<close> and preserved by precondition splitting. This is exactly the hypothesis that
  the \<open>def_translate\<close> validity-equivalence (\<^const>\<open>def_explicated_conj_problem_dt\<close>) consumes.\<close>
theorem P\<^sub>N_def_explicated_conj:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.def_explicated_conj_prob P\<^sub>N"
proof -
  have wfX: "ast_classical_problem.wf_classical_problem P\<^sub>X"
    unfolding P\<^sub>X_def
    using assms detype_prob_wf_compact
          ast_classical_problem.degoal_prob_wf_compact
          ast_classical_problem.explicate_def_prob_wf_compact by simp
  have deX: "ast_classical_problem.def_explicated_conj_prob P\<^sub>X"
    unfolding P\<^sub>X_def
    using assms detype_prob_wf_compact
          ast_classical_problem.degoal_prob_wf_compact
          ast_classical_problem.explicate_def_def_explicated_conj_compact by simp
  from wfX deX have "wf_ast_classical_problem4 P\<^sub>X"
    unfolding wf_ast_classical_problem4_def def_explicated_conj_problem_def
              def_explicated_conj_problem_axioms_def wf_ast_classical_problem_def by simp
  from wf_ast_classical_problem4.def_explicated_conj_split_prob[OF this]
  show ?thesis unfolding P\<^sub>N_def .
qed

theorem normalization_wf:
  "restrict_prob \<Longrightarrow> wf_classical_problem \<Longrightarrow> ast_classical_problem.wf_classical_problem P\<^sub>N"
  unfolding P\<^sub>N_def P\<^sub>X_def
  using detype_prob_wf_compact
        ast_classical_problem.degoal_prob_wf_compact
        ast_classical_problem.explicate_def_prob_wf_compact
        ast_classical_problem.explicate_def_def_explicated_conj_compact
        ast_classical_problem.split_prob_wf_compact
  by simp

theorem normalization_valid_iff:
  "restrict_prob \<Longrightarrow> wf_classical_problem \<Longrightarrow>
    (\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>N \<pi>s')"
  unfolding P\<^sub>N_def P\<^sub>X_def
  using detype_prob_wf_compact
        ast_classical_problem.degoal_prob_wf_compact
        ast_classical_problem.explicate_def_prob_wf_compact
        ast_classical_problem.explicate_def_def_explicated_conj_compact
        detyped_valid_iff_compact
        ast_classical_problem.degoaled_valid_iff_compact
        ast_classical_problem.explicate_def_valid_iff_compact
        ast_classical_problem.split_valid_iff_compact
  by metis

theorem normalization_reconstruct:
  "restrict_prob \<Longrightarrow> wf_classical_problem \<Longrightarrow>
    ast_classical_problem.valid_classical_plan2 P\<^sub>N \<pi>s \<Longrightarrow> valid_classical_plan2 (reconstruct_plan_norm \<pi>s)"
  unfolding P\<^sub>N_def P\<^sub>X_def reconstruct_plan_norm_def
  using detype_prob_wf_compact
        ast_classical_problem.degoal_prob_wf_compact
        ast_classical_problem.explicate_def_prob_wf_compact
        ast_classical_problem.explicate_def_def_explicated_conj_compact
        ast_classical_problem.restore_plan_split_valid_compact
        ast_classical_problem.restore_plan_explicate_valid_compact
        ast_classical_problem.degoal_plan_restore_compact
        detyped_valid_iff_compact
  by (metis ast_classical_problem.degoal_prob_sel(1) detype_classical_prob_sel(1)
            ast_classical_problem.explicate_def_prob_sel(1))

end

subsection \<open> Relaxation \<close>

context ast_classical_problem begin

definition "P\<^sub>T \<equiv> ast_classical_problem.def_translate_prob P\<^sub>N"

definition "P\<^sub>R \<equiv> ast_classical_problem.relax_prob P\<^sub>T"

lemma relaxation_applicables:
  assumes "restrict_prob" "wf_classical_problem"
  shows "{\<pi>. ast_classical_problem.applicable P\<^sub>T \<pi>} \<subseteq> {\<pi>. ast_classical_problem.applicable P\<^sub>R \<pi>}"
proof -
  have wf_N: "ast_classical_problem.wf_classical_problem P\<^sub>N" using assms normalization_wf by simp
  have norm_N: "ast_classical_problem.normalized_prob P\<^sub>N" using assms normalization_normalizes by simp
  have wf_T: "ast_classical_problem.wf_classical_problem P\<^sub>T"
    using wf_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_prob_wf_compact)
  have norm_T: "ast_classical_problem.normalized_prob P\<^sub>T"
    using norm_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  show ?thesis
    unfolding P\<^sub>R_def
    using wf_T norm_T by (rule ast_classical_problem.relax_applicables_compact)
qed

lemma relaxation_achievables:
  assumes "restrict_prob" "wf_classical_problem"
  shows "{a. ast_classical_problem.achievable P\<^sub>T a} \<subseteq> {a. ast_classical_problem.achievable P\<^sub>R a}"
proof -
  have wf_N: "ast_classical_problem.wf_classical_problem P\<^sub>N" using assms normalization_wf by simp
  have norm_N: "ast_classical_problem.normalized_prob P\<^sub>N" using assms normalization_normalizes by simp
  have wf_T: "ast_classical_problem.wf_classical_problem P\<^sub>T"
    using wf_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_prob_wf_compact)
  have norm_T: "ast_classical_problem.normalized_prob P\<^sub>T"
    using norm_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  show ?thesis
    unfolding P\<^sub>R_def
    using wf_T norm_T by (rule ast_classical_problem.relax_achievables_compact)
qed

lemma relaxation_wf_relaxed_normed:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.wf_classical_problem P\<^sub>R" "ast_classical_problem.relaxed_prob P\<^sub>R" "ast_classical_problem.normalized_prob P\<^sub>R"
proof -
  have wf_N: "ast_classical_problem.wf_classical_problem P\<^sub>N" using assms normalization_wf by simp
  have norm_N: "ast_classical_problem.normalized_prob P\<^sub>N" using assms normalization_normalizes by simp
  have wf_T: "ast_classical_problem.wf_classical_problem P\<^sub>T"
    using wf_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_prob_wf_compact)
  have norm_T: "ast_classical_problem.normalized_prob P\<^sub>T"
    using norm_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  show "ast_classical_problem.wf_classical_problem P\<^sub>R" "ast_classical_problem.relaxed_prob P\<^sub>R" "ast_classical_problem.normalized_prob P\<^sub>R"
    unfolding P\<^sub>R_def
    using wf_T norm_T ast_classical_problem.relax_wf_relaxed_compact ast_classical_problem.relax_normed_compact by blast+
qed

subsection \<open> Reachability Analysis & Grounding via Certificate Checking \<close>

context
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes px_numfree: "numeric_free_problem (ast_classical_problem.relax_prob P\<^sub>T)"
      and nonempty: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and grounding_cert: "normalized_problem_rx.grounding_checks P\<^sub>T M"
begin

lemma P_T_normalized_problem_rx:
  assumes "restrict_prob" "wf_classical_problem"
  shows "normalized_problem_rx P\<^sub>T"
proof -
  have wf_N: "ast_classical_problem.wf_classical_problem P\<^sub>N" using assms normalization_wf by simp
  have norm_N: "ast_classical_problem.normalized_prob P\<^sub>N" using assms normalization_normalizes by simp
  have wf_T: "ast_classical_problem.wf_classical_problem P\<^sub>T"
    using wf_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_prob_wf_compact)
  have norm_T: "ast_classical_problem.normalized_prob P\<^sub>T"
    using norm_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  show ?thesis
    unfolding normalized_problem_rx_def normalized_problem_def'
    using wf_T norm_T by blast
qed

lemma certified_reachability_i:
  assumes "restrict_prob" "wf_classical_problem"
  shows "certified_reachability P\<^sub>T M dc"
proof -
  interpret rx: normalized_problem_rx P\<^sub>T using P_T_normalized_problem_rx[OF assms] .
  show ?thesis
    apply unfold_locales
    using px_numfree nonempty cert grounding_cert numeric_free_problem.num_free_prob[OF px_numfree]
    by simp_all
qed

definition "P\<^sub>G_cert \<equiv> grounder.ground_prob P\<^sub>T
  (normalized_problem_rx.cert_facts_of P\<^sub>T M)
  (remdups (normalized_problem_rx.cert_ops_of P\<^sub>T M))"

definition "reconstruct_plan_ground_cert \<pi>s \<equiv>
  reconstruct_plan_norm (restore_plan_def_translate
    (grounder.restore_ground_plan (remdups (normalized_problem_rx.cert_ops_of P\<^sub>T M)) \<pi>s))"

lemma wf_ground_cert_problem:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.wf_classical_problem P\<^sub>G_cert"
    "ast_classical_problem.normalized_prob P\<^sub>G_cert"
    "ast_classical_problem.grounded_prob P\<^sub>G_cert"
proof -
  interpret cr: certified_reachability P\<^sub>T M dc using certified_reachability_i[OF assms] .
  have norm_T: "ast_classical_problem.normalized_prob P\<^sub>T"
    using normalization_normalizes[OF assms] unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  have pg_eq: "P\<^sub>G_cert = cr.wfg.ground_prob"
    unfolding P\<^sub>G_cert_def cr.cert_facts'_def cr.cert_ops'_def by simp
  show "ast_classical_problem.wf_classical_problem P\<^sub>G_cert"
    unfolding pg_eq using cr.wfg.ground_prob_wf by simp
  show "ast_classical_problem.normalized_prob P\<^sub>G_cert"
    unfolding pg_eq using cr.wfg.ground_prob_normed[OF norm_T] by simp
  show "ast_classical_problem.grounded_prob P\<^sub>G_cert"
    unfolding pg_eq using cr.wfg.ground_prob_grounded by simp
qed

lemma ground_cert_num_free:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.num_free_prob P\<^sub>G_cert"
proof -
  interpret cr: certified_reachability P\<^sub>T M dc using certified_reachability_i[OF assms] .
  have pg_eq: "P\<^sub>G_cert = cr.wfg.ground_prob"
    unfolding P\<^sub>G_cert_def cr.cert_facts'_def cr.cert_ops'_def by simp
  show ?thesis unfolding pg_eq using cr.wfg.ground_prob_num_free by simp
qed

lemma ground_cert_plan_valid_iff:
  assumes "restrict_prob" "wf_classical_problem"
  shows "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>G_cert \<pi>s')"
proof -
  interpret cr: certified_reachability P\<^sub>T M dc using certified_reachability_i[OF assms] .
  have "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>N \<pi>s')"
    using assms normalization_valid_iff by simp
  also have "... \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>T \<pi>s')"
    using ast_classical_problem.def_translate_valid_iff_compact[OF normalization_wf[OF assms] P\<^sub>N_def_explicated_conj[OF assms]]
    unfolding P\<^sub>T_def by simp
  also have "... \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 P\<^sub>G_cert \<pi>s')"
    unfolding P\<^sub>G_cert_def
    using cr.wfg.valid_classical_plan_iff[unfolded cr.cert_facts'_def cr.cert_ops'_def] by simp
  finally show ?thesis .
qed

lemma ground_cert_plan_reconstruct:
  assumes "restrict_prob" "wf_classical_problem"
  shows "ast_classical_problem.valid_classical_plan2 P\<^sub>G_cert \<pi>s \<Longrightarrow>
    valid_classical_plan2 (reconstruct_plan_ground_cert \<pi>s)"
proof -
  assume p: "ast_classical_problem.valid_classical_plan2 P\<^sub>G_cert \<pi>s"
  interpret cr: certified_reachability P\<^sub>T M dc using certified_reachability_i[OF assms] .
  let ?q = "grounder.restore_ground_plan (remdups (normalized_problem_rx.cert_ops_of P\<^sub>T M)) \<pi>s"
  have "ast_classical_problem.valid_classical_plan2 P\<^sub>T ?q"
    using p[unfolded P\<^sub>G_cert_def] cr.wfg.valid_classical_plan_left[unfolded cr.cert_facts'_def cr.cert_ops'_def] by simp
  hence "ast_classical_problem.valid_classical_plan2 (ast_classical_problem.def_translate_prob P\<^sub>N) ?q"
    unfolding P\<^sub>T_def .
  hence "ast_classical_problem.valid_classical_plan2 P\<^sub>N (restore_plan_def_translate ?q)"
    using ast_classical_problem.restore_plan_def_translate_compact[OF normalization_wf[OF assms] P\<^sub>N_def_explicated_conj[OF assms]] by blast
  hence "valid_classical_plan2 (reconstruct_plan_norm (restore_plan_def_translate ?q))"
    using assms normalization_reconstruct by simp
  thus "valid_classical_plan2 (reconstruct_plan_ground_cert \<pi>s)"
    unfolding reconstruct_plan_ground_cert_def .
qed

end

end
end