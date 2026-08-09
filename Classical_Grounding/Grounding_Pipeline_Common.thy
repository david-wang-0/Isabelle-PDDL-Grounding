theory Grounding_Pipeline_Common
  imports Classical_Type_Normalization.Classical_Type_Normalization_Semantics
    Classical_Goal_Normalization.Classical_Goal_Normalization_Semantics
    Classical_Definedness_Normalization.Classical_Definedness_Normalization_Semantics
    Classical_Precondition_Normalization.Classical_Precondition_Normalization_Semantics
    Classical_Definedness_Translation.Classical_Definedness_Translation_Semantics
    Classical_PDDL_Relaxation.Classical_PDDL_Relaxation_Semantics
    Classical_Reachability_Analysis.Classical_Certified_Grounding_Semantics
    Classical_Grounded_PDDL.Classical_Grounded_PDDL_Factorization
    Grounding_Classical_Common.Numeric_Free
begin

text \<open>The stage-to-stage transformations shared by \<^emph>\<open>every\<close> grounding entry point:
  type/goal/definedness/precondition normalization (\<^term>\<open>P\<^sub>X\<close>, \<^term>\<open>P\<^sub>N\<close>),
  definedness translation (\<^term>\<open>P\<^sub>T\<close>) and delete-relaxation (\<^term>\<open>P\<^sub>R\<close>), together with
  the well-formedness / normalization / plan-equivalence theorems of each step. Nothing here mentions
  a reachability certificate or a grounder product --- those are the branch-specific parts, in
  \<^verbatim>\<open>Grounding_Pipeline_Numeric\<close> (the numeric-fluent-retaining grounder) and
  \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close> (the propositional grounder and the STRIPS conversion).

  \<^bold>\<open>The chain at a glance.\<close> Reading the input problem as \<open>P\<close>:
  \<^item> \<^emph>\<open>stage 1\<close> type normalization --- types become unary predicates;
  \<^item> \<^emph>\<open>stage 2\<close> goal normalization --- the goal becomes one fresh nullary atom;
  \<^item> \<^emph>\<open>stage 3\<close> definedness normalization --- implicit numeric definedness becomes explicit
    conjuncts, giving \<open>P\<^sub>X\<close>;
  \<^item> \<^emph>\<open>stage 4\<close> precondition normalization --- preconditions become DNF disjuncts, one action
    each, giving \<open>P\<^sub>N\<close>;
  \<^item> \<^emph>\<open>stage 5\<close> definedness translation --- definedness atoms become ordinary predicates, giving
    \<open>P\<^sub>T\<close>, the problem that is grounded;
  \<^item> \<^emph>\<open>stage 6\<close> delete-relaxation --- \<open>P\<^sub>R\<close>, the monotone over-approximation reachability is
    read off, and the only stage that is not plan-equivalent.

  Stages 1--5 each preserve well-formedness, are proven solvability-equivalent, and come with a
  restoration map; composing those gives \<open>normalization_wf\<close>, \<open>normalization_valid_iff\<close> and
  \<open>normalization_reconstruct\<close>. Stage 6 instead contributes two containments
  (\<open>relaxation_achievables\<close>, \<open>relaxation_applicables\<close>).\<close>

subsection \<open> Grounding preserves normalization \<close>

text \<open>Numeric-freeness preservation is proven \<^emph>\<open>stage-locally\<close>, adjacent to each stage: the fact
  folder's \<open>fold_prob_num_free\<close> lives in
  \<^theory>\<open>Classical_Grounded_PDDL.Classical_Grounded_PDDL_Num_Free\<close>, the variable-freeness
  stage's \<open>varfree_inst_prob_num_free\<close> in \<^verbatim>\<open>Classical_Variable_Freeness_Num_Free\<close>, and the
  one-shot grounder's \<open>ground_prob_num_free\<close> derives compositionally from the folder's theorem in
  \<^theory>\<open>Classical_Grounded_PDDL.Classical_Grounded_PDDL_Factorization\<close>. Here we keep only the
  \<^emph>\<open>normalization\<close> covariance: the grounded problem is typeless, and precondition-normalized
  whenever its input is.\<close>

text \<open>The pieces this covariance is assembled from are \<^emph>\<open>stage-local\<close>, matching the placement
  rule above --- the grounded product is the composite of two stages, so each proves its own half:
  \<^item> the instantiation stage's \<open>varfree_inst_normed\<close> (\<^verbatim>\<open>Classical_Variable_Freeness\<close>) --- the
    declarations are copied verbatim, the objects move into the constants, and every instantiated
    schema is parameterless;
  \<^item> the folding stage's \<open>fold_prob_normed\<close> (\<^verbatim>\<open>Classical_Grounded_PDDL\<close>) --- \<open>ground_fmla\<close>
    maps literals to literals, and typelessness comes free from \<open>fold_prob_grounded\<close> via
    \<open>typeless_classical_problem_of_grounded\<close>.

  Nothing about the two stages needs restating here: the grounded product's parameterless actions
  and its selectors are already \<open>fold_ac_sel\<close> / \<open>fold_dom_sel\<close>.\<close>

subsection \<open> Important theorems from individual grounding pipeline steps.
  Setting up compact notations for some of them to remove contexts. \<close>

text \<open>Every stage proves its correctness inside a locale bundling that stage's input requirements
  (well-formedness, plus whatever invariant its predecessor established), so chaining the stages
  naively would mean interpreting one locale per step at a different problem term. The
  \<open>_compact\<close> lemmas below remove that friction: each stage theorem is restated \<^emph>\<open>at\<close>
  \<^locale>\<open>ast_classical_problem\<close> as a plain implication whose premises are exactly the stage's
  requirements, so the pipeline theorems downstream chain them without a single interpretation.
  A stage contributes up to four facts:
  \<^item> the selector equations \<open>_sel\<close> (cited by \<open>thm\<close> here for reference) --- what the stage does to
    each component of the problem record;
  \<^item> \<open>_wf_compact\<close> --- the stage maps well-formed problems to well-formed problems;
  \<^item> \<open>_valid_iff_compact\<close> --- plan-existence equivalence, the direction that matters for a
    \<^emph>\<open>planner\<close> (solvable before iff solvable after);
  \<^item> \<open>restore_plan_*_compact\<close> --- the constructive converse: a concrete map turning a plan of the
    stage's output into a plan of its input, which is what the pipeline's plan reconstruction
    composes in reverse.\<close>

context ast_classical_problem begin

text \<open>\<^bold>\<open>Stage 1 --- type normalization (detyping).\<close> \<open>detype_classical_prob\<close> erases the PDDL type
  system: each declared type becomes a unary predicate, each object's type is asserted as a
  supertype fact in the initial state, and every typed parameter contributes a corresponding
  precondition atom, leaving all declarations at the universal type. It is the one stage whose plan
  equivalence holds for the \<^emph>\<open>same\<close> plan list (\<open>detyped_valid_iff_compact\<close> is an iff on
  \<open>\<pi>s\<close>, not merely on existence), so plan reconstruction needs no inverse map for it. The premise
  \<open>restrict_prob\<close> is the input restriction on the type graph that detyping needs.\<close>
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

text \<open>\<^bold>\<open>Stage 2 --- goal normalization.\<close> \<open>degoal_prob\<close> replaces an arbitrary goal formula by a
  single fresh nullary predicate, and adds one fresh action whose precondition is the original goal
  and whose only effect asserts that predicate. Downstream every stage therefore sees a goal that is
  a single atom --- which is what makes the STRIPS encoding's single-goal-literal side-condition
  discharge later on. Because a plan must now append the extra goal action, the equivalence is in
  \<^emph>\<open>existence\<close> form only, and \<open>restore_plan_degoal\<close> is the map that strips it again.\<close>
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

text \<open>\<^bold>\<open>Stage 3 --- definedness normalization (explication).\<close> In the PDDL semantics a numeric
  expression is only meaningful where every fluent it reads is assigned and no divisor is zero;
  those side conditions are \<^emph>\<open>implicit\<close> in the evaluation. \<open>explicate_def_prob\<close> makes them
  syntactic: each precondition and the goal are conjoined with the definedness atoms and
  divisor-nonzero atoms of the expressions occurring in them. The output satisfies
  \<open>def_explicated_conj_prob\<close>, the invariant the definedness \<^emph>\<open>translation\<close> (stage 5) consumes,
  and which precondition splitting is proven to preserve.\<close>
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

text \<open>\<^bold>\<open>Stage 4 --- precondition normalization (splitting).\<close> \<open>split_prob\<close> puts every action's
  precondition into disjunctive normal form and emits \<^emph>\<open>one action per disjunct\<close>, so that
  afterwards each precondition is a plain conjunction of literals (\<open>prec_normed_dom\<close>). This is what
  lets the grounder read an operator's preconditions off as a fact list, and what the datalog
  encoding of reachability needs in order to turn one action into one rule per disjunct. The
  premise \<open>def_explicated_conj_prob\<close> is stage 3's invariant; splitting preserves it
  (\<open>P\<^sub>N_def_explicated_conj\<close> below).\<close>
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

text \<open>\<^bold>\<open>Stage 5 --- definedness translation.\<close> \<open>def_translate_prob\<close> discharges the definedness
  conditions that stage 3 made explicit by \<^emph>\<open>propositionalizing\<close> them: each definedness /
  divisor-nonzero atom is replaced by a fresh predicate, whose truth the actions maintain (a
  numeric effect that assigns a fluent also asserts its definedness predicate). After it, no
  reasoning about undefinedness is left in the preconditions --- the remaining numeric content is
  ordinary comparisons --- which is what the reachability encoding downstream assumes.

  Two properties make this stage the cheapest link in the chain: it preserves normalization
  (\<open>def_translate_normed_compact\<close>, so stage 4's work is not undone), and its plan equivalence holds
  for the \<^emph>\<open>same\<close> plan (\<open>def_translate_valid_plan_iff_compact\<close>), so
  \<open>restore_plan_def_translate\<close> is the identity map.\<close>
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

text \<open>\<^bold>\<open>Stage 6 --- delete-relaxation.\<close> \<open>relax_prob\<close> drops the negative (deleting) part of every
  effect, so no atom, once achieved, is ever lost: truth grows monotonically along any execution.
  Unlike stages 1--5 this is \<^emph>\<open>not\<close> an equivalence-preserving transformation and it is
  deliberately not given a plan-restoration map. Its only role is as an \<^emph>\<open>over-approximation\<close>
  device: the two containments below --- every achievable fact of the input is achievable in the
  relaxation (\<open>relax_achievables_compact\<close>), every applicable ground action is applicable in it
  (\<open>relax_applicables_compact\<close>) --- are what license reading reachability off the monotone problem,
  where a least-fixpoint datalog computation answers it.

  \<^bold>\<open>The relaxation is only a lens, never the thing that gets grounded.\<close> Grounding the relaxed
  problem would be unsound (it has no deletes); the grounder is applied to \<open>P\<^sub>T\<close>, with the
  relaxation used purely to justify that the certified fact/operator set is a superset of what
  \<open>P\<^sub>T\<close> can reach.\<close>
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

text \<open>\<^bold>\<open>The grounding stage, seen from the normalization side.\<close> The grounder itself (its
  well-formedness and plan-equivalence theorems, cited below) is developed in the
  \<open>Grounded_PDDL\<close> stage; what belongs here is that it is \<^emph>\<open>invariant-preserving\<close> for the
  properties this file's chain establishes. The grounded problem is trivially typeless (every
  action loses its parameters), its preconditions stay conjunctive because instantiation and fact
  folding map literals to literals, and its goal stays conjunctive for the same reason --- together,
  \<open>ground_prob_normed\<close>. This is what allows the branch pipelines to apply further normalization-
  indexed results to the grounder's output.\<close>
thm fact_folder.fold_prob_grounded
thm wf_grounder.ground_prob_wf
lemma (in wf_grounder) ground_prob_normed:
  assumes "normalized_prob"
  shows "ast_classical_problem.normalized_prob P\<^sub>G"
  using ff.fold_prob_normed[OF varfree_inst_normed[OF assms]] .
thm wf_grounder.valid_classical_plan_iff
thm wf_grounder.valid_classical_plan_left

end

subsection \<open> Normalization correctness \<close>

text \<open>The stage lemmas above are now composed into the \<^emph>\<open>normalization chain\<close> and its four
  end-to-end theorems. Two abbreviations name the intermediate products --- \<open>P\<^sub>X\<close> after stages
  1--3, \<open>P\<^sub>N\<close> after stage 4 --- and \<open>reconstruct_plan_norm\<close> runs the stage restorers in
  \<^emph>\<open>reverse\<close> order (split, then explicate, then degoal; detyping needs none, its equivalence
  being on the same plan).

  What the four theorems say about \<open>P\<^sub>N\<close>, for a restricted well-formed input:
  \<^item> \<open>normalization_normalizes\<close> --- it is normalized: typeless, precondition-normalized, with a
    conjunctive goal. This is the input contract of everything downstream.
  \<^item> \<open>P\<^sub>N_def_explicated_conj\<close> --- it still carries stage 3's explicated structure, the hypothesis
    the definedness translation consumes.
  \<^item> \<open>normalization_wf\<close> --- it is well-formed.
  \<^item> \<open>normalization_valid_iff\<close> / \<open>normalization_reconstruct\<close> --- it is solvable iff the input is,
    and any of its plans maps back to a concrete plan of the input.

  The interesting subtlety is that the stages do not commute and do not blindly preserve each
  other's invariants: the lemmas immediately below record which ones actually survive which stage
  (and, in the two comments, which ones do \<^emph>\<open>not\<close>), and that is what pins the chain's order.\<close>

context ast_classical_problem begin

text \<open>\<open>P\<^sub>X\<close>: the explicated-and-degoaled-and-detyped problem, fed to the split step.\<close>
definition "P\<^sub>X \<equiv> ast_classical_problem.explicate_def_prob
  (ast_classical_problem.degoal_prob detype_classical_prob)"

text \<open>\<open>P\<^sub>N\<close>: the \<^emph>\<open>normalized\<close> problem --- \<open>P\<^sub>X\<close> with its preconditions split into DNF
  disjuncts. This is the end of the equivalence-preserving normalization chain and the problem all
  correctness statements of the pipeline are phrased against.\<close>
definition "P\<^sub>N \<equiv> ast_classical_problem.split_prob P\<^sub>X"

text \<open>Plan reconstruction for the whole chain: undo the stages in reverse (split \<open>\<rightarrow>\<close> explicate
  \<open>\<rightarrow>\<close> degoal). Detyping contributes no step --- it validates the very same plan list.\<close>
definition "reconstruct_plan_norm \<pi>s \<equiv>
  ast_classical_domain.restore_plan_degoal detype_classical_dom
    (restore_plan_explicate
      (ast_classical_domain.restore_plan_split \<pi>s))"

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
    Classical_Goal_Normalization_Locales.ast_classical_problem.degoal_prob_sel Classical_Goal_Normalization_Locales.ast_classical_problem.degoal_dom_sel
  unfolding Goal_Normalization.domain_signature.goal_pred_decl_def
    Classical_Goal_Normalization_Locales.ast_classical_domain.goal_ac_def by auto

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
  using Classical_Precondition_Normalization.ast_classical_domain.split_ac_sel(2)
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
    Classical_Definedness_Normalization_Locales.ast_classical_problem.explicate_def_prob_sel(4)
    Classical_Goal_Normalization_Locales.ast_classical_problem.degoal_prob_sel(4))
  apply (unfold explicate_def_fmla_def)
  apply (unfold Definedness_Normalization.definedness_atoms_def
    Definedness_Normalization.divisor_zero_atoms_def)
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

text \<open>The last two links of the shared chain, and the point at which the two branch pipelines take
  over. \<open>P\<^sub>T\<close> is the problem that actually gets grounded; \<open>P\<^sub>R\<close> is never grounded --- it exists
  so that reachability may be computed monotonically and then transferred back to \<open>P\<^sub>T\<close> by the
  containments proven here.\<close>

context ast_classical_problem begin

text \<open>\<open>P\<^sub>T\<close>: the \<^emph>\<open>translated\<close> problem --- \<open>P\<^sub>N\<close> after stage 5, with definedness conditions
  turned into ordinary predicates. Every downstream statement (the reachability gate, both
  grounders, the STRIPS encoding) is indexed by this problem.\<close>
definition "P\<^sub>T \<equiv> ast_classical_problem.def_translate_prob P\<^sub>N"

text \<open>\<open>P\<^sub>R\<close>: the delete-relaxation of \<open>P\<^sub>T\<close>, the monotone problem whose least fixpoint the
  datalog rules compute. The certificate is checked against \<open>dl_rules P\<^sub>R\<close>, but the grounder is
  run on \<open>P\<^sub>T\<close> --- see the caveat at stage 6.\<close>
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

text \<open>\<open>P\<^sub>T\<close> is a \<^locale>\<open>normalized_problem_rx\<close> as soon as the input problem is restricted and
  well-formed --- no reachability certificate and no re-check plays any part in it. Stated here, at
  the end of the shared transformation chain, so that both branches use one copy.\<close>
lemma normalized_problem_rx_P\<^sub>T:
  assumes rp: "restrict_prob"
      and wf: "wf_classical_problem"
  shows "normalized_problem_rx P\<^sub>T"
proof -
  have wf_N: "ast_classical_problem.wf_classical_problem P\<^sub>N" using rp wf normalization_wf by simp
  have norm_N: "ast_classical_problem.normalized_prob P\<^sub>N" using rp wf normalization_normalizes by simp
  have wf_T: "ast_classical_problem.wf_classical_problem P\<^sub>T"
    using wf_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_prob_wf_compact)
  have norm_T: "ast_classical_problem.normalized_prob P\<^sub>T"
    using norm_N unfolding P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  show ?thesis
    unfolding normalized_problem_rx_def normalized_problem_def'
    using wf_T norm_T by blast
qed

end

end
