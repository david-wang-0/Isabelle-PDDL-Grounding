theory Grounding_Pipeline_Common_Executable
  imports Grounding_Pipeline_STRIPS Code_Setup
    Datalog_Certification.Datalog_Certificate_Code
    Datalog_Graph.Datalog_Cycle_DFS
begin

text \<open>Importing the DFS check pulls in the graph library's red-black-tree constructors \<open>R\<close> / \<open>B\<close>
  (from \<^theory>\<open>HOL-Data_Structures.RBT_Set\<close>), which shadow the pipeline's habitual variable name
  \<open>R\<close> for the relaxed problem. Hide them at the surface (the RBT \<^const>\<open>dl_acyclic_dfs\<close> code, defined
  upstream, is unaffected) so \<open>R\<close> reads as a variable again downstream.\<close>
hide_const (open) R B

section \<open>Executable grounding pipeline: shared infrastructure\<close>

text \<open>The re-checked executable grounding machinery common to \<^emph>\<open>all\<close> grounding entry points --- the
  STRIPS grounders (theory \<open>Grounding_Pipeline_STRIPS_Executable\<close>) and the numeric
  fluent-retaining grounder (theory \<open>Grounding_Pipeline_Numeric_Executable\<close>) both
  build on it. Everything here is driven by an \<^emph>\<open>untrusted, re-checked\<close> reachability oracle
  \<open>f :: dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate\<close> (Nemo): given the datalog program
  of the relaxed problem it returns a candidate model \<open>M\<close> together with a generic datalog certificate
  \<open>dc\<close>; the kernel re-checks \<^const>\<open>dl_certified_model_exec\<close> / \<^const>\<open>dl_certified_model_dfs\<close> +
  \<^const>\<open>normalized_problem_rx.grounding_checks\<close>. Soundness never depends on trusting the oracle.\<close>

subsection \<open>The datalog program handed to the reachability oracle\<close>

datatype dl_program = DLProgram
  (dl_clauses: "pddl_dl_clause list")   \<comment> \<open>rules ++ initial facts (facts: ground, empty body)\<close>
  (dl_consts: "object list")            \<comment> \<open>the object universe (the oracle's \<open>dom\<close> guards)\<close>

definition dl_program_of where
  [code]: "dl_program_of P \<equiv>
     (let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P) in
        DLProgram (dl_rules R) (ast_classical_problem.const_names R))"

text \<open>The numeric-freeness check (\<^const>\<open>ast_classical_problem.num_free_prob\<close>) entered the executable
  path via \<open>ground_via_cert'\<close>; register its (assumption-free, classical-only) code equations.\<close>
declare num_free_code [code]

subsection \<open>Executable mirrors of the grounding checks\<close>

text \<open>The \<^const>\<open>normalized_problem_rx\<close>-side checks (\<^const>\<open>normalized_problem_rx.cert_ops_of\<close>,
  \<^const>\<open>normalized_problem_rx.cert_facts_of\<close>, \<^const>\<open>normalized_problem_rx.grounding_checks\<close>) live in
  a locale \<^emph>\<open>with\<close> assumptions, so their defining equations are guarded by the locale predicate and
  are not code equations. Each mirror below replays the locale body verbatim (the bodies do not use
  the locale assumptions), keyed on the certified fact list \<open>M\<close>; the \<open>_eq\<close> bridges record equality
  under the locale predicate for the soundness link.\<close>

definition cert_ops_of_exec where
  [code]: "cert_ops_of_exec N M \<equiv> concat (map
       (cert_ops_for_clause (ast_classical_problem.const_names (ast_classical_problem.relax_prob N))
                            (organize_facts (map fact_to_facty M)))
       (ast_classical_problem.a_clauses (ast_classical_problem.relax_prob N)))"

definition extra_eff_atoms_of_exec where
  [code]: "extra_eff_atoms_of_exec N M \<equiv>
     remdups (concat (map (\<lambda>\<pi>.
        let eff = ground_action.effect (the (simple_action_instantiations.res_inst
                    (ast_classical_domain.resolve_classical_action_schema (domain N))
                    instantiate_classical_action_schema \<pi>))
        in adds eff @ dels eff) (cert_ops_of_exec N M)))"

definition cert_facts_of_exec where
  [code]: "cert_facts_of_exec N M \<equiv> remdups (map fact_to_facty M @ extra_eff_atoms_of_exec N M)"

definition grounding_checks_exec where
  [code]: "grounding_checks_exec N M \<equiv>
     (\<forall>a \<in> set (cert_facts_of_exec N M).
        domain_signature.wf_fmla_atom (types (domain N)) (predicates (domain N))
          (problem_signature.objT (consts (domain N)) (objects N)) a)
   \<and> (\<forall>\<pi> \<in> set (cert_ops_of_exec N M). ast_classical_problem.wf_classical_plan_action N \<pi>)
   \<and> (\<forall>\<pi> \<in> set (cert_ops_of_exec N M).
        let eff = ground_action.effect (the (simple_action_instantiations.res_inst
                    (ast_classical_domain.resolve_classical_action_schema (domain N))
                    instantiate_classical_action_schema \<pi>))
        in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> (cert_facts_of_exec N M))
   \<and> (\<forall>\<pi> \<in> set (cert_ops_of_exec N M).
        covered (ground_action.precondition (the (simple_action_instantiations.res_inst
                   (ast_classical_domain.resolve_classical_action_schema (domain N))
                   instantiate_classical_action_schema \<pi>))) (cert_facts_of_exec N M))
   \<and> covered (goal N) (cert_facts_of_exec N M)
   \<and> (\<forall>f \<in> set (init N). is_predAtom f)
   \<and> (\<forall>\<pi> \<in> set (cert_ops_of_exec N M).
        numeric_effects (ground_action.effect (the (simple_action_instantiations.res_inst
          (ast_classical_domain.resolve_classical_action_schema (domain N))
          instantiate_classical_action_schema \<pi>))) = [])"

text \<open>The \<^emph>\<open>numeric-fluent-retaining\<close> re-check: the single ops-well-formedness obligation of
  \<^const>\<open>grounding_checks_exec\<close> (its \<open>covered\<close>-coverage, \<open>facts\<close>-wf and numeric-freeness conjuncts are
  dropped --- the fluent grounder needs none of them, and \<^const>\<open>covered\<close> rejects the retained numeric
  atoms anyway). Executable twin of \<^const>\<open>normalized_problem_rx.numeric_grounding_checks\<close>; gates the
  fluent grounder, so a task whose reachable ops still carry numeric effects can pass.\<close>
definition numeric_grounding_checks_exec where
  [code]: "numeric_grounding_checks_exec N M \<equiv>
     (\<forall>\<pi> \<in> set (cert_ops_of_exec N M). ast_classical_problem.wf_classical_plan_action N \<pi>)"

subsection \<open>Grounding a problem against a certified fact list\<close>

text \<open>Unconditional executable twin of \<^verbatim>\<open>P\<^sub>G_cert\<close>, replayed at the top level as a code-generable
  function keyed on the certified facts \<open>M\<close>. This is the \<^emph>\<open>propositional\<close> grounder
  (\<^const>\<open>grounder.ground_prob\<close>, numerics compiled away); the fluent-retaining twin
  \<open>numeric_ground_by_cert\<close> lives with the numeric grounder.\<close>
definition ground_by_cert where
  [code]: "ground_by_cert P M \<equiv>
     grounder.ground_prob (ast_classical_problem.P\<^sub>T P)
       (cert_facts_of_exec (ast_classical_problem.P\<^sub>T P) M)
       (remdups (cert_ops_of_exec (ast_classical_problem.P\<^sub>T P) M))"

subsection \<open>Shared code equations for plan reconstruction\<close>

text \<open>The grounder-level reconstruction operations reused by every reconstructor (both the STRIPS
  \<open>reconstruct_plan_by_cert\<close> and the grounded-PDDL \<open>reconstruct_plan_by_cert_numeric\<close>); the
  STRIPS-only code equations (\<open>restore_prefix\<close>, \<open>restore_pddl_pa\<close>, the STRIPS model) stay with the
  STRIPS grounders.\<close>
declare grounder.op_names_def[code]
declare grounder.op_map_def[code]
declare grounder.restore_ground_pa.simps[code]
declare ast_classical_problem.reconstruct_plan_norm_def[code]

subsection \<open>Grounded-plan restoration (no STRIPS prefix; shared by both grounders)\<close>

text \<open>Executable twin of the abstract reconstructors \<^const>\<open>ast_classical_problem.reconstruct_plan_ground_cert\<close>
  (propositional) and \<open>ast_classical_problem.numeric_reconstruct_plan_ground_cert\<close> (numeric, downstream):
  a plan of a grounded PDDL problem is restored to a plan of the original \<open>P\<close> by undoing grounding
  (\<^const>\<open>grounder.restore_ground_plan\<close>) \<open>\<rightarrow>\<close> def-translation \<open>\<rightarrow>\<close> normalization. Unlike the STRIPS
  \<open>reconstruct_plan_by_cert\<close> there is no \<open>restore_prefix\<close> step: the input is already a grounded-problem
  plan (both the propositional and numeric error-monad grounders return grounded PDDL, not STRIPS). The
  propositional \<open>_eq\<close> bridge is in the STRIPS executable theory; the numeric one is in the numeric
  executable theory.\<close>
definition reconstruct_plan_by_cert_numeric where
  [code]: "reconstruct_plan_by_cert_numeric P M \<pi>s \<equiv>
     ast_classical_problem.reconstruct_plan_norm P
       (restore_plan_def_translate
          (grounder.restore_ground_plan (remdups (cert_ops_of_exec (ast_classical_problem.P\<^sub>T P) M)) \<pi>s))"

subsection \<open>Exec \<open>\<leftrightarrow>\<close> locale bridges\<close>

lemma normalized_problem_rx_pddl_datalog:
  assumes "normalized_problem_rx N"
  shows "pddl_datalog (ast_classical_problem.relax_prob N)"
proof -
  interpret rx: normalized_problem_rx N by fact
  show ?thesis
    unfolding pddl_datalog_def
    by (simp add: normalized_problem_def' relaxed_problem.intro relaxed_problem_axioms_def
                  rx.relax_wf rx.relax_normed rx.relax_relaxes)
qed

lemma P_T_normalized_problem_rx_unconditional:
  assumes "ast_classical_problem.restrict_prob P" "ast_classical_problem.wf_classical_problem P"
  shows "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
proof -
  interpret p: ast_classical_problem P .
  have wf_N: "ast_classical_problem.wf_classical_problem p.P\<^sub>N" using assms p.normalization_wf by simp
  have norm_N: "ast_classical_problem.normalized_prob p.P\<^sub>N" using assms p.normalization_normalizes by simp
  have wf_T: "ast_classical_problem.wf_classical_problem p.P\<^sub>T"
    using wf_N unfolding p.P\<^sub>T_def by (rule ast_classical_problem.def_translate_prob_wf_compact)
  have norm_T: "ast_classical_problem.normalized_prob p.P\<^sub>T"
    using norm_N unfolding p.P\<^sub>T_def by (rule ast_classical_problem.def_translate_normed_compact)
  show ?thesis
    unfolding normalized_problem_rx_def normalized_problem_def'
    using wf_T norm_T by blast
qed

lemma cert_ops_of_exec_eq:
  assumes "normalized_problem_rx N"
  shows "cert_ops_of_exec N M = normalized_problem_rx.cert_ops_of N M"
  unfolding cert_ops_of_exec_def normalized_problem_rx.cert_ops_of_def[OF assms]
  by (rule refl)

lemma extra_eff_atoms_of_exec_eq:
  assumes "normalized_problem_rx N"
  shows "extra_eff_atoms_of_exec N M = normalized_problem_rx.extra_eff_atoms_of N M"
  unfolding extra_eff_atoms_of_exec_def normalized_problem_rx.extra_eff_atoms_of_def[OF assms]
            cert_ops_of_exec_eq[OF assms]
  by (rule refl)

lemma cert_facts_of_exec_eq:
  assumes "normalized_problem_rx N"
  shows "cert_facts_of_exec N M = normalized_problem_rx.cert_facts_of N M"
  unfolding cert_facts_of_exec_def normalized_problem_rx.cert_facts_of_def[OF assms]
            extra_eff_atoms_of_exec_eq[OF assms]
  by (rule refl)

lemma grounding_checks_exec_eq:
  assumes "normalized_problem_rx N"
  shows "grounding_checks_exec N M = normalized_problem_rx.grounding_checks N M"
  unfolding grounding_checks_exec_def normalized_problem_rx.grounding_checks_def[OF assms]
            cert_ops_of_exec_eq[OF assms] cert_facts_of_exec_eq[OF assms]
  by (rule refl)

lemma numeric_grounding_checks_exec_eq:
  assumes "normalized_problem_rx N"
  shows "numeric_grounding_checks_exec N M = normalized_problem_rx.numeric_grounding_checks N M"
  unfolding numeric_grounding_checks_exec_def normalized_problem_rx.numeric_grounding_checks_def[OF assms]
            cert_ops_of_exec_eq[OF assms] cert_facts_of_exec_eq[OF assms]
  by (rule refl)

text \<open>The three side conditions of the certified-grounding context, discharged from executable
  checks at \<^term>\<open>ast_classical_problem.P\<^sub>T P\<close>.\<close>

lemma numeric_free_problem_exec:
  assumes "ast_classical_problem.num_free_prob Rp"
  shows "numeric_free_problem Rp"
  using assms by unfold_locales

lemma grounding_checks_exec_P\<^sub>T:
  assumes "ast_classical_problem.restrict_prob P" "ast_classical_problem.wf_classical_problem P"
      and "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
  shows "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
  using assms(3)
  unfolding grounding_checks_exec_eq[OF P_T_normalized_problem_rx_unconditional[OF assms(1,2)]] .

text \<open>Under the (re-checked) kernel checks, the executable grounding agrees with the verified
  \<open>P\<^sub>G_cert\<close> of the pipeline.\<close>
lemma ground_by_cert_eq:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
      and pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
      and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
      and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
  shows "ground_by_cert P M = ast_classical_problem.P\<^sub>G_cert P M"
proof -
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding grounding_checks_exec_eq[OF rx] .
  show ?thesis
    unfolding ground_by_cert_def ast_classical_problem.P\<^sub>G_cert_def[OF pnf ne cert gc']
              cert_facts_of_exec_eq[OF rx] cert_ops_of_exec_eq[OF rx]
    by (rule refl)
qed

end
