theory Grounding_Pipeline_STRIPS_Executable
  imports Grounding_Pipeline_STRIPS Code_Setup
begin

section \<open>Executable end-to-end pipeline\<close>

text \<open>This theory exposes the verified grounding pipeline as runnable functions, driven by two
  \<^emph>\<open>untrusted, re-checked\<close> external oracles:
  \<^item> \<^verbatim>\<open>f :: dl_program \<Rightarrow> certificate\<close> --- a reachability oracle (Nemo). Given the datalog
    program of the relaxed problem, it returns a certificate; the kernel re-checks
    \<^const>\<open>pddl_datalog.admissible\<close> + \<^const>\<open>normalized_problem_rx.grounding_checks\<close>.
  \<^item> \<open>g\<close> --- an external SAT solver (Phase 2); its decoded plan is re-checked with
    \<^const>\<open>is_serial_solution_for_problem\<close>.
  Soundness therefore never depends on trusting either oracle (see \<open>WIP_executable_pipeline.md\<close>).\<close>

subsection \<open>The datalog program handed to the reachability oracle\<close>

text \<open>The serialization of a (relaxed, normalized) problem into the AFP \<open>Stratified_Datalog\<close>
  clause syntax --- \<^const>\<open>dl_rules\<close> --- and its bridge to the generic certificate checker
  (session \<open>Datalog_Certification\<close>) live in
  \<^theory>\<open>Reachability_Analysis.PDDL_Reachability_Certificate\<close>. Here we only package the program of
  the pipeline's relaxed normalized problem \<open>relax_prob P\<^sub>T\<close> --- the problem the certificate is
  about --- as the oracle's wire-format input (the constant list feeds the oracle's \<open>dom\<close>
  guards).\<close>

datatype dl_program = DLProgram
  (dl_clauses: "pddl_dl_clause list")   \<comment> \<open>rules ++ initial facts (facts: ground, empty body)\<close>
  (dl_consts: "object list")            \<comment> \<open>the object universe (the oracle's \<open>dom\<close> guards)\<close>

definition dl_program_of where
  [code]: "dl_program_of P \<equiv>
     (let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P) in
        DLProgram (dl_rules R) (ast_classical_problem.const_names R))"

subsection \<open>Executable mirrors of the grounding checks\<close>

text \<open>The \<^const>\<open>pddl_datalog\<close>-side mirrors of the certificate checks
  (\<^const>\<open>closure_check_exec\<close>, \<^const>\<open>ordered_check_exec\<close>, \<^const>\<open>local_valid_exec\<close>,
  \<^const>\<open>admissible_exec\<close>, \<^const>\<open>cert_ops_exec\<close>) live in
  \<^theory>\<open>Reachability_Analysis.PDDL_Reachability_Certificate\<close> next to their locale originals. The
  \<^const>\<open>normalized_problem_rx\<close>-side mirrors below take the \<^emph>\<open>normalized\<close> problem and relax it
  internally; as with the certificate checks, each body replays its locale original verbatim
  (the bodies do not use the locale assumptions), and the \<open>_eq\<close> bridges below record equality
  under the locale predicate for the soundness link.\<close>

definition cert_ops_of_exec where
  [code]: "cert_ops_of_exec P c \<equiv> cert_ops_exec (ast_classical_problem.relax_prob P) c"

definition extra_eff_atoms_of_exec where
  [code]: "extra_eff_atoms_of_exec P c \<equiv>
     remdups (concat (map (\<lambda>\<pi>.
        let eff = ground_action.effect (the (simple_action_instantiations.res_inst
                    (ast_classical_domain.resolve_classical_action_schema (domain P))
                    instantiate_classical_action_schema \<pi>))
        in adds eff @ dels eff) (cert_ops_of_exec P c)))"

definition cert_facts_of_exec where
  [code]: "cert_facts_of_exec P c \<equiv> remdups (cert_facts c @ extra_eff_atoms_of_exec P c)"

definition grounding_checks_exec where
  [code]: "grounding_checks_exec P c \<equiv>
     (\<forall>a \<in> set (cert_facts_of_exec P c).
        domain_signature.wf_fmla_atom (types (domain P)) (predicates (domain P))
          (problem_signature.objT (consts (domain P)) (objects P)) a)
   \<and> (\<forall>\<pi> \<in> set (cert_ops_of_exec P c). ast_classical_problem.wf_classical_plan_action P \<pi>)
   \<and> (\<forall>\<pi> \<in> set (cert_ops_of_exec P c).
        let eff = ground_action.effect (the (simple_action_instantiations.res_inst
                    (ast_classical_domain.resolve_classical_action_schema (domain P))
                    instantiate_classical_action_schema \<pi>))
        in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> (cert_facts_of_exec P c))
   \<and> (\<forall>\<pi> \<in> set (cert_ops_of_exec P c).
        covered (ground_action.precondition (the (simple_action_instantiations.res_inst
                   (ast_classical_domain.resolve_classical_action_schema (domain P))
                   instantiate_classical_action_schema \<pi>))) (cert_facts_of_exec P c))
   \<and> covered (goal P) (cert_facts_of_exec P c)
   \<and> (\<forall>f \<in> set (init P). is_predAtom f)
   \<and> (\<forall>\<pi> \<in> set (cert_ops_of_exec P c).
        numeric_effects (ground_action.effect (the (simple_action_instantiations.res_inst
          (ast_classical_domain.resolve_classical_action_schema (domain P))
          instantiate_classical_action_schema \<pi>))) = [])"

subsection \<open>Grounding a problem against a certificate\<close>

text \<open>Unconditional executable twin of \<^verbatim>\<open>P\<^sub>G_cert\<close>. The defining RHS of \<^verbatim>\<open>P\<^sub>G_cert\<close>
  (\<^verbatim>\<open>Grounding_Pipeline_Numeric\<close>) does not depend on the \<open>admissible_cert\<close>/\<open>grounding_cert\<close>
  assumptions of its context --- it is a plain expression in \<^term>\<open>P\<^sub>T\<close> and \<open>cert\<close> --- so we
  replay it at the top level as a code-generable function. Equality with \<^verbatim>\<open>P\<^sub>G_cert\<close>
  (under the assumptions) is recorded later for the soundness link.\<close>
definition ground_by_cert where
  [code]: "ground_by_cert P cert \<equiv>
     grounder.ground_prob (ast_classical_problem.P\<^sub>T P)
       (cert_facts_of_exec (ast_classical_problem.P\<^sub>T P) cert)
       (cert_ops_of_exec (ast_classical_problem.P\<^sub>T P) cert)"

text \<open>Run the grounding half end-to-end against the (untrusted) reachability oracle \<^term>\<open>f\<close>:
  normalize \<open>P\<close> to \<open>P\<^sub>T\<close>, ask \<^term>\<open>f\<close> for a certificate of the relaxed problem, \<^emph>\<open>re-check\<close> it
  (\<^const>\<open>pddl_datalog.admissible\<close> + \<^const>\<open>normalized_problem_rx.grounding_checks\<close>), and only then
  emit the grounded STRIPS problem. Returns \<^const>\<open>None\<close> if the input is ill-formed or the
  certificate fails the kernel checks --- so the oracle is never trusted.\<close>
definition ground_via_cert' where
  [code]: "ground_via_cert' f P \<equiv>
     (if \<not> ast_classical_problem.restrict_prob P \<or> \<not> ast_classical_problem.wf_classical_problem P
      then None
      else
        let cert = f (dl_program_of P) in
          if admissible_exec (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) cert
             \<and> grounding_checks_exec (ast_classical_problem.P\<^sub>T P) cert
          then Some (cert, ast_classical_problem.as_strips (ground_by_cert P cert))
          else None)"

text \<open>The plain grounding entry point keeps its old type: certificate discarded.\<close>
definition ground_via_cert where
  [code]: "ground_via_cert f P \<equiv> map_option snd (ground_via_cert' f P)"

subsection \<open>Executable plan reconstruction\<close>

text \<open>Code equations for the assumption-free plan-restoration chain: a STRIPS solution prefix
  back to grounded plan actions (\<^const>\<open>ast_classical_problem.restore_prefix\<close>), grounded plan
  actions back to normalized ones (\<^const>\<open>grounder.restore_ground_pa\<close>), and back up the
  normalization stages (\<^const>\<open>ast_classical_problem.reconstruct_plan_norm\<close>).\<close>

lemma drop_lit_code [code]: "drop_lit n s = String.implode (drop n (String.explode s))"
  by (metis drop_lit.rep_eq String.implode_explode_eq)

text \<open>\<^const>\<open>ast_classical_problem.strips_model\<close> quantifies over all (infinitely many) predicates;
  on the grounded problems it is applied to, \<open>wf_pred\<close> bounds the witnesses to the declared
  predicate list, which makes the existentials finite and hence code-generable.\<close>
lemma strips_model_code [code]:
  "ast_classical_problem.strips_model P M v =
     (if v \<in> set (ast_classical_problem.pos_vars P @ ast_classical_problem.neg_vars P)
      then Some (v = v\<^sub>T
               \<or> (\<exists>p \<in> pred ` set (predicates (domain P)).
                    ast_classical_domain.wf_pred (domain P) p \<and> v = vpos p
                    \<and> Atom (predAtm p []) \<in> fst M)
               \<or> (\<exists>p \<in> pred ` set (predicates (domain P)).
                    ast_classical_domain.wf_pred (domain P) p \<and> v = vneg p
                    \<and> Atom (predAtm p []) \<notin> fst M))
      else None)"
  unfolding ast_classical_problem.strips_model_def ast_classical_domain.wf_pred_def
  by (force simp: image_iff)

declare ast_classical_problem.I_def[code]
declare ast_classical_problem.execute_plan_action_def[code]
declare ast_classical_domain.wf_pred_def[code]
declare ast_classical_problem.restore_pddl_pa_def[code]
declare ast_classical_problem.restore_prefix.simps[code]
declare grounder.op_names_def[code]
declare grounder.op_map_def[code]
declare grounder.restore_ground_pa.simps[code]
declare ast_classical_problem.reconstruct_plan_norm_def[code]

text \<open>Unconditional executable twin of the cert-context \<open>reconstruct_pipeline_plan_cert\<close>
  (\<open>Grounding_Pipeline_STRIPS\<close>): restore the applicable prefix of the STRIPS solution against
  the grounded problem, decode operator names back to grounded plan actions, and run the
  normalization restorations. Equality with the locale composition (under the kernel checks)
  is recorded for the soundness link of \<open>plan_by_cert\<close>.\<close>
definition reconstruct_plan_by_cert where
  [code]: "reconstruct_plan_by_cert P cert ops \<equiv>
     ast_classical_problem.reconstruct_plan_norm P
       (restore_plan_def_translate
          (grounder.restore_ground_plan (cert_ops_of_exec (ast_classical_problem.P\<^sub>T P) cert)
             (ast_classical_problem.restore_prefix (ground_by_cert P cert)
                (ast_classical_problem.I (ground_by_cert P cert)) ops)))"

subsection \<open>Exec \<open>\<leftrightarrow>\<close> locale bridges\<close>

text \<open>\<^locale>\<open>normalized_problem_rx\<close> sees the certificate kernel at its relaxation (the \<open>px\<close>
  sublocale); replayed here as a top-level fact.\<close>
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

lemma cert_ops_of_exec_eq:
  assumes "normalized_problem_rx N"
  shows "cert_ops_of_exec N c = normalized_problem_rx.cert_ops_of N c"
  unfolding cert_ops_of_exec_def normalized_problem_rx.cert_ops_of_def[OF assms]
            cert_ops_exec_eq[OF normalized_problem_rx_pddl_datalog[OF assms]]
  by (rule refl)

lemma extra_eff_atoms_of_exec_eq:
  assumes "normalized_problem_rx N"
  shows "extra_eff_atoms_of_exec N c = normalized_problem_rx.extra_eff_atoms_of N c"
  unfolding extra_eff_atoms_of_exec_def normalized_problem_rx.extra_eff_atoms_of_def[OF assms]
            cert_ops_of_exec_eq[OF assms]
  by (rule refl)

lemma cert_facts_of_exec_eq:
  assumes "normalized_problem_rx N"
  shows "cert_facts_of_exec N c = normalized_problem_rx.cert_facts_of N c"
  unfolding cert_facts_of_exec_def normalized_problem_rx.cert_facts_of_def[OF assms]
            extra_eff_atoms_of_exec_eq[OF assms]
  by (rule refl)

lemma grounding_checks_exec_eq:
  assumes "normalized_problem_rx N"
  shows "grounding_checks_exec N c = normalized_problem_rx.grounding_checks N c"
  unfolding grounding_checks_exec_def normalized_problem_rx.grounding_checks_def[OF assms]
            cert_ops_of_exec_eq[OF assms] cert_facts_of_exec_eq[OF assms]
  by (simp add: ast_classical_problem.relax_prob_def ast_classical_domain.relax_dom_def Let_def)

text \<open>Re-prove \<open>P_T_normalized_problem_rx\<close> (\<open>Grounding_Pipeline_Numeric\<close>) outside the
  cert-assuming context: its proof never touches the certificate, but its exported form carries
  the context's \<open>admissible_cert\<close>/\<open>grounding_cert\<close> hypotheses, which is circular here (we need
  the locale predicate \<^emph>\<open>before\<close> we can translate the exec checks into those hypotheses).\<close>
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

text \<open>Under the (re-checked) kernel checks, the executable grounding agrees with the verified
  \<open>P\<^sub>G_cert\<close> of the pipeline.\<close>
lemma ground_by_cert_eq:
  assumes "ast_classical_problem.restrict_prob P" "ast_classical_problem.wf_classical_problem P"
      and adm: "admissible_exec (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) cert"
      and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) cert"
  shows "ground_by_cert P cert = ast_classical_problem.P\<^sub>G_cert P cert"
proof -
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF assms(1,2)])
  have adm': "pddl_datalog.admissible (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) cert"
    by (rule admissible_exec_sound[OF normalized_problem_rx_pddl_datalog[OF rx] adm])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) cert"
    using gc unfolding grounding_checks_exec_eq[OF rx] .
  show ?thesis
    unfolding ground_by_cert_def ast_classical_problem.P\<^sub>G_cert_def[OF adm' gc']
              cert_facts_of_exec_eq[OF rx] cert_ops_of_exec_eq[OF rx]
    by (rule refl)
qed

text \<open>Convenience forms of the two oracle-check translations at \<^term>\<open>ast_classical_problem.P\<^sub>T P\<close>,
  as consumed by the cert-context facts of \<open>Grounding_Pipeline_Numeric\<close>/\<open>_STRIPS\<close>.\<close>

lemma admissible_exec_P\<^sub>T:
  assumes "ast_classical_problem.restrict_prob P" "ast_classical_problem.wf_classical_problem P"
      and "admissible_exec (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) cert"
  shows "pddl_datalog.admissible (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) cert"
  by (rule admissible_exec_sound[OF normalized_problem_rx_pddl_datalog[OF
        P_T_normalized_problem_rx_unconditional[OF assms(1,2)]] assms(3)])

lemma grounding_checks_exec_P\<^sub>T:
  assumes "ast_classical_problem.restrict_prob P" "ast_classical_problem.wf_classical_problem P"
      and "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) cert"
  shows "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) cert"
  using assms(3)
  unfolding grounding_checks_exec_eq[OF P_T_normalized_problem_rx_unconditional[OF assms(1,2)]] .

text \<open>The executable grounding, converted to STRIPS, is exactly the pipeline's \<open>P\<^sub>S_cert\<close>.\<close>
lemma ground_by_cert_strips_eq:
  assumes "ast_classical_problem.restrict_prob P" "ast_classical_problem.wf_classical_problem P"
      and adm: "admissible_exec (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) cert"
      and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) cert"
  shows "ast_classical_problem.as_strips (ground_by_cert P cert)
           = ast_classical_problem.P\<^sub>S_cert P cert"
  unfolding ground_by_cert_eq[OF assms]
            ast_classical_problem.P\<^sub>S_cert_def[OF admissible_exec_P\<^sub>T[OF assms(1,2) adm]
                                                 grounding_checks_exec_P\<^sub>T[OF assms(1,2) gc]]
  by (rule refl)

text \<open>The executable reconstruction agrees with the pipeline's verified
  \<open>reconstruct_pipeline_plan_cert\<close>, whose \<open>strips_plan_reconstruct_cert\<close> theorem then carries a
  STRIPS serial solution all the way back to a valid plan of the original problem.\<close>
lemma reconstruct_plan_by_cert_eq:
  assumes "ast_classical_problem.restrict_prob P" "ast_classical_problem.wf_classical_problem P"
      and adm: "admissible_exec (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) cert"
      and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) cert"
  shows "reconstruct_plan_by_cert P cert ops
           = ast_classical_problem.reconstruct_pipeline_plan_cert P cert ops"
proof -
  note rx = P_T_normalized_problem_rx_unconditional[OF assms(1,2)]
  note adm' = admissible_exec_P\<^sub>T[OF assms(1,2) adm]
  note gc' = grounding_checks_exec_P\<^sub>T[OF assms(1,2) gc]
  show ?thesis
    unfolding reconstruct_plan_by_cert_def
              ast_classical_problem.reconstruct_pipeline_plan_cert_def[OF adm' gc']
              ast_classical_problem.reconstruct_plan_ground_cert_def[OF adm' gc']
              ground_by_cert_eq[OF assms] cert_ops_of_exec_eq[OF rx]
    by (rule refl)
qed

end
