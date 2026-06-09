theory Grounding_Pipeline_Executable
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

text \<open>A serializable bundle of exactly the data \<^const>\<open>pddl_datalog.closure_check\<close> /
  \<^const>\<open>pddl_datalog.admissible\<close> quantify over: the action clauses, the initial facts, and the
  object names. The oracle (in SML) renders this as a Nemo program, runs Nemo, and parses the
  certificate back.\<close>

datatype dl_program = DLProgram
  (dl_clauses: "action_clause list")
  (dl_init: "object atom formula list")
  (dl_consts: "object list")

text \<open>Extract the datalog program of the \<^emph>\<open>relaxed, normalized\<close> problem \<open>relax_prob P\<^sub>T\<close> --- the
  problem the certificate is about.\<close>
definition dl_program_of where
  [code]: "dl_program_of P \<equiv>
     (let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P) in
        DLProgram (ast_classical_problem.a_clauses R)
                  (ast_classical_problem.init' R)
                  (ast_classical_problem.const_names R))"

subsection \<open>Executable mirrors of the certificate / grounding checks\<close>

text \<open>The certificate / grounding checks live in locales \<^emph>\<open>with\<close> assumptions (\<open>pddl_datalog\<close>,
  \<open>normalized_problem_rx\<close>), so their \<open>_def\<close> equations are guarded by the locale predicate and are
  not directly code-registrable. We replay each body unconditionally at the top level (the bodies do
  not use the assumptions). Equality with the locale versions (under the locale predicate) is for the
  soundness link. The \<^const>\<open>pddl_datalog\<close>-side mirrors take the \<^emph>\<open>relaxed\<close> problem; the
  \<^const>\<open>normalized_problem_rx\<close>-side mirrors take the normalized problem and relax it internally.\<close>

definition closure_check_exec where
  [code]: "closure_check_exec R c \<equiv>
     (let fs = cert_facts c in
        (\<forall>f \<in> set fs. is_predAtom f) \<and>
        (\<forall>f \<in> set (ast_classical_problem.init' R). f \<in> set fs) \<and>
        (\<forall>cl \<in> set (ast_classical_problem.a_clauses R).
           \<forall>args \<in> set (all_combos \<checkmark> (replicate (length (cl_params cl)) (ast_classical_problem.const_names R))).
              (set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl)) \<subseteq> set fs
               \<and> satisfies_conds (cl_params cl) (cl_cond_pre cl) args)
              \<longrightarrow> set (consequence_of cl args) \<subseteq> set fs))"

definition ordered_check_exec where
  [code]: "ordered_check_exec c \<equiv> (\<forall>i < length (nodes c). \<forall>j \<in> set (cn_preds (nodes c ! i)). j < i)"

text \<open>\<^const>\<open>pddl_datalog.local_valid\<close> has an \<^emph>\<open>unbounded\<close> \<open>\<exists>args\<close>, not code-generable. We bound it
  to the same finite object-name combinations the closure check enumerates. This is a \<^emph>\<open>sound
  under-approximation\<close> --- \<open>local_valid_exec R c i \<longrightarrow> pddl_datalog.local_valid R c i\<close> (bounded
  \<open>\<exists>\<close> implies \<open>\<exists>\<close>) --- so an accepted certificate is genuinely admissible. (Nemo's witness args are
  always object names, so legitimate certificates still pass.)\<close>
definition local_valid_exec where
  [code]: "local_valid_exec R c i \<equiv>
     (let n = nodes c ! i in
        (cn_preds n = [] \<and> cn_fact n \<in> set (ast_classical_problem.init' R)) \<or>
        (\<exists>cl \<in> set (ast_classical_problem.pred_clauses R).
           \<exists>args \<in> set (all_combos \<checkmark> (replicate (length (cl_params cl)) (ast_classical_problem.const_names R))).
              satisfies_conds (cl_params cl) (cl_cond_pre cl) args \<and>
              cn_fact n \<in> set (consequence_of cl args) \<and>
              set (cn_body c i)
                = set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl))))"

definition admissible_exec where
  [code]: "admissible_exec R c \<equiv>
     closure_check_exec R c \<and> ordered_check_exec c \<and> (\<forall>i < length (nodes c). local_valid_exec R c i)"

definition cert_ops_exec where
  [code]: "cert_ops_exec R c =
     remdups (concat (map (\<lambda>cl.
        map (SimplePlanAction (cl_name cl))
            (filter (\<lambda>args.
                set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl))
                  \<subseteq> set (cert_facts c)
                \<and> satisfies_conds (cl_params cl) (cl_cond_pre cl) args)
              (all_combos \<checkmark> (replicate (length (cl_params cl)) (ast_classical_problem.const_names R)))))
        (ast_classical_problem.a_clauses R)))"

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
definition ground_via_cert where
  [code]: "ground_via_cert f P \<equiv>
     (if \<not> ast_classical_problem.restrict_prob P \<or> \<not> ast_classical_problem.wf_classical_problem P
      then None
      else
        let cert = f (dl_program_of P) in
          if admissible_exec (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) cert
             \<and> grounding_checks_exec (ast_classical_problem.P\<^sub>T P) cert
          then Some (ast_classical_problem.as_strips (ground_by_cert P cert))
          else None)"

end
