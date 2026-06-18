theory Grounding_Pipeline_STRIPS_Executable
  imports Grounding_Pipeline_STRIPS Code_Setup Datalog_Certification.Datalog_Certificate_Code
begin

section \<open>Executable end-to-end pipeline\<close>

text \<open>This theory exposes the verified grounding pipeline as runnable functions, driven by two
  \<^emph>\<open>untrusted, re-checked\<close> external oracles:
  \<^item> \<open>f :: dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate\<close> --- a reachability oracle
    (Nemo). Given the datalog program of the relaxed problem, it returns a candidate model \<open>M\<close>
    together with a generic datalog certificate \<open>dc\<close>; the kernel re-checks
    \<^const>\<open>dl_certified_model_exec\<close> + \<^const>\<open>normalized_problem_rx.grounding_checks\<close>.
  \<^item> \<open>g\<close> --- an external SAT solver (Phase 2); its decoded plan is re-checked with
    \<^const>\<open>is_serial_solution_for_problem\<close>.
  Soundness therefore never depends on trusting either oracle.\<close>

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
  [code]: "cert_ops_of_exec N M \<equiv> concat (map (\<lambda>c.
      map (SimplePlanAction (cl_name c))
        (all_combos (\<lambda>args.
            (\<forall>a \<in> set (cl_pred_pre c).
                map_atom_fmla (ac_tsubst (cl_params c) args) a \<in> set (map fact_to_facty M))
            \<and> satisfies_conds (cl_params c) (cl_cond_pre c) args)
          (replicate (length (cl_params c))
             (ast_classical_problem.const_names (ast_classical_problem.relax_prob N)))))
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

subsection \<open>Grounding a problem against a certified fact list\<close>

text \<open>Unconditional executable twin of \<^verbatim>\<open>P\<^sub>G_cert\<close>, replayed at the top level as a code-generable
  function keyed on the certified facts \<open>M\<close>.\<close>
definition ground_by_cert where
  [code]: "ground_by_cert P M \<equiv>
     grounder.ground_prob (ast_classical_problem.P\<^sub>T P)
       (cert_facts_of_exec (ast_classical_problem.P\<^sub>T P) M)
       (remdups (cert_ops_of_exec (ast_classical_problem.P\<^sub>T P) M))"

text \<open>Run the grounding half end-to-end against the (untrusted) reachability oracle \<^term>\<open>f\<close>:
  normalize \<open>P\<close> to \<open>P\<^sub>T\<close>, ask \<^term>\<open>f\<close> for a model \<open>M\<close> and certificate \<open>dc\<close> of the relaxed problem,
  \<^emph>\<open>re-check\<close> them (the universe is nonempty, the relaxation is numeric-free,
  \<^const>\<open>dl_certified_model_exec\<close> accepts \<open>(M, dc)\<close>, and the \<^const>\<open>grounding_checks_exec\<close> hold), and
  only then emit the grounded STRIPS problem. Returns \<^const>\<open>None\<close> if the input is ill-formed or any
  check fails --- so the oracle is never trusted.\<close>
definition ground_via_cert' where
  [code]: "ground_via_cert' f P \<equiv>
     (if \<not> ast_classical_problem.restrict_prob P \<or> \<not> ast_classical_problem.wf_classical_problem P
      then None
      else
        let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
            Mdc = f (dl_program_of P)
        in (case Mdc of (M, dc) \<Rightarrow>
          if ast_classical_problem.const_names R \<noteq> []
             \<and> ast_classical_problem.num_free_prob R
             \<and> dl_certified_model_exec (dl_rules R) (ast_classical_problem.const_names R) M dc
             \<and> grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
          then Some ((M, dc), ast_classical_problem.as_strips (ground_by_cert P M))
          else None))"

text \<open>The plain grounding entry point: certificate pair discarded.\<close>
definition ground_via_cert where
  [code]: "ground_via_cert f P \<equiv> map_option snd (ground_via_cert' f P)"

subsection \<open>Executable plan reconstruction\<close>

lemma drop_lit_code [code]: "drop_lit n s = String.implode (drop n (String.explode s))"
  by (metis drop_lit.rep_eq String.implode_explode_eq)

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

text \<open>Unconditional executable twin of the cert-context \<open>reconstruct_pipeline_plan_cert\<close>.\<close>
definition reconstruct_plan_by_cert where
  [code]: "reconstruct_plan_by_cert P M ops \<equiv>
     ast_classical_problem.reconstruct_plan_norm P
       (restore_plan_def_translate
          (grounder.restore_ground_plan (remdups (cert_ops_of_exec (ast_classical_problem.P\<^sub>T P) M))
             (ast_classical_problem.restore_prefix (ground_by_cert P M)
                (ast_classical_problem.I (ground_by_cert P M)) ops)))"

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

text \<open>The three side conditions of the certified-grounding context, discharged from executable
  checks at \<^term>\<open>ast_classical_problem.P\<^sub>T P\<close>.\<close>

lemma numeric_free_problem_exec:
  assumes "ast_classical_problem.num_free_prob R"
  shows "numeric_free_problem R"
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

lemma ground_by_cert_strips_eq:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
      and pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
      and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
      and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
  shows "ast_classical_problem.as_strips (ground_by_cert P M) = ast_classical_problem.P\<^sub>S_cert P M"
proof -
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding grounding_checks_exec_eq[OF rx] .
  show ?thesis
    unfolding ground_by_cert_eq[OF rp wf pnf ne cert gc]
              ast_classical_problem.P\<^sub>S_cert_def[OF pnf ne cert gc']
    by (rule refl)
qed

lemma reconstruct_plan_by_cert_eq:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
      and pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
      and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
      and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
  shows "reconstruct_plan_by_cert P M ops = ast_classical_problem.reconstruct_pipeline_plan_cert P M ops"
proof -
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding grounding_checks_exec_eq[OF rx] .
  show ?thesis
    unfolding reconstruct_plan_by_cert_def
              ast_classical_problem.reconstruct_pipeline_plan_cert_def[OF pnf ne cert gc']
              ast_classical_problem.reconstruct_plan_ground_cert_def[OF pnf ne cert gc']
              ground_by_cert_eq[OF rp wf pnf ne cert gc] cert_ops_of_exec_eq[OF rx]
    by (rule refl)
qed

end
