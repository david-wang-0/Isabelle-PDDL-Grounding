theory Grounding_Pipeline_STRIPS_Executable
  imports Grounding_Pipeline_Common_Executable Grounding_Pipeline_STRIPS
    Datalog_Graph.Datalog_Cycle_DFS_Global
begin

text \<open>\<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS_Global\<close> (imported for the global-sweep certificate
  check \<^const>\<open>dl_certified_model_gdfs\<close>) re-exports the graph library's red-black-tree constructors
  \<open>R\<close> / \<open>B\<close>, which \<^theory>\<open>Classical_Grounding.Grounding_Pipeline_Common_Executable\<close> had already
  hidden --- and which shadow the pipeline's habitual variable name \<open>R\<close> for the relaxed problem.
  Re-hide them at the surface so \<open>R\<close> keeps reading as a variable here and downstream.\<close>
hide_const (open) R B

section \<open>Executable STRIPS grounding entry points\<close>

text \<open>The STRIPS-producing half of the executable pipeline: the shared re-checked infrastructure
  (\<^theory>\<open>Classical_Grounding.Grounding_Pipeline_Common_Executable\<close>) followed by the propositional STRIPS
  encoding \<^const>\<open>ast_classical_problem.as_strips\<close>. Two entry points --- \<open>ground_via_cert\<close> (the
  reachability certificate gated through the ordered linear scan \<^const>\<open>dl_certified_model_exec\<close>) and
  \<open>ground_via_cert_dfs\<close> (gated through the verified directed-cycle DFS
  \<^const>\<open>dl_certified_model_dfs\<close>) --- plus STRIPS plan reconstruction and the error-reporting
  propositional grounder. A second external oracle \<open>g\<close> (a SAT solver, Phase 2) is re-checked with
  \<^const>\<open>is_serial_solution_for_problem\<close> downstream; soundness never trusts either oracle.\<close>

subsection \<open>STRIPS-specific code equations for plan reconstruction\<close>

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

subsection \<open>Grounding a problem to STRIPS against a certified fact list\<close>

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

subsection \<open>DFS-founded grounding entry points\<close>

text \<open>Twins of \<^const>\<open>ground_via_cert'\<close> / \<^const>\<open>ground_via_cert\<close> that gate the untrusted certificate
  through \<^const>\<open>dl_certified_model_dfs\<close> (foundedness discharged by the verified directed-cycle DFS
  \<^const>\<open>dl_acyclic_dfs\<close>) instead of \<^const>\<open>dl_certified_model_exec\<close> (the ordered linear scan). Both
  re-checks bridge to the same abstract \<^const>\<open>dl_certified_model\<close> (\<open>dl_certified_model_dfs_imp\<close> vs
  \<open>dl_certified_model_exec_imp\<close>), so grounding is identical.\<close>

definition ground_via_cert'_dfs where
  [code]: "ground_via_cert'_dfs f P \<equiv>
     (if \<not> ast_classical_problem.restrict_prob P \<or> \<not> ast_classical_problem.wf_classical_problem P
      then None
      else
        let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
            Mdc = f (dl_program_of P)
        in (case Mdc of (M, dc) \<Rightarrow>
          if ast_classical_problem.const_names R \<noteq> []
             \<and> ast_classical_problem.num_free_prob R
             \<and> dl_certified_model_dfs (dl_rules R) (ast_classical_problem.const_names R) M dc
             \<and> grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
          then Some ((M, dc), ast_classical_problem.as_strips (ground_by_cert P M))
          else None))"

definition ground_via_cert_dfs where
  [code]: "ground_via_cert_dfs f P \<equiv> map_option snd (ground_via_cert'_dfs f P)"

subsection \<open>STRIPS plan reconstruction\<close>

text \<open>Unconditional executable twin of the cert-context \<open>reconstruct_pipeline_plan_cert\<close>. A decoded
  STRIPS serial solution is undone step by step: \<^const>\<open>ast_classical_problem.restore_prefix\<close> (the
  applicable prefix of the STRIPS plan) \<open>\<rightarrow>\<close> \<^const>\<open>varfree.restore_ground_plan\<close> (undo grounding)
  \<open>\<rightarrow>\<close> def-translation \<open>\<rightarrow>\<close> normalization.\<close>
definition reconstruct_plan_by_cert where
  [code]: "reconstruct_plan_by_cert P M ops \<equiv>
     ast_classical_problem.reconstruct_plan_norm P
       (restore_plan_def_translate
          (varfree.restore_ground_plan (canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M))
             (ast_classical_problem.restore_prefix (ground_by_cert P M)
                (ast_classical_problem.I (ground_by_cert P M)) ops)))"

subsection \<open>STRIPS exec \<open>\<leftrightarrow>\<close> locale bridges\<close>

text \<open>Under the (re-checked) kernel checks, the executable grounding agrees with the verified
  \<open>P\<^sub>G_cert\<close> of the pipeline. Stated here rather than with \<^const>\<open>ground_by_cert\<close> itself
  (\<^verbatim>\<open>Grounding_Pipeline_Common_Executable\<close>): \<open>ground_by_cert\<close> is branch-neutral --- the numeric
  branch bridges the same function to its folded product --- whereas \<open>P\<^sub>G_cert\<close> belongs to the
  propositional branch, so only this theory may mention it.\<close>
lemma ground_by_cert_eq:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
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
    unfolding ground_by_cert_def ast_classical_problem.P\<^sub>G_cert_def[OF ne cert gc']
              cert_facts_of_exec_eq[OF rx] cert_ops_of_exec_fast_canon_eq[OF rx]
    by (rule refl)
qed

lemma ground_by_cert_strips_eq:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
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
    unfolding ground_by_cert_eq[OF rp wf ne cert gc]
              ast_classical_problem.P\<^sub>S_cert_def[OF ne cert gc']
    by (rule refl)
qed

lemma reconstruct_plan_by_cert_eq:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
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
              ast_classical_problem.reconstruct_pipeline_plan_cert_def[OF ne cert gc']
              ast_classical_problem.reconstruct_plan_ground_cert_def[OF ne cert gc']
              ground_by_cert_eq[OF rp wf ne cert gc] cert_ops_of_exec_fast_canon_eq[OF rx]
    by (rule refl)
qed

section \<open>Error-reporting propositional grounding (mirror of the numeric error-monad path)\<close>

text \<open>The propositional twin of \<open>instantiate_all_actions_dfs_e\<close>: same error monad + \<open>return_iff\<close>
  discipline, but grounding to the propositional \<^emph>\<open>PDDL\<close> problem \<^const>\<open>ground_by_cert\<close> (= \<open>P\<^sub>G_cert\<close>,
  numerics compiled away) rather than the fluent-retaining one. It gates on the \<^emph>\<open>full\<close>
  \<^const>\<open>grounding_checks_exec\<close> (which the propositional grounder needs) and reuses the abstract
  \<open>ground_cert_plan_valid_iff\<close> / \<open>ground_cert_plan_reconstruct\<close> for plan preservation + restoration.\<close>

definition ground_via_cert_prop_dfs_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + ast_classical_problem" where
  [code]: "ground_via_cert_prop_dfs_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (dl_certified_model_dfs (dl_rules R) (ast_classical_problem.const_names R) M dc)
           (STR ''reachability certificate rejected by the verified DFS checker'');
     check (grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M)
           (STR ''grounding well-formedness checks failed'');
     Error_Monad.return (ground_by_cert P M)
   }"

lemma ground_via_cert_prop_dfs_e_return_iff[return_iff]:
  "ground_via_cert_prop_dfs_e f P = Inr Pg \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_dfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> Pg = ground_by_cert P M))"
  unfolding ground_via_cert_prop_dfs_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

text \<open>Unpack a successful propositional grounding into the abstract certificate conditions and the
  identity \<open>Pg = P\<^sub>G_cert P M\<close> (converting \<open>num_free_prob\<close>/\<open>dl_certified_model_dfs\<close> to their abstract
  forms and applying \<open>ground_by_cert_eq\<close>).\<close>
lemma ground_via_cert_prop_dfs_e_InrE:
  assumes "ground_via_cert_prop_dfs_e f P = Inr Pg"
  obtains M dc where
    "f (dl_program_of P) = (M, dc)"
    "ast_classical_problem.restrict_prob P"
    "ast_classical_problem.wf_classical_problem P"
    "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    "dl_certified_model
       (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
       (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    "Pg = ast_classical_problem.P\<^sub>G_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_via_cert_prop_dfs_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_dfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Pg: "Pg = ground_by_cert P M"
    by (auto split: prod.splits)
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    by (rule numeric_free_problem_exec[OF normalized_problem_rx.relax_num_free[OF rx]])
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_dfs_imp[OF certE])
  have Pg_cert: "Pg = ast_classical_problem.P\<^sub>G_cert P M"
    using Pg ground_by_cert_eq[OF rp wf ne cert gc] by simp
  show thesis by (rule that[OF fMdc rp wf pnf ne cert gc Pg_cert])
qed

theorem ground_via_cert_prop_dfs_e_sound:
  assumes "ground_via_cert_prop_dfs_e f P = Inr Pg"
  shows "\<exists>M. Pg = ast_classical_problem.P\<^sub>G_cert P M"
  using assms by (elim ground_via_cert_prop_dfs_e_InrE) blast

theorem ground_via_cert_prop_dfs_e_plan_valid_iff:
  assumes "ground_via_cert_prop_dfs_e f P = Inr Pg"
  shows "(\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)
         \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 Pg \<pi>s')"
  using assms
proof (elim ground_via_cert_prop_dfs_e_InrE)
  fix M dc
  assume rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Pg_cert: "Pg = ast_classical_problem.P\<^sub>G_cert P M"
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding grounding_checks_exec_eq[OF rx] .
  show "(\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)
        \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 Pg \<pi>s')"
    unfolding Pg_cert
    by (rule ast_classical_problem.ground_cert_plan_valid_iff[OF ne cert gc' rp wf])
qed

text \<open>Plan restoration for the propositional error-monad grounding, reusing
  \<^const>\<open>reconstruct_plan_by_cert_numeric\<close> (its body \<^emph>\<open>is\<close> the shared restore chain, no \<open>restore_prefix\<close>,
  so it also serves the propositional grounded PDDL).\<close>
lemma reconstruct_plan_by_cert_numeric_eq_prop:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
      and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
      and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
  shows "reconstruct_plan_by_cert_numeric P M \<pi>s = ast_classical_problem.reconstruct_plan_ground_cert P M \<pi>s"
proof -
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding grounding_checks_exec_eq[OF rx] .
  show ?thesis
    unfolding reconstruct_plan_by_cert_numeric_def
              ast_classical_problem.reconstruct_plan_ground_cert_def[OF ne cert gc']
              cert_ops_of_exec_fast_canon_eq[OF rx]
    by (rule refl)
qed

theorem ground_via_cert_prop_dfs_e_plan_restore:
  assumes ie: "ground_via_cert_prop_dfs_e f P = Inr Pg"
      and vp: "ast_classical_problem.valid_classical_plan2 Pg \<pi>s"
  shows "ast_classical_problem.valid_classical_plan2 P
           (reconstruct_plan_by_cert_numeric P (fst (f (dl_program_of P))) \<pi>s)"
  using ie
proof (elim ground_via_cert_prop_dfs_e_InrE)
  fix M dc
  assume fMdc: "f (dl_program_of P) = (M, dc)"
    and rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Pg_cert: "Pg = ast_classical_problem.P\<^sub>G_cert P M"
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding grounding_checks_exec_eq[OF rx] .
  have "ast_classical_problem.valid_classical_plan2 P
          (ast_classical_problem.reconstruct_plan_ground_cert P M \<pi>s)"
    using vp[unfolded Pg_cert]
          ast_classical_problem.ground_cert_plan_reconstruct[OF ne cert gc' rp wf] by blast
  thus "ast_classical_problem.valid_classical_plan2 P
          (reconstruct_plan_by_cert_numeric P (fst (f (dl_program_of P))) \<pi>s)"
    unfolding fMdc fst_conv reconstruct_plan_by_cert_numeric_eq_prop[OF rp wf ne cert gc] .
qed

section \<open>Numeric-free STRIPS grounding from the folded numeric product\<close>

text \<open>The executable half of the numeric-free (STRIPS) rebase: the STRIPS problem is produced from
  the \<^emph>\<open>folded numeric\<close> product \<^const>\<open>ast_classical_problem.numeric_P\<^sub>G_cert\<close> rather than from a
  separate propositional grounding run. No new computation is involved --- \<^const>\<open>ground_by_cert\<close> is
  the same function both gates call --- only a different, decidable entry gate: the numeric fold
  re-check \<^const>\<open>numeric_fold_checks_exec\<close> together with numeric-freeness of \<open>P\<^sub>T\<close> and a purely
  propositional initial state. Through the abstract gate bridge
  (\<open>grounding_checks_P\<^sub>T_of_num_free\<close>) that triple re-derives the propositional re-check, and through
  the product identity (\<open>numeric_P\<^sub>S_cert_eq_P\<^sub>S_cert\<close>) the whole STRIPS block transfers.

  The gates are genuinely \<^emph>\<open>different\<close> predicates (neither implies the other in general), so these
  entry points are added \<^bold>\<open>alongside\<close> \<^const>\<open>ground_via_cert_dfs\<close> / \<^const>\<open>ground_via_cert_prop_dfs_e\<close>,
  never in place of them; the shipped CLI path is untouched. Nothing here carries a \<open>[code]\<close>
  attribute yet and nothing is added to the export list, so the generated SML is unchanged.\<close>

subsection \<open>The numeric-free grounding gate\<close>

text \<open>Executable twin of the abstract numeric-free gate triple: the numeric fold re-check plus
  numeric-freeness of the normalized problem plus a purely propositional initial state. The
  \<open>num_free_prob\<close> conjunct is already executable (\<open>num_free_code\<close>, registered in
  \<^theory>\<open>Classical_Grounding.Grounding_Pipeline_Common_Executable\<close>), and \<open>is_predAtom\<close> is the very
  conjunct \<^const>\<open>grounding_checks_exec\<close> already carries.\<close>
definition strips_fold_checks_exec where
  "strips_fold_checks_exec N M \<equiv>
     numeric_fold_checks_exec N M
   \<and> ast_classical_problem.num_free_prob N
   \<and> (\<forall>f \<in> set (init N). is_predAtom f)"

lemma strips_fold_checks_exec_eq:
  assumes rx: "normalized_problem_rx N"
  shows "strips_fold_checks_exec N M =
    (normalized_problem_rx.numeric_fold_checks N M
     \<and> ast_classical_problem.num_free_prob N
     \<and> (\<forall>f \<in> set (init N). is_predAtom f))"
  unfolding strips_fold_checks_exec_def numeric_fold_checks_exec_eq[OF rx]
  by (rule refl)

text \<open>Destruction rules for the gate: the three abstract conjuncts the numeric-free pipeline
  theorems consume, in the order their \<open>[OF]\<close> lists expect.\<close>
lemma strips_fold_checks_exec_D:
  assumes rx: "normalized_problem_rx N"
      and gc: "strips_fold_checks_exec N M"
  shows "normalized_problem_rx.numeric_fold_checks N M"
    and "ast_classical_problem.num_free_prob N"
    and "\<forall>f \<in> set (init N). is_predAtom f"
  using gc unfolding strips_fold_checks_exec_eq[OF rx] by simp_all

text \<open>\<^bold>\<open>The executable gate bridge\<close>: the numeric-free gate subsumes the propositional
  \<^const>\<open>grounding_checks_exec\<close>, so everything the numeric-free STRIPS entry points accept the
  propositional ones accept too. Executable twin of \<open>grounding_checks_of_num_free\<close>.\<close>
lemma strips_fold_checks_exec_imp_grounding_checks_exec:
  assumes rp: "ast_classical_problem.restrict_prob P"
      and wf: "ast_classical_problem.wf_classical_problem P"
      and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
      and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
  shows "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
proof -
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  show ?thesis
    unfolding grounding_checks_exec_eq[OF rx]
    by (rule ast_classical_problem.grounding_checks_P\<^sub>T_of_num_free[OF ne cert
          strips_fold_checks_exec_D(1)[OF rx gc] strips_fold_checks_exec_D(2)[OF rx gc]
          strips_fold_checks_exec_D(3)[OF rx gc] rp wf])
qed

subsection \<open>Shared numeric-free STRIPS bridges\<close>

text \<open>The four obligations every numeric-free STRIPS entry point discharges, stated once against
  the re-checked kernel conditions and reused verbatim by the DFS / ordered-scan / global-sweep
  twins below. Each is the corresponding abstract theorem of
  \<^theory>\<open>Classical_Grounding.Grounding_Pipeline_STRIPS\<close> with the executable gate unfolded into the
  abstract triple.\<close>

context
  fixes P :: ast_classical_problem
    and M :: "fact list"
    and dc :: "(predicate, object) dl_certificate"
  assumes rp: "ast_classical_problem.restrict_prob P"
      and wf: "ast_classical_problem.wf_classical_problem P"
      and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
      and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
begin

lemmas strips_num_free_gate =
  strips_fold_checks_exec_D[OF P_T_normalized_problem_rx_unconditional[OF rp wf] gc]

text \<open>The executable STRIPS product \<^emph>\<open>is\<close> the abstract one built from the folded numeric product.\<close>
lemma as_strips_ground_by_cert_num_free_eq:
  "ast_classical_problem.as_strips (ground_by_cert P M) = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  unfolding ground_by_cert_strips_eq[OF rp wf ne cert
              strips_fold_checks_exec_imp_grounding_checks_exec[OF rp wf ne cert gc]]
            ast_classical_problem.numeric_P\<^sub>S_cert_eq_P\<^sub>S_cert[OF ne cert strips_num_free_gate rp wf]
  by (rule refl)

lemma strips_num_free_wf: "is_valid_problem_strips (ast_classical_problem.numeric_P\<^sub>S_cert P M)"
  by (rule ast_classical_problem.numeric_wf_as_strips_cert[OF ne cert strips_num_free_gate rp wf])

lemma strips_num_free_plan_iff:
  "(\<exists>ops. is_serial_solution_for_problem (ast_classical_problem.numeric_P\<^sub>S_cert P M) ops)
   \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)"
  by (rule ast_classical_problem.numeric_strips_plan_iff_cert[OF ne cert strips_num_free_gate rp wf])

lemma strips_num_free_plan_restore:
  assumes ser: "is_serial_solution_for_problem (ast_classical_problem.numeric_P\<^sub>S_cert P M) ops"
  shows "ast_classical_problem.valid_classical_plan2 P (reconstruct_plan_by_cert P M ops)"
proof -
  have "ast_classical_problem.valid_classical_plan2 P
          (ast_classical_problem.reconstruct_pipeline_plan_cert P M ops)"
    by (rule ast_classical_problem.numeric_strips_plan_reconstruct_cert[OF ne cert
          strips_num_free_gate rp wf ser])
  thus ?thesis
    unfolding reconstruct_plan_by_cert_eq[OF rp wf ne cert
                strips_fold_checks_exec_imp_grounding_checks_exec[OF rp wf ne cert gc]] .
qed

end

subsection \<open>DFS-founded numeric-free STRIPS entry point\<close>

text \<open>Mirror of \<open>ground_all_actions_dfs_e\<close> (\<^emph>\<open>Grounding_Pipeline_Numeric_Executable\<close>) --- same error monad, same \<open>return_iff\<close>
  discipline, same certificate re-check \<^const>\<open>dl_certified_model_dfs\<close> --- gated on
  \<^const>\<open>strips_fold_checks_exec\<close> and with \<^const>\<open>ast_classical_problem.as_strips\<close> applied to the
  grounded product. The result is the STRIPS encoding of the \<^emph>\<open>folded numeric\<close> product
  \<^const>\<open>ast_classical_problem.numeric_P\<^sub>S_cert\<close>, so the memory-optimized fold shared with the numeric
  grounder feeds the SAT planner.\<close>
definition ground_strips_all_actions_dfs_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + name strips_problem" where
  "ground_strips_all_actions_dfs_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (dl_certified_model_dfs (dl_rules R) (ast_classical_problem.const_names R) M dc)
           (STR ''reachability certificate rejected by the verified DFS checker'');
     check (strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M)
           (STR ''numeric-free grounding fold well-formedness checks failed'');
     Error_Monad.return (ast_classical_problem.as_strips (ground_by_cert P M))
   }"

lemma ground_strips_all_actions_dfs_e_return_iff[return_iff]:
  "ground_strips_all_actions_dfs_e f P = Inr Ps \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_dfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> Ps = ast_classical_problem.as_strips (ground_by_cert P M)))"
  unfolding ground_strips_all_actions_dfs_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

lemma ground_strips_all_actions_dfs_e_InrE:
  assumes "ground_strips_all_actions_dfs_e f P = Inr Ps"
  obtains M dc where
    "f (dl_program_of P) = (M, dc)"
    "ast_classical_problem.restrict_prob P"
    "ast_classical_problem.wf_classical_problem P"
    "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    "dl_certified_model
       (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
       (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_strips_all_actions_dfs_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_dfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps: "Ps = ast_classical_problem.as_strips (ground_by_cert P M)"
    by (auto split: prod.splits)
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_dfs_imp[OF certE])
  have Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
    unfolding Ps by (rule as_strips_ground_by_cert_num_free_eq[OF rp wf ne cert gc])
  show thesis by (rule that[OF fMdc rp wf ne cert gc Ps_cert])
qed

theorem ground_strips_all_actions_dfs_e_sound:
  assumes "ground_strips_all_actions_dfs_e f P = Inr Ps"
  shows "\<exists>M. Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  using assms by (elim ground_strips_all_actions_dfs_e_InrE) blast

theorem ground_strips_all_actions_dfs_e_wf:
  assumes "ground_strips_all_actions_dfs_e f P = Inr Ps"
  shows "is_valid_problem_strips Ps"
  using assms
proof (elim ground_strips_all_actions_dfs_e_InrE)
  fix M dc
  assume rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  show "is_valid_problem_strips Ps"
    unfolding Ps_cert by (rule strips_num_free_wf[OF rp wf ne cert gc])
qed

theorem ground_strips_all_actions_dfs_e_plan_valid_iff:
  assumes "ground_strips_all_actions_dfs_e f P = Inr Ps"
  shows "(\<exists>ops. is_serial_solution_for_problem Ps ops)
         \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)"
  using assms
proof (elim ground_strips_all_actions_dfs_e_InrE)
  fix M dc
  assume rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  show "(\<exists>ops. is_serial_solution_for_problem Ps ops)
        \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)"
    unfolding Ps_cert by (rule strips_num_free_plan_iff[OF rp wf ne cert gc])
qed

theorem ground_strips_all_actions_dfs_e_plan_restore:
  assumes ge: "ground_strips_all_actions_dfs_e f P = Inr Ps"
      and ser: "is_serial_solution_for_problem Ps ops"
  shows "ast_classical_problem.valid_classical_plan2 P
           (reconstruct_plan_by_cert P (fst (f (dl_program_of P))) ops)"
  using ge
proof (elim ground_strips_all_actions_dfs_e_InrE)
  fix M dc
  assume fMdc: "f (dl_program_of P) = (M, dc)"
    and rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  have "ast_classical_problem.valid_classical_plan2 P (reconstruct_plan_by_cert P M ops)"
    by (rule strips_num_free_plan_restore[OF rp wf ne cert gc ser[unfolded Ps_cert]])
  thus "ast_classical_problem.valid_classical_plan2 P
          (reconstruct_plan_by_cert P (fst (f (dl_program_of P))) ops)"
    unfolding fMdc fst_conv .
qed

subsection \<open>Ordered-scan numeric-free STRIPS entry point\<close>

text \<open>Verbatim mirror of \<^const>\<open>ground_strips_all_actions_dfs_e\<close> with the ordered linear scan
  \<^const>\<open>dl_certified_model_exec\<close> discharging datalog foundedness instead of the verified
  directed-cycle DFS. Both re-checks bridge to the same abstract \<^const>\<open>dl_certified_model\<close>, so the
  grounded product --- and every theorem about it --- is identical.\<close>
definition ground_strips_all_actions_exec_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + name strips_problem" where
  "ground_strips_all_actions_exec_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (dl_certified_model_exec (dl_rules R) (ast_classical_problem.const_names R) M dc)
           (STR ''reachability certificate rejected by the verified ordered-scan checker'');
     check (strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M)
           (STR ''numeric-free grounding fold well-formedness checks failed'');
     Error_Monad.return (ast_classical_problem.as_strips (ground_by_cert P M))
   }"

lemma ground_strips_all_actions_exec_e_return_iff[return_iff]:
  "ground_strips_all_actions_exec_e f P = Inr Ps \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_exec (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> Ps = ast_classical_problem.as_strips (ground_by_cert P M)))"
  unfolding ground_strips_all_actions_exec_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

lemma ground_strips_all_actions_exec_e_InrE:
  assumes "ground_strips_all_actions_exec_e f P = Inr Ps"
  obtains M dc where
    "f (dl_program_of P) = (M, dc)"
    "ast_classical_problem.restrict_prob P"
    "ast_classical_problem.wf_classical_problem P"
    "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    "dl_certified_model
       (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
       (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_strips_all_actions_exec_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_exec (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps: "Ps = ast_classical_problem.as_strips (ground_by_cert P M)"
    by (auto split: prod.splits)
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_exec_imp[OF certE])
  have Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
    unfolding Ps by (rule as_strips_ground_by_cert_num_free_eq[OF rp wf ne cert gc])
  show thesis by (rule that[OF fMdc rp wf ne cert gc Ps_cert])
qed

theorem ground_strips_all_actions_exec_e_sound:
  assumes "ground_strips_all_actions_exec_e f P = Inr Ps"
  shows "\<exists>M. Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  using assms by (elim ground_strips_all_actions_exec_e_InrE) blast

theorem ground_strips_all_actions_exec_e_wf:
  assumes "ground_strips_all_actions_exec_e f P = Inr Ps"
  shows "is_valid_problem_strips Ps"
  using assms
proof (elim ground_strips_all_actions_exec_e_InrE)
  fix M dc
  assume rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  show "is_valid_problem_strips Ps"
    unfolding Ps_cert by (rule strips_num_free_wf[OF rp wf ne cert gc])
qed

theorem ground_strips_all_actions_exec_e_plan_valid_iff:
  assumes "ground_strips_all_actions_exec_e f P = Inr Ps"
  shows "(\<exists>ops. is_serial_solution_for_problem Ps ops)
         \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)"
  using assms
proof (elim ground_strips_all_actions_exec_e_InrE)
  fix M dc
  assume rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  show "(\<exists>ops. is_serial_solution_for_problem Ps ops)
        \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)"
    unfolding Ps_cert by (rule strips_num_free_plan_iff[OF rp wf ne cert gc])
qed

theorem ground_strips_all_actions_exec_e_plan_restore:
  assumes ge: "ground_strips_all_actions_exec_e f P = Inr Ps"
      and ser: "is_serial_solution_for_problem Ps ops"
  shows "ast_classical_problem.valid_classical_plan2 P
           (reconstruct_plan_by_cert P (fst (f (dl_program_of P))) ops)"
  using ge
proof (elim ground_strips_all_actions_exec_e_InrE)
  fix M dc
  assume fMdc: "f (dl_program_of P) = (M, dc)"
    and rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  have "ast_classical_problem.valid_classical_plan2 P (reconstruct_plan_by_cert P M ops)"
    by (rule strips_num_free_plan_restore[OF rp wf ne cert gc ser[unfolded Ps_cert]])
  thus "ast_classical_problem.valid_classical_plan2 P
          (reconstruct_plan_by_cert P (fst (f (dl_program_of P))) ops)"
    unfolding fMdc fst_conv .
qed

subsection \<open>Global-sweep DFS numeric-free STRIPS entry point\<close>

text \<open>Verbatim mirror of \<^const>\<open>ground_strips_all_actions_dfs_e\<close> with the single-sweep certificate
  check \<^const>\<open>dl_certified_model_gdfs\<close>.\<close>
definition ground_strips_all_actions_gdfs_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + name strips_problem" where
  "ground_strips_all_actions_gdfs_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (dl_certified_model_gdfs (dl_rules R) (ast_classical_problem.const_names R) M dc)
           (STR ''reachability certificate rejected by the verified global-sweep DFS checker'');
     check (strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M)
           (STR ''numeric-free grounding fold well-formedness checks failed'');
     Error_Monad.return (ast_classical_problem.as_strips (ground_by_cert P M))
   }"

lemma ground_strips_all_actions_gdfs_e_return_iff[return_iff]:
  "ground_strips_all_actions_gdfs_e f P = Inr Ps \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_gdfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> Ps = ast_classical_problem.as_strips (ground_by_cert P M)))"
  unfolding ground_strips_all_actions_gdfs_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

lemma ground_strips_all_actions_gdfs_e_InrE:
  assumes "ground_strips_all_actions_gdfs_e f P = Inr Ps"
  obtains M dc where
    "f (dl_program_of P) = (M, dc)"
    "ast_classical_problem.restrict_prob P"
    "ast_classical_problem.wf_classical_problem P"
    "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    "dl_certified_model
       (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
       (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_strips_all_actions_gdfs_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_gdfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps: "Ps = ast_classical_problem.as_strips (ground_by_cert P M)"
    by (auto split: prod.splits)
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_gdfs_imp[OF certE])
  have Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
    unfolding Ps by (rule as_strips_ground_by_cert_num_free_eq[OF rp wf ne cert gc])
  show thesis by (rule that[OF fMdc rp wf ne cert gc Ps_cert])
qed

theorem ground_strips_all_actions_gdfs_e_sound:
  assumes "ground_strips_all_actions_gdfs_e f P = Inr Ps"
  shows "\<exists>M. Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  using assms by (elim ground_strips_all_actions_gdfs_e_InrE) blast

theorem ground_strips_all_actions_gdfs_e_wf:
  assumes "ground_strips_all_actions_gdfs_e f P = Inr Ps"
  shows "is_valid_problem_strips Ps"
  using assms
proof (elim ground_strips_all_actions_gdfs_e_InrE)
  fix M dc
  assume rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  show "is_valid_problem_strips Ps"
    unfolding Ps_cert by (rule strips_num_free_wf[OF rp wf ne cert gc])
qed

theorem ground_strips_all_actions_gdfs_e_plan_valid_iff:
  assumes "ground_strips_all_actions_gdfs_e f P = Inr Ps"
  shows "(\<exists>ops. is_serial_solution_for_problem Ps ops)
         \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)"
  using assms
proof (elim ground_strips_all_actions_gdfs_e_InrE)
  fix M dc
  assume rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  show "(\<exists>ops. is_serial_solution_for_problem Ps ops)
        \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)"
    unfolding Ps_cert by (rule strips_num_free_plan_iff[OF rp wf ne cert gc])
qed

theorem ground_strips_all_actions_gdfs_e_plan_restore:
  assumes ge: "ground_strips_all_actions_gdfs_e f P = Inr Ps"
      and ser: "is_serial_solution_for_problem Ps ops"
  shows "ast_classical_problem.valid_classical_plan2 P
           (reconstruct_plan_by_cert P (fst (f (dl_program_of P))) ops)"
  using ge
proof (elim ground_strips_all_actions_gdfs_e_InrE)
  fix M dc
  assume fMdc: "f (dl_program_of P) = (M, dc)"
    and rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "strips_fold_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Ps_cert: "Ps = ast_classical_problem.numeric_P\<^sub>S_cert P M"
  have "ast_classical_problem.valid_classical_plan2 P (reconstruct_plan_by_cert P M ops)"
    by (rule strips_num_free_plan_restore[OF rp wf ne cert gc ser[unfolded Ps_cert]])
  thus "ast_classical_problem.valid_classical_plan2 P
          (reconstruct_plan_by_cert P (fst (f (dl_program_of P))) ops)"
    unfolding fMdc fst_conv .
qed

end
