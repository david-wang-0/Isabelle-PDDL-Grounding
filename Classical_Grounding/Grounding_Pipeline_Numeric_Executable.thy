theory Grounding_Pipeline_Numeric_Executable
  imports Grounding_Pipeline_Common_Executable Grounder_Timing
    Datalog_Graph.Datalog_Cycle_DFS_Global
begin

subsection \<open>Per-conjunct timing split of the certificate check (measurement instrumentation)\<close>

text \<open>Split the single \<open>check\<close> timing bracket of \<^const>\<open>dl_certified_model_dfs\<close> into one
  \<^const>\<open>time_it\<close> key per admissibility conjunct. Since \<^const>\<open>time_it\<close> is the identity
  (\<open>time_it_id\<close>) this is a proven-equal \<open>[code]\<close> refinement --- no logical change --- used only to
  attribute the certificate-check wall-clock across positivity / rule-validity / closure /
  body-closedness / acyclicity.\<close>

declare dl_admissible_dfs_def [code del]

lemma dl_admissible_dfs_timed_code [code]:
  "dl_admissible_dfs Pl Ul c =
     (time_it (STR ''chk_positive'')   (\<lambda>_. dl_positive_prog_exec Pl)
      \<and> time_it (STR ''chk_rulevalid'')  (\<lambda>_. list_all (dl_rule_valid_exec Pl Ul) (Datalog_Certificate.dl_rules c))
      \<and> time_it (STR ''chk_closure'')    (\<lambda>_. dl_closure_check_exec Pl Ul c)
      \<and> time_it (STR ''chk_bodyclosed'') (\<lambda>_. dl_body_closed c)
      \<and> time_it (STR ''chk_acyclic'')    (\<lambda>_. dl_acyclic_dfs c))"
  by (simp add: dl_admissible_dfs_def time_it_id)

declare dl_admissible_gdfs_def [code del]

lemma dl_admissible_gdfs_timed_code [code]:
  "dl_admissible_gdfs Pl Ul c =
     (time_it (STR ''chk_positive'')   (\<lambda>_. dl_positive_prog_exec Pl)
      \<and> time_it (STR ''chk_rulevalid'')  (\<lambda>_. list_all (dl_rule_valid_exec Pl Ul) (Datalog_Certificate.dl_rules c))
      \<and> time_it (STR ''chk_closure'')    (\<lambda>_. dl_closure_check_exec Pl Ul c)
      \<and> time_it (STR ''chk_bodyclosed'') (\<lambda>_. dl_body_closed c)
      \<and> time_it (STR ''chk_acyclic_global'') (\<lambda>_. dl_acyclic_dfs_global c))"
  by (simp add: dl_admissible_gdfs_def time_it_id)

section \<open>Executable numeric grounding (up to, but not including, the STRIPS conversion)\<close>

text \<open>The re-checked grounding pipeline, stopping one step before the propositional STRIPS encoding
  \<^const>\<open>ast_classical_problem.as_strips\<close>: it returns the grounded \<^emph>\<open>PDDL\<close> problem
  \<^term>\<open>numeric_ground_by_cert P M\<close> (a full \<^type>\<open>ast_problem\<close>) that \<^bold>\<open>retains numeric fluents\<close> ---
  the \<^emph>\<open>numeric-fluent-retaining\<close> grounder \<^const>\<open>grounder.numeric_ground_prob\<close> (verified in
  \<^theory>\<open>Classical_Grounded_PDDL.Numeric_Grounder\<close>: well-formed, and plan-preserving via
  \<open>ast_classical_problem.numeric_ground_cert_plan_valid_iff\<close>), \<^emph>\<open>not\<close> the propositional
  \<^const>\<open>ground_by_cert\<close> that drops numerics. Foundedness of the untrusted datalog certificate is
  discharged by the verified directed-cycle DFS (\<^const>\<open>dl_certified_model_dfs\<close>).\<close>

subsection \<open>Code setup for the fluent grounder\<close>

text \<open>Make the fluent grounder \<^const>\<open>grounder.numeric_ground_prob\<close> (and the domain / action
  constructors it is built from) code-generable, mirroring the propositional grounder's code
  equations (\<open>grounder.ground_dom_def[code]\<close> etc. in \<^theory>\<open>Classical_Grounding.Code_Setup\<close>). All the
  underlying operations (\<^const>\<open>simple_action_instantiations.res_inst\<close>, \<^const>\<open>grounder.op_names\<close>,
  \<^const>\<open>map2\<close>, \<^const>\<open>map_atom_fmla\<close>, \<^const>\<open>map_ast_effect\<close>) are already executable.\<close>

declare ast_classical_problem.numeric_ground_ac_def[code]
declare grounder.numeric_ground_dom_def[code]
declare grounder.numeric_ground_prob_def[code]

subsection \<open>Executable numeric grounder against a certified fact list\<close>

text \<open>Unconditional executable twin of \<^const>\<open>ast_classical_problem.numeric_P\<^sub>G_cert\<close>, replayed at the
  top level keyed on the certified facts \<open>M\<close>. Like \<^const>\<open>ground_by_cert\<close> but calling the
  fluent grounder \<^const>\<open>grounder.numeric_ground_prob\<close>; note it takes only the ops (the grounder's
  \<open>facts\<close> parameter is unused by the fluent grounder, so the locale drops it).\<close>
definition numeric_ground_by_cert where
  [code]: "numeric_ground_by_cert P M \<equiv>
     grounder.numeric_ground_prob (ast_classical_problem.P\<^sub>T P)
       (canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M))"

lemma numeric_ground_by_cert_eq:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
      and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
      and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
  shows "numeric_ground_by_cert P M = ast_classical_problem.numeric_P\<^sub>G_cert P M"
proof -
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.numeric_grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding numeric_grounding_checks_exec_eq[OF rx] .
  show ?thesis
    unfolding numeric_ground_by_cert_def ast_classical_problem.numeric_P\<^sub>G_cert_def[OF ne cert gc']
              cert_ops_of_exec_fast_canon_eq[OF rx]
    by (rule refl)
qed

subsection \<open>Error-reporting numeric grounding (well-formedness + certificate rejection)\<close>

text \<open>The DFS-founded numeric grounding in the \<^emph>\<open>error monad\<close> (\<^theory>\<open>Certification_Monads.Error_Monad\<close>):
  each well-formedness check and the certificate re-check yields a specific diagnostic on failure
  (\<^const>\<open>Inl\<close>) instead of a bare \<^const>\<open>None\<close>; on success it returns \<^const>\<open>Inr\<close> of the certified
  numeric grounding. This is the \<^emph>\<open>only\<close> numeric grounding entry point --- there is no separate
  option-returning variant; the \<open>return_iff\<close> characterization + the \<open>_InrE\<close> elimination drive the SML
  entry point and all downstream soundness / plan-preservation / plan-restoration theorems.\<close>

definition ground_via_cert_numeric_dfs_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + ast_classical_problem" where
  [code]: "ground_via_cert_numeric_dfs_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (time_it (STR ''check'')
              (\<lambda>_. dl_certified_model_dfs (dl_rules R) (ast_classical_problem.const_names R) M dc))
           (STR ''reachability certificate rejected by the verified DFS checker'');
     check (time_it (STR ''gcheck'')
              (\<lambda>_. numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M))
           (STR ''grounding well-formedness checks failed'');
     Error_Monad.return (time_it (STR ''enumerate'') (\<lambda>_. numeric_ground_by_cert P M))
   }"

lemma ground_via_cert_numeric_dfs_e_return_iff[return_iff]:
  "ground_via_cert_numeric_dfs_e f P = Inr Pg \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_dfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> Pg = numeric_ground_by_cert P M))"
  unfolding ground_via_cert_numeric_dfs_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

text \<open>Unpack a successful numeric grounding into the abstract certificate conditions and the identity
  \<open>Pg = numeric_P\<^sub>G_cert P M\<close> (converting \<open>num_free_prob\<close>/\<open>dl_certified_model_dfs\<close> to their abstract
  forms and applying \<open>numeric_ground_by_cert_eq\<close>).\<close>
lemma ground_via_cert_numeric_dfs_e_InrE:
  assumes "ground_via_cert_numeric_dfs_e f P = Inr Pg"
  obtains M dc where
    "f (dl_program_of P) = (M, dc)"
    "ast_classical_problem.restrict_prob P"
    "ast_classical_problem.wf_classical_problem P"
    "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    "dl_certified_model
       (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
       (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    "Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_via_cert_numeric_dfs_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_dfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Pg: "Pg = numeric_ground_by_cert P M"
    by (auto split: prod.splits)
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    by (rule numeric_free_problem_exec[OF normalized_problem_rx.relax_num_free[OF rx]])
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_dfs_imp[OF certE])
  have Pg_cert: "Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
    using Pg numeric_ground_by_cert_eq[OF rp wf ne cert gc] by simp
  show thesis by (rule that[OF fMdc rp wf pnf ne cert gc Pg_cert])
qed

theorem ground_via_cert_numeric_dfs_e_sound:
  assumes "ground_via_cert_numeric_dfs_e f P = Inr Pg"
  shows "\<exists>M. Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
  using assms by (elim ground_via_cert_numeric_dfs_e_InrE) blast

subsection \<open>Ordered-scan (Nemo topological-order) alternative to the DFS check\<close>

text \<open>Identical to \<^const>\<open>ground_via_cert_numeric_dfs_e\<close> except that the reachability certificate is
  re-checked with the \<^emph>\<open>ordered linear scan\<close> \<^const>\<open>dl_certified_model_exec\<close> (foundedness via
  \<^const>\<open>dl_founded_exec\<close>, which validates the certificate's rule order --- the topological order the
  Nemo oracle emits) instead of the per-vertex directed-cycle DFS \<^const>\<open>dl_certified_model_dfs\<close>.
  Both are sound (\<open>dl_certified_model_exec_imp\<close> / \<open>dl_certified_model_dfs_imp\<close> to the same
  abstract \<^const>\<open>dl_certified_model\<close>), so the soundness argument is verbatim once the \<open>InrE\<close> rule has
  converted the concrete check. On Hard-To-Ground tasks the ordered scan is \<open>O(|rules| \<cdot> |body| \<cdot>
  |facts|)\<close> versus the DFS's \<open>O(|facts|\<^sup>2)\<close>.\<close>
definition ground_via_cert_numeric_exec_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + ast_classical_problem" where
  [code]: "ground_via_cert_numeric_exec_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (time_it (STR ''check'')
              (\<lambda>_. dl_certified_model_exec (dl_rules R) (ast_classical_problem.const_names R) M dc))
           (STR ''reachability certificate rejected by the verified ordered-scan checker'');
     check (time_it (STR ''gcheck'')
              (\<lambda>_. numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M))
           (STR ''grounding well-formedness checks failed'');
     Error_Monad.return (time_it (STR ''enumerate'') (\<lambda>_. numeric_ground_by_cert P M))
   }"

lemma ground_via_cert_numeric_exec_e_return_iff[return_iff]:
  "ground_via_cert_numeric_exec_e f P = Inr Pg \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_exec (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> Pg = numeric_ground_by_cert P M))"
  unfolding ground_via_cert_numeric_exec_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

lemma ground_via_cert_numeric_exec_e_InrE:
  assumes "ground_via_cert_numeric_exec_e f P = Inr Pg"
  obtains M dc where
    "f (dl_program_of P) = (M, dc)"
    "ast_classical_problem.restrict_prob P"
    "ast_classical_problem.wf_classical_problem P"
    "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    "dl_certified_model
       (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
       (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    "Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_via_cert_numeric_exec_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_exec (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Pg: "Pg = numeric_ground_by_cert P M"
    by (auto split: prod.splits)
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    by (rule numeric_free_problem_exec[OF normalized_problem_rx.relax_num_free[OF rx]])
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_exec_imp[OF certE])
  have Pg_cert: "Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
    using Pg numeric_ground_by_cert_eq[OF rp wf ne cert gc] by simp
  show thesis by (rule that[OF fMdc rp wf pnf ne cert gc Pg_cert])
qed

theorem ground_via_cert_numeric_exec_e_sound:
  assumes "ground_via_cert_numeric_exec_e f P = Inr Pg"
  shows "\<exists>M. Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
  using assms by (elim ground_via_cert_numeric_exec_e_InrE) blast

subsection \<open>Fast single-sweep DFS alternative to the per-vertex check\<close>

text \<open>Identical to \<^const>\<open>ground_via_cert_numeric_dfs_e\<close> except that the reachability certificate is
  re-checked with the fast \<^emph>\<open>single-sweep\<close> directed-cycle DFS \<^const>\<open>dl_certified_model_gdfs\<close>
  (foundedness via \<^const>\<open>dl_acyclic_dfs_global\<close>, one \<open>O(|V|+|E|)\<close> pass sharing \<open>seen\<close> across roots)
  instead of the per-vertex \<^const>\<open>dl_certified_model_dfs\<close> (which restarts the DFS from every vertex).
  Both are sound (\<open>dl_certified_model_gdfs_imp\<close> / \<open>dl_certified_model_dfs_imp\<close> to the same abstract
  \<^const>\<open>dl_certified_model\<close>), so the grounded output is identical.\<close>

definition ground_via_cert_numeric_gdfs_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + ast_classical_problem" where
  [code]: "ground_via_cert_numeric_gdfs_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (time_it (STR ''check'')
              (\<lambda>_. dl_certified_model_gdfs (dl_rules R) (ast_classical_problem.const_names R) M dc))
           (STR ''reachability certificate rejected by the verified global-sweep DFS checker'');
     check (time_it (STR ''gcheck'')
              (\<lambda>_. numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M))
           (STR ''grounding well-formedness checks failed'');
     Error_Monad.return (time_it (STR ''enumerate'') (\<lambda>_. numeric_ground_by_cert P M))
   }"

lemma ground_via_cert_numeric_gdfs_e_return_iff[return_iff]:
  "ground_via_cert_numeric_gdfs_e f P = Inr Pg \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_gdfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> Pg = numeric_ground_by_cert P M))"
  unfolding ground_via_cert_numeric_gdfs_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

lemma ground_via_cert_numeric_gdfs_e_InrE:
  assumes "ground_via_cert_numeric_gdfs_e f P = Inr Pg"
  obtains M dc where
    "f (dl_program_of P) = (M, dc)"
    "ast_classical_problem.restrict_prob P"
    "ast_classical_problem.wf_classical_problem P"
    "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    "dl_certified_model
       (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
       (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    "Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_via_cert_numeric_gdfs_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_gdfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Pg: "Pg = numeric_ground_by_cert P M"
    by (auto split: prod.splits)
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    by (rule numeric_free_problem_exec[OF normalized_problem_rx.relax_num_free[OF rx]])
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_gdfs_imp[OF certE])
  have Pg_cert: "Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
    using Pg numeric_ground_by_cert_eq[OF rp wf ne cert gc] by simp
  show thesis by (rule that[OF fMdc rp wf pnf ne cert gc Pg_cert])
qed

theorem ground_via_cert_numeric_gdfs_e_sound:
  assumes "ground_via_cert_numeric_gdfs_e f P = Inr Pg"
  shows "\<exists>M. Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
  using assms by (elim ground_via_cert_numeric_gdfs_e_InrE) blast

text \<open>Plan-validity equivalence: whenever the numeric grounder succeeds, the grounded
  (fluent-retaining) output has a valid plan \<^emph>\<open>iff\<close> the original problem does.\<close>
theorem ground_via_cert_numeric_dfs_e_plan_valid_iff:
  assumes "ground_via_cert_numeric_dfs_e f P = Inr Pg"
  shows "(\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)
         \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 Pg \<pi>s')"
  using assms
proof (elim ground_via_cert_numeric_dfs_e_InrE)
  fix M dc
  assume rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Pg_cert: "Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.numeric_grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding numeric_grounding_checks_exec_eq[OF rx] .
  show "(\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 P \<pi>s)
        \<longleftrightarrow> (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 Pg \<pi>s')"
    unfolding Pg_cert
    by (rule ast_classical_problem.numeric_ground_cert_plan_valid_iff[OF ne cert gc' rp wf])
qed

subsection \<open>Executable plan restoration for the numeric grounder\<close>

text \<open>Numeric bridge for the shared \<^const>\<open>reconstruct_plan_by_cert_numeric\<close> (defined in
  \<^theory>\<open>Classical_Grounding.Grounding_Pipeline_Common_Executable\<close>): it equals the abstract
  \<^const>\<open>ast_classical_problem.numeric_reconstruct_plan_ground_cert\<close> under the certificate conditions.\<close>
lemma reconstruct_plan_by_cert_numeric_eq:
  assumes rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
      and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
      and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
  shows "reconstruct_plan_by_cert_numeric P M \<pi>s = ast_classical_problem.numeric_reconstruct_plan_ground_cert P M \<pi>s"
proof -
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.numeric_grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding numeric_grounding_checks_exec_eq[OF rx] .
  show ?thesis
    unfolding reconstruct_plan_by_cert_numeric_def
              ast_classical_problem.numeric_reconstruct_plan_ground_cert_def[OF ne cert gc']
              cert_ops_of_exec_fast_canon_eq[OF rx]
    by (rule refl)
qed

text \<open>Plan restoration at the error-monad level: whenever the numeric grounder succeeds, any valid
  plan \<open>\<pi>s\<close> of the grounded output \<open>Pg\<close> is restored (via \<^const>\<open>reconstruct_plan_by_cert_numeric\<close>) to a
  \<^emph>\<open>concrete\<close> valid plan of the original problem \<open>P\<close>.\<close>
theorem ground_via_cert_numeric_dfs_e_plan_restore:
  assumes ie: "ground_via_cert_numeric_dfs_e f P = Inr Pg"
      and vp: "ast_classical_problem.valid_classical_plan2 Pg \<pi>s"
  shows "ast_classical_problem.valid_classical_plan2 P
           (reconstruct_plan_by_cert_numeric P (fst (f (dl_program_of P))) \<pi>s)"
  using ie
proof (elim ground_via_cert_numeric_dfs_e_InrE)
  fix M dc
  assume fMdc: "f (dl_program_of P) = (M, dc)"
    and rp: "ast_classical_problem.restrict_prob P" and wf: "ast_classical_problem.wf_classical_problem P"
    and pnf: "numeric_free_problem (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and cert: "dl_certified_model
                 (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                 (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and Pg_cert: "Pg = ast_classical_problem.numeric_P\<^sub>G_cert P M"
  have rx: "normalized_problem_rx (ast_classical_problem.P\<^sub>T P)"
    by (rule P_T_normalized_problem_rx_unconditional[OF rp wf])
  have gc': "normalized_problem_rx.numeric_grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    using gc unfolding numeric_grounding_checks_exec_eq[OF rx] .
  have "ast_classical_problem.valid_classical_plan2 P
          (ast_classical_problem.numeric_reconstruct_plan_ground_cert P M \<pi>s)"
    using vp[unfolded Pg_cert]
          ast_classical_problem.numeric_ground_cert_plan_reconstruct[OF ne cert gc' rp wf] by blast
  thus "ast_classical_problem.valid_classical_plan2 P
          (reconstruct_plan_by_cert_numeric P (fst (f (dl_program_of P))) \<pi>s)"
    unfolding fMdc fst_conv reconstruct_plan_by_cert_numeric_eq[OF rp wf ne cert gc] .
qed

subsection \<open>Streaming numeric grounding: return the ops enumeration, not the built problem\<close>

text \<open>Memory optimization for action-list-bound domains. Instead of materializing the full
  ground-action-schema list inside \<^const>\<open>numeric_ground_by_cert\<close> (the \<open>map2\<close> that expands every
  reachable op into an instantiated precondition/effect schema --- the peak-RSS bottleneck), these
  streaming variants run \<^emph>\<open>exactly the same checks\<close> as their \<open>_e\<close> twins but return only the small
  materialized ops list \<^term>\<open>canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)\<close>. The
  untrusted SML printer then folds the schema expansion \<^const>\<open>ast_classical_problem.numeric_ground_ac\<close>
  over that ops list, one schema live at a time, reproducing the identical bytes. Each soundness lemma
  records both the ops identity and that building the full problem from \<open>M\<close> would have equalled the
  abstract \<^const>\<open>ast_classical_problem.numeric_P\<^sub>G_cert\<close> (via \<open>numeric_ground_by_cert_eq\<close> under the
  checks that \<open>Inr\<close> established).\<close>

definition ground_via_cert_numeric_dfs_stream_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + ast_classical_plan_action list" where
  [code]: "ground_via_cert_numeric_dfs_stream_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (time_it (STR ''check'')
              (\<lambda>_. dl_certified_model_dfs (dl_rules R) (ast_classical_problem.const_names R) M dc))
           (STR ''reachability certificate rejected by the verified DFS checker'');
     check (time_it (STR ''gcheck'')
              (\<lambda>_. numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M))
           (STR ''grounding well-formedness checks failed'');
     Error_Monad.return (time_it (STR ''enumerate'')
       (\<lambda>_. canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)))
   }"

lemma ground_via_cert_numeric_dfs_stream_e_return_iff[return_iff]:
  "ground_via_cert_numeric_dfs_stream_e f P = Inr ops \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_dfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)))"
  unfolding ground_via_cert_numeric_dfs_stream_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

theorem ground_via_cert_numeric_dfs_stream_e_sound:
  assumes "ground_via_cert_numeric_dfs_stream_e f P = Inr ops"
  shows "\<exists>M dc. f (dl_program_of P) = (M, dc)
      \<and> ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)
      \<and> numeric_ground_by_cert P M = ast_classical_problem.numeric_P\<^sub>G_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_via_cert_numeric_dfs_stream_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_dfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and ops_eq: "ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)"
    by (auto split: prod.splits)
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_dfs_imp[OF certE])
  have "numeric_ground_by_cert P M = ast_classical_problem.numeric_P\<^sub>G_cert P M"
    by (rule numeric_ground_by_cert_eq[OF rp wf ne cert gc])
  thus ?thesis using fMdc ops_eq by blast
qed

definition ground_via_cert_numeric_exec_stream_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + ast_classical_plan_action list" where
  [code]: "ground_via_cert_numeric_exec_stream_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (time_it (STR ''check'')
              (\<lambda>_. dl_certified_model_exec (dl_rules R) (ast_classical_problem.const_names R) M dc))
           (STR ''reachability certificate rejected by the verified ordered-scan checker'');
     check (time_it (STR ''gcheck'')
              (\<lambda>_. numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M))
           (STR ''grounding well-formedness checks failed'');
     Error_Monad.return (time_it (STR ''enumerate'')
       (\<lambda>_. canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)))
   }"

lemma ground_via_cert_numeric_exec_stream_e_return_iff[return_iff]:
  "ground_via_cert_numeric_exec_stream_e f P = Inr ops \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_exec (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)))"
  unfolding ground_via_cert_numeric_exec_stream_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

theorem ground_via_cert_numeric_exec_stream_e_sound:
  assumes "ground_via_cert_numeric_exec_stream_e f P = Inr ops"
  shows "\<exists>M dc. f (dl_program_of P) = (M, dc)
      \<and> ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)
      \<and> numeric_ground_by_cert P M = ast_classical_problem.numeric_P\<^sub>G_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_via_cert_numeric_exec_stream_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_exec (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and ops_eq: "ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)"
    by (auto split: prod.splits)
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_exec_imp[OF certE])
  have "numeric_ground_by_cert P M = ast_classical_problem.numeric_P\<^sub>G_cert P M"
    by (rule numeric_ground_by_cert_eq[OF rp wf ne cert gc])
  thus ?thesis using fMdc ops_eq by blast
qed

definition ground_via_cert_numeric_gdfs_stream_e ::
  "(dl_program \<Rightarrow> fact list \<times> (predicate, object) dl_certificate)
     \<Rightarrow> ast_classical_problem \<Rightarrow> String.literal + ast_classical_plan_action list" where
  [code]: "ground_via_cert_numeric_gdfs_stream_e f P \<equiv> do {
     check (ast_classical_problem.restrict_prob P)
           (STR ''input problem is outside the restricted (single-type) fragment'');
     check (ast_classical_problem.wf_classical_problem P)
           (STR ''input problem is not well-formed'');
     let R = ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P);
     let (M, dc) = f (dl_program_of P);
     check (ast_classical_problem.const_names R \<noteq> [])
           (STR ''relaxed problem has an empty object universe'');
     check (time_it (STR ''check'')
              (\<lambda>_. dl_certified_model_gdfs (dl_rules R) (ast_classical_problem.const_names R) M dc))
           (STR ''reachability certificate rejected by the verified global-sweep DFS checker'');
     check (time_it (STR ''gcheck'')
              (\<lambda>_. numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M))
           (STR ''grounding well-formedness checks failed'');
     Error_Monad.return (time_it (STR ''enumerate'')
       (\<lambda>_. canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)))
   }"

lemma ground_via_cert_numeric_gdfs_stream_e_return_iff[return_iff]:
  "ground_via_cert_numeric_gdfs_stream_e f P = Inr ops \<longleftrightarrow>
   (ast_classical_problem.restrict_prob P
    \<and> ast_classical_problem.wf_classical_problem P
    \<and> (case f (dl_program_of P) of (M, dc) \<Rightarrow>
         ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []
         \<and> dl_certified_model_gdfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
              (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc
         \<and> numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M
         \<and> ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)))"
  unfolding ground_via_cert_numeric_gdfs_stream_e_def
  by (auto simp: return_iff Let_def split: prod.splits)

theorem ground_via_cert_numeric_gdfs_stream_e_sound:
  assumes "ground_via_cert_numeric_gdfs_stream_e f P = Inr ops"
  shows "\<exists>M dc. f (dl_program_of P) = (M, dc)
      \<and> ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)
      \<and> numeric_ground_by_cert P M = ast_classical_problem.numeric_P\<^sub>G_cert P M"
proof -
  obtain M dc where fMdc: "f (dl_program_of P) = (M, dc)" by (cases "f (dl_program_of P)")
  from assms[unfolded ground_via_cert_numeric_gdfs_stream_e_return_iff] fMdc
  have rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_gdfs (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "numeric_grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and ops_eq: "ops = canon (cert_ops_of_exec_fast (ast_classical_problem.P\<^sub>T P) M)"
    by (auto split: prod.splits)
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_gdfs_imp[OF certE])
  have "numeric_ground_by_cert P M = ast_classical_problem.numeric_P\<^sub>G_cert P M"
    by (rule numeric_ground_by_cert_eq[OF rp wf ne cert gc])
  thus ?thesis using fMdc ops_eq by blast
qed

end
