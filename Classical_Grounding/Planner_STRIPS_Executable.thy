theory Planner_STRIPS_Executable
  imports
    Grounding_Pipeline_STRIPS_Executable
    Verified_SAT_Based_AI_Planning.SAT_Plan_Extensions
    Verified_SAT_Based_AI_Planning.Solve_SASP
begin

section \<open>Executable SAT-based planner \<open>plan_by_cert\<close>\<close>

text \<open>The SAT half of the executable pipeline. The grounded STRIPS problem (from
  \<^const>\<open>ground_via_cert\<close>) is encoded with the AFP \<open>\<forall>\<close>-step encoding
  \<^const>\<open>encode_problem_with_operator_interference_exclusion\<close> (\<open>\<Phi>\<^sub>\<forall>\<close>), handed to an
  \<^emph>\<open>untrusted\<close> external SAT oracle \<open>g\<close> as a DIMACS-style \<open>int list list\<close>, and the returned
  assignment is \<^emph>\<open>re-checked\<close> by the only trusted runtime check on this path: the executable
  model check \<open>\<A> \<Turnstile> \<Phi>\<^sub>\<forall> P\<^sub>S t\<close>. Serial-solution-ness then follows \<^emph>\<open>by theorem\<close>
  (@{thm [source] serializable_encoding_decoded_plan_is_serializable}), not by execution ---
  \<^const>\<open>is_serial_solution_for_problem\<close> itself (\<open>\<subseteq>\<^sub>m\<close> over function states) is not executable.
  A bug in the DIMACS translation can only lose \<^emph>\<open>completeness\<close> (the model check fails and the
  horizon loop moves on), never soundness.\<close>

subsection \<open>Formula \<open>\<rightarrow>\<close> DIMACS-style CNF\<close>

text \<open>The DIMACS layer is reused from the AFP \<open>Solve_SASP\<close>: \<^const>\<open>cnf_to_dimacs\<close> /
  \<^const>\<open>disj_to_dimacs\<close> flatten a CNF formula into an \<open>int list list\<close>,
  \<^const>\<open>cnf_to_dimacs.var_to_dimacs\<close> numbers the SATPlan variables (\<open>h\<close> bounds the time
  indices --- use \<open>Suc t\<close> for horizon \<open>t\<close> --- and \<open>n_ops\<close> the operator indices; DIMACS
  variables must be \<open>\<ge> 1\<close>), and \<^const>\<open>dimacs_model_to_abs\<close> reads an (untrusted) assignment
  back as a valuation on \<^typ>\<open>nat\<close> variables. \<open>\<Phi>\<^sub>\<forall> \<Pi> t\<close> is \<^const>\<open>is_cnf\<close> (@{thm [source]
  is_cnf_encode_problem_with_operator_interference_exclusion}), so the destructuring is total
  on the formulas we feed it. No lemmas about these functions are needed (see above).

  Importing \<open>Solve_SASP\<close> also drags the SAS+ \<open>ast_problem\<close> namespace into scope alongside the
  Classical PDDL one; every reference in this development is qualified
  (\<open>ast_classical_problem.*\<close>), so the collision stays harmless.\<close>

subsection \<open>The horizon loop\<close>

text \<open>Try one horizon \<open>t\<close>: encode, hand the CNF to the SAT oracle \<open>g :: int list list \<Rightarrow>
  int list\<close>, pull the assignment back along the variable numbering, and \<^emph>\<open>re-check the model
  in HOL\<close>. Only on a successful model check is the decoded parallel plan flattened and
  returned.\<close>
definition try_horizon ::
  "(int list list \<Rightarrow> int list) \<Rightarrow> 'v strips_problem \<Rightarrow> nat \<Rightarrow> 'v strips_operator list option"
  where
  [code]: "try_horizon g PS t \<equiv>
     (let F = encode_problem_with_operator_interference_exclusion PS t;
          vmap = cnf_to_dimacs.var_to_dimacs (Suc t) (Suc (length (strips_problem.operators_of PS)));
          M = g (cnf_to_dimacs (map_formula vmap F));
          \<A> = dimacs_model_to_abs M (\<lambda>_. False) \<circ> vmap
      in if \<A> \<Turnstile> F then Some (concat (decode_plan PS \<A> t)) else None)"

fun sat_solve_strips ::
  "(int list list \<Rightarrow> int list) \<Rightarrow> nat \<Rightarrow> 'v strips_problem \<Rightarrow> 'v strips_operator list option"
  where
  "sat_solve_strips g 0 PS = try_horizon g PS 0"
| "sat_solve_strips g (Suc t) PS =
     (case sat_solve_strips g t PS of
        Some ops \<Rightarrow> Some ops
      | None \<Rightarrow> try_horizon g PS (Suc t))"

lemma try_horizon_sound:
  assumes "is_valid_problem_strips PS"
      and "try_horizon g PS t = Some ops"
    shows "STRIPS_Semantics.is_serial_solution_for_problem PS ops"
proof -
  let ?vmap = "cnf_to_dimacs.var_to_dimacs (Suc t) (Suc (length (strips_problem.operators_of PS)))"
  let ?\<A> = "dimacs_model_to_abs (g (cnf_to_dimacs (map_formula ?vmap
              (encode_problem_with_operator_interference_exclusion PS t)))) (\<lambda>_. False) \<circ> ?vmap"
  from assms(2) have model: "?\<A> \<Turnstile> encode_problem_with_operator_interference_exclusion PS t"
    and ops: "ops = concat (decode_plan PS ?\<A> t)"
    unfolding try_horizon_def Let_def by (auto split: if_splits)
  from serializable_encoding_decoded_plan_is_serializable[OF assms(1) model] ops
  show ?thesis by simp
qed

lemma sat_solve_strips_sound:
  assumes "is_valid_problem_strips PS"
      and "sat_solve_strips g t_max PS = Some ops"
    shows "STRIPS_Semantics.is_serial_solution_for_problem PS ops"
  using assms(2)
proof (induction t_max)
  case 0 then show ?case using try_horizon_sound[OF assms(1)] by simp
next
  case (Suc t) then show ?case
    using try_horizon_sound[OF assms(1)] by (auto split: option.splits)
qed

subsection \<open>The planner\<close>

text \<open>End-to-end: ground via the (re-checked) reachability oracle \<open>f\<close>, solve via the
  (re-checked) SAT oracle \<open>g\<close> with horizons \<open>0..t_max\<close>, and reconstruct a plan of the
  \<^emph>\<open>original\<close> problem through the verified restoration chain.\<close>
definition plan_by_cert where
  [code]: "plan_by_cert f g t_max P \<equiv>
     Option.bind (ground_via_cert' f P) (\<lambda>(Mdc, PS).
       Option.bind (sat_solve_strips g t_max PS) (\<lambda>ops.
         Some (reconstruct_plan_by_cert P (fst Mdc) ops)))"

subsection \<open>Soundness\<close>

text \<open>The payoff theorem: whatever the two untrusted oracles do, a \<^const>\<open>Some\<close> answer of
  \<^const>\<open>plan_by_cert\<close> is a valid plan of the \<^emph>\<open>original\<close> PDDL problem. The certificate side
  is re-checked by \<open>admissible_exec\<close>/\<open>grounding_checks_exec\<close> (bridged to the verified pipeline
  by \<open>ground_by_cert_strips_eq\<close>/\<open>reconstruct_plan_by_cert_eq\<close>), the SAT side by the executable
  model check inside \<^const>\<open>try_horizon\<close>.\<close>
theorem plan_by_cert_sound:
  assumes "plan_by_cert f g t_max P = Some \<pi>s"
  shows "ast_classical_problem.valid_classical_plan2 P \<pi>s"
proof -
  from assms obtain Mdc PS ops where
    g1: "ground_via_cert' f P = Some (Mdc, PS)" and
    g2: "sat_solve_strips g t_max PS = Some ops" and
    \<pi>s: "\<pi>s = reconstruct_plan_by_cert P (fst Mdc) ops"
    unfolding plan_by_cert_def by (auto split: Option.bind_splits)
  obtain M dc where Mdc: "Mdc = (M, dc)" by (cases Mdc)
  from g1[unfolded Mdc] have
        rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_exec
                  (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and PS: "PS = ast_classical_problem.as_strips (ground_by_cert P M)"
    unfolding ground_via_cert'_def by (auto simp: Let_def split: if_splits prod.splits)
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_exec_imp[OF certE])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    by (rule grounding_checks_exec_P\<^sub>T[OF rp wf gc])
  have PS_cert: "PS = ast_classical_problem.P\<^sub>S_cert P M"
    using PS ground_by_cert_strips_eq[OF rp wf ne cert gc] by simp
  have valid: "is_valid_problem_strips PS"
    unfolding PS_cert by (rule ast_classical_problem.wf_as_strips_cert[OF ne cert gc' rp wf])
  have serial: "STRIPS_Semantics.is_serial_solution_for_problem (ast_classical_problem.P\<^sub>S_cert P M) ops"
    using sat_solve_strips_sound[OF valid g2] unfolding PS_cert .
  have "ast_classical_problem.valid_classical_plan2 P
          (ast_classical_problem.reconstruct_pipeline_plan_cert P M ops)"
    by (rule ast_classical_problem.strips_plan_reconstruct_cert[OF ne cert gc' rp wf serial])
  thus ?thesis
    unfolding \<pi>s Mdc fst_conv reconstruct_plan_by_cert_eq[OF rp wf ne cert gc] .
qed

subsection \<open>The DFS-founded planner\<close>

text \<open>Twin of \<^const>\<open>plan_by_cert\<close> using the DFS-founded grounding gate \<^const>\<open>ground_via_cert'_dfs\<close>
  (foundedness via the verified directed-cycle DFS). Same soundness, since
  \<^const>\<open>dl_certified_model_dfs\<close> bridges to the same abstract \<^const>\<open>dl_certified_model\<close>.\<close>

definition plan_by_cert_dfs where
  [code]: "plan_by_cert_dfs f g t_max P \<equiv>
     Option.bind (ground_via_cert'_dfs f P) (\<lambda>(Mdc, PS).
       Option.bind (sat_solve_strips g t_max PS) (\<lambda>ops.
         Some (reconstruct_plan_by_cert P (fst Mdc) ops)))"

theorem plan_by_cert_dfs_sound:
  assumes "plan_by_cert_dfs f g t_max P = Some \<pi>s"
  shows "ast_classical_problem.valid_classical_plan2 P \<pi>s"
proof -
  from assms obtain Mdc PS ops where
    g1: "ground_via_cert'_dfs f P = Some (Mdc, PS)" and
    g2: "sat_solve_strips g t_max PS = Some ops" and
    \<pi>s: "\<pi>s = reconstruct_plan_by_cert P (fst Mdc) ops"
    unfolding plan_by_cert_dfs_def by (auto split: Option.bind_splits)
  obtain M dc where Mdc: "Mdc = (M, dc)" by (cases Mdc)
  from g1[unfolded Mdc] have
        rp: "ast_classical_problem.restrict_prob P"
    and wf: "ast_classical_problem.wf_classical_problem P"
    and ne: "ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)) \<noteq> []"
    and certE: "dl_certified_model_dfs
                  (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))
                  (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))) M dc"
    and gc: "grounding_checks_exec (ast_classical_problem.P\<^sub>T P) M"
    and PS: "PS = ast_classical_problem.as_strips (ground_by_cert P M)"
    unfolding ground_via_cert'_dfs_def by (auto simp: Let_def split: if_splits prod.splits)
  have cert: "dl_certified_model
                (set (dl_rules (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P))))
                (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob (ast_classical_problem.P\<^sub>T P)))) M dc"
    by (rule dl_certified_model_dfs_imp[OF certE])
  have gc': "normalized_problem_rx.grounding_checks (ast_classical_problem.P\<^sub>T P) M"
    by (rule grounding_checks_exec_P\<^sub>T[OF rp wf gc])
  have PS_cert: "PS = ast_classical_problem.P\<^sub>S_cert P M"
    using PS ground_by_cert_strips_eq[OF rp wf ne cert gc] by simp
  have valid: "is_valid_problem_strips PS"
    unfolding PS_cert by (rule ast_classical_problem.wf_as_strips_cert[OF ne cert gc' rp wf])
  have serial: "STRIPS_Semantics.is_serial_solution_for_problem (ast_classical_problem.P\<^sub>S_cert P M) ops"
    using sat_solve_strips_sound[OF valid g2] unfolding PS_cert .
  have "ast_classical_problem.valid_classical_plan2 P
          (ast_classical_problem.reconstruct_pipeline_plan_cert P M ops)"
    by (rule ast_classical_problem.strips_plan_reconstruct_cert[OF ne cert gc' rp wf serial])
  thus ?thesis
    unfolding \<pi>s Mdc fst_conv reconstruct_plan_by_cert_eq[OF rp wf ne cert gc] .
qed

end
