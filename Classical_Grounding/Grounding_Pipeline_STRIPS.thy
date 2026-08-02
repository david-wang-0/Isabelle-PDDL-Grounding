theory Grounding_Pipeline_STRIPS
  imports Grounding_Pipeline_Numeric "PDDL_to_STRIPS/Classical_PDDL_to_STRIPS"
begin

text \<open>The numeric-free specialization of the grounding pipeline: it imports the general
  (with-numerics) pipeline \<^verbatim>\<open>Grounding_Pipeline_Numeric\<close> and, on top of the certificate-grounded
  problem \<^term>\<open>P\<^sub>G_cert\<close>, converts it to STRIPS. This branch requires \<^const>\<open>ast_classical_problem.num_free_prob\<close>.\<close>

subsection \<open>The grounder's predicate names are nonempty\<close>

text \<open>The folded predicate names carry a trailing \<open>_<index>\<close> suffix
  (\<^const>\<open>fact_folder.fact_names\<close>, built with \<^const>\<open>idx_name\<close>), hence are nonempty
  unconditionally (\<open>fact_names_nonempty\<close>). This discharges the \<open>nonempty_pred_names\<close>
  side-condition for the grounded problem.\<close>

context ast_classical_problem begin

lemma wf_as_strips_compact:
  "wf_classical_problem \<Longrightarrow> grounded_prob \<Longrightarrow> normalized_prob \<Longrightarrow> num_free_prob \<Longrightarrow> is_valid_problem_strips as_strips"
  using grounded_normalized_numeric_free_problem.wf_as_strips
  unfolding grounded_normalized_numeric_free_problem_def
            grounded_normalized_problem_def grounded_normalized_problem_axioms_def
            grounded_problem_def grounded_problem_axioms_def wf_ast_classical_problem_def
            numeric_free_problem_def
            normalized_prob_def by blast

text \<open>Goal normalization collapses the goal to a single nullary predicate atom, and the
  subsequent stages (definedness explication, precondition splitting, definedness translation)
  leave a non-numeric atom untouched. Hence \<^term>\<open>P\<^sub>T\<close>'s goal is still a single predicate atom.\<close>
lemma goal_P\<^sub>T_single: "\<exists>gp. goal P\<^sub>T = Atom (predAtm gp [])"
proof -
  obtain gp where g3: "goal (ast_classical_problem.degoal_prob detype_classical_prob)
      = Atom (predAtm gp [])"
    using ast_classical_problem.degoal_prob_sel(4) by metis
  have "goal P\<^sub>X = explicate_def_fmla (goal (ast_classical_problem.degoal_prob detype_classical_prob))"
    unfolding P\<^sub>X_def by (simp add: ast_classical_problem.explicate_def_prob_sel(4))
  also have "\<dots> = Atom (predAtm gp [])"
    unfolding g3 explicate_def_fmla_def definedness_atoms_def divisor_zero_atoms_def by simp
  finally have gX: "goal P\<^sub>X = Atom (predAtm gp [])" .
  hence gN: "goal P\<^sub>N = Atom (predAtm gp [])"
    unfolding P\<^sub>N_def using ast_classical_problem.split_prob_sel(4) by metis
  hence "goal P\<^sub>T = Atom (predAtm gp [])"
    unfolding P\<^sub>T_def
    using ast_classical_problem.def_translate_prob_sel(4)[of P\<^sub>N]
    by (simp add: def_translate_fmla_def)
  thus ?thesis by blast
qed

text \<open>Assembling the \<^locale>\<open>strips_encodable_problem\<close> interpretation from the four normalization
  invariants plus the two STRIPS-specific side-conditions.\<close>
lemma strips_encodable_compact:
  assumes "wf_classical_problem" "grounded_prob" "normalized_prob" "num_free_prob"
    and np: "\<And>p. wf_pred p \<Longrightarrow> predicate.name p \<noteq> STR ''''"
    and gnc: "\<And>l1 l2. l1 \<in> set (un_and (goal P)) \<Longrightarrow> l2 \<in> set (un_and (goal P))
       \<Longrightarrow> fst (lit_as_goal l1) = fst (lit_as_goal l2)
       \<Longrightarrow> snd (lit_as_goal l1) = snd (lit_as_goal l2)"
  shows "strips_encodable_problem P"
proof unfold_locales
  show "wf_classical_problem" by (rule assms(1))
  show "grounded_prob" by (rule assms(2))
  show "prec_normed_dom \<and> is_conj (goal P)"
    using assms(3) unfolding normalized_prob_def by blast
  show "num_free_prob" by (rule assms(4))
  show "\<And>p. wf_pred p \<Longrightarrow> predicate.name p \<noteq> STR ''''" using np by blast
  show "\<And>l1 l2. l1 \<in> set (un_and (goal P)) \<Longrightarrow> l2 \<in> set (un_and (goal P))
       \<Longrightarrow> fst (lit_as_goal l1) = fst (lit_as_goal l2)
       \<Longrightarrow> snd (lit_as_goal l1) = snd (lit_as_goal l2)" using gnc by blast
qed

context
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes nonempty: "ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T) \<noteq> []"
      and cert: "dl_certified_model
                   (set (dl_rules (ast_classical_problem.relax_prob P\<^sub>T)))
                   (set (ast_classical_problem.const_names (ast_classical_problem.relax_prob P\<^sub>T))) M dc"
      and grounding_cert: "normalized_problem_rx.grounding_checks P\<^sub>T M"
begin

subsection \<open> Conversion to STRIPS (Certificate-based) \<close>

definition "P\<^sub>S_cert \<equiv> ast_classical_problem.as_strips (P\<^sub>G_cert M)"

lemma wf_as_strips_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "is_valid_problem_strips P\<^sub>S_cert"
proof -
  have nf: "ast_classical_problem.num_free_prob (P\<^sub>G_cert M)"
    using ground_cert_num_free[OF nonempty cert grounding_cert assms] .
  show ?thesis
    unfolding P\<^sub>S_cert_def
    using assms ast_classical_problem.wf_as_strips_compact
          wf_ground_cert_problem[OF nonempty cert grounding_cert assms] nf by blast
qed

text \<open>The grounded goal is a single nullary predicate atom: \<^const>\<open>fact_folder.ground_fmla\<close> maps the
  single-atom goal of \<^term>\<open>P\<^sub>T\<close> (\<open>goal_P\<^sub>T_single\<close>) to one nullary \<^const>\<open>predAtm\<close>.\<close>
lemma goal_P\<^sub>G_cert_single:
  assumes "restrict_prob" "wf_classical_problem"
  shows "\<exists>q. goal (P\<^sub>G_cert M) = Atom (predAtm q [])"
proof -
  interpret cr: certified_reachability P\<^sub>T M dc
    using certified_reachability_i[OF nonempty cert grounding_cert assms] .
  have pg_eq: "P\<^sub>G_cert M = cr.wfg.ground_prob"
    unfolding P\<^sub>G_cert_def[OF nonempty cert grounding_cert]
              cr.cert_facts'_def cr.cert_ops'_def by simp
  obtain gp where g: "goal P\<^sub>T = Atom (predAtm gp [])" using goal_P\<^sub>T_single by blast
  have "goal (P\<^sub>G_cert M) = cr.wfg.ground_fmla (goal P\<^sub>T)"
    unfolding pg_eq using cr.wfg.ground_prob_sel(4) by simp
  also have "\<dots> = Atom (predAtm (the (cr.wfg.fact_map (Atom (predAtm gp [])))) [])"
    unfolding g by simp
  finally show ?thesis by blast
qed

text \<open>Every well-formed predicate of the grounded problem has a nonempty name: the grounder's
  fact names end in an underscore-separated index (\<open>fact_names_nonempty\<close>).\<close>
lemma pg_cert_pred_nonempty:
  assumes "restrict_prob" "wf_classical_problem"
    and "ast_classical_domain.wf_pred (ast_problem.domain (P\<^sub>G_cert M)) n"
  shows "predicate.name n \<noteq> STR ''''"
proof -
  interpret cr: certified_reachability P\<^sub>T M dc
    using certified_reachability_i[OF nonempty cert grounding_cert assms(1,2)] .
  have pg_eq: "P\<^sub>G_cert M = cr.wfg.ground_prob"
    unfolding P\<^sub>G_cert_def[OF nonempty cert grounding_cert]
              cr.cert_facts'_def cr.cert_ops'_def by simp
  from assms(3) have "PredDecl n [] \<in> set (predicates (ast_problem.domain (P\<^sub>G_cert M)))"
    unfolding ast_classical_domain.wf_pred_def .
  hence "PredDecl n [] \<in> set (map (\<lambda>p. PredDecl p []) cr.wfg.fact_names)"
    unfolding pg_eq using cr.wfg.ground_prob_sel(1) cr.wfg.ground_dom_sel(2) by simp
  hence nfn: "n \<in> set cr.wfg.fact_names" by auto
  thus ?thesis using cr.wfg.fact_names_nonempty by blast
qed

lemma strips_encodable_P\<^sub>G_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "strips_encodable_problem (P\<^sub>G_cert M)"
proof -
  note wfg = wf_ground_cert_problem[OF nonempty cert grounding_cert assms]
  obtain q where q: "goal (P\<^sub>G_cert M) = Atom (predAtm q [])"
    using goal_P\<^sub>G_cert_single[OF assms] by blast
  show ?thesis
  proof (rule ast_classical_problem.strips_encodable_compact)
    show "ast_classical_problem.wf_classical_problem (P\<^sub>G_cert M)" using wfg by blast
    show "ast_classical_problem.grounded_prob (P\<^sub>G_cert M)" using wfg by blast
    show "ast_classical_problem.normalized_prob (P\<^sub>G_cert M)" using wfg by blast
    show "ast_classical_problem.num_free_prob (P\<^sub>G_cert M)"
      using ground_cert_num_free[OF nonempty cert grounding_cert assms] .
    show "\<And>p. ast_classical_domain.wf_pred (ast_problem.domain (P\<^sub>G_cert M)) p
              \<Longrightarrow> predicate.name p \<noteq> STR ''''"
      using pg_cert_pred_nonempty[OF assms] by blast
    show "\<And>l1 l2. l1 \<in> set (un_and (goal (P\<^sub>G_cert M)))
       \<Longrightarrow> l2 \<in> set (un_and (goal (P\<^sub>G_cert M)))
       \<Longrightarrow> fst (lit_as_goal l1) = fst (lit_as_goal l2)
       \<Longrightarrow> snd (lit_as_goal l1) = snd (lit_as_goal l2)"
      using q by simp
  qed
qed

text \<open>Soundness of the STRIPS encoding (existence form). The literal whole-plan restoration
  \<open>valid_classical_plan2 (reconstruct_plan_ground_cert M (restore_pddl_plan ops))\<close>
  is \<^emph>\<open>not\<close> provable for the same reason as \<open>restore_pddl_plan_valid\<close>: \<open>execute_serial_plan\<close> halts at
  the first non-applicable operator, so a STRIPS solution may carry trailing non-enabled operators
  that \<^const>\<open>ast_classical_problem.valid_classical_plan2\<close> rejects. We therefore conclude existence
  of a valid plan (the restored \<^emph>\<open>applicable prefix\<close> witnesses it).\<close>
lemma strips_plan_sound_cert:
  assumes "restrict_prob" "wf_classical_problem"
    and "is_serial_solution_for_problem P\<^sub>S_cert ops"
  shows "\<exists>\<pi>s. valid_classical_plan2 \<pi>s"
proof -
  from assms(3) have "is_serial_solution_for_problem (ast_classical_problem.as_strips (P\<^sub>G_cert M)) ops"
    unfolding P\<^sub>S_cert_def .
  with strips_encodable_problem.restore_pddl_plan_valid[OF strips_encodable_P\<^sub>G_cert[OF assms(1,2)]]
  have "\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 (P\<^sub>G_cert M) \<pi>s" by blast
  thus ?thesis using ground_cert_plan_valid_iff[OF nonempty cert grounding_cert assms(1,2)] by blast
qed

text \<open>Solvability equivalence: the grounded problem has a STRIPS serial solution iff the original
  classical problem has a valid plan. This is the end-to-end correctness theorem of the
  numeric-free grounding-to-STRIPS pipeline.\<close>
lemma strips_plan_iff_cert:
  assumes "restrict_prob" "wf_classical_problem"
  shows "(\<exists>ops. is_serial_solution_for_problem P\<^sub>S_cert ops) \<longleftrightarrow>
    (\<exists>\<pi>s. valid_classical_plan2 \<pi>s)"
proof -
  have "(\<exists>ops. is_serial_solution_for_problem P\<^sub>S_cert ops)
      \<longleftrightarrow> (\<exists>\<pi>s. ast_classical_problem.valid_classical_plan2 (P\<^sub>G_cert M) \<pi>s)"
    unfolding P\<^sub>S_cert_def
    using strips_encodable_problem.valid_plan_iff[OF strips_encodable_P\<^sub>G_cert[OF assms]] by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>\<pi>s. valid_classical_plan2 \<pi>s)"
    using ground_cert_plan_valid_iff[OF nonempty cert grounding_cert assms] by blast
  finally show ?thesis .
qed

subsection \<open> Concrete plan reconstruction (STRIPS solution \<open>\<rightarrow>\<close> original PDDL plan) \<close>

text \<open>End-to-end \<^emph>\<open>executable\<close> reconstruction: decode a STRIPS serial solution of \<^term>\<open>P\<^sub>S_cert\<close>
  into a concrete valid plan of the \<^emph>\<open>original\<close> problem \<^term>\<open>P\<close>. Two concrete stages compose:
  \<^const>\<open>ast_classical_problem.restore_prefix\<close> turns the STRIPS solution into a valid plan of the
  grounded problem \<^term>\<open>P\<^sub>G_cert M\<close> (its applicable prefix), and \<^const>\<open>reconstruct_plan_ground_cert\<close>
  lifts that back through grounding + the normalization chain to \<^term>\<open>P\<close>.\<close>
definition "reconstruct_pipeline_plan_cert ops \<equiv>
  reconstruct_plan_ground_cert M
    (ast_classical_problem.restore_prefix (P\<^sub>G_cert M)
       (ast_classical_problem.I (P\<^sub>G_cert M)) ops)"

theorem strips_plan_reconstruct_cert:
  assumes "restrict_prob" "wf_classical_problem"
    and "is_serial_solution_for_problem P\<^sub>S_cert ops"
  shows "valid_classical_plan2 (reconstruct_pipeline_plan_cert ops)"
proof -
  from assms(3) have ser:
    "is_serial_solution_for_problem (ast_classical_problem.as_strips (P\<^sub>G_cert M)) ops"
    unfolding P\<^sub>S_cert_def .
  have v: "ast_classical_problem.valid_classical_plan2 (P\<^sub>G_cert M)
            (ast_classical_problem.restore_prefix (P\<^sub>G_cert M)
               (ast_classical_problem.I (P\<^sub>G_cert M)) ops)"
    using strips_encodable_problem.restore_prefix_valid[OF strips_encodable_P\<^sub>G_cert[OF assms(1,2)] ser] .
  show ?thesis
    unfolding reconstruct_pipeline_plan_cert_def
    using ground_cert_plan_reconstruct[OF nonempty cert grounding_cert assms(1,2) v] .
qed

end

end
end
