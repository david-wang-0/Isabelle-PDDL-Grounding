theory Temporal_Grounding_Pipeline_Numeric
  imports Temporal_Type_Normalization.Temporal_Type_Normalization_Semantics
    Temporal_Goal_Normalization.Temporal_Goal_Normalization_Semantics
    Temporal_Definedness_Normalization.Temporal_Definedness_Normalization_Semantics
    Temporal_Precondition_Normalization.Temporal_Precondition_Normalization_Semantics
    Temporal_Definedness_Translation.Temporal_Definedness_Translation_Semantics
    Temporal_PDDL_Relaxation.Temporal_PDDL_Relaxation_Semantics
    Temporal_Reachability_Analysis.Temporal_Certified_Grounding_Semantics
    Temporal_Grounded_PDDL.Temporal_Grounded_PDDL
begin

section \<open>Temporal Grounding Pipeline for Numeric Problems\<close>

consts detype_temporal_prob :: "ast_temporal_problem \<Rightarrow> ast_temporal_problem"
consts degoal_temporal_prob :: "ast_temporal_problem \<Rightarrow> ast_temporal_problem"
consts explicate_def_temporal_prob :: "ast_temporal_problem \<Rightarrow> ast_temporal_problem"
consts split_temporal_prob :: "ast_temporal_problem \<Rightarrow> ast_temporal_problem"
consts def_translate_temporal_prob :: "ast_temporal_problem \<Rightarrow> ast_temporal_problem"
consts relax_temporal_prob :: "ast_temporal_problem \<Rightarrow> ast_temporal_problem"

consts dl_rules :: "ast_temporal_problem \<Rightarrow> 'a list"
consts const_names :: "ast_temporal_problem \<Rightarrow> 'b list"

consts ground_temporal_prob :: "ast_temporal_problem \<Rightarrow> fact list \<Rightarrow> plan_action list \<Rightarrow> ast_temporal_problem"
consts restore_ground_plan :: "plan_action list \<Rightarrow> (rat \<times> plan_action) list \<Rightarrow> (rat \<times> plan_action) list"
consts reconstruct_plan_norm :: "(rat \<times> plan_action) list \<Rightarrow> (rat \<times> plan_action) list"
consts restore_plan_def_translate :: "(rat \<times> plan_action) list \<Rightarrow> (rat \<times> plan_action) list"

subsection \<open>Intermediate Stage Layout\<close>

context ast_temporal_problem
begin

text \<open>Stage 1: Detyping\<close>
definition "P_TN \<equiv> detype_temporal_prob P"

text \<open>Stage 2: Goal Normalization\<close>
definition "P_GN \<equiv> degoal_temporal_prob P_TN"

text \<open>Stage 3: Definedness Explication\<close>
definition "P_DN \<equiv> explicate_def_temporal_prob P_GN"

text \<open>Stage 4: Precondition splitting (DNF)\<close>
definition "P_PN \<equiv> split_temporal_prob P_DN"

text \<open>Stage 5: Definedness Translation\<close>
definition "P_DT \<equiv> def_translate_temporal_prob P_PN"

text \<open>We refer to the normalized, definedness-translated temporal problem as P_T\<close>
abbreviation "P_T \<equiv> P_DT"

text \<open>Stage 6: Delete Relaxation\<close>
definition "P_R \<equiv> relax_temporal_prob P_T"

subsection \<open>End-to-End Pipeline Context\<close>

context
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes restrict_prob: "restrict_problem P"
      and cert: "dl_certified_model
                   (set (dl_rules P_R))
                   (set (const_names P_R)) M dc"
      and grounding_cert: "normalized_problem_rx.grounding_checks P_T M"
begin

definition "P_G_cert \<equiv> ground_temporal_prob P_T
  (normalized_problem_rx.cert_facts_of P_T M)
  (remdups (normalized_problem_rx.cert_ops_of P_T M))"

definition "reconstruct_plan_ground_cert \<pi>s \<equiv>
  reconstruct_plan_norm (restore_plan_def_translate
    (restore_ground_plan (remdups (normalized_problem_rx.cert_ops_of P_T M)) \<pi>s))"

subsection \<open>Pipeline Correctness Guarantees\<close>

theorem wf_ground_cert_problem:
  shows "ast_temporal_problem.wf_temporal_problem P_G_cert"
    and "ast_temporal_problem.normalized_prob P_G_cert"
    and "ast_temporal_problem.grounded_temporal_prob P_G_cert"
  sorry

theorem ground_cert_plan_valid_iff:
  shows "(\<exists>\<pi>s. valid_temp_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_temporal_problem.valid_temp_plan2 P_G_cert \<pi>s')"
  sorry

theorem ground_cert_plan_reconstruct:
  assumes "ast_temporal_problem.valid_temp_plan2 P_G_cert \<pi>s"
  shows "valid_temp_plan2 (reconstruct_plan_ground_cert \<pi>s)"
  sorry

end

end

end

