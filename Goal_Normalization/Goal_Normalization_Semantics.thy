theory Goal_Normalization_Semantics
  imports Goal_Normalization
begin

section ‹Goal Normalization Preserves Semantics›

context wf_ast_classical_problem3 begin

text ‹Resolving and instantiating the goal action yields a ground action
  whose precondition is the original goal and whose only add-effect is the
  goal predicate atom.›

lemma resinst_goal_ac:
  "(the o p3.res_inst) π⇩g = GroundAction (goal P) goal_effect"
  sorry

text ‹Forward direction: a typed valid plan extended with the goal action
  is valid in the degoaled problem.›

theorem valid_plan_right:
  assumes "valid_classical_plan2 πs"
  shows "p3.valid_classical_plan2 (πs @ [π⇩g])"
  sorry

text ‹Reverse direction: from a valid degoaled plan, dropping the suffix
  after the (first) goal action gives a valid typed plan.›

theorem valid_plan_left:
  assumes "p3.valid_classical_plan2 πs"
  shows "valid_classical_plan2 (restore_plan_degoal πs)"
  sorry

theorem degoaled_valid_iff:
  "(∃πs. valid_classical_plan2 πs) ⟷ (∃πs. p3.valid_classical_plan2 πs)"
  using valid_plan_left valid_plan_right by auto

end

subsection ‹ Code Setup ›

lemmas goal_norm_code =
  domain_signature.goal_pred_def
  domain_signature.goal_pred_decl_def
  ast_classical_domain.goal_ac_def
  ast_classical_problem.term_goal_def
  ast_classical_problem.degoal_dom_def
  ast_classical_problem.degoal_prob_def
declare goal_norm_code[code]

end

