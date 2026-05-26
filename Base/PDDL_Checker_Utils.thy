theory PDDL_Checker_Utils
  imports "Classical_Planning.Classical_PDDL_Checker"
    PDDL_Sema_Supplement
begin

abbreviation "of_type_x D oT T \<equiv> of_type_impl (ast_domain.STG D) oT T"

abbreviation "wf_domain_x D \<equiv> ast_domain.wf_domain' D (ast_domain.STG D) (ast_domain.mp_constT D)"

abbreviation "wf_problem_x P \<equiv>
  let D = domain P in
  ast_problem.wf_problem' P (ast_domain.STG D) (ast_domain.mp_constT D) (ast_problem.mp_objT P)"

(* this just directly displays the first error if applicable *)
fun reveal_error :: "(unit \<Rightarrow> char list \<Rightarrow> char list) + 'a \<Rightarrow> char list + 'a" where
  "reveal_error (Inl e) = Inl (e () [])" |
  "reveal_error (Inr x) = Inr x"

abbreviation "enab_exec_x P pa s \<equiv>
  let D = domain P in reveal_error( 
  ast_problem.en_exE2 P (ast_domain.STG D) (ast_problem.mp_objT P) pa s)"

abbreviation "check_wf_domain_x D \<equiv> reveal_error (
  check_wf_domain D (ast_domain.STG D) (ast_domain.mp_constT D))"

abbreviation "valid_plan_x P \<pi>s \<equiv>
  let D = domain P;
      stg = ast_domain.STG D;
      obT = ast_problem.mp_objT P;
      i = ast_problem.I P in
  reveal_error (ast_problem.valid_plan_fromE P stg obT 1 i \<pi>s)"

(* these are useful for unit tests. You can just do e.g.
  \<open>lemma "ast_domain.wf_domain some_domain" by (intro wf_domain_intro) eval\<close> *)
lemmas wf_domain_intro = HOL.iffD1[OF ast_domain.wf_domain'_correct]
lemmas wf_problem_intro = HOL.iffD1[OF ast_problem.wf_problem'_correct]

lemma (in wf_ast_problem) i_basic: "wm_basic I"
  using wf_fmla_atom_alt wf_world_model_def wf_I wm_basic_def
  by metis

lemma reveal_no_error: "reveal_error x = Inr () \<longleftrightarrow> x = Inr()"
  by (cases x; simp)

(* usage:
  \<open>lemma "ast_problem.valid_plan my_problem my_plan"
  by (intro valid_plan_intro[OF wf_p1]) eval\<close> *)
lemma valid_plan_intro:
  assumes "ast_problem.wf_problem P" "valid_plan_x P \<pi>s = Inr()"
  shows "ast_problem.valid_plan P \<pi>s"
proof -
  from assms have "wm_basic (ast_problem.I P)" using wf_ast_problem.intro wf_ast_problem.i_basic by simp
  with assms have "ast_problem.valid_plan_from P (ast_problem.I P) \<pi>s"
    using ast_problem.valid_plan_fromE_return_iff' reveal_no_error by simp
  thus ?thesis using ast_problem.valid_plan_def by simp
qed



end