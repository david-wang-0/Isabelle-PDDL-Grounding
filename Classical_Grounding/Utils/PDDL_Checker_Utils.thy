theory PDDL_Checker_Utils
  imports "Classical_Planning.Classical_PDDL_Checker_Numeric"
    Classical_PDDL_Sema_Supplement
begin

text \<open>This theory used to wrap the generic Formal-PDDL-Semantics executable checker
  (\<open>ast_domain.STG\<close>, \<open>wf_domain'\<close>, \<open>en_exE2\<close>, \<open>valid_plan_fromE\<close>, \<dots>) in \<open>value\<close>-friendly
  abbreviations (\<open>wf_domain_x\<close>, \<open>valid_plan_x\<close>, \<dots>) for unit-test probes. That checker layer
  was renamed/specialized upstream (the generic \<open>ast_domain\<close>/\<open>ast_problem\<close> locales are gone;
  the executable checker now lives in \<open>ast_cont_domain\<close>/\<open>ast_cont_problem\<close> and the classical
  path goes through \<open>check_classical_plan\<close>), so those wrappers were removed. Their only uses
  were already-commented-out probes in \<open>Running_Example.thy\<close>. What remains here are the
  generic error-revealing helpers.\<close>

(* this just directly displays the first error if applicable *)
fun reveal_error :: "(unit \<Rightarrow> char list \<Rightarrow> char list) + 'a \<Rightarrow> char list + 'a" where
  "reveal_error (Inl e) = Inl (e () [])" |
  "reveal_error (Inr x) = Inr x"

lemma reveal_no_error: "reveal_error x = Inr () \<longleftrightarrow> x = Inr()"
  by (cases x; simp)

end
