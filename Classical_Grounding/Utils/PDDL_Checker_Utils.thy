theory PDDL_Checker_Utils
  imports "Classical_Planning.Classical_PDDL_Checker_Numeric"
    Classical_PDDL_Sema_Supplement
begin

text \<open>This theory used to wrap the generic Formal-PDDL-Semantics executable checker
  (\<open>ast_domain.STG\<close>, \<open>wf_domain'\<close>, \<open>en_exE2\<close>, \<open>valid_plan_fromE\<close>, \<dots>) in \<open>value\<close>-friendly
  abbreviations (\<open>wf_domain_x\<close>, \<open>valid_plan_x\<close>, \<dots>) for unit-test probes. That checker layer
  was renamed/specialized upstream (the generic \<open>ast_domain\<close>/\<open>ast_problem\<close> locales are gone;
  the executable checker now lives in \<open>ast_cont_domain\<close>/\<open>ast_cont_problem\<close> and the classical
  path goes through \<open>check_classical_plan\<close>), so those wrappers were removed. The generic
  error-revealing helper \<^const>\<open>reveal_error\<close> is AST-agnostic, so it now lives in the reusable
  \<open>Grounding_Utils.Grounding_Utils\<close> and is inherited here through \<open>Classical_PDDL_Sema_Supplement\<close>.\<close>

end
