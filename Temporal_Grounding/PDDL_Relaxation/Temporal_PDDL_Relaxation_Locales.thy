theory Temporal_PDDL_Relaxation_Locales
  imports "Temporal_Planning.Temporal_Abstract_Syntax"
    Grounding_Temporal_Common.Temporal_PDDL_Normalization
    Grounding_PDDL_Relaxation.PDDL_Relaxation
begin

locale normalized_problem_rx = normalized_problem

context normalized_problem_rx
begin

definition cert_facts_of :: "fact list \<Rightarrow> fact list" where
  "cert_facts_of M \<equiv> (if P = undefined then undefined else undefined)"

definition cert_ops_of :: "fact list \<Rightarrow> plan_action list" where
  "cert_ops_of M \<equiv> (if P = undefined then undefined else undefined)"

definition grounding_checks :: "fact list \<Rightarrow> bool" where
  "grounding_checks M \<equiv> (P = undefined)"

end

end
