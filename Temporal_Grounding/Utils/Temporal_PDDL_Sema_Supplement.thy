theory Temporal_PDDL_Sema_Supplement
  imports "Temporal_Planning.Temporal_Happening_Semantics"
    Grounding_Utils.Grounding_Utils Grounding_Common.Formula_Utils Grounding_Common.PDDL_Normalization
    Grounding_Common.PDDL_Sema_Supplement
begin

subsection \<open>Accessors for Temporal AST\<close>

abbreviation "ac_head \<equiv> ast_temporal_action_schema.head"
abbreviation "ac_name a \<equiv> ast_action_head.name (ac_head a)"
abbreviation "ac_params a \<equiv> ast_action_head.parameters (ac_head a)"

end
