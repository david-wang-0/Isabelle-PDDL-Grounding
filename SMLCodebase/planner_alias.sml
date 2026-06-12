(* Alias the exported planner structure under the names used by the parser in
   pddl_refactor.sml (copied from Formal-PDDL-Semantics).  This lets us reuse
   the parser unchanged for the SAT-based planner. *)
structure Continuous_PDDL_Checker_Exported = PDDL_SAT_Planner_Exported
structure TEMPORAL_PDDL_Checker_Exported = PDDL_SAT_Planner_Exported
