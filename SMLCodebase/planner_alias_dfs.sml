(* Alias the DFS-founded exported structure under the names the shared driver
   glue expects (nemo_driver.sml / pddl_to_isabelle.sml reference
   `PDDL_SAT_Planner_Exported`; the parser pddl_refactor.sml references
   `Continuous_PDDL_Checker_Exported`). This lets the entire SMLCodebase driver
   be reused unchanged against the DFS export; only the entry points differ
   (`plan_by_cert_dfs` / `ground_via_cert_numeric_dfs`). *)
structure PDDL_SAT_Planner_Exported = PDDL_SAT_Planner_DFS_Exported
structure Continuous_PDDL_Checker_Exported = PDDL_SAT_Planner_DFS_Exported
structure TEMPORAL_PDDL_Checker_Exported = PDDL_SAT_Planner_DFS_Exported
