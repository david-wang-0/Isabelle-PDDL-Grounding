chapter AFP

session Tree_Decomp_Grounding = Tree_Decomp_Grounding_Common +
  description \<open>An executable grounder for PDDL tasks based on FastDownward system.\<close>
  options [timeout = 900]
  sessions
	"Datalog_Certification"
	"Type_Normalization"
	"Definedness_Normalization"
	"Goal_Normalization"
	"Precondition_Normalization"
	"Definedness_Translation"
	"PDDL_Relaxation"
	"Grounded_PDDL"
	"Reachability_Analysis"
  directories
	"PDDL_to_STRIPS"
  theories
	"PDDL_to_STRIPS/Classical_PDDL_to_STRIPS"
	Grounding_Pipeline_Numeric
	Grounding_Pipeline_STRIPS
	Code_Setup
	Grounding_Pipeline_STRIPS_Executable
	Planner_STRIPS_Executable
	Planner_STRIPS_Export
	Running_Example
  export_files
	"SMLCodebase/code/PDDL_SAT_Planner_Exported.sml"
