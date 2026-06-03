chapter AFP

session Tree_Decomp_Grounding = Tree_Decomp_Grounding_Base +
  description \<open>An executable grounder for PDDL tasks based on FastDownward system.\<close>
  options [timeout = 900]
  sessions
	"Type_Normalization"
	"Definedness_Normalization"
	"Goal_Normalization"
	"Precondition_Normalization"
	"Definedness_Translation"
	"PDDL_Relaxation"
  theories
	Reachability_Analysis
	Grounded_PDDL
	PDDL_to_STRIPS
	Grounding_Pipeline
	Running_Example
