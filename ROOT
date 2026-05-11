chapter AFP

session Tree_Decomp_Grounding = HOL +
  description \<open>An executable grounder for PDDL tasks based on FastDownward system.\<close>
  options [timeout = 900]
  sessions
	"Classical_Planning"
	"HOL-Library"
	"Show"
	"Propositional_Proof_Systems"
  theories [document = false]
	"HOL-Library.Sublist"
	"HOL-Library.List_Lexorder"
	"HOL-Library.Char_ord"
	"HOL-Library.Monad_Syntax"
	"Show.Show_Instances"
	"Propositional_Proof_Systems.Sema"
	"Propositional_Proof_Systems.CNF"
    "Propositional_Proof_Systems.CNF_Formulas"
    "Propositional_Proof_Systems.CNF_Sema"
    "Propositional_Proof_Systems.CNF_Formulas_Sema"
  theories [document = false]
    Grounding_Utils
	Formula_Utils
	Nat_Show_Utils
	String_Utils
	PDDL_Sema_Supplement
	STRIPS_Sema_Supplement	
	PDDL_Checker_Utils
  theories
	DNF
	Graph_Funs
	Normalization_Definitions
	"Type_Normalization/Type_Normalization_Locales"
	"Type_Normalization/Type_Normalization"
	"Type_Normalization/Type_Normalization_Semantics"
	Goal_Normalization
	Precondition_Normalization
	PDDL_Relaxation
	Reachability_Analysis
	Grounded_PDDL
	PDDL_to_STRIPS
	Grounding_Pipeline
	Running_Example