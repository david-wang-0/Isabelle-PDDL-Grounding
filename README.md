# Verified Grounding of PDDL Tasks using Reachability Analysis (and Tree Decomposition)
A partially verified Isabelle implementation of the grounder in [Helmert 2009](https://www.sciencedirect.com/science/article/pii/S0004370208001926).

### Dependencies:
- [AI_Planning_Languages_Semantics](https://www.isa-afp.org/entries/AI_Planning_Languages_Semantics.html): a formalization of PDDL, the input format
- [Verified_SAT_Based_AI_Planning](https://www.isa-afp.org/entries/Verified_SAT_Based_AI_Planning.html): includes a formalization of propositional STRIPS, the output format

### Files
```
Repository
├── Documentation
│   └── thesis.pdf  - - - - - - - The thesis for this project
├── ROOT, ROOTS  - - - - - - - - Isabelle session definitions
├── Base/  - - - - - - - - - - - Shared foundation: PDDL semantics supplement, normalization
│                                definitions, formula/graph/string utilities
├── Type_Normalization/  - - - - \
├── Goal_Normalization/          |
├── Precondition_Normalization/  |  the normalization pipeline steps, each its own session
├── Definedness_Normalization/   |  (PDDL is detyped, goals/preconditions normalized, numeric
├── Definedness_Translation/     |  definedness explicated/translated, then relaxed)
├── PDDL_Relaxation/  - - - - - -/
├── Reachability_Analysis/ - - - Reachability analysis run directly on the PDDL task
│                                (semi-naive datalog-style engine) + reachability certificate
├── Grounded_PDDL/ - - - - - - - The verified grounder core: grounds a task to a nullary,
│                                purely-propositional task and proves the grounding correct
│                                (well-formed, grounded, and plan-preserving in both directions)
├── Grounding_Pipeline.thy - - - The central collection wiring the steps together (WIP)
├── PDDL_to_STRIPS.thy - - - - - Conversion of the grounded task to STRIPS, the output format
└── Running_Example.thy  - - - - A full project demonstration
```

### Status

Partially verified. The grounder core (`Grounded_PDDL/`) is fully proven on the classical
pair-world-model PDDL semantics — `0 sorry`. Its top-level results are
`ground_dom_grounded` / `ground_prob_grounded` (the output is grounded),
`ground_dom_wf` / `ground_prob_wf` (the output is well-formed), and
`valid_classical_plan_iff` / `valid_classical_plan_left` (a plan exists for the original task iff
one exists for the grounded task, and a grounded plan can be restored to the original). The
normalization steps are likewise verified; wiring them all together in `Grounding_Pipeline.thy`
and the STRIPS conversion in `PDDL_to_STRIPS.thy` are still in progress.
