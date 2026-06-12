# Verified Grounding of PDDL Tasks using Reachability Analysis (and Tree Decomposition)

A partially verified Isabelle implementation of the grounder in
[Helmert 2009](https://www.sciencedirect.com/science/article/pii/S0004370208001926), extended
into an end-to-end verified SAT-based planner: normalize → certify reachability (untrusted
datalog engine + verified certificate checker) → ground → convert to STRIPS → SAT-solve
(untrusted solver + verified re-check) → reconstruct a proven-valid plan of the original task.

## Dependencies

- **Formal-PDDL-Semantics** (sibling submodule, sessions `Classical_Planning` /
  `Continuous_Planning`): the classical PDDL semantics used throughout, plus the PDDL parser
  reused by the SML harness
- [Verified_SAT_Based_AI_Planning](https://www.isa-afp.org/entries/Verified_SAT_Based_AI_Planning.html):
  propositional STRIPS (the output format) and the verified SATPlan encoding
- [Stratified_Datalog](https://www.isa-afp.org/entries/Stratified_Datalog.html): the datalog
  clause syntax of the reachability-oracle interface

## Layout

```text
Repository
├── ROOT, ROOTS  - - - - - - - - - - Isabelle session definitions (one session per stage)
├── Tree_Decomp_Grounding_Base/  - - external/library dependencies (prebuilt heap)
├── Common/  - - - - - - - - - - - - shared foundation: PDDL semantics supplement,
│                                    normalization definitions, formula/graph/string utilities
├── Datalog/ - - - - - - - - - - - - standalone session Datalog_Certification: generic,
│                                    PDDL-free certificate checker for positive datalog
├── Type_Normalization/  - - - - - - \
├── Goal_Normalization/              |
├── Definedness_Normalization/      |  the normalization pipeline steps, each its own session
├── Precondition_Normalization/      |  (detype, degoal, definedness explication, DNF split,
├── Definedness_Translation/         |  definedness translation, delete relaxation)
├── PDDL_Relaxation/ - - - - - - - -/
├── Reachability_Analysis/ - - - - - reachability certificate kernel (Nemo ograph format),
│                                    PDDL→datalog serialization, generic-checker bridge,
│                                    certificate→grounder plug-in
├── Grounded_PDDL/ - - - - - - - - - the verified grounder core (fully proven)
├── PDDL_to_STRIPS/  - - - - - - - - conversion of the grounded task to STRIPS + plan restoration
├── Grounding_Pipeline_Numeric.thy - pipeline wiring (with numerics, up to the grounded task)
├── Grounding_Pipeline_STRIPS.thy  - numeric-free specialization down to STRIPS
├── *_Executable.thy, Code_Setup.thy executable entry points (ground_via_cert, plan_by_cert)
├── Planner_STRIPS_Export.thy  - - - SML code export
├── SMLCodebase/ - - - - - - - - - - compiled planner binary + untrusted oracle drivers (Nemo,
│                                    external SAT solver), reusing the Formal-PDDL-Semantics parser
└── Running_Example.thy  - - - - - - a full project demonstration
```

## Status

The grounder core (`Grounded_PDDL/`), every normalization stage, the relaxation, the STRIPS
conversion, the pipeline wiring, and the executable planner soundness theorem
(`plan_by_cert_sound`: any plan returned is a valid plan of the original task, regardless of
the two untrusted oracles) are proven with `0 sorry`. The compiled binary plans the running
example and its output is confirmed by an independent PDDL plan validator.

Remaining `sorry`s are confined to the deliberately-unverified legacy reachability engine
(`Reachability_Analysis.thy`, retired in favor of certificate checking) and the in-progress
bridge between the generic datalog certificate checker and the PDDL reachability requirements
(`Reachability_Certificate.thy`). See `HANDOVER.md` for the precise inventory and
`ARCHITECTURE_pipeline.md` / `ARCHITECTURE_datalog_certification.md` for the design.
