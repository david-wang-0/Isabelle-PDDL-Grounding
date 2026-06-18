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
│                                    PDDL-free certificate checker + forward-chaining evaluator
│                                    (Datalog_Evaluation) for positive datalog
├── Type_Normalization/  - - - - - - \
├── Goal_Normalization/              |
├── Definedness_Normalization/      |  the normalization pipeline steps, each its own session
├── Precondition_Normalization/      |  (detype, degoal, definedness explication, DNF split,
├── Definedness_Translation/         |  definedness translation, delete relaxation)
├── PDDL_Relaxation/ - - - - - - - -/
├── Reachability_Analysis/ - - - - - PDDL reachability-certificate kernel: shared PDDL→datalog
│                                    infrastructure (Reachability_Analysis.thy) + the
│                                    PDDL_Reachability_{Locales,Analysis,Certificate}.thy
│                                    development (reachability = minimal model of the translated
│                                    program; certified_pddl grounding-input locale)
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

The PDDL reachability-certificate development
(`PDDL_Reachability_{Locales,Analysis,Certificate}.thy`) is also `0 sorry`: reachability is proven
to be exactly the minimal model of the translated datalog program, and the `certified_pddl` locale
exposes the reachable-fact set to the grounder. The retired untrusted reachability engine was
deleted and replaced by the generic, verified `Datalog_Evaluation` evaluator (also `0 sorry`). The
generic certificate kernel is fully executable (`Datalog/Datalog_Certificate_Code.thy`:
`dl_certified_model_exec`), with `dl_founded` discharged by an ordered-cert linear scan.

The whole pipeline is wired end-to-end: the `Certified_Grounding*` bridge, both grounding pipelines,
and the executable layer (`ground_via_cert` / `plan_by_cert` / the SML export) are rewired onto the
generic `(M, dc)` certificate and verified; the compiled binary plans the running example. The main
remaining work is the stronger Path-2 foundedness story (construct the rank inside the kernel from a
verified graph topological order / cycle check, so the certificate needs no trusted order — see
`PLAN_datalog_graph.md`). See `HANDOVER.md` for the precise inventory and `ARCHITECTURE_pipeline.md` /
`ARCHITECTURE_datalog_certification.md` for the design.
