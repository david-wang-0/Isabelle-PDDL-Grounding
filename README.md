# Verified Grounding of PDDL Tasks using Reachability Analysis (and Tree Decomposition)

A partially verified Isabelle implementation of the grounder in
[Helmert 2009](https://www.sciencedirect.com/science/article/pii/S0004370208001926), extended
into an end-to-end verified SAT-based planner: normalize → certify reachability (untrusted
datalog engine + verified certificate checker) → ground → convert to STRIPS → SAT-solve
(untrusted solver + verified re-check) → reconstruct a proven-valid plan of the original task.

## Dependencies

- **Formal-PDDL-Semantics** (sibling repo, sessions `Classical_Planning` /
  `Continuous_Planning`): the classical PDDL semantics used throughout (this supersedes the older
  AFP `AI_Planning_Languages_Semantics` entry), plus the PDDL parser reused by the SML harness
- [Verified_SAT_Based_AI_Planning](https://www.isa-afp.org/entries/Verified_SAT_Based_AI_Planning.html):
  propositional STRIPS (the output format) and the verified SATPlan encoding
- [Stratified_Datalog](https://www.isa-afp.org/entries/Stratified_Datalog.html): the datalog
  clause syntax of the reachability-oracle interface

## Layout

The repo is two mirrored trees: a reusable, Classical-free `Grounding_Common/` and the classical
grounder `Classical_Grounding/` built on top of it. Stage directories keep a plain name; the session
and theories inside the classical half carry a `Classical_` prefix, the reusable half does not.

```text
Repository
├── ROOTS, *.md - - - - - - - - - - - session list + docs (README, HANDOVER, ARCHITECTURE_*, GUIDANCE)
├── Grounding_Common/  - - - - - - - - REUSABLE, Classical-free tree (reusable by a future temporal grounder)
│   ├── Base/  - - - - - - - - - - - - Grounding_Light_Base (= HOL +) and Grounding_Base (frozen heavy heap)
│   ├── Utils/  - - - - - - - - - - - - PDDL-free utilities (Graph_Funs, Grounding_Utils, String_Utils, ...)
│   ├── Common/  - - - - - - - - - - - Formula_Utils, DNF, PDDL_Normalization, PDDL_Sema_Supplement
│   ├── Datalog/, Datalog_Graph/  - - - PDDL-free datalog certificate checker + evaluator (graph-lib isolated)
│   └── <stage>/  - - - - - - - - - - - the AST-agnostic half of each pipeline stage (session Grounding_<stage>)
├── Classical_Grounding/  - - - - - - - the CLASSICAL grounder, built on Grounding_Common/
│   ├── Base/  - - - - - - - - - - - - Grounding_Classical_Base and Grounding_Base_STRIPS (SAT lives only here)
│   ├── Utils/, Common/  - - - - - - - Classical_PDDL_Sema_Supplement, PDDL_Checker_Utils;
│   │                                  Classical_PDDL_Normalization, Numeric_Free
│   ├── <stage>/  - - - - - - - - - - - each stage's classical half: Classical_<stage>{_Locales,,_Semantics}
│   │                                  (Type/Goal/Precondition/Definedness_Normalization,
│   │                                   Definedness_Translation, PDDL_Relaxation, Reachability_Analysis, Grounded_PDDL)
│   ├── PDDL_to_STRIPS/  - - - - - - - conversion of the grounded task to STRIPS + plan restoration
│   ├── Grounding_Pipeline_{Numeric,STRIPS}.thy  pipeline wiring (with numerics / numeric-free to STRIPS)
│   ├── Code_Setup.thy, *_Executable.thy, Planner_{STRIPS_,}Export.thy  executable entry points + SML export
│   └── Running_Example{,_DFS,_Numeric}.thy  project demonstrations (STRIPS plan / DFS / numeric fluent)
└── SMLCodebase/  - - - - - - - - - - - the single SML codebase (top level): verified exported kernel (code/),
                                        untrusted oracle drivers (Nemo, SAT), the Formal-PDDL-Semantics parser
                                        bridge + grounded-PDDL printer, and the pddl_ground_planner_dfs CLI
```

## Status

The grounder core (`Grounded_PDDL/`), every normalization stage, the relaxation, the STRIPS
conversion, the pipeline wiring, and the executable planner soundness theorem
(`plan_by_cert_sound`: any plan returned is a valid plan of the original task, regardless of
the two untrusted oracles) are proven with `0 sorry`. The compiled binary plans the running
example and its output is confirmed by an independent PDDL plan validator.

A second, **numeric-fluent-retaining** grounding pipeline (`Numeric_Grounder.thy`) grounds a task
while keeping its real numeric preconditions/effects and function assignments (e.g. `(>= (fuel ?c) 1)`
and `(decrease (fuel ?c) 1)`) in the grounded PDDL, rather than compiling them away for STRIPS. Its
well-formedness (`numeric_ground_prob_wf`) and plan-preservation (`numeric_valid_classical_plan_iff`)
are proven `0 sorry`, and the binary's `ground` subcommand prints the fluent-retaining grounded PDDL.
See [ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md#numeric-grounding-pipeline-fluent-retaining).

The PDDL reachability-certificate development
(`PDDL_Reachability_{Locales,Analysis,Certificate}.thy`) is also `0 sorry`: reachability is proven
to be exactly the minimal model of the translated datalog program, and the `certified_pddl` locale
exposes the reachable-fact set to the grounder. Following the action-predicate elimination of
Corrêa et al., the datalog translation drops the auxiliary per-schema *action* predicate and
projects each schema's rules directly onto their add-effect atoms (`dl_clauses_of_action_clause`),
so the certified model is the set of reachable *facts* only — not reachable action instances. The
applicable ground operators are therefore reconstructed downstream by a fact-driven join over that
fact set (`cert_ops_of`, a proven-complete over-approximation), rather than read off the model. The
retired untrusted reachability engine was
deleted and replaced by the generic, verified `Datalog_Evaluation` evaluator (also `0 sorry`). The
generic certificate kernel is fully executable (`Datalog/Datalog_Certificate_Code.thy`:
`dl_certified_model_exec`), with `dl_founded` discharged by an ordered-cert linear scan.

The whole pipeline is wired end-to-end: the `Certified_Grounding*` bridge, both grounding pipelines,
and the executable layer (`ground_via_cert` / `plan_by_cert` / the SML export) are rewired onto the
generic `(M, dc)` certificate and verified; the compiled binary plans the running example. The
stronger foundedness story is also done: the `Datalog_Graph` session proves, purely graph-theoretically,
that a finite directed graph is acyclic iff it has a topological numbering, converts a certificate to
its support graph, and derives `acyclic (dl_dep_graph c) ⟹ dl_founded c` — wired into the kernel's
admissibility check (`dl_admissible_via_acyclic`). This gives a second, complementary way to discharge
foundedness: both are kept, the fast ordered-cert linear scan (`dl_founded_exec`) when the certificate
carries a trusted order, and the graph/acyclicity path when it does not. The one remaining piece is a
verified cycle-detecting DFS that *produces* the acyclicity witness. See `HANDOVER.md` for the precise inventory
and `ARCHITECTURE_pipeline.md` / `ARCHITECTURE_datalog_certification.md` for the design.
