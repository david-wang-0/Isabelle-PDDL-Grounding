# Verified Grounding of PDDL Tasks using Reachability Analysis (and Tree Decomposition)

> **Development here has paused.** This grounder has been merged into
> [Formal-PDDL-Semantics](https://github.com/mabdula/Formal-PDDL-Semantics), under
> `PDDL_Grounding/`, with this repository's history preserved — that is where it is developed
> now. The PDDL semantics it is built on live there, so the merge turned three cross-repository
> component dependencies into ordinary in-repo session dependencies.
>
> This repository is kept as-is for reference and for the history; it is not archived, but new
> work should go to Formal-PDDL-Semantics.

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

The repo is mirrored trees over a shared spine: a reusable, Classical-free `Grounding_Common/`, the
classical grounder `Classical_Grounding/` built on top of it, and an in-progress `Temporal_Grounding/`
draft (grounding only, no STRIPS). Stage directories keep a plain name; the session and theories inside
a tree's half carry that tree's prefix (`Classical_`, `Temporal_`), the reusable half does not.

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
│   │                                  (+ Classical_<stage>_Num_Free where numeric-freeness is preserved)
│   │                                  (Type/Goal/Precondition/Definedness_Normalization, Definedness_Translation,
│   │                                   PDDL_Relaxation, Reachability_Analysis, Variable_Freeness, Grounded_PDDL)
│   ├── PDDL_to_STRIPS/  - - - - - - - conversion of the grounded task to STRIPS + plan restoration
│   ├── Grounding_Pipeline_{Numeric,STRIPS}.thy  pipeline wiring (with numerics / numeric-free to STRIPS)
│   ├── Code_Setup.thy, *_Executable.thy, Planner_{STRIPS_,}Export.thy  executable entry points + SML export
│   └── Running_Example{,_DFS,_Numeric}.thy  project demonstrations (STRIPS plan / DFS / numeric fluent)
├── Temporal_Grounding/  - - - - - - - - IN-PROGRESS temporal draft, same shape (grounding only, no STRIPS);
│                                        normalization ladder green, reachability/pipeline still sketched
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

A second, **numeric-fluent-retaining** grounding pipeline grounds a task while keeping its real numeric
preconditions/effects and function assignments (e.g. `(>= (fuel ?c) 1)` and `(decrease (fuel ?c) 1)`) in
the grounded PDDL, rather than compiling them away for STRIPS. It runs in two proven stages — the
variable-free instantiation (`Classical_Grounding/Variable_Freeness/`, `varfree_inst_prob`) and the
fact/fluent fold to a nullary problem (`fact_folder.fold_prob`, fluents becoming nullary functions such
as `fuel_c1_0`) — with well-formedness and plan-equivalence proven `0 sorry` for both. The binary's
`ground` subcommand prints the stage-1 fluent-retaining PDDL, `ground --folded` the fully grounded
product, and `ground --strips` the verified STRIPS problem. The STRIPS path is itself this pipeline plus
a numeric-freeness gate (the products are equal by `refl`).
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
admissibility check (`dl_admissible_via_acyclic`). Deciding that acyclicity executably is also done
(`0 sorry`), so foundedness now has **two complementary, verified re-checks** — both kept, both
producing byte-identical grounded output, and selectable in the SML binary as
`ground [--dfs|--topo]`: the fast ordered-cert linear scan (`dl_founded_exec`, `--topo`) when the
certificate carries a trusted order, and the linear whole-graph directed-cycle DFS sweep
(`dl_acyclic_dfs`, `--dfs`, `O(V+E)`). The one dominant cost turned out to be graph *construction* — the
support graph rebuilt `dl_cert_facts` (an `O(R²)` `remdups`) per relabelling — now fixed by a
proven-equal `[code]` refinement, so the acyclicity checks run in milliseconds on the hard-to-ground
set. The only remaining (optional) piece is a DFS that *produces* the topological numbering rather than
a bool. See `HANDOVER.md` for the precise inventory
and `ARCHITECTURE_pipeline.md` / `ARCHITECTURE_datalog_certification.md` for the design.
