# Architecture: the verified planning pipeline at a glance

One-page summary of the end-to-end pipeline (Helmert-2009-style grounding + SAT planning).
Details: session layout in `CLAUDE.md`, certification design in
[ARCHITECTURE_datalog_certification.md](ARCHITECTURE_datalog_certification.md). Last updated
2026-06-30 (two-tree + ladder refactor).

```text
 PDDL problem P
   │  normalize (plan-preserving, each stage its own session):
   │    detype → degoal → explicate definedness → split preconditions → translate definedness
   ▼
 P_T  (normalized: typed→unary preds, single goal atom, DNF preconds, numeric-free on the
   │   STRIPS path)
   ├────────────► relax (drop deletes) ──► P_R ──dl_program_of──► Nemo (untrusted)
   │                                        ▲                        │ model M + certificate (M, dc)
   │              verified kernel re-checks ┘ dl_certified_model + grounding checks
   ▼
 ground (wf_grounder, targets P_N = real deletes, pruned by the certified reachable set)
   │
   ▼
 grounded nullary PDDL ──as_strips──► STRIPS (AFP Verified_SAT_Based_AI_Planning format)
   │                                     │  ∀-step SAT encoding, external SAT solver (untrusted)
   │                                     ▼
   │                       decoded parallel plan ── re-checked, parallel→serial bridge
   ▼
 restore: STRIPS serial plan ──restore_prefix──► grounded plan ──reconstruct_plan_norm──►
 valid plan of the ORIGINAL problem P
```

## Stages and where they live

Theory names below carry the per-stage `Classical_` prefix (the classical half); the reusable half of
each stage lives in session `Grounding_<Stage>`. Session layout is in `CLAUDE.md`.

| Stage | Session / theory | Status |
| --- | --- | --- |
| Type / goal / precondition / definedness normalization | sessions `Classical_Type_Normalization`, `Classical_Goal_Normalization`, `Classical_Precondition_Normalization`, `Classical_Definedness_Normalization`, `Classical_Definedness_Translation` | proven plan-preserving |
| Delete relaxation (monotone reachability) | `Classical_PDDL_Relaxation` | proven |
| Reachability certificate kernel (PDDL-specific) | session `Classical_Reachability_Analysis`: `Classical_PDDL_Reachability_{Locales,Analysis,Certificate}.thy` (+ shared infra in `Classical_Reachability_Analysis.thy`) | 0 sorry |
| Generic positive-datalog certificate kernel + evaluator | session `Datalog_Certification` (`Grounding_Common/Datalog/`): `Datalog_Certificate.thy`, `Datalog_Evaluation.thy` | 0 sorry |
| Grounder | `Classical_Grounded_PDDL` | fully proven |
| STRIPS conversion + plan restoration + parallel→serial bridge | `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy` | proven |
| Pipeline wiring (numeric / STRIPS paths) | `Grounding_Pipeline_Numeric`, `Grounding_Pipeline_STRIPS` | green |
| Executable entry points | `Grounding_Pipeline_STRIPS_Executable.thy` (`ground_via_cert`), `Planner_STRIPS_Executable.thy` (`plan_by_cert`) | green, `plan_by_cert_sound` 0 sorry |
| Generic kernel executable refinement | `Datalog_Certificate_Code.thy` (`dl_certified_model_exec`) | 0 sorry |
| Code export + SML harness | `Planner_STRIPS_Export.thy`, `SMLCodebase/` | binary plans the running example |
| End-to-end demo | `Running_Example.thy` | green; in-Isabelle `(M, dc)` cert demo (`naive_cert`) |

## Trust story

Two untrusted oracles, both re-checked by verified kernels, so soundness never depends on them:

1. **Reachability (Nemo)** — input is the serialized `dl_program` (transport only); the returned
   model + certificate `(M, dc)` is re-checked (`dl_certified_model_exec` + `grounding_checks_exec`)
   against action clauses the kernel recomputes from the problem itself.
2. **SAT solver** — the decoded plan is re-checked with `is_serial_solution_for_problem`
   after the parallel→serial bridge.

Everything in between (normalization, grounding, STRIPS conversion, plan restoration) is
proven plan-preserving in both directions, so an accepted answer is a valid plan of the
original PDDL problem.
