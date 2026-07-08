# Architecture: the verified planning pipeline at a glance

One-page summary of the end-to-end pipeline (Helmert-2009-style grounding + SAT planning).
Details: session layout in `CLAUDE.md`, certification design in
[ARCHITECTURE_datalog_certification.md](ARCHITECTURE_datalog_certification.md). Last updated
2026-07-08 (added the numeric-fluent-retaining grounding pipeline).

There are **two grounding paths** sharing the same normalize → relax → certify front half: the
**STRIPS planning path** (below), which compiles numerics away and grounds to nullary propositional
STRIPS for SAT planning; and the **[numeric grounding pipeline](#numeric-grounding-pipeline-fluent-retaining)**,
which *retains* numeric fluents in the grounded PDDL. The diagram below is the STRIPS path.

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
| Grounder (propositional) | `Classical_Grounded_PDDL` | fully proven |
| Numeric-fluent-retaining grounder | `Numeric_Grounder.thy` (`numeric_ground_prob`) | wf + plan-preservation proven, 0 sorry |
| STRIPS conversion + plan restoration + parallel→serial bridge | `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy` | proven |
| Pipeline wiring (numeric / STRIPS paths) | `Grounding_Pipeline_Numeric`, `Grounding_Pipeline_STRIPS` | green |
| Executable entry points | `Grounding_Pipeline_STRIPS_Executable.thy` (`ground_via_cert`/`_dfs`, `plan_by_cert_dfs`), `Grounding_Pipeline_Numeric_Executable.thy` (`ground_via_cert_numeric_dfs`) | green; `plan_by_cert_dfs_sound` 0 sorry |
| Generic kernel executable refinement | `Datalog_Certificate_Code.thy` (`dl_certified_model_exec`), `Datalog_Cycle_DFS.thy` (`dl_certified_model_dfs`, verified DFS foundedness) | 0 sorry |
| Code export + SML harness | `Planner_Export.thy` (default, DFS), `Planner_STRIPS_Export.thy` (retained non-DFS); top-level `SMLCodebase/` | `pddl_ground_planner_dfs` (CLI `plan` / `ground`) |
| End-to-end demos | `Running_Example.thy`, `Running_Example_DFS.thy`, `Running_Example_Numeric.thy` | green; in-Isabelle `(M, dc)` cert demos (`naive_cert`) |

## Numeric grounding pipeline (fluent-retaining)

The STRIPS path compiles numerics away (definedness normalization + translation turn every numeric
condition into a propositional `def(f,args)` predicate) so it can ground to a purely propositional task.
The **numeric grounding pipeline** instead **retains the real numeric fluents** — `(>= (fuel ?c) 1)`
guards, `(decrease (fuel ?c) 1)` effects, `(= (fuel c) 10)` init assignments, and `(:functions …)`
declarations — in the grounded output. It shares the whole normalize → relax → certify front half and
diverges only at the grounder; it stops at grounded PDDL (no STRIPS conversion, no SAT for the numeric task).

```text
 PDDL problem P  with numeric fluents:  (>= (fuel ?c) 1)   (decrease (fuel ?c) 1)   (= (fuel c) 10)
   │  SAME normalization, but definedness-translation KEEPS P_T's real numerics
   │  (it only ADDS propositional def(f,args) predicates/facts for the datalog's benefit)
   ▼
 P_T  numerics RETAINED: the (decrease …) effects, (>= …) guards and (= …) init all survive verbatim
   ├──────────► relax ──► P_R  numeric-FREE (so the reachability datalog stays legal):
   │                       │     • relax_lit maps numeric comparison atoms to ¬⊥
   │                       │     • relax_eff / relax_prob drop numeric effects + init assignments
   │                       └─dl_program_of─► Nemo (untrusted) ─► (M, dc), re-checked as on the STRIPS path
   ▼
 numeric_ground  (wf_grounder_num, targets P_T; each reachable op π grounds to a NULLARY schema whose
   │              body is the term.CONST-lift of the instantiated ground action res_inst π — parameters
   │              are substituted, atoms are NOT propositionalised, so the numerics stay put)
   ▼
 grounded nullary PDDL that RETAINS the fluent — STOPS here:
   (:functions (fuel …)); each grounded drive keeps its (>= (fuel c) 1) guard + (decrease (fuel c) 1) effect
```

**Why the two halves can disagree about numerics.** The lossiness lives where it is *sound*:

* **Definedness translation is plan-equivalent**, so it must keep `P_T` exact — it adds `def(f,args)`
  predicates but leaves the numeric comparisons, effects, and init assignments untouched.
* **Relaxation is already a one-directional over-approximation** (`relax_achievables`: real ⊆ relaxed),
  and a numeric effect contributes *zero* propositional facts, so dropping numerics in `relax_eff` /
  `relax_prob` leaves the datalog's derivable facts unchanged. This is the cheap, correct place to make
  `P_R` numeric-free for the datalog while `P_T` stays faithful.

**Verification.** `numeric_ground_ac π n` lifts `res_inst π` via `term.CONST`; the linchpin
`numeric_ground_ac_inst` shows that instantiating the nullary schema at `[]` undoes the lift and recovers
`res_inst π` exactly — so the grounded problem executes each op identically to `P_T` (same world model,
same numeric effects). That yields well-formedness (`numeric_ground_prob_wf`) and plan-preservation
(`numeric_valid_classical_plan_iff`), both `0 sorry`.

**Locale plumbing.** The propositional grounder's `covered` re-check rejects numeric atoms outright, and
the numeric grounder needs none of the facts/coverage obligations, so `wf_grounder_num` is the **minimal**
locale (`wf_problem`, `ops_dist`, `all_ops`, `ops_wf` only); `wf_grounder` adds the coverage/facts and
numeric-freeness assumptions for the propositional path. On the certificate side,
`certified_reachability_num` (interprets `wf_grounder_num`, discharging only the single decidable check
`numeric_grounding_checks` = "every certified op is a well-formed plan action") is a **sibling** of
`certified_reachability` (interprets the full `wf_grounder`) — neither extends the other, so the
propositional STRIPS pipeline keeps `cr.wfg.ground_prob` verbatim.

**Executable + demo.** `ground_via_cert_numeric_dfs` gates on the weaker `numeric_grounding_checks_exec`
(so a task whose reachable ops still carry numeric effects passes) and calls the fluent grounder;
`Running_Example_Numeric.thy` evaluates the whole chain in-Isabelle on a `fuel` fluent. The exported SML
binary's `ground` subcommand (top-level `SMLCodebase/`) prints the grounded, fluent-retaining PDDL:
`bin/pddl_ground_planner_dfs ground examples/running_example_numeric/{domain,problem}.pddl`.

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
