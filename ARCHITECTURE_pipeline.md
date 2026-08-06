# Architecture: the verified planning pipeline at a glance

One-page summary of the end-to-end pipeline (Helmert-2009-style grounding + SAT planning).
Details: session layout in `CLAUDE.md`, certification design in
[ARCHITECTURE_datalog_certification.md](ARCHITECTURE_datalog_certification.md). Last updated
2026-08-06 (fold plan-equivalence under numerics; STRIPS path rebased on the numeric pipeline).

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
| Numeric stage 1: variable-free instantiation | `Classical_Variable_Freeness` (`varfree.varfree_inst_prob`) | wf + plan-preservation proven, 0 sorry |
| Numeric stage 2: fact/fluent fold (fully grounded) | `Classical_Grounded_PDDL` (`fact_folder.fold_prob` at `wf_fact_folder_num` / `wf_grounder_num`) | wf + plan-equivalence proven, 0 sorry |
| STRIPS conversion + plan restoration + parallel→serial bridge | `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy` | proven |
| Pipeline wiring (numeric / STRIPS paths) | `Grounding_Pipeline_Numeric`, `Grounding_Pipeline_STRIPS` | green |
| Executable entry points | `Grounding_Pipeline_STRIPS_Executable.thy` (`ground_via_cert`/`_dfs`, `plan_by_cert_dfs`), `Grounding_Pipeline_Numeric_Executable.thy` (`instantiate_all_actions_dfs`) | green; `plan_by_cert_dfs_sound` 0 sorry |
| Generic kernel executable refinement | `Datalog_Certificate_Code.thy` (`dl_certified_model_exec`, ordered scan), `Datalog_Cycle_DFS.thy` (`dl_certified_model_dfs`, per-vertex DFS), `Datalog_Cycle_DFS_Global.thy` (`dl_certified_model_gdfs`, fast `O(V+E)` global-sweep DFS) — three verified foundedness re-checks | 0 sorry |
| Code export + SML harness | `Planner_Export.thy` (default, DFS), `Planner_STRIPS_Export.thy` (retained non-DFS); top-level `SMLCodebase/` | `pddl_ground_planner_dfs` (CLI `plan` / `ground [--dfs\|--topo\|--gdfs] [--folded\|--strips]`) |
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
 STAGE 1  varfree_inst_prob  (varfree_instantiator, targets P_T; each reachable op π instantiates to a
   │              NULLARY schema whose body is the term.CONST-lift of the instantiated ground action
   │              res_inst π — parameters are substituted, atoms are NOT propositionalised, so the
   │              numerics stay put)                       ⇒ numeric_P_V_cert
   ▼
 nullary-schema PDDL that RETAINS the fluent, with ground atoms and fuel(c) PNEs still present
   │
   │  STAGE 2  fold_prob  (wf_grounder_num / wf_fact_folder_num: re-index the ground atoms onto fresh
   │              nullary predicates and the ground fluents onto fresh nullary functions,
   │              fuel(c1) ↦ fuel_c1_0)                    ⇒ numeric_P_G_cert
   ▼
 FULLY GROUNDED nullary PDDL that RETAINS the fluent — STOPS here:
   (:functions (fuel_c1_0) …); each grounded drive keeps its (>= (fuel_c1_0) 1) guard +
   (decrease (fuel_c1_0) 1) effect, and init keeps (= (fuel_c1_0) 10)
```

**Why the two halves can disagree about numerics.** The lossiness lives where it is *sound*:

* **Definedness translation is plan-equivalent**, so it must keep `P_T` exact — it adds `def(f,args)`
  predicates but leaves the numeric comparisons, effects, and init assignments untouched.
* **Relaxation is already a one-directional over-approximation** (`relax_achievables`: real ⊆ relaxed),
  and a numeric effect contributes *zero* propositional facts, so dropping numerics in `relax_eff` /
  `relax_prob` leaves the datalog's derivable facts unchanged. This is the cheap, correct place to make
  `P_R` numeric-free for the datalog while `P_T` stays faithful.

**Verification (stage 1).** `varfree_inst_ac π n` lifts `res_inst π` via `term.CONST`; the linchpin
`varfree_inst_ac_inst` shows that instantiating the nullary schema at `[]` undoes the lift and recovers
`res_inst π` exactly — so the instantiated problem executes each op identically to `P_T` (same world model,
same numeric effects). That yields well-formedness (`varfree_inst_prob_wf`) and plan-preservation
(`varfree_valid_classical_plan_iff`), both `0 sorry`.

**Verification (stage 2).** The fold re-indexes atoms *and* fluents, so its coverage obligation is the
**numeric-permissive** `covered_num` (`Grounding_Common/Grounded_PDDL/Grounded_PDDL.thy`): a numeric atom
is admissible as long as every ground fluent in it is one of the reachable `fluents` (`facts_covered` /
`fluents_covered` are its two named halves, with `covered_numI/E/D` reaching element level). The folded
problem's well-formedness is `wf_fact_folder_num.fold_prob_wf_num`, lifted to the one-shot grounder as
`wf_grounder_num.ground_prob_wf_num` through the factorization `ground_prob_factors`, and to the pipeline
as `numeric_wf_ground_cert_problem`. **Plan-equivalence across the fold is proven under numerics too**
(`0 sorry`): the state relation renames the numeric component of `M` via `fold_nstate` (inverting
`ground_pne` on `fluents`) rather than carrying it unchanged, giving the semantic core
(`ground_numexp_val`, `ground_fmla_sem_num`, the `ground_neff_update_num` / `fold_action_update_num`
update commutations) and the transfer chain `fold_init_num` → `fold_enabled_iff_num` →
`fold_exec_right_num` → `fold_valid_classical_plan_iff_num` in
`Classical_Grounded_PDDL_Semantics.thy`. It is lifted through
`wf_grounder_num.valid_classical_plan_iff_num` to the pipeline
(`numeric_ground_cert_plan_valid_iff` / `_plan_reconstruct`) and to the executable entry points
(`ground_all_actions_*_e_plan_valid_iff` / `_plan_restore`). Stage 1 has the analogous
`varfree_inst_cert_plan_valid_iff` / `varfree_inst_cert_plan_reconstruct`.

**STRIPS from the numeric pipeline.** The propositional STRIPS path is now the *same* pipeline plus a
numeric-freeness gate rather than a parallel development: `numeric_P_G_cert = P_G_cert` holds by `refl`
under the seven-conjunct bridge `grounding_checks_of_num_free`, so the STRIPS block
(`numeric_P_S_cert` + wf / encodable / plan-iff / reconstruct) is a set of one-line rewrites over the
folded numeric product, with executable entry points `ground_strips_all_actions_{dfs,exec,gdfs}_e`
(gate `strips_fold_checks_exec`) exposed as CLI `ground --strips`.

**Locale plumbing.** The propositional grounder's `covered` re-check rejects numeric atoms outright, and
stage 1 needs none of the facts/coverage obligations, so `varfree_instantiator` is the **minimal**
locale (`wf_problem`, `ops_dist`, `all_ops`, `ops_wf` only). `grounder_inst` = `grounder` +
`varfree_instantiator` (no new assumptions) carries the factorization; `wf_grounder_cov` adds the
`covered`/`covered_num` coverage layer on top of it; `wf_grounder` re-asserts the *strong* `covered`
coverage plus the numeric-freeness assumptions for the propositional path, while `wf_grounder_num` adds
only `init_covered_num` (every init formula is `covered_num`) for the folded numeric path. On the
certificate side there are **three siblings**, none extending another (which would deduplicate the
shared `grounder` interpretation): `certified_reachability_num` (interprets `varfree_instantiator`, one
decidable check `numeric_grounding_checks`), `certified_reachability_fold_num` (interprets
`wf_grounder_num`, check `numeric_fold_checks`) and `certified_reachability` (interprets the full
`wf_grounder`, check `grounding_checks`) — so the propositional STRIPS pipeline keeps
`cr.wfg.ground_prob` verbatim.

**Executable + demo.** `instantiate_all_actions_{dfs,exec,gdfs}_e` (and their `_stream_e` twins, which
the shipped `ground` command calls) gate on the weaker `numeric_grounding_checks_exec` and return the
stage-1 instantiation; `ground_all_actions_{dfs,exec,gdfs}_e` gate on the strictly stronger
`numeric_fold_checks_exec` and return the fully grounded stage-2 problem (`_wf` corollaries prove it
well-formed). The shipped CLI's acceptance behaviour and output are unchanged.
`Running_Example_Numeric.thy` evaluates both stages in-Isabelle on a `fuel` fluent. The exported SML
binary's `ground` subcommand (top-level `SMLCodebase/`) prints the stage-1, fluent-retaining PDDL:
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
