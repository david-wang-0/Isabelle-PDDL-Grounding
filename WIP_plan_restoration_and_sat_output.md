# WIP — Concrete STRIPS→PDDL plan restoration + SAT-planner STRIPS output

Status: **Parts 1 & 2 DONE (2026-06-09, green); Part 3 still planning.** Prerequisite work was done:
`Grounding_Pipeline_STRIPS.thy` fully green (0 sorry/oops) — `strips_plan_iff_cert` (solvability
equivalence) and `strips_plan_sound_cert` (existence-of-valid-plan). Parts 1 & 2 now turn *existence*
into a *concrete, runnable* plan (`restore_prefix` + `reconstruct_pipeline_plan_cert`). Part 3
(connecting the pipeline's STRIPS output to the verified SAT planner) remains.

> **Implementation note (what actually shipped).** `restore_prefix` was placed in
> `ast_classical_problem` (not `strips_encodable_problem`) — it only needs `strips_model` /
> `restore_pddl_pa` / `execute_plan_action`, so keeping it in the base locale makes it an executable
> `fun` (auto `[code]`) without the extra `strips_encodable_problem` assumptions; the *proofs*
> (`restore_pddl_pa_witness`, `restore_prefix_sim`, `restore_prefix_valid`) live in
> `strips_encodable_problem`. The `find_index` correctness lemma went into `Common/Grounding_Utils.thy`
> as `find_index_Some_mem`. `ast_classical_problem.I ?P` and `ast_classical_problem.restore_prefix ?P`
> are the qualified forms used in the pipeline wiring.

The end-to-end goal:

```
PDDL task ─(our pipeline)─▶ STRIPS problem (as_strips, P_S_cert)
          ─(SAT planner)──▶ STRIPS serial solution ops          ← Part 3
          ─(restoration)──▶ valid PDDL plan of the ORIGINAL task ← Parts 1 & 2
```

---

## Why "restore plans from STRIPS" is non-trivial

The naive whole-plan restoration `restore_pddl_plan = map restore_pddl_pa`
(`Classical_PDDL_to_STRIPS.thy:131`) is **provably wrong**: `is_serial_solution_for_problem`
executes via `execute_serial_plan`, which *halts at the first non-applicable operator*
(`STRIPS_Semantics.thy:22`). So a valid STRIPS serial solution may carry **trailing operators that
are not enabled in PDDL** (the goal was already reached), and `valid_classical_plan2` rejects them
because it requires *every* action enabled in turn. Hence `valid_classical_plan2 (restore_pddl_plan ops)`
is FALSE in general, and we currently only have the *existence* form.

The fix is the **applicable prefix**: restore operators only up to the first non-applicable one.
That prefix is already constructed (existentially) inside `sim_serial_rev`
(`Classical_PDDL_to_STRIPS.thy:1626`). We just need to reify it as a function and re-state its proof
with the concrete witness.

---

## Part 1 — Concrete restoration  ✅ DONE (2026-06-09)
File: `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy`. `restore_prefix` landed in the
`ast_classical_problem` context (see implementation note above); the proofs in
`strips_encodable_problem`.

### 1a. The restoration function (executable)
```isabelle
fun restore_prefix
  :: "'a world_model \<Rightarrow> name strips_operator list \<Rightarrow> ast_classical_plan_action list"
  where
    "restore_prefix M [] = []"
  | "restore_prefix M (opr # ops) =
       (if is_operator_applicable_in (strips_model M) opr
        then restore_pddl_pa opr
               # restore_prefix (execute_plan_action (restore_pddl_pa opr) M) ops
        else [])"
```
Mirrors the case split in `sim_serial_rev`. Uses the existing `restore_pddl_pa`
(`…:129`), `is_operator_applicable_in`, `execute_plan_action`, `strips_model` — all executable.

### 1b. `restore_pddl_pa` is the canonical witness  *(small supporting lemma)*
`sim_serial_rev` obtains its action via `strips_op_has_pa` (`…:1610`) as
`SimplePlanAction (ac_name ac) []` where `opr = as_strips_op ac`. `restore_pddl_pa opr`
(`…:129`) is `SimplePlanAction (ac_name (actions D ! the (find_index opr strips_ops))) []`,
i.e. the *same* action provided `find_index`/`!` recovers `ac` (`strips_ops = map as_strips_op (actions D)`).
Prove:
```isabelle
lemma restore_pddl_pa_witness:
  assumes "opr \<in> set strips_ops"
  shows "wf_classical_plan_action (restore_pddl_pa opr) \<and> strips_pa (restore_pddl_pa opr) = opr"
```
Needs `find_index` correctness on `map as_strips_op (actions D)`; reuse `resolve_classical_action_schema_name`
and the `grounded_pa_nullary` / `wf_pa_refs_ac` machinery already used in `strips_op_has_pa`.
(If `as_strips_op` is not injective, `find_index` returns the first match — still a valid `ac` with the
same encoding, which is all we need.)

### 1c. Reify `sim_serial_rev` with the concrete witness
```isabelle
lemma restore_prefix_sim:
  assumes "\<forall>opr \<in> set ops. opr \<in> set strips_ops"
  shows "\<exists>M'. valid_classical_plan_alt M (restore_prefix M ops) M'
            \<and> strips_model M' = execute_serial_plan (strips_model M) ops"
```
Identical induction to `sim_serial_rev`, but the existential plan witness `\<pi>s` is replaced
throughout by the literal `restore_prefix M ops` (the `True` branch prepends `restore_pddl_pa opr`
and recurses on `execute_plan_action (restore_pddl_pa opr) M`; the `False` branch returns `[]`).
Discharge the two facts about `restore_pddl_pa opr` with 1b instead of the `obtain a` from
`strips_op_has_pa`. `execute_commute` + `applicable_enabled` carry over unchanged.

### 1d. Concrete soundness theorem (replaces the existence form)
```isabelle
theorem restore_prefix_valid:
  assumes "is_serial_solution_for_problem as_strips ops"
  shows "valid_classical_plan2 (restore_prefix I ops)"
```
Same shape as `restore_pddl_plan_valid` (`…:1672`): get `ops_mem`/`goaldom` from the assumption,
instantiate 1c at `M = I`, then `goal_bridge` + `valid_classical_plan2_alt`. `I` = the problem's
initial world model (as used in `restore_pddl_plan_valid`).

### 1e. Code export
Add `[code]` for `restore_prefix` (structurally executable). Optionally keep the old
existence theorem and `restore_pddl_plan`, or deprecate the latter in favour of `restore_prefix`.

---

## Part 2 — Wire restoration through the pipeline  ✅ DONE (2026-06-09)
File: `Grounding_Pipeline_STRIPS.thy` (the `cert` context, inside `context ast_classical_problem`).

The PDDL side is already concrete: `reconstruct_plan_ground_cert` (`Grounding_Pipeline_Numeric.thy:536`)
with `ground_cert_plan_reconstruct` (`…:585`):
`valid_classical_plan2 P_G_cert \<pi>s \<Longrightarrow> valid_classical_plan2 (reconstruct_plan_ground_cert \<pi>s)`
— a concrete reconstruction from a `P_G_cert` plan back to a plan of the **original** problem `P`.

We already interpret `strips_encodable_problem (P_G_cert cert)` (lemma `strips_encodable_P_G_cert`),
and `restore_prefix` lives in `ast_classical_problem`, so it is available for `P_G_cert cert`.
Shipped (green):
```isabelle
definition "reconstruct_pipeline_plan_cert ops \<equiv>
  reconstruct_plan_ground_cert cert
    (ast_classical_problem.restore_prefix (P\<^sub>G_cert cert)
       (ast_classical_problem.I (P\<^sub>G_cert cert)) ops)"

theorem strips_plan_reconstruct_cert:
  assumes "restrict_prob" "wf_classical_problem"
    and "is_serial_solution_for_problem P\<^sub>S_cert ops"
  shows "valid_classical_plan2 (reconstruct_pipeline_plan_cert ops)"
```
Proof: `P\<^sub>S_cert_def` ▸ `strips_encodable_problem.restore_prefix_valid[OF strips_encodable_P\<^sub>G_cert ser]`
▸ `ground_cert_plan_reconstruct[OF admissible_cert grounding_cert assms(1,2) v]`.
Chain: STRIPS solution of `P_S_cert = as_strips (P_G_cert cert)`
→ (Part 1d, in the `strips_encodable_problem (P_G_cert cert)` interpretation) a concrete valid plan
of `P_G_cert cert` → (`ground_cert_plan_reconstruct`) a concrete valid plan of the original `P`.

This **restores** the `reconstruct_pipeline_plan_cert` definition that was deleted earlier (it was
removed when the literal restore looked unprovable; the prefix makes it provable). Keep
`strips_plan_iff_cert` (solvability) and `strips_plan_sound_cert` (existence) as corollaries.

Effort: Parts 1+2 are a focused, low-risk session — the hard semantic lemma (`sim_serial_rev`,
`execute_commute`) already exists; this is reification + plumbing.

---

## Part 3 — Can the SAT planner output a STRIPS plan?

**Investigated the AFP `Verified_SAT_Based_AI_Planning` entry. Summary:**

### Verified-theory layer — YES, natively over STRIPS
`SAT_Plan_Base.thy` is a full SAT encoder/decoder on a `strips_problem`:
`encode_problem` (`\<Phi> \<Pi> t`, `…:207`) and `decode_plan` (`\<Phi>\<inverse> \<Pi> \<A> t`, `…:242`),
with soundness/completeness `encode_problem_parallel_sound` (`…:3481`) and complete (in
`SAT_Plan_Extensions.thy`, which also adds interfering-operator exclusion). So the SAT planner *does*
characterise STRIPS solutions — but as **parallel** plans (`is_parallel_solution_for_problem`,
`STRIPS_Semantics.thy:566`), a list of operator-*sets* per time step.

### Serial vs parallel — serialization bridge  ✅ DONE (2026-06-09)
Our pipeline targets **serial** solutions (`is_serial_solution_for_problem`, `…:46`), which is what
Parts 1–2 consume. The bridge is now proven in `Classical_PDDL_to_STRIPS.thy` (top level, green):

- `parallel_plan_fires s π` — the plan fires to completion from `s` (every step applicable +
  effect-consistent; `execute_parallel_plan` never short-circuits). Needed because the parallel and
  serial semantics only *halt-align* on singleton steps — that's why the AFP `flattening_lemma`
  (`…:2461`) is restricted to `∀ops. ∃op. ops = [op]`.
- `execute_parallel_plan_eq_serial_concat`: `parallel_plan_fires s π ⟹ (∀ops∈set π. non-interfering)
  ⟹ execute_parallel_plan s π = execute_serial_plan s (concat π)` — the state-level equality, by
  induction over `execute_parallel_operator_equals_execute_sequential_strips_if` (`…:2026`, per-step)
  + `execute_serial_plan_split` (`…:2136`, the `@`-split under applicable+non-interfering).
- `parallel_solution_imp_serial_solution`: `parallel_plan_fires (initial_of Π) π ⟹ (∀ops∈set π.
  non-interfering) ⟹ is_parallel_solution_for_problem Π π ⟹ is_serial_solution_for_problem Π (concat π)`
  — goal subset transfers via the equality, operator membership via the AFP `flattening_lemma_i`.

NOTE the AFP `flattening_lemma` only covers singleton steps; this generalizes to multi-op steps.
The `parallel_plan_fires` hypothesis is discharged downstream by SAT-decode soundness (the
operator/frame encoding forces every active operator to be applicable at its step) — that connection
is the remaining Part-3 code-export work.

### Executable / exported layer — NO direct STRIPS entry
The only `export_code` targets in the whole AFP entry are `encode` and `decode` in
`Solve_SASP.thy` (`…:848`, `…:852`), and both are **SAS+**-in / **SAS+**-plan-out
(`decode … = Inl (ast_problem.decode_abs_plan …)`, proven `ast_problem.valid_plan`). There is **no**
exported runnable function that takes a STRIPS problem and returns a STRIPS plan. The STRIPS-level
`SAT_Plan_Base.encode_problem`/`decode_plan` are verified but not set up for code export.

### Two routes to a runnable end-to-end planner
- **(ii) Export the STRIPS layer directly (recommended).** `export_code` `SAT_Plan_Base.encode_problem`
  / `decode_plan` (+ `SAT_Plan_Extensions` interference), drive an external SAT solver on the STRIPS
  CNF, decode a STRIPS *parallel* plan, serialize (bridge above), feed to Parts 1–2. Stays entirely
  in STRIPS — matches our `as_strips` / `is_serial_solution_for_problem` target. Expect code-export
  friction (non-executable pieces needing `code drop`, as in `WIP_running_example_certification.md`).
- **(i) Round-trip through the exported SAS+ `decode`.** Embed STRIPS → SAS+ (boolean variables via
  `range_of_strips`, `SAS_Plus_STRIPS.thy:110`), call the already-exported SAS+ `decode`, get a SAS+
  plan, map operators back to STRIPS (`strips_op_to_sasp` / `sasp_op_to_strips`). Reuses the exported
  entry + the existing DIMACS plumbing in `Solve_SASP` (`SASP_to_DIMACS`, `dimacs_model`, `max_var`),
  but the AFP bridge is oriented **SAS+→STRIPS** on **parallel** plans and the strips→sasp direction
  carries a `TODO` (`SAS_Plus_STRIPS.thy:85`) — so this needs the missing bridge direction + proofs.

**Recommendation:** route (ii) — keep the SAT integration in STRIPS, since that is exactly the format
the pipeline emits and the format Parts 1–2 restore from. Route (i) only if reusing the pre-exported
SAS+ `decode` proves cheaper than exporting the STRIPS encoder.

---

## Suggested order
1. ~~**Part 1** (restore_prefix + 1b–1d)~~ ✅ done — `Classical_PDDL_to_STRIPS.thy` + `Grounding_Utils.thy`.
2. ~~**Part 2** (pipeline wiring)~~ ✅ done — `Grounding_Pipeline_STRIPS.thy`.
3. ~~**Part 3 serial bridge** (parallel→serial)~~ ✅ done — `Classical_PDDL_to_STRIPS.thy`.
4. **Part 3 code export** (route ii) — largest, depends on the running-example code-setup work
   (`WIP_running_example_certification.md`, `TODO.md`). ← next; then wire SAT `decode_plan` →
   `parallel_solution_imp_serial_solution` → `restore_prefix` (discharging `parallel_plan_fires`).

Related: [[WIP_session_handoff]], [[WIP_running_example_certification]],
memory `project_restore_pddl_plan_existence`, `project_relaxation_refactor_pipeline_wip`.
