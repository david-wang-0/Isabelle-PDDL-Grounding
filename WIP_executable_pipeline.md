# WIP — Executable grounding pipeline + `plan_by_cert f g P`

Status: **Phase 1 in progress (2026-06-09).** Grounding-half architecture is in place and green;
`dl_program_of` runs end-to-end on the running example. Remaining Phase-1 work is precisely scoped
(executable mirrors for 9 assumption-guarded checks). Phase 2 (SAT) not started.

## Progress (2026-06-09)

Done & green (verified via `jedit-status` / actual `value` evaluation):
- **`Code_Setup.thy`** (NEW, top session `./ROOT`, imports `Grounding_Pipeline_Numeric`): shared
  code-gen setup factored out of `Running_Example` (which now imports it). Contains:
  - the FPS detype/`def_translate`/string `[code]` block (moved verbatim);
  - **the key unblock** — `numeric_expression_valuation` overridden with a self-referential
    `Code.abort` code equation (`Code.abort m (λ_. e) = e`, a tautology ⇒ sound). FPS
    `numeric_expression` has `SinExpr`/`CosExpr`/`ExpExpr` ⇒ `numeric_expression_valuation` pulls
    `sin → suminf → Inf [filter]` (`filter :: enum` wellsortedness); whole-program codegen compiles
    *every* `valuation` branch even for numeric-free problems, so this poisoned `init'`/
    `closure_check`/`cert_ops`/`grounding_checks`/`dl_program_of`. The abort severs the dep on `sin`;
    numeric-free runs never reach it. After this, `init' my_P⇩R` and `dl_program_of my_problem`
    evaluate (~3s each).
  - `[code]` for 4 assumption-free locale defs: `ast_classical_problem.{restrict_prob,
    wf_classical_problem}`, `ast_classical_domain.resolve_classical_action_schema`,
    `simple_action_instantiations.res_inst.simps`.
- **`Grounding_Pipeline_Executable.thy`** (NEW): `datatype dl_program = DLProgram (dl_clauses)
  (dl_init) (dl_consts)`; `dl_program_of P` (`= DLProgram (a_clauses R) (init' R) (const_names R)`
  at `R = relax_prob (P⇩T P)`, ✓ evaluates); `ground_by_cert P cert` (unconditional executable twin
  of `P⇩G_cert`'s assumption-free RHS); `ground_via_cert f P :: _ strips_problem option` (runtime
  `restrict_prob`/`wf_classical_problem`/`admissible`/`grounding_checks` re-checks, else `None`).
  All typecheck green.
- `Running_Example.thy` carries codegen probes with a dummy oracle `(λ_. Cert [])`.

**Code-equation gotcha found:** locale definitions in locales WITHOUT assumptions are directly
`declare …_def[code]`-able; but the cert/grounding checks live in `pddl_datalog = relaxed_problem`
and `normalized_problem_rx` (WITH assumptions), so their `_def` is guarded
(`pddl_datalog ?P ⟹ admissible ?P ?c ≡ …`) — "Not an equation", silently ignored by `[code]`.
The 9 affected: `pddl_datalog.{admissible, closure_check, ordered_check, local_valid, cert_ops}`,
`normalized_problem_rx.{grounding_checks, cert_facts_of, cert_ops_of, extra_eff_atoms_of}`.

**Immediate next:** write unconditional executable **mirrors** for those 9 (the `ground_by_cert`
pattern; bodies are visible in the "Not an equation" output), `[code]` them, route `ground_via_cert`
through them, prove `*_exec = locale.*` under the locale predicate (for soundness). Then
`ground_via_cert` evaluates → `export_code` → Nemo SML driver.

One correction to the plan below: `Code_Setup.thy` lives in the **top session**, not `Common/`
(it `[code]`-declares `P⇩X/P⇩N/P⇩T`/`def_translate`, which are in `Grounding_Pipeline_Numeric`).

## Context

The verified grounding→STRIPS pipeline is complete and green (`Grounding_Pipeline_STRIPS.thy`),
but it lives entirely inside `context ast_classical_problem` / `context fixes cert assumes
admissible_cert grounding_cert` — correctness is conditional on *assumed* certificate admissibility,
and nothing is exposed as a runnable end-to-end function. We want an **executable** entry point that:
parses a PDDL task, runs normalization+grounding, obtains the reachability **certificate from an
external Nemo oracle** `f`, re-checks it, converts to STRIPS, solves via an **external SAT oracle**
`g`, and reconstructs a concrete valid PDDL plan of the *original* task. Both oracles are untrusted
and their results are **re-checked** in verified code (`admissible`/`grounding_checks` for `f`;
`is_serial_solution_for_problem` for `g`), so soundness does not depend on trusting Nemo or the SAT
solver — the same certifying-kernel philosophy already used for the certificate.

Decisions taken with the user:
- **`plan_by_cert f g P`** — two oracles. `f :: dl_program ⇒ certificate` (Nemo), `g` the external
  SAT solver. Both untrusted, re-checked.
- `f` receives a **structured `dl_program` value** (not a pre-rendered string); the SML side
  serializes it to Nemo `.rls`, runs Nemo, parses the certificate.

## Current state (verified, reusable)

- Certificate datatype + checks: `Reachability_Analysis/Reachability_Certificate.thy`
  — `certificate = Cert (nodes: cert_node list)`, `CNode (cn_fact: facty) (cn_preds: nat list)`;
  `closure_check` / `ordered_check` / `local_valid` / `admissible` (line 200), `cert_facts`,
  `cert_ops` — all decidable (executability to be confirmed; expect `code drop` friction).
- DL program data already exists in `Reachability_Analysis/Reachability_Analysis.thy`:
  `action_clause = AClause (cl_name) (cl_params) (cl_pred_pre) (cl_cond_pre) (…add…)`,
  `a_clauses ≡ map as_action_clause (actions D)` (:90), `init' ≡ conc_unique pseudo_init (init P)`
  (:104), `const_names`, `consequence_of` (:85). These are the natural payload for `f`.
- STRIPS pipeline (conditional, proven): `Grounding_Pipeline_STRIPS.thy` — `P⇩S_cert` (:97),
  `reconstruct_pipeline_plan_cert` (:219), `strips_plan_reconstruct_cert` (:224) —
  `is_serial_solution_for_problem P⇩S_cert ops ⟹ valid_classical_plan2 (reconstruct_pipeline_plan_cert ops)`,
  under `restrict_prob`, `wf_classical_problem`, `admissible_cert`, `grounding_cert`.
- Restoration: `restore_prefix` + `reconstruct_pipeline_plan_cert` (executable `fun`s).
- Parallel→serial bridge (top level, green): `parallel_plan_fires`,
  `execute_parallel_plan_eq_serial_concat`, `parallel_solution_imp_serial_solution`
  in `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy`.
- Normalization chain `P → P⇩T` is executable with code-setup (see `Running_Example.thy`
  `value "my_P⇩T"`; TODO notes moving its inline code-setup block into a shared theory).
- PDDL parser: code-exported by **Formal-PDDL-Semantics**
  (`Classical_Planning/Classical_PDDL_Checker_Explicit_Export.thy` + `codeBase/`); reuse its
  parser, do not write a new one.
- SAT layer (AFP `Verified_SAT_Based_AI_Planning`): `SAT_Plan_Base.encode_problem` (`Φ Π t`),
  `decode_plan` (`Φ⁻¹ Π A t`) — verified over `strips_problem`, **not yet code-exported** (the heavy
  lift, flagged in `WIP_plan_restoration_and_sat_output.md` Part 3 route ii).

## Approach — two phases

### Shared code-setup (prerequisite)
Create `Common/Code_Setup.thy` holding the code-equation block currently inlined in
`Running_Example.thy` (FPS `code drop`s + re-adds, `def_translate_{dom,prob}` `[code]`,
`padl_lit_code`, `distinct_strings_lit_eq[code]`). Import it from `Running_Example` and the new
pipeline theory. This is the "same wall" both files hit.

### Phase 1 — executable grounding to STRIPS + Nemo oracle `f`
New theory **`Grounding_Pipeline_Executable.thy`** (top session `./ROOT`), imports
`Grounding_Pipeline_STRIPS` + `Common/Code_Setup` + the Formal-PDDL-Semantics parser export theory.

1. **`dl_program` payload + extractor.** Define a serializable
   `dl_program = (dl_clauses: action_clause list) (dl_init: facty list) (dl_consts: object list)`
   and an executable `dl_program_of P ≡ ⦇ a_clauses, init', const_names ⦈` at `P`'s relaxed-`P⇩T`
   interpretation (reuse the locale constants; they already have code). This is the value handed to `f`.
2. **Make the checks executable.** Confirm/repair code equations for `pddl_datalog.admissible`,
   `normalized_problem_rx.grounding_checks`, `cert_facts`, `cert_ops`, `ground_prob`, `as_strips`
   (note `value "ast_classical_problem.as_strips"` already probes this). `P⇩G_cert_def` is a
   *conditional* equation — do **not** rely on it for code; instead define an **unconditional
   executable** `ground_by_cert P cert ≡ grounder.ground_prob P⇩T (cert_facts' …) (cert_ops' …)`
   that computes directly, and prove it equals `P⇩G_cert cert` under the assumptions (soundness link
   only). Expect a round of `code drop`/`[code]` repairs.
3. **`ground_via_cert f P :: name strips_problem option`** (executable):
   ```
   ground_via_cert f P =
     (if ¬ restrict_prob P ∨ ¬ wf_classical_problem P then None
      else let cert = f (dl_program_of P) in
        if pddl_datalog.admissible (relax_prob P⇩T) cert
           ∧ normalized_problem_rx.grounding_checks P⇩T cert
        then Some (as_strips (ground_by_cert P cert)) else None)
   ```
   (qualified-at-`P` forms, matching the `Grounding_Pipeline_STRIPS` context).
4. **`export_code`** `ground_via_cert`, `dl_program_of`, the parser, and the cert datatype to SML
   (`file_prefix` under a new `Executable/` dir).

### Phase 2 — SAT oracle `g` + full plan (carries encode/decode export friction)
5. **Export `encode_problem` / `decode_plan`** (`SAT_Plan_Base`, + `SAT_Plan_Extensions`
   interference) for code. Largest sub-task (`code drop`s for non-executable pieces).
6. **`sat_solve_strips g t_max P_S :: (name strips_operator list) option`** (executable horizon loop):
   for `t = 1..t_max`: `cnf = encode_problem P_S t`; `A = g cnf`; `par = decode_plan P_S A t`; if
   `is_parallel_solution_for_problem P_S par` and `parallel_plan_fires (initial_of P_S) par` and all
   steps non-interfering → return `Some (concat par)`; else next `t`. `g` does DIMACS/Tseitin +
   solver invocation in SML (kept out of HOL), so `g :: <encoded formula> ⇒ <assignment>`.
7. **`plan_by_cert f g t_max P :: ast_classical_plan_action list option`**:
   ```
   plan_by_cert f g t_max P =
     Option.bind (ground_via_cert f P) (λP_S.
       Option.bind (sat_solve_strips g t_max P_S) (λops.
         if is_serial_solution_for_problem P_S ops
         then Some (reconstruct_pipeline_plan_cert cert ops) else None))
   ```
   (`cert` threaded from the `f` call; refactor `ground_via_cert` to also return the cert / its
   `reconstruct_pipeline_plan_cert` closure).
8. **Soundness theorem** (the payoff):
   `plan_by_cert f g t_max P = Some π ⟹ valid_classical_plan2 P π`.
   Proof: the `Some` branch witnesses `restrict_prob`, `wf_classical_problem`, `admissible_cert`,
   `grounding_cert`, and `is_serial_solution_for_problem P⇩S_cert ops`; apply the existing
   `strips_plan_reconstruct_cert`. The serial re-check (step 7) + `parallel_solution_imp_serial_solution`
   (step 6) discharge its hypothesis. No trust in `f`/`g`.

### SML glue (hand-written, under `Executable/`)
- **Nemo driver** `f`: serialize `dl_program` → Nemo `.rls` (one rule per `action_clause`: head =
  consequence atom, body = `cl_pred_pre` + `cl_cond_pre` guards; `dl_init` as facts), run the `nemo`
  binary, read its certificate output, parse the ograph into `Cert [CNode …]`. Fact (de)serialization
  follows the `facty = Atom (predAtm pred (object list))` shape. Format reference:
  `WIP_nemo_certificate_format.md` + the Lean `CertifyingDatalog` reference checker.
- **SAT driver** `g`: encoded formula → DIMACS (Tseitin) → external solver (e.g. minisat) → model →
  assignment for `decode_plan`. (Phase 2.)
- A `.mlb`/build entry wiring exported code + drivers + the Formal-PDDL-Semantics parser, analogous
  to the superproject's `ML/pddl_parser/` setup.

## Files

- **New:** `Grounding_Pipeline_Executable.thy`, `Common/Code_Setup.thy`, `Executable/` (SML drivers +
  build file). ROOT updates: `./ROOT` (+ AFP SAT sessions, parser session), `Common/ROOT` if
  Code_Setup lands there.
- **Touch (code equations / `[code]` only, no semantic change):**
  `Reachability_Analysis/Reachability_Certificate.thy` (executability of `admissible`/`cert_ops`),
  possibly `Certified_Grounding*.thy` (`grounding_checks` code), `Grounding_Pipeline_*` (unconditional
  `ground_by_cert` twin).

## Verification

- After each `[code]`/`code drop` repair, verify via the **jedit-status** skill (not a batch build) —
  must report `fully_processed: true` + `consolidated: true`.
- `value "dl_program_of my_problem"` and `value "ground_via_cert (λ_. my_hardcoded_cert) my_problem"`
  in a scratch section of `Running_Example.thy` to confirm the grounding half runs end-to-end before
  touching SAT.
- Phase 2: `value`-test `sat_solve_strips` with a stub `g` returning a known model; then exercise the
  exported SML with the real Nemo + SAT binaries on `examples/`.
- Final: `plan_by_cert_sound` proven (0 sorry) and the exported planner produces a plan that the
  Formal-PDDL-Semantics plan checker accepts on a sample task.

## Risks / open

- **Biggest risk: `encode_problem`/`decode_plan` code export** (Phase 2, step 5) — verified but never
  exported; the WIP predicts `code drop` friction. Phase 1 is unaffected and ships independently.
- `admissible`/`grounding_checks` executability unconfirmed — `semi_naive_eval` is deliberately *not*
  code-runnable, but the cert checks avoid it; still, confirm no non-executable dependency sneaks in.
- Nemo certificate on-the-wire format must match `cert_node`/`cn_preds` exactly (predecessor *indices*,
  `j < i`); validated by `ordered_check`/`local_valid` at runtime, so a format mismatch fails closed
  (returns `None`) rather than unsoundly.

Related: `WIP_plan_restoration_and_sat_output.md`, `WIP_reachability_datalog.md`,
`WIP_nemo_certificate_format.md`, `WIP_running_example_certification.md`, `TODO.md`.
