# To dos

- [x] close the numeric-free grounding→STRIPS pipeline — `Grounding_Pipeline_STRIPS.thy` fully
      green (0 sorry/oops): `strips_plan_iff_cert` (solvability ⟺) + `strips_plan_sound_cert`
      (∃ valid plan) proven (2026-06-09).
- [~] **restore an actual plan from STRIPS + drive the SAT planner** — full plan in
      `WIP_plan_restoration_and_sat_output.md`.
  - [x] Part 1: concrete applicable-prefix restoration `restore_prefix` in `ast_classical_problem`
        (executable `fun`); supporting `find_index_Some_mem` (`Grounding_Utils`), `restore_pddl_pa_witness`,
        `restore_prefix_sim`, `restore_prefix_valid` proven in `strips_encodable_problem` (2026-06-09, green).
  - [x] Part 2: wired through the pipeline — `reconstruct_pipeline_plan_cert` +
        `strips_plan_reconstruct_cert` proven in `Grounding_Pipeline_STRIPS.thy` (composes
        `restore_prefix` with `reconstruct_plan_ground_cert`); returns a concrete valid plan of the
        ORIGINAL problem from a STRIPS serial solution (2026-06-09, green).
  - [~] Part 3: SAT-planner STRIPS output — verified layer exists (`SAT_Plan_Base`, parallel plans).
    - [x] parallel→serial bridge: `parallel_plan_fires` + `execute_parallel_plan_eq_serial_concat` +
          `parallel_solution_imp_serial_solution` in `Classical_PDDL_to_STRIPS.thy` (2026-06-09, green) —
          generalizes the AFP singleton-only `flattening_lemma` to multi-op steps via
          `execute_parallel_operator_equals_execute_sequential_strips_if`.
    - [ ] decide route (export STRIPS encoder, or round-trip the already-exported SAS+ `decode`); the
          exported AFP solver is SAS+-only today. Then connect SAT `decode_plan` → bridge → `restore_prefix`.
- [~] run the small pieces of code in the running example
      — `Running_Example.thy` GREEN through `P\<^sub>T`/`P\<^sub>R`; full details + next steps in
      `WIP_running_example_certification.md` (§ SESSION PROGRESS 2026-06-07).
  - [x] port `Running_Example` to the current API (was stale: `ast_problem`→`ast_classical_problem`,
        `detype_prob`→`detype_classical_prob`, …)
  - [x] code-gen setup so `value "my_P\<^sub>T"`/`"my_P\<^sub>R"` evaluate: per shared `domain_signature`/
        `problem_signature` constant, `code drop` the FPS cont/temporal per-interpretation code
        equations (selector-pattern, invalid) + re-add the foundational one; `[code]` for
        `def_translate_{dom,prob}`; `padl_lit_code` + `distinct_strings_lit_eq[code]`
  - [x] move the inline code-setup block into `Code_Setup.thy` (in the **top** session, not
        `Common/` — it `[code]`s `P⇩X/P⇩N/P⇩T`/`def_translate`; + `ROOT`; imported by
        `Running_Example` and `Grounding_Pipeline_Executable`) (2026-06-09).
  - [ ] upstream: add a `def_translate_code` bundle in `Definedness_Translation/…Semantics.thy`
        (it is the ONLY normalization step missing one); land `padl_lit_code` +
        `distinct_strings_lit_eq[code]` in `Base/String_Utils.thy`
  - [ ] note: `semi_naive_eval` is NOT code-runnable — its `valuation` pulls
        `numeric_expression_valuation → sin → suminf → Inf [filter]` (wellsortedness, `filter`
        not `enum`). The certificate checker (`closure_check`/`admissible`) bypasses it.
  - [~] make `closure_check`/`admissible`/`grounding_checks`/`ground_prob` executable (2026-06-09):
        the `numeric_expression_valuation → sin` poison is fixed via a `Code.abort` override in
        `Code_Setup.thy` (sound tautology), so `init'`/`a_clauses`/`dl_program_of` now evaluate;
        4 assumption-free checks `[code]`'d. STILL TODO: the 9 assumption-guarded checks
        (`pddl_datalog.{admissible,closure_check,ordered_check,local_valid,cert_ops}`,
        `normalized_problem_rx.{grounding_checks,cert_facts_of,cert_ops_of,extra_eff_atoms_of}`)
        have locale-predicate-guarded `_def`s ⇒ need unconditional executable mirrors.
  - [ ] produce the certificate (decided: full Nemo `ograph`, live from `ML ‹…›`) — Parts 2/3 of
        `WIP_running_example_certification.md`
- [~] **executable end-to-end pipeline `plan_by_cert f g P`** — `WIP_executable_pipeline.md`.
  - [x] `Code_Setup.thy` + `numeric_expression_valuation` `Code.abort` codegen fix (2026-06-09).
  - [x] `Grounding_Pipeline_Executable.thy`: `dl_program`/`dl_program_of` (✓ evaluates),
        `ground_by_cert`, `ground_via_cert :: (dl_program ⇒ certificate) ⇒ _ ⇒ _ strips_problem option`
        (typecheck green) (2026-06-09).
  - [ ] unconditional mirrors for the 9 guarded checks → `value`-test `ground_via_cert` → `export_code`.
  - [ ] Nemo SML driver `f` (serialize `dl_program` → `.rls`, run nemo, parse certificate).
  - [ ] Phase 2: export `encode_problem`/`decode_plan`; `sat_solve_strips` + `plan_by_cert` +
        soundness (`plan_by_cert f g t_max P = Some π ⟹ valid_classical_plan2 P π`); SAT SML driver `g`.
- [ ] fix the relevant proofs w.r.t. abstract semantics
  - [ ] comment out executable bits for now
