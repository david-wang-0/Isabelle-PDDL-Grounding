# Handover: verified PDDL grounding + SAT planning (Isabelle-PDDL-Grounding)

Full-repository summary and handover, written 2026-06-12 after a read-through of every theory,
ROOT, doc, and SML file. Companion one-pagers: [ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md)
(dataflow + trust story) and
[ARCHITECTURE_datalog_certification.md](ARCHITECTURE_datalog_certification.md) (certificate
design). Active WIP: [WIP_datalog_cert_bridge.md](WIP_datalog_cert_bridge.md). Index:
[WIP.md](WIP.md).

## What this repository is

A partially-verified Isabelle/HOL implementation of the Helmert-2009 PDDL grounder, extended
into a complete **verified SAT-based planner**: parse classical PDDL → normalize → certify
reachability (untrusted Nemo datalog engine + verified certificate checker) → ground →
convert to STRIPS (AFP `Verified_SAT_Based_AI_Planning` format) → SAT-solve (untrusted external
solver + verified model re-check) → reconstruct a **proven-valid plan of the original
problem** (`plan_by_cert_sound`, 0 sorry). The exported SML binary
(`SMLCodebase/bin/pddl_sat_planner`) plans the running example end-to-end (~6–9 s with z3),
and the Formal-PDDL-Semantics validator confirms its plans.

PDDL semantics come from the sibling **Formal-PDDL-Semantics** submodule (sessions
`Classical_Planning`, `Continuous_Planning` — the "pair world model" classical semantics);
STRIPS/SAT come from AFP `Verified_SAT_Based_AI_Planning`; datalog clause syntax from
AFP `Stratified_Datalog`.

## Session architecture (ROOTS order)

Two-layer frozen/editable split, then one session per pipeline stage:

| Session (dir) | Contents / role | Status |
| --- | --- | --- |
| `Tree_Decomp_Grounding_Base` | external deps only (FPS Classical/Continuous, STRIPS+SAT incl. `Solve_SASP`, `Propositional_Proof_Systems`, `Show`); build once, load as frozen jEdit heap | stable |
| `Tree_Decomp_Grounding_Common` (`Common/`) | editable shared layer: `Formula_Utils` (is_conj/un_and/pos-conj/relax_lit), `DNF` (`dnf_list` + semantics), `Graph_Funs` (`reachable_nodes`, `all_combos`/`chosen_from`), `String_Utils` (fresh-name machinery: `safe_prefix`, `distinct_strings_lit`), `Nat_Show_Utils` (`show_nat_inj`), `Grounding_Utils`, `PDDL_Sema_Supplement` (alt defs, `valid_classical_plan_alt`, `plan_action_enabled`, `ac_tsubst`, wf lemmas), `STRIPS_Sema_Supplement`, `PDDL_Checker_Utils` (reduced to `reveal_error`), `Normalization_Definitions` (restriction/typeless/normalized/relaxed/grounded locale ladder, `achievable`/`applicable`), `Numeric_Free` | 0 sorry |
| `Datalog_Certification` (`Datalog/`) | **standalone, PDDL-free** generic positive-datalog certificate checker `Datalog_Certificate.thy`: `dl_certificate` (Nemo ograph), `dl_ordered_check`/`dl_local_valid`/`dl_closure_check`/`dl_admissible`, inductive least-model `dl_derivable`, `dl_certified_model_correct` (certified facts = minimal model) | 0 sorry |
| `Type_Normalization` | detype: types → unary predicates (`detype_classical_prob`); `*2` locale hierarchy with `rewrites`-collapsed sublocales; `detyped_valid_iff` | 0 sorry |
| `Goal_Normalization` | degoal: fresh goal predicate + goal action (`degoal_prob`); `*3` hierarchy; `degoaled_valid_iff` + plan restore | 0 sorry |
| `Definedness_Normalization` | explicate PNE definedness as reflexive `numericEqAtm` conj-prefix (`explicate_def_prob`); `explicate_valid_iff` | 0 sorry |
| `Precondition_Normalization` | DNF split, one action per disjunct (`split_prob`, `*4` hierarchy); needs the definedness conj-prefix invariant; `split_valid_iff` + `restore_plan_split_valid` | 0 sorry |
| `Definedness_Translation` | numeric definedness → fresh `Defined_*` propositional predicates (`def_translate_prob`, `*_dt`); `def_translate_valid_iff` | 0 sorry |
| `PDDL_Relaxation` | delete relaxation (`relax_prob`, `*_rx` hierarchy with `px` sublocale): `relax_wf/normed/relaxes`, **`relax_achievables` / `relax_applicables`** (the P vs P_R bridge that makes certificate-grounding sound) | 0 sorry |
| `Reachability_Analysis` | see below | 8 sorries, all accounted for |
| `Grounded_PDDL` | the verified grounder core: `grounder`/`wf_grounder` locales (input: problem + achievable-facts/applicable-ops supersets), fresh nullary fact/op names, `ground_dom/prob_grounded`, `ground_dom/prob_wf`, `ground_enabled_iff`, `valid_classical_plan_iff` / `valid_classical_plan_left` + `restore_ground_pa` plan restoration | 0 sorry |
| `Tree_Decomp_Grounding` (top, `./ROOT`) | `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS`, `Grounding_Pipeline_Numeric`, `Grounding_Pipeline_STRIPS`, `Code_Setup`, `Grounding_Pipeline_STRIPS_Executable`, `Planner_STRIPS_Executable`, `Planner_STRIPS_Export` (`export_files` → `SMLCodebase/code/`), `Running_Example` | 0 sorry |

### Reachability_Analysis session in detail

- `Reachability_Analysis.thy` — the **untrusted** semi-naive engine (`action_clause` =
  `AClause name params pred-pre cond-pre adds`, `as_action_clause`, `a_clauses`,
  `init'`/`pseudo_init`, `consequence_of`, `satisfies_cond(s)`, `semi_naive_eval`). Its 4
  sorries (`semi_naive_aux` termination ×2, `found_facts_achievable`,
  `found_pactions_applicable`) are **deliberately left**: the engine is retired in favor of
  certificate checking and is not on any trusted path. `semi_naive_eval` is also not
  code-generable (numeric `valuation` poison) — do not try; route through certificates.
- `Reachability_Certificate.thy` — the heart of the trust story; after the 2026-06-12
  restructure it contains, in order:
  1. PDDL certificate kernel (locale `pddl_datalog = relaxed_problem`): `certificate`/`CNode`,
     `closure_check` (⊇, all soundness needs), `ordered_check` + `local_valid` (⊆, exactness),
     `admissible`, `cert_ops`; theorems `closure_sound`, `cert_ops_sound`.
  2. The PDDL→datalog serialization (`dl_id_of_term` … `dl_fact_clause`, `dl_rules`) — the
     same clause list `dl_program_of` hands to Nemo.
  3. Executable mirrors `closure_check_exec`/`ordered_check_exec`/`local_valid_exec`/
     `admissible_exec`/`cert_ops_exec` + `_eq`/`_sound` bridges to the locale originals.
  4. The generic-checker bridge: fail-closed `cert_to_dl`, structural correspondence,
     positivity, substitution/guard transfer, `dl_bridge_wf`, **proven**
     `dl_closure_imp_closure_exec`, **sorried** `dl_local_valid_imp_local_valid_exec`, main
     theorem `dl_admissible_imp_admissible_exec`.
  5. NEW: minimal-model relation (`achievable_eq_minimal_model`:
     `{f. achievable f} = {f. dl_derivable (dl_rules P) const_names f}` under `dl_bridge_wf`;
     both inclusions + `minimal_model_ops_requirement` sorried,
     `minimal_model_facts_requirement` assembled).
- `Certified_Grounding_Locales/Certified_Grounding/Certified_Grounding_Semantics.thy` —
  locale `certified_reachability = normalized_problem_rx + admissible_cert + grounding_cert`;
  `grounding_checks` (decidable wf/coverage of cert facts+ops, augmented with the un-relaxed
  ops' effect atoms); `all_facts_super`/`all_ops_super` via `relax_achievables`/`relax_applicables`;
  ends with `sublocale certified_reachability ⊆ wfg: wf_grounder P cert_facts' cert_ops'` —
  the grounder targets the **un-relaxed** P (grounding the relaxed P_R directly would be
  unsound; an earlier such Locale B was removed).

### Top-session theories in detail

- `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy` — grounded nullary PDDL → STRIPS with
  positive/negative variable pairs (`vpos`/`vneg`) + static `v⊤`/`v⊥`;
  `grounded_normalized_numeric_free_problem.wf_as_strips`; `strips_encodable_problem` with
  `valid_plan_iff`, `restore_pddl_plan_valid` (existence form — `execute_serial_plan` halts at
  the first non-applicable op, so the literal form is false), executable `restore_prefix` +
  `restore_prefix_valid`; parallel→serial bridge (`parallel_solution_imp_serial_solution`,
  generalizes AFP's singleton-only `flattening_lemma`; not needed at runtime since the
  Φ∀ encoding theorem covers it).
- `Grounding_Pipeline_Numeric.thy` — with-numerics pipeline composition: `P⇩X` (explicate) →
  `P⇩N` (split) → `P⇩T` (def-translate), compact per-stage facts, `P⇩G_cert` (conditional on
  `admissible_cert`/`grounding_cert`), `reconstruct_plan_norm`/`reconstruct_plan_ground_cert`,
  `ground_cert_plan_valid_iff`.
- `Grounding_Pipeline_STRIPS.thy` — numeric-free STRIPS specialization: `P⇩S_cert`,
  `wf_as_strips_cert`, `strips_plan_iff_cert` (solvability ⟺),
  `reconstruct_pipeline_plan_cert` + `strips_plan_reconstruct_cert` (STRIPS serial solution →
  concrete valid plan of the original P).
- `Code_Setup.thy` — all code-generation repairs (see Gotchas).
- `Grounding_Pipeline_STRIPS_Executable.thy` — wire-format `dl_program` + `dl_program_of`;
  `normalized_problem_rx`-side mirrors (`grounding_checks_exec` etc.); `ground_by_cert`,
  `ground_via_cert(')`, `reconstruct_plan_by_cert`, and the exec↔locale equality bridges
  (incl. `P_T_normalized_problem_rx_unconditional`, needed because the locale facts'
  exported forms carry cert-context hypotheses).
- `Planner_STRIPS_Executable.thy` — SAT half: `try_horizon` (Φ∀ encode → DIMACS via AFP
  `Solve_SASP`'s `cnf_to_dimacs` → oracle `g` → pull back → **executable model check**
  `𝒜 ⊨ Φ∀` → `decode_plan`), `sat_solve_strips` horizon loop, `plan_by_cert`, and
  **`plan_by_cert_sound`** (0 sorry) — the payoff theorem.
- `Planner_STRIPS_Export.thy` — `export_code` of the planner + oracle datatypes + AST
  constructors (incl. temporal ones the reused parser mentions) → `SMLCodebase/code/`.
- `Running_Example.thy` — Helmert-2009-style example; green `value`s through `P⇩T`/`P⇩R`,
  `dl_program_of`; plus an executable in-Isabelle untrusted oracle `naive_cert` (naive
  saturation emitting a Nemo-format certificate) with `value` probes for `admissible_exec`,
  `grounding_checks_exec`, `ground_by_cert`, `ground_via_cert`.

### SMLCodebase/ (untrusted glue around the exported kernel)

`Makefile` (`make export` regenerates the exported SML via `isabelle build -e`; `make`
compiles with MLton; parser + cmlib/parcom come from the sibling Formal-PDDL-Semantics via the
`FPS_PLANNING` MLB path var — nothing vendored). `pddl_sat_planner.sml` (CLI), `nemo_driver.sml`
(oracle `f`: dl_program → mangled `.rls` + dom guards → `nmo` IDB export + trace → ograph
toposort → `Cert`), `external_sat.sml` (oracle `g`: DIMACS → `$SAT_SOLVER`, default z3) /
`sat_solver.sml` (builtin DPLL, toy only), `pddl_to_isabelle.sml` + `planner_alias.sml`
(parser glue), `json_parse.sml`, `basics.sml`. `.mlb` order matters (`pddl_refactor.sml`'s
`open PDDL` shadows `int`/`not` — keep solvers before it). Examples under `examples/`.

## Proof status: the only 8 sorries

| Where | What | Disposition |
| --- | --- | --- |
| `Reachability_Analysis.thy:176,182` | `semi_naive_aux` termination | retired engine, off the trusted path; leave or delete the engine |
| `Reachability_Analysis.thy:345,349` | `found_facts_achievable` / `found_pactions_applicable` | same |
| `Reachability_Certificate.thy:1334` | `dl_local_valid_imp_local_valid_exec` | check-level bridge, plan in [WIP_datalog_cert_bridge.md](WIP_datalog_cert_bridge.md) §2 |
| `Reachability_Certificate.thy:1390` | `achievable_imp_dl_derivable` | minimal-model ⊆; mirror `closure_invariant`/`closure_step_adds` with `dl_derivable` closure |
| `Reachability_Certificate.thy:1395` | `dl_derivable_imp_achievable` | minimal-model ⊇; rule induction on `dl_derivable` |
| `Reachability_Certificate.thy:1429` | `minimal_model_ops_requirement` | from ⊆ + `enabled_clause_body` + `action_params_match_combos`, mirroring `cert_ops_sound` |

Everything else — every normalization stage, relaxation, grounder, STRIPS conversion, pipeline
wiring, executable mirrors, SAT half, `plan_by_cert_sound` — is 0 sorry. (Three `oops` in
`Common/Graph_Funs.thy`/`Grounding_Utils.thy` are abandoned scratch lemmas, not obligations.)

## ⚠ Unverified restructure (2026-06-12) — verify FIRST

The session split + bridge move was performed **on disk with the Isabelle MCP bridge down**;
nothing has been re-processed in jEdit yet, and the new `Datalog_Certification` session
requires a **jEdit restart** to resolve at all. Checklist for the next session:

1. Restart jEdit (do not save stale buffers of `Reachability_Certificate.thy`,
   `Grounding_Pipeline_STRIPS_Executable.thy`, or the deleted
   `Datalog/Datalog_Certificate_Bridge.thy` if prompted).
2. Verify (jedit-status skill, `fully_processed` + `consolidated`):
   `Datalog/Datalog_Certificate.thy` → `Reachability_Analysis/Reachability_Certificate.thy` →
   `Certified_Grounding*` → `Grounding_Pipeline_Numeric/STRIPS` → `Code_Setup` →
   `Grounding_Pipeline_STRIPS_Executable` → `Planner_STRIPS_Executable/Export` →
   `Running_Example`.
3. Expected breakage: `Stratified_Datalog` names (`Cls`, `PosLit`, `Eql`, …) are now visible
   to every theory above `Reachability_Certificate` (previously only to the executable tail);
   `id.Var`/`id.Cst` capture is pre-handled by the moved `hide_const`, other clashes get fixed
   on sight. Antiquotation slips in moved `text` blocks are possible.
4. Then fill the four live sorries (order: minimal-model ⊆, ops requirement, ⊇,
   local-validity transfer — the first two unlock retiring the per-check transfer), and
   discharge `dl_bridge_wf (relax_prob (P⇩T P))` for restricted well-formed `P`
   (WIP doc §3) to specialize the bridge to `ground_via_cert`'s checking site.

## Other open work (beyond the sorries)

- **End state of the certification story**: parse Nemo's ograph directly into the generic
  `dl_certificate`, export the generic checker, and obtain `admissible_exec` (or directly the
  reachability requirements via the minimal-model theorems) by theorem — retiring the
  duplicated PDDL-side check implementations. SML wiring sketch in
  [WIP_datalog_cert_bridge.md](WIP_datalog_cert_bridge.md) §Runnable wiring.
- **Upstreaming**: a `def_translate_code` bundle in `Definedness_Translation_Semantics.thy`
  (the only stage without one) and `padl_lit_code`/`distinct_strings_lit_eq[code]` into
  `Common/String_Utils.thy` — both currently patched in `Code_Setup.thy`.
- **Base-heap rebuild** (optional, saves ~10 min jEdit warmup): the `Tree_Decomp_Grounding_Base`
  ROOT already preloads `Solve_SASP`; rebuild the heap to freeze it.
- `Running_Example.thy`'s final subsection ("next step" text) predates `naive_cert` and the
  SML round-trip — stale comment, tidy when the file is next open.
- Optional cleanups: delete the retired `semi_naive` engine (or fence it), then
  `Reachability_Analysis.thy` becomes 0 sorry too.

## Gotchas (hard-won; keep in mind)

- **Code generation**: FPS shared-locale constants carry selector-pattern code equations from
  the continuous/temporal interpretations — `[[code drop]]` + re-add the foundational equation
  (`Code_Setup.thy` is the catalogue). `numeric_expression_valuation` is severed with a sound
  self-referential `Code.abort`. Locale defs **with assumptions** yield guarded `_def`s
  ("not an equation") — they need unconditional executable mirrors + equality-under-predicate
  lemmas (the established pattern, now in `Reachability_Certificate.thy` and
  `Grounding_Pipeline_STRIPS_Executable.thy`).
- **`is_serial_solution_for_problem` is not executable** (`⊆⇩m` over function states); the SAT
  path's only runtime check is the executable model check, serial-ness follows by theorem.
- **Qualify, don't hide**, around the `Solve_SASP` import (SAS+ `ast_problem` namespace):
  `strips_problem.operators_of`, `STRIPS_Semantics.is_serial_solution_for_problem`.
- **jEdit workflow**: verify via the MCP server (jedit-status), never batch-build by default;
  force tail processing with `explore`(find_theorems) at EOF; edit open buffers only via
  `mcp__isabelle__write_file`; `iq.iq` imports are dev-only and must never be committed.
- This is a **git submodule**: push with the push-ssh skill; never `git remote set-url`.

## Document map (after the 2026-06-12 cleanup)

- `HANDOVER.md` (this file) — summary + handover.
- `ARCHITECTURE_pipeline.md` — pipeline one-pager. `ARCHITECTURE_datalog_certification.md` —
  certification design. `WIP_datalog_cert_bridge.md` — the active WIP. `WIP.md` — WIP index.
- `README.md` — public-facing overview (refreshed). `GUIDANCE.md` — proof-style principles.
- `CLAUDE.md`/`GEMINI.md` — agent instructions (kept identical).
- `gigante_benchmarks_conditions_effects.md` — survey of the Gigante et al. temporal
  benchmark constructs (reference for future temporal/numeric work; not stale).
- `Documentation/thesis.pdf` — the project thesis.
- Removed as stale (recover from git history): `TODO.md` (items absorbed here),
  `WIP_executable_pipeline.md` (done; milestone history in git),
  `WIP_running_example_certification.md` (superseded by `naive_cert` + SMLCodebase),
  `Documentation/dependencies.md` (pre-refactor import graph).
