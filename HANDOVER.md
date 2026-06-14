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
| `Datalog_Certification` (`Datalog/`) | **standalone, PDDL-free** generic positive-datalog certificate checker. `Datalog_Sema_Supplement.thy` (locale hierarchy `datalog_prog` ⊂ `datalog_universe` ⊂ `positive_datalog_universe`; inductive least-model `datalog_prog.derivable`; AFP `⊨⇩l⇩s⇩t` bridge `derivable_iff_least_solution`) + `Datalog_Certificate.thy` (**index-free** `dl_certificate` = list of `DLRule` ground rules; **set-based** `dl_rule_valid`/`dl_closure_check`/`dl_founded`/`dl_admissible`; `dl_certified_model_correct` = certified facts = `datalog_prog.derivable`; `certified_model_is_least_solution` = AFP least solution). **2026-06-14 rework**: was Nemo ograph + indices + list program; cycle-detecting DFS for `dl_founded` + executable refinement + downstream `dl_derivable` re-point are TODO (see `Datalog/HANDOVER.md`) | 0 sorry |
| `Type_Normalization` | detype: types → unary predicates (`detype_classical_prob`); `*2` locale hierarchy with `rewrites`-collapsed sublocales; `detyped_valid_iff` | 0 sorry |
| `Goal_Normalization` | degoal: fresh goal predicate + goal action (`degoal_prob`); `*3` hierarchy; `degoaled_valid_iff` + plan restore | 0 sorry |
| `Definedness_Normalization` | explicate PNE definedness as reflexive `numericEqAtm` conj-prefix (`explicate_def_prob`); `explicate_valid_iff` | 0 sorry |
| `Precondition_Normalization` | DNF split, one action per disjunct (`split_prob`, `*4` hierarchy); needs the definedness conj-prefix invariant; `split_valid_iff` + `restore_plan_split_valid` | 0 sorry |
| `Definedness_Translation` | numeric definedness → fresh `Defined_*` propositional predicates (`def_translate_prob`, `*_dt`); `def_translate_valid_iff` | 0 sorry |
| `PDDL_Relaxation` | delete relaxation (`relax_prob`, `*_rx` hierarchy with `px` sublocale): `relax_wf/normed/relaxes`, **`relax_achievables` / `relax_applicables`** (the P vs P_R bridge that makes certificate-grounding sound) | 0 sorry |
| `Reachability_Analysis` | see below | 7 sorries (4 retired-engine + 3 minimal-model cores) |
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
- `Reachability_Certificate.thy` — the heart of the trust story. **2026-06-14 rewrite** (relate
  admissible datalog certificates to PDDL reachability; de-Nemo; drop the PDDL-direct executable
  checker; remove the PDDL certificate data structure). Reachability is now related to the
  *generic* `dl_certificate` of `Datalog_Certification` **purely semantically**. In order it
  now contains:
  1. Locale `pddl_datalog = relaxed_problem` — reusable PDDL reachability **helper lemmas only**
     (`is_obj_of_type_const_name`, `action_params_match_combos`, `res_inst_adds_eq_consequence`,
     `enabled_clause_body`, the `un_and`/`valuation` helpers). **Removed** (recover from git
     ≤ `118b66f`): the certificate datatype `certificate`/`CNode`, `cert_facts`/`cn_body`,
     `closure_check`/`closure_sound`, the Nemo-ograph `ordered_check`/`local_valid`/`admissible`,
     `cert_ops`/`cert_ops_sound`, and the `*_exec` executable mirrors.
  2. The PDDL→datalog serialization (`dl_id_of_term` … `dl_fact_clause`, `dl_rules`) + the
     translation wf bundle `dl_bridge_wf` — **kept** (the datalog translation of the problem,
     not Nemo-specific; it is the program whose minimal model the bridge relates to reachability).
  3. Minimal-model relation (section "PDDL reachability is the minimal model …", `context
     pddl_datalog`), re-pointed onto `datalog_prog.derivable (set const_names) (set (dl_rules P))`
     (the removed list-based `dl_derivable` is gone). **Proved**: `derivable_invariant`,
     `achievable_imp_dl_derivable`, `achievable_eq_minimal_model`, `minimal_model_facts_requirement`,
     and the capstone `certified_facts_eq_achievable`
     (`dl_certified_model (set (dl_rules P)) (set const_names) M dc ⟹ set M = {f. achievable f}`,
     via the generic `dl_certified_model_correct`). **2 sorries** (2026-06-14, down from 3) =
     `derivable_step_adds` and the `step` case of `dl_derivable_imp_achievable`. `derivable_init`
     is now **proven**; and four reusable helper lemmas were added to the `pddl_datalog` context to
     scaffold `derivable_step_adds`: `subst_id_dl_id_term` (the `subst_id`/`ac_tsubst` bridge —
     generic substitution on a translated id = PDDL `ac_tsubst` on the term),
     `ac_arg_in_const_names` (a matched action arg is an object name), `ac_tsubst_var_in_args`
     (a param variable substitutes to one of the action's args), and `dl_cond_rh_eval_guard`
     (a translated equality guard holds under the generic subst iff the PDDL equality condition
     is satisfied). With these, `derivable_step_adds` remains the assembly step: fire the action,
     read the clause `Cls p0 (map dl_id_of_term ts0) body` out of `dl_clauses_of_action_clause`
     (its body atoms come from `enabled_clause_body` + IH, guards from `dl_cond_rh_eval_guard`,
     var-coverage from `dl_bridge_wf` + `ac_tsubst_var_in_args`), and the clause survives the
     fail-closed drop because `enabled_clause_body`'s `satisfies_conds` contradicts any
     statically-unsatisfiable condition.
  - GREEN in jEdit (0 error / 0 warning; 2 `sorry` warnings; 427 cmds). The old **check-level
    bridge** (`cert_to_dl`,
    `dl_closure_imp_closure_exec`, `dl_local_valid_imp_local_valid_exec`,
    `dl_admissible_imp_admissible_exec`) was **excised** — the generic checker's 2026-06-14
    index-free/set-based rework made it the obsolete path; the semantic relation supersedes it.
  - ⚠️ **Downstream deliberately broken** (user: "ignore downstream theories for now"):
    `Certified_Grounding_Locales/Certified_Grounding{,_Semantics}.thy`,
    `Grounding_Pipeline_STRIPS_Executable.thy`, `Planner_STRIPS_Executable.thy`,
    `Planner_STRIPS_Export.thy`, `Running_Example.thy`, `Code_Setup.thy` reference the removed
    `cert_facts`/`cert_ops`/`closure_sound`/`admissible_exec`/`cert_ops_exec`/`dl_program_of` etc.
    They must be **rewired onto the generic-checker entry point** (`dl_certified_model` +
    `certified_facts_eq_achievable`) before the top session builds again.
  - 📋 **TODO — ops/applicable exactness** (semantic action model, user-chosen 2026-06-14; keep
    `dl_rules` as-is — heads stay = add-effects, **no** action-applicability predicates, no
    wire-format change). The exactness story (admissible certificate ⟹ exact w.r.t. relaxed PDDL)
    is the symmetric pair: *facts* are exact (`certified_facts_eq_achievable`, done); the *actions*
    side is **not yet stated**. The three supporting invariants are already in place:
    1. *"achievable fact = head of a fired ground rule"* — built into `datalog_prog.derivable.derive`
       (a derivable fact is exactly `subst_atom σ (the_lh cl)`); it is the content of
       `achievable_eq_minimal_model`.
    2. *"no founded rule refers to an unachievable/unapplicable thing"* — the generic checker's
       `dl_founded` (each certified fact has a justifying rule with body ⊆ certified facts, strictly
       lower rank ⇒ acyclic ⇒ genuinely derivable) + `dl_rule_valid` (each rule a real clause
       instance), both proved in `Datalog_Certificate`.
    3. *"admissible ⟹ facts exact"* — `dl_certified_model_correct` ∘ `achievable_eq_minimal_model`.
    The action being added: an action is **applicable iff one of its translated rules fires**
    (its identity lives in a rule *body*, not a head, since the translation emits one rule per
    add-effect). Lemmas to add (proofs reuse the kept helpers `enabled_clause_body`,
    `action_params_match_combos`, `res_inst_adds_eq_consequence`):
    - `applicable_iff_minimal_model`: `applicable (SimplePlanAction n args) ⟷ (∃cl ∈ a_clauses.
      cl_name cl = n ∧ args ∈ all_combos … ∧ satisfies_conds (cl_params cl) (cl_cond_pre cl) args
      ∧ (∀a ∈ cl_pred_pre cl. datalog_prog.derivable (set const_names) (set (dl_rules P))
      (instance of a)))` — equivalently body instances ⊆ minimal model = `{f. achievable f}`.
    - combined exactness: `dl_certified_model (set (dl_rules P)) (set const_names) M dc ⟹
      set M = {f. achievable f} ∧ {π. applicable π} = {π enumerable from a_clauses with body ⊆ set M
      ∧ guards}` — applicable actions read straight off the certified facts `M`, no `cert_ops`
      structure needed.
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

## Proof status: the only 6 sorries (2026-06-14)

| Where | What | Disposition |
| --- | --- | --- |
| `Reachability_Analysis.thy` (`semi_naive_aux` termination ×2) | retired-engine termination | retired engine, off the trusted path; leave or delete the engine |
| `Reachability_Analysis.thy` (`found_facts_achievable` / `found_pactions_applicable`) | retired-engine correctness | same |
| `Reachability_Certificate.thy:484` | `derivable_step_adds` | minimal-model ⊆ step core; **all four helper lemmas now in place** (`subst_id_dl_id_term`, `ac_arg_in_const_names`, `ac_tsubst_var_in_args`, `dl_cond_rh_eval_guard`) — remaining work is the assembly described in the Reachability_Certificate section above |
| `Reachability_Certificate.thy:559` | `dl_derivable_imp_achievable` (`step` case) | minimal-model ⊇; rule induction on `datalog_prog.derivable` — the fired clause is either a translated action clause (fire that action; positive-precondition body instances achievable by `step.IH`, guards hold) or a bodyless `init'` fact clause (achievable at the initial model) |

`derivable_init` and the helper lemmas around it are **proven** (was a sorry as of 2026-06-12).
`achievable_imp_dl_derivable`, `derivable_invariant`, `achievable_eq_minimal_model`,
`certified_facts_eq_achievable`, `minimal_model_facts_requirement` are all proven (they consume
the two remaining sorries). The old `dl_local_valid_imp_local_valid_exec` /
`minimal_model_ops_requirement` sorries no longer exist (the check-level bridge was excised).

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

## Planned refactor — split the certificate theory (user request, 2026-06-14)

`Reachability_Analysis/Reachability_Certificate.thy` currently carries **two distinct concerns**:
(a) relating PDDL reachability to the datalog **minimal model** (the `dl_rules` serialization +
`pddl_datalog` helper lemmas + `derivable_init`/`derivable_step_adds`/`derivable_invariant` +
`achievable_eq_minimal_model`), and (b) relating an admissible datalog **certificate** to PDDL
(`certified_facts_eq_achievable`, `minimal_model_facts_requirement`, which sit on top of (a) plus
the generic `dl_certified_model_correct`). The user wants these split into two theories:

- **`PDDL_Reachability_Analysis`** — concern (a): PDDL ⟷ datalog (minimal model).
- **`PDDL_Reachability_Certificate`** — concern (b): datalog certificate ⟷ PDDL.

This is a mechanical `isabelle-refactor`-style move once the two remaining sorries are filled
(do it after, so the split moves only green blocks). Naming TBD with the user — note the existing
files are `Reachability_Analysis.thy` (the retired untrusted engine) and
`Reachability_Certificate.thy`; decide whether `PDDL_Reachability_Analysis` renames/absorbs the
retired engine file or is a fresh theory carved out of the certificate file.

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
