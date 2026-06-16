# WIP — Reachability_Certificate cleanup + locale reorganisation

Handover, 2026-06-16. The reverse-direction `sorry` is **done**: `Reachability_Certificate.thy`
is `0 sorry / 0 errors`. The minimal-model relation is fully proved in both directions
(`achievable_eq_minimal_model`, `certified_facts_eq_achievable`). This doc is the *next* phase:
clean up the file and put the proofs in the locales that actually satisfy their assumptions, then
add a `certified_pddl` locale. Do the steps **in order** — each leaves the file green.

Companion: `HANDOVER.md` (repo overview), `ARCHITECTURE_datalog_certification.md`. The old
`WIP_reverse_direction.md` is now historical (the sorry it tracked is closed).

## Current locale landscape (after the 2026-06-16 work)

- `pddl_datalog = relaxed_problem` (`Reachability_Certificate.thy`). **`relaxed` was strengthened**
  (`Common/Normalization_Definitions.thy`) to combine precondition- *and* delete-relaxation:
  - `relaxed_action a ⟷ is_pos_conj (ac_pre a) ∧ dels (ac_eff a) = []` (global def) with
    `[intro]`/`[dest]` rules `relaxed_actionI` / `relaxed_action_preD` / `relaxed_action_delD`;
  - `relaxed_dom ≡ normalized_dom ∧ (∀a∈actions D. relaxed_action a)` and
    `relaxed_prob ≡ normalized_prob ∧ is_pos_conj (goal P) ∧ relaxed_dom`, each with
    `relaxed_domI`/`relaxed_dom_normedD`/`relaxed_dom_actionD` and
    `relaxed_probI`/`relaxed_prob_normedD`/`relaxed_prob_goalD`/`relaxed_prob_actionD`
    ([intro]/[dest], reach down to `relaxed_action`).
  - **Therefore `pddl_datalog` already has empty deletes (`nd`) intrinsically** — see step 2.
- `dl_prog: datalog_prog "set const_names" "set (dl_rules P)"` is a sublocale of `pddl_datalog`;
  the minimal model is `dl_prog.derivable`.
- `num_free_relaxed_problem = pddl_datalog + numeric_free_problem + assumes bridge: "dl_bridge_wf P"`.
  Proves `nne` (from `num_free_dom`), `nd` (from `relaxed_prob`), and the hyp-free capstones
  `reachable_eq_minimal_model`, `certified_facts_eq_reachable`. `dl_bridge_wf` is its one
  outstanding *assumption* (see step 4).

## Step 1 — clean up `Reachability_Certificate.thy`

The file grew organically and predates `~/.claude/isabelle.md`. Bring it into line; re-verify with
the `jedit-status` skill after each chunk (`fully_processed` + `consolidated`).

- **Stale text/comments**: the header still describes a "closure-checked certificate fed to
  `wf_grounder`" and calls the tightness direction "still `sorry`" (§ "PDDL reachability is the
  minimal model …" and the `derivable_init`/`derivable_step_adds` blurbs). Update to reflect that
  ⊇ is proved and `dl_prog` is the model. Remove the "❙‹(still ❙‹sorry›)›" markers.
- **Style** (mostly done for chaining; finish the rest): `have` steps that state a bounded `∀x∈S`
  / `∀`/`⟶` and immediately peel it with `ballI`/`allI`/`impI` should use `if`/`for` instead
  (several remain in `derivable_step_adds`, `valuation_pos_conj_mono`, the older engine cores).
  One `using` per rule/fact group.
- **Dead scaffolding**: the long `text` block about the removed `cert_facts`/`cert_ops`/Nemo layer
  can be trimmed to a one-line pointer.
- After cleanup, do the **planned theory split** (`HANDOVER.md` §"Planned refactor"): carve
  `PDDL_Reachability_Analysis` (PDDL ⟷ minimal model: `dl_rules` serialization, `pddl_datalog`
  helpers, `derivable_*`, `achievable_eq_minimal_model`) from `PDDL_Reachability_Certificate`
  (`dl_certified_model` ⟷ PDDL: `certified_facts_eq_achievable`, the capstones). Use the
  `isabelle-refactor` skill; only move green blocks.

## Step 2 — put each proof in the locale that satisfies its assumptions

Right now the reverse-direction engine lemmas carry `nne`/`nd`/`dl_bridge_wf` as **explicit
hypotheses** (a hold-over from when `relaxed` did not imply delete-relaxation). Now that `relaxed`
*does*, relocate:

- **`nd`-only obligations**: `dl_derivable_imp_achievable`, `derivable_invariant`,
  `execute_facts_eq`, `plan_grows_facts`, `plan_replay_mono`, `achievables_reach_common`,
  `fire_clause_achievable`, `init'_achievable`, `clause_body_enabled` (and the `enabled_mono`
  family) take `nd` (and `nne`) as hypotheses. `nd` now holds in `pddl_datalog` (`relaxed_prob`
  ⟹ `relaxed_action` ⟹ `dels = []`). **Drop the `nd` hypothesis** from these and use the locale
  fact (a one-line `have nd: … using relaxed_prob_actionD …` at the top of `context pddl_datalog`,
  or just inline `relaxed_action_delD`). This removes `nd` threading throughout.
- **`nne`-dependent obligations**: `nne` needs numeric-freeness, which is **not** in `pddl_datalog`
  — it is in `num_free_relaxed_problem`. So the lemmas that genuinely need `nne` (`enabled_mono`,
  `plan_replay_mono`, `clause_body_enabled`, `fire_clause_achievable`, `init'_achievable`,
  `dl_derivable_imp_achievable`, and the `=` capstone `achievable_eq_minimal_model`) should move
  **down into `num_free_relaxed_problem`** (or a thin locale `pddl_datalog + numeric_free_problem`),
  where `nne` is a proved lemma — dropping the explicit `nne` premise. Keep the ⊆ soundness path
  (`achievable_imp_dl_derivable`, `derivable_init`, `derivable_step_adds`, `derivable_invariant`)
  in `pddl_datalog` unconditional.
- Net effect: no lemma should take `nne`/`nd` as a bare hypothesis; each lives in the locale that
  proves it. `dl_bridge_wf` likewise (step 4).

## Step 3 — `certified_pddl` locale (extends `pddl_datalog`)

Add a locale that bundles "a `pddl_datalog` problem together with an accepted generic datalog
certificate of its reachable facts", so the reachable-fact set is available as a *fact*, not a
hypothesis. Sketch:

```isabelle
locale certified_pddl = pddl_datalog +
  fixes M :: "fact list" and dc :: "_ dl_cert"      (* or whatever the cert witness type is *)
  assumes wf:   "dl_bridge_wf P"
      and cert: "dl_certified_model (set (dl_rules P)) (set const_names) M dc"
begin
  (* with nne available (so make this extend num_free_relaxed_problem, or add numeric_free_problem),
     certified_facts_eq_achievable gives: *)
  lemma certified_reachable: "set M = {f. achievable f}" ...
end
```

Decide whether `certified_pddl` extends `pddl_datalog` directly (then it still needs `numeric_free`
for the ⊇ direction → also extend `numeric_free_problem`, i.e. effectively
`num_free_relaxed_problem`) or extends `num_free_relaxed_problem`. Given step 2, the latter is
cleanest: `certified_pddl = num_free_relaxed_problem + fixes M dc + assumes cert`. Then
`certified_reachable` is just `certified_facts_eq_reachable[OF cert]`, and the grounder consumes
`set M` as the exact achievable-fact set. This is the locale `Certified_Grounding*` (currently the
deliberately-broken downstream) should be re-pointed onto.

## Step 4 — discharge `dl_bridge_wf` (drop the `bridge` assumption)

Prove `dl_bridge_wf P` as a lemma in `num_free_relaxed_problem` (+ a `const_names ≠ []`
assumption), then remove `bridge`. Via `dl_bridge_wfI`; for each `cl ∈ a_clauses` obtain
`sch ∈ actions D`, `cl = as_action_clause sch`,
`sch = SimpleActionSchema (ActionHead nm ps) (SimpleActionBody pre (Effect ad dl' nl))`. Conjuncts:

1. `dl_pre_translates` — automatic (`cl_pred_pre = pos_lits_of pre = filter is_predAtom`,
   `dl_pos_rh` of a predAtom is `Some`).
2. `dl_adds_predAtoms` — `wf_D(3)` ⟹ `wf_classical_action_schema sch` ⟹ `wf_effect (ac_tyt sch)
   (ac_eff sch)` ⟹ adds are `wf_fmla_atom` ⟹ `is_predAtom` (`wf_fmla_atom_alt`).
3. `dl_cond_translates` — `cl_cond_pre = cond_lits_of pre = filter (¬is_predAtom)`; relaxed ⟹
   `is_pos_lit`; num-free (`num_free_fmla_un_and` on `num_free_ac sch`) + `num_free_fmla_Atom_predAtom`
   ⟹ the cond atom is `eqAtm` ⟹ `dl_cond_rh = Some (Some (Eql …)) ≠ None`.
4. **(the crux)** `dl_clause_vars_params` — every term-VAR in `dl_clauses_of_action_clause cl`
   (head from an add atom, body from pos-precond/cond atoms) is in `map fst ps`. No existing lemma:
   build the chain `wf_pred_atom (p, vs)` ⟹ each arg `is_of_type` ⟹ for `VAR v`,
   `ty_term (map_of ps) constT (VAR v) = map_of ps v ≠ None` ⟹ `v ∈ dom (map_of ps) = fst ` set ps`.
5. `init'` facts predAtoms — wf `init P` (`wf_fmla_atom`) + conjunct 2 (`pseudo_init` = adds of
   fact clauses).
6. `const_names ≠ []` — from the `nonempty` assumption.

## Notes / gotchas carried over

- jEdit loads the **`Tree_Decomp_Grounding_Base`** heap; everything above is sources. A *new* theory
  import (e.g. `Numeric_Free`) is only picked up after a full jEdit **restart**, not a live edit.
  Launch with the `isabelle-launch` skill; kill via `/tmp/jedit-launch.pid` or `pkill -f JEdit_Main`.
- `?case` is **not** bound inside a nested `proof cases` (the `dl_derivable_imp_achievable` step
  case) — use the explicit goal term.
- `ac_tsubst` is `[simp]`; add `simp del: ac_tsubst_def` when you need it to stay folded
  (substitution-agreement steps).
- Edit open `.thy` only via `mcp__isabelle__write_file`; bulk syntactic renames via disk + reopen.
- `Grounding_Pipeline_Numeric` (top session) handles the strengthened `relaxed` fine (per the
  project owner); `Certified_Grounding*` is the pre-existing deliberately-broken downstream that
  step 3's `certified_pddl` should re-point.
