# WIP: datalog-certification bridge (generic checker ⟹ PDDL checker)

Status 2026-06-12 (restructured). The generic checker is now a **standalone session**
`Datalog_Certification` (`Datalog/ROOT`); the bridge was **absorbed into
`Reachability_Analysis/Reachability_Certificate.thy`** (sections *The PDDL → datalog
serialization*, *Executable mirrors of the certificate checks*, *Bridging generic datalog
certification…*, *PDDL reachability is the minimal model of the translated program*), along
with the serialization (`dl_id_of_term` … `dl_fact_clause`, `dl_rules`) and the `*_exec` check
mirrors, all formerly in `Grounding_Pipeline_STRIPS_Executable.thy`. That theory keeps only the
wire-format `dl_program` datatype and `dl_program_of` (now *defined* as
`DLProgram (dl_rules R) (const_names R)`, retiring `dl_program_of_alt`) plus the
`normalized_problem_rx`-side mirrors. `Datalog/Datalog_Certificate_Bridge.thy` is deleted.
**Restructure not yet re-verified in jEdit** (MCP bridge was down; needs a jEdit restart for
the new session anyway).
Design context: [ARCHITECTURE_datalog_certification.md](ARCHITECTURE_datalog_certification.md).

## Goal

Justify the PDDL reachability checks by the generic positive-datalog checker
(`Datalog/Datalog_Certificate.thy`), run on the *translated* program — the same
`dl_clauses_of_action_clause` / `dl_fact_clause` serialization that `dl_program_of` hands to
Nemo. Target theorem (already stated and proven *modulo two sorried transfer lemmas*):

`dl_bridge_wf R ⟹ cert_to_dl c = Some dc ⟹ dl_admissible (dl_rules R) (const_names R) dc ⟹ admissible_exec R c`

End state (runnable, per 2026-06-12 discussion): the exported SML binary asks Nemo for the
certificate of `dl_program_of P`, parses the ograph **directly into a generic
`dl_certificate`**, runs the (exported) generic `dl_admissible` / `dl_certified_model`, and
the bridge theorem converts acceptance into the `admissible_exec` fact the grounding pipeline
needs — one checker implementation, two layers of meaning.

## Done (green, 0 errors)

- `dl_rules R` — parametric form of `dl_program_of` (`dl_program_of_alt`).
- Fail-closed certificate conversion `cert_to_dl : certificate ⇒ dl_certificate option`
  (`None` if any node fact is not a predicate atom), executable (`[code]`).
- Structural correspondence: `those_Some`, `cert_to_dl_len`, `cert_to_dl_nth`,
  `cert_to_dl_facts` (`cert_facts c = map facty_of_dl (dl_cert_facts dc)`),
  `cert_to_dl_predAtom`.
- `cert_to_dl_ordered`: the ordered check transfers **both ways** (proved).
- `dl_clauses_of_action_clause_mem`: inversion of the clause translation (head is a
  `predAtm` of `cl_pos`, body = translated `cl_pred_pre` ++ translated guards, nothing
  dropped). Proof gotcha: case-congruence blocks `map_map` normalization inside
  `case`-branches over a variable scrutinee — state the case equation in the **composed**
  `map (the ∘ f)` form (what simp produces inside the translation lambda) and do the formula
  shape analysis with `(cases f) (auto split: atom.splits)`.
- `dl_rules_positive`: the translated program never contains `NegLit`, so the generic
  checker's positivity gate is free.
- `dl_bridge_wf` — the well-formedness bundle the transfer needs (see below).
- Main theorem `dl_admissible_imp_admissible_exec` assembled from the pieces.

## Remaining sorries

### 0. NEW: the minimal-model relation (section *PDDL reachability is the minimal model…*)

In `context pddl_datalog`, under `dl_bridge_wf P`:

- `achievable_imp_dl_derivable` (sorried): `achievable f ⟹ dl_derivable (dl_rules P)
  const_names f`. Plan: mirror `closure_invariant`/`closure_step_adds` with
  `dl_derivable`-closure in place of certificate membership; the σ-construction of the (now
  proven) closure transfer supplies the generic ground instance per fired action.
- `dl_derivable_imp_achievable` (sorried): rule induction on `dl_derivable`; a step is a
  translated action clause (fire that action; relaxation persists earlier facts) or an `init'`
  fact clause.
- `achievable_eq_minimal_model` (= the two above, proven assembly).
- `minimal_model_facts_requirement` (proven assembly) / `minimal_model_ops_requirement`
  (sorried; plan in its text: reachable world model facts are achievable ⟹ in the model ⟹
  in `cert_facts c`, then `enabled_clause_body` + `action_params_match_combos`).

### 1. `dl_closure_imp_closure_exec` — DONE (proof landed, 0 sorry)

`dl_bridge_wf R ⟹ cert_to_dl c = Some dc ⟹ dl_closure_check (dl_rules R) (const_names R) dc ⟹ closure_check_exec R c`

The plan below was executed; kept for reference:

- *all facts predAtoms*: `cert_to_dl_predAtom` (done).
- *`init' ⊆ fs`*: each `f ∈ init'` is a predAtom (bundle) ⟹ `dl_fact_clause f = Some (Cls p
  (map Cst xs) [])` is in `dl_rules R`; its unique vacuous substitution fires with empty body
  ⟹ generic closure puts `(p, xs)` in `dl_cert_facts dc` ⟹ `cert_to_dl_facts` maps it back.
  Needs: `cls_vars` of a ground fact clause is `[]` and `cls_substs U` of it is a singleton
  (`set_all_combos` + `chosen_from [] []`).
- *clause firing*: fix `cl ∈ a_clauses R`, `args ∈ all_combos ✓ (replicate |params| consts)`
  with instantiated `cl_pred_pre ⊆ fs` and `satisfies_conds`. If the clause was dropped by the
  translation: `None ∈ map dl_pos_rh (cl_pred_pre)` is excluded by the bundle;
  `None ∈ map dl_cond_rh (cl_cond_pre)` means (bundle) some cond is statically unsatisfiable,
  contradicting `satisfies_conds` — vacuous. Otherwise, for every add `h ∈ cl_pos` (predAtm by
  bundle) there is `dcl ∈ dl_rules R` with head `h`. Build `σ = (λv. ac_tsubst params args
  (term.VAR v))` restricted to `cls_vars dcl`; membership in `cls_substs` via
  `set_all_combos` + `chosen_from` (each value is some `args ! i ∈ set args ⊆ consts`) and
  `subst_of`-on-`remdups`-distinct agreement (`map_of (zip …)`).
  Key sub-lemmas to develop (shared with lemma 2):
  - `subst_id σ (dl_id_of_term t) = ac_tsubst params args t` for `t` mentioning only
    covered variables;
  - `subst_atom σ (translated atom) = (p, map (ac_tsubst …) ts)` and its `facty_of_dl` image
    is `map_atom_fmla (ac_tsubst params args) (Atom (predAtm p ts))`;
  - guard transfer: `eval_guard σ (Eql/Neql …) ⟷ satisfies_cond params args (eqAtm/¬eqAtm …)`
    — needs the `valuation`-on-`eqAtm` simp facts (cf. `valuation_predAtm_iff`,
    `cond_lit_model_indep` in `Reachability_Certificate.thy`); the dropped conds
    (`¬⊥`, `¬predAtm` ↦ `Some None`) are *true* in the empty model, so dropping is sound.

### 2. `dl_local_valid_imp_local_valid_exec`

`… ⟹ i < |nodes c| ⟹ dl_local_valid (dl_rules R) (const_names R) dc i ⟹ local_valid_exec R c i`

Generic witness `dcl ∈ dl_rules R`, `σ ∈ cls_substs`. Case split on `dcl`'s origin:

- *fact clause of `init'`*: body atoms `[]` ⟹ `set (dn_body dc i) = {}` ⟹ `dn_preds = []`
  (= `cn_preds`, by `cert_to_dl_nth`) and `cn_fact = facty_of_dl (p, xs) ∈ set init'` —
  the PDDL init disjunct.
- *translated action clause `cl`*: if `cl_pred_pre cl = []` the head fact is in `pseudo_init ⊆
  init'` (same as above, via `all_fact_paramz`; needs the reverse arg construction). Otherwise
  `cl ∈ pred_clauses R`; construct `args`: for parameters in `cls_vars dcl` take `σ v`, for
  the rest take any element of `const_names R` (bundle: non-empty). Then `satisfies_conds`
  (guard transfer, unused params don't matter), `cn_fact (nodes c ! i) ∈ consequence_of cl
  args` (head correspondence), and `set (cn_body c i) = set (map (map_atom_fmla …)
  (cl_pred_pre cl))` (body correspondence through `facty_of_dl`, which is injective).

### 3. Discharge `dl_bridge_wf` for the pipeline instance

Separate, after 1–2: `restrict_prob P ⟹ wf_classical_problem P ⟹ dl_bridge_wf
(relax_prob (P⇩T P))` — the normalization/relaxation invariants (DNF literal shapes, predAtom
effects, parameter-closed schemas, non-empty object universe may need a side condition).
Then specialize the main theorem to `ground_via_cert`'s checking site.

## Runnable wiring (after the proofs, or in parallel — untrusted side)

1. `export_code` the generic checker (`dl_admissible`, `dl_certified_model`, `cert_to_dl`,
   `dl_rules`) alongside the existing exports in `Planner_STRIPS_Export.thy`.
2. In `SMLCodebase/`, extend the Nemo driver to parse the ograph into the *generic*
   `dl_certificate` (today it builds the PDDL `certificate`; the node structure is identical,
   only the fact payload differs: `(predicate, object list)` vs `facty`).
3. Either keep handing the PDDL kernel its own certificate (status quo) or switch
   `ground_via_cert` to: convert via `cert_to_dl`, check generically, use the bridge theorem
   for soundness. The second option retires the duplicated `*_exec` check bodies.

## Gotchas log

- `Stratified_Datalog.Datalog`'s `id.Var`/`id.Cst` capture unqualified `Var` downstream —
  hidden via `hide_const (open)` in `Grounding_Pipeline_STRIPS_Executable.thy` (2026-06-12).
- The translation drops clauses fail-closed (`None` cond/pre) and drops non-predAtm heads
  silently — both directions of any *equivalence* would be false without `dl_bridge_wf`;
  the bridge only claims the generic⟹PDDL implication under the bundle.
- PDDL enumerates one argument per *parameter*; the generic checker one constant per
  *occurring variable* — the `≠ []` universe assumption is what lets unused parameters be
  witnessed (a genuinely-empty universe with a parameterized clause makes PDDL
  `local_valid_exec`'s existential unsatisfiable while the generic one can hold).
