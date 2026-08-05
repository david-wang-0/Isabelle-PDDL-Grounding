# TODO — relocate the per-stage numeric-freeness lemmas into `Classical_<Stage>_Num_Free.thy`

The input-side numeric-freeness preservation chain (STRIPS-rebase tier 4) was proven entirely in
`Classical_Grounding/Grounding_Pipeline_STRIPS.thy` (the top session) to avoid rebuilding the
prebuilt stage sessions at the time. Structurally, each stage's preservation lemma belongs in a
stage-local theory `Classical_<Stage>/Classical_<Stage>_Num_Free.thy`, mirroring the existing
`Classical_Variable_Freeness/Classical_Variable_Freeness_Num_Free.thy` (imports the stage theory +
`Grounding_Classical_Common.Numeric_Free`). Do this the next time those sessions are being reprocessed
anyway; it needs a full batch rebuild + jEdit relaunch.

## What moves where

Current homes are in `Grounding_Pipeline_STRIPS.thy` (line numbers as of commit `822ab97`; the
generic ingredients — `num_free_fmla_atoms`, the map-preservation `[simp]` trio, `resolve_schema_mem`,
`num_free_resinst'` — already live in `Classical_PDDL_Sema_Supplement` and do **not** move again).

| target file (new) | lemmas to move (current line) |
|---|---|
| `Type_Normalization/Classical_Type_Normalization_Num_Free.thy` | `num_free_fmla_type_precond` (:542), `num_free_fmla_param_precond` (:550), `num_free_ac_detype_classical_ac` (:554), `restrict_prob_sigD` + `supertype_facts_predAtom'` (nearby), **`detype_prob_num_free`** (:577) |
| `Goal_Normalization/Classical_Goal_Normalization_Num_Free.thy` | `num_free_ac_goal_ac` (:612), **`degoal_prob_num_free`** (:617) |
| `Definedness_Normalization/Classical_Definedness_Normalization_Num_Free.thy` | `atom_enumerate_pne_num_free` (:648), `atom_enumerate_divisor_num_free` (:653), `definedness_atoms_num_free` (:658), `divisor_zero_atoms_num_free` (:669), `explicate_def_fmla_num_free_id` (:680), `num_free_ac_explicate_def_ac` (:687), **`explicate_def_prob_num_free`** (:692) |
| `Precondition_Normalization/Classical_Precondition_Normalization_Num_Free.thy` | `num_free_fmla_dnf_list` (:719), `num_free_ac_split_ac` (:730), **`split_prob_num_free`** (:741) |
| `Definedness_Translation/Classical_Definedness_Translation_Num_Free.thy` | `is_numeric_atom_def_translate_atom` (:769), `num_free_fmla_def_translate_fmla` (:774), `init_def_fact_num_free` (:780), `map_filter_init_def_fact_num_free` (:789), `num_free_ac_def_translate_ac` (:794), **`def_translate_prob_num_free`** (:809) |

Stays in `Grounding_Pipeline_STRIPS.thy` (genuinely pipeline-level — composes the stages in `P⇩T`'s
order): `P⇩X_num_free` (:833), `P⇩N_num_free` (:843), `P⇩T_num_free` (:851), `init_P⇩N_eq` /
`init_P⇩T_eq` / `init_P⇩T_props` (:866/:872/:888), `grounding_checks_P⇩T_of_num_free_input` (:904)
and `certified_reachability_i_num_free_input`.

Judgment calls during the move:

- The generic formula helpers `num_free_fmla_atomsI` / `num_free_fmla_of_predAtom` /
  `num_free_fmla_BigAnd` / `num_free_fmla_BigOr` (:516–:531) are stage-independent — move them into
  the numeric-freeness section of `Classical_PDDL_Sema_Supplement` next to `num_free_fmla_atoms`
  (they only need `num_free_fmla` + `BigAnd`/`BigOr`; check `BigAnd`/`BigOr` visibility there —
  if they are not in the supplement's closure, `Numeric_Free.thy` is the fallback home).
- `detype_prob_num_free` needs `restrict_prob` (supertype facts are only known `predAtm`s under the
  signature restriction) — keep that hypothesis; the stage file sees `restrict_prob` via
  `Grounding_Classical_Common`.

## Procedure (heap-boundary work)

1. `jedit-down`; delete `#…#` autosaves and `*.thy~` backups.
2. Create the five `Classical_<Stage>_Num_Free.thy` files (imports: the stage's main theory +
   `Grounding_Classical_Common.Numeric_Free`, session-qualified); cut the lemma blocks over
   verbatim; add each new theory to its stage session's `ROOT`.
3. Drop the moved blocks from `Grounding_Pipeline_STRIPS.thy` and import the new theories there
   (session-qualified, e.g. `Classical_Type_Normalization.Classical_Type_Normalization_Num_Free`) —
   check whether the pipeline file's existing imports already reach them transitively.
4. `isabelle components -u .` is NOT needed (no new sessions, only new theories in existing
   sessions — but the ROOT edits still require a jEdit restart to be seen). Note: the stage
   sessions have **no persisted heaps** — their theories build inside the top `Classical_Grounding`
   session — so the authoritative check is `isabelle build -b Classical_Grounding`, run from the
   `Classical_Grounding/` directory (the old-style `export_code … file "../SMLCodebase/…"` resolves
   against the build CWD).
5. Verify: build exit 0, exported SML regenerated, `make -C SMLCodebase` exit 0, default `ground`
   output byte-identical on gripper, smoke 37/41/5. `jedit-up Grounding_Classical_Common`.

## Rider (same rebuild, optional)

Declare the dest-rule kit for the bundled numeric-freeness predicates in
`Classical_PDDL_Sema_Supplement` (per the house intro/elim/dest rule for bundled predicates, stated
with `\<And>`): `num_free_probD` (→ `num_free_dom`, `num_free_fmla (goal P)`, per-element init),
`num_free_domD` (→ per-action `num_free_ac`), `num_free_acD` (→ pre/eff). Every tier-4 stage proof
currently re-unfolds `num_free_prob_def`/`num_free_dom_def`; the kit would shorten them and future
consumers.
