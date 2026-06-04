# WIP: Numeric Definedness Tracking

This document captures the design and outstanding work for extending the verified PDDL grounder to numeric PDDL by translating numeric definedness into propositional predicates. This simpler definedness-tracking approach replaces the earlier bound-splitting approach.

## Goal

Extend the grounder to handle definedness of Primitive Numeric Expressions (PNEs) properly under delete relaxation. 
Instead of complex bound splitting, we introduce a new step (`Definedness_Translation`) right before precondition relaxation. This step converts definedness requirements and assignments into regular propositional atoms.

## Pipeline (Target Order)

```text
detype (Type_Normalization)
  -> degoal (Goal_Normalization)
  -> explicate_def (Definedness_Normalization) 
  -> split (Precondition_Normalization)
  -> def_translate (NEW — Definedness_Translation)
  -> relax (PDDL_Relaxation)
  -> reach (semi_naive_eval on the relaxed problem)
  -> ground (existing grounder)
  -> as_strips
```

## The Definedness_Translation Step

The `Definedness_Translation` step transforms actions as follows:

1. **Preconditions:**
   - Strips out the `(Atom (numericEqAtm (FunctionExpr p) (FunctionExpr p)))` checks that were added during `explicate_def`.
   - Adds a new propositional predicate `(predAtm (Pred "Defined_f") args)` for all PNEs that were in that original `numericEqAtm` prefix.
   - Also adds `(predAtm (Pred "Defined_f") args)` for any PNE that appears on the **RHS** of any numeric effects in the action, as the action cannot execute if the RHS is undefined.

2. **Effects:**
   - For any PNE that is assigned on the **LHS** of a numeric effect, adds `(predAtm (Pred "Defined_f") args)` to the propositional `adds` of the action to indicate that the PNE has become defined.

Because this step translates numeric definedness fully into propositional atoms, the subsequent `relax` step (which destroys numeric atoms) can be left completely unchanged!

## Concrete Work Items

1. **Create `Definedness_Translation/ROOT` and skeleton `Definedness_Translation.thy`**. — done.
2. **Implement AST transformations** for `Definedness_Translation` (preconditions and effects as described above). — done.
3. **Wire into `Grounding_Pipeline.thy`** between `split` and `relax`. — in progress (see status below).

## Status

**`Definedness_Translation` (done).**
- Well-formedness (`Definedness_Translation.thy`): `def_translate_prob_wf`, `dt`/`pt` wf sublocales — 0 sorry.
- Plan equivalence (`Definedness_Translation_Semantics.thy`): `def_translate_valid_iff` /
  `def_translate_valid_plan_iff` — 0 sorry. The reflexive definedness checks `(= p p)` are
  forced into the positive conjunctive prefix (`is_def_explicated_conj`), which rescues the
  per-literal equivalence under the three-valued `⊨⇩m`.
- Normalization preservation (`def_translate_normalized`, end of `Definedness_Translation.thy`):
  `def_translate` preserves `normalized_prob` (parameters/objects untouched ⇒ typeless preserved;
  the added `Defined_` predicates inherit the `ω`-typed argument types of the functions they track;
  preconditions/goal are mapped through `map_formula` inside a positive conjunctive prefix ⇒
  `is_conj` preserved). This is what lets the unchanged `relax` step consume `P⇩T`.

**`PDDL_Relaxation` (done).** Refactored `PDDL_Relaxation_Locales.thy` to fold the `dx`/`px`
signature constants onto the originals via sublocale `rewrites` (mirroring
`Type_Normalization_Locales`); the only retained explicit bridge is `rx_resolve_eq[simp]`
(`resolve` genuinely changes, and folding it clashes with the `simple_action_instantiations`
sublocale). Removed the now-redundant `rx_*` bridge lemmas. Adapted the world-model refactor in
`PDDL_Relaxation_Semantics.thy` (`rx_exec` + new `rx_exec_snd` for the numeric part, `rx_path_right`
with a `snd M1 = snd M1'` invariant) and re-enabled `relax_achievables` / `relax_applicables`.

**Pipeline wiring (in progress).** `Grounding_Pipeline.thy` now imports
`PDDL_Relaxation_Semantics` and has `def_translate` compact lemmas (`def_translate_prob_wf_compact`,
`def_translate_normed_compact`). The pipeline order is
`detype → degoal → explicate_def → split → def_translate (P⇩T) → relax (P⇩R)`. Still TODO:
fix the `normalization_normalizes` proof for the new `typeless`/`is_conj` structure, rethread
`relaxation_applicables`/`relaxation_achievables`/`relaxation_wf_relaxed_normed` onto `P⇩T`. The
grounding/reachability section (`wf_grounder`, `semi_naive_eval`, `relaxed_problem.found_facts_achievable`,
`as_strips`) is blocked on `Reachability_Analysis.thy`/`Grounded_PDDL.thy`, which are still on the
old `ast_problem` API and out of scope for the relaxation wiring.
