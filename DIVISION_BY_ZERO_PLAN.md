# Division-by-zero: grounding-side plan (Definedness_Normalization)

> **STATUS (2026-08-02): COMPLETE — whole classical pipeline green.** Changes 1–3 below are
> implemented and verified end-to-end: restated supplements, `plan_action_enabled` + 5th
> conjunct `numeric_effects_defined`, `conj_literal_prefix`/`is_div_explicated_conj` + split
> survival (`dnf_list_NotAtom_And` twin chain), two-segment `explicate_def_fmla`,
> truth-neutral `explicate_valid_iff`, translation, relaxation, reachability, grounder,
> STRIPS, both pipelines, executables, `Code_Setup`, and both Running_Examples (outputs
> unchanged). The fresh-fluent effect gap discovered en route (translation equivalence false
> for `None`-writes to fresh fluents) was fixed **FPS-side**: `numeric_effects_defined` now
> quantifies over `dom w ∪ ⋃(set ` lvalues ` set Aᵢ)` (FPS commits `48f903d` + QA `db15114`
> with 29 regression lemmas and `examples/division-by-zero-effects/`); the interim
> `div_free_effects_dom` crutch was removed repo-wide, the translation stage's rhs-evaluation
> now comes from the FPS contract lemma `numeric_effects_defined_rhs_defined`.
> Recurring repair recipes (for future semantics bumps): def-unfolding transfers need
> `lvalues_def image_image` in the simp set; effect-free actions discharge the 5th conjunct
> by `using <no-num-effects fact> by (auto simp: numeric_effects_defined_def
> action_list_numeric_update_function_def action_numeric_update_function_def lvalues_def
> dom_def)` — chain the fact via `using`, never `simp add:` (a rule about `(the o res_inst) a`
> does not fire after composition normalization).
> Not re-verified (no references to any changed name; next batch build covers them):
> `Planner_Export.thy`, `Planner_STRIPS_*`, `Grounder_Timing.thy`.

The FPS side has **landed**
(commit `97a5657`, "Make division by zero undefined in the numeric semantics"): all three
evaluators return `None` on a zero divisor, `enumerate_divisor_expressions` + atom/formula lifts
exist (`Analysis_Free_Base/Abstract_Syntax.thy:137,151,173,186`), the None-characterization
lemmas are restated, and `examples/division-by-zero/` has solvable/unsolvable instances.
(The originally-specced contract lemma `valuation_numericEq_inv_divisor` was never added and is
**not needed** — the revised witness below gets its semantics from `valuation_def` directly.)

## The one insight that scopes the work

Under the new semantics, a zero divisor is *just another source of atom-undefinedness*, exactly
like an unassigned fluent. The pipeline already reduces atom-undefinedness to **definedness
witnesses conjoined into a prefix before the DNF split** — the split's plan-equivalence lemmas
are gated on `def_explicated_conj_prob`. So:

- **All correctness (plan-equivalence) work is in `Definedness_Normalization`.** Emit a
  divisor-nonzero witness, and make it *survive the split* into every DNF clause.
- **`Definedness_Translation` needs no correctness change.** `def_translate_fmla` is
  `map_formula (def_translate_atom pfx)` — an atom-wise, shape-preserving map that rewrites only
  the reflexive `f = f` definedness equalities into propositional `defined_f` predicates. The
  divisor witnesses are *not* of that shape, so they pass through verbatim as honest numeric
  preconditions of the grounded numeric problem. Translation-stage tightness for the relaxation
  (letting reachability prune provably-zero divisors) is an optional follow-up, not a blocker.

## The witness shape (REVISED — negated disequality, not the `1/y = 1/y` trick)

Explicated preconditions have the form

```
(f_0 = f_0) ∧ … ∧ (f_n = f_n) ∧ ¬(y_0 = 0) ∧ … ∧ ¬(y_m = 0) ∧ form
```

where `f_i` ranges over `formula_enumerate_primitive_numeric_expressions form` (as today) and
`y_j` over `formula_enumerate_divisor_expressions form`. The divisor witness is the *literal*

```
Not (Atom (numericEqAtm y (ConstantExpr 0)))
```

Truth conditions under strict `⊨ₘ` (`𝒜 ⊨ₘ Not φ ⟷ atoms φ ⊆ dom 𝒜 ∧ ¬ 𝒜 ⊨ₘ φ`, and
`valuation` of `numericEqAtm y (ConstantExpr 0)` is `map_two_options (y⟦nw⟧) (Some 0) (=)`):
satisfied **iff `y` is defined and `y ≠ 0`** — undefined divisor → atom undefined → literal
fails; zero divisor → atom `Some True` → negation fails. Exactly the divisor condition. Note
divisors may be compound (`x/(a+b)` → witness `¬(a+b = 0)`); their leaves are covered by the
`f = f` segment, and nested divisors get their own witnesses via the FPS enumerator (`DivExpr`
case emits inner divisors and `y` itself).

**Why the equalities come first.** `conj_atom_prefix`
(`Classical_Grounding/Common/Classical_PDDL_Normalization.thy:164`) collects leading `Atom`
conjuncts and **stops at the first non-Atom conjunct**. Keeping all `f = f` atoms before the
`¬(y = 0)` literals means `conj_atom_prefix`, `is_def_explicated_conj` (`:172`), and every proof
about the fluent segment survive **unchanged**. The divisor literals form a second segment with
its own (new, parallel) tracking.

## Change 1 — `definedness_atoms` + `explicate_def_fmla` (reusable)

`Grounding_Common/Definedness_Normalization/Definedness_Normalization.thy`. Keep
`definedness_atoms` as-is (atoms only, so `conj_atom_prefix_foldr_and_Atom` (`:168`) still
applies verbatim). Add the divisor-atom list and interleave in the right order:

```
definition "divisor_zero_atoms f ≡
  map (λy. numericEqAtm y (ConstantExpr 0)) (formula_enumerate_divisor_expressions f)"

definition "explicate_def_fmla f ≡
  foldr (∧) (map Atom (definedness_atoms f))
    (foldr (∧) (map (λa. ¬(Atom a)) (divisor_zero_atoms f)) f)"
```

(equalities segment → disequalities segment → `form`.)

## Change 2 — the "survive the split" obligation

`Classical_Grounding/Common/Classical_PDDL_Normalization.thy`. `is_def_explicated_conj` (`:172`)
stays **unchanged** (fluent segment only). Add the parallel notion for the literal segment — a
prefix scanner that accepts both polarities, and the divisor predicate:

```
fun conj_literal_prefix :: "'a formula ⇒ 'a formula list" where
  "conj_literal_prefix (Atom a ∧ f)      = Atom a # conj_literal_prefix f"
| "conj_literal_prefix (¬(Atom a) ∧ f)   = ¬(Atom a) # conj_literal_prefix f"
| "conj_literal_prefix _ = []"

definition "is_div_explicated_conj f ≡
  ∀y ∈ set (formula_enumerate_divisor_expressions f).
    ¬(Atom (numericEqAtm y (ConstantExpr 0))) ∈ set (conj_literal_prefix f)"
```

and conjoin `is_div_explicated_conj` into `def_explicated_conj_dom` / `_prob` (`:176,:182`)
(or keep it a separate locale assumption threaded the same way — implementor's choice).

Why this is the heart of it: with strict `⊨ₘ`, `𝒜 ⊨ₘ (f ∨ g)` requires *both* disjuncts' atoms
defined. If `g` divides by a zero divisor, `f ∨ g` is false even when `f` holds; for the DNF-split
equivalence `𝒜 ⊨ₘ F ⟷ (∃c ∈ set (dnf_list F). 𝒜 ⊨ₘ c)`
(`Classical_Precondition_Normalization_Semantics.thy:135`) to survive, the `f`-clause must carry
`g`'s divisor witness. Conjoining the *whole formula's* witnesses into the prefix, then requiring
prefix-membership per clause, is exactly that guarantee.

Split-survival lemmas to mirror (`Classical_Precondition_Normalization.thy`):

- `:69–74` "clause PNEs = formula PNEs" → twin:
  `set (formula_enumerate_divisor_expressions c) = set (formula_enumerate_divisor_expressions f)`
  for `c ∈ set (dnf_list f)`, given the explication predicates.
- `:96–101` `is_def_explicated_conj c` per clause → twin `is_div_explicated_conj c`
  (dnf_list keeps prefix literals in clause prefixes; `¬(Atom _)` is NNF/DNF-stable).
- `def_explicated_conj_split_prob` / `_dom` (`:346–354`) → extend with the divisor half.

## Change 3 — `explicate_valid_iff` (uses the new FPS semantics)

`ast_classical_problem_de.explicate_valid_iff` (surfaced as `explicate_def_valid_iff_compact`,
`Grounding_Pipeline_Numeric.thy:185`). The new conjuncts must be **truth-neutral** on the
unsplit formula: whenever `𝒜 ⊨ₘ form`, every atom of `form` is defined, and by the restated
`numeric_expression_valuation_eq_None_iff` (definedness ⟹ no divisor evaluates to `Some 0`)
every divisor witness `¬(y = 0)` is satisfied — so conjoining them changes nothing; conversely
the explicated formula implies `form` trivially. The `⊨ₘ`-characterization of the witness literal
(defined-and-nonzero, above) is provable here from `valuation_def` + the FPS None-iff — no new
FPS lemma required.

## Housekeeping lemmas — expected fallout

- `atoms_explicate_def_fmla` (`Classical_Definedness_Normalization.thy:13`): becomes
  `… = set (definedness_atoms f) ∪ set (divisor_zero_atoms f) ∪ atoms f`; needs the `¬`-case
  analogue of `atoms_foldr_and`.
- `explicate_def_fmla_pnes` (`:29`): PNE set still unchanged — divisor atoms' leaves
  (`y`, `ConstantExpr 0`) contribute only existing leaves. Re-prove with the extra segment.
- Divisor-set of the explicated formula = divisor-set of `form` (the witness `y = 0` atom
  introduces **no new divisor**: `numericEqAtm y (Const 0)`'s divisors are `y`'s own divisors,
  already enumerated). Needed for idempotence-style lemmas and Change 2's twins.
- `is_def_explicated_conj (map_atom_fmla m f)` (`Classical_Definedness_Translation_Semantics.thy:442`,
  and the use at `:192`): add the `is_div_explicated_conj` analogue — note `def_translate_atom`
  leaves `numericEqAtm y (ConstantExpr 0)` alone (not the reflexive `FunctionExpr p = FunctionExpr p`
  shape), so the literal segment maps through `def_translate_fmla` unchanged.
- **Pre-existing red**: the FPS change restated `numeric_expression_valuation_eq_None_iff` /
  `dom_valuation_iff` / `valuation_of_undefined`; grounding theories referencing them
  (`PDDL_Sema_Supplement`, `Classical_PDDL_Sema_Supplement`, `Code_Setup`, the Definedness/
  Precondition `_Semantics` files) may be broken *before* any of this plan starts. Repair first.

## Order of operations

1. ~~FPS change lands~~ **done** (`97a5657`).
2. Rebuild `Grounding_Base` (`isabelle build -b`) on the new FPS; relaunch jEdit
   (`Grounding_Classical_Common` heap so the stages process live).
3. Survey + repair the pre-existing red against the restated FPS lemmas.
4. Changes 1–3 above, verifying via `jedit-status`.
5. Optional: relaxation-tightness treatment of the divisor literals in reachability.
