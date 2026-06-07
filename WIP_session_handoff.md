# Session handoff (2026-06-07, updated)

Status snapshot for resuming in a fresh session. Covers the certificate→grounder bridge,
numeric-freeness, the PDDL→STRIPS port (now COMPLETE), and the pipeline wiring.

> **Newer work (2026-06-07, separate track): executable running example.**
> `Running_Example.thy` is ported to the current API and GREEN through `P\<^sub>T`/`P\<^sub>R`
> (`value` runs). This required real code-generation setup (dropping FPS cont/temporal
> per-interpretation code equations that poison shared `domain_signature`/`problem_signature`
> constants, a missing `def_translate` code bundle, and lifted-string code eqs). `semi_naive_eval`
> is *not* code-runnable (numeric `valuation` → `Inf [filter]` wellsortedness); the certificate
> checker bypasses it. Full state + next steps: **`WIP_running_example_certification.md`**
> (§ SESSION PROGRESS 2026-06-07) and `TODO.md`.

## ✅ DONE (verified green via jEdit/MCP)

### 1. Certificate→grounder bridge — COMPLETE, 0 sorries
- `Reachability_Analysis/Reachability_Certificate.thy`: **0 sorries, 0 errors**, consolidated.
  - `cert_ops` redefined as a **finite enumeration** over `a_clauses × all_combos`, filtered by
    "instantiated `cl_pred_pre` ⊆ `cert_facts` ∧ `satisfies_conds cl_cond_pre`".
  - `cert_ops_sound`: `closure_check c ⟹ {applicable} ⊆ set (cert_ops c)` (plan induction).
  - Dead unsound old `Locale B` removed.
- `Reachability_Analysis/Certified_Grounding{_Locales,,_Semantics}.thy`: **0 sorries**.
  `wf_grounder P cert_facts' cert_ops'` sublocale at **P_N** fully discharged ⇒
  `valid_classical_plan_iff` holds at the un-relaxed problem.

### 2. `Base/Numeric_Free.thy` — green (in `Base/ROOT`)
Propositional-fragment restriction. Key names (used heavily by the STRIPS port):
- `is_numeric_atom`, `num_free_fmla`, `num_free_eff`, `num_free_ac` (def, global),
  `(in ast_classical_domain) num_free_dom` = `∀a∈set(actions D). num_free_ac a`,
  `(in ast_classical_problem) num_free_prob` = `num_free_dom ∧ num_free_fmla (goal P) ∧
  (∀f∈set(init P). num_free_fmla f)`.
- locales `numeric_free_domain` / `numeric_free_problem` (problem sublocales domain via
  `num_free_prob_def`). Helper `num_free_fmla_un_and`.
- Numeric-freeness is an INPUT restriction checked + carried through, NOT a grounder guarantee.

### 3. `PDDL_to_STRIPS.thy` — **PORT COMPLETE, 0 errors** (was the main task this session)
Full propositional-fragment STRIPS translation now type-checks and the WF side is proven.

**Numeric-free threading.** New combined locale:
```
locale grounded_normalized_numeric_free_problem =
  grounded_normalized_problem + numeric_free_problem
```
The `valid_strips` sublocale and the final `wf_as_strips` theorem live here; `init_covered`,
`goal_covered` moved here too. Inside, the needed num-free facts are derived from the assumption:
`using num_free_prob unfolding num_free_prob_def [num_free_dom_def] by blast`.

**Per-lemma fixes (all green):**
- `wf_empty_lit`/`wf_empty_lits`/`wf_empty_atom`: take `num_free_fmla` hyp (false without it
  under the numeric atom type); `wf_empty_atom` derives num-free from `wf_fmla_atom`.
- `ac_tyt_empty`: `proof (rule ext) fix x show … by (cases x) (simp_all add: ac_tyt_def acp
  constT_empty) qed`.
- `wf_pre_lits` / `wf_eff_lits`: `(cases ac rule: ast_classical_action_schema_cases_unfold)
  (auto simp: ac_tyt_def Let_def)` — the `Let_def` is essential (the case rule leaves a
  `let tyt = … in …` in the hypothesis). `wf_pre_lits` carries `num_free_ac ac`.
- `wf_init_lits`: `assumes ∀f∈set(init P). num_free_fmla f`; for each init `f`, `wf_P(4)` gives
  `wf_fmla_atom objT f ∨ wf_func_assign f`, and `(cases x rule: wf_func_assign.cases) auto`
  rules out the `wf_func_assign` (numericEqAtm) branch via the num-free hyp ⇒ `wf_fmla_atom`,
  then `wf_empty_atom` (`unfolding objT_empty`).
- `wf_goal_lits`: `assumes num_free_fmla (goal P)`; `is_conj (goal P)` from `normed_prob`.
- `wf_as_strips_op`: gained `assumes "num_free_ac ac"`; fixed `wf_eff_lits[OF assms(1)]`.
- `wf_as_strips` (in combined locale): derives `ndom: ∀a∈set(actions D). num_free_ac a` and
  `ops` from `num_free_prob`, then the old apply-script.
- **String inequalities — `String_Utils` could NOT be imported** (jEdit: "Bad theory import"
  `Tree_Decomp_Grounding_Base.String_Utils`, even though sibling Base files import it; the
  loaded session graph wouldn't resolve a *new* import of a not-yet-loaded theory). So the two
  needed facts were proved **inline** at the top of the file instead:
  - `lit_prepend_inj: "(s + a = s + b) = (a = b)" for s a b :: name`
    `by (metis String.implode_explode_eq plus_literal.rep_eq same_append_eq)` (= `inj_prepend`).
  - `vneg_neq_vpos: "vneg p ≠ vpos q"` — contradiction: `explode (STR ''-'' + …) = explode
    (STR ''+'' + …)`, then `have "literal.explode (STR ''-'' :: name) = ''-''" "… ''+'' = ''+''"
    by eval+`, `ultimately … by (simp add: plus_literal.rep_eq)`.
  - `v_inj` now uses `(simp add: lit_prepend_inj)`; `pos_vs_neg` uses `(simp_all add: vneg_neq_vpos)`.
- Bottom region: `strips_pa` → `resolve_classical_action_schema`; `strips_model_props` /
  `pddl_model_props` statements changed `∈ M` → `∈ fst M` (world_model is now a PAIR); the
  `pred_vpos` line of the exploratory `wf_pred` lemma was commented out (`pred_vpos` is iceboxed).

**Still `oops` in PDDL_to_STRIPS (the semantics-preservation direction — next real goal):**
`strips_model` / `pddl_model` are stubbed `≡ undefined`; `strips_model_props`,
`pddl_model_props`, `valid_plan_right`, `restore_pddl_plan`, `valid_plan_iff` are all `oops`.
The WF side (`is_valid_problem_strips as_strips` + `valid_strips` sublocale) is fully proven;
the plan-equivalence side is not started.

## ✅ DONE (2026-06-07 session): §B + §C — `Grounding_Pipeline.thy` is now GREEN

`Grounding_Pipeline.thy`: **0 errors, 0 sorry**; the only remaining `oops` are
`strips_plan_reconstruct_cert` / `strips_plan_iff_cert` (the STRIPS-cert branch), which
genuinely need §A (the `valid_plan_iff` plan-equivalence still `oops` in `PDDL_to_STRIPS.thy`).

- §B: `(in grounder) ground_prob_num_free` — the grounded problem is **unconditionally**
  numeric-free (`ground_fmla` only emits ⊥/¬⊥/nullary `predAtm`, never a numeric atom).
- §C: `(in wf_grounder) ground_prob_normed` sorry filled; `restore_plan_def_translate_compact`
  defined; `ground_cert_plan_reconstruct` re-qualified onto `P⇩N`; `ground_cert_plan_valid_iff`,
  `wf_ground_cert_problem`, `wf_as_strips_cert` all proven.
- Also repaired pre-existing relaxation-refactor drift that had been masked by the earlier
  parse error: the two `def_translate_valid*_iff_compact` lemmas moved to locale
  `def_explicated_conj_problem_dt` (+ added `def_explicated_conj_prob` hyp); new
  `P⇩N_def_explicated_conj`; `wf_as_strips_compact` retargeted to
  `grounded_normalized_numeric_free_problem`; `reconstruct_plan_norm` def + `normalization_reconstruct`
  metis name fixes; `P_T_normalized_problem_rx` via `normalized_problem_def'`; cert header
  `ast_classical_problem.relax_prob P⇩T`.
- **Cert-block gotcha:** `certified_reachability ⊆ wfg: wf_grounder P cert_facts' cert_ops'` is a
  NAMED sublocale, so bridge facts are `cr.wfg.<fact>` (NOT `cr.<fact>`), and
  `cert_facts' ≡ cert_facts_of cert` / `cert_ops' ≡ cert_ops_of cert` — unfold those defs to make
  `cr.wfg.ground_prob` match `P⇩G_cert` (defined with `cert_facts_of`).

## ❌ NOT DONE / remaining

### A. STRIPS semantics preservation (the `oops` stubs in PDDL_to_STRIPS)
(Still the blocker for the two `strips_plan_*_cert` `oops` in the pipeline.)
Define `strips_model :: world_model ⇒ name strips_state` and `pddl_model` for real, prove
`strips_model_props` / `pddl_model_props`, then `valid_plan_right` / `restore_pddl_plan` /
`valid_plan_iff`. This is what makes the STRIPS branch a genuine plan-equivalence (both
directions), not just a WF task. Remember `world_model = logical × numeric` (a PAIR); the
propositional state lives in `fst`.

### B. Discharge numeric-freeness for the grounded problem `P_G`
In `Certified_Grounding_Semantics` (where the grounding output lives): prove `P_G` (the
certificate-grounded problem) instantiates `numeric_free_problem` / satisfies `num_free_prob`
from the `grounding_checks` (predicate-atom-only `facts`, `ops_no_num`) + the propositional
input restriction. That is what lets the pipeline instantiate
`grounded_normalized_numeric_free_problem` and take the STRIPS branch.

### C. Finish `Grounding_Pipeline.thy` (certificate grounding + STRIPS)
- `restore_plan_def_translate_compact` is USED but **not defined** — add it
  (`restore_plan_def_translate` is identity; from `def_translate_valid_plan_iff_compact`).
- `ground_cert_plan_reconstruct` chain mis-qualified: intermediate
  `valid_classical_plan2 (restore_plan_def_translate q)` should be at **`P_N`**, not base `P`.
- `ground_prob_normed` (in `wf_grounder`) still `sorry` (~line 137).
- Verify `P⇩G_cert` / `ground_cert_plan_valid_iff` / `wf_as_strips_cert` chain; wire the
  STRIPS-cert branch to require `num_free_prob` for `P_T`/`P_G` (depends on B).

### D. Engine residual sorries (superseded, low priority)
`Reachability_Analysis/Reachability_Analysis.thy`: `semi_naive_aux` termination (~176/182) and
`found_facts_achievable` / `found_pactions_applicable` (~345/349) — the UNTRUSTED engine,
superseded by the certificate path; not on the verified path.

## KEY FACTS / API NOTES (new semantics)
- `atom`: `predAtm | eqAtm | numericEqAtm | numericLessAtm | numericLEAtm | numericGreaterAtm
  | numericGEAtm`. `is_predAtom (Atom (predAtm _ _)) = True | _ = False`.
- `world_model = logical_world_model × numeric_world_model` (PAIR); `wf_world_model (M,_) =
  (∀f∈M. wf_fmla_atom objT f)` (a `fun`, no `_def`).
- `wf_D = conj_split_3[wf_classical_domain_def]`: (1) sig, (2) distinct names, (3)
  `∀a. wf_classical_action_schema a`. So **`wf_D(3)`**.
- `wf_P = conj_split_5[wf_classical_problem_def]`: (4) `∀f∈init. wf_fmla_atom objT f ∨
  wf_func_assign f`, (5) `wf_fmla objT (goal P)`.
- `wf_classical_action_schema (SimpleActionSchema h b) = wf_action_head h ∧
  wf_simple_action_body (ty_term (map_of (parameters h)) constT) b`; the
  `ast_classical_action_schema_cases_unfold` case rule fully decomposes
  `SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff)` (needs `Let_def`).
- `ac_tyt a ≡ ty_term (map_of (ac_params a)) constT`; in a grounded problem `constT`/`objT` are
  `(λx. None)` (`constT_empty`/`objT_empty`).
- `wf_func_assign (Atom (numericEqAtm (FunctionExpr l)(ConstantExpr r))) = … | _ = False`.
- `resolve_classical_action_schema` is the classical resolver (`resolve_action_schema` is the
  continuous one — do not use it here).
- `name = String.literal`; `STR ''+'' + …` is literal append. `String_Utils.thy` has
  `inj_prepend` / `append_eq_append_conv_lit` but is **awkward to import into PDDL_to_STRIPS**
  (see §3) — prove tiny string facts inline if needed.
- **DROPPED** the old `AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics` dependency; STRIPS
  target is the AFP `Verified_SAT_Based_AI_Planning` format (`name strips_problem`,
  `is_serial_solution_for_problem`).

## TARGET (decided earlier)
Dual backend, shared trusted core = the verified PDDL plan validator (`valid_classical_plan2`):
- **Propositional** problems → STRIPS / AFP verified SAT planner. Numeric-freeness
  (`Numeric_Free`) is the input restriction enabling this branch; the WF translation is proven,
  plan-equivalence (§A) is next.
- **Numeric** problems → (future) SMT backend; untrusted plan checked by the verified validator,
  no-plan via certifying (Alethe) proof. See the comment in `Base/Numeric_Free.thy`.

## RELATED MEMORY
`project_pddl_to_strips_new_semantics`, `project_certificate_grounds_pn_not_pr` (bridge
complete), `project_unrefactored_files`, `project_relaxation_refactor_pipeline_wip`. Full
reachability/certificate writeup: `WIP_reachability_datalog.md`.
