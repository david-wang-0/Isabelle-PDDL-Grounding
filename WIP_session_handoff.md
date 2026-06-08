# Session handoff (2026-06-08, updated)

Status snapshot for resuming in a fresh session. Covers the certificate→grounder bridge,
numeric-freeness, the PDDL→STRIPS port (WF complete; **semantics preservation now FULLY proven —
`Classical_PDDL_to_STRIPS.thy` is 0 sorry, 0 errors, consolidated**), and the pipeline wiring.

> **§A COMPLETE (2026-06-08, this session).** `Classical_PDDL_to_STRIPS.thy` now has **0 sorry**.
> `execute_commute` and `restore_pddl_plan_valid` are proven, so `valid_plan_iff` holds.
> **Important restatement:** `restore_pddl_plan_valid` is now the *existence* form
> `is_serial_solution_for_problem as_strips ops ⟹ ∃πs. valid_classical_plan2 πs`, NOT the literal
> `valid_classical_plan2 (restore_pddl_plan ops)`. The literal form is FALSE: `execute_serial_plan`
> halts at the first non-applicable operator, so a "solution" may carry trailing non-enabled ops,
> whereas `valid_classical_plan2` requires every action enabled. The existence form is exactly what
> `valid_plan_iff` (and the pipeline) needs. See memory `project_restore_pddl_plan_existence`.
> Remaining: pipeline wiring §7 (instantiate `strips_encodable_problem` for `P\<^sub>G_cert cert`)
> to close the two `strips_plan_*_cert` `oops` in `Grounding_Pipeline_STRIPS.thy`.

> **Session split (2026-06-08).** The base session was split (mirrors `Continuous_Planning_Base`)
> so jEdit can load a stable external heap while the shared theories stay editable:
>
> - **`Tree_Decomp_Grounding_Base`** — NEW folder `Tree_Decomp_Grounding_Base/` (ROOT only, no
>   `.thy`), `= HOL +`: every EXTERNAL import (AFP `Classical_Planning`/`Continuous_Planning`/
>   `Verified_SAT_Based_AI_Planning` theories, `Propositional_Proof_Systems.*`, `HOL-Library.*`,
>   `Show`, `iq`). **This is the heap to load in jEdit** (`isabelle jedit -d . -l
>   Tree_Decomp_Grounding_Base`) so edited files' imports are all cached.
> - **`Tree_Decomp_Grounding_Common`** — folder `Common/` (was `Base/`), `=
>   Tree_Decomp_Grounding_Base +`: the editable project-local shared theories (supplements, utils,
>   `Normalization_Definitions`, `Numeric_Free`, DNF, `Graph_Funs`).
> - All downstream `imports Tree_Decomp_Grounding_Base.X` are now `…Common.X`; every sub-session +
>   the main `Tree_Decomp_Grounding` parent is `…Common`. Main `ROOT` gained `directories
>   "PDDL_to_STRIPS"`. `isabelle build -n -d .` resolves all three clean. Done via `isabelle-refactor`.
> - The STRIPS file was relocated earlier: `PDDL_to_STRIPS.thy` → `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy`
>   (theory `Classical_PDDL_to_STRIPS`). See memory `project_base_common_session_split`.

> **Pipeline split (2026-06-08).** The monolithic `Grounding_Pipeline.thy` is gone, split by
> numeric capability:
>
> - **`Grounding_Pipeline_Numeric.thy`** — the general pipeline for problems *with* numerics:
>   normalization → `def_translate` → relaxation → certificate-based reachability grounding,
>   ending at the grounded PDDL problem `P\<^sub>G_cert`. GREEN (`fully_processed` + `consolidated`,
>   0 errors). Now also imports `Tree_Decomp_Grounding_Common.Numeric_Free` directly (it lost that
>   transitively when the `PDDL_to_STRIPS` import moved out) and gained `ground_cert_num_free`
>   (`P\<^sub>G_cert` is numeric-free — this is the old §B, now DISCHARGED).
> - **`Grounding_Pipeline_STRIPS.thy`** — the numeric-free specialization: `imports
>   Grounding_Pipeline_Numeric PDDL_to_STRIPS`, re-opens the `ast_classical_problem` + `cert`
>   context, hosts `wf_as_strips_compact`, `P\<^sub>S_cert`, `wf_as_strips_cert` (proven), and the
>   two `strips_plan_*_cert` `oops` (the §A blockers). 0 errors.
>
> `ROOT` lists both; `Running_Example` now imports `Grounding_Pipeline_Numeric`.
> Cross-context note: `P\<^sub>G_cert`/`reconstruct_plan_ground_cert` are defined in the base
> cert-context, so in the STRIPS file they take `cert` explicitly (`P\<^sub>G_cert cert`), and base
> facts re-export with `admissible_cert`/`grounding_cert` as leading premises
> (`...[OF admissible_cert grounding_cert assms]`). Done via the `isabelle-refactor` skill.

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

### 2. `Common/Numeric_Free.thy` — green (in `Common/ROOT`, session `Tree_Decomp_Grounding_Common`)
Propositional-fragment restriction. Key names (used heavily by the STRIPS port):
- `is_numeric_atom`, `num_free_fmla`, `num_free_eff`, `num_free_ac` (def, global),
  `(in ast_classical_domain) num_free_dom` = `∀a∈set(actions D). num_free_ac a`,
  `(in ast_classical_problem) num_free_prob` = `num_free_dom ∧ num_free_fmla (goal P) ∧
  (∀f∈set(init P). num_free_fmla f)`.
- locales `numeric_free_domain` / `numeric_free_problem` (problem sublocales domain via
  `num_free_prob_def`). Helper `num_free_fmla_un_and`.
- Numeric-freeness is an INPUT restriction checked + carried through, NOT a grounder guarantee.

### 3. `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy` — **WF PORT COMPLETE, 0 errors**
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
  `Tree_Decomp_Grounding_Common.String_Utils`, even though sibling Common files import it; the
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

**Semantics-preservation (§A) — COMPLETE (2026-06-08).** `strips_model` is defined for real; the
throwaway `pddl_model ≡ undefined` / old `valid_plan` `oops` block was replaced. All of
`execute_commute`, `goal_bridge`, `restore_pddl_plan_valid` are now proven — **0 sorry** in the
file. See §A below.

## ✅ DONE (2026-06-07/08): §B + §C — the grounding pipeline is GREEN (and now split)

The pipeline (since 2026-06-08 split into `Grounding_Pipeline_Numeric.thy` +
`Grounding_Pipeline_STRIPS.thy`; see the top blockquote): **0 errors, 0 sorry**; the only
remaining `oops` are `strips_plan_reconstruct_cert` / `strips_plan_iff_cert` (in
`Grounding_Pipeline_STRIPS.thy`, the STRIPS-cert branch), which genuinely need §A (the
`valid_plan_iff` plan-equivalence still has `sorry`s in `Classical_PDDL_to_STRIPS.thy`).

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

### A. STRIPS semantics preservation (`Classical_PDDL_to_STRIPS.thy`) — ✅ COMPLETE (0 sorry)

The whole file is `fully_processed` + `consolidated`, 0 errors, 0 sorry. The only thing left for
the pipeline is the wiring in §7 below (instantiate the locale for `P\<^sub>G_cert`). `world_model =
logical × numeric` (a PAIR); the propositional state lives in `fst`.

**PROVEN (0 sorry):**
- `strips_model :: world_model ⇒ name strips_state` defined for real; `strips_model_props`
  (`strips_model_vT/vF/vpos/vneg/None`) and `strips_init_eq_model` (`strips_init = strips_model I`).
  Also fixed a soundness bug in `empty_state` (negative-variable init was inverted).
- New locale `strips_encodable_problem = grounded_normalized_numeric_free_problem + assumes
  nonempty_pred_names` (predicate names ≠ `STR ''''`, so `vpos/vneg` never collide with the static
  markers `v⇩T/v⇩F`). All the semantics lemmas live here.
- Plan-action **simulation substrate**: `strips_model_lit_inst` (literal/instantiation bridge),
  `pre_applicable_iff`, `enabled_applicable` (`valuation M ⊨⇩m precondition (the (res_inst a)) ⟷
  is_operator_applicable_in (strips_model M) (strips_pa a)`), `sim_serial` (execution simulation),
  `sim_ops`.
- **Forward theorem `valid_plan_right`**: `valid_classical_plan2 πs ⟹
  is_serial_solution_for_problem as_strips (map strips_pa πs)`. Restated on `valid_classical_plan2`
  (clean simp rules `valid_classical_plan2_alt` / `…_from2_Nil/Cons` in `PDDL_Sema_Supplement`).
- Generic helpers `un_and_map_formula`, `map_sem_un_and`, `inst_precondition`, `inst_effect_sel`.
- `strips_pa` moved above the locale so it is in scope; the broken throwaway tail
  (`wf_state`/`pddl_model ≡ undefined`/old `valid_plan` `oops`) was removed.

**ALL PROVEN (2026-06-08, this session):**
1. `execute_commute`: discharged pointwise via `strips_var_cases` + new `execute_operator_var`
   (per-variable wrapper over AFP `effect__strips_iii_a/b/c`) + the four `vpos/vneg_{add,del}_iff`
   effect bridges + `exec_adds_iff`/`exec_dels_iff` (nullary-atom membership survives instantiation,
   term→object via `inst_eff_list_iff`). The `fix_effect` add-precedence vs `apply_ground_actions`
   delete-then-add reconciliation is handled by a boolean case split in the `pos`/`neg` cases.
2. `goal_bridge`: proven (was done just before this session). Uses `lit_as_goal` + the
   `goal_no_conflict` locale assumption.
3. `restore_pddl_plan_valid` (reverse): proven as the **existence** form (see top blockquote) via
   the reverse-simulation lemma `sim_serial_rev` (induction on the op list; applicable case uses
   `execute_commute` + `applicable_enabled`, halting case takes the applicable prefix),
   `strips_op_has_pa` (`resolve_classical_action_schema_name` + `grounded_pa_nullary`), and
   `applicable_enabled` (`plan_action_enabled`'s numeric side-conditions are vacuous since
   `num_free_eff` forces the numeric effect list empty — `inst_no_numeric`,
   `numeric_effects_non_intrf_no_numeric_effects`). `valid_plan_iff` now proven.

**Pipeline wiring (§7, not yet done):** to close `strips_plan_*_cert` in
`Grounding_Pipeline_STRIPS.thy`, instantiate `strips_encodable_problem` for `P⇩G_cert cert`, which
needs `nonempty_pred_names` discharged at the grounder (predicate names are nonempty decimal
strings — `fact_names = map Pred (distinct_strings_lit …)`).

### B. Discharge numeric-freeness for the grounded problem `P_G` — ✅ DONE (2026-06-08)

`Grounding_Pipeline_Numeric.ground_cert_num_free` proves `num_free_prob P\<^sub>G_cert` (via the
`pg_eq: P\<^sub>G_cert = cr.wfg.ground_prob` rewrite + `cr.wfg.ground_prob_num_free`). That is what
lets `Grounding_Pipeline_STRIPS.wf_as_strips_cert` instantiate the STRIPS branch
(`grounded_normalized_numeric_free_problem`) — now proven.

### C. Finish the grounding pipeline (certificate grounding + STRIPS) — ✅ DONE (2026-06-07/08)

`restore_plan_def_translate_compact` defined; `ground_cert_plan_reconstruct` re-qualified onto
`P⇩N`; `ground_prob_normed` sorry filled; the `P⇩G_cert` / `ground_cert_plan_valid_iff` /
`wf_as_strips_cert` chain is proven, with the STRIPS-cert branch now requiring `num_free_prob`
(discharged by §B's `ground_cert_num_free`). Only §A keeps `strips_plan_*_cert` `oops`.

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
  no-plan via certifying (Alethe) proof. See the comment in `Common/Numeric_Free.thy`.

## RELATED MEMORY
`project_base_common_session_split` (Base→Common + external Base heap),
`project_pddl_to_strips_semantics_section` (§A details), `project_pddl_to_strips_new_semantics`,
`project_certificate_grounds_pn_not_pr` (bridge complete), `project_unrefactored_files`,
`project_relaxation_refactor_pipeline_wip`. Full reachability/certificate writeup:
`WIP_reachability_datalog.md`.
