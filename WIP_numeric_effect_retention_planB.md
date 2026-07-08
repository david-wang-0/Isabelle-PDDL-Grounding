# WIP Plan — Faithful numeric-effect retention (Option B)

Goal: let the numeric-fluent-retaining grounder (`ground_via_cert_numeric_dfs`) accept a PDDL
problem that carries numeric **effects** (e.g. `(decrease (fuel ?c) 1)`) and emit a grounded
problem that **retains those effects verbatim**, while keeping the classical pipeline's
plan-equivalence intact. Demonstrated on `Running_Example_Numeric.thy` (a `fuel` fluent added to
the Helmert-2009 running example).

## Root cause (verified empirically against the code)

By design, **def-translate keeps P⇩T's numerics** (real semantics) and *adds* the propositional
`def(fuel,…)` predicates/facts for the datalog: `def_translate_atom` only rewrites the definedness
atoms `numericEqAtm (FunctionExpr p) (FunctionExpr p)` (the `eq x x` from def-normalization) into
`def(fuel)`, and leaves `numericGEAtm` comparisons, `NumericEffect`s, and the `(= fuel 10)` init
assignments untouched. That is the **correct** design for faithful retention — do NOT change
def-translate.

The datalog needs a numeric-free P⇩R, and relaxation is *mostly* already doing that:
- `relax_lit` (`Grounding_Common/Common/Formula_Utils.thy`) **already** maps every numeric
  comparison atom (`numericGEAtm`/`numericEqAtm`/`numericLessAtm`/…) to `¬⊥` — so relaxed
  **preconditions** and the relaxed **goal** (via `relax_conj`) are numeric-free. ✓

The only two numeric leaks into P⇩R are:
1. `relax_eff (Effect a b ne) = Effect a [] ne` — keeps `ne` (numeric effects). ✗
2. `relax_prob` sets `init = init P` verbatim — keeps the `(= fuel 10)` `numericEqAtm` assignments.
   ✗ (P⇩R needs only the propositional init + the `def(fuel)` facts def-translate already appended.)

Consequences on `Running_Example_Numeric` (verified):
- `dl_certified_model_dfs … = True` (certificate is fine),
- `grounding_checks_exec my_P⇩T_num (fst my_cert_num) = False` — `ops_no_num` (P⇩T's reachable ops
  have no numeric effects) is violated (drive keeps `Decrease`); `init_props` is likewise violated
  (init keeps `(= fuel 10)`),
- `num_free_prob (relax_prob P⇩T)` is violated on **effects** (relax_eff keeps `ne`) and **init**
  (relax_prob keeps the assignments) — but NOT on preconditions/goal (`relax_lit` handles those).

Also confirmed: `Numeric_Grounder.thy` uses neither `ops_no_num` nor `init_props` → the re-base is
mechanical.

## Why Option B (over Option A)

The two lossy possibilities live in stages with different semantic contracts:
- **Definedness_Translation is plan-*equivalent*** (`def_translate_valid_plan_iff` is an `iff`).
  Dropping `neffs` there (Option A) would make it an over-approximation → breaks that `iff` and the
  end-to-end `ground_cert_plan_valid_iff`, and degrades "retention" to the definedness bit only.
- **Relaxation is already an over-*approximation*** (one-directional `relax_achievables` bridge).
  A numeric effect contributes **zero** propositional facts, so dropping `ne` in `relax_eff` leaves
  the datalog's derivable facts unchanged — reachability soundness is untouched. This is the cheap,
  correct place for the lossiness.

So Option B keeps `P⇩T` exact (numeric effects retained → faithful fluent retention) and moves the
numeric-freeness needed by the *datalog* into relaxation, where it belongs. The cost is that the
*numeric grounder* must stop requiring `ops_no_num`/`init_props` (those are the propositional
grounder's needs), which is sound because its plan-preservation rests on
`numeric_ground_ac π n = res_inst π` *exactly* and never used them.

## Phases

### Phase 1 — Relaxation strips residual numeric effects + init  (`PDDL_Relaxation`, stage) — DONE ✅ (build green)

Done + verified (`isabelle build Classical_PDDL_Relaxation` EXIT 0):
- `relax_eff (Effect a b ne) = Effect a [] []` (+ `numeric_effects (relax_eff e) = []` selector) in
  `Grounding_Common/PDDL_Relaxation/PDDL_Relaxation.thy`.
- `relax_prob` init `= filter is_predAtom (init P)` (+ `relax_prob_sel` init selector) in
  `_Locales.thy`.
- wf/syntax (`_.thy`): `relax_wf` init obligations via `distinct_filter` / `set_filter`; `rx_I`
  weakened `px.I = I` → `fst px.I = fst I` (via `filter_filter`); `relax_eff_wf` unchanged.
- semantics (`_Semantics.thy`): dropped the `snd` invariant — `rx_enabled` no longer assumes
  `snd M = snd M'` (numeric consumers trivial: relaxed `numeric_effects = []`); **`rx_exec_snd`
  deleted** (relaxation no longer preserves the valuation); `rx_path_right` tracks only `fst ⊆ fst`;
  `relax_achievables`/`relax_applicables` drop the `snd` arg. Soundness unchanged: numeric
  effects/init are propositionally inert, so `relax_achievables` (real ⊆ relaxed) still holds.

(original phase text:)
### Phase 1 (spec) — Relaxation strips residual numeric effects + init  (`PDDL_Relaxation`, stage)

Two edits in `Classical_PDDL_Relaxation_Locales.thy` (preconditions/goal already handled by
`relax_lit`):
- `relax_eff (Effect a b ne) = Effect a [] ne` → `Effect a [] []` (drop numeric effects too).
- `relax_prob`: `init = init P` → `init = filter num_free_fmla (init P)` (keep the propositional
  init + `def(fuel)` facts, drop the `(= fuel 10)` `numericEqAtm` assignments).
- Re-verify the relaxation semantics/wf: `relax_wf`, `relax_normed`, `relax_achievables`,
  `relax_applicables`, and that `relax_prob` is now `num_free_prob`. Soundness argument: numeric
  effects and numeric init assignments are propositionally inert (contribute no `predAtom` facts),
  so the monotone datalog closure (`relax_achievables`: real ⊆ relaxed) is unchanged; wf of the
  smaller effect/init is immediate. Empirically re-check `value "num_free_prob my_P⇩R_num" = True`.

### Phase 2 — Split off `wf_grounder_num`  (`Grounded_PDDL`, stage) — DONE ✅ (build green)

Done + verified (`isabelle build Classical_Grounded_PDDL` EXIT 0): `locale wf_grounder_num = grounder
+ ⟨9 assumptions⟩` (all except `init_props`/`ops_no_num`); `locale wf_grounder = wf_grounder_num +
assumes init_props ops_no_num`. The propositional grounder proofs (`in wf_grounder`) and all
sublocales compile unchanged (inheritance gives them everything). Gotcha: a `\<^theory>` antiquotation
to a downstream theory in doc text = "Unknown ancestor theory" — use plain text.

### STATUS (2026-07-07): Phases 1 & 2 DONE + VERIFIED. Reorg step DONE + GREEN — the only two shared lemmas the numeric grounder needs (`plan_in_ops`, `restore_map_entry`) now live in `context wf_grounder_num` (verified: `Classical_Grounded_PDDL.thy` fully_processed + consolidated, 0 errors). The earlier "deep reuse of restore_wf_pa/alt_covered/exec_covered/i_covered" claim was an over-estimate — those are used only by the *propositional* grounder; the numeric grounder core reuses ONLY `plan_in_ops` + `restore_map_entry`. Now doing Phase 4 with the **sibling** structure below (avoids the dedup).

**Chosen Phase-4 structure (siblings, NOT extension — this is what avoids the dedup):**
- `certified_reachability_base = normalized_problem_rx + fixes M dc + assumes px_numfree nonempty cert` — holds ALL shared machinery (`cert_facts'`/`cert_ops'` defs, `all_facts_super`, `all_ops_super`, `certified_facts`, the 5 coverage `_l` lemmas). NO wf_grounder interpretation.
- `certified_reachability_num = certified_reachability_base + assumes grounding_cert_num: numeric_grounding_checks M` — adds `sublocale ⊆ wfg_num: wf_grounder_num` (9 shows) + `numeric_ground_via_cert` machinery. ONLY wfg_num.
- `certified_reachability = certified_reachability_base + assumes grounding_cert: grounding_checks M` — adds `init_props_l`/`ops_no_num_l` + `sublocale ⊆ wfg: wf_grounder` (12 shows). ONLY wfg.
- `certified_reachability` and `certified_reachability_num` are SIBLINGS (both extend base, neither extends the other) → no single locale interprets both `wf_grounder` and `wf_grounder_num` → no `ground_prob` dedup. Propositional pipeline keeps `cr.wfg.ground_prob`; numeric pipeline uses `cr.wfg_num.numeric_ground_prob`.

**Phase 4 blocker (why 3–6 were reverted):** re-basing the numeric grounder onto `wf_grounder_num`
and splitting `certified_reachability`/`grounding_checks` hit two coupled problems:
1. **Locale-interpretation dedup.** With `certified_reachability` interpreting BOTH `wfg_num:
   wf_grounder_num` and `wfg: wf_grounder` (sharing the `grounder` base at the same params), the
   shared `grounder` constant `ground_prob` resolves only under `wfg_num`, so `cr.wfg.ground_prob`
   becomes undefined — breaking the propositional P⇩G_cert lemmas AND the whole STRIPS pipeline
   (`Grounding_Pipeline_STRIPS`, `_Executable`) which pervasively use `cr.wfg.ground_prob`.
2. **The numeric grounder deeply reuses `wf_grounder`-specific lemmas** — not just `ops_no_num`/
   `init_props` (the two it doesn't need), but a large shared set: `restore_map_entry`,
   `plan_in_ops`, `restore_wf_pa`, `alt_covered`, `exec_covered`, `i_covered`, `ground_pa`
   machinery, etc. These are proven `in wf_grounder`, so `context wf_grounder_num` can't see them.

**What Phase 3–6 actually requires (the real remaining work):** a substantial reorganization of
`Classical_Grounded_PDDL.thy` to move ALL the shared, numeric-freeness-independent lemmas (the
restore/coverage/plan-in-ops machinery — everything the numeric grounder reuses) DOWN from
`wf_grounder` into `wf_grounder_num`, leaving only the genuinely propositional lemmas (`ground_fmla`
faithfulness, `ground_ac_wf`, etc.) in `wf_grounder`. Then re-base the numeric grounder + do the
`certified_reachability_num`/`wfg_num` split WITHOUT the dedup (either make `wf_grounder` NOT share
the `grounder` interpretation with `wfg_num` on the same locale, or give the propositional pipeline
`cr.wfg_num.ground_prob` throughout). This is a focused day of stage-reorg + re-verification, best
done fresh — NOT a quick push.

### PHASES 3 & 4 DONE + GREEN (2026-07-07)

Verified in jEdit (`Numeric_Grounder.thy` fully_processed + consolidated, 0 errors, 1432 cmds):
- **Certificate split (3 cert files), sibling structure:** `_Locales.thy` now defines
  `numeric_grounding_checks` (5 coverage conjuncts) + `grounding_checks = numeric_grounding_checks
  \<and> init_props \<and> ops_no_num`; locales `certified_reachability_base` (shared: `px_nfr`,
  `cert_facts'`/`cert_ops'`), `certified_reachability_num = base + numeric_grounding_checks`,
  `certified_reachability = base + grounding_checks` (SIBLINGS). `Classical_Certified_Grounding.thy`
  moved the superset lemmas (`certified_eq_px_achievable`, `all_facts_super`, `px_applicable_super`,
  `all_ops_super`) into `context certified_reachability_base`. `_Semantics.thy` gained
  `sublocale certified_reachability_num \<subseteq> wfg_num: wf_grounder_num` (10 shows) alongside the kept
  `sublocale certified_reachability \<subseteq> wfg: wf_grounder` (12 shows); the 5 coverage `_l` lemmas are
  duplicated per sibling (one-liners). NO dedup — the propositional STRIPS pipeline keeps
  `cr.wfg.ground_prob` verbatim (certified_reachability unchanged as a locale predicate).
- **Numeric cert block re-pointed** (`Numeric_Grounder.thy`): new `certified_reachability_num_i`
  (mirror of `certified_reachability_i` but discharging only `numeric_grounding_checks`); the cert
  block's anonymous context assumes `grounding_cert_num: normalized_problem_rx.numeric_grounding_checks
  P\<^sub>T M`; `numeric_wf_ground_cert_problem`/`numeric_ground_cert_plan_valid_iff` now interpret
  `cr: certified_reachability_num` and use `cr.wfg_num.numeric_ground_prob_wf` /
  `cr.wfg_num.numeric_valid_classical_plan_iff`.
  - **GOTCHA (fixed):** `certified_reachability_num_i` must prove `normalized_problem_rx P\<^sub>T` INLINE
    (from `restrict_prob`/`wf` via `normalization_wf`/`def_translate_prob_wf_compact` etc.), NOT reuse
    `P_T_normalized_problem_rx` — that lemma is stated inside the propositional cert context, so
    externally it carries the FULL `grounding_checks` as a premise, which the numeric path lacks.
  - **GOTCHA (fixed):** inside `context ast_classical_problem`, write `ast_classical_problem.relax_prob
    P\<^sub>T` / `ast_classical_problem.const_names (...)` — a bare `relax_prob P\<^sub>T` reads `relax_prob` as the
    locale's own (already applied to `P`) and clashes (`operator not of function type`).

### Phase 4 (crux, DONE — spec kept for reference) — Numeric `certified_reachability` + `grounding_checks`  (`Reachability_Analysis`, stage)

`grounding_checks M` (in `Classical_Certified_Grounding_Locales.thy`) is a 7-conjunct AND whose LAST
TWO conjuncts are exactly `init_props` (`∀f∈init. is_predAtom f`) and `ops_no_num`
(`∀π∈cert_ops. numeric_effects … = []`). `certified_reachability` assumes `grounding_cert:
grounding_checks M` and `sublocale certified_reachability ⊆ wfg: wf_grounder` discharges all. Split:
- `numeric_grounding_checks M` = the first 5 conjuncts; redefine `grounding_checks M =
  numeric_grounding_checks M ∧ init_props_check ∧ ops_no_num_check`.
- `locale certified_reachability_num = normalized_problem_rx + fixes M dc + assumes px_numfree
  nonempty cert (grounding_cert_num: numeric_grounding_checks M)`; move the SHARED lemmas
  (`px_nfr`, `certified_facts…`, `all_facts_super`, `all_ops_super`, `facts_wf_l`, `ops_wf_l`,
  `effs_covered_l`, `pres_covered_l`, `goal_covered_l`) into it; `sublocale certified_reachability_num
  ⊆ wfg_num: wf_grounder_num` (9 shows).
- `locale certified_reachability = certified_reachability_num + assumes ⟨the 2 extra checks⟩`; keep
  `init_props_l`/`ops_no_num_l` + `sublocale … ⊆ wfg: wf_grounder` (discharge the 2 extra).
- Executable: `numeric_grounding_checks_exec` (first 5 conjuncts) + `_eq` bridge, in
  `Grounding_Pipeline_STRIPS_Executable.thy`.

NOTE — Phase 4 spans the stage's **three files** (preserve the structure): `_Locales`
(`numeric_grounding_checks` def; `grounding_checks = numeric ∧ 2`; `certified_reachability_num`
locale + `certified_reachability = _num + 2`; move `px_nfr`, `cert_ops'`/`cert_facts'` defs into
`_num`), `Classical_Certified_Grounding.thy` (the certificate-soundness `all_facts_super`,
`all_ops_super`, `certified_facts` → `_num` context; they don't use the 2 checks), and
`_Semantics` (5 `_l` lemmas → `_num`; `init_props_l`/`ops_no_num_l` stay in `certified_reachability`;
`sublocale certified_reachability_num ⊆ wfg_num` (10 shows) + keep `sublocale certified_reachability
⊆ wfg` (12 shows, reusing the moved `_l` lemmas + the 2)).

### Phase 2 (spec) — Split off `wf_grounder_num`  (`Grounded_PDDL`, stage)

- Introduce `locale wf_grounder_num = grounder + ⟨all wf_grounder assumptions EXCEPT ops_no_num,
  init_props⟩`, and redefine `wf_grounder = wf_grounder_num + assumes init_props ops_no_num` (so the
  propositional grounder is unchanged — it still sees both).
- **Open check 2:** confirm the numeric grounder's proofs never use `ops_no_num`/`init_props`
  (grep `Numeric_Grounder.thy` for those names; the wf proof used `wf_resolve_instantiate` off
  `ops_wf`, the plan-preservation used the exact `res_inst` correspondence — neither should need
  them). If a stray use exists, fix it.

### Phase 3 — Re-base the numeric grounder  (`Numeric_Grounder.thy`, pipeline)

- Change `context wf_grounder` → `context wf_grounder_num` for the numeric grounder core
  (`numeric_ground_prob` wf + plan-preservation). The `png` sublocale and the correspondence lemmas
  move with it.
- The cert block: the numeric `numeric_P⇩G_cert` + `numeric_wf_ground_cert_problem` +
  `numeric_ground_cert_plan_valid_iff` must be re-pointed at a numeric certified-reachability
  interpretation (see Phase 4).

### Phase 4 — Numeric certified-reachability + grounding-checks variant  (`Reachability_Analysis`, stage; `STRIPS_Executable`, pipeline)

- Add `sublocale certified_reachability ⊆ wfg_num: wf_grounder_num P cert_facts' cert_ops'`
  (discharges the weaker assumption set — everything except the two dropped clauses, which we no
  longer need). Keep the existing `wfg: wf_grounder` sublocale for the propositional path.
- Add a numeric grounding-checks variant that omits the `ops_no_num` + `init_props` conjuncts:
  abstract `numeric_grounding_checks` (`Classical_Certified_Grounding_*`) and executable
  `numeric_grounding_checks_exec` (`Grounding_Pipeline_STRIPS_Executable`), plus the
  `_eq` bridge (mirroring `grounding_checks_exec_eq`).

### PHASE 5 DONE + GREEN (2026-07-07)

Verified (`Grounding_Pipeline_Numeric_Executable.thy` fully_processed + consolidated, 0 errors; STRIPS_Executable
loaded clean as import). In `Grounding_Pipeline_STRIPS_Executable.thy`: added `numeric_grounding_checks_exec`
(the 5 coverage conjuncts, `[code]`), `numeric_grounding_checks_exec_eq` (bridge to
`normalized_problem_rx.numeric_grounding_checks`), and `numeric_ground_via_cert'`/`_dfs` (twins of
`ground_via_cert'`/`_dfs` gating on the WEAKER `numeric_grounding_checks_exec`, returning just the re-checked
cert pair `(M, dc)`). In `Grounding_Pipeline_Numeric_Executable.thy`: `numeric_ground_by_cert_eq` now takes
`numeric_grounding_checks_exec` (feeds `numeric_P⇩G_cert_def[OF pnf ne cert gc']` with
`normalized_problem_rx.numeric_grounding_checks`); `ground_via_cert_numeric`/`_dfs` re-pointed onto
`numeric_ground_via_cert'`/`_dfs` (destructure `Some (M, dc)` directly, `split: option.splits prod.splits`).
Propositional STRIPS path untouched (pure additions). REMAINING: Phase 6 (example + build + run).

### Phase 5 (spec) — Wire the executable numeric path  (`Grounding_Pipeline_Numeric_Executable.thy`, pipeline)

- Introduce `numeric_ground_via_cert'`/`_dfs` (twins of `ground_via_cert'`/`_dfs`) that gate on
  `numeric_grounding_checks_exec` (not the strict `grounding_checks_exec`) and call
  `numeric_ground_by_cert`; re-point `ground_via_cert_numeric`/`_dfs` onto them. `num_free_prob R`
  still gates (now satisfied thanks to Phase 1). Update `numeric_ground_by_cert_eq` and the
  `ground_via_cert_numeric_*_eq` theorems to the numeric certified-reachability discharge.

### PHASE 6 DONE + GREEN (jEdit-verified 2026-07-07) — the fluent example evaluates end-to-end

**KEY MID-PHASE FINDING — `wf_grounder_num` had to become genuinely minimal.** The first attempt
(numeric_grounding_checks = the 5 coverage conjuncts) FAILED: `value "numeric_grounding_checks_exec
my_P⇩T_num …" = False`, because `pres_covered`/`covered` (`Grounding_Common/Grounded_PDDL/Grounded_PDDL.thy:10`)
returns `False` on ANY numeric comparison atom (`_ ⇒ False`), and the drive op RETAINS its
`numericGEAtm (fuel c) 1` guard in `P⇩T`. Since the numeric grounder core uses NONE of the
coverage/facts assumptions (grep of `Numeric_Grounder.thy`: no `pres_covered`/`effs_covered`/
`goal_covered`/`facts_wf`/`all_facts`/`facts_dist`/`covered`), the fix was to make `wf_grounder_num`
truly minimal — **only 4 assumptions**: `wf_problem`, `ops_dist`, `all_ops`, `ops_wf`. The 6
coverage/facts assumptions moved DOWN into `wf_grounder` (which keeps all 12 → propositional grounder
unchanged). Consequently `numeric_grounding_checks M ≡ (∀π∈set(cert_ops_of M). wf_classical_plan_action π)`
(a SINGLE decidable re-check), `grounding_checks` reverted to its original standalone 7-conjunct def
(so `grounding_checks_exec_eq` is untouched), the `wfg_num` sublocale shrank 10→4 shows, and
`numeric_grounding_checks_exec` shrank 5→1 conjunct. Files touched: `Classical_Grounded_PDDL.thy`
(locale split reorder — green, 1894 cmds), the 3 cert files (`_Locales` defs + `_Semantics` `wfg_num`
4 shows, drop 4 numeric `_l` lemmas — green), `Grounding_Pipeline_STRIPS_Executable.thy`
(`numeric_grounding_checks_exec` 1 conjunct — green).

**Running_Example_Numeric.thy — green, all `value`s evaluate (added to ROOT):**
- `grounding_checks_exec my_P⇩T_num (fst my_cert_num) = False` (propositional check fails: `P⇩T` retains
  the `decrease`/`fuel>=1` → `ops_no_num`/`init_props`/`covered` fail),
- `numeric_grounding_checks_exec my_P⇩T_num (fst my_cert_num) = True` (the ops-wf re-check passes),
- `dl_certified_model_dfs … = True` (cert accepted on the numeric-free `P⇩R`; reachability carries the
  `Defined_fuel(c)` predicates from def-translate),
- `ground_via_cert_numeric_dfs (λ_. my_cert_num) my_problem_num = Some (Problem …)` — the grounded PDDL
  RETAINS the fluent: each reachable drive becomes a NULLARY schema `SimpleActionSchema (ActionHead ''n'' [])`
  whose `Effect`'s third slot is `[NumericEffect Decrease (PNE (Func ''fuel'') [term.CONST (Obj ''c3'')])
  (ConstantExpr 1)]` — 18 retained `NumericEffect`s across 73 grounded schemas.

**BUILD + SML RUN + rat printing — ALL DONE + GREEN (2026-07-07).**
- Full `isabelle build -e Classical_Grounding` EXIT 0 (3:31 elapsed; NO `-d` flags — graph-lib+repo are
  registered components). The export (`SMLCodebase_DFS/code/PDDL_SAT_Planner_DFS_Exported.sml`) regenerated.
- `rat` printing: added `Rat.quotient_of` to `Planner_Export.thy`'s `export_code` (exports cleanly, 15 refs);
  `pddl_printer.sml` `numExprStr` now decodes `ConstantExpr r` via `E.quotient_of` → `E.integer_of_int` →
  `IntInf.toString` (integer if den=1, else `n/d`). No more `#num`.
- SML binary recompiled (`make`, MLton; only pre-existing non-exhaustive-match warnings) →
  `bin/pddl_ground_planner_dfs`. Ran `ground examples/running_example_numeric/domain.pddl
  examples/running_example_numeric/problem.pddl` (nmo on PATH) EXIT 0 → 302-line grounded PDDL.
  (The SML codebase is now a SINGLE top-level `SMLCodebase/`; examples live in per-example folders
  `examples/running_example{,_numeric}/{domain,problem}.pddl`; build artifacts are gitignored.)
- **The grounded PDDL retains fluents end-to-end:** `(:functions (fuel ?a0 - object))`; each of 18 nullary
  `(:action N :parameters ())` drives keeps `(>= (fuel cK) 1)` in its precondition AND `(decrease (fuel cK) 1)`
  in its effect (rat prints as `1`); grounded `:init` keeps `(= (fuel c1) 10)` etc. (73 grounded actions total,
  0 `#num` placeholders left).

### Phase 6 (spec) — Example, build, run

- Re-run `Running_Example_Numeric.thy`: `grounding_checks`-numeric and the final grounding must now
  return `Some`, and the printed grounded PDDL must retain the `fuel` function decl **and** the
  `(decrease (fuel c) 1)` effect (as a real `NumericEffect`) on each grounded drive.
- Add `Numeric_Grounder`/example to ROOT as needed; `isabelle build -e Classical_Grounding` green.
- Extend `pddl_printer.sml` already handles numeric effects; recompile the SML binary and run
  `ground` on `examples/domain_numeric.pddl` + `problem_numeric.pddl` (kept for this) to show the
  end-to-end fluent-retaining grounding.

## Open questions / empirical checks (resolve during implementation)

1. Does `def_translate_fmla` fully *replace* numeric comparison atoms in conditions with `def(…)`
   predicates (→ preconditions numeric-free), or keep them? Inspect `my_P⇩R_num`/`my_P⇩T_num`
   preconditions. If kept, `num_free_prob` needs the condition side handled too.
2. Do any numeric-grounder proofs actually use `ops_no_num`/`init_props`? (Expected: no.)
3. Does dropping `init_props` for the numeric grounder require anything of `numeric_ground_prob`'s
   init handling? (`numeric_ground_prob` keeps `init P` verbatim; wf of init comes from
   `wf_problem`, not `init_props` — expected fine.)

## Files touched

- Stage: `PDDL_Relaxation/*` (relax_eff), `Grounded_PDDL/Classical_Grounded_PDDL.thy`
  (wf_grounder_num split), `Reachability_Analysis/Classical_Certified_Grounding_*`
  (wfg_num sublocale + numeric_grounding_checks).
- Pipeline: `Numeric_Grounder.thy`, `Grounding_Pipeline_STRIPS_Executable.thy`
  (numeric_grounding_checks_exec), `Grounding_Pipeline_Numeric_Executable.thy`,
  `Running_Example_Numeric.thy`, `SMLCodebase*` (rebuild only).

## Rollback

Each phase is independently revertable; the propositional grounder / STRIPS path is never modified
(wf_grounder keeps both assumptions; `grounding_checks_exec` unchanged; `ground_by_cert` unchanged).
`relax_eff` dropping `ne` is the only change that touches a shared path — its safety rests on
numeric effects being propositionally inert.
