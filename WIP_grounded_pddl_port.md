# WIP: porting the downstream tail (Reachability_Analysis + Grounded_PDDL) to the new classical API

Status as of **2026-06-05**. Authorized refactor of the pre-refactor "old-API" tail.

> **UPDATE 2026-06-05 — `Grounded_PDDL.thy` is now FULLY PROVEN (0 `sorry`, fully processed +
> consolidated, 0 errors).** All six headline theorems (`ground_dom_grounded`, `ground_prob_grounded`,
> `ground_dom_wf`, `ground_prob_wf`, `valid_classical_plan_iff`, `valid_classical_plan_left`) are
> proved on the pair world model. Key changes vs. the plan below: `covered` was restricted to
> predicate/equality atoms (no numerics); `wf_grounder` gained `init_props` + `ops_no_num`; the
> `D⇩G`/`P⇩G` selectors are deliberately **not** `[simp]`; conjunctive predicates use declared
> `[intro]`/`[dest]` rules; `list_all1` was deleted project-wide (use bounded `∀∈set`); and the big
> preserved "Stage 3 (deferred)" comment block has been deleted. The Stage-3 plan notes below are
> kept only as historical context.

## Goal

Port the two unrefactored downstream theories from the **old PDDL `ast_problem` /
set-world-model API** to the **new `ast_classical_problem` / pair-world-model API**, so the
reachability-certificate locales (and eventually the grounding pipeline) compile.

- `ast_problem` (locale, AFP PDDL) → `ast_classical_problem`
- action schema `Action_Schema n params pre (Effect a d)` →
  `SimpleActionSchema (ActionHead n params) (SimpleActionBody pre (Effect a d ne))`
  (`ast_effect` now has a 3rd field `numeric_effects`; `Domain` now has 5 fields incl.
  `functions`; `Ground_Action`→`GroundAction`)
- plan action `PAction` → `SimplePlanAction` (type `ast_classical_plan_action`)
- atom equality `Eq` → `eqAtm`; `name = String.literal`
- world model `object atom formula set` → `(set × (PNE ⇒ real option))`;
  `valuation M ⊨ φ` (set) → `valuation M ⊨⇩m φ` (pair); empty model `({}, Map.empty)`
- `achievable :: fact ⇒ bool` (`fact = predicate × object list`); lift to formula via
  `fact_to_facty f ≡ Atom (uncurry predAtm f)`
- `resolve_instantiate π` → `the (res_inst π)`; `wf_plan_action` → `wf_classical_plan_action`;
  `valid_plan` → `valid_classical_plan2`
- old PDDL `plan_action_path`/`execute_plan_action`/`plan_action_enabled` → classical
  versions in `Common/PDDL_Sema_Supplement.thy` (`execute_plan_action`/`plan_action_enabled`/
  `valid_classical_plan_alt` over the pair model; note `plan_action_enabled` now ALSO requires
  `numeric_effects_non_intrf` and `set (ast_effect_enumerate_rhs_primitive_numeric_expressions
  (effect a')) ⊆ dom (snd M)` — trivially true for our purely-propositional grounded effects).

## Session / folder restructure — DONE

Each is now its own session folder (mirrors `PDDL_Relaxation/` etc.):

- `Reachability_Analysis/` — `Reachability_Analysis.thy` (engine) + `Reachability_Certificate.thy`.
  `ROOT`: `session Reachability_Analysis = Tree_Decomp_Grounding_Base + sessions Grounded_PDDL`.
- `Grounded_PDDL/` — `Grounded_PDDL.thy`. `ROOT`: `session Grounded_PDDL = Tree_Decomp_Grounding_Base`.
- `ROOTS` lists both; top `ROOT` (`Tree_Decomp_Grounding`) has them under `sessions`, and keeps
  `PDDL_to_STRIPS`, `Grounding_Pipeline`, `Running_Example` as theories.
- `Grounding_Pipeline.thy` import: `Reachability_Analysis.Reachability_Analysis
  Grounded_PDDL.Grounded_PDDL PDDL_to_STRIPS`.
- `Reachability_Certificate.thy` imports `Reachability_Analysis Grounded_PDDL.Grounded_PDDL`.

**OPEN QUESTION (user, not yet decided):** should `Grounded_PDDL` live in the Base session
instead of its own? My recommendation: keep standalone — Base is the upstream foundation that
all normalization steps import; the grounder is downstream, so folding it into Base inverts the
layering. It only deps on Base, so a separate session is cheap.

**jEdit caveat:** new sessions are only picked up after a jEdit reload/restart. `Grounded_PDDL.thy`
processes fine as `Draft.*` because it only imports Base. `Reachability_Certificate.thy` needs
jEdit to know the `Grounded_PDDL` session before it resolves `Grounded_PDDL.Grounded_PDDL`.

## `Reachability_Analysis.thy` (engine) — DONE, 0 errors

- `context ast_problem` → `context ast_classical_problem`; `as_action_clause` ported to the new
  schema constructor; `all_derivs_of` yields `ast_classical_plan_action` (`SimplePlanAction`).
- `satisfies_cond` uses `valuation ({}, Map.empty) ⊨⇩m …`.
- `enumerate_orga` is `(in ast_classical_problem)`; code lemmas qualified `ast_classical_problem.*`;
  `ast_domain.subst_term.simps` → top-level `subst_term.simps`.
- `found_facts_achievable` restated `set (snd semi_naive_eval) = (λf. Atom (uncurry predAtm f)) \``
  `{f. achievable f}` (still `sorry` — that's the certificate's job to replace).
- Old example/`value` block (used `Action_Schema`/`Problem`/`PAction`) is commented out.

## `Grounded_PDDL.thy` — Stage 1+2 DONE (green); Stage 3 = the remaining work

**Stage 1 (constructors/types) + Stage 2 (naming + distinctness): complete & green.**
- `locale grounder = ast_classical_problem + fixes facts ops::ast_classical_plan_action list`.
- Name generation rewritten with `distinct_strings_lit` (no more `char list` `padl`/`show`):
  `fact_names ≡ map Pred (distinct_strings_lit (length facts))`,
  `op_names ≡ distinct_strings_lit (length ops)`. Distinctness `fact_names_dis`/`op_names_dis`
  PROVED (via `distinct_strings_lit_dist` + `distinct_map`/`inj_on`).
- `ground_fmla` (uses `eqAtm`), `ga_pre`/`ga_eff` (3-field `Effect … []`, no numerics),
  `ground_ac` (`SimpleActionSchema (ActionHead n []) (SimpleActionBody …)` via `the (res_inst π)`),
  `ground_dom` (5-field `Domain [] preds [] [] acs` :: `ast_classical_domain`),
  `ground_prob` :: `ast_classical_problem`, `op_map`, `restore_ground_pa` — all typecheck.
- `wf_grounder` assumptions ported; `wf_problem: wf_classical_problem`, `all_facts:
  fact_to_facty \` {a. achievable a} ⊆ set facts`, `ops_wf`/`facts_wf` use `∀x∈set …` (user
  prefers ∀ over `list_all` in specs — see memory). Sublocales `wf_ast_classical_problem P`,
  `dg: ast_classical_domain D⇩G`, `pg: ast_classical_problem P⇩G`.
- Code-setup `pddl_ground_code` trimmed to surviving defs.

**Stage 3 (the ~45 semantic correctness lemmas): TODO — this is the next session's task.**
- Currently the 6 headline results are `sorry`-d, in the "Stage 1+2" block near the top:
  `ground_dom_grounded : dg.grounded_dom`, `ground_prob_grounded : pg.grounded_prob`
  (in `grounder`); `ground_dom_wf : dg.wf_classical_domain`, `ground_prob_wf : pg.wf_classical_problem`,
  `valid_classical_plan_iff`, `valid_classical_plan_left` (in `wf_grounder`).
- **The full pre-refactor proofs are preserved verbatim in the big `(* ===== Stage 3 (deferred)
  … *)` comment block** further down. Port them in dependency order, deleting the duplicate
  `facts_len`/`ops_len`/`fact_names_dis`/`op_names_dis` (already proven up top) and the dead
  `ground_pred_cond`/`ground_ac_name_alt` (those funcs were removed).

### Stage 3 plan (dependency order, from the preserved block)

1. **Selectors** ("Alternative definitions"): `ga_pre_alt`, `ga_eff_alt`/`ga_eff_sel` (add `[]`
   numeric field), `ground_ac_sel` (`ac_name`/`ac_params`/`ac_pre`/`ac_eff`; `resolve_instantiate`
   → `the (res_inst …)`), `ground_dom_sel` (5-field), `ground_prob_sel`, `restore_ground_pa_alt`.
   NB selectors `ac_name`/`ac_params`/`ac_pre`/`ac_eff` exist for `ast_classical_action_schema`
   (used in `Normalization_Definitions.grounded_pa_nullary`) — confirm their exact source
   (likely abbreviations over `head`/`body` in Classical_Abstract_Syntax / PDDL_Sema_Supplement).
2. **Grounded output**: `acs_grounded`, `ground_dom_grounded`, `ground_prob_grounded`
   (target preds `grounded_pred`/`grounded_ac`/`grounded_dom`/`grounded_prob` from
   `Common/Normalization_Definitions.thy:328-347`).
3. **Well-formedness**: `gr_preds_dis/_wf`, `ground_ac_names`, `gr_acs_dis`, `wf_ops_resinst`,
   `gr_atom_wf`, `gr_fmla_atom_wf`, `ground_fmla_wf`, `ground_ac_wf`, `gr_acs_wf`,
   `ground_dom_wf`, `gr_init_dis/_wf`, `gr_goal_wf`, `ground_prob_wf`. (Uses classical
   `wf_classical_domain`/`wf_problem`/`wf_fmla_atom`/`wf_action_schema` in `Classical_Well_Formedness.thy`
   + `PDDL_Sema_Supplement.thy`; key helpers `wf_pa_refs_ac`, `res_aux`,
   `wf_classical_plan_action_simple`, `action_params_match_def`.)
4. **Semantics** (the deep part): sublocales `grounded_domain`/`grounded_problem`; `ground_init`,
   `covered_predAtom`, `ground_fmla_inj/_inv/_sem`, `ground_goal_sem`, `op_map_inv`/`ground_pa`,
   `ground_fmla_subst`/`ground_effect_subst`, `gr_pa_instantiation`, `ground_action_map_entry`,
   `resolve_ground_pa`, `resinst_ground_pa`, `ground_enabled_iff`, `effs_covered_alt`,
   `exec_covered`, `i_covered`, `execs_covered`, `path_covered`, `ground_action_exec_right`,
   `ground_plan_path_right`, **`valid_classical_plan_iff`** (right dir), `restore_wf_pa`,
   `ground_enabled_left`, `ground_exec_left`, `ground_plan_path_left`,
   **`valid_classical_plan_left`**.
   Old proofs used PDDL `valid_plan`/`plan_action_path`/`execute_plan_action`/`M ⊨⇩c⁼ φ`/
   set-`valuation ⊨`; classical replacements live in `Common/PDDL_Sema_Supplement.thy`
   (`valid_classical_plan_alt`/`execute_plan_action`/`plan_action_enabled` over the pair model,
   `valuation ⊨⇩m`, `valid_classical_plan_from2_*`, `wf_valid_classical_plan_alt`). Watch the new
   `plan_action_enabled` numeric side-conditions (discharge via empty numeric effects).

## Pending after Grounded_PDDL

- **`Reachability_Certificate.thy`**: re-verify on the ported engine+grounder. The engine now
  yields `ast_classical_plan_action`, so `cert_ops`/`ce_just` should switch to that type and the
  `pa_of_classical` bridge can be DROPPED (engine and `applicable` now share
  `ast_classical_plan_action`). Then re-check the two locales compile (needs jEdit to know the
  `Grounded_PDDL` session).
- **Do NOT touch `Grounding_Pipeline.thy`** (user instruction). NOTE (2026-06-08):
  `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy` is now fully refactored to the current API and
  **0 sorry / 0 errors** — WF + full semantics preservation (`valid_plan_iff`) proven. No longer a
  later job. See `WIP_session_handoff.md` §A and memory `project_restore_pddl_plan_existence`.

## Tooling notes (important)

- **Edit the open `.thy` ONLY via `mcp__isabelle__write_file`** (buffer-authoritative). Mixing
  built-in `Edit`/`Write` (disk) with jEdit causes buffer/disk divergence: `open_file` won't
  reload disk edits, and a later `write_file` flushes the stale buffer to disk, clobbering them.
  (Cost me real time this session.)
- **Avoid `get_command_info`** (user pref: it can hang jEdit). Use `get_processing_status` +
  `get_diagnostics`; `write_file`'s `wait_until_processed` reprocesses the touched commands.
  Large files may stall a few commands short of the tail — touch a late command via `write_file`
  to nudge, or accept partial when the unprocessed tail is just code-setup.
- See memories: `project_unrefactored_files` (API map + status), `feedback_file_edits`
  (write_file gotcha), `feedback_forall_over_list_all`, `project_reachability_analysis_session`.
