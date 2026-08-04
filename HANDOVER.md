# Handover — Isabelle-PDDL-Grounding

A pick-up note for **incomplete work**, not documentation. For what the repo *is* and how it is laid
out, see `README.md` and `CLAUDE.md`; for design, `ARCHITECTURE_pipeline.md` /
`ARCHITECTURE_datalog_certification.md` and `Datalog/HANDOVER.md`.

## Current state

The **classical** pipeline is **`0 sorry` and `jedit-status`-green**. It builds
(`isabelle build -d <Isabelle-Graph-Library> -d . Classical_Grounding`), the exported SML binary plans
the running example, and the payoff theorem `plan_by_cert_sound` (any returned plan is a valid plan of
the original task, regardless of the two untrusted oracles) is proven. The repo was reorganized into two
mirrored trees (`Grounding_Common/` reusable + `Classical_Grounding/` classical) with a per-stage
ladder; that refactor is done and committed.

A sibling **`Temporal_Grounding/`** tree (numeric temporal grounding, grounding-only — no STRIPS) is an
**in-progress draft**: the normalization-ladder locales are green (including the positivity-only
`positive_temporal_problem`), but the reachability/relaxation locales are still placeholders and the
numeric pipeline is a `consts`-axiomatized sketch with sorried theorems.

## Open work

- **DONE (tiers 1+2, 0 `sorry`) — the numeric pipeline now has a real *grounded* output, not just
  the variable-free instantiation.** Honest names first: the stage-1 (variable-free) product is
  `numeric_P⇩V_cert` with executable entry points `instantiate_all_actions_{dfs,exec,gdfs}[_stream]_e`
  (the shipped `ground` CLI keeps calling the `_stream_e` ones, gate + output unchanged), and its wf /
  restore theorems are `numeric_wf_varfree_cert_problem` / `numeric_reconstruct_plan_varfree_cert`.
  The freed name `numeric_P⇩G_cert` now denotes the **stage-2** product: stage 1 composed with the
  fact/fluent fold `fact_folder.fold_prob`, i.e. the fully grounded nullary problem (nullary
  predicates for the certified facts, nullary functions `fuel_c1_0` for the reachable fluents,
  folded init assignments). Executable entry points `ground_all_actions_{dfs,exec,gdfs}_e` (gated by
  the new `numeric_fold_checks[_exec]`, `_return_iff`/`_InrE`/`_sound`/`_wf`), exported from
  `Planner_Export.thy`. Verification scaffolding: numeric-permissive coverage `covered_num` (+
  `facts_covered`/`fluents_covered` halves and intro/elim/dest rules) in
  `Grounding_Common/Grounded_PDDL/Grounded_PDDL.thy`; `wf_fact_folder_cov`/`wf_grounder_cov` weakened
  to `covered_num` with the strong `covered` re-asserted under the same names one level up in
  `wf_fact_folder`/`wf_grounder`; new `wf_fact_folder_num`/`wf_grounder_num` and the sibling
  `certified_reachability_fold_num` (**must** extend `certified_reachability_base` only, else the
  `grounder` interpretation deduplicates); factorization block moved into the new assumption-free
  `grounder_inst` locale. Pipeline theorem `numeric_wf_ground_cert_problem`.
  **DONE (tier 3): plan equivalence across the fold under numerics.** Numeric states transfer via
  the renaming `fold_nstate` (inverting `ground_pne` on `fluents`); semantic core
  (`ground_numexp_val`, `ground_fmla_sem_num`, the `ground_neff_update_num`/`fold_action_update_num`
  update commutations) and the full transfer chain (`fold_init_num`, `fold_enabled_iff_num`,
  `fold_exec_right_num`, path/validity, `fold_valid_classical_plan_iff_num`) live in
  `Classical_Grounded_PDDL_Semantics.thy`; lifted through `wf_grounder_num.valid_classical_plan_iff_num`
  (Factorization) to the pipeline (`numeric_ground_cert_plan_valid_iff`/`_plan_reconstruct`) and the
  entry points (`ground_all_actions_*_e_plan_valid_iff`/`_plan_restore`). The CLI prints the folded
  product via `ground --folded`.
- **DONE (tiers 1–4): STRIPS pipeline rebased on the numeric pipeline.** The numeric-free pipeline
  is the numeric pipeline plus a numeric-freeness gate: the seven-conjunct bridge
  `grounding_checks_of_num_free` (`numeric_fold_checks + num_free_prob + init_props ⟹
  grounding_checks`; `is_predAtom` on init stays an explicit conjunct — `eqAtm` in init is
  numeric-free), the `refl`-shaped product identity `numeric_P⇩G_cert_eq_P⇩G_cert`, the STRIPS
  block restated on `numeric_P⇩G_cert` (`numeric_P⇩S_cert` + wf/encodable/plan iff/reconstruct,
  all one-line rewrites), executable entry points
  `ground_strips_all_actions_{dfs,exec,gdfs}_e : … ⇒ String.literal + name strips_problem`
  (gate `strips_fold_checks_exec`, deliberately not `[code]` yet) with the six standard
  companions each, and the input-side chain `P⇩T_num_free` + `init_P⇩T_props` (numeric-freeness
  and init-props preserved through detype/degoal/explicate/split/def_translate;
  `explicate_def_fmla` is the *identity* on numeric-free formulas). Plan:
  `/tmp/plan_strips_rebase.md`. **OPEN (needs sign-off, breaks export byte-identity): tier 5** —
  add `ground_strips_all_actions_*_e` to `Planner_Export.thy` + a `--strips` CLI mode, regenerate
  (`isabelle build -c`), re-run smoke baselines. Deferred: stage-local relocation of the tier-4
  lemmas into `Classical_<Stage>_Num_Free.thy` files at the next heap rebuild;
  `num_free_prob`/`num_free_ac` dest-rule kit.
- **DONE (fully verified, 0 `sorry`) — readable generated names everywhere (no underscore-runs, no
  bare-numeral names).** All generated names are now human-readable, with freshness/distinctness
  still *theorems* (no new locale assumptions, no gate checks). The machinery lives in
  `Grounding_Common/Utils/String_Utils.thy` (baked into the `Grounding_Classical_Common` heap):
  `fresh_name`/`fresh_prefix` (least-index decoration of a fixed token via the previously-dead
  `safe_suffix`; index only on a genuine clash) replaced `safe_prefix`'s underscore-runs in
  Type_Normalization (`type_car`), Goal_Normalization (`Goal`, classical goal action `Goal`) and
  Definedness_Translation (`Defined_fuel`); `idx_name`/`strip_idx` (numeric `_i` suffix + executable
  strip-back-to-last-`_` restore) replaced the `padl` fixed-width underscore-padded numeral *prefix*
  on Precondition_Normalization split copies (`drop_0`, restore needs no width bound) and now also
  carries `varfree.op_names` and the fact folder's `fact_names`/`fluent_names`, which became
  readable-indexed (`at_p1_G_72`, `fuel_c1_0` — encoders `readable_fact`/`readable_fluent` in
  `Classical_Grounded_PDDL_Locales.thy`, theory-level so the factorization equality survives
  untouched). The whole `pad`/`padl`/`drop_lit`/`safe_prefix` family was deleted; grounder output is
  deliberately **not** byte-identical to older runs (names changed; counts unchanged). Residual
  cleanup for a future heap rebuild: `distinct_strings_lit` (+ its lemmas) in `String_Utils.thy` is
  now referenced by nothing outside its own file; the two `declare safe_suffix(')...simps [simp del]`
  in `Grounding_Common/Goal_Normalization/Goal_Normalization.thy` (they stop simp looping on the
  recursive index search) belong next to `safe_suffix` in `String_Utils.thy`.
- **DONE (fully verified, 0 `sorry`) — STRIPS grounder rebased on the variable-freeness stage.** The
  former `Numeric_Grounder` is now its own pipeline stage `Classical_Grounding/Variable_Freeness/`
  (session `Classical_Variable_Freeness`, constants `varfree_inst_ac/dom/prob`, locale ladder
  `varfree` → `varfree_instantiator`, output predicates `varfree_dom`/`varfree_prob`). The propositional
  grounder factors through it: `locale fact_folder` (`Classical_Grounded_PDDL_Locales.thy`) takes a
  variable-free problem plus **both** the reachable-facts and reachable-fluents lists and folds them
  to nullary predicates/functions (`fold_ac`/`fold_dom`/`fold_prob`, action names kept verbatim, so
  plan restore is the identity); `wf_fact_folder_cov`/`wf_fact_folder` carry the folder's wf +
  plan-equivalence (`fold_prob_wf`, `fold_valid_classical_plan_iff`).
  `Classical_Grounded_PDDL_Factorization.thy` proves `ground_prob_factors`:
  `fact_folder.fold_prob varfree_inst_prob facts fluents = ground_prob` (syntactic equality — the
  one-shot definition doubles as the fused code path, so exported SML is unchanged), interprets the
  folder layers from `wf_grounder_cov`/`wf_grounder` (prefix `ff`), and re-derives the grounder's
  interface theorems as `factored_*` from the two stages composed. The old `grounder` locale is now
  `varfree + fixes facts` — **parameter order (P, ops, facts)**, call sites were swapped.
- **DONE — monolithic one-shot proofs retired.** The direct `wf_grounder_cov`/`wf_grounder` wf chain
  (`Classical_Grounded_PDDL.thy`) and the monolithic `wf_grounder` semantics sections
  (`Classical_Grounded_PDDL_Semantics.thy`) are deleted; the interface theorems (`ground_dom_wf`,
  `ground_prob_wf`, `valid_plan_right`, `valid_classical_plan_left`, `valid_classical_plan_iff`,
  `ground_prob_num_free`, the `dg`-wf and `pg: grounded_problem` sublocales) are re-derived under
  their original names in `Classical_Grounded_PDDL_Factorization.thy` from the two stages composed.
  Numeric-freeness preservation is stage-local per David's convention: each stage has an adjacent
  `*_Num_Free.thy` (`Classical_Variable_Freeness_Num_Free.thy`: input num-free \<Rightarrow>
  variable-free output num-free; `Classical_Grounded_PDDL_Num_Free.thy`: `fold_prob_num_free` under
  `wf_fact_folder`). The running example `Running_Example_Numeric.thy` now demonstrates the staged
  path concretely (stage-1 output, folded output with nullary `fuel_c` fluents, and two
  `value`-checked `True` equalities incl. the factorization). Residual cleanup nits: stale prose at
  `Classical_Grounded_PDDL.thy` lines 7-11 (claims sorries that no longer exist); pipeline's
  `resolve_mem` duplicated by `resolve_schema_mem`; a duplicate-simp warning in
  `ground_prob_typeless`.
- **DONE (fully verified, 0 `sorry`) — HTG cert-check speed + three selectable foundedness checks.** The
  exported grounder offers three re-checks of the reachability certificate, `ground [--dfs|--topo|--gdfs]`
  (default `--dfs`), each `instantiate_all_actions_{dfs,exec,gdfs}_e` + `dl_certified_model_{dfs,exec,gdfs}`,
  all kept on purpose: `--dfs` per-vertex `dl_acyclic_dfs` (`O(V²)`); `--topo` ordered scan
  `dl_founded_exec` over Nemo's topological order; `--gdfs` the fast single-sweep global-visited DFS
  `dl_acyclic_dfs_global` (`Datalog_Cycle_DFS_Global.thy`, `O(V+E)`), **now fully proven** —
  `dl_acyclic_dfs_global_imp_acyclic` → `_imp_dl_founded` → grounder soundness, via `global_sweep_acyclic`
  (a `dfs_gctx` locale + 12-conjunct `dfs_inv` DFS invariant + fuel measure). The real bottleneck was
  **graph construction, not the DFS**: `nat_edges_code [code]` binds `dl_cert_facts` once (it was an
  `O(R²)` `remdups` rebuilt per relabelling), speeding up BOTH default checks. GED `d-8-12`, all three
  byte-identical: acyclicity `--gdfs` **111 s → 141 ms**, `--dfs` **57 s → 1.25 s**, `--topo` 0 ms. Unsafe
  closure branch streamed via `combos_forall` (proven-equal, `Datalog_Certificate_Index.thy`). The session
  builds normally (no `-o quick_and_dirty`).
- **Order-constructing witness (optional).** `Datalog_Graph` proves `acyclic ⟺ has_top_num` and the
  kernel integration (`dl_admissible_via_acyclic` / `dl_certified_model_via_acyclic`); a verified DFS
  that *constructs* the topological order (vs merely detecting a cycle) would slot into
  `dl_certified_model` → `dl_certified_model_correct`. Candidate AFP DFS entries in memory
  `project_afp_dfs_lookup`.
- **Swap the fuel-counted evaluator for a fixpoint one.** `Grounding_Common/Datalog/Datalog_Evaluation_Fixpoint.thy`
  holds a counter-free `dl_saturate` (+ termination + soundness, written) meant to replace
  `dl_iterate`/`dl_eval`. It is **not in any ROOT and not jEdit-verified**; wire it in and retire the
  fuel-counted path. (memory `project_datalog_fixpoint_eval_replace`)
- **Upstream the patched code bundles.** A `def_translate_code` bundle belongs in
  `Classical_Definedness_Translation_Semantics.thy` (the only stage without one). (The other half of
  this item is done: `padl_lit_code` died with the `padl` family, and `distinct_strings_lit_eq[code]`
  now sits at its definition site in `String_Utils.thy`.)
- **Finish the certification end-state.** Parse Nemo's ograph directly into the generic `dl_certificate`,
  export the generic checker, and obtain the reachability requirements by theorem — retiring the
  duplicated PDDL-side check implementations.
- **Optional — evaluator completeness.** `dl_eval` is proven *sound*; a *completeness* theorem
  (`{f. datalog_prog.derivable …} ⊆ set (dl_eval U Pl)`, via the `all_head_facts` iteration bound) would
  make it exactly the least model. Not needed for trust (the certificate checker validates the oracle's
  output).
- **Temporal negation-elimination (positive normal form) stage** — *do this last, if ever*; general-PDDL
  future-proofing, NOT needed for the Gigante benchmark set (which has no negated predicate
  preconditions). The positivity-only target locale `positive_temporal_problem` already exists in the
  temporal ladder (`Temporal_Grounding/Common/Temporal_PDDL_Normalization.thy`, positivity-only — keeps
  deletes); this stage is what would *establish* it for domains that do use negative predicate
  preconditions. Mirroring FD/TFD `normalize.py`: for each predicate occurring negatively, a fresh
  complementary `not-p`; init sets it; every effect on `p` mirrors onto `not-p` (in **both**
  at_start/at_end snap effects); replace `¬p` preconditions — including `over all` invariants — with
  `not-p`. Semantics-preserving. **Placement: post-grounding** on the nullary ground actions (not
  pre-grounding like FD): the grounder's reachability is delete-relaxed and monotone, so it already
  ignores negation — the complements are only needed in the final real-deletes ground problem, where
  adding `not-p` per *negatively-occurring reachable* ground atom is precise and minimal. Keep negatives
  out of the *reduction* (its certified mutex / `acts_non_intrf` stays positive) rather than supporting
  them there.

- **Temporal equality-atom (`eqAtm`) elimination stage** — *companion to negation-elimination above;
  do during or after grounding.* The temporal `positive_temporal_problem` / `is_pos_conj`
  (`Grounding_Common/Common/Formula_Utils.thy`) deliberately accept `eqAtm a b` / `¬(eqAtm a b)` as
  positive literals, but the downstream temporal **NTA reduction** (project
  `temporal-planning-certification`) maps preconditions to propositions and handles **`predAtm` only**
  — it cannot represent `eqAtm` literals. After grounding, every equality atom is ground
  (`= c1 c2`), so it is decidable and should be **constant-folded / feasibility-pruned away**
  (`True` ⇒ drop the conjunct, `False` ⇒ prune the action/goal) so grounded preconditions/goal are
  `predAtm`-only. Until this stage exists, the NTA-reduction consumer carries an explicit project-side
  "preconditions/goal are eqAtm-free (`predAtm`-only)" **side assumption** (see
  `temporal-planning-certification` `Ground_PDDL_Problem_Defs` re-point, 2026-06-30); this stage is
  what would let that assumption be **discharged** instead of assumed. Pairs with the
  constant-fold/feasibility-prune stage already noted for the re-expansion `χ` (GROUNDING_PLAN §4/§6).

## Gotchas (hard-won; keep in mind)

- **Code generation**: FPS shared-locale constants carry selector-pattern code equations from the
  continuous/temporal interpretations — `[[code drop]]` + re-add the foundational equation
  (`Code_Setup.thy` is the catalogue). `numeric_expression_valuation` is severed with a sound
  self-referential `Code.abort`. Locale defs **with assumptions** yield guarded `_def`s ("not an
  equation") — they need unconditional executable mirrors + equality-under-predicate lemmas (the
  established pattern, in `Classical_PDDL_Reachability_Locales.thy` and
  `Grounding_Pipeline_STRIPS_Executable.thy`).
- **`is_serial_solution_for_problem` is not executable** (`⊆⇩m` over function states); the SAT path's
  only runtime check is the executable model check, serial-ness follows by theorem.
- **Qualify, don't hide**, around the `Solve_SASP` import (SAS+ `ast_problem` namespace):
  `strips_problem.operators_of`, `STRIPS_Semantics.is_serial_solution_for_problem`.
- **jEdit workflow**: verify via the MCP server (`jedit-status`), never batch-build by default; force
  tail processing with `explore`(find_theorems) at EOF; edit open buffers only via
  `mcp__isabelle__write_file`.
- **Not a submodule** — `origin` is already SSH, so a plain `git push` works.
