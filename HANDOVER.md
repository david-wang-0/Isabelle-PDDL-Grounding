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

- **DONE (fully verified, 0 `sorry`) — STRIPS grounder rebased on the variable-freeness stage.** The
  former `Numeric_Grounder` is now its own pipeline stage `Classical_Grounding/Variable_Freeness/`
  (session `Classical_Variable_Freeness`, constants `varfree_ground_ac/dom/prob`, locale ladder
  `varfree` → `varfree_grounder`, output predicates `varfree_dom`/`varfree_prob`). The propositional
  grounder factors through it: `locale fact_folder` (`Classical_Grounded_PDDL_Locales.thy`) takes a
  variable-free problem plus **both** the reachable-facts and reachable-fluents lists and folds them
  to nullary predicates/functions (`fold_ac`/`fold_dom`/`fold_prob`, action names kept verbatim, so
  plan restore is the identity); `wf_fact_folder_cov`/`wf_fact_folder` carry the folder's wf +
  plan-equivalence (`fold_prob_wf`, `fold_valid_classical_plan_iff`).
  `Classical_Grounded_PDDL_Factorization.thy` proves `ground_prob_factors`:
  `fact_folder.fold_prob varfree_ground_prob facts fluents = ground_prob` (syntactic equality — the
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
  (default `--dfs`), each `ground_via_cert_numeric_{dfs,exec,gdfs}_e` + `dl_certified_model_{dfs,exec,gdfs}`,
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
  `Classical_Definedness_Translation_Semantics.thy` (the only stage without one), and
  `padl_lit_code` / `distinct_strings_lit_eq[code]` in `Grounding_Common/Utils/String_Utils.thy` — both
  currently patched in `Code_Setup.thy`.
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
