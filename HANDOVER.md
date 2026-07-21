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
