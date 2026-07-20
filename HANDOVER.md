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

- **Cert-check speed on HTG — SOLVED; three selectable foundedness checks (ONE soundness `sorry` left).**
  The exported grounder now offers three re-checks of the reachability certificate, selectable via the
  SML CLI `ground [--dfs|--topo|--gdfs]` (default `--dfs`), each a grounder entry
  `ground_via_cert_numeric_{dfs,exec,gdfs}_e` + `dl_certified_model_{dfs,exec,gdfs}`, all **kept on
  purpose**:
  - `--dfs` — the per-vertex directed-cycle DFS `dl_acyclic_dfs` (graph library, `O(V²)`);
  - `--topo` — the ordered linear scan `dl_founded_exec` over Nemo's topological order (`dl_certified_model_exec`);
  - `--gdfs` — a fast single-sweep global-visited directed-cycle DFS `dl_acyclic_dfs_global`
    (`Datalog_Cycle_DFS_Global.thy`, `O(V+E)`, one `seen`/gray set shared across roots; list-iterated
    neighbours + balancing `RBT_Set.insert`/`delete`).

  The real bottleneck turned out to be **graph construction, not the DFS**: `nat_edges`/`fact_idx`
  rebuilt `dl_cert_facts` (an `O(R²)` `remdups`) inside every one of the `~2·|edges|` relabellings.
  `nat_edges_code [code]` (bind `dl_cert_facts` once) fixed it — helping BOTH default checks. GED
  `d-8-12`, all three byte-identical: acyclicity `--gdfs` **111 s → 129 ms**, `--dfs` **57 s → 1.25 s**,
  `--topo` 0 ms; total ~4.4–5.6 s. The unsafe closure branch was also streamed
  (`combos_forall`, proven-equal, `Datalog_Certificate_Index.thy`) so head-only clauses no longer
  materialise `|U|^k` substitutions.

  **Remaining obligation — ONE `sorry`, reduced to a clean self-contained sub-lemma.** The top lemma
  `dl_acyclic_dfs_global_imp_acyclic` is **proved** (via `not_acyclic_dep_graph_imp_nat_edges`), and
  everything downstream (`dl_admissible_gdfs` → `dl_founded` → grounder soundness) sits on it. Four
  plumbing lemmas are proved: `rbt_delete_inv`, `rbt_delete_set`, `adj_set`
  (`set (Tree2.inorder (neighbourhood (dep_adjmap c) w)) = {v. (w,v) ∈ set (nat_edges c)}`),
  `nat_edges_endpoint_lt` (`dl_body_closed c ⟹` edge endpoints `< length (dl_cert_facts c)`). The one
  `sorry` is:
  `global_sweep_acyclic : dl_body_closed c ⟹ dl_acyclic_dfs_global c ⟹ acyclic (set (nat_edges c))`
  — 3-colour-DFS completeness for the fuel-bounded `dfs_fuel`. It needs a **REPL/sledgehammer** session
  (the `isabelle-prover` subagent's toolset lacks `repl_connect`, so it could only do buffer-write +
  diagnostics). **Plan** (contrapositive over `E = set (nat_edges c)`, `n = length (dl_cert_facts c)`,
  `adj w` set fixed by `adj_set`): a `dfs_inv E adj s` invariant guarded by `¬ gs_cyc s` — `vset_inv`
  seen/unf; `GRAY ⊆ SEEN`; `GRAY = set (map fst (work s))` distinct; per frame `set ns ⊆ out v` and
  consumed neighbours `⊆ SEEN`; **(F)** no `BLACK→GRAY` edge; **(G)** `BLACK` (= SEEN−GRAY) is E-closed;
  **(Hacyc)** `acyclic (E ∩ BLACK×BLACK)`, preserved at *blacken* via `acyclic_insert` (newly-blackened
  top vertex is a fresh source: all out-neighbours already BLACK by the split form, no BLACK in-edge by
  (F)); **(K)** split form `work = ss1 @ (v,ns) # ss2 ⟹ out v − set ns ⊆ BLACK ∪ set (map fst ss1)`.
  Two inductions on fuel (`dfs_fuel.induct`): **(1)** single-step `dfs_inv` preservation (cases
  blacken/push/skip/back-edge, set-algebra via `rbt_insert_set`/`rbt_delete_set` + `set.set_isin`);
  **(2)** fuel sufficiency via measure `μ s = 2·(n−|SEEN|) + Σ_{v∉SEEN} outdeg v + |GRAY| + Σ_frames
  length ns` (drops ≥1/step, starts `< fuel = 2n+|nat_edges|+1`) ⇒ `work(fin)=[]` when `¬gs_cyc`. Then
  the `foldl` over `[0..<n)` keeps `dfs_inv` and forces `SEEN ⊇ [0..<n)`; with `nat_edges_endpoint_lt`,
  `E ∩ BLACK×BLACK = E`, so (Hacyc) gives `acyclic E`. **Until it is discharged the session builds only
  under `-o quick_and_dirty`.**
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
