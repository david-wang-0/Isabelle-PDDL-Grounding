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

- **Verified cycle-detecting DFS for `dl_founded` (path 2).** Session `Datalog_Graph` already proves the
  graph-theoretic `acyclic ⟺ has_top_num` and the kernel integration
  (`dl_admissible_via_acyclic` / `dl_certified_model_via_acyclic`), which replace the non-executable
  `dl_founded` conjunct by support-graph acyclicity. The one missing piece is a **verified DFS that
  *constructs* the topological order / acyclicity witness**; it then slots straight into
  `dl_certified_model` → `dl_certified_model_correct`. (Both discharge paths are kept on purpose: the
  fast ordered-cert linear scan `dl_founded_exec` when the certificate carries a trusted order, the
  graph path when it does not.) Candidate AFP DFS entries noted in memory `project_afp_dfs_lookup`.
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
