# Handover: verified PDDL grounding + SAT planning (Isabelle-PDDL-Grounding)

Full-repository summary and handover, written 2026-06-12 (read-through of every theory, ROOT, doc,
and SML file) and updated 2026-06-18. Companion one-pagers:
[ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md) (dataflow + trust story) and
[ARCHITECTURE_datalog_certification.md](ARCHITECTURE_datalog_certification.md) (certificate design).
The per-stage `WIP*.md` notes have been retired — the work they tracked is done; the few remaining
open items are folded into this handover (below). The PDDL reachability-certificate development is
`0 sorry` and was split + extended this session (see the note next).

## Latest session (2026-06-18) — executable layer DONE + validated end-to-end

The **executable layer** is finished and validated after the certificate rework (the PDDL-side
ograph `certificate`/`CNode` datatype was removed; the kernel now consumes the **generic** pair
`M :: (predicate × object list) list` + `dc :: (predicate, object) dl_certificate = DLCert (dl_rules
:: dl_ground_rule list)`, `dl_ground_rule = DLRule gr_head gr_body`). The compiled planner runs
Nemo → verified kernel → grounder → SAT → plan and prints a **verified-valid plan**
(`plan_by_cert_sound`). All Isabelle below is `jedit-status`-green, 0 sorry.

`dl_founded` was discharged via **path 1** (ordered-cert linear scan); the verified-DFS path 2 is
still future work (see "Other open work"). The Nemo parser AND printer stay standard ML (untrusted
oracle glue, fail-closed against the verified checker).

**Datalog kernel — fully executable:**

- `Datalog/Datalog_Certificate.thy` — abstract checker + correctness (`dl_certified_model_correct`),
  0 sorry.
- `Datalog/Datalog_Certificate_Code.thy` (NEW, `imports Datalog_Certificate`) — the executable
  refinement: `dl_founded_scan`/`dl_founded_exec` (left-to-right scan, each `DLRule head body`
  requires every body fact `∈ set acc`) + `dl_founded_exec_imp_dl_founded` (rank `f` = list index,
  `LEAST i. i < length rs ∧ gr_head (rs!i) = f`; helper `dl_founded_scan_body`),
  `dl_{positive_prog,rule_valid,closure_check,admissible,certified_model}_exec` (all `[code]`), the
  `cls_substs_tabulate` + `subst_atom_head/body_cong`/`eval_guard_cls_cong` bridges, the `*_exec_imp`
  soundness chain, and the capstone `dl_certified_model_exec_correct`. 0 sorry. (Gotchas: don't
  annotate `define rank :: dl_rank` — proof-local tyvar clash; a `subset` transitivity `by blast`
  diverged, use a `subset_trans` chain.)
- `Datalog/ROOT`: + `Datalog_Certificate_Code`. Side fix: converted `Datalog/Datalog_Sema_Supplement.thy`
  from raw-Unicode glyphs to ASCII escapes (lone raw-Unicode file; broke the batch lexer at the first
  control symbol `\<^emph>`).

**Exec-layer rewire (PDDL side), all 0 sorry / green:**

- `Grounding_Pipeline_STRIPS_Executable.thy` — oracle retyped `f :: dl_program ⇒ (predicate × object
  list) list × (predicate,object) dl_certificate`; exec mirrors (`cert_ops_of_exec`/`extra_eff_atoms_of_exec`/
  `cert_facts_of_exec`/`grounding_checks_exec`) **retargeted from the old cert `c` onto `M :: fact
  list`**, `_eq` lemmas by `refl`; `numeric_free_problem_exec` (`num_free_prob R ⟹ numeric_free_problem
  R` by `unfold_locales`); `ground_by_cert`/`ground_via_cert(')` (returns `((M,dc), PS)`)/
  `reconstruct_plan_by_cert` + `ground_by_cert_eq`/`_strips_eq`/`reconstruct_plan_by_cert_eq`; plus
  `declare num_free_code [code]` (needed because `num_free_prob` enters the exec path via
  `ground_via_cert'`). Gotcha: in `grounding_checks`, `px.wf_fmla_atom px.objT` simplifies to **N's**
  signature, so the mirror must use `domain N`/`objects N`, not `relax_prob N`.
- `Planner_STRIPS_Executable.thy` — `plan_by_cert` binds `(Mdc, PS)` and reconstructs with `fst Mdc`;
  `plan_by_cert_sound` retargeted to the new 4-assumption discharges (`numeric_free_problem_exec` /
  `dl_certified_model_exec_imp` / `grounding_checks_exec_P⇩T`, then `[OF pnf ne cert gc' rp wf …]`).
- `Planner_STRIPS_Export.thy` — `export_code` cert ctors `Cert CNode cert_facts nodes cn_fact cn_preds`
  → `DLCert DLRule gr_head gr_body`; runs clean, regenerates `SMLCodebase/code/PDDL_SAT_Planner_Exported.sml`
  (134 KB, with `DLCert`/`DLRule`, no stale ctors).
- `Code_Setup.thy` — unchanged (generic code-equation setup only).
- top `ROOT`: + `Datalog_Certification` in `sessions` (the exec file is the first `Tree_Decomp_Grounding`
  theory to *directly* import a `Datalog_Certification` theory; transitive reachability via
  `Reachability_Analysis` was NOT enough; import is session-qualified
  `Datalog_Certification.Datalog_Certificate_Code`). Re-register (`isabelle components -u .`) + restart
  jEdit after ROOT edits.

**SML driver + build + end-to-end run:**

- `SMLCodebase/nemo_driver.sml` — `NemoDriver.certify` now returns `(M, dc)`: each node fact
  `E.Atom (E.PredAtm (p,args))` → `dl_fact (p,args)`; predecessor *indices* resolved to predecessor
  *facts* via a `Vector`; emits `E.DLCert [E.DLRule ((p,args), body) …]` in topo order (replaced the
  old `E.Cert [E.CNode …]`). Oracle type: `dl_program → (predicate × object list) list × (predicate,
  object) dl_certificate`.
- `make all` (MLton) compiles `SMLCodebase/bin/pddl_sat_planner` clean (only pre-existing
  non-exhaustive-match warnings); `./bin/pddl_sat_planner examples/domain.pddl examples/problem.pddl`
  with `nmo` + `z3` **plans end-to-end** — Nemo cert (new format) re-checked by
  `dl_certified_model_exec`, grounded, SAT-solved, reconstructed. By `plan_by_cert_sound` a printed
  plan is verified-valid.

**`Running_Example.thy` demo — DONE (2026-06-18).** The 6 action schemas were rewired off the
removed `Cert`/`CNode` ograph onto the generic `(M, dc)` pair (`naive_cert` saturates `dl_rules R`),
and the pre-existing bare-`Var` clash was fixed by qualifying every `(Var STR …)` → `(variable.Var
STR …)` and removing the dead `hide_const (open) Datalog.id.Var` block. Fully green (0 errors/warnings,
processed + consolidated); the `value` probes give the expected results: `dl_certified_model_exec …
= True`, `grounding_checks_exec … = True`, `ground_via_cert (λ_. ([], DLCert [])) … = None`
(fail-closed), `ground_via_cert (λ_. my_cert) … = Some (problem_for …)`. **The whole
`Tree_Decomp_Grounding` top session is now wireable end-to-end.**

## Latest session (2026-06-17 cont.) — grounding pipelines re-pointed onto `certified_reachability`

The two abstract grounding-pipeline theories were rewired off the **removed** PDDL-side
certificate datatype (`certificate` / `pddl_datalog.admissible`) onto the generic
`certified_reachability P\<^sub>T M dc` interface, and **verified green in jEdit** (0 errors,
fully processed):

- **`Grounding_Pipeline_Numeric.thy`** — the inner `context fixes cert :: certificate; assumes
  pddl_datalog.admissible … / grounding_checks … cert` block became
  `context fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"` with the four
  `certified_reachability` assumptions: `px_numfree: numeric_free_problem (relax_prob P\<^sub>T)`,
  `nonempty: const_names (relax_prob P\<^sub>T) ≠ []`,
  `cert: dl_certified_model (set (dl_rules (relax_prob P\<^sub>T))) (set (const_names (relax_prob P\<^sub>T))) M dc`,
  `grounding_cert: normalized_problem_rx.grounding_checks P\<^sub>T M`. `P\<^sub>G_cert`/`reconstruct_plan_ground_cert`
  now read `cert_facts_of P\<^sub>T M` / **`remdups (cert_ops_of P\<^sub>T M)`** (matching the locale's
  `cert_ops' = remdups (cert_ops_of M)`). `certified_reachability_i` discharges the `num_free_prob`
  locale goal via `numeric_free_problem.num_free_prob[OF px_numfree]` (the bare `numeric_free_problem PX`
  fact does not `simp`-reduce to `num_free_prob PX`).
- **`Grounding_Pipeline_STRIPS.thy`** — same header swap; `P\<^sub>G_cert cert` → `P\<^sub>G_cert M`,
  `[OF admissible_cert grounding_cert …]` → `[OF px_numfree nonempty cert grounding_cert …]`,
  `interpret cr: certified_reachability P\<^sub>T cert` → `… P\<^sub>T M dc`. `P\<^sub>S_cert`/`strips_plan_*_cert`/
  `reconstruct_pipeline_plan_cert` all carry through.

**~~Still BROKEN~~ — RESOLVED 2026-06-18** (see the top-of-file session note): the **executable
layer** (`Grounding_Pipeline_STRIPS_Executable`, `Planner_STRIPS_Executable`, `Code_Setup`,
`Running_Example`, `Planner_STRIPS_Export`) was rewired off the removed
`admissible_exec`/`cert_ops_exec`/`cert_facts`/`certificate` onto the generic `(M, dc)` interface.
`dl_founded` got an **executable re-check** via the ordered-cert linear scan (`dl_founded_exec`,
rank = list index — discharged from the SML driver's existing toposort, no DFS needed); the Nemo
parser/printer produce the `(M, dc)` pair in standard ML. The verified cycle-detecting DFS is left
as a second, independent refinement (future work). The whole executable layer — including the
`Running_Example` demo — is now green (2026-06-18).

## Latest session (2026-06-17) — certificate split, `certified_pddl`, generic datalog evaluator

The (formerly monolithic, 0-sorry) `Reachability_Certificate.thy` was **split into three files**, a
**`certified_pddl`** grounding-input locale was added, and the retired untrusted `semi_naive` engine
was **deleted and replaced** by a generic verified datalog evaluator. All green in jEdit. Not
committed. Details below; the earlier cleanup + locale-relocation work (`dl_bridge_wf` discharge,
both minimal-model inclusions, style sweep) that brought the file to 0 sorry is summarised after.

- **`dl_bridge_wf P` discharged** — proved as `lemma bridge` inside `num_free_relaxed_problem`; its
  only remaining assumption is `nonempty: "const_names \<noteq> []"`. The minimal-model ⊇ direction
  (`dl_derivable_imp_achievable`) and both capstones (`reachable_eq_minimal_model`,
  `certified_facts_eq_reachable`) are proven and **hypothesis-free** in that locale.
- **Locale relocation** — `nd` is now a `pddl_datalog` fact; `nne` and `bridge` are
  `num_free_relaxed_problem` facts. The ~15 engine/soundness/tightness lemmas dropped their
  `nne`/`nd`/`wf` hypotheses and read the facts from their locale.
- **Typeless hoist** — `const_name_is_obj_of_type` + `params_match_from_const_args` moved into
  `typeless_classical_problem` in `Common/Normalization_Definitions.thy`; the
  `normalized_problem \<subseteq> typeless_classical_problem` sublocale (formerly commented out) is
  now enabled.
- **Style sweep** — every `from`/`with` proof command rewritten to `using`/`hence`/`thus`/`then
  obtain`; `moreover`/`ultimately` on their own lines; `obtain … where` and multi-`and` `have`s
  reformatted one-fact-per-line. Rules follow the contributor's Isabelle/HOL working-rules style guide.
- **Lemma extraction** — `bridge` 187→46 lines (`dcl_vars_subset_params`, `init'_is_predAtom`);
  `dl_derivable_imp_achievable` 200→146 (`satisfies_conds_of_guards`, `ach_of_pred_pre`).

**DONE this session (2026-06-17, follow-up):**

- **`certified_pddl` locale added** — `certified_pddl = num_free_relaxed_problem + fixes M dc +
  assumes cert: "dl_certified_model (set (dl_rules P)) (set const_names) M dc"`, deriving the
  hypothesis-free fact `certified_facts_eq_reachable: "set M = {f. achievable f}"`. This is the
  grounding-input locale the downstream grounder consumes.
- **Theory split done + jEdit-verified green** — `Reachability_Certificate.thy` carved into three
  files in the `Reachability_Analysis/` session (all 0 sorry / 0 error, fully consolidated):
  - `PDDL_Reachability_Locales.thy` — the PDDL↔datalog **locale hierarchy** (`pddl_datalog`,
    `num_free_relaxed_problem`, `certified_pddl` headers) + the serialization defs (`dl_rules`
    etc.) + the `dl_bridge_wf` bundle.
  - `PDDL_Reachability_Analysis.thy` (`imports PDDL_Reachability_Locales`) — concern (a): PDDL↔datalog
    minimal model. Re-opens `context pddl_datalog` / `context num_free_relaxed_problem` with the
    helper/tightness lemmas through `achievable_eq_minimal_model`.
  - `PDDL_Reachability_Certificate.thy` (`imports PDDL_Reachability_Analysis`) — concern (b):
    `certified_facts_eq_achievable`, `minimal_model_facts_requirement`, and `certified_pddl`'s
    `certified_facts_eq_reachable`.

  The split re-opens the **same** locales in each file (no lemma hoisted to top level), so no
  `[OF …]` premise-order breakage — green on first reload. Importers re-pointed:
  `Certified_Grounding_Locales` now `imports PDDL_Reachability_Certificate`; the two
  `\<^theory>` antiquotations in `Grounding_Pipeline_STRIPS_Executable.thy` point at
  `PDDL_Reachability_Certificate`. ROOT updated.

**Retired engine replaced (2026-06-17).** Rather than move the PDDL-specific `semi_naive_eval`,
the untrusted forward-chaining solver was **deleted** from `Reachability_Analysis.thy` (along with
its instantiation helpers `fix_to`/`finish_args`/`all_insts_*`/`all_derivs`, the `my_prob` demo,
the orphaned `enumerate_orga`/`pred_clauses`, and the two unproven soundness statements
`found_facts_achievable`/`found_pactions_applicable`) and **replaced by a generic, PDDL-free,
verified evaluator** `Datalog/Datalog_Evaluation.thy` (in the `Datalog_Certification` session): a
total, executable, `[code]` forward-chaining `dl_eval` over the generic clause types, proven
**sound** (`dl_eval_sound`: every returned fact is `datalog_prog.derivable`). `Reachability_Analysis.thy`
now keeps **only** the shared PDDL→datalog infra the certificate uses (`as_action_clause`,
`consequence_of`, `organize_facts`/`in_orga`, `a_clauses`, `init'`, …) and is **0 sorry** — the four
retired-engine sorries are gone. The two stale `thm` lines in `Grounding_Pipeline_Numeric.thy` were
removed. All green in jEdit.

**Certified grounding rewired (2026-06-17).** `Certified_Grounding_Locales/Certified_Grounding{,_Semantics}.thy`
were re-pointed off the removed PDDL certificate datatype onto the **generic** entry point and are now
**0 sorry / green**. The `certified_reachability` locale = `normalized_problem_rx` + `fixes M dc` +
`assumes numeric_free_problem PX`, `const_names PX ≠ []`, `dl_certified_model (set (dl_rules PX))
(set (const_names PX)) M dc`, and the decidable `grounding_checks M`. Facts/ops come from `M`:
`cert_facts' = remdups (map fact_to_facty M @ eff-atoms)`; `cert_ops'` is the precondition-filtered
ground-instance enumeration (`cert_ops_of`). Both supersets proven over the un-relaxed `P`
(`all_facts_super`, `all_ops_super`), the latter via the new **ops-exactness** lemma
`px_applicable_super` (`{px.applicable} ⊆ set (cert_ops_of M)` — applicable ⟹ enabled in a reachable
state ⟹ positive precondition atoms achievable ∈ M, using `px.enabled_clause_body` +
`certified_facts_eq_achievable`). The `sublocale certified_reachability ⊆ wfg: wf_grounder P
cert_facts' cert_ops'` goes through with all 12 obligations discharged.

> Gotcha (worked around): the `normalized_problem_rx ⊆ px: pddl_datalog PX` sublocale mis-interprets
> the `objects`-dependent `pddl_datalog` lemmas (`is_obj_of_type_const_name`, `action_params_match_combos`)
> as `objects relax_prob` (the `P` argument drops), so `[OF]` against a well-formed `px.action_params_match`
> fact fails to unify. Re-derived the needed `args ⊆ const_names` inline from the (fine)
> `px.action_params_match_def` and `px.objT_alt` instead of the broken theorems.

~~Still open: the pipeline entry points still assume `pddl_datalog.admissible`~~ — **DONE**
(2026-06-17 cont., see the top-of-file note): `Grounding_Pipeline_Numeric.thy` /
`Grounding_Pipeline_STRIPS.thy` are re-pointed onto `certified_reachability P\<^sub>T M dc` and green.
The **executable layer** (including the `Running_Example` demo) was finished + validated 2026-06-18
(`dl_founded` via the ordered-cert linear scan, no DFS needed for path 1).

⚠ **jEdit buffer/disk gotcha** (learned the hard way): never edit an open `.thy` on disk. For a bulk
reorg, kill jEdit and delete `#*#` autosave + `*.thy~` backup files **before** relaunching, else
jEdit re-flushes a stale buffer over the on-disk edit. Codified in the `isabelle-launch` skill.

## What this repository is

A partially-verified Isabelle/HOL implementation of the Helmert-2009 PDDL grounder, extended
into a complete **verified SAT-based planner**: parse classical PDDL → normalize → certify
reachability (untrusted Nemo datalog engine + verified certificate checker) → ground →
convert to STRIPS (AFP `Verified_SAT_Based_AI_Planning` format) → SAT-solve (untrusted external
solver + verified model re-check) → reconstruct a **proven-valid plan of the original
problem** (`plan_by_cert_sound`, 0 sorry). The exported SML binary
(`SMLCodebase/bin/pddl_sat_planner`) plans the running example end-to-end (~6–9 s with z3),
and the Formal-PDDL-Semantics validator confirms its plans.

PDDL semantics come from the sibling **Formal-PDDL-Semantics** submodule (sessions
`Classical_Planning`, `Continuous_Planning` — the "pair world model" classical semantics);
STRIPS/SAT come from AFP `Verified_SAT_Based_AI_Planning`; datalog clause syntax from
AFP `Stratified_Datalog`.

## Session architecture (ROOTS order)

Two-layer frozen/editable split, then one session per pipeline stage:

| Session (dir) | Contents / role | Status |
| --- | --- | --- |
| `Tree_Decomp_Grounding_Base` | external deps only (FPS Classical/Continuous, STRIPS+SAT incl. `Solve_SASP`, `Propositional_Proof_Systems`, `Show`); build once, load as frozen jEdit heap | stable |
| `Tree_Decomp_Grounding_Common` (`Common/`) | editable shared layer: `Formula_Utils` (is_conj/un_and/pos-conj/relax_lit), `DNF` (`dnf_list` + semantics), `Graph_Funs` (`reachable_nodes`, `all_combos`/`chosen_from`), `String_Utils` (fresh-name machinery: `safe_prefix`, `distinct_strings_lit`), `Nat_Show_Utils` (`show_nat_inj`), `Grounding_Utils`, `PDDL_Sema_Supplement` (alt defs, `valid_classical_plan_alt`, `plan_action_enabled`, `ac_tsubst`, wf lemmas), `STRIPS_Sema_Supplement`, `PDDL_Checker_Utils` (reduced to `reveal_error`), `Normalization_Definitions` (restriction/typeless/normalized/relaxed/grounded locale ladder, `achievable`/`applicable`), `Numeric_Free` | 0 sorry |
| `Datalog_Certification` (`Datalog/`) | **standalone, PDDL-free** generic positive-datalog certificate checker. `Datalog_Sema_Supplement.thy` (locale hierarchy `datalog_prog` ⊂ `datalog_universe` ⊂ `positive_datalog_universe`; inductive least-model `datalog_prog.derivable`; AFP `⊨⇩l⇩s⇩t` bridge `derivable_iff_least_solution`) + `Datalog_Certificate.thy` (**index-free** `dl_certificate` = list of `DLRule` ground rules; **set-based** `dl_rule_valid`/`dl_closure_check`/`dl_founded`/`dl_admissible`; `dl_certified_model_correct` = certified facts = `datalog_prog.derivable`; `certified_model_is_least_solution` = AFP least solution) + `Datalog_Evaluation.thy` (**2026-06-17**: generic, executable, `[code]` forward-chaining evaluator `dl_eval`, proven **sound** `dl_eval_sound` — the untrusted oracle that produces a candidate model for the checker to validate) + `Datalog_Certificate_Code.thy` (**2026-06-18**: executable refinement `dl_certified_model_exec`, `dl_founded_exec` ordered-cert linear scan, all `[code]`, 0 sorry). **History**: was Nemo ograph + indices; executable refinement + downstream `dl_derivable` re-point now **DONE**; the verified graph topological order / cycle-check for `dl_founded` is **DONE** in session `Datalog_Graph` (see that row + `Datalog/HANDOVER.md`) | 0 sorry |
| `Type_Normalization` | detype: types → unary predicates (`detype_classical_prob`); `*2` locale hierarchy with `rewrites`-collapsed sublocales; `detyped_valid_iff` | 0 sorry |
| `Goal_Normalization` | degoal: fresh goal predicate + goal action (`degoal_prob`); `*3` hierarchy; `degoaled_valid_iff` + plan restore | 0 sorry |
| `Definedness_Normalization` | explicate PNE definedness as reflexive `numericEqAtm` conj-prefix (`explicate_def_prob`); `explicate_valid_iff` | 0 sorry |
| `Precondition_Normalization` | DNF split, one action per disjunct (`split_prob`, `*4` hierarchy); needs the definedness conj-prefix invariant; `split_valid_iff` + `restore_plan_split_valid` | 0 sorry |
| `Definedness_Translation` | numeric definedness → fresh `Defined_*` propositional predicates (`def_translate_prob`, `*_dt`); `def_translate_valid_iff` | 0 sorry |
| `PDDL_Relaxation` | delete relaxation (`relax_prob`, `*_rx` hierarchy with `px` sublocale): `relax_wf/normed/relaxes`, **`relax_achievables` / `relax_applicables`** (the P vs P_R bridge that makes certificate-grounding sound) | 0 sorry |
| `Reachability_Analysis` | see below | 0 sorry (retired-engine sorries deleted; minimal-model reverse direction proven) |
| `Grounded_PDDL` | the verified grounder core: `grounder`/`wf_grounder` locales (input: problem + achievable-facts/applicable-ops supersets), fresh nullary fact/op names, `ground_dom/prob_grounded`, `ground_dom/prob_wf`, `ground_enabled_iff`, `valid_classical_plan_iff` / `valid_classical_plan_left` + `restore_ground_pa` plan restoration | 0 sorry |
| `Tree_Decomp_Grounding` (top, `./ROOT`) | `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS`, `Grounding_Pipeline_Numeric`, `Grounding_Pipeline_STRIPS`, `Code_Setup`, `Grounding_Pipeline_STRIPS_Executable`, `Planner_STRIPS_Executable`, `Planner_STRIPS_Export` (`export_files` → `SMLCodebase/code/`), `Running_Example` | 0 sorry |
| `Datalog_Graph` (`Datalog_Graph/`, `= Datalog_Certification +`) | **Path-2 foundedness via graphs (2026-06-18)**: `Graph_Topological_Order.thy` (graph-theoretic `acyclic ⟺ has_top_num`, `no_cycle_iff_acyclic`) + `Datalog_To_Graph.thy` (`dl_dep_graph` support-graph conversion; `acyclic ⟹ dl_founded`; `dl_admissible_via_acyclic` kernel integration). Builds on the graph library now in the Base heap | 0 sorry |

### Reachability_Analysis session in detail

- `Reachability_Analysis.thy` — now **shared PDDL→datalog infra only**, 0 sorry (`action_clause` =
  `AClause name params pred-pre cond-pre adds`, `as_action_clause`, `a_clauses`,
  `init'`/`pseudo_init`, `consequence_of`, `satisfies_cond(s)`, `organize_facts`/`in_orga`). The
  untrusted `semi_naive_eval` engine + its instantiation helpers + the `my_prob` demo + the two
  unproven `found_*` soundness statements were **deleted** (2026-06-17); the generic, verified
  replacement is `Datalog/Datalog_Evaluation.thy`.
- `Datalog/Datalog_Evaluation.thy` — generic, PDDL-free, **verified** forward-chaining evaluator
  (`dl_eval`, total + `[code]`, proven sound: `dl_eval_sound`). The untrusted reachability oracle
  now runs on the translated datalog program; the certificate checker validates its output.
- `PDDL_Reachability_{Locales,Analysis,Certificate}.thy` — the former `Reachability_Certificate.thy`,
  split 2026-06-17 (see the top-of-file session note and the "Refactor" section).
- The former `Reachability_Certificate.thy` (split 2026-06-17 into
  `PDDL_Reachability_{Locales,Analysis,Certificate}.thy`, **0 sorry**) — the heart of the trust
  story. **2026-06-14 rewrite** (relate admissible datalog certificates to PDDL reachability;
  de-Nemo; drop the PDDL-direct executable checker; remove the PDDL certificate data structure).
  Reachability is related to the *generic* `dl_certificate` of `Datalog_Certification` **purely
  semantically**. The content, in order (now spread across the three split files):
  1. Locale `pddl_datalog = relaxed_problem` — reusable PDDL reachability **helper lemmas only**
     (`is_obj_of_type_const_name`, `action_params_match_combos`, `res_inst_adds_eq_consequence`,
     `enabled_clause_body`, the `un_and`/`valuation` helpers). **Removed** (recover from git
     ≤ `118b66f`): the certificate datatype `certificate`/`CNode`, `cert_facts`/`cn_body`,
     `closure_check`/`closure_sound`, the Nemo-ograph `ordered_check`/`local_valid`/`admissible`,
     `cert_ops`/`cert_ops_sound`, and the `*_exec` executable mirrors.
  2. The PDDL→datalog serialization (`dl_id_of_term` … `dl_fact_clause`, `dl_rules`) + the
     translation wf bundle `dl_bridge_wf` — **kept** (the datalog translation of the problem,
     not Nemo-specific; it is the program whose minimal model the bridge relates to reachability).
  3. Minimal-model relation (section "PDDL reachability is the minimal model …", `context
     pddl_datalog`), re-pointed onto `datalog_prog.derivable (set const_names) (set (dl_rules P))`
     (the removed list-based `dl_derivable` is gone). **Proved**: `derivable_invariant`,
     `achievable_imp_dl_derivable`, `achievable_eq_minimal_model`, `minimal_model_facts_requirement`,
     and the capstone `certified_facts_eq_achievable`
     (`dl_certified_model (set (dl_rules P)) (set const_names) M dc ⟹ set M = {f. achievable f}`,
     via the generic `dl_certified_model_correct`). **0 sorry** (as of 2026-06-16): both inclusions
     are proven — forward/`⊆` (soundness) via `achievable_imp_dl_derivable` → `derivable_invariant`,
     and reverse/`⊇` (tightness) via `dl_derivable_imp_achievable` (the last `step` case, needing the
     delete-relaxation persistence argument, was completed 2026-06-16). `derivable_init` and
     `derivable_step_adds` are both proven. So `achievable_eq_minimal_model` /
     `certified_facts_eq_achievable` hold unconditionally in `num_free_relaxed_problem`.
     Helper lemmas in the `pddl_datalog` context, all proven: `subst_id_dl_id_term`
     (`subst_id`/`ac_tsubst` bridge), `ac_arg_in_const_names`, `ac_tsubst_var_in_args`,
     `dl_cond_rh_eval_guard`, plus six added for `derivable_step_adds`: `dl_pos_rh_form` /
     `dl_pos_rh_Some` / `dl_cond_rh_form` (shapes of the translated literals), `dl_clause_of_pos_mem`
     (the add-effect's clause is in `dl_clauses_of_action_clause` when no literal fails to translate),
     `guard_from_cond` / `body_atom_from_pre` (every clause guard / body atom traces back to a
     condition / positive precondition). `derivable_step_adds` resolves the fired action's schema,
     derives the no-None facts from `dl_bridge_wf` + `enabled_clause_body`'s `satisfies_conds` (a
     statically-unsatisfiable condition can't be enabled, so the clause survives the fail-closed drop),
     decomposes the add-effect via `res_inst_adds_eq_consequence`, and applies
     `datalog_prog.derivable.derive` with `σ = λv. ac_tsubst ps args (VAR v)`.

     **The reverse direction** `dl_derivable_imp_achievable` `step` case (rule induction on
     `datalog_prog.derivable`) was the last to land (2026-06-16): it needed the delete-relaxation
     MONOTONICITY/PERSISTENCE infrastructure — in the action-clause case each body atom is achievable
     *individually* (IH), but firing the action needs them all true in ONE state, sound only because
     the relaxed problem never deletes, so the per-fact plans concatenate (plan validity is monotone
     in the start state). The fact-clause case isn't just `init_achievable` either: `init'` =
     `conc_unique pseudo_init (init P)`, so a fact may sit in `pseudo_init` (empty-precondition
     action) rather than `fst I`. The supporting lemmas (relaxed actions have empty deletes ⟹
     `fst M ⊆ fst (execute_plan_action a M)`; plan validity monotone in start state; fold/concatenate
     plans) are all proven.
  - GREEN in jEdit (0 error / 0 `sorry`). REPL note: the `iq` session is NOT on this
    submodule's path (`Bad theory import iq.iq`); to use the I/R REPL, `repl_connect` with an explicit
    `ir_home` pointing at the AutoCorrode `ir` backend directory (works without adding the import). The old **check-level
    bridge** (`cert_to_dl`,
    `dl_closure_imp_closure_exec`, `dl_local_valid_imp_local_valid_exec`,
    `dl_admissible_imp_admissible_exec`) was **excised** — the generic checker's 2026-06-14
    index-free/set-based rework made it the obsolete path; the semantic relation supersedes it.
  - ✅ **`Certified_Grounding*` rewired (2026-06-17), 0 sorry** onto the generic entry point
    (`dl_certified_model` + `certified_facts_eq_achievable`), feeding `wf_grounder` — see the
    "Certified grounding rewired" note up top. (The pipeline theories
    `Grounding_Pipeline_STRIPS/Numeric.thy` are rewired onto `certified_reachability` and green
    (2026-06-17 cont.). The executable layer `Planner_STRIPS_*` / `Code_Setup` /
    `Grounding_Pipeline_STRIPS_Executable` / `Planner_STRIPS_Export` was rewired onto the generic
    `(M, dc)` + `dl_certified_model_exec` and is green/validated end-to-end, including the
    `Running_Example` demo (2026-06-18, see top note).)
  - ✅ **Ops/applicable superset DONE (2026-06-17)** — the direction the grounder needs,
    `px_applicable_super` in `Certified_Grounding.thy`: `{π. px.applicable π} ⊆ set (cert_ops_of M)`,
    where `cert_ops_of M` enumerates ground instances of `a_clauses` whose substituted positive
    precondition atoms lie in `M` and whose equality guards hold. Applicable actions are read
    straight off the certified facts `M` — **no `cert_ops` structure needed** (proof reuses
    `enabled_clause_body` + `applicable_alt` + `achievable_def` + `certified_facts_eq_achievable`).
    The reverse inclusion (full `applicable_iff_minimal_model` exactness) is **not** needed for the
    grounder and is left unstated.
- `Certified_Grounding_Locales/Certified_Grounding/Certified_Grounding_Semantics.thy` (rewired
  2026-06-17) — locale `certified_reachability = normalized_problem_rx + fixes M dc + assumes
  numeric_free_problem PX, const_names PX ≠ [], dl_certified_model …, grounding_checks M`;
  `grounding_checks` (decidable wf/coverage of cert facts+ops, augmented with the un-relaxed
  ops' effect atoms); `all_facts_super`/`all_ops_super` via `relax_achievables`/`relax_applicables`;
  ends with `sublocale certified_reachability ⊆ wfg: wf_grounder P cert_facts' cert_ops'` —
  the grounder targets the **un-relaxed** P (grounding the relaxed P_R directly would be
  unsound; an earlier such Locale B was removed).

### Top-session theories in detail

- `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS.thy` — grounded nullary PDDL → STRIPS with
  positive/negative variable pairs (`vpos`/`vneg`) + static `v⊤`/`v⊥`;
  `grounded_normalized_numeric_free_problem.wf_as_strips`; `strips_encodable_problem` with
  `valid_plan_iff`, `restore_pddl_plan_valid` (existence form — `execute_serial_plan` halts at
  the first non-applicable op, so the literal form is false), executable `restore_prefix` +
  `restore_prefix_valid`; parallel→serial bridge (`parallel_solution_imp_serial_solution`,
  generalizes AFP's singleton-only `flattening_lemma`; not needed at runtime since the
  Φ∀ encoding theorem covers it).
- `Grounding_Pipeline_Numeric.thy` — with-numerics pipeline composition: `P⇩X` (explicate) →
  `P⇩N` (split) → `P⇩T` (def-translate), compact per-stage facts, `P⇩G_cert` (conditional on
  `admissible_cert`/`grounding_cert`), `reconstruct_plan_norm`/`reconstruct_plan_ground_cert`,
  `ground_cert_plan_valid_iff`.
- `Grounding_Pipeline_STRIPS.thy` — numeric-free STRIPS specialization: `P⇩S_cert`,
  `wf_as_strips_cert`, `strips_plan_iff_cert` (solvability ⟺),
  `reconstruct_pipeline_plan_cert` + `strips_plan_reconstruct_cert` (STRIPS serial solution →
  concrete valid plan of the original P).
- `Code_Setup.thy` — all code-generation repairs (see Gotchas).
- `Grounding_Pipeline_STRIPS_Executable.thy` — wire-format `dl_program` + `dl_program_of`;
  `normalized_problem_rx`-side mirrors (`grounding_checks_exec` etc.); `ground_by_cert`,
  `ground_via_cert(')`, `reconstruct_plan_by_cert`, and the exec↔locale equality bridges
  (incl. `P_T_normalized_problem_rx_unconditional`, needed because the locale facts'
  exported forms carry cert-context hypotheses).
- `Planner_STRIPS_Executable.thy` — SAT half: `try_horizon` (Φ∀ encode → DIMACS via AFP
  `Solve_SASP`'s `cnf_to_dimacs` → oracle `g` → pull back → **executable model check**
  `𝒜 ⊨ Φ∀` → `decode_plan`), `sat_solve_strips` horizon loop, `plan_by_cert`, and
  **`plan_by_cert_sound`** (0 sorry) — the payoff theorem.
- `Planner_STRIPS_Export.thy` — `export_code` of the planner + oracle datatypes + AST
  constructors (incl. temporal ones the reused parser mentions) → `SMLCodebase/code/`.
- `Running_Example.thy` — Helmert-2009-style example; green `value`s through `P⇩T`/`P⇩R`,
  `dl_program_of`; plus an executable in-Isabelle untrusted oracle `naive_cert` (naive saturation
  of `dl_rules R`, emitting the generic `(M, dc)` pair) with `value` probes for
  `dl_certified_model_exec`, `grounding_checks_exec`, `ground_by_cert`, `ground_via_cert`.
  **Demo only — not on the verified-binary path; green (2026-06-18).** Fully rewired to `(M, dc)`;
  the pre-existing bare-`Var` clash was fixed by qualifying the schemas' `Var` → `variable.Var`.

### SMLCodebase/ (untrusted glue around the exported kernel)

`Makefile` (`make export` regenerates the exported SML via `isabelle build -e`; `make`
compiles with MLton; parser + cmlib/parcom come from the sibling Formal-PDDL-Semantics via the
`FPS_PLANNING` MLB path var — nothing vendored). `pddl_sat_planner.sml` (CLI), `nemo_driver.sml`
(oracle `f`: dl_program → mangled `.rls` + dom guards → `nmo` IDB export + trace → ograph
toposort → `Cert`), `external_sat.sml` (oracle `g`: DIMACS → `$SAT_SOLVER`, default z3) /
`sat_solver.sml` (builtin DPLL, toy only), `pddl_to_isabelle.sml` + `planner_alias.sml`
(parser glue), `json_parse.sml`, `basics.sml`. `.mlb` order matters (`pddl_refactor.sml`'s
`open PDDL` shadows `int`/`not` — keep solvers before it). Examples under `examples/`.

## Proof status (2026-06-17): 0 sorries in this development

The PDDL↔datalog minimal-model relation is **0 sorry** (now in `PDDL_Reachability_Analysis` /
`PDDL_Reachability_Certificate`): both inclusions are proven and `dl_bridge_wf` is discharged, so
`achievable_eq_minimal_model` / `certified_facts_eq_achievable` / `certified_facts_eq_reachable`
hold **hypothesis-free** in `num_free_relaxed_problem` / `certified_pddl`. The retired untrusted
engine and its 4 sorries were **deleted** (2026-06-17); its replacement, the generic verified
`Datalog/Datalog_Evaluation.thy` (`dl_eval`, proven sound), is 0 sorry, and the trimmed
`Reachability_Analysis.thy` (shared infra only) is 0 sorry.

Everything else — every normalization stage, relaxation, grounder, STRIPS conversion, pipeline
wiring, executable mirrors, SAT half, `plan_by_cert_sound` — is 0 sorry. (Three `oops` in
`Common/Graph_Funs.thy`/`Grounding_Utils.thy` are abandoned scratch lemmas, not obligations.)

## Restructure status (2026-06-12 split — verified green 2026-06-17)

The 2026-06-12 session split + bridge move (the standalone `Datalog_Certification` session, and the
bridge/serialization relocation into what was then `Reachability_Certificate.thy`, now
`PDDL_Reachability_Locales.thy` after the 2026-06-17 split) is **verified green** in jEdit, and
`dl_bridge_wf` is discharged (above). `Stratified_Datalog` names (`Cls`, `PosLit`, `Eql`, …) are
visible in `PDDL_Reachability_Locales` with `id.Var`/`id.Cst` capture handled by a `hide_const`.
`Certified_Grounding*` was rewired onto the generic minimal-model entry point (2026-06-17, 0 sorry —
see the "Certified grounding rewired" note). `Grounding_Pipeline_STRIPS/Numeric.thy` are now
rewired onto `certified_reachability` and green (2026-06-17 cont.). The **executable layer**
(`Grounding_Pipeline_STRIPS_Executable`, `Planner_STRIPS_*`, `Code_Setup`, `Planner_STRIPS_Export`,
and the `Running_Example` demo) was rewired onto the generic `(M, dc)` + `dl_certified_model_exec`
and is green/validated end-to-end (2026-06-18). **The full `Tree_Decomp_Grounding` top session is
now consistent.**

## Refactor — split the certificate theory (DONE 2026-06-17)

`Reachability_Certificate.thy` carried **two distinct concerns** — (a) PDDL reachability ⟷ datalog
**minimal model**, and (b) an admissible datalog **certificate** ⟷ PDDL. Now split (per the user
request) into a three-file `_Locales`-convention layout, all green in jEdit:

- **`PDDL_Reachability_Locales`** — the PDDL↔datalog **locale hierarchy**, the `dl_rules`
  serialization, and the `dl_bridge_wf` bundle.
- **`PDDL_Reachability_Analysis`** (`imports …_Locales`) — concern (a): `pddl_datalog` helpers,
  `derivable_init`/`derivable_step_adds`/`derivable_invariant`, `achievable_eq_minimal_model`.
- **`PDDL_Reachability_Certificate`** (`imports …_Analysis`) — concern (b):
  `certified_facts_eq_achievable`, `minimal_model_facts_requirement`, `certified_facts_eq_reachable`.

The seam re-opens the same locales in each file (no top-level hoist → no `[OF …]` breakage). See the
"Latest session" note up top for the importer/ROOT rewiring.

**Retired engine — replaced, not moved (DONE 2026-06-17).** `Reachability_Analysis.thy` was half
**shared PDDL→datalog infra** the certificate depends on and half the **untrusted `semi_naive`
solver** + demo (the 4 sorries). Rather than quarantine the PDDL-specific solver, it was deleted and
replaced by a generic, PDDL-free, verified evaluator `Datalog/Datalog_Evaluation.thy` (`dl_eval`,
total + `[code]` + `dl_eval_sound`), in the `Datalog_Certification` session. The shared infra stays
in the now-0-sorry `Reachability_Analysis.thy`. See the top-of-file session note.

## Other open work (beyond the sorries)

- **`certified_pddl` locale** — DONE (2026-06-17, in `PDDL_Reachability_Locales` +
  `PDDL_Reachability_Certificate`). Extends `num_free_relaxed_problem`, fixes an accepted generic
  certificate (`fixes M dc` + `assumes cert: dl_certified_model (set (dl_rules P)) (set const_names)
  M dc`), exposing `certified_facts_eq_reachable: set M = {f. achievable f}` hypothesis-free.
- **Certified grounding + executable layer** — DONE (2026-06-17 / 2026-06-18). `Certified_Grounding*`
  rewired onto the generic entry point, 0 sorry, `wf_grounder` interpretation discharged; the ops
  superset `px_applicable_super` reads applicable actions off the certified facts `M`. The pipeline
  theories `Grounding_Pipeline_STRIPS/Numeric.thy` are re-pointed onto `certified_reachability P⇩T M dc`
  and green (2026-06-17 cont.). The **executable layer** (`*_Executable`, `Planner_STRIPS_*`,
  `Code_Setup`, `Export`, the SML driver) was rewired onto the generic `(M, dc)` +
  `dl_certified_model_exec` (ordered-cert linear scan for `dl_founded`) and **validates end-to-end**
  (2026-06-18, see top note). The verified cycle-detecting DFS for `dl_founded` (path 2) is future
  work below.
- **`Running_Example.thy` demo — DONE (2026-06-18).** `naive_round`/`naive_sat`/`naive_cert` rewired
  to saturate `dl_rules R` and return the `(M, dc)` pair; `value` probes + descriptive texts updated
  to the generic checker. The pre-existing bare-`Var` clash (the 6 action schemas used bare `Var`,
  which resolved to the AFP datalog `Datalog.id.Var` rather than the PDDL `variable.Var`) was fixed by
  qualifying every `(Var STR …)` → `(variable.Var STR …)` in the schemas (`term.VAR` left untouched)
  and removing the dead `hide_const (open) Datalog.id.Var` block. Fully green; the `value` probes
  evaluate as expected (`dl_certified_model_exec … = True`, `grounding_checks_exec … = True`,
  `ground_via_cert (λ_. my_cert) … = Some (problem_for …)`, empty-cert dummy `= None`).
- **Path 2 — graph topological order / cycle-detection for `dl_founded`** — **DONE (2026-06-18),
  session `Datalog_Graph` (own folder, in `ROOTS`), 0 sorry.** This is a *second, complementary*
  refinement of `dl_founded` — **both discharge paths are kept** (it's efficient): `dl_founded_exec`
  (ordered-cert linear scan) is the fast O(n) check when the certificate carries a trusted order,
  while the graph path lets the rank be *constructed* from acyclicity of the support graph when no
  trusted order is available. Two theories, both `jedit-status`-green:
  - `Datalog_Graph/Graph_Topological_Order.thy` (parent on the graph library, now in the Base heap):
    the **purely graph-theoretic** result `finite E ⟹ (∄p. cycle E p) ⟷ has_top_num E` (the library
    `cycle`, **not** `cycle'`). `has_top_num`/`top_num` (a strictly-increasing vertex numbering);
    `finite_acyclic_imp_has_top_num` via the strict-predecessor-count witness `card {u. (u,x) ∈ E⁺}`;
    `no_cycle_iff_acyclic` whose hard direction `not_acyclic_imp_cycle` (closed walk → proper cycle)
    is proven by `closed_walk_imp_cycle` — strong induction on walk length, peeling the first arc to
    a strictly-shorter *open* walk and extracting a closed sub-walk via `awalk_not_distinct_decomp`.
    `acyclic` is surfaced as first-class API (it gives the HOL `trancl`/`wf`/`acyclic` leverage; the
    `cycle` formulation is the thin equivalent on top).
  - `Datalog_Graph/Datalog_To_Graph.thy`: the **datalog→graph bridge**. `dl_dep_graph c` (edge
    `b → f` per supplied rule with head `f`, body fact `b`); `top_num_imp_dl_founded` (a topological
    numbering *is* a foundedness rank, under the mild `dl_body_closed`); capstones
    `acyclic_dep_graph_imp_dl_founded` / `no_cycle_dep_graph_imp_dl_founded` /
    `acyclic_dep_graph_imp_derivable`; and the **kernel-integration** lemmas
    `dl_admissible_via_acyclic` / `dl_certified_model_via_acyclic` that replace the non-executable
    `dl_founded` conjunct in `dl_admissible` by support-graph acyclicity — so a future verified
    cycle-detecting DFS slots straight into `dl_certified_model` → `dl_certified_model_correct`.
    Documented as *sufficient, not necessary* (the support graph carries edges for *all* rules,
    while `dl_founded` needs only one per fact). A verified DFS *producing* the order is the only
    remaining piece; the kernel side is done.
  - Infra: `Tree_Decomp_Grounding_Base/ROOT` now pulls in `Directed_Set_Graphs` (`Pair_Graph`/`Awalk`
    baked into the heap) so the datalog + graph theories share one heap.
- **End state of the certification story**: parse Nemo's ograph directly into the generic
  `dl_certificate`, export the generic checker, and obtain the reachability requirements via the
  minimal-model theorems by theorem — retiring the duplicated PDDL-side check implementations. (SML
  wiring sketch lived in the now-removed `WIP_datalog_cert_bridge.md`; recover from git history if
  needed.)
- **Upstreaming**: a `def_translate_code` bundle in `Definedness_Translation_Semantics.thy`
  (the only stage without one) and `padl_lit_code`/`distinct_strings_lit_eq[code]` into
  `Common/String_Utils.thy` — both currently patched in `Code_Setup.thy`.
- **Base-heap rebuild** (optional, saves ~10 min jEdit warmup): the `Tree_Decomp_Grounding_Base`
  ROOT already preloads `Solve_SASP`; rebuild the heap to freeze it.
- Optional next step on the evaluator: `dl_eval` is proven **sound**; a **completeness**
  theorem (`{f. datalog_prog.derivable …} \<subseteq> set (dl_eval U Pl)`, via the
  `all_head_facts` iteration bound) would upgrade it to exactly the least model. Not needed for
  trust (the certificate checker validates the oracle's output), so left as future work.

## Gotchas (hard-won; keep in mind)

- **Code generation**: FPS shared-locale constants carry selector-pattern code equations from
  the continuous/temporal interpretations — `[[code drop]]` + re-add the foundational equation
  (`Code_Setup.thy` is the catalogue). `numeric_expression_valuation` is severed with a sound
  self-referential `Code.abort`. Locale defs **with assumptions** yield guarded `_def`s
  ("not an equation") — they need unconditional executable mirrors + equality-under-predicate
  lemmas (the established pattern, now in `PDDL_Reachability_Locales.thy` and
  `Grounding_Pipeline_STRIPS_Executable.thy`).
- **`is_serial_solution_for_problem` is not executable** (`⊆⇩m` over function states); the SAT
  path's only runtime check is the executable model check, serial-ness follows by theorem.
- **Qualify, don't hide**, around the `Solve_SASP` import (SAS+ `ast_problem` namespace):
  `strips_problem.operators_of`, `STRIPS_Semantics.is_serial_solution_for_problem`.
- **jEdit workflow**: verify via the MCP server (jedit-status), never batch-build by default;
  force tail processing with `explore`(find_theorems) at EOF; edit open buffers only via
  `mcp__isabelle__write_file`; `iq.iq` imports are dev-only and must never be committed.
- This is a **git submodule**: push with the push-ssh skill; never `git remote set-url`.

## Document map (after the 2026-06-12 cleanup)

- `HANDOVER.md` (this file) — summary + handover.
- `Datalog/HANDOVER.md` — the `Datalog_Certification` session sub-handoff (kernel internals).
- `ARCHITECTURE_pipeline.md` — pipeline one-pager. `ARCHITECTURE_datalog_certification.md` —
  certification design.
- `README.md` — public-facing overview (refreshed). `GUIDANCE.md` — proof-style principles.
- `CLAUDE.md`/`GEMINI.md` — agent instructions (kept identical).
- `gigante_benchmarks_conditions_effects.md` — survey of the Gigante et al. temporal
  benchmark constructs (reference for future temporal/numeric work; not stale).
- `Documentation/thesis.pdf` — the project thesis.
- Removed as stale/done (recover from git history): `TODO.md` (items absorbed here),
  `WIP_executable_pipeline.md`, `WIP_running_example_certification.md`,
  `Documentation/dependencies.md`, and (2026-06-17) `WIP.md`, `WIP_cert_cleanup_and_locales.md`,
  `WIP_datalog_cert_bridge.md`, `WIP_reverse_direction.md` — their work is done; remaining items are
  folded into this handover.
- Removed 2026-06-18 (never committed; folded into this handover's top note + "Other open work"):
  `WIP_executable_layer.md` (the executable-layer step-by-step) and
  `HANDOVER_2026-06-18_executable_layer.md` (the per-session handover) — the executable layer landed
  and validated end-to-end (including the `Running_Example` demo).
- Removed 2026-06-18 (folded into the Path-2 bullet in "Other open work"): `PLAN_datalog_graph.md`
  — the `Datalog_Graph` theories (`Graph_Topological_Order`, `Datalog_To_Graph`) landed and are
  green/0-sorry, so the plan is done.
