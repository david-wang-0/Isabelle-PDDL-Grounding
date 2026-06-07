# WIP: Reachability analysis via a verified datalog certificate

> ## ⚠ CORRECTION (2026-06-06): the grounding target is P⇩N, not P⇩R
>
> **The certificate certifies the relaxed reachable _set_; the grounded _task_ must still be
> built over the un-relaxed P⇩N (real add+delete effects).** Conflating these is unsound.
>
> - An untrusted certifying solver (Fast Downward's grounder, or Nemo) runs the **delete-relaxed
>   reachability**; our kernel only *checks* the certificate (`admissible`). What comes out,
>   trusted, is the reachable ground atom/action **set** of the relaxed problem
>   (`cert_facts`/`cert_ops`). This is "grounding" in the FD sense (relaxed reachability decides
>   which ground atoms/actions exist) — and we never prove the solver. ✅ Keep all of this.
> - But that set is only the **pruning oracle**. The grounded *task* handed to the SAT planner
>   must carry P⇩N's **real deletes** — a plan for the delete-relaxed problem (`relax_eff` drops
>   deletes, `PDDL_Relaxation_Locales.thy:19`) is a relaxed plan, not executable in the real task.
> - **The bug it exposes:** `Reachability_Certificate.thy:474`
>   `sublocale certified_reachability ⊆ wf_grounder P cert_facts' cert_ops'` interprets the
>   grounder at the **relaxed** `P` (`certified_reachability = pddl_datalog = relaxed_problem`,
>   whose `P` has positive preconditions / no deletes). Its `valid_classical_plan_iff`
>   (`Grounded_PDDL.thy:999`) then certifies `(P⇩R)_G ↔ P⇩R` — the over-approximation, **not**
>   P⇩N. `relax_achievables` (`PDDL_Relaxation_Semantics.thy:289`) is only one-directional
>   (`{achievable} ⊆ {px.achievable}`), so P⇩R can be solvable when P⇩N is not. The stated
>   plug-in cannot discharge the pipeline's `wf_grounder P⇩N` goal — different problems.
>
> **Fix (two options):**
> 1. **Explicit bridge.** Keep `closure_sound` over the relaxed problem, but make Locale B target
>    P⇩N: `wf_grounder P⇩N cert_facts cert_ops`, discharging `all_facts` by composing
>    `{achievable P⇩N} ⊆ {achievable P⇩R}` (`relax_achievables`, a verified PDDL fact) with
>    `{achievable P⇩R} ⊆ set cert_facts` (`closure_sound`). This mirrors the pipeline's existing
>    `wf_grounder P⇩N all_facts all_pactions` (`Grounding_Pipeline.thy:290`) — the certificate
>    just swaps the oracle's *producer* (`semi_naive_eval` → checked certificate); grounding
>    target and bridge are unchanged. Needs both P⇩N and its relaxation in scope (build Locale B
>    from `normalized_problem_rx`, which has `P` and `px` both, not from bare `relaxed_problem`).
> 2. **Fold relaxation into the closure check.** Don't materialize P⇩R at all. State
>    `closure_check` over **P⇩N's** actions using `pos_lits_of (ac_pre)` + adds (drop negative
>    precondition literals and deletes *in the operator*). Since `pre` holding implies its
>    positive atoms hold even when `pre` has negative literals, `closure_sound` proves
>    `{achievable P⇩N} ⊆ cert` **directly** — the over-approximation lives in the one soundness
>    proof, and `relax_prob`/`relax_achievables` drop out. The certificate is still a
>    relaxed-reachability certificate from the untrusted solver.
>
> Everything below predates this correction; read the Option-2 note and Building blocks #3/#4
> with the "grounder targets P⇩N" fix applied.

> ## ✅ DONE (2026-06-06): certificate→grounder bridge is sorry-free
>
> `px_cert_ops_super` is **proved** and the whole `certified_reachability` chain
> (`Reachability_Certificate` + `Certified_Grounding_Locales`/`_`/`_Semantics`) is **0 sorries,
> 0 errors, fully consolidated**. Method: in Locale A, **`cert_ops` was redefined from the engine
> (`all_derivs`) to a finite enumeration** (over `a_clauses × all_combos`, filtered by
> "pos-precondition ⊆ cert_facts ∧ guards") — the ops mirror of the `closure_check` facts redesign —
> and `cert_ops_sound : closure_check c ⟹ {applicable} ⊆ set (cert_ops c)` proved by plan induction
> structurally identical to `closure_step_adds`. The dead unsound old Locale B
> (`certified_reachability = pddl_datalog`) and the unused `admissible_exact` sorry were removed.
> The `wf_grounder P cert_facts' cert_ops'` sublocale at **P_N** is fully discharged.
> **Next: Building block #4 — rewire `Grounding_Pipeline.wf_grounder_args`.** Everything below
> predates this and describes the path taken.
>
> ### Building block #4 — pipeline wiring (IN PROGRESS, 2026-06-07)
>
> The pipeline was rethreaded (partly by a parallel external edit) so the grounding target is
> **`P_T = def_translate P_N`** (numeric-free, normalized) and its relaxation `P_R = relax P_T` is
> what the certificate certifies — matching the certificate framework (which grounds the same
> problem it relaxes). New `Grounding_Pipeline` pieces, all inside a
> `context fixes cert assumes admissible_cert: pddl_datalog.admissible (relax_prob P_T) cert and
> grounding_cert: normalized_problem_rx.grounding_checks P_T cert`:
> `P_T_normalized_problem_rx`, `certified_reachability_i` (interprets the locale at `P_T`),
> `P\<^sub>G_cert = grounder.ground_prob P_T (cert_facts_of P_T cert) (cert_ops_of P_T cert)`,
> `wf_ground_cert_problem`, `ground_cert_plan_valid_iff`, `ground_cert_plan_reconstruct`, plus the
> STRIPS-side `P\<^sub>S_cert`/`wf_as_strips_cert`.
>
> **Done:** completed `normalization_normalizes` (was a dangling proof); added
> `def_translate_valid_iff_compact` / `def_translate_valid_plan_iff_compact`; rethreaded
> `relaxation_applicables`/`relaxation_achievables`/`relaxation_wf_relaxed_normed` onto `P_T`.
> **Added the missing import** `Reachability_Analysis.Certified_Grounding_Semantics` (the file was
> referencing `pddl_datalog.admissible` / `certified_reachability` / `normalized_problem_rx.*`
> without importing the bridge).
> **Open issues (being fixed):** (a) `restore_plan_def_translate_compact` is *used* but not
> defined — needs adding (restore is identity, so it follows from `def_translate_valid_plan_iff`);
> (b) the `ground_cert_plan_reconstruct` chain looks mis-qualified — the intermediate
> `valid_classical_plan2 (restore_plan_def_translate q)` should be at **`P_N`**, not the base `P`
> (def_translate maps `P_T`-plan → `P_N`-plan; `reconstruct_plan_norm` then maps `P_N` → base `P`);
> (c) `ground_prob_normed` (`wf_grounder`) is still `sorry`.
>
> **PDDL_to_STRIPS / STRIPS target:** the STRIPS type already IS the AFP SAT planner's input
> (`name strips_problem` / `is_serial_solution_for_problem` from `Verified_SAT_Based_AI_Planning`).
> But `PDDL_to_STRIPS.thy` is unrefactored: it must drop the old `PDDL_STRIPS_Semantics` dependency
> (new numeric atom type), `wf_empty_lit` is FALSE under numeric atoms (now a documented `sorry`),
> and ~20 errors remain (API drift: `wf_D` arity, pair `world_model`, `resolve_action_schema`;
> string-ineq gaps; `oops` semantics-preservation stubs). See `[[project_pddl_to_strips_new_semantics]]`.

Status: **⊇ soundness FULLY PROVED & green** (2026-06-06).
`Reachability_Analysis/Reachability_Certificate.thy` compiles clean (0 errors, fully
processed) with the Nemo-aligned certificate datatype (`CNode (cn_fact) (cn_preds: nat list)`
/ `Cert`), the `closure_check` (now a finite executable model check) / `ordered_check` /
`local_valid` / `admissible` / `cert_ops` definitions, and Locales A (`pddl_datalog`) and B
(`certified_reachability`). The whole `closure_sound` (⊇) path is sorry-free. **3 sorries
left:** `all_ops_super`, the `wf_grounder` sublocale, and `admissible_exact` (the last to be
dropped/weakened per the Option-2 design decision below).

**Proved this round:** `closure_sound` (the ⊇ anchor) — *structurally*, by reducing it to two
kernels via a plan-induction invariant; `closure_invariant` (every reachable world model's
facts stay in a closed certificate, by induction on the plan using
`apply_ground_action_alt`: `fst M' = (fst M - dels) ∪ adds`); `closure_init_sub` (**Kernel
1**, initial facts ⊆ cert); the reusable `in_orga_update_facts` / `in_orga_organize_facts`
round-trip (over predicate-atom lists, `organize_facts` membership = list membership);
`all_facts_super`. `closure_check` gained a `(∀f∈set fs. is_predAtom f)` conjunct (genuinely
required — `organize_facts`/`in_orga` are only meaningful on predicate atoms). `fst I =
set (filter is_predAtom (init P))`; `set init' ⊇ set (init P)` via `conc_unique_un`.

**Kernel 2 (`closure_step_adds`) — FULLY PROVED.** The ⊇ soundness path
`closure_sound`→`closure_invariant`→`closure_step_adds`→{`enabled_clause_body`,
`consequence_in_cert`} plus `closure_init_sub` is now entirely sorry-free.

> **Design change (2026-06-05): `closure_check` is now a finite, executable model check
> decoupled from the engine.** Instead of `∀w∈cert. all_derivs w (organize_facts cert) ⊆ cert`
> it is now: cert facts are predicate atoms, `init' ⊆ cert`, and for every action clause and
> every argument tuple from `all_combos ✓ (replicate (length params) const_names)` (the finite
> object-name combinations), *if* the instantiated positive precondition is ⊆ cert and the
> equality guards hold, *then* the instantiated adds are ⊆ cert. This makes `consequence_in_cert`
> immediate (no engine-instantiation-completeness needed) and keeps the engine purely an
> untrusted producer — exactly the plan's philosophy. Key supporting lemmas:
> `set_all_combos`/`chosen_from_replicate` (Graph_Funs), `is_obj_of_type_const_name`
> (`is_obj_of_type n T ⟹ n ∈ set const_names`, via `objT_alt`), `action_params_match_combos`.
> The `in_orga`/`organize_facts` round-trip lemmas are now unused (harmless).

Sub-parts 1–3, all now proved:
1. **`res_inst_adds_eq_consequence` — PROVED.** `adds (effect (the (res_inst (SimplePlanAction
   n args)))) = consequence_of (as_action_clause schema) args` when the schema for `n` is in
   `actions D`. Both sides reduce to `map (map_atom_fmla (ac_tsubst params args)) (adds eff)`
   (via `res_inst_cond`, `Effect (adds)(dels)(numeric_effects)`, `as_action_clause`/`consequence_of`).
2. **`enabled_clause_body` (relaxation precond) — PROVED.** Enabled ⟹ instantiated positive
   precondition atoms `map (map_atom_fmla (ac_tsubst params args)) (cl_pred_pre clause)` ⊆
   `fst M`, and the `cl_cond_pre` equality guards `satisfies_conds … args`. Via the `⊨⇩m`
   map-semantics helpers `map_formula_semantics_simps`, `valuation_predAtm_iff`,
   `un_and_map_semantics`, `un_and_map_atom_fmla`, `cond_lit_model_indep` (equality guards are
   model-independent, so they hold under the empty model `({}, Map.empty)` the engine uses).
3. **`consequence_in_cert` — PROVED, immediately** (no engine-completeness mountain), thanks to
   the finite-enumeration `closure_check` redesign above: the closure conjunct *is* exactly the
   property, instantiated at the clause + `args ∈ combos`. `closure_step_adds` establishes
   `args ∈ combos` from `action_params_match_combos`.

**3 sorries remain:** `all_ops_super` (ops ⊇), the `wf_grounder` sublocale, and
`admissible_exact` (= / tightness). **The whole ⊇ soundness path
`closure_sound`→`closure_step_adds` is fully proved and green.** The old
`plan_action`/`pa_of_classical` bridge was dropped — `all_derivs` already yields
`ast_classical_plan_action`, matching `applicable`/`wf_grounder`.

> **Design decision (2026-06-06): the certificate is the delete-relaxed reachable set, so it
> over-approximates the true PDDL-reachable set (Option 2).** The grounder's `effs_covered`
> (`Grounded_PDDL.thy:198`) needs *every* effect atom — adds **and dels** — of each applicable
> op to be in `facts`, because `ga_eff` rewrites del atoms through `fact_map`/`ground_fmla`
> (`Grounded_PDDL.thy:90,99,112`) and an uncovered atom grounds to `the None` (undefined). Since
> `as_action_clause` drops del effects, the certificate must be strengthened to also contain the
> adds+dels of applicable ops, read from the **original action schemas**. Consequence: the
> certificate is a *strict superset* of `{achievable}` (it contains facts/actions unreachable in
> real PDDL but reachable in the delete-relaxed Datalog closure), so the exact-equality theorem
> **`admissible_exact` is dropped/weakened** — which is consistent with the delete-relaxed
> framing where exactness was never the goal. `wf_grounder` only needs supersets anyway.

> **Certificate format is fixed: it is a Nemo proof certificate.** The certificate our
> kernel re-checks is *produced by [Nemo](https://github.com/knowsys/nemo)* and the
> reference verified checker is `~/work/CertifyingDatalog` (Lean 4). The concrete JSON
> formats, the `ograph` (ordered-graph) structure we mirror, the `locallyValid` check, and
> the soundness-direction caveat are written up in **`WIP_nemo_certificate_format.md`** —
> read it alongside this plan. The summary below folds those findings into the building
> blocks; the Nemo doc is the source of truth for the on-the-wire format.

## Goal

Replace the unverified, hard-to-prove `semi_naive_eval` reachability with a
**certificate-checking** approach: an (untrusted) engine computes the reachable
set; a verified kernel re-checks that its output is admissible, and only then
feeds it to `wf_grounder`.

## Where this plugs in

The pipeline (`Grounding_Pipeline.thy`) runs reachability on the **relaxed**
problem `P\<^sub>R` (positive preconditions, single datalog stratum) and currently
depends on two *sorried* equalities in the `relaxed_problem` context
(`Reachability_Analysis.thy:341-347`):

```
found_facts_achievable:    set (snd semi_naive_eval) = {f. achievable f}
found_pactions_applicable: set (fst semi_naive_eval) = {f. applicable f}
```

`wf_grounder` (`Grounded_PDDL.thy:108`) only requires **supersets**:

- `all_facts: set facts \<supseteq> {a. achievable a}`   (`Grounded_PDDL.thy:112`)
- `all_ops:   set ops   \<supseteq> {\<pi>. applicable \<pi>}` (`Grounded_PDDL.thy:115`)

So:

- **Closure check = soundness (\<supseteq>).** The certificate set is a *model* (closed
  under the immediate-consequence operator). This is all the pipeline's
  correctness theorems need.
- **Acyclicity check = tightness (\<subseteq>).** Gives exact equality (least model =
  reachable set); needed to retire the `found_*` theorems and keep grounding
  small, but *not* required for soundness.

Build closure first, acyclicity second. After the closure proof lands, the
grounder pipeline is sorry-free on the reachability side even before the
(harder, optional) acyclicity proof.

## Key finding: AFP datalog has NO fixpoint semantics

AFP's `Stratified_Datalog/Datalog.thy` is purely
model/order-theoretic:

- `solves_program \<rho> dl` (`:69`) — \<rho> satisfies every clause (a *model*).
- `least_solution` (`:379`) — solution below all solutions in the stratified
  order `lte`/`lt` (`:362-377`); for a single stratum (`s = \<lambda>_. 0`) this
  collapses to **pointwise \<subseteq>**.
- Existence (`exi_least_solution`, `:1457`) and leastness come via `solve_pg`,
  an **intersection construction** (`Inter'`) — NOT a `T_P` iteration.
- **No immediate-consequence operator, no `lfp`, no Kleene chain** anywhere.

We must add the fixpoint layer ourselves. Decision (2026-06-05): **self-contained
`T_P`/`lfp`** — reuse only AFP's syntax + model semantics; skip AFP's
stratification/`least_solution`, since reachability only ever runs on the
relaxed (positive, single-stratum) program.

(Sanity check on this layer: `~/work/CertifyingDatalog`'s `Datalog/Semantics.lean` already
formalizes, in Lean, the equivalence we rely on — `proofTheoreticSemantics`
[has-a-proof-tree, = `lfp`] `=` `modelTheoreticSemantics` [`\<Inter>` of all models], with the
"is a model" lemmas. So our `lfp`-is-the-least-model obligations are a known, mechanizable
result, not a research risk; we just redo them in Isabelle.)

## Optional middle path: cite AFP `solves_program` without the `lfp` mountain

**When to take it:** if the goal is only to *reuse a vetted AFP datalog semantics* (so the
certificate is certified "a model" in `Stratified_Datalog`'s vocabulary), **not** to obtain
exact equality. This is a small, self-contained add-on on top of the *already-green*
`closure_sound` (⊇) path — it does **not** replace it and does **not** require Building
blocks #0/#1 (`T_dl`, `lfp`, Kleene, or `achievable_iff_lfp`).

Cost asymmetry that motivates it: the current `closure_check` already proves the certificate
facts are closed under the immediate-consequence operator — i.e. *a model*. AFP
`Stratified_Datalog`'s `solves_program` (`Datalog.thy:69`) is *exactly* a model predicate
(`∀ clause ∈ dl. ∀ var_val. meaning_cls`). So the bridge is a re-reading of an existing
finite check into AFP's definition, with no fixpoint theory in between.

**What to add (one new theory, ~one definition + one lemma, no deep semantics):**

1. **Program encoding only** `dl_of_prob :: "(…) dl_program"` — the *program* half of the old
   Building block #1, **without** the `achievable_iff_lfp` anchor. One `Cls` per action clause
   (head = an add-effect atom, body = `cl_pred_pre` positive precondition atoms as `rh`s, with
   `Eq`-style `rh`s for the `cl_cond_pre` guards); init facts as body-less clauses. Maps
   `predicate → 'p`, `object → 'c`, `variable → 'x`. Reuse the existing `a_clauses` /
   `consequence_of` / `cl_pred_pre` / `cl_cond_pre` data so the encoding lines up with
   `closure_check` term-for-term.
2. **Lift** `pred_val_of_cert :: "certificate ⇒ ('p,'c) pred_val"` — send each predicate atom
   in `cert_facts` to its argument tuple under predicate `p`
   (`p ↦ {args | Atom (predAtm p args) ∈ set (cert_facts c)}`).
3. **Bridge lemma** `closure_check_solves`:
   `closure_check c ⟹ pred_val_of_cert c ⊨⇩d⇩l dl_of_prob`.
   Unfold `solves_program`/`solves_cls`/`meaning_cls`: fix a clause and a `var_val`; the
   `var_val` instantiates the clause's variables to objects, which is exactly an `args` tuple
   from `all_combos ✓ (replicate … const_names)` (reuse `action_params_match_combos` /
   `set_all_combos`). Then the clause body holding under `pred_val_of_cert` is `set (map
   (map_atom_fmla (ac_tsubst …)) (cl_pred_pre cl)) ⊆ set (cert_facts c)` plus the `cl_cond_pre`
   guards — precisely the antecedent of the `closure_check` conjunct — whose conclusion gives
   the head atom in `cert_facts`, i.e. `meaning_cls` holds. The only fiddly part is the
   `var_val ↔ args`/`ac_tsubst` correspondence on `meaning_rh`/`eval_id`; everything else is
   the existing closure conjunct read backwards.

**What it does and does NOT give:**
- ✅ "The certificate is a model of `dl_of_prob` in the sense of AFP `Stratified_Datalog`."
  Lets the writeup *cite* the vetted semantics for the soundness story.
- ❌ Soundness of the pipeline still comes from `closure_sound` (the PDDL-side plan induction),
  **not** from this lemma — the bridge alone says nothing about `{achievable}` unless paired
  with `lfp ≤` any model, which needs Building block #0. (If you ever add #0's
  `model ⟹ lfp ≤ model`, this lemma is the missing half that yields `{achievable} ⊆ cert`
  *through* the datalog layer instead of directly.)
- ❌ No exactness (`admissible_exact` stays dropped per the Option-2 decision).

**Effort:** small. One theory importing `Stratified_Datalog.Datalog`; no `lfp`/Kleene/order
theory; the bridge lemma is structurally the `closure_check` conjunct re-expressed through
`meaning_cls`. Reuses `a_clauses`, `cl_pred_pre`/`cl_cond_pre`, `action_params_match_combos`,
`set_all_combos`. Independent of, and parallel to, the (deferred) exactness machinery.

## Graph-library constraint: `DFS_Cycles` is undirected-only (checked 2026-06-05)

The graph library's cycle detector is unusable for a directed support graph:

- `DFS_Cycles` locale bakes **symmetry + irreflexivity** into its graph
  invariant (`Isabelle-Graph-Library/.../DFS_Cycles.thy:89-90`) and derives
  `graph_symmetric[simp]` (`:330`) — it detects *undirected* cycles. A datalog
  support graph is directed; a shared premise (diamond) is an undirected cycle
  but a valid DAG, so this checker would spuriously reject good certificates.
- **No directed `DFS_Cycles` is committed on any branch** (`afp-2025-2-compat`
  [current/pinned `f26a1f5`], `main`, `verified-sat-planner` all share DFS
  history up to `ba6ce02`). No remote updates pending.
- `DFS_Cycles_Aux_Directed_Sketch.thy` exists only as a **local untracked file**
  (`??`, never `git add`ed) and is a **sketch** — its 4 main correctness
  theorems are `sorry` (`:424-440`), 12 sorry/TODO markers total. It does drop
  symmetry and detect directed cycles via back-edge-into-open-stack
  (white/grey/black), i.e. the right idea, but it is unproven WIP.

**Upstream checked too (2026-06-05):** origin is the fork `david-wang-0/...`;
parent is `mabdula/Isabelle-Graph-Library`. Across all branches of both
(fork: afp-2025-2-compat/main/verified-sat-planner; upstream: main/Imperative/
fds_book) there is **no verified directed-cycle algorithm** — `Imperative` only
adds imperative/AVL/time refinements of reachability DFS. Nothing to pull.

The directed-cycle *predicates* do exist though (`Awalk_Defs.thy`): `cycle`
(`:35`) is a genuine directed cycle; `cycle'` (`:41`) = `cycle \<and> length>2` is
**undirected-only by design** (its comment says so — the `>2` guard drops
`A\<rightarrow>B\<rightarrow>A`). `DFS_Cycles` is stated against `cycle'`, hence the symmetry binding.
If acyclicity is ever restated in library terms, use `cycle` (NOT `cycle'`,
which silently ignores 2-cycles/self-loops — real cycles in a digraph).

\<Rightarrow> **Do not depend on the graph-library DFS for the acyclic check.** Use the
rank/level certificate (Building block #2) instead: no graph traversal, no
verified DFS, and the rank doubles as the well-founded order for `cert \<le> lfp`.

---

## Plan

### Building block #0 — `Reachability_Analysis/Datalog_Fixpoint.thy` (new)

Sits on top of AFP's `clause` / `meaning_cls` / `solves_program` (so "is a
model" matches a vetted definition), adding:

1. `T_dl :: dl_program \<Rightarrow> pred_val \<Rightarrow> pred_val` — immediate consequence over
   ground clause instances. Carrier `pred_val = 'p \<Rightarrow> 'c list set` is already a
   **complete lattice** in HOL (function space into `set`), so `mono`, `lfp`,
   `lfp_unfold`, `lfp_induct` come from the distribution — no order theory to
   rebuild.
2. **Positivity** (relaxed program has no negative `rh`) \<Longrightarrow> `mono (T_dl dl)`.
   This is where relaxation pays off: single stratum, monotone operator.
3. **Bridge A — model = pre-fixpoint:** `\<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<longleftrightarrow> T_dl dl \<rho> \<le> \<rho>`.
   (\<Rightarrow> closure-check \<Longrightarrow> overapproximation.)
4. **Kleene:** `lfp (T_dl dl) = (\<Squnion>n. (T_dl dl ^^ n) \<bottom>)` — finite clause bodies
   \<Longrightarrow> Sup-continuity \<Longrightarrow> Kleene fixpoint. (\<Rightarrow> acyclic-support \<Longrightarrow> membership induction.)
5. `lfp (T_dl dl)` is *the* reachable predicate valuation; prove it is itself a
   model (`solves_program`) and the least one — self-contained, not via
   `solve_pg`.

### Building block #1 — `Reachability_Analysis/Datalog_Encoding.thy` (new)

Encode a normalized+relaxed PDDL problem as a `dl_program`:

- One clause per action schema: head = an add-effect atom, body = positive
  precondition atoms; predicate constants / `Eq` rhs for the `cond_pre` guards.
  Maps `predicate \<rightarrow> 'p`, `object \<rightarrow> 'c`, `variable \<rightarrow> 'x`. Init facts = bodyless
  clauses. `definition (in ast_problem) dl_of_prob :: "... dl_program"`.
- `fact_rel`: correspondence `object atom formula \<longleftrightarrow> ('p,'c) lh`, lifting a
  `pred_val` to a set of PDDL facts.
- **Semantic anchor (the one hard proof):**
  `achievable_iff_lfp: achievable f \<longleftrightarrow> (f corresponds to an atom in lfp (T_dl dl_of_prob))`.
  Connects `valid_classical_plan_alt` execution (`achievable_def`,
  `Normalization_Definitions.thy:287`) to datalog derivation. `T_P` iteration
  mirrors plan steps, so this is far more natural operationally than via
  `solve_pg`. Everything downstream is finite checking.

### Building block #2 — `Reachability_Analysis/Reachability_Certificate.thy` — **Locale A**

```
locale pddl_datalog = relaxed_problem   (* bundles wf + normalized + relaxed; dl is positive *)
```

(The skeleton already uses `relaxed_problem`, which packages the plan's
`assumes normalized, relaxed` plus well-formedness.)

- **Certificate datatype = Nemo `ograph`** (see `WIP_nemo_certificate_format.md`). Each node
  is a derived fact plus the *indices* of the predecessor facts that justify it; the list
  order IS the derivation rank, and the `j < i` invariant is *checked*, giving acyclicity by
  construction (no stored `nat` rank field, no DFS):

  ```
  datatype cert_node  = CNode (cn_fact: facty) (cn_preds: "nat list")
  datatype certificate = Cert (nodes: "cert_node list")
  cert_facts c = map cn_fact (nodes c)
  cn_body  c i = map (\<lambda>j. cn_fact (nodes c ! j)) (cn_preds (nodes c ! i))
  ```

  (Supersedes the old `Cert (cert_facts) (cert_rules)` / explicit-rank sketch and the current
  skeleton's `cert_entry` with `(plan_action \<times> facty list) option + nat`.)
- **Closure check** `closure_check` (= Nemo *model check*, the **essential \<supseteq>** direction):
  one round of `all_derivs` over `cert_facts` produces no fact outside `cert_facts`, and
  `init' \<subseteq> cert_facts`. Reuse `all_derivs`/`update_facts`/`in_orga`
  (`Reachability_Analysis.thy`) as the executable one-step operator — the engine stays an
  untrusted producer, related to the abstract `T_dl` only at the certificate boundary. Gives
  `lfp \<le> cert`, hence (via `achievable_iff_lfp`) `{achievable} \<subseteq> cert_facts`. **This is all
  the pipeline needs; it ignores `cn_preds` entirely (just the fact set).**
- **Ordered / `local_valid` check** (= Nemo `ograph` `locallyValid`, the **\<subseteq> exactness**
  upgrade — a rank certificate, NOT a DFS, see "Graph-library constraint" below):
  `ordered_check c \<equiv> \<forall>i<length (nodes c). \<forall>j\<in>set (cn_preds (nodes c!i)). j<i`, plus for every
  node `i`: either `cn_preds = []` and `cn_fact \<in> init'`, or there is a clause
  `cl \<in> pred_clauses` and `args` with the `cl_cond_pre` guards satisfied,
  `cn_fact \<in> consequence_of cl args`, and `cn_body c i` equal to the ground positive
  preconditions `map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl)`. The
  index is the well-founded order: by induction on `i`, every cert node is at Kleene stage
  `\<le> i`, giving `cert \<le> lfp` (the `\<subseteq>` direction). No graph traversal, no verified DFS.
- `definition admissible cert \<equiv> closure_check cert \<and> ordered_check cert \<and> (\<forall>i. local_valid cert i)`.
- Results:
  - `admissible_model: admissible cert \<Longrightarrow> {a. achievable a} \<subseteq> set (cert_facts cert)`
    (closure + `achievable_iff_lfp`)  — **soundness**
  - `admissible_exact: admissible cert \<Longrightarrow> {a. achievable a} = set (cert_facts cert)`
    (adds acyclic \<subseteq>)  — **tightness**

### Building block #3 — **Locale B**, the P⇩N↔certificate bridge (OPTION 1, concrete spec; 3 small theories — see Step 0)

> **STATUS 2026-06-06: skeleton LANDED & GREEN** (all three theories `fully_processed` +
> `consolidated`, 0 errors). Created `Certified_Grounding_Locales.thy` /
> `Certified_Grounding.thy` / `Certified_Grounding_Semantics.thy`; added `PDDL_Relaxation` dep +
> the 3 theories to `Reachability_Analysis/ROOT`. **Proven (no sorry):** Step-1 sublocale
> `normalized_problem_rx ⊆ px: pddl_datalog PX` (`by (simp add: normalized_problem_def'
> relaxed_problem.intro relaxed_problem_axioms_def relax_wf relax_normed relax_relaxes)`); the
> `cert_ops'`/`extra_del_atoms`/`cert_facts'` defs; `all_facts_super` (via `px.closure_sound` ∘
> `relax_achievables`); and in the `wf_grounder P cert_facts' cert_ops'` sublocale, 5/12
> obligations: `wf_problem` (`wf_classical_problem`), `facts_dist`/`ops_dist` (`remdups`),
> `all_facts` (`all_facts_super`), `all_ops` (`all_ops_super`). **The grounder is now interpreted
> at P⇩N** — `certified_reachability` inherits `valid_classical_plan_iff` at the right problem.
>
> **UPDATE 2026-06-06 — ROUTE 2 DONE: down to 1 sorry.** Chose Route 2 (strengthen the checked
> conditions). The 7 syntactic grounder obligations (`facts_wf`, `ops_wf`, `effs_covered`,
> `pres_covered`, `goal_covered`, `init_props`, `ops_no_num`) are all decidable, so they are
> bundled into an executable `grounding_checks :: certificate ⇒ bool` predicate (defined in the
> `normalized_problem_rx` context over `cert_facts_of`/`cert_ops_of`), which `certified_reachability`
> assumes as `grounding_cert` alongside `admissible_cert`. This is the certifying-kernel philosophy
> (same as `admissible`): the untrusted producer must supply a certificate that *passes* the
> decidable re-check. Each obligation is then a one-line `using grounding_cert unfolding
> grounding_checks_def … by simp` (lemmas `facts_wf_l`…`ops_no_num_l` in
> `Certified_Grounding_Semantics`), and the `wf_grounder P cert_facts' cert_ops'` sublocale is
> **fully discharged**. `extra_del_atoms` was generalised to `extra_eff_atoms` (adds+dels) so
> `effs_covered` is even re-checkable. The semantic supersets stay proofs, not checks:
> `all_facts` from `closure_sound`∘`relax_achievables`; `all_ops` from `relax_applicables`∘
> `px_cert_ops_super`.
>
> **The ONLY remaining sorry (MCP-confirmed, `Certified_Grounding.thy:35`):**
> `px_cert_ops_super : {π. px.applicable π} ⊆ set (px.cert_ops cert)` — the ops analogue of
> `closure_sound` (relaxed-problem ops soundness). It is genuinely *not* decidable (quantifies over
> plans), so it can't be a check; it needs a soundness proof like `closure_sound`, and morally
> belongs in `pddl_datalog`. This was always the open gap (old `all_ops_super` sorry).
>
> Net: the certificate→grounder bridge at P⇩N is complete except this one semantic ops-soundness
> lemma. Next: prove `px_cert_ops_super` in `pddl_datalog` (mirror `closure_sound`'s plan-induction,
> ops side), then rewire `Grounding_Pipeline.wf_grounder_args` (Building block #4).

> Decided 2026-06-06: **Option 1 (explicit bridge).** Keep `closure_sound` exactly as proven
> over the relaxed problem; bridge it to P⇩N with the existing `relax_achievables` /
> `relax_applicables`. (Option 2 — fold the relaxation into `closure_check` over P⇩N and re-prove
> `closure_sound` there — is the cleaner end state but re-proves the kernel; not taken now.)

Keep **Locale A** (`pddl_datalog = relaxed_problem`, `closure_check`/`admissible`/`closure_sound`,
`Reachability_Certificate.thy:126`) **untouched** — it is the problem-agnostic certificate kernel
and `closure_sound` (`:415`) stays green. All the new wiring is in a separate theory.

The load-bearing structural fact: `wf_grounder ?P ?facts ?ops` (`Grounded_PDDL.thy:187`) is fully
parameterised by `?P` — every obligation (`all_facts`, `all_ops`, `effs_covered`, …) is over `?P`,
and `valid_classical_plan_iff` (`:999`) certifies `?P \<leftrightarrow> (?P)_G`. So we interpret it at **P⇩N**.

**Step 0 — new theories + imports/ROOT.** Don't put this in one massive file — follow the
`_Locales` / main / `_Semantics` split the other steps use (cf. `PDDL_Relaxation_Locales` /
`PDDL_Relaxation` / `PDDL_Relaxation_Semantics`). Three small theories under
`Reachability_Analysis/`:
- `Certified_Grounding_Locales.thy` — `imports Reachability_Certificate
  PDDL_Relaxation.PDDL_Relaxation_Semantics`; the Step-1 `px: pddl_datalog PX` sublocale, the
  Locale B header (`certified_reachability`), and the `cert_facts'`/`cert_ops'`/`extra_del_atoms`
  definitions (Steps 1–2 defs + Step 3 def). No deep proofs.
- `Certified_Grounding.thy` — `imports Certified_Grounding_Locales`; the superset lemmas
  `all_facts_super` / `all_ops_super` (Step 2) and the `effs_covered` dels lemma (Step 3).
- `Certified_Grounding_Semantics.thy` — `imports Certified_Grounding`; the Step-4
  `sublocale certified_reachability \<subseteq> wf_grounder P \<dots>` discharging the grounder obligations.

Add `PDDL_Relaxation` to the `sessions` of `Reachability_Analysis/ROOT` and the three theories to
its `theories`. ⚠ New session dep ⇒ heap rebuild; a stale jEdit cannot verify it until the user
reopens (cf. memory `project_reachability_analysis_session`).

**Step 1 — expose the kernel at the relaxation.** PX is a `relaxed_problem`
(`relax_relaxes : px.relaxed_prob`, `PDDL_Relaxation.thy:44`; `px: normalized_problem PX` already
at `:113`), and `pddl_datalog = relaxed_problem` adds nothing, so:
```isabelle
sublocale normalized_problem_rx \<subseteq> px: pddl_datalog PX
  by unfold_locales (use relax_relaxes in \<open>simp add: relaxed_problem_def relaxed_problem_axioms_def
                                                       normalized_problem_def' \<dots>\<close>)
```
Now `px.closure_check`, `px.cert_facts`, `px.cert_ops`, and
`px.closure_sound : {px.achievable} \<subseteq> set (px.cert_facts c)` are all available at PX.

**Step 2 — Locale B over `normalized_problem_rx`** (so both P⇩N and `px` are in scope):
```isabelle
locale certified_reachability = normalized_problem_rx +
  fixes cert :: certificate
  assumes admissible_cert: "px.admissible cert"
begin
  definition "cert_facts' \<equiv> px.cert_facts cert @ extra_del_atoms"   (* Step 3 *)
  definition "cert_ops'   \<equiv> px.cert_ops cert"

  lemma all_facts_super: "fact_to_facty ` {a. achievable a} \<subseteq> set cert_facts'"
    (* relax_achievables (PDDL_Relaxation_Semantics.thy:289): {achievable} \<subseteq> {px.achievable};
       px.closure_sound (admissible_cert \<Longrightarrow> px.closure_check): {px.achievable} \<subseteq> px.cert_facts \<subseteq> cert_facts' *)
  lemma all_ops_super:   "{\<pi>. applicable \<pi>} \<subseteq> set cert_ops'"
    (* relax_applicables (:303): {applicable} \<subseteq> {px.applicable}; then px.all_ops_super *)
end
```
`achievable`/`applicable` here are **P⇩N's**; the `relax_*` theorems lift them to px's.
(`px.all_ops_super` is still sorried in Locale A — `Reachability_Certificate.thy:462` — so
`all_ops_super` inherits that gap; it is the ops-side analogue of `closure_sound`.)

**Step 3 — the dels gap (the one genuinely new obligation).** `effs_covered`
(`Grounded_PDDL.thy:198`, MCP-confirmed) requires every atom of `adds eff @ dels eff` of each
applicable op to be `covered`. `res_inst` over **P⇩N** keeps real deletes
(`relax_eff` drops them, `PDDL_Relaxation_Locales.thy:18`), but `px.cert_facts` holds only
add/initial atoms. So augment with the dels of the applicable ops, read off P⇩N's real schemas:
```isabelle
definition "extra_del_atoms \<equiv> concat (map (\<lambda>\<pi>. dels (effect (the (res_inst \<pi>)))) cert_ops')"
```
Sound because `wf_grounder` needs `facts \<supseteq> {achievable}` only (extra non-achievable del-atoms are
harmless), and these atoms are wf effect atoms of wf actions so `facts_wf` survives. (Add `remdups`
to keep `facts_dist`.)

**Step 4 — plug into the grounder at P⇩N:**
```isabelle
sublocale certified_reachability \<subseteq> wfg: wf_grounder P cert_facts' cert_ops'
```
(`P` = base problem of `normalized_problem_rx` = P⇩N.) Obligations:
`all_facts`/`all_ops` ← Step 2; `ops_wf` ← `rx_wf_classical_plan_action`
(`PDDL_Relaxation_Semantics.thy:42`) + px ops_wf; `effs_covered` adds-half ← cert coverage,
dels-half ← `extra_del_atoms`; `pres_covered`/`goal_covered`/`facts_wf`/`init_props`/`ops_no_num`
← P⇩N well-formedness + the `covered`/encoding lemmas. `valid_classical_plan_iff` then yields
**P⇩N \<leftrightarrow> (P⇩N)_G** — the correct problem.

### Building block #4 — rewire `Grounding_Pipeline.thy`

Discharge the `sorry` in `wf_grounder_args` (`Grounding_Pipeline.thy:289`, target
`wf_grounder P\<^sub>N all_facts all_pactions`) by **interpreting `certified_reachability` at
P⇩N = `normalize P`** with a concrete certificate `cert` produced by the untrusted engine
(`semi_naive_eval P\<^sub>R`, or a Nemo certificate). Steps: (a) check `px.admissible cert` executably;
(b) the interpretation yields `wf_grounder P\<^sub>N cert_facts' cert_ops'`; (c) replace the
`all_facts`/`all_pactions` abbreviations (`:288-289`) with `cert_facts'`/`cert_ops'`. The
unverified engine is now only the *producer*; admissibility is re-checked in the kernel.

---

## Proof-obligation ordering (risk-front-loaded) — OPTION 1

(Building blocks #0/#1 — `Datalog_Fixpoint`/`achievable_iff_lfp` — are **not** on the Option-1
path; `closure_sound` already gives the ⊇ anchor directly. They return only if exactness is
revived.)

1. **Step 1 sublocale** `normalized_problem_rx \<subseteq> px: pddl_datalog PX` — mechanical, from
   `relax_relaxes`. Unblocks everything by exposing `px.closure_sound` at PX.
2. **Step 2** `all_facts_super` via `relax_achievables` ∘ `px.closure_sound` — short. `all_ops_super`
   waits on Locale A's `px.all_ops_super` (`Reachability_Certificate.thy:462`, still sorry).
3. **Step 3** `extra_del_atoms` + the `effs_covered` dels-half — the one new lemma; the rest of the
   grounder obligations are P⇩N well-formedness already available in `wf_ast_classical_problem`.
4. **Step 4** the `wf_grounder P` sublocale (#3) + **Step 0** session wiring + pipeline rewire (#4)
   — pipeline sound and sorry-free on the reachability side.
5. Locale A's `all_ops_super` (ops ⊇) and the ordered `local_valid` exactness check remain the
   deeper residual work (the latter optional, per the dropped `admissible_exact`).

## Open / deferred

- Engine reuse: relate `all_derivs`/`update_facts` to `T_dl` only at the
  certificate boundary; keep the engine as a pure untrusted producer.
- `applicable`/ops side: the Nemo `ograph` stores no rule per node (the checker *searches*
  for a matching ground instance — `checkRuleMatch`). So `cert_ops` is reconstructed from
  the `local_valid` witnesses (the clause+args proving each non-initial node), bridged
  `plan_action \<leftrightarrow> ast_classical_plan_action` by `pa_of_classical`. This couples the ops
  superset to the `\<subseteq>`/exactness machinery; for the soundness-only v1 (closure check),
  `cert_ops` can instead be over-approximated directly from `all_derivs` over `cert_facts`.
- v1 can ship after step 4 (soundness only / closure check), deferring the ordered
  `local_valid` check and exactness.
