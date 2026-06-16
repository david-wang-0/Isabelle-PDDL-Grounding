# WIP — `dl_derivable_imp_achievable` (tightness / ⊇ direction)

Session handover, 2026-06-16. Goal: discharge the **last sorry** in
`Reachability_Analysis/Reachability_Certificate.thy` — the `step` case of
`dl_derivable_imp_achievable` (every derivable datalog fact is PDDL-achievable). See
`HANDOVER.md` §"Remaining sorry" for the original framing. This file tracks the
infrastructure being built and the exact next steps.

## Current build state

⚠️ **The file has exactly ONE error right now** (plus the pre-existing `sorry` warning and the
2 harmless duplicate-rewrite NOTEs). Everything else added this session is **green**.

- **The one error**: `achievables_reach_common`, the `Nil` case. It currently reads

  ```isabelle
  case Nil
  have "valid_classical_plan_alt I [] I" by simp
  thus ?case by auto
  ```

  `auto` eagerly splits the pair witness `M` into `(a, b)` and cannot reassemble `I`. **Fix
  (verified-by-reasoning, was about to be applied when the session was interrupted):** replace
  the `Nil` branch with explicit existential witnesses:

  ```isabelle
  case Nil
  show ?case by (rule exI[of _ "[]"], rule exI[of _ I], simp)
  ```

  Apply that one edit and `achievables_reach_common` should go green.

## Key design decision (read first)

The abstract `relaxed_problem` locale (which `pddl_datalog` extends) assumes **only positive
preconditions**, NOT empty deletes and NOT numeric-freeness. The ⊇ direction genuinely needs
both (delete-relaxation for fact *persistence* when concatenating per-fact plans; no numeric
effects so `snd` is invariant and num-free/positive preconditions are monotone in `fst`).

Rather than narrow the locale (which would break the `normalized_problem_rx ⊆ px: pddl_datalog`
sublocale in the deliberately-broken downstream `Certified_Grounding_Locales.thy`, and would
make the *soundness* ⊆ direction no longer unconditional), these are threaded as **two explicit
hypotheses** on the reverse-direction lemmas:

- `nne: "\<forall>a \<in> set (actions D). numeric_effects (ac_eff a) = []"` (no numeric effects)
- `nd:  "\<forall>a \<in> set (actions D). dels (ac_eff a) = []"` (delete relaxation)

Both hold for the pipeline's actual relaxed problem `relax_prob (P\<^sub>T P)` (`P\<^sub>T` is
def-translated ⟹ numeric-free; `relax_eff` ⟹ empty deletes — note `relax_eff` *keeps*
`numeric_effects`, so `nne` needs `P\<^sub>T`'s numeric-freeness, discharged separately).
NB: I deliberately did **not** use `num_free_prob` — that constant is **not imported** into this
theory (it silently parsed as a free variable and wasted a cycle); `nne` is the exact minimal
fact actually used, so it sidesteps the missing import.

**Consequence for the capstone:** once the step case is closed,
`achievable_eq_minimal_model` and `certified_facts_eq_achievable` must gain `nne` and `nd`
(they use both inclusions). The ⊆ soundness path
(`achievable_imp_dl_derivable` / `derivable_invariant` / `minimal_model_facts_requirement`)
stays **unconditional**.

## Infrastructure already landed this session (all green except the Nil case above)

In `context pddl_datalog`, between `derivable_invariant`/`achievable_imp_dl_derivable` and
`dl_derivable_imp_achievable`:

1. `execute_facts_eq [nd, en]` — `fst (execute_plan_action a M) = fst M \<union> set (adds (effect ((the \<circ> res_inst) a)))`
   (resolved action has empty deletes). `execute_grows` is the `\<subseteq>` corollary.
2. `plan_grows_facts [nd]` — `valid_classical_plan_alt M \<pi>s N \<Longrightarrow> fst M \<subseteq> fst N`.
3. `un_and_map_semantics_rev` — reverse of the existing `un_and_map_semantics`
   (`(\<forall>f\<in>set (un_and F). A \<Turnstile>\<^sub>m f) \<Longrightarrow> A \<Turnstile>\<^sub>m F`).
4. `valuation_pos_conj_mono [is_pos_conj F, fst M1 \<subseteq> fst M2, v1]` — a positive-conjunction
   precondition instance true at `M1` is true at any fact-superset `M2` (predicate atoms persist;
   equality/cond literals are model-independent via `cond_lit_model_indep`).
   ⚠️ A buffer/disk desync earlier corrupted this lemma's *name* to `valuation_poslimsconj_mono`;
   it is now correct — watch for it if you see "undefined fact".
5. `enabled_mono [nne, en@M1, fst M1 \<subseteq> fst M2]` — `plan_action_enabled a M2`. Numeric side
   conditions discharged by `numeric_effects_non_intrf_no_numeric_effects` /
   `enumerate_rhs_pnes_no_numeric_effects` (both keyed on `numeric_effects (effect a') = []`);
   precondition by `valuation_pos_conj_mono`; `is_pos_conj` of the precondition from `relaxed_prob`.
6. `plan_replay_mono [nne, nd, valid M1 \<pi>s N1, fst M1 \<subseteq> fst M2]` —
   `\<exists>N2. valid M2 \<pi>s N2 \<and> fst N1 \<subseteq> fst N2`. Induction on `\<pi>s` using `enabled_mono` +
   `execute_facts_eq`.
7. `achievables_reach_common [nne, nd, \<forall>f\<in>set fs. achievable f]` —
   `\<exists>\<pi>s M. valid_classical_plan_alt I \<pi>s M \<and> (\<forall>f\<in>set fs. Atom (uncurry predAtm f) \<in> fst M)`.
   Induction on `fs`; each per-fact plan is `plan_replay_mono`'d from the growing common state
   (`fst I \<subseteq> fst M` via `plan_grows_facts`), concatenated by
   `valid_classical_plan_alt_append_intro`. **(needs the Nil-case fix above.)**

## `dl_bridge_wf` refactor (done this session, green — per user request)

The definition was restructured with **named per-clause sub-predicates** and given
**intro/elim/dest rules using the `\<And>` (big-and) meta-binder** instead of HOL `\<forall>`/ball:

- New named predicates: `dl_pre_translates`, `dl_adds_predAtoms`, `dl_cond_translates`,
  `dl_clause_vars_params` (each a `definition` over an `action_clause`); `dl_bridge_wf` is now a
  conjunction of these over `a_clauses` plus the init/const conditions.
- Rules (element-level, so consumers never re-derive the nested quantifiers):
  `dl_bridge_wfI [intro]`, `dl_bridge_wfE [elim]`, and dest rules `dl_bridge_wf_pred_preD`,
  `dl_bridge_wf_posD`, `dl_bridge_wf_condD`, `dl_bridge_wf_varsD`, `dl_bridge_wf_initD`,
  `dl_bridge_wf_const_namesD` (all `[dest]`).
- `derivable_step_adds` was rewired: its old `wf[unfolded dl_bridge_wf_def] \<dots> by blast`
  extraction is now four `dl_bridge_wf_*D[OF wf cl_ac_mem]` uses (with `unfolding clparams[symmetric]`
  to swap `cl_params cl_ac` \<leftrightarrow> `ps`).
- `derivable_init` assumes `dl_bridge_wf P` but **does not use it** (unchanged).

Open question raised by the user (not yet actioned): *should `~/.claude/isabelle.md` instruct
always adding intro/dest/elim rules?* Recommendation: yes but **scoped** — for conjunctive/bundled
predicates (well-formedness bundles, locale-assumption bundles) consumed as hypotheses or proved
as goals in more than one place, define named sub-predicates + `\<And>`-binder intro/elim/dest
rules reaching element level; **not** for simple/one-off/`[code]` defs. Would need
`sync-ai-instructions` to mirror into the Gemini copy.

## Remaining plan for the step case (not yet started)

Rule induction on `datalog_prog.derivable` (`induct[consumes 1, case_names step]`). In `step`:
`cl \<in> set (dl_rules P)`, `\<sigma>` with vars in `const_names`, guards hold, body atoms
`subst_atom \<sigma> a` derivable **and (IH) achievable**. Show `achievable (subst_atom \<sigma> (the_lh cl))`.
`cl \<in> set (dl_rules P)` splits (`dl_rules_def`) into:

- **(A) action clause**: `cl \<in> set (dl_clauses_of_action_clause cl_ac)`, `cl_ac \<in> set a_clauses`.
- **(B) fact clause**: `cl \<in> set (List.map_filter dl_fact_clause init')`.

Lemmas still to prove (all in `context pddl_datalog`, carrying `nne`/`nd` where needed):

1. **`clause_body_enabled`** (reverse of `enabled_clause_body`, needs `nne`): given
   `sch \<in> set (actions D)`, `ac_name sch = n`,
   `action_params_match (head sch) args`, the positive-precondition instances
   `\<subseteq> fst M`, and `satisfies_conds (cl_params (as_action_clause sch)) (cl_cond_pre \<dots>) args`,
   conclude `plan_action_enabled (SimplePlanAction n args) M`. Rebuild `valuation M \<Turnstile>\<^sub>m precondition a'`
   from `pos_part` + `cond_part` via `un_and_map_semantics_rev` (mirror `enabled_clause_body`
   *backwards*); discharge the two numeric conditions from `nne`; `wf_classical_plan_action` via
   `wf_classical_plan_action_cond` + `action_params_match`.
   - **Typing of `args`**: in a *typeless* (normalized) problem every param type is `\<omega>` and every
     object is of type `\<omega>`, so `action_params_match` reduces to `length args = length params \<and>
     set args \<subseteq> set const_names`. Need a small lemma `n \<in> set const_names \<Longrightarrow> is_obj_of_type n \<omega>`
     (reverse of the existing `is_obj_of_type_const_name`).

2. **`fire_clause_achievable`** (unifying lemma, needs `nne`, `nd`, `dl_bridge_wf P`): given
   `cl_ac \<in> set a_clauses`, well-typed `args`, every positive-precondition instance achievable,
   and `satisfies_conds \<dots> args`, conclude every `f0 \<in> set (consequence_of cl_ac args)` is
   achievable. Proof: `achievables_reach_common` over the precondition instances → common state
   `M*`; `clause_body_enabled` → enabled at `M*`; fire one step;
   `res_inst_adds_eq_consequence` puts `f0` in the adds ⟹ `achievable`.

3. **`init'_achievable`**: `Atom (predAtm p args) \<in> set init' \<Longrightarrow> achievable (p, args)`.
   `init' = conc_unique pseudo_init (init P)`, so `set init' = set pseudo_init \<union> set (init P)`.
   `init P` facts ⟹ `init_achievable` (existing). `pseudo_init` facts are adds of
   **empty-`cl_pred_pre`** action clauses at condition-satisfying args (`pseudo_init` =
   `concat (map all_fact_consqs fact_clauses)`, `fact_clauses` = `a_clauses` with empty
   `cl_pred_pre`) ⟹ a special case of `fire_clause_achievable` (vacuous body).

4. **Discharge the `step` case**: case (A) → `fire_clause_achievable` on the resolved schema with
   `args = map (\<lambda>(v,_). if v \<in> set (cls_vars cl) then \<sigma> v else c0) ps` (witness
   `c0 = hd const_names` from `dl_bridge_wf_const_namesD` for non-clause params; clause-var args are
   `\<sigma> v \<in> const_names` from the `step` `cls_vars` hypothesis). Head/body atoms only mention
   clause vars, so `subst_atom \<sigma>` agrees with `ac_tsubst ps args`. Guards ⟹ `satisfies_conds`
   (reverse of `dl_cond_rh_eval_guard`); body atoms achievable from IH via `body_atom_from_pre`.
   Case (B) → `init'_achievable`. Reuse the kept helpers `subst_id_dl_id_term`,
   `ac_arg_in_const_names`, `ac_tsubst_var_in_args`, `guard_from_cond`, `body_atom_from_pre`,
   `dl_clause_of_pos_mem`.

5. **Clean up**: add `nne`/`nd` to `achievable_eq_minimal_model` and
   `certified_facts_eq_achievable`; update the section text and the `HANDOVER.md` sorry inventory.
   After everything is green, do the planned `isabelle-refactor` theory split
   (`PDDL_Reachability_Analysis` / `PDDL_Reachability_Certificate`).

## Style cleanup owed on `Reachability_Certificate.thy`

The whole `Reachability_Analysis/Reachability_Certificate.thy` file predates (and does not yet
follow) the proof-style rules in `~/.claude/isabelle.md`, and should be brought into line as a
dedicated pass (ideally once the step case is green, so the cleanup moves only finished text).
Things to fix throughout:

- **Chaining**: replace `then have`/`with R have` with `hence`/`thus`, threading extra named facts
  via `using` (e.g. the many `from \<dots> have`/`with \<dots> have` steps in `derivable_init`,
  `derivable_step_adds`, `derivable_invariant`).
- **One `using` per rule/fact group** when several rule-applied facts feed one step.
- **`have` steps**: use `if`/`for` instead of stating a bounded `\<forall>x\<in>S`/`\<forall>`/`\<longrightarrow>`
  and immediately peeling it with `ballI`/`allI`/`impI` (several intermediate `have "\<forall>\<dots>"`
  blocks here do this; note the new infra I added mostly already uses `if`/`for`, but
  `condwf`/`varsub`/`posprop`/`np` in `derivable_step_adds` and the bounded-`\<forall>` `have`s in the
  older lemmas should be revisited).
- Keep bounded `\<forall>x\<in>set xs` only where it genuinely *is* a `shows`/spec statement, not a
  `have` intermediate.
- No `(in -)` at theory top level; no mixed `assumes`/`shows`.

This is a mechanical-but-careful pass (re-verify with `jedit-status` after) and is independent of
finishing the proof.

## Workflow gotchas hit this session

- **Do not mix disk `Edit`/`Write` with `mcp__isabelle__write_file` on the open buffer** (exactly
  what `~/.claude/isabelle.md` warns). Disk edits + `open_file` did **not** reliably reload the
  jEdit buffer here, and a desync silently corrupted a lemma name. Use `mcp__isabelle__write_file`
  (`str_replace` / `line` / `insert`) for **all** edits to the open file; it writes the buffer
  *and* disk (a follow-up `save_file` reports nothing to save). Verify via `get_diagnostics`
  (`wait_until_processed: true`).
- The I/R REPL backend would not start (`repl_connect` even with explicit
  `ir_home=~/bin/AutoCorrode2025-2/ir`), so proofs were developed straight into the file +
  `get_diagnostics`, not via the REPL scratchpad.
