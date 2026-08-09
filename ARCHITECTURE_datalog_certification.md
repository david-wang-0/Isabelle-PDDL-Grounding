# Architecture: certificate-based datalog / reachability checking

How the project certifies the result of an *untrusted* datalog engine (Nemo), and how that
splits into a **generic datalog layer** and a **PDDL-specific layer**. Last updated 2026-06-18.

> **2026-06-14 — Layer 1 reworked; 2026-06-17 — Layer 2 unified; 2026-06-18 — kernel made
> executable.** The generic checker (`Datalog_Certification`) moved from the Nemo *ordered-graph*
> form (predecessor indices) to an **index-free list of grounded rules** with an abstract
> well-foundedness obligation, and its checks / program / universe are now **set-based**, proven
> exact against `datalog_prog.derivable`. Layer 2's own ograph certificate datatype was **removed**;
> both layers now share the *single* generic `(M, dc)` certificate, related purely semantically
> (`certified_facts_eq_achievable`). The set-based checks were given an executable refinement
> (`Datalog/Datalog_Certificate_Code.thy`: `dl_certified_model_exec`, `dl_founded` via an ordered-cert
> linear scan), so the whole kernel is now code-generable. The stronger **Path-2 foundedness story**
> (rank from a verified graph topological order) is **DONE** in session `Datalog_Graph` — `acyclic
> (dl_dep_graph c) ⟹ dl_founded c`, wired into `dl_admissible` via `dl_admissible_via_acyclic`.
>
> **2026-07-21 — the executable acyclicity check is DONE too, and `0 sorry`.** A verified
> cycle-detecting DFS now decides `acyclic (dl_dep_graph c)` executably and discharges
> `dl_founded`: `dl_acyclic_dfs` (`Datalog_Cycle_DFS`, graph library), since rebased onto the linear
> whole-graph sweep `DFS_DirCycle_Linear` (`O(V+E)`). Together with the ordered scan `dl_founded_exec` this
> gives **two selectable, byte-identical foundedness re-checks** — surfaced in the SML binary as
> `ground [--dfs|--topo]`. Only an order-*producing* witness (a DFS that emits the topological
> numbering itself, rather than a bool) remains, and it is optional.

## The certification idea

We never verify the reachability engine. Instead the engine emits a **certificate** — a set of
derived facts together with the ground rule instances that justify them — and a small verified
kernel re-checks the certificate against the program/problem itself. Acceptance gives an *exact*
characterization of the engine's fact set. The **generic Layer 1** kernel (as of 2026-06-14) uses
these three checks:

| Check | What it enforces | Direction |
| --- | --- | --- |
| **rule validity** | each supplied ground rule is a genuine ground instance of some program clause (over the universe set `U`) whose guards hold | ties the rules back to the program |
| **closure check** | for every clause and every `U`-valued substitution: body inside the certified facts + guards hold ⟹ head inside | no extra fact is derivable; the certified facts form a model (`⊇` least model) |
| **foundedness** | a rank assigns every fact a strictly larger value than the body facts of one justifying rule | the support graph is acyclic, so every fact is genuinely derivable (`⊆` least model) |

(Since the 2026-06-14 rewrite the **PDDL Layer 2** no longer has its own checker at all — the old
Nemo *ograph* variant with predecessor indices / `ordered_check` / `local_valid` was removed. Layer 2
relates PDDL reachability to Layer 1's generic checker *semantically* (the minimal-model identity
`achievable_eq_minimal_model`), so it inherits Layer 1's checks rather than duplicating them. The
index-free Layer 1's foundedness rank can be supplied either by the cert's rule order
(`dl_founded_exec`, an executable linear scan) or, **Path-2 (DONE, session `Datalog_Graph`)**,
reconstructed *inside* the kernel from a verified graph topological order — `acyclic (dl_dep_graph c)
⟹ dl_founded c`.)

The asymmetry matters downstream: the *grounding pipeline's* soundness theorems only need the
closure (`⊇`) half — an over-approximation of the reachable facts is safe to ground against.
The ordered + local-validity (`⊆`) half buys exactness, i.e. the grounder output is not bloated
with unreachable facts/operators.

## Layer 1 — generic datalog certification (session `Datalog_Certification`, `Datalog/Datalog_Certificate.thy`)

A **standalone session** (`Grounding_Common/Datalog/ROOT`, parent `Grounding_Utils`, plus
`Stratified_Datalog`): datalog certification is meaningful and reusable without any planning
context. Self-contained and **PDDL-free**: imports only the AFP `Stratified_Datalog` clause syntax
(`('p,'x,'c) clause = Cls head-pred head-args rhs` with `PosLit` / `Eql` / `Neql` / `NegLit`
right-hand sides) and the `all_combos` enumeration utility from
`Grounding_Utils.Graph_Funs`.

- **Certificate**: `('p,'c) dl_certificate = DLCert (dl_rules: ('p,'c) dl_ground_rule list)`,
  rules `DLRule (gr_head: fact) (gr_body: fact list)` over ground facts
  `('p,'c) dl_fact = 'p × 'c list`; certified fact set `dl_cert_facts c` = the rule heads, and an
  empty body marks a base/EDB fact. The certificate is a concrete **list**.
- **Checks**: `dl_rule_valid`, `dl_closure_check`, `dl_founded` (an abstract `∃rank` well-founded
  support), bundled with `dl_positive_prog` into `dl_admissible`; entry point
  `dl_certified_model P U M cert` (admissible + `set M = set (dl_cert_facts cert)`). The program
  `P :: ('p,'x,'c) dl_program` and universe `U :: 'c set` are now **sets**, matching the reference
  semantics — so the *abstract* checks are not `eval`-executable (∀σ/∃σ over substitutions). The
  executable **list-based refinement** is `Datalog/Datalog_Certificate_Code.thy` (`dl_admissible_exec`
  / `dl_certified_model_exec` over `set Pl` / `set Ul`, with `dl_founded_exec` an ordered-cert linear
  scan, all `[code]` and proven sound, 0 sorry). Constructing the `dl_founded` rank *inside* the
  kernel from support-graph acyclicity (rather than trusting the cert's order) is **Path-2 (DONE,
  session `Datalog_Graph`)**: `acyclic (dl_dep_graph c) ⟹ dl_founded c` + `dl_admissible_via_acyclic`.
  Deciding that acyclicity executably is **also DONE (`0 sorry`)**: `dl_acyclic_dfs` (the linear
  whole-graph directed-cycle DFS sweep, `O(V+E)`), with `dl_acyclic_dfs_imp_dl_founded` giving
  `dl_admissible_dfs` / `dl_certified_model_dfs` beside the `_exec`
  variants. Only an order-*producing* DFS witness remains (optional).
- **Reference semantics**: `datalog_prog.derivable U P f` — an inductive bottom-up least-model
  semantics of a positive program, owned by the **assumption-free** locale `datalog_prog`, with
  substitutions mapping clause variables into the universe set `U`.
- **Correctness** (0 sorry): `dl_certified_model_correct`:
  `dl_certified_model P U M c ⟹ set M = {f. datalog_prog.derivable U P f}`.
- **AFP least-solution bridge** (0 sorry): the locale `certified_positive_datalog_model`
  (extends `positive_datalog_universe`) proves `certified_model_is_least_solution` — under
  positivity + safety + head-coverage, `set M` equals the AFP `Stratified_Datalog` least solution
  `ρ ⊨⇩l⇩s⇩t P (λ_. 0)`. (Supersedes the earlier "nothing needs this bridge today" note — it now
  exists, via the supplement's `derivable_iff_least_solution`.)
- **Restrictions, fail-closed**: programs containing `NegLit` are rejected
  (`dl_positive_prog`) — with negation the consequence operator is not monotone and the
  certificate argument does not apply. `Eql`/`Neql` are supported as guards.

## Layer 2 — PDDL reachability certification (`Reachability_Analysis/PDDL_Reachability_*.thy`)

The session `Reachability_Analysis` depends on `Datalog_Certification`. The PDDL side was
**rewritten 2026-06-14** (de-Nemo) and **split 2026-06-17** into three files:

- `Reachability_Analysis.thy` — shared PDDL→datalog infrastructure only: the native clause view
  of action schemas (`as_action_clause` / `a_clauses`: positive precondition atoms = body,
  equality conditions = guards, add effects = heads), `consequence_of`, the fact-store helpers,
  and the per-problem `init'`. (The retired untrusted `semi_naive` engine that used to live here
  was deleted; its generic replacement is `Datalog/Datalog_Evaluation.thy`.)
- `PDDL_Reachability_Locales.thy` — the locale hierarchy (`pddl_datalog = relaxed_problem`,
  `num_free_relaxed_problem`, `certified_pddl`), the PDDL→datalog serialization (`dl_rules`), and
  the translation well-formedness bundle (`dl_bridge_wf`).
- `PDDL_Reachability_Analysis.thy` / `PDDL_Reachability_Certificate.thy` — the proofs.

The kernel no longer has its own PDDL certificate datatype or PDDL-direct `closure_check` /
`cert_facts` / `cert_ops` (all **removed** in the 2026-06-14 rewrite). Instead the relation to the
**generic** `dl_certificate` of Layer 1 is established **purely semantically**: the serialized
program `dl_rules P` is a positive datalog program, and `PDDL_Reachability_Analysis` proves

> `achievable_eq_minimal_model`: `{f. achievable f} = {f. datalog_prog.derivable (set const_names) (set (dl_rules P)) f}`

— PDDL reachability of the (relaxed, normalized) problem is *exactly* the minimal model of the
translated program (both inclusions, against the PDDL execution semantics `achievable` /
`plan_action_enabled` / `valuation`). Composed with Layer 1's `dl_certified_model_correct`
(certified facts = minimal model), `PDDL_Reachability_Certificate` gets the capstone

> `certified_facts_eq_achievable`: `dl_certified_model (set (dl_rules P)) (set const_names) M dc ⟹ set M = {f. achievable f}`

and the `certified_pddl` locale (fix an accepted `M`/`dc`) exposes the reachable-fact set as the
hypothesis-free fact `certified_facts_eq_reachable` for the grounder. No PDDL-specific check is
transferred any more; trust flows through the single generic checker.

Key PDDL-specific twists that the generic layer does not have:

- the checker runs on the **delete-relaxed** normalized problem `P_R = relax_prob P_T`
  (relaxation makes the consequence operator monotone / the program positive by construction),
  while the grounder targets the real-deletes problem `P_N` via the relaxation bridge —
  grounding the over-approximation directly would be unsound;
- bodyless clauses are folded into the initial facts (`pseudo_init`/`init'`), so an init node
  in the PDDL certificate is "no predecessors + fact ∈ `init'`";
- on top of `admissible` there are *grounding* checks (`grounding_checks_exec`): certified
  facts/operators must be well-formed, cover goal/preconditions/effects, and be numeric-free.

## Transport (`Grounding_Pipeline_STRIPS_Executable.thy` + `SMLCodebase/`)

The oracle input is the wire-format datatype `dl_program = DLProgram clause-list const-universe`
(AFP clause syntax, list-based for code export and deterministic serialization; the constant
list feeds the oracle's `dom` guards). `dl_program_of P` serializes the relaxed normalized
problem; the (untrusted) oracle — either the generic verified evaluator `Datalog_Evaluation.dl_eval`
or an external solver such as Nemo — produces a candidate minimal model + certificate.
**Transport is untrusted**: the returned certificate is re-checked by the **generic** Layer 1
checker `dl_certified_model (set (dl_rules P)) (set const_names) M dc`, and `certified_facts_eq_achievable`
turns that acceptance into `set M = {f. achievable f}` — no proof ever mentions the serialization
or the oracle.

```text
                          (Layer 2: PDDL, verified)
 PDDL problem P ──P_T──▶ normalized ──relax──▶ P_R ──dl_rules──▶ generic checker (Layer 1)
        │                                       │                        ▲
        │                                       │ dl_program_of          │ certificate + model M
        ▼                                       ▼ (transport, untrusted) │
   ground_via_cert ◀── wf_grounder ◀──┐   datalog program ──▶ oracle ────┘
        (set M = {f. achievable f}  ──┘   (dl_eval / Nemo)
         via certified_facts_eq_achievable)

 (Layer 1: Datalog/Datalog_Certificate.thy — the generic certificate checker for *arbitrary*
  positive datalog programs, proven against dl_derivable; Datalog_Evaluation.thy is the generic
  forward-chaining evaluator. Both independent of everything above.)
```

## Separation rationale & future direction

Layer 1 exists so that datalog certification is meaningful (and reusable) without any planning
context: certify the model of *any* positive datalog program — hence its own session,
`Datalog_Certification`. Layer 2 carries the PDDL-semantics obligations the pipeline actually
needs. As of the 2026-06-14 rewrite the two are unified at a **single, purely semantic level**
(the earlier fail-closed check-level bridge `cert_to_dl` + per-check transfer lemmas was
**excised** — the index-free generic checker made it obsolete). The bridge lives in
`Reachability_Analysis/PDDL_Reachability_{Analysis,Certificate}.thy`:

- under the translation well-formedness bundle `dl_bridge_wf` (discharged in
  `num_free_relaxed_problem`), the PDDL-achievable facts of the relaxed problem are **exactly the
  minimal datalog model** — `achievable_eq_minimal_model`:
  `{f. achievable f} = {f. datalog_prog.derivable (set const_names) (set (dl_rules P)) f}`
  (a PDDL `fact` and a generic ground datalog fact are the *same type*; **both inclusions proven**,
  0 sorry);
- combined with the generic `dl_certified_model_correct` (certified facts = minimal model), this
  discharges the PDDL reachability requirement directly from a generic-checker acceptance, with no
  per-check transfer: `certified_facts_eq_achievable`, and the `certified_pddl` locale's
  hypothesis-free `certified_facts_eq_reachable` that the grounder consumes.

End state: the untrusted oracle is the generic `Datalog_Evaluation.dl_eval` (or an external solver
such as Nemo), and the PDDL-side fact comes out by theorem — one exported generic checker, no
second PDDL-specific checker implementation.

Reference checker for the certificate format: the Lean 4 `CertifyingDatalog` development
(closure check = `⊇`, ordered locallyValid = `⊆`); see the
`Datalog/Datalog_Certificate.thy` / `PDDL_Reachability_Locales.thy` headers.
