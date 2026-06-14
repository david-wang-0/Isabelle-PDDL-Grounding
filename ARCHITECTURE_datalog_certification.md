# Architecture: certificate-based datalog / reachability checking

How the project certifies the result of an *untrusted* datalog engine (Nemo), and how that
splits into a **generic datalog layer** and a **PDDL-specific layer**. Last updated 2026-06-14.

> **2026-06-14 — Layer 1 reworked.** The generic checker (`Datalog_Certification`) moved from the
> Nemo *ordered-graph* form (predecessor indices) to an **index-free list of grounded rules** with
> an abstract well-foundedness obligation, and its checks / program / universe are now **set-based**,
> proven exact against the locale predicate `datalog_prog.derivable`. The PDDL kernel (Layer 2)
> still uses the ograph form, so the two certificate shapes currently **diverge** — reconciling
> them is open work (see the bridge note below and `Datalog/HANDOVER.md`).

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

(The **PDDL Layer 2** kernel still uses the older Nemo *ograph* variant: one node per fact carrying
predecessor *indices*, with an `ordered check` `j < i` standing in for the rank and a `local
validity` check folding rule-validity and exact-body together. The index order is a ready-made
derivation rank, so it needs no cycle detection; the index-free Layer 1 instead reconstructs that
rank with a topological-sort / DFS — see `Datalog/HANDOVER.md`.)

The asymmetry matters downstream: the *grounding pipeline's* soundness theorems only need the
closure (`⊇`) half — an over-approximation of the reachable facts is safe to ground against.
The ordered + local-validity (`⊆`) half buys exactness, i.e. the grounder output is not bloated
with unreachable facts/operators.

## Layer 1 — generic datalog certification (session `Datalog_Certification`, `Datalog/Datalog_Certificate.thy`)

A **standalone session** (`Datalog/ROOT`, parent `Tree_Decomp_Grounding_Common`, plus
`Stratified_Datalog`): datalog certification is meaningful and reusable without any planning
context. Self-contained and **PDDL-free**: imports only the AFP `Stratified_Datalog` clause syntax
(`('p,'x,'c) clause = Cls head-pred head-args rhs` with `PosLit` / `Eql` / `Neql` / `NegLit`
right-hand sides) and the `all_combos` enumeration utility from
`Tree_Decomp_Grounding_Common.Graph_Funs`.

- **Certificate**: `('p,'c) dl_certificate = DLCert (dl_rules: ('p,'c) dl_ground_rule list)`,
  rules `DLRule (gr_head: fact) (gr_body: fact list)` over ground facts
  `('p,'c) dl_fact = 'p × 'c list`; certified fact set `dl_cert_facts c` = the rule heads, and an
  empty body marks a base/EDB fact. The certificate is a concrete **list**.
- **Checks**: `dl_rule_valid`, `dl_closure_check`, `dl_founded` (an abstract `∃rank` well-founded
  support), bundled with `dl_positive_prog` into `dl_admissible`; entry point
  `dl_certified_model P U M cert` (admissible + `set M = set (dl_cert_facts cert)`). The program
  `P :: ('p,'x,'c) dl_program` and universe `U :: 'c set` are now **sets**, matching the reference
  semantics — so the checks are *not* `eval`-executable (∀σ/∃σ over substitutions); an executable
  list-based refinement, plus a cycle-detecting DFS discharging `dl_founded`, are deferred (see
  `Datalog/HANDOVER.md`).
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

## Layer 2 — PDDL reachability certification (`Reachability_Analysis/Reachability_Certificate.thy`)

The session `Reachability_Analysis` depends on `Datalog_Certification`; everything
PDDL-side — the certificate kernel, the PDDL→datalog serialization (`dl_rules`), the
executable check mirrors (`*_exec`), and the **bridge** to the generic checker — lives in
`Reachability_Certificate.thy`. The kernel is the planning-specific analogue of Layer 1,
phrased over the **native clause view of action schemas**
rather than serialized datalog: `as_action_clause` / `a_clauses` (an action schema read as a
clause: positive precondition atoms = body, equality conditions = guards, add effects = heads).
Locale `pddl_datalog = relaxed_problem` defines `closure_check` / `ordered_check` /
`local_valid` / `admissible` over the certificate type of `Reachability_Certificate.thy`
(`certificate = Cert (cert_node list)`, facts are `facty` formulas) and proves them
**directly against the PDDL execution semantics** — `achievable`, `plan_action_enabled`,
`valuation` — culminating in the image of `{f. achievable f}` under `fact_to_facty` being
contained in `set (cert_facts c)`, plus the `cert_ops` operator enumeration that feeds
`wf_grounder`.

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
list feeds Nemo's `dom` guards). `dl_program_of P` serializes the relaxed normalized problem;
the SML driver renders it as a Nemo program, runs Nemo, and parses the certificate back.
**Transport is untrusted**: the kernel re-checks the returned certificate against `a_clauses`,
which it recomputes from the problem itself — no proof ever mentions the serialization.

```text
                          (Layer 2: PDDL, verified)
 PDDL problem P ──P_T──▶ normalized ──relax──▶ P_R ──a_clauses──▶ admissible + grounding checks
        │                                       │                        ▲
        │                                       │ dl_program_of          │ certificate
        ▼                                       ▼ (transport, untrusted) │ (Nemo ograph)
   ground_via_cert ◀── wf_grounder ◀──┐   Nemo program ──▶ Nemo ─────────┘
                                      └── certified facts/ops

 (Layer 1: Datalog/Datalog_Certificate.thy — the same ograph checking idea for *arbitrary* positive
  datalog programs, proven against dl_derivable; independent of everything above)
```

## Separation rationale & future direction

Layer 1 exists so that datalog certification is meaningful (and reusable) without any planning
context: certify the model of *any* positive datalog program — hence its own session,
`Datalog_Certification`. Layer 2 predates it and carries the PDDL-semantics obligations the
pipeline actually needs. They share the *idea* (identical check structure, same Nemo format);
the unification lives in the bridge sections of
`Reachability_Analysis/Reachability_Certificate.thy`
(see [WIP_datalog_cert_bridge.md](WIP_datalog_cert_bridge.md)), at two levels:

1. **Check-level**: a fail-closed certificate conversion `cert_to_dl` plus the theorem that
   `dl_admissible` on the translated program (`dl_rules` = exactly the `dl_program_of`
   serialization) implies the PDDL `admissible_exec` — structural/ordered/positivity/closure
   parts proven, the local-validity transfer still sorried.
2. **Semantic-level** (section *PDDL reachability is the minimal model of the translated
   program*): under the translation well-formedness bundle `dl_bridge_wf`, the PDDL-achievable
   facts of the relaxed problem are **exactly the minimal datalog model**
   (`achievable_eq_minimal_model`: `{f. achievable f} = {f. dl_derivable (dl_rules P)
   const_names f}` — a PDDL `fact` and a generic ground datalog fact are the *same type*).
   Combined with the generic `dl_certified_model_correct` (certified facts = minimal model),
   this discharges the PDDL reachability requirements — the conclusions of `closure_sound`
   (facts ⊇) and `cert_ops_sound` (ops ⊇) — directly from a generic-checker acceptance,
   without per-check transfer. Both inclusions + the ops requirement are currently sorried.

End state: parse Nemo's ograph straight into a generic `dl_certificate`, run one exported
checker, and get the PDDL-side fact by theorem rather than by a second checker implementation.

Reference checker for the certificate format: the Lean 4 `CertifyingDatalog` development
(closure check = `⊇`, ordered locallyValid = `⊆`), see `WIP.md` history and
`Reachability_Analysis/Reachability_Certificate.thy` header.
