# `Datalog_Certification` session — handoff (2026-06-14)

## Status: GREEN

Both theory files are fully processed, consolidated, **0 sorry / 0 error / 0 warning** in jEdit:

| File | Role |
| --- | --- |
| `Datalog_Sema_Supplement.thy` | datalog semantics: defs, helper lemmas, the locale hierarchy, the inductive least-model `datalog_prog.derivable`, and the relation to the AFP stratified-datalog least solution |
| `Datalog_Certificate.thy` | certificate datatype, the checks, the exactness theorem, the AFP-semantics bridge locale, examples |

`ROOT` lists the two theories. `Positive_Datalog.thy` and `Datalog_Certificate_Locales.thy` were
**consolidated into the supplement** and no longer exist on disk — the lingering `#…#` / `.thy~`
files are stale emacs/jEdit buffers; ignore them.

## What changed this session (all green)

1. **Locale split** (supplement). `inductive derivable` used to live inside `datalog_universe`,
   whose `safe`/`covered` assumptions leaked into the exported `.induct`/`.derive` rules so the
   assumption-free checker could not use them. It now lives in an **assumption-free parent**
   `datalog_prog`; the side conditions sit in `datalog_universe` on top.
2. **Index-free certificate** (checker). Dropped the Nemo ordered-graph form (`DLNode` +
   predecessor indices, `dl_ordered_check`, `dl_local_valid`). A certificate is now a plain
   **list of grounded rules** `DLRule (gr_head) (gr_body)`; the checks are rule-validity + closure
   + **foundedness** (`dl_founded`, an abstract `∃rank` acyclicity witness — the cycle-detecting
   DFS that reconstructs the rank is deferred).
3. **Set-based checks**. `dl_rule_valid` / `dl_closure_check` / `dl_admissible` /
   `dl_certified_model` now take a **set** program `P :: ('p,'x,'c) dl_program` and a **set**
   universe `U :: 'c set`; the substitution condition is `∀x∈set (cls_vars cl). σ x ∈ U` (no more
   `cls_substs` enumeration). The **certificate stays a concrete list**.
4. **AFP-semantics bridge**. New locale `certified_positive_datalog_model` extends
   `positive_datalog_universe`; theorem `certified_model_is_least_solution` identifies the certified
   fact set with the AFP `Stratified_Datalog` least solution.

## Locale hierarchy (`Datalog_Sema_Supplement.thy`)

```text
datalog_sem            fixes U :: 'c set
  └ datalog_prog       = datalog_sem U + fixes P            -- ASSUMPTION-FREE; owns `inductive derivable`
      └ datalog_universe = datalog_prog U P + assumes dl_safe P, dl_heads_covered U P
positive_datalog       fixes P + assumes dl_positive_prog P  -- relation to stratified datalog (λ_. 0)
  positive_datalog_universe = datalog_universe U P + positive_datalog P
      -- derivable_in_solution, derivable_iff_least_solution
```

## Key results

+ `datalog_prog.derivable U P` — inductive bottom-up least-model semantics of a positive program
  over the universe set `U` (a fact is derivable iff it is the head of a ground clause instance,
  `σ` mapping the clause variables into `U`, whose guards hold and whose body atoms are derivable).
+ `dl_certified_model_correct` (`Datalog_Certificate.thy`):
  `dl_certified_model P U M c ⟹ set M = {f. datalog_prog.derivable U P f}`.
+ `certified_model_is_least_solution` (in `certified_positive_datalog_model`):
  `dl_certified_model P U M c ⟹ ρ ⊨⇩l⇩s⇩t P (λ_. 0) ⟹ set M = {(p, r). r ∈ ρ p}`.
+ `derivable_iff_least_solution` (in `positive_datalog_universe`): the bare `derivable` = the AFP
  rank-0 least solution, under positivity + safety + head-coverage.

## The two correctness directions

| Check | Enforces | Direction |
| --- | --- | --- |
| `dl_closure_check P U c` | every clause + `U`-valued `σ`: guards ∧ body ⊆ facts ⟹ head ∈ facts | facts form a model; no missing fact (`⊇` least model) |
| `dl_rule_valid P U r` (∀ rule) | each supplied rule is a genuine ground `P`/`U` instance | ties rules to the program |
| `dl_founded c` | `∃rank`: every fact has a rule with body ⊆ facts and strictly lower rank | well-founded support; no junk fact (`⊆` least model) |

`dl_admissible = dl_positive_prog P ∧ (∀ rule. dl_rule_valid) ∧ dl_closure_check ∧ dl_founded`.

## Gotchas (each cost real time — see also private memory `datalog-prog-locale-split`)

+ A locale-qualified induction rule used **outside** its locale, `datalog_prog.derivable.induct`,
  loses its auto `[consumes 1, case_names derive]` → supply them explicitly in the `induction rule:`.
+ `obtain rank` from the function-typed `∃rank` (in `dl_founded`) defeats `blast` / `..` / `metis`;
  use `define rank :: "(_, _) dl_rank"` + `by (rule someI_ex)`. The **wildcard** `(_, _) dl_rank`
  is required — a literal `('p,'c)` type annotation in a proof introduces *fresh* type vars that
  clash with the certificate's.
+ A `using f g by blast` that floods facts can **diverge** (it did, on the old σ′ retabulation);
  promote facts to `intro:` / `dest:` hints (`try0` confirms `blast` then runs in ~1 ms).

## Relating `dl_founded` to topological order and PDDL reachability

**Topological order (graph library).** `dl_founded c` is exactly "the support digraph — each fact
→ the body facts of *one* justifying rule — is acyclic", and the witnessing `rank` is a topological
numbering of that DAG. So the deferred `dl_acyclic_check` (next step #1) should **not** hand-roll a
DFS but *refine an existing topological-sort / acyclicity notion* — from the sibling
`Isabelle-Graph-Library` submodule, or the superproject's
`theories/graphs/Digraph_DFS_Cycles_Reachability*.thy`. A clean target shape is
`graph_topological_order (support_graph c) rank ⟹ dl_founded c`, so the executable check produces
the `∃rank` witness. **Caveat** (private memory `reachability-datalog-plan`): that DFS-cycles
development is **undirected-only**, whereas the support graph is **directed** — a directed
topological sort / SCC-freeness check is what is actually required, which is the very reason the
abstract `rank` certificate exists (to sidestep the missing directed-cycle machinery).

**PDDL reachability.** Certifying a *least model* matters because it is the datalog image of PDDL
**reachability**: under the relaxation bridge the achievable facts of the relaxed problem are
exactly the minimal model of the translated program (downstream `achievable_eq_minimal_model`,
modulo its sorries), so an accepted certificate yields the reachable-fact set *by theorem*. The
foundedness `rank` is the datalog analogue of **derivation depth** — the number of relaxed-plan
steps to first achieve a fact — and a topological order on the support graph is the order in which a
relaxed plan fires the rules. This is why the `⊆` (no-junk) direction needs well-foundedness: a
cyclically-supported fact would be one "justified" only by a circular argument with no grounding in
the initial facts — precisely an *unreachable* fact in PDDL terms.

## Pending / next steps

1. **Cycle-detecting DFS for `dl_founded`.** `dl_founded` is a non-executable `∃rank`. Add an
   executable `dl_acyclic_check :: dl_certificate ⇒ bool` that topologically sorts the support
   graph (or reports a cycle) and *constructs* the rank, with `dl_acyclic_check c ⟹ dl_founded c`.
   This is the obligation that the dropped predecessor indices used to discharge for free.
2. **Executable checker refinement.** The set-based checks are not `eval`-runnable (∀σ/∃σ over
   functions). A list-based instantiation (`set Pl` / `set Ul`) with executable substitution
   enumeration gives `dl_admissible_exec c ⟹ dl_admissible (set Pl) (set Ul) c` and restores the
   `eval` examples (currently only the certificate-local `ex_founded` + a foundedness negative
   probe survive; `ex_rules_valid` / `ex_closure` / `ex_certified` were removed).
3. **Downstream bridge re-point** (`Reachability_Analysis/Reachability_Certificate.thy`). It still
   references the **removed** list-based `dl_derivable` constant in its sorried bridge lemmas
   (`achievable_imp_dl_derivable`, `dl_derivable_imp_achievable`, `achievable_eq_minimal_model`)
   and carries its **own** ograph certificate format (`Cert (cert_node list)` with predecessor
   indices). Re-point those onto `datalog_prog.derivable U P` and reconcile the PDDL certificate
   format with the index-free generic one. (User will prompt for this.)

## Scope decision

The checker is kept **positive-only**. The PDDL relaxed reachability program is positive by
construction (delete-relaxation drops negatives → monotone), so positive is exactly what the
application needs. Stratified datalog would be an *additive* lift (negative bodies + per-stratum
iteration, positive = trivial stratification `λ_. 0`), enabled by the exactness the positive
checker already proves; not built. Reference if ever needed: the Lean `~/work/CertifyingDatalog`.
