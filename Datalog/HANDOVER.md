# `Datalog_Certification` session — handoff (2026-06-14, updated 2026-06-18)

## Status: GREEN

All theory files are fully processed, consolidated, **0 sorry / 0 error / 0 warning** in jEdit:

| File | Role |
| --- | --- |
| `Datalog_Sema_Supplement.thy` | datalog semantics: defs, helper lemmas, the locale hierarchy, the inductive least-model `datalog_prog.derivable`, and the relation to the AFP stratified-datalog least solution |
| `Datalog_Certificate.thy` | certificate datatype, the (set-based) checks, the exactness theorem, the AFP-semantics bridge locale, examples |
| `Datalog_Certificate_Code.thy` | **(2026-06-18)** executable refinement: `dl_founded_scan`/`dl_founded_exec` (+ `dl_founded_exec_imp_dl_founded`, rank = list index), `dl_{positive_prog,rule_valid,closure_check,admissible,certified_model}_exec` (all `[code]`), the `cls_substs_tabulate` + `*_cong` bridges, and the soundness chain to `dl_certified_model_exec_correct`. 0 sorry |
| `Datalog_Evaluation.thy` | generic, PDDL-free, verified forward-chaining evaluator `dl_eval` (total + `[code]` + `dl_eval_sound`) — the untrusted oracle that produces a candidate model for the checker to validate |

`ROOT` lists all four theories. `Positive_Datalog.thy` and `Datalog_Certificate_Locales.thy` were
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
numbering of that DAG. **This is now planned in `../PLAN_datalog_graph.md`** (repo-root): convert the
support relation to the `Isabelle-Graph-Library` `'a dgraph` (`dl_dep_graph`), prove the
graph-theoretic `finite E ⟹ (∄p. cycle E p) ⟷ has_top_num E` (the **directed** library `cycle`,
**not** `cycle'`), and derive `has_top_num (dl_dep_graph c) ⟹ dl_founded c`. The target shape is
exactly `graph_topological_order (support_graph c) rank ⟹ dl_founded c`. **Resolved caveat** (private
memory `reachability-datalog-plan`): the `DFS_Cycles` development is **undirected-only**, but the plan
uses the directed `cycle`/`awalk` notions from `Awalk.thy` (via `reachable1_awalk`) plus a
self-contained `acyclic ⟺ topological order` proof, sidestepping that gap. The interim
`dl_founded_exec` (ordered-cert linear scan, **shipped** in `Datalog_Certificate_Code.thy`) already
discharges `dl_founded` by trusting the cert's emit order; the graph path removes that trust.

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

1. **Graph topological order for `dl_founded`** (the stronger, no-trusted-order path). `dl_founded`
   is a `∃rank` acyclicity witness. The interim `dl_founded_exec` (ordered-cert linear scan, **DONE**
   in `Datalog_Certificate_Code.thy`) discharges it by trusting the cert's emit order. The next step
   *constructs* the rank inside the kernel from a verified graph topological order /
   cycle-check, with `acyclic (dl_dep_graph c) ⟹ dl_founded c`. **Planned in
   `../PLAN_datalog_graph.md`** (two theories: `Graph_Topological_Order`, `Datalog_To_Graph`).
2. ~~**Executable checker refinement.**~~ **DONE (2026-06-18)** — `Datalog_Certificate_Code.thy`:
   `dl_admissible_exec` / `dl_certified_model_exec` over `set Pl` / `set Ul` with executable
   substitution enumeration (`cls_substs`) and the `cls_substs_tabulate` soundness bridge, all
   `[code]`, 0 sorry; `dl_certified_model_exec_correct` is the capstone. The whole pipeline now
   exports to SML through it.
3. ~~**Downstream bridge re-point.**~~ **DONE (2026-06-14/17)** — `Reachability_Analysis` was
   rewritten (de-Nemo): the list-based `dl_derivable` and the PDDL-side ograph certificate datatype
   were removed; the bridge lemmas (`achievable_imp_dl_derivable`, `dl_derivable_imp_achievable`,
   `achievable_eq_minimal_model`) are re-pointed onto `datalog_prog.derivable U P` and **proven**
   (0 sorry), and the former `Reachability_Certificate.thy` was split into
   `PDDL_Reachability_{Locales,Analysis,Certificate}.thy`.

## Scope decision

The checker is kept **positive-only**. The PDDL relaxed reachability program is positive by
construction (delete-relaxation drops negatives → monotone), so positive is exactly what the
application needs. Stratified datalog would be an *additive* lift (negative bodies + per-stratum
iteration, positive = trivial stratification `λ_. 0`), enabled by the exactness the positive
checker already proves; not built. Reference if ever needed: the Lean `~/work/CertifyingDatalog`.
