# WIP: Nemo certificate format & the CertifyingDatalog reference checker

Status: **reference notes** (2026-06-05). The reachability certificate our checker
re-validates is **produced by [Nemo](https://github.com/knowsys/nemo)** (`nmo`, the
existential-rule / Datalog engine) via its proof-trace output. The reference *verified*
checker for that output is **`~/work/CertifyingDatalog`** (Lean 4 + mathlib4). Our Isabelle
certificate datatype in `Reachability_Analysis/Reachability_Certificate.thy` should mirror
Nemo's output so the grounding pipeline can consume a real Nemo trace directly.

Companion docs: `WIP_reachability_datalog.md` (overall plan, rank-certificate decision),
`WIP_grounded_pddl_port.md`.

---

## How Nemo produces a certificate

`nmo` is run with proof tracing on a goal, and a Python post-processor converts the trace
into one of three JSON formats. From `CertifyingDatalog/Examples/*/inputCreatorNemo.py`:

```
nmo --trace-input-file traceGoal.txt --trace-output temp <ruleFile>
```

`traceGoal.txt` holds the goal atom(s) to explain; `temp` receives Nemo's trace; the script
then emits `*.tree.json`, `*.graph.json`, or `*.ograph.json` (+ the rule program). The rule
program itself is plain Datalog (`*.rls`), e.g. the transitive-closure toy example:

```
edge(a,b).  edge(b,c).  edge(c,d).
trans(?X,?Y) :- edge(?X,?Y).
trans(?X,?Z) :- trans(?X,?Y), trans(?Y,?Z).
```

## The three certificate formats

All three are parsed in `CertifyingDatalog/Parsing.lean`. Shared leaf types:

```
InputTerm  = constant String | variable String          -- {"constant":"a"} / {"variable":"X"}
InputAtom  = { symbol: String, terms: List InputTerm }   -- {"symbol":"trans","terms":[...]}
InputRule  = { head: InputAtom, body: List InputAtom }
```

### 1. `tree` — proof trees (redundant, can blow up exponentially)

```
InputTree A = node (label: A) (children: List (InputTree A))
TreeProblemInput = { trees: List (InputTree InputAtom), program: List InputRule }
```
Each fact gets a full derivation tree; shared sub-derivations are duplicated. Validated in
`TreeValidation.lean`.

### 2. `graph` — unordered DAG (predecessors as atoms)

```
InputEdge  = { vertex: InputAtom, predecessors: List InputAtom }
InputGraph = { edges: List InputEdge }
GraphProblemInput = { graph: InputGraph, program: List InputRule }
```
A DAG of derivations; each derived atom lists the body atoms that justify it. Validated in
`GraphValidation.lean` (needs a DFS / cycle check because order is not given).

### 3. `ograph` — **ordered DAG (predecessors as indices)** ← the one we mirror

```
InputOrderedGraphEdge = { label: InputAtom, predecessors: List Nat }
InputOrderedGraph     = { edges: Array InputOrderedGraphEdge }
OrderedGraphProblemInput = { graph: InputOrderedGraph, program: List InputRule }
```

Concrete `transitiveClosureToyExample.ograph.json` (abbreviated):

```json
{ "graph": { "edges": [
    { "label": {"symbol":"edge","terms":[{"constant":"a"},{"constant":"b"}]}, "predecessors": [] },
    { "label": {"symbol":"trans","terms":[{"constant":"a"},{"constant":"b"}]}, "predecessors": [0] },
    { "label": {"symbol":"edge","terms":[{"constant":"c"},{"constant":"d"}]}, "predecessors": [] },
    { "label": {"symbol":"trans","terms":[{"constant":"c"},{"constant":"d"}]}, "predecessors": [2] }
] }, "program": [ ... ] }
```

`predecessors` are **indices into earlier entries of the same array**. The Lean type bakes
the ordering invariant into the carrier (`OrderedGraphValidation.lean`):

```lean
abbrev OrderedProofGraph τ :=
  { arr : Array ((GroundAtom τ) × List ℕ) // ∀ i : Fin arr.size, ∀ j ∈ arr[i].snd, j < i }
```

**Why this is the format for us:** the array index *is* the derivation rank, and the
invariant `j < i` makes the support graph acyclic *by construction* — no cycle detection /
DFS at all. This is exactly the "rank/level certificate, not a DFS" decision recorded in
`WIP_reachability_datalog.md` (the graph library's `DFS_Cycles` is undirected-only and
unusable for a directed support graph).

## What the `ograph` checker checks (`locallyValid`)

For each index `i` (`OrderedGraphValidation.lean`):

```lean
locallyValid G kb i :=
  (G.arr[i].snd = [] ∧ kb.db.contains G.arr[i].fst)               -- an initial / DB fact
  ∨ (∃ r ∈ kb.prog, ∃ g : Grounding,
       g.applyRule' r = { head := G.arr[i].fst,                    -- a real ground rule instance
                          body := G.arr[i].snd.map (fun j => G.arr[j].fst) })
isValid G kb := ∀ i, locallyValid G kb i
```

i.e. every node is **either** a database fact with no predecessors, **or** the head of a
ground instance of some program rule whose body is exactly the labels sitting at the
predecessor indices. Executable checker: `checkValidity` walks the array
front-to-back (`checkValidityStep`, index 0 upward) and at each node calls
`checkRuleMatch` (unification against the program); proven equivalent to `isValid`
(`checkValidity_semantics`).

## Direction caveat (do not get this backwards)

`Datalog/Semantics.lean` defines two semantics and proves them equal
(`modelAndProofTreeSemanticsEquivalent`):

- `proofTheoreticSemantics kb` = atoms that *have a proof tree* (= `lfp T`, derivable set);
- `modelTheoreticSemantics kb` = `⋂ {models of kb}` (= `lfp T` too).

The `ograph` validity theorem
(`verticesValidOrderedProofGraphAreInProofTheoreticSemantics`) proves

```
G.isValid kb  ⟹  G.labels ⊆ kb.proofTheoreticSemantics
```

That is **`cert ⊆ lfp`**: every certified fact is genuinely derivable — the **soundness of
the engine's output / tightness (⊆)** direction.

But what the grounder (`wf_grounder` in `Grounded_PDDL`) needs is the **opposite**:
`{a. achievable a} ⊆ set (cert_facts)`, i.e. **`lfp ⊆ cert`** (the certificate
*over-approximates* the reachable facts; missing a reachable fact would make grounding drop
a reachable action — unsound). That comes from the **closure / model check**
(`ModelChecking.lean`): if `cert` is closed under all rules and contains the DB, then
`modelTheoreticSemantics = lfp ⊆ cert`.

So in our checker:

| check | gives | needed for |
|---|---|---|
| **closure check** (cert closed under one round of `all_derivs`, contains `init'`) | `lfp ⊆ cert` (**⊇** of reachable) | **pipeline soundness — essential** |
| **ordered `locallyValid`** (Nemo `ograph`) | `cert ⊆ lfp` (**⊆**) | exactness; retire `found_*` sorries — optional |

Build the closure check first (sound, sorry-free pipeline); the Nemo `ograph` structure is
the exactness upgrade on top.

## Mapping to our Isabelle types

- Nemo `InputAtom` (ground) ↔ our `fact = predicate × object list`, lifted to
  `facty = object atom formula` via `Atom (uncurry predAtm f)`.
- Nemo `program` (`InputRule` list) ↔ our PDDL action clauses
  (`ast_classical_problem.pred_clauses`, with `consequence_of`/`cl_pred_pre`/`cl_cond_pre`
  supplying head / positive body / guards). DB facts ↔ `init'`.
- Nemo `ograph` edge `{label, predecessors}` ↔

  ```isabelle
  datatype cert_node  = CNode (cn_fact: facty) (cn_preds: "nat list")
  datatype certificate = Cert (nodes: "cert_node list")
  ```

  with `cn_body c i = map (λj. cn_fact (nodes c ! j)) (cn_preds (nodes c ! i))`,
  `ordered_check = (∀ i<length (nodes c). ∀ j∈set (cn_preds (nodes c!i)). j<i)`, and
  `local_valid` the PDDL transcription of Nemo's `locallyValid`.
- `cert_ops` (applicable plan actions for `wf_grounder`) are read off the rule instance
  witnessing each non-initial node, bridged `plan_action ↔ ast_classical_plan_action` by
  `pa_of_classical`.

## Reference file index (`~/work/CertifyingDatalog`)

- `CertifyingDatalog/Parsing.lean` — all three JSON formats + parsing to typed problems.
- `CertifyingDatalog/OrderedGraphValidation.lean` — `OrderedProofGraph`, `locallyValid`,
  `checkValidity`, soundness theorem. **Closest match to our target.**
- `CertifyingDatalog/GraphValidation*.lean` — unordered DAG + DFS cycle check.
- `CertifyingDatalog/TreeValidation.lean` — proof-tree checker + `checkRuleMatch`.
- `CertifyingDatalog/ModelChecking.lean` — model/closure checking (the **⊇** direction).
- `CertifyingDatalog/Datalog/Semantics.lean` — proof-theoretic vs model-theoretic semantics,
  their equivalence, "is a model" lemmas.
- `CertifyingDatalog/Examples/*/` — runnable examples; `inputCreatorNemo.py` shows the exact
  `nmo` invocation and JSON emission; `*.ograph.json` are concrete certificates.
