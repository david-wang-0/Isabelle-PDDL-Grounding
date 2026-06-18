# Plan — datalog `dl_founded` via a graph topological order (Path 2 foundation)

Goal: discharge the abstract foundedness obligation `dl_founded`
(`Datalog/Datalog_Certificate.thy:92`) **graph-theoretically**, by converting a datalog
certificate to the graph library's directed-graph format and showing that a topological
order of that graph yields the required rank. Plus the purely graph-theoretic fact that a
graph is acyclic **iff** it has a topological order. This is the verified-kernel half of the
"Path 2 — verified cycle-detecting DFS" future work (the DFS itself, which *finds* the order
/ detects a cycle, comes later and plugs into the acyclic side of the equivalence).

Two theories to **draft** (definitions + theorem statements + proof sketches; `sorry` the
hard steps initially, fill top-down):

1. **`Datalog_To_Graph`** — the datalog↔graph bridge (conversion + `topological order ⟹ rank`).
2. **`Graph_Topological_Order`** — purely graph-theoretic: `acyclic ⟺ ∃ topological order`.

`Datalog_To_Graph` imports `Graph_Topological_Order`, so the second is the lower layer.

---

## 0. The two endpoints (already in the tree)

**Datalog side** (`Datalog/Datalog_Certificate.thy`, `Datalog/Datalog_Sema_Supplement.thy`):

```isabelle
type_synonym ('p,'c) dl_fact = "'p × 'c list"
datatype ('p,'c) dl_ground_rule = DLRule (gr_head: "('p,'c) dl_fact") (gr_body: "('p,'c) dl_fact list")
datatype ('p,'c) dl_certificate = DLCert (dl_rules: "('p,'c) dl_ground_rule list")
definition "dl_cert_facts c = remdups (map gr_head (dl_rules c))"
type_synonym ('p,'c) dl_rank = "('p,'c) dl_fact ⇒ nat"

definition dl_founded :: "('p,'c) dl_certificate ⇒ bool" where
  "dl_founded c ≡ (∃rank::('p,'c) dl_rank. ∀f ∈ set (dl_cert_facts c).
      ∃r ∈ set (dl_rules c). gr_head r = f
         ∧ set (gr_body r) ⊆ set (dl_cert_facts c)
         ∧ (∀b ∈ set (gr_body r). rank b < rank f))"
```

`dl_founded` already feeds `dl_founded_imp_derivable` → `dl_certified_model_correct`, so anything
that establishes `dl_founded` plugs straight into the existing trust chain.

**Graph side** (`Isabelle-Graph-Library`, session `Directed_Set_Graphs`):

```isabelle
type_synonym 'a dgraph = "('a × 'a) set"          (* Pair_Graph.thy: edge (u,v) means u → v *)
definition "dVs G = ⋃ {{v1,v2} | v1 v2. (v1,v2) ∈ G}" (* vertices *)
(* Awalk_Defs.thy *)
definition awalk  :: "'a dgraph ⇒ 'a ⇒ ('a×'a) list ⇒ 'a ⇒ bool"   (* arc-walk u --p--> v *)
definition cycle  :: "'a dgraph ⇒ 'a awalk ⇒ bool" where
  "cycle E p = (∃u. awalk E u p u ∧ distinct (tl (awalk_verts u p)) ∧ p ≠ [])"
(* cycle' = cycle ∧ length p > 2 — for UNDIRECTED use; NOT what we want (per user) *)
(* Awalk.thy:349 *) lemma reachable1_awalk: "u →⁺⇘E⇘ v ⟷ (∃p. awalk E u p v ∧ p ≠ [])"   (* shape *)
```

Use **`cycle`** (genuine directed cycle, includes self-loops / 2-cycles), **never `cycle'`**.
"No cycles" ≡ `¬ (∃p. cycle E p)`.

---

## 1. Theory `Graph_Topological_Order` (purely graph-theoretic)

Self-contained, parametric in `E :: 'a dgraph`. Bridges the library `cycle` to HOL `acyclic`
(`acyclic E = (∀x. (x,x) ∉ E⁺)`), then proves the equivalence with a topological numbering.

### Definitions

```isabelle
definition top_num :: "'a dgraph ⇒ ('a ⇒ nat) ⇒ bool" where
  "top_num E τ ≡ ∀(u,v) ∈ E. τ u < τ v"
definition has_top_num :: "'a dgraph ⇒ bool" where
  "has_top_num E ≡ ∃τ. top_num E τ"
```

(A topological *numbering* — strictly-increasing rank along every edge — is the form we need
for `dl_founded`'s `rank`. Equivalent to a topological *ordering* for finite graphs.)

### Lemmas (in dependency order)

1. `top_num_imp_acyclic`: `top_num E τ ⟹ acyclic E`.
   *Proof:* `(u,v) ∈ E⁺ ⟹ τ u < τ v` by `trancl_induct`; then `(x,x) ∈ E⁺` is impossible. **Easy.**

2. `no_cycle_iff_acyclic`: `(∄p. cycle E p) ⟷ acyclic E`.
   *Proof:* via `reachable1_awalk` + `cycle`/`closed_w` ↔ "some vertex on a positive-length
   closed walk" ↔ `(v,v) ∈ E⁺`. Forward: a `cycle` gives `awalk E u p u`, `p ≠ []` ⟹ `u →⁺ u`.
   Reverse: `(v,v) ∈ E⁺` ⟹ a closed walk ⟹ shrink to an apath-based cycle (library
   `closed_w` / `awalk_to_apath` machinery). **Medium — may `sorry` the closed-walk→cycle
   normalisation first; check Awalk.thy for `closed_w`/`cycle` lemmas to reuse.**

3. `finite_acyclic_imp_has_top_num`: `finite E ⟹ acyclic E ⟹ has_top_num E`.
   *Witness:* `τ x = card {u. (u,x) ∈ E⁺}` (number of strict predecessors).
   *Proof:* for `(u,v) ∈ E`: `{w. w →⁺ u} ⊆ {w. w →⁺ v}` (trans), `u ∈ {w. w →⁺ v}`
   (since `(u,v) ∈ E ⊆ E⁺`) but `u ∉ {w. w →⁺ u}` (acyclic), and both sets `⊆ dVs E`
   (finite). Hence `card (preds u) < card (preds v)`, i.e. `τ u < τ v`. **Provable, self-contained.**
   (Need `finite {u. (u,x) ∈ E⁺}`: `⊆ dVs E`, finite by `finite_vertices_iff`.)

4. **Main:** `acyclic_iff_has_top_num`:
   `assumes "finite E" shows "(∄p. cycle E p) ⟷ has_top_num E"`
   *Proof:* `(∄p. cycle) =(2)= acyclic`; `acyclic ⟹ has_top_num` by (3); `has_top_num ⟹ acyclic`
   by (1). Combine.

---

## 2. Theory `Datalog_To_Graph` (the bridge)

Imports `Graph_Topological_Order` and `Datalog_Certification.Datalog_Certificate`.

### Conversion (the "abstract conversion from datalog to the graph format")

```isabelle
definition dl_dep_graph :: "('p,'c) dl_certificate ⇒ ('p,'c) dl_fact dgraph" where
  "dl_dep_graph c ≡
     {(b, f) | r b f. r ∈ set (dl_rules c) ∧ gr_head r = f ∧ b ∈ set (gr_body r)}"
```

Edge `b → f` ("body fact `b` must precede head fact `f`"). With a topological numbering `τ`
(strictly increasing along edges) every body fact ranks below its head — exactly `dl_founded`.

Auxiliary:

```isabelle
definition dl_body_closed :: "('p,'c) dl_certificate ⇒ bool" where
  "dl_body_closed c ≡ ∀r ∈ set (dl_rules c). set (gr_body r) ⊆ set (dl_cert_facts c)"
```

`dl_body_closed` holds for any cert whose rule bodies are themselves derived facts (true of the
Nemo / `naive_cert` certs, where each body fact is an earlier head). It lets every fact reuse
*any* of its rules in the `dl_founded` witness. **Decide:** assume it here, or derive it from the
existing `dl_closure_check` / cert-validity (investigate — `dl_closure_check` is about the
*program* closure, not body⊆facts; likely keep `dl_body_closed` as an explicit hypothesis and
discharge it executably alongside the other cert checks).

### Lemmas

1. `finite_dl_dep_graph`: `finite (dl_dep_graph c)`.
   *Proof:* image of the finite `set (dl_rules c) × ...`; bound by
   `dl_dep_graph c ⊆ set (concat (map (λr. map (λb. (b, gr_head r)) (gr_body r)) (dl_rules c)))`.
   **Easy.**

2. `dl_dep_graph_edge`: `(b,f) ∈ dl_dep_graph c ⟷ (∃r ∈ set (dl_rules c). gr_head r = f ∧ b ∈ set (gr_body r))`.
   (unfolding helper.)

3. **Main:** `top_num_imp_dl_founded`:
   `assumes "dl_body_closed c" and "has_top_num (dl_dep_graph c)" shows "dl_founded c"`
   *Proof:* obtain `τ` with `top_num (dl_dep_graph c) τ`; use `rank := τ`. Fix
   `f ∈ set (dl_cert_facts c)`. Then `f ∈ set (map gr_head (dl_rules c))`, so `∃r ∈ set (dl_rules c).
   gr_head r = f`. By `dl_body_closed`, `set (gr_body r) ⊆ set (dl_cert_facts c)`. For
   `b ∈ set (gr_body r)`: `(b,f) ∈ dl_dep_graph c` (by (2)), so `τ b < τ f`. Discharge `dl_founded`.
   **Easy given the pieces.**

4. **Capstone:** `acyclic_dep_graph_imp_dl_founded`:
   `assumes "dl_body_closed c" and "∄p. cycle (dl_dep_graph c) p" shows "dl_founded c"`
   *Proof:* `finite (dl_dep_graph c)` by (1); `acyclic_iff_has_top_num` ⟹ `has_top_num`; then (3).

5. *(optional, ties to trust chain)* `acyclic_dep_graph_imp_derivable`:
   chain (4) with `dl_founded_imp_derivable` (needs the `dl_rule_valid` hyp already in scope for
   the checker). Shows: **dependency graph acyclic + valid rules ⟹ every cert fact derivable.**

So the eventual executable story (Path 2 proper): an SML/verified DFS checks
`∄p. cycle (dl_dep_graph c) p`; (4)+(5) turn that into `dl_founded` / derivability **by theorem**,
removing the need for the cert to carry a *trusted* topological order (the current
`dl_founded_exec` linear-scan path trusts the Nemo emit order).

---

## 3. Session / folder structure

**Decision:** new folder **`Datalog_Graph/`** with its own session (keeps the AFP `Graph_Theory`
dependency out of the standalone `Datalog_Certification` session).

```
session Datalog_Graph = Datalog_Certification +
  sessions
    Directed_Set_Graphs
    Graph_Theory
  theories
    Graph_Topological_Order
    Datalog_To_Graph
```

- **Parent heap = `Datalog_Certification`** (already in the project chain; gives `dl_certificate`).
- Import the graph side at **theory** granularity — `imports Directed_Set_Graphs.Awalk` pulls only
  `Awalk ← Vwalk ← Pair_Graph ← Graph_Theory.Rtrancl_On` (+ the Awalk adaptor), **not** the heavy
  `Pair_Graph_Imperative` / Separation-Logic / Automatic_Refinement theories in that session. So the
  merge cost is moderate (AFP `Graph_Theory`), not the full imperative stack.
- `Directed_Set_Graphs` heap already built; `Graph_Theory` is a registered AFP session.
- Register: add `Datalog_Graph` to the top `ROOTS`, then `isabelle components -u .`.

`Graph_Topological_Order` itself only needs `Awalk` (+ HOL `acyclic`/`trancl`), no datalog — could
later move to its own `= Directed_Set_Graphs +` session if we want it reusable/standalone, but
co-locating both in `Datalog_Graph` is simpler for the draft.

---

## 4. Verification approach

- `Graph_Topological_Order` is single-heap (graph only) — cheapest to verify; **do it first** (its
  acyclic/topo-numbering proofs are the substantive ones).
- `Datalog_To_Graph` needs the merged heap. jEdit: launch with `-l Datalog_Certification` (or
  `-l Tree_Decomp_Grounding_Common` and let the Datalog + light graph theories process live) after
  ROOT registration + restart. The current jEdit (`Tree_Decomp_Grounding_Base`) does **not** see the
  graph library, so a restart on the right heap is required.
- Draft with `sorry` top-down; the only genuinely non-trivial proof is
  `no_cycle_iff_acyclic` (reverse direction: closed walk → normalised cycle) — reuse Awalk.thy's
  `closed_w` / `awalk_to_apath` lemmas; `sorry` it first, then fill.

## 5. Risk / open questions

- **`no_cycle_iff_acyclic`** reverse direction — depends on what cycle/closed-walk lemmas Awalk.thy
  already provides (`reachable1_awalk` is the key handle; `closed_w_rotate` etc. exist). Main risk.
- **`dl_body_closed` provenance** — assume vs. derive from cert checks; tentatively an explicit,
  executably-checkable hypothesis (mirrors how `dl_founded` already demands body⊆facts per rule).
- **Heap merge weight** — theory-level import should keep it moderate; confirm by a one-off build of
  `Datalog_Graph` before relying on jEdit.
- **Naming** — `Datalog_To_Graph` / `Graph_Topological_Order` provisional.

## 6. Deliverables of the draft

- `Datalog_Graph/ROOT`, entry in top `ROOTS`.
- `Datalog_Graph/Graph_Topological_Order.thy` — defs + 4 lemmas (aim: 0–1 `sorry`).
- `Datalog_Graph/Datalog_To_Graph.thy` — conversion + 5 lemmas (aim: 0 `sorry`, modulo the above).
- Fold this plan into `HANDOVER.md` once the theories land; delete `PLAN_datalog_graph.md`.
