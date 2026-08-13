# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Critical Rules

- **Do NOT build automatically.** Never run `isabelle build` / `make build` / any compile command while editing files or answering questions, unless the user explicitly asks for a build.
- **Verify via the `jedit-status` skill, not a batch build.** jEdit only processes the band around the caret + visible viewport, so `get_diagnostics` can report a *false* `0 errors` over an unprocessed tail. The skill forces tail-processing; do not declare a file clean until it reports `fully_processed: true` **and** `consolidated: true`. Fall back to a batch build only if the MCP server is down or the user asks for a clean/heap rebuild.
- **Not a submodule.** `git rev-parse --show-superproject-working-tree` is empty (the former superproject is gone). `origin` is `david-wang-0/Isabelle-PDDL-Grounding` and is already an SSH URL, so a plain `git push` goes over SSH.

## Project Overview

A partially-verified Isabelle/HOL implementation of the PDDL grounder from **Helmert 2009**. It takes a PDDL task, normalizes it, runs reachability analysis to find the achievable facts / applicable operators, grounds the task to a nullary purely-propositional task, and converts the result to STRIPS (the AFP `Verified_SAT_Based_AI_Planning` input format). Every stage is proven well-formedness- and plan-preserving on the classical pair-world-model PDDL semantics.

The PDDL semantics (input) come entirely from the sibling **Formal-PDDL-Semantics** repo (sessions `Classical_Planning`, `Continuous_Planning`) — which **supersedes** the older AFP `AI_Planning_Languages_Semantics` entry — and must be registered as Isabelle components. STRIPS output targets the AFP **Verified_SAT_Based_AI_Planning** entry. The **Isabelle-Graph-Library** (`Directed_Set_Graphs` and `Directed_Cycle_DFS`, needed only by `Datalog_Graph`) is supplied on the command line via `-d`. `Directed_Cycle_DFS` carries the directed-cycle detector and the linear whole-graph cycle sweep with its refinement chain, on the generic DFS skeleton in its parent session `DFS_Skeletons` — the graph-theoretic layer this repo used to keep in `Grounding_Common/Graph`, upstreamed in `mabdula/Isabelle-Graph-Library#16`; until that is merged the checkout must be on the `directed-cycle-dfs-refinements` branch.

> `HANDOVER.md` (repo root) is a short pick-up note for **incomplete work** — current open items + gotchas, not documentation. The `ROOT`/`ROOTS` files are authoritative for the current layout.

## Session Architecture

This is a multi-session AFP-style development laid out as **two mirrored trees** under the repo root, plus `ROOTS` and the docs. `ROOTS` lists every session directory; each has its own `ROOT`.

- **`Grounding_Common/`** — the **reusable**, Classical-free spine (usable by classical *and* a future temporal grounder).
- **`Classical_Grounding/`** — the **classical** grounder built on top of it.

Stage directories keep a plain name (e.g. `Type_Normalization/`), but the session/theories *inside* a classical stage dir carry the `Classical_` prefix; the reusable session in the mirrored dir under `Grounding_Common/` does not.

### Base spine (light Analysis-free AST base + light-datalog + SAT-free)

- **`Grounding_Light_Base`** (`= HOL +`) — `HOL-Library` + `Show`; the light root for the PDDL-free utility/datalog branch.
- **`Grounding_Base`** (`= Analysis_Free_Base +`) — the **Analysis-free PDDL-AST base** (FPS `Analysis_Free_Base` — the discrete, HOL-Analysis/ODE-free core of the PDDL semantics — plus `Analysis_Free_Base.Abstract_Syntax`, `Propositional_Proof_Systems`, `HOL-Library`/`Show`). Build once and load in jEdit as a prebuilt heap. The heavy euclidean/ODE tower is **not** here; only the classical base pulls it (via `Classical_Planning`). The whole reusable `Grounding_Common` spine sits on this, so it is Analysis-free and reusable by the temporal grounder.
- **`Grounding_Classical_Base`** (`= Grounding_Base +`, `sessions Classical_Planning`) — the classical layer; importing `Classical_Planning` is what pulls the continuous/ODE tower, making this (and everything above it) the heavy classical heap (`Classical_Planning` happening semantics + numeric checker for code export).
- **`Grounding_Temporal_Base`** (`= Grounding_Base +`, `sessions Temporal_Planning_Discrete`) — the temporal layer, loading only the **discrete** temporal semantics (`Temporal_Planning_Discrete`); Analysis-free (no ODE checker).
- **`Grounding_Base_STRIPS`** (`= Grounding_Classical_Base +`) — the AFP SAT planner (`Verified_SAT_Based_AI_Planning`); SAT lives **only** here.

### Reusable tree — `Grounding_Common/` (Classical-free)

| Session (dir) | Contents |
|---|---|
| `Grounding_Utils` (`Utils/`) | PDDL-free utilities: `Graph_Funs`, `Grounding_Utils`, `Nat_Show_Utils`, `String_Utils` |
| `Grounding_Common` (`Common/`) | AST-agnostic PDDL helpers: `Formula_Utils`, `DNF`, `PDDL_Normalization` (signature locales), `PDDL_Sema_Supplement` (reusable PDDL-semantics + signature supplements + wf-covariance) |
| `Datalog_Certification` (`Datalog/`), `Datalog_Graph` (`Datalog_Graph/`) | standalone PDDL-free positive-datalog certificate checker + sound forward-chaining evaluator (`Datalog_Evaluation.dl_eval`); the graph-lib (`Directed_Set_Graphs`, `Directed_Cycle_DFS`) is isolated to `Datalog_Graph` |
| `Grounding_<Stage>` (`<Stage>/`) | the AST-agnostic half of each pipeline stage (e.g. `Grounding_Type_Normalization`: `Type_Normalization`, `Type_Normalization_Proofs`) |

### Classical tree — `Classical_Grounding/`

| Session (dir) | Contents |
|---|---|
| `Classical_Grounding_Utils` (`Utils/`) | classical PDDL supplements: `Classical_PDDL_Sema_Supplement`, `PDDL_Checker_Utils` |
| `Grounding_Classical_Common` (`Common/`) | `Classical_PDDL_Normalization`, `Numeric_Free` |
| `Classical_<Stage>` (`<Stage>/`) | each stage's classical-AST half: `Classical_<Stage>_Locales`, `Classical_<Stage>`, `Classical_<Stage>_Semantics` |
| `Classical_Grounding` (top, `./ROOT`) | the pipelines (`Grounding_Pipeline_Numeric`/`_STRIPS`), `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS`, `Code_Setup`, `Planner_STRIPS_*`, `Running_Example` |

Pipeline stages, in order: **Type_Normalization** (detype → unary predicates) → **Goal_Normalization** → **Precondition_Normalization** (DNF-friendly, one disjunct → one action) → **Definedness_Normalization** → **Definedness_Translation** (numeric definedness → propositional predicates) → **PDDL_Relaxation** (delete-relaxation, monotone reachability) → **Reachability_Analysis** (the PDDL→datalog **certificate** kernel feeding the grounder) → **Grounded_PDDL** (the verified grounder core, `0 sorry`).

### Two recurring code patterns

1. **The ladder (reusable / classical columns per stage).** Each stage has a reusable column in `Grounding_<Stage>` (bare-named theories: signature/formula-level defs + proofs) and a classical column in `Classical_<Stage>` (`Classical_`-prefixed theories carrying the classical AST). A theory imports its predecessor *in its own column* plus its *common equivalent* across the columns. Classical stages still ship `Classical_X_Locales` (the abstract locale + sig constants/assumptions), `Classical_X` (the executable impl + proofs), and `Classical_X_Semantics` (plan-equivalence / well-formedness); stages compose via `sublocale` rewrites that fold one stage's signature constants onto the next.
2. **Certified reachability, not trusted reachability.** The reachability oracle (the generic `Datalog_Evaluation.dl_eval`, or an external solver) is *untrusted*; correctness flows through a datalog certificate that the verified checker validates, with PDDL reachability related to the certificate's minimal model purely semantically (`certified_facts_eq_achievable`). The grounder is targeted at the real-deletes problem `P_N` (via the relaxation bridge), **not** the relaxed over-approximation `P_R` — grounding the over-approximation directly would be unsound. See `ARCHITECTURE_datalog_certification.md`.

## Building (when explicitly asked)

There is **no Makefile** here. The FPS sibling (`Continuous_Planning`/`Classical_Planning`) and the AFP entries must be registered as Isabelle components first; the **Isabelle-Graph-Library** is supplied on the command line. Then a session builds with:

```bash
isabelle build -d <Isabelle-Graph-Library> -d . <Session>   # e.g. Classical_Grounding for the whole pipeline
```

`Grounding_Base` is the expensive heap (heavy `Continuous_Planning` theories); build it once, keep it warm, and develop the `Grounding_Common`-and-above sessions on top (jEdit is usually launched with `-l Grounding_Classical_Common` so the stages/pipeline process live). Per the Critical Rules, prefer `jedit-status` over rebuilding.

## Proof Development (MCP server)

Always develop in Isabelle/jEdit. The Isabelle/Q MCP server (`mcp__isabelle__*`) drives interactive proof work and keeps PIDE in sync with your edits. Use the dedicated skills rather than ad-hoc tool calls:

- **`isabelle-authenticate`** — once per session, before any other `mcp__isabelle__*` call (placeholder token; a `PreToolUse` hook injects the real `$IQ_AUTH_TOKEN`).
- **`isabelle-search`** — for locating any definition / lemma / locale / constant. Use it on the *first* attempt; never start with `grep`/`find`.
- **`isabelle-prove`** — writing/editing/stepping proofs (sorry-driven top-down structuring, REPL stepping, sledgehammer).
- **`try0-minimize`** — when a method fails or you're unsure which to use; **`isabelle-stuck-method`** when a method diverges (never returns).
- **`isabelle-refactor`** — structural moves (split/merge theories, move locales/lemmas, rewire ROOT/imports).

### Editing conventions

- When a `.thy` is **open in jEdit**, mutate it through `mcp__isabelle__write_file` (edits the buffer + reprocesses). Do **not** mix disk `Edit`/`Write` with `write_file` on the same open file — the buffer flush clobbers disk-only edits. `Edit`/`Write` are fine for ROOT/ROOTS, new files before first open, and bulk syntactic renames (then `open_file` to refresh).
- Write Isabelle symbols as **ASCII escapes** (`\<subseteq>`, `\<Rightarrow>`, `\<open>`, `\<close>`), never raw Unicode glyphs.

In specs and locale assumptions prefer bounded `\<forall>x \<in> set xs. P x` over `list_all` (keep `list_all` only on executable/`[code]` paths). Use `(in -)` only inside an open `context`/`locale` block, never at theory top level. See `GUIDANCE.md` for the underlying philosophy (surgical Isar, `sorry`-then-fill, hoist complex subgoals into named lemmas).

Statement/proof shape:

- **Never mix premises between `assumes` and the conclusion.** Write `assumes P and Q shows R`, never `assumes P shows "Q \<Longrightarrow> R"` — every premise goes in `assumes`, the conclusion stays bare. (Fix dependent `[OF \<dots>]` arity, e.g. `assms` \<rightarrow> `assms(1,2)`, if you flatten one out.)
- **In `have` steps use `if`/`for`, not a `\<forall>`/`\<longrightarrow>` (or bounded `\<forall>x \<in> S`) you immediately strip.** Write `have "Q x" if "P x" for x` / `have "P x" if "x \<in> S" for x`, not `have "\<forall>x. P x \<longrightarrow> Q x"` peeled with `proof (rule allI, rule impI)` (or `rule ballI`). This is for `have` (intermediate goals); the bounded-`\<forall>` preference above is for `shows`/spec/locale assumptions, where the quantifier genuinely *is* the statement.
