# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Critical Rules

- **Do NOT build automatically.** Never run `isabelle build` / `make build` / any compile command while editing files or answering questions, unless the user explicitly asks for a build.
- **Verify via the `jedit-status` skill, not a batch build.** jEdit only processes the band around the caret + visible viewport, so `get_diagnostics` can report a *false* `0 errors` over an unprocessed tail. The skill forces tail-processing; do not declare a file clean until it reports `fully_processed: true` **and** `consolidated: true`. Fall back to a batch build only if the MCP server is down or the user asks for a clean/heap rebuild.
- **This is a Git submodule.** `git rev-parse --show-superproject-working-tree` is non-empty. Push with the `push-ssh` skill (explicit SSH URL override); never `git remote set-url` on `origin` — that drifts from the superproject's `.gitmodules`. `origin` is `david-wang-0/Isabelle-PDDL-Grounding`.

## Project Overview

A partially-verified Isabelle/HOL implementation of the PDDL grounder from **Helmert 2009**. It takes a PDDL task, normalizes it, runs reachability analysis to find the achievable facts / applicable operators, grounds the task to a nullary purely-propositional task, and converts the result to STRIPS (the AFP `Verified_SAT_Based_AI_Planning` input format). Every stage is proven well-formedness- and plan-preserving on the classical pair-world-model PDDL semantics.

Built on two AFP entries: **AI_Planning_Languages_Semantics** (PDDL input) and **Verified_SAT_Based_AI_Planning** (STRIPS output). The PDDL/Continuous semantics actually used come from the sibling **Formal-PDDL-Semantics** submodule (sessions `Classical_Planning`, `Continuous_Planning`), registered as Isabelle components by the superproject's `make register-components`.

> `HANDOVER.md` (repo root) is the full repository summary + handover: per-session contents, the exact sorry inventory, gotchas, and the ordered next-steps list. `README.md` was refreshed to the current layout (2026-06-12); the ROOT files remain authoritative.

## Session Architecture

This is a multi-session AFP-style development. `ROOTS` lists every sub-session directory; each has its own `ROOT`. The dependency spine is a **two-layer frozen/editable split**:

- **`Tree_Decomp_Grounding_Base`** (`Tree_Decomp_Grounding_Base/ROOT`, `= HOL +`) — external/library dependencies only (AFP PDDL Classical/Continuous semantics, the STRIPS theories, `Propositional_Proof_Systems`, `HOL-Library`, `Show`). No project-local theories. Build it once and load it in jEdit as a **stable prebuilt heap**; it is then frozen — you cannot add imports (e.g. `iq.iq`) to anything in it at runtime.
- **`Tree_Decomp_Grounding_Common`** (`Common/ROOT`, `= Tree_Decomp_Grounding_Base +`) — the **editable** shared layer: formula/graph/string/show utilities, PDDL/STRIPS semantic supplements, DNF, and `Normalization_Definitions` / `Numeric_Free`. Everything else builds on top of this.

On top of `Common`, each pipeline stage is its **own session** (`= Tree_Decomp_Grounding_Common +`):

| Session | Role |
|---|---|
| `Datalog_Certification` (`Datalog/`) | standalone, PDDL-free positive-datalog certificate checker (proven against its least-model semantics `dl_derivable`) plus a generic, executable, sound forward-chaining evaluator (`Datalog_Evaluation.dl_eval`) |
| `Type_Normalization` | detype — encode type membership as unary predicates |
| `Goal_Normalization` | rewrite the goal (runs before definedness, no definedness invariant) |
| `Precondition_Normalization` | DNF-friendly preconditions, one disjunct → one action |
| `Definedness_Normalization` | conjoin reflexive numeric equalities so every DNF disjunct carries the full atom set |
| `Definedness_Translation` | translate numeric definedness into propositional predicates |
| `PDDL_Relaxation` | delete-relaxation (drop negative effects) so reachability is monotone |
| `Reachability_Analysis` | PDDL datalog-**certificate** kernel: shared PDDL→datalog infra (`Reachability_Analysis.thy`) + the `PDDL_Reachability_{Locales,Analysis,Certificate}.thy` development (reachability = minimal model of the translated program; `certified_pddl` grounding-input locale) that feeds the grounder. The untrusted forward-chaining oracle is now the generic `Datalog_Evaluation` |
| `Grounded_PDDL` | the verified grounder core (fully proven, `0 sorry`) |

The top session **`Tree_Decomp_Grounding`** (`./ROOT`, `= Tree_Decomp_Grounding_Common +`) pulls in all the stage sessions and wires them together via the top-level theories: `Grounding_Pipeline_Numeric` (with-numerics path, green), `Grounding_Pipeline_STRIPS` (numeric-free path to STRIPS), `PDDL_to_STRIPS/Classical_PDDL_to_STRIPS`, and `Running_Example` (end-to-end demo).

### Two recurring code patterns

1. **Three-file per stage.** Each normalization stage ships `X_Locales.thy` (the abstract locale + sig constants and assumptions), `X.thy` (the executable implementation), and `X_Semantics.thy` (the plan-equivalence / well-formedness proofs). Stages compose via `sublocale` with rewrites that fold one stage's signature constants onto the next.
2. **Certified reachability, not trusted reachability.** The reachability oracle (the generic `Datalog_Evaluation.dl_eval`, or an external solver) is *untrusted*; correctness flows through a datalog certificate that the verified checker validates, with PDDL reachability related to the certificate's minimal model purely semantically (`certified_facts_eq_achievable`). The grounder is targeted at the real-deletes problem `P_N` (via the relaxation bridge), **not** the relaxed over-approximation `P_R` — grounding the over-approximation directly would be unsound. See `ARCHITECTURE_datalog_certification.md`.

## Building (when explicitly asked)

There is **no Makefile in this submodule** — builds run through `isabelle build` or, more usually, the superproject's `make`. The external dependency sessions (AFP entries, `Formal-PDDL-Semantics`) must be registered as components first (superproject `make register-components`). Then a given session builds with:

```bash
isabelle build -d . <Session>      # e.g. Grounded_PDDL, or Tree_Decomp_Grounding for the whole pipeline
```

`Tree_Decomp_Grounding_Base` is the expensive heap (heavy `Continuous_Planning` theories); build it once, keep it as a warm heap, and develop the `Common`-and-above sessions on top. Per the Critical Rules, prefer `jedit-status` over rebuilding.

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
- `iq.iq` is a **development-only** import (pulls in `Isar_Explore`, needed for `explore` / `get_proof_context` live goal state). It must never land in a commit. Keep it on its own import line; the per-repo strip hook lives in the *Formal-PDDL-Semantics* submodule, **not here**, so in this repo remove it by hand before committing.

In specs and locale assumptions prefer bounded `\<forall>x \<in> set xs. P x` over `list_all` (keep `list_all` only on executable/`[code]` paths). Use `(in -)` only inside an open `context`/`locale` block, never at theory top level. See `GUIDANCE.md` for the underlying philosophy (surgical Isar, `sorry`-then-fill, hoist complex subgoals into named lemmas).

Statement/proof shape:

- **Never mix premises between `assumes` and the conclusion.** Write `assumes P and Q shows R`, never `assumes P shows "Q \<Longrightarrow> R"` — every premise goes in `assumes`, the conclusion stays bare. (Fix dependent `[OF \<dots>]` arity, e.g. `assms` \<rightarrow> `assms(1,2)`, if you flatten one out.)
- **In `have` steps use `if`/`for`, not a `\<forall>`/`\<longrightarrow>` (or bounded `\<forall>x \<in> S`) you immediately strip.** Write `have "Q x" if "P x" for x` / `have "P x" if "x \<in> S" for x`, not `have "\<forall>x. P x \<longrightarrow> Q x"` peeled with `proof (rule allI, rule impI)` (or `rule ballI`). This is for `have` (intermediate goals); the bounded-`\<forall>` preference above is for `shows`/spec/locale assumptions, where the quantifier genuinely *is* the statement.
