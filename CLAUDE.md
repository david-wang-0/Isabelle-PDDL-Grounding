# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Critical Rules

- **Do NOT build the project automatically**: Never run build or compile commands (such as `make build`, `make compile-sml-mlton`, `make compile-sml-poly`, or `isabelle build`) when performing operations, editing files, or answering questions, unless the user has explicitly requested a build or compilation.

- **ALWAYS check theory status via the `jedit-status` skill**: To verify a theory file builds / is error-free / is fully processed, you MUST invoke the `jedit-status` skill rather than calling `mcp__isabelle__get_diagnostics` / `get_processing_status` / `get_command_info` ad hoc. The skill enforces forcing tail-processing (jEdit only checks the *visible* viewport, so a buffer can sit "unprocessed" — and report a false `0 errors` — until its tail is forced). Do not declare a file clean until `fully_processed: true` **and** `consolidated: true`.


## Project Overview

A **verified PDDL planner** built in Isabelle/HOL with SML code export. The project combines formal verification of AI planning algorithms with code generation for practical execution. It's organized in three main layers:

1. **Isabelle/HOL theories** — formal proofs of planning algorithms, SAT-based solving, and PDDL grounding
2. **Submodule libraries** — reusable verified components (graph algorithms, PDDL semantics, datalog)
3. **SML compilation** — exported and compiled code for the PDDL parser and validator

## Development Workflows

### Local Development (Interactive)

Requires **Isabelle 2025-2** (`~/bin/Isabelle2025-2`), **AFP 2025-2** (`~/bin/afp-2025-2`), **MLton** or **Poly/ML**.

```bash
make init              # One-time: fetch submodules + register components
make jedit             # Open in Isabelle/jEdit (uses your personal settings)
make build             # Batch-build the session
make compile-sml-mlton # Compile PDDL parser with MLton
make compile-sml-poly  # Compile PDDL parser with Poly/ML
```

**Configuration:**
- Override core count: `make build CORES=8`
- Skip sorries for faster builds: `QUICK_AND_DIRTY=1 make build`
- Override session name: `make build SESSION=My_Session`

## Project Structure

```
Plan.md                         # Project plan and architecture
PROOF_STATUS.md                 # Detailed status of all unfinished proofs

theories/
├── ROOTS                       # Lists sub-session directories
├── graphs/
│   ├── ROOT                    # Verified_SAT_Planner_Graphs session
│   ├── Digraph_DFS_Cycles_Reachability_Aux.thy   # Inner single-source DFS
│   └── Digraph_DFS_Cycles_Reachability.thy        # Outer multi-component loop
├── pddl/
│   ├── ROOT                    # Verified_SAT_Planner_PDDL session
│   └── Certify_PDDL_Grounding.thy    # PDDL grounding verification (stub)
└── datalog/
    ├── ROOT                    # Verified_SAT_Planner_Datalog session
    └── Certify_Datalog_Model.thy     # Datalog model certification (stub)

dependencies/submodules/
├── Isabelle-Graph-Library/           # Graph algorithms (Git submodule)
├── Isabelle-PDDL-Grounding/          # PDDL semantics (Git submodule)
└── parcom/                           # SML parser combinator library

ML/pddl_parser/
├── pddl_validate_plan.sml    # Main SML validator
├── pddl_refactor.sml         # PDDL parser (parser combinators + grammar)
├── pddl_validate_plan.mlb    # MLton build file
└── build_poly.sml            # Poly/ML build script

export/                        # Generated SML files (after `make export-sml`)
```

## Key Architectural Patterns

### Isabelle Session Dependencies

The `theories/ROOTS` file lists sub-session directories (`graphs`, `pddl`, `datalog`), each with their own `ROOT` file. Each session is registered as an Isabelle component. When adding new sessions or modifying dependencies, update the relevant `ROOT` file and rerun `make register-components`.

**Session dependency chain:**
- Main session: `Verified_SAT_Planner`
- Depends on: AFP `Verified_SAT_Based_AI_Planning`, plus `Stratified_Datalog`, `Graph_Algorithms_Dev`, `Tree_Decomp_Grounding`, and project-specific sessions (`Verified_SAT_Planner_Graphs`, `Verified_SAT_Planner_PDDL`, `Verified_SAT_Planner_Datalog`)

### SML Compilation

Two compilers are supported:

- **MLton** (`compile-sml-mlton`): Static compiler, aggressive optimization
- **Poly/ML** (`compile-sml-poly`): Interactive, better for debugging

Both use `.mlb` (MLB) files for dependency management. The `AFP_PATH` environment variable must point to AFP for proper linking.

### Verified Components

Each major feature (PDDL grounding, datalog models, graph algorithms) is isolated in its own subdirectory under `theories/`. Theory files use the naming convention `Verify_*.thy` or `Certify_*.thy`. Complex proofs are structured using Isar with clear reasoning steps rather than imperative tactic mode.

## Proof Development

Always use Isabelle/jEdit (`make jedit`) to create/edit theory files. The Isabelle/Q MCP server must be configured as an MCP server for Claude.

### For GitHub Copilot Agents

**Agents should use native VS Code file I/O tools** (read_file, replace_string_in_file, create_file, etc.) rather than MCP server tools for standard tasks. The MCP server is primarily for interactive proof development. For batch operations, code updates, and file management:

- Use standard workspace file tools for reading and editing `.thy` theory files
- Use `run_in_terminal` for `make` commands and Isabelle batch operations
- Use MCP server tools only when needing real-time interactive proof stepping or when explicitly developing within Isabelle/jEdit

This approach is simpler, more reliable for agents, and avoids coupling workflows to ITP server availability.

### MCP Server Integration

Once per session, before any other `mcp__isabelle__*` call, follow the `isabelle-authenticate` skill: call `mcp__isabelle__authenticate` with any placeholder `token` value (e.g. `""`). A user-side `PreToolUse` hook injects `$IQ_AUTH_TOKEN` from the environment before the request reaches the server, so the token never enters the agent's context.

The Isabelle/jEdit MCP server provides these capability categories:

**File & Context Management:**
- `read_file`, `write_file`, `open_file`, `save_file` — manage theory files
- `get_context_info` — query the command at the active cursor (use `command_selection: 'current'`)
- `get_type_at_selection` — type introspection at cursor position
- `get_entities`, `get_definitions` — explore definitions and entities

**Proof Introspection:**
- `get_proof_context` — inspect current proof state
- `get_proof_blocks` — structure of proof blocks at cursor
- `get_diagnostics` — error and warning messages
- `explore` — navigate and explore the proof structure

**Interactive Proof Development (REPL):**
- `repl_connect`, `repl_init`, `repl_init_from_source` — start interactive sessions
- `repl_step`, `repl_back` — step through proofs forward and backward
- `repl_show`, `repl_state` — display current proof state
- `repl_edit`, `repl_text` — edit proof text
- `repl_replay`, `repl_truncate` — replay or truncate proof history
- `repl_sledgehammer`, `repl_find_theorems` — invoke automation tactics
- `repl_timeout`, `repl_raw` — control execution and raw commands

**Introspection:**
- `list_files` — list tracked theory files
- `get_command_info` — metadata about commands
- `get_document_info` — document structure information
- `resolve_command_target` — resolve command references

See `GUIDANCE.md` for proof writing principles:
- Use `sorry` to sketch structure, then fill gaps one at a time
- Prefer structured Isar for complex proofs; use apply-style for simple lemmas
- Extract complex sub-goals into separate lemmas for clarity
- Develop proofs incrementally, testing 1-2 tactics at a time

## Common Tasks

### Build and test

```bash
make build                    # Full batch build
make build CORES=N           # Use N cores
QUICK_AND_DIRTY=1 make build # Skip sorries
```

### Add a new submodule

1. Register with git and fetch:
   ```bash
   git submodule add <url> dependencies/submodules/<name>
   git submodule update --init --recursive
   ```

2. Register with Isabelle:
   ```bash
   make register-components
   ```

3. Update `theories/ROOT` session dependencies if needed.

### Clean build

```bash
rm -rf export/
isabelle build -c -d . Verified_SAT_Planner  # Clear Isabelle heaps
```

## Dependencies

| Component | Source | Purpose |
|---|---|---|
| Isabelle 2025-2 | `~/bin/Isabelle2025-2` | ITP framework |
| AFP 2025-2 | `~/bin/afp-2025-2` | SAT-based planning semantics |
| Isabelle-Graph-Library | Git submodule | Verified graph algorithms |
| Isabelle-PDDL-Grounding | Git submodule | PDDL semantics and grounding |
| Formal-PDDL-Semantics | Git submodule | Formal PDDL semantics |
| parcom | Git submodule (parcom branch) | SML parsing and utilities |
| MLton / Poly/ML | System package | SML compilation |
| AutoCorrode2025-2 (`iq`) | `~/bin/AutoCorrode2025-2/iq` | Proof exploration (I/Q MCP server) |

## Debugging

**Isabelle build failures:**
- Check component registration: `isabelle components`
- Verify `theories/ROOT` session dependencies exist and are accessible
- Increase verbosity: `make build ISABELLE_FLAGS=-vvv`

**SML compilation errors:**
- Ensure `AFP_PATH` environment variable is set correctly
- Verify `.mlb` file syntax and paths
- Try Poly/ML if MLton fails (often provides clearer error messages)

**Heap cache issues after Isabelle updates:**
```bash
isabelle build -c -d . Verified_SAT_Planner
make build
```

## Project Memory (Synchronized from Claude)

The following project decisions, feedback, and notes are imported from Claude's project memory:

- [Reachability via datalog certificate plan](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/project_reachability_datalog_plan.md) — self-contained T_P/lfp; DFS_Cycles is undirected-only so use a rank certificate; full plan in WIP_reachability_datalog.md.
- [Certificate grounds P_N, not P_R](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/project_certificate_grounds_pn_not_pr.md) — cert certifies the relaxed reachable SET (oracle); grounder must target P_N (real deletes); the `certified_reachability ⊆ wf_grounder P` sublocale grounds the over-approximation = unsound; fix via relax_achievables bridge or fold relaxation into closure_check.
- [Nemo certificate format + CertifyingDatalog reference](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/reference_nemo_certificate_format.md) — cert is Nemo ograph (ordered DAG, predecessor indices, j<i = rank); ~/work/CertifyingDatalog (Lean) is the reference checker; closure check = ⊇ (essential), ordered locallyValid = ⊆ (exactness).
- [Reachability_Analysis is its own session/folder](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/project_reachability_analysis_session.md) — engine+grounder+certificate moved into Reachability_Analysis/; stale jEdit can't verify new session; relaxed_problem sees engine consts unqualified; all_derivs yields ast_classical_plan_action (no plan_action/pa_of_classical bridge — that was dropped).
- [Always invoke isabelle-search first](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_isabelle_search.md) — for any Isabelle name lookup, use the isabelle-search skill on the FIRST attempt; never start with grep/find.
- [Use Isabelle MCP for file edits](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_file_edits.md) — default to mcp__isabelle__write_file/save_file over Edit/Write to keep jEdit's buffer in sync.
- [Edit the .thy file often while proving](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_edit_file_while_proving.md) — land each proof into the file via write_file as you go; don't develop wholesale in a scratch REPL and assemble at the end.
- [Direct edits for bulk renames](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_syntactic_edits.md) — for bulk syntactic edits, use Edit/Write and reload via open_file; reserve mcp__isabelle__write_file for interactive proof work.
- [Formal-PDDL-Semantics: strip iq.iq before push](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/project_formal_pddl_semantics_push.md) — submodule has local pre-commit hook removing `iq.iq` imports; push via SSH to mabdula/Formal-PDDL-Semantics.
- [Submodule pushes go over SSH, never rewrite origin](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_submodule_ssh_push.md) — in any submodule, use the push-ssh skill (explicit SSH URL override); do not `git remote set-url`.
- [Never call get_command_info](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_avoid_get_command_info.md) — it hangs jEdit and forces the user to scroll manually; use get_context_info / jedit-status instead.
- [Verify Isabelle edits via jedit-status, not make build](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_verify_via_jedit.md) — query the running jEdit through `mcp__isabelle__*` (jedit-status skill); only fall back to `make build` if MCP unavailable.
- [Old→new API mapping for the downstream tail](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/project_unrefactored_files.md) — ast_problem→ast_classical_problem, SimpleActionSchema/SimpleActionBody, pair world model + valuation, achievable=fact; Reachability_Analysis ported (green); Grounded_PDDL FULLY proven; don't touch Grounding_Pipeline yet.
- [Grounded_PDDL fully proven — design decisions](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/project_grounded_pddl_done.md) — 0 sorry on pair API; covered forbids numerics, wf_grounder gained init_props/ops_no_num, no [simp] on D⇩G selectors, pair-model proof patterns (I_simp, pg.res_inst unfolding, image distribution).
- [Prefer ∀x∈set xs over list_all](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_forall_over_list_all.md) — in specs/assumptions use bounded ∀; keep list_all only on executable/code paths.
- [No list_all1; use intro/dest rules](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_intro_dest_rules.md) — never state list_all1 (use ∀x∈set); replace `unfolding x_def proof (intro conjI strip)` with declared [intro] rules + [dest] rules for the converse.
- [`(in -)` only inside a context/locale block](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_in_dash_locale.md) — using the dash target qualifier at the top level breaks something; drop it unless nested in an open `context`/`locale` block.
- [Definedness_Translation status](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/project_definedness_translation_status.md) — wf file fully proved (0 sorry); Semantics plan-equivalence now scaffolded in `wf_ast_classical_problem_dt` (`def_state_rel` invariant + 8-lemma chain, all sorried). Notes the `fst M :: atom formula set` type gotcha, the `[simp]`-selector workaround, and (2026-06-04) the located semantics defs + engine lemmas (`entail_adds_irrelevant`, `valuation_def`, `valid_classical_plan_from2_Nil/Cons`) + the global-conjunction/wf hypotheses the scaffold still lacks.
- [Isabelle MCP bridge stale → no tools](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/env_isabelle_mcp_bridge_stale.md) — if `mcp__isabelle__*` never surfaces despite jEdit running, the iq_bridge predates the jEdit launch; ask user to reconnect, don't retry, and don't edit open `.thy` files on disk.
- [Use try0 skill in proofs](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/feedback_use_try0_in_proofs.md) — when a proof method fails or you're unsure, run try0-minimize rather than hand-guessing blast/metis/auto.
- [Relaxation refactor + pipeline WIP](file:///home/david/ai-config/memory/Isabelle-PDDL-Grounding/project_relaxation_refactor_pipeline_wip.md) — PDDL_Relaxation locales fold dx/px sig constants via sublocale rewrites; relax semantics fixed for pair world model; def_translate_normalized proved; Grounding_Pipeline wiring through relaxation still WIP (normalization_normalizes + relaxation rethread onto P_T remain).

