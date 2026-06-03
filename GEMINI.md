# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) and Gemini when working with code in this repository.

## Critical Rules

- **Do NOT build the project automatically**: Never run build or compile commands (such as `make build`, `make compile-sml-mlton`, `make compile-sml-poly`, or `isabelle build`) when performing operations, editing files, or answering questions, unless the user has explicitly requested a build or compilation.


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
