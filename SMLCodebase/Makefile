# Build the DFS-founded verified planner + numeric grounder/printer.
#
#   make export   -- regenerate code/PDDL_SAT_Planner_DFS_Exported.sml from the
#                    Classical_Grounding session (writes here via the ROOT's
#                    export_files clause + Planner_Export.thy)
#   make          -- compile the binary with MLton
#   make clean
#
# This is the single SML codebase for the development: the verified exported
# kernel (code/), the untrusted oracle drivers (Nemo, SAT), the PDDL<->Isabelle
# parser bridge, the grounded-PDDL printer, and the CLI. The PDDL parser +
# libraries come from the sibling Formal-PDDL-Semantics checkout (override with
# FPS_PLANNING=...).
#
# Runtime dependencies: the `nmo` (Nemo) binary on PATH, and, for `plan`, a
# DIMACS SAT solver (select with SAT_SOLVER; default "z3"; SAT_SOLVER=builtin
# uses the hand-written DPLL, adequate for the toy running example).

ISABELLE ?= isabelle
MLTON ?= mlton
FPS_PLANNING ?= $(abspath ../../Formal-PDDL-Semantics/codeBase/planning)

BIN = bin/pddl_ground_planner_dfs

SRCS = pddl_ground_planner_dfs.mlb \
       pddl_ground_planner_dfs.sml \
       pddl_printer.sml \
       planner_alias_dfs.sml \
       code/PDDL_SAT_Planner_DFS_Exported.sml \
       sat_solver.sml \
       external_sat.sml \
       nemo_driver.sml \
       json_parse.sml \
       basics.sml \
       pddl_to_isabelle.sml \
       $(FPS_PLANNING)/pddlParser/util.sml \
       $(FPS_PLANNING)/pddlParser/pddl_refactor.sml

all: $(BIN)

$(BIN): $(SRCS)
	mkdir -p bin
	$(MLTON) -mlb-path-var 'FPS_PLANNING $(FPS_PLANNING)' -output $(BIN) pddl_ground_planner_dfs.mlb

# Regenerates the exported SML into code/ (the graph library and this repo are
# registered Isabelle components, so no -d flags -- adding -d double-registers).
export:
	$(ISABELLE) build -e Classical_Grounding

clean:
	rm -rf bin nemo_tmp sat_tmp

.PHONY: all export clean
