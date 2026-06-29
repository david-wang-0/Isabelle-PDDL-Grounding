# Build the verified SAT-based PDDL planner.
#
#   make export   -- regenerate code/PDDL_SAT_Planner_Exported.sml from the
#                    Isabelle session (Planner_STRIPS_Export.thy + ROOT export_files)
#   make          -- compile the planner binary with MLton
#   make clean
#
# Compile-time dependency: the PDDL parser + libraries (cmlib, SMLParsecomb)
# are taken from the sibling Formal-PDDL-Semantics submodule (no vendored
# copies); override the location with FPS_PLANNING=... if your checkout
# differs.
#
# Runtime dependencies:
#   - the `nmo` (Nemo) binary on PATH (override with NMO=...)
#   - a DIMACS SAT solver speaking SAT-competition output (select with
#     SAT_SOLVER=...; default "z3", e.g. "cryptominisat5 --verb 0" or
#     "kissat -q"; SAT_SOLVER=builtin uses the hand-written DPLL, which is
#     only adequate for the toy running example).

ISABELLE ?= isabelle
MLTON ?= mlton
FPS_PLANNING ?= $(abspath ../../Formal-PDDL-Semantics/codeBase/planning)

BIN = bin/pddl_sat_planner

SRCS = pddl_sat_planner.mlb \
       pddl_sat_planner.sml \
       sat_solver.sml \
       external_sat.sml \
       nemo_driver.sml \
       json_parse.sml \
       basics.sml \
       planner_alias.sml \
       pddl_to_isabelle.sml \
       code/PDDL_SAT_Planner_Exported.sml \
       $(FPS_PLANNING)/pddlParser/util.sml \
       $(FPS_PLANNING)/pddlParser/pddl_refactor.sml

all: $(BIN)

$(BIN): $(SRCS)
	mkdir -p bin
	$(MLTON) -mlb-path-var 'FPS_PLANNING $(FPS_PLANNING)' -output $(BIN) pddl_sat_planner.mlb

# Regenerates the exported SML (writes SMLCodebase/code/... via the ROOT's
# export_files clause). Run from the repository root's session directory.
export:
	$(ISABELLE) build -e -d .. Classical_Grounding

clean:
	rm -rf bin nemo_tmp sat_tmp

.PHONY: all export clean
