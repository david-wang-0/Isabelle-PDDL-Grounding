# Verified PDDL Grounding — temporal normalization cone (artifact branch)

This branch is a trimmed copy of [Isabelle-PDDL-Grounding](https://github.com/david-wang-0/Isabelle-PDDL-Grounding)
(branch `fps-analysis-free-split`, commit `352ea8c`) that keeps only the sessions the temporal
planning certification development depends on: the normalization locales and formula utilities
for temporal PDDL, built on the discrete (HOL-Analysis-free) core of Formal-PDDL-Semantics.

| session | directory |
|---|---|
| `Grounding_Light_Base` | `Grounding_Common/Base/Light_Base` |
| `Grounding_Base` | `Grounding_Common/Base/Base` |
| `Grounding_Utils` | `Grounding_Common/Utils` |
| `Grounding_Common` | `Grounding_Common/Common` |
| `Grounding_Temporal_Base` | `Temporal_Grounding/Base/Temporal_Base` |
| `Temporal_Grounding_Utils` | `Temporal_Grounding/Utils` |
| `Grounding_Temporal_Common` | `Temporal_Grounding/Common` |

The grounding pipeline itself (reachability analysis, datalog certification, classical grounding,
the SAT-based planner and its SML harness) is not part of this branch.

## Requirements

- [Isabelle2025-2](https://isabelle.in.tum.de/installation.html) with the
  [AFP](https://www.isa-afp.org/download/) for Isabelle2025-2 registered as a component.
- The `artifact` branch of Formal-PDDL-Semantics (sessions `Discrete_Planning_Common`,
  `Discrete_Temporal_Planning`, `Utils`), registered as a component or passed with `-d`.

## Building

```sh
isabelle build -d <formal-pddl-semantics> -d . -b Grounding_Temporal_Common
```
