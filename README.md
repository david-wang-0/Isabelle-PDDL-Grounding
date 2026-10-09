# Verified PDDL Grounding — temporal normalization cone

This is a trimmed copy of the verified PDDL grounding development that keeps only the sessions the
temporal planning certification development depends on: the normalization locales and formula utilities
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
the SAT-based planner and its SML harness) is not included.

## Requirements

- [Isabelle2025-2](https://isabelle.in.tum.de/installation.html) with the
  [AFP](https://www.isa-afp.org/download/) for Isabelle2025-2 registered as a component.
- The discrete core of Formal PDDL Semantics (sessions `Discrete_Planning_Common`,
  `Discrete_Temporal_Planning`, `Utils`), registered as a component or passed with `-d`.

## Building

```sh
isabelle build -d <formal-pddl-semantics> -d . -b Grounding_Temporal_Common
```

## Origin

The theories in this repository are derived from Maximilian Vollath's verified PDDL grounder, his
thesis project "Verified Grounding of PDDL Tasks using Reachability Analysis (and Tree
Decomposition)" (<https://github.com/MVollath/Isabelle-PDDL-Grounding>), used under the MIT
licence. His portions remain his work. See `NOTICE.md`.

## Licence

MIT, see `LICENSE`.
