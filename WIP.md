# WIP index

Status overview of the planning documents (last reviewed 2026-06-12, post-cleanup).

Start here: [HANDOVER.md](HANDOVER.md) — full repository summary, exact sorry inventory,
and the ordered next-steps list (including the **unverified 2026-06-12 session restructure**
that must be re-checked in jEdit first).

Architecture references (not WIP docs):

- [ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md) — one-page summary of the entire
  pipeline: normalization → relaxation → certified reachability → grounding → STRIPS → SAT →
  plan restoration, with per-stage status and the two-untrusted-oracles trust story.
- [ARCHITECTURE_datalog_certification.md](ARCHITECTURE_datalog_certification.md) — the
  certificate-based checking design: the standalone generic datalog certification session
  (`Datalog_Certification`, 0 sorry) vs. PDDL reachability certification
  (`Reachability_Analysis/Reachability_Certificate.thy`, now also hosting the bridge and the
  minimal-model relation), and the untrusted Nemo transport between them.

| | File | Summary | Status |
| --- | --- | --- | --- |
| `[ ]` | [WIP_datalog_cert_bridge.md](WIP_datalog_cert_bridge.md) | Bridge the generic datalog checker to the PDDL reachability requirements: check-level (`dl_admissible` ⟹ `admissible_exec`) and semantic-level (`achievable_eq_minimal_model`). | Active. Proven: conversion, structural/ordered/positivity, closure transfer, main theorem assembly. Sorried: local-validity transfer + the two minimal-model inclusions + ops requirement (4 sorries in `Reachability_Certificate.thy`); `dl_bridge_wf` discharge for the pipeline instance still to do. |

Removed as completed/superseded — recover from git history if needed:

- 2026-06-12: `TODO.md` (open items absorbed into `HANDOVER.md`), `WIP_executable_pipeline.md`
  (end-to-end `plan_by_cert` done: `plan_by_cert_sound` 0 sorry, binary plans the running
  example, FPS validator confirms), `WIP_running_example_certification.md` (superseded by the
  in-Isabelle `naive_cert` oracle in `Running_Example.thy` + the `SMLCodebase/` round-trip),
  `Documentation/dependencies.md` (pre-refactor import graph).
- 2026-06-10: `WIP_grounded_pddl_port.md`, `WIP_nemo_certificate_format.md`,
  `WIP_reachability_datalog.md`, `WIP_numeric_definedness.md`,
  `WIP_plan_restoration_and_sat_output.md`, `WIP_session_handoff.md`.
