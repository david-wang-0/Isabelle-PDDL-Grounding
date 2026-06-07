# To dos

- [~] run the small pieces of code in the running example
      — `Running_Example.thy` GREEN through `P\<^sub>T`/`P\<^sub>R`; full details + next steps in
      `WIP_running_example_certification.md` (§ SESSION PROGRESS 2026-06-07).
  - [x] port `Running_Example` to the current API (was stale: `ast_problem`→`ast_classical_problem`,
        `detype_prob`→`detype_classical_prob`, …)
  - [x] code-gen setup so `value "my_P\<^sub>T"`/`"my_P\<^sub>R"` evaluate: per shared `domain_signature`/
        `problem_signature` constant, `code drop` the FPS cont/temporal per-interpretation code
        equations (selector-pattern, invalid) + re-add the foundational one; `[code]` for
        `def_translate_{dom,prob}`; `padl_lit_code` + `distinct_strings_lit_eq[code]`
  - [ ] move the inline code-setup block into `Base/Code_Setup.thy` (+ `ROOT`, import from
        `Running_Example` and the future Part-3 export theory — same wall)
  - [ ] upstream: add a `def_translate_code` bundle in `Definedness_Translation/…Semantics.thy`
        (it is the ONLY normalization step missing one); land `padl_lit_code` +
        `distinct_strings_lit_eq[code]` in `Base/String_Utils.thy`
  - [ ] note: `semi_naive_eval` is NOT code-runnable — its `valuation` pulls
        `numeric_expression_valuation → sin → suminf → Inf [filter]` (wellsortedness, `filter`
        not `enum`). The certificate checker (`closure_check`/`admissible`) bypasses it.
  - [ ] make `closure_check`/`admissible`/`grounding_checks`/`ground_prob` executable; add the
        certification section to the example (expect another round of `code drop`s)
  - [ ] produce the certificate (decided: full Nemo `ograph`, live from `ML ‹…›`) — Parts 2/3 of
        `WIP_running_example_certification.md`
- [ ] fix the relevant proofs w.r.t. abstract semantics
  - [ ] comment out executable bits for now
