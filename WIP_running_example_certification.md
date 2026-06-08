# WIP: run the certificate-grounding pipeline on the running example

Status: **plan** (2026-06-07). Goal: drive `Running_Example.thy` through the **verified
certificate** grounding path (not the unverified `semi_naive_eval`), and stand up an
**executable** SML pipeline that parses real PDDL, calls Nemo, reads the certificate back,
and grounds.

Decisions taken (2026-06-07):
- **Certificate source for the example = full Nemo `ograph`.** We keep the *complete*
  `admissible` check (`closure_check ∧ ordered_check ∧ local_valid`) — exercise the real
  format, not the closure-only shortcut.
- **Generate it live from an `ML ‹…›` block**, not by hand. Isabelle/ML can shell out to
  `nmo` via `Isabelle_System.bash` (AFP precedent below), so the example does the full
  print→nemo→parse round-trip itself. **No SML/Isabelle PDDL parser is needed for the
  example** — `my_problem` is already Isabelle terms; we only need a Datalog **printer** and a
  Nemo-certificate **parser** at ML level.
- **Q1 (AST identity FPS parser ↔ grounding `Base`): assumed YES** (user "pretty sure").
  Light-verify when Part 3 starts; not on the critical path for the example.
- **Q2 (does `value "P_T my_problem"` terminate): UNKNOWN** — must test first.

### AFP references (how to do the ML shell-out + print/parse)
- `Randomised_Social_Choice/Automation/QSOpt_Exact.thy` — **closest analogue.** Shells out to
  an external exact-LP solver and parses the result back. Pattern: a `print : prog -> string`
  + `read : string -> T option`; driver uses `Isabelle_System.with_tmp_file "prog" "lp"` /
  `File.write filename (print_program prog)` /
  `Isabelle_System.bash_process (Bash.script command)` / `read_result (File.read resultname)`;
  binary path from `getenv "QSOPT_EXACT_PATH"` (fallback `"esolver"`). Mirror this with a
  `NEMO_PATH` env var.
- `Hello_World/RunningCodeFromIsabelle.thy` — minimal `Code_Target.produce_code` +
  `Isabelle_System.bash cmd` + `File.tmp_path`/`Bytes.write` template for running generated
  code from inside Isabelle.
- `Munta_Certificate_Checker/` — architecture reference for a *verified certificate checker*
  with both Poly/ML and MLton compile theories (`Munta_Certificate_Compile_{Poly,MLton}.thy`)
  and an `mlunta/` SML front-end (parser + driver). Closest structural model for Part 3's
  standalone binary.

Companion docs: `WIP_nemo_certificate_format.md` (Nemo `ograph` format + CertifyingDatalog
reference), `WIP_reachability_datalog.md` (rank-certificate rationale).

---

## Background: the verified path vs. what the example currently does

`Running_Example.thy` today grounds `my_problem` via `ast_problem.semi_naive_eval` (the
*unverified* reachability — its `found_*` theorems in `Reachability_Analysis.thy` are still
`sorry`) and then `as_strips`. The verified path in `Grounding_Pipeline.thy`
(`context ast_classical_problem`, then inner `context fixes cert assumes admissible_cert
grounding_cert`) is:

```
P_X = explicate_def_prob …            -- definedness explication
P_N = split_prob P_X                  -- precondition split
P_T = def_translate_prob P_N          -- THE problem the certificate is checked against
P_R = relax_prob P_T                  -- delete-relaxation (positive single-stratum datalog)
admissible cert ∧ grounding_checks cert        -- both fully executable (eval)
P_G_cert = grounder.ground_prob P_T (cert_facts_of P_T cert) (cert_ops_of P_T cert)
P_S_cert = as_strips P_G_cert
```

Everything is `value`/`eval`-computable; all names resolve as `ast_classical_problem.X
my_problem cert`.

Key facts about the certificate machinery (from `Reachability_Analysis/`):
- `datatype cert_node = CNode (cn_fact: facty) (cn_preds: "nat list")`,
  `datatype certificate = Cert (nodes: "cert_node list")`. `facty = object atom formula`;
  `fact_to_facty (p, xs) = Atom (predAtm p xs)`.
- `pddl_datalog.admissible c = closure_check c ∧ ordered_check c ∧ (∀ i. local_valid c i)`,
  checked against the **relaxed** problem `relax_prob P_T`.
- `normalized_problem_rx.grounding_checks` — syntactic wf/coverage of
  `cert_facts_of`/`cert_ops_of` (decidable).
- `certified_reachability = normalized_problem_rx + assumes admissible_cert grounding_cert`.
- Only `closure_check` is needed for soundness (`closure_sound`/`cert_ops_sound`);
  `ordered_check`+`local_valid` are the exactness (⊆) upgrade — but we keep them per the
  decision above.

---

## Part 1 — Isabelle: extend `Running_Example.thy` to the certificate step

1. `definition my_P_T ≡ ast_classical_problem.P\<^sub>T my_problem` (and `my_P_R ≡ relax_prob
   my_P_T`); `value` both. **Confirm `value` terminates** in the warm heap (reachability
   already "takes a minute" here).
2. Paste the Nemo-generated `ograph` as `definition my_cert ≡ Cert [CNode … …, …]`
   (see Part 2).
3. Discharge the two locale assumptions by evaluation:
   - `lemma "pddl_datalog.admissible my_P_R my_cert" by eval`
   - `lemma "normalized_problem_rx.grounding_checks my_P_T my_cert" by eval`
4. Ground + inspect, paralleling the existing `Π_G`/`Π_S` block but on certified facts/ops:
   - `value "grounder.ground_prob my_P_T (normalized_problem_rx.cert_facts_of my_P_T my_cert)
            (normalized_problem_rx.cert_ops_of my_P_T my_cert)"` (= `P_G_cert`)
   - `value "ast_classical_problem.as_strips …"` (= `P_S_cert`)
5. Optional: `interpret certified_reachability my_problem my_cert` (discharging via the two
   eval lemmas) and pull `wf_ground_cert_problem` to show the grounded problem is well-formed.

## Part 2 — Generating the example certificate with Nemo, live from `ML ‹…›`

Do the whole print→nemo→parse round-trip inside an `ML ‹…›` block (QSOpt_Exact pattern), so
the example is reproducible and actually exercises the printer + parser. The output is a HOL
`certificate` we feed to the `by eval` checks of Part 1.

1. **Datalog printer (ML).** `print_program : term (relax_prob my_P_T) -> string` emitting
   Nemo `.rls`:
   - init facts → ground `p(a,b).`
   - each `pred_clause` → `head(?X,…) :- b1(…), …` (positive body from `cl_pred_pre`, guards
     from `cl_cond_pre`, head from `consequence_of`).
   Easiest to drive off a `value`-computed `relax_prob my_P_T` reflected to ML, or off an
   exported printer (Part 3.3) reused here.
2. **Trace goal.** `traceGoal.txt` = facts to explain (all reachable, or the goal atoms).
3. **Shell out (QSOpt_Exact pattern).**
   ```
   Isabelle_System.with_tmp_file "prog" "rls" (fn rlsname =>
     Isabelle_System.with_tmp_file "cert" "json" (fn outname => let
       val nemo = (case getenv "NEMO_PATH" of "" => "nmo" | p => p)
       val _ = File.write rlsname (print_program prog)
       val cmd = Bash.string nemo ^ " --trace-input-file … --trace-output " ^
                 File.bash_path outname ^ " " ^ File.bash_path rlsname
       val res = Isabelle_System.bash_process (Bash.script cmd)
     in read_certificate (File.read outname) end))
   ```
   (+ the `inputCreatorNemo.py` post-processor → `*.ograph.json`, or call nemo's native trace
   output if it already emits ograph.)
4. **Certificate parser (ML).** `read_certificate : string -> term` parsing the `ograph` JSON
   (`{graph:{edges:[{label:{symbol,terms}, predecessors:[Nat]}]}}`) into a HOL
   `certificate` term: each edge → `CNode (Atom (predAtm (Pred STR ''symbol'')
   [Obj STR ''t1'', …])) [preds]`, **preserving array order** (= rank; `ordered_check` needs
   predecessor index < own index).
5. **Inject + check.** Bind the parsed term as `definition my_cert ≡ Cert […]` (emit the
   source via ML, or splice the term through a local-theory definition), then discharge
   `admissible`/`grounding_checks` by `eval` (Part 1.3). `by eval` is the safety net — any
   ordering/transcription slip is rejected, not trusted.

## Part 3 — Executable SML pipeline (parser → datalog → Nemo → cert → ground)

Standalone binary that grounds a real `.pddl`/`.problem` pair by certification. Unlike the
example (Part 2) this **does** need a PDDL parser. Three SML pieces, mirroring the
`Formal-PDDL-Semantics` repo layout: (i) **PDDL parser** (reuse FPS), (ii) **Datalog
printer**, (iii) **Nemo-certificate parser**. The ML printer/parser from Part 2 are the
working prototypes for (ii) and (iii) — port them to exported SML here. Architecture model:
`Munta_Certificate_Checker/mlunta/` + `Munta_Certificate_Compile_{Poly,MLton}.thy`.

1. **Code export (new theory).** No `export_code` exists yet. Add `Code_Export.thy` (model on
   `Formal-PDDL-Semantics/Classical_PDDL_Checker_Explicit_Export.thy`: containers `derive`
   setup, strip `STArray`/`FArray`). Export: normalization chain → `P_T`, `relax_prob`,
   `closure_check`/`admissible`/`grounding_checks`, `cert_facts_of`, `cert_ops_of`,
   `ground_prob`, `as_strips`.
2. **Front-end parser.** Reuse `Formal-PDDL-Semantics/codeBase/planning/pddlParser/
   pddl_refactor.sml` + `classical_explicit_alias.sml`.
   **RISK — spike first:** confirm the parser's classical AST is the *same type* the grounding
   repo's `Base` uses (`Domain/Problem/PredDecl/SimpleActionSchema/predAtm/Obj/Pred/Either`).
   If they differ, write a thin AST adapter. This is the biggest unknown.
3. **Datalog emitter (net-new).** No `.rls` printer exists — only `pred_clauses`/
   `consequence_of` give rule *structure*. Add `relax_prob P_T → string` (Isabelle or SML)
   printing Nemo `.rls` + the goal/trace file.
4. **Nemo shell-out (SML driver).** Write `prog.rls` + `traceGoal.txt`, run `nmo …`, run the
   Python post-processor → `*.ograph.json`.
5. **Certificate read-back (net-new SML JSON reader).** Parse Nemo `ograph`
   (`{graph:{edges:[{label:{symbol,terms},predecessors:[Nat]}]}}`) into the exported
   `certificate` datatype.
6. **Check + ground.** Run exported `admissible`/`grounding_checks`; on success
   `ground_prob`/`as_strips`; emit result. Add a `.mlb` + Makefile target next to
   `compile-sml-*`.

Emitter (Part 3.3) and ograph reader (Part 3.5) are **outside the trusted kernel** — the
kernel re-checks their output via `admissible`/`grounding_checks` — so they need testing, not
proofs.

## Part 4 — Risks / confirm-as-you-go

- **AST identity** between the FPS parser and the grounding repo (Part 3.2) — spike before
  anything else.
- **`value`/`eval` performance** on `P_T` + the checks at this example size — may need `[code]`
  tuning.
- **Net-new untrusted code**: the `.rls` emitter and ograph JSON reader.
- Transcription fidelity of the offline `ograph` (Part 2.4) — `ordered_check` will reject any
  out-of-order predecessor index; `by eval` is the safety net.

---

# SESSION PROGRESS — 2026-06-07 (handoff)

## What now works (verified green in jEdit)

`Running_Example.thy` is **ported to the current API and green** (`fully_processed`,
`consolidated`, 0 errors) through the normalization+relaxation spine:

- `definition my_P\<^sub>T \<equiv> ast_classical_problem.P\<^sub>T my_problem` — `value "my_P\<^sub>T"` **evaluates**.
- `definition my_P\<^sub>R \<equiv> ast_classical_problem.relax_prob my_P\<^sub>T` — `value "my_P\<^sub>R"` **evaluates**.

So the example runs end-to-end **up to the certification step** (`P\<^sub>R` = the normalized,
delete-relaxed problem that feeds certification). Pipeline order (in `context
ast_classical_problem`, so everything is `ast_classical_problem.X my_problem`):
`P\<^sub>T = def_translate(split(explicate_def(degoal(detype(P)))))`, `P\<^sub>R = relax_prob P\<^sub>T`.

The old file was **stale** (old API: `ast_problem`/`ast_domain`/`detype_prob`…). Lines 188→end
were rewritten; the data definitions (`my_types`…`my_problem`, `my_plan`) were kept verbatim
(constructors unchanged). The old slow `semi_naive`/`grounder.ground_prob`/`as_strips` tail was
replaced.

## The big blocker we found and fixed: code-generation setup

`value`-ing any pipeline constant fails out of the box. Two distinct causes, both now handled
inline in `Running_Example.thy` (the block headed *"Code setup (to move to Common/Code_Setup.thy)"*):

**(1) Shared-locale code-equation poisoning.** Grounding's normalization functions are defined
`(in domain_signature)`/`(in problem_signature)` — base locales FPS *also* instantiates at its
record-based continuous/temporal problem types (`ast_cont_domain`, `ast_cont_problem`,
`ast_temporal_domain`, `ast_temporal_problem`; `ast_domain`/`ast_problem` is one datatype reused
for all schema types, `Continuous_Planning/Abstract_Syntax.thy`). The shared constant takes the
signature fields as leading args; the per-interpretation code equations instantiate them with
**field-selector applications** (`predicates ?d`), which are not valid code-equation patterns
(`"…predicates" is not a constructor, on left hand side of equation`). Code-gen validates **all**
equations for a constant (reachable or not), so it hard-errors. **Fix:** per shared constant,
`declare [[code drop: domain_signature.X]]` then `declare domain_signature.X_def[code]`
(re-add only the clean field-variable equation). Done for: `detyped_predicates`,
`detyped_consts`, `detyped_functions`, `problem_signature.detyped_objs`, `param_precond`,
`def_prefix`, `detype_simple_action_body` (a `fun` → re-add `.simps`, drop by const name).
- **GOTCHA:** `pred_names` is an **abbreviation** (`map (predicate.name ∘ pred)`), *not* a
  constant — `code drop: …pred_names` fails (`Not a constant: …`) and it has no `_def`. Leave
  it out entirely (it inlines). Same caution for other abbreviations (`sf_substate`,
  `all_consts` had no `ast_cont_problem.all_consts_def` fact either).
- The bracket `[[code drop: a b c]]` form drops the constants it *can* even if one name in the
  list errors (that's why values worked despite the `pred_names` error before we removed it).

**(2) Missing executable equations.** Independent of (1):
- **`def_translate` has no `*_code` bundle.** Every other normalization step ships one
  (`type_norm_code`, `goal_norm_code`, `precond_norm_code`, `explicate_def_code`, `relax_code`,
  `pddl_ground_code`, `to_strips_code`, `pseudo_datalog_code`, each `declare …[code]` in its
  `*_Semantics.thy`). Definedness_Translation is the **only** step missing it. Inline fix:
  `declare ast_classical_domain.def_translate_dom_def[code]` +
  `ast_classical_problem.def_translate_prob_def[code]`. → **upstream TODO: add a
  `def_translate_code` bundle in `Definedness_Translation/…Semantics.thy`.**
- **Lifted string ops** (`Common/String_Utils.thy`) have no code equations. Added:
  `lemma padl_lit_code[code]: "padl_lit n s = String.implode (padl n (String.explode s))"`
  `by (metis padl_lit.rep_eq String.implode_explode_eq)` and `declare distinct_strings_lit_eq[code]`
  (the latter already proven, just not `[code]`). → **upstream TODO: land these in
  `String_Utils.thy`.**

## Dead end: `semi_naive_eval` reachability is not code-runnable

`value (semi_naive_eval my_P\<^sub>R)` fails with a **wellsortedness error**: its dependency graph is
`semi_naive_eval → … → all_finished_paramz → valuation → numeric_expression_valuation → sin →
suminf → sums → nhds → Inf [filter]` and `filter` is not of sort `enum`. The numeric-free
problem never executes those paths, but code-gen needs the whole graph. **The certificate route
avoids this** — `pddl_datalog.closure_check`/`admissible` validate the certificate against the
action clauses + facts of `P\<^sub>R` directly, never touching the numeric `valuation`. (So do **not**
try to make `semi_naive_eval` executable; route through the cert checker instead.)

## Next steps (in order)

1. **Migrate the inline code-setup block into `Common/Code_Setup.thy`** (the agreed home). Import
   it from `Running_Example` (and later from the Part 3 export theory — it hits the identical
   wall). Add to the session `ROOT`. *Driving method stays:* iterate via `value`/`code_thms`
   errors (each names the next bad fact). More `code drop`s will surface as the cert checker’s
   own constants (`closure_check`, `consequence_of`, `satisfies_conds`, `ac_tsubst`,
   `cert_facts_of`, `ground_prob`) get exercised.
2. **Make the cert checker executable** and add the certification section to the example:
   `value`/`eval` on `pddl_datalog.closure_check my_P\<^sub>R cert`, `admissible`,
   `normalized_problem_rx.grounding_checks my_P\<^sub>T cert`, then
   `grounder.ground_prob my_P\<^sub>T (cert_facts_of …) (cert_ops_of …)` (= `P\<^sub>G_cert`). Expect a
   fresh round of code-setup drops here.
3. **Produce the certificate** (decided: full Nemo `ograph`, live from `ML ‹…›` — Part 2 above):
   datalog printer → `Isabelle_System.bash` to `nmo` (QSOpt_Exact pattern) → ograph parser →
   HOL `certificate` term → `by eval` the checks.

## MCP workflow notes (this jEdit session)

- The prover wedges (idle at partial `finished`, `running:0`) and won't advance on
  `get_diagnostics`/`get_command_info` alone. **`get_proof_context` at a `file_offset`/`file_pattern`
  inside the target command DOES advance processing** (it returns an Isar_Explore error but
  forces the prefix). Then read results via `get_command_info include_results=true`.
- `value` output / `get_diagnostics scope=file` can exceed the token limit (huge printed terms);
  it gets saved to a temp file — `grep`/`python` slice it for the actual error lines.
