theory Running_Example
  imports Main
    Grounding_Pipeline_STRIPS_Executable
begin


subsection \<open> Problem Description \<close>

text \<open>
This is the PDDL problem from Helmert 2009, but modified in minor ways.
It makes use of:
  - type hierarchy
  - parameters with Either types
  - non-trivial preconditions
  - multiple inheritance
  - circular type graph
  - negations in preconditions
It doesn't use:
  - Eq in formulas
It can't use, because I restrict that:
  - objects/consts with Either types
\<close>

definition "my_types \<equiv> [
  (STR ''City'', STR ''object''), (STR ''Movable'', STR ''object''),
  (STR ''Vehicle'', STR ''Movable''), (STR ''Parcel'', STR ''Movable''),
  (STR ''Car'', STR ''Vehicle''), (STR ''Train'', STR ''Vehicle''),
  (STR ''R'', STR ''L''), (STR ''L'', STR ''R''),
  (STR ''Batmobile'', STR ''Car''), (STR ''Batmobile'', STR ''Train'')]"
(* purposely doing Car/Train instead of only Vehicle, for no reason other than to just use that feature somewhere *)
definition "my_preds \<equiv> [
  PredDecl (Pred STR ''at'') [Either [STR ''Movable''], Either [STR ''City'']],
  PredDecl (Pred STR ''in'') [Either [STR ''Parcel''], Either [STR ''Car'', STR ''Train'']],
  PredDecl (Pred STR ''road'') [Either [STR ''City''], Either [STR ''City'']],
  PredDecl (Pred STR ''rails'') [Either [STR ''City''], Either [STR ''City'']]
]"
definition "my_consts \<equiv> [
  (Obj STR ''A'', Either [STR ''City'']), (Obj STR ''B'', Either [STR ''City'']),
  (Obj STR ''C'', Either [STR ''City'']), (Obj STR ''D'', Either [STR ''City'']),
  (Obj STR ''E'', Either [STR ''City'']), (Obj STR ''F'', Either [STR ''City'']),
  (Obj STR ''G'', Either [STR ''City''])
]"

definition "op_drive \<equiv> SimpleActionSchema
  (ActionHead STR ''drive''
    [(variable.Var STR ''c'', Either [STR ''Car'']), (variable.Var STR ''from'', Either [STR ''City'']), (variable.Var STR ''to'', Either [STR ''City''])])
  (SimpleActionBody
    (And (Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''c''), term.VAR (variable.Var STR ''from'')]))
       (Or (Atom (predAtm (Pred STR ''road'') [term.VAR (variable.Var STR ''from''), term.VAR (variable.Var STR ''to'')]))
           (Atom (predAtm (Pred STR ''road'') [term.VAR (variable.Var STR ''to''), term.VAR (variable.Var STR ''from'')]))))
    (Effect
      [Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''c''), term.VAR (variable.Var STR ''to'')])]
      [Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''c''), term.VAR (variable.Var STR ''from'')])] []))"
definition "op_choochoo \<equiv> SimpleActionSchema
  (ActionHead STR ''choochoo''
    [(variable.Var STR ''t'', Either [STR ''Train'']), (variable.Var STR ''from'', Either [STR ''City'']), (variable.Var STR ''to'', Either [STR ''City''])])
  (SimpleActionBody
    (And (Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''t''), term.VAR (variable.Var STR ''from'')]))
       (Or (Atom (predAtm (Pred STR ''rails'') [term.VAR (variable.Var STR ''from''), term.VAR (variable.Var STR ''to'')]))
           (Atom (predAtm (Pred STR ''rails'') [term.VAR (variable.Var STR ''to''), term.VAR (variable.Var STR ''from'')]))))
    (Effect
      [Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''t''), term.VAR (variable.Var STR ''to'')])]
      [Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''t''), term.VAR (variable.Var STR ''from'')])] []))"
(* into has to be Car/Train instead of Vehicle because of the definition of the predicate "in" *)
definition "op_load \<equiv> SimpleActionSchema
  (ActionHead STR ''load''
    [(variable.Var STR ''what'', Either [STR ''Parcel'']), (variable.Var STR ''where'', Either [STR ''City'']), (variable.Var STR ''into'', Either [STR ''Car'', STR ''Train''])])
  (SimpleActionBody
     (And (Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''into''), term.VAR (variable.Var STR ''where'')]))
         (Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''what''), term.VAR (variable.Var STR ''where'')])))
    (Effect
      [Atom (predAtm (Pred STR ''in'') [term.VAR (variable.Var STR ''what''), term.VAR (variable.Var STR ''into'')])]
      [Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''what''), term.VAR (variable.Var STR ''where'')])] []))"
definition "op_unload \<equiv> SimpleActionSchema
  (ActionHead STR ''unload''
    [(variable.Var STR ''what'', Either [STR ''Parcel'']), (variable.Var STR ''from'', Either [STR ''Car'', STR ''Train'']), (variable.Var STR ''where'', Either [STR ''City''])])
  (SimpleActionBody
     (And (Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''from''), term.VAR (variable.Var STR ''where'')]))
         (Atom (predAtm (Pred STR ''in'') [term.VAR (variable.Var STR ''what''), term.VAR (variable.Var STR ''from'')])))
    (Effect
      [Atom (predAtm (Pred STR ''at'') [term.VAR (variable.Var STR ''what''), term.VAR (variable.Var STR ''where'')])]
      [Atom (predAtm (Pred STR ''in'') [term.VAR (variable.Var STR ''what''), term.VAR (variable.Var STR ''from'')])] []))"
(* btw, this is considered well-formed as long as x is not used in precondition or effects *)
definition "op_broken \<equiv> SimpleActionSchema
  (ActionHead STR ''broken''
    [(variable.Var STR ''x'', Either [STR ''n'existe pas''])])
  (SimpleActionBody \<bottom> (Effect [] [] []))"
(* This operator is only there to demonstrate relaxation of action preconditions, since I couldn't think of anything
  better that would make use of negative preconditions.*)
definition "op_build_tracks \<equiv> SimpleActionSchema
  (ActionHead STR ''lay_tracks''
    [(variable.Var STR ''from'', Either [STR ''City'']), (variable.Var STR ''to'', Either [STR ''City''])])
  (SimpleActionBody
    (And (Not (Atom (predAtm (Pred STR ''rails'') [term.VAR (variable.Var STR ''from''), term.VAR (variable.Var STR ''to'')])))
         (Not (Atom (predAtm (Pred STR ''rails'') [term.VAR (variable.Var STR ''to''), term.VAR (variable.Var STR ''from'')]))))
    (Effect [Atom (predAtm (Pred STR ''rails'') [term.VAR (variable.Var STR ''from''), term.VAR (variable.Var STR ''to'')])] [] []))"

definition "my_funcs \<equiv> []"

definition "my_actions \<equiv> [op_drive, op_choochoo, op_load, op_unload]"

definition "my_domain \<equiv> Domain my_types my_preds my_funcs my_consts my_actions"
value "my_domain"

(* batmobile because why not *)
definition "my_objs \<equiv> [
  (Obj STR ''c1'', Either [STR ''Car'']),
  (Obj STR ''c2'', Either [STR ''Car'']),
  (Obj STR ''c3'', Either [STR ''Car'']),
  (Obj STR ''t'', Either [STR ''Train'']),
  (Obj STR ''p1'', Either [STR ''Parcel'']),
  (Obj STR ''p2'', Either [STR ''Parcel'']),
  (Obj STR ''batmobile'', Either [STR ''Batmobile''])
]"

abbreviation fact_to_atm :: "(name \<times> String.literal list) \<Rightarrow> object atom formula" where
  "fact_to_atm f \<equiv> case f of (p, xs) \<Rightarrow> Atom (predAtm (Pred p) (map Obj xs))"

definition "my_init \<equiv> [
  Atom (predAtm (Pred STR ''at'') [Obj STR ''c1'', Obj STR ''A'']),
  Atom (predAtm (Pred STR ''at'') [Obj STR ''c2'', Obj STR ''B'']),
  Atom (predAtm (Pred STR ''at'') [Obj STR ''c3'', Obj STR ''G'']),
  Atom (predAtm (Pred STR ''at'') [Obj STR ''t'', Obj STR ''E'']),
  Atom (predAtm (Pred STR ''at'') [Obj STR ''p1'', Obj STR ''C'']),
  Atom (predAtm (Pred STR ''at'') [Obj STR ''p2'', Obj STR ''F'']),
  Atom (predAtm (Pred STR ''road'') [Obj STR ''A'', Obj STR ''D'']),
  Atom (predAtm (Pred STR ''road'') [Obj STR ''B'', Obj STR ''D'']),
  Atom (predAtm (Pred STR ''road'') [Obj STR ''C'', Obj STR ''D'']),
  Atom (predAtm (Pred STR ''rails'') [Obj STR ''D'', Obj STR ''E'']),
  Atom (predAtm (Pred STR ''road'') [Obj STR ''E'', Obj STR ''F'']),
  Atom (predAtm (Pred STR ''road'') [Obj STR ''F'', Obj STR ''G'']),
  Atom (predAtm (Pred STR ''road'') [Obj STR ''G'', Obj STR ''E''])
]"
(* purposefully omitting batmobile from init because that would
  increase the ground problem too much *)
(* Atom (predAtm (Pred STR ''at'') [Obj STR ''batmobile'', Obj STR ''D'']) *)

definition "my_goal \<equiv>
  And (Atom (predAtm (Pred STR ''at'') [Obj STR ''p1'', Obj STR ''G'']))
      (Atom (predAtm (Pred STR ''at'') [Obj STR ''p2'', Obj STR ''E'']))"

definition "my_problem \<equiv> Problem my_domain my_objs my_init my_goal"

(* lemma wf_d1: "wf_ast_classical_domain my_domain"
  apply unfold_locales
  unfolding ast_classical_domain.wf_classical_domain_def 
  unfolding domain_signature.wf_domain_signature_def
  unfolding domain_signature.wf_types_def
  

lemma wf_p1: "ast_problem.wf_problem my_problem"
  by (intro wf_problem_intro) eval *)

subsection \<open> Execution \<close>

definition "my_plan \<equiv> [
  SimplePlanAction STR ''drive'' [Obj STR ''c1'', Obj STR ''A'', Obj STR ''D''],
  SimplePlanAction STR ''drive'' [Obj STR ''c1'', Obj STR ''D'', Obj STR ''C''],
  SimplePlanAction STR ''load'' [Obj STR ''p1'', Obj STR ''C'', Obj STR ''c1''],
  SimplePlanAction STR ''drive'' [Obj STR ''c1'', Obj STR ''C'', Obj STR ''D''],
  SimplePlanAction STR ''unload'' [Obj STR ''p1'', Obj STR ''c1'', Obj STR ''D''],  
  SimplePlanAction STR ''choochoo'' [Obj STR ''t'', Obj STR ''E'', Obj STR ''D''],
  SimplePlanAction STR ''load'' [Obj STR ''p1'', Obj STR ''D'', Obj STR ''t''],  
  SimplePlanAction STR ''choochoo'' [Obj STR ''t'', Obj STR ''D'', Obj STR ''E''],
  SimplePlanAction STR ''unload'' [Obj STR ''p1'', Obj STR ''t'', Obj STR ''E''],

  SimplePlanAction STR ''drive'' [Obj STR ''c3'', Obj STR ''G'', Obj STR ''F''],
  SimplePlanAction STR ''load'' [Obj STR ''p2'', Obj STR ''F'', Obj STR ''c3''],
  SimplePlanAction STR ''drive'' [Obj STR ''c3'', Obj STR ''F'', Obj STR ''E''],
  SimplePlanAction STR ''unload'' [Obj STR ''p2'', Obj STR ''c3'', Obj STR ''E''],

  SimplePlanAction STR ''load'' [Obj STR ''p1'', Obj STR ''E'', Obj STR ''c3''],
  SimplePlanAction STR ''drive'' [Obj STR ''c3'', Obj STR ''E'', Obj STR ''G''],
  SimplePlanAction STR ''unload'' [Obj STR ''p1'', Obj STR ''c3'', Obj STR ''G'']
]"
(*
SimplePlanAction STR ''choochoo'' [Obj STR ''batmobile'', Obj STR ''D'', Obj STR ''E''],
  SimplePlanAction STR ''drive'' [Obj STR ''batmobile'', Obj STR ''E'', Obj STR ''G'']
Just taking the batmobile for a spin at the end, for fun. *)
(* 
value "enab_exec_x my_problem
  (SimplePlanAction STR ''drive'' [Obj STR ''c1'', Obj STR ''A'', Obj STR ''D'']) (set my_init)"

value "valid_plan_x my_problem my_plan"
lemma "ast_problem.valid_plan my_problem my_plan"
  by (intro valid_plan_intro[OF wf_p1]) eval *)


subsection \<open>Pipeline normalization to \<open>P\<^sub>T\<close>, stage by stage\<close>

text \<open>The verified grounding pipeline normalizes via
  detype \<rightarrow> degoal \<rightarrow> explicate-definedness \<rightarrow> split \<rightarrow> def-translate, which
  \<^const>\<open>ast_classical_problem.P\<^sub>T\<close> composes into a single constant. Below, each intermediate
  problem is named and evaluated as well, so the effect of every stage is visible in isolation
  (the numeric twin \<open>Running_Example_Numeric\<close> threads the same chain, with the definedness
  stages doing real work there). Since this problem has no numeric functions,
  the definedness steps here are essentially identity. The code-generation setup needed to evaluate
  the stages lives in \<^theory>\<open>Classical_Grounding.Code_Setup\<close> (imported above).\<close>

text \<open>\<^bold>\<open>Stage 1 --- type normalization\<close> (\<open>P2\<close>,
  \<^const>\<open>ast_classical_problem.detype_classical_prob\<close>). The type hierarchy is compiled away into
  unary predicates: each type \<open>t\<close> gains a predicate \<open>type_t\<close>, every parameter's declared type
  becomes a \<open>type_t ?x\<close> precondition guard, and the supertype closure of each constant/object is
  asserted in the initial state --- so \<open>batmobile\<close>, being both a \<open>Car\<close> and a \<open>Train\<close>, gets both
  chains, and the circular \<open>R\<close>/\<open>L\<close> pair contributes nothing.\<close>
definition "my_P2 \<equiv> ast_classical_problem.detype_classical_prob my_problem"
value "my_P2"

text \<open>\<^bold>\<open>Stage 2 --- goal normalization\<close> (\<open>P3\<close>, \<^const>\<open>ast_classical_problem.degoal_prob\<close>). The
  goal formula becomes the precondition of one fresh nullary \<open>Goal\<close> action whose effect is a fresh
  nullary \<open>Goal\<close> atom, and that atom is the new goal. The problem's objects are absorbed into the
  domain's constants (\<open>consts = objects @ consts\<close>, \<open>objects = []\<close>), so the domain becomes
  self-contained from here on.\<close>
definition "my_P3 \<equiv> ast_classical_problem.degoal_prob my_P2"
value "my_P3"

text \<open>\<^bold>\<open>Stage 3 --- definedness normalization\<close> (the pipeline's \<open>P\<^sub>X\<close>,
  \<^const>\<open>ast_classical_problem.explicate_def_prob\<close>): every numeric-fluent read is made explicitly
  conditional on that fluent being defined. With \<^const>\<open>my_funcs\<close> empty there is nothing to guard,
  so this stage passes the problem through unchanged.\<close>
definition "my_P\<^sub>X \<equiv> ast_classical_problem.explicate_def_prob my_P3"
value "my_P\<^sub>X"

text \<open>\<^bold>\<open>Stage 4 --- precondition normalization\<close> (\<open>P4\<close>,
  \<^const>\<open>ast_classical_problem.split_prob\<close>). Preconditions are brought into DNF and each disjunct
  becomes its \<^emph>\<open>own\<close> action schema, so every schema's precondition is a plain conjunction.
  \<open>drive\<close>'s \<open>road from to \<or> road to from\<close> thus splits into two \<open>drive\<close> copies (and \<open>choochoo\<close>
  likewise over \<open>rails\<close>) --- this is the copy index that later prefixes each grounded action name.\<close>
definition "my_P\<^sub>N \<equiv> ast_classical_problem.split_prob my_P\<^sub>X"
value "my_P\<^sub>N"

text \<open>\<^bold>\<open>Stage 5 --- definedness translation\<close> (\<^const>\<open>ast_classical_problem.def_translate_prob\<close>),
  yielding the fully normalized \<open>P\<^sub>T\<close>: the definedness conditions of stage 3 are compiled into
  ordinary propositional \<open>def(f, ...)\<close> predicates, which is what keeps the reachability datalog
  numeric-free. Another no-op here for want of functions. The last \<^const>\<open>value\<close> probe confirms the
  composed \<^const>\<open>ast_classical_problem.P\<^sub>T\<close> is exactly the stage-by-stage chain above.\<close>
definition "my_P\<^sub>T \<equiv> ast_classical_problem.P\<^sub>T my_problem"
value "my_P\<^sub>T"
value "my_P\<^sub>T = ast_classical_problem.def_translate_prob my_P\<^sub>N"

text \<open>\<^bold>\<open>Relaxation\<close> (\<^const>\<open>ast_classical_problem.relax_prob\<close>): the delete-relaxed
  over-approximation \<open>P\<^sub>R\<close>, on which the monotone reachability datalog runs --- delete lists are
  dropped and negative preconditions relaxed away (visible on \<open>lay_tracks\<close> were it in
  \<^const>\<open>my_actions\<close>). Grounding itself targets \<open>P\<^sub>T\<close>, i.e.\ the problem \<^emph>\<open>with\<close> its real deletes;
  \<open>P\<^sub>R\<close> only supplies the reachable-fact/operator over-approximation.\<close>
definition "my_P\<^sub>R \<equiv> ast_classical_problem.relax_prob my_P\<^sub>T"
value "my_P\<^sub>R"

subsection \<open>Executability probes (datalog program extraction)\<close>

value "ast_classical_problem.a_clauses my_P\<^sub>R"
value "ast_classical_problem.init' my_P\<^sub>R"
value "dl_program_of my_problem"

text \<open>Codegen probe for the grounding half (dummy empty model + certificate): the DFS-founded,
  error-reporting \<^const>\<open>ground_via_cert_prop_dfs_e\<close> with a trivial oracle must reduce to
  \<^const>\<open>Inl\<close> of a diagnostic (the empty certificate fails \<^const>\<open>dl_certified_model_dfs\<close> /
  \<^const>\<open>grounding_checks_exec\<close>, i.e.\ fails closed), and the grounder must itself be
  code-generable.\<close>
value "ground_via_cert_prop_dfs_e (\<lambda>_. ([], DLCert [])) my_problem"

subsection \<open>Grounding via a generated certificate\<close>

text \<open>An executable \<^emph>\<open>untrusted\<close> reference oracle (the in-Isabelle analogue of \<open>nemo_driver.sml\<close>):
  naive datalog saturation of the relaxed problem's datalog program \<^term>\<open>dl_rules R\<close>, returning the
  generic \<open>(M, dc)\<close> pair --- the derived model \<open>M\<close> and a \<^typ>\<open>(predicate, object) dl_certificate\<close>
  recording, for each derived fact, the body facts that justify it. Nothing here is trusted ---
  \<^const>\<open>ground_via_cert_prop_dfs_e\<close> re-checks the result via \<^const>\<open>dl_certified_model_dfs\<close> +
  \<^const>\<open>grounding_checks_exec\<close>. The construction makes the checks hold: each round fires every
  clause of \<^term>\<open>dl_rules R\<close> at every \<^const>\<open>cls_substs\<close> universe substitution whose ground body is
  already derived and whose guards hold, appending the new heads with their body facts; bodyless
  (init) clauses fire first, so every rule's body lies among strictly-earlier heads (foundedness),
  every node is an actual clause instance (rule validity), and saturating to a fixpoint gives
  closure --- exactly the obligations of \<^const>\<open>dl_certified_model_dfs\<close>.\<close>

definition naive_round where
  "naive_round R ns \<equiv>
     foldl (\<lambda>ns' cl.
       foldl (\<lambda>ns'' \<sigma>.
          (let fs = map fst ns'';
               body = map (subst_atom \<sigma>) (cls_body_atoms cl);
               head = subst_atom \<sigma> (the_lh cl)
           in if set body \<subseteq> set fs
                 \<and> (\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
                 \<and> head \<notin> set fs
              then ns'' @ [(head, body)]
              else ns''))
         ns' (cls_substs (ast_classical_problem.const_names R) cl))
       ns (dl_rules R)"

fun naive_sat where
  "naive_sat R 0 ns = ns"
| "naive_sat R (Suc n) ns =
     (let ns' = naive_round R ns
      in if length ns' = length ns then ns else naive_sat R n ns')"

definition naive_cert where
  "naive_cert R \<equiv>
     (let ns = naive_sat R 1000 []
      in (map fst ns, DLCert (map (\<lambda>(h, b). DLRule h b) ns)))"

definition "my_cert \<equiv> naive_cert my_P\<^sub>R"
definition "my_dl_rules \<equiv> dl_rules my_P\<^sub>R"
definition "my_const_names \<equiv> ast_classical_problem.const_names my_P\<^sub>R"
value "my_cert"
value "my_dl_rules"
value "dl_certified_model_dfs my_dl_rules my_const_names (fst my_cert) (snd my_cert)"
value "dl_acyclic_dfs (snd my_cert)"

text \<open>The \<^emph>\<open>ordered-scan\<close> alternative to the per-vertex DFS foundedness: \<^const>\<open>dl_founded_exec\<close>
  validates foundedness by scanning the certificate rules \<^emph>\<open>in list order\<close> --- the topological order
  the Nemo oracle emits, and the derivation order \<^const>\<open>naive_cert\<close> produces here (each rule is
  \<open>@\<close>-appended only once its body is already derived) --- checking each rule's body precedes its head.
  \<^const>\<open>dl_certified_model_exec\<close> therefore accepts the \<^emph>\<open>same\<close> certificate as the DFS
  \<^const>\<open>dl_certified_model_dfs\<close> above (both \<^const>\<open>True\<close>), but in \<open>O(|rules| \<cdot> |body| \<cdot> |facts|)\<close>
  rather than the per-vertex DFS's \<open>O(|facts|\<^sup>2)\<close>.\<close>
value "dl_founded_exec (snd my_cert)"
value "dl_certified_model_exec my_dl_rules my_const_names (fst my_cert) (snd my_cert)"
value "grounding_checks_exec my_P\<^sub>T (fst my_cert)"

value "my_P\<^sub>T"

text \<open>The fully grounded problem: first the raw nullary propositional PDDL (\<^const>\<open>ground_by_cert\<close>),
  then via the guarded DFS-founded, error-monad entry point \<^const>\<open>ground_via_cert_prop_dfs_e\<close> --- an
  \<^const>\<open>Inl\<close> diagnostic would mean the certificate failed the kernel re-checks, while \<^const>\<open>Inr\<close>
  carries the grounded PDDL problem.\<close>
value "ground_by_cert my_problem (fst my_cert)"
definition "my_grounded \<equiv> ground_via_cert_prop_dfs_e (\<lambda>_. my_cert) my_problem"
value "my_grounded"

text \<open>The grounded problem's components, projected out of the \<^const>\<open>Inr\<close> with \<^const>\<open>map_sum\<close> (an
  \<^const>\<open>Inl\<close> diagnostic would pass through unchanged) --- the propositional counterpart of the
  numeric twin's probe. Where the numeric grounder \<^emph>\<open>keeps\<close> object-carrying atoms (\<open>at c1 A\<close>, arity
  2), the propositional grounder turns every reachable ground fact into its \<^bold>\<open>own nullary\<close>
  predicate: \<open>fact_names\<close> names fact \<open>i\<close> by its readable encoding --- the original predicate name
  with the argument objects appended --- plus the position index \<open>i\<close> as a trailing \<open>_i\<close> suffix
  (\<open>at_c1_rooma_7\<close>), and \<open>ground_fmla\<close> rewrites each ground atom to \<open>predAtm name []\<close>.
  So the predicate list below is one nullary \<open>PredDecl\<close> per reachable
  fact, and the grounded domain keeps no types, no constants and no objects whatsoever.\<close>
value "map_sum id (\<lambda>P. predicates (ast_problem.domain P)) my_grounded"

text \<open>The grounded action schemas: one nullary schema per certified-reachable operator, its
  precondition and effect referring to those nullary fact predicates only. The names carry the
  splitting copy index, the schema name, its arguments and a disambiguating counter.\<close>
value "map_sum id (\<lambda>P. actions (ast_problem.domain P)) my_grounded"

text \<open>Initial state and goal after grounding --- both nullary atom lists over the same fact
  predicates; the goal is the single \<open>Goal\<close> atom introduced by stage 2 above.\<close>
value "map_sum id (\<lambda>P. init P) my_grounded"
value "map_sum id (\<lambda>P. goal P) my_grounded"

text \<open>The residue of the erased typing: the grounded domain's types, constants and objects are all
  empty (all three \<^const>\<open>True\<close>), which is exactly what makes the result a purely propositional
  task, ready for the STRIPS conversion.\<close>
value "map_sum id (\<lambda>P. (types (ast_problem.domain P) = [],
                        consts (ast_problem.domain P) = [],
                        objects P = [])) my_grounded"

subsection \<open>The real (untrusted) oracle: Nemo via the SML driver\<close>

text \<open>The \<open>naive_cert\<close> oracle above is an in-Isabelle reference saturation. In the deployed planner
  the model+certificate \<open>(M, dc)\<close> come instead from an external solver (Nemo) through
  \<open>nemo_driver.sml\<close> in the top-level \<open>SMLCodebase/\<close>, which emits the same generic
  \<^typ>\<open>(predicate, object) dl_certificate\<close>; the verified \<^const>\<open>dl_certified_model_dfs\<close> re-check
  inside \<^const>\<open>ground_via_cert_prop_dfs_e\<close> makes that path fail closed. The compiled
  \<open>SMLCodebase/bin/pddl_ground_planner_dfs\<close> runs the whole chain (Nemo \<open>\<rightarrow>\<close> verified kernel \<open>\<rightarrow>\<close>
  grounder \<open>\<rightarrow>\<close> SAT \<open>\<rightarrow>\<close> plan reconstruction) via its \<open>plan\<close> subcommand, and grounds a numeric task via
  \<open>ground\<close>; by \<open>plan_by_cert_dfs_sound\<close> any plan it prints is verified-valid.\<close>

end

