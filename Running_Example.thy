theory Running_Example
  imports Main
    Grounding_Pipeline_Numeric
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
    [(Var STR ''c'', Either [STR ''Car'']), (Var STR ''from'', Either [STR ''City'']), (Var STR ''to'', Either [STR ''City''])])
  (SimpleActionBody
    (And (Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''c''), term.VAR (Var STR ''from'')]))
       (Or (Atom (predAtm (Pred STR ''road'') [term.VAR (Var STR ''from''), term.VAR (Var STR ''to'')]))
           (Atom (predAtm (Pred STR ''road'') [term.VAR (Var STR ''to''), term.VAR (Var STR ''from'')]))))
    (Effect
      [Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''c''), term.VAR (Var STR ''to'')])]
      [Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''c''), term.VAR (Var STR ''from'')])] []))"
definition "op_choochoo \<equiv> SimpleActionSchema
  (ActionHead STR ''choochoo''
    [(Var STR ''t'', Either [STR ''Train'']), (Var STR ''from'', Either [STR ''City'']), (Var STR ''to'', Either [STR ''City''])])
  (SimpleActionBody
    (And (Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''t''), term.VAR (Var STR ''from'')]))
       (Or (Atom (predAtm (Pred STR ''rails'') [term.VAR (Var STR ''from''), term.VAR (Var STR ''to'')]))
           (Atom (predAtm (Pred STR ''rails'') [term.VAR (Var STR ''to''), term.VAR (Var STR ''from'')]))))
    (Effect
      [Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''t''), term.VAR (Var STR ''to'')])]
      [Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''t''), term.VAR (Var STR ''from'')])] []))"
(* into has to be Car/Train instead of Vehicle because of the definition of the predicate "in" *)
definition "op_load \<equiv> SimpleActionSchema
  (ActionHead STR ''load''
    [(Var STR ''what'', Either [STR ''Parcel'']), (Var STR ''where'', Either [STR ''City'']), (Var STR ''into'', Either [STR ''Car'', STR ''Train''])])
  (SimpleActionBody
     (And (Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''into''), term.VAR (Var STR ''where'')]))
         (Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''what''), term.VAR (Var STR ''where'')])))
    (Effect
      [Atom (predAtm (Pred STR ''in'') [term.VAR (Var STR ''what''), term.VAR (Var STR ''into'')])]
      [Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''what''), term.VAR (Var STR ''where'')])] []))"
definition "op_unload \<equiv> SimpleActionSchema
  (ActionHead STR ''unload''
    [(Var STR ''what'', Either [STR ''Parcel'']), (Var STR ''from'', Either [STR ''Car'', STR ''Train'']), (Var STR ''where'', Either [STR ''City''])])
  (SimpleActionBody
     (And (Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''from''), term.VAR (Var STR ''where'')]))
         (Atom (predAtm (Pred STR ''in'') [term.VAR (Var STR ''what''), term.VAR (Var STR ''from'')])))
    (Effect
      [Atom (predAtm (Pred STR ''at'') [term.VAR (Var STR ''what''), term.VAR (Var STR ''where'')])]
      [Atom (predAtm (Pred STR ''in'') [term.VAR (Var STR ''what''), term.VAR (Var STR ''from'')])] []))"
(* btw, this is considered well-formed as long as x is not used in precondition or effects *)
definition "op_broken \<equiv> SimpleActionSchema
  (ActionHead STR ''broken''
    [(Var STR ''x'', Either [STR ''n'existe pas''])])
  (SimpleActionBody \<bottom> (Effect [] [] []))"
(* This operator is only there to demonstrate relaxation of action preconditions, since I couldn't think of anything
  better that would make use of negative preconditions.*)
definition "op_build_tracks \<equiv> SimpleActionSchema
  (ActionHead STR ''lay_tracks''
    [(Var STR ''from'', Either [STR ''City'']), (Var STR ''to'', Either [STR ''City''])])
  (SimpleActionBody
    (And (Not (Atom (predAtm (Pred STR ''rails'') [term.VAR (Var STR ''from''), term.VAR (Var STR ''to'')])))
         (Not (Atom (predAtm (Pred STR ''rails'') [term.VAR (Var STR ''to''), term.VAR (Var STR ''from'')]))))
    (Effect [Atom (predAtm (Pred STR ''rails'') [term.VAR (Var STR ''from''), term.VAR (Var STR ''to'')])] [] []))"

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


subsection \<open>Pipeline normalization to \<open>P\<^sub>T\<close>\<close>

text \<open>The verified grounding pipeline normalizes via
  detype \<rightarrow> degoal \<rightarrow> explicate-definedness \<rightarrow> split \<rightarrow> def-translate.
  Since this problem has no numeric functions, the definedness steps are essentially identity.\<close>

declare ast_classical_problem.P\<^sub>X_def [code]
declare ast_classical_problem.P\<^sub>N_def [code]
declare ast_classical_problem.P\<^sub>T_def [code]

text \<open>--- Code setup (to move to Base/Code_Setup.thy) ---
  The pipeline's normalization functions live in the shared \<open>domain_signature\<close>/
  \<open>problem_signature\<close> locales, which FPS also instantiates at its record-based
  continuous/temporal problem types. Those per-interpretation code equations pattern-match
  on field selectors (e.g. \<open>predicates ?d\<close>) and are not valid code equations, poisoning the
  shared constant. Drop all code equations for each affected constant and re-add only the
  clean foundational (field-variable) equation.\<close>
declare [[code drop:
  domain_signature.detyped_predicates domain_signature.detyped_consts
  domain_signature.detyped_functions problem_signature.detyped_objs
  domain_signature.param_precond
  domain_signature.def_prefix domain_signature.detype_simple_action_body]]
declare domain_signature.detyped_predicates_def[code]
declare domain_signature.detyped_consts_def[code]
declare domain_signature.detyped_functions_def[code]
declare problem_signature.detyped_objs_def[code]
declare domain_signature.param_precond_def[code]
declare domain_signature.def_prefix_def[code]
declare domain_signature.detype_simple_action_body.simps[code]

text \<open>Missing executable equations: def_translate code bundle + lifted string ops.\<close>
declare ast_classical_domain.def_translate_dom_def[code]
declare ast_classical_problem.def_translate_prob_def[code]
lemma padl_lit_code[code]: "padl_lit n s = String.implode (padl n (String.explode s))"
  by (metis padl_lit.rep_eq String.implode_explode_eq)
declare distinct_strings_lit_eq[code]

definition "my_P\<^sub>T \<equiv> ast_classical_problem.P\<^sub>T my_problem"
value "my_P\<^sub>T"

definition "my_P\<^sub>R \<equiv> ast_classical_problem.relax_prob my_P\<^sub>T"
value "my_P\<^sub>R"

subsection \<open>Reachability / grounding by certification (next step)\<close>

text \<open>\<open>my_P\<^sub>R\<close> (above) is the normalized, delete-relaxed problem fed to the certification step.
  The executable oracle \<open>ast_classical_problem.semi_naive_eval my_P\<^sub>R\<close> is \<^emph>\<open>not\<close> code-runnable:
  its \<open>valuation\<close> drags in \<open>numeric_expression_valuation \<rightarrow> sin \<rightarrow> suminf \<rightarrow> Inf [filter]\<close>
  (a wellsortedness error \<open>filter :: enum\<close>), even though this numeric-free problem never takes
  those paths. The certificate route side-steps this: \<open>pddl_datalog.closure_check\<close> /
  \<open>admissible\<close> validate a (Nemo \<open>ograph\<close>) certificate against the action clauses and facts of
  \<open>my_P\<^sub>R\<close> directly, without the numeric \<open>valuation\<close>. Next: emit the datalog program for
  \<open>my_P\<^sub>R\<close>, run Nemo, parse the certificate, and \<open>by eval\<close> the checks, then
  \<open>grounder.ground_prob my_P\<^sub>T (cert_facts_of \<dots>) (cert_ops_of \<dots>)\<close>. See
  \<open>WIP_running_example_certification.md\<close>.\<close>

end

