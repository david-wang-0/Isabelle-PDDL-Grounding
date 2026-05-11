theory Running_Example
  imports Main
    Grounding_Pipeline
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


subsection \<open> Type normalization \<close>

(* 
lemma "ast_domain.restrict_dom my_domain" by eval *)

(* Type system shenanigans *)
value "of_type_x my_domain (Either []) (Either [])"
value "of_type_x my_domain (Either []) (Either [STR ''FOO''])" (* even though FOO doesn't exist *)
value "of_type_x my_domain (Either [STR ''FOO'', STR ''BAR'']) (Either [STR ''BAR'', STR ''FOO''])" (* even though both don't exist *)
value "of_type_x my_domain (Either [STR ''R'']) (Either [STR ''object''])"
(* 
declare ast_domain.constT_def [code]
declare ast_problem.objT_def [code] *)

(* value "ast_domain.is_of_type' (ast_problem.objT my_problem)
  (ast_domain.STG my_domain) (Obj STR ''c1'') (Either [STR ''Car'', STR ''FOO''])" *) (* even though FOO doesn't exist *)

(* type normalization testing *)
definition "my_type_names \<equiv> ast_domain.type_names my_domain"
value "showvals (reachable_nodes my_types) my_type_names"
value "ast_domain.type_preds my_domain"
value "ast_domain.supertype_facts_for my_domain (my_objs ! 1)"
value "ast_domain.type_precond my_domain (Var STR ''into'', Either [STR ''Car'', STR ''Train''])"
value "ast_domain.detype_ac my_domain op_load"
value "detype_preds my_preds"

definition "my_dom_detyped \<equiv> ast_domain.detype_dom my_domain"
value "my_dom_detyped"
definition "my_prob_detyped \<equiv> ast_problem.detype_prob my_problem"
value "my_prob_detyped" (* Important *)

(* also follows from restr_problem2.detype_prob_wf *)
lemma wf_p2: "ast_problem.wf_problem my_prob_detyped"
  by (intro wf_problem_intro) eval

value "enab_exec_x my_prob_detyped
  (my_plan ! 0) (ast_problem.I my_prob_detyped)"

lemma "ast_problem.valid_plan my_prob_detyped my_plan"
  by (intro valid_plan_intro[OF wf_p2]) eval

subsection \<open> Goal normalization \<close>

definition "my_dom_degoaled \<equiv> ast_problem.degoal_dom my_prob_detyped"
definition "my_prob_degoaled \<equiv> ast_problem.degoal_prob my_prob_detyped"
value "my_prob_degoaled" (* Important *)
lemma wf_p3: "ast_problem.wf_problem my_prob_degoaled"
  by (intro wf_problem_intro) eval

definition "my_plan_2 \<equiv> my_plan @ [ast_domain.\<pi>\<^sub>g my_dom_detyped]"
value my_plan_2
value "valid_plan_x my_prob_degoaled my_plan" (* missing goal planaction *)
lemma "ast_problem.valid_plan my_prob_degoaled my_plan_2"
  by (intro valid_plan_intro[OF wf_p3]) eval

subsection \<open> Precondition normalization \<close>

value "ast_domain.split_pre_pad my_dom_degoaled"
value "ast_domain.split_ac_names my_dom_degoaled op_drive"
value "ast_domain.split_ac my_dom_degoaled op_drive"
value "ast_domain.split_acs my_dom_degoaled"
definition "my_dom_split \<equiv> ast_domain.split_dom my_dom_degoaled"
definition "my_prob_split \<equiv> ast_problem.split_prob my_prob_degoaled"
value "my_dom_split"
value "my_prob_split" (* Important *)
lemma wf_p4: "ast_problem.wf_problem my_prob_split"
  by (intro wf_problem_intro) eval

(* A little manual labor to decide which one of the split actions
  corresponds to which step in the original plan. *)
definition "my_plan_3 \<equiv> [
  SimplePlanAction STR ''0drive'' [Obj STR ''c1'', Obj STR ''A'', Obj STR ''D''],
  SimplePlanAction STR ''1drive'' [Obj STR ''c1'', Obj STR ''D'', Obj STR ''C''],
  SimplePlanAction STR ''0load'' [Obj STR ''p1'', Obj STR ''C'', Obj STR ''c1''],
  SimplePlanAction STR ''0drive'' [Obj STR ''c1'', Obj STR ''C'', Obj STR ''D''],
  SimplePlanAction STR ''0unload'' [Obj STR ''p1'', Obj STR ''c1'', Obj STR ''D''],  
  SimplePlanAction STR ''1choochoo'' [Obj STR ''t'', Obj STR ''E'', Obj STR ''D''],
  SimplePlanAction STR ''1load'' [Obj STR ''p1'', Obj STR ''D'', Obj STR ''t''],  
  SimplePlanAction STR ''0choochoo'' [Obj STR ''t'', Obj STR ''D'', Obj STR ''E''],
  SimplePlanAction STR ''1unload'' [Obj STR ''p1'', Obj STR ''t'', Obj STR ''E''],

  SimplePlanAction STR ''1drive'' [Obj STR ''c3'', Obj STR ''G'', Obj STR ''F''],
  SimplePlanAction STR ''0load'' [Obj STR ''p2'', Obj STR ''F'', Obj STR ''c3''],
  SimplePlanAction STR ''1drive'' [Obj STR ''c3'', Obj STR ''F'', Obj STR ''E''],
  SimplePlanAction STR ''0unload'' [Obj STR ''p2'', Obj STR ''c3'', Obj STR ''E''],

  SimplePlanAction STR ''0load'' [Obj STR ''p1'', Obj STR ''E'', Obj STR ''c3''],
  SimplePlanAction STR ''1drive'' [Obj STR ''c3'', Obj STR ''E'', Obj STR ''G''],
  SimplePlanAction STR ''0unload'' [Obj STR ''p1'', Obj STR ''c3'', Obj STR ''G''],

  SimplePlanAction STR ''0Goal_____'' []
]"

(* SimplePlanAction STR ''choochoo'' [Obj STR ''batmobile'', Obj STR ''D'', Obj STR ''E''],
  SimplePlanAction STR ''drive'' [Obj STR ''batmobile'', Obj STR ''E'', Obj STR ''G''] *)

(* if you choose the wrong plan action at one point, this tells you where *)
value "valid_plan_x my_prob_split my_plan_3"

value "enab_exec_x my_prob_split
  (my_plan_3 ! 0) (ast_problem.I my_prob_split)"
lemma "ast_problem.valid_plan my_prob_split my_plan_3"
  by (intro valid_plan_intro[OF wf_p4]) eval

(* And this is how you would reconstruct the original plan from a plan obtained for the normalized
instance: *)

definition "restored_plan \<equiv>
  let p2 = ast_domain.restore_plan_split my_dom_degoaled my_plan_3 in
  ast_domain.restore_plan_degoal my_dom_detyped p2"
value "restored_plan" (* important *)
lemma "ast_problem.valid_plan my_problem restored_plan"
  by (intro valid_plan_intro[OF wf_p1]) eval

subsection \<open> PDDL Relaxation \<close>
(* The only action with impacted preconditions is op_build_tracks,
  which I removed because that one blows up grounding. *)
value "actions (my_dom_split) ! 8"
value "relax_ac (actions (my_dom_split) ! 8)"

definition "my_dom_relaxed \<equiv> ast_domain.relax_dom my_dom_split"
definition "my_prob_relaxed \<equiv> ast_problem.relax_prob my_prob_split"
value my_prob_relaxed (* Important *)
lemma wf_p5: "ast_problem.wf_problem my_prob_relaxed"
  by (intro wf_problem_intro) eval

(* note that a plan is still valid after relaxation *)
lemma "ast_problem.valid_plan my_prob_relaxed my_plan_3"
  by (intro valid_plan_intro[OF wf_p5]) eval

subsection \<open>Reachability Analysis\<close>

definition "my_prob_reachables \<equiv> ast_problem.semi_naive_eval my_prob_relaxed"
value "my_prob_reachables" (* takes a minute *)

value "ast_problem.all_derivs_of my_prob_relaxed
  (as_atom STR ''at'' [Obj STR ''c1'', Obj STR ''A''])
  (organize_facts (ast_problem.init' my_prob_relaxed))
  (as_action_clause (actions my_dom_relaxed ! 1))"

subsection \<open>Grounding\<close>

(* "P\<^sub>G \<equiv> grounder.ground_prob my_prob_split g_facts g_ops" *)

definition PG ("\<Pi>\<^sub>G") where "PG \<equiv> let reach = my_prob_reachables in
  grounder.ground_prob my_prob_split
  (snd reach) (fst reach)"

value "length (fst my_prob_reachables)"

value "\<Pi>\<^sub>G" (* takes a minute *)

(* TO STRIPS *)

definition P\<^sub>S ("\<Pi>\<^sub>S") where "P\<^sub>S \<equiv> ast_problem.as_strips \<Pi>\<^sub>G"
value "\<Pi>\<^sub>S" (* takes a minute *)
value "map (\<lambda>x. (x, initial_of \<Pi>\<^sub>S x)) (variables_of \<Pi>\<^sub>S)"
value "map (\<lambda>x. (x, goal_of \<Pi>\<^sub>S x)) (variables_of \<Pi>\<^sub>S)"

end
