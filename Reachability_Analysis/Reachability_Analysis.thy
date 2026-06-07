theory Reachability_Analysis
  imports Tree_Decomp_Grounding_Base.PDDL_Sema_Supplement
    Tree_Decomp_Grounding_Base.Normalization_Definitions
    Tree_Decomp_Grounding_Base.Formula_Utils
    Tree_Decomp_Grounding_Base.Graph_Funs
    Tree_Decomp_Grounding_Base.String_Utils
    (*"AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker"*)
begin


text \<open>
Here, reachability analysis is performed directly on the PDDL problem data structure, instead of
first converting it to Datalog.

The input problem is assumed to be:
  - well-formed: duh
  - normalized: preconditions and goals must be pure conjunctions, and we don't want to deal with
    the type system here.
  - relaxed: there are no negative literals in precondition clauses
    TODO: re-evaluate if the structure of the goal really matters here...
\<close>

type_synonym fact_orga = "predicate \<Rightarrow> object list list"
type_synonym partial_args = "variable \<rightharpoonup> object"

datatype action_clause = AClause
  (cl_name: name)
  (cl_params: "(variable \<times> type) list")
  (cl_pred_pre: "term atom formula list")
  (cl_cond_pre: "term atom formula list")
  (cl_pos: "term atom formula list")

definition pos_lits_of :: "'a atom formula \<Rightarrow> 'a atom formula list" where
  "pos_lits_of F = filter is_predAtom (un_and F)"
definition cond_lits_of :: "'a atom formula \<Rightarrow> 'a atom formula list" where
  "cond_lits_of F = filter (HOL.Not \<circ> is_predAtom) (un_and F)"


(* TODO: add action predicate to a? *)
fun as_action_clause :: "ast_classical_action_schema \<Rightarrow> action_clause" where
  "as_action_clause (SimpleActionSchema (ActionHead n params) (SimpleActionBody pre (Effect a d ne))) =
    AClause n params (pos_lits_of pre) (cond_lits_of pre) a"

(* fact_orga functionality *)
fun update_facts :: "object atom formula list \<Rightarrow> fact_orga \<Rightarrow> fact_orga" where
  "update_facts [] orga = orga" |
  "update_facts (Atom (predAtm p args) # fs) orga =
    (let orga' = update_facts fs orga in
    orga'(p := args # orga' p))" |
  "update_facts (_ # fs) orga = undefined" (* not pred atom *)
abbreviation organize_facts :: "object atom formula list \<Rightarrow> fact_orga" where
  "organize_facts fs \<equiv> update_facts fs (\<lambda>p. [])"
fun in_orga :: "object atom formula \<Rightarrow> fact_orga \<Rightarrow> bool" where
  "in_orga (Atom (predAtm p args)) orga \<longleftrightarrow> args \<in> set (orga p)" |
  "in_orga _ orga \<longleftrightarrow> undefined" (* not pred atom *)
definition (in ast_classical_problem) enumerate_orga :: "fact_orga \<Rightarrow> object atom formula list" where
  "enumerate_orga facts = [Atom (predAtm (pred p) args). p \<leftarrow> predicates D, args \<leftarrow> facts (pred p)]"

(* partial_args functionality *)
fun fix_to :: "object list \<Rightarrow> term list \<Rightarrow> partial_args \<Rightarrow> partial_args option" where
  "fix_to [] [] args = Some args" |
  "fix_to (obj # objs) (term.CONST x # ts) args = (if obj = x then fix_to objs ts args else None)" |
  "fix_to (obj # objs) (term.VAR x # ts) args = (case args x of
    None \<Rightarrow> fix_to objs ts (args(x \<mapsto> obj)) |
    Some y \<Rightarrow> (if y = obj then fix_to objs ts args else None))" |
  "fix_to _ _ args = undefined" (* different lengths *)

abbreviation fix_to' :: "object list \<Rightarrow> term atom formula \<Rightarrow> partial_args \<Rightarrow> partial_args option" where
  "fix_to' f c args \<equiv> fix_to f (atom.arguments (un_Atom c)) args"
abbreviation as_arg_list :: "(variable \<times> type) list \<Rightarrow> partial_args \<Rightarrow> object option list" where
  "as_arg_list vs args \<equiv> map (args \<circ> fst) vs"

(* instantiating action clauses *)
abbreviation "satisfies_cond params args c \<equiv>
  valuation ({}, Map.empty) \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst params args) c"
abbreviation satisfies_conds where
  "satisfies_conds params conds args \<equiv>
    list_all (satisfies_cond params args) conds"
fun finish_args :: "'a option list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "finish_args [] [] = []" |
  "finish_args (None # partial) (y # ys) = y # finish_args partial ys" |
  "finish_args (Some x # partial) ys = x # finish_args partial ys" |
  "finish_args _ _ = undefined" (* number of Nones does not match length of ys *)
  (* other cases for length ys \<noteq> count None xs *)
fun consequence_of where "consequence_of (AClause n params preds cond add) args =
  map (map_atom_fmla (ac_tsubst params args)) add"

context ast_classical_problem begin

definition "a_clauses \<equiv> map as_action_clause (actions D)"
definition "pred_clauses \<equiv> filter (\<lambda>c. cl_pred_pre c \<noteq> []) a_clauses"
definition "fact_clauses \<equiv> filter (\<lambda>c. cl_pred_pre c = []) a_clauses"
abbreviation "const_names \<equiv> map fst all_consts"

(* set of initial facts, considering some clauses may have an empty body... *)
(* all possible parameterizations for a fact *)
(* corresponds to level 6 *)
fun all_fact_paramz :: "action_clause \<Rightarrow> object list list" where
  "all_fact_paramz (AClause n params preds cond add) =
    all_combos (satisfies_conds params cond) (replicate (length params) const_names)"
abbreviation all_fact_consqs where
  "all_fact_consqs r \<equiv> concat (map (consequence_of r) (all_fact_paramz r))"
definition "pseudo_init \<equiv> concat (map all_fact_consqs fact_clauses)"
definition "init' \<equiv> conc_unique pseudo_init (init P)"

(* Level 6: fix list of optional args, for every satisfied finished parameterization...*)
fun all_finished_paramz :: "action_clause \<Rightarrow> object option list \<Rightarrow> object list list" where
  "all_finished_paramz (AClause n params preds cond add) partial =
    all_combos (satisfies_conds params cond \<circ> finish_args partial)
      (replicate (count_list partial None) const_names)"

(* Level 5: fix w r i j, for f \<in> facts, where f matches r!j...
  (the f chosen from 'previous' j is a fixed parameter in the recursion. Initially, it's w.)
  (i is 'integrated' into args, j is the recursive parameter)*)
fun all_insts_owa_aux
  :: "fact_orga \<Rightarrow> object list \<Rightarrow> partial_args \<Rightarrow> term atom formula list
    \<Rightarrow> partial_args list"
  where
  "all_insts_owa_aux facts f args [] = undefined" | (* should not be called on empty clauses *)
  "all_insts_owa_aux facts f args [c] = (case fix_to' f c args of
    Some a \<Rightarrow> [a] | None \<Rightarrow> [])" |
  "all_insts_owa_aux facts f args (c#c'#cs) = (case fix_to' f c args of Some a' \<Rightarrow>
    concat [all_insts_owa_aux facts f' a' (c'#cs). f' \<leftarrow> facts (unPredAtom c')] | None \<Rightarrow> [])"

(* Level 4: fix w r i, IF r!i matches w THEN for all j...
  Two checks can fail here: Either the predicate symbols of r!i and w don't match.
  Or their parameters can't be unified, i.e. when w=P(a,b) and r!i=P(x,x) *)
fun all_insts_of_with_at'' :: "object atom formula \<Rightarrow> fact_orga \<Rightarrow> action_clause \<Rightarrow> nat \<Rightarrow> partial_args list" where
  "all_insts_of_with_at'' f facts c i =
    
    (let preds = cl_pred_pre c in
      (if unPredAtom f \<noteq> unPredAtom (preds ! i) then [] else let
         f_objs = atom.arguments (un_Atom f) in
      case fix_to' f_objs (preds ! i) (\<lambda>x. None) of
        Some args\<^sub>0 \<Rightarrow> all_insts_owa_aux facts f_objs args\<^sub>0 (to_front preds i) |
        None \<Rightarrow> []))"

(* Level 4: fix w r, transform partial args into list of optional *)
fun all_insts_of_with_at' :: "object atom formula \<Rightarrow> fact_orga \<Rightarrow> action_clause \<Rightarrow> nat \<Rightarrow> object option list list" where
  "all_insts_of_with_at' f facts c i =
    (let partials = all_insts_of_with_at'' f facts c i in
    map (as_arg_list (cl_params c)) partials)"

(* Level 4: fix w r, given partial args, obtain finished args *)
fun all_insts_of_with_at :: "object atom formula \<Rightarrow> fact_orga \<Rightarrow> action_clause \<Rightarrow> nat \<Rightarrow> object list list" where
  "all_insts_of_with_at f facts c i =
    (let partials = all_insts_of_with_at' f facts c i in
    [finish_args p extra. p \<leftarrow> partials, extra \<leftarrow> all_finished_paramz c p])"

(* Level 3: fix w r, for i in range(body(r))... *)
fun all_insts_of_with :: "object atom formula \<Rightarrow> fact_orga \<Rightarrow> action_clause \<Rightarrow> object list list" where
  "all_insts_of_with f facts c = concat (map (all_insts_of_with_at f facts c) (nat_range (length (cl_pred_pre c))))"

(* Level 3: fix w r, given args, apply heads *)
fun all_derivs_of :: "object atom formula \<Rightarrow> fact_orga \<Rightarrow> action_clause \<Rightarrow>
  (ast_classical_plan_action list \<times> object atom formula list)" where
  "all_derivs_of f facts c = (let all_args = all_insts_of_with f facts c in
    (map (SimplePlanAction (cl_name c)) all_args,
    [a. args \<leftarrow> all_args, a \<leftarrow> consequence_of c args]))"

(* Level 2: fix w, for r in pred_clauses... *)
fun all_derivs where
  "all_derivs f facts = concat2 (map (all_derivs_of f facts) pred_clauses)"

(* Level 1: for w in working set... *)
function (sequential) semi_naive_aux where
  "semi_naive_aux [] facts calls = (calls, facts)" |
  "semi_naive_aux (w#works) facts calls =
    (let derivs = (all_derivs w facts);
         news = filter (\<lambda>x. \<not> in_orga x facts) (remdups (snd derivs));
         facts' = update_facts news facts;
         calls' = fst derivs @ calls in
    semi_naive_aux (works @ news) facts' calls')"
  by (pat_completeness) blast+ (* takes a few seconds *)
termination semi_naive_aux proof
  show "wf undefined" sorry
  show "\<And>w works facts calls x xa xb xc.
       x = all_derivs w facts \<Longrightarrow>
       xa = filter (\<lambda>x. \<not> in_orga x facts) (remdups (snd x)) \<Longrightarrow>
       xb = update_facts xa facts \<Longrightarrow>
       xc = fst x @ calls \<Longrightarrow> ((works @ xa, xb, xc), w # works, facts, calls) \<in> undefined"
    sorry
qed

(* ugh *)
definition "letsss w works facts \<equiv> (let derivs = all_derivs w facts;
         news = filter (\<lambda>x. \<not> in_orga x facts) (remdups (snd derivs));
         facts' = update_facts news facts in
         (works @ news, facts', w#news))"

(* nat pattern on the right because Code_Binary_Nat (which is included in PDDL_Checker) will otherwise
  break it. *)
fun semi_naive_lim where
  "semi_naive_lim n [] facts news= ([], facts, news)" |
  "semi_naive_lim m (w#works) facts news = (case m of 0 \<Rightarrow> (w#works, facts, news) |
    Suc n \<Rightarrow> (case letsss w works facts of (a, b, c) \<Rightarrow>
    semi_naive_lim n a b c))"

definition "semi_naive_eval \<equiv> case ((\<lambda>x. semi_naive_aux x (organize_facts x) []) init') of
  (pactions, facts) \<Rightarrow> (pactions, enumerate_orga facts)"

definition "semi_naive_limm n \<equiv> case semi_naive_lim n init' (organize_facts init') [] of
  (a, b, c) \<Rightarrow> (c, a, enumerate_orga b)"

end

lemmas pseudo_datalog_code =
  subst_term.simps (* TODO move*)
  ast_classical_problem.enumerate_orga_def
  ast_classical_problem.a_clauses_def
  ast_classical_problem.pred_clauses_def
  ast_classical_problem.fact_clauses_def
  ast_classical_problem.all_fact_paramz.simps
  ast_classical_problem.pseudo_init_def
  ast_classical_problem.init'_def
  ast_classical_problem.all_finished_paramz.simps
  ast_classical_problem.all_insts_owa_aux.simps
  ast_classical_problem.all_insts_of_with_at''.simps
  ast_classical_problem.all_insts_of_with_at'.simps
  ast_classical_problem.all_insts_of_with_at.simps
  ast_classical_problem.all_insts_of_with.simps
  ast_classical_problem.all_derivs_of.simps
  ast_classical_problem.all_derivs.simps
  ast_classical_problem.semi_naive_aux.simps
  ast_classical_problem.semi_naive_eval_def

  ast_classical_problem.letsss_def
  ast_classical_problem.semi_naive_lim.simps
  ast_classical_problem.semi_naive_limm_def

declare pseudo_datalog_code[code]

(* Example/test problem and \<open>value\<close> sanity checks (old-API constructors); kept for reference.
abbreviation "as_atom n args \<equiv> Atom (predAtm (Pred n) args)"
abbreviation "var n \<equiv> term.VAR (Var n)"
abbreviation "cst n \<equiv> term.CONST (Obj n)"

definition "action_move \<equiv> Action_Schema
      ''move''
      [(Var ''what'', \<omega>), (Var ''from'', \<omega>), (Var ''to'', \<omega>)]
      (as_atom ''at'' [term.VAR (Var ''what''), term.VAR (Var ''from'')] \<^bold>\<and>
        as_atom ''path'' [term.VAR (Var ''from''), term.VAR (Var ''to'')])
      (Effect [as_atom ''at'' [var ''what'', var ''to'']]
              [as_atom ''at'' [var ''what'', var ''from'']])"
definition "action_DE \<equiv> Action_Schema
      ''DE''
      [(Var ''d'', \<omega>), (Var ''e'', \<omega>), (Var ''x'', \<omega>)]
      (Atom (atom.Eq (var ''d'') (cst ''D'')) \<^bold>\<and> Atom (atom.Eq (var ''e'') (cst ''E'')))
      (Effect [as_atom ''path'' [var ''d'', var ''e'']] [])"
definition "action_omni \<equiv> Action_Schema
      ''omni''
      [(Var ''where'', \<omega>)]
      (\<^bold>\<not>(Atom (atom.Eq (var ''where'') (cst ''w''))) \<^bold>\<and>
      (\<^bold>\<not>(Atom (atom.Eq (var ''where'') (cst ''x''))) \<^bold>\<and>
      (\<^bold>\<not>(Atom (atom.Eq (var ''where'') (cst ''B''))) \<^bold>\<and>
       \<^bold>\<not>(Atom (atom.Eq (var ''where'') (cst ''y''))))))
      (Effect [as_atom ''at'' [cst ''w'', var ''where'']] [])"
definition "action_foo \<equiv> Action_Schema
      ''foo''
      [(Var ''a'', \<omega>), (Var ''b'', \<omega>)]
      (Atom (atom.Eq (var ''a'') (var ''b'')) \<^bold>\<and>
      (as_atom ''at'' [cst ''x'', var ''a'']))
      (Effect [as_atom ''foo'' [var ''a'', var ''b'']] [])"

definition my_prob ("\<Pi>") where "my_prob \<equiv> Problem
  (Domain
    []
    [PredDecl (Pred ''at'') [\<omega>, \<omega>],
     PredDecl (Pred ''path'') [\<omega>, \<omega>],
     PredDecl (Pred ''foo'') [\<omega>, \<omega>]]
    []
    [action_DE, action_omni, action_move, action_foo])
  [(Obj ''A'', \<omega>), (Obj ''B'', \<omega>), (Obj ''C'', \<omega>), (Obj ''D'', \<omega>), (Obj ''E'', \<omega>),
   (Obj ''x'', \<omega>), (Obj ''y'', \<omega>), (Obj ''w'', \<omega>)]
  [as_atom ''at'' [Obj ''x'', Obj ''A''], as_atom ''at'' [Obj ''y'', Obj ''D''],
   as_atom ''path'' [Obj ''A'', Obj ''B''], as_atom ''path'' [Obj ''B'', Obj ''C''],
   as_atom ''path'' [Obj ''C'', Obj ''A''], as_atom ''at'' [Obj ''w'', Obj ''A'']]
  \<bottom>"

fun lel :: "nat \<Rightarrow> nat" where
  "lel 0 = 0" |
  "lel (Suc n) = n + lel n"

term Suc
value "ast_problem.semi_naive_eval \<Pi>"
value "ast_problem.semi_naive_limm \<Pi> 1"
value "ast_problem.semi_naive_limm \<Pi> 2"
value "ast_problem.semi_naive_limm \<Pi> 3"
value "ast_problem.semi_naive_limm \<Pi> 40"
*)

(*
interpretation Pi: ast_problem \<Pi> done

value "Pi.all_finished_paramz (as_action_clause action_foo) [Some (Obj ''A''), None]"


value "Pi.pred_clauses"
value "Pi.fact_clauses"
value "Pi.enumerate_orga (organize_facts Pi.init')"

abbreviation (input) "facto \<equiv> (as_atom ''path'' [Obj ''A'', Obj ''B''])"
abbreviation "orga0 \<equiv> organize_facts Pi.init'"
abbreviation "clause \<equiv> as_action_clause action_move"

thm Pi.all_insts_of_with_at''.simps[of facto orga0 clause 0]
thm Pi.all_insts_owa_aux.simps
value "cl_pred_pre clause"
abbreviation "args0 \<equiv> fix_to' (atom.arguments (un_Atom facto)) ((cl_pred_pre clause) ! 0) (\<lambda>x. None)"
value "as_arg_list (cl_params clause) (the args0)"
value "Pi.all_insts_owa_aux
  orga0
  (atom.arguments (un_Atom facto))
  (the args0)
  (cl_pred_pre clause)"
value "fix_to' (atom.arguments (un_Atom facto)) ((cl_pred_pre clause) ! 0) (the args0)"

value "Pi.all_insts_of_with_at'' facto (organize_facts Pi.init') (as_action_clause action_move) 1"
value "Pi.all_insts_of_with_at' facto (organize_facts Pi.init') (as_action_clause action_move) 0"
value "Pi.all_insts_of_with_at facto (organize_facts Pi.init') (as_action_clause action_move) 0"
value "consequence_of (as_action_clause action_move) [Obj ''A'', Obj ''B'', Obj ''C'']"
value "Pi.all_insts_of_with facto (organize_facts Pi.init') (as_action_clause action_move)"
value "Pi.all_derivs_of facto (organize_facts Pi.init') (as_action_clause action_move)"
value "Pi.all_derivs (as_atom ''at'' [Obj ''x'', Obj ''B'']) (organize_facts Pi.init')"
value "Pi.enumerate_orga orga0"
value "Pi.enumerate_orga (update_facts (Pi.all_derivs facto (organize_facts Pi.init'))orga0)"
value "Pi.enumerate_orga (Pi.semi_naive_eval)"

abbreviation "d1 \<equiv> Pi.all_derivs (as_atom ''path'' [Obj ''A'', Obj ''B'']) orga0"
value d1
value "Pi.enumerate_orga (update_facts d1 orga0)" *)

subsection \<open> Proofs \<close>

lemma "set (un_and xs) = set (pos_lits_of xs) \<union> set (cond_lits_of xs)"
  unfolding pos_lits_of_def cond_lits_of_def
  apply (induction "un_and xs") apply simp
  by auto


context relaxed_problem begin

theorem found_facts_achievable:
  "set (snd semi_naive_eval) = (\<lambda>f. Atom (uncurry predAtm f)) ` {f. achievable f}"
  sorry

theorem found_pactions_applicable:
  "set (fst semi_naive_eval) = {f. applicable f}"
  sorry

end



end