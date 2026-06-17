theory Reachability_Analysis
  imports Tree_Decomp_Grounding_Common.PDDL_Sema_Supplement
    Tree_Decomp_Grounding_Common.Normalization_Definitions
    Tree_Decomp_Grounding_Common.Formula_Utils
    Tree_Decomp_Grounding_Common.Graph_Funs
    Tree_Decomp_Grounding_Common.String_Utils
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
\<close>

text \<open>This theory keeps only the \<^emph>\<open>shared\<close> PDDL \<rightarrow> datalog infrastructure that the certificate
  development (\<open>PDDL_Reachability_Locales\<close> / \<open>PDDL_Reachability_Analysis\<close>) builds on: the
  action-clause view of a schema (\<open>as_action_clause\<close>, \<open>consequence_of\<close>), the
  fact-store helpers (\<open>organize_facts\<close> / \<open>in_orga\<close>), and the per-problem clause/fact
  lists (\<open>a_clauses\<close>, \<open>init'\<close>).

  The retired, untrusted \<open>semi_naive_eval\<close> forward-chaining engine (and its instantiation
  helpers, the example problem, and the unproven \<open>found_facts_achievable\<close> /
  \<open>found_pactions_applicable\<close> soundness statements) has been removed. Its generic, PDDL-free
  replacement is the verified evaluator \<open>Datalog_Evaluation\<close> in the \<open>Datalog_Certification\<close>
  session: the reachability oracle runs on the translated datalog program, and the certificate
  checker validates its output.\<close>

type_synonym fact_orga = "predicate \<Rightarrow> object list list"

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

(* instantiating action clauses *)
abbreviation "satisfies_cond params args c \<equiv>
  valuation ({}, Map.empty) \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst params args) c"
abbreviation satisfies_conds where
  "satisfies_conds params conds args \<equiv>
    list_all (satisfies_cond params args) conds"
fun consequence_of where "consequence_of (AClause n params preds cond add) args =
  map (map_atom_fmla (ac_tsubst params args)) add"

context ast_classical_problem begin

definition "a_clauses \<equiv> map as_action_clause (actions D)"
definition "fact_clauses \<equiv> filter (\<lambda>c. cl_pred_pre c = []) a_clauses"
abbreviation "const_names \<equiv> map fst all_consts"

(* set of initial facts, considering some clauses may have an empty body... *)
(* all possible parameterizations for a fact (corresponds to level 6) *)
fun all_fact_paramz :: "action_clause \<Rightarrow> object list list" where
  "all_fact_paramz (AClause n params preds cond add) =
    all_combos (satisfies_conds params cond) (replicate (length params) const_names)"
abbreviation all_fact_consqs where
  "all_fact_consqs r \<equiv> concat (map (consequence_of r) (all_fact_paramz r))"
definition "pseudo_init \<equiv> concat (map all_fact_consqs fact_clauses)"
definition "init' \<equiv> conc_unique pseudo_init (init P)"

end

lemmas pseudo_datalog_code =
  subst_term.simps (* TODO move*)
  ast_classical_problem.a_clauses_def
  ast_classical_problem.fact_clauses_def
  ast_classical_problem.all_fact_paramz.simps
  ast_classical_problem.pseudo_init_def
  ast_classical_problem.init'_def

declare pseudo_datalog_code[code]

subsection \<open> Proofs \<close>

lemma "set (un_and xs) = set (pos_lits_of xs) \<union> set (cond_lits_of xs)"
  unfolding pos_lits_of_def cond_lits_of_def
  apply (induction "un_and xs") apply simp
  by auto


end
