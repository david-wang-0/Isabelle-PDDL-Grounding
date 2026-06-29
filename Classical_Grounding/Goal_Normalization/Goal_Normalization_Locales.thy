theory Goal_Normalization_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Grounding_Classical_Common.Normalization_Definitions
    Classical_Grounding_Utils.PDDL_Sema_Supplement
    Grounding_Utils.String_Utils
    Grounding_Utils.Grounding_Utils
    Grounding_Common.DNF
begin

section \<open>Goal Normalization Definitions and Locales\<close>

text \<open>Goal normalization replaces an arbitrary goal formula with a single
  goal-predicate atom, achieved by a fresh goal action whose precondition is
  the original goal. This file holds the definitions and the parallel \<open>*3\<close>
  locale hierarchy that relates a typed problem to its degoaled counterpart.\<close>

subsection \<open>Degoaling definitions\<close>

context domain_signature begin

  definition "goal_pred \<equiv> Pred (safe_prefix pred_names + STR ''Goal'')"
  definition "goal_pred_decl \<equiv> PredDecl goal_pred []"

end

context ast_classical_domain begin

  abbreviation "ac_names \<equiv> map ac_name (actions D)"

  abbreviation "goal_ac_name \<equiv> safe_prefix ac_names + STR ''Goal''"

  abbreviation "goal_effect \<equiv> Effect [Atom (predAtm goal_pred [])] [] []"

  definition goal_ac :: "term atom formula \<Rightarrow> ast_classical_action_schema" where
    "goal_ac g =
      SimpleActionSchema (ActionHead goal_ac_name []) (SimpleActionBody g goal_effect)"
end

context ast_classical_problem begin

  definition "term_goal \<equiv> map_atom_fmla term.CONST (goal P)"

  definition "degoal_dom \<equiv>
    Domain
      (types D)
      (goal_pred_decl # predicates D)
      (functions D)
      (objects P @ consts D)
      (goal_ac term_goal # actions D)"

  definition "degoal_prob \<equiv>
    Problem
      degoal_dom
      []
      (init P)
      (Atom (predAtm goal_pred []))"
end

context ast_classical_domain begin

abbreviation "\<pi>\<^sub>g \<equiv> SimplePlanAction goal_ac_name []"
abbreviation "restore_plan_degoal \<pi>s \<equiv> sublist_until \<pi>s \<pi>\<^sub>g"

end

subsection \<open>Selectors for the degoaled domain/problem\<close>

text \<open>Selectors used by both the locale-rewrite setup and the proofs.\<close>

abbreviation (in ast_classical_problem) (input) "D3 \<equiv> degoal_dom"
abbreviation (in ast_classical_problem) (input) "P3 \<equiv> degoal_prob"

lemma (in ast_classical_problem) degoal_dom_sel [simp]:
  "types D3 = types D"
  "predicates D3 = goal_pred_decl # predicates D"
  "functions D3 = functions D"
  "consts D3 = objects P @ consts D"
  "actions D3 = goal_ac term_goal # actions D"
  using degoal_dom_def by simp_all

lemma (in ast_classical_problem) degoal_prob_sel [simp]:
  "domain P3 = D3"
  "objects P3 = []"
  "init P3 = init P"
  "goal P3 = Atom (predAtm goal_pred [])"
  using degoal_prob_def by simp_all

subsection \<open>The \<open>*3\<close> locale hierarchy\<close>

text \<open>No \<open>ast_classical_domain3\<close>: the degoaled domain depends on the problem
  (it absorbs the problem objects into its constants), so \<open>D3\<close> is not
  available in the bare \<open>ast_classical_domain\<close> context.\<close>

locale ast_classical_problem3 = ast_classical_problem
sublocale ast_classical_problem3 \<subseteq> p3: ast_classical_problem P3 .

text \<open>Goal normalization runs before definedness explication in the pipeline,
  so its input has no special definedness invariant beyond well-formedness.\<close>

locale wf_ast_classical_problem3 = wf_ast_classical_problem
sublocale wf_ast_classical_problem3 \<subseteq> ast_classical_problem3 .

end

