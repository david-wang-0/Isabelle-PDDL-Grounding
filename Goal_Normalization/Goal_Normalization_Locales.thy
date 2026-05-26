theory Goal_Normalization_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Tree_Decomp_Grounding_Base.Normalization_Definitions
    Tree_Decomp_Grounding_Base.PDDL_Sema_Supplement
    Tree_Decomp_Grounding_Base.String_Utils
    Tree_Decomp_Grounding_Base.Grounding_Utils
    Tree_Decomp_Grounding_Base.DNF
begin

section ‹Goal Normalization Definitions and Locales›

text ‹Goal normalization replaces an arbitrary goal formula with a single
  goal-predicate atom, achieved by a fresh goal action whose precondition is
  the original goal. This file holds the definitions and the parallel ‹*3›
  locale hierarchy that relates a typed problem to its degoaled counterpart.›

subsection ‹Degoaling definitions›

context domain_signature begin

  definition "goal_pred ≡ Pred (safe_prefix pred_names + STR ''Goal'')"
  definition "goal_pred_decl ≡ PredDecl goal_pred []"

end

context ast_classical_domain begin

  abbreviation "ac_names ≡ map ac_name (actions D)"

  abbreviation "goal_ac_name ≡ safe_prefix ac_names + STR ''Goal''"

  abbreviation "goal_effect ≡ Effect [Atom (predAtm goal_pred [])] [] []"

  definition goal_ac :: "term atom formula ⇒ ast_classical_action_schema" where
    "goal_ac g =
      SimpleActionSchema (ActionHead goal_ac_name []) (SimpleActionBody g goal_effect)"
end

context ast_classical_problem begin

  definition "term_goal ≡ map_atom_fmla term.CONST (goal P)"

  definition "degoal_dom ≡
    Domain
      (types D)
      (goal_pred_decl # predicates D)
      (functions D)
      (objects P @ consts D)
      (goal_ac term_goal # actions D)"

  definition "degoal_prob ≡
    Problem
      degoal_dom
      []
      (init P)
      (Atom (predAtm goal_pred []))"
end

context ast_classical_domain begin

abbreviation "π⇩g ≡ SimplePlanAction goal_ac_name []"
abbreviation "restore_plan_degoal πs ≡ sublist_until πs π⇩g"

end

subsection ‹Selectors for the degoaled domain/problem›

text ‹Selectors used by both the locale-rewrite setup and the proofs.›

abbreviation (in ast_classical_problem) (input) "D3 ≡ degoal_dom"
abbreviation (in ast_classical_problem) (input) "P3 ≡ degoal_prob"

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

subsection ‹The ‹*3› locale hierarchy›

text ‹No ‹ast_classical_domain3›: the degoaled domain depends on the problem
  (it absorbs the problem objects into its constants), so ‹D3› is not
  available in the bare ‹ast_classical_domain› context.›

locale ast_classical_problem3 = ast_classical_problem
sublocale ast_classical_problem3 ⊆ p3: ast_classical_problem P3 .

text ‹Goal normalization runs before definedness explication in the pipeline,
  so its input has no special definedness invariant beyond well-formedness.›

locale wf_ast_classical_problem3 = wf_ast_classical_problem
sublocale wf_ast_classical_problem3 ⊆ ast_classical_problem3 .

end

