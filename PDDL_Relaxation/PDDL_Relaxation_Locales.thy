theory PDDL_Relaxation_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Tree_Decomp_Grounding_Base.Grounding_Utils
    Tree_Decomp_Grounding_Base.PDDL_Sema_Supplement
    Tree_Decomp_Grounding_Base.Formula_Utils
    Tree_Decomp_Grounding_Base.Normalization_Definitions
begin

section \<open> Relaxation Definitions and Locales \<close>

text \<open>Delete relaxation drops the delete-effects of every action and replaces both
  the action preconditions and the goal by their positive relaxation. This file holds
  the relaxation definitions, the \<open>*_rx\<close> locale hierarchy relating a domain/problem to
  its relaxed counterpart, and the basic selector lemmas.\<close>

subsection \<open> Relaxation Procedure \<close>

fun relax_eff :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "relax_eff (Effect a b ne) = Effect a [] ne"

fun relax_ac :: "ast_classical_action_schema \<Rightarrow> ast_classical_action_schema" where
  "relax_ac (SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff)) =
    SimpleActionSchema (ActionHead n params) (SimpleActionBody (relax_conj pre) (relax_eff eff))"

definition (in ast_classical_domain) "relax_dom \<equiv>
  Domain
    (types D)
    (predicates D)
    (functions D)
    (consts D)
    (map relax_ac (actions D))"

definition (in ast_classical_problem) "relax_prob \<equiv>
  Problem
    relax_dom
    (objects P)
    (init P)
    (relax_conj (goal P))"

subsection \<open> Contexts \<close>

text \<open> locale setup for simplified syntax \<close>

(* TODO replace with D\<^sup>+ and P\<^sup>+ *)
abbreviation (in ast_classical_domain) (input) "DX \<equiv> relax_dom"
abbreviation (in ast_classical_problem) (input) "PX \<equiv> relax_prob"

locale ast_classical_domain_rx = ast_classical_domain
sublocale ast_classical_domain_rx \<subseteq> dx: ast_classical_domain DX .

locale normalized_domain_rx = normalized_domain
sublocale normalized_domain_rx \<subseteq> dx: ast_classical_domain DX .
(* this is later strengthened to "dx: normed_dom DX" *)
sublocale normalized_domain_rx \<subseteq> ast_classical_domain_rx .

locale ast_classical_problem_rx = ast_classical_problem
sublocale ast_classical_problem_rx \<subseteq> px: ast_classical_problem PX .
sublocale ast_classical_problem_rx \<subseteq> ast_classical_domain_rx D .

locale normalized_problem_rx = normalized_problem
sublocale normalized_problem_rx \<subseteq> px : ast_classical_problem PX.
(* this is later strengthened to "px: normed_prob PX" *)
sublocale normalized_problem_rx \<subseteq> ast_classical_problem_rx .
sublocale normalized_problem_rx \<subseteq> normalized_domain_rx D
  by unfold_locales

subsection \<open> Alt definitions \<close>

lemma (in ast_classical_domain) relax_ac_sel[simp]:
  "ac_name (relax_ac ac) = ac_name ac"
  "ac_params (relax_ac ac) = ac_params ac"
  "ac_pre (relax_ac ac) = relax_conj (ac_pre ac)"
  "ac_eff (relax_ac ac) = relax_eff (ac_eff ac)"
  apply (cases ac rule: ast_classical_action_schema_cases_unfold; simp)
  apply (cases ac rule: ast_classical_action_schema_cases_unfold; simp)
  apply (cases ac rule: ast_classical_action_schema_cases_unfold; simp)
  apply (cases ac rule: ast_classical_action_schema_cases_unfold; simp)
  done

lemma (in ast_classical_domain) relax_eff_sel[simp]:
  "adds (relax_eff e) = adds e"
  "dels (relax_eff e) = []"
   apply (cases e; simp)
  apply (cases e; simp)
  done

lemma (in ast_classical_domain) relax_dom_sel[simp]:
  "types DX = types D"
  "predicates DX = predicates D"
  "functions DX = functions D"
  "consts DX = consts D"
  "actions DX = map relax_ac (actions D)"
  using relax_dom_def by simp_all

lemma (in ast_classical_problem) relax_prob_sel[simp]:
  "domain PX = relax_dom"
  "objects PX = objects P"
  "init PX = init P"
  "goal PX = relax_conj (goal P)"
  using relax_prob_def by simp_all

end
