theory Classical_PDDL_Relaxation_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Grounding_Utils.Grounding_Utils
    Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement
    Grounding_Common.Formula_Utils
    Grounding_Classical_Common.Classical_PDDL_Normalization Grounding_PDDL_Relaxation.PDDL_Relaxation
begin

section \<open> Relaxation Definitions and Locales \<close>

text \<open>Delete relaxation drops the delete-effects of every action and replaces both
  the action preconditions and the goal by their positive relaxation. This file holds
  the relaxation definitions, the \<open>*_rx\<close> locale hierarchy relating a domain/problem to
  its relaxed counterpart, and the basic selector lemmas.\<close>

subsection \<open> Relaxation Procedure \<close>


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
    (filter is_predAtom (init P))
    (relax_conj (goal P))"

subsection \<open> Abbreviations and selectors \<close>

text \<open> locale setup for simplified syntax \<close>

(* TODO replace with D\<^sup>+ and P\<^sup>+ *)
abbreviation (in ast_classical_domain) (input) "DX \<equiv> relax_dom"
abbreviation (in ast_classical_problem) (input) "PX \<equiv> relax_prob"

lemma (in ast_classical_domain) relax_ac_sel[simp]:
  "ac_name (relax_ac ac) = ac_name ac"
  "ac_params (relax_ac ac) = ac_params ac"
  "ac_pre (relax_ac ac) = relax_conj (ac_pre ac)"
  "ac_eff (relax_ac ac) = relax_eff (ac_eff ac)"
  by (cases ac rule: ast_classical_action_schema_cases_unfold; simp)+


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
  "init PX = filter is_predAtom (init P)"
  "goal PX = relax_conj (goal P)"
  using relax_prob_def by simp_all

subsection \<open> Contexts \<close>

text \<open>Relaxation leaves the signature (types, predicates, functions, consts, objects)
  completely untouched and only rewrites action preconditions/effects and the goal.
  Hence every signature-level constant of the relaxed domain/problem coincides with the
  original one. We fold
  these identifications into the \<open>dx\<close>/\<open>px\<close> sublocale interpretations via \<open>rewrites\<close>, so that
  e.g.\ \<open>dx.wf_fmla\<close> collapses to \<open>wf_fmla\<close> and \<open>px.resolve_classical_action_schema\<close> to
  \<open>dx.resolve_classical_action_schema\<close>. The only constants that genuinely change are the
  ones depending on the action list (\<open>resolve_classical_action_schema\<close>, \<open>wf_classical_domain\<close>,
  \<open>typeless_classical_domain\<close>) and on the goal.\<close>

locale ast_classical_domain_rx = ast_classical_domain
sublocale ast_classical_domain_rx \<subseteq> dx: ast_classical_domain DX
  rewrites "dx.subtype_rel = subtype_rel"
    and "dx.of_type = of_type"
    and "dx.is_of_type = is_of_type"
    and "dx.sig = sig"
    and "dx.func_sig = func_sig"
    and "dx.constT = constT"
    and "dx.wf_type = wf_type"
    and "dx.wf_predicate_decl = wf_predicate_decl"
    and "dx.wf_function_decl = wf_function_decl"
    and "dx.wf_types = wf_types"
    and "dx.wf_domain_signature = wf_domain_signature"
    and "dx.wf_pred_atom = wf_pred_atom"
    and "dx.wf_func_args = wf_func_args"
    and "dx.wf_primitive_numeric_expression = wf_primitive_numeric_expression"
    and "dx.wf_numeric_expression = wf_numeric_expression"
    and "dx.wf_atom = wf_atom"
    and "dx.wf_fmla = wf_fmla"
    and "dx.wf_fmla_atom = wf_fmla_atom"
    and "dx.wf_numeric_effect = wf_numeric_effect"
    and "dx.wf_effect = wf_effect"
    and "dx.wf_continuous_effect = wf_continuous_effect"
    and "dx.wf_duration_const = wf_duration_const"
    and "dx.ac_tyt = ac_tyt"
    and "dx.wf_classical_action_schema = wf_classical_action_schema"
    and "dx.typeless_domain_signature = typeless_domain_signature"
  by (simp_all add: relax_dom_sel)

locale normalized_domain_rx = normalized_domain
sublocale normalized_domain_rx \<subseteq> ast_classical_domain_rx .

locale ast_classical_problem_rx = ast_classical_problem
sublocale ast_classical_problem_rx \<subseteq> ast_classical_domain_rx D .
sublocale ast_classical_problem_rx \<subseteq> px: ast_classical_problem PX
  rewrites "px.subtype_rel = subtype_rel"
    and "px.of_type = of_type"
    and "px.is_of_type = is_of_type"
    and "px.sig = sig"
    and "px.func_sig = func_sig"
    and "px.constT = constT"
    and "px.objT = objT"
    and "px.wf_type = wf_type"
    and "px.wf_predicate_decl = wf_predicate_decl"
    and "px.wf_function_decl = wf_function_decl"
    and "px.wf_types = wf_types"
    and "px.wf_domain_signature = wf_domain_signature"
    and "px.wf_problem_signature = wf_problem_signature"
    and "px.wf_pred_atom = wf_pred_atom"
    and "px.wf_func_args = wf_func_args"
    and "px.wf_primitive_numeric_expression = wf_primitive_numeric_expression"
    and "px.wf_numeric_expression = wf_numeric_expression"
    and "px.wf_atom = wf_atom"
    and "px.wf_fmla = wf_fmla"
    and "px.wf_fmla_atom = wf_fmla_atom"
    and "px.wf_numeric_effect = wf_numeric_effect"
    and "px.wf_effect = wf_effect"
    and "px.wf_continuous_effect = wf_continuous_effect"
    and "px.wf_duration_const = wf_duration_const"
    and "px.wf_world_model = wf_world_model"
    and "px.wf_fact = wf_fact"
    and "px.wf_func_assign = wf_func_assign"
    and "px.is_obj_of_type = is_obj_of_type"
    and "px.action_params_match = action_params_match"
    and "px.ac_tyt = ac_tyt"
    and "px.wf_classical_action_schema = wf_classical_action_schema"
    and "px.wf_ground_action = wf_ground_action"
    and "px.typeless_domain_signature = typeless_domain_signature"
    and "px.typeless_problem_signature = typeless_problem_signature"
    and "px.wf_classical_domain = dx.wf_classical_domain"
    and "px.typeless_classical_domain = dx.typeless_classical_domain"
  by (simp_all add: relax_prob_sel relax_dom_sel)

text \<open>\<open>resolve_classical_action_schema\<close> is the one problem\<rightarrow>domain delegation we keep as a
  plain \<open>[simp]\<close> bridge rather than a locale \<open>rewrites\<close>: folding it into the \<open>px\<close>
  interpretation rewrites the parameter of the \<open>simple_action_instantiations\<close> sublocale and
  clashes with the later \<open>normalized_problem PX\<close> strengthening (duplicate \<open>res_inst_graph\<close>).\<close>
lemma (in ast_classical_problem_rx) rx_resolve_eq[simp]:
  "px.resolve_classical_action_schema = dx.resolve_classical_action_schema"
  by (simp add: ast_classical_domain.resolve_classical_action_schema_def relax_prob_sel)

locale normalized_problem_rx = normalized_problem
sublocale normalized_problem_rx \<subseteq> ast_classical_problem_rx .
sublocale normalized_problem_rx \<subseteq> normalized_domain_rx D
  by unfold_locales

end
