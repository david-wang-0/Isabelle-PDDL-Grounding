theory Definedness_Normalization_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Tree_Decomp_Grounding_Base.Normalization_Definitions
    Tree_Decomp_Grounding_Base.PDDL_Sema_Supplement
    iq.iq
begin

section ‹Definedness Explication Definitions and Locales›

text ‹For every PNE ‹p› appearing in a formula ‹f›, conjoin the reflexive
  numeric equality ‹numericEqAtm (FunctionExpr p) (FunctionExpr p)›, which
  evaluates to ‹True› iff ‹p› is defined. This is the syntactic counterpart of
  the strict definedness requirement that ‹map_formula_semantics› places on
  formulas: ‹𝒜 ⊨⇩m f› is ‹False› unless every atom of ‹f› has its arguments
  defined.

  Explicating definedness this way makes every disjunct of ‹dnf_list f› carry
  the full atom set of ‹f›, so subsequent DNF-splitting is exact.›

subsection ‹Explication on formulas›

definition "definedness_atoms f ≡
  let pnes = formula_enumerate_primitive_numeric_expressions f;
      pne_exprs = map FunctionExpr pnes
  in map (λe. numericEqAtm e e) pne_exprs"

definition "explicate_def_fmla f ≡
  foldr (❙∧) (map Atom (definedness_atoms f)) f"

subsection ‹Explication on actions, domains, and problems›

fun explicate_def_ac :: "ast_classical_action_schema ⇒ ast_classical_action_schema" where
  "explicate_def_ac (SimpleActionSchema h (SimpleActionBody pre eff))
    = SimpleActionSchema h (SimpleActionBody (explicate_def_fmla pre) eff)"

context ast_classical_domain begin

definition "explicate_def_dom ≡
  Domain
    (types D)
    (predicates D)
    (functions D)
    (consts D)
    (map explicate_def_ac (actions D))"

end

context ast_classical_problem begin

definition "explicate_def_prob ≡
  Problem
    explicate_def_dom
    (objects P)
    (init P)
    (explicate_def_fmla (goal P))"

end

text ‹Plan restoration is identity: explication never renames actions.›

definition "restore_plan_explicate πs ≡ πs"

subsection ‹Selectors for the explicated domain/problem›

lemma (in ast_classical_domain) explicate_def_dom_sel [simp]:
  "types explicate_def_dom = types D"
  "predicates explicate_def_dom = predicates D"
  "functions explicate_def_dom = functions D"
  "consts explicate_def_dom = consts D"
  "actions explicate_def_dom = map explicate_def_ac (actions D)"
  using explicate_def_dom_def by simp_all

lemma (in ast_classical_problem) explicate_def_prob_sel [simp]:
  "domain explicate_def_prob = explicate_def_dom"
  "objects explicate_def_prob = objects P"
  "init explicate_def_prob = init P"
  "goal explicate_def_prob = explicate_def_fmla (goal P)"
  using explicate_def_prob_def by simp_all

lemma explicate_def_ac_sel [simp]:
  "ac_name (explicate_def_ac a) = ac_name a"
  "ac_params (explicate_def_ac a) = ac_params a"
  "ac_pre (explicate_def_ac a) = explicate_def_fmla (ac_pre a)"
  "ac_eff (explicate_def_ac a) = ac_eff a"
  by (cases a rule: ast_classical_action_schema_cases_unfold; simp)+

subsection ‹The ‹*De› locale hierarchy›

text ‹The classical-domain ‹*De› locale. Explication preserves the domain
  signature (only the action bodies' precondition formulas change), so every
  signature-level constant of ‹d_de› is rewritten back to its counterpart in
  the input domain.›

locale ast_classical_domain_de = ast_classical_domain
sublocale ast_classical_domain_de ⊆ d_de: ast_classical_domain explicate_def_dom
  rewrites
    "d_de.subtype_rel = subtype_rel"
    and "d_de.of_type = of_type"
    and "d_de.is_of_type = is_of_type"
    and "d_de.sig = sig"
    and "d_de.func_sig = func_sig"
    and "d_de.constT = constT"
    and "d_de.wf_type = wf_type"
    and "d_de.wf_predicate_decl = wf_predicate_decl"
    and "d_de.wf_function_decl = wf_function_decl"
    and "d_de.wf_types = wf_types"
    and "d_de.wf_domain_signature = wf_domain_signature"
    and "d_de.wf_pred_atom = wf_pred_atom"
    and "d_de.wf_func_args = wf_func_args"
    and "d_de.wf_primitive_numeric_expression = wf_primitive_numeric_expression"
    and "d_de.wf_numeric_expression = wf_numeric_expression"
    and "d_de.wf_atom = wf_atom"
    and "d_de.wf_fmla = wf_fmla"
    and "d_de.wf_fmla_atom = wf_fmla_atom"
    and "d_de.wf_numeric_effect = wf_numeric_effect"
    and "d_de.wf_effect = wf_effect"
    and "d_de.wf_continuous_effect = wf_continuous_effect"
    and "d_de.wf_duration_const = wf_duration_const"
    and "d_de.ac_tyt = ac_tyt"
    and "d_de.wf_classical_action_schema = wf_classical_action_schema"
    and "d_de.typeless_domain_signature = typeless_domain_signature"
  by (simp_all only: explicate_def_dom_sel)

locale wf_ast_classical_domain_de = wf_ast_classical_domain
sublocale wf_ast_classical_domain_de ⊆ ast_classical_domain_de .

locale ast_classical_problem_de = ast_classical_problem
sublocale ast_classical_problem_de ⊆ ast_classical_domain_de D .
sublocale ast_classical_problem_de ⊆ p_de: ast_classical_problem explicate_def_prob
  rewrites
    "p_de.subtype_rel = d_de.subtype_rel"
    and "p_de.of_type = d_de.of_type"
    and "p_de.is_of_type = d_de.is_of_type"
    and "p_de.sig = d_de.sig"
    and "p_de.func_sig = d_de.func_sig"
    and "p_de.constT = d_de.constT"
    and "p_de.wf_type = d_de.wf_type"
    and "p_de.wf_predicate_decl = d_de.wf_predicate_decl"
    and "p_de.wf_function_decl = d_de.wf_function_decl"
    and "p_de.wf_types = d_de.wf_types"
    and "p_de.wf_domain_signature = d_de.wf_domain_signature"
    and "p_de.wf_pred_atom = d_de.wf_pred_atom"
    and "p_de.wf_func_args = d_de.wf_func_args"
    and "p_de.wf_primitive_numeric_expression = d_de.wf_primitive_numeric_expression"
    and "p_de.wf_numeric_expression = d_de.wf_numeric_expression"
    and "p_de.wf_atom = d_de.wf_atom"
    and "p_de.wf_fmla = d_de.wf_fmla"
    and "p_de.wf_fmla_atom = d_de.wf_fmla_atom"
    and "p_de.wf_numeric_effect = d_de.wf_numeric_effect"
    and "p_de.wf_effect = d_de.wf_effect"
    and "p_de.wf_continuous_effect = d_de.wf_continuous_effect"
    and "p_de.wf_duration_const = d_de.wf_duration_const"
    and "p_de.ac_tyt = d_de.ac_tyt"
    and "p_de.wf_classical_action_schema = d_de.wf_classical_action_schema"
    and "p_de.wf_classical_domain = d_de.wf_classical_domain"
    and "p_de.resolve_classical_action_schema = d_de.resolve_classical_action_schema"
    and "p_de.objT = objT"
    and "p_de.wf_world_model = wf_world_model"
    and "p_de.is_obj_of_type = is_obj_of_type"
    and "p_de.action_params_match = action_params_match"
  by (auto simp: explicate_def_dom_def explicate_def_prob_def
                 d_de.ac_tyt_def domain_signature.ac_tyt_def
                 d_de.subtype_rel_def d_de.of_type_def d_de.is_of_type_def
                 d_de.sig_def d_de.func_sig_def d_de.constT_def
                 d_de.wf_types_def d_de.wf_domain_signature_def
                 d_de.typeless_domain_signature_def
                 domain_signature.subtype_rel_def domain_signature.of_type_def
                 domain_signature.is_of_type_def
                 domain_signature.sig_def domain_signature.func_sig_def
                 domain_signature.constT_def
                 domain_signature.wf_types_def domain_signature.wf_domain_signature_def
                 domain_signature.typeless_domain_signature_def
                 problem_signature.objT_def problem_signature.wf_problem_signature_def
                 problem_signature.wf_fact_def problem_signature.is_obj_of_type_def
                 problem_signature.action_params_match_def
                 problem_signature.typeless_problem_signature_def
                 ast_classical_domain.wf_classical_domain_def
                 ast_classical_domain.resolve_classical_action_schema_def)

locale wf_ast_classical_problem_de = wf_ast_classical_problem
sublocale wf_ast_classical_problem_de ⊆ ast_classical_problem_de .
sublocale wf_ast_classical_problem_de ⊆ wf_ast_classical_domain_de D
  by unfold_locales

end
