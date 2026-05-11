theory Type_Normalization_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Tree_Decomp_Grounding.Normalization_Definitions 
    Tree_Decomp_Grounding.Graph_Funs
    Tree_Decomp_Grounding.String_Utils iq.iq
begin

section \<open>Type Normalization Definitions and Locales\<close>

text \<open>This file holds the definitions backing type normalization (helper detyping functions,
  detyped predicate/function/object lists, the detyped domain/problem) together with the
  parallel \<open>*2\<close> locale hierarchy that relates a typed signature/domain/problem to its
  detyped counterpart.

  Each \<open>*2\<close> locale extends its plain counterpart and adds sublocale interpretations for the
  detyped instance. Two named instances are introduced for each detyped object:
  \<^item> \<open>sig2\<close> — the detyped signature (\<open>domain_signature\<close>/\<open>problem_signature\<close>),
  \<^item> \<open>d2\<close>/\<open>p2\<close> — the detyped domain/problem.

  Without further intervention this would create two distinct copies of every signature-level
  constant — e.g.\ \<open>d2.wf_fmla\<close> and \<open>sig2.wf_fmla\<close> — so a fact about one would not unify with
  a goal about the other. Below, every sublocale that introduces \<open>d2\<close> or \<open>p2\<close> is given
  \<open>rewrites\<close> equations identifying its signature-level constants with the corresponding
  \<open>sig2\<close>/\<open>d2\<close> versions, so the duplicates collapse on import.\<close>

subsection \<open>Detyping definitions\<close>

text \<open>Even before performing normalization, we place a two restrictions on the input PDDL task.
* Restrict consts/objects to primitive types only. This greatly simplifies type normalization.
  I couldn't find any PDDL planning task that makes use of constants with Either types, anyway.
* Ensure that action signature types are well-formed. This not being ensured in wf_domain may be an
  oversight. In practice, PDDL domains should adhere to this, anyway.\<close>

context domain_signature
begin

  (* TODO: maybe better name, e.g. "____is_Car" *)

  definition pred_for_type :: "name \<Rightarrow> predicate" where
      "pred_for_type t \<equiv> Pred (safe_prefix pred_names + (STR ''type_'' + t))"

  fun type_pred :: "name \<Rightarrow> predicate_decl" where
      "type_pred t = PredDecl (pred_for_type t) [\<omega>]"

  (* if multiple inheritance exists, there are duplicates *)
  abbreviation "type_names \<equiv> remdups (STR ''object'' # map fst ty_decl)"

  definition type_preds :: "predicate_decl list" where
    "type_preds \<equiv> map type_pred type_names"

  abbreviation supertypes_of :: "name \<Rightarrow> name list" where
    "supertypes_of \<equiv> reachable_nodes ty_decl"

  abbreviation (input) type_predatm :: "'a \<Rightarrow> name \<Rightarrow> 'a atom" where
    "type_predatm x t \<equiv> predAtm (pred_for_type t) [x]"

  fun type_atom :: "'a \<Rightarrow> name \<Rightarrow> 'a atom formula" where
    "type_atom x t = Atom (type_predatm x t)"

  fun type_precond :: "variable \<times> type \<Rightarrow> term atom formula" where
    "type_precond (v, (Either ts)) = \<^bold>\<Or> (map (type_atom (term.VAR v)) ts)"

  definition param_precond :: "(variable \<times> type) list \<Rightarrow> term atom formula" where
    "param_precond params = \<^bold>\<And> (map type_precond params)"

  abbreviation (in -) detype_pred :: "predicate_decl \<Rightarrow> predicate_decl" where
    "detype_pred p \<equiv> PredDecl (pred p) (replicate (length (predicate_decl.argTs p)) \<omega>)"

  definition (in -) detype_preds :: "predicate_decl list \<Rightarrow> predicate_decl list" where
    "detype_preds preds \<equiv> map detype_pred preds"

  fun (in -) detype_fun :: "function_decl \<Rightarrow> function_decl" where
    "detype_fun (FuncDecl n as) = FuncDecl n (replicate (length as) \<omega>)"

  definition (in -) detype_funs :: "function_decl list \<Rightarrow> function_decl list" where
    "detype_funs funs \<equiv> map detype_fun funs"

  fun (in -) detype_ent :: "('ent \<times> type) \<Rightarrow> ('ent \<times> type)" where
    "detype_ent (n, T) = (n, \<omega>)"

  definition (in -) detype_ents :: "('ent \<times> type) list \<Rightarrow> ('ent \<times> type) list" where
    "detype_ents params \<equiv> map detype_ent params"

  fun (in -) detype_action_head::"ast_action_head \<Rightarrow> ast_action_head" where
    "detype_action_head (ActionHead n params) = ActionHead n (detype_ents params)"

  fun detype_simple_action_body::"ast_action_head \<Rightarrow> ast_simple_action_body \<Rightarrow> ast_simple_action_body" where
    "detype_simple_action_body h (SimpleActionBody pre eff) = SimpleActionBody (param_precond (parameters h) \<^bold>\<and> pre) eff"

  primrec detype_classical_ac :: "ast_classical_action_schema \<Rightarrow> ast_classical_action_schema" where
    "detype_classical_ac (SimpleActionSchema h b) = SimpleActionSchema (detype_action_head h) (detype_simple_action_body h b)"


  text \<open>This only works for single types on purpose.\<close>
  fun supertype_facts_for :: "(object \<times> type) \<Rightarrow> object atom formula list" where
    "supertype_facts_for (n, Either [t]) =
      map (type_atom n) (supertypes_of t)" |
    "supertype_facts_for (n, _) = undefined"

  definition supertype_facts :: "(object \<times> type) list \<Rightarrow> object atom formula list" where
    "supertype_facts objs \<equiv> concat (map supertype_facts_for objs)"
end

text \<open>Now, we provide access to the detyped predicates, functions, constants, and objects\<close>

definition (in domain_signature) "detyped_predicates \<equiv> type_preds @ detype_preds predicates"

definition (in domain_signature) "detyped_functions \<equiv> detype_funs functions"

definition (in domain_signature) "detyped_consts \<equiv> detype_ents consts"

definition (in problem_signature) "detyped_objs \<equiv> detype_ents objs"


definition (in ast_classical_domain) detype_classical_dom :: "ast_classical_domain" where
"detype_classical_dom \<equiv>
  Domain
    []
    detyped_predicates
    detyped_functions
    detyped_consts
    (map detype_classical_ac (actions D))"

(* TODO remove remdups lmao *)
definition (in ast_classical_problem) detype_classical_prob :: "ast_classical_problem" where
"detype_classical_prob \<equiv> Problem
    detype_classical_dom
    detyped_objs
    (remdups (supertype_facts (all_consts) @ (init P)))
    (goal P)"

(* This will be referenced a lot in proofs. *)
abbreviation (in problem_signature) "sf_substate \<equiv> set (supertype_facts all_consts)"

text \<open>Abbreviations for the detyped domain/problem. These keep proofs readable: \<open>d2.foo\<close>
  reads better than \<open>ast_classical_domain.foo detype_classical_dom\<close>.\<close>
abbreviation (in ast_classical_domain) (input) "D2 \<equiv> detype_classical_dom"
abbreviation (in ast_classical_problem) (input) "P2 \<equiv> detype_classical_prob"

subsection \<open>Selectors for the detyped domain/problem\<close>

text \<open>These \<open>[simp]\<close> rules — \<open>consts D2 = detyped_consts\<close>, \<open>domain P2 = D2\<close>, etc. — are needed
  to discharge the \<open>rewrites\<close> equations in the locale hierarchy below, so they live here
  rather than with the rest of the proofs.\<close>

lemma (in ast_classical_domain) detype_classical_dom_sel [simp]:
  "types D2 = []"
  "predicates D2 = detyped_predicates"
  "consts D2 = detyped_consts"
  "actions D2 = map detype_classical_ac (actions D)"
  using detype_classical_dom_def by simp_all

lemma (in ast_classical_problem) detype_classical_prob_sel [simp]:
  "domain P2 = D2"
  "objects P2 = detyped_objs"
  "init P2 = remdups (supertype_facts all_consts @ (init P))"
  "goal P2 = goal P"
  using ast_classical_problem.detype_classical_prob_def by simp_all

subsection \<open>The \<open>*2\<close> locale hierarchy\<close>

text \<open>First we relate signatures, domains, and problems to their detyped counterparts.\<close>
locale domain_signature2 = domain_signature
sublocale domain_signature2 \<subseteq> 
  sig2: domain_signature Nil detyped_predicates detyped_functions detyped_consts .

locale wf_domain_signature2 = wf_domain_signature
sublocale wf_domain_signature2 \<subseteq> domain_signature2 .

locale problem_signature2 = problem_signature
sublocale problem_signature2 \<subseteq> 
  sig2: problem_signature Nil detyped_predicates detyped_functions detyped_consts detyped_objs .
sublocale problem_signature2 \<subseteq> domain_signature2 .

locale wf_problem_signature2 = wf_problem_signature
sublocale wf_problem_signature2 \<subseteq> problem_signature2 .
sublocale wf_problem_signature2 \<subseteq> wf_domain_signature2 by unfold_locales

text \<open>The classical-domain \<open>*2\<close> locale. The \<open>sig2\<close> sublocale is established \<^emph>\<open>first\<close>
  so the rewrites on the subsequent \<open>d2\<close> sublocale can refer to it.\<close>
locale ast_classical_domain2 = ast_classical_domain
sublocale ast_classical_domain2 \<subseteq>
  domain_signature2 "types D" "predicates D" "functions D" "consts D" .
sublocale ast_classical_domain2 \<subseteq> d2: ast_classical_domain D2
  rewrites
    "d2.subtype_rel = sig2.subtype_rel"
    and "d2.of_type = sig2.of_type"
    and "d2.is_of_type = sig2.is_of_type"
    and "d2.sig = sig2.sig"
    and "d2.func_sig = sig2.func_sig"
    and "d2.constT = sig2.constT"
    and "d2.wf_type = sig2.wf_type"
    and "d2.wf_predicate_decl = sig2.wf_predicate_decl"
    and "d2.wf_function_decl = sig2.wf_function_decl"
    and "d2.wf_types = sig2.wf_types"
    and "d2.wf_domain_signature = sig2.wf_domain_signature"
    and "d2.wf_pred_atom = sig2.wf_pred_atom"
    and "d2.wf_func_args = sig2.wf_func_args"
    and "d2.wf_primitive_numeric_expression = sig2.wf_primitive_numeric_expression"
    and "d2.wf_numeric_expression = sig2.wf_numeric_expression"
    and "d2.wf_atom = sig2.wf_atom"
    and "d2.wf_fmla = sig2.wf_fmla"
    and "d2.wf_fmla_atom = sig2.wf_fmla_atom"
    and "d2.wf_numeric_effect = sig2.wf_numeric_effect"
    and "d2.wf_effect = sig2.wf_effect"
    and "d2.wf_continuous_effect = sig2.wf_continuous_effect"
    and "d2.wf_duration_const = sig2.wf_duration_const"
    and "d2.ac_tyt = sig2.ac_tyt"
    and "d2.wf_classical_action_schema = sig2.wf_classical_action_schema"
    and "d2.typeless_domain_signature = sig2.typeless_domain_signature"
  by (auto simp: detype_classical_dom_def
                 sig2.ac_tyt_def domain_signature.ac_tyt_def
                 sig2.subtype_rel_def sig2.of_type_def sig2.is_of_type_def
                 sig2.sig_def sig2.func_sig_def sig2.constT_def
                 sig2.wf_types_def sig2.wf_domain_signature_def
                 sig2.typeless_domain_signature_def
                 domain_signature.subtype_rel_def domain_signature.of_type_def
                 domain_signature.is_of_type_def
                 domain_signature.sig_def domain_signature.func_sig_def
                 domain_signature.constT_def
                 domain_signature.wf_types_def domain_signature.wf_domain_signature_def
                 domain_signature.typeless_domain_signature_def)

locale wf_ast_classical_domain2 = wf_ast_classical_domain
sublocale wf_ast_classical_domain2 \<subseteq> ast_classical_domain2 .
sublocale wf_ast_classical_domain2 \<subseteq>
  wf_domain_signature2 "types D" "predicates D" "functions D" "consts D" by unfold_locales

text \<open>The classical-problem \<open>*2\<close> locale. The \<open>sig2\<close> (problem signature) and \<open>d2\<close> sublocales
  are established \<^emph>\<open>first\<close> so the rewrites on \<open>p2\<close> can refer to them; the domain-level rewrites
  flow in via the \<open>ast_classical_domain2\<close> sublocale.\<close>
locale ast_classical_problem2 = ast_classical_problem
sublocale ast_classical_problem2 \<subseteq>
  problem_signature2 "types D" "predicates D" "functions D" "consts D" "objects P" .
sublocale ast_classical_problem2 \<subseteq> ast_classical_domain2 D .
sublocale ast_classical_problem2 \<subseteq> p2: ast_classical_problem P2
  rewrites
    "p2.subtype_rel = sig2.subtype_rel"
    and "p2.of_type = sig2.of_type"
    and "p2.is_of_type = sig2.is_of_type"
    and "p2.sig = sig2.sig"
    and "p2.func_sig = sig2.func_sig"
    and "p2.constT = sig2.constT"
    and "p2.objT = sig2.objT"
    and "p2.wf_type = sig2.wf_type"
    and "p2.wf_predicate_decl = sig2.wf_predicate_decl"
    and "p2.wf_function_decl = sig2.wf_function_decl"
    and "p2.wf_types = sig2.wf_types"
    and "p2.wf_domain_signature = sig2.wf_domain_signature"
    and "p2.wf_problem_signature = sig2.wf_problem_signature"
    and "p2.wf_pred_atom = sig2.wf_pred_atom"
    and "p2.wf_func_args = sig2.wf_func_args"
    and "p2.wf_primitive_numeric_expression = sig2.wf_primitive_numeric_expression"
    and "p2.wf_numeric_expression = sig2.wf_numeric_expression"
    and "p2.wf_atom = sig2.wf_atom"
    and "p2.wf_fmla = sig2.wf_fmla"
    and "p2.wf_fmla_atom = sig2.wf_fmla_atom"
    and "p2.wf_numeric_effect = sig2.wf_numeric_effect"
    and "p2.wf_effect = sig2.wf_effect"
    and "p2.wf_continuous_effect = sig2.wf_continuous_effect"
    and "p2.wf_duration_const = sig2.wf_duration_const"
    and "p2.wf_world_model = sig2.wf_world_model"
    and "p2.wf_fact = sig2.wf_fact"
    and "p2.wf_func_assign = sig2.wf_func_assign"
    and "p2.is_obj_of_type = sig2.is_obj_of_type"
    and "p2.action_params_match = sig2.action_params_match"
    and "p2.ac_tyt = sig2.ac_tyt"
    and "p2.wf_classical_action_schema = sig2.wf_classical_action_schema"
    and "p2.wf_ground_action = sig2.wf_ground_action"
    and "p2.wf_classical_domain = d2.wf_classical_domain"
    and "p2.resolve_classical_action_schema = d2.resolve_classical_action_schema"
    and "p2.typeless_domain_signature = sig2.typeless_domain_signature"
    and "p2.typeless_problem_signature = sig2.typeless_problem_signature"
    and "p2.typeless_classical_domain = d2.typeless_classical_domain"
  by (auto simp: detype_classical_dom_def detype_classical_prob_def
                 sig2.ac_tyt_def domain_signature.ac_tyt_def
                 sig2.subtype_rel_def sig2.of_type_def sig2.is_of_type_def
                 sig2.sig_def sig2.func_sig_def sig2.constT_def sig2.objT_def
                 sig2.wf_types_def sig2.wf_domain_signature_def
                 sig2.wf_problem_signature_def
                 sig2.wf_fact_def sig2.is_obj_of_type_def
                 sig2.action_params_match_def
                 sig2.typeless_domain_signature_def
                 sig2.typeless_problem_signature_def
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
                 ast_classical_domain.resolve_classical_action_schema_def
                 ast_classical_domain.typeless_classical_domain_def)

locale wf_ast_classical_problem2 = wf_ast_classical_problem
sublocale wf_ast_classical_problem2 \<subseteq> ast_classical_problem2 .
sublocale wf_ast_classical_problem2 \<subseteq> wf_ast_classical_domain2 D by unfold_locales
sublocale wf_ast_classical_problem2 \<subseteq>
  wf_problem_signature2 "types D" "predicates D" "functions D" "consts D" "objects P"
  by unfold_locales

text \<open>Now, we relate restricted (no either types) signatures, etc. to their detyped counterparts.\<close>
locale restrict_domain_signature2 = restrict_domain_signature
sublocale restrict_domain_signature2 \<subseteq> domain_signature2 .

locale restrict_problem_signature2 = restrict_problem_signature
sublocale restrict_problem_signature2 \<subseteq> problem_signature2 .

locale wf_restrict_domain_signature2 = wf_restrict_domain_signature
sublocale wf_restrict_domain_signature2 \<subseteq> restrict_domain_signature2 ..
sublocale wf_restrict_domain_signature2 \<subseteq> wf_domain_signature2 ..

locale wf_restrict_problem_signature2 = wf_restrict_problem_signature
sublocale wf_restrict_problem_signature2 \<subseteq> restrict_problem_signature2 ..
sublocale wf_restrict_problem_signature2 \<subseteq> wf_problem_signature2 ..
sublocale wf_restrict_problem_signature2 \<subseteq> wf_restrict_domain_signature2 ..

locale restrict_classical_domain2 = restrict_classical_domain
sublocale restrict_classical_domain2 \<subseteq> wf_ast_classical_domain2 by unfold_locales
sublocale restrict_classical_domain2 \<subseteq> 
  wf_restrict_domain_signature2 "types D" "predicates D" "functions D" "consts D" 
  by unfold_locales

locale restrict_classical_problem2 = restrict_classical_problem
sublocale restrict_classical_problem2 \<subseteq> restrict_classical_domain2 D
  by unfold_locales
sublocale restrict_classical_problem2 \<subseteq> wf_ast_classical_problem2
  by unfold_locales
sublocale restrict_classical_problem2 \<subseteq> 
  wf_restrict_problem_signature2 "types D" "predicates D" "functions D" "consts D" "objects P" 
  by unfold_locales

(* Note: Extend a locale loc with a new name loc2 and then in loc2 obtain a new instance of loc
  named l2 using the constants L2, which are present in loc *)


end
