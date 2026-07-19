theory Type_Normalization
  imports "Analysis_Free_Base.Signatures"
    Grounding_Common.PDDL_Normalization
    Grounding_Common.Formula_Utils
    Grounding_Utils.Graph_Funs
    Grounding_Utils.String_Utils
begin

section \<open>Signature-level detyping (reusable)\<close>

text \<open>The AST-agnostic part of type normalization: the detyping helper functions over a PDDL
  domain/problem \<^emph>\<open>signature\<close>, the detyped predicate/function/object lists, and the parallel \<open>*2\<close>
  signature-locale hierarchy relating a typed signature to its detyped counterpart. These mention only
  the shared signature and the shared action AST (\<open>ActionHead\<close>/\<open>SimpleActionBody\<close> from
  Continuous_Planning), so they are reusable by any grounder. The classical-AST counterparts
  (\<open>detype_classical_ac\<close>, \<open>detype_classical_dom\<close>/\<open>prob\<close>, the \<open>ast_classical_*2\<close> locales) live in
  \<open>Classical_Grounding.Classical_Type_Normalization_Locales\<close>.\<close>

context domain_signature
begin

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

  text \<open>This only works for single types on purpose.\<close>
  fun supertype_facts_for :: "(object \<times> type) \<Rightarrow> object atom formula list" where
    "supertype_facts_for (n, Either [t]) =
      map (type_atom n) (supertypes_of t)" |
    "supertype_facts_for (n, _) = undefined"

  definition supertype_facts :: "(object \<times> type) list \<Rightarrow> object atom formula list" where
    "supertype_facts objs \<equiv> concat (map supertype_facts_for objs)"
end

text \<open>The detyped predicates, functions, constants, and objects.\<close>

definition (in domain_signature) "detyped_predicates \<equiv> type_preds @ detype_preds predicates"

definition (in domain_signature) "detyped_functions \<equiv> detype_funs functions"

definition (in domain_signature) "detyped_consts \<equiv> detype_ents consts"

definition (in problem_signature) "detyped_objs \<equiv> detype_ents objs"

text \<open>The supertype facts added to the initial state by detyping (referenced often in proofs).\<close>
abbreviation (in problem_signature) "sf_substate \<equiv> set (supertype_facts all_consts)"

subsection \<open>The signature \<open>*2\<close> locale hierarchy\<close>

text \<open>Relate signatures to their detyped counterparts. Each \<open>*2\<close> locale extends its plain counterpart
  and adds a \<open>sig2\<close> sublocale interpretation for the detyped signature.\<close>

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

text \<open>Now the restricted (no Either types) signatures.\<close>

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

end
