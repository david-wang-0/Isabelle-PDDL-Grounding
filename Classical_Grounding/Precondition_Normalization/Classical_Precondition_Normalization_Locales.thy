theory Classical_Precondition_Normalization_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Grounding_Classical_Common.Classical_PDDL_Normalization
    Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement
    Grounding_Utils.String_Utils
    Grounding_Common.DNF
begin

section \<open> Precondition Normalization Definitions and Locales \<close>

text \<open>This file holds the definitions backing precondition normalization (splitting a
  classical action schema into one schema per DNF clause of its precondition) together
  with the parallel \<open>*4\<close> locale hierarchy that relates a classical domain/problem to its
  precondition-normalized counterpart.\<close>

subsection \<open> Splitting definitions \<close>

definition "n_clauses ac \<equiv> length (dnf_list (ac_pre ac))"

context ast_classical_domain begin

fun (in -) set_n_pre ::
  "ast_classical_action_schema \<Rightarrow> name \<Rightarrow> term atom formula \<Rightarrow> ast_classical_action_schema" where
  "set_n_pre (SimpleActionSchema (ActionHead _ params) (SimpleActionBody _ eff)) n pre
  = SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff)"

text \<open>The DNF copies of an action schema are named by decorating the schema's own name with
  a decimal clause index, \<open>ac_name ac + STR ''_'' + show i\<close> (see \<open>idx_name\<close>). Since a decimal
  numeral contains no underscore, the last underscore of a generated name is exactly the
  separator, so the original name is recovered by \<open>strip_idx\<close> --- no fixed-width padding and
  no global bound on the clause count are needed.\<close>
definition "split_ac_names ac \<equiv> map (idx_name (ac_name ac)) [0 ..< n_clauses ac]"


definition split_ac :: "ast_classical_action_schema \<Rightarrow> ast_classical_action_schema list" where
  "split_ac ac = map2 (set_n_pre ac) (split_ac_names ac) (dnf_list (ac_pre ac))"

definition "split_acs \<equiv> concat (map split_ac (actions D))"

definition split_dom :: ast_classical_domain where
  "split_dom \<equiv>
  Domain
    (types D)
    (predicates D)
    (functions D)
    (consts D)
    split_acs"

definition (in ast_classical_problem) split_prob :: ast_classical_problem where
  "split_prob \<equiv>
  Problem
    split_dom
    (objects P)
    (init P)
    (goal P)"

(* it's important to be able to convert a plan for the output problem into a plan for the input problem.
  The other direction is probably (hopefully?) not important. *)
fun restore_pa_split where
  "restore_pa_split (SimplePlanAction n args)
    = SimplePlanAction (strip_idx n) args"
abbreviation "restore_plan_split \<pi>s \<equiv> map restore_pa_split \<pi>s"

(* prec_normed_dom taken from here *)

end

text \<open> locale setup for simplified syntax \<close>

abbreviation (in ast_classical_domain) (input) "D4 \<equiv> split_dom"
abbreviation (in ast_classical_problem) (input) "P4 \<equiv> split_prob"

subsection \<open> Selectors for the split domain/problem \<close>

text \<open>These selectors are \<open>[simp]\<close> and discharge the \<open>rewrites\<close> equations of the
  \<open>*4\<close> locale hierarchy below, so they are established ahead of it.\<close>

lemma (in ast_classical_domain) split_dom_sel [simp]:
  "types D4 = types D"
  "predicates D4 = predicates D"
  "functions D4 = functions D"
  "consts D4 = consts D"
  "actions D4 = split_acs"
  using split_dom_def by simp_all

lemma (in ast_classical_problem) split_prob_sel [simp]:
  "domain P4 = D4"
  "objects P4 = objects P"
  "init P4 = init P"
  "goal P4 = goal P"
  using split_prob_def by simp_all

subsection \<open> The \<open>*4\<close> locale hierarchy \<close>

text \<open>The classical-domain \<open>*4\<close> locale. Splitting preserves the domain signature
  (only the action list changes), so every signature-level constant of \<open>d4\<close> is
  rewritten back to its counterpart in the input domain.\<close>
locale ast_classical_domain4 = ast_classical_domain
sublocale ast_classical_domain4 \<subseteq> d4: ast_classical_domain D4
  rewrites
    "d4.subtype_rel = subtype_rel"
    and "d4.of_type = of_type"
    and "d4.is_of_type = is_of_type"
    and "d4.sig = sig"
    and "d4.func_sig = func_sig"
    and "d4.constT = constT"
    and "d4.wf_type = wf_type"
    and "d4.wf_predicate_decl = wf_predicate_decl"
    and "d4.wf_function_decl = wf_function_decl"
    and "d4.wf_types = wf_types"
    and "d4.wf_domain_signature = wf_domain_signature"
    and "d4.wf_pred_atom = wf_pred_atom"
    and "d4.wf_func_args = wf_func_args"
    and "d4.wf_primitive_numeric_expression = wf_primitive_numeric_expression"
    and "d4.wf_numeric_expression = wf_numeric_expression"
    and "d4.wf_atom = wf_atom"
    and "d4.wf_fmla = wf_fmla"
    and "d4.wf_fmla_atom = wf_fmla_atom"
    and "d4.wf_numeric_effect = wf_numeric_effect"
    and "d4.wf_effect = wf_effect"
    and "d4.wf_continuous_effect = wf_continuous_effect"
    and "d4.wf_duration_const = wf_duration_const"
    and "d4.ac_tyt = ac_tyt"
    and "d4.wf_classical_action_schema = wf_classical_action_schema"
    and "d4.typeless_domain_signature = typeless_domain_signature"
  by (simp_all only: split_dom_sel)

locale wf_ast_classical_domain4 = def_explicated_conj_domain
sublocale wf_ast_classical_domain4 \<subseteq> ast_classical_domain4 .

locale ast_classical_problem4 = ast_classical_problem
sublocale ast_classical_problem4 \<subseteq> ast_classical_domain4 D .
sublocale ast_classical_problem4 \<subseteq> p4: ast_classical_problem P4 
  rewrites
    "p4.subtype_rel = d4.subtype_rel"
    and "p4.of_type = d4.of_type"
    and "p4.is_of_type = d4.is_of_type"
    and "p4.sig = d4.sig"
    and "p4.func_sig = d4.func_sig"
    and "p4.constT = d4.constT"
    and "p4.wf_type = d4.wf_type"
    and "p4.wf_predicate_decl = d4.wf_predicate_decl"
    and "p4.wf_function_decl = d4.wf_function_decl"
    and "p4.wf_types = d4.wf_types"
    and "p4.wf_domain_signature = d4.wf_domain_signature"
    and "p4.wf_pred_atom = d4.wf_pred_atom"
    and "p4.wf_func_args = d4.wf_func_args"
    and "p4.wf_primitive_numeric_expression = d4.wf_primitive_numeric_expression"
    and "p4.wf_numeric_expression = d4.wf_numeric_expression"
    and "p4.wf_atom = d4.wf_atom"
    and "p4.wf_fmla = d4.wf_fmla"
    and "p4.wf_fmla_atom = d4.wf_fmla_atom"
    and "p4.wf_numeric_effect = d4.wf_numeric_effect"
    and "p4.wf_effect = d4.wf_effect"
    and "p4.wf_continuous_effect = d4.wf_continuous_effect"
    and "p4.wf_duration_const = d4.wf_duration_const"
    and "p4.ac_tyt = d4.ac_tyt"
    and "p4.wf_classical_action_schema = d4.wf_classical_action_schema"
    and "p4.wf_classical_domain = d4.wf_classical_domain"
    and "p4.resolve_classical_action_schema = d4.resolve_classical_action_schema"
    and "p4.objT = objT"
    and "p4.wf_world_model = wf_world_model"
    and "p4.is_obj_of_type = is_obj_of_type"
    and "p4.action_params_match = action_params_match"
  by (auto simp: split_dom_def split_prob_def
                  d4.ac_tyt_def domain_signature.ac_tyt_def
                  d4.subtype_rel_def d4.of_type_def d4.is_of_type_def
                  d4.sig_def d4.func_sig_def d4.constT_def
                  d4.wf_types_def d4.wf_domain_signature_def
                  d4.typeless_domain_signature_def
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

  

text \<open>Under the pipeline order \<open>\<dots> \<rightarrow> degoal \<rightarrow> explicate_def \<rightarrow> split \<rightarrow> \<dots>\<close>,
  precondition normalization assumes its input has the conj-prefix definedness
  shape produced by \<open>Classical_Definedness_Normalization\<close>. That structural invariant is
  what lets DNF-splitting be exact under \<open>\<Turnstile>\<^sub>m\<close>'s strict definedness
  evaluation without re-explicating definedness atoms onto each disjunct.\<close>

locale wf_ast_classical_problem4 = def_explicated_conj_problem
sublocale wf_ast_classical_problem4 \<subseteq> ast_classical_problem4 .
sublocale wf_ast_classical_problem4 \<subseteq> wf_ast_classical_domain4 D
  by unfold_locales

text \<open> Alternate definitions \<close>

(* probably unnecessary *)
lemma set_n_pre_alt: "set_n_pre ac n pre =
  SimpleActionSchema (ActionHead n (ac_params ac)) (SimpleActionBody pre (ac_eff ac))"
  by (cases ac rule: ast_classical_action_schema_cases_unfold) simp

(* probably unnecessary *)
lemma set_n_pre_sel [simp]:
  "ac_name (set_n_pre ac n pre) = n"
  "ac_params (set_n_pre ac n pre) = ac_params ac"
  "ac_pre (set_n_pre ac n pre) = pre"
  "ac_eff (set_n_pre ac n pre) = ac_eff ac"
  using set_n_pre_alt by simp_all

lemma (in -) set_n_pre_mapsel:
  assumes "length ns = length pres"
  shows
    "map ac_name (map2 (set_n_pre ac) ns pres) = ns"
    (*"map ac_params (map2 (set_n_pre ac) ns pres) = replicate (n_clauses ac) (ac_params ac)" *)
    "map ac_pre (map2 (set_n_pre ac) ns pres) = pres"
    (*"map ac_eff (map2 (set_n_pre ac) ns pres) = replicate (n_clauses ac) (ac_eff ac)" *)
using assms by (induction ns pres rule: list_induct2) simp_all

end
