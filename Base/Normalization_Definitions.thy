theory Normalization_Definitions
  imports PDDL_Sema_Supplement
begin

text \<open>This file contains definitions of PDDL normalization properties.
The only reason these are here instead of in their respective
  normalization files is to reduce dependencies across files.
  This benefits development on my low-RAM laptop.\<close>

text \<open> Input Restriction \<close>

(* TODO think of a better name *)
abbreviation "\<omega> \<equiv> Either [STR ''object'']"

(* This being omitted from wf_action_schema complicates type normalization *)
definition (in domain_signature) wf_action_params :: "ast_classical_action_schema \<Rightarrow> bool" where
  "wf_action_params a \<equiv> (\<forall>(n, t) \<in> set (parameters (head a)). wf_type t)"
 
fun single_type :: "type \<Rightarrow> bool" where
  "single_type (Either ts) \<longleftrightarrow> length ts = 1"
abbreviation single_types :: "('a \<times> type) list \<Rightarrow> bool" where
  "single_types os \<equiv> \<forall>(_, T) \<in> set os. single_type T"

definition (in domain_signature) restrict_dom_sig where
  "restrict_dom_sig \<equiv> single_types consts"

definition (in ast_classical_domain) restrict_dom where
  "restrict_dom \<equiv> restrict_dom_sig \<and> (\<forall>a \<in> set (actions D). wf_action_params a)"

definition (in problem_signature) restrict_prob_sig where
  "restrict_prob_sig \<equiv> restrict_dom_sig \<and> single_types objs"

definition (in ast_classical_problem) restrict_prob where
  "restrict_prob \<equiv> restrict_dom \<and> single_types (objects P)"

locale restrict_domain_signature = domain_signature +
  assumes restrict_dom_sig: restrict_dom_sig

locale restrict_problem_signature = problem_signature +
  assumes restrict_prob_sig: restrict_prob_sig

locale restrict_classical_domain = wf_ast_classical_domain +
  assumes restrict_dom: restrict_dom

locale restrict_classical_problem = wf_ast_classical_problem +
  assumes restrict_prob: restrict_prob

sublocale restrict_problem_signature \<subseteq> restrict_domain_signature
  using restrict_prob_sig restrict_prob_sig_def
  by unfold_locales blast

sublocale restrict_classical_domain \<subseteq> restrict_domain_signature 
    "types D" "predicates D" "functions D" "consts D"
  using restrict_dom restrict_dom_def restrict_dom_sig_def
  by unfold_locales blast

sublocale restrict_classical_problem \<subseteq> restrict_classical_domain D
  using restrict_prob restrict_prob_def
  by unfold_locales blast
 
sublocale restrict_classical_problem \<subseteq> restrict_problem_signature
    "types D" "predicates D" "functions D" "consts D" "objects P"
  using restrict_prob restrict_prob_def restrict_dom_def restrict_prob_sig_def
  by unfold_locales blast

text \<open>Combined well-formed + restricted signatures. These are convenient to use as a single
  context for proofs that need both the \<open>wf_\<close> assumption and the \<open>restrict_\<close> assumption.\<close>

locale wf_restrict_domain_signature = wf_domain_signature + restrict_domain_signature

locale wf_restrict_problem_signature = wf_problem_signature + restrict_problem_signature

sublocale wf_restrict_problem_signature \<subseteq> wf_restrict_domain_signature ..

sublocale restrict_classical_domain \<subseteq>
  wf_restrict_domain_signature "types D" "predicates D" "functions D" "consts D" ..

sublocale restrict_classical_problem \<subseteq>
  wf_restrict_problem_signature "types D" "predicates D" "functions D" "consts D" "objects P" ..


text \<open> Type normalization:
- type hierarchy is empty (implicitly includes ''object'')
- Everything else is Either [''object''].
  This is a little superfluous: If well-formed, they can only be [''object'', ''object'', ...],
    which is semantically equivalent to [''object'']
  - predicate argument types are Either [''object''].
  - const types are Either [''object'']
  - actions parameters are detyped
    This isn't superfluous because wf_action_schema does not ensure well-formed param types. \<close>

definition (in domain_signature) "typeless_domain_signature \<equiv>
  ty_decl = []
  \<and> (\<forall>p \<in> set predicates. \<forall>T \<in> set (predicate_decl.argTs p). T = \<omega>)
  \<and> (\<forall>f \<in> set functions. \<forall>T \<in> set (function_decl.argTs f). T = \<omega>)
  \<and> (\<forall>(n, T) \<in> set consts. T = \<omega>)"

locale typeless_domain_signature = domain_signature + 
  assumes typeless_domain_signature: typeless_domain_signature

definition (in problem_signature) "typeless_problem_signature \<equiv>
  typeless_domain_signature
  \<and> (\<forall>(n, T) \<in> set objs. T = \<omega>)"

locale typeless_problem_signature = problem_signature +
  assumes typeless_problem_signature: typeless_problem_signature

sublocale typeless_problem_signature \<subseteq> typeless_domain_signature
  using typeless_problem_signature typeless_problem_signature_def
  by unfold_locales simp

definition (in ast_classical_domain) "typeless_classical_domain \<equiv>
    typeless_domain_signature
    \<and> (\<forall>ac \<in> set (actions D). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>)"

locale typeless_classical_domain = wf_ast_classical_domain +
  assumes typeless_classical_domain: typeless_classical_domain

sublocale typeless_classical_domain \<subseteq> typeless_domain_signature "types D" "predicates D" "functions D" "consts D"
  using typeless_classical_domain typeless_classical_domain_def
  by unfold_locales simp

lemmas typeless_classical_domain_def' =
  typeless_classical_domain_def[unfolded wf_ast_classical_domain_def typeless_classical_domain_axioms_def]

text \<open>
- domain is detyped
- objects are detyped \<close>

definition (in ast_classical_problem) "typeless_classical_problem \<equiv>
  typeless_classical_domain \<and> (\<forall>(n, T) \<in> set (objects P). T = \<omega>)"

locale typeless_classical_problem = wf_ast_classical_problem +
  assumes typeless_classical_problem: typeless_classical_problem
lemmas typeless_classical_problem_def' =
  typeless_classical_problem_def[unfolded wf_ast_classical_problem_def typeless_classical_problem_axioms_def]

sublocale typeless_classical_problem \<subseteq> typeless_classical_domain D
  using typeless_classical_problem typeless_classical_problem_def by (unfold_locales) blast

sublocale typeless_classical_problem \<subseteq> 
    typeless_problem_signature "types D" "predicates D" "functions D" "consts D" "objects P"
  apply unfold_locales
  using typeless_classical_problem 
  unfolding typeless_classical_problem_def typeless_classical_domain_def 
  unfolding typeless_domain_signature_def typeless_problem_signature_def
  by simp

text \<open> Definedness explication: every PNE appearing in the formula has its
  definedness atom \<open>numericEqAtm (FunctionExpr p) (FunctionExpr p)\<close> sitting
  in the formula's top-level conjunctive prefix. This is the syntactic
  invariant established by the \<open>Definedness_Normalization\<close> step's
  \<open>prepend_atoms_to_conj\<close> shape and the invariant assumed by
  \<open>Precondition_Normalization\<close>'s DNF split (otherwise the split would have
  to re-explicate definedness atoms onto each disjunct). \<close>

fun conj_atom_prefix :: "'a formula \<Rightarrow> 'a list" where
  "conj_atom_prefix (Atom a \<^bold>\<and> f) = a # conj_atom_prefix f"
| "conj_atom_prefix _ = []"

lemma conj_atom_prefix_foldr_and_Atom:
  "conj_atom_prefix (foldr (\<^bold>\<and>) (map Atom as) f) = as @ conj_atom_prefix f"
  by (induction as) auto

definition "is_def_explicated_conj f \<equiv>
  \<forall>p \<in> set (formula_enumerate_primitive_numeric_expressions f).
    numericEqAtm (FunctionExpr p) (FunctionExpr p) \<in> set (conj_atom_prefix f)"

definition (in ast_classical_domain) "def_explicated_conj_dom \<equiv>
  \<forall>a \<in> set (actions D). is_def_explicated_conj (ac_pre a)"

locale def_explicated_conj_domain = wf_ast_classical_domain +
  assumes def_explicated_conj_dom: def_explicated_conj_dom

definition (in ast_classical_problem) "def_explicated_conj_prob \<equiv>
  def_explicated_conj_dom \<and> is_def_explicated_conj (goal P)"

locale def_explicated_conj_problem = wf_ast_classical_problem +
  assumes def_explicated_conj_prob: def_explicated_conj_prob

sublocale def_explicated_conj_problem \<subseteq> def_explicated_conj_domain D
  using def_explicated_conj_prob def_explicated_conj_prob_def by (unfold_locales) blast

text \<open> Precondition normalization: all action preconditions are normalized. \<close>

definition (in ast_classical_domain) "prec_normed_dom \<equiv> \<forall>ac \<in> set (actions D). is_conj (ac_pre ac)"

(*locale precond_normed_domain = wf_ast_classical_domain +
  assumes prec_normed_dom: prec_normed_dom
lemmas precond_normed_domain_def' =
  precond_normed_domain_def[unfolded wf_ast_classical_domain_def precond_normed_domain_axioms_def]*)

text \<open> Preconditions only exist in the domain, so no additional definition is needed for the problem.\<close>

(*locale precond_normed_problem = wf_ast_classical_problem +
  assumes prec_normed_prob: prec_normed_dom
lemmas precond_normed_problem_def' =
  precond_normed_problem_def[unfolded wf_ast_classical_problem_def precond_normed_problem_axioms_def]

sublocale precond_normed_problem \<subseteq> precond_normed_domain D
  using prec_normed_prob by (unfold_locales) simp*)

text \<open> Complete normalization additionally assumes that the goal is a conjunction. \<close>

definition (in ast_classical_domain) "normalized_dom \<equiv> typeless_classical_domain \<and> prec_normed_dom"

locale normalized_domain = wf_ast_classical_domain +
  assumes normalized_dom: normalized_dom
lemmas normalized_domain_def' =
  normalized_domain_def[unfolded wf_ast_classical_domain_def normalized_domain_axioms_def]

(*sublocale normalized_domain \<subseteq> typeless_classical_domain D
  using normalized_dom normalized_dom_def by (unfold_locales) simp

sublocale normalized_domain \<subseteq> precond_normed_domain D
  using normalized_dom normalized_dom_def by (unfold_locales) simp*)

definition (in ast_classical_problem) "normalized_prob \<equiv>
  typeless_classical_problem \<and> prec_normed_dom \<and> is_conj (goal P)"

locale normalized_problem = wf_ast_classical_problem +
  assumes normalized_prob: normalized_prob
lemmas normalized_problem_def' =
  normalized_problem_def[unfolded wf_ast_classical_problem_def normalized_problem_axioms_def]

sublocale normalized_problem \<subseteq> normalized_domain D
  using normalized_prob normalized_dom_def normalized_prob_def typeless_classical_problem_def
  by (unfold_locales) blast

(*sublocale normalized_problem \<subseteq> typeless_classical_problem P
  using normalized_prob normalized_prob_def by (unfold_locales) simp

sublocale normalized_problem \<subseteq> precond_normed_problem P
  using normalized_prob normalized_prob_def by (unfold_locales) simp*)

text \<open> Relaxation \<close>

definition (in ast_classical_domain) "relaxed_dom \<equiv>
  normalized_dom \<and> (\<forall>a \<in> set (actions D). is_pos_conj (ac_pre a))"

locale relaxed_domain = normalized_domain +
  assumes relaxed_dom: relaxed_dom

definition (in ast_classical_problem) "relaxed_prob \<equiv> normalized_prob \<and>
  is_pos_conj (goal P) \<and> (\<forall>a \<in> set (actions D). is_pos_conj (ac_pre a))"

locale relaxed_problem = normalized_problem +
  assumes relaxed_prob: relaxed_prob

sublocale relaxed_problem \<subseteq> relaxed_domain D
  using relaxed_prob normalized_dom relaxed_prob_def relaxed_dom_def
  by (unfold_locales) simp

text \<open> Bound-split readiness. A structural restriction on a normalized,
  definedness-explicated problem, capturing exactly the conditions under
  which the bound-split transformation (item #7 in \<open>WIP_bound_split.md\<close>)
  is sound:

  \<^item> every numeric effect uses a monotone or assignment op
    (\<open>Increase\<close> / \<open>Decrease\<close> / \<open>Assign\<close>; \<open>ScaleUp\<close> / \<open>ScaleDown\<close> are
    forbidden) with a statically computable \<open>ConstantExpr\<close> rhs;
  \<^item> every numeric atom in a precondition or in the goal is either a
    reflexive definedness check
    \<open>numericEqAtm (FunctionExpr p) (FunctionExpr p)\<close>, or a comparison of
    one PNE expression against a constant.

  The corresponding locale extends \<open>def_explicated_conj_domain\<close> via a
  sublocale (preconditions arrive split + def-explicated by the upstream
  pipeline) but deliberately does NOT extend \<open>relaxed_domain\<close>: the existing
  \<open>relax_conj\<close> rewrites numeric atoms into \<open>\<not>\<bottom>\<close>, but bound-split must
  inspect them to rewrite each into the direction-appropriate
  upper/lower-bound predicate. So bound-split has to run before \<open>relax\<close>.
\<close>

fun bsplit_ready_cmp :: "'ent numeric_expression \<Rightarrow> 'ent numeric_expression \<Rightarrow> bool" where
  "bsplit_ready_cmp (FunctionExpr _) (ConstantExpr _) = True"
| "bsplit_ready_cmp (ConstantExpr _) (FunctionExpr _) = True"
| "bsplit_ready_cmp _ _ = False"

fun bsplit_ready_natom :: "'ent atom \<Rightarrow> bool" where
  "bsplit_ready_natom (predAtm _ _) = True"
| "bsplit_ready_natom (eqAtm _ _) = True"
| "bsplit_ready_natom (numericEqAtm l r) =
    (\<exists>p. l = FunctionExpr p \<and> r = FunctionExpr p)"
| "bsplit_ready_natom (numericLessAtm l r) = bsplit_ready_cmp l r"
| "bsplit_ready_natom (numericLEAtm l r) = bsplit_ready_cmp l r"
| "bsplit_ready_natom (numericGreaterAtm l r) = bsplit_ready_cmp l r"
| "bsplit_ready_natom (numericGEAtm l r) = bsplit_ready_cmp l r"

fun bsplit_ready_fmla :: "'ent atom formula \<Rightarrow> bool" where
  "bsplit_ready_fmla \<bottom> = True"
| "bsplit_ready_fmla (Atom a) = bsplit_ready_natom a"
| "bsplit_ready_fmla (\<^bold>\<not> f) = bsplit_ready_fmla f"
| "bsplit_ready_fmla (f \<^bold>\<and> g) = (bsplit_ready_fmla f \<and> bsplit_ready_fmla g)"
| "bsplit_ready_fmla (f \<^bold>\<or> g) = (bsplit_ready_fmla f \<and> bsplit_ready_fmla g)"
| "bsplit_ready_fmla (f \<^bold>\<rightarrow> g) = (bsplit_ready_fmla f \<and> bsplit_ready_fmla g)"

fun bsplit_ready_neff :: "'ent numeric_effect \<Rightarrow> bool" where
  "bsplit_ready_neff (NumericEffect Assign _ rhs) = (\<exists>c. rhs = ConstantExpr c)"
| "bsplit_ready_neff (NumericEffect Increase _ rhs) = (\<exists>c. rhs = ConstantExpr c)"
| "bsplit_ready_neff (NumericEffect Decrease _ rhs) = (\<exists>c. rhs = ConstantExpr c)"
| "bsplit_ready_neff (NumericEffect ScaleUp _ _) = False"
| "bsplit_ready_neff (NumericEffect ScaleDown _ _) = False"

definition (in ast_classical_domain) "bsplit_ready_dom \<equiv>
  normalized_dom
  \<and> def_explicated_conj_dom
  \<and> (\<forall>a \<in> set (actions D).
        bsplit_ready_fmla (ac_pre a)
      \<and> list_all1 bsplit_ready_neff (numeric_effects (ac_eff a)))"

locale bsplit_ready_domain = wf_ast_classical_domain +
  assumes bsplit_ready_dom: bsplit_ready_dom

sublocale bsplit_ready_domain \<subseteq> normalized_domain
  using bsplit_ready_dom bsplit_ready_dom_def by unfold_locales blast

sublocale bsplit_ready_domain \<subseteq> def_explicated_conj_domain
  using bsplit_ready_dom bsplit_ready_dom_def by unfold_locales blast

definition (in ast_classical_problem) "bsplit_ready_prob \<equiv>
  bsplit_ready_dom
  \<and> normalized_prob
  \<and> is_def_explicated_conj (goal P)
  \<and> bsplit_ready_fmla (goal P)"

locale bsplit_ready_problem = wf_ast_classical_problem +
  assumes bsplit_ready_prob: bsplit_ready_prob

sublocale bsplit_ready_problem \<subseteq> bsplit_ready_domain D
  using bsplit_ready_prob bsplit_ready_prob_def by unfold_locales blast

sublocale bsplit_ready_problem \<subseteq> normalized_problem
  using bsplit_ready_prob bsplit_ready_prob_def normalized_prob_def
  by unfold_locales blast

sublocale bsplit_ready_problem \<subseteq> def_explicated_conj_problem
  using bsplit_ready_prob bsplit_ready_prob_def
  by unfold_locales (auto simp: def_explicated_conj_prob_def
                                bsplit_ready_dom_def)


subsection \<open> Reachability Definitions \<close>
text \<open> A plan action is applicable if there exists some plan that executes it.
  Whether or not this plan actually solves the task doesn't matter.\<close>

definition (in ast_classical_problem) applicable :: "ast_classical_plan_action \<Rightarrow> bool"
  where "applicable \<pi> \<equiv> \<exists>\<pi>s M. valid_classical_plan_alt I \<pi>s M \<and> \<pi> \<in> set \<pi>s"

lemma (in ast_classical_problem) applicable_alt:
  "applicable \<pi> \<longleftrightarrow> (\<exists>\<pi>s M. valid_classical_plan_alt I \<pi>s M \<and>
    plan_action_enabled \<pi> M)"
proof
  assume "applicable \<pi>"
  then obtain \<pi>s M where 1: "valid_classical_plan_alt I \<pi>s M \<and> \<pi> \<in> set \<pi>s"
    unfolding applicable_def by blast
  then obtain \<pi>s' where "sublist_until \<pi>s \<pi> @ (\<pi> # \<pi>s') = \<pi>s"
    using sublist_just_until by fastforce
  with 1 show "\<exists>\<pi>s M. valid_classical_plan_alt I \<pi>s M \<and>
    plan_action_enabled \<pi> M"
    using valid_classical_plan_alt_append_elim valid_classical_plan_alt.simps(2) by metis
next
  assume "\<exists>\<pi>s M. valid_classical_plan_alt I \<pi>s M \<and> plan_action_enabled \<pi> M"
  then obtain \<pi>s M where 1: "valid_classical_plan_alt I \<pi>s M" "plan_action_enabled \<pi> M"
    by auto
  hence "valid_classical_plan_alt M [\<pi>] (execute_plan_action \<pi> M)"
    using valid_classical_plan_alt.simps plan_action_enabled_def
    using execute_plan_action_def by simp
  moreover have "\<pi> \<in> set (\<pi>s @ [\<pi>])" by simp
  ultimately show "applicable \<pi>" 
    using 1 valid_classical_plan_alt_append_intro applicable_def by fast
qed

text \<open> A fact is achievable if there exists some plan that results in a state containing it. \<close>

definition (in ast_classical_problem) achievable :: "fact \<Rightarrow> bool"
  where "achievable f \<equiv> \<exists>\<pi>s M. valid_classical_plan_alt I \<pi>s M \<and> Atom (uncurry predAtm f) \<in> fst M"


lemma (in wf_ast_classical_problem) init_achievable:
  assumes "Atom (predAtm p xs) \<in> set (init P)"
  shows "achievable (p, xs)"
proof -
  have 1: "valid_classical_plan_alt I [] I" by simp
  have 2: "Atom (predAtm p xs) \<in> fst I"
    using assms unfolding I_def by simp
  show ?thesis
    unfolding achievable_def
    by (rule exI[of _ "[]"]; rule exI[of _ I]) (use 1 2 in \<open>simp add: uncurry_def\<close>)
qed

lemma (in wf_ast_classical_problem) achievable_wf:
  "achievable (p, xs) \<Longrightarrow> wf_fact (p, xs)"
proof -
  assume "achievable (p, xs)"
  then obtain \<pi>s M where vp: "valid_classical_plan_alt I \<pi>s M"
    and mem: "Atom (predAtm p xs) \<in> fst M"
    unfolding achievable_def by (auto simp: uncurry_def)
  have wm: "wf_world_model M"
    using wf_I wf_valid_classical_plan_alt vp by blast
  obtain L N where M_eq: "M = (L, N)" by (cases M)
  hence "Atom (predAtm p xs) \<in> L" using mem by simp
  moreover have "\<forall>f \<in> L. wf_fmla_atom objT f" using wm M_eq by simp
  ultimately have "wf_fmla_atom objT (Atom (predAtm p xs))" by blast
  thus "wf_fact (p, xs)"
    unfolding wf_fact_def by simp
qed


subsection \<open> Grounded PDDL \<close>

text \<open>
  Types, constants and objects don't really matter for grounded PDDL: they can just be ignored.
  But for completeness' sake, they are restricted to be empty in grounded PDDL.
\<close>

fun grounded_pred :: "predicate_decl \<Rightarrow> bool" where
  "grounded_pred (PredDecl n args) \<longleftrightarrow> args = []"

fun grounded_ac :: "ast_classical_action_schema \<Rightarrow> bool" where
  "grounded_ac (SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff)) \<longleftrightarrow> params = []"

definition (in ast_classical_domain) "grounded_dom \<equiv>
  types D = [] \<and>
  list_all1 grounded_pred (predicates D) \<and>
  consts D = [] \<and>
  list_all1 grounded_ac (actions D)"

locale grounded_domain = wf_ast_classical_domain +
  assumes grounded_dom: grounded_dom

definition (in ast_classical_problem) "grounded_prob \<equiv>
  grounded_dom \<and> objects P = []"

locale grounded_problem = wf_ast_classical_problem +
  assumes grounded_prob: grounded_prob

sublocale grounded_problem \<subseteq> grounded_domain D
  using grounded_prob grounded_prob_def by (unfold_locales) simp

lemma (in grounded_problem) grounded_pa_nullary:
  "wf_classical_plan_action (SimplePlanAction n args) \<longleftrightarrow> n \<in> ac_name ` set (actions D) \<and> args = []" (is "?L \<longleftrightarrow> ?R")
proof -
  have empty: "ac_params ac = []" if "ac \<in> set (actions D)" for ac
    using that grounded_dom grounded_dom_def grounded_ac.simps
    apply (cases ac rule: ast_classical_action_schema_cases_unfold) by auto
  show ?thesis proof
    assume ?L
    then obtain ac where ac: "ac \<in> set (actions D)" "action_params_match (head ac) args" "ac_name ac = n"
      using wf_pa_refs_ac by metis
    with ac show ?R using empty action_params_match_def by auto
  next
    assume ?R
    then obtain ac where ac: "ac \<in> set (actions D)" "ac_name ac = n" by blast
    with \<open>?R\<close> show ?L
      unfolding wf_classical_plan_action_simple action_params_match_def
      using res_aux[of n ac] empty by simp
  qed
qed

text \<open> Grounded and normalized PDDL, which is convertible to STRIPS \<close>

(* type normalization follows from grounded domain *)
locale grounded_normalized_domain = grounded_domain +
  assumes normed_dom: prec_normed_dom

locale grounded_normalized_problem = grounded_problem +
  assumes normed_prob: "prec_normed_dom \<and> (is_conj (goal P))"

sublocale grounded_normalized_problem \<subseteq> grounded_normalized_domain D
  using normed_prob by (unfold_locales) blast


end