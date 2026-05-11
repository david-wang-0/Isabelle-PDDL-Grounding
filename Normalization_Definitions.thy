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
(* 
subsection \<open> Reachability Definitions \<close>
text \<open> A plan action is applicable if there exists some plan that executes it.
  Whether or not this plan actually solves the task doesn't matter.\<close>
(
definition (in ast_classical_problem) applicable :: "plan_action \<Rightarrow> bool"
  where "applicable \<pi> \<equiv> \<exists>\<pi>s M. plan_action_path I \<pi>s M \<and> \<pi> \<in> set \<pi>s"

lemma (in ast_classical_problem) applicable_alt:
  "applicable \<pi> \<longleftrightarrow> (\<exists>\<pi>s M. plan_action_path I \<pi>s M \<and>
    plan_action_enabled \<pi> M)"
proof
  assume "applicable \<pi>"
  then obtain \<pi>s M where 1: "plan_action_path I \<pi>s M \<and> \<pi> \<in> set \<pi>s"
    unfolding applicable_def by blast
  then obtain \<pi>s' where "sublist_until \<pi>s \<pi> @ (\<pi> # \<pi>s') = \<pi>s"
    using sublist_just_until by fastforce
  with 1 show "\<exists>\<pi>s M. plan_action_path I \<pi>s M \<and>
    plan_action_enabled \<pi> M"
    using plan_action_path_append_elim plan_action_path_Cons by metis
next
  assume "\<exists>\<pi>s M. plan_action_path I \<pi>s M \<and> plan_action_enabled \<pi> M"
  then obtain \<pi>s M where 1: "plan_action_path I \<pi>s M" "plan_action_enabled \<pi> M"
    by auto
  hence "plan_action_path M [\<pi>] (execute_plan_action \<pi> M)"
    using plan_action_path_def plan_action_enabled_def
    using execute_plan_action_def execute_ground_action_def by simp
  moreover have "\<pi> \<in> set (\<pi>s @ [\<pi>])" by simp
  ultimately show "applicable \<pi>" using 1 applicable_def plan_action_path_append_intro by fast
qed

text \<open> A fact is achievable if there exists some plan that results in a state containing it. \<close>

definition (in ast_classical_problem) achievable :: "object atom formula \<Rightarrow> bool"
  where "achievable a \<equiv> \<exists>\<pi>s M. plan_action_path I \<pi>s M \<and> a \<in> M"

lemma (in wf_ast_classical_problem) init_achievable:
  "\<forall>a \<in> set (init P). achievable a"
proof -
  have "plan_action_path I [] I" by simp
  thus ?thesis unfolding achievable_def I_def by blast
qed

lemma (in wf_ast_classical_problem) achievable_wf:
  "achievable a \<Longrightarrow> wf_fmla_atom objT a"
  unfolding achievable_def
  using wf_I wf_plan_action_path
  unfolding wf_world_model_def by meson

lemma (in wf_ast_classical_problem) achievable_predAtm:
  "achievable a \<Longrightarrow> is_predAtom a"
  using achievable_wf wf_fmla_atom_alt by blast

subsection \<open> Grounded PDDL \<close>

text \<open>
  Types, constants and objects don't really matter for grounded PDDL: they can just be ignored.
  But for completeness' sake, they are restricted to be empty in grounded PDDL.
\<close>

fun grounded_pred :: "predicate_decl \<Rightarrow> bool" where
  "grounded_pred (PredDecl n args) \<longleftrightarrow> args = []"

fun grounded_ac :: "ast_action_schema \<Rightarrow> bool" where
  "grounded_ac (Action_Schema n params pre effs) \<longleftrightarrow> params = []"

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
  "wf_plan_action (PAction n args) \<longleftrightarrow> n \<in> ac_name ` set (actions D) \<and> args = []" (is "?L \<longleftrightarrow> ?R")
proof -
  have empty: "ac_params ac = []" if "ac \<in> set (actions D)" for ac
    using that grounded_dom grounded_dom_def grounded_ac.simps
    by (metis ast_action_schema.exhaust_sel that)
  show ?thesis proof
    assume ?L
    then obtain ac where ac: "ac \<in> set (actions D)" "action_params_match ac args" "ac_name ac = n"
      using wf_pa_refs_ac by metis
    with ac show ?R using empty action_params_match_def by auto
  next
    assume ?R
    then obtain ac where ac: "ac \<in> set (actions D)" "ac_name ac = n" by blast
    with \<open>?R\<close> show ?L
      unfolding wf_plan_action_simple action_params_match_def
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
  *)

end