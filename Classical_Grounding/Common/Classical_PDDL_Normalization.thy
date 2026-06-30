theory Classical_PDDL_Normalization
  imports Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement Grounding_Common.PDDL_Normalization
begin

text \<open>This file contains definitions of PDDL normalization properties.
The only reason these are here instead of in their respective
  normalization files is to reduce dependencies across files.
  This benefits development on my low-RAM laptop.\<close>


(* This being omitted from wf_action_schema complicates type normalization *)
definition (in domain_signature) wf_action_params :: "ast_classical_action_schema \<Rightarrow> bool" where
  "wf_action_params a \<equiv> (\<forall>(n, t) \<in> set (parameters (head a)). wf_type t)"
 


definition (in ast_classical_domain) restrict_dom where
  "restrict_dom \<equiv> restrict_dom_sig \<and> (\<forall>a \<in> set (actions D). wf_action_params a)"


definition (in ast_classical_problem) restrict_prob where
  "restrict_prob \<equiv> restrict_dom \<and> single_types (objects P)"


locale restrict_classical_domain = wf_ast_classical_domain +
  assumes restrict_dom: restrict_dom

locale restrict_classical_problem = wf_ast_classical_problem +
  assumes restrict_prob: restrict_prob


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


sublocale restrict_classical_domain \<subseteq>
  wf_restrict_domain_signature "types D" "predicates D" "functions D" "consts D" ..

sublocale restrict_classical_problem \<subseteq>
  wf_restrict_problem_signature "types D" "predicates D" "functions D" "consts D" "objects P" ..



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

text \<open>In a typeless domain every action parameter has the universal type \<open>\<omega>\<close>.\<close>
lemma (in typeless_classical_domain) param_types_omega:
  assumes "ac \<in> set (actions D)" and "(v, T) \<in> set (ac_params ac)"
  shows "T = \<omega>"
  using assms typeless_classical_domain unfolding typeless_classical_domain_def by auto

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

text \<open>In a typeless problem every object name has the universal type \<open>\<omega>\<close>, so any object name
  trivially matches the universal parameter type (reverse of \<open>is_obj_of_type_const_name\<close>).\<close>
lemma (in typeless_classical_problem) const_name_is_obj_of_type:
  assumes "n \<in> set (map fst all_consts)"
  shows "is_obj_of_type n \<omega>"
proof -
  have all\<omega>: "T = \<omega>" if "(m, T) \<in> set all_consts" for m T
  proof -
    from that have "(m, T) \<in> set (consts D) \<or> (m, T) \<in> set (objects P)" by auto
    thus ?thesis
    proof
      assume "(m, T) \<in> set (consts D)"
      thus ?thesis using typeless_classical_problem
        unfolding typeless_classical_problem_def typeless_classical_domain_def
          typeless_domain_signature_def by auto
    next
      assume "(m, T) \<in> set (objects P)"
      thus ?thesis using typeless_classical_problem unfolding typeless_classical_problem_def by auto
    qed
  qed
  from assms have "n \<in> dom objT"
    by (auto simp: objT_alt dom_map_of_conv_image_fst)
  then obtain oT where oT: "objT n = Some oT" by auto
  hence "(n, oT) \<in> set all_consts" unfolding objT_alt by (auto dest: map_of_SomeD)
  hence "oT = \<omega>" using all\<omega> by blast
  thus ?thesis using oT unfolding is_obj_of_type_def by (simp add: of_type_refl)
qed

text \<open>An argument tuple of the right length drawn entirely from the object names matches an
  action's (typeless) parameters.\<close>
lemma (in typeless_classical_problem) params_match_from_const_args:
  assumes sch_mem: "sch \<in> set (actions D)"
    and len: "length args = length (ac_params sch)"
    and inc: "\<And>x. x \<in> set args \<Longrightarrow> x \<in> set (map fst all_consts)"
  shows "action_params_match (ac_head sch) args"
proof -
  obtain n ps b where sch_eq: "sch = SimpleActionSchema (ActionHead n ps) b"
    by (metis ast_classical_action_schema_cases_unfold)
  have ph: "ac_head sch = ActionHead n ps" and pp: "ac_params sch = ps"
    using sch_eq by simp_all
  have types: "snd x = \<omega>" if "x \<in> set ps" for x
    using param_types_omega[OF sch_mem] that pp by (cases x) auto
  show ?thesis
    unfolding ph action_params_match_def list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length args = length (map snd (parameters (ActionHead n ps)))"
      using len pp by simp
  next
    fix i assume i: "i < length args"
    have "args ! i \<in> set (map fst all_consts)" using inc i by simp
    hence "is_obj_of_type (args ! i) \<omega>" using const_name_is_obj_of_type by simp
    moreover have "map snd (parameters (ActionHead n ps)) ! i = \<omega>"
      using i len pp types by (simp add: nth_mem)
    ultimately show "is_obj_of_type (args ! i) (map snd (parameters (ActionHead n ps)) ! i)"
      by simp
  qed
qed

text \<open> Definedness explication: every PNE appearing in the formula has its
  definedness atom \<open>numericEqAtm (FunctionExpr p) (FunctionExpr p)\<close> sitting
  in the formula's top-level conjunctive prefix. This is the syntactic
  invariant established by the \<open>Classical_Definedness_Normalization\<close> step's
  \<open>prepend_atoms_to_conj\<close> shape and the invariant assumed by
  \<open>Classical_Precondition_Normalization\<close>'s DNF split (otherwise the split would have
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

sublocale normalized_domain \<subseteq> typeless_classical_domain D
  using normalized_dom normalized_dom_def by (unfold_locales) simp

(*sublocale normalized_domain \<subseteq> precond_normed_domain D
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

sublocale normalized_problem \<subseteq> typeless_classical_problem P
  using normalized_prob normalized_prob_def by (unfold_locales) simp

(*sublocale normalized_problem \<subseteq> precond_normed_problem P
  using normalized_prob normalized_prob_def by (unfold_locales) simp*)

text \<open> Relaxation combines two restrictions: \<^emph>\<open>precondition relaxation\<close> (preconditions and goal
  are positive conjunctions) and \<^emph>\<open>delete relaxation\<close> (actions never delete facts, so the
  reachable-fact set is monotone along any plan --- the property produced by \<open>relax_eff\<close> in
  \<open>Classical_PDDL_Relaxation\<close>). Both are folded into \<open>relaxed_dom\<close>/\<open>relaxed_prob\<close>. \<close>

text \<open> A single action schema is relaxed when its precondition is a positive conjunction and its
  effect deletes nothing. \<close>
definition relaxed_action :: "ast_classical_action_schema \<Rightarrow> bool" where
  "relaxed_action a \<longleftrightarrow> is_pos_conj (ac_pre a) \<and> dels (ac_eff a) = []"

lemma relaxed_actionI [intro]:
  assumes "is_pos_conj (ac_pre a)" and "dels (ac_eff a) = []"
  shows "relaxed_action a"
  using assms unfolding relaxed_action_def by simp

lemma relaxed_action_preD [dest]: "relaxed_action a \<Longrightarrow> is_pos_conj (ac_pre a)"
  unfolding relaxed_action_def by simp

lemma relaxed_action_delD [dest]: "relaxed_action a \<Longrightarrow> dels (ac_eff a) = []"
  unfolding relaxed_action_def by simp

definition (in ast_classical_domain) "relaxed_dom \<equiv>
  normalized_dom \<and> (\<forall>a \<in> set (actions D). relaxed_action a)"

lemma (in ast_classical_domain) relaxed_domI [intro]:
  assumes "normalized_dom" and "\<And>a. a \<in> set (actions D) \<Longrightarrow> relaxed_action a"
  shows "relaxed_dom"
  using assms unfolding relaxed_dom_def by blast

lemma (in ast_classical_domain) relaxed_dom_normedD [dest]: "relaxed_dom \<Longrightarrow> normalized_dom"
  unfolding relaxed_dom_def by simp

lemma (in ast_classical_domain) relaxed_dom_actionD [dest]:
  "relaxed_dom \<Longrightarrow> a \<in> set (actions D) \<Longrightarrow> relaxed_action a"
  unfolding relaxed_dom_def by blast

locale relaxed_domain = normalized_domain +
  assumes relaxed_dom: relaxed_dom

definition (in ast_classical_problem) "relaxed_prob \<equiv> 
  normalized_prob \<and> is_pos_conj (goal P) \<and> relaxed_dom"

lemma (in ast_classical_problem) relaxed_probI [intro]:
  assumes "normalized_prob" and "is_pos_conj (goal P)"
    and "\<And>a. a \<in> set (actions D) \<Longrightarrow> relaxed_action a"
  shows "relaxed_prob"
proof -
  have "normalized_dom"
    using assms(1) unfolding normalized_prob_def normalized_dom_def typeless_classical_problem_def
    by blast
  thus ?thesis using assms unfolding relaxed_prob_def relaxed_dom_def by blast
qed

lemma (in ast_classical_problem) relaxed_prob_normedD [dest]: "relaxed_prob \<Longrightarrow> normalized_prob"
  unfolding relaxed_prob_def by simp

lemma (in ast_classical_problem) relaxed_prob_goalD [dest]: "relaxed_prob \<Longrightarrow> is_pos_conj (goal P)"
  unfolding relaxed_prob_def by simp

lemma (in ast_classical_problem) relaxed_prob_actionD [dest]:
  "relaxed_prob \<Longrightarrow> a \<in> set (actions D) \<Longrightarrow> relaxed_action a"
  unfolding relaxed_prob_def relaxed_dom_def by blast

locale relaxed_problem = normalized_problem +
  assumes relaxed_prob: relaxed_prob

sublocale relaxed_problem \<subseteq> relaxed_domain D
  using relaxed_prob normalized_dom relaxed_prob_def relaxed_dom_def
  by (unfold_locales) simp

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
  (\<forall>p \<in> set (predicates D). grounded_pred p) \<and>
  consts D = [] \<and>
  (\<forall>a \<in> set (actions D). grounded_ac a)"

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