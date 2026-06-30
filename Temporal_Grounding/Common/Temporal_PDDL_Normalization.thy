theory Temporal_PDDL_Normalization
  imports "Temporal_Planning.Temporal_Well_Formedness"
    "Grounding_Common.PDDL_Normalization"
    "Grounding_Common.Formula_Utils"
begin

section \<open>Temporal PDDL Normalization Locales and Assumptions\<close>

text \<open>
  This theory mirrors the classical PDDL normalization locales but adapts them
  for the temporal planning AST (which includes durative actions, timed conditions,
  and timed effects).
\<close>

abbreviation "ac_head \<equiv> ast_temporal_action_schema.head"
abbreviation "ac_params a \<equiv> ast_action_head.parameters (ac_head a)"

subsection \<open> Typeless Temporal PDDL \<close>

definition (in ast_temporal_domain) "typeless_temporal_domain \<equiv>
    typeless_domain_signature
    \<and> (\<forall>ac \<in> set (actions D). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>)"

locale typeless_temporal_domain = wf_ast_temporal_domain +
  assumes typeless_temporal_domain: typeless_temporal_domain

sublocale typeless_temporal_domain \<subseteq> typeless_domain_signature "types D" "predicates D" "functions D" "consts D"
  using typeless_temporal_domain typeless_temporal_domain_def
  by unfold_locales simp

definition (in ast_temporal_problem) "typeless_temporal_problem \<equiv>
  typeless_temporal_domain \<and> (\<forall>(n, T) \<in> set (objects P). T = \<omega>)"

locale typeless_temporal_problem = wf_ast_temporal_problem +
  assumes typeless_temporal_problem: typeless_temporal_problem

sublocale typeless_temporal_problem \<subseteq> typeless_temporal_domain D
  using typeless_temporal_problem typeless_temporal_problem_def by (unfold_locales) blast

sublocale typeless_temporal_problem \<subseteq> 
    typeless_problem_signature "types D" "predicates D" "functions D" "consts D" "objects P"
  apply unfold_locales
  using typeless_temporal_problem 
  unfolding typeless_temporal_problem_def typeless_temporal_domain_def 
  unfolding typeless_domain_signature_def typeless_problem_signature_def
  by simp

subsection \<open> Precondition Normalization (DNF / Conjunctive Preconditions) \<close>

definition (in ast_temporal_domain) "prec_normed_dom \<equiv>
  \<forall>ac \<in> set (actions D). (case ac of
    SimpleActionSchema h b \<Rightarrow> is_conj (ast_simple_action_body.precondition b)
    | DurativeActionSchema h b \<Rightarrow> \<forall>(t, c) \<in> set (ast_temporal_durative_action_body.condition b). is_conj c)"

locale prec_normed_domain = wf_ast_temporal_domain +
  assumes prec_normed_dom: prec_normed_dom

subsection \<open> Complete Normalization (Typeless + Conjunctive) \<close>

definition (in ast_temporal_domain) "normalized_dom \<equiv> typeless_temporal_domain \<and> prec_normed_dom"

locale normalized_domain = wf_ast_temporal_domain +
  assumes normalized_dom: normalized_dom

sublocale normalized_domain \<subseteq> typeless_temporal_domain D
  using normalized_dom normalized_dom_def by (unfold_locales) simp

definition (in ast_temporal_problem) "normalized_prob \<equiv>
  typeless_temporal_problem \<and> prec_normed_dom \<and> is_conj (goal P)"

locale normalized_problem = wf_ast_temporal_problem +
  assumes normalized_prob: normalized_prob

sublocale normalized_problem \<subseteq> normalized_domain D
  using normalized_prob normalized_dom_def normalized_prob_def typeless_temporal_problem_def
  by (unfold_locales) blast

sublocale normalized_problem \<subseteq> typeless_temporal_problem P
  using normalized_prob normalized_prob_def by (unfold_locales) simp

subsection \<open> Grounded Temporal PDDL \<close>

fun grounded_temporal_ac :: "ast_temporal_action_schema \<Rightarrow> bool" where
  "grounded_temporal_ac (SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff)) \<longleftrightarrow> params = []"
| "grounded_temporal_ac (DurativeActionSchema (ActionHead n params) (DurativeActionBody dc cond deff)) \<longleftrightarrow> params = []"

definition (in ast_temporal_domain) "grounded_temporal_dom \<equiv>
  types D = [] \<and>
  (\<forall>p \<in> set (predicates D). grounded_pred p) \<and>
  (\<forall>f \<in> set (functions D). grounded_func f) \<and>
  consts D = [] \<and>
  (\<forall>a \<in> set (actions D). grounded_temporal_ac a)"

locale grounded_temporal_domain = wf_ast_temporal_domain +
  assumes grounded_temporal_dom: grounded_temporal_dom

definition (in ast_temporal_problem) "grounded_temporal_prob \<equiv>
  grounded_temporal_dom \<and> objects P = []"

locale grounded_temporal_problem = wf_ast_temporal_problem +
  assumes grounded_temporal_prob: grounded_temporal_prob

sublocale grounded_temporal_problem \<subseteq> grounded_temporal_domain D
  using grounded_temporal_prob grounded_temporal_prob_def by (unfold_locales) simp

subsection \<open> Grounded and Normalized Temporal PDDL \<close>

locale grounded_normalized_temporal_domain = grounded_temporal_domain +
  assumes normed_dom: prec_normed_dom

locale grounded_normalized_temporal_problem = grounded_temporal_problem +
  assumes normed_prob: "prec_normed_dom \<and> is_conj (goal P)"

sublocale grounded_normalized_temporal_problem \<subseteq> grounded_normalized_temporal_domain D
  using normed_prob by (unfold_locales) blast

subsection \<open> Positive Temporal PDDL (positive preconditions; keeps deletes) \<close>

text \<open>Positivity only: positive (negation-free conjunctive) preconditions / timed conditions and goal.
  Unlike the classical \<open>relaxed_\<close> locales this does \<^emph>\<open>not\<close> bundle delete-relaxation (\<open>dels = []\<close>) ---
  it is the positivity half needed by the temporal NTA reduction, which is the real planning problem
  and keeps deletes. Built on \<^locale>\<open>wf_ast_temporal_domain\<close> / \<^locale>\<open>wf_ast_temporal_problem\<close>,
  orthogonal to grounded-ness and normalization, so a consumer can bundle it with
  \<^locale>\<open>grounded_temporal_problem\<close> independently.\<close>

fun positive_temporal_ac :: "ast_temporal_action_schema \<Rightarrow> bool" where
  "positive_temporal_ac (SimpleActionSchema h (SimpleActionBody pre eff)) \<longleftrightarrow> is_pos_conj pre"
| "positive_temporal_ac (DurativeActionSchema h (DurativeActionBody dc cond deff))
     \<longleftrightarrow> (\<forall>(t, c) \<in> set cond. is_pos_conj c)"

definition (in ast_temporal_domain) "positive_temporal_dom \<equiv>
  \<forall>a \<in> set (actions D). positive_temporal_ac a"

lemma (in ast_temporal_domain) positive_temporal_domI [intro]:
  assumes "\<And>a. a \<in> set (actions D) \<Longrightarrow> positive_temporal_ac a"
  shows positive_temporal_dom
  using assms unfolding positive_temporal_dom_def by blast

lemma (in ast_temporal_domain) positive_temporal_domD [dest]:
  "positive_temporal_dom \<Longrightarrow> a \<in> set (actions D) \<Longrightarrow> positive_temporal_ac a"
  unfolding positive_temporal_dom_def by blast

locale positive_temporal_domain = wf_ast_temporal_domain +
  assumes positive_temporal_dom: positive_temporal_dom

definition (in ast_temporal_problem) "positive_temporal_prob \<equiv>
  positive_temporal_dom \<and> is_pos_conj (goal P)"

lemma (in ast_temporal_problem) positive_temporal_probI [intro]:
  assumes positive_temporal_dom
    and "is_pos_conj (goal P)"
  shows positive_temporal_prob
  using assms unfolding positive_temporal_prob_def by blast

lemma (in ast_temporal_problem) positive_temporal_prob_domD [dest]:
  "positive_temporal_prob \<Longrightarrow> positive_temporal_dom"
  unfolding positive_temporal_prob_def by simp

lemma (in ast_temporal_problem) positive_temporal_prob_goalD [dest]:
  "positive_temporal_prob \<Longrightarrow> is_pos_conj (goal P)"
  unfolding positive_temporal_prob_def by simp

lemma (in ast_temporal_problem) positive_temporal_prob_acD [dest]:
  "positive_temporal_prob \<Longrightarrow> a \<in> set (actions D) \<Longrightarrow> positive_temporal_ac a"
  unfolding positive_temporal_prob_def positive_temporal_dom_def by blast

locale positive_temporal_problem = wf_ast_temporal_problem +
  assumes positive_temporal_prob: positive_temporal_prob

sublocale positive_temporal_problem \<subseteq> positive_temporal_domain D
  using positive_temporal_prob positive_temporal_prob_def by (unfold_locales) blast

end

