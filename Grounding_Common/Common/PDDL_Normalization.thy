theory PDDL_Normalization
  imports "Continuous_Planning.Signatures"
begin

text \<open>AST-agnostic signature-level normalization properties: input restriction and detyping over a
  PDDL domain/problem \<^emph>\<open>signature\<close> (types, predicates, functions, consts). These locales mention only
  the shared signature (not the classical action AST), so they are reusable by any grounder ---
  classical or temporal. The classical-AST counterparts live in
  \<open>Grounding_Classical_Common.Classical_PDDL_Normalization\<close>.\<close>

text \<open> Signature accessors (AST-agnostic). \<close>

abbreviation (in domain_signature) pred_names :: "name list" where
    "pred_names \<equiv> map (predicate.name \<circ> pred) predicates"

abbreviation (in problem_signature) "all_consts \<equiv> consts @ objs"

text \<open> Input Restriction \<close>

abbreviation "\<omega> \<equiv> Either [STR ''object'']"

fun single_type :: "type \<Rightarrow> bool" where
  "single_type (Either ts) \<longleftrightarrow> length ts = 1"
abbreviation single_types :: "('a \<times> type) list \<Rightarrow> bool" where
  "single_types os \<equiv> \<forall>(_, T) \<in> set os. single_type T"

definition (in domain_signature) restrict_dom_sig where
  "restrict_dom_sig \<equiv> single_types consts"

definition (in problem_signature) restrict_prob_sig where
  "restrict_prob_sig \<equiv> restrict_dom_sig \<and> single_types objs"

locale restrict_domain_signature = domain_signature +
  assumes restrict_dom_sig: restrict_dom_sig

locale restrict_problem_signature = problem_signature +
  assumes restrict_prob_sig: restrict_prob_sig

sublocale restrict_problem_signature \<subseteq> restrict_domain_signature
  using restrict_prob_sig restrict_prob_sig_def
  by unfold_locales blast

text \<open>Combined well-formed + restricted signatures. These are convenient to use as a single
  context for proofs that need both the \<open>wf_\<close> assumption and the \<open>restrict_\<close> assumption.\<close>

locale wf_restrict_domain_signature = wf_domain_signature + restrict_domain_signature

locale wf_restrict_problem_signature = wf_problem_signature + restrict_problem_signature

sublocale wf_restrict_problem_signature \<subseteq> wf_restrict_domain_signature ..

text \<open> Type normalization (signature level):
- type hierarchy is empty (implicitly includes ''object'')
- predicate argument types are \<open>Either [''object'']\<close>
- const types are \<open>Either [''object'']\<close> \<close>

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

text \<open> Grounded (nullary) declarations (AST-agnostic). A predicate or function declaration is
  \<^emph>\<open>grounded\<close> when it takes no arguments. These leaf predicates range over the shared declaration
  types, so the classical and temporal grounders both reuse them to state that a grounded domain has
  only nullary predicates and (for the numeric target) nullary numeric fluents. \<close>

fun grounded_pred :: "predicate_decl \<Rightarrow> bool" where
  "grounded_pred (PredDecl n args) \<longleftrightarrow> args = []"

fun grounded_func :: "function_decl \<Rightarrow> bool" where
  "grounded_func (FuncDecl n args) \<longleftrightarrow> args = []"

end
