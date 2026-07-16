theory Numeric_Free
  imports Classical_PDDL_Normalization
begin

section \<open>Numeric-freeness (the propositional fragment)\<close>

text \<open>The verified grounding pipeline can compile to two backends:

  \<^enum> the AFP \<^emph>\<open>verified SAT-based planner\<close> (\<open>Verified_SAT_Based_AI_Planning.STRIPS_Semantics\<close>),
    whose task type \<open>'v strips_problem\<close> is \<^emph>\<open>purely propositional\<close> (boolean state variables,
    no fluents, no arithmetic); and
  \<^enum> (future) an \<^emph>\<open>SMT solver\<close> backend, which \<^emph>\<open>can\<close> handle numeric fluents/arithmetic natively.

  The grounder itself is faithful: the grounded problem still structurally carries numeric
  conditions and effects (it is exact w.r.t. the relaxed problem, which over-approximates the
  exact normalised problem, which is exact w.r.t. the original lifted problem). Numeric-freeness
  is therefore \<^emph>\<open>not\<close> a guarantee of the grounder; it is an \<^emph>\<open>input restriction\<close> that we carry
  through the pipeline and \<^emph>\<open>check\<close> (it is decidable) before taking the propositional / STRIPS
  branch.

  \<^bold>\<open>Numeric planning is implementable\<close> by dropping the \<open>numeric_free_problem\<close> restriction and
  routing the (numeric) grounded problem to the SMT backend instead of restricting it
  to STRIPS: an untrusted SMT solver returns a candidate plan that the verified PDDL plan
  validator checks (the plan is the certificate; soundness is for free), with the no-plan
  direction certified later via an SMT proof (Alethe) checked through Isabelle's proof
  reconstruction. None of the definitions below preclude that; they only \<^emph>\<open>identify\<close> the
  propositional fragment that the STRIPS backend supports.\<close>

subsection \<open>Numeric-free locales\<close>

text \<open>The structural numeric-freeness predicates (\<^const>\<open>is_numeric_atom\<close>, \<^const>\<open>num_free_fmla\<close>,
  \<^const>\<open>num_free_eff\<close>, \<^const>\<open>num_free_ac\<close>, \<^const>\<open>ast_classical_domain.num_free_dom\<close>,
  \<^const>\<open>ast_classical_problem.num_free_prob\<close>) are defined in
  \<^theory>\<open>Grounding_Classical_Common.Classical_PDDL_Normalization\<close> (they must precede
  \<^locale>\<open>relaxed_problem\<close>, which now carries \<open>num_free_prob\<close> as an assumption). Here we package the
  restriction as locales, in the style of \<^locale>\<open>restrict_classical_problem\<close>.\<close>
locale numeric_free_domain = ast_classical_domain +
  assumes num_free_dom: num_free_dom

locale numeric_free_problem = ast_classical_problem +
  assumes num_free_prob: num_free_prob
begin
sublocale numeric_free_domain D
  using num_free_prob unfolding num_free_prob_def by unfold_locales blast
end

subsection \<open>Decidability: numeric-freeness is an executable check\<close>

text \<open>All predicates above are executable, so a problem can be \<^emph>\<open>checked\<close> for numeric-freeness
  before committing to the propositional / STRIPS branch of the pipeline.\<close>
lemmas num_free_code =
  is_numeric_atom.simps num_free_fmla.simps num_free_eff.simps
  num_free_ac_def ast_classical_domain.num_free_dom_def ast_classical_problem.num_free_prob_def

end
