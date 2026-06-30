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

subsection \<open>Numeric atoms and numeric-free formulas\<close>

text \<open>The numeric atoms of the PDDL \<^typ>\<open>'ent atom\<close> type: the arithmetic comparisons. The
  \<^const>\<open>predAtm\<close> and \<^const>\<open>eqAtm\<close> (object equality) constructors are not numeric.\<close>
fun is_numeric_atom :: "'ent atom \<Rightarrow> bool" where
  "is_numeric_atom (numericEqAtm _ _) = True"
| "is_numeric_atom (numericLessAtm _ _) = True"
| "is_numeric_atom (numericLEAtm _ _) = True"
| "is_numeric_atom (numericGreaterAtm _ _) = True"
| "is_numeric_atom (numericGEAtm _ _) = True"
| "is_numeric_atom _ = False"

fun num_free_fmla :: "'ent atom formula \<Rightarrow> bool" where
  "num_free_fmla (Atom a) = (\<not> is_numeric_atom a)"
| "num_free_fmla \<bottom> = True"
| "num_free_fmla (\<^bold>\<not> \<phi>) = num_free_fmla \<phi>"
| "num_free_fmla (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = (num_free_fmla \<phi>\<^sub>1 \<and> num_free_fmla \<phi>\<^sub>2)"
| "num_free_fmla (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = (num_free_fmla \<phi>\<^sub>1 \<and> num_free_fmla \<phi>\<^sub>2)"
| "num_free_fmla (\<phi>\<^sub>1 \<^bold>\<rightarrow> \<phi>\<^sub>2) = (num_free_fmla \<phi>\<^sub>1 \<and> num_free_fmla \<phi>\<^sub>2)"

lemma num_free_fmla_un_and:
  "num_free_fmla F \<Longrightarrow> \<forall>f \<in> set (un_and F). num_free_fmla f"
  by (induction F rule: un_and.induct) auto

lemma num_free_fmla_Atom_predAtom:
  assumes "num_free_fmla (Atom a)" and "\<not> is_eqAtom (Atom a)"
  shows "is_predAtom (Atom a)"
  using assms by (cases a) auto

subsection \<open>Numeric-free effects, actions, domains, problems\<close>

text \<open>A purely propositional effect: its add/delete lists are numeric-free and it carries no
  numeric effects.\<close>
fun num_free_eff :: "'ent ast_effect \<Rightarrow> bool" where
  "num_free_eff (Effect a d n) =
     ((\<forall>\<phi> \<in> set a. num_free_fmla \<phi>) \<and> (\<forall>\<phi> \<in> set d. num_free_fmla \<phi>) \<and> n = [])"

definition num_free_ac :: "ast_classical_action_schema \<Rightarrow> bool" where
  "num_free_ac a \<equiv> num_free_fmla (ac_pre a) \<and> num_free_eff (ac_eff a)"

definition (in ast_classical_domain) num_free_dom :: bool where
  "num_free_dom \<equiv> \<forall>a \<in> set (actions D). num_free_ac a"

definition (in ast_classical_problem) num_free_prob :: bool where
  "num_free_prob \<equiv> num_free_dom \<and> num_free_fmla (goal P) \<and> (\<forall>f \<in> set (init P). num_free_fmla f)"

text \<open>Locales packaging the restriction, in the style of \<^locale>\<open>restrict_classical_problem\<close>.\<close>
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
