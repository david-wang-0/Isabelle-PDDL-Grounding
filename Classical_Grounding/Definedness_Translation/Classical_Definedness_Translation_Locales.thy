theory Classical_Definedness_Translation_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Grounding_Classical_Common.Classical_PDDL_Normalization
    Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement
    Grounding_Utils.String_Utils Grounding_Definedness_Translation.Definedness_Translation
begin

section \<open>Definedness Translation Definitions and Locales\<close>

text \<open>Convert numeric definedness into propositional predicates.
  Replaces reflexive numeric equalities (which represent definedness) with
  a propositional predicate \<open>Defined_f\<close>. Also ensures that assigning to a PNE
  makes it defined, and requiring a PNE on the RHS of an assignment requires
  it to be defined.

  The generated predicate names sit under a \<open>Defined_\<close> namespace token that
  \<open>fresh_prefix\<close> guarantees is not a prefix of any existing predicate name, so they
  cannot collide with declared predicates. The name-generating functions are therefore
  parameterised by this prefix \<open>pfx\<close>, which is instantiated to \<open>def_prefix\<close> in
  the domain/problem context.\<close>


subsection \<open>Action translation\<close>

fun def_translate_ac :: "name \<Rightarrow> ast_classical_action_schema \<Rightarrow> ast_classical_action_schema" where
  "def_translate_ac pfx (SimpleActionSchema h (SimpleActionBody pre (Effect ads dls neffs))) =
    (let rhs = remdups (rhs_pnes_eff (Effect ads dls neffs));
         lhs = remdups (lhs_pnes_eff (Effect ads dls neffs));
         new_pre_atoms = map (pne_to_def_atom pfx) rhs;
         new_pre = foldr (\<^bold>\<and>) (map Atom new_pre_atoms) (def_translate_fmla pfx pre);
         new_eff_atoms = map (pne_to_def_atom pfx) lhs;
         new_ads = map Atom new_eff_atoms @ ads
     in SimpleActionSchema h (SimpleActionBody new_pre (Effect new_ads dls neffs)))"



subsection \<open>Domain and problem translation\<close>

context ast_classical_domain begin

definition "def_translate_dom \<equiv>
  Domain
    (types D)
    (predicates D @ map (def_predicate_decl def_prefix) (functions D))
    (functions D)
    (consts D)
    (map (def_translate_ac def_prefix) (actions D))"

end

context ast_classical_problem begin

definition "def_translate_prob \<equiv>
  Problem
    def_translate_dom
    (objects P)
    (init P @ remdups (List.map_filter (init_def_fact def_prefix) (init P)))
    (def_translate_fmla def_prefix (goal P))"

end

definition "restore_plan_def_translate \<pi>s \<equiv> \<pi>s"

subsection \<open>Selectors\<close>

abbreviation (in ast_classical_domain) (input) "DT \<equiv> def_translate_dom"
abbreviation (in ast_classical_problem) (input) "PT \<equiv> def_translate_prob"

lemma (in ast_classical_domain) def_translate_dom_sel [simp]:
  "types DT = types D"
  "predicates DT = predicates D @ map (def_predicate_decl def_prefix) (functions D)"
  "functions DT = functions D"
  "consts DT = consts D"
  "actions DT = map (def_translate_ac def_prefix) (actions D)"
  using def_translate_dom_def by simp_all

lemma (in ast_classical_problem) def_translate_prob_sel [simp]:
  "domain PT = DT"
  "objects PT = objects P"
  "init PT = init P @ remdups (List.map_filter (init_def_fact def_prefix) (init P))"
  "goal PT = def_translate_fmla def_prefix (goal P)"
  using def_translate_prob_def by simp_all

subsection \<open>The \<open>*_dt\<close> locale hierarchy\<close>

text \<open>Unlike precondition splitting, definedness translation changes the domain
  signature (it appends the \<open>Defined_\<close> predicates), so \<open>dt.sig\<close> and everything
  derived from it cannot be rewritten back to the input domain. Only the
  type-, function- and constant-level constants are preserved. We therefore set
  up a bare interpretation (as in goal normalization) and prove the
  signature-monotonicity facts explicitly.\<close>

locale ast_classical_domain_dt = ast_classical_domain
sublocale ast_classical_domain_dt \<subseteq> dt: ast_classical_domain DT .

locale wf_ast_classical_domain_dt = wf_ast_classical_domain
sublocale wf_ast_classical_domain_dt \<subseteq> ast_classical_domain_dt .

locale ast_classical_problem_dt = ast_classical_problem
sublocale ast_classical_problem_dt \<subseteq> ast_classical_domain_dt D .
sublocale ast_classical_problem_dt \<subseteq> pt: ast_classical_problem PT .

locale wf_ast_classical_problem_dt = wf_ast_classical_problem
sublocale wf_ast_classical_problem_dt \<subseteq> ast_classical_problem_dt .
sublocale wf_ast_classical_problem_dt \<subseteq> wf_ast_classical_domain_dt D by (unfold_locales)

text \<open>The locale in which the semantic equivalence of the translation is proved:
  a well-formed \<open>*_dt\<close> problem whose action preconditions and goal carry the
  definedness-explicated conjunctive prefix (\<open>is_def_explicated_conj\<close>). This is
  the structural invariant established by \<open>Classical_Definedness_Normalization\<close> and
  preserved by \<open>Classical_Precondition_Normalization\<close>; it confines every reflexive
  definedness atom \<open>numericEqAtm (FunctionExpr p) (FunctionExpr p)\<close> to a positive
  top-level conjunct, which is exactly what makes the numeric-to-propositional
  \<open>def_translate\<close> rewrite truth-preserving under \<open>\<Turnstile>\<^sub>m\<close>'s strict
  (three-valued) definedness semantics.\<close>

locale def_explicated_conj_problem_dt =
  wf_ast_classical_problem_dt + def_explicated_conj_problem

end
