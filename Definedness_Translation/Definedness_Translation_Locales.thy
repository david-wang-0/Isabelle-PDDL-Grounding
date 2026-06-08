theory Definedness_Translation_Locales
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Tree_Decomp_Grounding_Common.Normalization_Definitions
    Tree_Decomp_Grounding_Common.PDDL_Sema_Supplement
    Tree_Decomp_Grounding_Common.String_Utils
begin

section \<open>Definedness Translation Definitions and Locales\<close>

text \<open>Convert numeric definedness into propositional predicates.
  Replaces reflexive numeric equalities (which represent definedness) with
  a propositional predicate \<open>Defined_f\<close>. Also ensures that assigning to a PNE
  makes it defined, and requiring a PNE on the RHS of an assignment requires
  it to be defined.

  The generated predicate names carry a \<open>Defined_\<close> token but are prefixed by a
  domain-fresh \<open>safe_prefix\<close> of the existing predicate names, so they cannot
  collide with declared predicates. The name-generating functions are therefore
  parameterised by this prefix \<open>pfx\<close>, which is instantiated to \<open>def_prefix\<close> in
  the domain/problem context.\<close>

subsection \<open>Name generation\<close>

definition pne_to_def_atom :: "name \<Rightarrow> 'ent primitive_numeric_expression \<Rightarrow> 'ent atom" where
  "pne_to_def_atom pfx p = (case p of PNE (Func n) args \<Rightarrow> predAtm (Pred (pfx + n)) args)"

fun def_translate_atom :: "name \<Rightarrow> 'ent atom \<Rightarrow> 'ent atom" where
  "def_translate_atom pfx (numericEqAtm (FunctionExpr p) (FunctionExpr p')) =
    (if p = p' then pne_to_def_atom pfx p else numericEqAtm (FunctionExpr p) (FunctionExpr p'))"
| "def_translate_atom pfx a = a"

definition def_translate_fmla :: "name \<Rightarrow> 'ent atom formula \<Rightarrow> 'ent atom formula" where
  "def_translate_fmla pfx f = map_formula (def_translate_atom pfx) f"

subsection \<open>Collecting the PNEs of an effect\<close>

definition rhs_pnes_num_eff :: "'ent numeric_effect \<Rightarrow> 'ent primitive_numeric_expression list" where
  "rhs_pnes_num_eff eff = (case eff of
    NumericEffect _ _ e \<Rightarrow> enumerate_primitive_numeric_expressions e)"

fun rhs_pnes_eff :: "'ent ast_effect \<Rightarrow> 'ent primitive_numeric_expression list" where
  "rhs_pnes_eff (Effect _ _ ne) = concat (map rhs_pnes_num_eff ne)"

definition lhs_pnes_num_eff :: "'ent numeric_effect \<Rightarrow> 'ent primitive_numeric_expression list" where
  "lhs_pnes_num_eff eff = (case eff of
    NumericEffect numeric_effect_op.Assign p _ \<Rightarrow> [p] | _ \<Rightarrow> [])"

fun lhs_pnes_eff :: "'ent ast_effect \<Rightarrow> 'ent primitive_numeric_expression list" where
  "lhs_pnes_eff (Effect _ _ ne) = concat (map lhs_pnes_num_eff ne)"

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

definition def_predicate_decl :: "name \<Rightarrow> function_decl \<Rightarrow> predicate_decl" where
  "def_predicate_decl pfx d = (case d of FuncDecl (Func n) ts \<Rightarrow> PredDecl (Pred (pfx + n)) ts)"

text \<open>Extract from an initial-state function assignment
  \<open>(= (f args) c)\<close> the definedness fact \<open>Defined_f args\<close>.\<close>

definition init_def_fact :: "name \<Rightarrow> object atom formula \<Rightarrow> object atom formula option" where
  "init_def_fact pfx f = (case f of
      Atom (numericEqAtm (FunctionExpr l) (ConstantExpr _)) \<Rightarrow> Some (Atom (pne_to_def_atom pfx l))
    | _ \<Rightarrow> None)"

subsection \<open>Domain-fresh prefix\<close>

context domain_signature begin

text \<open>A prefix fresh w.r.t. the declared predicate names, extended with the
  \<open>Defined_\<close> token. Freshness follows from \<open>safe_prefix_correct\<close>.\<close>

definition "def_prefix \<equiv> safe_prefix pred_names + STR ''Defined_''"

end

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
  the structural invariant established by \<open>Definedness_Normalization\<close> and
  preserved by \<open>Precondition_Normalization\<close>; it confines every reflexive
  definedness atom \<open>numericEqAtm (FunctionExpr p) (FunctionExpr p)\<close> to a positive
  top-level conjunct, which is exactly what makes the numeric-to-propositional
  \<open>def_translate\<close> rewrite truth-preserving under \<open>\<Turnstile>\<^sub>m\<close>'s strict
  (three-valued) definedness semantics.\<close>

locale def_explicated_conj_problem_dt =
  wf_ast_classical_problem_dt + def_explicated_conj_problem

end
