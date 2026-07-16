theory Classical_Grounded_PDDL_Locales
imports "Classical_Planning.Classical_Abstract_Syntax"
    Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement
    Grounding_Classical_Common.Classical_PDDL_Normalization
    Grounding_Utils.Grounding_Utils
    Grounding_Utils.String_Utils Grounding_Grounded_PDDL.Grounded_PDDL
begin

type_synonym facty = "object atom formula"

subsection \<open>Introduction / elimination rules for the conjunctive target predicates\<close>

text \<open>Rather than repeatedly \<open>unfolding\<close> the definitions and splitting with \<open>intro conjI\<close>, we
  give each conjunctive predicate a proper introduction rule (declared \<open>[intro]\<close>) and the
  matching destruction rules (declared \<open>[dest]\<close>).\<close>

context ast_classical_domain begin

lemma grounded_domI [intro]:
  assumes "types D = []" "\<forall>p \<in> set (predicates D). grounded_pred p"
    "consts D = []" "\<forall>f \<in> set (functions D). grounded_func f"
    "\<forall>a \<in> set (actions D). grounded_ac a"
  shows grounded_dom
  unfolding grounded_dom_def using assms by blast

lemma grounded_domD [dest]:
  assumes grounded_dom
  shows "types D = []" "\<forall>p \<in> set (predicates D). grounded_pred p"
    "consts D = []" "\<forall>f \<in> set (functions D). grounded_func f"
    "\<forall>a \<in> set (actions D). grounded_ac a"
  using assms unfolding grounded_dom_def by blast+

lemma wf_classical_domainI [intro]:
  assumes wf_domain_signature "distinct (map ac_name (actions D))"
    "\<forall>a \<in> set (actions D). wf_classical_action_schema a"
  shows wf_classical_domain
  unfolding wf_classical_domain_def using assms by blast

lemma wf_classical_domainD [dest]:
  assumes wf_classical_domain
  shows wf_domain_signature "distinct (map ac_name (actions D))"
    "\<forall>a \<in> set (actions D). wf_classical_action_schema a"
  using assms unfolding wf_classical_domain_def by blast+

end

lemma (in domain_signature) wf_classical_action_schemaI [intro]:
  assumes "distinct (map fst (ac_params ac))"
    "wf_fmla (ac_tyt ac) (ac_pre ac)" "wf_effect (ac_tyt ac) (ac_eff ac)"
  shows "wf_classical_action_schema ac"
  unfolding wf_classical_action_schema_alt using assms by blast

context ast_classical_problem begin

lemma grounded_probI [intro]:
  assumes grounded_dom "objects P = []"
  shows grounded_prob
  unfolding grounded_prob_def using assms by blast

lemma grounded_probD [dest]:
  assumes grounded_prob shows grounded_dom "objects P = []"
  using assms unfolding grounded_prob_def by blast+

lemma wf_classical_problemI [intro]:
  assumes wf_classical_domain wf_problem_signature "distinct (init P)"
    "\<forall>f \<in> set (init P). wf_fmla_atom objT f \<or> wf_func_assign f"
    "wf_fmla objT (goal P)"
  shows wf_classical_problem
  unfolding wf_classical_problem_def using assms by blast

lemma wf_classical_problemD [dest]:
  assumes wf_classical_problem
  shows wf_classical_domain wf_problem_signature "distinct (init P)"
    "\<forall>f \<in> set (init P). wf_fmla_atom objT f \<or> wf_func_assign f"
    "wf_fmla objT (goal P)"
  using assms unfolding wf_classical_problem_def by blast+

end

text \<open>The grounder is parameterised by the lists of achievable facts and applicable plan actions.\<close>

locale grounder = ast_classical_problem +
  fixes facts :: "facty list" and ops :: "ast_classical_plan_action list"
begin

text \<open>Fresh, distinct nullary predicate names for the achievable facts, and fresh,
  distinct action names for the applicable ops, via the \<^const>\<open>distinct_strings_lit\<close>
  machinery of \<^theory>\<open>Grounding_Utils.String_Utils\<close> (\<^const>\<open>name\<close> is now
  \<^typ>\<open>String.literal\<close>, so the old \<open>char list\<close> padding/\<open>show\<close> mangling is replaced by
  the \<open>String.literal\<close>-native unique-name helpers).\<close>
definition "fact_names \<equiv> map Pred (distinct_strings_lit (length facts))"
definition "fact_map \<equiv> map_of (zip facts fact_names)"

text \<open>The fluent analogue of \<open>fact_names\<close>/\<open>fact_map\<close>: the ground fluents (primitive numeric
  expressions) occurring in the reachable ops' ground actions, and fresh nullary function names for
  them. Predicate and function names live in separate namespaces (\<^const>\<open>Pred\<close> vs \<^const>\<open>Func\<close>),
  so reusing the \<open>distinct_strings_lit\<close> pool is clash-free.\<close>
definition op_fluents :: "ast_classical_plan_action \<Rightarrow> object primitive_numeric_expression list" where
  "op_fluents \<pi> = (let ga = the (res_inst \<pi>) in
     formula_enumerate_primitive_numeric_expressions (precondition ga)
     @ map (\<lambda>ne. case ne of NumericEffect _ l _ \<Rightarrow> l) (numeric_effects (effect ga))
     @ ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ga))"

definition "fluents \<equiv> remdups (concat (map op_fluents ops))"
definition "fluent_names \<equiv> map Func (distinct_strings_lit (length fluents))"
definition "fluent_map \<equiv> map_of (zip fluents fluent_names)"

text \<open>Re-index a ground fluent / numeric expression / numeric effect to nullary form
  (\<open>fuel(c) \<mapsto> fuel_c()\<close>), mirroring \<open>ground_fmla\<close> on atoms.\<close>
definition ground_pne :: "object primitive_numeric_expression \<Rightarrow> 'a primitive_numeric_expression" where
  "ground_pne fl = PNE (the (fluent_map fl)) []"

fun ground_numexp :: "object numeric_expression \<Rightarrow> 'a numeric_expression" where
  "ground_numexp (ConstantExpr r) = ConstantExpr r"
| "ground_numexp DurationExpr = DurationExpr"
| "ground_numexp PiExpr = PiExpr"
| "ground_numexp (AddExpr x y) = AddExpr (ground_numexp x) (ground_numexp y)"
| "ground_numexp (SubExpr x y) = SubExpr (ground_numexp x) (ground_numexp y)"
| "ground_numexp (MulExpr x y) = MulExpr (ground_numexp x) (ground_numexp y)"
| "ground_numexp (DivExpr x y) = DivExpr (ground_numexp x) (ground_numexp y)"
| "ground_numexp (SinExpr x) = SinExpr (ground_numexp x)"
| "ground_numexp (CosExpr x) = CosExpr (ground_numexp x)"
| "ground_numexp (ExpExpr x) = ExpExpr (ground_numexp x)"
| "ground_numexp (FunctionExpr fl) = FunctionExpr (ground_pne fl)"

definition ground_neff :: "object numeric_effect \<Rightarrow> 'a numeric_effect" where
  "ground_neff ne =
     (case ne of NumericEffect opr l r \<Rightarrow> NumericEffect opr (ground_pne l) (ground_numexp r))"

text \<open>Grounded fluents/expressions/effects are nullary, hence invariant under term substitution.\<close>
lemma ground_pne_subst: "map_primitive_numeric_expression f (ground_pne fl) = ground_pne fl"
  by (simp add: ground_pne_def)

lemma ground_numexp_subst: "map_numeric_expression f (ground_numexp e) = ground_numexp e"
  by (induction e) (simp_all add: ground_pne_subst)

lemma ground_neff_subst: "map_numeric_effect f (ground_neff x) = ground_neff x"
  by (simp add: ground_neff_def ground_pne_subst ground_numexp_subst split: numeric_effect.split)

(* As this signature reveals, this function has to be handled with care,
  since a new type parameter appears from nowhere.
  In code, 'a is always object. In proofs, however, it is sometimes term, too. *)
fun ground_fmla :: "object atom formula \<Rightarrow> 'a atom formula" where
  "ground_fmla \<bottom> = \<bottom>" |
  "ground_fmla (Atom (eqAtm a b)) = (if a = b then \<^bold>\<not>\<bottom> else \<bottom>)" |
  "ground_fmla (\<^bold>\<not> (Atom (eqAtm a b))) = (if a = b then \<bottom> else \<^bold>\<not>\<bottom>)" |
  "ground_fmla (Atom (numericEqAtm l r)) = Atom (numericEqAtm (ground_numexp l) (ground_numexp r))" |
  "ground_fmla (Atom (numericLessAtm l r)) = Atom (numericLessAtm (ground_numexp l) (ground_numexp r))" |
  "ground_fmla (Atom (numericLEAtm l r)) = Atom (numericLEAtm (ground_numexp l) (ground_numexp r))" |
  "ground_fmla (Atom (numericGreaterAtm l r)) = Atom (numericGreaterAtm (ground_numexp l) (ground_numexp r))" |
  "ground_fmla (Atom (numericGEAtm l r)) = Atom (numericGEAtm (ground_numexp l) (ground_numexp r))" |
  "ground_fmla (Atom patm) = Atom (predAtm (the (fact_map (Atom patm))) [])" |
  "ground_fmla (\<^bold>\<not> \<phi>) = \<^bold>\<not> (ground_fmla \<phi>)" |
  "ground_fmla (\<phi> \<^bold>\<and> \<psi>) = ground_fmla \<phi> \<^bold>\<and> ground_fmla \<psi>" |
  "ground_fmla (\<phi> \<^bold>\<or> \<psi>) = ground_fmla \<phi> \<^bold>\<or> ground_fmla \<psi>" |
  "ground_fmla (\<phi> \<^bold>\<rightarrow> \<psi>) = ground_fmla \<phi> \<^bold>\<rightarrow> ground_fmla \<psi>"

(* in code, 'a=term. In proofs, 'a can be object, too *)
fun ga_pre :: "ground_action \<Rightarrow> 'a atom formula" where
  "ga_pre (GroundAction pre eff) = ground_fmla pre"

(* in code, 'a=term. In proofs, 'a can be object, too. The grounded effect is purely
  propositional, so it carries no numeric effects. *)
fun ga_eff :: "ground_action \<Rightarrow> 'a ast_effect" where
  "ga_eff (GroundAction pre (Effect a d ne)) =
    Effect (map ground_fmla a) (map ground_fmla d) (map ground_neff ne)"

definition "op_names \<equiv> distinct_strings_lit (length ops)"

definition ground_ac :: "ast_classical_plan_action \<Rightarrow> name \<Rightarrow> ast_classical_action_schema" where
  "ground_ac \<pi> n =
    (let ga = the (res_inst \<pi>) in
    SimpleActionSchema (ActionHead n []) (SimpleActionBody (ga_pre ga) (ga_eff ga)))"

definition ground_dom :: "ast_classical_domain" where
  "ground_dom \<equiv> Domain
    []
    (map (\<lambda>p. PredDecl p []) fact_names)
    (map (\<lambda>f. FuncDecl f []) fluent_names)
    []
    (map2 ground_ac ops op_names)"

definition ground_prob :: "ast_classical_problem" where
  "ground_prob \<equiv> Problem
    ground_dom
    []
    (map ground_fmla (init P))
    (ground_fmla (goal P))"


definition "op_map \<equiv> map_of (zip op_names ops)"

fun restore_ground_pa :: "ast_classical_plan_action \<Rightarrow> ast_classical_plan_action" where
  "restore_ground_pa (SimplePlanAction n args) = the (op_map n)"

abbreviation restore_ground_plan :: "ast_classical_plan_action list \<Rightarrow> ast_classical_plan_action list" where
  "restore_ground_plan \<pi>s \<equiv> map restore_ground_pa \<pi>s"

end


text \<open>Some of these may follow from one another\<close>

text \<open>\<open>achievable\<close> ranges over \<^typ>\<open>fact\<close> (\<open>predicate \<times> object list\<close>) whereas the grounder's
  \<open>facts\<close> are \<^typ>\<open>facty\<close> formulas; this lifts a reachable fact to its formula.\<close>
abbreviation (in grounder) fact_to_facty :: "fact \<Rightarrow> facty" where
  "fact_to_facty f \<equiv> Atom (uncurry predAtm f)"

text \<open>The \<^emph>\<open>minimal\<close> reachability/well-formedness assumptions the numeric-fluent-retaining grounder
  needs: the input problem is well-formed, the reachable-op list \<open>ops\<close> is distinct, over-approximates
  the applicable actions, and every op is a well-formed plan action. The numeric-fluent-retaining
  grounder (theory \<open>Numeric_Grounder\<close>, downstream) is based on this weaker locale: it grounds the
  un-relaxed problem \<open>P\<^sub>T\<close> keeping its numeric preconditions/effects and function assignments verbatim
  (via a \<open>term.CONST\<close> lift, undone by instantiate-at-\<open>[]\<close>), so it never propositionalises an atom and
  hence needs \<^emph>\<open>none\<close> of the coverage / \<open>facts\<close> assumptions --- those (and \<open>covered\<close>, which rejects
  numeric atoms outright) are what the \<^emph>\<open>propositional\<close> grounder needs, and they move to
  \<open>wf_grounder\<close> below.\<close>
locale wf_grounder_num = grounder +
  assumes
    wf_problem: "wf_classical_problem" and
    ops_dist: "distinct ops" and
    all_ops: "set ops \<supseteq> {\<pi>. applicable \<pi>}" and
    (* If "set ops = {\<pi>. applicable \<pi>}", this follows: *)
    ops_wf: "\<forall>\<pi> \<in> set ops. wf_classical_plan_action \<pi>"

text \<open>The \<^emph>\<open>covered\<close> numeric grounder: \<^locale>\<open>wf_grounder_num\<close> plus a reachable \<open>facts\<close> list that is
  well-formed and covers every op's precondition/effect predicate atoms and the goal, so the shared
  \<open>ground_fmla\<close> / \<open>ga_eff\<close> re-indexing of \<^emph>\<open>predicate\<close> atoms onto nullary \<open>predAtm\<close>s
  is faithful. Numeric atoms/effects are \<^emph>\<open>allowed\<close> here (they re-index onto nullary fluents); this
  is the layer at which the nullary-fluent-retaining grounded problem \<open>ground_prob\<close> lives.\<close>
locale wf_grounder_cov = wf_grounder_num +
  assumes
    facts_dist: "distinct facts" and
    all_facts: "fact_to_facty ` {a. achievable a} \<subseteq> set facts" and
    facts_wf: "\<forall>a \<in> set facts. wf_fmla_atom objT a" and (* If "set facts = {a. achievable a}", this follows. *)
    effs_covered: "\<forall>\<pi> \<in> set ops. (let eff = effect (the (res_inst \<pi>)) in
      \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)" and
    pres_covered: "\<forall>\<pi> \<in> set ops. covered (precondition (the (res_inst \<pi>))) facts" and
    goal_covered: "covered (goal P) facts"

text \<open>The \<^emph>\<open>propositional\<close>/STRIPS grounder = the covered numeric grounder plus the actual
  \<^emph>\<open>no-fluents\<close> assumptions: the initial state has no function assignments (it is purely
  propositional) and the applicable ops carry no numeric effects. Under these the shared grounder
  emits no numeric atom or effect, so the grounded problem is numeric-free --- these hold trivially
  once numerics have been compiled away upstream. So \<^bold>\<open>the STRIPS grounder is the numeric grounder
  (\<^locale>\<open>wf_grounder_cov\<close>) with the two numeric-freeness assumptions added\<close>.\<close>
locale wf_grounder = wf_grounder_cov +
  assumes
    init_props: "\<forall>f \<in> set (init P). is_predAtom f" and
    ops_no_num: "\<forall>\<pi> \<in> set ops. numeric_effects (effect (the (res_inst \<pi>))) = []"

text \<open>
The last two conditions can be satisfied by instantiating every \<pi>\<in>ops and adding all missing atoms
to \<open>facts\<close>. I don't need to implement this for my grounder, but you are welcome to.
\<close>

abbreviation (in grounder) "D\<^sub>G \<equiv> ground_dom"
abbreviation (in grounder) "P\<^sub>G \<equiv> ground_prob"

sublocale wf_grounder_num \<subseteq> wf_ast_classical_problem P
  apply (unfold_locales)
  using wf_problem unfolding wf_classical_problem_def by simp

sublocale grounder \<subseteq> dg: ast_classical_domain D\<^sub>G .
sublocale grounder \<subseteq> pg: ast_classical_problem P\<^sub>G .

end
