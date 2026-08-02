theory Classical_Grounded_PDDL_Locales
imports "Classical_Planning.Classical_Abstract_Syntax"
    Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement
    Grounding_Classical_Common.Classical_PDDL_Normalization
    Grounding_Utils.Grounding_Utils
    Grounding_Utils.String_Utils Grounding_Grounded_PDDL.Grounded_PDDL
    Classical_Variable_Freeness.Classical_Variable_Freeness
begin

type_synonym facty = "object atom formula"

text \<open>The op-fluent enumeration: the ground fluents (primitive numeric expressions) occurring in a
  plan action's instantiated ground action --- precondition, numeric-effect left-hand sides, and
  numeric right-hand-side expressions.\<close>
definition (in ast_classical_problem) op_fluents :: "ast_classical_plan_action \<Rightarrow> object primitive_numeric_expression list" where
  "op_fluents \<pi> = (let ga = the (res_inst \<pi>) in
     formula_enumerate_primitive_numeric_expressions (precondition ga)
     @ map (\<lambda>ne. case ne of NumericEffect _ l _ \<Rightarrow> l) (numeric_effects (effect ga))
     @ ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ga))"

subsection \<open>The fact folder: folding ground atoms and fluents to nullary form\<close>

text \<open>The second stage of the propositional grounder, parameterised by the achievable-facts list
  \<open>facts\<close> \<^bold>\<open>and\<close> the reachable ground-fluent list \<open>fluents\<close> --- both supplied by whatever provides
  the reachable actions (in the pipeline, the datalog certificate stage; the grounder below derives
  its fluents from the reachable ops). It re-indexes ground predicate atoms onto fresh nullary
  predicates (\<open>fact_names\<close>) and ground fluents onto fresh nullary functions (\<open>fluent_names\<close>);
  \<open>fold_prob\<close> folds an entire \<^emph>\<open>variable-free\<close> problem (the Variable_Freeness stage's output
  shape \<^const>\<open>ast_classical_problem.varfree_prob\<close>) into the fully grounded, nullary-predicate
  form.\<close>

locale fact_folder = ast_classical_problem +
  fixes facts :: "facty list" and fluents :: "object primitive_numeric_expression list"
begin

text \<open>Fresh, distinct nullary predicate names for the achievable facts and fresh nullary function
  names for the reachable fluents, via the \<^const>\<open>distinct_strings_lit\<close> machinery of
  \<^theory>\<open>Grounding_Utils.String_Utils\<close> (\<^const>\<open>name\<close> is now \<^typ>\<open>String.literal\<close>, so the old
  \<open>char list\<close> padding/\<open>show\<close> mangling is replaced by the \<open>String.literal\<close>-native unique-name
  helpers). Predicate and function names live in separate namespaces (\<^const>\<open>Pred\<close> vs
  \<^const>\<open>Func\<close>), so reusing the \<open>distinct_strings_lit\<close> pool is clash-free.\<close>
definition "fact_names \<equiv> map Pred (distinct_strings_lit (length facts))"
definition "fact_map \<equiv> map_of (zip facts fact_names)"

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

text \<open>\<open>achievable\<close> ranges over \<^typ>\<open>fact\<close> (\<open>predicate \<times> object list\<close>) whereas the folder's
  \<open>facts\<close> are \<^typ>\<open>facty\<close> formulas; this lifts a reachable fact to its formula.\<close>
abbreviation fact_to_facty :: "fact \<Rightarrow> facty" where
  "fact_to_facty f \<equiv> Atom (uncurry predAtm f)"

text \<open>Folding a whole variable-free problem: each nullary action schema resolves-and-instantiates
  at the empty argument list (undoing the \<open>term.CONST\<close> lift of the Variable_Freeness stage), and
  its ground body is re-indexed by \<open>ga_pre\<close>/\<open>ga_eff\<close>; the action \<^emph>\<open>name\<close> is kept verbatim.\<close>

definition ac_pa :: "ast_classical_action_schema \<Rightarrow> ast_classical_plan_action" where
  "ac_pa a = SimplePlanAction (ac_name a) []"

definition fold_ac :: "ast_classical_action_schema \<Rightarrow> ast_classical_action_schema" where
  "fold_ac a =
    (let ga = the (res_inst (ac_pa a)) in
    SimpleActionSchema (ActionHead (ac_name a) []) (SimpleActionBody (ga_pre ga) (ga_eff ga)))"

definition fold_dom :: ast_classical_domain where
  "fold_dom \<equiv> Domain
    []
    (map (\<lambda>p. PredDecl p []) fact_names)
    (map (\<lambda>f. FuncDecl f []) fluent_names)
    []
    (map fold_ac (actions (domain P)))"

definition fold_prob :: ast_classical_problem where
  "fold_prob \<equiv> Problem
    fold_dom
    []
    (map ground_fmla (init P))
    (ground_fmla (goal P))"

end

subsection \<open>The one-shot grounder: variable elimination and folding in one step\<close>

text \<open>The grounder is parameterised by the achievable-facts list \<open>facts\<close> on top of the
  variable-freeness name machinery's reachable-op list \<open>ops\<close> (locale \<open>varfree\<close>); its fluents are
  \<^emph>\<open>derived\<close> from the reachable ops, and the folding machinery is the shared
  \<^locale>\<open>fact_folder\<close>, imported below at exactly these derived fluents.\<close>

locale grounder = varfree +
  fixes facts :: "facty list"
begin

definition "fluents \<equiv> remdups (concat (map op_fluents ops))"

end

sublocale grounder \<subseteq> fact_folder P facts fluents .

context grounder begin

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

end


text \<open>Some of these may follow from one another\<close>

text \<open>The \<^emph>\<open>covered\<close> numeric grounder: \<^locale>\<open>varfree_instantiator\<close> plus a reachable \<open>facts\<close> list that is
  well-formed and covers every op's precondition/effect predicate atoms and the goal, so the shared
  \<open>ground_fmla\<close> / \<open>ga_eff\<close> re-indexing of \<^emph>\<open>predicate\<close> atoms onto nullary \<open>predAtm\<close>s
  is faithful. Numeric atoms/effects are \<^emph>\<open>allowed\<close> here (they re-index onto nullary fluents); this
  is the layer at which the nullary-fluent-retaining grounded problem \<open>ground_prob\<close> lives.\<close>
locale wf_grounder_cov = grounder + varfree_instantiator +
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

subsection \<open>Assumption layers for the standalone fact folder\<close>

text \<open>The folder's input obligations, stated on the variable-free problem \<open>P\<close> itself (no ops
  parameter --- the nullary plan actions \<^const>\<open>fact_folder.ac_pa\<close> are determined by the
  problem's own action schemas). Mirrors \<^locale>\<open>wf_grounder_cov\<close>: input well-formed and
  variable-free, \<open>facts\<close> distinct / well-formed / covering everything achievable and every
  predicate atom of the action bodies and goal, \<open>fluents\<close> distinct / well-formed / covering every
  ground fluent of the action bodies.\<close>
locale wf_fact_folder_cov = fact_folder +
  assumes
    wf_problem: "wf_classical_problem" and
    varfree_input: varfree_prob and
    facts_dist: "distinct facts" and
    all_facts: "fact_to_facty ` {a. achievable a} \<subseteq> set facts" and
    facts_wf: "\<forall>a \<in> set facts. wf_fmla_atom objT a" and
    effs_covered: "\<forall>a \<in> set (actions (domain P)). (let eff = effect (the (res_inst (ac_pa a))) in
      \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)" and
    pres_covered: "\<forall>a \<in> set (actions (domain P)). covered (precondition (the (res_inst (ac_pa a)))) facts" and
    goal_covered: "covered (goal P) facts" and
    fluents_dist: "distinct fluents" and
    fluents_wf: "\<forall>fl \<in> set fluents. wf_primitive_numeric_expression objT fl" and
    acs_fluents: "\<forall>a \<in> set (actions (domain P)). set (op_fluents (ac_pa a)) \<subseteq> set fluents"

text \<open>The propositional/STRIPS layer of the folder, mirroring \<^locale>\<open>wf_grounder\<close>: the initial
  state is purely propositional and the (nullary) actions carry no numeric effects.\<close>
locale wf_fact_folder = wf_fact_folder_cov +
  assumes
    init_props: "\<forall>f \<in> set (init P). is_predAtom f" and
    acs_no_num: "\<forall>a \<in> set (actions (domain P)). numeric_effects (effect (the (res_inst (ac_pa a)))) = []"

sublocale wf_fact_folder_cov \<subseteq> wf_ast_classical_problem P
  apply (unfold_locales)
  using wf_problem unfolding wf_classical_problem_def by simp

sublocale fact_folder \<subseteq> fdg: ast_classical_domain fold_dom .
sublocale fact_folder \<subseteq> fpg: ast_classical_problem fold_prob .

abbreviation (in grounder) "D\<^sub>G \<equiv> ground_dom"
abbreviation (in grounder) "P\<^sub>G \<equiv> ground_prob"

sublocale grounder \<subseteq> dg: ast_classical_domain D\<^sub>G .
sublocale grounder \<subseteq> pg: ast_classical_problem P\<^sub>G .

end
