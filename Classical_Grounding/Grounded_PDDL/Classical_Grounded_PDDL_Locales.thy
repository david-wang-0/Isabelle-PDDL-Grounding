theory Classical_Grounded_PDDL_Locales
imports "Classical_Planning.Classical_Abstract_Syntax"
    Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement
    Grounding_Classical_Common.Classical_PDDL_Normalization
    Grounding_Utils.Grounding_Utils
    Grounding_Utils.String_Utils Grounding_Grounded_PDDL.Grounded_PDDL
    Classical_Variable_Freeness.Classical_Variable_Freeness
begin

type_synonym facty = "object atom formula"

text \<open>\<^const>\<open>covered\<close> is \<^const>\<open>facts_covered\<close> plus the outright rejection of numeric atoms, so
  on a numeric-free formula the two coincide. This is the converse of \<open>covered_imp_covered_num\<close>
  under numeric-freeness.\<close>
lemma covered_of_facts_covered:
  assumes "facts_covered \<phi> facts"
      and "num_free_fmla \<phi>"
  shows "covered \<phi> facts"
  unfolding covered_def
proof
  fix a assume a: "a \<in> atoms \<phi>"
  have nn: "\<not> is_numeric_atom a" using num_free_fmla_atoms[OF assms(2) a] .
  show "(case a of predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> set facts
          | eqAtm x y \<Rightarrow> True | _ \<Rightarrow> False)"
    using nn facts_coveredD[OF assms(1)] a by (cases a) auto
qed

text \<open>The op-fluent enumeration: the ground fluents (primitive numeric expressions) occurring in a
  plan action's instantiated ground action --- precondition, numeric-effect left-hand sides, and
  numeric right-hand-side expressions.\<close>
definition (in ast_classical_problem) op_fluents :: "ast_classical_plan_action \<Rightarrow> object primitive_numeric_expression list" where
  "op_fluents \<pi> = (let ga = the (res_inst \<pi>) in
     formula_enumerate_primitive_numeric_expressions (precondition ga)
     @ map (\<lambda>ne. case ne of NumericEffect _ l _ \<Rightarrow> l) (numeric_effects (effect ga))
     @ ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ga))"

text \<open>\<open>achievable\<close> ranges over \<^typ>\<open>fact\<close> (\<open>predicate \<times> object list\<close>) whereas the folder's
  \<open>facts\<close> are \<^typ>\<open>facty\<close> formulas; this lifts a reachable fact to its formula.\<close>
abbreviation fact_to_facty :: "fact \<Rightarrow> facty" where
  "fact_to_facty f \<equiv> Atom (uncurry predAtm f)"

subsection \<open>The fact folder: folding ground atoms and fluents to nullary form\<close>

text \<open>The second stage of the propositional grounder, parameterised by the achievable-facts list
  \<open>facts\<close> \<^bold>\<open>and\<close> the reachable ground-fluent list \<open>fluents\<close> --- both supplied by whatever provides
  the reachable actions (in the pipeline, the datalog certificate stage; the grounder below derives
  its fluents from the reachable ops). It re-indexes ground predicate atoms onto readable,
  index-tagged nullary predicates (\<open>fact_names\<close>) and ground fluents onto readable, index-tagged
  nullary functions (\<open>fluent_names\<close>);
  \<open>fold_prob\<close> folds an entire \<^emph>\<open>variable-free\<close> problem (the Variable_Freeness stage's output
  shape \<^const>\<open>ast_classical_problem.varfree_prob\<close>) into the fully grounded, nullary-predicate
  form.\<close>

text \<open>Readable string encoders for ground facts and fluents, mirroring \<^const>\<open>readable_pa\<close> of
  the Variable_Freeness stage: the original predicate / function name with each argument object's
  name appended, all joined by underscores. Total --- every non-\<^const>\<open>predAtm\<close> shape (equality,
  numeric atom, compound formula) falls through to the empty string. Those shapes never occur under
  \<open>facts_wf\<close>, and the index suffix added by \<open>fact_names\<close> below keeps the generated names distinct
  even if they did, so the encoders themselves need not be injective. They live at theory level, not
  inside the folder: the names must not depend on the problem parameter.\<close>

fun readable_fact :: "facty \<Rightarrow> String.literal" where
  "readable_fact (Atom (predAtm p args)) =
     foldl (\<lambda>s ob. s + STR ''_'' + obj_str ob) (predicate.name p) args"
| "readable_fact _ = STR ''''"

fun readable_fluent :: "object primitive_numeric_expression \<Rightarrow> String.literal" where
  "readable_fluent (PNE f args) =
     foldl (\<lambda>s ob. s + STR ''_'' + obj_str ob) (func.name f) args"

locale fact_folder = ast_classical_problem +
  fixes facts :: "facty list" and fluents :: "object primitive_numeric_expression list"
begin

text \<open>Readable nullary predicate names for the achievable facts and readable nullary function
  names for the reachable fluents: each folded fact / fluent is named by its \<^emph>\<open>original\<close>
  predicate / function name with the argument objects' names appended, underscore-separated, plus a
  trailing decimal index via \<^const>\<open>idx_name\<close> (\<open>at(c1, rooma) \<mapsto> at_c1_rooma_7\<close>,
  \<open>fuel(c1) \<mapsto> fuel_c1_2\<close>) --- the \<^const>\<open>readable_pa\<close> / \<open>op_names\<close> idiom of the
  Variable_Freeness stage. Since \<open>_\<close> never occurs inside a decimal numeral the index is recoverable
  from the encoding (\<^const>\<open>strip_idx\<close>), so equal names force equal indices
  (\<open>idx_name_inj_idx\<close>) and pairwise distinctness is a \<^emph>\<open>theorem\<close> (\<open>fact_names_dis\<close> /
  \<open>fluent_names_dis\<close>), not an assumption: the readable encodings need not be injective. Predicate
  and function names live in separate namespaces (\<^const>\<open>Pred\<close> vs \<^const>\<open>Func\<close>), so sharing the
  encoding is clash-free.\<close>
definition "fact_names \<equiv>
  map2 (\<lambda>f i. Pred (idx_name (readable_fact f) i)) facts [0..<length facts]"
definition "fact_map \<equiv> map_of (zip facts fact_names)"

definition "fluent_names \<equiv>
  map2 (\<lambda>fl i. Func (idx_name (readable_fluent fl) i)) fluents [0..<length fluents]"
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

subsection \<open>The two-stage grounder: variable-free instantiation followed by fact folding\<close>

text \<open>The reachable ops determine the ground fluents the grounded problem must declare. This is
  the only piece of the (removed) one-shot grounder that the two-stage composite still needs, so it
  lives directly on the assumption-free name-machinery locale \<^locale>\<open>varfree\<close> --- keeping
  \<open>fluents_def\<close> unconditional, as the pipeline's \<open>numeric_cert_fluents\<close> relies on.\<close>
definition (in varfree) "fluents \<equiv> remdups (concat (map op_fluents ops))"

text \<open>The \<^emph>\<open>instantiating\<close> grounder: the Variable_Freeness stage's \<^emph>\<open>minimal\<close> obligations
  (\<^locale>\<open>varfree_instantiator\<close>) plus the achievable-facts list \<open>facts\<close>, and \<^bold>\<open>no coverage
  assumptions at all\<close>. The grounded product is the composite of the two stages: the variable-free
  instantiation \<^const>\<open>varfree.varfree_inst_prob\<close> put through the shared
  \<^locale>\<open>fact_folder\<close> at \<open>facts\<close>/\<open>fluents\<close>, interpreted as \<open>ff\<close> below.\<close>
locale grounder_inst = varfree_instantiator +
  fixes facts :: "facty list"

text \<open>The fact folder at the variable-free problem, with the grounder's own \<open>facts\<close>/\<open>fluents\<close>.
  \<^locale>\<open>fact_folder\<close> is assumption-free, so this interpretation costs nothing here;
  \<open>wf_grounder_cov\<close> strengthens the \<^emph>\<open>same\<close> \<open>ff\<close> interpretation to
  \<open>wf_fact_folder_cov\<close>.\<close>
sublocale grounder_inst \<subseteq> ff: fact_folder varfree_inst_prob facts fluents .

text \<open>The grounded product \<^emph>\<open>is\<close> the composite of the two stages --- there is no separate
  one-shot construction to relate it to, so \<open>D\<^sub>G\<close>/\<open>P\<^sub>G\<close> are plain abbreviations for the
  folder's output at the variable-free instantiation.\<close>
abbreviation (in grounder_inst) "D\<^sub>G \<equiv> ff.fold_dom"
abbreviation (in grounder_inst) "P\<^sub>G \<equiv> ff.fold_prob"

text \<open>Some of these may follow from one another\<close>

text \<open>The \<^emph>\<open>covered\<close> numeric grounder: \<^locale>\<open>grounder_inst\<close> plus a reachable \<open>facts\<close> list that is
  well-formed and covers every op's precondition/effect predicate atoms and the goal, so the shared
  \<open>ground_fmla\<close> / \<open>ga_eff\<close> re-indexing of \<^emph>\<open>predicate\<close> atoms onto nullary \<open>predAtm\<close>s
  is faithful. Numeric atoms/effects are \<^emph>\<open>allowed\<close> here (they re-index onto nullary fluents); this
  is the layer at which the nullary-fluent-retaining grounded problem \<open>ground_prob\<close> lives, so the
  precondition/goal coverage obligations are the \<^emph>\<open>numeric-permissive\<close> \<^const>\<open>covered_num\<close>
  (a numeric atom is fine as long as its ground fluents are in \<open>fluents\<close>). The effect
  add/delete literals stay at the strong \<^const>\<open>covered\<close>: they are \<open>wf_fmla_atom\<close>s, hence always
  predicate atoms.\<close>
locale wf_grounder_cov = grounder_inst +
  assumes
    facts_dist: "distinct facts" and
    all_facts: "fact_to_facty ` {a. achievable a} \<subseteq> set facts" and
    facts_wf: "\<forall>a \<in> set facts. wf_fmla_atom objT a" and (* If "set facts = {a. achievable a}", this follows. *)
    effs_covered: "\<forall>\<pi> \<in> set ops. (let eff = effect (the (res_inst \<pi>)) in
      \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)" and
    pres_covered_num: "\<forall>\<pi> \<in> set ops. covered_num (precondition (the (res_inst \<pi>))) facts fluents" and
    goal_covered_num: "covered_num (goal P) facts fluents"

text \<open>The \<^emph>\<open>propositional\<close>/STRIPS grounder = the covered numeric grounder plus the actual
  \<^emph>\<open>no-fluents\<close> assumptions: precondition and goal coverage strengthen back to
  \<^const>\<open>covered\<close> (no numeric atom anywhere), the initial state has no function assignments (it is
  purely propositional) and the applicable ops carry no numeric effects. Under these the shared
  grounder emits no numeric atom or effect, so the grounded problem is numeric-free --- these hold
  trivially once numerics have been compiled away upstream. So \<^bold>\<open>the STRIPS grounder is the numeric
  grounder (\<^locale>\<open>wf_grounder_cov\<close>) with the numeric-freeness assumptions added\<close>. The two strong
  coverage assumptions keep the \<^emph>\<open>names\<close> \<open>pres_covered\<close> / \<open>goal_covered\<close> they had before the
  \<^const>\<open>covered_num\<close> weakening, so every downstream proof reads unchanged.\<close>
locale wf_grounder = wf_grounder_cov +
  assumes
    pres_covered: "\<forall>\<pi> \<in> set ops. covered (precondition (the (res_inst \<pi>))) facts" and
    goal_covered: "covered (goal P) facts" and
    init_props: "\<forall>f \<in> set (init P). is_predAtom f" and
    ops_no_num: "\<forall>\<pi> \<in> set ops. numeric_effects (effect (the (res_inst \<pi>))) = []"

text \<open>The \<^emph>\<open>numeric\<close> grounder: the covered numeric layer plus the one obligation that the
  \<^emph>\<open>problem\<close> level needs on top of the domain level --- every initial-state formula is
  \<^const>\<open>covered_num\<close>, i.e. its predicate atoms are facts and its ground fluents are reachable
  fluents. This is what lets \<open>fold_prob\<close> fold an initial function assignment such as
  \<open>(= (fuel c1) 10)\<close> onto its nullary form; it cannot be derived, because
  \<open>fluents\<close> is enumerated from the reachable \<^emph>\<open>ops\<close> only.\<close>
locale wf_grounder_num = wf_grounder_cov +
  assumes
    init_covered_num: "\<forall>f \<in> set (init P). covered_num f facts fluents"

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
    pres_covered_num: "\<forall>a \<in> set (actions (domain P)).
      covered_num (precondition (the (res_inst (ac_pa a)))) facts fluents" and
    goal_covered_num: "covered_num (goal P) facts fluents" and
    fluents_dist: "distinct fluents" and
    fluents_wf: "\<forall>fl \<in> set fluents. wf_primitive_numeric_expression objT fl" and
    acs_fluents: "\<forall>a \<in> set (actions (domain P)). set (op_fluents (ac_pa a)) \<subseteq> set fluents"

text \<open>The propositional/STRIPS layer of the folder, mirroring \<^locale>\<open>wf_grounder\<close>: precondition
  and goal coverage strengthen back to \<^const>\<open>covered\<close> (under the \<^emph>\<open>same names\<close> they carried
  before the \<^const>\<open>covered_num\<close> weakening, so the folder's semantics chain reads unchanged), the
  initial state is purely propositional and the (nullary) actions carry no numeric effects.\<close>
locale wf_fact_folder = wf_fact_folder_cov +
  assumes
    pres_covered: "\<forall>a \<in> set (actions (domain P)). covered (precondition (the (res_inst (ac_pa a)))) facts" and
    goal_covered: "covered (goal P) facts" and
    init_props: "\<forall>f \<in> set (init P). is_predAtom f" and
    acs_no_num: "\<forall>a \<in> set (actions (domain P)). numeric_effects (effect (the (res_inst (ac_pa a)))) = []"

text \<open>The \<^emph>\<open>numeric\<close> layer of the folder, mirroring \<^locale>\<open>wf_grounder_num\<close>: the covered
  numeric layer plus \<^const>\<open>covered_num\<close> coverage of every initial-state formula, which is what
  lets \<open>fold_prob\<close> fold an initial function assignment onto its nullary form.\<close>
locale wf_fact_folder_num = wf_fact_folder_cov +
  assumes
    init_covered_num: "\<forall>f \<in> set (init P). covered_num f facts fluents"

sublocale wf_fact_folder_cov \<subseteq> wf_ast_classical_problem P
  apply (unfold_locales)
  using wf_problem unfolding wf_classical_problem_def by simp

sublocale fact_folder \<subseteq> fdg: ast_classical_domain fold_dom .
sublocale fact_folder \<subseteq> fpg: ast_classical_problem fold_prob .

end
