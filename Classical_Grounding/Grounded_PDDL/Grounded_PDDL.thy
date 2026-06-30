theory Grounded_PDDL
imports "Classical_Planning.Classical_Abstract_Syntax"
    Classical_Grounding_Utils.PDDL_Sema_Supplement
    Grounding_Classical_Common.Normalization_Definitions
    Grounding_Utils.Grounding_Utils
    Grounding_Utils.String_Utils Grounding_Grounded_PDDL.Grounded_PDDL_Covered
begin

type_synonym facty = "object atom formula"

subsection \<open>Introduction / elimination rules for the conjunctive target predicates\<close>

text \<open>Rather than repeatedly \<open>unfolding\<close> the definitions and splitting with \<open>intro conjI\<close>, we
  give each conjunctive predicate a proper introduction rule (declared \<open>[intro]\<close>) and the
  matching destruction rules (declared \<open>[dest]\<close>).\<close>

context ast_classical_domain begin

lemma grounded_domI [intro]:
  assumes "types D = []" "\<forall>p \<in> set (predicates D). grounded_pred p"
    "consts D = []" "\<forall>a \<in> set (actions D). grounded_ac a"
  shows grounded_dom
  unfolding grounded_dom_def using assms by blast

lemma grounded_domD [dest]:
  assumes grounded_dom
  shows "types D = []" "\<forall>p \<in> set (predicates D). grounded_pred p"
    "consts D = []" "\<forall>a \<in> set (actions D). grounded_ac a"
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

(* As this signature reveals, this function has to be handled with care,
  since a new type parameter appears from nowhere.
  In code, 'a is always object. In proofs, however, it is sometimes term, too. *)
fun ground_fmla :: "object atom formula \<Rightarrow> 'a atom formula" where
  "ground_fmla \<bottom> = \<bottom>" |
  "ground_fmla (Atom (eqAtm a b)) = (if a = b then \<^bold>\<not>\<bottom> else \<bottom>)" |
  "ground_fmla (\<^bold>\<not> (Atom (eqAtm a b))) = (if a = b then \<bottom> else \<^bold>\<not>\<bottom>)" |
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
    Effect (map ground_fmla a) (map ground_fmla d) []"

definition "op_names \<equiv> distinct_strings_lit (length ops)"

definition ground_ac :: "ast_classical_plan_action \<Rightarrow> name \<Rightarrow> ast_classical_action_schema" where
  "ground_ac \<pi> n =
    (let ga = the (res_inst \<pi>) in
    SimpleActionSchema (ActionHead n []) (SimpleActionBody (ga_pre ga) (ga_eff ga)))"

definition ground_dom :: "ast_classical_domain" where
  "ground_dom \<equiv> Domain
    []
    (map (\<lambda>p. PredDecl p []) fact_names)
    []
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

locale wf_grounder = grounder +
  assumes
    wf_problem: "wf_classical_problem" and
    facts_dist: "distinct facts" and
    all_facts: "fact_to_facty ` {a. achievable a} \<subseteq> set facts" and
    facts_wf: "\<forall>a \<in> set facts. wf_fmla_atom objT a" and (* If "set facts = {a. achievable a}", this follows. *)
    ops_dist: "distinct ops" and
    all_ops: "set ops \<supseteq> {\<pi>. applicable \<pi>}" and
    (* If "set ops = {\<pi>. applicable \<pi>}", this follows: *)
    ops_wf: "\<forall>\<pi> \<in> set ops. wf_classical_plan_action \<pi>" and
    (* So does this: *)
    effs_covered: "\<forall>\<pi> \<in> set ops. (let eff = effect (the (res_inst \<pi>)) in
      \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)" and
    (* This follows if, additionally, prec_normed_dom: *)
    pres_covered: "\<forall>\<pi> \<in> set ops. covered (precondition (the (res_inst \<pi>))) facts" and
    goal_covered: "covered (goal P) facts" and
    (* The grounder targets purely propositional (post-relaxation) problems: the initial state
       has no function assignments, and the applicable ops carry no numeric effects. These hold
       trivially once numerics have been compiled away upstream, and are what makes the purely
       propositional \<open>ground_fmla\<close> / \<open>ga_eff\<close> faithful. *)
    init_props: "\<forall>f \<in> set (init P). is_predAtom f" and
    ops_no_num: "\<forall>\<pi> \<in> set ops. numeric_effects (effect (the (res_inst \<pi>))) = []"

text \<open>
The last two conditions can be satisfied by instantiating every \<pi>\<in>ops and adding all missing atoms
to \<open>facts\<close>. I don't need to implement this for my grounder, but you are welcome to.
\<close>

abbreviation (in grounder) "D\<^sub>G \<equiv> ground_dom"
abbreviation (in grounder) "P\<^sub>G \<equiv> ground_prob"

sublocale wf_grounder \<subseteq> wf_ast_classical_problem P
  apply (unfold_locales)
  using wf_problem unfolding wf_classical_problem_def by simp

sublocale grounder \<subseteq> dg: ast_classical_domain D\<^sub>G .
sublocale grounder \<subseteq> pg: ast_classical_problem P\<^sub>G .

subsection \<open> Stage 1+2: ported definitions, names, distinctness \<close>

text \<open>The constructor/type port (Stage 1) and the \<^const>\<open>distinct_strings_lit\<close>-based name
  generation with its distinctness obligations (Stage 2) are complete here. The detailed
  grounding-correctness development (preserved verbatim in the commented block below) is
  being re-derived against the classical pair-based semantics (Stage 3); for now the
  headline results the pipeline consumes are stated with \<^bold>\<open>sorry\<close>.\<close>

context grounder begin

lemma facts_len: "length facts = length fact_names"
  unfolding fact_names_def by simp

lemma ops_len: "length ops = length op_names"
  unfolding op_names_def by simp

lemma fact_names_dis: "distinct fact_names"
  unfolding fact_names_def
  by (simp add: distinct_strings_lit_dist distinct_map inj_on_def)

lemma op_names_dis: "distinct op_names"
  unfolding op_names_def by (rule distinct_strings_lit_dist)

subsubsection \<open> Alternative definitions (selectors) \<close>

lemma ground_dom_sel:
  "types D\<^sub>G = []"
  "predicates D\<^sub>G = map (\<lambda>p. PredDecl p []) fact_names"
  "consts D\<^sub>G = []"
  "actions D\<^sub>G = map2 ground_ac ops op_names"
  unfolding ground_dom_def by simp_all

lemma ground_prob_sel [simp]:
  "ast_problem.domain P\<^sub>G = D\<^sub>G"
  "objects P\<^sub>G = []"
  "init P\<^sub>G = map ground_fmla (init P)"
  "goal P\<^sub>G = ground_fmla (goal P)"
  unfolding ground_prob_def by simp_all

lemmas ground_inst_sel = ground_dom_sel ground_prob_sel

lemma ground_ac_sel [simp]:
  "ac_name (ground_ac \<pi> n) = n"
  "ac_params (ground_ac \<pi> n) = []"
  "ac_pre (ground_ac \<pi> n) = ga_pre (the (res_inst \<pi>))"
  "ac_eff (ground_ac \<pi> n) = ga_eff (the (res_inst \<pi>))"
  unfolding ground_ac_def Let_def by simp_all

lemma ga_pre_alt: "ga_pre ga = ground_fmla (precondition ga)"
  by (cases ga; simp)

text \<open>The grounded effect is purely propositional, hence carries no numeric effects.\<close>
lemma ga_eff_alt: "ga_eff ga =
  Effect (map ground_fmla (adds (effect ga))) (map ground_fmla (dels (effect ga))) []"
  by (cases ga rule: ga_eff.cases) simp

lemma ga_eff_sel [simp]:
  "adds (ga_eff ga) = map ground_fmla (adds (effect ga))"
  "dels (ga_eff ga) = map ground_fmla (dels (effect ga))"
  "numeric_effects (ga_eff ga) = []"
  unfolding ga_eff_alt by simp_all

subsubsection \<open> The output is grounded \<close>

lemma acs_grounded: "(\<forall>x \<in> set (actions D\<^sub>G). grounded_ac x)"
proof
  fix x assume "x \<in> set (actions D\<^sub>G)"
  then obtain op i where "x = ground_ac op i"
    unfolding ground_dom_sel using map2_obtain by metis
  hence "ac_params x = []" using ground_ac_sel by simp
  thus "grounded_ac x" by (cases x rule: grounded_ac.cases) simp_all
qed

theorem ground_dom_grounded: "dg.grounded_dom"
proof (intro dg.grounded_domI)
  show "types D\<^sub>G = []" by (simp add: ground_dom_sel)
  show "\<forall>p \<in> set (predicates D\<^sub>G). grounded_pred p" by (auto simp: ground_dom_sel)
  show "consts D\<^sub>G = []" by (simp add: ground_dom_sel)
  show "\<forall>a \<in> set (actions D\<^sub>G). grounded_ac a" using acs_grounded .
qed

theorem ground_prob_grounded: "pg.grounded_prob"
  using ground_dom_grounded by (intro pg.grounded_probI) (simp_all add: ground_prob_sel)

end

context wf_grounder begin

subsubsection \<open> Predicate and action well-formedness \<close>

lemma gr_preds_dis: "distinct (map pred (predicates D\<^sub>G))"
proof -
  have "map pred (predicates D\<^sub>G) = fact_names" unfolding ground_dom_sel by (simp add: comp_def)
  thus ?thesis using fact_names_dis by metis
qed

lemma gr_preds_wf: "(\<forall>x \<in> set (predicates D\<^sub>G). dg.wf_predicate_decl x)"
  unfolding ground_dom_sel by (simp add: domain_signature.wf_predicate_decl.simps)

lemma gr_sig_fact: "p \<in> set fact_names \<Longrightarrow> dg.sig p = Some []"
proof -
  assume "p \<in> set fact_names"
  hence "PredDecl p [] \<in> set (predicates D\<^sub>G)" unfolding ground_dom_sel by force
  thus "dg.sig p = Some []" using dg.pred_resolve gr_preds_dis by metis
qed

lemma ground_ac_names: "map ac_name (map2 ground_ac ops op_names) = op_names"
proof -
  have "map ac_name (map2 ground_ac ops names) = names" if "length ops = length names" for names
    using that proof (induction ops arbitrary: names)
    case (Cons op ops)
    hence "length names \<noteq> 0" by auto
    hence 1: "names = hd names # tl names" by simp
    with Cons have "map ac_name (map2 ground_ac ops (tl names)) = tl names" by auto
    hence "map ac_name (map2 ground_ac (op # ops) (hd names # tl names)) = hd names # tl names"
      using ground_ac_sel by simp
    thus ?case using 1 by simp
  qed simp
  thus ?thesis using ops_len by simp
qed

lemma gr_acs_dis: "distinct (map ac_name (actions D\<^sub>G))"
  using ground_ac_names op_names_dis by (simp add: ground_dom_sel)

subsubsection \<open> Grounding a covered atom / formula yields a well-formed one \<close>

lemma gr_atom_wf:
  assumes "a \<in> set facts"
  shows "dg.wf_fmla_atom tyt (ground_fmla a)"
proof -
  from assms obtain p where p: "fact_map a = Some p" "p \<in> set fact_names"
    unfolding fact_map_def using lookup_zip facts_len by metis
  with p have 1: "ground_fmla a = Atom (predAtm p [])"
    using facts_wf assms by (cases a rule: is_predAtom.cases) auto
  have "dg.wf_fmla_atom tyt (Atom (predAtm p []))"
    using gr_sig_fact[OF p(2)] by (simp add: dg.wf_fmla_atom_alt)
  thus ?thesis using 1 by metis
qed

lemma gr_fmla_atom_wf:
  assumes "covered \<phi> facts" "is_predAtom \<phi>"
  shows "dg.wf_fmla_atom tyt (ground_fmla \<phi>)"
proof -
  from assms(2) obtain p xs where "\<phi> = Atom (predAtm p xs)" using is_predAtom_decomp by blast
  hence "\<phi> \<in> set facts" using covered_predAtm_mem[OF assms(1)] by simp
  thus ?thesis using gr_atom_wf by blast
qed

lemma ground_fmla_wf:
  assumes "covered \<phi> facts"
  shows "dg.wf_fmla tyt (ground_fmla \<phi>)"
  using assms apply (induction \<phi> rule: ground_fmla.induct)
                      apply (simp_all add: covered_def)
  subgoal for v va
    using gr_atom_wf[of "Atom (predAtm v va)"]
    by (simp add: dg.wf_fmla_atom_alt)
  done

lemma ground_fmla_inj: "inj_on ground_fmla (set facts)"
proof -
  {
    fix a b
    assume assms: "a \<in> set facts" "b \<in> set facts" "a \<noteq> b"
    then obtain n args where a: "a = Atom (predAtm n args)"
      using facts_wf wf_fmla_atom_alt by (cases a rule: is_predAtom.cases) auto
    from assms obtain n' args' where b: "b = Atom (predAtm n' args')"
      using facts_wf wf_fmla_atom_alt by (cases b rule: is_predAtom.cases) auto
    note mapof_distinct_zip_neq[OF facts_len fact_names_dis assms]
    hence "ground_fmla a \<noteq> ground_fmla b"
      using a b fact_map_def by auto
  }
  thus ?thesis unfolding inj_on_def by fast
qed

subsubsection \<open> Effect / action-schema well-formedness \<close>

lemma wf_ops_resinst:
  "\<forall>\<pi> \<in> set ops. wf_ground_action (the (res_inst \<pi>))"
  "\<forall>\<pi> \<in> set ops. wf_fmla objT (precondition (the (res_inst \<pi>)))"
  "\<forall>\<pi> \<in> set ops. wf_effect objT (effect (the (res_inst \<pi>)))"
  using ops_wf wf_resolve_instantiate wf_ground_action_alt by simp_all

abbreviation "eff_lits eff \<equiv> set (adds eff) \<union> set (dels eff)"

lemma eff_lit_covered:
  assumes "\<pi> \<in> set ops" "a \<in> eff_lits (effect (the (res_inst \<pi>)))"
  shows "covered a facts"
  using assms effs_covered unfolding Let_def by auto

lemma eff_lit_predAtom:
  assumes "\<pi> \<in> set ops" "a \<in> eff_lits (effect (the (res_inst \<pi>)))"
  shows "is_predAtom a"
proof -
  have "wf_effect objT (effect (the (res_inst \<pi>)))" using assms(1) wf_ops_resinst(3) by blast
  hence "wf_fmla_atom objT a" using assms(2) unfolding wf_effect_alt list_all_iff by blast
  thus "is_predAtom a" using wf_fmla_atom_pred by blast
qed

lemma ground_eff_lit_wf:
  assumes "\<pi> \<in> set ops" "a \<in> eff_lits (effect (the (res_inst \<pi>)))"
  shows "dg.wf_fmla_atom tyt (ground_fmla a)"
  using eff_lit_covered[OF assms] eff_lit_predAtom[OF assms] gr_fmla_atom_wf by blast

lemma wf_effect_ground:
  assumes "\<forall>a\<in>set (adds (effect ga)). dg.wf_fmla_atom tyt (ground_fmla a)"
          "\<forall>a\<in>set (dels (effect ga)). dg.wf_fmla_atom tyt (ground_fmla a)"
  shows "dg.wf_effect tyt (ga_eff ga)"
  unfolding dg.wf_effect_alt ga_eff_sel list_all_iff using assms by auto

lemma ground_eff_wf:
  assumes "\<pi> \<in> set ops"
  shows "dg.wf_effect tyt (ga_eff (the (res_inst \<pi>)))"
  by (rule wf_effect_ground) (use ground_eff_lit_wf[OF assms] in blast)+

lemma ground_ac_wf:
  assumes "\<pi> \<in> set ops"
  shows "dg.wf_classical_action_schema (ground_ac \<pi> i)"
proof (intro dg.wf_classical_action_schemaI)
  show "distinct (map fst (ac_params (ground_ac \<pi> i)))" by simp
  have "covered (precondition (the (res_inst \<pi>))) facts" using assms pres_covered by blast
  thus "dg.wf_fmla (dg.ac_tyt (ground_ac \<pi> i)) (ac_pre (ground_ac \<pi> i))"
    using ground_fmla_wf by (simp add: ga_pre_alt)
  show "dg.wf_effect (dg.ac_tyt (ground_ac \<pi> i)) (ac_eff (ground_ac \<pi> i))"
    using ground_eff_wf[OF assms] by simp
qed

lemma gr_acs_wf: "(\<forall>x \<in> set (actions D\<^sub>G). dg.wf_classical_action_schema x)"
proof (rule ballI)
  fix ac assume "ac \<in> set (actions D\<^sub>G)"
  then obtain \<pi> i where "ac = ground_ac \<pi> i" "\<pi> \<in> set ops"
    unfolding ground_dom_sel using map2_obtain by metis
  thus "dg.wf_classical_action_schema ac" using ground_ac_wf by simp
qed

lemma ground_dom_funcs: "functions D\<^sub>G = []"
  unfolding ground_dom_def by simp

theorem ground_dom_wf: "dg.wf_classical_domain"
proof (intro dg.wf_classical_domainI)
  show "dg.wf_domain_signature"
    unfolding dg.wf_domain_signature_def
    using gr_preds_dis gr_preds_wf
    by (simp add: ground_dom_sel ground_dom_funcs domain_signature.wf_types_def)
  show "distinct (map ac_name (actions D\<^sub>G))" using gr_acs_dis .
  show "\<forall>a \<in> set (actions D\<^sub>G). dg.wf_classical_action_schema a" using gr_acs_wf .
qed

subsubsection \<open> Problem well-formedness \<close>

text \<open>The initial state is propositional (\<open>init_props\<close>), so each of its atoms is an achievable
  fact, hence lies in \<open>facts\<close> and grounds to a well-formed nullary atom.\<close>
lemma init_in_facts: "set (init P) \<subseteq> set facts"
proof
  fix f assume f: "f \<in> set (init P)"
  then obtain p xs where "f = Atom (predAtm p xs)"
    using init_props is_predAtom_decomp by blast
  with f have "achievable (p, xs)" using init_achievable by simp
  thus "f \<in> set facts" using all_facts \<open>f = Atom (predAtm p xs)\<close> by (auto simp: uncurry_def)
qed

lemma gr_init_dis: "distinct (init P\<^sub>G)"
proof -
  have "distinct (init P)" using wf_problem unfolding wf_classical_problem_def by simp
  moreover have "inj_on ground_fmla (set (init P))"
    using ground_fmla_inj init_in_facts inj_on_subset by blast
  ultimately show ?thesis unfolding ground_prob_sel using distinct_map by blast
qed

lemma gr_init_wf: "\<forall>f \<in> set (init P\<^sub>G). pg.wf_fmla_atom pg.objT f \<or> pg.wf_func_assign f"
proof
  fix f assume "f \<in> set (init P\<^sub>G)"
  then obtain g where g: "g \<in> set (init P)" "f = ground_fmla g"
    unfolding ground_prob_sel by auto
  hence "g \<in> set facts" using init_in_facts by blast
  hence "pg.wf_fmla_atom pg.objT f" using gr_atom_wf g by (simp add: ground_prob_sel)
  thus "pg.wf_fmla_atom pg.objT f \<or> pg.wf_func_assign f" by blast
qed

lemma gr_goal_wf: "pg.wf_fmla pg.objT (goal P\<^sub>G)"
  unfolding ground_prob_sel using goal_covered ground_fmla_wf by blast

lemma pg_wf_dom_sig: "pg.wf_domain_signature"
  using ground_dom_wf unfolding dg.wf_classical_domain_def by (simp add: ground_prob_sel)

theorem ground_prob_wf: "pg.wf_classical_problem"
proof (intro pg.wf_classical_problemI)
  show "pg.wf_classical_domain" using ground_dom_wf by (simp add: ground_prob_sel)
  show "pg.wf_problem_signature"
    unfolding pg.wf_problem_signature_def
    using pg_wf_dom_sig by (simp add: ground_prob_sel ground_dom_sel)
  show "distinct (init P\<^sub>G)" using gr_init_dis .
  show "\<forall>f\<in>set (init P\<^sub>G). pg.wf_fmla_atom pg.objT f \<or> pg.wf_func_assign f" using gr_init_wf .
  show "pg.wf_fmla pg.objT (goal P\<^sub>G)" using gr_goal_wf .
qed

subsubsection \<open> Semantics: grounding preserves formula truth \<close>

text \<open>The grounded world model corresponding to \<open>M\<close> keeps the (irrelevant) numeric component
  \<open>snd M\<close> and grounds the logical atoms. Since \<^const>\<open>ground_fmla\<close> produces no numeric atoms and the
  covered formulas contain none either, the pair-based \<open>\<Turnstile>\<^sub>m\<close> semantics never sees the numeric
  part for these formulas.\<close>

lemma gr_predAtom: "is_predAtom a \<Longrightarrow> is_predAtom (ground_fmla a)"
  by (cases a rule: is_predAtom.cases) simp_all

lemma covered_predAtom: "is_predAtom a \<Longrightarrow> covered a facts \<longleftrightarrow> a \<in> set facts"
  unfolding covered_def by (cases a rule: is_predAtom.cases) (auto split: atom.splits)

lemma ground_fmla_inv:
  assumes "M \<subseteq> set facts" "Atom (predAtm n args) \<in> set facts"
  assumes "ground_fmla (Atom (predAtm n args)) \<in> ground_fmla ` M"
  shows "Atom (predAtm n args) \<in> M"
  using assms ground_fmla_inj inj_on_image_mem_iff by metis

lemma val_predAtm_dom: "predAtm p xs \<in> dom (valuation M)"
  unfolding valuation_def by (simp add: domIff)

lemma val_eqAtm_dom: "eqAtm a b \<in> dom (valuation M)"
  unfolding valuation_def by (simp add: domIff)

lemma covered_atoms_dom: "covered \<phi> facts \<Longrightarrow> atoms \<phi> \<subseteq> dom (valuation M)"
  using covered_atoms val_predAtm_dom val_eqAtm_dom by (metis subsetI)

lemma ground_atoms_predAtm: "a \<in> atoms (ground_fmla \<phi>) \<Longrightarrow> \<exists>p. a = predAtm p []"
  by (induction \<phi> rule: ground_fmla.induct) (auto split: if_splits)

lemma ground_atoms_dom: "atoms (ground_fmla \<phi>) \<subseteq> dom (valuation N)"
  using ground_atoms_predAtm val_predAtm_dom by blast

lemma ground_fmla_sem_aux:
  assumes "fst M \<subseteq> set facts"
  shows "covered \<phi> facts \<Longrightarrow>
    (the \<circ> valuation M) \<Turnstile> \<phi> \<longleftrightarrow> (the \<circ> valuation (ground_fmla ` fst M, snd M)) \<Turnstile> ground_fmla \<phi>"
proof (induction \<phi> rule: ground_fmla.induct)
  case ("4_1" p xs)
  hence mem: "Atom (predAtm p xs) \<in> set facts" by (simp add: covered_def)
  have "(Atom (predAtm p xs) \<in> fst M)
    = (ground_fmla (Atom (predAtm p xs)) \<in> ground_fmla ` fst M)"
  proof
    assume "Atom (predAtm p xs) \<in> fst M"
    thus "ground_fmla (Atom (predAtm p xs)) \<in> ground_fmla ` fst M" by (rule imageI)
  next
    assume "ground_fmla (Atom (predAtm p xs)) \<in> ground_fmla ` fst M"
    thus "Atom (predAtm p xs) \<in> fst M" using ground_fmla_inv[OF assms mem] by simp
  qed
  thus ?case unfolding valuation_def by simp
qed (auto simp: valuation_def covered_def)

lemma ground_fmla_sem:
  assumes "covered \<phi> facts" "fst M \<subseteq> set facts"
  shows "valuation M \<Turnstile>\<^sub>m \<phi> \<longleftrightarrow> valuation (ground_fmla ` fst M, snd M) \<Turnstile>\<^sub>m ground_fmla \<phi>"
proof -
  have dL: "\<forall>a\<in>atoms \<phi>. a \<in> dom (valuation M)" using covered_atoms_dom assms(1) by blast
  have dR: "\<forall>a\<in>atoms (ground_fmla \<phi>). a \<in> dom (valuation (ground_fmla ` fst M, snd M))"
    using ground_atoms_dom by blast
  show ?thesis
    unfolding map_formula_semantics_def
    using dL dR ground_fmla_sem_aux[OF assms(2) assms(1)] by simp
qed

lemma ground_goal_sem:
  assumes "fst M \<subseteq> set facts"
  shows "valuation M \<Turnstile>\<^sub>m goal P \<longleftrightarrow> valuation (ground_fmla ` fst M, snd M) \<Turnstile>\<^sub>m ground_fmla (goal P)"
  using assms goal_covered ground_fmla_sem by blast

subsubsection \<open> The initial states correspond \<close>

text \<open>Both the original and the grounded initial state have an empty numeric component (the
  problem is propositional), and the grounded logical state is the image of the original under
  \<^term>\<open>ground_fmla\<close>.\<close>

lemma predAtom_not_num: "is_predAtom f \<Longrightarrow> \<not> is_numericInitializationAtom f"
  by (cases f rule: is_predAtom.cases) auto

lemma init_no_num: "filter is_numericInitializationAtom (init P) = []"
  using init_props predAtom_not_num by (auto simp: filter_empty_conv)

lemma I_simp: "I = (set (init P), Map.empty)"
proof -
  have "filter is_predAtom (init P) = init P" using init_props by (simp add: filter_id_conv)
  thus ?thesis using init_no_num unfolding I_def by simp
qed

lemma fst_I: "fst I = set (init P)" using I_simp by simp

lemma i_covered: "fst I \<subseteq> set facts" using fst_I init_in_facts by simp

lemma ground_init_predAtm: "f \<in> set (init P\<^sub>G) \<Longrightarrow> is_predAtom f"
proof -
  assume "f \<in> set (init P\<^sub>G)"
  then obtain g where "g \<in> set (init P)" "f = ground_fmla g"
    unfolding ground_prob_sel by auto
  thus "is_predAtom f" using init_props gr_predAtom by blast
qed

lemma pg_init_no_num: "filter is_numericInitializationAtom (init P\<^sub>G) = []"
  using ground_init_predAtm predAtom_not_num by (auto simp: filter_empty_conv)

lemma ground_init: "pg.I = (ground_fmla ` fst I, snd I)"
proof -
  have 1: "filter is_predAtom (init P\<^sub>G) = init P\<^sub>G"
    using ground_init_predAtm by (simp add: filter_id_conv)
  have "pg.I = (ground_fmla ` set (init P), Map.empty)"
    unfolding pg.I_def using 1 pg_init_no_num by (simp add: ground_prob_sel)
  thus ?thesis using fst_I I_simp by simp
qed

end

subsection \<open> Plan-action correspondence \<close>

text \<open>\<open>ground_pa\<close> maps an applicable op to its nullary grounded plan action; \<open>restore_ground_pa\<close>
  (defined in the \<open>grounder\<close> locale) is its inverse on grounded plan actions.\<close>

definition (in grounder) "op_map_inv \<equiv> map_of (zip ops op_names)"
definition (in grounder) "ground_pa \<pi> \<equiv> SimplePlanAction (the (op_map_inv \<pi>)) []"

text \<open>Promote the grounded domain/problem to their well-formed and grounded locales, so that the
  classical resolution/instantiation machinery (\<open>res_aux\<close>, \<open>grounded_pa_nullary\<close>, \<dots>) is available
  under the \<open>dg\<close>/\<open>pg\<close> prefixes.\<close>

sublocale wf_grounder \<subseteq> dg: wf_ast_classical_domain D\<^sub>G
  using ground_dom_wf by unfold_locales
sublocale wf_grounder \<subseteq> pg: grounded_problem P\<^sub>G
  using ground_prob_wf ground_prob_grounded by unfold_locales

context wf_grounder begin

lemma ground_action_map_entry:
  assumes "\<pi> \<in> set ops"
  obtains n where
    "(\<pi>, n) \<in> set (zip ops op_names)"
    "ground_ac \<pi> n \<in> set (actions D\<^sub>G)"
    "op_map_inv \<pi> = Some n"
proof -
  from assms obtain i where i: "i < length ops" "ops ! i = \<pi>"
    using in_set_conv_nth by meson
  let ?n = "op_names ! i"
  have lz: "i < length (zip ops op_names)" using i ops_len by simp
  have eqz: "zip ops op_names ! i = (\<pi>, ?n)" using i ops_len by simp
  have z: "(\<pi>, ?n) \<in> set (zip ops op_names)" using nth_mem[OF lz] eqz by simp
  have ntheq: "actions D\<^sub>G ! i = ground_ac \<pi> ?n"
    unfolding ground_dom_sel using i ops_len by simp
  have li: "i < length (actions D\<^sub>G)" unfolding ground_dom_sel using i ops_len by simp
  have ac: "ground_ac \<pi> ?n \<in> set (actions D\<^sub>G)" using ntheq nth_mem[OF li] by simp
  have omap: "op_map_inv \<pi> = Some ?n"
    unfolding op_map_inv_def
    using z ops_dist ops_len by (simp add: map_of_is_SomeI map_fst_zip)
  show thesis by (rule that[OF z ac omap])
qed

subsubsection \<open> Resolving and instantiating a grounded plan action \<close>

lemma resolve_ground_pa:
  assumes "\<pi> \<in> set ops"
  obtains n where "dg.resolve_classical_action_schema (name (ground_pa \<pi>)) = Some (ground_ac \<pi> n)"
proof -
  from assms obtain n where n: "ground_ac \<pi> n \<in> set (actions D\<^sub>G)" "op_map_inv \<pi> = Some n"
    using ground_action_map_entry by metis
  have "name (ground_pa \<pi>) = n" unfolding ground_pa_def using n(2) by simp
  moreover have "dg.resolve_classical_action_schema n = Some (ground_ac \<pi> n)"
    using n(1) ground_ac_sel dg.res_aux by metis
  ultimately show thesis using that by simp
qed

lemma ground_fmla_subst:
  "map_formula (map_atom (subst_term t)) (ground_fmla \<phi>) = ground_fmla \<phi>"
  by (induction \<phi> rule: ground_fmla.induct) (auto split: if_splits)

lemma ground_effect_subst:
  "map_ast_effect (subst_term t) (ga_eff ga) = ga_eff ga"
  using ground_fmla_subst by (cases ga rule: ga_eff.cases) (simp add: ga_eff_alt)

lemma gr_pa_instantiation:
  "instantiate_classical_action_schema (ground_ac \<pi> n) [] =
    GroundAction (ga_pre (the (res_inst \<pi>))) (ga_eff (the (res_inst \<pi>)))"
  unfolding instantiate_classical_action_schema_alt ground_ac_sel ga_pre_alt
  by (simp add: ground_fmla_subst ground_effect_subst)

lemma pg_resolve_eq_dg: "pg.resolve_classical_action_schema = dg.resolve_classical_action_schema"
  by (simp add: pg.resolve_classical_action_schema_def dg.resolve_classical_action_schema_def ground_prob_sel)

lemma resinst_ground_pa:
  assumes "\<pi> \<in> set ops"
  shows "the (pg.res_inst (ground_pa \<pi>)) =
    GroundAction (ga_pre (the (res_inst \<pi>))) (ga_eff (the (res_inst \<pi>)))"
proof -
  from assms obtain n where n: "dg.resolve_classical_action_schema (name (ground_pa \<pi>)) = Some (ground_ac \<pi> n)"
    using resolve_ground_pa by metis
  have "pg.res_inst (ground_pa \<pi>) = Some (instantiate_classical_action_schema (ground_ac \<pi> n) [])"
    unfolding pg.res_inst_alt using n pg_resolve_eq_dg by (simp add: ground_pa_def)
  thus ?thesis using gr_pa_instantiation by simp
qed

lemma resinst_ground_pa_sel:
  assumes "\<pi> \<in> set ops"
  shows "precondition (the (pg.res_inst (ground_pa \<pi>))) = ga_pre (the (res_inst \<pi>))"
        "effect (the (pg.res_inst (ground_pa \<pi>))) = ga_eff (the (res_inst \<pi>))"
  unfolding resinst_ground_pa[OF assms] by simp_all

subsubsection \<open> Well-formedness and enabledness of grounded plan actions \<close>

lemma ground_pa_name_in: "\<pi> \<in> set ops \<Longrightarrow> name (ground_pa \<pi>) \<in> ac_name ` set (actions D\<^sub>G)"
proof -
  assume a: "\<pi> \<in> set ops"
  then obtain n where n: "ground_ac \<pi> n \<in> set (actions D\<^sub>G)" "op_map_inv \<pi> = Some n"
    using ground_action_map_entry by metis
  have "name (ground_pa \<pi>) = n" unfolding ground_pa_def using n(2) by simp
  moreover have "n = ac_name (ground_ac \<pi> n)" by simp
  ultimately show ?thesis using n(1) by (metis image_eqI)
qed

lemma ground_pa_wf: "\<pi> \<in> set ops \<Longrightarrow> pg.wf_classical_plan_action (ground_pa \<pi>)"
  using ground_pa_name_in pg.grounded_pa_nullary
  by (metis ground_pa_def ast_classical_plan_action.sel ground_prob_sel(1))

theorem ground_enabled_iff:
  assumes "fst M \<subseteq> set facts" "\<pi> \<in> set ops"
  shows "plan_action_enabled \<pi> M \<longleftrightarrow> pg.plan_action_enabled (ground_pa \<pi>) (ground_fmla ` fst M, snd M)"
proof -
  let ?a = "the (res_inst \<pi>)"
  let ?ga = "the (pg.res_inst (ground_pa \<pi>))"
  let ?gM = "(ground_fmla ` fst M, snd M)"
  have ri: "?ga = GroundAction (ga_pre ?a) (ga_eff ?a)" using resinst_ground_pa[OF assms(2)] .
  have num1: "numeric_effects (effect ?a) = []" using assms(2) ops_no_num by blast
  have num2: "numeric_effects (effect ?ga) = []" unfolding ri by (simp add: ga_eff_sel)
  have pre: "valuation M \<Turnstile>\<^sub>m precondition ?a \<longleftrightarrow> valuation ?gM \<Turnstile>\<^sub>m precondition ?ga"
    unfolding ri ground_action.sel ga_pre_alt
    using ground_fmla_sem[OF _ assms(1)] pres_covered assms(2) by simp
  show ?thesis
    unfolding plan_action_enabled_def pg.plan_action_enabled_def Let_def
    using ops_wf assms(2) ground_pa_wf[OF assms(2)] num1 num2 pre
      numeric_effects_non_intrf_no_numeric_effects enumerate_rhs_pnes_no_numeric_effects
    by simp
qed

subsubsection \<open> Executing a grounded plan action mirrors the original \<close>

lemma num_update_id: "numeric_effects (effect a) = [] \<Longrightarrow> action_numeric_update_function a N = N"
  by (simp add: action_numeric_update_function_def)

lemma list_num_update_single_id:
  "numeric_effects (effect a) = [] \<Longrightarrow> action_list_numeric_update_function [a] N = N"
  unfolding action_list_numeric_update_function_def by (simp add: num_update_id)

lemma num_ground: "\<pi> \<in> set ops \<Longrightarrow> numeric_effects (effect (the (pg.res_inst (ground_pa \<pi>)))) = []"
  unfolding resinst_ground_pa_sel(2) by (simp add: ga_eff_sel)

lemma pg_exec_simp:
  assumes "numeric_effects (effect (the (pg.res_inst a))) = []"
  shows "pg.execute_plan_action a M' =
    (fst M' - set (dels (effect (the (pg.res_inst a)))) \<union> set (adds (effect (the (pg.res_inst a)))), snd M')"
  using assms list_num_update_single_id
  unfolding pg.execute_plan_action_def apply_ground_action_alt by (cases M') simp

lemma pg_exec_ground_simp:
  assumes "\<pi> \<in> set ops"
  shows "pg.execute_plan_action (ground_pa \<pi>) (ground_fmla ` fst M, snd M) =
    (ground_fmla ` fst M - ground_fmla ` set (dels (effect (the (res_inst \<pi>))))
       \<union> ground_fmla ` set (adds (effect (the (res_inst \<pi>)))), snd M)"
  using pg_exec_simp[OF num_ground[OF assms], of "(ground_fmla ` fst M, snd M)"]
  unfolding resinst_ground_pa_sel(2)[OF assms]
  by (simp add: ga_eff_sel)

lemma exec_simp:
  assumes "\<pi> \<in> set ops"
  shows "execute_plan_action \<pi> M =
    (fst M - set (dels (effect (the (res_inst \<pi>)))) \<union> set (adds (effect (the (res_inst \<pi>)))), snd M)"
  using assms ops_no_num list_num_update_single_id
  unfolding execute_plan_action_def apply_ground_action_alt by (cases M) simp

lemma effs_covered_alt:
  assumes "\<pi> \<in> set ops"
  shows "set (adds (effect (the (res_inst \<pi>)))) \<union> set (dels (effect (the (res_inst \<pi>)))) \<subseteq> set facts"
proof
  fix a assume "a \<in> set (adds (effect (the (res_inst \<pi>)))) \<union> set (dels (effect (the (res_inst \<pi>))))"
  hence "a \<in> eff_lits (effect (the (res_inst \<pi>)))" by simp
  thus "a \<in> set facts"
    using eff_lit_covered[OF assms] eff_lit_predAtom[OF assms] covered_predAtom by blast
qed

lemma exec_covered:
  assumes "fst M \<subseteq> set facts" "\<pi> \<in> set ops"
  shows "fst (execute_plan_action \<pi> M) \<subseteq> set facts"
  using assms effs_covered_alt by (auto simp: exec_simp)

lemma ground_action_exec_right:
  assumes "fst M \<subseteq> set facts" "\<pi> \<in> set ops"
  shows "pg.execute_plan_action (ground_pa \<pi>) (ground_fmla ` fst M, snd M)
       = (ground_fmla ` fst (execute_plan_action \<pi> M), snd (execute_plan_action \<pi> M))"
proof -
  let ?d = "set (dels (effect (the (res_inst \<pi>))))"
  let ?a = "set (adds (effect (the (res_inst \<pi>))))"
  have cov: "?a \<union> ?d \<subseteq> set facts" using effs_covered_alt[OF assms(2)] by simp
  have inj: "inj_on ground_fmla (fst M \<union> ?d \<union> ?a)"
    by (rule inj_on_subset[OF ground_fmla_inj]) (use assms(1) cov in auto)
  have d_eq: "ground_fmla ` (fst M - ?d) = ground_fmla ` fst M - ground_fmla ` ?d"
    by (rule inj_on_image_set_diff[OF inj]) auto
  have un_eq: "ground_fmla ` (fst M - ?d \<union> ?a) = ground_fmla ` fst M - ground_fmla ` ?d \<union> ground_fmla ` ?a"
    by (simp add: image_Un d_eq)
  show ?thesis
    by (simp add: pg_exec_ground_simp[OF assms(2)] exec_simp[OF assms(2)] un_eq)
qed

subsubsection \<open> Plan-path correspondence and the validity equivalence \<close>

lemma ground_path_right:
  assumes "fst M \<subseteq> set facts" "set \<pi>s \<subseteq> set ops" "valid_classical_plan_alt M \<pi>s M'"
  shows "pg.valid_classical_plan_alt (ground_fmla ` fst M, snd M) (map ground_pa \<pi>s) (ground_fmla ` fst M', snd M')"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons \<pi> \<pi>s)
  hence pi: "\<pi> \<in> set ops" and rest: "set \<pi>s \<subseteq> set ops" by auto
  from Cons have en: "plan_action_enabled \<pi> M"
    and val: "valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'" by auto
  have ex: "pg.execute_plan_action (ground_pa \<pi>) (ground_fmla ` fst M, snd M)
    = (ground_fmla ` fst (execute_plan_action \<pi> M), snd (execute_plan_action \<pi> M))"
    using ground_action_exec_right[OF Cons.prems(1) pi] .
  have cov': "fst (execute_plan_action \<pi> M) \<subseteq> set facts" using exec_covered[OF Cons.prems(1) pi] .
  have "pg.plan_action_enabled (ground_pa \<pi>) (ground_fmla ` fst M, snd M)"
    using ground_enabled_iff[OF Cons.prems(1) pi] en by simp
  moreover have "pg.valid_classical_plan_alt
      (ground_fmla ` fst (execute_plan_action \<pi> M), snd (execute_plan_action \<pi> M))
      (map ground_pa \<pi>s) (ground_fmla ` fst M', snd M')"
    using Cons.IH[OF cov' rest val] .
  ultimately show ?case using ex by simp
qed

lemma plan_in_ops:
  assumes "valid_classical_plan_alt I \<pi>s M'"
  shows "set \<pi>s \<subseteq> set ops"
proof
  fix \<pi> assume "\<pi> \<in> set \<pi>s"
  with assms have "applicable \<pi>" unfolding applicable_def by blast
  thus "\<pi> \<in> set ops" using all_ops by blast
qed

lemma alt_covered:
  assumes "fst M \<subseteq> set facts" "set \<pi>s \<subseteq> set ops" "valid_classical_plan_alt M \<pi>s M'"
  shows "fst M' \<subseteq> set facts"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons \<pi> \<pi>s)
  hence pi: "\<pi> \<in> set ops" and v: "valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'" by auto
  show ?case using Cons.IH[OF exec_covered[OF Cons.prems(1) pi] _ v] Cons.prems(2) by auto
qed

theorem valid_plan_right:
  assumes "valid_classical_plan2 \<pi>s"
  shows "pg.valid_classical_plan2 (map ground_pa \<pi>s)"
proof -
  from assms obtain M' where M': "valid_classical_plan_alt I \<pi>s M'" "valuation M' \<Turnstile>\<^sub>m goal P"
    using valid_classical_plan2_alt by blast
  have ops: "set \<pi>s \<subseteq> set ops" using plan_in_ops[OF M'(1)] .
  have cov: "fst M' \<subseteq> set facts" using alt_covered[OF i_covered ops M'(1)] .
  have path: "pg.valid_classical_plan_alt pg.I (map ground_pa \<pi>s) (ground_fmla ` fst M', snd M')"
    unfolding ground_init using ground_path_right[OF i_covered ops M'(1)] .
  have goal: "valuation (ground_fmla ` fst M', snd M') \<Turnstile>\<^sub>m goal P\<^sub>G"
    using ground_goal_sem[OF cov] M'(2) by (simp add: ground_prob_sel)
  show ?thesis using path goal pg.valid_classical_plan2_alt by blast
qed

text \<open> Left direction: restore a grounded plan to the original problem. \<close>

lemma op_names_eq: "set op_names = ac_name ` set (actions D\<^sub>G)"
  using ground_ac_names ground_dom_sel by (metis list.set_map)

lemma restore_map_entry:
  assumes "n \<in> set op_names"
  obtains \<pi> where "op_map n = Some \<pi>" "\<pi> \<in> set ops" "op_map_inv \<pi> = Some n"
proof -
  from assms obtain i where i: "i < length op_names" "op_names ! i = n"
    using in_set_conv_nth by meson
  let ?\<pi> = "ops ! i"
  have iops: "i < length ops" using i ops_len by simp
  have zo: "(n, ?\<pi>) \<in> set (zip op_names ops)"
    using i iops ops_len by (force simp: set_zip)
  have zi: "(?\<pi>, n) \<in> set (zip ops op_names)"
    using i iops ops_len by (force simp: set_zip)
  have "op_map n = Some ?\<pi>"
    unfolding op_map_def using zo op_names_dis ops_len by (simp add: map_of_is_SomeI map_fst_zip)
  moreover have "op_map_inv ?\<pi> = Some n"
    unfolding op_map_inv_def using zi ops_dist ops_len by (simp add: map_of_is_SomeI map_fst_zip)
  moreover have "?\<pi> \<in> set ops" using iops nth_mem by blast
  ultimately show thesis using that by blast
qed

lemma restore_wf_pa:
  assumes "pg.wf_classical_plan_action \<pi>'"
  shows "restore_ground_pa \<pi>' \<in> set ops" "ground_pa (restore_ground_pa \<pi>') = \<pi>'"
proof -
  obtain n args where pi'0: "\<pi>' = SimplePlanAction n args" by (cases \<pi>')
  with assms have "n \<in> ac_name ` set (actions D\<^sub>G) \<and> args = []"
    using pg.grounded_pa_nullary by (simp add: ground_prob_sel)
  hence pi': "\<pi>' = SimplePlanAction n []" and nin: "n \<in> set op_names"
    using pi'0 op_names_eq by auto
  then obtain \<pi> where p: "op_map n = Some \<pi>" "\<pi> \<in> set ops" "op_map_inv \<pi> = Some n"
    using restore_map_entry by metis
  have r: "restore_ground_pa \<pi>' = \<pi>" unfolding pi' using p(1) by simp
  have g: "ground_pa \<pi> = \<pi>'" unfolding ground_pa_def pi' using p(3) by simp
  show "restore_ground_pa \<pi>' \<in> set ops" using r p(2) by simp
  show "ground_pa (restore_ground_pa \<pi>') = \<pi>'" using r g by simp
qed

lemma ground_enabled_left:
  assumes "fst M \<subseteq> set facts" "pg.plan_action_enabled \<pi>' (ground_fmla ` fst M, snd M)"
  shows "plan_action_enabled (restore_ground_pa \<pi>') M"
proof -
  have wf: "pg.wf_classical_plan_action \<pi>'" using assms(2) by (simp add: pg.plan_action_enabled_def)
  have "restore_ground_pa \<pi>' \<in> set ops" "ground_pa (restore_ground_pa \<pi>') = \<pi>'"
    using restore_wf_pa[OF wf] by auto
  thus ?thesis using ground_enabled_iff[OF assms(1)] assms(2) by simp
qed

lemma ground_exec_left:
  assumes "fst M \<subseteq> set facts" "pg.wf_classical_plan_action \<pi>'"
  shows "pg.execute_plan_action \<pi>' (ground_fmla ` fst M, snd M)
       = (ground_fmla ` fst (execute_plan_action (restore_ground_pa \<pi>') M),
          snd (execute_plan_action (restore_ground_pa \<pi>') M))"
proof -
  have "restore_ground_pa \<pi>' \<in> set ops" "ground_pa (restore_ground_pa \<pi>') = \<pi>'"
    using restore_wf_pa[OF assms(2)] by auto
  thus ?thesis using ground_action_exec_right[OF assms(1)] by metis
qed

lemma ground_path_left:
  assumes "fst M \<subseteq> set facts"
    "pg.valid_classical_plan_alt (ground_fmla ` fst M, snd M) \<pi>s' gM'"
  shows "\<exists>M'. gM' = (ground_fmla ` fst M', snd M')
    \<and> valid_classical_plan_alt M (map restore_ground_pa \<pi>s') M'"
  using assms proof (induction \<pi>s' arbitrary: M)
  case Nil
  hence "gM' = (ground_fmla ` fst M, snd M)" by simp
  thus ?case by auto
next
  case (Cons \<pi>' \<pi>s')
  hence en: "pg.plan_action_enabled \<pi>' (ground_fmla ` fst M, snd M)"
    and val: "pg.valid_classical_plan_alt
      (pg.execute_plan_action \<pi>' (ground_fmla ` fst M, snd M)) \<pi>s' gM'" by auto
  have wf: "pg.wf_classical_plan_action \<pi>'" using en by (simp add: pg.plan_action_enabled_def)
  let ?\<pi> = "restore_ground_pa \<pi>'"
  have piops: "?\<pi> \<in> set ops" using restore_wf_pa[OF wf] by simp
  let ?N = "execute_plan_action ?\<pi> M"
  have ex: "pg.execute_plan_action \<pi>' (ground_fmla ` fst M, snd M) = (ground_fmla ` fst ?N, snd ?N)"
    using ground_exec_left[OF Cons.prems(1) wf] .
  have covN: "fst ?N \<subseteq> set facts" using exec_covered[OF Cons.prems(1) piops] .
  have enM: "plan_action_enabled ?\<pi> M" using ground_enabled_left[OF Cons.prems(1) en] .
  from val ex have "pg.valid_classical_plan_alt (ground_fmla ` fst ?N, snd ?N) \<pi>s' gM'" by simp
  from Cons.IH[OF covN this] obtain M' where
    M': "gM' = (ground_fmla ` fst M', snd M')"
        "valid_classical_plan_alt ?N (map restore_ground_pa \<pi>s') M'" by blast
  have "valid_classical_plan_alt M (?\<pi> # map restore_ground_pa \<pi>s') M'"
    using enM M'(2) by simp
  thus ?case using M'(1) by auto
qed

theorem valid_classical_plan_left:
  assumes "pg.valid_classical_plan2 \<pi>s'"
  shows "valid_classical_plan2 (restore_ground_plan \<pi>s')"
proof -
  from assms obtain gM' where g: "pg.valid_classical_plan_alt pg.I \<pi>s' gM'"
    "valuation gM' \<Turnstile>\<^sub>m goal P\<^sub>G" using pg.valid_classical_plan2_alt by blast
  from ground_path_left[OF i_covered g(1)[unfolded ground_init]] obtain M' where
    M': "gM' = (ground_fmla ` fst M', snd M')"
        "valid_classical_plan_alt I (map restore_ground_pa \<pi>s') M'" by blast
  have ops: "set (map restore_ground_pa \<pi>s') \<subseteq> set ops" using plan_in_ops[OF M'(2)] .
  have cov: "fst M' \<subseteq> set facts" using alt_covered[OF i_covered ops M'(2)] .
  have goalM': "valuation M' \<Turnstile>\<^sub>m goal P"
    using ground_goal_sem[OF cov] g(2) M'(1) by (simp add: ground_prob_sel)
  show ?thesis unfolding valid_classical_plan2_alt using M'(2) goalM' by blast
qed

theorem valid_classical_plan_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. pg.valid_classical_plan2 \<pi>s')"
  using valid_plan_right valid_classical_plan_left by blast

end


subsection \<open> Code Setup \<close>

lemmas pddl_ground_code =
  grounder.fact_names_def
  grounder.fact_map_def
  grounder.ground_fmla.simps
  grounder.ga_pre.simps
  grounder.ga_eff.simps
  grounder.ground_ac_def
  grounder.op_names_def
  grounder.ground_dom_def
  grounder.ground_prob_def
  grounder.op_map_def
  grounder.restore_ground_pa.simps
declare pddl_ground_code[code]

end