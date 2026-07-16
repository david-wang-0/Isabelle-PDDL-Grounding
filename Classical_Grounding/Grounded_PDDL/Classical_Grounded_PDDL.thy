theory Classical_Grounded_PDDL
  imports Classical_Grounded_PDDL_Locales
begin

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

text \<open>The grounded effect re-indexes the numeric effects onto nullary fluents (empty when the input is
  numeric-free, i.e. under \<open>ops_no_num\<close>).\<close>
lemma ga_eff_alt: "ga_eff ga =
  Effect (map ground_fmla (adds (effect ga))) (map ground_fmla (dels (effect ga)))
         (map ground_neff (numeric_effects (effect ga)))"
  by (cases ga rule: ga_eff.cases) simp

lemma ga_eff_sel [simp]:
  "adds (ga_eff ga) = map ground_fmla (adds (effect ga))"
  "dels (ga_eff ga) = map ground_fmla (dels (effect ga))"
  "numeric_effects (ga_eff ga) = map ground_neff (numeric_effects (effect ga))"
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
  show "\<forall>f \<in> set (functions D\<^sub>G). grounded_func f" by (simp add: ground_dom_def)
  show "\<forall>a \<in> set (actions D\<^sub>G). grounded_ac a" using acs_grounded .
qed

theorem ground_prob_grounded: "pg.grounded_prob"
  using ground_dom_grounded by (intro pg.grounded_probI) (simp_all add: ground_prob_sel)

end


subsection \<open> General (numeric-effect-retaining) effect well-formedness \<close>

text \<open>The propositional grounder's \<open>ground_eff_wf\<close> holds only under \<open>ops_no_num\<close> (no numeric
  effects). Here we prove the \<^emph>\<open>general\<close> effect well-formedness \<open>ground_eff_wf_cov\<close> in
  \<^locale>\<open>wf_grounder_cov\<close>, i.e. WITHOUT \<open>ops_no_num\<close>: the retained numeric effects
  (\<open>map ground_neff (numeric_effects \<dots>)\<close>) are also well-formed, because every fluent occurring in
  them is re-indexed to a freshly-declared nullary function in the grounded domain. The fluent side
  mirrors the fact side: \<open>fluent_names\<close>/\<open>fluent_map\<close>/\<open>func_sig\<close> play the roles of
  \<open>fact_names\<close>/\<open>fact_map\<close>/\<open>sig\<close>.\<close>

context wf_grounder_cov begin

subsubsection \<open> Fluent names, map, and nullary function signature \<close>

lemma fluent_names_dis: "distinct fluent_names"
  unfolding fluent_names_def
  by (simp add: distinct_strings_lit_dist distinct_map inj_on_def)

lemma fluent_names_len: "length fluent_names = length fluents"
  unfolding fluent_names_def by simp

lemma fluent_map_dom:
  assumes "fl \<in> set fluents"
  shows "\<exists>f. fluent_map fl = Some f \<and> f \<in> set fluent_names"
  unfolding fluent_map_def using lookup_zip fluent_names_len assms by metis

lemma gr_funcs_dis: "distinct (map function_decl.func (functions D\<^sub>G))"
proof -
  have "map function_decl.func (functions D\<^sub>G) = fluent_names"
    unfolding ground_dom_def by (simp add: comp_def)
  thus ?thesis using fluent_names_dis by metis
qed

lemma gr_sig_fun:
  assumes "f \<in> set fluent_names"
  shows "dg.func_sig f = Some []"
proof -
  have "FuncDecl f [] \<in> set (functions D\<^sub>G)"
    using assms unfolding ground_dom_def by force
  thus ?thesis using dg.func_resolve gr_funcs_dis by metis
qed

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
  have "map ac_name (map2 ground_ac xs ys) = ys" if "length xs = length ys" for xs ys
    using that by (induction xs ys rule: list_induct2) (simp_all add: ground_ac_sel)
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

subsubsection \<open> Effect literal well-formedness \<close>

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

subsubsection \<open> Grounding a fluent / numeric expression / numeric effect is well-formed \<close>

lemma ground_pne_wf:
  assumes "fl \<in> set fluents"
  shows "dg.wf_primitive_numeric_expression tyt (ground_pne fl)"
proof -
  obtain f where f: "fluent_map fl = Some f" "f \<in> set fluent_names"
    using fluent_map_dom[OF assms] by blast
  hence "dg.func_sig f = Some []" using gr_sig_fun by blast
  thus ?thesis using f(1) by (simp add: ground_pne_def)
qed

lemma ground_numexp_wf:
  assumes "set (enumerate_primitive_numeric_expressions e) \<subseteq> set fluents"
  shows "dg.wf_numeric_expression tyt (ground_numexp e)"
  using assms by (induction e) (auto simp: ground_pne_wf)

subsubsection \<open> Fluents of an op's numeric effects are collected in \<open>fluents\<close> \<close>

lemma op_fluents_subset:
  assumes "\<pi> \<in> set ops"
  shows "set (op_fluents \<pi>) \<subseteq> set fluents"
  using assms unfolding fluents_def by auto

lemma neff_lhs_in_op_fluents:
  assumes "NumericEffect opr l r \<in> set (numeric_effects (effect (the (res_inst \<pi>))))"
  shows "l \<in> set (op_fluents \<pi>)"
  using assms unfolding op_fluents_def Let_def by force

lemma neff_rhs_pnes_in_op_fluents:
  assumes "NumericEffect opr l r \<in> set (numeric_effects (effect (the (res_inst \<pi>))))"
  shows "set (enumerate_primitive_numeric_expressions r) \<subseteq> set (op_fluents \<pi>)"
proof -
  let ?eff = "effect (the (res_inst \<pi>))"
  have "enumerate_primitive_numeric_expressions r
    = numeric_effect_enumerate_rhs_primitive_numeric_expressions (NumericEffect opr l r)"
    by simp
  hence "set (enumerate_primitive_numeric_expressions r)
    \<subseteq> set (ast_effect_enumerate_rhs_primitive_numeric_expressions ?eff)"
    using assms by (cases ?eff) auto
  thus ?thesis unfolding op_fluents_def Let_def by auto
qed

subsubsection \<open> The grounded effect (with numeric effects) is well-formed \<close>

lemma ground_neff_wf:
  assumes "\<pi> \<in> set ops"
          "ne \<in> set (numeric_effects (effect (the (res_inst \<pi>))))"
  shows "dg.wf_numeric_effect tyt (ground_neff ne)"
proof -
  obtain opr l r where ne: "ne = NumericEffect opr l r" by (cases ne)
  have "l \<in> set fluents"
    using neff_lhs_in_op_fluents op_fluents_subset[OF assms(1)] assms(2) ne by blast
  hence lhs: "dg.wf_primitive_numeric_expression tyt (ground_pne l)"
    using ground_pne_wf by blast
  have "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using neff_rhs_pnes_in_op_fluents op_fluents_subset[OF assms(1)] assms(2) ne by blast
  hence "dg.wf_numeric_expression tyt (ground_numexp r)"
    using ground_numexp_wf by blast
  thus ?thesis using lhs ne by (simp add: ground_neff_def)
qed

lemma ground_eff_wf_cov:
  assumes "\<pi> \<in> set ops"
  shows "dg.wf_effect tyt (ga_eff (the (res_inst \<pi>)))"
proof -
  let ?eff = "effect (the (res_inst \<pi>))"
  have adds: "\<forall>a \<in> set (adds ?eff). dg.wf_fmla_atom tyt (ground_fmla a)"
    using ground_eff_lit_wf[OF assms(1)] by auto
  have dels: "\<forall>a \<in> set (dels ?eff). dg.wf_fmla_atom tyt (ground_fmla a)"
    using ground_eff_lit_wf[OF assms(1)] by auto
  have nums: "\<forall>ne \<in> set (numeric_effects ?eff). dg.wf_numeric_effect tyt (ground_neff ne)"
    using ground_neff_wf[OF assms] by blast
  show ?thesis
    unfolding dg.wf_effect_alt ga_eff_sel list_all_iff
    using adds dels nums by auto
qed

subsubsection \<open> Action-schema and domain well-formedness \<close>

lemma wf_effect_ground:
  assumes "\<forall>a\<in>set (adds (effect ga)). dg.wf_fmla_atom tyt (ground_fmla a)"
          "\<forall>a\<in>set (dels (effect ga)). dg.wf_fmla_atom tyt (ground_fmla a)"
          "numeric_effects (effect ga) = []"
  shows "dg.wf_effect tyt (ga_eff ga)"
  unfolding dg.wf_effect_alt ga_eff_sel list_all_iff using assms by auto

lemma ground_ac_wf:
  assumes "\<pi> \<in> set ops"
  shows "dg.wf_classical_action_schema (ground_ac \<pi> i)"
proof (intro dg.wf_classical_action_schemaI)
  show "distinct (map fst (ac_params (ground_ac \<pi> i)))" by simp
  have "covered (precondition (the (res_inst \<pi>))) facts" using assms pres_covered by blast
  thus "dg.wf_fmla (dg.ac_tyt (ground_ac \<pi> i)) (ac_pre (ground_ac \<pi> i))"
    using ground_fmla_wf by (simp add: ga_pre_alt)
  show "dg.wf_effect (dg.ac_tyt (ground_ac \<pi> i)) (ac_eff (ground_ac \<pi> i))"
    using ground_eff_wf_cov[OF assms] by simp
qed

lemma gr_acs_wf: "(\<forall>x \<in> set (actions D\<^sub>G). dg.wf_classical_action_schema x)"
proof (rule ballI)
  fix ac assume "ac \<in> set (actions D\<^sub>G)"
  then obtain \<pi> i where "ac = ground_ac \<pi> i" "\<pi> \<in> set ops"
    unfolding ground_dom_sel using map2_obtain by metis
  thus "dg.wf_classical_action_schema ac" using ground_ac_wf by simp
qed

text \<open>At \<^locale>\<open>wf_grounder_cov\<close> the grounded function table is NOT empty (numeric effects are
  retained, so \<open>functions D\<^sub>G = map (\<lambda>f. FuncDecl f []) fluent_names\<close>). It is still well-formed:
  the names are distinct (\<open>gr_funcs_dis\<close>) and every declaration is nullary, hence trivially
  \<^const>\<open>domain_signature.wf_function_decl\<close>.\<close>
theorem ground_dom_wf: "dg.wf_classical_domain"
proof (intro dg.wf_classical_domainI)
  show "dg.wf_domain_signature"
    unfolding dg.wf_domain_signature_def
    using gr_preds_dis gr_preds_wf gr_funcs_dis
    by (simp add: ground_dom_sel ground_dom_def domain_signature.wf_types_def comp_def
                  domain_signature.wf_predicate_decl.simps domain_signature.wf_function_decl.simps)
  show "distinct (map ac_name (actions D\<^sub>G))" using gr_acs_dis .
  show "\<forall>a \<in> set (actions D\<^sub>G). dg.wf_classical_action_schema a" using gr_acs_wf .
qed

end

sublocale wf_grounder_cov \<subseteq> dg: wf_ast_classical_domain D\<^sub>G
  using ground_dom_wf by unfold_locales

subsection \<open> Propositional grounder: problem well-formedness \<close>

text \<open>The remaining development is \<^locale>\<open>wf_grounder\<close>-specific: it needs the numeric-freeness
  assumptions \<open>ops_no_num\<close>/\<open>init_props\<close>. It builds on the domain-wf lemmas proved above in
  \<^locale>\<open>wf_grounder_cov\<close> (inherited here) — in particular \<open>wf_effect_ground\<close>, \<open>ground_eff_lit_wf\<close>,
  \<open>gr_atom_wf\<close>, \<open>ground_fmla_wf\<close>, \<open>ground_fmla_inj\<close>, and \<open>ground_dom_wf\<close>.\<close>

context wf_grounder begin

subsubsection \<open> Effect well-formedness under the no-fluents assumptions \<close>

text \<open>The propositional \<open>ground_eff_wf\<close> routes through the numeric-free \<open>wf_effect_ground\<close>
  (inherited from \<^locale>\<open>wf_grounder_cov\<close>) and \<open>ops_no_num\<close>.\<close>

lemma ground_eff_wf:
  assumes "\<pi> \<in> set ops"
  shows "dg.wf_effect tyt (ga_eff (the (res_inst \<pi>)))"
  by (rule wf_effect_ground)
     (use ground_eff_lit_wf[OF assms] ops_no_num assms in blast)+

text \<open>Under the no-fluents assumptions (\<open>covered\<close> forbids numeric atoms, \<open>ops_no_num\<close> forbids numeric
  effects) no ground fluents occur, so the grounded function table is empty.\<close>
lemma covered_no_pne:
  assumes "covered \<phi> facts" shows "formula_enumerate_primitive_numeric_expressions \<phi> = []"
proof -
  have "atom_enumerate_primitive_numeric_expressions a = []" if "a \<in> atoms \<phi>" for a
    using assms that unfolding covered_def by (cases a) auto
  hence "set (formula_enumerate_primitive_numeric_expressions \<phi>) = {}"
    by (auto simp: set_formula_enumerate_primitive_numeric_expressions_conv)
  thus ?thesis by simp
qed

lemma fluents_empty: "fluents = []"
proof -
  have "op_fluents \<pi> = []" if "\<pi> \<in> set ops" for \<pi>
  proof -
    have p: "formula_enumerate_primitive_numeric_expressions (precondition (the (res_inst \<pi>))) = []"
      using covered_no_pne pres_covered that by blast
    have n: "numeric_effects (effect (the (res_inst \<pi>))) = []" using ops_no_num that by blast
    have r: "ast_effect_enumerate_rhs_primitive_numeric_expressions (effect (the (res_inst \<pi>))) = []"
      using n by (cases "effect (the (res_inst \<pi>))") auto
    show ?thesis using p n r by (simp add: op_fluents_def)
  qed
  thus ?thesis by (simp add: fluents_def)
qed

lemma fluent_names_empty: "fluent_names = []"
proof -
  have "distinct_strings_lit 0 = []" by (metis distinct_str_lit_length length_0_conv)
  thus ?thesis using fluents_empty by (simp add: fluent_names_def)
qed

lemma ground_dom_funcs: "functions D\<^sub>G = []"
  unfolding ground_dom_def by (simp add: fluent_names_empty)

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

end

end
