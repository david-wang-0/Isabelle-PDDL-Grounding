theory Classical_Grounded_PDDL_Factorization
  imports Classical_Grounded_PDDL_Num_Free
    Classical_Variable_Freeness.Classical_Variable_Freeness_Semantics
begin

section \<open>Factorization: the one-shot grounder is variable-freeness followed by fact folding\<close>

text \<open>The propositional grounder \<^const>\<open>grounder.ground_prob\<close> factors through the two pipeline
  stages: the Variable_Freeness stage's \<^const>\<open>varfree.varfree_inst_prob\<close> (instantiate every
  reachable op into a nullary schema) followed by the fact folder's
  \<^const>\<open>fact_folder.fold_prob\<close> (collapse ground atoms and fluents onto fresh nullary
  predicate/function names). This theory proves the factorization: the folder's input obligations
  hold at the variable-free problem, the composed output is \<^emph>\<open>syntactically equal\<close> to the
  one-shot \<^const>\<open>grounder.ground_prob\<close>, and the grounder's well-formedness and plan-preservation
  theorems re-derive from the two stages' theorems composed.\<close>

subsection \<open>The plan-action bridge: zip pairs and \<open>res_inst\<close> transfer\<close>

context wf_grounder_cov
begin

text \<open>Each index of the reachable-op list pairs the op with its generated name, and the
  op\<open>\<rightarrow>\<close>name map agrees with that pairing (\<open>ops\<close> is distinct).\<close>
lemma op_map_inv_nth:
  assumes "i < length ops"
  shows "op_map_inv (ops ! i) = Some (op_names ! i)"
proof -
  have "(ops ! i, op_names ! i) \<in> set (zip ops op_names)"
    using assms ops_len by (force simp: set_zip)
  thus ?thesis
    unfolding op_map_inv_def using ops_dist ops_len by simp
qed

text \<open>Every action of the variable-free domain is \<^term>\<open>varfree_inst_ac \<pi> n\<close> for an actual
  zip pair, so the op\<open>\<rightarrow>\<close>name map pins its name.\<close>
lemma vg_acs_obtain:
  assumes "a \<in> set (actions varfree_inst_dom)"
  obtains \<pi> n where "a = varfree_inst_ac \<pi> n" and "\<pi> \<in> set ops" and "op_map_inv \<pi> = Some n"
proof -
  obtain i where
    i: "i < length (actions varfree_inst_dom)"
    and nth: "actions varfree_inst_dom ! i = a"
    using assms in_set_conv_nth by metis
  have il: "i < length ops" using i ops_len by simp
  have "a = varfree_inst_ac (ops ! i) (op_names ! i)"
    using nth il ops_len by simp
  moreover have "ops ! i \<in> set ops" using il by simp
  moreover have "op_map_inv (ops ! i) = Some (op_names ! i)" using op_map_inv_nth[OF il] .
  ultimately show thesis using that by blast
qed

text \<open>The folder's nullary plan action of a variable-free grounded schema is exactly the
  grounder's \<^term>\<open>ground_pa \<pi>\<close> for the paired op, so \<open>res_inst\<close> transfers back to \<open>P\<close>.\<close>
lemma ac_pa_varfree_inst_ac:
  assumes "op_map_inv \<pi> = Some n"
  shows "ac_pa (varfree_inst_ac \<pi> n) = ground_pa \<pi>"
  unfolding ac_pa_def ground_pa_def using assms by simp

lemma resinst_ac_pa:
  assumes "\<pi> \<in> set ops"
      and "op_map_inv \<pi> = Some n"
  shows "png.res_inst (ac_pa (varfree_inst_ac \<pi> n)) = res_inst \<pi>"
  unfolding ac_pa_varfree_inst_ac[OF assms(2)] using resinst_varfree_inst_pa[OF assms(1)] .

text \<open>The op-fluent enumeration only consumes \<^term>\<open>the (res_inst \<pi>)\<close>, so it transfers along
  the \<open>res_inst\<close> correspondence.\<close>
lemma png_op_fluents_ac_pa:
  assumes "\<pi> \<in> set ops"
      and "op_map_inv \<pi> = Some n"
  shows "png.op_fluents (ac_pa (varfree_inst_ac \<pi> n)) = op_fluents \<pi>"
  unfolding png.op_fluents_def op_fluents_def resinst_ac_pa[OF assms] ..

subsection \<open>Well-formedness of the derived fluents\<close>

text \<open>Every fluent enumerated from a reachable op's instantiated ground action is well-formed
  under \<^const>\<open>objT\<close>: the precondition and effect are well-formed (\<open>wf_ops_resinst\<close>), and the
  enumerators only surface PNEs of those.\<close>
lemma op_fluents_wf:
  assumes "\<pi> \<in> set ops"
      and "fl \<in> set (op_fluents \<pi>)"
  shows "wf_primitive_numeric_expression objT fl"
proof -
  let ?ga = "the (res_inst \<pi>)"
  have ne_wf: "wf_numeric_effect objT ne" if "ne \<in> set (numeric_effects (effect ?ga))" for ne
    using wf_ops_resinst(3) assms(1) that unfolding wf_effect_alt list_all_iff by blast
  consider
      (pre) "fl \<in> set (formula_enumerate_primitive_numeric_expressions (precondition ?ga))"
    | (lhs) "fl \<in> (\<lambda>ne. case ne of NumericEffect _ l _ \<Rightarrow> l) ` set (numeric_effects (effect ?ga))"
    | (rhs) "fl \<in> set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ?ga))"
    using assms(2) unfolding op_fluents_def Let_def by auto
  thus ?thesis
  proof cases
    case pre
    show ?thesis using wf_fmla_imp_wf_pnes[OF _ pre] wf_ops_resinst(2) assms(1) by blast
  next
    case lhs
    then obtain ne where
      ne: "ne \<in> set (numeric_effects (effect ?ga))"
      and fl: "fl = (case ne of NumericEffect _ l _ \<Rightarrow> l)" by blast
    obtain opr l r where [simp]: "ne = NumericEffect opr l r" by (cases ne)
    show ?thesis using ne_wf[OF ne] fl by simp
  next
    case rhs
    obtain ad dl nes where eff: "effect ?ga = Effect ad dl nes" by (cases "effect ?ga")
    obtain ne where
      ne: "ne \<in> set nes"
      and fl: "fl \<in> set (numeric_effect_enumerate_rhs_primitive_numeric_expressions ne)"
      using rhs unfolding eff by auto
    obtain opr l r where [simp]: "ne = NumericEffect opr l r" by (cases ne)
    have nein: "ne \<in> set (numeric_effects (effect ?ga))" using ne eff by simp
    have "wf_numeric_expression objT r" using ne_wf[OF nein] by simp
    thus ?thesis using wf_numeric_expression_imp_wf_pnes fl by simp
  qed
qed

lemma fluents_wf_orig:
  assumes "fl \<in> set fluents"
  shows "wf_primitive_numeric_expression objT fl"
proof -
  obtain \<pi> where
    pi: "\<pi> \<in> set ops"
    and fl: "fl \<in> set (op_fluents \<pi>)"
    using assms unfolding fluents_def by auto
  show ?thesis using op_fluents_wf[OF pi fl] .
qed

end

subsection \<open>The folder's covered obligations hold at the variable-free problem\<close>

text \<open>Interpretation of the fact folder's covered assumption layer at
  \<^const>\<open>varfree.varfree_inst_prob\<close> with the grounder's own \<open>facts\<close>/\<open>fluents\<close>: the folder's
  obligations about the variable-free problem reduce to \<^locale>\<open>wf_grounder_cov\<close>'s own
  assumptions via the \<open>res_inst\<close> transfer, the \<open>png\<close> signature bridge, and the achievability
  transfer \<open>varfree_achievable_sub\<close>.\<close>
sublocale wf_grounder_cov \<subseteq> ff: wf_fact_folder_cov varfree_inst_prob facts fluents
proof (unfold_locales)
  show "png.wf_classical_problem" using varfree_inst_prob_wf .
  show "png.varfree_prob" using varfree_inst_prob_varfree .
  show "distinct facts" using facts_dist .
  have "{a. png.achievable a} \<subseteq> {a. achievable a}" using varfree_achievable_sub by blast
  hence "fact_to_facty ` {a. png.achievable a} \<subseteq> fact_to_facty ` {a. achievable a}"
    by (rule image_mono)
  thus "fact_to_facty ` {a. png.achievable a} \<subseteq> set facts" using all_facts by blast
  show "\<forall>a \<in> set facts. png.wf_fmla_atom png.objT a"
    unfolding varfree_png_wf_fmla_atom varfree_png_objT using facts_wf .
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      (let eff = effect (the (png.res_inst (ac_pa a))) in
       \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have ri: "png.res_inst (ac_pa a) = res_inst \<pi>" unfolding a using resinst_ac_pa[OF pi n] .
    have "(let eff = effect (the (res_inst \<pi>)) in
       \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)"
      using effs_covered pi by blast
    thus "(let eff = effect (the (png.res_inst (ac_pa a))) in
       \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)" unfolding ri .
  qed
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      covered (precondition (the (png.res_inst (ac_pa a)))) facts"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have ri: "png.res_inst (ac_pa a) = res_inst \<pi>" unfolding a using resinst_ac_pa[OF pi n] .
    show "covered (precondition (the (png.res_inst (ac_pa a)))) facts"
      unfolding ri using pres_covered pi by blast
  qed
  show "covered (goal varfree_inst_prob) facts" using goal_covered by simp
  show "distinct fluents" unfolding fluents_def by simp
  show "\<forall>fl \<in> set fluents. png.wf_primitive_numeric_expression png.objT fl"
    unfolding varfree_png_wf_pne varfree_png_objT using fluents_wf_orig by blast
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      set (png.op_fluents (ac_pa a)) \<subseteq> set fluents"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have "png.op_fluents (ac_pa a) = op_fluents \<pi>"
      unfolding a using png_op_fluents_ac_pa[OF pi n] .
    thus "set (png.op_fluents (ac_pa a)) \<subseteq> set fluents"
      using op_fluents_subset[OF pi] by simp
  qed
qed

subsection \<open>The factorization equality\<close>

context wf_grounder_cov
begin

text \<open>Pointwise: folding a variable-free grounded schema yields exactly the one-shot grounded
  schema for the paired op --- the folder resolves the nullary plan action back to
  \<^term>\<open>the (res_inst \<pi>)\<close> (the \<open>res_inst\<close> transfer) and re-indexes with the \<^emph>\<open>same\<close>
  \<open>ga_pre\<close>/\<open>ga_eff\<close> at the same \<open>facts\<close>/\<open>fluents\<close>.\<close>
lemma fold_ac_varfree_inst_ac:
  assumes "\<pi> \<in> set ops"
      and "op_map_inv \<pi> = Some n"
  shows "ff.fold_ac (varfree_inst_ac \<pi> n) = ground_ac \<pi> n"
  unfolding ff.fold_ac_def ground_ac_def Let_def resinst_ac_pa[OF assms] by simp

lemma fold_acs_eq:
  "map ff.fold_ac (map2 varfree_inst_ac ops op_names) = map2 ground_ac ops op_names"
proof (rule nth_equalityI)
  show "length (map ff.fold_ac (map2 varfree_inst_ac ops op_names))
      = length (map2 ground_ac ops op_names)" by simp
  fix i assume "i < length (map ff.fold_ac (map2 varfree_inst_ac ops op_names))"
  hence i: "i < length ops" using ops_len by simp
  have "ops ! i \<in> set ops" using i by simp
  hence "ff.fold_ac (varfree_inst_ac (ops ! i) (op_names ! i)) = ground_ac (ops ! i) (op_names ! i)"
    using fold_ac_varfree_inst_ac op_map_inv_nth[OF i] by blast
  thus "map ff.fold_ac (map2 varfree_inst_ac ops op_names) ! i = map2 ground_ac ops op_names ! i"
    using i ops_len by simp
qed

theorem ground_dom_factors: "ff.fold_dom = ground_dom"
proof -
  have acts: "actions (ast_problem.domain varfree_inst_prob) = map2 varfree_inst_ac ops op_names"
    by simp
  show ?thesis
    unfolding ff.fold_dom_def ground_dom_def acts fold_acs_eq by simp
qed

theorem ground_prob_factors: "ff.fold_prob = ground_prob"
  unfolding ff.fold_prob_def ground_prob_def by (simp add: ground_dom_factors)

end

subsection \<open>The grounder's domain well-formedness, re-derived\<close>

text \<open>The one-shot grounder's \<open>ground_dom_wf\<close> is the folder's \<open>fold_dom_wf\<close> rewritten through
  the factorization equality, and the \<open>dg\<close> interpretation is promoted to
  \<^locale>\<open>wf_ast_classical_domain\<close> exactly as the retired monolithic development did.\<close>

theorem (in wf_grounder_cov) ground_dom_wf: "dg.wf_classical_domain"
  using ff.fold_dom_wf unfolding ground_dom_factors .

sublocale wf_grounder_cov \<subseteq> dg: wf_ast_classical_domain D\<^sub>G
  using ground_dom_wf by unfold_locales

subsection \<open>The propositional folder layer\<close>

text \<open>At \<^locale>\<open>wf_grounder\<close> strength the folder's two propositional obligations follow from
  \<open>init_props\<close> (the initial states coincide) and \<open>ops_no_num\<close> (via the \<open>res_inst\<close> transfer),
  refining the \<open>ff\<close> interpretation to \<^locale>\<open>wf_fact_folder\<close>.\<close>
sublocale wf_grounder \<subseteq> ff: wf_fact_folder varfree_inst_prob facts fluents
proof (unfold_locales)
  show "\<forall>f \<in> set (init varfree_inst_prob). is_predAtom f" using init_props by simp
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      numeric_effects (effect (the (png.res_inst (ac_pa a)))) = []"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have ri: "png.res_inst (ac_pa a) = res_inst \<pi>" unfolding a using resinst_ac_pa[OF pi n] .
    show "numeric_effects (effect (the (png.res_inst (ac_pa a)))) = []"
      unfolding ri using ops_no_num pi by blast
  qed
qed

subsection \<open>The grounder's theorems, re-derived through the factorization\<close>

text \<open>The one-shot grounder's headline theorems (\<open>ground_prob_wf\<close>, \<open>valid_plan_right\<close>,
  \<open>valid_classical_plan_left\<close>, \<open>valid_classical_plan_iff\<close>) derive by composing the
  Variable_Freeness stage's theorems (\<open>P \<leftrightarrow> png\<close>, plans mapped by \<open>ground_pa\<close> /
  \<open>restore_ground_pa\<close>) with the fact folder's (\<open>png \<leftrightarrow>\<close> folded, the \<^emph>\<open>identity\<close> on plans),
  rewritten through the factorization equality \<open>ground_prob_factors\<close>. Each statement is
  literally the retired monolithic original.\<close>

theorem (in wf_grounder) ground_prob_wf: "pg.wf_classical_problem"
  using ff.fold_prob_wf unfolding ground_prob_factors .

sublocale wf_grounder \<subseteq> pg: grounded_problem P\<^sub>G
  using ground_prob_wf ground_prob_grounded by unfold_locales

context wf_grounder
begin

theorem valid_plan_right:
  assumes "valid_classical_plan2 \<pi>s"
  shows "pg.valid_classical_plan2 (map ground_pa \<pi>s)"
proof -
  have "png.valid_classical_plan2 (map ground_pa \<pi>s)"
    using varfree_valid_plan_right[OF assms] .
  thus ?thesis by (rule ff.fold_valid_plan_right[unfolded ground_prob_factors])
qed

theorem valid_classical_plan_left:
  assumes "pg.valid_classical_plan2 \<pi>s'"
  shows "valid_classical_plan2 (restore_ground_plan \<pi>s')"
proof -
  have "png.valid_classical_plan2 \<pi>s'"
    using assms by (rule ff.fold_valid_plan_left[unfolded ground_prob_factors])
  thus ?thesis by (rule varfree_valid_plan_left)
qed

theorem valid_classical_plan_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. pg.valid_classical_plan2 \<pi>s')"
  using valid_plan_right valid_classical_plan_left by blast

end

subsection \<open>Numeric-freeness, re-derived through the factorization\<close>

text \<open>The one-shot grounder's numeric-freeness theorem is the fact folder's stage-local
  \<open>fold_prob_num_free\<close> (of \<^theory>\<open>Classical_Grounded_PDDL.Classical_Grounded_PDDL_Num_Free\<close>,
  at the variable-free problem) rewritten through the factorization equality; the statement is
  literally the retired pipeline original.\<close>

theorem (in wf_grounder) ground_prob_num_free: "ast_classical_problem.num_free_prob ground_prob"
  using ff.fold_prob_num_free unfolding ground_prob_factors .

end
