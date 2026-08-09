theory Classical_Grounded_PDDL_Factorization
  imports Classical_Grounded_PDDL_Num_Free
    Classical_Variable_Freeness.Classical_Variable_Freeness_Semantics
begin

section \<open>The grounded product: variable-free instantiation followed by fact folding\<close>

text \<open>The grounded problem is the composite of the two pipeline stages: the Variable_Freeness
  stage's \<^const>\<open>varfree.varfree_inst_prob\<close> (instantiate every reachable op into a nullary
  schema) followed by the fact folder's \<^const>\<open>fact_folder.fold_prob\<close> (collapse ground atoms
  and fluents onto fresh nullary predicate/function names) --- that composite \<^emph>\<open>is\<close>
  \<open>P\<^sub>G\<close>. This theory discharges the folder's input obligations at the variable-free
  problem, and derives the grounded problem's well-formedness and plan-preservation theorems from
  the two stages' theorems composed.\<close>

subsection \<open>The plan-action bridge: zip pairs and \<open>res_inst\<close> transfer\<close>

text \<open>This bridge needs \<^emph>\<open>no\<close> coverage assumptions, only the \<open>res_inst\<close> transfer of the
  Variable_Freeness stage, so it lives in \<^locale>\<open>grounder_inst\<close>. Every
  \<^locale>\<open>wf_grounder_cov\<close> context inherits it, and the \<^emph>\<open>numeric\<close> pipeline --- which only
  ever establishes \<^locale>\<open>varfree_instantiator\<close> --- can use it too.\<close>

context grounder_inst
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
  shows "ff.ac_pa (varfree_inst_ac \<pi> n) = ground_pa \<pi>"
  unfolding ff.ac_pa_def ground_pa_def using assms by simp

lemma resinst_ac_pa:
  assumes "\<pi> \<in> set ops"
      and "op_map_inv \<pi> = Some n"
  shows "png.res_inst (ff.ac_pa (varfree_inst_ac \<pi> n)) = res_inst \<pi>"
  unfolding ac_pa_varfree_inst_ac[OF assms(2)] using resinst_varfree_inst_pa[OF assms(1)] .

text \<open>The op-fluent enumeration only consumes \<^term>\<open>the (res_inst \<pi>)\<close>, so it transfers along
  the \<open>res_inst\<close> correspondence.\<close>
lemma png_op_fluents_ac_pa:
  assumes "\<pi> \<in> set ops"
      and "op_map_inv \<pi> = Some n"
  shows "png.op_fluents (ff.ac_pa (varfree_inst_ac \<pi> n)) = op_fluents \<pi>"
  unfolding png.op_fluents_def op_fluents_def resinst_ac_pa[OF assms] ..

end

subsection \<open>Well-formedness of the derived fluents\<close>

context wf_grounder_cov
begin

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
  show "fact_to_facty ` {a. png.achievable a} \<subseteq> set facts"
    using all_facts using varfree_achievable_sub by blast
  show "\<forall>a \<in> set facts. png.wf_fmla_atom png.objT a"
    unfolding varfree_png_wf_fmla_atom varfree_png_objT using facts_wf .
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      (let eff = effect (the (png.res_inst (ff.ac_pa a))) in
       \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have ri: "png.res_inst (ff.ac_pa a) = res_inst \<pi>" unfolding a using resinst_ac_pa[OF pi n] .
    have "(let eff = effect (the (res_inst \<pi>)) in
       \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)"
      using effs_covered pi by blast
    thus "(let eff = effect (the (png.res_inst (ff.ac_pa a))) in
       \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)" unfolding ri .
  qed
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      covered_num (precondition (the (png.res_inst (ff.ac_pa a)))) facts fluents"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have ri: "png.res_inst (ff.ac_pa a) = res_inst \<pi>" unfolding a using resinst_ac_pa[OF pi n] .
    show "covered_num (precondition (the (png.res_inst (ff.ac_pa a)))) facts fluents"
      unfolding ri using pres_covered_num pi by blast
  qed
  show "covered_num (goal varfree_inst_prob) facts fluents" using goal_covered_num by simp
  show "distinct fluents" unfolding fluents_def by simp
  show "\<forall>fl \<in> set fluents. png.wf_primitive_numeric_expression png.objT fl"
    unfolding varfree_png_wf_pne varfree_png_objT using fluents_wf_orig by blast
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      set (png.op_fluents (ff.ac_pa a)) \<subseteq> set fluents"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have "png.op_fluents (ff.ac_pa a) = op_fluents \<pi>"
      unfolding a using png_op_fluents_ac_pa[OF pi n] .
    thus "set (png.op_fluents (ff.ac_pa a)) \<subseteq> set fluents"
      using op_fluents_subset[OF pi] by simp
  qed
qed

subsection \<open>The grounded domain's well-formedness\<close>

text \<open>\<open>D\<^sub>G\<close> \<^emph>\<open>is\<close> the folder's output at the variable-free instantiation, so its
  well-formedness is the folder's \<open>fold_dom_wf\<close> verbatim.\<close>

theorem (in wf_grounder_cov) ground_dom_wf: "ff.fdg.wf_classical_domain"
  using ff.fold_dom_wf .

subsection \<open>The propositional folder layer\<close>

text \<open>At \<^locale>\<open>wf_grounder\<close> strength the folder's two propositional obligations follow from
  \<open>init_props\<close> (the initial states coincide) and \<open>ops_no_num\<close> (via the \<open>res_inst\<close> transfer),
  refining the \<open>ff\<close> interpretation to \<^locale>\<open>wf_fact_folder\<close>.\<close>
sublocale wf_grounder \<subseteq> ff: wf_fact_folder varfree_inst_prob facts fluents
proof (unfold_locales)
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      covered (precondition (the (png.res_inst (ff.ac_pa a)))) facts"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have ri: "png.res_inst (ff.ac_pa a) = res_inst \<pi>" unfolding a using resinst_ac_pa[OF pi n] .
    show "covered (precondition (the (png.res_inst (ff.ac_pa a)))) facts"
      unfolding ri using pres_covered pi by blast
  qed
  show "covered (goal varfree_inst_prob) facts" using goal_covered by simp
  show "\<forall>f \<in> set (init varfree_inst_prob). is_predAtom f" using init_props by simp
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)).
      numeric_effects (effect (the (png.res_inst (ff.ac_pa a)))) = []"
  proof
    fix a assume "a \<in> set (actions (ast_problem.domain varfree_inst_prob))"
    hence "a \<in> set (actions varfree_inst_dom)" by simp
    then obtain \<pi> n where
      a: "a = varfree_inst_ac \<pi> n"
      and pi: "\<pi> \<in> set ops"
      and n: "op_map_inv \<pi> = Some n"
      using vg_acs_obtain by metis
    have ri: "png.res_inst (ff.ac_pa a) = res_inst \<pi>" unfolding a using resinst_ac_pa[OF pi n] .
    show "numeric_effects (effect (the (png.res_inst (ff.ac_pa a)))) = []"
      unfolding ri using ops_no_num pi by blast
  qed
qed

subsection \<open>The numeric folder layer\<close>

text \<open>At \<^locale>\<open>wf_grounder_num\<close> strength the folder's extra numeric obligation is literally
  \<open>init_covered_num\<close> --- the variable-free problem keeps \<open>P\<close>'s initial state verbatim --- so the
  \<open>ff\<close> interpretation refines to \<^locale>\<open>wf_fact_folder_num\<close>, and the one-shot grounder's
  \<^emph>\<open>numeric\<close> problem well-formedness is the folder's, rewritten through the factorization
  equality. This is the theorem that makes the folded numeric product a proper pipeline stage: the
  grounded problem retains nullary function declarations and function assignments, and is
  well-formed.\<close>
sublocale wf_grounder_num \<subseteq> ff: wf_fact_folder_num varfree_inst_prob facts fluents
proof (unfold_locales)
  show "\<forall>f \<in> set (init varfree_inst_prob). covered_num f facts fluents"
    using init_covered_num by simp
qed

theorem (in wf_grounder_num) ground_prob_wf_num: "ff.fpg.wf_classical_problem"
  using ff.fold_prob_wf_num .

subsection \<open>The grounded product's headline theorems\<close>

text \<open>The one-shot grounder's headline theorems (\<open>ground_prob_wf\<close>, \<open>valid_plan_right\<close>,
  \<open>valid_classical_plan_left\<close>, \<open>valid_classical_plan_iff\<close>) derive by composing the
  Variable_Freeness stage's theorems (\<open>P \<leftrightarrow> png\<close>, plans mapped by \<open>ground_pa\<close> /
  \<open>restore_ground_pa\<close>) with the fact folder's (\<open>png \<leftrightarrow>\<close> folded, the \<^emph>\<open>identity\<close> on plans),
  stated directly on the two-stage product \<open>P\<^sub>G\<close>. Each statement is
  literally the retired monolithic original.\<close>

theorem (in wf_grounder) ground_prob_wf: "ff.fpg.wf_classical_problem"
  using ff.fold_prob_wf .

context wf_grounder
begin

theorem valid_plan_right:
  assumes "valid_classical_plan2 \<pi>s"
  shows "ff.fpg.valid_classical_plan2 (map ground_pa \<pi>s)"
proof -
  have "png.valid_classical_plan2 (map ground_pa \<pi>s)"
    using varfree_valid_plan_right[OF assms] .
  thus ?thesis by (rule ff.fold_valid_plan_right)
qed

theorem valid_classical_plan_left:
  assumes "ff.fpg.valid_classical_plan2 \<pi>s'"
  shows "valid_classical_plan2 (restore_ground_plan \<pi>s')"
proof -
  have "png.valid_classical_plan2 \<pi>s'"
    using assms by (rule ff.fold_valid_plan_left)
  thus ?thesis by (rule varfree_valid_plan_left)
qed

theorem valid_classical_plan_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ff.fpg.valid_classical_plan2 \<pi>s')"
  using valid_plan_right valid_classical_plan_left by blast

end

subsection \<open>The numeric product's plan equivalence\<close>

text \<open>The numeric one-shot grounder's plan-equivalence theorems: the Variable_Freeness stage's
  theorems composed with the numeric fact folder's (\<open>fold_valid_plan_right_num\<close> /
  \<open>fold_valid_plan_left_num\<close> --- the \<^emph>\<open>identity\<close> on plans). Numeric twins of \<open>valid_plan_right\<close> /
  \<open>valid_classical_plan_left\<close> / \<open>valid_classical_plan_iff\<close>: the fully grounded
  (nullary, fluent-retaining) problem has a valid plan iff the input does, and any of its valid
  plans restores to a concrete valid plan of the input.\<close>

context wf_grounder_num
begin

theorem valid_plan_right_num:
  assumes "valid_classical_plan2 \<pi>s"
  shows "ff.fpg.valid_classical_plan2 (map ground_pa \<pi>s)"
proof -
  have "png.valid_classical_plan2 (map ground_pa \<pi>s)"
    using varfree_valid_plan_right[OF assms] .
  thus ?thesis by (rule ff.fold_valid_plan_right_num)
qed

theorem valid_classical_plan_left_num:
  assumes "ff.fpg.valid_classical_plan2 \<pi>s'"
  shows "valid_classical_plan2 (restore_ground_plan \<pi>s')"
proof -
  have "png.valid_classical_plan2 \<pi>s'"
    using assms by (rule ff.fold_valid_plan_left_num)
  thus ?thesis by (rule varfree_valid_plan_left)
qed

theorem valid_classical_plan_iff_num:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ff.fpg.valid_classical_plan2 \<pi>s')"
  using valid_plan_right_num valid_classical_plan_left_num by blast

end

subsection \<open>Numeric-freeness of the grounded product\<close>

text \<open>The one-shot grounder's numeric-freeness theorem is the fact folder's stage-local
  \<open>fold_prob_num_free\<close> (of \<^theory>\<open>Classical_Grounded_PDDL.Classical_Grounded_PDDL_Num_Free\<close>,
  at the variable-free problem); the statement is literally the retired pipeline original.\<close>

theorem (in wf_grounder) ground_prob_num_free: "ast_classical_problem.num_free_prob P\<^sub>G"
  using ff.fold_prob_num_free .

end
