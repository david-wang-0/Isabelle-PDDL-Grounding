theory Classical_Variable_Freeness_Semantics
  imports Classical_Variable_Freeness
begin

context varfree_grounder begin

text \<open>\<^bold>\<open>The res_inst correspondence at the plan-action level.\<close> Resolving-and-instantiating the nullary
  grounded action \<^term>\<open>ground_pa \<pi>\<close> inside the numeric grounded problem yields \<^emph>\<open>exactly\<close> the original
  instantiated ground action \<^term>\<open>res_inst \<pi>\<close> --- so the numeric grounded problem executes each op
  identically to \<open>P\<close> (same world model, same numeric effects), no \<open>ground_fmla\<close> remapping.\<close>

lemma varfree_ground_action_map_entry:
  assumes "\<pi> \<in> set ops"
  obtains n where
    "(\<pi>, n) \<in> set (zip ops op_names)"
    "varfree_ground_ac \<pi> n \<in> set (actions varfree_ground_dom)"
    "op_map_inv \<pi> = Some n"
proof -
  from assms obtain i where i: "i < length ops" "ops ! i = \<pi>"
    using in_set_conv_nth by meson
  let ?n = "op_names ! i"
  have lz: "i < length (zip ops op_names)" using i ops_len by simp
  have eqz: "zip ops op_names ! i = (\<pi>, ?n)" using i ops_len by simp
  have z: "(\<pi>, ?n) \<in> set (zip ops op_names)" using nth_mem[OF lz] eqz by simp
  have ntheq: "actions varfree_ground_dom ! i = varfree_ground_ac \<pi> ?n"
    using i ops_len by simp
  have li: "i < length (actions varfree_ground_dom)" using i ops_len by simp
  have ac: "varfree_ground_ac \<pi> ?n \<in> set (actions varfree_ground_dom)"
    using ntheq nth_mem[OF li] by simp
  have omap: "op_map_inv \<pi> = Some ?n"
    unfolding op_map_inv_def using z ops_dist ops_len by (simp add: map_of_is_SomeI map_fst_zip)
  show thesis by (rule that[OF z ac omap])
qed

lemma resinst_varfree_ground_pa:
  assumes "\<pi> \<in> set ops"
  shows "png.res_inst (ground_pa \<pi>) = res_inst \<pi>"
proof -
  from assms obtain n where n:
    "varfree_ground_ac \<pi> n \<in> set (actions varfree_ground_dom)" "op_map_inv \<pi> = Some n"
    using varfree_ground_action_map_entry by metis
  have nm: "name (ground_pa \<pi>) = n" unfolding ground_pa_def using n(2) by simp
  have nname: "ast_classical_action_schema_name (varfree_ground_ac x m) = m" for x m
    by (simp add: varfree_ground_ac_def)
  have res: "png.resolve_classical_action_schema n = Some (varfree_ground_ac \<pi> n)"
    unfolding png.resolve_classical_action_schema_def
    using n(1) varfree_ground_dom_names_dis nname
    by (simp add: ast_classical_domain.resolve_classical_action_schema_def index_by_eq_Some_eq)
  have "png.res_inst (ground_pa \<pi>) = Some (instantiate_classical_action_schema (varfree_ground_ac \<pi> n) [])"
    unfolding png.res_inst_alt using res nm by (simp add: ground_pa_def)
  also have "\<dots> = res_inst \<pi>" using varfree_ground_ac_inst by (simp add: res_inst_alt)
  finally show ?thesis .
qed

subsubsection \<open>Initial state and well-formedness of grounded plan actions\<close>

text \<open>The numeric grounded problem keeps the same \<^const>\<open>init\<close>, so its initial world model is
  literally \<open>P\<close>'s --- no \<open>ground_fmla\<close> remap (contrast the propositional \<open>ground_init\<close>).\<close>
lemma varfree_png_init: "png.I = I"
  unfolding png.I_def I_def by simp

text \<open>The nullary grounded plan action resolves to its (nullary) schema, and its empty argument
  list trivially matches the empty parameter list, so it is well-formed in the numeric grounded
  problem.\<close>
lemma varfree_ground_pa_wf:
  assumes "\<pi> \<in> set ops"
  shows "png.wf_classical_plan_action (ground_pa \<pi>)"
proof -
  from assms obtain n where n:
    "varfree_ground_ac \<pi> n \<in> set (actions varfree_ground_dom)" "op_map_inv \<pi> = Some n"
    using varfree_ground_action_map_entry by metis
  have nm: "name (ground_pa \<pi>) = n" unfolding ground_pa_def using n(2) by simp
  have nname: "ast_classical_action_schema_name (varfree_ground_ac x m) = m" for x m
    by (simp add: varfree_ground_ac_def)
  have res: "png.resolve_classical_action_schema n = Some (varfree_ground_ac \<pi> n)"
    unfolding png.resolve_classical_action_schema_def
    using n(1) varfree_ground_dom_names_dis nname
    by (simp add: ast_classical_domain.resolve_classical_action_schema_def index_by_eq_Some_eq)
  have gp: "ground_pa \<pi> = SimplePlanAction n []" unfolding ground_pa_def using n(2) by simp
  have pm: "png.action_params_match (ActionHead n []) []"
    unfolding png.action_params_match_def by simp
  show ?thesis
    unfolding gp using res pm by (simp add: varfree_ground_ac_def)
qed

subsubsection \<open>Enabledness and execution mirror the original\<close>

text \<open>Because \<^term>\<open>png.res_inst (ground_pa \<pi>)\<close> is literally \<^term>\<open>res_inst \<pi>\<close>, the enabledness
  predicate agrees on the two sides: the precondition, numeric-non-interference and
  numeric-domain conditions are the same term on the same world model \<open>M\<close>; only the
  well-formedness conjunct differs, and it holds on both sides.\<close>
lemma varfree_ground_enabled_iff:
  assumes "\<pi> \<in> set ops"
  shows "plan_action_enabled \<pi> M \<longleftrightarrow> png.plan_action_enabled (ground_pa \<pi>) M"
proof -
  have ri: "png.res_inst (ground_pa \<pi>) = res_inst \<pi>" using resinst_varfree_ground_pa[OF assms] .
  have wfl: "wf_classical_plan_action \<pi>" using assms ops_wf by blast
  have wfr: "png.wf_classical_plan_action (ground_pa \<pi>)" using varfree_ground_pa_wf[OF assms] .
  show ?thesis
    unfolding plan_action_enabled_def png.plan_action_enabled_def Let_def
    using ri wfl wfr by simp
qed

text \<open>Executing the grounded op applies the identical ground action to the identical world
  model, so the resulting world model is unchanged.\<close>
lemma varfree_ground_exec_right:
  assumes "\<pi> \<in> set ops"
  shows "png.execute_plan_action (ground_pa \<pi>) M = execute_plan_action \<pi> M"
proof -
  have ri: "png.res_inst (ground_pa \<pi>) = res_inst \<pi>" using resinst_varfree_ground_pa[OF assms] .
  show ?thesis
    unfolding png.execute_plan_action_def execute_plan_action_def using ri by simp
qed

subsubsection \<open>Plan-path correspondence (forward direction)\<close>

text \<open>Since each op is enabled and executes identically on the shared world model, a valid
  path of \<open>P\<close> lifts to a valid path of the numeric grounded problem on the \<^emph>\<open>same\<close> world
  models (no \<open>ground_fmla\<close> remap).\<close>
lemma varfree_ground_path_right:
  assumes "set \<pi>s \<subseteq> set ops" "valid_classical_plan_alt M \<pi>s M'"
  shows "png.valid_classical_plan_alt M (map ground_pa \<pi>s) M'"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons \<pi> \<pi>s)
  hence pi: "\<pi> \<in> set ops" and rest: "set \<pi>s \<subseteq> set ops" by auto
  from Cons have en: "plan_action_enabled \<pi> M"
    and val: "valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'" by auto
  have ex: "png.execute_plan_action (ground_pa \<pi>) M = execute_plan_action \<pi> M"
    using varfree_ground_exec_right[OF pi] .
  have "png.plan_action_enabled (ground_pa \<pi>) M"
    using varfree_ground_enabled_iff[OF pi] en by simp
  moreover have "png.valid_classical_plan_alt (execute_plan_action \<pi> M) (map ground_pa \<pi>s) M'"
    using Cons.IH[OF rest val] .
  ultimately show ?case using ex by simp
qed

theorem varfree_valid_plan_right:
  assumes "valid_classical_plan2 \<pi>s"
  shows "png.valid_classical_plan2 (map ground_pa \<pi>s)"
proof -
  from assms obtain M' where M': "valid_classical_plan_alt I \<pi>s M'" "valuation M' \<Turnstile>\<^sub>m goal P"
    using valid_classical_plan2_alt by blast
  have ops: "set \<pi>s \<subseteq> set ops" using plan_in_ops[OF M'(1)] .
  have path: "png.valid_classical_plan_alt png.I (map ground_pa \<pi>s) M'"
    unfolding varfree_png_init using varfree_ground_path_right[OF ops M'(1)] .
  have goal: "valuation M' \<Turnstile>\<^sub>m goal varfree_ground_prob" using M'(2) by simp
  show ?thesis using path goal png.valid_classical_plan2_alt by blast
qed

subsubsection \<open>Restoring a grounded plan (backward direction)\<close>

text \<open>Every action schema in the numeric grounded domain is nullary, so a well-formed grounded
  plan action carries an empty argument list and a name among \<open>op_names\<close>. This is the numeric
  counterpart of \<open>grounded_pa_nullary\<close> (the numeric problem is not a \<open>grounded_problem\<close>, so we
  derive nullarity directly from \<^const>\<open>varfree_ground_ac\<close>).\<close>
lemma varfree_ground_pa_nullary:
  assumes "png.wf_classical_plan_action (SimplePlanAction n args)"
  shows "n \<in> set op_names" "args = []"
proof -
  from assms obtain a where a:
    "png.resolve_classical_action_schema n = Some a" "png.action_params_match (head a) args"
    unfolding png.wf_classical_plan_action_simple by (auto split: option.splits)
  have "index_by ast_classical_action_schema_name (actions varfree_ground_dom) n = Some a"
    using a(1) unfolding png.resolve_classical_action_schema_def by simp
  hence "a \<in> set (actions varfree_ground_dom) \<and> ast_classical_action_schema_name a = n"
    by (rule index_by_eq_SomeD)
  hence amem: "a \<in> set (actions varfree_ground_dom)"
    and an: "ast_classical_action_schema_name a = n" by simp_all
  from amem obtain \<pi>'' m where am: "a = varfree_ground_ac \<pi>'' m"
    unfolding varfree_ground_dom_sel using map2_obtain by metis
  have hd: "head a = ActionHead m []" unfolding am by (simp add: varfree_ground_ac_def)
  have "m = n" using an unfolding am by (simp add: varfree_ground_ac_def)
  hence hd': "head a = ActionHead n []" using hd by simp
  show "args = []"
    using a(2) unfolding hd' png.action_params_match_def by simp
  show "n \<in> set op_names"
    using an amem varfree_ground_dom_names by (metis image_eqI list.set_map)
qed

lemma varfree_restore_wf_pa:
  assumes "png.wf_classical_plan_action \<pi>'"
  shows "restore_ground_pa \<pi>' \<in> set ops" "ground_pa (restore_ground_pa \<pi>') = \<pi>'"
proof -
  obtain n args where pi'0: "\<pi>' = SimplePlanAction n args" by (cases \<pi>')
  with assms have nin: "n \<in> set op_names" and args: "args = []"
    using varfree_ground_pa_nullary by blast+
  have pi': "\<pi>' = SimplePlanAction n []" using pi'0 args by simp
  then obtain \<pi> where p: "op_map n = Some \<pi>" "\<pi> \<in> set ops" "op_map_inv \<pi> = Some n"
    using restore_map_entry nin by metis
  have r: "restore_ground_pa \<pi>' = \<pi>" unfolding pi' using p(1) by simp
  have g: "ground_pa \<pi> = \<pi>'" unfolding ground_pa_def pi' using p(3) by simp
  show "restore_ground_pa \<pi>' \<in> set ops" using r p(2) by simp
  show "ground_pa (restore_ground_pa \<pi>') = \<pi>'" using r g by simp
qed

text \<open>The path lifts back: a valid grounded path restores to a valid path of \<open>P\<close> on the same
  world models.\<close>
lemma varfree_ground_path_left:
  assumes "png.valid_classical_plan_alt M \<pi>s' M'"
  shows "valid_classical_plan_alt M (map restore_ground_pa \<pi>s') M'"
  using assms proof (induction \<pi>s' arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons \<pi>' \<pi>s')
  hence en: "png.plan_action_enabled \<pi>' M"
    and val: "png.valid_classical_plan_alt (png.execute_plan_action \<pi>' M) \<pi>s' M'" by auto
  have wf: "png.wf_classical_plan_action \<pi>'" using en by (simp add: png.plan_action_enabled_def)
  let ?\<pi> = "restore_ground_pa \<pi>'"
  have piops: "?\<pi> \<in> set ops" and g: "ground_pa ?\<pi> = \<pi>'" using varfree_restore_wf_pa[OF wf] by auto
  have enM: "plan_action_enabled ?\<pi> M"
    using varfree_ground_enabled_iff[OF piops] en g by simp
  have ex: "png.execute_plan_action \<pi>' M = execute_plan_action ?\<pi> M"
    using varfree_ground_exec_right[OF piops] g by simp
  have "valid_classical_plan_alt (execute_plan_action ?\<pi> M) (map restore_ground_pa \<pi>s') M'"
    using Cons.IH val ex by simp
  thus ?case using enM by simp
qed

theorem varfree_valid_plan_left:
  assumes "png.valid_classical_plan2 \<pi>s'"
  shows "valid_classical_plan2 (restore_ground_plan \<pi>s')"
proof -
  from assms obtain M' where g: "png.valid_classical_plan_alt png.I \<pi>s' M'"
    "valuation M' \<Turnstile>\<^sub>m goal varfree_ground_prob" using png.valid_classical_plan2_alt by blast
  have path: "valid_classical_plan_alt I (map restore_ground_pa \<pi>s') M'"
    using varfree_ground_path_left[OF g(1)[unfolded varfree_png_init]] .
  have goal: "valuation M' \<Turnstile>\<^sub>m goal P" using g(2) by simp
  show ?thesis unfolding valid_classical_plan2_alt using path goal by blast
qed

subsubsection \<open>Plan-preservation equivalence\<close>

theorem varfree_valid_classical_plan_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. png.valid_classical_plan2 \<pi>s')"
  using varfree_valid_plan_right varfree_valid_plan_left by blast

subsubsection \<open>Achievability transfer\<close>

text \<open>Every fact achievable in the numeric grounded problem is achievable in \<open>P\<close>: a
  png-execution path restores to a \<open>P\<close>-execution path on the \<^emph>\<open>same\<close> world models
  (\<open>varfree_ground_path_left\<close>), so the achieving world model is shared.\<close>
lemma varfree_achievable_sub:
  assumes "png.achievable a"
  shows "achievable a"
proof -
  obtain \<pi>s' M where
    M: "png.valid_classical_plan_alt png.I \<pi>s' M"
    and mem: "Atom (uncurry predAtm a) \<in> fst M"
    using assms unfolding png.achievable_def by blast
  have "valid_classical_plan_alt I (map restore_ground_pa \<pi>s') M"
    using varfree_ground_path_left[OF M[unfolded varfree_png_init]] .
  thus ?thesis unfolding achievable_def using mem by blast
qed

end

end
