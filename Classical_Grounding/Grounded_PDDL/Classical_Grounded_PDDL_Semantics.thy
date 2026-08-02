theory Classical_Grounded_PDDL_Semantics
  imports Classical_Grounded_PDDL
begin

subsection \<open> Propositional grounder: semantics, plan-action correspondence, plan preservation \<close>

context wf_grounder begin

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

lemma ground_atoms_predAtm:
  "covered \<phi> facts \<Longrightarrow> a \<in> atoms (ground_fmla \<phi>) \<Longrightarrow> \<exists>p. a = predAtm p []"
  by (induction \<phi> rule: ground_fmla.induct) (auto split: if_splits simp: covered_def)

lemma ground_atoms_dom: "covered \<phi> facts \<Longrightarrow> atoms (ground_fmla \<phi>) \<subseteq> dom (valuation N)"
  using ground_atoms_predAtm val_predAtm_dom by blast

lemma ground_fmla_sem_aux:
  assumes "fst M \<subseteq> set facts"
  shows "covered \<phi> facts \<Longrightarrow>
    (the \<circ> valuation M) \<Turnstile> \<phi> \<longleftrightarrow> (the \<circ> valuation (ground_fmla ` fst M, snd M)) \<Turnstile> ground_fmla \<phi>"
proof (induction \<phi> rule: ground_fmla.induct)
  case ("9" p xs)
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
    using ground_atoms_dom assms(1) by blast
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

text \<open>The \<open>dg: wf_ast_classical_domain\<close> interpretation is already provided one layer down (see the
  \<open>sublocale wf_grounder_cov \<subseteq> dg: wf_ast_classical_domain\<close> above) and inherited here; only the
  grounded-problem interpretation is \<^locale>\<open>wf_grounder\<close>-specific (problem wf needs \<open>init_props\<close>).\<close>

sublocale wf_grounder \<subseteq> pg: grounded_problem P\<^sub>G
  using ground_prob_wf ground_prob_grounded by unfold_locales

text \<open>Shared restore/reachability machinery, provable already in \<^locale>\<open>wf_grounder_num\<close> (it needs
  only \<open>all_ops\<close> / \<open>ops_dist\<close> + the \<^locale>\<open>grounder\<close> name machinery \<open>op_map\<close>/\<open>op_map_inv\<close>, not the
  numeric-freeness assumptions). Placed here so both the propositional grounder and the
  numeric-fluent-retaining grounder inherit it.\<close>
context wf_grounder_num begin

lemma plan_in_ops:
  assumes "valid_classical_plan_alt I \<pi>s M'"
  shows "set \<pi>s \<subseteq> set ops"
proof
  fix \<pi> assume "\<pi> \<in> set \<pi>s"
  with assms have "applicable \<pi>" unfolding applicable_def by blast
  thus "\<pi> \<in> set ops" using all_ops by blast
qed

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

end

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
  by (induction \<phi> rule: ground_fmla.induct) (auto split: if_splits simp: ground_numexp_subst)

lemma ground_effect_subst:
  "map_ast_effect (subst_term t) (ga_eff ga) = ga_eff ga"
  using ground_fmla_subst by (cases ga rule: ga_eff.cases) (simp add: ga_eff_alt ground_neff_subst)

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
  have num2: "numeric_effects (effect ?ga) = []" unfolding ri by (simp add: ga_eff_sel num1)
  have ned1: "numeric_effects_defined [?a] (snd M)"
    using num1 by (auto simp: numeric_effects_defined_def action_list_numeric_update_function_def
        action_numeric_update_function_def lvalues_def dom_def)
  have ned2: "numeric_effects_defined [?ga] (snd M)"
    using num2 by (auto simp: numeric_effects_defined_def action_list_numeric_update_function_def
        action_numeric_update_function_def lvalues_def dom_def)
  have pre: "valuation M \<Turnstile>\<^sub>m precondition ?a \<longleftrightarrow> valuation ?gM \<Turnstile>\<^sub>m precondition ?ga"
    unfolding ri ground_action.sel ga_pre_alt
    using ground_fmla_sem[OF _ assms(1)] pres_covered assms(2) by simp
  show ?thesis
    unfolding plan_action_enabled_def pg.plan_action_enabled_def Let_def
    using ops_wf assms(2) ground_pa_wf[OF assms(2)] num1 num2 pre ned1 ned2
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
  using ops_no_num unfolding resinst_ground_pa_sel(2) by (simp add: ga_eff_sel)

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
  grounder.op_fluents_def
  grounder.fluents_def
  grounder.fluent_names_def
  grounder.fluent_map_def
  grounder.ground_pne_def
  grounder.ground_numexp.simps
  grounder.ground_neff_def
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