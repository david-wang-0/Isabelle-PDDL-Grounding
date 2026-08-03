theory Classical_Grounded_PDDL_Semantics
  imports Classical_Grounded_PDDL
begin

text \<open>The one-shot grounder's semantics and well-formedness are no longer proved directly
  here: they now derive from the Variable_Freeness stage composed with the fact folder --- see
  \<open>Classical_Grounded_PDDL_Factorization\<close>. This theory proves the standalone fact folder's own
  semantics: plan preservation between the (variable-free) input problem and its folded output.\<close>


subsection \<open> Fact folder: semantics, plan-action correspondence, plan preservation \<close>

text \<open>The plan-preservation development for the standalone \<^locale>\<open>wf_fact_folder\<close> stage mirrors
  the one-shot grounder's above, with one structural simplification: the folder \<^emph>\<open>keeps\<close> the
  action names and both sides' plan actions are nullary, so a plan of \<open>fold_prob\<close> is
  \<^emph>\<open>literally\<close> a plan of \<open>P\<close> --- the same \<^term>\<open>SimplePlanAction n []\<close> list is valid on both
  sides (no \<open>ground_pa\<close> / \<open>restore_ground_pa\<close> renaming).\<close>

subsubsection \<open> Generic helpers: pairwise transfer, update functions, execution components \<close>

lemma list_pairwise_map_iff:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f (g x) (g y) \<longleftrightarrow> f' x y"
  shows "list_pairwise f (map g xs) \<longleftrightarrow> list_pairwise f' xs"
  using assms by (induction xs) auto

lemma action_list_numeric_update_function_single:
  "action_list_numeric_update_function [ga] = action_numeric_update_function ga"
  unfolding action_list_numeric_update_function_def by simp

lemma (in ast_classical_problem) execute_plan_action_alt:
  "execute_plan_action \<pi> M =
    (fst M - set (dels (effect (the (res_inst \<pi>)))) \<union> set (adds (effect (the (res_inst \<pi>)))),
     action_numeric_update_function (the (res_inst \<pi>)) (snd M))"
  unfolding execute_plan_action_def
  by (cases M) (simp add: apply_ground_action_alt action_list_numeric_update_function_single)

subsubsection \<open> Resolving and instantiating the nullary plan actions in the folded problem \<close>

text \<open>The resolution/instantiation plumbing for the folded problem's nullary plan actions
  needs no numeric-freeness --- only the covered layer's well-formedness --- so it lives at
  \<^locale>\<open>fact_folder\<close> / \<^locale>\<open>wf_fact_folder_cov\<close>, where both the propositional
  (\<^locale>\<open>wf_fact_folder\<close>) and the numeric (\<^locale>\<open>wf_fact_folder_num\<close>) plan-equivalence
  chains consume it.\<close>

context fact_folder begin

lemma ground_fmla_subst:
  "map_formula (map_atom (subst_term t)) (ground_fmla \<phi>) = ground_fmla \<phi>"
  by (induction \<phi> rule: ground_fmla.induct) (auto split: if_splits simp: ground_numexp_subst)

lemma ground_effect_subst:
  "map_ast_effect (subst_term t) (ga_eff ga) = ga_eff ga"
  using ground_fmla_subst by (cases ga rule: ga_eff.cases) (simp add: ga_eff_alt ground_neff_subst)

lemma fold_ac_instantiation:
  "instantiate_classical_action_schema (fold_ac a) [] =
    GroundAction (ga_pre (the (res_inst (ac_pa a)))) (ga_eff (the (res_inst (ac_pa a))))"
  unfolding instantiate_classical_action_schema_alt fold_ac_sel ga_pre_alt
  by (simp add: ground_fmla_subst ground_effect_subst)

lemma fpg_resolve_eq_fdg: "fpg.resolve_classical_action_schema = fdg.resolve_classical_action_schema"
  by (simp add: fpg.resolve_classical_action_schema_def fdg.resolve_classical_action_schema_def
      fold_prob_sel)

lemma fold_names_eq: "ac_name ` set (actions fold_dom) = ac_name ` set (actions (domain P))"
proof -
  have "map ac_name (actions fold_dom) = map ac_name (actions (domain P))"
    unfolding fold_dom_sel(5) by (simp add: fold_ac_sel(1) comp_def)
  thus ?thesis by (metis list.set_map)
qed

end

context wf_fact_folder_cov begin

lemma fold_resolve:
  assumes "a \<in> set (actions (domain P))"
  shows "fdg.resolve_classical_action_schema (ac_name a) = Some (fold_ac a)"
proof -
  have mem: "fold_ac a \<in> set (actions fold_dom)" unfolding fold_dom_sel(5) using assms by simp
  have "fdg.resolve_classical_action_schema (ac_name (fold_ac a)) = Some (fold_ac a)"
    using fdg.resolve_classical_action_schema_name[OF mem] .
  thus ?thesis by (simp add: fold_ac_sel)
qed

lemma resinst_fold_pa:
  assumes "a \<in> set (actions (domain P))"
  shows "the (fpg.res_inst (ac_pa a)) =
    GroundAction (ga_pre (the (res_inst (ac_pa a)))) (ga_eff (the (res_inst (ac_pa a))))"
proof -
  have "fpg.res_inst (ac_pa a) = Some (instantiate_classical_action_schema (fold_ac a) [])"
    unfolding fpg.res_inst_alt using fold_resolve[OF assms] fpg_resolve_eq_fdg
    by (simp add: ac_pa_def)
  thus ?thesis using fold_ac_instantiation by simp
qed

lemma resinst_fold_pa_sel:
  assumes "a \<in> set (actions (domain P))"
  shows "precondition (the (fpg.res_inst (ac_pa a))) = ga_pre (the (res_inst (ac_pa a)))"
    and "effect (the (fpg.res_inst (ac_pa a))) = ga_eff (the (res_inst (ac_pa a)))"
  unfolding resinst_fold_pa[OF assms] by simp_all

text \<open>Both sides' well-formed plan actions are \<^emph>\<open>exactly\<close> the nullary \<^term>\<open>ac_pa a\<close> for the
  problem's own action schemas: on the \<open>P\<close> side because the input is variable-free, on the
  \<open>fold_prob\<close> side because the folded schemas are nullary and resolution is faithful.\<close>

lemma wf_pa_ac_pa:
  assumes "wf_classical_plan_action \<pi>"
  obtains a where "a \<in> set (actions (domain P))" "\<pi> = ac_pa a"
proof -
  obtain n args where pi0: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  obtain ac where
    ac1: "ac \<in> set (actions (domain P))"
    and ac2: "ac_name ac = n"
    and ac3: "action_params_match (head ac) args"
    using assms wf_pa_refs_ac pi0 by metis
  have par: "ac_params ac = []" using varfree_probD(1)[OF varfree_input] ac1 by blast
  hence "args = []" using ac3 unfolding action_params_match_def by simp
  hence "\<pi> = ac_pa ac" unfolding ac_pa_def using pi0 ac2 by simp
  thus thesis using that ac1 by blast
qed

lemma fold_pa_wf:
  assumes "a \<in> set (actions (domain P))"
  shows "fpg.wf_classical_plan_action (ac_pa a)"
proof -
  have res: "fpg.resolve_classical_action_schema (ac_name a) = Some (fold_ac a)"
    using fold_resolve[OF assms] fpg_resolve_eq_fdg by simp
  have pm: "fpg.action_params_match (ac_head (fold_ac a)) []"
    unfolding fpg.action_params_match_def using fold_ac_sel(2)[of a] by (cases "fold_ac a") simp
  show ?thesis
    unfolding ac_pa_def fpg.wf_classical_plan_action_simple using res pm by simp
qed

lemma fold_pa_inv:
  assumes "fpg.wf_classical_plan_action \<pi>"
  obtains a where "a \<in> set (actions (domain P))" "\<pi> = ac_pa a"
proof -
  obtain n args where pi0: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  obtain ac where
    res: "fpg.resolve_classical_action_schema n = Some ac"
    and pm: "fpg.action_params_match (head ac) args"
    using assms pi0 fpg.wf_classical_plan_action_simple by (auto split: option.splits)
  have mem: "ac \<in> set (actions fold_dom)" and n: "ac_name ac = n"
    using res fdg.res_aux fpg_resolve_eq_fdg by simp_all
  obtain a where
    a: "a \<in> set (actions (domain P))"
    and ac_eq: "ac = fold_ac a"
    using mem unfolding fold_dom_sel(5) by auto
  have "ac_params ac = []" using ac_eq fold_ac_sel(2) by simp
  hence "args = []" using pm unfolding fpg.action_params_match_def by (cases ac) simp
  hence "\<pi> = ac_pa a" unfolding ac_pa_def using pi0 ac_eq n fold_ac_sel(1) by simp
  thus thesis using that a by blast
qed

subsubsection \<open> Covered effects and execution: the propositional component stays in the facts \<close>

lemma covered_predAtom: "is_predAtom a \<Longrightarrow> covered a facts \<longleftrightarrow> a \<in> set facts"
  unfolding covered_def by (cases a rule: is_predAtom.cases) (auto split: atom.splits)

lemma effs_covered_alt:
  assumes "a \<in> set (actions (domain P))"
  shows "set (adds (effect (the (res_inst (ac_pa a)))))
    \<union> set (dels (effect (the (res_inst (ac_pa a))))) \<subseteq> set facts"
proof
  fix \<phi> assume "\<phi> \<in> set (adds (effect (the (res_inst (ac_pa a)))))
    \<union> set (dels (effect (the (res_inst (ac_pa a)))))"
  hence "\<phi> \<in> eff_lits (effect (the (res_inst (ac_pa a))))" by simp
  thus "\<phi> \<in> set facts"
    using eff_lit_covered[OF assms] eff_lit_predAtom[OF assms] covered_predAtom by blast
qed

lemma exec_covered:
  assumes "fst M \<subseteq> set facts"
      and "a \<in> set (actions (domain P))"
  shows "fst (execute_plan_action (ac_pa a) M) \<subseteq> set facts"
  using assms effs_covered_alt by (auto simp: execute_plan_action_alt)

lemma path_actions_ac_pa:
  assumes "valid_classical_plan_alt M \<pi>s M'"
  shows "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons \<pi> \<pi>s)
  hence en: "plan_action_enabled \<pi> M"
    and rest: "valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'"
    by auto
  have "wf_classical_plan_action \<pi>" using en by (simp add: plan_action_enabled_def)
  then obtain a where "a \<in> set (actions (domain P))" "\<pi> = ac_pa a" using wf_pa_ac_pa by metis
  hence "\<pi> \<in> ac_pa ` set (actions (domain P))" by blast
  thus ?case using Cons.IH[OF rest] by simp
qed

lemma alt_covered:
  assumes "fst M \<subseteq> set facts"
      and "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))"
      and "valid_classical_plan_alt M \<pi>s M'"
  shows "fst M' \<subseteq> set facts"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons \<pi> \<pi>s)
  obtain a where
    a: "a \<in> set (actions (domain P))"
    and pi: "\<pi> = ac_pa a"
    using Cons.prems(2) by auto
  have v: "valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'" using Cons.prems(3) by simp
  have covN: "fst (execute_plan_action \<pi> M) \<subseteq> set facts"
    using exec_covered[OF Cons.prems(1) a] pi by simp
  show ?case using Cons.IH[OF covN _ v] Cons.prems(2) by simp
qed

end

context wf_fact_folder begin

subsubsection \<open> Semantics: folding preserves formula truth \<close>

lemma gr_predAtom: "is_predAtom a \<Longrightarrow> is_predAtom (ground_fmla a)"
  by (cases a rule: is_predAtom.cases) simp_all


lemma ground_fmla_inv:
  assumes "M \<subseteq> set facts"
      and "Atom (predAtm n args) \<in> set facts"
      and "ground_fmla (Atom (predAtm n args)) \<in> ground_fmla ` M"
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
  assumes "covered \<phi> facts"
      and "fst M \<subseteq> set facts"
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

lemma fold_init_predAtm:
  assumes "f \<in> set (init fold_prob)"
  shows "is_predAtom f"
proof -
  obtain g where
    g1: "g \<in> set (init P)"
    and g2: "f = ground_fmla g"
    using assms unfolding fold_prob_sel by auto
  show ?thesis unfolding g2 using init_props gr_predAtom g1 by blast
qed

lemma fold_init_no_num: "filter is_numericInitializationAtom (init fold_prob) = []"
  using fold_init_predAtm predAtom_not_num by (auto simp: filter_empty_conv)

lemma fold_init: "fpg.I = (ground_fmla ` fst I, snd I)"
proof -
  have 1: "filter is_predAtom (init fold_prob) = init fold_prob"
    using fold_init_predAtm by (simp add: filter_id_conv)
  have "fpg.I = (ground_fmla ` set (init P), Map.empty)"
    unfolding fpg.I_def using 1 fold_init_no_num by (simp add: fold_prob_sel)
  thus ?thesis using fst_I I_simp by simp
qed

subsubsection \<open> Enabledness correspondence for the shared nullary plan actions \<close>

theorem fold_enabled_iff:
  assumes "fst M \<subseteq> set facts"
      and "a \<in> set (actions (domain P))"
  shows "plan_action_enabled (ac_pa a) M \<longleftrightarrow>
    fpg.plan_action_enabled (ac_pa a) (ground_fmla ` fst M, snd M)"
proof -
  let ?ga = "the (res_inst (ac_pa a))"
  let ?fa = "the (fpg.res_inst (ac_pa a))"
  let ?gM = "(ground_fmla ` fst M, snd M)"
  have ri: "?fa = GroundAction (ga_pre ?ga) (ga_eff ?ga)" using resinst_fold_pa[OF assms(2)] .
  have num1: "numeric_effects (effect ?ga) = []" using assms(2) acs_no_num by blast
  have num2: "numeric_effects (effect ?fa) = []" unfolding ri by (simp add: ga_eff_sel num1)
  have ned1: "numeric_effects_defined [?ga] (snd M)"
    using num1 by (auto simp: numeric_effects_defined_def action_list_numeric_update_function_def
        action_numeric_update_function_def lvalues_def dom_def)
  have ned2: "numeric_effects_defined [?fa] (snd M)"
    using num2 by (auto simp: numeric_effects_defined_def action_list_numeric_update_function_def
        action_numeric_update_function_def lvalues_def dom_def)
  have pre: "valuation M \<Turnstile>\<^sub>m precondition ?ga \<longleftrightarrow> valuation ?gM \<Turnstile>\<^sub>m precondition ?fa"
    unfolding ri ground_action.sel ga_pre_alt
    using ground_fmla_sem[OF _ assms(1)] pres_covered assms(2) by simp
  show ?thesis
    unfolding plan_action_enabled_def fpg.plan_action_enabled_def Let_def
    using ac_pa_wf[OF assms(2)] fold_pa_wf[OF assms(2)] num1 num2 pre ned1 ned2
      numeric_effects_non_intrf_no_numeric_effects enumerate_rhs_pnes_no_numeric_effects
    by simp
qed

subsubsection \<open> Executing a plan action commutes with folding \<close>

lemma num_update_id: "numeric_effects (effect ga) = [] \<Longrightarrow> action_numeric_update_function ga N = N"
  by (simp add: action_numeric_update_function_def)

lemma list_num_update_single_id:
  "numeric_effects (effect ga) = [] \<Longrightarrow> action_list_numeric_update_function [ga] N = N"
  unfolding action_list_numeric_update_function_def by (simp add: num_update_id)

lemma fold_num_ground:
  assumes "a \<in> set (actions (domain P))"
  shows "numeric_effects (effect (the (fpg.res_inst (ac_pa a)))) = []"
  unfolding resinst_fold_pa_sel(2)[OF assms] using acs_no_num assms by (simp add: ga_eff_sel)

lemma fpg_exec_simp:
  assumes "numeric_effects (effect (the (fpg.res_inst \<pi>))) = []"
  shows "fpg.execute_plan_action \<pi> M' =
    (fst M' - set (dels (effect (the (fpg.res_inst \<pi>)))) \<union> set (adds (effect (the (fpg.res_inst \<pi>)))), snd M')"
  using assms list_num_update_single_id
  unfolding fpg.execute_plan_action_def apply_ground_action_alt by (cases M') simp

lemma fpg_exec_fold_simp:
  assumes "a \<in> set (actions (domain P))"
  shows "fpg.execute_plan_action (ac_pa a) (ground_fmla ` fst M, snd M) =
    (ground_fmla ` fst M - ground_fmla ` set (dels (effect (the (res_inst (ac_pa a)))))
       \<union> ground_fmla ` set (adds (effect (the (res_inst (ac_pa a))))), snd M)"
  using fpg_exec_simp[OF fold_num_ground[OF assms], of "(ground_fmla ` fst M, snd M)"]
  unfolding resinst_fold_pa_sel(2)[OF assms]
  by (simp add: ga_eff_sel)

lemma exec_simp:
  assumes "a \<in> set (actions (domain P))"
  shows "execute_plan_action (ac_pa a) M =
    (fst M - set (dels (effect (the (res_inst (ac_pa a)))))
       \<union> set (adds (effect (the (res_inst (ac_pa a))))), snd M)"
  using assms acs_no_num list_num_update_single_id
  unfolding execute_plan_action_def apply_ground_action_alt by (cases M) simp


lemma fold_exec_right:
  assumes "fst M \<subseteq> set facts"
      and "a \<in> set (actions (domain P))"
  shows "fpg.execute_plan_action (ac_pa a) (ground_fmla ` fst M, snd M)
       = (ground_fmla ` fst (execute_plan_action (ac_pa a) M), snd (execute_plan_action (ac_pa a) M))"
proof -
  let ?dl = "set (dels (effect (the (res_inst (ac_pa a)))))"
  let ?ad = "set (adds (effect (the (res_inst (ac_pa a)))))"
  have cov: "?ad \<union> ?dl \<subseteq> set facts" using effs_covered_alt[OF assms(2)] by simp
  have inj: "inj_on ground_fmla (fst M \<union> ?dl \<union> ?ad)"
    by (rule inj_on_subset[OF ground_fmla_inj]) (use assms(1) cov in auto)
  have d_eq: "ground_fmla ` (fst M - ?dl) = ground_fmla ` fst M - ground_fmla ` ?dl"
    by (rule inj_on_image_set_diff[OF inj]) auto
  have un_eq: "ground_fmla ` (fst M - ?dl \<union> ?ad)
    = ground_fmla ` fst M - ground_fmla ` ?dl \<union> ground_fmla ` ?ad"
    by (simp add: image_Un d_eq)
  show ?thesis
    by (simp add: fpg_exec_fold_simp[OF assms(2)] exec_simp[OF assms(2)] un_eq)
qed

subsubsection \<open> Plan-path correspondence and the validity equivalence \<close>


lemma fold_path_right:
  assumes "fst M \<subseteq> set facts"
      and "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))"
      and "valid_classical_plan_alt M \<pi>s M'"
  shows "fpg.valid_classical_plan_alt (ground_fmla ` fst M, snd M) \<pi>s (ground_fmla ` fst M', snd M')"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons \<pi> \<pi>s)
  obtain a where
    a: "a \<in> set (actions (domain P))"
    and pi: "\<pi> = ac_pa a"
    using Cons.prems(2) by auto
  have rest: "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))" using Cons.prems(2) by auto
  have en: "plan_action_enabled \<pi> M"
    and val: "valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'"
    using Cons.prems(3) by auto
  have ex: "fpg.execute_plan_action \<pi> (ground_fmla ` fst M, snd M)
    = (ground_fmla ` fst (execute_plan_action \<pi> M), snd (execute_plan_action \<pi> M))"
    using fold_exec_right[OF Cons.prems(1) a] pi by simp
  have cov': "fst (execute_plan_action \<pi> M) \<subseteq> set facts"
    using exec_covered[OF Cons.prems(1) a] pi by simp
  have "fpg.plan_action_enabled \<pi> (ground_fmla ` fst M, snd M)"
    using fold_enabled_iff[OF Cons.prems(1) a] en pi by simp
  moreover
  have "fpg.valid_classical_plan_alt
      (ground_fmla ` fst (execute_plan_action \<pi> M), snd (execute_plan_action \<pi> M))
      \<pi>s (ground_fmla ` fst M', snd M')"
    using Cons.IH[OF cov' rest val] .
  ultimately
  show ?case using ex by simp
qed

theorem fold_valid_plan_right:
  assumes "valid_classical_plan2 \<pi>s"
  shows "fpg.valid_classical_plan2 \<pi>s"
proof -
  obtain M' where
    M1: "valid_classical_plan_alt I \<pi>s M'"
    and M2: "valuation M' \<Turnstile>\<^sub>m goal P"
    using assms valid_classical_plan2_alt by blast
  have acs: "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))" using path_actions_ac_pa[OF M1] .
  have cov: "fst M' \<subseteq> set facts" using alt_covered[OF i_covered acs M1] .
  have path: "fpg.valid_classical_plan_alt fpg.I \<pi>s (ground_fmla ` fst M', snd M')"
    unfolding fold_init using fold_path_right[OF i_covered acs M1] .
  have goal: "valuation (ground_fmla ` fst M', snd M') \<Turnstile>\<^sub>m goal fold_prob"
    using ground_goal_sem[OF cov] M2 by (simp add: fold_prob_sel)
  show ?thesis using path goal fpg.valid_classical_plan2_alt by blast
qed

text \<open> Left direction: the \<^emph>\<open>same\<close> plan-action list transfers back --- no restore map. \<close>

lemma fold_path_left:
  assumes "fst M \<subseteq> set facts"
      and "fpg.valid_classical_plan_alt (ground_fmla ` fst M, snd M) \<pi>s gM'"
  shows "\<exists>M'. gM' = (ground_fmla ` fst M', snd M') \<and> valid_classical_plan_alt M \<pi>s M'"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil
  hence "gM' = (ground_fmla ` fst M, snd M)" by simp
  thus ?case by auto
next
  case (Cons \<pi> \<pi>s)
  hence en: "fpg.plan_action_enabled \<pi> (ground_fmla ` fst M, snd M)"
    and val: "fpg.valid_classical_plan_alt
      (fpg.execute_plan_action \<pi> (ground_fmla ` fst M, snd M)) \<pi>s gM'"
    by auto
  have wf: "fpg.wf_classical_plan_action \<pi>" using en by (simp add: fpg.plan_action_enabled_def)
  obtain a where
    a: "a \<in> set (actions (domain P))"
    and pi: "\<pi> = ac_pa a"
    using fold_pa_inv[OF wf] by blast
  let ?N = "execute_plan_action \<pi> M"
  have ex: "fpg.execute_plan_action \<pi> (ground_fmla ` fst M, snd M) = (ground_fmla ` fst ?N, snd ?N)"
    using fold_exec_right[OF Cons.prems(1) a] pi by simp
  have covN: "fst ?N \<subseteq> set facts" using exec_covered[OF Cons.prems(1) a] pi by simp
  have enM: "plan_action_enabled \<pi> M"
    using fold_enabled_iff[OF Cons.prems(1) a] en pi by simp
  have "fpg.valid_classical_plan_alt (ground_fmla ` fst ?N, snd ?N) \<pi>s gM'" using val ex by simp
  then obtain M' where
    M1: "gM' = (ground_fmla ` fst M', snd M')"
    and M2: "valid_classical_plan_alt ?N \<pi>s M'"
    using Cons.IH[OF covN] by blast
  have "valid_classical_plan_alt M (\<pi> # \<pi>s) M'" using enM M2 by simp
  thus ?case using M1 by auto
qed

theorem fold_valid_plan_left:
  assumes "fpg.valid_classical_plan2 \<pi>s"
  shows "valid_classical_plan2 \<pi>s"
proof -
  obtain gM' where
    g1: "fpg.valid_classical_plan_alt fpg.I \<pi>s gM'"
    and g2: "valuation gM' \<Turnstile>\<^sub>m goal fold_prob"
    using assms fpg.valid_classical_plan2_alt by blast
  obtain M' where
    M1: "gM' = (ground_fmla ` fst M', snd M')"
    and M2: "valid_classical_plan_alt I \<pi>s M'"
    using fold_path_left[OF i_covered g1[unfolded fold_init]] by blast
  have acs: "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))" using path_actions_ac_pa[OF M2] .
  have cov: "fst M' \<subseteq> set facts" using alt_covered[OF i_covered acs M2] .
  have goalM': "valuation M' \<Turnstile>\<^sub>m goal P"
    using ground_goal_sem[OF cov] g2 M1 by (simp add: fold_prob_sel)
  show ?thesis unfolding valid_classical_plan2_alt using M2 goalM' by blast
qed

theorem fold_valid_classical_plan_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s. fpg.valid_classical_plan2 \<pi>s)"
  using fold_valid_plan_right fold_valid_plan_left by blast

end


subsection \<open> Numeric fact folder: state renaming and semantics transfer \<close>

text \<open>The numeric groundwork for the \<^locale>\<open>wf_fact_folder_num\<close> plan-equivalence chain. With
  fluents retained, the folded problem's numeric states are the input's numeric states
  \<^emph>\<open>renamed\<close> along \<open>ground_pne\<close>: \<open>fold_nstate\<close> maps a folded (nullary) fluent back to the
  original fluent it names and looks that up, and is \<open>None\<close> outside the folded fluents. The
  lemmas below transfer expression valuation, divisor enumeration, atom/formula valuation, and
  the numeric update functions across that renaming; everything lives at the
  \<^locale>\<open>wf_fact_folder_cov\<close> layer (injectivity of the naming is all that is needed), so both
  the propositional and the numeric problem layers can consume it.\<close>

lemma covered_num_atom_pnes:
  assumes "covered_num (Atom a) facts fluents"
  shows "set (atom_enumerate_primitive_numeric_expressions a) \<subseteq> set fluents"
  using covered_num_fluent_mem[OF assms] by auto

context fact_folder begin

text \<open>The numeric-state renaming: a folded fluent name is looked up back to the fluent it
  re-indexes, all other keys are undefined. This is the numeric component of the folded world
  model corresponding to input numeric state \<open>N\<close>.\<close>
definition fold_nstate :: "numeric_world_model \<Rightarrow> numeric_world_model" where
  "fold_nstate N = (\<lambda>x. case map_of (zip (map ground_pne fluents) fluents) x of
     Some fl \<Rightarrow> N fl | None \<Rightarrow> None)"

lemma fold_nstate_None:
  assumes "map_of (zip (map ground_pne fluents) fluents) x = None"
  shows "fold_nstate N x = None"
  unfolding fold_nstate_def assms by simp

lemma fold_nstate_Some:
  assumes "map_of (zip (map ground_pne fluents) fluents) x = Some fl"
  shows "fold_nstate N x = N fl"
  unfolding fold_nstate_def assms by simp

lemma fold_nstate_keyE:
  assumes "map_of (zip (map ground_pne fluents) fluents) x = Some fl"
  obtains "fl \<in> set fluents" and "x = ground_pne fl"
proof -
  have mem: "(x, fl) \<in> set (zip (map ground_pne fluents) fluents)"
    using map_of_SomeD[OF assms] .
  then obtain i where
    i: "i < length fluents"
    and x: "map ground_pne fluents ! i = x"
    and fl: "fluents ! i = fl"
    using in_set_zip[of "(x, fl)"] by auto
  have "fl \<in> set fluents" using i fl nth_mem by blast
  moreover
  have "x = ground_pne fl" using i x fl by simp
  ultimately
  show thesis using that by blast
qed

text \<open>Folding maps the divisor enumeration through \<open>ground_numexp\<close> pointwise, so
  division-by-zero definedness questions transfer along the valuation equality below.\<close>
lemma ground_numexp_divisors:
  "enumerate_divisor_expressions (ground_numexp e) = map ground_numexp (enumerate_divisor_expressions e)"
  by (induction e) simp_all

text \<open>Selectors of the folded numeric effect, and the folded expression's / effect's PNE,
  right-hand-side PNE and lvalue enumerations: everything maps pointwise through
  \<open>ground_pne\<close>.\<close>
lemma ground_neff_sel:
  "numeric_effect.lhs (ground_neff ne) = ground_pne (numeric_effect.lhs ne)"
  "numeric_effect.op (ground_neff ne) = numeric_effect.op ne"
  "numeric_effect.rhs (ground_neff ne) = ground_numexp (numeric_effect.rhs ne)"
  by (simp_all add: ground_neff_def split: numeric_effect.split)

lemma ground_numexp_pnes:
  "enumerate_primitive_numeric_expressions (ground_numexp e)
   = map ground_pne (enumerate_primitive_numeric_expressions e)"
  by (induction e) simp_all

lemma ground_neff_rhs_pnes:
  "numeric_effect_enumerate_rhs_primitive_numeric_expressions (ground_neff ne)
   = map ground_pne (numeric_effect_enumerate_rhs_primitive_numeric_expressions ne)"
  by (cases ne) (simp add: ground_neff_def ground_numexp_pnes)

lemma ground_rhs_pnes:
  "ast_effect_enumerate_rhs_primitive_numeric_expressions (ga_eff ga)
   = map ground_pne (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ga))"
proof -
  obtain ad dl nes where eff: "effect ga = Effect ad dl nes" by (cases "effect ga")
  show ?thesis
    unfolding ga_eff_alt eff by (simp add: map_concat comp_def ground_neff_rhs_pnes)
qed

lemma ground_lvalues:
  "lvalues (GroundAction (ga_pre ga) (ga_eff ga)) = map ground_pne (lvalues ga)"
  unfolding lvalues_def by (simp add: ga_eff_sel ground_neff_sel comp_def)

end

context wf_fact_folder_cov begin

text \<open>The folded-fluent lookup inverts \<open>ground_pne\<close> on the reachable fluents --- this is where
  \<open>ground_pne_inj\<close> (i.e. distinctness of the generated \<open>fluent_names\<close>) enters.\<close>
lemma ground_pne_key:
  assumes "fl \<in> set fluents"
  shows "map_of (zip (map ground_pne fluents) fluents) (ground_pne fl :: object primitive_numeric_expression) = Some fl"
proof -
  have "map_of (zip (map ground_pne fluents) fluents) (ground_pne fl :: object primitive_numeric_expression) \<noteq> None"
    using assms by (simp add: map_of_zip_is_None)
  then obtain fl' where fl': "map_of (zip (map ground_pne fluents) fluents) (ground_pne fl :: object primitive_numeric_expression) = Some fl'"
    by blast
  have "fl' = fl"
  proof (rule fold_nstate_keyE[OF fl'])
    assume "fl' \<in> set fluents" and "ground_pne fl = (ground_pne fl' :: object primitive_numeric_expression)"
    thus "fl' = fl" using inj_onD[OF ground_pne_inj _ assms] by blast
  qed
  thus ?thesis using fl' by simp
qed

lemma fold_nstate_ground_pne:
  assumes "fl \<in> set fluents"
  shows "fold_nstate N (ground_pne fl) = N fl"
  using fold_nstate_Some[OF ground_pne_key[OF assms]] .

lemma fold_nstate_dom:
  "dom (fold_nstate N) = ground_pne ` (set fluents \<inter> dom N)"
proof -
  have "x \<in> dom (fold_nstate N) \<longleftrightarrow> x \<in> ground_pne ` (set fluents \<inter> dom N)" for x
  proof (cases "map_of (zip (map ground_pne fluents) fluents) x")
    case None
    have "x \<noteq> ground_pne fl" if "fl \<in> set fluents" for fl
      using ground_pne_key[OF that] None that by auto
    hence "x \<notin> ground_pne ` (set fluents \<inter> dom N)" by blast
    thus ?thesis using fold_nstate_None[OF None] by (simp add: domIff)
  next
    case (Some fl)
    obtain mem: "fl \<in> set fluents" and x: "x = ground_pne fl"
      by (rule fold_nstate_keyE[OF Some])
    have d: "x \<in> dom (fold_nstate N) \<longleftrightarrow> fl \<in> dom N"
      using fold_nstate_Some[OF Some] by (simp add: domIff)
    have inj: "fl' = fl" if "fl' \<in> set fluents" and "x = ground_pne fl'" for fl'
      using inj_onD[OF ground_pne_inj] that mem x by blast
    show ?thesis using d inj mem x by blast
  qed
  thus ?thesis by blast
qed

text \<open>Folding preserves numeric-expression valuation: the folded expression evaluated in the
  renamed state agrees with the original --- including undefinedness (missing fluents and
  division by zero transfer both ways), since the two sides are equal as \<^type>\<open>option\<close>
  values.\<close>
lemma ground_numexp_val:
  assumes "set (enumerate_primitive_numeric_expressions e) \<subseteq> set fluents"
  shows "(ground_numexp e)\<lbrakk>fold_nstate N\<rbrakk> = e\<lbrakk>N\<rbrakk>"
  using assms by (induction e) (simp_all add: fold_nstate_ground_pne)

text \<open>The numeric-atom cases of the valuation correspondence: on numeric comparison atoms the
  folded valuation is \<^emph>\<open>equal\<close> (as an \<^type>\<open>option\<close> value) to the original, for any logical
  components on either side.\<close>
lemma fold_valuation_num_atom:
  assumes l: "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
      and r: "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
  shows "valuation (L, fold_nstate (snd M)) (numericEqAtm (ground_numexp l) (ground_numexp r)) = valuation M (numericEqAtm l r)"
    and "valuation (L, fold_nstate (snd M)) (numericLessAtm (ground_numexp l) (ground_numexp r)) = valuation M (numericLessAtm l r)"
    and "valuation (L, fold_nstate (snd M)) (numericLEAtm (ground_numexp l) (ground_numexp r)) = valuation M (numericLEAtm l r)"
    and "valuation (L, fold_nstate (snd M)) (numericGreaterAtm (ground_numexp l) (ground_numexp r)) = valuation M (numericGreaterAtm l r)"
    and "valuation (L, fold_nstate (snd M)) (numericGEAtm (ground_numexp l) (ground_numexp r)) = valuation M (numericGEAtm l r)"
  by (simp_all add: valuation_def ground_numexp_val[OF l] ground_numexp_val[OF r])

text \<open>Atom-definedness transfers: a \<^const>\<open>covered_num\<close> formula's atoms are in the valuation's
  domain iff the folded formula's atoms are (equality atoms compile to \<open>\<bottom>\<close>/\<open>\<^bold>\<not>\<bottom>\<close> and are always
  defined; numeric atoms transfer by the valuation equality above).\<close>
lemma ground_fmla_dom_num:
  assumes "covered_num \<phi> facts fluents"
  shows "(\<forall>a \<in> atoms \<phi>. a \<in> dom (valuation M)) \<longleftrightarrow>
    (\<forall>a \<in> atoms (ground_fmla \<phi>). a \<in> dom (valuation (ground_fmla ` fst M, fold_nstate (snd M))))"
  using assms
proof (induction \<phi> rule: ground_fmla.induct)
  case ("4" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(1) by (simp add: domIff)
next
  case ("5" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(2) by (simp add: domIff)
next
  case ("6" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(3) by (simp add: domIff)
next
  case ("7" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(4) by (simp add: domIff)
next
  case ("8" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(5) by (simp add: domIff)
qed (auto simp: valuation_def domIff)

text \<open>The numeric generalisation of \<open>ground_fmla_sem_aux\<close>: truth under the total-ised valuation
  transfers for any \<^const>\<open>covered_num\<close> formula.\<close>
lemma ground_fmla_sem_aux_num:
  assumes "fst M \<subseteq> set facts"
      and "covered_num \<phi> facts fluents"
  shows "(the \<circ> valuation M) \<Turnstile> \<phi> \<longleftrightarrow>
    (the \<circ> valuation (ground_fmla ` fst M, fold_nstate (snd M))) \<Turnstile> ground_fmla \<phi>"
  using assms(2)
proof (induction \<phi> rule: ground_fmla.induct)
  case ("4" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(1) by simp
next
  case ("5" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(2) by simp
next
  case ("6" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(3) by simp
next
  case ("7" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(4) by simp
next
  case ("8" l r)
  hence "set (enumerate_primitive_numeric_expressions l) \<subseteq> set fluents"
    and "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using covered_num_atom_pnes by fastforce+
  thus ?case using fold_valuation_num_atom(5) by simp
next
  case ("9" p xs)
  hence mem: "Atom (predAtm p xs) \<in> set facts" using covered_num_predAtm_mem by fastforce
  have "(Atom (predAtm p xs) \<in> fst M) = (ground_fmla (Atom (predAtm p xs)) \<in> ground_fmla ` fst M)"
  proof
    assume "Atom (predAtm p xs) \<in> fst M"
    thus "ground_fmla (Atom (predAtm p xs)) \<in> ground_fmla ` fst M" by (rule imageI)
  next
    assume "ground_fmla (Atom (predAtm p xs)) \<in> ground_fmla ` fst M"
    thus "Atom (predAtm p xs) \<in> fst M"
      using ground_fmla_inj inj_on_image_mem_iff assms(1) mem by metis
  qed
  thus ?case unfolding valuation_def by simp
qed (auto simp: valuation_def)

text \<open>The numeric generalisation of \<open>ground_fmla_sem\<close>: full \<open>\<Turnstile>\<^sub>m\<close> semantics (truth \<^emph>\<open>and\<close>
  definedness) transfer across the fold.\<close>
lemma ground_fmla_sem_num:
  assumes "covered_num \<phi> facts fluents"
      and "fst M \<subseteq> set facts"
  shows "valuation M \<Turnstile>\<^sub>m \<phi> \<longleftrightarrow>
    valuation (ground_fmla ` fst M, fold_nstate (snd M)) \<Turnstile>\<^sub>m ground_fmla \<phi>"
  unfolding map_formula_semantics_def
  using ground_fmla_dom_num[OF assms(1)] ground_fmla_sem_aux_num[OF assms(2) assms(1)] by simp

text \<open>Executing a single folded numeric effect on the renamed states is the renaming of
  executing the original: the \<open>if x = lhs\<close> test inside \<^const>\<open>numeric_update_function\<close>
  transfers through injectivity of \<open>ground_pne\<close>, the right-hand side by the valuation
  equality, and everything outside the folded fluents is \<open>None\<close> on both sides.\<close>
lemma ground_neff_update_num:
  assumes "numeric_effect.lhs ne \<in> set fluents"
      and "set (enumerate_primitive_numeric_expressions (numeric_effect.rhs ne)) \<subseteq> set fluents"
  shows "numeric_update_function (ground_neff ne) (fold_nstate N) (fold_nstate N')
       = fold_nstate (numeric_update_function ne N N')"
proof -
  obtain opr l r where ne: "ne = NumericEffect opr l r" by (cases ne)
  have l: "l \<in> set fluents" using assms(1) unfolding ne by simp
  have r: "(ground_numexp r)\<lbrakk>fold_nstate N\<rbrakk> = r\<lbrakk>N\<rbrakk>"
    using ground_numexp_val assms(2) unfolding ne by simp
  have glhs: "numeric_effect.lhs (ground_neff ne :: object numeric_effect) = ground_pne l"
    unfolding ne ground_neff_def by simp
  show ?thesis
  proof (rule ext)
    fix x :: "object primitive_numeric_expression"
    show "numeric_update_function (ground_neff ne) (fold_nstate N) (fold_nstate N') x
        = fold_nstate (numeric_update_function ne N N') x"
    proof (cases "map_of (zip (map ground_pne fluents) fluents) x")
      case None
      hence xl: "x \<noteq> ground_pne l" using ground_pne_key[OF l] l by auto
      have "numeric_update_function (ground_neff ne) (fold_nstate N) (fold_nstate N') x
          = fold_nstate N' x"
        using numeric_update_function_only_changes_lvalue[of x "ground_neff ne" "fold_nstate N" "fold_nstate N'"]
        using xl glhs by simp
      thus ?thesis using fold_nstate_None[OF None] by simp
    next
      case (Some fl)
      obtain mem: "fl \<in> set fluents" and x: "x = ground_pne fl"
        by (rule fold_nstate_keyE[OF Some])
      show ?thesis
      proof (cases "fl = l")
        case True
        have "numeric_update_function (ground_neff ne) (fold_nstate N) (fold_nstate N') x
            = numeric_update_function ne N N' l"
          unfolding ne ground_neff_def x True
          by (cases opr) (simp_all add: r fold_nstate_ground_pne[OF l])
        thus ?thesis using fold_nstate_Some[OF Some] True by simp
      next
        case False
        hence xl: "x \<noteq> ground_pne l"
          using inj_onD[OF ground_pne_inj] mem l x by blast
        have "numeric_update_function (ground_neff ne) (fold_nstate N) (fold_nstate N') x
            = fold_nstate N' x"
          using numeric_update_function_only_changes_lvalue[of x "ground_neff ne" "fold_nstate N" "fold_nstate N'"]
          using xl glhs by simp
        also have "\<dots> = N' fl" using fold_nstate_Some[OF Some] .
        also have "\<dots> = numeric_update_function ne N N' fl"
          using numeric_update_function_only_changes_lvalue[of fl ne N N'] False
          unfolding ne by simp
        also have "\<dots> = fold_nstate (numeric_update_function ne N N') x"
          using fold_nstate_Some[OF Some] by simp
        finally show ?thesis .
      qed
    qed
  qed
qed

text \<open>Executing a folded action's whole numeric-effect list commutes with the renaming ---
  induction over the effect list, lifting the single-effect commutation. Stated for the
  explicit \<^const>\<open>GroundAction\<close> the folded nullary plan action resolves to
  (\<open>resinst_fold_pa\<close>), so the \<^locale>\<open>wf_fact_folder_num\<close> execution chain can rewrite with it
  directly.\<close>
lemma fold_action_update_num:
  assumes "a \<in> set (actions (domain P))"
  shows "action_numeric_update_function
           (GroundAction (ga_pre (the (res_inst (ac_pa a)))) (ga_eff (the (res_inst (ac_pa a)))))
           (fold_nstate N)
       = fold_nstate (action_numeric_update_function (the (res_inst (ac_pa a))) N)"
proof -
  let ?ga = "the (res_inst (ac_pa a))"
  let ?nes = "numeric_effects (effect ?ga)"
  have lhs_mem: "numeric_effect.lhs ne \<in> set fluents" if "ne \<in> set ?nes" for ne
  proof -
    obtain opr l r where ne: "ne = NumericEffect opr l r" by (cases ne)
    have "l \<in> set (op_fluents (ac_pa a))"
      using neff_lhs_in_op_fluents that unfolding ne by blast
    thus ?thesis using acs_fluents assms unfolding ne by auto
  qed
  have rhs_sub: "set (enumerate_primitive_numeric_expressions (numeric_effect.rhs ne)) \<subseteq> set fluents"
    if "ne \<in> set ?nes" for ne
  proof -
    obtain opr l r where ne: "ne = NumericEffect opr l r" by (cases ne)
    have "set (enumerate_primitive_numeric_expressions r) \<subseteq> set (op_fluents (ac_pa a))"
      using neff_rhs_pnes_in_op_fluents that unfolding ne by blast
    thus ?thesis using acs_fluents assms unfolding ne by auto
  qed
  have main: "fold (\<circ>) (map (\<lambda>u. numeric_update_function u (fold_nstate N)) (map ground_neff nes)) id (fold_nstate N')
            = fold_nstate (fold (\<circ>) (map (\<lambda>u. numeric_update_function u N) nes) id N')"
    if "set nes \<subseteq> set ?nes" for nes N'
    using that
  proof (induction nes arbitrary: N')
    case Nil thus ?case by simp
  next
    case (Cons ne nes)
    have ne_mem: "ne \<in> set ?nes" using Cons.prems by simp
    have upd: "numeric_update_function (ground_neff ne) (fold_nstate N) (fold_nstate N')
             = fold_nstate (numeric_update_function ne N N')"
      using ground_neff_update_num[OF lhs_mem[OF ne_mem] rhs_sub[OF ne_mem]] .
    have "fold (\<circ>) (map (\<lambda>u. numeric_update_function u (fold_nstate N)) (map ground_neff (ne # nes))) id (fold_nstate N')
        = fold (\<circ>) (map (\<lambda>u. numeric_update_function u (fold_nstate N)) (map ground_neff nes)) id
            (numeric_update_function (ground_neff ne) (fold_nstate N) (fold_nstate N'))"
      by (simp add: fold_of_comp'[where g="numeric_update_function (ground_neff ne) (fold_nstate N)"])
    also have "\<dots> = fold (\<circ>) (map (\<lambda>u. numeric_update_function u (fold_nstate N)) (map ground_neff nes)) id
            (fold_nstate (numeric_update_function ne N N'))"
      unfolding upd ..
    also have "\<dots> = fold_nstate (fold (\<circ>) (map (\<lambda>u. numeric_update_function u N) nes) id
            (numeric_update_function ne N N'))"
      by (rule Cons.IH) (use Cons.prems in auto)
    also have "\<dots> = fold_nstate (fold (\<circ>) (map (\<lambda>u. numeric_update_function u N) (ne # nes)) id N')"
      by (simp add: fold_of_comp'[where g="numeric_update_function ne N"])
    finally show ?case .
  qed
  show ?thesis
    unfolding action_numeric_update_function_def
    using main[of ?nes N] by (simp add: ga_eff_sel)
qed

text \<open>The folded-fluent image of a subset of the reachable fluents lies in the renamed state's
  domain iff the subset lies in the original state's domain.\<close>
lemma ground_pne_dom_iff:
  assumes "S \<subseteq> set fluents"
  shows "ground_pne ` S \<subseteq> dom (fold_nstate N) \<longleftrightarrow> S \<subseteq> dom N"
proof
  assume L: "ground_pne ` S \<subseteq> dom (fold_nstate N)"
  show "S \<subseteq> dom N"
  proof
    fix x assume x: "x \<in> S"
    have "(ground_pne x :: object primitive_numeric_expression) \<in> ground_pne ` (set fluents \<inter> dom N)"
      using L x fold_nstate_dom by auto
    then obtain y where
      y: "y \<in> set fluents \<inter> dom N"
      and eq: "(ground_pne x :: object primitive_numeric_expression) = ground_pne y"
      by auto
    have "x = y" using inj_onD[OF ground_pne_inj eq] assms x y by blast
    thus "x \<in> dom N" using y by blast
  qed
next
  assume "S \<subseteq> dom N"
  hence "S \<subseteq> set fluents \<inter> dom N" using assms by blast
  thus "ground_pne ` S \<subseteq> dom (fold_nstate N)" unfolding fold_nstate_dom by blast
qed

text \<open>Renaming an association list's fluent keys along \<open>ground_pne\<close> commutes with \<open>map_of\<close>:
  the renamed table is the \<open>fold_nstate\<close> renaming of the original table. This is what folds the
  initial function assignments.\<close>
lemma fold_nstate_map_of:
  assumes "fst ` set xs \<subseteq> set fluents"
  shows "map_of (map (\<lambda>(l, v). (ground_pne l, v)) xs) = fold_nstate (map_of xs)"
proof (rule ext)
  fix x :: "object primitive_numeric_expression"
  show "map_of (map (\<lambda>(l, v). (ground_pne l, v)) xs) x = fold_nstate (map_of xs) x"
  proof (cases "map_of (zip (map ground_pne fluents) fluents) x")
    case None
    have ne: "x \<noteq> ground_pne fl" if "fl \<in> set fluents" for fl
      using ground_pne_key[OF that] None that by auto
    have "map_of (map (\<lambda>(l, v). (ground_pne l, v)) xs) x = None"
      using assms ne by (induction xs) auto
    thus ?thesis using fold_nstate_None[OF None] by simp
  next
    case (Some fl)
    obtain mem: "fl \<in> set fluents" and x: "x = ground_pne fl"
      by (rule fold_nstate_keyE[OF Some])
    have "map_of (map (\<lambda>(l, v). (ground_pne l, v)) xs)
            (ground_pne fl :: object primitive_numeric_expression) = map_of xs fl"
      using assms proof (induction xs)
      case Nil thus ?case by simp
    next
      case (Cons p xs)
      obtain l v where p: "p = (l, v)" by (cases p)
      have l: "l \<in> set fluents" using Cons.prems unfolding p by simp
      show ?case
      proof (cases "l = fl")
        case True thus ?thesis unfolding p by simp
      next
        case False
        hence "(ground_pne fl :: object primitive_numeric_expression) \<noteq> ground_pne l"
          using inj_onD[OF ground_pne_inj] mem l by blast
        thus ?thesis unfolding p using Cons.IH Cons.prems False by simp
      qed
    qed
    thus ?thesis using fold_nstate_Some[OF Some] x by simp
  qed
qed

subsubsection \<open> The five enabledness conjuncts transfer through the renaming \<close>

text \<open>The reachable actions' lvalues and right-hand-side PNEs lie in the reachable fluents
  (components of \<open>op_fluents\<close> under \<open>acs_fluents\<close>).\<close>

lemma acs_lvalues:
  assumes "a \<in> set (actions (domain P))"
  shows "set (lvalues (the (res_inst (ac_pa a)))) \<subseteq> set fluents"
proof -
  have "set (lvalues (the (res_inst (ac_pa a)))) \<subseteq> set (op_fluents (ac_pa a))"
    unfolding lvalues_def op_fluents_def Let_def
    by (auto simp: numeric_effect.case_eq_if)
  thus ?thesis using acs_fluents assms by blast
qed

lemma acs_rhs_pnes:
  assumes "a \<in> set (actions (domain P))"
  shows "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect (the (res_inst (ac_pa a))))) \<subseteq> set fluents"
proof -
  have "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect (the (res_inst (ac_pa a)))))
      \<subseteq> set (op_fluents (ac_pa a))"
    unfolding op_fluents_def Let_def by auto
  thus ?thesis using acs_fluents assms by blast
qed

text \<open>Non-interference is syntactic on the numeric-effect list; it transfers because folding
  keeps the operators and renames the lvalues injectively.\<close>
lemma fold_non_intrf_iff:
  assumes "a \<in> set (actions (domain P))"
  shows "numeric_effects_non_intrf
           (GroundAction (ga_pre (the (res_inst (ac_pa a)))) (ga_eff (the (res_inst (ac_pa a)))))
     \<longleftrightarrow> numeric_effects_non_intrf (the (res_inst (ac_pa a)))"
proof -
  let ?ga = "the (res_inst (ac_pa a))"
  let ?nes = "numeric_effects (effect ?ga)"
  have lhs_mem: "numeric_effect.lhs ne \<in> set fluents" if "ne \<in> set ?nes" for ne
  proof -
    obtain opr l r where ne: "ne = NumericEffect opr l r" by (cases ne)
    have "l \<in> set (op_fluents (ac_pa a))"
      using neff_lhs_in_op_fluents that unfolding ne by blast
    thus ?thesis using acs_fluents assms unfolding ne by auto
  qed
  have iff: "(numeric_effect.lhs (ground_neff x :: object numeric_effect) = numeric_effect.lhs (ground_neff y)
          \<longrightarrow> numeric_effect_same_type (numeric_effect.op (ground_neff x :: object numeric_effect)) (numeric_effect.op (ground_neff y :: object numeric_effect))
            \<and> numeric_effect.op (ground_neff x :: object numeric_effect) \<noteq> Assign)
      \<longleftrightarrow> (numeric_effect.lhs x = numeric_effect.lhs y
          \<longrightarrow> numeric_effect_same_type (numeric_effect.op x) (numeric_effect.op y)
            \<and> numeric_effect.op x \<noteq> Assign)"
    if "x \<in> set ?nes" and "y \<in> set ?nes" for x y
  proof -
    have "(ground_pne (numeric_effect.lhs x) :: object primitive_numeric_expression) = ground_pne (numeric_effect.lhs y)
        \<longleftrightarrow> numeric_effect.lhs x = numeric_effect.lhs y"
      using inj_onD[OF ground_pne_inj] lhs_mem[OF that(1)] lhs_mem[OF that(2)] by auto
    thus ?thesis by (simp add: ground_neff_sel)
  qed
  have "list_pairwise
          (\<lambda>a b. numeric_effect.lhs a = numeric_effect.lhs b \<longrightarrow>
                 numeric_effect_same_type (numeric_effect.op a) (numeric_effect.op b) \<and> numeric_effect.op a \<noteq> Assign)
          (map ground_neff ?nes :: object numeric_effect list)
      \<longleftrightarrow> list_pairwise
          (\<lambda>a b. numeric_effect.lhs a = numeric_effect.lhs b \<longrightarrow>
                 numeric_effect_same_type (numeric_effect.op a) (numeric_effect.op b) \<and> numeric_effect.op a \<noteq> Assign)
          ?nes"
    by (rule list_pairwise_map_iff) (use iff in blast)
  thus ?thesis
    unfolding numeric_effects_non_intrf_def by (simp add: ga_eff_sel)
qed

text \<open>Definedness of the numeric effects transfers: the renamed update commutes
  (\<open>fold_action_update_num\<close>), the renamed domain restricts to the reachable fluents, and outside
  the lvalues the update leaves the state untouched.\<close>
lemma fold_num_defined_iff:
  assumes "a \<in> set (actions (domain P))"
  shows "numeric_effects_defined
           [GroundAction (ga_pre (the (res_inst (ac_pa a)))) (ga_eff (the (res_inst (ac_pa a))))]
           (fold_nstate N)
     \<longleftrightarrow> numeric_effects_defined [the (res_inst (ac_pa a))] N"
proof -
  let ?ga = "the (res_inst (ac_pa a))"
  let ?fa = "GroundAction (ga_pre ?ga) (ga_eff ?ga) :: ground_action"
  let ?W = "action_numeric_update_function ?ga N"
  have lv: "set (lvalues ?ga) \<subseteq> set fluents" using acs_lvalues[OF assms] .
  have upd: "action_numeric_update_function ?fa (fold_nstate N) = fold_nstate ?W"
    using fold_action_update_num[OF assms] .
  have lvfa: "lvalues ?fa = map ground_pne (lvalues ?ga)" using ground_lvalues .
  have L: "numeric_effects_defined [?fa] (fold_nstate N)
       \<longleftrightarrow> (\<forall>l \<in> dom (fold_nstate N) \<union> set (lvalues ?fa). fold_nstate ?W l \<noteq> None)"
    unfolding numeric_effects_defined_def
    by (simp add: action_list_numeric_update_function_single upd)
  have R: "numeric_effects_defined [?ga] N
       \<longleftrightarrow> (\<forall>fl \<in> dom N \<union> set (lvalues ?ga). ?W fl \<noteq> None)"
    unfolding numeric_effects_defined_def
    by (simp add: action_list_numeric_update_function_single)
  have un: "dom (fold_nstate N) \<union> set (lvalues ?fa)
          = ground_pne ` ((set fluents \<inter> dom N) \<union> set (lvalues ?ga))"
    unfolding fold_nstate_dom lvfa by (simp add: image_Un)
  have pt: "fold_nstate ?W (ground_pne fl) = ?W fl"
    if "fl \<in> (set fluents \<inter> dom N) \<union> set (lvalues ?ga)" for fl
    using fold_nstate_ground_pne that lv by auto
  have L': "numeric_effects_defined [?fa] (fold_nstate N)
       \<longleftrightarrow> (\<forall>fl \<in> (set fluents \<inter> dom N) \<union> set (lvalues ?ga). ?W fl \<noteq> None)"
    unfolding L un by (simp add: pt)
  show ?thesis
  proof
    assume "numeric_effects_defined [?fa] (fold_nstate N)"
    hence res: "\<forall>fl \<in> (set fluents \<inter> dom N) \<union> set (lvalues ?ga). ?W fl \<noteq> None"
      using L' by blast
    have "?W fl \<noteq> None" if "fl \<in> dom N \<union> set (lvalues ?ga)" for fl
    proof (cases "fl \<in> (set fluents \<inter> dom N) \<union> set (lvalues ?ga)")
      case True thus ?thesis using res by blast
    next
      case False
      hence fl: "fl \<in> dom N" and nfl: "fl \<notin> set (lvalues ?ga)" using that by auto
      have "?W fl = N fl" using action_numeric_update_function_only_changes_lvalues[OF nfl] .
      thus ?thesis using fl by auto
    qed
    thus "numeric_effects_defined [?ga] N" using R by blast
  next
    assume "numeric_effects_defined [?ga] N"
    thus "numeric_effects_defined [?fa] (fold_nstate N)" using R L' by blast
  qed
qed

lemma ground_goal_sem_num:
  assumes "fst M \<subseteq> set facts"
  shows "valuation M \<Turnstile>\<^sub>m goal P \<longleftrightarrow>
    valuation (ground_fmla ` fst M, fold_nstate (snd M)) \<Turnstile>\<^sub>m ground_fmla (goal P)"
  using ground_fmla_sem_num[OF goal_covered_num assms] .

subsubsection \<open> Enabledness and execution correspond under the renaming \<close>

theorem fold_enabled_iff_num:
  assumes "fst M \<subseteq> set facts"
      and "a \<in> set (actions (domain P))"
  shows "plan_action_enabled (ac_pa a) M \<longleftrightarrow>
    fpg.plan_action_enabled (ac_pa a) (ground_fmla ` fst M, fold_nstate (snd M))"
proof -
  let ?ga = "the (res_inst (ac_pa a))"
  let ?fa = "the (fpg.res_inst (ac_pa a))"
  let ?gM = "(ground_fmla ` fst M, fold_nstate (snd M))"
  have ri: "?fa = GroundAction (ga_pre ?ga) (ga_eff ?ga)" using resinst_fold_pa[OF assms(2)] .
  have wf: "wf_classical_plan_action (ac_pa a)"
    and fwf: "fpg.wf_classical_plan_action (ac_pa a)"
    using ac_pa_wf[OF assms(2)] fold_pa_wf[OF assms(2)] .
  have ni: "numeric_effects_non_intrf ?fa \<longleftrightarrow> numeric_effects_non_intrf ?ga"
    unfolding ri using fold_non_intrf_iff[OF assms(2)] .
  have rhs: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ?fa)) \<subseteq> dom (snd ?gM)
         \<longleftrightarrow> set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ?ga)) \<subseteq> dom (snd M)"
    unfolding ri ground_action.sel ground_rhs_pnes
    using ground_pne_dom_iff[OF acs_rhs_pnes[OF assms(2)]] by (simp add: set_map)
  have pre_cov: "covered_num (precondition ?ga) facts fluents"
    using pres_covered_num assms(2) by blast
  have pre: "valuation M \<Turnstile>\<^sub>m precondition ?ga \<longleftrightarrow> valuation ?gM \<Turnstile>\<^sub>m precondition ?fa"
    unfolding ri ground_action.sel ga_pre_alt
    using ground_fmla_sem_num[OF pre_cov assms(1)] by simp
  have ned: "numeric_effects_defined [?fa] (snd ?gM) \<longleftrightarrow> numeric_effects_defined [?ga] (snd M)"
    unfolding ri using fold_num_defined_iff[OF assms(2)] by simp
  show ?thesis
    unfolding plan_action_enabled_def fpg.plan_action_enabled_def Let_def
    using wf fwf ni rhs pre ned by (simp add: comp_def)
qed

lemma fold_exec_right_num:
  assumes "fst M \<subseteq> set facts"
      and "a \<in> set (actions (domain P))"
  shows "fpg.execute_plan_action (ac_pa a) (ground_fmla ` fst M, fold_nstate (snd M))
       = (ground_fmla ` fst (execute_plan_action (ac_pa a) M),
          fold_nstate (snd (execute_plan_action (ac_pa a) M)))"
proof -
  let ?ga = "the (res_inst (ac_pa a))"
  let ?dl = "set (dels (effect ?ga))"
  let ?ad = "set (adds (effect ?ga))"
  have ri: "the (fpg.res_inst (ac_pa a)) = GroundAction (ga_pre ?ga) (ga_eff ?ga)"
    using resinst_fold_pa[OF assms(2)] .
  have cov: "?ad \<union> ?dl \<subseteq> set facts" using effs_covered_alt[OF assms(2)] by simp
  have inj: "inj_on ground_fmla (fst M \<union> ?dl \<union> ?ad)"
    by (rule inj_on_subset[OF ground_fmla_inj]) (use assms(1) cov in auto)
  have d_eq: "ground_fmla ` (fst M - ?dl) = ground_fmla ` fst M - ground_fmla ` ?dl"
    by (rule inj_on_image_set_diff[OF inj]) auto
  have un_eq: "ground_fmla ` (fst M - ?dl \<union> ?ad)
    = ground_fmla ` fst M - ground_fmla ` ?dl \<union> ground_fmla ` ?ad"
    by (simp add: image_Un d_eq)
  have upd: "action_numeric_update_function (GroundAction (ga_pre ?ga) (ga_eff ?ga)) (fold_nstate (snd M))
           = fold_nstate (action_numeric_update_function ?ga (snd M))"
    using fold_action_update_num[OF assms(2)] .
  show ?thesis
    unfolding fpg.execute_plan_action_alt execute_plan_action_alt ri
    by (simp add: ga_eff_sel un_eq upd)
qed

subsubsection \<open> Plan-path correspondence under the renaming \<close>

lemma fold_path_right_num:
  assumes "fst M \<subseteq> set facts"
      and "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))"
      and "valid_classical_plan_alt M \<pi>s M'"
  shows "fpg.valid_classical_plan_alt (ground_fmla ` fst M, fold_nstate (snd M)) \<pi>s
           (ground_fmla ` fst M', fold_nstate (snd M'))"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons \<pi> \<pi>s)
  obtain a where
    a: "a \<in> set (actions (domain P))"
    and pi: "\<pi> = ac_pa a"
    using Cons.prems(2) by auto
  have rest: "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))" using Cons.prems(2) by auto
  have en: "plan_action_enabled \<pi> M"
    and val: "valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'"
    using Cons.prems(3) by auto
  have ex: "fpg.execute_plan_action \<pi> (ground_fmla ` fst M, fold_nstate (snd M))
    = (ground_fmla ` fst (execute_plan_action \<pi> M), fold_nstate (snd (execute_plan_action \<pi> M)))"
    using fold_exec_right_num[OF Cons.prems(1) a] pi by simp
  have cov': "fst (execute_plan_action \<pi> M) \<subseteq> set facts"
    using exec_covered[OF Cons.prems(1) a] pi by simp
  have "fpg.plan_action_enabled \<pi> (ground_fmla ` fst M, fold_nstate (snd M))"
    using fold_enabled_iff_num[OF Cons.prems(1) a] en pi by simp
  moreover
  have "fpg.valid_classical_plan_alt
      (ground_fmla ` fst (execute_plan_action \<pi> M), fold_nstate (snd (execute_plan_action \<pi> M)))
      \<pi>s (ground_fmla ` fst M', fold_nstate (snd M'))"
    using Cons.IH[OF cov' rest val] .
  ultimately
  show ?case using ex by simp
qed

lemma fold_path_left_num:
  assumes "fst M \<subseteq> set facts"
      and "fpg.valid_classical_plan_alt (ground_fmla ` fst M, fold_nstate (snd M)) \<pi>s gM'"
  shows "\<exists>M'. gM' = (ground_fmla ` fst M', fold_nstate (snd M')) \<and> valid_classical_plan_alt M \<pi>s M'"
  using assms proof (induction \<pi>s arbitrary: M)
  case Nil
  hence g: "gM' = (ground_fmla ` fst M, fold_nstate (snd M))" by simp
  show ?case by (rule exI[of _ M]) (simp add: g)
next
  case (Cons \<pi> \<pi>s)
  hence en: "fpg.plan_action_enabled \<pi> (ground_fmla ` fst M, fold_nstate (snd M))"
    and val: "fpg.valid_classical_plan_alt
      (fpg.execute_plan_action \<pi> (ground_fmla ` fst M, fold_nstate (snd M))) \<pi>s gM'"
    by auto
  have wf: "fpg.wf_classical_plan_action \<pi>" using en by (simp add: fpg.plan_action_enabled_def)
  obtain a where
    a: "a \<in> set (actions (domain P))"
    and pi: "\<pi> = ac_pa a"
    using fold_pa_inv[OF wf] by blast
  let ?N = "execute_plan_action \<pi> M"
  have ex: "fpg.execute_plan_action \<pi> (ground_fmla ` fst M, fold_nstate (snd M))
    = (ground_fmla ` fst ?N, fold_nstate (snd ?N))"
    using fold_exec_right_num[OF Cons.prems(1) a] pi by simp
  have covN: "fst ?N \<subseteq> set facts" using exec_covered[OF Cons.prems(1) a] pi by simp
  have enM: "plan_action_enabled \<pi> M"
    using fold_enabled_iff_num[OF Cons.prems(1) a] en pi by simp
  have "fpg.valid_classical_plan_alt (ground_fmla ` fst ?N, fold_nstate (snd ?N)) \<pi>s gM'"
    using val ex by simp
  then obtain M' where
    M1: "gM' = (ground_fmla ` fst M', fold_nstate (snd M'))"
    and M2: "valid_classical_plan_alt ?N \<pi>s M'"
    using Cons.IH[OF covN] by blast
  have "valid_classical_plan_alt M (\<pi> # \<pi>s) M'" using enM M2 by simp
  thus ?case by (intro exI[of _ M']) (simp add: M1)
qed

end

subsection \<open> Numeric fact folder: initial state and plan preservation \<close>

text \<open>The problem-level chain at \<^locale>\<open>wf_fact_folder_num\<close>: the folded initial state is the
  renamed initial state (predicate atoms fold through \<open>ground_fmla\<close>, function assignments through
  \<open>fold_nstate_map_of\<close>), and plan validity transfers in both directions --- the \<^emph>\<open>same\<close>
  nullary plan-action list is valid on both sides, exactly as in the propositional
  \<^locale>\<open>wf_fact_folder\<close> chain.\<close>

context wf_fact_folder_num begin

lemma i_covered_num: "fst I \<subseteq> set facts"
proof
  fix f assume "f \<in> fst I"
  hence f: "f \<in> set (init P)" and p: "is_predAtom f" by (simp_all add: I_def)
  show "f \<in> set facts"
    using init_shape[OF f] p by (auto simp: is_predAtom_decomp)
qed

lemma init_ground_predAtom:
  assumes "g \<in> set (init P)"
  shows "is_predAtom (ground_fmla g) \<longleftrightarrow> is_predAtom g"
  using init_shape[OF assms] by auto

lemma init_ground_numInit:
  assumes "g \<in> set (init P)"
  shows "is_numericInitializationAtom (ground_fmla g) \<longleftrightarrow> is_numericInitializationAtom g"
  using init_shape[OF assms] by auto

lemma fold_init_num: "fpg.I = (ground_fmla ` fst I, fold_nstate (snd I))"
proof -
  let ?conv = "\<lambda>x. case x of Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r)) \<Rightarrow> (l, real_of_rat r)"
  have fil_p: "filter is_predAtom (map ground_fmla (init P)) = map ground_fmla (filter is_predAtom (init P))"
    by (simp add: filter_map comp_def filter_cong[OF refl init_ground_predAtom])
  have fil_n: "filter is_numericInitializationAtom (map ground_fmla (init P))
             = map ground_fmla (filter is_numericInitializationAtom (init P))"
    by (simp add: filter_map comp_def filter_cong[OF refl init_ground_numInit])
  have fstI: "fst I = set (filter is_predAtom (init P))" by (simp add: I_def)
  have prop_part: "set (filter is_predAtom (init fold_prob)) = ground_fmla ` fst I"
    unfolding fold_prob_sel fil_p fstI by simp
  have conv_pt: "?conv (ground_fmla g) = (\<lambda>(l, v). (ground_pne l, v)) (?conv g)"
    if "g \<in> set (filter is_numericInitializationAtom (init P))" for g
  proof -
    have g: "g \<in> set (init P)" and n: "is_numericInitializationAtom g" using that by simp_all
    obtain l r where lr: "g = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
      using is_numericInitializationAtom.elims(2)[OF n] by metis
    show ?thesis unfolding lr by simp
  qed
  have keys: "fst ` set (map ?conv (filter is_numericInitializationAtom (init P))) \<subseteq> set fluents"
  proof
    fix x assume "x \<in> fst ` set (map ?conv (filter is_numericInitializationAtom (init P)))"
    then obtain g where
      g: "g \<in> set (init P)"
      and n: "is_numericInitializationAtom g"
      and x: "x = fst (?conv g)"
      by auto
    obtain l r where lr: "g = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
      using is_numericInitializationAtom.elims(2)[OF n] by metis
    have "l \<in> set fluents" using init_shape[OF g] unfolding lr by auto
    thus "x \<in> set fluents" using x unfolding lr by simp
  qed
  have num_part: "map_of (map ?conv (filter is_numericInitializationAtom (init fold_prob)))
                = fold_nstate (snd I)"
  proof -
    have "map ?conv (filter is_numericInitializationAtom (init fold_prob))
        = map (?conv \<circ> ground_fmla) (filter is_numericInitializationAtom (init P))"
      unfolding fold_prob_sel fil_n by simp
    also have "\<dots> = map ((\<lambda>(l, v). (ground_pne l, v)) \<circ> ?conv) (filter is_numericInitializationAtom (init P))"
      using conv_pt by (intro map_cong[OF refl]) simp
    finally have eq: "map ?conv (filter is_numericInitializationAtom (init fold_prob))
        = map (\<lambda>(l, v). (ground_pne l, v)) (map ?conv (filter is_numericInitializationAtom (init P)))"
      by simp
    show ?thesis
      unfolding eq fold_nstate_map_of[OF keys] by (simp add: I_def)
  qed
  show ?thesis
    unfolding fpg.I_def using prop_part num_part by simp
qed

theorem fold_valid_plan_right_num:
  assumes "valid_classical_plan2 \<pi>s"
  shows "fpg.valid_classical_plan2 \<pi>s"
proof -
  obtain M' where
    M1: "valid_classical_plan_alt I \<pi>s M'"
    and M2: "valuation M' \<Turnstile>\<^sub>m goal P"
    using assms valid_classical_plan2_alt by blast
  have acs: "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))" using path_actions_ac_pa[OF M1] .
  have cov: "fst M' \<subseteq> set facts" using alt_covered[OF i_covered_num acs M1] .
  have path: "fpg.valid_classical_plan_alt fpg.I \<pi>s (ground_fmla ` fst M', fold_nstate (snd M'))"
    unfolding fold_init_num using fold_path_right_num[OF i_covered_num acs M1] .
  have goal: "valuation (ground_fmla ` fst M', fold_nstate (snd M')) \<Turnstile>\<^sub>m goal fold_prob"
    using ground_goal_sem_num[OF cov] M2 by (simp add: fold_prob_sel)
  show ?thesis using path goal fpg.valid_classical_plan2_alt by blast
qed

theorem fold_valid_plan_left_num:
  assumes "fpg.valid_classical_plan2 \<pi>s"
  shows "valid_classical_plan2 \<pi>s"
proof -
  obtain gM' where
    g1: "fpg.valid_classical_plan_alt fpg.I \<pi>s gM'"
    and g2: "valuation gM' \<Turnstile>\<^sub>m goal fold_prob"
    using assms fpg.valid_classical_plan2_alt by blast
  obtain M' where
    M1: "gM' = (ground_fmla ` fst M', fold_nstate (snd M'))"
    and M2: "valid_classical_plan_alt I \<pi>s M'"
    using fold_path_left_num[OF i_covered_num g1[unfolded fold_init_num]] by blast
  have acs: "set \<pi>s \<subseteq> ac_pa ` set (actions (domain P))" using path_actions_ac_pa[OF M2] .
  have cov: "fst M' \<subseteq> set facts" using alt_covered[OF i_covered_num acs M2] .
  have goalM': "valuation M' \<Turnstile>\<^sub>m goal P"
    using ground_goal_sem_num[OF cov] g2 M1 by (simp add: fold_prob_sel)
  show ?thesis unfolding valid_classical_plan2_alt using M2 goalM' by blast
qed

theorem fold_valid_classical_plan_iff_num:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s. fpg.valid_classical_plan2 \<pi>s)"
  using fold_valid_plan_right_num fold_valid_plan_left_num by blast

end

subsection \<open> Code Setup \<close>

lemmas pddl_ground_code =
  fact_folder.fact_names_def
  fact_folder.fact_map_def
  ast_classical_problem.op_fluents_def
  grounder.fluents_def
  fact_folder.fluent_names_def
  fact_folder.fluent_map_def
  fact_folder.ground_pne_def
  fact_folder.ground_numexp.simps
  fact_folder.ground_neff_def
  fact_folder.ground_fmla.simps
  fact_folder.ga_pre.simps
  fact_folder.ga_eff.simps
  fact_folder.ac_pa_def
  fact_folder.fold_ac_def
  fact_folder.fold_dom_def
  fact_folder.fold_prob_def
  grounder.ground_ac_def
  varfree.op_names_def
  grounder.ground_dom_def
  grounder.ground_prob_def
  varfree.op_map_def
  varfree.restore_ground_pa.simps
declare pddl_ground_code[code]

end