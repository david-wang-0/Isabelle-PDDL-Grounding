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

context wf_fact_folder begin

subsubsection \<open> Semantics: folding preserves formula truth \<close>

lemma gr_predAtom: "is_predAtom a \<Longrightarrow> is_predAtom (ground_fmla a)"
  by (cases a rule: is_predAtom.cases) simp_all

lemma covered_predAtom: "is_predAtom a \<Longrightarrow> covered a facts \<longleftrightarrow> a \<in> set facts"
  unfolding covered_def by (cases a rule: is_predAtom.cases) (auto split: atom.splits)

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

subsubsection \<open> Resolving and instantiating the nullary plan actions in the folded problem \<close>

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

lemma fold_resolve:
  assumes "a \<in> set (actions (domain P))"
  shows "fdg.resolve_classical_action_schema (ac_name a) = Some (fold_ac a)"
proof -
  have mem: "fold_ac a \<in> set (actions fold_dom)" unfolding fold_dom_sel(5) using assms by simp
  have "fdg.resolve_classical_action_schema (ac_name (fold_ac a)) = Some (fold_ac a)"
    using fdg.resolve_classical_action_schema_name[OF mem] .
  thus ?thesis by (simp add: fold_ac_sel)
qed

lemma fpg_resolve_eq_fdg: "fpg.resolve_classical_action_schema = fdg.resolve_classical_action_schema"
  by (simp add: fpg.resolve_classical_action_schema_def fdg.resolve_classical_action_schema_def
      fold_prob_sel)

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

subsubsection \<open> Nullarity and well-formedness of the shared plan actions \<close>

lemma fold_names_eq: "ac_name ` set (actions fold_dom) = ac_name ` set (actions (domain P))"
proof -
  have "map ac_name (actions fold_dom) = map ac_name (actions (domain P))"
    unfolding fold_dom_sel(5) by (simp add: fold_ac_sel(1) comp_def)
  thus ?thesis by (metis list.set_map)
qed

lemma fold_pa_wf:
  assumes "a \<in> set (actions (domain P))"
  shows "fpg.wf_classical_plan_action (ac_pa a)"
proof -
  have "ac_name a \<in> ac_name ` set (actions fold_dom)" using fold_names_eq assms by blast
  thus ?thesis unfolding ac_pa_def using fpg.grounded_pa_nullary by (simp add: fold_prob_sel)
qed

text \<open>Both sides' well-formed plan actions are \<^emph>\<open>exactly\<close> the nullary \<^term>\<open>ac_pa a\<close> for the
  problem's own action schemas: on the \<open>P\<close> side because the input is variable-free, on the
  \<open>fold_prob\<close> side by \<open>grounded_pa_nullary\<close> and name preservation.\<close>

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

lemma fold_pa_inv:
  assumes "fpg.wf_classical_plan_action \<pi>"
  obtains a where "a \<in> set (actions (domain P))" "\<pi> = ac_pa a"
proof -
  obtain n args where pi0: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  hence n_in: "n \<in> ac_name ` set (actions fold_dom)"
    and args: "args = []"
    using assms fpg.grounded_pa_nullary by (simp_all add: fold_prob_sel)
  obtain a where
    a1: "a \<in> set (actions (domain P))"
    and a2: "ac_name a = n"
    using n_in fold_names_eq by auto
  have "\<pi> = ac_pa a" unfolding ac_pa_def using pi0 args a2 by simp
  thus thesis using that a1 by blast
qed

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
  using assms effs_covered_alt by (auto simp: exec_simp)

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