theory Classical_Grounded_PDDL
  imports Classical_Grounded_PDDL_Locales
begin

subsection \<open> Names and distinctness \<close>

text \<open>The folder's generated names: lengths, the positional characterisation
  (\<open>fact_names_nth\<close> / \<open>fluent_names_nth\<close> --- the reusable interface, preferred over re-unfolding
  the definitions downstream), pairwise distinctness, and nonemptiness. Distinctness is carried
  purely by the \<^const>\<open>idx_name\<close> index suffix (\<open>idx_name_inj_idx\<close>), so it holds in the bare
  \<^locale>\<open>fact_folder\<close> without any assumption --- in particular the readable encodings
  \<^const>\<open>readable_fact\<close> / \<^const>\<open>readable_fluent\<close> need not be injective. Nonemptiness likewise
  is structural (\<open>idx_name_nonempty\<close>).\<close>

context fact_folder begin

lemma facts_len: "length facts = length fact_names"
  unfolding fact_names_def by simp

lemma fluent_names_len: "length fluent_names = length fluents"
  unfolding fluent_names_def by simp

lemma fact_names_nth:
  assumes "k < length facts"
  shows "fact_names ! k = Pred (idx_name (readable_fact (facts ! k)) k)"
  using assms unfolding fact_names_def by simp

lemma fluent_names_nth:
  assumes "k < length fluents"
  shows "fluent_names ! k = Func (idx_name (readable_fluent (fluents ! k)) k)"
  using assms unfolding fluent_names_def by simp

lemma fact_names_dis: "distinct fact_names"
proof -
  have "fact_names ! i \<noteq> fact_names ! j"
    if ij: "i < length fact_names" "j < length fact_names" "i \<noteq> j" for i j
  proof
    assume eq: "fact_names ! i = fact_names ! j"
    have li: "i < length facts" and lj: "j < length facts" using ij facts_len by simp_all
    have "idx_name (readable_fact (facts ! i)) i = idx_name (readable_fact (facts ! j)) j"
      using eq fact_names_nth[OF li] fact_names_nth[OF lj] by simp
    hence "i = j" using idx_name_inj_idx by blast
    thus False using ij(3) by simp
  qed
  thus "distinct fact_names" by (simp add: distinct_conv_nth)
qed

lemma fluent_names_dis: "distinct fluent_names"
proof -
  have "fluent_names ! i \<noteq> fluent_names ! j"
    if ij: "i < length fluent_names" "j < length fluent_names" "i \<noteq> j" for i j
  proof
    assume eq: "fluent_names ! i = fluent_names ! j"
    have li: "i < length fluents" and lj: "j < length fluents"
      using ij fluent_names_len by simp_all
    have "idx_name (readable_fluent (fluents ! i)) i = idx_name (readable_fluent (fluents ! j)) j"
      using eq fluent_names_nth[OF li] fluent_names_nth[OF lj] by simp
    hence "i = j" using idx_name_inj_idx by blast
    thus False using ij(3) by simp
  qed
  thus "distinct fluent_names" by (simp add: distinct_conv_nth)
qed

lemma fact_names_nonempty:
  assumes "p \<in> set fact_names"
  shows "predicate.name p \<noteq> STR ''''"
proof -
  obtain k where
    k: "k < length facts"
    and p: "p = fact_names ! k"
    using assms facts_len in_set_conv_nth by metis
  show ?thesis unfolding p fact_names_nth[OF k] using idx_name_nonempty by simp
qed

lemma fluent_names_nonempty:
  assumes "f \<in> set fluent_names"
  shows "func.name f \<noteq> STR ''''"
proof -
  obtain k where
    k: "k < length fluents"
    and f: "f = fluent_names ! k"
    using assms fluent_names_len in_set_conv_nth by metis
  show ?thesis unfolding f fluent_names_nth[OF k] using idx_name_nonempty by simp
qed

end

context grounder begin

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


subsection \<open> Grounder facts consumed by the factorization \<close>

text \<open>The one-shot grounder's well-formedness chain (domain/problem wf) is no longer proved
  directly here: it derives from the Variable_Freeness stage composed with the fact folder ---
  see \<open>Classical_Grounded_PDDL_Factorization\<close>. Only the \<^locale>\<open>wf_grounder_cov\<close> facts that
  the factorization and the pipeline still consume remain: action-name distinctness, resolution
  well-formedness, and the op-fluent collection.\<close>

context wf_grounder_cov begin

lemma ground_ac_names: "map ac_name (map2 ground_ac ops op_names) = op_names"
proof -
  have "map ac_name (map2 ground_ac xs ys) = ys" if "length xs = length ys" for xs ys
    using that by (induction xs ys rule: list_induct2) (simp_all add: ground_ac_sel)
  thus ?thesis using ops_len by simp
qed

lemma gr_acs_dis: "distinct (map ac_name (actions D\<^sub>G))"
  using ground_ac_names op_names_dis by (simp add: ground_dom_sel)

lemma wf_ops_resinst:
  "\<forall>\<pi> \<in> set ops. wf_ground_action (the (res_inst \<pi>))"
  "\<forall>\<pi> \<in> set ops. wf_fmla objT (precondition (the (res_inst \<pi>)))"
  "\<forall>\<pi> \<in> set ops. wf_effect objT (effect (the (res_inst \<pi>)))"
  using ops_wf wf_resolve_instantiate wf_ground_action_alt by simp_all

lemma op_fluents_subset:
  assumes "\<pi> \<in> set ops"
  shows "set (op_fluents \<pi>) \<subseteq> set fluents"
  using assms unfolding fluents_def by auto

end

subsection \<open> Propositional grounder: no ground fluents \<close>

text \<open>The one-shot grounder's problem well-formedness is no longer proved here: it derives from
  the Variable_Freeness stage composed with the fact folder --- see
  \<open>Classical_Grounded_PDDL_Factorization\<close>. What remains is the \<^locale>\<open>wf_grounder\<close>-specific
  observation that under the no-fluents assumptions the grounded function table is empty.\<close>

context wf_grounder begin

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
  using fluents_empty unfolding fluent_names_def by simp

lemma ground_dom_funcs: "functions D\<^sub>G = []"
  unfolding ground_dom_def by (simp add: fluent_names_empty)

end

subsection \<open> The standalone fact folder: selectors and groundedness \<close>

text \<open>The remaining development mirrors the one-shot grounder's proofs above for the standalone
  \<^locale>\<open>fact_folder\<close> stage: the same folding machinery, but quantified over the variable-free
  problem's own action schemas --- each folded via its nullary plan action
  \<^const>\<open>fact_folder.ac_pa\<close> --- instead of a reachable-op list.\<close>

context fact_folder begin

lemma fold_ac_sel [simp]:
  "ac_name (fold_ac a) = ac_name a"
  "ac_params (fold_ac a) = []"
  "ac_pre (fold_ac a) = ga_pre (the (res_inst (ac_pa a)))"
  "ac_eff (fold_ac a) = ga_eff (the (res_inst (ac_pa a)))"
  unfolding fold_ac_def Let_def by simp_all

lemma fold_dom_sel:
  "types fold_dom = []"
  "predicates fold_dom = map (\<lambda>p. PredDecl p []) fact_names"
  "functions fold_dom = map (\<lambda>f. FuncDecl f []) fluent_names"
  "consts fold_dom = []"
  "actions fold_dom = map fold_ac (actions (domain P))"
  unfolding fold_dom_def by simp_all

lemma fold_prob_sel [simp]:
  "ast_problem.domain fold_prob = fold_dom"
  "objects fold_prob = []"
  "init fold_prob = map ground_fmla (init P)"
  "goal fold_prob = ground_fmla (goal P)"
  unfolding fold_prob_def by simp_all

text \<open>Restatements of the grounder's generic \<open>ga_pre\<close>/\<open>ga_eff\<close> selectors in
  \<^locale>\<open>fact_folder\<close>, so the standalone folder development below can use them (their
  originals above live in \<^locale>\<open>grounder\<close>, which the folder layers do not import).\<close>

lemma ga_pre_alt: "ga_pre ga = ground_fmla (precondition ga)"
  by (cases ga; simp)

lemma ga_eff_alt: "ga_eff ga =
  Effect (map ground_fmla (adds (effect ga))) (map ground_fmla (dels (effect ga)))
         (map ground_neff (numeric_effects (effect ga)))"
  by (cases ga rule: ga_eff.cases) simp

lemma ga_eff_sel [simp]:
  "adds (ga_eff ga) = map ground_fmla (adds (effect ga))"
  "dels (ga_eff ga) = map ground_fmla (dels (effect ga))"
  "numeric_effects (ga_eff ga) = map ground_neff (numeric_effects (effect ga))"
  unfolding ga_eff_alt by simp_all

subsubsection \<open> The folded output is grounded \<close>

lemma fold_acs_grounded: "(\<forall>x \<in> set (actions fold_dom). grounded_ac x)"
proof
  fix x assume "x \<in> set (actions fold_dom)"
  then obtain a where "x = fold_ac a" unfolding fold_dom_sel(5) by auto
  hence "ac_params x = []" using fold_ac_sel by simp
  thus "grounded_ac x" by (cases x rule: grounded_ac.cases) simp_all
qed

theorem fold_dom_grounded: "fdg.grounded_dom"
proof (intro fdg.grounded_domI)
  show "types fold_dom = []" by (simp add: fold_dom_sel)
  show "\<forall>p \<in> set (predicates fold_dom). grounded_pred p" by (auto simp: fold_dom_sel)
  show "consts fold_dom = []" by (simp add: fold_dom_sel)
  show "\<forall>f \<in> set (functions fold_dom). grounded_func f" by (simp add: fold_dom_def)
  show "\<forall>a \<in> set (actions fold_dom). grounded_ac a" using fold_acs_grounded .
qed

theorem fold_prob_grounded: "fpg.grounded_prob"
  using fold_dom_grounded by (intro fpg.grounded_probI) (simp_all add: fold_prob_sel)

end

subsection \<open> Covered fact folder: resolution and domain well-formedness \<close>

text \<open>The \<^locale>\<open>wf_fact_folder_cov\<close> development mirrors \<^locale>\<open>wf_grounder_cov\<close> above;
  where the grounder quantified over \<open>\<pi> \<in> set ops\<close> (with \<open>ops_wf\<close>), the folder quantifies
  over \<open>a \<in> set (actions (domain P))\<close> and resolves the nullary plan action \<open>ac_pa a\<close> back to
  \<open>a\<close> itself (the input is variable-free, so instantiation at \<open>[]\<close> is total).\<close>

context wf_fact_folder_cov begin

subsubsection \<open> Resolving and instantiating the nullary plan actions \<close>

lemma resolve_ac:
  assumes "a \<in> set (actions (domain P))"
  shows "resolve_classical_action_schema (ac_name a) = Some a"
proof -
  have dis: "distinct (map ac_name (actions (domain P)))"
    using wf_classical_domainD(2)[OF wf_classical_problemD(1)[OF wf_problem]] .
  show ?thesis
    unfolding resolve_classical_action_schema_def
    using index_by_eq_Some_eq[OF dis] assms by blast
qed

lemma res_inst_ac:
  assumes "a \<in> set (actions (domain P))"
  shows "res_inst (ac_pa a) = Some (instantiate_classical_action_schema a [])"
  unfolding res_inst_alt using resolve_ac[OF assms] by (simp add: ac_pa_def)

lemma ac_pa_wf:
  assumes "a \<in> set (actions (domain P))"
  shows "wf_classical_plan_action (ac_pa a)"
proof -
  have par: "ac_params a = []" using varfree_probD(1)[OF varfree_input] assms by blast
  have pm: "action_params_match (ac_head a) []"
    unfolding action_params_match_def using par by (cases a) simp
  show ?thesis
    unfolding ac_pa_def wf_classical_plan_action_simple
    using resolve_ac[OF assms] pm by simp
qed

lemma wf_acs_resinst:
  "\<forall>a \<in> set (actions (domain P)). wf_ground_action (the (res_inst (ac_pa a)))"
  "\<forall>a \<in> set (actions (domain P)). wf_fmla objT (precondition (the (res_inst (ac_pa a))))"
  "\<forall>a \<in> set (actions (domain P)). wf_effect objT (effect (the (res_inst (ac_pa a))))"
  using ac_pa_wf wf_resolve_instantiate wf_ground_action_alt by simp_all

subsubsection \<open> Fluent names, map, and nullary function signature \<close>

lemma fluent_map_dom:
  assumes "fl \<in> set fluents"
  shows "\<exists>f. fluent_map fl = Some f \<and> f \<in> set fluent_names"
  unfolding fluent_map_def using lookup_zip fluent_names_len assms by metis

lemma gr_funcs_dis: "distinct (map function_decl.func (functions fold_dom))"
proof -
  have "map function_decl.func (functions fold_dom) = fluent_names"
    unfolding fold_dom_def by (simp add: comp_def)
  thus ?thesis using fluent_names_dis by metis
qed

lemma gr_sig_fun:
  assumes "f \<in> set fluent_names"
  shows "fdg.func_sig f = Some []"
proof -
  have "FuncDecl f [] \<in> set (functions fold_dom)"
    using assms unfolding fold_dom_def by force
  thus ?thesis using fdg.func_resolve gr_funcs_dis by metis
qed

subsubsection \<open> Predicate and action well-formedness \<close>

lemma gr_preds_dis: "distinct (map pred (predicates fold_dom))"
proof -
  have "map pred (predicates fold_dom) = fact_names"
    unfolding fold_dom_sel(2) by (simp add: comp_def)
  thus ?thesis using fact_names_dis by metis
qed

lemma gr_preds_wf: "(\<forall>x \<in> set (predicates fold_dom). fdg.wf_predicate_decl x)"
  unfolding fold_dom_sel(2) by (simp add: domain_signature.wf_predicate_decl.simps)

lemma gr_sig_fact:
  assumes "p \<in> set fact_names"
  shows "fdg.sig p = Some []"
proof -
  have "PredDecl p [] \<in> set (predicates fold_dom)"
    using assms unfolding fold_dom_sel(2) by force
  thus ?thesis using fdg.pred_resolve gr_preds_dis by metis
qed

lemma gr_acs_dis: "distinct (map ac_name (actions fold_dom))"
proof -
  have "map ac_name (actions fold_dom) = map ac_name (actions (domain P))"
    unfolding fold_dom_sel(5) by (simp add: fold_ac_sel(1) comp_def)
  thus ?thesis
    using wf_classical_domainD(2)[OF wf_classical_problemD(1)[OF wf_problem]] by simp
qed

subsubsection \<open> Grounding a covered atom / formula yields a well-formed one \<close>

lemma gr_atom_wf:
  assumes "a \<in> set facts"
  shows "fdg.wf_fmla_atom tyt (ground_fmla a)"
proof -
  obtain p where
    p: "fact_map a = Some p"
    and pmem: "p \<in> set fact_names"
    unfolding fact_map_def using lookup_zip facts_len assms by metis
  hence 1: "ground_fmla a = Atom (predAtm p [])"
    using facts_wf assms by (cases a rule: is_predAtom.cases) auto
  have "fdg.wf_fmla_atom tyt (Atom (predAtm p []))"
    using gr_sig_fact[OF pmem] by (simp add: fdg.wf_fmla_atom_alt)
  thus ?thesis using 1 by metis
qed

lemma gr_fmla_atom_wf:
  assumes "covered \<phi> facts" "is_predAtom \<phi>"
  shows "fdg.wf_fmla_atom tyt (ground_fmla \<phi>)"
proof -
  obtain p xs where "\<phi> = Atom (predAtm p xs)" using assms(2) is_predAtom_decomp by blast
  hence "\<phi> \<in> set facts" using covered_predAtm_mem[OF assms(1)] by simp
  thus ?thesis using gr_atom_wf by blast
qed

lemma ground_fmla_wf:
  assumes "covered \<phi> facts"
  shows "fdg.wf_fmla tyt (ground_fmla \<phi>)"
  using assms apply (induction \<phi> rule: ground_fmla.induct)
                      apply (simp_all add: covered_def)
  subgoal for v va
    using gr_atom_wf[of "Atom (predAtm v va)"]
    by (simp add: fdg.wf_fmla_atom_alt)
  done

lemma ground_fmla_inj: "inj_on ground_fmla (set facts)"
proof -
  {
    fix a b
    assume assms: "a \<in> set facts" "b \<in> set facts" "a \<noteq> b"
    then obtain n args where a: "a = Atom (predAtm n args)"
      using facts_wf wf_fmla_atom_alt by (cases a rule: is_predAtom.cases) auto
    obtain n' args' where b: "b = Atom (predAtm n' args')"
      using assms facts_wf wf_fmla_atom_alt by (cases b rule: is_predAtom.cases) auto
    note mapof_distinct_zip_neq[OF facts_len fact_names_dis assms]
    hence "ground_fmla a \<noteq> ground_fmla b"
      using a b fact_map_def by auto
  }
  thus ?thesis unfolding inj_on_def by fast
qed

subsubsection \<open> Effect literal well-formedness \<close>

abbreviation "eff_lits eff \<equiv> set (adds eff) \<union> set (dels eff)"

lemma eff_lit_covered:
  assumes "a \<in> set (actions (domain P))"
      and "\<phi> \<in> eff_lits (effect (the (res_inst (ac_pa a))))"
  shows "covered \<phi> facts"
  using assms effs_covered unfolding Let_def by auto

lemma eff_lit_predAtom:
  assumes "a \<in> set (actions (domain P))"
      and "\<phi> \<in> eff_lits (effect (the (res_inst (ac_pa a))))"
  shows "is_predAtom \<phi>"
proof -
  have "wf_effect objT (effect (the (res_inst (ac_pa a))))"
    using assms(1) wf_acs_resinst(3) by blast
  hence "wf_fmla_atom objT \<phi>" using assms(2) unfolding wf_effect_alt list_all_iff by blast
  thus ?thesis using wf_fmla_atom_pred by blast
qed

lemma ground_eff_lit_wf:
  assumes "a \<in> set (actions (domain P))"
      and "\<phi> \<in> eff_lits (effect (the (res_inst (ac_pa a))))"
  shows "fdg.wf_fmla_atom tyt (ground_fmla \<phi>)"
  using eff_lit_covered[OF assms] eff_lit_predAtom[OF assms] gr_fmla_atom_wf by blast

subsubsection \<open> Grounding a fluent / numeric expression / numeric effect is well-formed \<close>

lemma ground_pne_wf:
  assumes "fl \<in> set fluents"
  shows "fdg.wf_primitive_numeric_expression tyt (ground_pne fl)"
proof -
  obtain f where f: "fluent_map fl = Some f" "f \<in> set fluent_names"
    using fluent_map_dom[OF assms] by blast
  hence "fdg.func_sig f = Some []" using gr_sig_fun by blast
  thus ?thesis using f(1) by (simp add: ground_pne_def)
qed

lemma ground_numexp_wf:
  assumes "set (enumerate_primitive_numeric_expressions e) \<subseteq> set fluents"
  shows "fdg.wf_numeric_expression tyt (ground_numexp e)"
  using assms by (induction e) (auto simp: ground_pne_wf)

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

lemma ground_neff_wf:
  assumes "a \<in> set (actions (domain P))"
      and "ne \<in> set (numeric_effects (effect (the (res_inst (ac_pa a)))))"
  shows "fdg.wf_numeric_effect tyt (ground_neff ne)"
proof -
  obtain opr l r where ne: "ne = NumericEffect opr l r" by (cases ne)
  have "l \<in> set fluents"
    using neff_lhs_in_op_fluents acs_fluents assms ne by blast
  hence lhs: "fdg.wf_primitive_numeric_expression tyt (ground_pne l)"
    using ground_pne_wf by blast
  have "set (enumerate_primitive_numeric_expressions r) \<subseteq> set fluents"
    using neff_rhs_pnes_in_op_fluents acs_fluents assms ne by blast
  hence "fdg.wf_numeric_expression tyt (ground_numexp r)"
    using ground_numexp_wf by blast
  thus ?thesis using lhs ne by (simp add: ground_neff_def)
qed

subsubsection \<open> Folded action-schema and domain well-formedness \<close>

lemma ground_eff_wf_cov:
  assumes "a \<in> set (actions (domain P))"
  shows "fdg.wf_effect tyt (ga_eff (the (res_inst (ac_pa a))))"
proof -
  let ?eff = "effect (the (res_inst (ac_pa a)))"
  have adds: "\<forall>\<phi> \<in> set (adds ?eff). fdg.wf_fmla_atom tyt (ground_fmla \<phi>)"
    using ground_eff_lit_wf[OF assms] by auto
  have dels: "\<forall>\<phi> \<in> set (dels ?eff). fdg.wf_fmla_atom tyt (ground_fmla \<phi>)"
    using ground_eff_lit_wf[OF assms] by auto
  have nums: "\<forall>ne \<in> set (numeric_effects ?eff). fdg.wf_numeric_effect tyt (ground_neff ne)"
    using ground_neff_wf[OF assms] by blast
  show ?thesis
    unfolding fdg.wf_effect_alt ga_eff_sel list_all_iff
    using adds dels nums by auto
qed

lemma wf_effect_ground:
  assumes "\<forall>\<phi> \<in> set (adds (effect ga)). fdg.wf_fmla_atom tyt (ground_fmla \<phi>)"
      and "\<forall>\<phi> \<in> set (dels (effect ga)). fdg.wf_fmla_atom tyt (ground_fmla \<phi>)"
      and "numeric_effects (effect ga) = []"
  shows "fdg.wf_effect tyt (ga_eff ga)"
  unfolding fdg.wf_effect_alt ga_eff_sel list_all_iff using assms by auto

lemma fold_ac_wf:
  assumes "a \<in> set (actions (domain P))"
  shows "fdg.wf_classical_action_schema (fold_ac a)"
proof (intro fdg.wf_classical_action_schemaI)
  show "distinct (map fst (ac_params (fold_ac a)))" by (simp add: fold_ac_sel)
  have "covered (precondition (the (res_inst (ac_pa a)))) facts" using assms pres_covered by blast
  thus "fdg.wf_fmla (fdg.ac_tyt (fold_ac a)) (ac_pre (fold_ac a))"
    using ground_fmla_wf by (simp add: fold_ac_sel ga_pre_alt)
  show "fdg.wf_effect (fdg.ac_tyt (fold_ac a)) (ac_eff (fold_ac a))"
    using ground_eff_wf_cov[OF assms] by (simp add: fold_ac_sel)
qed

lemma gr_acs_wf: "(\<forall>x \<in> set (actions fold_dom). fdg.wf_classical_action_schema x)"
proof (rule ballI)
  fix ac assume "ac \<in> set (actions fold_dom)"
  then obtain a where
    ac: "ac = fold_ac a"
    and amem: "a \<in> set (actions (domain P))"
    unfolding fold_dom_sel(5) by auto
  show "fdg.wf_classical_action_schema ac" using fold_ac_wf[OF amem] ac by simp
qed

theorem fold_dom_wf: "fdg.wf_classical_domain"
proof (intro fdg.wf_classical_domainI)
  show "fdg.wf_domain_signature"
    unfolding fdg.wf_domain_signature_def
    using gr_preds_dis gr_preds_wf gr_funcs_dis
    by (simp add: fold_dom_sel fold_dom_def domain_signature.wf_types_def comp_def
                  domain_signature.wf_predicate_decl.simps domain_signature.wf_function_decl.simps)
  show "distinct (map ac_name (actions fold_dom))" using gr_acs_dis .
  show "\<forall>a \<in> set (actions fold_dom). fdg.wf_classical_action_schema a" using gr_acs_wf .
qed

end

sublocale wf_fact_folder_cov \<subseteq> fdg: wf_ast_classical_domain fold_dom
  using fold_dom_wf by unfold_locales

subsection \<open> Propositional fact folder: problem well-formedness \<close>

context wf_fact_folder begin

lemma fold_eff_wf:
  assumes "a \<in> set (actions (domain P))"
  shows "fdg.wf_effect tyt (ga_eff (the (res_inst (ac_pa a))))"
proof (rule wf_effect_ground)
  let ?eff = "effect (the (res_inst (ac_pa a)))"
  show "\<forall>\<phi> \<in> set (adds ?eff). fdg.wf_fmla_atom tyt (ground_fmla \<phi>)"
    using ground_eff_lit_wf[OF assms] by blast
  show "\<forall>\<phi> \<in> set (dels ?eff). fdg.wf_fmla_atom tyt (ground_fmla \<phi>)"
    using ground_eff_lit_wf[OF assms] by blast
  show "numeric_effects ?eff = []" using acs_no_num assms by blast
qed

lemma init_in_facts: "set (init P) \<subseteq> set facts"
proof
  fix f assume f: "f \<in> set (init P)"
  then obtain p xs where "f = Atom (predAtm p xs)"
    using init_props is_predAtom_decomp by blast
  hence "achievable (p, xs)" using f init_achievable by simp
  thus "f \<in> set facts" using all_facts \<open>f = Atom (predAtm p xs)\<close> by (auto simp: uncurry_def)
qed

lemma fold_init_dis: "distinct (init fold_prob)"
proof -
  have "distinct (init P)" using wf_problem unfolding wf_classical_problem_def by simp
  moreover
  have "inj_on ground_fmla (set (init P))"
    using ground_fmla_inj init_in_facts inj_on_subset by blast
  ultimately
  show ?thesis unfolding fold_prob_sel using distinct_map by blast
qed

lemma fold_init_wf: "\<forall>f \<in> set (init fold_prob). fpg.wf_fmla_atom fpg.objT f \<or> fpg.wf_func_assign f"
proof
  fix f assume "f \<in> set (init fold_prob)"
  then obtain g where g: "g \<in> set (init P)" "f = ground_fmla g"
    unfolding fold_prob_sel by auto
  hence "g \<in> set facts" using init_in_facts by blast
  hence "fpg.wf_fmla_atom fpg.objT f" using gr_atom_wf g by (simp add: fold_prob_sel)
  thus "fpg.wf_fmla_atom fpg.objT f \<or> fpg.wf_func_assign f" by blast
qed

lemma fold_goal_wf: "fpg.wf_fmla fpg.objT (goal fold_prob)"
  unfolding fold_prob_sel using goal_covered ground_fmla_wf by blast

lemma fpg_wf_dom_sig: "fpg.wf_domain_signature"
  using fold_dom_wf unfolding fdg.wf_classical_domain_def by (simp add: fold_prob_sel)

theorem fold_prob_wf: "fpg.wf_classical_problem"
proof (intro fpg.wf_classical_problemI)
  show "fpg.wf_classical_domain" using fold_dom_wf by (simp add: fold_prob_sel)
  show "fpg.wf_problem_signature"
    unfolding fpg.wf_problem_signature_def
    using fpg_wf_dom_sig by (simp add: fold_prob_sel fold_dom_sel)
  show "distinct (init fold_prob)" using fold_init_dis .
  show "\<forall>f \<in> set (init fold_prob). fpg.wf_fmla_atom fpg.objT f \<or> fpg.wf_func_assign f"
    using fold_init_wf .
  show "fpg.wf_fmla fpg.objT (goal fold_prob)" using fold_goal_wf .
qed

end

sublocale wf_fact_folder \<subseteq> fpg: grounded_problem fold_prob
  using fold_prob_wf fold_prob_grounded by unfold_locales

end
