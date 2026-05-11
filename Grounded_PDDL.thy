theory Grounded_PDDL
imports "Classical_Planning.Classical_Abstract_Syntax"
    PDDL_Sema_Supplement Normalization_Definitions
    Grounding_Utils String_Utils
begin

type_synonym facty = "object atom formula" (* maybe fact_atom? *)

(* TODO split into wf_dom_grounder, dom_grounder, prob_grounder? *)

(* parameters for grounding: lists of achievable facts and applicable plan actions *)

fun arg_str :: "object list \<Rightarrow> string" where
  "arg_str [] = ''''" |
  "arg_str [Obj n] = n" |
  "arg_str (Obj n # objs) = n @ ((CHR ''-'') # arg_str objs)"

fun fact_str :: "object atom \<Rightarrow> string" where
  "fact_str (predAtm (Pred n) args) = n @ ((CHR ''-'' # arg_str args))" |
  "fact_str _ = undefined"

fun ac_str :: "plan_action \<Rightarrow> string" where
  "ac_str (PAction n args) = n @ (CHR ''-'' # arg_str args)"

locale grounder = ast_problem +
  fixes facts :: "facty list" and ops :: "plan_action list"
begin

definition "fact_ids \<equiv> nat_range (length facts)"
definition "fact_prefix_pad \<equiv> length (show (length facts))" (* length facts - 1 is enough *)
definition "op_ids \<equiv> nat_range (length ops)"
definition "op_prefix_pad \<equiv> length (show (length ops))" (* length ops - 1 is enough *)

fun ground_pred :: "facty \<Rightarrow> nat \<Rightarrow> predicate" where
  "ground_pred (Atom a) i = Pred (padl fact_prefix_pad (show i) @ (CHR ''/'' # fact_str a))" |
  "ground_pred _ _ = undefined"

abbreviation "fact_names \<equiv> map2 ground_pred facts fact_ids"
definition "fact_map \<equiv> map_of (zip facts fact_names)"

(* As this signature reveals, this function has to be handled with care,
  since a new type parameter appears from nowhere.
  In code, 'a is always object. In proofs, however, it is sometimes term, too. *)
fun ground_fmla :: "object atom formula \<Rightarrow> 'a atom formula" where
  (* literals *)
  "ground_fmla \<bottom> = \<bottom>" |
  "ground_fmla (Atom (Eq a b)) = (if a = b then \<^bold>\<not>\<bottom> else \<bottom>)" |
  "ground_fmla (\<^bold>\<not> (Atom (Eq a b))) = (if a = b then \<bottom> else \<^bold>\<not>\<bottom>)" |
  "ground_fmla (Atom patm) = Atom (predAtm (the (fact_map (Atom patm))) [])" |
  "ground_fmla (\<^bold>\<not> \<phi>) = \<^bold>\<not> (ground_fmla \<phi>)" | (* this one also coveres non-literal cases *)
  (* conjunction *)
  "ground_fmla (\<phi> \<^bold>\<and> \<psi>) = ground_fmla \<phi> \<^bold>\<and> ground_fmla \<psi>" |
  (* covering formulas that don't satisfy \<open>is_conj\<close> *)
  "ground_fmla (\<phi> \<^bold>\<or> \<psi>) = ground_fmla \<phi> \<^bold>\<or> ground_fmla \<psi>" |
  "ground_fmla (\<phi> \<^bold>\<rightarrow> \<psi>) = ground_fmla \<phi> \<^bold>\<rightarrow> ground_fmla \<psi>"

(* in code, 'a=term. In proofs, 'a can be object, too *)
fun ga_pre :: "ground_action \<Rightarrow> 'a atom formula" where
  "ga_pre (Ground_Action pre eff) = ground_fmla pre"

(* in code, 'a=term. In proofs, 'a can be object, too *)
fun ga_eff :: "ground_action \<Rightarrow> 'a ast_effect" where
  "ga_eff (Ground_Action pre (Effect a d)) =
    Effect (map ground_fmla a) (map ground_fmla d)"

fun ground_ac_name :: "plan_action \<Rightarrow> nat \<Rightarrow> string" where
  "ground_ac_name (PAction n args) i =
    padl op_prefix_pad (show i) @ (CHR ''/'' # n) @ ((CHR ''-'' # arg_str args))"

definition "op_names \<equiv> map2 ground_ac_name ops op_ids"

definition ground_ac :: "plan_action \<Rightarrow> string \<Rightarrow> ast_action_schema" where
  "ground_ac \<pi> n =
    (let ga = resolve_instantiate \<pi> in
    Action_Schema n [] (ga_pre ga) (ga_eff ga))"

definition ground_dom :: "ast_domain" where
  "ground_dom \<equiv> Domain
    []
    (map (\<lambda>p. PredDecl p []) fact_names)
    []
    (map2 ground_ac ops op_names)"

definition ground_prob :: "ast_problem" where
  "ground_prob \<equiv> Problem
    ground_dom
    []
    (map ground_fmla (init P))
    (ground_fmla (goal P))"


definition "op_map \<equiv> map_of (zip op_names ops)"

fun restore_ground_pa :: "plan_action \<Rightarrow> plan_action" where
  "restore_ground_pa (PAction n args) = the (op_map n)"

abbreviation restore_ground_plan :: "plan_action list \<Rightarrow> plan_action list" where
  "restore_ground_plan \<pi>s \<equiv> map restore_ground_pa \<pi>s"

end

definition "covered \<phi> facts \<equiv> \<forall>a \<in> atoms \<phi>. is_predAtm a \<longrightarrow> Atom a \<in> set facts"

text \<open>Some of these may follow from one another\<close>

locale wf_grounder = grounder +
  assumes
    wf_problem and
    facts_dist: "distinct facts" and
    all_facts: "set facts \<supseteq> {a. achievable a}" and
    facts_wf: "list_all1 (wf_fmla_atom objT) facts" and (* If "set facts = {a. achievable a}", this follows. *)
    ops_dist: "distinct ops" and
    all_ops: "set ops \<supseteq> {\<pi>. applicable \<pi>}" and
    (* If "set ops = {\<pi>. applicable \<pi>}", this follows: *)
    ops_wf: "list_all1 wf_plan_action ops" and
    (* So does this: *)
    effs_covered: "\<forall>\<pi> \<in> set ops. (let eff = effect (resolve_instantiate \<pi>) in
      \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> facts)" and
    (* This follows if, additionally, prec_normed_dom: *)
    pres_covered: "\<forall>\<pi> \<in> set ops. covered (precondition (resolve_instantiate \<pi>)) facts" and
    goal_covered: "covered (goal P) facts"

text \<open>
The last two conditions can be satisfied by instantiating every \<pi>\<in>ops and adding all missing atoms
to \<open>facts\<close>. I don't need to implement this for my grounder, but you are welcome to.
\<close>

abbreviation (in grounder) "D\<^sub>G \<equiv> ground_dom"
abbreviation (in grounder) "P\<^sub>G \<equiv> ground_prob"

sublocale wf_grounder \<subseteq> wf_ast_problem P
  apply (unfold_locales)
  using wf_grounder_axioms wf_grounder_def by blast

sublocale grounder \<subseteq> dg: ast_domain D\<^sub>G .
sublocale grounder \<subseteq> pg: ast_problem P\<^sub>G .

subsection \<open> Alternative definitions \<close>

context grounder begin

lemma ground_pred_cond:
  "is_predAtom a \<Longrightarrow>
  (\<exists>s. ground_pred a i = Pred (padl fact_prefix_pad (show i) @ s))"
  by (cases a rule: is_predAtom.cases) simp_all

lemma ga_pre_alt: "ga_pre ga = ground_fmla (precondition ga)"
  by (cases ga; simp)

lemma ga_eff_alt: "ga_eff ga =
  Effect (map ground_fmla (adds (effect ga))) (map ground_fmla (dels (effect ga)))"
  by (cases ga rule: ga_eff.cases) simp

lemma ga_eff_sel [simp]:
  "adds (ga_eff ga) = map ground_fmla (adds (effect ga))"
  "dels (ga_eff ga) = map ground_fmla (dels (effect ga))"
  unfolding ga_eff_alt by simp_all

lemma ground_ac_name_alt:
  "ground_ac_name \<pi> i =
    padl op_prefix_pad (show i)
      @ (CHR ''/'' # (name \<pi>))
      @ ((CHR ''-'' # arg_str (arguments \<pi>)))"
  by (cases \<pi>) simp

lemma ground_ac_sel [simp]:
  "ac_name (ground_ac \<pi> n) = n"
  "ac_params (ground_ac \<pi> n) = []"
  "ac_pre (ground_ac \<pi> n) = ga_pre (resolve_instantiate \<pi>)"
  "ac_eff (ground_ac \<pi> n) = ga_eff (resolve_instantiate \<pi>)"
  unfolding ground_ac_def Let_def by simp_all

lemma ground_dom_sel [simp]:
  "types D\<^sub>G = []"
  "predicates D\<^sub>G = map (\<lambda>p. PredDecl p []) fact_names"
  "consts D\<^sub>G = []"
  "actions D\<^sub>G = map2 ground_ac ops op_names"
  unfolding ground_dom_def by simp_all

lemma ground_prob_sel [simp]:
  "domain P\<^sub>G \<equiv> D\<^sub>G"
  "objects P\<^sub>G = []"
  "init P\<^sub>G = map ground_fmla (init P)"
  "goal P\<^sub>G = ground_fmla (goal P)"
  unfolding ground_prob_def by simp_all

lemma restore_ground_pa_alt: "restore_ground_pa \<pi> = the (op_map (name \<pi>))"
  by (cases \<pi>) simp

end

subsection \<open> Output format \<close>
text \<open> The output is, in fact, grounded \<close>

context grounder begin

lemma acs_grounded: "list_all1 grounded_ac (actions D\<^sub>G)"
proof
  fix x assume a: "x \<in> set (actions D\<^sub>G)"
  then obtain op i where "x = ground_ac op i" by auto
  hence "ac_params x = []" by simp
  thus "grounded_ac x" by (cases x) simp
qed

theorem ground_dom_grounded: "dg.grounded_dom"
  unfolding dg.grounded_dom_def apply (intro conjI)
     apply simp
  unfolding grounded_pred.simps apply (intro ballI)
  subgoal for x apply (cases x) by auto
   apply simp
  using acs_grounded by blast

theorem ground_prob_grounded: "pg.grounded_prob"
  using pg.grounded_prob_def ground_dom_grounded by simp

end

subsection \<open> Well-formedness \<close>

context grounder begin

lemma facts_len: "length facts = length fact_names"
  using fact_ids_def nat_range_length by simp

lemma ops_len: "length ops = length op_names"
  unfolding op_ids_def op_names_def by simp

end

context wf_grounder begin


lemma fact_names_dis: "distinct fact_names"
proof -
  have "fact_names ! i \<noteq> fact_names ! j" if "i \<noteq> j" "i < length fact_names" "j < length fact_names" for i j
  proof -
    have nth: "fact_names ! x = ground_pred (facts ! x) x" if "x < length facts" for x
      unfolding fact_ids_def using that nat_range_nth by simp

    have "is_predAtom (facts ! x)" if "x < length facts" for x
      using facts_wf wf_fmla_atom_alt that by fastforce
    with nth have app: "\<exists>s. fact_names ! x = Pred (padl fact_prefix_pad (show x) @ s)" if "x < length facts" for x
      using that ground_pred_cond by simp
    have "length (padl fact_prefix_pad (show x)) = fact_prefix_pad" if "x < length facts" for x
      using that fact_prefix_pad_def padl_length nat_show_len_mono
      using order_less_imp_le by metis
    hence "padl fact_prefix_pad (show i) @ s \<noteq> padl fact_prefix_pad (show j) @ t" for s t
      using that pad_show_neq by simp
    thus ?thesis using that app facts_len by (metis predicate.inject)
  qed
  thus ?thesis using distinct_conv_nth by blast
qed




lemma gr_preds_dis: "distinct (map pred (predicates D\<^sub>G))"
proof -
  have "map pred (predicates D\<^sub>G) = fact_names" by simp
  thus ?thesis using fact_names_dis by metis
qed

lemma gr_preds_wf: "list_all1 pg.wf_predicate_decl (predicates D\<^sub>G)"
  unfolding ground_dom_sel pg.wf_predicate_decl_alt by simp

lemma op_names_dis: "distinct (op_names)" proof -
  have "op_names ! i \<noteq> op_names ! j" if "i \<noteq> j" "i < length op_names" "j < length op_names" for i j
  proof -
    have nth: "\<exists>\<pi>. op_names ! x = ground_ac_name \<pi> x" if "x < length ops" for x
      using that op_ids_def op_names_def by force
    hence app: "\<exists>s. op_names ! x = padl op_prefix_pad (show x) @ s" if "x < length ops" for x
      using that ground_ac_name_alt by metis
    have "length (padl op_prefix_pad (show x)) = op_prefix_pad" if "x < length ops" for x
      using that op_prefix_pad_def padl_length nat_show_len_mono
      using order_less_imp_le by metis
    hence "padl op_prefix_pad (show i) @ s \<noteq> padl op_prefix_pad (show j) @ t" for s t
      using that pad_show_neq op_names_def by simp
    thus ?thesis using that app ops_len op_ids_def by metis
  qed
  thus ?thesis using distinct_conv_nth by blast
qed

lemma ground_ac_names:
  shows "map ac_name (map2 ground_ac ops op_names) = op_names"
proof -
  have "map ac_name (map2 ground_ac ops names) = names" if "length ops = length names" for names
    using that proof (induction ops arbitrary: names)
    case (Cons op ops)
    hence "length names \<noteq> 0" by auto
    hence 1: "names = hd names # tl names" by simp

    with Cons have "map ac_name (map2 ground_ac ops (tl names)) = tl names" by auto
    hence "map ac_name (map2 ground_ac (op # ops) (hd names # tl names)) =
      hd names # tl names" using ground_ac_sel by simp
    thus ?case using 1 by simp
  qed simp
  thus ?thesis using ops_len by simp
qed

lemma gr_acs_dis: "distinct (map ac_name (actions D\<^sub>G))"
  using ground_ac_names op_names_dis by simp

lemma wf_ops_resinst:
  "\<forall>\<pi> \<in> set ops. wf_ground_action (resolve_instantiate \<pi>)"
  "\<forall>\<pi> \<in> set ops. wf_fmla objT (precondition (resolve_instantiate \<pi>))"
  "\<forall>\<pi> \<in> set ops. wf_effect objT (effect (resolve_instantiate \<pi>))"
  using ops_wf wf_resolve_instantiate wf_ground_action_alt by simp_all

lemma gr_atom_wf:
  assumes "a \<in> set facts"
  shows "dg.wf_fmla_atom tyt (ground_fmla a)"
proof -
  from assms obtain p where p: "fact_map a = Some p" "p \<in> set fact_names"
    unfolding fact_map_def using lookup_zip facts_len by metis
  with p have 1: "ground_fmla a = Atom (predAtm p [])"
    using facts_wf assms by (cases a rule: is_predAtom.cases) auto
  hence patm: "is_predAtom (ground_fmla a)" using is_predAtom_decomp by auto

  from 1 have "dg.wf_fmla tyt (ground_fmla a) \<longleftrightarrow> dg.wf_atom tyt (predAtm p [])"
    by (metis dg.wf_fmla.simps(1))
  also have "... \<longleftrightarrow> dg.sig p = Some []" by (cases "dg.sig p") simp_all
  also have "... \<longleftrightarrow> PredDecl p [] \<in> set (predicates D\<^sub>G)"
    by (metis dg.pred_resolve gr_preds_dis)
  also have "... \<longleftrightarrow> p \<in> set fact_names" by force

  finally show ?thesis using p patm dg.wf_fmla_atom_alt by blast
qed

lemma gr_fmla_atom_wf:
  assumes "covered \<phi> facts" "is_predAtom \<phi>"
  shows "dg.wf_fmla_atom tyt (ground_fmla \<phi>)"
  using assms apply (cases \<phi> rule: is_predAtom.cases)
  unfolding covered_def using gr_atom_wf apply fastforce
  by simp_all

lemma ground_fmla_wf:
  assumes "covered \<phi> facts"
  shows "dg.wf_fmla tyt (ground_fmla \<phi>)"
  using assms apply (induction \<phi> rule: ground_fmla.induct)
  unfolding covered_def ground_fmla.simps ast_domain.wf_fmla.simps
              apply simp
             apply simp
            apply simp
  using gr_atom_wf apply force
  using formula.set_intros by metis+

abbreviation "eff_lits eff \<equiv> set (adds eff) \<union> set (dels eff)"

lemma ground_ac_wf:
  assumes "\<pi> \<in> set ops"
  shows "pg.wf_action_schema (ground_ac \<pi> i)"
proof -
  have "pg.wf_fmla tyt (ground_fmla (precondition (resolve_instantiate \<pi>)))" for tyt
    using assms pres_covered ground_fmla_wf by auto
  moreover have "ac_pre (ground_ac \<pi> i) = ground_fmla (precondition (resolve_instantiate \<pi>))"
    unfolding ground_ac_sel apply (cases "resolve_instantiate \<pi>") by simp
  ultimately have C1: "pg.wf_fmla (pg.ac_tyt (ground_ac \<pi> i)) (ac_pre (ground_ac \<pi> i))"
    by simp

  (* TODO simplify *)
  from assms have "wf_plan_action \<pi>" using ops_wf by simp
  hence "wf_ground_action (resolve_instantiate \<pi>)" using wf_resolve_instantiate by simp
  hence "wf_effect objT (effect (resolve_instantiate \<pi>))" using wf_ground_action_alt by simp
  hence "\<forall>a \<in> eff_lits (effect (resolve_instantiate \<pi>)). is_predAtom a"
    using wf_effect_alt wf_fmla_atom_alt by blast
  moreover have "\<forall>a \<in> eff_lits (effect (resolve_instantiate \<pi>)). covered a facts"
    using assms effs_covered unfolding Let_def by simp
  ultimately have "\<forall>a \<in> eff_lits (effect (resolve_instantiate \<pi>)).
    dg.wf_fmla_atom tyt (ground_fmla a)" for tyt using gr_fmla_atom_wf by blast
  hence "pg.wf_effect tyt (ga_eff (resolve_instantiate \<pi>))" for tyt
    using pg.wf_effect_alt by fastforce
  hence C2: "pg.wf_effect (ty_term (map_of (ac_params (ground_ac \<pi> i))) pg.constT) (ac_eff (ground_ac \<pi> i))" by simp

  from C1 C2 show ?thesis using pg.wf_action_schema_alt by simp
qed

lemma gr_acs_wf: "list_all1 pg.wf_action_schema (actions D\<^sub>G)"
proof (rule ballI)
  fix ac assume assm: "ac \<in> set (actions D\<^sub>G)"
  then obtain \<pi> i where "ac = ground_ac \<pi> i" "\<pi> \<in> set ops"
    unfolding ground_dom_sel using map2_obtain by metis
  with assm show "pg.wf_action_schema ac" using ground_ac_wf by simp
qed

theorem ground_dom_wf: "dg.wf_domain"
  unfolding dg.wf_domain_def apply (intro conjI)
  using dg.wf_types_def apply simp
  using gr_preds_dis apply simp
  using gr_preds_wf apply simp
  apply simp (* consts wf *)
  apply simp (* consts' types *)
  using gr_acs_dis gr_acs_wf by simp_all

lemma "length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> map_of (zip xs ys) (xs ! i) =
  Some (ys ! i)"
  by (simp add: map_of_zip_nth)

lemma "distinct xs \<Longrightarrow> i \<noteq> j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i \<noteq> xs ! j"
  by (simp add: nth_eq_iff_index_eq)

lemma gr_init_dis: "distinct (init P\<^sub>G)"
proof -
  have 0: "init P\<^sub>G = map ground_fmla (init P)" by simp
  have 1: "set (init P) \<subseteq> set facts" using all_facts init_achievable by blast
  have patms: "\<forall>a \<in> set (init P). is_predAtom a"
    using wf_P wf_world_model_def wf_fmla_atom_alt by blast

  have "is_predAtom a \<Longrightarrow> ground_fmla a = Atom (predAtm (the (fact_map a)) [])" for a
    by (cases a rule: is_predAtom.cases) simp_all
  hence 2: "map ground_fmla (init P) =
    map ((\<lambda>x. Atom (predAtm x [])) \<circ> (the \<circ> fact_map)) (init P)"
    using patms by auto
  have 3: "distinct (map (the \<circ> fact_map) (init P))"
    unfolding fact_map_def
    using facts_len facts_dist fact_names_dis wf_P 1 mapof_distinct_zip_distinct by blast

  have "inj (\<lambda>x. Atom (predAtm x []))"
    by (meson atom.inject(1) formula.inject(1) injI)
  hence "distinct (map ((\<lambda>x. Atom (predAtm x [])) \<circ> (the \<circ> fact_map)) (init P))"
    using 3 using map_inj_distinct by fastforce

  thus ?thesis using 0 2 by metis
qed

lemma gr_init_wf: "pg.wf_world_model (set (init P\<^sub>G))"
  unfolding pg.wf_world_model_def ground_prob_sel
  using init_achievable gr_atom_wf all_facts by auto

lemma gr_goal_wf: "pg.wf_fmla pg.objT (goal P\<^sub>G)"
  using goal_covered ground_fmla_wf by auto


theorem ground_prob_wf: "pg.wf_problem"
  unfolding pg.wf_problem_def apply (intro conjI)
  using ground_dom_wf apply simp
      apply simp (* consts + objects distinct *)
     apply simp (* objects' types *)
    using gr_init_dis apply blast
   using gr_init_wf apply blast
  using gr_goal_wf by blast

end

sublocale wf_grounder \<subseteq> dg: wf_ast_domain D\<^sub>G
  using ground_dom_wf
  by (simp add: wf_ast_domain_def)

sublocale wf_grounder \<subseteq> pg: wf_ast_problem P\<^sub>G
  using ground_prob_wf
  by (simp add: wf_ast_problem_def)


subsection \<open> Semantics \<close>

text \<open> ground locale setup \<close>

sublocale wf_grounder \<subseteq> dg: grounded_domain ground_dom
  using ground_dom_grounded
  by unfold_locales simp

sublocale wf_grounder \<subseteq> pg: grounded_problem ground_prob
  using ground_prob_grounded
  by unfold_locales simp



subsection \<open> Grounder Semantics \<close>

context grounder begin

lemma gr_predAtom: "is_predAtom a \<Longrightarrow> is_predAtom (ground_fmla a)"
  by (cases a rule: is_predAtom.cases) simp_all

lemma ground_init:
  "pg.I = ground_fmla ` I"
  unfolding ast_problem.I_def ground_prob_sel by simp

lemma covered_predAtom: "is_predAtom a \<Longrightarrow> covered a facts \<longleftrightarrow> a \<in> set facts"
  unfolding covered_def by (cases a rule: is_predAtom.cases) simp_all


end

context wf_grounder begin

(* can't easily apply mapof_zip_inj here due to the recursive nature of ground_fmla_inj *)
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

lemma ground_fmla_inv:
  assumes "M \<subseteq> set facts" "Atom (predAtm n args) \<in> set facts"
  assumes "ground_fmla (Atom (predAtm n args)) \<in> ground_fmla ` M"
  shows "Atom (predAtm n args) \<in> M"
  using assms ground_fmla_inj inj_on_image_mem_iff by metis

lemma ground_fmla_sem:
  assumes "covered \<phi> facts" "M \<subseteq> set facts"
  shows "M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<longleftrightarrow> ground_fmla ` M \<^sup>c\<TTurnstile>\<^sub>= ground_fmla \<phi>"
proof -
  have 1: "valuation M \<Turnstile> \<phi> \<longleftrightarrow> valuation (ground_fmla ` M) \<Turnstile> ground_fmla \<phi>"
    using assms(1) unfolding covered_def valuation_def
  proof (induction \<phi> rule: ground_fmla.induct)
    case (4 p args)
    hence cov: "Atom (predAtm p args) \<in> set facts" by simp
    from 4 show ?case
      using ground_fmla_inv[OF assms(2) cov] by force
  next
    case ("5_1" p args)
    hence cov: "Atom (predAtm p args) \<in> set facts" by simp
    from "5_1" show ?case
      using ground_fmla_inv[OF assms(2) cov] by force
  qed simp_all

  have "wm_basic M" "wm_basic (ground_fmla ` M)"
    using assms facts_wf wm_basic_def wf_fmla_atom_alt gr_predAtom by fast+
  thus ?thesis using 1 valuation_iff_close_world by blast
qed

lemma ground_goal_sem:
  assumes "M \<subseteq> set facts"
  shows "M \<^sup>c\<TTurnstile>\<^sub>= goal P \<longleftrightarrow> ground_fmla ` M \<^sup>c\<TTurnstile>\<^sub>= ground_fmla (goal P)"
  using assms goal_covered ground_fmla_sem by blast

(* only used in proofs, not in code *)
definition (in grounder) "op_map_inv \<equiv> map_of (zip ops op_names)"
definition (in grounder) "ground_pa \<pi> \<equiv> PAction (the (op_map_inv \<pi>)) []"

(* careful: two different type instances of ground_fmla.
  On the left side to 'term atom formula', on the right to 'object atom formula' *)
lemma ground_fmla_subst:
  "map_formula (map_atom (subst_term t)) (ground_fmla \<phi>)
    = ground_fmla \<phi>"
  by (induction \<phi> rule: ground_fmla.induct) simp_all

(* careful: two different type instance of ga_eff.
  On the left side to 'term ast_effect', on the right to 'object ast_effect' *)
lemma ground_effect_subst:
  "map_ast_effect (subst_term t) (ga_eff ga)
    = ga_eff ga"
  using ground_fmla_subst by (cases ga rule: ga_eff.cases) simp

lemma gr_pa_instantiation:
  shows "instantiate_action_schema (ground_ac \<pi> n) [] =
    (let ga = resolve_instantiate \<pi> in
      Ground_Action (ga_pre ga) (ga_eff ga))"
  unfolding ground_ac_def
  using ground_fmla_subst ground_effect_subst
    by (cases "resolve_instantiate \<pi>") simp

lemma ground_action_map_entry:
  assumes "\<pi> \<in> set ops"
  obtains i where
    "(\<pi>, ground_ac_name \<pi> i) \<in> set (zip ops op_names)"
    "(ground_ac_name \<pi> i, \<pi>) \<in> set (zip op_names ops)"
    "ground_ac \<pi> (ground_ac_name \<pi> i) \<in> set (actions D\<^sub>G)"
proof -
  from assms obtain i where i: "i < length ops" "ops ! i = \<pi>"
    using in_set_conv_nth by meson
  hence n: "op_names ! i = ground_ac_name \<pi> i"
    unfolding op_names_def op_ids_def by simp
  with i have "actions D\<^sub>G ! i = ground_ac \<pi> (ground_ac_name \<pi> i)"
    unfolding ground_dom_sel using ops_len by simp
  with i have a: "ground_ac \<pi> (ground_ac_name \<pi> i) \<in> set (actions D\<^sub>G)"
    unfolding ground_dom_sel in_set_conv_nth
    using ops_len by auto
  (* TODO use thesis variable if it exists *)
  from a n i show "(\<And>i. (\<pi>, ground_ac_name \<pi> i) \<in> set (zip ops op_names) \<Longrightarrow>
          (ground_ac_name \<pi> i, \<pi>) \<in> set (zip op_names ops) \<Longrightarrow>
          ground_ac \<pi> (ground_ac_name \<pi> i) \<in> set (actions D\<^sub>G) \<Longrightarrow> thesis) \<Longrightarrow>
    thesis"
    unfolding ground_dom_sel using ops_len
    by (metis map_of_SomeD map_of_zip_nth op_names_dis ops_dist)
qed

lemma ground_action_map_entry':
  assumes "\<pi> \<in> set ops"
  obtains n where
    "(\<pi>, n) \<in> set (zip ops op_names)"
    "(n, \<pi>) \<in> set (zip op_names ops)"
    "ground_ac \<pi> n \<in> set (actions D\<^sub>G)"
  using assms ground_action_map_entry by metis

lemma resolve_ground_pa:
  assumes "\<pi> \<in> set ops"
  obtains n where
    "dg.resolve_action_schema (name (ground_pa \<pi>)) = Some (ground_ac \<pi> n)"
proof -
  from assms obtain n where n:
    "(\<pi>, n) \<in> set (zip ops op_names)"
    "ground_ac \<pi> n \<in> set (actions D\<^sub>G)"
    using ground_action_map_entry' by metis

  hence "op_map_inv \<pi> = Some n"
    unfolding op_map_inv_def
    using ops_dist ops_len by simp
  (* TODO use thesis variable if it exists *)
  with n show "(\<And>n. dg.resolve_action_schema (name (ground_pa \<pi>)) = Some (ground_ac \<pi> n) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    unfolding dg.res_aux ground_ac_sel ground_pa_def by simp
qed

lemma resinst_ground_pa:
  assumes "\<pi> \<in> set ops"
  defines "ga \<equiv> resolve_instantiate \<pi>"
  shows "pg.resolve_instantiate (ground_pa \<pi>) =
    Ground_Action (ga_pre ga) (ga_eff ga)"
  unfolding pg.resolve_instantiate_alt grounder.ground_prob_sel(1)
  using assms resolve_ground_pa gr_pa_instantiation ground_pa_def
  by (metis option.sel plan_action.sel)

theorem ground_enabled_iff:
  assumes "M \<subseteq> set facts" "\<pi> \<in> set ops"
  shows "plan_action_enabled \<pi> M \<longleftrightarrow> pg.plan_action_enabled (ground_pa \<pi>) (ground_fmla ` M)"
    (is "?L \<longleftrightarrow> ?R")
proof -
  from assms obtain n where n:
    "pg.resolve_action_schema (name (ground_pa \<pi>)) = Some (ground_ac \<pi> n)"
    unfolding ground_prob_sel(1) using resolve_ground_pa by meson

  from assms have pre_iff: "M \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate \<pi>) \<longleftrightarrow>
    ground_fmla ` M \<^sup>c\<TTurnstile>\<^sub>= ground_fmla (precondition (resolve_instantiate \<pi>))"
    using pres_covered ground_fmla_sem by blast

  show ?thesis proof
    assume ?L
    have C1: "pg.wf_plan_action (ground_pa \<pi>)"
      unfolding pg.wf_plan_action_alt n apply simp
      unfolding ground_pa_def plan_action.sel
      unfolding pg.action_params_match_def by simp

    have C2: "ground_fmla ` M \<^sup>c\<TTurnstile>\<^sub>= precondition (pg.resolve_instantiate (ground_pa \<pi>))"
      unfolding resinst_ground_pa[OF assms(2)]
      unfolding ground_action.sel ga_pre_alt
      using \<open>?L\<close> pre_iff plan_action_enabled_def by blast
    
    from C1 C2 show ?R unfolding pg.plan_action_enabled_def ..
  next
    assume ?R
    have C1: "wf_plan_action \<pi>" using assms ops_wf by blast
    have C2: "M \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate \<pi>)"
      using \<open>?R\<close>
      unfolding pg.plan_action_enabled_def resinst_ground_pa[OF assms(2)]
      unfolding ground_action.sel plan_action.sel ga_pre_alt
      using pre_iff by blast

    from C1 C2 show ?L unfolding plan_action_enabled_def ..
  qed
qed

lemma effs_covered_alt:
  assumes "\<pi> \<in> set ops"
  shows "set (adds (effect (resolve_instantiate \<pi>))) \<union>
    set (dels (effect (resolve_instantiate \<pi>))) \<subseteq> set facts"
proof -
  have "wf_ground_action (resolve_instantiate \<pi>)"
    using assms ops_wf wf_resolve_instantiate by blast
  thus ?thesis
    unfolding wf_ground_action_alt wf_effect_alt wf_fmla_atom_alt
    using effs_covered covered_predAtom
    unfolding set_append Let_def using assms by blast
qed

lemma exec_covered:
  assumes "M \<subseteq> set facts" "\<pi> \<in> set ops"
  shows "execute_plan_action \<pi> M \<subseteq> set facts"
  using assms effs_covered_alt
  unfolding execute_plan_action_def apply_effect_alt by blast

lemma i_covered: "I \<subseteq> set facts"
  using all_facts
  by (auto simp add: init_achievable subset_Collect_conv)

lemma execs_covered:
  assumes "M \<subseteq> set facts" "set \<pi>s \<subseteq> set ops"
    "plan_action_path M \<pi>s M'"
  shows "M' \<subseteq> set facts"
using assms proof (induction \<pi>s arbitrary: M)
  case (Cons \<pi> \<pi>s)
  then obtain M'' where M'': "execute_plan_action \<pi> M = M''" "plan_action_path M'' \<pi>s M'"
    by simp
  with Cons show ?case using exec_covered
    by (meson dual_order.trans list.set_intros(1) set_subset_Cons subsetD)
qed simp

lemma path_covered:
  assumes "plan_action_path I \<pi>s M"
  shows "M \<subseteq> set facts" "set \<pi>s \<subseteq> set ops"
  using assms all_facts achievable_def apply auto[1]
  using assms all_ops applicable_def by blast

(* Right direction; from a valid plan in the lifted instance construct the corresponding plan for
  the grounded task. *)

lemma ground_action_exec_right:
  assumes "M \<subseteq> set facts" "\<pi> \<in> set ops" "execute_plan_action \<pi> M = M'"
  shows "pg.execute_plan_action (ground_pa \<pi>) (ground_fmla ` M) = ground_fmla ` M'"
proof -
  have injs: "inj_on ground_fmla (M \<union> set (dels (effect (resolve_instantiate \<pi>)))
      \<union> set (adds (effect (resolve_instantiate \<pi>))) \<union> M')"
    apply (rule inj_on_subset[of ground_fmla "set facts"])
     apply (simp add: ground_fmla_inj)
    using assms effs_covered_alt exec_covered by blast

  show ?thesis using assms(3)
    unfolding ast_problem.execute_plan_action_def
    unfolding resinst_ground_pa[OF assms(2)] ground_action.sel ga_eff_alt
    unfolding apply_effect_alt ast_effect.sel
    using set_image_minus_un(2)[OF injs] by simp
qed

lemma ground_plan_path_right:
  assumes "M \<subseteq> set facts" "set \<pi>s \<subseteq> set ops" "plan_action_path M \<pi>s M'"
  shows "pg.plan_action_path (ground_fmla ` M) (map ground_pa \<pi>s) (ground_fmla ` M')"
  using assms proof (induction \<pi>s arbitrary: M)
  case (Cons \<pi> \<pi>s)
  then obtain M'' where M'': "execute_plan_action \<pi> M = M''" "plan_action_path M'' \<pi>s M'"
    by simp
  thus ?case
    using Cons ground_action_exec_right exec_covered ground_enabled_iff by auto
qed simp

theorem valid_plan_right:
  assumes "valid_plan \<pi>s"
  shows "pg.valid_plan (map ground_pa \<pi>s)"
proof -
  from assms obtain M where M: "plan_action_path I \<pi>s M" "M \<^sup>c\<TTurnstile>\<^sub>= goal P"
    unfolding valid_plan_def valid_plan_from_def by blast

  thus ?thesis
    unfolding ast_problem.valid_plan_def ast_problem.valid_plan_from_def ground_prob_sel
    using ground_init ground_plan_path_right i_covered path_covered ground_goal_sem
     by metis
qed

(* Left *)

lemma restore_wf_pa:
  assumes "pg.wf_plan_action \<pi>'"
  shows "restore_ground_pa \<pi>' \<in> set ops" "ground_pa (restore_ground_pa \<pi>') = \<pi>'"
proof -
  obtain n where pi'[simp]: "\<pi>' = PAction n []"
    using pg.grounded_pa_nullary assms by (cases \<pi>') simp
  with assms obtain ac' where ac': "ac' \<in> set (actions D\<^sub>G)" "ac_name ac' = n"
    using pg.wf_plan_action_simple pg.wf_pa_refs_ac ground_prob_sel
    by metis
  then obtain \<pi> where pi: "(\<pi>, n) \<in> set (zip ops op_names)" "\<pi> \<in> set ops" "n \<in> set op_names" "ac' = ground_ac \<pi> n"
    unfolding ground_dom_sel using map2_obtain ac' ground_ac_sel by metis
  hence res: "restore_ground_pa \<pi>' = \<pi>"
    unfolding op_map_def pi' restore_ground_pa.simps
    using ops_len in_set_zip_flip op_names_dis by fastforce
  moreover from pi have "ground_pa \<pi> = \<pi>'"
    unfolding ground_pa_def op_map_inv_def pi'
    using ops_len ops_dist by simp
  from res this pi show "restore_ground_pa \<pi>' \<in> set ops" "ground_pa (restore_ground_pa \<pi>') = \<pi>'"
    by simp_all
qed

lemma ground_enabled_left:
  assumes "M \<subseteq> set facts" "pg.plan_action_enabled \<pi>' (ground_fmla ` M)"
  shows "plan_action_enabled (restore_ground_pa \<pi>') M"
  using assms restore_wf_pa ground_enabled_iff
  by (auto simp add: pg.plan_action_enabled_def)

lemma ground_exec_left:
  assumes "M \<subseteq> set facts" "pg.wf_plan_action \<pi>'"
  obtains M' where
    "pg.execute_plan_action \<pi>' (ground_fmla ` M) = ground_fmla ` M'"
    "execute_plan_action (restore_ground_pa \<pi>') M = M'"
  using assms restore_wf_pa ground_action_exec_right by metis

lemma ground_plan_path_left:
  assumes "M \<subseteq> set facts"
    "pg.plan_action_path (ground_fmla ` M) \<pi>s' gM'"
  shows "\<exists>M'. gM' = ground_fmla ` M' \<and>
    plan_action_path M (map restore_ground_pa \<pi>s') M'"
using assms proof (induction \<pi>s' arbitrary: M)
  case (Cons \<pi>' \<pi>s')
  hence w: "pg.wf_plan_action \<pi>'" "list_all1 pg.wf_plan_action \<pi>s'"
    unfolding pg.plan_action_path_def by simp_all
  from Cons obtain gN where
    "pg.execute_plan_action \<pi>' (ground_fmla ` M) = gN"
    "pg.plan_action_path gN \<pi>s' gM'" by simp
  with Cons w obtain N where N:
    "pg.execute_plan_action \<pi>' (ground_fmla ` M) = ground_fmla ` N"
    "execute_plan_action (restore_ground_pa \<pi>') M = N"
    "pg.plan_action_path (ground_fmla ` N) \<pi>s' gM'"
    using ground_exec_left by metis
  hence "N \<subseteq> set facts"
    using Cons.prems(1) w restore_wf_pa exec_covered by meson
  hence "\<exists>M'. gM' = ground_fmla ` M' \<and> plan_action_path N (restore_ground_plan \<pi>s') M'"
    using Cons.IH w(2) N(3) by presburger
  with Cons.prems N show ?case using ground_enabled_left by simp
qed simp

theorem valid_plan_left:
  assumes "pg.valid_plan \<pi>s'"
  shows "valid_plan (restore_ground_plan \<pi>s')"
proof -
  from assms obtain M' where M': "pg.plan_action_path pg.I \<pi>s' (ground_fmla ` M')"
    "ground_fmla ` M' \<^sup>c\<TTurnstile>\<^sub>= goal P\<^sub>G" "plan_action_path I (map restore_ground_pa \<pi>s') M'"
    unfolding pg.valid_plan_def pg.valid_plan_from_def
    using i_covered ground_plan_path_left ground_init by metis
  hence "M' \<subseteq> set facts" using path_covered by blast
  thus ?thesis
    unfolding valid_plan_def valid_plan_from_def
    using M' ground_goal_sem by auto
qed

corollary valid_plan_iff:
  "(\<exists>\<pi>s. valid_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. pg.valid_plan \<pi>s')"
  using valid_plan_right valid_plan_left by blast

end

subsection \<open> Code Setup \<close>

lemmas pddl_ground_code =
  grounder.fact_ids_def
  grounder.fact_prefix_pad_def
  grounder.op_ids_def
  grounder.op_names_def
  grounder.op_prefix_pad_def
  grounder.ground_pred.simps
  grounder.fact_map_def
  grounder.ground_fmla.simps
  grounder.ga_pre.simps
  grounder.ga_eff.simps
  grounder.ground_ac_def
  grounder.ground_dom_def
  grounder.ground_prob_def
  grounder.ground_ac_name.simps
  grounder.op_map_def
  grounder.restore_ground_pa.simps
declare pddl_ground_code[code]

end