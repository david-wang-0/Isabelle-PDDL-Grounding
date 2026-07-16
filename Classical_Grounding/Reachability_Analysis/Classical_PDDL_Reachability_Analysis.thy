theory Classical_PDDL_Reachability_Analysis
  imports Classical_PDDL_Reachability_Locales
begin

section \<open>PDDL reachability is the minimal model of the translated program\<close>

text \<open>The semantic relation between an accepted certificate and PDDL reachability. A PDDL
  \<^typ>\<open>fact\<close> and a ground datalog fact are the \<^emph>\<open>same type\<close> (\<^typ>\<open>predicate \<times> object list\<close>),
  so the achievable facts of the relaxed problem can be compared directly with the
  \<^emph>\<open>minimal datalog model\<close> of the translated program --- \<open>datalog_prog.derivable\<close>, the least
  model of the positive program \<^const>\<open>dl_rules\<close> with substitutions drawn from the object
  universe \<^const>\<open>ast_classical_problem.const_names\<close>. Under the translation well-formedness
  bundle \<^const>\<open>dl_bridge_wf\<close> they coincide.

  Combined with the generic \<^const>\<open>dl_certified_model\<close> correctness (an accepted certificate's
  facts are exactly the minimal model), this turns a generic-checker acceptance directly into the
  PDDL reachable-fact set --- the capstone \<open>certified_facts_eq_achievable\<close> --- without
  transferring each PDDL check. The two inclusions play the two familiar roles:
  \<^item> \<open>\<subseteq>\<close> (every achievable fact is derivable) is the \<^emph>\<open>soundness\<close> direction: the certified facts
    over-approximate the reachable facts, so it is safe to ground against them.
  \<^item> \<open>\<supseteq>\<close> (every derivable fact is achievable) is the \<^emph>\<open>tightness\<close> direction: the minimal model
    contains no junk, so the grounder output is not bloated with unreachable facts.

  Proof structure: \<open>\<subseteq>\<close> propagates \<open>derivable\<close>-closure along a valid plan (\<open>derivable_invariant\<close>),
  with \<open>derivable_init\<close> + \<open>derivable_step_adds\<close> the two engine-instantiation cores, still
  \<^bold>\<open>sorry\<close>; \<open>\<supseteq>\<close> is rule
  induction on \<open>derivable\<close> (\<open>dl_derivable_imp_achievable\<close>, the \<open>step\<close> case still
  \<^bold>\<open>sorry\<close>): a derivation step comes from a translated action clause (fire that action ---
  relaxation makes earlier facts persist) or from a fact clause of
  \<^const>\<open>ast_classical_problem.init'\<close> (achievable at the initial model).\<close>

context pddl_datalog
begin

subsubsection \<open>Reachability helper lemmas for the relaxed problem\<close>

text \<open>Building blocks for the minimal-model relation below (the engine-instantiation cores
  \<open>derivable_init\<close> / \<open>derivable_step_adds\<close>): argument enumeration over the finite object
  universe, the \<open>res_inst\<close>/\<open>consequence_of\<close> correspondence, and the relaxation precondition
  fact (an enabled action's positive precondition holds in the current model). These are
  PDDL-side facts that do not mention any certificate.\<close>

text \<open>Every object argument of a well-formed plan action is one of the finitely many object
  names, so the closure check's enumeration covers it.\<close>
lemma is_obj_of_type_const_name:
  assumes "is_obj_of_type n T"
  shows "n \<in> set const_names"
proof -
  have "objT n \<noteq> None" using assms by (auto simp: is_obj_of_type_def split: option.splits)
  hence "n \<in> dom objT" by auto
  thus ?thesis unfolding objT_alt by (auto simp: dom_map_of_conv_image_fst)
qed

lemma action_params_match_combos:
  assumes "action_params_match h args"
  shows "args \<in> set (all_combos \<checkmark> (replicate (length (parameters h)) const_names))"
proof -
  have len: "length args = length (parameters h)" using assms
    unfolding action_params_match_def by (simp add: list_all2_lengthD)
  have "\<forall>a \<in> set args. a \<in> set const_names"
  proof
    fix a assume "a \<in> set args"
    then obtain i where "i < length args" "args ! i = a" by (auto simp: in_set_conv_nth)
    hence "is_obj_of_type a (map snd (parameters h) ! i)"
      using assms unfolding action_params_match_def by (auto simp: list_all2_conv_all_nth)
    thus "a \<in> set const_names" using is_obj_of_type_const_name by blast
  qed
  hence "chosen_from (replicate (length (parameters h)) const_names) args"
    using chosen_from_replicate[OF len] by blast
  thus ?thesis using set_all_combos by auto
qed



text \<open>\<^bold>\<open>Kernel 2, sub-part 1 (\<open>res_inst\<close> \<open>\<leftrightarrow>\<close> \<open>consequence_of\<close>).\<close> The add-effects of the ground
  action a plan action resolves to are exactly the engine's \<open>consequence_of\<close> for the
  corresponding action clause: both apply the ground substitution \<open>ac_tsubst params args\<close> to the
  schema's add list.\<close>
lemma res_inst_adds_eq_consequence:
  assumes "SimpleActionSchema (ActionHead n params) b \<in> set (actions D)"
  shows "adds (effect (the (res_inst (SimplePlanAction n args))))
           = consequence_of (as_action_clause (SimpleActionSchema (ActionHead n params) b)) args"
proof -
  obtain pre eff where b: "b = SimpleActionBody pre eff" by (cases b)
  obtain a d ne where eff: "eff = Effect a d ne" by (cases eff)
  have "res_inst (SimplePlanAction n args)
          = Some (GroundAction (map_atom_fmla (ac_tsubst params args) pre)
                                (map_ast_effect (ac_tsubst params args) eff))"
    using res_inst_cond[OF assms[unfolded b]] .
  hence "adds (effect (the (res_inst (SimplePlanAction n args))))
           = map (map_atom_fmla (ac_tsubst params args)) a"
    using eff by simp
  also have "\<dots> = consequence_of (as_action_clause (SimpleActionSchema (ActionHead n params) b)) args"
    using b eff by simp
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Kernel 2 (one-step adds-closure).\<close> The add-effects of an \<^emph>\<open>enabled\<close> action are produced
  by one round of \<open>all_derivs\<close> from the (closed) certificate facts, hence already present. This
  is the deep engine-instantiation-completeness step; it is where \<^emph>\<open>relaxation\<close> is used (an
  enabled action's positive precondition atoms are exactly the facts that must already hold).\<close>
text \<open>\<^bold>\<open>Sub-part 2 (relaxation precondition) --- TODO.\<close> An enabled action's instantiated
  positive precondition atoms already hold in \<open>M\<close>, and its equality guards are satisfied.
  Uses relaxation (\<open>is_pos_conj (ac_pre ac)\<close>) + \<open>valuation\<close> semantics
  (\<open>valuation M \<Turnstile>\<^sub>m Atom (predAtm p xs) \<longleftrightarrow> Atom (predAtm p xs) \<in> fst M\<close>) + \<open>un_and\<close>
  conjunction elimination (\<open>cl_pred_pre = pos_lits_of\<close>, \<open>cl_cond_pre = cond_lits_of\<close>).\<close>
lemma enabled_clause_body:
  assumes "plan_action_enabled (SimplePlanAction n args) M"
    and "ac \<in> set (actions D)" and "ac_name ac = n"
  shows "set (map (map_atom_fmla (ac_tsubst (cl_params (as_action_clause ac)) args))
                  (cl_pred_pre (as_action_clause ac))) \<subseteq> fst M
       \<and> satisfies_conds (cl_params (as_action_clause ac))
            (cl_cond_pre (as_action_clause ac)) args"
proof -
  obtain h b where ac_hb: "ac = SimpleActionSchema h b" by (cases ac)
  obtain nm ps where h: "h = ActionHead nm ps" by (cases h)
  obtain pre eff where bdy: "b = SimpleActionBody pre eff" by (cases b)
  have nm_n: "nm = n" using assms(3) ac_hb h by simp
  have ac_eq: "ac = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre eff)"
    using ac_hb h bdy nm_n by simp
  obtain ad dl nl where eff_eq: "eff = Effect ad dl nl" by (cases eff)
  have cl_params: "cl_params (as_action_clause ac) = ps" using ac_eq eff_eq by simp
  have cl_pred: "cl_pred_pre (as_action_clause ac) = pos_lits_of pre" using ac_eq eff_eq by simp
  have cl_cond: "cl_cond_pre (as_action_clause ac) = cond_lits_of pre" using ac_eq eff_eq by simp
  have val_pre: "valuation M \<Turnstile>\<^sub>m precondition ((the \<circ> res_inst) (SimplePlanAction n args))"
    using assms(1) unfolding plan_action_enabled_def by (simp add: Let_def)
  have res: "res_inst (SimplePlanAction n args)
               = Some (GroundAction (map_atom_fmla (ac_tsubst ps args) pre)
                                    (map_ast_effect (ac_tsubst ps args) eff))"
    using res_inst_cond[OF assms(2)[unfolded ac_eq]] .
  have val_pre': "valuation M \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) pre"
    using val_pre res by simp
  have all_lits: "\<forall>l \<in> set (un_and pre). valuation M \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) l"
    using un_and_map_semantics[OF val_pre'] unfolding un_and_map_atom_fmla by auto
  have pos: "is_pos_conj pre"
  proof -
    have "\<forall>a\<in>set (actions D). is_pos_conj (ac_pre a)"
      using relaxed_prob by (auto simp: relaxed_prob_def relaxed_dom_def)
    hence "is_pos_conj (ac_pre ac)" using assms(2) by simp
    thus ?thesis using ac_eq by simp
  qed
  have pos_part: "set (map (map_atom_fmla (ac_tsubst ps args)) (pos_lits_of pre)) \<subseteq> fst M"
  proof
    fix x assume "x \<in> set (map (map_atom_fmla (ac_tsubst ps args)) (pos_lits_of pre))"
    then obtain l where l: "l \<in> set (pos_lits_of pre)"
      and x: "x = map_atom_fmla (ac_tsubst ps args) l" by auto
    have l_un: "l \<in> set (un_and pre)"
      and l_pred: "is_predAtom l" using l
      unfolding pos_lits_of_def by auto
    obtain p xs where l_eq: "l = Atom (predAtm p xs)" using l_pred
      by (cases l rule: is_predAtom.cases) auto
    have "valuation M \<Turnstile>\<^sub>m x" using all_lits l_un x by blast
    thus "x \<in> fst M" using x l_eq by (simp add: valuation_def)
  qed
  have cond_part: "list_all (\<lambda>c. valuation ({}, Map.empty) \<Turnstile>\<^sub>m
                              map_atom_fmla (ac_tsubst ps args) c) (cond_lits_of pre)"
    unfolding list_all_iff
  proof
    fix c assume "c \<in> set (cond_lits_of pre)"
    hence c_un: "c \<in> set (un_and pre)"
      and c_npred: "\<not> is_predAtom c"
      unfolding cond_lits_of_def by auto
    have "is_pos_lit c" using pos c_un is_pos_conj_alt by blast
    moreover
    have "valuation M \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) c"
      using all_lits c_un by blast
    ultimately
    show "valuation ({}, Map.empty) \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) c"
      using cond_lit_model_indep c_npred by blast
  qed
  show ?thesis
    unfolding cl_params cl_pred cl_cond using pos_part cond_part by blast
qed




text \<open>The translated program \<^const>\<open>dl_rules\<close> of this (relaxed, normalized) problem, over the
  object universe \<^const>\<open>const_names\<close>, as an interpretation of the assumption-free
  \<^locale>\<open>datalog_prog\<close>. Its inductive least model is available as \<open>dl_prog.derivable\<close>
  (= \<^term>\<open>datalog_prog.derivable (set const_names) (set (dl_rules P))\<close>).\<close>
sublocale dl_prog: datalog_prog "set const_names" "set (dl_rules P)" .

text \<open>\<^bold>\<open>Base core (still \<^bold>\<open>sorry\<close>):\<close> every initial fact is derivable --- it is the head of a
  bodyless ground fact clause \<^const>\<open>dl_fact_clause\<close> in \<^const>\<open>dl_rules\<close>, fired by the vacuous
  substitution.\<close>
lemma derivable_init:
  assumes mem: "Atom (predAtm p xs) \<in> fst I"
  shows "dl_prog.derivable (p, xs)"
proof -
  have "Atom (predAtm p xs) \<in> set (init P)" using mem
    unfolding I_def by simp
  hence mem': "Atom (predAtm p xs) \<in> set init'"
    unfolding init'_def conc_unique_un by simp
  have "Cls p (map id.Cst xs) [] \<in> set (List.map_filter dl_fact_clause init')"
    using mem' by (auto simp: set_map_filter' intro!: bexI[where x="Atom (predAtm p xs)"])
  hence cl: "(Cls p (map id.Cst xs) [] :: pddl_dl_clause) \<in> set (dl_rules P)"
    unfolding dl_rules_def by simp
  have v: "\<forall>x\<in>set (cls_vars (Cls p (map id.Cst xs) [] :: pddl_dl_clause)).
             (\<lambda>_. undefined) x \<in> set const_names" by simp
  have g: "\<forall>gd\<in>set (cls_guards (Cls p (map id.Cst xs) [] :: pddl_dl_clause)).
             eval_guard (\<lambda>_. undefined) gd" by (simp add: cls_guards_def)
  have b: "\<forall>a\<in>set (cls_body_atoms (Cls p (map id.Cst xs) [] :: pddl_dl_clause)).
             dl_prog.derivable (subst_atom (\<lambda>_. undefined) a)"
    by (simp add: cls_body_atoms_def List.map_filter_simps)
  have "dl_prog.derivable
          (subst_atom (\<lambda>_. undefined) (the_lh (Cls p (map id.Cst xs) [] :: pddl_dl_clause)))"
    using dl_prog.derivable.derive[OF cl v g b] .
  thus ?thesis by (simp add: subst_atom_def comp_def)
qed

text \<open>The substitution correspondence: the generic substitution \<open>\<lambda>v. ac_tsubst ps args (VAR v)\<close>
  applied to a translated term id agrees with the PDDL ground substitution \<^const>\<open>ac_tsubst\<close>
  on the original term (variables map through, constants are fixed). This is the bridge between
  the generic datalog \<^const>\<open>subst_id\<close> and the PDDL \<^const>\<open>ac_tsubst\<close>.\<close>
lemma subst_id_dl_id_term:
  "subst_id (\<lambda>v. ac_tsubst ps args (term.VAR v)) (dl_id_of_term t) = ac_tsubst ps args t"
  by (cases t) simp_all

text \<open>Every matched argument of an action is one of the object names.\<close>
lemma ac_arg_in_const_names:
  assumes "action_params_match h args" and "a \<in> set args"
  shows "a \<in> set const_names"
proof -
  obtain i where "i < length args" "args ! i = a" using assms(2)
    by (auto simp: in_set_conv_nth)
  hence "is_obj_of_type a (map snd (parameters h) ! i)"
    using assms(1) unfolding action_params_match_def by (auto simp: list_all2_conv_all_nth)
  thus ?thesis using is_obj_of_type_const_name by blast
qed

text \<open>A parameter variable is substituted to one of its action's arguments.\<close>
lemma ac_tsubst_var_in_args:
  assumes pm: "action_params_match (ActionHead n ps) args"
    and x: "x \<in> set (map fst ps)"
  shows "ac_tsubst ps args (term.VAR x) \<in> set args"
proof -
  have len: "length (map fst ps) = length args"
    using pm unfolding action_params_match_def by (simp add: list_all2_lengthD)
  obtain y where y: "map_of (zip (map fst ps) args) x = Some y" using x len
    by (metis map_of_zip_is_Some)
  hence "(x, y) \<in> set (zip (map fst ps) args)" by (rule map_of_SomeD)
  hence "y \<in> set args" by (rule set_zip_rightD)
  moreover
  have "ac_tsubst ps args (term.VAR x) = y" using y by simp
  ultimately
  show ?thesis by simp
qed

text \<open>A translated equality guard holds under the generic substitution exactly when the original
  PDDL equality condition is satisfied (the empty-model condition semantics of \<^const>\<open>satisfies_cond\<close>
  for an (in)equality is a pure object (in)equality, matching \<^const>\<open>eval_guard\<close>).\<close>
lemma dl_cond_rh_eval_guard:
  assumes "dl_cond_rh cnd = Some (Some g)"
    and "satisfies_cond ps args cnd"
  shows "eval_guard (\<lambda>v. ac_tsubst ps args (term.VAR v)) g"
  using assms
  by (cases cnd rule: dl_cond_rh.cases)
     (auto simp del: ac_tsubst_def simp add: valuation_def subst_id_dl_id_term)

text \<open>Shape of the translated literals: \<^const>\<open>dl_pos_rh\<close> yields either nothing or a positive
  body literal; \<^const>\<open>dl_cond_rh\<close> yields nothing, the drop marker \<open>Some None\<close>, or an equality
  guard. These pin down the body of a translated action clause.\<close>
lemma dl_pos_rh_form: "dl_pos_rh a = None \<or> (\<exists>p ids. dl_pos_rh a = Some (PosLit p ids))"
  by (cases a rule: dl_pos_rh.cases) auto

lemma dl_pos_rh_Some:
  assumes "dl_pos_rh a = Some r"
  shows "\<exists>p ts. a = Atom (predAtm p ts) \<and> r = PosLit p (map dl_id_of_term ts)"
  using assms by (cases a rule: dl_pos_rh.cases) auto

lemma dl_cond_rh_form:
  "dl_cond_rh c = None \<or> dl_cond_rh c = Some None
   \<or> (\<exists>g. dl_cond_rh c = Some (Some g) \<and> is_dl_guard g)"
  by (cases c rule: dl_cond_rh.cases) auto

text \<open>When no precondition/condition literal fails to translate, the clause produced for an
  add-effect predicate atom of an action clause is in \<^const>\<open>dl_clauses_of_action_clause\<close>.\<close>
lemma dl_clause_of_pos_mem:
  assumes nc: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl))"
    and np: "None \<notin> set (map dl_pos_rh (cl_pred_pre cl))"
    and mem: "Atom (predAtm p ts) \<in> set (cl_pos cl)"
  shows "Cls p (map dl_id_of_term ts) (dl_clause_body cl) \<in> set (dl_clauses_of_action_clause cl)"
  using assms
  by (auto simp: dl_clauses_of_action_clause_def Let_def set_map_filter' image_iff
           intro!: bexI[where x="Atom (predAtm p ts)"])

text \<open>Every guard of a translated action clause comes from an equality condition literal.\<close>
lemma guard_from_cond:
  assumes nc: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl))"
    and np: "None \<notin> set (map dl_pos_rh (cl_pred_pre cl))"
    and g: "gd \<in> set (cls_guards (Cls p ids (dl_clause_body cl)))"
  shows "\<exists>cnd \<in> set (cl_cond_pre cl). dl_cond_rh cnd = Some (Some gd)"
proof -
  let ?A = "map the (map dl_pos_rh (cl_pred_pre cl))"
  let ?Bc = "List.map_filter id (map the (map dl_cond_rh (cl_cond_pre cl)))"
  have gdf: "gd \<in> set (filter is_dl_guard (?A @ ?Bc))" using g
    by (simp add: cls_guards_def dl_clause_body_def)
  hence guard: "is_dl_guard gd"
    and inAB: "gd \<in> set ?A \<or> gd \<in> set ?Bc" by auto
  have notA: "gd \<notin> set ?A"
  proof
    assume "gd \<in> set ?A"
    then obtain a where
      a: "a \<in> set (cl_pred_pre cl)"
      and gd_eq: "gd = the (dl_pos_rh a)" by auto
    have m: "dl_pos_rh a \<in> set (map dl_pos_rh (cl_pred_pre cl))" using a by auto
    have nn: "dl_pos_rh a \<noteq> None"
    proof
      assume "dl_pos_rh a = None"
      hence "None \<in> set (map dl_pos_rh (cl_pred_pre cl))" using m by simp
      thus False using np by simp
    qed
    then obtain p' ids' where "dl_pos_rh a = Some (PosLit p' ids')" using dl_pos_rh_form[of a] by auto
    thus False using gd_eq guard by simp
  qed
  hence "gd \<in> set ?Bc" using inAB by simp
  hence "Some gd \<in> set (map the (map dl_cond_rh (cl_cond_pre cl)))"
    by (auto simp: set_map_filter')
  then obtain cnd where
    cnd: "cnd \<in> set (cl_cond_pre cl)"
    and someq: "the (dl_cond_rh cnd) = Some gd" by auto
  have m2: "dl_cond_rh cnd \<in> set (map dl_cond_rh (cl_cond_pre cl))" using cnd by auto
  have nn2: "dl_cond_rh cnd \<noteq> None"
  proof
    assume "dl_cond_rh cnd = None"
    hence "None \<in> set (map dl_cond_rh (cl_cond_pre cl))" using m2 by simp
    thus False using nc by simp
  qed
  hence "dl_cond_rh cnd = Some (Some gd)" using someq by (cases "dl_cond_rh cnd") auto
  thus ?thesis using cnd by blast
qed

text \<open>Every body atom of a translated action clause comes from a positive precondition atom.\<close>
lemma body_atom_from_pre:
  assumes nc: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl))"
    and np: "None \<notin> set (map dl_pos_rh (cl_pred_pre cl))"
    and b: "ba \<in> set (cls_body_atoms (Cls p ids (dl_clause_body cl)))"
  shows "\<exists>p' ts'. Atom (predAtm p' ts') \<in> set (cl_pred_pre cl) \<and> ba = (p', map dl_id_of_term ts')"
proof -
  let ?A = "map the (map dl_pos_rh (cl_pred_pre cl))"
  let ?Bc = "List.map_filter id (map the (map dl_cond_rh (cl_cond_pre cl)))"
  have "ba \<in> set (List.map_filter rh_body_atom (?A @ ?Bc))" using b
    by (simp add: cls_body_atoms_def dl_clause_body_def)
  then obtain x where
    x: "x \<in> set (?A @ ?Bc)"
    and rb: "rh_body_atom x = Some ba"
    by (auto simp: set_map_filter')
  have "x \<notin> set ?Bc"
  proof
    assume "x \<in> set ?Bc"
    hence "Some x \<in> set (map the (map dl_cond_rh (cl_cond_pre cl)))"
      by (auto simp: set_map_filter')
    then obtain cnd where
      cnd: "cnd \<in> set (cl_cond_pre cl)"
      and sx: "the (dl_cond_rh cnd) = Some x" by auto
    have m2: "dl_cond_rh cnd \<in> set (map dl_cond_rh (cl_cond_pre cl))" using cnd by auto
    have "dl_cond_rh cnd \<noteq> None"
    proof
      assume "dl_cond_rh cnd = None"
      hence "None \<in> set (map dl_cond_rh (cl_cond_pre cl))" using m2 by simp
      thus False using nc by simp
    qed
    hence "is_dl_guard x" using dl_cond_rh_form[of cnd] sx by auto
    thus False using rb by (cases x) auto
  qed
  hence "x \<in> set ?A" using x by simp
  then obtain a where
    a: "a \<in> set (cl_pred_pre cl)"
    and xeq: "x = the (dl_pos_rh a)" by auto
  have m: "dl_pos_rh a \<in> set (map dl_pos_rh (cl_pred_pre cl))" using a by auto
  have "dl_pos_rh a \<noteq> None"
  proof
    assume "dl_pos_rh a = None"
    hence "None \<in> set (map dl_pos_rh (cl_pred_pre cl))" using m by simp
    thus False using np by simp
  qed
  then obtain r where r: "dl_pos_rh a = Some r" by auto
  then obtain p' ts' where
    aeq: "a = Atom (predAtm p' ts')"
    and req: "r = PosLit p' (map dl_id_of_term ts')"
    using dl_pos_rh_Some
    by blast
  have "x = PosLit p' (map dl_id_of_term ts')" using xeq r req by simp
  hence "ba = (p', map dl_id_of_term ts')" using rb by simp
  thus ?thesis using aeq a by auto
qed

subsection \<open>Delete-relaxation monotonicity infrastructure (for the tightness direction)\<close>

text \<open>The tightness direction needs that the relaxed problem never deletes facts (delete
  relaxation, \<open>nd\<close>) and --- in the \<^locale>\<open>pddl_datalog\<close> context below --- is numeric-free
  (\<open>nne\<close>). Both are already part of \<^locale>\<open>relaxed_problem\<close> (hence \<^locale>\<open>pddl_datalog\<close>), so \<open>nd\<close>
  and numeric-freeness hold here as locale facts; under \<open>nd\<close> facts only grow along a plan and a plan
  replays from any larger start state. The firing/derivability lemmas additionally need only a
  non-empty object universe, threaded as an explicit \<open>const_names \<noteq> []\<close> hypothesis.\<close>

text \<open>Delete relaxation: the resolved action of every schema has no deletes; hence one executed
  step only adds facts (post-state facts = pre-state facts plus the action's adds).\<close>
lemma nd: "\<forall>a \<in> set (actions D). dels (ac_eff a) = []"
  using relaxed_prob by (auto simp: relaxed_prob_def relaxed_dom_def)

lemma execute_facts_eq:
  assumes en: "plan_action_enabled a M"
  shows "fst (execute_plan_action a M) = fst M \<union> set (adds (effect ((the \<circ> res_inst) a)))"
proof -
  obtain n args where a_eq: "a = SimplePlanAction n args" by (cases a)
  have wfa: "wf_classical_plan_action (SimplePlanAction n args)" using en
    unfolding a_eq plan_action_enabled_def by (simp add: Let_def)
  obtain sch where res: "resolve_classical_action_schema n = Some sch" using wfa
    by (auto simp: wf_classical_plan_action_simple split: option.splits)
  have sch_mem: "sch \<in> set (actions D)" using res
    unfolding resolve_classical_action_schema_def by (auto dest: index_by_eq_SomeD)
  have ri: "res_inst (SimplePlanAction n args)
              = Some (instantiate_classical_action_schema sch args)"
    using res by (simp add: res_inst_alt)
  have eff: "effect ((the \<circ> res_inst) a)
              = map_ast_effect (ac_tsubst (ac_params sch) args) (ac_eff sch)"
    unfolding a_eq using ri by (simp add: instantiate_classical_action_schema_alt)
  have "dels (ac_eff sch) = []" using nd sch_mem by blast
  hence dels0: "dels (effect ((the \<circ> res_inst) a)) = []"
    unfolding eff by (cases "ac_eff sch") simp
  obtain L N where M: "M = (L, N)" by (cases M)
  have "fst (execute_plan_action a M)
          = (L - set (dels (effect ((the \<circ> res_inst) a)))) \<union> set (adds (effect ((the \<circ> res_inst) a)))"
    unfolding execute_plan_action_def M by (simp add: apply_ground_action_alt)
  thus ?thesis using dels0 M by auto
qed

lemma execute_grows:
  assumes en: "plan_action_enabled a M"
  shows "fst M \<subseteq> fst (execute_plan_action a M)"
  using execute_facts_eq[OF en] by blast

text \<open>Hence facts persist along an entire valid plan.\<close>
lemma plan_grows_facts:
  assumes "valid_classical_plan_alt M \<pi>s N"
  shows "fst M \<subseteq> fst N"
  using assms
proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons a \<pi>s)
  have en: "plan_action_enabled a M"
    and rest: "valid_classical_plan_alt (execute_plan_action a M) \<pi>s N" using Cons.prems by simp_all
  have "fst M \<subseteq> fst (execute_plan_action a M)" by (rule execute_grows[OF en])
  also have "\<dots> \<subseteq> fst N" using Cons.IH[OF rest] .
  finally show ?case .
qed

text \<open>Reverse of \<open>un_and_map_semantics\<close>: a conjunction holds if all its \<open>un_and\<close> members do.\<close>
lemma un_and_map_semantics_rev: "(\<forall>f \<in> set (un_and F). A \<Turnstile>\<^sub>m f) \<Longrightarrow> A \<Turnstile>\<^sub>m F"
  by (induction F rule: un_and.induct) auto

text \<open>A positive conjunction's truth under \<open>valuation\<close> is monotone in the fact set: its positive
  predicate literals persist (membership grows), and its non-predicate (equality) literals are
  model-independent.\<close>
lemma valuation_pos_conj_mono:
  assumes pc: "is_pos_conj F" and sub: "fst M1 \<subseteq> fst M2"
    and v1: "valuation M1 \<Turnstile>\<^sub>m map_atom_fmla \<sigma> F"
  shows "valuation M2 \<Turnstile>\<^sub>m map_atom_fmla \<sigma> F"
proof (rule un_and_map_semantics_rev, unfold un_and_map_atom_fmla, rule ballI)
  fix g assume "g \<in> set (map (map_atom_fmla \<sigma>) (un_and F))"
  then obtain l where
    l: "l \<in> set (un_and F)"
    and g: "g = map_atom_fmla \<sigma> l" by auto
  have posl: "is_pos_lit l" using is_pos_conj_alt using l pc by blast
  have v1l: "valuation M1 \<Turnstile>\<^sub>m map_atom_fmla \<sigma> l" using un_and_map_semantics[OF v1] l
    unfolding un_and_map_atom_fmla by auto
  show "valuation M2 \<Turnstile>\<^sub>m g" unfolding g
  proof (cases "is_predAtom l")
    case True
    then obtain p xs where l_eq: "l = Atom (predAtm p xs)"
      by (cases l rule: is_predAtom.cases) auto
    have "Atom (predAtm p (map \<sigma> xs)) \<in> fst M1" using v1l
      unfolding l_eq by (simp add: valuation_def)
    hence "Atom (predAtm p (map \<sigma> xs)) \<in> fst M2" using sub by blast
    thus "valuation M2 \<Turnstile>\<^sub>m map_atom_fmla \<sigma> l" unfolding l_eq by (simp add: valuation_def)
  next
    case False
    show "valuation M2 \<Turnstile>\<^sub>m map_atom_fmla \<sigma> l"
      using cond_lit_model_indep[OF posl False] v1l by blast
  qed
qed



end

context pddl_datalog
begin

text \<open>No numeric effects --- derived from numeric-freeness (a numeric-free effect has an empty
  numeric-effect list).\<close>
lemma nne: "\<forall>a \<in> set (actions D). numeric_effects (ac_eff a) = []"
proof
  fix a assume "a \<in> set (actions D)"
  hence "num_free_ac a" using num_free unfolding num_free_prob_def num_free_dom_def by blast
  thus "numeric_effects (ac_eff a) = []" unfolding num_free_ac_def by (cases "ac_eff a") auto
qed

text \<open>Discharging the translation well-formedness bundle \<^const>\<open>dl_bridge_wf\<close> --- the last
  outstanding assumption. We prove each of its six conjuncts from numeric-freeness, relaxation,
  classical well-formedness, and the non-empty object universe.\<close>

text \<open>A variable that is typed by an action's parameter map is one of the parameter names.\<close>
lemma ty_term_VAR_dom:
  assumes "ty_term (map_of ps) constT (term.VAR x) \<noteq> None"
  shows "x \<in> set (map fst ps)"
proof -
  have "map_of ps x \<noteq> None" using assms by simp
  hence "x \<in> dom (map_of ps)" by blast
  thus ?thesis by (auto simp: dom_map_of_conv_image_fst)
qed

text \<open>A positive, non-predicate condition literal either translates (its \<^const>\<open>dl_cond_rh\<close> is
  not \<open>None\<close>) or is \<open>\<bottom>\<close> (statically unsatisfiable). These are the only positive non-predAtom
  literal shapes, and only \<open>\<bottom>\<close> fails to translate.\<close>
lemma cond_lit_translates_or_bot:
  assumes "is_pos_lit c" and "\<not> is_predAtom c"
  shows "dl_cond_rh c \<noteq> None \<or> c = \<bottom>"
  using assms by (cases c rule: is_pos_lit.cases) auto

text \<open>Decomposition of an action clause of the problem: it is \<^const>\<open>as_action_clause\<close> of a
  well-formed, positive-precondition action schema, exposing the four clause selectors and the
  precondition/effect well-formedness.\<close>
lemma aclause_decomp:
  assumes "cl \<in> set (ast_classical_problem.a_clauses P)"
  obtains n ps pre ad dl nl where
    "SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl)) \<in> set (actions D)"
    and "cl_params cl = ps"
    and "cl_pred_pre cl = pos_lits_of pre"
    and "cl_cond_pre cl = cond_lits_of pre"
    and "cl_pos cl = ad"
    and "wf_fmla (ty_term (map_of ps) constT) pre"
    and "wf_effect (ty_term (map_of ps) constT) (Effect ad dl nl)"
    and "is_pos_conj pre"
proof -
  have "cl \<in> set (map as_action_clause (actions D))" using assms
    by (simp add: ast_classical_problem.a_clauses_def)
  then obtain sch where
    sch: "sch \<in> set (actions D)"
    and cleq: "cl = as_action_clause sch" by auto
  obtain n ps pre ad dl nl where scheq:
      "sch = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl))"
    by (metis ast_classical_action_schema_cases_unfold ast_effect.exhaust)
  have wfsch: "wf_classical_action_schema sch"
    using sch wf_classical_domain unfolding wf_classical_domain_def by blast
  hence wfbody: "wf_fmla (ty_term (map_of ps) constT) pre
                 \<and> wf_effect (ty_term (map_of ps) constT) (Effect ad dl nl)"
    unfolding scheq by (simp add: Let_def)
  have pos: "is_pos_conj pre"
  proof -
    have "\<forall>a\<in>set (actions D). is_pos_conj (ac_pre a)"
      using relaxed_prob by (auto simp: relaxed_prob_def relaxed_dom_def)
    hence "is_pos_conj (ac_pre sch)" using sch by simp
    thus ?thesis unfolding scheq by simp
  qed
  have clsel: "cl_params cl = ps" "cl_pred_pre cl = pos_lits_of pre"
      "cl_cond_pre cl = cond_lits_of pre" "cl_pos cl = ad"
    using cleq scheq by simp_all
  show thesis
  proof (rule that[of n ps pre ad dl nl])
    show "SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl)) \<in> set (actions D)"
      using sch scheq by simp
    show "wf_fmla (ty_term (map_of ps) constT) pre" using wfbody by simp
    show "wf_effect (ty_term (map_of ps) constT) (Effect ad dl nl)" using wfbody by simp
  qed (rule clsel pos)+
qed

text \<open>Every add-effect of an action clause is a predicate atom (well-formed effects are atomic).\<close>
lemma aclause_adds_predAtom:
  assumes "cl \<in> set (ast_classical_problem.a_clauses P)" and "a \<in> set (cl_pos cl)"
  shows "is_predAtom a"
proof -
  obtain n ps pre ad dl nl where
      pos: "cl_pos cl = ad"
      and wfe: "wf_effect (ty_term (map_of ps) constT) (Effect ad dl nl)"
    by (rule aclause_decomp[OF assms(1)])
  have "a \<in> set ad" using assms(2) pos by simp
  hence "wf_fmla_atom (ty_term (map_of ps) constT) a" using wfe by simp
  thus ?thesis by (simp add: wf_fmla_atom_alt)
qed

text \<open>Every consequence of an action clause is a predicate atom: it is a ground instance of an
  add-effect, and \<^const>\<open>map_atom_fmla\<close> preserves the predicate-atom shape.\<close>
lemma consequence_predAtom:
  assumes "cl \<in> set (ast_classical_problem.a_clauses P)" and "f \<in> set (consequence_of cl args)"
  shows "is_predAtom f"
proof -
  obtain nm params preds cond add where cleq: "cl = AClause nm params preds cond add" by (cases cl)
  obtain a where a: "a \<in> set add"
    and feq: "f = map_atom_fmla (ac_tsubst params args) a" using assms(2) cleq by auto
  have "a \<in> set (cl_pos cl)" using a cleq by simp
  hence "is_predAtom a" by (rule aclause_adds_predAtom[OF assms(1)])
  then obtain p ts where "a = Atom (predAtm p ts)" by (cases a rule: is_predAtom.cases) auto
  thus "is_predAtom f" using feq by simp
qed

text \<open>A variable occurring in a translated head/body id list comes from the original term list.\<close>
lemma dl_id_vars_VAR:
  assumes "x \<in> set (concat (map id_vars_list (map dl_id_of_term ts)))"
  shows "term.VAR x \<in> set ts"
proof -
  obtain t where
    t: "t \<in> set ts"
    and xt: "x \<in> set (id_vars_list (dl_id_of_term t))" using assms
    by auto
  have "t = term.VAR x" using xt by (cases t) auto
  thus ?thesis using t by simp
qed

text \<open>Well-formedness of a conjunctive formula descends to its \<^const>\<open>un_and\<close> conjuncts.\<close>
lemma wf_fmla_un_and:
  assumes "wf_fmla T F" and "l \<in> set (un_and F)"
  shows "wf_fmla T l"
  using assms by (induction F rule: un_and.induct) auto

text \<open>A variable argument of a well-formed predicate/equality atom is an action parameter.\<close>
lemma wf_predAtm_VAR_param:
  assumes "wf_atom (ty_term (map_of ps) constT) (predAtm p ts)" and "term.VAR x \<in> set ts"
  shows "x \<in> set (map fst ps)"
proof -
  obtain Ts where la: "list_all2 (is_of_type (ty_term (map_of ps) constT)) ts Ts" using assms(1)
    by (auto split: option.splits)
  obtain i where i: "i < length ts" "ts ! i = term.VAR x" using assms(2)
    by (auto simp: in_set_conv_nth)
  have "i < length Ts" using i la by (simp add: list_all2_lengthD)
  hence "is_of_type (ty_term (map_of ps) constT) (term.VAR x) (Ts ! i)"
    using la i by (auto simp: list_all2_conv_all_nth)
  hence "ty_term (map_of ps) constT (term.VAR x) \<noteq> None"
    by (auto simp: is_of_type_def split: option.splits)
  thus ?thesis by (rule ty_term_VAR_dom)
qed

lemma wf_eqAtm_VAR_param:
  assumes "wf_atom (ty_term (map_of ps) constT) (eqAtm t1 t2)"
    and "term.VAR x = t1 \<or> term.VAR x = t2"
  shows "x \<in> set (map fst ps)"
proof -
  have "ty_term (map_of ps) constT (term.VAR x) \<noteq> None" using assms by auto
  thus ?thesis by (rule ty_term_VAR_dom)
qed

text \<open>A condition literal whose translation is a real guard is an (possibly negated) equality.\<close>
lemma dl_cond_rh_eqAtm_shape:
  assumes "dl_cond_rh cnd = Some (Some rh)"
  shows "(\<exists>t1 t2. cnd = Atom (eqAtm t1 t2) \<and> rh = Eql (dl_id_of_term t1) (dl_id_of_term t2))
       \<or> (\<exists>t1 t2. cnd = \<^bold>\<not> (Atom (eqAtm t1 t2)) \<and> rh = Neql (dl_id_of_term t1) (dl_id_of_term t2))"
  using assms by (cases cnd rule: dl_cond_rh.cases) auto

text \<open>Variables of a translated clause are contained in the action clause's parameters.\<close>
lemma dcl_vars_subset_params:
  assumes cl: "cl \<in> set (ast_classical_problem.a_clauses P)"
    and dcl: "dcl \<in> set (dl_clauses_of_action_clause cl)"
  shows "set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))"
proof -
  obtain n ps pre ad dl nl where
      clpar: "cl_params cl = ps"
      and clpred: "cl_pred_pre cl = pos_lits_of pre"
      and clcond: "cl_cond_pre cl = cond_lits_of pre"
      and clpos: "cl_pos cl = ad"
      and wfpre: "wf_fmla (ty_term (map_of ps) constT) pre"
      and wfeff: "wf_effect (ty_term (map_of ps) constT) (Effect ad dl nl)"
    by (rule aclause_decomp[OF cl])
  have nc: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl))"
    and np: "None \<notin> set (map dl_pos_rh (cl_pred_pre cl))" using dcl
    by (auto simp: dl_clauses_of_action_clause_def Let_def split: if_splits)
  have "dcl \<in> set (List.map_filter
       (\<lambda>f. case f of Atom (predAtm p ts) \<Rightarrow> Some (Cls p (map dl_id_of_term ts) (dl_clause_body cl))
                    | _ \<Rightarrow> None) (cl_pos cl))" using dcl np nc
    by (simp add: dl_clauses_of_action_clause_def Let_def)
  then obtain g where
    gmem: "g \<in> set (cl_pos cl)"
    and geq: "(case g of Atom (predAtm p ts) \<Rightarrow> Some (Cls p (map dl_id_of_term ts) (dl_clause_body cl))
                       | _ \<Rightarrow> None) = Some dcl"
    by (auto simp: set_map_filter')
  obtain hp hts where g_eq: "g = Atom (predAtm hp hts)"
    and dcleq: "dcl = Cls hp (map dl_id_of_term hts) (dl_clause_body cl)"
    using geq
    by (auto split: formula.splits atom.splits)
  have hmem: "Atom (predAtm hp hts) \<in> set ad" using gmem g_eq clpos by simp
  show "set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))"
    unfolding clpar
  proof
    fix x assume "x \<in> set (cls_vars dcl)"
    hence "x \<in> set (concat (map id_vars_list (map dl_id_of_term hts)))
         \<or> x \<in> set (concat (map rh_vars_list (dl_clause_body cl)))"
      using dcleq by auto
    thus "x \<in> set (map fst ps)"
    proof
      assume "x \<in> set (concat (map id_vars_list (map dl_id_of_term hts)))"
      hence vx: "term.VAR x \<in> set hts" by (rule dl_id_vars_VAR)
      have "\<forall>ae\<in>set ad. wf_fmla_atom (ty_term (map_of ps) constT) ae" using wfeff by simp
      hence "wf_fmla_atom (ty_term (map_of ps) constT) (Atom (predAtm hp hts))" using hmem by blast
      hence "wf_atom (ty_term (map_of ps) constT) (predAtm hp hts)" by (simp add: wf_fmla_atom_alt)
      thus "x \<in> set (map fst ps)" using wf_predAtm_VAR_param[OF _ vx] by blast
    next
      assume "x \<in> set (concat (map rh_vars_list (dl_clause_body cl)))"
      then obtain rh where
        rh: "rh \<in> set (dl_clause_body cl)"
        and xrh: "x \<in> set (rh_vars_list rh)"
        by auto
      have "rh \<in> set (map the (map dl_pos_rh (cl_pred_pre cl)))
                  \<or> rh \<in> set (List.map_filter id (map the (map dl_cond_rh (cl_cond_pre cl))))" using rh
        by (auto simp: dl_clause_body_def)
      thus "x \<in> set (map fst ps)"
      proof
        assume "rh \<in> set (map the (map dl_pos_rh (cl_pred_pre cl)))"
        then obtain a where
          a: "a \<in> set (cl_pred_pre cl)"
          and rh_eq: "rh = the (dl_pos_rh a)"
          by auto
        have m: "dl_pos_rh a \<in> set (map dl_pos_rh (cl_pred_pre cl))" using a by simp
        have "dl_pos_rh a \<noteq> None"
        proof
          assume "dl_pos_rh a = None"
          hence "None \<in> set (map dl_pos_rh (cl_pred_pre cl))" using m by simp
          thus False using np by simp
        qed
        then obtain r where r: "dl_pos_rh a = Some r" by auto
        then obtain p' ts' where a_eq: "a = Atom (predAtm p' ts')"
          and r_eq: "r = PosLit p' (map dl_id_of_term ts')" using dl_pos_rh_Some by blast
        have "x \<in> set (concat (map id_vars_list (map dl_id_of_term ts')))" using xrh rh_eq r r_eq
          by simp
        hence vx: "term.VAR x \<in> set ts'" by (rule dl_id_vars_VAR)
        have "a \<in> set (un_and pre)" using a clpred by (simp add: pos_lits_of_def)
        hence "wf_fmla (ty_term (map_of ps) constT) a" using wfpre by (rule wf_fmla_un_and[rotated])
        hence "wf_atom (ty_term (map_of ps) constT) (predAtm p' ts')" using a_eq by simp
        thus "x \<in> set (map fst ps)" using wf_predAtm_VAR_param[OF _ vx] by blast
      next
        assume "rh \<in> set (List.map_filter id (map the (map dl_cond_rh (cl_cond_pre cl))))"
        hence "Some rh \<in> set (map the (map dl_cond_rh (cl_cond_pre cl)))"
          by (auto simp: set_map_filter')
        then obtain cnd where
          cnd: "cnd \<in> set (cl_cond_pre cl)"
          and srh: "the (dl_cond_rh cnd) = Some rh"
          by auto
        have m2: "dl_cond_rh cnd \<in> set (map dl_cond_rh (cl_cond_pre cl))" using cnd by simp
        have "dl_cond_rh cnd \<noteq> None"
        proof
          assume "dl_cond_rh cnd = None"
          hence "None \<in> set (map dl_cond_rh (cl_cond_pre cl))" using m2 by simp
          thus False using nc by simp
        qed
        hence dceq: "dl_cond_rh cnd = Some (Some rh)" using srh by (cases "dl_cond_rh cnd") auto
        have cnd_un: "cnd \<in> set (un_and pre)" using cnd clcond by (simp add: cond_lits_of_def)
        have wfcnd: "wf_fmla (ty_term (map_of ps) constT) cnd"
          using wfpre cnd_un by (rule wf_fmla_un_and)
        show "x \<in> set (map fst ps)" using dl_cond_rh_eqAtm_shape[OF dceq]
        proof
          assume "\<exists>t1 t2. cnd = Atom (eqAtm t1 t2) \<and> rh = Eql (dl_id_of_term t1) (dl_id_of_term t2)"
          then obtain t1 t2 where ce: "cnd = Atom (eqAtm t1 t2)"
            and re: "rh = Eql (dl_id_of_term t1) (dl_id_of_term t2)" by blast
          have "x \<in> set (concat (map id_vars_list (map dl_id_of_term [t1, t2])))" using xrh re by simp
          hence "term.VAR x \<in> set [t1, t2]" by (rule dl_id_vars_VAR)
          hence vx: "term.VAR x = t1 \<or> term.VAR x = t2" by auto
          have "wf_atom (ty_term (map_of ps) constT) (eqAtm t1 t2)" using wfcnd ce by simp
          thus "x \<in> set (map fst ps)" using wf_eqAtm_VAR_param[OF _ vx] by blast
        next
          assume "\<exists>t1 t2. cnd = \<^bold>\<not> (Atom (eqAtm t1 t2)) \<and> rh = Neql (dl_id_of_term t1) (dl_id_of_term t2)"
          then obtain t1 t2 where ce: "cnd = \<^bold>\<not> (Atom (eqAtm t1 t2))"
            and re: "rh = Neql (dl_id_of_term t1) (dl_id_of_term t2)" by blast
          have "x \<in> set (concat (map id_vars_list (map dl_id_of_term [t1, t2])))" using xrh re by simp
          hence "term.VAR x \<in> set [t1, t2]" by (rule dl_id_vars_VAR)
          hence vx: "term.VAR x = t1 \<or> term.VAR x = t2" by auto
          have "wf_atom (ty_term (map_of ps) constT) (eqAtm t1 t2)" using wfcnd ce by simp
          thus "x \<in> set (map fst ps)" using wf_eqAtm_VAR_param[OF _ vx] by blast
        qed
      qed
    qed
  qed
qed

text \<open>Every formula in the extended initial state is a predicate atom.\<close>
lemma init'_is_predAtom:
  assumes f: "f \<in> set (ast_classical_problem.init' P)"
  shows "is_predAtom f"
proof -
  have setun: "f \<in> set pseudo_init \<or> f \<in> set (init P)"
    using f by (simp add: init'_def conc_unique_un)
  show "is_predAtom f"
  proof (cases "f \<in> set (init P)")
    case True
    have wfor: "wf_fmla_atom objT f \<or> wf_func_assign f"
      using True wf_classical_problem unfolding wf_classical_problem_def by blast
    have nf: "num_free_fmla f" using True num_free unfolding num_free_prob_def by blast
    have "\<not> wf_func_assign f"
    proof
      assume "wf_func_assign f"
      then obtain l r where "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
        by (cases f rule: wf_func_assign.cases) auto
      thus False using nf by simp
    qed
    hence "wf_fmla_atom objT f" using wfor by blast
    thus "is_predAtom f" by (simp add: wf_fmla_atom_alt)
  next
    case False
    hence "f \<in> set pseudo_init" using setun by simp
    then obtain fc where
      fc: "fc \<in> set fact_clauses"
      and fcc: "f \<in> set (all_fact_consqs fc)"
      by (auto simp: pseudo_init_def)
    obtain args where args: "f \<in> set (consequence_of fc args)" using fcc by auto
    have fcmem: "fc \<in> set (ast_classical_problem.a_clauses P)"
      using fc by (auto simp: fact_clauses_def)
    show "is_predAtom f" by (rule consequence_predAtom[OF fcmem args])
  qed
qed

text \<open>The translation well-formedness bundle holds for this problem, given a non-empty object
  universe (\<open>ne\<close>) --- the only conjunct of \<^const>\<open>dl_bridge_wf\<close> not derivable from the
  \<^locale>\<open>pddl_datalog\<close> data.\<close>
lemma bridge:
  assumes ne: "const_names \<noteq> []"
  shows "dl_bridge_wf P"
proof (rule dl_bridge_wfI)
  fix cl a
  assume cl: "cl \<in> set (ast_classical_problem.a_clauses P)" and a: "a \<in> set (cl_pred_pre cl)"
  obtain n ps pre ad dl nl where dec: "cl_pred_pre cl = pos_lits_of pre"
    by (rule aclause_decomp[OF cl])
  have "a \<in> set (pos_lits_of pre)" using a dec by simp
  hence "is_predAtom a" by (simp add: pos_lits_of_def)
  then obtain p ts where "a = Atom (predAtm p ts)" by (cases a rule: is_predAtom.cases) auto
  thus "dl_pos_rh a \<noteq> None" by simp
next
  fix cl a
  assume cl: "cl \<in> set (ast_classical_problem.a_clauses P)" and a: "a \<in> set (cl_pos cl)"
  show "is_predAtom a" by (rule aclause_adds_predAtom[OF cl a])
next
  fix cl cnd
  assume cl: "cl \<in> set (ast_classical_problem.a_clauses P)" and cnd: "cnd \<in> set (cl_cond_pre cl)"
  obtain n ps pre ad dl nl where
    dec: "cl_cond_pre cl = cond_lits_of pre"
    and pos: "is_pos_conj pre"
    by (rule aclause_decomp[OF cl])
  have cnd': "cnd \<in> set (cond_lits_of pre)" using cnd dec by simp
  hence cnd_un: "cnd \<in> set (un_and pre)"
    and cnd_np: "\<not> is_predAtom cnd"
    by (auto simp: cond_lits_of_def)
  have "is_pos_lit cnd" using pos cnd_un is_pos_conj_alt by blast
  hence "dl_cond_rh cnd \<noteq> None \<or> cnd = \<bottom>" using cnd_np cond_lit_translates_or_bot by blast
  thus "dl_cond_rh cnd \<noteq> None \<or> (\<forall>args. \<not> satisfies_cond (cl_params cl) args cnd)"
  proof
    assume "cnd = \<bottom>"
    hence "\<forall>args. \<not> satisfies_cond (cl_params cl) args cnd" by simp
    thus ?thesis by blast
  qed blast
next
  fix cl dcl
  assume cl: "cl \<in> set (ast_classical_problem.a_clauses P)"
    and dcl: "dcl \<in> set (dl_clauses_of_action_clause cl)"
  show "set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))"
    by (rule dcl_vars_subset_params[OF cl dcl])
next
  fix f
  assume f: "f \<in> set (ast_classical_problem.init' P)"
  show "is_predAtom f" by (rule init'_is_predAtom[OF f])
next
  show "ast_classical_problem.const_names P \<noteq> []" using ne by simp
qed

text \<open>\<^bold>\<open>Step core:\<close> the add-effects of an enabled action are derivable, given
  that the current world-model facts are. The fired action's translated clause supplies the
  generic ground instance (substitution from the action arguments, body atoms from the
  hypothesis, equality guards from \<^const>\<open>satisfies_conds\<close>).\<close>
lemma derivable_step_adds:
  assumes ne: "const_names \<noteq> []"
    and en: "plan_action_enabled a M"
    and IH: "\<forall>p xs. Atom (predAtm p xs) \<in> fst M
               \<longrightarrow> dl_prog.derivable (p, xs)"
    and mem: "Atom (predAtm p xs) \<in> set (adds (effect ((the \<circ> res_inst) a)))"
  shows "dl_prog.derivable (p, xs)"
proof -
  obtain n args where a_eq: "a = SimplePlanAction n args" by (cases a)
  have wfa: "wf_classical_plan_action (SimplePlanAction n args)" using en
    unfolding a_eq plan_action_enabled_def by simp
  obtain sch where res: "resolve_classical_action_schema n = Some sch" using wfa
    by (auto simp: wf_classical_plan_action_simple split: option.splits)
  obtain n' ps pre ad dl nl where sch_eq:
      "sch = SimpleActionSchema (ActionHead n' ps) (SimpleActionBody pre (Effect ad dl nl))"
    by (metis ast_classical_action_schema_cases_unfold ast_effect.exhaust)
  have pm0: "action_params_match (ActionHead n' ps) args" using wfa res
    by (simp add: wf_classical_plan_action_simple sch_eq)
  have sch_mem: "sch \<in> set (actions D)"
    and sch_name: "ac_name sch = n" using res
    unfolding resolve_classical_action_schema_def by (auto dest: index_by_eq_SomeD)
  have n'_n: "n' = n" using sch_name sch_eq by simp
  have sch_eq': "sch = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl))"
    using sch_eq n'_n by simp
  have pm: "action_params_match (ActionHead n ps) args" using pm0 n'_n by simp
  define cl_ac where "cl_ac = as_action_clause sch"
  have clparams: "cl_params cl_ac = ps"
    and clpred: "cl_pred_pre cl_ac = pos_lits_of pre"
    and clcond: "cl_cond_pre cl_ac = cond_lits_of pre"
    and clpos: "cl_pos cl_ac = ad"
    unfolding cl_ac_def sch_eq' by simp_all
  have cl_ac_mem: "cl_ac \<in> set a_clauses"
    unfolding cl_ac_def a_clauses_def using sch_mem by simp
  have np: "None \<notin> set (map dl_pos_rh (cl_pred_pre cl_ac))"
    using dl_bridge_wf_pred_preD[OF bridge[OF ne] cl_ac_mem] by fastforce
  have posprop: "\<forall>a \<in> set (cl_pos cl_ac). is_predAtom a"
    using dl_bridge_wf_posD[OF bridge[OF ne] cl_ac_mem] by blast
  have condwf: "\<forall>cnd \<in> set (cl_cond_pre cl_ac).
       dl_cond_rh cnd \<noteq> None \<or> (\<forall>args. \<not> satisfies_cond ps args cnd)"
    unfolding clparams[symmetric] using dl_bridge_wf_condD[OF bridge[OF ne] cl_ac_mem] by blast
  have varsub: "\<forall>dcl \<in> set (dl_clauses_of_action_clause cl_ac). set (cls_vars dcl) \<subseteq> set (map fst ps)"
    unfolding clparams[symmetric] using dl_bridge_wf_varsD[OF bridge[OF ne] cl_ac_mem] by blast
  have en': "plan_action_enabled (SimplePlanAction n args) M" using en a_eq by simp
  note ecb = enabled_clause_body[OF en' sch_mem sch_name]
  have pos_part: "set (map (map_atom_fmla (ac_tsubst ps args)) (cl_pred_pre cl_ac)) \<subseteq> fst M"
    using ecb by (simp add: cl_ac_def[symmetric] clparams)
  have sat: "satisfies_conds ps (cl_cond_pre cl_ac) args"
    using ecb by (simp add: cl_ac_def[symmetric] clparams)
  have nc: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl_ac))"
  proof -
    have "\<forall>cnd \<in> set (cl_cond_pre cl_ac). dl_cond_rh cnd \<noteq> None"
    proof
      fix cnd assume c: "cnd \<in> set (cl_cond_pre cl_ac)"
      have "satisfies_cond ps args cnd" using sat c by (simp add: list_all_iff)
      moreover
      have "dl_cond_rh cnd \<noteq> None \<or> (\<forall>args'. \<not> satisfies_cond ps args' cnd)" using condwf c by blast
      ultimately
      show "dl_cond_rh cnd \<noteq> None" by blast
    qed
    thus ?thesis by auto
  qed
  have adds_eq: "adds (effect ((the \<circ> res_inst) a)) = consequence_of cl_ac args"
    using res_inst_adds_eq_consequence[OF sch_mem[unfolded sch_eq']]
    unfolding a_eq cl_ac_def sch_eq' by (simp add: comp_def)
  have conseq: "consequence_of cl_ac args = map (map_atom_fmla (ac_tsubst ps args)) (cl_pos cl_ac)"
    unfolding cl_ac_def sch_eq' by simp
  have memc: "Atom (predAtm p xs) \<in> set (map (map_atom_fmla (ac_tsubst ps args)) (cl_pos cl_ac))"
    using mem adds_eq conseq by simp
  then obtain f0 where f0: "f0 \<in> set (cl_pos cl_ac)"
    and f0eq: "Atom (predAtm p xs) = map_atom_fmla (ac_tsubst ps args) f0" by auto
  have "is_predAtom f0" using posprop f0 by blast
  then obtain p0 ts0 where f0_pred: "f0 = Atom (predAtm p0 ts0)"
    by (cases f0 rule: is_predAtom.cases) auto
  have pxs: "p = p0 \<and> xs = map (ac_tsubst ps args) ts0"
    using f0eq f0_pred by simp
  have mem0: "Atom (predAtm p0 ts0) \<in> set (cl_pos cl_ac)" using f0 f0_pred by simp
  define sig where "sig = (\<lambda>v. ac_tsubst ps args (term.VAR v))"
  define B where "B = dl_clause_body cl_ac"
  have clmem: "Cls p0 (map dl_id_of_term ts0) B \<in> set (dl_clauses_of_action_clause cl_ac)"
    unfolding B_def by (rule dl_clause_of_pos_mem[OF nc np mem0])
  have clrules: "Cls p0 (map dl_id_of_term ts0) B \<in> set (dl_rules P)"
    unfolding dl_rules_def using clmem cl_ac_mem by auto
  have vars: "\<forall>x \<in> set (cls_vars (Cls p0 (map dl_id_of_term ts0) B)). sig x \<in> set const_names"
  proof
    fix x assume "x \<in> set (cls_vars (Cls p0 (map dl_id_of_term ts0) B))"
    hence xp: "x \<in> set (map fst ps)" using varsub clmem by blast
    have "sig x \<in> set args" unfolding sig_def using ac_tsubst_var_in_args[OF pm xp] .
    thus "sig x \<in> set const_names" using ac_arg_in_const_names[OF pm] by blast
  qed
  have guards: "\<forall>g \<in> set (cls_guards (Cls p0 (map dl_id_of_term ts0) B)). eval_guard sig g"
  proof
    fix g assume "g \<in> set (cls_guards (Cls p0 (map dl_id_of_term ts0) B))"
    hence ing: "g \<in> set (cls_guards (Cls p0 (map dl_id_of_term ts0) (dl_clause_body cl_ac)))"
      unfolding B_def .
    obtain cnd where cnd: "cnd \<in> set (cl_cond_pre cl_ac)"
      and dcr: "dl_cond_rh cnd = Some (Some g)" using guard_from_cond[OF nc np ing] by blast
    have sc: "satisfies_cond ps args cnd" using sat cnd by (simp add: list_all_iff)
    show "eval_guard sig g" using dl_cond_rh_eval_guard[OF dcr sc] unfolding sig_def .
  qed
  have bodyder: "\<forall>a \<in> set (cls_body_atoms (Cls p0 (map dl_id_of_term ts0) B)).
      dl_prog.derivable (subst_atom sig a)"
  proof
    fix a assume "a \<in> set (cls_body_atoms (Cls p0 (map dl_id_of_term ts0) B))"
    hence ainb: "a \<in> set (cls_body_atoms (Cls p0 (map dl_id_of_term ts0) (dl_clause_body cl_ac)))"
      unfolding B_def .
    obtain p' ts'
      where prem: "Atom (predAtm p' ts') \<in> set (cl_pred_pre cl_ac)"
        and aeq: "a = (p', map dl_id_of_term ts')"
      using body_atom_from_pre[OF nc np ainb] by blast
    have sa: "subst_atom sig a = (p', map (ac_tsubst ps args) ts')"
      unfolding aeq subst_atom_def
      by (simp add: sig_def subst_id_dl_id_term comp_def del: ac_tsubst_def)
    have "map_atom_fmla (ac_tsubst ps args) (Atom (predAtm p' ts')) \<in> fst M"
      using pos_part prem by auto
    hence "Atom (predAtm p' (map (ac_tsubst ps args) ts')) \<in> fst M" by simp
    hence "dl_prog.derivable (p', map (ac_tsubst ps args) ts')" using IH by blast
    thus "dl_prog.derivable (subst_atom sig a)" unfolding sa .
  qed
  have der: "dl_prog.derivable
        (subst_atom sig (the_lh (Cls p0 (map dl_id_of_term ts0) B)))"
    by (rule dl_prog.derivable.derive[OF clrules vars guards bodyder])
  have lh: "subst_atom sig (the_lh (Cls p0 (map dl_id_of_term ts0) B)) = (p, xs)"
    unfolding subst_atom_def
    by (simp add: sig_def subst_id_dl_id_term comp_def pxs del: ac_tsubst_def)
  show ?thesis using der lh by simp
qed

text \<open>The derivability invariant carried along a valid plan, proved from \<open>derivable_step_adds\<close>:
  every fact of a reachable world model is derivable, given the initial facts are.\<close>
lemma derivable_invariant:
  assumes ne: "const_names \<noteq> []"
  shows "valid_classical_plan_alt M \<pi>s M'
         \<Longrightarrow> (\<forall>p xs. Atom (predAtm p xs) \<in> fst M
                \<longrightarrow> dl_prog.derivable (p, xs))
         \<Longrightarrow> (\<forall>p xs. Atom (predAtm p xs) \<in> fst M'
                \<longrightarrow> dl_prog.derivable (p, xs))"
proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons a \<pi>s)
  let ?a' = "(the \<circ> res_inst) a"
  have en: "plan_action_enabled a M"
    and rest: "valid_classical_plan_alt (execute_plan_action a M) \<pi>s M'" using Cons.prems(1) by simp_all
  obtain L N where M: "M = (L, N)" by (cases M)
  have fstM': "fst (execute_plan_action a M)
                 = (L - set (dels (effect ?a'))) \<union> set (adds (effect ?a'))"
    unfolding execute_plan_action_def M using apply_ground_action_alt[of ?a' L N] by simp
  have step: "\<forall>p xs. Atom (predAtm p xs) \<in> fst (execute_plan_action a M)
                \<longrightarrow> dl_prog.derivable (p, xs)"
  proof (intro allI impI)
    fix p xs assume "Atom (predAtm p xs) \<in> fst (execute_plan_action a M)"
    hence "Atom (predAtm p xs) \<in> L \<or> Atom (predAtm p xs) \<in> set (adds (effect ?a'))"
      unfolding fstM' by auto
    thus "dl_prog.derivable (p, xs)"
    proof
      assume "Atom (predAtm p xs) \<in> L"
      hence "Atom (predAtm p xs) \<in> fst M" using M by simp
      thus ?thesis using Cons.prems(2) by blast
    next
      assume "Atom (predAtm p xs) \<in> set (adds (effect ?a'))"
      thus ?thesis using derivable_step_adds[OF ne en Cons.prems(2)] by blast
    qed
  qed
  show ?case using Cons.IH[OF rest step] .
qed

subsection \<open>The minimal-model relation\<close>

lemma achievable_imp_dl_derivable:
  assumes ne: "const_names \<noteq> []"
    and ach: "achievable f"
  shows "dl_prog.derivable f"
proof -
  obtain \<pi>s M where vp: "valid_classical_plan_alt I \<pi>s M"
    and mem: "Atom (uncurry predAtm f) \<in> fst M"
    using ach
    unfolding achievable_def by auto
  obtain p xs where f: "f = (p, xs)" by (cases f)
  have init: "\<forall>p xs. Atom (predAtm p xs) \<in> fst I
                \<longrightarrow> dl_prog.derivable (p, xs)"
    using derivable_init by blast
  have allM: "\<forall>p xs. Atom (predAtm p xs) \<in> fst M
                \<longrightarrow> dl_prog.derivable (p, xs)"
    using derivable_invariant[OF ne vp init] .
  have "Atom (predAtm p xs) \<in> fst M" using mem f by simp
  hence "dl_prog.derivable (p, xs)" using allM by blast
  thus ?thesis using f by simp
qed

text \<open>An action enabled at \<open>M1\<close> is enabled at any fact-superset \<open>M2\<close>: relaxed (positive
  conjunction) preconditions are monotone, and numeric-freeness makes the two numeric side
  conditions vacuous (no numeric effects).\<close>
lemma enabled_mono:
  assumes en: "plan_action_enabled a M1"
    and sub: "fst M1 \<subseteq> fst M2"
  shows "plan_action_enabled a M2"
proof -
  obtain n args where a_eq: "a = SimplePlanAction n args" by (cases a)
  have wfa: "wf_classical_plan_action (SimplePlanAction n args)" using en
    unfolding a_eq plan_action_enabled_def by (simp add: Let_def)
  have val1: "valuation M1 \<Turnstile>\<^sub>m precondition ((the \<circ> res_inst) a)" using en
    unfolding plan_action_enabled_def by (simp add: Let_def)
  obtain sch where res: "resolve_classical_action_schema n = Some sch" using wfa
    by (auto simp: wf_classical_plan_action_simple split: option.splits)
  have sch_mem: "sch \<in> set (actions D)" using res
    unfolding resolve_classical_action_schema_def by (auto dest: index_by_eq_SomeD)
  have nm: "ac_name sch = n" using res res_aux sch_mem by blast
  obtain n' ps pre ad dl nl where sch_eq0:
      "sch = SimpleActionSchema (ActionHead n' ps) (SimpleActionBody pre (Effect ad dl nl))"
    by (metis ast_classical_action_schema_cases_unfold ast_effect.exhaust)
  have sch_eq: "sch = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl))"
    using sch_eq0 nm by simp
  have schmem': "SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl)) \<in> set (actions D)"
    using sch_mem sch_eq by simp
  have ri: "res_inst (SimplePlanAction n args) = Some (GroundAction
      (map_atom_fmla (ac_tsubst ps args) pre) (map_ast_effect (ac_tsubst ps args) (Effect ad dl nl)))"
    by (rule res_inst_cond[OF schmem'])
  have pre_eq: "precondition ((the \<circ> res_inst) a) = map_atom_fmla (ac_tsubst ps args) pre"
    unfolding a_eq using ri by simp
  have eff_eq: "effect ((the \<circ> res_inst) a) = map_ast_effect (ac_tsubst ps args) (Effect ad dl nl)"
    unfolding a_eq using ri by simp
  have ne0: "numeric_effects (ac_eff sch) = []" using nne sch_mem by blast
  have nl0: "nl = []" using ne0 sch_eq by simp
  have numeff0: "numeric_effects (effect ((the \<circ> res_inst) a)) = []"
    unfolding eff_eq by (simp add: nl0)
  have pos: "is_pos_conj pre"
  proof -
    have "\<forall>a\<in>set (actions D). is_pos_conj (ac_pre a)"
      using relaxed_prob by (auto simp: relaxed_prob_def relaxed_dom_def)
    hence "is_pos_conj (ac_pre sch)" using sch_mem by simp
    thus ?thesis using sch_eq by simp
  qed
  show "plan_action_enabled a M2"
    unfolding plan_action_enabled_def Let_def
  proof (intro conjI)
    show "wf_classical_plan_action a" using wfa unfolding a_eq .
    show "numeric_effects_non_intrf ((the \<circ> res_inst) a)"
      by (rule numeric_effects_non_intrf_no_numeric_effects[OF numeff0])
    show "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ((the \<circ> res_inst) a)))
            \<subseteq> dom (snd M2)"
      using enumerate_rhs_pnes_no_numeric_effects[OF numeff0] by simp
    show "valuation M2 \<Turnstile>\<^sub>m precondition ((the \<circ> res_inst) a)"
      unfolding pre_eq by (rule valuation_pos_conj_mono[OF pos sub val1[unfolded pre_eq]])
  qed
qed

text \<open>A valid plan replays from any fact-superset start state, reaching a fact-superset endpoint.\<close>
lemma plan_replay_mono:
  assumes "valid_classical_plan_alt M1 \<pi>s N1" and "fst M1 \<subseteq> fst M2"
  shows "\<exists>N2. valid_classical_plan_alt M2 \<pi>s N2 \<and> fst N1 \<subseteq> fst N2"
  using assms(1,2)
proof (induction \<pi>s arbitrary: M1 M2)
  case (Nil M1 M2)
  hence "M1 = N1" by simp
  thus ?case using Nil.prems(2) by auto
next
  case (Cons a \<pi>s M1 M2)
  have en1: "plan_action_enabled a M1"
    and rest1: "valid_classical_plan_alt (execute_plan_action a M1) \<pi>s N1" using Cons.prems(1) by simp_all
  have en2: "plan_action_enabled a M2" by (rule enabled_mono[OF en1 Cons.prems(2)])
  have step_sub: "fst (execute_plan_action a M1) \<subseteq> fst (execute_plan_action a M2)"
    unfolding execute_facts_eq[OF en1] execute_facts_eq[OF en2]
    using Cons.prems(2) by blast
  obtain N2
    where v2: "valid_classical_plan_alt (execute_plan_action a M2) \<pi>s N2"
      and sub2: "fst N1 \<subseteq> fst N2" using Cons.IH[OF rest1 step_sub] by blast
  have "valid_classical_plan_alt M2 (a # \<pi>s) N2" using en2 v2 by simp
  thus ?case using sub2 by blast
qed

text \<open>A finite set of individually-achievable facts is jointly achievable: the per-fact plans
  are concatenated, each replayed from the growing state, persistence keeping the earlier facts.\<close>
lemma achievables_reach_common:
  assumes "\<forall>f \<in> set fs. achievable f"
  shows "\<exists>\<pi>s M. valid_classical_plan_alt I \<pi>s M \<and> (\<forall>f \<in> set fs. Atom (uncurry predAtm f) \<in> fst M)"
  using assms(1)
proof (induction fs)
  case Nil
  show ?case by (rule exI[of _ "[]"], rule exI[of _ I], simp)
next
  case (Cons f fs)
  have af: "achievable f"
    and rest: "\<forall>f \<in> set fs. achievable f" using Cons.prems by simp_all
  obtain \<pi>s M
    where vM: "valid_classical_plan_alt I \<pi>s M"
      and fsM: "\<forall>g \<in> set fs. Atom (uncurry predAtm g) \<in> fst M" using Cons.IH[OF rest] by blast
  obtain \<rho>s Mf where
      vMf: "valid_classical_plan_alt I \<rho>s Mf"
      and fMf: "Atom (uncurry predAtm f) \<in> fst Mf"
    using af
    unfolding achievable_def by blast
  have fIM: "fst I \<subseteq> fst M" by (rule plan_grows_facts[OF vM])
  obtain N
    where vN: "valid_classical_plan_alt M \<rho>s N"
      and MfN: "fst Mf \<subseteq> fst N"
    using plan_replay_mono[OF vMf fIM] by blast
  have vIN: "valid_classical_plan_alt I (\<pi>s @ \<rho>s) N"
    using valid_classical_plan_alt_append_intro[OF conjI[OF vM vN]] .
  have fN: "Atom (uncurry predAtm f) \<in> fst N" using fMf MfN by blast
  have "fst M \<subseteq> fst N" by (rule plan_grows_facts[OF vN])
  hence "\<forall>g \<in> set (f # fs). Atom (uncurry predAtm g) \<in> fst N" using fsM fN by auto
  thus ?case using vIN by blast
qed


text \<open>Reverse of \<open>enabled_clause_body\<close>: an action whose translated positive-precondition atom
  instances all hold in \<open>M\<close> and whose equality conditions are satisfied is enabled at \<open>M\<close>. The
  precondition formula is rebuilt from its \<open>un_and\<close> literals (\<open>un_and_map_semantics_rev\<close>); the two
  numeric side conditions are vacuous under \<open>nne\<close>.\<close>
lemma clause_body_enabled:
  assumes sch_mem: "ac \<in> set (actions D)" and sch_name: "ac_name ac = n"
    and pm: "action_params_match (ac_head ac) args"
    and pos: "set (map (map_atom_fmla (ac_tsubst (cl_params (as_action_clause ac)) args))
                 (cl_pred_pre (as_action_clause ac))) \<subseteq> fst M"
    and sat: "satisfies_conds (cl_params (as_action_clause ac))
                 (cl_cond_pre (as_action_clause ac)) args"
  shows "plan_action_enabled (SimplePlanAction n args) M"
proof -
  obtain n' ps pre ad dl nl where sch_eq0:
      "ac = SimpleActionSchema (ActionHead n' ps) (SimpleActionBody pre (Effect ad dl nl))"
    by (metis ast_classical_action_schema_cases_unfold ast_effect.exhaust)
  have nm: "n' = n" using sch_name sch_eq0 by simp
  have ac_eq: "ac = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl))"
    using sch_eq0 nm by simp
  have cl_params: "cl_params (as_action_clause ac) = ps" using ac_eq by simp
  have cl_pred: "cl_pred_pre (as_action_clause ac) = pos_lits_of pre" using ac_eq by simp
  have cl_cond: "cl_cond_pre (as_action_clause ac) = cond_lits_of pre" using ac_eq by simp
  let ?a' = "(the \<circ> res_inst) (SimplePlanAction n args)"
  have res: "res_inst (SimplePlanAction n args)
              = Some (GroundAction (map_atom_fmla (ac_tsubst ps args) pre)
                                   (map_ast_effect (ac_tsubst ps args) (Effect ad dl nl)))"
    using res_inst_cond[OF sch_mem[unfolded ac_eq]] .
  have pre_eq: "precondition ?a' = map_atom_fmla (ac_tsubst ps args) pre" using res by simp
  have eff_eq: "effect ?a' = map_ast_effect (ac_tsubst ps args) (Effect ad dl nl)"
    using res by simp
  have ne0: "numeric_effects (ac_eff ac) = []" using nne sch_mem by blast
  have nl0: "nl = []" using ne0 ac_eq by simp
  have numeff0: "numeric_effects (effect ?a') = []" unfolding eff_eq by (simp add: nl0)
  have pos_conj: "is_pos_conj pre"
  proof -
    have "\<forall>a\<in>set (actions D). is_pos_conj (ac_pre a)"
      using relaxed_prob by (auto simp: relaxed_prob_def relaxed_dom_def)
    hence "is_pos_conj (ac_pre ac)" using sch_mem by simp
    thus ?thesis using ac_eq by simp
  qed
  have val_pre: "valuation M \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) pre"
  proof (rule un_and_map_semantics_rev, unfold un_and_map_atom_fmla, rule ballI)
    fix g assume "g \<in> set (map (map_atom_fmla (ac_tsubst ps args)) (un_and pre))"
    then obtain l where l: "l \<in> set (un_and pre)"
      and g: "g = map_atom_fmla (ac_tsubst ps args) l" by auto
    show "valuation M \<Turnstile>\<^sub>m g" unfolding g
    proof (cases "is_predAtom l")
      case True
      hence l_pos: "l \<in> set (pos_lits_of pre)" using l by (simp add: pos_lits_of_def)
      then obtain p xs where l_eq: "l = Atom (predAtm p xs)"
        using True by (cases l rule: is_predAtom.cases) auto
      have "map_atom_fmla (ac_tsubst ps args) l
              \<in> set (map (map_atom_fmla (ac_tsubst ps args)) (cl_pred_pre (as_action_clause ac)))"
        using l_pos cl_pred by auto
      hence "map_atom_fmla (ac_tsubst ps args) l \<in> fst M" using pos cl_params by auto
      thus "valuation M \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) l"
        unfolding l_eq by (simp add: valuation_def)
    next
      case False
      hence l_cond: "l \<in> set (cond_lits_of pre)" using l by (simp add: cond_lits_of_def)
      have posl: "is_pos_lit l" using pos_conj l is_pos_conj_alt by blast
      have "satisfies_cond ps args l"
        using sat l_cond cl_cond cl_params by (simp add: list_all_iff)
      hence "valuation ({}, Map.empty) \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) l" by simp
      thus "valuation M \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) l"
        using cond_lit_model_indep[OF posl False] by blast
    qed
  qed
  have wf: "wf_classical_plan_action (SimplePlanAction n args)"
    using wf_classical_plan_action_cond[OF sch_mem sch_name] pm by simp
  show ?thesis
    unfolding plan_action_enabled_def Let_def
  proof (intro conjI)
    show "wf_classical_plan_action (SimplePlanAction n args)" using wf .
    show "numeric_effects_non_intrf ?a'"
      by (rule numeric_effects_non_intrf_no_numeric_effects[OF numeff0])
    show "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect ?a')) \<subseteq> dom (snd M)"
      using enumerate_rhs_pnes_no_numeric_effects[OF numeff0] by simp
    show "valuation M \<Turnstile>\<^sub>m precondition ?a'" unfolding pre_eq using val_pre .
  qed
qed

text \<open>Firing one action clause: if its translated argument tuple is well-typed, every
  positive-precondition atom instance is achievable, and its equality conditions hold, then every
  add-effect of the clause is achievable. The individually-achievable body facts are merged into a
  common reachable state (\<open>achievables_reach_common\<close>), at which the action is enabled
  (\<open>clause_body_enabled\<close>); firing it once produces the add-effect (\<open>execute_facts_eq\<close>,
  \<open>res_inst_adds_eq_consequence\<close>).\<close>
lemma fire_clause_achievable:
  assumes cl_mem: "cl_ac \<in> set a_clauses"
    and pm: "action_params_match (ActionHead (cl_name cl_ac) (cl_params cl_ac)) args"
    and ach: "\<And>p xs. Atom (predAtm p xs) \<in> set (cl_pred_pre cl_ac)
                \<Longrightarrow> achievable (p, map (ac_tsubst (cl_params cl_ac) args) xs)"
    and sat: "satisfies_conds (cl_params cl_ac) (cl_cond_pre cl_ac) args"
    and head: "Atom (predAtm p0 ts0) \<in> set (cl_pos cl_ac)"
  shows "achievable (p0, map (ac_tsubst (cl_params cl_ac) args) ts0)"
proof -
  obtain sch where sch_mem: "sch \<in> set (actions D)"
    and cl_eq: "cl_ac = as_action_clause sch" using cl_mem unfolding a_clauses_def by auto
  obtain n ps pre ad dl nl where sch_eq:
      "sch = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl))"
    by (metis ast_classical_action_schema_cases_unfold ast_effect.exhaust)
  have cl_eq': "cl_ac = AClause n ps (pos_lits_of pre) (cond_lits_of pre) ad"
    using cl_eq sch_eq by simp
  have cl_name: "cl_name cl_ac = n"
    and cl_params: "cl_params cl_ac = ps"
    and cl_pos: "cl_pos cl_ac = ad"
    and cl_pred: "cl_pred_pre cl_ac = pos_lits_of pre"
    using cl_eq' by simp_all
  have sch_name: "ac_name sch = n" using sch_eq by simp
  have head_eq: "ac_head sch = ActionHead n ps" using sch_eq by simp
  have pm': "action_params_match (ac_head sch) args"
    using pm cl_name cl_params head_eq by simp
  have pred: "is_predAtom b" if "b \<in> set (cl_pred_pre cl_ac)" for b
    using that cl_pred by (auto simp: pos_lits_of_def)
  define fs where "fs = map (\<lambda>b. case b of Atom (predAtm p xs) \<Rightarrow> (p, map (ac_tsubst ps args) xs))
                            (cl_pred_pre cl_ac)"
  have achfs: "\<forall>f \<in> set fs. achievable f"
  proof
    fix f assume "f \<in> set fs"
    then obtain b where b: "b \<in> set (cl_pred_pre cl_ac)"
      and f_eq: "f = (case b of Atom (predAtm p xs) \<Rightarrow> (p, map (ac_tsubst ps args) xs))"
      unfolding fs_def by (auto simp del: ac_tsubst_def)
    obtain p xs where b_eq: "b = Atom (predAtm p xs)" using pred[OF b]
      by (cases b rule: is_predAtom.cases) auto
    have "achievable (p, map (ac_tsubst (cl_params cl_ac) args) xs)"
      using ach b b_eq by auto
    hence "achievable (p, map (ac_tsubst ps args) xs)" by (simp add: cl_params)
    thus "achievable f" using f_eq b_eq by simp
  qed
  obtain \<pi>s Mstar
    where vM: "valid_classical_plan_alt I \<pi>s Mstar"
      and fsM: "\<forall>f \<in> set fs. Atom (uncurry predAtm f) \<in> fst Mstar" using achievables_reach_common[OF achfs] by blast
  have pos: "set (map (map_atom_fmla (ac_tsubst ps args)) (cl_pred_pre cl_ac)) \<subseteq> fst Mstar"
  proof
    fix x assume "x \<in> set (map (map_atom_fmla (ac_tsubst ps args)) (cl_pred_pre cl_ac))"
    then obtain b where b: "b \<in> set (cl_pred_pre cl_ac)"
      and x: "x = map_atom_fmla (ac_tsubst ps args) b" by auto
    obtain p xs where b_eq: "b = Atom (predAtm p xs)" using pred[OF b]
      by (cases b rule: is_predAtom.cases) auto
    have "(p, map (ac_tsubst ps args) xs) \<in> set fs" unfolding fs_def using b b_eq by force
    hence "Atom (uncurry predAtm (p, map (ac_tsubst ps args) xs)) \<in> fst Mstar" using fsM by blast
    moreover
    have "x = Atom (uncurry predAtm (p, map (ac_tsubst ps args) xs))"
      using x b_eq by (simp add: uncurry_def)
    ultimately
    show "x \<in> fst Mstar" by simp
  qed
  let ?pa = "SimplePlanAction n args"
  have en: "plan_action_enabled ?pa Mstar"
  proof (rule clause_body_enabled[OF sch_mem sch_name pm'])
    show "set (map (map_atom_fmla (ac_tsubst (cl_params (as_action_clause sch)) args))
                 (cl_pred_pre (as_action_clause sch))) \<subseteq> fst Mstar"
      using pos by (simp add: cl_eq[symmetric] cl_params)
    show "satisfies_conds (cl_params (as_action_clause sch))
            (cl_cond_pre (as_action_clause sch)) args"
      using sat by (simp add: cl_eq[symmetric])
  qed
  have fire: "valid_classical_plan_alt Mstar [?pa] (execute_plan_action ?pa Mstar)"
    using en by (simp add: plan_action_enabled_def execute_plan_action_def)
  have valid_full: "valid_classical_plan_alt I (\<pi>s @ [?pa]) (execute_plan_action ?pa Mstar)"
    using valid_classical_plan_alt_append_intro[OF conjI[OF vM fire]] .
  have adds_eq: "adds (effect ((the \<circ> res_inst) ?pa)) = consequence_of cl_ac args"
    using res_inst_adds_eq_consequence[OF sch_mem[unfolded sch_eq]]
    by (simp add: cl_eq sch_eq comp_def)
  have conseq: "consequence_of cl_ac args = map (map_atom_fmla (ac_tsubst ps args)) (cl_pos cl_ac)"
    using cl_eq' cl_pos by simp
  have headmem: "Atom (predAtm p0 (map (ac_tsubst ps args) ts0))
                   \<in> set (adds (effect ((the \<circ> res_inst) ?pa)))"
  proof -
    have "map_atom_fmla (ac_tsubst ps args) (Atom (predAtm p0 ts0)) \<in> set (consequence_of cl_ac args)"
      unfolding conseq using head
      by (auto simp del: ac_tsubst_def simp add: image_iff
               intro!: bexI[where x="Atom (predAtm p0 ts0)"])
    thus ?thesis unfolding adds_eq by simp
  qed
  have memN: "Atom (predAtm p0 (map (ac_tsubst ps args) ts0)) \<in> fst (execute_plan_action ?pa Mstar)"
    using headmem execute_facts_eq[OF en] by auto
  have "achievable (p0, map (ac_tsubst ps args) ts0)"
    unfolding achievable_def
    by (rule exI[of _ "\<pi>s @ [?pa]"], rule exI[of _ "execute_plan_action ?pa Mstar"])
       (use valid_full memN in \<open>simp add: uncurry_def\<close>)
  thus ?thesis using cl_params by simp
qed

text \<open>Every fact of \<^const>\<open>init'\<close> is achievable. A fact of \<^term>\<open>init P\<close> holds at the initial
  state (\<open>init_achievable\<close>); a fact of \<^const>\<open>pseudo_init\<close> is the add-effect of a bodyless fact
  clause fired at condition-satisfying object arguments --- the empty-body special case of
  \<open>fire_clause_achievable\<close>.\<close>
lemma init'_achievable:
  assumes ne: "const_names \<noteq> []"
    and mem: "Atom (predAtm p xs) \<in> set init'"
  shows "achievable (p, xs)"
proof -
  have "Atom (predAtm p xs) \<in> set pseudo_init \<or> Atom (predAtm p xs) \<in> set (init P)" using mem
    unfolding init'_def conc_unique_un by simp
  thus ?thesis
  proof
    assume "Atom (predAtm p xs) \<in> set (init P)"
    thus ?thesis by (rule init_achievable)
  next
    assume "Atom (predAtm p xs) \<in> set pseudo_init"
    then obtain cl_ac where cl_fc: "cl_ac \<in> set fact_clauses"
      and inafc: "Atom (predAtm p xs) \<in> set (all_fact_consqs cl_ac)"
      unfolding pseudo_init_def by auto
    then obtain args where args: "args \<in> set (all_fact_paramz cl_ac)"
      and inconseq: "Atom (predAtm p xs) \<in> set (consequence_of cl_ac args)"
      using inafc by auto
    have cl_mem: "cl_ac \<in> set a_clauses" using cl_fc unfolding fact_clauses_def by simp
    have cl_pred_empty: "cl_pred_pre cl_ac = []" using cl_fc unfolding fact_clauses_def by simp
    obtain sch where sch_mem: "sch \<in> set (actions D)"
      and cl_eq: "cl_ac = as_action_clause sch" using cl_mem unfolding a_clauses_def by auto
    obtain n ps pre ad dl nl where sch_eq:
        "sch = SimpleActionSchema (ActionHead n ps) (SimpleActionBody pre (Effect ad dl nl))"
      by (metis ast_classical_action_schema_cases_unfold ast_effect.exhaust)
    have cl_eq': "cl_ac = AClause n ps (pos_lits_of pre) (cond_lits_of pre) ad"
      using cl_eq sch_eq by simp
    have cl_name: "cl_name cl_ac = n"
      and cl_params: "cl_params cl_ac = ps"
      and cl_cond: "cl_cond_pre cl_ac = cond_lits_of pre"
      and cl_pos: "cl_pos cl_ac = ad"
      using cl_eq' by simp_all
    have fp: "all_fact_paramz cl_ac
                = all_combos (satisfies_conds ps (cond_lits_of pre)) (replicate (length ps) const_names)"
      using cl_eq' by simp
    have chosen: "chosen_from (replicate (length ps) const_names) args"
      and satp: "satisfies_conds ps (cond_lits_of pre) args"
      using args fp by (auto simp: set_all_combos)
    have lenargs: "length args = length ps"
      and inc: "\<forall>x \<in> set args. x \<in> set const_names" using chosen_from_replicate_dest[OF chosen] by auto
    have pm: "action_params_match (ActionHead (cl_name cl_ac) (cl_params cl_ac)) args"
    proof -
      have "action_params_match (ac_head sch) args"
      proof (rule params_match_from_const_args[OF sch_mem])
        show "length args = length (ac_params sch)" using lenargs sch_eq by simp
        show "\<And>x. x \<in> set args \<Longrightarrow> x \<in> set const_names" using inc by blast
      qed
      thus ?thesis using cl_name cl_params sch_eq by simp
    qed
    have sat: "satisfies_conds (cl_params cl_ac) (cl_cond_pre cl_ac) args"
      using satp cl_params cl_cond by simp
    have conseq: "consequence_of cl_ac args = map (map_atom_fmla (ac_tsubst ps args)) (cl_pos cl_ac)"
      using cl_eq' cl_pos by simp
    have "Atom (predAtm p xs) \<in> set (map (map_atom_fmla (ac_tsubst ps args)) (cl_pos cl_ac))"
      using inconseq conseq by simp
    then obtain f0 where f0: "f0 \<in> set (cl_pos cl_ac)"
      and f0eq: "Atom (predAtm p xs) = map_atom_fmla (ac_tsubst ps args) f0" by auto
    have "is_predAtom f0" using dl_bridge_wf_posD[OF bridge[OF ne] cl_mem] f0 by blast
    then obtain p0 ts0 where f0_pred: "f0 = Atom (predAtm p0 ts0)"
      by (cases f0 rule: is_predAtom.cases) auto
    have pxs: "p = p0 \<and> xs = map (ac_tsubst ps args) ts0" using f0eq f0_pred by simp
    have head: "Atom (predAtm p0 ts0) \<in> set (cl_pos cl_ac)" using f0 f0_pred by simp
    have ach: "achievable (p', map (ac_tsubst (cl_params cl_ac) args) xs')"
      if "Atom (predAtm p' xs') \<in> set (cl_pred_pre cl_ac)" for p' xs'
      using that cl_pred_empty by simp
    have "achievable (p0, map (ac_tsubst (cl_params cl_ac) args) ts0)"
      by (rule fire_clause_achievable[OF cl_mem pm ach sat head])
    thus ?thesis using pxs cl_params by simp
  qed
qed

text \<open>Inverting \<^const>\<open>dl_clauses_of_action_clause\<close>: a clause it produces has a predicate-atom add
  effect as head and the translated precondition/condition body, and no literal failed to translate
  (else the clause list would be empty). Dual to \<open>dl_clause_of_pos_mem\<close>.\<close>
lemma dl_clause_of_action_clause_dest:
  assumes "cl \<in> set (dl_clauses_of_action_clause cl_ac)"
  obtains p ts where
      "Atom (predAtm p ts) \<in> set (cl_pos cl_ac)"
      "None \<notin> set (map dl_cond_rh (cl_cond_pre cl_ac))"
      "None \<notin> set (map dl_pos_rh (cl_pred_pre cl_ac))"
      "cl = Cls p (map dl_id_of_term ts) (dl_clause_body cl_ac)"
proof -
  let ?conds = "map dl_cond_rh (cl_cond_pre cl_ac)"
  let ?pres = "map dl_pos_rh (cl_pred_pre cl_ac)"
  let ?body = "dl_clause_body cl_ac"
  have nN1: "None \<notin> set ?conds"
    and nN2: "None \<notin> set ?pres"
  proof -
    have "\<not> (None \<in> set ?conds \<or> None \<in> set ?pres)"
    proof
      assume "None \<in> set ?conds \<or> None \<in> set ?pres"
      hence "dl_clauses_of_action_clause cl_ac = []"
        unfolding dl_clauses_of_action_clause_def Let_def by auto
      thus False using assms by simp
    qed
    thus "None \<notin> set ?conds" "None \<notin> set ?pres" by auto
  qed
  obtain f where f: "f \<in> set (cl_pos cl_ac)"
    and fc: "(case f of Atom (predAtm p ts) \<Rightarrow> Some (Cls p (map dl_id_of_term ts) ?body) | _ \<Rightarrow> None)
               = Some cl"
    using assms nN1 nN2
    unfolding dl_clauses_of_action_clause_def Let_def
    by (auto simp add: set_map_filter' simp del: map_map split: if_split_asm)
  obtain p ts where "f = Atom (predAtm p ts)"
    and "cl = Cls p (map dl_id_of_term ts) ?body"
    using fc
    by (auto split: formula.splits atom.splits)
  thus ?thesis using f nN1 nN2 that by blast
qed

text \<open>Reverse of \<open>dl_cond_rh_eval_guard\<close>: a translated condition is satisfied (in the empty model)
  whenever it is a drop-marker (\<open>Some None\<close>) or its equality guard holds under the
  argument substitution.\<close>
lemma dl_cond_rh_satisfies:
  assumes nN: "dl_cond_rh cnd \<noteq> None"
    and gd: "\<And>g. dl_cond_rh cnd = Some (Some g)
               \<Longrightarrow> eval_guard (\<lambda>v. ac_tsubst ps args (term.VAR v)) g"
  shows "satisfies_cond ps args cnd"
  using assms
  by (cases cnd rule: dl_cond_rh.cases)
     (auto simp del: ac_tsubst_def simp add: valuation_def subst_id_dl_id_term)

text \<open>The equality-guard conditions of an action clause are satisfied whenever: no condition
  maps to \<open>None\<close> (i.e.\ the clause has no unconditional drops), the RHS of the datalog clause
  equals the clause body, every guard evaluates under \<open>\<sigma>\<close>, and \<open>\<sigma>\<close> agrees with the
  argument substitution on the clause variables.\<close>
lemma satisfies_conds_of_guards:
  assumes nc: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl_ac))"
    and rhs_eq: "the_rhs cl = dl_clause_body cl_ac"
    and guards: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
    and agree: "\<forall>x \<in> set (cls_vars cl). ac_tsubst ps args (term.VAR x) = \<sigma> x"
  shows "satisfies_conds ps (cl_cond_pre cl_ac) args"
  unfolding list_all_iff
proof
  fix cnd assume cnd: "cnd \<in> set (cl_cond_pre cl_ac)"
  show "satisfies_cond ps args cnd"
  proof (rule dl_cond_rh_satisfies)
    show "dl_cond_rh cnd \<noteq> None"
    proof
      assume "dl_cond_rh cnd = None"
      hence "None \<in> set (map dl_cond_rh (cl_cond_pre cl_ac))" using cnd by force
      thus False using nc by simp
    qed
  next
    fix g assume g: "dl_cond_rh cnd = Some (Some g)"
    have "Some g \<in> set (map the (map dl_cond_rh (cl_cond_pre cl_ac)))"
      using cnd g by force
    hence "g \<in> set (List.map_filter id (map the (map dl_cond_rh (cl_cond_pre cl_ac))))"
      by (auto simp: set_map_filter')
    hence g_rhs: "g \<in> set (the_rhs cl)" using rhs_eq by (simp add: dl_clause_body_def)
    have "is_dl_guard g" using g by (cases cnd rule: dl_cond_rh.cases) auto
    hence g_grd: "g \<in> set (cls_guards cl)" using g_rhs by (simp add: cls_guards_def)
    have ev: "eval_guard \<sigma> g" using guards g_grd by blast
    have "\<forall>x \<in> set (rh_vars_list g). \<sigma> x = (\<lambda>v. ac_tsubst ps args (term.VAR v)) x"
    proof
      fix x assume xr: "x \<in> set (rh_vars_list g)"
      have xcv: "x \<in> set (cls_vars cl)" using cls_vars_rhs_vars[OF g_rhs] xr by blast
      show "\<sigma> x = (\<lambda>v. ac_tsubst ps args (term.VAR v)) x"
        using agree xcv by (simp del: ac_tsubst_def)
    qed
    hence "eval_guard \<sigma> g = eval_guard (\<lambda>v. ac_tsubst ps args (term.VAR v)) g"
      by (rule eval_guard_agree)
    thus "eval_guard (\<lambda>v. ac_tsubst ps args (term.VAR v)) g" using ev by simp
  qed
qed

text \<open>Tightness / \<open>\<supseteq>\<close>: every fact of the minimal model is PDDL-achievable. Rule induction on
  \<^const>\<open>datalog_prog.derivable\<close>. A derivation step fires a clause of \<^const>\<open>dl_rules\<close>: a
  translated action clause (fire that action via \<open>fire_clause_achievable\<close>; its body-atom instances
  are achievable by the IH, its equality guards give the conditions, and the argument tuple is
  reconstructed from the generic substitution \<open>\<sigma>\<close>) or a bodyless fact clause from
  \<^const>\<open>init'\<close> (\<open>init'_achievable\<close>). Needs the delete-relaxation / numeric-freeness hypotheses
  \<open>nne\<close> / \<open>nd\<close> that \<open>fire_clause_achievable\<close> and that people \<open>init'_achievable\<close> carry.\<close>
text \<open>If every body atom of a datalog clause \<open>cl\<close> is achievable under substitution \<open>\<sigma>\<close>, and
  \<open>\<sigma>\<close> agrees with the argument substitution \<open>ac_tsubst ps args\<close> on the clause variables (captured
  via \<open>subst_eq\<close>), then every positive-predicate precondition of the corresponding action clause
  \<open>cl_ac\<close> is achievable under \<open>ac_tsubst (cl_params cl_ac) args\<close>.  This is the inner step
  extracted from the action branch of \<open>dl_derivable_imp_achievable\<close>.\<close>
lemma ach_of_pred_pre:
  assumes np: "None \<notin> set (map dl_pos_rh (cl_pred_pre cl_ac))"
    and rhs_eq: "the_rhs cl = dl_clause_body cl_ac"
    and subst_eq: "\<And>t. (\<And>v. t = term.VAR v \<Longrightarrow> v \<in> set (cls_vars cl))
                     \<Longrightarrow> subst_id \<sigma> (dl_id_of_term t) = ac_tsubst ps args t"
    and IH: "\<And>a. a \<in> set (cls_body_atoms cl) \<Longrightarrow> achievable (subst_atom \<sigma> a)"
    and cl_params: "cl_params cl_ac = ps"
    and pre': "Atom (predAtm p' xs') \<in> set (cl_pred_pre cl_ac)"
  shows "achievable (p', map (ac_tsubst (cl_params cl_ac) args) xs')"
proof -
  have rh_mem: "PosLit p' (map dl_id_of_term xs') \<in> set (the_rhs cl)"
  proof -
    have "the (dl_pos_rh (Atom (predAtm p' xs')))
            \<in> set (map the (map dl_pos_rh (cl_pred_pre cl_ac)))" using pre' by force
    thus ?thesis using rhs_eq by (simp add: dl_clause_body_def)
  qed
  hence body_mem: "(p', map dl_id_of_term xs') \<in> set (cls_body_atoms cl)"
    by (simp add: cls_body_atoms_iff)
  have body_vars: "v \<in> set (cls_vars cl)" if tv: "t \<in> set xs'" "t = term.VAR v" for t v
  proof -
    have "term.VAR v \<in> set xs'" using tv by simp
    hence "v \<in> set (rh_vars_list (PosLit p' (map dl_id_of_term xs')))" by force
    thus ?thesis using cls_vars_rhs_vars[OF rh_mem] by blast
  qed
  have "map (subst_id \<sigma>) (map dl_id_of_term xs') = map (ac_tsubst ps args) xs'"
  proof (subst map_map, rule map_cong[OF refl])
    fix t assume "t \<in> set xs'"
    thus "(subst_id \<sigma> \<circ> dl_id_of_term) t = ac_tsubst ps args t"
      using subst_eq[OF body_vars[OF \<open>t \<in> set xs'\<close>]] by (simp del: ac_tsubst_def)
  qed
  hence "subst_atom \<sigma> (p', map dl_id_of_term xs') = (p', map (ac_tsubst ps args) xs')"
    unfolding subst_atom_def by simp
  moreover
  have "achievable (subst_atom \<sigma> (p', map dl_id_of_term xs'))"
    using IH body_mem by blast
  ultimately
  show ?thesis using cl_params by simp
qed

lemma dl_derivable_imp_achievable:
  assumes ne: "const_names \<noteq> []"
    and der: "dl_prog.derivable f"
  shows "achievable f"
proof -
  note ind = dl_prog.derivable.induct[consumes 1, case_names step]
  show ?thesis using der
  proof (induction rule: ind)
    case (step cl \<sigma>)
    consider
        (act) cl_ac where "cl_ac \<in> set a_clauses" "cl \<in> set (dl_clauses_of_action_clause cl_ac)"
      | (fct) "cl \<in> set (List.map_filter dl_fact_clause init')"
      using step.hyps(1)
      unfolding dl_rules_def by auto
    thus ?case
    proof cases
      case (act cl_ac)
      obtain p0 ts0 where
          head: "Atom (predAtm p0 ts0) \<in> set (cl_pos cl_ac)"
          and nc: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl_ac))"
          and np: "None \<notin> set (map dl_pos_rh (cl_pred_pre cl_ac))"
          and cl_eq: "cl = Cls p0 (map dl_id_of_term ts0) (dl_clause_body cl_ac)"
          using dl_clause_of_action_clause_dest[OF act(2)] .
      obtain sch where
        sch_mem: "sch \<in> set (actions D)"
        and cl_eq2: "cl_ac = as_action_clause sch"
        using act(1) unfolding a_clauses_def by auto
      obtain nm ps pre ad dl' nl where sch_eq:
          "sch = SimpleActionSchema (ActionHead nm ps) (SimpleActionBody pre (Effect ad dl' nl))"
        by (metis ast_classical_action_schema_cases_unfold ast_effect.exhaust)
      have cl_params: "cl_params cl_ac = ps"
        and cl_name: "cl_name cl_ac = nm"
        using cl_eq2 sch_eq by simp_all
      have "wf_classical_action_schema sch" using wf_D(3) sch_mem by blast
      hence "distinct (map fst (ac_params sch))" using wf_classical_action_schema_alt by blast
      hence dist: "distinct (map fst ps)" using sch_eq by simp
      have cn_ne: "const_names \<noteq> []" using ne .
      define c0 where "c0 = hd const_names"
      have c0_mem: "c0 \<in> set const_names" unfolding c0_def by (rule hd_in_set[OF cn_ne])
      define args where
        "args = map (\<lambda>vp. if fst vp \<in> set (cls_vars cl) then \<sigma> (fst vp) else c0) ps"
      have lenargs: "length args = length ps" unfolding args_def by simp
      have varsub: "set (cls_vars cl) \<subseteq> set (map fst ps)"
        using dl_bridge_wf_varsD[OF bridge[OF ne] act(1) act(2)] cl_params by simp
      have agree: "ac_tsubst ps args (term.VAR x) = \<sigma> x" if x: "x \<in> set (cls_vars cl)" for x
      proof -
        have "x \<in> set (map fst ps)" using x varsub by auto
        then obtain i where
          i: "i < length ps"
          and xi: "map fst ps ! i = x"
          by (auto simp: in_set_conv_nth)
        have psi: "ps ! i = (x, snd (ps ! i))" using xi i by (cases "ps ! i") auto
        have fstx: "fst (ps ! i) = x" using xi i by simp
        have ai: "args ! i = \<sigma> x" unfolding args_def using i fstx x by simp
        have il: "i < length args" using i lenargs by simp
        show ?thesis by (rule ac_tsubst_intro[OF dist psi ai i il])
      qed
      have subst_eq: "subst_id \<sigma> (dl_id_of_term t) = ac_tsubst ps args t"
        if "\<And>v. t = term.VAR v \<Longrightarrow> v \<in> set (cls_vars cl)" for t
      proof (cases t)
        case (VAR v)
        hence hv: "v \<in> set (cls_vars cl)" using that by simp
        show ?thesis unfolding VAR using agree[OF hv] by (simp del: ac_tsubst_def)
      next
        case (CONST c)
        thus ?thesis by simp
      qed
      have args_const: "a \<in> set const_names" if "a \<in> set args" for a
      proof -
        have a_in: "a \<in> set (map (\<lambda>vp. if fst vp \<in> set (cls_vars cl) then \<sigma> (fst vp) else c0) ps)"
          using that unfolding args_def .
        obtain vp where vp: "vp \<in> set ps"
          and a_eq: "a = (if fst vp \<in> set (cls_vars cl) then \<sigma> (fst vp) else c0)"
          using a_in by auto
        show ?thesis
        proof (cases "fst vp \<in> set (cls_vars cl)")
          case True
          hence "a = \<sigma> (fst vp)" using a_eq by simp
          thus ?thesis using step.hyps(2) True by auto
        next
          case False
          thus ?thesis using a_eq c0_mem by simp
        qed
      qed
      have head_vars: "v \<in> set (cls_vars cl)" if "t \<in> set ts0" "t = term.VAR v" for t v
      proof -
        have "dl_id_of_term t \<in> set (snd (the_lh cl))" using that(1) by (simp add: cl_eq)
        moreover
        have "v \<in> set (id_vars_list (dl_id_of_term t))" using that(2) by simp
        ultimately
        show ?thesis by (rule cls_vars_head_vars)
      qed
      have lh_eq: "subst_atom \<sigma> (the_lh cl) = (p0, map (ac_tsubst ps args) ts0)"
      proof -
        have "map (subst_id \<sigma>) (map dl_id_of_term ts0) = map (ac_tsubst ps args) ts0"
        proof (subst map_map, rule map_cong[OF refl])
          fix t assume "t \<in> set ts0"
          thus "(subst_id \<sigma> \<circ> dl_id_of_term) t = ac_tsubst ps args t"
            using subst_eq[OF head_vars[OF \<open>t \<in> set ts0\<close>]] by (simp del: ac_tsubst_def)
        qed
        thus ?thesis unfolding cl_eq subst_atom_def by (simp del: ac_tsubst_def)
      qed
      have pmh: "action_params_match (ac_head sch) args"
      proof (rule params_match_from_const_args[OF sch_mem])
        show "length args = length (ac_params sch)" using lenargs sch_eq by simp
        show "\<And>a. a \<in> set args \<Longrightarrow> a \<in> set const_names" using args_const by blast
      qed
      have pm: "action_params_match (ActionHead (cl_name cl_ac) (cl_params cl_ac)) args"
        using pmh sch_eq cl_name cl_params by simp
      have rhs_eq': "the_rhs cl = dl_clause_body cl_ac" using cl_eq by simp
      have IH': "\<And>a. a \<in> set (cls_body_atoms cl) \<Longrightarrow> achievable (subst_atom \<sigma> a)"
        using step.IH by blast
      have ach: "achievable (p', map (ac_tsubst (cl_params cl_ac) args) xs')"
        if pre': "Atom (predAtm p' xs') \<in> set (cl_pred_pre cl_ac)" for p' xs'
        using ach_of_pred_pre[OF np rhs_eq' subst_eq IH' cl_params pre'] .
      have agree': "\<forall>x \<in> set (cls_vars cl). ac_tsubst ps args (term.VAR x) = \<sigma> x"
        using agree by blast
      have sat: "satisfies_conds (cl_params cl_ac) (cl_cond_pre cl_ac) args"
        unfolding cl_params
        using satisfies_conds_of_guards[OF nc rhs_eq' step.hyps(3) agree'] .
      have "achievable (p0, map (ac_tsubst (cl_params cl_ac) args) ts0)"
        by (rule fire_clause_achievable[OF act(1) pm ach sat head])
      thus "achievable (subst_atom \<sigma> (the_lh cl))" using lh_eq cl_params by simp
    next
      case fct
      then obtain f0 where
        f0: "f0 \<in> set init'"
        and dfc: "dl_fact_clause f0 = Some cl"
        unfolding set_map_filter' by auto
      obtain pp xs where
        f0_eq: "f0 = Atom (predAtm pp xs)"
        and cl_eq: "cl = Cls pp (map id.Cst xs) []"
        using dfc
        by (cases f0 rule: dl_fact_clause.cases) auto
      have "Atom (predAtm pp xs) \<in> set init'" using f0 f0_eq by simp
      hence "achievable (pp, xs)" by (rule init'_achievable[OF ne])
      moreover
      have "subst_atom \<sigma> (the_lh cl) = (pp, xs)"
        unfolding cl_eq subst_atom_def by (simp add: comp_def)
      ultimately
      show "achievable (subst_atom \<sigma> (the_lh cl))" by simp
    qed
  qed
qed

text \<open>PDDL reachability is exactly the minimal datalog model: \<open>\<subseteq>\<close> (soundness) is unconditional,
  \<open>\<supseteq>\<close> (tightness) needs the delete-relaxation / numeric-freeness hypotheses \<open>nne\<close> / \<open>nd\<close>.\<close>
theorem achievable_eq_minimal_model:
  assumes ne: "const_names \<noteq> []"
  shows "{f. achievable f} = {f. dl_prog.derivable f}"
  using achievable_imp_dl_derivable[OF ne] dl_derivable_imp_achievable[OF ne] by blast

end

end
