theory Reachability_Certificate
  imports Reachability_Analysis Grounded_PDDL.Grounded_PDDL
    Datalog_Certification.Datalog_Certificate
begin

text \<open>\<^theory>\<open>Stratified_Datalog.Datalog\<close>'s \<^typ>\<open>('x, 'c) id\<close> constructors would otherwise capture
  the unqualified \<open>Var\<close> of PDDL \<^typ>\<open>variable\<close> in every downstream theory; we only ever use them
  qualified (\<^const>\<open>id.Var\<close> / \<^const>\<open>id.Cst\<close>).\<close>
hide_const (open) Datalog.id.Var Datalog.id.Cst

section \<open>Reachability via a verified datalog certificate (Nemo proof certificate)\<close>

text \<open>
  This theory replaces the unverified \<open>ast_classical_problem.semi_naive_eval\<close>
  reachability (whose correctness theorems \<open>found_facts_achievable\<close> /
  \<open>found_pactions_applicable\<close> in theory \<open>Reachability_Analysis\<close> are still \<^bold>\<open>sorry\<close>)
  with a \<^emph>\<open>certificate-checking\<close> approach:

  \<^item> an (untrusted) engine --- here \<^bold>\<open>Nemo\<close> --- produces a certificate: the reachable facts,
    each tagged with the predecessor facts that derive it and an implicit derivation rank;
  \<^item> a verified kernel re-checks that the certificate is \<^emph>\<open>admissible\<close> (closed under one-step
    derivation, ordered, and locally valid);
  \<^item> only an admissible certificate is fed to \<^locale>\<open>wf_grounder\<close>.

  The certificate format is Nemo's \<^emph>\<open>ordered graph\<close> (\<open>ograph\<close>); the design notes live in
  \<open>ARCHITECTURE_datalog_certification.md\<close> (repo root), with the Lean 4 \<open>CertifyingDatalog\<close>
  development as the reference checker.

  Key asymmetry that \<^locale>\<open>wf_grounder\<close> exploits:
  \<^item> \<^bold>\<open>closure check = soundness (\<supseteq>)\<close>: the certificate facts form a model of the
    immediate-consequence operator, so they over-approximate the reachable set. This is all
    the pipeline's correctness theorems need.
  \<^item> \<^bold>\<open>ordered local-validity check = tightness (\<subseteq>)\<close>: every certificate fact is genuinely
    derivable; gives exact equality, needed only to retire the \<open>found_*\<close> theorems.
\<close>

subsection \<open>Certificate data structure (Nemo ordered-graph format)\<close>

text \<open>A certificate is a list of nodes. Each node records a reachable fact (the Nemo edge
  \<^emph>\<open>label\<close>) together with the \<^emph>\<open>indices\<close> of the predecessor facts that justify it (the Nemo
  edge \<^emph>\<open>predecessors\<close>, pointing at earlier nodes). The list order is the derivation rank;
  the ordering invariant (predecessor index \<open>< \<close> own index) is \<^emph>\<open>checked\<close> (see \<open>ordered_check\<close>),
  so the support graph is acyclic by construction --- no rank field and no DFS.\<close>

datatype cert_node = CNode
  (cn_fact: facty)          \<comment> \<open>the derived fact (Nemo edge label)\<close>
  (cn_preds: "nat list")    \<comment> \<open>indices of predecessor facts (Nemo edge predecessors)\<close>

datatype certificate = Cert (nodes: "cert_node list")

definition cert_facts :: "certificate \<Rightarrow> facty list" where
  "cert_facts c = map cn_fact (nodes c)"

text \<open>The body facts of node \<open>i\<close>: the labels sitting at its predecessor indices.\<close>
definition cn_body :: "certificate \<Rightarrow> nat \<Rightarrow> facty list" where
  "cn_body c i = map (\<lambda>j. cn_fact (nodes c ! j)) (cn_preds (nodes c ! i))"

text \<open>Lift a \<^typ>\<open>fact\<close> to the corresponding \<^typ>\<open>facty\<close> formula. This matches the
  \<open>fact_to_facty\<close> abbreviation used inside \<^locale>\<open>grounder\<close>; we also need it at theory scope.\<close>
abbreviation fact_to_facty :: "fact \<Rightarrow> facty" where
  "fact_to_facty f \<equiv> Atom (uncurry predAtm f)"


text \<open>Round-trip for the executable fact store: over a list of predicate atoms, membership in
  \<open>organize_facts\<close> coincides with list membership. Lets us read the closure check (phrased over
  \<open>in_orga\<close>/\<open>organize_facts\<close>) back as a statement about the certificate fact \<^emph>\<open>set\<close>.\<close>
lemma in_orga_update_facts:
  assumes "\<forall>g \<in> set fs. is_predAtom g"
  shows "in_orga (Atom (predAtm p args)) (update_facts fs orga)
           \<longleftrightarrow> args \<in> set (orga p) \<or> Atom (predAtm p args) \<in> set fs"
  using assms
proof (induction fs)
  case Nil
  show ?case by simp
next
  case (Cons g fs)
  from Cons.prems have "is_predAtom g" by simp
  then obtain p' args' where g: "g = Atom (predAtm p' args')"
    by (cases g rule: is_predAtom.cases) auto
  have ih: "in_orga (Atom (predAtm p args)) (update_facts fs orga)
              \<longleftrightarrow> args \<in> set (orga p) \<or> Atom (predAtm p args) \<in> set fs"
    using Cons.prems Cons.IH by simp
  show ?case
  proof (cases "p' = p")
    case True
    then show ?thesis using g ih by (auto simp: Let_def)
  next
    case False
    then show ?thesis using g ih by (simp add: Let_def)
  qed
qed

lemma in_orga_organize_facts:
  assumes "\<forall>g \<in> set fs. is_predAtom g"
  shows "in_orga (Atom (predAtm p args)) (organize_facts fs)
           \<longleftrightarrow> Atom (predAtm p args) \<in> set fs"
  using in_orga_update_facts[OF assms, of p args "\<lambda>_. []"] by simp


text \<open>Formula / valuation helpers for the relaxation precondition argument (Kernel 2,
  sub-part 2). \<open>un_and\<close> distributes over the map-formula semantics and over \<open>map_atom_fmla\<close>;
  a positive predicate atom is entailed by \<open>valuation M\<close> iff it is in \<open>fst M\<close>; and a positive
  non-predicate literal (an equality guard) is entailed model-independently.\<close>

lemma un_and_map_semantics: "A \<Turnstile>\<^sub>m F \<Longrightarrow> \<forall>f \<in> set (un_and F). A \<Turnstile>\<^sub>m f"
  by (induction F rule: un_and.induct) auto

lemma un_and_map_atom_fmla: "un_and (map_atom_fmla \<sigma> F) = map (map_atom_fmla \<sigma>) (un_and F)"
  by (induction F rule: un_and.induct) auto

lemma valuation_predAtm_iff:
  "valuation M \<Turnstile>\<^sub>m Atom (predAtm p xs) \<longleftrightarrow> Atom (predAtm p xs) \<in> fst M"
  by (simp add: valuation_def)

lemma cond_lit_model_indep:
  assumes "is_pos_lit c" "\<not> is_predAtom c"
  shows "valuation M \<Turnstile>\<^sub>m map_atom_fmla \<sigma> c \<longleftrightarrow> valuation M' \<Turnstile>\<^sub>m map_atom_fmla \<sigma> c"
  using assms by (cases c rule: is_pos_lit.cases) (auto simp: valuation_def)

lemma chosen_from_replicate:
  "length xs = n \<Longrightarrow> (\<forall>x \<in> set xs. x \<in> set S) \<Longrightarrow> chosen_from (replicate n S) xs"
  by (induction xs arbitrary: n) auto


subsection \<open>Locale A: admissible certificates for a relaxed problem\<close>

text \<open>The checker runs on a \<^emph>\<open>relaxed\<close> problem (positive preconditions, single datalog
  stratum), so the immediate-consequence operator is monotone. \<^locale>\<open>relaxed_problem\<close>
  bundles well-formedness, normalization and relaxation. In the pipeline it is interpreted at
  the relaxed problem \<open>P\<^sub>R\<close>.\<close>

locale pddl_datalog = relaxed_problem
begin

subsubsection \<open>Closure check (soundness, \<open>\<supseteq>\<close>) --- a finite model check\<close>

text \<open>The certificate facts contain every initial fact and are \<^emph>\<open>closed\<close> under the immediate
  consequence operator: for every action clause and every ground argument tuple (drawn from the
  finitely many object names), if the instantiated positive precondition is already present and
  the equality guards hold, then the instantiated add-effects are present too. This is a finite,
  executable check that does \<^emph>\<open>not\<close> depend on the untrusted engine's instantiation machinery; it
  makes the certificate facts a model of the consequence operator, hence a superset of the
  reachable facts.\<close>
definition closure_check :: "certificate \<Rightarrow> bool" where
  "closure_check c \<equiv>
     (let fs = cert_facts c in
        (\<forall>f \<in> set fs. is_predAtom f) \<and>
        (\<forall>f \<in> set init'. f \<in> set fs) \<and>
        (\<forall>cl \<in> set a_clauses.
           \<forall>args \<in> set (all_combos \<checkmark> (replicate (length (cl_params cl)) const_names)).
              (set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl)) \<subseteq> set fs
               \<and> satisfies_conds (cl_params cl) (cl_cond_pre cl) args)
              \<longrightarrow> set (consequence_of cl args) \<subseteq> set fs))"

text \<open>Every object argument of a well-formed plan action is one of the finitely many object
  names, so the closure check's enumeration covers it.\<close>
lemma is_obj_of_type_const_name:
  assumes "is_obj_of_type n T"
  shows "n \<in> set const_names"
proof -
  from assms have "objT n \<noteq> None" unfolding is_obj_of_type_def by (auto split: option.splits)
  hence "n \<in> dom objT" by auto
  thus ?thesis unfolding objT_alt by (auto simp: dom_map_of_conv_image_fst)
qed

lemma action_params_match_combos:
  assumes "action_params_match h args"
  shows "args \<in> set (all_combos \<checkmark> (replicate (length (parameters h)) const_names))"
proof -
  from assms have len: "length args = length (parameters h)"
    unfolding action_params_match_def by (simp add: list_all2_lengthD)
  have "\<forall>a \<in> set args. a \<in> set const_names"
  proof
    fix a assume "a \<in> set args"
    then obtain i where "i < length args" "args ! i = a" by (auto simp: in_set_conv_nth)
    then have "is_obj_of_type a (map snd (parameters h) ! i)"
      using assms unfolding action_params_match_def by (auto simp: list_all2_conv_all_nth)
    thus "a \<in> set const_names" using is_obj_of_type_const_name by blast
  qed
  hence "chosen_from (replicate (length (parameters h)) const_names) args"
    using chosen_from_replicate[OF len] by blast
  thus ?thesis using set_all_combos by auto
qed

subsubsection \<open>Ordered local-validity check (tightness, \<open>\<subseteq>\<close>) --- the Nemo \<open>ograph\<close> check\<close>

text \<open>Every predecessor index is strictly smaller than the node's own index (Nemo's array
  ordering invariant). The index is the well-founded rank; strictly decreasing along support
  edges \<Rightarrow> acyclic, with no graph traversal and no verified DFS.\<close>
definition ordered_check :: "certificate \<Rightarrow> bool" where
  "ordered_check c \<equiv> (\<forall>i < length (nodes c). \<forall>j \<in> set (cn_preds (nodes c ! i)). j < i)"

text \<open>Local validity of node \<open>i\<close> (Nemo's \<open>locallyValid\<close>): either it is an initial fact with no
  predecessors, or it is the head of a ground instance of some action clause whose positive
  precondition atoms are exactly the body facts at the predecessor indices.\<close>
definition local_valid :: "certificate \<Rightarrow> nat \<Rightarrow> bool" where
  "local_valid c i \<equiv>
     (let n = nodes c ! i in
        (cn_preds n = [] \<and> cn_fact n \<in> set init') \<or>
        (\<exists>cl \<in> set pred_clauses. \<exists>args.
            satisfies_conds (cl_params cl) (cl_cond_pre cl) args \<and>
            cn_fact n \<in> set (consequence_of cl args) \<and>
            set (cn_body c i)
              = set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl))))"

definition admissible :: "certificate \<Rightarrow> bool" where
  "admissible c \<equiv>
     closure_check c \<and> ordered_check c \<and> (\<forall>i < length (nodes c). local_valid c i)"

subsubsection \<open>Applicable plan actions read off the certificate\<close>

text \<open>For the soundness-only route the applicable plan actions are over-approximated by a
  \<^emph>\<open>finite enumeration\<close> (the same device as \<open>closure_check\<close>, decoupled from the untrusted
  engine): for every action clause and every ground argument tuple drawn from the finitely many
  object names, the ground action \<open>SimplePlanAction (cl_name cl) args\<close> is included iff its
  instantiated positive precondition is already in the (closed) certificate facts and its
  equality guards hold. With closure this is a superset of \<open>applicable\<close>: an enabled action's
  positive precondition holds in a reachable world model, whose facts are inside the certificate.
  (The exact route would read each ground action off the \<open>local_valid\<close> witnesses instead.)\<close>
definition cert_ops :: "certificate \<Rightarrow> ast_classical_plan_action list" where
  "cert_ops c =
     remdups (concat (map (\<lambda>cl.
        map (SimplePlanAction (cl_name cl))
            (filter (\<lambda>args.
                set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl))
                  \<subseteq> set (cert_facts c)
                \<and> satisfies_conds (cl_params cl) (cl_cond_pre cl) args)
              (all_combos \<checkmark> (replicate (length (cl_params cl)) const_names))))
        a_clauses))"

subsubsection \<open>Results\<close>

text \<open>\<^bold>\<open>Kernel 1 (initial inclusion).\<close> The world-model initial facts \<open>fst I\<close> lie in any
  closure-checked certificate: \<open>closure_check\<close> records every fact of \<open>init'\<close>, and
  \<open>fst I = set (init P) \<subseteq> set init'\<close>. (Sub-obligation: the \<open>organize_facts\<close>/\<open>in_orga\<close>
  round-trip and \<open>init P \<subseteq> init'\<close>.)\<close>
lemma closure_init_sub:
  assumes "closure_check c"
  shows "fst I \<subseteq> set (cert_facts c)"
proof
  fix f assume "f \<in> fst I"
  hence "f \<in> set (init P)" by (auto simp: I_def)
  hence "f \<in> set init'" unfolding init'_def by (simp add: conc_unique_un)
  thus "f \<in> set (cert_facts c)" using assms unfolding closure_check_def Let_def by blast
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
      using relaxed_prob unfolding relaxed_prob_def by simp
    hence "is_pos_conj (ac_pre ac)" using assms(2) by simp
    thus ?thesis using ac_eq by simp
  qed
  have pos_part: "set (map (map_atom_fmla (ac_tsubst ps args)) (pos_lits_of pre)) \<subseteq> fst M"
  proof
    fix x assume "x \<in> set (map (map_atom_fmla (ac_tsubst ps args)) (pos_lits_of pre))"
    then obtain l where l: "l \<in> set (pos_lits_of pre)"
      and x: "x = map_atom_fmla (ac_tsubst ps args) l" by auto
    from l have l_un: "l \<in> set (un_and pre)" and l_pred: "is_predAtom l"
      unfolding pos_lits_of_def by auto
    from l_pred obtain p xs where l_eq: "l = Atom (predAtm p xs)"
      by (cases l rule: is_predAtom.cases) auto
    have "valuation M \<Turnstile>\<^sub>m x" using all_lits l_un x by blast
    thus "x \<in> fst M" using x l_eq by (simp add: valuation_def)
  qed
  have cond_part: "list_all (\<lambda>c. valuation ({}, Map.empty) \<Turnstile>\<^sub>m
                              map_atom_fmla (ac_tsubst ps args) c) (cond_lits_of pre)"
    unfolding list_all_iff
  proof
    fix c assume "c \<in> set (cond_lits_of pre)"
    hence c_un: "c \<in> set (un_and pre)" and c_npred: "\<not> is_predAtom c"
      unfolding cond_lits_of_def by auto
    have "is_pos_lit c" using pos c_un is_pos_conj_alt by blast
    moreover have "valuation M \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) c"
      using all_lits c_un by blast
    ultimately show "valuation ({}, Map.empty) \<Turnstile>\<^sub>m map_atom_fmla (ac_tsubst ps args) c"
      using cond_lit_model_indep c_npred by blast
  qed
  show ?thesis
    unfolding cl_params cl_pred cl_cond using pos_part cond_part by blast
qed

text \<open>\<^bold>\<open>Sub-part 3 (engine instantiation completeness) --- TODO, the mountain.\<close> A clause whose
  instantiated positive body is already in the certificate (and whose equality guards hold)
  has its \<open>consequence_of\<close> inside the certificate: the engine's \<open>all_derivs\<close> generates it (or,
  for a body-less fact clause, it is in \<open>init'\<close>), and \<open>closure_check\<close> keeps it in. This is the
  Level-1..6 instantiation-completeness step of theory \<open>Reachability_Analysis\<close>.\<close>
lemma consequence_in_cert:
  assumes "closure_check c"
    and "cl \<in> set a_clauses"
    and "args \<in> set (all_combos \<checkmark> (replicate (length (cl_params cl)) const_names))"
    and "set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl))
           \<subseteq> set (cert_facts c)"
    and "satisfies_conds (cl_params cl) (cl_cond_pre cl) args"
  shows "set (consequence_of cl args) \<subseteq> set (cert_facts c)"
  using assms unfolding closure_check_def Let_def by blast

text \<open>\<^bold>\<open>Kernel 2 (one-step adds-closure).\<close> Assembled from sub-parts 1--3: resolve the enabled
  action to its schema (@{thm wf_pa_refs_ac}), rewrite its adds to the engine's
  \<open>consequence_of\<close> (@{thm res_inst_adds_eq_consequence}), note the instantiated body is in the
  certificate (sub-part 2 + \<open>fst M \<subseteq> cert\<close>), and close under the engine (sub-part 3).\<close>
lemma closure_step_adds:
  assumes cc: "closure_check c" and en: "plan_action_enabled a M"
    and subM: "fst M \<subseteq> set (cert_facts c)"
  shows "set (adds (effect ((the \<circ> res_inst) a))) \<subseteq> set (cert_facts c)"
proof -
  obtain n args where a: "a = SimplePlanAction n args" by (cases a)
  have wf: "wf_classical_plan_action (SimplePlanAction n args)"
    using en unfolding a plan_action_enabled_def by (simp add: Let_def)
  from wf obtain ac where acD: "ac \<in> set (actions D)" and acn: "ac_name ac = n"
    and apm: "action_params_match (head ac) args"
    and res: "resolve_classical_action_schema n = Some ac"
    by (rule wf_pa_refs_ac)
  obtain h bb where ac_h: "ac = SimpleActionSchema h bb" by (cases ac)
  obtain nm ps where h: "h = ActionHead nm ps" by (cases h)
  have ac_eq: "ac = SimpleActionSchema (ActionHead n ps) bb"
    using ac_h h acn by simp
  let ?cl = "as_action_clause ac"
  have clause_mem: "?cl \<in> set a_clauses"
    using acD unfolding a_clauses_def by simp
  obtain bpre beff where bb: "bb = SimpleActionBody bpre beff" by (cases bb)
  obtain bad bdl bnl where beff: "beff = Effect bad bdl bnl" by (cases beff)
  have args_combos: "args \<in> set (all_combos \<checkmark> (replicate (length (cl_params ?cl)) const_names))"
    using action_params_match_combos[OF apm] ac_eq bb beff by simp
  have adds_eq: "adds (effect ((the \<circ> res_inst) a)) = consequence_of ?cl args"
    using res_inst_adds_eq_consequence[OF acD[unfolded ac_eq]] a ac_eq by simp
  have en': "plan_action_enabled (SimplePlanAction n args) M" using en a by simp
  have body: "set (map (map_atom_fmla (ac_tsubst (cl_params ?cl) args)) (cl_pred_pre ?cl))
                \<subseteq> fst M"
    and conds: "satisfies_conds (cl_params ?cl) (cl_cond_pre ?cl) args"
    using enabled_clause_body[OF en' acD acn] by simp_all
  have "set (map (map_atom_fmla (ac_tsubst (cl_params ?cl) args)) (cl_pred_pre ?cl))
          \<subseteq> set (cert_facts c)"
    using body subM by blast
  hence "set (consequence_of ?cl args) \<subseteq> set (cert_facts c)"
    using consequence_in_cert[OF cc clause_mem args_combos _ conds] by blast
  thus ?thesis using adds_eq by simp
qed

text \<open>The closure invariant carried along a valid plan: from the fact update
  \<open>fst M' = (fst M - dels) \<union> adds\<close> (@{thm apply_ground_action_alt}), deleting facts keeps the
  subset and Kernel 2 keeps the adds inside, so every reachable world model's facts stay in the
  certificate.\<close>
lemma closure_invariant:
  assumes "closure_check c"
  shows "valid_classical_plan_alt M \<pi>s M' \<Longrightarrow> fst M \<subseteq> set (cert_facts c)
           \<Longrightarrow> fst M' \<subseteq> set (cert_facts c)"
proof (induction \<pi>s arbitrary: M)
  case Nil
  thus ?case by simp
next
  case (Cons a \<pi>s)
  let ?a' = "(the \<circ> res_inst) a"
  from Cons.prems(1) have en: "plan_action_enabled a M"
    and rest: "valid_classical_plan_alt (execute_plan_action a M) \<pi>s M'" by simp_all
  obtain L N where M: "M = (L, N)" by (cases M)
  have fstM': "fst (execute_plan_action a M)
                 = (L - set (dels (effect ?a'))) \<union> set (adds (effect ?a'))"
    unfolding execute_plan_action_def M using apply_ground_action_alt[of ?a' L N] by simp
  have add_sub: "set (adds (effect ?a')) \<subseteq> set (cert_facts c)"
    using closure_step_adds[OF assms en Cons.prems(2)] .
  have "L \<subseteq> set (cert_facts c)" using Cons.prems(2) M by simp
  hence "fst (execute_plan_action a M) \<subseteq> set (cert_facts c)"
    unfolding fstM' using add_sub by auto
  thus ?case using Cons.IH[OF rest] by blast
qed

text \<open>Soundness: a closed certificate over-approximates the reachable facts --- the \<open>\<supseteq>\<close>
  direction \<^locale>\<open>wf_grounder\<close> requires. Structural: every achievable fact sits in some
  reachable world model, which by @{thm closure_invariant} (started from @{thm closure_init_sub})
  stays inside the certificate.\<close>
theorem closure_sound:
  assumes "closure_check c"
  shows "fact_to_facty ` {f. achievable f} \<subseteq> set (cert_facts c)"
proof (rule image_subsetI)
  fix f assume "f \<in> {f. achievable f}"
  then obtain \<pi>s M where vp: "valid_classical_plan_alt I \<pi>s M"
    and mem: "Atom (uncurry predAtm f) \<in> fst M"
    unfolding achievable_def by auto
  have "fst I \<subseteq> set (cert_facts c)" using closure_init_sub[OF assms] .
  with closure_invariant[OF assms vp] have "fst M \<subseteq> set (cert_facts c)" by blast
  thus "fact_to_facty f \<in> set (cert_facts c)" using mem by auto
qed

text \<open>\<^bold>\<open>Ops soundness (\<open>\<supseteq>\<close> for actions).\<close> Every applicable plan action is in \<open>cert_ops\<close>: an
  applicable action is enabled in some reachable world model \<open>M\<close>; by @{thm closure_invariant}
  (from @{thm closure_init_sub}) \<open>fst M\<close> lies in the certificate, so the action's instantiated
  positive precondition is too (@{thm enabled_clause_body}), its equality guards hold, and its
  argument tuple is one of the enumerated combinations (@{thm action_params_match_combos}) ---
  exactly the membership condition of the finite \<open>cert_ops\<close> enumeration. Mirrors
  @{thm closure_step_adds}.\<close>
theorem cert_ops_sound:
  assumes cc: "closure_check c"
  shows "{\<pi>. applicable \<pi>} \<subseteq> set (cert_ops c)"
proof
  fix \<pi> assume "\<pi> \<in> {\<pi>. applicable \<pi>}"
  then obtain \<pi>s M where vp: "valid_classical_plan_alt I \<pi>s M"
    and en: "plan_action_enabled \<pi> M" using applicable_alt by auto
  have subM: "fst M \<subseteq> set (cert_facts c)"
    using closure_invariant[OF cc vp] closure_init_sub[OF cc] by blast
  obtain n args where pi: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  have wf: "wf_classical_plan_action (SimplePlanAction n args)"
    using en unfolding pi plan_action_enabled_def by (simp add: Let_def)
  from wf obtain ac where acD: "ac \<in> set (actions D)" and acn: "ac_name ac = n"
    and apm: "action_params_match (head ac) args"
    and res: "resolve_classical_action_schema n = Some ac"
    by (rule wf_pa_refs_ac)
  obtain h bb where ac_h: "ac = SimpleActionSchema h bb" by (cases ac)
  obtain nm ps where h: "h = ActionHead nm ps" by (cases h)
  have ac_eq: "ac = SimpleActionSchema (ActionHead n ps) bb" using ac_h h acn by simp
  let ?cl = "as_action_clause ac"
  have clause_mem: "?cl \<in> set a_clauses" using acD unfolding a_clauses_def by simp
  obtain bpre beff where bb: "bb = SimpleActionBody bpre beff" by (cases bb)
  obtain bad bdl bnl where beff: "beff = Effect bad bdl bnl" by (cases beff)
  have clname: "cl_name ?cl = n" using ac_eq bb beff by simp
  have args_combos: "args \<in> set (all_combos \<checkmark> (replicate (length (cl_params ?cl)) const_names))"
    using action_params_match_combos[OF apm] ac_eq bb beff by simp
  have en': "plan_action_enabled (SimplePlanAction n args) M" using en pi by simp
  have body: "set (map (map_atom_fmla (ac_tsubst (cl_params ?cl) args)) (cl_pred_pre ?cl)) \<subseteq> fst M"
    and conds: "satisfies_conds (cl_params ?cl) (cl_cond_pre ?cl) args"
    using enabled_clause_body[OF en' acD acn] by simp_all
  have body': "set (map (map_atom_fmla (ac_tsubst (cl_params ?cl) args)) (cl_pred_pre ?cl))
                 \<subseteq> set (cert_facts c)" using body subM by blast
  let ?cps = "filter (\<lambda>a. set (map (map_atom_fmla (ac_tsubst (cl_params ?cl) a)) (cl_pred_pre ?cl))
                            \<subseteq> set (cert_facts c)
                          \<and> satisfies_conds (cl_params ?cl) (cl_cond_pre ?cl) a)
                  (all_combos \<checkmark> (replicate (length (cl_params ?cl)) const_names))"
  have args_in: "args \<in> set ?cps" using args_combos body' conds by simp
  have pi_in: "\<pi> \<in> set (map (SimplePlanAction (cl_name ?cl)) ?cps)"
    using args_in pi clname by auto
  show "\<pi> \<in> set (cert_ops c)"
    unfolding cert_ops_def using clause_mem pi_in by auto
qed

end


text \<open>\<^bold>\<open>Locale B (the certificate \<open>\<rightarrow>\<close> grounder plug-in) lives in theory
  \<open>Certified_Grounding_Locales\<close>\<close> as the locale \<open>certified_reachability\<close> over
  \<open>normalized_problem_rx\<close>. It targets the \<^emph>\<open>un-relaxed\<close> problem \<open>P\<close> (real add+delete
  effects), using this kernel's relaxed reachable facts (\<open>cert_facts\<close>) and applicable ops
  (\<open>cert_ops\<close>) only as the pruning oracle, bridged to \<open>P\<close> by \<open>relax_achievables\<close> /
  \<open>relax_applicables\<close>. An earlier \<open>pddl_datalog\<close>-based Locale B grounded the relaxed
  problem \<open>P\<^sub>R\<close> directly --- unsound, since \<open>P\<^sub>R\<close> can be solvable when \<open>P\<close> is not --- and was
  removed. This kernel exports \<open>closure_sound\<close> (facts \<open>\<supseteq>\<close>) and \<open>cert_ops_sound\<close>
  (ops \<open>\<supseteq>\<close>) for that bridge.\<close>


section \<open>The PDDL \<open>\<rightarrow>\<close> datalog serialization\<close>

text \<open>The reachability oracle's input is phrased in the AFP \<open>Stratified_Datalog\<close> clause syntax
  (\<^typ>\<open>('p, 'x, 'c) clause\<close>): one \<^const>\<open>Cls\<close> per add-effect of each action clause --- body =
  one \<^const>\<open>PosLit\<close> per positive precondition atom plus \<^const>\<open>Eql\<close>/\<^const>\<open>Neql\<close> filters for
  the equality conditions --- and one bodyless ground clause per initial fact. The condition
  translation mirrors the kernel's \<open>satisfies_cond\<close> semantics (literals evaluated in the
  \<^emph>\<open>empty\<close> world model): \<open>\<^bold>\<not>\<bottom>\<close> and negated predicate atoms are unconditionally true and are
  dropped; a \<open>\<bottom>\<close> condition makes the clause statically unsatisfiable, so the whole clause is
  omitted. The program is \<^emph>\<open>transport only\<close>: the kernel re-checks the returned certificate via
  \<^const>\<open>pddl_datalog.admissible\<close> + \<open>normalized_problem_rx.grounding_checks\<close> (over the
  \<^const>\<open>ast_classical_problem.a_clauses\<close> it recomputes itself), never against this
  serialization, so no proofs depend on it. The oracle (in SML) renders this as a Nemo program,
  runs Nemo, and parses the certificate back.\<close>

type_synonym pddl_dl_clause = "(predicate, variable, object) clause"

fun dl_id_of_term :: "term \<Rightarrow> (variable, object) id" where
  "dl_id_of_term (term.VAR v) = id.Var v"
| "dl_id_of_term (term.CONST c) = id.Cst c"

fun dl_pos_rh :: "term atom formula \<Rightarrow> (predicate, variable, object) rh option" where
  "dl_pos_rh (Atom (predAtm p ts)) = Some (PosLit p (map dl_id_of_term ts))"
| "dl_pos_rh _ = None"

text \<open>\<^term>\<open>Some (Some rh)\<close>: an equality filter; \<^term>\<open>Some None\<close>: unconditionally true (drop
  the literal); \<^const>\<open>None\<close>: statically false / unsupported (drop the clause, fail-closed).\<close>
fun dl_cond_rh :: "term atom formula \<Rightarrow> (predicate, variable, object) rh option option" where
  "dl_cond_rh (Atom (eqAtm t1 t2)) = Some (Some (Eql (dl_id_of_term t1) (dl_id_of_term t2)))"
| "dl_cond_rh (\<^bold>\<not> (Atom (eqAtm t1 t2))) = Some (Some (Neql (dl_id_of_term t1) (dl_id_of_term t2)))"
| "dl_cond_rh (\<^bold>\<not> \<bottom>) = Some None"
| "dl_cond_rh (\<^bold>\<not> (Atom (predAtm _ _))) = Some None"
| "dl_cond_rh _ = None"

definition dl_clauses_of_action_clause :: "action_clause \<Rightarrow> pddl_dl_clause list" where
  [code]: "dl_clauses_of_action_clause cl \<equiv>
     (let conds = map dl_cond_rh (cl_cond_pre cl);
          pres = map dl_pos_rh (cl_pred_pre cl)
      in if None \<in> set conds \<or> None \<in> set pres then []
         else
           let body = map the pres @ List.map_filter id (map the conds)
           in List.map_filter
                (\<lambda>f. case f of Atom (predAtm p ts) \<Rightarrow> Some (Cls p (map dl_id_of_term ts) body)
                             | _ \<Rightarrow> None)
                (cl_pos cl))"

fun dl_fact_clause :: "object atom formula \<Rightarrow> pddl_dl_clause option" where
  "dl_fact_clause (Atom (predAtm p args)) = Some (Cls p (map id.Cst args) [])"
| "dl_fact_clause _ = None"

text \<open>The full translated rule set of a (relaxed, normalized) problem \<open>R\<close>: one group of clauses
  per action clause plus one bodyless ground fact clause per initial fact. The wire-format
  packaging \<open>dl_program_of\<close> (theory \<open>Grounding_Pipeline_STRIPS_Executable\<close>) hands exactly this
  list to Nemo, so the bridge lemmas below speak about the very program the oracle runs on.\<close>
definition dl_rules where
  [code]: "dl_rules R \<equiv>
     concat (map dl_clauses_of_action_clause (ast_classical_problem.a_clauses R))
     @ List.map_filter dl_fact_clause (ast_classical_problem.init' R)"


subsection \<open>Executable mirrors of the certificate checks\<close>

text \<open>The certificate checks above live in a locale \<^emph>\<open>with\<close> assumptions (\<^locale>\<open>pddl_datalog\<close>),
  so their \<open>_def\<close> equations are guarded by the locale predicate and are not directly
  code-registrable. We replay each body unconditionally at the top level (the bodies do not use
  the assumptions), over the \<^emph>\<open>relaxed\<close> problem as an explicit argument \<open>R\<close>; equality with the
  locale versions (under the locale predicate) is recorded below for the soundness link.\<close>

definition closure_check_exec where
  [code]: "closure_check_exec R c \<equiv>
     (let fs = cert_facts c in
        (\<forall>f \<in> set fs. is_predAtom f) \<and>
        (\<forall>f \<in> set (ast_classical_problem.init' R). f \<in> set fs) \<and>
        (\<forall>cl \<in> set (ast_classical_problem.a_clauses R).
           \<forall>args \<in> set (all_combos \<checkmark> (replicate (length (cl_params cl)) (ast_classical_problem.const_names R))).
              (set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl)) \<subseteq> set fs
               \<and> satisfies_conds (cl_params cl) (cl_cond_pre cl) args)
              \<longrightarrow> set (consequence_of cl args) \<subseteq> set fs))"

definition ordered_check_exec where
  [code]: "ordered_check_exec c \<equiv> (\<forall>i < length (nodes c). \<forall>j \<in> set (cn_preds (nodes c ! i)). j < i)"

text \<open>\<^const>\<open>pddl_datalog.local_valid\<close> has an \<^emph>\<open>unbounded\<close> \<open>\<exists>args\<close>, not code-generable. We bound it
  to the same finite object-name combinations the closure check enumerates. This is a \<^emph>\<open>sound
  under-approximation\<close> --- \<open>local_valid_exec R c i \<longrightarrow> pddl_datalog.local_valid R c i\<close> (bounded
  \<open>\<exists>\<close> implies \<open>\<exists>\<close>) --- so an accepted certificate is genuinely admissible. (Nemo's witness args are
  always object names, so legitimate certificates still pass.)\<close>
definition local_valid_exec where
  [code]: "local_valid_exec R c i \<equiv>
     (let n = nodes c ! i in
        (cn_preds n = [] \<and> cn_fact n \<in> set (ast_classical_problem.init' R)) \<or>
        (\<exists>cl \<in> set (ast_classical_problem.pred_clauses R).
           \<exists>args \<in> set (all_combos \<checkmark> (replicate (length (cl_params cl)) (ast_classical_problem.const_names R))).
              satisfies_conds (cl_params cl) (cl_cond_pre cl) args \<and>
              cn_fact n \<in> set (consequence_of cl args) \<and>
              set (cn_body c i)
                = set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl))))"

definition admissible_exec where
  [code]: "admissible_exec R c \<equiv>
     closure_check_exec R c \<and> ordered_check_exec c \<and> (\<forall>i < length (nodes c). local_valid_exec R c i)"

definition cert_ops_exec where
  [code]: "cert_ops_exec R c =
     remdups (concat (map (\<lambda>cl.
        map (SimplePlanAction (cl_name cl))
            (filter (\<lambda>args.
                set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl))
                  \<subseteq> set (cert_facts c)
                \<and> satisfies_conds (cl_params cl) (cl_cond_pre cl) args)
              (all_combos \<checkmark> (replicate (length (cl_params cl)) (ast_classical_problem.const_names R)))))
        (ast_classical_problem.a_clauses R)))"

text \<open>The mirrors replay the locale bodies verbatim, so under the locale predicate each mirror
  agrees with its locale original (\<open>local_valid_exec\<close> only \<^emph>\<open>implies\<close> its original: the bounded
  \<open>\<exists>\<close> is a sound under-approximation).\<close>

lemma closure_check_exec_eq:
  assumes "pddl_datalog R"
  shows "closure_check_exec R c = pddl_datalog.closure_check R c"
  unfolding closure_check_exec_def pddl_datalog.closure_check_def[OF assms] by (rule refl)

lemma ordered_check_exec_eq:
  assumes "pddl_datalog R"
  shows "ordered_check_exec c = pddl_datalog.ordered_check c"
  unfolding ordered_check_exec_def pddl_datalog.ordered_check_def[OF assms] by (rule refl)

lemma local_valid_exec_sound:
  assumes "pddl_datalog R"
      and "local_valid_exec R c i"
  shows "pddl_datalog.local_valid R c i"
  using assms(2)
  unfolding local_valid_exec_def pddl_datalog.local_valid_def[OF assms(1)] Let_def
  by blast

lemma admissible_exec_sound:
  assumes "pddl_datalog R"
      and "admissible_exec R c"
  shows "pddl_datalog.admissible R c"
  using assms(2) local_valid_exec_sound[OF assms(1)]
  unfolding admissible_exec_def pddl_datalog.admissible_def[OF assms(1)]
            closure_check_exec_eq[OF assms(1)] ordered_check_exec_eq[OF assms(1)]
  by blast

lemma cert_ops_exec_eq:
  assumes "pddl_datalog R"
  shows "cert_ops_exec R c = pddl_datalog.cert_ops R c"
  unfolding cert_ops_exec_def pddl_datalog.cert_ops_def[OF assms] by (rule refl)


section \<open>Bridging generic datalog certification to PDDL reachability certification\<close>

text \<open>Goal: justify the PDDL certificate checks by the \<^emph>\<open>generic\<close> positive-datalog checks of
  \<^theory>\<open>Datalog_Certification.Datalog_Certificate\<close>, run on the translated program
  (\<^const>\<open>dl_clauses_of_action_clause\<close> rules + \<^const>\<open>dl_fact_clause\<close> facts --- the same
  serialization \<open>dl_program_of\<close> hands to Nemo). Direction needed by the pipeline:

    \<^term>\<open>dl_admissible (dl_rules R) (ast_classical_problem.const_names R) dc
          \<Longrightarrow> admissible_exec R c\<close>

  for a PDDL certificate \<open>c\<close> that converts losslessly to the generic certificate \<open>dc\<close>
  (\<open>cert_to_dl c = Some dc\<close>, fail-closed on non-predicate-atom facts). Once the remaining
  sorried transfer lemma below is discharged, the pipeline can run the generic checker and
  obtain the PDDL-side admissibility for free; see \<open>WIP_datalog_cert_bridge.md\<close> for the
  discharge plan and \<open>ARCHITECTURE_datalog_certification.md\<close> for the design.\<close>

subsection \<open>Certificate conversion (fail-closed)\<close>

fun dl_fact_of_facty :: "facty \<Rightarrow> (predicate \<times> object list) option" where
  "dl_fact_of_facty (Atom (predAtm p xs)) = Some (p, xs)"
| "dl_fact_of_facty _ = None"

fun facty_of_dl :: "(predicate \<times> object list) \<Rightarrow> facty" where
  "facty_of_dl (p, xs) = Atom (predAtm p xs)"

definition dl_node_of :: "cert_node \<Rightarrow> (predicate, object) dl_cert_node option" where
  [code]: "dl_node_of n = map_option (\<lambda>f. DLNode f (cn_preds n)) (dl_fact_of_facty (cn_fact n))"

definition cert_to_dl :: "certificate \<Rightarrow> (predicate, object) dl_certificate option" where
  [code]: "cert_to_dl c = map_option DLCert (those (map dl_node_of (nodes c)))"

lemma dl_fact_of_facty_Some:
  assumes "dl_fact_of_facty f = Some g"
  shows "f = facty_of_dl g" and "is_predAtom f"
  using assms by (cases f rule: dl_fact_of_facty.cases; cases g; simp)+

subsection \<open>Structural correspondence\<close>

lemma those_Some:
  assumes "those xs = Some ys"
  shows "length ys = length xs \<and> (\<forall>i < length xs. xs ! i = Some (ys ! i))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then obtain y ys' where x: "x = Some y" and rest: "those xs = Some ys'" and ys: "ys = y # ys'"
    by (cases x) auto
  from Cons.IH[OF rest] show ?case
    unfolding x ys by (auto simp: nth_Cons split: nat.splits)
qed

lemma cert_to_dl_len:
  assumes "cert_to_dl c = Some dc"
  shows "length (dl_nodes dc) = length (nodes c)"
  using assms those_Some unfolding cert_to_dl_def by fastforce

lemma cert_to_dl_nth:
  assumes "cert_to_dl c = Some dc" and "i < length (nodes c)"
  shows "dn_preds (dl_nodes dc ! i) = cn_preds (nodes c ! i)"
    and "dl_fact_of_facty (cn_fact (nodes c ! i)) = Some (dn_fact (dl_nodes dc ! i))"
proof -
  from assms(1) obtain ns where ns: "those (map dl_node_of (nodes c)) = Some ns"
    and dc: "dc = DLCert ns"
    unfolding cert_to_dl_def by auto
  from those_Some[OF ns] assms(2)
  have "dl_node_of (nodes c ! i) = Some (ns ! i)" by auto
  then obtain f where "dl_fact_of_facty (cn_fact (nodes c ! i)) = Some f"
    and "ns ! i = DLNode f (cn_preds (nodes c ! i))"
    unfolding dl_node_of_def
    by (cases "dl_fact_of_facty (cn_fact (nodes c ! i))") auto
  then have "dl_fact_of_facty (cn_fact (nodes c ! i)) = Some (dn_fact (ns ! i))"
    and "dn_preds (ns ! i) = cn_preds (nodes c ! i)"
    by simp_all
  then show "dn_preds (dl_nodes dc ! i) = cn_preds (nodes c ! i)"
    and "dl_fact_of_facty (cn_fact (nodes c ! i)) = Some (dn_fact (dl_nodes dc ! i))"
    unfolding dc by simp_all
qed

lemma cert_to_dl_facts:
  assumes "cert_to_dl c = Some dc"
  shows "cert_facts c = map facty_of_dl (dl_cert_facts dc)"
proof (rule nth_equalityI)
  show "length (cert_facts c) = length (map facty_of_dl (dl_cert_facts dc))"
    using cert_to_dl_len[OF assms]
    unfolding cert_facts_def dl_cert_facts_def by simp
  fix i assume "i < length (cert_facts c)"
  then have i: "i < length (nodes c)" unfolding cert_facts_def by simp
  show "cert_facts c ! i = map facty_of_dl (dl_cert_facts dc) ! i"
    using dl_fact_of_facty_Some(1)[OF cert_to_dl_nth(2)[OF assms i]] cert_to_dl_len[OF assms] i
    unfolding cert_facts_def dl_cert_facts_def by simp
qed

lemma cert_to_dl_predAtom:
  assumes "cert_to_dl c = Some dc"
  shows "\<forall>f \<in> set (cert_facts c). is_predAtom f"
proof
  fix f assume "f \<in> set (cert_facts c)"
  then have "f \<in> facty_of_dl ` set (dl_cert_facts dc)"
    using cert_to_dl_facts[OF assms] by simp
  then obtain g where "f = facty_of_dl g" by auto
  then show "is_predAtom f" by (cases g) simp
qed

text \<open>The ordered check transfers both ways: conversion preserves indices and predecessors.\<close>
lemma cert_to_dl_ordered:
  assumes "cert_to_dl c = Some dc"
  shows "dl_ordered_check dc \<longleftrightarrow> ordered_check_exec c"
  unfolding dl_ordered_check_def ordered_check_exec_def
  using cert_to_dl_len[OF assms] cert_to_dl_nth(1)[OF assms] by simp

subsection \<open>The translated program is positive\<close>

lemma in_set_map_filter:
  "y \<in> set (List.map_filter f xs) \<longleftrightarrow> (\<exists>x \<in> set xs. f x = Some y)"
  by (force simp: List.map_filter_def image_iff intro: option.collapse[symmetric])

lemma dl_pos_rh_Some_shape:
  assumes "dl_pos_rh a = Some rh"
  shows "\<exists>p ts. rh = PosLit p ts"
  using assms by (cases a rule: dl_pos_rh.cases) auto

lemma dl_cond_rh_Some_guard:
  assumes "dl_cond_rh a = Some (Some rh)"
  shows "is_dl_guard rh"
  using assms by (cases a rule: dl_cond_rh.cases) auto

lemma dl_clauses_of_action_clause_mem:
  assumes "dcl \<in> set (dl_clauses_of_action_clause cl)"
  obtains p ts where
    "Atom (predAtm p ts) \<in> set (cl_pos cl)"
    and "dcl = Cls p (map dl_id_of_term ts)
                 (map (the \<circ> dl_pos_rh) (cl_pred_pre cl)
                  @ List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl)))"
    and "None \<notin> dl_pos_rh ` set (cl_pred_pre cl)"
    and "None \<notin> dl_cond_rh ` set (cl_cond_pre cl)"
proof -
  from assms have nn: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl))"
    "None \<notin> set (map dl_pos_rh (cl_pred_pre cl))"
    unfolding dl_clauses_of_action_clause_def by (auto simp: Let_def split: if_splits)
  from assms obtain f where f: "f \<in> set (cl_pos cl)"
    and some: "(case f of Atom (predAtm p ts) \<Rightarrow> Some (Cls p (map dl_id_of_term ts)
                  (map (the \<circ> dl_pos_rh) (cl_pred_pre cl)
                   @ List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl))))
                | _ \<Rightarrow> None) = Some dcl"
    unfolding dl_clauses_of_action_clause_def
    by (auto simp: Let_def in_set_map_filter split: if_splits)
  from some obtain p ts where "f = Atom (predAtm p ts)"
    and "dcl = Cls p (map dl_id_of_term ts)
            (map (the \<circ> dl_pos_rh) (cl_pred_pre cl)
             @ List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl)))"
    by (cases f) (auto split: atom.splits)
  with f nn show thesis by (intro that[of p ts]) auto
qed

lemma dl_rules_positive: "dl_positive_prog (dl_rules R)"
proof -
  have "\<forall>rh \<in> set (the_rhs dcl). is_pos_rh rh" if dcl: "dcl \<in> set (dl_rules R)" for dcl
  proof (cases "dcl \<in> set (concat (map dl_clauses_of_action_clause
                                       (ast_classical_problem.a_clauses R)))")
    case True
    then obtain cl where "dcl \<in> set (dl_clauses_of_action_clause cl)" by auto
    then show ?thesis
    proof (cases rule: dl_clauses_of_action_clause_mem)
      case (1 p ts)
      have "is_pos_rh rh" if rh: "rh \<in> set (the_rhs dcl)" for rh
      proof -
        from rh 1(2) consider
          (pre) a where "a \<in> set (cl_pred_pre cl)" "rh = the (dl_pos_rh a)"
        | (cond) a where "a \<in> set (cl_cond_pre cl)" "the (dl_cond_rh a) = Some rh"
          by (auto simp: in_set_map_filter)
        then show ?thesis
        proof cases
          case pre
          with 1(3) have "dl_pos_rh a = Some rh" by (metis image_eqI option.collapse)
          from dl_pos_rh_Some_shape[OF this] show ?thesis by auto
        next
          case cond
          with 1(4) have "dl_cond_rh a = Some (Some rh)" by (metis image_eqI option.collapse)
          from dl_cond_rh_Some_guard[OF this] show ?thesis by (cases rh) auto
        qed
      qed
      then show ?thesis by blast
    qed
  next
    case False
    with dcl obtain f where "dl_fact_clause f = Some dcl"
      unfolding dl_rules_def by (auto simp: in_set_map_filter)
    then have "the_rhs dcl = []" by (cases f rule: dl_fact_clause.cases) auto
    then show ?thesis by simp
  qed
  then show ?thesis unfolding dl_positive_prog_def by blast
qed

subsection \<open>Substitution, guard and atom transfer\<close>

text \<open>The mechanical correspondence between the generic checker's ground instances
  (\<^const>\<open>Datalog_Certificate.subst_id\<close> over \<^typ>\<open>(variable, object) id\<close>) and the PDDL
  kernel's (\<^const>\<open>subst_term\<close> via \<^const>\<open>ac_tsubst\<close>), plus the shape of a translated clause.\<close>

lemma facty_of_dl_eq_iff[simp]: "facty_of_dl g = facty_of_dl g' \<longleftrightarrow> g = g'"
  by (cases g; cases g') simp

lemma subst_id_dl_id_of_term:
  assumes "\<forall>v \<in> set (id_vars_list (dl_id_of_term t)). \<sigma> v = f v"
  shows "Datalog_Certificate.subst_id \<sigma> (dl_id_of_term t) = subst_term f t"
  using assms by (cases t) simp_all

lemma all_combos_replicateD:
  assumes "args \<in> set (all_combos \<checkmark> (replicate n U))"
  shows "length args = n" and "set args \<subseteq> set U"
  using assms unfolding set_all_combos
  by (auto simp: Datalog_Certificate.chosen_from_replicate)

lemma all_combos_replicateI:
  assumes "length args = n" and "set args \<subseteq> set U"
  shows "args \<in> set (all_combos \<checkmark> (replicate n U))"
  using assms unfolding set_all_combos
  by (auto simp: Datalog_Certificate.chosen_from_replicate)

lemma map_filter_append:
  "List.map_filter f (xs @ ys) = List.map_filter f xs @ List.map_filter f ys"
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

text \<open>The generic image of a (positive, predicate) precondition atom.\<close>
fun dl_atom_of :: "term atom formula \<Rightarrow> predicate \<times> (variable, object) id list" where
  "dl_atom_of (Atom (predAtm p ts)) = (p, map dl_id_of_term ts)"
| "dl_atom_of _ = undefined"

lemma dl_pos_rh_not_NoneE:
  assumes "dl_pos_rh a \<noteq> None"
  obtains p ts where "a = Atom (predAtm p ts)"
  using assms by (cases a rule: dl_pos_rh.cases) auto

lemma dl_cond_rh_SomeE:
  assumes "dl_cond_rh cnd = Some (Some g)"
  obtains (eq) t1 t2 where "cnd = Atom (eqAtm t1 t2)"
            "g = Eql (dl_id_of_term t1) (dl_id_of_term t2)"
        | (neq) t1 t2 where "cnd = \<^bold>\<not> (Atom (eqAtm t1 t2))"
            "g = Neql (dl_id_of_term t1) (dl_id_of_term t2)"
  using assms by (cases cnd rule: dl_cond_rh.cases) auto

lemma body_atoms_of_pres:
  assumes "\<forall>a \<in> set pres. dl_pos_rh a \<noteq> None"
  shows "List.map_filter rh_body_atom (map (the \<circ> dl_pos_rh) pres) = map dl_atom_of pres"
  using assms
proof (induction pres)
  case Nil
  show ?case by (simp add: List.map_filter_simps)
next
  case (Cons a pres)
  from Cons.prems have "dl_pos_rh a \<noteq> None" by simp
  then obtain p ts where "a = Atom (predAtm p ts)" by (rule dl_pos_rh_not_NoneE)
  then show ?case using Cons by (simp add: List.map_filter_simps)
qed

lemma body_atoms_of_conds:
  assumes "\<forall>cnd \<in> set conds. dl_cond_rh cnd \<noteq> None"
  shows "List.map_filter rh_body_atom (List.map_filter id (map (the \<circ> dl_cond_rh) conds)) = []"
  using assms
proof (induction conds)
  case Nil
  show ?case by (simp add: List.map_filter_simps)
next
  case (Cons cnd conds)
  then obtain x where x: "dl_cond_rh cnd = Some x" by auto
  show ?case
  proof (cases x)
    case None
    then show ?thesis using Cons x by (simp add: List.map_filter_simps)
  next
    case (Some g)
    with x have "is_dl_guard g" using dl_cond_rh_Some_guard by blast
    then have "rh_body_atom g = None" by (cases g) auto
    then show ?thesis using Cons x Some by (simp add: List.map_filter_simps)
  qed
qed

lemma guards_of_pres:
  assumes "\<forall>a \<in> set pres. dl_pos_rh a \<noteq> None"
  shows "filter is_dl_guard (map (the \<circ> dl_pos_rh) pres) = []"
  using assms
proof (induction pres)
  case Nil
  show ?case by simp
next
  case (Cons a pres)
  from Cons.prems have "dl_pos_rh a \<noteq> None" by simp
  then obtain p ts where "a = Atom (predAtm p ts)" by (rule dl_pos_rh_not_NoneE)
  then show ?case using Cons by simp
qed

lemma guards_of_conds:
  assumes "\<forall>cnd \<in> set conds. dl_cond_rh cnd \<noteq> None"
  shows "filter is_dl_guard (List.map_filter id (map (the \<circ> dl_cond_rh) conds))
           = List.map_filter id (map (the \<circ> dl_cond_rh) conds)"
  using assms
proof (induction conds)
  case Nil
  show ?case by (simp add: List.map_filter_simps)
next
  case (Cons cnd conds)
  then obtain x where x: "dl_cond_rh cnd = Some x" by auto
  show ?case
  proof (cases x)
    case None
    then show ?thesis using Cons x by (simp add: List.map_filter_simps)
  next
    case (Some g)
    with x have "is_dl_guard g" using dl_cond_rh_Some_guard by blast
    then show ?thesis using Cons x Some by (simp add: List.map_filter_simps)
  qed
qed

text \<open>Constructive direction of \<^const>\<open>dl_clauses_of_action_clause\<close>: an undropped clause
  contributes one generic clause per predicate-atom add effect.\<close>
lemma dl_clause_intro:
  assumes pres: "\<forall>a \<in> set (cl_pred_pre cl). dl_pos_rh a \<noteq> None"
    and conds: "\<forall>cnd \<in> set (cl_cond_pre cl). dl_cond_rh cnd \<noteq> None"
    and h: "Atom (predAtm p ts) \<in> set (cl_pos cl)"
  shows "Cls p (map dl_id_of_term ts)
           (map (the \<circ> dl_pos_rh) (cl_pred_pre cl)
            @ List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl)))
         \<in> set (dl_clauses_of_action_clause cl)"
proof -
  have nN: "None \<notin> set (map dl_cond_rh (cl_cond_pre cl))"
    "None \<notin> set (map dl_pos_rh (cl_pred_pre cl))"
    using conds pres by auto
  show ?thesis
    unfolding dl_clauses_of_action_clause_def Let_def
    using nN h
    by (auto simp: in_set_map_filter map_map o_def intro!: bexI[of _ "Atom (predAtm p ts)"])
qed

text \<open>Component view of a translated clause: head, positive body atoms, guards.\<close>
lemma dl_clause_shape:
  assumes dcl: "dcl \<in> set (dl_clauses_of_action_clause cl)"
  obtains p ts where
    "Atom (predAtm p ts) \<in> set (cl_pos cl)"
    and "the_lh dcl = (p, map dl_id_of_term ts)"
    and "cls_body_atoms dcl = map dl_atom_of (cl_pred_pre cl)"
    and "set (cls_guards dcl)
           = {g. \<exists>cnd \<in> set (cl_cond_pre cl). dl_cond_rh cnd = Some (Some g)}"
    and "\<forall>a \<in> set (cl_pred_pre cl). dl_pos_rh a \<noteq> None"
    and "\<forall>cnd \<in> set (cl_cond_pre cl). dl_cond_rh cnd \<noteq> None"
proof -
  from dl_clauses_of_action_clause_mem[OF dcl] obtain p ts where
    h: "Atom (predAtm p ts) \<in> set (cl_pos cl)" and
    e: "dcl = Cls p (map dl_id_of_term ts)
                (map (the \<circ> dl_pos_rh) (cl_pred_pre cl)
                 @ List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl)))" and
    nP: "None \<notin> dl_pos_rh ` set (cl_pred_pre cl)" and
    nC: "None \<notin> dl_cond_rh ` set (cl_cond_pre cl)" .
  have pres': "\<forall>a \<in> set (cl_pred_pre cl). dl_pos_rh a \<noteq> None" using nP by force
  have conds': "\<forall>cnd \<in> set (cl_cond_pre cl). dl_cond_rh cnd \<noteq> None" using nC by force
  have body: "cls_body_atoms dcl = map dl_atom_of (cl_pred_pre cl)"
    unfolding e cls_body_atoms_def
    by (simp add: map_filter_append body_atoms_of_pres[OF pres'] body_atoms_of_conds[OF conds'])
  have guards: "cls_guards dcl = List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl))"
    unfolding e cls_guards_def
    by (simp add: guards_of_pres[OF pres'] guards_of_conds[OF conds'])
  have gset: "set (cls_guards dcl)
                = {g. \<exists>cnd \<in> set (cl_cond_pre cl). dl_cond_rh cnd = Some (Some g)}"
  proof -
    have "set (List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl)))
            = {g. \<exists>cnd \<in> set (cl_cond_pre cl). the (dl_cond_rh cnd) = Some g}"
      by (force simp: in_set_map_filter)
    also have "\<dots> = {g. \<exists>cnd \<in> set (cl_cond_pre cl). dl_cond_rh cnd = Some (Some g)}"
      using conds' by (metis option.collapse)
    finally show ?thesis unfolding guards .
  qed
  have lh: "the_lh dcl = (p, map dl_id_of_term ts)" unfolding e by simp
  show thesis by (rule that[OF h lh body gset pres' conds'])
qed

text \<open>Atom-level transfer: applying the generic substitution to a translated atom and reading
  the result back as a \<^typ>\<open>facty\<close> is the same as instantiating the PDDL atom.\<close>
lemma facty_subst_atom_transfer:
  assumes agr: "\<forall>t \<in> set ts. \<forall>v \<in> set (id_vars_list (dl_id_of_term t)). \<sigma> v = f v"
  shows "facty_of_dl (Datalog_Certificate.subst_atom \<sigma> (p, map dl_id_of_term ts))
           = map_atom_fmla (subst_term f) (Atom (predAtm p ts))"
proof -
  have "map (\<lambda>t. Datalog_Certificate.subst_id \<sigma> (dl_id_of_term t)) ts = map (subst_term f) ts"
    using agr by (intro map_cong[OF refl] subst_id_dl_id_of_term) auto
  then show ?thesis
    unfolding Datalog_Certificate.subst_atom_def by (simp add: comp_def)
qed

text \<open>Guard transfer: a translated equality condition evaluates under the generic substitution
  exactly as the PDDL condition under the instantiated empty-model valuation.\<close>
lemma eval_guard_transfer:
  assumes g: "dl_cond_rh cnd = Some (Some g)"
    and agr: "\<forall>v \<in> set (rh_vars_list g). \<sigma> v = f v"
  shows "eval_guard \<sigma> g \<longleftrightarrow> valuation ({}, Map.empty) \<Turnstile>\<^sub>m map_atom_fmla (subst_term f) cnd"
proof (cases rule: dl_cond_rh_SomeE[OF g])
  case (1 t1 t2)
  have "Datalog_Certificate.subst_id \<sigma> (dl_id_of_term t1) = subst_term f t1"
    "Datalog_Certificate.subst_id \<sigma> (dl_id_of_term t2) = subst_term f t2"
    using agr unfolding 1(2) by (auto intro!: subst_id_dl_id_of_term)
  then show ?thesis unfolding 1 by (force simp: valuation_def dom_def)
next
  case (2 t1 t2)
  have "Datalog_Certificate.subst_id \<sigma> (dl_id_of_term t1) = subst_term f t1"
    "Datalog_Certificate.subst_id \<sigma> (dl_id_of_term t2) = subst_term f t2"
    using agr unfolding 2(2) by (auto intro!: subst_id_dl_id_of_term)
  then show ?thesis unfolding 2 by (force simp: valuation_def dom_def)
qed

text \<open>The conditions the translation drops as unconditionally true really are true.\<close>
lemma dl_cond_rh_dropped_true:
  assumes "dl_cond_rh cnd = Some None"
  shows "valuation ({}, Map.empty) \<Turnstile>\<^sub>m map_atom_fmla \<tau> cnd"
proof -
  from assms consider (notbot) "cnd = \<^bold>\<not> \<bottom>"
    | (negpred) p ts where "cnd = \<^bold>\<not> (Atom (predAtm p ts))"
    by (cases cnd rule: dl_cond_rh.cases) auto
  then show ?thesis
  proof cases
    case notbot
    then show ?thesis by simp
  next
    case negpred
    then show ?thesis by (force simp: valuation_def dom_def)
  qed
qed

text \<open>Tabulating a PDDL argument map over the clause variables yields a generic substitution.\<close>
lemma subst_of_zip_in_cls_substs:
  assumes vars: "set (cls_vars dcl) \<subseteq> set vs"
    and len: "length args = length vs"
    and mem: "set args \<subseteq> set U"
  shows "subst_of (cls_vars dcl) (map (the \<circ> map_of (zip vs args)) (cls_vars dcl))
           \<in> set (cls_substs U dcl)"
proof -
  have "the (map_of (zip vs args) v) \<in> set U" if "v \<in> set (cls_vars dcl)" for v
  proof -
    from that vars have "v \<in> set vs" by blast
    then obtain y where "map_of (zip vs args) v = Some y"
      using len by (metis map_of_zip_is_Some)
    then show ?thesis using mem map_of_SomeD set_zip_rightD by fastforce
  qed
  then show ?thesis unfolding cls_substs_iff
    by (intro exI[of _ "map (the \<circ> map_of (zip vs args)) (cls_vars dcl)"]) auto
qed

text \<open>Body correspondence at certificate level: predecessors in range let the PDDL body be
  read off the generic one.\<close>
lemma cert_to_dl_body:
  assumes conv: "cert_to_dl c = Some dc"
    and i: "i < length (nodes c)"
    and bound: "\<forall>j \<in> set (cn_preds (nodes c ! i)). j < length (nodes c)"
  shows "cn_body c i = map facty_of_dl (dn_body dc i)"
proof -
  have preds: "dn_preds (dl_nodes dc ! i) = cn_preds (nodes c ! i)"
    using cert_to_dl_nth(1)[OF conv i] .
  have "cn_fact (nodes c ! j) = facty_of_dl (dn_fact (dl_nodes dc ! j))"
    if "j \<in> set (cn_preds (nodes c ! i))" for j
    using dl_fact_of_facty_Some(1)[OF cert_to_dl_nth(2)[OF conv]] bound that by blast
  then show ?thesis
    unfolding cn_body_def dn_body_def preds map_map
    by (intro map_cong[OF refl]) (auto simp: o_def)
qed

subsection \<open>Well-formedness bundle for the transfer\<close>

text \<open>What the (relaxed, normalized) problem must guarantee for the generic checks to imply the
  PDDL ones. All conditions hold for \<open>ast_classical_problem.relax_prob
  (ast_classical_problem.P\<^sub>T P)\<close> of a well-formed restricted \<open>P\<close> --- discharging that is part of
  the WIP plan (\<open>WIP_datalog_cert_bridge.md\<close>):

  \<^item> every positive precondition atom is a predicate atom (its translation succeeds);
  \<^item> every add effect is a predicate atom (no clause head is dropped);
  \<^item> every condition literal either translates (\<open>Eql\<close>/\<open>Neql\<close>/drop-as-true) or is statically
    unsatisfiable (\<open>\<bottom>\<close>; then the PDDL check is vacuous for the whole clause, matching the
    fail-closed clause drop);
  \<^item> the variables of every translated clause are action parameters (so a generic substitution
    can be extended to a PDDL argument tuple);
  \<^item> the initial facts are predicate atoms (their fact clauses survive the translation);
  \<^item> the object universe is non-empty (parameters that do not occur in a clause still need a
    witness argument on the PDDL side).\<close>
definition dl_bridge_wf where
  "dl_bridge_wf R \<equiv>
     (\<forall>cl \<in> set (ast_classical_problem.a_clauses R).
        (\<forall>a \<in> set (cl_pred_pre cl). dl_pos_rh a \<noteq> None)
        \<and> (\<forall>a \<in> set (cl_pos cl). is_predAtom a)
        \<and> (\<forall>cnd \<in> set (cl_cond_pre cl).
             dl_cond_rh cnd \<noteq> None \<or> (\<forall>args. \<not> satisfies_cond (cl_params cl) args cnd))
        \<and> (\<forall>dcl \<in> set (dl_clauses_of_action_clause cl).
             set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))))
     \<and> (\<forall>f \<in> set (ast_classical_problem.init' R). is_predAtom f)
     \<and> ast_classical_problem.const_names R \<noteq> []"

subsection \<open>The transfer lemmas (one still sorried; see \<open>WIP_datalog_cert_bridge.md\<close>)\<close>

lemma dl_closure_imp_closure_exec:
  assumes wf: "dl_bridge_wf R"
    and conv: "cert_to_dl c = Some dc"
    and cc: "dl_closure_check (dl_rules R) (ast_classical_problem.const_names R) dc"
  shows "closure_check_exec R c"
proof -
  let ?U = "ast_classical_problem.const_names R"
  have facts_eq: "set (cert_facts c) = facty_of_dl ` set (dl_cert_facts dc)"
    using cert_to_dl_facts[OF conv] by simp
  have c1: "\<forall>f \<in> set (cert_facts c). is_predAtom f"
    using cert_to_dl_predAtom[OF conv] .

  have c2: "f \<in> set (cert_facts c)" if f: "f \<in> set (ast_classical_problem.init' R)" for f
  proof -
    from wf f have "is_predAtom f" unfolding dl_bridge_wf_def by blast
    then obtain p xs where fpx: "f = Atom (predAtm p xs)"
      by (cases f rule: is_predAtom.cases) auto
    have mem: "Cls p (map id.Cst xs) [] \<in> set (dl_rules R)"
      unfolding dl_rules_def using f by (force simp: in_set_map_filter fpx)
    have vars: "cls_vars (Cls p (map id.Cst xs) []) = []"
      by (induction xs) auto
    define \<sigma>0 :: "variable \<Rightarrow> object" where "\<sigma>0 = subst_of [] []"
    have \<sigma>0_in: "\<sigma>0 \<in> set (cls_substs ?U (Cls p (map id.Cst xs) []))"
      unfolding cls_substs_iff vars \<sigma>0_def by auto
    have head: "Datalog_Certificate.subst_atom \<sigma>0 (the_lh (Cls p (map id.Cst xs) [])) = (p, xs)"
      unfolding Datalog_Certificate.subst_atom_def by (simp add: comp_def)
    have inst: "(\<forall>g \<in> set (cls_guards (Cls p (map id.Cst xs) [])). eval_guard \<sigma>0 g)
        \<and> (\<forall>a \<in> set (cls_body_atoms (Cls p (map id.Cst xs) [])).
             Datalog_Certificate.subst_atom \<sigma>0 a \<in> set (dl_cert_facts dc))"
      by (simp add: cls_guards_def cls_body_atoms_def List.map_filter_simps)
    have "Datalog_Certificate.subst_atom \<sigma>0 (the_lh (Cls p (map id.Cst xs) []))
            \<in> set (dl_cert_facts dc)"
      using cc mem \<sigma>0_in inst unfolding dl_closure_check_def by blast
    then have "(p, xs) \<in> set (dl_cert_facts dc)" using head by simp
    then have "facty_of_dl (p, xs) \<in> set (cert_facts c)" using facts_eq by blast
    then show ?thesis using fpx by simp
  qed

  have c3: "set (consequence_of cl args) \<subseteq> set (cert_facts c)"
    if cl: "cl \<in> set (ast_classical_problem.a_clauses R)"
      and args: "args \<in> set (all_combos \<checkmark> (replicate (length (cl_params cl)) ?U))"
      and pre: "set (map (map_atom_fmla (ac_tsubst (cl_params cl) args)) (cl_pred_pre cl))
                  \<subseteq> set (cert_facts c)"
      and conds: "satisfies_conds (cl_params cl) (cl_cond_pre cl) args"
    for cl args
  proof
    fix h assume h: "h \<in> set (consequence_of cl args)"
    from wf cl have bw_pres: "\<forall>a \<in> set (cl_pred_pre cl). dl_pos_rh a \<noteq> None"
      and bw_pos: "\<forall>a \<in> set (cl_pos cl). is_predAtom a"
      and bw_cond: "\<forall>cnd \<in> set (cl_cond_pre cl).
                       dl_cond_rh cnd \<noteq> None
                       \<or> (\<forall>args'. \<not> satisfies_cond (cl_params cl) args' cnd)"
      and bw_vars: "\<forall>dcl \<in> set (dl_clauses_of_action_clause cl).
                       set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))"
      unfolding dl_bridge_wf_def by blast+
    have conds_nN: "\<forall>cnd \<in> set (cl_cond_pre cl). dl_cond_rh cnd \<noteq> None"
    proof
      fix cnd assume cnd: "cnd \<in> set (cl_cond_pre cl)"
      from conds cnd have "satisfies_cond (cl_params cl) args cnd"
        by (simp add: list_all_iff)
      then show "dl_cond_rh cnd \<noteq> None" using bw_cond cnd by blast
    qed
    from h obtain h0 where h0: "h0 \<in> set (cl_pos cl)"
      and h_eq: "h = map_atom_fmla (ac_tsubst (cl_params cl) args) h0"
      by (cases cl) auto
    from bw_pos h0 have "is_predAtom h0" by blast
    then obtain p ts where h0_eq: "h0 = Atom (predAtm p ts)"
      by (cases h0 rule: is_predAtom.cases) auto
    define body where
      "body = map (the \<circ> dl_pos_rh) (cl_pred_pre cl)
              @ List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl))"
    define dcl where "dcl = Cls p (map dl_id_of_term ts) body"
    have dcl_mem: "dcl \<in> set (dl_clauses_of_action_clause cl)"
      unfolding dcl_def body_def
      using dl_clause_intro[OF bw_pres conds_nN] h0 h0_eq by blast
    have dcl_rules: "dcl \<in> set (dl_rules R)"
      unfolding dl_rules_def using dcl_mem cl by auto
    have lh_dcl: "the_lh dcl = (p, map dl_id_of_term ts)" unfolding dcl_def by simp
    have body_atoms: "cls_body_atoms dcl = map dl_atom_of (cl_pred_pre cl)"
      unfolding dcl_def body_def cls_body_atoms_def
      by (simp add: map_filter_append body_atoms_of_pres[OF bw_pres]
                    body_atoms_of_conds[OF conds_nN])
    have guards_eq: "cls_guards dcl
                       = List.map_filter id (map (the \<circ> dl_cond_rh) (cl_cond_pre cl))"
      unfolding dcl_def body_def cls_guards_def
      by (simp add: guards_of_pres[OF bw_pres] guards_of_conds[OF conds_nN])

    define f where "f = the \<circ> map_of (zip (map fst (cl_params cl)) args)"
    define \<sigma>' where "\<sigma>' = subst_of (cls_vars dcl) (map f (cls_vars dcl))"
    have len: "length args = length (cl_params cl)" and aU: "set args \<subseteq> set ?U"
      using all_combos_replicateD[OF args] by auto
    have varsub: "set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))"
      using bw_vars dcl_mem by blast
    have \<sigma>'_in: "\<sigma>' \<in> set (cls_substs ?U dcl)"
      unfolding \<sigma>'_def f_def
      using subst_of_zip_in_cls_substs[OF varsub _ aU] len by simp
    have agree: "\<sigma>' v = f v" if "v \<in> set (cls_vars dcl)" for v
      unfolding \<sigma>'_def using that Datalog_Certificate.subst_of_map by fastforce
    have ac_f: "ac_tsubst (cl_params cl) args = subst_term f"
      unfolding f_def by simp

    have guards: "eval_guard \<sigma>' g" if g: "g \<in> set (cls_guards dcl)" for g
    proof -
      from g obtain cnd where cnd: "cnd \<in> set (cl_cond_pre cl)"
        and the_some: "the (dl_cond_rh cnd) = Some g"
        unfolding guards_eq by (auto simp: in_set_map_filter)
      with conds_nN have some: "dl_cond_rh cnd = Some (Some g)"
        by (metis option.collapse)
      have gvars: "\<forall>v \<in> set (rh_vars_list g). \<sigma>' v = f v"
      proof
        fix v assume v: "v \<in> set (rh_vars_list g)"
        have "g \<in> set (the_rhs dcl)" using g unfolding cls_guards_def by auto
        then have "v \<in> set (cls_vars dcl)"
          using v Datalog_Certificate.cls_vars_rhs_vars by blast
        then show "\<sigma>' v = f v" using agree by blast
      qed
      have "satisfies_cond (cl_params cl) args cnd"
        using conds cnd by (simp add: list_all_iff)
      then show ?thesis
        using eval_guard_transfer[OF some gvars] ac_f by simp
    qed

    have body_in: "Datalog_Certificate.subst_atom \<sigma>' a \<in> set (dl_cert_facts dc)"
      if a: "a \<in> set (cls_body_atoms dcl)" for a
    proof -
      from a body_atoms obtain a0 where a0: "a0 \<in> set (cl_pred_pre cl)"
        and a_eq: "a = dl_atom_of a0" by auto
      from bw_pres a0 have "dl_pos_rh a0 \<noteq> None" by blast
      then obtain p' ts' where a0_eq: "a0 = Atom (predAtm p' ts')"
        by (rule dl_pos_rh_not_NoneE)
      have a_eq': "a = (p', map dl_id_of_term ts')" using a_eq a0_eq by simp
      have agr': "\<forall>t \<in> set ts'. \<forall>v \<in> set (id_vars_list (dl_id_of_term t)). \<sigma>' v = f v"
      proof (intro ballI)
        fix t v assume t: "t \<in> set ts'" and v: "v \<in> set (id_vars_list (dl_id_of_term t))"
        have "PosLit p' (map dl_id_of_term ts') \<in> set (the_rhs dcl)"
          using a a_eq' Datalog_Certificate.cls_body_atoms_iff by fastforce
        moreover have "v \<in> set (rh_vars_list (PosLit p' (map dl_id_of_term ts')))"
          using t v by force
        ultimately have "v \<in> set (cls_vars dcl)"
          by (metis Datalog_Certificate.cls_vars_rhs_vars)
        then show "\<sigma>' v = f v" using agree by blast
      qed
      have "facty_of_dl (Datalog_Certificate.subst_atom \<sigma>' a)
              = map_atom_fmla (ac_tsubst (cl_params cl) args) a0"
        unfolding a_eq' a0_eq ac_f using facty_subst_atom_transfer[OF agr'] .
      moreover have "map_atom_fmla (ac_tsubst (cl_params cl) args) a0 \<in> set (cert_facts c)"
        using pre a0 by auto
      ultimately have "facty_of_dl (Datalog_Certificate.subst_atom \<sigma>' a)
                         \<in> facty_of_dl ` set (dl_cert_facts dc)"
        using facts_eq by simp
      then show ?thesis by auto
    qed

    have fire: "Datalog_Certificate.subst_atom \<sigma>' (the_lh dcl) \<in> set (dl_cert_facts dc)"
      using cc dcl_rules \<sigma>'_in guards body_in unfolding dl_closure_check_def by blast
    have head_vars: "\<forall>t \<in> set ts. \<forall>v \<in> set (id_vars_list (dl_id_of_term t)). \<sigma>' v = f v"
    proof (intro ballI)
      fix t v assume t: "t \<in> set ts" and v: "v \<in> set (id_vars_list (dl_id_of_term t))"
      have "dl_id_of_term t \<in> set (snd (the_lh dcl))" using t lh_dcl by simp
      then have "v \<in> set (cls_vars dcl)"
        using v Datalog_Certificate.cls_vars_head_vars by blast
      then show "\<sigma>' v = f v" using agree by blast
    qed
    have "facty_of_dl (Datalog_Certificate.subst_atom \<sigma>' (p, map dl_id_of_term ts))
            \<in> set (cert_facts c)"
      using fire facts_eq lh_dcl by auto
    then have "map_atom_fmla (subst_term f) (Atom (predAtm p ts)) \<in> set (cert_facts c)"
      using facty_subst_atom_transfer[OF head_vars] by simp
    then show "h \<in> set (cert_facts c)"
      using h_eq h0_eq ac_f by simp
  qed
  show ?thesis
    unfolding closure_check_exec_def Let_def using c1 c2 c3 by blast
qed

lemma dl_local_valid_imp_local_valid_exec:
  assumes "dl_bridge_wf R"
    and "cert_to_dl c = Some dc"
    and "i < length (nodes c)"
    and "dl_local_valid (dl_rules R) (ast_classical_problem.const_names R) dc i"
  shows "local_valid_exec R c i"
  sorry

subsection \<open>Main bridge theorem\<close>

theorem dl_admissible_imp_admissible_exec:
  assumes wf: "dl_bridge_wf R"
    and conv: "cert_to_dl c = Some dc"
    and adm: "dl_admissible (dl_rules R) (ast_classical_problem.const_names R) dc"
  shows "admissible_exec R c"
proof -
  from adm have oc: "dl_ordered_check dc"
    and cc: "dl_closure_check (dl_rules R) (ast_classical_problem.const_names R) dc"
    and lv: "\<forall>i < length (dl_nodes dc).
               dl_local_valid (dl_rules R) (ast_classical_problem.const_names R) dc i"
    unfolding dl_admissible_def by auto
  have "ordered_check_exec c" using cert_to_dl_ordered[OF conv] oc by simp
  moreover have "closure_check_exec R c"
    using dl_closure_imp_closure_exec[OF wf conv cc] .
  moreover have "local_valid_exec R c i" if "i < length (nodes c)" for i
    using dl_local_valid_imp_local_valid_exec[OF wf conv that] lv cert_to_dl_len[OF conv] that
    by simp
  ultimately show ?thesis unfolding admissible_exec_def by simp
qed


section \<open>PDDL reachability is the minimal model of the translated program\<close>

text \<open>The semantic core behind the check-level bridge. A PDDL \<^typ>\<open>fact\<close> and a ground datalog
  fact are the \<^emph>\<open>same type\<close> (\<^typ>\<open>predicate \<times> object list\<close>), so the achievable facts of the
  relaxed problem can be compared directly with the \<^emph>\<open>minimal datalog model\<close> of the translated
  program --- \<^const>\<open>dl_derivable\<close>, the least model of the positive program \<^const>\<open>dl_rules\<close>
  with substitutions drawn from the object universe. Under the translation well-formedness
  bundle \<^const>\<open>dl_bridge_wf\<close> they coincide.

  Downstream, the two inclusions play the two familiar roles:
  \<^item> \<open>\<subseteq>\<close> (every achievable fact is derivable) is the \<^emph>\<open>soundness\<close> direction: together with the
    generic \<open>dl_certified_model_correct\<close> (certified facts = minimal model) it turns a
    generic-checker acceptance directly into the PDDL reachability requirements --- the
    conclusions of \<open>closure_sound\<close> and \<open>cert_ops_sound\<close> --- without per-check transfer.
  \<^item> \<open>\<supseteq>\<close> (every derivable fact is achievable) is the \<^emph>\<open>tightness\<close> direction: the minimal model
    contains no junk, so the grounder output is not bloated with unreachable facts.

  Proof plan (see \<open>WIP_datalog_cert_bridge.md\<close>): \<open>\<subseteq>\<close> mirrors \<open>closure_invariant\<close> /
  \<open>closure_step_adds\<close> with \<open>dl_derivable\<close>-closure in place of certificate membership; the
  substitution/guard machinery above (\<open>subst_of_zip_in_cls_substs\<close>,
  \<open>facty_subst_atom_transfer\<close>, \<open>eval_guard_transfer\<close>) supplies the generic ground instance for
  each fired action. \<open>\<supseteq>\<close> is rule induction on \<open>dl_derivable\<close>: a derivation step comes from a
  translated action clause (fire that action --- relaxation makes earlier facts persist) or
  from a fact clause of \<open>init'\<close> (achievable at the initial model).\<close>

context pddl_datalog
begin

lemma achievable_imp_dl_derivable:
  assumes "dl_bridge_wf P" and "achievable f"
  shows "dl_derivable (dl_rules P) const_names f"
  sorry

lemma dl_derivable_imp_achievable:
  assumes "dl_bridge_wf P" and "dl_derivable (dl_rules P) const_names f"
  shows "achievable f"
  sorry

theorem achievable_eq_minimal_model:
  assumes "dl_bridge_wf P"
  shows "{f. achievable f} = {f. dl_derivable (dl_rules P) const_names f}"
  using achievable_imp_dl_derivable[OF assms] dl_derivable_imp_achievable[OF assms] by blast

text \<open>The facts requirement, discharged by a certified minimal model: any fact list \<open>M\<close> that
  the generic checker certifies to be the minimal model over-approximates (indeed captures
  exactly) the achievable facts --- the conclusion of \<open>closure_sound\<close> without running the PDDL
  closure check.\<close>
theorem minimal_model_facts_requirement:
  assumes wf: "dl_bridge_wf P"
    and model: "set M = {f. dl_derivable (dl_rules P) const_names f}"
  shows "fact_to_facty ` {f. achievable f} \<subseteq> facty_of_dl ` set M"
proof -
  have sub: "{f. achievable f} \<subseteq> set M"
    using achievable_imp_dl_derivable[OF wf] model by blast
  have "fact_to_facty f = facty_of_dl f" for f by (cases f) simp
  with sub show ?thesis by auto
qed

text \<open>The ops requirement, discharged by a certified minimal model: every applicable plan
  action lands in the \<open>cert_ops\<close> enumeration of any certificate whose facts cover the minimal
  model --- the conclusion of \<open>cert_ops_sound\<close> without the PDDL closure check. Proof plan:
  an applicable action is enabled in some reachable world model \<open>W\<close>; every fact of \<open>fst W\<close> is
  achievable, hence (by \<open>achievable_imp_dl_derivable\<close>) in the minimal model, hence in
  \<open>set (cert_facts c)\<close>; then \<open>enabled_clause_body\<close> + \<open>action_params_match_combos\<close> give the
  membership condition of the finite enumeration, as in \<open>cert_ops_sound\<close>.\<close>
theorem minimal_model_ops_requirement:
  assumes wf: "dl_bridge_wf P"
    and cover: "fact_to_facty ` {f. dl_derivable (dl_rules P) const_names f}
                  \<subseteq> set (cert_facts c)"
  shows "{\<pi>. applicable \<pi>} \<subseteq> set (cert_ops c)"
  sorry

end

end

