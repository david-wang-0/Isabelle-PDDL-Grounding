theory Reachability_Certificate
  imports Reachability_Analysis Grounded_PDDL.Grounded_PDDL
begin

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
  \<open>WIP_reachability_datalog.md\<close> and \<open>WIP_nemo_certificate_format.md\<close> (repo root), with
  \<open>~/work/CertifyingDatalog\<close> (Lean 4) as the reference checker.

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

end

