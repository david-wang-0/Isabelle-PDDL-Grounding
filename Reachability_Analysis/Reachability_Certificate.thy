theory Reachability_Certificate
  imports Reachability_Analysis Grounded_PDDL.Grounded_PDDL
    Datalog_Certification.Datalog_Certificate
begin

text \<open>\<^theory>\<open>Stratified_Datalog.Datalog\<close>'s \<^typ>\<open>('x, 'c) id\<close> constructors would otherwise capture
  the unqualified \<open>Var\<close> of PDDL \<^typ>\<open>variable\<close> in every downstream theory; we only ever use them
  qualified (\<^const>\<open>id.Var\<close> / \<^const>\<open>id.Cst\<close>).\<close>
hide_const (open) Datalog.id.Var Datalog.id.Cst

section \<open>Reachability via a verified datalog certificate\<close>

text \<open>
  This theory replaces the unverified \<open>ast_classical_problem.semi_naive_eval\<close>
  reachability (whose correctness theorems \<open>found_facts_achievable\<close> /
  \<open>found_pactions_applicable\<close> in theory \<open>Reachability_Analysis\<close> are still \<^bold>\<open>sorry\<close>)
  with a \<^emph>\<open>certificate-checking\<close> approach:

  \<^item> an (untrusted) datalog engine produces a certificate of the reachable facts;
  \<^item> a verified kernel re-checks that the certificate facts are \<^emph>\<open>closed\<close> under one-step
    derivation (a model of the immediate-consequence operator);
  \<^item> only a closure-checked certificate is fed to \<^locale>\<open>wf_grounder\<close>.

  Design notes live in \<open>ARCHITECTURE_datalog_certification.md\<close> (repo root), with the Lean 4
  \<open>CertifyingDatalog\<close> development as the reference checker.

  Key asymmetry that \<^locale>\<open>wf_grounder\<close> exploits:
  \<^item> \<^bold>\<open>closure check = soundness (\<supseteq>)\<close>: the certificate facts form a model of the
    immediate-consequence operator, so they over-approximate the reachable set. This is all
    the pipeline's correctness theorems need, and is the only check kept here.
  \<^item> \<^bold>\<open>tightness (\<subseteq>)\<close>: every certificate fact is genuinely derivable; this gives exact
    equality and is now established \<^emph>\<open>semantically\<close> (the minimal-model relation below), via the
    generic positive-datalog checker of \<^theory>\<open>Datalog_Certification.Datalog_Certificate\<close>.
\<close>

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



end


text \<open>The PDDL-specific certificate data structure and its closure / ops checking layer
  (\<open>cert_node\<close> / \<open>certificate\<close>, \<open>cert_facts\<close>, \<open>closure_check\<close> / \<open>closure_sound\<close>,
  \<open>cert_ops\<close> / \<open>cert_ops_sound\<close>) were removed. Reachability is now related to an \<^emph>\<open>abstract\<close>
  datalog certificate (the generic \<^typ>\<open>('p, 'c) dl_certificate\<close> of
  \<^theory>\<open>Datalog_Certification.Datalog_Certificate\<close>) purely semantically, via the minimal-model
  relation below (\<open>certified_facts_eq_achievable\<close>). Downstream theories that consumed
  \<open>cert_facts\<close> / \<open>cert_ops\<close> / \<open>closure_sound\<close> (e.g. \<open>Certified_Grounding\<close>) will need
  re-wiring onto that generic entry point --- see the handover.\<close>


section \<open>The PDDL \<open>\<rightarrow>\<close> datalog serialization\<close>

text \<open>The reachability oracle's input is phrased in the AFP \<open>Stratified_Datalog\<close> clause syntax
  (\<^typ>\<open>('p, 'x, 'c) clause\<close>): one \<^const>\<open>Cls\<close> per add-effect of each action clause --- body =
  one \<^const>\<open>PosLit\<close> per positive precondition atom plus \<^const>\<open>Eql\<close>/\<^const>\<open>Neql\<close> filters for
  the equality conditions --- and one bodyless ground clause per initial fact. The condition
  translation mirrors the kernel's \<open>satisfies_cond\<close> semantics (literals evaluated in the
  \<^emph>\<open>empty\<close> world model): \<open>\<^bold>\<not>\<bottom>\<close> and negated predicate atoms are unconditionally true and are
  dropped; a \<open>\<bottom>\<close> condition makes the clause statically unsatisfiable, so the whole clause is
  omitted. This is the \<^emph>\<open>translated program\<close> \<^const>\<open>dl_rules\<close> whose minimal model the section
  below identifies with the PDDL-achievable facts. The program is \<^emph>\<open>transport only\<close>: an untrusted
  engine runs on it and returns a certificate, which the kernel re-checks against the
  \<^const>\<open>ast_classical_problem.a_clauses\<close> it recomputes itself --- never against this
  serialization, so no proofs depend on it.\<close>

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
  per action clause plus one bodyless ground fact clause per initial fact. This is the positive
  datalog program whose least model the section below identifies with the PDDL-achievable facts.\<close>
definition dl_rules where
  [code]: "dl_rules R \<equiv>
     concat (map dl_clauses_of_action_clause (ast_classical_problem.a_clauses R))
     @ List.map_filter dl_fact_clause (ast_classical_problem.init' R)"



section \<open>Well-formedness bundle for the PDDL \<rightarrow> datalog translation\<close>

text \<open>The check-level bridge (the @{text cert_to_dl} certificate conversion and the per-check
  transfer lemmas) was removed: the generic checker of
  \<^theory>\<open>Datalog_Certification.Datalog_Certificate\<close> moved to an index-free, set-based form, so
  the relation between an accepted certificate and PDDL reachability is now established
  \<^emph>\<open>semantically\<close> --- the achievable facts of the relaxed problem are exactly the minimal model
  of the translated program (section below), which combined with the generic
  \<open>dl_certified_model_correct\<close> (certified facts = minimal model) yields the reachability
  facts directly, without transferring each check.

  What survives from the old bridge is the translation well-formedness bundle, the hypothesis
  under which the PDDL serialization \<^const>\<open>dl_rules\<close> faithfully mirrors the action clauses.\<close>

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

text \<open>\<^bold>\<open>Base core (still \<^bold>\<open>sorry\<close>):\<close> every initial fact is derivable --- it is the head of a
  bodyless ground fact clause \<^const>\<open>dl_fact_clause\<close> in \<^const>\<open>dl_rules\<close>, fired by the vacuous
  substitution.\<close>
lemma derivable_init:
  assumes wf: "dl_bridge_wf P"
    and mem: "Atom (predAtm p xs) \<in> fst I"
  shows "datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs)"
proof -
  from mem have "Atom (predAtm p xs) \<in> set (init P)"
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
             datalog_prog.derivable (set const_names) (set (dl_rules P)) (subst_atom (\<lambda>_. undefined) a)"
    by (simp add: cls_body_atoms_def List.map_filter_simps)
  have "datalog_prog.derivable (set const_names) (set (dl_rules P))
          (subst_atom (\<lambda>_. undefined) (the_lh (Cls p (map id.Cst xs) [] :: pddl_dl_clause)))"
    using datalog_prog.derivable.derive[OF cl v g b] .
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
  from assms(2) obtain i where "i < length args" "args ! i = a"
    by (auto simp: in_set_conv_nth)
  then have "is_obj_of_type a (map snd (parameters h) ! i)"
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
  from x len obtain y where y: "map_of (zip (map fst ps) args) x = Some y"
    by (metis map_of_zip_is_Some)
  hence "(x, y) \<in> set (zip (map fst ps) args)" by (rule map_of_SomeD)
  hence "y \<in> set args" by (rule set_zip_rightD)
  moreover have "ac_tsubst ps args (term.VAR x) = y" using y by simp
  ultimately show ?thesis by simp
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

text \<open>\<^bold>\<open>Step core (still \<^bold>\<open>sorry\<close>):\<close> the add-effects of an enabled action are derivable, given
  that the current world-model facts are. The fired action's translated clause supplies the
  generic ground instance (substitution from the action arguments, body atoms from the
  hypothesis, equality guards from \<^const>\<open>satisfies_conds\<close>).\<close>
lemma derivable_step_adds:
  assumes wf: "dl_bridge_wf P" and en: "plan_action_enabled a M"
    and IH: "\<forall>p xs. Atom (predAtm p xs) \<in> fst M
               \<longrightarrow> datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs)"
    and mem: "Atom (predAtm p xs) \<in> set (adds (effect ((the \<circ> res_inst) a)))"
  shows "datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs)"
  sorry

text \<open>The derivability invariant carried along a valid plan, proved from \<open>derivable_step_adds\<close>:
  every fact of a reachable world model is derivable, given the initial facts are.\<close>
lemma derivable_invariant:
  assumes wf: "dl_bridge_wf P"
  shows "valid_classical_plan_alt M \<pi>s M'
         \<Longrightarrow> (\<forall>p xs. Atom (predAtm p xs) \<in> fst M
                \<longrightarrow> datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs))
         \<Longrightarrow> (\<forall>p xs. Atom (predAtm p xs) \<in> fst M'
                \<longrightarrow> datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs))"
proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons a \<pi>s)
  let ?a' = "(the \<circ> res_inst) a"
  from Cons.prems(1) have en: "plan_action_enabled a M"
    and rest: "valid_classical_plan_alt (execute_plan_action a M) \<pi>s M'" by simp_all
  obtain L N where M: "M = (L, N)" by (cases M)
  have fstM': "fst (execute_plan_action a M)
                 = (L - set (dels (effect ?a'))) \<union> set (adds (effect ?a'))"
    unfolding execute_plan_action_def M using apply_ground_action_alt[of ?a' L N] by simp
  have step: "\<forall>p xs. Atom (predAtm p xs) \<in> fst (execute_plan_action a M)
                \<longrightarrow> datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs)"
  proof (intro allI impI)
    fix p xs assume "Atom (predAtm p xs) \<in> fst (execute_plan_action a M)"
    then have "Atom (predAtm p xs) \<in> L \<or> Atom (predAtm p xs) \<in> set (adds (effect ?a'))"
      unfolding fstM' by auto
    thus "datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs)"
    proof
      assume "Atom (predAtm p xs) \<in> L"
      then have "Atom (predAtm p xs) \<in> fst M" using M by simp
      thus ?thesis using Cons.prems(2) by blast
    next
      assume "Atom (predAtm p xs) \<in> set (adds (effect ?a'))"
      thus ?thesis using derivable_step_adds[OF wf en Cons.prems(2)] by blast
    qed
  qed
  show ?case using Cons.IH[OF rest step] .
qed

subsection \<open>The minimal-model relation\<close>

lemma achievable_imp_dl_derivable:
  assumes wf: "dl_bridge_wf P" and ach: "achievable f"
  shows "datalog_prog.derivable (set const_names) (set (dl_rules P)) f"
proof -
  from ach obtain \<pi>s M where vp: "valid_classical_plan_alt I \<pi>s M"
    and mem: "Atom (uncurry predAtm f) \<in> fst M"
    unfolding achievable_def by auto
  obtain p xs where f: "f = (p, xs)" by (cases f)
  have init: "\<forall>p xs. Atom (predAtm p xs) \<in> fst I
                \<longrightarrow> datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs)"
    using derivable_init[OF wf] by blast
  have allM: "\<forall>p xs. Atom (predAtm p xs) \<in> fst M
                \<longrightarrow> datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs)"
    using derivable_invariant[OF wf vp init] .
  have "Atom (predAtm p xs) \<in> fst M" using mem f by simp
  with allM have "datalog_prog.derivable (set const_names) (set (dl_rules P)) (p, xs)" by blast
  thus ?thesis using f by simp
qed

lemma dl_derivable_imp_achievable:
  assumes wf: "dl_bridge_wf P"
    and der: "datalog_prog.derivable (set const_names) (set (dl_rules P)) f"
  shows "achievable f"
proof -
  note ind = datalog_prog.derivable.induct[consumes 1, case_names step]
  show ?thesis using der
  proof (induction rule: ind)
    case (step cl \<sigma>)
    text \<open>\<^bold>\<open>(still \<^bold>\<open>sorry\<close>)\<close> \<open>cl\<close> is a clause of \<^const>\<open>dl_rules\<close>: either a translated
      action clause --- fire that action, whose positive precondition body instances are
      achievable by \<open>step.IH\<close> and whose equality guards hold --- or a bodyless fact clause from
      \<open>init'\<close>, achievable at the initial model. Either way the head instance is achievable.\<close>
    show ?case sorry
  qed
qed

theorem achievable_eq_minimal_model:
  assumes "dl_bridge_wf P"
  shows "{f. achievable f} = {f. datalog_prog.derivable (set const_names) (set (dl_rules P)) f}"
  using achievable_imp_dl_derivable[OF assms] dl_derivable_imp_achievable[OF assms] by blast

subsection \<open>Relating an admissible certificate to PDDL reachability\<close>

text \<open>The capstone: any list \<open>M\<close> that the \<^emph>\<open>generic\<close> checker certifies to be the minimal model of
  the translated program \<^const>\<open>dl_rules\<close> (over the object universe) is \<^emph>\<open>exactly\<close> the set of
  PDDL-achievable facts of the relaxed problem. An accepted \<^const>\<open>dl_admissible\<close> certificate
  thus yields the reachable-fact set by theorem, with no PDDL-specific check.\<close>
theorem certified_facts_eq_achievable:
  assumes wf: "dl_bridge_wf P"
    and cert: "dl_certified_model (set (dl_rules P)) (set const_names) M dc"
  shows "set M = {f. achievable f}"
proof -
  have "{f. achievable f} = {f. datalog_prog.derivable (set const_names) (set (dl_rules P)) f}"
    by (rule achievable_eq_minimal_model[OF wf])
  with dl_certified_model_correct[OF cert] show ?thesis by simp
qed

text \<open>The facts requirement, discharged by a certified minimal model: the facts of any certified
  minimal model capture exactly the achievable facts --- the facts-soundness direction,
  established without any PDDL-specific closure check.\<close>
theorem minimal_model_facts_requirement:
  assumes wf: "dl_bridge_wf P"
    and model: "set M = {f. datalog_prog.derivable (set const_names) (set (dl_rules P)) f}"
  shows "fact_to_facty ` {f. achievable f} \<subseteq> fact_to_facty ` set M"
proof -
  have "{f. achievable f} \<subseteq> set M"
    using achievable_imp_dl_derivable[OF wf] model by blast
  thus ?thesis by (rule image_mono)
qed

end

end

