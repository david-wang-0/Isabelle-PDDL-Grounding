theory PDDL_Reachability_Locales
  imports Reachability_Analysis Grounded_PDDL.Grounded_PDDL
    Datalog_Certification.Datalog_Certificate
    Grounding_Classical_Common.Numeric_Free Grounding_Reachability_Analysis.Reachability_Formula_Helpers
begin

text \<open>\<^theory>\<open>Stratified_Datalog.Datalog\<close>'s \<^typ>\<open>('x, 'c) id\<close> constructors would otherwise capture
  the unqualified \<open>Var\<close> of PDDL \<^typ>\<open>variable\<close> in every downstream theory; we only ever use them
  qualified (\<^const>\<open>id.Var\<close> / \<^const>\<open>id.Cst\<close>).\<close>
hide_const (open) Datalog.id.Var Datalog.id.Cst

section \<open>Reachability via a verified datalog certificate\<close>

text \<open>
  This theory replaces direct, unverified forward-chaining reachability on the PDDL problem
  with a \<^emph>\<open>certificate-checking\<close> approach:

  \<^item> an (untrusted) datalog engine --- the generic \<open>Datalog_Evaluation.dl_eval\<close> of the
    \<open>Datalog_Certification\<close> session, run on the translated program --- produces a certificate of
    the reachable facts;
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
  have "is_predAtom g" using Cons.prems by simp
  then obtain p' args' where g: "g = Atom (predAtm p' args')"
    by (cases g rule: is_predAtom.cases) auto
  have ih: "in_orga (Atom (predAtm p args)) (update_facts fs orga)
              \<longleftrightarrow> args \<in> set (orga p) \<or> Atom (predAtm p args) \<in> set fs"
    using Cons.prems Cons.IH by simp
  show ?case
  proof (cases "p' = p")
    case True
    thus ?thesis using g ih by (auto simp: Let_def)
  next
    case False
    thus ?thesis using g ih by (simp add: Let_def)
  qed
qed

lemma in_orga_organize_facts:
  assumes "\<forall>g \<in> set fs. is_predAtom g"
  shows "in_orga (Atom (predAtm p args)) (organize_facts fs)
           \<longleftrightarrow> Atom (predAtm p args) \<in> set fs"
  using in_orga_update_facts[OF assms, of p args "\<lambda>_. []"] by simp




lemma un_and_map_atom_fmla: "un_and (map_atom_fmla \<sigma> F) = map (map_atom_fmla \<sigma>) (un_and F)"
  by (induction F rule: un_and.induct) auto

lemma cond_lit_model_indep:
  assumes "is_pos_lit c" "\<not> is_predAtom c"
  shows "valuation M \<Turnstile>\<^sub>m map_atom_fmla \<sigma> c \<longleftrightarrow> valuation M' \<Turnstile>\<^sub>m map_atom_fmla \<sigma> c"
  using assms by (cases c rule: is_pos_lit.cases) (auto simp: valuation_def)

subsection \<open>Locale A: admissible certificates for a relaxed problem\<close>

text \<open>The checker runs on a \<^emph>\<open>relaxed\<close> problem (positive preconditions, single datalog
  stratum), so the immediate-consequence operator is monotone. \<^locale>\<open>relaxed_problem\<close>
  bundles well-formedness, normalization and relaxation. In the pipeline it is interpreted at
  the relaxed problem \<open>P\<^sub>R\<close>.\<close>

locale pddl_datalog = relaxed_problem


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

text \<open>The shared datalog clause body of an action clause: one \<^const>\<open>PosLit\<close> per positive
  precondition atom plus the surviving \<^const>\<open>Eql\<close>/\<^const>\<open>Neql\<close> equality guards. Every clause
  emitted for the action clause (one per add-effect) carries this same body, so it is factored out.\<close>
definition dl_clause_body :: "action_clause \<Rightarrow> (predicate, variable, object) rh list" where
  "dl_clause_body cl =
     map the (map dl_pos_rh (cl_pred_pre cl))
     @ List.map_filter id (map the (map dl_cond_rh (cl_cond_pre cl)))"

definition dl_clauses_of_action_clause :: "action_clause \<Rightarrow> pddl_dl_clause list" where
  [code]: "dl_clauses_of_action_clause cl \<equiv>
     (let conds = map dl_cond_rh (cl_cond_pre cl);
          pres = map dl_pos_rh (cl_pred_pre cl)
      in if None \<in> set conds \<or> None \<in> set pres then []
         else
           List.map_filter
             (\<lambda>f. case f of Atom (predAtm p ts) \<Rightarrow> Some (Cls p (map dl_id_of_term ts) (dl_clause_body cl))
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
text \<open>Named per-action-clause sub-conditions of the bundle, so the definition and its rules read
  declaratively instead of as a nested \<open>\<forall>\<close>/\<open>\<forall>x\<in>set\<close> term.\<close>
definition dl_pre_translates :: "action_clause \<Rightarrow> bool" where
  "dl_pre_translates cl \<longleftrightarrow> (\<forall>a \<in> set (cl_pred_pre cl). dl_pos_rh a \<noteq> None)"

definition dl_adds_predAtoms :: "action_clause \<Rightarrow> bool" where
  "dl_adds_predAtoms cl \<longleftrightarrow> (\<forall>a \<in> set (cl_pos cl). is_predAtom a)"

definition dl_cond_translates :: "action_clause \<Rightarrow> bool" where
  "dl_cond_translates cl \<longleftrightarrow> (\<forall>cnd \<in> set (cl_cond_pre cl).
       dl_cond_rh cnd \<noteq> None \<or> (\<forall>args. \<not> satisfies_cond (cl_params cl) args cnd))"

definition dl_clause_vars_params :: "action_clause \<Rightarrow> bool" where
  "dl_clause_vars_params cl \<longleftrightarrow> (\<forall>dcl \<in> set (dl_clauses_of_action_clause cl).
       set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl)))"

definition dl_bridge_wf where
  "dl_bridge_wf R \<longleftrightarrow>
     (\<forall>cl \<in> set (ast_classical_problem.a_clauses R).
        dl_pre_translates cl \<and> dl_adds_predAtoms cl
        \<and> dl_cond_translates cl \<and> dl_clause_vars_params cl)
     \<and> (\<forall>f \<in> set (ast_classical_problem.init' R). is_predAtom f)
     \<and> ast_classical_problem.const_names R \<noteq> []"

text \<open>Introduction / elimination / destruction rules for the bundle. Following the project
  convention, they are stated with the \<open>\<And>\<close> (big-and) meta-binder rather than HOL \<open>\<forall>\<close>/\<open>\<forall>x\<in>set\<close>,
  and reach all the way down to the element-level facts, so consuming proofs never re-derive the
  nested quantifier structure.\<close>
lemma dl_bridge_wfI [intro]:
  assumes "\<And>cl a. cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> a \<in> set (cl_pred_pre cl)
             \<Longrightarrow> dl_pos_rh a \<noteq> None"
    and "\<And>cl a. cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> a \<in> set (cl_pos cl)
             \<Longrightarrow> is_predAtom a"
    and "\<And>cl cnd. cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> cnd \<in> set (cl_cond_pre cl)
             \<Longrightarrow> dl_cond_rh cnd \<noteq> None \<or> (\<forall>args. \<not> satisfies_cond (cl_params cl) args cnd)"
    and "\<And>cl dcl. cl \<in> set (ast_classical_problem.a_clauses R)
             \<Longrightarrow> dcl \<in> set (dl_clauses_of_action_clause cl)
             \<Longrightarrow> set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))"
    and "\<And>f. f \<in> set (ast_classical_problem.init' R) \<Longrightarrow> is_predAtom f"
    and "ast_classical_problem.const_names R \<noteq> []"
  shows "dl_bridge_wf R"
  using assms unfolding dl_bridge_wf_def dl_pre_translates_def dl_adds_predAtoms_def
    dl_cond_translates_def dl_clause_vars_params_def by blast

lemma dl_bridge_wfE [elim]:
  assumes "dl_bridge_wf R"
  obtains "\<And>cl a. cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> a \<in> set (cl_pred_pre cl)
             \<Longrightarrow> dl_pos_rh a \<noteq> None"
    and "\<And>cl a. cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> a \<in> set (cl_pos cl)
             \<Longrightarrow> is_predAtom a"
    and "\<And>cl cnd. cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> cnd \<in> set (cl_cond_pre cl)
             \<Longrightarrow> dl_cond_rh cnd \<noteq> None \<or> (\<forall>args. \<not> satisfies_cond (cl_params cl) args cnd)"
    and "\<And>cl dcl. cl \<in> set (ast_classical_problem.a_clauses R)
             \<Longrightarrow> dcl \<in> set (dl_clauses_of_action_clause cl)
             \<Longrightarrow> set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))"
    and "\<And>f. f \<in> set (ast_classical_problem.init' R) \<Longrightarrow> is_predAtom f"
    and "ast_classical_problem.const_names R \<noteq> []"
  using assms unfolding dl_bridge_wf_def dl_pre_translates_def dl_adds_predAtoms_def
    dl_cond_translates_def dl_clause_vars_params_def by blast

lemma dl_bridge_wf_pred_preD [dest]:
  "dl_bridge_wf R \<Longrightarrow> cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> a \<in> set (cl_pred_pre cl)
     \<Longrightarrow> dl_pos_rh a \<noteq> None"
  unfolding dl_bridge_wf_def dl_pre_translates_def by blast

lemma dl_bridge_wf_posD [dest]:
  "dl_bridge_wf R \<Longrightarrow> cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> a \<in> set (cl_pos cl)
     \<Longrightarrow> is_predAtom a"
  unfolding dl_bridge_wf_def dl_adds_predAtoms_def by blast

lemma dl_bridge_wf_condD [dest]:
  "dl_bridge_wf R \<Longrightarrow> cl \<in> set (ast_classical_problem.a_clauses R) \<Longrightarrow> cnd \<in> set (cl_cond_pre cl)
     \<Longrightarrow> dl_cond_rh cnd \<noteq> None \<or> (\<forall>args. \<not> satisfies_cond (cl_params cl) args cnd)"
  unfolding dl_bridge_wf_def dl_cond_translates_def by blast

lemma dl_bridge_wf_varsD [dest]:
  "dl_bridge_wf R \<Longrightarrow> cl \<in> set (ast_classical_problem.a_clauses R)
     \<Longrightarrow> dcl \<in> set (dl_clauses_of_action_clause cl)
     \<Longrightarrow> set (cls_vars dcl) \<subseteq> set (map fst (cl_params cl))"
  unfolding dl_bridge_wf_def dl_clause_vars_params_def by blast

lemma dl_bridge_wf_initD [dest]:
  "dl_bridge_wf R \<Longrightarrow> f \<in> set (ast_classical_problem.init' R) \<Longrightarrow> is_predAtom f"
  unfolding dl_bridge_wf_def by blast

lemma dl_bridge_wf_const_namesD [dest]:
  "dl_bridge_wf R \<Longrightarrow> ast_classical_problem.const_names R \<noteq> []"
  unfolding dl_bridge_wf_def by blast


subsection \<open>The grounding-input locale: numeric-free, delete-relaxed, well-translated\<close>

text \<open>On top of \<^locale>\<open>pddl_datalog\<close> and \<^locale>\<open>numeric_free_problem\<close>, fixing a
  non-empty object universe, numeric-freeness (\<open>nne\<close>), delete relaxation (\<open>nd\<close>, inherited)
  and the translation bundle (\<open>bridge\<close>) are all available as facts --- so every tightness
  lemma below lives here without explicit \<open>nne\<close>/\<open>nd\<close>/\<open>dl_bridge_wf\<close> hypotheses.\<close>
locale num_free_relaxed_problem = pddl_datalog + numeric_free_problem +
  assumes nonempty: "const_names \<noteq> []"

subsection \<open>The certified-grounding-input locale: a fixed accepted certificate\<close>

text \<open>On top of \<^locale>\<open>num_free_relaxed_problem\<close>, fix a list \<open>M\<close> and certificate \<open>dc\<close> that the
  \<^emph>\<open>generic\<close> datalog checker accepts as the minimal model of the translated program
  \<^const>\<open>dl_rules\<close> over the object universe \<^const>\<open>ast_classical_problem.const_names\<close>. Then the PDDL reachable-fact
  set is available \<^emph>\<open>hypothesis-free\<close> as the fact \<open>certified_facts_eq_reachable\<close>:
  \<^term>\<open>set M = {f. achievable f}\<close>. This is the grounding-input locale the downstream grounder
  consumes --- it needs the achievable facts as a concrete enumerated list, with no PDDL-specific
  reachability check.\<close>
locale certified_pddl = num_free_relaxed_problem +
  fixes M and dc
  assumes cert: "dl_certified_model (set (dl_rules P)) (set const_names) M dc"

end
