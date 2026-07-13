theory Classical_Certified_Grounding_Locales
  imports Classical_PDDL_Reachability_Certificate "Classical_PDDL_Relaxation.Classical_PDDL_Relaxation_Semantics"
    Grounding_Classical_Common.PDDL_Orderings
begin

section \<open>Certificate-to-grounder bridge: locale and definitions\<close>

text \<open>This connects the relaxed-problem reachability certificate --- the generic
  \<^const>\<open>dl_certified_model\<close> of the translated program \<^const>\<open>dl_rules\<close>, related to PDDL
  reachability by \<open>certified_facts_eq_achievable\<close> --- to the grounder \<^locale>\<open>wf_grounder\<close>, so
  that the grounder targets the \<^emph>\<open>un-relaxed\<close> problem \<open>P\<close> (real add+delete effects), using the
  relaxed reachable set only as the pruning oracle.\<close>

subsection \<open>Step 1: the relaxation \<open>PX\<close> is a \<^locale>\<open>pddl_datalog\<close>\<close>

text \<open>\<open>PX\<close> (the delete-relaxation of a normalized problem) is a \<^locale>\<open>normalized_problem\<close> (the
  existing \<open>px\<close> sublocale) and satisfies \<open>relax_relaxes\<close>; since \<^locale>\<open>pddl_datalog\<close> adds nothing
  to \<^locale>\<open>relaxed_problem\<close>, \<open>PX\<close> is a \<^locale>\<open>pddl_datalog\<close>. This exposes the reachability kernel
  (\<open>achievable\<close>, \<open>enabled_clause_body\<close>, \<dots>) instantiated at \<open>PX\<close> under the \<open>px\<close> prefix.\<close>

sublocale normalized_problem_rx \<subseteq> px: pddl_datalog PX
  unfolding pddl_datalog_def
  by (simp add: normalized_problem_def' relaxed_problem.intro relaxed_problem_axioms_def
                relax_wf relax_normed relax_relaxes)

subsection \<open>Step 2/3: certificate-derived facts/ops and the grounding well-formedness check\<close>

subsection \<open>Fact-driven join for the certified ops\<close>

text \<open>\<open>cert_ops_of\<close> below reads the applicable ops off the certificate by a fact-driven join
  instead of the \<open>|const_names|\<close>-to-the-arity product: the positive precondition atoms of each
  clause are unified against the certified facts (indexed by predicate via \<^const>\<open>organize_facts\<close>),
  binding the clause variables to objects that actually occur in reachable facts; variables not
  constrained by any positive precondition are crossed with the universe, and the equality guards
  are applied afterwards.  Only the enumeration changes; the over-approximation lemma
  \<open>px_applicable_super\<close> is re-established via \<open>cert_ops_of_complete\<close>.\<close>

fun punify :: "(variable \<times> object) list \<Rightarrow> term list \<Rightarrow> object list \<Rightarrow> (variable \<times> object) list option" where
  "punify b (term.VAR v # ts) (ob # os) =
     (case map_of b v of Some ob2 \<Rightarrow> (if ob2 = ob then punify b ts os else None)
                       | None \<Rightarrow> punify ((v, ob) # b) ts os)"
| "punify b (term.CONST c # ts) (ob # os) = (if c = ob then punify b ts os else None)"
| "punify b [] [] = Some b"
| "punify b _ _ = None"

definition pmatch_atom :: "fact_orga \<Rightarrow> (variable \<times> object) list \<Rightarrow> term atom formula \<Rightarrow> (variable \<times> object) list list" where
  "pmatch_atom orga b a =
     (case a of Atom (predAtm p ts) \<Rightarrow> List.map_filter (punify b ts) (orga p) | _ \<Rightarrow> [])"

fun pjoin :: "fact_orga \<Rightarrow> (variable \<times> object) list \<Rightarrow> term atom formula list \<Rightarrow> (variable \<times> object) list list" where
  "pjoin orga b [] = [b]"
| "pjoin orga b (a # as) = concat (map (\<lambda>b'. pjoin orga b' as) (pmatch_atom orga b a))"

fun ptuples :: "object list \<Rightarrow> (variable \<times> object) list \<Rightarrow> variable list \<Rightarrow> object list list" where
  "ptuples allobjs b [] = [[]]"
| "ptuples allobjs b (v # vs) =
     concat (map (\<lambda>a. map (\<lambda>t. a # t) (ptuples allobjs b vs))
                 (case map_of b v of Some ob \<Rightarrow> [ob] | None \<Rightarrow> allobjs))"

definition cert_ops_for_clause :: "object list \<Rightarrow> fact_orga \<Rightarrow> action_clause \<Rightarrow> ast_classical_plan_action list" where
  "cert_ops_for_clause allobjs orga c =
     map (SimplePlanAction (cl_name c))
       (filter (satisfies_conds (cl_params c) (cl_cond_pre c))
         (concat (map (\<lambda>b. ptuples allobjs b (map fst (cl_params c)))
                      (pjoin orga [] (cl_pred_pre c)))))"

lemma punify_complete:
  assumes "map (subst_term \<rho>) ts = os"
    and "\<forall>x d. map_of b0 x = Some d \<longrightarrow> \<rho> x = d"
  shows "\<exists>b. punify b0 ts os = Some b
           \<and> (\<forall>x d. map_of b0 x = Some d \<longrightarrow> map_of b x = Some d)
           \<and> (\<forall>x d. map_of b x = Some d \<longrightarrow> \<rho> x = d)
           \<and> (\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b v = Some (\<rho> v))"
  using assms
proof (induction b0 ts os rule: punify.induct)
  case (1 b v ts ob os)
  from "1.prems"(1) have hv: "\<rho> v = ob" and rest: "map (subst_term \<rho>) ts = os" by simp_all
  show ?case
  proof (cases "map_of b v")
    case None
    have cons': "\<forall>x d. map_of ((v, ob) # b) x = Some d \<longrightarrow> \<rho> x = d"
      using "1.prems"(2) hv by (auto split: if_splits)
    from "1.IH"(1)[OF None rest cons'] obtain b' where
      p: "punify ((v, ob) # b) ts os = Some b'"
      and ext: "\<forall>x d. map_of ((v, ob) # b) x = Some d \<longrightarrow> map_of b' x = Some d"
      and cons: "\<forall>x d. map_of b' x = Some d \<longrightarrow> \<rho> x = d"
      and bind: "\<forall>v'. term.VAR v' \<in> set ts \<longrightarrow> map_of b' v' = Some (\<rho> v')" by blast
    have ext0: "\<forall>x d. map_of b x = Some d \<longrightarrow> map_of b' x = Some d"
    proof (intro allI impI)
      fix x d assume xd: "map_of b x = Some d"
      with None have "x \<noteq> v" by auto
      hence "map_of ((v, ob) # b) x = Some d" using xd by simp
      thus "map_of b' x = Some d" using ext by blast
    qed
    have bindv: "map_of b' v = Some (\<rho> v)"
    proof -
      have "map_of ((v, ob) # b) v = Some ob" by simp
      hence "map_of b' v = Some ob" using ext by blast
      thus ?thesis using hv by simp
    qed
    show ?thesis
    proof (intro exI[where x=b'] conjI)
      show "punify b (term.VAR v # ts) (ob # os) = Some b'" using None p by simp
      show "\<forall>x d. map_of b x = Some d \<longrightarrow> map_of b' x = Some d" using ext0 .
      show "\<forall>x d. map_of b' x = Some d \<longrightarrow> \<rho> x = d" using cons .
      show "\<forall>v'. term.VAR v' \<in> set (term.VAR v # ts) \<longrightarrow> map_of b' v' = Some (\<rho> v')"
        using bind bindv by auto
    qed
  next
    case (Some ob2)
    have "\<rho> v = ob2" using "1.prems"(2) Some by blast
    hence eq: "ob2 = ob" using hv by simp
    from "1.IH"(2)[OF Some eq rest "1.prems"(2)] obtain b' where
      p: "punify b ts os = Some b'"
      and ext: "\<forall>x d. map_of b x = Some d \<longrightarrow> map_of b' x = Some d"
      and cons: "\<forall>x d. map_of b' x = Some d \<longrightarrow> \<rho> x = d"
      and bind: "\<forall>v'. term.VAR v' \<in> set ts \<longrightarrow> map_of b' v' = Some (\<rho> v')" by blast
    have bindv: "map_of b' v = Some (\<rho> v)"
    proof -
      have "map_of b v = Some ob" using Some eq by simp
      hence "map_of b' v = Some ob" using ext by blast
      thus ?thesis using hv by simp
    qed
    show ?thesis
    proof (intro exI[where x=b'] conjI)
      show "punify b (term.VAR v # ts) (ob # os) = Some b'" using Some eq p by simp
      show "\<forall>x d. map_of b x = Some d \<longrightarrow> map_of b' x = Some d" using ext .
      show "\<forall>x d. map_of b' x = Some d \<longrightarrow> \<rho> x = d" using cons .
      show "\<forall>v'. term.VAR v' \<in> set (term.VAR v # ts) \<longrightarrow> map_of b' v' = Some (\<rho> v')"
        using bind bindv by auto
    qed
  qed
next
  case (2 b c ts ob os)
  from "2.prems"(1) have ceq: "c = ob" and rest: "map (subst_term \<rho>) ts = os" by simp_all
  from "2.IH"[OF _ rest "2.prems"(2)] ceq obtain b' where
    p: "punify b ts os = Some b'"
    and ext: "\<forall>x d. map_of b x = Some d \<longrightarrow> map_of b' x = Some d"
    and cons: "\<forall>x d. map_of b' x = Some d \<longrightarrow> \<rho> x = d"
    and bind: "\<forall>v'. term.VAR v' \<in> set ts \<longrightarrow> map_of b' v' = Some (\<rho> v')" by blast
  show ?case
  proof (intro exI[where x=b'] conjI)
    show "punify b (term.CONST c # ts) (ob # os) = Some b'" using ceq p by simp
    show "\<forall>x d. map_of b x = Some d \<longrightarrow> map_of b' x = Some d" using ext .
    show "\<forall>x d. map_of b' x = Some d \<longrightarrow> \<rho> x = d" using cons .
    show "\<forall>v'. term.VAR v' \<in> set (term.CONST c # ts) \<longrightarrow> map_of b' v' = Some (\<rho> v')"
      using bind by auto
  qed
next
  case (3 b)
  show ?case using "3.prems"(2) by auto
next
  case ("4_1" b v va)
  from "4_1.prems"(1) show ?case by simp
next
  case ("4_2" b v va)
  from "4_2.prems"(1) show ?case by simp
next
  case ("4_3" b v)
  from "4_3.prems"(1) show ?case by simp
qed

lemma pmatch_atom_complete:
  assumes "map (subst_term \<rho>) ts \<in> set (orga p)"
    and "\<forall>x d. map_of b0 x = Some d \<longrightarrow> \<rho> x = d"
  shows "\<exists>b \<in> set (pmatch_atom orga b0 (Atom (predAtm p ts))).
           (\<forall>x d. map_of b0 x = Some d \<longrightarrow> map_of b x = Some d)
           \<and> (\<forall>x d. map_of b x = Some d \<longrightarrow> \<rho> x = d)
           \<and> (\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b v = Some (\<rho> v))"
proof -
  from punify_complete[OF refl assms(2), of ts] obtain b where
    p: "punify b0 ts (map (subst_term \<rho>) ts) = Some b"
    and ext: "\<forall>x d. map_of b0 x = Some d \<longrightarrow> map_of b x = Some d"
    and cons: "\<forall>x d. map_of b x = Some d \<longrightarrow> \<rho> x = d"
    and bind: "\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b v = Some (\<rho> v)" by blast
  have "b \<in> set (pmatch_atom orga b0 (Atom (predAtm p ts)))"
    unfolding pmatch_atom_def using p assms(1) by (force simp: List.map_filter_def)
  thus ?thesis using ext cons bind by blast
qed

lemma pjoin_complete:
  assumes "\<forall>p ts. Atom (predAtm p ts) \<in> set atms \<longrightarrow> map (subst_term \<rho>) ts \<in> set (orga p)"
    and "\<forall>a \<in> set atms. is_predAtom a"
    and "\<forall>x d. map_of b0 x = Some d \<longrightarrow> \<rho> x = d"
  shows "\<exists>b \<in> set (pjoin orga b0 atms).
           (\<forall>x d. map_of b0 x = Some d \<longrightarrow> map_of b x = Some d)
           \<and> (\<forall>x d. map_of b x = Some d \<longrightarrow> \<rho> x = d)
           \<and> (\<forall>p ts. Atom (predAtm p ts) \<in> set atms
                \<longrightarrow> (\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b v = Some (\<rho> v)))"
  using assms
proof (induction atms arbitrary: b0)
  case Nil
  then show ?case by auto
next
  case (Cons a atms)
  from Cons.prems(2) have "is_predAtom a" by simp
  then obtain p ts where a: "a = Atom (predAtm p ts)"
    by (cases a rule: is_predAtom.cases) auto
  have inset: "map (subst_term \<rho>) ts \<in> set (orga p)"
    using Cons.prems(1) a by simp
  from pmatch_atom_complete[where orga=orga, OF inset Cons.prems(3)] obtain b1 where
    b1in: "b1 \<in> set (pmatch_atom orga b0 (Atom (predAtm p ts)))"
    and ext1: "\<forall>x d. map_of b0 x = Some d \<longrightarrow> map_of b1 x = Some d"
    and cons1: "\<forall>x d. map_of b1 x = Some d \<longrightarrow> \<rho> x = d"
    and bind1: "\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b1 v = Some (\<rho> v)" by blast
  have rest_facts: "\<forall>p ts. Atom (predAtm p ts) \<in> set atms \<longrightarrow> map (subst_term \<rho>) ts \<in> set (orga p)"
    using Cons.prems(1) by simp
  have rest_pred: "\<forall>a \<in> set atms. is_predAtom a" using Cons.prems(2) by simp
  from Cons.IH[OF rest_facts rest_pred cons1] obtain b where
    bin: "b \<in> set (pjoin orga b1 atms)"
    and ext': "\<forall>x d. map_of b1 x = Some d \<longrightarrow> map_of b x = Some d"
    and cons': "\<forall>x d. map_of b x = Some d \<longrightarrow> \<rho> x = d"
    and bind': "\<forall>p ts. Atom (predAtm p ts) \<in> set atms
                  \<longrightarrow> (\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b v = Some (\<rho> v))" by blast
  have binda: "\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b v = Some (\<rho> v)"
    using bind1 ext' by blast
  show ?case
  proof (intro bexI[where x=b] conjI)
    show "\<forall>x d. map_of b0 x = Some d \<longrightarrow> map_of b x = Some d" using ext1 ext' by blast
    show "\<forall>x d. map_of b x = Some d \<longrightarrow> \<rho> x = d" using cons' .
    show "\<forall>p' ts'. Atom (predAtm p' ts') \<in> set (a # atms)
            \<longrightarrow> (\<forall>v. term.VAR v \<in> set ts' \<longrightarrow> map_of b v = Some (\<rho> v))"
      using binda bind' a by auto
    show "b \<in> set (pjoin orga b0 (a # atms))"
      using bin b1in a by (auto simp: a)
  qed
qed

lemma ptuples_complete:
  assumes "\<forall>v \<in> set vars. (case map_of b v of Some ob \<Rightarrow> ob = \<rho> v | None \<Rightarrow> \<rho> v \<in> set allobjs)"
  shows "map \<rho> vars \<in> set (ptuples allobjs b vars)"
  using assms
proof (induction vars)
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  have ih: "map \<rho> vs \<in> set (ptuples allobjs b vs)" using Cons by simp
  have hd: "\<rho> v \<in> set (case map_of b v of Some ob \<Rightarrow> [ob] | None \<Rightarrow> allobjs)"
    using Cons.prems by (auto split: option.splits)
  show ?case
    using hd ih by (auto split: option.splits)
qed

context normalized_problem_rx
begin

text \<open>The applicable-ops over-approximation read off the certified reachable facts \<open>M\<close>: for every
  action clause of \<open>PX\<close> and every object-tuple over the universe whose substituted positive
  precondition atoms all lie in \<open>M\<close> and whose equality guards hold, the corresponding ground plan
  action. By \<open>px.enabled_clause_body\<close> every action enabled in a reachable state of the relaxed
  problem is enumerated here, which is what makes \<open>cert_ops'\<close> an over-approximation of the
  applicable actions.\<close>
definition cert_ops_of :: "fact list \<Rightarrow> ast_classical_plan_action list" where
  "cert_ops_of M \<equiv> concat (map
       (cert_ops_for_clause px.const_names (organize_facts (map fact_to_facty M)))
       px.a_clauses)"

text \<open>Completeness of the join: every object tuple that passes the old \<open>all_combos\<close> filter --- its
  substituted positive precondition atoms all lie in \<open>M\<close>, its guards hold, and it ranges over the
  object universe --- is still enumerated.  This is all \<open>px_applicable_super\<close> needs (the join is an
  over-approximation; the reverse inclusion is not required).\<close>
lemma cert_ops_of_complete:
  assumes "c \<in> set px.a_clauses"
    and "length args = length (cl_params c)"
    and "set args \<subseteq> set px.const_names"
    and "\<forall>a \<in> set (cl_pred_pre c).
           map_atom_fmla (ac_tsubst (cl_params c) args) a \<in> set (map fact_to_facty M)"
    and "satisfies_conds (cl_params c) (cl_cond_pre c) args"
  shows "SimplePlanAction (cl_name c) args \<in> set (cert_ops_of M)"
proof -
  define \<rho> where "\<rho> = (the \<circ> map_of (zip (map fst (cl_params c)) args))"
  have sigma: "ac_tsubst (cl_params c) args = subst_term \<rho>"
    unfolding \<rho>_def ac_tsubst_def by simp
  define orga where "orga = organize_facts (map fact_to_facty M)"
  \<comment> \<open>the clause comes from a well-formed action schema, so its parameters are distinct\<close>
  from assms(1) obtain sch where sch_mem: "sch \<in> set (actions (domain PX))"
    and c_eq: "c = as_action_clause sch"
    unfolding px.a_clauses_def by auto
  obtain nm ps pre ad dl nl where sch_eq:
    "sch = SimpleActionSchema (ActionHead nm ps) (SimpleActionBody pre (Effect ad dl nl))"
    by (metis ast_classical_action_schema_cases_unfold ast_effect.exhaust)
  have cl_params_c: "cl_params c = ps" using c_eq sch_eq by simp
  have cl_pred_c: "cl_pred_pre c = pos_lits_of pre" using c_eq sch_eq by simp
  have dist: "distinct (map fst (cl_params c))"
    using bspec[OF px.wf_D(3) sch_mem] px.wf_classical_action_schema_alt sch_eq cl_params_c by simp
  \<comment> \<open>the positive precondition atoms are predicate atoms\<close>
  have pred_pre: "\<forall>a \<in> set (cl_pred_pre c). is_predAtom a"
    using cl_pred_c unfolding pos_lits_of_def by auto
  \<comment> \<open>membership in the fact store: every substituted precondition atom lies in \<open>orga\<close>\<close>
  have facty_pred: "\<forall>g \<in> set (map fact_to_facty M). is_predAtom g"
    by (auto split: prod.splits)
  have join_facts: "\<forall>p ts. Atom (predAtm p ts) \<in> set (cl_pred_pre c)
                      \<longrightarrow> map (subst_term \<rho>) ts \<in> set (orga p)"
  proof (intro allI impI)
    fix p ts assume mem: "Atom (predAtm p ts) \<in> set (cl_pred_pre c)"
    have "map_atom_fmla (ac_tsubst (cl_params c) args) (Atom (predAtm p ts))
            \<in> set (map fact_to_facty M)"
      using assms(4) mem by blast
    hence inM: "Atom (predAtm p (map (subst_term \<rho>) ts)) \<in> set (map fact_to_facty M)"
      by (simp add: \<rho>_def)
    have "in_orga (Atom (predAtm p (map (subst_term \<rho>) ts))) orga"
      unfolding orga_def using in_orga_organize_facts[OF facty_pred] inM by blast
    thus "map (subst_term \<rho>) ts \<in> set (orga p)" by simp
  qed
  \<comment> \<open>step 1: the fact-driven join produces a binding consistent with \<open>\<rho>\<close>\<close>
  have b0cons: "\<forall>x d. map_of ([]::(variable \<times> object) list) x = Some d \<longrightarrow> \<rho> x = d" by simp
  from pjoin_complete[OF join_facts pred_pre b0cons] obtain b where
    bin: "b \<in> set (pjoin orga [] (cl_pred_pre c))"
    and bcons: "\<forall>x d. map_of b x = Some d \<longrightarrow> \<rho> x = d"
    and bbind: "\<forall>p ts. Atom (predAtm p ts) \<in> set (cl_pred_pre c)
                  \<longrightarrow> (\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b v = Some (\<rho> v))" by blast
  \<comment> \<open>\<open>\<rho>\<close> on the clause parameters reproduces \<open>args\<close>\<close>
  have rho_arg: "\<rho> (fst (ps ! i)) = args ! i" if i: "i < length ps" for i
  proof -
    have il: "i < length args" using i assms(2) cl_params_c by simp
    have psi: "ps ! i = (fst (ps ! i), snd (ps ! i))" by simp
    have "ac_tsubst (cl_params c) args (term.VAR (fst (ps ! i))) = args ! i"
      using ac_tsubst_intro[OF _ psi refl _ il] dist cl_params_c i by simp
    thus ?thesis by (simp add: \<rho>_def)
  qed
  have map_rho_args: "map \<rho> (map fst (cl_params c)) = args"
  proof (rule nth_equalityI)
    show "length (map \<rho> (map fst (cl_params c))) = length args"
      using assms(2) cl_params_c by simp
    fix i assume "i < length (map \<rho> (map fst (cl_params c)))"
    hence i: "i < length ps" using cl_params_c by simp
    have "map \<rho> (map fst (cl_params c)) ! i = \<rho> (fst (ps ! i))"
      using i cl_params_c by simp
    thus "map \<rho> (map fst (cl_params c)) ! i = args ! i" using rho_arg[OF i] by simp
  qed
  \<comment> \<open>step 2: reconstruct the argument tuple from the binding\<close>
  have ptup_cond: "\<forall>v \<in> set (map fst (cl_params c)).
        (case map_of b v of Some ob \<Rightarrow> ob = \<rho> v | None \<Rightarrow> \<rho> v \<in> set px.const_names)"
  proof
    fix v assume v: "v \<in> set (map fst (cl_params c))"
    show "case map_of b v of Some ob \<Rightarrow> ob = \<rho> v | None \<Rightarrow> \<rho> v \<in> set px.const_names"
    proof (cases "map_of b v")
      case (Some ob)
      thus ?thesis using bcons by auto
    next
      case None
      have "\<rho> v \<in> set args"
      proof -
        from v obtain i where i: "i < length ps" and vi: "map fst ps ! i = v"
          using cl_params_c by (auto simp: in_set_conv_nth)
        have "fst (ps ! i) = v" using vi i by simp
        hence "\<rho> v = args ! i" using rho_arg[OF i] by simp
        moreover have "args ! i \<in> set args"
          using i assms(2) cl_params_c by (simp add: in_set_conv_nth) blast
        ultimately show ?thesis by simp
      qed
      hence "\<rho> v \<in> set px.const_names" using assms(3) by blast
      thus ?thesis using None by simp
    qed
  qed
  have args_in_ptuples: "args \<in> set (ptuples px.const_names b (map fst (cl_params c)))"
    using ptuples_complete[OF ptup_cond] map_rho_args by simp
  \<comment> \<open>step 3: assemble the certified op for the clause, then lift to all clauses\<close>
  have args_in_concat: "args \<in> set (concat (map (\<lambda>b. ptuples px.const_names b (map fst (cl_params c)))
                                              (pjoin orga [] (cl_pred_pre c))))"
    using bin args_in_ptuples by auto
  have "SimplePlanAction (cl_name c) args \<in> set (cert_ops_for_clause px.const_names orga c)"
    unfolding cert_ops_for_clause_def
    using args_in_concat assms(5) by auto
  thus ?thesis
    unfolding cert_ops_of_def orga_def
    using assms(1) by auto
qed

text \<open>Augment the reachable facts with the add/delete atoms of the certified ops (read off \<open>P\<close>'s
  real schemas via \<open>res_inst\<close>) so that the grounder's effect-coverage obligation can hold at all.\<close>
definition extra_eff_atoms_of :: "fact list \<Rightarrow> facty list" where
  "extra_eff_atoms_of M \<equiv>
     remdups (concat (map (\<lambda>\<pi>. let eff = effect (the (res_inst \<pi>)) in adds eff @ dels eff)
                          (canon (cert_ops_of M))))"

definition cert_facts_of :: "fact list \<Rightarrow> facty list" where
  "cert_facts_of M \<equiv> remdups (map fact_to_facty M @ extra_eff_atoms_of M)"

text \<open>The decidable grounding obligations, phrased to match the \<^locale>\<open>wf_grounder\<close> goals exactly.
  The semantic supersets (\<open>all_facts\<close>/\<open>all_ops\<close>) are \<^emph>\<open>not\<close> here --- they are proven from the
  certificate, not re-checked.

  \<open>numeric_grounding_checks\<close> is the \<^emph>\<open>single\<close> obligation that the numeric-fluent-retaining grounder
  needs --- every certified op is a well-formed plan action (\<^locale>\<open>wf_grounder_num\<close>'s only decidable
  goal; the other three, \<open>wf_problem\<close>/\<open>ops_dist\<close>/\<open>all_ops\<close>, are proven from the problem and the
  certificate, not re-checked). Because it retains numerics verbatim it must \<^emph>\<open>not\<close> demand
  \<open>covered\<close>-coverage of preconditions/effects (\<open>covered\<close> rejects numeric atoms) --- that, the \<open>facts\<close>
  well-formedness, and the two numeric-freeness obligations are what the purely propositional
  \<open>grounding_checks\<close> adds for \<^locale>\<open>wf_grounder\<close>.\<close>
definition numeric_grounding_checks :: "fact list \<Rightarrow> bool" where
  "numeric_grounding_checks M \<equiv>
     (\<forall>\<pi> \<in> set (cert_ops_of M). wf_classical_plan_action \<pi>)"

definition grounding_checks :: "fact list \<Rightarrow> bool" where
  "grounding_checks M \<equiv>
     (\<forall>a \<in> set (cert_facts_of M). px.wf_fmla_atom px.objT a) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of M). wf_classical_plan_action \<pi>) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of M). let eff = effect (the (res_inst \<pi>))
        in \<forall>\<phi> \<in> set (adds eff @ dels eff). covered \<phi> (cert_facts_of M)) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of M). covered (precondition (the (res_inst \<pi>))) (cert_facts_of M)) \<and>
     covered (goal P) (cert_facts_of M) \<and>
     (\<forall>f \<in> set (init P). is_predAtom f) \<and>
     (\<forall>\<pi> \<in> set (cert_ops_of M). numeric_effects (effect (the (res_inst \<pi>))) = [])"

end

text \<open>The shared grounding-input base locale: a relaxed-problem certificate \<open>M\<close>/\<open>dc\<close> accepted by the
  generic checker, plus the (numeric-free, nonempty-universe) side conditions that make the
  \<^locale>\<open>num_free_relaxed_problem\<close> reachability bridge available at \<open>PX\<close>. This carries all the
  certificate machinery (\<open>cert_facts'\<close>/\<open>cert_ops'\<close>, the semantic supersets) that is independent of
  which grounding re-check is imposed; the two grounders extend it with their respective checks.\<close>
locale certified_reachability_base = normalized_problem_rx +
  fixes M :: "fact list" and dc :: "(predicate, object) dl_certificate"
  assumes px_numfree: "numeric_free_problem PX"
      and nonempty: "ast_classical_problem.const_names PX \<noteq> []"
      and cert: "dl_certified_model (set (dl_rules PX)) (set (ast_classical_problem.const_names PX)) M dc"
begin

text \<open>\<open>PX\<close> is numeric-free, delete-relaxed and has a nonempty object universe, so the full
  reachability bridge of \<^locale>\<open>num_free_relaxed_problem\<close> --- in particular
  \<open>certified_facts_eq_achievable\<close> --- applies to it.\<close>
lemma px_nfr: "num_free_relaxed_problem PX"
proof -
  have "pddl_datalog PX"
    unfolding pddl_datalog_def
    by (simp add: normalized_problem_def' relaxed_problem.intro relaxed_problem_axioms_def
                  relax_wf relax_normed relax_relaxes)
  thus ?thesis
    using px_numfree nonempty
    by (simp add: num_free_relaxed_problem_def num_free_relaxed_problem_axioms_def)
qed

definition cert_ops' :: "ast_classical_plan_action list" where
  "cert_ops' \<equiv> canon (cert_ops_of M)"

definition cert_facts' :: "facty list" where
  "cert_facts' \<equiv> cert_facts_of M"

end

text \<open>The numeric-fluent-retaining grounding-input locale: the shared base plus the single ops
  well-formedness re-check (\<open>numeric_grounding_checks\<close>). It grounds the un-relaxed problem \<open>P\<close>
  \<^emph>\<open>retaining\<close> its numeric preconditions/effects, so it must \<^emph>\<open>not\<close> require the coverage /
  facts-wf / numeric-freeness checks --- it interprets \<^locale>\<open>wf_grounder_num\<close>, not
  \<^locale>\<open>wf_grounder\<close>.\<close>
locale certified_reachability_num = certified_reachability_base +
  assumes grounding_cert_num: "numeric_grounding_checks M"

text \<open>The propositional grounding-input locale: the shared base plus the full \<open>grounding_checks\<close>
  (the five coverage checks \<^emph>\<open>and\<close> the two numeric-freeness checks). It interprets the full
  \<^locale>\<open>wf_grounder\<close>. Sibling of \<^locale>\<open>certified_reachability_num\<close> --- neither extends the other,
  so no locale interprets both \<^locale>\<open>wf_grounder\<close> and \<^locale>\<open>wf_grounder_num\<close> at the same
  parameters (which would deduplicate the shared \<open>grounder\<close> interpretation).\<close>
locale certified_reachability = certified_reachability_base +
  assumes grounding_cert: "grounding_checks M"

end

