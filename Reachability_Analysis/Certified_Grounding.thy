theory Certified_Grounding
  imports Certified_Grounding_Locales
begin

section \<open>Certificate-to-grounder bridge: semantic supersets over the un-relaxed problem \<open>P\<close>\<close>

context certified_reachability
begin

text \<open>The certified reachable facts are \<^emph>\<open>exactly\<close> the relaxed problem's achievable facts
  (\<open>certified_facts_eq_achievable\<close> on \<open>PX\<close>), which over-approximate the un-relaxed problem's
  achievable facts (\<open>relax_achievables\<close>).\<close>
lemma certified_eq_px_achievable: "set M = {f. px.achievable f}"
  using num_free_relaxed_problem.certified_facts_eq_achievable[OF px_nfr cert] by simp

subsection \<open>Facts superset over \<open>P\<close>\<close>

lemma all_facts_super: "fact_to_facty ` {a. achievable a} \<subseteq> set cert_facts'"
proof -
  have "fact_to_facty ` {a. achievable a} \<subseteq> fact_to_facty ` {a. px.achievable a}"
    using relax_achievables by blast
  also have "\<dots> = fact_to_facty ` set M" using certified_eq_px_achievable by simp
  also have "\<dots> \<subseteq> set cert_facts'"
    unfolding cert_facts'_def cert_facts_of_def by auto
  finally show ?thesis .
qed

subsection \<open>Ops superset over \<open>P\<close>\<close>

text \<open>Every action applicable in the un-relaxed problem is applicable in the relaxed problem
  (\<open>relax_applicables\<close>), and every relaxed-applicable action is enabled in some reachable state, so
  its positive precondition atoms are achievable --- hence in \<open>M\<close> --- and its equality guards hold.
  That is exactly the filter \<^const>\<open>cert_ops_of\<close> applies, so the action is enumerated.\<close>
text \<open>A predicate-atom fact that holds in a reachable state of the relaxed problem is achievable,
  hence (by \<open>certified_eq_px_achievable\<close>) one of the certified facts \<open>M\<close>.\<close>
lemma reachable_atom_in_M:
  assumes vp: "px.valid_classical_plan_alt px.I \<pi>s Mst"
      and mem: "Atom (predAtm p xs) \<in> fst Mst"
  shows "Atom (predAtm p xs) \<in> set (map fact_to_facty M)"
proof -
  have "Atom (uncurry predAtm (p, xs)) \<in> fst Mst" using mem by simp
  hence "px.achievable (p, xs)" unfolding px.achievable_def using vp by blast
  hence "(p, xs) \<in> set M" using certified_eq_px_achievable by simp
  thus ?thesis by force
qed

lemma px_applicable_super: "{\<pi>. px.applicable \<pi>} \<subseteq> set (cert_ops_of M)"
proof
  fix \<pi> assume "\<pi> \<in> {\<pi>. px.applicable \<pi>}"
  then obtain \<pi>s Mst where vp: "px.valid_classical_plan_alt px.I \<pi>s Mst"
    and en: "px.plan_action_enabled \<pi> Mst"
    using px.applicable_alt by blast
  obtain n args where \<pi>_eq: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  have wf: "px.wf_classical_plan_action (SimplePlanAction n args)"
    using en unfolding \<pi>_eq px.plan_action_enabled_def by (simp add: Let_def)
  obtain ac where ac_mem: "ac \<in> set (actions (domain PX))"
    and ac_name: "ac_name ac = n"
    and apm: "action_params_match (head ac) args"
    using px.wf_pa_refs_ac[OF wf] by metis
  define c where "c = as_action_clause ac"
  \<comment> \<open>shape of the schema, to read off \<open>cl_name\<close> / \<open>cl_params\<close>\<close>
  obtain nm ps pre eff where ac_eq:
    "ac = SimpleActionSchema (ActionHead nm ps) (SimpleActionBody pre eff)"
    by (cases ac rule: ast_classical_action_schema_cases_unfold)
  obtain ad dl nl where eff_eq: "eff = Effect ad dl nl" by (cases eff)
  have nm_n: "nm = n" using ac_name ac_eq by simp
  have cl_name_c: "cl_name c = n" using c_def ac_eq eff_eq nm_n by simp
  have cl_params_c: "cl_params c = ps" using c_def ac_eq eff_eq by simp
  have head_ps: "parameters (head ac) = ps" using ac_eq by simp
  \<comment> \<open>the enabled action's positive precondition atoms hold in \<open>Mst\<close>; its guards are satisfied\<close>
  have ecb: "set (map (map_atom_fmla (ac_tsubst (cl_params c) args)) (cl_pred_pre c)) \<subseteq> fst Mst"
        and guards: "satisfies_conds (cl_params c) (cl_cond_pre c) args"
    using px.enabled_clause_body[OF en[unfolded \<pi>_eq] ac_mem ac_name] c_def by auto
  \<comment> \<open>each substituted positive precondition atom is a predicate atom, hence achievable, hence in \<open>M\<close>\<close>
  have pos_in_M: "map_atom_fmla (ac_tsubst (cl_params c) args) a \<in> set (map fact_to_facty M)"
    if a: "a \<in> set (cl_pred_pre c)" for a
  proof -
    have x_mem: "map_atom_fmla (ac_tsubst (cl_params c) args) a \<in> fst Mst"
      using ecb a by auto
    have "cl_pred_pre c = pos_lits_of pre" using c_def ac_eq eff_eq by simp
    hence "is_predAtom a" using a unfolding pos_lits_of_def by auto
    then obtain p xs where "a = Atom (predAtm p xs)"
      by (cases a rule: is_predAtom.cases) auto
    hence "map_atom_fmla (ac_tsubst (cl_params c) args) a
             = Atom (predAtm p (map (ac_tsubst (cl_params c) args) xs))" by simp
    thus ?thesis using x_mem reachable_atom_in_M[OF vp] by simp
  qed
  \<comment> \<open>so \<open>args\<close> passes the \<^const>\<open>cert_ops_of\<close> filter\<close>
  have filt: "(\<forall>a \<in> set (cl_pred_pre c).
                map_atom_fmla (ac_tsubst (cl_params c) args) a \<in> set (map fact_to_facty M))
            \<and> satisfies_conds (cl_params c) (cl_cond_pre c) args"
    using pos_in_M guards by blast
  \<comment> \<open>and \<open>args\<close> is a tuple over the object universe of the right length\<close>
  have len: "length args = length (cl_params c)"
    using apm unfolding px.action_params_match_def
    by (simp add: list_all2_lengthD head_ps cl_params_c)
  have sub: "\<forall>a \<in> set args. a \<in> set px.const_names"
  proof
    fix a assume "a \<in> set args"
    then obtain i where i: "i < length args" "args ! i = a" by (auto simp: in_set_conv_nth)
    hence ioat: "px.is_obj_of_type a (map snd (parameters (head ac)) ! i)"
      using apm unfolding px.action_params_match_def by (auto simp: list_all2_conv_all_nth)
    have "px.objT a \<noteq> None"
      using ioat by (auto simp: px.is_obj_of_type_def split: option.splits)
    hence "a \<in> dom px.objT" by auto
    thus "a \<in> set px.const_names"
      unfolding px.objT_alt by (auto simp: dom_map_of_conv_image_fst)
  qed
  have chosen: "chosen_from (replicate (length (cl_params c)) px.const_names) args"
    by (rule chosen_from_replicate[OF len sub])
  have args_mem: "args \<in> set (all_combos
      (\<lambda>args. (\<forall>a \<in> set (cl_pred_pre c).
                  map_atom_fmla (ac_tsubst (cl_params c) args) a \<in> set (map fact_to_facty M))
              \<and> satisfies_conds (cl_params c) (cl_cond_pre c) args)
      (replicate (length (cl_params c)) px.const_names))"
    unfolding set_all_combos using chosen filt by simp
  have c_mem: "c \<in> set px.a_clauses"
    using ac_mem unfolding c_def px.a_clauses_def by auto
  have "\<pi> \<in> set (map (SimplePlanAction (cl_name c))
      (all_combos
        (\<lambda>args. (\<forall>a \<in> set (cl_pred_pre c).
                    map_atom_fmla (ac_tsubst (cl_params c) args) a \<in> set (map fact_to_facty M))
                \<and> satisfies_conds (cl_params c) (cl_cond_pre c) args)
        (replicate (length (cl_params c)) px.const_names)))"
    using args_mem \<pi>_eq cl_name_c by force
  thus "\<pi> \<in> set (cert_ops_of M)"
    unfolding cert_ops_of_def using c_mem by auto
qed

lemma all_ops_super: "{\<pi>. applicable \<pi>} \<subseteq> set cert_ops'"
  using relax_applicables px_applicable_super unfolding cert_ops'_def set_remdups by blast

end

end
