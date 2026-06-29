theory Goal_Normalization_Semantics
  imports Goal_Normalization
begin

section \<open>Goal Normalization Preserves Semantics\<close>

context wf_ast_classical_problem3 begin

text \<open> Proving valid_classical_plan2_right \<close>

lemma resinst_goal_ac:
  "(the o p3.res_inst) \<pi>\<^sub>g = GroundAction (goal P) goal_effect"
proof -
  have "goal_ac term_goal \<in> set (actions D3)" using degoal_dom_sel by simp
  hence "(the o p3.res_inst) \<pi>\<^sub>g = GroundAction
    (map_atom_fmla (ac_tsubst [] []) term_goal)
    (map_ast_effect (ac_tsubst [] []) goal_effect)"
    using goal_ac_def p3_wf.res_inst_cond by fastforce
  thus ?thesis using term_to_obj_fmla term_goal_def by simp
qed

lemma g_goal_sem_right:
  assumes "wf_world_model M" "valuation M \<Turnstile>\<^sub>m goal P" 
  shows
    "p3.plan_action_enabled \<pi>\<^sub>g M"
    "valuation (p3.execute_plan_action \<pi>\<^sub>g M) \<Turnstile>\<^sub>m goal P3"
proof -
  from assms show "p3.plan_action_enabled \<pi>\<^sub>g M"
    using resinst_goal_ac wf_goal_pa p3.plan_action_enabled_def
          numeric_effects_non_intrf_no_numeric_effects
          enumerate_rhs_pnes_no_numeric_effects by simp

  from assms(1) this
  have basic: "lwm_basic (fst (p3.execute_plan_action \<pi>\<^sub>g M))"
    using g_wm_wf p3_wf.wf_execute_stronger wf_goal_pa p3.wf_lwm_basic
          p3.plan_action_enabled_def
    by metis

  from resinst_goal_ac have "effect ((the o p3.res_inst) \<pi>\<^sub>g) = goal_effect"
    by simp
  hence "Atom (predAtm goal_pred []) \<in> fst (p3.execute_plan_action \<pi>\<^sub>g M)"
    using p3.execute_plan_action_def by simp
  hence "valuation (p3.execute_plan_action \<pi>\<^sub>g M) (predAtm goal_pred []) = Some True"
    using valuation_def by simp
  with basic show "valuation (p3.execute_plan_action \<pi>\<^sub>g M) \<Turnstile>\<^sub>m goal P3"
    by simp
qed


(* TODO clean up *)
lemma g_wf_pa_right:
  assumes "wf_classical_plan_action \<pi>"
  shows
    "(the o res_inst) \<pi> = (the o p3.res_inst) \<pi>" "p3.wf_classical_plan_action \<pi>"
proof -
  obtain n args where
    \<pi>[simp]:  "\<pi> = SimplePlanAction n args" by (cases \<pi>) auto


  obtain ac h b where
    res: "resolve_classical_action_schema n = Some ac"
    and ac: "ac = SimpleActionSchema h b"
    "ac \<in> set (actions D)" 
    and name: "ac_name ac = n" 
    and params: "action_params_match h args"
    apply (rule wf_pa_res_sas[OF assms])
    subgoal for ac
      apply (cases ac rule: ast_classical_action_schema_cases_unfold)
      by simp
    done

  have acD3: "ac \<in> set (actions D3)" using ac by simp
  have res3: "p3.resolve_classical_action_schema n = Some ac"
    using degoal_prob_sel degoal_dom_sel 
    using name acD3 
    using res_aux p3_wf.res_aux by simp

  have params3: "p3.action_params_match h args"
    using g_obj_of_type using params
    unfolding action_params_match_def p3.action_params_match_def by simp

  show g1: "(the o res_inst) \<pi> = (the o p3.res_inst) \<pi>"
    using res_inst_alt p3.res_inst_alt using res res3 by simp

  show wf3: "p3.wf_classical_plan_action \<pi>"
    using params3 res3 ac by simp
qed


lemma g_exec_right:
  assumes "wf_classical_plan_action \<pi>"
  shows "execute_plan_action \<pi> M = p3.execute_plan_action \<pi> M"
  using assms ast_classical_problem.execute_plan_action_def g_wf_pa_right by simp

lemma g_enab_right:
  assumes "wf_classical_plan_action \<pi>"
  shows "plan_action_enabled \<pi> M = p3.plan_action_enabled \<pi> M"
  using assms g_wf_pa_right ast_classical_problem.plan_action_enabled_def by simp

lemma g_execs_right:
  assumes "wf_world_model M" "valid_classical_plan_alt M \<pi>s M'"
  shows "p3.valid_classical_plan_alt M \<pi>s M'"
  using assms proof (induction \<pi>s arbitrary: M)
case (Cons p ps)
  have enab: "plan_action_enabled p M" 
   and path: "valid_classical_plan_alt (execute_plan_action p M) ps M'"
    using Cons by simp_all
  
  have enab3: "p3.plan_action_enabled p M"
    apply (subst g_enab_right[symmetric])
    using enab unfolding plan_action_enabled_def by auto

  from Cons enab have "wf_world_model (execute_plan_action p M)"
    using wf_execute_stronger by (simp add: plan_action_enabled_def Let_def)

  with Cons.IH this path have path2: "p3.valid_classical_plan_alt (execute_plan_action p M) ps M'" by simp
  then show ?case using enab enab3
    using g_exec_right plan_action_enabled_def by simp
qed simp

theorem valid_classical_plan2_right:
  assumes "valid_classical_plan2 \<pi>s"
  shows "p3.valid_classical_plan2 (\<pi>s @ [\<pi>\<^sub>g])"
proof -
  from assms obtain M where 1: "valid_classical_plan_alt I \<pi>s M" and 2: "valuation M \<Turnstile>\<^sub>m goal P"
    using valid_classical_plan2_alt by auto

  from 1 have wf_m: "wf_world_model M"
    using wf_I wf_valid_classical_plan_alt by blast
  from 1 have "p3.valid_classical_plan_alt p3.I \<pi>s M"
    using ast_classical_problem.I_def g_execs_right wf_I by auto
  moreover from 2 wf_m have "p3.plan_action_enabled \<pi>\<^sub>g M"
           "valuation (p3.execute_plan_action \<pi>\<^sub>g M) \<Turnstile>\<^sub>m goal P3"
    using g_goal_sem_right by simp_all
  ultimately show ?thesis
    unfolding p3.valid_classical_plan_from2_snoc p3.valid_classical_plan2_def 
    apply (intro exI)
    by blast
qed

(* ------------- left direction ------------- *)

lemma g_ac_split: "ac \<in> set (actions D3) \<longleftrightarrow> ac \<in> set (actions D) \<or> ac = goal_ac term_goal"
  using degoal_dom_sel by auto

lemma iffOrI: "\<lbrakk>\<lbrakk>A; \<not>C\<rbrakk> \<Longrightarrow> B; B \<Longrightarrow> A; C \<Longrightarrow> A\<rbrakk> \<Longrightarrow> A \<longleftrightarrow> B \<or> C"
  by blast

lemma g_wf_pa_left:
  "p3.wf_classical_plan_action \<pi> \<longleftrightarrow> wf_classical_plan_action \<pi> \<or> \<pi> = \<pi>\<^sub>g"
proof (cases \<pi>)
  case [simp]: (SimplePlanAction n args)
  show ?thesis proof (rule iffOrI)
    assume 1: "p3.wf_classical_plan_action \<pi>" and 2: "\<not>\<pi> = \<pi>\<^sub>g"
    from 1 obtain ac where 3:
      "p3.resolve_classical_action_schema n = Some ac" "ac \<in> set (actions D3)"
      "ac_name ac = n" "p3.action_params_match (head ac) args"
      using p3.wf_pa_refs_ac by auto

    have "ac \<noteq> goal_ac term_goal"
    proof (rule eq_contr)
      assume g: "ac = goal_ac term_goal"
      hence "ac_name ac = goal_ac_name" unfolding goal_ac_def by simp
      moreover have "args = []" using 3 goal_ac_def p3.action_params_match_def using g by simp
      ultimately have "\<pi> = \<pi>\<^sub>g" using 3 by simp
      with 2 show False by simp
    qed

    hence "ac \<in> set (actions D)" using 3 g_ac_split by simp
    moreover have "action_params_match (head ac) args"
      using action_params_match_def p3.action_params_match_def 
      using g_obj_of_type 3 by simp
    ultimately show "wf_classical_plan_action \<pi>"
      using 3 res_aux wf_classical_plan_action_cond
      by (metis SimplePlanAction ast_classical_action_schema.exhaust ast_classical_action_schema.sel(1))
  next
    assume "wf_classical_plan_action \<pi>" thus "p3.wf_classical_plan_action \<pi>"
      using g_wf_pa_right by blast
  next
    assume "\<pi> = \<pi>\<^sub>g" thus "p3.wf_classical_plan_action \<pi>"
      using wf_goal_pa by blast
  qed
qed

thm entail_adds_irrelevant
thm wf_ast_classical_problem.wf_resolve_instantiate
thm wf_pa_refs_ac
thm g_wf_pa_right
thm degoal_prob_sel

(* TODO move a lof of goal_pred exclusion logic outside *)
(* you could use wm_basic in the condition, but then you'd need a version of
  wf_execute that only cares about preserving wm_basic. *)
lemma goal_atm_not_wf: "\<not>wf_fmla_atom tyt (Atom (predAtm goal_pred []))"
proof -
  have "safe_prefix pred_names + STR ''Goal'' \<notin> set pred_names"
    using safe_prefix_correct by blast
  hence "safe_prefix pred_names + STR ''Goal'' \<notin> predicate.name ` (pred ` set (predicates D))"
    by auto
  hence "goal_pred \<notin> pred ` set (predicates D)"
    unfolding goal_pred_def by (metis image_iff predicate.sel)
  hence "\<not>wf_pred_atom tyt (goal_pred, [])"
    using sig_None wf_pred_atom.simps by (metis option.simps(4))
  thus ?thesis by simp
qed

lemma g_goal_unaffected:
  assumes "\<not>valuation M \<Turnstile>\<^sub>m goal P3" "wf_classical_plan_action \<pi>" "p3.wf_world_model M"
  shows "\<not>valuation (p3.execute_plan_action \<pi> M) \<Turnstile>\<^sub>m goal P3"
proof -
  let ?goal_atm = "Atom (predAtm goal_pred [])"

  let ?ga = "(the o p3.res_inst) \<pi>"

  from assms(2) have "wf_ground_action ?ga"
    using g_wf_pa_right wf_resolve_instantiate by simp
  hence "wf_effect objT (effect ?ga)"
    by (simp add: wf_ground_action_alt)
  hence "\<forall>ae \<in> set (adds (effect ?ga)). wf_fmla_atom objT ae"
    using wf_effect_alt unfolding list_all_iff by blast
  hence notin: "?goal_atm \<notin> set (adds (effect ?ga))"
    using goal_atm_not_wf by blast

  have end_basic: "lwm_basic (fst (p3.execute_plan_action \<pi> M))"
    using assms g_wf_pa_right p3_wf.wf_execute_stronger p3.wf_lwm_basic by blast

  (* Todo simplify / export *)
  from assms have "\<not> valuation M \<Turnstile>\<^sub>m goal P3"
    using p3.wf_lwm_basic by blast
  hence "valuation M (predAtm goal_pred []) \<noteq> Some True"
    by simp
  hence "?goal_atm \<notin> fst M" using valuation_def by simp
  with notin have "?goal_atm \<notin> fst (p3.execute_plan_action \<pi> M)"
    using p3.execute_plan_action_def apply_ground_action_alt by simp
  hence "valuation (p3.execute_plan_action \<pi> M) (predAtm goal_pred []) \<noteq> Some True"
    using valuation_def by simp
  hence "\<not> valuation (p3.execute_plan_action \<pi> M) \<Turnstile>\<^sub>m goal P3"
    by simp
  thus ?thesis using assms end_basic by blast
qed

lemma g_init_not_sat: "\<not> valuation p3.I \<Turnstile>\<^sub>m goal P3"
proof -
  have "(Atom (predAtm goal_pred [])) \<notin> fst I"
    using wf_I goal_atm_not_wf wf_lwm_basic lwm_basic_def by fastforce
  hence "valuation p3.I (predAtm goal_pred []) \<noteq> Some True"
    using valuation_def by simp
  thus ?thesis using p3_wf.i_basic by simp
qed

lemma no_goal_pa_no_sat:
  assumes "p3.wf_world_model M" "\<not>valuation M \<Turnstile>\<^sub>m goal P3" "\<pi>\<^sub>g \<notin> set \<pi>s" "p3.valid_classical_plan_alt M \<pi>s M'"
  shows "\<not>valuation M' \<Turnstile>\<^sub>m goal P3"
using assms proof (induction \<pi>s arbitrary: M)
  case Nil then show ?case
    using p3.valid_classical_plan2_def p3.valid_classical_plan_from2_def by auto
next
  case (Cons \<pi> \<pi>s)
  hence "p3.wf_classical_plan_action \<pi>"
    using p3.valid_classical_plan_alt.simps(2) p3.plan_action_enabled_def by blast
  hence "wf_classical_plan_action \<pi>" using g_wf_pa_left \<open>\<pi>\<^sub>g \<notin> set (\<pi> # \<pi>s)\<close> by auto

  from Cons have 1: "p3.wf_world_model (p3.execute_plan_action \<pi> M)"
    using p3_wf.wf_execute_stronger \<open>p3.wf_classical_plan_action \<pi>\<close> by simp
  from Cons have 2: "\<not>valuation (p3.execute_plan_action \<pi> M) \<Turnstile>\<^sub>m goal P3"
    using g_goal_unaffected \<open>wf_classical_plan_action \<pi>\<close> by blast
  from Cons have 3: "\<pi>\<^sub>g \<notin> set \<pi>s" by simp
  from Cons have 4: "p3.valid_classical_plan_alt (p3.execute_plan_action \<pi> M) \<pi>s M'"
    using p3.valid_classical_plan_alt.simps(2) by simp

  from Cons.IH[OF 1 2 3 4] show ?case .
qed

lemma no_goal_pa_not_valid:
  assumes "\<pi>\<^sub>g \<notin> set \<pi>s"
  shows "\<not>p3.valid_classical_plan2 \<pi>s"
proof -
  have "p3.valid_classical_plan2 \<pi>s \<longleftrightarrow> (\<exists>M. p3.valid_classical_plan_alt p3.I \<pi>s M \<and> valuation M \<Turnstile>\<^sub>m goal P3)"
    unfolding p3.valid_classical_plan2_def p3.valid_classical_plan_from2_alt by simp
  (* with no_goal_pa_no_sat we get
    p3.valid_classical_plan_alt p3.I \<pi>s M \<Longrightarrow> \<not>valuation M \<Turnstile>\<^sub>m goal P3 *)
  with assms show ?thesis using g_init_not_sat no_goal_pa_no_sat p3_wf.wf_I by blast
qed

lemma g_valid_classical_plan2_has_ga:
  "p3.valid_classical_plan2 \<pi>s \<Longrightarrow> \<pi>\<^sub>g \<in> set \<pi>s"
  using no_goal_pa_not_valid by auto

lemma g_goal_sem_left:
  assumes "p3.plan_action_enabled \<pi>\<^sub>g M"
  shows "valuation M \<Turnstile>\<^sub>m goal P"
using assms p3.plan_action_enabled_def wf_goal_pa
    resinst_goal_ac by auto

lemma g_exec_left:
  assumes "p3.wf_classical_plan_action \<pi>" "\<pi> \<noteq> \<pi>\<^sub>g"
  shows "p3.execute_plan_action \<pi> M = execute_plan_action \<pi> M"
  using assms g_wf_pa_left g_exec_right by simp

lemma g_enab_left:
  assumes "p3.wf_classical_plan_action \<pi>" "\<pi> \<noteq> \<pi>\<^sub>g"
  shows "p3.plan_action_enabled \<pi> M = plan_action_enabled \<pi> M"
  using assms g_wf_pa_left g_enab_right by simp

lemma g_execs_left:
  assumes "wf_world_model M" "\<pi>\<^sub>g \<notin> set \<pi>s" "p3.valid_classical_plan_alt M \<pi>s M'"
  shows "valid_classical_plan_alt M \<pi>s M'"
using assms proof (induction \<pi>s arbitrary: M)
  case (Cons \<pi> \<pi>s)
  hence neq: "\<pi> \<noteq> \<pi>\<^sub>g" and notin: "\<pi>\<^sub>g \<notin> set \<pi>s" by auto
  from Cons have enab3: "p3.plan_action_enabled \<pi> M" and path3: "p3.valid_classical_plan_alt (p3.execute_plan_action \<pi> M) \<pi>s M'"
    by simp_all

  from enab3 have wf3: "p3.wf_classical_plan_action \<pi>" using p3.plan_action_enabled_def by simp
  with enab3 have enab: "plan_action_enabled \<pi> M" using neq g_enab_left by simp
  from path3 wf3 have path2: "p3.valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'" 
    using neq g_exec_left by simp

  from Cons enab have wf_m: "wf_world_model (execute_plan_action \<pi> M)" 
    using wf_execute_stronger plan_action_enabled_def by blast

  have path: "valid_classical_plan_alt (execute_plan_action \<pi> M) \<pi>s M'" 
    using Cons.IH[OF wf_m notin path2] .

  from enab path show ?case using valid_classical_plan_alt.simps(2) by simp
qed simp

theorem valid_classical_plan2_left:
  assumes "p3.valid_classical_plan2 \<pi>s"
  shows "valid_classical_plan2 (restore_plan_degoal \<pi>s)"
proof -
  let ?ogs = "restore_plan_degoal \<pi>s"
  from assms obtain ys where
    restore: "(?ogs @ [\<pi>\<^sub>g]) @ ys = \<pi>s" (* parantheses important for unification with valid_classical_plan_alt_append_elim *)
    using g_valid_classical_plan2_has_ga sublist_just_until by fastforce
  from assms obtain M3 where
    fullpath: "p3.valid_classical_plan_alt p3.I \<pi>s M3"
    using p3.valid_classical_plan2_alt by blast
  then obtain M2 where
    path: "p3.valid_classical_plan_alt p3.I (?ogs @ [\<pi>\<^sub>g]) M2"
    using p3.valid_classical_plan_alt_append_elim restore by metis
  then obtain M1 where
    sol: "p3.valid_classical_plan_alt p3.I ?ogs M1" and
    skip: "p3.valid_classical_plan_alt M1 [\<pi>\<^sub>g] M2"
    using p3.valid_classical_plan_alt_append_elim by blast

  from skip have "p3.plan_action_enabled \<pi>\<^sub>g M1"
    using valid_classical_plan_alt.simps(2) by simp
  hence sat: "valuation M1 \<Turnstile>\<^sub>m goal P"
    using g_goal_sem_left by simp
  moreover have "valid_classical_plan_alt p3.I ?ogs M1"
    apply (rule g_execs_left)
    using notin_sublist_until sol wf_I by fastforce+
  ultimately show ?thesis unfolding valid_classical_plan2_alt 
    by (intro exI, simp) 
qed

theorem degoaled_valid_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s. p3.valid_classical_plan2 \<pi>s)"
  using valid_classical_plan2_left valid_classical_plan2_right by auto

end

subsection \<open> Code Setup \<close>

lemmas goal_norm_code =
  domain_signature.goal_pred_def
  domain_signature.goal_pred_decl_def
  ast_classical_domain.goal_ac_def
  ast_classical_problem.term_goal_def
  ast_classical_problem.degoal_dom_def
  ast_classical_problem.degoal_prob_def
declare goal_norm_code[code]

end

