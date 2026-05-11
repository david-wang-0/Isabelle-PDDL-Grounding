theory Goal_Normalization
imports "Classical_Planning.Classical_Abstract_Syntax"
    PDDL_Sema_Supplement String_Utils Grounding_Utils DNF
begin

context ast_domain begin

  definition "goal_pred \<equiv> Pred (make_unique pred_names ''Goal'')"
  definition "goal_pred_decl \<equiv> PredDecl goal_pred []"
  
  abbreviation "ac_names \<equiv> map ac_name (actions D)"
  
  abbreviation "goal_ac_name \<equiv> make_unique ac_names ''Goal''"
  
  abbreviation "goal_effect \<equiv> Effect [Atom (predAtm goal_pred [])] []"
  
  definition goal_ac where "goal_ac g =
    Action_Schema goal_ac_name [] g goal_effect"
end

context ast_problem begin

  definition "term_goal \<equiv> map_atom_fmla term.CONST (goal P)"
  
  definition "degoal_dom \<equiv>
    Domain
      (types D)
      (goal_pred_decl # predicates D)
      (objects P @ consts D)
      (goal_ac term_goal # actions D)"
  
  definition "degoal_prob \<equiv>
    Problem
      degoal_dom
      []
      (init P)
      (Atom (predAtm goal_pred []))"
end

context ast_domain begin

abbreviation "\<pi>\<^sub>g \<equiv> PAction goal_ac_name []"
abbreviation "restore_plan_degoal \<pi>s \<equiv> sublist_until \<pi>s \<pi>\<^sub>g"

end

text \<open> locale setup for simplified syntax \<close>

(* no ast_domain3 etc, because the degoaled domain requires the whole
  problem as input, anyway. As such, D3 isn't defined in ast_domain. *)

abbreviation (in ast_problem) (input) "D3 \<equiv> degoal_dom"
abbreviation (in ast_problem) (input) "P3 \<equiv> degoal_prob"

locale ast_problem3 = ast_problem
sublocale ast_problem3 \<subseteq> d3: ast_domain D3 .
sublocale ast_problem3 \<subseteq> p3: ast_problem P3 .

locale wf_ast_problem3 = wf_ast_problem
sublocale wf_ast_problem3 \<subseteq> d3: ast_domain D3 .
sublocale wf_ast_problem3 \<subseteq> p3: ast_problem P3 .

subsection \<open> Alternate/simplified definitions\<close>
context ast_problem begin

lemma degoal_dom_sel[simp]:
  "types D3 = types D"
  "predicates D3 = goal_pred_decl # predicates D"
  "consts D3 = objects P @ consts D"
  "actions D3 = goal_ac term_goal # actions D"
  using degoal_dom_def by simp_all

lemma degoal_prob_sel[simp]:
  "domain P3 = D3"
  "objects P3 = []"
  "init P3 = init P"
  "goal P3 = Atom (predAtm goal_pred [])"
  using degoal_prob_def by simp_all
end

text \<open> There aren't really any better lemmas to describe that the output has the required format
  than degoal_dom_sel and degoal_prob_sel \<close>

subsection \<open>Well-Formedness\<close>

context wf_ast_problem3 begin

lemma pred_stack: "Pred ` predicate.name ` ps = ps" by force

lemma g_preds_dist: "distinct (map pred (predicates D3))"
proof -
  have "make_unique pred_names ''Goal'' \<notin> set pred_names"
    using made_unique by blast
  hence "make_unique pred_names ''Goal'' \<notin> predicate.name ` (pred ` set (predicates D))"
    by auto
  hence "goal_pred \<notin> pred ` set (predicates D)"
    unfolding goal_pred_def using pred_stack by blast
  hence "pred goal_pred_decl \<notin> pred ` set (predicates D)"
    using goal_pred_decl_def by force
  thus ?thesis
    using wf_D(2) degoal_dom_sel(2) by auto
qed

lemma g_type_wf: "wf_type T \<Longrightarrow> d3.wf_type T"
  using degoal_dom_sel(1) by (cases T) simp

lemma g_preds_wf: "list_all1 d3.wf_predicate_decl (predicates D3)"
proof -
  have "wf_predicate_decl pd \<Longrightarrow> d3.wf_predicate_decl pd" for pd
    using g_type_wf by (cases pd) simp

  hence "list_all1 d3.wf_predicate_decl (predicates D)"
    using wf_D(3) degoal_dom_sel(2) by simp
  moreover have "d3.wf_predicate_decl goal_pred_decl"
    unfolding goal_pred_decl_def by simp

  ultimately show ?thesis using degoal_dom_sel(2) by simp
qed

lemma g_acs_dist: "distinct (map ac_name (actions D3))"
proof -
  have "goal_ac_name \<notin> set ac_names"
    using made_unique by blast
  hence "ac_name (goal_ac term_goal) \<notin> ac_name ` set (actions D)"
    using ast_domain.goal_ac_def by fastforce
  thus ?thesis using degoal_dom_sel wf_D(6) by auto
qed

lemma g_sig:
  assumes "sig p = Some xs" shows "d3.sig p = Some xs"
proof -
  from assms have "PredDecl p xs \<in> set (predicates D3)"
    using sig_Some degoal_dom_sel by simp
  thus ?thesis using g_preds_dist degoal_dom_sel d3.sig_def
    using ast_domain.pred_resolve by blast
qed

lemma g_is_of_type: "is_of_type = d3.is_of_type"
  apply (rule ext)
  unfolding ast_domain.is_of_type_def ast_domain.of_type_def ast_domain.subtype_rel_def degoal_dom_sel(1)
  by simp

lemma g_atom_wf:
  assumes "wf_atom tyt a" shows "d3.wf_atom tyt a"
using assms proof (cases a)
  case [simp]: (predAtm p xs)
  hence a: "wf_pred_atom tyt (p, xs)" using assms by simp
  then obtain Ts where sig: "sig p = Some Ts" by fastforce
  with a have "list_all2 (is_of_type tyt) xs Ts" by simp
  hence "list_all2 (d3.is_of_type tyt) xs Ts" using g_is_of_type by metis
  moreover have "d3.sig p = Some Ts" using g_sig sig by simp
  ultimately have "d3.wf_pred_atom tyt (p, xs)" by simp
  then show ?thesis using predAtm by simp
qed simp

lemma g_fmla_wf: "wf_fmla tyt \<phi> \<Longrightarrow> d3.wf_fmla tyt \<phi>"
  using g_atom_wf co_fmla_wf by blast

lemma g_eff_wf: "wf_effect tyt \<epsilon> \<Longrightarrow> d3.wf_effect tyt \<epsilon>"
  using g_atom_wf co_effect_wf by blast

lemma g_constT:
  "objT = d3.constT"
  using objT_def degoal_dom_sel d3.constT_def
  using constT_def map_le_iff_map_add_commute objm_le_objT by auto

lemma g_objT:
  "objT = p3.objT"
  using g_constT d3.constT_def p3.objT_def degoal_prob_sel by simp

lemma g_wm_wf: "wf_world_model wm \<Longrightarrow> p3.wf_world_model wm"
  using degoal_prob_sel(1) g_objT g_atom_wf co_wm_wf by metis

lemma g_obj_of_type: "is_obj_of_type = p3.is_obj_of_type"
  unfolding ast_problem.is_obj_of_type_alt ast_domain.is_of_type_def ast_domain.of_type_def
    ast_domain.subtype_rel_def
  using g_objT degoal_dom_sel(1) degoal_prob_sel(1) by metis

lemma is_of_type_term: "is_of_type tyt x t \<longleftrightarrow> is_of_type (ty_term xd tyt) (term.CONST x) t"
  unfolding is_of_type_def by simp

lemma wf_atom_to_term:
  assumes "wf_atom tyt a"
  shows "wf_atom (ty_term vart tyt) (map_atom term.CONST a)"
proof (cases a)
  case [simp]: (predAtm p xs)
  with assms obtain Ts where [simp]: "sig p = Some Ts" by fastforce
  hence match: "list_all2 (is_of_type tyt) xs Ts" using assms by simp
  hence "list_all2 (is_of_type (ty_term vart tyt)) (map term.CONST xs) Ts"
  using match proof (induction xs Ts) (* rule: list_all2_induct *)
    case Cons thus ?case using is_of_type_term list_all2_Cons by simp
  qed simp

  thus ?thesis by simp
next
  case Eq thus ?thesis using assms by auto
qed

lemma wf_fmla_to_term:
  assumes "wf_fmla tyt F"
  shows "wf_fmla (ty_term vart tyt) (map_atom_fmla term.CONST F)"
  using assms by (induction F) (simp_all add: wf_atom_to_term)

lemma g_acs_wf: "(\<forall>a\<in>set (actions D3). d3.wf_action_schema a)"
proof -
  (* carrying over original actinos *)
  have 1: "d3.wf_action_schema ac" if "wf_action_schema ac" for ac
  proof (cases ac)
    case (Action_Schema n params pre eff)

    let ?tyt = "ty_term (map_of params) constT"
    let ?tyt3 = "ty_term (map_of params) d3.constT"
    have tyts: "?tyt \<subseteq>\<^sub>m ?tyt3"
      using ast_domain.constT_def g_constT constT_ss_objT
      by (simp add: ty_term_mono)

    from that have "wf_fmla ?tyt pre \<and> wf_effect ?tyt eff"
      by (metis Action_Schema ast_domain.wf_action_schema.simps)
    hence "d3.wf_fmla ?tyt3 pre \<and> d3.wf_effect ?tyt3 eff" using tyts wf_fmla_mono wf_eff_mono
      using g_eff_wf g_fmla_wf by blast
    moreover have "distinct (map fst params)" using Action_Schema that by (meson wf_action_schema.simps)    
    ultimately show ?thesis using Action_Schema ast_domain.wf_action_schema.simps by simp
  qed

  (* goal action well-formed *)
  let ?gac = "goal_ac term_goal"
  have "d3.wf_action_schema ?gac"
  proof -
    have 1: "distinct (map fst (ac_params ?gac))"
      unfolding goal_ac_def by (cases ?gac) simp
    let ?tyt = "ty_term Map.empty d3.constT"
    have 2: "d3.wf_fmla ?tyt term_goal"
      unfolding term_goal_def
      using wf_P g_constT wf_fmla_to_term g_fmla_wf by metis
    have 3: "d3.wf_effect ?tyt goal_effect"
      (* g_preds_dist not needed, since goal_pred is the first in the list *)
      using d3.sig_def goal_pred_decl_def by force
    from 1 2 3 show ?thesis
      by (simp add: goal_ac_def)

  qed
  with 1 show ?thesis using wf_D(7) by simp
qed

lemma degoal_dom_wf: "d3.wf_domain"
proof -
  have c1: "d3.wf_types" using ast_domain.wf_types_def wf_D by simp
  note c2 = g_preds_dist
  note c3 = g_preds_wf
  have c4: "distinct (map fst (consts D3))" using wf_D wf_P by simp
  have c5: "\<forall>(n, T) \<in> set (consts D3). d3.wf_type T" using wf_D wf_P g_type_wf by auto
  note c6 = g_acs_dist
  note c7 = g_acs_wf
  from c1 c2 c3 c4 c5 c6 c7 show ?thesis using d3.wf_domain_def by simp
qed

lemma degoal_prob_wf: "p3.wf_problem"
proof -
  note c1 = degoal_dom_wf
  have c2: "distinct (map fst (objects degoal_prob) @ map fst (consts p3.D))"
    using wf_D wf_P by simp
  have c3: "\<forall>(n, y) \<in> set (objects degoal_prob). p3.wf_type y" by simp (* empty list *)
  note c4 = wf_P(3)
  have c5: "p3.wf_world_model (set (init P))" using g_wm_wf wf_P(4) by simp
  have c6: "p3.wf_fmla p3.objT (goal degoal_prob)"
    (* g_preds_dist not needed, since goal_pred is the first in the list *)
    using d3.sig_def goal_pred_decl_def by auto
  from c1 c2 c3 c4 c5 c6 show ?thesis using p3.wf_problem_def by simp
qed

end

sublocale wf_ast_problem3 \<subseteq> d3: wf_ast_domain D3
  using degoal_dom_wf wf_ast_domain.intro by simp

sublocale wf_ast_problem3 \<subseteq> p3: wf_ast_problem P3
  using degoal_prob_wf wf_ast_problem.intro by simp

context wf_ast_problem3 begin

lemma resolve_goal_ac:
  "p3.resolve_action_schema goal_ac_name = Some (goal_ac term_goal)"
  using goal_ac_def p3.res_aux degoal_prob_sel degoal_dom_sel by simp

lemma wf_goal_pa:
  "p3.wf_plan_action \<pi>\<^sub>g"
proof -
  have "p3.action_params_match (goal_ac term_goal) []"
    unfolding goal_ac_def p3.action_params_match_def by simp
  with resolve_goal_ac show ?thesis using p3.wf_plan_action_simple by fastforce
qed

lemma term_to_obj: "ac_tsubst [] [] (term.CONST x) = x"
  unfolding ac_tsubst_def by simp

lemma term_to_obj_atom:
  shows "map_atom (ac_tsubst [] []) (map_atom term.CONST x) = x"
proof (cases x)
  case [simp]: (predAtm p xs)
  hence "map_atom (ac_tsubst [] []) (map_atom term.CONST x)
    = predAtm p (map (ac_tsubst [] [] \<circ> term.CONST) xs)"
    by simp
  also have "... = predAtm p xs" using term_to_obj
    by (simp add: map_idI)
  finally show ?thesis by simp
qed (simp add: term_to_obj)

lemma term_to_obj_fmla:
  shows "map_atom_fmla (ac_tsubst [] []) (map_atom_fmla term.CONST F) = F"
  using term_to_obj_atom by (induction F; simp)

text \<open> Proving valid_plan_right \<close>

lemma resinst_goal_ac:
  "p3.resolve_instantiate \<pi>\<^sub>g = Ground_Action (goal P) goal_effect"
proof -
  have "goal_ac term_goal \<in> set (actions D3)" using degoal_dom_sel by simp
  hence "p3.resolve_instantiate \<pi>\<^sub>g = Ground_Action
    (map_atom_fmla (ac_tsubst [] []) term_goal)
    (map_ast_effect (ac_tsubst [] []) goal_effect)"
    using goal_ac_def p3.resolve_instantiate_cond by fastforce
  thus ?thesis using term_to_obj_fmla term_goal_def by simp
qed

lemma g_goal_sem_right:
  assumes "wf_world_model M" "M \<^sup>c\<TTurnstile>\<^sub>= goal P"
  shows
    "p3.plan_action_enabled \<pi>\<^sub>g M"
    "p3.execute_plan_action \<pi>\<^sub>g M \<^sup>c\<TTurnstile>\<^sub>= goal P3"
proof -
  from assms show "p3.plan_action_enabled \<pi>\<^sub>g M"
    using resinst_goal_ac wf_goal_pa p3.plan_action_enabled_def by simp

  from assms(1) this
  have basic: "wm_basic (p3.execute_plan_action \<pi>\<^sub>g M)"
    using g_wm_wf p3.wf_execute p3.wf_fmla_atom_alt p3.wf_world_model_def wm_basic_def
    by metis

  from resinst_goal_ac have "effect (p3.resolve_instantiate \<pi>\<^sub>g) = goal_effect"
    by simp
  hence "Atom (predAtm goal_pred []) \<in> p3.execute_plan_action \<pi>\<^sub>g M"
    using p3.execute_plan_action_def by simp
  hence "valuation (p3.execute_plan_action \<pi>\<^sub>g M) \<Turnstile> goal P3"
    using valuation_def by simp
  with basic show "p3.execute_plan_action \<pi>\<^sub>g M \<^sup>c\<TTurnstile>\<^sub>= goal P3"
    using valuation_iff_close_world by blast
qed

(* TODO clean up *)
lemma g_wf_pa_right:
  assumes "wf_plan_action \<pi>"
  shows 
    "resolve_instantiate \<pi> = p3.resolve_instantiate \<pi> \<and> p3.wf_plan_action \<pi>"
using assms proof (cases \<pi>)
  case [simp]: (PAction n args)
  with assms obtain ac where 1:
    "resolve_action_schema n = Some ac" "ac \<in> set (actions D)" "ac_name ac = n"
    by (meson wf_pa_refs_ac)
  hence "ac \<in> set (actions D3)" by simp
  with 1 have r: "d3.resolve_action_schema n = Some ac"
    using degoal_prob_sel by (metis p3.res_aux)
  hence g1: "resolve_instantiate \<pi> = p3.resolve_instantiate \<pi>"
    using 1 by simp

  from 1 assms have "action_params_match ac args" by simp
  hence "p3.action_params_match ac args"
    unfolding ast_problem.action_params_match_def
    using g_obj_of_type by simp
  with r have g2: "p3.wf_plan_action \<pi>"
    using p3.wf_plan_action_simple PAction by fastforce

  from g1 g2 show ?thesis by simp
qed


lemma g_exec_right:
  assumes "wf_plan_action \<pi>"
  shows "execute_plan_action \<pi> M = p3.execute_plan_action \<pi> M"
  using assms ast_problem.execute_plan_action_def g_wf_pa_right by simp

lemma g_enab_right:
  assumes "wf_plan_action \<pi>"
  shows "plan_action_enabled \<pi> M = p3.plan_action_enabled \<pi> M"
  using assms g_wf_pa_right ast_problem.plan_action_enabled_def by simp

lemma g_execs_right:
  assumes "wf_world_model M" "plan_action_path M \<pi>s M'"
  shows "p3.plan_action_path M \<pi>s M'"
  using assms proof (induction \<pi>s arbitrary: M)
case (Cons p ps)
  hence enab: "plan_action_enabled p M" and path: "plan_action_path (execute_plan_action p M) ps M'"
    using plan_action_path_Cons by simp_all
  with Cons have enab3: "p3.plan_action_enabled p M" using g_enab_right
    by (simp add: plan_action_path_def)
  from Cons enab have "wf_world_model (execute_plan_action p M)"
    by (simp add: wf_execute)
  with Cons.IH this path have path2: "p3.plan_action_path (execute_plan_action p M) ps M'" by simp
  then show ?case using enab enab3 p3.plan_action_path_Cons
    using g_exec_right plan_action_enabled_def by force
qed simp

theorem valid_plan_right:
  assumes "valid_plan \<pi>s"
  shows "p3.valid_plan (\<pi>s @ [\<pi>\<^sub>g])"
proof -
  from assms obtain M where 1: "plan_action_path I \<pi>s M" and 2: "M \<^sup>c\<TTurnstile>\<^sub>= goal P"
    using valid_plan_def valid_plan_from_def by auto
  
  from 1 have wf_m: "wf_world_model M"
    using wf_I wf_plan_action_path by blast
  from 1 have "p3.plan_action_path p3.I \<pi>s M"
    using ast_problem.I_def g_execs_right wf_I by auto
  moreover from 2 wf_m have "p3.plan_action_enabled \<pi>\<^sub>g M"
           "p3.execute_plan_action \<pi>\<^sub>g M \<^sup>c\<TTurnstile>\<^sub>= goal P3"
    using g_goal_sem_right by simp_all
  ultimately show ?thesis
    using p3.valid_plan_from_snoc p3.valid_plan_def by auto
qed

(* ------------- left direction ------------- *)

lemma g_ac_split: "ac \<in> set (actions D3) \<longleftrightarrow> ac \<in> set (actions D) \<or> ac = goal_ac term_goal"
  using degoal_dom_sel by auto

lemma iffOrI: "\<lbrakk>\<lbrakk>A; \<not>C\<rbrakk> \<Longrightarrow> B; B \<Longrightarrow> A; C \<Longrightarrow> A\<rbrakk> \<Longrightarrow> A \<longleftrightarrow> B \<or> C"
  by blast

lemma g_wf_pa_left:
  "p3.wf_plan_action \<pi> \<longleftrightarrow> wf_plan_action \<pi> \<or> \<pi> = \<pi>\<^sub>g"
proof (cases \<pi>)
  case [simp]: (PAction n args)
  show ?thesis proof (rule iffOrI)
    assume 1: "p3.wf_plan_action \<pi>" and 2: "\<not>\<pi> = \<pi>\<^sub>g"
    from 1 obtain ac where 3:
      "d3.resolve_action_schema n = Some ac" "ac \<in> set (actions D3)"
      "ac_name ac = n" "p3.action_params_match ac args"
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
    moreover have "action_params_match ac args"
      using ast_problem.action_params_match_def g_obj_of_type 3 by simp
    ultimately show "wf_plan_action \<pi>"
      using 3 res_aux wf_plan_action_cond
      by (metis PAction ast_action_schema.exhaust ast_action_schema.sel(1))
  next
    assume "wf_plan_action \<pi>" thus "p3.wf_plan_action \<pi>"
      using g_wf_pa_right by blast
  next
    assume "\<pi> = \<pi>\<^sub>g" thus "p3.wf_plan_action \<pi>"
      using wf_goal_pa by blast
  qed
qed

thm entail_adds_irrelevant
thm wf_ast_problem.wf_resolve_instantiate
thm wf_pa_refs_ac
thm g_wf_pa_right
thm degoal_prob_sel

(* TODO move a lof of goal_pred exclusion logic outside *)
(* you could use wm_basic in the condition, but then you'd need a version of
  wf_execute that only cares about preserving wm_basic. *)
lemma goal_atm_not_wf: "\<not>wf_fmla_atom tyt (Atom (predAtm goal_pred []))"
proof -
  have "make_unique pred_names ''Goal'' \<notin> set pred_names"
    using made_unique by blast
  hence "make_unique pred_names ''Goal'' \<notin> predicate.name ` (pred ` set (predicates D))"
    by auto
  hence "goal_pred \<notin> pred ` set (predicates D)"
    unfolding goal_pred_def using pred_stack by blast
  hence "\<not>wf_pred_atom tyt (goal_pred, [])"
    using sig_None wf_pred_atom.simps by (metis option.simps(4))
  thus ?thesis by simp
qed

lemma g_goal_unaffected:
  assumes "\<not>M \<^sup>c\<TTurnstile>\<^sub>= goal P3" "wf_plan_action \<pi>" "p3.wf_world_model M"
  shows "\<not>(p3.execute_plan_action \<pi> M) \<^sup>c\<TTurnstile>\<^sub>= goal P3"
proof -
  let ?goal_atm = "Atom (predAtm goal_pred [])"

  let ?ga = "p3.resolve_instantiate \<pi>"

  from assms(2) have "wf_ground_action ?ga"
    using g_wf_pa_right wf_resolve_instantiate by simp
  hence "wf_effect objT (effect ?ga)"
    by (simp add: wf_ground_action_alt)
  hence "\<forall>ae \<in> set (adds (effect ?ga)). wf_fmla_atom objT ae"
    using wf_effect_alt by blast
  hence notin: "?goal_atm \<notin> set (adds (effect ?ga))"
    using goal_atm_not_wf by blast

  have end_basic: "wm_basic (p3.execute_plan_action \<pi> M)"
    using assms g_wf_pa_right p3.wf_execute_stronger p3.wf_wm_basic by simp

  (* Todo simplify / export *)
  from assms have "\<not>(valuation M) \<Turnstile> goal P3"
    using valuation_iff_close_world p3.wf_wm_basic by blast
  hence "\<not> (valuation M) (predAtm goal_pred [])"
    by simp
  hence "?goal_atm \<notin> M" using valuation_def by simp
  with notin have "\<not>?goal_atm \<in> p3.execute_plan_action \<pi> M"
    using p3.execute_plan_action_def p3.apply_effect_alt by simp
  hence "\<not>(valuation (p3.execute_plan_action \<pi> M)) (predAtm goal_pred [])"
    using valuation_def by simp
  hence "\<not>(valuation (p3.execute_plan_action \<pi> M)) \<Turnstile> goal P3"
    by simp
  thus ?thesis using assms valuation_iff_close_world
    end_basic by blast
qed

lemma g_init_not_sat: "\<not>p3.I \<^sup>c\<TTurnstile>\<^sub>= goal P3"
proof -
  have "(Atom (predAtm goal_pred [])) \<notin> I"
    using wf_P wf_world_model_def goal_atm_not_wf by fastforce
  hence "\<not>(valuation p3.I) \<Turnstile> goal P3"
    using valuation_def by simp
  thus ?thesis using p3.i_basic valuation_iff_close_world by blast
qed

lemma no_goal_pa_no_sat:
  assumes "p3.wf_world_model M" "\<not>M \<^sup>c\<TTurnstile>\<^sub>= goal P3" "\<pi>\<^sub>g \<notin> set \<pi>s" "p3.plan_action_path M \<pi>s M'"
  shows "\<not>M' \<^sup>c\<TTurnstile>\<^sub>= goal P3"
using assms proof (induction \<pi>s arbitrary: M)
  case Nil then show ?case
    using p3.valid_plan_def p3.valid_plan_from_def by auto
next
  case (Cons \<pi> \<pi>s)
  hence "p3.wf_plan_action \<pi>"
    using p3.plan_action_path_Cons p3.plan_action_enabled_def by blast
  hence "wf_plan_action \<pi>" using g_wf_pa_left \<open>\<pi>\<^sub>g \<notin> set (\<pi> # \<pi>s)\<close> by auto

  from Cons have 1: "p3.wf_world_model (p3.execute_plan_action \<pi> M)"
    using p3.wf_execute_stronger \<open>p3.wf_plan_action \<pi>\<close> by simp
  from Cons have 2: "\<not>(p3.execute_plan_action \<pi> M) \<^sup>c\<TTurnstile>\<^sub>= goal P3"
    using g_goal_unaffected \<open>wf_plan_action \<pi>\<close> by blast
  from Cons have 3: "\<pi>\<^sub>g \<notin> set \<pi>s" by simp
  from Cons have 4: "p3.plan_action_path (p3.execute_plan_action \<pi> M) \<pi>s M'"
    using p3.plan_action_path_Cons by simp

  from Cons.IH[OF 1 2 3 4] show ?case .
qed

lemma no_goal_pa_not_valid:
  assumes "\<pi>\<^sub>g \<notin> set \<pi>s"
  shows "\<not>p3.valid_plan \<pi>s"
proof -
  have "p3.valid_plan \<pi>s \<longleftrightarrow> (\<exists>M. p3.plan_action_path p3.I \<pi>s M \<and> M \<^sup>c\<TTurnstile>\<^sub>= goal P3)"
    using p3.valid_plan_def p3.valid_plan_from_def by simp
  (* with no_goal_pa_no_sat we get
    p3.plan_action_path p3.I \<pi>s M \<Longrightarrow> \<not>M \<^sup>c\<TTurnstile>\<^sub>= goal P3 *)
  with assms show ?thesis using g_init_not_sat no_goal_pa_no_sat p3.wf_I by blast
qed

lemma g_valid_plan_has_ga:
  "p3.valid_plan \<pi>s \<Longrightarrow> \<pi>\<^sub>g \<in> set \<pi>s"
  using no_goal_pa_not_valid by auto

lemma g_goal_sem_left:
  assumes "p3.plan_action_enabled \<pi>\<^sub>g M"
  shows "M \<^sup>c\<TTurnstile>\<^sub>= goal P"
using assms p3.plan_action_enabled_def wf_goal_pa
    resinst_goal_ac by auto

lemma g_exec_left:
  assumes "p3.wf_plan_action \<pi>" "\<pi> \<noteq> \<pi>\<^sub>g"
  shows "p3.execute_plan_action \<pi> M = execute_plan_action \<pi> M"
  using assms g_wf_pa_left g_exec_right by simp

lemma g_enab_left:
  assumes "p3.wf_plan_action \<pi>" "\<pi> \<noteq> \<pi>\<^sub>g"
  shows "p3.plan_action_enabled \<pi> M = plan_action_enabled \<pi> M"
  using assms g_wf_pa_left g_enab_right by simp

lemma g_execs_left:
  assumes "wf_world_model M" "\<pi>\<^sub>g \<notin> set \<pi>s" "p3.plan_action_path M \<pi>s M'"
  shows "plan_action_path M \<pi>s M'"
using assms proof (induction \<pi>s arbitrary: M)
  case (Cons \<pi> \<pi>s)
  hence neq: "\<pi> \<noteq> \<pi>\<^sub>g" and notin: "\<pi>\<^sub>g \<notin> set \<pi>s" by auto
  from Cons have enab3: "p3.plan_action_enabled \<pi> M" and path3: "p3.plan_action_path (p3.execute_plan_action \<pi> M) \<pi>s M'"
    by simp_all
  
  from enab3 have wf3: "p3.wf_plan_action \<pi>" using p3.plan_action_enabled_def by simp
  with enab3 have enab: "plan_action_enabled \<pi> M" using neq g_enab_left by simp
  from path3 wf3 have path2: "p3.plan_action_path (execute_plan_action \<pi> M) \<pi>s M'" using neq g_exec_left by simp

  from Cons enab have wf_m: "wf_world_model (execute_plan_action \<pi> M)" using wf_execute by simp

  have path: "plan_action_path (execute_plan_action \<pi> M) \<pi>s M'" using Cons.IH[OF wf_m notin path2] .

  from enab path show ?case using plan_action_path_Cons by simp
qed simp

theorem valid_plan_left:
  assumes "p3.valid_plan \<pi>s"
  shows "valid_plan (restore_plan_degoal \<pi>s)"
proof -
  let ?ogs = "restore_plan_degoal \<pi>s"
  from assms obtain ys where
    restore: "(?ogs @ [\<pi>\<^sub>g]) @ ys = \<pi>s" (* parantheses important for unification with plan_action_path_append_elim *)
    using g_valid_plan_has_ga sublist_just_until by fastforce
  from assms obtain M3 where
    fullpath: "p3.plan_action_path p3.I \<pi>s M3"
    using p3.valid_plan_def p3.valid_plan_from_def by auto
  then obtain M2 where
    path: "p3.plan_action_path p3.I (?ogs @ [\<pi>\<^sub>g]) M2"
    using p3.plan_action_path_append_elim restore by metis
  then obtain M1 where
    sol: "p3.plan_action_path p3.I ?ogs M1" and
    skip: "p3.plan_action_path M1 [\<pi>\<^sub>g] M2"
    using p3.plan_action_path_append_elim by blast

  from skip have "p3.plan_action_enabled \<pi>\<^sub>g M1"
    using plan_action_path_Cons by simp
  hence sat: "M1 \<^sup>c\<TTurnstile>\<^sub>= goal P"
    using g_goal_sem_left by simp
  moreover from sol have "plan_action_path p3.I ?ogs M1"
    using notin_sublist_until g_execs_left wf_I by fastforce
  ultimately show ?thesis using valid_plan_def valid_plan_from_def by auto
qed

theorem degoaled_valid_iff:
  "(\<exists>\<pi>s. valid_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s. p3.valid_plan \<pi>s)"
  using valid_plan_left valid_plan_right by auto

end

subsection \<open> Code Setup \<close>

lemmas goal_norm_code =
  ast_domain.goal_pred_def
  ast_domain.goal_pred_decl_def
  ast_domain.goal_ac_def
  ast_problem.term_goal_def
  ast_problem.degoal_dom_def
  ast_problem.degoal_prob_def
declare goal_norm_code[code]

end