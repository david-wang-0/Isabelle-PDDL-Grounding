theory PDDL_to_STRIPS
  imports "Classical_Planning.Classical_Abstract_Syntax"
    "Classical_Planning.Classical_Happening_Semantics"
    PDDL_Sema_Supplement STRIPS_Sema_Supplement Normalization_Definitions
    (* list linorder: *) "HOL-Library.List_Lexorder" "HOL-Library.Char_ord" (* only used to minimize negative literals *)
begin

term "sorted_list_of_set :: string set \<Rightarrow> string list"

text \<open>There are two big differences between normalized ground PDDL and
  STRIPS. Normalized PDDL formulas are pure conjunctions, but they can contain
  \<bottom> and negative atoms. These differences require workarounds:
- We introduce negative variants of all ground predicates in the STRIPS task.
  Init and operator effects are modified accordingly.
  TODO: only use negative variables where needed, i.e.: when the goal clause or
  operator preconditions contain the negative literal.
- A new static variable that is always false is introduced to be used in place of \<bottom>.
  Although technically not needed since it can always be removed from clauses,
  we also introduce a static variable for \<not>\<bottom>.
- Of course, we could also omit any operators whose preconditions contain \<bottom>, but this
  seemed easier.
\<close>

definition "v\<^sub>T \<equiv> ''+'' :: name"
definition "v\<^sub>F \<equiv> ''-'' :: name"
abbreviation "vpos p \<equiv> CHR ''+'' # predicate.name p"
abbreviation "vneg p \<equiv> CHR ''-'' # predicate.name p"
lemmas vb_defs = v\<^sub>T_def v\<^sub>F_def

text \<open>iceboxed because e.g. "pred_vpos = vpos \<circ> pred" \<close>
(*fun pred_vpos :: "predicate_decl \<Rightarrow> name" where
  "pred_vpos (PredDecl n args) = vpos n"
fun pred_vneg :: "predicate_decl \<Rightarrow> name" where
  "pred_vneg (PredDecl n args) = vneg n"*)

(* Converting formulas into variables *)
(* assumes is_lit_plus and not Eq *)
fun lit_as_var :: "'a atom formula \<Rightarrow> name" where
  "lit_as_var \<bottom> = v\<^sub>F" |
  "lit_as_var (\<^bold>\<not>\<bottom>) = v\<^sub>T" |
  "lit_as_var (Atom (predAtm n args)) = vpos n" |
  "lit_as_var (\<^bold>\<not>(Atom (predAtm n args))) = vneg n"

definition fmla_as_vars :: "'a atom formula \<Rightarrow> name list" where
  "fmla_as_vars F \<equiv> map lit_as_var (un_and F)"

fun lit_as_goal :: "'a atom formula \<Rightarrow> (name \<times> bool)" where
  "lit_as_goal \<bottom> = (v\<^sub>F, True)" |
  "lit_as_goal (\<^bold>\<not>\<bottom>) = (v\<^sub>T, True)" | (* equivalent: (v\<^sub>F, False) *)
  "lit_as_goal (Atom (predAtm n args)) = (vpos n, True)" |
  "lit_as_goal (\<^bold>\<not>(Atom (predAtm n args))) = (vpos n, False)"

abbreviation "fmla_as_goals F \<equiv> map lit_as_goal (un_and F)"

(* atm_as_vpos is technically subsumed by lit_as_var *)
fun atm_as_vpos :: "'a atom formula \<Rightarrow> name" where
  "atm_as_vpos (Atom (predAtm n args)) = vpos n"
fun atm_as_vneg :: "'a atom formula \<Rightarrow> name" where
  "atm_as_vneg (Atom (predAtm n args)) = vneg n"

(* add effects take precedence *)
(* removes duplicates *)
fun fix_effect :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "fix_effect (Effect add del) = Effect add (filter (\<lambda>x. x \<notin> set add) del)"

fun as_strips_op :: "ast_action_schema \<Rightarrow> name strips_operator" where
  "as_strips_op (Action_Schema n args pre eff) =
  (let eff' = fix_effect eff; add = adds eff'; del = dels eff' in
  \<lparr>
    precondition_of = fmla_as_vars pre
    , add_effects_of = map atm_as_vpos add @ map atm_as_vneg del
    , delete_effects_of = map atm_as_vpos del @ map atm_as_vneg add \<rparr>)"

context ast_problem begin

abbreviation "strips_ops \<equiv> map as_strips_op (actions D)"

definition "pos_vars = v\<^sub>T # map (vpos \<circ> pred) (predicates D)"
definition "neg_vars = v\<^sub>F # map (vneg \<circ> pred) (predicates D)"
abbreviation "strips_vars \<equiv> pos_vars @ neg_vars"
lemmas vars_defs = pos_vars_def neg_vars_def
(*
  initD: ["A", "B"]
  pvars: + A B C,
  nvars: - a b c,
  "init": [+, A, B]
  empty: +:0, A:0, B:0, C:0, -:1, a:1, b:1, c:1
  init: +:1, A:1, B:1, C:0, -:0, a:0, b:0, c:1
*)

abbreviation "pos_empty \<equiv> fold (\<lambda>v s. s(v \<mapsto> False)) pos_vars (\<lambda>x. None)"
definition "empty_state \<equiv> fold (\<lambda>v s. s(v \<mapsto> True)) neg_vars pos_empty"
definition (in -) "upd_init a s \<equiv> s(atm_as_vpos a \<mapsto> True, atm_as_vneg a \<mapsto> False)"
definition strips_init :: "name strips_state" where
  "strips_init \<equiv> fold upd_init (init P) empty_state"
lemmas init_defs = empty_state_def upd_init_def strips_init_def

fun (in -) upd_goal where "upd_goal (v, b) s = s(v \<mapsto> b)"
definition strips_goal :: "name strips_state" where
  "strips_goal \<equiv> fold upd_goal (fmla_as_goals (goal P)) (\<lambda>x. None)"

definition as_strips :: "name strips_problem" where
  "as_strips \<equiv> \<lparr> 
    variables_of = strips_vars
    , operators_of = strips_ops
    , initial_of = strips_init
    , goal_of = strips_goal \<rparr>"

definition "restore_pddl_pa op \<equiv>
  PAction (ac_name (actions D ! the (find_index op strips_ops))) []"
definition "restore_pddl_plan op_is \<equiv> map restore_pddl_pa op_is"

end text \<open>context ast_problem\<close>

lemmas to_strips_code =
  ast_problem.vars_defs
  ast_problem.init_defs
  ast_problem.strips_goal_def
  ast_problem.as_strips_def
  ast_problem.restore_pddl_pa_def
  ast_problem.restore_pddl_plan_def
declare to_strips_code[code]

value "ast_problem.as_strips" (* checking if code exists *)

subsection \<open> Alternative definitions \<close>

context ast_problem begin

lemma as_strips_op_sel [simp]:
  fixes ac
  defines "eff' \<equiv> fix_effect (ac_eff ac)"
  shows "precondition_of (as_strips_op ac) = fmla_as_vars (ac_pre ac)"
  "add_effects_of (as_strips_op ac) = map atm_as_vpos (adds eff') @ map atm_as_vneg (dels eff')"
  "delete_effects_of (as_strips_op ac) = map atm_as_vpos (dels eff') @ map atm_as_vneg (adds eff')"
  apply (cases ac) apply simp_all unfolding as_strips_op.simps Let_def apply simp
  apply (cases ac) apply simp_all unfolding as_strips_op.simps Let_def eff'_def apply simp
  apply (cases ac) apply simp_all unfolding as_strips_op.simps Let_def eff'_def by simp

lemma as_strips_sel [simp]:
  "as_strips \<^sub>\<V> = strips_vars"
  "as_strips \<^sub>\<O> = map as_strips_op (actions D)"
  "as_strips \<^sub>I = strips_init"
  "as_strips \<^sub>G = strips_goal"
  unfolding as_strips_def by simp_all
end text \<open>context ast_problem\<close>

subsection \<open> Formula structures \<close>

context ast_domain begin
definition "wf_pred n \<equiv> PredDecl n [] \<in> set (predicates D)"
fun wf_lit where
  "wf_lit \<bottom> = True" |
  "wf_lit (\<^bold>\<not>\<bottom>) = True" |
  "wf_lit (Atom (predAtm n [])) = wf_pred n" |
  "wf_lit (\<^bold>\<not>(Atom (predAtm n []))) = wf_pred n" |
  "wf_lit _ = False"
abbreviation "wf_lit_atom F \<equiv> wf_lit F \<and> is_predAtom F"
(* ? *)
lemma wf_lit_plus: "wf_lit L \<Longrightarrow> is_lit_plus L"
  by (cases L rule: wf_lit.cases) simp_all
end text \<open>context ast_domain\<close>


(* technically, also holds in ast_domain but easier to prove here with sig_Some *)
context wf_ast_domain begin
lemma wf_predatom_lit:
  "wf_pred_atom (\<lambda>x. None) (n, args) \<longleftrightarrow> args = [] \<and> wf_pred n"
  (is "?L \<longleftrightarrow> ?R")
proof -
  have notypes: "list_all2 (is_of_type (\<lambda>x. None)) vs Ts \<longleftrightarrow> vs = [] \<and> Ts = []" for vs Ts
    unfolding is_of_type_def of_type_def by (cases vs; cases Ts) force+

  have "?L \<longleftrightarrow> (\<exists>Ts. sig n = Some Ts \<and> list_all2 (is_of_type (\<lambda>x. None)) args Ts)"
    unfolding wf_pred_atom.simps using case_optionE by fastforce
  also have "... \<longleftrightarrow> (sig n = Some [] \<and> args = [])"
    using notypes by metis
  also have "... \<longleftrightarrow> ?R"
    using sig_Some wf_pred_def by blast
  finally show ?thesis .
qed

lemma wf_empty_lit:
  assumes "is_lit_plus L" "wf_fmla (\<lambda>x. None) L"
  shows "wf_lit L"
  using assms wf_predatom_lit[unfolded wf_pred_atom.simps]
  by (cases L rule: wf_lit.cases) force+

lemma wf_empty_lits:
  assumes "is_conj F" "wf_fmla (\<lambda>x. None) F"
  shows "list_all1 wf_lit (un_and F)"
  using assms wf_empty_lit
  by (induction F) auto

lemma wf_empty_atom:
  assumes "wf_fmla_atom (\<lambda>x. None) L"
  shows "wf_lit_atom L"
proof -
  from assms have "is_lit_plus L"
    by (cases L rule: wf_fmla_atom.cases) simp_all
  with assms show ?thesis using wf_empty_lit unfolding wf_fmla_atom_alt by blast
qed
end text \<open>context wf_ast_domain\<close>


context grounded_problem begin

lemma constT_empty: "constT = (\<lambda>x. None)"
  using grounded_dom
  unfolding grounded_dom_def constT_def by auto
lemma objT_empty: "objT = (\<lambda>x. None)"
  using grounded_prob constT_empty
  unfolding grounded_prob_def objT_def by auto

(* technically, wf_grounded_problem suffices for this one *)
lemma ac_tyt_empty:
  assumes "ac \<in> set (actions D)" shows "ac_tyt ac = (\<lambda>x. None)"
proof -
  from assms have "grounded_ac ac" using grounded_dom grounded_dom_def by blast
  hence "ac_params ac = []" by (cases ac) simp
  thus "?thesis"
    apply (intro ext)
    subgoal for x
      using constT_empty by (cases x) simp_all
    done
qed

lemma (in grounded_normalized_problem) wf_pre_lits:
  assumes "ac \<in> set (actions D)" shows "list_all1 wf_lit (un_and (ac_pre ac))"
proof -
  have "wf_fmla (\<lambda>x. None) (ac_pre ac)"
    using assms wf_D(7) ac_tyt_empty wf_action_schema_alt by metis
  moreover have "is_conj (ac_pre ac)"
    using assms normed_prob
    unfolding prec_normed_dom_def by simp
  ultimately show ?thesis using wf_empty_lits by blast
qed

lemma wf_eff_lits:
  assumes "ac \<in> set (actions D)"
  shows "list_all1 wf_lit_atom (adds (ac_eff ac))" (is ?A)
        "list_all1 wf_lit_atom (dels (ac_eff ac))" (is ?B)
  using assms ac_tyt_empty
  using wf_D(7) wf_action_schema_alt wf_effect_alt wf_empty_atom
    by metis+

lemma wf_init_lits:
  shows "list_all1 wf_lit_atom (init P)"
  using wf_empty_atom wf_P(4)
  unfolding wf_world_model_def objT_empty by blast

end text \<open>context wf_grounded_problem \<close>

lemma (in grounded_normalized_problem) wf_goal_lits:
  "list_all1 wf_lit (un_and (goal P))"
  using objT_empty wf_P(5) wf_empty_lits normed_prob by auto

subsection \<open> STRIPS task is WF \<close>

context ast_problem begin

lemma (in ast_problem) wf_lit_covered:
  assumes "wf_lit F"
  shows "lit_as_var F \<in> set strips_vars"
  unfolding vars_defs
  using assms wf_pred_def by (cases F rule: wf_lit.cases) force+

lemma (in ast_problem) wf_lit_goal_covered:
  assumes "wf_lit F"
  shows "fst (lit_as_goal F) \<in> set strips_vars"
  unfolding vars_defs
  using assms wf_pred_def by (cases F rule: wf_lit.cases) force+

lemma (in ast_problem) wf_lit_atom_covered:
  assumes "wf_lit_atom F" shows
    "atm_as_vpos F \<in> set pos_vars"
    "atm_as_vneg F \<in> set neg_vars"
  unfolding vars_defs
  using assms wf_pred_def apply (cases F rule: wf_lit.cases) apply force+
  using assms wf_pred_def apply (cases F rule: wf_lit.cases) apply force+
  done

lemma (in ast_problem) wf_lits_covered:
  assumes "list_all1 wf_lit (un_and F)"
  shows "set (fmla_as_vars F) \<subseteq> set strips_vars"
  using assms wf_lit_covered unfolding fmla_as_vars_def by auto

lemma (in ast_problem) wf_lits_goal_covered:
  assumes "list_all1 wf_lit (un_and F)"
  shows "fst ` set (fmla_as_goals F) \<subseteq> set strips_vars"
  using assms wf_lit_goal_covered apply simp
  using image_iff list.set_map subsetI by blast

end text \<open>context ast_problem \<close>

lemma (in grounded_normalized_problem) wf_as_strips_op:
  assumes "ac \<in> set (actions D)"
  shows "is_valid_operator_strips as_strips (as_strips_op ac)"
proof -
  have C1: "\<forall>v\<in>set (precondition_of (as_strips_op ac)). v \<in> set strips_vars"
    using assms wf_pre_lits wf_lits_covered
    unfolding as_strips_op_sel by blast

  obtain a d where eff: "ac_eff ac = Effect a d" by (cases "ac_eff ac") simp

  have "\<forall>v \<in> atm_as_vpos ` set a. v \<in> set strips_vars"
          "\<forall>v \<in> atm_as_vneg ` set a. v \<in> set strips_vars"
          "\<forall>v \<in> atm_as_vpos ` set d. v \<in> set strips_vars"
          "\<forall>v \<in> atm_as_vneg ` set d. v \<in> set strips_vars"
    using assms eff wf_eff_lits wf_lit_atom_covered by fastforce+

  hence C2_3: "\<forall>v\<in>set (add_effects_of (as_strips_op ac)). v \<in> set strips_vars"
                    "\<forall>v\<in>set (delete_effects_of (as_strips_op ac)). v \<in> set strips_vars"
    unfolding eff as_strips_op_sel by auto

  let ?adds = "adds (fix_effect (ac_eff ac))"
  let ?dels = "dels (fix_effect (ac_eff ac))"

  have lits: "\<forall>x\<in>set ?adds. wf_lit_atom x"
    "\<forall>x\<in>set ?dels. wf_lit_atom x"
    using wf_eff_lits[OF assms] apply (cases "ac_eff ac") apply simp_all
    using wf_eff_lits[OF assms] apply (cases "ac_eff ac") apply simp_all
    done
  have v_inj: "x \<noteq> y \<Longrightarrow> wf_lit_atom x \<Longrightarrow> wf_lit_atom y \<Longrightarrow>
    atm_as_vpos x \<noteq> atm_as_vpos y \<and> atm_as_vneg x \<noteq> atm_as_vneg y" for x y
    apply (cases x rule: wf_lit.cases; cases y rule: wf_lit.cases; simp)
    subgoal for u v apply (cases u; cases v) by simp done

  have adds_vs_dels: "atm_as_vpos ` set ?adds \<inter> atm_as_vpos ` set ?dels = {}" (is ?A)
          "atm_as_vneg ` set ?adds \<inter> atm_as_vneg ` set ?dels = {}" (is ?B)
  proof -
    have "set ?adds \<inter> set ?dels = {}"
      by (cases "ac_eff ac") auto
    hence neq: "\<forall>x \<in> set ?adds. \<forall>y \<in> set ?dels. x \<noteq> y" by blast
    have "\<forall>x \<in> set ?adds. \<forall>y \<in> set ?dels. atm_as_vpos x \<noteq> atm_as_vpos y"
         "\<forall>x \<in> set ?adds. \<forall>y \<in> set ?dels. atm_as_vneg x \<noteq> atm_as_vneg y"
      using lits v_inj neq by metis+
    thus ?A ?B by blast+
  qed
  have pos_vs_neg: "atm_as_vpos ` set ?adds \<inter> atm_as_vneg ` set ?adds = {}" (is ?A)
          "atm_as_vpos ` set ?dels \<inter> atm_as_vneg ` set ?dels = {}" (is ?B)
  proof -
    {
      fix x y l assume "l = ?adds \<or> l = ?dels" "x \<in> set l" "y \<in> set l"
      hence "wf_lit_atom x" "wf_lit_atom y" by (auto simp add: lits)
      hence "atm_as_vneg x \<noteq> atm_as_vpos y"
        by (cases x rule: is_predAtom.cases; cases y rule: is_predAtom.cases) simp_all
    }
    thus ?A ?B by force+
  qed

  have C4_5: "\<forall>v\<in>set (add_effects_of (as_strips_op ac)). v \<notin> set (delete_effects_of (as_strips_op ac))"
             "\<forall>v\<in>set (delete_effects_of (as_strips_op ac)). v \<notin> set (add_effects_of (as_strips_op ac))"
    apply simp_all
    using adds_vs_dels pos_vs_neg by (metis Set.set_insert Un_iff insert_disjoint(1))+

  from C1 C2_3 C4_5 show ?thesis
    unfolding is_valid_operator_strips_def Let_def
    unfolding ListMem_iff Ball_set[symmetric]
    unfolding as_strips_sel by blast    
qed

lemma (in grounded_problem) init_covered: "strips_init v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars"
proof -
  have "fold (\<lambda>v s. s(v \<mapsto> b)) vars s v \<noteq> None \<longleftrightarrow> v \<in> set vars \<or> s v \<noteq> None"
    for b vars s by (induction vars arbitrary: s) simp_all
  hence "empty_state v \<noteq> None \<longleftrightarrow> v \<in> set neg_vars \<or> v \<in> set pos_vars"
    unfolding empty_state_def by metis
  hence empty: "empty_state v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars" by force

  have "fold upd_init vars s v \<noteq> None \<longleftrightarrow> s v \<noteq> None \<or>
    (\<exists>x \<in> set vars. atm_as_vpos x = v \<or> atm_as_vneg x = v)" for vars s
    unfolding upd_init_def by (induction vars arbitrary: s) auto
  moreover have "\<exists>x \<in> set (init P). atm_as_vpos x = v \<or> atm_as_vneg x = v \<Longrightarrow> v \<in> set strips_vars"
    using wf_init_lits wf_lit_atom_covered by auto
  ultimately show ?thesis unfolding strips_init_def using empty by blast
qed

lemma (in grounded_normalized_problem) goal_covered:
  assumes "strips_goal v \<noteq> None"
  shows "v \<in> set strips_vars"
proof -
  have "fold upd_goal xs s v \<noteq> None \<longleftrightarrow> s v \<noteq> None \<or> v \<in> fst ` set xs"
    for xs s apply (induction xs arbitrary: s) apply auto done
  hence "v \<in> fst ` set (fmla_as_goals (goal P))"
    using assms unfolding strips_goal_def by metis
  thus ?thesis using wf_goal_lits wf_lits_goal_covered by blast
qed

theorem (in grounded_normalized_problem) wf_as_strips: "is_valid_problem_strips as_strips"
  unfolding is_valid_problem_strips_def Let_def as_strips_sel
  apply (intro conjI)
  using wf_as_strips_op unfolding Ball_set[symmetric] apply simp
  using init_covered apply (meson ListMem_iff)
  using goal_covered by (meson ListMem_iff)

sublocale grounded_normalized_problem \<subseteq> s: valid_strips as_strips
  using wf_as_strips by unfold_locales

subsection \<open> STRIPS task semantics are preserved \<close>

lemma (in grounded_problem)
  "wf_pred n \<longleftrightarrow> PredDecl n [] \<in> set (predicates D)"
  "wf_pred n \<longleftrightarrow> n \<in> pred ` set (predicates D)"
  "wf_pred n \<longleftrightarrow> vpos n \<in> pred_vpos ` set (predicates D)"
    (* not pos_vars, tho, because n could be '''' and vpos n = v\<^sub>T *)
  oops

context ast_problem begin
(* strips state equivalent *)

term empty_state
definition strips_model :: "world_model \<Rightarrow> name strips_state" where
  "strips_model M v \<equiv> undefined"

thm wf_ast_domain.wf_empty_atom (* use this to work with wf_world_model M *)
lemma strips_model_props:
  assumes "wf_world_model M"
    "wf_pred n"
  shows
    "strips_init = strips_model I"
    "strips_model M v\<^sub>T = Some True"
    "strips_model M v\<^sub>F = Some False"
    "strips_model M v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars"
    "strips_model M (vpos n) = Some (Atom (predAtm n []) \<in> M)"
    "strips_model M (vneg n) = Some (Atom (predAtm n []) \<notin> M)"
  oops

(* other direction equivalent *)

definition wf_state :: "name strips_state \<Rightarrow> bool" where
  "wf_state s \<equiv> s v\<^sub>T = Some True \<and>
    s v\<^sub>F = Some False \<and>
    (\<forall>v. s v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars) \<and>
    (\<forall>n b. s (vpos n) = Some b \<longleftrightarrow> s (vneg n) = Some (\<not>b))"

definition pddl_model :: "name strips_state \<Rightarrow> world_model" where
  "pddl_model s = undefined"
lemma pddl_model_props:
  assumes "valid_strips_state s" "wf_pred n"
  shows "Atom (predAtm n []) \<in> pddl_model s \<longleftrightarrow> s (vpos n) = Some True"
  oops


fun (in ast_domain) strips_pa where
  "strips_pa (PAction n args) = as_strips_op (the (resolve_action_schema n))"



theorem (in grounded_normalized_problem) valid_plan_right:
  assumes "valid_plan \<pi>s"
  shows "is_serial_solution_for_problem as_strips (map strips_pa \<pi>s)"
  oops

theorem (in grounded_normalized_problem) restore_pddl_plan:
  assumes "is_serial_solution_for_problem as_strips \<pi>s'"
  shows "valid_plan (restore_pddl_plan \<pi>s')"
  oops

corollary (in grounded_normalized_problem) valid_plan_iff:
  "(\<exists>\<pi>s. valid_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. is_serial_solution_for_problem as_strips \<pi>s')"
  oops


end text \<open> context ast_problem \<close>
end