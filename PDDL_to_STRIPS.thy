 
theory PDDL_to_STRIPS
  imports "Classical_Planning.Classical_Abstract_Syntax"
    "Classical_Planning.Classical_Happening_Semantics"
    Tree_Decomp_Grounding_Base.PDDL_Sema_Supplement
    Tree_Decomp_Grounding_Base.STRIPS_Sema_Supplement
    Tree_Decomp_Grounding_Base.Normalization_Definitions
    Tree_Decomp_Grounding_Base.Numeric_Free
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

definition "v\<^sub>T \<equiv> STR ''+'' :: name"
definition "v\<^sub>F \<equiv> STR ''-'' :: name"
abbreviation "vpos p \<equiv> STR ''+'' + predicate.name p"
abbreviation "vneg p \<equiv> STR ''-'' + predicate.name p"
lemmas vb_defs = v\<^sub>T_def v\<^sub>F_def

lemma lit_prepend_inj: "(s + a = s + b) = (a = b)" for s a b :: name
  by (metis String.implode_explode_eq plus_literal.rep_eq same_append_eq)

lemma vneg_neq_vpos: "vneg p \<noteq> vpos q"
proof
  assume "vneg p = vpos q"
  hence "literal.explode (STR ''-'' + predicate.name p)
       = literal.explode (STR ''+'' + predicate.name q)" by simp
  moreover have "literal.explode (STR ''-'' :: name) = ''-''"
                "literal.explode (STR ''+'' :: name) = ''+''" by eval+
  ultimately show False by (simp add: plus_literal.rep_eq)
qed

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
  "fix_effect (Effect add del nums) = Effect add (filter (\<lambda>x. x \<notin> set add) del) nums"

fun as_strips_op :: "ast_classical_action_schema \<Rightarrow> name strips_operator" where
  "as_strips_op (SimpleActionSchema (ActionHead n args) (SimpleActionBody pre eff)) =
  (let eff' = fix_effect eff; add = adds eff'; del = dels eff' in
  \<lparr>
    precondition_of = fmla_as_vars pre
    , add_effects_of = map atm_as_vpos add @ map atm_as_vneg del
    , delete_effects_of = map atm_as_vpos del @ map atm_as_vneg add \<rparr>)"

context ast_classical_problem begin

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

definition "restore_pddl_pa opp \<equiv>
  SimplePlanAction (ac_name (actions D ! the (find_index opp strips_ops))) []"
definition "restore_pddl_plan op_is \<equiv> map restore_pddl_pa op_is"

end text \<open>context ast_classical_problem\<close>

lemmas to_strips_code =
  ast_classical_problem.vars_defs
  ast_classical_problem.init_defs
  ast_classical_problem.strips_goal_def
  ast_classical_problem.as_strips_def
  ast_classical_problem.restore_pddl_pa_def
  ast_classical_problem.restore_pddl_plan_def
declare to_strips_code[code]

value "ast_classical_problem.as_strips" (* checking if code exists *)

subsection \<open> Alternative definitions \<close>

context ast_classical_problem begin

lemma as_strips_op_sel [simp]:
  fixes ac
  defines "eff' \<equiv> fix_effect (ac_eff ac)"
  shows "precondition_of (as_strips_op ac) = fmla_as_vars (ac_pre ac)"
  "add_effects_of (as_strips_op ac) = map atm_as_vpos (adds eff') @ map atm_as_vneg (dels eff')"
  "delete_effects_of (as_strips_op ac) = map atm_as_vpos (dels eff') @ map atm_as_vneg (adds eff')"
  apply (cases ac)
  subgoal for head body by (cases head, cases body) (simp add: Let_def)
  apply (cases ac)
  subgoal for head body by (cases head, cases body) (simp add: Let_def eff'_def)
  apply (cases ac)
  subgoal for head body by (cases head, cases body) (simp add: Let_def eff'_def)
  done

lemma as_strips_sel [simp]:
  "as_strips \<^sub>\<V> = strips_vars"
  "as_strips \<^sub>\<O> = map as_strips_op (actions D)"
  "as_strips \<^sub>I = strips_init"
  "as_strips \<^sub>G = strips_goal"
  unfolding as_strips_def by simp_all
end text \<open>context ast_classical_problem\<close>

subsection \<open> Formula structures \<close>

context ast_classical_domain begin
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
end text \<open>context ast_classical_domain\<close>


(* technically, also holds in ast_classical_domain but easier to prove here with sig_Some *)
context wf_ast_classical_domain begin
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

text \<open>A numeric-free (\<^const>\<open>num_free_fmla\<close>) well-formed literal under the empty type environment
  is a \<^const>\<open>wf_lit\<close>: the numeric-free hypothesis rules out the \<open>numericXxxAtm\<close> atoms (which
  \<open>wf_lit\<close> would otherwise reject), an \<open>eqAtm\<close> is impossible under \<open>\<lambda>x. None\<close>
  (\<open>wf_atom (eqAtm a b)\<close> needs both entities typed), and a \<open>predAtm\<close> must have empty arguments and
  a declared predicate (@{thm wf_predatom_lit}). The numeric-free hypothesis is the
  propositional-fragment restriction (see \<^theory>\<open>Tree_Decomp_Grounding_Base.Numeric_Free\<close>); it
  holds for the grounded+normalized input fed to the STRIPS backend.\<close>
lemma wf_empty_lit:
  assumes "num_free_fmla L" "is_lit_plus L" "wf_fmla (\<lambda>x. None) L"
  shows "wf_lit L"
  using assms
proof (cases L rule: is_lit_plus.cases)
  case (3 a) \<comment> \<open>\<open>L = Atom a\<close>\<close>
  then show ?thesis using assms by (cases a) (auto simp: wf_predatom_lit simp del: wf_pred_atom.simps)
next
  case (4 a) \<comment> \<open>\<open>L = \<^bold>\<not> (Atom a)\<close>\<close>
  then show ?thesis using assms by (cases a) (auto simp: wf_predatom_lit simp del: wf_pred_atom.simps)
qed auto


lemma wf_empty_lits:
  assumes "num_free_fmla F" "is_conj F" "wf_fmla (\<lambda>x. None) F"
  shows "(\<forall>x \<in> set (un_and F). wf_lit x)"
  using assms wf_empty_lit
  by (induction F) auto

lemma wf_empty_atom:
  assumes "wf_fmla_atom (\<lambda>x. None) L"
  shows "wf_lit_atom L"
proof -
  from assms have lp: "is_lit_plus L"
    by (cases L rule: wf_fmla_atom.cases) simp_all
  from assms have nf: "num_free_fmla L"
    by (cases L rule: wf_fmla_atom.cases) auto
  from assms have pa: "is_predAtom L"
    by (cases L rule: wf_fmla_atom.cases) auto
  from assms have wff: "wf_fmla (\<lambda>x. None) L"
    unfolding wf_fmla_atom_alt by simp
  have "wf_lit L" by (rule wf_empty_lit[OF nf lp wff])
  with pa show "wf_lit_atom L" by simp
qed
end text \<open>context wf_ast_classical_domain\<close>


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
  hence acp: "ac_params ac = []" by (cases ac rule: grounded_ac.cases) auto
  show ?thesis
  proof (rule ext)
    fix x show "ac_tyt ac x = None" by (cases x) (simp_all add: ac_tyt_def acp constT_empty)
  qed
qed

lemma (in grounded_normalized_problem) wf_pre_lits:
  assumes "ac \<in> set (actions D)" "num_free_ac ac"
  shows "(\<forall>x \<in> set (un_and (ac_pre ac)). wf_lit x)"
proof -
  have wfa: "wf_classical_action_schema ac" using assms(1) wf_D(3) by blast
  have "wf_fmla (ac_tyt ac) (ac_pre ac)"
    using wfa by (cases ac rule: ast_classical_action_schema_cases_unfold) (auto simp: ac_tyt_def Let_def)
  hence "wf_fmla (\<lambda>x. None) (ac_pre ac)" using ac_tyt_empty[OF assms(1)] by simp
  moreover have "is_conj (ac_pre ac)"
    using assms(1) normed_prob
    unfolding prec_normed_dom_def by simp
  moreover have "num_free_fmla (ac_pre ac)"
    using assms(2) unfolding num_free_ac_def by simp
  ultimately show ?thesis using wf_empty_lits by blast
qed

lemma wf_eff_lits:
  assumes "ac \<in> set (actions D)"
  shows "(\<forall>x \<in> set (adds (ac_eff ac)). wf_lit_atom x)" (is ?A)
        "(\<forall>x \<in> set (dels (ac_eff ac)). wf_lit_atom x)" (is ?B)
proof -
  have wfa: "wf_classical_action_schema ac" using assms wf_D(3) by blast
  have "wf_effect (ac_tyt ac) (ac_eff ac)"
    using wfa by (cases ac rule: ast_classical_action_schema_cases_unfold) (auto simp: ac_tyt_def Let_def)
  hence eff: "wf_effect (\<lambda>x. None) (ac_eff ac)" using ac_tyt_empty[OF assms] by simp
  show ?A using eff wf_empty_atom by (cases "ac_eff ac") auto
  show ?B using eff wf_empty_atom by (cases "ac_eff ac") auto
qed

lemma wf_init_lits:
  assumes "\<forall>f \<in> set (init P). num_free_fmla f"
  shows "(\<forall>x \<in> set (init P). wf_lit_atom x)"
proof (rule ballI)
  fix x assume x: "x \<in> set (init P)"
  from x wf_P(4) have disj: "wf_fmla_atom objT x \<or> wf_func_assign x" by blast
  from x assms have nf: "num_free_fmla x" by blast
  have "wf_fmla_atom objT x"
    using disj nf by (cases x rule: wf_func_assign.cases) auto
  thus "wf_lit_atom x" using wf_empty_atom unfolding objT_empty by blast
qed

end text \<open>context wf_grounded_problem \<close>

lemma (in grounded_normalized_problem) wf_goal_lits:
  assumes "num_free_fmla (goal P)"
  shows "(\<forall>x \<in> set (un_and (goal P)). wf_lit x)"
  using assms objT_empty wf_P(5) wf_empty_lits normed_prob by auto

subsection \<open> STRIPS task is WF \<close>

context ast_classical_problem begin

lemma (in ast_classical_problem) wf_lit_covered:
  assumes "wf_lit F"
  shows "lit_as_var F \<in> set strips_vars"
  unfolding vars_defs
  using assms wf_pred_def by (cases F rule: wf_lit.cases) force+

lemma (in ast_classical_problem) wf_lit_goal_covered:
  assumes "wf_lit F"
  shows "fst (lit_as_goal F) \<in> set strips_vars"
  unfolding vars_defs
  using assms wf_pred_def by (cases F rule: wf_lit.cases) force+

lemma (in ast_classical_problem) wf_lit_atom_covered:
  assumes "wf_lit_atom F" shows
    "atm_as_vpos F \<in> set pos_vars"
    "atm_as_vneg F \<in> set neg_vars"
  unfolding vars_defs
  using assms wf_pred_def apply (cases F rule: wf_lit.cases) apply force+
  using assms wf_pred_def apply (cases F rule: wf_lit.cases) apply force+
  done

lemma (in ast_classical_problem) wf_lits_covered:
  assumes "(\<forall>x \<in> set (un_and F). wf_lit x)"
  shows "set (fmla_as_vars F) \<subseteq> set strips_vars"
  using assms wf_lit_covered unfolding fmla_as_vars_def by auto

lemma (in ast_classical_problem) wf_lits_goal_covered:
  assumes "(\<forall>x \<in> set (un_and F). wf_lit x)"
  shows "fst ` set (fmla_as_goals F) \<subseteq> set strips_vars"
  using assms wf_lit_goal_covered apply simp
  using image_iff list.set_map subsetI by blast

end text \<open>context ast_classical_problem \<close>

lemma (in grounded_normalized_problem) wf_as_strips_op:
  assumes "ac \<in> set (actions D)" "num_free_ac ac"
  shows "is_valid_operator_strips as_strips (as_strips_op ac)"
proof -
  have C1: "\<forall>v\<in>set (precondition_of (as_strips_op ac)). v \<in> set strips_vars"
    using assms wf_pre_lits wf_lits_covered
    unfolding as_strips_op_sel by blast

  obtain a d n where eff: "ac_eff ac = Effect a d n" by (cases "ac_eff ac") simp

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
    using wf_eff_lits[OF assms(1)] apply (cases "ac_eff ac") apply simp_all
    using wf_eff_lits[OF assms(1)] apply (cases "ac_eff ac") apply simp_all
    done
  have v_inj: "x \<noteq> y \<Longrightarrow> wf_lit_atom x \<Longrightarrow> wf_lit_atom y \<Longrightarrow>
    atm_as_vpos x \<noteq> atm_as_vpos y \<and> atm_as_vneg x \<noteq> atm_as_vneg y" for x y
    apply (cases x rule: wf_lit.cases; cases y rule: wf_lit.cases; simp)
    subgoal for u v apply (cases u; cases v) by (simp add: lit_prepend_inj) done

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
        by (cases x rule: is_predAtom.cases; cases y rule: is_predAtom.cases)
           (simp_all add: vneg_neq_vpos)
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

locale grounded_normalized_numeric_free_problem =
  grounded_normalized_problem + numeric_free_problem

lemma (in grounded_normalized_numeric_free_problem) init_covered: "strips_init v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars"
proof -
  have inf: "\<forall>f\<in>set (init P). num_free_fmla f" using num_free_prob unfolding num_free_prob_def by blast
  have "fold (\<lambda>v s. s(v \<mapsto> b)) vars s v \<noteq> None \<longleftrightarrow> v \<in> set vars \<or> s v \<noteq> None"
    for b vars s by (induction vars arbitrary: s) simp_all
  hence "empty_state v \<noteq> None \<longleftrightarrow> v \<in> set neg_vars \<or> v \<in> set pos_vars"
    unfolding empty_state_def by metis
  hence empty: "empty_state v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars" by force

  have "fold upd_init vars s v \<noteq> None \<longleftrightarrow> s v \<noteq> None \<or>
    (\<exists>x \<in> set vars. atm_as_vpos x = v \<or> atm_as_vneg x = v)" for vars s
    unfolding upd_init_def by (induction vars arbitrary: s) auto
  moreover have "\<exists>x \<in> set (init P). atm_as_vpos x = v \<or> atm_as_vneg x = v \<Longrightarrow> v \<in> set strips_vars"
    using wf_init_lits[OF inf] wf_lit_atom_covered by auto
  ultimately show ?thesis unfolding strips_init_def using empty by blast
qed

lemma (in grounded_normalized_numeric_free_problem) goal_covered:
  assumes "strips_goal v \<noteq> None"
  shows "v \<in> set strips_vars"
proof -
  have gnf: "num_free_fmla (goal P)" using num_free_prob unfolding num_free_prob_def by blast
  have "fold upd_goal xs s v \<noteq> None \<longleftrightarrow> s v \<noteq> None \<or> v \<in> fst ` set xs"
    for xs s apply (induction xs arbitrary: s) apply auto done
  hence "v \<in> fst ` set (fmla_as_goals (goal P))"
    using assms unfolding strips_goal_def by metis
  thus ?thesis using wf_goal_lits[OF gnf] wf_lits_goal_covered by blast
qed

theorem (in grounded_normalized_numeric_free_problem) wf_as_strips: "is_valid_problem_strips as_strips"
proof -
  have ndom: "\<forall>a\<in>set (actions D). num_free_ac a"
    using num_free_prob unfolding num_free_prob_def num_free_dom_def by blast
  have ops: "\<forall>ac\<in>set (actions D). is_valid_operator_strips as_strips (as_strips_op ac)"
    using wf_as_strips_op ndom by blast
  show ?thesis
    unfolding is_valid_problem_strips_def Let_def as_strips_sel
    apply (intro conjI)
    using ops unfolding Ball_set[symmetric] apply simp
    using init_covered apply (meson ListMem_iff)
    using goal_covered by (meson ListMem_iff)
qed

sublocale grounded_normalized_numeric_free_problem \<subseteq> s: valid_strips as_strips
  using wf_as_strips by unfold_locales

subsection \<open> STRIPS task semantics are preserved \<close>

lemma (in grounded_problem)
  "wf_pred n \<longleftrightarrow> PredDecl n [] \<in> set (predicates D)"
  "wf_pred n \<longleftrightarrow> n \<in> pred ` set (predicates D)"
  (* "wf_pred n \<longleftrightarrow> vpos n \<in> pred_vpos ` set (predicates D)" -- pred_vpos is iceboxed/undefined *)
    (* not pos_vars, tho, because n could be '''' and vpos n = v\<^sub>T *)
  oops

context ast_classical_problem begin
(* strips state equivalent *)

term empty_state
definition strips_model :: "world_model \<Rightarrow> name strips_state" where
  "strips_model M v \<equiv> undefined"

thm wf_ast_classical_domain.wf_empty_atom (* use this to work with wf_world_model M *)
lemma strips_model_props:
  assumes "wf_world_model M"
    "wf_pred n"
  shows
    "strips_init = strips_model I"
    "strips_model M v\<^sub>T = Some True"
    "strips_model M v\<^sub>F = Some False"
    "strips_model M v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars"
    "strips_model M (vpos n) = Some (Atom (predAtm n []) \<in> fst M)"
    "strips_model M (vneg n) = Some (Atom (predAtm n []) \<notin> fst M)"
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
  shows "Atom (predAtm n []) \<in> fst (pddl_model s) \<longleftrightarrow> s (vpos n) = Some True"
  oops


fun (in ast_classical_domain) strips_pa where
  "strips_pa (SimplePlanAction n args) = as_strips_op (the (resolve_classical_action_schema n))"



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


end text \<open> context ast_classical_problem \<close>
end  