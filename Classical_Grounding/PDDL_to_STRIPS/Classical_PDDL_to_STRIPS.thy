 theory Classical_PDDL_to_STRIPS
  imports "Classical_Planning.Classical_Abstract_Syntax"
    "Classical_Planning.Classical_Happening_Semantics"
    Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement
    STRIPS_Sema_Supplement
    "Verified_SAT_Based_AI_Planning.STRIPS_Semantics"
    Grounding_Classical_Common.Classical_PDDL_Normalization
    Grounding_Classical_Common.Numeric_Free
    (* list linorder: *) "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"  (* only used to minimize negative literals *)
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

fun (in ast_classical_domain) strips_pa where
  "strips_pa (SimplePlanAction n args) = as_strips_op (the (resolve_classical_action_schema n))"

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
definition "empty_state \<equiv> (fold (\<lambda>v s. s(v \<mapsto> True)) neg_vars pos_empty)(v\<^sub>T \<mapsto> True, v\<^sub>F \<mapsto> False)"
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
  propositional-fragment restriction (see \<^theory>\<open>Grounding_Classical_Common.Numeric_Free\<close>); it
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
  have step: "fold (\<lambda>v s. s(v \<mapsto> b)) vars s v \<noteq> None \<longleftrightarrow> v \<in> set vars \<or> s v \<noteq> None"
    for b vars s by (induction vars arbitrary: s) simp_all
  have "empty_state v \<noteq> None \<longleftrightarrow> v \<in> set neg_vars \<or> v \<in> set pos_vars"
    unfolding empty_state_def
    using step[of True neg_vars pos_empty] step[of False pos_vars "\<lambda>x. None"]
    by (auto simp: pos_vars_def neg_vars_def)
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

text \<open>Injectivity / disjointness of the STRIPS variable encoding. \<^const>\<open>vpos\<close>/\<^const>\<open>vneg\<close>
  prepend a fixed character to the predicate name, so they are injective and disjoint from each
  other; they coincide with the static markers \<^const>\<open>v\<^sub>T\<close>/\<^const>\<open>v\<^sub>F\<close> only for the empty predicate
  name, which the encodable-problem locale rules out.\<close>

lemma (in -) name_empty_iff: "(s = STR '''') \<longleftrightarrow> literal.explode s = []"
  by (metis String.implode_explode_eq zero_literal.rep_eq)

lemma (in -) lit_append_empty_right: "s + STR '''' = s" for s :: name
  by (metis append_Nil2 String.implode_explode_eq plus_literal.rep_eq zero_literal.rep_eq)

lemma vpos_inj: "(vpos p = vpos q) \<longleftrightarrow> (p = q)"
  by (metis lit_prepend_inj predicate.expand)

lemma vneg_inj: "(vneg p = vneg q) \<longleftrightarrow> (p = q)"
  by (metis lit_prepend_inj predicate.expand)

lemma vpos_eq_vT: "(vpos p = v\<^sub>T) \<longleftrightarrow> (predicate.name p = STR '''')"
  unfolding v\<^sub>T_def by (metis lit_append_empty_right lit_prepend_inj)

lemma vneg_eq_vF: "(vneg p = v\<^sub>F) \<longleftrightarrow> (predicate.name p = STR '''')"
  unfolding v\<^sub>F_def by (metis lit_append_empty_right lit_prepend_inj)

lemma vpos_neq_vF: "vpos p \<noteq> v\<^sub>F"
proof
  assume "vpos p = v\<^sub>F"
  hence "literal.explode (STR ''+'' + predicate.name p) = literal.explode (STR ''-'' :: name)"
    by (simp add: v\<^sub>F_def)
  moreover have "literal.explode (STR ''+'' :: name) = ''+''"
                "literal.explode (STR ''-'' :: name) = ''-''" by eval+
  ultimately show False by (simp add: plus_literal.rep_eq)
qed

lemma vneg_neq_vT: "vneg p \<noteq> v\<^sub>T"
proof
  assume "vneg p = v\<^sub>T"
  hence "literal.explode (STR ''-'' + predicate.name p) = literal.explode (STR ''+'' :: name)"
    by (simp add: v\<^sub>T_def)
  moreover have "literal.explode (STR ''-'' :: name) = ''-''"
                "literal.explode (STR ''+'' :: name) = ''+''" by eval+
  ultimately show False by (simp add: plus_literal.rep_eq)
qed

lemma vT_neq_vF: "v\<^sub>T \<noteq> v\<^sub>F"
  unfolding vb_defs by eval

context ast_classical_problem begin
(* strips state equivalent *)

text \<open>The STRIPS state induced by a PDDL world model: the static markers are fixed, a positive
  variable \<^term>\<open>vpos p\<close> records whether the (nullary) atom for \<open>p\<close> holds in \<open>M\<close>, and the negative
  variable \<^term>\<open>vneg p\<close> records its complement. Defined only on \<^const>\<open>strips_vars\<close>.\<close>
definition strips_model :: "world_model \<Rightarrow> name strips_state" where
  "strips_model M v \<equiv>
    (if v \<in> set strips_vars
     then Some (v = v\<^sub>T
              \<or> (\<exists>p. wf_pred p \<and> v = vpos p \<and> Atom (predAtm p []) \<in> fst M)
              \<or> (\<exists>p. wf_pred p \<and> v = vneg p \<and> Atom (predAtm p []) \<notin> fst M))
     else None)"

lemma strips_model_None_iff: "strips_model M v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars"
  unfolding strips_model_def by simp

lemma strips_model_vT [simp]: "strips_model M v\<^sub>T = Some True"
  unfolding strips_model_def vars_defs by simp

lemma vpos_mem: "wf_pred n \<Longrightarrow> vpos n \<in> set pos_vars"
  unfolding vars_defs wf_pred_def by (force simp: image_iff)

lemma vneg_mem: "wf_pred n \<Longrightarrow> vneg n \<in> set neg_vars"
  unfolding vars_defs wf_pred_def by (force simp: image_iff)

text \<open>Folding a constant-valued update over a variable list: the result is \<open>Some b\<close> exactly on
  the listed variables.\<close>
lemma fold_upd_const_mem:
  "fold (\<lambda>v s. s(v \<mapsto> b)) vars s w = (if w \<in> set vars then Some b else s w)"
  by (induction vars arbitrary: s) auto

lemma empty_state_vT: "empty_state v\<^sub>T = Some True"
  unfolding empty_state_def by (simp add: vb_defs)

lemma empty_state_vF: "empty_state v\<^sub>F = Some False"
  unfolding empty_state_def by simp

lemma empty_state_None:
  assumes "v \<notin> set strips_vars" shows "empty_state v = None"
proof -
  from assms have "v \<noteq> v\<^sub>T" "v \<noteq> v\<^sub>F" "v \<notin> set neg_vars" "v \<notin> set pos_vars"
    unfolding vars_defs by auto
  thus ?thesis unfolding empty_state_def by (simp add: fold_upd_const_mem)
qed

text \<open>\<^const>\<open>upd_init\<close> only ever writes \<open>Some True\<close> to positive variables (resp. \<open>Some False\<close> to
  negative ones), so the folded init state's value at a positive/negative variable is determined by
  whether \<^emph>\<open>any\<close> init atom targets it.\<close>
lemma fold_upd_init_pos:
  assumes "\<forall>a\<in>set xs. is_predAtom a"
  shows "fold upd_init xs s (vpos n)
       = (if (\<exists>a\<in>set xs. atm_as_vpos a = vpos n) then Some True else s (vpos n))"
  using assms
proof (induction xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  from Cons.prems have "is_predAtom x" by simp
  then obtain p args where x: "x = Atom (predAtm p args)"
    by (cases x rule: is_predAtom.cases) auto
  have vn: "atm_as_vneg x = vneg p" using x by simp
  have ne: "atm_as_vneg x \<noteq> vpos n" using vn vneg_neq_vpos by metis
  have IH: "fold upd_init xs (upd_init x s) (vpos n)
          = (if (\<exists>a\<in>set xs. atm_as_vpos a = vpos n) then Some True else upd_init x s (vpos n))"
    using Cons.IH Cons.prems by simp
  show ?case
  proof (cases "atm_as_vpos x = vpos n")
    case True
    hence "upd_init x s (vpos n) = Some True" unfolding upd_init_def using ne by simp
    thus ?thesis using True IH by simp
  next
    case False
    hence "upd_init x s (vpos n) = s (vpos n)" unfolding upd_init_def using ne by simp
    thus ?thesis using False IH by simp
  qed
qed

lemma fold_upd_init_neg:
  assumes "\<forall>a\<in>set xs. is_predAtom a"
  shows "fold upd_init xs s (vneg n)
       = (if (\<exists>a\<in>set xs. atm_as_vneg a = vneg n) then Some False else s (vneg n))"
  using assms
proof (induction xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  from Cons.prems have "is_predAtom x" by simp
  then obtain p args where x: "x = Atom (predAtm p args)"
    by (cases x rule: is_predAtom.cases) auto
  have vp: "atm_as_vpos x = vpos p" using x by simp
  have ne: "atm_as_vpos x \<noteq> vneg n" using vp vneg_neq_vpos by metis
  have IH: "fold upd_init xs (upd_init x s) (vneg n)
          = (if (\<exists>a\<in>set xs. atm_as_vneg a = vneg n) then Some False else upd_init x s (vneg n))"
    using Cons.IH Cons.prems by simp
  show ?case
  proof (cases "atm_as_vneg x = vneg n")
    case True
    hence "upd_init x s (vneg n) = Some False" unfolding upd_init_def by simp
    thus ?thesis using True IH by simp
  next
    case False
    hence "upd_init x s (vneg n) = s (vneg n)" unfolding upd_init_def using ne by simp
    thus ?thesis using False IH by simp
  qed
qed

lemma fold_upd_init_untouched:
  assumes "\<forall>a\<in>set xs. atm_as_vpos a \<noteq> v \<and> atm_as_vneg a \<noteq> v"
  shows "fold upd_init xs s v = s v"
  using assms by (induction xs arbitrary: s) (auto simp: upd_init_def)

text \<open>Concrete (executable) restoration of a STRIPS serial solution into a PDDL plan: restore the
  \<^emph>\<open>applicable prefix\<close> only. Mirrors the case split of \<^const>\<open>execute_serial_plan\<close> — restore the
  decoded plan action while the operator is applicable in the induced STRIPS state, and stop at the
  first non-applicable operator (the suffix is irrelevant: the goal is already reached). This is the
  function whose existence \<open>sim_serial_rev\<close> asserts; \<^const>\<open>restore_pddl_pa\<close> is the canonical
  decoder of a single operator.\<close>
fun restore_prefix
  :: "world_model \<Rightarrow> name strips_operator list \<Rightarrow> ast_classical_plan_action list"
  where
    "restore_prefix M [] = []"
  | "restore_prefix M (opr # ops) =
       (if is_operator_applicable_in (strips_model M) opr
        then restore_pddl_pa opr
               # restore_prefix (execute_plan_action (restore_pddl_pa opr) M) ops
        else [])"

end text \<open>context ast_classical_problem\<close>

text \<open>Two generic bridges used by the semantics-preservation proof: \<^const>\<open>un_and\<close> commutes with
  formula instantiation, and (for a conjunction) the map-valuation of a formula reduces to the
  map-valuation of each of its conjuncts.\<close>
lemma (in -) un_and_map_formula:
  "un_and (map_formula h F) = map (map_formula h) (un_and F)"
  by (induction F) auto

lemma (in -) map_sem_un_and:
  assumes "is_conj F"
  shows "(\<A> \<Turnstile>\<^sub>m F) \<longleftrightarrow> (\<forall>l \<in> set (un_and F). \<A> \<Turnstile>\<^sub>m l)"
  using assms by (induction F rule: conj_induct) auto

text \<open>Folding the goal-assignment list \<^const>\<open>upd_goal\<close>: any non-\<open>None\<close> result either comes from a
  list entry or was already present, the domain is monotone, and a list entry forces membership.\<close>
lemma (in -) fold_upd_goal_Some:
  "fold upd_goal kvs s v = Some b \<Longrightarrow> (v, b) \<in> set kvs \<or> s v = Some b"
proof (induction kvs arbitrary: s)
  case (Cons kv kvs)
  obtain v' b' where kv: "kv = (v', b')" by (cases kv)
  from Cons.prems have "fold upd_goal kvs (s(v' \<mapsto> b')) v = Some b" using kv by simp
  from Cons.IH[OF this] have "(v, b) \<in> set kvs \<or> (s(v' \<mapsto> b')) v = Some b" .
  thus ?case using kv by (auto split: if_split_asm)
qed simp

lemma (in -) fold_upd_goal_dom_mono:
  "s v \<noteq> None \<Longrightarrow> fold upd_goal kvs s v \<noteq> None"
proof (induction kvs arbitrary: s)
  case (Cons kv kvs)
  obtain v' b' where kv: "kv = (v', b')" by (cases kv)
  have "(upd_goal kv s) v \<noteq> None" using Cons.prems kv by auto
  thus ?case using Cons.IH by simp
qed simp

lemma (in -) fold_upd_goal_mem_dom:
  "(v, b) \<in> set kvs \<Longrightarrow> fold upd_goal kvs s v \<noteq> None"
proof (induction kvs arbitrary: s)
  case (Cons kv kvs)
  show ?case
  proof (cases "(v, b) \<in> set kvs")
    case True thus ?thesis using Cons.IH by simp
  next
    case False
    with Cons.prems have kv: "kv = (v, b)" by (cases kv) auto
    have "(upd_goal kv s) v \<noteq> None" using kv by simp
    thus ?thesis using fold_upd_goal_dom_mono by simp
  qed
qed simp

text \<open>A nullary atom is fixed by any term substitution (it has no arguments to rewrite).\<close>
lemma (in -) map_atom_fmla_nullary:
  "map_atom_fmla \<sigma> (Atom (predAtm m [])) = Atom (predAtm m [])"
  by simp

text \<open>Selectors of an instantiated classical action schema: instantiation applies the
  parameter substitution \<^const>\<open>tsubst\<close> pointwise to the precondition formula and to the
  add/delete effect lists.\<close>
lemma (in -) inst_precondition:
  "precondition (instantiate_classical_action_schema ac args)
   = map_atom_fmla (tsubst (ac_head ac) args) (ac_pre ac)"
  by (cases ac rule: ast_classical_action_schema_cases_unfold) simp

lemma (in -) inst_effect_sel:
  "adds (effect (instantiate_classical_action_schema ac args))
   = map (map_atom_fmla (tsubst (ac_head ac) args)) (adds (ac_eff ac))"
  "dels (effect (instantiate_classical_action_schema ac args))
   = map (map_atom_fmla (tsubst (ac_head ac) args)) (dels (ac_eff ac))"
  by (cases ac rule: ast_classical_action_schema_cases_unfold,
      rename_tac n params pre eff, case_tac eff, simp)+

text \<open>A problem whose (grounded, normalized, numeric-free) shape additionally has no
  empty-named predicate, so the positive/negative STRIPS variables never collide with the static
  truth markers. The emptiness exclusion is discharged from the grounder's construction (predicate
  names are nonempty decimal strings); see the \<open>grounder\<close> locale in \<open>Classical_Grounded_PDDL\<close>.\<close>
locale strips_encodable_problem =
  grounded_normalized_numeric_free_problem +
  assumes nonempty_pred_names: "\<And>p. wf_pred p \<Longrightarrow> predicate.name p \<noteq> STR ''''"
  \<comment> \<open>The goal carries no conflicting literals (same STRIPS variable, opposite polarity). Trivially
    discharged whenever the goal is a single atom, as produced by goal normalization
    (\<open>degoal_prob\<close> yields \<open>goal P3 = Atom (predAtm goal_pred [])\<close>).\<close>
  and goal_no_conflict:
    "\<And>l1 l2. l1 \<in> set (un_and (goal P)) \<Longrightarrow> l2 \<in> set (un_and (goal P))
       \<Longrightarrow> fst (lit_as_goal l1) = fst (lit_as_goal l2) \<Longrightarrow> snd (lit_as_goal l1) = snd (lit_as_goal l2)"
begin

lemma vpos_neq_vT: "wf_pred p \<Longrightarrow> vpos p \<noteq> v\<^sub>T"
  using nonempty_pred_names vpos_eq_vT by blast

lemma vneg_neq_vF: "wf_pred p \<Longrightarrow> vneg p \<noteq> v\<^sub>F"
  using nonempty_pred_names vneg_eq_vF by blast

lemma strips_model_vF [simp]: "strips_model M v\<^sub>F = Some False"
proof -
  have mem: "v\<^sub>F \<in> set strips_vars" unfolding vars_defs by simp
  have "\<not> (v\<^sub>F = v\<^sub>T \<or> (\<exists>p. wf_pred p \<and> v\<^sub>F = vpos p \<and> Atom (predAtm p []) \<in> fst M)
              \<or> (\<exists>p. wf_pred p \<and> v\<^sub>F = vneg p \<and> Atom (predAtm p []) \<notin> fst M))"
    using vT_neq_vF vpos_neq_vF vneg_neq_vF by (metis)
  thus ?thesis unfolding strips_model_def using mem by simp
qed

lemma strips_model_vpos:
  assumes "wf_pred n"
  shows "strips_model M (vpos n) = Some (Atom (predAtm n []) \<in> fst M)"
proof -
  have mem: "vpos n \<in> set strips_vars" using vpos_mem[OF assms] by auto
  have "(vpos n = v\<^sub>T \<or> (\<exists>p. wf_pred p \<and> vpos n = vpos p \<and> Atom (predAtm p []) \<in> fst M)
              \<or> (\<exists>p. wf_pred p \<and> vpos n = vneg p \<and> Atom (predAtm p []) \<notin> fst M))
        \<longleftrightarrow> Atom (predAtm n []) \<in> fst M"
  proof
    assume "vpos n = v\<^sub>T \<or> (\<exists>p. wf_pred p \<and> vpos n = vpos p \<and> Atom (predAtm p []) \<in> fst M)
              \<or> (\<exists>p. wf_pred p \<and> vpos n = vneg p \<and> Atom (predAtm p []) \<notin> fst M)"
    hence "\<exists>p. vpos n = vpos p \<and> Atom (predAtm p []) \<in> fst M"
      using vpos_neq_vT[OF assms] vneg_neq_vpos[THEN not_sym] by blast
    thus "Atom (predAtm n []) \<in> fst M" using vpos_inj by auto
  next
    assume "Atom (predAtm n []) \<in> fst M"
    thus "vpos n = v\<^sub>T \<or> (\<exists>p. wf_pred p \<and> vpos n = vpos p \<and> Atom (predAtm p []) \<in> fst M)
              \<or> (\<exists>p. wf_pred p \<and> vpos n = vneg p \<and> Atom (predAtm p []) \<notin> fst M)"
      using assms by blast
  qed
  thus ?thesis unfolding strips_model_def using mem by simp
qed

lemma strips_model_vneg:
  assumes "wf_pred n"
  shows "strips_model M (vneg n) = Some (Atom (predAtm n []) \<notin> fst M)"
proof -
  have mem: "vneg n \<in> set strips_vars" using vneg_mem[OF assms] by auto
  have "(vneg n = v\<^sub>T \<or> (\<exists>p. wf_pred p \<and> vneg n = vpos p \<and> Atom (predAtm p []) \<in> fst M)
              \<or> (\<exists>p. wf_pred p \<and> vneg n = vneg p \<and> Atom (predAtm p []) \<notin> fst M))
        \<longleftrightarrow> Atom (predAtm n []) \<notin> fst M"
  proof
    assume "vneg n = v\<^sub>T \<or> (\<exists>p. wf_pred p \<and> vneg n = vpos p \<and> Atom (predAtm p []) \<in> fst M)
              \<or> (\<exists>p. wf_pred p \<and> vneg n = vneg p \<and> Atom (predAtm p []) \<notin> fst M)"
    hence "\<exists>p. vneg n = vneg p \<and> Atom (predAtm p []) \<notin> fst M"
      using vneg_neq_vT vneg_neq_vpos by blast
    thus "Atom (predAtm n []) \<notin> fst M" using vneg_inj by auto
  next
    assume "Atom (predAtm n []) \<notin> fst M"
    thus "vneg n = v\<^sub>T \<or> (\<exists>p. wf_pred p \<and> vneg n = vpos p \<and> Atom (predAtm p []) \<in> fst M)
              \<or> (\<exists>p. wf_pred p \<and> vneg n = vneg p \<and> Atom (predAtm p []) \<notin> fst M)"
      using assms by blast
  qed
  thus ?thesis unfolding strips_model_def using mem by simp
qed

lemma wf_pred_pred:
  assumes "pd \<in> set (predicates D)" shows "wf_pred (pred pd)"
proof -
  from assms grounded_dom have "grounded_pred pd" unfolding grounded_dom_def by blast
  hence "PredDecl (pred pd) [] = pd" by (cases pd) auto
  thus ?thesis using assms unfolding wf_pred_def by simp
qed

lemma strips_var_cases:
  assumes "v \<in> set strips_vars"
  obtains (T) "v = v\<^sub>T" | (F) "v = v\<^sub>F"
    | (pos) n where "wf_pred n" "v = vpos n"
    | (neg) n where "wf_pred n" "v = vneg n"
proof -
  from assms have "v \<in> set pos_vars \<or> v \<in> set neg_vars" by auto
  then show thesis
  proof
    assume "v \<in> set pos_vars"
    then consider "v = v\<^sub>T" | pd where "pd \<in> set (predicates D)" "v = vpos (pred pd)"
      unfolding pos_vars_def by auto
    then show thesis using that wf_pred_pred by metis
  next
    assume "v \<in> set neg_vars"
    then consider "v = v\<^sub>F" | pd where "pd \<in> set (predicates D)" "v = vneg (pred pd)"
      unfolding neg_vars_def by auto
    then show thesis using that wf_pred_pred by metis
  qed
qed

lemma empty_state_vpos:
  assumes "wf_pred n" shows "empty_state (vpos n) = Some False"
proof -
  have "vpos n \<noteq> v\<^sub>T" using vpos_neq_vT[OF assms] .
  moreover have "vpos n \<noteq> v\<^sub>F" using vpos_neq_vF .
  moreover have "vpos n \<notin> set neg_vars"
  proof
    assume "vpos n \<in> set neg_vars"
    then consider "vpos n = v\<^sub>F" | x where "x \<in> set (predicates D)" "vpos n = vneg (pred x)"
      unfolding neg_vars_def by auto
    thus False using vpos_neq_vF vneg_neq_vpos by metis
  qed
  moreover have "vpos n \<in> set pos_vars" using vpos_mem[OF assms] .
  ultimately show ?thesis unfolding empty_state_def by (simp add: fold_upd_const_mem)
qed

lemma empty_state_vneg:
  assumes "wf_pred n" shows "empty_state (vneg n) = Some True"
proof -
  have "vneg n \<noteq> v\<^sub>T" using vneg_neq_vT .
  moreover have "vneg n \<noteq> v\<^sub>F" using vneg_neq_vF[OF assms] .
  moreover have "vneg n \<in> set neg_vars" using vneg_mem[OF assms] .
  ultimately show ?thesis unfolding empty_state_def by (simp add: fold_upd_const_mem)
qed

lemma init_atoms_wf:
  assumes "a \<in> set (init P)" shows "\<exists>m. a = Atom (predAtm m []) \<and> wf_pred m"
proof -
  have inf: "\<forall>f\<in>set (init P). num_free_fmla f"
    using num_free_prob unfolding num_free_prob_def by blast
  from assms wf_init_lits[OF inf] have wfa: "wf_lit_atom a" by blast
  hence pa: "is_predAtom a" and wl: "wf_lit a" by auto
  from pa obtain m args where am: "a = Atom (predAtm m args)"
    by (cases a rule: is_predAtom.cases) auto
  from wl am have "args = [] \<and> wf_pred m" by (cases args) auto
  thus ?thesis using am by auto
qed

lemma init_predAtoms: "\<forall>a\<in>set (init P). is_predAtom a"
  using init_atoms_wf by fastforce

lemma init_pos_iff:
  assumes "wf_pred n"
  shows "(\<exists>a\<in>set (init P). atm_as_vpos a = vpos n) \<longleftrightarrow> Atom (predAtm n []) \<in> fst I"
proof
  assume "\<exists>a\<in>set (init P). atm_as_vpos a = vpos n"
  then obtain a where a: "a \<in> set (init P)" "atm_as_vpos a = vpos n" by blast
  from a(1) obtain m where am: "a = Atom (predAtm m [])" "wf_pred m" using init_atoms_wf by blast
  from a(2) am have "vpos m = vpos n" by simp
  hence "m = n" using vpos_inj by simp
  with am a(1) show "Atom (predAtm n []) \<in> fst I" unfolding I_def by simp
next
  assume "Atom (predAtm n []) \<in> fst I"
  hence "Atom (predAtm n []) \<in> set (init P)" unfolding I_def by simp
  moreover have "atm_as_vpos (Atom (predAtm n [])) = vpos n" by simp
  ultimately show "\<exists>a\<in>set (init P). atm_as_vpos a = vpos n" by blast
qed

lemma init_neg_iff:
  assumes "wf_pred n"
  shows "(\<exists>a\<in>set (init P). atm_as_vneg a = vneg n) \<longleftrightarrow> Atom (predAtm n []) \<in> fst I"
proof
  assume "\<exists>a\<in>set (init P). atm_as_vneg a = vneg n"
  then obtain a where a: "a \<in> set (init P)" "atm_as_vneg a = vneg n" by blast
  from a(1) obtain m where am: "a = Atom (predAtm m [])" "wf_pred m" using init_atoms_wf by blast
  from a(2) am have "vneg m = vneg n" by simp
  hence "m = n" using vneg_inj by simp
  with am a(1) show "Atom (predAtm n []) \<in> fst I" unfolding I_def by simp
next
  assume "Atom (predAtm n []) \<in> fst I"
  hence "Atom (predAtm n []) \<in> set (init P)" unfolding I_def by simp
  moreover have "atm_as_vneg (Atom (predAtm n [])) = vneg n" by simp
  ultimately show "\<exists>a\<in>set (init P). atm_as_vneg a = vneg n" by blast
qed

lemma strips_init_vT: "strips_init v\<^sub>T = Some True"
proof -
  have "\<forall>a\<in>set (init P). atm_as_vpos a \<noteq> v\<^sub>T \<and> atm_as_vneg a \<noteq> v\<^sub>T"
  proof
    fix a assume "a \<in> set (init P)"
    then obtain m where am: "a = Atom (predAtm m [])" "wf_pred m" using init_atoms_wf by blast
    show "atm_as_vpos a \<noteq> v\<^sub>T \<and> atm_as_vneg a \<noteq> v\<^sub>T"
      using am vpos_neq_vT[OF am(2)] vneg_neq_vT by simp
  qed
  hence "strips_init v\<^sub>T = empty_state v\<^sub>T"
    unfolding strips_init_def using fold_upd_init_untouched by blast
  thus ?thesis using empty_state_vT by simp
qed

lemma strips_init_vF: "strips_init v\<^sub>F = Some False"
proof -
  have "\<forall>a\<in>set (init P). atm_as_vpos a \<noteq> v\<^sub>F \<and> atm_as_vneg a \<noteq> v\<^sub>F"
  proof
    fix a assume "a \<in> set (init P)"
    then obtain m where am: "a = Atom (predAtm m [])" "wf_pred m" using init_atoms_wf by blast
    show "atm_as_vpos a \<noteq> v\<^sub>F \<and> atm_as_vneg a \<noteq> v\<^sub>F"
      using am vpos_neq_vF vneg_neq_vF[OF am(2)] by simp
  qed
  hence "strips_init v\<^sub>F = empty_state v\<^sub>F"
    unfolding strips_init_def using fold_upd_init_untouched by blast
  thus ?thesis using empty_state_vF by simp
qed

lemma strips_init_vpos:
  assumes "wf_pred n" shows "strips_init (vpos n) = Some (Atom (predAtm n []) \<in> fst I)"
proof -
  have "strips_init (vpos n)
      = (if (\<exists>a\<in>set (init P). atm_as_vpos a = vpos n) then Some True else empty_state (vpos n))"
    unfolding strips_init_def using fold_upd_init_pos[OF init_predAtoms] .
  also have "... = (if Atom (predAtm n []) \<in> fst I then Some True else Some False)"
    using init_pos_iff[OF assms] empty_state_vpos[OF assms] by simp
  finally show ?thesis by simp
qed

lemma strips_init_vneg:
  assumes "wf_pred n" shows "strips_init (vneg n) = Some (Atom (predAtm n []) \<notin> fst I)"
proof -
  have "strips_init (vneg n)
      = (if (\<exists>a\<in>set (init P). atm_as_vneg a = vneg n) then Some False else empty_state (vneg n))"
    unfolding strips_init_def using fold_upd_init_neg[OF init_predAtoms] .
  also have "... = (if Atom (predAtm n []) \<in> fst I then Some False else Some True)"
    using init_neg_iff[OF assms] empty_state_vneg[OF assms] by simp
  finally show ?thesis by simp
qed

lemma strips_init_None:
  assumes "v \<notin> set strips_vars" shows "strips_init v = None"
proof -
  have "\<forall>a\<in>set (init P). atm_as_vpos a \<noteq> v \<and> atm_as_vneg a \<noteq> v"
  proof
    fix a assume "a \<in> set (init P)"
    then obtain m where am: "a = Atom (predAtm m [])" "wf_pred m" using init_atoms_wf by blast
    have "vpos m \<in> set strips_vars" "vneg m \<in> set strips_vars"
      using vpos_mem[OF am(2)] vneg_mem[OF am(2)] by auto
    thus "atm_as_vpos a \<noteq> v \<and> atm_as_vneg a \<noteq> v" using assms am by auto
  qed
  hence "strips_init v = empty_state v"
    unfolding strips_init_def using fold_upd_init_untouched by blast
  thus ?thesis using empty_state_None[OF assms] by simp
qed

lemma strips_init_eq_model: "strips_init = strips_model I"
proof (rule ext)
  fix v
  show "strips_init v = strips_model I v"
  proof (cases "v \<in> set strips_vars")
    case True
    from True show ?thesis
    proof (cases rule: strips_var_cases)
      case T then show ?thesis using strips_init_vT by simp
    next
      case F then show ?thesis using strips_init_vF by simp
    next
      case (pos m) then show ?thesis
        using strips_init_vpos[OF pos(1)] strips_model_vpos[OF pos(1)] by simp
    next
      case (neg m) then show ?thesis
        using strips_init_vneg[OF neg(1)] strips_model_vneg[OF neg(1)] by simp
    qed
  next
    case False
    have "strips_init v = None" using strips_init_None False by blast
    moreover have "strips_model I v = None" using False unfolding strips_model_def by simp
    ultimately show ?thesis by simp
  qed
qed

subsection \<open> Plan-action simulation \<close>

text \<open>A well-formed (numeric-free, grounded) literal is satisfied by \<^term>\<open>valuation M\<close> (after any
  instantiating substitution \<open>\<sigma>\<close>, which is the identity on nullary atoms) iff its encoding STRIPS
  variable holds in \<^term>\<open>strips_model M\<close>.\<close>
lemma strips_model_lit_inst:
  assumes "wf_lit l"
  shows "(valuation M \<Turnstile>\<^sub>m map_atom_fmla \<sigma> l) \<longleftrightarrow> strips_model M (lit_as_var l) = Some True"
proof (cases l rule: wf_lit.cases)
  case 1 thus ?thesis by simp
next
  case 2 thus ?thesis by simp
next
  case (3 n)
  hence "wf_pred n" using assms by simp
  thus ?thesis using 3 by (simp add: valuation_def strips_model_vpos)
next
  case (4 n)
  hence wf: "wf_pred n" using assms by simp
  have dom: "predAtm n [] \<in> dom (valuation M)" by (simp add: valuation_def domIff)
  show ?thesis using 4 wf dom by (simp add: valuation_def strips_model_vneg)
qed (use assms in simp_all)

text \<open>The map-valuation of a (grounded, instantiated) precondition coincides with STRIPS operator
  applicability in the induced state.\<close>
lemma pre_applicable_iff:
  assumes "ac \<in> set (actions D)"
  shows "(valuation M \<Turnstile>\<^sub>m map_atom_fmla \<sigma> (ac_pre ac))
       \<longleftrightarrow> is_operator_applicable_in (strips_model M) (as_strips_op ac)"
proof -
  have conj: "is_conj (ac_pre ac)"
    using assms normed_prob unfolding prec_normed_dom_def by blast
  have nf: "num_free_ac ac"
    using assms num_free_prob unfolding num_free_prob_def num_free_dom_def by blast
  have wfl: "\<forall>l \<in> set (un_and (ac_pre ac)). wf_lit l" using wf_pre_lits[OF assms nf] .
  have "is_conj (map_atom_fmla \<sigma> (ac_pre ac))"
    using map_preserves_isconj[OF conj] by (simp add: comp_def)
  hence "(valuation M \<Turnstile>\<^sub>m map_atom_fmla \<sigma> (ac_pre ac))
      \<longleftrightarrow> (\<forall>l' \<in> set (un_and (map_atom_fmla \<sigma> (ac_pre ac))). valuation M \<Turnstile>\<^sub>m l')"
    by (rule map_sem_un_and)
  also have "... \<longleftrightarrow> (\<forall>l \<in> set (un_and (ac_pre ac)). valuation M \<Turnstile>\<^sub>m map_atom_fmla \<sigma> l)"
    by (simp add: un_and_map_formula)
  also have "... \<longleftrightarrow> (\<forall>l \<in> set (un_and (ac_pre ac)). strips_model M (lit_as_var l) = Some True)"
    using wfl strips_model_lit_inst by metis
  also have "... \<longleftrightarrow> is_operator_applicable_in (strips_model M) (as_strips_op ac)"
    unfolding is_operator_applicable_in_def as_strips_op_sel fmla_as_vars_def
    by (simp add: list_all_iff)
  finally show ?thesis .
qed

text \<open>A well-formed plan action is enabled (its instantiated precondition holds) iff the
  corresponding STRIPS operator is applicable in the induced state.\<close>
lemma enabled_applicable:
  assumes "wf_classical_plan_action a"
  shows "(valuation M \<Turnstile>\<^sub>m precondition (the (res_inst a)))
       \<longleftrightarrow> is_operator_applicable_in (strips_model M) (strips_pa a)"
proof -
  obtain n args where aeq: "a = SimplePlanAction n args" by (cases a)
  with assms have args: "args = []" using grounded_pa_nullary by simp
  from assms aeq args obtain ac where
    res: "resolve_classical_action_schema n = Some ac" and mem: "ac \<in> set (actions D)"
    using wf_pa_refs_ac by metis
  have "the (res_inst a) = instantiate_classical_action_schema ac []"
    using aeq args res by simp
  hence pre: "precondition (the (res_inst a)) = map_atom_fmla (tsubst (ac_head ac) []) (ac_pre ac)"
    by (simp add: inst_precondition)
  have op: "strips_pa a = as_strips_op ac" using aeq args res by simp
  show ?thesis unfolding pre op by (rule pre_applicable_iff[OF mem])
qed

text \<open>A well-formed (numeric-free) effect-atom is a nullary predicate atom.\<close>
lemma wf_lit_atom_nullary:
  assumes "wf_lit_atom x" shows "\<exists>m. x = Atom (predAtm m []) \<and> wf_pred m"
proof -
  from assms have pa: "is_predAtom x" and wl: "wf_lit x" by auto
  from pa obtain m args where am: "x = Atom (predAtm m args)"
    by (cases x rule: is_predAtom.cases) auto
  from wl am have "args = [] \<and> wf_pred m" by (cases args) auto
  thus ?thesis using am by auto
qed

text \<open>Translating STRIPS-variable membership in an encoded (nullary) atom list back to atom
  membership, using injectivity/disjointness of \<^const>\<open>vpos\<close>/\<^const>\<open>vneg\<close>.\<close>
lemma atm_vpos_image_iff:
  assumes "\<And>x. x \<in> set es \<Longrightarrow> \<exists>k. x = Atom (predAtm k []) \<and> wf_pred k"
  shows "(vpos m \<in> atm_as_vpos ` set es) \<longleftrightarrow> Atom (predAtm m []) \<in> set es"
proof
  assume "vpos m \<in> atm_as_vpos ` set es"
  then obtain x where x: "x \<in> set es" "atm_as_vpos x = vpos m" by auto
  from assms[OF x(1)] obtain k where xk: "x = Atom (predAtm k [])" by blast
  with x(2) have "vpos k = vpos m" by simp
  hence "k = m" using vpos_inj by simp
  thus "Atom (predAtm m []) \<in> set es" using xk x(1) by simp
next
  assume "Atom (predAtm m []) \<in> set es"
  thus "vpos m \<in> atm_as_vpos ` set es" by (force simp: image_iff)
qed

lemma atm_vneg_image_iff:
  assumes "\<And>x. x \<in> set es \<Longrightarrow> \<exists>k. x = Atom (predAtm k []) \<and> wf_pred k"
  shows "(vneg m \<in> atm_as_vneg ` set es) \<longleftrightarrow> Atom (predAtm m []) \<in> set es"
proof
  assume "vneg m \<in> atm_as_vneg ` set es"
  then obtain x where x: "x \<in> set es" "atm_as_vneg x = vneg m" by auto
  from assms[OF x(1)] obtain k where xk: "x = Atom (predAtm k [])" by blast
  with x(2) have "vneg k = vneg m" by simp
  hence "k = m" using vneg_inj by simp
  thus "Atom (predAtm m []) \<in> set es" using xk x(1) by simp
next
  assume "Atom (predAtm m []) \<in> set es"
  thus "vneg m \<in> atm_as_vneg ` set es" by (force simp: image_iff)
qed

lemma atm_vpos_notin_vneg_image:
  assumes "\<And>x. x \<in> set es \<Longrightarrow> \<exists>k. x = Atom (predAtm k []) \<and> wf_pred k"
  shows "vpos m \<notin> atm_as_vneg ` set es"
proof
  assume "vpos m \<in> atm_as_vneg ` set es"
  then obtain x where x: "x \<in> set es" "atm_as_vneg x = vpos m" by auto
  from assms[OF x(1)] obtain k where "x = Atom (predAtm k [])" by blast
  with x(2) show False using vneg_neq_vpos by (metis atm_as_vneg.simps)
qed

lemma atm_vneg_notin_vpos_image:
  assumes "\<And>x. x \<in> set es \<Longrightarrow> \<exists>k. x = Atom (predAtm k []) \<and> wf_pred k"
  shows "vneg m \<notin> atm_as_vpos ` set es"
proof
  assume "vneg m \<in> atm_as_vpos ` set es"
  then obtain x where x: "x \<in> set es" "atm_as_vpos x = vneg m" by auto
  from assms[OF x(1)] obtain k where "x = Atom (predAtm k [])" by blast
  with x(2) show False using vneg_neq_vpos by (metis atm_as_vpos.simps)
qed

lemma atm_vT_notin_images:
  assumes "\<And>x. x \<in> set es \<Longrightarrow> \<exists>k. x = Atom (predAtm k []) \<and> wf_pred k"
  shows "v\<^sub>T \<notin> atm_as_vpos ` set es" and "v\<^sub>T \<notin> atm_as_vneg ` set es"
proof -
  show "v\<^sub>T \<notin> atm_as_vpos ` set es"
  proof
    assume "v\<^sub>T \<in> atm_as_vpos ` set es"
    then obtain x where x: "x \<in> set es" "atm_as_vpos x = v\<^sub>T" by auto
    from assms[OF x(1)] obtain k where xk: "x = Atom (predAtm k [])" "wf_pred k" by blast
    with x(2) show False using vpos_neq_vT[OF xk(2)] by simp
  qed
next
  show "v\<^sub>T \<notin> atm_as_vneg ` set es"
  proof
    assume "v\<^sub>T \<in> atm_as_vneg ` set es"
    then obtain x where x: "x \<in> set es" "atm_as_vneg x = v\<^sub>T" by auto
    from assms[OF x(1)] obtain k where "x = Atom (predAtm k [])" by blast
    with x(2) show False using vneg_neq_vT by simp
  qed
qed

lemma atm_vF_notin_images:
  assumes "\<And>x. x \<in> set es \<Longrightarrow> \<exists>k. x = Atom (predAtm k []) \<and> wf_pred k"
  shows "v\<^sub>F \<notin> atm_as_vpos ` set es" and "v\<^sub>F \<notin> atm_as_vneg ` set es"
proof -
  show "v\<^sub>F \<notin> atm_as_vpos ` set es"
  proof
    assume "v\<^sub>F \<in> atm_as_vpos ` set es"
    then obtain x where x: "x \<in> set es" "atm_as_vpos x = v\<^sub>F" by auto
    from assms[OF x(1)] obtain k where "x = Atom (predAtm k [])" by blast
    with x(2) show False using vpos_neq_vF by simp
  qed
next
  show "v\<^sub>F \<notin> atm_as_vneg ` set es"
  proof
    assume "v\<^sub>F \<in> atm_as_vneg ` set es"
    then obtain x where x: "x \<in> set es" "atm_as_vneg x = v\<^sub>F" by auto
    from assms[OF x(1)] obtain k where xk: "x = Atom (predAtm k [])" "wf_pred k" by blast
    with x(2) show False using vneg_neq_vF[OF xk(2)] by simp
  qed
qed

text \<open>Mapping a list of nullary (well-formed) atoms by an instantiating substitution preserves
  membership of a nullary atom: the substitution is the identity on every element (no arguments to
  rewrite), only changing the atom's element type from \<open>term\<close> to \<open>object\<close>.\<close>
lemma inst_eff_list_iff:
  assumes "\<forall>x \<in> set es. wf_lit_atom x"
  shows "(Atom (predAtm p []) \<in> map_atom_fmla \<sigma> ` set es) \<longleftrightarrow> (Atom (predAtm p []) \<in> set es)"
proof
  assume "Atom (predAtm p []) \<in> map_atom_fmla \<sigma> ` set es"
  then obtain x where x: "x \<in> set es" "map_atom_fmla \<sigma> x = Atom (predAtm p [])" by auto
  from assms x(1) obtain m where m: "x = Atom (predAtm m [])" using wf_lit_atom_nullary by metis
  with x(2) have "(Atom (predAtm m []) :: object atom formula) = Atom (predAtm p [])"
    by (simp add: map_atom_fmla_nullary)
  hence "m = p" by simp
  thus "Atom (predAtm p []) \<in> set es" using m x(1) by simp
next
  assume "Atom (predAtm p []) \<in> set es"
  thus "Atom (predAtm p []) \<in> map_atom_fmla \<sigma> ` set es"
    by (metis image_eqI map_atom_fmla_nullary)
qed

text \<open>Hence, for a grounded well-formed action, a nullary atom is added (resp. deleted) by the
  instantiated effect iff it is added (resp. deleted) by the schema effect.\<close>
lemma exec_adds_iff:
  assumes "ac \<in> set (actions D)"
  shows "(Atom (predAtm p []) \<in> set (adds (effect (instantiate_classical_action_schema ac args))))
       \<longleftrightarrow> (Atom (predAtm p []) \<in> set (adds (ac_eff ac)))"
  unfolding inst_effect_sel(1) set_map
  by (rule inst_eff_list_iff[OF wf_eff_lits(1)[OF assms]])

lemma exec_dels_iff:
  assumes "ac \<in> set (actions D)"
  shows "(Atom (predAtm p []) \<in> set (dels (effect (instantiate_classical_action_schema ac args))))
       \<longleftrightarrow> (Atom (predAtm p []) \<in> set (dels (ac_eff ac)))"
  unfolding inst_effect_sel(2) set_map
  by (rule inst_eff_list_iff[OF wf_eff_lits(2)[OF assms]])

text \<open>The literal component of a single-action execution: delete then add the (instantiated)
  effect's atoms.\<close>
lemma fst_execute_plan_action:
  "fst (execute_plan_action a M)
   = (fst M - set (dels (effect (the (res_inst a))))) \<union> set (adds (effect (the (res_inst a))))"
  unfolding execute_plan_action_def by simp

text \<open>STRIPS successor value at a single variable: add-effects take precedence, then delete-effects,
  otherwise the state is unchanged. A direct consequence of the AFP per-variable lemmas.\<close>
lemma execute_operator_var:
  "execute_operator s opr v
   = (if v \<in> set (add_effects_of opr) then Some True
      else if v \<in> set (delete_effects_of opr) then Some False else s v)"
proof -
  consider (a) "v \<in> set (add_effects_of opr)"
    | (d) "v \<notin> set (add_effects_of opr)" "v \<in> set (delete_effects_of opr)"
    | (n) "v \<notin> set (add_effects_of opr)" "v \<notin> set (delete_effects_of opr)" by blast
  thus ?thesis
  proof cases
    case a thus ?thesis using effect__strips_iii_a[OF refl a] by simp
  next
    case d
    have "(s \<then> opr) v = Some False"
      by (rule effect__strips_iii_b[OF refl]) (use d in simp)
    thus ?thesis using d by simp
  next
    case n
    have "(s \<then> opr) v = s v"
      by (rule effect__strips_iii_c[OF refl]) (use n in simp)
    thus ?thesis using n by simp
  qed
qed

text \<open>Every atom occurring in a (fixed) schema effect is a nullary, well-formed predicate atom.\<close>
lemma eff_adds_nullary:
  assumes "ac \<in> set (actions D)" "x \<in> set (adds (fix_effect (ac_eff ac)))"
  shows "\<exists>k. x = Atom (predAtm k []) \<and> wf_pred k"
proof -
  have "wf_lit_atom x" using wf_eff_lits(1)[OF assms(1)] assms(2) by (cases "ac_eff ac") auto
  thus ?thesis using wf_lit_atom_nullary by blast
qed

lemma eff_dels_nullary:
  assumes "ac \<in> set (actions D)" "x \<in> set (dels (fix_effect (ac_eff ac)))"
  shows "\<exists>k. x = Atom (predAtm k []) \<and> wf_pred k"
proof -
  have "wf_lit_atom x" using wf_eff_lits(2)[OF assms(1)] assms(2) by (cases "ac_eff ac") auto
  thus ?thesis using wf_lit_atom_nullary by blast
qed

text \<open>The STRIPS operator's add/delete effects, in terms of the schema effect: a positive variable
  \<open>vpos n\<close> is added iff the atom is added, deleted iff it is (genuinely) deleted; a negative variable
  \<open>vneg n\<close> is added iff the atom is deleted, deleted iff the atom is added.\<close>
lemma vpos_add_iff:
  assumes "ac \<in> set (actions D)"
  shows "vpos n \<in> set (add_effects_of (as_strips_op ac)) \<longleftrightarrow> Atom (predAtm n []) \<in> set (adds (ac_eff ac))"
proof -
  have "vpos n \<in> set (add_effects_of (as_strips_op ac))
      \<longleftrightarrow> vpos n \<in> atm_as_vpos ` set (adds (fix_effect (ac_eff ac)))"
    using atm_vpos_notin_vneg_image[OF eff_dels_nullary[OF assms]] by (auto simp: as_strips_op_sel)
  also have "... \<longleftrightarrow> Atom (predAtm n []) \<in> set (adds (fix_effect (ac_eff ac)))"
    using atm_vpos_image_iff[OF eff_adds_nullary[OF assms]] .
  also have "... \<longleftrightarrow> Atom (predAtm n []) \<in> set (adds (ac_eff ac))" by (cases "ac_eff ac") simp
  finally show ?thesis .
qed

lemma vpos_del_iff:
  assumes "ac \<in> set (actions D)"
  shows "vpos n \<in> set (delete_effects_of (as_strips_op ac))
       \<longleftrightarrow> Atom (predAtm n []) \<in> set (dels (fix_effect (ac_eff ac)))"
proof -
  have "vpos n \<in> set (delete_effects_of (as_strips_op ac))
      \<longleftrightarrow> vpos n \<in> atm_as_vpos ` set (dels (fix_effect (ac_eff ac)))"
    using atm_vpos_notin_vneg_image[OF eff_adds_nullary[OF assms]] by (auto simp: as_strips_op_sel)
  also have "... \<longleftrightarrow> Atom (predAtm n []) \<in> set (dels (fix_effect (ac_eff ac)))"
    using atm_vpos_image_iff[OF eff_dels_nullary[OF assms]] .
  finally show ?thesis .
qed

lemma vneg_add_iff:
  assumes "ac \<in> set (actions D)"
  shows "vneg n \<in> set (add_effects_of (as_strips_op ac))
       \<longleftrightarrow> Atom (predAtm n []) \<in> set (dels (fix_effect (ac_eff ac)))"
proof -
  have "vneg n \<in> set (add_effects_of (as_strips_op ac))
      \<longleftrightarrow> vneg n \<in> atm_as_vneg ` set (dels (fix_effect (ac_eff ac)))"
    using atm_vneg_notin_vpos_image[OF eff_adds_nullary[OF assms]] by (auto simp: as_strips_op_sel)
  also have "... \<longleftrightarrow> Atom (predAtm n []) \<in> set (dels (fix_effect (ac_eff ac)))"
    using atm_vneg_image_iff[OF eff_dels_nullary[OF assms]] .
  finally show ?thesis .
qed

lemma vneg_del_iff:
  assumes "ac \<in> set (actions D)"
  shows "vneg n \<in> set (delete_effects_of (as_strips_op ac))
       \<longleftrightarrow> Atom (predAtm n []) \<in> set (adds (fix_effect (ac_eff ac)))"
proof -
  have "vneg n \<in> set (delete_effects_of (as_strips_op ac))
      \<longleftrightarrow> vneg n \<in> atm_as_vneg ` set (adds (fix_effect (ac_eff ac)))"
    using atm_vneg_notin_vpos_image[OF eff_dels_nullary[OF assms]] by (auto simp: as_strips_op_sel)
  also have "... \<longleftrightarrow> Atom (predAtm n []) \<in> set (adds (fix_effect (ac_eff ac)))"
    using atm_vneg_image_iff[OF eff_adds_nullary[OF assms]] .
  finally show ?thesis .
qed

text \<open>The static truth markers never appear among an operator's effects.\<close>
lemma vT_notin_eff:
  assumes "ac \<in> set (actions D)"
  shows "v\<^sub>T \<notin> set (add_effects_of (as_strips_op ac))"
    and "v\<^sub>T \<notin> set (delete_effects_of (as_strips_op ac))"
  using atm_vT_notin_images[OF eff_adds_nullary[OF assms]]
        atm_vT_notin_images[OF eff_dels_nullary[OF assms]]
  by (auto simp: as_strips_op_sel)

lemma vF_notin_eff:
  assumes "ac \<in> set (actions D)"
  shows "v\<^sub>F \<notin> set (add_effects_of (as_strips_op ac))"
    and "v\<^sub>F \<notin> set (delete_effects_of (as_strips_op ac))"
  using atm_vF_notin_images[OF eff_adds_nullary[OF assms]]
        atm_vF_notin_images[OF eff_dels_nullary[OF assms]]
  by (auto simp: as_strips_op_sel)

text \<open>All of an operator's effect variables are declared STRIPS variables.\<close>
lemma strips_pa_eff_covered:
  assumes "ac \<in> set (actions D)"
  shows "set (add_effects_of (as_strips_op ac)) \<subseteq> set strips_vars"
    and "set (delete_effects_of (as_strips_op ac)) \<subseteq> set strips_vars"
proof -
  have a: "\<forall>x \<in> set (adds (fix_effect (ac_eff ac))). wf_lit_atom x"
    using wf_eff_lits(1)[OF assms] by (cases "ac_eff ac") simp
  have d: "\<forall>x \<in> set (dels (fix_effect (ac_eff ac))). wf_lit_atom x"
    using wf_eff_lits(2)[OF assms] by (cases "ac_eff ac") auto
  show "set (add_effects_of (as_strips_op ac)) \<subseteq> set strips_vars"
    using a d wf_lit_atom_covered by (auto simp: as_strips_op_sel)
  show "set (delete_effects_of (as_strips_op ac)) \<subseteq> set strips_vars"
    using a d wf_lit_atom_covered by (auto simp: as_strips_op_sel)
qed

text \<open>Executing a well-formed plan action commutes with the STRIPS encoding: the induced state of
  the successor world model equals the STRIPS successor state. Discharged via the AFP per-variable
  lemmas \<open>effect__strips_iii_a/b/c\<close> and a \<open>strips_var_cases\<close> analysis.\<close>
lemma execute_commute:
  assumes "wf_classical_plan_action a"
  shows "strips_model (execute_plan_action a M) = execute_operator (strips_model M) (strips_pa a)"
proof (rule ext)
  fix v
  obtain n0 args where aeq: "a = SimplePlanAction n0 args" by (cases a)
  with assms have args: "args = []" using grounded_pa_nullary by simp
  from assms aeq args obtain ac where
    res: "resolve_classical_action_schema n0 = Some ac" and mem: "ac \<in> set (actions D)"
    using wf_pa_refs_ac by metis
  have op: "strips_pa a = as_strips_op ac" using aeq args res by simp
  have ri: "the (res_inst a) = instantiate_classical_action_schema ac []"
    using aeq args res by simp
  \<comment> \<open>membership of a nullary atom in the executed literal set\<close>
  have execmem: "(Atom (predAtm p []) :: object atom formula) \<in> fst (execute_plan_action a M)
     \<longleftrightarrow> (Atom (predAtm p []) \<in> set (adds (ac_eff ac))
         \<or> ((Atom (predAtm p []) :: object atom formula) \<in> fst M
             \<and> Atom (predAtm p []) \<notin> set (dels (ac_eff ac))))" for p
    unfolding fst_execute_plan_action ri
    by (auto simp: exec_adds_iff[OF mem] exec_dels_iff[OF mem])
  show "strips_model (execute_plan_action a M) v = execute_operator (strips_model M) (strips_pa a) v"
  proof (cases "v \<in> set strips_vars")
    case True
    then show ?thesis
    proof (cases rule: strips_var_cases)
      case T
      have "execute_operator (strips_model M) (strips_pa a) v\<^sub>T = strips_model M v\<^sub>T"
        unfolding op execute_operator_var using vT_notin_eff[OF mem] by simp
      thus ?thesis unfolding T by simp
    next
      case F
      have "execute_operator (strips_model M) (strips_pa a) v\<^sub>F = strips_model M v\<^sub>F"
        unfolding op execute_operator_var using vF_notin_eff[OF mem] by simp
      thus ?thesis unfolding F by simp
    next
      case (pos n)
      have R: "execute_operator (strips_model M) (strips_pa a) (vpos n)
             = (if Atom (predAtm n []) \<in> set (adds (ac_eff ac)) then Some True
                else if Atom (predAtm n []) \<in> set (dels (fix_effect (ac_eff ac))) then Some False
                else strips_model M (vpos n))"
        unfolding op execute_operator_var
        using vpos_add_iff[OF mem] vpos_del_iff[OF mem] by simp
      show ?thesis
        unfolding pos(2) R
        using strips_model_vpos[OF pos(1)] execmem[of n]
        by (cases "ac_eff ac") auto
    next
      case (neg n)
      have R: "execute_operator (strips_model M) (strips_pa a) (vneg n)
             = (if Atom (predAtm n []) \<in> set (dels (fix_effect (ac_eff ac))) then Some True
                else if Atom (predAtm n []) \<in> set (adds (fix_effect (ac_eff ac))) then Some False
                else strips_model M (vneg n))"
        unfolding op execute_operator_var
        using vneg_add_iff[OF mem] vneg_del_iff[OF mem] by simp
      show ?thesis
        unfolding neg(2) R
        using strips_model_vneg[OF neg(1)] execmem[of n]
        by (cases "ac_eff ac") auto
    qed
  next
    case False
    hence ln: "strips_model (execute_plan_action a M) v = None"
      unfolding strips_model_def by simp
    have "v \<notin> set (add_effects_of (strips_pa a))" "v \<notin> set (delete_effects_of (strips_pa a))"
      unfolding op using strips_pa_eff_covered[OF mem] False by auto
    hence "execute_operator (strips_model M) (strips_pa a) v = strips_model M v"
      unfolding execute_operator_var by simp
    also have "... = None" using False unfolding strips_model_def by simp
    finally show ?thesis using ln by simp
  qed
qed

text \<open>Per goal literal: a well-formed literal is map-satisfied iff its encoding goal variable
  \<^term>\<open>fst (lit_as_goal l)\<close> carries the required value \<^term>\<open>snd (lit_as_goal l)\<close> in
  \<^term>\<open>strips_model M\<close>. Note \<^const>\<open>lit_as_goal\<close> encodes a negative literal as \<open>(vpos n, False)\<close>
  (it never uses \<^term>\<open>vneg\<close>).\<close>
lemma lit_as_goal_correct:
  assumes "wf_lit l"
  shows "(valuation M \<Turnstile>\<^sub>m l) \<longleftrightarrow> strips_model M (fst (lit_as_goal l)) = Some (snd (lit_as_goal l))"
proof (cases l rule: wf_lit.cases)
  case 1 thus ?thesis by simp
next
  case 2 thus ?thesis by simp
next
  case (3 n)
  hence "wf_pred n" using assms by simp
  thus ?thesis using 3 by (simp add: valuation_def strips_model_vpos)
next
  case (4 n)
  hence "wf_pred n" using assms by simp
  thus ?thesis using 4 by (simp add: valuation_def strips_model_vpos domIff)
qed (use assms in simp_all)

text \<open>The goal STRIPS state \<^const>\<open>strips_goal\<close> is exactly the assignment induced by the goal
  literals: every defined entry comes from some goal literal, and every goal literal contributes
  to the domain.\<close>
lemma strips_goal_Some:
  "strips_goal v = Some b \<Longrightarrow> \<exists>l \<in> set (un_and (goal P)). lit_as_goal l = (v, b)"
  unfolding strips_goal_def using fold_upd_goal_Some by fastforce

lemma strips_goal_dom:
  assumes "l \<in> set (un_and (goal P))"
  shows "fst (lit_as_goal l) \<in> dom strips_goal"
proof -
  obtain v b where vb: "lit_as_goal l = (v, b)" by (cases "lit_as_goal l")
  from assms have "lit_as_goal l \<in> set (fmla_as_goals (goal P))" by force
  with vb have mem: "(v, b) \<in> set (fmla_as_goals (goal P))" by simp
  have "strips_goal v \<noteq> None" unfolding strips_goal_def by (rule fold_upd_goal_mem_dom[OF mem])
  thus ?thesis using vb by (simp add: domIff)
qed

text \<open>The PDDL goal holds in \<open>M\<close> iff the encoded STRIPS goal state is dominated by
  \<^term>\<open>strips_model M\<close>. Soundness of the \<^const>\<open>vpos\<close>-only goal encoding relies on
  \<open>goal_no_conflict\<close> (no atom occurs with both polarities), which holds for the single-atom
  goal produced by goal normalization.\<close>
lemma goal_bridge:
  "(valuation M \<Turnstile>\<^sub>m goal P) \<longleftrightarrow> strips_goal \<subseteq>\<^sub>m strips_model M"
proof -
  have conj: "is_conj (goal P)" using normed_prob by blast
  have gnf: "num_free_fmla (goal P)" using num_free_prob unfolding num_free_prob_def by blast
  have wfl: "\<forall>l \<in> set (un_and (goal P)). wf_lit l" using wf_goal_lits[OF gnf] .
  have L: "(valuation M \<Turnstile>\<^sub>m goal P)
       \<longleftrightarrow> (\<forall>l \<in> set (un_and (goal P)). strips_model M (fst (lit_as_goal l)) = Some (snd (lit_as_goal l)))"
  proof -
    have "(valuation M \<Turnstile>\<^sub>m goal P) \<longleftrightarrow> (\<forall>l \<in> set (un_and (goal P)). valuation M \<Turnstile>\<^sub>m l)"
      by (rule map_sem_un_and[OF conj])
    also have "... \<longleftrightarrow> (\<forall>l \<in> set (un_and (goal P)). strips_model M (fst (lit_as_goal l)) = Some (snd (lit_as_goal l)))"
      using wfl lit_as_goal_correct by blast
    finally show ?thesis .
  qed
  have R: "(strips_goal \<subseteq>\<^sub>m strips_model M)
       \<longleftrightarrow> (\<forall>l \<in> set (un_and (goal P)). strips_model M (fst (lit_as_goal l)) = Some (snd (lit_as_goal l)))"
  proof
    assume le: "strips_goal \<subseteq>\<^sub>m strips_model M"
    show "\<forall>l \<in> set (un_and (goal P)). strips_model M (fst (lit_as_goal l)) = Some (snd (lit_as_goal l))"
    proof
      fix l assume l: "l \<in> set (un_and (goal P))"
      obtain v b where vb: "lit_as_goal l = (v, b)" by (cases "lit_as_goal l")
      have dom: "v \<in> dom strips_goal" using strips_goal_dom[OF l] vb by simp
      then obtain b'' where sgb: "strips_goal v = Some b''" by blast
      from strips_goal_Some[OF sgb] obtain l'' where
        l'': "l'' \<in> set (un_and (goal P))" "lit_as_goal l'' = (v, b'')" by blast
      have "snd (lit_as_goal l'') = snd (lit_as_goal l)"
        using goal_no_conflict[OF l''(1) l] l''(2) vb by simp
      hence "b'' = b" using l''(2) vb by simp
      with sgb have sgv: "strips_goal v = Some b" by simp
      have "strips_model M v = strips_goal v" using le dom by (auto simp: map_le_def)
      thus "strips_model M (fst (lit_as_goal l)) = Some (snd (lit_as_goal l))"
        using sgv vb by simp
    qed
  next
    assume holds: "\<forall>l \<in> set (un_and (goal P)). strips_model M (fst (lit_as_goal l)) = Some (snd (lit_as_goal l))"
    show "strips_goal \<subseteq>\<^sub>m strips_model M"
      unfolding map_le_def
    proof
      fix v assume "v \<in> dom strips_goal"
      then obtain b where sgb: "strips_goal v = Some b" by blast
      from strips_goal_Some[OF sgb] obtain l where
        l: "l \<in> set (un_and (goal P))" "lit_as_goal l = (v, b)" by blast
      have "strips_model M v = Some b" using holds l by (metis fst_conv snd_conv)
      thus "strips_goal v = strips_model M v" using sgb by simp
    qed
  qed
  from L R show ?thesis by simp
qed

text \<open>Simulation of a classical-plan execution by the STRIPS serial-plan execution.\<close>
lemma sim_serial:
  assumes "valid_classical_plan_alt M \<pi>s M'"
  shows "execute_serial_plan (strips_model M) (map strips_pa \<pi>s) = strips_model M'"
  using assms
proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons a as)
  from Cons.prems have en: "plan_action_enabled a M"
    and rest: "valid_classical_plan_alt (execute_plan_action a M) as M'" by simp_all
  from en have wfa: "wf_classical_plan_action a"
    unfolding plan_action_enabled_def by (simp add: Let_def)
  from en have "valuation M \<Turnstile>\<^sub>m precondition ((the \<circ> res_inst) a)"
    unfolding plan_action_enabled_def by (simp add: Let_def)
  hence app: "is_operator_applicable_in (strips_model M) (strips_pa a)"
    using enabled_applicable[OF wfa] by simp
  have "execute_serial_plan (strips_model M) (map strips_pa (a # as))
      = execute_serial_plan (execute_operator (strips_model M) (strips_pa a)) (map strips_pa as)"
    using app by simp
  also have "... = execute_serial_plan (strips_model (execute_plan_action a M)) (map strips_pa as)"
    using execute_commute[OF wfa] by simp
  also have "... = strips_model M'" using Cons.IH[OF rest] .
  finally show ?case .
qed

text \<open>Every restored STRIPS operator is one of the task's operators.\<close>
lemma sim_ops:
  assumes "valid_classical_plan_alt M \<pi>s M'"
  shows "list_all (\<lambda>op. ListMem op (operators_of as_strips)) (map strips_pa \<pi>s)"
  using assms
proof (induction \<pi>s arbitrary: M)
  case Nil thus ?case by simp
next
  case (Cons a as)
  from Cons.prems have en: "plan_action_enabled a M"
    and rest: "valid_classical_plan_alt (execute_plan_action a M) as M'" by simp_all
  from en have wfa: "wf_classical_plan_action a"
    unfolding plan_action_enabled_def by (simp add: Let_def)
  obtain n args where aeq: "a = SimplePlanAction n args" by (cases a)
  from wfa aeq obtain ac where res: "resolve_classical_action_schema n = Some ac"
    and mem: "ac \<in> set (actions D)" using wf_pa_refs_ac by metis
  have "strips_pa a = as_strips_op ac" using aeq res by simp
  hence "ListMem (strips_pa a) (operators_of as_strips)"
    using mem by (simp add: as_strips_sel ListMem_iff)
  thus ?case using Cons.IH[OF rest] by simp
qed

subsection \<open> Semantics preservation \<close>

theorem valid_plan_right:
  assumes "valid_classical_plan2 \<pi>s"
  shows "is_serial_solution_for_problem as_strips (map strips_pa \<pi>s)"
proof -
  from assms obtain M' where
    vp: "valid_classical_plan_alt I \<pi>s M'" and gl: "valuation M' \<Turnstile>\<^sub>m goal P"
    using valid_classical_plan2_alt by blast
  have "execute_serial_plan strips_init (map strips_pa \<pi>s) = strips_model M'"
    using sim_serial[OF vp] strips_init_eq_model by simp
  hence "goal_of as_strips \<subseteq>\<^sub>m execute_serial_plan (initial_of as_strips) (map strips_pa \<pi>s)"
    using gl goal_bridge by (simp add: as_strips_sel)
  moreover have "list_all (\<lambda>op. ListMem op (operators_of as_strips)) (map strips_pa \<pi>s)"
    using sim_ops[OF vp] .
  ultimately show ?thesis unfolding is_serial_solution_for_problem_def by blast
qed

text \<open>A numeric-free, grounded action instantiates to a ground action with no numeric effects.\<close>
lemma inst_no_numeric:
  assumes "ac \<in> set (actions D)"
  shows "numeric_effects (ground_action.effect (instantiate_classical_action_schema ac args)) = []"
proof -
  have nf: "num_free_eff (ac_eff ac)"
    using assms num_free_prob
    unfolding num_free_prob_def num_free_dom_def num_free_ac_def by blast
  hence "numeric_effects (ac_eff ac) = []" by (cases "ac_eff ac") auto
  thus ?thesis
    unfolding instantiate_classical_action_schema_alt by (simp add: ast_effect.map_sel(3))
qed

text \<open>Applicability of the encoded STRIPS operator suffices for the PDDL plan action to be enabled:
  the precondition matches by @{thm enabled_applicable}, and the numeric side-conditions of
  \<^const>\<open>plan_action_enabled\<close> are vacuous because the instantiated effect carries no numeric part.\<close>
lemma applicable_enabled:
  assumes "wf_classical_plan_action a"
    and "is_operator_applicable_in (strips_model M) (strips_pa a)"
  shows "plan_action_enabled a M"
proof -
  obtain n args where aeq: "a = SimplePlanAction n args" by (cases a)
  from assms(1) aeq obtain ac where
    res: "resolve_classical_action_schema n = Some ac" and mem: "ac \<in> set (actions D)"
    using wf_pa_refs_ac by metis
  have a': "the (res_inst a) = instantiate_classical_action_schema ac args" using aeq res by simp
  have num: "numeric_effects (ground_action.effect (the (res_inst a))) = []"
    unfolding a' by (rule inst_no_numeric[OF mem])
  have pre: "valuation M \<Turnstile>\<^sub>m ground_action.precondition (the (res_inst a))"
    using enabled_applicable[OF assms(1)] assms(2) by simp
  have nintf: "numeric_effects_non_intrf (the (res_inst a))"
    by (rule numeric_effects_non_intrf_no_numeric_effects[OF num])
  have rhs: "ast_effect_enumerate_rhs_primitive_numeric_expressions
                (ground_action.effect (the (res_inst a))) = []"
  proof -
    obtain aa dd nn where e: "ground_action.effect (the (res_inst a)) = Effect aa dd nn"
      by (cases "ground_action.effect (the (res_inst a))")
    have "nn = []" using num e by simp
    thus ?thesis using e by simp
  qed
  show ?thesis
    unfolding plan_action_enabled_def Let_def
    using assms(1) pre nintf rhs by simp
qed

text \<open>Every STRIPS operator of the encoded task is the encoding of some well-formed plan action.\<close>
lemma strips_op_has_pa:
  assumes "opr \<in> set strips_ops"
  obtains a where "wf_classical_plan_action a" "strips_pa a = opr"
proof -
  from assms obtain ac where ac: "ac \<in> set (actions D)" "opr = as_strips_op ac" by auto
  have "wf_classical_plan_action (SimplePlanAction (ac_name ac) [])"
    unfolding grounded_pa_nullary using ac(1) by auto
  moreover have "strips_pa (SimplePlanAction (ac_name ac) []) = opr"
    using ac by (simp add: resolve_classical_action_schema_name)
  ultimately show thesis using that by blast
qed

text \<open>Reverse simulation: any STRIPS operator sequence (over the task's operators) is simulated by a
  PDDL plan — namely the restoration of its applicable prefix. Executing that prefix in PDDL induces
  the same final STRIPS state that \<open>execute_serial_plan\<close> reaches (which halts at the first
  non-applicable operator).\<close>
lemma sim_serial_rev:
  assumes "\<forall>opr \<in> set ops. opr \<in> set strips_ops"
  shows "\<exists>\<pi>s M'. valid_classical_plan_alt M \<pi>s M'
              \<and> strips_model M' = execute_serial_plan (strips_model M) ops"
  using assms
proof (induction ops arbitrary: M)
  case Nil
  have "valid_classical_plan_alt M [] M \<and> strips_model M = execute_serial_plan (strips_model M) []"
    by simp
  thus ?case by blast
next
  case (Cons opr ops)
  from Cons.prems have hd: "opr \<in> set strips_ops" and tl: "\<forall>x\<in>set ops. x \<in> set strips_ops"
    by simp_all
  from hd obtain a where wfa: "wf_classical_plan_action a" and pa: "strips_pa a = opr"
    using strips_op_has_pa by blast
  show ?case
  proof (cases "is_operator_applicable_in (strips_model M) opr")
    case True
    have step: "execute_operator (strips_model M) opr = strips_model (execute_plan_action a M)"
      using execute_commute[OF wfa] pa by simp
    from Cons.IH[OF tl, of "execute_plan_action a M"] obtain \<pi>s M' where
      ih1: "valid_classical_plan_alt (execute_plan_action a M) \<pi>s M'"
      and ih2: "strips_model M' = execute_serial_plan (strips_model (execute_plan_action a M)) ops"
      by blast
    have en: "plan_action_enabled a M"
      using applicable_enabled[OF wfa] True pa by simp
    have "valid_classical_plan_alt M (a # \<pi>s) M'" using en ih1 by simp
    moreover have "strips_model M' = execute_serial_plan (strips_model M) (opr # ops)"
      using True step ih2 by simp
    ultimately show ?thesis by blast
  next
    case False
    have "valid_classical_plan_alt M [] M
        \<and> strips_model M = execute_serial_plan (strips_model M) (opr # ops)"
      using False by simp
    thus ?thesis by blast
  qed
qed

text \<open>Reverse direction (soundness of the encoding): from a STRIPS serial solution one obtains a
  valid classical plan. Note the literal \<open>valid_classical_plan2 (restore_pddl_plan ops)\<close> is NOT
  provable: \<open>execute_serial_plan\<close> halts at the first non-applicable operator, so \<open>ops\<close> may carry
  trailing operators that are not enabled in PDDL, whereas \<open>valid_classical_plan2\<close> requires every
  action enabled. We therefore restore the applicable prefix and conclude existence — which is
  exactly what the soundness/completeness equivalence \<open>valid_plan_iff\<close> needs.\<close>
theorem restore_pddl_plan_valid:
  assumes "is_serial_solution_for_problem as_strips ops"
  shows "\<exists>\<pi>s. valid_classical_plan2 \<pi>s"
proof -
  from assms have ops_mem: "\<forall>opr \<in> set ops. opr \<in> set strips_ops"
    unfolding is_serial_solution_for_problem_def
    by (simp add: as_strips_sel list_all_iff ListMem_iff)
  from assms have goaldom: "strips_goal \<subseteq>\<^sub>m execute_serial_plan strips_init ops"
    unfolding is_serial_solution_for_problem_def by (simp add: as_strips_sel)
  from sim_serial_rev[OF ops_mem, of I] obtain \<pi>s M' where
    vp: "valid_classical_plan_alt I \<pi>s M'"
    and ex: "strips_model M' = execute_serial_plan (strips_model I) ops" by blast
  have "strips_goal \<subseteq>\<^sub>m strips_model M'" using goaldom ex strips_init_eq_model by simp
  hence "valuation M' \<Turnstile>\<^sub>m goal P" using goal_bridge by blast
  hence "valid_classical_plan2 \<pi>s" using vp valid_classical_plan2_alt by blast
  thus ?thesis ..
qed

text \<open>\<^const>\<open>restore_pddl_pa\<close> decodes any task operator to a well-formed plan action that re-encodes
  to it. (\<^const>\<open>restore_pddl_pa\<close> uses \<^const>\<open>find_index\<close>, which returns the \<^emph>\<open>first\<close> matching index;
  if \<^const>\<open>as_strips_op\<close> is non-injective this is still a valid task action with the same encoding,
  which is all we need.)\<close>
lemma restore_pddl_pa_witness:
  assumes "opr \<in> set strips_ops"
  shows "wf_classical_plan_action (restore_pddl_pa opr) \<and> strips_pa (restore_pddl_pa opr) = opr"
proof -
  from find_index_Some_mem[OF assms] obtain j where
    fi: "find_index opr strips_ops = Some j" and jlen: "j < length strips_ops"
    and jnth: "strips_ops ! j = opr" by blast
  define ac where "ac = actions D ! j"
  have aclen: "j < length (actions D)" using jlen by simp
  hence acmem: "ac \<in> set (actions D)" unfolding ac_def by simp
  have opeq: "opr = as_strips_op ac" using jnth aclen unfolding ac_def by simp
  have rp: "restore_pddl_pa opr = SimplePlanAction (ac_name ac) []"
    unfolding restore_pddl_pa_def ac_def using fi by simp
  have "wf_classical_plan_action (SimplePlanAction (ac_name ac) [])"
    unfolding grounded_pa_nullary using acmem by auto
  moreover have "strips_pa (SimplePlanAction (ac_name ac) []) = opr"
    using acmem opeq by (simp add: resolve_classical_action_schema_name)
  ultimately show ?thesis unfolding rp by simp
qed

text \<open>Reverse simulation with the \<^emph>\<open>concrete\<close> restored plan: executing \<^const>\<open>restore_prefix\<close> in
  PDDL reaches a world model whose induced STRIPS state matches \<^const>\<open>execute_serial_plan\<close>. This is
  \<open>sim_serial_rev\<close> with the existential plan witness replaced by the literal
  \<^term>\<open>restore_prefix M ops\<close>.\<close>
lemma restore_prefix_sim:
  assumes "\<forall>opr \<in> set ops. opr \<in> set strips_ops"
  shows "\<exists>M'. valid_classical_plan_alt M (restore_prefix M ops) M'
            \<and> strips_model M' = execute_serial_plan (strips_model M) ops"
  using assms
proof (induction ops arbitrary: M)
  case Nil
  have "valid_classical_plan_alt M (restore_prefix M []) M
        \<and> strips_model M = execute_serial_plan (strips_model M) []" by simp
  thus ?case by blast
next
  case (Cons opr ops)
  from Cons.prems have hd: "opr \<in> set strips_ops" and tl: "\<forall>x\<in>set ops. x \<in> set strips_ops"
    by simp_all
  define a where "a = restore_pddl_pa opr"
  from restore_pddl_pa_witness[OF hd] have wfa: "wf_classical_plan_action a"
    and pa: "strips_pa a = opr" unfolding a_def by simp_all
  show ?case
  proof (cases "is_operator_applicable_in (strips_model M) opr")
    case True
    have step: "execute_operator (strips_model M) opr = strips_model (execute_plan_action a M)"
      using execute_commute[OF wfa] pa by simp
    from Cons.IH[OF tl, of "execute_plan_action a M"] obtain M' where
      ih1: "valid_classical_plan_alt (execute_plan_action a M)
              (restore_prefix (execute_plan_action a M) ops) M'"
      and ih2: "strips_model M' = execute_serial_plan (strips_model (execute_plan_action a M)) ops"
      by blast
    have en: "plan_action_enabled a M"
      using applicable_enabled[OF wfa] True pa by simp
    have rp: "restore_prefix M (opr # ops) = a # restore_prefix (execute_plan_action a M) ops"
      using True unfolding a_def by simp
    have "valid_classical_plan_alt M (restore_prefix M (opr # ops)) M'"
      unfolding rp using en ih1 by simp
    moreover have "strips_model M' = execute_serial_plan (strips_model M) (opr # ops)"
      using True step ih2 by simp
    ultimately show ?thesis by blast
  next
    case False
    have "valid_classical_plan_alt M (restore_prefix M (opr # ops)) M
        \<and> strips_model M = execute_serial_plan (strips_model M) (opr # ops)"
      using False by simp
    thus ?thesis by blast
  qed
qed

text \<open>Concrete soundness of the encoding: a STRIPS serial solution restores (via its applicable
  prefix) to a literal valid classical plan. Strengthens \<open>restore_pddl_plan_valid\<close> from an
  existence statement to an executable witness \<^term>\<open>restore_prefix I ops\<close>.\<close>
theorem restore_prefix_valid:
  assumes "is_serial_solution_for_problem as_strips ops"
  shows "valid_classical_plan2 (restore_prefix I ops)"
proof -
  from assms have ops_mem: "\<forall>opr \<in> set ops. opr \<in> set strips_ops"
    unfolding is_serial_solution_for_problem_def
    by (simp add: as_strips_sel list_all_iff ListMem_iff)
  from assms have goaldom: "strips_goal \<subseteq>\<^sub>m execute_serial_plan strips_init ops"
    unfolding is_serial_solution_for_problem_def by (simp add: as_strips_sel)
  from restore_prefix_sim[OF ops_mem, of I] obtain M' where
    vp: "valid_classical_plan_alt I (restore_prefix I ops) M'"
    and ex: "strips_model M' = execute_serial_plan (strips_model I) ops" by blast
  have "strips_goal \<subseteq>\<^sub>m strips_model M'" using goaldom ex strips_init_eq_model by simp
  hence "valuation M' \<Turnstile>\<^sub>m goal P" using goal_bridge by blast
  thus "valid_classical_plan2 (restore_prefix I ops)" using vp valid_classical_plan2_alt by blast
qed

corollary valid_plan_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) \<longleftrightarrow> (\<exists>ops. is_serial_solution_for_problem as_strips ops)"
  using valid_plan_right restore_pddl_plan_valid by blast

end text \<open>context strips_encodable_problem\<close>

subsection \<open> Parallel-to-serial bridge \<close>

text \<open>The verified SAT planner (AFP \<open>SAT_Plan_Base\<close>) decodes \<^emph>\<open>parallel\<close> STRIPS plans
  (\<^const>\<open>is_parallel_solution_for_problem\<close>), but our restoration consumes \<^emph>\<open>serial\<close> ones
  (\<^const>\<open>is_serial_solution_for_problem\<close>). This bridge flattens a parallel plan to a serial one via
  \<^const>\<open>concat\<close>. The AFP only provides the singleton-step case (\<open>flattening_lemma\<close>); here we cover the
  general (multi-operator-per-step) case using the AFP's per-step equality
  \<open>execute_parallel_operator_equals_execute_sequential_strips_if\<close> (valid under applicability,
  effect-consistency and non-interference).\<close>

text \<open>A parallel plan \<^emph>\<open>fires to completion\<close> from \<open>s\<close> when every step is applicable and
  effect-consistent in the state reached so far — i.e. \<^const>\<open>execute_parallel_plan\<close> never
  short-circuits. (A decoded SAT plan always satisfies this; the operator/frame encoding forces each
  active operator to be applicable at its time step.)\<close>
fun parallel_plan_fires
  :: "'a strips_state \<Rightarrow> 'a strips_operator list list \<Rightarrow> bool"
  where
    "parallel_plan_fires s [] = True"
  | "parallel_plan_fires s (ops # opss) =
       (are_all_operators_applicable s ops \<and> are_all_operator_effects_consistent ops
        \<and> parallel_plan_fires (execute_parallel_operator s ops) opss)"

text \<open>State-level bridge: under per-step non-interference, a fully-firing parallel execution reaches
  the same state as the serial execution of the flattened plan.\<close>
lemma execute_parallel_plan_eq_serial_concat:
  assumes "parallel_plan_fires s \<pi>"
    and "\<forall>ops \<in> set \<pi>. are_all_operators_non_interfering ops"
  shows "execute_parallel_plan s \<pi> = execute_serial_plan s (concat \<pi>)"
  using assms
proof (induction \<pi> arbitrary: s)
  case Nil
  show ?case by simp
next
  case (Cons ops opss)
  from Cons.prems(1) have app: "are_all_operators_applicable s ops"
    and cons: "are_all_operator_effects_consistent ops"
    and fires': "parallel_plan_fires (execute_parallel_operator s ops) opss"
    by auto
  from Cons.prems(2) have ni: "are_all_operators_non_interfering ops"
    and ni': "\<forall>os \<in> set opss. are_all_operators_non_interfering os"
    by auto
  have pe: "execute_parallel_operator s ops = execute_serial_plan s ops"
    using execute_parallel_operator_equals_execute_sequential_strips_if[OF app cons ni] .
  have "execute_parallel_plan s (ops # opss)
      = execute_parallel_plan (execute_parallel_operator s ops) opss"
    using app cons by simp
  also have "\<dots> = execute_serial_plan (execute_parallel_operator s ops) (concat opss)"
    using Cons.IH[OF fires' ni'] by simp
  also have "\<dots> = execute_serial_plan (execute_serial_plan s ops) (concat opss)"
    using pe by simp
  also have "\<dots> = execute_serial_plan s (ops @ concat opss)"
    using execute_serial_plan_split[OF app ni] by simp
  also have "\<dots> = execute_serial_plan s (concat (ops # opss))" by simp
  finally show ?case .
qed

text \<open>Solution-level bridge: a fully-firing, per-step non-interfering parallel solution flattens to a
  serial solution of the same problem.\<close>
theorem parallel_solution_imp_serial_solution:
  assumes "parallel_plan_fires (initial_of \<Pi>\<^sub>P) \<pi>"
    and "\<forall>ops \<in> set \<pi>. are_all_operators_non_interfering ops"
    and "is_parallel_solution_for_problem \<Pi>\<^sub>P \<pi>"
  shows "is_serial_solution_for_problem \<Pi>\<^sub>P (concat \<pi>)"
proof -
  from assms(3) have goal_par: "(\<Pi>\<^sub>P)\<^sub>G \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>\<^sub>P)\<^sub>I) \<pi>"
    and mem: "\<forall>ops \<in> set \<pi>. \<forall>op \<in> set ops. op \<in> set ((\<Pi>\<^sub>P)\<^sub>\<O>)"
    unfolding is_parallel_solution_for_problem_def list_all_iff ListMem_iff by auto
  have eq: "execute_parallel_plan ((\<Pi>\<^sub>P)\<^sub>I) \<pi> = execute_serial_plan ((\<Pi>\<^sub>P)\<^sub>I) (concat \<pi>)"
    using execute_parallel_plan_eq_serial_concat[OF assms(1,2)] .
  from mem have "\<forall>op \<in> set (concat \<pi>). op \<in> set ((\<Pi>\<^sub>P)\<^sub>\<O>)" by auto
  thus ?thesis using goal_par eq
    unfolding is_serial_solution_for_problem_def list_all_iff ListMem_iff by auto
qed

end