theory PDDL_Sema_Supplement
  imports "Analysis_Free_Base.Instantiations"
    "Analysis_Free_Base.Happening_Semantics_Discrete"
    "Analysis_Free_Base.Numeric_Update_Functions"
    Grounding_Common.Formula_Utils
    Grounding_Utils.Grounding_Utils
begin

section \<open>Signature-level PDDL semantics supplements (reusable)\<close>

text \<open>AST-agnostic supplement lemmas about a PDDL domain/problem \<^emph>\<open>signature\<close>: splitting the
  well-formedness bundles into component facts, characterizing predicate/function-declaration and
  effect well-formedness, resolving \<open>sig\<close>/\<open>func_sig\<close> against the declaration lists, and lifting an
  atom-level signature relation to formulas/effects/world models (well-formedness covariance). These
  mention only the shared \<open>domain_signature\<close>/\<open>problem_signature\<close> semantics (from Analysis_Free_Base),
  so they are reusable by any grounder. They were previously in
  \<open>Classical_Grounding.Classical_PDDL_Sema_Supplement\<close>; the classical-AST supplements (action schemas, the
  \<open>ast_classical_*\<close> locales) stay there.\<close>

subsection \<open>Type helpers\<close>

text \<open>The single type name of a primitive type.\<close>
abbreviation (input) get_t :: "type \<Rightarrow> name" where
    "get_t T \<equiv> hd (primitives T)"

lemma get_t_alt: "get_t (Either (t # ts)) = t"
  by simp

subsection \<open>Splitting the well-formedness bundles\<close>

lemmas (in wf_domain_signature) wf_D_sig =
  conj_split_7[OF wf_domain_signature[unfolded wf_domain_signature_def]]

lemmas (in wf_problem_signature) wf_P_sig =
  conj_split_3[OF wf_problem_signature[unfolded wf_problem_signature_def]]

lemmas (in wf_problem_signature) wf_sig = wf_D_sig wf_P_sig

subsection \<open>Well-formedness characterizations\<close>

lemma (in domain_signature) wf_predicate_decl_alt:
  "wf_predicate_decl pd \<longleftrightarrow> (\<forall>T \<in> set (predicate_decl.argTs pd). wf_type T)"
  by (cases pd; simp)

lemma (in domain_signature) wf_function_decl_alt:
  "wf_function_decl fd \<longleftrightarrow> (\<forall>T \<in> set (function_decl.argTs fd). wf_type T)"
  by (cases fd; simp)

text \<open>An effect is well-formed iff all its add/delete formula-atoms and numeric effects are; the
  characterization used to drive the effect covariance proof.\<close>
lemma (in domain_signature) wf_effect_alt:
    "wf_effect tyt \<epsilon> \<longleftrightarrow>
        (list_all (wf_fmla_atom tyt) (adds \<epsilon>))
      \<and> (list_all (wf_fmla_atom tyt) (dels \<epsilon>))
      \<and> (list_all (wf_numeric_effect tyt) (numeric_effects \<epsilon>))"
  by (cases \<epsilon>; auto simp: list_all_iff)

subsection \<open>Resolving \<open>sig\<close>\<close>

abbreviation "split_pred \<equiv> (\<lambda>PredDecl p n \<Rightarrow> (p, n))"

lemma split_pred_alt: "split_pred p = (pred p, predicate_decl.argTs p)"
  using predicate_decl.case_eq_if by auto

lemma (in domain_signature) pred_resolve:
  assumes "distinct (map pred predicates)"
  shows "sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set predicates"
proof -
  let ?preds = "predicates"
  have "map (fst \<circ> split_pred) ?preds = map pred ?preds"
    using split_pred_alt by simp
  hence dis: "distinct (map (fst \<circ> split_pred) ?preds)"
    using assms by metis

  have "PredDecl p Ts \<in> set ?preds
    \<longleftrightarrow> (p, Ts) \<in> set (map split_pred ?preds)"
    using split_pred_alt by force
  also have "... \<longleftrightarrow> map_of (map split_pred ?preds) p = Some Ts"
    using dis by simp

  ultimately show ?thesis using sig_def by simp
qed

lemmas (in wf_domain_signature) sig_Some = pred_resolve[OF wf_D_sig(2)]

subsection \<open>Resolving \<open>func_sig\<close>\<close>

abbreviation "split_func \<equiv> (\<lambda>FuncDecl f n \<Rightarrow> (f, n))"

lemma split_func_alt: "split_func f = (function_decl.func f, function_decl.argTs f)"
  using function_decl.case_eq_if by auto

lemma (in domain_signature) func_resolve:
  assumes "distinct (map function_decl.func functions)"
  shows "func_sig f = Some Ts \<longleftrightarrow> FuncDecl f Ts \<in> set functions"
proof -
  let ?funcs = "functions"
  have "map (fst \<circ> split_func) ?funcs = map function_decl.func ?funcs"
    using split_func_alt by simp
  hence dis: "distinct (map (fst \<circ> split_func) ?funcs)"
    using assms by metis

  have "FuncDecl f Ts \<in> set ?funcs
    \<longleftrightarrow> (f, Ts) \<in> set (map split_func ?funcs)"
    using split_func_alt by force
  also have "... \<longleftrightarrow> map_of (map split_func ?funcs) f = Some Ts"
    using dis by simp

  ultimately show ?thesis using func_sig_def by simp
qed

lemmas (in wf_domain_signature) func_sig_Some = func_resolve[OF wf_D_sig(4)]

subsection \<open>Well-formedness covariance\<close>

text \<open>If a one-step weakening of the signature (an atom that is well-formed under the first
  signature is well-formed under the second) holds, then well-formedness of every compound
  syntactic category — formulas, formula-atoms, numeric expressions/effects, effects, and whole
  world models — is preserved across the two signatures.\<close>

lemma co_fmla_wf:
  assumes "\<And>a. domain_signature.wf_atom ty1 preds1 funs1 tyt1 a
            \<Longrightarrow> domain_signature.wf_atom ty2 preds2 funs2 tyt2 a"
  shows "domain_signature.wf_fmla ty1 preds1 funs1 tyt1 \<phi>
       \<Longrightarrow> domain_signature.wf_fmla ty2 preds2 funs2 tyt2 \<phi>"
  apply (induction \<phi>)
  unfolding domain_signature.wf_fmla.simps
  subgoal for x apply (induction x)
    by (auto intro: assms)
  by auto

lemma co_fmla_atom_wf:
  assumes "\<And>a. domain_signature.wf_atom ty1 preds1 funs1 tyt1 a
            \<Longrightarrow> domain_signature.wf_atom ty2 preds2 funs2 tyt2 a"
  shows "domain_signature.wf_fmla_atom ty1 preds1 tyt1 \<phi>
       \<Longrightarrow> domain_signature.wf_fmla_atom ty2 preds2 tyt2 \<phi>"
  apply (subst domain_signature.wf_fmla_atom_alt)
  apply (subst (asm) domain_signature.wf_fmla_atom_alt)
  by (auto intro: assms co_fmla_wf)

lemma co_numeric_expression_wf:
  assumes "\<And>p. domain_signature.wf_primitive_numeric_expression ty1 funs1 tyt1 p
            \<Longrightarrow> domain_signature.wf_primitive_numeric_expression ty2 funs2 tyt2 p"
  shows "domain_signature.wf_numeric_expression ty1 funs1 tyt1 n
       \<Longrightarrow> domain_signature.wf_numeric_expression ty2 funs2 tyt2 n"
  apply (induction n)
  unfolding domain_signature.wf_numeric_expression.simps
  by (auto intro: assms)

lemma co_numeric_effect_wf:
  assumes "\<And>p. domain_signature.wf_primitive_numeric_expression ty1 funs1 tyt1 p
            \<Longrightarrow> domain_signature.wf_primitive_numeric_expression ty2 funs2 tyt2 p"
  shows "domain_signature.wf_numeric_effect ty1 funs1 tyt1 ne
       \<Longrightarrow> domain_signature.wf_numeric_effect ty2 funs2 tyt2 ne"
  apply (induction ne)
  unfolding domain_signature.wf_numeric_effect.simps
  by (blast intro: assms co_numeric_expression_wf)


lemma co_effect_wf:
  assumes "\<And>a. domain_signature.wf_atom ty1 preds1 funs1 tyt1 a
            \<Longrightarrow> domain_signature.wf_atom ty2 preds2 funs2 tyt2 a"
      and "\<And>p. domain_signature.wf_primitive_numeric_expression ty1 funs1 tyt1 p
            \<Longrightarrow> domain_signature.wf_primitive_numeric_expression ty2 funs2 tyt2 p"
  shows "domain_signature.wf_effect ty1 preds1 funs1 tyt1 \<epsilon>
       \<Longrightarrow> domain_signature.wf_effect ty2 preds2 funs2 tyt2 \<epsilon>"
  unfolding domain_signature.wf_effect_alt list_all_iff
  by (auto intro: assms co_fmla_atom_wf co_numeric_effect_wf)

lemma co_wm_wf:
  assumes "\<And>a. domain_signature.wf_atom ty1 preds1 funs1
                 (problem_signature.objT consts1 objs1) a
            \<Longrightarrow> domain_signature.wf_atom ty2 preds2 funs2
                 (problem_signature.objT consts2 objs2) a"
  shows "problem_signature.wf_world_model ty1 preds1 consts1 objs1 m
       \<Longrightarrow> problem_signature.wf_world_model ty2 preds2 consts2 objs2 m"
  apply (induction m)
  unfolding problem_signature.wf_world_model.simps
  by (auto intro: assms co_fmla_atom_wf)

subsection \<open>Formula / atom / effect well-formedness\<close>

lemma (in domain_signature) wf_fmla_alt: "wf_fmla tyt \<phi> = (\<forall>a\<in>atoms \<phi>. wf_atom tyt a)"
      by (induction \<phi>) auto

lemma (in domain_signature) wf_fmla_mono_atoms:
  assumes "atoms f \<subseteq> atoms g" "wf_fmla tyt g"
  shows "wf_fmla tyt f"
  using assms unfolding wf_fmla_alt by blast

lemmas (in domain_signature) wf_atom_deep = wf_atom.simps[unfolded wf_pred_atom.simps]

lemma (in domain_signature) wf_type_alt: "wf_type T \<longleftrightarrow> set (primitives T) \<subseteq> insert (STR ''object'') (fst ` set ty_decl)"
  by (cases T; simp)

lemma (in domain_signature) bigand_wf:
  assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
  shows "wf_fmla tyt (\<^bold>\<And> \<phi>s)"
  using assms by (induction \<phi>s; simp)

lemma (in domain_signature) bigor_wf:
  assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
  shows "wf_fmla tyt (\<^bold>\<Or> \<phi>s)"
  using assms by (induction \<phi>s; simp)

lemma (in domain_signature) wf_fmla_atom_pred:
  "wf_fmla_atom tyt f \<Longrightarrow> is_predAtom f"
  apply (cases f)
  subgoal for a
    by (cases a) auto
  by auto

lemma (in domain_signature) wf_action_head_alt: "wf_action_head h \<longleftrightarrow>
  distinct (map fst (ast_action_head.parameters h))" by (cases h) simp

lemma (in domain_signature) wf_simple_action_body_alt: "wf_simple_action_body tyt b \<longleftrightarrow>
  wf_fmla tyt (ast_simple_action_body.precondition b) \<and> wf_effect tyt (ast_simple_action_body.effect b)"
  by (cases b) simp

subsection \<open>Well-formedness monotonicity under signature weakening\<close>

lemma (in domain_signature) wf_fmla_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_fmla tys \<phi>"
  shows "wf_fmla tys' \<phi>"
  using assms apply (induction \<phi>)
       apply (simp add: wf_atom_mono) by simp_all

lemma (in domain_signature) wf_numeric_effect_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_numeric_effect tys f"
  shows "wf_numeric_effect tys' f"
  using assms(2) apply (induction f)
  using wf_numeric_expression_mono[OF assms(1)] wf_pne_mono[OF assms(1)]
  by simp

lemma (in domain_signature) wf_effect_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_effect tys eff"
  shows "wf_effect tys' eff"
  using assms apply (cases eff)
  using wf_fmla_atom_mono[OF assms(1)] wf_numeric_effect_mono[OF assms(1)]
  by simp

subsection \<open>Subtype relation\<close>

lemma (in domain_signature) subtype_edge_swap: "subtype_edge = prod.swap"
  by (intro ext; auto)

lemma (in domain_signature) subtype_rel_alt: "subtype_rel = (set ty_decl)\<inverse>"
  unfolding subtype_rel_def
  by (subst subtype_edge_swap; auto)

lemma (in domain_signature) subtype_rel_star_alt: "subtype_rel\<^sup>* = ((set ty_decl)\<^sup>*)\<inverse>"
    using subtype_rel_alt rtrancl_converse by simp

subsection \<open>World models and ground actions\<close>

lemma (in problem_signature) wf_func_assign_imp_not_predAtm:
  "wf_func_assign x \<Longrightarrow> \<not>is_predAtom x"
  apply (cases x)
  subgoal for a
    apply (cases a)
    by auto
  by auto

lemma (in problem_signature) wf_lwm_basic:
  "wf_world_model M \<Longrightarrow> lwm_basic (fst M)"
  using wf_fmla_atom_pred unfolding lwm_basic_def
  by (cases M) auto

lemma (in problem_signature) wf_ground_action_alt: "wf_ground_action ga \<longleftrightarrow>
  wf_fmla objT (precondition ga) \<and> wf_effect objT (effect ga)"
  by (cases ga; simp)

lemma (in wf_problem_signature) consts_objs_disj:
  "fst ` set consts \<inter> fst ` set objs = {}"
  using list.set_map wf_P_sig by auto

lemma (in wf_problem_signature) objm_le_objT: "map_of objs \<subseteq>\<^sub>m objT"
proof -
  have "dom constT \<inter> dom (map_of objs) = {}"
    using constT_def consts_objs_disj
    by (simp add: dom_map_of_conv_image_fst)
  thus ?thesis using objT_def
    by (simp add: map_add_comm map_le_iff_map_add_commute)
qed

subsection \<open>\<open>sig\<close> / \<open>func_sig\<close> resolving to \<open>None\<close>\<close>

lemma (in domain_signature) sig_None:
    "sig p = None \<longleftrightarrow> p \<notin> pred ` set predicates"
  proof -
    have "sig p = None \<longleftrightarrow> p \<notin> fst ` set (map split_pred predicates)"
      using sig_def by (simp add: map_of_eq_None_iff)
    also have "... \<longleftrightarrow> p \<notin> pred ` set predicates"
      using split_pred_alt by auto
    ultimately show ?thesis by simp
  qed

lemma (in domain_signature) func_sig_None:
    "func_sig f = None \<longleftrightarrow> f \<notin> function_decl.func ` set functions"
  proof -
    have "func_sig f = None \<longleftrightarrow> f \<notin> fst ` set (map split_func functions)"
      using func_sig_def by (simp add: map_of_eq_None_iff)
    also have "... \<longleftrightarrow> f \<notin> function_decl.func ` set functions"
      using split_func_alt by auto
    ultimately show ?thesis by simp
  qed

section \<open>Reusable formula, atom, valuation, and ground-action utilities\<close>

text \<open>Formula/atom accessors, the map-formula (PDDL partial-valuation) semantics over big
  conjunctions/disjunctions, ground-action application on a world model, atoms-in-the-domain-of-a-
  valuation reasoning, and the well-formedness \<leftrightarrow> enumerated-PNE bridge. All AST-agnostic; moved here
  from \<open>Classical_Grounding.Classical_PDDL_Sema_Supplement\<close>.\<close>

subsection \<open>Formula semantics and accessors\<close>

lemma BigOr_map_semantics[simp]: "A \<Turnstile>\<^sub>m \<^bold>\<Or>F = ((\<forall>f\<in>set F. atoms f \<subseteq> dom A) \<and> (\<exists>f \<in> set F. A \<Turnstile>\<^sub>m f))"
  by (induction F) auto

lemma BigAnd_map_semantics[simp]: "A \<Turnstile>\<^sub>m \<^bold>\<And>F = ((\<forall>f\<in>set F. A \<Turnstile>\<^sub>m f))"
  by (induction F) auto

fun un_Atom :: "'a formula \<Rightarrow> 'a" where
  "un_Atom (Atom x) = x" |
  "un_Atom _ = undefined"

lemma is_predAtom_decomp:
  "is_predAtom a \<longleftrightarrow> (\<exists>p xs. a = Atom (predAtm p xs))"
  apply (cases a)
  subgoal for x
    by (cases x) simp_all
  by simp_all

abbreviation "map_atom_fmla \<equiv> map_formula \<circ> map_atom"

lemma formula_atom_simps[simp]:
  "atoms (Atom a) = {a}"
  "atoms \<bottom> = {}"
  "atoms (\<^bold>\<not> F) = atoms F"
  "atoms (F \<^bold>\<and> G) = atoms F \<union> atoms G"
  "atoms (F \<^bold>\<or> G) = atoms F \<union> atoms G"
  "atoms (F \<^bold>\<rightarrow> G) = atoms F \<union> atoms G"
  by auto

subsection \<open>Ground-action application\<close>

lemma apply_ground_action_alt:
  "apply_ground_actions [a] (L, N) =
     ((L - set (dels (effect a))) \<union> set (adds (effect a)),
      action_numeric_update_function a N)"
  by (simp add: action_list_numeric_update_function_def)

lemma apply_ground_actions_equiv_weak:
  assumes "map effect as = map effect bs"
  shows "apply_ground_actions as = apply_ground_actions bs"
proof -

  have "map action_numeric_update_function as = map action_numeric_update_function bs"
    using assms unfolding map_equality_iff action_numeric_update_function_def by simp
  hence 1: "action_list_numeric_update_function as = action_list_numeric_update_function bs"
    using action_list_numeric_update_function_def by simp

  have "effect ` set as = effect ` set bs" using assms set_map[where f = effect] by metis
  hence 2: "(\<Union>x\<in>set as. (f o effect) x) = (\<Union>x\<in>set bs. (f o effect) x)" for f::"object ast_effect \<Rightarrow> 'a set"
    by (metis image_comp)

  show ?thesis
    using assms
    apply (intro ext)
    subgoal for M
      apply (cases M)
      apply simp
      using 1
      using 2[where f1 = "set o adds"] 2[where f1 = "set o dels"] by simp
    done
qed

lemma numeric_effects_non_intrf_equiv_weak:
  assumes "effect a = effect b"
  shows "numeric_effects_non_intrf a = numeric_effects_non_intrf b"
  unfolding numeric_effects_non_intrf_def
  using assms by simp

lemma numeric_effects_non_intrf_no_numeric_effects:
  assumes "numeric_effects (effect a) = []"
  shows "numeric_effects_non_intrf a"
  using assms unfolding numeric_effects_non_intrf_def by simp

lemma enumerate_rhs_pnes_no_numeric_effects:
  assumes "numeric_effects (effect a) = []"
  shows "ast_effect_enumerate_rhs_primitive_numeric_expressions (effect a) = []"
  using assms by (cases "effect a") simp

subsection \<open>Atoms in the domain of a valuation\<close>

lemma atoms_dom_valuation_Un_eq:
  assumes "A \<inter> Atom ` atoms \<F> = {}"
  shows "(atoms \<F> \<subseteq> dom (valuation (M, X))) = (atoms \<F> \<subseteq> dom (valuation (M \<union> A, X)))"
  using assms
proof (induction \<F>)
  case (Atom x)
  then show ?case unfolding valuation_def by (induction x) auto
next
  case Bot
  then show ?case by auto
next
  case (Not \<F>)
  then show ?case by auto
next
  case (And \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))" using And by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))" using And by fastforce
  ultimately
  show ?case by simp
next
  case (Or \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))" using Or by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))" using Or by fastforce
  ultimately
  show ?case by simp
next
  case (Imp \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))" using Imp by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))" using Imp by fastforce
  ultimately
  show ?case by simp
qed

lemma atoms_dom_valuation_Diff_eq:
  assumes "D \<inter> Atom ` atoms \<F> = {}"
  shows "(atoms \<F> \<subseteq> dom (valuation (M, X))) = (atoms \<F> \<subseteq> dom (valuation (M - D, X)))"
  using assms
proof (induction \<F>)
  case (Atom x)
  then show ?case unfolding valuation_def by (induction x) auto
next
  case Bot
  then show ?case by auto
next
  case (Not \<F>)
  then show ?case by auto
next
  case (And \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))" using And by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))" using And by fastforce
  ultimately
  show ?case by simp
next
  case (Or \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))" using Or by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))" using Or by fastforce
  ultimately
  show ?case by simp
next
  case (Imp \<F>1 \<F>2)
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))" using Imp by fastforce
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))" using Imp by fastforce
  ultimately
  show ?case by simp
qed

lemma entail_adds_irrelevant:
  assumes "lwm_basic M" "lwm_basic A"
          "A \<inter> Atom ` atoms \<F> = {}"
  shows "(valuation (M \<union> A, X) \<Turnstile>\<^sub>m \<F>) \<longleftrightarrow> (valuation (M, X) \<Turnstile>\<^sub>m \<F>)"
  using assms
proof (induction \<F>)
  case (Atom x)
  thus ?case unfolding valuation_def by (cases x) simp_all
next
  case Bot
  then show ?case by simp
next
  case (Not \<F>)
  have "(atoms \<F> \<subseteq> dom (valuation (M, X))) = (atoms \<F> \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Not(4) by simp
  thus ?case unfolding map_formula_semantics_simps using Not by simp
next
  case (And \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using And by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using And by auto
  ultimately
  show ?case by auto
next
  case (Or \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Or by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Or by auto
  ultimately
  show ?case by auto
next
  case (Imp \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Imp by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M \<union> A, X)))"
    apply (rule atoms_dom_valuation_Un_eq)
    using Imp by auto
  ultimately
  show ?case by auto
qed

lemma entail_dels_irrelevant:
  assumes "lwm_basic M" "lwm_basic D"
          "D \<inter> Atom ` atoms \<F> = {}"
        shows "(valuation (M - D , X) \<Turnstile>\<^sub>m \<F>) \<longleftrightarrow> (valuation (M, X) \<Turnstile>\<^sub>m \<F>)"
  using assms
proof (induction \<F>)
  case (Atom x)
  then show ?case unfolding valuation_def by (cases x) simp_all
next
  case Bot
  then show ?case by simp
next
  case (Not \<F>)
  have "(atoms \<F> \<subseteq> dom (valuation (M, X))) = (atoms \<F> \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Not(4) by simp
  thus ?case unfolding map_formula_semantics_simps using Not by simp
next
  case (And \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using And by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using And by auto
  ultimately
  show ?case by auto
next
  case (Or \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Or by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Or by auto
  ultimately
  show ?case by auto
next
  case (Imp \<F>1 \<F>2)
  moreover
  have "(atoms \<F>1 \<subseteq> dom (valuation (M, X))) = (atoms \<F>1 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Imp by auto
  moreover
  have "(atoms \<F>2 \<subseteq> dom (valuation (M, X))) = (atoms \<F>2 \<subseteq> dom (valuation (M - D, X)))"
    apply (rule atoms_dom_valuation_Diff_eq)
    using Imp by auto
  ultimately
  show ?case by auto
qed

lemma formula_atoms_in_dom_valuation_iff:
  "atoms F \<subseteq> dom (valuation M) \<longleftrightarrow>
     set (formula_enumerate_primitive_numeric_expressions F) \<subseteq> dom (snd M)
     \<and> (\<forall>d \<in> set (formula_enumerate_divisor_expressions F). d\<lbrakk>snd M\<rbrakk> \<noteq> Some 0)"
  by (induction M)
     (auto simp: dom_valuation_iff subset_iff
       set_formula_enumerate_primitive_numeric_expressions_conv
       set_formula_enumerate_divisor_expressions_conv)

subsection \<open>Formula predicates\<close>

fun fmla_preds :: "'ent atom formula \<Rightarrow> predicate set" where
  "fmla_preds (Atom (predAtm p xs)) = {p}" |
  "fmla_preds (Atom _) = {}" |
  "fmla_preds \<bottom> = {}" |
  "fmla_preds (\<^bold>\<not> \<phi>) = fmla_preds \<phi>" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<rightarrow> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2"

lemma fmla_preds_alt: "fmla_preds \<phi> = {p | p xs. predAtm p xs \<in> atoms \<phi>}"
  apply (induction \<phi>)
  subgoal for x
    apply (cases x; simp_all)
    done
  by auto

lemma map_preserves_fmla_preds: "fmla_preds F = fmla_preds ((map_formula \<circ> map_atom) f F)"
proof (induction F)
  case (Atom x)
  thus ?case by (cases x) simp_all
qed auto

lemma notin_fmla_preds_notin_atoms: "p \<notin> fmla_preds \<phi> \<Longrightarrow> predAtm p args \<notin> atoms \<phi>"
  using fmla_preds_alt by blast

subsection \<open>Well-formedness \<leftrightarrow> enumerated primitive numeric expressions\<close>

lemma (in domain_signature) wf_numeric_expression_imp_wf_pnes:
  assumes "wf_numeric_expression tyt n"
      and "p \<in> set (enumerate_primitive_numeric_expressions n)"
    shows "wf_primitive_numeric_expression tyt p"
  using assms by (induction n) auto

lemma (in domain_signature) wf_atom_imp_wf_pnes:
  assumes "wf_atom tyt a"
      and "p \<in> set (atom_enumerate_primitive_numeric_expressions a)"
    shows "wf_primitive_numeric_expression tyt p"
  using assms by (cases a) (auto intro: wf_numeric_expression_imp_wf_pnes)

lemma (in domain_signature) wf_fmla_imp_wf_pnes:
  assumes "wf_fmla tyt f"
      and "p \<in> set (formula_enumerate_primitive_numeric_expressions f)"
    shows "wf_primitive_numeric_expression tyt p"
  using assms by (induction f) (auto intro: wf_atom_imp_wf_pnes)

lemma (in domain_signature) wf_fmla_imp_wf_pred_atom:
  assumes "wf_fmla tyt f"
      and "predAtm p xs \<in> atoms f"
    shows "wf_pred_atom tyt (p, xs)"
  using assms by (induction f) auto

lemma (in domain_signature) wf_fmla_imp_eqs_def:
  assumes "wf_fmla tyt f"
      and "eqAtm a b \<in> atoms f"
    shows "tyt a \<noteq> None \<and> tyt b \<noteq> None"
  using assms by (induction f) auto

lemma (in domain_signature) wf_numeric_expressionI:
  assumes "\<And>p. p \<in> set (enumerate_primitive_numeric_expressions n)
              \<Longrightarrow> wf_primitive_numeric_expression tyt p"
    shows "wf_numeric_expression tyt n"
  using assms by (induction n) auto

lemma (in domain_signature) wf_atomI:
  assumes "\<And>p. p \<in> set (atom_enumerate_primitive_numeric_expressions a)
              \<Longrightarrow> wf_primitive_numeric_expression tyt p"
      and "\<And>p xs. a = predAtm p xs \<Longrightarrow> wf_pred_atom tyt (p, xs)"
      and "\<And>x y. a = eqAtm x y \<Longrightarrow> tyt x \<noteq> None \<and> tyt y \<noteq> None"
    shows "wf_atom tyt a"
  using assms by (cases a) (auto intro: wf_numeric_expressionI)

lemma (in domain_signature) wf_fmlaI:
  assumes "\<And>p. p \<in> set (formula_enumerate_primitive_numeric_expressions f)
              \<Longrightarrow> wf_primitive_numeric_expression tyt p"
      and "\<And>p xs. predAtm p xs \<in> atoms f \<Longrightarrow> wf_pred_atom tyt (p, xs)"
      and "\<And>x y. eqAtm x y \<in> atoms f \<Longrightarrow> tyt x \<noteq> None \<and> tyt y \<noteq> None"
    shows "wf_fmla tyt f"
  using assms by (induction f) (force intro!: wf_atomI)+

end
