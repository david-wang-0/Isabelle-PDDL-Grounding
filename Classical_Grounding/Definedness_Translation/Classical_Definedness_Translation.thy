theory Classical_Definedness_Translation
  imports Classical_Definedness_Translation_Locales
begin

section \<open>Definedness Translation Well-Formedness Proofs\<close>

subsection \<open>PNE preservation under the atom/formula translation\<close>

lemma def_translate_atom_pnes:
  "set (atom_enumerate_primitive_numeric_expressions (def_translate_atom pfx a))
   \<subseteq> set (atom_enumerate_primitive_numeric_expressions a)"
  apply (cases a)
  apply (auto simp: pne_to_def_atom_def)
  subgoal for x31 x32 x
    apply (cases x31 rule: Abstract_Syntax.numeric_expression.exhaust;
           cases x32 rule: Abstract_Syntax.numeric_expression.exhaust)
    apply (auto simp: pne_to_def_atom_def
        split: Abstract_Syntax.primitive_numeric_expression.splits Abstract_Syntax.func.splits if_splits)
    done
  done

lemma def_translate_fmla_pnes:
  "set (formula_enumerate_primitive_numeric_expressions (def_translate_fmla pfx f))
   \<subseteq> set (formula_enumerate_primitive_numeric_expressions f)"
proof (induction f)
  case (Atom a)
  then show ?case unfolding def_translate_fmla_def by (simp add: def_translate_atom_pnes)
qed (auto simp: def_translate_fmla_def)

subsection \<open>Names of the generated \<open>Defined_\<close> predicates\<close>

fun func_nm :: "func \<Rightarrow> name" where "func_nm (Func n) = n"

definition "fdecl_nm fd \<equiv> func_nm (function_decl.func fd)"

lemma inj_func_nm: "inj func_nm"
  by (rule injI) (metis func_nm.simps func.exhaust)

lemma def_predicate_decl_alt:
  "def_predicate_decl pfx fd = PredDecl (Pred (pfx + fdecl_nm fd)) (function_decl.argTs fd)"
  by (cases fd; cases "function_decl.func fd") (auto simp: def_predicate_decl_def fdecl_nm_def)

lemma def_pred_name: "pred (def_predicate_decl pfx fd) = Pred (pfx + fdecl_nm fd)"
  by (simp add: def_predicate_decl_alt)

(* wf_numexpr_enum_pne, rhs_pne_wf, lhs_pne_wf moved to
   Grounding_Definedness_Translation.Definedness_Translation *)

subsection \<open>Signature monotonicity of the translated domain\<close>

context wf_ast_classical_domain_dt begin

text \<open>Types, functions and constants are untouched, so every constant derived
  from them is preserved.\<close>

lemma dt_subtype_rel: "dt.subtype_rel = subtype_rel"
  unfolding dt.subtype_rel_def subtype_rel_def by simp

lemma dt_is_of_type: "dt.is_of_type = is_of_type"
  apply (rule ext)+
  unfolding dt.is_of_type_def is_of_type_def dt.of_type_def of_type_def dt_subtype_rel by simp

lemma dt_func_sig: "dt.func_sig = func_sig"
  unfolding dt.func_sig_def func_sig_def by simp

lemma dt_constT: "dt.constT = constT"
  unfolding dt.constT_def constT_def by simp

lemma dt_type_wf: "wf_type T \<Longrightarrow> dt.wf_type T"
  using def_translate_dom_sel(1) by (cases T) simp

text \<open>The new \<open>Defined_\<close> predicate names are fresh and pairwise distinct.\<close>

lemma def_prefix_fresh: "def_prefix + n \<notin> set pred_names"
proof -
  have "def_prefix + n = safe_prefix pred_names + (STR ''Defined_'' + n)"
    unfolding def_prefix_def by (simp add: add.assoc)
  thus ?thesis using safe_prefix_correct by metis
qed

lemma fdecl_nm_dist: "distinct (map fdecl_nm (functions D))"
proof -
  have d: "distinct (functions D)" and fi: "inj_on function_decl.func (set (functions D))"
    using wf_D_sig(4) by (simp_all add: distinct_map)
  have "inj_on fdecl_nm (set (functions D))"
  proof (rule inj_onI)
    fix x y assume xy: "x \<in> set (functions D)" "y \<in> set (functions D)" "fdecl_nm x = fdecl_nm y"
    from xy(3) have "function_decl.func x = function_decl.func y"
      using inj_func_nm by (auto simp: fdecl_nm_def dest: injD)
    thus "x = y" using xy(1,2) fi by (auto dest: inj_onD)
  qed
  with d show ?thesis by (simp add: distinct_map)
qed

lemma dt_preds_dist: "distinct (map pred (predicates DT))"
proof -
  let ?new = "map (def_predicate_decl def_prefix) (functions D)"
  have "map pred ?new = map (\<lambda>fd. Pred (def_prefix + fdecl_nm fd)) (functions D)"
    by (simp add: def_pred_name)
  hence dist_new: "distinct (map pred ?new)"
    using fdecl_nm_dist
    by (simp add: distinct_map inj_on_def predicate.expand inj_prepend[unfolded inj_def])
  have disj: "set (map pred (predicates D)) \<inter> set (map pred ?new) = {}"
  proof -
    have fr: "Pred (def_prefix + fdecl_nm fd) \<notin> pred ` set (predicates D)" for fd
    proof
      assume "Pred (def_prefix + fdecl_nm fd) \<in> pred ` set (predicates D)"
      then obtain pd where "pd \<in> set (predicates D)" "pred pd = Pred (def_prefix + fdecl_nm fd)" by auto
      hence "def_prefix + fdecl_nm fd \<in> set pred_names" by (force simp: predicate.expand)
      thus False using def_prefix_fresh by blast
    qed
    show ?thesis
    proof (intro equals0I)
      fix y assume y: "y \<in> set (map pred (predicates D)) \<inter> set (map pred ?new)"
      hence yp: "y \<in> pred ` set (predicates D)" by simp
      from y obtain xb where "xb \<in> set (functions D)" "y = Pred (def_prefix + fdecl_nm xb)"
        by (auto simp: def_pred_name)
      thus False using yp fr by blast
    qed
  qed
  show ?thesis using wf_D_sig(2) dist_new disj by simp
qed

text \<open>The existing signature is preserved; declared functions induce a
  \<open>Defined_\<close> predicate with the same argument types.\<close>

lemma dt_sig:
  assumes "sig p = Some Ts" shows "dt.sig p = Some Ts"
proof -
  have "PredDecl p Ts \<in> set (predicates D)" using assms sig_Some by simp
  hence "PredDecl p Ts \<in> set (predicates DT)" by simp
  thus ?thesis using dt.pred_resolve[OF dt_preds_dist] by blast
qed

lemma dt_sig_def_pred:
  assumes "FuncDecl (Func n) ts \<in> set (functions D)"
  shows "dt.sig (Pred (def_prefix + n)) = Some ts"
proof -
  have "PredDecl (Pred (def_prefix + n)) ts \<in> set (predicates DT)"
    using assms by (force simp: def_predicate_decl_def)
  thus ?thesis using dt.pred_resolve[OF dt_preds_dist] by blast
qed

text \<open>The key lemma: a well-formed PNE maps to a well-formed \<open>Defined_\<close> atom.\<close>

lemma pne_to_def_atom_wf:
  assumes "wf_primitive_numeric_expression tyt p"
  shows "dt.wf_atom tyt (pne_to_def_atom def_prefix p)"
proof (cases p)
  case [simp]: (PNE f args)
  obtain n where [simp]: "f = Func n" by (cases f)
  from assms obtain ts where ts: "func_sig (Func n) = Some ts"
    and m: "list_all2 (is_of_type tyt) args ts" by (auto split: option.splits)
  from ts have "FuncDecl (Func n) ts \<in> set (functions D)" using func_sig_Some by simp
  hence sig: "dt.sig (Pred (def_prefix + n)) = Some ts" using dt_sig_def_pred by simp
  from m have m': "list_all2 (dt.is_of_type tyt) args ts" using dt_is_of_type by metis
  have wfp: "dt.wf_pred_atom tyt (Pred (def_prefix + n), args)"
    apply (subst dt.wf_pred_atom.simps) using sig m' by (auto simp: option.case_cong)
  hence "dt.wf_atom tyt (predAtm (Pred (def_prefix + n)) args)"
    by (subst dt.wf_atom.simps) simp
  thus ?thesis by (simp add: pne_to_def_atom_def)
qed

subsection \<open>Monotonicity of well-formedness under the bigger signature\<close>

lemma dt_pne_wf:
  assumes "wf_primitive_numeric_expression tyt p"
  shows "dt.wf_primitive_numeric_expression tyt p"
proof (cases p)
  case [simp]: (PNE f args)
  from assms obtain ts where ts: "func_sig f = Some ts"
    and m: "list_all2 (is_of_type tyt) args ts" by (auto split: option.splits)
  from ts have "dt.func_sig f = Some ts" using dt_func_sig by simp
  moreover from m have "list_all2 (dt.is_of_type tyt) args ts" using dt_is_of_type by metis
  ultimately show ?thesis by simp
qed

lemma dt_numexpr_wf: "wf_numeric_expression tyt e \<Longrightarrow> dt.wf_numeric_expression tyt e"
  by (induction e) (auto intro: dt_pne_wf)

lemma dt_atom_wf:
  assumes "wf_atom tyt a" shows "dt.wf_atom tyt a"
proof (cases a)
  case (predAtm p xs)
  with assms have "wf_pred_atom tyt (p, xs)" by simp
  then obtain Ts where sig: "sig p = Some Ts"
    and m: "list_all2 (is_of_type tyt) xs Ts" by (auto split: option.splits)
  have sig': "dt.sig p = Some Ts" using sig dt_sig by simp
  have m': "list_all2 (dt.is_of_type tyt) xs Ts" using m dt_is_of_type by metis
  have "dt.wf_pred_atom tyt (p, xs)"
    apply (subst dt.wf_pred_atom.simps) using sig' m' by (auto simp: option.case_cong)
  hence "dt.wf_atom tyt (predAtm p xs)" by (subst dt.wf_atom.simps) simp
  thus ?thesis using predAtm by simp
qed (use assms in \<open>auto simp: domain_signature.wf_atom.simps\<close>)

lemma dt_fmla_wf: "wf_fmla tyt \<phi> \<Longrightarrow> dt.wf_fmla tyt \<phi>"
  using dt_atom_wf co_fmla_wf by blast

lemma dt_fmla_atom_wf: "wf_fmla_atom tyt \<phi> \<Longrightarrow> dt.wf_fmla_atom tyt \<phi>"
  using dt_atom_wf co_fmla_atom_wf by blast

lemma dt_numeric_effect_wf: "wf_numeric_effect tyt ne \<Longrightarrow> dt.wf_numeric_effect tyt ne"
  using dt_pne_wf co_numeric_effect_wf by blast

lemma dt_eff_wf: "wf_effect tyt \<epsilon> \<Longrightarrow> dt.wf_effect tyt \<epsilon>"
  using dt_atom_wf dt_pne_wf co_effect_wf by blast

subsection \<open>Well-formedness of the translated atoms\<close>

text \<open>A \<open>Defined_\<close> atom built from a well-formed PNE is a well-formed fact.\<close>

lemma pne_to_def_fmla_atom_wf:
  assumes "wf_primitive_numeric_expression tyt p"
  shows "dt.wf_fmla_atom tyt (Atom (pne_to_def_atom def_prefix p))"
proof -
  obtain f args where [simp]: "p = PNE f args" by (cases p)
  obtain n where [simp]: "f = Func n" by (cases f)
  have wfa: "dt.wf_atom tyt (predAtm (Pred (def_prefix + n)) args)"
    using pne_to_def_atom_wf[OF assms] by (simp add: pne_to_def_atom_def)
  have "dt.wf_fmla_atom tyt (Atom (predAtm (Pred (def_prefix + n)) args))"
    by (subst dt.wf_fmla_atom.simps)
       (use wfa in \<open>simp add: domain_signature.wf_atom.simps\<close>)
  thus ?thesis by (simp add: pne_to_def_atom_def)
qed

lemma dt_def_translate_atom_wf:
  assumes "wf_atom tyt a"
  shows "dt.wf_atom tyt (def_translate_atom def_prefix a)"
proof (cases "\<exists>p. a = numericEqAtm (FunctionExpr p) (FunctionExpr p)")
  case True
  then obtain p where ap: "a = numericEqAtm (FunctionExpr p) (FunctionExpr p)" by blast
  hence "def_translate_atom def_prefix a = pne_to_def_atom def_prefix p" by simp
  moreover from assms ap have "wf_primitive_numeric_expression tyt p" by simp
  ultimately show ?thesis by (metis pne_to_def_atom_wf)
next
  case False
  hence "def_translate_atom def_prefix a = a"
    by (cases "(def_prefix, a)" rule: def_translate_atom.cases) auto
  thus ?thesis using dt_atom_wf[OF assms] by simp
qed

text \<open>TODO: the remaining assembly lemmas are blocked by the \<open>[simp]\<close>
  selector \<open>def_translate_dom_sel\<close> dismantling the \<open>dt.wf_\<dots>\<close> heads (rewriting
  \<open>predicates DT\<close> inside them), so the locale \<open>.simps\<close> and the monotonicity
  helper lemmas no longer match. The fix is to drop \<open>[simp]\<close> from the selectors
  and thread them explicitly through the proofs above; the mathematical content
  (all signature-monotonicity lemmas, the key \<open>pne_to_def_atom_wf\<close>, \<open>dt_atom_wf\<close>,
  freshness and distinctness) is already established.\<close>

lemma dt_def_translate_fmla_wf:
  assumes "wf_fmla tyt \<phi>" shows "dt.wf_fmla tyt (def_translate_fmla def_prefix \<phi>)"
  using assms unfolding def_translate_fmla_def
proof (induction \<phi>)
  case (Atom a)
  show ?case using Atom.prems domain_signature.wf_fmla.simps(1) dt_def_translate_atom_wf by fastforce
next
  case Bot
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
next
  case (Not \<phi>)
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
next
  case (And \<phi>1 \<phi>2)
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
next
  case (Or \<phi>1 \<phi>2)
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
next
  case (Imp \<phi>1 \<phi>2)
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
qed

lemma dt_wf_fmla_foldr_conj:
  assumes "\<forall>a\<in>set as. dt.wf_atom tyt a" and "dt.wf_fmla tyt base"
  shows "dt.wf_fmla tyt (foldr (\<^bold>\<and>) (map Atom as) base)"
  using assms by (induction as) (auto simp: domain_signature.wf_fmla.simps)

subsection \<open>Well-formedness of a translated action\<close>

lemma dt_ac_name: "ac_name (def_translate_ac def_prefix a) = ac_name a"
proof (cases a)
  case (SimpleActionSchema h b)
  obtain pre eff where "b = SimpleActionBody pre eff" by (cases b)
  moreover obtain ad dl ne where "eff = Effect ad dl ne" by (cases eff)
  ultimately show ?thesis using SimpleActionSchema by (simp add: Let_def)
qed

lemma dt_ac_wf:
  assumes "wf_classical_action_schema a"
  shows "dt.wf_classical_action_schema (def_translate_ac def_prefix a)"
proof (cases a)
  case a1: (SimpleActionSchema h b)
  obtain pre eff where b1: "b = SimpleActionBody pre eff" by (cases b)
  obtain ads dls neffs where e1: "eff = Effect ads dls neffs" by (cases eff)
  define tyt where "tyt = ty_term (map_of (parameters h)) constT"
  have head: "wf_action_head h" and body: "wf_simple_action_body tyt b"
    using assms a1 by (auto simp: tyt_def Let_def)
  from body b1 have wf_pre: "wf_fmla tyt pre" and wf_eff: "wf_effect tyt eff" by auto
  from wf_eff e1 have
    wf_ads: "\<forall>ae\<in>set ads. wf_fmla_atom tyt ae" and
    wf_dls: "\<forall>de\<in>set dls. wf_fmla_atom tyt de" and
    wf_neffs: "\<forall>ne\<in>set neffs. wf_numeric_effect tyt ne"
    by auto
  \<comment> \<open>The new \<open>Defined_\<close> atoms collected from the effect are well-formed.\<close>
  have rhs_wf: "dt.wf_atom tyt (pne_to_def_atom def_prefix q)"
    if "q \<in> set (rhs_pnes_eff (Effect ads dls neffs))" for q
    using rhs_pne_wf[OF wf_eff[unfolded e1] that] pne_to_def_atom_wf by blast
  have lhs_wf: "dt.wf_fmla_atom tyt (Atom (pne_to_def_atom def_prefix q))"
    if "q \<in> set (lhs_pnes_eff (Effect ads dls neffs))" for q
    using lhs_pne_wf[OF wf_eff[unfolded e1] that] pne_to_def_fmla_atom_wf by blast
  \<comment> \<open>The translated precondition is well-formed.\<close>
  have pre_atoms_wf:
    "\<forall>x\<in>set (map (pne_to_def_atom def_prefix) (remdups (rhs_pnes_eff (Effect ads dls neffs)))). dt.wf_atom tyt x"
    using rhs_wf by auto
  have base_wf: "dt.wf_fmla tyt (def_translate_fmla def_prefix pre)"
    using dt_def_translate_fmla_wf[OF wf_pre] .
  have new_pre_wf: "dt.wf_fmla tyt (foldr (\<^bold>\<and>)
      (map Atom (map (pne_to_def_atom def_prefix) (remdups (rhs_pnes_eff (Effect ads dls neffs)))))
      (def_translate_fmla def_prefix pre))"
    using dt_wf_fmla_foldr_conj[OF pre_atoms_wf base_wf] .
  \<comment> \<open>The translated effect is well-formed.\<close>
  have new_ads_wf: "dt.wf_fmla_atom tyt ae"
    if "ae \<in> set (map Atom (map (pne_to_def_atom def_prefix)
                  (remdups (lhs_pnes_eff (Effect ads dls neffs)))) @ ads)" for ae
  proof -
    from that consider
        "ae \<in> set (map Atom (map (pne_to_def_atom def_prefix)
                   (remdups (lhs_pnes_eff (Effect ads dls neffs)))))"
      | "ae \<in> set ads" by auto
    thus ?thesis
    proof cases
      case 1
      then obtain q where "q \<in> set (lhs_pnes_eff (Effect ads dls neffs))"
        "ae = Atom (pne_to_def_atom def_prefix q)" by auto
      thus ?thesis using lhs_wf by blast
    next
      case 2
      thus ?thesis using wf_ads dt_fmla_atom_wf by blast
    qed
  qed
  have new_dls_wf: "\<forall>de\<in>set dls. dt.wf_fmla_atom tyt de" using wf_dls dt_fmla_atom_wf by blast
  have new_neffs_wf: "\<forall>ne\<in>set neffs. dt.wf_numeric_effect tyt ne"
    using wf_neffs dt_numeric_effect_wf by blast
  have eff_wf: "dt.wf_effect tyt (Effect (map Atom (map (pne_to_def_atom def_prefix)
      (remdups (lhs_pnes_eff (Effect ads dls neffs)))) @ ads) dls neffs)"
    using new_ads_wf new_dls_wf new_neffs_wf by (subst dt.wf_effect.simps) blast
  \<comment> \<open>Assemble the translated action body and conclude.\<close>
  have body_wf: "dt.wf_simple_action_body tyt (SimpleActionBody
      (foldr (\<^bold>\<and>) (map Atom (map (pne_to_def_atom def_prefix)
        (remdups (rhs_pnes_eff (Effect ads dls neffs))))) (def_translate_fmla def_prefix pre))
      (Effect (map Atom (map (pne_to_def_atom def_prefix)
        (remdups (lhs_pnes_eff (Effect ads dls neffs)))) @ ads) dls neffs))"
    unfolding dt.wf_simple_action_body.simps using new_pre_wf eff_wf by blast
  have head_dt: "dt.wf_action_head h"
    using head by (cases h) (simp_all add: dt.wf_action_head.simps)
  have dac: "def_translate_ac def_prefix a = SimpleActionSchema h (SimpleActionBody
      (foldr (\<^bold>\<and>) (map Atom (map (pne_to_def_atom def_prefix)
        (remdups (rhs_pnes_eff (Effect ads dls neffs))))) (def_translate_fmla def_prefix pre))
      (Effect (map Atom (map (pne_to_def_atom def_prefix)
        (remdups (lhs_pnes_eff (Effect ads dls neffs)))) @ ads) dls neffs))"
    by (simp add: a1 b1 e1 Let_def del: def_translate_dom_sel)
  show ?thesis
    unfolding dac
    apply (subst dt.wf_classical_action_schema.simps)
    apply (simp only: Let_def dt_constT tyt_def[symmetric])
    apply (rule conjI[OF head_dt body_wf])
    done
qed 

subsection \<open>Well-formedness of the translated domain\<close>

lemma dt_preds_wf: "list_all dt.wf_predicate_decl (predicates DT)"
proof -
  have orig: "list_all dt.wf_predicate_decl (predicates D)"
  proof (subst list_all_iff, intro ballI)
    fix pd assume "pd \<in> set (predicates D)"
    hence "wf_predicate_decl pd" using wf_D_sig(3) by (simp add: list_all_iff)
    thus "dt.wf_predicate_decl pd" using dt_type_wf by (cases pd) auto
  qed
  have new: "dt.wf_predicate_decl (def_predicate_decl def_prefix fd)"
    if "fd \<in> set (functions D)" for fd
  proof -
    from that wf_D_sig(5) have "wf_function_decl fd" by (simp add: list_all_iff)
    thus ?thesis using dt_type_wf
      by (cases fd) (auto simp: def_predicate_decl_alt)
  qed
  show ?thesis using orig new by (auto simp: list_all_iff)
qed

lemma dt_dom_sig_wf: "dt.wf_domain_signature"
  unfolding dt.wf_domain_signature_def
proof (intro conjI)
  show "dt.wf_types" using wf_D_sig(1) by (simp add: dt.wf_types_def wf_types_def)
  show "distinct (map pred (predicates DT))" by (rule dt_preds_dist)
  show "Ball (set (predicates DT)) dt.wf_predicate_decl"
    using dt_preds_wf by (simp add: list_all_iff)
  show "distinct (map function_decl.func (functions DT))"
    using wf_D_sig(4) by simp
  show "Ball (set (functions DT)) dt.wf_function_decl"
  proof
    fix f assume "f \<in> set (functions DT)"
    hence "wf_function_decl f" using wf_D_sig(5) by simp
    thus "dt.wf_function_decl f" by (cases f) (auto intro: dt_type_wf)
  qed
  show "distinct (map fst (consts DT))"
    using wf_D_sig(6) by simp
  show "\<forall>(n,y)\<in>set (consts DT). dt.wf_type y"
    using wf_D_sig(7) by (auto intro: dt_type_wf)
qed

lemma dt_acs_dist: "distinct (map ac_name (actions DT))"
  by (simp add: list.map_comp comp_def dt_ac_name wf_D(2))

theorem def_translate_dom_wf: "dt.wf_classical_domain"
  unfolding dt.wf_classical_domain_def
  using dt_dom_sig_wf dt_acs_dist dt_ac_wf wf_D(3)
  by (auto simp: list_all_iff)

end

subsection \<open>Well-formedness of the translated problem\<close>

context wf_ast_classical_problem_dt begin

theorem def_translate_prob_wf: "pt.wf_classical_problem"
proof -
  \<comment> \<open>The object typing environment is untouched by the translation.\<close>
  have objT_eq: "pt.objT = objT"
    by (simp add: problem_signature.objT_def dt_constT)
  \<comment> \<open>Types are unchanged, so type well-formedness coincides.\<close>
  have wf_type_eq: "pt.wf_type T \<longleftrightarrow> wf_type T" for T
    by (cases T) (simp add: domain_signature.wf_type.simps def_translate_prob_sel)
  \<comment> \<open>The problem signature stays well-formed: only fresh predicates were added.\<close>
  have psig: "pt.wf_problem_signature"
    unfolding problem_signature.wf_problem_signature_def
  proof (intro conjI)
    show "pt.wf_domain_signature" using dt_dom_sig_wf by (simp add: def_translate_prob_sel)
    show "distinct (map fst (objects def_translate_prob) @ map fst (consts pt.D))"
      using wf_P_sig(2) by (simp add: def_translate_prob_sel)
    show "\<forall>(n,y)\<in>set (objects def_translate_prob). pt.wf_type y"
      using wf_P_sig(3) by (simp add: def_translate_prob_sel wf_type_eq)
  qed
  \<comment> \<open>Every freshly generated init fact is a well-formed \<open>Defined_\<close> atom
      with a fresh predicate name.\<close>
  have newfact: "dt.wf_fmla_atom objT g \<and> (\<exists>n args. g = Atom (predAtm (Pred (def_prefix + n)) args))"
    if g_in: "g \<in> set (List.map_filter (init_def_fact def_prefix) (init P))" for g
  proof -
    from g_in obtain f where f: "f \<in> set (init P)" and idf: "init_def_fact def_prefix f = Some g"
      by (auto simp: set_map_filter)
    from idf obtain l c where fl: "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr c))"
      and g_eq: "g = Atom (pne_to_def_atom def_prefix l)"
      by (auto simp: init_def_fact_def split: formula.splits atom.splits numeric_expression.splits)
    have "wf_fmla_atom objT f \<or> wf_func_assign f" using f wf_P(4) by blast
    moreover have "\<not> wf_fmla_atom objT f" using fl by simp
    ultimately have "wf_func_assign f" by blast
    hence wfl: "wf_primitive_numeric_expression objT l" using fl by simp
    obtain f' args where lf: "l = PNE f' args" by (cases l)
    obtain n where fn: "f' = Func n" by (cases f')
    have "g = Atom (predAtm (Pred (def_prefix + n)) args)"
      using g_eq lf fn by (simp add: pne_to_def_atom_def)
    moreover have "dt.wf_fmla_atom objT g"
      using pne_to_def_fmla_atom_wf[OF wfl] g_eq by simp
    ultimately show ?thesis by blast
  qed
  \<comment> \<open>A well-formed declared predicate atom carries a declared predicate name.\<close>
  have wf_pred_in_names: "predicate.name p \<in> set pred_names"
    if wf: "wf_fmla_atom objT (Atom (predAtm p vs))" for p vs
  proof -
    from wf have "wf_pred_atom objT (p, vs)" by simp
    then obtain Ts where "sig p = Some Ts" by (auto split: option.splits)
    hence "PredDecl p Ts \<in> set (predicates D)" using sig_Some by simp
    hence "p \<in> pred ` set (predicates D)" by force
    thus ?thesis by force
  qed
  \<comment> \<open>Hence the new init facts are disjoint from the original ones: their
      predicate names are fresh, while every original fact is either a declared
      predicate atom or a (non-predicate) function assignment.\<close>
  have disj: "set (init P) \<inter> set (List.map_filter (init_def_fact def_prefix) (init P)) = {}"
  proof (intro equals0I)
    fix g assume "g \<in> set (init P) \<inter> set (List.map_filter (init_def_fact def_prefix) (init P))"
    hence gP: "g \<in> set (init P)"
      and gN: "g \<in> set (List.map_filter (init_def_fact def_prefix) (init P))" by auto
    from newfact[OF gN] obtain n args
      where gshape: "g = Atom (predAtm (Pred (def_prefix + n)) args)" by blast
    from gP wf_P(4) have "wf_fmla_atom objT g \<or> wf_func_assign g" by blast
    thus False
    proof
      assume "wf_fmla_atom objT g"
      hence "predicate.name (Pred (def_prefix + n)) \<in> set pred_names"
        using gshape wf_pred_in_names by blast
      hence "def_prefix + n \<in> set pred_names" by simp
      thus False using def_prefix_fresh by blast
    next
      assume "wf_func_assign g"
      thus False using gshape by simp
    qed
  qed
  \<comment> \<open>Function assignments stay well-formed under the bigger signature.\<close>
  have pt_fa: "pt.wf_func_assign f" if "wf_func_assign f" for f
  proof -
    from that obtain l r where f: "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
      and wfl: "wf_primitive_numeric_expression objT l"
      by (cases f rule: wf_func_assign.cases) auto
    from wfl have "dt.wf_primitive_numeric_expression objT l" by (rule dt_pne_wf)
    thus ?thesis using f objT_eq by (simp add: problem_signature.wf_func_assign.simps)
  qed
  \<comment> \<open>The domain-signature notions coincide for the \<open>pt\<close> and \<open>dt\<close> views.\<close>
  have wfa_eq: "pt.wf_fmla_atom = dt.wf_fmla_atom"
    and wfm_eq: "pt.wf_fmla = dt.wf_fmla"
    and dom_eq: "pt.wf_classical_domain = dt.wf_classical_domain"
    by (simp_all add: def_translate_prob_sel)
  show ?thesis
    unfolding pt.wf_classical_problem_def
  proof (intro conjI)
    show "pt.wf_classical_domain" using def_translate_dom_wf dom_eq by simp
    show "pt.wf_problem_signature" by (rule psig)
    show "distinct (init PT)"
      using wf_P(3) disj by (simp add: def_translate_prob_sel distinct_append)
    show "\<forall>f\<in>set (init PT). pt.wf_fmla_atom pt.objT f \<or> pt.wf_func_assign f"
    proof (intro ballI)
      fix f assume "f \<in> set (init PT)"
      hence "f \<in> set (init P) \<or> f \<in> set (List.map_filter (init_def_fact def_prefix) (init P))"
        by (auto simp: def_translate_prob_sel)
      thus "pt.wf_fmla_atom pt.objT f \<or> pt.wf_func_assign f"
      proof
        assume "f \<in> set (init P)"
        with wf_P(4) have "wf_fmla_atom objT f \<or> wf_func_assign f" by blast
        thus ?thesis
        proof
          assume "wf_fmla_atom objT f"
          hence "dt.wf_fmla_atom objT f" by (rule dt_fmla_atom_wf)
          hence "pt.wf_fmla_atom pt.objT f" by (simp add: wfa_eq objT_eq)
          thus ?thesis ..
        next
          assume "wf_func_assign f"
          hence "pt.wf_func_assign f" by (rule pt_fa)
          thus ?thesis ..
        qed
      next
        assume "f \<in> set (List.map_filter (init_def_fact def_prefix) (init P))"
        from newfact[OF this] have "dt.wf_fmla_atom objT f" by blast
        hence "pt.wf_fmla_atom pt.objT f" by (simp add: wfa_eq objT_eq)
        thus ?thesis ..
      qed
    qed
    show "pt.wf_fmla pt.objT (goal PT)"
      using dt_def_translate_fmla_wf[OF wf_P(5)]
      by (simp add: wfm_eq objT_eq def_translate_prob_sel)
  qed
qed

end

subsection \<open>Well-formedness sublocale instantiations\<close>

sublocale wf_ast_classical_domain_dt \<subseteq> dt: wf_ast_classical_domain DT
  using def_translate_dom_wf wf_ast_classical_domain.intro by simp

sublocale wf_ast_classical_problem_dt \<subseteq> pt: wf_ast_classical_problem PT
  using def_translate_prob_wf wf_ast_classical_problem.intro by simp

subsection \<open>Preservation of normalization\<close>

text \<open>Delete relaxation requires its input problem to be normalized, so the definedness
  translation (which sits just before relaxation in the pipeline) must preserve
  normalization. It keeps action parameters and objects untouched (typelessness is
  preserved), the added \<open>Defined_\<close> predicates inherit the \<open>\<omega>\<close>-typed argument types of the
  functions they track, and it maps preconditions/goal through \<open>map_formula\<close> inside a
  positive conjunctive prefix (so \<open>is_conj\<close> is preserved).\<close>

lemma is_conj_foldr_lits:
  "(\<forall>x\<in>set ats. is_lit_plus x) \<Longrightarrow> is_conj c \<Longrightarrow> is_conj (foldr (\<^bold>\<and>) ats c)"
  by (induction ats) auto

lemma is_conj_def_translate_fmla:
  "is_conj f \<Longrightarrow> is_conj (def_translate_fmla pfx f)"
  unfolding def_translate_fmla_def by (rule map_preserves_isconj)

lemma dt_ac_pre_is_conj:
  assumes "is_conj (ac_pre a)"
  shows "is_conj (ac_pre (def_translate_ac pfx a))"
  using assms
  by (cases "(pfx, a)" rule: def_translate_ac.cases)
     (simp add: Let_def is_conj_def_translate_fmla
      is_conj_foldr_lits[OF _ is_conj_def_translate_fmla])

lemma dt_ac_params_eq: "ac_params (def_translate_ac pfx a) = ac_params a"
  by (cases "(pfx, a)" rule: def_translate_ac.cases) (simp add: Let_def)

lemma def_predicate_decl_argTs:
  "predicate_decl.argTs (def_predicate_decl pfx d) = function_decl.argTs d"
  by (simp add: def_predicate_decl_def split: function_decl.splits func.splits)

lemma (in ast_classical_domain) dt_typeless_dom:
  "typeless_classical_domain \<Longrightarrow> ast_classical_domain.typeless_classical_domain def_translate_dom"
  unfolding ast_classical_domain.typeless_classical_domain_def[where ?D=def_translate_dom]
            typeless_classical_domain_def
            domain_signature.typeless_domain_signature_def
            def_translate_dom_sel
  by (auto simp: dt_ac_params_eq def_predicate_decl_argTs)

lemma (in ast_classical_problem) def_translate_normalized:
  assumes "normalized_prob"
  shows "ast_classical_problem.normalized_prob def_translate_prob"
proof -
  from assms have tp: "typeless_classical_problem" and pn: "prec_normed_dom"
    and gc: "is_conj (goal P)"
    unfolding normalized_prob_def by auto
  have td: "typeless_classical_domain"
    using tp unfolding typeless_classical_problem_def by simp
  have 1: "ast_classical_domain.typeless_classical_domain (domain def_translate_prob)"
    using dt_typeless_dom[OF td] by (simp add: def_translate_prob_sel)
  have 2: "\<forall>(n,T)\<in>set (objects def_translate_prob). T = \<omega>"
    using tp unfolding typeless_classical_problem_def by (simp add: def_translate_prob_sel)
  have tprob: "ast_classical_problem.typeless_classical_problem def_translate_prob"
    unfolding ast_classical_problem.typeless_classical_problem_def using 1 2 by simp
  have prec: "ast_classical_domain.prec_normed_dom (domain def_translate_prob)"
    unfolding ast_classical_domain.prec_normed_dom_def def_translate_prob_sel def_translate_dom_sel
    using pn[unfolded prec_normed_dom_def] dt_ac_pre_is_conj by auto
  have goal: "is_conj (goal def_translate_prob)"
    using gc is_conj_def_translate_fmla by (simp add: def_translate_prob_sel)
  show ?thesis
    unfolding ast_classical_problem.normalized_prob_def
    using tprob prec goal by simp
qed
end

