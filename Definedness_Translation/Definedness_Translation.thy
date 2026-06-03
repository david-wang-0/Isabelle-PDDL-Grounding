theory Definedness_Translation
  imports Definedness_Translation_Locales
begin

section ‹Definedness Translation Well-Formedness Proofs›

subsection ‹PNE preservation under the atom/formula translation›

lemma def_translate_atom_pnes:
  "set (atom_enumerate_primitive_numeric_expressions (def_translate_atom pfx a))
   ⊆ set (atom_enumerate_primitive_numeric_expressions a)"
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
   ⊆ set (formula_enumerate_primitive_numeric_expressions f)"
proof (induction f)
  case (Atom a)
  then show ?case unfolding def_translate_fmla_def by (simp add: def_translate_atom_pnes)
qed (auto simp: def_translate_fmla_def)

subsection ‹Names of the generated ‹Defined_› predicates›

fun func_nm :: "func ⇒ name" where "func_nm (Func n) = n"

definition "fdecl_nm fd ≡ func_nm (function_decl.func fd)"

lemma inj_func_nm: "inj func_nm"
  by (rule injI) (metis func_nm.simps func.exhaust)

lemma def_predicate_decl_alt:
  "def_predicate_decl pfx fd = PredDecl (Pred (pfx + fdecl_nm fd)) (function_decl.argTs fd)"
  by (cases fd; cases "function_decl.func fd") (auto simp: def_predicate_decl_def fdecl_nm_def)

lemma def_pred_name: "pred (def_predicate_decl pfx fd) = Pred (pfx + fdecl_nm fd)"
  by (simp add: def_predicate_decl_alt)

subsection ‹PNEs collected from a well-formed effect are well-formed›

lemma (in domain_signature) wf_numexpr_enum_pne:
  assumes "wf_numeric_expression tyt e"
    and "q ∈ set (enumerate_primitive_numeric_expressions e)"
  shows "wf_primitive_numeric_expression tyt q"
  using assms by (induction e) auto

lemma (in domain_signature) rhs_pne_wf:
  assumes "wf_effect tyt (Effect ads dls neffs)"
    and "q ∈ set (rhs_pnes_eff (Effect ads dls neffs))"
  shows "wf_primitive_numeric_expression tyt q"
proof -
  from assms(2) obtain ne where ne: "ne ∈ set neffs" "q ∈ set (rhs_pnes_num_eff ne)"
    by auto
  obtain opr l r where ner: "ne = NumericEffect opr l r" by (cases ne)
  with ne have qin: "q ∈ set (enumerate_primitive_numeric_expressions r)"
    by (simp add: rhs_pnes_num_eff_def)
  from assms(1) ne ner have "wf_numeric_expression tyt r" by auto
  thus ?thesis using qin wf_numexpr_enum_pne by blast
qed

lemma (in domain_signature) lhs_pne_wf:
  assumes "wf_effect tyt (Effect ads dls neffs)"
    and "q ∈ set (lhs_pnes_eff (Effect ads dls neffs))"
  shows "wf_primitive_numeric_expression tyt q"
proof -
  from assms(2) obtain ne where ne: "ne ∈ set neffs" "q ∈ set (lhs_pnes_num_eff ne)"
    by auto
  obtain opr l r where ner: "ne = NumericEffect opr l r" by (cases ne)
  with ne have "q = l" by (simp add: lhs_pnes_num_eff_def)
  moreover from assms(1) ne ner have "wf_primitive_numeric_expression tyt l" by auto
  ultimately show ?thesis by simp
qed

subsection ‹Signature monotonicity of the translated domain›

context wf_ast_classical_domain_dt begin

text ‹Types, functions and constants are untouched, so every constant derived
  from them is preserved.›

lemma dt_subtype_rel: "dt.subtype_rel = subtype_rel"
  unfolding dt.subtype_rel_def subtype_rel_def by simp

lemma dt_is_of_type: "dt.is_of_type = is_of_type"
  apply (rule ext)+
  unfolding dt.is_of_type_def is_of_type_def dt.of_type_def of_type_def dt_subtype_rel by simp

lemma dt_func_sig: "dt.func_sig = func_sig"
  unfolding dt.func_sig_def func_sig_def by simp

lemma dt_constT: "dt.constT = constT"
  unfolding dt.constT_def constT_def by simp

lemma dt_type_wf: "wf_type T ⟹ dt.wf_type T"
  using def_translate_dom_sel(1) by (cases T) simp

text ‹The new ‹Defined_› predicate names are fresh and pairwise distinct.›

lemma def_prefix_fresh: "def_prefix + n ∉ set pred_names"
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
    fix x y assume xy: "x ∈ set (functions D)" "y ∈ set (functions D)" "fdecl_nm x = fdecl_nm y"
    from xy(3) have "function_decl.func x = function_decl.func y"
      using inj_func_nm by (auto simp: fdecl_nm_def dest: injD)
    thus "x = y" using xy(1,2) fi by (auto dest: inj_onD)
  qed
  with d show ?thesis by (simp add: distinct_map)
qed

lemma dt_preds_dist: "distinct (map pred (predicates DT))"
proof -
  let ?new = "map (def_predicate_decl def_prefix) (functions D)"
  have "map pred ?new = map (λfd. Pred (def_prefix + fdecl_nm fd)) (functions D)"
    by (simp add: def_pred_name)
  hence dist_new: "distinct (map pred ?new)"
    using fdecl_nm_dist
    by (simp add: distinct_map inj_on_def predicate.expand inj_prepend[unfolded inj_def])
  have disj: "set (map pred (predicates D)) ∩ set (map pred ?new) = {}"
  proof -
    have fr: "Pred (def_prefix + fdecl_nm fd) ∉ pred ` set (predicates D)" for fd
    proof
      assume "Pred (def_prefix + fdecl_nm fd) ∈ pred ` set (predicates D)"
      then obtain pd where "pd ∈ set (predicates D)" "pred pd = Pred (def_prefix + fdecl_nm fd)" by auto
      hence "def_prefix + fdecl_nm fd ∈ set pred_names" by (force simp: predicate.expand)
      thus False using def_prefix_fresh by blast
    qed
    show ?thesis
    proof (intro equals0I)
      fix y assume y: "y ∈ set (map pred (predicates D)) ∩ set (map pred ?new)"
      hence yp: "y ∈ pred ` set (predicates D)" by simp
      from y obtain xb where "xb ∈ set (functions D)" "y = Pred (def_prefix + fdecl_nm xb)"
        by (auto simp: def_pred_name)
      thus False using yp fr by blast
    qed
  qed
  show ?thesis using wf_D_sig(2) dist_new disj by simp
qed

text ‹The existing signature is preserved; declared functions induce a
  ‹Defined_› predicate with the same argument types.›

lemma dt_sig:
  assumes "sig p = Some Ts" shows "dt.sig p = Some Ts"
proof -
  have "PredDecl p Ts ∈ set (predicates D)" using assms sig_Some by simp
  hence "PredDecl p Ts ∈ set (predicates DT)" by simp
  thus ?thesis using dt.pred_resolve[OF dt_preds_dist] by blast
qed

lemma dt_sig_def_pred:
  assumes "FuncDecl (Func n) ts ∈ set (functions D)"
  shows "dt.sig (Pred (def_prefix + n)) = Some ts"
proof -
  have "PredDecl (Pred (def_prefix + n)) ts ∈ set (predicates DT)"
    using assms by (force simp: def_predicate_decl_def)
  thus ?thesis using dt.pred_resolve[OF dt_preds_dist] by blast
qed

text ‹The key lemma: a well-formed PNE maps to a well-formed ‹Defined_› atom.›

lemma pne_to_def_atom_wf:
  assumes "wf_primitive_numeric_expression tyt p"
  shows "dt.wf_atom tyt (pne_to_def_atom def_prefix p)"
proof (cases p)
  case [simp]: (PNE f args)
  obtain n where [simp]: "f = Func n" by (cases f)
  from assms obtain ts where ts: "func_sig (Func n) = Some ts"
    and m: "list_all2 (is_of_type tyt) args ts" by (auto split: option.splits)
  from ts have "FuncDecl (Func n) ts ∈ set (functions D)" using func_sig_Some by simp
  hence sig: "dt.sig (Pred (def_prefix + n)) = Some ts" using dt_sig_def_pred by simp
  from m have m': "list_all2 (dt.is_of_type tyt) args ts" using dt_is_of_type by metis
  have wfp: "dt.wf_pred_atom tyt (Pred (def_prefix + n), args)"
    apply (subst dt.wf_pred_atom.simps) using sig m' by (auto simp: option.case_cong)
  hence "dt.wf_atom tyt (predAtm (Pred (def_prefix + n)) args)"
    by (subst dt.wf_atom.simps) simp
  thus ?thesis by (simp add: pne_to_def_atom_def)
qed

subsection ‹Monotonicity of well-formedness under the bigger signature›

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

lemma dt_numexpr_wf: "wf_numeric_expression tyt e ⟹ dt.wf_numeric_expression tyt e"
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
qed (use assms in ‹auto simp: domain_signature.wf_atom.simps›)

lemma dt_fmla_wf: "wf_fmla tyt φ ⟹ dt.wf_fmla tyt φ"
  using dt_atom_wf co_fmla_wf by blast

lemma dt_fmla_atom_wf: "wf_fmla_atom tyt φ ⟹ dt.wf_fmla_atom tyt φ"
  using dt_atom_wf co_fmla_atom_wf by blast

lemma dt_numeric_effect_wf: "wf_numeric_effect tyt ne ⟹ dt.wf_numeric_effect tyt ne"
  using dt_pne_wf co_numeric_effect_wf by blast

lemma dt_eff_wf: "wf_effect tyt ε ⟹ dt.wf_effect tyt ε"
  using dt_atom_wf dt_pne_wf co_effect_wf by blast

subsection ‹Well-formedness of the translated atoms›

text ‹A ‹Defined_› atom built from a well-formed PNE is a well-formed fact.›

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
       (use wfa in ‹simp add: domain_signature.wf_atom.simps›)
  thus ?thesis by (simp add: pne_to_def_atom_def)
qed

lemma dt_def_translate_atom_wf:
  assumes "wf_atom tyt a"
  shows "dt.wf_atom tyt (def_translate_atom def_prefix a)"
proof (cases "∃p. a = numericEqAtm (FunctionExpr p) (FunctionExpr p)")
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

text ‹TODO: the remaining assembly lemmas are blocked by the ‹[simp]›
  selector ‹def_translate_dom_sel› dismantling the ‹dt.wf_…› heads (rewriting
  ‹predicates DT› inside them), so the locale ‹.simps› and the monotonicity
  helper lemmas no longer match. The fix is to drop ‹[simp]› from the selectors
  and thread them explicitly through the proofs above; the mathematical content
  (all signature-monotonicity lemmas, the key ‹pne_to_def_atom_wf›, ‹dt_atom_wf›,
  freshness and distinctness) is already established.›

lemma dt_def_translate_fmla_wf:
  assumes "wf_fmla tyt φ" shows "dt.wf_fmla tyt (def_translate_fmla def_prefix φ)"
  using assms unfolding def_translate_fmla_def
proof (induction φ)
  case (Atom a)
  show ?case using Atom.prems domain_signature.wf_fmla.simps(1) dt_def_translate_atom_wf by fastforce
next
  case Bot
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
next
  case (Not φ)
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
next
  case (And φ1 φ2)
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
next
  case (Or φ1 φ2)
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
next
  case (Imp φ1 φ2)
  thus ?case by (simp add: domain_signature.wf_fmla.simps)
qed

lemma dt_wf_fmla_foldr_conj:
  assumes "∀a∈set as. dt.wf_atom tyt a" and "dt.wf_fmla tyt base"
  shows "dt.wf_fmla tyt (foldr (❙∧) (map Atom as) base)"
  using assms by (induction as) (auto simp: domain_signature.wf_fmla.simps)

subsection ‹Well-formedness of a translated action›

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
    wf_ads: "∀ae∈set ads. wf_fmla_atom tyt ae" and
    wf_dls: "∀de∈set dls. wf_fmla_atom tyt de" and
    wf_neffs: "∀ne∈set neffs. wf_numeric_effect tyt ne"
    by auto
  ― ‹The new ‹Defined_› atoms collected from the effect are well-formed.›
  have rhs_wf: "dt.wf_atom tyt (pne_to_def_atom def_prefix q)"
    if "q ∈ set (rhs_pnes_eff (Effect ads dls neffs))" for q
    using rhs_pne_wf[OF wf_eff[unfolded e1] that] pne_to_def_atom_wf by blast
  have lhs_wf: "dt.wf_fmla_atom tyt (Atom (pne_to_def_atom def_prefix q))"
    if "q ∈ set (lhs_pnes_eff (Effect ads dls neffs))" for q
    using lhs_pne_wf[OF wf_eff[unfolded e1] that] pne_to_def_fmla_atom_wf by blast
  ― ‹The translated precondition is well-formed.›
  have pre_atoms_wf:
    "∀x∈set (map (pne_to_def_atom def_prefix) (remdups (rhs_pnes_eff (Effect ads dls neffs)))). dt.wf_atom tyt x"
    using rhs_wf by auto
  have base_wf: "dt.wf_fmla tyt (def_translate_fmla def_prefix pre)"
    using dt_def_translate_fmla_wf[OF wf_pre] .
  have new_pre_wf: "dt.wf_fmla tyt (foldr (❙∧)
      (map Atom (map (pne_to_def_atom def_prefix) (remdups (rhs_pnes_eff (Effect ads dls neffs)))))
      (def_translate_fmla def_prefix pre))"
    using dt_wf_fmla_foldr_conj[OF pre_atoms_wf base_wf] .
  ― ‹The translated effect is well-formed.›
  have new_ads_wf: "dt.wf_fmla_atom tyt ae"
    if "ae ∈ set (map Atom (map (pne_to_def_atom def_prefix)
                  (remdups (lhs_pnes_eff (Effect ads dls neffs)))) @ ads)" for ae
  proof -
    from that consider
        "ae ∈ set (map Atom (map (pne_to_def_atom def_prefix)
                   (remdups (lhs_pnes_eff (Effect ads dls neffs)))))"
      | "ae ∈ set ads" by auto
    thus ?thesis
    proof cases
      case 1
      then obtain q where "q ∈ set (lhs_pnes_eff (Effect ads dls neffs))"
        "ae = Atom (pne_to_def_atom def_prefix q)" by auto
      thus ?thesis using lhs_wf by blast
    next
      case 2
      thus ?thesis using wf_ads dt_fmla_atom_wf by blast
    qed
  qed
  have new_dls_wf: "∀de∈set dls. dt.wf_fmla_atom tyt de" using wf_dls dt_fmla_atom_wf by blast
  have new_neffs_wf: "∀ne∈set neffs. dt.wf_numeric_effect tyt ne"
    using wf_neffs dt_numeric_effect_wf by blast
  have eff_wf: "dt.wf_effect tyt (Effect (map Atom (map (pne_to_def_atom def_prefix)
      (remdups (lhs_pnes_eff (Effect ads dls neffs)))) @ ads) dls neffs)"
    using new_ads_wf new_dls_wf new_neffs_wf by (subst dt.wf_effect.simps) blast
  ― ‹Assemble the translated action body and conclude.›
  have body_wf: "dt.wf_simple_action_body tyt (SimpleActionBody
      (foldr (❙∧) (map Atom (map (pne_to_def_atom def_prefix)
        (remdups (rhs_pnes_eff (Effect ads dls neffs))))) (def_translate_fmla def_prefix pre))
      (Effect (map Atom (map (pne_to_def_atom def_prefix)
        (remdups (lhs_pnes_eff (Effect ads dls neffs)))) @ ads) dls neffs))"
    unfolding dt.wf_simple_action_body.simps using new_pre_wf eff_wf by blast
  have head_dt: "dt.wf_action_head h"
    using head by (cases h) (simp_all add: dt.wf_action_head.simps)
  have dac: "def_translate_ac def_prefix a = SimpleActionSchema h (SimpleActionBody
      (foldr (❙∧) (map Atom (map (pne_to_def_atom def_prefix)
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

subsection ‹Well-formedness of the translated domain›

lemma dt_preds_wf: "list_all dt.wf_predicate_decl (predicates DT)"
proof -
  have orig: "list_all dt.wf_predicate_decl (predicates D)"
  proof (subst list_all_iff, intro ballI)
    fix pd assume "pd ∈ set (predicates D)"
    hence "wf_predicate_decl pd" using wf_D_sig(3) by (simp add: list_all_iff)
    thus "dt.wf_predicate_decl pd" using dt_type_wf by (cases pd) auto
  qed
  have new: "dt.wf_predicate_decl (def_predicate_decl def_prefix fd)"
    if "fd ∈ set (functions D)" for fd
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
    fix f assume "f ∈ set (functions DT)"
    hence "wf_function_decl f" using wf_D_sig(5) by simp
    thus "dt.wf_function_decl f" by (cases f) (auto intro: dt_type_wf)
  qed
  show "distinct (map fst (consts DT))"
    using wf_D_sig(6) by simp
  show "∀(n,y)∈set (consts DT). dt.wf_type y"
    using wf_D_sig(7) by (auto intro: dt_type_wf)
qed

lemma dt_acs_dist: "distinct (map ac_name (actions DT))"
  by (simp add: list.map_comp comp_def dt_ac_name wf_D(2))

theorem def_translate_dom_wf: "dt.wf_classical_domain"
  unfolding dt.wf_classical_domain_def
  using dt_dom_sig_wf dt_acs_dist dt_ac_wf wf_D(3)
  by (auto simp: list_all_iff)

end

subsection ‹Well-formedness of the translated problem›

context wf_ast_classical_problem_dt begin

theorem def_translate_prob_wf: "pt.wf_classical_problem"
proof -
  ― ‹The object typing environment is untouched by the translation.›
  have objT_eq: "pt.objT = objT"
    by (simp add: problem_signature.objT_def dt_constT)
  ― ‹Types are unchanged, so type well-formedness coincides.›
  have wf_type_eq: "pt.wf_type T ⟷ wf_type T" for T
    by (cases T) (simp add: domain_signature.wf_type.simps def_translate_prob_sel)
  ― ‹The problem signature stays well-formed: only fresh predicates were added.›
  have psig: "pt.wf_problem_signature"
    unfolding problem_signature.wf_problem_signature_def
  proof (intro conjI)
    show "pt.wf_domain_signature" using dt_dom_sig_wf by (simp add: def_translate_prob_sel)
    show "distinct (map fst (objects def_translate_prob) @ map fst (consts pt.D))"
      using wf_P_sig(2) by (simp add: def_translate_prob_sel)
    show "∀(n,y)∈set (objects def_translate_prob). pt.wf_type y"
      using wf_P_sig(3) by (simp add: def_translate_prob_sel wf_type_eq)
  qed
  ― ‹Every freshly generated init fact is a well-formed ‹Defined_› atom
      with a fresh predicate name.›
  have newfact: "dt.wf_fmla_atom objT g ∧ (∃n args. g = Atom (predAtm (Pred (def_prefix + n)) args))"
    if g_in: "g ∈ set (List.map_filter (init_def_fact def_prefix) (init P))" for g
  proof -
    from g_in obtain f where f: "f ∈ set (init P)" and idf: "init_def_fact def_prefix f = Some g"
      by (auto simp: set_map_filter)
    from idf obtain l c where fl: "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr c))"
      and g_eq: "g = Atom (pne_to_def_atom def_prefix l)"
      by (auto simp: init_def_fact_def split: formula.splits atom.splits numeric_expression.splits)
    have "wf_fmla_atom objT f ∨ wf_func_assign f" using f wf_P(4) by blast
    moreover have "¬ wf_fmla_atom objT f" using fl by simp
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
  ― ‹A well-formed declared predicate atom carries a declared predicate name.›
  have wf_pred_in_names: "predicate.name p ∈ set pred_names"
    if wf: "wf_fmla_atom objT (Atom (predAtm p vs))" for p vs
  proof -
    from wf have "wf_pred_atom objT (p, vs)" by simp
    then obtain Ts where "sig p = Some Ts" by (auto split: option.splits)
    hence "PredDecl p Ts ∈ set (predicates D)" using sig_Some by simp
    hence "p ∈ pred ` set (predicates D)" by force
    thus ?thesis by force
  qed
  ― ‹Hence the new init facts are disjoint from the original ones: their
      predicate names are fresh, while every original fact is either a declared
      predicate atom or a (non-predicate) function assignment.›
  have disj: "set (init P) ∩ set (List.map_filter (init_def_fact def_prefix) (init P)) = {}"
  proof (intro equals0I)
    fix g assume "g ∈ set (init P) ∩ set (List.map_filter (init_def_fact def_prefix) (init P))"
    hence gP: "g ∈ set (init P)"
      and gN: "g ∈ set (List.map_filter (init_def_fact def_prefix) (init P))" by auto
    from newfact[OF gN] obtain n args
      where gshape: "g = Atom (predAtm (Pred (def_prefix + n)) args)" by blast
    from gP wf_P(4) have "wf_fmla_atom objT g ∨ wf_func_assign g" by blast
    thus False
    proof
      assume "wf_fmla_atom objT g"
      hence "predicate.name (Pred (def_prefix + n)) ∈ set pred_names"
        using gshape wf_pred_in_names by blast
      hence "def_prefix + n ∈ set pred_names" by simp
      thus False using def_prefix_fresh by blast
    next
      assume "wf_func_assign g"
      thus False using gshape by simp
    qed
  qed
  ― ‹Function assignments stay well-formed under the bigger signature.›
  have pt_fa: "pt.wf_func_assign f" if "wf_func_assign f" for f
  proof -
    from that obtain l r where f: "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
      and wfl: "wf_primitive_numeric_expression objT l"
      by (cases f rule: wf_func_assign.cases) auto
    from wfl have "dt.wf_primitive_numeric_expression objT l" by (rule dt_pne_wf)
    thus ?thesis using f objT_eq by (simp add: problem_signature.wf_func_assign.simps)
  qed
  ― ‹The domain-signature notions coincide for the ‹pt› and ‹dt› views.›
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
    show "∀f∈set (init PT). pt.wf_fmla_atom pt.objT f ∨ pt.wf_func_assign f"
    proof (intro ballI)
      fix f assume "f ∈ set (init PT)"
      hence "f ∈ set (init P) ∨ f ∈ set (List.map_filter (init_def_fact def_prefix) (init P))"
        by (auto simp: def_translate_prob_sel)
      thus "pt.wf_fmla_atom pt.objT f ∨ pt.wf_func_assign f"
      proof
        assume "f ∈ set (init P)"
        with wf_P(4) have "wf_fmla_atom objT f ∨ wf_func_assign f" by blast
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
        assume "f ∈ set (List.map_filter (init_def_fact def_prefix) (init P))"
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

subsection ‹Well-formedness sublocale instantiations›

sublocale wf_ast_classical_domain_dt ⊆ dt: wf_ast_classical_domain DT
  using def_translate_dom_wf wf_ast_classical_domain.intro by simp

sublocale wf_ast_classical_problem_dt ⊆ pt: wf_ast_classical_problem PT
  using def_translate_prob_wf wf_ast_classical_problem.intro by simp

end

