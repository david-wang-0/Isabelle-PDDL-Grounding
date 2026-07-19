theory Definedness_Translation
  imports Grounding_Common.PDDL_Normalization
    Grounding_Common.Formula_Utils
    Grounding_Utils.String_Utils
    "Analysis_Free_Base.Well_Formedness"
begin

text \<open>Reusable, AST-agnostic core of definedness translation: convert reflexive numeric equalities
  into propositional \<open>Defined_\<close> atoms, collect the PNEs read/written by an effect, and the
  signature-fresh prefix. Mirrors the classical Classical_Definedness_Translation stage; the action/domain/problem
  translation and the \<open>*_dt\<close> locales stay in \<open>Classical_Grounding.Classical_Definedness_Translation_Locales\<close>.\<close>

subsection \<open>Name generation\<close>

definition pne_to_def_atom :: "name \<Rightarrow> 'ent primitive_numeric_expression \<Rightarrow> 'ent atom" where
  "pne_to_def_atom pfx p = (case p of PNE (Func n) args \<Rightarrow> predAtm (Pred (pfx + n)) args)"

fun def_translate_atom :: "name \<Rightarrow> 'ent atom \<Rightarrow> 'ent atom" where
  "def_translate_atom pfx (numericEqAtm (FunctionExpr p) (FunctionExpr p')) =
    (if p = p' then pne_to_def_atom pfx p else numericEqAtm (FunctionExpr p) (FunctionExpr p'))"
| "def_translate_atom pfx a = a"

definition def_translate_fmla :: "name \<Rightarrow> 'ent atom formula \<Rightarrow> 'ent atom formula" where
  "def_translate_fmla pfx f = map_formula (def_translate_atom pfx) f"

subsection \<open>Collecting the PNEs of an effect\<close>

definition rhs_pnes_num_eff :: "'ent numeric_effect \<Rightarrow> 'ent primitive_numeric_expression list" where
  "rhs_pnes_num_eff eff = (case eff of
    NumericEffect _ _ e \<Rightarrow> enumerate_primitive_numeric_expressions e)"

fun rhs_pnes_eff :: "'ent ast_effect \<Rightarrow> 'ent primitive_numeric_expression list" where
  "rhs_pnes_eff (Effect _ _ ne) = concat (map rhs_pnes_num_eff ne)"

definition lhs_pnes_num_eff :: "'ent numeric_effect \<Rightarrow> 'ent primitive_numeric_expression list" where
  "lhs_pnes_num_eff eff = (case eff of
    NumericEffect numeric_effect_op.Assign p _ \<Rightarrow> [p] | _ \<Rightarrow> [])"

fun lhs_pnes_eff :: "'ent ast_effect \<Rightarrow> 'ent primitive_numeric_expression list" where
  "lhs_pnes_eff (Effect _ _ ne) = concat (map lhs_pnes_num_eff ne)"

subsection \<open>Definedness predicate declarations and initial-state facts\<close>

definition def_predicate_decl :: "name \<Rightarrow> function_decl \<Rightarrow> predicate_decl" where
  "def_predicate_decl pfx d = (case d of FuncDecl (Func n) ts \<Rightarrow> PredDecl (Pred (pfx + n)) ts)"

text \<open>Extract from an initial-state function assignment \<open>(= (f args) c)\<close> the definedness fact
  \<open>Defined_f args\<close>.\<close>

definition init_def_fact :: "name \<Rightarrow> object atom formula \<Rightarrow> object atom formula option" where
  "init_def_fact pfx f = (case f of
      Atom (numericEqAtm (FunctionExpr l) (ConstantExpr _)) \<Rightarrow> Some (Atom (pne_to_def_atom pfx l))
    | _ \<Rightarrow> None)"

subsection \<open>Domain-fresh prefix\<close>

context domain_signature begin

text \<open>A prefix fresh w.r.t. the declared predicate names, extended with the \<open>Defined_\<close> token.
  Freshness follows from \<open>safe_prefix_correct\<close>.\<close>

definition "def_prefix \<equiv> safe_prefix pred_names + STR ''Defined_''"

end

subsection \<open>PNEs collected from a well-formed effect are well-formed\<close>

lemma (in domain_signature) wf_numexpr_enum_pne:
  assumes "wf_numeric_expression tyt e"
    and "q \<in> set (enumerate_primitive_numeric_expressions e)"
  shows "wf_primitive_numeric_expression tyt q"
  using assms by (induction e) auto

lemma (in domain_signature) rhs_pne_wf:
  assumes "wf_effect tyt (Effect ads dls neffs)"
    and "q \<in> set (rhs_pnes_eff (Effect ads dls neffs))"
  shows "wf_primitive_numeric_expression tyt q"
proof -
  from assms(2) obtain ne where ne: "ne \<in> set neffs" "q \<in> set (rhs_pnes_num_eff ne)"
    by auto
  obtain opr l r where ner: "ne = NumericEffect opr l r" by (cases ne)
  with ne have qin: "q \<in> set (enumerate_primitive_numeric_expressions r)"
    by (simp add: rhs_pnes_num_eff_def)
  from assms(1) ne ner have "wf_numeric_expression tyt r" by auto
  thus ?thesis using qin wf_numexpr_enum_pne by blast
qed

lemma (in domain_signature) lhs_pne_wf:
  assumes "wf_effect tyt (Effect ads dls neffs)"
    and "q \<in> set (lhs_pnes_eff (Effect ads dls neffs))"
  shows "wf_primitive_numeric_expression tyt q"
proof -
  from assms(2) obtain ne where ne: "ne \<in> set neffs" "q \<in> set (lhs_pnes_num_eff ne)"
    by auto
  obtain opr l r where ner: "ne = NumericEffect opr l r" by (cases ne)
  with ne(2) have "q = l" by (cases opr) (auto simp: lhs_pnes_num_eff_def)
  moreover from assms(1) ne ner have "wf_primitive_numeric_expression tyt l" by auto
  ultimately show ?thesis by simp
qed

end
