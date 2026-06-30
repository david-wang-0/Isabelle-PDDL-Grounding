theory Classical_Precondition_Normalization
  imports Classical_Precondition_Normalization_Locales
begin

section \<open> Precondition Normalization Well-Formedness Proofs \<close>

subsection \<open> Structural lemmas about \<open>dnf_list\<close> \<close>

text \<open>\<open>dnf_list\<close> propagates a leftmost conjunctive-prefix atom into every
  output clause. This is the structural fact that lets \<open>is_def_explicated_conj\<close>
  be preserved across the DNF split: the upstream \<open>Classical_Definedness_Normalization\<close>
  step puts every PNE's definedness atom in the conj-prefix of the source
  formula, and DNF then carries each of those atoms into every clause.\<close>

lemma dnf_list_Atom_And:
  "dnf_list (Atom a \<^bold>\<and> f) = map (\<lambda>c. Atom a \<^bold>\<and> c) (dnf_list f)"
proof -
  have CL: "cnf_lists (nnf (\<^bold>\<not> (Atom a \<^bold>\<and> f)))
          = map (\<lambda>g. a\<inverse> # g) (cnf_lists (nnf (\<^bold>\<not> f)))"
    by simp
  have nc: "neg_conj_of_clause (a\<inverse> # c) = Atom a \<^bold>\<and> neg_conj_of_clause c" for c
    unfolding neg_conj_of_clause_def by simp
  have "dnf_list (Atom a \<^bold>\<and> f)
      = map neg_conj_of_clause (map (\<lambda>g. a\<inverse> # g) (cnf_lists (nnf (\<^bold>\<not> f))))"
    unfolding dnf_list_def by (subst CL) rule
  also have "... = map (\<lambda>g. Atom a \<^bold>\<and> neg_conj_of_clause g) (cnf_lists (nnf (\<^bold>\<not> f)))"
    by (simp add: nc)
  also have "... = map (\<lambda>c. Atom a \<^bold>\<and> c) (map neg_conj_of_clause (cnf_lists (nnf (\<^bold>\<not> f))))"
    by simp
  finally show ?thesis unfolding dnf_list_def .
qed

lemma conj_atom_prefix_dnf_list:
  assumes "c \<in> set (dnf_list f)" "a \<in> set (conj_atom_prefix f)"
  shows "a \<in> set (conj_atom_prefix c)"
  using assms
proof (induction f arbitrary: c rule: conj_atom_prefix.induct)
  case (1 a' f)
  from "1.prems"(1) obtain c' where c': "c' \<in> set (dnf_list f)" "c = Atom a' \<^bold>\<and> c'"
    unfolding dnf_list_Atom_And by auto
  from "1.prems"(2) consider "a = a'" | "a \<in> set (conj_atom_prefix f)" by auto
  thus ?case
  proof cases
    case 1 thus ?thesis using c'(2) by simp
  next
    case 2
    hence "a \<in> set (conj_atom_prefix c')"
      using "1.IH" c'(1) by blast
    thus ?thesis using c'(2) by simp
  qed
qed simp_all

lemma formula_enum_pnes_dnf_list_subset:
  assumes "c \<in> set (dnf_list f)"
  shows "set (formula_enumerate_primitive_numeric_expressions c)
       \<subseteq> set (formula_enumerate_primitive_numeric_expressions f)"
proof -
  have "atoms c \<subseteq> atoms f" using assms dnf_list_atoms by fast
  thus ?thesis
    by (auto simp: set_formula_enumerate_primitive_numeric_expressions_conv)
qed

text \<open>Under \<open>is_def_explicated_conj\<close>, every clause of \<open>dnf_list\<close> carries the
  full PNE set: each clause inherits the definedness atoms from the conj-prefix
  via \<open>conj_atom_prefix_dnf_list\<close>, and each such atom enumerates one PNE of the
  source formula.\<close>

lemma formula_enum_pnes_dnf_list_def_explicated:
  assumes "is_def_explicated_conj f" "c \<in> set (dnf_list f)"
  shows "set (formula_enumerate_primitive_numeric_expressions c)
       = set (formula_enumerate_primitive_numeric_expressions f)"
proof
  show "set (formula_enumerate_primitive_numeric_expressions c)
      \<subseteq> set (formula_enumerate_primitive_numeric_expressions f)"
    using assms(2) formula_enum_pnes_dnf_list_subset by blast
next
  show "set (formula_enumerate_primitive_numeric_expressions f)
      \<subseteq> set (formula_enumerate_primitive_numeric_expressions c)"
  proof
    fix p assume "p \<in> set (formula_enumerate_primitive_numeric_expressions f)"
    with assms(1) have "numericEqAtm (FunctionExpr p) (FunctionExpr p)
                          \<in> set (conj_atom_prefix f)"
      unfolding is_def_explicated_conj_def by blast
    with assms(2) have
      "numericEqAtm (FunctionExpr p) (FunctionExpr p) \<in> set (conj_atom_prefix c)"
      by (auto dest: conj_atom_prefix_dnf_list) 
    hence "numericEqAtm (FunctionExpr p) (FunctionExpr p) \<in> atoms c"
      by (induction c rule: conj_atom_prefix.induct) auto
    thus "p \<in> set (formula_enumerate_primitive_numeric_expressions c)"
      unfolding set_formula_enumerate_primitive_numeric_expressions_conv
      by force
  qed
qed

lemma is_def_explicated_conj_dnf_list:
  assumes "is_def_explicated_conj f" "c \<in> set (dnf_list f)"
  shows "is_def_explicated_conj c"
  unfolding is_def_explicated_conj_def
proof
  fix p assume "p \<in> set (formula_enumerate_primitive_numeric_expressions c)"
  hence "p \<in> set (formula_enumerate_primitive_numeric_expressions f)"
    using formula_enum_pnes_dnf_list_def_explicated[OF assms] by blast
  with assms(1) have "numericEqAtm (FunctionExpr p) (FunctionExpr p)
                        \<in> set (conj_atom_prefix f)"
    unfolding is_def_explicated_conj_def by blast
  with assms(2) show
    "numericEqAtm (FunctionExpr p) (FunctionExpr p) \<in> set (conj_atom_prefix c)"
    using conj_atom_prefix_dnf_list by fast
qed

subsection \<open> Action splitting properties \<close>

lemma (in ast_classical_domain) split_ac_names_length:
  "length (split_ac_names ac) = length (dnf_list (ac_pre ac))"
  unfolding split_ac_names_def length_map n_clauses_def by simp

lemma (in ast_classical_domain) split_ac_length:
  "length (split_ac ac) = length (dnf_list (ac_pre ac))"
  unfolding split_ac_def
  unfolding length_map2
  unfolding split_ac_names_length
  by force

lemma (in ast_classical_domain) split_ac_nth:
  assumes "i < length (dnf_list (ac_pre ac))"
  shows "split_ac ac ! i =
    SimpleActionSchema
      (ActionHead (padl_lit split_pre_pad (String.implode (show i)) + ac_name ac) (ac_params ac))
      (SimpleActionBody (dnf_list (ac_pre ac) ! i) (ac_eff ac))"
  using assms unfolding split_ac_def split_ac_names_def n_clauses_def
  apply (induction ac rule: ast_classical_action_schema_induct_unfold)
  by (simp add: padl_lit_implode)

lemma (in ast_classical_domain4) p_ac:
  "ac' \<in> set (actions D4) \<longleftrightarrow> (\<exists>ac \<in> set (actions D). ac' \<in> set (split_ac ac))"
  unfolding split_dom_sel split_acs_def by simp

lemma (in ast_classical_domain) split_pres:
  "map ac_pre (split_ac a) = dnf_list (ac_pre a)"
  unfolding split_ac_def
  apply (rule set_n_pre_mapsel)
  using split_ac_names_length by simp

lemma (in ast_classical_domain) split_ac_sel:
  assumes "a' \<in> set (split_ac a)"
  shows
    "\<exists>i < length (split_ac a). ac_name a' = padl_lit split_pre_pad (String.implode (show i)) + ac_name a"
    "ac_params a' = ac_params a"
    "ac_pre a' \<in> set (dnf_list (ac_pre a))"
    "ac_eff a' = ac_eff a"
proof -
  from assms show "ac_params a' = ac_params a" "ac_eff a' = ac_eff a"
    unfolding split_ac_def by auto
  from assms obtain i where i: "i < length (split_ac a)" "a' = split_ac a ! i"
    using in_set_conv_nth by metis
  from i show "ac_pre a' \<in> set (dnf_list (ac_pre a))"
    using split_ac_nth[of i a] split_ac_length split_ac_names_length by auto
  from i show "\<exists>i < length (split_ac a). ac_name a' = padl_lit split_pre_pad (String.implode (show i)) + ac_name a"
    using split_ac_nth split_ac_names_length split_ac_length by auto
qed

subsection \<open> Output format \<close>

theorem (in ast_classical_problem4) prec_normed_ac:
  "\<forall>ac' \<in> set (split_ac ac). is_conj (ac_pre ac')"
  using split_ac_sel(3) dnf_list_conjs by auto

theorem (in ast_classical_problem4) prec_normed_dom:
  "d4.prec_normed_dom"
  unfolding d4.prec_normed_dom_def split_prob_sel split_dom_sel split_acs_def
  using prec_normed_ac by simp

subsection \<open> Well-formedness \<close>

context wf_ast_classical_domain4 begin

(* generated action IDs are distinct *)
(* TODO: simplify; combine with split_ac_sel *)

lemma (in ast_classical_domain) split_names_prefix_length:
  assumes "ac \<in> set (actions D)" "n \<in> set (split_ac_names ac)"
  shows "\<exists>p. size p = split_pre_pad \<and> n = p + ac_name ac"
proof -
  from assms(2)[unfolded split_ac_names_def] obtain p::String.literal where
    pin: "p \<in> set (distinct_strings_lit (n_clauses ac))" and
    n: "n = (padl_lit split_pre_pad p) + ac_name ac"
    by auto

  have "n_clauses ac \<le> max_n_clauses"
    using max_n_clauses_def assms(1) by simp
  hence "size p \<le> split_pre_pad"
    using pin split_pre_pad_def distinct_strings_lit_max_size by simp
  hence "size (padl_lit split_pre_pad p) = split_pre_pad"
    using padl_lit_size by blast
  thus ?thesis using n by blast
qed

lemma (in ast_classical_domain) split_names_distinct:
  shows "distinct (split_ac_names ac)"
proof -
  have "split_ac_names ac =
    map (\<lambda>p. p + ac_name ac) (map (padl_lit split_pre_pad) (distinct_strings_lit (n_clauses ac)))"
    unfolding split_ac_names_def by simp
  thus ?thesis using distinct_strings_padl_lit append_r_distinct_lit by metis
qed

lemma (in wf_ast_classical_domain) split_names_disjoint:
  assumes "ac \<in> set (actions D)" "ac' \<in> set (actions D)" "ac_name ac \<noteq> ac_name ac'"
  shows "set (split_ac_names ac) \<inter> set (split_ac_names ac') = {}"
  apply (unfold disjoint_iff_not_equal)
  using assms split_names_prefix_length
  using append_eq_append_conv_lit by metis

(* TODO generalize to Utils:
  distinct xs \<Longrightarrow> x \<noteq> y; \<in> set xs \<longrightarrow> f x \<inter> f y = {} \<Longrightarrow> distinct (removeAll ... *)
lemma (in wf_ast_classical_domain) split_names_dist_nonempty:
  "distinct (removeAll [] (map split_ac_names (actions D)))"
proof -
  have "distinct (removeAll [] (map split_ac_names as))"
    if "distinct (map ac_name as)" "set as \<subseteq> set (actions D)" for as
    using that
  proof (induction as)
    case (Cons a as)
    thus ?case proof (cases "split_ac_names a = []")
      case False

      from Cons.prems have ain: "\<forall>a' \<in> set as. a' \<in> set (actions D)" "a \<in> set (actions D)" by auto

      from Cons that have "\<forall>n \<in> set (map ac_name as). ac_name a \<noteq> n" by auto
      hence "\<forall>a' \<in> set as. ac_name a' \<noteq> ac_name a" by auto
      with ain have "\<forall>a' \<in> set as. set (split_ac_names a) \<inter> set (split_ac_names a') = {}"
        using split_names_disjoint by blast
      hence "\<forall>s \<in> set (removeAll [] (map split_ac_names as)). set (split_ac_names a) \<inter> set s = {}" by auto
      with False have "split_ac_names a \<notin> set (removeAll [] (map split_ac_names as))" by blast
      then show ?thesis using False Cons by simp
    qed (simp add: Cons)

  qed simp
  thus ?thesis using wf_D by simp
qed

lemma (in wf_ast_classical_domain) split_names_disjoint2:
  assumes
    "xs \<in> set (map split_ac_names (actions D))"
    "ys \<in> set (map split_ac_names (actions D))"
    "xs \<noteq> ys"
  shows "set xs \<inter> set ys = {}"
proof -
  from assms obtain x y where
    xy: "xs = split_ac_names x"  "x \<in> set (actions D)"
        "ys = split_ac_names y"  "y \<in> set (actions D)" by auto
  hence "x \<noteq> y" using assms(3) by blast
  hence "ac_name x \<noteq> ac_name y" using wf_D xy
    by (meson distinct_map_eq)
  thus ?thesis
    using split_names_disjoint xy by simp
qed

lemma (in ast_classical_domain4) p_ac_names:
  "map ac_name (actions D4) = concat (map split_ac_names (actions D))"
proof -
  have l: "length (split_ac_names ac) = length (dnf_list (ac_pre ac))" for ac
    unfolding split_ac_names_def n_clauses_def by simp

  have "map ac_name (actions D4) = concat
      (map (map ac_name) (map split_ac (actions D)))"
    unfolding split_dom_sel split_acs_def
    using map_concat by metis
  also have "... = concat
      (map (map ac_name \<circ> split_ac) (actions D))" by simp
  also have "... = concat (map split_ac_names (actions D))"
    unfolding split_ac_def comp_def
    using set_n_pre_mapsel(1) l by simp
  finally show ?thesis .
qed

lemma split_ac_names_dist:
  "distinct (map ac_name (actions D4))"
  unfolding p_ac_names distinct_concat_iff
  using split_names_dist_nonempty split_names_distinct split_names_disjoint2 by auto

(* action well-formedness *)

lemma p_actions_wf: "list_all d4.wf_classical_action_schema (actions D4)"
proof (subst list_all_iff, intro ballI)
  fix a' assume assm: "a' \<in> set (actions D4)"
  then obtain a where a: "a \<in> set (actions D)" "a' \<in> set (split_ac a)" using p_ac by auto
  have atoms_sub: "atoms (ac_pre a') \<subseteq> atoms (ac_pre a)"
    using split_ac_sel(3)[OF a(2)] dnf_list_atoms by fast
  have pnes_sub: "set (formula_enumerate_primitive_numeric_expressions (ac_pre a'))
                \<subseteq> set (formula_enumerate_primitive_numeric_expressions (ac_pre a))"
    using split_ac_sel(3)[OF a(2)] formula_enum_pnes_dnf_list_subset by blast
  have fmla_wf: "d4.wf_fmla tyt (ac_pre a')" if "wf_fmla tyt (ac_pre a)" for tyt
    apply (rule d4.wf_fmlaI)
    using wf_fmla_imp_wf_pred_atom[OF that] wf_fmla_imp_eqs_def[OF that]
          wf_fmla_imp_wf_pnes[OF that] atoms_sub pnes_sub
    by blast+

  have ac_tyt: "ac_tyt a' = ac_tyt a"
    using split_ac_sel[OF a(2)] ac_tyt_def by simp

  have "d4.wf_classical_action_schema a'" if "wf_classical_action_schema a"
    using that unfolding wf_classical_action_schema_alt
    using split_ac_sel(2-)[OF a(2)] fmla_wf ac_tyt by simp

  thus "d4.wf_classical_action_schema a'" using a(1) wf_D by simp
qed

theorem (in wf_ast_classical_domain4) split_dom_wf: "d4.wf_classical_domain"
  unfolding d4.wf_classical_domain_def
  using wf_D split_ac_names_dist p_actions_wf
  unfolding list_all_iff split_dom_sel by argo

theorem (in wf_ast_classical_problem4) split_prob_wf: "p4.wf_classical_problem"
  unfolding p4.wf_classical_problem_def split_prob_sel
  using wf_P split_dom_wf by simp_all

end

sublocale wf_ast_classical_domain4 \<subseteq> wf_ast_classical_domain D4
  using split_dom_wf wf_ast_classical_domain.intro by simp

sublocale wf_ast_classical_problem4 \<subseteq> p4_wf: wf_ast_classical_problem P4
  using split_prob_wf wf_ast_classical_problem.intro by simp_all

subsection \<open>Precondition normalization preserves \<open>def_explicated_conj\<close>\<close>

text \<open>With the input domain already \<open>def_explicated_conj\<close>, every clause of
  \<open>dnf_list (ac_pre a)\<close> inherits the definedness atoms via
  \<open>is_def_explicated_conj_dnf_list\<close>, so the property is preserved by the
  split.\<close>

lemma (in wf_ast_classical_domain4) def_explicated_conj_split_dom:
  "ast_classical_domain.def_explicated_conj_dom D4"
  unfolding ast_classical_domain.def_explicated_conj_dom_def
proof (intro ballI)
  fix a' assume "a' \<in> set (actions D4)"
  then obtain a where a: "a \<in> set (actions D)" "a' \<in> set (split_ac a)"
    using p_ac by auto
  from a(1) have "is_def_explicated_conj (ac_pre a)"
    using def_explicated_conj_dom unfolding def_explicated_conj_dom_def by blast
  thus "is_def_explicated_conj (ac_pre a')"
    using is_def_explicated_conj_dnf_list split_ac_sel(3)[OF a(2)] by blast
qed

lemma (in wf_ast_classical_problem4) def_explicated_conj_split_prob:
  "ast_classical_problem.def_explicated_conj_prob P4"
  unfolding ast_classical_problem.def_explicated_conj_prob_def
  using def_explicated_conj_split_dom
        def_explicated_conj_prob[unfolded def_explicated_conj_prob_def]
  by simp

sublocale wf_ast_classical_domain4 \<subseteq> p4_de: def_explicated_conj_domain D4
  by unfold_locales (rule def_explicated_conj_split_dom)

sublocale wf_ast_classical_problem4 \<subseteq> p4_de: def_explicated_conj_problem P4
  by unfold_locales (rule def_explicated_conj_split_prob)

end
