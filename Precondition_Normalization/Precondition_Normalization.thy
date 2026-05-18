theory Precondition_Normalization
  imports Precondition_Normalization_Locales
begin

section \<open> Precondition Normalization Well-Formedness Proofs \<close>

subsection \<open> Action splitting properties \<close>

lemma (in ast_classical_domain) split_ac_len:
  "length (split_ac ac) = length (dnf_list (ac_pre ac))"
  "length (split_ac_names ac) = length (dnf_list (ac_pre ac))"
  unfolding split_ac_def split_ac_names_def n_clauses_def by simp_all

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

lemma (in ast_classical_domain) split_pres: "map ac_pre (split_ac a) = dnf_list (ac_pre a)"
  unfolding split_ac_def Let_def apply (rule set_n_pre_mapsel)
  unfolding split_ac_names_def n_clauses_def by simp

lemma (in ast_classical_domain) split_ac_sel:
  assumes "a' \<in> set (split_ac a)"
  shows
    "\<exists>i < length (split_ac a). ac_name a' = padl_lit split_pre_pad (String.implode (show i)) + ac_name a"
    "ac_params a' = ac_params a"
    "ac_pre a' \<in> set (dnf_list (ac_pre a))"
    "ac_eff a' = ac_eff a"
proof -
  from assms show "ac_params a' = ac_params a" "ac_eff a' = ac_eff a"
    unfolding split_ac_def Let_def by auto
  from assms obtain i where i: "i < length (split_ac a)" "a' = split_ac a ! i"
    using in_set_conv_nth by metis
  from i show "ac_pre a' \<in> set (dnf_list (ac_pre a))"
    using split_ac_nth split_ac_len(1) by simp
  from i show "\<exists>i < length (split_ac a). ac_name a' = padl_lit split_pre_pad (String.implode (show i)) + ac_name a"
    using split_ac_nth split_ac_len(1) by auto
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
  hence "atoms (ac_pre a') \<subseteq> atoms (ac_pre a)" using split_ac_sel(3) dnf_list_atoms by metis
  hence fmla_wf: "d4.wf_fmla tyt (ac_pre a')" if "wf_fmla tyt (ac_pre a)" for tyt
    using that wf_fmla_alt by blast

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

end
