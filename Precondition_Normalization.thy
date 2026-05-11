theory Precondition_Normalization
imports "Classical_Planning.Classical_Abstract_Syntax"
    Normalization_Definitions String_Utils DNF Normalization_Definitions
begin

definition "n_clauses ac \<equiv> length (dnf_list (ac_pre ac))"

context ast_domain begin

definition "max_n_clauses \<equiv> Max (set (map n_clauses (actions D)))"
(* Technically, (max_n_clauses - 1) would be enough.*)
definition "split_pre_pad \<equiv> length (show max_n_clauses)"

fun (in -) set_n_pre :: " ast_action_schema \<Rightarrow> string \<Rightarrow> term atom formula \<Rightarrow> ast_action_schema" where
  "set_n_pre (Action_Schema _ params _ eff) n pre
  = Action_Schema n params pre eff"

definition "split_ac_names ac \<equiv>
  map (\<lambda>prefix. padl split_pre_pad prefix @ ac_name ac)
    (distinct_strings (n_clauses ac))"

definition split_ac :: "ast_action_schema \<Rightarrow> ast_action_schema list" where
  "split_ac ac =
    (let clauses = dnf_list (ac_pre ac) in
    map2 (set_n_pre ac) (split_ac_names ac) clauses)"

definition "split_acs \<equiv> concat (map split_ac (actions D))"

definition "split_dom \<equiv>
  Domain
    (types D)
    (predicates D)
    (consts D)
    split_acs"

definition (in ast_problem) "split_prob \<equiv>
  Problem
    split_dom
    (objects P)
    (init P)
    (goal P)"

(* it's important to be able to convert a plan for the output problem into a plan for the input problem.
  The other direction is probably (hopefully?) not important. *)
fun restore_pa_split where
  "restore_pa_split (PAction n args) = PAction (drop split_pre_pad n) args"
abbreviation "restore_plan_split \<pi>s \<equiv> map restore_pa_split \<pi>s"

(* prec_normed_dom taken from here *)

end

section \<open> Precondition Normalization Proofs \<close>

text \<open> locale setup for simplified syntax \<close>

abbreviation (in ast_domain) (input) "D4 \<equiv> split_dom"
abbreviation (in ast_problem) (input) "P4 \<equiv> split_prob"

locale ast_domain4 = ast_domain
sublocale ast_domain4 \<subseteq> d4: ast_domain D4 .

locale wf_ast_domain4 = wf_ast_domain
sublocale wf_ast_domain4 \<subseteq> d4: ast_domain D4 .
sublocale wf_ast_domain4 \<subseteq> ast_domain4 .

locale ast_problem4 = ast_problem
sublocale ast_problem4 \<subseteq> p4: ast_problem P4 .
sublocale ast_problem4 \<subseteq> ast_domain4 D .

locale wf_ast_problem4 = wf_ast_problem
sublocale wf_ast_problem4 \<subseteq> p4 : ast_problem P4.
sublocale wf_ast_problem4 \<subseteq> ast_problem4 .
sublocale wf_ast_problem4 \<subseteq> wf_ast_domain4 D
  by unfold_locales

text \<open> Alternate definitions \<close>

(* probably unnecessary *)
lemma set_n_pre_alt: "set_n_pre ac n pre =
  Action_Schema n (ac_params ac) pre (ac_eff ac)"
  by (cases ac) simp

(* probably unnecessary *)
lemma set_n_pre_sel [simp]:
  "ac_name (set_n_pre ac n pre) = n"
  "ac_params (set_n_pre ac n pre) = ac_params ac"
  "ac_pre (set_n_pre ac n pre) = pre"
  "ac_eff (set_n_pre ac n pre) = ac_eff ac"
  using set_n_pre_alt by simp_all

lemma (in -) set_n_pre_mapsel:
  assumes "length ns = length pres"
  shows
    "map ac_name (map2 (set_n_pre ac) ns pres) = ns"
    (*"map ac_params (map2 (set_n_pre ac) ns pres) = replicate (n_clauses ac) (ac_params ac)" *)
    "map ac_pre (map2 (set_n_pre ac) ns pres) = pres"
    (*"map ac_eff (map2 (set_n_pre ac) ns pres) = replicate (n_clauses ac) (ac_eff ac)" *)
using assms by (induction ns pres rule: list_induct2) simp_all

lemma (in ast_domain) split_dom_sel [simp]:
  "types D4 = types D"
  "predicates D4 = predicates D"
  "consts D4 = consts D"
  "actions D4 = split_acs"
  using split_dom_def by simp_all

lemma (in ast_problem) split_prob_sel [simp]:
  "domain P4 = D4"
  "objects P4 = objects P"
  "init P4 = init P"
  "goal P4 = goal P"
  using split_prob_def by simp_all

text \<open> Action splitting properties \<close>
lemma (in ast_domain) split_ac_len:
  "length (split_ac ac) = length (dnf_list (ac_pre ac))"
  "length (split_ac_names ac) = length (dnf_list (ac_pre ac))"
  unfolding split_ac_def split_ac_names_def n_clauses_def by simp_all

lemma (in ast_domain) split_ac_nth:
  assumes "i < length (dnf_list (ac_pre ac))"
  shows "split_ac ac ! i =
    Action_Schema
      (padl split_pre_pad (show i) @ ac_name ac)
      (ac_params ac)
      (dnf_list (ac_pre ac) ! i)
      (ac_eff ac)"
  using assms unfolding split_ac_def split_ac_names_def n_clauses_def
  by (cases ac) simp

lemma (in ast_domain4) p_ac:
  "ac' \<in> set (actions D4) \<longleftrightarrow> (\<exists>ac \<in> set (actions D). ac' \<in> set (split_ac ac))"
  unfolding split_dom_sel split_acs_def by simp

lemma (in ast_domain) split_pres: "map ac_pre (split_ac a) = dnf_list (ac_pre a)"
  unfolding split_ac_def Let_def apply (rule set_n_pre_mapsel)
  unfolding split_ac_names_def n_clauses_def by simp

lemma (in ast_domain) split_ac_sel:
  assumes "a' \<in> set (split_ac a)"
  shows
    "\<exists>i < length (split_ac a). ac_name a' = padl split_pre_pad (show i) @ ac_name a"
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
  from i show "\<exists>i < length (split_ac a). ac_name a' = padl split_pre_pad (show i) @ ac_name a"
    using split_ac_nth split_ac_len(1) by auto
qed

subsection \<open> Output format \<close>

theorem (in ast_problem4) prec_normed_ac:
  "\<forall>ac' \<in> set (split_ac ac). is_conj (ac_pre ac')"
  using split_ac_sel(3) dnf_list_conjs by auto

theorem (in ast_problem4) prec_normed_dom:
  "d4.prec_normed_dom"
  unfolding d4.prec_normed_dom_def split_prob_sel split_dom_sel split_acs_def
  using prec_normed_ac by simp

subsection \<open> Well-formedness \<close>

context ast_domain4 begin

lemma p_wf_type: "d4.wf_type = wf_type"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma p_wf_pred_decl: "d4.wf_predicate_decl = wf_predicate_decl"
  apply (rule ext)
  subgoal for x                                      
    apply (cases x; simp) using p_wf_type by simp
  done

lemma p_constT: "d4.constT = constT"
  unfolding ast_domain.constT_def by simp

lemma (in ast_problem4) p_objT: "p4.objT = objT"
  unfolding ast_problem.objT_def using p_constT by simp

lemma p_sig: "d4.sig = sig"
  unfolding ast_domain.sig_def by simp

lemma p_subtype_rel: "d4.subtype_rel = subtype_rel"
  unfolding ast_domain.subtype_rel_def by simp

lemma p_of_type: "d4.of_type = of_type"
  unfolding ast_domain.of_type_def using p_subtype_rel by simp

lemma p_is_of_type: "d4.is_of_type = is_of_type"
  unfolding ast_domain.is_of_type_def using p_of_type by metis

lemma p_wf_atom: "d4.wf_atom = wf_atom"
  apply (rule ext; rule ext)
  subgoal for tyt x
    apply (cases x; simp)
    using split_dom_sel(1-2) p_sig p_is_of_type by metis
  done

lemma p_wf_fmla: "d4.wf_fmla = wf_fmla"
  unfolding ast_domain.wf_fmla_alt using p_wf_atom by metis

lemma p_wf_eff: "d4.wf_effect = wf_effect"
  unfolding ast_domain.wf_effect_alt ast_domain.wf_fmla_atom_alt
  using p_wf_fmla by metis

lemma (in ast_problem4) p_wf_wm: "p4.wf_world_model = wf_world_model"
  unfolding ast_problem.wf_world_model_def ast_domain.wf_fmla_atom_alt
  using p_wf_fmla p_objT split_prob_sel(1) by metis

lemma (in ast_problem4) p_is_obj_of_type: "p4.is_obj_of_type = is_obj_of_type"
  unfolding ast_problem.is_obj_of_type_def p_objT split_prob_sel p_of_type ..

end
context wf_ast_domain4 begin

(* generated action IDs are distinct *)
(* TODO: simplify; combine with split_ac_sel *)

lemma (in ast_domain) split_names_prefix_length:
  assumes "ac \<in> set (actions D)" "n \<in> set (split_ac_names ac)"
  shows "\<exists>p. length p = split_pre_pad \<and> n = p @ ac_name ac"
proof -
  from assms(2)[unfolded split_ac_names_def] obtain p where
    pin: "p \<in> set (distinct_strings (n_clauses ac))" and
    n: "n = padl split_pre_pad p @ ac_name ac"
    by auto

  have "n_clauses ac \<le> max_n_clauses"
    using max_n_clauses_def assms(1) by simp
  hence "length p \<le> split_pre_pad"
    using pin split_pre_pad_def distinct_strings_max_len by simp
  hence "length (padl split_pre_pad p) = split_pre_pad"
    using padl_length(1) by auto
  thus ?thesis using n by simp
qed

lemma (in ast_domain) split_names_distinct:
  shows "distinct (split_ac_names ac)"
proof -
  have "split_ac_names ac =
    map (\<lambda>p. p @ ac_name ac) (map (padl split_pre_pad) (distinct_strings (n_clauses ac)))"
    unfolding split_ac_names_def by simp
  thus ?thesis using distinct_strings_padded append_r_distinct by metis
qed

lemma (in wf_ast_domain) split_names_disjoint:
  assumes "ac \<in> set (actions D)" "ac' \<in> set (actions D)" "ac_name ac \<noteq> ac_name ac'"
  shows "set (split_ac_names ac) \<inter> set (split_ac_names ac') = {}"
  apply (unfold disjoint_iff_not_equal)
  using assms split_names_prefix_length
  using append_eq_append_conv by metis

(* TODO generalize to Utils:
  distinct xs \<Longrightarrow> x \<noteq> y; \<in> set xs \<longrightarrow> f x \<inter> f y = {} \<Longrightarrow> distinct (removeAll ... *)
lemma (in wf_ast_domain) split_names_dist_nonempty:
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
  thus ?thesis using wf_D(6) by simp
qed

lemma (in wf_ast_domain) split_names_disjoint2:
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

lemma (in ast_domain4) p_ac_names:
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

lemma p_actions_wf: "list_all1 d4.wf_action_schema (actions D4)"
proof
  fix a' assume assm: "a' \<in> set (actions D4)"
  then obtain a where a: "a \<in> set (actions D)" "a' \<in> set (split_ac a)" using p_ac by auto
  hence "atoms (ac_pre a') \<subseteq> atoms (ac_pre a)" using split_ac_sel(3) dnf_list_atoms by metis
  hence fmla_wf: "d4.wf_fmla tyt (ac_pre a')" if "wf_fmla tyt (ac_pre a)" for tyt
    unfolding p_wf_fmla
    using that ast_domain.wf_fmla_alt p_wf_fmla by blast

  have "d4.wf_action_schema a'" if "wf_action_schema a"
    using that unfolding ast_domain.wf_action_schema_alt
    using a(2) split_ac_sel p_constT fmla_wf p_wf_eff by metis

  thus "d4.wf_action_schema a'" using a(1) wf_D by simp
qed

theorem (in wf_ast_domain4) split_dom_wf: "d4.wf_domain"
  unfolding d4.wf_domain_def split_dom_sel
  unfolding p_wf_type p_wf_pred_decl
  using wf_D split_ac_names_dist p_actions_wf ast_domain.wf_types_def by simp_all

theorem (in wf_ast_problem4) split_prob_wf: "p4.wf_problem"
  unfolding p4.wf_problem_def split_prob_sel
  unfolding p_wf_type p_wf_wm p_wf_fmla p_objT
  using wf_P split_dom_wf by simp_all

end

sublocale wf_ast_domain4 \<subseteq> d4: wf_ast_domain D4
  using split_dom_wf wf_ast_domain.intro by simp

sublocale wf_ast_problem4 \<subseteq> p4: wf_ast_problem P4
  using split_prob_wf wf_ast_problem.intro by simp

subsection \<open> Semantics \<close>

text \<open> Applying a map to dnf_list \<close>

lemma neg_of_lit_map: "map_formula m (neg_of_lit l) = neg_of_lit (map_literal m l)"
  by (cases l) simp_all

lemma neg_conj_of_clause_map: "map_formula m (neg_conj_of_clause c)
  = neg_conj_of_clause (map (map_literal m) c)"
  unfolding neg_conj_of_clause_def
  apply (induction c) apply simp using neg_of_lit_map by auto
  
lemma neg_conj_of_clause_map2: "map ((map_formula m) \<circ> neg_conj_of_clause) D
  = map neg_conj_of_clause (map (map (map_literal m)) D)"
  using neg_conj_of_clause_map by auto

lemma nnf_map: "map_formula m (nnf F) = nnf (map_formula m F)"
  by (induction F rule: nnf.induct) auto

(* there's gotta be some easier way to prove this *)
(* I can't overload g in this proof, so I need a second instance g' *)
lemma lin_prod_map:
  assumes "\<And>x y. f (g x y) = g' (f x) (f y)"
  shows "map f [g x y. x \<leftarrow> xs, y \<leftarrow> ys] = [g' x y. x \<leftarrow> map f xs, y \<leftarrow> map f ys]"
proof -
  have aux: "map (\<lambda>x. f (g x)) xs = map f (map g xs)"
    for g :: "'a \<Rightarrow> 'b" and f :: "'b \<Rightarrow> 'c" and xs :: "'a list" by simp

  (* "map f [g x y. x \<leftarrow> xs, y \<leftarrow> ys] = map f (concat (map (\<lambda>x. map (g x) ys) xs))" *)
  have "map f [g x y. x \<leftarrow> xs, y \<leftarrow> ys] = (concat (map (map f) (map (\<lambda>x. map (g x) ys) xs)))"
    using map_concat by blast
  also have "... = concat (map ((map f) \<circ> (\<lambda>x. map (g x) ys)) xs)" by simp
  also have "... = concat (map (\<lambda>x. map f (map (g x) ys)) xs)" by (meson comp_apply)
  also have "... = concat (map (\<lambda>x. map (f \<circ> (g x)) ys) xs)" by simp
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. f (g x y)) ys) xs)"
    by (metis fun_comp_eq_conv[of f])
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. g' (f x) (f y)) ys) xs)"
    using assms by simp
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. g' (f x) y) (map f ys)) xs)"
    using aux by metis
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. g' x y) (map f ys)) (map f xs))"
    using aux[of "(\<lambda>x. map (\<lambda>y. g' x y) (map f ys))"] by metis
  finally show ?thesis by simp
qed

lemma append_prod_map:
  shows "map (map f) [x @ y. x \<leftarrow> xss, y \<leftarrow> yss] = [x @ y. x \<leftarrow> map (map f) xss, y \<leftarrow> map (map f) yss]"
  by (rule lin_prod_map) simp

lemma cnf_lists_map:
  assumes "is_nnf F"
  shows "map (map (map_literal m)) (cnf_lists F) = cnf_lists (map_formula m F)"
  using assms proof (induction F rule: cnf_lists.induct)
  case (6 F G)
    define mp where "mp = (map (map_literal m))"
    have "map mp (cnf_lists (F \<^bold>\<or> G)) = map mp [f @ g. f \<leftarrow> (cnf_lists F), g \<leftarrow> (cnf_lists G)]" by simp
    also have "... = [f @ g. f \<leftarrow> map mp (cnf_lists F), g \<leftarrow> map mp (cnf_lists G)]"
      unfolding mp_def using append_prod_map by auto
    also have "... = [f @ g. f \<leftarrow> cnf_lists (map_formula m F), g \<leftarrow> cnf_lists (map_formula m G)]"
      using 6 unfolding mp_def by fastforce
    finally show ?case unfolding mp_def by simp
qed simp_all

lemma dnf_list_map: "map (map_formula m) (dnf_list F) = dnf_list (map_formula m F)"
proof -
  have "map (map_formula m) (dnf_list F)
    = map (map_formula m) (map neg_conj_of_clause (cnf_lists (nnf (\<^bold>\<not> F))))"
    unfolding dnf_list_def ..
  also have "... = map ((map_formula m) \<circ> neg_conj_of_clause) (cnf_lists (nnf (\<^bold>\<not> F)))"
    by simp
  also have "... = map neg_conj_of_clause (map (map (map_literal m)) (cnf_lists (nnf (\<^bold>\<not> F))))"
    using neg_conj_of_clause_map by auto
  also have "... = map neg_conj_of_clause (cnf_lists (map_formula m (nnf (\<^bold>\<not> F))))"
    using cnf_lists_map by (metis is_nnf_nnf)
  also have "... = map neg_conj_of_clause (cnf_lists (nnf (\<^bold>\<not> (map_formula m F))))"
    using nnf_map formula.map(3) by metis
  finally show ?thesis unfolding dnf_list_def by simp
qed

(* end map *)

context ast_domain4 begin

lemma (in -) dnf_list_cw:
  assumes "wm_basic M"
  shows "M \<^sup>c\<TTurnstile>\<^sub>= F \<longleftrightarrow> (\<exists>c\<in>set (dnf_list F). M \<^sup>c\<TTurnstile>\<^sub>= c)"
  using assms valuation_iff_close_world dnf_list_semantics by blast

lemma precond_prop_iff_split:
  "(\<exists>c \<in> set (dnf_list (ac_pre a)). P c) \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). P (ac_pre a'))"
proof -
  let ?dnf = "dnf_list (ac_pre a)"
  have "(\<exists>c \<in> set ?dnf. P c) \<longleftrightarrow> (\<exists>i < length ?dnf. P (?dnf ! i))"
    using in_set_conv_nth by metis
  also have "... \<longleftrightarrow> (\<exists>i < length ?dnf. P (ac_pre (split_ac a ! i)))"
    using split_ac_nth by auto
  also have "... \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). P (ac_pre a'))"
    using in_set_conv_nth split_ac_len by metis
  finally show ?thesis by simp
qed

lemma inst_pre_iff_split:
  assumes "wm_basic M"
  shows "M \<^sup>c\<TTurnstile>\<^sub>= precondition (instantiate_action_schema a args) \<longleftrightarrow>
    (\<exists>a' \<in> set (split_ac a). M \<^sup>c\<TTurnstile>\<^sub>= precondition (d4.instantiate_action_schema a' args))"
proof -
  let ?inst_fmla = "map_atom_fmla (ac_tsubst (ac_params a) args)"
  have "M \<^sup>c\<TTurnstile>\<^sub>= precondition (instantiate_action_schema a args) \<longleftrightarrow>
    M \<^sup>c\<TTurnstile>\<^sub>= ?inst_fmla (ac_pre a)"
    using instantiate_action_schema_alt by simp
  also have "... \<longleftrightarrow> (\<exists>c \<in> set (dnf_list (?inst_fmla (ac_pre a))). M \<^sup>c\<TTurnstile>\<^sub>= c)"
    using dnf_list_cw[OF assms] by metis
  also have "... \<longleftrightarrow> (\<exists>c \<in> set (map ?inst_fmla (dnf_list (ac_pre a))). M \<^sup>c\<TTurnstile>\<^sub>= c)"
    using dnf_list_map[of "map_atom (ac_tsubst (ac_params a) args)"] by auto
  also have "... \<longleftrightarrow> (\<exists>c \<in> set (dnf_list (ac_pre a)). M \<^sup>c\<TTurnstile>\<^sub>= ?inst_fmla c)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). M \<^sup>c\<TTurnstile>\<^sub>= ?inst_fmla (ac_pre a'))"
    using precond_prop_iff_split by simp
  also have "... \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). M \<^sup>c\<TTurnstile>\<^sub>= precondition (instantiate_action_schema a' args))"
    using instantiate_action_schema_alt split_ac_sel by simp
  finally show ?thesis by simp
qed

lemma (in ast_problem4) p_ac_params_match:
  assumes "a' \<in> set (split_ac a)"
  shows "action_params_match a = p4.action_params_match a'"
  unfolding ast_problem.action_params_match_def p_is_obj_of_type split_ac_sel(2)[OF assms] ..

lemma (in ast_problem4) p_exec:
  assumes "a' \<in> set (split_ac a)"
    "resolve_action_schema n = Some a" "d4.resolve_action_schema n' = Some a'"
  shows "execute_plan_action (PAction n args) = p4.execute_plan_action (PAction n' args)"
  unfolding ast_problem.execute_plan_action_def ast_problem.resolve_instantiate.simps
  using assms(2,3) apply simp
  unfolding instantiate_action_schema_alt apply simp
  unfolding split_ac_sel(2,4)[OF assms(1)] ..

end
context wf_ast_problem4 begin

lemma split_pa_enabled:
  assumes "wm_basic M" "plan_action_enabled \<pi> M"
  shows "\<exists>\<pi>'. p4.plan_action_enabled \<pi>' M \<and> (execute_plan_action \<pi> M = p4.execute_plan_action \<pi>' M)"
proof (cases \<pi>)
  case [simp]: (PAction n args)

  from assms(2) obtain a where a: "resolve_action_schema n = Some a" "action_params_match a args"
    "a \<in> set (actions D)"
    unfolding plan_action_enabled_def using wf_pa_refs_ac by force
  from assms obtain a' where a': "a' \<in> set (split_ac a)"
    "M \<^sup>c\<TTurnstile>\<^sub>= precondition (d4.instantiate_action_schema a' args)"
    unfolding plan_action_enabled_def
    using inst_pre_iff_split PAction by (metis a(1) resolve_instantiate.simps option.sel)
  
  let ?pi = "PAction n args"
  let ?pi' = "PAction (ac_name a') args"

  (* precondition satisfied *)
  from a'(1) have "a' \<in> set (actions D4)" using a(3) split_dom_sel(4)
    unfolding split_acs_def by auto
  hence res': "d4.resolve_action_schema (ac_name a') = Some a'"
    using d4.res_aux by simp
  with a'(2) have sat': "M \<^sup>c\<TTurnstile>\<^sub>= precondition (p4.resolve_instantiate ?pi')"
    by simp

  (* well-formed *)
  have "p4.action_params_match a' args"
    using a'(1) a(2) p_ac_params_match by simp
  with res' have wf': "p4.wf_plan_action ?pi'"
    using p4.wf_plan_action_simple by fastforce

  from wf' sat' have enab': "p4.plan_action_enabled ?pi' M"
    using p4.plan_action_enabled_def by simp
  thus ?thesis using p_exec a'(1) a(1) res' by auto
qed

lemma p_valid_plan_from:
  assumes "wf_world_model s" "valid_plan_from s \<pi>s"
  shows "\<exists>\<pi>s'. p4.valid_plan_from s \<pi>s'"
using assms proof (induction \<pi>s arbitrary: s)
  case Nil thus ?case
    unfolding ast_problem.valid_plan_def ast_problem.valid_plan_from_def split_prob_sel
    using ast_problem.plan_action_path_Nil by metis
next
  case (Cons \<pi> \<pi>s)
  then obtain \<pi>' where pi': "p4.plan_action_enabled \<pi>' s" "execute_plan_action \<pi> s = p4.execute_plan_action \<pi>' s"
    using split_pa_enabled wf_wm_basic valid_plan_from_Cons by blast
  then obtain \<pi>s' where "p4.valid_plan_from (p4.execute_plan_action \<pi>' s) \<pi>s'"
    using Cons wf_execute by fastforce
  thus ?case using p4.valid_plan_from_Cons pi'(1) by metis
qed

lemma (in ast_domain4) restore_split_ac:
  assumes "a \<in> set (actions D)" "a' \<in> set (split_ac a)"
  shows "drop split_pre_pad (ac_name a') = ac_name a"
proof -
  from assms have "ac_name a' \<in> set (map ac_name (split_ac a))" by auto
  hence "ac_name a' \<in> set (split_ac_names a)"
    unfolding split_ac_def
    using split_ac_len set_n_pre_mapsel by metis
  thus ?thesis
    using assms split_names_prefix_length drop_prefix by metis
qed

lemma restore_pa_enabled:
  assumes "wm_basic M" "p4.plan_action_enabled \<pi>' M"
  defines pi: "\<pi> \<equiv> restore_pa_split \<pi>'"
  shows "plan_action_enabled \<pi> M \<and> (execute_plan_action \<pi> M = p4.execute_plan_action \<pi>' M)"
proof (cases \<pi>')
  case [simp]: (PAction n' args)
  let ?pi' = "PAction n' args"
  let ?pi = "PAction (drop split_pre_pad n') args"

  from assms(2) obtain a' where a': "p4.resolve_action_schema n' = Some a'" "p4.action_params_match a' args"
    "a' \<in> set (actions D4)" "ac_name a' = n'"
    unfolding p4.plan_action_enabled_def
    using split_prob_sel p4.wf_pa_refs_ac by force
  from assms a'(1,3) obtain a where a: "a' \<in> set (split_ac a)"
    "M \<^sup>c\<TTurnstile>\<^sub>= precondition (instantiate_action_schema a args)" "a \<in> set (actions D)"
    unfolding p4.plan_action_enabled_def
    using PAction by (metis p_ac inst_pre_iff_split p4.resolve_instantiate.simps option.sel)

  (* precondition enabled *)
  hence "drop split_pre_pad (ac_name a') = ac_name a"
    using restore_split_ac by simp
  with a(3) have res: "resolve_action_schema (drop split_pre_pad n') = Some a"
    using res_aux a'(4) by simp
  with a(2) have sat: "M \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate ?pi)"
    by simp

  (* well-formed *)
  have "action_params_match a args" using a(1) a'(2) p_ac_params_match by simp
  with res have wf: "wf_plan_action ?pi"
    using wf_plan_action_simple by fastforce

  from wf sat have enab: "plan_action_enabled ?pi M"
    using plan_action_enabled_def by simp
  with a(1) a'(1) res show ?thesis using p_exec pi by simp
qed

lemma restore_plan_split_valid_from:
  assumes "p4.wf_world_model s" "p4.valid_plan_from s \<pi>s'"
  shows "valid_plan_from s (restore_plan_split \<pi>s')"
using assms proof (induction \<pi>s' arbitrary: s)
  case Nil thus ?case 
  unfolding ast_problem.valid_plan_def ast_problem.valid_plan_from_def split_prob_sel list.map(1)
    using ast_problem.plan_action_path_Nil by metis
next
  case (Cons \<pi>' \<pi>s')
  let ?pi = "restore_pa_split \<pi>'" and ?pis = "restore_plan_split \<pi>s'"
  from Cons have pi: "plan_action_enabled ?pi s" "execute_plan_action ?pi s = p4.execute_plan_action \<pi>' s"
    using restore_pa_enabled p4.wf_wm_basic p4.valid_plan_from_Cons wf_wm_basic by simp_all

  from Cons have "valid_plan_from (execute_plan_action ?pi s) ?pis"
    using p4.wf_execute p4.valid_plan_from_Cons pi(2) by simp
  thus ?case using valid_plan_from_Cons p_wf_wm pi(1) by simp
qed

theorem split_valid_iff:
  "(\<exists>\<pi>s. valid_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. p4.valid_plan \<pi>s')"
  unfolding ast_problem.valid_plan_def
  using restore_plan_split_valid_from p_valid_plan_from
  by (metis I_def p4.I_def p4.wf_I wf_I split_prob_sel(3))

theorem restore_plan_split_valid:
  "p4.valid_plan \<pi>s' \<Longrightarrow> valid_plan (restore_plan_split \<pi>s')"
  unfolding ast_problem.valid_plan_def
  using restore_plan_split_valid_from p4.wf_I by simp

end

subsection \<open> Code Setup \<close>

lemmas precond_norm_code =
  n_clauses_def
  ast_domain.max_n_clauses_def
  ast_domain.split_pre_pad_def
  ast_domain.split_ac_names_def
  ast_domain.split_ac_def
  ast_domain.split_acs_def
  ast_domain.split_dom_def
  ast_problem.split_prob_def
  ast_domain.restore_pa_split.simps
declare precond_norm_code[code]

end