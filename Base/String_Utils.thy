theory String_Utils
imports Main Nat_Show_Utils "HOL-Library.Sublist" Grounding_Utils
begin

abbreviation max_length :: "'a list list \<Rightarrow> nat" where
  "max_length xss \<equiv> Max (length ` set xss)"

lemma inj_prepend: "inj ((+) (s::String.literal))"
  apply (rule injI)
  by (metis String.implode_explode_eq plus_literal.rep_eq same_append_eq)

definition safe_prefix :: "String.literal list \<Rightarrow> String.literal" where
  "safe_prefix ss \<equiv>
    String.implode (replicate (max_length (map literal.explode ss) + 1) (CHR ''_''))"

lemma safe_prefix_explode:
  "literal.explode (safe_prefix xs)
     = replicate (max_length (map literal.explode xs) + 1) (CHR ''_'')"
  unfolding safe_prefix_def
  by (simp add: String.explode_implode_eq String.ascii_of_idem map_replicate_const)

lemma safe_prefix_correct: "safe_prefix xs + x \<notin> set xs"
proof
  assume "safe_prefix xs + x \<in> set xs"
  hence "length (literal.explode (safe_prefix xs + x))
           \<le> max_length (map literal.explode xs)" by force
  moreover have "length (literal.explode (safe_prefix xs + x))
                   = length (literal.explode (safe_prefix xs)) + length (literal.explode x)"
    by (simp add: plus_literal.rep_eq)
  moreover have "length (literal.explode (safe_prefix xs))
                   = max_length (map literal.explode xs) + 1"
    using safe_prefix_explode by simp
  ultimately show False by simp
qed

lemma dist_prefix: "distinct xs \<Longrightarrow> distinct (map (\<lambda>x. safe_prefix ys + x) xs)"
  by (simp add: distinct_map inj_on_def inj_prepend[unfolded inj_def])

lemma inj_append_lit: "inj (\<lambda>x. x + (p::String.literal))"
  by (rule injI) (metis String.implode_explode_eq plus_literal.rep_eq append_same_eq)

lemma append_r_distinct_lit: "distinct xs \<Longrightarrow> distinct (map (\<lambda>x. x + (p::String.literal)) xs)"
  by (simp add: distinct_map inj_on_def inj_append_lit[unfolded inj_def])

lemma append_eq_append_conv_lit:
  assumes "size (xs::String.literal) = size ys \<or> size us = size vs"
  shows "(xs + us = ys + vs) = (xs = ys \<and> us = vs)"
  using assms
  by (metis size_literal.rep_eq plus_literal.rep_eq literal.explode_inject append_eq_append_conv)



lemma implode_inj_on:
  "inj_on String.implode {s. \<forall>n \<in> set s. \<not>digit7 n}"
proof -
  have 1: "String.implode x \<noteq> String.implode y" 
    if "\<forall>n \<in> set x. \<not>digit7 n"
    and "\<forall>n \<in> set y. \<not>digit7 n"
    and "x \<noteq> y" for x y
  proof (rule notI)
    assume "String.implode x = String.implode y"
    hence "literal.explode (String.implode x) = literal.explode (String.implode y)"
      by presburger
    moreover
    have "literal.explode (String.implode x) = x" using that
      by (simp add: String.ascii_of_idem list.map_ident_strong)
    moreover
    have "literal.explode (String.implode y) = y" using that
      by (simp add: String.ascii_of_idem list.map_ident_strong)
    ultimately show False using that by simp
  qed
  show ?thesis by (rule inj_onI) (use 1 in auto)
qed

function (domintros) safe_suffix'::"String.literal list \<Rightarrow> String.literal \<Rightarrow> nat \<Rightarrow> String.literal" where
"safe_suffix' S s n = (
  let s' = s + String.implode (show n) 
  in if (s' \<in> set S) then safe_suffix' S s (Suc n) else s')"
  by pat_completeness auto

lemma show_no_digit7: "\<forall>c \<in> set (show (m::nat)). \<not>digit7 c"
  using show_nat_chars[of m] by auto

lemma inj_show_prepend: "inj (\<lambda>m::nat. s + String.implode (show m))"
proof (rule injI)
  fix x y :: nat
  assume "s + String.implode (show x) = s + String.implode (show y)"
  hence "String.implode (show x) = String.implode (show y)"
    using inj_prepend by (simp add: inj_eq)
  hence "show x = show y"
    using show_no_digit7 implode_inj_on by (auto simp: inj_on_def)
  thus "x = y" using show_nat_inj by blast
qed

lemma finite_show_preimage: "finite {j::nat. s + String.implode (show j) \<in> set S}"
  using finite_inverse_image[OF finite_set[of S] inj_show_prepend] by blast

lemma safe_suffix'_dom:
  shows "safe_suffix'_dom (S, s, n)"
proof (induction "card {m. n \<le> m \<and> s + String.implode (show m) \<in> set S}"
                 arbitrary: n rule: less_induct)
  case (less n)
  let ?A = "\<lambda>k. {m::nat. k \<le> m \<and> s + String.implode (show m) \<in> set S}"
  have sub: "?A k \<subseteq> {j::nat. s + String.implode (show j) \<in> set S}" for k by auto
  have fin: "finite (?A k)" for k
    using finite_show_preimage by (rule finite_subset[OF sub])
  show ?case
  proof (rule safe_suffix'.domintros)
    assume H: "s + String.implode (show n) \<in> set S"
    have eq: "?A (Suc n) = ?A n - {n}" by auto
    have nin: "n \<in> ?A n" using H by simp
    have "card (?A n - {n}) < card (?A n)"
      using fin[of n] nin by (rule card_Diff1_less)
    hence "card (?A (Suc n)) < card (?A n)" using eq by simp
    thus "safe_suffix'_dom (S, s, Suc n)"
      using less.hyps by blast
  qed
qed

termination safe_suffix' using safe_suffix'_dom by simp

fun safe_suffix::"String.literal list \<Rightarrow> String.literal \<Rightarrow> String.literal" where
"safe_suffix S s = (if (s \<in> set S) then safe_suffix' S s 0 else s)"

lemma safe_suffix'_correct:
  "safe_suffix' S s n \<notin> set S"
proof (induction "card {m. n \<le> m \<and> s + String.implode (show m) \<in> set S}"
                 arbitrary: n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "s + String.implode (show n) \<in> set S")
    case False
    thus ?thesis by simp
  next
    case True
    let ?A = "\<lambda>k. {m::nat. k \<le> m \<and> s + String.implode (show m) \<in> set S}"
    have eq: "?A (Suc n) = ?A n - {n}" by auto
    have sub: "?A n \<subseteq> {j::nat. s + String.implode (show j) \<in> set S}" by auto
    have fin: "finite (?A n)"
      using finite_show_preimage by (rule finite_subset[OF sub])
    have nin: "n \<in> ?A n" using True by simp
    have "card (?A n - {n}) < card (?A n)"
      using fin nin by (rule card_Diff1_less)
    hence "card (?A (Suc n)) < card (?A n)" using eq by simp
    hence "safe_suffix' S s (Suc n) \<notin> set S"
      using less.hyps by blast
    thus ?thesis using True by simp
  qed
qed

lemma safe_suffix_correct:
  "safe_suffix S s \<notin> set S"
  using safe_suffix'_correct
  by simp

(* padding *)

definition pad :: "nat \<Rightarrow> string \<Rightarrow> string" where
  "pad n s \<equiv> s @ replicate (n - length s) (CHR ''_'')"

definition padl :: "nat \<Rightarrow> string \<Rightarrow> string" where
  "padl n s \<equiv> replicate (n - length s) (CHR ''_'') @ s"

lemma pad_length:
  "n \<ge> length s \<Longrightarrow> length (pad n s) = n"
  "length (pad n s) \<ge> n"
  "length (pad n s) \<ge> length s"
  unfolding pad_def by simp_all

lemma padl_length:
  "n \<ge> length s \<Longrightarrow> length (padl n s) = n"
  "length (padl n s) \<ge> n"
  "length (padl n s) \<ge> length s"
  unfolding padl_def by simp_all

lemma count_replicate: "count_list (replicate n x) x = n"
  by (induction n) simp_all

lemma count_pad:
  assumes "CHR ''_'' \<notin> set xs"
  shows "count_list (pad n xs) (CHR ''_'') = n - length xs"
  unfolding pad_def using assms count_replicate by fastforce

lemma count_padl:
  assumes "CHR ''_'' \<notin> set xs"
  shows "count_list (padl n xs) (CHR ''_'') = n - length xs"
  unfolding padl_def using assms count_replicate by fastforce

(* Omitting "n \<ge> length xs" "n \<ge> length ys" from assumptions because it's unnecessary*)
lemma pad_neq:
  assumes "(CHR ''_'') \<notin> set xs" "CHR ''_'' \<notin> set ys" "xs \<noteq> ys"
  shows "pad n xs \<noteq> pad n ys"
proof (cases "length xs = length ys")
  case False
  from False consider
      (neq) "n - length xs \<noteq> n - length ys" |
      (zero) "n - length xs = 0 \<and> n - length ys = 0"
    by linarith
  then show ?thesis
  proof (cases)
    case neq
    moreover have "count_list (pad n ys) (CHR ''_'') = n - length ys" using assms(2) count_pad by simp
    moreover have "count_list (pad n xs) (CHR ''_'') = n - length xs" using assms(1) count_pad by simp
    ultimately show ?thesis by metis
  next
    case zero
    thus ?thesis using False pad_def by auto
  qed
qed (simp add: pad_def assms(3))

lemma padl_neq:
  assumes "(CHR ''_'') \<notin> set xs" "CHR ''_'' \<notin> set ys" "xs \<noteq> ys"
  shows "padl n xs \<noteq> padl n ys"
proof (cases "length xs = length ys")
  case False
  from False consider
      (neq) "n - length xs \<noteq> n - length ys" |
      (zero) "n - length xs = 0 \<and> n - length ys = 0"
    by linarith
  then show ?thesis
  proof (cases)
    case neq
    moreover have "count_list (padl n ys) (CHR ''_'') = n - length ys" using assms(2) count_padl by simp
    moreover have "count_list (padl n xs) (CHR ''_'') = n - length xs" using assms(1) count_padl by simp
    ultimately show ?thesis by metis
  next
    case zero
    thus ?thesis using False padl_def by auto
  qed
qed (simp add: padl_def assms(3))

definition make_unique :: "string list \<Rightarrow> string \<Rightarrow> string" where
  "make_unique ss s \<equiv> pad (max_length ss + 1) s"

lemma made_unique: "make_unique ss x \<notin> set ss"
proof -
  have "\<forall>s \<in> set ss. length s \<le> max_length ss"
    by simp
  moreover have "max_length ss + 1 \<le> length (make_unique ss x)"
    using make_unique_def pad_length(2) by simp
  ultimately have "\<forall>s \<in> set ss. length s < length (make_unique ss x)"
    by (meson add_le_mono1 le_trans less_iff_succ_less_eq)
  thus ?thesis by auto
qed


definition pad_strings :: "string list \<Rightarrow> string list" where
  "pad_strings ss \<equiv> map (pad (max_length ss + 1)) ss"


(* nat upto *)

fun nat_range_help :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "nat_range_help 0 build = build" |
  "nat_range_help (Suc n) build = nat_range_help n (n # build)"

definition "nat_range n \<equiv> nat_range_help n []"

lemma nat_range_help_len: "length (nat_range_help n xs) = n + length xs"
  by (induction n arbitrary: xs) simp_all

lemma nat_range_length [simp]: "length (nat_range n) = n"
  using nat_range_def nat_range_help_len by simp

lemma nat_range_help_aux: "nat_range_help n (xs @ ys) = nat_range_help n xs @ ys"
  by (induction n xs rule: nat_range_help.induct) simp_all

lemma nat_range_help_nth: assumes "i < n" shows "nat_range_help n xs ! i = i"
  using assms proof (induction n xs rule: nat_range_help.induct)
  case (2 n xs)
  then consider "i < n" | (eq) "i = n" by linarith
  thus ?case proof (cases)
    case eq
    have "nat_range_help (Suc n) xs = nat_range_help n ([] @ (n # xs))"
      by simp
    also have "... = nat_range_help n [] @ (n # xs)"
      using nat_range_help_aux by metis
    also have "i = length (nat_range_help n [])"
      using nat_range_help_len eq by simp
    ultimately show ?thesis using eq
      by (metis nth_append_length)
  qed (simp add: 2)
qed simp_all

lemma nat_range_nth [simp]: assumes "i < n" shows "nat_range n ! i = i"
  using assms nat_range_help_nth nat_range_def by simp

lemma nat_range_zero[simp]: "nat_range 0 = []"
  unfolding nat_range_def by simp

lemma nat_range_snoc[simp]: "nat_range (Suc n) = nat_range n @ [n]"
  unfolding nat_range_def nat_range_help.simps
  using nat_range_help_aux by (metis eq_Nil_appendI)

lemmas nat_range_simps = nat_range_zero nat_range_snoc

lemma nat_range_prefix: "prefix (nat_range n) (nat_range (n+k))"
  apply (induction k)
   apply simp
  apply (subst add_Suc_right)
  apply (subst nat_range_snoc)
  using prefix_def by auto

lemma nat_range_dist: "distinct (nat_range n)"
proof -
  have "nat_range n ! i \<noteq> nat_range n ! j" if "i \<noteq> j" "i < n" "j < n" for i j
    using nat_range_nth that by simp
  moreover have "i < n \<longleftrightarrow> i < length (nat_range n)" for i by auto
  ultimately show ?thesis using distinct_conv_nth by blast
qed

definition "distinct_strings n \<equiv> map show (nat_range n)"

lemma unique_str_bij:
  fixes i :: nat and j :: nat
  shows "i \<noteq> j \<longleftrightarrow> show i \<noteq> show j"
  using show_nat_inj by auto

lemma distinct_str_length [simp]: "length (distinct_strings n) = n"
  unfolding distinct_strings_def
  by (cases n) simp_all

lemma distinct_strings_nth [simp]:
  assumes "i < n" shows "distinct_strings n ! i = show i"
  unfolding distinct_strings_def using assms
  by (metis nat_range_length nat_range_nth nth_map)

lemma distinct_strings_dist:
  "distinct (distinct_strings n)"
  using unique_str_bij distinct_conv_nth by fastforce

(* not sure how important those are *)

lemma distinct_strings_max_len:
  assumes "m \<le> n"
  shows "\<forall>x \<in> set (distinct_strings m). length x \<le> length (show n)"
  unfolding distinct_strings_def
using assms proof (induction n arbitrary: m)
  case (Suc n)
  have "set (distinct_strings (Suc n)) = insert (show n) (set (distinct_strings n))"
    unfolding distinct_strings_def nat_range_simps by force
  moreover have "length (show n) \<le> length (show (Suc n))"
    using nat_show_len_mono
    by (metis Suc_n_not_le_n nat_le_linear)
  ultimately show ?case using Suc (* TODO simplify *)
    by (metis (mono_tags, lifting) Suc_le_mono distinct_strings_def dual_order.trans insertE le_SucE)
qed simp

lemma distinct_strings_prefix: "prefix (distinct_strings n) (distinct_strings (n+k))"
  using distinct_strings_def nat_range_prefix map_mono_prefix by metis

lemma pad_show_neq:
  fixes i j :: nat
  assumes "i \<noteq> j"
  shows "padl k (show i) \<noteq> padl k (show j)"
  using assms padl_neq notin_show_nat show_nat_inj by simp

(* TODO pull inner if i \<noteq> j out to generalize for when map isn't explicitly used *)
lemma distinct_strings_padded:
  shows "distinct (map (padl k) (distinct_strings n))"
proof -
  let ?d = "distinct_strings n"
  have "map (padl k) ?d ! i \<noteq> map (padl k) ?d ! j"
    if "i < length ?d" "j < length ?d" "i \<noteq> j" for i j
    using that distinct_strings_dist distinct_conv_nth list_ball_nth
  proof -
    (* TODO simplify with pad_show_neq *)
    from that have notin: "CHR ''_'' \<notin> set (?d ! i)" "CHR ''_'' \<notin> set (?d ! j)"
      using distinct_strings_def notin_show_nat list_ball_nth by simp_all
    from that have  "?d ! i \<noteq> ?d ! j" using distinct_strings_dist distinct_conv_nth by metis
    hence "padl k (?d ! i) \<noteq> padl k (?d ! j)" using padl_neq notin by simp
    thus ?thesis using that by auto
  qed
  thus ?thesis using distinct_conv_nth by force
qed


context includes literal.lifting 
begin
lift_definition pad_lit::"nat \<Rightarrow> String.literal \<Rightarrow> String.literal" is pad
  by (auto simp: pad_def)

lift_definition padl_lit::"nat \<Rightarrow> String.literal \<Rightarrow> String.literal" is padl
  by (auto simp: padl_def)
                                                                              
lift_definition distinct_strings_lit :: "nat \<Rightarrow> String.literal list" is distinct_strings
  by (simp add: distinct_strings_def list_all_iff show_no_digit7)

lift_definition drop_lit :: "nat \<Rightarrow> String.literal \<Rightarrow> String.literal" is drop
  by (auto dest: in_set_dropD)

lemma pad_lit_length:
  "n \<ge> length (String.explode s) \<Longrightarrow> length (String.explode (pad_lit n s)) = n"
  "length (String.explode (pad_lit n s)) \<ge> n"
  "length (String.explode (pad_lit n s)) \<ge> length (String.explode s)"
  by (simp_all add: pad_lit.rep_eq pad_length)

lemma padl_lit_length:
  "n \<ge> length (String.explode s) \<Longrightarrow> length (String.explode (padl_lit n s)) = n"
  "length (String.explode (padl_lit n s)) \<ge> n"
  "length (String.explode (padl_lit n s)) \<ge> length (String.explode s)"
  by (simp_all add: padl_lit.rep_eq padl_length)

lemma pad_lit_size:
  "n \<ge> size s \<Longrightarrow> size (pad_lit n s) = n"
  "size (pad_lit n s) \<ge> n"
  "size (pad_lit n s) \<ge> size s"
  by (simp_all add: size_literal.rep_eq pad_lit.rep_eq pad_length)

lemma padl_lit_size:
  "n \<ge> size s \<Longrightarrow> size (padl_lit n s) = n"
  "size (padl_lit n s) \<ge> n"
  "size (padl_lit n s) \<ge> size s"
  by (simp_all add: size_literal.rep_eq padl_lit.rep_eq padl_length)

lemma count_pad_lit:
  assumes "CHR ''_'' \<notin> set (String.explode xs)"
  shows "count_list (String.explode (pad_lit n xs)) (CHR ''_'') = n - length (String.explode xs)"
  using assms by (simp add: pad_lit.rep_eq count_pad)

lemma count_padl_lit:
  assumes "CHR ''_'' \<notin> set (String.explode xs)"
  shows "count_list (String.explode (padl_lit n xs)) (CHR ''_'') = n - length (String.explode xs)"
  using assms by (simp add: padl_lit.rep_eq count_padl)

lemma pad_lit_neq:
  assumes "CHR ''_'' \<notin> set (String.explode xs)" "CHR ''_'' \<notin> set (String.explode ys)" "xs \<noteq> ys"
  shows "pad_lit n xs \<noteq> pad_lit n ys"
  using assms by transfer (rule pad_neq)

lemma padl_lit_neq:
  assumes "CHR ''_'' \<notin> set (String.explode xs)" "CHR ''_'' \<notin> set (String.explode ys)" "xs \<noteq> ys"
  shows "padl_lit n xs \<noteq> padl_lit n ys"
  using assms by transfer (rule padl_neq)

lemma distinct_padl_lit:
  assumes "distinct xs"
    and "\<forall>x \<in> set xs. CHR ''_'' \<notin> set (String.explode x)"
  shows "distinct (map (padl_lit k) xs)"
proof -
  have "inj_on (padl_lit k) (set xs)"
  proof (rule inj_onI)
    fix x y assume "x \<in> set xs" "y \<in> set xs" "padl_lit k x = padl_lit k y"
    thus "x = y" using assms(2) padl_lit_neq by metis
  qed
  thus ?thesis using assms(1) by (simp add: distinct_map)
qed

lemma distinct_strings_lit_eq: "distinct_strings_lit n = map String.implode (distinct_strings n)"
proof -
  have "list_all (\<lambda>cs. \<forall>c\<in>set cs. \<not> digit7 c) (distinct_strings n)"
    by (simp add: distinct_strings_def list_all_iff show_no_digit7)
  thus ?thesis
    by transfer (simp add: list_all_iff String.ascii_of_idem list.map_ident_strong)
qed

lemma distinct_str_lit_length [simp]: "length (distinct_strings_lit n) = n"
  by (simp add: distinct_strings_lit_eq)

lemma distinct_strings_lit_nth [simp]:
  assumes "i < n" shows "distinct_strings_lit n ! i = String.implode (show i)"
  using assms by (simp add: distinct_strings_lit_eq)

lemma distinct_strings_lit_dist: "distinct (distinct_strings_lit n)"
proof -
  have nd: "\<forall>s \<in> set (distinct_strings n). \<forall>c \<in> set s. \<not> digit7 c"
    unfolding distinct_strings_def using show_no_digit7 by auto
  have "inj_on String.implode (set (distinct_strings n))"
    using implode_inj_on nd by (blast intro: inj_on_subset)
  thus ?thesis
    unfolding distinct_strings_lit_eq
    using distinct_strings_dist by (simp add: distinct_map)
qed

lemma distinct_strings_lit_max_len:
  assumes "m \<le> n"
  shows "\<forall>x \<in> set (distinct_strings_lit m). length (String.explode x) \<le> length (show n)"
proof
  fix x assume "x \<in> set (distinct_strings_lit m)"
  then obtain s where s: "s \<in> set (distinct_strings m)" "x = String.implode s"
    unfolding distinct_strings_lit_eq by auto
  from s(1) have "\<forall>c \<in> set s. \<not> digit7 c"
    unfolding distinct_strings_def using show_no_digit7 by auto
  hence "String.explode x = s"
    using s(2) by (simp add: String.ascii_of_idem list.map_ident_strong)
  thus "length (String.explode x) \<le> length (show n)"
    using s(1) assms distinct_strings_max_len by metis
qed

lemma distinct_strings_lit_max_size:
  assumes "m \<le> n"
  shows "\<forall>x \<in> set (distinct_strings_lit m). size x \<le> length (show n)"
  using distinct_strings_lit_max_len[OF assms] by (simp add: size_literal.rep_eq)

lemma distinct_strings_lit_prefix:
  "prefix (distinct_strings_lit n) (distinct_strings_lit (n+k))"
  unfolding distinct_strings_lit_eq
  using distinct_strings_prefix map_mono_prefix by metis

lemma distinct_strings_padl_lit:
  "distinct (map (padl_lit k) (distinct_strings_lit n))"
proof (rule distinct_padl_lit)
  show "distinct (distinct_strings_lit n)" by (rule distinct_strings_lit_dist)
  show "\<forall>x \<in> set (distinct_strings_lit n). CHR ''_'' \<notin> set (String.explode x)"
  proof
    fix x assume "x \<in> set (distinct_strings_lit n)"
    then obtain s where s: "s \<in> set (distinct_strings n)" "x = String.implode s"
      unfolding distinct_strings_lit_eq by auto
    from s(1) have nds: "\<forall>c \<in> set s. \<not> digit7 c"
      unfolding distinct_strings_def using show_no_digit7 by auto
    have ex: "String.explode x = s"
      using s(2) nds by (simp add: String.ascii_of_idem list.map_ident_strong)
    have "CHR ''_'' \<notin> set s"
      unfolding distinct_strings_def using s(1)[unfolded distinct_strings_def] notin_show_nat by auto
    thus "CHR ''_'' \<notin> set (String.explode x)" using ex by simp
  qed
qed

lemma padl_lit_implode:
  shows "String.implode (padl n s) = padl_lit n (String.implode s)" 
  using literal.explode_inject padl_def padl_lit.rep_eq by fastforce

lemma drop_lit_explode: "drop_lit n s = String.implode (drop n (literal.explode s))"
  by (metis String.implode_explode_eq drop_lit.rep_eq)

lemma drop_lit_prefix: 
  assumes "size s = n" shows "drop_lit n (s + ys) = ys"
  apply (subst drop_lit_explode)
  apply (subst plus_literal.rep_eq)
  apply (subst drop_prefix)
  using size_literal.rep_eq assms apply simp
  using String.implode_explode_eq by simp

end


end