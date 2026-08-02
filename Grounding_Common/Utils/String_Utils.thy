theory String_Utils
imports Main Nat_Show_Utils "HOL-Library.Sublist" Grounding_Utils
begin

lemma inj_prepend: "inj ((+) (s::String.literal))"
  apply (rule injI)
  by (metis String.implode_explode_eq plus_literal.rep_eq same_append_eq)

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

(* fresh generated names: a token decorated with the least free decimal index *)

text \<open>Two entry points onto the single least-index search \<^const>\<open>safe_suffix\<close>:
  \<^item> \<^const>\<open>safe_suffix\<close> itself (aliased \<open>fresh_name\<close>) decorates a token so that the result is
    not a member of a given name list --- for a *complete* generated name;
  \<^item> \<open>fresh_prefix\<close> runs the same search over the prefix-closure \<open>all_prefixes\<close> of the name
    list and appends a separator, so that the result is not a *prefix* of any existing name
    --- for a namespace under which arbitrarily many names are minted.

  In the common case no index is emitted at all (\<open>type_\<close>, \<open>Goal\<close>, \<open>Defined_\<close>); an index
  appears only on a genuine clash (\<open>type0_\<close>, \<open>Goal0\<close>, \<open>Defined0_\<close>). The prefix test is mildly
  over-conservative --- an existing name \<open>typeof\<close> bumps the token to \<open>type0_\<close> even though no
  \<open>type_*\<close> name exists --- which is cosmetic and accepted.\<close>

definition prefixes_lit :: "String.literal \<Rightarrow> String.literal list" where
  "prefixes_lit s \<equiv> map String.implode (prefixes (String.explode s))"

definition all_prefixes :: "String.literal list \<Rightarrow> String.literal list" where
  "all_prefixes ns \<equiv> concat (map prefixes_lit ns)"

abbreviation fresh_name :: "String.literal list \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "fresh_name ns t \<equiv> safe_suffix ns t"

definition fresh_prefix :: "String.literal list \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "fresh_prefix ns t \<equiv> safe_suffix (all_prefixes ns) t + STR ''_''"

lemma prefixes_litI [intro]:
  assumes "n = u + x"
  shows "u \<in> set (prefixes_lit n)"
proof -
  have "String.explode n = String.explode u @ String.explode x"
    using assms by (simp add: plus_literal.rep_eq)
  hence "String.explode u \<in> set (prefixes (String.explode n))" by simp
  thus ?thesis unfolding prefixes_lit_def
    using String.implode_explode_eq by (metis image_eqI list.set_map)
qed

lemma all_prefixesI [intro]:
  assumes "n \<in> set ns"
    and "n = u + x"
  shows "u \<in> set (all_prefixes ns)"
  unfolding all_prefixes_def using assms prefixes_litI by fastforce

lemma set_subset_all_prefixes: "set ns \<subseteq> set (all_prefixes ns)"
proof
  fix n :: String.literal
  assume a: "n \<in> set ns"
  have "String.explode n \<in> set (prefixes (String.explode n))" by simp
  hence "n \<in> set (prefixes_lit n)"
    unfolding prefixes_lit_def
    using String.implode_explode_eq by (metis image_eqI list.set_map)
  thus "n \<in> set (all_prefixes ns)" using a unfolding all_prefixes_def by auto
qed

lemma fresh_name_correct: "fresh_name ns t \<notin> set ns"
  by (rule safe_suffix_correct)

lemma fresh_prefix_correct: "fresh_prefix ns t + x \<notin> set ns"
proof
  assume a: "fresh_prefix ns t + x \<in> set ns"
  have eq: "fresh_prefix ns t + x = safe_suffix (all_prefixes ns) t + (STR ''_'' + x)"
    unfolding fresh_prefix_def by (simp add: add.assoc)
  have "safe_suffix (all_prefixes ns) t \<in> set (all_prefixes ns)"
    using all_prefixesI[OF a eq] .
  thus False using safe_suffix_correct by blast
qed

lemma fresh_prefix_notin: "fresh_prefix ns t \<notin> set ns"
proof
  assume a: "fresh_prefix ns t \<in> set ns"
  have eq: "fresh_prefix ns t = safe_suffix (all_prefixes ns) t + STR ''_''"
    by (simp add: fresh_prefix_def)
  have "safe_suffix (all_prefixes ns) t \<in> set (all_prefixes ns)"
    using all_prefixesI[OF a eq] .
  thus False using safe_suffix_correct by blast
qed

lemma dist_fresh_prefix:
  assumes "distinct xs"
  shows "distinct (map (\<lambda>x. fresh_prefix ns t + x) xs)"
  using assms by (simp add: distinct_map inj_on_def inj_prepend[unfolded inj_def])

(* indexed generated names: a base string with a trailing decimal index *)

text \<open>A base name decorated with a trailing \<open>_<decimal index>\<close>, and the matching strip.
  Since \<open>_\<close> never occurs inside \<^term>\<open>show (i :: nat)\<close> (\<open>notin_show_nat\<close>), the last \<open>_\<close>
  of an \<open>idx_name\<close> is exactly the separator: \<open>strip_idx\<close> recovers the base
  unconditionally (the base may itself contain underscores; no width bound is needed), and
  equal encodings force both equal bases and equal indices.\<close>

definition idx_name :: "String.literal \<Rightarrow> nat \<Rightarrow> String.literal" where
  "idx_name s i \<equiv> s + STR ''_'' + String.implode (show i)"

definition strip_idx :: "String.literal \<Rightarrow> String.literal" where
  "strip_idx s \<equiv> String.implode
     (rev (drop 1 (dropWhile (\<lambda>c. c \<noteq> CHR ''_'') (rev (String.explode s)))))"

lemma strip_idx_idx_name [simp]: "strip_idx (idx_name s i) = s"
proof -
  have expl_us: "String.explode (STR ''_'') = [CHR ''_'']" by code_simp
  have expl_show: "String.explode (String.implode (show (n::nat))) = show n" for n
    using show_no_digit7
    by (simp add: String.ascii_of_idem list.map_ident_strong)
  have e: "rev (String.explode (idx_name s i))
             = rev (show i) @ ([CHR ''_''] @ rev (String.explode s))"
    unfolding idx_name_def
    by (simp add: plus_literal.rep_eq expl_us expl_show del: String.explode_implode_eq)
  have dw: "dropWhile (\<lambda>c. c \<noteq> CHR ''_'') (rev (String.explode (idx_name s i)))
              = [CHR ''_''] @ rev (String.explode s)"
  proof -
    have "dropWhile (\<lambda>c. c \<noteq> CHR ''_'') (rev (show i) @ ([CHR ''_''] @ rev (String.explode s)))
            = dropWhile (\<lambda>c. c \<noteq> CHR ''_'') ([CHR ''_''] @ rev (String.explode s))"
      using notin_show_nat[of i] by (intro dropWhile_append2) auto
    thus ?thesis using e by simp
  qed
  show ?thesis unfolding strip_idx_def
    by (simp add: dw)
qed

lemma idx_name_inj_base:
  assumes "idx_name a d = idx_name b e"
  shows "a = b"
  using assms[THEN arg_cong[where f = strip_idx]] by simp

lemma idx_name_inj_idx:
  assumes "idx_name a d = idx_name b e"
  shows "d = e"
proof -
  have ab: "a = b" using idx_name_inj_base[OF assms] .
  have "a + STR ''_'' + String.implode (show d) = a + STR ''_'' + String.implode (show e)"
    using assms ab unfolding idx_name_def by simp
  thus ?thesis using inj_show_prepend[of "a + STR ''_''"] by (auto simp: inj_def)
qed

lemma inj_idx_name: "inj (idx_name s)"
  by (rule injI) (rule idx_name_inj_idx)

lemma distinct_idx_names:
  assumes "distinct is"
  shows "distinct (map (idx_name s) is)"
  using assms by (simp add: distinct_map inj_on_def inj_idx_name[unfolded inj_def])

text \<open>Every name carrying an underscore-joined infix is nonempty; in particular every
  \<^const>\<open>idx_name\<close> is, which discharges the nonempty-name side conditions structurally.\<close>

lemma underscore_infix_nonempty: "a + STR ''_'' + b \<noteq> STR ''''"
proof -
  have expl_us: "String.explode (STR ''_'') = [CHR ''_'']" by code_simp
  have "String.explode (a + STR ''_'' + b) = String.explode a @ [CHR ''_''] @ String.explode b"
    by (simp add: plus_literal.rep_eq expl_us)
  hence "String.explode (a + STR ''_'' + b) \<noteq> []" by simp
  thus ?thesis by (metis zero_literal.rep_eq)
qed

corollary idx_name_nonempty: "idx_name s i \<noteq> STR ''''"
  unfolding idx_name_def by (rule underscore_infix_nonempty)


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

lemma distinct_strings_prefix: "prefix (distinct_strings n) (distinct_strings (n+k))"
  using distinct_strings_def nat_range_prefix map_mono_prefix by metis


context includes literal.lifting
begin

lift_definition distinct_strings_lit :: "nat \<Rightarrow> String.literal list" is distinct_strings
  by (simp add: distinct_strings_def list_all_iff show_no_digit7)

lemma distinct_strings_lit_eq [code]:
  "distinct_strings_lit n = map String.implode (distinct_strings n)"
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

lemma distinct_strings_lit_prefix:
  "prefix (distinct_strings_lit n) (distinct_strings_lit (n+k))"
  unfolding distinct_strings_lit_eq
  using distinct_strings_prefix map_mono_prefix by metis

end


end
