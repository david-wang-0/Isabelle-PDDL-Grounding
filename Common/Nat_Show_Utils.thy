theory Nat_Show_Utils
imports "Show.Show_Instances"
begin

text \<open> By Maximlian Shäffeler:
https://isabelle.zulipchat.com/#narrow/channel/238552-Beginner-Questions/topic/String.20inequality.20with.20show/near/500270718 \<close>

lemma div_mod_imp_eq: \<open>(a :: nat) div n = b div n \<Longrightarrow> a mod n = b mod n \<Longrightarrow> a = b\<close>
  by (metis div_mult_mod_eq)

lemma string_of_digit_inj:
  assumes \<open>a \<noteq> (b :: nat)\<close> \<open>a < 10\<close> \<open>b < 10\<close>
  shows \<open>string_of_digit a \<noteq> string_of_digit b\<close>
proof -
  have \<open>a \<in> {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}\<close>
    using \<open>a < 10\<close>
    by auto
  thus ?thesis
    using \<open>a \<noteq> b\<close> \<open>b < 10\<close>
    by auto (auto split: if_splits simp: string_of_digit_def)
qed

lemma shows_prec_nat: \<open>shows_prec p n '''' = (if n < 10 then string_of_digit n
    else shows_prec p (n div 10) '''' @ string_of_digit (n mod 10))\<close>
  unfolding shows_prec_nat_def
proof (induction p n rule: showsp_nat.induct)
  case (1 p n)
  then show ?case
    unfolding shows_string_def showsp_nat.simps[of p n]
    by (auto simp: shows_prec_append[symmetric] shows_prec_nat_def[symmetric])
qed

lemma show_nat: \<open>show n = (if n < 10 then string_of_digit n
    else show (n div 10) @ string_of_digit (n mod 10))\<close>
  using shows_prec_nat .

lemma show_nat_induct:
  \<open>(\<And>n. (\<And>z. \<not> n < 10 \<Longrightarrow> z \<in> range (shows_string (string_of_digit (n mod 10))) \<Longrightarrow> P (n div 10)) \<Longrightarrow> P n) \<Longrightarrow> P n\<close>
  by (rule showsp_nat.induct) blast

lemma length_string_of_digit[simp]: \<open>length (string_of_digit n) = 1\<close>
  unfolding string_of_digit_def
  by auto

lemma len_show_ge10: \<open>(n :: nat) \<ge> 10 \<Longrightarrow> length (show n) \<ge> 2\<close>
  unfolding show_nat[of n] show_nat[of \<open>(n div 10)\<close>]
  by auto

lemma len_show_lt10: \<open>(n :: nat) < 10 \<Longrightarrow> length (show n) = 1\<close>
  unfolding show_nat[of n]
  by auto

lemma show_nat_inj:
  fixes a b :: nat
  assumes \<open>a \<noteq> b\<close>
  shows \<open>show a \<noteq> show b\<close>
  using assms
proof (induction a arbitrary: b rule: show_nat_induct)
  case (1 n)
  hence ?case if \<open>\<not>n < 10\<close> \<open>\<not>b < 10\<close>
    using that div_mod_imp_eq[of n 10 b] string_of_digit_inj[of \<open>n mod 10\<close> \<open>b mod 10\<close>]
    by (cases \<open>n div 10 = b div 10\<close>) (auto simp: show_nat[of n] show_nat[of b])
  moreover have ?case if \<open>n < 10\<close> \<open>b < 10\<close>
    using 1 string_of_digit_inj that
    by (auto simp: show_nat[of n] show_nat[of b])
  moreover have ?case if \<open>((n :: nat) < 10) \<noteq> ((b :: nat) < 10)\<close>
    using that len_show_ge10[of n] len_show_lt10[of b] len_show_ge10[of b] len_show_lt10[of n]
    by auto
  ultimately show ?case
    by blast
qed

text \<open> My stuff \<close>

lemma nat_induct_all [case_names 0 Suc]:
  fixes n::nat
  assumes "P 0" "\<And>n. (\<And>k. k \<le> n \<Longrightarrow> P k) \<Longrightarrow> P (Suc n)"
  shows "P n"
proof -
  have "\<And>k. k \<le> n \<Longrightarrow> P k" by (induction n) (auto simp add: le_Suc_eq assms)
  thus ?thesis by simp
qed


lemma nat_induct_10 [case_names digit0 digitN]:
  fixes n::nat
  assumes "(\<And>n. n < 10 \<Longrightarrow> P n)" "(\<And>n m. P n \<Longrightarrow> m < 10 \<Longrightarrow> P (10 * n + m))"
  shows "P n"
proof (induction n rule: nat_induct_all)
  case (Suc n)
  show "P (Suc n)"
  proof (cases)
    assume "Suc n \<ge> 10"
    with Suc show ?thesis
      using assms(2)[of "Suc n div 10" "Suc n mod 10"] by simp
  qed (simp add: assms)
qed (simp add: assms)

lemma digit_chars: "set (string_of_digit n) \<subseteq> {CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'',
  CHR ''3'', CHR ''4'', CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9''}"
  unfolding string_of_digit_def by simp

lemma show_nat_chars:
  fixes n :: nat
  shows "set (show n) \<subseteq> {CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'',
  CHR ''3'', CHR ''4'', CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9''}"
  apply (induction n rule: nat_induct_10)
  using show_nat digit_chars by simp_all

lemma notin_show_nat: "CHR ''_'' \<notin> set (show (n::nat))"
  using show_nat_chars by blast

lemma nat_show_len_mono:
  fixes i j :: nat
  assumes "i \<le> j"
  shows "length (show i) \<le> length (show j)"
proof -
  have "\<And>k. k \<le> n \<Longrightarrow> length (show k) \<le> length (show (Suc k))" for n
  proof (induction n rule: nat_induct_10)
    case (digitN n m)
    show ?case
    proof (cases "k \<ge> 10")
      case True
      from digitN have "k div 10 \<le> n" by simp
      with digitN have kih: "length (show (k div 10)) \<le> length (show (Suc (k div 10)))" by simp
      have "Suc k div 10 = k div 10 \<or> Suc k div 10 = Suc (k div 10)" by auto
      hence "show (Suc k) = show (k div 10) @ string_of_digit (Suc k mod 10) \<or>
        show (Suc k) = show (Suc (k div 10)) @ string_of_digit (Suc k mod 10)"
        using show_nat True by fastforce
      with kih show ?thesis using show_nat by fastforce
    qed (simp_all add: show_nat)
  qed (simp add: show_nat)
  hence "length (show n) \<le> length (show (Suc n))" for n by auto
  hence "length (show i) \<le> length (show (i+k))" for i k :: nat
    apply (induction k arbitrary: i)
     apply simp
    using le_trans by fastforce
  thus ?thesis using assms by (metis le_iff_add)
qed

lemma nat_show_len_nonzero:
  fixes n :: nat
  shows "length (show n) \<ge> 1"
  using show_nat by simp

end