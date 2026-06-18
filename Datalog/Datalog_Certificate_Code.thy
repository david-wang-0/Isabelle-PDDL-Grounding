theory Datalog_Certificate_Code
  imports Datalog_Certificate
begin

section \<open>Executable refinement of the certificate checker\<close>

text \<open>The abstract checker of \<^theory>\<open>Datalog_Certification.Datalog_Certificate\<close> quantifies over the
  program \<open>P\<close> and universe \<open>U\<close> as \<^emph>\<open>sets\<close> and witnesses foundedness with an abstract \<open>\<exists>rank\<close>.
  This theory adds the \<open>[code]\<close>-executable refinement: a left-to-right ordered-certificate scan for
  foundedness, list-presentation checks for rule-validity / closure that enumerate
  \<^const>\<open>cls_substs\<close> (as the forward-chaining evaluator's \<open>fireable_heads\<close> does), and the assembled
  \<open>dl_certified_model_exec\<close> with its soundness bridge to the abstract checker (hence, via
  \<open>dl_certified_model_correct\<close>, to \<^const>\<open>datalog_prog.derivable\<close>). Only the soundness
  direction (exec \<open>\<Longrightarrow>\<close> abstract) is needed for trust.\<close>

subsection \<open>Executable foundedness (ordered-certificate scan)\<close>

text \<open>\<^bold>\<open>Executable foundedness\<close> (\<open>dl_founded_exec\<close>): the ordered-certificate refinement of
  \<^const>\<open>dl_founded\<close>. The untrusted engine emits the rules in derivation (topological) order; the
  checker scans them left to right, requiring each rule's body to lie among the heads of the
  \<^emph>\<open>strictly earlier\<close> rules. This is decidable (no \<open>\<exists>rank\<close>) and refines \<^const>\<open>dl_founded\<close>
  with the rank taken to be a rule's position in the list (a body fact, being an earlier head, has a
  strictly smaller first-occurrence index). The verified cycle-detecting DFS that reconstructs the
  rank from an \<^emph>\<open>unordered\<close> certificate is a further, independent refinement onto the same
  \<^const>\<open>dl_founded\<close>.\<close>

fun dl_founded_scan :: "('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_ground_rule list \<Rightarrow> bool" where
  "dl_founded_scan acc [] = True"
| "dl_founded_scan acc (r # rs) =
     (list_all (\<lambda>b. b \<in> set acc) (gr_body r) \<and> dl_founded_scan (gr_head r # acc) rs)"

definition dl_founded_exec :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_founded_exec c = dl_founded_scan [] (dl_rules c)"

declare dl_founded_scan.simps [code] dl_founded_exec_def [code]

text \<open>Locality of the scan: after a successful scan, rule \<open>i\<close>'s body lies in the initial
  accumulator together with the heads of the rules strictly before \<open>i\<close>.\<close>
lemma dl_founded_scan_body:
  assumes "dl_founded_scan acc rs" and "i < length rs"
  shows "set (gr_body (rs ! i)) \<subseteq> set acc \<union> gr_head ` set (take i rs)"
  using assms
proof (induction rs arbitrary: acc i)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  show ?case
  proof (cases i)
    case 0
    have "\<forall>b \<in> set (gr_body r). b \<in> set acc"
      using Cons.prems(1) by (simp add: list.pred_set)
    then show ?thesis using 0 by auto
  next
    case (Suc k)
    have scan': "dl_founded_scan (gr_head r # acc) rs" using Cons.prems(1) by simp
    have k: "k < length rs" using Cons.prems(2) Suc by simp
    have "set (gr_body (rs ! k)) \<subseteq> set (gr_head r # acc) \<union> gr_head ` set (take k rs)"
      using Cons.IH[OF scan' k] .
    then show ?thesis using Suc by auto
  qed
qed

text \<open>The refinement: an ordered, scan-checked certificate is founded, with rank = first index.\<close>
lemma dl_founded_exec_imp_dl_founded:
  assumes "dl_founded_exec c"
  shows "dl_founded c"
proof -
  define rs where "rs = dl_rules c"
  have scan: "dl_founded_scan [] rs" using assms unfolding dl_founded_exec_def rs_def .
  define rank where
    "rank f = (LEAST i. i < length rs \<and> gr_head (rs ! i) = f)" for f
  have facts_eq: "set (dl_cert_facts c) = gr_head ` set rs"
    unfolding dl_cert_facts_def rs_def by auto
  have main: "\<exists>r \<in> set (dl_rules c). gr_head r = f \<and> set (gr_body r) \<subseteq> set (dl_cert_facts c)
                \<and> (\<forall>b \<in> set (gr_body r). rank b < rank f)"
    if f: "f \<in> set (dl_cert_facts c)" for f
  proof -
    obtain j where jP: "j < length rs \<and> gr_head (rs ! j) = f"
      using f facts_eq by (auto simp: in_set_conv_nth)
    have P: "rank f < length rs \<and> gr_head (rs ! (rank f)) = f"
      unfolding rank_def using jP by (rule LeastI)
    let ?r = "rs ! (rank f)"
    have hd: "gr_head ?r = f" using P by simp
    have rmem: "?r \<in> set (dl_rules c)" using P unfolding rs_def by simp
    have body_sub: "set (gr_body ?r) \<subseteq> gr_head ` set (take (rank f) rs)"
      using dl_founded_scan_body[OF scan, of "rank f"] P by simp
    have body_cf: "set (gr_body ?r) \<subseteq> set (dl_cert_facts c)"
    proof -
      have "set (gr_body ?r) \<subseteq> gr_head ` set rs"
        using body_sub image_mono[OF set_take_subset] by (rule subset_trans)
      then show ?thesis unfolding facts_eq .
    qed
    have rank_lt: "rank b < rank f" if b: "b \<in> set (gr_body ?r)" for b
    proof -
      have "b \<in> gr_head ` set (take (rank f) rs)" using b body_sub by blast
      then obtain r' where r': "r' \<in> set (take (rank f) rs)" and hr': "gr_head r' = b"
        by auto
      obtain m where m: "m < length (take (rank f) rs)" and rm: "take (rank f) rs ! m = r'"
        using r' by (auto simp: in_set_conv_nth)
      have mlt: "m < rank f" using m by (auto simp: min_def split: if_splits)
      have "rs ! m = r'" using rm mlt by (metis nth_take)
      then have mb: "m < length rs \<and> gr_head (rs ! m) = b" using mlt P hr' by simp
      have "rank b \<le> m" unfolding rank_def using mb by (rule Least_le)
      then show ?thesis using mlt by simp
    qed
    show ?thesis using hd rmem body_cf rank_lt by blast
  qed
  show ?thesis unfolding dl_founded_def using main by blast
qed

subsection \<open>Executable refinement of the checks\<close>

text \<open>The abstract checks quantify over the program \<open>P\<close> and universe \<open>U\<close> as \<^emph>\<open>sets\<close>. Here we add
  \<open>[code]\<close>-executable versions over \<^emph>\<open>list\<close> presentations \<open>Pl\<close> / \<open>Ul\<close> (\<open>P = set Pl\<close>, \<open>U = set Ul\<close>),
  enumerating the grounding substitutions with \<^const>\<open>cls_substs\<close> (as the forward-chaining
  evaluator's \<open>fireable_heads\<close> does), and prove each refines its set-level counterpart. Only the \<^emph>\<open>soundness\<close> direction
  (exec \<open>\<Longrightarrow>\<close> abstract) is needed for trust: an accepted executable certificate is accepted by the
  abstract checker,  hence by \<open>dl_certified_model_correct\<close> its facts are exactly the derivable
  ones.\<close>

definition dl_positive_prog_exec :: "('p, 'x, 'c) clause list \<Rightarrow> bool" where
  "dl_positive_prog_exec Pl = list_all (\<lambda>cl. list_all is_pos_rh (the_rhs cl)) Pl"

definition dl_rule_valid_exec :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_ground_rule \<Rightarrow> bool" where
  "dl_rule_valid_exec Pl Ul r =
     list_ex (\<lambda>cl. list_ex (\<lambda>\<sigma>.
        list_all (\<lambda>g. eval_guard \<sigma> g) (cls_guards cl)
        \<and> gr_head r = subst_atom \<sigma> (the_lh cl)
        \<and> set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl)))
        (cls_substs Ul cl)) Pl"

definition dl_closure_check_exec :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_closure_check_exec Pl Ul c =
     list_all (\<lambda>cl. list_all (\<lambda>\<sigma>.
        (list_all (\<lambda>g. eval_guard \<sigma> g) (cls_guards cl)
         \<and> list_all (\<lambda>a. subst_atom \<sigma> a \<in> set (dl_cert_facts c)) (cls_body_atoms cl))
        \<longrightarrow> subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c))
        (cls_substs Ul cl)) Pl"

definition dl_admissible_exec :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_admissible_exec Pl Ul c =
     (dl_positive_prog_exec Pl
      \<and> list_all (dl_rule_valid_exec Pl Ul) (dl_rules c)
      \<and> dl_closure_check_exec Pl Ul c
      \<and> dl_founded_exec c)"

definition dl_certified_model_exec :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_certified_model_exec Pl Ul M c = (dl_admissible_exec Pl Ul c \<and> set M = set (dl_cert_facts c))"

declare dl_positive_prog_exec_def [code] dl_rule_valid_exec_def [code]
        dl_closure_check_exec_def [code] dl_admissible_exec_def [code]
        dl_certified_model_exec_def [code]

text \<open>Any \<open>U\<close>-valued substitution agrees on the clause variables with a tabulated one from
  \<^const>\<open>cls_substs\<close> --- the bridge from the abstract \<open>\<forall>\<sigma>\<close> to the enumerated list.\<close>
lemma cls_substs_tabulate:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul"
  obtains \<sigma>' where "\<sigma>' \<in> set (cls_substs Ul cl)"
    and "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
proof -
  let ?\<sigma>' = "subst_of (cls_vars cl) (map \<sigma> (cls_vars cl))"
  have "?\<sigma>' \<in> set (cls_substs Ul cl)"
    unfolding cls_substs_iff
    using assms by (auto simp: image_subset_iff intro!: exI[where x = "map \<sigma> (cls_vars cl)"])
  moreover have "\<forall>x \<in> set (cls_vars cl). ?\<sigma>' x = \<sigma> x"
    by (simp add: subst_of_map)
  ultimately show ?thesis using that by blast
qed

text \<open>Agreement on the clause variables transfers head, body-atom and guard instances.\<close>
lemma subst_atom_head_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
  shows "subst_atom \<sigma>' (the_lh cl) = subst_atom \<sigma> (the_lh cl)"
  using assms by (intro subst_atom_agree) (auto dest: cls_vars_head_vars)

lemma subst_atom_body_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x" and "a \<in> set (cls_body_atoms cl)"
  shows "subst_atom \<sigma>' a = subst_atom \<sigma> a"
proof (intro subst_atom_agree ballI)
  fix i x assume i: "i \<in> set (snd a)" and xi: "x \<in> set (id_vars_list i)"
  have "PosLit (fst a) (snd a) \<in> set (the_rhs cl)"
    using assms(2) cls_body_atoms_iff by blast
  moreover have "x \<in> set (rh_vars_list (PosLit (fst a) (snd a)))"
    using i xi by auto
  ultimately have "x \<in> set (cls_vars cl)" by (rule cls_vars_rhs_vars)
  then show "\<sigma>' x = \<sigma> x" using assms(1) by blast
qed

lemma eval_guard_cls_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x" and "g \<in> set (cls_guards cl)"
  shows "eval_guard \<sigma>' g = eval_guard \<sigma> g"
proof (intro eval_guard_agree ballI)
  fix x assume x: "x \<in> set (rh_vars_list g)"
  have "g \<in> set (the_rhs cl)" using assms(2) by (auto simp: cls_guards_def)
  then have "x \<in> set (cls_vars cl)" using x by (rule cls_vars_rhs_vars)
  then show "\<sigma>' x = \<sigma> x" using assms(1) by blast
qed

text \<open>\<^bold>\<open>Positivity\<close> refines.\<close>
lemma dl_positive_prog_exec_iff: "dl_positive_prog_exec Pl = dl_positive_prog (set Pl)"
  by (simp add: dl_positive_prog_exec_def dl_positive_prog_def list_all_iff)

text \<open>\<^bold>\<open>Rule validity\<close> refines: an enumerated witness is a genuine \<open>U\<close>-valued one.\<close>
lemma dl_rule_valid_exec_imp:
  assumes "dl_rule_valid_exec Pl Ul r"
  shows "dl_rule_valid (set Pl) (set Ul) r"
proof -
  obtain cl \<sigma> where
    cl: "cl \<in> set Pl" and
    \<sigma>: "\<sigma> \<in> set (cls_substs Ul cl)" and
    g: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g" and
    hd: "gr_head r = subst_atom \<sigma> (the_lh cl)" and
    bd: "set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl))"
    using assms unfolding dl_rule_valid_exec_def by (auto simp: list_ex_iff list_all_iff)
  have "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul"
    using \<sigma> by (blast dest: cls_substs_rangeD)
  then show ?thesis using cl g hd bd unfolding dl_rule_valid_def by blast
qed

text \<open>\<^bold>\<open>Closure check\<close> refines: an arbitrary \<open>U\<close>-valued substitution is handled via its tabulated
  agree-partner.\<close>
lemma dl_closure_check_exec_imp:
  assumes "dl_closure_check_exec Pl Ul c"
  shows "dl_closure_check (set Pl) (set Ul) c"
  unfolding dl_closure_check_def
proof (intro ballI allI impI)
  fix cl \<sigma>
  assume cl: "cl \<in> set Pl"
    and rng: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul"
    and hyp: "(\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
              \<and> (\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set (dl_cert_facts c))"
  obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> set (cls_substs Ul cl)"
    and ag: "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
    using cls_substs_tabulate[OF rng] by blast
  have gd: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma>' g"
    using hyp ag by (simp add: eval_guard_cls_cong)
  have bd: "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma>' a \<in> set (dl_cert_facts c)"
    using hyp ag by (simp add: subst_atom_body_cong)
  have "subst_atom \<sigma>' (the_lh cl) \<in> set (dl_cert_facts c)"
    using assms cl \<sigma>' gd bd unfolding dl_closure_check_exec_def by (auto simp: list_all_iff)
  then show "subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c)"
    using subst_atom_head_cong[OF ag] by simp
qed

text \<open>\<^bold>\<open>Admissibility\<close> and the \<^bold>\<open>model-checking entry point\<close> refine, assembling the four checks.\<close>
lemma dl_admissible_exec_imp:
  assumes "dl_admissible_exec Pl Ul c"
  shows "dl_admissible (set Pl) (set Ul) c"
proof -
  have pos: "dl_positive_prog_exec Pl"
    and rv: "list_all (dl_rule_valid_exec Pl Ul) (dl_rules c)"
    and cc: "dl_closure_check_exec Pl Ul c"
    and fd: "dl_founded_exec c"
    using assms unfolding dl_admissible_exec_def by auto
  have "dl_positive_prog (set Pl)" using pos by (simp add: dl_positive_prog_exec_iff)
  moreover have "\<forall>r \<in> set (dl_rules c). dl_rule_valid (set Pl) (set Ul) r"
    using rv by (auto simp: list_all_iff intro: dl_rule_valid_exec_imp)
  moreover have "dl_closure_check (set Pl) (set Ul) c"
    using cc by (rule dl_closure_check_exec_imp)
  moreover have "dl_founded c" using fd by (rule dl_founded_exec_imp_dl_founded)
  ultimately show ?thesis unfolding dl_admissible_def by blast
qed

theorem dl_certified_model_exec_imp:
  assumes "dl_certified_model_exec Pl Ul M c"
  shows "dl_certified_model (set Pl) (set Ul) M c"
  using assms dl_admissible_exec_imp
  unfolding dl_certified_model_exec_def dl_certified_model_def by blast

text \<open>\<^bold>\<open>Capstone (executable):\<close> an accepted executable certificate's facts are exactly the derivable
  facts of the program.\<close>
corollary dl_certified_model_exec_correct:
  assumes "dl_certified_model_exec Pl Ul M c"
  shows "set M = {f. datalog_prog.derivable (set Ul) (set Pl) f}"
  using dl_certified_model_correct[OF dl_certified_model_exec_imp[OF assms]] .

end
