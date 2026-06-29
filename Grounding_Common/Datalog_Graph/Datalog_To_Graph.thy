theory Datalog_To_Graph
  imports
    Graph_Topological_Order
    Datalog_Certification.Datalog_Certificate
begin

section \<open>The support graph of a datalog certificate\<close>

text \<open>We convert a datalog certificate \<^typ>\<open>('p, 'c) dl_certificate\<close> to the graph library's
  \<^typ>\<open>('p, 'c) dl_fact dgraph\<close> format: one vertex per certified fact, and an edge \<open>b \<rightarrow> f\<close>
  whenever some supplied rule derives head \<open>f\<close> from a body containing \<open>b\<close> (read: ``\<open>b\<close> must be
  derived before \<open>f\<close>''). A topological numbering of this \<^emph>\<open>support graph\<close> is exactly a foundedness
  rank (a \<open>dl_rank\<close>), so an acyclic support graph yields \<^const>\<open>dl_founded\<close>, and — via the
  generic checker's \<open>dl_founded_imp_derivable\<close> — derivability of every certified fact.\<close>

definition dl_dep_graph :: "('p, 'c) dl_certificate \<Rightarrow> ('p, 'c) dl_fact dgraph" where
  "dl_dep_graph c =
     (\<Union>r \<in> set (dl_rules c). (\<lambda>b. (b, gr_head r)) ` set (gr_body r))"

lemma dl_dep_graph_edgeI:
  assumes "r \<in> set (dl_rules c)" and "b \<in> set (gr_body r)"
  shows "(b, gr_head r) \<in> dl_dep_graph c"
  using assms by (auto simp: dl_dep_graph_def)

lemma dl_dep_graph_edgeE:
  assumes "(b, f) \<in> dl_dep_graph c"
  obtains r where "r \<in> set (dl_rules c)" and "gr_head r = f" and "b \<in> set (gr_body r)"
  using assms by (auto simp: dl_dep_graph_def)

text \<open>The support graph is finite: the rules are a list, and each rule contributes finitely many
  edges (one per body fact).\<close>

lemma finite_dl_dep_graph: "finite (dl_dep_graph c)"
  by (auto simp: dl_dep_graph_def)

section \<open>Topological order of the support graph \<open>\<Longrightarrow>\<close> foundedness\<close>

text \<open>Foundedness lets each fact reuse \<^emph>\<open>any\<close> of its justifying rules, provided that rule's body
  lies inside the certified facts. The mild side condition \<open>dl_body_closed\<close> — every rule's body is
  certified — holds for the certificates the project produces (each body fact is an earlier head),
  and lets the support-graph numbering serve directly as the foundedness rank.\<close>

definition dl_body_closed :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_body_closed c \<longleftrightarrow> (\<forall>r \<in> set (dl_rules c). set (gr_body r) \<subseteq> set (dl_cert_facts c))"

lemma top_num_imp_dl_founded:
  assumes bc: "dl_body_closed c"
    and tn: "has_top_num (dl_dep_graph c)"
  shows "dl_founded c"
proof -
  from tn obtain \<tau> where \<tau>: "top_num (dl_dep_graph c) \<tau>"
    by (auto simp: has_top_num_def)
  show ?thesis
    unfolding dl_founded_def
  proof (intro exI[where x = \<tau>] ballI)
    fix f assume "f \<in> set (dl_cert_facts c)"
    then obtain r where r: "r \<in> set (dl_rules c)" and hd: "gr_head r = f"
      by (auto simp: dl_cert_facts_def)
    have body_facts: "set (gr_body r) \<subseteq> set (dl_cert_facts c)"
      using bc r by (auto simp: dl_body_closed_def)
    have "\<tau> b < \<tau> f" if b: "b \<in> set (gr_body r)" for b
    proof -
      have "(b, f) \<in> dl_dep_graph c"
        using dl_dep_graph_edgeI[OF r b] hd by simp
      thus ?thesis using top_numD[OF \<tau>] by blast
    qed
    with r hd body_facts
    show "\<exists>r \<in> set (dl_rules c). gr_head r = f
            \<and> set (gr_body r) \<subseteq> set (dl_cert_facts c)
            \<and> (\<forall>b \<in> set (gr_body r). \<tau> b < \<tau> f)"
      by blast
  qed
qed

section \<open>Acyclic support graph \<open>\<Longrightarrow>\<close> foundedness (and derivability)\<close>

theorem acyclic_dep_graph_imp_dl_founded:
  assumes bc: "dl_body_closed c"
    and ac: "acyclic (dl_dep_graph c)"
  shows "dl_founded c"
  using top_num_imp_dl_founded[OF bc]
        finite_acyclic_imp_has_top_num[OF finite_dl_dep_graph ac]
  by blast

text \<open>Equivalently, phrased with the library's directed \<^const>\<open>cycle\<close> predicate: a support graph
  with no cycle is founded.\<close>

corollary no_cycle_dep_graph_imp_dl_founded:
  assumes bc: "dl_body_closed c"
    and nc: "\<nexists>p. cycle (dl_dep_graph c) p"
  shows "dl_founded c"
  using acyclic_dep_graph_imp_dl_founded[OF bc]
        no_cycle_iff_acyclic[of "dl_dep_graph c"] nc
  by blast

text \<open>Chaining with the generic checker's soundness theorem: under rule validity, an acyclic
  support graph certifies that every fact of the certificate is genuinely derivable.\<close>

corollary acyclic_dep_graph_imp_derivable:
  assumes valid: "\<forall>r \<in> set (dl_rules c). dl_rule_valid P U r"
    and bc: "dl_body_closed c"
    and ac: "acyclic (dl_dep_graph c)"
    and f: "f \<in> set (dl_cert_facts c)"
  shows "datalog_prog.derivable U P f"
  using dl_founded_imp_derivable[OF valid acyclic_dep_graph_imp_dl_founded[OF bc ac] f] .

section \<open>Slotting acyclicity into the kernel's admissibility / certified-model checks\<close>

text \<open>The kernel's \<^const>\<open>dl_admissible\<close> / \<^const>\<open>dl_certified_model\<close> carry the abstract,
  non-executable \<^const>\<open>dl_founded\<close> as their only non-decidable conjunct. Replacing it by acyclicity
  of the support graph yields the same admissibility from checks a (future) verified
  cycle-detecting DFS can discharge --- the other conjuncts (\<^const>\<open>dl_positive_prog\<close>,
  \<^const>\<open>dl_rule_valid\<close>, \<^const>\<open>dl_closure_check\<close>) are already decidable.\<close>

lemma dl_admissible_via_acyclic:
  assumes "dl_positive_prog P"
    and "\<forall>r \<in> set (dl_rules c). dl_rule_valid P U r"
    and "dl_closure_check P U c"
    and "dl_body_closed c"
    and "acyclic (dl_dep_graph c)"
  shows "dl_admissible P U c"
  unfolding dl_admissible_def
  using assms acyclic_dep_graph_imp_dl_founded[OF assms(4,5)] by blast

lemma dl_certified_model_via_acyclic:
  assumes "dl_positive_prog P"
    and "\<forall>r \<in> set (dl_rules c). dl_rule_valid P U r"
    and "dl_closure_check P U c"
    and "dl_body_closed c"
    and "acyclic (dl_dep_graph c)"
    and "set M = set (dl_cert_facts c)"
  shows "dl_certified_model P U M c"
  unfolding dl_certified_model_def
  using dl_admissible_via_acyclic[OF assms(1,2,3,4,5)] assms(6) by blast

text \<open>\<^bold>\<open>Sufficient, not necessary.\<close> The support graph \<^const>\<open>dl_dep_graph\<close> carries an edge for
  \<^emph>\<open>every\<close> rule, whereas \<^const>\<open>dl_founded\<close> only needs \<^emph>\<open>one\<close> justifying rule per fact whose body
  ranks below it. So \<open>has_top_num (dl_dep_graph c) \<Longrightarrow> dl_founded c\<close> holds (above), but the converse
  fails in general: a certificate with a redundant, cyclically-supported extra rule can still be
  founded via its other rules. Acyclicity of the full support graph is therefore a \<^emph>\<open>sufficient\<close>
  check (and, for single-justification certificates such as Nemo's, the expected one) --- not a
  characterisation of \<^const>\<open>dl_founded\<close>.\<close>

end
