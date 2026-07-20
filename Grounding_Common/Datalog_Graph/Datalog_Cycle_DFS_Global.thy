theory Datalog_Cycle_DFS_Global
  imports Datalog_Cycle_DFS
begin

section \<open>Approach 1 (WIP): a single O(V+E) directed-cycle sweep with an explicit on-stack set\<close>

text \<open>\<^const>\<open>dl_acyclic_dfs\<close> runs \<^const>\<open>find_dircycle\<close> from every fact index with a fresh state
  (quadratic), and each step recomputes the RBT set difference \<open>seen -\<^sub>G finished\<close> for the back-edge
  test. This variant does one sweep sharing \<open>seen\<close> across roots and maintains the on-stack (gray) set
  \<open>unf\<close> incrementally, so the back-edge test is a single \<^const>\<open>isin\<close> membership. Correctness
  (\<open>= dl_acyclic_dfs\<close>) is the remaining obligation.\<close>

type_synonym vs = "(nat \<times> color) tree"

record dfs_gs =
  work :: "(nat \<times> nat list) list"   \<comment> \<open>stack of (vertex, its still-unprocessed out-neighbours as a list)\<close>
  gs_seen :: "vs"             \<comment> \<open>visited (gray or black)\<close>
  gs_unf  :: "vs"             \<comment> \<open>on the current DFS stack (gray)\<close>
  gs_cyc  :: bool

text \<open>The neighbours of each pushed vertex are materialised ONCE into a list (\<^const>\<open>Tree2.inorder\<close> of
  the adjacency vset) and iterated by head-pop, so a step is \<open>O(1)\<close> list work plus one \<^const>\<open>isin\<close>.
  The earlier draft re-\<^const>\<open>sel\<close>ed the neighbour vset per edge (min-selection is linear in the vset),
  which made the single sweep slower than the per-vertex \<^const>\<open>dl_acyclic_dfs\<close>; iterating a list fixes
  that. \<open>adj\<close> is the neighbour-list function, closed over the once-built adjacency map \<open>g\<close>.\<close>

fun dfs_fuel :: "nat \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> dfs_gs \<Rightarrow> dfs_gs" where
  "dfs_fuel 0 adj s = s"
| "dfs_fuel (Suc k) adj s =
     (if gs_cyc s then s else
      case work s of
        [] \<Rightarrow> s
      | (v, ns) # rest \<Rightarrow>
          (case ns of
             [] \<Rightarrow> dfs_fuel k adj (s \<lparr> work := rest, gs_unf := RBT_Set.delete v (gs_unf s) \<rparr>)
           | w # ns' \<Rightarrow>
                 (if isin (gs_unf s) w then s \<lparr> gs_cyc := True \<rparr>
                  else if isin (gs_seen s) w then dfs_fuel k adj (s \<lparr> work := (v, ns') # rest \<rparr>)
                  else dfs_fuel k adj (s \<lparr> work := (w, adj w) # (v, ns') # rest,
                                         gs_seen := RBT_Set.insert w (gs_seen s),
                                         gs_unf := RBT_Set.insert w (gs_unf s) \<rparr>))))"

definition dl_acyclic_dfs_global :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_acyclic_dfs_global c =
     (let g = dep_adjmap c; n = length (dl_cert_facts c);
          adj = (\<lambda>w. Tree2.inorder (neighbourhood g w));
          fuel = 2 * n + length (nat_edges c) + 1;
          fin = foldl (\<lambda>s r.
                  if gs_cyc s \<or> isin (gs_seen s) r then s
                  else dfs_fuel fuel adj (s \<lparr> work := [(r, adj r)],
                                            gs_seen := RBT_Set.insert r (gs_seen s),
                                            gs_unf := RBT_Set.insert r vset_empty \<rparr>))
                \<lparr> work = [], gs_seen = vset_empty, gs_unf = vset_empty, gs_cyc = False \<rparr>
                [0..<n]
      in \<not> gs_cyc fin)"

subsection \<open>Correctness of the global sweep\<close>

text \<open>Soundness --- the only direction needed to \<^emph>\<open>use\<close> the check: a sweep that reports no back edge
  means the support graph really is acyclic, so \<^const>\<open>dl_founded\<close> holds just as for the per-vertex
  \<^const>\<open>dl_acyclic_dfs\<close>. (Completeness --- that the sweep accepts a genuinely acyclic certificate --- is
  not required for soundness of the grounder; it is exhibited by evaluation on the examples below.)
  The obligation is the classical 3-colour DFS fact: on a cyclic graph the shared-\<open>seen\<close> sweep meets an
  edge into the on-stack (gray) set, i.e. sets \<^term>\<open>gs_cyc\<close>.\<close>

subsection \<open>Plumbing: RBT-set \<^const>\<open>RBT_Set.delete\<close>, adjacency lists, edge-index range\<close>

text \<open>\<^const>\<open>RBT_Set.delete\<close> preserves the vset invariant and removes exactly one element
  (the \<^const>\<open>RBT_Set.insert\<close> analogues \<open>rbt_insert_inv\<close> / \<open>rbt_insert_set\<close> live in
  \<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS\<close>).\<close>

lemma rbt_delete_inv:
  assumes "vset_inv t"
  shows "vset_inv (RBT_Set.delete x t)"
proof -
  have c: "invc t" and h: "invh t" and b: "Tree2.bst t"
    using assms by (auto simp: vset_inv_def)
  note invd = inv_del[OF h c]
  have "invh (RBT_Set.delete x t)"
    using invd by (simp add: RBT_Set.delete_def invh_paint)
  moreover have "invc (RBT_Set.delete x t)"
    using invd by (cases "color t") (auto simp: RBT_Set.delete_def invc2I)
  moreover have "Tree2.bst (RBT_Set.delete x t)"
  proof -
    have s: "sorted (Tree2.inorder t)" using b by (simp add: bst_iff_sorted_inorder)
    have "Tree2.inorder (RBT_Set.delete x t) = del_list x (Tree2.inorder t)"
      using s by (rule RBT_Set.inorder_delete)
    thus ?thesis using s by (simp add: bst_iff_sorted_inorder sorted_del_list)
  qed
  ultimately show ?thesis by (simp add: vset_inv_def)
qed

lemma rbt_delete_set:
  assumes "vset_inv t"
  shows "t_set (RBT_Set.delete x t) = t_set t - {x}"
proof -
  have b: "Tree2.bst t" using assms by (auto simp: vset_inv_def)
  hence s: "sorted (Tree2.inorder t)" by (simp add: bst_iff_sorted_inorder)
  have "t_set (RBT_Set.delete x t) = set (Tree2.inorder (RBT_Set.delete x t))"
    by (simp add: Tree2.set_inorder)
  also have "\<dots> = set (del_list x (Tree2.inorder t))"
    using s by (simp add: RBT_Set.inorder_delete)
  also have "\<dots> = set (Tree2.inorder t) - {x}"
    using s by (simp add: set_del_list)
  also have "\<dots> = t_set t - {x}"
    by (simp add: Tree2.set_inorder)
  finally show ?thesis .
qed

text \<open>The materialised neighbour list of \<^const>\<open>dep_adjmap\<close> lists exactly the out-neighbours of a
  vertex in the natural-number edge set.\<close>

lemma adj_set:
  "set (Tree2.inorder (neighbourhood (dep_adjmap c) w)) = {v. (w, v) \<in> set (nat_edges c)}"
  by (simp add: dep_adjmap_def Tree2.set_inorder a_graph_neighbourhood)

text \<open>Under \<^const>\<open>dl_body_closed\<close> every endpoint of a natural-number edge is a fact index below the
  number of certified facts.\<close>

lemma nat_edges_endpoint_lt:
  assumes "dl_body_closed c" and "(a, b) \<in> set (nat_edges c)"
  shows "a < length (dl_cert_facts c)"
    and "b < length (dl_cert_facts c)"
proof -
  obtain u v where uv: "(u, v) \<in> dl_dep_graph c" and ab: "a = fact_idx c u" "b = fact_idx c v"
    using assms(2) by (auto simp: set_nat_edges)
  have "u \<in> set (dl_cert_facts c)" and "v \<in> set (dl_cert_facts c)"
    using assms(1) uv by (auto dest: dl_dep_graph_vertex_cert_fact)
  thus "a < length (dl_cert_facts c)" and "b < length (dl_cert_facts c)"
    using ab by (auto simp: fact_idx_def idx_of_less)
qed

text \<open>The mathematical core (completeness of the shared-\<open>seen\<close> 3-colour sweep): a global sweep that
  reports no back edge witnesses that the natural-number support graph \<^term>\<open>set (nat_edges c)\<close> is
  acyclic. Everything else is relabelling.\<close>

lemma global_sweep_acyclic:
  assumes bc: "dl_body_closed c" and dfs: "dl_acyclic_dfs_global c"
  shows "acyclic (set (nat_edges c))"
  sorry

lemma dl_acyclic_dfs_global_imp_acyclic:
  assumes bc: "dl_body_closed c" and dfs: "dl_acyclic_dfs_global c"
  shows "acyclic (dl_dep_graph c)"
proof (rule ccontr)
  assume "\<not> acyclic (dl_dep_graph c)"
  hence "\<not> acyclic (set (nat_edges c))"
    by (rule not_acyclic_dep_graph_imp_nat_edges)
  moreover have "acyclic (set (nat_edges c))"
    using bc dfs by (rule global_sweep_acyclic)
  ultimately show False by blast
qed

theorem dl_acyclic_dfs_global_imp_dl_founded:
  assumes "dl_body_closed c" and "dl_acyclic_dfs_global c"
  shows "dl_founded c"
  using acyclic_dep_graph_imp_dl_founded[OF assms(1) dl_acyclic_dfs_global_imp_acyclic[OF assms]] .

subsection \<open>A global-DFS-founded executable certified-model check\<close>

text \<open>The executable admissibility check with its foundedness conjunct discharged by the fast
  single-sweep \<^const>\<open>dl_acyclic_dfs_global\<close> instead of the per-vertex \<^const>\<open>dl_acyclic_dfs\<close>
  (\<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS\<close>) or the ordered linear scan \<^const>\<open>dl_founded_exec\<close>
  (\<^theory>\<open>Datalog_Certification.Datalog_Certificate_Code\<close>). The other three conjuncts are reused
  verbatim; \<^const>\<open>dl_body_closed\<close> together with \<^const>\<open>dl_acyclic_dfs_global\<close> discharge
  \<^const>\<open>dl_founded\<close> (\<open>dl_acyclic_dfs_global_imp_dl_founded\<close>).\<close>

definition dl_admissible_gdfs :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_admissible_gdfs Pl Ul c =
     (dl_positive_prog_exec Pl
      \<and> list_all (dl_rule_valid_exec Pl Ul) (dl_rules c)
      \<and> dl_closure_check_exec Pl Ul c
      \<and> dl_body_closed c
      \<and> dl_acyclic_dfs_global c)"

lemma dl_admissible_gdfs_imp:
  assumes "dl_admissible_gdfs Pl Ul c"
  shows "dl_admissible (set Pl) (set Ul) c"
proof -
  have pos: "dl_positive_prog_exec Pl"
    and rv: "list_all (dl_rule_valid_exec Pl Ul) (dl_rules c)"
    and cc: "dl_closure_check_exec Pl Ul c"
    and bc: "dl_body_closed c"
    and ac: "dl_acyclic_dfs_global c"
    using assms unfolding dl_admissible_gdfs_def by auto
  have "dl_positive_prog (set Pl)" using pos by (simp add: dl_positive_prog_exec_iff)
  moreover have "\<forall>r \<in> set (dl_rules c). dl_rule_valid (set Pl) (set Ul) r"
    using rv by (auto simp: list_all_iff intro: dl_rule_valid_exec_imp)
  moreover have "dl_closure_check (set Pl) (set Ul) c"
    using cc by (rule dl_closure_check_exec_imp)
  moreover have "dl_founded c" using dl_acyclic_dfs_global_imp_dl_founded[OF bc ac] .
  ultimately show ?thesis unfolding dl_admissible_def by blast
qed

definition dl_certified_model_gdfs :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_certified_model_gdfs Pl Ul M c = (dl_admissible_gdfs Pl Ul c \<and> set M = set (dl_cert_facts c))"

theorem dl_certified_model_gdfs_imp:
  assumes "dl_certified_model_gdfs Pl Ul M c"
  shows "dl_certified_model (set Pl) (set Ul) M c"
  using assms dl_admissible_gdfs_imp
  unfolding dl_certified_model_gdfs_def dl_certified_model_def by blast

declare dl_admissible_gdfs_def [code] dl_certified_model_gdfs_def [code]

subsection \<open>Examples: the running edge/path DAG and a 2-cycle\<close>

text \<open>The single sweep agrees with the per-vertex DFS on both examples: \<open>True\<close> on the edge/path DAG,
  \<open>False\<close> on the mutually-supporting 2-cycle \<open>p(1) \<leftrightarrow> q(1)\<close>.\<close>
value "dl_acyclic_dfs_global ex_cert"
value "dl_acyclic_dfs_global cyc_cert"

end

