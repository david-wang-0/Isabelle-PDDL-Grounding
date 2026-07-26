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

subsection \<open>The completeness invariant of the shared-\<open>seen\<close> sweep\<close>

text \<open>We fix the natural-number support graph as an abstract edge set \<^term>\<open>E\<close> over indices below
  \<^term>\<open>n\<close>, together with the adjacency-list function \<^term>\<open>adj\<close> materialising each vertex's
  out-neighbours (\<open>set (adj w) = {u. (w, u) \<in> E}\<close>, distinct). The DFS invariant \<^term>\<open>dfs_inv\<close>
  captures a partially-completed shared-\<open>seen\<close> 3-colour sweep: \<open>SEEN\<close>/\<open>GRAY\<close>/\<open>BLACK\<close> are the visited,
  on-stack and finished vertices, \<open>GRAY\<close> is exactly the stack's vertices, no edge runs from a finished
  to an on-stack vertex, every finished vertex's out-neighbours are already seen, and the finished
  subgraph is acyclic. On termination with no back edge, \<open>BLACK\<close> covers every index, so the whole graph
  is acyclic.\<close>

text \<open>Adding a fresh source vertex --- one that is not mentioned by an acyclic relation and points only
  outward --- keeps the relation acyclic: the new vertex has no incoming edge, so it lies on no cycle.\<close>

lemma acyclic_fresh_source:
  assumes ac: "acyclic r" and vf: "v \<notin> Field r" and vs: "v \<notin> S"
  shows "acyclic (r \<union> {v} \<times> S)"
proof -
  have vR: "v \<notin> Range (r \<union> {v} \<times> S)" using vf vs by (auto simp: Field_def)
  have step: "(a, b) \<in> r\<^sup>+ \<or> a = v" if "(a, b) \<in> (r \<union> {v} \<times> S)\<^sup>+" for a b
    using that
  proof (induction rule: trancl_induct)
    case (base y)
    thus ?case by (auto intro: r_into_trancl)
  next
    case (step y z)
    have "y \<noteq> v" using step.hyps(1) vR by (meson Range.intros tranclD2)
    hence "(y, z) \<in> r" using step.hyps(2) by auto
    thus ?case using step.IH by (auto intro: trancl_into_trancl)
  qed
  show ?thesis
  proof (rule acyclicI, intro allI notI)
    fix x assume xx: "(x, x) \<in> (r \<union> {v} \<times> S)\<^sup>+"
    have "x \<noteq> v" using xx vR by (meson Range.intros tranclD2)
    hence "(x, x) \<in> r\<^sup>+" using step[OF xx] by simp
    thus False using ac by (simp add: acyclic_def)
  qed
qed

locale dfs_gctx =
  fixes E :: "(nat \<times> nat) set" and n :: nat and adj :: "nat \<Rightarrow> nat list"
  assumes adj_set': "\<And>w. set (adj w) = {u. (w, u) \<in> E}"
      and adj_distinct: "\<And>w. distinct (adj w)"
      and E_range: "E \<subseteq> {0..<n} \<times> {0..<n}"
begin

abbreviation SEEN :: "dfs_gs \<Rightarrow> nat set" where "SEEN s \<equiv> t_set (gs_seen s)"
abbreviation GRAY :: "dfs_gs \<Rightarrow> nat set" where "GRAY s \<equiv> t_set (gs_unf s)"
abbreviation BLACK :: "dfs_gs \<Rightarrow> nat set" where "BLACK s \<equiv> t_set (gs_seen s) - t_set (gs_unf s)"
abbreviation nbr :: "nat \<Rightarrow> nat set" where "nbr v \<equiv> {u. (v, u) \<in> E}"

definition dfs_inv :: "dfs_gs \<Rightarrow> bool" where
  "dfs_inv s \<longleftrightarrow>
     vset_inv (gs_seen s)
   \<and> vset_inv (gs_unf s)
   \<and> GRAY s \<subseteq> SEEN s
   \<and> GRAY s = set (map fst (work s))
   \<and> distinct (map fst (work s))
   \<and> (\<forall>(v, ns) \<in> set (work s). set ns \<subseteq> nbr v)
   \<and> (\<forall>(v, ns) \<in> set (work s). nbr v - set ns \<subseteq> SEEN s)
   \<and> (\<forall>b \<in> BLACK s. \<forall>g \<in> GRAY s. (b, g) \<notin> E)
   \<and> (\<forall>b \<in> BLACK s. nbr b \<subseteq> SEEN s)
   \<and> acyclic (E \<inter> (BLACK s \<times> BLACK s))
   \<and> (\<forall>ss1 v ns ss2. work s = ss1 @ (v, ns) # ss2 \<longrightarrow> nbr v - set ns \<subseteq> BLACK s \<union> set (map fst ss1))
   \<and> SEEN s \<subseteq> {0..<n}"

lemma isin_tset: "vset_inv t \<Longrightarrow> isin t x = (x \<in> t_set t)"
  by (simp add: isin_set_tree vset_inv_def)

lemma dfs_inv_seeninv: "dfs_inv s \<Longrightarrow> vset_inv (gs_seen s)" by (simp add: dfs_inv_def)
lemma dfs_inv_unfinv: "dfs_inv s \<Longrightarrow> vset_inv (gs_unf s)" by (simp add: dfs_inv_def)
lemma dfs_inv_grayeq: "dfs_inv s \<Longrightarrow> GRAY s = set (map fst (work s))" by (simp add: dfs_inv_def)
lemma dfs_inv_distinct: "dfs_inv s \<Longrightarrow> distinct (map fst (work s))" by (simp add: dfs_inv_def)
lemma dfs_inv_range: "dfs_inv s \<Longrightarrow> SEEN s \<subseteq> {0..<n}" by (simp add: dfs_inv_def)
lemma dfs_inv_graysub: "dfs_inv s \<Longrightarrow> GRAY s \<subseteq> SEEN s" unfolding dfs_inv_def by (elim conjE; assumption)
lemma dfs_inv_acyc: "dfs_inv s \<Longrightarrow> acyclic (E \<inter> (BLACK s \<times> BLACK s))" unfolding dfs_inv_def by (elim conjE; assumption)
lemma dfs_inv_F:
  assumes "dfs_inv s" and "b \<in> BLACK s" and "g \<in> GRAY s"
  shows "(b, g) \<notin> E"
proof -
  have "\<forall>b \<in> BLACK s. \<forall>g \<in> GRAY s. (b, g) \<notin> E" using assms(1) unfolding dfs_inv_def by blast
  thus ?thesis using assms(2,3) by blast
qed

lemma dfs_inv_G:
  assumes "dfs_inv s" and "b \<in> BLACK s"
  shows "nbr b \<subseteq> SEEN s"
proof -
  have "\<forall>b \<in> BLACK s. nbr b \<subseteq> SEEN s" using assms(1) unfolding dfs_inv_def by blast
  thus ?thesis using assms(2) by blast
qed

lemma dfs_inv_K:
  assumes "dfs_inv s" and "work s = ss1 @ (v, ns) # ss2"
  shows "nbr v - set ns \<subseteq> BLACK s \<union> set (map fst ss1)"
proof -
  have "dfs_inv s \<Longrightarrow> \<forall>ss1 v ns ss2. work s = ss1 @ (v, ns) # ss2 \<longrightarrow> nbr v - set ns \<subseteq> BLACK s \<union> set (map fst ss1)"
    unfolding dfs_inv_def by (elim conjE; assumption)
  thus ?thesis using assms by blast
qed

lemma dfs_inv_nssub:
  assumes "dfs_inv s" and "(v, ns) \<in> set (work s)"
  shows "set ns \<subseteq> nbr v"
proof -
  have "dfs_inv s \<Longrightarrow> \<forall>(v, ns) \<in> set (work s). set ns \<subseteq> nbr v"
    unfolding dfs_inv_def by (elim conjE; assumption)
  thus ?thesis using assms by fastforce
qed

lemma dfs_inv_consumed:
  assumes "dfs_inv s" and "(v, ns) \<in> set (work s)"
  shows "nbr v - set ns \<subseteq> SEEN s"
proof -
  have "dfs_inv s \<Longrightarrow> \<forall>(v, ns) \<in> set (work s). nbr v - set ns \<subseteq> SEEN s"
    unfolding dfs_inv_def by (elim conjE; assumption)
  thus ?thesis using assms by fastforce
qed

lemma dfs_invI:
  assumes a1: "vset_inv (gs_seen s)" and a2: "vset_inv (gs_unf s)"
    and a3: "GRAY s \<subseteq> SEEN s" and a4: "GRAY s = set (map fst (work s))"
    and a5: "distinct (map fst (work s))"
    and a6: "\<And>v ns. (v, ns) \<in> set (work s) \<Longrightarrow> set ns \<subseteq> nbr v"
    and a7: "\<And>v ns. (v, ns) \<in> set (work s) \<Longrightarrow> nbr v - set ns \<subseteq> SEEN s"
    and a8: "\<And>b g. b \<in> BLACK s \<Longrightarrow> g \<in> GRAY s \<Longrightarrow> (b, g) \<notin> E"
    and a9: "\<And>b. b \<in> BLACK s \<Longrightarrow> nbr b \<subseteq> SEEN s"
    and a10: "acyclic (E \<inter> (BLACK s \<times> BLACK s))"
    and a11: "\<And>ss1 v ns ss2. work s = ss1 @ (v, ns) # ss2 \<Longrightarrow> nbr v - set ns \<subseteq> BLACK s \<union> set (map fst ss1)"
    and a12: "SEEN s \<subseteq> {0..<n}"
  shows "dfs_inv s"
  unfolding dfs_inv_def
proof (intro conjI)
  show "vset_inv (gs_seen s)" by (rule a1)
  show "vset_inv (gs_unf s)" by (rule a2)
  show "GRAY s \<subseteq> SEEN s" by (rule a3)
  show "GRAY s = set (map fst (work s))" by (rule a4)
  show "distinct (map fst (work s))" by (rule a5)
  show "\<forall>(v, ns)\<in>set (work s). set ns \<subseteq> nbr v" using a6 by fastforce
  show "\<forall>(v, ns)\<in>set (work s). nbr v - set ns \<subseteq> SEEN s" using a7 by fastforce
  show "\<forall>b\<in>BLACK s. \<forall>g\<in>GRAY s. (b, g) \<notin> E" using a8 by blast
  show "\<forall>b\<in>BLACK s. nbr b \<subseteq> SEEN s" using a9 by blast
  show "acyclic (E \<inter> (BLACK s \<times> BLACK s))" by (rule a10)
  show "\<forall>ss1 v ns ss2. work s = ss1 @ (v, ns) # ss2 \<longrightarrow> nbr v - set ns \<subseteq> BLACK s \<union> set (map fst ss1)" using a11 by blast
  show "SEEN s \<subseteq> {0..<n}" by (rule a12)
qed

text \<open>One recursive step preserves \<^term>\<open>dfs_inv\<close>. There are three recursive branches --- blackening
  a finished vertex (its work-list is exhausted), skipping an already-seen neighbour, and pushing a
  fresh white neighbour as a new gray stack frame. (The back-edge branch sets \<^term>\<open>gs_cyc\<close> and does
  not recurse; it is handled directly in the fuel lemma.)\<close>

lemma dfs_inv_blacken:
  assumes inv: "dfs_inv s" and w: "work s = (v, []) # rest"
  shows "dfs_inv (s\<lparr>work := rest, gs_unf := RBT_Set.delete v (gs_unf s)\<rparr>)"
proof -
  define s' where "s' = s\<lparr>work := rest, gs_unf := RBT_Set.delete v (gs_unf s)\<rparr>"
  have seen': "gs_seen s' = gs_seen s" by (simp add: s'_def)
  have unf': "gs_unf s' = RBT_Set.delete v (gs_unf s)" by (simp add: s'_def)
  have work': "work s' = rest" by (simp add: s'_def)
  note vseen = dfs_inv_seeninv[OF inv]
  note vunf = dfs_inv_unfinv[OF inv]
  have grayeq: "GRAY s = set (map fst (work s))" by (rule dfs_inv_grayeq[OF inv])
  have dist: "distinct (map fst (work s))" by (rule dfs_inv_distinct[OF inv])
  have vmem: "v \<in> GRAY s" using grayeq w by simp
  have vnr: "v \<notin> set (map fst rest)" using dist w by simp
  have distrest: "distinct (map fst rest)" using dist w by simp
  have SEEN': "SEEN s' = SEEN s" using seen' by simp
  have GRAY': "GRAY s' = GRAY s - {v}" using unf' rbt_delete_set[OF vunf] by simp
  have vseen_mem: "v \<in> SEEN s" using vmem dfs_inv_graysub[OF inv] by blast
  have BLACK': "BLACK s' = {v} \<union> BLACK s" using SEEN' GRAY' vseen_mem vmem by auto
  have outv_black: "nbr v \<subseteq> BLACK s" using dfs_inv_K[OF inv, of "[]" v "[]" rest] w by simp
  have vnotblack: "v \<notin> BLACK s" using vmem by simp
  have no_in: "(b, v) \<notin> E" if "b \<in> BLACK s" for b using dfs_inv_F[OF inv] that vmem by blast
  have vnr_nbr: "v \<notin> nbr v" using outv_black vnotblack by blast
  have restsub: "set (work s') \<subseteq> set (work s)" using work' w by auto
  have a1: "vset_inv (gs_seen s')" using seen' vseen by simp
  have a2: "vset_inv (gs_unf s')" using unf' rbt_delete_inv[OF vunf] by simp
  have a3: "GRAY s' \<subseteq> SEEN s'" using GRAY' SEEN' dfs_inv_graysub[OF inv] by blast
  have a4: "GRAY s' = set (map fst (work s'))" using GRAY' work' grayeq w vnr by auto
  have a5: "distinct (map fst (work s'))" using work' distrest by simp
  have a6: "set ns0 \<subseteq> nbr v0" if "(v0, ns0) \<in> set (work s')" for v0 ns0
    using dfs_inv_nssub[OF inv] that restsub by blast
  have a7: "nbr v0 - set ns0 \<subseteq> SEEN s'" if "(v0, ns0) \<in> set (work s')" for v0 ns0
    using dfs_inv_consumed[OF inv] that restsub SEEN' by blast
  have a8: "(b, g) \<notin> E" if "b \<in> BLACK s'" "g \<in> GRAY s'" for b g
  proof -
    have g_in: "g \<in> GRAY s" and g_ne: "g \<noteq> v" using that(2) GRAY' by auto
    show ?thesis
    proof (cases "b = v")
      case True
      show ?thesis
      proof
        assume "(b, g) \<in> E"
        hence "g \<in> nbr v" using True by simp
        hence "g \<in> BLACK s" using outv_black by blast
        thus False using g_in by blast
      qed
    next
      case False
      hence "b \<in> BLACK s" using that(1) BLACK' by simp
      thus ?thesis using dfs_inv_F[OF inv] g_in by blast
    qed
  qed
  have a9: "nbr b \<subseteq> SEEN s'" if "b \<in> BLACK s'" for b
  proof (cases "b = v")
    case True
    thus ?thesis using outv_black SEEN' by auto
  next
    case False
    hence "b \<in> BLACK s" using that BLACK' by simp
    thus ?thesis using dfs_inv_G[OF inv] SEEN' by blast
  qed
  have setEq: "E \<inter> (BLACK s' \<times> BLACK s') = (E \<inter> (BLACK s \<times> BLACK s)) \<union> ({v} \<times> nbr v)"
    using outv_black no_in vnr_nbr unfolding BLACK' by auto
  have a10: "acyclic (E \<inter> (BLACK s' \<times> BLACK s'))"
    unfolding setEq
  proof (rule acyclic_fresh_source)
    show "acyclic (E \<inter> (BLACK s \<times> BLACK s))" by (rule dfs_inv_acyc[OF inv])
    show "v \<notin> Field (E \<inter> (BLACK s \<times> BLACK s))" using vnotblack by (auto simp: Field_def)
    show "v \<notin> nbr v" by (rule vnr_nbr)
  qed
  have a11: "nbr v0 - set ns0 \<subseteq> BLACK s' \<union> set (map fst ss1)"
    if "work s' = ss1 @ (v0, ns0) # ss2" for ss1 v0 ns0 ss2
  proof -
    have "work s = ((v, []) # ss1) @ (v0, ns0) # ss2" using that work' w by simp
    hence "nbr v0 - set ns0 \<subseteq> BLACK s \<union> set (map fst ((v, []) # ss1))"
      by (rule dfs_inv_K[OF inv])
    thus ?thesis using BLACK' by auto
  qed
  have a12: "SEEN s' \<subseteq> {0..<n}" using SEEN' dfs_inv_range[OF inv] by simp
  show "dfs_inv (s\<lparr>work := rest, gs_unf := RBT_Set.delete v (gs_unf s)\<rparr>)"
    unfolding s'_def[symmetric]
    by (rule dfs_invI[OF a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12])
qed

lemma dfs_inv_skip:
  assumes inv: "dfs_inv s" and w: "work s = (v, u # ns') # rest"
    and useen: "u \<in> SEEN s" and ugray: "u \<notin> GRAY s"
  shows "dfs_inv (s\<lparr>work := (v, ns') # rest\<rparr>)"
proof -
  define s' where "s' = s\<lparr>work := (v, ns') # rest\<rparr>"
  have seen': "gs_seen s' = gs_seen s" by (simp add: s'_def)
  have unf': "gs_unf s' = gs_unf s" by (simp add: s'_def)
  have work': "work s' = (v, ns') # rest" by (simp add: s'_def)
  have SEENeq: "SEEN s' = SEEN s" using seen' by simp
  have GRAYeq: "GRAY s' = GRAY s" using unf' by simp
  have mapfst': "map fst (work s') = map fst (work s)" using w work' by simp
  have grayeq: "GRAY s = set (map fst (work s))" by (rule dfs_inv_grayeq[OF inv])
  have hd: "(v, u # ns') \<in> set (work s)" using w by simp
  have ublack: "u \<in> BLACK s" using useen ugray by simp
  have a1: "vset_inv (gs_seen s')" using seen' dfs_inv_seeninv[OF inv] by simp
  have a2: "vset_inv (gs_unf s')" using unf' dfs_inv_unfinv[OF inv] by simp
  have a3: "GRAY s' \<subseteq> SEEN s'" using GRAYeq SEENeq dfs_inv_graysub[OF inv] by simp
  have a4: "GRAY s' = set (map fst (work s'))" using GRAYeq grayeq mapfst' by simp
  have a5: "distinct (map fst (work s'))" using mapfst' dfs_inv_distinct[OF inv] by simp
  have a6: "set ns0 \<subseteq> nbr v0" if "(v0, ns0) \<in> set (work s')" for v0 ns0
  proof (cases "(v0, ns0) = (v, ns')")
    case True
    have "set (u # ns') \<subseteq> nbr v" using dfs_inv_nssub[OF inv] hd by blast
    thus ?thesis using True by auto
  next
    case False
    hence "(v0, ns0) \<in> set (work s)" using that work' w by auto
    thus ?thesis using dfs_inv_nssub[OF inv] by blast
  qed
  have a7: "nbr v0 - set ns0 \<subseteq> SEEN s'" if "(v0, ns0) \<in> set (work s')" for v0 ns0
  proof (cases "(v0, ns0) = (v, ns')")
    case True
    have "nbr v - set (u # ns') \<subseteq> SEEN s" using dfs_inv_consumed[OF inv] hd by blast
    hence "nbr v - set ns' \<subseteq> SEEN s" using useen by auto
    thus ?thesis using True SEENeq by auto
  next
    case False
    hence "(v0, ns0) \<in> set (work s)" using that work' w by auto
    thus ?thesis using dfs_inv_consumed[OF inv] SEENeq by blast
  qed
  have a8: "(b, g) \<notin> E" if "b \<in> BLACK s'" "g \<in> GRAY s'" for b g
    using dfs_inv_F[OF inv] that seen' unf' by simp
  have a9: "nbr b \<subseteq> SEEN s'" if "b \<in> BLACK s'" for b
    using dfs_inv_G[OF inv] that seen' unf' by simp
  have a10: "acyclic (E \<inter> (BLACK s' \<times> BLACK s'))" using dfs_inv_acyc[OF inv] seen' unf' by simp
  have a11: "nbr v0 - set ns0 \<subseteq> BLACK s' \<union> set (map fst ss1)"
    if "work s' = ss1 @ (v0, ns0) # ss2" for ss1 v0 ns0 ss2
  proof (cases ss1)
    case Nil
    hence e: "v0 = v \<and> ns0 = ns'" using that work' by simp
    have "nbr v - set (u # ns') \<subseteq> BLACK s" using dfs_inv_K[OF inv, of "[]" v "u # ns'" rest] w by simp
    hence "nbr v - set ns' \<subseteq> BLACK s" using ublack by auto
    thus ?thesis using Nil e seen' unf' by auto
  next
    case (Cons p tt)
    hence pe: "p = (v, ns')" and rst: "rest = tt @ (v0, ns0) # ss2" using that work' by auto
    have "work s = ((v, u # ns') # tt) @ (v0, ns0) # ss2" using w rst by simp
    hence "nbr v0 - set ns0 \<subseteq> BLACK s \<union> set (map fst ((v, u # ns') # tt))"
      by (rule dfs_inv_K[OF inv])
    thus ?thesis using Cons pe seen' unf' by auto
  qed
  have a12: "SEEN s' \<subseteq> {0..<n}" using SEENeq dfs_inv_range[OF inv] by simp
  show "dfs_inv (s\<lparr>work := (v, ns') # rest\<rparr>)"
    unfolding s'_def[symmetric]
    by (rule dfs_invI[OF a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12])
qed

lemma dfs_inv_push:
  assumes inv: "dfs_inv s" and w: "work s = (v, u # ns') # rest" and useen: "u \<notin> SEEN s"
  shows "dfs_inv (s\<lparr>work := (u, adj u) # (v, ns') # rest,
                    gs_seen := RBT_Set.insert u (gs_seen s),
                    gs_unf := RBT_Set.insert u (gs_unf s)\<rparr>)"
proof -
  define s' where "s' = s\<lparr>work := (u, adj u) # (v, ns') # rest,
                    gs_seen := RBT_Set.insert u (gs_seen s),
                    gs_unf := RBT_Set.insert u (gs_unf s)\<rparr>"
  note vseen = dfs_inv_seeninv[OF inv]
  note vunf = dfs_inv_unfinv[OF inv]
  have work': "work s' = (u, adj u) # (v, ns') # rest" by (simp add: s'_def)
  have SEEN': "SEEN s' = Set.insert u (SEEN s)" by (simp add: s'_def rbt_insert_set[OF vseen])
  have GRAY': "GRAY s' = Set.insert u (GRAY s)" by (simp add: s'_def rbt_insert_set[OF vunf])
  have BLACK': "BLACK s' = BLACK s" using SEEN' GRAY' useen by auto
  have grayeq: "GRAY s = set (map fst (work s))" by (rule dfs_inv_grayeq[OF inv])
  have dist: "distinct (map fst (work s))" by (rule dfs_inv_distinct[OF inv])
  have hdw: "(v, u # ns') \<in> set (work s)" using w by simp
  have adjset: "set (adj u) = nbr u" by (simp add: adj_set')
  have unbrset: "set (u # ns') \<subseteq> nbr v" using dfs_inv_nssub[OF inv] hdw by blast
  have unbr: "u \<in> nbr v" using unbrset by simp
  have urange: "u \<in> {0..<n}" using unbr E_range by auto
  have ugray: "u \<notin> GRAY s" using useen dfs_inv_graysub[OF inv] by blast
  have unotin: "u \<notin> set (map fst (work s))" using ugray grayeq by simp
  have a1: "vset_inv (gs_seen s')" by (simp add: s'_def rbt_insert_inv[OF vseen])
  have a2: "vset_inv (gs_unf s')" by (simp add: s'_def rbt_insert_inv[OF vunf])
  have a3: "GRAY s' \<subseteq> SEEN s'" using GRAY' SEEN' dfs_inv_graysub[OF inv] by auto
  have a4: "GRAY s' = set (map fst (work s'))" using GRAY' grayeq w work' by simp
  have a5: "distinct (map fst (work s'))" using work' w unotin dist by simp
  have a6: "set ns0 \<subseteq> nbr v0" if "(v0, ns0) \<in> set (work s')" for v0 ns0
  proof -
    have mem: "(v0, ns0) \<in> set ((u, adj u) # (v, ns') # rest)" using that work' by simp
    consider (pu) "(v0, ns0) = (u, adj u)" | (mo) "(v0, ns0) = (v, ns')" | (re) "(v0, ns0) \<in> set rest"
      using mem by auto
    thus ?thesis
    proof cases
      case pu thus ?thesis using adjset by auto
    next
      case mo thus ?thesis using unbrset by auto
    next
      case re
      hence "(v0, ns0) \<in> set (work s)" using w by simp
      thus ?thesis using dfs_inv_nssub[OF inv] by blast
    qed
  qed
  have a7: "nbr v0 - set ns0 \<subseteq> SEEN s'" if "(v0, ns0) \<in> set (work s')" for v0 ns0
  proof -
    have mem: "(v0, ns0) \<in> set ((u, adj u) # (v, ns') # rest)" using that work' by simp
    consider (pu) "(v0, ns0) = (u, adj u)" | (mo) "(v0, ns0) = (v, ns')" | (re) "(v0, ns0) \<in> set rest"
      using mem by auto
    thus ?thesis
    proof cases
      case pu thus ?thesis using adjset by auto
    next
      case mo
      have "nbr v - set (u # ns') \<subseteq> SEEN s" using dfs_inv_consumed[OF inv] hdw by blast
      hence "nbr v - set ns' \<subseteq> Set.insert u (SEEN s)" by auto
      thus ?thesis using mo SEEN' by auto
    next
      case re
      hence "(v0, ns0) \<in> set (work s)" using w by simp
      hence "nbr v0 - set ns0 \<subseteq> SEEN s" using dfs_inv_consumed[OF inv] by blast
      thus ?thesis using SEEN' by auto
    qed
  qed
  have a8: "(b, g) \<notin> E" if "b \<in> BLACK s'" "g \<in> GRAY s'" for b g
  proof -
    have bblack: "b \<in> BLACK s" using that(1) BLACK' by simp
    have gg: "g = u \<or> g \<in> GRAY s" using that(2) GRAY' by simp
    show ?thesis
    proof (cases "g = u")
      case True
      show ?thesis
      proof
        assume "(b, g) \<in> E"
        hence "u \<in> nbr b" using True by simp
        hence "u \<in> SEEN s" using dfs_inv_G[OF inv] bblack by blast
        thus False using useen by simp
      qed
    next
      case False
      hence "g \<in> GRAY s" using gg by simp
      thus ?thesis using dfs_inv_F[OF inv] bblack by blast
    qed
  qed
  have a9: "nbr b \<subseteq> SEEN s'" if "b \<in> BLACK s'" for b
  proof -
    have "b \<in> BLACK s" using that BLACK' by simp
    hence "nbr b \<subseteq> SEEN s" using dfs_inv_G[OF inv] by blast
    thus ?thesis using SEEN' by auto
  qed
  have a10: "acyclic (E \<inter> (BLACK s' \<times> BLACK s'))" using dfs_inv_acyc[OF inv] BLACK' by simp
  have a11: "nbr v0 - set ns0 \<subseteq> BLACK s' \<union> set (map fst ss1)"
    if split: "work s' = ss1 @ (v0, ns0) # ss2" for ss1 v0 ns0 ss2
  proof (cases ss1)
    case Nil
    hence "(v0, ns0) = (u, adj u)" using split work' by auto
    thus ?thesis using adjset Nil by auto
  next
    case (Cons x xs)
    hence xu: "x = (u, adj u)" and rest1: "xs @ (v0, ns0) # ss2 = (v, ns') # rest"
      using split work' by auto
    have ss1e: "ss1 = (u, adj u) # xs" using Cons xu by simp
    show ?thesis
    proof (cases xs)
      case Nil
      hence "(v0, ns0) = (v, ns')" using rest1 by auto
      hence "nbr v0 - set ns0 \<subseteq> BLACK s \<union> {u}"
        using dfs_inv_K[OF inv, of "[]" v "u # ns'" rest] w by auto
      thus ?thesis using ss1e Nil BLACK' by auto
    next
      case (Cons y ys)
      hence ye: "y = (v, ns')" and rest2: "ys @ (v0, ns0) # ss2 = rest"
        using rest1 by auto
      have "work s = ((v, u # ns') # ys) @ (v0, ns0) # ss2" using w rest2 by simp
      hence "nbr v0 - set ns0 \<subseteq> BLACK s \<union> set (map fst ((v, u # ns') # ys))"
        by (rule dfs_inv_K[OF inv])
      thus ?thesis using ss1e Cons ye BLACK' by auto
    qed
  qed
  have a12: "SEEN s' \<subseteq> {0..<n}" using SEEN' urange dfs_inv_range[OF inv] by auto
  show "dfs_inv (s\<lparr>work := (u, adj u) # (v, ns') # rest,
                    gs_seen := RBT_Set.insert u (gs_seen s),
                    gs_unf := RBT_Set.insert u (gs_unf s)\<rparr>)"
    unfolding s'_def[symmetric]
    by (rule dfs_invI[OF a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12])
qed

subsection \<open>A fuel measure: the sweep terminates before exhausting its fuel\<close>

text \<open>The recursion strictly decreases \<^term>\<open>mu\<close>: two units of ``credit'' per still-unseen index plus
  its out-degree, one per gray stack vertex, and one per unprocessed out-neighbour on the work list.
  Blackening and skipping drop \<^term>\<open>mu\<close> by one, pushing by two (the pushed vertex's out-degree is paid
  for out of the newly-seen credit). A single root call starts below \<open>2\<cdot>n + |edges| + 1\<close>, so the fuel
  in \<^const>\<open>dl_acyclic_dfs_global\<close> always suffices to drain the work list.\<close>

definition mu :: "dfs_gs \<Rightarrow> nat" where
  "mu s = 2 * card ({0..<n} - SEEN s) + (\<Sum>v \<in> {0..<n} - SEEN s. card (nbr v))
          + card (GRAY s) + (\<Sum>(v, ns) \<leftarrow> work s. length ns)"

lemma E_finite: "finite E" using E_range by (simp add: finite_subset)
lemma nbr_sub_n: "nbr v \<subseteq> {0..<n}" using E_range by auto
lemma nbr_finite: "finite (nbr v)" using nbr_sub_n finite_subset by fastforce
lemma adj_len_card: "length (adj u) = card (nbr u)"
  using distinct_card[OF adj_distinct] adj_set' by simp

lemma sum_nbr_card_E: "(\<Sum>v \<in> {0..<n}. card (nbr v)) = card E"
proof -
  have "E = Sigma {0..<n} nbr" using E_range by auto
  hence "card E = card (Sigma {0..<n} nbr)" by simp
  also have "\<dots> = (\<Sum>v \<in> {0..<n}. card (nbr v))"
    by (rule card_SigmaI) (auto simp: nbr_finite)
  finally show ?thesis by simp
qed

lemma finite_SEEN: "dfs_inv s \<Longrightarrow> finite (SEEN s)" using dfs_inv_range finite_subset by fastforce
lemma finite_GRAY: "dfs_inv s \<Longrightarrow> finite (GRAY s)" using dfs_inv_graysub dfs_inv_range finite_subset by fastforce

lemma mu_blacken:
  assumes inv: "dfs_inv s" and w: "work s = (v, []) # rest"
  shows "mu (s\<lparr>work := rest, gs_unf := RBT_Set.delete v (gs_unf s)\<rparr>) < mu s"
proof -
  define s' where "s' = s\<lparr>work := rest, gs_unf := RBT_Set.delete v (gs_unf s)\<rparr>"
  note vunf = dfs_inv_unfinv[OF inv]
  have vmem: "v \<in> GRAY s" using dfs_inv_grayeq[OF inv] w by simp
  have finG: "finite (GRAY s)" by (rule finite_GRAY[OF inv])
  have SEEN': "SEEN s' = SEEN s" by (simp add: s'_def)
  have GRAY': "GRAY s' = GRAY s - {v}" using rbt_delete_set[OF vunf] by (simp add: s'_def)
  have work': "work s' = rest" by (simp add: s'_def)
  have cardG: "card (GRAY s) = Suc (card (GRAY s - {v}))" using card_Suc_Diff1[OF finG vmem] by simp
  have sw: "(\<Sum>(v, ns) \<leftarrow> work s. length ns) = (\<Sum>(v, ns) \<leftarrow> rest. length ns)" using w by simp
  have "mu s' < mu s" unfolding mu_def SEEN' GRAY' work' using cardG sw by simp
  thus ?thesis unfolding s'_def .
qed

lemma mu_skip:
  assumes inv: "dfs_inv s" and w: "work s = (v, u # ns') # rest"
  shows "mu (s\<lparr>work := (v, ns') # rest\<rparr>) < mu s"
proof -
  define s' where "s' = s\<lparr>work := (v, ns') # rest\<rparr>"
  have SEEN': "SEEN s' = SEEN s" by (simp add: s'_def)
  have GRAY': "GRAY s' = GRAY s" by (simp add: s'_def)
  have sw: "(\<Sum>(v, ns) \<leftarrow> work s. length ns) = Suc (\<Sum>(v, ns) \<leftarrow> work s'. length ns)"
    using w by (simp add: s'_def)
  have "mu s' < mu s" unfolding mu_def SEEN' GRAY' using sw by simp
  thus ?thesis unfolding s'_def .
qed

lemma mu_push:
  assumes inv: "dfs_inv s" and w: "work s = (v, u # ns') # rest" and useen: "u \<notin> SEEN s"
  shows "mu (s\<lparr>work := (u, adj u) # (v, ns') # rest,
                gs_seen := RBT_Set.insert u (gs_seen s),
                gs_unf := RBT_Set.insert u (gs_unf s)\<rparr>) < mu s"
proof -
  define s' where "s' = s\<lparr>work := (u, adj u) # (v, ns') # rest,
                gs_seen := RBT_Set.insert u (gs_seen s),
                gs_unf := RBT_Set.insert u (gs_unf s)\<rparr>"
  note vseen = dfs_inv_seeninv[OF inv]
  note vunf = dfs_inv_unfinv[OF inv]
  have SEEN': "SEEN s' = Set.insert u (SEEN s)" by (simp add: s'_def rbt_insert_set[OF vseen])
  have GRAY': "GRAY s' = Set.insert u (GRAY s)" by (simp add: s'_def rbt_insert_set[OF vunf])
  have work': "work s' = (u, adj u) # (v, ns') # rest" by (simp add: s'_def)
  have hdw: "(v, u # ns') \<in> set (work s)" using w by simp
  have "set (u # ns') \<subseteq> nbr v" using dfs_inv_nssub[OF inv] hdw by blast
  hence unbr: "u \<in> nbr v" by simp
  have urange: "u \<in> {0..<n}" using unbr E_range by auto
  have ugray: "u \<notin> GRAY s" using useen dfs_inv_graysub[OF inv] by blast
  have finG: "finite (GRAY s)" by (rule finite_GRAY[OF inv])
  have umem: "u \<in> {0..<n} - SEEN s" using urange useen by simp
  have finU: "finite ({0..<n} - SEEN s)" by simp
  have finU': "finite ({0..<n} - SEEN s')" by simp
  have compl': "{0..<n} - SEEN s' = ({0..<n} - SEEN s) - {u}" using SEEN' by auto
  have compl2: "{0..<n} - SEEN s = Set.insert u ({0..<n} - SEEN s')" using insert_Diff[OF umem] compl' by simp
  have unotin': "u \<notin> {0..<n} - SEEN s'" using compl' by simp
  have e1: "card ({0..<n} - SEEN s) = Suc (card ({0..<n} - SEEN s'))"
    using card_Suc_Diff1[OF finU umem] compl' by simp
  have e2: "(\<Sum>x\<in>{0..<n} - SEEN s. card (nbr x)) = card (nbr u) + (\<Sum>x\<in>{0..<n} - SEEN s'. card (nbr x))"
  proof -
    have "(\<Sum>x\<in>{0..<n} - SEEN s. card (nbr x)) = (\<Sum>x\<in>Set.insert u ({0..<n} - SEEN s'). card (nbr x))"
      using compl2 by simp
    also have "\<dots> = card (nbr u) + (\<Sum>x\<in>{0..<n} - SEEN s'. card (nbr x))"
      using finU' unotin' by simp
    finally show ?thesis .
  qed
  have e3: "card (GRAY s') = Suc (card (GRAY s))"
    using GRAY' ugray finG by (simp add: card_insert_disjoint)
  have e4: "Suc (\<Sum>(x, ns) \<leftarrow> work s'. length ns) = card (nbr u) + (\<Sum>(x, ns) \<leftarrow> work s. length ns)"
    using w work' adj_len_card by simp
  have "mu s' < mu s" unfolding mu_def using e1 e2 e3 e4 by linarith
  thus ?thesis unfolding s'_def .
qed

subsection \<open>Preservation under fuel-bounded iteration, and enough fuel per root call\<close>

text \<open>Chaining single-step preservation and the strict measure-decrease through the fuel recursion: while
  the run has not flagged a back edge, \<^const>\<open>dfs_inv\<close> is preserved, the seen set only grows, and, once
  the fuel exceeds \<^term>\<open>mu\<close>, the work list is fully drained.\<close>

lemma dfs_fuel_terminal:
  "dfs_inv s \<Longrightarrow> mu s \<le> fuel \<Longrightarrow> \<not> gs_cyc (dfs_fuel fuel adj s) \<Longrightarrow>
   dfs_inv (dfs_fuel fuel adj s) \<and> work (dfs_fuel fuel adj s) = [] \<and> SEEN s \<subseteq> SEEN (dfs_fuel fuel adj s)"
proof (induction fuel arbitrary: s)
  case 0
  note prems0 = 0
  have m0: "mu s = 0" using prems0(2) by simp
  have "card (GRAY s) = 0" using m0 unfolding mu_def by simp
  hence "GRAY s = {}" using finite_GRAY[OF prems0(1)] by (simp add: card_0_eq)
  hence "set (map fst (work s)) = {}" using dfs_inv_grayeq[OF prems0(1)] by simp
  hence wnil: "work s = []" by simp
  have "dfs_fuel 0 adj s = s" by simp
  thus ?case using prems0(1) wnil by simp
next
  case (Suc k)
  note inv = Suc.prems(1) and mubound = Suc.prems(2) and ncyc = Suc.prems(3)
  show ?case
  proof (cases "gs_cyc s")
    case cyc: True
    hence "dfs_fuel (Suc k) adj s = s" by simp
    thus ?thesis using ncyc cyc by simp
  next
    case ncyc0: False
    show ?thesis
    proof (cases "work s")
      case Nil
      hence e: "dfs_fuel (Suc k) adj s = s" using ncyc0 by simp
      show ?thesis using inv Nil e by simp
    next
      case (Cons f rest)
      obtain vv ns where f: "f = (vv, ns)" by fastforce
      have work_eq: "work s = (vv, ns) # rest" using Cons f by simp
      show ?thesis
      proof (cases ns)
        case Nil
        have wwork: "work s = (vv, []) # rest" using work_eq Nil by simp
        define s' where "s' = s\<lparr>work := rest, gs_unf := RBT_Set.delete vv (gs_unf s)\<rparr>"
        have step: "dfs_fuel (Suc k) adj s = dfs_fuel k adj s'" using ncyc0 wwork by (simp add: s'_def)
        have inv': "dfs_inv s'" using dfs_inv_blacken[OF inv wwork] by (simp add: s'_def)
        have "mu s' < mu s" using mu_blacken[OF inv wwork] by (simp add: s'_def)
        hence muk: "mu s' \<le> k" using mubound by linarith
        have nc': "\<not> gs_cyc (dfs_fuel k adj s')" using ncyc step by simp
        note IH = Suc.IH[OF inv' muk nc']
        have seen_eq: "SEEN s' = SEEN s" by (simp add: s'_def)
        show ?thesis
        proof (intro conjI)
          show "dfs_inv (dfs_fuel (Suc k) adj s)" unfolding step using IH by simp
          show "work (dfs_fuel (Suc k) adj s) = []" unfolding step using IH by simp
          show "SEEN s \<subseteq> SEEN (dfs_fuel (Suc k) adj s)" unfolding step using IH seen_eq by auto
        qed
      next
        case (Cons w ns')
        have wwork: "work s = (vv, w # ns') # rest" using work_eq Cons by simp
        show ?thesis
        proof (cases "isin (gs_unf s) w")
          case True
          hence e: "dfs_fuel (Suc k) adj s = s\<lparr>gs_cyc := True\<rparr>" using ncyc0 wwork by simp
          have "gs_cyc (dfs_fuel (Suc k) adj s)" using e by simp
          thus ?thesis using ncyc by simp
        next
          case notgray: False
          have wgray: "w \<notin> GRAY s" using notgray isin_tset[OF dfs_inv_unfinv[OF inv]] by simp
          show ?thesis
          proof (cases "isin (gs_seen s) w")
            case True
            have wseen: "w \<in> SEEN s" using True isin_tset[OF dfs_inv_seeninv[OF inv]] by simp
            define s' where "s' = s\<lparr>work := (vv, ns') # rest\<rparr>"
            have step: "dfs_fuel (Suc k) adj s = dfs_fuel k adj s'"
              using ncyc0 wwork notgray True by (simp add: s'_def)
            have inv': "dfs_inv s'" using dfs_inv_skip[OF inv wwork wseen wgray] by (simp add: s'_def)
            have "mu s' < mu s" using mu_skip[OF inv wwork] by (simp add: s'_def)
            hence muk: "mu s' \<le> k" using mubound by linarith
            have nc': "\<not> gs_cyc (dfs_fuel k adj s')" using ncyc step by simp
            note IH = Suc.IH[OF inv' muk nc']
            have seen_eq: "SEEN s' = SEEN s" by (simp add: s'_def)
            show ?thesis
            proof (intro conjI)
              show "dfs_inv (dfs_fuel (Suc k) adj s)" unfolding step using IH by simp
              show "work (dfs_fuel (Suc k) adj s) = []" unfolding step using IH by simp
              show "SEEN s \<subseteq> SEEN (dfs_fuel (Suc k) adj s)" unfolding step using IH seen_eq by auto
            qed
          next
            case notseen: False
            have wseen: "w \<notin> SEEN s" using notseen isin_tset[OF dfs_inv_seeninv[OF inv]] by simp
            define s' where "s' = s\<lparr>work := (w, adj w) # (vv, ns') # rest,
                                     gs_seen := RBT_Set.insert w (gs_seen s),
                                     gs_unf := RBT_Set.insert w (gs_unf s)\<rparr>"
            have step: "dfs_fuel (Suc k) adj s = dfs_fuel k adj s'"
              using ncyc0 wwork notgray notseen by (simp add: s'_def)
            have inv': "dfs_inv s'" using dfs_inv_push[OF inv wwork wseen] by (simp add: s'_def)
            have "mu s' < mu s" using mu_push[OF inv wwork wseen] by (simp add: s'_def)
            hence muk: "mu s' \<le> k" using mubound by linarith
            have nc': "\<not> gs_cyc (dfs_fuel k adj s')" using ncyc step by simp
            note IH = Suc.IH[OF inv' muk nc']
            have seen_sub: "SEEN s \<subseteq> SEEN s'"
              by (auto simp: s'_def rbt_insert_set[OF dfs_inv_seeninv[OF inv]])
            show ?thesis
            proof (intro conjI)
              show "dfs_inv (dfs_fuel (Suc k) adj s)" unfolding step using IH by simp
              show "work (dfs_fuel (Suc k) adj s) = []" unfolding step using IH by simp
              show "SEEN s \<subseteq> SEEN (dfs_fuel (Suc k) adj s)" unfolding step using IH seen_sub by (blast intro: subset_trans)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma dfs_inv_enter:
  assumes inv: "dfs_inv s" and wnil: "work s = []" and rseen: "r \<notin> SEEN s" and rrange: "r < n"
  shows "dfs_inv (s\<lparr>work := [(r, adj r)], gs_seen := RBT_Set.insert r (gs_seen s), gs_unf := RBT_Set.insert r vset_empty\<rparr>)"
proof -
  define s' where "s' = s\<lparr>work := [(r, adj r)], gs_seen := RBT_Set.insert r (gs_seen s), gs_unf := RBT_Set.insert r vset_empty\<rparr>"
  note vseen = dfs_inv_seeninv[OF inv]
  have emp_leaf: "vset_empty = \<langle>\<rangle>" by (simp add: RBT_Set.empty_def)
  have graynil: "GRAY s = {}" using dfs_inv_grayeq[OF inv] wnil by simp
  have SEEN': "SEEN s' = Set.insert r (SEEN s)" by (simp add: s'_def rbt_insert_set[OF vseen])
  have GRAY': "GRAY s' = {r}" by (simp add: s'_def emp_leaf rbt_insert_set[OF vset_inv_Leaf])
  have work': "work s' = [(r, adj r)]" by (simp add: s'_def)
  have adjset: "set (adj r) = nbr r" by (simp add: adj_set')
  have BLACKeq: "BLACK s' = BLACK s" using SEEN' GRAY' rseen graynil by auto
  have a1: "vset_inv (gs_seen s')" by (simp add: s'_def rbt_insert_inv[OF vseen])
  have a2: "vset_inv (gs_unf s')" by (simp add: s'_def emp_leaf rbt_insert_inv[OF vset_inv_Leaf])
  have a3: "GRAY s' \<subseteq> SEEN s'" using GRAY' SEEN' by auto
  have a4: "GRAY s' = set (map fst (work s'))" using GRAY' work' by simp
  have a5: "distinct (map fst (work s'))" using work' by simp
  have a6: "set ns0 \<subseteq> nbr v0" if "(v0, ns0) \<in> set (work s')" for v0 ns0
    using that work' adjset by auto
  have a7: "nbr v0 - set ns0 \<subseteq> SEEN s'" if "(v0, ns0) \<in> set (work s')" for v0 ns0
    using that work' adjset by auto
  have a8: "(b, g) \<notin> E" if "b \<in> BLACK s'" "g \<in> GRAY s'" for b g
  proof -
    have bblack: "b \<in> BLACK s" using that(1) BLACKeq by simp
    have geq: "g = r" using that(2) GRAY' by simp
    show ?thesis
    proof
      assume "(b, g) \<in> E"
      hence "r \<in> nbr b" using geq by simp
      hence "r \<in> SEEN s" using dfs_inv_G[OF inv] bblack by blast
      thus False using rseen by simp
    qed
  qed
  have a9: "nbr b \<subseteq> SEEN s'" if "b \<in> BLACK s'" for b
  proof -
    have "b \<in> BLACK s" using that BLACKeq by simp
    hence "nbr b \<subseteq> SEEN s" using dfs_inv_G[OF inv] by blast
    thus ?thesis using SEEN' by auto
  qed
  have a10: "acyclic (E \<inter> (BLACK s' \<times> BLACK s'))" using dfs_inv_acyc[OF inv] BLACKeq by simp
  have a11: "nbr v0 - set ns0 \<subseteq> BLACK s' \<union> set (map fst ss1)"
    if split: "work s' = ss1 @ (v0, ns0) # ss2" for ss1 v0 ns0 ss2
  proof (cases ss1)
    case Nil
    hence "(v0, ns0) = (r, adj r)" using split work' by auto
    thus ?thesis using adjset by auto
  next
    case (Cons a as)
    hence False using split work' by simp
    thus ?thesis by simp
  qed
  have a12: "SEEN s' \<subseteq> {0..<n}" using SEEN' rrange dfs_inv_range[OF inv] by auto
  show "dfs_inv (s\<lparr>work := [(r, adj r)], gs_seen := RBT_Set.insert r (gs_seen s), gs_unf := RBT_Set.insert r vset_empty\<rparr>)"
    unfolding s'_def[symmetric]
    by (rule dfs_invI[OF a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12])
qed

lemma mu_enter:
  assumes inv: "dfs_inv s" and rrange: "r < n"
  shows "mu (s\<lparr>work := [(r, adj r)], gs_seen := RBT_Set.insert r (gs_seen s), gs_unf := RBT_Set.insert r vset_empty\<rparr>) \<le> 2 * n + card E + 1"
proof -
  define s' where "s' = s\<lparr>work := [(r, adj r)], gs_seen := RBT_Set.insert r (gs_seen s), gs_unf := RBT_Set.insert r vset_empty\<rparr>"
  note vseen = dfs_inv_seeninv[OF inv]
  have emp_leaf: "vset_empty = \<langle>\<rangle>" by (simp add: RBT_Set.empty_def)
  have SEEN': "SEEN s' = Set.insert r (SEEN s)" by (simp add: s'_def rbt_insert_set[OF vseen])
  have GRAY': "GRAY s' = {r}" by (simp add: s'_def emp_leaf rbt_insert_set[OF vset_inv_Leaf])
  have work': "work s' = [(r, adj r)]" by (simp add: s'_def)
  have rnotin: "r \<notin> {0..<n} - SEEN s'" using SEEN' by simp
  have finU': "finite ({0..<n} - SEEN s')" by simp
  have t1: "2 * card ({0..<n} - SEEN s') \<le> 2 * n"
    using card_mono[of "{0..<n}" "{0..<n} - SEEN s'"] by simp
  have edgesum: "(\<Sum>x\<in>{0..<n} - SEEN s'. card (nbr x)) + card (nbr r) \<le> card E"
  proof -
    have "(\<Sum>x\<in>{0..<n} - SEEN s'. card (nbr x)) + card (nbr r) = (\<Sum>x\<in>Set.insert r ({0..<n} - SEEN s'). card (nbr x))"
      using finU' rnotin by simp
    also have "\<dots> \<le> (\<Sum>x\<in>{0..<n}. card (nbr x))"
      by (rule sum_mono2) (auto simp: rrange)
    also have "\<dots> = card E" by (rule sum_nbr_card_E)
    finally show ?thesis .
  qed
  have sw: "(\<Sum>(x, ns) \<leftarrow> work s'. length ns) = card (nbr r)" using work' adj_len_card by simp
  have cg: "card (GRAY s') = 1" using GRAY' by simp
  have "mu s' \<le> 2 * n + card E + 1"
    unfolding mu_def using t1 edgesum sw cg by linarith
  thus ?thesis unfolding s'_def .
qed

subsection \<open>The outer per-root sweep\<close>

definition init0 :: dfs_gs where
  "init0 = \<lparr>work = [], gs_seen = vset_empty, gs_unf = vset_empty, gs_cyc = False\<rparr>"

definition estep :: "nat \<Rightarrow> dfs_gs \<Rightarrow> nat \<Rightarrow> dfs_gs" where
  "estep fuel s r = (if gs_cyc s \<or> isin (gs_seen s) r then s
                     else dfs_fuel fuel adj (s\<lparr>work := [(r, adj r)],
                                               gs_seen := RBT_Set.insert r (gs_seen s),
                                               gs_unf := RBT_Set.insert r vset_empty\<rparr>))"

lemma estep_cyc_mono: "gs_cyc s \<Longrightarrow> gs_cyc (estep fuel s r)"
  by (simp add: estep_def)

lemma dfs_inv_init: "dfs_inv init0"
  unfolding init0_def
  by (rule dfs_invI; auto simp: RBT_Set.empty_def vset_inv_Leaf acyclic_def)

text \<open>The per-root loop keeps \<^const>\<open>dfs_inv\<close> and, once a run reports no back edge, covers every index it
  has folded over: each processed root is seen, and the seen set never shrinks.\<close>

lemma foldl_cover:
  "2 * n + card E + 1 \<le> fuel \<Longrightarrow> m \<le> n \<Longrightarrow> \<not> gs_cyc (foldl (estep fuel) init0 [0..<m]) \<Longrightarrow>
   dfs_inv (foldl (estep fuel) init0 [0..<m]) \<and> work (foldl (estep fuel) init0 [0..<m]) = []
   \<and> {0..<m} \<subseteq> SEEN (foldl (estep fuel) init0 [0..<m])"
proof (induction m)
  case 0
  have "foldl (estep fuel) init0 [0..<0] = init0" by simp
  thus ?case using dfs_inv_init by (simp add: init0_def RBT_Set.empty_def)
next
  case (Suc m)
  note fuel_ok = Suc.prems(1) and mn = Suc.prems(2) and ncyc = Suc.prems(3)
  define F where "F = foldl (estep fuel) init0 [0..<m]"
  have Fsuc: "foldl (estep fuel) init0 [0..<Suc m] = estep fuel F m"
    by (simp add: F_def upt_Suc_append)
  have mn': "m \<le> n" using mn by simp
  have mlt: "m < n" using mn by simp
  have ncyc_m: "\<not> gs_cyc F"
  proof
    assume "gs_cyc F"
    hence "gs_cyc (estep fuel F m)" by (rule estep_cyc_mono)
    thus False using ncyc Fsuc by simp
  qed
  note IH = Suc.IH[OF fuel_ok mn' ncyc_m[unfolded F_def]]
  have invF: "dfs_inv F" and workF: "work F = []" and coverF: "{0..<m} \<subseteq> SEEN F"
    using IH by (simp_all add: F_def)
  show ?case
  proof (cases "isin (gs_seen F) m")
    case True
    have mseen: "m \<in> SEEN F" using True isin_tset[OF dfs_inv_seeninv[OF invF]] by simp
    have eF: "estep fuel F m = F" using ncyc_m True by (simp add: estep_def)
    have cover': "{0..<Suc m} \<subseteq> SEEN F" using coverF mseen by (auto simp: less_Suc_eq)
    show ?thesis unfolding Fsuc eF using invF workF cover' by simp
  next
    case False
    have mseen: "m \<notin> SEEN F" using False isin_tset[OF dfs_inv_seeninv[OF invF]] by simp
    define e where "e = F\<lparr>work := [(m, adj m)], gs_seen := RBT_Set.insert m (gs_seen F), gs_unf := RBT_Set.insert m vset_empty\<rparr>"
    have estep_eq: "estep fuel F m = dfs_fuel fuel adj e"
      using ncyc_m False by (simp add: estep_def e_def)
    have inve: "dfs_inv e" using dfs_inv_enter[OF invF workF mseen mlt] by (simp add: e_def)
    have mue: "mu e \<le> fuel" using mu_enter[OF invF mlt] fuel_ok unfolding e_def by linarith
    have nce: "\<not> gs_cyc (dfs_fuel fuel adj e)" using ncyc Fsuc estep_eq by simp
    note T = dfs_fuel_terminal[OF inve mue nce]
    have seen_e1: "m \<in> SEEN e"
      by (simp add: e_def rbt_insert_set[OF dfs_inv_seeninv[OF invF]])
    have seen_e2: "SEEN F \<subseteq> SEEN e"
      by (auto simp: e_def rbt_insert_set[OF dfs_inv_seeninv[OF invF]])
    have final: "foldl (estep fuel) init0 [0..<Suc m] = dfs_fuel fuel adj e"
      using Fsuc estep_eq by simp
    show ?thesis
    proof (intro conjI)
      show "dfs_inv (foldl (estep fuel) init0 [0..<Suc m])" unfolding final using T by simp
      show "work (foldl (estep fuel) init0 [0..<Suc m]) = []" unfolding final using T by simp
      show "{0..<Suc m} \<subseteq> SEEN (foldl (estep fuel) init0 [0..<Suc m])"
        unfolding final
      proof -
        have "{0..<m} \<subseteq> SEEN e" using coverF seen_e2 by blast
        hence "{0..<Suc m} \<subseteq> SEEN e" using seen_e1 by (auto simp: less_Suc_eq)
        moreover have "SEEN e \<subseteq> SEEN (dfs_fuel fuel adj e)" using T by simp
        ultimately show "{0..<Suc m} \<subseteq> SEEN (dfs_fuel fuel adj e)" by (blast intro: subset_trans)
      qed
    qed
  qed
qed

text \<open>Assembling the pieces: if the whole sweep reports no back edge, every index is finished, hence
  black; since every edge lies within the index range, the black-restricted graph is the full support
  graph, which the invariant keeps acyclic.\<close>

lemma sweep_acyclic:
  assumes fuel_ok: "2 * n + card E + 1 \<le> fuel"
      and ncyc: "\<not> gs_cyc (foldl (estep fuel) init0 [0..<n])"
  shows "acyclic E"
proof -
  define fin where "fin = foldl (estep fuel) init0 [0..<n]"
  have C: "dfs_inv fin \<and> work fin = [] \<and> {0..<n} \<subseteq> SEEN fin"
    using foldl_cover[OF fuel_ok le_refl ncyc] by (simp add: fin_def)
  hence invfin: "dfs_inv fin" and workfin: "work fin = []" and cover: "{0..<n} \<subseteq> SEEN fin" by simp_all
  have graynil: "GRAY fin = {}" using dfs_inv_grayeq[OF invfin] workfin by simp
  have blackcov: "{0..<n} \<subseteq> BLACK fin" using cover graynil by simp
  have "E \<inter> (BLACK fin \<times> BLACK fin) = E" using E_range blackcov by auto
  moreover have "acyclic (E \<inter> (BLACK fin \<times> BLACK fin))" by (rule dfs_inv_acyc[OF invfin])
  ultimately show "acyclic E" by simp
qed
end

text \<open>\<^const>\<open>Tree2.inorder\<close> of a valid vset lists its elements without repetition: a binary search tree
  is strictly sorted.\<close>

lemma tset_inorder_distinct: "vset_inv t \<Longrightarrow> distinct (Tree2.inorder t)"
  by (simp add: bst_iff_sorted_inorder strict_sorted_iff vset_inv_def)

lemma global_sweep_acyclic:
  assumes bc: "dl_body_closed c" and dfs: "dl_acyclic_dfs_global c"
  shows "acyclic (set (nat_edges c))"
proof -
  interpret I: dfs_gctx "set (nat_edges c)" "length (dl_cert_facts c)"
      "\<lambda>w. Tree2.inorder (neighbourhood (dep_adjmap c) w)"
  proof
    show "\<And>w. set (Tree2.inorder (neighbourhood (dep_adjmap c) w)) = {u. (w, u) \<in> set (nat_edges c)}"
      by (rule adj_set)
  next
    show "\<And>w. distinct (Tree2.inorder (neighbourhood (dep_adjmap c) w))"
      by (rule tset_inorder_distinct) (simp add: dep_adjmap_def a_graph_neighbourhood_inv)
  next
    show "set (nat_edges c) \<subseteq> {0..<length (dl_cert_facts c)} \<times> {0..<length (dl_cert_facts c)}"
      using bc by (auto dest: nat_edges_endpoint_lt)
  qed
  let ?fuel = "2 * length (dl_cert_facts c) + length (nat_edges c) + 1"
  have ncyc: "\<not> gs_cyc (foldl (I.estep ?fuel) I.init0 [0..<length (dl_cert_facts c)])"
  proof -
    have "I.estep ?fuel = (\<lambda>s r. if gs_cyc s \<or> isin (gs_seen s) r then s
             else dfs_fuel ?fuel (\<lambda>w. Tree2.inorder (neighbourhood (dep_adjmap c) w))
                    (s\<lparr>work := [(r, Tree2.inorder (neighbourhood (dep_adjmap c) r))],
                        gs_seen := RBT_Set.insert r (gs_seen s), gs_unf := RBT_Set.insert r vset_empty\<rparr>))"
      by (simp add: I.estep_def fun_eq_iff)
    moreover have "I.init0 = \<lparr>work = [], gs_seen = vset_empty, gs_unf = vset_empty, gs_cyc = False\<rparr>"
      by (simp add: I.init0_def)
    ultimately show ?thesis using dfs unfolding dl_acyclic_dfs_global_def Let_def by simp
  qed
  have fuel_ok: "2 * length (dl_cert_facts c) + card (set (nat_edges c)) + 1 \<le> ?fuel"
    by (simp add: card_length)
  show ?thesis using I.sweep_acyclic[OF fuel_ok ncyc] .
qed

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
      \<and> dl_rules_valid_oi Pl Ul (dl_rules c)
      \<and> dl_closure_check_exec Pl Ul c
      \<and> dl_body_closed c
      \<and> dl_acyclic_dfs_global c)"

lemma dl_admissible_gdfs_imp:
  assumes "dl_admissible_gdfs Pl Ul c"
  shows "dl_admissible (set Pl) (set Ul) c"
proof -
  have pos: "dl_positive_prog_exec Pl"
    and rv: "list_all (dl_rule_valid_oi Pl Ul) (dl_rules c)"
    and cc: "dl_closure_check_exec Pl Ul c"
    and bc: "dl_body_closed c"
    and ac: "dl_acyclic_dfs_global c"
    using assms unfolding dl_admissible_gdfs_def dl_rules_valid_oi_def by auto
  have "dl_positive_prog (set Pl)" using pos by (simp add: dl_positive_prog_exec_iff)
  moreover have "\<forall>r \<in> set (dl_rules c). dl_rule_valid (set Pl) (set Ul) r"
    using rv by (auto simp: list_all_iff dl_rule_valid_oi_eq)
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

