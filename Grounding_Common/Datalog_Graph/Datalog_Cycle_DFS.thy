theory Datalog_Cycle_DFS
  imports
    Datalog_To_Graph
    Datalog_Certification.Datalog_Certificate_Code
    Directed_Cycle_DFS.DFS_DirCycle
    Directed_Set_Graphs.Pair_Graph_RBT
begin

section \<open>Discharging datalog foundedness by a verified directed-cycle DFS\<close>

text \<open>\<open>Datalog_To_Graph\<close> proves the mathematical bridge ``\<open>acyclic (dl_dep_graph c)\<close> implies
  \<open>dl_founded c\<close>'' (under \<open>dl_body_closed\<close>) but leaves the acyclicity check itself abstract. Here we
  discharge it \<^emph>\<open>executably\<close> with the graph library's verified directed-cycle detector
  \<open>find_dircycle\<close> (session \<open>Directed_Cycle_DFS\<close>): a certificate's support graph is acyclic iff
  running the single-source DFS from every certified fact reports no back edge.\<close>

subsection \<open>Executable directed-cycle DFS over RBT adjacency maps\<close>

text \<open>Instantiate the abstract \<^locale>\<open>DFS_dircycle\<close> at the red-black-tree graph representation
  (\<^theory>\<open>Directed_Set_Graphs.Pair_Graph_RBT\<close>), exactly as the library's example does. This yields
  executable \<^term>\<open>find_dircycle\<close> / \<^term>\<open>dircycle_initial_state\<close>.\<close>

global_interpretation dircycle: DFS_dircycle where insert = vset_insert and
 sel = sel and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and
s = s for F s
defines dircycle_initial_state = dircycle.dircycle_initial_state and
find_dircycle = dircycle.dc.DFS_skel_impl and
cyc_found = dircycle.cyc_found and
neighbourhood = dircycle.Graph.neighbourhood
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS_dircycle.intro simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                                           vset_inv_def)

lemmas find_dircycle_code[code] =
  dircycle.dc.DFS_skel_impl.simps[folded find_dircycle_def[folded cyc_found_def],
    unfolded dircycle.cyc_on_found_def dircycle.cyc_on_empty_def dircycle.cyc_on_backtrack_def]

subsection \<open>The certificate's support graph as an RBT adjacency map\<close>

text \<open>\<^const>\<open>dl_dep_graph\<close> as an executable edge list, and the corresponding RBT adjacency map.\<close>

definition dep_edges :: "('p, 'c) dl_certificate \<Rightarrow> (('p, 'c) dl_fact \<times> ('p, 'c) dl_fact) list" where
  "dep_edges c = concat (map (\<lambda>r. map (\<lambda>b. (b, gr_head r)) (gr_body r)) (dl_rules c))"

lemma set_dep_edges: "set (dep_edges c) = dl_dep_graph c"
  by (auto simp: dep_edges_def dl_dep_graph_def)

text \<open>Vertices are indexed by position in \<^term>\<open>dl_cert_facts c\<close>, so the RBT keys are plain
  \<^typ>\<open>nat\<close> (always a \<^class>\<open>linorder\<close>, avoiding any lexicographic order on facts); the support
  graph's edges are relabelled accordingly.\<close>

fun idx_of :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "idx_of [] y = 0"
| "idx_of (x # xs) y = (if x = y then 0 else Suc (idx_of xs y))"

definition fact_idx :: "('p, 'c) dl_certificate \<Rightarrow> ('p, 'c) dl_fact \<Rightarrow> nat" where
  "fact_idx c = idx_of (dl_cert_facts c)"

definition nat_edges :: "('p, 'c) dl_certificate \<Rightarrow> (nat \<times> nat) list" where
  "nat_edges c = map (\<lambda>(a, b). (fact_idx c a, fact_idx c b)) (dep_edges c)"

definition dep_adjmap :: "('p, 'c) dl_certificate \<Rightarrow> _" where
  "dep_adjmap c = a_graph (nat_edges c)"

subsection \<open>The executable acyclicity check\<close>

text \<open>The support graph is acyclic iff the single-source directed-cycle DFS reports no back edge when
  started from \<^emph>\<open>every\<close> fact index: a directed cycle is reachable from each of its own vertices, so
  some source hits it.\<close>

definition dl_acyclic_dfs :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_acyclic_dfs c =
     list_all (\<lambda>i. \<not> DFS_dircycle_state.cycle (find_dircycle (dep_adjmap c) (dircycle_initial_state i)))
              [0..<length (dl_cert_facts c)]"

text \<open>Code equation hoisting the support graph out of the per-vertex loop: \<^const>\<open>dep_adjmap\<close> does
  not depend on the source \<open>i\<close>, but as written it sits inside the \<^const>\<open>list_all\<close> lambda, so the
  generated code rebuilds the whole RBT adjacency map (relabelling every edge through the linear-scan
  \<^const>\<open>fact_idx\<close>) once per certified fact --- \<open>O(|facts| \<cdot> |edges| \<cdot> |facts|)\<close>. Binding it once with a
  \<^theory_text>\<open>let\<close> (the code generator emits an SML \<open>let val g = \<dots>\<close>, evaluated once) makes it
  \<open>O(|edges| \<cdot> |facts|)\<close> plus the per-vertex DFS. Pure refinement: the term is definitionally equal, so
  every soundness lemma about \<^const>\<open>dl_acyclic_dfs\<close> is untouched.\<close>
lemma dl_acyclic_dfs_code [code]:
  "dl_acyclic_dfs c =
     (let g = dep_adjmap c in
      list_all (\<lambda>i. \<not> DFS_dircycle_state.cycle (find_dircycle g (dircycle_initial_state i)))
               [0..<length (dl_cert_facts c)])"
  by (simp add: dl_acyclic_dfs_def Let_def)

subsection \<open>Correctness of the acyclicity check\<close>

text \<open>Step 2: the RBT adjacency map \<^const>\<open>a_graph\<close> faithfully abstracts an edge list.\<close>

text \<open>\<^const>\<open>nbs\<close> is built with the plain \<^const>\<open>RBT_Set.insert\<close> (\<open>paint Black \<circ> ins\<close>), not the
  join-based \<^term>\<open>insert_rbt\<close> of the \<^locale>\<open>Pair_Graph_Specs\<close> interpretation. We therefore prove
  \<^const>\<open>vset_inv\<close>/\<^const>\<open>t_set\<close> preservation for it directly.\<close>

lemma bst_iff_sorted_inorder: "Tree2.bst t = sorted (Tree2.inorder t)"
proof (induction t rule: Tree2.bst.induct)
  case 1
  show ?case by simp
next
  case (2 l a b r)
  have snoc: "sorted (Tree2.inorder l @ [a])
                = (sorted (Tree2.inorder l) \<and> (\<forall>x \<in> set_tree l. x < a))"
    by (simp only: sorted_wrt_append Tree2.set_inorder) simp
  have cons: "sorted (a # Tree2.inorder r)
                = ((\<forall>x \<in> set_tree r. a < x) \<and> sorted (Tree2.inorder r))"
    by (simp only: sorted_wrt_Cons Tree2.set_inorder)
  have "sorted (Tree2.inorder l @ a # Tree2.inorder r)
          = (sorted (Tree2.inorder l @ [a]) \<and> sorted (a # Tree2.inorder r))"
    by (rule sorted_mid_iff)
  hence "sorted (Tree2.inorder \<langle>l, (a, b), r\<rangle>)
          = (sorted (Tree2.inorder l) \<and> (\<forall>x \<in> set_tree l. x < a)
             \<and> (\<forall>x \<in> set_tree r. a < x) \<and> sorted (Tree2.inorder r))"
    by (simp add: snoc cons conj_assoc)
  thus ?case
    using 2 by auto
qed

lemma rbt_insert_inv:
  assumes "vset_inv t"
  shows "vset_inv (RBT_Set.insert x t)"
proof -
  have c: "invc t" and h: "invh t" and b: "Tree2.bst t"
    using assms by (auto simp: vset_inv_def)
  have "invc (RBT_Set.insert x t)"
    using c by (simp add: RBT_Set.insert_def invc_ins)
  moreover have "invh (RBT_Set.insert x t)"
    using h by (simp add: RBT_Set.insert_def invh_ins invh_paint)
  moreover have "Tree2.bst (RBT_Set.insert x t)"
    using b by (simp add: bst_iff_sorted_inorder RBT_Set.inorder_insert sorted_ins_list)
  ultimately show ?thesis by (simp add: vset_inv_def)
qed

lemma rbt_insert_set:
  assumes "vset_inv t"
  shows "t_set (RBT_Set.insert x t) = Set.insert x (t_set t)"
proof -
  have b: "Tree2.bst t" using assms by (auto simp: vset_inv_def)
  hence "t_set (RBT_Set.insert x t) = set (Tree2.inorder (RBT_Set.insert x t))"
    by (simp add: Tree2.set_inorder)
  also have "\<dots> = set (ins_list x (Tree2.inorder t))"
    using b by (simp add: RBT_Set.inorder_insert bst_iff_sorted_inorder)
  also have "\<dots> = Set.insert x (t_set t)"
    by (simp add: set_ins_list Tree2.set_inorder)
  finally show ?thesis .
qed

lemma vset_inv_Leaf: "vset_inv Leaf"
  by (simp add: vset_inv_def)

lemma foldr_rbt_insert_inv: "vset_inv (foldr (\<lambda>x t. RBT_Set.insert x t) xs Leaf)"
  by (induction xs) (simp_all add: vset_inv_Leaf rbt_insert_inv)

lemma foldr_rbt_insert_set:
  "t_set (foldr (\<lambda>x t. RBT_Set.insert x t) xs Leaf) = set xs"
  by (induction xs) (simp_all add: rbt_insert_set foldr_rbt_insert_inv)

lemma nbs_inv: "vset_inv (nbs E v)"
  unfolding nbs_def by (rule foldr_rbt_insert_inv)

lemma nbs_set: "t_set (nbs E v) = {w. (v, w) \<in> set E}"
  unfolding nbs_def foldr_rbt_insert_set by force

lemma M_invar_Leaf: "M.invar Leaf"
  using M.invar_empty by (simp add: RBT_Set.empty_def)

lemma a_graph_fold_invar:
  "M.invar (foldr (\<lambda>x t. update x (nbs E x) t) ks Leaf)"
  by (induction ks) (simp_all add: M_invar_Leaf M.invar_update)

lemma a_graph_fold_lookup:
  "lookup (foldr (\<lambda>x t. update x (nbs E x) t) ks Leaf)
          = (\<lambda>k. if k \<in> set ks then Some (nbs E k) else None)"
proof (induction ks)
  case Nil
  show ?case by (simp add: M.map_empty)
next
  case (Cons a ks)
  have "lookup (foldr (\<lambda>x t. update x (nbs E x) t) (a # ks) Leaf)
          = (lookup (foldr (\<lambda>x t. update x (nbs E x) t) ks Leaf))(a := Some (nbs E a))"
    by (simp add: M.map_update a_graph_fold_invar)
  also have "\<dots> = (\<lambda>k. if k \<in> set (a # ks) then Some (nbs E k) else None)"
    using Cons.IH by auto
  finally show ?case .
qed

lemma a_graph_lookup:
  "lookup (a_graph E) = (\<lambda>k. if k \<in> set (vertices E) then Some (nbs E k) else None)"
  unfolding a_graph_def RBT_Set.empty_def by (rule a_graph_fold_lookup)

lemma a_graph_invar: "M.invar (a_graph E)"
  unfolding a_graph_def RBT_Set.empty_def by (rule a_graph_fold_invar)

lemma a_graph_graph_inv: "dircycle.Graph.graph_inv (a_graph E)"
proof (rule dircycle.Graph.graph_invI)
  show "adj_inv (a_graph E)"
    by (simp add: adj_inv_def a_graph_invar)
next
  fix v vset
  assume "lookup (a_graph E) v = Some vset"
  thus "vset_inv vset"
    by (auto simp: a_graph_lookup nbs_inv split: if_splits)
qed

lemma a_graph_finite_graph: "dircycle.Graph.finite_graph (a_graph E)"
  unfolding dircycle.Graph.finite_graph_def
  by (rule finite_subset[of _ "set (vertices E)"]) (auto simp: a_graph_lookup)

lemma a_graph_finite_vsets: "dircycle.Graph.finite_vsets (a_graph E)"
  unfolding dircycle.Graph.finite_vsets_def
  by (auto simp: a_graph_lookup nbs_set split: if_splits)

lemma a_graph_neighbourhood:
  "t_set (dircycle.Graph.neighbourhood (a_graph E) u) = {w. (u, w) \<in> set E}"
  unfolding dircycle.Graph.neighbourhood_def
  by (auto simp: a_graph_lookup nbs_set vertices_def RBT_Set.empty_def
                 rev_image_eqI split: option.splits if_splits)

lemma a_graph_neighbourhood_inv:
  "vset_inv (dircycle.Graph.neighbourhood (a_graph E) u)"
  using a_graph_graph_inv by (rule dircycle.Graph.neighbourhood_invars')

lemma a_graph_digraph_abs: "dircycle.Graph.digraph_abs (a_graph E) = set E"
proof -
  have "dircycle.Graph.digraph_abs (a_graph E)
          = {(u, v). v \<in> t_set (dircycle.Graph.neighbourhood (a_graph E) u)}"
    by (auto simp: dircycle.Graph.digraph_abs_def
                   set.set_isin[OF a_graph_neighbourhood_inv])
  also have "\<dots> = set E"
    by (auto simp: a_graph_neighbourhood)
  finally show ?thesis .
qed

text \<open>Step 3: the natural-number edge list relabels the support graph by \<^const>\<open>fact_idx\<close>.\<close>

lemma set_nat_edges:
  "set (nat_edges c) = (\<lambda>(a, b). (fact_idx c a, fact_idx c b)) ` dl_dep_graph c"
  by (simp add: nat_edges_def set_dep_edges [symmetric])

lemma trancl_map_prod:
  assumes "(x, y) \<in> Rel\<^sup>+"
  shows "(g x, g y) \<in> ((\<lambda>(a, b). (g a, g b)) ` Rel)\<^sup>+"
  using assms
proof (induction rule: trancl_induct)
  case (base y)
  thus ?case by (auto intro: r_into_trancl)
next
  case (step y z)
  have "(g y, g z) \<in> (\<lambda>(a, b). (g a, g b)) ` Rel"
    using step.hyps(2) by (auto intro: rev_image_eqI)
  thus ?case using step.IH by (auto intro: trancl_into_trancl)
qed

lemma not_acyclic_dep_graph_imp_nat_edges:
  assumes "\<not> acyclic (dl_dep_graph c)"
  shows "\<not> acyclic (set (nat_edges c))"
proof -
  obtain x where "(x, x) \<in> (dl_dep_graph c)\<^sup>+"
    using assms by (auto simp: acyclic_def)
  hence "(fact_idx c x, fact_idx c x)
           \<in> ((\<lambda>(a, b). (fact_idx c a, fact_idx c b)) ` dl_dep_graph c)\<^sup>+"
    by (rule trancl_map_prod)
  thus ?thesis by (auto simp: acyclic_def set_nat_edges)
qed

text \<open>Step 4: \<^const>\<open>idx_of\<close> assigns each list element a position below the list length; under
  \<^const>\<open>dl_body_closed\<close> every vertex of the support graph is a certified fact, so its index is in
  range.\<close>

lemma idx_of_less: "y \<in> set xs \<Longrightarrow> idx_of xs y < length xs"
  by (induction xs) auto

lemma dl_dep_graph_vertex_cert_fact:
  assumes "dl_body_closed c" and "(u, v) \<in> dl_dep_graph c"
  shows "u \<in> set (dl_cert_facts c)"
    and "v \<in> set (dl_cert_facts c)"
proof -
  obtain r where r: "r \<in> set (dl_rules c)" and hd: "gr_head r = v" and b: "u \<in> set (gr_body r)"
    using assms(2) by (auto elim: dl_dep_graph_edgeE)
  show "u \<in> set (dl_cert_facts c)"
    using assms(1) r b by (auto simp: dl_body_closed_def)
  show "v \<in> set (dl_cert_facts c)"
    using r hd by (auto simp: dl_cert_facts_def)
qed

text \<open>Step 5: single-source cycle detection is complete over the support-graph indices. If the
  support graph carries a cycle, running the DFS from the (in-range) index of one of its vertices
  reports it; hence \<^const>\<open>dl_acyclic_dfs\<close> failing is equivalent to acyclicity.\<close>

text \<open>The DFS started at a vertex of a cycle detects it. This is the completeness argument: at the
  end of a cycle-free run \<open>seen = finished\<close> is closed under edges and contains the source, so it
  contains every vertex reachable from the source --- in particular the whole cycle through it --- and
  the cycle survives in the explored subgraph, contradicting the completeness theorem.\<close>

lemma dircycle_detects_cycle:
  assumes ax: "dircycle.DFS_dircycle_axioms TYPE('a :: linorder) (a_graph E) i"
    and cyc: "(i, i) \<in> (set E)\<^sup>+"
  shows "DFS_dircycle_state.cycle (find_dircycle (a_graph E) (dircycle_initial_state i))"
proof -
  interpret thms: DFS_dircycle_thms where insert = vset_insert and
    sel = sel and vset_empty = vset_empty and diff = vset_diff and
    lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
    and vset_inv = vset_inv and union = vset_union and inter = vset_inter
    and G = "a_graph E" and s = i
    using dircycle.DFS_dircycle_axioms ax
    by (auto intro!: DFS_dircycle_thms.intro DFS_dircycle_thms_axioms.intro)
  define init where "init = dircycle_initial_state i"
  define r where "r = thms.dc.DFS_skel init"
  have dom: "thms.dc.DFS_skel_dom init"
    unfolding init_def dircycle_initial_state_def using thms.dircycle_initial_dom by simp
  have bridge: "find_dircycle (a_graph E) (dircycle_initial_state i) = r"
    unfolding r_def init_def [symmetric]
    by (simp add: find_dircycle_def thms.dc.DFS_skel_impl_same[OF dom])
  have init_raw: "init = DFS_dircycle.dircycle_initial_state vset_insert vset_empty i"
    by (simp add: init_def dircycle_initial_state_def)
  have DG: "dircycle.Graph.digraph_abs (a_graph E) = set E"
    by (rule a_graph_digraph_abs)
  \<comment> \<open>the initial source \<open>i\<close> stays in \<open>seen\<close> throughout the run\<close>
  have seen_eq: "seen init = vset_insert i vset_empty"
    unfolding init_def
    by (simp add: dircycle.dircycle_initial_state_def)
  have seen_init: "i \<in> t_set (seen init)"
    unfolding seen_eq
    by (simp add: set.set_insert[OF set.invar_empty] set.set_empty RBT_Set.empty_def)
  show ?thesis
  proof (rule ccontr)
    assume "\<not> DFS_dircycle_state.cycle (find_dircycle (a_graph E) (dircycle_initial_state i))"
    hence ncyc: "\<not> DFS_dircycle_state.cycle r" by (simp add: bridge)
    \<comment> \<open>invariants of the terminated run\<close>
    have fc: "thms.invar_finished_closed r"
      unfolding r_def init_raw
      by (intro thms.invar_finished_closed_holds thms.dircycle_initial_dom
                thms.initial_invars thms.initial_fin thms.initial_fc)
    have ssf: "thms.invar_ssf r"
      unfolding r_def init_raw
      by (intro thms.invar_ssf_holds thms.dircycle_initial_dom
                thms.initial_invars thms.initial_fin thms.initial_struct)
    have "thms.dc.DFS_skel_ret_1_conds r"
      unfolding r_def
      using thms.no_cycle_ret_1[OF dom] ncyc unfolding r_def by blast
    hence empty: "stack r = []"
      by (auto simp: thms.dc.DFS_skel_ret_1_conds_def split: list.splits)
    \<comment> \<open>at the end, finished = seen and the source is finished\<close>
    have fin_seen: "t_set (finished r) = t_set (seen r)"
      using ssf empty by (auto simp: thms.invar_ssf_def)
    \<comment> \<open>seen only grows, so the initial source survives to the final state\<close>
    have set_insert_mono: "t_set s \<subseteq> t_set (vset_insert x s)" if "vset_inv s" for s x
      by (auto simp: set.set_insert[OF that])
    have seen_upd1: "t_set (seen st) \<subseteq> t_set (seen (thms.dc.DFS_skel_upd1 st))"
      if v: "vset_inv (seen st)" for st
      unfolding thms.dc.DFS_skel_upd1_def Let_def
      by simp (rule set_insert_mono[OF v])
    have inv1_upd1: "thms.dc.invar_1 (thms.dc.DFS_skel_upd1 st)"
      if "thms.dc.DFS_skel_call_1_conds st" "thms.dc.invar_1 st" for st
      using that by (rule thms.dc.invar_1_holds_1)
    have inv1_upd2: "thms.dc.invar_1 (thms.dc.DFS_skel_upd2 st)"
      if "thms.dc.DFS_skel_call_2_conds st" "thms.dc.invar_1 st" for st
      using that by (rule thms.dc.invar_1_holds_2)
    have seen_mono0: "thms.dc.invar_1 st \<longrightarrow> t_set (seen st) \<subseteq> t_set (seen (thms.dc.DFS_skel st))"
      if dst: "thms.dc.DFS_skel_dom st" for st
    proof (induction rule: thms.dc.DFS_skel_induct[OF dst])
      case IH: (1 st)
      note simps = thms.dc.DFS_skel_simps[OF IH(1)]
      show ?case
      proof (intro impI, rule thms.dc.DFS_skel_cases[where dfs_state = st])
        assume inv: "thms.dc.invar_1 st"
        assume c: "thms.dc.DFS_skel_call_1_conds st"
        have v: "vset_inv (seen st)" using inv by (simp add: thms.dc.invar_1_def)
        have "t_set (seen (thms.dc.DFS_skel_upd1 st))
                \<subseteq> t_set (seen (thms.dc.DFS_skel (thms.dc.DFS_skel_upd1 st)))"
          using IH(2)[OF c] inv1_upd1[OF c inv] by (simp add: mp)
        hence "t_set (seen st) \<subseteq> t_set (seen (thms.dc.DFS_skel (thms.dc.DFS_skel_upd1 st)))"
          using seen_upd1[OF v] by (rule subset_trans [rotated])
        thus "t_set (seen st) \<subseteq> t_set (seen (thms.dc.DFS_skel st))"
          by (simp add: simps(1) c)
      next
        assume inv: "thms.dc.invar_1 st"
        assume c: "thms.dc.DFS_skel_call_2_conds st"
        have "t_set (seen (thms.dc.DFS_skel_upd2 st))
                \<subseteq> t_set (seen (thms.dc.DFS_skel (thms.dc.DFS_skel_upd2 st)))"
          using IH(3)[OF c] inv1_upd2[OF c inv] by (simp add: mp)
        thus "t_set (seen st) \<subseteq> t_set (seen (thms.dc.DFS_skel st))"
          by (simp add: simps(2) c thms.upd2_unfold)
      next
        assume "thms.dc.invar_1 st" and c: "thms.dc.DFS_skel_ret_1_conds st"
        thus "t_set (seen st) \<subseteq> t_set (seen (thms.dc.DFS_skel st))"
          by (simp add: simps(3) thms.dc.DFS_skel_ret1_def)
      next
        assume "thms.dc.invar_1 st" and c: "thms.dc.DFS_skel_ret_2_conds st"
        thus "t_set (seen st) \<subseteq> t_set (seen (thms.dc.DFS_skel st))"
          by (simp add: simps(4) thms.dc.DFS_skel_ret2_def)
      qed
    qed
    have seen_mono: "t_set (seen st) \<subseteq> t_set (seen (thms.dc.DFS_skel st))"
      if "thms.dc.DFS_skel_dom st" and "thms.dc.invar_1 st" for st
      using seen_mono0[OF that(1)] that(2) by blast
    have inv1_init: "thms.dc.invar_1 init"
      unfolding init_raw by (rule thms.initial_invars(1))
    have i_seen_r: "i \<in> t_set (seen r)"
      unfolding r_def using seen_init seen_mono[OF dom inv1_init] by auto
    have i_fin: "i \<in> t_set (finished r)"
      using i_seen_r fin_seen by simp
    \<comment> \<open>finished is closed under edges, so all vertices reachable from \<open>i\<close> are finished\<close>
    have closed: "\<And>u w. u \<in> t_set (finished r) \<Longrightarrow> (u, w) \<in> set E \<Longrightarrow> w \<in> t_set (finished r)"
      using fc DG by (auto simp: thms.invar_finished_closed_def)
    have reach_fin: "w \<in> t_set (finished r)" if "(i, w) \<in> (set E)\<^sup>+" for w
      using that i_fin by (induction rule: trancl_induct) (auto intro: closed)
    \<comment> \<open>the cycle through \<open>i\<close> survives in the subgraph induced on the finished vertices\<close>
    have loop_induced: "(i, i) \<in> (set E \<downharpoonright> t_set (finished r))\<^sup>+"
    proof -
      have "(i, w) \<in> (set E \<downharpoonright> t_set (finished r))\<^sup>+" if "(i, w) \<in> (set E)\<^sup>+" for w
        using that
      proof (induction rule: trancl_induct)
        case (base w)
        thus ?case
          using i_fin reach_fin[OF r_into_trancl[OF base]]
          by (auto simp: induce_subgraph_def)
      next
        case (step w z)
        have "(w, z) \<in> set E \<downharpoonright> t_set (finished r)"
          using step.hyps(2) reach_fin[OF step.hyps(1)]
                reach_fin[OF trancl_into_trancl[OF step.hyps(1,2)]]
          by (auto simp: induce_subgraph_def)
        thus ?case using step.IH by (auto intro: trancl_into_trancl)
      qed
      thus ?thesis using cyc by blast
    qed
    have "\<not> acyclic (dircycle.Graph.digraph_abs (a_graph E) \<downharpoonright> t_set (seen r))"
      using loop_induced by (auto simp: acyclic_def DG fin_seen)
    hence "\<exists>c. Awalk_Defs.cycle (dircycle.Graph.digraph_abs (a_graph E) \<downharpoonright> t_set (seen r)) c"
      by (rule not_acyclic_imp_cycle)
    moreover have "\<nexists>c. Awalk_Defs.cycle (dircycle.Graph.digraph_abs (a_graph E) \<downharpoonright> t_set (seen r)) c"
      using thms.DFS_dircycle_complete[OF ncyc[unfolded r_def init_raw]]
      unfolding r_def init_raw [symmetric] .
    ultimately show False by blast
  qed
qed

lemma dep_adjmap_axioms:
  assumes "i \<in> dVs (set (nat_edges c))"
  shows "dircycle.DFS_dircycle_axioms TYPE(nat) (a_graph (nat_edges c)) i"
  unfolding dircycle.DFS_dircycle_axioms_def
  using assms
  by (simp add: a_graph_graph_inv a_graph_finite_graph a_graph_finite_vsets a_graph_digraph_abs)

lemma dl_acyclic_dfs_imp_acyclic:
  assumes bc: "dl_body_closed c" and dfs: "dl_acyclic_dfs c"
  shows "acyclic (dl_dep_graph c)"
proof (rule ccontr)
  assume "\<not> acyclic (dl_dep_graph c)"
  then obtain x where xx: "(x, x) \<in> (dl_dep_graph c)\<^sup>+"
    by (auto simp: acyclic_def)
  \<comment> \<open>the cycle vertex is a certified fact, so its index is in range\<close>
  obtain u v where "(u, v) \<in> dl_dep_graph c" and "x = u"
    using xx by (metis converse_tranclE)
  hence xfact: "x \<in> set (dl_cert_facts c)"
    using bc dl_dep_graph_vertex_cert_fact(1) by blast
  let ?i = "fact_idx c x"
  have irange: "?i \<in> set [0..<length (dl_cert_facts c)]"
    using xfact by (simp add: fact_idx_def idx_of_less)
  \<comment> \<open>the relabelled cycle lives in the natural-number edge set\<close>
  have loop: "(?i, ?i) \<in> (set (nat_edges c))\<^sup>+"
    using trancl_map_prod[OF xx, of "fact_idx c"] by (simp add: set_nat_edges)
  have "\<exists>z. (?i, z) \<in> set (nat_edges c)"
    using loop by (metis tranclD)
  hence "?i \<in> dVs (set (nat_edges c))"
    by (auto simp: dVs_def)
  \<comment> \<open>hence the DFS from that source detects a cycle, refuting the acyclicity check\<close>
  hence "DFS_dircycle_state.cycle
           (find_dircycle (a_graph (nat_edges c)) (dircycle_initial_state ?i))"
    using dircycle_detects_cycle[OF dep_adjmap_axioms loop] by blast
  hence "\<not> dl_acyclic_dfs c"
    using irange by (auto simp: dl_acyclic_dfs_def dep_adjmap_def list_all_iff)
  thus False using dfs by blast
qed

subsection \<open>The certificate's support graph is founded when the DFS reports acyclic\<close>

theorem dl_acyclic_dfs_imp_dl_founded:
  assumes "dl_body_closed c" and "dl_acyclic_dfs c"
  shows "dl_founded c"
  using acyclic_dep_graph_imp_dl_founded[OF assms(1) dl_acyclic_dfs_imp_acyclic[OF assms]] .

subsection \<open>A DFS-founded executable certified-model check\<close>

text \<open>The executable admissibility check of \<^theory>\<open>Datalog_Certification.Datalog_Certificate_Code\<close>
  with its ordered linear-scan foundedness conjunct \<^const>\<open>dl_founded_exec\<close> replaced by the
  verified directed-cycle DFS: \<^const>\<open>dl_body_closed\<close> (each rule body is certified) together with
  \<^const>\<open>dl_acyclic_dfs\<close> (the support graph is acyclic) discharge \<^const>\<open>dl_founded\<close> just the same
  (\<open>dl_acyclic_dfs_imp_dl_founded\<close>). The other three conjuncts are reused verbatim.\<close>

lemma dl_body_closed_code [code]:
  "dl_body_closed c =
     list_all (\<lambda>r. list_all (\<lambda>b. b \<in> set (dl_cert_facts c)) (gr_body r)) (dl_rules c)"
  by (auto simp: dl_body_closed_def list_all_iff)

definition dl_admissible_dfs :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_admissible_dfs Pl Ul c =
     (dl_positive_prog_exec Pl
      \<and> list_all (dl_rule_valid_exec Pl Ul) (dl_rules c)
      \<and> dl_closure_check_exec Pl Ul c
      \<and> dl_body_closed c
      \<and> dl_acyclic_dfs c)"

lemma dl_admissible_dfs_imp:
  assumes "dl_admissible_dfs Pl Ul c"
  shows "dl_admissible (set Pl) (set Ul) c"
proof -
  have pos: "dl_positive_prog_exec Pl"
    and rv: "list_all (dl_rule_valid_exec Pl Ul) (dl_rules c)"
    and cc: "dl_closure_check_exec Pl Ul c"
    and bc: "dl_body_closed c"
    and ac: "dl_acyclic_dfs c"
    using assms unfolding dl_admissible_dfs_def by auto
  have "dl_positive_prog (set Pl)" using pos by (simp add: dl_positive_prog_exec_iff)
  moreover have "\<forall>r \<in> set (dl_rules c). dl_rule_valid (set Pl) (set Ul) r"
    using rv by (auto simp: list_all_iff intro: dl_rule_valid_exec_imp)
  moreover have "dl_closure_check (set Pl) (set Ul) c"
    using cc by (rule dl_closure_check_exec_imp)
  moreover have "dl_founded c" using dl_acyclic_dfs_imp_dl_founded[OF bc ac] .
  ultimately show ?thesis unfolding dl_admissible_def by blast
qed

definition dl_certified_model_dfs :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_certified_model_dfs Pl Ul M c = (dl_admissible_dfs Pl Ul c \<and> set M = set (dl_cert_facts c))"

theorem dl_certified_model_dfs_imp:
  assumes "dl_certified_model_dfs Pl Ul M c"
  shows "dl_certified_model (set Pl) (set Ul) M c"
  using assms dl_admissible_dfs_imp
  unfolding dl_certified_model_dfs_def dl_certified_model_def by blast

declare dl_admissible_dfs_def [code] dl_certified_model_dfs_def [code]

subsection \<open>Example: the running edge/path certificate\<close>

value "dep_edges ex_cert"
value "nat_edges ex_cert"
text \<open>The edge/path support graph is a DAG, so the DFS reports acyclic (\<open>True\<close>).\<close>
value "dl_acyclic_dfs ex_cert"

text \<open>A certificate whose support graph carries a genuine 2-cycle \<open>p(1) \<leftrightarrow> q(1)\<close> (mutually
  supporting rules): the DFS detects the back edge and reports \<open>False\<close>.\<close>
definition cyc_cert :: "(String.literal, nat) dl_certificate" where
  "cyc_cert = DLCert [DLRule (STR ''p'', [1]) [(STR ''q'', [1])],
                      DLRule (STR ''q'', [1]) [(STR ''p'', [1])]]"

value "nat_edges cyc_cert"
value "dl_acyclic_dfs cyc_cert"

end
