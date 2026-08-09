theory Datalog_Cycle_DFS
  imports
    Datalog_To_Graph
    Datalog_Certification.Datalog_Certificate_Code
    DFS_DirCycle_Linear
    Directed_Set_Graphs.Pair_Graph_RBT
begin

section \<open>Discharging datalog foundedness by a verified directed-cycle DFS\<close>

text \<open>\<open>Datalog_To_Graph\<close> proves the mathematical bridge ``\<open>acyclic (dl_dep_graph c)\<close> implies
  \<open>dl_founded c\<close>'' (under \<open>dl_body_closed\<close>) but leaves the acyclicity check itself abstract. Here we
  discharge it \<^emph>\<open>executably\<close> with the verified whole-graph directed-cycle sweep
  \<open>DFS_DirCycle_Linear\<close>: a certificate's support graph is acyclic iff a single sweep over its
  vertices --- each inner DFS seeded with the region the earlier calls already finished --- reports
  no back edge.

  This replaces the earlier \<^emph>\<open>per-vertex\<close> check, which ran an independent single-source DFS from
  every certified fact and so re-explored the same region once per source (\<open>O(V\<cdot>(V+E))\<close>). The
  linear sweep visits each vertex once (\<open>O(V+E)\<close>) and, unlike a shared-\<open>seen\<close> hack, is justified
  by the seed contract \<open>seed_ok\<close> the inner DFS re-establishes for the enlarged region.\<close>

subsection \<open>Executable directed-cycle DFS over RBT adjacency maps\<close>

text \<open>Instantiate both abstract locales at the red-black-tree graph representation
  (\<^theory>\<open>Directed_Set_Graphs.Pair_Graph_RBT\<close>): the pre-seeded inner DFS
  \<^locale>\<open>DFS_dircycle_linear_aux\<close>, then the outer sweep \<^locale>\<open>DFS_DirCycle_Linear\<close> that calls
  it once per remaining root.\<close>

global_interpretation dircycle: DFS_dircycle_linear_aux where insert = vset_insert and
 sel = sel and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and
s = s and f = f for F s f
defines dircycle_linear_initial_state = dircycle.dircycle_linear_initial_state and
find_dircycle_linear = dircycle.dc.DFS_skel_impl and
cyc_found = dircycle.cyc_found and
neighbourhood = dircycle.Graph.neighbourhood
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS_dircycle_linear_aux.intro DFS_dircycle.intro simp add: edge_map_update_def
                                           RBT_Set.empty_def adj_inv_def map_empty_def vset_inv_def)

lemmas find_dircycle_linear_code[code] =
  dircycle.dc.DFS_skel_impl.simps[folded find_dircycle_linear_def[folded cyc_found_def],
    unfolded dircycle.cyc_on_found_def dircycle.cyc_on_empty_def dircycle.cyc_on_backtrack_def]

global_interpretation dclin: DFS_DirCycle_Linear where insert = vset_insert and
 sel = sel and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and V = W and
dfs_aux = "\<lambda>s fs. find_dircycle_linear F (dircycle_linear_initial_state s fs)" and
fin_aux = finished and cycle_aux = DFS_dircycle_state.cycle for F W
defines sweep_initial_state = dclin.initial_state and
sweep_dircycle = dclin.DFS_DirCycle_Linear_impl
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by(auto intro!: DFS_DirCycle_Linear.intro simp add: edge_map_update_def RBT_Set.empty_def adj_inv_def map_empty_def
                                           vset_inv_def)

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

text \<open>Code refinement: as written, \<^const>\<open>fact_idx\<close> is \<^term>\<open>idx_of (dl_cert_facts c)\<close>, so the generated
  code rebuilds \<^const>\<open>dl_cert_facts\<close> --- an \<open>O(R\<^sup>2)\<close> \<^const>\<open>remdups\<close> --- once for \<^emph>\<open>each\<close> of the
  \<open>2\<cdot>|dep_edges|\<close> endpoint relabellings, i.e. \<open>O(|edges|\<cdot>R\<^sup>2)\<close> (this, not the per-vertex DFS, is what
  dominates \<open>dl_acyclic_dfs\<close>). Binding \<^const>\<open>dl_cert_facts\<close> once with a \<^theory_text>\<open>let\<close>
  drops it to \<open>O(R\<^sup>2 + |edges|\<cdot>R)\<close>. Pure refinement (definitionally equal).\<close>
lemma nat_edges_code [code]:
  "nat_edges c = (let facts = dl_cert_facts c in
                  map (\<lambda>(a, b). (idx_of facts a, idx_of facts b)) (dep_edges c))"
  by (simp add: nat_edges_def fact_idx_def Let_def)

definition dep_adjmap :: "('p, 'c) dl_certificate \<Rightarrow> _" where
  "dep_adjmap c = a_graph (nat_edges c)"

subsection \<open>The executable acyclicity check\<close>

text \<open>The sweep needs the support graph's vertex set as a vset. \<^const>\<open>dVs\<close> of an edge set is
  exactly its set of endpoints, so collecting both projections of the edge list gives it --- and,
  unlike the fact-index range \<open>[0..<length (dl_cert_facts c)]\<close> the per-vertex check swept, it is
  the vertex set \<^emph>\<open>exactly\<close>, which is what \<open>DFS_DirCycle_Linear_axioms\<close> demands.\<close>

definition dep_verts :: "('p, 'c) dl_certificate \<Rightarrow> _" where
  "dep_verts c = foldr (\<lambda>x t. RBT_Set.insert x t)
                       (map fst (nat_edges c) @ map snd (nat_edges c)) Leaf"

text \<open>Its \<^const>\<open>vset_inv\<close> / \<^const>\<open>t_set\<close> characterisation needs the \<^const>\<open>RBT_Set.insert\<close>
  lemmas below, so it is proved there (\<open>dep_verts_inv\<close>, \<open>dep_verts_set\<close>).\<close>

text \<open>The support graph is acyclic iff the whole-graph sweep reports no back edge. One pass: each
  inner DFS is seeded with the region its predecessors finished, so no vertex is explored twice.\<close>

definition dl_acyclic_dfs :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_acyclic_dfs c =
     (\<not> cyc (sweep_dircycle (dep_adjmap c) (dep_verts c) sweep_initial_state))"

lemmas dl_acyclic_dfs_code [code] = dl_acyclic_dfs_def

lemmas sweep_dircycle_code [code] =
  dclin.DFS_DirCycle_Linear_impl.simps[folded sweep_dircycle_def]

lemmas sweep_initial_state_code [code] = sweep_initial_state_def

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

lemma dep_verts_inv: "vset_inv (dep_verts c)"
  unfolding dep_verts_def by (rule foldr_rbt_insert_inv)

lemma dep_verts_set: "t_set (dep_verts c) = dVs (set (nat_edges c))"
  unfolding dep_verts_def
  by (simp add: foldr_rbt_insert_set dVs_eq del: foldr_append)

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

text \<open>Step 5: the sweep's two locale obligations at the support graph, and then acyclicity. The
  per-vertex check needed an index-range argument here (every cycle vertex is a certified fact, so
  some swept source hits the cycle); the sweep needs none, because it is driven by the graph's own
  vertex set and reports on the \<^emph>\<open>whole\<close> graph in one go.\<close>

lemma dep_adjmap_axioms:
  "dclin.DFS_DirCycle_Linear_axioms TYPE(nat) (a_graph (nat_edges c)) (dep_verts c)"
  unfolding dclin.DFS_DirCycle_Linear_axioms_def
  by (simp add: a_graph_graph_inv a_graph_finite_graph a_graph_finite_vsets a_graph_digraph_abs
                dep_verts_inv dep_verts_set)

text \<open>The inner DFS meets the contract the sweep assumes of it. For a root outside a seed satisfying
  \<open>seed_ok\<close>, the run's five structural exports together with its own soundness and completeness are
  exactly the seven conjuncts of \<open>dfs_aux_axioms\<close> --- which is the whole point of stating those
  exports in \<open>DFS_DirCycle_Linear_Aux\<close>.\<close>

lemma dep_adjmap_aux_axioms: "dclin.dfs_aux_axioms TYPE(nat) (a_graph E)"
  unfolding dclin.dfs_aux_axioms_def
proof (intro ballI allI impI)
  fix s fs
  assume sV: "s \<in> dVs (dircycle.Graph.digraph_abs (a_graph E))"
     and ok: "dclin.seed_ok (a_graph E) fs"
     and snew: "s \<notin> t_set fs"
  interpret aux: DFS_dircycle_linear_aux_thms where insert = vset_insert and
    sel = sel and vset_empty = vset_empty and diff = vset_diff and
    lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
    and vset_inv = vset_inv and union = vset_union and inter = vset_inter
    and G = "a_graph E" and s = s and f = fs
  proof
    show "dircycle.DFS_dircycle_linear_aux_axioms TYPE(nat) (a_graph E) s fs"
      using sV snew ok
      by (simp add: dircycle.DFS_dircycle_linear_aux_axioms_def dircycle.DFS_dircycle_axioms_def
                    dclin.seed_ok_def a_graph_graph_inv a_graph_finite_graph a_graph_finite_vsets
                    a_graph_digraph_abs)
  qed
  have impl: "find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs)
                = aux.dircycle_linear_result"
    unfolding find_dircycle_linear_def dircycle_linear_initial_state_def
    by (rule aux.dc.DFS_skel_impl_same[OF aux.dircycle_linear_initial_dom])
  show "vset_inv (finished (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs)))
        \<and> t_set fs \<subseteq> t_set (finished (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs)))
        \<and> t_set (finished (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs)))
             \<subseteq> dVs (dircycle.Graph.digraph_abs (a_graph E))
        \<and> (\<forall>u w. u \<in> t_set (finished (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs))) \<longrightarrow>
              (u, w) \<in> dircycle.Graph.digraph_abs (a_graph E) \<longrightarrow>
              w \<in> t_set (finished (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs))))
        \<and> (DFS_dircycle_state.cycle (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs)) \<longrightarrow>
              (\<exists>p. Awalk_Defs.cycle (dircycle.Graph.digraph_abs (a_graph E)) p))
        \<and> (\<not> DFS_dircycle_state.cycle (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs)) \<longrightarrow>
              s \<in> t_set (finished (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs)))
              \<and> (\<nexists>p. Awalk_Defs.cycle (dircycle.Graph.digraph_abs (a_graph E) \<downharpoonright>
                        t_set (finished (find_dircycle_linear (a_graph E) (dircycle_linear_initial_state s fs)))) p))"
    unfolding impl
    using aux.dircycle_linear_finished_inv aux.dircycle_linear_seed_subset
    using aux.dircycle_linear_finished_subset_dVs aux.dircycle_linear_finished_closed
    using aux.DFS_dircycle_linear_sound aux.dircycle_linear_root_finished
    using aux.DFS_dircycle_linear_complete
    by blast
qed

text \<open>Step 6: a clean sweep means the whole support graph is acyclic.\<close>

lemma dl_acyclic_dfs_imp_acyclic:
  assumes dfs: "dl_acyclic_dfs c"
  shows "acyclic (dl_dep_graph c)"
proof (rule ccontr)
  let ?E = "nat_edges c"
  interpret sweep: DFS_DirCycle_Linear_thms where insert = vset_insert and
    sel = sel and vset_empty = vset_empty and diff = vset_diff and
    lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
    and vset_inv = vset_inv and union = vset_union and inter = vset_inter
    and G = "a_graph ?E" and V = "dep_verts c"
    and dfs_aux = "\<lambda>s fs. find_dircycle_linear (a_graph ?E) (dircycle_linear_initial_state s fs)"
    and fin_aux = finished and cycle_aux = DFS_dircycle_state.cycle
  proof
    show "dclin.DFS_DirCycle_Linear_axioms TYPE(nat) (a_graph ?E) (dep_verts c)"
      by (rule dep_adjmap_axioms)
    show "dclin.dfs_aux_axioms TYPE(nat) (a_graph ?E)"
      by (rule dep_adjmap_aux_axioms)
  qed
  have impl: "sweep_dircycle (a_graph ?E) (dep_verts c) sweep_initial_state
                = dclin.DFS_DirCycle_Linear (dep_verts c) (a_graph ?E) sweep_initial_state"
    unfolding sweep_initial_state_def
    by (rule dclin.DFS_DirCycle_Linear_impl_same[OF sweep.initial_state_props(4)])
  have "\<nexists>p. Awalk_Defs.cycle (set ?E) p"
    using sweep.DFS_DirCycle_Linear_complete[folded sweep_initial_state_def] dfs
    by (simp add: dl_acyclic_dfs_def dep_adjmap_def impl a_graph_digraph_abs)
  moreover
  assume "\<not> acyclic (dl_dep_graph c)"
  hence "\<not> acyclic (set ?E)" by (rule not_acyclic_dep_graph_imp_nat_edges)
  hence "\<exists>p. Awalk_Defs.cycle (set ?E) p" by (rule not_acyclic_imp_cycle)
  ultimately show False by blast
qed

subsection \<open>The certificate's support graph is founded when the DFS reports acyclic\<close>

theorem dl_acyclic_dfs_imp_dl_founded:
  assumes "dl_body_closed c" and "dl_acyclic_dfs c"
  shows "dl_founded c"
  using acyclic_dep_graph_imp_dl_founded[OF assms(1) dl_acyclic_dfs_imp_acyclic[OF assms(2)]] .

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
      \<and> dl_rules_valid_oi Pl Ul (dl_rules c)
      \<and> dl_closure_check_exec Pl Ul c
      \<and> dl_body_closed c
      \<and> dl_acyclic_dfs c)"

lemma dl_admissible_dfs_imp:
  assumes "dl_admissible_dfs Pl Ul c"
  shows "dl_admissible (set Pl) (set Ul) c"
proof -
  have pos: "dl_positive_prog_exec Pl"
    and rv: "list_all (dl_rule_valid_oi Pl Ul) (dl_rules c)"
    and cc: "dl_closure_check_exec Pl Ul c"
    and bc: "dl_body_closed c"
    and ac: "dl_acyclic_dfs c"
    using assms unfolding dl_admissible_dfs_def dl_rules_valid_oi_def by auto
  have "dl_positive_prog (set Pl)" using pos by (simp add: dl_positive_prog_exec_iff)
  moreover have "\<forall>r \<in> set (dl_rules c). dl_rule_valid (set Pl) (set Ul) r"
    using rv by (auto simp: list_all_iff dl_rule_valid_oi_eq)
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
