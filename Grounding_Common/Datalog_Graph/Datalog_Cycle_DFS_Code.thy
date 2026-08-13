theory Datalog_Cycle_DFS_Code
  imports
    Datalog_Cycle_DFS
    Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Refine
begin

section \<open>The refined directed-cycle sweep at the certificate's support graph\<close>

subsection \<open>A set-determined choice on red-black trees\<close>

text \<open>The refined inner DFS assumes \<open>sel_cong\<close>: the chosen element depends only on the element
  set. The red-black \<^const>\<open>sel\<close> of \<^theory>\<open>Directed_Set_Graphs.Pair_Graph_RBT\<close> returns the
  \<^emph>\<open>root label\<close>, which is not a function of the set, so it cannot serve. We choose the
  \<^emph>\<open>leftmost\<close> element instead --- for a search tree that is the minimum, hence determined by the
  set.

  The choice is written so that \<^locale>\<open>Set_Choose\<close>'s obligation \<open>isin s (sel s)\<close> holds for
  \<^emph>\<open>every\<close> tree, not only for search trees (the locale grants no \<open>invar\<close>): descending left is
  only taken when it yields something smaller than the current label, so \<^const>\<open>isin\<close>'s own search
  path follows it.\<close>

fun sel_min :: "('a::linorder \<times> 'b) tree \<Rightarrow> 'a" where
  "sel_min Leaf = undefined"
| "sel_min (Node l (a, b) r) =
     (if l = Leaf then a else (let x = sel_min l in if x < a then x else a))"

lemma sel_min_isin:
  assumes "t \<noteq> Leaf"
  shows "isin t (sel_min t)"
  using assms
proof (induction t rule: sel_min.induct)
  case 1
  thus ?case by simp
next
  case (2 l a b r)
  show ?case
  proof (cases "l = Leaf")
    case True
    thus ?thesis by simp
  next
    case False
    hence il: "isin l (sel_min l)" using 2(1) by simp
    show ?thesis
    proof (cases "sel_min l < a")
      case True
      thus ?thesis using il False by simp
    next
      case False
      thus ?thesis by simp
    qed
  qed
qed

lemma sel_min_eq_Min:
  assumes "Tree2.bst t" and "t \<noteq> Leaf"
  shows "sel_min t = Min (Tree2.set_tree t)"
  using assms
proof (induction t rule: sel_min.induct)
  case 1
  thus ?case by simp
next
  case (2 l a b r)
  have bl: "Tree2.bst l"
    and la: "\<forall>x \<in> Tree2.set_tree l. x < a"
    and ar: "\<forall>x \<in> Tree2.set_tree r. a < x"
    using 2(2) by auto
  show ?case
  proof (cases "l = Leaf")
    case True
    have "Min (Tree2.set_tree (Node l (a, b) r)) = a"
    proof (rule Min_eqI)
      show "finite (Tree2.set_tree (Node l (a, b) r))" by simp
      show "a \<le> y" if "y \<in> Tree2.set_tree (Node l (a, b) r)" for y
        using that True ar by force
      show "a \<in> Tree2.set_tree (Node l (a, b) r)" by simp
    qed
    thus ?thesis using True by simp
  next
    case False
    have IH: "sel_min l = Min (Tree2.set_tree l)" using 2(1) False bl by simp
    have mem: "Min (Tree2.set_tree l) \<in> Tree2.set_tree l"
      using False by (simp add: Min_in)
    hence lt: "Min (Tree2.set_tree l) < a" using la by simp
    have "Min (Tree2.set_tree (Node l (a, b) r)) = Min (Tree2.set_tree l)"
    proof (rule Min_eqI)
      show "finite (Tree2.set_tree (Node l (a, b) r))" by simp
      show "Min (Tree2.set_tree l) \<le> y" if y: "y \<in> Tree2.set_tree (Node l (a, b) r)" for y
      proof -
        consider "y = a" | "y \<in> Tree2.set_tree l" | "y \<in> Tree2.set_tree r"
          using y by auto
        thus ?thesis
        proof cases
          case 1
          thus ?thesis using lt by order
        next
          case 2
          thus ?thesis by simp
        next
          case 3
          hence "a < y" using ar by simp
          thus ?thesis using lt by order
        qed
      qed
      show "Min (Tree2.set_tree l) \<in> Tree2.set_tree (Node l (a, b) r)" using mem by simp
    qed
    thus ?thesis using False IH lt by (simp add: Let_def)
  qed
qed

lemma sel_min_cong:
  assumes "vset_inv X"
      and "vset_inv Y"
      and "t_set X = t_set Y"
  shows "sel_min X = sel_min Y"
proof (cases "X = Leaf")
  case True
  hence "Tree2.set_tree Y = {}" using assms(3)[symmetric] by simp
  hence "Y = Leaf" by simp
  thus ?thesis using True by simp
next
  case False
  hence "Y \<noteq> Leaf" using assms(3) by auto
  thus ?thesis
    using False assms(1,2,3) by (simp add: sel_min_eq_Min vset_inv_def)
qed

text \<open>The red-black graph ADT again, with \<^const>\<open>sel_min\<close> in place of \<^const>\<open>sel\<close>. Only the
  \<^locale>\<open>Set_Choose\<close> obligation changes; everything else is the existing interpretation's.\<close>

lemma Pair_Graph_Specs_sel_min:
  "Pair_Graph_Specs map_empty delete lookup vset_insert isin t_set sel_min update adj_inv
     vset_empty vset_delete vset_inv"
proof (rule Pair_Graph_Specs.intro, goal_cases)
  case 1
  show ?case
    using Map_axioms_as_needed by (simp add: map_empty_def adj_inv_def)
next
  case 2
  show ?case
  proof (rule Set_Choose.intro, goal_cases)
    case 1
    show ?case
      using set.Set_axioms by (simp add: RBT_Set.empty_def)
  next
    case 2
    show ?case
      by (simp add: Set_Choose_axioms_def RBT_Set.empty_def sel_min_isin)
  qed
qed

text \<open>The four locale predicates the instantiations below discharge. They are also what turns the
  locales' \<^emph>\<open>conditional\<close> definitional equations (a locale with assumptions exports its
  \<open>definition\<close>s guarded by its own predicate) into plain rewrite rules --- see
  \<open>sweep_defs\<close> below.\<close>

lemma DFS_dircycle_linear_tracked_aux_sel_min:
  "DFS_dircycle_linear_tracked_aux map_empty delete vset_insert isin t_set sel_min update adj_inv
     vset_empty vset_delete vset_inv vset_union vset_inter vset_diff lookup"
  using Pair_Graph_Specs_sel_min RBT.Set2_axioms
  by (auto intro!: DFS_dircycle_linear_tracked_aux.intro simp add: RBT_Set.empty_def vset_inv_def)

lemma DFS_dircycle_linear_tracked_aux_refine_sel_min:
  "DFS_dircycle_linear_tracked_aux_refine map_empty delete vset_insert isin t_set sel_min update adj_inv
     vset_empty vset_delete vset_inv vset_union vset_inter vset_diff lookup"
  by (rule DFS_dircycle_linear_tracked_aux_refine.intro[OF DFS_dircycle_linear_tracked_aux_sel_min])

lemma DFS_dircycle_linear_tracked_sel_min:
  "DFS_dircycle_linear_tracked map_empty delete vset_insert isin t_set sel_min update adj_inv
     vset_empty vset_delete vset_inv vset_union vset_inter vset_diff lookup"
  using Pair_Graph_Specs_sel_min RBT.Set2_axioms
  by (auto intro!: DFS_dircycle_linear_tracked.intro simp add: RBT_Set.empty_def vset_inv_def)

lemma DFS_dircycle_linear_tracked_refine_sel_min:
  "DFS_dircycle_linear_tracked_refine map_empty delete vset_insert isin t_set sel_min update adj_inv
     vset_empty vset_delete vset_inv vset_union vset_inter vset_diff lookup"
  by (rule DFS_dircycle_linear_tracked_refine.intro[OF DFS_dircycle_linear_tracked_sel_min])

lemmas sweep_defs =
  DFS_dircycle_linear_tracked_aux.DFS_dircycle_linear_tracked_aux_axioms_def[OF DFS_dircycle_linear_tracked_aux_sel_min]
  DFS_dircycle_linear_tracked.DFS_dircycle_linear_tracked_axioms_def[OF DFS_dircycle_linear_tracked_sel_min]
  DFS_dircycle_linear_tracked.dfs_aux_axioms_def[OF DFS_dircycle_linear_tracked_sel_min]
  DFS_dircycle_linear_tracked.seed_ok_def[OF DFS_dircycle_linear_tracked_sel_min]
  DFS_dircycle_linear_tracked.part_ok_def[OF DFS_dircycle_linear_tracked_sel_min]
  DFS_dircycle_linear_tracked_refine.rdfs_aux_axioms_def[OF DFS_dircycle_linear_tracked_refine_sel_min]
  DFS_dircycle_linear_tracked_refine.adj_ok_def[OF DFS_dircycle_linear_tracked_refine_sel_min]

subsection \<open>The refined directed-cycle sweep over RBT adjacency maps\<close>

text \<open>Three instantiations at the red-black-tree representation, all with \<^const>\<open>sel_min\<close>: the
  \<^emph>\<open>tracked\<close> inner DFS of level 1 (\<^locale>\<open>DFS_dircycle_linear_tracked_aux\<close>) --- which is only ever the
  specification the refinement is measured against, never run --- the \<^emph>\<open>refined\<close> inner DFS of
  level 2 (\<^locale>\<open>DFS_dircycle_linear_tracked_aux_refine\<close>), and the outer sweep
  \<^locale>\<open>DFS_dircycle_linear_tracked_refine\<close> that threads the pruned adjacency map from one inner call to the
  next.\<close>

global_interpretation dctracked: DFS_dircycle_linear_tracked_aux where insert = vset_insert and
 sel = sel_min and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and
s = s and f = f and uf = uf for F s f uf
defines tracked_initial_state = dctracked.dircycle_tracked_initial_state and
find_dircycle_tracked = dctracked.dc.DFS_skeleton_impl and
rbt_delete_edge = dctracked.Graph.delete_edge
  by (rule DFS_dircycle_linear_tracked_aux_sel_min)

global_interpretation rdircycle: DFS_dircycle_linear_tracked_aux_refine where insert = vset_insert and
 sel = sel_min and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and
s = s and f = f and uf = uf and R = Rv and A = Av for F s f uf Rv Av
defines del_preds_rbt = rdircycle.del_preds and
del_in_edges_rbt = rdircycle.del_in_edges and
dircycle_refine_init = rdircycle.dircycle_refine_initial_state and
find_dircycle_refine = rdircycle.rdc.DFS_skeleton_refine_impl and
rcyc_found_rbt = rdircycle.rcyc_found
  by (rule DFS_dircycle_linear_tracked_aux_refine_sel_min)

text \<open>Code equations. As at level 0, the equations the interpretation exports still mention the
  \<^emph>\<open>locale\<close> constants \<^const>\<open>Pair_Graph_Specs.neighbourhood\<close> and
  \<^const>\<open>Pair_Graph_Specs.delete_edge\<close>, for which the code generator has nothing; folding them onto
  the global \<^const>\<open>neighbourhood\<close> of \<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS\<close> and the
  \<^const>\<open>rbt_delete_edge\<close> defined above fixes that. The inner loop's own unfolding rule has to be
  restated with the callbacks expanded, again exactly as at level 0.\<close>

declare [[code drop: del_preds_rbt del_in_edges_rbt rcyc_found_rbt]]

lemmas del_preds_rbt_code [code] = rdircycle.del_preds.simps[folded rbt_delete_edge_def]

lemmas del_in_edges_rbt_code [code] = rdircycle.del_in_edges_def[folded neighbourhood_def]

lemmas rcyc_found_rbt_code [code] = rdircycle.rcyc_found_def[folded neighbourhood_def]

lemmas find_dircycle_refine_code [code] =
  rdircycle.rdc.DFS_skeleton_refine_impl.simps[folded find_dircycle_refine_def[folded rcyc_found_rbt_def],
    unfolded rdircycle.rcyc_on_found_def rdircycle.rcyc_on_empty_def
             rdircycle.rcyc_on_backtrack_def rdircycle.rcyc_on_push_def,
    folded neighbourhood_def]

global_interpretation rdclin: DFS_dircycle_linear_tracked_refine where insert = vset_insert and
 sel = sel_min and vset_empty = vset_empty and diff = vset_diff and
 lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
and vset_inv = vset_inv and union = vset_union and inter = vset_inter and G = F and V = W and
dfs_aux = "\<lambda>s fs us. find_dircycle_tracked F (tracked_initial_state s fs us)" and
fin_aux = DFS_dircycle_linear_tracked_aux_state.finished and
unfin_aux = DFS_dircycle_linear_tracked_aux_state.unfinished and
cycle_aux = DFS_dircycle_linear_tracked_aux_state.cycle and
rdfs_aux = "\<lambda>s fs us M. find_dircycle_refine F Rv (dircycle_refine_init s fs us Rv M)" and
rfin_aux = DFS_dircycle_linear_tracked_aux_state.finished and
runfin_aux = DFS_dircycle_linear_tracked_aux_state.unfinished and
rcycle_aux = DFS_dircycle_linear_tracked_aux_state.cycle and
radj_aux = DFS_dircycle_linear_tracked_aux_refine_state.adj
for F W Rv
defines sweep_refine_init = rdclin.refine_initial_state and
sweep_dircycle_refine = rdclin.DFS_dircycle_linear_tracked_refine_impl
  by (rule DFS_dircycle_linear_tracked_refine_sel_min)

subsection \<open>The support graph's reverse adjacency map\<close>

text \<open>The refined inner DFS deletes, at every push, the edges \<^emph>\<open>entering\<close> the pushed vertex.
  \<^const>\<open>Pair_Graph_Specs.delete_edge\<close> is keyed by an edge's source, so it needs the pushed
  vertex's predecessors --- a \<^emph>\<open>static\<close> reverse adjacency map, built once and never updated.
  Reversing the support graph's edge list and reusing \<^const>\<open>a_graph\<close> gives it, and its two
  contract lemmas come straight from the \<open>a_graph_\<dots>\<close> lemmas of
  \<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS\<close>.\<close>

definition dep_radjmap :: "('p, 'c) dl_certificate \<Rightarrow> _" where
  "dep_radjmap c = a_graph (map prod.swap (nat_edges c))"

lemma a_graph_swap_neighbourhood:
  "t_set (dctracked.Graph.neighbourhood (a_graph (map prod.swap E)) u) = {p. (p, u) \<in> set E}"
  by (force simp: a_graph_neighbourhood[unfolded neighbourhood_def])

lemma dep_radjmap_graph_inv: "dctracked.Graph.graph_inv (dep_radjmap c)"
  unfolding dep_radjmap_def by (rule a_graph_graph_inv)

lemma dep_radjmap_preds:
  "t_set (dctracked.Graph.neighbourhood (dep_radjmap c) u)
     = {p. (p, u) \<in> dctracked.Graph.digraph_abs (dep_adjmap c)}"
  by (simp add: dep_radjmap_def dep_adjmap_def a_graph_swap_neighbourhood a_graph_digraph_abs)

subsection \<open>The refined executable acyclicity check\<close>

definition dl_acyclic_dfs_code :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_acyclic_dfs_code c =
     (\<not> sweep_cyc (sweep_dircycle_refine (dep_adjmap c) (dep_radjmap c)
                     (sweep_refine_init (dep_adjmap c) (dep_verts c))))"

text \<open>The \<^emph>\<open>tracked\<close> inner DFS meets the sweep's abstract contract, exactly as the level-0 inner
  DFS meets it in \<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS\<close>: for a root outside a seed satisfying
  \<open>seed_ok\<close> whose complement satisfies \<open>part_ok\<close>, the run's structural exports together with its
  soundness and completeness are the seven conjuncts of \<open>dfs_aux_axioms\<close>.\<close>

lemma a_graph_tracked_aux_axioms:
  "DFS_dircycle_linear_tracked.dfs_aux_axioms isin t_set vset_empty vset_inv lookup (a_graph E)
     (\<lambda>s fs us. find_dircycle_tracked (a_graph E) (tracked_initial_state s fs us))
     DFS_dircycle_linear_tracked_aux_state.finished DFS_dircycle_linear_tracked_aux_state.unfinished
     DFS_dircycle_linear_tracked_aux_state.cycle"
  unfolding sweep_defs(3)
proof (intro ballI allI impI, goal_cases call)
  case (call s fs us)
  interpret aux: DFS_dircycle_linear_tracked_aux_thms where insert = vset_insert and
    sel = sel_min and vset_empty = vset_empty and diff = vset_diff and
    lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
    and vset_inv = vset_inv and union = vset_union and inter = vset_inter
    and G = "a_graph E" and s = s and f = fs and uf = us
  proof (unfold_locales, goal_cases)
    case 1
    show ?case
      using call
      by (simp add: sweep_defs(1,4,5) a_graph_graph_inv a_graph_finite_graph
                    a_graph_finite_vsets a_graph_digraph_abs)
  qed
  have impl: "find_dircycle_tracked (a_graph E) (tracked_initial_state s fs us)
                = aux.dircycle_tracked_result"
    unfolding tracked_initial_state_def
    by (rule dctracked.dc.DFS_skeleton_impl_same[OF aux.dircycle_tracked_initial_dom])
  show ?case
    unfolding impl sweep_defs(5)
    using aux.dircycle_tracked_finished_inv aux.dircycle_tracked_seed_subset
    using aux.dircycle_tracked_finished_subset_dVs aux.dircycle_tracked_finished_closed
    using aux.DFS_dircycle_linear_tracked_aux_sound aux.dircycle_tracked_root_finished
    using aux.DFS_dircycle_linear_tracked_aux_complete
    using aux.dircycle_tracked_unfinished_inv aux.dircycle_tracked_unfinished_char
    by blast
qed

text \<open>And the \<^emph>\<open>refined\<close> inner DFS meets the refinement contract: on a legitimate call it agrees
  with the tracked one on the three components the sweep reads, and on a clean run hands back a map
  that is again \<open>adj_ok\<close> --- theorems \<open>dircycle_refine_components\<close> and
  \<open>dircycle_refine_adj_abs_finished\<close> of
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Aux_Refine\<close>. This is where the two genuinely
  new ingredients are consumed: \<^const>\<open>dep_radjmap\<close> discharges \<open>R_graph_inv\<close>/\<open>R_preds\<close>, and
  \<^const>\<open>sel_min\<close> discharges \<open>sel_cong\<close>.\<close>

lemma dep_adjmap_refine_aux_axioms:
  "DFS_dircycle_linear_tracked_refine.rdfs_aux_axioms isin t_set adj_inv vset_empty vset_inv
     (a_graph (nat_edges c))
     (\<lambda>s fs us. find_dircycle_tracked (a_graph (nat_edges c)) (tracked_initial_state s fs us))
     DFS_dircycle_linear_tracked_aux_state.finished DFS_dircycle_linear_tracked_aux_state.unfinished
     DFS_dircycle_linear_tracked_aux_state.cycle lookup
     (\<lambda>s fs us M. find_dircycle_refine (a_graph (nat_edges c)) (dep_radjmap c)
                    (dircycle_refine_init s fs us (dep_radjmap c) M))
     DFS_dircycle_linear_tracked_aux_state.finished DFS_dircycle_linear_tracked_aux_state.unfinished
     DFS_dircycle_linear_tracked_aux_state.cycle DFS_dircycle_linear_tracked_aux_refine_state.adj"
  unfolding sweep_defs(6)
proof (intro ballI allI impI, goal_cases call)
  case (call s fs us M)
  interpret raux: DFS_dircycle_linear_tracked_aux_refine_thms where insert = vset_insert and
    sel = sel_min and vset_empty = vset_empty and diff = vset_diff and
    lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
    and vset_inv = vset_inv and union = vset_union and inter = vset_inter
    and G = "a_graph (nat_edges c)" and s = s and f = fs and uf = us
    and R = "dep_radjmap c" and A = M
  proof (unfold_locales, goal_cases)
    case 1
    show ?case
      using call(1,2,3,4)
      by (simp add: sweep_defs(1,4,5) a_graph_graph_inv a_graph_finite_graph
                    a_graph_finite_vsets a_graph_digraph_abs)
  next
    case 2
    show ?case using 2 by (rule sel_min_cong)
  next
    case 3
    show ?case by (rule dep_radjmap_graph_inv)
  next
    case 4
    show ?case using dep_radjmap_preds by (simp add: dep_adjmap_def)
  next
    case 5
    show ?case using call(5) by (simp add: sweep_defs(7))
  next
    case 6
    show ?case using call(5) by (simp add: sweep_defs(7))
  qed
  have rimpl: "find_dircycle_refine (a_graph (nat_edges c)) (dep_radjmap c)
                 (dircycle_refine_init s fs us (dep_radjmap c) M) = raux.dircycle_refine_result"
    unfolding find_dircycle_refine_def dircycle_refine_init_def
    using raux.dircycle_refine_impl_eq_more raux.dircycle_refine_eq_more by simp
  have timpl: "find_dircycle_tracked (a_graph (nat_edges c)) (tracked_initial_state s fs us)
                 = raux.dircycle_tracked_result"
    unfolding tracked_initial_state_def
    by (rule dctracked.dc.DFS_skeleton_impl_same[OF raux.dircycle_tracked_initial_dom])
  show ?case
    unfolding rimpl timpl sweep_defs(7)
    using raux.dircycle_refine_components(3,5,6)
    using raux.dircycle_refine_adj_graph_inv
    using raux.dircycle_refine_adj_abs_finished
    by blast
qed

text \<open>The refined sweep is sound and complete on the support graph, so its verdict \<^emph>\<open>is\<close> the
  graph's acyclicity. Both halves are inherited: they are \<open>DFS_dircycle_linear_tracked_refine_sound\<close> /
  \<open>DFS_dircycle_linear_tracked_refine_complete\<close>, which
  \<^theory>\<open>Directed_Cycle_DFS.DFS_DirCycle_Linear_Tracked_Refine\<close> transports from level 1 rather than
  re-proving.\<close>

lemma dl_acyclic_dfs_code_iff:
  "dl_acyclic_dfs_code c = (\<nexists>p. Awalk_Defs.cycle (set (nat_edges c)) p)"
proof -
  let ?E = "nat_edges c"
  interpret sweep: DFS_dircycle_linear_tracked_refine_thms where insert = vset_insert and
    sel = sel_min and vset_empty = vset_empty and diff = vset_diff and
    lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
    and vset_inv = vset_inv and union = vset_union and inter = vset_inter
    and G = "a_graph ?E" and V = "dep_verts c"
    and dfs_aux = "\<lambda>s fs us. find_dircycle_tracked (a_graph ?E) (tracked_initial_state s fs us)"
    and fin_aux = DFS_dircycle_linear_tracked_aux_state.finished
    and unfin_aux = DFS_dircycle_linear_tracked_aux_state.unfinished
    and cycle_aux = DFS_dircycle_linear_tracked_aux_state.cycle
    and rdfs_aux = "\<lambda>s fs us M. find_dircycle_refine (a_graph ?E) (dep_radjmap c)
                                  (dircycle_refine_init s fs us (dep_radjmap c) M)"
    and rfin_aux = DFS_dircycle_linear_tracked_aux_state.finished
    and runfin_aux = DFS_dircycle_linear_tracked_aux_state.unfinished
    and rcycle_aux = DFS_dircycle_linear_tracked_aux_state.cycle
    and radj_aux = DFS_dircycle_linear_tracked_aux_refine_state.adj
  proof (unfold_locales, goal_cases)
    case 1
    show ?case
      unfolding sweep_defs(2)
      by (simp add: a_graph_graph_inv a_graph_finite_graph a_graph_finite_vsets
                    a_graph_digraph_abs dep_verts_inv dep_verts_set)
  next
    case 2
    show ?case by (rule a_graph_tracked_aux_axioms)
  next
    case 3
    show ?case by (rule dep_adjmap_refine_aux_axioms)
  qed
  have impl: "sweep_dircycle_refine (a_graph ?E) (dep_radjmap c)
                (sweep_refine_init (a_graph ?E) (dep_verts c))
                = rdclin.DFS_dircycle_linear_tracked_refine (a_graph ?E) (dep_radjmap c)
                    (sweep_refine_init (a_graph ?E) (dep_verts c))"
    unfolding sweep_refine_init_def
    by (rule rdclin.DFS_dircycle_linear_tracked_refine_impl_same[OF sweep.refine_initial_state_props(6)])
  show ?thesis
    using sweep.DFS_dircycle_linear_tracked_refine_sound[folded sweep_refine_init_def]
    using sweep.DFS_dircycle_linear_tracked_refine_complete[folded sweep_refine_init_def]
    by (auto simp: dl_acyclic_dfs_code_def dep_adjmap_def impl a_graph_digraph_abs)
qed

lemma dl_acyclic_dfs_code_imp_acyclic:
  assumes dfs: "dl_acyclic_dfs_code c"
  shows "acyclic (dl_dep_graph c)"
proof (rule ccontr)
  assume "\<not> acyclic (dl_dep_graph c)"
  hence "\<not> acyclic (set (nat_edges c))" by (rule not_acyclic_dep_graph_imp_nat_edges)
  hence "\<exists>p. Awalk_Defs.cycle (set (nat_edges c)) p" by (rule not_acyclic_imp_cycle)
  thus False using dfs by (simp add: dl_acyclic_dfs_code_iff)
qed

theorem dl_acyclic_dfs_code_imp_dl_founded:
  assumes "dl_body_closed c" and "dl_acyclic_dfs_code c"
  shows "dl_founded c"
  using acyclic_dep_graph_imp_dl_founded[OF assms(1) dl_acyclic_dfs_code_imp_acyclic[OF assms(2)]] .

subsection \<open>The refined check is the reference check\<close>

text \<open>The level-0 sweep of \<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS\<close> is sound and complete on the
  same graph, so it has the same verdict --- and the two locale obligations it needs were already
  discharged there (\<open>dep_adjmap_axioms\<close>, \<open>dep_adjmap_aux_axioms\<close>).\<close>

lemma dl_acyclic_dfs_iff:
  "dl_acyclic_dfs c = (\<nexists>p. Awalk_Defs.cycle (set (nat_edges c)) p)"
proof -
  let ?E = "nat_edges c"
  interpret sweep0: DFS_dircycle_linear_thms where insert = vset_insert and
    sel = sel and vset_empty = vset_empty and diff = vset_diff and
    lookup = lookup and empty = map_empty and delete = delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv and vset_delete = vset_delete
    and vset_inv = vset_inv and union = vset_union and inter = vset_inter
    and G = "a_graph ?E" and V = "dep_verts c"
    and dfs_aux = "\<lambda>s fs. find_dircycle_linear (a_graph ?E) (dircycle_linear_initial_state s fs)"
    and fin_aux = DFS_dircycle_state.finished and cycle_aux = DFS_dircycle_state.cycle
  proof
    show "dclin.DFS_dircycle_linear_axioms TYPE(nat) (a_graph ?E) (dep_verts c)"
      by (rule dep_adjmap_axioms)
    show "dclin.dfs_aux_axioms TYPE(nat) (a_graph ?E)"
      by (rule dep_adjmap_aux_axioms)
  qed
  have impl: "sweep_dircycle (a_graph ?E) (dep_verts c) sweep_initial_state
                = dclin.DFS_dircycle_linear (dep_verts c) (a_graph ?E) sweep_initial_state"
    unfolding sweep_initial_state_def
    by (rule dclin.DFS_dircycle_linear_impl_same[OF sweep0.initial_state_props(4)])
  show ?thesis
    using sweep0.DFS_dircycle_linear_sound[folded sweep_initial_state_def]
    using sweep0.DFS_dircycle_linear_complete[folded sweep_initial_state_def]
    by (auto simp: dl_acyclic_dfs_def dep_adjmap_def impl a_graph_digraph_abs)
qed

theorem dl_acyclic_dfs_eq_code: "dl_acyclic_dfs c = dl_acyclic_dfs_code c"
  by (simp add: dl_acyclic_dfs_iff dl_acyclic_dfs_code_iff)

text \<open>So the reference check's \<^emph>\<open>code\<close> equation can simply be re-pointed at the refined sweep.
  Nothing downstream changes name or meaning: \<^const>\<open>dl_admissible_dfs\<close>,
  \<^const>\<open>dl_certified_model_dfs\<close> and their soundness theorems are those of
  \<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS\<close>, and they now \<^emph>\<open>evaluate\<close> through the refined sweep.\<close>

declare [[code drop: dl_acyclic_dfs]]
lemmas dl_acyclic_dfs_refined [code] = dl_acyclic_dfs_eq_code

subsection \<open>Example: the running edge/path certificate\<close>

text \<open>The two smoke checks of \<^theory>\<open>Datalog_Graph.Datalog_Cycle_DFS\<close>, run through the refined
  sweep: the edge/path support graph is a DAG (\<open>True\<close>), the mutually supporting \<open>p(1)\<close>/\<open>q(1)\<close>
  certificate has a 2-cycle (\<open>False\<close>).\<close>

value "dl_acyclic_dfs_code ex_cert"
value "dl_acyclic_dfs_code cyc_cert"

text \<open>And the same through the re-pointed reference check.\<close>

value "dl_acyclic_dfs ex_cert"
value "dl_acyclic_dfs cyc_cert"

end

