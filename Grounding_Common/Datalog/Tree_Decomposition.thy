theory Tree_Decomposition
  imports Main "HOL-Library.Multiset"
begin

text \<open>Generic, PDDL-free tree-decomposition certificate for Variant 2 (split+project) of the
  tree-decomposition grounder. A clause's join is over a list of atoms, each identified by its index
  and carrying a variable list. An (untrusted) decomposer emits a \<open>'v td_node\<close> tree; the
  in-kernel \<open>valid_decomp\<close> checker re-validates it so the projected split-join can be trusted to
  compute the same set of head-variable bindings as the flat join. The soundness bridge
  (\<open>valid_decomp \<Longrightarrow> projected-join image = flat-join image, restricted to the target vars\<close>) is the
  Yannakakis obligation proven against the join theories that consume this checker.\<close>

datatype 'v td_node =
  TDNode (bag: "'v list") (node_atoms: "nat list") (children: "'v td_node list")

text \<open>All atom indices assigned across the tree (each atom should appear exactly once).\<close>
fun td_atom_ids :: "'v td_node \<Rightarrow> nat list" where
  "td_atom_ids (TDNode b as cs) = as @ concat (map td_atom_ids cs)"

text \<open>All variables occurring in any bag at or below a node.\<close>
fun td_subtree_vars :: "'v td_node \<Rightarrow> 'v set" where
  "td_subtree_vars (TDNode b as cs) = set b \<union> (\<Union>c\<in>set cs. td_subtree_vars c)"

lemma td_subtree_vars_child:
  "c \<in> set cs \<Longrightarrow> td_subtree_vars c \<subseteq> td_subtree_vars (TDNode b as cs)"
  by auto

text \<open>Local coverage: every atom assigned to a node has all its variables inside that node's bag.\<close>
fun local_cover :: "(nat \<Rightarrow> 'v list) \<Rightarrow> 'v td_node \<Rightarrow> bool" where
  "local_cover avars (TDNode b as cs) =
     (list_all (\<lambda>i. set (avars i) \<subseteq> set b) as \<and> list_all (local_cover avars) cs)"

text \<open>Running-intersection / connectedness, checked top-down carrying the set of variables that occur
  strictly \<^emph>\<open>outside\<close> the current subtree (ancestor bags, the target, and sibling subtrees). Any such
  variable that also occurs inside this subtree must sit in this node's bag, so a variable projected
  away below the node can never be re-constrained above it --- the property that licenses early
  projection.\<close>
fun ri_ok :: "'v set \<Rightarrow> 'v td_node \<Rightarrow> bool" where
  "ri_ok outside (TDNode b as cs) =
     (td_subtree_vars (TDNode b as cs) \<inter> outside \<subseteq> set b
      \<and> list_all (\<lambda>c. ri_ok (outside \<union> set b
                             \<union> (\<Union>c'\<in>set cs. td_subtree_vars c') - td_subtree_vars c) c) cs)"

text \<open>The full validity check for a decomposition of \<open>n\<close> atoms with variable lists \<open>avars\<close> and
  projection target \<open>target\<close> (the head/param variables the flat join must get right).\<close>
definition valid_decomp :: "'v list \<Rightarrow> (nat \<Rightarrow> 'v list) \<Rightarrow> nat \<Rightarrow> 'v td_node \<Rightarrow> bool" where
  "valid_decomp target avars n td \<longleftrightarrow>
     mset (td_atom_ids td) = mset [0..<n]        \<comment> \<open>each atom placed in exactly one node\<close>
   \<and> local_cover avars td                        \<comment> \<open>each atom's vars covered by its node's bag\<close>
   \<and> set target \<subseteq> set (bag td)                  \<comment> \<open>root bag covers the projection target\<close>
   \<and> ri_ok (set target) td                       \<comment> \<open>running intersection w.r.t. the target as the root's outside\<close>"

text \<open>Executability sanity: the checker is a plain boolean over list/set operations (all the sets arise
  from finite lists), so it code-generates.\<close>
lemma valid_decomp_code:
  "valid_decomp target avars n td \<longleftrightarrow>
     mset (td_atom_ids td) = mset [0..<n]
   \<and> local_cover avars td
   \<and> set target \<subseteq> set (bag td)
   \<and> ri_ok (set target) td"
  by (simp add: valid_decomp_def)

text \<open>The trivial single-bag decomposition --- one node holding every atom, its bag the union of all
  atom variables and the target --- is always valid. It induces no projection (bag = everything), so
  the projected split-join degenerates to the flat join; this is the safe fallback when a nontrivial
  decomposition is rejected.\<close>
definition trivial_decomp :: "'v list \<Rightarrow> (nat \<Rightarrow> 'v list) \<Rightarrow> nat \<Rightarrow> 'v td_node" where
  "trivial_decomp target avars n =
     TDNode (remdups (target @ concat (map avars [0..<n]))) [0..<n] []"

lemma td_atom_ids_trivial: "td_atom_ids (trivial_decomp target avars n) = [0..<n]"
  by (simp add: trivial_decomp_def)

lemma ri_ok_trivial: "ri_ok (set target) (trivial_decomp target avars n)"
  by (simp add: trivial_decomp_def)

text \<open>DEFERRED (sprint debt): \<open>local_cover_trivial\<close> and hence \<open>valid_trivial_decomp\<close>
  (@{term "valid_decomp target avars n (trivial_decomp target avars n)"}) --- the single-bag fallback is
  valid. The atom-coverage conjunct reduces to
  \<^prop>\<open>\<forall>i\<in>set [0..<n]. set (avars i) \<subseteq> set (remdups (target @ concat (map avars [0..<n])))\<close>,
  which is true by @{thm set_concat}, but the surrounding \<open>list_all\<close>/\<open>Ball\<close> bridge fights this session's
  simp set; left for the return pass. Not load-bearing for the datatype/checker scaffolding below.\<close>

end
