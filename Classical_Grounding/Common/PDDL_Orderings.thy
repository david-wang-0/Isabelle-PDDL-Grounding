theory PDDL_Orderings
  imports Classical_PDDL_Normalization "HOL-Library.List_Lexorder"
begin

text \<open>Shared linear orders on the PDDL base types, factored out of the executable pipeline so both
  the RBT certificate index (\<open>dl_closure_check_exec_fast\<close>) and the classical action grounder can key
  red-black trees on them. Each type wraps a \<^typ>\<open>String.literal\<close> (\<open>name\<close>), already a
  \<^class>\<open>linorder\<close> in the distribution, so we lift that order through the single constructor. Plain
  \<^class>\<open>linorder\<close> instances (no Containers/\<open>ceq\<close>/\<open>ccompare\<close>), keeping the datalog layer
  Collections-free.\<close>

instantiation predicate :: linorder
begin

definition less_eq_predicate :: "predicate \<Rightarrow> predicate \<Rightarrow> bool" where
  "less_eq_predicate p q \<longleftrightarrow> predicate.name p \<le> predicate.name q"

definition less_predicate :: "predicate \<Rightarrow> predicate \<Rightarrow> bool" where
  "less_predicate p q \<longleftrightarrow> predicate.name p < predicate.name q"

instance
proof
  fix x y z :: predicate
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_eq_predicate_def less_predicate_def less_le_not_le)
  show "x \<le> x" by (simp add: less_eq_predicate_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (auto simp: less_eq_predicate_def intro: order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp: less_eq_predicate_def predicate.expand)
  show "x \<le> y \<or> y \<le> x"
    by (auto simp: less_eq_predicate_def)
qed

end

instantiation object :: linorder
begin

definition less_eq_object :: "object \<Rightarrow> object \<Rightarrow> bool" where
  "less_eq_object p q \<longleftrightarrow> object.name p \<le> object.name q"

definition less_object :: "object \<Rightarrow> object \<Rightarrow> bool" where
  "less_object p q \<longleftrightarrow> object.name p < object.name q"

instance
proof
  fix x y z :: object
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_eq_object_def less_object_def less_le_not_le)
  show "x \<le> x" by (simp add: less_eq_object_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (auto simp: less_eq_object_def intro: order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp: less_eq_object_def object.expand)
  show "x \<le> y \<or> y \<le> x"
    by (auto simp: less_eq_object_def)
qed

end

text \<open>A linear order on ground actions \<^type>\<open>ast_classical_plan_action\<close>, used to canonicalise the
  ground-op / fact lists so the executable (index-reordered) grounder produces a problem equal to the
  abstract \<open>P\<^sub>G_cert\<close>. Single constructor \<^const>\<open>SimplePlanAction\<close>, so we order lexicographically on
  \<open>(name, arguments)\<close> via the existing \<^type>\<open>String.literal\<close> and list-lexicographic orders.\<close>

instantiation ast_classical_plan_action :: linorder
begin

definition less_eq_ast_classical_plan_action ::
    "ast_classical_plan_action \<Rightarrow> ast_classical_plan_action \<Rightarrow> bool" where
  "less_eq_ast_classical_plan_action a b \<longleftrightarrow>
     (case a of SimplePlanAction na aa \<Rightarrow> case b of SimplePlanAction nb ab \<Rightarrow>
        na < nb \<or> (na = nb \<and> aa \<le> ab))"

definition less_ast_classical_plan_action ::
    "ast_classical_plan_action \<Rightarrow> ast_classical_plan_action \<Rightarrow> bool" where
  "less_ast_classical_plan_action a b \<longleftrightarrow>
     (case a of SimplePlanAction na aa \<Rightarrow> case b of SimplePlanAction nb ab \<Rightarrow>
        na < nb \<or> (na = nb \<and> aa < ab))"

instance
proof
  fix x y z :: ast_classical_plan_action
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y)
       (auto simp: less_eq_ast_classical_plan_action_def less_ast_classical_plan_action_def
                   less_le_not_le)
  show "x \<le> x" by (cases x) (auto simp: less_eq_ast_classical_plan_action_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z)
       (auto simp: less_eq_ast_classical_plan_action_def dest: order_trans less_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) (auto simp: less_eq_ast_classical_plan_action_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (auto simp: less_eq_ast_classical_plan_action_def)
qed

end

text \<open>Canonical form of a list up to its element set: the sorted, duplicate-free list. Because it
  depends only on \<^term>\<open>set xs\<close>, two set-equal lists (e.g. the abstract fact-driven join and the
  index-reordered executable join) canonicalise to the \<^emph>\<open>same\<close> list, which is what keeps
  \<open>ground_by_cert = P\<^sub>G_cert\<close> a strict equality.\<close>

definition canon :: "'a::linorder list \<Rightarrow> 'a list" where
  "canon xs = sorted_list_of_set (set xs)"

lemma canon_set [simp]: "set (canon xs) = set xs"
  by (simp add: canon_def)

lemma canon_cong: "set xs = set ys \<Longrightarrow> canon xs = canon ys"
  by (simp add: canon_def)

lemma canon_distinct [simp]: "distinct (canon xs)"
  by (simp add: canon_def)

lemma canon_sorted: "sorted (canon xs)"
  by (simp add: canon_def)

end
