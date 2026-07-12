theory PDDL_Orderings
  imports Classical_PDDL_Normalization
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

end
