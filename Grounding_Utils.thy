theory Grounding_Utils
  imports Main
begin

(* for testing and debugging *)
definition "showvals f xs \<equiv> map (\<lambda>x. (x, f x)) xs"

fun showsteps :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list" where
  "showsteps f i [] = [i]" |
  "showsteps f i (x # xs) = i # showsteps f (f i x) xs"

(* syntax sugar *)

text \<open> Not using the default list_all because it makes proofs cumbersome \<close>
abbreviation (input) list_all1 where
  "list_all1 P xs \<equiv> \<forall>x \<in> set xs. P x"

(* rule rewriting *)
lemma conj_split_3:
  assumes "A \<and> B \<and> C"
  shows "A" "B" "C"
  using assms by simp_all

lemma conj_split_4:
  assumes "A \<and> B \<and> C \<and> D"
  shows "A" "B" "C" "D"
  using assms by simp_all

lemma conj_split_5:
  assumes "A \<and> B \<and> C \<and> D \<and> E"
  shows "A" "B" "C" "D" "E"
  using assms by simp_all

lemma conj_split_6:
  assumes "A \<and> B \<and> C \<and> D \<and> E \<and> F"
  shows "A" "B" "C" "D" "E" "F"
  using assms by simp_all

lemma conj_split_7:
  assumes "A \<and> B \<and> C \<and> D \<and> E \<and> F \<and> G"
  shows "A" "B" "C" "D" "E" "F" "G"
  using assms by simp_all

(* proof rules *)

lemma eq_contr: "(a = b \<Longrightarrow> False) \<Longrightarrow> a \<noteq> b"
  by auto

(* lists *)

fun find_index :: "'a \<Rightarrow> 'a list \<rightharpoonup> nat" where
  "find_index a [] = None" |
  "find_index a (x # xs) = (if a = x then Some 0
      else map_option Suc (find_index a xs))"

(* Saves a a line or two sometimes *)
lemma list_induct_n [consumes 1, case_names Nil Suc]:
  assumes "length xs = n" "P [] 0"
  "\<And>x xs n. length xs = n \<Longrightarrow>
  P xs n \<Longrightarrow> P (x # xs) (Suc n)" shows "P xs n"
using assms proof (induction xs arbitrary: n)
  case (Cons x xs)
  thus ?case by (cases n) simp_all
qed simp

lemma in_set_zip_flip: "length as = length bs \<Longrightarrow> (a, b) \<in> set (zip as bs) \<longleftrightarrow> (b, a) \<in> set (zip bs as)"
  unfolding in_set_conv_nth by fastforce+

(* utility function: sublist_until *)
fun sublist_until :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "sublist_until [] a = []" |
  "sublist_until (x # xs) a =
    (if x = a then [] else x # sublist_until xs a)"

lemma sublist_just_until:
  assumes "x \<in> set xs"
  shows "\<exists>ys. sublist_until xs x @ [x] @ ys = xs"
  using assms by (induction xs) auto

lemma notin_sublist_until:
  "x \<notin> set (sublist_until xs x)"
  by (induction xs) simp_all


(* bringing a list element to the front *)
definition to_front :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "to_front xs i = (xs ! i) # (take i xs @ drop (i + 1) xs)"

(* map *)

lemma map_inj_distinct:
  assumes "distinct xs" "inj f"
  shows "distinct (map f xs)"
  using assms distinct_map inj_on_subset by blast

lemma map_set_comprehension:
  "{f (xs ! i) | i. i < length xs} = set (map f xs)"
proof -
  have "{f (xs ! i) | i. i < length xs} = {f x | x. x \<in> set xs}"
    by (metis in_set_conv_nth)
  thus ?thesis by auto
qed

lemma append_r_distinct: "distinct xs \<Longrightarrow> distinct (map (\<lambda>x. x @ p) xs)" (is "?L \<Longrightarrow> ?R")
proof - (* TODO how to apply contradiction correctly here? *)
  assume l: ?L
  {assume "\<not>?R"
    then obtain i j where
      ij: "i < length xs" "j < length xs" "i \<noteq> j"
      "map (\<lambda>x. x @ p) xs ! i = map (\<lambda>x. x @ p) xs ! j"
      by (metis distinct_conv_nth length_map)
    hence "xs ! i = xs ! j" by simp
    hence "\<not>?L" using ij distinct_conv_nth by blast}
  thus ?thesis using l by auto
qed

lemma append_l_distinct: "distinct xs \<Longrightarrow> distinct (map ((@)p) xs)" (is "?L \<Longrightarrow> ?R")
proof - (* TODO how to apply contradiction correctly here? *)
  assume l: ?L
  {assume "\<not>?R"
    then obtain i j where
      ij: "i < length xs" "j < length xs" "i \<noteq> j"
      "map ((@)p) xs ! i = map ((@)p) xs ! j"
      by (metis distinct_conv_nth length_map)
    hence "xs ! i = xs ! j" by simp    
    hence "\<not>?L" using ij distinct_conv_nth by blast}
  thus ?thesis using l by auto
qed

(* map2 *)

lemma map2_obtain:
  assumes "z \<in> set (map2 f xs ys)"
  obtains x y where "z = f x y" "(x, y) \<in> set (zip xs ys)" "x \<in> set xs" "y \<in> set ys" 
  using assms by (induction xs ys rule: list_induct2') auto

(* TODO, if I end up using it *)
lemma map2_dist_2:
  assumes "distinct ys" "\<And>x1 x2 y1 y2. y1 \<in> set ys \<Longrightarrow> y2 \<in> set ys \<Longrightarrow> y1 \<noteq> y2 \<Longrightarrow> f x1 y1 \<noteq> f x2 y2"
  shows "distinct (map2 f xs ys)"
  using assms proof (induction xs ys rule: list_induct2')
  case (4 x xs y ys)
  hence "distinct (map2 f xs ys)" by simp

  thus ?case apply (induction xs ys rule: list_induct2') oops

lemma drop_prefix:
  assumes "length xs = n" shows "drop n (xs @ ys) = ys"
using assms proof (induction rule: list_induct_n)
  case (Suc x xs n) (* explicit just to learn how to use case_names *)
  then show ?case by simp
qed simp

(* map_of *)

lemma map_of_in_L_iff: "x \<in> fst ` set m \<longleftrightarrow> (\<exists>y. map_of m x = Some y)"
  by (metis map_of_eq_None_iff not_None_eq)

lemma map_of_single_val:
  assumes "\<forall>(x, y) \<in> set m. y = z"
  shows "x \<in> fst ` set m \<longleftrightarrow> map_of m x = Some z"
  using assms map_of_in_L_iff
  by (metis (full_types) case_prodD map_of_SomeD)

lemma lookup_zip: "length xs = length ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y. map_of (zip xs ys) x = Some y \<and> y \<in> set ys"
  by (induction xs ys rule: list_induct2) auto

lemma mapof_distinct_zip_neq:
  assumes "length xs = length ys" "distinct ys" "a \<in> set xs" "b \<in> set xs" "a \<noteq> b"
  shows "the (map_of (zip xs ys) a) \<noteq> the (map_of (zip xs ys) b)"
proof -
  from assms obtain y where y: "(a, y) \<in> set (zip xs ys)" "map_of (zip xs ys) a = Some y"
    by (meson lookup_zip map_of_SomeD)
  from assms obtain z where z: "(b, z) \<in> set (zip xs ys)" "map_of (zip xs ys) b = Some z"
    by (meson lookup_zip map_of_SomeD)
  from y assms(1) obtain i where i: "i < length xs" "xs ! i = a" "ys ! i = y"
    by (metis fst_eqD in_set_zip sndI)
  from z assms(1) obtain j where j: "j < length xs" "xs ! j = b" "ys ! j = z"
    by (metis fst_eqD in_set_zip sndI)

  from y z i j assms show ?thesis using nth_eq_iff_index_eq by auto
qed

(* the second statement is weaker but follows from the first and assms in a complex way *)
lemma mapof_zip_inj:
  assumes "length xs = length ys" "distinct ys"
  shows "inj_on (the \<circ> map_of (zip xs ys)) (set xs)" "inj_on (map_of (zip xs ys)) (set xs)"
  using assms inj_on_def mapof_distinct_zip_neq by fastforce+

lemma mapof_distinct_zip_distinct:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "distinct as" "set as \<subseteq> set xs"
  shows "distinct (map (the \<circ> map_of (zip xs ys)) as)"
  using assms mapof_zip_inj(1)
  using distinct_map inj_on_subset by blast

(* misc *)
(* Set arithmetic lemma, useful for effect application.
  TODO check where this may be needed elsewhere in normalization.
  Currently only employed in Grounded_PDDL *)
lemma (in -) set_image_minus_un:
  assumes "inj_on f (A \<union> B \<union> C \<union> D)"
  shows "A - B \<union> C = D \<longleftrightarrow> f ` (A - B \<union> C) = f ` D"
    "A - B \<union> C = D \<longleftrightarrow> f ` A - f ` B \<union> f ` C = f ` D"
  using assms unfolding inj_on_def by blast+

(* Concatenate two lists at once *)
fun (in -) concat2 :: "('a list \<times> 'b list) list \<Rightarrow> ('a list \<times> 'b list)" where
  "concat2 xs = (concat (map fst xs), concat (map snd xs))"


end