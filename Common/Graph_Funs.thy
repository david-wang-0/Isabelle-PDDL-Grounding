theory Graph_Funs
imports Main "HOL-Library.Monad_Syntax" "HOL-Library.Sublist"
begin

subsection \<open> Enumerating the transitive closure \<close>

(* alternatively, use remdups on each bag at the end *)
text \<open> the use of conc_unique here is only for performance issues.\<close>
fun conc_unique :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "conc_unique [] rs = rs" |
  "conc_unique (l # ls) rs = conc_unique ls (if l \<in> set rs then rs else l # rs)"

definition upd_bag :: "'a list \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 'a list)" where
  "upd_bag values key rel \<equiv> rel(key := conc_unique values (rel key))"

definition upd_all where
  "upd_all rel keys values \<equiv> fold (upd_bag values) keys rel"
(*foldr is easier to prove by induction *)

fun reach_aux :: "('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list))" where
  "reach_aux [] R L = L" |
  "reach_aux ((l, r) # rest) R L = 
    (let l_rs = R l; r_ls = L r in
    reach_aux rest
      (upd_all R r_ls l_rs)
      (upd_all L l_rs r_ls))"

(* only used in proofs *)
fun reach_aux_aux :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list))" where
  "reach_aux_aux [] done R L = L" |
  "reach_aux_aux ((l, r) # todo) done R L = 
    (let l_rs = R l; r_ls = L r in
    reach_aux_aux todo ((l, r) # done)
      (upd_all R r_ls l_rs)
      (upd_all L l_rs r_ls))"

text \<open> TODO: use mapping instead of lambda! \<close>
abbreviation reachable_nodes :: "('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "reachable_nodes rel \<equiv> reach_aux rel (\<lambda>x. [x]) (\<lambda>x. [x])"

(* ---------------- PROOFS ------------------- *)

lemma conc_unique_un:
  "set (conc_unique xs ys) = set xs \<union> set ys"
  apply (induction xs arbitrary: ys)
  by auto

definition describes_rel :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "describes_rel rel bags \<equiv> \<forall>x y. y \<in> set (bags x) \<longleftrightarrow> (x, y) \<in> rel"
declare describes_rel_def[simp]

lemma desc_rel_alt: "describes_rel rel bags \<longleftrightarrow> (\<forall>x. set (bags x) = {y. (x, y) \<in> rel})"
  by auto

lemma upd_bag_aux:
  assumes "set u = vs \<union> set (f x)"
    "describes_rel r f"
  shows "describes_rel (r \<union> (Pair x) ` vs) (f(x:=u))"
  using assms by auto

lemma upd_bag_correct:
  "describes_rel r f \<Longrightarrow> describes_rel (r \<union> (Pair x) ` set vals) (upd_bag vals x f)"
  using conc_unique_un upd_bag_aux upd_bag_def by metis

(* TODO *)
lemma upd_all_correct:
  assumes "describes_rel r f"
  shows "describes_rel (r \<union> {(k, v). k \<in> set ks \<and> v \<in> set vs}) (upd_all f ks vs)"
  using assms
proof (induction ks rule: rev_induct)
  case Nil
  thus ?case unfolding upd_all_def by simp
next
  case snoc
  note snoc.IH[OF snoc.prems]
  note upd_bag_correct[OF this]
  thus ?case unfolding upd_all_def by auto
qed

(* TODO use this *)
lemma "foldr f xs i = fold f (rev xs) i"
  by (metis foldr_conv_fold)

lemma rtrancl_insert_elem: "(a, b) \<in> (insert (c, d) rel)\<^sup>* \<longleftrightarrow>
        (a, b) \<in> rel\<^sup>* \<or> ((a, c) \<in> rel\<^sup>* \<and> (d, b) \<in> rel\<^sup>*)"
  using rtrancl_insert (* by fast: 4 seconds *)
proof -
  have "(a, b) \<in> (insert (c, d) rel)\<^sup>* \<longleftrightarrow>
    (a, b) \<in> rel\<^sup>* \<union> {(x, y). (x, c) \<in> rel\<^sup>* \<and> (d, y) \<in> rel\<^sup>*}"
    using rtrancl_insert by metis
  thus ?thesis by simp
qed

lemma upd_all_L:
  assumes "describes_rel (rel\<^sup>*) L"
          "describes_rel ((rel\<^sup>*)\<inverse>) R"
  shows "describes_rel ((insert (l, r) rel)\<^sup>*) (upd_all L (R l) (L r))"
proof -
  let ?B = "upd_all L (R l) (L r)"
  have "describes_rel (rel\<^sup>* \<union> {(k, v). k \<in> set (R l) \<and> v \<in> set (L r)}) ?B"
    using upd_all_correct[OF assms(1)] .
  hence "describes_rel (rel\<^sup>* \<union> {(k, v). (l, k) \<in> (rel\<^sup>*)\<inverse> \<and> (r, v) \<in> rel\<^sup>*}) ?B"
    using assms by simp
  hence "describes_rel (rel\<^sup>* \<union> {(k, v). (k, l) \<in> rel\<^sup>* \<and> (r, v) \<in> rel\<^sup>*}) ?B" by simp
  thus ?thesis using assms rtrancl_insert by metis
qed

lemma upd_all_R:
  assumes "describes_rel (rel\<^sup>*) L"
          "describes_rel ((rel\<^sup>*)\<inverse>) R"
        shows "describes_rel (((insert (l, r) rel)\<^sup>*)\<inverse>) (upd_all R (L r) (R l))"
proof -
  from assms(2) have 1: "describes_rel ((rel\<inverse>)\<^sup>*) R" by (simp add: rtrancl_converse)
  from assms(1) have 2: "describes_rel (((rel\<inverse>)\<^sup>*)\<inverse>) L" by (simp add: rtrancl_converse)
  have 3: "describes_rel ((insert (r, l) (rel\<inverse>))\<^sup>*) (upd_all R (L r) (R l))"
    by (rule upd_all_L[OF 1 2])
  have "(insert (l, r) rel)\<inverse> = insert (r, l) (rel\<inverse>)" by auto
  moreover have   "((insert (l, r) rel)\<^sup>*)\<inverse> = ((insert (l, r) rel)\<inverse>)\<^sup>*" by (simp add: rtrancl_converse)
  ultimately have "((insert (l, r) rel)\<^sup>*)\<inverse> = (insert (r, l) (rel\<inverse>))\<^sup>*" by simp
  from 3 this show ?thesis by simp
qed

lemma reach_aux_aux: "reach_aux rel R L = reach_aux_aux rel dones R L"
  apply (induction rel arbitrary: dones R L)
  by auto

lemma reach_aux_aux_correct:
  assumes "describes_rel ((set dones)\<^sup>*) L"
          "describes_rel (((set dones)\<^sup>*)\<inverse>) R"
  shows "describes_rel ((set todo \<union> set dones)\<^sup>*) (reach_aux_aux todo dones R L)"
  using assms
proof (induction todo arbitrary: dones L R)
  case (Cons t todo)
  let ?rel = "set dones"
  obtain l r where lr: "t = (l, r)" by fastforce
  note reach_aux_aux.simps(2)[unfolded Let_def] (* TODO how to have simp deal with "let" again? *)
  hence aux_it: "reach_aux_aux ((l, r) # todo) dones R L =
    reach_aux_aux todo ((l, r) # dones)
      (upd_all R (L r) (R l))
      (upd_all L (R l) (L r))" by simp
  
  have L: "describes_rel ((set ((l, r) # dones))\<^sup>*) (upd_all L (R l) (L r))"
    using assms Cons.prems upd_all_L by simp
  have R: "describes_rel (((set ((l, r) # dones))\<^sup>*)\<inverse>) (upd_all R (L r) (R l))"
    using assms Cons.prems upd_all_R by simp
  from L R have "describes_rel ((set todo \<union> set ((l, r) # dones))\<^sup>*)
   (reach_aux_aux todo ((l, r) # dones) (upd_all R (L r) (R l)) (upd_all L (R l) (L r)))"
    by (rule Cons.IH)
  hence "describes_rel ((set (t # todo) \<union> set dones)\<^sup>*)
    (reach_aux_aux (t # todo) dones R L)" using aux_it lr by simp
  thus ?case .
qed simp

lemma reach_aux_aux_usage:
  shows "describes_rel ((set rel)\<^sup>*) (reach_aux_aux rel [] (\<lambda>x. [x]) (\<lambda>x. [x]))"
proof -
  have 1: "describes_rel ((set [])\<^sup>*) (\<lambda>x. [x])" by auto
  moreover have 2: "describes_rel (((set [])\<^sup>*)\<inverse>) (\<lambda>x. [x])" by auto
  moreover note reach_aux_aux_correct[OF 1 2]
  ultimately show ?thesis by simp
qed

declare describes_rel_def[simp del]

(* \<longleftrightarrow> "describes_rel ((set rel)\<^sup>* ) (reachable_nodes rel)" *)
theorem reachable_iff_in_star: "y \<in> set (reachable_nodes rel x) \<longleftrightarrow> (x, y) \<in> (set rel)\<^sup>*"
  using reach_aux_aux_usage reach_aux_aux describes_rel_def
  by metis

lemma reachable_set: "set (reachable_nodes rel x) \<subseteq> insert x (snd ` set rel)"
proof -
  have "set (reachable_nodes rel x) = {y. (x, y) \<in> (set rel)\<^sup>*}"
    using reachable_iff_in_star by fast
  also have "... = (set rel)\<^sup>* `` {x}" by auto
  also have "... = insert x ((set rel)\<^sup>+ `` {x})" using rtrancl_trancl_reflcl by blast
  also have "... \<subseteq> insert x (snd ` (set rel)\<^sup>+)" by force
  also have "... = insert x (snd ` set rel)" by (metis trancl_range snd_eq_Range)
  finally show ?thesis .
qed

lemma conc_unique_dist:
  assumes "distinct ys"
  shows "distinct (conc_unique xs ys)"
  using assms by (induction xs arbitrary: ys) auto

lemma upd_bag_dist:
  assumes "distinct (rel x)"
  shows "distinct ((upd_bag values key rel) x)"
  using assms conc_unique_dist unfolding upd_bag_def by auto

lemma upd_bags_dist:
  assumes "distinct (rel x)"
  shows "distinct ((upd_all rel keys values) x)"
  unfolding upd_all_def
  using assms apply (induction keys rule: rev_induct)
  apply simp using upd_bag_dist by force

lemma reach_aux_dist:
  assumes "distinct (L x)"
  shows "distinct ((reach_aux rel R L) x)"
  using assms apply (induction rel R L rule: reach_aux.induct)
  apply simp unfolding reach_aux.simps Let_def using upd_bags_dist by fast

lemma reachable_dis: "distinct (reachable_nodes rel x)"
  using reach_aux_dist[of "\<lambda>x. [x]"] by fastforce

subsection \<open> All combinations, i.e. cartesian powers \<close>

text \<open> All valid combinations of lists of elements that satisfy a given property.
  This function is designed to enumerate them, without keeping all of them in memory
  at once.\<close>

text \<open>There are n (length vals) slots, each with a list of possible values (vals[i]).
  A testing function (f) takes in a list of length n and checks whether the
  combination is valid.\<close>

fun nxt :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list option" where
  "nxt [] [] = None" |
  "nxt (vs # vss) [] = None" | (*values and curr need same length. may as well be undefined, but termination is harder to prove*)
  "nxt [] (cs # css) = None" | (*values and curr need same length*)
  "nxt (vs # vss) ([] # css) = None" | (* all lists in curr are non-empty*)
  "nxt (vs # vss) ([c] # css) = do {nxs \<leftarrow> nxt vss css; Some (vs # nxs)}" |
  "nxt (vs # vss) ((c#cs) # css) = Some (cs # css)"

function (sequential) all_combos_aux :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "all_combos_aux f vals crr accum = 
    (let look = map hd crr;
         acc' = (if f look then look # accum else accum) in
    case nxt vals crr of None \<Rightarrow> acc' |
         Some nxs \<Rightarrow> all_combos_aux f vals nxs acc')"
  by pat_completeness simp

definition all_combos :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "all_combos f vals \<equiv> if [] \<in> set vals then [] else all_combos_aux f vals vals []"




(* --------------------- PROOFS ------------------------ *)

text \<open> termination of all_combos_aux, and induction for nxt \<close>

fun nxt_runs :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> nat" where
  "nxt_runs [] [] = 0" |
  "nxt_runs (v # va) [] = 0" | (* illegal *)
  "nxt_runs [] (v # va) = 0" | (* illegal *)
  "nxt_runs (vs # vss) (cs # css) = (length cs) + (length vs) * nxt_runs vss css"
  (* technically, "... = length cs - 1 + length vs * nxt_runs vss css" is enough,
     and it would model the number of next values. But that only works if "vs \<noteq> [], cs \<noteq> []".
     If you need a theorem that describes the exact number of next values in a sequence,
     you'll have to create special cases for [] (or assume valid input). *)

lemma nxt_termination:
  assumes "nxt vss css = Some nxs"
  shows "nxt_runs vss nxs < nxt_runs vss css"
using assms proof (induction vss css arbitrary: nxs rule: nxt.induct)
  case (5 vs vss c css)
  then obtain nx where nx: "nxt vss css = Some nx" by fastforce
  with 5 have lt: "nxt_runs vss nx < nxt_runs vss css" and
    nxs: "nxs = vs # nx" by simp_all
  from lt have gt0: "nxt_runs vss css > 0" by simp

  from nxs have "nxt_runs (vs # vss) nxs = nxt_runs (vs # vss) (vs # nx)" by blast
  also have "... = length vs + length vs * nxt_runs vss nx" by simp
  also have "... \<le> length vs + length vs * (nxt_runs vss css - 1)" using lt by auto
  also have "... = length vs * nxt_runs vss css"
    using gt0 by (metis Suc_diff_1 mult_Suc_right)
  also have "... < length [c] + length vs * nxt_runs vss css" by simp
  also have "... = nxt_runs (vs # vss) ([c] # css)" by simp
  finally show ?case .
qed auto

text \<open> Using wf_induct to create a more palatable induction rule for nxt.
  If using wf_induct directly, you'd equivalently have the following cumbersome induction step:
  "\<And>vals crr. (\<And>nxs. nxt_runs vals nxs < nxt_runs vals crr \<Longrightarrow> P vals nxs) \<Longrightarrow> P vals crr"\<close>
lemma nxt_induct [case_names Last Step]:
  assumes "\<And>vals crr. nxt vals crr = None \<Longrightarrow> P vals crr"
    "\<And>vals crr nxs. nxt vals crr = Some nxs \<Longrightarrow> P vals nxs \<Longrightarrow> P vals crr"
  shows "P vals crr"
proof -
  let ?m = "measure (case_prod nxt_runs)"
  have wf: "wf ?m" by simp

  have "(\<And>nxs. nxt_runs vals nxs < nxt_runs vals crr \<Longrightarrow> P vals nxs) \<Longrightarrow> P vals crr"
    for vals crr
    using assms nxt_termination by (cases "nxt vals crr") blast+
  hence "\<And>x. (\<forall>y. (y, x) \<in> ?m \<longrightarrow> (case_prod P) y) \<Longrightarrow> (case_prod P) x"
    by fastforce
  with wf have "\<And>x. (case_prod P) x" using wf_induct[of _ "case_prod P"] by blast
  thus ?thesis by blast
qed

termination all_combos_aux proof
  let ?m = "measure (\<lambda>(f, vals, crr, accum). nxt_runs vals crr)"
  show "wf ?m" by simp

  fix f vals crr accum
  fix nexto look acc' nxs
  assume "nxt vals crr = Some nxs"
  hence "nxt_runs vals nxs < nxt_runs vals crr"
    using nxt_termination by blast
  thus "((f, vals, nxs, acc'), (f, vals, crr, accum)) \<in> ?m"
    by simp
qed

lemma all_combos_aux_simps:
  "nxt vals crr = None \<Longrightarrow> all_combos_aux f vals crr accum =
    (if f (map hd crr) then map hd crr # accum else accum)"
  "nxt vals crr = Some nxs \<Longrightarrow> all_combos_aux f vals crr accum =
    all_combos_aux f vals nxs (if f (map hd crr) then map hd crr # accum else accum)"
   apply simp_all by metis+

declare all_combos_aux.simps[simp del]

lemma all_combos_accum:
  shows "all_combos_aux f vals crr (xs @ ys) = all_combos_aux f vals crr xs @ ys"
  apply (induction vals crr arbitrary: xs rule: nxt_induct)
  unfolding all_combos_aux_simps apply simp apply (cases "f (map hd crr)"; simp)
   apply (metis append_Cons)+
  done

abbreviation (input) accept ("\<checkmark>") where "accept \<equiv> \<lambda>_. True"
lemma accept_all_combos_simps:
  "nxt vals crr = None \<Longrightarrow> all_combos_aux \<checkmark> vals crr [] = [map hd crr]"
  "nxt vals crr = Some nxs \<Longrightarrow> all_combos_aux \<checkmark> vals crr [] =
    all_combos_aux \<checkmark> vals nxs [] @ [map hd crr]"
  using all_combos_aux_simps apply metis
  unfolding all_combos_accum[symmetric] using all_combos_aux_simps by fastforce

lemma all_combos_filters:
  shows "all_combos_aux f vals crr [] = filter f (all_combos_aux \<checkmark> vals crr [])"
proof (induction vals crr rule: nxt_induct)
  case (Step vals crr nxs)
  have "all_combos_aux f vals crr [] = (if f (map hd crr) then all_combos_aux f vals nxs ([] @ [map hd crr]) else
    all_combos_aux f vals nxs [])"
    using Step all_combos_aux_simps by fastforce
  also have "... = (if f (map hd crr) then all_combos_aux f vals nxs [] @ [map hd crr] else
    all_combos_aux f vals nxs [])"
    using all_combos_accum by metis
  also have "... = all_combos_aux f vals nxs [] @ (if f (map hd crr) then [map hd crr] else [])"
    by simp
  also have "... = filter f (all_combos_aux \<checkmark> vals nxs [] @ [map hd crr])"
    using Step by simp
  also have "... = filter f (all_combos_aux \<checkmark> vals crr [])"
    using Step accept_all_combos_simps by fastforce
  finally show ?case .
next
  case (Last vals crr)
  note all_combos_aux_simps(1)[OF Last(1)]
  thus ?case by simp
qed

abbreviation "valid_vals vals \<equiv> \<forall>v \<in> set vals. v \<noteq> Nil"
abbreviation "matches_range vs cs \<equiv> cs \<noteq> [] \<and> suffix cs vs"
fun valid_crr :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> bool" where
  "valid_crr [] [] = True" |
  "valid_crr _ [] = False" |
  "valid_crr [] _ = False" |
  "valid_crr (vs#vss) (cs#css) \<longleftrightarrow> cs \<noteq> [] \<and> suffix cs vs \<and> valid_crr vss css"

lemma valid_crr_listall2: "valid_crr vals crr \<longleftrightarrow> list_all2 matches_range vals crr"
  by (induction vals crr rule: valid_crr.induct) simp_all

lemma nxt_valid:
  assumes "valid_vals vals" "valid_crr vals crr" "nxt vals crr = Some nxs"
  shows "valid_crr vals nxs"
  using assms proof (induction vals crr arbitrary: nxs rule: nxt.induct)
  case (5 vs vss c css)
  then obtain nx where nx: "nxt vss css = Some nx" "valid_crr vss nx" by fastforce
  with 5 have "nxs = vs # nx" by auto
  with 5 nx show ?case by auto
next
  case 6 thus ?case using suffix_ConsD by force
qed simp_all

lemma valid_vals_crr: "valid_vals vals \<Longrightarrow> valid_crr vals vals"
  by (induction vals) simp_all

abbreviation "cart_prepend vs xss \<equiv> [v # xs. xs \<leftarrow> xss, v \<leftarrow> vs]"
  (* \<equiv> concat (map (\<lambda>xs. map (\<lambda>v. v # xs) vs) xss) *)
  (* xss outer, vs inner *)

lemma accept_all_combos_unroll_digit:
  assumes "nxt vals crr = Some nxs" "cs \<noteq> []"
  shows "all_combos_aux \<checkmark> (vs # vals) (cs # crr) [] =
    all_combos_aux \<checkmark> (vs # vals) (vs # nxs) [] @ [v # map hd crr. v \<leftarrow> rev cs]"
  using assms(2) proof (induction cs rule: induct_list012)
case (2 c)
  from assms(1) have "nxt (vs # vals) ([c] # crr) = Some (vs # nxs)" by simp
  note accept_all_combos_simps(2)[OF this]
  hence "all_combos_aux \<checkmark> (vs # vals) ([c] # crr) [] =
    all_combos_aux \<checkmark> (vs # vals) (vs # nxs) [] @ [map hd ([c] # crr)]" by simp
  also have "... = all_combos_aux \<checkmark> (vs # vals) (vs # nxs) []
    @ [v # map hd crr. v \<leftarrow> rev [c]]" by simp
  finally show ?case .
next
  case (3 d c cs)
  hence ih: "all_combos_aux \<checkmark> (vs # vals) ((c # cs) # crr) [] =
    all_combos_aux \<checkmark> (vs # vals) (vs # nxs) [] @
    [v # map hd crr. v \<leftarrow> rev (c # cs)]" by blast
  let ?cs = "d # c # cs"
  have "nxt (vs # vals) (?cs # crr) = Some ((c # cs) # crr)" by simp
  note accept_all_combos_simps(2)[OF this]
  hence "all_combos_aux \<checkmark> (vs # vals) (?cs # crr) [] =
    all_combos_aux \<checkmark> (vs # vals) (vs # nxs) [] @
    [v # map hd crr. v \<leftarrow> rev (c # cs)] @ [map hd (?cs # crr)]"
    unfolding ih by simp    
  also have "... =
     all_combos_aux \<checkmark> (vs # vals) (vs # nxs) [] @
     [v # map hd crr. v \<leftarrow> rev ?cs]" by simp
  finally show ?case .
qed simp

lemma accept_all_combos_unroll_digit':
  assumes "nxt vals crr = None" "cs \<noteq> []"
  shows "all_combos_aux \<checkmark> (vs # vals) (cs # crr) [] =
    [v # map hd crr. v \<leftarrow> rev cs]"
  using assms(2) proof (induction cs rule: induct_list012)
  case (2 c)
  from assms(1) have "nxt (vs # vals) ([c] # crr) = None" by simp
  note accept_all_combos_simps(1)[OF this]
  hence "all_combos_aux \<checkmark> (vs # vals) ([c] # crr) [] = [map hd ([c] # crr)]"
    by blast
  thus ?case by simp
next
  case (3 d c cs)
  hence ih: "all_combos_aux \<checkmark> (vs # vals) ((c # cs) # crr) [] =
    [v # map hd crr. v \<leftarrow> rev (c # cs)]" by blast
  let ?cs = "d # c # cs"
  have "nxt (vs # vals) (?cs # crr) = Some ((c # cs) # crr)" by simp
  note accept_all_combos_simps(2)[OF this]
  hence "all_combos_aux \<checkmark> (vs # vals) (?cs # crr) [] =
    [v # map hd crr. v \<leftarrow> rev (c # cs)] @ [map hd (?cs # crr)]"
    unfolding ih by simp    
  also have "... = [v # map hd crr. v \<leftarrow> rev ?cs]" by simp
  finally show ?case .
qed simp

lemma accept_all_combos_new_digit:
  assumes "valid_vals vals" "valid_crr vals crr" "vs \<noteq> []"
  shows "all_combos_aux \<checkmark> (vs # vals) (vs # crr) [] =
    cart_prepend (rev vs) (all_combos_aux \<checkmark> vals crr [])"
using assms proof (induction vals crr rule: nxt_induct)
  case (Last vals crr)
  have "all_combos_aux \<checkmark> (vs # vals) (vs # crr) [] = [v # map hd crr. v \<leftarrow> rev vs]"
    using accept_all_combos_unroll_digit' Last by blast
  also have "... = cart_prepend (rev vs) (all_combos_aux \<checkmark> vals crr [])"
    using accept_all_combos_simps(1)[OF Last(1)] by simp
  finally show ?case .
next
  case (Step vals crr nxs)
  have "all_combos_aux \<checkmark> (vs # vals) (vs # crr) [] =
    all_combos_aux \<checkmark> (vs # vals) (vs # nxs) [] @ [v # map hd crr. v \<leftarrow> rev vs]"
    using accept_all_combos_unroll_digit Step by blast
  also have "... = cart_prepend (rev vs) (all_combos_aux \<checkmark> vals nxs []) @
    [v # map hd crr. v \<leftarrow> rev vs]"
    using Step(2)[OF Step(3) nxt_valid[OF Step(3,4,1)] assms(3)]
    by blast
  also have "... = cart_prepend (rev vs) (all_combos_aux \<checkmark> vals nxs [] @ [map hd crr])"
    by simp
  also have "... = cart_prepend (rev vs) (all_combos_aux \<checkmark> vals crr [])"
    using accept_all_combos_simps(2)[OF Step(1)] by simp
  finally show ?case .
qed

fun chosen_from :: "'a list list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "chosen_from [] [] = True" |
  "chosen_from (vs#vss) [] = False" |
  "chosen_from [] (x#xs) = False" |
  "chosen_from (vs#vss) (x#xs) \<longleftrightarrow> x \<in> set vs \<and> chosen_from vss xs"

lemma nothing_to_choose:
  assumes "[] \<in> set vs"
  shows "\<not> chosen_from vs xs"
  using assms apply (induction vs arbitrary: xs)
   apply simp
  subgoal for v vs xs by (cases xs) auto
  done

lemma
  assumes "valid_crr vals crr"
  shows "chosen_from vals (map hd crr)"
  oops

lemma chosen_from_new_digit:
  assumes "set xs = {x. chosen_from vs x}"
  shows "set (cart_prepend ys xs) = {x. chosen_from (ys # vs) x}"
proof -
  have "chosen_from (ys # vs) z \<longleftrightarrow> (\<exists>k ks. z = k # ks \<and> k \<in> set ys \<and> chosen_from vs ks)" for z
    by (cases z) simp_all
  with assms show ?thesis by auto
qed

theorem set_all_combos: "set (all_combos p vals) = {x. chosen_from vals x \<and> p x}"
proof -
  have o: "set (all_combos \<checkmark> vals) = {x. chosen_from vals x}"
    unfolding all_combos_def proof (induction vals)
    case Nil
    have "chosen_from [] crr \<longleftrightarrow> crr = []" for crr by (cases crr) simp_all
    thus ?case by (subst all_combos_aux.simps) auto
  next
    case out: (Cons vs vss)
    show ?case
    proof (cases vs)
      case Nil thus ?thesis using nothing_to_choose by force
    next
      case inn: (Cons x xs)
      thus ?thesis proof (cases "[] \<in> set vss")
        case True thus ?thesis using nothing_to_choose by fastforce
      next
        case False
        with inn have 1: "all_combos_aux \<checkmark> (vs # vss) (vs # vss) [] =
          cart_prepend (rev vs) (all_combos_aux \<checkmark> vss vss [])"
          using valid_vals_crr accept_all_combos_new_digit by fast
        from False out have 2: "set (all_combos_aux \<checkmark> vss vss []) = {x. chosen_from vss x}"
          by argo
        from 1 have "set (all_combos_aux \<checkmark> (vs # vss) (vs # vss) []) =
          {x. chosen_from (vs # vss) x}"
          using chosen_from_new_digit[OF 2] by simp
        with False inn show ?thesis by simp
      qed
    qed
  qed
  thus ?thesis
  unfolding all_combos_def all_combos_filters[of p] by force
qed

theorem all_combos_dist:
  assumes "list_all distinct vals"
  shows "distinct (all_combos p vals)"
  oops


(* testing *)
fun test_sorted :: "nat list \<Rightarrow> bool" where
  "test_sorted [] = True" |
  "test_sorted [x] = True" |
  "test_sorted (x # y # xs) \<longleftrightarrow> x \<le> y \<and> test_sorted (y # xs)"

abbreviation "threes \<equiv> [[1,2,3],[1,2, 3],[1, 2, 3::nat]]"

value "nxt threes threes"

value "all_combos \<checkmark> threes"
value "all_combos test_sorted threes"
value "all_combos test_sorted [[1, 2, 3],[1],[1, 2, 3::nat]]"
value "all_combos (\<lambda>xs. (3::nat) \<in> set xs) threes"

end