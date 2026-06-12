theory Datalog_Certificate
  imports Stratified_Datalog.Datalog Tree_Decomp_Grounding_Common.Graph_Funs
begin

section \<open>Certified models of positive datalog programs\<close>

text \<open>A self-contained certificate checker for \<^emph>\<open>positive\<close> datalog programs phrased in the AFP
  \<^theory>\<open>Stratified_Datalog.Datalog\<close> clause syntax --- independent of any PDDL notion (the PDDL
  reachability certificate in \<open>Reachability_Analysis/Reachability_Certificate.thy\<close> is the
  planning-specific analogue; see \<open>ARCHITECTURE_datalog_certification.md\<close>).

  An untrusted engine (e.g. Nemo) claims that a list of ground facts \<open>M\<close> is \<^emph>\<open>the\<close> model of a
  program; it justifies the claim with a certificate in Nemo's ordered-graph format: one node per
  fact, each carrying the \<^emph>\<open>indices\<close> of the predecessor facts it was derived from. The checker
  validates, against the program itself:

  \<^item> \<^bold>\<open>ordered check\<close> (\<open>dl_ordered_check\<close>): every predecessor index is strictly smaller than the
    node's own index. The index order is a well-founded derivation rank, so the support graph is
    acyclic by construction --- no cycle detection / DFS needed.
  \<^item> \<^bold>\<open>local validity\<close> (\<open>dl_local_valid\<close>): every node is the head of a ground instance of some
    program clause whose guards hold and whose positive body atoms are \<^emph>\<open>exactly\<close> the facts at
    the predecessor indices. With the ordered check this makes every certificate fact genuinely
    derivable (\<open>\<subseteq>\<close> the least model).
  \<^item> \<^bold>\<open>closure check\<close> (\<open>dl_closure_check\<close>): for every clause and every grounding substitution
    (drawn from the finite constant universe), if the guards hold and the instantiated body is
    inside the certificate facts, the instantiated head is too. So the certificate facts form a
    model, i.e. no extra fact is derivable (\<open>\<supseteq>\<close> the least model).

  Together (theorem \<open>dl_certified_model_correct\<close>): the certified fact set is \<^emph>\<open>exactly\<close> the set
  of derivable facts. Derivability (\<open>dl_derivable\<close>) is the standard least-model semantics of a
  positive program, restricted to substitutions over the given constant universe \<open>U\<close> (for safe
  programs --- every head/guard variable occurs in the body --- this coincides with the
  unrestricted least model; the universe plays the role of Nemo's \<open>dom\<close> guards). Programs
  containing \<^const>\<open>NegLit\<close> are rejected outright (\<open>dl_positive_prog\<close>, fail-closed): with
  negation the consequence operator is not monotone and this checker's argument does not apply.\<close>

subsection \<open>Certificate data structure (Nemo ordered-graph format)\<close>

type_synonym ('p, 'c) dl_fact = "'p \<times> 'c list"

datatype ('p, 'c) dl_cert_node = DLNode
  (dn_fact: "('p, 'c) dl_fact")   \<comment> \<open>the derived ground fact (Nemo edge label)\<close>
  (dn_preds: "nat list")          \<comment> \<open>indices of the predecessor facts (Nemo edge predecessors)\<close>

datatype ('p, 'c) dl_certificate = DLCert (dl_nodes: "('p, 'c) dl_cert_node list")

definition dl_cert_facts :: "('p, 'c) dl_certificate \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_cert_facts c = map dn_fact (dl_nodes c)"

text \<open>The body facts of node \<open>i\<close>: the fact labels sitting at its predecessor indices.\<close>
definition dn_body :: "('p, 'c) dl_certificate \<Rightarrow> nat \<Rightarrow> ('p, 'c) dl_fact list" where
  "dn_body c i = map (\<lambda>j. dn_fact (dl_nodes c ! j)) (dn_preds (dl_nodes c ! i))"

subsection \<open>Ground instances of clauses\<close>

fun subst_id :: "('x \<Rightarrow> 'c) \<Rightarrow> ('x, 'c) id \<Rightarrow> 'c" where
  "subst_id \<sigma> (id.Var x) = \<sigma> x"
| "subst_id \<sigma> (id.Cst c) = c"

definition subst_atom :: "('x \<Rightarrow> 'c) \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p, 'c) dl_fact" where
  "subst_atom \<sigma> a = (fst a, map (subst_id \<sigma>) (snd a))"

fun rh_body_atom :: "('p, 'x, 'c) rh \<Rightarrow> ('p, 'x, 'c) lh option" where
  "rh_body_atom (PosLit p ids) = Some (p, ids)"
| "rh_body_atom _ = None"

definition cls_body_atoms :: "('p, 'x, 'c) clause \<Rightarrow> ('p, 'x, 'c) lh list" where
  "cls_body_atoms cl = List.map_filter rh_body_atom (the_rhs cl)"

fun is_dl_guard :: "('p, 'x, 'c) rh \<Rightarrow> bool" where
  "is_dl_guard (Eql _ _) = True"
| "is_dl_guard (Neql _ _) = True"
| "is_dl_guard _ = False"

definition cls_guards :: "('p, 'x, 'c) clause \<Rightarrow> ('p, 'x, 'c) rh list" where
  "cls_guards cl = filter is_dl_guard (the_rhs cl)"

fun eval_guard :: "('x \<Rightarrow> 'c) \<Rightarrow> ('p, 'x, 'c) rh \<Rightarrow> bool" where
  "eval_guard \<sigma> (Eql a b) = (subst_id \<sigma> a = subst_id \<sigma> b)"
| "eval_guard \<sigma> (Neql a b) = (subst_id \<sigma> a \<noteq> subst_id \<sigma> b)"
| "eval_guard \<sigma> _ = True"

fun is_pos_rh :: "('p, 'x, 'c) rh \<Rightarrow> bool" where
  "is_pos_rh (NegLit _ _) = False"
| "is_pos_rh _ = True"

definition dl_positive_prog :: "('p, 'x, 'c) clause list \<Rightarrow> bool" where
  "dl_positive_prog P \<equiv> (\<forall>cl \<in> set P. \<forall>rh \<in> set (the_rhs cl). is_pos_rh rh)"

text \<open>The grounding substitutions of a clause over a finite constant universe \<open>U\<close>: one for every
  assignment of the clause's variables to constants from \<open>U\<close>. A ground clause has no variables
  and exactly one (vacuous) substitution.\<close>

fun id_vars_list :: "('x, 'c) id \<Rightarrow> 'x list" where
  "id_vars_list (id.Var x) = [x]"
| "id_vars_list (id.Cst _) = []"

fun rh_vars_list :: "('p, 'x, 'c) rh \<Rightarrow> 'x list" where
  "rh_vars_list (Eql a b) = id_vars_list a @ id_vars_list b"
| "rh_vars_list (Neql a b) = id_vars_list a @ id_vars_list b"
| "rh_vars_list (PosLit _ ids) = concat (map id_vars_list ids)"
| "rh_vars_list (NegLit _ ids) = concat (map id_vars_list ids)"

fun cls_vars :: "('p, 'x, 'c) clause \<Rightarrow> 'x list" where
  "cls_vars (Cls _ ids rhs) = remdups (concat (map id_vars_list ids) @ concat (map rh_vars_list rhs))"

definition subst_of :: "'x list \<Rightarrow> 'c list \<Rightarrow> 'x \<Rightarrow> 'c" where
  "subst_of vs args x = the (map_of (zip vs args) x)"

definition cls_substs :: "'c list \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> ('x \<Rightarrow> 'c) list" where
  "cls_substs U cl = map (subst_of (cls_vars cl))
                         (all_combos \<checkmark> (replicate (length (cls_vars cl)) U))"

subsection \<open>The three checks\<close>

definition dl_ordered_check :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_ordered_check c \<equiv>
     (\<forall>i < length (dl_nodes c). \<forall>j \<in> set (dn_preds (dl_nodes c ! i)). j < i)"

definition dl_local_valid :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> nat \<Rightarrow> bool" where
  "dl_local_valid P U c i \<equiv>
     (\<exists>cl \<in> set P. \<exists>\<sigma> \<in> set (cls_substs U cl).
        (\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
        \<and> dn_fact (dl_nodes c ! i) = subst_atom \<sigma> (the_lh cl)
        \<and> set (dn_body c i) = set (map (subst_atom \<sigma>) (cls_body_atoms cl)))"

definition dl_closure_check :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_closure_check P U c \<equiv>
     (\<forall>cl \<in> set P. \<forall>\<sigma> \<in> set (cls_substs U cl).
        ((\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
         \<and> (\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set (dl_cert_facts c)))
        \<longrightarrow> subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c))"

definition dl_admissible :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_admissible P U c \<equiv>
     dl_positive_prog P
     \<and> dl_ordered_check c
     \<and> dl_closure_check P U c
     \<and> (\<forall>i < length (dl_nodes c). dl_local_valid P U c i)"

text \<open>The model-checking entry point: \<open>M\<close> is certified to be the (universe-restricted) least
  model of \<open>P\<close> iff the certificate is admissible and its facts are exactly \<open>M\<close>.\<close>
definition dl_certified_model :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_certified_model P U M c \<equiv> dl_admissible P U c \<and> set M = set (dl_cert_facts c)"

subsection \<open>Reference semantics: bottom-up derivability\<close>

text \<open>The least-model semantics of a positive program over universe \<open>U\<close>, as an inductive
  predicate: a fact is derivable iff it is the head of a ground clause instance whose guards
  hold and whose body atoms are derivable. Bodyless clauses are the base case.\<close>
inductive dl_derivable :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_fact \<Rightarrow> bool"
  for P :: "('p, 'x, 'c) clause list" and U :: "'c list" where
  derive: "\<lbrakk> cl \<in> set P; \<sigma> \<in> set (cls_substs U cl);
             \<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g;
             \<forall>a \<in> set (cls_body_atoms cl). dl_derivable P U (subst_atom \<sigma> a) \<rbrakk>
           \<Longrightarrow> dl_derivable P U (subst_atom \<sigma> (the_lh cl))"

subsection \<open>Relating to AFP Datalog semantics\<close>

text \<open>The least model of a positive program is always on rank 0. 
The stratum of each predicate is 0.\<close>

text \<open>The equivalence needs three side conditions tying \<open>P\<close>, \<open>U\<close> and the AFP semantics together:
\<^item> \<^bold>\<open>positivity\<close> (\<^const>\<open>dl_positive_prog\<close>): \<open>dl_derivable\<close> silently ignores \<^const>\<open>NegLit\<close>s
  (they are neither guards nor body atoms), while the AFP semantics constrains them.
\<^item> \<^bold>\<open>safety\<close> (\<open>dl_safe\<close>): every clause variable occurs in a positive body atom. The AFP
  \<^const>\<open>solves_cls\<close> quantifies over \<^emph>\<open>all\<close> valuations \<open>'x \<Rightarrow> 'c\<close>, whereas \<open>dl_derivable\<close>
  only instantiates variables from \<open>U\<close>; safety pins every variable to a derivable fact.
\<^item> \<^bold>\<open>head-constant coverage\<close> (\<open>dl_heads_covered\<close>): constants in clause heads lie in \<open>U\<close>,
  so derivable facts only mention \<open>U\<close>-constants and body variables stay inside \<open>U\<close>.\<close>

fun id_consts_list :: "('x, 'c) id \<Rightarrow> 'c list" where
  "id_consts_list (id.Var _) = []"
| "id_consts_list (id.Cst c) = [c]"

definition dl_heads_covered :: "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> bool" where
  "dl_heads_covered U P \<equiv>
     \<forall>cl \<in> set P. \<forall>i \<in> set (snd (the_lh cl)). set (id_consts_list i) \<subseteq> set U"

definition dl_safe :: "('p, 'x, 'c) clause list \<Rightarrow> bool" where
  "dl_safe P \<equiv>
     \<forall>cl \<in> set P. \<forall>x \<in> set (cls_vars cl).
       \<exists>a \<in> set (cls_body_atoms cl). x \<in> set (concat (map id_vars_list (snd a)))"

text \<open>Bridging the checker's substitution application to the AFP evaluation functions.\<close>

lemma subst_id_eval_id: "subst_id \<sigma> = (\<lambda>i. \<lbrakk>i\<rbrakk>\<^sub>i\<^sub>d \<sigma>)"
proof (rule ext)
  fix i show "subst_id \<sigma> i = \<lbrakk>i\<rbrakk>\<^sub>i\<^sub>d \<sigma>" by (cases i) simp_all
qed

lemma rh_body_atom_Some: "rh_body_atom rh = Some a \<longleftrightarrow> rh = PosLit (fst a) (snd a)"
  by (cases rh; cases a) auto

lemma set_map_filter': "set (List.map_filter f xs) = {y. \<exists>x \<in> set xs. f x = Some y}"
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

lemma cls_body_atoms_iff:
  "a \<in> set (cls_body_atoms cl) \<longleftrightarrow> PosLit (fst a) (snd a) \<in> set (the_rhs cl)"
  unfolding cls_body_atoms_def set_map_filter' by (auto simp: rh_body_atom_Some)

lemma cls_vars_head_vars:
  assumes "i \<in> set (snd (the_lh cl))" and "x \<in> set (id_vars_list i)"
  shows "x \<in> set (cls_vars cl)"
  using assms by (cases cl) auto

lemma cls_vars_rhs_vars:
  assumes "rh \<in> set (the_rhs cl)" and "x \<in> set (rh_vars_list rh)"
  shows "x \<in> set (cls_vars cl)"
  using assms by (cases cl) auto

lemma subst_id_agree:
  assumes "\<forall>x \<in> set (id_vars_list i). \<sigma> x = \<sigma>' x"
  shows "subst_id \<sigma> i = subst_id \<sigma>' i"
  using assms by (cases i) simp_all

lemma subst_atom_agree:
  assumes "\<forall>i \<in> set (snd a). \<forall>x \<in> set (id_vars_list i). \<sigma> x = \<sigma>' x"
  shows "subst_atom \<sigma> a = subst_atom \<sigma>' a"
proof -
  have "map (subst_id \<sigma>) (snd a) = map (subst_id \<sigma>') (snd a)"
    using assms by (intro map_cong[OF refl] subst_id_agree) auto
  then show ?thesis unfolding subst_atom_def by simp
qed

lemma eval_guard_agree:
  assumes "\<forall>x \<in> set (rh_vars_list g). \<sigma> x = \<sigma>' x"
  shows "eval_guard \<sigma> g = eval_guard \<sigma>' g"
proof (cases g)
  case (Eql a b)
  then have "subst_id \<sigma> a = subst_id \<sigma>' a" "subst_id \<sigma> b = subst_id \<sigma>' b"
    using assms by (auto intro!: subst_id_agree)
  with Eql show ?thesis by simp
next
  case (Neql a b)
  then have "subst_id \<sigma> a = subst_id \<sigma>' a" "subst_id \<sigma> b = subst_id \<sigma>' b"
    using assms by (auto intro!: subst_id_agree)
  with Neql show ?thesis by simp
qed simp_all

text \<open>Membership in \<^const>\<open>cls_substs\<close>: exactly the tabulated substitutions over \<open>U\<close>.\<close>

lemma chosen_from_replicate:
  "chosen_from (replicate n U) xs \<longleftrightarrow> length xs = n \<and> set xs \<subseteq> set U"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by (cases n) simp_all
next
  case (Cons x xs)
  then show ?case by (cases n) auto
qed

lemma cls_substs_iff:
  "\<sigma> \<in> set (cls_substs U cl) \<longleftrightarrow>
     (\<exists>cs. \<sigma> = subst_of (cls_vars cl) cs
           \<and> length cs = length (cls_vars cl) \<and> set cs \<subseteq> set U)"
  unfolding cls_substs_def set_map set_all_combos
  by (auto simp: chosen_from_replicate)

lemma subst_of_map: "x \<in> set vs \<Longrightarrow> subst_of vs (map f vs) x = f x"
  unfolding subst_of_def map_of_zip_map by simp

lemma subst_of_in_set:
  assumes "length cs = length vs" and "x \<in> set vs"
  shows "subst_of vs cs x \<in> set cs"
proof -
  obtain c where "map_of (zip vs cs) x = Some c"
    using assms by (metis map_of_zip_is_Some)
  then show ?thesis
    unfolding subst_of_def using map_of_SomeD set_zip_rightD by fastforce
qed

lemma cls_substs_rangeD:
  assumes "\<sigma> \<in> set (cls_substs U cl)" and "x \<in> set (cls_vars cl)"
  shows "\<sigma> x \<in> set U"
  using assms subst_of_in_set unfolding cls_substs_iff by fastforce

text \<open>Derivable facts only mention constants from \<open>U\<close>.\<close>

lemma dl_derivable_consts:
  assumes cov: "dl_heads_covered U P"
    and der: "dl_derivable P U f"
  shows "set (snd f) \<subseteq> set U"
  using der
proof (induction rule: dl_derivable.induct)
  case (derive cl \<sigma>)
  have "subst_id \<sigma> i \<in> set U" if i: "i \<in> set (snd (the_lh cl))" for i
  proof (cases i)
    case (Var x)
    then have "x \<in> set (cls_vars cl)"
      using i cls_vars_head_vars by fastforce
    then show ?thesis
      using Var cls_substs_rangeD[OF derive.hyps(2)] by simp
  next
    case (Cst c)
    then show ?thesis
      using cov derive.hyps(1) i unfolding dl_heads_covered_def by fastforce
  qed
  then show ?case unfolding subst_atom_def by auto
qed

text \<open>\<^bold>\<open>Soundness\<close>: every derivable fact is in every AFP solution (positivity needed).\<close>

lemma dl_derivable_in_solution:
  assumes pos: "dl_positive_prog P"
    and sol: "\<rho> \<Turnstile>\<^sub>d\<^sub>l (set P)"
    and der: "dl_derivable P U f"
  shows "snd f \<in> \<rho> (fst f)"
  using der
proof (induction rule: dl_derivable.induct)
  case (derive cl \<sigma>)
  obtain q ids rhs where cl_eq: "cl = Cls q ids rhs" by (cases cl)
  have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>" if rh: "rh \<in> set rhs" for rh
  proof (cases rh)
    case (Eql a b)
    then have "rh \<in> set (cls_guards cl)"
      using rh cl_eq unfolding cls_guards_def by simp
    then have "eval_guard \<sigma> rh" using derive.hyps(3) by blast
    then show ?thesis using Eql by (simp add: subst_id_eval_id)
  next
    case (Neql a b)
    then have "rh \<in> set (cls_guards cl)"
      using rh cl_eq unfolding cls_guards_def by simp
    then have "eval_guard \<sigma> rh" using derive.hyps(3) by blast
    then show ?thesis using Neql by (simp add: subst_id_eval_id)
  next
    case (PosLit p' ids')
    then have "(p', ids') \<in> set (cls_body_atoms cl)"
      using rh cl_eq cls_body_atoms_iff by fastforce
    then have "snd (subst_atom \<sigma> (p', ids')) \<in> \<rho> (fst (subst_atom \<sigma> (p', ids')))"
      using derive.IH by blast
    then show ?thesis
      using PosLit by (simp add: subst_atom_def subst_id_eval_id)
  next
    case (NegLit p' ids')
    then have False
      using pos derive.hyps(1) rh cl_eq unfolding dl_positive_prog_def by fastforce
    then show ?thesis ..
  qed
  then have rhs_sat: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>" by simp
  have "\<lbrakk>cl\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    using sol derive.hyps(1) unfolding solves_program_def solves_cls_def by blast
  then have "\<lbrakk>(q, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
    using rhs_sat unfolding cl_eq meaning_cls.simps by blast
  then show ?case using cl_eq by (simp add: subst_atom_def subst_id_eval_id)
qed

text \<open>\<^bold>\<open>Completeness core\<close>: the derivable facts form an AFP solution (safety + coverage).\<close>

lemma dl_derivable_solves:
  assumes safe: "dl_safe P" and cov: "dl_heads_covered U P"
  shows "(\<lambda>q. {r. dl_derivable P U (q, r)}) \<Turnstile>\<^sub>d\<^sub>l (set P)"
    (is "?D \<Turnstile>\<^sub>d\<^sub>l _")
  unfolding solves_program_def solves_cls_def
proof (intro ballI allI)
  fix cl \<sigma>
  assume cl: "cl \<in> set P"
  obtain q ids rhs where cl_eq: "cl = Cls q ids rhs" by (cases cl)
  have main: "\<lbrakk>(q, ids)\<rbrakk>\<^sub>l\<^sub>h ?D \<sigma>" if body: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s ?D \<sigma>"
  proof -
    have body_der: "dl_derivable P U (fst a, \<lbrakk>snd a\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
      if a: "a \<in> set (cls_body_atoms cl)" for a
    proof -
      from a have "PosLit (fst a) (snd a) \<in> set rhs"
        using cls_body_atoms_iff[of a cl] cl_eq by simp
      then have "\<lbrakk>\<^bold>+ (fst a) (snd a)\<rbrakk>\<^sub>r\<^sub>h ?D \<sigma>" using body by fastforce
      then show ?thesis by simp
    qed
    have varU: "\<sigma> x \<in> set U" if x: "x \<in> set (cls_vars cl)" for x
    proof -
      from safe cl x obtain a where a: "a \<in> set (cls_body_atoms cl)"
        and xa: "x \<in> set (concat (map id_vars_list (snd a)))"
        unfolding dl_safe_def by blast
      from xa obtain i where i: "i \<in> set (snd a)" and xi: "x \<in> set (id_vars_list i)"
        by auto
      have i_eq: "i = id.Var x" using xi by (cases i) auto
      have "set (\<lbrakk>snd a\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>) \<subseteq> set U"
        using dl_derivable_consts[OF cov body_der[OF a]] by simp
      moreover have "\<sigma> x \<in> set (\<lbrakk>snd a\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
        using i i_eq by force
      ultimately show ?thesis by blast
    qed
    define \<sigma>' where "\<sigma>' = subst_of (cls_vars cl) (map \<sigma> (cls_vars cl))"
    have agree: "\<sigma>' x = \<sigma> x" if "x \<in> set (cls_vars cl)" for x
      unfolding \<sigma>'_def using that subst_of_map by fastforce
    have \<sigma>'_in: "\<sigma>' \<in> set (cls_substs U cl)"
    proof -
      have "length (map \<sigma> (cls_vars cl)) = length (cls_vars cl)" by simp
      moreover have "set (map \<sigma> (cls_vars cl)) \<subseteq> set U" using varU by auto
      ultimately show ?thesis unfolding cls_substs_iff \<sigma>'_def by blast
    qed
    have guards: "eval_guard \<sigma>' g" if g: "g \<in> set (cls_guards cl)" for g
    proof -
      from g have g_rhs: "g \<in> set rhs"
        using cl_eq unfolding cls_guards_def by simp
      have "eval_guard \<sigma> g"
      proof (cases g)
        case (Eql a b)
        then show ?thesis using body g_rhs by (fastforce simp: subst_id_eval_id)
      next
        case (Neql a b)
        then show ?thesis using body g_rhs by (fastforce simp: subst_id_eval_id)
      qed simp_all
      moreover have "\<forall>x \<in> set (rh_vars_list g). \<sigma>' x = \<sigma> x"
        using agree cls_vars_rhs_vars g_rhs cl_eq by fastforce
      ultimately show ?thesis using eval_guard_agree by blast
    qed
    have body': "dl_derivable P U (subst_atom \<sigma>' a)"
      if a: "a \<in> set (cls_body_atoms cl)" for a
    proof -
      have vars_a: "\<forall>i \<in> set (snd a). \<forall>x \<in> set (id_vars_list i). \<sigma>' x = \<sigma> x"
      proof (intro ballI)
        fix i x assume i: "i \<in> set (snd a)" and x: "x \<in> set (id_vars_list i)"
        have "PosLit (fst a) (snd a) \<in> set (the_rhs cl)"
          using a cls_body_atoms_iff by blast
        moreover have "x \<in> set (rh_vars_list (PosLit (fst a) (snd a)))"
          using i x by force
        ultimately have "x \<in> set (cls_vars cl)" by (metis cls_vars_rhs_vars)
        then show "\<sigma>' x = \<sigma> x" using agree by blast
      qed
      have "subst_atom \<sigma>' a = subst_atom \<sigma> a"
        using subst_atom_agree vars_a by blast
      moreover have "subst_atom \<sigma> a = (fst a, \<lbrakk>snd a\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
        unfolding subst_atom_def by (simp add: subst_id_eval_id)
      ultimately show ?thesis using body_der[OF a] by simp
    qed
    have "dl_derivable P U (subst_atom \<sigma>' (the_lh cl))"
      using dl_derivable.derive[OF cl \<sigma>'_in] guards body' by blast
    moreover have "subst_atom \<sigma>' (the_lh cl) = subst_atom \<sigma> (the_lh cl)"
    proof -
      have "\<forall>i \<in> set (snd (the_lh cl)). \<forall>x \<in> set (id_vars_list i). \<sigma>' x = \<sigma> x"
        using agree cls_vars_head_vars by fast
      then show ?thesis using subst_atom_agree by blast
    qed
    ultimately have "dl_derivable P U (subst_atom \<sigma> (the_lh cl))" by simp
    then show ?thesis
      using cl_eq by (simp add: subst_atom_def subst_id_eval_id)
  qed
  then show "\<lbrakk>cl\<rbrakk>\<^sub>c\<^sub>l\<^sub>s ?D \<sigma>"
    unfolding cl_eq meaning_cls.simps by blast
qed

text \<open>\<^bold>\<open>The equivalence\<close>: on positive, safe, head-covered programs, \<open>dl_derivable\<close> coincides
  with the (rank-0) least solution of the AFP semantics.\<close>

lemma dl_derivable_iff_least_solution:
  assumes lst: "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (set P) (\<lambda>p. 0)"
    and pos: "dl_positive_prog P"
    and safe: "dl_safe P"
    and cov: "dl_heads_covered U P"
  shows "dl_derivable P U (p, r) \<longleftrightarrow> r \<in> \<rho> p"
proof
  assume "dl_derivable P U (p, r)"
  moreover have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (set P)"
    using lst unfolding least_solution_def by blast
  ultimately show "r \<in> \<rho> p"
    using dl_derivable_in_solution[OF pos] by fastforce
next
  assume r: "r \<in> \<rho> p"
  have D_sol: "(\<lambda>q. {r. dl_derivable P U (q, r)}) \<Turnstile>\<^sub>d\<^sub>l (set P)"
    using dl_derivable_solves[OF safe cov] .
  with lst have "lte \<rho> (\<lambda>p. 0) (\<lambda>q. {r. dl_derivable P U (q, r)})"
    unfolding least_solution_def by blast
  then have "\<rho> p \<subseteq> {r. dl_derivable P U (p, r)}"
    unfolding lte_def lt_def by auto
  with r show "dl_derivable P U (p, r)" by blast
qed
  

subsection \<open>Correctness\<close>

text \<open>\<^bold>\<open>Closure soundness (\<open>\<supseteq>\<close>):\<close> every derivable fact is in a closure-checked certificate ---
  the certificate facts form a model, and derivability is the least one.\<close>
lemma dl_derivable_in_cert:
  assumes "dl_closure_check P U c"
    and "dl_derivable P U f"
  shows "f \<in> set (dl_cert_facts c)"
  using assms(2)
proof (induction rule: dl_derivable.induct)
  case (derive cl \<sigma>)
  from derive.IH have "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set (dl_cert_facts c)"
    by blast
  then show ?case
    using assms(1) derive.hyps(1,2,3) unfolding dl_closure_check_def by blast
qed

text \<open>\<^bold>\<open>Local-validity tightness (\<open>\<subseteq>\<close>):\<close> in an ordered, locally valid certificate every node's
  fact is genuinely derivable, by strong induction on the node index (predecessor indices are
  strictly smaller, so their facts are derivable by induction hypothesis).\<close>
lemma dl_cert_node_derivable:
  assumes oc: "dl_ordered_check c"
    and lv: "\<forall>i < length (dl_nodes c). dl_local_valid P U c i"
    and i: "i < length (dl_nodes c)"
  shows "dl_derivable P U (dn_fact (dl_nodes c ! i))"
  using i
proof (induction i rule: less_induct)
  case (less i)
  from lv less.prems have "dl_local_valid P U c i" by blast
  then obtain cl \<sigma> where
    cl: "cl \<in> set P" and s: "\<sigma> \<in> set (cls_substs U cl)" and
    g: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g" and
    hd_eq: "dn_fact (dl_nodes c ! i) = subst_atom \<sigma> (the_lh cl)" and
    bd: "set (dn_body c i) = set (map (subst_atom \<sigma>) (cls_body_atoms cl))"
    unfolding dl_local_valid_def by blast
  have "\<forall>a \<in> set (cls_body_atoms cl). dl_derivable P U (subst_atom \<sigma> a)"
  proof
    fix a assume "a \<in> set (cls_body_atoms cl)"
    then have "subst_atom \<sigma> a \<in> set (dn_body c i)" using bd by auto
    then obtain j where j: "j \<in> set (dn_preds (dl_nodes c ! i))"
      and fj: "subst_atom \<sigma> a = dn_fact (dl_nodes c ! j)"
      unfolding dn_body_def by auto
    from oc less.prems j have "j < i" unfolding dl_ordered_check_def by blast
    then show "dl_derivable P U (subst_atom \<sigma> a)"
      using less.IH less.prems fj by simp
  qed
  then show ?case
    using dl_derivable.derive[OF cl s g] hd_eq by simp
qed

text \<open>\<^bold>\<open>Main theorem:\<close> an accepted model is exactly the set of derivable facts.\<close>
theorem dl_certified_model_correct:
  assumes "dl_certified_model P U M c"
  shows "set M = {f. dl_derivable P U f}"
proof -
  from assms have adm: "dl_admissible P U c" and M: "set M = set (dl_cert_facts c)"
    unfolding dl_certified_model_def by auto
  from adm have oc: "dl_ordered_check c" and cc: "dl_closure_check P U c"
    and lv: "\<forall>i < length (dl_nodes c). dl_local_valid P U c i"
    unfolding dl_admissible_def by auto
  have "set (dl_cert_facts c) \<subseteq> {f. dl_derivable P U f}"
  proof
    fix f assume "f \<in> set (dl_cert_facts c)"
    then obtain i where "i < length (dl_nodes c)" and "dn_fact (dl_nodes c ! i) = f"
      unfolding dl_cert_facts_def by (auto simp: in_set_conv_nth)
    then show "f \<in> {f. dl_derivable P U f}"
      using dl_cert_node_derivable[OF oc lv] by auto
  qed
  moreover have "{f. dl_derivable P U f} \<subseteq> set (dl_cert_facts c)"
    using dl_derivable_in_cert[OF cc] by auto
  ultimately show ?thesis using M by auto
qed

subsection \<open>Example: transitive closure\<close>

text \<open>\<open>path\<close> is the transitive closure of \<open>edge\<close> over the chain \<open>1 \<rightarrow> 2 \<rightarrow> 3\<close>.\<close>

definition ex_prog :: "(String.literal, String.literal, nat) clause list" where
  "ex_prog \<equiv> [
     Cls (STR ''edge'') [id.Cst 1, id.Cst 2] [],
     Cls (STR ''edge'') [id.Cst 2, id.Cst 3] [],
     Cls (STR ''path'') [id.Var (STR ''x''), id.Var (STR ''y'')]
       [PosLit (STR ''edge'') [id.Var (STR ''x''), id.Var (STR ''y'')]],
     Cls (STR ''path'') [id.Var (STR ''x''), id.Var (STR ''z'')]
       [PosLit (STR ''edge'') [id.Var (STR ''x''), id.Var (STR ''y'')],
        PosLit (STR ''path'') [id.Var (STR ''y''), id.Var (STR ''z'')]]
   ]"

definition ex_universe :: "nat list" where
  "ex_universe \<equiv> [1, 2, 3]"

definition ex_cert :: "(String.literal, nat) dl_certificate" where
  "ex_cert \<equiv> DLCert [
     DLNode (STR ''edge'', [1, 2]) [],
     DLNode (STR ''edge'', [2, 3]) [],
     DLNode (STR ''path'', [1, 2]) [0],
     DLNode (STR ''path'', [2, 3]) [1],
     DLNode (STR ''path'', [1, 3]) [0, 3]
   ]"

definition ex_model :: "(String.literal, nat) dl_fact list" where
  "ex_model \<equiv> dl_cert_facts ex_cert"

lemma "dl_certified_model ex_prog ex_universe ex_model ex_cert" by eval

text \<open>Negative probes: dropping \<open>path (1, 3)\<close> breaks the closure check (the fact is still
  derivable), and reversing a support edge breaks the ordered check.\<close>
lemma "\<not> dl_closure_check ex_prog ex_universe (DLCert (butlast (dl_nodes ex_cert)))" by eval
lemma "\<not> dl_ordered_check (DLCert [DLNode (STR ''edge'', [1, 2]) [0]]
                            :: (String.literal, nat) dl_certificate)" by eval

end
