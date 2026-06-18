theory Datalog_Sema_Supplement
  imports Stratified_Datalog.Datalog Tree_Decomp_Grounding_Common.Graph_Funs
begin

text \<open>\<^emph>\<open>Semantic supplement to the AFP \<^theory>\<open>Stratified_Datalog.Datalog\<close>.\<close> Two layers, both over
  the AFP datatypes (programs are \<^typ>\<open>('p, 'x, 'c) dl_program\<close>, i.e.\ clause \<^emph>\<open>sets\<close>): first
  \<^emph>\<open>positive datalog\<close> and its relation to stratified datalog, then the \<^emph>\<open>universe-restricted\<close>
  reference semantics with the locales \<open>datalog_sem\<close>, \<open>positive_datalog\<close>,
  \<open>datalog_universe\<close> and \<open>positive_datalog_universe\<close>. The executable certificate
  checker that refines this lives in \<open>Datalog_Certificate.thy\<close>.\<close>

section \<open>Positive datalog and its relation to stratified datalog\<close>

text \<open>The \<^emph>\<open>positive\<close> fragment of the AFP \<^theory>\<open>Stratified_Datalog.Datalog\<close> clause language:
  programs whose clause bodies contain no \<^const>\<open>NegLit\<close>. This is the syntactic restriction under
  which the consequence operator is monotone, and --- as shown here --- a degenerate case of
  \<^emph>\<open>stratified\<close> datalog: a positive program is well-stratified at the trivial stratification
  \<open>\<lambda>_. 0\<close>, where the AFP stratum ordering collapses to pointwise \<open>\<subseteq>\<close>. The \<open>positive_datalog\<close>
  locale packages the positivity assumption together with these consequences; the universe- and
  certificate-level developments build on it below.\<close>

subsection \<open>Positivity of a program\<close>

fun is_pos_rh :: "('p, 'x, 'c) rh \<Rightarrow> bool" where
  "is_pos_rh (NegLit _ _) = False"
| "is_pos_rh _ = True"

text \<open>Phrased on the AFP program type \<^typ>\<open>('p, 'x, 'c) dl_program\<close> (a \<^typ>\<open>('p, 'x, 'c) clause set\<close>),
  not a list: positivity is a property of the program as a set of clauses. The executable
  list-based refinement (where a \<open>clause list\<close> implements the set via \<^const>\<open>set\<close>) is layered on
  top later, in the certificate development.\<close>

definition dl_positive_prog :: "('p, 'x, 'c) dl_program \<Rightarrow> bool" where
  "dl_positive_prog P \<equiv> (\<forall>cl \<in> P. \<forall>rh \<in> set (the_rhs cl). is_pos_rh rh)"

subsection \<open>Relation to stratified datalog\<close>

text \<open>A positive program is a stratified program, which is well-stratified
  (\<^const>\<open>strat_wf\<close>) at the constant stratification \<open>\<lambda>_. 0\<close>. The only way a clause can violate
  stratification is a negative body literal (\<^const>\<open>rnk\<close> \<open>1 + s p\<close>), which a positive program has
  none of, so every body literal has rank \<open>0 \<le> s p\<close>. The AFP stratified-datalog least-solution
  machinery (\<^const>\<open>least_solution\<close>) therefore applies; and at a single stratum its
  predicate-valuation ordering \<open>\<sqsubseteq>\<close> collapses to pointwise \<open>\<subseteq>\<close>, so the stratified least solution is
  just the \<open>\<subseteq>\<close>-least model.\<close>

lemma rnk_pos_zero: "is_pos_rh rh \<Longrightarrow> rnk (\<lambda>_. 0) rh = 0"
  by (cases rh) auto

text \<open>At the trivial stratification the stratum ordering is plain pointwise \<open>\<subseteq>\<close>.\<close>
lemma lte_zero_iff: "(\<rho> \<sqsubseteq>(\<lambda>_. 0)\<sqsubseteq> \<rho>') \<longleftrightarrow> (\<forall>p. \<rho> p \<subseteq> \<rho>' p)"
proof
  assume "\<rho> \<sqsubseteq>(\<lambda>_. 0)\<sqsubseteq> \<rho>'"
  then show "\<forall>p. \<rho> p \<subseteq> \<rho>' p"
    unfolding lte_def lt_def by auto
next
  assume sub: "\<forall>p. \<rho> p \<subseteq> \<rho>' p"
  show "\<rho> \<sqsubseteq>(\<lambda>_. 0)\<sqsubseteq> \<rho>'"
  proof (cases "\<rho> = \<rho>'")
    case True then show ?thesis unfolding lte_def by simp
  next
    case False
    then obtain p where "\<rho> p \<subset> \<rho>' p"
      using sub by (metis fun_eq_iff psubsetI)
    then have "\<rho> \<sqsubset>(\<lambda>_. 0)\<sqsubset> \<rho>'"
      unfolding lt_def using sub by (auto intro!: exI[of _ p])
    then show ?thesis unfolding lte_def by simp
  qed
qed

text \<open>Hence a least solution at \<open>\<lambda>_. 0\<close> is exactly the \<open>\<subseteq>\<close>-least solution.\<close>
lemma least_solution_zero_iff:
  "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl (\<lambda>_. 0) \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> (\<forall>p. \<rho> p \<subseteq> \<rho>' p))"
  unfolding least_solution_def by (metis lte_zero_iff)

subsection \<open>The positive datalog locale\<close>

text \<open>A program carrying just the positivity assumption.\<close>

locale positive_datalog =
  fixes P :: "('p, 'x, 'c) dl_program"
  assumes positive: "dl_positive_prog P"
begin

text \<open>\<^bold>\<open>Relation to stratified datalog:\<close> \<open>P\<close> is well-stratified at the trivial stratification \<open>\<lambda>_. 0\<close>
  --- with no negative body literals, every clause's body ranks at most its head stratum.\<close>
lemma positive_strat_wf: "strat_wf (\<lambda>_. 0) P"
  unfolding strat_wf_def
proof
  fix c assume c: "c \<in> P"
  obtain p ids rhs where ceq: "c = Cls p ids rhs" by (cases c)
  have "\<forall>rh \<in> set rhs. is_pos_rh rh"
    using positive c unfolding dl_positive_prog_def ceq by auto
  then have "\<forall>rh \<in> set rhs. rnk (\<lambda>_. 0) rh = 0"
    using rnk_pos_zero by blast
  then show "strat_wf_cls (\<lambda>_. 0) c"
    unfolding ceq strat_wf_cls.simps by simp
qed

lemmas stratified = positive_strat_wf

text \<open>So a least solution of \<open>P\<close> at that stratification is exactly the \<open>\<subseteq>\<close>-least model.\<close>
lemma least_solution_iff:
  "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t P (\<lambda>_. 0) \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l P \<and> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l P \<longrightarrow> (\<forall>p. \<rho> p \<subseteq> \<rho>' p))"
  using least_solution_zero_iff .

end

section \<open>Universe-restricted datalog semantics\<close>

text \<open>The reference least-model semantics of a positive datalog program over a finite constant
  universe \<open>U\<close>, phrased on the AFP \<^theory>\<open>Stratified_Datalog.Datalog\<close> clause syntax with the
  program a \<^typ>\<open>('p, 'x, 'c) dl_program\<close> (clause \<^emph>\<open>set\<close>). The \<open>datalog_sem\<close> locale fixes \<open>U\<close>;
  \<open>datalog_universe\<close> adds a \<open>U\<close>-safe, head-covered program; and \<open>positive_datalog_universe\<close>
  combines that with \<open>positive_datalog\<close>, so that \<open>U\<close>-restricted derivability coincides with the
  AFP least solution. The list-based grounding (\<open>cls_substs\<close>) is the executable layer.\<close>

subsection \<open>Ground facts and substitutions\<close>

type_synonym ('p, 'c) dl_fact = "'p \<times> 'c list"

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

subsection \<open>Side conditions tying \<open>P\<close>, \<open>U\<close> and the AFP semantics together\<close>

text \<open>The equivalence needs three side conditions:
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

definition dl_heads_covered :: "'c set \<Rightarrow> ('p, 'x, 'c) dl_program \<Rightarrow> bool" where
  "dl_heads_covered U P \<equiv>
     \<forall>cl \<in> P. \<forall>i \<in> set (snd (the_lh cl)). set (id_consts_list i) \<subseteq> U"

definition dl_safe :: "('p, 'x, 'c) dl_program \<Rightarrow> bool" where
  "dl_safe P \<equiv>
     \<forall>cl \<in> P. \<forall>x \<in> set (cls_vars cl).
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


subsection \<open>Datalog semantics restricted to a universe\<close>

text \<open>A fixed (abstract) finite constant universe \<open>U\<close>, as a \<^emph>\<open>set\<close>. Fixing only the universe ---
  no program --- \<open>datalog_universe\<close> below extends it with a program and the inductive derivability.
  The universe is abstract; the executable certificate checker instantiates it with \<open>set U_list\<close>.\<close>

locale datalog_sem =
  fixes U :: "'c set"


subsection \<open>The universe-restricted datalog locale\<close>

text \<open>\<^emph>\<open>Datalog universe\<close>: the universe-restriction half --- a fixed universe set \<open>U\<close>
  (\<^locale>\<open>datalog_sem\<close>) together with a program \<open>P\<close> that is \<^emph>\<open>safe\<close> and \<^emph>\<open>head-covered\<close>. No
  positivity is assumed, so this isolates the facts that follow from the universe side conditions
  alone. It owns the inductive derivability \<open>derivable\<close>.\<close>

locale datalog_prog = datalog_sem U for U :: "'c set" +
  fixes P :: "('p, 'x, 'c) dl_program"
begin

text \<open>The least-model semantics of this locale's program \<open>P\<close> over its universe \<open>U\<close>, as an
  inductive predicate: a fact is derivable iff it is the head of a ground clause instance (each
  variable assigned a constant from the universe set \<open>U\<close>) whose guards hold and whose body atoms
  are derivable. Bodyless clauses are the base case. The inductive is owned by this
  \<^emph>\<open>assumption-free\<close> locale, so the exported \<open>derivable.induct\<close> / \<open>derivable.derive\<close> rules carry no
  side conditions and can be used by the (assumption-free) certificate checker.\<close>
inductive derivable :: "('p, 'c) dl_fact \<Rightarrow> bool" where
  derive: "\<lbrakk> cl \<in> P; \<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> U;
             \<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g;
             \<forall>a \<in> set (cls_body_atoms cl). derivable (subst_atom \<sigma> a) \<rbrakk>
           \<Longrightarrow> derivable (subst_atom \<sigma> (the_lh cl))"

end

text \<open>\<^emph>\<open>Datalog universe\<close>: the universe-restriction half --- the assumption-free
  \<^locale>\<open>datalog_prog\<close> (a fixed universe set \<open>U\<close> and program \<open>P\<close>) plus the side conditions that
  \<open>P\<close> is \<^emph>\<open>safe\<close> and \<^emph>\<open>head-covered\<close>. No positivity is assumed, so this isolates the facts that
  follow from the universe side conditions alone.\<close>

locale datalog_universe = datalog_prog U P
  for U :: "'c set" and P :: "('p, 'x, 'c) dl_program" +
  assumes safe:    "dl_safe P"
      and covered: "dl_heads_covered U P"
begin

text \<open>Derivable facts mention only universe constants (head coverage from the locale).\<close>
lemma derivable_consts: "derivable f \<Longrightarrow> set (snd f) \<subseteq> U"
proof (induction rule: derivable.induct)
  case (derive cl \<sigma>)
  have "subst_id \<sigma> i \<in> U" if i: "i \<in> set (snd (the_lh cl))" for i
  proof (cases i)
    case (Var x)
    then have "x \<in> set (cls_vars cl)"
      using i cls_vars_head_vars by fastforce
    then have "\<sigma> x \<in> U" using derive.hyps(2) by blast
    then show ?thesis using Var by simp
  next
    case (Cst c)
    then show ?thesis
      using covered derive.hyps(1) i unfolding dl_heads_covered_def by fastforce
  qed
  then show ?case unfolding subst_atom_def by auto
qed

text \<open>\<^bold>\<open>Completeness core\<close>: the derivable facts form an AFP solution of \<open>P\<close> (safety + coverage).\<close>
lemma derivable_solves: "(\<lambda>q. {r. derivable (q, r)}) \<Turnstile>\<^sub>d\<^sub>l P"
    (is "?D \<Turnstile>\<^sub>d\<^sub>l _")
  unfolding solves_program_def solves_cls_def
proof (intro ballI allI)
  fix cl \<sigma>
  assume cl: "cl \<in> P"
  obtain q ids rhs where cl_eq: "cl = Cls q ids rhs" by (cases cl)
  have main: "\<lbrakk>(q, ids)\<rbrakk>\<^sub>l\<^sub>h ?D \<sigma>" if body: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s ?D \<sigma>"
  proof -
    have body_der: "derivable (fst a, \<lbrakk>snd a\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
      if a: "a \<in> set (cls_body_atoms cl)" for a
    proof -
      from a have "PosLit (fst a) (snd a) \<in> set rhs"
        using cls_body_atoms_iff[of a cl] cl_eq by simp
      then have "\<lbrakk>\<^bold>+ (fst a) (snd a)\<rbrakk>\<^sub>r\<^sub>h ?D \<sigma>" using body by fastforce
      then show ?thesis by simp
    qed
    text \<open>Safety pins each clause variable to a body atom, whose derivable instance has only
      universe constants --- so \<open>\<sigma>\<close> already maps the clause variables into \<open>U\<close>.\<close>
    have subst_cond: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> U"
    proof
      fix x assume x: "x \<in> set (cls_vars cl)"
      from safe cl x obtain a where a: "a \<in> set (cls_body_atoms cl)"
        and xa: "x \<in> set (concat (map id_vars_list (snd a)))"
        unfolding dl_safe_def by blast
      from xa obtain i where i: "i \<in> set (snd a)" and xi: "x \<in> set (id_vars_list i)"
        by auto
      have i_eq: "i = id.Var x" using xi by (cases i) auto
      have "set (\<lbrakk>snd a\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>) \<subseteq> U"
        using derivable_consts[OF body_der[OF a]] by simp
      moreover have "\<sigma> x \<in> set (\<lbrakk>snd a\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
        using i i_eq by force
      ultimately show "\<sigma> x \<in> U" by blast
    qed
    have guards: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
    proof
      fix g assume g: "g \<in> set (cls_guards cl)"
      then have g_rhs: "g \<in> set rhs" using cl_eq unfolding cls_guards_def by simp
      show "eval_guard \<sigma> g"
      proof (cases g)
        case (Eql a b)
        then show ?thesis using body g_rhs by (fastforce simp: subst_id_eval_id)
      next
        case (Neql a b)
        then show ?thesis using body g_rhs by (fastforce simp: subst_id_eval_id)
      qed simp_all
    qed
    have body': "\<forall>a \<in> set (cls_body_atoms cl). derivable (subst_atom \<sigma> a)"
    proof
      fix a assume a: "a \<in> set (cls_body_atoms cl)"
      have "subst_atom \<sigma> a = (fst a, \<lbrakk>snd a\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
        unfolding subst_atom_def by (simp add: subst_id_eval_id)
      then show "derivable (subst_atom \<sigma> a)" using body_der[OF a] by simp
    qed
    have "derivable (subst_atom \<sigma> (the_lh cl))"
      using derivable.derive[OF cl subst_cond guards body'] by blast
    then show ?thesis
      using cl_eq by (simp add: subst_atom_def subst_id_eval_id)
  qed
  then show "\<lbrakk>cl\<rbrakk>\<^sub>c\<^sub>l\<^sub>s ?D \<sigma>"
    unfolding cl_eq meaning_cls.simps by blast
qed

end

subsection \<open>Positive datalog over a universe (the combined locale)\<close>

text \<open>The two halves combined: a \<^locale>\<open>positive_datalog\<close> program \<open>P\<close> that is also a
  \<^locale>\<open>datalog_universe\<close> (safe, head-covered, over \<open>U\<close>). As a sublocale of
  \<^locale>\<open>positive_datalog\<close> it inherits the relation to stratified datalog, and under all the side
  conditions the \<open>U\<close>-restricted \<open>derivable\<close> is exactly the stratified-datalog least solution of
  \<open>P\<close>. Instantiate with any concrete \<open>U\<close>/\<open>P\<close>.\<close>

locale positive_datalog_universe = datalog_universe U P + positive_datalog P
  for U :: "'c set" and P :: "('p, 'x, 'c) dl_program"
begin

text \<open>\<^bold>\<open>Soundness\<close>: every derivable fact is in every AFP solution of \<open>P\<close> (positivity needed).\<close>
lemma derivable_in_solution:            
  assumes sol: "\<rho> \<Turnstile>\<^sub>d\<^sub>l P" and der: "derivable f"
  shows "snd f \<in> \<rho> (fst f)"
  using der
proof (induction rule: derivable.induct)
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
      using positive derive.hyps(1) rh cl_eq unfolding dl_positive_prog_def by fastforce
    then show ?thesis ..
  qed
  then have rhs_sat: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>" by simp
  have "\<lbrakk>cl\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    using sol derive.hyps(1) unfolding solves_program_def solves_cls_def by blast
  then have "\<lbrakk>(q, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
    using rhs_sat unfolding cl_eq meaning_cls.simps by blast
  then show ?case using cl_eq by (simp add: subst_atom_def subst_id_eval_id)
qed

text \<open>\<^bold>\<open>The equivalence\<close>: \<open>derivable\<close> coincides with the (rank-0) least solution of \<open>P\<close>.\<close>
lemma derivable_iff_least_solution:
  assumes lst: "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t P (\<lambda>_. 0)"
  shows "derivable (p, r) \<longleftrightarrow> r \<in> \<rho> p"
proof
  assume "derivable (p, r)"
  moreover have "\<rho> \<Turnstile>\<^sub>d\<^sub>l P"
    using lst unfolding least_solution_def by blast
  ultimately show "r \<in> \<rho> p"
    using derivable_in_solution by fastforce
next
  assume r: "r \<in> \<rho> p"
  have D_sol: "(\<lambda>q. {r. derivable (q, r)}) \<Turnstile>\<^sub>d\<^sub>l P"
    using derivable_solves .
  with lst have "lte \<rho> (\<lambda>_. 0) (\<lambda>q. {r. derivable (q, r)})"
    unfolding least_solution_def by blast
  then have "\<rho> p \<subseteq> {r. derivable (p, r)}"
    unfolding lte_def lt_def by auto
  with r show "derivable (p, r)" by blast
qed

end

end
