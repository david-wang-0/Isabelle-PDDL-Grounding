theory Datalog_Certificate_Code_Index
  imports Fact_Index
begin

section \<open>Indexed, order-independent executable datalog rule-validity check\<close>

text \<open>Executable code layer for the order-independent rule validity
  \<^const>\<open>dl_rule_valid_oi\<close> (defined in \<^theory>\<open>Datalog_Certification.Datalog_Certificate_Code\<close>): a
  fact/rule split with the fact-side lookup through \<^theory>\<open>Datalog_Certification.Fact_Index\<close> and an
  order-independent body match (the fact-driven \<^const>\<open>body_join\<close> + an explicit set-equality check),
  proved \<^emph>\<open>equal\<close> to \<^const>\<open>dl_rule_valid_oi\<close> and installed as its \<open>[code]\<close> equation. This closes the
  chain \<open>dl_rule_valid_exec_idx (mk_rulevalid_index Pl) Ul r = dl_rule_valid_oi Pl Ul r
  = dl_rule_valid (set Pl) (set Ul) r\<close>, so the admissibility checks (which call
  \<^const>\<open>dl_rule_valid_oi\<close>) execute through the index and stay order-independent.\<close>

subsection \<open>Per-clause phrasing of order-independent rule validity\<close>

definition clause_oi :: "'c list \<Rightarrow> ('p, 'c) dl_ground_rule \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> bool" where
  "clause_oi Ul r cl \<equiv>
     (\<exists>\<sigma>. (\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul)
        \<and> (\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
        \<and> gr_head r = subst_atom \<sigma> (the_lh cl)
        \<and> set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl)))"

lemma dl_rule_valid_oi_clause: "dl_rule_valid_oi Pl Ul r = (\<exists>cl \<in> set Pl. clause_oi Ul r cl)"
  unfolding dl_rule_valid_oi_def clause_oi_def by (rule refl)

subsection \<open>Layer 3: the executable indexed checker\<close>

text \<open>A clause is a \<^emph>\<open>pure ground fact clause\<close> when its whole right-hand side is empty and every
  head id is a constant: then its (unique, \<open>\<sigma>\<close>-independent) ground head atom determines it.\<close>
definition is_ground_fact_cls :: "('p, 'x, 'c) clause \<Rightarrow> bool" where
  "is_ground_fact_cls cl \<longleftrightarrow>
     the_rhs cl = [] \<and> list_all (\<lambda>i. id_vars_list i = []) (snd (the_lh cl))"

text \<open>The ground head atom of a pure ground fact clause (any \<open>\<sigma>\<close>; only constants occur).\<close>
definition gfc_atom :: "('p, 'x, 'c) clause \<Rightarrow> ('p, 'c) dl_fact" where
  "gfc_atom cl = subst_atom (\<lambda>_. undefined) (the_lh cl)"

text \<open>The split index: per-argument fact index and predicate-bucket fact index over the ground-fact
  atoms of \<open>Pl\<close> (fact case); the empty-body-but-not-pure-ground clauses (fact fallback); and the
  clauses with a non-empty body (rule case).\<close>
datatype ('p, 'x, 'c) rvindex = RVIndex
  (rvi_a: "('p, 'c) afidx")
  (rvi_p: "('p, 'c) pfidx")
  (rvi_other: "('p, 'x, 'c) clause list")
  (rvi_rules: "('p, 'x, 'c) clause list")

definition mk_rulevalid_index ::
    "('p::linorder, 'x, 'c::linorder) clause list \<Rightarrow> ('p, 'x, 'c) rvindex" where
  "mk_rulevalid_index Pl =
     (let atoms = map gfc_atom (filter is_ground_fact_cls Pl)
      in RVIndex (build_aidx atoms) (build_pidx atoms)
           (filter (\<lambda>cl. cls_body_atoms cl = [] \<and> \<not> is_ground_fact_cls cl) Pl)
           (filter (\<lambda>cl. cls_body_atoms cl \<noteq> []) Pl))"

text \<open>Exact per-clause decision: for a \<^emph>\<open>safe\<close> clause a fact-driven, order-independent join over the
  rule body (\<^const>\<open>body_join\<close>, reuse allowed) followed by an explicit head-equality and body
  \<^emph>\<open>set\<close>-equality check; otherwise the full \<^const>\<open>cls_substs\<close> enumeration. In both branches the
  four abstract conjuncts are checked, so the decision is exact (see \<open>clause_ok_iff\<close>).\<close>
definition clause_ok :: "'c list \<Rightarrow> ('p, 'c) dl_ground_rule \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> bool" where
  "clause_ok Ul r cl =
     (if clause_safe_exec cl
      then list_ex (\<lambda>al.
             list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set Ul | None \<Rightarrow> False) (cls_vars cl)
             \<and> list_all (eval_guard_al al) (cls_guards cl)
             \<and> subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl) = gr_head r
             \<and> set (map (subst_atom (\<lambda>x. the (map_of al x))) (cls_body_atoms cl)) = set (gr_body r))
           (body_join [] (cls_body_atoms cl) (gr_body r))
      else list_ex (\<lambda>\<sigma>.
             list_all (\<lambda>g. eval_guard \<sigma> g) (cls_guards cl)
             \<and> subst_atom \<sigma> (the_lh cl) = gr_head r
             \<and> set (map (subst_atom \<sigma>) (cls_body_atoms cl)) = set (gr_body r))
           (cls_substs Ul cl))"

text \<open>The indexed checker: fact case (\<open>gr_body r = []\<close>) --- accept if the ground head atom is in the
  per-argument (or, for a nullary head, predicate-bucket) fact index, or some fallback empty-body
  clause matches; rule case --- some non-empty-body clause matches.\<close>
definition dl_rule_valid_exec_idx ::
    "('p::linorder, 'x, 'c::linorder) rvindex \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_ground_rule \<Rightarrow> bool" where
  "dl_rule_valid_exec_idx idx Ul r =
     (if gr_body r = []
      then list_ex (\<lambda>f. f = gr_head r)
             (if snd (gr_head r) = []
              then plookup (rvi_p idx) (fst (gr_head r))
              else alookup (rvi_a idx) (fst (gr_head r)) 0 (snd (gr_head r) ! 0))
           \<or> list_ex (clause_ok Ul r) (rvi_other idx)
      else list_ex (clause_ok Ul r) (rvi_rules idx))"

subsection \<open>Ground-fact-clause facts\<close>

lemma ground_fact_body: "is_ground_fact_cls cl \<Longrightarrow> cls_body_atoms cl = []"
  by (simp add: cls_body_atoms_def is_ground_fact_cls_def List.map_filter_simps)

lemma ground_fact_guards: "is_ground_fact_cls cl \<Longrightarrow> cls_guards cl = []"
  by (simp add: cls_guards_def is_ground_fact_cls_def)

lemma ground_fact_head_no_vars:
  "is_ground_fact_cls cl \<Longrightarrow> i \<in> set (snd (the_lh cl)) \<Longrightarrow> id_vars_list i = []"
  by (simp add: is_ground_fact_cls_def list_all_iff)

lemma ground_fact_vars: "is_ground_fact_cls cl \<Longrightarrow> cls_vars cl = []"
  by (cases cl) (auto simp: is_ground_fact_cls_def list_all_iff)

lemma gfc_atom_subst: "is_ground_fact_cls cl \<Longrightarrow> subst_atom \<sigma> (the_lh cl) = gfc_atom cl"
  unfolding gfc_atom_def by (intro subst_atom_agree ballI) (simp add: ground_fact_head_no_vars)

lemma ground_fact_clause_oi:
  assumes "is_ground_fact_cls cl" and "gfc_atom cl = gr_head r" and "gr_body r = []"
  shows "clause_oi Ul r cl"
  unfolding clause_oi_def
  using assms by (auto simp: ground_fact_vars ground_fact_guards ground_fact_body gfc_atom_subst)

lemma ground_fact_clause_oi_head:
  assumes "is_ground_fact_cls cl" and "clause_oi Ul r cl"
  shows "gfc_atom cl = gr_head r"
  using assms unfolding clause_oi_def by (auto simp: gfc_atom_subst)

lemma clause_oi_body_empty:
  assumes "clause_oi Ul r cl"
  shows "(cls_body_atoms cl = []) = (gr_body r = [])"
  using assms unfolding clause_oi_def by auto

subsection \<open>Per-clause exactness of \<open>clause_ok\<close>\<close>

lemma clause_ok_iff: "clause_ok Ul r cl = clause_oi Ul r cl"
proof
  assume ok: "clause_ok Ul r cl"
  show "clause_oi Ul r cl"
  proof (cases "clause_safe_exec cl")
    case True
    then obtain al where
      alin: "al \<in> set (body_join [] (cls_body_atoms cl) (gr_body r))" and
      U: "list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set Ul | None \<Rightarrow> False) (cls_vars cl)" and
      G: "list_all (eval_guard_al al) (cls_guards cl)" and
      H: "subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl) = gr_head r" and
      B: "set (map (subst_atom (\<lambda>x. the (map_of al x))) (cls_body_atoms cl)) = set (gr_body r)"
      using ok unfolding clause_ok_def by (auto simp: list_ex_iff)
    define \<sigma> where "\<sigma> = (\<lambda>x. the (map_of al x))"
    have "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul"
      using U by (auto simp: list_all_iff \<sigma>_def split: option.splits)
    moreover have "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
      using G by (auto simp: list_all_iff eval_guard_al_eq \<sigma>_def)
    moreover have "gr_head r = subst_atom \<sigma> (the_lh cl)" using H by (simp add: \<sigma>_def)
    moreover have "set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl))"
      using B by (simp add: \<sigma>_def)
    ultimately show ?thesis unfolding clause_oi_def by blast
  next
    case False
    then obtain \<sigma> where
      \<sigma>in: "\<sigma> \<in> set (cls_substs Ul cl)" and
      G: "list_all (\<lambda>g. eval_guard \<sigma> g) (cls_guards cl)" and
      H: "subst_atom \<sigma> (the_lh cl) = gr_head r" and
      B: "set (map (subst_atom \<sigma>) (cls_body_atoms cl)) = set (gr_body r)"
      using ok unfolding clause_ok_def by (auto simp: list_ex_iff)
    have "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul" using cls_substs_rangeD[OF \<sigma>in] by blast
    moreover have "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g" using G by (simp add: list_all_iff)
    ultimately show ?thesis using H B unfolding clause_oi_def by metis
  qed
next
  assume "clause_oi Ul r cl"
  then obtain \<sigma> where
    rng: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul" and
    gsig: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g" and
    hsig: "gr_head r = subst_atom \<sigma> (the_lh cl)" and
    bsig: "set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl))"
    unfolding clause_oi_def by blast
  show "clause_ok Ul r cl"
  proof (cases "clause_safe_exec cl")
    case True
    have bin: "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set (gr_body r)"
      using bsig by auto
    have empty_cons: "\<forall>x d. map_of [] x = Some d \<longrightarrow> \<sigma> x = d" by simp
    obtain al where alin: "al \<in> set (body_join [] (cls_body_atoms cl) (gr_body r))"
      and albind: "\<forall>a \<in> set (cls_body_atoms cl).
                     \<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x)"
      using body_join_complete[OF bin empty_cons] by auto
    have safe: "\<forall>x \<in> set (cls_vars cl).
                  \<exists>a \<in> set (cls_body_atoms cl). x \<in> set (concat (map id_vars_list (snd a)))"
      using True unfolding clause_safe_exec_def by (simp add: list_all_iff list_ex_iff)
    have agall: "\<forall>x \<in> set (cls_vars cl). map_of al x = Some (\<sigma> x)"
    proof
      fix x assume x: "x \<in> set (cls_vars cl)"
      then obtain a where a: "a \<in> set (cls_body_atoms cl)"
        and xa: "x \<in> set (concat (map id_vars_list (snd a)))" using safe by blast
      show "map_of al x = Some (\<sigma> x)" using albind a xa by blast
    qed
    have ag: "\<forall>x \<in> set (cls_vars cl). (\<lambda>x. the (map_of al x)) x = \<sigma> x" using agall by simp
    have U: "list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set Ul | None \<Rightarrow> False) (cls_vars cl)"
      unfolding list_all_iff
    proof
      fix x assume x: "x \<in> set (cls_vars cl)"
      have "map_of al x = Some (\<sigma> x)" using agall x by blast
      then show "case map_of al x of Some c \<Rightarrow> c \<in> set Ul | None \<Rightarrow> False" using rng x by simp
    qed
    have Gd: "list_all (eval_guard_al al) (cls_guards cl)"
      unfolding list_all_iff
    proof
      fix g assume g: "g \<in> set (cls_guards cl)"
      have "eval_guard_al al g = eval_guard \<sigma> g"
        by (simp add: eval_guard_al_eq eval_guard_cls_cong[OF ag g])
      then show "eval_guard_al al g" using gsig g by simp
    qed
    have Hd: "subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl) = gr_head r"
      using subst_atom_head_cong[OF ag] hsig by simp
    have Bd: "set (map (subst_atom (\<lambda>x. the (map_of al x))) (cls_body_atoms cl)) = set (gr_body r)"
    proof -
      have "map (subst_atom (\<lambda>x. the (map_of al x))) (cls_body_atoms cl)
              = map (subst_atom \<sigma>) (cls_body_atoms cl)"
        by (intro map_cong[OF refl] subst_atom_body_cong[OF ag])
      then show ?thesis using bsig by simp
    qed
    show ?thesis unfolding clause_ok_def
      using True alin U Gd Hd Bd by (auto simp: list_ex_iff)
  next
    case False
    obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> set (cls_substs Ul cl)"
      and ag: "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
      using cls_substs_tabulate[OF rng] by blast
    have Gd: "list_all (\<lambda>g. eval_guard \<sigma>' g) (cls_guards cl)"
      unfolding list_all_iff using gsig eval_guard_cls_cong[OF ag] by auto
    have Hd: "subst_atom \<sigma>' (the_lh cl) = gr_head r"
      using subst_atom_head_cong[OF ag] hsig by simp
    have Bd: "set (map (subst_atom \<sigma>') (cls_body_atoms cl)) = set (gr_body r)"
    proof -
      have "map (subst_atom \<sigma>') (cls_body_atoms cl) = map (subst_atom \<sigma>) (cls_body_atoms cl)"
        by (intro map_cong[OF refl] subst_atom_body_cong[OF ag])
      then show ?thesis using bsig by simp
    qed
    show ?thesis unfolding clause_ok_def
      using False \<sigma>' Gd Hd Bd by (auto simp: list_ex_iff)
  qed
qed

subsection \<open>Fact-index soundness and completeness\<close>

lemma fact_index_iff:
  fixes Pl :: "('p::linorder, 'x, 'c::linorder) clause list"
  shows "list_ex (\<lambda>f. f = gr_head r)
           (if snd (gr_head r) = []
            then plookup (build_pidx (map gfc_atom (filter is_ground_fact_cls Pl))) (fst (gr_head r))
            else alookup (build_aidx (map gfc_atom (filter is_ground_fact_cls Pl)))
                   (fst (gr_head r)) 0 (snd (gr_head r) ! 0))
         = (\<exists>cl \<in> set Pl. is_ground_fact_cls cl \<and> gfc_atom cl = gr_head r)"
    (is "?L = ?R")
proof -
  let ?atoms = "map gfc_atom (filter is_ground_fact_cls Pl)"
  have mem: "?L = (gr_head r \<in> set ?atoms)"
  proof (cases "snd (gr_head r) = []")
    case True
    have "?L = (gr_head r \<in> set (plookup (build_pidx ?atoms) (fst (gr_head r))))"
      using True by (simp add: list_ex_iff)
    also have "\<dots> = (gr_head r \<in> set ?atoms)"
      using plookup_build_sound[of ?atoms "fst (gr_head r)"]
            plookup_build_complete[of "gr_head r" ?atoms] by auto
    finally show ?thesis .
  next
    case False
    have "?L = (gr_head r \<in> set (alookup (build_aidx ?atoms) (fst (gr_head r)) 0 (snd (gr_head r) ! 0)))"
      using False by (simp add: list_ex_iff)
    also have "\<dots> = (gr_head r \<in> set ?atoms)"
      using alookup_build_sound[of ?atoms "fst (gr_head r)" 0 "snd (gr_head r) ! 0"]
            alookup_build_complete[of "gr_head r" ?atoms 0] False by auto
    finally show ?thesis .
  qed
  have "(gr_head r \<in> set ?atoms) = ?R" by (auto simp: image_iff)
  with mem show ?thesis by simp
qed

subsection \<open>Layer 3 = Layer 2, and the code equation\<close>

theorem dl_rule_valid_exec_idx_eq:
  "dl_rule_valid_exec_idx (mk_rulevalid_index Pl) Ul r = dl_rule_valid_oi Pl Ul r"
proof -
  have oi: "dl_rule_valid_oi Pl Ul r = (\<exists>cl \<in> set Pl. clause_oi Ul r cl)"
    by (rule dl_rule_valid_oi_clause)
  have "dl_rule_valid_exec_idx (mk_rulevalid_index Pl) Ul r = (\<exists>cl \<in> set Pl. clause_oi Ul r cl)"
  proof (cases "gr_body r = []")
    case True
    let ?exec = "dl_rule_valid_exec_idx (mk_rulevalid_index Pl) Ul r"
    have exec_eq: "?exec = ((\<exists>cl \<in> set Pl. is_ground_fact_cls cl \<and> gfc_atom cl = gr_head r)
        \<or> (\<exists>cl \<in> set Pl. cls_body_atoms cl = [] \<and> \<not> is_ground_fact_cls cl \<and> clause_oi Ul r cl))"
    proof -
      have "?exec = (list_ex (\<lambda>f. f = gr_head r)
              (if snd (gr_head r) = []
               then plookup (build_pidx (map gfc_atom (filter is_ground_fact_cls Pl))) (fst (gr_head r))
               else alookup (build_aidx (map gfc_atom (filter is_ground_fact_cls Pl)))
                      (fst (gr_head r)) 0 (snd (gr_head r) ! 0))
             \<or> list_ex (clause_ok Ul r)
                 (filter (\<lambda>cl. cls_body_atoms cl = [] \<and> \<not> is_ground_fact_cls cl) Pl))"
        unfolding dl_rule_valid_exec_idx_def mk_rulevalid_index_def Let_def rvindex.sel
        by (simp only: if_P[OF True])
      also have "\<dots> = ((\<exists>cl \<in> set Pl. is_ground_fact_cls cl \<and> gfc_atom cl = gr_head r)
        \<or> (\<exists>cl \<in> set Pl. cls_body_atoms cl = [] \<and> \<not> is_ground_fact_cls cl \<and> clause_oi Ul r cl))"
        unfolding fact_index_iff by (auto simp: list_ex_iff clause_ok_iff set_filter)
      finally show ?thesis .
    qed
    show "?exec = (\<exists>cl \<in> set Pl. clause_oi Ul r cl)"
    proof
      assume ?exec
      then consider
          (a) cl where "cl \<in> set Pl" "is_ground_fact_cls cl" "gfc_atom cl = gr_head r"
        | (b) cl where "cl \<in> set Pl" "cls_body_atoms cl = []" "\<not> is_ground_fact_cls cl"
                       "clause_oi Ul r cl"
        using exec_eq by blast
      then show "\<exists>cl \<in> set Pl. clause_oi Ul r cl"
      proof cases
        case a
        then have "clause_oi Ul r cl" using ground_fact_clause_oi[OF a(2) a(3) True] by simp
        then show ?thesis using a(1) by blast
      next
        case b then show ?thesis by blast
      qed
    next
      assume "\<exists>cl \<in> set Pl. clause_oi Ul r cl"
      then obtain cl where cl: "cl \<in> set Pl" and oi: "clause_oi Ul r cl" by blast
      have body: "cls_body_atoms cl = []" using clause_oi_body_empty[OF oi] True by simp
      show ?exec
      proof (cases "is_ground_fact_cls cl")
        case True
        have "gfc_atom cl = gr_head r" using ground_fact_clause_oi_head[OF True oi] .
        then have "\<exists>cl \<in> set Pl. is_ground_fact_cls cl \<and> gfc_atom cl = gr_head r"
          using cl True by blast
        then show ?thesis using exec_eq by blast
      next
        case False
        then have "\<exists>cl \<in> set Pl. cls_body_atoms cl = [] \<and> \<not> is_ground_fact_cls cl \<and> clause_oi Ul r cl"
          using cl body oi by blast
        then show ?thesis using exec_eq by blast
      qed
    qed
  next
    case False
    have "dl_rule_valid_exec_idx (mk_rulevalid_index Pl) Ul r
          = list_ex (clause_ok Ul r) (filter (\<lambda>cl. cls_body_atoms cl \<noteq> []) Pl)"
      using False by (simp add: dl_rule_valid_exec_idx_def mk_rulevalid_index_def Let_def)
    also have "\<dots> = (\<exists>cl \<in> set Pl. cls_body_atoms cl \<noteq> [] \<and> clause_oi Ul r cl)"
      by (auto simp: list_ex_iff clause_ok_iff set_filter)
    also have "\<dots> = (\<exists>cl \<in> set Pl. clause_oi Ul r cl)"
    proof -
      have "cls_body_atoms cl \<noteq> []" if "clause_oi Ul r cl" for cl
        using clause_oi_body_empty[OF that] False by simp
      then show ?thesis by blast
    qed
    finally show ?thesis .
  qed
  with oi show ?thesis by simp
qed

text \<open>Code equation: \<^const>\<open>dl_rule_valid_oi\<close> executes through the indexed checker.\<close>
lemma dl_rule_valid_oi_code [code]:
  "dl_rule_valid_oi Pl Ul r = dl_rule_valid_exec_idx (mk_rulevalid_index Pl) Ul r"
  by (rule dl_rule_valid_exec_idx_eq [symmetric])

text \<open>The full soundness/completeness chain to the abstract set-based check.\<close>
corollary dl_rule_valid_exec_idx_correct:
  "dl_rule_valid_exec_idx (mk_rulevalid_index Pl) Ul r = dl_rule_valid (set Pl) (set Ul) r"
  unfolding dl_rule_valid_exec_idx_eq dl_rule_valid_oi_eq by (rule refl)

end
