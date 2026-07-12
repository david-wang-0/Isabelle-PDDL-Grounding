theory Datalog_Certificate_Index
  imports Datalog_Cycle_DFS "HOL-Data_Structures.RBT_Map"
begin

text \<open>\<^theory>\<open>HOL-Data_Structures.RBT_Map\<close> re-exports its own \<open>AList_Upd_Del.map_of\<close>, which would
  shadow \<open>Map.map_of\<close> --- the association-list lookup the datalog matcher threads. Keep the short
  name \<open>map_of\<close> resolving to \<^const>\<open>Map.map_of\<close>.\<close>
hide_const (open) AList_Upd_Del.map_of

text \<open>Fast [code] refinements of the certificate-check hot paths (join reorder + RBT
  per-argument index for the closure check; one-pass acyclicity), sited here because the
  graph layer (session \<open>Datalog_Graph\<close>) already carries RBT, which the Collections-free
  \<open>Datalog_Certification\<close> session deliberately does not. WORK IN PROGRESS.\<close>

subsection \<open>Index key: (predicate, argument position, value), lexicographically ordered\<close>

text \<open>The per-argument fact index is an \<^theory>\<open>HOL-Data_Structures.RBT_Map\<close> keyed by
  \<^emph>\<open>(predicate, position, value)\<close>. RBT keys must be a \<^class>\<open>linorder\<close>; since
  \<open>HOL-Library.Product_Lexorder\<close> is not reachable on this heap (and would risk a prod-order clash
  with the graph library), we wrap the triple in a datatype and give it the lexicographic order
  directly.\<close>

datatype ('p, 'c) ikey = IKey (ik_pred: 'p) (ik_pos: nat) (ik_val: 'c)

instantiation ikey :: (linorder, linorder) linorder
begin

definition less_eq_ikey :: "('a, 'b) ikey \<Rightarrow> ('a, 'b) ikey \<Rightarrow> bool" where
  "less_eq_ikey k1 k2 \<longleftrightarrow>
     ik_pred k1 < ik_pred k2 \<or>
     (ik_pred k1 = ik_pred k2 \<and>
        (ik_pos k1 < ik_pos k2 \<or>
           (ik_pos k1 = ik_pos k2 \<and> ik_val k1 \<le> ik_val k2)))"

definition less_ikey :: "('a, 'b) ikey \<Rightarrow> ('a, 'b) ikey \<Rightarrow> bool" where
  "less_ikey k1 k2 \<longleftrightarrow>
     ik_pred k1 < ik_pred k2 \<or>
     (ik_pred k1 = ik_pred k2 \<and>
        (ik_pos k1 < ik_pos k2 \<or>
           (ik_pos k1 = ik_pos k2 \<and> ik_val k1 < ik_val k2)))"

instance
proof
  fix x y z :: "('a, 'b) ikey"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (auto simp: less_eq_ikey_def less_ikey_def)
  show "x \<le> x" by (simp add: less_eq_ikey_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (auto simp: less_eq_ikey_def dest: less_trans le_less_trans less_le_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp: less_eq_ikey_def ikey.expand)
  show "x \<le> y \<or> y \<le> x"
    by (auto simp: less_eq_ikey_def)
qed

end


subsection \<open>Predicate-bucket fact index (used to seed the join)\<close>

text \<open>A first, coarse index: predicate \<mapsto> all facts of that predicate. Used for a body atom whose
  arguments are all still unbound under the current partial assignment (the join's seed atom),
  where the per-argument index below has no bound position to narrow on.\<close>

type_synonym ('p, 'c) pfidx = "('p \<times> ('p, 'c) dl_fact list) rbt"

definition plookup :: "('p::linorder, 'c) pfidx \<Rightarrow> 'p \<Rightarrow> ('p, 'c) dl_fact list" where
  "plookup idx p = (case Lookup2.lookup idx p of Some fs \<Rightarrow> fs | None \<Rightarrow> [])"

definition pins :: "('p, 'c) dl_fact \<Rightarrow> ('p::linorder, 'c) pfidx \<Rightarrow> ('p, 'c) pfidx" where
  "pins f idx = RBT_Map.update (fst f) (f # plookup idx (fst f)) idx"

definition build_pidx :: "('p::linorder, 'c) dl_fact list \<Rightarrow> ('p, 'c) pfidx" where
  "build_pidx facts = fold pins facts RBT_Set.empty"

lemma pins_invar: "M.invar idx \<Longrightarrow> M.invar (pins f idx)"
  by (simp add: pins_def M.invar_update)

lemma fold_pins_invar: "M.invar idx \<Longrightarrow> M.invar (fold pins facts idx)"
  by (induct facts arbitrary: idx) (auto simp: pins_invar)

lemma plookup_pins:
  "M.invar idx \<Longrightarrow>
     plookup (pins g idx) p = (if p = fst g then g # plookup idx (fst g) else plookup idx p)"
  by (simp add: plookup_def pins_def M.map_update)

lemma plookup_pins_mono:
  "M.invar idx \<Longrightarrow> set (plookup idx p) \<subseteq> set (plookup (pins g idx) p)"
  by (auto simp: plookup_pins)

lemma plookup_fold_pins_mono:
  "M.invar idx \<Longrightarrow> set (plookup idx p) \<subseteq> set (plookup (fold pins facts idx) p)"
proof (induct facts arbitrary: idx)
  case Nil then show ?case by simp
next
  case (Cons g facts)
  have "set (plookup idx p) \<subseteq> set (plookup (pins g idx) p)"
    using plookup_pins_mono[OF Cons.prems] .
  also have "\<dots> \<subseteq> set (plookup (fold pins facts (pins g idx)) p)"
    using Cons.hyps[OF pins_invar[OF Cons.prems]] .
  finally show ?case by simp
qed

lemma plookup_fold_pins_sound:
  "M.invar idx \<Longrightarrow> set (plookup (fold pins facts idx) p) \<subseteq> set (plookup idx p) \<union> set facts"
proof (induct facts arbitrary: idx p)
  case Nil then show ?case by simp
next
  case (Cons g facts)
  have "set (plookup (fold pins facts (pins g idx)) p) \<subseteq> set (plookup (pins g idx) p) \<union> set facts"
    using Cons.hyps[OF pins_invar[OF Cons.prems]] .
  moreover have "set (plookup (pins g idx) p) \<subseteq> set (plookup idx p) \<union> {g}"
    using Cons.prems by (auto simp: plookup_pins split: if_splits)
  ultimately show ?case by auto
qed

lemma plookup_build_sound: "set (plookup (build_pidx facts) p) \<subseteq> set facts"
  using plookup_fold_pins_sound[OF M.invar_empty, of facts p]
  by (simp add: build_pidx_def plookup_def M.map_empty)

lemma plookup_fold_pins_complete:
  "M.invar idx \<Longrightarrow> f \<in> set facts \<Longrightarrow> f \<in> set (plookup (fold pins facts idx) (fst f))"
proof (induct facts arbitrary: idx)
  case Nil then show ?case by simp
next
  case (Cons g facts)
  show ?case
  proof (cases "f \<in> set facts")
    case True
    then show ?thesis using Cons.hyps[OF pins_invar[OF Cons.prems(1)]] by simp
  next
    case False
    then have fg: "f = g" using Cons.prems(2) by simp
    have "f \<in> set (plookup (pins g idx) (fst f))"
      using Cons.prems(1) fg by (simp add: plookup_pins)
    then have "f \<in> set (plookup (fold pins facts (pins g idx)) (fst f))"
      using plookup_fold_pins_mono[OF pins_invar[OF Cons.prems(1)]] by blast
    then show ?thesis by simp
  qed
qed

lemma plookup_build_complete: "f \<in> set facts \<Longrightarrow> f \<in> set (plookup (build_pidx facts) (fst f))"
  using plookup_fold_pins_complete[OF M.invar_empty] by (simp add: build_pidx_def)

subsection \<open>Per-argument-position fact index\<close>

text \<open>The fine index: (predicate, position, value) \<mapsto> all facts carrying that value at that
  position. Used to narrow the candidate facts for a body atom that already has a bound argument
  under the current partial assignment (the essential per-argument bound-value index).\<close>

type_synonym ('p, 'c) afidx = "(('p, 'c) ikey \<times> ('p, 'c) dl_fact list) rbt"

definition alookup :: "('p::linorder, 'c::linorder) afidx \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> ('p, 'c) dl_fact list" where
  "alookup idx p j v = (case Lookup2.lookup idx (IKey p j v) of Some fs \<Rightarrow> fs | None \<Rightarrow> [])"

definition ains_pos :: "('p, 'c) dl_fact \<Rightarrow> nat \<Rightarrow> ('p::linorder, 'c::linorder) afidx \<Rightarrow> ('p, 'c) afidx" where
  "ains_pos f j idx =
     RBT_Map.update (IKey (fst f) j (snd f ! j)) (f # alookup idx (fst f) j (snd f ! j)) idx"

definition ains :: "('p, 'c) dl_fact \<Rightarrow> ('p::linorder, 'c::linorder) afidx \<Rightarrow> ('p, 'c) afidx" where
  "ains f idx = fold (ains_pos f) [0..<length (snd f)] idx"

definition build_aidx :: "('p::linorder, 'c::linorder) dl_fact list \<Rightarrow> ('p, 'c) afidx" where
  "build_aidx facts = fold ains facts RBT_Set.empty"

lemma ains_pos_invar: "M.invar idx \<Longrightarrow> M.invar (ains_pos f j idx)"
  by (simp add: ains_pos_def M.invar_update)

lemma fold_ains_pos_invar: "M.invar idx \<Longrightarrow> M.invar (fold (ains_pos f) js idx)"
  by (induct js arbitrary: idx) (auto simp: ains_pos_invar)

lemma ains_invar: "M.invar idx \<Longrightarrow> M.invar (ains f idx)"
  by (simp add: ains_def fold_ains_pos_invar)

lemma fold_ains_invar: "M.invar idx \<Longrightarrow> M.invar (fold ains facts idx)"
  by (induct facts arbitrary: idx) (auto simp: ains_invar)

lemma alookup_ains_pos:
  "M.invar idx \<Longrightarrow>
     alookup (ains_pos g j idx) p i v =
       (if IKey p i v = IKey (fst g) j (snd g ! j)
        then g # alookup idx (fst g) j (snd g ! j) else alookup idx p i v)"
  by (simp add: alookup_def ains_pos_def M.map_update)

lemma alookup_ains_pos_mono:
  "M.invar idx \<Longrightarrow> set (alookup idx p i v) \<subseteq> set (alookup (ains_pos g j idx) p i v)"
  by (auto simp: alookup_ains_pos)

lemma alookup_fold_ains_pos_mono:
  "M.invar idx \<Longrightarrow> set (alookup idx p i v) \<subseteq> set (alookup (fold (ains_pos g) js idx) p i v)"
proof (induct js arbitrary: idx)
  case Nil then show ?case by simp
next
  case (Cons k js)
  have "set (alookup idx p i v) \<subseteq> set (alookup (ains_pos g k idx) p i v)"
    using alookup_ains_pos_mono[OF Cons.prems] .
  also have "\<dots> \<subseteq> set (alookup (fold (ains_pos g) js (ains_pos g k idx)) p i v)"
    using Cons.hyps[OF ains_pos_invar[OF Cons.prems]] .
  finally show ?case by simp
qed

lemma alookup_ains_mono:
  "M.invar idx \<Longrightarrow> set (alookup idx p i v) \<subseteq> set (alookup (ains g idx) p i v)"
  by (simp add: ains_def alookup_fold_ains_pos_mono)

lemma alookup_fold_ains_mono:
  "M.invar idx \<Longrightarrow> set (alookup idx p i v) \<subseteq> set (alookup (fold ains facts idx) p i v)"
proof (induct facts arbitrary: idx)
  case Nil then show ?case by simp
next
  case (Cons g facts)
  have "set (alookup idx p i v) \<subseteq> set (alookup (ains g idx) p i v)"
    using alookup_ains_mono[OF Cons.prems] .
  also have "\<dots> \<subseteq> set (alookup (fold ains facts (ains g idx)) p i v)"
    using Cons.hyps[OF ains_invar[OF Cons.prems]] .
  finally show ?case by simp
qed

lemma alookup_fold_ains_pos_sub:
  "M.invar idx \<Longrightarrow> set (alookup (fold (ains_pos g) js idx) p i v) \<subseteq> set (alookup idx p i v) \<union> {g}"
proof (induct js arbitrary: idx)
  case Nil then show ?case by auto
next
  case (Cons k js)
  have "set (alookup (fold (ains_pos g) js (ains_pos g k idx)) p i v)
          \<subseteq> set (alookup (ains_pos g k idx) p i v) \<union> {g}"
    using Cons.hyps[OF ains_pos_invar[OF Cons.prems]] .
  moreover have "set (alookup (ains_pos g k idx) p i v) \<subseteq> set (alookup idx p i v) \<union> {g}"
    using Cons.prems by (auto simp: alookup_ains_pos split: if_splits)
  ultimately show ?case by auto
qed

lemma alookup_ains_sub:
  assumes "M.invar idx"
  shows "set (alookup (ains g idx) p i v) \<subseteq> set (alookup idx p i v) \<union> {g}"
  unfolding ains_def by (rule alookup_fold_ains_pos_sub[OF assms])

lemma alookup_fold_ains_sound:
  "M.invar idx \<Longrightarrow> set (alookup (fold ains facts idx) p i v) \<subseteq> set (alookup idx p i v) \<union> set facts"
proof (induct facts arbitrary: idx)
  case Nil then show ?case by simp
next
  case (Cons g facts)
  have "set (alookup (fold ains facts (ains g idx)) p i v)
          \<subseteq> set (alookup (ains g idx) p i v) \<union> set facts"
    using Cons.hyps[OF ains_invar[OF Cons.prems]] .
  moreover have "set (alookup (ains g idx) p i v) \<subseteq> set (alookup idx p i v) \<union> {g}"
    using alookup_ains_sub[OF Cons.prems] .
  ultimately show ?case by auto
qed

lemma alookup_build_sound: "set (alookup (build_aidx facts) p j v) \<subseteq> set facts"
  using alookup_fold_ains_sound[OF M.invar_empty, of facts p j v]
  by (simp add: build_aidx_def alookup_def M.map_empty)

lemma alookup_fold_ains_pos_hit:
  "M.invar idx \<Longrightarrow> j \<in> set js \<Longrightarrow> g \<in> set (alookup (fold (ains_pos g) js idx) (fst g) j (snd g ! j))"
proof (induct js arbitrary: idx)
  case Nil then show ?case by simp
next
  case (Cons k js)
  show ?case
  proof (cases "j \<in> set js")
    case True
    then show ?thesis using Cons.hyps[OF ains_pos_invar[OF Cons.prems(1)]] by simp
  next
    case False
    then have kj: "k = j" using Cons.prems(2) by simp
    have "g \<in> set (alookup (ains_pos g j idx) (fst g) j (snd g ! j))"
      using Cons.prems(1) by (simp add: alookup_ains_pos)
    then have "g \<in> set (alookup (fold (ains_pos g) js (ains_pos g j idx)) (fst g) j (snd g ! j))"
      using alookup_fold_ains_pos_mono[OF ains_pos_invar[OF Cons.prems(1)]] by blast
    then show ?thesis using kj by simp
  qed
qed

lemma alookup_ains_hit:
  assumes "M.invar idx" and "j < length (snd g)"
  shows "g \<in> set (alookup (ains g idx) (fst g) j (snd g ! j))"
proof -
  have "j \<in> set [0..<length (snd g)]" using assms(2) by simp
  from alookup_fold_ains_pos_hit[OF assms(1) this] show ?thesis
    by (simp add: ains_def)
qed

lemma alookup_fold_ains_complete:
  "M.invar idx \<Longrightarrow> f \<in> set facts \<Longrightarrow> j < length (snd f) \<Longrightarrow>
     f \<in> set (alookup (fold ains facts idx) (fst f) j (snd f ! j))"
proof (induct facts arbitrary: idx)
  case Nil then show ?case by simp
next
  case (Cons g facts)
  show ?case
  proof (cases "f \<in> set facts")
    case True
    then show ?thesis
      using Cons.hyps[OF ains_invar[OF Cons.prems(1)] _ Cons.prems(3)] by simp
  next
    case False
    then have fg: "f = g" using Cons.prems(2) by simp
    have "f \<in> set (alookup (ains g idx) (fst f) j (snd f ! j))"
      using alookup_ains_hit[OF Cons.prems(1), of j f] Cons.prems(3) fg by simp
    then have "f \<in> set (alookup (fold ains facts (ains g idx)) (fst f) j (snd f ! j))"
      using alookup_fold_ains_mono[OF ains_invar[OF Cons.prems(1)]] by blast
    then show ?thesis by simp
  qed
qed

lemma alookup_build_complete:
  "f \<in> set facts \<Longrightarrow> j < length (snd f) \<Longrightarrow> f \<in> set (alookup (build_aidx facts) (fst f) j (snd f ! j))"
  using alookup_fold_ains_complete[OF M.invar_empty] by (simp add: build_aidx_def)

subsection \<open>Index-backed candidate selection for one body atom\<close>

text \<open>Bundle both indices. For a body atom, if some argument is already determined under the
  current partial assignment @{term al} (a constant, or a variable bound in @{term al}), we fetch
  the narrow per-argument bucket for that (predicate, position, value); otherwise the atom is a
  seed and we fetch its whole predicate bucket. Either way the candidate list is a subset of the
  facts that still contains every fact that could match, so filtering it with @{const match_atom_al}
  yields exactly the same matches as scanning all facts.\<close>

datatype ('p, 'c) findex = FIndex (fx_p: "('p, 'c) pfidx") (fx_a: "('p, 'c) afidx")

definition build_findex :: "('p::linorder, 'c::linorder) dl_fact list \<Rightarrow> ('p, 'c) findex" where
  "build_findex facts = FIndex (build_pidx facts) (build_aidx facts)"

fun first_bound :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id list \<Rightarrow> (nat \<times> 'c) option" where
  "first_bound al [] = None"
| "first_bound al (i # is') =
     (case i of
        id.Cst c \<Rightarrow> Some (0, c)
      | id.Var x \<Rightarrow> (case map_of al x of
                      Some v \<Rightarrow> Some (0, v)
                    | None \<Rightarrow> map_option (\<lambda>(j, v). (Suc j, v)) (first_bound al is')))"

definition cand_facts ::
    "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p::linorder, 'c::linorder) findex \<Rightarrow> ('p, 'c) dl_fact list"
  where
  "cand_facts al a idx =
     (case first_bound al (snd a) of
        Some (j, v) \<Rightarrow> alookup (fx_a idx) (fst a) j v
      | None \<Rightarrow> plookup (fx_p idx) (fst a))"

definition match_facts_idx ::
    "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p::linorder, 'c::linorder) findex \<Rightarrow> ('x \<times> 'c) list list"
  where
  "match_facts_idx al a idx = List.map_filter (match_atom_al al a) (cand_facts al a idx)"

text \<open>Matching-layer facts (proof obligations for the equivalence below).\<close>

lemma match_id_al_mono:
  "match_id_al al i d = Some al' \<Longrightarrow> map_of al x = Some v \<Longrightarrow> map_of al' x = Some v"
  by (cases i) (auto split: option.splits if_splits)

lemma match_ids_al_len:
  "match_ids_al al ids ds = Some r \<Longrightarrow> length ids = length ds"
  by (induct al ids ds arbitrary: r rule: match_ids_al.induct) (auto split: option.splits)

lemma set_map_filter_eq: "set (List.map_filter g xs) = {y. \<exists>x \<in> set xs. g x = Some y}"
  by (induct xs) (auto split: option.splits)

text \<open>Generalised form of the forcing lemma: @{const first_bound} may be evaluated at a partial
  assignment @{term al0} smaller than the one @{const match_ids_al} threads, provided the latter
  extends it. This threads through the induction (each matched atom only grows the assignment).\<close>
lemma first_bound_match_gen:
  "first_bound al0 ids = Some (j, v) \<Longrightarrow> match_ids_al al ids ds = Some r \<Longrightarrow>
     (\<forall>z w. map_of al0 z = Some w \<longrightarrow> map_of al z = Some w) \<Longrightarrow> j < length ds \<and> ds ! j = v"
proof (induct ids arbitrary: al ds r j v)
  case Nil then show ?case by simp
next
  case (Cons i ids)
  from Cons.prems(2) obtain d ds' where ds: "ds = d # ds'" by (cases ds) auto
  from Cons.prems(2) ds obtain al' where mi: "match_id_al al i d = Some al'"
    and rec: "match_ids_al al' ids ds' = Some r" by (auto split: option.splits)
  have ext': "\<forall>z w. map_of al0 z = Some w \<longrightarrow> map_of al' z = Some w"
    using Cons.prems(3) match_id_al_mono[OF mi] by blast
  show ?case
  proof (cases i)
    case (Cst c)
    with Cons.prems(1) have jv: "j = 0" "v = c" by auto
    from mi Cst have "d = c" by (auto split: if_splits)
    with jv ds show ?thesis by simp
  next
    case (Var y)
    show ?thesis
    proof (cases "map_of al0 y")
      case (Some w)
      with Var Cons.prems(1) have jv: "j = 0" "v = w" by auto
      have "map_of al y = Some w" using Some Cons.prems(3) by blast
      with mi Var have "d = w" by (auto split: if_splits option.splits)
      with jv ds show ?thesis by simp
    next
      case None
      with Var Cons.prems(1) obtain j' where fb': "first_bound al0 ids = Some (j', v)"
        and jsuc: "j = Suc j'" by (auto split: option.splits prod.splits)
      from Cons.hyps[OF fb' rec ext'] show ?thesis using ds jsuc by simp
    qed
  qed
qed

text \<open>If @{const first_bound} reports position @{term j} determined to value @{term v}, then any
  fact whose arguments match at @{term al} carries @{term v} at position @{term j}.\<close>
lemma first_bound_match:
  "first_bound al ids = Some (j, v) \<Longrightarrow> match_ids_al al ids ds = Some r \<Longrightarrow> j < length ds \<and> ds ! j = v"
  using first_bound_match_gen[of al ids j v al ds r] by simp

text \<open>\<^bold>\<open>Lemma A\<close>: filtering the index-selected candidates yields exactly the matches of the
  full fact scan. The reorder/index refinement of the body join rests entirely on this.\<close>
lemma match_facts_idx_eq:
  "set (match_facts_idx al a (build_findex facts)) = set (match_facts_al al a facts)"
proof -
  let ?C = "cand_facts al a (build_findex facts)"
  have sub: "set ?C \<subseteq> set facts"
  proof (cases "first_bound al (snd a)")
    case None
    then show ?thesis by (simp add: cand_facts_def build_findex_def plookup_build_sound)
  next
    case (Some jv)
    obtain j v where "jv = (j, v)" by (cases jv)
    with Some show ?thesis by (simp add: cand_facts_def build_findex_def alookup_build_sound)
  qed
  have comp: "f \<in> set ?C" if f: "f \<in> set facts" and m: "match_atom_al al a f = Some y" for f y
  proof -
    from m have pa: "fst a = fst f" and mi: "match_ids_al al (snd a) (snd f) = Some y"
      by (auto simp: match_atom_al_def split: if_splits)
    show "f \<in> set ?C"
    proof (cases "first_bound al (snd a)")
      case None
      then have "?C = plookup (build_pidx facts) (fst a)"
        by (simp add: cand_facts_def build_findex_def)
      moreover have "f \<in> set (plookup (build_pidx facts) (fst f))"
        using plookup_build_complete[OF f] .
      ultimately show ?thesis using pa by simp
    next
      case (Some jv)
      obtain j v where jv: "jv = (j, v)" by (cases jv)
      with Some have fb: "first_bound al (snd a) = Some (j, v)" by simp
      then have C: "?C = alookup (build_aidx facts) (fst a) j v"
        by (simp add: cand_facts_def build_findex_def)
      from first_bound_match[OF fb mi] have jl: "j < length (snd f)" and vj: "snd f ! j = v"
        by simp_all
      have "f \<in> set (alookup (build_aidx facts) (fst f) j (snd f ! j))"
        using alookup_build_complete[OF f jl] .
      then show ?thesis using C pa vj by simp
    qed
  qed
  show ?thesis
    unfolding match_facts_idx_def match_facts_al_def set_map_filter_eq    using sub comp by blast
qed


subsection \<open>Index-backed body join and the fast closure check (code refinement)\<close>

text \<open>Replaying the fact-driven body join over the RBT index instead of a linear fact scan: at each
  body atom we look up only the candidate facts sharing a bound argument (or the predicate bucket for
  a seed atom). By @{thm match_facts_idx_eq} this visits the same set of matches, so the reindexed
  join enumerates exactly the same set of substitutions as @{const body_join}.\<close>

fun body_join_idx ::
    "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh list \<Rightarrow> ('p::linorder, 'c::linorder) findex \<Rightarrow> ('x \<times> 'c) list list"
  where
  "body_join_idx al [] idx = [al]"
| "body_join_idx al (a # as') idx =
     concat (map (\<lambda>al'. body_join_idx al' as' idx) (match_facts_idx al a idx))"

lemma body_join_idx_eq:
  "set (body_join_idx al atoms (build_findex facts)) = set (body_join al atoms facts)"
proof (induct atoms arbitrary: al)
  case Nil then show ?case by simp
next
  case (Cons a as')
  show ?case using match_facts_idx_eq[of al a facts] Cons.hyps by auto
qed

text \<open>The fast closure check: identical to @{const dl_closure_check_exec} except that the safe branch
  drives the join through the index. Only the executable term changes; the soundness bridge
  @{thm dl_closure_check_exec_imp} mentions only the abstract @{const dl_closure_check_exec} and is
  untouched.\<close>

definition dl_closure_check_exec_fast ::
    "('p::linorder, 'x, 'c::linorder) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_closure_check_exec_fast Pl Ul c =
     list_all (\<lambda>cl.
       if clause_safe_exec cl
       then list_all (\<lambda>al.
              list_all (eval_guard_al al) (cls_guards cl)
              \<longrightarrow> subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl) \<in> set (dl_cert_facts c))
              (body_join_idx [] (cls_body_atoms cl) (build_findex (dl_cert_facts c)))
       else list_all (\<lambda>\<sigma>.
              (list_all (\<lambda>g. eval_guard \<sigma> g) (cls_guards cl)
               \<and> list_all (\<lambda>a. subst_atom \<sigma> a \<in> set (dl_cert_facts c)) (cls_body_atoms cl))
              \<longrightarrow> subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c))
              (cls_substs Ul cl))
       Pl"

lemma dl_closure_check_exec_fast_eq:
  "dl_closure_check_exec Pl Ul c = dl_closure_check_exec_fast Pl Ul c"
  unfolding dl_closure_check_exec_def dl_closure_check_exec_fast_def
  by (simp add: list_all_iff body_join_idx_eq)

text \<open>Install the fast join as the code equation for @{const dl_closure_check_exec}, replacing its
  linear-scan equation.\<close>
declare dl_closure_check_exec_def [code del]
declare dl_closure_check_exec_fast_eq [code]

declare plookup_def [code] pins_def [code] build_pidx_def [code]
        alookup_def [code] ains_pos_def [code] ains_def [code] build_aidx_def [code]
        build_findex_def [code] cand_facts_def [code] match_facts_idx_def [code]
        dl_closure_check_exec_fast_def [code]

end
