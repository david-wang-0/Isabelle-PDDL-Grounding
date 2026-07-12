theory Fact_Index
  imports Datalog_Certificate_Code "HOL-Data_Structures.RBT_Map"
begin

text \<open>Generic RBT fact index, shared by the datalog closure check (\<^const>\<open>body_join\<close>, in
  \<open>Datalog_Certificate_Index\<close>) and the classical action grounder (\<open>pjoin\<close>, in the Classical layer).
  It is polymorphic in the predicate/constant pair \<open>('p::linorder, 'c::linorder)\<close> and carries no
  matching layer, so both joins reuse one copy. It lives in \<open>Datalog_Certification\<close> --- the lowest
  common ancestor of both branches --- which pulls in \<^theory>\<open>HOL-Data_Structures.RBT_Map\<close> here (the
  same functional RBT family the graph library already uses, not the Collections tower).\<close>

text \<open>\<^theory>\<open>HOL-Data_Structures.RBT_Map\<close> re-exports its own \<open>AList_Upd_Del.map_of\<close>, which would
  shadow \<open>Map.map_of\<close> --- the association-list lookup the datalog/classical matchers thread. Keep the
  short name \<open>map_of\<close> resolving to \<^const>\<open>Map.map_of\<close>.\<close>
hide_const (open) AList_Upd_Del.map_of

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

subsection \<open>Bundled index\<close>

text \<open>Both indices in one record: the coarse predicate bucket \<open>fx_p\<close> seeds a body atom whose
  arguments are all unbound; the fine per-argument bucket \<open>fx_a\<close> narrows an atom with a bound
  argument. The matching layer that consumes this (\<open>cand_facts\<close>/\<open>pmatch_atom_idx\<close>) is per-branch.\<close>

datatype ('p, 'c) findex = FIndex (fx_p: "('p, 'c) pfidx") (fx_a: "('p, 'c) afidx")

definition build_findex :: "('p::linorder, 'c::linorder) dl_fact list \<Rightarrow> ('p, 'c) findex" where
  "build_findex facts = FIndex (build_pidx facts) (build_aidx facts)"

declare plookup_def [code] pins_def [code] build_pidx_def [code]
        alookup_def [code] ains_pos_def [code] ains_def [code] build_aidx_def [code]
        build_findex_def [code]

end
