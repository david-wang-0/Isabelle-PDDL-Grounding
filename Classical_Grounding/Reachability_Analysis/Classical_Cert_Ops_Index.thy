theory Classical_Cert_Ops_Index
  imports Classical_Certified_Grounding_Locales Datalog_Certification.Fact_Index
    Grounding_Classical_Common.PDDL_Orderings
begin

text \<open>RBT-indexed refinement of the \<open>cert_ops\<close> action-grounding join, mirroring the datalog closure
  index (\<^const>\<open>Fact_Index.build_findex\<close> etc.). \<open>pmatch_atom\<close>/\<open>pjoin\<close> scan the whole predicate bucket
  \<open>orga p\<close>; here we instead look up only the candidate facts sharing a bound argument (or the predicate
  bucket for a seed atom), and prove (\<open>pmatch_atom_idx_eq\<close>, the Lemma-A analogue) that filtering the
  index candidates with \<^const>\<open>punify\<close> yields exactly the same matches. The certificate facts
  \<^term>\<open>M :: fact list\<close> are \<^typ>\<open>(predicate, object) dl_fact\<close> lists, so \<^const>\<open>build_findex\<close> applies
  directly; \<^const>\<open>organize_facts\<close> is the function-bucket \<open>orga\<close> that the abstract join uses.\<close>

text \<open>\<^theory>\<open>HOL-Data_Structures.RBT_Map\<close> (via \<^const>\<open>build_findex\<close>) re-exports \<open>AList_Upd_Del.map_of\<close>,
  which shadows \<open>Map.map_of\<close> --- the assoc-list lookup \<^const>\<open>punify\<close> threads. Re-hide it.\<close>
hide_const (open) AList_Upd_Del.map_of

subsection \<open>Index-backed candidate selection for one precondition atom\<close>

text \<open>The leftmost argument of the atom that is already determined under the current binding \<open>b\<close> ---
  a constant \<^const>\<open>term.CONST\<close>, or a variable \<^const>\<open>term.VAR\<close> already bound in \<open>b\<close> --- together with
  its value; \<^const>\<open>None\<close> if every argument is an unbound variable (a seed atom).\<close>

fun first_bound_t :: "(variable \<times> object) list \<Rightarrow> term list \<Rightarrow> (nat \<times> object) option" where
  "first_bound_t b [] = None"
| "first_bound_t b (t # ts) =
     (case t of
        term.CONST c \<Rightarrow> Some (0, c)
      | term.VAR v \<Rightarrow> (case map_of b v of
                        Some ob \<Rightarrow> Some (0, ob)
                      | None \<Rightarrow> map_option (\<lambda>(j, ob). (Suc j, ob)) (first_bound_t b ts)))"

text \<open>All determined positions with their values (not just the leftmost): a constant is determined
  at its own position, a variable is determined iff bound in \<open>b\<close>. Used to select the smallest
  (most-selective) candidate bucket rather than always the leftmost one.\<close>
fun determined_ids_t :: "(variable \<times> object) list \<Rightarrow> term list \<Rightarrow> (nat \<times> object) list" where
  "determined_ids_t b [] = []"
| "determined_ids_t b (t # ts) =
     (case t of
        term.CONST c \<Rightarrow> (0, c) # map (\<lambda>(j, v). (Suc j, v)) (determined_ids_t b ts)
      | term.VAR x \<Rightarrow> (case map_of b x of
                        Some ob \<Rightarrow> (0, ob) # map (\<lambda>(j, v). (Suc j, v)) (determined_ids_t b ts)
                      | None \<Rightarrow> map (\<lambda>(j, v). (Suc j, v)) (determined_ids_t b ts)))"

text \<open>Pick a shortest list from a nonempty list of lists; returns an element of its input.\<close>
fun shortest :: "'a list list \<Rightarrow> 'a list" where
  "shortest [] = []"
| "shortest [xs] = xs"
| "shortest (xs # ys # rest) = (let zs = shortest (ys # rest) in if length xs \<le> length zs then xs else zs)"

lemma shortest_mem: "xss \<noteq> [] \<Longrightarrow> shortest xss \<in> set xss"
  by (induct xss rule: shortest.induct) (auto simp: Let_def)

definition cand_facts_t ::
    "(variable \<times> object) list \<Rightarrow> predicate \<Rightarrow> term list \<Rightarrow> (predicate, object) findex
       \<Rightarrow> (predicate, object) dl_fact list" where
  "cand_facts_t b p ts idx =
     (case determined_ids_t b ts of
        [] \<Rightarrow> plookup (fx_p idx) p
      | dets \<Rightarrow> shortest (map (\<lambda>(j, v). alookup (fx_a idx) p j v) dets))"

definition pmatch_atom_idx ::
    "(predicate, object) findex \<Rightarrow> (variable \<times> object) list \<Rightarrow> term atom formula
       \<Rightarrow> (variable \<times> object) list list" where
  "pmatch_atom_idx idx b a =
     (case a of Atom (predAtm p ts) \<Rightarrow>
        List.map_filter (\<lambda>f. punify b ts (snd f)) (cand_facts_t b p ts idx)
      | _ \<Rightarrow> [])"

fun pjoin_idx ::
    "(predicate, object) findex \<Rightarrow> (variable \<times> object) list \<Rightarrow> term atom formula list
       \<Rightarrow> (variable \<times> object) list list" where
  "pjoin_idx idx b [] = [b]"
| "pjoin_idx idx b (a # as) =
     concat (map (\<lambda>b'. pjoin_idx idx b' as) (pmatch_atom_idx idx b a))"

subsection \<open>Equivalence to the unindexed join\<close>

text \<open>Forcing lemma: if \<^const>\<open>first_bound_t\<close> reports position \<open>j\<close> determined to \<open>v\<close>, then any object
  tuple \<open>os\<close> that \<^const>\<open>punify\<close> accepts against \<open>ts\<close> carries \<open>v\<close> at position \<open>j\<close>. Generalised over a
  smaller binding \<open>b0\<close> that \<open>b\<close> extends, to thread the induction.\<close>
lemma first_bound_t_match_gen:
  "first_bound_t b0 ts = Some (j, v) \<Longrightarrow> punify b ts os = Some r \<Longrightarrow>
     (\<forall>z w. map_of b0 z = Some w \<longrightarrow> map_of b z = Some w) \<Longrightarrow> j < length os \<and> os ! j = v"
proof (induct ts arbitrary: b os r j v)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  from Cons.prems(2) obtain ob os' where os: "os = ob # os'" by (cases os) (auto split: term.splits)
  show ?case
  proof (cases t)
    case (CONST c)
    with Cons.prems(1) have jv: "j = 0" "v = c" by auto
    from Cons.prems(2) os CONST have "c = ob" by (auto split: if_splits)
    with jv os show ?thesis by simp
  next
    case (VAR y)
    show ?thesis
    proof (cases "map_of b0 y")
      case (Some w)
      with VAR Cons.prems(1) have jv: "j = 0" "v = w" by auto
      have "map_of b y = Some w" using Some Cons.prems(3) by blast
      with Cons.prems(2) os VAR have "ob = w" by (auto split: if_splits option.splits)
      with jv os show ?thesis by simp
    next
      case None
      with VAR Cons.prems(1) obtain j' where fb': "first_bound_t b0 ts = Some (j', v)"
        and jsuc: "j = Suc j'" by (auto split: option.splits prod.splits)
      have rec: "\<exists>b'. punify b' ts os' = Some r \<and>
                   (\<forall>z w. map_of b0 z = Some w \<longrightarrow> map_of b' z = Some w)"
      proof (cases "map_of b y")
        case (Some ob2)
        with Cons.prems(2) os VAR have "punify b ts os' = Some r" by (auto split: if_splits)
        thus ?thesis using Cons.prems(3) by blast
      next
        case None': None
        with Cons.prems(2) os VAR have step: "punify ((y, ob) # b) ts os' = Some r"
          by (auto split: if_splits)
        have "\<forall>z w. map_of b0 z = Some w \<longrightarrow> map_of ((y, ob) # b) z = Some w"
          using Cons.prems(3) None None' by fastforce
        thus ?thesis using step by blast
      qed
      then obtain b' where step': "punify b' ts os' = Some r"
        and ext': "\<forall>z w. map_of b0 z = Some w \<longrightarrow> map_of b' z = Some w" by blast
      from Cons.hyps[OF fb' step' ext'] show ?thesis using os jsuc by simp
    qed
  qed
qed

lemma first_bound_t_match:
  "first_bound_t b ts = Some (j, v) \<Longrightarrow> punify b ts os = Some r \<Longrightarrow> j < length os \<and> os ! j = v"
  using first_bound_t_match_gen[of b ts j v b os r] by simp

text \<open>Every determined position \<^const>\<open>determined_ids_t\<close> reports is carried by any object tuple
  \<^term>\<open>os\<close> that \<^const>\<open>punify\<close> accepts against \<open>ts\<close>. Mirrors @{thm first_bound_t_match} but ranges
  over all determined positions, not just the leftmost. The recursion of \<^const>\<open>punify\<close> only extends
  the binding \<open>b\<close> (either unchanged, or with one new \<open>(x, ob)\<close> pair), so a position determined under
  \<open>b\<close> stays determined under the extended binding \<open>b'\<close> --- transported by the inner \<open>det_mono\<close>.\<close>
lemma determined_ids_t_match:
  "(j, v) \<in> set (determined_ids_t b ts) \<Longrightarrow> punify b ts os = Some r \<Longrightarrow> j < length os \<and> os ! j = v"
proof (induct ts arbitrary: b os r j v)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  from Cons.prems(2) obtain ob os' where os: "os = ob # os'" by (cases os) (auto split: term.splits)
  \<comment> \<open>The recursive \<^const>\<open>punify\<close> call runs at a binding \<open>b'\<close> extending \<open>b\<close>.\<close>
  have rec: "\<exists>b'. punify b' ts os' = Some r \<and>
               (\<forall>z w. map_of b z = Some w \<longrightarrow> map_of b' z = Some w)"
  proof (cases t)
    case (CONST c)
    with Cons.prems(2) os have "punify b ts os' = Some r" by (auto split: if_splits)
    then show ?thesis by blast
  next
    case (VAR y)
    show ?thesis
    proof (cases "map_of b y")
      case (Some ob2)
      with Cons.prems(2) os VAR have "punify b ts os' = Some r" by (auto split: if_splits)
      then show ?thesis by blast
    next
      case None
      with Cons.prems(2) os VAR have step: "punify ((y, ob) # b) ts os' = Some r"
        by (auto split: if_splits)
      have "\<forall>z w. map_of b z = Some w \<longrightarrow> map_of ((y, ob) # b) z = Some w"
        using None by fastforce
      with step show ?thesis by blast
    qed
  qed
  then obtain b' where step': "punify b' ts os' = Some r"
    and ext': "\<forall>z w. map_of b z = Some w \<longrightarrow> map_of b' z = Some w" by blast
  have IH: "\<And>j' v'. (j', v') \<in> set (determined_ids_t b' ts) \<Longrightarrow> j' < length os' \<and> os' ! j' = v'"
    using Cons.hyps step' by blast
  \<comment> \<open>Positions determined under \<open>b\<close> stay determined under the extended \<open>b'\<close>.\<close>
  have det_mono: "set (determined_ids_t b ts) \<subseteq> set (determined_ids_t b' ts)"
  proof (induct ts)
    case Nil then show ?case by simp
  next
    case (Cons s ss)
    show ?case
    proof (cases s)
      case (CONST c)
      then show ?thesis using Cons.hyps by auto
    next
      case (VAR x)
      show ?thesis
      proof (cases "map_of b x")
        case None
        then show ?thesis using VAR Cons.hyps by (auto split: option.splits)
      next
        case (Some w)
        then have "map_of b' x = Some w" using ext' by blast
        then show ?thesis using VAR Some Cons.hyps by auto
      qed
    qed
  qed
  show ?case
  proof (cases t)
    case (CONST c)
    show ?thesis
    proof (cases "(j, v) = (0, c)")
      case True
      from Cons.prems(2) os CONST have "c = ob" by (auto split: if_splits)
      with True os show ?thesis by simp
    next
      case False
      with CONST Cons.prems(1) obtain j' where jv: "(j, v) = (Suc j', v)"
        and mem: "(j', v) \<in> set (determined_ids_t b ts)"
        by (auto split: prod.splits)
      from IH[OF subsetD[OF det_mono mem]] jv os show ?thesis by simp
    qed
  next
    case (VAR x)
    show ?thesis
    proof (cases "map_of b x")
      case (Some w)
      show ?thesis
      proof (cases "(j, v) = (0, w)")
        case True
        from Cons.prems(2) os VAR Some have "ob = w" by (auto split: if_splits)
        with True os show ?thesis by simp
      next
        case False
        with VAR Some Cons.prems(1) obtain j' where jv: "(j, v) = (Suc j', v)"
          and mem: "(j', v) \<in> set (determined_ids_t b ts)"
          by (auto split: prod.splits)
        from IH[OF subsetD[OF det_mono mem]] jv os show ?thesis by simp
      qed
    next
      case None
      with VAR Cons.prems(1) obtain j' where jv: "(j, v) = (Suc j', v)"
        and mem: "(j', v) \<in> set (determined_ids_t b ts)"
        by (auto split: prod.splits)
      from IH[OF subsetD[OF det_mono mem]] jv os show ?thesis by simp
    qed
  qed
qed

text \<open>Bridge: the function bucket \<^term>\<open>organize_facts (map fact_to_facty M) p\<close> is exactly the set of
  argument tuples of predicate \<open>p\<close> occurring in \<open>M\<close>.\<close>
lemma set_organize_facts_eq:
  "set (organize_facts (map fact_to_facty M) p) = {args. (p, args) \<in> set M}"
proof -
  have pred: "\<forall>g \<in> set (map fact_to_facty M). is_predAtom g"
    by (auto simp: uncurry_def split: prod.splits)
  show ?thesis
  proof (rule set_eqI)
    fix args
    have "args \<in> set (organize_facts (map fact_to_facty M) p)
            \<longleftrightarrow> in_orga (Atom (predAtm p args)) (organize_facts (map fact_to_facty M))"
      by simp
    also have "... \<longleftrightarrow> Atom (predAtm p args) \<in> set (map fact_to_facty M)"
      by (rule in_orga_organize_facts[OF pred])
    also have "... \<longleftrightarrow> (p, args) \<in> set M"
      by (force simp: uncurry_def image_iff split: prod.splits)
    finally show "args \<in> set (organize_facts (map fact_to_facty M) p)
                    \<longleftrightarrow> args \<in> {args. (p, args) \<in> set M}"
      by simp
  qed
qed

text \<open>Predicate-key soundness for the coarse bucket: every fact returned by \<^const>\<open>plookup\<close> on the
  bucket built for predicate \<open>p\<close> actually has predicate \<open>p\<close>. (The existing @{thm plookup_build_sound}
  only bounds the candidates by \<open>set facts\<close>; here we additionally read off the bucket key.)\<close>
lemma plookup_build_pred:
  "f \<in> set (plookup (build_pidx facts) p) \<Longrightarrow> fst f = p"
proof -
  have gen: "(\<forall>f \<in> set (plookup idx p). fst f = p) \<Longrightarrow> M.invar idx \<Longrightarrow>
               (\<forall>f \<in> set (plookup (fold pins facts idx) p). fst f = p)" for idx facts
  proof (induct facts arbitrary: idx)
    case Nil then show ?case by simp
  next
    case (Cons g facts)
    have "\<forall>f \<in> set (plookup (pins g idx) p). fst f = p"
      using Cons.prems by (auto simp: plookup_pins split: if_splits)
    from Cons.hyps[OF this pins_invar[OF Cons.prems(2)]] show ?case by simp
  qed
  have base: "\<forall>f \<in> set (plookup RBT_Set.empty p). fst f = p"
    by (simp add: plookup_def M.map_empty)
  assume "f \<in> set (plookup (build_pidx facts) p)"
  then show ?thesis
    using gen[OF base M.invar_empty, of facts] by (simp add: build_pidx_def)
qed

text \<open>Predicate-key soundness for the fine per-argument bucket: every fact returned by
  \<^const>\<open>alookup\<close> on the bucket built for predicate \<open>p\<close> actually has predicate \<open>p\<close>.\<close>
lemma alookup_build_pred:
  "f \<in> set (alookup (build_aidx facts) p j v) \<Longrightarrow> fst f = p"
proof -
  have pos: "(\<forall>f \<in> set (alookup idx p i w). fst f = p) \<Longrightarrow> M.invar idx \<Longrightarrow>
               (\<forall>f \<in> set (alookup (fold (ains_pos g) js idx) p i w). fst f = p)" for idx js g i w
  proof (induct js arbitrary: idx)
    case Nil then show ?case by simp
  next
    case (Cons k js)
    have "\<forall>f \<in> set (alookup (ains_pos g k idx) p i w). fst f = p"
      using Cons.prems by (auto simp: alookup_ains_pos split: if_splits)
    from Cons.hyps[OF this ains_pos_invar[OF Cons.prems(2)]] show ?case by simp
  qed
  have gen: "(\<forall>f \<in> set (alookup idx p i w). fst f = p) \<Longrightarrow> M.invar idx \<Longrightarrow>
               (\<forall>f \<in> set (alookup (fold ains facts idx) p i w). fst f = p)" for idx i w facts
  proof (induct facts arbitrary: idx)
    case Nil then show ?case by simp
  next
    case (Cons g facts)
    have "\<forall>f \<in> set (alookup (ains g idx) p i w). fst f = p"
      unfolding ains_def using pos[OF Cons.prems(1) Cons.prems(2)] .
    from Cons.hyps[OF this ains_invar[OF Cons.prems(2)]] show ?case by simp
  qed
  have base: "\<forall>f \<in> set (alookup RBT_Set.empty p j v). fst f = p"
    by (simp add: alookup_def M.map_empty)
  assume "f \<in> set (alookup (build_aidx facts) p j v)"
  then show ?thesis
    using gen[OF base M.invar_empty] by (simp add: build_aidx_def)
qed

text \<open>\<^bold>\<open>Lemma A (cert_ops)\<close>: filtering the index-selected candidates with \<^const>\<open>punify\<close> yields exactly
  the matches of the full predicate-bucket scan.\<close>
lemma pmatch_atom_idx_eq:
  "set (pmatch_atom_idx (build_findex M) b a)
     = set (pmatch_atom (organize_facts (map fact_to_facty M)) b a)"
proof (cases "\<exists>p ts. a = Atom (predAtm p ts)")
  case False
  then show ?thesis
    by (auto simp: pmatch_atom_idx_def pmatch_atom_def split: atom.splits formula.splits)
next
  case True
  then obtain p ts where a: "a = Atom (predAtm p ts)" by blast
  have smf: "set (List.map_filter g xs) = {y. \<exists>x \<in> set xs. g x = Some y}" for g :: "'x \<Rightarrow> 'y option" and xs
    by (induct xs) (auto simp: List.map_filter_def split: option.splits)
  let ?C = "cand_facts_t b p ts (build_findex M)"
  let ?bkt = "\<lambda>(j, v). alookup (build_aidx M) p j v"
  \<comment> \<open>soundness: every candidate is a fact of predicate \<open>p\<close>\<close>
  have sub: "(p, snd f) \<in> set M" if f: "f \<in> set ?C" for f
  proof (cases "determined_ids_t b ts")
    case Nil
    then have "?C = plookup (build_pidx M) p"
      by (simp add: cand_facts_t_def build_findex_def)
    then have fp: "f \<in> set (plookup (build_pidx M) p)" using f by simp
    have "f \<in> set M" using plookup_build_sound fp by blast
    moreover have "fst f = p" using plookup_build_pred[OF fp] .
    ultimately show ?thesis by (metis prod.collapse)
  next
    case (Cons d dets)
    then have C: "?C = shortest (map ?bkt (d # dets))"
      by (simp add: cand_facts_t_def build_findex_def)
    have "?C \<in> set (map ?bkt (d # dets))"
      using shortest_mem[of "map ?bkt (d # dets)"] C by simp
    then obtain jv where Ceq: "?C = ?bkt jv" unfolding set_map by blast
    obtain j v where jv: "jv = (j, v)" by (cases jv)
    from Ceq jv have "f \<in> set (alookup (build_aidx M) p j v)" using f by simp
    then have fa: "f \<in> set (alookup (build_aidx M) p j v)" .
    have "f \<in> set M" using alookup_build_sound fa by blast
    moreover have "fst f = p" using alookup_build_pred[OF fa] .
    ultimately show ?thesis by (metis prod.collapse)
  qed
  \<comment> \<open>completeness: any fact of predicate \<open>p\<close> that unifies is among the candidates\<close>
  have comp: "(p, os) \<in> set ?C" if os: "(p, os) \<in> set M" and u: "punify b ts os = Some r" for os r
  proof (cases "determined_ids_t b ts")
    case Nil
    then have "?C = plookup (build_pidx M) p"
      by (simp add: cand_facts_t_def build_findex_def)
    moreover have "(p, os) \<in> set (plookup (build_pidx M) (fst (p, os)))"
      using plookup_build_complete[OF os] .
    ultimately show ?thesis by simp
  next
    case (Cons d dets)
    then have C: "?C = shortest (map ?bkt (d # dets))"
      by (simp add: cand_facts_t_def build_findex_def)
    \<comment> \<open>a matching fact carries every determined value, so it lies in \<^emph>\<open>every\<close> determined bucket\<close>
    have inbkt: "(p, os) \<in> set (?bkt jv)" if "jv \<in> set (d # dets)" for jv
    proof -
      obtain j v where jv: "jv = (j, v)" by (cases jv)
      with that Cons have "(j, v) \<in> set (determined_ids_t b ts)" by simp
      from determined_ids_t_match[OF this u] have jl: "j < length os" and vj: "os ! j = v"
        by simp_all
      have "(p, os) \<in> set (alookup (build_aidx M) (fst (p, os)) j (snd (p, os) ! j))"
        using alookup_build_complete[OF os] jl by simp
      then show ?thesis using vj jv by simp
    qed
    have "?C \<in> set (map ?bkt (d # dets))"
      using shortest_mem[of "map ?bkt (d # dets)"] C by simp
    then obtain jv where mem: "jv \<in> set (d # dets)" and sh: "?C = ?bkt jv"
      unfolding set_map by blast
    show ?thesis using sh inbkt[OF mem] by simp
  qed
  have "set (pmatch_atom_idx (build_findex M) b a)
          = {r. \<exists>f \<in> set ?C. punify b ts (snd f) = Some r}"
    unfolding a pmatch_atom_idx_def by (simp add: smf)
  also have "... = {r. \<exists>os. (p, os) \<in> set M \<and> punify b ts os = Some r}"
  proof (rule set_eqI, rule iffI)
    fix r assume "r \<in> {r. \<exists>f \<in> set ?C. punify b ts (snd f) = Some r}"
    then obtain f where fC: "f \<in> set ?C" and pu: "punify b ts (snd f) = Some r" by blast
    have "(p, snd f) \<in> set M" using sub[OF fC] .
    with pu show "r \<in> {r. \<exists>os. (p, os) \<in> set M \<and> punify b ts os = Some r}" by auto
  next
    fix r assume "r \<in> {r. \<exists>os. (p, os) \<in> set M \<and> punify b ts os = Some r}"
    then obtain os where os: "(p, os) \<in> set M" and pu: "punify b ts os = Some r" by blast
    from comp[OF os pu] have "(p, os) \<in> set ?C" .
    with pu show "r \<in> {r. \<exists>f \<in> set ?C. punify b ts (snd f) = Some r}" by force
  qed
  also have "... = set (pmatch_atom (organize_facts (map fact_to_facty M)) b a)"
    unfolding a pmatch_atom_def by (simp add: smf set_organize_facts_eq)
  finally show ?thesis .
qed

lemma pjoin_idx_eq:
  "set (pjoin_idx (build_findex M) b atms) = set (pjoin (organize_facts (map fact_to_facty M)) b atms)"
proof (induct atms arbitrary: b)
  case Nil then show ?case by simp
next
  case (Cons a as)
  show ?case using pmatch_atom_idx_eq[of M b a] Cons.hyps by auto
qed

definition cert_ops_for_clause_fast ::
    "object list \<Rightarrow> (predicate, object) findex \<Rightarrow> action_clause \<Rightarrow> ast_classical_plan_action list" where
  "cert_ops_for_clause_fast allobjs idx c =
     map (SimplePlanAction (cl_name c))
       (filter (satisfies_conds (cl_params c) (cl_cond_pre c))
         (concat (map (\<lambda>b. ptuples allobjs b (map fst (cl_params c)))
                      (pjoin_idx idx [] (cl_pred_pre c)))))"

lemma cert_ops_for_clause_fast_eq:
  "set (cert_ops_for_clause_fast allobjs (build_findex M) c)
     = set (cert_ops_for_clause allobjs (organize_facts (map fact_to_facty M)) c)"
  unfolding cert_ops_for_clause_fast_def cert_ops_for_clause_def
  by (simp add: pjoin_idx_eq)

end
