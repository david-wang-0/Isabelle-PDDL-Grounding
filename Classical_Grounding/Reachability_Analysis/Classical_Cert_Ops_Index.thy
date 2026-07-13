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

definition all_bound_t :: "(variable \<times> object) list \<Rightarrow> term list \<Rightarrow> bool" where
  "all_bound_t b ts = list_all (\<lambda>t. case t of term.VAR v \<Rightarrow> map_of b v \<noteq> None | _ \<Rightarrow> True) ts"

definition ground_tuple :: "(variable \<times> object) list \<Rightarrow> term list \<Rightarrow> object list" where
  "ground_tuple b ts = map (subst_term (\<lambda>x. the (map_of b x))) ts"

definition pmatch_atom_idx ::
    "(predicate, object) findex \<Rightarrow> (variable \<times> object) list \<Rightarrow> term atom formula
       \<Rightarrow> (variable \<times> object) list list" where
  "pmatch_atom_idx idx b a =
     (case a of Atom (predAtm p ts) \<Rightarrow>
        (if all_bound_t b ts
         then (if list_ex (\<lambda>f. snd f = ground_tuple b ts) (cand_facts_t b p ts idx) then [b] else [])
         else List.map_filter (\<lambda>f. punify b ts (snd f)) (cand_facts_t b p ts idx))
      | _ \<Rightarrow> [])"

fun pjoin_idx ::
    "(predicate, object) findex \<Rightarrow> (variable \<times> object) list \<Rightarrow> term atom formula list
       \<Rightarrow> (variable \<times> object) list list" where
  "pjoin_idx idx b [] = [b]"
| "pjoin_idx idx b (a # as) =
     concat (map (\<lambda>b'. pjoin_idx idx b' as) (pmatch_atom_idx idx b a))"

subsection \<open>Dynamic per-step join: pick the most-constrained remaining atom each step\<close>

definition sel :: "(predicate, object) findex \<Rightarrow> (variable \<times> object) list \<Rightarrow> term atom formula \<Rightarrow> nat" where
  "sel idx b a = (case a of Atom (predAtm p ts) \<Rightarrow> length (cand_facts_t b p ts idx) | _ \<Rightarrow> 0)"

function pjoin_dyn ::
    "(predicate, object) findex \<Rightarrow> (variable \<times> object) list \<Rightarrow> term atom formula list
       \<Rightarrow> (variable \<times> object) list list" where
  "pjoin_dyn idx b [] = [b]"
| "pjoin_dyn idx b (a0 # atms0) =
     (let a = arg_min_list (\<lambda>a. sel idx b a) (a0 # atms0);
          rest = remove1 a (a0 # atms0)
      in concat (map (\<lambda>b'. pjoin_dyn idx b' rest) (pmatch_atom_idx idx b a)))"
  by pat_completeness auto
termination
  apply (relation "Wellfounded.measure (\<lambda>(idx, b, atms). length atms)")
   apply simp
  subgoal for idx b a0 atms0
    using arg_min_list_in[of "a0 # atms0" "sel idx b"]
    by (auto simp: length_remove1 dest: length_pos_if_in_set)
  done

declare pjoin_dyn.simps [code]

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

text \<open>Tuple-pinning: when every variable of \<open>ts\<close> is already bound under \<open>b\<close>, \<^const>\<open>punify\<close> succeeds
  against \<open>os\<close> iff \<open>os\<close> is exactly the ground tuple \<^term>\<open>ground_tuple b ts\<close>, and then leaves the binding
  \<open>b\<close> unchanged. Proved by direct induction so as not to depend on \<open>punify_sound\<close> (defined later).\<close>
lemma punify_all_bound:
  "all_bound_t b ts \<Longrightarrow> (punify b ts os = Some r \<longleftrightarrow> os = ground_tuple b ts \<and> r = b)"
proof (induct ts arbitrary: os)
  case Nil
  then show ?case by (cases os) (auto simp: ground_tuple_def)
next
  case (Cons t ts)
  show ?case
  proof (cases t)
    case (VAR v)
    with Cons.prems have bv: "map_of b v \<noteq> None" and ab: "all_bound_t b ts"
      by (auto simp: all_bound_t_def)
    from bv obtain ob2 where mv: "map_of b v = Some ob2" by auto
    show ?thesis
    proof (cases os)
      case Nil then show ?thesis by (simp add: VAR mv ground_tuple_def)
    next
      case (Cons ob os')
      have pu: "punify b (t # ts) os = (if ob2 = ob then punify b ts os' else None)"
        by (simp add: VAR mv Cons)
      have gt: "ground_tuple b (t # ts) = ob2 # ground_tuple b ts"
        by (simp add: VAR ground_tuple_def mv)
      show ?thesis
      proof (cases "ob2 = ob")
        case True
        have "(punify b (t # ts) os = Some r) = (punify b ts os' = Some r)" using pu True by simp
        also have "\<dots> = (os' = ground_tuple b ts \<and> r = b)" using Cons.hyps[OF ab] by simp
        also have "\<dots> = (os = ground_tuple b (t # ts) \<and> r = b)" using gt Cons True by auto
        finally show ?thesis .
      next
        case False
        have "punify b (t # ts) os = None" using pu False by simp
        moreover have "os \<noteq> ground_tuple b (t # ts)" using gt Cons False by simp
        ultimately show ?thesis by simp
      qed
    qed
  next
    case (CONST c)
    with Cons.prems have ab: "all_bound_t b ts" by (auto simp: all_bound_t_def)
    show ?thesis
    proof (cases os)
      case Nil then show ?thesis by (simp add: CONST ground_tuple_def)
    next
      case (Cons ob os')
      have pu: "punify b (t # ts) os = (if c = ob then punify b ts os' else None)"
        by (simp add: CONST Cons)
      have gt: "ground_tuple b (t # ts) = c # ground_tuple b ts"
        by (simp add: CONST ground_tuple_def)
      show ?thesis
      proof (cases "c = ob")
        case True
        have "(punify b (t # ts) os = Some r) = (punify b ts os' = Some r)" using pu True by simp
        also have "\<dots> = (os' = ground_tuple b ts \<and> r = b)" using Cons.hyps[OF ab] by simp
        also have "\<dots> = (os = ground_tuple b (t # ts) \<and> r = b)" using gt Cons True by auto
        finally show ?thesis .
      next
        case False
        have "punify b (t # ts) os = None" using pu False by simp
        moreover have "os \<noteq> ground_tuple b (t # ts)" using gt Cons False by simp
        ultimately show ?thesis by simp
      qed
    qed
  qed
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
  \<comment> \<open>RHS is branch-independent\<close>
  have RHS: "set (pmatch_atom (organize_facts (map fact_to_facty M)) b a)
               = {r. \<exists>os. (p, os) \<in> set M \<and> punify b ts os = Some r}"
    unfolding a pmatch_atom_def by (simp add: smf set_organize_facts_eq)
  show ?thesis
  proof (cases "all_bound_t b ts")
    case False
    have "set (pmatch_atom_idx (build_findex M) b a) = {r. \<exists>f \<in> set ?C. punify b ts (snd f) = Some r}"
      unfolding a pmatch_atom_idx_def using False by (simp add: smf)
    also have "\<dots> = {r. \<exists>os. (p, os) \<in> set M \<and> punify b ts os = Some r}"
    proof (rule set_eqI, rule iffI)
      fix r assume "r \<in> {r. \<exists>f \<in> set ?C. punify b ts (snd f) = Some r}"
      then obtain f where fC: "f \<in> set ?C" and pu: "punify b ts (snd f) = Some r" by blast
      from sub[OF fC] pu show "r \<in> {r. \<exists>os. (p, os) \<in> set M \<and> punify b ts os = Some r}" by auto
    next
      fix r assume "r \<in> {r. \<exists>os. (p, os) \<in> set M \<and> punify b ts os = Some r}"
      then obtain os where os: "(p, os) \<in> set M" and pu: "punify b ts os = Some r" by blast
      from comp[OF os pu] pu show "r \<in> {r. \<exists>f \<in> set ?C. punify b ts (snd f) = Some r}" by force
    qed
    finally show ?thesis using RHS by simp
  next
    case True
    have lex: "list_ex (\<lambda>f. snd f = ground_tuple b ts) ?C \<longleftrightarrow> (p, ground_tuple b ts) \<in> set M"
    proof
      assume "list_ex (\<lambda>f. snd f = ground_tuple b ts) ?C"
      then obtain f where fC: "f \<in> set ?C" and sf: "snd f = ground_tuple b ts"
        by (auto simp: list_ex_iff)
      from sub[OF fC] sf show "(p, ground_tuple b ts) \<in> set M" by simp
    next
      assume m: "(p, ground_tuple b ts) \<in> set M"
      have "punify b ts (ground_tuple b ts) = Some b" using punify_all_bound[OF True] by simp
      from comp[OF m this] show "list_ex (\<lambda>f. snd f = ground_tuple b ts) ?C"
        by (auto simp: list_ex_iff intro!: bexI[where x = "(p, ground_tuple b ts)"])
    qed
    have "set (pmatch_atom_idx (build_findex M) b a)
            = (if list_ex (\<lambda>f. snd f = ground_tuple b ts) ?C then {b} else {})"
      unfolding a pmatch_atom_idx_def using True by simp
    also have "\<dots> = (if (p, ground_tuple b ts) \<in> set M then {b} else {})" using lex by simp
    also have "\<dots> = {r. \<exists>os. (p, os) \<in> set M \<and> punify b ts os = Some r}"
      using punify_all_bound[OF True] by auto
    finally show ?thesis using RHS by simp
  qed
qed

lemma pjoin_idx_eq:
  "set (pjoin_idx (build_findex M) b atms) = set (pjoin (organize_facts (map fact_to_facty M)) b atms)"
proof (induct atms arbitrary: b)
  case Nil then show ?case by simp
next
  case (Cons a as)
  show ?case using pmatch_atom_idx_eq[of M b a] Cons.hyps by auto
qed

subsection \<open>Most-constrained-first reordering of the precondition atoms\<close>

text \<open>Variable set of a term list / precondition atom (total, so no \<open>is_predAtom\<close> side-condition
  leaks into the domain bookkeeping below).\<close>
definition tvars :: "term list \<Rightarrow> variable set" where
  "tvars ts = {v. term.VAR v \<in> set ts}"

definition atom_vars :: "term atom formula \<Rightarrow> variable set" where
  "atom_vars a = (case a of Atom (predAtm p ts) \<Rightarrow> tvars ts | _ \<Rightarrow> {})"

text \<open>Soundness companion to @{thm punify_complete}: a successful \<^const>\<open>punify\<close> extends the binding
  by exactly the variables it meets, and grounds \<open>ts\<close> to the matched objects \<open>os\<close>.\<close>
lemma punify_sound:
  "punify b ts os = Some b' \<Longrightarrow>
     map_of b \<subseteq>\<^sub>m map_of b'
   \<and> dom (map_of b') = dom (map_of b) \<union> tvars ts
   \<and> map (subst_term (\<lambda>x. the (map_of b' x))) ts = os"
proof (induction b ts os arbitrary: b' rule: punify.induct)
  case (1 b v ts ob os)
  show ?case
  proof (cases "map_of b v")
    case (Some ob2)
    with "1.prems" have eq: "ob2 = ob" and rec: "punify b ts os = Some b'"
      by (auto split: if_splits)
    from "1.IH"(2)[OF Some eq rec]
    have le: "map_of b \<subseteq>\<^sub>m map_of b'"
      and dm: "dom (map_of b') = dom (map_of b) \<union> tvars ts"
      and gr: "map (subst_term (\<lambda>x. the (map_of b' x))) ts = os" by auto
    have vin: "v \<in> dom (map_of b)" using Some by (auto simp: dom_def)
    have "map_of b' v = Some ob" using le Some eq by (auto simp: map_le_def dom_def)
    hence hd: "subst_term (\<lambda>x. the (map_of b' x)) (term.VAR v) = ob" by simp
    have dm': "dom (map_of b') = dom (map_of b) \<union> tvars (term.VAR v # ts)"
      using dm vin by (auto simp: tvars_def)
    show ?thesis using le dm' gr hd by simp
  next
    case None
    with "1.prems" have rec: "punify ((v, ob) # b) ts os = Some b'" by simp
    note IH = "1.IH"(1)[OF None rec]
    have le: "map_of ((v, ob) # b) \<subseteq>\<^sub>m map_of b'" using conjunct1[OF IH] .
    have dm: "dom (map_of b') = dom (map_of ((v, ob) # b)) \<union> tvars ts"
      using conjunct1[OF conjunct2[OF IH]] .
    have gr: "map (subst_term (\<lambda>x. the (map_of b' x))) ts = os"
      using conjunct2[OF conjunct2[OF IH]] .
    have le0: "map_of b \<subseteq>\<^sub>m map_of b'"
      using le None by (auto simp: map_le_def dom_def)
    have "map_of ((v, ob) # b) v = Some ob" by simp
    hence "map_of b' v = Some ob" using le by (auto simp: map_le_def dom_def)
    hence hd: "subst_term (\<lambda>x. the (map_of b' x)) (term.VAR v) = ob" by simp
    have dm': "dom (map_of b') = dom (map_of b) \<union> tvars (term.VAR v # ts)"
      using dm by (auto simp: tvars_def)
    show ?thesis using le0 dm' gr hd by simp
  qed
next
  case (2 b c ts ob os)
  with "2.prems" have ceq: "c = ob" and rec: "punify b ts os = Some b'"
    by (auto split: if_splits)
  from "2.IH"[OF _ rec] ceq
  have le: "map_of b \<subseteq>\<^sub>m map_of b'"
    and dm: "dom (map_of b') = dom (map_of b) \<union> tvars ts"
    and gr: "map (subst_term (\<lambda>x. the (map_of b' x))) ts = os" by (auto split: if_splits)
  have dm': "dom (map_of b') = dom (map_of b) \<union> tvars (term.CONST c # ts)"
    using dm by (auto simp: tvars_def)
  show ?case using le dm' gr ceq by simp
next
  case (3 b)
  then show ?case by (simp add: tvars_def)
qed auto

text \<open>A non-predicate atom in the list makes \<^const>\<open>pmatch_atom\<close> --- and hence the whole join ---
  empty, so the join enumerates nothing.\<close>
lemma pjoin_nonpred_empty:
  "\<exists>a\<in>set atms. \<not> is_predAtom a \<Longrightarrow> pjoin orga b0 atms = []"
proof (induction atms arbitrary: b0)
  case (Cons a atms)
  show ?case
  proof (cases "is_predAtom a")
    case False
    then have "pmatch_atom orga b0 a = []"
      by (cases a rule: is_predAtom.cases) (auto simp: pmatch_atom_def)
    then show ?thesis by simp
  next
    case True
    with Cons.prems have "\<exists>a\<in>set atms. \<not> is_predAtom a" by auto
    then have "\<forall>b'. pjoin orga b' atms = []" using Cons.IH by blast
    then show ?thesis by (simp add: map_replicate_const)
  qed
qed simp

text \<open>Soundness companion to @{thm pjoin_complete}: every binding produced by the join extends
  @{term b0}, has domain exactly @{term b0}'s domain together with the variables of all joined
  atoms, and grounds every joined predicate atom into its bucket \<^term>\<open>orga p\<close>. No \<open>is_predAtom\<close>
  hypothesis is needed: a non-predicate atom makes @{term "set (pjoin orga b0 atms)"} empty, so the
  membership premise is vacuous there.\<close>
lemma pjoin_sound:
  "b \<in> set (pjoin orga b0 atms) \<Longrightarrow>
     map_of b0 \<subseteq>\<^sub>m map_of b
   \<and> dom (map_of b) = dom (map_of b0) \<union> (\<Union>a\<in>set atms. atom_vars a)
   \<and> (\<forall>p ts. Atom (predAtm p ts) \<in> set atms
        \<longrightarrow> map (subst_term (\<lambda>x. the (map_of b x))) ts \<in> set (orga p))"
proof (induction atms arbitrary: b0)
  case Nil then show ?case by simp
next
  case (Cons a atms)
  from Cons.prems obtain b1 where b1: "b1 \<in> set (pmatch_atom orga b0 a)"
    and bin: "b \<in> set (pjoin orga b1 atms)" by auto
  \<comment> \<open>the head atom must be a predicate atom (else \<^const>\<open>pmatch_atom\<close> is empty)\<close>
  from b1 obtain p ts where a: "a = Atom (predAtm p ts)"
    by (cases a rule: is_predAtom.cases) (auto simp: pmatch_atom_def)
  from b1 a obtain os where os: "os \<in> set (orga p)" and pu: "punify b0 ts os = Some b1"
    by (auto simp: pmatch_atom_def List.map_filter_def split: if_splits)
  from punify_sound[OF pu]
  have le01: "map_of b0 \<subseteq>\<^sub>m map_of b1"
    and dom1: "dom (map_of b1) = dom (map_of b0) \<union> tvars ts"
    and rep1: "map (subst_term (\<lambda>x. the (map_of b1 x))) ts = os" by auto
  from Cons.IH[OF bin]
  have le1: "map_of b1 \<subseteq>\<^sub>m map_of b"
    and dom: "dom (map_of b) = dom (map_of b1) \<union> (\<Union>a\<in>set atms. atom_vars a)"
    and gr: "\<forall>p ts. Atom (predAtm p ts) \<in> set atms
               \<longrightarrow> map (subst_term (\<lambda>x. the (map_of b x))) ts \<in> set (orga p)" by auto
  have le: "map_of b0 \<subseteq>\<^sub>m map_of b" using le01 le1 by (rule map_le_trans)
  \<comment> \<open>the head atom's instance is preserved under the extended binding (agrees on its vars)\<close>
  have repa: "map (subst_term (\<lambda>x. the (map_of b x))) ts = os"
  proof -
    have "subst_term (\<lambda>x. the (map_of b x)) t = subst_term (\<lambda>x. the (map_of b1 x)) t"
      if t: "t \<in> set ts" for t
    proof (cases t)
      case (VAR y)
      with t have "y \<in> tvars ts" by (auto simp: tvars_def)
      then have "y \<in> dom (map_of b1)" using dom1 by blast
      then have "map_of b y = map_of b1 y" using le1 by (auto simp: map_le_def dom_def)
      then show ?thesis using VAR by simp
    qed simp
    then have "map (subst_term (\<lambda>x. the (map_of b x))) ts
                 = map (subst_term (\<lambda>x. the (map_of b1 x))) ts" by simp
    also have "\<dots> = os" using rep1 .
    finally show ?thesis .
  qed
  have av: "atom_vars a = tvars ts" using a by (simp add: atom_vars_def)
  have domC: "dom (map_of b) = dom (map_of b0) \<union> (\<Union>a\<in>set (a # atoms). atom_vars a)"
    if "atoms = atms" for atoms
    using dom dom1 av that by auto
  have grC: "\<forall>p' ts'. Atom (predAtm p' ts') \<in> set (a # atms)
               \<longrightarrow> map (subst_term (\<lambda>x. the (map_of b x))) ts' \<in> set (orga p')"
    using gr repa os a by auto
  show ?case using le domC[OF refl] grC by blast
qed

text \<open>Order-independent characterisation of the join's binding SET viewed through \<^const>\<open>map_of\<close>:
  the image is exactly the maps that extend @{term b0}, whose domain is @{term b0}'s domain plus the
  variables of all atoms, and that ground every atom into its bucket. Every conjunct on the right
  depends only on @{term "set atms"}, so the image is manifestly permutation invariant.\<close>
lemma pjoin_map_of_char:
  assumes "\<forall>a\<in>set atms. is_predAtom a"
  shows "(\<lambda>b. map_of b) ` set (pjoin orga b0 atms) =
     {m. map_of b0 \<subseteq>\<^sub>m m
         \<and> dom m = dom (map_of b0) \<union> (\<Union>a\<in>set atms. atom_vars a)
         \<and> (\<forall>p ts. Atom (predAtm p ts) \<in> set atms
              \<longrightarrow> map (subst_term (\<lambda>x. the (m x))) ts \<in> set (orga p))}"
  (is "?L = ?R")
proof (intro equalityI subsetI)
  fix m assume "m \<in> ?L"
  then obtain b where b: "b \<in> set (pjoin orga b0 atms)" and meq: "m = map_of b" by auto
  show "m \<in> ?R" using pjoin_sound[OF b] meq by simp
next
  fix m assume mR: "m \<in> ?R"
  then have mle0: "map_of b0 \<subseteq>\<^sub>m m"
    and dm: "dom m = dom (map_of b0) \<union> (\<Union>a\<in>set atms. atom_vars a)"
    and gr: "\<forall>p ts. Atom (predAtm p ts) \<in> set atms
               \<longrightarrow> map (subst_term (\<lambda>x. the (m x))) ts \<in> set (orga p)" by auto
  define \<rho> where "\<rho> = (\<lambda>x. the (m x))"
  have gr\<rho>: "\<forall>p ts. Atom (predAtm p ts) \<in> set atms \<longrightarrow> map (subst_term \<rho>) ts \<in> set (orga p)"
    using gr by (simp add: \<rho>_def)
  have cons0: "\<forall>x d. map_of b0 x = Some d \<longrightarrow> \<rho> x = d"
    using mle0 by (auto simp: map_le_def dom_def \<rho>_def)
  from pjoin_complete[OF gr\<rho> assms cons0] obtain b where
    b: "b \<in> set (pjoin orga b0 atms)"
    and ext_b: "\<forall>x d. map_of b0 x = Some d \<longrightarrow> map_of b x = Some d"
    and bind_b: "\<forall>p ts. Atom (predAtm p ts) \<in> set atms
                   \<longrightarrow> (\<forall>v. term.VAR v \<in> set ts \<longrightarrow> map_of b v = Some (\<rho> v))" by blast
  from pjoin_sound[OF b]
  have le0: "map_of b0 \<subseteq>\<^sub>m map_of b"
    and dom_b: "dom (map_of b) = dom (map_of b0) \<union> (\<Union>a\<in>set atms. atom_vars a)" by auto
  \<comment> \<open>the fresh atom-variables of @{term b} are bound to @{term \<rho>} (read off @{thm pjoin_complete})\<close>
  have bindx: "map_of b x = Some (\<rho> x)"
    if "x \<in> (\<Union>a\<in>set atms. atom_vars a)" for x
  proof -
    from that obtain a where ain: "a \<in> set atms" and xa: "x \<in> atom_vars a" by blast
    from ain assms have "is_predAtom a" by blast
    then obtain p ts where a: "a = Atom (predAtm p ts)"
      by (cases a rule: is_predAtom.cases) auto
    from xa a have "term.VAR x \<in> set ts" by (auto simp: atom_vars_def tvars_def)
    with ain a bind_b show ?thesis by blast
  qed
  have "map_of b = m"
  proof (rule ext)
    fix x
    show "map_of b x = m x"
    proof (cases "x \<in> dom (map_of b0)")
      case True
      then obtain d where d: "map_of b0 x = Some d" by auto
      have "map_of b x = Some d" using ext_b d by blast
      moreover have "m x = Some d" using mle0 d by (auto simp: map_le_def dom_def)
      ultimately show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "x \<in> dom m")
        case True
        then have xv: "x \<in> (\<Union>a\<in>set atms. atom_vars a)"
          using dm False by blast
        then have "map_of b x = Some (\<rho> x)" using bindx by blast
        moreover have "m x = Some (\<rho> x)" using True by (auto simp: \<rho>_def)
        ultimately show ?thesis by simp
      next
        case False
        then have "x \<notin> dom (map_of b)" using dom_b dm by blast
        then show ?thesis using False by (auto simp: dom_def)
      qed
    qed
  qed
  then show "m \<in> ?L" using b by (auto simp del: pjoin.simps)
qed

text \<open>\<^bold>\<open>Permutation invariance of the precondition join\<close>: reordering the atoms leaves the SET of
  bindings produced by the join (viewed through \<^const>\<open>map_of\<close>) unchanged. For all-predicate lists
  this is immediate from @{thm pjoin_map_of_char}; if some atom is not a predicate then --- by
  set-equality --- both lists contain one and both joins are empty.\<close>
lemma pjoin_map_of_perm:
  assumes "mset atms = mset atms'"
  shows "(\<lambda>b. map_of b) ` set (pjoin orga b0 atms)
           = (\<lambda>b. map_of b) ` set (pjoin orga b0 atms')"
proof -
  have seq: "set atms = set atms'" using assms by (metis set_mset_mset)
  show ?thesis
  proof (cases "\<forall>a\<in>set atms. is_predAtom a")
    case True
    then have True': "\<forall>a\<in>set atms'. is_predAtom a" using seq by simp
    have "(\<lambda>b. map_of b) ` set (pjoin orga b0 atms) =
      {m. map_of b0 \<subseteq>\<^sub>m m
          \<and> dom m = dom (map_of b0) \<union> (\<Union>a\<in>set atms. atom_vars a)
          \<and> (\<forall>p ts. Atom (predAtm p ts) \<in> set atms
               \<longrightarrow> map (subst_term (\<lambda>x. the (m x))) ts \<in> set (orga p))}"
      using pjoin_map_of_char[OF True] .
    also have "\<dots> =
      {m. map_of b0 \<subseteq>\<^sub>m m
          \<and> dom m = dom (map_of b0) \<union> (\<Union>a\<in>set atms'. atom_vars a)
          \<and> (\<forall>p ts. Atom (predAtm p ts) \<in> set atms'
               \<longrightarrow> map (subst_term (\<lambda>x. the (m x))) ts \<in> set (orga p))}"
      using seq by simp
    also have "\<dots> = (\<lambda>b. map_of b) ` set (pjoin orga b0 atms')"
      using pjoin_map_of_char[OF True'] by simp
    finally show ?thesis .
  next
    case False
    then have "\<exists>a\<in>set atms. \<not> is_predAtom a" by blast
    moreover from this seq have "\<exists>a\<in>set atms'. \<not> is_predAtom a" by blast
    ultimately show ?thesis by (simp add: pjoin_nonpred_empty)
  qed
qed

text \<open>\<^const>\<open>ptuples\<close> reads the binding @{term b} only through \<^term>\<open>map_of b\<close>, so two bindings
  with equal lookups enumerate the same tuples.\<close>
lemma ptuples_map_of_cong:
  "map_of b = map_of b' \<Longrightarrow> ptuples allobjs b vs = ptuples allobjs b' vs"
  by (induct vs) (auto split: option.splits)

text \<open>The dynamic per-step join enumerates the same SET of bindings (through \<^const>\<open>map_of\<close>) as the
  abstract join on the same atom list. Strong induction on \<^term>\<open>length atms\<close>: peel the \<^const>\<open>arg_min_list\<close>
  atom \<open>a\<close>, apply the IH to the strictly-shorter \<^term>\<open>remove1 a atms\<close>, swap the indexed one-step for the
  abstract one via @{thm pmatch_atom_idx_eq}, recognise \<^term>\<open>pjoin orga b0 (a # rest)\<close>, then reorder
  \<^term>\<open>a # rest\<close> back to \<^term>\<open>atms\<close> via @{thm pjoin_map_of_perm}.\<close>
lemma pjoin_dyn_img_eq:
  "(\<lambda>b. map_of b) ` set (pjoin_dyn (build_findex M) b0 atms)
     = (\<lambda>b. map_of b) ` set (pjoin (organize_facts (map fact_to_facty M)) b0 atms)"
proof (induction atms arbitrary: b0 rule: measure_induct_rule[where f = length])
  case (less atms b0)
  show ?case
  proof (cases atms)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a0 atms0)
    define a where "a = arg_min_list (\<lambda>a. sel (build_findex M) b0 a) atms"
    define rest where "rest = remove1 a atms"
    have ne: "atms \<noteq> []" using Cons by simp
    have amem: "a \<in> set atms" unfolding a_def using arg_min_list_in[OF ne] .
    have mseteq: "mset (a # rest) = mset atms" unfolding rest_def using amem by simp
    have lrest: "length rest < length atms" unfolding rest_def using amem
      by (auto simp: length_remove1 dest: length_pos_if_in_set)
    have step: "pjoin_dyn (build_findex M) b0 atms
                  = concat (map (\<lambda>b'. pjoin_dyn (build_findex M) b' rest)
                                (pmatch_atom_idx (build_findex M) b0 a))"
      using Cons unfolding a_def rest_def by (simp add: Let_def)
    have "(\<lambda>b. map_of b) ` set (pjoin_dyn (build_findex M) b0 atms)
            = (\<Union>b'\<in>set (pmatch_atom_idx (build_findex M) b0 a).
                 (\<lambda>b. map_of b) ` set (pjoin_dyn (build_findex M) b' rest))"
      by (simp add: step image_UN)
    also have "\<dots> = (\<Union>b'\<in>set (pmatch_atom_idx (build_findex M) b0 a).
                 (\<lambda>b. map_of b) ` set (pjoin (organize_facts (map fact_to_facty M)) b' rest))"
      using less.IH[OF lrest] by simp
    also have "\<dots> = (\<Union>b'\<in>set (pmatch_atom (organize_facts (map fact_to_facty M)) b0 a).
                 (\<lambda>b. map_of b) ` set (pjoin (organize_facts (map fact_to_facty M)) b' rest))"
      by (simp add: pmatch_atom_idx_eq)
    also have "\<dots> = (\<lambda>b. map_of b) ` set (pjoin (organize_facts (map fact_to_facty M)) b0 (a # rest))"
      by (simp add: image_UN)
    also have "\<dots> = (\<lambda>b. map_of b) ` set (pjoin (organize_facts (map fact_to_facty M)) b0 atms)"
      using pjoin_map_of_perm[OF mseteq] .
    finally show ?thesis .
  qed
qed

text \<open>The dynamic join and the abstract join feed the same multiset of ground tuples to the final
  guard filter: they enumerate the same bindings through \<^const>\<open>map_of\<close> (@{thm pjoin_dyn_img_eq}), and
  each surviving \<^const>\<open>ptuples\<close> set depends only on that lookup (@{thm ptuples_map_of_cong}).\<close>
lemma pjoin_dyn_ptuples_eq:
  "(\<Union>b\<in>set (pjoin_dyn (build_findex M) [] atms). set (ptuples allobjs b vars))
     = (\<Union>b\<in>set (pjoin (organize_facts (map fact_to_facty M)) [] atms). set (ptuples allobjs b vars))"
proof -
  have img: "(\<lambda>b. map_of b) ` set (pjoin_dyn (build_findex M) [] atms)
               = (\<lambda>b. map_of b) ` set (pjoin (organize_facts (map fact_to_facty M)) [] atms)"
    using pjoin_dyn_img_eq .
  show ?thesis
  proof (rule equalityI, safe)
    fix b x assume b: "b \<in> set (pjoin_dyn (build_findex M) [] atms)"
      and x: "x \<in> set (ptuples allobjs b vars)"
    have "map_of b \<in> (\<lambda>b. map_of b) ` set (pjoin (organize_facts (map fact_to_facty M)) [] atms)"
      using b img by auto
    then obtain b' where b': "b' \<in> set (pjoin (organize_facts (map fact_to_facty M)) [] atms)"
      and eq: "map_of b' = map_of b" by auto
    have "x \<in> set (ptuples allobjs b' vars)" using x ptuples_map_of_cong[OF eq] by simp
    then show "x \<in> (\<Union>b\<in>set (pjoin (organize_facts (map fact_to_facty M)) [] atms). set (ptuples allobjs b vars))"
      using b' by blast
  next
    fix b x assume b: "b \<in> set (pjoin (organize_facts (map fact_to_facty M)) [] atms)"
      and x: "x \<in> set (ptuples allobjs b vars)"
    have "map_of b \<in> (\<lambda>b. map_of b) ` set (pjoin_dyn (build_findex M) [] atms)"
      using b img by auto
    then obtain b' where b': "b' \<in> set (pjoin_dyn (build_findex M) [] atms)"
      and eq: "map_of b' = map_of b" by auto
    have "x \<in> set (ptuples allobjs b' vars)" using x ptuples_map_of_cong[OF eq] by simp
    then show "x \<in> (\<Union>b\<in>set (pjoin_dyn (build_findex M) [] atms). set (ptuples allobjs b vars))"
      using b' by blast
  qed
qed

text \<open>Reorder a clause's precondition atoms most-constrained-first: an atom's seed candidate set
  \<^term>\<open>cand_facts_t [] p ts idx\<close> is the index-narrowed set of facts it could match before any
  variable is bound, so its \<^const>\<open>length\<close> is the atom's selectivity. Sorting ascending by that
  candidate-set size puts the most-selective (smallest-bucket) atoms before the seed atoms. As a
  @{const sort_key} this is a permutation, so by @{thm pjoin_map_of_perm} the join enumerates the
  same SET of bindings (through \<^const>\<open>map_of\<close>), which is all that survives into \<^const>\<open>ptuples\<close>.\<close>
definition reorder_pre :: "(predicate, object) findex \<Rightarrow> term atom formula list \<Rightarrow> term atom formula list" where
  "reorder_pre idx atms =
     sort_key (\<lambda>a. case a of
                     Atom (predAtm p ts) \<Rightarrow> length (cand_facts_t [] p ts idx)
                   | _ \<Rightarrow> 0) atms"

lemma mset_reorder_pre: "mset (reorder_pre idx atms) = mset atms"
  by (simp add: reorder_pre_def)

text \<open>Reordering the precondition atoms does not change the multiset of ground tuples fed to the
  final guard filter: the fast join enumerates the same bindings through \<^const>\<open>map_of\<close>
  (@{thm pjoin_map_of_perm}), and each surviving \<^const>\<open>ptuples\<close> set depends only on that lookup
  (@{thm ptuples_map_of_cong}).\<close>
lemma pjoin_idx_ptuples_reorder:
  "(\<Union>b\<in>set (pjoin_idx (build_findex M) [] (reorder_pre idx atms)). set (ptuples allobjs b vars))
     = (\<Union>b\<in>set (pjoin_idx (build_findex M) [] atms). set (ptuples allobjs b vars))"
proof -
  let ?orga = "organize_facts (map fact_to_facty M)"
  have img: "(\<lambda>b. map_of b) ` set (pjoin ?orga [] (reorder_pre idx atms))
               = (\<lambda>b. map_of b) ` set (pjoin ?orga [] atms)"
    using pjoin_map_of_perm[OF mset_reorder_pre[of idx]] .
  have "(\<Union>b\<in>set (pjoin_idx (build_findex M) [] (reorder_pre idx atms)). set (ptuples allobjs b vars))
          = (\<Union>b\<in>set (pjoin ?orga [] (reorder_pre idx atms)). set (ptuples allobjs b vars))"
    by (simp add: pjoin_idx_eq)
  also have "\<dots> = (\<Union>b\<in>set (pjoin ?orga [] atms). set (ptuples allobjs b vars))"
  proof (rule equalityI, safe)
    fix b x assume b: "b \<in> set (pjoin ?orga [] (reorder_pre idx atms))"
      and x: "x \<in> set (ptuples allobjs b vars)"
    have "map_of b \<in> (\<lambda>b. map_of b) ` set (pjoin ?orga [] atms)"
      using b img by auto
    then obtain b' where b': "b' \<in> set (pjoin ?orga [] atms)" and eq: "map_of b' = map_of b"
      by auto
    have "x \<in> set (ptuples allobjs b' vars)"
      using x ptuples_map_of_cong[OF eq] by simp
    then show "x \<in> (\<Union>b\<in>set (pjoin ?orga [] atms). set (ptuples allobjs b vars))"
      using b' by blast
  next
    fix b x assume b: "b \<in> set (pjoin ?orga [] atms)"
      and x: "x \<in> set (ptuples allobjs b vars)"
    have "map_of b \<in> (\<lambda>b. map_of b) ` set (pjoin ?orga [] (reorder_pre idx atms))"
      using b img by auto
    then obtain b' where b': "b' \<in> set (pjoin ?orga [] (reorder_pre idx atms))"
      and eq: "map_of b' = map_of b" by auto
    have "x \<in> set (ptuples allobjs b' vars)"
      using x ptuples_map_of_cong[OF eq] by simp
    then show "x \<in> (\<Union>b\<in>set (pjoin ?orga [] (reorder_pre idx atms)). set (ptuples allobjs b vars))"
      using b' by blast
  qed
  also have "\<dots> = (\<Union>b\<in>set (pjoin_idx (build_findex M) [] atms). set (ptuples allobjs b vars))"
    by (simp add: pjoin_idx_eq)
  finally show ?thesis .
qed

definition cert_ops_for_clause_fast ::
    "object list \<Rightarrow> (predicate, object) findex \<Rightarrow> action_clause \<Rightarrow> ast_classical_plan_action list" where
  "cert_ops_for_clause_fast allobjs idx c =
     map (SimplePlanAction (cl_name c))
       (filter (satisfies_conds (cl_params c) (cl_cond_pre c))
         (concat (map (\<lambda>b. ptuples allobjs b (map fst (cl_params c)))
                      (pjoin_dyn idx [] (cl_pred_pre c)))))"

lemma cert_ops_for_clause_fast_eq:
  "set (cert_ops_for_clause_fast allobjs (build_findex M) c)
     = set (cert_ops_for_clause allobjs (organize_facts (map fact_to_facty M)) c)"
proof -
  let ?g = "SimplePlanAction (cl_name c)"
  let ?P = "satisfies_conds (cl_params c) (cl_cond_pre c)"
  let ?vars = "map fst (cl_params c)"
  \<comment> \<open>candidate tuples: dynamic index join (fast) and unordered abstract enumerate the same set\<close>
  have tup: "(\<Union>b\<in>set (pjoin_dyn (build_findex M) [] (cl_pred_pre c)).
                set (ptuples allobjs b ?vars))
             = (\<Union>b\<in>set (pjoin (organize_facts (map fact_to_facty M)) [] (cl_pred_pre c)).
                set (ptuples allobjs b ?vars))"
    using pjoin_dyn_ptuples_eq[where M = M and atms = "cl_pred_pre c"
            and allobjs = allobjs and vars = ?vars] .
  \<comment> \<open>@{const cert_ops_for_clause}(\_fast) as an image of a filtered big-union of tuples\<close>
  have set_form: "set (map ?g (filter ?P (concat (map (\<lambda>b. ptuples allobjs b ?vars) L))))
                    = ?g ` {x \<in> (\<Union>b\<in>set L. set (ptuples allobjs b ?vars)). ?P x}" for L
    by auto
  have "set (cert_ops_for_clause_fast allobjs (build_findex M) c)
          = ?g ` {x \<in> (\<Union>b\<in>set (pjoin_dyn (build_findex M) []
                        (cl_pred_pre c)). set (ptuples allobjs b ?vars)). ?P x}"
    unfolding cert_ops_for_clause_fast_def using set_form .
  also have "\<dots> = ?g ` {x \<in> (\<Union>b\<in>set (pjoin (organize_facts (map fact_to_facty M)) []
                        (cl_pred_pre c)). set (ptuples allobjs b ?vars)). ?P x}"
    using tup by simp
  also have "\<dots> = set (cert_ops_for_clause allobjs (organize_facts (map fact_to_facty M)) c)"
    unfolding cert_ops_for_clause_def using set_form[symmetric] .
  finally show ?thesis .
qed
end
