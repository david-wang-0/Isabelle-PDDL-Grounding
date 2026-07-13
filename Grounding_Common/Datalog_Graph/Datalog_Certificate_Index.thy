theory Datalog_Certificate_Index
  imports Datalog_Cycle_DFS Datalog_Certification.Fact_Index
begin

text \<open>\<^theory>\<open>HOL-Data_Structures.RBT_Map\<close> --- pulled in both by \<open>Datalog_Cycle_DFS\<close> (via the graph
  library) and by \<open>Fact_Index\<close> --- re-exports \<open>AList_Upd_Del.map_of\<close>, which shadows
  \<open>Map.map_of\<close>, the assoc-list lookup the datalog matcher threads. \<open>Fact_Index\<close>'s own hide does
  not survive the merge with \<open>Datalog_Cycle_DFS\<close>, so re-hide it here where \<open>map_of\<close> is used.\<close>
hide_const (open) AList_Upd_Del.map_of

text \<open>Datalog matching layer over the generic \<open>Fact_Index\<close>: the fact-driven body join
  refined to look up only index candidates, proven equal to the linear scan (\<^bold>\<open>Lemma A\<close>,
  \<open>match_facts_idx_eq\<close>) and installed as the [code] equation for the closure check. The soundness
  bridge \<^const>\<open>dl_closure_check_exec\<close> / \<open>dl_closure_check_exec_imp\<close> mentions only the abstract check
  and is untouched. Sited in \<open>Datalog_Graph\<close> (not in its ROOT --- loaded live for dev) only because it
  wants the graph-layer heap; nothing here uses the graph library. WORK IN PROGRESS.\<close>

subsection \<open>Index-backed candidate selection for one body atom\<close>

text \<open>For a body atom, if some argument is already determined under the current partial assignment
  @{term al} (a constant, or a variable bound in @{term al}), we fetch the narrow per-argument bucket
  for that (predicate, position, value); otherwise the atom is a seed and we fetch its whole predicate
  bucket. Either way the candidate list is a subset of the facts that still contains every fact that
  could match, so filtering it with @{const match_atom_al} yields exactly the same matches as scanning
  all facts.\<close>

fun first_bound :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id list \<Rightarrow> (nat \<times> 'c) option" where
  "first_bound al [] = None"
| "first_bound al (i # is') =
     (case i of
        id.Cst c \<Rightarrow> Some (0, c)
      | id.Var x \<Rightarrow> (case map_of al x of
                      Some v \<Rightarrow> Some (0, v)
                    | None \<Rightarrow> map_option (\<lambda>(j, v). (Suc j, v)) (first_bound al is')))"

text \<open>All determined positions with their values (not just the leftmost): a constant is determined
  at its own position, a variable is determined iff bound in @{term al}. Used to select the
  smallest (most-selective) candidate bucket rather than always the leftmost one.\<close>
fun determined_ids :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id list \<Rightarrow> (nat \<times> 'c) list" where
  "determined_ids al [] = []"
| "determined_ids al (i # is') =
     (case i of
        id.Cst c \<Rightarrow> (0, c) # map (\<lambda>(j, v). (Suc j, v)) (determined_ids al is')
      | id.Var x \<Rightarrow> (case map_of al x of
                       Some v \<Rightarrow> (0, v) # map (\<lambda>(j, v). (Suc j, v)) (determined_ids al is')
                     | None \<Rightarrow> map (\<lambda>(j, v). (Suc j, v)) (determined_ids al is')))"

text \<open>Pick a shortest list from a nonempty list of lists; returns an element of its input.\<close>
fun shortest :: "'a list list \<Rightarrow> 'a list" where
  "shortest [] = []"
| "shortest [xs] = xs"
| "shortest (xs # ys # rest) = (let zs = shortest (ys # rest) in if length xs \<le> length zs then xs else zs)"

lemma shortest_mem: "xss \<noteq> [] \<Longrightarrow> shortest xss \<in> set xss"
  by (induct xss rule: shortest.induct) (auto simp: Let_def)

definition cand_facts ::
    "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p::linorder, 'c::linorder) findex \<Rightarrow> ('p, 'c) dl_fact list"
  where
  "cand_facts al a idx =
     (case determined_ids al (snd a) of
        [] \<Rightarrow> plookup (fx_p idx) (fst a)
      | dets \<Rightarrow> shortest (map (\<lambda>(j, v). alookup (fx_a idx) (fst a) j v) dets))"

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

text \<open>Generalised forcing lemma for @{const determined_ids}: every determined position it reports
  is carried by any fact whose arguments match at @{term al}. Mirrors @{thm first_bound_match_gen}
  but ranges over all determined positions, not just the leftmost.\<close>
lemma determined_ids_match:
  "(j, v) \<in> set (determined_ids al ids) \<Longrightarrow> match_ids_al al ids ds = Some r \<Longrightarrow> j < length ds \<and> ds ! j = v"
proof (induct ids arbitrary: al ds r j v)
  case Nil then show ?case by simp
next
  case (Cons i ids)
  from Cons.prems(2) obtain d ds' where ds: "ds = d # ds'" by (cases ds) auto
  from Cons.prems(2) ds obtain al' where mi: "match_id_al al i d = Some al'"
    and rec: "match_ids_al al' ids ds' = Some r" by (auto split: option.splits)
  have IH: "\<And>j' v'. (j', v') \<in> set (determined_ids al' ids) \<Longrightarrow> j' < length ds' \<and> ds' ! j' = v'"
    using Cons.hyps rec by blast
  \<comment> \<open>The recursive determined positions of @{term ids} depend on @{term al}, but every position
     bound under @{term al} stays bound under the extended @{term al'}; so we can transport them.\<close>
  have det_mono: "set (determined_ids al ids) \<subseteq> set (determined_ids al' ids)"
  proof (induct ids)
    case Nil then show ?case by simp
  next
    case (Cons k ks)
    show ?case
    proof (cases k)
      case (Cst c)
      then show ?thesis using Cons.hyps by auto
    next
      case (Var y)
      show ?thesis
      proof (cases "map_of al y")
        case None
        then show ?thesis using Var Cons.hyps by (auto split: option.splits)
      next
        case (Some w)
        then have "map_of al' y = Some w" using match_id_al_mono[OF mi] by blast
        then show ?thesis using Var Some Cons.hyps by auto
      qed
    qed
  qed
  show ?case
  proof (cases i)
    case (Cst c)
    show ?thesis
    proof (cases "(j, v) = (0, c)")
      case True
      from mi Cst have "d = c" by (auto split: if_splits)
      with True ds show ?thesis by simp
    next
      case False
      with Cst Cons.prems(1) obtain j' where jv: "(j, v) = (Suc j', v)"
        and mem: "(j', v) \<in> set (determined_ids al ids)"
        by (auto split: prod.splits)
      from IH[OF subsetD[OF det_mono mem]] jv ds show ?thesis by simp
    qed
  next
    case (Var x)
    show ?thesis
    proof (cases "map_of al x")
      case (Some w)
      show ?thesis
      proof (cases "(j, v) = (0, w)")
        case True
        have "map_of al x = Some w" using Some by simp
        with mi Var have "d = w" by (auto split: if_splits option.splits)
        with True ds show ?thesis by simp
      next
        case False
        with Var Some Cons.prems(1) obtain j' where jv: "(j, v) = (Suc j', v)"
          and mem: "(j', v) \<in> set (determined_ids al ids)"
          by (auto split: prod.splits)
        from IH[OF subsetD[OF det_mono mem]] jv ds show ?thesis by simp
      qed
    next
      case None
      with Var Cons.prems(1) obtain j' where jv: "(j, v) = (Suc j', v)"
        and mem: "(j', v) \<in> set (determined_ids al ids)"
        by (auto split: prod.splits)
      from IH[OF subsetD[OF det_mono mem]] jv ds show ?thesis by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>Lemma A\<close>: filtering the index-selected candidates yields exactly the matches of the
  full fact scan. The reorder/index refinement of the body join rests entirely on this.\<close>
lemma match_facts_idx_eq:
  "set (match_facts_idx al a (build_findex facts)) = set (match_facts_al al a facts)"
proof -
  let ?C = "cand_facts al a (build_findex facts)"
  let ?bkt = "\<lambda>(j, v). alookup (build_aidx facts) (fst a) j v"
  have sub: "set ?C \<subseteq> set facts"
  proof (cases "determined_ids al (snd a)")
    case Nil
    then show ?thesis by (simp add: cand_facts_def build_findex_def plookup_build_sound)
  next
    case (Cons d dets)
    then have C: "?C = shortest (map ?bkt (d # dets))"
      by (simp add: cand_facts_def build_findex_def)
    have "?C \<in> set (map ?bkt (d # dets))"
      using shortest_mem[of "map ?bkt (d # dets)"] C by simp
    then obtain jv where jv: "jv \<in> set (d # dets)" and Ceq: "?C = ?bkt jv"
      unfolding set_map by blast
    show ?thesis using Ceq by (cases jv) (simp add: alookup_build_sound)
  qed
  have comp: "f \<in> set ?C" if f: "f \<in> set facts" and m: "match_atom_al al a f = Some y" for f y
  proof -
    from m have pa: "fst a = fst f" and mi: "match_ids_al al (snd a) (snd f) = Some y"
      by (auto simp: match_atom_al_def split: if_splits)
    show "f \<in> set ?C"
    proof (cases "determined_ids al (snd a)")
      case Nil
      then have "?C = plookup (build_pidx facts) (fst a)"
        by (simp add: cand_facts_def build_findex_def)
      moreover have "f \<in> set (plookup (build_pidx facts) (fst f))"
        using plookup_build_complete[OF f] .
      ultimately show ?thesis using pa by simp
    next
      case (Cons d dets)
      then have C: "?C = shortest (map ?bkt (d # dets))"
        by (simp add: cand_facts_def build_findex_def)
      have inbkt: "f \<in> set (?bkt jv)" if "jv \<in> set (d # dets)" for jv
      proof -
        obtain j v where jv: "jv = (j, v)" by (cases jv)
        with that Cons have "(j, v) \<in> set (determined_ids al (snd a))" by simp
        from determined_ids_match[OF this mi] have jl: "j < length (snd f)" and vj: "snd f ! j = v"
          by simp_all
        have "f \<in> set (alookup (build_aidx facts) (fst f) j (snd f ! j))"
          using alookup_build_complete[OF f jl] .
        then show ?thesis using pa vj jv by simp
      qed
      have "?C \<in> set (map ?bkt (d # dets))"
        using shortest_mem[of "map ?bkt (d # dets)"] C by simp
      then obtain jv where mem: "jv \<in> set (d # dets)" and sh: "?C = ?bkt jv"
        unfolding set_map by blast
      show ?thesis using sh inbkt[OF mem] by simp
    qed
  qed
  show ?thesis
    unfolding match_facts_idx_def match_facts_al_def set_map_filter_eq using sub comp by blast
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


subsection \<open>Permutation invariance of the body join (as a set of substitution maps)\<close>

text \<open>Domain bookkeeping for the matcher: matching an id (resp. an id list, resp. a body atom)
  adds bindings for exactly the variables it meets and no others.\<close>

lemma match_id_al_dom:
  "match_id_al al i d = Some al' \<Longrightarrow> dom (map_of al') = dom (map_of al) \<union> set (id_vars_list i)"
  by (cases i) (auto split: option.splits if_splits)

lemma match_ids_al_dom:
  "match_ids_al al ids ds = Some al'
     \<Longrightarrow> dom (map_of al') = dom (map_of al) \<union> set (concat (map id_vars_list ids))"
proof (induct al ids ds arbitrary: al' rule: match_ids_al.induct)
  case (2 al i is' d ds)
  from "2.prems" obtain al2 where a2: "match_id_al al i d = Some al2"
    and rest: "match_ids_al al2 is' ds = Some al'" by (auto split: option.splits)
  from "2.hyps"[OF a2 rest] match_id_al_dom[OF a2] show ?case by auto
qed (auto split: option.splits)

lemma match_atom_al_dom:
  "match_atom_al al a f = Some al'
     \<Longrightarrow> dom (map_of al') = dom (map_of al) \<union> set (concat (map id_vars_list (snd a)))"
  using match_ids_al_dom[of al "snd a" "snd f" al']
  by (auto simp: match_atom_al_def split: if_splits)

text \<open>Soundness companion to @{thm body_join_complete}: every assignment produced by the join
  extends @{term al0}, has domain exactly @{term al0}'s domain together with the variables of all
  the joined atoms, and grounds every joined atom into @{term facts}.\<close>
lemma body_join_sound:
  "al \<in> set (body_join al0 atoms facts) \<Longrightarrow>
     map_of al0 \<subseteq>\<^sub>m map_of al
     \<and> dom (map_of al) = dom (map_of al0) \<union> (\<Union>a\<in>set atoms. set (concat (map id_vars_list (snd a))))
     \<and> (\<forall>a \<in> set atoms. subst_atom (\<lambda>x. the (map_of al x)) a \<in> set facts)"
proof (induct atoms arbitrary: al0)
  case Nil then show ?case by simp
next
  case (Cons a atoms)
  from Cons.prems obtain al1 where al1: "al1 \<in> set (match_facts_al al0 a facts)"
    and alin: "al \<in> set (body_join al1 atoms facts)" by auto
  from al1 obtain f where f: "f \<in> set facts" and m1: "match_atom_al al0 a f = Some al1"
    by (auto simp: match_facts_al_def List.map_filter_def split: if_splits)
  from match_atom_al_spec[OF m1]
  have le01: "map_of al0 \<subseteq>\<^sub>m map_of al1"
    and rep1: "subst_atom (\<lambda>x. the (map_of al1 x)) a = f" by auto
  have dom1: "dom (map_of al1) = dom (map_of al0) \<union> set (concat (map id_vars_list (snd a)))"
    using match_atom_al_dom[OF m1] .
  from Cons.hyps[OF alin]
  have le1: "map_of al1 \<subseteq>\<^sub>m map_of al"
    and dom: "dom (map_of al) = dom (map_of al1) \<union> (\<Union>a\<in>set atoms. set (concat (map id_vars_list (snd a))))"
    and gr: "\<forall>a \<in> set atoms. subst_atom (\<lambda>x. the (map_of al x)) a \<in> set facts" by auto
  have le: "map_of al0 \<subseteq>\<^sub>m map_of al" using le01 le1 by (rule map_le_trans)
  \<comment> \<open>the head atom's instance is preserved under the extended assignment (agrees on its vars)\<close>
  have repa: "subst_atom (\<lambda>x. the (map_of al x)) a = f"
  proof (rule subst_atom_agree[THEN trans, OF _ rep1], intro ballI)
    fix i x assume i: "i \<in> set (snd a)" and x: "x \<in> set (id_vars_list i)"
    then have "x \<in> set (concat (map id_vars_list (snd a)))" by auto
    then have "x \<in> dom (map_of al1)" using dom1 by blast
    then have "map_of al x = map_of al1 x" using le1 by (auto simp: map_le_def dom_def)
    thus "the (map_of al x) = the (map_of al1 x)" by simp
  qed
  have domC: "dom (map_of al) = dom (map_of al0) \<union> (\<Union>a\<in>set (a # atoms). set (concat (map id_vars_list (snd a))))"
    using dom dom1 by auto
  have grC: "\<forall>a' \<in> set (a # atoms). subst_atom (\<lambda>x. the (map_of al x)) a' \<in> set facts"
    using repa f gr by auto
  show ?case using le domC grC by blast
qed

text \<open>Order-independent characterisation of the join's substitution SET viewed through
  @{const map_of}: the image is exactly the maps that extend @{term al0}, whose domain is
  @{term al0}'s domain plus the variables of all atoms, and that ground every atom into
  @{term facts}. Every conjunct on the right depends only on @{term "set atoms"}, so the
  characterisation --- and hence the image --- is manifestly permutation invariant.\<close>
lemma body_join_map_of_char:
  "(\<lambda>al. map_of al) ` set (body_join al0 atoms facts) =
     {m. map_of al0 \<subseteq>\<^sub>m m
         \<and> dom m = dom (map_of al0) \<union> (\<Union>a\<in>set atoms. set (concat (map id_vars_list (snd a))))
         \<and> (\<forall>a \<in> set atoms. subst_atom (\<lambda>x. the (m x)) a \<in> set facts)}"
  (is "?L = ?R")
proof (intro equalityI subsetI)
  fix m assume "m \<in> ?L"
  then obtain al where al: "al \<in> set (body_join al0 atoms facts)" and meq: "m = map_of al" by auto
  show "m \<in> ?R" using body_join_sound[OF al] meq by simp
next
  fix m assume mR: "m \<in> ?R"
  then have mle0: "map_of al0 \<subseteq>\<^sub>m m"
    and dm: "dom m = dom (map_of al0) \<union> (\<Union>a\<in>set atoms. set (concat (map id_vars_list (snd a))))"
    and gr: "\<forall>a \<in> set atoms. subst_atom (\<lambda>x. the (m x)) a \<in> set facts" by auto
  define \<sigma> where "\<sigma> = (\<lambda>x. the (m x))"
  have gr\<sigma>: "\<forall>a \<in> set atoms. subst_atom \<sigma> a \<in> set facts" using gr by (simp add: \<sigma>_def)
  have cons0: "\<forall>x d. map_of al0 x = Some d \<longrightarrow> \<sigma> x = d"
    using mle0 by (auto simp: map_le_def dom_def \<sigma>_def)
  from body_join_complete[OF gr\<sigma> cons0] obtain al where
    al: "al \<in> set (body_join al0 atoms facts)"
    and ext_al: "\<forall>x d. map_of al0 x = Some d \<longrightarrow> map_of al x = Some d"
    and cons_al: "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
    and bind_al: "\<forall>a \<in> set atoms. \<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x)"
    by blast
  from body_join_sound[OF al]
  have le0: "map_of al0 \<subseteq>\<^sub>m map_of al"
    and dom_al: "dom (map_of al) = dom (map_of al0) \<union> (\<Union>a\<in>set atoms. set (concat (map id_vars_list (snd a))))"
    by auto
  have "map_of al = m"
  proof (rule ext)
    fix x
    show "map_of al x = m x"
    proof (cases "x \<in> dom (map_of al0)")
      case True
      then obtain d where d: "map_of al0 x = Some d" by auto
      have "map_of al x = Some d" using ext_al d by blast
      moreover have "m x = Some d" using mle0 d by (auto simp: map_le_def dom_def)
      ultimately show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "x \<in> dom m")
        case True
        then have xv: "x \<in> (\<Union>a\<in>set atoms. set (concat (map id_vars_list (snd a))))"
          using dm False by blast
        then obtain a where "a \<in> set atoms" and "x \<in> set (concat (map id_vars_list (snd a)))" by blast
        then have "map_of al x = Some (\<sigma> x)" using bind_al by blast
        moreover have "m x = Some (\<sigma> x)" using True by (auto simp: \<sigma>_def)
        ultimately show ?thesis by simp
      next
        case False
        then have "x \<notin> dom (map_of al)" using dom_al dm by blast
        then show ?thesis using False by (auto simp: dom_def)
      qed
    qed
  qed
  then show "m \<in> ?L" using al by (auto simp del: body_join.simps)
qed

text \<open>\<^bold>\<open>Permutation invariance of the body join\<close>: reordering the body atoms leaves the SET of
  substitution maps produced by the join unchanged. Immediate from the order-independent
  characterisation @{thm body_join_map_of_char}, since @{prop "mset atoms = mset atoms'"} forces
  @{prop "set atoms = set atoms'"}.\<close>
lemma body_join_map_of_perm:
  assumes "mset atoms = mset atoms'"
  shows "(\<lambda>al. map_of al) ` set (body_join al0 atoms facts)
           = (\<lambda>al. map_of al) ` set (body_join al0 atoms' facts)"
proof -
  have "set atoms = set atoms'" using assms by (metis set_mset_mset)
  then show ?thesis by (simp add: body_join_map_of_char)
qed

subsection \<open>Most-constrained-first reordering of the body atoms\<close>

text \<open>Reorder a clause's body atoms so that atoms with fewer variable (unbound-at-seed) arguments
  come first: a constant argument is determined at the seed @{term "al = []"}, a variable is not, so
  sorting ascending by the number of variable arguments puts the most-constrained atoms first and
  keeps a seed atom from fanning out before a constraining atom prunes it. As a @{const sort_key} this
  is a permutation of the atoms, so by @{thm body_join_map_of_perm} the join enumerates the same SET
  of substitution maps.\<close>

definition reorder_atoms :: "('p, 'x, 'c) lh list \<Rightarrow> ('p, 'x, 'c) lh list" where
  "reorder_atoms atoms = sort_key (\<lambda>a. length (filter is_Var (snd a))) atoms"

lemma mset_reorder_atoms: "mset (reorder_atoms atoms) = mset atoms"
  by (simp add: reorder_atoms_def)

text \<open>The safe-branch per-assignment predicate depends on @{term al} only through @{term "map_of al"}:
  @{const eval_guard_al} does (via @{const subst_id_al}, whose only use of @{term al} is
  @{term "map_of al"}) and the head instance @{term "subst_atom (\<lambda>x. the (map_of al x)) lh"} does
  manifestly. Hence the predicate is a congruence for equal @{const map_of} images.\<close>

lemma subst_id_al_map_of_cong:
  "map_of al = map_of al' \<Longrightarrow> subst_id_al al i = subst_id_al al' i"
  by (cases i) simp_all

lemma eval_guard_al_map_of_cong:
  assumes "map_of al = map_of al'"
  shows "eval_guard_al al g = eval_guard_al al' g"
  using subst_id_al_map_of_cong[OF assms] by (cases g) simp_all

text \<open>A @{const list_all} over a predicate that factors through @{const map_of} depends on the list
  only through the @{const map_of}-image of its element set. Lets us transport the check between two
  atom orderings once their join images agree.\<close>

lemma list_all_map_of_cong:
  assumes cong: "\<And>al al'. map_of al = map_of al' \<Longrightarrow> P al = P al'"
    and img: "(\<lambda>al. map_of al) ` set xs = (\<lambda>al. map_of al) ` set ys"
  shows "list_all P xs = list_all P ys"
proof -
  have "(\<forall>al\<in>set xs. P al) = (\<forall>al\<in>set ys. P al)"
  proof (intro iffI ballI)
    fix al assume "\<forall>al\<in>set xs. P al" and "al \<in> set ys"
    then have "map_of al \<in> (\<lambda>al. map_of al) ` set xs" using img by auto
    then obtain al' where "al' \<in> set xs" and "map_of al' = map_of al" by auto
    then show "P al" using \<open>\<forall>al\<in>set xs. P al\<close> cong by metis
  next
    fix al assume "\<forall>al\<in>set ys. P al" and "al \<in> set xs"
    then have "map_of al \<in> (\<lambda>al. map_of al) ` set ys" using img by auto
    then obtain al' where "al' \<in> set ys" and "map_of al' = map_of al" by auto
    then show "P al" using \<open>\<forall>al\<in>set ys. P al\<close> cong by metis
  qed
  then show ?thesis by (simp add: list_all_iff)
qed

text \<open>The fast closure check: identical to @{const dl_closure_check_exec} except that the safe branch
  reorders the body atoms most-constrained-first and drives the join through the index. Only the
  executable term changes; the soundness bridge @{thm dl_closure_check_exec_imp} mentions only the
  abstract @{const dl_closure_check_exec} and is untouched.\<close>

definition dl_closure_check_exec_fast ::
    "('p::linorder, 'x, 'c::linorder) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_closure_check_exec_fast Pl Ul c =
     (let idx = build_findex (dl_cert_facts c) in
      list_all (\<lambda>cl.
       if clause_safe_exec cl
       then list_all (\<lambda>al.
              list_all (eval_guard_al al) (cls_guards cl)
              \<longrightarrow> subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl) \<in> set (dl_cert_facts c))
              (body_join_idx [] (reorder_atoms (cls_body_atoms cl)) idx)
       else list_all (\<lambda>\<sigma>.
              (list_all (\<lambda>g. eval_guard \<sigma> g) (cls_guards cl)
               \<and> list_all (\<lambda>a. subst_atom \<sigma> a \<in> set (dl_cert_facts c)) (cls_body_atoms cl))
              \<longrightarrow> subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c))
              (cls_substs Ul cl))
       Pl)"

text \<open>The safe-branch check is invariant under the most-constrained-first reindexing: the indexed join
  over the reordered atoms visits the same SET of substitution maps as the abstract join over the
  original atoms (@{thm body_join_idx_eq}, @{thm body_join_map_of_perm} via the permutation
  @{thm mset_reorder_atoms}), and the per-assignment predicate factors through @{const map_of}
  (@{thm eval_guard_al_map_of_cong}), so @{thm list_all_map_of_cong} carries the check across.\<close>
lemma safe_branch_reorder_idx_eq:
  "list_all (\<lambda>al.
      list_all (eval_guard_al al) gs
      \<longrightarrow> subst_atom (\<lambda>x. the (map_of al x)) lh \<in> set facts)
     (body_join_idx [] (reorder_atoms atoms) (build_findex facts))
   = list_all (\<lambda>al.
      list_all (eval_guard_al al) gs
      \<longrightarrow> subst_atom (\<lambda>x. the (map_of al x)) lh \<in> set facts)
     (body_join [] atoms facts)"
  (is "list_all ?P _ = _")
proof -
  have pcong: "?P al = ?P al'" if eq: "map_of al = map_of al'" for al al'
  proof -
    have "list_all (eval_guard_al al) gs = list_all (eval_guard_al al') gs"
      by (rule list_all_cong[OF refl]) (simp add: eval_guard_al_map_of_cong[OF eq])
    moreover have "subst_atom (\<lambda>x. the (map_of al x)) lh = subst_atom (\<lambda>x. the (map_of al' x)) lh"
      using eq by simp
    ultimately show ?thesis by simp
  qed
  have img: "(\<lambda>al. map_of al) ` set (body_join [] (reorder_atoms atoms) facts)
             = (\<lambda>al. map_of al) ` set (body_join [] atoms facts)"
    using body_join_map_of_perm[OF mset_reorder_atoms] .
  have "list_all ?P (body_join_idx [] (reorder_atoms atoms) (build_findex facts))
        = list_all ?P (body_join [] (reorder_atoms atoms) facts)"
    by (simp add: list_all_iff body_join_idx_eq)
  also have "\<dots> = list_all ?P (body_join [] atoms facts)"
    using list_all_map_of_cong[OF pcong img] .
  finally show ?thesis .
qed

lemma dl_closure_check_exec_fast_eq:
  "dl_closure_check_exec Pl Ul c = dl_closure_check_exec_fast Pl Ul c"
  unfolding dl_closure_check_exec_def dl_closure_check_exec_fast_def Let_def
  by (simp add: safe_branch_reorder_idx_eq)

text \<open>Install the fast join as the code equation for @{const dl_closure_check_exec}, replacing its
  linear-scan equation.\<close>
declare dl_closure_check_exec_def [code del]
declare dl_closure_check_exec_fast_eq [code]

declare cand_facts_def [code] match_facts_idx_def [code]
        dl_closure_check_exec_fast_def [code]

end
