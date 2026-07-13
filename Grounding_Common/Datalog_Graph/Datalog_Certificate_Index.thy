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

text \<open>The fast closure check: identical to @{const dl_closure_check_exec} except that the safe branch
  drives the join through the index. Only the executable term changes; the soundness bridge
  @{thm dl_closure_check_exec_imp} mentions only the abstract @{const dl_closure_check_exec} and is
  untouched.\<close>

definition dl_closure_check_exec_fast ::
    "('p::linorder, 'x, 'c::linorder) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_closure_check_exec_fast Pl Ul c =
     (let idx = build_findex (dl_cert_facts c) in
      list_all (\<lambda>cl.
       if clause_safe_exec cl
       then list_all (\<lambda>al.
              list_all (eval_guard_al al) (cls_guards cl)
              \<longrightarrow> subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl) \<in> set (dl_cert_facts c))
              (body_join_idx [] (cls_body_atoms cl) idx)
       else list_all (\<lambda>\<sigma>.
              (list_all (\<lambda>g. eval_guard \<sigma> g) (cls_guards cl)
               \<and> list_all (\<lambda>a. subst_atom \<sigma> a \<in> set (dl_cert_facts c)) (cls_body_atoms cl))
              \<longrightarrow> subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c))
              (cls_substs Ul cl))
       Pl)"

lemma dl_closure_check_exec_fast_eq:
  "dl_closure_check_exec Pl Ul c = dl_closure_check_exec_fast Pl Ul c"
  unfolding dl_closure_check_exec_def dl_closure_check_exec_fast_def
  by (simp add: list_all_iff body_join_idx_eq Let_def)

text \<open>Install the fast join as the code equation for @{const dl_closure_check_exec}, replacing its
  linear-scan equation.\<close>
declare dl_closure_check_exec_def [code del]
declare dl_closure_check_exec_fast_eq [code]

declare cand_facts_def [code] match_facts_idx_def [code]
        dl_closure_check_exec_fast_def [code]

end
