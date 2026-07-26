theory Datalog_Certificate_Code
  imports Datalog_Certificate
begin

section \<open>Executable refinement of the certificate checker\<close>

text \<open>The abstract checker of \<^theory>\<open>Datalog_Certification.Datalog_Certificate\<close> quantifies over the
  program \<open>P\<close> and universe \<open>U\<close> as \<^emph>\<open>sets\<close> and witnesses foundedness with an abstract \<open>\<exists>rank\<close>.
  This theory adds the \<open>[code]\<close>-executable refinement: a left-to-right ordered-certificate scan for
  foundedness, list-presentation checks for rule-validity / closure that enumerate
  \<^const>\<open>cls_substs\<close> (as the forward-chaining evaluator's \<open>fireable_heads\<close> does), and the assembled
  \<open>dl_certified_model_exec\<close> with its soundness bridge to the abstract checker (hence, via
  \<open>dl_certified_model_correct\<close>, to \<^const>\<open>datalog_prog.derivable\<close>). Only the soundness
  direction (exec \<open>\<Longrightarrow>\<close> abstract) is needed for trust.\<close>

subsection \<open>Executable foundedness (ordered-certificate scan)\<close>

text \<open>\<^bold>\<open>Executable foundedness\<close> (\<open>dl_founded_exec\<close>): the ordered-certificate refinement of
  \<^const>\<open>dl_founded\<close>. The untrusted engine emits the rules in derivation (topological) order; the
  checker scans them left to right, requiring each rule's body to lie among the heads of the
  \<^emph>\<open>strictly earlier\<close> rules. This is decidable (no \<open>\<exists>rank\<close>) and refines \<^const>\<open>dl_founded\<close>
  with the rank taken to be a rule's position in the list (a body fact, being an earlier head, has a
  strictly smaller first-occurrence index). The verified cycle-detecting DFS that reconstructs the
  rank from an \<^emph>\<open>unordered\<close> certificate is a further, independent refinement onto the same
  \<^const>\<open>dl_founded\<close> --- now realised downstream as \<open>dl_acyclic_dfs\<close> / \<open>dl_certified_model_dfs\<close>
  (session \<open>Datalog_Graph\<close>, theory \<open>Datalog_Cycle_DFS\<close>), which the deployed grounder
  (\<open>plan_by_cert_dfs\<close> / \<open>ground_via_cert_prop_dfs_e\<close>) uses in place of this ordered scan. So
  \<open>dl_founded_exec\<close> here and the \<open>dl_certified_model_exec\<close> entry point below are the fast path
  retained for a certificate that already carries a trusted derivation order --- \<^emph>\<open>superseded in
  the deployed (DFS) pipeline\<close> by that variant.\<close>

fun dl_founded_scan :: "('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_ground_rule list \<Rightarrow> bool" where
  "dl_founded_scan acc [] = True"
| "dl_founded_scan acc (r # rs) =
     (list_all (\<lambda>b. b \<in> set acc) (gr_body r) \<and> dl_founded_scan (gr_head r # acc) rs)"

definition dl_founded_exec :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_founded_exec c = dl_founded_scan [] (dl_rules c)"

declare dl_founded_scan.simps [code] dl_founded_exec_def [code]

text \<open>Locality of the scan: after a successful scan, rule \<open>i\<close>'s body lies in the initial
  accumulator together with the heads of the rules strictly before \<open>i\<close>.\<close>
lemma dl_founded_scan_body:
  assumes "dl_founded_scan acc rs" and "i < length rs"
  shows "set (gr_body (rs ! i)) \<subseteq> set acc \<union> gr_head ` set (take i rs)"
  using assms
proof (induction rs arbitrary: acc i)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  show ?case
  proof (cases i)
    case 0
    have "\<forall>b \<in> set (gr_body r). b \<in> set acc"
      using Cons.prems(1) by (simp add: list.pred_set)
    then show ?thesis using 0 by auto
  next
    case (Suc k)
    have scan': "dl_founded_scan (gr_head r # acc) rs" using Cons.prems(1) by simp
    have k: "k < length rs" using Cons.prems(2) Suc by simp
    have "set (gr_body (rs ! k)) \<subseteq> set (gr_head r # acc) \<union> gr_head ` set (take k rs)"
      using Cons.IH[OF scan' k] .
    then show ?thesis using Suc by auto
  qed
qed

text \<open>The refinement: an ordered, scan-checked certificate is founded, with rank = first index.\<close>
lemma dl_founded_exec_imp_dl_founded:
  assumes "dl_founded_exec c"
  shows "dl_founded c"
proof -
  define rs where "rs = dl_rules c"
  have scan: "dl_founded_scan [] rs" using assms unfolding dl_founded_exec_def rs_def .
  define rank where
    "rank f = (LEAST i. i < length rs \<and> gr_head (rs ! i) = f)" for f
  have facts_eq: "set (dl_cert_facts c) = gr_head ` set rs"
    unfolding dl_cert_facts_def rs_def by auto
  have main: "\<exists>r \<in> set (dl_rules c). gr_head r = f \<and> set (gr_body r) \<subseteq> set (dl_cert_facts c)
                \<and> (\<forall>b \<in> set (gr_body r). rank b < rank f)"
    if f: "f \<in> set (dl_cert_facts c)" for f
  proof -
    obtain j where jP: "j < length rs \<and> gr_head (rs ! j) = f"
      using f facts_eq by (auto simp: in_set_conv_nth)
    have P: "rank f < length rs \<and> gr_head (rs ! (rank f)) = f"
      unfolding rank_def using jP by (rule LeastI)
    let ?r = "rs ! (rank f)"
    have hd: "gr_head ?r = f" using P by simp
    have rmem: "?r \<in> set (dl_rules c)" using P unfolding rs_def by simp
    have body_sub: "set (gr_body ?r) \<subseteq> gr_head ` set (take (rank f) rs)"
      using dl_founded_scan_body[OF scan, of "rank f"] P by simp
    have body_cf: "set (gr_body ?r) \<subseteq> set (dl_cert_facts c)"
    proof -
      have "set (gr_body ?r) \<subseteq> gr_head ` set rs"
        using body_sub image_mono[OF set_take_subset] by (rule subset_trans)
      then show ?thesis unfolding facts_eq .
    qed
    have rank_lt: "rank b < rank f" if b: "b \<in> set (gr_body ?r)" for b
    proof -
      have "b \<in> gr_head ` set (take (rank f) rs)" using b body_sub by blast
      then obtain r' where r': "r' \<in> set (take (rank f) rs)" and hr': "gr_head r' = b"
        by auto
      obtain m where m: "m < length (take (rank f) rs)" and rm: "take (rank f) rs ! m = r'"
        using r' by (auto simp: in_set_conv_nth)
      have mlt: "m < rank f" using m by (auto simp: min_def split: if_splits)
      have "rs ! m = r'" using rm mlt by (metis nth_take)
      then have mb: "m < length rs \<and> gr_head (rs ! m) = b" using mlt P hr' by simp
      have "rank b \<le> m" unfolding rank_def using mb by (rule Least_le)
      then show ?thesis using mlt by simp
    qed
    show ?thesis using hd rmem body_cf rank_lt by blast
  qed
  show ?thesis unfolding dl_founded_def using main by blast
qed

subsection \<open>Executable refinement of the checks\<close>

text \<open>The abstract checks quantify over the program \<open>P\<close> and universe \<open>U\<close> as \<^emph>\<open>sets\<close>. Here we add
  \<open>[code]\<close>-executable versions over \<^emph>\<open>list\<close> presentations \<open>Pl\<close> / \<open>Ul\<close> (\<open>P = set Pl\<close>, \<open>U = set Ul\<close>),
  enumerating the grounding substitutions with \<^const>\<open>cls_substs\<close> (as the forward-chaining
  evaluator's \<open>fireable_heads\<close> does), and prove each refines its set-level counterpart. Only the \<^emph>\<open>soundness\<close> direction
  (exec \<open>\<Longrightarrow>\<close> abstract) is needed for trust: an accepted executable certificate is accepted by the
  abstract checker,  hence by \<open>dl_certified_model_correct\<close> its facts are exactly the derivable
  ones.\<close>

definition dl_positive_prog_exec :: "('p, 'x, 'c) clause list \<Rightarrow> bool" where
  "dl_positive_prog_exec Pl = list_all (\<lambda>cl. list_all is_pos_rh (the_rhs cl)) Pl"

subsection \<open>Reading a substitution off a ground rule (assoc-list, no \<open>\<sigma>\<close> function)\<close>

text \<open>For rule validity the substitution is fully determined by the ground rule: read it
  positionally off \<open>the_lh cl # cls_body_atoms cl\<close> against \<open>gr_head r # gr_body r\<close> as an
  association list, checking consistency (a repeated variable must agree). No \<open>('x \<Rightarrow> 'c)\<close>
  function is built or applied in the executable path --- only \<^const>\<open>map_of\<close> look-ups.\<close>

fun match_id_al :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id \<Rightarrow> 'c \<Rightarrow> ('x \<times> 'c) list option" where
  "match_id_al al (id.Cst c) d = (if c = d then Some al else None)"
| "match_id_al al (id.Var x) d =
     (case map_of al x of Some c \<Rightarrow> (if c = d then Some al else None) | None \<Rightarrow> Some ((x, d) # al))"

fun match_ids_al :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id list \<Rightarrow> 'c list \<Rightarrow> ('x \<times> 'c) list option" where
  "match_ids_al al [] [] = Some al"
| "match_ids_al al (i # is') (d # ds) =
     (case match_id_al al i d of Some al' \<Rightarrow> match_ids_al al' is' ds | None \<Rightarrow> None)"
| "match_ids_al al _ _ = None"

definition match_atom_al :: "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p, 'c) dl_fact \<Rightarrow> ('x \<times> 'c) list option" where
  "match_atom_al al a f = (if fst a = fst f then match_ids_al al (snd a) (snd f) else None)"

fun match_atoms_al :: "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('x \<times> 'c) list option" where
  "match_atoms_al al [] [] = Some al"
| "match_atoms_al al (a # as') (f # fs') =
     (case match_atom_al al a f of Some al' \<Rightarrow> match_atoms_al al' as' fs' | None \<Rightarrow> None)"
| "match_atoms_al al _ _ = None"

fun subst_id_al :: "('x \<times> 'c) list \<Rightarrow> ('x, 'c) id \<Rightarrow> 'c" where
  "subst_id_al al (id.Cst c) = c"
| "subst_id_al al (id.Var x) = the (map_of al x)"

fun eval_guard_al :: "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) rh \<Rightarrow> bool" where
  "eval_guard_al al (Eql a b) = (subst_id_al al a = subst_id_al al b)"
| "eval_guard_al al (Neql a b) = (subst_id_al al a \<noteq> subst_id_al al b)"
| "eval_guard_al al _ = True"

definition dl_rule_valid_exec :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_ground_rule \<Rightarrow> bool" where
  "dl_rule_valid_exec Pl Ul r =
     list_ex (\<lambda>cl.
        case match_atoms_al [] (the_lh cl # cls_body_atoms cl) (gr_head r # gr_body r) of
          None \<Rightarrow> False
        | Some al \<Rightarrow>
            list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set Ul | None \<Rightarrow> False) (cls_vars cl)
            \<and> list_all (eval_guard_al al) (cls_guards cl))
       Pl"

text \<open>\<^bold>\<open>Order-independent list-based rule validity\<close>: the abstract set-based \<^const>\<open>dl_rule_valid\<close>
  presented on \<^emph>\<open>list\<close> arguments. The executable admissibility checks use this (in place of the
  order-\<^emph>\<open>sensitive\<close> \<^const>\<open>dl_rule_valid_exec\<close>); its executable code equation is the indexed checker
  in the downstream theory \<open>Datalog_Certificate_Code_Index\<close>. Being definitionally the abstract
  check, it is order-independent and both sound \<^emph>\<open>and\<close> complete against it.\<close>
definition dl_rule_valid_oi ::
    "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_ground_rule \<Rightarrow> bool" where
  "dl_rule_valid_oi Pl Ul r \<equiv>
     (\<exists>cl \<in> set Pl. \<exists>\<sigma>. (\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul)
        \<and> (\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
        \<and> gr_head r = subst_atom \<sigma> (the_lh cl)
        \<and> set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl)))"

lemma dl_rule_valid_oi_eq: "dl_rule_valid_oi Pl Ul r = dl_rule_valid (set Pl) (set Ul) r"
  unfolding dl_rule_valid_oi_def dl_rule_valid_def by (rule refl)

definition match_facts_al :: "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('x \<times> 'c) list list" where
  "match_facts_al al a facts = List.map_filter (match_atom_al al a) facts"

fun body_join :: "('x \<times> 'c) list \<Rightarrow> ('p, 'x, 'c) lh list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('x \<times> 'c) list list" where
  "body_join al [] facts = [al]"
| "body_join al (a # as') facts = concat (map (\<lambda>al'. body_join al' as' facts) (match_facts_al al a facts))"

definition clause_safe_exec :: "('p, 'x, 'c) clause \<Rightarrow> bool" where
  "clause_safe_exec cl =
     list_all (\<lambda>x. list_ex (\<lambda>a. x \<in> set (concat (map id_vars_list (snd a)))) (cls_body_atoms cl)) (cls_vars cl)"

text \<open>Closure check: for a SAFE clause enumerate only the substitutions that map the body into the
  certificate facts (a fact-driven join over the body atoms --- cost \<open>\<propto>\<close> matching tuples, not
  \<open>|U|^k\<close>); fall back to the full \<open>cls_substs\<close> enumeration only for the (non-datalog) unsafe case, so
  the soundness refinement stays unconditional.\<close>
definition dl_closure_check_exec :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_closure_check_exec Pl Ul c =
     list_all (\<lambda>cl.
       if clause_safe_exec cl
       then list_all (\<lambda>al.
              list_all (eval_guard_al al) (cls_guards cl)
              \<longrightarrow> subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl) \<in> set (dl_cert_facts c))
              (body_join [] (cls_body_atoms cl) (dl_cert_facts c))
       else list_all (\<lambda>\<sigma>.
              (list_all (\<lambda>g. eval_guard \<sigma> g) (cls_guards cl)
               \<and> list_all (\<lambda>a. subst_atom \<sigma> a \<in> set (dl_cert_facts c)) (cls_body_atoms cl))
              \<longrightarrow> subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c))
              (cls_substs Ul cl))
       Pl"

definition dl_admissible_exec :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_admissible_exec Pl Ul c =
     (dl_positive_prog_exec Pl
      \<and> list_all (dl_rule_valid_oi Pl Ul) (dl_rules c)
      \<and> dl_closure_check_exec Pl Ul c
      \<and> dl_founded_exec c)"

definition dl_certified_model_exec :: "('p, 'x, 'c) clause list \<Rightarrow> 'c list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_certified_model_exec Pl Ul M c = (dl_admissible_exec Pl Ul c \<and> set M = set (dl_cert_facts c))"

declare dl_positive_prog_exec_def [code] dl_rule_valid_exec_def [code]
        dl_closure_check_exec_def [code] dl_admissible_exec_def [code]
        dl_certified_model_exec_def [code]

text \<open>Any \<open>U\<close>-valued substitution agrees on the clause variables with a tabulated one from
  \<^const>\<open>cls_substs\<close> --- the bridge from the abstract \<open>\<forall>\<sigma>\<close> to the enumerated list.\<close>
lemma cls_substs_tabulate:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul"
  obtains \<sigma>' where "\<sigma>' \<in> set (cls_substs Ul cl)"
    and "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
proof -
  let ?\<sigma>' = "subst_of (cls_vars cl) (map \<sigma> (cls_vars cl))"
  have "?\<sigma>' \<in> set (cls_substs Ul cl)"
    unfolding cls_substs_iff
    using assms by (auto simp: image_subset_iff intro!: exI[where x = "map \<sigma> (cls_vars cl)"])
  moreover have "\<forall>x \<in> set (cls_vars cl). ?\<sigma>' x = \<sigma> x"
    by (simp add: subst_of_map)
  ultimately show ?thesis using that by blast
qed

text \<open>Agreement on the clause variables transfers head, body-atom and guard instances.\<close>
lemma subst_atom_head_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
  shows "subst_atom \<sigma>' (the_lh cl) = subst_atom \<sigma> (the_lh cl)"
  using assms by (intro subst_atom_agree) (auto dest: cls_vars_head_vars)

lemma subst_atom_body_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x" and "a \<in> set (cls_body_atoms cl)"
  shows "subst_atom \<sigma>' a = subst_atom \<sigma> a"
proof (intro subst_atom_agree ballI)
  fix i x assume i: "i \<in> set (snd a)" and xi: "x \<in> set (id_vars_list i)"
  have "PosLit (fst a) (snd a) \<in> set (the_rhs cl)"
    using assms(2) cls_body_atoms_iff by blast
  moreover have "x \<in> set (rh_vars_list (PosLit (fst a) (snd a)))"
    using i xi by auto
  ultimately have "x \<in> set (cls_vars cl)" by (rule cls_vars_rhs_vars)
  then show "\<sigma>' x = \<sigma> x" using assms(1) by blast
qed

lemma eval_guard_cls_cong:
  assumes "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x" and "g \<in> set (cls_guards cl)"
  shows "eval_guard \<sigma>' g = eval_guard \<sigma> g"
proof (intro eval_guard_agree ballI)
  fix x assume x: "x \<in> set (rh_vars_list g)"
  have "g \<in> set (the_rhs cl)" using assms(2) by (auto simp: cls_guards_def)
  then have "x \<in> set (cls_vars cl)" using x by (rule cls_vars_rhs_vars)
  then show "\<sigma>' x = \<sigma> x" using assms(1) by blast
qed

text \<open>\<^bold>\<open>Positivity\<close> refines.\<close>
lemma dl_positive_prog_exec_iff: "dl_positive_prog_exec Pl = dl_positive_prog (set Pl)"
  by (simp add: dl_positive_prog_exec_def dl_positive_prog_def list_all_iff)

text \<open>The assoc-list guard/subst evaluators coincide with the \<open>\<sigma>\<close>-function ones for
  \<open>\<sigma> = \<lambda>x. the (map_of al x)\<close> --- the bridge used only inside the soundness proof.\<close>
lemma subst_id_al_eq: "subst_id_al al i = subst_id (\<lambda>x. the (map_of al x)) i"
  by (cases i) auto

lemma eval_guard_al_eq: "eval_guard_al al g = eval_guard (\<lambda>x. the (map_of al x)) g"
  by (cases g) (auto simp: subst_id_al_eq)

text \<open>Matching only ever \<^emph>\<open>extends\<close> the bindings (\<open>map_of\<close>-monotone), and a matched id/atom is
  reproduced by the resulting bindings.\<close>
lemma match_id_al_mono:
  "match_id_al al i d = Some al' \<Longrightarrow> map_of al \<subseteq>\<^sub>m map_of al'"
  by (cases i) (auto simp: map_le_def split: option.splits if_splits)

lemma match_id_al_correct:
  "match_id_al al i d = Some al'
     \<Longrightarrow> subst_id (\<lambda>x. the (map_of al' x)) i = d \<and> (\<forall>x. i = id.Var x \<longrightarrow> map_of al' x \<noteq> None)"
  by (cases i) (auto split: option.splits if_splits)

text \<open>The id-list match extends the bindings, binds every matched variable, and reproduces the
  constant list under the resulting substitution.\<close>
lemma match_ids_al_spec:
  "match_ids_al al ids ds = Some al'
     \<Longrightarrow> map_of al \<subseteq>\<^sub>m map_of al'
       \<and> (\<forall>x \<in> set (concat (map id_vars_list ids)). map_of al' x \<noteq> None)
       \<and> map (subst_id (\<lambda>x. the (map_of al' x))) ids = ds"
proof (induction al ids ds arbitrary: al' rule: match_ids_al.induct)
  case (2 al i is' d ds)
  from "2.prems" obtain al2 where a2: "match_id_al al i d = Some al2"
    and rest: "match_ids_al al2 is' ds = Some al'"
    by (auto split: option.splits)
  from "2.IH"[OF a2 rest]
  have le2: "map_of al2 \<subseteq>\<^sub>m map_of al'"
    and bndT: "\<forall>x \<in> set (concat (map id_vars_list is')). map_of al' x \<noteq> None"
    and repT: "map (subst_id (\<lambda>x. the (map_of al' x))) is' = ds" by auto
  from match_id_al_mono[OF a2] le2 have le: "map_of al \<subseteq>\<^sub>m map_of al'" by (rule map_le_trans)
  from match_id_al_correct[OF a2]
  have drep2: "subst_id (\<lambda>x. the (map_of al2 x)) i = d"
    and bnd2: "\<forall>x. i = id.Var x \<longrightarrow> map_of al2 x \<noteq> None" by auto
  have agree_i: "the (map_of al' x) = the (map_of al2 x)" if "x \<in> set (id_vars_list i)" for x
    using that bnd2 le2 by (cases i) (auto simp: map_le_def dom_def)
  have headbnd: "\<forall>x \<in> set (id_vars_list i). map_of al' x \<noteq> None"
    using bnd2 le2 by (cases i) (auto simp: map_le_def dom_def)
  have drep: "subst_id (\<lambda>x. the (map_of al' x)) i = d"
    using drep2 agree_i by (cases i) auto
  have bnd: "\<forall>x \<in> set (concat (map id_vars_list (i # is'))). map_of al' x \<noteq> None"
    using headbnd bndT by auto
  show ?case using le drep repT bnd by simp
qed (auto simp: map_le_def)

text \<open>The atom-level match reproduces the fact and binds the atom's variables.\<close>
lemma match_atom_al_spec:
  "match_atom_al al a f = Some al'
     \<Longrightarrow> map_of al \<subseteq>\<^sub>m map_of al'
       \<and> (\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al' x \<noteq> None)
       \<and> subst_atom (\<lambda>x. the (map_of al' x)) a = f"
  using match_ids_al_spec[of al "snd a" "snd f"]
  by (auto simp: match_atom_al_def subst_atom_def split: if_splits)

text \<open>The atom-list match positionally reproduces the fact list under the resulting substitution.\<close>
lemma match_atoms_al_spec:
  "match_atoms_al al as fs = Some al'
     \<Longrightarrow> map_of al \<subseteq>\<^sub>m map_of al' \<and> map (subst_atom (\<lambda>x. the (map_of al' x))) as = fs"
proof (induction al as fs arbitrary: al' rule: match_atoms_al.induct)
  case (2 al a as' f fs')
  from "2.prems" obtain al2 where a2: "match_atom_al al a f = Some al2"
    and rest: "match_atoms_al al2 as' fs' = Some al'"
    by (auto split: option.splits)
  from "2.IH"[OF a2 rest] have le2: "map_of al2 \<subseteq>\<^sub>m map_of al'"
    and repT: "map (subst_atom (\<lambda>x. the (map_of al' x))) as' = fs'" by auto
  from match_atom_al_spec[OF a2]
  have le0: "map_of al \<subseteq>\<^sub>m map_of al2"
    and bnd2: "\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al2 x \<noteq> None"
    and hrep2: "subst_atom (\<lambda>x. the (map_of al2 x)) a = f" by auto
  have le: "map_of al \<subseteq>\<^sub>m map_of al'" using le0 le2 by (rule map_le_trans)
  have "subst_atom (\<lambda>x. the (map_of al' x)) a = subst_atom (\<lambda>x. the (map_of al2 x)) a"
  proof (intro subst_atom_agree ballI)
    fix i x assume i: "i \<in> set (snd a)" and x: "x \<in> set (id_vars_list i)"
    from i x have "x \<in> set (concat (map id_vars_list (snd a)))" by auto
    with bnd2 have "map_of al2 x \<noteq> None" by blast
    with le2 have "map_of al' x = map_of al2 x" by (auto simp: map_le_def dom_def)
    thus "the (map_of al' x) = the (map_of al2 x)" by simp
  qed
  hence hrep: "subst_atom (\<lambda>x. the (map_of al' x)) a = f" using hrep2 by simp
  show ?case using le hrep repT by simp
qed (auto simp: map_le_def)

text \<open>\<^bold>\<open>Rule validity\<close> refines: a matched clause yields a genuine \<open>U\<close>-valued substitution
  \<open>\<sigma> = \<lambda>x. the (map_of al x)\<close> (built only here, as the existential witness).\<close>
lemma dl_rule_valid_exec_imp:
  assumes "dl_rule_valid_exec Pl Ul r"
  shows "dl_rule_valid (set Pl) (set Ul) r"
proof -
  from assms obtain cl al where
    cl: "cl \<in> set Pl" and
    m: "match_atoms_al [] (the_lh cl # cls_body_atoms cl) (gr_head r # gr_body r) = Some al" and
    U: "list_all (\<lambda>x. case map_of al x of Some c \<Rightarrow> c \<in> set Ul | None \<Rightarrow> False) (cls_vars cl)" and
    G: "list_all (eval_guard_al al) (cls_guards cl)"
    unfolding dl_rule_valid_exec_def by (auto simp: list_ex_iff split: option.splits)
  define \<sigma> where "\<sigma> = (\<lambda>x. the (map_of al x))"
  from match_atoms_al_spec[OF m]
  have rep: "map (subst_atom \<sigma>) (the_lh cl # cls_body_atoms cl) = gr_head r # gr_body r"
    by (simp add: \<sigma>_def)
  from rep have hd: "gr_head r = subst_atom \<sigma> (the_lh cl)" by simp
  from rep have "map (subst_atom \<sigma>) (cls_body_atoms cl) = gr_body r" by simp
  hence bd: "set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl))" by simp
  have Uv: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul"
    using U by (auto simp: list_all_iff \<sigma>_def split: option.splits)
  have Gv: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
    using G by (auto simp: list_all_iff eval_guard_al_eq \<sigma>_def)
  from cl Uv Gv hd bd show ?thesis unfolding dl_rule_valid_def by blast
qed

text \<open>\<^bold>\<open>Join completeness\<close>: matching a whole rhs predicate against a fact (fixing all its
  arguments at once) captures every substitution consistent with the current bindings; the
  atom-list join then captures every \<open>\<sigma>\<close> that maps the body into the facts.\<close>
lemma match_id_al_complete:
  assumes "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
  shows "\<exists>al'. match_id_al al i (subst_id \<sigma> i) = Some al'
             \<and> (\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al' x = Some d)
             \<and> (\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d)
             \<and> (\<forall>x \<in> set (id_vars_list i). map_of al' x = Some (\<sigma> x))"
proof (cases i)
  case (Cst c)
  then show ?thesis using assms by (intro exI[where x=al]) auto
next
  case (Var x)
  show ?thesis
  proof (cases "map_of al x")
    case None
    with Var show ?thesis using assms by (intro exI[where x="(x, \<sigma> x) # al"]) auto
  next
    case (Some d)
    with assms have "\<sigma> x = d" by blast
    with Var Some assms show ?thesis by (intro exI[where x=al]) auto
  qed
qed

lemma match_ids_al_complete:
  assumes "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
  shows "\<exists>al'. match_ids_al al ids (map (subst_id \<sigma>) ids) = Some al'
             \<and> (\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al' x = Some d)
             \<and> (\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d)
             \<and> (\<forall>x \<in> set (concat (map id_vars_list ids)). map_of al' x = Some (\<sigma> x))"
  using assms
proof (induction ids arbitrary: al)
  case Nil then show ?case by auto
next
  case (Cons i ids)
  from match_id_al_complete[OF Cons.prems, of i]
  obtain al1 where m1: "match_id_al al i (subst_id \<sigma> i) = Some al1"
    and ext1: "\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al1 x = Some d"
    and cons1: "\<forall>x d. map_of al1 x = Some d \<longrightarrow> \<sigma> x = d"
    and bind1: "\<forall>x \<in> set (id_vars_list i). map_of al1 x = Some (\<sigma> x)" by blast
  from Cons.IH[OF cons1] obtain al' where
    m': "match_ids_al al1 ids (map (subst_id \<sigma>) ids) = Some al'"
    and ext': "\<forall>x d. map_of al1 x = Some d \<longrightarrow> map_of al' x = Some d"
    and cons': "\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d"
    and bind': "\<forall>x \<in> set (concat (map id_vars_list ids)). map_of al' x = Some (\<sigma> x)" by blast
  have bindi: "\<forall>x \<in> set (id_vars_list i). map_of al' x = Some (\<sigma> x)" using bind1 ext' by blast
  show ?case
  proof (intro exI[where x=al'] conjI)
    show "match_ids_al al (i # ids) (map (subst_id \<sigma>) (i # ids)) = Some al'" using m1 m' by simp
    show "\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al' x = Some d" using ext1 ext' by blast
    show "\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d" using cons' .
    show "\<forall>x \<in> set (concat (map id_vars_list (i # ids))). map_of al' x = Some (\<sigma> x)"
      using bindi bind' by auto
  qed
qed

lemma match_atom_al_complete:
  assumes "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
  shows "\<exists>al'. match_atom_al al a (subst_atom \<sigma> a) = Some al'
             \<and> (\<forall>x d. map_of al x = Some d \<longrightarrow> map_of al' x = Some d)
             \<and> (\<forall>x d. map_of al' x = Some d \<longrightarrow> \<sigma> x = d)
             \<and> (\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al' x = Some (\<sigma> x))"
  using match_ids_al_complete[OF assms, of "snd a"]
  by (simp add: match_atom_al_def subst_atom_def)

lemma body_join_complete:
  assumes "\<forall>a \<in> set atoms. subst_atom \<sigma> a \<in> set facts"
    and "\<forall>x d. map_of al0 x = Some d \<longrightarrow> \<sigma> x = d"
  shows "\<exists>al \<in> set (body_join al0 atoms facts).
           (\<forall>x d. map_of al0 x = Some d \<longrightarrow> map_of al x = Some d)
           \<and> (\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d)
           \<and> (\<forall>a \<in> set atoms. \<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x))"
  using assms
proof (induction atoms arbitrary: al0)
  case Nil then show ?case by auto
next
  case (Cons a atoms)
  have fa: "subst_atom \<sigma> a \<in> set facts" using Cons.prems(1) by simp
  from match_atom_al_complete[OF Cons.prems(2), of a]
  obtain al1 where m1: "match_atom_al al0 a (subst_atom \<sigma> a) = Some al1"
    and ext1: "\<forall>x d. map_of al0 x = Some d \<longrightarrow> map_of al1 x = Some d"
    and cons1: "\<forall>x d. map_of al1 x = Some d \<longrightarrow> \<sigma> x = d"
    and bind1: "\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al1 x = Some (\<sigma> x)" by blast
  have al1in: "al1 \<in> set (match_facts_al al0 a facts)"
    using m1 fa by (force simp: match_facts_al_def List.map_filter_def)
  have rest_facts: "\<forall>a \<in> set atoms. subst_atom \<sigma> a \<in> set facts" using Cons.prems(1) by simp
  from Cons.IH[OF rest_facts cons1] obtain al where
    alin: "al \<in> set (body_join al1 atoms facts)"
    and ext': "\<forall>x d. map_of al1 x = Some d \<longrightarrow> map_of al x = Some d"
    and cons': "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d"
    and bind': "\<forall>a \<in> set atoms. \<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x)" by blast
  have binda: "\<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x)"
    using bind1 ext' by blast
  show ?case
  proof (intro bexI[where x=al] conjI)
    show "\<forall>x d. map_of al0 x = Some d \<longrightarrow> map_of al x = Some d" using ext1 ext' by blast
    show "\<forall>x d. map_of al x = Some d \<longrightarrow> \<sigma> x = d" using cons' .
    show "\<forall>a' \<in> set (a # atoms). \<forall>x \<in> set (concat (map id_vars_list (snd a'))). map_of al x = Some (\<sigma> x)"
      using binda bind' by auto
    show "al \<in> set (body_join al0 (a # atoms) facts)" using alin al1in by auto
  qed
qed

text \<open>\<^bold>\<open>Closure check\<close> refines: an arbitrary \<open>U\<close>-valued substitution is handled via its tabulated
  agree-partner.\<close>
lemma dl_closure_check_exec_imp:
  assumes "dl_closure_check_exec Pl Ul c"
  shows "dl_closure_check (set Pl) (set Ul) c"
  unfolding dl_closure_check_def
proof (intro ballI allI impI)
  fix cl \<sigma>
  assume cl: "cl \<in> set Pl"
    and rng: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set Ul"
    and hyp: "(\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
              \<and> (\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set (dl_cert_facts c))"
  from hyp have gsig: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
    and bsig: "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set (dl_cert_facts c)" by simp_all
  show "subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c)"
  proof (cases "clause_safe_exec cl")
    case False \<comment> \<open>unsafe: fall back to the full \<open>cls_substs\<close> enumeration (old argument)\<close>
    obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> set (cls_substs Ul cl)"
      and ag: "\<forall>x \<in> set (cls_vars cl). \<sigma>' x = \<sigma> x"
      using cls_substs_tabulate[OF rng] by blast
    have gd: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma>' g"
      using gsig ag by (simp add: eval_guard_cls_cong)
    have bd: "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma>' a \<in> set (dl_cert_facts c)"
      using bsig ag by (simp add: subst_atom_body_cong)
    have "subst_atom \<sigma>' (the_lh cl) \<in> set (dl_cert_facts c)"
      using assms cl False \<sigma>' gd bd unfolding dl_closure_check_exec_def by (auto simp: list_all_iff)
    then show ?thesis using subst_atom_head_cong[OF ag] by simp
  next
    case True \<comment> \<open>safe: the fact-driven join captures \<open>\<sigma>\<close> (agrees on all clause variables)\<close>
    have empty_cons: "\<forall>x d. map_of [] x = Some d \<longrightarrow> \<sigma> x = d" by simp
    obtain al where alin: "al \<in> set (body_join [] (cls_body_atoms cl) (dl_cert_facts c))"
      and albind: "\<forall>a \<in> set (cls_body_atoms cl).
                     \<forall>x \<in> set (concat (map id_vars_list (snd a))). map_of al x = Some (\<sigma> x)"
      using body_join_complete[OF bsig empty_cons] by auto
    have safe: "\<forall>x \<in> set (cls_vars cl). \<exists>a \<in> set (cls_body_atoms cl). x \<in> set (concat (map id_vars_list (snd a)))"
      using True unfolding clause_safe_exec_def by (simp add: list_all_iff list_ex_iff)
    have agall: "\<forall>x \<in> set (cls_vars cl). map_of al x = Some (\<sigma> x)"
    proof
      fix x assume x: "x \<in> set (cls_vars cl)"
      then obtain a where a: "a \<in> set (cls_body_atoms cl)"
        and xa: "x \<in> set (concat (map id_vars_list (snd a)))"
        using safe by blast
      show "map_of al x = Some (\<sigma> x)" using albind a xa by blast
    qed
    have ag: "\<forall>x \<in> set (cls_vars cl). (\<lambda>x. the (map_of al x)) x = \<sigma> x" using agall by simp
    have gd: "list_all (eval_guard_al al) (cls_guards cl)"
      unfolding list_all_iff
    proof
      fix g assume g: "g \<in> set (cls_guards cl)"
      have "eval_guard_al al g = eval_guard \<sigma> g"
        by (simp add: eval_guard_al_eq eval_guard_cls_cong[OF ag g])
      then show "eval_guard_al al g" using gsig g by simp
    qed
    have "subst_atom (\<lambda>x. the (map_of al x)) (the_lh cl) \<in> set (dl_cert_facts c)"
      using assms cl True alin gd unfolding dl_closure_check_exec_def by (auto simp: list_all_iff)
    then show ?thesis using subst_atom_head_cong[OF ag] by simp
  qed
qed

text \<open>\<^bold>\<open>Admissibility\<close> and the \<^bold>\<open>model-checking entry point\<close> refine, assembling the four checks.\<close>
lemma dl_admissible_exec_imp:
  assumes "dl_admissible_exec Pl Ul c"
  shows "dl_admissible (set Pl) (set Ul) c"
proof -
  have pos: "dl_positive_prog_exec Pl"
    and rv: "list_all (dl_rule_valid_oi Pl Ul) (dl_rules c)"
    and cc: "dl_closure_check_exec Pl Ul c"
    and fd: "dl_founded_exec c"
    using assms unfolding dl_admissible_exec_def by auto
  have "dl_positive_prog (set Pl)" using pos by (simp add: dl_positive_prog_exec_iff)
  moreover have "\<forall>r \<in> set (dl_rules c). dl_rule_valid (set Pl) (set Ul) r"
    using rv by (auto simp: list_all_iff dl_rule_valid_oi_eq)
  moreover have "dl_closure_check (set Pl) (set Ul) c"
    using cc by (rule dl_closure_check_exec_imp)
  moreover have "dl_founded c" using fd by (rule dl_founded_exec_imp_dl_founded)
  ultimately show ?thesis unfolding dl_admissible_def by blast
qed

theorem dl_certified_model_exec_imp:
  assumes "dl_certified_model_exec Pl Ul M c"
  shows "dl_certified_model (set Pl) (set Ul) M c"
  using assms dl_admissible_exec_imp
  unfolding dl_certified_model_exec_def dl_certified_model_def by blast

text \<open>\<^bold>\<open>Capstone (executable):\<close> an accepted executable certificate's facts are exactly the derivable
  facts of the program.\<close>
corollary dl_certified_model_exec_correct:
  assumes "dl_certified_model_exec Pl Ul M c"
  shows "set M = {f. datalog_prog.derivable (set Ul) (set Pl) f}"
  using dl_certified_model_correct[OF dl_certified_model_exec_imp[OF assms]] .

end
