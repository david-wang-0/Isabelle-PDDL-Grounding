theory Datalog_Certificate
  imports Datalog_Sema_Supplement
begin

section \<open>Certified models of positive datalog programs\<close>

text \<open>A self-contained certificate checker for \<^emph>\<open>positive\<close> datalog programs phrased in the AFP
  \<^theory>\<open>Stratified_Datalog.Datalog\<close> clause syntax --- independent of any PDDL notion (the PDDL
  reachability certificate in \<open>Reachability_Analysis/PDDL_Reachability_Certificate.thy\<close> is the
  planning-specific analogue; see \<open>ARCHITECTURE_datalog_certification.md\<close>).

  The reference least-model semantics is the abstract assumption-free locale predicate
  \<open>datalog_prog.derivable\<close> (over a constant universe set \<open>U\<close>), defined in \<open>Datalog_Sema_Supplement.thy\<close>;
  here we add a certificate checker over the same set program \<open>P\<close> and universe \<open>U\<close> and prove it exact
  against that semantics. The certificate itself stays a concrete \<^emph>\<open>list\<close> of ground rules; only the
  checks quantify over \<open>P\<close> / \<open>U\<close> as sets (an \<open>eval\<close>-executable refinement that enumerates
  substitutions from list presentations is future work).

  An untrusted engine (e.g. Nemo) claims that a list of ground facts \<open>M\<close> is \<^emph>\<open>the\<close> model of a
  program; it justifies the claim with a certificate that is simply a \<^emph>\<open>list of grounded rule
  instances\<close> --- each a derived head fact together with the ground body facts it was fired from (no
  predecessor indices, no stored order). The certified fact set is the set of rule heads. The
  checker validates, against the program itself:

  \<^item> \<^bold>\<open>rule validity\<close> (\<open>dl_rule_valid\<close>): every supplied ground rule is a genuine ground instance of
    some program clause over the universe --- guards hold, and head/body are the instance of an
    actual clause. This ties the rules back to the original program.
  \<^item> \<^bold>\<open>closure check\<close> (\<open>dl_closure_check\<close>): for every clause and every \<open>U\<close>-valued grounding
    substitution, if the guards hold and the instantiated body is
    inside the certificate facts, the instantiated head is too. So the certificate facts form a
    model, i.e. no extra fact is derivable (\<open>\<supseteq>\<close> the least model).
  \<^item> \<^bold>\<open>foundedness\<close> (\<open>dl_founded\<close>): every certificate fact has \<^emph>\<open>some\<close> supplied rule whose body lies
    in the facts and is strictly lower-ranked --- a well-founded support order, so every fact is
    genuinely derivable (\<open>\<subseteq>\<close> the least model). The rank is an abstract \<open>\<exists>\<close>-witness here; an
    executable cycle-detecting DFS will reconstruct it (left for later).

  Together (theorem \<open>dl_certified_model_correct\<close>): the certified fact set is \<^emph>\<open>exactly\<close> the set
  of derivable facts. Programs containing \<^const>\<open>NegLit\<close> are rejected outright
  (\<open>dl_positive_prog\<close>, fail-closed): with negation the consequence operator is not monotone and
  this checker's argument does not apply.\<close>

subsection \<open>Certificate data structure (list of grounded rules)\<close>

text \<open>A certificate is just a list of \<^emph>\<open>grounded rule instances\<close>: each pairs a derived ground
  \<open>gr_head\<close> fact with the list of ground \<open>gr_body\<close> facts it was fired from (an empty body marks a
  base/EDB fact). No predecessor \<^emph>\<open>indices\<close> and no ordering are stored --- the derivation order is
  recovered separately (the well-foundedness / acyclicity obligation \<open>dl_founded\<close>, to be discharged
  by a cycle-detecting DFS later). The certified fact set \<open>dl_cert_facts\<close> is exactly the rule heads.\<close>

datatype ('p, 'c) dl_ground_rule = DLRule
  (gr_head: "('p, 'c) dl_fact")        \<comment> \<open>the derived ground fact\<close>
  (gr_body: "('p, 'c) dl_fact list")   \<comment> \<open>the ground facts it was fired from (\<open>[]\<close> = base fact)\<close>

datatype ('p, 'c) dl_certificate = DLCert (dl_rules: "('p, 'c) dl_ground_rule list")

definition dl_cert_facts :: "('p, 'c) dl_certificate \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_cert_facts c = remdups (map gr_head (dl_rules c))"

subsection \<open>The checks\<close>

text \<open>\<^bold>\<open>Rule validity\<close> (\<open>dl_rule_valid\<close>): each supplied ground rule is a genuine ground instance of
  some program clause over the universe \<open>U\<close> --- a clause \<open>cl \<in> P\<close> and a substitution \<open>\<sigma>\<close> mapping the
  clause variables into \<open>U\<close> whose guards hold, whose head is \<open>gr_head\<close> and whose body atoms are
  exactly \<open>gr_body\<close>. This ties the supplied rules back to the \<^emph>\<open>original program\<close>; without it a
  bogus rule could found a junk fact.\<close>
definition dl_rule_valid :: "('p, 'x, 'c) dl_program \<Rightarrow> 'c set \<Rightarrow> ('p, 'c) dl_ground_rule \<Rightarrow> bool" where
  "dl_rule_valid P U r \<equiv>
     (\<exists>cl \<in> P. \<exists>\<sigma>. (\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> U)
        \<and> (\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
        \<and> gr_head r = subst_atom \<sigma> (the_lh cl)
        \<and> set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl)))"

text \<open>\<^bold>\<open>Closure check\<close> (\<open>dl_closure_check\<close>): for every clause and every \<open>U\<close>-valued grounding
  substitution, if the guards hold and the instantiated body is inside
  the certificate facts, so is the instantiated head. So the facts form a \<^emph>\<open>model\<close>, i.e. no extra
  fact is derivable (\<open>\<supseteq>\<close> the least model). Order-free.\<close>
definition dl_closure_check :: "('p, 'x, 'c) dl_program \<Rightarrow> 'c set \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_closure_check P U c \<equiv>
     (\<forall>cl \<in> P. \<forall>\<sigma>. (\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> U) \<longrightarrow>
        ((\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
         \<and> (\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set (dl_cert_facts c)))
        \<longrightarrow> subst_atom \<sigma> (the_lh cl) \<in> set (dl_cert_facts c))"

text \<open>A \<^emph>\<open>rank\<close> assigns each ground fact a natural-number derivation depth; a strictly decreasing
  rank along every rule's body edges is exactly what makes the support well-founded (acyclic).\<close>
type_synonym ('p, 'c) dl_rank = "('p, 'c) dl_fact \<Rightarrow> nat"

text \<open>\<^bold>\<open>Foundedness\<close> (\<open>dl_founded\<close>): every certificate fact has \<^emph>\<open>some\<close> supplied rule whose body
  lies in the facts and is strictly lower-ranked --- a well-founded support order witnessing that
  each fact is genuinely derivable (\<open>\<subseteq>\<close> the least model). The \<open>\<exists>rank\<close> is the abstract acyclicity
  obligation; an executable cycle-detecting DFS will later \<^emph>\<open>construct\<close> the rank and refine this.\<close>
definition dl_founded :: "('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_founded c \<equiv>
     (\<exists>rank :: ('p, 'c) dl_rank.
        \<forall>f \<in> set (dl_cert_facts c).
          \<exists>r \<in> set (dl_rules c).
             gr_head r = f
             \<and> set (gr_body r) \<subseteq> set (dl_cert_facts c)
             \<and> (\<forall>b \<in> set (gr_body r). rank b < rank f))"


definition dl_admissible :: "('p, 'x, 'c) dl_program \<Rightarrow> 'c set \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_admissible P U c \<equiv>
     dl_positive_prog P
     \<and> (\<forall>r \<in> set (dl_rules c). dl_rule_valid P U r)
     \<and> dl_closure_check P U c
     \<and> dl_founded c"

text \<open>The model-checking entry point: \<open>M\<close> is certified to be the (universe-restricted) least
  model of \<open>P\<close> iff the certificate is admissible and its facts are exactly \<open>M\<close>.\<close>
definition dl_certified_model :: "('p, 'x, 'c) dl_program \<Rightarrow> 'c set \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_certificate \<Rightarrow> bool" where
  "dl_certified_model P U M c \<equiv> dl_admissible P U c \<and> set M = set (dl_cert_facts c)"

subsection \<open>Correctness\<close>

text \<open>\<^bold>\<open>Closure soundness (\<open>\<supseteq>\<close>):\<close> every derivable fact is in a closure-checked certificate ---
  the certificate facts form a model, and derivability is the least one.\<close>
lemma dl_derivable_in_cert:
  assumes "dl_closure_check P U c"
    and "datalog_prog.derivable U P f"
  shows "f \<in> set (dl_cert_facts c)"
  using assms(2)
proof (induction rule: datalog_prog.derivable.induct[consumes 1, case_names derive])
  case (derive cl \<sigma>)
  have "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set (dl_cert_facts c)"
    using derive.IH by blast
  with derive.hyps(1,2,3) assms(1) show ?case
    unfolding dl_closure_check_def by blast
qed

text \<open>\<^bold>\<open>Foundedness tightness (\<open>\<subseteq>\<close>):\<close> under rule validity and a well-founded support every
  certificate fact is genuinely derivable, by well-founded induction on the \<open>dl_founded\<close> rank ---
  the index \<open>less_induct\<close> of the ordered-graph version, now on the reconstructed rank.\<close>
lemma dl_founded_imp_derivable:
  assumes valid: "\<forall>r \<in> set (dl_rules c). dl_rule_valid P U r"
    and founded: "dl_founded c"
    and f: "f \<in> set (dl_cert_facts c)"
  shows "datalog_prog.derivable U P f"
proof -
  define rank :: "(_, _) dl_rank" where "rank =
    (SOME s. \<forall>f \<in> set (dl_cert_facts c). \<exists>r \<in> set (dl_rules c).
        gr_head r = f \<and> set (gr_body r) \<subseteq> set (dl_cert_facts c)
        \<and> (\<forall>b \<in> set (gr_body r). s b < s f))"
  have rk: "\<forall>f \<in> set (dl_cert_facts c). \<exists>r \<in> set (dl_rules c).
            gr_head r = f \<and> set (gr_body r) \<subseteq> set (dl_cert_facts c)
            \<and> (\<forall>b \<in> set (gr_body r). rank b < rank f)"
    unfolding rank_def using founded[unfolded dl_founded_def] by (rule someI_ex)
  have "\<forall>f \<in> set (dl_cert_facts c). rank f = n \<longrightarrow> datalog_prog.derivable U P f" for n
  proof (induction n rule: less_induct)
    case (less n)
    show ?case
    proof (intro ballI impI)
      fix f assume f: "f \<in> set (dl_cert_facts c)" and rn: "rank f = n"
      from rk f obtain r where r: "r \<in> set (dl_rules c)" and hd: "gr_head r = f"
        and body_in: "set (gr_body r) \<subseteq> set (dl_cert_facts c)"
        and body_rank: "\<forall>b \<in> set (gr_body r). rank b < rank f"
        by blast
      from valid r have "dl_rule_valid P U r" by blast
      then obtain cl \<sigma> where
        cl: "cl \<in> P" and su: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> U" and
        g: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g" and
        hd_eq: "gr_head r = subst_atom \<sigma> (the_lh cl)" and
        bd: "set (gr_body r) = set (map (subst_atom \<sigma>) (cls_body_atoms cl))"
        unfolding dl_rule_valid_def by blast
      have "\<forall>a \<in> set (cls_body_atoms cl). datalog_prog.derivable U P (subst_atom \<sigma> a)"
      proof
        fix a assume "a \<in> set (cls_body_atoms cl)"
        then have mem: "subst_atom \<sigma> a \<in> set (gr_body r)" using bd by auto
        then have inM: "subst_atom \<sigma> a \<in> set (dl_cert_facts c)" using body_in by blast
        from body_rank mem rn have "rank (subst_atom \<sigma> a) < n" by auto
        then show "datalog_prog.derivable U P (subst_atom \<sigma> a)"
          using less.IH inM by blast
      qed
      then have "datalog_prog.derivable U P (subst_atom \<sigma> (the_lh cl))"
        using datalog_prog.derivable.derive[OF cl su g] by blast
      then show "datalog_prog.derivable U P f" using hd hd_eq by simp
    qed
  qed
  with f show ?thesis by blast
qed

text \<open>\<^bold>\<open>Main theorem:\<close> an accepted model is exactly the set of derivable facts.\<close>
theorem dl_certified_model_correct:
  assumes "dl_certified_model P U M c"
  shows "set M = {f. datalog_prog.derivable U P f}"
proof -
  from assms have adm: "dl_admissible P U c" and M: "set M = set (dl_cert_facts c)"
    unfolding dl_certified_model_def by auto
  from adm have cc: "dl_closure_check P U c"
    and valid: "\<forall>r \<in> set (dl_rules c). dl_rule_valid P U r"
    and founded: "dl_founded c"
    unfolding dl_admissible_def by auto
  have "set (dl_cert_facts c) \<subseteq> {f. datalog_prog.derivable U P f}"
    using dl_founded_imp_derivable[OF valid founded] by auto
  moreover have "{f. datalog_prog.derivable U P f} \<subseteq> set (dl_cert_facts c)"
    using dl_derivable_in_cert[OF cc] by auto
  ultimately show ?thesis using M by auto
qed


text \<open>\<^bold>\<open>Relation to the AFP datalog semantics.\<close> The locale \<open>certified_positive_datalog_model\<close>
  extends the supplement's \<^locale>\<open>positive_datalog_universe\<close> (a \<^emph>\<open>positive\<close>, \<^emph>\<open>safe\<close>,
  \<^emph>\<open>head-covered\<close> program \<open>P\<close> over a universe \<open>U\<close>). In it the certified fact set of any admissible
  certificate is exactly the AFP \<^theory>\<open>Stratified_Datalog.Datalog\<close> \<^emph>\<open>least solution\<close> \<open>\<rho>\<close> of \<open>P\<close>
  at the trivial stratification \<open>\<lambda>_. 0\<close> (for a positive program, the \<open>\<subseteq>\<close>-least model):
  \<open>dl_certified_model_correct\<close> identifies it with the locale's \<open>derivable\<close>, and
  \<open>derivable_iff_least_solution\<close> with the least solution.\<close>
locale certified_positive_datalog_model = positive_datalog_universe U P
  for U :: "'c set" and P :: "('p, 'x, 'c) dl_program"
begin

theorem certified_model_is_least_solution:
  assumes "dl_certified_model P U M c"
    and "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t P (\<lambda>_. 0)"
  shows "set M = {(p, r). r \<in> \<rho> p}"
proof -
  have "set M = {f. derivable f}"
    using dl_certified_model_correct[OF assms(1)] by simp
  also have "\<dots> = {(p, r). r \<in> \<rho> p}"
    using derivable_iff_least_solution[OF assms(2)] by auto
  finally show ?thesis .
qed

end

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
     DLRule (STR ''edge'', [1, 2]) [],
     DLRule (STR ''edge'', [2, 3]) [],
     DLRule (STR ''path'', [1, 2]) [(STR ''edge'', [1, 2])],
     DLRule (STR ''path'', [2, 3]) [(STR ''edge'', [2, 3])],
     DLRule (STR ''path'', [1, 3]) [(STR ''edge'', [1, 2]), (STR ''path'', [2, 3])]
   ]"

definition ex_model :: "(String.literal, nat) dl_fact list" where
  "ex_model \<equiv> dl_cert_facts ex_cert"

text \<open>With the program/universe now \<^emph>\<open>sets\<close>, the rule-validity and closure checks are no longer
  \<open>eval\<close>-executable, so only the certificate-local \<open>dl_founded\<close> obligation is exhibited here (plus a
  negative probe). Foundedness needs a witnessing rank --- here the derivation depth: \<open>edge\<close> facts at
  0, one-hop \<open>path\<close> at 1, the two-hop \<open>path (1,3)\<close> at 2 --- since \<open>dl_founded\<close> quantifies
  existentially over ranks; this is what the DFS will reconstruct. An \<open>eval\<close>-checkable refinement of
  the full \<open>dl_admissible\<close> check awaits a list-based instantiation of the universe/program.\<close>
lemma ex_founded: "dl_founded ex_cert"
  unfolding dl_founded_def
  by (rule exI[where x = "\<lambda>f. if fst f = STR ''edge'' then 0::nat else if snd f = [1, 3] then 2 else 1"])
     eval

text \<open>Negative probe: a self-supporting rule breaks foundedness (no well-founded rank exists).\<close>
lemma "\<not> dl_founded (DLCert [DLRule (STR ''p'', [1]) [(STR ''p'', [1])]]
                       :: (String.literal, nat) dl_certificate)"
  unfolding dl_founded_def dl_cert_facts_def by auto

end
