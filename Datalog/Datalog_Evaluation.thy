theory Datalog_Evaluation
  imports Datalog_Sema_Supplement
begin

section \<open>Executable least-model evaluation for positive datalog programs\<close>

text \<open>An executable forward-chaining (semi-naive-style) evaluator that computes the least model
  \<^const>\<open>datalog_prog.derivable\<close> of a datalog program \<open>set Pl\<close> over a finite constant universe
  \<open>set U\<close>, both given as lists. It is the generic, PDDL-free analogue of the retired
  \<open>ast_classical_problem.semi_naive_eval\<close>: forward-chaining of the immediate-consequence operator
  to a fixpoint.

  The evaluator is an \<^emph>\<open>oracle\<close> --- in the certified pipeline its output is re-validated by the
  certificate checker of theory \<open>Datalog_Certificate\<close>, which is where trust
  lives. We nonetheless prove it \<^emph>\<open>sound\<close>: every fact it returns is genuinely derivable.\<close>

subsection \<open>One round of the immediate-consequence operator\<close>

text \<open>The heads a single clause fires from the current fact set: for every grounding substitution
  over \<open>U\<close> whose guards hold and whose positive body atoms are all present, the (substituted) head.\<close>
definition fireable_heads ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "fireable_heads U cl facts =
     map (\<lambda>\<sigma>. subst_atom \<sigma> (the_lh cl))
       (filter (\<lambda>\<sigma>. (\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g)
                    \<and> (\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set facts))
               (cls_substs U cl))"

text \<open>One immediate-consequence round over the whole program: keep the current facts, add every
  clause's fireable heads.\<close>
definition dl_step ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_step U Pl facts = remdups (facts @ concat (map (\<lambda>cl. fireable_heads U cl facts) Pl))"

text \<open>Every fact any clause could ever produce (the body/guard filter dropped) --- a finite upper
  bound on the model, used to bound the number of fixpoint iterations.\<close>
definition all_head_facts ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list" where
  "all_head_facts U Pl =
     remdups (concat (map (\<lambda>cl. map (\<lambda>\<sigma>. subst_atom \<sigma> (the_lh cl)) (cls_substs U cl)) Pl))"

subsection \<open>Iteration to a fixpoint\<close>

fun dl_iterate ::
  "nat \<Rightarrow> 'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_iterate 0 U Pl facts = facts"
| "dl_iterate (Suc n) U Pl facts = dl_iterate n U Pl (dl_step U Pl facts)"

text \<open>The evaluator: iterate the immediate-consequence operator from no facts. The fact set is a
  subset of the finite \<^const>\<open>all_head_facts\<close> and grows strictly until the fixpoint, so
  \<^term>\<open>length (all_head_facts U Pl)\<close> rounds always suffice.\<close>
definition dl_eval ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_eval U Pl = dl_iterate (length (all_head_facts U Pl)) U Pl []"

declare fireable_heads_def [code] dl_step_def [code] all_head_facts_def [code]
        dl_iterate.simps [code] dl_eval_def [code]

subsection \<open>Soundness: every returned fact is derivable\<close>

text \<open>A single round preserves derivability: if every current fact is derivable, so is every fact
  after one round (each new head is the instance of a program clause over \<open>U\<close> whose guards hold and
  whose body atoms are derivable).\<close>
lemma dl_step_sound:
  assumes IH: "\<And>g. g \<in> set facts \<Longrightarrow> datalog_prog.derivable (set U) (set Pl) g"
      and f: "f \<in> set (dl_step U Pl facts)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
proof -
  have "f \<in> set facts \<or> f \<in> set (concat (map (\<lambda>cl. fireable_heads U cl facts) Pl))"
    using f unfolding dl_step_def by auto
  thus ?thesis
  proof
    assume "f \<in> set facts" thus ?thesis using IH by blast
  next
    assume "f \<in> set (concat (map (\<lambda>cl. fireable_heads U cl facts) Pl))"
    then obtain cl where cl: "cl \<in> set Pl" and fcl: "f \<in> set (fireable_heads U cl facts)"
      by auto
    obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (cls_substs U cl)"
      and guards: "\<forall>g \<in> set (cls_guards cl). eval_guard \<sigma> g"
      and body: "\<forall>a \<in> set (cls_body_atoms cl). subst_atom \<sigma> a \<in> set facts"
      and feq: "f = subst_atom \<sigma> (the_lh cl)"
      using fcl unfolding fireable_heads_def by auto
    have rng: "\<forall>x \<in> set (cls_vars cl). \<sigma> x \<in> set U"
      using \<sigma> by (blast intro: cls_substs_rangeD)
    have bder: "\<forall>a \<in> set (cls_body_atoms cl). datalog_prog.derivable (set U) (set Pl) (subst_atom \<sigma> a)"
      using body IH by blast
    show ?thesis
      using datalog_prog.derivable.derive[OF cl rng guards bder] feq by simp
  qed
qed

lemma dl_iterate_sound:
  assumes "\<And>g. g \<in> set facts \<Longrightarrow> datalog_prog.derivable (set U) (set Pl) g"
      and "f \<in> set (dl_iterate n U Pl facts)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
  using assms
proof (induction n arbitrary: facts)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have step: "datalog_prog.derivable (set U) (set Pl) g" if "g \<in> set (dl_step U Pl facts)" for g
    using Suc.prems(1) that by (blast intro: dl_step_sound)
  have "f \<in> set (dl_iterate n U Pl (dl_step U Pl facts))" using Suc.prems(2) by simp
  thus ?case using Suc.IH[OF step] by blast
qed

theorem dl_eval_sound:
  assumes "f \<in> set (dl_eval U Pl)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
proof -
  have base: "datalog_prog.derivable (set U) (set Pl) g" if "g \<in> set []" for g
    using that by simp
  show ?thesis
    using dl_iterate_sound[OF base] assms unfolding dl_eval_def by blast
qed

end
