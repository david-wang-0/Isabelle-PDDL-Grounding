theory Datalog_Evaluation_Fixpoint
  imports Datalog_Evaluation
begin

section \<open>Counter-free fixpoint evaluation (needs a termination proof)\<close>

text \<open>This is the \<^emph>\<open>fuel-free\<close> sibling of \<^const>\<open>dl_eval\<close>. Where \<^const>\<open>dl_iterate\<close> runs the
  immediate-consequence operator a \<^emph>\<open>fixed\<close> number of times --- structural recursion on an explicit
  \<^typ>\<open>nat\<close> counter, so it terminates trivially with no proof obligation --- \<^const>\<open>dl_saturate\<close>
  instead iterates \<^const>\<open>dl_step\<close> until it stops producing new facts (a genuine fixpoint test
  \<open>set (dl_step U Pl facts) = set facts\<close>).

  That recursion is \<^emph>\<open>not\<close> structural: each call recurses on \<^term>\<open>dl_step U Pl facts\<close>, which is a
  \<^emph>\<open>larger\<close> fact list, so Isabelle cannot guess a termination order. We must supply one: the measure
  is the number of head-facts not yet derived, \<^term>\<open>card (set (all_head_facts U Pl) - set facts)\<close>.
  Because \<^const>\<open>dl_step\<close> is monotone and every new fact lies in the finite \<^const>\<open>all_head_facts\<close>,
  this measure strictly decreases on every recursive call --- that is the content of the
  \<^theory_text>\<open>termination\<close> proof below.

  Once termination is discharged we recover the same guarantees as the counted version: every fact
  it returns is \<^const>\<open>datalog_prog.derivable\<close> (\<open>dl_saturate_sound\<close>), proved by relating each run to
  some \<^term>\<open>dl_iterate n\<close> and reusing \<open>dl_iterate_sound\<close>.\<close>

subsection \<open>Facts about a single round needed for termination\<close>

text \<open>One round only ever adds facts.\<close>
lemma dl_step_mono:
  "set facts \<subseteq> set (dl_step U Pl facts)"
  unfolding dl_step_def by auto

text \<open>The facts after one round are exactly the old ones plus every clause's fireable heads.\<close>
lemma dl_step_set:
  "set (dl_step U Pl facts) = set facts \<union> (\<Union>cl \<in> set Pl. set (fireable_heads U cl facts))"
  unfolding dl_step_def by auto

text \<open>Every head a clause can fire is one of the program's potential head-facts.\<close>
lemma fireable_heads_subset_all_head_facts:
  assumes "cl \<in> set Pl"
  shows "set (fireable_heads U cl facts) \<subseteq> set (all_head_facts U Pl)"
proof
  fix f assume "f \<in> set (fireable_heads U cl facts)"
  then obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (cls_substs U cl)"
    and feq: "f = subst_atom \<sigma> (the_lh cl)"
    unfolding fireable_heads_def by auto
  have "f \<in> set (map (\<lambda>\<sigma>. subst_atom \<sigma> (the_lh cl)) (cls_substs U cl))"
    using \<sigma> feq by simp
  thus "f \<in> set (all_head_facts U Pl)"
    using assms unfolding all_head_facts_def by auto
qed

text \<open>Hence one round stays within the finite upper bound \<^const>\<open>all_head_facts\<close> (modulo the seed).\<close>
lemma dl_step_subset_all_head_facts:
  "set (dl_step U Pl facts) \<subseteq> set facts \<union> set (all_head_facts U Pl)"
proof
  fix f assume "f \<in> set (dl_step U Pl facts)"
  hence "f \<in> set facts \<or> (\<exists>cl \<in> set Pl. f \<in> set (fireable_heads U cl facts))"
    using dl_step_set by blast
  thus "f \<in> set facts \<union> set (all_head_facts U Pl)"
    using fireable_heads_subset_all_head_facts by blast
qed

subsection \<open>The fuel-free evaluator and its termination proof\<close>

function dl_saturate ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_saturate U Pl facts =
     (if set (dl_step U Pl facts) = set facts
      then facts
      else dl_saturate U Pl (dl_step U Pl facts))"
  by pat_completeness auto

termination dl_saturate
proof (relation "measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts))")
  show "wf (measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts)))"
    by simp
next
  fix U Pl facts
  assume neq: "set (dl_step U Pl facts) \<noteq> set facts"
  have mono: "set facts \<subseteq> set (dl_step U Pl facts)"
    by (rule dl_step_mono)
  have psub_sets: "set facts \<subset> set (dl_step U Pl facts)"
    using mono neq by auto
  obtain x where "x \<in> set (dl_step U Pl facts) - set facts"
    using psubset_imp_ex_mem[OF psub_sets] by blast
  hence x_in: "x \<in> set (dl_step U Pl facts)"
    and x_out: "x \<notin> set facts"
    by auto
  have x_head: "x \<in> set (all_head_facts U Pl)"
    using x_in x_out dl_step_subset_all_head_facts by blast
  have psub: "set (all_head_facts U Pl) - set (dl_step U Pl facts)
                \<subset> set (all_head_facts U Pl) - set facts"
  proof (rule psubsetI)
    show "set (all_head_facts U Pl) - set (dl_step U Pl facts)
            \<subseteq> set (all_head_facts U Pl) - set facts"
      using mono by blast
  next
    show "set (all_head_facts U Pl) - set (dl_step U Pl facts)
            \<noteq> set (all_head_facts U Pl) - set facts"
    proof
      assume eq: "set (all_head_facts U Pl) - set (dl_step U Pl facts)
                    = set (all_head_facts U Pl) - set facts"
      have "x \<in> set (all_head_facts U Pl) - set facts"
        using x_head x_out by blast
      hence "x \<in> set (all_head_facts U Pl) - set (dl_step U Pl facts)"
        using eq by simp
      thus False using x_in by blast
    qed
  qed
  have fin: "finite (set (all_head_facts U Pl) - set facts)"
    by simp
  have "card (set (all_head_facts U Pl) - set (dl_step U Pl facts))
          < card (set (all_head_facts U Pl) - set facts)"
    by (rule psubset_card_mono[OF fin psub])
  thus "((U, Pl, dl_step U Pl facts), (U, Pl, facts))
          \<in> measure (\<lambda>(U, Pl, facts). card (set (all_head_facts U Pl) - set facts))"
    by simp
qed

text \<open>Keep the recursive equation out of the default simp set (it would loop) and expose it as a
  one-step unfolding rule plus a code equation.\<close>
declare dl_saturate.simps [simp del, code]

lemma dl_saturate_unfold:
  "dl_saturate U Pl facts =
     (if set (dl_step U Pl facts) = set facts then facts else dl_saturate U Pl (dl_step U Pl facts))"
  by (rule dl_saturate.simps)

text \<open>The seeded entry point, mirroring \<^const>\<open>dl_eval\<close>.\<close>
definition dl_saturate_eval ::
  "'c list \<Rightarrow> ('p, 'x, 'c) clause list \<Rightarrow> ('p, 'c) dl_fact list" where
  "dl_saturate_eval U Pl = dl_saturate U Pl []"

declare dl_saturate_eval_def [code]

subsection \<open>Soundness, via the counted evaluator\<close>

text \<open>Every saturation run coincides with running \<^const>\<open>dl_iterate\<close> for some number of rounds, so
  soundness reduces to \<open>dl_iterate_sound\<close>.\<close>
lemma dl_saturate_eq_iterate:
  "\<exists>n. dl_saturate U Pl facts = dl_iterate n U Pl facts"
proof (induction U Pl facts rule: dl_saturate.induct)
  case (1 U Pl facts)
  show ?case
  proof (cases "set (dl_step U Pl facts) = set facts")
    case True
    have "dl_saturate U Pl facts = facts"
      using True dl_saturate_unfold[of U Pl facts] by simp
    moreover have "dl_iterate 0 U Pl facts = facts"
      by simp
    ultimately show ?thesis by metis
  next
    case False
    obtain n where n: "dl_saturate U Pl (dl_step U Pl facts) = dl_iterate n U Pl (dl_step U Pl facts)"
      using "1.IH"[OF False] by blast
    have "dl_saturate U Pl facts = dl_saturate U Pl (dl_step U Pl facts)"
      using False dl_saturate_unfold[of U Pl facts] by simp
    also have "... = dl_iterate n U Pl (dl_step U Pl facts)"
      using n by simp
    also have "... = dl_iterate (Suc n) U Pl facts"
      by simp
    finally show ?thesis by blast
  qed
qed

theorem dl_saturate_sound:
  assumes "\<And>g. g \<in> set facts \<Longrightarrow> datalog_prog.derivable (set U) (set Pl) g"
      and "f \<in> set (dl_saturate U Pl facts)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
proof -
  obtain n where eq: "dl_saturate U Pl facts = dl_iterate n U Pl facts"
    using dl_saturate_eq_iterate by blast
  have "f \<in> set (dl_iterate n U Pl facts)"
    using assms(2) eq by simp
  thus ?thesis using dl_iterate_sound[OF assms(1)] by blast
qed

theorem dl_saturate_eval_sound:
  assumes "f \<in> set (dl_saturate_eval U Pl)"
  shows "datalog_prog.derivable (set U) (set Pl) f"
proof -
  have base: "datalog_prog.derivable (set U) (set Pl) g" if "g \<in> set []" for g
    using that by simp
  show ?thesis
    using dl_saturate_sound[OF base] assms unfolding dl_saturate_eval_def by blast
qed

end
