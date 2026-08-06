theory Classical_Type_Normalization_Num_Free
  imports Classical_Type_Normalization Grounding_Classical_Common.Numeric_Free
begin

section \<open>The type-normalization stage maintains numeric-freeness\<close>

text \<open>Stage-local preservation property, the first link of the input-side numeric-freeness chain
  composed in \<^verbatim>\<open>Grounding_Pipeline_STRIPS\<close>: detyping rewrites types and parameters only. It
  conjoins the generated type preconditions onto every action's precondition and appends the
  supertype facts to the initial state; both are built from \<^const>\<open>domain_signature.type_atom\<close>,
  i.e.\ plain \<^const>\<open>predAtm\<close>s, so nothing numeric enters. The generic ingredients
  (\<open>num_free_fmla_atomsI\<close>, \<open>num_free_fmla_of_predAtom\<close>, \<open>num_free_fmla_BigAnd\<close>,
  \<open>num_free_fmla_BigOr\<close>) live in \<^verbatim>\<open>Classical_PDDL_Sema_Supplement\<close>.\<close>

subsection \<open>Numeric-freeness of the generated type preconditions\<close>

lemma (in domain_signature) num_free_fmla_type_precond: "num_free_fmla (type_precond p)"
proof (cases p rule: type_precond.cases)
  case (1 v ts)
  show ?thesis
    unfolding 1 type_precond.simps
    by (rule num_free_fmla_BigOr) auto
qed

lemma (in domain_signature) num_free_fmla_param_precond: "num_free_fmla (param_precond ps)"
  unfolding param_precond_def
  by (rule num_free_fmla_BigAnd) (auto simp: num_free_fmla_type_precond)

lemma (in domain_signature) num_free_ac_detype_classical_ac:
  assumes "num_free_ac a"
  shows "num_free_ac (detype_classical_ac a)"
  using assms unfolding num_free_ac_def by (simp add: num_free_fmla_param_precond)

subsection \<open>Numeric-freeness of the detyped problem\<close>

text \<open>The restriction assumption \<open>restrict_prob\<close> is what makes the supertype facts well defined ---
  \<^const>\<open>domain_signature.supertype_facts_for\<close> is \<^const>\<open>undefined\<close> on a non-primitive constant type
  --- so it is needed even though detyping itself is numeric-blind.\<close>
lemma (in ast_classical_problem) restrict_prob_sigD:
  assumes restrict_prob
  shows restrict_prob_sig
  using assms unfolding restrict_prob_def restrict_dom_def restrict_prob_sig_def by blast

lemma (in ast_classical_problem) supertype_facts_predAtom':
  assumes rp: restrict_prob
  shows "\<forall>\<phi> \<in> set (supertype_facts all_consts). is_predAtom \<phi>"
proof -
  interpret rp2: restrict_problem_signature
      "types D" "predicates D" "functions D" "consts D" "objects P"
    using restrict_prob_sigD[OF rp] by unfold_locales
  show ?thesis by (rule rp2.supertype_facts_predAtom)
qed

theorem (in ast_classical_problem) detype_prob_num_free:
  assumes rp: restrict_prob
      and nf: num_free_prob
  shows "ast_classical_problem.num_free_prob detype_classical_prob"
proof -
  have dom: "ast_classical_domain.num_free_dom D2"
    unfolding ast_classical_domain.num_free_dom_def
  proof
    fix a assume "a \<in> set (actions D2)"
    then obtain a' where a: "a = detype_classical_ac a'"
      and a'in: "a' \<in> set (actions D)"
      unfolding detype_classical_dom_sel by auto
    have "num_free_ac a'" using nf a'in unfolding num_free_prob_def num_free_dom_def by blast
    thus "num_free_ac a" unfolding a by (rule num_free_ac_detype_classical_ac)
  qed
  have init: "\<forall>f \<in> set (init P2). num_free_fmla f"
  proof
    fix f assume "f \<in> set (init P2)"
    hence "f \<in> set (supertype_facts all_consts) \<or> f \<in> set (init P)"
      unfolding detype_classical_prob_sel by auto
    thus "num_free_fmla f"
      using supertype_facts_predAtom'[OF rp] num_free_fmla_of_predAtom
            nf[unfolded num_free_prob_def] by blast
  qed
  show ?thesis
    unfolding ast_classical_problem.num_free_prob_def
    using dom init nf unfolding num_free_prob_def by simp
qed

end
