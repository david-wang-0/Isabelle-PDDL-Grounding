theory Certified_Grounding
  imports Certified_Grounding_Locales
begin

section \<open>Certificate-to-grounder bridge (Option 1): supersets over the un-relaxed problem\<close>

context certified_reachability
begin

subsection \<open>Step 2: facts superset over \<open>P\<close>\<close>

text \<open>The un-relaxed problem's achievable facts are over-approximated by the relaxed reachable set
  (\<open>relax_achievables\<close>), which the closure-checked certificate bounds (\<open>px.closure_sound\<close>).
  \<open>cert_facts'\<close> only \<^emph>\<open>adds\<close> atoms to the relaxed reachable set, so the inclusion survives.\<close>

lemma all_facts_super: "fact_to_facty ` {a. achievable a} \<subseteq> set cert_facts'"
  \<comment> \<open>P's achievable facts \<subseteq> relaxed reachable set \<subseteq> certificate\<close>
proof -
  have cc: "px.closure_check cert"
    using admissible_cert unfolding px.admissible_def by simp
  have "fact_to_facty ` {a. px.achievable a} \<subseteq> set (cert_facts cert)"
    using px.closure_sound[OF cc] .
  with relax_achievables have "fact_to_facty ` {a. achievable a} \<subseteq> set (cert_facts cert)"
    by blast
  thus ?thesis unfolding cert_facts'_def cert_facts_of_def by auto
qed

subsection \<open>Step 2: ops superset over \<open>P\<close> (inherits the relaxed-problem ops gap)\<close>

text \<open>Ops analogue of \<open>px.closure_sound\<close>: every plan action applicable in the relaxed problem lies
  in the certificate's op set. This is \<open>px.cert_ops_sound\<close> (theory \<open>Reachability_Certificate\<close>,
  in \<^locale>\<open>pddl_datalog\<close> next to \<open>closure_sound\<close>), instantiated at \<open>PX\<close>: the finite \<open>cert_ops\<close>
  enumeration over-approximates the applicable actions of the closure-checked certificate.\<close>

lemma px_cert_ops_super: "{\<pi>. px.applicable \<pi>} \<subseteq> set (px.cert_ops cert)"
proof -
  have cc: "px.closure_check cert"
    using admissible_cert unfolding px.admissible_def by simp
  show ?thesis using px.cert_ops_sound[OF cc] .
qed

lemma all_ops_super: "{\<pi>. applicable \<pi>} \<subseteq> set cert_ops'"
  using relax_applicables px_cert_ops_super unfolding cert_ops'_def cert_ops_of_def by blast

end

end

