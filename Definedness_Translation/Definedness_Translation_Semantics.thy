theory Definedness_Translation_Semantics
  imports Definedness_Translation
begin

section \<open>Definedness Translation Semantics\<close>

context ast_classical_problem begin

lemma def_translate_valid_plan_iff:
  "ast_classical_problem.valid_classical_plan2 def_translate_prob πs ⟷ valid_classical_plan2 πs"
  sorry

lemma def_translate_valid_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. ast_classical_problem.valid_classical_plan2 def_translate_prob \<pi>s')"
  using def_translate_valid_plan_iff by blast

end

end
