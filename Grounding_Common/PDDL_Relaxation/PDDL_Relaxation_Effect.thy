theory PDDL_Relaxation_Effect
  imports "Continuous_Planning.Abstract_Syntax"
begin

text \<open>Reusable, AST-agnostic core of delete-relaxation: dropping the delete-effects of an effect.
  Mirrors the classical PDDL_Relaxation stage; the classical relaxation of action schemas, domains,
  and problems (and the \<open>*_rx\<close> locales) stay in \<open>Classical_Grounding.PDDL_Relaxation_Locales\<close>.\<close>

fun relax_eff :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "relax_eff (Effect a b ne) = Effect a [] ne"

lemma relax_eff_sel[simp]:
  "adds (relax_eff e) = adds e"
  "dels (relax_eff e) = []"
  by (cases e; simp)+

end
