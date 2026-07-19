theory PDDL_Relaxation
  imports "Analysis_Free_Base.Abstract_Syntax"
begin

text \<open>Reusable, AST-agnostic core of delete-relaxation: dropping the delete-effects \<^emph>\<open>and\<close> the
  numeric effects of an effect. The relaxation feeds the (numeric-free) datalog reachability
  analysis, and numeric effects are propositionally inert --- they add no \<^const>\<open>predAtm\<close> fact ---
  so dropping them leaves the monotone reachability closure unchanged while making the relaxed
  problem numeric-effect-free (as the datalog requires). The \<^emph>\<open>real\<close> numeric effects are kept in the
  un-relaxed problem \<open>P\<^sub>T\<close>, where the numeric-fluent-retaining grounder preserves them.
  Mirrors the classical Classical_PDDL_Relaxation stage; the classical relaxation of action schemas, domains,
  and problems (and the \<open>*_rx\<close> locales) stay in \<open>Classical_Grounding.Classical_PDDL_Relaxation_Locales\<close>.\<close>

fun relax_eff :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "relax_eff (Effect a b ne) = Effect a [] []"

lemma relax_eff_sel[simp]:
  "adds (relax_eff e) = adds e"
  "dels (relax_eff e) = []"
  "numeric_effects (relax_eff e) = []"
  by (cases e; simp)+

end
