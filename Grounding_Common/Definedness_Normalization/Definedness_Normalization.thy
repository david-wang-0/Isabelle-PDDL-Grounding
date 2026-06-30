theory Definedness_Normalization
  imports Grounding_Common.Formula_Utils
begin

text \<open>Reusable, AST-agnostic core of definedness explication: for every PNE appearing in a formula,
  conjoin the reflexive numeric equality witnessing its definedness. Mirrors the classical
  Classical_Definedness_Normalization stage; the action/domain/problem explication and the locales stay in
  \<open>Classical_Grounding.Classical_Definedness_Normalization_Locales\<close>.\<close>

definition "definedness_atoms f \<equiv>
  let pnes = formula_enumerate_primitive_numeric_expressions f;
      pne_exprs = map FunctionExpr pnes
  in map (\<lambda>e. numericEqAtm e e) pne_exprs"

definition "explicate_def_fmla f \<equiv>
  foldr (\<^bold>\<and>) (map Atom (definedness_atoms f)) f"

end
