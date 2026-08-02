theory Definedness_Normalization
  imports Grounding_Common.Formula_Utils
begin

text \<open>Reusable, AST-agnostic core of definedness explication: for every PNE appearing in a formula,
  conjoin the reflexive numeric equality witnessing its definedness, and — division by zero
  being undefined — for every divisor sub-expression \<open>y\<close> the nonzero witness \<open>\<^bold>\<not>(y = 0)\<close>.
  The equalities stay \<^emph>\<open>first\<close> so the atom-prefix machinery (\<open>conj_atom_prefix\<close>) is untouched;
  the disequality literals form a second prefix segment tracked by \<open>conj_literal_prefix\<close>.
  Mirrors the classical Classical_Definedness_Normalization stage; the action/domain/problem
  explication and the locales stay in
  \<open>Classical_Grounding.Classical_Definedness_Normalization_Locales\<close>.\<close>

definition "definedness_atoms f \<equiv>
  let pnes = formula_enumerate_primitive_numeric_expressions f;
      pne_exprs = map FunctionExpr pnes
  in map (\<lambda>e. numericEqAtm e e) pne_exprs"

definition "divisor_zero_atoms f \<equiv>
  map (\<lambda>y. numericEqAtm y (ConstantExpr 0)) (formula_enumerate_divisor_expressions f)"

definition "explicate_def_fmla f \<equiv>
  foldr (\<^bold>\<and>) (map Atom (definedness_atoms f))
    (foldr (\<^bold>\<and>) (map (\<lambda>a. \<^bold>\<not>(Atom a)) (divisor_zero_atoms f)) f)"

end
