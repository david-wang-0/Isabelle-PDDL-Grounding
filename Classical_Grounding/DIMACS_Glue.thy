theory DIMACS_Glue
  imports Verified_SAT_Based_AI_Planning.SAT_Plan_Base
begin

section \<open>DIMACS-style CNF for the SAT oracle\<close>

text \<open>The four functions the executable planner needs to talk to an external SAT solver:
  \<open>cnf_to_dimacs\<close> / \<open>disj_to_dimacs\<close> flatten a CNF formula into an \<open>int list list\<close>,
  \<open>cnf_to_dimacs.var_to_dimacs\<close> numbers the SATPlan variables, and \<open>dimacs_model_to_abs\<close> reads an
  assignment back as a valuation on \<^typ>\<open>nat\<close>.

  \<^bold>\<open>Provenance.\<close> These definitions, and the two code equations at the end, are taken verbatim from
  \<open>Solve_SASP\<close> in the AFP entry \<^emph>\<open>Verified_SAT_Based_AI_Planning\<close> (Abdulaziz and Kurz), which is
  where the executable planner previously got them by importing that theory.

  \<^bold>\<open>Why they are copied rather than imported.\<close> \<open>Solve_SASP\<close> is the SAS+ solver: it exists to
  wire the encoding to \<open>AI_Planning_Languages_Semantics.SASP_Checker\<close>, and it vendors its own
  copy of \<open>Set2_Join_RBT\<close>. The Isabelle-Graph-Library vendors a copy under that name too, so a
  theory importing both --- which \<open>Planner_STRIPS_Executable\<close> does, needing the SAT encoding and
  the datalog foundedness check at once --- fails with \<open>Duplicate theory name\<close> before any of its
  own content is read. Nothing else in \<open>Solve_SASP\<close> is used here: it contributed exactly these
  four constants, as \<^emph>\<open>untrusted\<close> plumbing around the oracle call, with no lemma of its own
  entering any proof (soundness rests on re-checking the returned model, not on the encoding).
  Dropping the import also keeps the superseded \<open>AI_Planning_Languages_Semantics\<close> entry, and the
  SAS+ \<open>ast_problem\<close> namespace, out of scope entirely.\<close>

subsection \<open>Numbering the SATPlan variables\<close>

text \<open>\<open>h\<close> bounds the time indices --- use \<open>Suc t\<close> for horizon \<open>t\<close> --- and \<open>n_ops\<close> the operator
  indices. DIMACS variables must be \<open>\<ge> 1\<close>, hence the offsets.\<close>

locale cnf_to_dimacs =
  fixes h :: nat and n_ops :: nat
begin

fun var_to_dimacs where
  "var_to_dimacs (Operator t k) = 1 + t + k * h"
| "var_to_dimacs (State t k) = 1 + n_ops * h + t + k * (h)"

end

subsection \<open>Flattening a CNF formula\<close>

fun disj_to_dimacs :: "nat formula \<Rightarrow> int list" where
  "disj_to_dimacs (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = disj_to_dimacs \<phi>\<^sub>1 @ disj_to_dimacs \<phi>\<^sub>2"
| "disj_to_dimacs \<bottom> = []"
| "disj_to_dimacs (Not \<bottom>) = [-1::int, 1::int]"
| "disj_to_dimacs (Atom v) = [int v]"
| "disj_to_dimacs (Not (Atom v)) = [-(int v)]"

fun cnf_to_dimacs :: "nat formula \<Rightarrow> int list list" where
  "cnf_to_dimacs (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = cnf_to_dimacs \<phi>\<^sub>1 @ cnf_to_dimacs \<phi>\<^sub>2"
| "cnf_to_dimacs d = [disj_to_dimacs d]"

subsection \<open>Reading an assignment back\<close>

definition "dimacs_model_to_abs dimacs_M M \<equiv>
  fold (\<lambda>l M. if (l > 0) then M((nat (abs l)) := True) else M((nat (abs l)) := False)) dimacs_M M"

subsection \<open>Code setup inherited from \<open>Solve_SASP\<close>\<close>

text \<open>Both equations were declared in \<open>Solve_SASP\<close> and are needed by the export: the locale
  function has no code equations of its own, and \<^const>\<open>ListMem\<close> --- which the AFP frame-axiom
  encoding in \<^theory>\<open>Verified_SAT_Based_AI_Planning.SAT_Plan_Base\<close> uses --- is an inductive
  predicate that the code generator cannot execute unfolded.\<close>

lemmas [code] = cnf_to_dimacs.var_to_dimacs.simps

lemma [code]:
  \<open>ListMem x xs \<longleftrightarrow> List.member xs x\<close>
  by (simp add: ListMem_iff)

end
