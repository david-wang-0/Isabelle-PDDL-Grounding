theory Reachability_Formula_Helpers
  imports "Continuous_Planning.Worlds"
    Grounding_Common.Formula_Utils
    Grounding_Utils.Graph_Funs
begin

text \<open>Reusable, AST-agnostic formula/valuation and combinatorial helpers from the relaxation
  reachability argument: \<open>un_and\<close> distributes over the map-formula semantics and over
  \<open>map_atom_fmla\<close>; a positive predicate atom is entailed by \<open>valuation M\<close> iff it lies in \<open>fst M\<close>; a
  positive non-predicate literal is entailed model-independently; and the inversion of \<open>chosen_from\<close>
  on a uniform domain. Mirrors the classical Reachability_Analysis stage; the datalog/reachability
  locales stay in \<open>Classical_Grounding.PDDL_Reachability_Locales\<close>.\<close>

lemma un_and_map_semantics: "A \<Turnstile>\<^sub>m F \<Longrightarrow> \<forall>f \<in> set (un_and F). A \<Turnstile>\<^sub>m f"
  by (induction F rule: un_and.induct) auto

lemma valuation_predAtm_iff:
  "valuation M \<Turnstile>\<^sub>m Atom (predAtm p xs) \<longleftrightarrow> Atom (predAtm p xs) \<in> fst M"
  by (simp add: valuation_def)

lemma chosen_from_replicate:
  "length xs = n \<Longrightarrow> (\<forall>x \<in> set xs. x \<in> set S) \<Longrightarrow> chosen_from (replicate n S) xs"
  by (induction xs arbitrary: n) auto

text \<open>Inverting \<open>chosen_from\<close> on a uniform domain: a tuple chosen from \<open>n\<close> copies of \<open>S\<close> has
  length \<open>n\<close> and lives in \<open>S\<close>.\<close>
lemma chosen_from_replicate_dest:
  assumes "chosen_from (replicate n S) xs"
  shows "length xs = n" and "\<forall>x \<in> set xs. x \<in> set S"
proof -
  have "length xs = n \<and> (\<forall>x \<in> set xs. x \<in> set S)" using assms
  proof (induction n arbitrary: xs)
    case 0 thus ?case by (cases xs) auto
  next
    case (Suc n) thus ?case by (cases xs) auto
  qed
  thus "length xs = n" "\<forall>x \<in> set xs. x \<in> set S" by simp_all
qed

end
