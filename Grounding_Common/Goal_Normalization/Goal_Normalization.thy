theory Goal_Normalization
  imports Grounding_Common.PDDL_Normalization
    Grounding_Utils.String_Utils
begin

text \<open>\<open>fresh_name\<close> abbreviates the recursive least-index search \<open>safe_suffix\<close>, whose defining
  equations are declared \<open>[simp]\<close> by \<^theory_text>\<open>fun\<close>/\<^theory_text>\<open>function\<close>. Unfolding them is never useful in the
  grounder (the search is only ever consumed through its freshness lemmas) and is actively harmful:
  \<open>safe_suffix'\<close> recurses on an increasing index, so a \<open>simp\<close>/\<open>auto\<close> call meeting a generated name
  rewrites it into a nest of \<open>if\<close>-terms and loses the goal. Take both out of the simpset here, once,
  for the whole stage chain below.\<close>

declare safe_suffix.simps [simp del]
declare safe_suffix'.simps [simp del]

text \<open>Reusable, signature-level goal-normalization name: the fresh goal predicate (and its
  declaration), named by the token \<open>Goal\<close> decorated with the least decimal index that makes it
  distinct from every declared predicate name (\<open>fresh_name\<close>), so it is plain \<open>Goal\<close> unless the
  domain already declares that predicate. Mirrors the
  classical Classical_Goal_Normalization stage; the degoaling of domain/problem and the \<open>*3\<close> locales stay in
  \<open>Classical_Grounding.Classical_Goal_Normalization_Locales\<close>.\<close>

context domain_signature begin
  definition "goal_pred \<equiv> Pred (fresh_name pred_names (STR ''Goal''))"
  definition "goal_pred_decl \<equiv> PredDecl goal_pred []"
end

end
