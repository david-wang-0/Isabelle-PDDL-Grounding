theory Goal_Normalization_Pred
  imports Grounding_Common.Signature_Normalization
    Grounding_Utils.String_Utils
begin

text \<open>Reusable, signature-level goal-normalization name: the fresh goal predicate (and its
  declaration), prefixed by a domain-fresh \<open>safe_prefix\<close> of the declared predicate names. Mirrors the
  classical Goal_Normalization stage; the degoaling of domain/problem and the \<open>*3\<close> locales stay in
  \<open>Classical_Grounding.Goal_Normalization_Locales\<close>.\<close>

context domain_signature begin
  definition "goal_pred \<equiv> Pred (safe_prefix pred_names + STR ''Goal'')"
  definition "goal_pred_decl \<equiv> PredDecl goal_pred []"
end

end
