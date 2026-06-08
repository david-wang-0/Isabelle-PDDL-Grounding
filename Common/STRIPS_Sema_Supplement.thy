theory STRIPS_Sema_Supplement
  imports "Classical_Planning.Classical_Happening_Semantics"
    "Verified_SAT_Based_AI_Planning.STRIPS_Representation"
begin

locale strips =
  fixes P_strips :: "'a strips_problem"

locale valid_strips = strips +
  assumes "is_valid_problem_strips P_strips"


end