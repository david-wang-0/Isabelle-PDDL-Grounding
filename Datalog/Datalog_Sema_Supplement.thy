theory Datalog_Sema_Supplement
  imports Stratified_Datalog.Datalog Tree_Decomp_Grounding_Common.Graph_Funs
begin

text ‹∗‹Semantic supplement to the AFP \<^theory>‹Stratified_Datalog.Datalog›.› Two layers, both over
  the AFP datatypes (programs are \<^typ>‹('p, 'x, 'c) dl_program›, i.e.\ clause ∗‹sets›): first
  ∗‹positive datalog› and its relation to stratified datalog, then the ∗‹universe-restricted›
  reference semantics with the locales ‹datalog_sem›, ‹positive_datalog›,
  ‹datalog_universe› and ‹positive_datalog_universe›. The executable certificate
  checker that refines this lives in ‹Datalog_Certificate.thy›.›

section ‹Positive datalog and its relation to stratified datalog›

text ‹The ∗‹positive› fragment of the AFP \<^theory>‹Stratified_Datalog.Datalog› clause language:
  programs whose clause bodies contain no \<^const>‹NegLit›. This is the syntactic restriction under
  which the consequence operator is monotone, and --- as shown here --- a degenerate case of
  ∗‹stratified› datalog: a positive program is well-stratified at the trivial stratification
  ‹λ_. 0›, where the AFP stratum ordering collapses to pointwise ‹⊆›. The ‹positive_datalog›
  locale packages the positivity assumption together with these consequences; the universe- and
  certificate-level developments build on it below.›

subsection ‹Positivity of a program›

fun is_pos_rh :: "('p, 'x, 'c) rh ⇒ bool" where
  "is_pos_rh (NegLit _ _) = False"
| "is_pos_rh _ = True"

text ‹Phrased on the AFP program type \<^typ>‹('p, 'x, 'c) dl_program› (a \<^typ>‹('p, 'x, 'c) clause set›),
  not a list: positivity is a property of the program as a set of clauses. The executable
  list-based refinement (where a ‹clause list› implements the set via \<^const>‹set›) is layered on
  top later, in the certificate development.›

definition dl_positive_prog :: "('p, 'x, 'c) dl_program ⇒ bool" where
  "dl_positive_prog P ≡ (∀cl ∈ P. ∀rh ∈ set (the_rhs cl). is_pos_rh rh)"

subsection ‹Relation to stratified datalog›

text ‹A positive program is a stratified program, which is well-stratified
  (\<^const>‹strat_wf›) at the constant stratification ‹λ_. 0›. The only way a clause can violate
  stratification is a negative body literal (\<^const>‹rnk› ‹1 + s p›), which a positive program has
  none of, so every body literal has rank ‹0 ≤ s p›. The AFP stratified-datalog least-solution
  machinery (\<^const>‹least_solution›) therefore applies; and at a single stratum its
  predicate-valuation ordering ‹⊑› collapses to pointwise ‹⊆›, so the stratified least solution is
  just the ‹⊆›-least model.›

lemma rnk_pos_zero: "is_pos_rh rh ⟹ rnk (λ_. 0) rh = 0"
  by (cases rh) auto

text ‹At the trivial stratification the stratum ordering is plain pointwise ‹⊆›.›
lemma lte_zero_iff: "(ρ ⊑(λ_. 0)⊑ ρ') ⟷ (∀p. ρ p ⊆ ρ' p)"
proof
  assume "ρ ⊑(λ_. 0)⊑ ρ'"
  then show "∀p. ρ p ⊆ ρ' p"
    unfolding lte_def lt_def by auto
next
  assume sub: "∀p. ρ p ⊆ ρ' p"
  show "ρ ⊑(λ_. 0)⊑ ρ'"
  proof (cases "ρ = ρ'")
    case True then show ?thesis unfolding lte_def by simp
  next
    case False
    then obtain p where "ρ p ⊂ ρ' p"
      using sub by (metis fun_eq_iff psubsetI)
    then have "ρ ⊏(λ_. 0)⊏ ρ'"
      unfolding lt_def using sub by (auto intro!: exI[of _ p])
    then show ?thesis unfolding lte_def by simp
  qed
qed

text ‹Hence a least solution at ‹λ_. 0› is exactly the ‹⊆›-least solution.›
lemma least_solution_zero_iff:
  "ρ ⊨⇩l⇩s⇩t dl (λ_. 0) ⟷ ρ ⊨⇩d⇩l dl ∧ (∀ρ'. ρ' ⊨⇩d⇩l dl ⟶ (∀p. ρ p ⊆ ρ' p))"
  unfolding least_solution_def by (metis lte_zero_iff)

subsection ‹The positive datalog locale›

text ‹A program carrying just the positivity assumption.›

locale positive_datalog =
  fixes P :: "('p, 'x, 'c) dl_program"
  assumes positive: "dl_positive_prog P"
begin

text ‹❙‹Relation to stratified datalog:› ‹P› is well-stratified at the trivial stratification ‹λ_. 0›
  --- with no negative body literals, every clause's body ranks at most its head stratum.›
lemma positive_strat_wf: "strat_wf (λ_. 0) P"
  unfolding strat_wf_def
proof
  fix c assume c: "c ∈ P"
  obtain p ids rhs where ceq: "c = Cls p ids rhs" by (cases c)
  have "∀rh ∈ set rhs. is_pos_rh rh"
    using positive c unfolding dl_positive_prog_def ceq by auto
  then have "∀rh ∈ set rhs. rnk (λ_. 0) rh = 0"
    using rnk_pos_zero by blast
  then show "strat_wf_cls (λ_. 0) c"
    unfolding ceq strat_wf_cls.simps by simp
qed

lemmas stratified = positive_strat_wf

text ‹So a least solution of ‹P› at that stratification is exactly the ‹⊆›-least model.›
lemma least_solution_iff:
  "ρ ⊨⇩l⇩s⇩t P (λ_. 0) ⟷ ρ ⊨⇩d⇩l P ∧ (∀ρ'. ρ' ⊨⇩d⇩l P ⟶ (∀p. ρ p ⊆ ρ' p))"
  using least_solution_zero_iff .

end

section ‹Universe-restricted datalog semantics›

text ‹The reference least-model semantics of a positive datalog program over a finite constant
  universe ‹U›, phrased on the AFP \<^theory>‹Stratified_Datalog.Datalog› clause syntax with the
  program a \<^typ>‹('p, 'x, 'c) dl_program› (clause ∗‹set›). The ‹datalog_sem› locale fixes ‹U›;
  ‹datalog_universe› adds a ‹U›-safe, head-covered program; and ‹positive_datalog_universe›
  combines that with ‹positive_datalog›, so that ‹U›-restricted derivability coincides with the
  AFP least solution. The list-based grounding (‹cls_substs›) is the executable layer.›

subsection ‹Ground facts and substitutions›

type_synonym ('p, 'c) dl_fact = "'p × 'c list"

fun subst_id :: "('x ⇒ 'c) ⇒ ('x, 'c) id ⇒ 'c" where
  "subst_id σ (id.Var x) = σ x"
| "subst_id σ (id.Cst c) = c"

definition subst_atom :: "('x ⇒ 'c) ⇒ ('p, 'x, 'c) lh ⇒ ('p, 'c) dl_fact" where
  "subst_atom σ a = (fst a, map (subst_id σ) (snd a))"

fun rh_body_atom :: "('p, 'x, 'c) rh ⇒ ('p, 'x, 'c) lh option" where
  "rh_body_atom (PosLit p ids) = Some (p, ids)"
| "rh_body_atom _ = None"

definition cls_body_atoms :: "('p, 'x, 'c) clause ⇒ ('p, 'x, 'c) lh list" where
  "cls_body_atoms cl = List.map_filter rh_body_atom (the_rhs cl)"

fun is_dl_guard :: "('p, 'x, 'c) rh ⇒ bool" where
  "is_dl_guard (Eql _ _) = True"
| "is_dl_guard (Neql _ _) = True"
| "is_dl_guard _ = False"

definition cls_guards :: "('p, 'x, 'c) clause ⇒ ('p, 'x, 'c) rh list" where
  "cls_guards cl = filter is_dl_guard (the_rhs cl)"

fun eval_guard :: "('x ⇒ 'c) ⇒ ('p, 'x, 'c) rh ⇒ bool" where
  "eval_guard σ (Eql a b) = (subst_id σ a = subst_id σ b)"
| "eval_guard σ (Neql a b) = (subst_id σ a ≠ subst_id σ b)"
| "eval_guard σ _ = True"

text ‹The grounding substitutions of a clause over a finite constant universe ‹U›: one for every
  assignment of the clause's variables to constants from ‹U›. A ground clause has no variables
  and exactly one (vacuous) substitution.›

fun id_vars_list :: "('x, 'c) id ⇒ 'x list" where
  "id_vars_list (id.Var x) = [x]"
| "id_vars_list (id.Cst _) = []"

fun rh_vars_list :: "('p, 'x, 'c) rh ⇒ 'x list" where
  "rh_vars_list (Eql a b) = id_vars_list a @ id_vars_list b"
| "rh_vars_list (Neql a b) = id_vars_list a @ id_vars_list b"
| "rh_vars_list (PosLit _ ids) = concat (map id_vars_list ids)"
| "rh_vars_list (NegLit _ ids) = concat (map id_vars_list ids)"

fun cls_vars :: "('p, 'x, 'c) clause ⇒ 'x list" where
  "cls_vars (Cls _ ids rhs) = remdups (concat (map id_vars_list ids) @ concat (map rh_vars_list rhs))"

definition subst_of :: "'x list ⇒ 'c list ⇒ 'x ⇒ 'c" where
  "subst_of vs args x = the (map_of (zip vs args) x)"

definition cls_substs :: "'c list ⇒ ('p, 'x, 'c) clause ⇒ ('x ⇒ 'c) list" where
  "cls_substs U cl = map (subst_of (cls_vars cl))
                         (all_combos ✓ (replicate (length (cls_vars cl)) U))"

subsection ‹Side conditions tying ‹P›, ‹U› and the AFP semantics together›

text ‹The equivalence needs three side conditions:
▪ ❙‹positivity› (\<^const>‹dl_positive_prog›): ‹dl_derivable› silently ignores \<^const>‹NegLit›s
  (they are neither guards nor body atoms), while the AFP semantics constrains them.
▪ ❙‹safety› (‹dl_safe›): every clause variable occurs in a positive body atom. The AFP
  \<^const>‹solves_cls› quantifies over ∗‹all› valuations ‹'x ⇒ 'c›, whereas ‹dl_derivable›
  only instantiates variables from ‹U›; safety pins every variable to a derivable fact.
▪ ❙‹head-constant coverage› (‹dl_heads_covered›): constants in clause heads lie in ‹U›,
  so derivable facts only mention ‹U›-constants and body variables stay inside ‹U›.›

fun id_consts_list :: "('x, 'c) id ⇒ 'c list" where
  "id_consts_list (id.Var _) = []"
| "id_consts_list (id.Cst c) = [c]"

definition dl_heads_covered :: "'c set ⇒ ('p, 'x, 'c) dl_program ⇒ bool" where
  "dl_heads_covered U P ≡
     ∀cl ∈ P. ∀i ∈ set (snd (the_lh cl)). set (id_consts_list i) ⊆ U"

definition dl_safe :: "('p, 'x, 'c) dl_program ⇒ bool" where
  "dl_safe P ≡
     ∀cl ∈ P. ∀x ∈ set (cls_vars cl).
       ∃a ∈ set (cls_body_atoms cl). x ∈ set (concat (map id_vars_list (snd a)))"

text ‹Bridging the checker's substitution application to the AFP evaluation functions.›

lemma subst_id_eval_id: "subst_id σ = (λi. ⟦i⟧⇩i⇩d σ)"
proof (rule ext)
  fix i show "subst_id σ i = ⟦i⟧⇩i⇩d σ" by (cases i) simp_all
qed

lemma rh_body_atom_Some: "rh_body_atom rh = Some a ⟷ rh = PosLit (fst a) (snd a)"
  by (cases rh; cases a) auto

lemma set_map_filter': "set (List.map_filter f xs) = {y. ∃x ∈ set xs. f x = Some y}"
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

lemma cls_body_atoms_iff:
  "a ∈ set (cls_body_atoms cl) ⟷ PosLit (fst a) (snd a) ∈ set (the_rhs cl)"
  unfolding cls_body_atoms_def set_map_filter' by (auto simp: rh_body_atom_Some)

lemma cls_vars_head_vars:
  assumes "i ∈ set (snd (the_lh cl))" and "x ∈ set (id_vars_list i)"
  shows "x ∈ set (cls_vars cl)"
  using assms by (cases cl) auto

lemma cls_vars_rhs_vars:
  assumes "rh ∈ set (the_rhs cl)" and "x ∈ set (rh_vars_list rh)"
  shows "x ∈ set (cls_vars cl)"
  using assms by (cases cl) auto

lemma subst_id_agree:
  assumes "∀x ∈ set (id_vars_list i). σ x = σ' x"
  shows "subst_id σ i = subst_id σ' i"
  using assms by (cases i) simp_all

lemma subst_atom_agree:
  assumes "∀i ∈ set (snd a). ∀x ∈ set (id_vars_list i). σ x = σ' x"
  shows "subst_atom σ a = subst_atom σ' a"
proof -
  have "map (subst_id σ) (snd a) = map (subst_id σ') (snd a)"
    using assms by (intro map_cong[OF refl] subst_id_agree) auto
  then show ?thesis unfolding subst_atom_def by simp
qed

lemma eval_guard_agree:
  assumes "∀x ∈ set (rh_vars_list g). σ x = σ' x"
  shows "eval_guard σ g = eval_guard σ' g"
proof (cases g)
  case (Eql a b)
  then have "subst_id σ a = subst_id σ' a" "subst_id σ b = subst_id σ' b"
    using assms by (auto intro!: subst_id_agree)
  with Eql show ?thesis by simp
next
  case (Neql a b)
  then have "subst_id σ a = subst_id σ' a" "subst_id σ b = subst_id σ' b"
    using assms by (auto intro!: subst_id_agree)
  with Neql show ?thesis by simp
qed simp_all

text ‹Membership in \<^const>‹cls_substs›: exactly the tabulated substitutions over ‹U›.›

lemma chosen_from_replicate:
  "chosen_from (replicate n U) xs ⟷ length xs = n ∧ set xs ⊆ set U"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by (cases n) simp_all
next
  case (Cons x xs)
  then show ?case by (cases n) auto
qed

lemma cls_substs_iff:
  "σ ∈ set (cls_substs U cl) ⟷
     (∃cs. σ = subst_of (cls_vars cl) cs
           ∧ length cs = length (cls_vars cl) ∧ set cs ⊆ set U)"
  unfolding cls_substs_def set_map set_all_combos
  by (auto simp: chosen_from_replicate)

lemma subst_of_map: "x ∈ set vs ⟹ subst_of vs (map f vs) x = f x"
  unfolding subst_of_def map_of_zip_map by simp

lemma subst_of_in_set:
  assumes "length cs = length vs" and "x ∈ set vs"
  shows "subst_of vs cs x ∈ set cs"
proof -
  obtain c where "map_of (zip vs cs) x = Some c"
    using assms by (metis map_of_zip_is_Some)
  then show ?thesis
    unfolding subst_of_def using map_of_SomeD set_zip_rightD by fastforce
qed

lemma cls_substs_rangeD:
  assumes "σ ∈ set (cls_substs U cl)" and "x ∈ set (cls_vars cl)"
  shows "σ x ∈ set U"
  using assms subst_of_in_set unfolding cls_substs_iff by fastforce


subsection ‹Datalog semantics restricted to a universe›

text ‹A fixed (abstract) finite constant universe ‹U›, as a ∗‹set›. Fixing only the universe ---
  no program --- ‹datalog_universe› below extends it with a program and the inductive derivability.
  The universe is abstract; the executable certificate checker instantiates it with ‹set U_list›.›

locale datalog_sem =
  fixes U :: "'c set"


subsection ‹The universe-restricted datalog locale›

text ‹∗‹Datalog universe›: the universe-restriction half --- a fixed universe set ‹U›
  (\<^locale>‹datalog_sem›) together with a program ‹P› that is ∗‹safe› and ∗‹head-covered›. No
  positivity is assumed, so this isolates the facts that follow from the universe side conditions
  alone. It owns the inductive derivability ‹derivable›.›

locale datalog_prog = datalog_sem U for U :: "'c set" +
  fixes P :: "('p, 'x, 'c) dl_program"
begin

text ‹The least-model semantics of this locale's program ‹P› over its universe ‹U›, as an
  inductive predicate: a fact is derivable iff it is the head of a ground clause instance (each
  variable assigned a constant from the universe set ‹U›) whose guards hold and whose body atoms
  are derivable. Bodyless clauses are the base case. The inductive is owned by this
  ∗‹assumption-free› locale, so the exported ‹derivable.induct› / ‹derivable.derive› rules carry no
  side conditions and can be used by the (assumption-free) certificate checker.›
inductive derivable :: "('p, 'c) dl_fact ⇒ bool" where
  derive: "⟦ cl ∈ P; ∀x ∈ set (cls_vars cl). σ x ∈ U;
             ∀g ∈ set (cls_guards cl). eval_guard σ g;
             ∀a ∈ set (cls_body_atoms cl). derivable (subst_atom σ a) ⟧
           ⟹ derivable (subst_atom σ (the_lh cl))"

end

text ‹∗‹Datalog universe›: the universe-restriction half --- the assumption-free
  \<^locale>‹datalog_prog› (a fixed universe set ‹U› and program ‹P›) plus the side conditions that
  ‹P› is ∗‹safe› and ∗‹head-covered›. No positivity is assumed, so this isolates the facts that
  follow from the universe side conditions alone.›

locale datalog_universe = datalog_prog U P
  for U :: "'c set" and P :: "('p, 'x, 'c) dl_program" +
  assumes safe:    "dl_safe P"
      and covered: "dl_heads_covered U P"
begin

text ‹Derivable facts mention only universe constants (head coverage from the locale).›
lemma derivable_consts: "derivable f ⟹ set (snd f) ⊆ U"
proof (induction rule: derivable.induct)
  case (derive cl σ)
  have "subst_id σ i ∈ U" if i: "i ∈ set (snd (the_lh cl))" for i
  proof (cases i)
    case (Var x)
    then have "x ∈ set (cls_vars cl)"
      using i cls_vars_head_vars by fastforce
    then have "σ x ∈ U" using derive.hyps(2) by blast
    then show ?thesis using Var by simp
  next
    case (Cst c)
    then show ?thesis
      using covered derive.hyps(1) i unfolding dl_heads_covered_def by fastforce
  qed
  then show ?case unfolding subst_atom_def by auto
qed

text ‹❙‹Completeness core›: the derivable facts form an AFP solution of ‹P› (safety + coverage).›
lemma derivable_solves: "(λq. {r. derivable (q, r)}) ⊨⇩d⇩l P"
    (is "?D ⊨⇩d⇩l _")
  unfolding solves_program_def solves_cls_def
proof (intro ballI allI)
  fix cl σ
  assume cl: "cl ∈ P"
  obtain q ids rhs where cl_eq: "cl = Cls q ids rhs" by (cases cl)
  have main: "⟦(q, ids)⟧⇩l⇩h ?D σ" if body: "⟦rhs⟧⇩r⇩h⇩s ?D σ"
  proof -
    have body_der: "derivable (fst a, ⟦snd a⟧⇩i⇩d⇩s σ)"
      if a: "a ∈ set (cls_body_atoms cl)" for a
    proof -
      from a have "PosLit (fst a) (snd a) ∈ set rhs"
        using cls_body_atoms_iff[of a cl] cl_eq by simp
      then have "⟦❙+ (fst a) (snd a)⟧⇩r⇩h ?D σ" using body by fastforce
      then show ?thesis by simp
    qed
    text ‹Safety pins each clause variable to a body atom, whose derivable instance has only
      universe constants --- so ‹σ› already maps the clause variables into ‹U›.›
    have subst_cond: "∀x ∈ set (cls_vars cl). σ x ∈ U"
    proof
      fix x assume x: "x ∈ set (cls_vars cl)"
      from safe cl x obtain a where a: "a ∈ set (cls_body_atoms cl)"
        and xa: "x ∈ set (concat (map id_vars_list (snd a)))"
        unfolding dl_safe_def by blast
      from xa obtain i where i: "i ∈ set (snd a)" and xi: "x ∈ set (id_vars_list i)"
        by auto
      have i_eq: "i = id.Var x" using xi by (cases i) auto
      have "set (⟦snd a⟧⇩i⇩d⇩s σ) ⊆ U"
        using derivable_consts[OF body_der[OF a]] by simp
      moreover have "σ x ∈ set (⟦snd a⟧⇩i⇩d⇩s σ)"
        using i i_eq by force
      ultimately show "σ x ∈ U" by blast
    qed
    have guards: "∀g ∈ set (cls_guards cl). eval_guard σ g"
    proof
      fix g assume g: "g ∈ set (cls_guards cl)"
      then have g_rhs: "g ∈ set rhs" using cl_eq unfolding cls_guards_def by simp
      show "eval_guard σ g"
      proof (cases g)
        case (Eql a b)
        then show ?thesis using body g_rhs by (fastforce simp: subst_id_eval_id)
      next
        case (Neql a b)
        then show ?thesis using body g_rhs by (fastforce simp: subst_id_eval_id)
      qed simp_all
    qed
    have body': "∀a ∈ set (cls_body_atoms cl). derivable (subst_atom σ a)"
    proof
      fix a assume a: "a ∈ set (cls_body_atoms cl)"
      have "subst_atom σ a = (fst a, ⟦snd a⟧⇩i⇩d⇩s σ)"
        unfolding subst_atom_def by (simp add: subst_id_eval_id)
      then show "derivable (subst_atom σ a)" using body_der[OF a] by simp
    qed
    have "derivable (subst_atom σ (the_lh cl))"
      using derivable.derive[OF cl subst_cond guards body'] by blast
    then show ?thesis
      using cl_eq by (simp add: subst_atom_def subst_id_eval_id)
  qed
  then show "⟦cl⟧⇩c⇩l⇩s ?D σ"
    unfolding cl_eq meaning_cls.simps by blast
qed

end

subsection ‹Positive datalog over a universe (the combined locale)›

text ‹The two halves combined: a \<^locale>‹positive_datalog› program ‹P› that is also a
  \<^locale>‹datalog_universe› (safe, head-covered, over ‹U›). As a sublocale of
  \<^locale>‹positive_datalog› it inherits the relation to stratified datalog, and under all the side
  conditions the ‹U›-restricted ‹derivable› is exactly the stratified-datalog least solution of
  ‹P›. Instantiate with any concrete ‹U›/‹P›.›

locale positive_datalog_universe = datalog_universe U P + positive_datalog P
  for U :: "'c set" and P :: "('p, 'x, 'c) dl_program"
begin

text ‹❙‹Soundness›: every derivable fact is in every AFP solution of ‹P› (positivity needed).›
lemma derivable_in_solution:            
  assumes sol: "ρ ⊨⇩d⇩l P" and der: "derivable f"
  shows "snd f ∈ ρ (fst f)"
  using der
proof (induction rule: derivable.induct)
  case (derive cl σ)
  obtain q ids rhs where cl_eq: "cl = Cls q ids rhs" by (cases cl)
  have "⟦rh⟧⇩r⇩h ρ σ" if rh: "rh ∈ set rhs" for rh
  proof (cases rh)
    case (Eql a b)
    then have "rh ∈ set (cls_guards cl)"
      using rh cl_eq unfolding cls_guards_def by simp
    then have "eval_guard σ rh" using derive.hyps(3) by blast
    then show ?thesis using Eql by (simp add: subst_id_eval_id)
  next
    case (Neql a b)
    then have "rh ∈ set (cls_guards cl)"
      using rh cl_eq unfolding cls_guards_def by simp
    then have "eval_guard σ rh" using derive.hyps(3) by blast
    then show ?thesis using Neql by (simp add: subst_id_eval_id)
  next
    case (PosLit p' ids')
    then have "(p', ids') ∈ set (cls_body_atoms cl)"
      using rh cl_eq cls_body_atoms_iff by fastforce
    then have "snd (subst_atom σ (p', ids')) ∈ ρ (fst (subst_atom σ (p', ids')))"
      using derive.IH by blast
    then show ?thesis
      using PosLit by (simp add: subst_atom_def subst_id_eval_id)
  next
    case (NegLit p' ids')
    then have False
      using positive derive.hyps(1) rh cl_eq unfolding dl_positive_prog_def by fastforce
    then show ?thesis ..
  qed
  then have rhs_sat: "⟦rhs⟧⇩r⇩h⇩s ρ σ" by simp
  have "⟦cl⟧⇩c⇩l⇩s ρ σ"
    using sol derive.hyps(1) unfolding solves_program_def solves_cls_def by blast
  then have "⟦(q, ids)⟧⇩l⇩h ρ σ"
    using rhs_sat unfolding cl_eq meaning_cls.simps by blast
  then show ?case using cl_eq by (simp add: subst_atom_def subst_id_eval_id)
qed

text ‹❙‹The equivalence›: ‹derivable› coincides with the (rank-0) least solution of ‹P›.›
lemma derivable_iff_least_solution:
  assumes lst: "ρ ⊨⇩l⇩s⇩t P (λ_. 0)"
  shows "derivable (p, r) ⟷ r ∈ ρ p"
proof
  assume "derivable (p, r)"
  moreover have "ρ ⊨⇩d⇩l P"
    using lst unfolding least_solution_def by blast
  ultimately show "r ∈ ρ p"
    using derivable_in_solution by fastforce
next
  assume r: "r ∈ ρ p"
  have D_sol: "(λq. {r. derivable (q, r)}) ⊨⇩d⇩l P"
    using derivable_solves .
  with lst have "lte ρ (λ_. 0) (λq. {r. derivable (q, r)})"
    unfolding least_solution_def by blast
  then have "ρ p ⊆ {r. derivable (p, r)}"
    unfolding lte_def lt_def by auto
  with r show "derivable (p, r)" by blast
qed

end

end
