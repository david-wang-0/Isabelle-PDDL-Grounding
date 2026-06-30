theory Classical_Definedness_Translation_Semantics
  imports Classical_Definedness_Translation
begin

section \<open>Definedness Translation Semantics\<close>

text \<open>The translation changes the domain signature (it appends \<open>Defined_\<close>
  predicates), so the equivalence proof needs both the freshness of these
  predicates (\<open>def_prefix_fresh\<close>) and the well-formedness invariants that keep
  reachable states free of \<open>Defined_\<close> atoms. We therefore work inside the
  well-formed translation locale, where the \<open>pt\<close>/\<open>dt\<close> sublocales and all
  signature-monotonicity facts from \<^theory>\<open>Classical_Definedness_Translation.Classical_Definedness_Translation\<close>
  are available.\<close>

subsection \<open>General formula-semantics helpers\<close>

text \<open>Evaluating a syntactically translated formula under a valuation is the same
  as evaluating the original formula under the pre-composed valuation. Holds for
  the strict (three-valued) \<open>\<Turnstile>\<^sub>m\<close> because \<open>atoms (map_formula g \<phi>) = g ` atoms \<phi>\<close>
  matches the domain side-conditions.\<close>

lemma map_formula_semantics_map:
  "(\<A> \<Turnstile>\<^sub>m map_formula g \<phi>) = ((\<A> \<circ> g) \<Turnstile>\<^sub>m \<phi>)"
  by (induction \<phi>) (auto simp: formula.set_map)

text \<open>Every atom in the top-level positive conjunctive prefix is entailed by the
  whole conjunction (\<open>\<^bold>\<and>\<close> carries no definedness guard).\<close>

lemma conj_atom_prefix_entails:
  "a \<in> set (conj_atom_prefix \<phi>) \<Longrightarrow> \<A> \<Turnstile>\<^sub>m \<phi> \<Longrightarrow> \<A> \<Turnstile>\<^sub>m Atom a"
  by (induction \<phi> rule: conj_atom_prefix.induct) auto

context def_explicated_conj_problem_dt begin

subsection \<open>State relation tracking definedness\<close>

text \<open>A translated run-state \<open>MT\<close> mirrors an original run-state \<open>M\<close> iff their
  numeric parts coincide and the boolean part of \<open>MT\<close> is that of \<open>M\<close> augmented
  with exactly the \<open>Defined_\<close> atoms of the currently-defined PNEs. Freshness of
  \<open>def_prefix\<close> guarantees the added atoms never clash with \<open>fst M\<close>, so the
  relation loses no information.\<close>

text \<open>The boolean part of a world model is a set of \<open>Atom (predAtm \<dots>)\<close> facts
  (\<open>valuation\<close> reads \<open>Atom (predAtm p xs) \<in> fst M\<close>), so the tracked \<open>Defined_\<close>
  facts are \<open>Atom\<close>-wrapped predicate atoms.\<close>

definition defined_atoms where
  "defined_atoms ns = (\<lambda>p. Atom (pne_to_def_atom def_prefix p)) ` dom ns"

text \<open>Besides linking the two states, the relation records that the original
  boolean state \<open>fst M\<close> never mentions a \<open>Defined_\<close> predicate (those names are
  domain-fresh, so no reachable original fact can use them). This is what makes
  a reflexive definedness atom read the same on both sides.\<close>

definition def_state_rel where
  "def_state_rel M MT \<longleftrightarrow>
     snd MT = snd M \<and> fst MT = fst M \<union> defined_atoms (snd M)
     \<and> (\<forall>n args. Atom (predAtm (Pred (def_prefix + n)) args) \<notin> fst M)"

lemma defined_atom_iff:
  "(Atom (predAtm (Pred (def_prefix + n)) args) \<in> defined_atoms ns)
     \<longleftrightarrow> PNE (Func n) args \<in> dom ns"
  unfolding defined_atoms_def
proof
  assume "Atom (predAtm (Pred (def_prefix + n)) args) \<in> (\<lambda>p. Atom (pne_to_def_atom def_prefix p)) ` dom ns"
  then obtain p where p: "p \<in> dom ns"
    and eq: "predAtm (Pred (def_prefix + n)) args = pne_to_def_atom def_prefix p" by (auto simp: image_iff)
  obtain f bs where pf: "p = PNE f bs" by (cases p)
  obtain m where fm: "f = Func m" by (cases f)
  from eq have "predAtm (Pred (def_prefix + n)) args = predAtm (Pred (def_prefix + m)) bs"
    by (simp add: pf fm pne_to_def_atom_def)
  hence "def_prefix + n = def_prefix + m" and "args = bs" by auto
  hence "n = m" "args = bs" using injD[OF inj_prepend] by auto
  thus "PNE (Func n) args \<in> dom ns" using p pf fm by simp
next
  assume "PNE (Func n) args \<in> dom ns"
  moreover have "Atom (pne_to_def_atom def_prefix (PNE (Func n) args)) = Atom (predAtm (Pred (def_prefix + n)) args)"
    by (simp add: pne_to_def_atom_def)
  ultimately show "Atom (predAtm (Pred (def_prefix + n)) args) \<in> (\<lambda>p. Atom (pne_to_def_atom def_prefix p)) ` dom ns"
    by (force simp: image_iff)
qed

subsection \<open>Atom-level evaluation under the translation\<close>

text \<open>The reflexive definedness atom \<open>(= p p)\<close> translates to its \<open>Defined_p\<close>
  predicate, which the related target state reads as \<open>True\<close> exactly when \<open>p\<close> is
  defined; freshness of \<open>def_prefix\<close> (recorded in \<open>def_state_rel\<close>) is what rules
  out a spurious \<open>Defined_p\<close> already sitting in \<open>fst M\<close>.\<close>

lemma valT_atom_refl:
  assumes rel: "def_state_rel M MT"
  shows "valuation MT (def_translate_atom def_prefix (numericEqAtm (FunctionExpr p) (FunctionExpr p)))
          = Some (p \<in> dom (snd M))"
proof -
  obtain f args where pf: "p = PNE f args" by (cases p)
  obtain n where fn: "f = Func n" by (cases f)
  have notin: "Atom (predAtm (Pred (def_prefix + n)) args) \<notin> fst M"
    using rel unfolding def_state_rel_def by blast
  have fstMT: "fst MT = fst M \<union> defined_atoms (snd M)"
    using rel unfolding def_state_rel_def by blast
  have "valuation MT (def_translate_atom def_prefix (numericEqAtm (FunctionExpr p) (FunctionExpr p)))
        = Some (Atom (predAtm (Pred (def_prefix + n)) args) \<in> fst MT)"
    by (simp add: pf fn pne_to_def_atom_def valuation_def)
  also have "\<dots> = Some (Atom (predAtm (Pred (def_prefix + n)) args) \<in> defined_atoms (snd M))"
    using notin fstMT by simp
  also have "\<dots> = Some (p \<in> dom (snd M))"
    using defined_atom_iff pf fn by simp
  finally show ?thesis .
qed

lemma val_atom_refl:
  "valuation M (numericEqAtm (FunctionExpr p) (FunctionExpr p))
     = (if p \<in> dom (snd M) then Some True else None)"
  by (cases "snd M p") (auto simp: valuation_def domIff)

text \<open>A well-formed predicate atom carries a declared predicate, hence cannot use
  a (domain-fresh) \<open>Defined_\<close> predicate name.\<close>

lemma wf_predAtm_not_def:
  assumes "wf_atom objT (predAtm (Pred (def_prefix + m)) vs)"
  shows False
proof -
  from assms have "wf_pred_atom objT (Pred (def_prefix + m), vs)" by simp
  then obtain Ts where "sig (Pred (def_prefix + m)) = Some Ts"
    by (auto split: option.splits)
  hence "PredDecl (Pred (def_prefix + m)) Ts \<in> set (predicates D)" using sig_Some by simp
  hence "def_prefix + m \<in> set pred_names" by (force simp: image_iff)
  thus False using def_prefix_fresh by blast
qed

lemma defined_atoms_predAtm_shape:
  assumes "Atom (predAtm q vs) \<in> defined_atoms ns"
  shows "\<exists>m. q = Pred (def_prefix + m)"
proof -
  from assms obtain pne where "predAtm q vs = pne_to_def_atom def_prefix pne"
    unfolding defined_atoms_def by auto
  moreover obtain f a where "pne = PNE f a" by (cases pne)
  moreover obtain m where "f = Func m" by (cases f)
  ultimately show ?thesis by (auto simp: pne_to_def_atom_def)
qed

lemma def_translate_atom_id:
  assumes "\<forall>p. a \<noteq> numericEqAtm (FunctionExpr p) (FunctionExpr p)"
  shows "def_translate_atom pfx a = a"
  using assms by (cases "(pfx, a)" rule: def_translate_atom.cases) auto

text \<open>On every atom other than a reflexive definedness atom, the translated atom
  reads identically on related states.\<close>

lemma valT_atom_eq:
  assumes rel: "def_state_rel M MT"
    and wf: "wf_atom objT a"
    and nr: "\<forall>p. a \<noteq> numericEqAtm (FunctionExpr p) (FunctionExpr p)"
  shows "valuation MT (def_translate_atom def_prefix a) = valuation M a"
proof -
  have id: "def_translate_atom def_prefix a = a" using nr def_translate_atom_id by blast
  show ?thesis
  proof (cases a)
    case (predAtm q vs)
    have "Atom (predAtm q vs) \<notin> defined_atoms (snd M)"
    proof
      assume "Atom (predAtm q vs) \<in> defined_atoms (snd M)"
      then obtain m where "q = Pred (def_prefix + m)" using defined_atoms_predAtm_shape by blast
      with wf predAtm wf_predAtm_not_def show False by blast
    qed
    thus ?thesis using rel id predAtm unfolding def_state_rel_def by (auto simp: valuation_def)
  next
    case (eqAtm x y) thus ?thesis using id by (simp add: valuation_def)
  next
    case (numericEqAtm l r) thus ?thesis using rel id unfolding def_state_rel_def by (simp add: valuation_def)
  next
    case (numericLessAtm l r) thus ?thesis using rel id unfolding def_state_rel_def by (simp add: valuation_def)
  next
    case (numericLEAtm l r) thus ?thesis using rel id unfolding def_state_rel_def by (simp add: valuation_def)
  next
    case (numericGreaterAtm l r) thus ?thesis using rel id unfolding def_state_rel_def by (simp add: valuation_def)
  next
    case (numericGEAtm l r) thus ?thesis using rel id unfolding def_state_rel_def by (simp add: valuation_def)
  qed
qed

subsection \<open>Formula evaluation is preserved by the atom translation\<close>

text \<open>Under the definedness-explicated conjunctive invariant, the translation
  preserves \<open>\<Turnstile>\<^sub>m\<close>. The two valuations agree on every atom except a reflexive
  definedness atom of an undefined PNE; but the invariant forces that atom into
  the positive conjunctive prefix, so both sides collapse to \<open>False\<close> there.\<close>

lemma val_def_translate_fmla:
  assumes rel: "def_state_rel M MT"
    and wf: "wf_fmla objT \<phi>"
    and dec: "is_def_explicated_conj \<phi>"
  shows "(valuation MT \<Turnstile>\<^sub>m def_translate_fmla def_prefix \<phi>) = (valuation M \<Turnstile>\<^sub>m \<phi>)"
proof -
  let ?A' = "valuation MT \<circ> def_translate_atom def_prefix"
  have map: "(valuation MT \<Turnstile>\<^sub>m def_translate_fmla def_prefix \<phi>) = (?A' \<Turnstile>\<^sub>m \<phi>)"
    unfolding def_translate_fmla_def by (rule map_formula_semantics_map)
  show ?thesis
  proof (cases "\<forall>a \<in> atoms \<phi>. ?A' a = valuation M a")
    case True
    hence "(?A' \<Turnstile>\<^sub>m \<phi>) = (valuation M \<Turnstile>\<^sub>m \<phi>)"
      by (rule map_relevant_atoms_same_semantics)
    thus ?thesis using map by simp
  next
    case False
    then obtain a where a_in: "a \<in> atoms \<phi>" and a_ne: "?A' a \<noteq> valuation M a" by auto
    have wfa: "wf_atom objT a" using wf a_in by (auto simp: wf_fmla_alt)
    have "\<not> (\<forall>p. a \<noteq> numericEqAtm (FunctionExpr p) (FunctionExpr p))"
    proof
      assume "\<forall>p. a \<noteq> numericEqAtm (FunctionExpr p) (FunctionExpr p)"
      hence "?A' a = valuation M a" using valT_atom_eq[OF rel wfa] by (simp add: comp_def)
      with a_ne show False ..
    qed
    then obtain p where ap: "a = numericEqAtm (FunctionExpr p) (FunctionExpr p)" by auto
    have A'a: "?A' a = Some (p \<in> dom (snd M))"
      using valT_atom_refl[OF rel] ap by (simp add: comp_def)
    have Ma: "valuation M a = (if p \<in> dom (snd M) then Some True else None)"
      using val_atom_refl ap by simp
    from a_ne A'a Ma have pundef: "p \<notin> dom (snd M)" by (auto split: if_splits)
    have "p \<in> set (atom_enumerate_primitive_numeric_expressions a)" using ap by simp
    hence "p \<in> set (formula_enumerate_primitive_numeric_expressions \<phi>)"
      using a_in by (auto simp: set_formula_enumerate_primitive_numeric_expressions_conv)
    hence inprefix: "numericEqAtm (FunctionExpr p) (FunctionExpr p) \<in> set (conj_atom_prefix \<phi>)"
      using dec unfolding is_def_explicated_conj_def by blast
    have notM: "\<not> (valuation M \<Turnstile>\<^sub>m \<phi>)"
    proof
      assume a1: "valuation M \<Turnstile>\<^sub>m \<phi>"
      from conj_atom_prefix_entails[OF inprefix a1]
      have "valuation M (numericEqAtm (FunctionExpr p) (FunctionExpr p)) = Some True" by simp
      thus False using pundef val_atom_refl by simp
    qed
    have notA': "\<not> (?A' \<Turnstile>\<^sub>m \<phi>)"
    proof
      assume a2: "?A' \<Turnstile>\<^sub>m \<phi>"
      from conj_atom_prefix_entails[OF inprefix a2]
      have "?A' (numericEqAtm (FunctionExpr p) (FunctionExpr p)) = Some True" by simp
      thus False using pundef A'a ap by (simp add: comp_def)
    qed
    have "(?A' \<Turnstile>\<^sub>m \<phi>) = (valuation M \<Turnstile>\<^sub>m \<phi>)" using notM notA' by simp
    thus ?thesis using map by simp
  qed
qed

subsection \<open>Initial states are related\<close>

lemma init_def_fact_SomeD:
  assumes "init_def_fact def_prefix f = Some g"
  obtains l r where "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
    "g = Atom (pne_to_def_atom def_prefix l)"
  using assms by (auto simp: init_def_fact_def split: formula.splits atom.splits numeric_expression.splits)

lemma init_def_fact_predAtom:
  assumes "g \<in> set (List.map_filter (init_def_fact def_prefix) (init P))"
  shows "is_predAtom g \<and> \<not> is_numericInitializationAtom g"
proof -
  from assms obtain f where "init_def_fact def_prefix f = Some g" by (auto simp: set_map_filter)
  then obtain l r where "g = Atom (pne_to_def_atom def_prefix l)" by (rule init_def_fact_SomeD)
  thus ?thesis by (cases l rule: primitive_numeric_expression.exhaust)
                  (auto simp: pne_to_def_atom_def split: func.splits)
qed

lemma numInit_shapeD:
  assumes "is_numericInitializationAtom x"
  obtains l r where "x = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
  using assms by (cases x rule: is_numericInitializationAtom.cases) auto

lemma dom_snd_I:
  "p \<in> dom (snd I) \<longleftrightarrow> (\<exists>r. Atom (numericEqAtm (FunctionExpr p) (ConstantExpr r)) \<in> set (init P))"
proof -
  let ?ex = "\<lambda>x. case x of Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r)) \<Rightarrow> (l, real_of_rat r) | _ \<Rightarrow> undefined"
  have dom: "dom (snd I) = fst ` set (map ?ex (filter is_numericInitializationAtom (init P)))"
    by (simp add: dom_map_of_conv_image_fst)
  show ?thesis
  proof
    assume "p \<in> dom (snd I)"
    then obtain x where x: "x \<in> set (init P)" "is_numericInitializationAtom x" "fst (?ex x) = p"
      using dom by auto
    from x(2) obtain l r where lr: "x = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
      by (rule numInit_shapeD)
    from x(3) lr have "p = l" by simp
    with x(1) lr show "\<exists>r. Atom (numericEqAtm (FunctionExpr p) (ConstantExpr r)) \<in> set (init P)" by auto
  next
    assume "\<exists>r. Atom (numericEqAtm (FunctionExpr p) (ConstantExpr r)) \<in> set (init P)"
    then obtain r where r: "Atom (numericEqAtm (FunctionExpr p) (ConstantExpr r)) \<in> set (init P)" by blast
    hence "Atom (numericEqAtm (FunctionExpr p) (ConstantExpr r)) \<in> set (filter is_numericInitializationAtom (init P))" by simp
    hence "(p, real_of_rat r) \<in> set (map ?ex (filter is_numericInitializationAtom (init P)))"
      by (force simp del: filter_set)
    thus "p \<in> dom (snd I)" using dom by force
  qed
qed

lemma map_filter_init_eq_defined_atoms:
  "set (List.map_filter (init_def_fact def_prefix) (init P)) = defined_atoms (snd I)"
proof (rule set_eqI, rule iffI)
  fix g assume "g \<in> set (List.map_filter (init_def_fact def_prefix) (init P))"
  then obtain f where f: "f \<in> set (init P)" "init_def_fact def_prefix f = Some g"
    by (auto simp: set_map_filter)
  from f(2) obtain l r where lr: "f = Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))"
    "g = Atom (pne_to_def_atom def_prefix l)" by (rule init_def_fact_SomeD)
  from f(1) lr(1) have "l \<in> dom (snd I)" using dom_snd_I by blast
  thus "g \<in> defined_atoms (snd I)" unfolding defined_atoms_def using lr(2) by blast
next
  fix g assume "g \<in> defined_atoms (snd I)"
  then obtain l where l: "l \<in> dom (snd I)" "g = Atom (pne_to_def_atom def_prefix l)"
    unfolding defined_atoms_def by blast
  from l(1) obtain r where r: "Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r)) \<in> set (init P)"
    using dom_snd_I by blast
  have "init_def_fact def_prefix (Atom (numericEqAtm (FunctionExpr l) (ConstantExpr r))) = Some g"
    using l(2) by (simp add: init_def_fact_def)
  thus "g \<in> set (List.map_filter (init_def_fact def_prefix) (init P))"
    using r by (auto simp: set_map_filter)
qed

lemma fst_I_not_def: "Atom (predAtm (Pred (def_prefix + n)) args) \<notin> fst I"
proof
  assume "Atom (predAtm (Pred (def_prefix + n)) args) \<in> fst I"
  hence inP: "Atom (predAtm (Pred (def_prefix + n)) args) \<in> set (init P)" by simp
  with wf_P(4) have "wf_fmla_atom objT (Atom (predAtm (Pred (def_prefix + n)) args)) \<or> wf_func_assign (Atom (predAtm (Pred (def_prefix + n)) args))" by blast
  hence "wf_fmla_atom objT (Atom (predAtm (Pred (def_prefix + n)) args))" by simp
  hence "wf_pred_atom objT (Pred (def_prefix + n), args)" by simp
  then obtain Ts where "sig (Pred (def_prefix + n)) = Some Ts" by (auto split: option.splits)
  hence "PredDecl (Pred (def_prefix + n)) Ts \<in> set (predicates D)" using sig_Some by simp
  hence "def_prefix + n \<in> set pred_names" by (force simp: image_iff)
  thus False using def_prefix_fresh by blast
qed

lemma def_state_rel_I: "def_state_rel I pt.I"
  unfolding def_state_rel_def
proof (intro conjI allI)
  let ?new = "remdups (List.map_filter (init_def_fact def_prefix) (init P))"
  have new_notnum: "filter is_numericInitializationAtom ?new = []"
    using init_def_fact_predAtom by (auto simp: filter_empty_conv)
  have new_pred: "filter is_predAtom ?new = ?new"
    using init_def_fact_predAtom by (auto simp: filter_id_conv)
  show "snd pt.I = snd I" by (simp add: new_notnum)
  show "fst pt.I = fst I \<union> defined_atoms (snd I)"
    by (simp add: new_pred map_filter_init_eq_defined_atoms)
  show "Atom (predAtm (Pred (def_prefix + n)) args) \<notin> fst I" for n args by (rule fst_I_not_def)
qed

subsection \<open>Resolution and plan-action well-formedness under the translation\<close>

text \<open>Resolution in the translated problem is the \<open>def_translate_ac\<close>-image of
  resolution in the original: \<open>def_translate_ac\<close> leaves the action head (hence
  \<open>ac_name\<close>) untouched, so the \<open>index_by ac_name\<close> lookup commutes with the map.\<close>

lemma map_of_pair_map:
  "map_of (map (\<lambda>x. (f x, g x)) xs) n = map_option g (map_of (map (\<lambda>x. (f x, x)) xs) n)"
  by (induction xs) auto

lemma pt_resolve:
  "pt.resolve_classical_action_schema n
   = map_option (def_translate_ac def_prefix) (resolve_classical_action_schema n)"
proof -
  have "pt.resolve_classical_action_schema n
      = map_of (map (\<lambda>x. (ac_name x, def_translate_ac def_prefix x)) (actions D)) n"
    unfolding pt.resolve_classical_action_schema_def index_by_def
    by (simp add: comp_def dt_ac_name)
  also have "\<dots> = map_option (def_translate_ac def_prefix) (resolve_classical_action_schema n)"
    unfolding resolve_classical_action_schema_def index_by_def by (rule map_of_pair_map)
  finally show ?thesis .
qed

lemma dt_ac_head:
  "ast_classical_action_schema.head (def_translate_ac def_prefix a) = ast_classical_action_schema.head a"
proof (cases a)
  case (SimpleActionSchema h b)
  obtain pre eff where "b = SimpleActionBody pre eff" by (cases b)
  moreover obtain ad dl ne where "eff = Effect ad dl ne" by (cases eff)
  ultimately show ?thesis using SimpleActionSchema by (simp add: Let_def)
qed

lemma wf_classical_plan_action_iff:
  "pt.wf_classical_plan_action \<pi> \<longleftrightarrow> wf_classical_plan_action \<pi>"
proof (cases \<pi>)
  case (SimplePlanAction n args)
  show ?thesis
    unfolding SimplePlanAction pt.wf_classical_plan_action_simple wf_classical_plan_action_simple pt_resolve
    by (auto simp: dt_ac_head split: option.splits)
qed

subsection \<open>Substitution commutes with the atom translation\<close>

lemma val_foldr_and:
  "(\<A> \<Turnstile>\<^sub>m foldr (\<^bold>\<and>) (map Atom as) F) \<longleftrightarrow> (\<A> \<Turnstile>\<^sub>m F) \<and> (\<forall>a\<in>set as. \<A> a = Some True)"
  by (induction as) auto

lemma rhs_pnes_num_eff_eq:
  "rhs_pnes_num_eff ne = numeric_effect_enumerate_rhs_primitive_numeric_expressions ne"
  by (cases ne) (simp add: rhs_pnes_num_eff_def)

lemma rhs_pnes_eff_eq:
  "rhs_pnes_eff E = ast_effect_enumerate_rhs_primitive_numeric_expressions E"
  by (cases E) (simp cong: map_cong add: rhs_pnes_num_eff_eq)

lemma pne_to_def_atom_map:
  "map_atom \<sigma> (pne_to_def_atom pfx q) = pne_to_def_atom pfx (map_primitive_numeric_expression \<sigma> q)"
proof (cases q)
  case (PNE f a)
  thus ?thesis by (cases f) (simp add: pne_to_def_atom_def)
qed

lemma valT_val_eq_wf:
  assumes rel: "def_state_rel M MT" and wf: "wf_atom objT b"
  shows "valuation MT b = valuation M b"
proof (cases b)
  case (predAtm q vs)
  have "Atom (predAtm q vs) \<notin> defined_atoms (snd M)"
  proof
    assume "Atom (predAtm q vs) \<in> defined_atoms (snd M)"
    then obtain m where "q = Pred (def_prefix + m)" using defined_atoms_predAtm_shape by blast
    with wf predAtm wf_predAtm_not_def show False by blast
  qed
  thus ?thesis using rel predAtm unfolding def_state_rel_def by (auto simp: valuation_def)
qed (use rel in \<open>auto simp: valuation_def def_state_rel_def\<close>)

lemma valT_def_atom:
  assumes "def_state_rel M MT"
  shows "valuation MT (pne_to_def_atom def_prefix p) = Some (p \<in> dom (snd M))"
  using valT_atom_refl[OF assms, of p] by simp

lemma enumerate_primitive_numeric_expressions_map:
  "enumerate_primitive_numeric_expressions (map_numeric_expression m e)
    = map (map_primitive_numeric_expression m) (enumerate_primitive_numeric_expressions e)"
  by (induction e) auto

lemma atom_enumerate_primitive_numeric_expressions_map:
  "atom_enumerate_primitive_numeric_expressions (map_atom m a)
    = map (map_primitive_numeric_expression m) (atom_enumerate_primitive_numeric_expressions a)"
  by (cases a) (auto simp: enumerate_primitive_numeric_expressions_map)

lemma formula_enumerate_primitive_numeric_expressions_map:
  "formula_enumerate_primitive_numeric_expressions (map_formula (map_atom m) F)
    = map (map_primitive_numeric_expression m) (formula_enumerate_primitive_numeric_expressions F)"
  by (induction F) (auto simp: atom_enumerate_primitive_numeric_expressions_map)

lemma conj_atom_prefix_map_formula:
  "conj_atom_prefix (map_formula h f) = map h (conj_atom_prefix f)"
  by (induction f rule: conj_atom_prefix.induct) auto

lemma is_def_explicated_conj_map_atom_fmla:
  assumes "is_def_explicated_conj f"
  shows "is_def_explicated_conj (map_atom_fmla m f)"
  unfolding is_def_explicated_conj_def
proof (intro ballI)
  fix p' assume "p' \<in> set (formula_enumerate_primitive_numeric_expressions (map_atom_fmla m f))"
  then obtain p where p:
    "p \<in> set (formula_enumerate_primitive_numeric_expressions f)"
    "p' = map_primitive_numeric_expression m p"
    using formula_enumerate_primitive_numeric_expressions_map[of m f]
    by (auto simp: comp_def)
  from p(1) assms have prefix_f:
    "numericEqAtm (FunctionExpr p) (FunctionExpr p) \<in> set (conj_atom_prefix f)"
    unfolding is_def_explicated_conj_def by blast
  have "map_atom m (numericEqAtm (FunctionExpr p) (FunctionExpr p))
        = numericEqAtm (FunctionExpr p') (FunctionExpr p')"
    using p(2) by simp
  with prefix_f show "numericEqAtm (FunctionExpr p') (FunctionExpr p')
                       \<in> set (conj_atom_prefix (map_atom_fmla m f))"
    unfolding comp_def conj_atom_prefix_map_formula by force
qed

text \<open>Truth-preservation lifted to the \<^emph>\<open>instantiated\<close> precondition: the
  invariant transports through the parameter substitution \<open>\<sigma>\<close>.\<close>

lemma val_inst_def_translate:
  assumes rel: "def_state_rel M MT"
    and wf: "wf_fmla objT (map_atom_fmla \<sigma> \<phi>)"
    and dec: "is_def_explicated_conj \<phi>"
  shows "(valuation MT \<Turnstile>\<^sub>m map_atom_fmla \<sigma> (def_translate_fmla def_prefix \<phi>))
       = (valuation M \<Turnstile>\<^sub>m map_atom_fmla \<sigma> \<phi>)"
proof -
  let ?g = "map_atom \<sigma> \<circ> def_translate_atom def_prefix"
  let ?A' = "valuation MT \<circ> ?g"
  let ?B = "valuation M \<circ> map_atom \<sigma>"
  have eq1: "map_atom_fmla \<sigma> (def_translate_fmla def_prefix \<phi>) = map_formula ?g \<phi>"
    by (simp add: def_translate_fmla_def formula.map_comp comp_apply)
  have mapL: "(valuation MT \<Turnstile>\<^sub>m map_atom_fmla \<sigma> (def_translate_fmla def_prefix \<phi>)) = (?A' \<Turnstile>\<^sub>m \<phi>)"
    unfolding eq1 by (rule map_formula_semantics_map)
  have mapR: "(valuation M \<Turnstile>\<^sub>m map_atom_fmla \<sigma> \<phi>) = (?B \<Turnstile>\<^sub>m \<phi>)"
    by (simp add: comp_apply map_formula_semantics_map)
  show ?thesis
  proof (cases "\<forall>a \<in> atoms \<phi>. ?A' a = ?B a")
    case True
    hence "(?A' \<Turnstile>\<^sub>m \<phi>) = (?B \<Turnstile>\<^sub>m \<phi>)" by (rule map_relevant_atoms_same_semantics)
    thus ?thesis using mapL mapR by simp
  next
    case False
    then obtain a where a_in: "a \<in> atoms \<phi>" and a_ne: "?A' a \<noteq> ?B a" by auto
    have wfsa: "wf_atom objT (map_atom \<sigma> a)"
      using wf a_in by (auto simp: wf_fmla_alt formula.set_map)
    have "\<not> (\<forall>p. a \<noteq> numericEqAtm (FunctionExpr p) (FunctionExpr p))"
    proof
      assume nr: "\<forall>p. a \<noteq> numericEqAtm (FunctionExpr p) (FunctionExpr p)"
      hence "def_translate_atom def_prefix a = a" by (rule def_translate_atom_id)
      hence "?A' a = valuation MT (map_atom \<sigma> a)" by (simp add: comp_def)
      also have "\<dots> = valuation M (map_atom \<sigma> a)" using valT_val_eq_wf[OF rel wfsa] .
      also have "\<dots> = ?B a" by (simp add: comp_def)
      finally show False using a_ne by simp
    qed
    then obtain p where ap: "a = numericEqAtm (FunctionExpr p) (FunctionExpr p)" by auto
    let ?q = "map_primitive_numeric_expression \<sigma> p"
    have A'a: "?A' a = Some (?q \<in> dom (snd M))"
      using ap by (simp add: comp_def pne_to_def_atom_map valT_def_atom[OF rel])
    have Ba: "?B a = (if ?q \<in> dom (snd M) then Some True else None)"
      using ap by (simp add: comp_def val_atom_refl)
    from a_ne A'a Ba have qundef: "?q \<notin> dom (snd M)" by (auto split: if_splits)
    have "p \<in> set (atom_enumerate_primitive_numeric_expressions a)" using ap by simp
    hence "p \<in> set (formula_enumerate_primitive_numeric_expressions \<phi>)"
      using a_in by (auto simp: set_formula_enumerate_primitive_numeric_expressions_conv)
    hence inprefix: "numericEqAtm (FunctionExpr p) (FunctionExpr p) \<in> set (conj_atom_prefix \<phi>)"
      using dec unfolding is_def_explicated_conj_def by blast
    have notB: "\<not> (?B \<Turnstile>\<^sub>m \<phi>)"
    proof
      assume a1: "?B \<Turnstile>\<^sub>m \<phi>"
      from conj_atom_prefix_entails[OF inprefix a1]
      have "?B (numericEqAtm (FunctionExpr p) (FunctionExpr p)) = Some True" by simp
      thus False using qundef Ba ap by (simp add: comp_def)
    qed
    have notA': "\<not> (?A' \<Turnstile>\<^sub>m \<phi>)"
    proof
      assume a2: "?A' \<Turnstile>\<^sub>m \<phi>"
      from conj_atom_prefix_entails[OF inprefix a2]
      have "?A' (numericEqAtm (FunctionExpr p) (FunctionExpr p)) = Some True" by simp
      thus False using qundef A'a ap by (simp add: comp_def)
    qed
    have "(?A' \<Turnstile>\<^sub>m \<phi>) = (?B \<Turnstile>\<^sub>m \<phi>)" using notB notA' by simp
    thus ?thesis using mapL mapR by simp
  qed
qed

subsection \<open>Enabledness coincides on related states\<close>

text \<open>Enabledness coincides: the resolved/instantiated ground action has an
  identical numeric effect, the original \<open>plan_action_enabled\<close> already requires
  \<open>rhs_pnes \<subseteq> dom (snd M)\<close>, and the translated precondition conjoins precisely the
  matching \<open>Defined_q\<close> atoms, with the boolean precondition handled by
  \<open>val_inst_def_translate\<close>.\<close>

lemma dt_ac_pre:
  "ac_pre (def_translate_ac def_prefix a)
   = foldr (\<^bold>\<and>) (map Atom (map (pne_to_def_atom def_prefix) (remdups (rhs_pnes_eff (ac_eff a)))))
        (def_translate_fmla def_prefix (ac_pre a))"
proof (cases a)
  case (SimpleActionSchema h b)
  obtain pre eff where "b = SimpleActionBody pre eff" by (cases b)
  moreover obtain ad dl ne where "eff = Effect ad dl ne" by (cases eff)
  ultimately show ?thesis using SimpleActionSchema by (simp add: Let_def)
qed

lemma dt_ac_eff:
  "ac_eff (def_translate_ac def_prefix a)
   = Effect (map Atom (map (pne_to_def_atom def_prefix) (remdups (lhs_pnes_eff (ac_eff a)))) @ adds (ac_eff a))
        (dels (ac_eff a)) (numeric_effects (ac_eff a))"
proof (cases a)
  case (SimpleActionSchema h b)
  obtain pre eff where "b = SimpleActionBody pre eff" by (cases b)
  moreover obtain ad dl ne where "eff = Effect ad dl ne" by (cases eff)
  ultimately show ?thesis using SimpleActionSchema by (simp add: Let_def)
qed

lemma dt_ac_params: "ac_params (def_translate_ac def_prefix a) = ac_params a"
  by (simp add: dt_ac_head)

lemma map_fmla_foldr_and:
  "map_atom_fmla m (foldr (\<^bold>\<and>) (map Atom as) F) = foldr (\<^bold>\<and>) (map Atom (map (map_atom m) as)) (map_atom_fmla m F)"
  by (induction as) auto

lemma rhs_pnes_num_eff_map:
  "rhs_pnes_num_eff (map_numeric_effect m ne) = map (map_primitive_numeric_expression m) (rhs_pnes_num_eff ne)"
  by (cases ne) (simp add: rhs_pnes_num_eff_def enumerate_primitive_numeric_expressions_map)

lemma lhs_pnes_num_eff_map:
  "lhs_pnes_num_eff (map_numeric_effect m ne) = map (map_primitive_numeric_expression m) (lhs_pnes_num_eff ne)"
  by (cases ne) (simp add: lhs_pnes_num_eff_def split: numeric_effect_op.splits)

lemma rhs_pnes_eff_map:
  "rhs_pnes_eff (map_ast_effect m E) = map (map_primitive_numeric_expression m) (rhs_pnes_eff E)"
  by (cases E) (simp add: rhs_pnes_num_eff_map map_concat cong: map_cong)

lemma lhs_pnes_eff_map:
  "lhs_pnes_eff (map_ast_effect m E) = map (map_primitive_numeric_expression m) (lhs_pnes_eff E)"
  by (cases E) (simp add: lhs_pnes_num_eff_map map_concat cong: map_cong)

lemma dt_resolve:
  "dt.resolve_classical_action_schema n
   = map_option (def_translate_ac def_prefix) (resolve_classical_action_schema n)"
proof -
  have "dt.resolve_classical_action_schema n
      = map_of (map (\<lambda>x. (ac_name x, def_translate_ac def_prefix x)) (actions D)) n"
    unfolding dt.resolve_classical_action_schema_def index_by_def
    by (simp add: comp_def dt_ac_name)
  also have "\<dots> = map_option (def_translate_ac def_prefix) (resolve_classical_action_schema n)"
    unfolding resolve_classical_action_schema_def index_by_def by (rule map_of_pair_map)
  finally show ?thesis .
qed

lemma pt_res_inst_alt:
  assumes res: "resolve_classical_action_schema n = Some a"
  shows "pt.res_inst (SimplePlanAction n args)
       = Some (instantiate_classical_action_schema (def_translate_ac def_prefix a) args)"
  using pt.res_inst_alt[of "SimplePlanAction n args"] res by (simp add: dt_resolve)

lemma defatoms_all_true_iff:
  assumes rel: "def_state_rel M MT"
  shows "(\<forall>d \<in> set (map (map_atom \<sigma>) (map (pne_to_def_atom def_prefix) (remdups (rhs_pnes_eff E)))). valuation MT d = Some True)
       \<longleftrightarrow> set (ast_effect_enumerate_rhs_primitive_numeric_expressions (map_ast_effect \<sigma> E)) \<subseteq> dom (snd M)"
proof -
  have "(\<forall>d \<in> set (map (map_atom \<sigma>) (map (pne_to_def_atom def_prefix) (remdups (rhs_pnes_eff E)))). valuation MT d = Some True)
      = (\<forall>q \<in> set (rhs_pnes_eff E). valuation MT (pne_to_def_atom def_prefix (map_primitive_numeric_expression \<sigma> q)) = Some True)"
    by (simp add: pne_to_def_atom_map)
  also have "\<dots> = (\<forall>q \<in> set (rhs_pnes_eff E). map_primitive_numeric_expression \<sigma> q \<in> dom (snd M))"
    by (simp add: valT_def_atom[OF rel])
  also have "\<dots> = (set (map (map_primitive_numeric_expression \<sigma>) (rhs_pnes_eff E)) \<subseteq> dom (snd M))"
    by auto
  also have "\<dots> = (set (ast_effect_enumerate_rhs_primitive_numeric_expressions (map_ast_effect \<sigma> E)) \<subseteq> dom (snd M))"
    by (simp add: rhs_pnes_eff_eq[symmetric] rhs_pnes_eff_map)
  finally show ?thesis .
qed

lemma wf_inst_pre_dec:
  assumes ina: "a \<in> set (actions D)"
    and pm: "action_params_match (ac_head a) args"
  shows "wf_fmla objT (map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a))"
    and "is_def_explicated_conj (ac_pre a)"
proof -
  have wfa: "wf_classical_action_schema a" using wf_D(3) ina by (simp add: list_all_iff)
  obtain h b where ab: "a = SimpleActionSchema h b" by (cases a)
  have "wf_ground_action (instantiate_classical_action_schema a args)"
    using wf_inst_action_schema[of h args b] wfa pm ab by simp
  hence "wf_fmla objT (precondition (instantiate_classical_action_schema a args))" by (cases "instantiate_classical_action_schema a args") simp
  thus "wf_fmla objT (map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a))"
    by (simp add: instantiate_classical_action_schema_alt)
  show "is_def_explicated_conj (ac_pre a)"
    using def_explicated_conj_dom ina unfolding def_explicated_conj_dom_def by blast
qed

lemma val_pre_foldr_subst:
  "(valuation MT \<Turnstile>\<^sub>m map_atom_fmla \<sigma> (foldr (\<^bold>\<and>) (map Atom (map (pne_to_def_atom def_prefix) L)) F))
   = ((valuation MT \<Turnstile>\<^sub>m map_atom_fmla \<sigma> F)
      \<and> (\<forall>q \<in> set L. valuation MT (pne_to_def_atom def_prefix (map_primitive_numeric_expression \<sigma> q)) = Some True))"
proof (induction L)
  case Nil thus ?case by simp
next
  case (Cons q L)
  have "map_atom_fmla \<sigma> (foldr (\<^bold>\<and>) (map Atom (map (pne_to_def_atom def_prefix) (q # L))) F)
      = (Atom (pne_to_def_atom def_prefix (map_primitive_numeric_expression \<sigma> q)))
        \<^bold>\<and> map_atom_fmla \<sigma> (foldr (\<^bold>\<and>) (map Atom (map (pne_to_def_atom def_prefix) L)) F)"
    by (simp add: pne_to_def_atom_map)
  thus ?case using Cons by auto
qed

text \<open>The translated precondition holds in \<open>MT\<close> exactly when, in \<open>M\<close>, the original
  precondition holds \<^emph>\<open>and\<close> all right-hand-side PNEs are defined --- precisely the
  numeric-definedness side-condition that the original \<open>plan_action_enabled\<close>
  carries separately.\<close>

lemma pt_pre_iff:
  assumes rel: "def_state_rel M MT"
    and res: "resolve_classical_action_schema n = Some a"
    and ina: "a \<in> set (actions D)"
    and pm: "action_params_match (ac_head a) args"
  shows "(valuation MT \<Turnstile>\<^sub>m precondition (the (pt.res_inst (SimplePlanAction n args))))
       \<longleftrightarrow> (set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect (the (res_inst (SimplePlanAction n args))))) \<subseteq> dom (snd M)
            \<and> valuation M \<Turnstile>\<^sub>m precondition (the (res_inst (SimplePlanAction n args))))"
proof -
  let ?\<sigma> = "ac_tsubst (ac_params a) args"
  have g: "the (res_inst (SimplePlanAction n args)) = instantiate_classical_action_schema a args"
    using res_inst_alt[of "SimplePlanAction n args"] res by simp
  have preg: "precondition (the (res_inst (SimplePlanAction n args))) = map_atom_fmla ?\<sigma> (ac_pre a)"
    unfolding g by (simp add: instantiate_classical_action_schema_alt)
  have effg: "effect (the (res_inst (SimplePlanAction n args))) = map_ast_effect ?\<sigma> (ac_eff a)"
    unfolding g by (simp add: instantiate_classical_action_schema_alt)
  have preT0: "precondition (the (pt.res_inst (SimplePlanAction n args)))
      = map_atom_fmla ?\<sigma> (foldr (\<^bold>\<and>) (map Atom (map (pne_to_def_atom def_prefix) (remdups (rhs_pnes_eff (ac_eff a))))) (def_translate_fmla def_prefix (ac_pre a)))"
    unfolding pt_res_inst_alt[OF res] option.sel
    by (simp add: instantiate_classical_action_schema_alt dt_ac_params dt_ac_pre)
  have wfpre: "wf_fmla objT (map_atom_fmla ?\<sigma> (ac_pre a))"
    and decpre: "is_def_explicated_conj (ac_pre a)"
    using wf_inst_pre_dec[OF ina pm] by blast+
  have c1: "(valuation MT \<Turnstile>\<^sub>m map_atom_fmla ?\<sigma> (def_translate_fmla def_prefix (ac_pre a)))
          = (valuation M \<Turnstile>\<^sub>m map_atom_fmla ?\<sigma> (ac_pre a))"
    by (rule val_inst_def_translate[OF rel wfpre decpre])
  have c2: "(\<forall>q \<in> set (remdups (rhs_pnes_eff (ac_eff a))). valuation MT (pne_to_def_atom def_prefix (map_primitive_numeric_expression ?\<sigma> q)) = Some True)
          = (set (ast_effect_enumerate_rhs_primitive_numeric_expressions (map_ast_effect ?\<sigma> (ac_eff a))) \<subseteq> dom (snd M))"
    by (auto simp: valT_def_atom[OF rel] rhs_pnes_eff_eq[symmetric] rhs_pnes_eff_map)
  have "(valuation MT \<Turnstile>\<^sub>m precondition (the (pt.res_inst (SimplePlanAction n args))))
      = ((valuation MT \<Turnstile>\<^sub>m map_atom_fmla ?\<sigma> (def_translate_fmla def_prefix (ac_pre a)))
         \<and> (\<forall>q \<in> set (remdups (rhs_pnes_eff (ac_eff a))). valuation MT (pne_to_def_atom def_prefix (map_primitive_numeric_expression ?\<sigma> q)) = Some True))"
    unfolding preT0 by (rule val_pre_foldr_subst)
  also have "\<dots> = (set (ast_effect_enumerate_rhs_primitive_numeric_expressions (map_ast_effect ?\<sigma> (ac_eff a))) \<subseteq> dom (snd M)
         \<and> valuation M \<Turnstile>\<^sub>m map_atom_fmla ?\<sigma> (ac_pre a))"
    using c1 c2 by blast
  finally show ?thesis using preg effg by simp
qed

lemma rhs_pnes_eff_dt:
  "rhs_pnes_eff (ac_eff (def_translate_ac def_prefix a)) = rhs_pnes_eff (ac_eff a)"
  by (cases "ac_eff a") (simp add: dt_ac_eff)

lemma enabled_iff:
  assumes rel: "def_state_rel M MT"
  shows "pt.plan_action_enabled \<pi> MT \<longleftrightarrow> plan_action_enabled \<pi> M"
proof (cases \<pi>)
  case (SimplePlanAction n args)
  show ?thesis
  proof (cases "wf_classical_plan_action \<pi>")
    case False
    hence "\<not> pt.wf_classical_plan_action \<pi>" using wf_classical_plan_action_iff by simp
    with False show ?thesis
      unfolding plan_action_enabled_def pt.plan_action_enabled_def by simp
  next
    case True
    then obtain a where res: "resolve_classical_action_schema n = Some a"
      and pm: "action_params_match (ac_head a) args"
      unfolding SimplePlanAction wf_classical_plan_action_simple
      by (auto split: option.splits)
    have ina: "a \<in> set (actions D)" using res res_aux by simp
    let ?\<sigma> = "ac_tsubst (ac_params a) args"
    have effO: "effect (the (res_inst (SimplePlanAction n args))) = map_ast_effect ?\<sigma> (ac_eff a)"
      using res_inst_alt[of "SimplePlanAction n args"] res
      by (simp add: instantiate_classical_action_schema_alt)
    have effT: "effect (the (pt.res_inst (SimplePlanAction n args))) = map_ast_effect ?\<sigma> (ac_eff (def_translate_ac def_prefix a))"
      unfolding pt_res_inst_alt[OF res] option.sel
      by (simp add: instantiate_classical_action_schema_alt dt_ac_params)
    have ne_eq: "numeric_effects (effect (the (pt.res_inst (SimplePlanAction n args))))
               = numeric_effects (effect (the (res_inst (SimplePlanAction n args))))"
      unfolding effO effT ast_effect.map_sel(3) by (simp add: dt_ac_eff)
    have nint_eq: "numeric_effects_non_intrf (the (pt.res_inst (SimplePlanAction n args)))
                 = numeric_effects_non_intrf (the (res_inst (SimplePlanAction n args)))"
      unfolding numeric_effects_non_intrf_def using ne_eq by simp
    have rhs_eq: "ast_effect_enumerate_rhs_primitive_numeric_expressions (effect (the (pt.res_inst (SimplePlanAction n args))))
                = ast_effect_enumerate_rhs_primitive_numeric_expressions (effect (the (res_inst (SimplePlanAction n args))))"
      unfolding effO effT
      by (simp add: rhs_pnes_eff_eq[symmetric] rhs_pnes_eff_map rhs_pnes_eff_dt)
    have snd_eq: "snd MT = snd M" using rel unfolding def_state_rel_def by simp
    have pre: "(valuation MT \<Turnstile>\<^sub>m precondition (the (pt.res_inst (SimplePlanAction n args))))
             \<longleftrightarrow> (set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect (the (res_inst (SimplePlanAction n args))))) \<subseteq> dom (snd M)
                \<and> valuation M \<Turnstile>\<^sub>m precondition (the (res_inst (SimplePlanAction n args))))"
      by (rule pt_pre_iff[OF rel res ina pm])
    show ?thesis
      unfolding SimplePlanAction pt.plan_action_enabled_def plan_action_enabled_def Let_def o_apply
      by (simp only: wf_classical_plan_action_iff nint_eq rhs_eq snd_eq pre) argo
  qed
qed

subsection \<open>One step preserves the relation\<close>

text \<open>Executing the (translated) action preserves the relation: numeric updates
  are identical, and the translated effect adds exactly the \<open>Defined_q\<close> atoms for
  the LHS PNEs, which is exactly how \<open>dom (snd M)\<close> grows (an assignment makes its
  LHS defined and deletes nothing).\<close>

text \<open>Domain growth of the numeric update: applying a single (Assign-only-tracked)
  numeric effect with a defined right-hand side adds exactly its \<open>Assign\<close> lhs to the
  domain, and removes nothing.\<close>

lemma dom_numeric_update_function_eq:
  assumes "set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e)) \<subseteq> dom N"
  shows "dom (numeric_update_function e N w) = dom w \<union> set (lhs_pnes_num_eff e)"
proof (cases e)
  case (NumericEffect opr l r)
  with assms have "set (enumerate_primitive_numeric_expressions r) \<subseteq> dom N" by simp
  then obtain v where v: "r\<lbrakk>N\<rbrakk> = Some v"
    using numeric_expression_eq_SomeI' by blast
  show ?thesis
    using NumericEffect v
    by (cases opr; cases "w l")
       (auto simp: lhs_pnes_num_eff_def dom_def split: if_splits)
qed

lemma dom_numeric_update_fold:
  assumes "\<forall>e \<in> set es. set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e)) \<subseteq> dom N"
  shows "dom (fold (\<circ>) (map (\<lambda>u. numeric_update_function u N) es) id w)
       = dom w \<union> set (concat (map lhs_pnes_num_eff es))"
  using assms
proof (induction es arbitrary: w)
  case Nil thus ?case by simp
next
  case (Cons e es)
  hence preme: "set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e)) \<subseteq> dom N"
    and prem_es: "\<forall>e \<in> set es. set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e)) \<subseteq> dom N" by simp_all
  have "dom (fold (\<circ>) (map (\<lambda>u. numeric_update_function u N) (e # es)) id w)
      = dom (fold (\<circ>) (map (\<lambda>u. numeric_update_function u N) es) id (numeric_update_function e N w))"
    by (simp add: fold_of_comp'[of "map (\<lambda>u. numeric_update_function u N) es" "numeric_update_function e N" w])
  also have "\<dots> = dom (numeric_update_function e N w) \<union> set (concat (map lhs_pnes_num_eff es))"
    by (rule Cons.IH[OF prem_es])
  also have "\<dots> = dom w \<union> set (lhs_pnes_num_eff e) \<union> set (concat (map lhs_pnes_num_eff es))"
    by (simp add: dom_numeric_update_function_eq[OF preme])
  also have "\<dots> = dom w \<union> set (concat (map lhs_pnes_num_eff (e # es)))" by auto
  finally show ?case .
qed

lemma dom_action_numeric_update_function_eq:
  assumes "\<forall>e \<in> set (numeric_effects (effect a)). set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e)) \<subseteq> dom N"
  shows "dom (action_numeric_update_function a N) = dom N \<union> set (lhs_pnes_eff (effect a))"
  using dom_numeric_update_fold[OF assms, of N]
  by (cases "effect a") (simp add: action_numeric_update_function_def)

lemma execute_preserves_rel:
  assumes rel: "def_state_rel M MT" and en: "plan_action_enabled \<pi> M"
  shows "def_state_rel (execute_plan_action \<pi> M) (pt.execute_plan_action \<pi> MT)"
proof -
  obtain n args where pi: "\<pi> = SimplePlanAction n args" by (cases \<pi>)
  from en have wf: "wf_classical_plan_action \<pi>" by (simp add: plan_action_enabled_def)
  then obtain a where res: "resolve_classical_action_schema n = Some a"
    and pm: "action_params_match (ac_head a) args"
    unfolding pi wf_classical_plan_action_simple by (auto split: option.splits)
  have ina: "a \<in> set (actions D)" using res res_aux by simp
  have effa: "effect (the (res_inst \<pi>)) = map_ast_effect (ac_tsubst (ac_params a) args) (ac_eff a)"
    unfolding pi using res_inst_alt[of "SimplePlanAction n args"] res
    by (simp add: instantiate_classical_action_schema_alt)
  have effaT: "effect (the (pt.res_inst \<pi>)) = map_ast_effect (ac_tsubst (ac_params a) args) (ac_eff (def_translate_ac def_prefix a))"
    unfolding pi using pt_res_inst_alt[OF res]
    by (simp add: instantiate_classical_action_schema_alt dt_ac_params)
  have rhs_sel: "set (rhs_pnes_num_eff e) = set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e))" for e
    by (cases e) (simp add: rhs_pnes_num_eff_def)
  have rhsset: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions E)
    = (\<Union>e\<in>set (numeric_effects E). set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e)))" for E :: "object ast_effect"
    by (cases E) (auto simp: rhs_pnes_eff_eq[symmetric] rhs_sel)
  have ndom: "set (ast_effect_enumerate_rhs_primitive_numeric_expressions (effect (the (res_inst \<pi>)))) \<subseteq> dom (snd M)"
    using plan_action_enabled_props(3)[OF en] by simp
  have ndom_e: "\<forall>e \<in> set (numeric_effects (effect (the (res_inst \<pi>)))). set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e)) \<subseteq> dom (snd M)"
    using ndom rhsset[of "effect (the (res_inst \<pi>))"] by auto
  obtain L N where MLN: "M = (L, N)" by (cases M)
  with rel have MTeq: "MT = (L \<union> defined_atoms N, N)"
    unfolding def_state_rel_def by (cases MT) auto
  have exec: "execute_plan_action \<pi> M
     = ((L - set (dels (effect (the (res_inst \<pi>))))) \<union> set (adds (effect (the (res_inst \<pi>)))),
        action_numeric_update_function (the (res_inst \<pi>)) N)"
    unfolding MLN execute_plan_action_def
    by (simp add: apply_ground_action_alt action_list_numeric_update_function_def)
  have execT: "pt.execute_plan_action \<pi> MT
     = ((L \<union> defined_atoms N - set (dels (effect (the (pt.res_inst \<pi>))))) \<union> set (adds (effect (the (pt.res_inst \<pi>)))),
        action_numeric_update_function (the (pt.res_inst \<pi>)) N)"
    unfolding MTeq pt.execute_plan_action_def
    by (simp add: apply_ground_action_alt action_list_numeric_update_function_def)
  have dels_eq: "dels (effect (the (pt.res_inst \<pi>))) = dels (effect (the (res_inst \<pi>)))"
    unfolding effa effaT by (simp add: dt_ac_eff ast_effect.map_sel)
  have ne_eq: "numeric_effects (effect (the (pt.res_inst \<pi>))) = numeric_effects (effect (the (res_inst \<pi>)))"
    unfolding effa effaT by (simp add: dt_ac_eff ast_effect.map_sel)
  have adds_eq: "adds (effect (the (pt.res_inst \<pi>)))
     = map (map_atom_fmla (ac_tsubst (ac_params a) args)) (map Atom (map (pne_to_def_atom def_prefix) (remdups (lhs_pnes_eff (ac_eff a)))))
       @ adds (effect (the (res_inst \<pi>)))"
    unfolding effa effaT by (simp add: dt_ac_eff ast_effect.map_sel)
  have sndM: "snd M = N" by (simp add: MLN)
  have snd_eq: "snd (pt.execute_plan_action \<pi> MT) = snd (execute_plan_action \<pi> M)"
    unfolding exec execT snd_conv by (simp only: action_numeric_update_function_def ne_eq)
  have ndom_eN: "\<forall>e\<in>set (numeric_effects (effect (the (res_inst \<pi>)))). set (enumerate_primitive_numeric_expressions (numeric_effect.rhs e)) \<subseteq> dom N"
    using ndom_e sndM by simp
  have domexec: "dom (action_numeric_update_function (the (res_inst \<pi>)) N) = dom N \<union> set (lhs_pnes_eff (effect (the (res_inst \<pi>))))"
    by (rule dom_action_numeric_update_function_eq[OF ndom_eN])
  have newadds_set:
    "set (map (map_atom_fmla (ac_tsubst (ac_params a) args)) (map Atom (map (pne_to_def_atom def_prefix) (remdups (lhs_pnes_eff (ac_eff a))))))
     = (\<lambda>p. Atom (pne_to_def_atom def_prefix p)) ` set (lhs_pnes_eff (effect (the (res_inst \<pi>))))"
    unfolding effa
    by (simp add: lhs_pnes_eff_map pne_to_def_atom_map image_image comp_def)
  have wfga: "wf_ground_action (the (res_inst \<pi>))"
    by (rule wf_resolve_instantiate[OF wf])
  have wf_notdef: "Atom (predAtm (Pred (def_prefix + m)) vs)
       \<notin> set (adds (effect (the (res_inst \<pi>)))) \<union> set (dels (effect (the (res_inst \<pi>))))" for m vs
  proof
    assume "Atom (predAtm (Pred (def_prefix + m)) vs) \<in> set (adds (effect (the (res_inst \<pi>)))) \<union> set (dels (effect (the (res_inst \<pi>))))"
    hence "wf_fmla_atom objT (Atom (predAtm (Pred (def_prefix + m)) vs))"
      using wfga by (auto simp: wf_ground_action_alt wf_effect_alt list_all_iff)
    hence "wf_atom objT (predAtm (Pred (def_prefix + m)) vs)" by simp
    thus False using wf_predAtm_not_def by blast
  qed
  have disjN: "defined_atoms N \<inter> set (dels (effect (the (res_inst \<pi>)))) = {}"
  proof safe
    fix x assume xd: "x \<in> defined_atoms N" and xdel: "x \<in> set (dels (effect (the (res_inst \<pi>))))"
    from xd obtain p where xp: "x = Atom (pne_to_def_atom def_prefix p)"
      unfolding defined_atoms_def by auto
    obtain f aa where "p = PNE f aa" by (cases p)
    moreover obtain k where "f = Func k" by (cases f)
    ultimately have "x = Atom (predAtm (Pred (def_prefix + k)) aa)"
      using xp by (simp add: pne_to_def_atom_def)
    thus "x \<in> {}" using xdel wf_notdef by simp
  qed
  have defexec2: "defined_atoms (action_numeric_update_function (the (res_inst \<pi>)) N)
     = defined_atoms N \<union> (\<lambda>p. Atom (pne_to_def_atom def_prefix p)) ` set (lhs_pnes_eff (effect (the (res_inst \<pi>))))"
    unfolding defined_atoms_def domexec by (simp add: image_Un defined_atoms_def)
  have fst_eq: "fst (pt.execute_plan_action \<pi> MT)
     = fst (execute_plan_action \<pi> M) \<union> defined_atoms (snd (execute_plan_action \<pi> M))"
    unfolding exec execT fst_conv snd_conv dels_eq adds_eq defexec2 set_append newadds_set
    using disjN by auto
  have deffree: "Atom (predAtm (Pred (def_prefix + m)) vs) \<notin> fst (execute_plan_action \<pi> M)" for m vs
    unfolding exec fst_conv
    using rel[unfolded def_state_rel_def] wf_notdef MLN by auto
  show ?thesis
    unfolding def_state_rel_def
    using snd_eq fst_eq deffree by blast
qed

subsection \<open>Plan validity coincides\<close>

lemma valid_from_iff:
  assumes "def_state_rel M MT"
  shows "pt.valid_classical_plan_from2 MT \<pi>s \<longleftrightarrow> valid_classical_plan_from2 M \<pi>s"
  using assms
proof (induction \<pi>s arbitrary: M MT)
  case (Nil M MT)
  have dec: "is_def_explicated_conj (goal P)"
    using def_explicated_conj_prob unfolding def_explicated_conj_prob_def by simp
  have "(valuation MT \<Turnstile>\<^sub>m goal PT) = (valuation M \<Turnstile>\<^sub>m goal P)"
    using val_def_translate_fmla[OF Nil.prems wf_P(5) dec] by (simp add: def_translate_prob_sel)
  thus ?case
    by (simp add: pt.valid_classical_plan_from2_Nil valid_classical_plan_from2_Nil)
next
  case (Cons \<pi> \<pi>s M MT)
  show ?case
  proof (cases "plan_action_enabled \<pi> M")
    case True
    have "def_state_rel (execute_plan_action \<pi> M) (pt.execute_plan_action \<pi> MT)"
      by (rule execute_preserves_rel[OF Cons.prems True])
    thus ?thesis
      using enabled_iff[OF Cons.prems, of \<pi>] True Cons.IH
      by (simp add: pt.valid_classical_plan_from2_Cons valid_classical_plan_from2_Cons)
  next
    case False
    thus ?thesis
      using enabled_iff[OF Cons.prems, of \<pi>]
      by (simp add: pt.valid_classical_plan_from2_Cons valid_classical_plan_from2_Cons)
  qed
qed

subsection \<open>Main theorem\<close>

lemma def_translate_valid_plan_iff:
  "pt.valid_classical_plan2 \<pi>s \<longleftrightarrow> valid_classical_plan2 \<pi>s"
  unfolding pt.valid_classical_plan2_def valid_classical_plan2_def
  using valid_from_iff[OF def_state_rel_I] .  

lemma def_translate_valid_iff:
  "(\<exists>\<pi>s. valid_classical_plan2 \<pi>s) = (\<exists>\<pi>s'. pt.valid_classical_plan2 \<pi>s')"
  using def_translate_valid_plan_iff by blast

end

end
