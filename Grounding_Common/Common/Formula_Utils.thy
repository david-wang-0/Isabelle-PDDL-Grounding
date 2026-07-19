theory Formula_Utils
  imports "Propositional_Proof_Systems.Sema"
    "Propositional_Proof_Systems.CNF_Formulas"
    "Analysis_Free_Base.Abstract_Syntax" (* just for the datatype atom *)
begin

subsection \<open> pure conjunctions \<close>
(* Modeled after Propositional_Proof_Systems.CNF_Formulas.is_disj.
  A conjunction is a right deep tree e.g: A \<and> (\<not>B \<and> C) *)
term is_disj
fun is_conj where
  "is_conj (F \<^bold>\<and> G) \<longleftrightarrow> is_lit_plus F \<and> is_conj G" |
  "is_conj H \<longleftrightarrow> is_lit_plus H"

(* assumes the argument to be in a right-deep tree, i.e. is_conj *)
(* possible optimization: un_and (Not Bot) = []" *)
(* still is defined and preserves semantics if argument isn't a pure right conjunction *)
fun un_and :: "'a formula \<Rightarrow> 'a formula list" where
  "un_and (F \<^bold>\<and> G) = F # un_and G" |
  "un_and F = [F]"

lemma conj_induct [consumes 1,
    case_names Bot Top Atom NotAtom BotAnd TopAnd AtomAnd NotAtomAnd]:
  assumes "is_conj \<phi>"
    "P \<bottom>" "P (\<^bold>\<not>\<bottom>)" "\<And>a. P(Atom a)" "\<And>a. P(\<^bold>\<not> (Atom a))"
    "\<And>G. P G \<Longrightarrow> P (\<bottom> \<^bold>\<and> G)" "\<And>G. P G \<Longrightarrow> P (\<^bold>\<not>\<bottom> \<^bold>\<and> G)"
    "\<And>G a. P G \<Longrightarrow> P(Atom a \<^bold>\<and> G)" "\<And>G a. P G \<Longrightarrow> P(\<^bold>\<not> (Atom a) \<^bold>\<and> G)"
  shows "P \<phi>"
using assms proof (induction \<phi>)
  case (Not l)
  then show ?case by (cases l) simp_all
next
  case (And F G)
  then show ?case by (cases F rule: is_lit_plus.cases) simp_all
qed simp_all

lemma un_and_lits: "is_conj F \<Longrightarrow> \<forall>f \<in> set (un_and F). is_lit_plus f"
  by (induction F) simp_all

lemma un_and_sem: "A \<Turnstile> F \<longleftrightarrow> (\<forall>f \<in> set (un_and F). A \<Turnstile> f)"
  by (induction F) simp_all

lemma map_preserves_isconj:
  assumes "is_conj F" shows "is_conj (map_formula m F)"
using assms by (induction F rule: conj_induct) simp_all

subsection \<open> Formula Semantics \<close>

lemma entail_and: "A \<TTurnstile> a \<^bold>\<and> b \<longleftrightarrow> A \<TTurnstile> a \<and> A \<TTurnstile> b"
  by (auto simp add: entailment_def)

(* Doesn't work with OR. But this isn't a problem since closed world entailment can
   be represented as semantics of the world's valuation, and then we can apply
   \<open>BigOr_semantics\<close> *)
lemma bigAnd_entailment: "\<Gamma> \<TTurnstile> (\<^bold>\<And>F) \<longleftrightarrow>
  (\<forall>f \<in> set F. \<Gamma> \<TTurnstile> f)"
  unfolding entailment_def
  by auto

text \<open> Single formula entailment, since entailment has a formula set on the left side... \<close>

definition fmla_entailment :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> bool" ("(_ \<TTurnstile>\<^sub>1/ _)" [53,53] 53) where
  "F \<TTurnstile>\<^sub>1 G \<equiv> \<forall>\<A>. \<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G"

lemma fmla_ent_ent: "F \<TTurnstile>\<^sub>1 G \<longleftrightarrow> (\<forall>\<Gamma>. \<Gamma> \<TTurnstile> F \<longrightarrow> \<Gamma> \<TTurnstile> G)"
  apply (rule)
  using fmla_entailment_def entailment_def apply metis
  using fmla_entailment_def entailment_def apply fastforce
  done

text \<open> Other formula properties \<close>

thm atoms_BigAnd
(* this one isn't in Formulas.thy *)
lemma atoms_BigOr[simp]: "atoms (\<^bold>\<Or> \<phi>s) = \<Union>(atoms ` set \<phi>s)"
  by (induction \<phi>s) simp_all

lemma bigAnd_map: "(\<^bold>\<And>(map (map_formula f) \<phi>s)) = map_formula f (\<^bold>\<And>\<phi>s)"
  by (induction \<phi>s; simp_all)
lemma bigOr_map: "(\<^bold>\<Or>(map (map_formula f) \<phi>s)) = map_formula f (\<^bold>\<Or>\<phi>s)"
  by (induction \<phi>s; simp_all)

lemma bigAnd_map_atom: "(\<^bold>\<And>(map ((map_formula \<circ> map_atom) f) \<phi>s)) =
  (map_formula \<circ> map_atom) f (\<^bold>\<And>\<phi>s)"
  using bigAnd_map by auto
lemma bigOr_map_atom: "(\<^bold>\<Or>(map ((map_formula \<circ> map_atom) f) \<phi>s)) =
  (map_formula \<circ> map_atom) f (\<^bold>\<Or>\<phi>s)"
  using bigOr_map by auto

lemma map_formula_bigOr: "(\<^bold>\<Or> (map (map_formula f) \<phi>s)) = map_formula f (\<^bold>\<Or> \<phi>s)"
  by (induction \<phi>s; simp_all)


subsection \<open> Conjunction Relaxation \<close>

fun is_pos_lit :: "'a atom formula \<Rightarrow> bool" where
  f: "is_pos_lit \<bottom> = True" |
  "is_pos_lit (\<^bold>\<not>\<bottom>) = True" |
  "is_pos_lit (Atom (predAtm n args)) = True" |
  "is_pos_lit (\<^bold>\<not>(Atom (predAtm n args))) = False" |
  "is_pos_lit (Atom (eqAtm a b)) = True" |
  "is_pos_lit (\<^bold>\<not>(Atom (eqAtm a b))) = True" |
  "is_pos_lit _ = False"

fun is_pos_conj :: "'a atom formula \<Rightarrow> bool" where
  "is_pos_conj (F \<^bold>\<and> G) \<longleftrightarrow> is_pos_lit F \<and> is_pos_conj G" |
  "is_pos_conj F \<longleftrightarrow> is_pos_lit F"

lemma conj_induct_atoms [consumes 1, case_names
    Bot Top Pred NotPred eqAtm NoteqAtm
    numericEq NotnumericEq numericLess NotnumericLess numericLE NotnumericLE
    numericGreater NotnumericGreater numericGE NotnumericGE
    BotAnd TopAnd PredAnd NotPredAnd eqAtmAnd NoteqAtmAnd
    numericEqAnd NotnumericEqAnd numericLessAnd NotnumericLessAnd
    numericLEAnd NotnumericLEAnd
    numericGreaterAnd NotnumericGreaterAnd numericGEAnd NotnumericGEAnd]:
  assumes "is_conj \<phi>"
    "P \<bottom>" "P (\<^bold>\<not> \<bottom>)"
    "\<And>n args. P(Atom (predAtm n args))" "\<And>n args. P(\<^bold>\<not>(Atom (predAtm n args)))"
    "\<And>a b. P (Atom (eqAtm a b))" "\<And>a b. P (\<^bold>\<not> (Atom (eqAtm a b)))"
    "\<And>a b. P (Atom (numericEqAtm a b))" "\<And>a b. P (\<^bold>\<not> (Atom (numericEqAtm a b)))"
    "\<And>a b. P (Atom (numericLessAtm a b))" "\<And>a b. P (\<^bold>\<not> (Atom (numericLessAtm a b)))"
    "\<And>a b. P (Atom (numericLEAtm a b))" "\<And>a b. P (\<^bold>\<not> (Atom (numericLEAtm a b)))"
    "\<And>a b. P (Atom (numericGreaterAtm a b))" "\<And>a b. P (\<^bold>\<not> (Atom (numericGreaterAtm a b)))"
    "\<And>a b. P (Atom (numericGEAtm a b))" "\<And>a b. P (\<^bold>\<not> (Atom (numericGEAtm a b)))"
    "\<And>G. P G \<Longrightarrow> P (\<bottom> \<^bold>\<and> G)" "\<And>G. P G \<Longrightarrow> P (\<^bold>\<not>\<bottom> \<^bold>\<and> G)"
    "\<And>G n args. P G \<Longrightarrow> P(Atom (predAtm n args) \<^bold>\<and> G)"
    "\<And>G n args. P G \<Longrightarrow> P(\<^bold>\<not>(Atom (predAtm n args)) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (Atom (eqAtm a b) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (\<^bold>\<not> (Atom (eqAtm a b)) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (Atom (numericEqAtm a b) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (\<^bold>\<not> (Atom (numericEqAtm a b)) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (Atom (numericLessAtm a b) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (\<^bold>\<not> (Atom (numericLessAtm a b)) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (Atom (numericLEAtm a b) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (\<^bold>\<not> (Atom (numericLEAtm a b)) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (Atom (numericGreaterAtm a b) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (\<^bold>\<not> (Atom (numericGreaterAtm a b)) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (Atom (numericGEAtm a b) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (\<^bold>\<not> (Atom (numericGEAtm a b)) \<^bold>\<and> G)"
  shows "P \<phi>"
using assms proof (induction \<phi>)
  case (Atom x)
  thus ?case by (cases x) simp_all
next
  case (Not l)
  thus ?case
  proof (cases l)
    case (Atom a) with Not show ?thesis by (cases a) simp_all
  qed (use Not in simp_all)
next
  case (And F G)
  thus ?case
  proof (cases F)
    case (Atom a) with And show ?thesis by (cases a) simp_all
  next
    case (Not k)
    show ?thesis
    proof (cases k)
      case (Atom a) with And \<open>F = \<^bold>\<not> k\<close> show ?thesis by (cases a) simp_all
    qed (use And \<open>F = \<^bold>\<not> k\<close> in simp_all)
  qed (use And in simp_all)
qed simp_all

lemma pos_conj_induct [consumes 1, case_names
    Bot Top PredAtom eqAtm NoteqAtm BotAnd TopAnd PredAtomAnd eqAtmAnd NoteqAtmAnd]:
  assumes "is_pos_conj \<phi>"
    "P \<bottom>" "P (\<^bold>\<not> \<bottom>)" "\<And>n args. P(Atom (predAtm n args))"
    "\<And>a b. P (Atom (eqAtm a b))" "\<And>a b. P (\<^bold>\<not> (Atom (eqAtm a b)))"
    
    "\<And>G. P G \<Longrightarrow> P (\<bottom> \<^bold>\<and> G)" "\<And>G. P G \<Longrightarrow> P (\<^bold>\<not>\<bottom> \<^bold>\<and> G)"
    "\<And>G n args. P G \<Longrightarrow> P(Atom (predAtm n args) \<^bold>\<and> G)"
    "\<And>G a b. P G \<Longrightarrow> P (Atom (eqAtm a b) \<^bold>\<and> G)" "\<And>G a b. P G \<Longrightarrow> P (\<^bold>\<not> (Atom (eqAtm a b)) \<^bold>\<and> G)"
  shows "P \<phi>"
using assms proof (induction \<phi>)
  case (Atom x)
  thus ?case by (cases x) simp_all
next
  case (Not l)
  thus ?case by (cases l rule: is_pos_lit.cases) simp_all
next
  case (And F G)
  thus ?case by (cases F rule: is_pos_lit.cases) simp_all
qed simp_all

lemma pos_conj_conj: "is_pos_conj F \<Longrightarrow> is_conj F"
  by (induction F rule: pos_conj_induct) simp_all

lemma is_pos_conj_alt: "is_pos_conj F \<longleftrightarrow> (\<forall>l \<in> set (un_and F). is_pos_lit l)"
  by (induction F) simp_all

lemma pos_lit_vs_plus: "is_lit_plus l \<longleftrightarrow> is_pos_lit l
    \<or> (\<exists>n args. l = \<^bold>\<not>(Atom(predAtm n args)))
    \<or> (\<exists>a b. l = Atom (numericEqAtm a b)) \<or> (\<exists>a b. l = \<^bold>\<not>(Atom (numericEqAtm a b)))
    \<or> (\<exists>a b. l = Atom (numericLessAtm a b)) \<or> (\<exists>a b. l = \<^bold>\<not>(Atom (numericLessAtm a b)))
    \<or> (\<exists>a b. l = Atom (numericLEAtm a b)) \<or> (\<exists>a b. l = \<^bold>\<not>(Atom (numericLEAtm a b)))
    \<or> (\<exists>a b. l = Atom (numericGreaterAtm a b)) \<or> (\<exists>a b. l = \<^bold>\<not>(Atom (numericGreaterAtm a b)))
    \<or> (\<exists>a b. l = Atom (numericGEAtm a b)) \<or> (\<exists>a b. l = \<^bold>\<not>(Atom (numericGEAtm a b)))"
proof (cases l)
  case (Atom a) thus ?thesis by (cases a) auto
next
  case (Not k)
  show ?thesis
  proof (cases k)
    case (Atom a) with \<open>l = \<^bold>\<not> k\<close> show ?thesis by (cases a) auto
  qed (use \<open>l = \<^bold>\<not> k\<close> in auto)
qed auto

text\<open> formula relaxation. Not in Formula_Utils because it uses PDDL atoms. \<close>

(* expects is_lit_plus *)
fun relax_lit :: "'a atom formula \<Rightarrow> 'a atom formula" where
  "relax_lit (\<^bold>\<not>(Atom (predAtm n args))) = \<^bold>\<not>\<bottom>" |
  "relax_lit (Atom (numericEqAtm a b)) = \<^bold>\<not>\<bottom>" |
  "relax_lit (\<^bold>\<not>(Atom (numericEqAtm a b))) = \<^bold>\<not>\<bottom>" |
  "relax_lit (Atom (numericLessAtm a b)) = \<^bold>\<not>\<bottom>" |
  "relax_lit (\<^bold>\<not>(Atom (numericLessAtm a b))) = \<^bold>\<not>\<bottom>" |
  "relax_lit (Atom (numericLEAtm a b)) = \<^bold>\<not>\<bottom>" |
  "relax_lit (\<^bold>\<not>(Atom (numericLEAtm a b))) = \<^bold>\<not>\<bottom>" |
  "relax_lit (Atom (numericGreaterAtm a b)) = \<^bold>\<not>\<bottom>" |
  "relax_lit (\<^bold>\<not>(Atom (numericGreaterAtm a b))) = \<^bold>\<not>\<bottom>" |
  "relax_lit (Atom (numericGEAtm a b)) = \<^bold>\<not>\<bottom>" |
  "relax_lit (\<^bold>\<not>(Atom (numericGEAtm a b))) = \<^bold>\<not>\<bottom>" |
  "relax_lit l = l"
(* expects is_conj *)
fun relax_conj :: "'a atom formula \<Rightarrow> 'a atom formula" where
  "relax_conj (F \<^bold>\<and> G) = relax_lit F \<^bold>\<and> relax_conj G" |
  "relax_conj f = relax_lit f"

lemma relax_conj_un_and: "un_and (relax_conj F) = map relax_lit (un_and F)"
proof (induction F)
  case (Atom x) thus ?case by (cases x) auto
next
  case (Not x) thus ?case
  proof (cases x)
    case (Atom a) thus ?thesis by (cases a) auto
  qed auto
qed auto

lemma relax_lit_pos: "is_lit_plus f \<Longrightarrow> is_pos_lit (relax_lit f)"
  by (cases f rule: is_pos_lit.cases) simp_all

lemma relax_conj_pos: "is_conj F \<Longrightarrow> is_pos_conj (relax_conj F)"
  by (induction F rule: conj_induct_atoms) simp_all

lemma relax_lit_sem: "A \<Turnstile> l \<Longrightarrow> A \<Turnstile> relax_lit l"
  by (cases l rule: relax_lit.cases) simp_all

lemma relax_conj_sem:
  shows "A \<Turnstile> F \<Longrightarrow> A \<Turnstile> relax_conj F"
  unfolding un_and_sem[of _ F] un_and_sem[of _ "relax_conj F"] relax_conj_un_and
  using relax_lit_sem by auto

(* todo use map_atom_formula *)
lemma relax_conj_map:
  assumes "is_conj F"
  shows "(map_formula \<circ> map_atom) m (relax_conj F) =
    relax_conj ((map_formula \<circ> map_atom) m F)"
  using assms by (induction F rule: conj_induct_atoms) simp_all

subsection \<open> STRIPS Formulas \<close>

text \<open>The lemma \<open>Propositional_Proof_Systems.Sema.pn_atoms_updates\<close> is in a very unfortunate form,
  so I have to split it.\<close>

lemma prod_unions_alt: "prod_unions (a, b) (c, d) = (a \<union> c, b \<union> d)"
  using prod_unions_def by auto

lemma snd_prod_unions: "snd (prod_unions A B) = snd A \<union> snd B"
  apply (induction A; induction B)
  by (simp_all add: prod_unions_alt)

lemma fst_prod_unions: "fst (prod_unions A B) = fst A \<union> fst B"
  apply (induction A; induction B)
  by (simp_all add: prod_unions_alt)

lemma pn_atoms_updates_split: "(p \<notin> snd (pn_atoms F) \<longrightarrow>
    ((M \<Turnstile> F \<longrightarrow> M(p := True) \<Turnstile> F)
    \<and> (\<not>(M \<Turnstile> F) \<longrightarrow> \<not>M(p := False) \<Turnstile> F))) \<and>
   (p \<notin> fst (pn_atoms F) \<longrightarrow>
    ((M \<Turnstile> F \<longrightarrow> M(p := False) \<Turnstile> F)
    \<and> (\<not>(M \<Turnstile> F) \<longrightarrow> \<not>M(p := True) \<Turnstile> F)))"
  (is "(?notn \<longrightarrow> (?A F\<and> ?B)) \<and> (?notp \<longrightarrow> (?C \<and> ?D))")
proof (induction F)
  case (And F1 F2)
    (* TODO: can I just use "intro conjI; intro: impI" here to automatically create assumptions and split the goal? *)
  { assume "p \<notin> snd (pn_atoms (F1 \<^bold>\<and> F2))"
    hence "p \<notin> snd (pn_atoms F1) \<and> p \<notin> snd (pn_atoms F2)"
      using snd_prod_unions pn_atoms.simps(4) by (metis UnCI)
    hence "(M \<Turnstile> F1 \<^bold>\<and> F2 \<longrightarrow> M(p := True) \<Turnstile> F1 \<^bold>\<and> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<and> F2 \<longrightarrow> \<not> M(p := False) \<Turnstile> F1 \<^bold>\<and> F2)"
      using And.IH formula_semantics.simps(4) by blast }
  moreover { assume "p \<notin> fst (pn_atoms (F1 \<^bold>\<and> F2))"
    hence "p \<notin> fst (pn_atoms F1) \<and> p \<notin> fst (pn_atoms F2)"
      using fst_prod_unions pn_atoms.simps(4) by (metis UnCI)
    hence "(M \<Turnstile> F1 \<^bold>\<and> F2 \<longrightarrow> M(p := False) \<Turnstile> F1 \<^bold>\<and> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<and> F2 \<longrightarrow> \<not> M(p := True) \<Turnstile> F1 \<^bold>\<and> F2)"
      using And.IH formula_semantics.simps(4) by blast }
  ultimately show ?case by blast
next
  case (Or F1 F2)
  { assume "p \<notin> snd (pn_atoms (F1 \<^bold>\<or> F2))"
    hence "p \<notin> snd (pn_atoms F1) \<and> p \<notin> snd (pn_atoms F2)"
      using snd_prod_unions pn_atoms.simps(5) by (metis UnCI)
    hence "(M \<Turnstile> F1 \<^bold>\<or> F2 \<longrightarrow> M(p := True) \<Turnstile> F1 \<^bold>\<or> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<or> F2 \<longrightarrow> \<not> M(p := False) \<Turnstile> F1 \<^bold>\<or> F2)"
      using Or.IH formula_semantics.simps(5) by blast }
  moreover { assume "p \<notin> fst (pn_atoms (F1 \<^bold>\<or> F2))"
    hence "p \<notin> fst (pn_atoms F1) \<and> p \<notin> fst (pn_atoms F2)"
      using fst_prod_unions pn_atoms.simps(5) by (metis UnCI)
    hence "(M \<Turnstile> F1 \<^bold>\<or> F2 \<longrightarrow> M(p := False) \<Turnstile> F1 \<^bold>\<or> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<or> F2 \<longrightarrow> \<not> M(p := True) \<Turnstile> F1 \<^bold>\<or> F2)"
      using Or.IH formula_semantics.simps(5) by blast }
  ultimately show ?case by blast
next
  case (Imp F1 F2)
  note Imp.IH
  { assume "p \<notin> snd (pn_atoms (F1 \<^bold>\<rightarrow> F2))"
    hence "p \<notin> fst (pn_atoms F1) \<and> p \<notin> snd (pn_atoms F2)"
      using snd_prod_unions pn_atoms.simps(6) UnCI by (metis snd_swap)
    hence "(M \<Turnstile> F1 \<^bold>\<rightarrow> F2 \<longrightarrow> M(p := True) \<Turnstile> F1 \<^bold>\<rightarrow> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<rightarrow> F2 \<longrightarrow> \<not> M(p := False) \<Turnstile> F1 \<^bold>\<rightarrow> F2)"
      using Imp.IH formula_semantics.simps(6) by blast }
  moreover { assume "p \<notin> fst (pn_atoms (F1 \<^bold>\<rightarrow> F2))"
    hence "p \<notin> snd (pn_atoms F1) \<and> p \<notin> fst (pn_atoms F2)"
      using fst_prod_unions pn_atoms.simps(6) UnCI by (metis fst_swap)
    hence "(M \<Turnstile> F1 \<^bold>\<rightarrow> F2 \<longrightarrow> M(p := False) \<Turnstile> F1 \<^bold>\<rightarrow> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<rightarrow> F2 \<longrightarrow> \<not> M(p := True) \<Turnstile> F1 \<^bold>\<rightarrow> F2)"
      using Imp.IH formula_semantics.simps(6) by blast }
  ultimately show ?case by blast
qed simp_all

(* this now follows *)
thm pn_atoms_updates
lemma "p \<notin> snd (pn_atoms F) \<Longrightarrow> n \<notin> fst (pn_atoms F) \<Longrightarrow>
  ((M \<Turnstile> F \<longrightarrow> (M(p := True) \<Turnstile> F \<and> M(n := False) \<Turnstile> F)))
\<and> ((\<not>(M \<Turnstile> F)) \<longrightarrow> \<not>(M(n := True) \<Turnstile> F) \<and> \<not>(M(p := False) \<Turnstile> F))"
  using pn_atoms_updates_split by metis

lemma p_atoms_updates:
  assumes "p \<notin> snd (pn_atoms F)"
  shows "M \<Turnstile> F \<longrightarrow> M(p := True) \<Turnstile> F"
        "\<not>(M \<Turnstile> F) \<longrightarrow> \<not>M(p := False) \<Turnstile> F"
  apply (metis assms pn_atoms_updates_split)
  by (metis assms pn_atoms_updates_split)

lemma n_atoms_updates:
  assumes "p \<notin> fst (pn_atoms F)"
  shows "M \<Turnstile> F \<longrightarrow> M(p := False) \<Turnstile> F"
        "\<not>(M \<Turnstile> F) \<longrightarrow> \<not>M(p := True) \<Turnstile> F"
  apply (metis assms pn_atoms_updates_split)
  by (metis assms pn_atoms_updates_split)


end