theory Classical_Variable_Freeness
  imports "Classical_Planning.Classical_Abstract_Syntax"
    Classical_Grounding_Utils.Classical_PDDL_Sema_Supplement
    Grounding_Classical_Common.Classical_PDDL_Normalization
    Grounding_Utils.Grounding_Utils
    Grounding_Utils.String_Utils
begin

subsection \<open>Introduction / elimination rules for the conjunctive target predicates\<close>

text \<open>Rather than repeatedly \<open>unfolding\<close> the definitions and splitting with \<open>intro conjI\<close>, we
  give each conjunctive predicate a proper introduction rule (declared \<open>[intro]\<close>) and the
  matching destruction rules (declared \<open>[dest]\<close>).\<close>

context ast_classical_domain begin

lemma grounded_domI [intro]:
  assumes "types D = []" "\<forall>p \<in> set (predicates D). grounded_pred p"
    "consts D = []" "\<forall>f \<in> set (functions D). grounded_func f"
    "\<forall>a \<in> set (actions D). grounded_ac a"
  shows grounded_dom
  unfolding grounded_dom_def using assms by blast

lemma grounded_domD [dest]:
  assumes grounded_dom
  shows "types D = []" "\<forall>p \<in> set (predicates D). grounded_pred p"
    "consts D = []" "\<forall>f \<in> set (functions D). grounded_func f"
    "\<forall>a \<in> set (actions D). grounded_ac a"
  using assms unfolding grounded_dom_def by blast+

text \<open>A grounded domain is \<^emph>\<open>a fortiori\<close> typeless: groundedness empties the type declarations and
  the constants, and makes every predicate/function argument list and every parameter list nil ---
  so each \<open>T = \<omega>\<close> obligation of typelessness is vacuous. Proving it once here spares every
  grounding stage a typelessness proof of its own. (Its natural home is beside
  \<open>typeless_classical_domain\<close> in \<^verbatim>\<open>Classical_PDDL_Normalization\<close>; it sits here, with the other
  derived \<open>grounded_*\<close> rules, to leave that base session untouched.)\<close>
lemma typeless_classical_domain_of_grounded:
  assumes g: grounded_dom
  shows typeless_classical_domain
proof -
  have p: "\<forall>T \<in> set (predicate_decl.argTs p). T = \<omega>" if "p \<in> set (predicates D)" for p
    using grounded_domD(2)[OF g] that by (cases p) auto
  have f: "\<forall>T \<in> set (function_decl.argTs f). T = \<omega>" if "f \<in> set (functions D)" for f
    using grounded_domD(4)[OF g] that by (cases f) auto
  have a: "\<forall>(n, T) \<in> set (ac_params ac). T = \<omega>" if "ac \<in> set (actions D)" for ac
    using grounded_domD(5)[OF g] that by (cases ac rule: grounded_ac.cases) auto
  show ?thesis
    unfolding typeless_classical_domain_def domain_signature.typeless_domain_signature_def
    using grounded_domD(1)[OF g] grounded_domD(3)[OF g] p f a by auto
qed

text \<open>Resolving an action name yields a schema of the domain --- the one fact about
  \<^const>\<open>ast_classical_domain.resolve_classical_action_schema\<close> the grounding stages keep needing.\<close>
lemma resolve_mem:
  assumes "resolve_classical_action_schema n = Some a"
  shows "a \<in> set (actions D)"
  using assms unfolding resolve_classical_action_schema_def by (meson index_by_eq_SomeD)

lemma wf_classical_domainI [intro]:
  assumes wf_domain_signature "distinct (map ac_name (actions D))"
    "\<forall>a \<in> set (actions D). wf_classical_action_schema a"
  shows wf_classical_domain
  unfolding wf_classical_domain_def using assms by blast

lemma wf_classical_domainD [dest]:
  assumes wf_classical_domain
  shows wf_domain_signature "distinct (map ac_name (actions D))"
    "\<forall>a \<in> set (actions D). wf_classical_action_schema a"
  using assms unfolding wf_classical_domain_def by blast+

end

lemma (in domain_signature) wf_classical_action_schemaI [intro]:
  assumes "distinct (map fst (ac_params ac))"
    "wf_fmla (ac_tyt ac) (ac_pre ac)" "wf_effect (ac_tyt ac) (ac_eff ac)"
  shows "wf_classical_action_schema ac"
  unfolding wf_classical_action_schema_alt using assms by blast

context ast_classical_problem begin

lemma grounded_probI [intro]:
  assumes grounded_dom "objects P = []"
  shows grounded_prob
  unfolding grounded_prob_def using assms by blast

lemma grounded_probD [dest]:
  assumes grounded_prob shows grounded_dom "objects P = []"
  using assms unfolding grounded_prob_def by blast+

text \<open>The problem-level twin: a grounded problem is typeless, its object list being empty.\<close>
lemma typeless_classical_problem_of_grounded:
  assumes g: grounded_prob
  shows typeless_classical_problem
  unfolding typeless_classical_problem_def
  using ast_classical_domain.typeless_classical_domain_of_grounded[OF grounded_probD(1)[OF g]]
        grounded_probD(2)[OF g]
  by simp

lemma wf_classical_problemI [intro]:
  assumes wf_classical_domain wf_problem_signature "distinct (init P)"
    "\<forall>f \<in> set (init P). wf_fmla_atom objT f \<or> wf_func_assign f"
    "wf_fmla objT (goal P)"
  shows wf_classical_problem
  unfolding wf_classical_problem_def using assms by blast

lemma wf_classical_problemD [dest]:
  assumes wf_classical_problem
  shows wf_classical_domain wf_problem_signature "distinct (init P)"
    "\<forall>f \<in> set (init P). wf_fmla_atom objT f \<or> wf_func_assign f"
    "wf_fmla objT (goal P)"
  using assms unfolding wf_classical_problem_def by blast+

end

text \<open>A readable string encoder for ground plan actions: the action name, followed by each
  argument object's name, all joined by underscores. Used to name ground actions readably.\<close>

fun obj_str :: "object \<Rightarrow> String.literal" where
  "obj_str (Obj nm) = nm"

definition readable_pa :: "ast_classical_plan_action \<Rightarrow> String.literal" where
  "readable_pa \<pi> = (case \<pi> of SimplePlanAction n args \<Rightarrow>
     foldl (\<lambda>s ob. s + STR ''_'' + obj_str ob) n args)"

text \<open>The variable-freeness name machinery: fresh, distinct, readable nullary action names for
  the reachable ops (\<open>op_names\<close>), and the op\<open>\<leftrightarrow>\<close>name maps used to ground and restore plans.
  Parameterised by the reachable-op list \<open>ops\<close> alone --- no facts. Each name decorates the
  readable encoding with its position index via \<open>idx_name\<close>; since \<open>_\<close> never occurs inside a
  decimal numeral, equal encodings force equal indices (\<open>idx_name_inj_idx\<close>), which is what
  makes the generated names distinct.\<close>

locale varfree = ast_classical_problem +
  fixes ops :: "ast_classical_plan_action list"
begin

definition "op_names \<equiv>
  map2 (\<lambda>\<pi> i. idx_name (readable_pa \<pi>) i) ops [0..<length ops]"

lemma ops_len: "length ops = length op_names"
  unfolding op_names_def by simp

lemma op_names_dis: "distinct op_names"
proof -
  have opn_nth: "op_names ! k = idx_name (readable_pa (ops ! k)) k"
    if "k < length ops" for k
    using that unfolding op_names_def by simp
  have "op_names ! i \<noteq> op_names ! j"
    if ij: "i < length op_names" "j < length op_names" "i \<noteq> j" for i j
  proof
    assume eq: "op_names ! i = op_names ! j"
    have li: "i < length ops" and lj: "j < length ops" using ij ops_len by simp_all
    have "idx_name (readable_pa (ops ! i)) i = idx_name (readable_pa (ops ! j)) j"
      using eq opn_nth[OF li] opn_nth[OF lj] by simp
    hence "i = j" using idx_name_inj_idx by blast
    thus False using ij(3) by simp
  qed
  thus "distinct op_names" by (simp add: distinct_conv_nth)
qed

definition "op_map \<equiv> map_of (zip op_names ops)"

definition "op_map_inv \<equiv> map_of (zip ops op_names)"
definition "ground_pa \<pi> \<equiv> SimplePlanAction (the (op_map_inv \<pi>)) []"

fun restore_ground_pa :: "ast_classical_plan_action \<Rightarrow> ast_classical_plan_action" where
  "restore_ground_pa (SimplePlanAction n args) = the (op_map n)"

abbreviation restore_ground_plan :: "ast_classical_plan_action list \<Rightarrow> ast_classical_plan_action list" where
  "restore_ground_plan \<pi>s \<equiv> map restore_ground_pa \<pi>s"

end

context ast_classical_problem begin

text \<open>Grounding stage one --- instantiation. It keeps the ground actions' numeric effects, numeric
  preconditions, and the domain's function declarations: only the action \<^emph>\<open>parameters\<close> are
  instantiated (via \<^const>\<open>res_inst\<close>), nothing is propositionalised. That second step is stage two,
  the fact/fluent fold \<open>fact_folder.fold_prob\<close>. Grounds the un-relaxed \<open>P\<close> over the
  (over-approximated) reachable ops \<open>ops\<close>.\<close>

definition varfree_inst_ac :: "ast_classical_plan_action \<Rightarrow> name \<Rightarrow> ast_classical_action_schema" where
  "varfree_inst_ac \<pi> n =
     SimpleActionSchema (ActionHead n [])
       (SimpleActionBody
          (map_atom_fmla term.CONST (precondition (the (res_inst \<pi>))))
          (map_ast_effect term.CONST (effect (the (res_inst \<pi>)))))"

lemma varfree_inst_ac_sel [simp]:
  "ac_name (varfree_inst_ac \<pi> n) = n"
  "ac_params (varfree_inst_ac \<pi> n) = []"
  "ac_pre (varfree_inst_ac \<pi> n) = map_atom_fmla term.CONST (precondition (the (res_inst \<pi>)))"
  "ac_eff (varfree_inst_ac \<pi> n) = map_ast_effect term.CONST (effect (the (res_inst \<pi>)))"
  unfolding varfree_inst_ac_def by simp_all

lemma ac_tsubst_Nil_CONST [simp]: "ac_tsubst [] [] (term.CONST c) = c"
  by simp

text \<open>\<^bold>\<open>The key correspondence.\<close> Instantiating the nullary numeric-grounded action at \<open>[]\<close> undoes the
  \<open>term.CONST\<close> lift and recovers exactly the original instantiated ground action \<^term>\<open>the (res_inst \<pi>)\<close>
  --- numerics and all. (Contrast the propositional grounder, whose \<open>ground_fmla\<close> re-indexes atoms.)\<close>
lemma varfree_inst_ac_inst:
  "instantiate_classical_action_schema (varfree_inst_ac \<pi> n) [] = the (res_inst \<pi>)"
proof -
  have hf: "subst_term f \<circ> term.CONST = id" for f :: "variable \<Rightarrow> object" by (rule ext) simp
  have "instantiate_classical_action_schema (varfree_inst_ac \<pi> n) [] =
    GroundAction (map_atom_fmla (ac_tsubst [] [] \<circ> term.CONST) (precondition (the (res_inst \<pi>))))
                 (map_ast_effect (ac_tsubst [] [] \<circ> term.CONST) (effect (the (res_inst \<pi>))))"
    by (simp add: instantiate_classical_action_schema_alt atom.map_comp formula.map_comp
                  ast_effect.map_comp comp_def)
  also have "\<dots> = GroundAction (precondition (the (res_inst \<pi>))) (effect (the (res_inst \<pi>)))"
    by (simp add: hf atom.map_id0 formula.map_id0 ast_effect.map_id0)
  also have "\<dots> = the (res_inst \<pi>)" by (cases "the (res_inst \<pi>)") simp
  finally show ?thesis .
qed

end


context varfree begin

text \<open>The instantiated domain / problem. Its actions carry the nullary \<^emph>\<open>names\<close> \<open>op_names\<close> (one
  per reachable op) that stage two's \<open>fact_folder.fold_dom\<close> / \<open>fact_folder.fold_prob\<close> then keep
  verbatim, but the domain still holds the original types / predicates / functions and each action
  retains its numeric ground body.\<close>

text \<open>The grounded actions are nullary schemas whose bodies reference the instantiation's
  \<^emph>\<open>objects\<close> (via \<^const>\<open>term.CONST\<close>). A schema's body is typed by \<^const>\<open>ac_tyt\<close> \<open>= ty_term
  (params) constT\<close> --- i.e. by \<^emph>\<open>constants\<close> only --- so for the grounded schemas to be
  well-formed we \<^bold>\<open>promote the objects to constants\<close> (\<open>consts = consts (domain P) @ objects P\<close>,
  \<open>objects = []\<close>). This mirrors the propositional grounder's \<open>objects P\<^sub>G = []\<close> and is
  \<^emph>\<open>semantics-preserving\<close>: \<^term>\<open>objT\<close> is definitionally unchanged, since
  \<open>map_of (consts @ objects) = map_of objects ++ constT = objT\<close>.\<close>

definition varfree_inst_dom :: ast_classical_domain where
  "varfree_inst_dom =
     Domain (types (domain P)) (predicates (domain P)) (functions (domain P))
            (consts (domain P) @ objects P)
            (map2 varfree_inst_ac ops op_names)"

definition varfree_inst_prob :: ast_classical_problem where
  "varfree_inst_prob = Problem varfree_inst_dom [] (init P) (goal P)"

lemma varfree_inst_dom_sel [simp]:
  "types varfree_inst_dom = types (domain P)"
  "predicates varfree_inst_dom = predicates (domain P)"
  "functions varfree_inst_dom = functions (domain P)"
  "consts varfree_inst_dom = consts (domain P) @ objects P"
  "actions varfree_inst_dom = map2 varfree_inst_ac ops op_names"
  unfolding varfree_inst_dom_def by simp_all

lemma varfree_inst_prob_sel [simp]:
  "domain varfree_inst_prob = varfree_inst_dom"
  "objects varfree_inst_prob = []"
  "init varfree_inst_prob = init P"
  "goal varfree_inst_prob = goal P"
  unfolding varfree_inst_prob_def by simp_all

lemma varfree_inst_dom_names:
  "map ast_classical_action_schema_name (actions varfree_inst_dom) = op_names"
proof -
  have "map ast_classical_action_schema_name (map2 varfree_inst_ac xs ys) = ys"
    if "length xs = length ys" for xs ys
    using that by (induction xs ys rule: list_induct2) (simp_all add: varfree_inst_ac_def)
  thus ?thesis using ops_len by simp
qed

lemma varfree_inst_dom_names_dis:
  "distinct (map ast_classical_action_schema_name (actions varfree_inst_dom))"
  using varfree_inst_dom_names op_names_dis by simp

end

text \<open>The \<^emph>\<open>minimal\<close> reachability/well-formedness assumptions the numeric-fluent-retaining grounder
  needs: the input problem is well-formed, the reachable-op list \<open>ops\<close> is distinct, over-approximates
  the applicable actions, and every op is a well-formed plan action. The numeric-fluent-retaining
  grounder (this theory) is based on this weaker locale: it grounds the
  un-relaxed problem \<open>P\<^sub>T\<close> keeping its numeric preconditions/effects and function assignments verbatim
  (via a \<open>term.CONST\<close> lift, undone by instantiate-at-\<open>[]\<close>), so it never propositionalises an atom and
  hence needs \<^emph>\<open>none\<close> of the coverage / \<open>facts\<close> assumptions --- those (and \<open>covered\<close>, which rejects
  numeric atoms outright) are what the \<^emph>\<open>propositional\<close> grounder needs, and they move to
  \<open>wf_grounder\<close> below.\<close>
locale varfree_instantiator = varfree +
  assumes
    wf_problem: "wf_classical_problem" and
    ops_dist: "distinct ops" and
    all_ops: "set ops \<supseteq> {\<pi>. applicable \<pi>}" and
    (* If "set ops = {\<pi>. applicable \<pi>}", this follows: *)
    ops_wf: "\<forall>\<pi> \<in> set ops. wf_classical_plan_action \<pi>"

sublocale varfree_instantiator \<subseteq> wf_ast_classical_problem P
  apply (unfold_locales)
  using wf_problem unfolding wf_classical_problem_def by simp

sublocale varfree_instantiator \<subseteq> png: ast_classical_problem varfree_inst_prob .

context varfree_instantiator begin

text \<open>Shared restore/reachability machinery, provable already in \<^locale>\<open>varfree_instantiator\<close> (it needs
  only \<open>all_ops\<close> / \<open>ops_dist\<close> + the \<open>grounder\<close> name machinery \<open>op_map\<close>/\<open>op_map_inv\<close>, not the
  numeric-freeness assumptions).\<close>

subsubsection \<open>Normalization covariance of the instantiation\<close>

text \<open>The instantiation stage preserves the three normalization invariants. It is \<^emph>\<open>not\<close> the
  folding stage: atoms keep their object arguments here, so typelessness cannot be inherited from
  groundedness (as it is for the folded product) and has to be traced through the copied
  declarations --- the domain's types/predicates/functions are kept verbatim, the objects are moved
  into the constants, and every instantiated schema is parameterless.\<close>

lemma varfree_inst_typeless:
  assumes t: typeless_classical_problem
  shows png.typeless_classical_problem
proof -
  have d: typeless_classical_domain and o: "\<forall>(n, T) \<in> set (objects P). T = \<omega>"
    using t unfolding typeless_classical_problem_def by blast+
  have sig: "types (domain P) = []"
       and pr: "\<forall>p \<in> set (predicates (domain P)). \<forall>T \<in> set (predicate_decl.argTs p). T = \<omega>"
       and fn: "\<forall>f \<in> set (functions (domain P)). \<forall>T \<in> set (function_decl.argTs f). T = \<omega>"
       and cs: "\<forall>(n, T) \<in> set (consts (domain P)). T = \<omega>"
    using d unfolding typeless_classical_domain_def domain_signature.typeless_domain_signature_def
    by blast+
  have ap: "\<forall>(n, T) \<in> set (ac_params ac). T = \<omega>" if "ac \<in> set (actions varfree_inst_dom)" for ac
    using that by (auto simp: varfree_inst_dom_sel(5) map2_map_map)
  show ?thesis
    unfolding ast_classical_problem.typeless_classical_problem_def
              ast_classical_domain.typeless_classical_domain_def
              domain_signature.typeless_domain_signature_def
    using sig pr fn cs o ap by (auto simp: varfree_inst_dom_sel)
qed

lemma varfree_inst_prec_normed:
  assumes pn: prec_normed_dom
  shows png.prec_normed_dom
  unfolding ast_classical_domain.prec_normed_dom_def
proof
  fix ac assume "ac \<in> set (actions (ast_problem.domain varfree_inst_prob))"
  then obtain \<pi> n where ac: "ac = varfree_inst_ac \<pi> n"
    and pin: "(\<pi>, n) \<in> set (zip ops op_names)"
    by (auto simp: map2_map_map)
  have piops: "\<pi> \<in> set ops" using pin set_zip_leftD by fastforce
  obtain nm args where pi: "\<pi> = SimplePlanAction nm args" by (cases \<pi>)
  have "wf_classical_plan_action \<pi>" using piops ops_wf by blast
  then obtain a where a: "resolve_classical_action_schema nm = Some a"
    using pi wf_classical_plan_action_simple by (auto split: option.splits)
  hence "a \<in> set (actions D)" by (rule resolve_mem)
  hence conj: "is_conj (ac_pre a)" using pn unfolding prec_normed_dom_def by blast
  have inst: "precondition (the (res_inst \<pi>))
      = map_atom_fmla (ac_tsubst (ac_params a) args) (ac_pre a)"
    using a unfolding pi by (simp add: instantiate_classical_action_schema_alt)
  show "is_conj (ac_pre ac)"
    unfolding ac varfree_inst_ac_sel(3) inst
    by (simp add: map_preserves_isconj comp_def conj)
qed

text \<open>The instantiation keeps the goal verbatim, so the three conjuncts compose.\<close>
lemma varfree_inst_normed:
  assumes n: normalized_prob
  shows png.normalized_prob
  unfolding ast_classical_problem.normalized_prob_def
  using varfree_inst_typeless varfree_inst_prec_normed n[unfolded normalized_prob_def]
  by (simp add: varfree_inst_prob_sel)

lemma plan_in_ops:
  assumes "valid_classical_plan_alt I \<pi>s M'"
  shows "set \<pi>s \<subseteq> set ops"
proof
  fix \<pi> assume "\<pi> \<in> set \<pi>s"
  with assms have "applicable \<pi>" unfolding applicable_def by blast
  thus "\<pi> \<in> set ops" using all_ops by blast
qed

lemma restore_map_entry:
  assumes "n \<in> set op_names"
  obtains \<pi> where "op_map n = Some \<pi>" "\<pi> \<in> set ops" "op_map_inv \<pi> = Some n"
proof -
  from assms obtain i where i: "i < length op_names" "op_names ! i = n"
    using in_set_conv_nth by meson
  let ?\<pi> = "ops ! i"
  have iops: "i < length ops" using i ops_len by simp
  have zo: "(n, ?\<pi>) \<in> set (zip op_names ops)"
    using i iops ops_len by (force simp: set_zip)
  have zi: "(?\<pi>, n) \<in> set (zip ops op_names)"
    using i iops ops_len by (force simp: set_zip)
  have "op_map n = Some ?\<pi>"
    unfolding op_map_def using zo op_names_dis ops_len by (simp add: map_of_is_SomeI map_fst_zip)
  moreover have "op_map_inv ?\<pi> = Some n"
    unfolding op_map_inv_def using zi ops_dist ops_len by (simp add: map_of_is_SomeI map_fst_zip)
  moreover have "?\<pi> \<in> set ops" using iops nth_mem by blast
  ultimately show thesis using that by blast
qed

subsection \<open>Well-formedness of the numeric grounded problem\<close>

text \<open>\<^bold>\<open>Signature bridge.\<close> The numeric grounded domain keeps \<open>P\<close>'s types / predicates /
  functions and merely \<^emph>\<open>promotes objects to constants\<close> (\<open>consts = consts (domain P) @ objects P\<close>,
  \<open>objects = []\<close>). Hence \<^const>\<open>png.constT\<close> and \<^const>\<open>png.objT\<close> both collapse to \<^const>\<open>objT\<close>,
  and the type / predicate / function signatures coincide with \<open>P\<close>'s.\<close>

lemma varfree_png_constT: "png.constT = objT"
proof -
  have "png.constT = map_of (consts (domain P) @ objects P)"
    unfolding png.constT_def by simp
  also have "\<dots> = map_of (objects P) ++ map_of (consts (domain P))"
    by (simp add: map_of_append)
  also have "\<dots> = objT" unfolding objT_def constT_def by simp
  finally show ?thesis .
qed

lemma varfree_png_objT: "png.objT = objT"
  unfolding png.objT_def varfree_png_constT by simp

lemma varfree_png_sig: "png.sig = sig"
  unfolding png.sig_def sig_def by simp

lemma varfree_png_func_sig: "png.func_sig = func_sig"
  unfolding png.func_sig_def func_sig_def by simp

text \<open>\<open>png\<close> shares \<open>P\<close>'s types / predicates / functions, so its typing / well-formedness
  primitives coincide with \<open>P\<close>'s (as functions of the entity-typing \<open>tyt\<close>).\<close>

lemma varfree_png_of_type: "png.of_type = of_type"
  unfolding png.of_type_def of_type_def png.subtype_rel_def subtype_rel_def by simp

lemma varfree_png_is_of_type: "png.is_of_type = is_of_type"
  unfolding png.is_of_type_def is_of_type_def varfree_png_of_type by simp

lemma varfree_png_wf_pne: "png.wf_primitive_numeric_expression = wf_primitive_numeric_expression"
proof (intro ext)
  fix tyt p
  show "png.wf_primitive_numeric_expression tyt p = wf_primitive_numeric_expression tyt p"
    by (cases p) (simp add: varfree_png_func_sig varfree_png_is_of_type)
qed

lemma varfree_png_wf_ne: "png.wf_numeric_expression = wf_numeric_expression"
proof (intro ext)
  fix tyt n
  show "png.wf_numeric_expression tyt n = wf_numeric_expression tyt n"
    by (induction n) (simp_all add: varfree_png_wf_pne)
qed

lemma varfree_png_wf_atom: "png.wf_atom = wf_atom"
proof (intro ext)
  fix tyt a
  show "png.wf_atom tyt a = wf_atom tyt a"
    by (cases a) (simp_all add: varfree_png_sig varfree_png_is_of_type varfree_png_wf_ne)
qed

lemma varfree_png_wf_fmla: "png.wf_fmla = wf_fmla"
proof (intro ext)
  fix tyt \<phi>
  show "png.wf_fmla tyt \<phi> = wf_fmla tyt \<phi>"
    by (induction \<phi>) (simp_all add: varfree_png_wf_atom)
qed

lemma varfree_png_wf_fmla_atom: "png.wf_fmla_atom = wf_fmla_atom"
proof (intro ext)
  fix tyt \<phi>
  show "png.wf_fmla_atom tyt \<phi> = wf_fmla_atom tyt \<phi>"
    by (cases \<phi> rule: wf_fmla_atom.cases) (simp_all add: varfree_png_sig varfree_png_is_of_type)
qed

lemma varfree_png_wf_num_eff: "png.wf_numeric_effect = wf_numeric_effect"
proof (intro ext)
  fix tyt ne
  show "png.wf_numeric_effect tyt ne = wf_numeric_effect tyt ne"
    by (cases ne) (simp add: varfree_png_wf_pne varfree_png_wf_ne)
qed

lemma varfree_png_wf_effect: "png.wf_effect = wf_effect"
proof (intro ext)
  fix tyt \<epsilon>
  show "png.wf_effect tyt \<epsilon> = wf_effect tyt \<epsilon>"
    by (cases \<epsilon>) (simp add: varfree_png_wf_fmla_atom varfree_png_wf_num_eff)
qed

text \<open>\<^bold>\<open>The CONST lift is typing-neutral.\<close> An OBJECT atom well-formed under \<^const>\<open>objT\<close> maps
  (via \<^const>\<open>term.CONST\<close>) to a TERM atom well-formed under \<open>ty_term Map.empty objT\<close>: the empty
  variable table is never consulted (there are no \<open>VAR\<close>s), and \<open>ty_term Map.empty objT (CONST c)
  = objT c\<close>. These mirror \<open>wf_atom_to_term\<close> / \<open>wf_fmla_to_term\<close> of \<open>Classical_Goal_Normalization\<close>,
  re-derived here for \<open>P\<close>'s signature.\<close>

lemma is_of_type_CONST: "is_of_type (ty_term vart objT) (term.CONST x) t = is_of_type objT x t"
  unfolding is_of_type_def by simp

lemma wf_pne_CONST:
  assumes "wf_primitive_numeric_expression objT p"
  shows "wf_primitive_numeric_expression (ty_term vart objT) (map_primitive_numeric_expression term.CONST p)"
proof (cases p)
  case [simp]: (PNE f xs)
  from assms obtain Ts where [simp]: "func_sig f = Some Ts" by fastforce
  with assms have "list_all2 (is_of_type objT) xs Ts" by simp
  hence "list_all2 (is_of_type (ty_term vart objT)) (map term.CONST xs) Ts"
    by (induction xs Ts rule: list_all2_induct) (simp_all add: is_of_type_CONST)
  thus ?thesis by simp
qed

lemma wf_ne_CONST:
  assumes "wf_numeric_expression objT n"
  shows "wf_numeric_expression (ty_term vart objT) (map_numeric_expression term.CONST n)"
  using assms by (induction n) (auto simp: wf_pne_CONST)

lemma wf_atom_CONST:
  assumes "wf_atom objT a"
  shows "wf_atom (ty_term vart objT) (map_atom term.CONST a)"
  using assms
proof (induction a)
  case (predAtm p xs)
  then obtain Ts where [simp]: "sig p = Some Ts" by fastforce
  hence "list_all2 (is_of_type objT) xs Ts" using predAtm by simp
  hence "list_all2 (is_of_type (ty_term vart objT)) (map term.CONST xs) Ts"
    by (induction xs Ts rule: list_all2_induct) (simp_all add: is_of_type_CONST)
  thus ?case by simp
qed (auto simp: wf_ne_CONST)

lemma wf_fmla_CONST:
  assumes "wf_fmla objT \<phi>"
  shows "wf_fmla (ty_term vart objT) (map_atom_fmla term.CONST \<phi>)"
  using assms by (induction \<phi>) (simp_all add: wf_atom_CONST)

lemma wf_fmla_atom_CONST:
  assumes "wf_fmla_atom objT \<phi>"
  shows "wf_fmla_atom (ty_term vart objT) (map_atom_fmla term.CONST \<phi>)"
proof -
  from assms obtain p xs where \<phi>: "\<phi> = Atom (predAtm p xs)"
    by (cases \<phi> rule: wf_fmla_atom.cases) auto
  have "wf_fmla objT \<phi>" using assms wf_fmla_atom_alt by blast
  hence "wf_fmla (ty_term vart objT) (map_atom_fmla term.CONST \<phi>)" by (rule wf_fmla_CONST)
  thus ?thesis unfolding \<phi> by (simp add: wf_fmla_atom_alt)
qed

lemma wf_num_eff_CONST:
  assumes "wf_numeric_effect objT ne"
  shows "wf_numeric_effect (ty_term vart objT) (map_numeric_effect term.CONST ne)"
  using assms by (cases ne) (auto simp: wf_pne_CONST wf_ne_CONST)

lemma wf_effect_CONST:
  assumes "wf_effect objT \<epsilon>"
  shows "wf_effect (ty_term vart objT) (map_ast_effect term.CONST \<epsilon>)"
proof (cases \<epsilon>)
  case [simp]: (Effect a d ne)
  have a: "\<forall>x \<in> set (map (map_atom_fmla term.CONST) a). wf_fmla_atom (ty_term vart objT) x"
    using assms wf_fmla_atom_CONST by (auto simp: wf_effect_alt list_all_iff)
  have d: "\<forall>x \<in> set (map (map_atom_fmla term.CONST) d). wf_fmla_atom (ty_term vart objT) x"
    using assms wf_fmla_atom_CONST by (auto simp: wf_effect_alt list_all_iff)
  have ne: "\<forall>x \<in> set (map (map_numeric_effect term.CONST) ne). wf_numeric_effect (ty_term vart objT) x"
    using assms wf_num_eff_CONST by (auto simp: wf_effect_alt list_all_iff)
  show ?thesis using a d ne by simp
qed

subsubsection \<open>Well-formedness of the grounded actions\<close>

text \<open>Every reachable op instantiates to a well-formed ground action (\<open>wf_resolve_instantiate\<close>),
  so its precondition / effect are OBJECT-well-formed under \<^const>\<open>objT\<close>. The CONST lift then makes
  the nullary grounded schema well-formed (its parameter table is empty; typing is by \<open>png.constT
  = objT\<close>).\<close>

lemma varfree_wf_resinst:
  assumes "\<pi> \<in> set ops"
  shows "wf_fmla objT (precondition (the (res_inst \<pi>)))"
    and "wf_effect objT (effect (the (res_inst \<pi>)))"
proof -
  have "wf_ground_action (the (res_inst \<pi>))"
    using assms ops_wf wf_resolve_instantiate by blast
  thus "wf_fmla objT (precondition (the (res_inst \<pi>)))"
    and "wf_effect objT (effect (the (res_inst \<pi>)))"
    unfolding wf_ground_action_alt by simp_all
qed

lemma varfree_inst_ac_tyt: "png.ac_tyt (varfree_inst_ac \<pi> n) = ty_term Map.empty objT"
  unfolding png.ac_tyt_def varfree_png_constT by simp

lemma varfree_inst_ac_wf:
  assumes "\<pi> \<in> set ops"
  shows "png.wf_classical_action_schema (varfree_inst_ac \<pi> n)"
proof (intro png.wf_classical_action_schemaI)
  show "distinct (map fst (ac_params (varfree_inst_ac \<pi> n)))" by simp
  have "wf_fmla (ty_term Map.empty objT) (map_atom_fmla term.CONST (precondition (the (res_inst \<pi>))))"
    using varfree_wf_resinst(1)[OF assms] by (rule wf_fmla_CONST)
  thus "png.wf_fmla (png.ac_tyt (varfree_inst_ac \<pi> n)) (ac_pre (varfree_inst_ac \<pi> n))"
    unfolding varfree_inst_ac_tyt varfree_png_wf_fmla by simp
  have "wf_effect (ty_term Map.empty objT) (map_ast_effect term.CONST (effect (the (res_inst \<pi>))))"
    using varfree_wf_resinst(2)[OF assms] by (rule wf_effect_CONST)
  thus "png.wf_effect (png.ac_tyt (varfree_inst_ac \<pi> n)) (ac_eff (varfree_inst_ac \<pi> n))"
    unfolding varfree_inst_ac_tyt varfree_png_wf_effect by simp
qed

lemma varfree_gr_acs_wf: "\<forall>a \<in> set (actions varfree_inst_dom). png.wf_classical_action_schema a"
proof
  fix a assume "a \<in> set (actions varfree_inst_dom)"
  then obtain \<pi> n where "a = varfree_inst_ac \<pi> n" "\<pi> \<in> set ops"
    unfolding varfree_inst_dom_sel using map2_obtain by metis
  thus "png.wf_classical_action_schema a" using varfree_inst_ac_wf by simp
qed

subsubsection \<open>Well-formedness of the grounded domain and problem\<close>

text \<open>\<open>png\<close> shares \<open>P\<close>'s type declarations, so its type / predicate / function well-formedness
  primitives coincide with \<open>P\<close>'s.\<close>

lemma varfree_png_wf_type: "png.wf_type = wf_type"
proof (intro ext)
  fix T show "png.wf_type T = wf_type T" by (cases T) simp
qed

lemma varfree_png_wf_pred_decl: "png.wf_predicate_decl = wf_predicate_decl"
proof (intro ext)
  fix p show "png.wf_predicate_decl p = wf_predicate_decl p"
    by (cases p) (simp add: varfree_png_wf_type)
qed

lemma varfree_png_wf_func_decl: "png.wf_function_decl = wf_function_decl"
proof (intro ext)
  fix f show "png.wf_function_decl f = wf_function_decl f"
    by (cases f) (simp add: varfree_png_wf_type)
qed

text \<open>The grounded domain signature is well-formed: types / predicates / functions are \<open>P\<close>'s,
  and the promoted constants (\<open>consts (domain P) @ objects P\<close>) are distinct and well-typed
  because \<open>P\<close>'s problem signature says so.\<close>

lemma varfree_inst_dom_wf_sig: "png.wf_domain_signature"
  unfolding domain_signature.wf_domain_signature_def
proof (intro conjI)
  have tyeq: "types (ast_problem.domain varfree_inst_prob) = types (domain P)" by simp
  show "png.wf_types"
    unfolding png.wf_types_def tyeq using wf_D_sig(1) unfolding wf_types_def by simp
  show "distinct (map pred (predicates (ast_problem.domain varfree_inst_prob)))"
    using wf_D_sig(2) by simp
  show "\<forall>p \<in> set (predicates (ast_problem.domain varfree_inst_prob)). png.wf_predicate_decl p"
    unfolding varfree_png_wf_pred_decl using wf_D_sig(3) by simp
  show "distinct (map function_decl.func (functions (ast_problem.domain varfree_inst_prob)))"
    using wf_D_sig(4) by simp
  show "\<forall>f \<in> set (functions (ast_problem.domain varfree_inst_prob)). png.wf_function_decl f"
    unfolding varfree_png_wf_func_decl using wf_D_sig(5) by simp
  show "distinct (map fst (consts (ast_problem.domain varfree_inst_prob)))"
    using wf_P_sig(2) by (auto simp: distinct_append)
  show "\<forall>(n,T) \<in> set (consts (ast_problem.domain varfree_inst_prob)). png.wf_type T"
    unfolding varfree_png_wf_type using wf_D_sig(7) wf_P_sig(3) by auto
qed

theorem varfree_inst_dom_wf: "png.wf_classical_domain"
proof (intro png.wf_classical_domainI)
  show "png.wf_domain_signature" using varfree_inst_dom_wf_sig .
  show "distinct (map ast_classical_action_schema_name (actions (ast_problem.domain varfree_inst_prob)))"
    using varfree_inst_dom_names_dis by simp
  show "\<forall>a \<in> set (actions (ast_problem.domain varfree_inst_prob)). png.wf_classical_action_schema a"
    using varfree_gr_acs_wf by simp
qed

text \<open>\<^const>\<open>wf_func_assign\<close> depends only on \<^const>\<open>objT\<close> and the (shared) function typing, so it too
  coincides with \<open>P\<close>'s.\<close>
lemma varfree_png_objT': "problem_signature.objT (consts (domain P) @ objects P) [] = objT"
  unfolding problem_signature.objT_def domain_signature.constT_def objT_def constT_def
  by (simp add: map_of_append)

lemma varfree_png_wf_func_assign: "png.wf_func_assign = wf_func_assign"
proof (intro ext)
  fix f show "png.wf_func_assign f = wf_func_assign f"
    by (cases f rule: wf_func_assign.cases)
       (simp_all add: problem_signature.wf_func_assign.simps varfree_png_objT')
qed

text \<open>The problem signature is well-formed (domain sig + no objects), and the initial / goal
  facts transfer verbatim from \<open>P\<close>'s \<^const>\<open>wf_classical_problem\<close> because \<open>png\<close>'s \<^const>\<open>init\<close> /
  \<^const>\<open>goal\<close> are \<open>P\<close>'s and \<open>png.objT = objT\<close>.\<close>
lemma varfree_inst_prob_wf_sig: "png.wf_problem_signature"
  unfolding problem_signature.wf_problem_signature_def
proof (intro conjI)
  show "png.wf_domain_signature" using varfree_inst_dom_wf_sig .
  show "distinct (map fst (objects varfree_inst_prob) @ map fst (consts (ast_problem.domain varfree_inst_prob)))"
    using varfree_inst_dom_wf_sig
    unfolding domain_signature.wf_domain_signature_def by (simp add: varfree_inst_prob_sel)
  show "\<forall>(n,T) \<in> set (objects varfree_inst_prob). png.wf_type T" by simp
qed

theorem varfree_inst_prob_wf: "png.wf_classical_problem"
proof (intro png.wf_classical_problemI)
  show "png.wf_classical_domain" using varfree_inst_dom_wf .
  show "png.wf_problem_signature" using varfree_inst_prob_wf_sig .
  show "distinct (init varfree_inst_prob)"
    using wf_classical_problemD(3)[OF wf_problem] by simp
  show "\<forall>f \<in> set (init varfree_inst_prob). png.wf_fmla_atom png.objT f \<or> png.wf_func_assign f"
    using wf_classical_problemD(4)[OF wf_problem]
    unfolding varfree_png_wf_fmla_atom varfree_png_wf_func_assign varfree_png_objT by simp
  show "png.wf_fmla png.objT (goal varfree_inst_prob)"
    using wf_classical_problemD(5)[OF wf_problem]
    unfolding varfree_png_wf_fmla varfree_png_objT by simp
qed

end

subsection \<open>The output shape: variable-freeness\<close>

text \<open>The stage's output invariant, mirroring \<open>grounded_dom\<close>/\<open>grounded_prob\<close> of the
  propositional grounder: every action schema is nullary (variable-free) and the problem
  carries no objects (they are promoted to constants). The downstream fact-folding stage
  consumes any problem of this shape.\<close>

definition (in ast_classical_domain) varfree_dom :: bool where
  "varfree_dom \<equiv> \<forall>a \<in> set (actions D). ac_params a = []"

context ast_classical_domain begin

lemma varfree_domI [intro]:
  assumes "\<And>a. a \<in> set (actions D) \<Longrightarrow> ac_params a = []"
  shows varfree_dom
  unfolding varfree_dom_def using assms by blast

lemma varfree_domD [dest]:
  assumes varfree_dom and "a \<in> set (actions D)"
  shows "ac_params a = []"
  using assms unfolding varfree_dom_def by blast

end

definition (in ast_classical_problem) varfree_prob :: bool where
  "varfree_prob \<equiv> varfree_dom \<and> objects P = []"

context ast_classical_problem begin

lemma varfree_probI [intro]:
  assumes varfree_dom "objects P = []"
  shows varfree_prob
  unfolding varfree_prob_def using assms by blast

lemma varfree_probD [dest]:
  assumes varfree_prob shows varfree_dom "objects P = []"
  using assms unfolding varfree_prob_def by blast+

end

context varfree begin

lemma varfree_inst_dom_varfree: "ast_classical_domain.varfree_dom varfree_inst_dom"
proof (rule ast_classical_domain.varfree_domI)
  fix a assume "a \<in> set (actions varfree_inst_dom)"
  then obtain \<pi> n where "a = varfree_inst_ac \<pi> n"
    unfolding varfree_inst_dom_sel using map2_obtain by metis
  thus "ac_params a = []" by simp
qed

lemma varfree_inst_prob_varfree: "ast_classical_problem.varfree_prob varfree_inst_prob"
  by (rule ast_classical_problem.varfree_probI)
     (simp_all add: varfree_inst_dom_varfree)

end

end
