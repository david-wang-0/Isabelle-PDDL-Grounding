theory Numeric_Grounder
  imports Classical_Grounded_PDDL_Semantics
begin

context ast_classical_problem begin

text \<open>Numeric grounder: like the propositional grounder (\<^const>\<open>grounder.ground_prob\<close>) but keeping
  the ground actions' numeric effects, numeric preconditions, and the domain's function
  declarations --- only the action \<^emph>\<open>parameters\<close> are instantiated (via \<^const>\<open>res_inst\<close>), nothing is
  propositionalised. Grounds the un-relaxed \<open>P\<close> over the (over-approximated) reachable ops \<open>ops\<close>.\<close>

definition numeric_ground_ac :: "ast_classical_plan_action \<Rightarrow> name \<Rightarrow> ast_classical_action_schema" where
  "numeric_ground_ac \<pi> n =
     SimpleActionSchema (ActionHead n [])
       (SimpleActionBody
          (map_atom_fmla term.CONST (precondition (the (res_inst \<pi>))))
          (map_ast_effect term.CONST (effect (the (res_inst \<pi>)))))"

lemma numeric_ground_ac_sel [simp]:
  "ac_name (numeric_ground_ac \<pi> n) = n"
  "ac_params (numeric_ground_ac \<pi> n) = []"
  "ac_pre (numeric_ground_ac \<pi> n) = map_atom_fmla term.CONST (precondition (the (res_inst \<pi>)))"
  "ac_eff (numeric_ground_ac \<pi> n) = map_ast_effect term.CONST (effect (the (res_inst \<pi>)))"
  unfolding numeric_ground_ac_def by simp_all

lemma ac_tsubst_Nil_CONST [simp]: "ac_tsubst [] [] (term.CONST c) = c"
  by simp

text \<open>\<^bold>\<open>The key correspondence.\<close> Instantiating the nullary numeric-grounded action at \<open>[]\<close> undoes the
  \<open>term.CONST\<close> lift and recovers exactly the original instantiated ground action \<^term>\<open>the (res_inst \<pi>)\<close>
  --- numerics and all. (Contrast the propositional grounder, whose \<open>ground_fmla\<close> re-indexes atoms.)\<close>
lemma numeric_ground_ac_inst:
  "instantiate_classical_action_schema (numeric_ground_ac \<pi> n) [] = the (res_inst \<pi>)"
proof -
  have hf: "subst_term f \<circ> term.CONST = id" for f :: "variable \<Rightarrow> object" by (rule ext) simp
  have "instantiate_classical_action_schema (numeric_ground_ac \<pi> n) [] =
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


context grounder begin

text \<open>The numeric grounded domain / problem, aligned with the propositional \<^const>\<open>grounder.ground_dom\<close>
  / \<^const>\<open>grounder.ground_prob\<close>: same nullary action \<^emph>\<open>names\<close> (\<open>op_names\<close>, one per reachable op),
  but the domain keeps the original types / predicates / functions and each action retains its
  numeric ground body.\<close>

text \<open>The grounded actions are nullary schemas whose bodies reference the instantiation's
  \<^emph>\<open>objects\<close> (via \<^const>\<open>term.CONST\<close>). A schema's body is typed by \<^const>\<open>ac_tyt\<close> \<open>= ty_term
  (params) constT\<close> --- i.e. by \<^emph>\<open>constants\<close> only --- so for the grounded schemas to be
  well-formed we \<^bold>\<open>promote the objects to constants\<close> (\<open>consts = consts (domain P) @ objects P\<close>,
  \<open>objects = []\<close>). This mirrors the propositional grounder's \<open>objects P\<^sub>G = []\<close> and is
  \<^emph>\<open>semantics-preserving\<close>: \<^term>\<open>objT\<close> is definitionally unchanged, since
  \<open>map_of (consts @ objects) = map_of objects ++ constT = objT\<close>.\<close>

definition numeric_ground_dom :: ast_classical_domain where
  "numeric_ground_dom =
     Domain (types (domain P)) (predicates (domain P)) (functions (domain P))
            (consts (domain P) @ objects P)
            (map2 numeric_ground_ac ops op_names)"

definition numeric_ground_prob :: ast_classical_problem where
  "numeric_ground_prob = Problem numeric_ground_dom [] (init P) (goal P)"

lemma numeric_ground_dom_sel [simp]:
  "types numeric_ground_dom = types (domain P)"
  "predicates numeric_ground_dom = predicates (domain P)"
  "functions numeric_ground_dom = functions (domain P)"
  "consts numeric_ground_dom = consts (domain P) @ objects P"
  "actions numeric_ground_dom = map2 numeric_ground_ac ops op_names"
  unfolding numeric_ground_dom_def by simp_all

lemma numeric_ground_prob_sel [simp]:
  "domain numeric_ground_prob = numeric_ground_dom"
  "objects numeric_ground_prob = []"
  "init numeric_ground_prob = init P"
  "goal numeric_ground_prob = goal P"
  unfolding numeric_ground_prob_def by simp_all

lemma numeric_ground_dom_names:
  "map ast_classical_action_schema_name (actions numeric_ground_dom) = op_names"
proof -
  have "map ast_classical_action_schema_name (map2 numeric_ground_ac xs ys) = ys"
    if "length xs = length ys" for xs ys
    using that by (induction xs ys rule: list_induct2) (simp_all add: numeric_ground_ac_def)
  thus ?thesis using ops_len by simp
qed

lemma numeric_ground_dom_names_dis:
  "distinct (map ast_classical_action_schema_name (actions numeric_ground_dom))"
  using numeric_ground_dom_names op_names_dis by simp

end


sublocale wf_grounder_num \<subseteq> png: ast_classical_problem numeric_ground_prob .

context wf_grounder_num begin

subsection \<open>Well-formedness of the numeric grounded problem\<close>

text \<open>\<^bold>\<open>Signature bridge.\<close> The numeric grounded domain keeps \<open>P\<close>'s types / predicates /
  functions and merely \<^emph>\<open>promotes objects to constants\<close> (\<open>consts = consts (domain P) @ objects P\<close>,
  \<open>objects = []\<close>). Hence \<^const>\<open>png.constT\<close> and \<^const>\<open>png.objT\<close> both collapse to \<^const>\<open>objT\<close>,
  and the type / predicate / function signatures coincide with \<open>P\<close>'s.\<close>

lemma numeric_png_constT: "png.constT = objT"
proof -
  have "png.constT = map_of (consts (domain P) @ objects P)"
    unfolding png.constT_def by simp
  also have "\<dots> = map_of (objects P) ++ map_of (consts (domain P))"
    by (simp add: map_of_append)
  also have "\<dots> = objT" unfolding objT_def constT_def by simp
  finally show ?thesis .
qed

lemma numeric_png_objT: "png.objT = objT"
  unfolding png.objT_def numeric_png_constT by simp

lemma numeric_png_sig: "png.sig = sig"
  unfolding png.sig_def sig_def by simp

lemma numeric_png_func_sig: "png.func_sig = func_sig"
  unfolding png.func_sig_def func_sig_def by simp

text \<open>\<open>png\<close> shares \<open>P\<close>'s types / predicates / functions, so its typing / well-formedness
  primitives coincide with \<open>P\<close>'s (as functions of the entity-typing \<open>tyt\<close>).\<close>

lemma numeric_png_of_type: "png.of_type = of_type"
  unfolding png.of_type_def of_type_def png.subtype_rel_def subtype_rel_def by simp

lemma numeric_png_is_of_type: "png.is_of_type = is_of_type"
  unfolding png.is_of_type_def is_of_type_def numeric_png_of_type by simp

lemma numeric_png_wf_pne: "png.wf_primitive_numeric_expression = wf_primitive_numeric_expression"
proof (intro ext)
  fix tyt p
  show "png.wf_primitive_numeric_expression tyt p = wf_primitive_numeric_expression tyt p"
    by (cases p) (simp add: numeric_png_func_sig numeric_png_is_of_type)
qed

lemma numeric_png_wf_ne: "png.wf_numeric_expression = wf_numeric_expression"
proof (intro ext)
  fix tyt n
  show "png.wf_numeric_expression tyt n = wf_numeric_expression tyt n"
    by (induction n) (simp_all add: numeric_png_wf_pne)
qed

lemma numeric_png_wf_atom: "png.wf_atom = wf_atom"
proof (intro ext)
  fix tyt a
  show "png.wf_atom tyt a = wf_atom tyt a"
    by (cases a) (simp_all add: numeric_png_sig numeric_png_is_of_type numeric_png_wf_ne)
qed

lemma numeric_png_wf_fmla: "png.wf_fmla = wf_fmla"
proof (intro ext)
  fix tyt \<phi>
  show "png.wf_fmla tyt \<phi> = wf_fmla tyt \<phi>"
    by (induction \<phi>) (simp_all add: numeric_png_wf_atom)
qed

lemma numeric_png_wf_fmla_atom: "png.wf_fmla_atom = wf_fmla_atom"
proof (intro ext)
  fix tyt \<phi>
  show "png.wf_fmla_atom tyt \<phi> = wf_fmla_atom tyt \<phi>"
    by (cases \<phi> rule: wf_fmla_atom.cases) (simp_all add: numeric_png_sig numeric_png_is_of_type)
qed

lemma numeric_png_wf_num_eff: "png.wf_numeric_effect = wf_numeric_effect"
proof (intro ext)
  fix tyt ne
  show "png.wf_numeric_effect tyt ne = wf_numeric_effect tyt ne"
    by (cases ne) (simp add: numeric_png_wf_pne numeric_png_wf_ne)
qed

lemma numeric_png_wf_effect: "png.wf_effect = wf_effect"
proof (intro ext)
  fix tyt \<epsilon>
  show "png.wf_effect tyt \<epsilon> = wf_effect tyt \<epsilon>"
    by (cases \<epsilon>) (simp add: numeric_png_wf_fmla_atom numeric_png_wf_num_eff)
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

lemma numeric_wf_resinst:
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

lemma numeric_ground_ac_tyt: "png.ac_tyt (numeric_ground_ac \<pi> n) = ty_term Map.empty objT"
  unfolding png.ac_tyt_def numeric_png_constT by simp

lemma numeric_ground_ac_wf:
  assumes "\<pi> \<in> set ops"
  shows "png.wf_classical_action_schema (numeric_ground_ac \<pi> n)"
proof (intro png.wf_classical_action_schemaI)
  show "distinct (map fst (ac_params (numeric_ground_ac \<pi> n)))" by simp
  have "wf_fmla (ty_term Map.empty objT) (map_atom_fmla term.CONST (precondition (the (res_inst \<pi>))))"
    using numeric_wf_resinst(1)[OF assms] by (rule wf_fmla_CONST)
  thus "png.wf_fmla (png.ac_tyt (numeric_ground_ac \<pi> n)) (ac_pre (numeric_ground_ac \<pi> n))"
    unfolding numeric_ground_ac_tyt numeric_png_wf_fmla by simp
  have "wf_effect (ty_term Map.empty objT) (map_ast_effect term.CONST (effect (the (res_inst \<pi>))))"
    using numeric_wf_resinst(2)[OF assms] by (rule wf_effect_CONST)
  thus "png.wf_effect (png.ac_tyt (numeric_ground_ac \<pi> n)) (ac_eff (numeric_ground_ac \<pi> n))"
    unfolding numeric_ground_ac_tyt numeric_png_wf_effect by simp
qed

lemma numeric_gr_acs_wf: "\<forall>a \<in> set (actions numeric_ground_dom). png.wf_classical_action_schema a"
proof
  fix a assume "a \<in> set (actions numeric_ground_dom)"
  then obtain \<pi> n where "a = numeric_ground_ac \<pi> n" "\<pi> \<in> set ops"
    unfolding numeric_ground_dom_sel using map2_obtain by metis
  thus "png.wf_classical_action_schema a" using numeric_ground_ac_wf by simp
qed

subsubsection \<open>Well-formedness of the grounded domain and problem\<close>

text \<open>\<open>png\<close> shares \<open>P\<close>'s type declarations, so its type / predicate / function well-formedness
  primitives coincide with \<open>P\<close>'s.\<close>

lemma numeric_png_wf_type: "png.wf_type = wf_type"
proof (intro ext)
  fix T show "png.wf_type T = wf_type T" by (cases T) simp
qed

lemma numeric_png_wf_pred_decl: "png.wf_predicate_decl = wf_predicate_decl"
proof (intro ext)
  fix p show "png.wf_predicate_decl p = wf_predicate_decl p"
    by (cases p) (simp add: numeric_png_wf_type)
qed

lemma numeric_png_wf_func_decl: "png.wf_function_decl = wf_function_decl"
proof (intro ext)
  fix f show "png.wf_function_decl f = wf_function_decl f"
    by (cases f) (simp add: numeric_png_wf_type)
qed

text \<open>The grounded domain signature is well-formed: types / predicates / functions are \<open>P\<close>'s,
  and the promoted constants (\<open>consts (domain P) @ objects P\<close>) are distinct and well-typed
  because \<open>P\<close>'s problem signature says so.\<close>

lemma numeric_ground_dom_wf_sig: "png.wf_domain_signature"
  unfolding domain_signature.wf_domain_signature_def
proof (intro conjI)
  have tyeq: "types (ast_problem.domain numeric_ground_prob) = types (domain P)" by simp
  show "png.wf_types"
    unfolding png.wf_types_def tyeq using wf_D_sig(1) unfolding wf_types_def by simp
  show "distinct (map pred (predicates (ast_problem.domain numeric_ground_prob)))"
    using wf_D_sig(2) by simp
  show "\<forall>p \<in> set (predicates (ast_problem.domain numeric_ground_prob)). png.wf_predicate_decl p"
    unfolding numeric_png_wf_pred_decl using wf_D_sig(3) by simp
  show "distinct (map function_decl.func (functions (ast_problem.domain numeric_ground_prob)))"
    using wf_D_sig(4) by simp
  show "\<forall>f \<in> set (functions (ast_problem.domain numeric_ground_prob)). png.wf_function_decl f"
    unfolding numeric_png_wf_func_decl using wf_D_sig(5) by simp
  show "distinct (map fst (consts (ast_problem.domain numeric_ground_prob)))"
    using wf_P_sig(2) by (auto simp: distinct_append)
  show "\<forall>(n,T) \<in> set (consts (ast_problem.domain numeric_ground_prob)). png.wf_type T"
    unfolding numeric_png_wf_type using wf_D_sig(7) wf_P_sig(3) by auto
qed

theorem numeric_ground_dom_wf: "png.wf_classical_domain"
proof (intro png.wf_classical_domainI)
  show "png.wf_domain_signature" using numeric_ground_dom_wf_sig .
  show "distinct (map ast_classical_action_schema_name (actions (ast_problem.domain numeric_ground_prob)))"
    using numeric_ground_dom_names_dis by simp
  show "\<forall>a \<in> set (actions (ast_problem.domain numeric_ground_prob)). png.wf_classical_action_schema a"
    using numeric_gr_acs_wf by simp
qed

text \<open>\<^const>\<open>wf_func_assign\<close> depends only on \<^const>\<open>objT\<close> and the (shared) function typing, so it too
  coincides with \<open>P\<close>'s.\<close>
lemma numeric_png_objT': "problem_signature.objT (consts (domain P) @ objects P) [] = objT"
  unfolding problem_signature.objT_def domain_signature.constT_def objT_def constT_def
  by (simp add: map_of_append)

lemma numeric_png_wf_func_assign: "png.wf_func_assign = wf_func_assign"
proof (intro ext)
  fix f show "png.wf_func_assign f = wf_func_assign f"
    by (cases f rule: wf_func_assign.cases)
       (simp_all add: problem_signature.wf_func_assign.simps numeric_png_objT')
qed

text \<open>The problem signature is well-formed (domain sig + no objects), and the initial / goal
  facts transfer verbatim from \<open>P\<close>'s \<^const>\<open>wf_classical_problem\<close> because \<open>png\<close>'s \<^const>\<open>init\<close> /
  \<^const>\<open>goal\<close> are \<open>P\<close>'s and \<open>png.objT = objT\<close>.\<close>
lemma numeric_ground_prob_wf_sig: "png.wf_problem_signature"
  unfolding problem_signature.wf_problem_signature_def
proof (intro conjI)
  show "png.wf_domain_signature" using numeric_ground_dom_wf_sig .
  show "distinct (map fst (objects numeric_ground_prob) @ map fst (consts (ast_problem.domain numeric_ground_prob)))"
    using numeric_ground_dom_wf_sig
    unfolding domain_signature.wf_domain_signature_def by (simp add: numeric_ground_prob_sel)
  show "\<forall>(n,T) \<in> set (objects numeric_ground_prob). png.wf_type T" by simp
qed

theorem numeric_ground_prob_wf: "png.wf_classical_problem"
proof (intro png.wf_classical_problemI)
  show "png.wf_classical_domain" using numeric_ground_dom_wf .
  show "png.wf_problem_signature" using numeric_ground_prob_wf_sig .
  show "distinct (init numeric_ground_prob)"
    using wf_classical_problemD(3)[OF wf_problem] by simp
  show "\<forall>f \<in> set (init numeric_ground_prob). png.wf_fmla_atom png.objT f \<or> png.wf_func_assign f"
    using wf_classical_problemD(4)[OF wf_problem]
    unfolding numeric_png_wf_fmla_atom numeric_png_wf_func_assign numeric_png_objT by simp
  show "png.wf_fmla png.objT (goal numeric_ground_prob)"
    using wf_classical_problemD(5)[OF wf_problem]
    unfolding numeric_png_wf_fmla numeric_png_objT by simp
qed


end

end
