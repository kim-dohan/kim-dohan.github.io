theory LLVM_Termination_Prover
  imports
    Closed_Checker_Proofs
    SegToLts
begin

definition check_renaming_formula where
  "check_renaming_formula r f f\<^sub>R =
    (try checkFormula (f\<^sub>R \<longrightarrow>\<^sub>f rename_vars r f) catch
   (\<lambda>e. Inl (e \<circ> showsl  (STR ''\<newline>'')
       \<circ> showsl STR ''f_r: '' \<circ> showsl f\<^sub>R \<circ>  showsl  (STR ''\<newline>'')
       \<circ> showsl STR ''f: '' \<circ> showsl f \<circ>  showsl  (STR ''\<newline>'')
       \<circ> showsl STR ''rename_vars r f: '' \<circ> showsl (rename_vars r f) \<circ>  showsl  (STR ''\<newline>''))))"

lemma check_renaming_formula:
  assumes "isOK (check_renaming_formula r f f\<^sub>R)"
  shows "IA.implies f\<^sub>R (rename_vars r f)" "IA.formula (f\<^sub>R \<longrightarrow>\<^sub>f rename_vars r f)"
  using assms unfolding check_renaming_formula_def isOK_update_error
  using checkFormula_formula checkFormula by blast+

definition check_renaming_transition_rule where
  "check_renaming_transition_rule r as as\<^sub>R tr tr\<^sub>R =
   (let s = LTS.source tr; t = LTS.target tr;
    r' = (\<lambda>v. case v of Pre v' \<Rightarrow> Pre (r s v') | Post v' \<Rightarrow> Post (r t v') |
         Intermediate v' \<Rightarrow> Intermediate (r s v') )
    in try
   do
   {check (s = LTS.source tr\<^sub>R \<and> t = LTS.target tr\<^sub>R) (showsl STR ''Non matching locations'');
    check_renaming_formula r' (transition_formula tr) (transition_formula tr\<^sub>R);
    check_renaming_formula (r s) (as s) (as\<^sub>R s);
    check_renaming_formula (r t) (as t) (as\<^sub>R t)
  } catch (\<lambda>f. Inl (showsl STR ''Checking '' \<circ> showsl s \<circ> showsl '' --> '' \<circ> showsl t \<circ> showsl STR '':''
                                \<circ> f \<circ> showsl  (STR ''\<newline>------------------\<newline>''))))"

lemma check_renaming_transition_rule:
  assumes "isOK (check_renaming_transition_rule r (assertion_of lts) (assertion_of lts\<^sub>R) tr tr\<^sub>R)"
  shows "IA.transition_renamed r (assertion_of lts) (assertion_of lts\<^sub>R) tr tr\<^sub>R"
    using assms check_renaming_formula unfolding check_renaming_transition_rule_def
    apply(cases tr, cases tr\<^sub>R)
    apply(auto)
    by (smt check_renaming_formula(1) formula.implies_Language subsetD)+

lemma choiceE:
  assumes "isOK (Error_Monad.choice xs)"
  shows "\<exists>x \<in> set xs. isOK x"
  using assms by (induction xs) (auto)

definition check_renaming_lts where
  "check_renaming_lts r lts lts\<^sub>R =  (
    let
   check_l = (\<lambda>(l\<^sub>R, tr\<^sub>R). do {
      let cf = (\<lambda>(l, tr). check_renaming_transition_rule r
                          (assertion_of lts) (assertion_of lts\<^sub>R) tr tr\<^sub>R);
      try Error_Monad.choice (map cf (transitions_impl lts))
      catch (\<lambda>f. Inl (default_showsl_list id f \<circ> showsl STR ''check_renaming_lts: transition_id: '' \<circ> showsl l\<^sub>R))})
 in do {
    check (set (initial lts\<^sub>R) \<subseteq> set (initial lts)) (showsl STR ''check_renaming_lts: initial sets not matching'');
    sequence (map check_l (transitions_impl lts\<^sub>R))
  })"

lemma check_renaming_lts:
  assumes "isOK (check_renaming_lts r lts lts\<^sub>R)"
  shows "IA.renamed_lts r (lts_of lts) (lts_of lts\<^sub>R)"
proof -
  have "\<exists>(l, tr) \<in> set (transitions_impl lts). IA.transition_renamed r (assertion_of lts)
                                               (assertion_of lts\<^sub>R) tr tr\<^sub>R"
    if "(l\<^sub>R, tr\<^sub>R) \<in> set (transitions_impl lts\<^sub>R)" for l\<^sub>R tr\<^sub>R
  proof -
    define check_l where "check_l = (\<lambda>(l\<^sub>R::'e, tr\<^sub>R::(IA.sig, 'c, IA.ty, 'a) transition_rule). do {
      let cf = (\<lambda>(l, tr). check_renaming_transition_rule r
                          (assertion_of lts) (assertion_of lts\<^sub>R) tr tr\<^sub>R);
      try Error_Monad.choice (map cf (transitions_impl lts))
      catch (\<lambda>f. Inl (default_showsl_list id f \<circ> showsl STR ''check_renaming_lts: transition_id: '' \<circ> showsl l\<^sub>R))})"
    have "isOK (check_l (l\<^sub>R, tr\<^sub>R))"
      apply(rule sequence_isOK[of "map check_l (transitions_impl lts\<^sub>R)"])
      using assms that unfolding check_renaming_lts_def check_l_def by (fastforce intro: imageI)+
    then have "isOK (Error_Monad.choice
             (map (\<lambda>p. check_renaming_transition_rule r (assertion_of lts)
                  (assertion_of lts\<^sub>R) (snd p) (snd (l\<^sub>R, tr\<^sub>R))) (transitions_impl lts)))"
      unfolding check_l_def unfolding case_prod_beta Let_def isOK_update_error by blast
    then show ?thesis
      by (auto simp add: case_prod_beta dest!: check_renaming_transition_rule choiceE split: prod.splits)
  qed
  then show ?thesis
    unfolding IA.renamed_lts_def
    using assms by (auto simp add:check_renaming_lts_def case_prod_beta split: sum_bind_splits)
qed

lemma inj_on_dom:
  assumes "finite (dom m)" "card (dom m) = card (ran m)"
  shows "inj_on m (dom m)"
proof -
  have "card (m ` (dom m)) = card ((the \<circ> m) ` dom m)"
  using assms basic_trans_rules(24) card_image_le cset_fin_intros(1) image_comp ran_is_image
  by (metis)
  then show ?thesis
    using assms unfolding ran_is_image by (auto intro: eq_card_imp_inj_on)
qed

context graph_exec'
begin

definition check_initial_node where
  "check_initial_node n f = do {
    asn \<leftarrow> option_to_sum (Mapping.lookup as n) (showsl STR ''check_initial_node 1'');
    fu \<leftarrow> map_sum (\<lambda>_. showsl STR ''check_initial_node 2'') id  (find_fun prog f) ;
    let bn = basic_block.name (hd_blocks fu);
    let p = map parameter_name (params fu);
    check (card (Mapping.keys (stack asn)) = card (Mapping_values (stack asn))) (showsl STR ''check_initial_node 3'');
    check (set p = Mapping.keys (stack asn)) (showsl STR ''check_initial_node 4'');
    check (pos asn = (f, bn, 0)) (showsl STR ''check_initial_node 5'');
    checkFormula (kb asn)
}"

lemma check_initial_node:
  assumes "isOK (check_initial_node n f)"
  shows "initial_abstract_state prog f ((asm_to_as \<circ> (the \<circ> (Mapping.lookup as))) n)"
proof -
  obtain asm where asm: "Mapping.lookup as n = Some asm"
    using assms unfolding check_initial_node_def
    by (auto split: Option.bind_splits sum_bind_splits elim!: option_to_sum.elims)
  have "(n, asm) \<in> set nodes_asm_list"
    using asm map_of_SomeD unfolding as_def lookup_of_alist by metis
  then have "finite (Mapping.keys (abstract_state_mapping.stack asm))"
    using asm unfolding nodes_asm_list_def by (auto split: prod.split)
  then show ?thesis
    using assms unfolding check_initial_node_def
    using  IA.check_valid_formula
    by (auto intro!: inj_on_dom
        split: Option.bind_splits sum_bind_splits elim!: option_to_sum.elims
        simp add: checkFormula_def asm keys_dom_lookup Mapping_values_ran)
qed

end

declare graph_exec'.check_initial_node_def[code]

datatype ('node,'f,'v,'t,'l,'tr,'h) llvm_termination_proof =
  Llvm_termination_proof
    (llt_seg: "('node, 'v) seg_impl")
    (llt_lts_renaming: "('l \<times> ('v \<times> 'v) list) list")
    (llt_lts_impl: "('f,'v,'t,'l,'tr) lts_impl")
    (llt_term_proof: "('f,'v,'t,'l,'tr,'h) termination_proof")

fun llvm_check_represents_seg where
  "llvm_check_represents_seg p fn seg = do {
    graph_exec'.closedGraphFun seg p;
    check ((initial_node seg) \<in> set (graph_exec'.nodes_list seg)) (showsl STR ''initial node not in nodes'');
    graph_exec'.check_initial_node seg p (initial_node seg) fn
}"

fun llvm_check_represents_lts where
  "llvm_check_represents_lts p fn seg ltsa rs = do {
    graph_exec'.closedGraphFun seg p;
    check ((initial_node seg) \<in> set (graph_exec'.nodes_list seg)) (showsl STR ''initial node not in nodes'');
    graph_exec'.check_initial_node seg p (initial_node seg) fn;
    lts_from_seg \<leftarrow> option_to_sum (graph_exec'.seg_impl_to_lts_impl seg) (showsl STR ''seg_impl_to_lts_impl failed'');
    let rs' = (\<lambda>l x. case Mapping.lookup (Mapping.of_alist rs) l of Some r \<Rightarrow>
                (case Mapping.lookup (Mapping.of_alist r) x of Some y \<Rightarrow> y | None \<Rightarrow> x)
               | None \<Rightarrow> x);
    check_renaming_lts rs' ltsa lts_from_seg
}"

fun llvm_check_termination where
  "llvm_check_termination p fn (Llvm_termination_proof seg rs lts lts_proof) = do {
    graph_exec'.closedGraphFun seg p;
    check ((initial_node seg) \<in> set (graph_exec'.nodes_list seg)) (showsl STR ''initial node not in nodes'');
    graph_exec'.check_initial_node seg p (initial_node seg) fn;
    lts_from_seg \<leftarrow> option_to_sum (graph_exec'.seg_impl_to_lts_impl seg) (showsl STR ''seg_impl_to_lts_impl failed'');
    let rs' = (\<lambda>l x. case Mapping.lookup (Mapping.of_alist rs) l of Some r \<Rightarrow>
                (case Mapping.lookup (Mapping.of_alist r) x of Some y \<Rightarrow> y | None \<Rightarrow> x)
               | None \<Rightarrow> x);
    check_renaming_lts rs' lts lts_from_seg;
    IA.check_termination lts lts_proof
}"

lemma option_to_sumE:
  assumes "isOK (option_to_sum M e)"
  obtains opt where "M = Some opt"
  using assms by (cases M) (auto)

lemma llvm_check_termination:
  assumes
    "isOK (llvm_check_termination p fn ll_proof)"
    "initial_llvm_frame p fn f"
    "frames c = [f]"
  shows
    "SN_on (step'_relation p) {c}"
proof -
  let ?nodes = "set (graph_exec'.nodes_list (llt_seg ll_proof))"
  let ?as_of_node = "(asm_to_as \<circ>\<circ>\<circ> (\<circ>)) the (Mapping.lookup (graph_exec'.as (llt_seg ll_proof)))"
  let ?renaming_of_edge = "graph_exec.renaming_of_edge' (graph_exec'.renaming_of_edge (llt_seg ll_proof))"
  let ?edges = "graph_exec'.edges (llt_seg ll_proof)"
  let ?all_var_names = "graph_exec'.all_var_names (llt_seg ll_proof)"
  let ?lv_to_pv = "graph_exec'.lv_to_pv (llt_seg ll_proof)"
  let ?initial_node = "initial_node (llt_seg ll_proof)"
  let ?rs' = "(\<lambda>l x. case Mapping.lookup (Mapping.of_alist (llt_lts_renaming ll_proof)) l of Some r \<Rightarrow>
                (case Mapping.lookup (Mapping.of_alist r) x of Some y \<Rightarrow> y | None \<Rightarrow> x)
               | None \<Rightarrow> x)"
  obtain lts_from_seg where
    lts_from_seg: "graph_exec'.seg_impl_to_lts_impl (llt_seg ll_proof) = Some lts_from_seg"
    using assms by (cases ll_proof) (auto elim: option_to_sumE)
  then have a: "lts_of lts_from_seg
    = graph'.lts_of_graph ?as_of_node ?renaming_of_edge ?edges ?lv_to_pv id {?initial_node}"
    using graph_exec'.seg_impl_to_lts_impl_eq_lts_of_graph by metis
  have b: "IA.renamed_lts ?rs' (lts_of (llt_lts_impl ll_proof)) (lts_of lts_from_seg)"
    using assms lts_from_seg
    by (cases ll_proof) (auto intro!: check_renaming_lts simp add: split: option.splits)
  have c: "IA.lts_termination (lts_of (llt_lts_impl ll_proof))"
    using assms  by (cases ll_proof)
      (auto intro!: IA.check_termination[of _ "llt_term_proof ll_proof"]
        simp add: split: option.splits)
  note termI = graph'.lts_termination_SN_as_step[where loc_of_node=id]
  have d: "IA.lts_termination (lts_of lts_from_seg)"
    using b c IA.lts_renaming_termination by blast
  then have e: "SN_on (graph'.as_step ?as_of_node ?renaming_of_edge ?edges)
    {(?initial_node, assig_of_state c)}"
    by (auto simp add: a intro!: termI)
  have f: "llvm_se_graph.seg_represents ?renaming_of_edge ?edges ?as_of_node p"
    using assms by (cases ll_proof)
      (auto intro!: graph_exec'.closedGraphFun split: option.splits)
  have g: "initial_abstract_state p fn (?as_of_node ?initial_node)"
    using assms
    by(cases ll_proof, intro graph_exec'.check_initial_node[of _ _ ?initial_node "fn"])
      (auto simp add:  split: option.splits)
  have h: "?nodes = graph'.nodes (graph_exec'.edges (llt_seg ll_proof))"
    unfolding graph_exec'.nodes_list_def graph'.nodes_def graph_exec'.edges_list_def
      graph_exec'.edges_def by (auto)
  show ?thesis
    using f assms e g h
    apply (cases ll_proof)
    by (intro llvm_se_graph.SN_on_initial_state) (fastforce split: option.splits)+
qed

end