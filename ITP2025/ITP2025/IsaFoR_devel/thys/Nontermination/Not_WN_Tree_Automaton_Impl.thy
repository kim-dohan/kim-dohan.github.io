theory Not_WN_Tree_Automaton_Impl
imports
  TA.Tree_Automata_NF_Impl
  TA.Tree_Automata_Impl
  First_Order_Rewriting.Trs_Impl
  Framework.QDP_Framework_Impl
begin

datatype ('f,'q)not_wn_ta_prf = Not_wn_ta_prf "('q,'f)tree_automaton" "'q ta_relation"

fun check_trs_not_wn where
  "check_trs_not_wn R (Not_wn_ta_prf TA rel) = do {
    check_varcond_subset R;
    check_left_linear_trs R;
    let TA_trim = trim_ta (ta_of_ta TA);
    check (\<not> ta_empty TA_trim) (showsl_lit (STR ''TA is empty''));
    tree_aut_trs_closed TA rel R;
    check (\<not> ta_contains_nf TA_trim (set R)) (showsl_lit (STR ''TA accepts some normal form''))
   }"

lemma check_trs_not_wn:
  assumes "isOK (check_trs_not_wn R (Not_wn_ta_prf TA rel))"
    shows "\<not> WN (rstep (set R))"
proof standard
  obtain fin rs eps where [simp]: "TA = (Tree_Automaton fin rs eps)" by (cases TA)
  let ?TA = "ta_of_ta (Tree_Automaton fin rs eps)"
  
  have [simp]: "\<And>TA. ta_empty (trim_ta TA) = ta_empty TA"
    by (auto simp: ta_empty[where ?'c = unit] trim_ta_lang)

  from assms have
    ne: "\<not> ta_empty ?TA" and
    wf: "\<forall> (l,r) \<in> set R. vars_term r \<subseteq> vars_term l" and
    no_nf: "ta_lang ?TA \<inter> NF_trs (set R) = {}"
  by (auto simp: ta_contains_nf trim_ta_lang)
  
  from assms have closed: "{t | s. s \<in> ta_lang ?TA \<and> (s,t) \<in> (rstep (set R))^*} \<subseteq> ta_lang ?TA" for t
    by (intro tree_aut_trs_closed) auto

  from assms have no_nf: "ta_lang ?TA \<inter> NF_trs (set R) = {}"
  by (auto split: option.splits simp: ta_contains_nf trim_ta_lang)

  assume wn: "WN (rstep (set R))"
  from ne obtain t::"('a, 'b) term" where lang: "t \<in> ta_lang ?TA" unfolding ta_empty[where ?'c = 'b] by blast
  from wn have "WN_on (rstep (set R)) {t}" by (simp add: WN_defs)
  from this obtain y where nf: "(t, y) \<in> (rstep (set R))\<^sup>!" by blast
  with closed lang have ylang: "y \<in> ta_lang ?TA" by blast
  moreover from nf have "y \<in> NF_trs (set R)" by blast
  ultimately show False using no_nf by blast
qed

lemma check_trs_not_wn_sn:
  assumes "isOK (check_trs_not_wn R (Not_wn_ta_prf TA rel))"
    shows "\<not> SN (rstep (set R))"
using check_trs_not_wn[OF assms] SN_imp_WN by blast

definition "check_not_wn_ta_prf I tp prf \<equiv> do {
  let R = tp_ops.rules I tp;
  check (tp_ops.Q I tp = []) (showsl_lit (STR ''strategy is unsupported for tree automata based nontermination''));
  check_trs_not_wn R prf
}"

lemma check_not_wn_ta_prf:
  assumes ok: "isOK (check_not_wn_ta_prf I tp prf)"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
proof -
  let ?R = "tp_ops.rules I tp"
  let ?Q = "tp_ops.Q I tp"
  obtain TA rel where [simp]: "prf = Not_wn_ta_prf TA rel" by (cases "prf")
  note ok = ok[unfolded check_not_wn_ta_prf_def Let_def]
  from ok have "?Q = []" by auto
  moreover from ok have "isOK(check_trs_not_wn ?R prf)" by auto
  ultimately show ?thesis using check_trs_not_wn_sn by auto
qed

end
