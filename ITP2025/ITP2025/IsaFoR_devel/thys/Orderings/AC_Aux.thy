(*
Author:  Alexander Lochmann <alexander.lochmann@uibk.ac.at> (2018)
License: LGPL (see file COPYING.LESSER)
*)
theory AC_Aux
  imports
    Term_Order
    TRS.Signature_Extension
    Weighted_Path_Order.Multiset_Extension2
    AC_TRS.AC_Equivalence
    Auxx.Multiset2
    TRS.More_Abstract_Rewriting
begin

lemma lex_ext_compat_l:
  assumes compat: "locally_compatible_l {(x, y). snd (f x y)} {(x, y). fst (f x y)} (mset ss) (mset ts) (mset us)"
    and trans: "locally_trans {(x, y). snd (f x y)} (mset ss) (mset ts) (mset us)"
    and "length ss = n" and "length ts = n" and "length us = n"
    and "\<forall> i < length ts. snd (f (ss ! i) (ts ! i))" and "fst (lex_ext f n ts us)"
  shows "fst (lex_ext f n ss us)"
proof -
  note len = assms(3-5)
  from assms(7) obtain i where wit_len: "i < length ts \<and> i < length us" and ns: "\<forall>j<i. snd (f (ts ! j) (us ! j))"
    and s: "fst (f (ts ! i) (us ! i))" unfolding lex_ext_iff by (auto simp add: len)
  from ns wit_len have "\<forall> j < i. snd (f (ss ! j) (us ! j))"
    using len assms(2, 6) nth_mem dual_order.strict_trans unfolding locally_trans_def in_multiset_in_set
    by auto (smt dual_order.strict_trans nth_mem)
  moreover have "fst (f (ss ! i) (us ! i))" using len wit_len s assms(1)
    unfolding locally_compatible_l_def in_multiset_in_set by auto (metis assms(6) nth_mem) 
  ultimately show ?thesis using len wit_len by (auto simp add: lex_ext_iff)
qed

lemma lex_ext_compat_r:
  assumes compat: "locally_compatible_r {(x, y). snd (f x y)} {(x, y). fst (f x y)} (mset ss) (mset ts) (mset us)"
    and trans: "locally_trans {(x, y). snd (f x y)} (mset ss) (mset ts) (mset us)"
    and "length ss = n" and "length ts = n" and "length us = n"
    and "\<forall> i < length us. snd (f (ts ! i) (us ! i))" and "fst (lex_ext f n ss ts)"
  shows "fst (lex_ext f n ss us)"
proof -
  note len = assms(3-5)
  from assms(7) obtain i where wit_len: "i < length ss \<and> i < length ts" and ns: "\<forall>j<i. snd (f (ss ! j) (ts ! j))"
    and s: "fst (f (ss ! i) (ts ! i))" unfolding lex_ext_iff by (auto simp add: len)
  from ns wit_len have "\<forall> j < i. snd (f (ss ! j) (us ! j))"
    using len assms(2, 6) nth_mem dual_order.strict_trans unfolding locally_trans_def in_multiset_in_set
    by auto (smt dual_order.strict_trans nth_mem)
  moreover have "fst (f (ss ! i) (us ! i))" using len wit_len s assms(1)
    unfolding locally_compatible_r_def in_multiset_in_set by auto (metis assms(6) nth_mem)
  ultimately show ?thesis using len wit_len by (auto simp add: lex_ext_iff)
qed

lemma lex_ext_trans:
  assumes trans_ns: "locally_trans {(x, y). snd (f x y)} (mset ss) (mset ts) (mset us)"
    and trans_s: "locally_trans {(x, y). fst (f x y)} (mset ss) (mset ts) (mset us)"
    and compat_l: "locally_compatible_l {(x, y). snd (f x y)} {(x, y). fst (f x y)} (mset ss) (mset ts) (mset us)"
    and compat_r: "locally_compatible_r {(x, y). snd (f x y)} {(x, y). fst (f x y)} (mset ss) (mset ts) (mset us)"
    and "length ss = n" and "length ts = n" and "length us = n"
    and "fst (lex_ext f n ss ts)" and "fst (lex_ext f n ts us)"
  shows "fst (lex_ext f n ss us)" using assms lex_ext_compat[of ss ts us f]
  unfolding locally_compatible_r_def locally_compatible_l_def locally_trans_def in_multiset_in_set
  by auto

lemma list_ext_pres_sub_closer:
  assumes "fst (lex_ext (\<lambda> x y. ((x,y) \<in> s_rel, (x, y) \<in> ns_rel)) (length ss) ss ts)"  (is "fst (lex_ext ?f _ _ _)")
    and "\<And> s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> (s,t) \<in> ns_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ns_rel"
    and "\<And> s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> (s,t) \<in> s_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> s_rel"
    and "length ss = length ts"
  shows "fst (lex_ext (\<lambda> x y. ((x, y) \<in> s_rel, (x, y) \<in> ns_rel)) (length (map (\<lambda>t. t \<cdot> \<sigma>) ss)) (map (\<lambda>t. t \<cdot> \<sigma>) ss) (map (\<lambda>t. t \<cdot> \<sigma>) ts))"
proof -
  let ?ss' = "map (\<lambda>t. t \<cdot> \<sigma>) ss"
  let ?ts' = "map (\<lambda>t. t \<cdot> \<sigma>) ts"
  have iff:"\<exists> i < length ss. i < length ts \<and> (\<forall> j < i. snd (?f (ss ! j) (ts ! j))) \<and> fst (?f (ss ! i) (ts ! i))"
    using lex_ext_iff assms(1) by (simp add: lex_ext_iff assms(4))
  then have "\<exists> i < length ?ss'. i < length ?ts' \<and> (\<forall> j < i. snd (?f (?ss' ! j) (?ts' ! j))) \<and> fst (?f (?ss' ! i) (?ts' ! i))"
    using assms(2-3) assms(1) leD less_imp_le_nat not_less_eq_eq snd_conv snd_conv by auto
  moreover have "length ?ss' = length ?ts'" using assms(4) by simp
  ultimately show ?thesis unfolding lex_ext_iff fst_conv by blast 
qed

lemma ns_mul_ext_cancel_singleR:
  assumes "(A, add_mset x B) \<in> ns_mul_ext ns s"
  shows "(A, B) \<in> ns_mul_ext ns s"
proof -
  from ns_mul_extE[OF assms] obtain A1 A2 B1 B2 where
   A: "A = A1 + A2" and B: "add_mset x B = B1 + B2" and mul: "(A1, B1) \<in> multpw ns" and
   str: "(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  then show ?thesis
  proof (cases "x \<in># B1")
    case True
    then obtain B1' where B1: "B1 = add_mset x B1'" by (meson mset_add)
    obtain z Z where "A1 = add_mset z Z" and "(z, x) \<in> ns" and "(Z, B1') \<in> multpw ns"
      using multpw_split1L[of A1 x B1'] mul unfolding B1 by blast 
    then show ?thesis using A B str unfolding B1 by (auto intro!: ns_mul_extI)+ 
  next
    case False
    then show ?thesis using str ns_mul_extI[OF A _ mul, of B "B2 - {#x#}"]
      by (auto, metis B Un_iff add_mset_add_single add_mset_remove_trivial diff_union_single_conv insert_DiffM set_mset_union union_commute union_single_eq_member) 
  qed
qed

lemma s_mul_ext_cancel_singleR:
  assumes "(A, add_mset x B) \<in> s_mul_ext ns s"
  shows "(A, B) \<in> s_mul_ext ns s"
proof -
  from s_mul_extE[OF assms] obtain A1 A2 B1 B2 where
   A: "A = A1 + A2" and B: "add_mset x B = B1 + B2" and mul: "(A1, B1) \<in> multpw ns" and nt: "A2 \<noteq> {#}" and
   str: "(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  then show ?thesis
  proof (cases "x \<in># B1")
    case True
    then obtain B1' where B1: "B1 = add_mset x B1'" by (meson mset_add)
    obtain z Z where "A1 = add_mset z Z" and "(z, x) \<in> ns" and "(Z, B1') \<in> multpw ns"
      using multpw_split1L[of A1 x B1'] mul unfolding B1 by blast 
    then show ?thesis using A B str unfolding B1 by (auto intro!: s_mul_extI)+
  next
    case False
    then show ?thesis using str s_mul_extI[OF A _ mul nt, of B "B2 - {#x#}"]
      by (auto, metis B Un_iff add_mset_add_single add_mset_remove_trivial diff_union_single_conv insert_DiffM set_mset_union union_commute union_single_eq_member) 
  qed
qed

lemma ns_mul_ext_cancelR:
  assumes "(A, B + C) \<in> ns_mul_ext ns s"
  shows "(A, B) \<in> ns_mul_ext ns s"
  using assms by (induct C) (auto simp add: ns_mul_ext_cancel_singleR)

lemma s_mul_ext_cancelR:
  assumes "(A, B + C) \<in> s_mul_ext ns s"
  shows "(A, B) \<in> s_mul_ext ns s"
  using assms by (induct C) (auto simp add: s_mul_ext_cancel_singleR)

lemma s_s_mul_ext_locally_trans:
  assumes "locally_trans ns A B C"
  and "locally_trans s A B C"
  and "locally_compatible_l ns s A B C"
  and "locally_compatible_r ns s A B C"
  and "(A, B) \<in> s_mul_ext ns s"
  and "(B, C) \<in> s_mul_ext ns s"
shows "(A, C) \<in> s_mul_ext ns s"
proof -
  have t: "(C, B) \<in> (mult2_alt_s (ns\<inverse>) (s\<inverse>))" using assms(6) unfolding s_mul_ext_def by auto
  have "(B, A) \<in> (mult2_alt_s (ns\<inverse>) (s\<inverse>))" using assms(5) unfolding s_mul_ext_def by auto
  from trans_mult2_alt_s_s_local[OF _ _ _ _ t this] show ?thesis using assms(1-4)
    unfolding locally_trans_def locally_compatible_l_def locally_compatible_r_def
    by (auto intro!: converse.intros simp add: s_mul_ext_def)
qed

lemma ns_s_mul_ext_locally_trans:
  assumes "locally_trans ns A B C"
  and "locally_trans s A B C"
  and "locally_compatible_l ns s A B C"
  and "locally_compatible_r ns s A B C"
  and "(A, B) \<in> ns_mul_ext ns s"
  and "(B, C) \<in> s_mul_ext ns s"
shows "(A, C) \<in> s_mul_ext ns s"
proof -
  have t: "(C, B) \<in> (mult2_alt_s (ns\<inverse>) (s\<inverse>))" using assms(6) unfolding s_mul_ext_def by auto
  have "(B, A) \<in> (mult2_alt_ns (ns\<inverse>) (s\<inverse>))" using assms(5) unfolding ns_mul_ext_def by auto
  from trans_mult2_alt_s_ns_local[OF _ _ _ _ t this] show ?thesis using assms(1-4)
    unfolding locally_trans_def locally_compatible_l_def locally_compatible_r_def
    by (auto intro!: converse.intros simp add: s_mul_ext_def)
qed

lemma s_ns_mul_ext_locally_trans:
  assumes "locally_trans ns A B C"
  and "locally_trans s A B C"
  and "locally_compatible_l ns s A B C"
  and "locally_compatible_r ns s A B C"
  and "(A, B) \<in> s_mul_ext ns s"
  and "(B, C) \<in> ns_mul_ext ns s"
shows "(A, C) \<in> s_mul_ext ns s"
proof -
  have t: "(C, B) \<in> (mult2_alt_ns (ns\<inverse>) (s\<inverse>))" using assms(6) unfolding ns_mul_ext_def by auto
  have "(B, A) \<in> (mult2_alt_s (ns\<inverse>) (s\<inverse>))" using assms(5) unfolding s_mul_ext_def by auto
  from trans_mult2_alt_ns_s_local[OF _ _ _ _ t this] show ?thesis using assms(1-4)
    unfolding locally_trans_def locally_compatible_l_def locally_compatible_r_def
    by (auto intro!: converse.intros simp add: s_mul_ext_def)
qed

lemma ns_ns_mul_ext_locally_trans:
  assumes "locally_trans ns A B C"
  and "locally_trans s A B C"
  and "locally_compatible_l ns s A B C"
  and "locally_compatible_r ns s A B C"
  and "(A, B) \<in> ns_mul_ext ns s"
  and "(B, C) \<in> ns_mul_ext ns s"
shows "(A, C) \<in> ns_mul_ext ns s"
proof -
  have t: "(C, B) \<in> (mult2_alt_ns (ns\<inverse>) (s\<inverse>))" using assms(6) unfolding ns_mul_ext_def by auto
  have "(B, A) \<in> (mult2_alt_ns (ns\<inverse>) (s\<inverse>))" using assms(5) unfolding ns_mul_ext_def by auto
  from trans_mult2_alt_ns_ns_local[OF _ _ _ _ t this] show ?thesis using assms(1-4)
    unfolding locally_trans_def locally_compatible_l_def locally_compatible_r_def
    by (auto intro!: converse.intros simp add: ns_mul_ext_def)
qed

lemma ns_s_mul_ext_sum_trans:
  assumes "locally_refl ns C"
  and "locally_trans ns A (B + C) (D + C)"
  and "locally_trans s A (B + C) (D + C)"
  and "locally_compatible_l ns s A (B + C) (D + C)"
  and "locally_compatible_r ns s A (B + C) (D + C)"
  and "(A, B + C) \<in> ns_mul_ext ns s"
  and "(B, D) \<in> s_mul_ext ns s"
  shows "(A, D + C) \<in> s_mul_ext ns s"
  using assms ns_mul_ext_refl_local[OF assms(1)] s_ns_mul_ext_union_compat[OF assms(7) ns_mul_ext_refl_local[OF assms(1)]]
  using ns_s_mul_ext_locally_trans[OF assms(2-5)] by auto

lemma s_ns_mul_ext_sum_trans:
  assumes "locally_refl ns B"
  and "locally_trans ns A (B + C) (B + D)"
  and "locally_trans s A (B + C) (B + D)"
  and "locally_compatible_l ns s A (B + C) (B + D)"
  and "locally_compatible_r ns s A (B + C) (B + D)"
  and "(A, B + C) \<in> s_mul_ext ns s"
  and "(C, D) \<in> ns_mul_ext ns s"
  shows "(A, B + D) \<in> s_mul_ext ns s"
  using assms ns_mul_ext_refl_local[OF assms(1)] ns_ns_mul_ext_union_compat[OF assms(7) ns_mul_ext_refl_local[OF assms(1)]]
  using s_ns_mul_ext_locally_trans[OF assms(2-6)] by (simp add: union_commute) 

lemma ns_ns_mul_ext_sum_trans:
  assumes "locally_refl ns C"
  and "locally_trans ns A (B + C) (D + C)"
  and "locally_trans s A (B + C) (D + C)"
  and "locally_compatible_l ns s A (B + C) (D + C)"
  and "locally_compatible_r ns s A (B + C) (D + C)"
  and "(A, B + C) \<in> ns_mul_ext ns s"
  and "(B, D) \<in> ns_mul_ext ns s"
  shows "(A, D + C) \<in> ns_mul_ext ns s"
  using assms ns_mul_ext_refl_local[OF assms(1)] ns_ns_mul_ext_union_compat[OF assms(7) ns_mul_ext_refl_local[OF assms(1)]]
  using ns_ns_mul_ext_locally_trans[OF assms(2-6)] by (simp add: union_commute)

lemma s_s_mul_ext_sum_trans:
  assumes "locally_refl ns C"
  and "locally_trans ns A (B + C) (D + C)"
  and "locally_trans s A (B + C) (D + C)"
  and "locally_compatible_l ns s A (B + C) (D + C)"
  and "locally_compatible_r ns s A (B + C) (D + C)"
  and "(A, B + C) \<in> s_mul_ext ns s"
  and "(B, D) \<in> s_mul_ext ns s"
  shows "(A, D + C) \<in> s_mul_ext ns s"
  using assms ns_mul_ext_refl_local[OF assms(1)]
  using s_ns_mul_ext_union_compat[OF assms(7) ns_mul_ext_refl_local[OF assms(1)]]
  using s_s_mul_ext_locally_trans[OF assms(2-6)] by auto



lemma actop_mset_subterm_eq:
  assumes "x \<in># actop f s"
  shows "s \<unrhd> x"
  using assms
proof (induct f s rule: actop.induct)
  case (1 f g s t)
  then show ?case by (cases "f=g", auto)
qed auto

lemma actop_mset_elem_subterm:
  assumes "x \<in># actop f (Fun f [u,v])"
  shows "Fun f [u,v] \<rhd> x"
  using assms
proof (induct f "Fun f [u,v]" arbitrary: u v rule: actop.induct)
  case (1 f s t)
  then have "x \<in># actop f s \<or> x \<in># actop f t" by simp 
  then show ?case by (metis "1.prems" actop_mset_subterm_eq supt_supteq_conv trivial_Bin_facts(5)) 
qed

lemma subset_relation:
  shows "U - S \<subseteq># (U - T) + (T - S)"
proof-
  have "U \<subseteq># (U - T) + (T - S) + S"
    by (metis (no_types, lifting) mset_subset_eq_mono_add_left_cancel subset_eq_diff_conv subset_mset.dual_order.refl subset_mset.dual_order.trans union_assoc)
  then show ?thesis using subset_eq_diff_conv by blast
qed

lemma multpw_impl_eq_size:
  assumes "(A, B) \<in> multpw ns_rel"
  shows "size A = size B"
  using assms
  by (induct rule: multpw.induct) auto


lemma ns_mul_ext_rhs_cancel:
  assumes "order_pair s ns"
  shows "(A + B, A + B - C) \<in> ns_mul_ext ns s"
  using assms by (meson order_pair.axioms(1) pre_order_pair_def subset_eq_diff_conv subset_mset.le_iff_add supseteq_imp_ns_mul_ext)

lemma s_mul_ext_subset_trans:
  assumes "order_pair s ns"
    and "(A, B) \<in> s_mul_ext ns s"
    and "C \<subseteq># B"
  shows "(A, C) \<in> s_mul_ext ns s"
proof -
  have "(B, C) \<in> ns_mul_ext ns s" using assms(1) assms(3) order_pair.axioms(1) pre_order_pair.refl_NS supseteq_imp_ns_mul_ext by blast 
  then show ?thesis by (metis assms(1) assms(2) assms(3) order_pair.axioms(1) order_pair.mul_ext_order_pair pre_order_pair_def subset_mset_def supset_imp_s_mul_ext transD) 
qed


lemma vars_term_ms_simp[simp]:
  fixes s :: "('f,'v) term"
  shows "vars_term_ms (Fun f [s]) = vars_term_ms s"
  by (induct s) auto

lemma vars_term_not_empty_imp_no_constant:
  assumes "vars_term_ms (Fun f ss) \<noteq> {#}"
  shows "length ss > 0"
  using assms
  by (cases "length ss = 0") auto

lemma actop_impl_subterm:
  assumes "x \<in># actop f s"
  shows "actop f s = {#s#} \<or> s \<rhd> x"
  using assms
proof (induct s)
  case (Var x)
  then show ?case by auto
next
  case (Fun g ss)
  then show ?case using actop_non_Bin[of ss f g]
    apply auto
    by (metis \<open>\<forall>u v. ss \<noteq> [u, v] \<Longrightarrow> actop f (Fun g ss) = {#Fun g ss#}\<close> actop.simps(1) actop_mset_elem_subterm)
qed

fun vars_ctxt_ms :: "('f,'v)ctxt \<Rightarrow> 'v multiset"
  where
    "vars_ctxt_ms Hole = {#}" |
    "vars_ctxt_ms (More f ss C ts) =
      \<Sum>\<^sub># (mset (map vars_term_ms ss)) +
      vars_ctxt_ms C +
      \<Sum>\<^sub># (mset (map vars_term_ms ts))"

lemma vars_ctxt_ms:
  shows "vars_term_ms C\<langle>s\<rangle> = vars_ctxt_ms C + vars_term_ms s"
  by (induct C) auto

lemma vars_ms_closed_under_ctxt:
  fixes s :: "('f,'v) term"
  assumes "vars_term_ms s = vars_term_ms t"
  shows "vars_term_ms C\<langle>s\<rangle> = vars_term_ms C\<langle>t\<rangle>"
  using assms vars_ctxt_ms[of C s] vars_ctxt_ms[of C t] by (auto)

lemma vars_ms_closed_under_sub:
  assumes "vars_term_ms s = vars_term_ms t"
  shows "vars_term_ms (s \<cdot> \<sigma>) = vars_term_ms (t \<cdot> \<sigma>)"
  using assms vars_term_ms_subst_mono[of s t \<sigma>] vars_term_ms_subst_mono[of t s \<sigma>] by auto

lemma ac_terms_eq_root:
  assumes "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
  shows   "root s = root t"
  using AC_class_abstract_aocnf.aocnf_roots aocnf_abstract_aocnf.acconv_imp_nf_eq assms by blast

lemma ac_rule_share_vars:
  assumes "(l, r) \<in> AC_rules AC AC"
  shows "vars_term_ms l = vars_term_ms r"
  using assms
  by (auto simp: A_rules_def C_rules_def AC_rules_def)

lemma ac_step_share_vars:
  assumes "(s, t) \<in> (acstep AC AC)"
  shows "vars_term_ms s = vars_term_ms t"
  using assms
proof (cases)
  case (rstep C \<sigma> l r)
  then show ?thesis using ac_rule_share_vars[of l r]
    by (auto simp: vars_term_ms_subst_mono vars_ms_closed_under_ctxt vars_ms_closed_under_sub ctxt_closed_acstep_symcl)
qed

lemma ac_converse_share_vars:
  assumes "(s, t) \<in> (acstep AC AC)\<inverse>"
  shows "vars_term_ms s = vars_term_ms t"
  using assms
proof 
  have "(t, s) \<in> acstep AC AC" using assms converseD[of s t] by auto
  then show ?thesis using assms ac_step_share_vars[of t s] by (auto)
qed

lemma ac_symcl_share_vars:
  fixes s ::"('f, 'v) term"
  assumes "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>"
  shows "vars_term_ms s = vars_term_ms t"
  using assms ac_step_share_vars ac_converse_share_vars by auto

lemma ac_terms_share_vars:
  assumes "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "vars_term_ms s = vars_term_ms t"
  using assms
  unfolding conversion_def by induction (auto simp:ac_symcl_share_vars)


lemma acstep_closed_subst:
  fixes s ::"('f, 'v) term"
    and \<sigma> ::"'v \<Rightarrow> ('f, 'v) term"
  assumes "(s, t) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
  using assms conversion_subst_closed by auto

lemma ac_vars_eq:
  assumes "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
    and "is_Var s"
    and "is_Var t"
  shows "s = t"
  using assms
proof -
  obtain x where term_s:"s = Var x" using assms(2) by blast 
  obtain y where term_t:"t = Var y" using assms(3) by blast 
  have "vars_term_ms s = vars_term_ms t" using assms(1) ac_terms_share_vars[of s t] by blast
  thus ?thesis by (simp add: term_s term_t)
qed

lemma ac_share_vars:
  shows "(Var x, Var y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> x = y"
  using ac_vars_eq by blast

lemma not_ac_imples_not_aceq_actop_ms:
  assumes "(s, t) \<notin> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
    and "f \<in> AC"
  shows "image_mset (acnf AC) (actop f s) \<noteq> image_mset (acnf AC) (actop f t)"
  using assms by (induct s) (meson AC_class_abstract_acnf.acnf_eq_intro acconv_iff)+

lemma ac_no_ac_root_on_args_list:
  assumes "(Fun f ss, Fun f ts) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
    and "f \<notin> AC"
  shows "map (acnf AC) ss = map (acnf AC) ts"
proof -
  have eq:"acnf AC (Fun f ss) = acnf AC (Fun f ts)" by (meson acnf_abstract_acnf.acconv_imp_nf_eq assms(1))
  then show ?thesis by (metis (no_types, lifting) acnf.simps(3) acnf_code(2) acterm.inject(2) assms(2) list.simps(8) list.simps(9)) 
qed

lemma ac_arity_not_two_impl_acnf_eq_on_args_list:
  assumes "(Fun f ss, Fun f ts) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
    and "length ss \<noteq> 2"
  shows "map (acnf AC) ss = map (acnf AC) ts"
proof -
  have eq:"acnf AC (Fun f ss) = acnf AC (Fun f ts)" by (meson acnf_abstract_acnf.acconv_imp_nf_eq assms(1))
  thus ?thesis
  proof(cases "(Fun f ss)" rule:acnf.cases)
    case (1 x)
    then show ?thesis using eq by blast 
  next
    case (2 g u v)
    show ?thesis using eq assms(2) 2 by auto 
  next
    case (3 f ts)
    then show ?thesis using eq
      by (smt One_nat_def Suc_eq_plus1 ac_terms_eq_root acnf.simps(3) acterm.inject(2) assms(1) assms(2) list.size(3) list.size(4) nat_1_add_1 root.simps(2) root_Some term.inject(2)) 
  qed
qed

lemma ac_arity_not_two_impl_ac_terms_on_args_list:
  assumes "(Fun f ss, Fun f ts) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
    and "f \<notin> AC \<or> length ss \<noteq> 2"
  shows "i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
proof
  assume a:"i < length ss"
  have eq:"map (acnf AC) ss = map (acnf AC) ts" using ac_arity_not_two_impl_acnf_eq_on_args_list ac_no_ac_root_on_args_list assms by metis 
  then show "(ss ! i, ts ! i) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>)\<^sup>*" by (meson a acconv_iff conversionE map_nth_conv) 
qed

definition filter_fun :: "('f, 'v) Term.term multiset \<Rightarrow> (('f \<times> nat) \<Rightarrow> ('f \<times> nat) \<Rightarrow> bool) \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) Term.term multiset"
  where
    "filter_fun T P f \<equiv> filter_mset (\<lambda> x. (case x of (Var _) \<Rightarrow> False | (Fun g ts) \<Rightarrow> P (g, length ts) f)) T"

declare filter_fun_def[simp]

(*abbreviation of filtering *)
abbreviation filter_var :: "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset"
  where
    "filter_var T \<equiv> filter_mset (\<lambda> x. is_Var x) T"

notation filter_var ("_ \<restriction>\<^sub>v" [200] 100)


lemma filter_fun_add_mset_cancel [simp]:
  assumes "\<not> P (g, length gs) f"
    and "s = Fun g gs" 
  shows "filter_fun (add_mset s S) P f = filter_fun S P f"
  using assms by (induct S) auto

lemma filter_fun_var_cancel [simp]:
  assumes "is_Var s" 
  shows "filter_fun (add_mset s S) P f = filter_fun S P f"
  using assms by (induct S) auto


lemma filter_var_of_fun_empty:
  assumes "\<And> x. x \<in># S \<and> is_Fun x"
  shows "S\<restriction>\<^sub>v = {#}"
  using assms by simp

lemma filter_fun_of_var_empty:
  assumes "\<And> x. x \<in># T \<and> is_Var x"
  shows "filter_fun T P f = {#}"
  using assms by blast

lemma filter_fun_distj_filter_var:
  shows "S\<restriction>\<^sub>v \<inter># filter_fun T P f = {#}"
  by (simp add: disjunct_not_in term.case_eq_if)



lemma image_mset_multpw_cong:
  assumes "image_mset f S = image_mset f T"
  shows "(S,T) \<in> multpw {(x,y). f x = f y}"
  using assms 
proof(induct S arbitrary: T)
  case empty
  then show ?case by simp 
next
  case (add x S)
  then show ?case using multpw.simps[of "add_mset x S" T "{(x,y). f x = f y}"]
    by (smt case_prodI image_mset_add_mset mem_Collect_eq msed_map_invR)
qed








lemma acstep_on_var_impl_var_eq:
  assumes "(s,t) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
    and "s = Var x"
  shows "t = Var x"
  using assms by (metis ac_terms_eq_root ac_vars_eq is_FunE root.simps(2) root_Some term.distinct(1)) 

lemma actop_size_1_r_simp [simp]:
  shows "size (actop f s) + size (actop f t) = Suc 0 \<longleftrightarrow> False"
  by (metis image_actop_nonempty image_mset_is_empty_iff one_is_add size_eq_0_iff_empty) 

lemma actop_size_1_l_simp [simp]:
  shows "Suc 0 = size (actop f s) + size (actop f t) \<longleftrightarrow> False"
  by (metis image_actop_nonempty image_mset_is_empty_iff one_is_add size_eq_0_iff_empty) 

lemma ac_var_fun_false [simp]:
  shows "(Var x, Fun f ts) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> False"
  by (metis acstep_on_var_impl_var_eq term.distinct(1))

lemma actop_sum_single_false [simp]:
  shows "actop f ta + actop f ua = {#u#} \<longleftrightarrow> False"
  by (metis image_actop_nonempty image_mset_empty non_empty_plus_non_empty_not_single)

lemma singl_actop_sum_false [simp]:
  shows "({#s#}, actop f ta + actop f ua) \<in> multpw ns \<longleftrightarrow> False"
  by (metis One_nat_def actop_size_1_l_simp multpw_impl_eq_size size_single size_union)

lemma multpw_single_simp [simp]:
  shows "({#s#}, {#t#}) \<in> multpw ns \<longleftrightarrow> (s, t) \<in> ns"
  by (auto simp add: add) (metis (full_types) add_mset_eq_single multpw_split1R)

lemma multpw_actop_simp :
  assumes "actop f s = {#u#}"
  shows "({#u#}, actop f t) \<in> multpw ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) \<longleftrightarrow> (s, t) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
  using assms Bin_cases[of s] Bin_cases[of t] apply (auto split:if_splits)
   apply (metis AC_class_abstract_aocnf.aocnf_Fun_roots aocnf_abstract_aocnf.acconv_imp_nf_eq)
  by (smt ac_terms_eq_root length_0_conv length_Cons length_Suc_conv root.simps(2) root_Some term.inject(2))

lemma acstep_impl_actop_multpw:
  assumes "(s, t) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)" and "f \<in> AC"
  shows "(actop f s, actop f t) \<in> multpw ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
proof -
  have "image_mset (acnf AC) (actop f s) = image_mset (acnf AC) (actop f t)"
    by (metis acnf_abstract_acnf.acconv_imp_nf_eq assms(1) assms(2) image_mset_acnf_actop)
  then have "(actop f s, actop f t) \<in> multpw {(x, y). (acnf AC) x = (acnf AC) y}" using image_mset_multpw_cong by blast  
  then show ?thesis using acconv_iff by (smt Collect_cong Collect_mem_eq case_prodE case_prodI2) 
qed

lemma actop_multpw_impl_acnf_actop:
  assumes "(actop f s, actop f t) \<in> multpw ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
  shows "image_mset (acnf AC) (actop f s) = image_mset (acnf AC) (actop f t)"
  using assms(1)
proof -
  let ?ac = "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
  from assms(1) obtain sl tl where wit: "mset sl = actop f s \<and> mset tl = actop f t \<and> length sl = length tl \<and> length tl = size (actop f s) \<and> (\<forall> i < length tl. (sl ! i, tl ! i) \<in> ?ac)"
    by (metis multpw_listE size_mset)
  then have "map (acnf AC) sl = map (acnf AC) tl" by (metis acnf_abstract_acnf.acconv_imp_nf_eq nth_map_conv)
  then show ?thesis using wit by (metis mset_map) 
qed

lemma actop_multpw_impl_acstep:
  assumes "(actop f s, actop f t) \<in> multpw ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)" and "f \<in> AC"
  shows "(s, t) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
  using actop_multpw_impl_acnf_actop[OF assms(1)] by (metis assms(2) not_ac_imples_not_aceq_actop_ms) 

locale prec =
  fixes pr_strict :: "('f \<times> nat) \<Rightarrow> ('f \<times> nat) \<Rightarrow> bool"
begin

(*
  Note that we use the following orientation order
  x > y \<longleftrightarrow> pr_strict x y
  x < y \<longleftrightarrow> pr_strict y x
*)
abbreviation filter_func_less :: "('f, 'v) term multiset \<Rightarrow> 'f \<times> nat \<Rightarrow>('f, 'v) term multiset"
  where
    "filter_func_less T f \<equiv> filter_fun T (\<lambda> x y. pr_strict y x) f"

abbreviation filter_func_nless :: "('f, 'v) term multiset \<Rightarrow> 'f \<times> nat \<Rightarrow>('f, 'v) term multiset"
  where
    "filter_func_nless T f \<equiv> filter_fun T (\<lambda> x y. \<not> pr_strict y x) f"

notation filter_func_less ("_ \<restriction>\<^sub>p _" [200, 200] 100)
notation filter_func_nless ("_ \<restriction>\<^sub>n _" [200, 200] 100)

abbreviation filtered_less_rel_s :: "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset \<Rightarrow> 'f \<times> nat \<Rightarrow> ('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel \<Rightarrow> bool"
  where
    "filtered_less_rel_s S T f ns_ord s_ord \<equiv> (S\<restriction>\<^sub>p f, T\<restriction>\<^sub>p f) \<in> s_mul_ext ns_ord s_ord"

abbreviation filtered_nless_rel_s ::  "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset \<Rightarrow> 'f \<times> nat \<Rightarrow> ('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel \<Rightarrow> bool"
  where
    "filtered_nless_rel_s  S T f ns_ord s_ord \<equiv> (S\<restriction>\<^sub>n f, T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)) \<in> s_mul_ext ns_ord s_ord"

abbreviation filtered_nless_rel_ns :: "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset \<Rightarrow> 'f \<times> nat \<Rightarrow> ('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel \<Rightarrow> bool"
  where
    "filtered_nless_rel_ns S T f ns_ord s_ord \<equiv> (S\<restriction>\<^sub>n f, T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)) \<in> ns_mul_ext ns_ord s_ord"

definition ac_case_filtered_rel
  where
    "ac_case_filtered_rel S T f ns_rel s_rel \<equiv> filtered_nless_rel_s S T f ns_rel s_rel \<or>
           filtered_nless_rel_ns S T f ns_rel s_rel \<and> size S > size T \<or>
           filtered_nless_rel_ns S T f ns_rel s_rel \<and> size S = size T \<and>
           filtered_less_rel_s S T f ns_rel s_rel"

lemma ac_case_filtered_rel_cases:
  shows "ac_case_filtered_rel U V g ns' s' \<Longrightarrow>
         (\<And> S T f ns s. U = S \<Longrightarrow> V = T \<Longrightarrow> g = f \<Longrightarrow> ns' = ns \<Longrightarrow> s' = s \<Longrightarrow> 
              filtered_nless_rel_s S T f ns s \<Longrightarrow> P) \<Longrightarrow>
         (\<And> S T f ns s. U = S \<Longrightarrow> V = T \<Longrightarrow> g = f \<Longrightarrow> ns' = ns \<Longrightarrow> s' = s \<Longrightarrow>
              filtered_nless_rel_ns S T f ns s \<Longrightarrow> size S > size T \<Longrightarrow> P) \<Longrightarrow>
         (\<And> S T f ns s. U = S \<Longrightarrow> V = T \<Longrightarrow> g = f \<Longrightarrow> ns' = ns \<Longrightarrow> s' = s \<Longrightarrow>
            filtered_nless_rel_ns S T f ns s \<Longrightarrow> size S = size T \<Longrightarrow>
            filtered_less_rel_s S T f ns s \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding ac_case_filtered_rel_def by meson 


lemma ac_case_filtered_rel_s_mono[mono]:
  assumes "\<And> x y. s x y \<longrightarrow> s' x y"
  shows "ac_case_filtered_rel S T f ns {(u, v). s u v} \<longrightarrow> ac_case_filtered_rel S T f ns {(u, v). s' u v}"
  using s_mul_ext_ord_s[OF assms, of _ _ ns] ns_mul_ext_ord_s[OF assms, of _ _ ns]
  by (auto simp add: ac_case_filtered_rel_def simp del: filter_fun_def)

lemma ac_case_filtered_rel_cong:
  assumes "S = V"
    and "T = U"
    and "\<And> x x'. x \<in># V \<Longrightarrow> x' \<in># U \<Longrightarrow> (x, x') \<in> s \<Longrightarrow> (x, x') \<in> s'"
    and "\<And> x x'. x \<in># V \<Longrightarrow> x' \<in># U \<Longrightarrow> (x, x') \<in> ns \<Longrightarrow> (x, x') \<in> ns'"
  shows "ac_case_filtered_rel S T f ns s \<Longrightarrow> ac_case_filtered_rel V U f ns' s'"
proof -
  assume "ac_case_filtered_rel S T f ns s"
  then have ass: "ac_case_filtered_rel V U f ns s" using assms by auto
  have str: "\<And> x x'. x \<in># V \<restriction>\<^sub>n f \<Longrightarrow> x' \<in># U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - V \<restriction>\<^sub>v)  \<Longrightarrow> (x, x') \<in> s \<Longrightarrow> (x, x') \<in> s'"
    using assms(3) in_diffD by fastforce
  have nstr: "\<And> x x'. x \<in># V \<restriction>\<^sub>n f \<Longrightarrow> x' \<in># U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - V \<restriction>\<^sub>v)  \<Longrightarrow> (x, x') \<in> ns \<Longrightarrow> (x, x') \<in> ns'"
    using assms(4) in_diffD by fastforce 
  from ac_case_filtered_rel_cases[OF ass]
  show "ac_case_filtered_rel V U f ns' s'"
  proof cases
    case (1 S T f ns s)
    then have "(S \<restriction>\<^sub>n f, T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> s_mul_ext ns' s'"
      using s_mul_ext_local_mono[OF _ _ 1(6), of ns' s'] 
      using str nstr by auto
    then show ?thesis unfolding ac_case_filtered_rel_def by (auto simp add: 1)
  next
    case (2 S T f ns s)
    then have "(S \<restriction>\<^sub>n f, T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> ns_mul_ext ns' s'"
      using ns_mul_ext_local_mono[OF _ _ 2(6), of ns' s']
      using str nstr by auto
    then show ?thesis unfolding ac_case_filtered_rel_def by (auto simp add: 2)
  next
    case (3 S T f ns s)
    then have "filtered_less_rel_s V U f ns' s'"
      using s_mul_ext_local_mono[OF _ _ 3(8), of ns' s'] assms(3, 4) by auto    
    then show ?thesis
      using ns_mul_ext_local_mono[OF _ _ 3(6), of ns' s']
      using str nstr  unfolding ac_case_filtered_rel_def by (auto simp add: 3)
  qed
qed


lemma filter_unions_eq:
  shows "S = S\<restriction>\<^sub>n f + S\<restriction>\<^sub>p f + S\<restriction>\<^sub>v"
  by (induct S) (auto simp add: term.case_eq_if)

lemma multpw_root_pres_impl_filter_fun_multpw:
  assumes "(S, T) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
  shows "(filter_fun S R f, filter_fun T R f) \<in> multpw ns"
  using assms by (induct rule:multpw.induct, auto simp add: multpw.add split: term.splits) fastforce+

lemma multpw_root_pres_impl_filter_var_eq:
  assumes "(S, T) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
  shows "S\<restriction>\<^sub>v = T\<restriction>\<^sub>v"
  using assms by (induct rule:multpw.induct) (auto elim!: root.elims) 



lemma subset_rel_filterd_comb:
  shows "T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v) \<subseteq># T"
  using  filter_unions_eq[of T] by (auto simp del: filter_fun_def)
    (metis diff_subset_eq_self filter_unions_eq mset_subset_eq_add_left mset_subset_eq_mono_add)

(** Section for irreflexivity  **)

lemma s_mul_irrefl [simp]:
  assumes "ns O s \<subseteq> s"
    and "s O ns \<subseteq> s"
    and irr: "locally_irrefl s S"
    and tr: "trans s"
  shows "(S, S) \<in> (s_mul_ext ns s) = False"
proof
  let ?ns = "ns\<^sup>*"
  assume "(S, S) \<in> s_mul_ext ns s"
  then have ass: "(S, S) \<in> s_mul_ext (ns\<^sup>*) s" using s_mul_ext_mono[of ns "ns\<^sup>*" s s] by auto
  from assms have "?ns O s \<subseteq> s" and "s O ?ns \<subseteq> s" apply (simp add: compat_tr_compat)
    by (simp add: assms(1, 2) compat_tr_compat compat_pair.S_O_rtrancl_NS(1) compat_pair.intro)
  then have comp_r: "s\<inverse> O ?ns\<inverse> \<subseteq> s\<inverse>" and comp_l: "?ns\<inverse> O s\<inverse> \<subseteq> s\<inverse>" by auto
  then have mul: "(S, S) \<in> (mult2_s ((ns\<^sup>*)\<inverse>) (s\<inverse>))\<inverse>" 
    using ass mult2_s_eq_mult2_s_alt[OF comp_l] tr refl_rtrancl
    unfolding s_mul_ext_def using refl_rtrancl by auto
  have "({#}, {#}) \<notin> mult2_s (?ns\<inverse>) (s\<inverse>)"
    by (simp add: mult2_s_def multpw_converse peak_iff)
  then show False using  mul mult2_s_locally_cancel[OF comp_r comp_l, of "{#}" S "{#}"] irr tr
    by (auto simp: multpw_converse peak_iff locally_irrefl_def refl_rtrancl trans_rtrancl) 
qed auto

lemma ac_case_filtered_rel_irrefl [simp]:
  assumes "ns O s \<subseteq> s"
    and "s O ns \<subseteq> s"
    and irr: "locally_irrefl s S"
    and tr: "trans s"
  shows "ac_case_filtered_rel S S f ns s = False"
proof -
  from s_mul_irrefl[OF assms(1-4)] show ?thesis unfolding irrefl_def ac_case_filtered_rel_def
    by auto (meson assms(1, 2) irr locally_irrefl_def mset_subset_eqD multiset_filter_subset prec.s_mul_irrefl tr)+ 
qed

(** end irreflexivity section **)

lemma filter_fun_add_dist [simp]:
  shows "filter_fun (T + U) P f = filter_fun T P f + filter_fun U P f"
  by auto

lemma filter_fun_minus_dist [simp]:
  shows "filter_fun (T - U) P f = filter_fun T P f - filter_fun U P f"
  by auto

lemma filter_fun_par [simp]:
  shows "filter_fun T P f + filter_var U - filter_var V = filter_fun T P f + (filter_var U - filter_var V)"
  by (metis filter_fun_distj_filter_var multiset_inter_commute multiset_union_diff_commute union_commute) 

lemma filter_var_dist:
  shows "(S - U)\<restriction>\<^sub>v = S\<restriction>\<^sub>v - U\<restriction>\<^sub>v"
  using filter_diff_mset by auto

declare filter_fun_def[simp del]

lemma ac_case_closed_under_mset_union:
  assumes "ac_case_filtered_rel S T f ns_rel s_rel "
    and "order_pair s_rel ns_rel"
  shows "ac_case_filtered_rel (S + U) (T + U) f ns_rel s_rel"
proof -
  have sub:"T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v) \<subseteq># T" using subset_rel_filterd_comb by (simp add: filter_fun_def)
  have U_dist:"(T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)) + U\<restriction>\<^sub>n f = (T\<restriction>\<^sub>n f + U\<restriction>\<^sub>n f) + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)"
    using union_assoc union_commute by smt 
  have Var_dist:"(T + U)\<restriction>\<^sub>v - (S + U)\<restriction>\<^sub>v = T\<restriction>\<^sub>v - S\<restriction>\<^sub>v" using filter_union_mset add_diff_cancel_right by auto
  consider (a) "filtered_nless_rel_s S T f ns_rel s_rel "|
    (b) "filtered_nless_rel_ns S T f ns_rel s_rel  \<and> size T < size S"|
    (c) "filtered_nless_rel_ns S T f ns_rel s_rel  \<and> size S = size T \<and>
                  filtered_less_rel_s S T f ns_rel s_rel"
    using assms unfolding ac_case_filtered_rel_def by blast
  then show ?thesis
  proof cases
    case a
    then have "(S\<restriction>\<^sub>n f + U\<restriction>\<^sub>n f, (T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)) + U\<restriction>\<^sub>n f) \<in> s_mul_ext ns_rel s_rel"
      using s_mul_ext_union_compat[of "S\<restriction>\<^sub>n f" "T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)" ns_rel s_rel "U\<restriction>\<^sub>n f"] assms(2) pre_order_pair_def r_lr  order_pair.axioms(1) by blast 
    then show ?thesis using U_dist Var_dist unfolding ac_case_filtered_rel_def by auto
  next
    case b
    then have "(S\<restriction>\<^sub>n f + U\<restriction>\<^sub>n f, (T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)) + U\<restriction>\<^sub>n f) \<in> ns_mul_ext ns_rel s_rel"
      using ns_mul_ext_union_compat[of "S\<restriction>\<^sub>n f" "T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)" ns_rel s_rel "U\<restriction>\<^sub>n f"] assms(2) pre_order_pair_def r_lr  order_pair.axioms(1) by blast 
    then have "filtered_nless_rel_ns (S + U) (T + U) f ns_rel s_rel" using U_dist Var_dist by auto
    moreover have "size (S + U) > size (T + U)" using b by auto
    ultimately show ?thesis unfolding ac_case_filtered_rel_def by auto
  next
    case c
    then have r_vers:"(S\<restriction>\<^sub>p f + U\<restriction>\<^sub>p f, T\<restriction>\<^sub>p f + U\<restriction>\<^sub>p f) \<in> s_mul_ext ns_rel s_rel"
      using s_mul_ext_union_compat assms(2) pre_order_pair_def r_lr order_pair.axioms(1) by blast
    from c have "(S\<restriction>\<^sub>n f + U\<restriction>\<^sub>n f, (T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)) + U\<restriction>\<^sub>n f) \<in> ns_mul_ext ns_rel s_rel"
      using ns_mul_ext_union_compat[of "S\<restriction>\<^sub>n f" "T\<restriction>\<^sub>n f + (T\<restriction>\<^sub>v - S\<restriction>\<^sub>v)" ns_rel s_rel "U\<restriction>\<^sub>n f"] assms(2) pre_order_pair_def r_lr order_pair.axioms(1) by blast 
    moreover have "size (S + U) = size (T + U)" using c by auto 
    ultimately show ?thesis using r_vers U_dist Var_dist unfolding ac_case_filtered_rel_def by auto
  qed
qed

lemma filtered_nless_rel_s:
  assumes "order_pair s_rel ns_rel"
    and "\<forall>y. y \<in># M \<longrightarrow> SN_on s_rel {y}"
  shows "SN_on {(S,T). filtered_nless_rel_s S T h ns_rel s_rel} {M}"
proof (rule ccontr)
  let ?cond = "\<lambda> S T. filtered_nless_rel_s S T h ns_rel s_rel"
  assume a:"\<not> SN_on {(S,T). ?cond  S T} {M}"
  then obtain f where f: "f 0 = M" "\<And> n :: nat. ?cond (f n) (f (Suc n))" unfolding SN_defs by auto
  then have "\<And> n ::nat. (f n\<restriction>\<^sub>n h + f n\<restriction>\<^sub>v,(f (Suc n)\<restriction>\<^sub>n h + (f (Suc n)\<restriction>\<^sub>v - f n\<restriction>\<^sub>v)) + f n\<restriction>\<^sub>v) \<in> s_mul_ext ns_rel s_rel"
    by (metis add_cancel_left_left assms(1) diff_union_cancelL mset_subset_eq_exists_conv ns_mul_ext_rhs_cancel s_ns_mul_ext_union_compat) 
  then have sn:"\<And> n ::nat. (f n\<restriction>\<^sub>n h + f n\<restriction>\<^sub>v,f (Suc n)\<restriction>\<^sub>n h + f (Suc n)\<restriction>\<^sub>v) \<in> s_mul_ext ns_rel s_rel"
    using s_mul_ext_subset_trans[OF assms(1)] by (metis diff_union_cancelR subset_eq_diff_conv subset_relation) 
  let ?f = "\<lambda> x. f x\<restriction>\<^sub>n h + f x\<restriction>\<^sub>v" 
  have "\<forall> y. y \<in># M\<restriction>\<^sub>n h + M\<restriction>\<^sub>v \<longrightarrow> SN_on s_rel {y}" by (metis assms(2) filter_unions_eq union_iff)
  from SN_s_mul_ext_strong[OF assms(1) this] have "SN_on (s_mul_ext ns_rel s_rel) {M\<restriction>\<^sub>n h + M\<restriction>\<^sub>v}" by auto
  then show False using sn chain_imp_not_SN_on[of ?f "s_mul_ext ns_rel s_rel" 0] f
    by auto
qed

(* Proof of following lemmas have the same scheme, therefore generalize 
   at the moment copy pasted and adapted for fast results


  This can be done quick by using the added locally transitive lemmas of s ns ect..

  then lemma equal_var_set_mult_pw becomes obsolete
*)

lemma equal_var_set_mult_pw:
  assumes "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
  shows "(U \<restriction>\<^sub>v, U \<restriction>\<^sub>v) \<in> multpw ns"
proof (induct U)
  case (add x U)
  then show ?case
  proof (cases x)
    case (Var x1)
    then show ?thesis using multpw.add[of x x ns, OF _ add] assms(1, 2)
      by auto 
  qed auto 
qed auto 

lemma compat_left_filter_nless_strict:
  assumes "(S, T) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "locally_trans ns S T U"
    and "locally_compatible_l ns s S T U"
    and "filtered_nless_rel_s T U f ns s"
  shows "filtered_nless_rel_s S U f ns s"
  using assms 
proof -
  have var: "T \<restriction>\<^sub>v = S \<restriction>\<^sub>v" using assms(1-3) by (metis prec.multpw_root_pres_impl_filter_var_eq)
  from s_mul_extE[OF assms(6)] obtain A1 A2 B1 B2 where
    u:"T \<restriction>\<^sub>n f = A1 + A2" and v:"U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) = B1 + B2" and mul_pw:"(A1, B1) \<in> multpw ns" and a:"A2 \<noteq> {#}" and
    str:"(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  from multpw_root_pres_impl_filter_fun_multpw[OF assms(1, 2)]
  have "(S \<restriction>\<^sub>n f, T \<restriction>\<^sub>n f) \<in> multpw ns" by blast
  then obtain A1' A2' where s: "S \<restriction>\<^sub>n f = A1' + A2'" and mul_pw1: "(A1', A1) \<in> multpw ns" and mul_pw2: "(A2', A2) \<in> multpw ns"
    using u multpw_splitL by auto blast
  have subs: "A1' \<subseteq># S \<and> A2' \<subseteq># S \<and> A1 \<subseteq># T \<and> A2 \<subseteq># T \<and> B1 \<subseteq># U \<and> B2 \<subseteq># U"
    using u v s by (metis (no_types, lifting) mset_subset_eq_add_left mset_subset_eq_add_right subset_mset.order_trans subset_rel_filterd_comb)  
  {fix b
    assume ass: "b \<in># B2"
    then obtain a where a: "a \<in># A2 \<and> (a, b) \<in> s" using str ass by presburger 
    then obtain a' where a': "a' \<in># A2' \<and>  (a', a) \<in> ns" using mul_pw2 by (metis mset_add multpw_split1L union_single_eq_member)
    then have "a' \<in># A2' \<and> (a', b) \<in> s" using assms(5) s u v mul_pw2 subs unfolding locally_compatible_l_def
      by auto (meson a ass mset_subset_eqD)
    then have "\<exists> a'. a' \<in># A2' \<and> (a', b) \<in> s" by blast}
  then have str: "(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2' \<and> (a, b) \<in> s)" by auto
  moreover have "(A1', B1) \<in> multpw ns" using locally_trans_multpw[OF _ mul_pw1 mul_pw] subs assms(4)
    by (smt lt_trans_l subset_mset.le_iff_add)
  then show ?thesis using u v s mul_pw1 mul_pw2 mul_pw a var str by (metis multpw_emptyL s_mul_extI)
qed

lemma compat_left_filter_nless_weak:
  assumes "(S, T) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "locally_trans ns S T U"
    and "locally_compatible_l ns s S T U"
    and "filtered_nless_rel_ns T U f ns s"
  shows "filtered_nless_rel_ns S U f ns s"
proof -
  have var: "T \<restriction>\<^sub>v = S \<restriction>\<^sub>v" using assms(1-3) by (metis prec.multpw_root_pres_impl_filter_var_eq)
  from ns_mul_extE[OF assms(6)] obtain A1 A2 B1 B2 where
    u:"T \<restriction>\<^sub>n f = A1 + A2" and v:"U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) = B1 + B2" and mul_pw:"(A1, B1) \<in> multpw ns" and
    str:"(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  from multpw_root_pres_impl_filter_fun_multpw[OF assms(1, 2)]
  have "(S \<restriction>\<^sub>n f, T \<restriction>\<^sub>n f) \<in> multpw ns" by blast
  then obtain A1' A2' where s: "S \<restriction>\<^sub>n f = A1' + A2'" and mul_pw1: "(A1', A1) \<in> multpw ns" and mul_pw2: "(A2', A2) \<in> multpw ns"
    using u multpw_splitL by auto blast
  have subs: "A1' \<subseteq># S \<and> A2' \<subseteq># S \<and> A1 \<subseteq># T \<and> A2 \<subseteq># T \<and> B1 \<subseteq># U \<and> B2 \<subseteq># U"
    using u v s by (metis (no_types, lifting) mset_subset_eq_add_left mset_subset_eq_add_right subset_mset.order_trans subset_rel_filterd_comb) 
  {fix b
    assume ass: "b \<in># B2"
    then obtain a where a: "a \<in># A2 \<and> (a, b) \<in> s"
      using str ass by presburger
    then obtain a' where a': "a' \<in># A2' \<and>  (a', a) \<in> ns"
      using mul_pw2 by (metis mset_add multpw_split1L union_single_eq_member)
    then have "a' \<in># A2' \<and> (a', b) \<in> s"
      using assms(5) s u v mul_pw2 subs unfolding locally_compatible_l_def by auto (meson a ass mset_subset_eqD)
    then have "\<exists> a'. a' \<in># A2' \<and> (a', b) \<in> s" by blast}
  then have str: "(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2' \<and> (a, b) \<in> s)" by auto
  moreover have "(A1', B1) \<in> multpw ns" using locally_trans_multpw[OF _ mul_pw1 mul_pw] subs assms(4)
    by (smt lt_trans_l subset_mset.le_iff_add)
  then show "filtered_nless_rel_ns S U f ns s" using u v s mul_pw1 mul_pw2 mul_pw var str
    by (simp add: ns_mul_extI)
qed

lemma compat_left_filter_less_strict:
  assumes "(S, T) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "locally_trans ns S T U"
    and "locally_compatible_l ns s S T U"
    and "filtered_less_rel_s T U f ns s"
  shows "filtered_less_rel_s S U f ns s"
proof -
  have var: "T \<restriction>\<^sub>v = S \<restriction>\<^sub>v" using assms(1-3) by (metis prec.multpw_root_pres_impl_filter_var_eq)
  from s_mul_extE[OF assms(6)] obtain A1 A2 B1 B2 where
    u:"T \<restriction>\<^sub>p f = A1 + A2" and v:"U \<restriction>\<^sub>p f = B1 + B2" and mul_pw:"(A1, B1) \<in> multpw ns" and a:"A2 \<noteq> {#}" and
    str:"(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  from multpw_root_pres_impl_filter_fun_multpw[OF assms(1, 2)]
  have "(S \<restriction>\<^sub>p f, T \<restriction>\<^sub>p f) \<in> multpw ns" by blast
  then obtain A1' A2' where s: "S \<restriction>\<^sub>p f = A1' + A2'" and mul_pw1: "(A1', A1) \<in> multpw ns" and mul_pw2: "(A2', A2) \<in> multpw ns"
    using u multpw_splitL by auto blast
  have subs: "A1' \<subseteq># S \<and> A2' \<subseteq># S \<and> A1 \<subseteq># T \<and> A2 \<subseteq># T \<and> B1 \<subseteq># U \<and> B2 \<subseteq># U" using u v s
    by (metis (no_types, lifting) filter_fun_def mset_subset_eq_add_left mset_subset_eq_add_right multiset_filter_subset subset_mset.order_trans) 
  {fix b
    assume ass: "b \<in># B2"
    then obtain a where a: "a \<in># A2 \<and> (a, b) \<in> s" using str ass by presburger 
    then obtain a' where a': "a' \<in># A2' \<and>  (a', a) \<in> ns" using mul_pw2 by (metis mset_add multpw_split1L union_single_eq_member)
    then have "a' \<in># A2' \<and> (a', b) \<in> s" using assms(5) s u v mul_pw2 subs unfolding locally_compatible_l_def by auto (meson a ass mset_subset_eqD)
    then have "\<exists> a'. a' \<in># A2' \<and> (a', b) \<in> s" by blast}
  then have str: "(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2' \<and> (a, b) \<in> s)" by auto
  moreover have "(A1', B1) \<in> multpw ns" using locally_trans_multpw[OF _ mul_pw1 mul_pw] subs assms(4)
    by (smt lt_trans_l subset_mset.le_iff_add)
  then show ?thesis using u v s mul_pw1 mul_pw2 mul_pw a var str by (metis multpw_emptyL s_mul_extI)
qed

lemma compat_left:
  assumes "(S, T) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "locally_trans ns S T U"
    and "locally_compatible_l ns s S T U"
    and "ac_case_filtered_rel T U f ns s"
  shows "ac_case_filtered_rel S U f ns s"
  using compat_left_filter_nless_strict[OF assms(1-5), of f] assms
  using compat_left_filter_nless_weak[OF assms(1-5), of f]
  using compat_left_filter_less_strict[OF assms(1-5), of f] multpw_impl_eq_size[OF assms(1)]
  unfolding ac_case_filtered_rel_def by auto

(* Proof of following lemmas have the same scheme, therefore generalize 
   at the moment copy pasted and adapted for fast results


  This can be done quick by using the added locally transitive lemmas of s ns ect..

  then lemma equal_var_set_mult_pw becomes obsolete
*)

lemma compat_right_filter_nless_strict:
  assumes "(T, U) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
    and "locally_trans ns S T U"
    and "locally_compatible_r ns s S T U"
    and "filtered_nless_rel_s S T f ns s"
  shows "filtered_nless_rel_s S U f ns s"
proof -
  have var: "T \<restriction>\<^sub>v = U \<restriction>\<^sub>v" using assms(1-3) by (metis prec.multpw_root_pres_impl_filter_var_eq)
  from s_mul_extE[OF assms(7)] obtain A1 A2 B1 B2 where
    s:"S \<restriction>\<^sub>n f = A1 + A2" and t: "T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v) = B1 + B2" and mul_pw:"(A1, B1) \<in> multpw ns" and
    a:"A2 \<noteq> {#}" and str:"(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  from multpw_root_pres_impl_filter_fun_multpw[OF assms(1, 2)]
  have l: "(T \<restriction>\<^sub>n f , U \<restriction>\<^sub>n f) \<in> multpw ns" by blast
  moreover have "(T \<restriction>\<^sub>v - S \<restriction>\<^sub>v , U \<restriction>\<^sub>v - S \<restriction>\<^sub>v) \<in> multpw ns"
    using equal_var_set_mult_pw[OF assms(3, 4), of "U - S"] unfolding var by simp
  from multpw_add[OF l this] obtain A1' A2' where u: "U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - S \<restriction>\<^sub>v) = A1' + A2'" and 
    mul_pw1: "(B1, A1') \<in> multpw ns" and mul_pw2: "(B2, A2') \<in> multpw ns"
    using t multpw_splitL by (metis (no_types, lifting) multpw_splitR)
  have subs: "A1 \<subseteq># S \<and> A2 \<subseteq># S \<and> B1 \<subseteq># T \<and> B2 \<subseteq># T \<and> A1' \<subseteq># U \<and> A2' \<subseteq># U"
    using s t u by (metis (no_types, lifting) mset_subset_eq_add_left mset_subset_eq_add_right subset_mset.order_trans subset_rel_filterd_comb)  
  {fix b
    assume ass: "b \<in># A2'"
    then obtain b' where b': "b' \<in># B2 \<and> (b', b) \<in> ns" using mul_pw2
      by (metis mset_add multpw_split1L union_single_eq_member)
    then obtain a where a: "a \<in># A2 \<and> (a, b') \<in> s" using str by presburger
    then have "(a, b) \<in> s" using b' assms(6) subs unfolding locally_compatible_r_def
      by (meson ass mset_subset_eqD)
    then have "\<exists> a. a \<in># A2 \<and> (a, b) \<in> s" using a by blast}
  then have str: "(\<And>b. b \<in># A2' \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  moreover have "(A1, A1') \<in> multpw ns" using locally_trans_multpw[OF _ mul_pw mul_pw1] subs assms(5)
    by (smt lt_trans_l subset_mset.le_iff_add)
  then show ?thesis using s t u mul_pw1 mul_pw2 mul_pw a var str by (metis s_mul_extI)
qed


lemma compat_right_filter_nless_weak:
  assumes "(T, U) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
    and "locally_trans ns S T U"
    and "locally_compatible_r ns s S T U"
    and "filtered_nless_rel_ns S T f ns s"
  shows "filtered_nless_rel_ns S U f ns s"
proof -
  have var: "T \<restriction>\<^sub>v = U \<restriction>\<^sub>v" using assms(1-3) by (metis prec.multpw_root_pres_impl_filter_var_eq)
  from ns_mul_extE[OF assms(7)] obtain A1 A2 B1 B2 where
    s:"S \<restriction>\<^sub>n f = A1 + A2" and t: "T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v) = B1 + B2" and mul_pw:"(A1, B1) \<in> multpw ns" and
    str:"(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  from multpw_root_pres_impl_filter_fun_multpw[OF assms(1, 2)]
  have l: "(T \<restriction>\<^sub>n f , U \<restriction>\<^sub>n f) \<in> multpw ns" by blast
  moreover have "(T \<restriction>\<^sub>v - S \<restriction>\<^sub>v , U \<restriction>\<^sub>v - S \<restriction>\<^sub>v) \<in> multpw ns"
    using equal_var_set_mult_pw[OF assms(3, 4), of "U - S"] unfolding var by simp
  from multpw_add[OF l this] obtain A1' A2' where u: "U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - S \<restriction>\<^sub>v) = A1' + A2'" and 
    mul_pw1: "(B1, A1') \<in> multpw ns" and mul_pw2: "(B2, A2') \<in> multpw ns"
    using t by (metis (no_types, lifting) multpw_splitR)
  have subs: "A1 \<subseteq># S \<and> A2 \<subseteq># S \<and> B1 \<subseteq># T \<and> B2 \<subseteq># T \<and> A1' \<subseteq># U \<and> A2' \<subseteq># U"
    using s t u by (metis (no_types, lifting) mset_subset_eq_add_left mset_subset_eq_add_right subset_mset.order_trans subset_rel_filterd_comb)  
  {fix b
    assume ass: "b \<in># A2'"
    then obtain b' where b': "b' \<in># B2 \<and> (b', b) \<in> ns" using mul_pw2
      by (metis mset_add multpw_split1L union_single_eq_member)
    then obtain a where a: "a \<in># A2 \<and> (a, b') \<in> s" using str by presburger
    then have "(a, b) \<in> s" using b' assms(6) subs unfolding locally_compatible_r_def
      by (meson ass mset_subset_eqD)
    then have "\<exists> a. a \<in># A2 \<and> (a, b) \<in> s" using a by blast}
  then have str: "(\<And>b. b \<in># A2' \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  moreover have "(A1, A1') \<in> multpw ns" using locally_trans_multpw[OF _ mul_pw mul_pw1] subs assms(5)
    by (smt lt_trans_l subset_mset.le_iff_add)
  then show ?thesis using s t u mul_pw1 mul_pw2 mul_pw var str by (simp add: ns_mul_extI) 
qed


lemma compat_right_filter_less_strict:
  assumes "(T, U) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
    and "locally_trans ns S T U"
    and "locally_compatible_r ns s S T U"
    and "filtered_less_rel_s S T f ns s"
  shows "filtered_less_rel_s S U f ns s"
proof -
  have var: "T \<restriction>\<^sub>v = U \<restriction>\<^sub>v" using assms(1-3) by (metis prec.multpw_root_pres_impl_filter_var_eq)
  from s_mul_extE[OF assms(7)] obtain A1 A2 B1 B2 where
    s:"S \<restriction>\<^sub>p f = A1 + A2" and t: "T \<restriction>\<^sub>p f = B1 + B2" and mul_pw:"(A1, B1) \<in> multpw ns" and
    a:"A2 \<noteq> {#}" and str:"(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  from multpw_root_pres_impl_filter_fun_multpw[OF assms(1, 2)]
  have l: "(T \<restriction>\<^sub>p f , U \<restriction>\<^sub>p f) \<in> multpw ns" by blast
  then obtain A1' A2' where u: "U \<restriction>\<^sub>p f = A1' + A2'" and 
    mul_pw1: "(B1, A1') \<in> multpw ns" and mul_pw2: "(B2, A2') \<in> multpw ns"
    using t by (metis (no_types, lifting) multpw_splitR)
  have subs: "A1 \<subseteq># S \<and> A2 \<subseteq># S \<and> B1 \<subseteq># T \<and> B2 \<subseteq># T \<and> A1' \<subseteq># U \<and> A2' \<subseteq># U"
    using s t u by (metis (no_types, lifting) filter_fun_def mset_subset_eq_add_left mset_subset_eq_add_right multiset_filter_subset subset_mset.order_trans) 
  {fix b
    assume ass: "b \<in># A2'"
    then obtain b' where b': "b' \<in># B2 \<and> (b', b) \<in> ns" using mul_pw2
      by (metis mset_add multpw_split1L union_single_eq_member)
    then obtain a where a: "a \<in># A2 \<and> (a, b') \<in> s" using str by presburger
    then have "(a, b) \<in> s" using b' assms(6) subs unfolding locally_compatible_r_def
      by (meson ass mset_subset_eqD)
    then have "\<exists> a. a \<in># A2 \<and> (a, b) \<in> s" using a by blast}
  then have str: "(\<And>b. b \<in># A2' \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s)" by blast
  moreover have "(A1, A1') \<in> multpw ns" using locally_trans_multpw[OF _ mul_pw mul_pw1] subs assms(5)
    by (smt lt_trans_l subset_mset.le_iff_add)
  then show ?thesis using s t u mul_pw1 mul_pw2 mul_pw a var str by (metis s_mul_extI)
qed

lemma compat_right:
  assumes "(T, U) \<in> multpw ns"
    and "\<And> x y. (x, y) \<in> ns \<Longrightarrow> root x = root y"
    and "\<And> x y. (Var x, Var y) \<in> ns \<Longrightarrow> x = y"
    and "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
    and "locally_trans ns S T U"
    and "locally_compatible_r ns s S T U"
    and "ac_case_filtered_rel S T f ns s"
  shows "ac_case_filtered_rel S U f ns s"
  using compat_right_filter_nless_strict[OF assms(1-6), of f] assms
  using compat_right_filter_nless_weak[OF assms(1-6), of f]
  using compat_right_filter_less_strict[OF assms(1-6), of f] multpw_impl_eq_size[OF assms(1)]
  unfolding ac_case_filtered_rel_def by auto

lemma ns_s_help_lemma:
  assumes "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
  and "locally_trans ns S (T + U) (T + U)"
  and "locally_trans s S (T + U) (T + U)"
  and "locally_compatible_l ns s S (T + U) (T + U)"
  and "locally_compatible_r ns s S (T + U) (T + U)"
  and "(S \<restriction>\<^sub>n f, T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s" 
  and "(T \<restriction>\<^sub>n f, U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)) \<in> s_mul_ext ns s"
shows "(S \<restriction>\<^sub>n f, U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> s_mul_ext ns s"
proof -
  have "locally_trans ns (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v))"
    using assms(2) unfolding locally_trans_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  moreover have "locally_trans s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v))"
     using assms(3) unfolding locally_trans_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  moreover have "locally_compatible_l ns s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v))"
     using assms(4) unfolding locally_compatible_l_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  moreover have "locally_compatible_r ns s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v))"
     using assms(5) unfolding locally_compatible_r_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  ultimately have "(S \<restriction>\<^sub>n f,  U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> s_mul_ext ns s"
  using assms(1) ns_s_mul_ext_sum_trans[OF _ _ _ _ _ assms(6, 7)]
    unfolding locally_refl_def by blast 
  moreover have  "(U \<restriction>\<^sub>v - S \<restriction>\<^sub>v) \<subseteq># (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)" 
    using subset_relation by blast
  ultimately show ?thesis using s_mul_ext_cancelR le_iff_add union_assoc
    by (smt subset_mset.add_diff_inverse)
qed


lemma s_ns_help_lemma:
  assumes "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
  and "locally_trans ns S (T + U) (T + U)"
  and "locally_trans s S (T + U) (T + U)"
  and "locally_compatible_l ns s S (T + U) (T + U)"
  and "locally_compatible_r ns s S (T + U) (T + U)"
  and "(S \<restriction>\<^sub>n f, T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> s_mul_ext ns s" 
  and "(T \<restriction>\<^sub>n f, U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s"
shows "(S \<restriction>\<^sub>n f, U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> s_mul_ext ns s"
proof -
  have trn: "locally_trans ns (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v + T \<restriction>\<^sub>n f) (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v + (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)))"
    using assms(2) unfolding locally_trans_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  have trs: "locally_trans s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v + T \<restriction>\<^sub>n f) (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v + (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)))"
     using assms(3) unfolding locally_trans_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  have cl: "locally_compatible_l ns s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v + T \<restriction>\<^sub>n f) (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v + (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)))"
     using assms(4) unfolding locally_compatible_l_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  have cr: "locally_compatible_r ns s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v + T \<restriction>\<^sub>n f) (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v + (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)))"
     using assms(5) unfolding locally_compatible_r_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  have "(S \<restriction>\<^sub>n f, U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> s_mul_ext ns s"
    using assms(1, 6, 7) s_ns_mul_ext_sum_trans[OF _ trn trs cl cr]
    unfolding locally_refl_def by (auto simp add: ac_simps)  
  moreover have  "(U \<restriction>\<^sub>v - S \<restriction>\<^sub>v) \<subseteq># (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)" 
    using subset_relation by blast
  ultimately show ?thesis using s_mul_ext_cancelR le_iff_add union_assoc
    by (smt subset_mset.add_diff_inverse)
qed


lemma ns_ns_help_lemma:
  assumes "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
  and "locally_trans ns S (T + U) (T + U)"
  and "locally_trans s S (T + U) (T + U)"
  and "locally_compatible_l ns s S (T + U) (T + U)"
  and "locally_compatible_r ns s S (T + U) (T + U)"
  and "(S \<restriction>\<^sub>n f, T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s" 
  and "(T \<restriction>\<^sub>n f, U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s"
shows "(S \<restriction>\<^sub>n f, U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s"
proof -
  have trn: "locally_trans ns (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v))"
    using assms(2) unfolding locally_trans_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  have trs: "locally_trans s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v))"
     using assms(3) unfolding locally_trans_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  have cl: "locally_compatible_l ns s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v))"
     using assms(4) unfolding locally_compatible_l_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  have cr: "locally_compatible_r ns s (S \<restriction>\<^sub>n f) (T \<restriction>\<^sub>n f + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) (U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v))"
     using assms(5) unfolding locally_compatible_r_def by (metis filter_fun_def in_diffD multiset_partition union_iff) 
  have "(S \<restriction>\<^sub>n f, U \<restriction>\<^sub>n f + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s"
    using assms(1, 6, 7) ns_ns_mul_ext_sum_trans[OF _ trn trs cl cr]
    unfolding locally_refl_def by (auto simp add: ac_simps)  
  moreover have  "(U \<restriction>\<^sub>v - S \<restriction>\<^sub>v) \<subseteq># (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v) + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)" 
    using subset_relation by blast
  ultimately show ?thesis using ns_mul_ext_cancelR le_iff_add union_assoc
    by (smt subset_mset.add_diff_inverse)
qed


(*******************************             *************************)

lemma ac_case_trans:
  assumes "\<And> x y. Var x = Var y \<Longrightarrow> (x, y) \<in> ns"
    and "locally_trans ns S (T + U) (T + U)"
    and "locally_trans s S (T + U) (T + U)"
    and "locally_compatible_l ns s S (T + U) (T + U)"
    and "locally_compatible_r ns s S (T + U) (T + U)"
    and "ac_case_filtered_rel S T f ns s"
    and "ac_case_filtered_rel T U f ns s"
  shows "ac_case_filtered_rel S U f ns s"
proof -
  consider (1) "filtered_nless_rel_s S T f ns s"|
    (2) "filtered_nless_rel_ns S T f ns s \<and> size S > size T"|
    (3) "filtered_nless_rel_ns S T f ns s \<and> size S = size T \<and> filtered_less_rel_s S T f ns s"
    using assms(6) unfolding ac_case_filtered_rel_def by blast
  then show "ac_case_filtered_rel S U f ns s"
  proof cases
    case 1
    then show ?thesis using ns_s_help_lemma[OF assms(1 - 5) s_ns_mul_ext[OF 1]]
      using s_ns_help_lemma[OF assms(1 - 5) 1] assms(7) unfolding ac_case_filtered_rel_def by auto
  next
    case 2
    then show ?thesis using assms(7) ns_s_help_lemma[OF assms(1 - 5) conjunct1[OF 2]]
      using ns_ns_help_lemma[OF assms(1 - 5) conjunct1[OF 2]]
      by (cases rule: ac_case_filtered_rel_cases[OF assms(7)], auto)
        (simp add: ac_case_filtered_rel_def)+
    next
    case 3
    {assume ass:"filtered_less_rel_s T U f ns s"
      from assms(2-5) have "locally_trans ns S T U" "locally_trans s S T U"
        "locally_compatible_l ns s S T U" "locally_compatible_r ns s S T U"
        using lt_trans_l[of ns S "{#}" T U U T] lt_trans_l[of s S "{#}" T U U T]
              lcl_trans_l[of ns s S "{#}" T U U T] lcr_trans_l[of ns s S "{#}" T U U T]
        by (simp add: union_commute)+
      then have "locally_trans ns (S \<restriction>\<^sub>p f) (T \<restriction>\<^sub>p f) (U \<restriction>\<^sub>p f)"  "locally_trans s (S \<restriction>\<^sub>p f) (T \<restriction>\<^sub>p f) (U \<restriction>\<^sub>p f)"
        "locally_compatible_l ns s (S \<restriction>\<^sub>p f) (T \<restriction>\<^sub>p f) (U \<restriction>\<^sub>p f)" "locally_compatible_r ns s (S \<restriction>\<^sub>p f) (T \<restriction>\<^sub>p f) (U \<restriction>\<^sub>p f)"
        unfolding locally_trans_def locally_compatible_l_def locally_compatible_r_def
        by (metis filter_fun_def multiset_partition union_iff)+
      then have "filtered_less_rel_s S U f ns s"
       using s_s_mul_ext_locally_trans[OF _ _ _ _ conjunct2[OF conjunct2[OF 3]] ass] by auto}
    then show ?thesis using assms(7) 3 ns_s_help_lemma[OF assms(1 - 5) conjunct1[OF 3]]
      using ns_ns_help_lemma[OF assms(1 - 5) conjunct1[OF 3]]
      by (cases rule: ac_case_filtered_rel_cases[OF assms(7)], auto)
         (simp add: ac_case_filtered_rel_def)+
  qed
qed

(* Section for substitution closure *)
abbreviation sub_mset (infixl "\<cdot>#" 67)
  where
    "sub_mset M s \<equiv> image_mset (\<lambda> x. x \<cdot> s) M"

lemma sub_mset_dist:
  shows "(M + N) \<cdot># s = M \<cdot># s + N \<cdot># s" 
  using image_mset_union by blast


lemma s_mul_ext_pres_sub_closer:
  assumes "(U, V) \<in> s_mul_ext ns_rel s_rel"
    and "\<And> s t. s \<in># U \<Longrightarrow> t \<in># V \<Longrightarrow> (s,t) \<in> ns_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ns_rel"
    and "\<And> s t. s \<in># U \<Longrightarrow> t \<in># V \<Longrightarrow> (s,t) \<in> s_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> s_rel"
  shows "(U \<cdot># \<sigma>, V \<cdot># \<sigma>) \<in> s_mul_ext ns_rel s_rel"
  using assms(1)
proof (rule s_mul_extE)
  let ?f ="\<lambda> x. x \<cdot> \<sigma>"
  fix A1 A2 B1 B2
  assume u:"U = A1 + A2"
  assume v:"V = B1 + B2"
  assume mul_pw:"(A1, B1) \<in> multpw ns_rel"
  assume a:"A2 \<noteq> {#}"
  assume str:"(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s_rel)"
  have str_subs:"\<And> s t. s \<in># A2 \<Longrightarrow> t \<in># B2 \<Longrightarrow> (s,t) \<in> s_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> s_rel" 
    using u v mset_subset_eqD assms(3) by auto
  have ns_subs:"\<And> s t. s \<in># A1 \<Longrightarrow> t \<in># B1 \<Longrightarrow> (s,t) \<in> ns_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ns_rel" 
    using u v mset_subset_eqD assms(2) by auto
  have u_s:"U \<cdot># \<sigma> = A1 \<cdot># \<sigma> + A2 \<cdot># \<sigma>" using u by auto
  moreover have "V \<cdot># \<sigma> = B1 \<cdot># \<sigma> + B2 \<cdot># \<sigma>" using v by auto
  moreover have "(A1 \<cdot># \<sigma>, B1 \<cdot># \<sigma>) \<in> multpw ns_rel" using mul_pw multpw_map[of A1 B1 _ ?f ?f] ns_subs by auto 
  moreover have "A2 \<cdot># \<sigma> \<noteq> {#}" using a by auto
  moreover have "\<And>b. b \<in># B2 \<cdot># \<sigma> \<Longrightarrow> \<exists>a. a \<in># A2 \<cdot># \<sigma> \<and> (a, b) \<in> s_rel" using str_subs str by fastforce 
  ultimately show ?thesis using s_mul_extI by blast
qed

lemma ns_mul_ext_pres_sub_closer:
  assumes "(U, V) \<in> ns_mul_ext ns_rel s_rel"
    and "\<And> s t. s \<in># U \<Longrightarrow> t \<in># V \<Longrightarrow> (s,t) \<in> ns_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ns_rel"
    and "\<And> s t. s \<in># U \<Longrightarrow> t \<in># V \<Longrightarrow> (s,t) \<in> s_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> s_rel"
  shows "(U \<cdot># \<sigma>,V \<cdot># \<sigma>) \<in> ns_mul_ext ns_rel s_rel"
  using assms(1)
proof (rule ns_mul_extE)
  let ?f ="\<lambda> x. x \<cdot> \<sigma>"
  fix A1 A2 B1 B2
  assume u:"U = A1 + A2"
  assume v:"V = B1 + B2"
  assume mul_pw:"(A1, B1) \<in> multpw ns_rel"
  assume str:"(\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s_rel)"
  have str_subs:"\<And> s t. s \<in># A2 \<Longrightarrow> t \<in># B2 \<Longrightarrow> (s,t) \<in> s_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> s_rel" 
    using u v mset_subset_eqD assms(3) by auto
  have ns_subs:"\<And> s t. s \<in># A1 \<Longrightarrow> t \<in># B1 \<Longrightarrow> (s,t) \<in> ns_rel \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ns_rel" 
    using u v mset_subset_eqD assms(2) by auto
  have u_s:"U \<cdot># \<sigma> = A1 \<cdot># \<sigma> + A2 \<cdot># \<sigma>" using u by auto
  moreover have "V \<cdot># \<sigma> = B1 \<cdot># \<sigma> + B2 \<cdot># \<sigma>" using v by auto
  moreover have "(A1 \<cdot># \<sigma>, B1 \<cdot># \<sigma>) \<in> multpw ns_rel" using mul_pw multpw_map[of A1 B1 _ ?f ?f] ns_subs by auto 
  moreover have "\<And>b. b \<in># B2 \<cdot># \<sigma> \<Longrightarrow> \<exists>a. a \<in># A2 \<cdot># \<sigma> \<and> (a, b) \<in> s_rel" using str_subs str by fastforce 
  ultimately show ?thesis using ns_mul_extI by blast
qed

(*
    Section: Closed under substitution ac_case
*)

abbreviation actop_mset
  where
    "actop_mset f M \<equiv> \<Sum>\<^sub># (image_mset (\<lambda> x. actop f x) M)"

notation actop_mset ("\<nabla># _ _" [200, 200] 90)

lemma sub_flat_filter_unfold:
  fixes f :: 'f
  shows "filter_fun (actop f (s \<cdot> \<sigma>)) P (f, n) = filter_fun (actop f s) P (f, n) \<cdot># \<sigma> 
                  + filter_fun (\<nabla># f (actop f s\<restriction>\<^sub>v \<cdot># \<sigma>)) P (f, n)"
proof (induct s rule: subterm_induct)
  case (subterm s)
  show ?case using Bin_cases[of s] subterm
    by (auto simp add: filter_fun_def AC_class_abstract_aocnf.map_not_bin)+  
qed

lemma sub_flat_var_unfold:
  fixes f :: 'f
  shows "(actop f (s \<cdot> \<sigma>)) \<restriction>\<^sub>v = (\<nabla># f (actop f s \<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>v"
proof (induct s rule: subterm_induct)
  case (subterm s)
  show ?case using Bin_cases[of s] subterm
    by (auto simp add: filter_fun_def AC_class_abstract_aocnf.map_not_bin)+  
qed


lemma dist_subs_var_subset:
  shows "\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>) - \<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>) \<subseteq># \<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>)"
  by auto (metis (no_types) image_mset_union subset_eq_diff_conv subset_mset.dual_order.refl subset_mset.le_iff_add sum_mset.union) 

lemma sub_flat_var_subset:
  shows "(\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v - (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v \<subseteq># (\<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v"
  using dist_subs_var_subset by (metis multiset_filter_mono prec.filter_var_dist) 

lemma aux_strict_subs:
  assumes "(\<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>p (f, n) \<noteq> {#}"
shows "T \<restriction>\<^sub>n (f, n) \<cdot># \<sigma> + (\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) + ((\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v - (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v)
  \<subset># T \<restriction>\<^sub>n (f, n) \<cdot># \<sigma> + (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n (f, n) + (\<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>))" (is "?L \<subset># ?R")
proof -
  let ?U = "(T - S)\<restriction>\<^sub>v"
  have "(\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) \<subseteq># (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) + (\<nabla># f (?U \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n)"
    using dist_subs_var_subset[of f \<sigma> T S]
    by (metis (no_types, lifting) Diff_eq_empty_iff_mset diff_add_zero diff_diff_add_mset prec.filter_fun_minus_dist) 
  then have "(\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) \<subset># (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) + (\<nabla># f (?U \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n)  + (\<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>p (f, n)"
    using assms by (metis subset_mset.add_strict_increasing subset_mset.gr_zeroI union_commute)
  then show ?thesis using sub_flat_var_subset[of f \<sigma> T S] 
  by auto (smt filter_unions_eq subset_mset.add_less_cancel_right subset_mset.add_strict_mono subset_mset.dual_order.not_eq_order_implies_strict union_assoc)
qed

lemma aux_nstrict_subs:
  shows "T \<restriction>\<^sub>n (f, n) \<cdot># \<sigma> + (\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) + ((\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v - (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v)
  \<subseteq># T \<restriction>\<^sub>n (f, n) \<cdot># \<sigma> + (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n (f, n) + (\<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>))"
proof -
  let ?U = "(T - S)\<restriction>\<^sub>v"
  have "(\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) \<subseteq># (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) + (\<nabla># f (?U \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n)"
    using dist_subs_var_subset[of f \<sigma> T S]
    by (metis (no_types, lifting) Diff_eq_empty_iff_mset diff_add_zero diff_diff_add_mset prec.filter_fun_minus_dist) 
  then have "(\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) \<subseteq># (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n) + (\<nabla># f (?U \<cdot># \<sigma>)) \<restriction>\<^sub>n (f, n)  + (\<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>p (f, n)"
    using mset_subset_eq_add_left subset_mset.add_increasing2 subset_mset.le_add_same_cancel1 by blast 
  then show ?thesis using sub_flat_var_subset[of f \<sigma> T S]
    by auto (smt Diff_eq_empty_iff_mset add.right_neutral filter_diff_mset filter_unions_eq prec.filter_fun_par subset_eq_diff_conv union_assoc) 
qed

(** Subsection dealing with size distribution under substitution **)

lemma actop_mim_size:
  shows "1 \<le> size (actop f t)"
  by (cases t, auto)
     (metis actop_non_Bin actop_size_1_r_simp add.left_neutral le_zero_eq list.simps(3) not_less_eq_eq size_add_mset size_eq_0_iff_empty) 


abbreviation int_size
  where "int_size M \<equiv> int (size M)"

lemma subst_actop_size_eq:
  shows "int_size (actop f (s \<cdot> \<sigma>)) = int_size (actop f s\<restriction>\<^sub>n h) + int_size (actop f s\<restriction>\<^sub>p h) + int_size (\<nabla># f (actop f s\<restriction>\<^sub>v \<cdot># \<sigma>))"
proof (induct s)
  case (Fun g gs)
  then show ?case
  proof (cases "\<exists> t u. gs = [t, u]")
    case True
    then show ?thesis using Fun
      by auto (metis (no_types, lifting) One_nat_def add_cancel_left_right filter_single_mset filter_unions_eq is_FunI of_nat_add semiring_1_class.of_nat_simps(2) size_single size_union) 
  next
    case False
    then show ?thesis
      by auto (smt AC_class_abstract_aocnf.map_not_bin actop_non_Bin add.right_neutral filter_single_mset filter_unions_eq is_FunI of_nat_add size_single size_union) 
  qed
qed (simp add: filter_fun_def)

lemma ac_case_subst_size:
  fixes S :: "('f, 'a) term multiset"
  assumes "actop f s = S" and "actop f t = T"
  and "actop f (s \<cdot> \<sigma>) = S'" and "actop f (t \<cdot> \<sigma>) = T'"
  and "\<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>) = (T - S)\<restriction>\<^sub>v \<cdot># \<sigma>"
shows "int_size S - int_size T \<le> int_size S' - int_size T'"
proof -
  let ?U = "(T - S)\<restriction>\<^sub>v"
  let ?f = "(h :: 'f \<times> nat)"
  obtain X H where x: "T\<restriction>\<^sub>v \<inter># S\<restriction>\<^sub>v = X" and h: "S\<restriction>\<^sub>v = H + X"
    by (metis add.commute multiset_inter_commute subset_mset.inf_le1 subset_mset.le_iff_add)
  from x have diff: "?U = T\<restriction>\<^sub>v - X" by auto
  have "int_size X \<le> int_size (\<nabla># f (X \<cdot># \<sigma>))"
    by (induct X, auto) (metis actop_mim_size add_mono of_nat_1 of_nat_le_iff)
  moreover have "int_size (H \<cdot># \<sigma>) \<le> int_size (\<nabla># f (H \<cdot># \<sigma>))"
    by (induct H, auto) (metis actop_mim_size add_mono of_nat_1 of_nat_le_iff)
  moreover have "int_size S = int_size (S\<restriction>\<^sub>n ?f) + int_size (S\<restriction>\<^sub>p ?f) + int_size H + int_size X"
    using h filter_unions_eq[of S ?f] by auto (metis (no_types) ab_semigroup_add_class.add_ac(1) of_nat_add size_union)   
  ultimately have lhs: "int_size S' \<ge> int_size S + int_size (\<nabla># f (X \<cdot># \<sigma>)) - int_size X"
    using subst_actop_size_eq[of f s \<sigma> ?f] h
    unfolding assms(1, 3) h by simp

  have "int_size (\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>)) = int_size (\<nabla># f (?U \<cdot># \<sigma>)) + int_size (\<nabla># f (X \<cdot># \<sigma>))" using x
    by (auto, smt diff_intersect_right_idem image_mset_union multiset_inter_commute of_nat_add size_union subset_mset.diff_add subset_mset.inf.cobounded2 sum_mset.union) 
  moreover have "int_size (?U \<cdot># \<sigma>) = int_size (T\<restriction>\<^sub>v) - int_size X" using x
    by (metis diff of_nat_diff size_Diff_subset_Int size_image_mset size_mset_mono subset_mset.inf.left_idem subset_mset.inf_le1)
  moreover have "int_size T' = int_size (T\<restriction>\<^sub>n ?f) + int_size (T\<restriction>\<^sub>p ?f) + int_size (\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>))"
    using subst_actop_size_eq[of f t \<sigma> ?f] unfolding assms(2, 4) by auto
  ultimately have "int_size T + int_size (\<nabla># f (X \<cdot># \<sigma>)) - int_size X = int_size T'"
    using filter_unions_eq[of T "h"] assms(5) x apply auto
    by (metis (no_types) ab_semigroup_add_class.add_ac(1) of_nat_add size_union)
  then show ?thesis using lhs by linarith 
qed


(** Subsection for case 3c **)

lemma ac_case_3_subst_cl:
  assumes "order_pair s' ns"
  and "\<And>u v. u \<in> set_mset (actop f s) \<Longrightarrow> v \<in> set_mset (actop f t) \<Longrightarrow> (u,v) \<in> ns \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> ns" 
  and "\<And>u v. u \<in> set_mset (actop f s) \<Longrightarrow> v \<in> set_mset (actop f t) \<Longrightarrow> (u,v) \<in> s' \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> s'"
  and "actop f s = S" and "actop f t = T"
  and "actop f (s \<cdot> \<sigma>) = S'" and "actop f (t \<cdot> \<sigma>) = T'"
  and "((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>) \<restriction>\<^sub>p (f, n) = {#}"
  and "\<nabla># f ((T - S)\<restriction>\<^sub>v \<cdot># \<sigma>) = (T - S)\<restriction>\<^sub>v \<cdot># \<sigma>"
  and "filtered_less_rel_s S T (f, n) ns s'"
shows "filtered_less_rel_s S' T' (f, n) ns s'"
proof -
  let ?U = "(T - S)\<restriction>\<^sub>v"
  have "T\<restriction>\<^sub>v \<cdot># \<sigma> \<subseteq># (?U + S\<restriction>\<^sub>v) \<cdot># \<sigma>"
    by (metis filter_diff_mset image_mset_subseteq_mono subset_eq_diff_conv subset_mset.order_refl)
  then have "\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>) \<subseteq># \<nabla># f ((?U + S\<restriction>\<^sub>v) \<cdot># \<sigma>)"
    by (metis image_mset_union subset_mset.le_iff_add sum_mset.union) 
  moreover have "(\<nabla># f ((?U + S\<restriction>\<^sub>v) \<cdot># \<sigma>))\<restriction>\<^sub>p (f, n) = (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>p (f, n)"
    using assms(8, 9) by (simp add: filter_fun_def)
  ultimately have "(\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>p (f, n) \<subseteq># (\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>p (f, n)"
    by (metis filter_fun_def multiset_filter_mono)
  then have ns: "((\<nabla># f (S\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>p (f, n), (\<nabla># f (T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>p (f, n)) \<in> ns_mul_ext ns s'"
    by (metis assms(1) diff_union_cancelL ns_mul_ext_rhs_cancel subset_mset.diff_add)
  from s_mul_ext_pres_sub_closer[OF assms(10)] assms(2, 3)
  have "({#x \<cdot> \<sigma>. x \<in># S \<restriction>\<^sub>p (f, n)#}, {#x \<cdot> \<sigma>. x \<in># T \<restriction>\<^sub>p (f, n)#}) \<in> s_mul_ext ns s'"
    by (simp add: assms(4, 5) filter_fun_def)
  from s_ns_mul_ext_union_compat[OF this ns]
  show ?thesis unfolding assms (4 - 7)[symmetric] by (auto simp add: sub_flat_filter_unfold)
qed

(** Subsection for ac_case_filtered_rel_cases **)

lemma mactopE:
  assumes "U \<noteq> (\<nabla># f U)"
  shows "(\<exists> A1 A2 B1 B2. U = A1 + A2 \<and> (\<nabla># f U) = B1 + B2 \<and> A1 = B1 \<and>
    A2 \<noteq> {#} \<and> (\<forall> x \<in># B2. \<exists> a \<in># A2. a \<rhd> x))"
  using assms
proof (induct U)
  case (add x U)  
  then show ?case
  proof (cases "U = \<nabla># f U")
    case True
    then show ?thesis
      by auto (metis actop_impl_subterm add.commute add.prems add_mset_add_single empty_not_add_mset multi_member_last sum_mset.insert)
  next
    case False
    then obtain A1 A2 B1 B2 where wit: "U = A1 + A2 \<and> (\<nabla># f U) = B1 + B2 \<and> A1 = B1 \<and>
    A2 \<noteq> {#} \<and> (\<forall> x \<in># B2. \<exists> a \<in># A2. a \<rhd> x)" using add by blast
    then show ?thesis 
    proof (cases "{#x#} = actop f x")
      case True
      then have "add_mset x U = add_mset x A1 + A2 \<and>  (\<nabla># f (add_mset x U)) = add_mset x B1 + B2"
        using wit by auto
      then show ?thesis using wit by auto (metis union_mset_add_mset_left) 
    next
      case False
      then have "(\<forall> e \<in># actop f x. x \<rhd> e)" using Bin_cases[of x]
        by auto (metis (mono_tags, lifting) actop.simps(1) actop_mset_elem_subterm)
      then have "\<forall> e \<in># (actop f x + B2). \<exists> a \<in># add_mset x A2. a \<rhd> e"
        using wit by auto
      moreover have "add_mset x U = A1 + add_mset x A2 \<and> (\<nabla># f (add_mset x U)) = B1 + (actop f x + B2)"
        using wit by auto
      ultimately show ?thesis using wit by (metis empty_not_add_mset)  
    qed
  qed
qed auto 

lemma aux1:
  assumes "\<And> s t. s \<rhd> t \<Longrightarrow> (s,t) \<in> s_rel"
  and "refl ns_rel"
  and "S \<cdot># \<sigma> \<noteq> (\<nabla># f (S \<cdot># \<sigma>))"
  shows "(S \<cdot># \<sigma>, (\<nabla># f (S \<cdot># \<sigma>))) \<in> s_mul_ext ns_rel s_rel"
  using assms(1, 2) mactopE[OF assms(3)] 
  by (auto intro!: s_mul_extI) (meson UNIV_I refl_multpw refl_on_def)+


lemma lemma_5_8_1:
  fixes s ::"('f, 'v) term"
    and \<sigma> ::"'v \<Rightarrow> ('f, 'v) term"
  assumes  "order_pair s_rel ns_rel"
    and "\<And>u v. u \<in> set_mset (actop f s) \<Longrightarrow> v \<in> set_mset (actop f t) \<Longrightarrow> (u,v) \<in> ns_rel \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> ns_rel"
    and "\<And>u v. u \<in> set_mset (actop f s) \<Longrightarrow> v \<in> set_mset (actop f t) \<Longrightarrow> (u,v) \<in> s_rel \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> s_rel"
    and "\<And> s t. s \<rhd> t \<Longrightarrow> (s,t) \<in> s_rel" 
    and "filtered_nless_rel_s (actop f s) (actop f t) (f, n) ns_rel s_rel" (is "filtered_nless_rel_s ?S ?T ?f _ _")
  shows "filtered_nless_rel_s (actop f (s \<cdot> \<sigma>)) (actop f (t \<cdot> \<sigma>)) (f, n) ns_rel s_rel" (is "filtered_nless_rel_s ?S' ?T' _ _ _")
proof -
  let ?U = "(?T - ?S)\<restriction>\<^sub>v"
  have ref: "refl ns_rel" using assms(1) order_pair.axioms(1) pre_order_pair_def by blast 
  from s_mul_ext_pres_sub_closer[OF assms(5, 2, 3)]
  have wit: "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma>, ?T\<restriction>\<^sub>n ?f \<cdot># \<sigma> + ?U \<cdot># \<sigma>) \<in> s_mul_ext ns_rel s_rel"
    by (smt filter_diff_mset filter_fun_def image_mset_union mset_subset_eqD multiset_filter_subset subset_rel_filterd_comb)  
  have l: "locally_refl ns_rel (\<Sum>\<^sub># (image_mset (actop f) {#x \<cdot> \<sigma>. x \<in># actop f s \<restriction>\<^sub>v#}) \<restriction>\<^sub>n ?f)"
    using ref unfolding locally_refl_def refl_on_def by blast
  have w:"(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f + ?U \<cdot># \<sigma>) \<in> s_mul_ext ns_rel s_rel"
    using s_mul_ext_union_compat[OF wit, of "(\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f"] l
    by (simp add: add.left_commute union_commute)
  then have "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f + (\<nabla># f (?U \<cdot># \<sigma>))) \<in> s_mul_ext ns_rel s_rel"
    using s_s_mul_ext_sum_trans[where ?B="?U \<cdot># \<sigma>" and ?D="(\<nabla># f (?U \<cdot># \<sigma>))"]
    using aux1[OF assms(4) ref, of \<sigma> ?U] assms(1)
    unfolding order_pair_def pre_order_pair_def compat_pair_def
    by (cases "?U \<cdot># \<sigma> \<noteq> (\<nabla># f (?U \<cdot># \<sigma>))", auto)
      (metis cl_lcl compatible_l_def compatible_r_def cr_lcr r_lr tr_ltr union_commute)
  from s_ns_mul_ext_trans[OF _ _ _ _ _ this supseteq_imp_ns_mul_ext[OF ref aux_nstrict_subs]]
  have "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T \<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n ?f + ((\<nabla># f (?T\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v - (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v)) \<in> s_mul_ext ns_rel s_rel"
    using assms(1) unfolding order_pair_def pre_order_pair_def compat_pair_def
    by (simp add: compatible_l_def compatible_r_def)
  then show ?thesis by (simp add: sub_flat_filter_unfold sub_flat_var_unfold)
qed

lemma lemma_5_8_2:
  fixes s ::"('f, 'v) term"
    and \<sigma> ::"'v \<Rightarrow> ('f, 'v) term"
  assumes  "order_pair s_rel ns_rel"
    and "\<And>u v. u \<in> set_mset (actop f s) \<Longrightarrow> v \<in> set_mset (actop f t) \<Longrightarrow> (u,v) \<in> ns_rel \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> ns_rel"
    and "\<And>u v. u \<in> set_mset (actop f s) \<Longrightarrow> v \<in> set_mset (actop f t) \<Longrightarrow> (u,v) \<in> s_rel \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> s_rel"
    and "\<And> s t. s \<rhd> t \<Longrightarrow> (s,t) \<in> s_rel" 
    and "filtered_nless_rel_ns (actop f s) (actop f t) (f, n) ns_rel s_rel" (is "filtered_nless_rel_ns ?S ?T ?f _ _")
  shows "filtered_nless_rel_s (actop f (s \<cdot> \<sigma>)) (actop f (t \<cdot> \<sigma>)) (f, n) ns_rel s_rel \<or>
         filtered_nless_rel_ns (actop f (s \<cdot> \<sigma>)) (actop f (t \<cdot> \<sigma>)) (f, n) ns_rel s_rel \<and>
         (\<nabla># f (((actop f t) - (actop f s))\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>p (f, n) = {#} \<and> \<nabla># f (((actop f t) - (actop f s))\<restriction>\<^sub>v \<cdot># \<sigma>) = ((actop f t) - (actop f s))\<restriction>\<^sub>v \<cdot># \<sigma>" 
proof -
  let ?S' = "actop f (s \<cdot> \<sigma>)"
  let ?T' = "actop f (t \<cdot> \<sigma>)" 
  let ?U = "(?T - ?S)\<restriction>\<^sub>v"
  have ref: "refl ns_rel" using assms(1) order_pair.axioms(1) pre_order_pair_def by blast 
  from ns_mul_ext_pres_sub_closer[OF assms(5, 2, 3)]
  have wit: "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma>, ?T\<restriction>\<^sub>n ?f \<cdot># \<sigma> + ?U \<cdot># \<sigma>) \<in> ns_mul_ext ns_rel s_rel"
    by (smt filter_diff_mset filter_fun_def image_mset_union mset_subset_eqD multiset_filter_subset subset_rel_filterd_comb)  
  have l: "locally_refl ns_rel (\<Sum>\<^sub># (image_mset (actop f) {#x \<cdot> \<sigma>. x \<in># actop f s \<restriction>\<^sub>v#}) \<restriction>\<^sub>n ?f)"
    using ref unfolding locally_refl_def refl_on_def by blast
  have w:"(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f + ?U \<cdot># \<sigma>) \<in> ns_mul_ext ns_rel s_rel"
    using ns_mul_ext_union_compat[OF wit, of "(\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f"] l
    by (simp add: add.left_commute union_commute)
  consider (a) "(\<nabla># f (?U \<cdot># \<sigma>)) \<restriction>\<^sub>p ?f = {#} \<and> \<nabla># f (?U \<cdot># \<sigma>) = ?U \<cdot># \<sigma>" |
    (b) "(\<nabla># f (?U \<cdot># \<sigma>)) \<restriction>\<^sub>p ?f \<noteq> {#}" | (c) "\<nabla># f (?U \<cdot># \<sigma>) \<noteq> ?U \<cdot># \<sigma>" by blast
  then show ?thesis
  proof cases
    case a
    have "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f + (\<nabla># f (?U \<cdot># \<sigma>))) \<in> ns_mul_ext ns_rel s_rel"
      using w a by simp
    from ns_mul_ext_trans[OF _ _ _ _ _ this supseteq_imp_ns_mul_ext[OF ref aux_nstrict_subs]]
    have "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T \<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n ?f + ((\<nabla># f (?T\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v - (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v)) \<in> ns_mul_ext ns_rel s_rel"
      using assms(1) unfolding order_pair_def pre_order_pair_def compat_pair_def
      by (simp add: compatible_l_def compatible_r_def)
    then show ?thesis using a by (metis sub_flat_filter_unfold sub_flat_var_unfold)
  next
    case b
    have "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f + (\<nabla># f (?U \<cdot># \<sigma>))) \<in> ns_mul_ext ns_rel s_rel"
      using w ns_s_mul_ext_sum_trans[where ?B="?U \<cdot># \<sigma>" and ?D="(\<nabla># f (?U \<cdot># \<sigma>))"]
      using aux1[OF assms(4) ref, of \<sigma> ?U] assms(1)
      unfolding order_pair_def pre_order_pair_def compat_pair_def
      by (cases "?U \<cdot># \<sigma> \<noteq> (\<nabla># f (?U \<cdot># \<sigma>))", auto)
        (metis cl_lcl compatible_l_def compatible_r_def cr_lcr r_lr s_ns_mul_ext tr_ltr union_commute)
    from ns_s_mul_ext_trans[OF _ _ _ _ _ this supset_imp_s_mul_ext[OF ref aux_strict_subs[OF b]]]
    have "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T \<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n ?f + ((\<nabla># f (?T\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v - (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v)) \<in> s_mul_ext ns_rel s_rel"
      using assms(1) unfolding order_pair_def pre_order_pair_def compat_pair_def
      by (simp add: compatible_l_def compatible_r_def)
    then show ?thesis using b by (simp add: sub_flat_filter_unfold sub_flat_var_unfold)
  next
    case c
    then have "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f + (\<nabla># f (?U \<cdot># \<sigma>))) \<in> s_mul_ext ns_rel s_rel"
      using w ns_s_mul_ext_sum_trans[where ?B="?U \<cdot># \<sigma>" and ?D="(\<nabla># f (?U \<cdot># \<sigma>))"]
      using aux1[OF assms(4) ref, of \<sigma> ?U] assms(1)
      unfolding order_pair_def pre_order_pair_def compat_pair_def
      by auto (metis cl_lcl compatible_l_def compatible_r_def cr_lcr r_lr tr_ltr union_commute)
    from s_ns_mul_ext_trans[OF _ _ _ _ _ this supseteq_imp_ns_mul_ext[OF ref aux_nstrict_subs]]
    have "(?S\<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>n ?f, ?T \<restriction>\<^sub>n ?f \<cdot># \<sigma> + (\<nabla># f (?T\<restriction>\<^sub>v \<cdot># \<sigma>)) \<restriction>\<^sub>n ?f + ((\<nabla># f (?T\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v - (\<nabla># f (?S\<restriction>\<^sub>v \<cdot># \<sigma>))\<restriction>\<^sub>v)) \<in> s_mul_ext ns_rel s_rel"
      using assms(1) unfolding order_pair_def pre_order_pair_def compat_pair_def
      by (simp add: compatible_l_def compatible_r_def)
    then show ?thesis by (metis sub_flat_filter_unfold sub_flat_var_unfold)
  qed
qed

lemma ac_case_subst_closed:
   fixes s ::"('f, 'v) term"
    and \<sigma> ::"'v \<Rightarrow> ('f, 'v) term"
  assumes  "order_pair s_rel ns_rel"
    and "\<And>u v. u \<in> set_mset (actop f s) \<Longrightarrow> v \<in> set_mset (actop f t) \<Longrightarrow> (u,v) \<in> ns_rel \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> ns_rel"
    and "\<And>u v. u \<in> set_mset (actop f s) \<Longrightarrow> v \<in> set_mset (actop f t) \<Longrightarrow> (u,v) \<in> s_rel \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> s_rel"
    and "\<And> s t. s \<rhd> t \<Longrightarrow> (s,t) \<in> s_rel" 
    and "ac_case_filtered_rel (actop f s) (actop f t) (f, n) ns_rel s_rel"
  shows "ac_case_filtered_rel (actop f (s \<cdot> \<sigma>)) (actop f (t \<cdot> \<sigma>)) (f, n) ns_rel s_rel"
proof (cases rule: ac_case_filtered_rel_cases[OF assms(5)])
  case (1 S T f' ns' s')
  then show ?thesis using lemma_5_8_1[OF assms(1-4), of f s t n]
    unfolding ac_case_filtered_rel_def by auto
next
  case (2 S T f' ns' s')
  then show ?thesis using lemma_5_8_2[OF assms(1-4), of f s t n]
    using ac_case_subst_size[OF 2(1,2), of \<sigma>]
    unfolding ac_case_filtered_rel_def by simp fastforce 
next
  case (3 S T f' ns' s')
  then show ?thesis using lemma_5_8_2[OF assms(1-4), of f s t n]
    using ac_case_subst_size[OF 3(1,2), of \<sigma>]
    using ac_case_3_subst_cl[OF assms(1-3) 3(1, 2)]
    unfolding ac_case_filtered_rel_def by simp fastforce
qed

end

end
