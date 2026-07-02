(*
Author:  Alexander Lochmann <alexander.lochmann@uibk.ac.at> (2018)
License: LGPL (see file COPYING.LESSER)
*)
theory Ackbo
  imports AC_Weight
begin

locale admissible_weight_fun_ac =
  admissible_weight_fun w w0 pr_strict 
  for w  :: "'f \<times> nat \<Rightarrow> nat"
    and w0 :: "nat"
    and pr_strict :: "('f \<times> nat) \<Rightarrow> ('f \<times> nat) \<Rightarrow> bool" +
  fixes AC ::"'f set"
begin

inductive ackbo_case0 :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "ackbo_case0 (Fun f [Var x]) (Var x)" |
    "ackbo_case0 (Fun f ts) x \<Longrightarrow> ackbo_case0 (Fun f [Fun f ts]) x"

lemma ackbo_case0_subterm:
  "ackbo_case0 s t \<Longrightarrow> s \<rhd> t"
  by (induct rule:ackbo_case0.induct) auto

lemma case0_adm_var:
  assumes "weight s = weight t"
    and "vars_term_ms t \<subseteq># vars_term_ms s"
    and "is_Fun s" and "is_Var t"
  shows "ackbo_case0 s t"
  using assms
proof (induct s)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ss)
  from assms have wt: "weight t = w0" by fastforce
  then have len: "length ss \<ge> 1" using Fun(2-5)
    by (cases "length ss = 0") (auto simp add: Suc_leI)
  then have "sum_list (map weight ss) \<ge> w0"
    by (metis (no_types, lifting) distrib_left le_iff_add mult.right_neutral trans_le_add1 weight_lower_bound_list) 
  then have wf: "w (f, 1) = 0" and "length ss = 1" using len Fun(2, 3) wt 
     apply (cases "length ss > 1", auto)
    by (metis Fun.prems(1) leD n_less_m_mult_n w0(2) weight_lower_bound_n_arry_fun)
       (metis Fun.prems(1) leD n_less_m_mult_n nat_less_le w0(2) weight_lower_bound_n_arry_fun) 
  then obtain su where s_u: "ss = [su]"
    by (metis impossible_Cons le_add1 length_0_conv length_Cons mult.left_neutral mult_Suc_right neq_Nil_conv zero_neq_one)     
  then show ?case proof(cases "is_Var su")
    case True
    then have "su = t" using s_u Fun(3, 5) vars_term_ms.simps(1) by fastforce
    then show ?thesis using s_u ackbo_case0.simps[of "Fun f ss" t] Fun(5) by blast
  next
    case False
    then obtain h hs where su: "su = Fun h hs" by blast
    then have len: "length hs \<ge> 1" using Fun(2-5) False unfolding s_u su
      by (cases "length hs = 0") (auto simp add: Suc_leI)
    then have "sum_list (map weight hs) \<ge> w0"
      by (metis (no_types, lifting) distrib_left le_iff_add mult.right_neutral trans_le_add1 weight_lower_bound_list) 
    then have "w(h, 1) = 0" and "length hs = 1" using Fun(2,5) wt su s_u wf len
       apply (cases "1 = length hs \<or> 1 < length hs", auto)
       apply (metis One_nat_def add_cancel_right_left le_antisym local.wf n_less_m_mult_n nat_less_le w0(2) weight.simps(2) weight_lower_bound_n_arry_fun)
      by (metis One_nat_def add_cancel_right_left le_add2 le_antisym local.wf mult.commute n_less_m_mult_n nat_less_le w0(2) weight_lower_bound_list)  
    then have feq: "h = f" using wf unique_unary_function_weight0 by blast
    then have "ackbo_case0 (Fun f hs) t" using Fun(1)[of su] Fun s_u wf su by auto
    then show ?thesis using ackbo_case0.simps[of "Fun f ss" t] s_u su feq by auto
  qed
qed


inductive ackbo :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    case_w: "vars_term_ms t \<subseteq># vars_term_ms s \<Longrightarrow> weight s > weight t \<Longrightarrow> ackbo s t" |
    case_0: "vars_term_ms t \<subseteq># vars_term_ms s \<Longrightarrow> weight s = weight t \<Longrightarrow> is_Fun s \<Longrightarrow> is_Var t \<Longrightarrow> ackbo s t" |
    case_1: "vars_term_ms t \<subseteq># vars_term_ms s \<Longrightarrow> weight s = weight t \<Longrightarrow> 
       s = Fun f ts \<Longrightarrow> t = Fun g ys \<Longrightarrow> pr_strict (f, length ts) (g, length ys) \<Longrightarrow> ackbo s t" |
    case_2: "vars_term_ms t \<subseteq># vars_term_ms s \<Longrightarrow> weight s = weight t \<Longrightarrow>
        s = Fun f ts \<Longrightarrow> t = Fun g ys \<Longrightarrow> g = f \<Longrightarrow> length ys = length ts \<Longrightarrow> length ts \<noteq> 2 \<or> f \<notin> AC \<Longrightarrow>
        fst (lex_ext (\<lambda> x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length ts) ts ys) \<Longrightarrow> ackbo s t" |
    case_3: "vars_term_ms t \<subseteq># vars_term_ms s \<Longrightarrow> weight s = weight t \<Longrightarrow>
        s = Fun f ts \<Longrightarrow> t = Fun g ys \<Longrightarrow> g = f \<Longrightarrow> length ys = length ts \<Longrightarrow> length ts = 2 \<Longrightarrow> f \<in> AC \<Longrightarrow>
        ac_case_filtered_rel (actop f s) (actop f t) (f, length ts) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y} \<Longrightarrow> ackbo s t"

lemma ackbo_weight_ineq:
  assumes "ackbo s t"
    and "weight s \<noteq> weight t"
  shows "weight s > weight t"
  using assms by cases auto

lemma ackbo_weight_eq:
  assumes "ackbo s t"
    and "\<not> weight s > weight t"
  shows "weight s = weight t"
  using assms by cases auto

lemma ackbo_weight_pos:
  assumes "ackbo s t"
  shows "weight s = weight t \<or> weight s > weight t"
  using assms by (induct rule: ackbo.induct) auto

lemma ackbo_trivial_context_closure:
  assumes "ackbo s t"
  shows "ackbo (Fun f [s]) (Fun f [t])"
proof -
  have vars:"vars_term_ms (Fun f [t]) \<subseteq># vars_term_ms (Fun f [s])" using assms ackbo.simps by auto
  consider (a) "weight s > weight t" | (b) "weight s = weight t" using assms ackbo.simps by blast
  then show ?thesis
  proof cases
    case a
    then have "weight (Fun f [s]) > weight (Fun f [t])" by auto
    then show ?thesis using vars ackbo.case_w by blast
  next
    case b
    then have "weight (Fun f [s]) = weight (Fun f [t])" by auto
    moreover have "fst (lex_ext (\<lambda> x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length [s]) [s] [t])" using assms by (simp add: lex_ext_iff) 
    ultimately show ?thesis using ackbo.case_2 vars
      by (simp add: case_2) 
  qed
qed

lemma ackbo_no_var_impl_prstrict_or_eq_root:
  assumes "ackbo s t"
    and "s = Fun f fs"
    and "t = Fun g gs"
    and "weight s = weight t"
  shows "pr_strict (f,length fs) (g,length gs) \<or> f = g \<and> length fs = length gs"
  using assms by cases auto

(* Section order pair *)
lemmas ac_terms_root_vars_w_eq = ac_terms_eq_root
  ac_terms_share_vars
  ac_terms_weight_eq


thm compat_right[of _ _ "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*", OF _ _ ac_share_vars[of _ _ AC]]
lemmas ac_compat_left = compat_left[OF _ ac_terms_eq_root[of _ _ AC] ac_share_vars[of _ _ AC] tr_ltr[OF conversion_trans[of "acstep AC AC"]]]
lemmas ac_compat_right = compat_right[OF _ ac_terms_eq_root[of _ _ AC] ac_share_vars[of _ _ AC] _ tr_ltr[OF conversion_trans[of "acstep AC AC"]]]
lemmas ac_trans = ac_case_trans[OF _ tr_ltr[OF conversion_trans[of "acstep AC AC"]]]

(* Subsection compatibility *)
lemma ackbo_compat_l:
  assumes "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
    and "ackbo t u"
  shows "ackbo s u"
  using assms
proof (induct t arbitrary: s u rule: subterm_induct)
  case (subterm t)
  from subterm(3) show ?case
  proof cases
    case case_w
    then have "weight u < weight s" by (metis ac_terms_weight_eq subterm.prems(1)) 
    then show ?thesis by (metis ac_terms_share_vars ackbo.case_w local.case_w(1) subterm.prems(1)) 
  next
    case case_0
    then show ?thesis using ac_terms_root_vars_w_eq[OF subterm(2)] case_0(1,2)
      by (auto simp add: ackbo.case_0 elim!: root.elims)
  next
    case case_1
    then show ?thesis using ac_terms_root_vars_w_eq[OF subterm(2)]
      by (auto simp add: ackbo.case_1 elim!: root.elims)
  next
    case case_2
    let ?f = "\<lambda> x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
    have rec: "\<forall> i < length (args s). ((args s ! i, args t ! i) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
      using case_2 ac_terms_eq_root[OF subterm(2)] apply (auto elim!: root.elims)
      by (metis (no_types, lifting) ac_arity_not_two_impl_ac_terms_on_args_list subterm.prems(1))+ 
    have "locally_compatible_l {(x, y). snd (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)}
     {(x, y). fst (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)} (mset (args s)) (mset (args t)) (mset (args u))"
      using subterm(1) unfolding locally_compatible_l_def by auto (metis local.case_2(3) supt.arg term.sel(4)) 
    from lex_ext_compat_l[OF this, of "length (args s)"] conversion_trans tr_ltr
    have "fst (lex_ext (\<lambda>x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (num_args s) (args s) (args u))"
      using ac_terms_eq_root[OF subterm(2)] case_2(2-4, 6, 8) rec
      by (auto simp add: all_nstri_imp_lex_nstri elim!: root.elims) blast
    then show ?thesis using ac_terms_root_vars_w_eq[OF subterm(2)] case_2
      by (auto elim!: root.elims simp add: ackbo.case_2)
  next
    case (case_3 f ts)
    then obtain ss where s: "s = Fun f ss" and len: "length ss = length ts"
      using ac_terms_eq_root[OF subterm(2)] by (auto elim!: root.elims)
    then have "locally_compatible_l ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x, y). ackbo x y} (actop f s) (actop f t) (actop f u)"
      using subterm(1) unfolding locally_compatible_l_def
      by auto (smt actop_mset_elem_subterm length_0_conv length_Suc_conv case_3(3,7) numeral_2_eq_2)
    from ac_compat_left[OF acstep_impl_actop_multpw[OF subterm(2) case_3(8)] _ _ this, of "(f,2)"] case_3(3) ac_terms_eq_root[OF subterm(2)]
    have "ac_case_filtered_rel (actop f s) (actop f u) (f, length ss) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y}"
      using case_3(7-9) s len by auto
    from ackbo.case_3[OF _ _ s case_3(4) _ _ _ case_3(8) this]
    show ?thesis using ac_terms_root_vars_w_eq[OF subterm(2)] len s case_3(1-7)
      by (auto elim!: root.elims)
  qed
qed

lemma ackbo_rel_compat_l:
  shows "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>* O {(x, y). ackbo x y} \<subseteq> {(x, y). ackbo x y}"
  using ackbo_compat_l by blast

lemma ackbo_compat_r:
  assumes "(t, u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
    and "ackbo s t"
  shows "ackbo s u"
  using assms
proof (induct s arbitrary: t u rule: subterm_induct)
  case (subterm s)
  have sym: "(u, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*" using subterm(2) by (simp add: conversion_inv) 
  from subterm(3) show ?case
  proof cases
    case case_w
    then have "weight u < weight s" by (metis ac_terms_weight_eq subterm.prems(1)) 
    then show ?thesis by (metis ac_terms_share_vars ackbo.case_w local.case_w(1) subterm.prems(1)) 
  next
    case case_0
    then show ?thesis using ac_terms_root_vars_w_eq[OF subterm(2)] case_0(1,2)
      by (auto simp add: ackbo.case_0 elim!: root.elims)
  next
    case (case_1 f ts g ys)
    then show ?thesis using ac_terms_root_vars_w_eq[OF subterm(2)] ackbo.case_1[of u s]
      by (auto elim!: root.elims simp del: weight.simps vars_term_ms.simps)
         (metis prod.sel(1, 2) root_Some)
  next
    case (case_2 f ts g ys)
    let ?f = "\<lambda> x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
    have rec: "\<forall> i < length (args t). ((args t ! i, args u ! i) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
      using case_2 ac_terms_eq_root[OF sym] apply (auto elim!: root.elims)
      by (metis (no_types, lifting) ac_arity_not_two_impl_ac_terms_on_args_list conversion_inv local.sym)+ 
    have "locally_compatible_r {(x, y). snd (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)}
     {(x, y). fst (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)} (mset (args s)) (mset (args t)) (mset (args u))"
      using subterm(1) unfolding locally_compatible_r_def
      by auto (metis Var_supt ackbo_case0_subterm supt.arg supt_imp_args term.sel(4) weight_fun.weight.cases)  
    from lex_ext_compat_r[OF this, of "length (args s)"] conversion_trans tr_ltr
    have "fst (lex_ext (\<lambda>x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (num_args s) (args s) (args u))"
      using ac_terms_eq_root[OF sym] case_2(2-4, 6, 8) rec
      by (auto simp add: all_nstri_imp_lex_nstri elim!: root.elims) blast
    then show ?thesis using ac_terms_root_vars_w_eq[OF sym] case_2
      by (auto elim!: root.elims simp add: ackbo.case_2)
  next
    case (case_3 f ts g ys)
    then obtain ss where s: "s = Fun f ss" and len: "length ss = length ts"
      using ac_terms_eq_root[OF subterm(2)] by (auto elim!: root.elims)
    then have "locally_compatible_r ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x, y). ackbo x y} (actop f s) (actop f t) (actop f u)"
      using subterm(1) unfolding locally_compatible_r_def
      by auto (smt actop_mset_elem_subterm length_0_conv length_Suc_conv case_3(3,7) numeral_2_eq_2)
    from ac_compat_right[OF acstep_impl_actop_multpw[OF subterm(2) case_3(8)] _ _ _ this, of "(f,2)"] case_3(3) ac_terms_eq_root[OF subterm(2)]
    have "ac_case_filtered_rel (actop f s) (actop f u) (f, length ss) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y}"
      using case_3(7-9) s len by auto
    from ackbo.case_3[OF _ _ s _ _ _ _ case_3(8) this]
    show ?thesis using ac_terms_root_vars_w_eq[OF sym] len s case_3(1-7)
      by (auto elim!: root.elims)
  qed
qed

lemma ackbo_rel_compat_r:
  shows "{(x, y). ackbo x y} O (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> {(x, y). ackbo x y}"
  using ackbo_compat_r by blast

(* Subsection transitivity *)

lemma ackbo_lhs_var_false[simp]:
  assumes "ackbo s t"
  shows "is_Var s = False"
  using assms leD weight_w0 by (cases, auto) fastforce

lemma ackbo_trans:
  assumes "ackbo s t"
    and "ackbo t u"
  shows "ackbo s u"
  using assms
proof (induct s arbitrary: t u rule: subterm_induct)
  case (subterm s)
  note assms = subterm(2,3)
  have vars: "vars_term_ms u \<subseteq># vars_term_ms s" using assms ackbo.simps subset_mset.order_trans by blast
  consider (a) "weight s \<noteq> weight t \<or> weight t \<noteq> weight u" | (weight_eq) "weight s = weight t \<and> weight t = weight u"
    by auto
  then show ?case
  proof cases
    case a
    then have "weight s > weight t \<or> weight t > weight u" using assms ackbo.simps by auto
    moreover have "weight s \<ge> weight t \<and> weight t \<ge> weight u" using assms ackbo.simps dual_order.order_iff_strict by blast
    ultimately have "weight s > weight u" by linarith
    then show ?thesis using vars by (auto simp add: case_w)
  next
    case weight_eq
    then have wsu: "weight s = weight u" by auto
    from assms have fun_s: "is_Fun s" and fun_t: "is_Fun t" using ackbo_lhs_var_false by auto
    consider (a) "root s \<noteq> root t \<or> root t \<noteq> root u" | (root_eq) "root s = root t \<and> root t = root u" by auto
    then show ?thesis
    proof cases
      case a

      then show ?thesis
      proof (cases u)
        case (Fun h us)
        from fun_s fun_t obtain f g ss ts where s: "s = Fun f ss" and t: "t = Fun g ts" by (meson is_FunE) 
        from ackbo_no_var_impl_prstrict_or_eq_root[OF subterm(2) s t conjunct1[OF weight_eq]]
             ackbo_no_var_impl_prstrict_or_eq_root[OF subterm(3) t Fun conjunct2[OF weight_eq]]
        have "pr_strict (f, length ss) (h, length us)" using a unfolding s t Fun
          apply (auto elim!:root.elims)  using pr_trans by blast+         
        then show ?thesis using wsu vars unfolding s Fun by (auto simp add: ackbo.case_1)
      qed (metis case_0 fun_s is_VarI vars weight_eq)  
     next
      case root_eq
      show ?thesis using assms(2)
      proof cases
        case case_w
        then show ?thesis using weight_eq by auto
      next
        case case_0
        then show ?thesis using weight_eq assms(1) by (metis ackbo.case_0 ackbo_lhs_var_false vars) 
      next
        case (case_1 f ts g ys)
        then show ?thesis using root_eq by (auto simp add: pr_irr elim!: root.elims)
      next
        case (case_2 f ts g us)
        let ?f = "\<lambda>x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
        from root_eq case_2
        obtain ss where s: "s = Fun g ss" and len_s: "length ss = length ts" by (auto elim!: root.elims) 
        have str: "fst (lex_ext ?f (length ts) ss ts)" using assms(1) len_s weight_eq case_2(7)
          unfolding s case_2(3, 5) by cases (auto simp add: pr_irr elim!: root.elims)
        have trans_ns: "locally_trans {(x, y). snd (?f x y)} (mset ss) (mset ts) (mset us)"
          by (simp add: acconv_iff locally_trans_def)
        have trans_s: "locally_trans {(x, y). fst (?f x y)} (mset ss) (mset ts) (mset us)"
          using subterm(1) unfolding locally_trans_def case_2
          by (metis (no_types, lifting) CollectI Product_Type.Collect_case_prodD case_prodI in_multiset_in_set prod.collapse prod.inject s supt.arg) 
        have locally_compat_l: "locally_compatible_l {(x, y). snd ((\<lambda>x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) x y)} {(x, y). fst ((\<lambda>x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) x y)} (mset ss) (mset ts) (mset us)"
          by (simp add: ackbo_compat_l locally_compatible_l_def)
        have locally_compat_r: "locally_compatible_r {(x, y). snd ((\<lambda>x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) x y)} {(x, y). fst ((\<lambda>x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) x y)} (mset ss) (mset ts) (mset us)"
          by (simp add: ackbo_compat_r locally_compatible_r_def)
        from lex_ext_trans[OF trans_ns trans_s locally_compat_l locally_compat_r _ _ _ str case_2(8)]
        have "fst (lex_ext (\<lambda>x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length ts) ss us)"
          using root_eq unfolding s case_2 by (auto elim!: root.elims)
        then show ?thesis using vars root_eq weight_eq case_2(7) unfolding case_2 s
          by (auto simp add: ackbo.case_2 elim!: root.elims)
      next
        case (case_3 f ts g us)
        from root_eq case_3
        obtain ss where s: "s = Fun g ss" and len_s: "length ss = length ts" by (auto elim!: root.elims)
        have s_c: "ac_case_filtered_rel (actop f s) (actop f t) (f, length ts) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y}"
          using assms(1) case_3(7, 8) root_eq weight_eq len_s pr_irr unfolding s case_3
          by cases (auto elim!: root.elims)
        have loc_trans_s: "locally_trans {(x, y). ackbo x y} (actop f s) (actop f t + actop f u) (actop f t + actop f u)"
          using subterm(1) unfolding s case_3 locally_trans_def
          by (smt CollectI Product_Type.Collect_case_prodD actop_mset_elem_subterm case_prodI len_s length_0_conv length_Suc_conv local.case_3(7) numeral_2_eq_2 prod.sel(1) prod.sel(2)) 
        have locally_compat_l: "locally_compatible_l ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x, y). ackbo x y} (actop f s) (actop f t + actop f u) (actop f t + actop f u)"
          by (simp add: ackbo_compat_l locally_compatible_l_def)
        have locally_compat_r: "locally_compatible_r ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x, y). ackbo x y} (actop f s) (actop f t + actop f u) (actop f t + actop f u)"
          by (simp add: ackbo_compat_r locally_compatible_r_def)
        from ac_trans[OF _ loc_trans_s locally_compat_l locally_compat_r s_c case_3(9)]
        show ?thesis using case_3(4, 5, 7, 8) vars len_s root_eq weight_eq
          unfolding s case_3 by (auto intro!: ackbo.case_3)
      qed
    qed
  qed
qed

lemma ackbo_rel_trans:
  shows "trans {(x, y). ackbo x y}"
  using ackbo_trans unfolding trans_def by auto

(* Subsection irreflexibility *)

lemma ackbo_irr:
  assumes "ackbo s s"
  shows False
  using assms
proof (induct s rule: subterm_induct)
  case (subterm s)
  show ?case using subterm(2)
  proof cases
    case (case_2 f ss g ys)
    then show ?thesis using subterm(1) unfolding lex_ext_iff by (auto simp add: local.case_2(3)) 
  next
    case (case_3 f ts g ys)
    then have "\<And> x. x \<in># actop f (Fun f ts) \<Longrightarrow> Fun f ts \<rhd> x"
      by (metis (no_types, lifting) actop_mset_subterm_eq length_0_conv length_Suc_conv numeral_2_eq_2 subterm.order.not_eq_order_implies_strict trivial_Bin_facts(5)) 
    then have "locally_irrefl {(x,y). ackbo x y} (actop f s)"
      using subterm(1) unfolding case_3 locally_irrefl_def by blast
    from ac_case_filtered_rel_irrefl[OF ackbo_rel_compat_l ackbo_rel_compat_r this ackbo_rel_trans]
    show ?thesis using case_3(9) by blast
  qed (auto simp add: pr_irr)
qed

interpretation ackbo_ord_p: order_pair "{(x,y). ackbo x y}" "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
  apply unfold_locales apply (auto simp add: ackbo_rel_trans conversion_def trans_rtrancl refl_rtrancl)+
  using ackbo_rel_compat_l ackbo_rel_compat_r by auto

lemma ackbo_order_pair:
  shows "order_pair {(x,y). ackbo x y} ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
  using ackbo_ord_p.order_pair_axioms by auto

(* Section subterm property *)
lemma min_weigth_of_not_empty_list:
  assumes "ss \<noteq> []"
  shows "sum_list (map weight ss) \<ge> w0"
proof (cases ss)
  case Nil
  then show ?thesis using assms(1) by auto
qed (simp add: trans_le_add1 weight_w0)

lemma min_weigth_of_list:
  assumes "u \<in> set ss"
    and "1 < length ss"
  shows "weight u < sum_list (map weight ss)"
  using assms
proof (induct ss arbitrary: u)
  case (Cons a ss)
  show ?case using Cons 
    by (metis all_gt_0_sum_list_map gr0I leD w0(2) weight_w0)
qed auto

lemma ackbo_closed_under_lhs_ext:
  shows "ackbo (Fun f [s]) s"
proof(induct s arbitrary: f)
  case (Var x)
  then show ?case by (cases "w (f, 1) = 0", intro ackbo.case_0, auto) (intro ackbo.case_w, auto)
next
  case (Fun g hs)
  then show ?case
    apply (cases "w (f, 1) = 0")
     apply (cases "pr_strict (f, 1) (g, length hs)", intro ackbo.case_1, auto)
     apply (metis (no_types, lifting) One_nat_def Pair_inject Suc_length_conv ackbo_trivial_context_closure adm length_0_conv list.set_intros(1))
    by (intro ackbo.case_w, auto)
qed

lemma ackbo_closed_under_lhs_ext2:
  shows "ackbo (Fun f (bef @ s # aft)) s"
  apply (cases "length bef + length aft = 0") apply (auto simp add: ackbo_closed_under_lhs_ext)
  using min_weigth_of_list[of s "bef @ s # aft"] by (auto simp add: min_weigth_of_list[of s "bef @ s # aft"] ackbo.case_w)

lemma ackbo_subterm_property:
  assumes "s \<rhd> t"
  shows "ackbo s t"
  using assms
  by (induct rule: supt.induct) 
    (metis ackbo_closed_under_lhs_ext2 split_list_last ackbo_trans split_list_first)+

(**********************************************************************)

lemma actop_size_one:
  assumes "size (actop f t) = 1"
  shows "actop f t = {#t#}"
  using assms apply (cases rule:actop.cases) apply (auto)
  by (metis Suc_n_not_le_n assms actop.simps(1) actop_mim_size actop_singleton non_empty_plus_non_empty_not_single size_1_singleton_mset size_eq_0_iff_empty) 


lemma aux2_for_ctxt_closure:
  assumes "ackbo s t"
    and "f \<in> AC"
  shows "({#s#}, actop f t) \<in> s_mul_ext ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y}"
proof (cases "size (actop f t) = 1")
  case True
  then have "actop f t = {#t#}" using actop_size_one by auto
  then show ?thesis by (simp add: assms(1)) 
next
  case False
  then have sm:"\<And>b. b \<in># actop f t \<Longrightarrow> (\<exists>a. a \<in># {#t#} \<and> ackbo a b)" using ackbo_subterm_property actop_impl_subterm
    by (metis multi_member_last size_single) 
  then have "({#t#}, actop f t) \<in> s_mul_ext ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y} " 
    using s_mul_extI[of "{#t#}" "{#}" "{#t#}" "actop f t" "{#}" "actop f t" "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*" "{(x, y). ackbo x y}"] by auto 
  then show ?thesis using sm
    by (metis CollectI ackbo_trans add_mset_eq_single all_s_s_mul_ext assms(1) case_prodI empty_not_add_mset multi_member_last multi_member_split) 
qed

(*
    Section: Closure under context proofs
*)

lemma lemma_5_7:
  assumes "ackbo s t"
    and "h \<in> AC"
    and "length (bef @ aft) = 1"
    and "u \<in> set (bef @ aft)"
  shows "ackbo (Fun h (bef @ s # aft)) (Fun h (bef @ t # aft))"
proof -
  let ?S = "actop h s"
  let ?T = "actop h t"
  let ?U = "actop h u"
  let ?f = "(h,2)"
  let ?lhs = "Fun h (bef @ s # aft)"
  let ?rhs = "Fun h (bef @ t # aft)"
  let ?str = "{(x,y). ackbo x y}"
  let ?ns = "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
  have v:"vars_term_ms t \<subseteq># vars_term_ms s" using ackbo.simps assms(1) by blast
  have one_empty:"bef = [] \<or> aft = []" using assms(3)
    by (metis One_nat_def Suc_length_conv append_eq_Cons_conv append_is_Nil_conv length_0_conv)
  then have one_con_u:"bef = [u] \<or> aft = [u]" using assms(3-4) by (smt List.self_append_conv One_nat_def Suc_length_conv append_self_conv2 in_set_simps(2) length_0_conv)  
  then have "Fun h (bef @ s # aft) = Fun h [u,s] \<or> Fun h (bef @ s # aft) = Fun h [s,u]" using one_empty by auto
  then have lhs:"actop h ?lhs = ?S + ?U" by auto
  have "Fun h (bef @ t # aft) = Fun h [u,t] \<or> Fun h (bef @ t # aft) = Fun h [t,u]" using one_empty one_con_u by auto
  then have rhs:"actop h ?rhs = ?T + ?U" by auto
  consider (a) "weight s > weight t" | (b) "weight s = weight t" using assms(1) ackbo_weight_pos by blast
  then show ?thesis
  proof cases
    case a
    then have "weight ((More h bef Hole aft)\<langle>s\<rangle>) > weight ((More h bef Hole aft)\<langle>t\<rangle>)" by auto
    moreover have "vars_term_ms ((More h bef Hole aft)\<langle>t\<rangle>) \<subseteq># vars_term_ms ((More h bef Hole aft)\<langle>s\<rangle>)" using assms(1) ackbo.simps by auto
    ultimately show ?thesis using case_w by fastforce
  next
    case b
    have vars:"vars_term_ms ?rhs \<subseteq># vars_term_ms ?lhs" using v by auto
    have wei:"weight ?lhs = weight ?rhs" using b by auto
    have sub:"?T \<restriction>\<^sub>n ?f + (?T\<restriction>\<^sub>v - ?S\<restriction>\<^sub>v) \<subseteq># ?T" by (metis subset_rel_filterd_comb)
    from b show ?thesis
    proof (cases "is_Var t")
      case True
      then have "ackbo_case0 s t" using b assms(1) ackbo_lhs_var_false case0_adm_var v by blast 
      then obtain f s1 where term_s:"s = Fun f [s1]" using is_FunE by (meson ackbo_case0.simps)
      then have "w(f,1) = 0" using True b
        by (metis One_nat_def add_cancel_right_left eq_iff is_FunI le_add2 length_Cons list.size(3) min_weigth_of_not_empty_list not_Cons_self2 weight.elims weight.simps(2))
      then have pr:"pr_strict (f,1) (h,2)" using adm by auto
      then have top_s:"?S = {#s#}" using actop.simps(4) term_s by auto
      then have "?S \<restriction>\<^sub>n ?f = {#s#}" using pr pr_str term_s unfolding filter_fun_def by auto  
      moreover have top_t:"?T = {#t#}" using actop.simps(2) True by auto
      ultimately have "filtered_nless_rel_s ?S ?T ?f ?ns ?str " using assms(1) pr True filter_fun_of_var_empty top_s term_s sub by auto
      then have "ac_case_filtered_rel (?S + ?U) (?T + ?U) ?f ?ns ?str"
        using ac_case_closed_under_mset_union[OF _ ackbo_order_pair] unfolding ac_case_filtered_rel_def by blast
      then show ?thesis using assms wei vars
        by (simp add: \<open>length (bef @ aft) = 1\<close> vars append_Nil2 case_3 lhs numeral_2_eq_2 one_empty rhs) 
    next
      case False
      obtain g gs where term_t:"t = Fun g gs" using False by blast
      obtain f fs where term_s:"s = Fun f fs" using assms(1) ackbo_lhs_var_false by blast 
      then have inv:"pr_strict (f, length fs) (g, length gs) \<or> f = g \<and> length fs = length gs"
        using assms(1) term_t term_s ackbo_no_var_impl_prstrict_or_eq_root b by blast
      consider (i) "\<not> pr_strict (h,2) (f, length fs) \<and> (f \<noteq> h \<or> length fs \<noteq> 2)"|
        (ii)  "pr_strict (h,2) (g,length gs) \<and> f = h \<and> length fs = 2"|
        (iii) "f = h \<and> g = h \<and> length fs = length gs \<and> length fs = 2"|
        (iv)  "pr_strict (h,2) (g,length gs) \<and> pr_strict (h,2) (f,length fs)"
        using inv term_t term_s False by (smt pr_trans)
      then have "ac_case_filtered_rel (?S + ?U) (?T + ?U) ?f ?ns ?str"
      proof cases
        case i
        then have top_s:"?S = {#s#}" using actop.simps term_s
          by (smt One_nat_def Suc_eq_plus1 actop_singleton length_Cons list.size(3) nat_1_add_1 term.sel(4))
        then have "?S \<restriction>\<^sub>n ?f = {#s#}" using i term_s unfolding filter_fun_def by auto
        then have "(?S \<restriction>\<^sub>n ?f, ?T) \<in> s_mul_ext ?ns ?str" using aux2_for_ctxt_closure assms(1-2) by auto
        then have "(?S \<restriction>\<^sub>n ?f, ?T \<restriction>\<^sub>n ?f + (?T\<restriction>\<^sub>v - ?S\<restriction>\<^sub>v)) \<in> s_mul_ext ?ns ?str"
          using s_mul_ext_subset_trans[OF ackbo_order_pair] sub by blast
        then have "filtered_nless_rel_s ?S ?T ?f ?ns ?str" by blast
        then show ?thesis  using ac_case_closed_under_mset_union[OF _ ackbo_order_pair] unfolding ac_case_filtered_rel_def by blast 
      next
        case ii
        then have "h \<noteq> g \<or> length gs \<noteq> 2" using ii pr_irr by auto
        then have top_t:"actop h t = {#Fun g gs#}" using term_t actop.simps
          by (smt One_nat_def Suc_eq_plus1 actop_singleton length_Cons list.size(3) nat_1_add_1 term.sel(4)) 
        then have emp:"?T\<restriction>\<^sub>n ?f = {#}" using term_t ii pr_str unfolding filter_fun_def by auto
        have "size ?S > 1" using ii term_s Bin_cases_with_length[of s] actop.simps(1)[of h f]
          by (smt actop_mim_size nat_less_le non_empty_plus_non_empty_not_single not_one_le_zero size_1_singleton_mset size_empty term.distinct(1) term.inject(2)) 
        then have "size ?S > size ?T" using top_t by auto
        then have "filtered_nless_rel_ns ?S ?T ?f ?ns ?str \<and> size ?S > size ?T" 
          using emp term_t top_t filter_var_of_fun_empty ns_mul_ext_bottom by auto
        then show ?thesis using ac_case_closed_under_mset_union[OF _ ackbo_order_pair] unfolding ac_case_filtered_rel_def by blast 
      next
        case iii
        have " ac_case_filtered_rel (actop f s) (actop f t) (f, length fs) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y}"
          using assms(1-2) b term_s term_t iii  by (smt False Term.term.simps(2) ackbo.simps nat_less_le pr_irr) 
        then show ?thesis using ac_case_closed_under_mset_union[OF _ ackbo_order_pair] term_s term_t iii
          by smt 
      next
        case iv
        then have top_s:"?S = {#s#}" using pr_irr actop.simps term_s
          by (smt One_nat_def Suc_eq_plus1 actop_singleton length_Cons list.size(3) nat_1_add_1 term.sel(4))
        moreover have top_t:"?T = {#t#}" using pr_irr actop.simps term_t iv
          by (smt One_nat_def Suc_eq_plus1 actop_singleton length_Cons list.size(3) nat_1_add_1 term.sel(4))
        ultimately have "filtered_less_rel_s ?S ?T ?f ?ns ?str" using assms(1) iv term_s term_t
          unfolding filter_fun_def by auto
        moreover have "size ?S = size ?T" using top_s top_t by auto
        moreover have "filtered_nless_rel_ns ?S ?T ?f ?ns ?str"
          using iv term_t top_t filter_var_of_fun_empty ns_mul_ext_bottom pr_str unfolding filter_fun_def by auto
        ultimately show ?thesis 
          using ac_case_closed_under_mset_union[OF _ ackbo_order_pair] unfolding ac_case_filtered_rel_def by blast
      qed
      then show ?thesis using assms(1) ackbo.case_3 wei vars
        by (smt One_nat_def append_Nil2 append_self_conv2 assms(2) assms(3) length_Cons length_append lhs list.size(3) numeral_2_eq_2 one_add_one one_empty rhs) 
    qed
  qed
qed


lemma ackbo_mono_one:
  assumes "ackbo s t"
  shows "ackbo (Fun f (ss1 @ s # ss2)) (Fun f (ss1 @ t # ss2))"
proof -
  let ?ss = "ss1 @ s # ss2"
  let ?ts = "ss1 @ t # ss2"
  let ?s = "Fun f ?ss"
  let ?t = "Fun f ?ts"
  have w: "weight t \<le> weight s" using ackbo_weight_eq assms by fastforce
  have v: "vars_term_ms t \<subseteq># vars_term_ms s" using assms ackbo.simps by auto
  have v': "vars_term_ms ?t \<subseteq># vars_term_ms ?s" using v by (induct ss1) auto
  have w': "weight ?t \<le> weight ?s" using w by (induct ss1) auto
  have eq_len:"length ?ss = length ?ts" by auto
  consider (a) "f \<in> AC \<and> length ?ss = 2" | (b) "f \<notin> AC \<or> length ?ss \<noteq> 2" by blast
  then show ?thesis
  proof cases
    case a
    then have "length (ss1 @ ss2) = 1" by auto
    then show ?thesis using lemma_5_7[of s t f ss1 ss2] a
      by (metis append_Nil assms in_set_conv_decomp length_0_conv list.exhaust zero_neq_one)  
  next
    case b
    have "\<forall> i < length ss1. (ss1 ! i, ss1 ! i) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*" by blast
    then have "(\<exists> i < length ?ss. i < length ?ts \<and> (\<forall> j < i. (?ss ! j, ?ts ! j) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) \<and> ackbo (?ss ! i) (?ts !i))"
      using assms
      by (metis (no_types, lifting) List.self_append_conv append_Cons_nth_left le_add_same_cancel1 length_append length_greater_0_conv list.distinct(1) list_eq_iff_nth_eq nat_less_le nth_append_length)
    then have lex: "fst (lex_ext (\<lambda> x y. (ackbo x y, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length ?ss) ?ss ?ts)"
      using eq_len by (simp add: lex_ext_iff)
    then show ?thesis using w' v' by (metis (mono_tags, lifting) b case_2 case_w eq_len nat_less_le) 
  qed
qed

lemma ackbo_ctxt:
  assumes "ackbo s t"
  shows "ackbo (C\<langle>s\<rangle>) (C\<langle>t\<rangle>)"
  using one_imp_ctxt_closed [of "{(x, y). ackbo x y}", to_pred, OF ackbo_mono_one, THEN ctxt.closedD, to_pred] assms by blast


(*
    Section: Closed under substitution for ackbo, above lemmas are more general for the last case (case 3)
*)

lemma ackbo_subst:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "ackbo s t"
  shows "ackbo (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  using assms
proof (induct s arbitrary: t rule: subterm_induct)
  case (subterm s t)
  then show ?case
  proof (cases s)
    case (Var x)
    then show ?thesis using subterm(2) ackbo_lhs_var_false by blast
  next
    case (Fun f fs)
    then have wt:"weight t \<le> weight (Fun f fs)" using subterm(2) ackbo_weight_eq by fastforce
    have vt:"vars_term_ms t \<subseteq># vars_term_ms (Fun f fs)" using Fun subterm(2) ackbo.simps by blast
    have vars_sub:"vars_term_ms (t \<cdot> \<sigma>) \<subseteq># vars_term_ms (s \<cdot> \<sigma>)" using vt Fun vars_term_ms_subst_mono by blast
    then consider (a) "weight (Fun f fs \<cdot> \<sigma>) > weight (t \<cdot> \<sigma>)"| (b) "weight (Fun f fs \<cdot> \<sigma>) = weight (t \<cdot> \<sigma>)" 
      using weight_stable_le[OF wt vt] dual_order.strict_iff_order by blast 
    then show ?thesis
    proof cases
      case a
      then show ?thesis using vars_sub using case_w local.Fun by blast
    next
      case b
      let ?ac_rel = "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
      have wt_eq:"weight t = weight (Fun f fs)" using b weight_stable_lt wt by (metis nat_less_le vt) 
      show ?thesis using subterm(2)
      proof cases
        case case_w
        then show ?thesis by (simp add: Fun wt_eq) 
      next
        case case_0
        then show ?thesis using ackbo_subterm_property Fun ackbo_case0_subterm by (metis case0_adm_var supt_subst) 
      next
        case (case_1 f ts g ys)
        then show ?thesis using eval_term.simps(2) b vars_sub Fun ackbo.simps length_map
          by (auto simp add: ackbo.case_1) 
      next
        case (case_2 f ts g ys)
        then have lext:"fst (lex_ext (\<lambda> x y. ((x,y) \<in> {(u,v). ackbo u v}, (x, y) \<in> ?ac_rel)) (length ts) ts ys)"
          by auto 
        have local_subst_c:"\<And>u v. u \<in> set ts \<Longrightarrow> v \<in> set ys \<Longrightarrow> (u, v) \<in> {(x, y). ackbo x y} \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> {(x, y). ackbo x y}"
          using subterm(1) case_2 by blast
        have local_subst_ac:"\<And>s t. s \<in> set ts \<Longrightarrow> t \<in> set ys \<Longrightarrow> (s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*" by (simp add: acstep_closed_subst) 
        have l: "length ts = length ys" using case_2 Fun by linarith 
        moreover have len: "length (map (\<lambda>t. t \<cdot> \<sigma>) ts) = length ys \<and> length (map (\<lambda>t. t \<cdot> \<sigma>) ys) = length ys" by (simp add: case_2(6)) 
        have "fst (lex_ext (\<lambda> x y. (ackbo x y, (x, y) \<in> ?ac_rel)) (length (map (\<lambda>t. t \<cdot> \<sigma>) ts)) (map (\<lambda>t. t \<cdot> \<sigma>) ts) (map (\<lambda>t. t \<cdot> \<sigma>) ys))"
          using list_ext_pres_sub_closer[OF lext local_subst_ac local_subst_c l] by auto
        then show ?thesis using ackbo.case_2 case_2
          by (smt b len local.Fun map_eq_conv eval_term.simps(2) vars_sub) 
      next
        case (case_3 f fs g ys)
        let ?S = "actop f (Fun f fs)"
        let ?T = "actop f t"
        let ?S' = "actop f (Fun f fs \<cdot> \<sigma>)"
        let ?T' = "actop f (t \<cdot> \<sigma>)"
        let ?ackbo_rel = "{(s,t). ackbo s t}"
        let ?f = "(f,2)"
        have acsym:"f \<in> AC" using case_3 by fastforce
        obtain f1 f2 where term_s:"s = Fun f [f1, f2]" using case_3 by (metis (no_types, lifting) length_0_conv length_Suc_conv numeral_2_eq_2)
        obtain t1 t2 where term_t:"t = Fun f [t1, t2]" using case_3 by (metis (no_types, lifting) length_0_conv length_Suc_conv numeral_2_eq_2)
        have "actop f (Fun f fs) \<noteq> {#Fun f fs#} \<and> actop f t \<noteq> {#t#}" using case_3 term_s term_t by (metis local.Fun multi_member_last trivial_Bin_facts(5)) 
        then have local_subst_c:"\<And>u v. u \<in># actop f (Fun f fs) \<Longrightarrow> v \<in># actop f t \<Longrightarrow> (u, v) \<in> {(x, y). ackbo x y} \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> {(x, y). ackbo x y}"
          using subterm(1) actop_impl_subterm by (metis case_prodD case_prodI case_3 mem_Collect_eq) 
        then have "ac_case_filtered_rel (actop f (s \<cdot> \<sigma>)) (actop f (t \<cdot> \<sigma>)) (f, length fs) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x, y). ackbo x y}"
          using ac_case_subst_closed[OF _ _ _ _ case_3(9)]
          by (metis (no_types, opaque_lifting) ackbo_order_pair ackbo_subterm_property case_prodI conversion_subst_closed case_3(3) mem_Collect_eq) 
        then show ?thesis using vars_sub b case_3
          by (metis admissible_weight_fun_ac.case_3 admissible_weight_fun_ac_axioms length_map local.Fun eval_term.simps(2)[of Fun]) 
      qed
    qed
  qed
qed

end

end
