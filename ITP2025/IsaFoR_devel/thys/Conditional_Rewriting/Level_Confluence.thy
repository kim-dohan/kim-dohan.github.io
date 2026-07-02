(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015, 2016)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Level Confluence\<close>

theory Level_Confluence
imports
  Conditional_Critical_Pairs
  First_Order_Rewriting.Parallel_Rewriting
begin


subsection \<open>Properties of CTRSs\<close>

lemma right_stable_perm_rhsD:
  assumes "right_stable R" and "\<pi> \<bullet> \<rho> \<in> R" and "i < length (snd \<rho>)"
  shows "(vars_term (clhs \<rho>) \<union> \<Union>(vars_term ` lhss (set (take (Suc i) (snd \<rho>)))) \<union>
    \<Union>(vars_term ` (rhss (set (take i (snd \<rho>)))))) \<inter> vars_term (snd (snd \<rho> ! i)) = {}"
proof -
  have "i < length (snd (\<pi> \<bullet> \<rho>))" using assms by (cases \<rho>; simp add: eqvt)
  with right_stable_rhsD [OF assms(1, 2) this]
    show ?thesis
    by (cases \<rho>; auto simp: eqvt [symmetric] take_map sup.commute sup.left_commute)
qed

lemma right_stable_perm_rhs_cases [consumes 3, case_names lct [linear cterm] gnf [ground nf]]:
  assumes "right_stable R" and "\<pi> \<bullet> \<rho> \<in> R"
    and "t \<in> rhss (set (snd \<rho>))"
  obtains
    (lct) "linear_term t" and "funas_term t \<subseteq> funas_ctrs R - {f. defined (Ru R) f}" |
    (gnf) "ground t" and "t \<in> NF (rstep (Ru R))"
proof -
  have "\<pi> \<bullet> t \<in> rhss (set (snd (\<pi> \<bullet> \<rho>)))"
    using assms(3) and rule_pt.snd_eqvt by (fastforce simp: eqvt [symmetric])
  from assms(1, 2) and this
    show ?thesis by (cases rule: right_stable_rhs_cases) (auto intro: that)
qed

text \<open>The usual definition of infeasibility is a sufficient condition.\<close>
lemma infeasible_sufficient:
  assumes "\<not> (\<exists>\<sigma> n. conds_n_sat R n (cs\<^sub>1 @ cs\<^sub>2) \<sigma>)"
  shows "\<forall>m n. comm ((cstep_n R m)\<^sup>*) ((cstep_n R n)\<^sup>*) \<longrightarrow>
        \<not> (\<exists>\<sigma>. conds_n_sat R m cs\<^sub>1 \<sigma> \<and> conds_n_sat R n cs\<^sub>2 \<sigma>)"
proof -
  { fix m n
    have "\<not> (\<exists>\<sigma>. conds_n_sat R m cs\<^sub>1 \<sigma> \<and> conds_n_sat R n cs\<^sub>2 \<sigma>)"
    using assms and conds_n_sat_mono [of m "max m n"] and conds_n_sat_mono [of n "max m n"] by force }
  then show ?thesis by blast
qed

definition level_confluent :: "('f, 'v) ctrs \<Rightarrow> bool"
where
  "level_confluent R \<longleftrightarrow> (\<forall> n. CR (cstep_n R n))"

(*unused*)
lemma cstep_n_varpeak:
  assumes "CCP R = {}" and rule1: "((l, r), cs) \<in> R"
    and "linear_term l"
    and l_\<sigma>: "l \<cdot> \<sigma> = C\<langle>t\<rangle>" and "C \<noteq> \<box>" and cstep: "(t, u) \<in> cstep_n R n"
  shows "\<exists>\<tau>. l \<cdot> \<tau> = C\<langle>u\<rangle> \<and> subst_domain \<tau> \<subseteq> vars_term l \<and>
    (\<forall>x \<in> vars_term l. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*)"
proof -
  from cstep [THEN cstep_nE] obtain D l\<^sub>2 r\<^sub>2 \<sigma>\<^sub>2 cs\<^sub>2 k
    where rule2: "((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R" and [simp]: "n = Suc k"
    and conds: "conds_n_sat R k cs\<^sub>2 \<sigma>\<^sub>2"
    and t: "t = D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" and u: "u = D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
    unfolding conds_n_sat_iff by metis (*only metis works; investigate!*)
  define p where "p \<equiv> hole_pos C @ hole_pos D"
  have *: "p \<in> poss (l \<cdot> \<sigma>)" by (simp add: assms t p_def)
  show ?thesis
  proof (cases "p \<in> fun_poss l")
    case False
    with * obtain q\<^sub>1 q\<^sub>2 x
      where p: "p = q\<^sub>1 @ q\<^sub>2" and q\<^sub>1: "q\<^sub>1 \<in> poss l"
      and lq\<^sub>1: "l |_ q\<^sub>1 = Var x" and q\<^sub>2: "q\<^sub>2 \<in> poss (\<sigma> x)"
        by (rule poss_subst_apply_term)
    moreover
    have [simp]: "l \<cdot> \<sigma> |_ p = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using assms p_def t by auto 
    ultimately
    have [simp]: "\<sigma> x |_ q\<^sub>2 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" by simp
    
    define \<tau> where "\<tau> \<equiv> \<lambda>y. if y = x then replace_at (\<sigma> x) q\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2) else (\<sigma> |s vars_term l) y"
    have \<tau>_x: "\<tau> x = replace_at (\<sigma> x) q\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)" by (simp add: \<tau>_def)
    have [simp]: "\<And>y. y \<in> vars_term l \<Longrightarrow> y \<noteq> x \<Longrightarrow> \<tau> y = \<sigma> y" by (simp add: \<tau>_def)
    have "(\<sigma> x, \<tau> x) \<in> cstep_n R n"
    proof -
      let ?C = "ctxt_of_pos_term q\<^sub>2 (\<sigma> x)"
      have "(?C\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>, ?C\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>) \<in> cstep_n R n"
        using conds by (auto intro!: cstep_n_SucI rule2 simp: conds_n_sat_iff)
      then show ?thesis using q\<^sub>2 by (simp add: \<tau>_def replace_at_ident)
    qed
    then have "\<forall>x \<in> vars_term l. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*" by (auto simp: \<tau>_def)
    moreover have "subst_domain \<tau> \<subseteq> vars_term l"
      using lq\<^sub>1 and vars_term_subt_at [OF q\<^sub>1]
      by (auto simp: subst_domain_def \<tau>_def subst_restrict_def)
    moreover have "l \<cdot> \<tau> = C\<langle>u\<rangle>"
    proof -
      have [simp]: "ctxt_of_pos_term p (l \<cdot> \<sigma>) = C \<circ>\<^sub>c D"
        by (simp add: assms t p_def ctxt_of_pos_term_append)
      have "l \<cdot> \<sigma> |_ q\<^sub>1 = \<sigma> x" by (simp add: lq\<^sub>1 q\<^sub>1)
      from linear_term_replace_in_subst [OF \<open>linear_term l\<close> q\<^sub>1 lq\<^sub>1, of \<sigma> \<tau>, OF _ \<tau>_x, folded ctxt_ctxt_compose]
        and q\<^sub>1 and ctxt_of_pos_term_append [of q\<^sub>1 "l \<cdot> \<sigma>" q\<^sub>2, folded p, unfolded this, symmetric]
        show "l \<cdot> \<tau> = C\<langle>u\<rangle>" by (simp add: u)
    qed
    ultimately show ?thesis by blast
  next
    case True
    from vars_crule_disjoint obtain \<pi>\<^sub>1
      where \<pi>\<^sub>1: "vars_crule (\<pi>\<^sub>1 \<bullet> ((l, r), cs)) \<inter> vars_crule ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) = {}" ..
    define l\<^sub>1 r\<^sub>1 cs\<^sub>1 \<sigma>\<^sub>1 where "l\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> l" and "r\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> r"
      and "cs\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> cs" and "\<sigma>\<^sub>1 \<equiv> sop (-\<pi>\<^sub>1) \<circ>\<^sub>s \<sigma>"
    note rename = l\<^sub>1_def r\<^sub>1_def cs\<^sub>1_def \<sigma>\<^sub>1_def
  
    have *: "-\<pi>\<^sub>1 \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R" and "0 \<bullet> ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R"
      using rule1 and rule2 by (simp_all add: eqvt rename o_def)
    then have rule_variants: "\<exists>\<pi>. \<pi> \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R" "\<exists>\<pi>. \<pi> \<bullet> ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R" by blast+
  
    have disj: "vars_crule ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<inter> vars_crule ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) = {}"
      using \<pi>\<^sub>1 by (auto simp: eqvt rename)
  
    from True have fun_poss: "p \<in> fun_poss (clhs ((l\<^sub>1, r\<^sub>1), cs\<^sub>1))" by (simp add: rename)
    then have "p \<in> poss l\<^sub>1" by (auto dest: fun_poss_imp_poss)
    with vars_term_subt_at [OF this] and disj and l_\<sigma>
      have "vars_term (l\<^sub>1 |_ p) \<inter> vars_term l\<^sub>2 = {}" and "(l\<^sub>1 |_ p) \<cdot> \<sigma>\<^sub>1 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
      by (auto simp: eqvt vars_crule_def vars_rule_def rename)
         (metis hole_pos_poss p_def subt_at_append subt_at_hole_pos subt_at_subst t)
    from vars_term_disjoint_imp_unifier [OF this]
      obtain \<mu> where mgu: "mgu (l\<^sub>1 |_ p) l\<^sub>2 = Some \<mu>"
      using mgu_complete by (auto simp: unifiers_def)
     
     have "p \<noteq> []" using \<open>C \<noteq> \<box>\<close> by (cases C) (simp_all add: p_def)
     with CCP_I [OF rule_variants disj fun_poss] and mgu and \<open>CCP R = {}\<close>
       show ?thesis by auto
  qed
qed


subsection \<open>Extended Parallel Rewriting\<close>

definition "epar_n_mctxt R n C =
  {(s, t). \<exists>ss ts. s =\<^sub>f (C, ss) \<and> t =\<^sub>f (C, ts) \<and>
    (\<forall>i<length ss. (ss ! i, ts ! i) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*)}"

definition epar_n :: "('f, 'v) ctrs => nat => ('f, 'v) term rel"
where
  "epar_n R n =
  {(s, t). \<exists>C ss ts. s =\<^sub>f (C, ss) \<and> t =\<^sub>f (C, ts) \<and>
    (\<forall>i<length ss. (ss ! i, ts ! i) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*)}"

lemma epar_n_epar_n_mctxt_conv:
  "(s, t) \<in> epar_n R n \<longleftrightarrow> (\<exists>C. (s, t) \<in> epar_n_mctxt R n C)"
  by (auto simp: epar_n_def epar_n_mctxt_def)

lemma epar_n_0 [simp]:
  "epar_n R 0 = Id"
by (auto simp: epar_n_def eq_fill.simps list_eq_iff_nth_eq intro: arg_cong)
   (metis eqfE mctxt_of_term)

lemma epar_n_SucE:
  assumes "(s, t) \<in> epar_n R (Suc n)"
  obtains C ss ts where "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "length ss = length ts"
    and "\<forall>i<length ss. (ss ! i, ts ! i) \<in> trs_n R (Suc n) \<union> (cstep_n R n)\<^sup>*"
proof -
  obtain C ss ts where "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "\<forall>i<length ss. (ss ! i, ts ! i) \<in> trs_n R (Suc n) \<union> (cstep_n R n)\<^sup>*"
    using assms by (auto simp: epar_n_def)
  then have "length ss = length ts" by (auto dest!: eqfE)
  show ?thesis by (rule) fact+
qed

lemma epar_n_mctxt_SucE:
  assumes "(s, t) \<in> epar_n_mctxt R (Suc n) C"
  obtains ss ts where "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "length ss = length ts"
    and "\<forall>i<length ss. (ss ! i, ts ! i) \<in> trs_n R (Suc n) \<union> (cstep_n R n)\<^sup>*"
using assms by (auto simp: epar_n_mctxt_def elim!: eq_fill.cases) (metis eqf_refl)

lemma epar_n_mctxtI:
  assumes "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*"
  shows "(s, t) \<in> epar_n_mctxt R n C"
  using assms by (auto simp: epar_n_mctxt_def)

lemma epar_nI:
  assumes "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*"
  shows "(s, t) \<in> epar_n R n"
  using assms by (auto simp: epar_n_def)

lemma trs_n_subset_epar_n:
  "trs_n R n \<subseteq> epar_n R n"
  by (auto intro!: epar_nI [of s MHole "[s]" t "[t]" R n for s t])

lemma epar_n_par_rstep_1_conv:
  "epar_n R 1 = par_rstep (trs_n R 1)"
  by (auto simp: epar_n_def) (force intro: par_rstep_mctxt par_rstep_id dest: par_rstep_mctxtD)+

lemma cstep_n_subset_epar_n:
  "cstep_n R n \<subseteq> epar_n R n"
proof
  fix s t
  assume "(s, t) \<in> cstep_n R n"
  then obtain C \<sigma> l r where [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and [simp]:"t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and "(l, r) \<in> trs_n R n"
    unfolding "cstep_n_rstep_trs_n_conv" by fast
  then have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> trs_n R n" using trs_n_subst by fast
  then show "(s, t) \<in> epar_n R n"
    by (auto intro: epar_nI[OF mctxt_of_ctxt mctxt_of_ctxt])
qed

lemma epar_n_NF_imp_cstep_n_NF:
  "t \<in> NF (epar_n R n) \<Longrightarrow> t \<in> NF (cstep_n R n)"
using NF_anti_mono [OF cstep_n_subset_epar_n] by blast

lemma epar_n_subset_csteps_n:
  "epar_n R n \<subseteq> (cstep_n R n)\<^sup>*"
proof (cases n)
  case (Suc k)
  then show ?thesis
    using rtrancl_mono [OF rstep_mono [OF trs_n_Suc_mono [of R k]]]
    by (auto elim!: epar_n_SucE simp: cstep_n_rstep_trs_n_conv) (rule rsteps_mctxt, auto+)
qed simp

lemma epars_n_subset_csteps_n:
  "(epar_n R n)\<^sup>* \<subseteq> (cstep_n R n)\<^sup>*"
using rtrancl_mono [OF epar_n_subset_csteps_n] and rtrancl_idemp by auto

lemma epar_n_refl [simp]:
  "(t, t) \<in> epar_n R n"
by (auto simp: epar_n_def intro: mctxt_of_term)

lemma refl_epar_n:
  "refl (epar_n R n)"
by (simp add: refl_on_def)

lemma csteps_n_subset_epar_n_Suc:
  "(cstep_n R n)\<^sup>* \<subseteq> epar_n R (Suc n)"
proof
  fix s t
  assume "(s, t) \<in> (cstep_n R n)\<^sup>*"
  then show "(s, t) \<in> epar_n R (Suc n)"
  proof (induct)
    case (step t u)
    then show ?case
      by (intro epar_nI [of _ MHole "[s]" _ "[u]"])
         (auto elim!: epar_n_SucE dest: rtrancl_into_rtrancl)
  qed simp
qed

lemma epar_n_Suc_mono:
  "epar_n R n \<subseteq> epar_n R (Suc n)"
using epar_n_subset_csteps_n csteps_n_subset_epar_n_Suc by blast

lemma rtrancl_epar_n_conv:
  "(epar_n R n)\<^sup>* = (cstep_n R n)\<^sup>*"
by (intro rtrancl_subset cstep_n_subset_epar_n epar_n_subset_csteps_n)

lemma epar_n_rtrancl_Suc_mono:
  "(epar_n R n)\<^sup>* \<subseteq> epar_n R (Suc n)"
using rtrancl_mono [OF epar_n_subset_csteps_n]
  and csteps_n_subset_epar_n_Suc by (simp) blast

lemma epar_n_mono:
  assumes "n \<le> m"
  shows "epar_n R n \<subseteq> epar_n R m"
using assms
proof (induct "m - n" arbitrary: n)
  case (Suc k)
  then have "k = m - (Suc n)" and "Suc n \<le> m" by arith+
  from Suc.hyps(1) [OF this]
    show ?case using epar_n_Suc_mono by blast
qed simp

definition "epar R = (\<Union>n. epar_n R n)"

lemma epar_iff:
  "(s, t) \<in> epar R \<longleftrightarrow> (\<exists>n. (s, t) \<in> epar_n R n)"
  by (auto simp: epar_def)

lemma all_ctxt_closed_epar_n [simp]:
  "all_ctxt_closed UNIV (epar_n R n)"
proof -
  { fix f ts ss
    assume [simp]: "length ts = length ss"
      and "\<forall>i<length ss. (ts ! i, ss ! i) \<in> epar_n R n"
    then have "\<forall>i<length ss. \<exists>C us vs.
      ts ! i =\<^sub>f (C, us) \<and> ss ! i =\<^sub>f (C, vs) \<and>
      (\<forall>i < length us. (us ! i, vs ! i) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*)"
      (is "\<forall>i<length ss. \<exists>C us vs. ?P i C us vs") by (auto simp: epar_n_def)
    then have "\<forall>i<length ss. \<exists>x. ?P i (fst x) (fst (snd x)) (snd (snd x))" by force
    then obtain c where "\<forall>i<length ss. ?P i (fst (c i)) (fst (snd (c i))) (snd (snd (c i)))"
      unfolding choice_iff' by blast
    moreover
    define Cs us vs where "Cs \<equiv> map (fst \<circ> c) [0 ..< length ss]"
      and "us \<equiv> map (fst \<circ> snd \<circ> c) [0 ..< length ss]"
      and  "vs \<equiv> map (snd \<circ> snd \<circ> c) [0 ..< length ss]"
    ultimately have [simp]: "length Cs = length ts" "length us = length ts" "length vs = length ts"
      and *: "\<forall>i<length ss. ?P i (Cs ! i) (us ! i) (vs ! i)"
      by (simp_all)
    define C where "C \<equiv> MFun f Cs"
    have "Fun f ts =\<^sub>f (C, concat us)" and "Fun f ss =\<^sub>f (C, concat vs)"
    using * by (auto simp: C_def intro: eqf_MFunI)
  moreover have "\<forall>i<length (concat us). (concat us ! i, concat vs ! i) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*"
    using * by (intro concat_all_nth) (auto simp: eq_fill.simps)
  ultimately have "(Fun f ts, Fun f ss) \<in> epar_n R n" by (auto intro!: epar_nI) }
  then show ?thesis by (auto simp: all_ctxt_closed_def)
qed

lemma epar_n_mctxt:
  assumes "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)"
    and "\<forall>i<length ss. (ss ! i, ts ! i) \<in> epar_n R n"
  shows "(s, t) \<in> epar_n R n"
proof -
  have [simp]: "length ss = length ts" using assms by (auto dest!: eqfE)
  have [simp]: "t = fill_holes C ts" using assms by (auto dest: eqfE)
  have "(s, fill_holes C ts) \<in> epar_n R n"
    using assms by (intro eqf_all_ctxt_closed_step [of UNIV _ s C ss, THEN conjunct1]) auto
  then show ?thesis by simp
qed

lemma epar_n_mctxt_mctxt:
  assumes "s =\<^sub>f (C, ss)" and "t =\<^sub>f (C, ts)" and "length Cs = length ss"
    and "\<forall>i < length ss. (ss ! i, ts ! i) \<in> epar_n_mctxt R n (Cs ! i)"
  shows "(s, t) \<in> epar_n_mctxt R n (fill_holes_mctxt C Cs)"
proof -
  have "\<forall>i < length ss. \<exists>us vs. ss ! i =\<^sub>f (Cs ! i, us) \<and> ts ! i =\<^sub>f (Cs ! i, vs) \<and>
    (\<forall>j < length us. (us ! j, vs ! j) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*)"
    using assms by (auto simp: epar_n_mctxt_def)
  then obtain f and g where *: "\<forall>i < length ss. ss ! i =\<^sub>f (Cs ! i, f i) \<and> ts ! i =\<^sub>f (Cs ! i, g i)"
    and **: "\<forall>i < length ss.
    (\<forall>j < length (f i). (f i ! j, g i ! j) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*)" by metis
  moreover define sss tss where "sss \<equiv> map f [0 ..< length ss]" and "tss \<equiv> map g [0 ..< length ss]"
  ultimately have "s =\<^sub>f (fill_holes_mctxt C Cs, concat sss)"
    and "t =\<^sub>f (fill_holes_mctxt C Cs, concat tss)"
    using assms by (auto intro: fill_holes_mctxt_sound elim!: eq_fill.cases)
  moreover
  { fix i
    assume "i < length (concat sss)"
    from less_length_concat [OF this] obtain j k
      where 2: "j < length sss" "k < length (sss ! j)"
        "i = sum_list (map length (take j sss)) + k"
        "concat sss ! i = sss ! j ! k" by blast
    moreover have 3: "j < length tss" "k < length (tss ! j)"     
      using * 2 by (auto simp: sss_def tss_def dest!: eqfE)
    have "i = sum_list (map length (take j tss)) + k" unfolding 2
      apply (intro arg_cong[of _ _ "\<lambda> xs. sum_list xs + k"])
      apply (intro nth_equalityI, insert 2 * 3, auto simp: sss_def tss_def)
      by (metis add_lessD1 canonically_ordered_monoid_add_class.lessE eqfE(2))    
    moreover from concat_nth [OF 3 this] have "concat tss ! i = tss ! j ! k" .
    ultimately have "(concat sss ! i, concat tss ! i) \<in> trs_n R n \<union> (cstep_n R (n - 1))\<^sup>*"
      using ** by (auto simp: sss_def tss_def) }
  ultimately show ?thesis by (rule epar_n_mctxtI)
qed

lemma Var_epar_n [dest]:
  assumes "(Var x, t) \<in> epar_n R n"
    and "\<forall>((l, r), cs) \<in> R. is_Fun l"
  shows "t = Var x"
using assms
by (cases n)
   (force elim!: epar_n_SucE eq_fill.cases fill_holes_eq_Var_cases intro: fill_holes_MHole)+

lemma subst_epar_n_imp_epar_n:
  fixes \<sigma> \<tau> :: "('f, 'v) subst"
  assumes "\<forall>x \<in> vars_term t. (\<sigma> x, \<tau> x) \<in> epar_n R n"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> epar_n R n"
using assms by (intro all_ctxt_closed_subst_step) simp_all

lemma epar_n_ctxt:
  assumes "(s, t) \<in> epar_n R n"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> epar_n R n"
using epar_n_mctxt [of "C\<langle>s\<rangle>" "mctxt_of_ctxt C" "[s]" "C\<langle>t\<rangle>" "[t]" R n]
  and assms by simp

lemma epar_n_rtrancl_all_ctxt_closed [simp]:
  "all_ctxt_closed UNIV ((epar_n R n)\<^sup>*)"
by (rule trans_ctxt_imp_all_ctxt_closed)
   (auto simp: ctxt.closed_def elim!: ctxt.closure.cases intro: refl_rtrancl trans_rtrancl epar_n_ctxt [THEN rtrancl_map])

lemma subst_epar_n_imp_epar_n_rtrancl:
  fixes \<sigma> \<tau> :: "('f, 'v) subst"
  assumes "\<forall>x \<in> vars_term t. (\<sigma> x, \<tau> x) \<in> (epar_n R n)\<^sup>*"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (epar_n R n)\<^sup>*"
using assms by (intro all_ctxt_closed_subst_step) simp_all

lemma linear_term_epar_n_mctxt_cases':
  fixes s :: "('f, 'v) term" and \<sigma> :: "('f, 'v) subst"
  assumes "linear_term s"
    and "(s \<cdot> \<sigma>, t) \<in> epar_n_mctxt R (Suc n) C"
  shows "(\<exists>\<tau>. t = s \<cdot> \<tau> \<and> (\<forall>x. (\<sigma> x, \<tau> x) \<in> epar_n R (Suc n))) \<or>
    (\<exists>\<tau> u p q. p \<in> hole_poss C \<and> p @ q \<in> fun_poss s \<and>
      (\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*) \<and>
      (s \<cdot> \<tau> |_ (p @ q), u) \<in> trs_n R (Suc n))"
    (is "(\<exists>\<tau>. ?P1 \<tau> s t) \<or> _" is "?P C s t")
using assms
proof (induction s arbitrary: C t)
  case (Var x C t)
  then show ?case
    using epar_n_epar_n_mctxt_conv [THEN iffD2, of _ _ R]
    by (intro disjI1 exI [of _ "\<lambda>y. if x = y then t else \<sigma> y"]) auto
next
  case (Fun f ss)
  from epar_n_mctxt_SucE [OF Fun.prems(2)] obtain ts us
    where eqf: "Fun f ss \<cdot> \<sigma> =\<^sub>f (C, ts)" "t =\<^sub>f (C, us)" and [simp]: "length ts = length us"
    and *: "\<forall>i < length ts. (ts ! i, us ! i) \<in> trs_n R (Suc n) \<union> (cstep_n R n)\<^sup>*" by blast
  show ?case
  proof (cases "C = MHole")
    case True
    with * have "(Fun f ss \<cdot> \<sigma>, t) \<in> trs_n R (Suc n) \<union> (cstep_n R n)\<^sup>*"
      using eqf by (cases ts) (auto elim!: eq_fill.cases simp: Suc_length_conv)
    then show ?thesis
    proof
      assume "(Fun f ss \<cdot> \<sigma>, t) \<in> trs_n R (Suc n)"
      with True have "[] \<in> hole_poss C"
        and "[] @ [] \<in> fun_poss (Fun f ss)"
        and "(Fun f ss \<cdot> \<sigma> |_ ([] @ []), t) \<in> trs_n R (Suc n)" by auto
      then show ?thesis by blast
    next
      assume "(Fun f ss \<cdot> \<sigma>, t) \<in> (cstep_n R n)\<^sup>*"
      with Fun.prems(1) show ?thesis
      proof (cases rule: linear_term_rtrancl_cstep_n_cases)
        case (var_poss \<tau>)
        then show ?thesis using csteps_n_subset_epar_n_Suc [of R n] by blast
      next
        case (fun_poss \<tau> q u)
        moreover then have "[] @ q \<in> fun_poss (Fun f ss)"
          and "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*"
          and "(Fun f ss \<cdot> \<tau> |_ ([] @ q), u) \<in> trs_n R n"
          using fun_poss_imp_poss [THEN vars_term_subt_at, of q "Fun f ss"] by auto
        moreover have "[] \<in> hole_poss C" by (simp add: True)
        ultimately show ?thesis using trs_n_Suc_mono [of R n] by blast
      qed
    qed
  next
    case False
    then obtain Cs where C: "C = MFun f Cs"
      and [simp]: "length Cs = length ss" "sum_list (map num_holes Cs) = length ts"
      and eqfs: "\<forall>i < length ss. (ss ! i) \<cdot> \<sigma> =\<^sub>f (Cs ! i, partition_holes ts Cs ! i)"
      using eqf by (cases C) (auto dest!: eqf_Fun_MFun elim: eq_fill.cases)
    let ?ts = "partition_holes ts Cs"
    let ?us = "partition_holes us Cs"
    let ?u = "\<lambda>i. fill_holes (Cs ! i) (?us ! i)"
    have "\<forall>i < length ts. (ts ! i, us ! i) \<in> epar_n_mctxt R (Suc n) MHole"
      using * by (auto intro!: epar_n_mctxtI [of s MHole "[s]" t "[t]" for s t])
    then have "\<forall>i < length ts. (concat ?ts ! i, concat ?us ! i) \<in> epar_n_mctxt R (Suc n) MHole"
      by (simp)
    then have **: "\<forall>i < length ss. (\<forall>j < length (?ts ! i). (?ts ! i ! j, ?us ! i ! j) \<in> epar_n_mctxt R (Suc n) MHole)"
      using concat_nth_length [of _ ?ts]
      by (auto simp: concat_nth_length partition_by_nth_nth take_map [symmetric])
    { fix i assume "i < length ss"
      then have "((ss ! i) \<cdot> \<sigma>, ?u i) \<in>
        epar_n_mctxt R (Suc n) (fill_holes_mctxt (Cs ! i) (replicate (num_holes (Cs ! i)) MHole))"
        using eqfs and ** by (intro epar_n_mctxt_mctxt) (auto elim!: eq_fill.cases) }
    with Fun(1, 2) have IH: "\<forall>i < length ss. ?P (Cs ! i) (ss ! i) (?u i)" by auto
    show ?thesis
    proof (cases "\<forall>i < length ss. (\<exists>\<tau>. ?P1 \<tau> (ss ! i) (?u i))")
      case False
      then obtain i and \<tau> and u and p and q where "i < length ss"
        and "p \<in> hole_poss (Cs ! i)" and "p @ q \<in> fun_poss (ss ! i)"
        and "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*"
        and "((ss ! i) \<cdot> \<tau> |_ (p @ q), u) \<in> trs_n R (Suc n)"
        using IH by blast
      moreover then have "i # p \<in> hole_poss C" and "(i # p) @ q \<in> fun_poss (Fun f ss)"
        and "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*"
        and "(Fun f ss \<cdot> \<tau> |_ ((i # p) @ q), u) \<in> trs_n R (Suc n)" by (auto simp: C)
      ultimately show ?thesis by blast
    next
      case True
      then obtain \<tau> where **: "\<forall>i < length ss. ?P1 (\<tau> i) (ss ! i) (?u i)"
        unfolding choice_iff' [of "\<lambda>i. i < length ss"] by auto
      have "is_partition (map vars_term ss)" using \<open>linear_term (Fun f ss)\<close> by simp
      from subst_merge [OF this, of \<tau>] obtain \<mu>
        where [simp]: "\<And>i x. i < length ss \<Longrightarrow> x \<in> vars_term (ss ! i) \<Longrightarrow> \<mu> x = \<tau> i x" by blast
      then have [simp]: "\<And>i. i < length ss \<Longrightarrow> ss ! i \<cdot> \<tau> i = ss ! i \<cdot> \<mu>"
        by (simp add: term_subst_eq_conv)
      let ?\<mu> = "\<lambda>x. if x \<in> vars_term (Fun f ss) then \<mu> x else \<sigma> x"
      have "t = Fun f ss \<cdot> ?\<mu>"
      proof -
        from eqf have "t = fill_holes C us" by (auto dest: eqfE)
        moreover have "\<forall>i < length Cs. fill_holes (Cs ! i) (?us ! i) = (ss ! i) \<cdot> ?\<mu>"
          using ** by (auto intro!: term_subst_eq simp: subst_restrict_def)
        ultimately show ?thesis
          by (auto simp del: fill_holes.simps simp: C partition_holes_fill_holes_conv
                   intro: nth_map_conv)
      qed
      moreover have "\<forall>x. (\<sigma> x, ?\<mu> x) \<in> epar_n R (Suc n)"
        using ** by (auto dest: in_set_idx)
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma linear_term_epar_n_mctxt_cases [consumes 2]:
  fixes s :: "('f, 'v) term" and \<sigma> :: "('f, 'v) subst"
  assumes "linear_term s"
    and "(s \<cdot> \<sigma>, t) \<in> epar_n_mctxt R (Suc n) C"
  obtains (var_poss) \<tau> where "t = s \<cdot> \<tau>"
    and "\<forall>x. (\<sigma> x, \<tau> x) \<in> epar_n R (Suc n)"
  | (fun_poss) \<tau> u p q where "p \<in> hole_poss C" and "p @ q \<in> fun_poss s"
    and "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*"
    and "(s \<cdot> \<tau> |_ (p @ q), u) \<in> trs_n R (Suc n)"
using linear_term_epar_n_mctxt_cases' [OF assms] by blast

lemma linear_term_epar_n_cases [consumes 2]:
  fixes s :: "('f, 'v) term" and \<sigma> :: "('f, 'v) subst"
  assumes "linear_term s"
    and "(s \<cdot> \<sigma>, t) \<in> epar_n R (Suc n)"
  obtains (var_poss) \<tau> where "t = s \<cdot> \<tau>" and "\<forall>x. (\<sigma> x, \<tau> x) \<in> epar_n R (Suc n)"
  | (fun_poss) \<tau> u p where "p \<in> fun_poss s" and "(s \<cdot> \<tau> |_ p, u) \<in> trs_n R (Suc n)"
using assms by (auto simp: epar_n_epar_n_mctxt_conv elim!: linear_term_epar_n_mctxt_cases)

definition "supports_linear_cases R S \<longleftrightarrow> (\<forall>s (\<sigma>::('f, 'v) subst) t P.
  linear_term s \<longrightarrow> (s \<cdot> \<sigma>, t) \<in> S \<longrightarrow>
  (\<forall>\<tau>. s \<cdot> \<tau> = t \<longrightarrow> (\<forall>x. (\<sigma> x, \<tau> x) \<in> S) \<longrightarrow> P) \<longrightarrow>
  (\<forall>\<tau> p u n. p \<in> fun_poss s \<longrightarrow> (s \<cdot> \<tau> |_ p, u) \<in> trs_n R n \<longrightarrow> P) \<longrightarrow> P)"

lemma supports_linear_cases [consumes 3]:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "supports_linear_cases R S" and "linear_term s" and "(s \<cdot> \<sigma>, t) \<in> S"
  obtains (var_poss) \<tau> where "s \<cdot> \<tau> = t" and "\<forall>x. (\<sigma> x, \<tau> x) \<in> S"
  | (fun_poss) \<tau> p u n where "p \<in> fun_poss s" and "(s \<cdot> \<tau> |_ p, u) \<in> trs_n R n"
using assms unfolding supports_linear_cases_def by metis

lemma conds_n_sat_extend_subst:
  fixes R :: "('f, 'v::{infinite}) ctrs"
  assumes linear_cases: "supports_linear_cases R S"
    and refl: "refl S"
    and acc: "all_ctxt_closed UNIV S"
    and S_imp_csteps: "S \<subseteq> (cstep R)\<^sup>*"
    and comm: "comm ((cstep_n R m)\<^sup>*) S"
    and vars: "\<forall>((l, r), cs) \<in> R. is_Fun l"
    and rs: "right_stable R"
    and rule: "\<pi> \<bullet> ((l, r), cs) \<in> R"
    and "\<forall>x. (\<sigma> x, \<tau> x) \<in> S"
    and conds: "conds_n_sat R m cs \<sigma>"
  obtains \<delta> where "\<forall>x \<in> vars_term l. \<delta> x = \<tau> x" and "conds_n_sat R m cs \<delta>"
    and "\<forall>x \<in> vars_term l \<union> \<Union>(vars_rule ` set cs). (\<sigma> x, \<delta> x) \<in> S"
proof -
  have [simp]: "\<And>x. (x, x) \<in> S" using refl by (simp add: refl_on_def)
  let ?c = "\<lambda>i. take i cs"
  let ?V = "\<lambda>i. \<Union>(vars_rule ` set (?c i))"
  let ?P\<^sub>1 = "\<lambda>\<delta>. \<forall>x \<in> vars_term l. \<delta> x = \<tau> x"
  let ?P\<^sub>2 = "\<lambda>\<delta> i. conds_n_sat R m (?c i) \<delta>"
  let ?P\<^sub>3 = "\<lambda>\<delta> i. \<forall>x \<in> vars_term l \<union> ?V i. (\<sigma> x, \<delta> x) \<in> S"
  { fix i :: nat
    assume "i \<le> length cs"
    then have "\<exists>\<delta>. ?P\<^sub>1 \<delta> \<and> ?P\<^sub>2 \<delta> i \<and> ?P\<^sub>3 \<delta> i"
    proof (induction i)
      case 0
      show ?case using assms by (intro exI [of _ \<tau>]) (simp add: subst_compose)
    next
      case (Suc i)
      then obtain \<delta>\<^sub>i where [simp]: "?P\<^sub>1 \<delta>\<^sub>i"
        and P\<^sub>2: "?P\<^sub>2 \<delta>\<^sub>i i" and P\<^sub>3: "?P\<^sub>3 \<delta>\<^sub>i i" and i: "i < length cs" by auto

      let ?s = "fst (cs ! i)" and ?t = "snd (cs ! i)"
      have [simp]: "take (Suc i) cs = take i cs @ [(?s, ?t)]"
        using i by (simp add: take_Suc_conv_app_nth)

      define \<delta>' where [simp]: "\<delta>' \<equiv> \<lambda>x. if x \<in> vars_term ?s - (vars_term l \<union> ?V i) then \<sigma> x else \<delta>\<^sub>i x"

      have "(?s \<cdot> \<sigma>, ?t \<cdot> \<sigma>) \<in> (cstep_n R m)\<^sup>*"
        using i and conds by (auto simp: conds_n_sat_iff)
      moreover have "(?s \<cdot> \<sigma>, ?s \<cdot> \<delta>') \<in> S"
        using P\<^sub>3 by (simp add: acc all_ctxt_closed_subst_step)
      ultimately obtain t'
        where n_t': "(?t \<cdot> \<sigma>, t') \<in> S" and m_t': "(?s \<cdot> \<delta>', t') \<in> (cstep_n R m)\<^sup>*"
        using comm by (auto elim: commE)

      have "?t \<in> rhss (set (snd ((l, r), cs)))" using i by auto
      with rs and rule show ?case
      proof (induct rule: right_stable_perm_rhs_cases)
        case (gnf)
        then have "?t \<cdot> \<sigma> = ?t" and "?t \<cdot> \<sigma> \<in> NF (cstep R)"
          by (auto simp: ground_subst_apply dest: Ru_NF_imp_R_NF)
        moreover with n_t' have "?t \<cdot> \<sigma> = t'"
          using S_imp_csteps by (auto dest: intro: NF_not_suc)
        ultimately have t': "t' = ?t \<cdot> \<delta>'" using gnf.ground by (simp add: ground_subst_apply)

        show ?thesis
        proof (intro exI [of _ \<delta>'] conjI)
          { fix s t
            assume *: "(s, t) \<in> set (take i cs)"
            with P\<^sub>2 have "(s \<cdot> \<delta>\<^sub>i, t \<cdot> \<delta>\<^sub>i) \<in> (cstep_n R m)\<^sup>*" by (auto simp: conds_n_sat_iff)
            moreover have "s \<cdot> \<delta>' = s \<cdot> \<delta>\<^sub>i" and "t \<cdot> \<delta>' = t \<cdot> \<delta>\<^sub>i"
              using * by (auto simp: vars_defs term_subst_eq_conv)
            ultimately have "(s \<cdot> \<delta>', t \<cdot> \<delta>') \<in> (cstep_n R m)\<^sup>*" by auto }
          then have "conds_n_sat R m (take i cs) \<delta>'" by (auto simp: conds_n_sat_iff)
          then show "?P\<^sub>2 \<delta>' (Suc i)" using m_t' by (auto simp: t')
        next
          have "vars_term ?t = {}" using gnf by (simp add: ground_vars_term_empty)
          then show "?P\<^sub>3 \<delta>' (Suc i)" using P\<^sub>3 by (auto simp: vars_defs)
        qed simp
      next
        case (lct)
        from linear_cases and lct.linear and n_t' obtain \<gamma>
          where "?t \<cdot> \<gamma> = t'" and *: "\<forall>x. (\<sigma> x, \<gamma> x) \<in> S"
          using no_step_from_constructor [OF vars lct.cterm]
          by (cases rule: supports_linear_cases; blast)

        have inter: "(vars_term l \<union> ?V i \<union> vars_term ?s) \<inter> vars_term ?t = {}"
          using right_stable_perm_rhsD [OF rs rule, of i] by (auto simp: i vars_defs)

        define \<delta> where [simp]: "\<delta> \<equiv> \<lambda>x. (if x \<in> vars_term ?t then \<gamma> x else \<delta>' x)"

        show ?thesis using inter
        proof (intro exI [of _ \<delta>] conjI)
          { fix s t
            assume *: "(s, t) \<in> set (take i cs)"
            with P\<^sub>2 have "(s \<cdot> \<delta>\<^sub>i, t \<cdot> \<delta>\<^sub>i) \<in> (cstep_n R m)\<^sup>*" by (auto simp: conds_n_sat_iff)
            moreover have "s \<cdot> \<delta> = s \<cdot> \<delta>\<^sub>i" and "t \<cdot> \<delta> = t \<cdot> \<delta>\<^sub>i"
              using * and inter by (fastforce simp: vars_defs term_subst_eq_conv)+
            ultimately have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> (cstep_n R m)\<^sup>*" by auto }
          then have [simp]: "conds_n_sat R m (take i cs) \<delta>" using P\<^sub>2 by (auto simp: conds_n_sat_iff)

          have "?s \<cdot> \<delta> = ?s \<cdot> \<delta>'" and "?t \<cdot> \<delta> = ?t \<cdot> \<gamma>"
            using inter by (auto simp: term_subst_eq_conv vars_defs)
          then have "(?s \<cdot> \<delta>, ?t \<cdot> \<delta>) \<in> (cstep_n R m)\<^sup>*" using \<open>?t \<cdot> \<gamma> = t'\<close> and m_t' by simp
          then show "?P\<^sub>2 \<delta> (Suc i)" by (simp del: \<delta>_def)
        next
          show "?P\<^sub>3 \<delta> (Suc i)" using P\<^sub>3 and * by (auto simp: vars_defs)
        qed auto
      qed
    qed }
  then obtain \<delta> where "\<forall>x \<in> vars_term l. \<delta> x = \<tau> x" and "conds_n_sat R m cs \<delta>"
    and "\<forall>x \<in> vars_term l \<union> \<Union>(vars_rule ` set cs). (\<sigma> x, \<delta> x) \<in> S" by force
  then show ?thesis by (intro that) auto
qed

lemma supports_linear_cases_csteps_n:
  "supports_linear_cases R ((cstep_n R n)\<^sup>*)"
unfolding supports_linear_cases_def by (blast elim: linear_term_rtrancl_cstep_n_cases)

lemma epar_n_subset_csteps:
  "epar_n R n \<subseteq> (cstep R)\<^sup>*"
using epar_n_subset_csteps_n and csteps_n_subset_csteps by blast

lemma supports_linear_cases_epar_n:
  "supports_linear_cases R (epar_n R (Suc n))"
unfolding supports_linear_cases_def by (blast elim: linear_term_epar_n_cases)

lemmas conds_n_sat_extend_subst_csteps_n =
  conds_n_sat_extend_subst [OF supports_linear_cases_csteps_n refl_rtrancl
    all_ctxt_closed_csteps_n csteps_n_subset_csteps]

lemmas conds_n_sat_extend_subst_epar_n =
  conds_n_sat_extend_subst [OF supports_linear_cases_epar_n refl_epar_n all_ctxt_closed_epar_n
    epar_n_subset_csteps]

lemma epar_n_varpeak':
  assumes comm: "comm ((cstep_n R m)\<^sup>*) ((cstep_n R n)\<^sup>*)"
    and vars: "\<forall>((l, r), cs) \<in> R. is_Fun l"
    and ao: "almost_orthogonal R"
    and rs: "right_stable R"
    and rule: "((l, r), cs) \<in> R"
    and conds: "conds_n_sat R m cs \<sigma>"
    and l_\<sigma>: "l \<cdot> \<sigma> =\<^sub>f (C, ts)" and "C \<noteq> MHole"
    and epar: "\<forall>i<length ts. (ts ! i, us ! i) \<in> trs_n R (Suc n) \<union> (cstep_n R n)\<^sup>*"
    and len: "length us = length ts"
  shows "\<exists>\<tau>. l \<cdot> \<tau> =\<^sub>f (C, us) \<and> (\<forall>x. (\<sigma> x, \<tau> x) \<in> epar_n R (Suc n))"
proof -
  have "linear_term l" using assms by simp
  have "(l \<cdot> \<sigma>, fill_holes C us) \<in> epar_n_mctxt R (Suc n) C"
    using epar and l_\<sigma> and len
    by (intro epar_n_mctxtI [OF l_\<sigma>, of "fill_holes C us" us]) (auto elim!: eq_fill.cases)
  with \<open>linear_term l\<close> show ?thesis
  proof (cases rule: linear_term_epar_n_mctxt_cases)
    case (var_poss \<tau>)
    moreover then have "l \<cdot> \<tau> =\<^sub>f (C, us)" using l_\<sigma> and len by (auto elim!: eq_fill.cases)
    ultimately show ?thesis by blast
  next
    case (fun_poss \<tau> u p q)
    obtain l\<^sub>2 r\<^sub>2 cs\<^sub>2 \<sigma>\<^sub>2
      where l_\<tau>: "l \<cdot> \<tau> |_ (p @ q) = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" and u: "u = r\<^sub>2 \<cdot> \<sigma>\<^sub>2"
      and rule2: "((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R"
      and conds2: "conds_n_sat R n cs\<^sub>2 \<sigma>\<^sub>2"
        by (rule fun_poss(4) [THEN trs_n_SucE]) (auto simp: cstep_n_rstep_trs_n_conv conds_n_sat_iff)

    from vars_crule_disjoint obtain \<pi>\<^sub>1
      where \<pi>\<^sub>1: "vars_crule (\<pi>\<^sub>1 \<bullet> ((l, r), cs)) \<inter> vars_crule ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) = {}" ..
    define l\<^sub>1 r\<^sub>1 cs\<^sub>1 \<sigma>\<^sub>1 where "l\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> l" and "r\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> r"
      and "cs\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> cs" and "\<sigma>\<^sub>1 \<equiv> sop (-\<pi>\<^sub>1) \<circ>\<^sub>s \<tau>"
    note rename = this

    have rule1: "-\<pi>\<^sub>1 \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R" and "0 \<bullet> ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R"
      using rule and rule2 by (simp_all add: eqvt rename o_def)
    then have rule_variants: "\<exists>\<pi>. \<pi> \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R" "\<exists>\<pi>. \<pi> \<bullet> ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R" by blast+
  
    have disj: "vars_crule ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<inter> vars_crule ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) = {}"
      using \<pi>\<^sub>1 by (auto simp: eqvt rename)

    from fun_poss have fp: "p @ q \<in> fun_poss (clhs ((l\<^sub>1, r\<^sub>1), cs\<^sub>1))" by (simp add: rename)
    then have "p @ q \<in> poss l\<^sub>1" by (auto dest: fun_poss_imp_poss)
    with vars_term_subt_at [OF this] and disj and l_\<tau>
      have "vars_term (l\<^sub>1 |_ (p @ q)) \<inter> vars_term l\<^sub>2 = {}" and "(l\<^sub>1 |_ (p @ q)) \<cdot> \<sigma>\<^sub>1 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
      by (auto simp: vars_crule_def vars_rule_def rename)
         (metis subt_at_eqvt term_pt.permute_minus_cancel(2))
    from vars_term_disjoint_imp_unifier [OF this]
      obtain \<mu> where mgu: "mgu (l\<^sub>1 |_ (p @ q)) l\<^sub>2 = Some \<mu>"
      using mgu_complete by (auto simp: unifiers_def)

    let ?\<sigma> = "\<sigma> \<circ> Rep_perm (-\<pi>\<^sub>1)"
    have "\<forall>x. (?\<sigma> x, \<sigma>\<^sub>1 x) \<in> (cstep_n R n)\<^sup>*" using fun_poss(3) by (simp add: rename subst_compose)
    moreover have "conds_n_sat R m cs\<^sub>1 ?\<sigma>"
      using conds
      by (simp only: rename conds_n_sat_perm_shift o_assoc [symmetric] Rep_perm_add [symmetric])
         (simp add: Rep_perm_0)
    ultimately obtain \<nu>
      where conds1: "conds_n_sat R m cs\<^sub>1 \<nu>" and \<nu>: "\<forall>x \<in> vars_term l\<^sub>1. \<nu> x = \<sigma>\<^sub>1 x"
      using conds_n_sat_extend_subst_csteps_n [OF comm vars rs rule1] by metis

    define \<delta> where "\<delta> \<equiv> \<lambda>x. if x \<in> vars_crule ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) then \<nu> x else \<sigma>\<^sub>2 x"

    from fun_poss have fp: "p @ q \<in> fun_poss (clhs ((l\<^sub>1, r\<^sub>1), cs\<^sub>1))" by (simp add: rename)
    then have pq: "p @ q \<in> poss l\<^sub>1" by (auto dest: fun_poss_imp_poss)
    with vars_term_subt_at [OF pq] and disj and l_\<tau>
      have "(l\<^sub>1 |_ (p @ q)) \<cdot> \<sigma>\<^sub>1 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
      by (auto simp: rename; metis subt_at_eqvt term_pt.permute_minus_cancel(2))
    moreover have "(l\<^sub>1 |_ (p @ q)) \<cdot> \<sigma>\<^sub>1 = (l\<^sub>1 |_ (p @ q)) \<cdot> \<delta>" and "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 = l\<^sub>2 \<cdot> \<delta>"
      using vars_term_subt_at [OF pq] and disj and \<nu>
      unfolding term_subst_eq_conv
      by (auto simp: \<delta>_def \<sigma>\<^sub>1_def vars_crule_def vars_rule_def)
    ultimately have eq: "(l\<^sub>1 |_ (p @ q)) \<cdot> \<delta> = l\<^sub>2 \<cdot> \<delta>" by simp
    then have "\<delta> \<in> unifiers {(l\<^sub>1 |_ (p @ q), l\<^sub>2)}" by (simp add: unifiers_def)
    with mgu_sound [OF mgu] have [simp]: "\<mu> \<circ>\<^sub>s \<delta> = \<delta>" by (simp add: is_imgu_def)

    { fix s t assume "(s, t) \<in> set cs\<^sub>2"
      then have "s \<cdot> \<delta> = s \<cdot> \<sigma>\<^sub>2" and "t \<cdot> \<delta> = t \<cdot> \<sigma>\<^sub>2"
        using disj by (force simp: term_subst_eq_conv \<delta>_def vars_crule_def vars_defs)+ }
    then have "conds_n_sat R n cs\<^sub>2 \<delta>" using conds2 by (auto simp: conds_n_sat_iff)
    then have conds2': "conds_n_sat R n (subst_list \<mu> cs\<^sub>2) \<delta>" by (simp add: conds_n_sat_subst_list)

    { fix s t assume "(s, t) \<in> set cs\<^sub>1"
      then have "s \<cdot> \<delta> = s \<cdot> \<nu>" and "t \<cdot> \<delta> = t \<cdot> \<nu>"
        by (auto simp: term_subst_eq_conv \<delta>_def vars_crule_def vars_defs) }
    then have "conds_n_sat R m cs\<^sub>1 \<delta>" using conds1 by (auto simp: conds_n_sat_iff)
    then have conds1': "conds_n_sat R m (subst_list \<mu> cs\<^sub>1) \<delta>" by (simp add: conds_n_sat_subst_list)

     from overlapI [OF rule_variants disj fp] and mgu
       have "overlap R ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) (p @ q)" by auto
     with ao show ?thesis
       using fun_poss(1) and \<open>C \<noteq> MHole\<close> and conds1' and conds2' and comm and mgu
       by (cases; cases C) auto
  qed
qed

context
  fixes R :: "('f, 'v :: infinite) ctrs"
  assumes ao: "almost_orthogonal R"
    and epo: "extended_properly_oriented R"
    and rs: "right_stable R"
    and t3: "type3 R"
    and vars: "\<forall>((l, r), cs) \<in> R. is_Fun l"
begin

lemma trs_n_peak:
  assumes "(s, t) \<in> trs_n R (Suc m)" and "(s, u) \<in> trs_n R (Suc n)"
    and "\<And>m' n'. m' + n' < (Suc m) + (Suc n) \<Longrightarrow> comm ((epar_n R m')\<^sup>*) ((epar_n R n')\<^sup>*)"
  shows "\<exists>v. (t, v) \<in> epar_n R (Suc n) \<and> (u, v) \<in> epar_n R (Suc m)"
proof -
  from assms(1) obtain l\<^sub>1' r\<^sub>1' cs\<^sub>1' \<sigma>\<^sub>1' where s1: "s = l\<^sub>1' \<cdot> \<sigma>\<^sub>1'" and t: "t = r\<^sub>1' \<cdot> \<sigma>\<^sub>1'"
    and rule1': "((l\<^sub>1', r\<^sub>1'), cs\<^sub>1') \<in> R"
    and cs1': "\<forall>(s', t') \<in> set cs\<^sub>1'. (s' \<cdot> \<sigma>\<^sub>1', t' \<cdot> \<sigma>\<^sub>1') \<in> (rstep (trs_n R m))\<^sup>*"
    and conds1': "conds_n_sat R m cs\<^sub>1' \<sigma>\<^sub>1'"
      by (auto elim: trs_n_SucE simp: conds_n_sat_iff cstep_n_rstep_trs_n_conv)
  from assms(2) obtain l\<^sub>2 r\<^sub>2 cs\<^sub>2 \<sigma>\<^sub>2 where s2: "s = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" and u: "u = r\<^sub>2 \<cdot> \<sigma>\<^sub>2"
    and rule2: "((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R"
    and cs2: "\<forall>(s', t') \<in> set cs\<^sub>2. (s' \<cdot> \<sigma>\<^sub>2, t' \<cdot> \<sigma>\<^sub>2) \<in> (rstep (trs_n R n))\<^sup>*"
    and conds2: "conds_n_sat R n cs\<^sub>2 \<sigma>\<^sub>2"
      by (auto elim: trs_n_SucE simp: conds_n_sat_iff cstep_n_rstep_trs_n_conv)

  from vars_crule_disjoint obtain \<pi>\<^sub>1
    where \<pi>\<^sub>1: "vars_crule (\<pi>\<^sub>1 \<bullet> ((l\<^sub>1', r\<^sub>1'), cs\<^sub>1')) \<inter> vars_crule ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) = {}" ..
  define l\<^sub>1 r\<^sub>1 cs\<^sub>1 \<sigma>\<^sub>1 where "l\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> l\<^sub>1'" and "r\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> r\<^sub>1'"
    and "cs\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> cs\<^sub>1'" and "\<sigma>\<^sub>1 \<equiv> sop (-\<pi>\<^sub>1) \<circ>\<^sub>s \<sigma>\<^sub>1'"
  note rename = l\<^sub>1_def r\<^sub>1_def cs\<^sub>1_def \<sigma>\<^sub>1_def

  have rule1: "-\<pi>\<^sub>1 \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R" and "0 \<bullet> ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R"
    using rule1' and rule2 by (simp_all add: eqvt rename o_def)
  then have rule_variants: "\<exists>\<pi>. \<pi> \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<in> R" "\<exists>\<pi>. \<pi> \<bullet> ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) \<in> R" by blast+

  have disj: "vars_crule ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) \<inter> vars_crule ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) = {}"
    using \<pi>\<^sub>1 by (auto simp: eqvt rename)

  have "[] \<in> fun_poss l\<^sub>1'" using rule1' and vars by (cases l\<^sub>1') (auto)
  then have fun_poss: "[] \<in> fun_poss (clhs ((l\<^sub>1, r\<^sub>1), cs\<^sub>1))" by (simp add: rename)

  have "vars_term (l\<^sub>1 |_ []) \<inter> vars_term l\<^sub>2 = {}"
    and l: "(l\<^sub>1 |_ []) \<cdot> \<sigma>\<^sub>1 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using s1 and s2 and disj
    by (auto simp: vars_crule_def vars_rule_def rename)
  from vars_term_disjoint_imp_unifier [OF this]
    obtain \<mu> where mgu: "mgu (l\<^sub>1 |_ []) l\<^sub>2 = Some \<mu>"
    using mgu_complete by (auto simp: unifiers_def)

  have "overlap R ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) ((l\<^sub>2, r\<^sub>2), cs\<^sub>2) []"
    using overlapI [OF rule_variants disj fun_poss] and mgu by auto
  with ao have "r\<^sub>1 \<cdot> \<mu> = r\<^sub>2 \<cdot> \<mu> \<or> (\<exists>\<pi>. \<pi> \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) = ((l\<^sub>2, r\<^sub>2), cs\<^sub>2)) \<or>
    (\<forall>m n. comm ((cstep_n R m)\<^sup>*) ((cstep_n R n)\<^sup>*) \<longrightarrow>
      \<not> (\<exists>\<sigma>. conds_n_sat R m (subst_list \<mu> cs\<^sub>1) \<sigma> \<and> conds_n_sat R n (subst_list \<mu> cs\<^sub>2) \<sigma>))"
    using mgu by (cases) (auto)
  moreover {
    define \<tau> where "\<tau> \<equiv> \<lambda>x. if x \<in> vars_crule ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) then \<sigma>\<^sub>1 x else \<sigma>\<^sub>2 x"
    have "l\<^sub>1 \<cdot> \<tau> = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" and "l\<^sub>2 \<cdot> \<tau> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
      and [simp]: "r\<^sub>1 \<cdot> \<tau> = r\<^sub>1 \<cdot> \<sigma>\<^sub>1" "r\<^sub>2 \<cdot> \<tau> = r\<^sub>2 \<cdot> \<sigma>\<^sub>2"
      using disj by (auto simp: term_subst_eq_conv vars_crule_def vars_rule_def \<tau>_def)
    then have "l\<^sub>1 \<cdot> \<tau> = l\<^sub>2 \<cdot> \<tau>" using l by simp
    from the_mgu [OF this] and mgu have "\<tau> = \<mu> \<circ>\<^sub>s \<tau>" by (auto simp: the_mgu_def)
    moreover assume "r\<^sub>1 \<cdot> \<mu> = r\<^sub>2 \<cdot> \<mu>"
    ultimately have "r\<^sub>1 \<cdot> \<tau> = r\<^sub>2 \<cdot> \<tau>" by (metis subst_subst)
    then have "(t, t) \<in> epar_n R (Suc n) \<and> (u, t) \<in> epar_n R (Suc m)"
      by (simp add: t u) (simp add: rename)
    then have ?thesis ..
  }
  moreover {
    assume "\<forall>m n. comm ((cstep_n R m)\<^sup>*) ((cstep_n R n)\<^sup>*) \<longrightarrow>
      \<not> (\<exists>\<sigma>. conds_n_sat R m (subst_list \<mu> cs\<^sub>1) \<sigma> \<and> conds_n_sat R n (subst_list \<mu> cs\<^sub>2) \<sigma>)"
    moreover have "comm ((cstep_n R m)\<^sup>*) ((cstep_n R n)\<^sup>*)" using assms(3) [of m n]
      by (auto simp: rtrancl_epar_n_conv)
    ultimately have infeasible:
      "\<not> (\<exists>\<sigma>. conds_n_sat R m (subst_list \<mu> cs\<^sub>1) \<sigma> \<and> conds_n_sat R n (subst_list \<mu> cs\<^sub>2) \<sigma>)" by blast

    define \<delta> where "\<delta> \<equiv> \<lambda>x. if x \<in> vars_crule ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) then \<sigma>\<^sub>1 x else \<sigma>\<^sub>2 x"

    have "l\<^sub>1 \<cdot> \<delta> = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" and "l\<^sub>2 \<cdot> \<delta> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
      using disj by (auto simp: term_subst_eq_conv \<delta>_def vars_crule_def vars_defs)
    then have "l\<^sub>1 \<cdot> \<delta> = l\<^sub>2 \<cdot> \<delta>" using l by simp
    then have "\<delta> \<in> unifiers {(l\<^sub>1, l\<^sub>2)}" by (simp add: unifiers_def)
    then have [simp]: "\<mu> \<circ>\<^sub>s \<delta> = \<delta>" using mgu_sound [OF mgu] by (simp add: is_imgu_def)

    { fix s t assume "(s, t) \<in> set cs\<^sub>1"
      then have "s \<cdot> \<delta> = s \<cdot> sop (-\<pi>\<^sub>1) \<circ>\<^sub>s \<sigma>\<^sub>1'" and "t \<cdot> \<delta> = t \<cdot> sop (-\<pi>\<^sub>1) \<circ>\<^sub>s \<sigma>\<^sub>1'"
        using disj
        unfolding term_subst_eq_conv
        by (auto simp: \<delta>_def vars_crule_def vars_defs \<sigma>\<^sub>1_def) }
      then have "conds_n_sat R m cs\<^sub>1 \<delta>"
        using conds1' by (auto simp: conds_n_sat_iff) (auto simp: rename eqvt)
      then have conds1: "conds_n_sat R m (subst_list \<mu> cs\<^sub>1) \<delta>" by (simp add: conds_n_sat_subst_list)

      { fix s t assume "(s, t) \<in> set cs\<^sub>2"
        then have "s \<cdot> \<delta> = s \<cdot> \<sigma>\<^sub>2" and "t \<cdot> \<delta> = t \<cdot> \<sigma>\<^sub>2"
          using disj by (force simp: term_subst_eq_conv \<delta>_def vars_crule_def vars_defs)+ }
      then have "conds_n_sat R n cs\<^sub>2 \<delta>"
        using conds2 by (auto simp: conds_n_sat_iff)
      then have conds2: "conds_n_sat R n (subst_list \<mu> cs\<^sub>2) \<delta>" by (simp add: conds_n_sat_subst_list)
      with infeasible and conds1 have ?thesis by blast
  }
  moreover {
    assume "\<exists>\<pi>. \<pi> \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) = ((l\<^sub>2, r\<^sub>2), cs\<^sub>2)"
    then obtain \<pi> where vt: "\<pi> \<bullet> ((l\<^sub>1, r\<^sub>1), cs\<^sub>1) = ((l\<^sub>2, r\<^sub>2), cs\<^sub>2)" using mgu by auto
    
    let ?\<sigma>\<^sub>2 = "(sop \<pi>) \<circ>\<^sub>s \<sigma>\<^sub>2"
    have \<sigma>: "\<forall>x \<in> vars_term l\<^sub>1. \<sigma>\<^sub>1 x = ?\<sigma>\<^sub>2 x"
      using vt l by (auto simp: subst_compose permute_term_subst_apply_term term_subst_eq_conv eqvt)
  
    have ?thesis
    proof (cases "vars_term r\<^sub>1 \<subseteq> vars_term l\<^sub>1")
      case True
      then have "r\<^sub>1 \<cdot> \<sigma>\<^sub>1 = r\<^sub>1 \<cdot> ?\<sigma>\<^sub>2" unfolding term_subst_eq_conv using \<sigma> by auto
      then have "(t, t) \<in> epar_n R (Suc n) \<and> (u, t) \<in> epar_n R (Suc m)"
        using vt u t r\<^sub>1_def \<sigma>\<^sub>1_def \<sigma> by (auto simp add: term_subst_eq_conv eqvt)
      then show ?thesis ..
    next
      case False
      let ?\<rho>\<^sub>1 = "((l\<^sub>1, r\<^sub>1), cs\<^sub>1)"

      from epo [unfolded extended_properly_oriented_def, THEN bspec, OF rule1']
        have "vars_term r\<^sub>1' \<subseteq> vars_term l\<^sub>1' \<or> (\<exists>m \<le> length cs\<^sub>1'.
          (\<forall>i < m. vars_term (fst (cs\<^sub>1' ! i)) \<subseteq> X_vars ((l\<^sub>1', r\<^sub>1'), cs\<^sub>1') i) \<and>
          (\<forall>i \<in> {m ..< length cs\<^sub>1'}. vars_term r\<^sub>1' \<inter> vars_rule (cs\<^sub>1' ! i) \<subseteq>
          X_vars ((l\<^sub>1', r\<^sub>1'), cs\<^sub>1') m))" by simp
      with False obtain k where "k \<le> length cs\<^sub>1'"
        and "(\<forall>i < k. vars_term (fst (cs\<^sub>1' ! i)) \<subseteq> X_vars ((l\<^sub>1', r\<^sub>1'), cs\<^sub>1') i) \<and>
          (\<forall>i \<in> {k ..< length cs\<^sub>1'}. vars_term r\<^sub>1' \<inter> vars_rule (cs\<^sub>1' ! i) \<subseteq> X_vars ((l\<^sub>1', r\<^sub>1'), cs\<^sub>1') k)"
        apply (auto simp: l\<^sub>1_def r\<^sub>1_def cs\<^sub>1_def eqvt)
        using atom_set_pt.subset_eqvt permute_boolI vars_term_eqvt by blast
      from this(1) and permute_boolI [OF this(2), of \<pi>\<^sub>1, unfolded eqvt bool_pt.all_eqvt' bool_pt.ball_eqvt']
        have k: "k \<le> length cs\<^sub>1"
        and ext_vars1: "\<forall>i < k. vars_term (fst (cs\<^sub>1 ! i)) \<subseteq> X_vars ?\<rho>\<^sub>1 i"
        and ext_vars2: "\<forall>i\<in>{k ..< length cs\<^sub>1}. vars_term r\<^sub>1 \<inter> vars_rule (cs\<^sub>1 ! i) \<subseteq> X_vars ?\<rho>\<^sub>1 k"
        by (auto simp: l\<^sub>1_def r\<^sub>1_def cs\<^sub>1_def eqvt)
      let ?c = "\<lambda>i. take (min i k) cs\<^sub>1"
      let ?V = "\<lambda>i. \<Union>(vars_rule ` set (?c i))"
      let ?d = "\<lambda>i. take (i - k) (drop k cs\<^sub>1)"
      let ?W = "\<lambda>i. vars_term r\<^sub>1 \<inter> \<Union>(vars_rule ` set (?d i))"
      let ?P\<^sub>1 = "\<lambda>\<sigma>. \<forall>x \<in> vars_term l\<^sub>1. \<sigma> x = \<sigma>\<^sub>1 x \<and> \<sigma>\<^sub>1 x = ?\<sigma>\<^sub>2 x"
      let ?P\<^sub>2 = "\<lambda>\<sigma> i. \<forall>x \<in> vars_term l\<^sub>1 \<union> ?V i \<union> ?W i.
        (\<sigma>\<^sub>1 x, \<sigma> x) \<in> (epar_n R n)\<^sup>* \<and> (?\<sigma>\<^sub>2 x, \<sigma> x) \<in> (epar_n R m)\<^sup>*"

      have "vars_term r\<^sub>1' \<subseteq> vars_term l\<^sub>1' \<union> \<Union>(vars_rule ` set cs\<^sub>1')"
        using t3 and rule1' by (force simp: type3_def vars_defs)
      from permute_boolI [OF this, of \<pi>\<^sub>1, unfolded eqvt]
        have t3': "vars_term r\<^sub>1 \<subseteq> vars_term l\<^sub>1 \<union> \<Union>(vars_rule ` set cs\<^sub>1)"
        by (auto simp: l\<^sub>1_def r\<^sub>1_def cs\<^sub>1_def eqvt)
      have "set (take (min (length cs\<^sub>1) k) cs\<^sub>1) \<union>
       set (take (length cs\<^sub>1 - k) (drop k cs\<^sub>1)) = set cs\<^sub>1"
        by (metis append_take_drop_id k length_drop min.absorb2 order_refl set_append take_all)
      then have rhs: "vars_term r\<^sub>1 \<subseteq> vars_term l\<^sub>1 \<union> ?V (length cs\<^sub>1) \<union> ?W (length cs\<^sub>1)"
        using t3' by force
      { fix i :: nat
        assume "i \<le> length cs\<^sub>1"
        then have "\<exists>\<sigma>. ?P\<^sub>1 \<sigma> \<and> ?P\<^sub>2 \<sigma> i"
        proof (induction i)
          case 0
          show ?case using \<sigma> by (intro exI [of _ \<sigma>\<^sub>1]; simp add: o_def)
        next
          case (Suc i)
          then obtain \<sigma> where a: "?P\<^sub>1 \<sigma>" and c: "?P\<^sub>2 \<sigma> i" and i: "i < length cs\<^sub>1"
            by (auto simp: subst_compose)

          let ?s = "fst (cs\<^sub>1 ! i)" and ?t = "snd (cs\<^sub>1 ! i)"

          have [simp]: "take (Suc i) cs\<^sub>1 = take i cs\<^sub>1 @ [(?s, ?t)]"
            by (auto simp: i take_Suc_conv_app_nth)

          consider "i > k" | "i = k" | "i < k" by arith
          then show ?case
          proof (cases)
            case 1
            then have "k \<le> i" by auto
            have "?P\<^sub>1 \<sigma>" by fact
            moreover have "?P\<^sub>2 \<sigma> (Suc i)"
              using c and ext_vars2 [THEN bspec, of i] and 1 and k and i
              apply (simp add: min_def Suc_diff_le [OF \<open>k \<le> i\<close>] take_Suc_conv_app_nth X_vars_def)
              apply (unfold vars_rule_def)
              by (blast 8)
            ultimately show ?thesis by blast
          next
            case [simp]: 2
            have "?P\<^sub>1 \<sigma>" by fact
            moreover have "?P\<^sub>2 \<sigma> (Suc i)"
              using ext_vars2 [THEN bspec, of i] and c and k and i
              by (auto simp add: min_def X_vars_def take_Suc_conv_app_nth vars_rule_def)
            ultimately show ?thesis by blast
          next
            case 3
            from ext_vars1 [THEN spec, THEN mp, OF 3]
              have ssubs: "vars_term ?s \<subseteq> vars_term l\<^sub>1 \<union> ?V i"
                using 3 by (auto simp: min_def X_vars_def vars_rule_def)
            then have "\<forall>x \<in> vars_term ?s. (\<sigma>\<^sub>1 x, \<sigma> x) \<in> (epar_n R n)\<^sup>* \<and> (?\<sigma>\<^sub>2 x, \<sigma> x) \<in> (epar_n R m)\<^sup>*"
              using c by auto
            then have 1: "(?s \<cdot> \<sigma>\<^sub>1, ?s \<cdot> \<sigma>) \<in> (epar_n R n)\<^sup>*" and 2: "(?s \<cdot> ?\<sigma>\<^sub>2, ?s \<cdot> \<sigma>) \<in> (epar_n R m)\<^sup>*"
            using subst_epar_n_imp_epar_n_rtrancl [of ?s \<sigma>\<^sub>1 \<sigma> R n]
            and subst_epar_n_imp_epar_n_rtrancl [of ?s ?\<sigma>\<^sub>2 \<sigma> R m] by auto

            from cs2 and vt have "(?s \<cdot> ?\<sigma>\<^sub>2, ?t \<cdot> ?\<sigma>\<^sub>2) \<in> (rstep (trs_n R n))\<^sup>*" by (auto simp: i eqvt)
            from rev_subsetD [OF this] have 3: "(?s \<cdot> ?\<sigma>\<^sub>2, ?t \<cdot> ?\<sigma>\<^sub>2) \<in> (epar_n R n)\<^sup>*"
              using cstep_n_rstep_trs_n_conv [of R n] and cstep_n_subset_epar_n [of R n]
              by (auto simp add: rtrancl_mono)
  
            from i and cs1' have "(?s \<cdot> \<sigma>\<^sub>1, ?t \<cdot> \<sigma>\<^sub>1) \<in> (rstep (trs_n R m))\<^sup>*"
              by (auto simp: cs\<^sub>1_def \<sigma>\<^sub>1_def eqvt)
            from rev_subsetD [OF this] have 4: "(?s \<cdot> \<sigma>\<^sub>1, ?t \<cdot> \<sigma>\<^sub>1) \<in> (epar_n R m)\<^sup>*"
              using cstep_n_rstep_trs_n_conv [of R m] and cstep_n_subset_epar_n [of R m]
              by (auto simp add: rtrancl_mono)
            
            from assms(3) have comm: "comm ((epar_n R m)\<^sup>*) ((epar_n R n)\<^sup>*)" by auto
            obtain u where 8: "(?t \<cdot> \<sigma>\<^sub>1, u) \<in> (epar_n R n)\<^sup>*"
              and 5: "(?s \<cdot> \<sigma>, u) \<in> (epar_n R m)\<^sup>*"
              using commE [OF comm 4 1] by auto
            from 2 and 5 have 6: "(?s \<cdot> ?\<sigma>\<^sub>2, u) \<in> (epar_n R m)\<^sup>*" by auto

            obtain s' where 9: "(u, s') \<in> (epar_n R n)\<^sup>*"
              and 10: "(?t \<cdot> ?\<sigma>\<^sub>2, s') \<in> (epar_n R m)\<^sup>*"
              using commE [OF comm 6 3] by auto
            from 8 9 have 7: "(?t \<cdot> \<sigma>\<^sub>1, s') \<in> (epar_n R n)\<^sup>*" by auto
  
            have "?t \<in> rhss (set (snd ((l\<^sub>1, r\<^sub>1), cs\<^sub>1)))" using Suc by auto
            with rs and rule1 show ?thesis
            proof (induct rule: right_stable_perm_rhs_cases)
              case gnf
              show ?thesis
              proof (intro exI [of _ \<sigma>] conjI)
                show "?P\<^sub>1 \<sigma>" by (fact a)
              next
                from gnf.ground have "vars_term ?t = {}" by (simp add: ground_vars_term_empty)
                with ssubs have "vars_rule (?s, ?t) \<subseteq> vars_term l\<^sub>1 \<union> ?V i" by (simp add: vars_defs)
                then show "?P\<^sub>2 \<sigma> (Suc i)" using c and \<open>i < k\<close> and k and i
                  by (auto simp: min_def)
              qed
            next
              case lct

              from lct.linear and 10 obtain \<gamma>
                where *: "?t \<cdot> \<gamma> = s'" "\<forall>x. (?\<sigma>\<^sub>2 x, \<gamma> x) \<in> (epar_n R m)\<^sup>*"
                using no_step_from_constructor [OF vars lct.cterm]
                by (auto elim: linear_term_rtrancl_cstep_n_cases simp: rtrancl_epar_n_conv
                  simp del: subst_subst_compose)
  
              from lct.linear and 7 obtain \<delta>
                where **: "?t \<cdot> \<delta> = s'" "\<forall>x \<in> vars_term ?t. (\<sigma>\<^sub>1 x, \<delta> x) \<in> (epar_n R n)\<^sup>*"
                using no_step_from_constructor [OF vars lct.cterm]
                by (auto elim: linear_term_rtrancl_cstep_n_cases simp: rtrancl_epar_n_conv)

              have inter: "(vars_term l\<^sub>1 \<union> ?V i \<union> vars_term ?s) \<inter> vars_term ?t = {}"
                using right_stable_perm_rhsD [OF rs rule1, of i] and \<open>i < k\<close>
                by (auto simp: min_def i vars_defs)
            
              let ?\<rho>\<^sub>i = "\<lambda>x. (if x \<in> vars_term ?t then \<delta> x else \<sigma> x)"

              show ?thesis
              proof (intro exI [of _ ?\<rho>\<^sub>i] conjI)
                from inter have "\<forall>x \<in> vars_term l\<^sub>1. ?\<rho>\<^sub>i x = \<sigma> x" by auto
                then show "?P\<^sub>1 ?\<rho>\<^sub>i" using a by auto
              next
                { fix x
                  assume "x \<in> vars_term l\<^sub>1 \<union> ?V (Suc i) \<union> ?W (Suc i)"
                  then have "x \<in> vars_term l\<^sub>1 \<union> ?V i \<or> x \<in> vars_term ?t"
                    using ssubs and i and \<open>i < k\<close> and 3
                    by (auto simp: min_def vars_defs split: if_splits)
                  then have "(\<sigma>\<^sub>1 x, ?\<rho>\<^sub>i x) \<in> (epar_n R n)\<^sup>* \<and> (?\<sigma>\<^sub>2 x, ?\<rho>\<^sub>i x) \<in> (epar_n R m)\<^sup>*"
                  proof
                    assume "x \<in> vars_term l\<^sub>1 \<union> ?V i"
                    moreover with c have "(\<sigma>\<^sub>1 x, \<sigma> x) \<in> (epar_n R n)\<^sup>*"
                      and "(?\<sigma>\<^sub>2 x, \<sigma> x) \<in> (epar_n R m)\<^sup>*" by auto
                    ultimately show ?thesis using inter by (auto simp: vars_defs)
                  next
                    assume "x \<in> vars_term ?t"
                    with * and ** show ?thesis using \<open>i < k\<close> and 3
                    by (auto simp: term_subst_eq_conv)
                  qed }
                then show "?P\<^sub>2 ?\<rho>\<^sub>i (Suc i)" ..
              qed
            qed
          qed
        qed }
        from this [OF le_refl] obtain \<rho> where C: "?P\<^sub>2 \<rho> (length cs\<^sub>1)" by auto
        have "vars_term r\<^sub>1' \<subseteq> vars_term l\<^sub>1' \<union> \<Union>(vars_rule ` set cs\<^sub>1')"
          using t3 and rule1' by (force simp: type3_def vars_defs)
        from permute_boolI [OF this, of \<pi>\<^sub>1, unfolded eqvt]
          have "vars_term r\<^sub>1 \<subseteq> vars_term l\<^sub>1 \<union> \<Union>(vars_rule ` set cs\<^sub>1)"
          by (auto simp add: l\<^sub>1_def r\<^sub>1_def cs\<^sub>1_def eqvt)
        from rhs and C subst_epar_n_imp_epar_n_rtrancl [of r\<^sub>1 _ _ R]
          have "(r\<^sub>1 \<cdot> \<sigma>\<^sub>1, r\<^sub>1 \<cdot> \<rho>) \<in> (epar_n R n)\<^sup>*"
          and "(r\<^sub>1 \<cdot> ?\<sigma>\<^sub>2, r\<^sub>1 \<cdot> \<rho>) \<in> (epar_n R m)\<^sup>*"
          by (simp_all add: subset_eq subst_compose_def)
        moreover have "u = \<pi> \<bullet> r\<^sub>1 \<cdot> \<sigma>\<^sub>2" using vt by (simp add: u eqvt)
        ultimately have "(t, r\<^sub>1 \<cdot> \<rho>) \<in> epar_n R (Suc n)"
          and "(u, r\<^sub>1 \<cdot> \<rho>) \<in> epar_n R (Suc m)"
          using epar_n_rtrancl_Suc_mono
          by (auto simp: t r\<^sub>1_def \<sigma>\<^sub>1_def)
        then show ?thesis by blast
    qed }
  ultimately show ?thesis by blast
qed

lemma epar_n_varpeak:
  assumes s: "s =\<^sub>f (C, ts)" and ne: "C \<noteq> MHole" and len: "length us = length ts"
    and trs_m: "(s, t) \<in> trs_n R (Suc m)"
    and *: "\<forall>i < length ts. (ts ! i, us ! i) \<in> trs_n R (Suc n) \<union> (cstep_n R n)\<^sup>*"
    and comm1: "\<And>m' n'. m' + n' < (Suc m) + (Suc n) \<Longrightarrow> comm ((epar_n R m')\<^sup>*) ((epar_n R n'))"
    and comm2: "\<And>m' n'. m' + n' < (Suc m) + (Suc n) \<Longrightarrow> comm ((epar_n R m')\<^sup>*) ((epar_n R n')\<^sup>*)"
  shows "\<exists>v. (t, v) \<in> epar_n R (Suc n) \<and> (fill_holes C us, v) \<in> epar_n R (Suc m)"
proof -
  obtain l r \<sigma> cs
    where s': "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    and rule: "((l, r), cs) \<in> R"
    and ***: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (rstep (trs_n R m))\<^sup>*"
    by (rule trs_n_SucE [OF trs_m])
  then have l_\<sigma>: "l \<cdot> \<sigma> =\<^sub>f (C, ts)" and conds: "conds_n_sat R m cs \<sigma>"
    using s by (auto simp: conds_n_sat_iff cstep_n_rstep_trs_n_conv)
  from comm2 [of m n] have comm: "comm ((cstep_n R m)\<^sup>*) ((cstep_n R n)\<^sup>*)"
    by (auto simp: rtrancl_epar_n_conv)
  from rule and ao have "linear_term l" by simp
  from epar_n_varpeak' [OF comm vars ao rs rule conds l_\<sigma> ne * len] obtain \<tau>
    where l_\<tau>: "l \<cdot> \<tau> =\<^sub>f (C, us)"
    and **: "\<forall>x. (\<sigma> x, \<tau> x) \<in> epar_n R (Suc n)" by blast

  let ?c = "\<lambda>i. take i cs"
  let ?V = "\<lambda>i. \<Union>(vars_rule ` set (?c i))"
  let ?P\<^sub>1 = "\<lambda>\<delta>. \<forall>x \<in> vars_term l. \<delta> x = \<tau> x"
  let ?P\<^sub>2 = "\<lambda>\<delta> i. conds_n_sat R m (?c i) \<delta>"
  let ?P\<^sub>3 = "\<lambda>\<delta> i. \<forall>x \<in> vars_term l \<union> ?V i. (\<sigma> x, \<delta> x) \<in> epar_n R (Suc n)"

  have comm: "comm ((cstep_n R m)\<^sup>*) (epar_n R (Suc n))"
    using comm1 [of m "Suc n"] by (auto simp: rtrancl_epar_n_conv)
  have "0 \<bullet> ((l, r), cs) \<in> R" using rule by auto
  from conds_n_sat_extend_subst_epar_n [OF comm vars rs this ** conds]
    obtain \<delta> where "?P\<^sub>1 \<delta>" and P\<^sub>2: "?P\<^sub>2 \<delta> (length cs)" and P\<^sub>3: "?P\<^sub>3 \<delta> (length cs)" by auto
  then have "l \<cdot> \<tau> = l \<cdot> \<delta>" by (simp add: term_subst_eq_conv)
  moreover have "conds_n_sat R m cs \<delta>" using P\<^sub>2 by simp
  ultimately have "(l \<cdot> \<tau>, r \<cdot> \<delta>) \<in> cstep_n R (Suc m)"
    using rule
    by (auto simp: conds_n_sat_iff cstep_n_rstep_trs_n_conv intro: trs_n_SucI [THEN rstep_rule])
  then have "(fill_holes C us, r \<cdot> \<delta>) \<in> epar_n R (Suc m)"
    using cstep_n_subset_epar_n eqfE(1) l_\<tau> by fastforce
  moreover have "(t, r \<cdot> \<delta>) \<in> epar_n R (Suc n)"
  proof -
    have "vars_term r \<subseteq> vars_term l \<union> \<Union>(vars_rule ` set cs)"
      using t3 and rule by (force simp: type3_def vars_trs_def vars_rule_def)
    then show ?thesis using P\<^sub>3 by (auto simp: t subset_iff subst_epar_n_imp_epar_n)
  qed
  ultimately show ?thesis by blast
qed

lemma comm_epar_n:
  assumes "(s, t) \<in> epar_n R m" and "(s, u) \<in> epar_n R n"
  shows "\<exists>v. (t, v) \<in> epar_n R n \<and> (u, v) \<in> epar_n R m"
using assms
proof (induct "m + n" arbitrary: s t u m n rule: less_induct)
  case (less)

  have "\<And>m' n'. m' + n' < m + n \<Longrightarrow> comm (epar_n R m') (epar_n R n')"
    using less.hyps by (auto simp: comm_def)
  have IH\<^sub>1: "\<And>m' n'. m' + n' < m + n \<Longrightarrow> comm ((epar_n R m')\<^sup>*) (epar_n R n')"
    by (rule comm_rtrancl) fact
  have IH\<^sub>2: "\<And>m' n'. m' + n' < m + n \<Longrightarrow> comm ((epar_n R m')\<^sup>*) ((epar_n R n')\<^sup>*)"
    by (subst comm_swap, rule comm_rtrancl, subst comm_swap) fact

  consider (0) "m = 0 \<or> n = 0" | (Suc) m' and n' where "m = Suc m'" "n = Suc n'" by (cases m; cases n; auto)
  then show ?case
  proof (cases)
    case 0 then show ?thesis using less.prems by auto
  next
    case [simp]: (Suc m' n')
    from less.prems obtain C ss ts and D us vs
      where s: "s =\<^sub>f (C, ss)" and t: "t =\<^sub>f (C, ts)" and [simp]: "length ts = length ss"
        and ss: "\<forall>i < length ss. (ss ! i, ts ! i) \<in> trs_n R m \<union> (cstep_n R m')\<^sup>*"
        and s': "s =\<^sub>f (D, us)" and u: "u =\<^sub>f (D, vs)" and [simp]: "length vs = length us"
        and us: "\<forall>i < length us. (us ! i, vs ! i) \<in> trs_n R n \<union> (cstep_n R n')\<^sup>*"
        by (auto elim!: epar_n_SucE)
    then have ss_epar: "\<forall>i < length ss. (ss ! i, ts ! i) \<in> epar_n R m"
      and us_epar: "\<forall>i < length us. (us ! i, vs ! i) \<in> epar_n R n"
      using trs_n_subset_epar_n [of R] and csteps_n_subset_epar_n_Suc [of R]
      by (simp_all) (blast)+
    
    have [simp]: "num_holes C = length ss" "num_holes D = length us"
      using t and u by (auto dest: eqfE)
    
    define E Cs Ds where "E \<equiv> C \<sqinter> D" and "Cs \<equiv> inf_mctxt_args C D" and "Ds \<equiv> inf_mctxt_args D C"
    have len_Cs: "num_holes E = length Cs" and C: "C = fill_holes_mctxt E Cs"
      and len_Ds: "num_holes E = length Ds" and D: "D = fill_holes_mctxt E Ds"
      by (simp_all add: E_def Cs_def Ds_def num_holes_inf_mctxt
           inf_mctxt_inf_mctxt_args inf_mctxt_inf_mctxt_args2)
         (metis inf_commute num_holes_inf_mctxt)
    have s_left: "s = fill_holes (fill_holes_mctxt E Cs) ss"
      and [simp]: "t = fill_holes (fill_holes_mctxt E Cs) ts"
      and s_right: "s = fill_holes (fill_holes_mctxt E Ds) us"
      and [simp]: "u = fill_holes (fill_holes_mctxt E Ds) vs"
      using s and s' and t and u by (auto simp: C D dest: eqfE)

    define sss where [simp]: "sss \<equiv> partition_holes ss Cs"
    define tss where [simp]: "tss \<equiv> partition_holes ts Cs"
    define uss where [simp]: "uss \<equiv> partition_holes us Ds"
    define vss where [simp]: "vss \<equiv> partition_holes vs Ds"

    define ss' where "ss' \<equiv> map (\<lambda>i. fill_holes (Cs ! i) (sss ! i)) [0..<length Cs]"
    define ts' where "ts' \<equiv> map (\<lambda>i. fill_holes (Cs ! i) (tss ! i)) [0..<length Cs]"
    define us' where "us' \<equiv> map (\<lambda>i. fill_holes (Ds ! i) (uss ! i)) [0..<length Ds]"
    define vs' where "vs' \<equiv> map (\<lambda>i. fill_holes (Ds ! i) (vss ! i)) [0..<length Ds]"

    have [simp]: "sum_list (map num_holes Cs) = length ss"
      using s by (auto simp: C len_Cs num_holes_fill_holes_mctxt dest: eqfE)
    have [simp]: "sum_list (map num_holes Ds) = length us"
      using s' by (auto simp: D len_Ds num_holes_fill_holes_mctxt dest: eqfE)

    have len_ss: "length ss = sum_list (map num_holes Cs)"
      using s by (auto simp: C len_Cs num_holes_fill_holes_mctxt dest: eqfE)
    have len_us: "length us = sum_list (map num_holes Ds)"
      using s' by (auto simp: D len_Ds num_holes_fill_holes_mctxt dest: eqfE)
    have len_vs: "length vs = sum_list (map num_holes Ds)"
      using s' by (auto simp: D len_Ds num_holes_fill_holes_mctxt dest: eqfE)

    have ss'_i: "\<And>i. i < length Cs \<Longrightarrow> ss' ! i = fill_holes (Cs ! i) (sss ! i)"
      and us'_i: "\<And>i. i < length Cs \<Longrightarrow> us' ! i = fill_holes (Ds ! i) (uss ! i)"
      and ts'_i: "\<And>i. i < length Cs \<Longrightarrow> ts' ! i = fill_holes (Cs ! i) (tss ! i)"
      and vs'_i: "\<And>i. i < length Cs \<Longrightarrow> vs' ! i = fill_holes (Ds ! i) (vss ! i)"
      using len_Cs len_Ds by (auto simp: ss'_def us'_def ts'_def vs'_def)

    have len_vss_uss[simp]: "\<And>i. i < length Cs \<Longrightarrow> length (vss ! i) = length (uss ! i)"
      using len_Cs and len_Ds and len_vs by simp

    have "s = fill_holes E ss'"
      using fill_holes_mctxt_fill_holes [of Cs E ss]
      by (simp add: s_left ss'_def len_Cs C [symmetric])
    moreover
    have "s = fill_holes E us'"
      using fill_holes_mctxt_fill_holes [of Ds E us]
      by (simp add: s_right us'_def len_Ds D [symmetric])
    ultimately
    have us'_ss': "us' = ss'"
      using len_Cs and len_Ds
      by (intro fill_holes_inj [of E]) (simp_all add: ss'_def us'_def)

    have "\<forall>i < length ts'. \<exists>v. (ts' ! i, v) \<in> epar_n R n \<and> (vs' ! i, v) \<in> epar_n R m"
      (is "\<forall>i < length ts'. \<exists>v. ?P i v")
    proof (intro allI impI)
      fix i
      assume [simp]: "i < length ts'"
      then have [simp]: "i < length ss'" "i < length vs'" "i < length us'"
        using len_Cs and len_Ds by (simp_all add: us'_ss' ts'_def ss'_def vs'_def)
      then have [simp]: "i < length Cs" "i < length Ds"
        using len_Cs and len_Ds by (simp_all add: ss'_def)
      then have "i < length (inf_mctxt_args C D)" by (simp add: Cs_def)
      moreover have "(C, D) \<in> comp_mctxt" using s and s' by (metis eqf_comp_mctxt)
      ultimately have "Cs ! i = MHole \<or> Ds ! i = MHole"
        using inf_mctxt_args_MHole by (auto simp: Cs_def Ds_def)
      then show "\<exists>v. ?P i v"
      proof
        assume [simp]: "Cs ! i = MHole"
        define j where "j \<equiv> sum_list (map length (take i tss))"
        have "j < length ss"
          unfolding len_ss
          by (subst id_take_nth_drop [OF \<open>i < length Cs\<close>])
             (simp add: take_map [symmetric] drop_map [symmetric] j_def)

        have "ts' ! i = tss ! i ! 0" by (auto simp: ts'_def intro: fill_holes_MHole)
        then have [simp]: "ts' ! i = ts ! j"
          using partition_by_nth_nth_old [of i ts "map num_holes Cs" 0] by (simp add: j_def)

        have "ss' ! i = sss ! i ! 0" by (auto simp: ss'_def intro: fill_holes_MHole)
        then have [simp]: "ss' ! i = ss ! j"
          using partition_by_nth_nth_old [of i ss "map num_holes Cs" 0]
          apply (simp add: j_def)
          apply (intro arg_cong [of _ _ "nth ss"] arg_cong[of _ _ sum_list] nth_map_conv, force)
          apply (simp)
          apply (intro allI impI)
          by (metis \<open>i < length Cs\<close> \<open>length ts = length ss\<close> add_lessD1 len_ss length_partition_holes_nth less_imp_add_positive)

        have "\<forall>i < length (concat uss). (concat uss ! i, concat vss ! i) \<in> epar_n R n"
          using us_epar by simp
        moreover have "i < length uss"
          using len_Cs and len_Ds by simp
        ultimately have epar_uss: "\<forall>j < length (uss ! i). (uss ! i ! j, vss ! i ! j) \<in> epar_n R n"
          using concat_nth_length [of i uss] and concat_nth_length [of i vss]
          by (auto simp: concat_nth [symmetric, OF _ _ refl] take_map [symmetric])
        then have epar_us': "(us' ! i, vs' ! i) \<in> epar_n R n"
          using len_Cs len_Ds by (intro epar_n_mctxt [of _ "Ds ! i"]) (auto simp: us'_i vs'_i)

        have uss: "\<forall>j < length (uss ! i). (uss ! i ! j, vss ! i ! j) \<in> trs_n R (Suc n') \<union> (cstep_n R n')\<^sup>*"
          using concat_nth_length [of i uss] and concat_nth_length [of i vss] and us
          by (auto simp: concat_nth [symmetric, OF _ _ refl] take_map [symmetric])

        have [simp]: "ss ! j = us' ! i" by (simp add: us'_ss')

        have epar_ss': "(ss' ! i, ts' ! i) \<in> epar_n R m"
          using \<open>j < length ss\<close> and ss_epar by auto
        
        have "(ss' ! i, ts' ! i) \<in> trs_n R m \<union> (cstep_n R m')\<^sup>*" using ss and \<open>j < length ss\<close> by auto
        moreover
        { assume "(ss' ! i, ts' ! i) \<in> (cstep_n R m')\<^sup>*"
          then have "(ss' ! i, ts' ! i) \<in> (epar_n R m')\<^sup>*"
            using rtrancl_mono [OF cstep_n_subset_epar_n] by blast
          moreover have "comm ((epar_n R m')\<^sup>*) (epar_n R n)" using IH\<^sub>1 by simp
          moreover have "(ss' ! i, vs' ! i) \<in> (epar_n R n)" using epar_us' by simp
          ultimately obtain v where "(ts' ! i, v) \<in> epar_n R n"
            and "(vs' ! i, v) \<in> (epar_n R m')\<^sup>*" by (auto elim: commE)
          then have ?thesis using epar_n_rtrancl_Suc_mono [of R m'] by auto }
        moreover
        { assume trs_m: "(ss' ! i, ts' ! i) \<in> trs_n R m"
          have ?thesis
          proof (cases "Ds ! i = MHole")
            case True note [simp] = this
            define k where "k \<equiv> sum_list (map length (take i uss))"
            have "k < length us"
            unfolding len_us
            by (subst id_take_nth_drop [OF \<open>i < length Ds\<close>])
               (simp add: k_def take_map [symmetric])
  
            have "vs' ! i = vss ! i ! 0" by (auto simp: vs'_def intro: fill_holes_MHole)
            then have [simp]: "vs' ! i = vs ! k"
              using partition_by_nth_nth_old [of i vs "map num_holes Ds" 0]
              by (simp add: k_def take_map [symmetric])
    
            have "us' ! i = uss ! i ! 0" by (auto simp: us'_def intro: fill_holes_MHole)
            then have [simp]: "us' ! i = us ! k"
              using partition_by_nth_nth_old [of i us "map num_holes Ds" 0] by (simp add: k_def)

            have "(us' ! i, vs' ! i) \<in> trs_n R n \<union> (cstep_n R n')\<^sup>*"
              using us and \<open>k < length us\<close> by auto
            moreover
            { assume "(us' ! i, vs' ! i) \<in> (cstep_n R n')\<^sup>*"
              then have "(us' ! i, vs' ! i) \<in> (epar_n R n')\<^sup>*"
                using rtrancl_mono [OF cstep_n_subset_epar_n] by blast
              moreover have "comm ((epar_n R n')\<^sup>*) (epar_n R m)" using IH\<^sub>1 by simp
              moreover have "(us' ! i, ts' ! i) \<in> (epar_n R m)" using epar_ss' by simp
              ultimately obtain v where "(ts' ! i, v) \<in> (epar_n R n')\<^sup>*"
                and "(vs' ! i, v) \<in> epar_n R m" by (auto elim: commE)
              then have ?thesis using epar_n_rtrancl_Suc_mono [of R n'] by auto }
            moreover
            { assume "(us' ! i, vs' ! i) \<in> trs_n R n"
              with trs_m have ?thesis using IH\<^sub>2 by (auto elim: trs_n_peak) }
            ultimately show ?thesis by blast
          next
            case False
            have *: "us' ! i =\<^sub>f (Ds ! i, uss ! i)"
              using len_Cs and len_Ds by (auto simp: us'_i)
            have len_vss: "length (vss ! i) = length (uss ! i)" by simp
            from epar_n_varpeak [OF * False len_vss trs_m [simplified] uss IH\<^sub>1 IH\<^sub>2]
              show ?thesis by (simp add: vs'_i)
          qed }
        ultimately show ?thesis by blast
      next
        assume [simp]: "Ds ! i = MHole"
        define j where "j \<equiv> sum_list (map length (take i vss))"
        have "j < length us"
          unfolding len_us
          by (subst id_take_nth_drop [OF \<open>i < length Ds\<close>])
             (simp add: take_map [symmetric] drop_map [symmetric] j_def)

        have "vs' ! i = vss ! i ! 0" by (auto simp: vs'_def intro: fill_holes_MHole)
        then have [simp]: "vs' ! i = vs ! j"
          using partition_by_nth_nth_old [of i vs "map num_holes Ds" 0] by (simp add: j_def)

        have "us' ! i = uss ! i ! 0" by (auto simp: us'_def intro: fill_holes_MHole)
        then have [simp]: "us' ! i = us ! j"
          using partition_by_nth_nth_old [of i us "map num_holes Ds" 0]
          unfolding j_def
          apply (simp)
          apply (intro arg_cong [of _ _ "nth us"] arg_cong[of _ _ sum_list] nth_map_conv, force)
          apply (simp)
          apply (intro allI impI)
          by (metis len_vss_uss \<open>i < length Ds\<close> add_lessD1 canonically_ordered_monoid_add_class.lessE len_Cs len_Ds uss_def vss_def)

        have "\<forall>i < length (concat sss). (concat sss ! i, concat tss ! i) \<in> epar_n R m"
          using ss_epar by simp
        moreover have "i < length sss"
          using len_Cs and len_Ds by simp
        ultimately have epar_uss: "\<forall>j < length (sss ! i). (sss ! i ! j, tss ! i ! j) \<in> epar_n R m"
          using concat_nth_length [of i sss] and concat_nth_length [of i tss]
          by (auto simp: concat_nth [symmetric, OF _ _ refl] take_map [symmetric])
        then have epar_ss': "(ss' ! i, ts' ! i) \<in> epar_n R m"
          using len_Cs len_Ds by (intro epar_n_mctxt [of _ "Cs ! i"]) (auto simp: ss'_i ts'_i)

        have sss: "\<forall>j < length (sss ! i). (sss ! i ! j, tss ! i ! j) \<in> trs_n R (Suc m') \<union> (cstep_n R m')\<^sup>*"
          using concat_nth_length [of i sss] and concat_nth_length [of i tss] and ss
          by (auto simp: concat_nth [symmetric, OF _ _ refl] take_map [symmetric])

        have [simp]: "us ! j = ss' ! i" by (simp add: us'_ss' [symmetric])

        have epar_us': "(us' ! i, vs' ! i) \<in> epar_n R n"
          using \<open>j < length us\<close> and us_epar by auto

        have "(us' ! i, vs' ! i) \<in> trs_n R n \<union> (cstep_n R n')\<^sup>*" using us and \<open>j < length us\<close> by auto
        moreover
        { assume "(us' ! i, vs' ! i) \<in> (cstep_n R n')\<^sup>*"
          then have "(us' ! i, vs' ! i) \<in> (epar_n R n')\<^sup>*"
            using rtrancl_mono [OF cstep_n_subset_epar_n] by blast
          moreover have "comm ((epar_n R n')\<^sup>*) (epar_n R m)" using IH\<^sub>1 by simp
          moreover have "(us' ! i, ts' ! i) \<in> (epar_n R m)" using epar_ss' by simp
          ultimately obtain v where "(vs' ! i, v) \<in> epar_n R m"
            and "(ts' ! i, v) \<in> (epar_n R n')\<^sup>*" by (auto elim: commE)
          then have ?thesis using epar_n_rtrancl_Suc_mono [of R n'] by auto }
        moreover
        { assume trs_n: "(us' ! i, vs' ! i) \<in> trs_n R n"
          have ?thesis
          proof (cases "Cs ! i = MHole")
            case True note [simp] = this
            define k where "k \<equiv> sum_list (map length (take i sss))"
            have "k < length ss"
            unfolding len_ss
            by (subst id_take_nth_drop [OF \<open>i < length Cs\<close>])
               (simp add: k_def take_map [symmetric])

            have "ts' ! i = tss ! i ! 0" by (auto simp: ts'_def intro: fill_holes_MHole)
            then have [simp]: "ts' ! i = ts ! k"
              using partition_by_nth_nth_old [of i ts "map num_holes Cs" 0]
              by (simp add: k_def take_map [symmetric])

            have "ss' ! i = sss ! i ! 0" by (auto simp: ss'_def intro: fill_holes_MHole)
            then have [simp]: "ss' ! i = ss ! k"
              using partition_by_nth_nth_old [of i ss "map num_holes Cs" 0] by (simp add: k_def)

            have "(ss' ! i, ts' ! i) \<in> trs_n R m \<union> (cstep_n R m')\<^sup>*"
              using ss and \<open>k < length ss\<close> by auto
            moreover
            { assume "(ss' ! i, ts' ! i) \<in> (cstep_n R m')\<^sup>*"
              then have "(ss' ! i, ts' ! i) \<in> (epar_n R m')\<^sup>*"
                using rtrancl_mono [OF cstep_n_subset_epar_n] by blast
              moreover have "comm ((epar_n R m')\<^sup>*) (epar_n R n)" using IH\<^sub>1 by simp
              moreover have "(ss' ! i, vs' ! i) \<in> (epar_n R n)" using epar_us' by simp
              ultimately obtain v where "(vs' ! i, v) \<in> (epar_n R m')\<^sup>*"
                and "(ts' ! i, v) \<in> epar_n R n" by (auto elim: commE)
              then have ?thesis using epar_n_rtrancl_Suc_mono [of R m'] by auto }
            moreover
            { assume "(ss' ! i, ts' ! i) \<in> trs_n R m"
              with trs_n have ?thesis using IH\<^sub>2 by (auto elim: trs_n_peak) }
            ultimately show ?thesis by blast
          next
            case False
            have *: "ss' ! i =\<^sub>f (Cs ! i, sss ! i)"
              using len_Cs and len_Ds by (auto simp: ss'_i)
            have len_tss: "length (tss ! i) = length (sss ! i)" by simp
            from epar_n_varpeak [OF * False len_tss trs_n [simplified] sss IH\<^sub>1 IH\<^sub>2]
              show ?thesis by (auto simp: ts'_i)
          qed }
        ultimately show ?thesis by blast
      qed
    qed
    then obtain v where "\<forall>i < length ts'. ?P i (v i)" unfolding choice_iff' by blast
    moreover define ws where "ws \<equiv> map v [0 ..< length ts']"
    ultimately have *: "\<forall>i < length ts'. ?P i (ws ! i)" by (simp)

    have [simp]: "length ts' = length vs'"
      by (simp add: vs'_def ts'_def len_Cs [symmetric] len_Ds)

    define w where "w \<equiv> fill_holes E ws"

    have [simp]: "num_holes (fill_holes_mctxt E Cs) = length ss"
      using s by (auto simp: C [symmetric] dest!: eqfE)
    have [simp]: "num_holes (fill_holes_mctxt E Ds) = length vs"
      using s' by (auto simp: D [symmetric] dest!: eqfE)
    have "(t, w) \<in> epar_n R n"
      using *
      by (intro epar_n_mctxt [of _ E ts' _ ws])
        (auto simp: ts'_def eq_fill.simps len_Cs fill_holes_mctxt_fill_holes w_def ws_def)
    moreover have "(u, w) \<in> epar_n R m"
      using *
      by (intro epar_n_mctxt [of _ E vs' _ ws])
        (auto simp: vs'_def eq_fill.simps len_Ds fill_holes_mctxt_fill_holes w_def ws_def len_Cs)
    ultimately show ?thesis by blast
  qed
qed

text \<open>
  Almost orthogonal (modulo infeasibility), properly oriented, right-stable 3-CTRSs
  are level-confluent.
\<close>
lemma level_confluence:
  shows "level_confluent R"
unfolding level_confluent_def
proof (intro allI diamond_imp_CR')
  fix n
  show "cstep_n R n \<subseteq> epar_n R n" by (rule cstep_n_subset_epar_n)
  show "epar_n R n \<subseteq> (cstep_n R n)\<^sup>*" by (rule epar_n_subset_csteps_n)
  show "\<diamond> (epar_n R n)" using comm_epar_n by fast
qed

end

lemma level_confluent_imp_CR:
  assumes "level_confluent R"
  shows "CR (cstep R)"
proof
  fix a b c
  assume "(a, b) \<in> (cstep R)\<^sup>*"
    and "(a, c) \<in> (cstep R)\<^sup>*"
  then obtain n and m where "(a, b) \<in> (cstep_n R n)\<^sup>*"
    and "(a, c) \<in> (cstep_n R m)\<^sup>*" using csteps_imp_csteps_n[of _ _ R] by blast
  then have "(a, b) \<in> (cstep_n R (n + m))\<^sup>*"
    and "(a, c) \<in> (cstep_n R (n + m))\<^sup>*"
    using cstep_n_mono [THEN rtrancl_mono, of _ "n + m" R]
    and le_add1[of n m] and le_add2[of m n] by blast+
  then obtain d where bd: "(b, d) \<in> (cstep_n R (n + m))\<^sup>*"
    and cd: "(c, d) \<in> (cstep_n R (n + m))\<^sup>*" using assms
    by (auto simp: level_confluent_def CR_defs) (metis joinE)
  then have "(b, d) \<in> (cstep R)\<^sup>*" and "(c, d) \<in> (cstep R)\<^sup>*"
  by (metis (erased, opaque_lifting) contra_subsetD cstep_iff rtrancl_mono subrelI)+
  then show "(b, c) \<in> (cstep R)\<^sup>\<down>" by auto
qed

end
