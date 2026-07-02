(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2013-2017)
Author:  Makarius Wenzel <makarius@sketis.net> (2013)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Strongly_Closed
imports
  First_Order_Rewriting.Critical_Pairs
  TRS.More_Abstract_Rewriting
begin

lemma linear_variable_overlap_commute:
  assumes st:"(s, t) \<in> rstep_r_p_s R1 (l1, r1) p1 \<sigma>1"
    and su:"(s, u) \<in> rstep_r_p_s R2 (l2, r2) p2 \<sigma>2"
    and q:"p2 = p1 @ q"
    and var:"q \<notin> fun_poss l1"
    and lin: "linear_trs R1"
  shows "\<exists>v. (t, v) \<in> (rstep R2)\<^sup>= \<and> (u, v) \<in> rstep R1"
proof -
  from st su have p1: "p1 \<in> poss s" and \<sigma>1: "s |_ p1 = l1 \<cdot> \<sigma>1"
    and t: "t = replace_at s p1 (r1 \<cdot> \<sigma>1)" and lr1: "(l1, r1) \<in> R1" and p2: "p2 \<in> poss s"
    and \<sigma>2: "s |_ p2 = l2 \<cdot> \<sigma>2" and u: "u = replace_at s p2 (r2 \<cdot> \<sigma>2)" and lr2: "(l2, r2) \<in> R2"
    unfolding rstep_r_p_s_def' by auto
  from q have l2q:"(l1 \<cdot> \<sigma>1) |_ q = l2 \<cdot> \<sigma>2" using \<sigma>1 \<sigma>2 p1 p2 by auto
  from q u \<sigma>1 have up1:"u = replace_at s p1 (replace_at (l1 \<cdot> \<sigma>1) q (r2 \<cdot> \<sigma>2))"
      using ctxt_of_pos_term_append[OF p1] ctxt_ctxt by auto
  from var have "\<not>(q \<in> poss l1 \<and> is_Fun (l1 |_ q))"
    by (metis DiffI is_Var_def poss_simps(3) var_poss_iff)
  then obtain q1 q2 x where q12:"q = q1 @ q2" and q1:"q1 \<in> poss l1" and x:"l1 |_ q1 = Var x"
    using \<sigma>1 p2 pos_into_subst[of l1 \<sigma>1 "s |_ p1" q] poss_append_poss q by auto
  then have xq2:"\<sigma>1 x |_ q2 = l2 \<cdot> \<sigma>2" using l2q  by auto
  have q1l1\<sigma>1:"q1 \<in> poss (l1 \<cdot> \<sigma>1)" using q1 by simp
  define \<tau> where "\<tau> \<equiv> \<lambda> y. if y = x then replace_at (\<sigma>1 x) q2 (r2 \<cdot> \<sigma>2) else \<sigma>1 y"
  let ?cr = "replace_at s p1 (r1 \<cdot> \<tau>)"
  from lin lr1 have linl1:"linear_term l1" and linr1: "linear_term r1" by (auto dest: linear_trsE)
  from linear_term_replace_in_subst[OF linl1 q1 x, of \<sigma>1 \<tau>]
  have "l1 \<cdot> \<tau> = replace_at (l1 \<cdot> \<sigma>1) q1 (\<tau> x)" by (simp add: \<tau>_def)
  also have "... = replace_at (l1 \<cdot> \<sigma>1) q (r2 \<cdot> \<sigma>2)"
    using q12 q1 x ctxt_of_pos_term_append[OF q1l1\<sigma>1] ctxt_ctxt \<tau>_def by auto
  finally have "l1 \<cdot> \<tau> = replace_at (l1 \<cdot> \<sigma>1) q (r2 \<cdot> \<sigma>2)" .
  with up1 have "u = replace_at s p1 (l1 \<cdot> \<tau>)" by auto
  then have ucr:"(u, ?cr) \<in> rstep R1" using subset_rstep lr1 by auto
  have tcr:"(t, ?cr) \<in> (rstep R2)\<^sup>="
  proof (cases "x \<in> vars_term r1")
    case False
      then have "r1 \<cdot> \<tau> = r1 \<cdot> \<sigma>1" by (induct r1) (auto simp: \<tau>_def)
      then show ?thesis using t by auto
  next
    case True
    obtain q' where q':"q' \<in> poss r1" and q'x:"r1 |_ q' = Var x"
      using  supteq_imp_subt_at[OF supteq_Var[OF True]] by auto
    have qr1\<sigma>1:"q' \<in> poss (r1 \<cdot> \<sigma>1)" using q' by simp
    from linear_term_replace_in_subst[OF linr1 q' q'x, of \<sigma>1 \<tau>]
    have "r1 \<cdot> \<tau> = replace_at (r1 \<cdot> \<sigma>1) q' (\<tau> x)" by (simp add: \<tau>_def)
    also have "... = replace_at (r1 \<cdot> \<sigma>1) q' (replace_at (\<sigma>1 x) q2 (r2 \<cdot> \<sigma>2))" by (simp add: \<tau>_def)
    also have "... = replace_at (r1 \<cdot> \<sigma>1) (q' @ q2) (r2 \<cdot> \<sigma>2)"
      using q' q'x ctxt_of_pos_term_append[OF qr1\<sigma>1] ctxt_ctxt by auto
    finally have r1\<tau>:"r1 \<cdot> \<tau> = replace_at (r1 \<cdot> \<sigma>1) (q' @ q2) (r2 \<cdot> \<sigma>2)" .
    from xq2 q'x have "(r1 \<cdot> \<sigma>1) |_ (q' @ q2) = l2 \<cdot> \<sigma>2"
      using q' subt_at_append[OF qr1\<sigma>1, of q2] by auto
    then have "r1 \<cdot> \<sigma>1 = (ctxt_of_pos_term (q' @ q2) (r1 \<cdot> \<sigma>1))\<langle>l2 \<cdot> \<sigma>2\<rangle>"
      using qr1\<sigma>1 ctxt_supt_id \<sigma>1 p2 poss_append_poss q' q'x subt_at_subst q q1 q12 x by metis
    from rstepI[OF lr2 this] r1\<tau> have "(r1 \<cdot> \<sigma>1, r1 \<cdot> \<tau>) \<in> rstep R2" by simp
    then show ?thesis using t by blast
  qed
  from tcr ucr show ?thesis by blast
qed

lemma strongly_closed_linear_strongly_commute:
  assumes closed_1:"\<And>b p q. (b, q, p) \<in> critical_pairs ren R1 R2 \<Longrightarrow> \<exists>v. (p, v) \<in> (rstep R2)\<^sup>= \<and> (q, v) \<in> (rstep R1)\<^sup>*"
  assumes closed_2:"\<And>b p q. (b, q, p) \<in> critical_pairs ren R2 R1 \<Longrightarrow> \<exists>v. (p, v) \<in> (rstep R1)\<^sup>* \<and> (q, v) \<in> (rstep R2)\<^sup>="
    and lin: "linear_trs R1" "linear_trs R2"
  shows "strongly_commute (rstep R1) (rstep R2)"
proof
  let ?R1 = "rstep R1"
  let ?R2 = "rstep R2"
  fix s t u
  assume "(s, t) \<in> ?R1" and "(s, u) \<in> ?R2"
  then obtain l1 r1 p1 \<sigma>1 l2 r2 p2 \<sigma>2
    where st:"(s, t) \<in> rstep_r_p_s R1 (l1, r1) p1 \<sigma>1"
    and su:"(s, u) \<in> rstep_r_p_s R2 (l2, r2) p2 \<sigma>2"
    using rstep_iff_rstep_r_p_s by metis
  then have p1: "p1 \<in> poss s" and \<sigma>1: "s |_ p1 = l1 \<cdot> \<sigma>1"
    and t: "t = replace_at s p1 (r1 \<cdot> \<sigma>1)" and lr1: "(l1, r1) \<in> R1" and p2: "p2 \<in> poss s"
    and \<sigma>2: "s |_ p2 = l2 \<cdot> \<sigma>2" and u: "u = replace_at s p2 (r2 \<cdot> \<sigma>2)" and lr2: "(l2, r2) \<in> R2"
    unfolding rstep_r_p_s_def' by auto
  consider (parallel) "p1 \<bottom> p2" | (nested1) "p1 \<le>\<^sub>p p2" | (nested2) "p2 \<le>\<^sub>p p1"
    using parallel_pos by auto
  then show "\<exists>v. (t, v) \<in> ?R2\<^sup>= \<and> (u, v) \<in> ?R1\<^sup>*"
  proof (cases)
    case parallel
    then show ?thesis using parallel_steps st su by (blast dest: rstep_r_p_s_imp_rstep)
  next
    case nested1
    then obtain q where q:"p2 = p1 @ q" using less_eq_pos_def by auto
    then have l2q:"(l1 \<cdot> \<sigma>1) |_ q = l2 \<cdot> \<sigma>2" using \<sigma>1 \<sigma>2 p1 p2 by auto
    from q u \<sigma>1 have up1:"u = replace_at s p1 (replace_at (l1 \<cdot> \<sigma>1) q (r2 \<cdot> \<sigma>2))"
      using ctxt_of_pos_term_append[OF p1] ctxt_ctxt by auto
    show ?thesis
    proof (cases "q \<in> fun_poss l1")
      case True
      then have ql1:"q \<in> poss l1" and l1q:"is_Fun (l1 |_ q)" and l1qs1: "l1 |_ q \<cdot> \<sigma>1 = l2 \<cdot> \<sigma>2"
        using fun_poss_fun_conv[OF True] fun_poss_imp_poss[OF True] l2q subt_at_subst by auto
      from mgu_vd_complete[OF l1qs1, of ren]
      obtain \<mu>1 \<mu>2 \<delta> where mgu: "mgu_vd ren (l1 |_ q) l2 = Some (\<mu>1,\<mu>2)"
        and d1:"\<sigma>1 = \<mu>1 \<circ>\<^sub>s \<delta>"  and d2:"\<sigma>2 = \<mu>2 \<circ>\<^sub>s \<delta>" and mu12:"l1 |_ q \<cdot> \<mu>1 = l2 \<cdot> \<mu>2"
        by auto
      define t' where "t' \<equiv> r1 \<cdot> \<mu>1"
      define u' where "u' \<equiv> (ctxt_of_pos_term q l1 \<cdot>\<^sub>c \<mu>1)\<langle>r2 \<cdot> \<mu>2\<rangle>"
      from critical_pairsI[OF lr1 lr2 _ l1q mgu] ctxt_supt_id[OF ql1]
      have "(ctxt_of_pos_term q l1 = \<box>, u', t') \<in> critical_pairs ren R1 R2"
        unfolding t'_def u'_def by auto
      from closed_1[OF this] obtain v where v: "(t', v) \<in> ?R2\<^sup>= \<and> (u', v) \<in> ?R1\<^sup>*" by auto
      from d2 d1 have d2:"u' \<cdot> \<delta> = replace_at (l1 \<cdot> \<sigma>1) q (r2 \<cdot> \<sigma>2)"
        unfolding u'_def using ctxt_compose_subst_compose_distrib ctxt_of_pos_term_subst[OF ql1]
          subst_apply_term_ctxt_apply_distrib subst_subst by metis
      from d1 t'_def have "t' \<cdot> \<delta> = r1 \<cdot> \<sigma>1" by auto
      with t have tt':"t = replace_at s p1 (t' \<cdot> \<delta>)" by auto
      from d2 u up1 have uu':"u = replace_at s p1 (u' \<cdot> \<delta>)" by auto
      from v have vsteps:"(t' \<cdot> \<delta>, v \<cdot> \<delta>) \<in> ?R2\<^sup>= \<and> (u' \<cdot> \<delta>, v \<cdot> \<delta>) \<in> ?R1\<^sup>*"
      using rstep_subst rstep_id rstep_union rsteps_closed_subst by metis
      from vsteps tt' have "(t, replace_at s p1 (v \<cdot> \<delta>)) \<in> ?R2\<^sup>=" by auto
      moreover from vsteps uu' have "(u, replace_at s p1 (v \<cdot> \<delta>)) \<in> ?R1\<^sup>*"
        using rsteps_closed_ctxt by auto
      ultimately show ?thesis by blast
    next
      case False
      with linear_variable_overlap_commute st su q lin show ?thesis by blast
    qed
  next
    case nested2
    then obtain q where q:"p1 = p2 @ q" using less_eq_pos_def by auto
    then have l1q:"(l2 \<cdot> \<sigma>2) |_ q = l1 \<cdot> \<sigma>1" using \<sigma>1 \<sigma>2 p1 p2 by auto
    from q t \<sigma>2 have tp2:"t = replace_at s p2 (replace_at (l2 \<cdot> \<sigma>2) q (r1 \<cdot> \<sigma>1))"
      using ctxt_of_pos_term_append[OF p2] ctxt_ctxt by auto
    show ?thesis
    proof (cases "q \<in> fun_poss l2")
      case True
      then have ql2:"q \<in> poss l2" and l2q:"is_Fun (l2 |_ q)" and l2qs2: "l2 |_ q \<cdot> \<sigma>2 = l1 \<cdot> \<sigma>1"
        using fun_poss_fun_conv[OF True] fun_poss_imp_poss[OF True] l1q subt_at_subst by auto
      from mgu_vd_complete[OF l2qs2, of ren]
      obtain \<mu>1 \<mu>2 \<delta> where mgu: "mgu_vd ren (l2 |_ q) l1 = Some (\<mu>2, \<mu>1)"
        and d1:"\<sigma>1 = \<mu>1 \<circ>\<^sub>s \<delta>"  and d2:"\<sigma>2 = \<mu>2 \<circ>\<^sub>s \<delta>" and mu12:"l2 |_ q \<cdot> \<mu>2 = l1 \<cdot> \<mu>1"
        by auto
      define u' where "u' \<equiv> r2 \<cdot> \<mu>2"
      define t' where "t' \<equiv> (ctxt_of_pos_term q l2 \<cdot>\<^sub>c \<mu>2)\<langle>r1 \<cdot> \<mu>1\<rangle>"
      from critical_pairsI[OF lr2 lr1 _ l2q mgu] ctxt_supt_id[OF ql2]
      have "(ctxt_of_pos_term q l2 = \<box>, t', u') \<in> critical_pairs ren R2 R1"
        unfolding t'_def u'_def by auto
      from closed_2[OF this] obtain v where v: "(t', v) \<in> ?R2\<^sup>= \<and> (u', v) \<in> ?R1\<^sup>*" by auto
      from d2 d1 have d1:"t' \<cdot> \<delta> = replace_at (l2 \<cdot> \<sigma>2) q (r1 \<cdot> \<sigma>1)"
        unfolding t'_def using ctxt_compose_subst_compose_distrib ctxt_of_pos_term_subst[OF ql2]
          subst_apply_term_ctxt_apply_distrib subst_subst by metis
      from d2 u'_def have "u' \<cdot> \<delta> = r2 \<cdot> \<sigma>2" by auto
      with u have uu':"u = replace_at s p2 (u' \<cdot> \<delta>)" by auto
      from d1 t tp2 have tt':"t = replace_at s p2 (t' \<cdot> \<delta>)" by auto
      from v have vsteps:"(t' \<cdot> \<delta>, v \<cdot> \<delta>) \<in> ?R2\<^sup>= \<and> (u' \<cdot> \<delta>, v \<cdot> \<delta>) \<in> ?R1\<^sup>*"
      using rstep_subst rstep_id rstep_union rsteps_closed_subst by metis
      from vsteps tt' have "(t, replace_at s p2 (v \<cdot> \<delta>)) \<in> ?R2\<^sup>=" by auto
      moreover from vsteps uu' have "(u, replace_at s p2 (v \<cdot> \<delta>)) \<in> ?R1\<^sup>*"
        using rsteps_closed_ctxt by auto
      ultimately show ?thesis by blast
     next
      case False
      with linear_variable_overlap_commute st su q lin show ?thesis by blast
    qed
  qed
qed

definition strongly_closed :: "_ \<Rightarrow> ('f,_) trs \<Rightarrow> bool"
where
  "strongly_closed ren R = (\<forall> (b, q, p) \<in> critical_pairs ren R R.
    \<exists>s r. (p, r) \<in> (rstep R)\<^sup>* \<and> (q, r) \<in> (rstep R)\<^sup>=
        \<and> (p, s) \<in> (rstep R)\<^sup>= \<and> (q, s) \<in> (rstep R)\<^sup>*)"

corollary strongly_closed_linear_CR:
  assumes "strongly_closed ren R"
    and "linear_trs R"
  shows "CR (rstep R)"
using assms unfolding CR_iff_self_commute strongly_closed_def
by (auto intro!: strongly_commute_imp_commute strongly_closed_linear_strongly_commute)

end
