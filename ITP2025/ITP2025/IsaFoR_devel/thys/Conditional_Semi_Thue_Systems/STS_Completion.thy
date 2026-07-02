(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Completion for String Rewriting Systems\<close>

theory STS_Completion
  imports
    STS_Critical_Pairs
    String_Rewriting
    ShortLex
    Well_Quasi_Orders.Multiset_Extension
    Abstract_Completion.Peak_Decreasingness
begin

context shortlex_total
begin

(* Definition 11 *)
inductive sts_compl_step :: "sts \<times> sts \<Rightarrow> sts \<times> sts \<Rightarrow> bool" (infix "\<turnstile>\<^sub>S\<^sub>R" 55)
where
  deduce:"(E, R) \<turnstile>\<^sub>S\<^sub>R (E \<union> {(s @ u3, u1 @ t)}, R)"
    if "(u1 @ u2, s) \<in> R" and "(u2 @ u3, t) \<in> R" and "u2 \<noteq> []"
| simplifyl:"(E \<union> {(u1 @ u2 @ u3, s)}, R) \<turnstile>\<^sub>S\<^sub>R (E \<union> {(u1 @ t @ u3, s)}, R)"
    if "(u2, t) \<in> R"
| simplifyr:"(E \<union> {(s, u1 @ u2 @ u3)}, R) \<turnstile>\<^sub>S\<^sub>R (E \<union> {(s, u1 @ t @ u3)}, R)"
    if "(u2, t) \<in> R"
| orientl: "(E \<union> {(s, t)}, R) \<turnstile>\<^sub>S\<^sub>R (E, R \<union> {(s, t)})"
    if "s \<succ>\<^sub>s\<^sub>l t"
| orientr: "(E \<union> {(s, t)}, R) \<turnstile>\<^sub>S\<^sub>R (E, R \<union> {(t, s)})"
    if "t \<succ>\<^sub>s\<^sub>l s"
| collapse: "(E, R \<union> {(u1 @ u2 @ u3, s)}) \<turnstile>\<^sub>S\<^sub>R (E \<union> {(u1 @ t @ u3, s)}, R)"
    if "(u2, t) \<in> R"
| compose: "(E, R \<union> {(s, u1 @ u2 @ u3)}) \<turnstile>\<^sub>S\<^sub>R (E, R \<union> {(s, u1 @ t @ u3)})"
    if "(u2, t) \<in> R"
| delete: "(E \<union> {(s, s)}, R) \<turnstile>\<^sub>S\<^sub>R (E, R)"

lemmas stscompI = sts_compl_step.intros [intro]
lemmas stscompE = sts_compl_step.cases [elim]

declare shortlex.simps [simp del]

lemma deduce_cr:
  assumes u1u2s:"(u1 @ u2, s) \<in> R" and u2u3t:"(u2 @ u3, t) \<in> R" and "u2 \<noteq> []"
    and "(E, R) \<turnstile>\<^sub>S\<^sub>R (E \<union> {(s @ u3, u1 @ t)}, R)"
  shows "(s @ u3, u1 @ t) \<in> sts_critical_pairs R"
proof -
  let ?x = "u1"
  let ?u = "u2 @ u3"
  let ?v = "t"
  let ?u' = "u1 @ u2"
  let ?y = "u3"
  let ?v' = "s"
  have leq:"?x @ ?u = ?u' @ ?y" by auto
  have len:"length ?x < length ?u'" using assms by auto
  have "(?v'@ ?y, ?x @ ?u, ?x @ ?v) \<in> sts_critical_peaks R" 
    using len u1u2s u2u3t by auto
  hence "(s @ u3, u1 @ u2 @ u3, u1 @ t) \<in> sts_critical_peaks R" by auto
  with sts_critical_peak_pairs[of "s @ u3" "u1 @ u2 @ u3" "u1 @ t"]
  show ?thesis by auto
qed

lemma sts_deduce_sub:
  assumes "E' = E \<union> {(s @ u3, u1 @ t)}" and "R' = R" 
    and "(u1 @ u2, s) \<in> R" and "(u2 @ u3, t) \<in> R" and "u2 \<noteq> []"
  shows "E \<union> R \<subseteq> E' \<union> R'" using assms by auto

lemma sts_deduce:
  assumes "E' = E \<union> {(s @ u3, u1 @ t)}" and "R' = R" 
    and "(u1 @ u2, s) \<in> R" and "(u2 @ u3, t) \<in> R" and "u2 \<noteq> []"
  shows "E' \<union> R' \<subseteq> (ststep (E \<union> R))\<^sup>\<leftrightarrow> O (ststep R)\<^sup>=" using assms 
  by (auto, metis UnCI converse_Un deduce deduce_cr relcomp_distrib2 sts_critical_pairs_ststeps)

lemma sts_deduce2_sub:
  assumes "E' = E \<union> {(u1 @ t @ u3, s)}" and "R' = R" 
    and "(u1 @ u2 @ u3, s) \<in> R" and "(u2, t) \<in> R"
  shows "E \<union> R \<subseteq> E' \<union> R'" using assms by auto

lemma sts_deduce2:
  assumes "E' = E \<union> {(u1 @ t @ u3, s)}" and "R' = R" 
    and "(u1 @ u2 @ u3, s) \<in> R" and "(u2, t) \<in> R"
  shows "E' \<union> R \<subseteq> (ststep (E \<union> R))\<^sup>\<leftrightarrow> O (ststep R)\<^sup>=" using assms by auto

lemma sts_simplifyl_sub:
  assumes "E' = (E - {(u1 @ u2 @ u3, s)}) \<union> {(u1 @ t @ u3, s)}" and "R' = R" 
    and "(u2, t) \<in> R" and "{(u1 @ u2 @ u3, s)} \<subseteq> E"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> ststep R' O ststep E'" using assms 
proof -
  have "(u1 @ u2 @ u3, u1 @ t @ u3) \<in> ststep R" using assms(3) by auto
  then show ?thesis using assms by auto
qed

lemma sts_simplifyl:
  assumes "E' = (E - {(u1 @ u2 @ u3, s)}) \<union> {(u1 @ t @ u3, s)}" and "R' = R" 
    and "(u2, t) \<in> R" and "{(u1 @ u2 @ u3, s)} \<subseteq> E"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> (ststep R)\<inverse> O ststep E \<union> ststep E O ststep R"
proof -
  have "(u1 @ u2 @ u3, u1 @ t @ u3) \<in> ststep R" using assms(3) by auto
  then show ?thesis using assms by auto
qed

lemma sts_simplifyr_sub:
  assumes "E' = (E - {(s, u1 @ u2 @ u3)}) \<union> {(s, u1 @ t @ u3)}" and "R' = R" 
    and "(u2, t) \<in> R" and "{(s, u1 @ u2 @ u3)} \<subseteq> E"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> (ststep R' O ststep E') \<union> (ststep E' O (ststep R')\<inverse>)" using assms 
proof -
  have "(u1 @ u2 @ u3, u1 @ t @ u3) \<in> ststep R" using assms(3) by auto
  then show ?thesis using assms by auto
qed

lemma sts_simplifyr:
  assumes "E' = (E - {(s, u1 @ u2 @ u3)}) \<union> {(s, u1 @ t @ u3)}" and "R' = R" 
    and "(u2, t) \<in> R" and "{(s, u1 @ u2 @ u3)} \<subseteq> E"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> ((ststep R)\<inverse> O ststep E) \<union> (ststep E O ststep R)"
proof - 
  have "(u1 @ u2 @ u3, u1 @ t @ u3) \<in> ststep R" using assms(3) by auto
  then show ?thesis using assms by auto
qed

lemma sts_orientl_sub:
  assumes "E' = E - {(s, t)}" and "R' = R \<union> {(s, t)}" 
    and "s \<succ>\<^sub>s\<^sub>l t" and "(s, t) \<in> E"
  shows "E \<union> R \<subseteq> E' \<union> R'" using assms by auto

lemma sts_orientr_sub:
  assumes "E' = E - {(s, t)}" and "R' = R \<union> {(t, s)}" 
    and "t \<succ>\<^sub>s\<^sub>l s" and "(s, t) \<in> E"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> E\<inverse>" using assms by auto

lemma sts_collapse_sub:
  assumes "E' = E \<union> {(u1 @ t @ u3, s)}" and "R' = (R - {(u1 @ u2 @ u3, s)})" 
    and "(u2, t) \<in> R - {(u1 @ u2 @ u3, s)}" and "{(u1 @ u2 @ u3, s)} \<subseteq> R" 
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> (ststep R' O ststep E')" using assms by auto

lemma sts_collapse:
  assumes "E' = E" and "R' = (R - {(u1 @ u2 @ u3, s)})" 
    and "(u2, t) \<in> R - {(u1 @ u2 @ u3, s)}" and "{(u1 @ u2 @ u3, s)} \<subseteq> R"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> (ststep R)\<inverse> O ststep R \<union> ststep R O ststep R" using assms by auto

lemma sts_compose_sub:
  assumes "E' = E" and "R' = (R - {(s, u1 @ u2 @ u3)} \<union> {(s, u1 @ t @ u3)})" 
    and "(u2, t) \<in> R - {(s, u1 @ u2 @ u3)}" and "{(s, u1 @ u2 @ u3)} \<subseteq> R"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> ststep R' O (ststep R')\<inverse>" using assms by auto

lemma sts_compose:
  assumes "E' = E" and "R' = (R - {(s, u1 @ u2 @ u3)} \<union> {(s, u1 @ t @ u3)})" 
    and "(u2, t) \<in> R - {(s, u1 @ u2 @ u3)}" and "{(s, u1 @ u2 @ u3)} \<subseteq> R"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> (ststep R)\<inverse> O ststep R \<union> ststep R O ststep R" using assms by auto

lemma sts_delete_sub:
  assumes "E' = E - {(s, s)}" and "R' = R" 
    and "(s, s) \<in> E"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> Id" using assms by auto

lemma sts_delete:
  assumes "E' = E - {(s, s)}" and "R' = R" 
    and "(s, s) \<in> E"
  shows "E' \<union> R' \<subseteq> E \<union> R" using assms by auto 

lemma SR_subset_pre:
  assumes "(E, R) \<turnstile>\<^sub>S\<^sub>R (E', R')"
  shows "ststep (E \<union> R) \<subseteq> (ststep R')\<^sup>= O (ststep (E' \<union> R'))\<^sup>= O ((ststep R')\<inverse>)\<^sup>="
proof -
  have "E \<union> R \<subseteq> (ststep R')\<^sup>= O (ststep (E' \<union> R'))\<^sup>= O ((ststep R')\<inverse>)\<^sup>=" (is "?L \<subseteq> ?R")
  proof
    fix s t
    assume asm: "(s, t) \<in> ?L"
    from assms show "(s, t) \<in> ?R"
    proof (cases)
      case (deduce u1 u2 s u3 t)
      with sts_deduce_sub[of E' E s u3 u1 t R' R u2]
      have "E \<union> R \<subseteq> E' \<union> R'" by auto
      then show ?thesis using asm by auto  
    next
      case (simplifyl u2 t T u1 u3 s)
      with sts_simplifyl_sub[of E' E u1 u2 u3 s t R' R]
      have "E \<union> R \<subseteq> E' \<union> R' \<union> ststep R' O ststep E' \<union> ststep E' O (ststep R')\<inverse>" by auto
      then show ?thesis using asm by auto
    next
      case (simplifyr u2 t T s u1 u3)
      with sts_simplifyr_sub[of E' E s u1 u2 u3 t R' R]
      have "E \<union> R \<subseteq> E' \<union> R' \<union> ststep R' O ststep E' \<union> ststep E' O (ststep R')\<inverse>" by auto
      then show ?thesis using asm by auto
    next
      case (orientl s t)
      then show ?thesis using sts_orientl_sub asm by auto
    next
      case (orientr t s)
      then show ?thesis using sts_orientr_sub asm by auto
    next
      case (collapse u2 t u1 u3 s)
      with sts_collapse_sub[of E' E u1 t u3 s R' R u2]
      have "E \<union> R \<subseteq> E' \<union> R' \<union> (ststep R' O ststep E')" by auto
      then show ?thesis using asm by auto 
    next
      case (compose u2 t T s u1 u3)
      with sts_compose_sub[of E' E R' R s u1 u2 u3 t]
      have "E \<union> R \<subseteq> E' \<union> R' \<union> ststep R' O (ststep R')\<inverse>" by auto
      then show ?thesis using asm by auto
    next
      case (delete s)
      then show ?thesis using sts_delete_sub asm by auto
    qed
  qed
  from ststep_mono [OF this]
  have "ststep (E \<union> R) \<subseteq> ststep ((ststep R')\<^sup>= O (ststep (E' \<union> R'))\<^sup>= O ((ststep R')\<inverse>)\<^sup>=)" by auto
  moreover have "ststep (E \<union> R) \<subseteq> ststep ((ststep R')\<^sup>= O (ststep (E' \<union> R'))\<^sup>= O ((ststep (R'\<inverse>))\<^sup>=))"
    using ststep_converse[of R'] calculation by auto
  moreover have "... \<subseteq> ststep ((ststep R')\<^sup>=) O ststep ((ststep (E' \<union> R'))\<^sup>=) O ststep(((ststep (R'\<inverse>))\<^sup>=))"
    using  sctxt.closed_comp sctxt.closed_converse sctxt_closed_ststep sctxt_closed_strings ststepE
    by (auto, metis+)
  ultimately show ?thesis by auto
qed
  
lemma SR_subset:
  assumes "(E, R) \<turnstile>\<^sub>S\<^sub>R (E', R')"
  shows "ststep (E \<union> R) \<subseteq> ((ststep (E' \<union> R'))\<^sup>\<leftrightarrow>)\<^sup>*"
proof -
  have "E \<union> R \<subseteq> (ststep (E' \<union> R'))\<^sup>= O (ststep (E' \<union> (R')\<inverse>))\<^sup>=" (is "?L \<subseteq> ?R")
  proof
    fix s t
    assume asm: "(s, t) \<in> ?L"
    from assms show "(s, t) \<in> ?R"
      by (cases, insert asm, blast+)
  qed
  moreover have "... \<subseteq> ((ststep (E' \<union> R'))\<^sup>\<leftrightarrow>)\<^sup>*"
    by (auto, goal_cases, simp add: converse_rtrancl_into_rtrancl in_rtrancl_UnI,meson UnCI r_into_rtrancl 
        rtrancl.rtrancl_into_rtrancl,meson in_rtrancl_UnI r_into_rtrancl relto_pair.trans_NS_point rtrancl_converseI, 
        meson in_rtrancl_UnI r_into_rtrancl relto_pair.trans_NS_point rtrancl_converseI)
  from ststep_mono [OF this] show ?thesis 
    by (metis (no_types, lifting) calculation conversion_def order_subst2 sclosed_trancl ststep_mono)
qed

lemma SR_subset':
  assumes "(E, R) \<turnstile>\<^sub>S\<^sub>R (E', R')"
  shows "ststep (E' \<union> R') \<subseteq> ((ststep (E \<union> R))\<^sup>\<leftrightarrow>)\<^sup>*" 
proof -
  have "E' \<union> R' \<subseteq> ((ststep (E \<union> R))\<^sup>\<leftrightarrow>)\<^sup>= O (ststep (E \<union> R))\<^sup>=" (is "?L \<subseteq> ?R") 
  proof
    fix s t
    assume asm: "(s, t) \<in> ?L"
    from assms show "(s, t) \<in> ?R"
    proof(cases)
      case (deduce u1 u2 v u3 w)
      then show ?thesis using asm sts_deduce[of E' E v u3 u1 w R' R u2] by auto
    next
      case (simplifyl u2 t T u1 u3 s)
      with asm sts_simplifyl[of E' E u1 u2 u3 s t R' R] 
      have "E' \<union> R' \<subseteq> E \<union> R \<union> (ststep R)\<inverse> O ststep E \<union> ststep E O ststep R" by auto
      then show ?thesis using asm by auto
    next
      case (simplifyr u2 t T s u1 u3)
      with asm sts_simplifyr[of E' E s u1 u2 u3 t R' R]
      have "E' \<union> R' \<subseteq> E \<union> R \<union> ((ststep R)\<inverse> O ststep E) \<union> (ststep E O ststep R)" by auto
      then show ?thesis using asm by auto
    next
      case (orientl s t)
      then show ?thesis using sts_orientl_sub[of E' E s t R' R] using asm by force
    next
      case (orientr t s)
      then show ?thesis using sts_orientr_sub[of E' E s t R' R] using asm by force
    next
      case (collapse u2 t u1 u3 s)
      with asm sts_collapse[of E' E R' R u1 u2 u3 s t]
      have "E' \<union> R' \<subseteq> E \<union> R \<union> (ststep R)\<inverse> O ststep R \<union> ststep R O ststep R" by auto
      then show ?thesis using asm by auto
    next
      case (compose u2 t T s u1 u3)
      with asm sts_compose[of E' E R' R s u1 u2 u3 t]
      have "E' \<union> R' \<subseteq> E \<union> R \<union> (ststep R)\<inverse> O ststep R \<union> ststep R O ststep R" by auto
      then show ?thesis using asm by auto
    next
      case (delete s)
      with asm sts_delete[of E' E s R' R]
      have "E' \<union> R' \<subseteq> E \<union> R" by auto
      then show ?thesis using asm by auto
    qed
  qed
  moreover have "... \<subseteq> ((ststep (E \<union> R))\<^sup>\<leftrightarrow>)\<^sup>*"
  proof(auto, goal_cases)
    case (1 x y z)
    then show ?case by (simp add: converse_rtrancl_into_rtrancl in_rtrancl_UnI)
  next
    case (2 x y z)
    then show ?case by (meson in_rtrancl_UnI r_into_rtrancl relto_pair.trans_NS_point)
  next
    case (3 x y z)
    then show ?case by (meson in_rtrancl_UnI r_into_rtrancl relto_pair.trans_NS_point rtrancl_converseI)
  next
    case (4 x y z)
    then show ?case by (meson in_rtrancl_UnI r_into_rtrancl relto_pair.trans_NS_point rtrancl_converseI)
  next
    case (5 x y z)
    then show ?case by (meson UnCI converse_rtrancl_into_rtrancl r_into_rtrancl)
  next
    case (6 x y z)
    then show ?case by (simp add: converse_rtrancl_into_rtrancl in_rtrancl_UnI)
  next
    case (7 x y z)
    then show ?case by (meson in_rtrancl_UnI r_into_rtrancl relto_pair.trans_NS_point rtrancl_converseI)
  next
    case (8 x y z)
    then show ?case by (meson in_rtrancl_UnI r_into_rtrancl relto_pair.trans_NS_point rtrancl_converseI)
  qed   
  from ststep_mono [OF this] show ?thesis 
    by (metis (no_types, lifting) calculation conversion_def order_subst2 sclosed_trancl ststep_mono)
qed

lemma sts_compl_conversion:
  assumes "(E, R) \<turnstile>\<^sub>S\<^sub>R (E', R')"
  shows "(ststep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* = (ststep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*" (is "?lhs = ?rhs")
  using conversion_rtrancl[of "E \<union> R"] SR_subset[of E R E' R'] SR_subset'[of E R E' R']
    by (metis assms conversion_conversion_idemp conversion_def conversion_mono dual_order.eq_iff)

lemma sts_rtrancl_conversion:
  assumes "(\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E, R) (E', R')"
  shows "(ststep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* = (ststep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
  by (induct "(E, R)" "(E', R')" arbitrary: E' R')
    (force dest: sts_compl_conversion)+

lemma sts_rtrancl_subset_shortlex:
  assumes "(\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E, R) (E', R')" and R:"R \<subseteq> shortlex_S"
  shows "R' \<subseteq> shortlex_S" using assms
proof (induction "(E, R)" "(E', R')" arbitrary: E' R') 
  case (rtrancl_into_rtrancl pair) 
  note IH = this
  then obtain Ex and Rx where pair: "pair = (Ex, Rx)" by force
  hence "(\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E, R) (Ex, Rx)" using rtrancl_into_rtrancl.hyps(1) by auto
  have *:"(Ex, Rx) \<turnstile>\<^sub>S\<^sub>R (E', R')" using rtrancl_into_rtrancl.hyps(3) pair by auto 
  have Rx:"Rx \<subseteq> shortlex_S" 
    by (rule IH(2)[of Ex Rx], simp add:pair, insert R, blast)
  from * show ?case
  proof(cases, insert Rx)
    case (compose u2 t T s u1 u3)
    hence "s \<succ>\<^sub>s\<^sub>l u1 @ u2 @ u3" using Rx by blast
    moreover have "u2 \<succ>\<^sub>s\<^sub>l t" using compose using Rx by blast
    ultimately have "s \<succ>\<^sub>s\<^sub>l u1 @ t @ u3" using sctxt_shortlex_closed_S_pre shortlex_trans by blast
    then show ?thesis using Rx compose by blast
  qed (blast+)
qed

lemma ststep_subset_S: "R \<subseteq> shortlex_S \<Longrightarrow> ststep R \<subseteq> shortlex_S"
proof (rule subrelI)
  fix s t
  assume R:"R \<subseteq> shortlex_S"
    and st:"(s, t) \<in> ststep R"
  then show "(s, t) \<in> shortlex_S"
  proof -
    from st have "\<exists>l r bef aft. (l, r) \<in> R \<and> s = bef @ l @ aft \<and> t = bef @ r @ aft" by blast
    then obtain l r bef aft where lr:"(l, r) \<in> R" and s:"s = bef @ l @ aft" and t:"t = bef @ r @ aft" by blast
    from sctxt_shortlex_closed_S_pre[of l r bef aft] 
    show ?thesis using lr s t R by blast
  qed
qed

(* Lemma 4*)
lemma "R \<subseteq> shortlex_S \<Longrightarrow> SN (ststep R)"
  by (meson SN_subset shortlex_SN ststep_subset_S)

(* Lemma 13 *)
lemma sts_finite_run_conv:
  assumes R0:"R 0 = {}" and En:"E n = {}"
    and run: "\<forall>i < n. (E i, R i) \<turnstile>\<^sub>S\<^sub>R (E (Suc i), R (Suc i))"
  shows "(ststep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (ststep (R n))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  have *: "\<And>i. i \<le> n \<Longrightarrow> (\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)"
  proof -
    fix i
    assume "i \<le> n"
    then show "(\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)" using run 
      by (induct i, insert Suc_le_eq, auto) 
  qed
  from sts_rtrancl_conversion [OF * [of n]]
  show "(ststep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (ststep (R n))\<^sup>\<leftrightarrow>\<^sup>*" using R0 En by simp
qed

lemma sts_finite_run_SN:
  assumes R0:"R 0 = {}" and En:"E n = {}"
    and run: "\<forall>i < n. (E i, R i) \<turnstile>\<^sub>S\<^sub>R (E (Suc i), R (Suc i))"
  shows "SN (ststep (R n))"
proof -
  have *: "\<And>i. i \<le> n \<Longrightarrow> (\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)"
  proof -
    fix i
    assume "i \<le> n"
    then show "(\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)" using run 
      by (induct i, insert Suc_le_eq, auto) 
  qed
  from * [THEN sts_rtrancl_subset_shortlex] and R0
  have "\<And>i. i \<le> n \<Longrightarrow> R i \<subseteq> shortlex_S" by simp
  then show "SN (ststep (R n))" 
    by (meson SN_subset le_refl shortlex_SN ststep_subset_S)
qed

text \<open>A (non-empty) peak that is joinable or a critical pair.\<close>
definition jcp_peak :: "sts \<Rightarrow> string \<Rightarrow> sts"
  where
    "jcp_peak R s = {(t, u).
      (s, t) \<in> (ststep R)\<^sup>+ \<and> (s, u) \<in> (ststep R)\<^sup>+ \<and>
      ((t, u) \<in> (ststep R)\<^sup>\<down> \<or> (t, u) \<in> (ststep (sts_critical_pairs R))\<^sup>\<leftrightarrow>)}"

lemma scp_subset_imp:
  assumes fair:"sts_critical_pairs R \<subseteq> (\<Union> i \<le> n. (ststep (E i))\<^sup>\<leftrightarrow>)"
  shows "(ststep (sts_critical_pairs R))\<^sup>\<leftrightarrow> \<subseteq> (\<Union> i \<le> n. (ststep (E i))\<^sup>\<leftrightarrow>)" (is "_ \<subseteq> ?rhs")
proof
  fix s t
  assume "(s, t) \<in> (ststep (sts_critical_pairs R))\<^sup>\<leftrightarrow>"
  hence "(s, t) \<in> ststep (sts_critical_pairs R) \<or> (t, s) \<in> ststep (sts_critical_pairs R)" by auto
  then show "(s, t) \<in> ?rhs"
  proof 
    assume asm:"(s, t) \<in> ststep (sts_critical_pairs R)"
    then show ?thesis
    proof(rule ststepE, safe)
      fix l r bef aft sa ta
      assume lr:"(l, r) \<in> sts_critical_pairs R"
        and s:"s = bef @ l @ aft" 
        and t:"t = bef @ r @ aft" 
        and "(bef @ l @ aft, bef @ r @ aft) \<in> ststep (sts_critical_pairs R)"
      with assms [THEN subsetD, OF lr] 
      show "(bef @ l @ aft, bef @ r @ aft) \<in> (\<Union> i \<le> n. (ststep (E i))\<^sup>\<leftrightarrow>)" 
        unfolding ststep.simps using append.assoc ststepE ststepI 
        by (smt (verit, del_insts) UN_iff Un_iff converse_iff)
    qed
  next
    assume "(t, s) \<in> ststep (sts_critical_pairs R)"
    then show ?thesis
     proof(rule ststepE, safe)
      fix l r bef aft sa ta
      assume lr:"(l, r) \<in> sts_critical_pairs R"
        and t:"t = bef @ l @ aft" 
        and s:"s = bef @ r @ aft" 
        and "(bef @ l @ aft, bef @ r @ aft) \<in> ststep (sts_critical_pairs R)"
      with assms [THEN subsetD, OF lr] 
      show "(bef @ r @ aft, bef @ l @ aft) \<in> (\<Union>i\<le>n. (ststep (E i))\<^sup>\<leftrightarrow>)" 
        unfolding ststep.simps using append.assoc ststepE ststepI 
        by (smt (verit, del_insts) UN_iff Un_iff converse_iff)
    qed
  qed
qed

lemma fair_imp_jcp_peak:
  assumes fair:"sts_critical_pairs R \<subseteq> (\<Union> i \<le> n. (ststep (E i))\<^sup>\<leftrightarrow>)"
  shows "\<And>s t u. (t, u) \<in> jcp_peak R s \<Longrightarrow> (t, u) \<in> (ststep R)\<^sup>\<down> \<union> (\<Union> i \<le> n. (ststep (E i))\<^sup>\<leftrightarrow>)"
  using scp_subset_imp [OF assms]
  by (auto simp add: jcp_peak_def)

(* Definition 14 *)
definition mststep :: "string multiset \<Rightarrow> sts \<Rightarrow> string rel"
  where
    "mststep M R = {(s, t). (s, t) \<in> ststep R \<and> (\<exists>s' t'. s' \<in># M \<and> t' \<in># M \<and> s' \<succeq>\<^sub>s\<^sub>l s \<and> t' \<succeq>\<^sub>s\<^sub>l t)}"

lemma mststep_iff:
  "(x, y) \<in> mststep M R \<longleftrightarrow> (x, y) \<in> ststep R \<and> (\<exists>s' t'. s' \<in># M \<and> t' \<in># M \<and> s' \<succeq>\<^sub>s\<^sub>l x \<and> t' \<succeq>\<^sub>s\<^sub>l y)"
  by (auto simp: mststep_def)

lemma UN_mststep:
  "(\<Union>x\<in>R. mststep M {x}) = mststep M R"
  by (auto simp add: mststep_iff) blast+

lemma mststep_Un [simp]:
  "mststep M (R \<union> R') = mststep M R \<union> mststep M R'"
  by (auto iff: mststep_iff)

lemma mststep_mono [simp]:
  "R \<subseteq> R' \<Longrightarrow> mststep M R \<subseteq> mststep M R'"
  unfolding mststep_def by fast

lemma mststep_subset':
  "(mststep M R')\<^sup>= O (mststep M (E' \<union> R'))\<^sup>= O ((mststep M R')\<inverse>)\<^sup>= \<subseteq> ((mststep M (E' \<union> R'))\<^sup>\<leftrightarrow>)\<^sup>*"
  (is "?L \<subseteq> ?R")
proof
  fix s t assume "(s, t) \<in> ?L"
  then obtain u and v where "(s, u) \<in> (mststep M R')\<^sup>="
    and "(u, v) \<in> (mststep M (E' \<union> R'))\<^sup>="
    and "(v, t) \<in> ((mststep M R')\<inverse>)\<^sup>=" by auto
  then have "(s, u) \<in> ?R" and "(u, v) \<in> ?R" and "(v, t) \<in> ?R" by auto
  then show "(s, t) \<in> ?R" by auto
qed

lemma mststep_converse:"(mststep M R)\<^sup>\<leftrightarrow> = mststep M (R\<^sup>\<leftrightarrow>)"  (is "?L = ?R")
proof 
  show lr:"?L \<subseteq> ?R"
  proof
    fix t
    assume "t \<in> ?L"
    then show "t \<in> ?R" using mststep_iff 
      by (smt (verit, ccfv_threshold) Un_iff converseE converseI mststep_Un ststep_converse)    
  qed
  show "?R \<subseteq> ?L"
  proof
    fix t
    assume "t \<in> ?R"
    then show "t \<in> ?L"  
      by (smt (verit, ccfv_threshold) UnCI UnE lr converse_iff equalityI mststep_Un mststep_iff ststep_converse subrelI)
  qed
qed

lemma ststeps_subset_shortlex_s:
  assumes "R \<subseteq> {(x, y). x \<succ>\<^sub>s\<^sub>l y}"
  shows "(ststep R)\<^sup>+ \<subseteq> {(x, y). x \<succ>\<^sub>s\<^sub>l y}"
proof
  fix s t
  assume "(s, t) \<in> (ststep R)\<^sup>+"
  then show "(s, t) \<in> {(x, y). x \<succ>\<^sub>s\<^sub>l y}"
  proof (induct)
    case (base u)
    with ststep_subset_S [OF assms] show ?case by auto
  next
    case (step t u)
    then show ?case
      using ststep_subset_S [OF assms]
      by (meson shorlex_pair.trans_S_point subsetD)
  qed
qed

lemma mststep_subset:
  assumes "(E, R) \<turnstile>\<^sub>S\<^sub>R (E', R')" and "R' \<subseteq> {(x, y). x \<succ>\<^sub>s\<^sub>l y}"
  shows "mststep M (E \<union> R) \<subseteq> (mststep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
proof
  fix s t
  assume "(s, t) \<in> mststep M (E \<union> R)"
  then obtain s' and t' where "s' \<in># M" and "t' \<in># M"
    and "s' \<succeq>\<^sub>s\<^sub>l s" and "t' \<succeq>\<^sub>s\<^sub>l t" and "(s, t) \<in> ststep (E \<union> R)"
    by (auto simp: mststep_def)
  with SR_subset_pre [OF assms(1)] obtain u and v
    where "(s, u) \<in> (ststep R')\<^sup>=" and "(u, v) \<in> (ststep (E' \<union> R'))\<^sup>="
      and "(v, t) \<in> ((ststep R')\<inverse>)\<^sup>=" by blast
  moreover have tv:"(t, v) \<in> (ststep R')\<^sup>=" using calculation(3) by fastforce
  moreover have sr_slex:"ststep R' \<subseteq> shortlex_S" using ststep_subset_S [OF assms(2)]  by auto
  ultimately have "s \<succeq>\<^sub>s\<^sub>l u" and "t \<succeq>\<^sub>s\<^sub>l v"
    by (blast, metis Un_iff sr_slex case_prodD mem_Collect_eq pair_in_Id_conv subset_Un_eq tv)
  with \<open>s' \<succeq>\<^sub>s\<^sub>l s\<close> and \<open>t' \<succeq>\<^sub>s\<^sub>l t\<close> have "s' \<succeq>\<^sub>s\<^sub>l u" and "t' \<succeq>\<^sub>s\<^sub>l v" using shortlex_trans by blast+
  then have "(s, u) \<in> (mststep M R')\<^sup>="
    and "(u, v) \<in> (mststep M (E' \<union> R'))\<^sup>="
    and "(v, t) \<in> ((mststep M R')\<inverse>)\<^sup>="
    using \<open>s' \<in># M\<close> and \<open>t' \<in># M\<close>
      and \<open>s' \<succeq>\<^sub>s\<^sub>l s\<close> and \<open>t' \<succeq>\<^sub>s\<^sub>l t\<close>
      and \<open>(s, u) \<in> (ststep R')\<^sup>=\<close>
      and \<open>(u, v) \<in> (ststep (E' \<union> R'))\<^sup>=\<close>
      and \<open>(v, t) \<in> ((ststep R')\<inverse>)\<^sup>=\<close>
    unfolding mststep_def by (blast)+
  then have "(s, t) \<in> (mststep M R')\<^sup>= O ((mststep M (E' \<union> R')))\<^sup>= O ((mststep M R')\<inverse>)\<^sup>=" by blast
  with mststep_subset' [of M R' E'] show "(s, t) \<in> (mststep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def by blast
qed

lemma ststeps_imp_mststeps:
  assumes "t \<in># M" and "(t, u) \<in> (ststep R)\<^sup>*" and "R \<subseteq> {(x, y). x \<succ>\<^sub>s\<^sub>l y}"
  shows "(t, u) \<in> (mststep M R)\<^sup>*"
  using assms(2, 1)
proof (induct)
  case base show ?case by simp
next
  note sl = ststeps_subset_shortlex_s [OF assms(3)]
  case (step u v)
  have "(u, v) \<in> ststep R" by fact
  moreover have "t \<in># M" by fact
  moreover
  from \<open>(t, u) \<in> (ststep R)\<^sup>*\<close> and sl
  have "t \<succeq>\<^sub>s\<^sub>l u" by (metis case_prodD mem_Collect_eq rtranclD subset_eq)
  moreover have "u \<succ>\<^sub>s\<^sub>l v" using sl step by blast
  ultimately have "(u, v) \<in> mststep M R" 
    by (meson mststep_iff shortlex_trans)
  with step show ?case by auto
qed

lemma mststep_subset'':
  assumes "(E, R) \<turnstile>\<^sub>S\<^sub>R (E', R')" and "R' \<subseteq> {(x, y). x \<succ>\<^sub>s\<^sub>l y}"
  shows "(mststep M (E \<union> R))\<inverse> \<subseteq> (mststep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using converse_mono [THEN iffD2, OF mststep_subset [OF assms, of M]]
  by auto

lemma mststep_symcl_subset:
  assumes "(E, R) \<turnstile>\<^sub>S\<^sub>R (E', R')" and "R' \<subseteq> {(x, y). x \<succ>\<^sub>s\<^sub>l y}"
  shows "(mststep M (E \<union> R))\<^sup>\<leftrightarrow> \<subseteq> (mststep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using mststep_subset [OF assms] and mststep_subset'' [OF assms] by blast

(* Lemma 15 *)
lemma mststeps_subset:
  assumes "(E, R) \<turnstile>\<^sub>S\<^sub>R (E', R')" and "R' \<subseteq> {(x, y). x \<succ>\<^sub>s\<^sub>l y}"
  shows "(mststep M (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (mststep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using mststep_symcl_subset [OF assms, THEN rtrancl_mono] by (simp add: conversion_def)

lemma UNIV_mstep_rstep_iff:
  "(\<Union>M\<in>UNIV. mststep M R) = ststep R"
proof -
  have *: "\<And>s t. (s, t) \<in> ststep R \<Longrightarrow>
    s \<in># {#s, t#} \<and> t \<in># {#s, t#} \<and> s \<succeq>\<^sub>s\<^sub>l s \<and> t \<succeq>\<^sub>s\<^sub>l t \<and>
  (s, t) \<in> mststep {#s, t#} R" by (auto iff: mststep_iff)
  show ?thesis by (auto iff: mststep_iff) (insert *, blast)
qed

lemma sts_finite_fair_run:
  assumes R0:"R 0 = {}" and En:"E n = {}"
    and run:"\<forall>i < n. (E i, R i) \<turnstile>\<^sub>S\<^sub>R (E (Suc i), R (Suc i))"
    and fair: "sts_critical_pairs (R n) \<subseteq> (\<Union> i \<le> n. (ststep (E i))\<^sup>\<leftrightarrow>)"
  shows "CR (ststep (R n))"
proof (rule Newman[OF sts_finite_run_SN[OF R0 En run]], unfold sts_critical_pair_lemma, safe)
  fix s t
  assume scp:"(s, t) \<in> sts_critical_pairs (R n)"
  define mshortlex_s where "mshortlex_s x y = mulex (\<succ>\<^sub>s\<^sub>l)\<inverse>\<inverse> y x" for x y
  have "CR (ststep (R n))"
  proof -
    interpret lab: ars_labeled_sn "\<lambda>M. mststep M (R n)" UNIV mshortlex_s
    proof
      show "SN {(x, y). mshortlex_s x y}" unfolding mshortlex_s_def using shortlex_SN SN_mulex by blast
    qed
    interpret pd:ars_peak_decreasing "\<lambda>M. mststep M (R n)" UNIV mshortlex_s
    proof
      fix s t u :: "string" and M\<^sub>1 M\<^sub>2 :: "string multiset"
      assume stM1:"(s, t) \<in> mststep M\<^sub>1 (R n)" and suM2:"(s, u) \<in> mststep M\<^sub>2 (R n)"
      from stM1 suM2 have st: "(s, t) \<in> (ststep (R n))" and su:"(s, u) \<in> ststep (R n)" 
        by (auto iff: mststep_iff)
      from fair have scp:"sts_critical_pairs (R n) \<subseteq> (\<Union>i\<le>n. (ststep (E i))\<^sup>\<leftrightarrow>)" by fastforce
      from sts_critical_pairs_main[of s t "R n" u]
      have "((t, u) \<in> (ststep (R n))\<^sup>\<down> \<or> (t, u) \<in> (ststep (sts_critical_pairs (R n)))\<^sup>\<leftrightarrow>)"
        using st su by blast
      hence tus:"(t, u) \<in> jcp_peak (R n) s" using st su unfolding jcp_peak_def by auto
      from fair_imp_jcp_peak[OF scp]
      have "(t, u) \<in> (ststep (R n))\<^sup>\<down> \<union> (\<Union>i\<le>n. (ststep (E i))\<^sup>\<leftrightarrow>)" using tus by blast
      hence *:"(t, u) \<in> (ststep (R n))\<^sup>\<down> \<or> (t, u) \<in> (\<Union>i\<le>n. (ststep (E i))\<^sup>\<leftrightarrow>)" using tus by blast
      let ?D = "(\<Union>c\<in>lab.downset2 M\<^sub>1 M\<^sub>2. mststep c (R n))\<^sup>\<leftrightarrow>\<^sup>*"
      let ?M = "{#t, u#}"
      have **: "\<And>i. i \<le> n \<Longrightarrow> (\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)"
      proof -
        fix i assume "i \<le> n"
        with run show "(\<turnstile>\<^sub>S\<^sub>R)\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)" by (induct i, auto, meson less_eq_Suc_le rtranclp.simps)
      qed
      from ** [THEN sts_rtrancl_subset_shortlex] and \<open>R 0 = {}\<close>
      have R_shortlex:"\<And>i. i \<le> n \<Longrightarrow> R i \<subseteq> {(x, y). x \<succ>\<^sub>s\<^sub>l y}" by auto
      have msM1:"mshortlex_s M\<^sub>1 ?M"
      proof -
        have sgeu:"s \<succ>\<^sub>s\<^sub>l u" using su R_shortlex
          by (metis (no_types, lifting) R_shortlex case_prodD less_or_eq_imp_le mem_Collect_eq ststep_subset_S subsetD)
        from st have ne1: "M\<^sub>1 \<noteq> {#}" by (metis empty_iff mststep_iff set_mset_empty stM1)
        have MM1:"\<forall>u. u \<in># ?M \<longrightarrow> (\<exists>z. z \<in># M\<^sub>1 \<and> z \<succ>\<^sub>s\<^sub>l u)" using sgeu mststep_iff shortlex_trans stM1
          by (smt (verit, best) R_shortlex add_eq_conv_ex add_mset_eq_single case_prodD less_or_eq_imp_le 
              mem_Collect_eq multi_member_split ststep_subset_S subsetD) 
        from mulex_on_all_strict [OF ne1 _ _ this, of UNIV]
        have "mulex (\<succ>\<^sub>s\<^sub>l)\<inverse>\<inverse> ?M M\<^sub>1" 
          by (simp add:MM1 mulex_on_all_strict ne1)
        then show ?thesis using mshortlex_s_def by blast 
      qed
      have msM2:"mshortlex_s M\<^sub>2 ?M"
      proof -
        have steu:"s \<succ>\<^sub>s\<^sub>l t" using st R_shortlex
          by (metis (no_types, lifting) R_shortlex case_prodD less_or_eq_imp_le mem_Collect_eq ststep_subset_S subsetD)
        from st have ne2: "M\<^sub>2 \<noteq> {#}" by (metis empty_iff mststep_iff set_mset_empty suM2)
        have MM2:"\<forall>u. u \<in># ?M \<longrightarrow> (\<exists>z. z \<in># M\<^sub>2 \<and> z \<succ>\<^sub>s\<^sub>l u)" using steu mststep_iff shortlex_trans suM2
          by (smt (verit, ccfv_SIG) R_shortlex add_eq_conv_ex add_mset_eq_single case_prodD less_or_eq_imp_le mem_Collect_eq multi_member_split ststep_subset_S subsetD)       
        from mulex_on_all_strict [OF ne2 _ _ this, of UNIV]
        have "mulex (\<succ>\<^sub>s\<^sub>l)\<inverse>\<inverse> ?M M\<^sub>2" 
          by (simp add:MM2 mulex_on_all_strict ne2)
        then show ?thesis using mshortlex_s_def by blast 
      qed
      show "(t, u) \<in> ?D" using *
      proof
        assume "(t, u) \<in> (ststep (R n))\<^sup>\<down>"
        then obtain w where tw:"(t, w) \<in> (ststep (R n))\<^sup>*"
            and uw:"(u, w) \<in> (ststep (R n))\<^sup>*" by auto
        from ststeps_imp_mststeps [of _ ?M, OF _ tw R_shortlex]
        have twM:"(t, w) \<in> (mststep ?M (R n))\<^sup>\<leftrightarrow>\<^sup>*" by auto
        from lab.conversion_in_downset2 [OF twM] msM1
        have twD: "(t, w) \<in> ?D" by auto
        from ststeps_imp_mststeps [of _ ?M, OF _ uw R_shortlex]
        have uwM:"(u, w) \<in> (mststep ?M (R n))\<^sup>\<leftrightarrow>\<^sup>*" by auto
        from lab.conversion_in_downset2 [OF uwM] msM2
        have uwD: "(u, w) \<in> ?D" by auto
        hence "(t, u) \<in> ?D" using twD uwD ars_labeled.conversion_R_conv_iff ars_labeled.conv_trans
          by (meson ars_labeled.conv_commute ars_labeled.conv_in_I)
        then show ?thesis .
      next
        assume "(t, u) \<in> (\<Union>i\<le>n. (ststep (E i))\<^sup>\<leftrightarrow>)"
        then obtain i where iln:"i \<le> n" and "(t, u) \<in> (ststep (E i))\<^sup>\<leftrightarrow>" by auto
        hence "(t, u) \<in> (mststep ?M (E i))\<^sup>\<leftrightarrow>" by (auto iff: mststep_iff)
        hence "(t, u) \<in> (mststep ?M (E i \<union> R i))\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: conversion_def)
        then show ?thesis using iln
        proof(induct "n - i" arbitrary: i)
          case 0
          hence "i = n" by arith
          with 0 have tuM:"(t, u) \<in> (mststep ?M (R n))\<^sup>\<leftrightarrow>\<^sup>*" by (simp add: assms)
          from lab.conversion_in_downset2 [OF tuM] msM1 
          show ?case by auto
        next
          case (Suc m)
          from \<open>Suc m = n - i\<close> have *: "m = n - Suc i" and leq: "Suc i \<le> n" by auto
          from run have **: "(E i, R i) \<turnstile>\<^sub>S\<^sub>R (E (Suc i), R (Suc i))" using leq by auto
          from \<open>(t, u) \<in> (mststep ?M (E i \<union> R i))\<^sup>\<leftrightarrow>\<^sup>*\<close>
          have "(t, u) \<in> (mststep ?M (E (Suc i) \<union> R (Suc i)))\<^sup>\<leftrightarrow>\<^sup>*"
            using mststeps_subset [OF **  R_shortlex [OF leq]] by blast
          from Suc.hyps(1) [OF * this leq]
          show ?case by auto
        qed
      qed
    qed
    from pd.CR show ?thesis using UNIV_mstep_rstep_iff by auto
  qed
  then show "(s, t) \<in> (ststep (R n))\<^sup>\<down>"
    using En R0 run scp sts_critical_pair_CR sts_finite_run_SN by force
qed

(* Theorem 18 *)
theorem sts_finite_fair_run_complete:
  assumes R0:"R 0 = {}" and En:"E n = {}"
    and run:"\<forall>i < n. (E i, R i) \<turnstile>\<^sub>S\<^sub>R (E (Suc i), R (Suc i))"
    and fair: "sts_critical_pairs (R n) \<subseteq> (\<Union> i \<le> n. (ststep (E i))\<^sup>\<leftrightarrow>)"
  shows "complete (ststep (R n))" using assms
    by (meson En R0 complete_on_def fair run sts_finite_fair_run sts_finite_run_SN)

end

end