(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>String Rewriting\<close>

theory String_Rewriting
  imports
   "HOL-Library.Sublist"
    ShortLex
begin

text \<open>STS (semi-Thus system) is a set of string rewriting rules \<close>
type_synonym srule = "string \<times> string"
type_synonym sts  = "srule set"

inductive_set ststep :: "sts \<Rightarrow> sts" for R 
  where
    ststep: "\<And>bef aft. (l, r) \<in> R \<Longrightarrow> s = bef @ l @ aft \<Longrightarrow> t = bef @ r @ aft \<Longrightarrow> (s, t) \<in> ststep R"

lemmas ststepI = ststep.intros [intro]
lemmas ststepE = ststep.cases [elim]

lemma ststep_incl[simp]: "R \<subseteq> ststep R" 
proof(intro subrelI)
  fix l r
  assume "(l, r) \<in> R"
  then show "(l, r) \<in> ststep R" unfolding ststep.simps by blast
qed

lemma ststep_mono[simp]: "R \<subseteq> S \<Longrightarrow> ststep R \<subseteq> ststep S" by force

lemma ststep_union[simp]: "ststep (R \<union> S) = ststep R \<union> ststep S" by auto

lemma ststep_empty [simp]: "ststep {} = {}" by auto

lemma ststep_ID [simp]: "ststep Id = Id"
proof
  show "ststep Id \<subseteq> Id"
  proof(intro subrelI)
    fix s t
    assume "(s, t) \<in> ststep Id"
    then show "(s, t) \<in> Id" by auto
  qed
qed auto

lemma ststep_converse[simp]: "ststep (R\<inverse>) = (ststep R)\<inverse>" by auto

lemma ststep_closed[simp]:"ststep (ststep R) = ststep R" (is "?lhs = ?rhs")
proof 
  show "?lhs \<subseteq> ?rhs" unfolding ststep.simps
  proof(intro subrelI)
    fix s t
    assume "(s, t) \<in> ststep (ststep R)"
    hence "\<exists>bef1 aft1 l1 r1. (l1, r1) \<in> ststep R \<and> s = bef1 @ l1 @ aft1 \<and> t = bef1 @ r1 @ aft1" by blast
    then obtain bef1 aft1 l1 r1 where l1r1:"(l1, r1) \<in> ststep R" and s':"s = bef1 @ l1 @ aft1" and t':"t = bef1 @ r1 @ aft1" by auto
    from l1r1 have "\<exists>bef2 aft2 l r. (l, r) \<in> R \<and> l1 = bef2 @ l @ aft2 \<and> r1 = bef2 @ r @ aft2" by blast
    then obtain bef2 aft2 l r where lr:"(l, r) \<in> R" and l1:"l1 = bef2 @ l @ aft2" and r1:"r1 = bef2 @ r @ aft2" by auto
    have s:"s = bef1 @ bef2 @ l @ aft2 @ aft1" and t:"t = bef1 @ bef2 @ r @ aft2 @ aft1" 
      by (auto simp add:s' t' l1 r1) 
    show "(s, t) \<in> ststep R"
      by (simp add:s t ststepI, insert lr append_eq_appendI, blast) 
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof(intro subrelI)
    fix s t
    assume "(s, t) \<in> ststep R"
    then show "(s, t) \<in> ststep (ststep R)"
      using ststep_incl by blast
  qed
qed
  
lemma ststep_reflcl[simp]: "ststep (R\<^sup>=) = (ststep R)\<^sup>=" by simp
 
lemma ststep_symcl[simp]: "ststep (R\<^sup>\<leftrightarrow>) = (ststep R)\<^sup>\<leftrightarrow>"
proof
  show "ststep (R\<^sup>\<leftrightarrow>) \<subseteq> (ststep R)\<^sup>\<leftrightarrow>"
  proof(intro subrelI)
    fix s t
    assume "(s, t) \<in> ststep (R\<^sup>\<leftrightarrow>)"
    hence "\<exists>bef aft l r. (l, r) \<in> R\<^sup>\<leftrightarrow> \<and> s = bef @ l @ aft \<and> t = bef @ r @ aft" by blast
    then obtain bef aft l r where lr:"(l, r) \<in> R\<^sup>\<leftrightarrow>" and s:"s = bef @ l @ aft" and t:"t = bef @ r @ aft" by auto
    from lr show "(s, t) \<in> (ststep R)\<^sup>\<leftrightarrow>"
      by (cases "(l, r) \<in> R", insert s t, blast+)
  qed  
next
  show "(ststep R)\<^sup>\<leftrightarrow> \<subseteq> ststep (R\<^sup>\<leftrightarrow>)"
  proof(intro subrelI)
    fix s t
    assume "(s, t) \<in> (ststep R)\<^sup>\<leftrightarrow>"
    then show "(s, t) \<in> ststep (R\<^sup>\<leftrightarrow>)"
    proof
      assume "(s, t) \<in> (ststep R)\<inverse>"
      then show ?thesis by blast
    qed auto
  qed
qed

lemma sts_incl_conv[simp]: "(ststep (E \<union> R))\<^sup>\<leftrightarrow> O (ststep R)\<^sup>= \<subseteq> (ststep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
proof(rule subrelI)
  fix l r
  assume "(l, r) \<in> (ststep (E \<union> R))\<^sup>\<leftrightarrow> O (ststep R)\<^sup>="
  then obtain u where lu:"(l, u) \<in> (ststep (E \<union> R))\<^sup>\<leftrightarrow>" and ur:"(u, r) \<in> (ststep R)\<^sup>=" by auto
  from ur show "(l, r) \<in> (ststep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  proof(cases "u = r")
    case True
    then show ?thesis using lu by blast
  next
    case False note F1 = this
    from lu show ?thesis
    proof(cases "(l, u) \<in> ststep (E \<union> R)")
      case True
      from ur have "(u, r) \<in> ststep (E \<union> R)" using F1 by auto
      then show ?thesis 
        by (meson True converse_rtrancl_into_rtrancl conversionI' r_into_rtrancl)
    next
      case False
      from ur have "(u, r) \<in> ststep (E \<union> R)" using F1 by auto
      then show ?thesis
        by (meson UnCI converse_rtrancl_into_rtrancl conversionI lu r_into_rtrancl)
    qed
  qed
qed

lemma ststep_sctxt [intro]: "(s, t) \<in> ststep R \<Longrightarrow> (C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> ststep R"
proof -
  assume "(s, t) \<in> ststep R"
  hence "\<exists>bef aft l r. (l, r) \<in> R \<and> s = bef @ l @ aft \<and> t = bef @ r @ aft" by blast
  then obtain bef aft l r where lr:"(l, r) \<in> R" 
    and s:"s = bef @ l @ aft" and t:"t = bef @ r @ aft" by auto
  have "\<exists>bef' aft'. C\<llangle>s\<rrangle> = bef'@ s @ aft' \<and> C\<llangle>t\<rrangle> = bef'@ t @ aft'" 
    using sctxt_apply_string.simps
  proof(induct C)
    case Hole
    then show ?case using hole empty_append by metis
  next
    case (More x1 C x3)
    then show ?case  by (metis append_assoc)
  qed
  then obtain bef' aft' where cs:"C\<llangle>s\<rrangle> = bef'@ s @ aft'" and ct:"C\<llangle>t\<rrangle> = bef'@ t @ aft'" by blast
  then show "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> ststep R" using append.assoc cs ct lr s t ststepI
    by metis
qed

lemma ststeps_closed_sctxt[simp]:
  assumes "(s, t) \<in> (ststep R)\<^sup>*"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> (ststep R)\<^sup>*" 
  using assms ststep_sctxt sctxt.closed_rtrancl
  by (simp add: sctxt.closedD sctxt.closedI)

lemma ststeps_sym_closed_sctxt[simp]:
  assumes "(s, t) \<in> (ststep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> (ststep R)\<^sup>\<leftrightarrow>\<^sup>*" 
  by (simp add: assms sctxt.closedD sctxt.closedI sctxt.closed_conversion ststep_sctxt)

lemma sclosed_trancl[simp]: "ststep ((ststep R)\<^sup>\<leftrightarrow>\<^sup>*) =  (ststep R)\<^sup>\<leftrightarrow>\<^sup>*"
proof
  show "ststep ((ststep R)\<^sup>\<leftrightarrow>\<^sup>*) \<subseteq> (ststep R)\<^sup>\<leftrightarrow>\<^sup>*"
  proof(rule subrelI)
    fix s t
    assume "(s, t) \<in> ststep ((ststep R)\<^sup>\<leftrightarrow>\<^sup>*)"
    hence "\<exists>l r bef aft. (l, r) \<in> (ststep R)\<^sup>\<leftrightarrow>\<^sup>* \<and> s = bef @ l @ aft \<and> t = bef @ r @ aft" by blast
    then obtain l r bef aft where lr:"(l, r) \<in> (ststep R)\<^sup>\<leftrightarrow>\<^sup>*" and s:"s = bef @ l @ aft" and t:"t = bef @ r @ aft" by auto
    let ?C = "More bef \<circle> aft"
    from ststeps_sym_closed_sctxt[OF lr, of ?C]
    show "(s, t) \<in> (ststep R)\<^sup>\<leftrightarrow>\<^sup>*"
      by (simp add: s t)
  qed
qed auto

lemma ststep_rule [intro]: "(l, r) \<in> R \<Longrightarrow> (l, r) \<in> ststep R"
  using ststep.ststep empty_append by blast

lemma sctxt_closed_ststeps [intro]: "sctxt.closed ((ststep R)\<^sup>*)" by blast
lemma sctxt_closed_ststep [intro]: "sctxt.closed (ststep R)" by blast

lemma ststep_eq_closure: "ststep R = sctxt.closure R"
proof (auto elim: sctxt.closure.cases)
  fix a b
  assume asm:"(a,b) \<in> ststep R"
  hence "\<exists>l r. (l, r) \<in> R" by (meson ststepE)
  then obtain l r where lr:"(l, r) \<in> R" 
    and "\<exists> bef aft. a = bef @ l @ aft \<and> b = bef @ r @aft" by (meson asm ststepE)
  then obtain bef aft where "a = bef @ l @ aft" and "b = bef @ r @aft" by auto
  then have "\<exists>C. a = C\<llangle>l\<rrangle> \<and> b = C\<llangle>r\<rrangle>" 
    using sctxt_apply_string.simps by metis
  then obtain C where a:"a = C\<llangle>l\<rrangle>" and b:"b = C\<llangle>r\<rrangle>" by auto
  from sctxt.closureI2[OF lr a b]
    show "(a, b) \<in> sctxt.closure R" by auto
qed

(* Lemma 5 *)
lemma sts_CR_WCR:
  fixes R :: "sts"
  assumes sn: "SN (ststep R)"
  shows "CR (ststep R) \<longleftrightarrow> WCR (ststep R)" using assms
    by (meson CR_onE Newman WCR_onI r_into_rtrancl)

definition ststep_c_s :: "sts  \<Rightarrow> sts"
  where "ststep_c_s R = {(s,t) | s t rl C. rl \<in> R \<and> s = C\<llangle>fst rl\<rrangle> \<and> t = C\<llangle>snd rl\<rrangle>}"

lemma ststep_iff_ststep_r_s:
  "(s, t) \<in> ststep R \<longleftrightarrow> (s, t) \<in> ststep_c_s R" (is "?lhs = ?rhs")
proof
  assume asm:"(s, t) \<in> ststep R"
  hence "\<exists>l r. (l, r) \<in> R" by (meson ststepE)
  then obtain l r where lr:"(l, r) \<in> R" 
    and "\<exists> bef aft. s = bef @ l @ aft \<and> t = bef @ r @aft" by (meson asm ststepE)
  then obtain bef aft where "s = bef @ l @ aft" and "t = bef @ r @aft" by auto
  then have "\<exists>C. s = C\<llangle>l\<rrangle> \<and> t = C\<llangle>r\<rrangle>" 
    using sctxt_apply_string.simps by metis
  then obtain C where a:"s = C\<llangle>l\<rrangle>" and b:"t = C\<llangle>r\<rrangle>" by auto
  then show ?rhs unfolding ststep_c_s_def using lr by auto
next
  assume ?rhs
  then obtain l r C where rl:"(l, r) \<in> R" and s:"s = C\<llangle>l\<rrangle>" and t:"t = C\<llangle>r\<rrangle>" 
    unfolding ststep_c_s_def by auto
  then show ?lhs by auto
qed

lemma ststep_ststep_c_s_iff:
  "ststep R = ststep_c_s R" using ststep_iff_ststep_r_s by auto

lemma sctxt_closed_SN_on_sublist:
  assumes sc:"sctxt.closed R" and "SN_on R {t}" and sub:"sublist s t"
  shows "SN_on R {s}"
proof (rule ccontr)
  assume "\<not> SN_on R {s}"
  then obtain A where s:"A 0 = s" and A_chain:"\<forall>i. (A i,A (Suc i)) \<in> R"
    unfolding SN_on_def by best
  from sub have "\<exists>bef aft. t = bef @ s @ aft" 
    by (simp add: sublist_def)
  then obtain C where t:"t = C\<llangle>s\<rrangle>" using sctxt_apply_string.simps
    by metis
  let ?B = "\<lambda>i. C\<llangle>A i\<rrangle>"
  have "\<forall>i. (?B i,?B(Suc i)) \<in> R"
  proof
    fix i
    from A_chain have "(?B i,?B(Suc i)) \<in> sctxt.closure R" by fast
    then show "(?B i,?B(Suc i)) \<in> R" using sc by auto
  qed
  with s have "?B 0 = t \<and> (\<forall>i. (?B i,?B(Suc i)) \<in> R)" using t by simp
  then have "\<not> SN_on R {t}" unfolding SN_on_def by auto
  with assms show "False" by simp
qed

lemma sublist_preserves_SN_gen:
  assumes sctxt: "sctxt.closed R"
  and SN: "SN_on R {t}" and sslist: "strict_sublist s t"
  shows "SN_on R {s}"
proof -
  from sslist have "sublist s t" by auto
  then show ?thesis 
    using sctxt_closed_SN_on_sublist[OF sctxt SN, of s] by simp
qed

lemma sublist_preserves_SN:
  "SN_on (ststep R) {t} \<Longrightarrow> sublist s t \<Longrightarrow> SN_on (ststep R) {s}"
  using sublist_preserves_SN_gen strict_sublist_def by blast

end

