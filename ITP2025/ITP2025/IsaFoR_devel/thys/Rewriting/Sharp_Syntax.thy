(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Overloading for the Sharp Symbol\<close>

theory Sharp_Syntax
imports
  First_Order_Rewriting.Trs
begin

consts SHARP :: "'a \<Rightarrow> 'b" ("\<sharp>")

locale sharp_syntax =
  fixes shp :: "'f \<Rightarrow> 'f"
begin

adhoc_overloading SHARP \<rightleftharpoons> shp

end

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

fun sharp_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "sharp_term (Var x) = Var x" |
  "sharp_term (Fun f ss) = Fun (\<sharp> f) ss"

fun sharp_ctxt :: "('f, 'v) ctxt \<Rightarrow> ('f, 'v) ctxt"
where
  "sharp_ctxt \<box> = \<box>" |
  "sharp_ctxt (More f ss\<^sub>1 C ss\<^sub>2) = More (\<sharp> f) ss\<^sub>1 C ss\<^sub>2"

abbreviation sharp_sig :: "('f \<times> nat) set \<Rightarrow> ('f \<times> nat) set"
where
  "sharp_sig \<equiv> image (\<lambda>(f, n). (\<sharp> f, n))"
end

context sharp_syntax
begin

adhoc_overloading
  SHARP \<rightleftharpoons> "sharp_term shp" "sharp_ctxt shp" "sharp_sig shp"

end

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

lemma sharp_term_ctxt_apply [simp]:
  "C \<noteq> \<box> \<Longrightarrow> \<sharp>(C\<langle>t\<rangle>) = (\<sharp> C)\<langle>t\<rangle>"
  by (cases C) simp_all

lemma supt_sharp_term_subst [simp]:
  "\<sharp> s \<cdot> \<sigma> \<rhd> t \<longleftrightarrow> s \<cdot> \<sigma> \<rhd> t"
by (cases s) auto

end

lemma sharp_term_id [simp]:
  "sharp_term id t = t"
  "sharp_term (\<lambda>x. x) t = t"
  by (induct t) simp_all


text \<open>A theory on first-order term rewrite systems (TRSs).\<close>

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

abbreviation sharp_trs :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "sharp_trs R \<equiv> dir_image R \<sharp>"

end

context sharp_syntax
begin

adhoc_overloading
  SHARP \<rightleftharpoons> "sharp_trs shp"

end

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

definition DP_on :: "'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "DP_on F R = {(s, t). \<exists>l r h us. s = \<sharp> l \<and> t = \<sharp> (Fun h us) \<and>
    (l, r) \<in> R \<and> r \<unrhd> Fun h us \<and> (h, length us) \<in> F \<and> \<not> l \<rhd> Fun h us}"

abbreviation "DP R \<equiv> DP_on {f. defined R f} R"

lemma nrrstep_imp_sharp_nrrstep: assumes "(s, t) \<in> nrrstep R"
  shows "(\<sharp> s, \<sharp> t) \<in> nrrstep R"
proof -
  from assms obtain C l r \<sigma> where "C \<noteq> \<box>" and "(l, r) \<in> R"
    and *: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    by (auto elim: nrrstepE)
  then obtain D f ss ts where "C = More f ss D ts"
    and "s = Fun f (ss @ D\<langle>l \<cdot> \<sigma>\<rangle> # ts)" by (cases C) (auto elim: sharp_term.elims)
  moreover with \<open>t = C\<langle>r \<cdot> \<sigma>\<rangle>\<close> have "t = Fun f (ss @ D\<langle>r \<cdot> \<sigma>\<rangle> # ts)"
    using assms by auto
  moreover define C' where "C' = More (\<sharp> f) ss D ts"
  ultimately have "\<sharp> s = C'\<langle>l \<cdot> \<sigma>\<rangle>" and "\<sharp> t = C'\<langle>r \<cdot> \<sigma>\<rangle>" by simp+
  moreover have "C' \<noteq> \<box>" using \<open>C \<noteq> \<box>\<close> by (simp add: C'_def)
  ultimately show "(\<sharp> s, \<sharp> t) \<in> nrrstep R" using \<open>(l, r) \<in> R\<close> by (auto simp: nrrstep_def')
qed

lemma nrrstep_imp_sharp_rstep:
  assumes "(s, t) \<in> nrrstep R"
  shows "(\<sharp> s, \<sharp> t) \<in> rstep R"
  using nrrstep_imp_sharp_nrrstep[OF assms] by (rule nrrstep_imp_rstep)

lemma nrrsteps_imp_sharp_rsteps:
  "(s, t) \<in> (nrrstep R)\<^sup>* \<Longrightarrow> (\<sharp> s, \<sharp> t) \<in> (rstep R)\<^sup>*"
proof (induct rule: rtrancl_induct)
  case (step a b)
  from \<open>(a,b) \<in> nrrstep R\<close> have "(\<sharp> a, \<sharp> b) \<in> rstep R"
    by (rule nrrstep_imp_sharp_rstep)
   with step show ?case by auto
qed simp

lemma finiteR_imp_finiteDP:
  assumes "finite R"
  shows "finite (DP_on F R)"
proof -
  have fS: "finite {(l, r, u).
    \<exists>h us. u = Fun h us \<and> (l,r) \<in> R \<and> r \<unrhd> u \<and> (h, length us) \<in> F \<and> \<not>(l \<rhd> u)}" (is "finite ?S")
  using assms by (rule finite_imp_finite_DP_on')
  let ?f = "\<lambda>(x :: ('f, 'v) term, y, z :: ('f, 'v) term). (\<sharp> x, \<sharp> z)"
  have eq1: "(\<Union>y\<in>?S. {x. x = ?f y}) = ?f ` ?S" by blast
  with fS have "finite(?f ` ?S)" by auto
  have "DP_on F R = ?f ` ?S" (is "?DP = ?T")
  proof
    show "?DP \<subseteq> ?T"
    proof
      fix x assume "x \<in> ?DP"
      then obtain l r h us
        where "fst x = \<sharp> l" and "snd x = \<sharp> (Fun h us)"
        and "(l,r) \<in> R" "r \<unrhd> Fun h us" and "(h, length us) \<in> F" and " \<not>(l \<rhd> Fun h us)"
        by (auto simp: DP_on_def split_def)
      then have "(l,r,Fun h us) \<in> ?S" by auto
      then show "x \<in> ?T" unfolding eq1[symmetric]
      proof (rule UN_I)
        have "x = (fst x, snd x)" by simp
        then have "x = (\<sharp> l, \<sharp> (Fun h us))"
          unfolding \<open>fst x = \<sharp> l\<close> \<open>snd x = \<sharp> (Fun h us)\<close> .
        then show "x \<in> {x. x = ?f (l,r,Fun h us)}" by auto
      qed
    qed
  next
    show "?T \<subseteq> ?DP"
    proof
      fix x assume "x \<in> ?T"
      then have "x \<in> (\<Union>y\<in>?S. {x. x = ?f y})" unfolding eq1 .
      then obtain y where "y \<in> ?S" and "x = ?f y" by fast
      then obtain l r h us where "y = (l, r, Fun h us)" and dp: "(l, r) \<in> R"
        and "r \<unrhd> Fun h us" and "(h, length us) \<in> F" and "\<not> (l \<rhd> Fun h us)" by blast
      moreover with \<open>x = ?f y\<close> have "x = (\<sharp> l, \<sharp> (Fun h us))" by auto
      ultimately show "x \<in> ?DP" using dp unfolding DP_on_def by auto
    qed
  qed
  with fS show ?thesis by auto
qed

lemma vars_sharp_eq_vars [simp]: "vars_term (\<sharp> t) = vars_term t"
by (induct t) auto

lemma wf_trs_imp_wf_DP_on:
 assumes "wf_trs R"
 shows "wf_trs (DP_on F R)"
unfolding wf_trs_def
proof (intro allI impI)
  fix s t
  assume "(s,t) \<in> DP_on F R"
  then obtain l r h us where "s = \<sharp> l" and "t = \<sharp> (Fun h us)" and "(l, r) \<in> R"
    and "r \<unrhd> (Fun h us)" "\<not> (l \<rhd> Fun h us)"
    by (auto simp:DP_on_def)
  from \<open>wf_trs R\<close> and \<open>(l,r) \<in> R\<close>
    have "\<exists>f ss. l = Fun f ss" and "vars_term r \<subseteq> vars_term l" by (auto simp: wf_trs_def)
  from \<open>\<exists>f ss. l = Fun f ss\<close> obtain f ss where "l = Fun f ss" by auto
  then have "s = Fun (\<sharp> f) ss" unfolding \<open>s = \<sharp> l\<close> by simp
  then have "\<exists>f ss. s = Fun f ss" by auto
  from \<open>r \<unrhd> Fun h us\<close> have "vars_term(Fun h us) \<le> vars_term r" by (induct rule: supteq.induct) auto
  then have "vars_term t \<subseteq> vars_term s" unfolding \<open>s = \<sharp> l\<close>
    and \<open>t = \<sharp> (Fun h us)\<close> vars_sharp_eq_vars using \<open>vars_term r \<le> vars_term l\<close> by simp
  from \<open>\<exists>f ss. s = Fun f ss\<close> \<open>vars_term t \<subseteq> vars_term s\<close>
  show "(\<exists>f ss. s = Fun f ss) \<and> vars_term t \<subseteq> vars_term s" by simp
qed

lemma sharp_eq_imp_eq:
  fixes s :: "('f, 'v) term"
  assumes "inj (\<sharp> :: 'f \<Rightarrow> 'f)"
  shows "\<sharp> s = \<sharp> t \<Longrightarrow> s = t"
proof (cases s)
  case (Var x)
  assume "\<sharp> s = \<sharp> t" with Var show ?thesis by (induct t) auto
next
  case (Fun f ss)
  assume "\<sharp> s = \<sharp> t"
  with Fun have "\<sharp> (Fun f ss) = \<sharp> t" by simp
  then obtain g ts where t: "t = Fun g ts" by (induct t) auto
  with \<open>\<sharp> s = \<sharp> t\<close> have "Fun (\<sharp> f) ss = Fun (\<sharp> g) ts" unfolding \<open>s = Fun f ss\<close> \<open>t = Fun g ts\<close>
    by simp
  then have "f = g" and "ss = ts" using \<open>inj (\<sharp> :: 'f \<Rightarrow> 'f)\<close>[unfolded inj_on_def] by auto
  then show ?thesis unfolding Fun t by simp
qed

lemma DP_on_step_in_R:
  fixes R :: "('f, 'v) trs" and v :: "('f, 'v) term \<Rightarrow> 'v"
  assumes "(s, t) \<in> DP_on F R" and inj: "inj (\<sharp> :: 'f \<Rightarrow> 'f)"
  shows "\<exists>C. funas_ctxt C \<subseteq> funas_trs R \<and>
    (sharp_term (the_inv \<sharp>) s, C\<langle>sharp_term (the_inv \<sharp>) t\<rangle>) \<in> R"
proof -
  let ?us = "sharp_term (the_inv (\<sharp> :: 'f \<Rightarrow> 'f))"
  from assms obtain l r f ts
    where s: "s = \<sharp> l" and t: "t = \<sharp> (Fun f ts)"
    and R: "(l,r) \<in> R" and sub: "r \<unrhd> Fun f ts" unfolding DP_on_def supt_supteq_conv by auto
  from sub obtain C where r: "r = C\<langle>Fun f ts\<rangle>" by auto
  from rhs_wf[OF R subset_refl] have "funas_term r \<subseteq> funas_trs R" .
  then have "funas_term (C\<langle>Fun f ts\<rangle>) \<subseteq> funas_trs R" unfolding r .
  then have  "funas_ctxt C \<subseteq> funas_trs R" and "funas_term (Fun f ts) \<subseteq> funas_trs R" by auto
  from lhs_wf[OF R subset_refl] have "funas_term l \<subseteq> funas_trs R" .
  have us: "?us s = l" unfolding s by (cases l, auto simp: the_inv_f_f[OF inj])
  have ut: "?us t = Fun f ts" unfolding t by (simp add: the_inv_f_f[OF inj])
  from R have "(?us s,C\<langle>?us t\<rangle>) \<in> R" unfolding us ut r .
  with \<open>funas_ctxt C \<subseteq> funas_trs R\<close> show ?thesis by best
qed

lemma sharp_rrstep_imp_rstep:
  assumes rrstep: "(\<sharp> s, \<sharp> t) \<in> subst.closure (DP_on F R)" and "inj (\<sharp> :: 'f \<Rightarrow> 'f)" and "wf_trs R"
  shows "\<exists>C. (s, C\<langle>t\<rangle>) \<in> rstep R"
proof -
  from \<open>wf_trs R\<close> have "wf_trs (DP_on F R)" by (rule wf_trs_imp_wf_DP_on)
  from rrstep obtain l r \<sigma> where "(l,r) \<in> DP_on F R" and ss: "\<sharp> s = l\<cdot>\<sigma>" and st: "\<sharp> t = r\<cdot>\<sigma>"
   by (induct, auto)
  from \<open>(l,r) \<in> DP_on F R\<close> obtain l' r' h' us'
    where l: "l = \<sharp> l'" and r: "r = \<sharp> (Fun h' us')" (is "r = \<sharp> ?u'")
    and l'r': "(l',r') \<in> R" and "r' \<unrhd> (Fun h' us')" and "\<not> l' \<rhd> Fun h' us'"
    unfolding DP_on_def by auto
  from \<open>wf_trs R\<close> and \<open>(l',r') \<in> R\<close> obtain f' ss' where l': "l' = Fun f' ss'" using wf_trs_imp_lhs_Fun by best
  from \<open>r' \<unrhd> ?u'\<close> obtain C where r': "r' = C\<langle>?u'\<rangle>" by best
  have ss: "\<sharp> s = (Fun (\<sharp> f') ss') \<cdot> \<sigma>" unfolding ss l l' by simp
  then obtain f where s: "s = (Fun f ss') \<cdot> \<sigma>" by (cases s, auto)
  from s ss have "\<sharp> f = \<sharp> f'" by simp
  with \<open>inj (\<sharp> :: 'f \<Rightarrow> 'f)\<close>[unfolded inj_on_def] have f: "f = f'" by simp
  have ts: "\<sharp> t = (Fun (\<sharp> h') us') \<cdot> \<sigma>" unfolding st r by simp
  then obtain h where t: "t = (Fun h us') \<cdot> \<sigma>" by (cases t, auto)
  from t ts have "\<sharp> h = \<sharp> h'" by simp
  with \<open>inj (\<sharp> :: 'f \<Rightarrow> 'f)\<close>[unfolded inj_on_def] have h: "h = h'" by simp
  show ?thesis
   by (rule exI[of _ "C \<cdot>\<^sub>c \<sigma>"], unfold s t f h, rule rstepI[OF l'r', of _ \<box> \<sigma>], unfold l' r', simp, simp)
qed

definition DP_simple :: " 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "DP_simple D R = {(s, t).
    \<exists>l r h us. s = \<sharp> l \<and> t = \<sharp> (Fun h us) \<and> (l, r) \<in> R \<and> (h, length us) \<in> D \<and> r \<unrhd> Fun h us}"

lemma DP_on_subset_DP_simple: "DP_on F R \<subseteq> DP_simple F R"
by (auto simp: DP_on_def DP_simple_def)

lemma funas_DP_simple_subset:
  "funas_trs (DP_simple D R) \<subseteq> funas_trs R \<union> \<sharp> (funas_trs R)"
  (is "?F \<subseteq> ?H \<union> ?I")
proof (rule subrelI)
  fix f n
  assume "(f,n) \<in> ?F"
  then obtain s t where st: "(s,t) \<in> DP_simple D R" and "(f,n) \<in> funas_rule (s,t)"
    unfolding funas_trs_def by auto
  then obtain u where fn: "(f,n) \<in> funas_term u" and u: "u = s \<or> u = t" unfolding funas_rule_def
    by auto
  from st[unfolded DP_simple_def] obtain l r uu where lr: "(l,r) \<in> R" and s: "s = \<sharp> l" and t: "t = \<sharp> uu" and uu: "r \<unrhd> uu"
    by force
  from fn u[unfolded s t] obtain v where fn: "(f, n) \<in> funas_term (\<sharp> v)" and v: "v = l \<or> v = uu" by auto
  from fn have fn: "(f, n) \<in> funas_term v \<union> \<sharp> (funas_term v)"
    by (cases v, auto)
  from uu obtain C where r: "r = C\<langle>uu\<rangle>" ..
  have "funas_term uu \<subseteq> funas_term r" unfolding r by simp
  with v have "funas_term v \<subseteq> funas_rule (l,r)" unfolding funas_rule_def by auto
  then have subset: "funas_term v \<subseteq> funas_trs R" using lr unfolding funas_trs_def by auto
  with fn show "(f,n) \<in> ?H \<union> ?I" by auto
qed

lemma funas_DP_on_subset:
  "funas_trs (DP_on F R) \<subseteq> funas_trs R \<union> \<sharp> (funas_trs R)"
by (rule order.trans [OF _ funas_DP_simple_subset [of F]])
   (insert DP_on_subset_DP_simple, auto simp: funas_trs_def)

end

end

