(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Reduction_Order
imports 
  First_Order_Rewriting.Trs
begin

locale reduction_order =
  fixes less :: "('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
  assumes SN_less: "SN {(x, y). x \<succ> y}"
    and ctxt: "s \<succ> t \<Longrightarrow> C\<langle>s\<rangle> \<succ> C\<langle>t\<rangle>"
    and subst: "s \<succ> t \<Longrightarrow> s \<cdot> \<sigma> \<succ> t \<cdot> \<sigma>"
    and trans: "s \<succ> t \<Longrightarrow> t \<succ> u \<Longrightarrow> s \<succ> u"
begin

abbreviation less_set ("{\<succ>}")
where
  "{\<succ>} \<equiv> {(x, y). x \<succ> y}"

lemma subst_closed_less: "subst.closed {\<succ>}"
using subst by auto

lemma ctxt_closed_less: "ctxt.closed {\<succ>}"
using ctxt by auto

lemma trans_less: "trans {\<succ>}" by (auto simp: trans_def dest: trans)

lemma trancl_less_set [simp]: "{\<succ>}\<^sup>+ = {\<succ>}"
by (auto elim: trancl.induct dest: trans)

lemma rtancl_less_set [simp]: "{\<succ>}\<^sup>* = {\<succ>}\<^sup>="
by (unfold rtrancl_trancl_reflcl) simp

lemma irrefl: "\<not> s \<succ> s"
  using SN_less by (auto simp: SN_defs)

lemma less_neq:
  "s \<succ> t \<Longrightarrow> s \<noteq> t"
  "s \<succ> t \<Longrightarrow> t \<noteq> s"
  by (auto simp: irrefl)

abbreviation lesseq (infix "\<succeq>" 50) where
  "s \<succeq> t \<equiv> (\<succ>)\<^sup>=\<^sup>= s t"

lemma compatible_rstep_imp_less:
  assumes "R \<subseteq> {\<succ>}"
    and "(s, t) \<in> rstep R"
  shows "s \<succ> t"
  using assms (2, 1) by (induct) (auto intro: subst ctxt)

lemma compatible_rstep_trancl_imp_less:
  assumes "R \<subseteq> {\<succ>}"
    and "(s, t) \<in> (rstep R)\<^sup>+"
  shows "s \<succ> t"
  using assms(2) and compatible_rstep_imp_less [OF assms(1)]
    by (induct) (auto dest: trans)

end

definition "fground F t \<longleftrightarrow> funas_term t \<subseteq> F \<and> ground t"
definition "FGROUND F r = Restr r {t. fground F t}"
                                          
locale fgtotal_reduction_order = reduction_order +
  fixes F :: "('a \<times> nat) set"
  assumes fgtotal: "fground F s \<Longrightarrow> fground F t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"
  and funas_less: "funas_trs {\<succ>} \<subseteq> F"

locale gtotal_reduction_order = fgtotal_reduction_order less UNIV
  for less :: "('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)

\<comment> \<open>reduction orders that are total on \<open>E\<close>-euqivalent ground terms\<close>
locale egtotal_reduction_order = reduction_order +
  fixes E
  assumes egtotal: "(s, t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> ground s \<Longrightarrow> ground t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"

end
