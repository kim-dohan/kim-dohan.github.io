(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2017)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory More_Abstract_Rewriting
  imports
    "Abstract-Rewriting.Abstract_Rewriting"
    "Decreasing-Diagrams-II.Decreasing_Diagrams_II"
begin

section \<open>Results that belong to @\<open>theory Abstract_Rewriting\<close>\<close>

lemma rtrancl_eq_CR:
  assumes "r\<^sup>* = s\<^sup>*"
  shows "CR r \<longleftrightarrow> CR s"
  using assms by (auto simp: CR_defs join_def rtrancl_converse)

lemma diamond_I':
  assumes "\<And> s t u. (s, t) \<in> r \<Longrightarrow> (s, u) \<in> r \<Longrightarrow> \<exists> v. (t, v) \<in> r \<and> (u, v) \<in> r"
  shows "\<diamond> r"
  apply (intro diamond_I subrelI)
  apply (auto dest: relcompE)
  subgoal for t s u
    using assms[of s u t] by auto
  done

subsection \<open>Commutation\<close>

text \<open>Short notation for diamond commutation of two relations.\<close>
definition "comm r s \<longleftrightarrow>
  (\<forall>x y z. (x, y) \<in> r \<and> (x, z) \<in> s \<longrightarrow> (\<exists>u. (y, u) \<in> s \<and> (z, u) \<in> r))"

lemma commI [intro?]:
  assumes "\<And>x y z. \<lbrakk>(x, y) \<in> r; (x, z) \<in> s\<rbrakk> \<Longrightarrow> (\<exists>u. (y, u) \<in> s \<and> (z, u) \<in> r)"
  shows "comm r s"
  using assms by (auto simp: comm_def)

lemma commE:
  assumes "comm r s" and "(x, y) \<in> r" and "(x, z) \<in> s"
  obtains u where "(y, u) \<in> s" and "(z, u) \<in> r"
  using assms by (force simp: comm_def)

lemma comm_swap:
  "comm r s \<longleftrightarrow> comm s r"
  by (auto elim: commE intro!: commI)

lemma comm_rtrancl:
  assumes "comm r s"
  shows "comm (r\<^sup>*) s"
proof
  fix x y z
  assume "(x, y) \<in> r\<^sup>*" and "(x, z) \<in> s"
  then show "\<exists>u. (y, u) \<in> s \<and> (z, u) \<in> r\<^sup>*" (is "\<exists>u. ?P u y z")
  proof (induct)
    case base
    moreover have "(z, z) \<in> r\<^sup>*" by blast
    ultimately show ?case by blast
  next
    case (step a b)
    then obtain u where "(a, u) \<in> s" and "(z, u) \<in> r\<^sup>*" by blast
    moreover with \<open>(a, b) \<in> r\<close> and \<open>comm r s\<close> obtain v
      where "(b, v) \<in> s" and "(u, v) \<in> r\<^sup>*" by (blast elim: commE)
    ultimately have "(b, v) \<in> s" and "(z, v) \<in> r\<^sup>*" by auto
    then show ?case by blast
  qed
qed

definition locally_commute :: "'a rel \<Rightarrow> 'a rel  \<Rightarrow> bool"
where
  "locally_commute r\<^sub>1 r\<^sub>2 \<longleftrightarrow>
    (\<forall>x y\<^sub>1 y\<^sub>2. (x, y\<^sub>1) \<in> r\<^sub>1 \<and> (x, y\<^sub>2) \<in> r\<^sub>2 \<longrightarrow> (\<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>* \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*))"

lemma locally_commute_E11:
  "locally_commute r\<^sub>1 r\<^sub>2 \<Longrightarrow> (x, y) \<in> r\<^sub>1 \<Longrightarrow> (x, z) \<in> r\<^sub>2 \<Longrightarrow>
    \<exists>u. (z, u) \<in> r\<^sub>1\<^sup>* \<and> (y, u) \<in> r\<^sub>2\<^sup>*"
unfolding locally_commute_def by blast

lemma locally_commuteI [intro]:
  "\<lbrakk>\<And>x y\<^sub>1 y\<^sub>2. (x, y\<^sub>1) \<in> r\<^sub>1 \<Longrightarrow> (x, y\<^sub>2) \<in> r\<^sub>2 \<Longrightarrow> \<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>* \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*\<rbrakk> \<Longrightarrow> locally_commute r\<^sub>1 r\<^sub>2"
unfolding locally_commute_def by auto

definition strongly_commute :: "'a rel \<Rightarrow> 'a rel  \<Rightarrow> bool"
where
  "strongly_commute r\<^sub>1 r\<^sub>2 \<longleftrightarrow>
    (\<forall>x y\<^sub>1 y\<^sub>2. (x, y\<^sub>1) \<in> r\<^sub>1 \<and> (x, y\<^sub>2) \<in> r\<^sub>2 \<longrightarrow> (\<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>= \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*))"

lemma strongly_commute_E11:
  "strongly_commute r\<^sub>1 r\<^sub>2 \<Longrightarrow> (x, y) \<in> r\<^sub>1 \<Longrightarrow> (x, z) \<in> r\<^sub>2 \<Longrightarrow>
    \<exists>u. (z, u) \<in> r\<^sub>1\<^sup>* \<and> (y, u) \<in> r\<^sub>2\<^sup>="
unfolding strongly_commute_def by blast

lemma strongly_commuteI [intro]:
  "\<lbrakk>\<And>x y\<^sub>1 y\<^sub>2. (x, y\<^sub>1) \<in> r\<^sub>1 \<Longrightarrow> (x, y\<^sub>2) \<in> r\<^sub>2 \<Longrightarrow> \<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>= \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*\<rbrakk> \<Longrightarrow> strongly_commute r\<^sub>1 r\<^sub>2"
unfolding strongly_commute_def by auto

lemma commuteI [intro]:
  "\<lbrakk>\<And>x y\<^sub>1 y\<^sub>2. (x, y\<^sub>1) \<in> r\<^sub>1\<^sup>* \<Longrightarrow> (x, y\<^sub>2) \<in> r\<^sub>2\<^sup>* \<Longrightarrow> \<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>* \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*\<rbrakk> \<Longrightarrow> commute r\<^sub>1 r\<^sub>2"
unfolding commute_def by auto (metis converse_converse relcomp.simps rtrancl_converseD)

lemma commuteE:
  assumes "commute r\<^sub>1 r\<^sub>2"
    and "(x, y) \<in> r\<^sub>1\<^sup>*"
    and "(x, z) \<in> r\<^sub>2\<^sup>*"
  shows "\<exists>u. (z, u) \<in> r\<^sub>1\<^sup>* \<and> (y, u) \<in> r\<^sub>2\<^sup>*"
proof -
  from assms have "(y, z) \<in> (r\<^sub>1\<inverse>)\<^sup>* O r\<^sub>2\<^sup>*" using rtrancl_converseI by fast
  with assms have "(y, z) \<in>  r\<^sub>2\<^sup>* O (r\<^sub>1\<inverse>)\<^sup>*" unfolding commute_def  by auto
  then show ?thesis by (metis converseD relcomp.cases rtrancl_converse)
qed

definition semi_commute  :: "'a rel \<Rightarrow> 'a rel  \<Rightarrow> bool"
where
  "semi_commute r\<^sub>1 r\<^sub>2 \<longleftrightarrow>
    (\<forall>x y\<^sub>1 y\<^sub>2. (x, y\<^sub>1) \<in> r\<^sub>1 \<and> (x, y\<^sub>2) \<in> r\<^sub>2\<^sup>* \<longrightarrow> (\<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>* \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*))"

lemma semi_commute_iff_commute:
  "semi_commute r\<^sub>1 r\<^sub>2 \<longleftrightarrow> commute r\<^sub>1 r\<^sub>2"
proof
  assume "commute r\<^sub>1 r\<^sub>2"
  then show "semi_commute r\<^sub>1 r\<^sub>2"
  unfolding semi_commute_def by (auto dest: commuteE)
next
  assume *:"semi_commute r\<^sub>1 r\<^sub>2"
  show "commute r\<^sub>1 r\<^sub>2"
  proof
    fix x y\<^sub>1 y\<^sub>2
    assume "(x, y\<^sub>1) \<in> r\<^sub>1\<^sup>*" and 2:"(x, y\<^sub>2) \<in> r\<^sub>2\<^sup>*"
    then obtain n where "(x, y\<^sub>1) \<in> r\<^sub>1^^n" by auto
    then show "\<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>* \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*"
    proof (induct n arbitrary: y\<^sub>1)
      case 0 then show ?case using 2 by auto
    next
      case (Suc n)
      then obtain y\<^sub>n where "(x, y\<^sub>n) \<in> r\<^sub>1 ^^ n" and 1:"(y\<^sub>n, y\<^sub>1) \<in> r\<^sub>1" by auto
      with Suc obtain z where "(y\<^sub>n, z) \<in> r\<^sub>2\<^sup>* \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*" by auto
      with 1 2 * show ?case unfolding semi_commute_def using rtrancl_trans by metis
    qed
  qed
qed

lemma strongly_commute_E1n:
  assumes "strongly_commute r\<^sub>1 r\<^sub>2"
  shows "(x, y) \<in> r\<^sub>2\<^sup>= \<Longrightarrow> (x, z) \<in> r\<^sub>1 ^^ n \<Longrightarrow> \<exists>u. (y, u) \<in> r\<^sub>1\<^sup>* \<and> (z, u) \<in> r\<^sub>2\<^sup>="
proof (induct n arbitrary: x y z)
  case (Suc m)
  from Suc(3) obtain w where xw: "(x, w) \<in> r\<^sub>1^^m" and wz: "(w, z) \<in> r\<^sub>1" by auto
  from Suc(1) [OF Suc(2) xw] obtain u where yu: "(y, u) \<in> r\<^sub>1\<^sup>*" and wu: "(w, u) \<in> r\<^sub>2\<^sup>=" by auto
  then have "w = u \<or> (w, u) \<in> r\<^sub>2" by auto
  then show ?case
  proof
    assume "w = u"
    with yu wz have "(y, z) \<in> r\<^sub>1\<^sup>*" by auto
    then show ?thesis by blast
  next
    assume "(w, u) \<in> r\<^sub>2"
    from strongly_commute_E11 [OF assms wz this] yu show ?thesis using rtrancl_trans by metis
  qed
qed auto

lemma strongly_commute_imp_commute:
  assumes "strongly_commute r\<^sub>1 r\<^sub>2"
  shows "commute r\<^sub>1 r\<^sub>2"
proof -
  have "semi_commute r\<^sub>1 r\<^sub>2" unfolding semi_commute_def
  proof (intro allI impI)
    fix x y\<^sub>1 y\<^sub>2
    assume *:"(x, y\<^sub>1) \<in> r\<^sub>1 \<and> (x, y\<^sub>2) \<in> r\<^sub>2\<^sup>*"
    then obtain n where "(x, y\<^sub>2) \<in> r\<^sub>2 ^^ n" and "(x, y\<^sub>1) \<in> r\<^sub>1" by auto
    then show "\<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>* \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*"
    proof (induct n arbitrary: y\<^sub>2)
      case (Suc n)
      then obtain y where "(x, y) \<in> r\<^sub>2 ^^ n" and "(y, y\<^sub>2) \<in> r\<^sub>2" by auto
      from Suc(1)[OF this(1) Suc(3)] obtain z where yz:"(y\<^sub>1, z) \<in> r\<^sub>2\<^sup>*" "(y, z) \<in> r\<^sub>1\<^sup>* " by auto
      from \<open>(y, y\<^sub>2) \<in> r\<^sub>2\<close> have "(y, y\<^sub>2) \<in> r\<^sub>2\<^sup>=" by auto
      from strongly_commute_E1n[OF assms this] yz obtain u where "(y\<^sub>2, u) \<in> r\<^sub>1\<^sup>* \<and> (z, u) \<in> r\<^sub>2\<^sup>="
        by blast
      moreover with yz have "(y\<^sub>1, u) \<in> r\<^sub>2\<^sup>*" by auto
      ultimately show ?case by auto
    qed auto
  qed
  with semi_commute_iff_commute show ?thesis ..
qed

lemma comm_imp_commute:
  assumes "comm r s"
  shows "commute r s"
by (metis assms commE comm_rtrancl comm_swap commuteI)

lemma commute_between_imp_commute:
  assumes "commute s\<^sub>1 s\<^sub>2" and "r\<^sub>1 \<subseteq> s\<^sub>1" and "s\<^sub>1 \<subseteq> r\<^sub>1\<^sup>*" and "r\<^sub>2 \<subseteq> s\<^sub>2" and "s\<^sub>2 \<subseteq> r\<^sub>2\<^sup>*"
  shows "commute r\<^sub>1 r\<^sub>2"
proof
  fix x y\<^sub>1 y\<^sub>2
  assume "(x, y\<^sub>1) \<in> r\<^sub>1\<^sup>*" and "(x, y\<^sub>2) \<in> r\<^sub>2\<^sup>*"
  then have "(x, y\<^sub>1) \<in> s\<^sub>1\<^sup>*" and "(x, y\<^sub>2) \<in> s\<^sub>2\<^sup>*"
    using assms rtrancl_subset by blast+
  then obtain v where "(y\<^sub>1, v) \<in> s\<^sub>2\<^sup>*" and "(y\<^sub>2, v) \<in> s\<^sub>1\<^sup>*"
    using assms(1) by (auto dest : commuteE)
  then show "\<exists>z. (y\<^sub>1, z) \<in> r\<^sub>2\<^sup>* \<and> (y\<^sub>2, z) \<in> r\<^sub>1\<^sup>*"
    using assms rtrancl_subset by blast
qed

lemma comm_between_imp_commute:
  assumes "comm s\<^sub>1 s\<^sub>2" and "r\<^sub>1 \<subseteq> s\<^sub>1" and "s\<^sub>1 \<subseteq> r\<^sub>1\<^sup>*" and "r\<^sub>2 \<subseteq> s\<^sub>2" and "s\<^sub>2 \<subseteq> r\<^sub>2\<^sup>*"
  shows "commute r\<^sub>1 r\<^sub>2"
using commute_between_imp_commute comm_imp_commute assms by blast

lemma CR_between_imp_CR:
  assumes "CR s" and "r \<subseteq> s" and "s \<subseteq> r\<^sup>*" shows "CR r"
using commute_between_imp_commute CR_iff_self_commute assms by blast

lemma Newman_commute:
  assumes sn: "SN (R \<union> S)" and lc: "locally_commute R S"
  shows "commute R S"
proof -
  let ?R = "\<lambda>s. {(s,t) |t. (s,t) \<in> R}"
  let ?S = "\<lambda>s. {(s,t) |t. (s,t) \<in> S}"
  let ?r = "((R \<union> S)\<inverse>)\<^sup>+"
  have R: "(\<Union>i. ?R i) = R" and S: "(\<Union>i. ?S i) = S" by auto
  show ?thesis
  proof (intro dd_commute[of "?r" ?R ?S, unfolded R S], goal_cases)
    case (3 a b s t u)
    have [simp]: "a = s" "b = s" using 3 by auto
    have "(s, t) \<in> R" "(s, u) \<in> S" and c: "(t, s) \<in> ?r" "(u, s) \<in> ?r" using 3 by auto
    then obtain v where v: "(t, v) \<in> S\<^sup>*" "(u, v) \<in> R\<^sup>*" using lc
      by (auto simp: peak_iff rtrancl_converse dest: locally_commute_E11)
    have "(t, v) \<in> conversion'' ?R ?S (under ?r s)" using v(1) c(1)
    proof (induct rule: converse_rtrancl_induct)
      case (step y z)
      have "(z, s) \<in> ((R \<union> S)\<inverse>)\<^sup>+" using step(1,4)
        by (intro trancl_into_trancl2[of z y]) auto
      moreover have "(y, z) \<in> conversion'' ?R ?S (under ?r s)"
        using step(1,4) by (auto simp: under_def)
      ultimately show ?case using step by auto
    qed auto
    moreover have "(v, u) \<in> conversion'' ?R ?S (under ?r s)" using v(2) c(2)
    proof (induct rule: converse_rtrancl_induct)
      case (step y z)
      have "(z, s) \<in> ((R \<union> S)\<inverse>)\<^sup>+" using step(1,4)
        by (intro trancl_into_trancl2[of z y]) auto
      moreover have "(z, y) \<in> conversion'' ?R ?S (under ?r s)"
        using step(1,4) by (auto simp: under_def)
      ultimately show ?case using step by auto
    qed auto
    ultimately show ?case
      by (intro relcompI[OF _ relcompI[OF _ relcompI[OF _ relcompI]], of t v _ v _ v _ v _ u]) auto
  qed (insert sn, auto intro: wf_trancl simp: SN_iff_wf)
qed

end
