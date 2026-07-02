(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Peak Decreasingness\<close>

theory Peak_Decreasingness
  imports
    "Abstract-Rewriting.Abstract_Rewriting"
    Well_Quasi_Orders.Multiset_Extension
    Auxx.Util
begin

lemma SN_mulex: "SN {(x, y). P x y} \<Longrightarrow> SN {(x, y). mulex P\<inverse>\<inverse> y x}"
  using wfp_on_mulex_on_multisets [of "P\<inverse>\<inverse>" UNIV]
  by (auto simp: wfp_def SN_iff_wf converse_def)

text \<open>ARSs whose relation is the union of an indexed set of relations.\<close>
locale ars_labeled =
  fixes r :: "'a \<Rightarrow> 'b rel"
    and I :: "'a set"
begin

abbreviation "R \<equiv> (\<Union>a\<in>I. r a)"

inductive conv where
  empty [simp, intro!]: "conv {#} x x" |
  step [intro]: "a \<in> I \<Longrightarrow> (x, y) \<in> (r a)\<^sup>\<leftrightarrow> \<Longrightarrow> conv M y z \<Longrightarrow> conv (add_mset a M) x z"

lemma conv_in_I [simp, dest]:
  "conv M x y \<Longrightarrow> set_mset M \<subseteq> I"
by (induct rule: conv.induct) simp_all

lemma conversion_conv_iff:
  assumes "A \<subseteq> I"
  shows "(x, y) \<in> (\<Union>a\<in>A. r a)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> (\<exists>M. set_mset M \<subseteq> A \<and> conv M x y)"
    (is "_ \<in> ?R\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> _")
proof
  assume "(x, y) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
  then have "(x, y) \<in> (?R \<union> ?R\<inverse>)\<^sup>*" by auto
  then show "\<exists>M. set_mset M \<subseteq> A \<and> conv M x y"
  proof (induct rule: converse_rtrancl_induct)
    case (step w x)
    moreover then obtain a and M where "a \<in> A" and "(w, x) \<in> (r a)\<^sup>\<leftrightarrow>"
      and "set_mset M \<subseteq> A" and "conv M x y" by blast
    ultimately show ?case using assms by (intro exI [of _ "M + {#a#}"]) auto
  qed (auto intro: exI [of _ "{#}"])
next
  assume "\<exists>M. set_mset M \<subseteq> A \<and> conv M x y"
  then obtain M where "conv M x y" and "set_mset M \<subseteq> A" by auto
  then show "(x, y) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
    by (induct) (auto simp: conversion_def intro: converse_rtrancl_into_rtrancl)
qed

lemma conversion_R_conv_iff: "(x, y) \<in> R\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> (\<exists>M. set_mset M \<subseteq> I \<and> conv M x y)"
  using conversion_conv_iff[OF subset_refl] .

lemma conv_singleton [intro]:
  "a \<in> I \<Longrightarrow> (x, y) \<in> (r a)\<^sup>\<leftrightarrow> \<Longrightarrow> conv {#a#} x y"
by (metis conv.empty conv.step empty_neutral(1))

lemma conv_step' [intro, simp]:
  assumes "a \<in> I" and "(y, z) \<in> (r a)\<^sup>\<leftrightarrow>" and "conv M x y"
  shows "conv (add_mset a M) x z"
  using assms (3, 2, 1) by (induct) (auto simp: add_mset_commute)

lemma conv_trans:
  assumes "conv M x y" and "conv N y z"
  shows "conv (M + N) x z"
  using assms(2, 1)
  apply (induct arbitrary: M)
   apply (auto simp: ac_simps)
  apply (metis UnCI conv_step' union_mset_add_mset_right)
  by (metis UnCI conv_step' converse_iff union_mset_add_mset_right)

lemma conv_commute:
  assumes "conv M x y" shows "conv M y x"
  using assms by (induct) auto

inductive seql where
  empty [simp, intro!]: "seql {#} x x" |
  step [intro]: "a \<in> I \<Longrightarrow> (z, y) \<in> r a \<Longrightarrow> seql M x y \<Longrightarrow> seql (add_mset a M) x z"

lemma rtrancl_seql_iff:
  "(x, y) \<in> R\<^sup>* \<longleftrightarrow> (\<exists>M. seql M y x)"
proof
  assume "(x, y) \<in> R\<^sup>*"
  then show "\<exists>M. seql M y x"
    by (induct rule: converse_rtrancl_induct) (auto)
next
  assume "\<exists>M. seql M y x"
  then obtain M where "seql M y x" ..
  then show "(x, y) \<in> R\<^sup>*"
    by (induct) (auto simp: rtrancl_converse intro: converse_rtrancl_into_rtrancl)
qed

lemma seql_singleton [intro]:
  "a \<in> I \<Longrightarrow> (x, y) \<in> r a \<Longrightarrow> seql {#a#} y x"
  by (metis empty_neutral(1) seql.empty seql.step)

lemma seql_imp_conv:
  assumes "seql M x y" shows "conv M x y"
  using assms by (induct) auto

lemma seql_add_mset [simp]:
  "a \<in> I \<Longrightarrow> (z, y) \<in> r a \<Longrightarrow> seql M x y \<Longrightarrow> seql (add_mset a M) x z"
  by auto

lemma seql_left' [intro]:
  assumes "a \<in> I" and "(y, x) \<in> r a" and "seql M y z"
  shows "seql (add_mset a M) x z"
  using assms(3, 2, 1) by (induct) (auto simp: add_mset_commute)

inductive valley where
  seql [simp, intro]: "seql M x y \<Longrightarrow> valley M x y" |
  left [intro]: "\<lbrakk>a \<in> I; (x, y) \<in> r a; valley M y z\<rbrakk> \<Longrightarrow> valley (add_mset a M) x z"

lemma join_valley_iff:
  "(x, y) \<in> R\<^sup>\<down> \<longleftrightarrow> (\<exists>M. valley M x y)"
proof
  assume "(x, y) \<in> R\<^sup>\<down>"
  then obtain z where "(x, z) \<in> R\<^sup>*" and "(y, z) \<in> R\<^sup>*" by auto
  then obtain N where "(x, z) \<in> R\<^sup>*" and "seql N z y" by (auto simp: rtrancl_seql_iff)
  then show "\<exists>M. valley M x y"
    by (induct arbitrary: y rule: converse_rtrancl_induct)
       (auto dest: valley.left)
next
  assume "\<exists>M. valley M x y"
  then obtain M where "valley M x y" by auto
  then show "(x, y) \<in> R\<^sup>\<down>"
    by (induct) (auto iff: rtrancl_seql_iff intro: rtrancl_join_join)
qed

lemma valley_imp_conv:
  assumes "valley M x y" shows "conv M x y"
  using assms by (induct) (auto intro: seql_imp_conv)

text \<open>A conversion is either a valley or contains a peak.\<close>
lemma conv_valley_peak_cases:
  assumes "conv M x y"
  obtains
    (valley) "valley M x y" |
    (peak) K L a b t u v
    where "M = K + L + {#a, b#}"
      and "conv K x t"
      and "a \<in> I" and "(u, t) \<in> r a"
      and "b \<in> I" and "(u, v) \<in> r b"
      and "conv L v y"
using assms
proof (induct)
  case (empty x) then show ?case by auto
next
  case (step a x y M z)
  show ?case
  proof (rule step.hyps)
    assume *: "valley M y z"
    from \<open>(x, y) \<in> (r a)\<^sup>\<leftrightarrow>\<close> show ?thesis
    proof
      assume "(x, y) \<in> r a"
      with * and \<open>a \<in> I\<close> have "valley (add_mset a M) x z" by auto
      then show ?thesis by fact
    next
      assume "(x, y) \<in> (r a)\<inverse>"
      then have "(y, x) \<in> r a" by simp
      from * show ?thesis
      proof (cases)
        assume "seql M y z"
        then have "valley (add_mset a M) x z" using step by blast
        then show ?thesis by fact
      next
        fix b u N
        assume "b \<in> I" and "(y, u) \<in> r b"
          and [simp]: "M = add_mset b N"
          and "valley N u z"
        then have *: "M - {#b#} = N" by simp
        have "add_mset a M = {#} + (M - {#b#}) + {#a, b#}" by (simp add: ac_simps)
        moreover have "conv {#} x x" by blast
        moreover have "a \<in> I" and "(y, x) \<in> r a" by fact+
        moreover have "b \<in> I" and "(y, u) \<in> r b" by fact+
        moreover have "conv (M - {#b#}) u z"
          unfolding * by (rule valley_imp_conv) fact
        ultimately show ?thesis by fact
      qed
    qed
  next
    fix K L b c t u v
    assume [simp]: "M = K + L + {#b, c#}"
      and "conv K y t" and "b \<in> I" and "(u, t) \<in> r b"
      and "c \<in> I" and "(u, v) \<in> r c" and "conv L v z"
    moreover with step have "conv (add_mset a K) x t" by blast
    moreover have "add_mset a M = add_mset a K + L + {#b, c#}" by (auto simp: ac_simps)
    show ?thesis by (rule step.prems) fact+
  qed
qed

end

text \<open>ARSs as unions of relations over an index set equipped with a well-founded order.\<close>
locale ars_labeled_sn = ars_labeled +
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50)
  assumes SN_less: "SN {(x, y). x \<succ> y}"
begin

abbreviation label_less_set ("{\<succ>}")
where
  "{\<succ>} \<equiv> {(x, y). x \<succ> y}"

definition mless :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" (infix "\<succ>\<^sub>M" 50) where
  "x \<succ>\<^sub>M y \<longleftrightarrow> mulex (\<succ>)\<inverse>\<inverse> y x"

abbreviation mlesseq (infix "\<succeq>\<^sub>M" 50) where
  "x \<succeq>\<^sub>M y \<equiv> mless\<^sup>=\<^sup>= x y"

lemma SN_mless: "SN {(x, y). x \<succ>\<^sub>M y}"
  using SN_mulex [OF SN_less] by (auto simp: SN_defs mless_def)

lemma mless_mono:
  "M \<succ>\<^sub>M N \<Longrightarrow> K + M \<succ>\<^sub>M K + N"
  unfolding mless_def by (metis UNIV_I mulex_on_union multisets_UNIV)

lemma mless_trans:
  "as \<succ>\<^sub>M bs \<Longrightarrow> bs \<succ>\<^sub>M cs \<Longrightarrow> as \<succ>\<^sub>M cs"
  unfolding mless_def by (metis mulex_on_trans)

lemma mless_empty [simp]:
  "M \<noteq> {#} \<Longrightarrow>  M \<succ>\<^sub>M {#}"
  by (auto simp: mless_def)

lemma mless_all_strict:
  "M \<noteq> {#} \<Longrightarrow> \<forall>y. y \<in># N \<longrightarrow> (\<exists>x. x \<in># M \<and> x \<succ> y) \<Longrightarrow> M \<succ>\<^sub>M N"
  using mulex_on_all_strict [of M UNIV N "(\<succ>)\<inverse>\<inverse>"] by (simp add: mless_def)

abbreviation downset1 :: "'a \<Rightarrow> 'a set" ("'(_')\<succ>")
where
  "(a)\<succ> \<equiv> {b \<in> I. a \<succ> b}"

abbreviation downset2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" ("\<or>'(_,/ _')")
where
  "\<or>(a, b) \<equiv> {c \<in> I. a \<succ> c \<or> b \<succ> c}"

lemma downset2_multiset:
  assumes "\<forall>c. c \<in># M \<longrightarrow> a \<succ> c \<or> b \<succ> c"
  shows "{#a, b#} \<succ>\<^sub>M M"
  using assms
  by (metis add_mset_add_single add_mset_commute add_mset_not_empty ars_labeled_sn.mless_all_strict ars_labeled_sn_axioms multi_member_this)

lemma Union_downset2_trans:
  "(s, t) \<in> (\<Union>c\<in>\<or>(a, b). (r c))\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow>
   (t, u) \<in> (\<Union>c\<in>\<or>(a, b). (r c))\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow>
   (s, u) \<in> (\<Union>c\<in>\<or>(a, b). (r c))\<^sup>\<leftrightarrow>\<^sup>*"
  by (auto simp: conversion_def)

lemma sym_step_in_downset2:
  assumes "(s, t) \<in> (r c)\<^sup>\<leftrightarrow>" and "c \<in> I" and "a \<succ> c \<or> b \<succ> c"
  shows "(s, t) \<in> (\<Union>c\<in>\<or>(a, b). r c)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms by (auto)

lemma sym_steps_in_downset2:
  assumes "(s, t) \<in> ((r c)\<^sup>\<leftrightarrow>)\<^sup>*" and "c \<in> I" and "a \<succ> c \<or> b \<succ> c"
  shows "(s, t) \<in> (\<Union>c\<in>\<or>(a, b). r c)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
  by (induct s t, simp) (metis (mono_tags) Union_downset2_trans sym_step_in_downset2)

lemma conversion_in_downset2:
  assumes "(s, t) \<in> (r c)\<^sup>\<leftrightarrow>\<^sup>*" and "c \<in> I" and "a \<succ> c \<or> b \<succ> c"
  shows "(s, t) \<in> (\<Union>c\<in>\<or>(a, b). r c)\<^sup>\<leftrightarrow>\<^sup>*"
  using sym_steps_in_downset2 [OF assms [unfolded conversion_def]] .

lemma downset2_conversion_imp_conv:
  assumes "(t, u) \<in> (\<Union>c\<in>\<or>(a, b). r c)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<exists>M. {#a, b#} \<succ>\<^sub>M M \<and> conv M t u"
proof -
  from assms [unfolded conversion_def]
    have "\<exists>M. (\<forall>c. c \<in># M \<longrightarrow> a \<succ> c \<or> b \<succ> c) \<and> conv M t u"
  proof (induct)
    case base
    show ?case
      by (metis add_mset_not_empty ars_labeled.conv.empty mset_add)
  next
    case (step u v)
    then obtain M where *: "\<forall>c. c \<in># M \<longrightarrow> a \<succ> c \<or> b \<succ> c" and "conv M t u" by blast
    from step(2) obtain c where "c \<in> I" and "a \<succ> c \<or> b \<succ> c"
      and "(u, v) \<in> (r c)\<^sup>\<leftrightarrow>" by auto
    with \<open>conv M t u\<close> have "conv (add_mset c M) t v" by (metis conv_step')
    moreover have "\<forall>d. d \<in># add_mset c M \<longrightarrow> a \<succ> d \<or> b \<succ> d"
      using * and \<open>a \<succ> c \<or> b \<succ> c\<close> by (auto)
    ultimately show ?case by blast
  qed
  with downset2_multiset [of _ a b]
    show ?thesis by blast
qed
end


locale ars_labelled_partially_sn = ars_labeled_sn +
  fixes B :: "'a set"
  assumes B_subset_I:"B \<subseteq> I"
begin


abbreviation downsetB :: "'a \<Rightarrow> 'a set" ("B\<succ>'(_')")
where
  "B\<succ>(a) \<equiv> B \<union> {b \<in> I. a \<succ> b}"

lemma aux:
  assumes "\<And>a x y. a \<in> A \<Longrightarrow> (x, y) \<in> r a \<Longrightarrow> (\<exists>M. set_mset M \<subseteq> J \<and> conv M x y)"
  shows "set_mset M \<subseteq> A \<and> conv M x y \<Longrightarrow> (\<exists>M. set_mset M \<subseteq> J \<and> conv M x y)"
proof-
  assume conv:"set_mset M \<subseteq> A \<and> conv M x y"
  let ?A = "\<Union>a\<in>set_mset M. r a"
  from conv conversion_conv_iff[of "set_mset M"] have "(x, y) \<in> ?A\<^sup>\<leftrightarrow>\<^sup>*" by auto
  then obtain n where "(x, y) \<in> ?A\<^sup>\<leftrightarrow> ^^ n" by fast
  then show "\<exists>M. set_mset M \<subseteq> J \<and> conv M x y" proof(induct n arbitrary:x)
    case 0
    then have "x=y" unfolding relpow.simps(1) by auto
    then show ?case by (intro exI[of _ "{#}"]) auto
  next
    case (Suc n)
    from relpow_Suc_D2[OF Suc(2)] obtain z where z:"(x,z) \<in> ?A\<^sup>\<leftrightarrow>" "(z,y) \<in> ?A\<^sup>\<leftrightarrow> ^^ n" by blast
    from symcl_Un have "?A\<^sup>\<leftrightarrow> = (\<Union>a\<in>set_mset M. (r a)\<^sup>\<leftrightarrow>)" by blast
    from z(1)[unfolded this UN_iff] obtain c where c:"(x, z) \<in> (r c)\<^sup>\<leftrightarrow>" "c \<in> set_mset M" by blast
    from c(1) have xz:"(x, z) \<in> r c \<or> (z, x) \<in> r c" by auto
    from conv c(2) assms have step:"\<And>x y.(x, y) \<in> r c \<Longrightarrow> \<exists>M. set_mset M \<subseteq> J \<and> conv M x y" by blast
    from xz step[of x z] step[of z x] conv_commute
     obtain N1 where N1:"set_mset N1 \<subseteq> J" "conv N1 x z" by meson
    from Suc(1)[OF z(2)] obtain N2 where N2:"set_mset N2 \<subseteq> J" "conv N2 z y" by auto
    from N1(1) N2(1) have subset:"set_mset (N1 + N2) \<subseteq> J" unfolding set_mset_union by simp
    from N1(2) N2(2) have "conv (N1 + N2) x y" using conv_trans by simp
    with subset show ?case using conv_trans set_mset_union by blast
  qed
qed

lemma conv_eq:
  assumes "\<And>a x y. (x, y) \<in> r a \<Longrightarrow> (\<exists>M. set_mset M \<subseteq> B\<succ>(a) \<and> conv M x y)"
  shows "set_mset M \<subseteq> I \<and> conv M x y \<Longrightarrow> (\<exists>M. set_mset M \<subseteq> B \<and> conv M x y)"
proof-
  assume conv:"set_mset M \<subseteq> I \<and> conv M x y"
  { fix b x y
    have "(x, y) \<in> r b \<Longrightarrow> (\<exists>M. set_mset M \<subseteq> B \<and> conv M x y)"
    proof (induct arbitrary: x y rule:SN_induct[OF SN_less])
      case (1 a)
      from assms[OF 1(2)] obtain M where M:"set_mset M \<subseteq> B \<union> (a)\<succ> \<and> conv M x y" by auto
      from B_subset_I have "B \<union> (a)\<succ> \<subseteq> I" by blast
      from M conversion_conv_iff[OF this] have "(x, y) \<in> (\<Union>a \<in> B \<union> (a)\<succ>. r a)\<^sup>\<leftrightarrow>\<^sup>*" by auto
      { fix c x y
        assume c:"c \<in> B \<union> (a)\<succ>" and rc:"(x, y) \<in> r c"
        have "\<exists>M. set_mset M \<subseteq> B \<and> conv M x y" proof (cases "c \<in> B")
          case True
          with c rc B_subset_I conv_singleton show ?thesis by (intro exI[of _ "{#c#}"]) auto
        next
          case False
          with c have "a \<succ> c" by auto
          from rc have xz:"(x, y) \<in> r c \<or> (y, x) \<in> r c" by auto
          from 1(1)[of c] \<open>a \<succ> c\<close> have
            ih:"\<And>x y. (x, y) \<in> r c \<Longrightarrow> \<exists>M. set_mset M \<subseteq> B \<and> conv M x y" by auto
          from ih[of x y] ih[of y x] xz conv_commute show ?thesis by blast
        qed
      }
      with aux[OF _ M, of B] show ?case by argo
    qed
  } note step = this
  let ?A = "\<Union>a\<in>set_mset M. r a"
  from aux[OF _ conv] step show "\<exists>M. set_mset M \<subseteq> B \<and> conv M x y" by force
 qed
end


locale ars_peak_decreasing = ars_labeled_sn +
  assumes peak_decreasing:
    "\<lbrakk>a \<in> I; b \<in> I; (x, y) \<in> r a; (x, z) \<in> r b\<rbrakk> \<Longrightarrow> (y, z) \<in> (\<Union>c\<in>\<or>(a, b). r c)\<^sup>\<leftrightarrow>\<^sup>*"
begin

lemma conv_join_mless_convD:
  assumes "conv M x y"
  shows "valley M x y \<or> (\<exists>N. M \<succ>\<^sub>M N \<and> conv N x y)"
using assms
proof (cases rule: conv_valley_peak_cases)
  case (peak K L a b t u v)
  with peak_decreasing
    have "(t, v) \<in> (\<Union>c\<in>\<or>(a, b). r c)\<^sup>\<leftrightarrow>\<^sup>*" by blast
  from downset2_conversion_imp_conv [OF this] obtain N
    where "{#a, b#} \<succ>\<^sub>M N" and "conv N t v" by blast
  then have "M \<succ>\<^sub>M K + L + N"
    unfolding peak by (intro mless_mono) auto
  then have "M \<succ>\<^sub>M K + N + L" by (auto simp: ac_simps)
  moreover have "conv (K + N + L) x y"
    using peak and \<open>conv N t v\<close> by (blast intro: conv_trans)
  ultimately show ?thesis by blast
qed simp

text \<open>A conversion is either a valley or can be made smaller w.r.t.\ @{const mless}.\<close>
lemma conv_join_mless_conv_cases:
  assumes "conv M x y"
  obtains
    (valley) "valley M x y" |
    (conv) N
    where "M \<succ>\<^sub>M N" and "conv N x y"
  using conv_join_mless_convD [OF assms] by blast

lemma conv_imp_valley:
  assumes "conv M x y"
  shows "\<exists>N. M \<succeq>\<^sub>M N \<and> valley N x y"
using SN_mless and assms
proof (induct)
  case (IH M)
  from \<open>conv M x y\<close> show ?case
  proof (cases rule: conv_join_mless_conv_cases)
    case valley then show ?thesis by auto
  next
    case (conv N)
    with IH(1) [of N] show ?thesis by (auto elim: mless_trans)
  qed
qed

text \<open>Every peak decreasing ARS is confluent.\<close>
lemma CR: "CR R"
proof
  fix x y z
  assume "x \<in> UNIV" and "(x, y) \<in> R\<^sup>*" and "(x, z) \<in> R\<^sup>*"
  then have "(y, z) \<in> R\<^sup>\<leftrightarrow>\<^sup>*" by (metis in_mono meetI meet_imp_conversion)
  then obtain M where "conv M y z" by (auto simp: conversion_conv_iff)
  from conv_imp_valley [OF this]
    show "(y, z) \<in> R\<^sup>\<down>" by (auto iff: join_valley_iff)
qed

end

context ars_labeled_sn
begin

lemma mset_replicate_Suc:
  "(\<forall>x. x \<in># mset (replicate (Suc n) y) \<longrightarrow> P x) \<longleftrightarrow> P y"
  by (induct n) auto

lemma same_label_conversion_imp_conv:
  assumes "(t, u) \<in> (r c)\<^sup>\<leftrightarrow>\<^sup>*" and "c \<in> I" and "a \<succ> c \<or> b \<succ> c"
  shows "\<exists>M. {#a, b#} \<succ>\<^sub>M M \<and> conv M t u"
proof -
  let ?M = "\<lambda>n. mset (replicate n c)"

  have "\<And>n. \<forall>y. y \<in># ?M (Suc n) \<longrightarrow> (\<exists>x. x \<in># {#a, b#} \<and> x \<succ> y)"
    unfolding mset_replicate_Suc using \<open>a \<succ> c \<or> b \<succ> c\<close> by auto
  from mulex_on_all_strict [OF _ _ _ this, of UNIV]
    have mless: "\<And>n. {#a, b#} \<succ>\<^sub>M ?M (Suc n)"
    by (auto simp: mless_def intro: mulex_on_mono)

  from assms(1) have "(t, u) \<in> (r c \<union> (r c)\<inverse>)\<^sup>*" by auto
  then have "\<exists>n. {#a, b#} \<succ>\<^sub>M ?M n \<and> conv (?M n) t u"
  proof (induct)
    case base
    have "{#a, b#} \<succ>\<^sub>M ?M 0" by (simp add: mless_def)
    moreover have "conv (?M 0) t t" by simp
    ultimately show ?case by blast
  next
    case (step y z)
    then obtain n where "conv (?M n) t y" by blast
    moreover from \<open>(y, z) \<in> r c \<union> (r c)\<inverse>\<close> and \<open>c \<in> I\<close>
      have "conv {#c#} y z" by (auto)
    ultimately have "conv (?M n + {#c#}) t z" by (rule conv_trans)
    then have "conv (?M (Suc n)) t z" by simp
    with mless show ?case by blast
  qed
  then show ?thesis by blast
qed

lemma ars_peak_decreasing_alt_intro:
  assumes *: "\<And>a b x y z.
    \<lbrakk>a \<in> I; b \<in> I; (x, y) \<in> r a; (x, z) \<in> r b\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> \<or>(a, b) \<and> (y, z) \<in> (r c)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "ars_peak_decreasing r I less"
proof (unfold_locales)
  fix a b x y z
  assume "a \<in> I" and "b \<in> I" and "(x, y) \<in> r a" and "(x, z) \<in> r b"
  from * [OF this] obtain c
    where "(y, z) \<in> (r c)\<^sup>\<leftrightarrow>\<^sup>*" and "c \<in> I" and "a \<succ> c \<or> b \<succ> c" by blast
  from conversion_in_downset2 [OF this]
    show "(y, z) \<in> (\<Union>c\<in>\<or>(a, b). r c)\<^sup>\<leftrightarrow>\<^sup>*" .
qed

end

text \<open>Partitioning of a relation that labels steps by their source.\<close>
definition source_step :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a rel"
where
  "source_step R x = {(x, y) | y. (x, y) \<in> R}"

lemma source_step_label [iff]:
  "(x, y) \<in> source_step R z \<longleftrightarrow> (x, y) \<in> R \<and> z = x"
by (auto simp: source_step_def)

lemma UN_source_step: "(\<Union>x. source_step R x) = R"
by auto

locale ars_source_decreasing =
  ars_labeled_sn "source_step R" I for R I +
  assumes source_decreasing: "\<And>a b c. a \<in> I \<Longrightarrow> (a, b) \<in> source_step R a \<Longrightarrow> (a, c) \<in> source_step R a \<Longrightarrow>
    (b, c) \<in> (\<Union>b\<in>(a)\<succ>. source_step R b)\<^sup>\<leftrightarrow>\<^sup>*"

sublocale ars_source_decreasing \<subseteq> ars_peak_decreasing "source_step R"
proof
  fix a b x y z assume "a \<in> I" and "b \<in> I"
    and "(x, y) \<in> source_step R a" and "(x, z) \<in> source_step R b"
  with source_decreasing have "(\<Union>b\<in>(a)\<succ>. source_step R b) \<subseteq> (\<Union>c\<in>\<or>(a, b). source_step R c)"
    and "(y, z) \<in> (\<Union>b\<in>(a)\<succ>. source_step R b)\<^sup>\<leftrightarrow>\<^sup>*" by auto
  then show "(y, z) \<in> (\<Union>c\<in>\<or>(a, b). source_step R c)\<^sup>\<leftrightarrow>\<^sup>*" by (rule conversion_mono [THEN subsetD])
qed

locale ars_mod_labeled = r: ars_labeled r I + s: ars_labeled s J
  for r s :: "'a \<Rightarrow> 'b rel"
    and I J :: "'a set"
begin

inductive valley_mod where
  seql [simp, intro]: " s.conv N z y \<Longrightarrow> r.seql M y x \<Longrightarrow> valley_mod (N + M) z x" |
  left [intro]: "\<lbrakk>a \<in> I; (x, y) \<in> r a; valley_mod M y z\<rbrakk> \<Longrightarrow> valley_mod (add_mset a M) x z"

lemma[simp]: "valley_mod {#} x x"
  using valley_mod.seql[OF s.conv.empty r.seql.empty] by auto

abbreviation "R \<equiv> (\<Union>a\<in>I. r a)"
abbreviation "S \<equiv> (\<Union>a\<in>J. s a)"

lemma join_mod_valley_mod_iff:
  "(x, y) \<in> R\<^sup>* O S\<^sup>\<leftrightarrow>\<^sup>* O (R\<inverse>)\<^sup>* \<longleftrightarrow> (\<exists>M. valley_mod M x y)"
proof
  assume "(x, y) \<in> R\<^sup>* O S\<^sup>\<leftrightarrow>\<^sup>* O (R\<inverse>)\<^sup>*"
  then obtain z\<^sub>1 where z\<^sub>1:"(x, z\<^sub>1) \<in> R\<^sup>*" and "(z\<^sub>1, y) \<in> S\<^sup>\<leftrightarrow>\<^sup>* O ((R\<inverse>)\<^sup>*)" by auto
  from this(2) obtain z\<^sub>2 where z\<^sub>2:"(z\<^sub>1, z\<^sub>2) \<in> S\<^sup>\<leftrightarrow>\<^sup>*" and "(y, z\<^sub>2) \<in> R\<^sup>*"
    unfolding relcomp.simps using rtrancl_converseD by metis
  then obtain M N where MN:"s.conv M z\<^sub>1 z\<^sub>2" "r.seql N z\<^sub>2 y"
    unfolding r.rtrancl_seql_iff s.conversion_R_conv_iff by auto
  with z\<^sub>1 have "(x, z\<^sub>1) \<in> R\<^sup>*" "valley_mod (M + N) z\<^sub>1 y" using valley_mod.seql[OF MN]  by auto
  then show "\<exists>M. valley_mod M x y" by (induct arbitrary: z\<^sub>1 rule: converse_rtrancl_induct, auto)
next
  assume "\<exists>M. valley_mod M x y"
  then obtain M where M:"valley_mod M x y" by auto
  have *:"\<And>N z y. s.conv N z y \<Longrightarrow> (z, y) \<in> S\<^sup>\<leftrightarrow>\<^sup>*" using s.conversion_R_conv_iff by auto
  have **:"\<And>y M x. r.seql M y x \<Longrightarrow> (y, x) \<in> (R\<inverse>)\<^sup>*" using
    r.rtrancl_seql_iff rtrancl_converseI by metis
  from M show "(x, y) \<in> R\<^sup>* O S\<^sup>\<leftrightarrow>\<^sup>* O (R\<inverse>)\<^sup>*"
    by induct  (auto iff: r.rtrancl_seql_iff dest!:*, auto dest!:**)
qed

abbreviation sr where "sr \<equiv> (\<lambda>i. (if i \<in> I then r i else {}) \<union> (if i \<in> J then s i else {}))"

lemma RS_subset_sr: "R \<union> S \<subseteq> (\<Union>a\<in>I \<union> J. sr a)"
  by auto

lemma sr_cases:"(x, y) \<in> (sr a) \<Longrightarrow> ((x,y) \<in> r a \<and> a \<in> I) \<or> ((x,y) \<in> s a \<and> a \<in> J)"
  by (smt Un_iff empty_iff)

sublocale sr: ars_labeled sr "I \<union> J" by unfold_locales

lemma rconv: assumes "r.conv M x y" shows "sr.conv M x y"
  using assms by (induct, auto)

lemma sconv: assumes "s.conv M x y" shows "sr.conv M x y"
  using assms by (induct, auto)

lemma valley_imp_conv:
  assumes "valley_mod M x y"
  shows "sr.conv M x y" using assms
proof(induct)
  case (seql N z y M x)
  from rconv[OF r.seql_imp_conv[OF this(2)]] sconv[OF this(1)] sr.conv_trans sr.conv_commute
    show ?case by auto
next
  case (left a x y M z)
  from r.conv_singleton left have "r.conv {#a#} x y" by auto
  with rconv have "sr.conv {#a#} x y" by auto
  from sr.conv_trans[OF this left(4)] show ?case by auto
qed

definition mod_peak where "mod_peak t a u b v \<equiv>
  (a \<in> I \<and> b \<in> I \<and> (u, t) \<in> r a \<and> (u, v) \<in> r b) \<or>
  (a \<in> I \<and> b \<in> J \<and> (u, t) \<in> r a \<and> (u, v) \<in> (s b)\<^sup>\<leftrightarrow>) \<or>
  (a \<in> I \<and> b \<in> J \<and> (u, t) \<in> (s b)\<^sup>\<leftrightarrow> \<and> (u, v) \<in> r a)"

lemma conv_valley_mod_peak_cases:
  assumes "sr.conv M x y"
  obtains
    (valley) "valley_mod M x y" |
    (peak) K L a b t u v
    where "M = K + L + {#a, b#}"
      and "sr.conv K x t"
      and "mod_peak t a u b v"
      and "sr.conv L v y"
using assms
proof (induct)
  case (empty x) then show ?case by auto
next
  case (step a x y M z)
  let ?peak = "\<lambda> K L c b t u v.
    add_mset a M = K + L + {#c, b#} \<and> sr.conv K x t \<and> mod_peak t c u b v \<and> sr.conv L v z"
  have conv_seql[simp]:"\<And>M x y. r.seql M x y \<Longrightarrow> sr.conv M x y" using r.seql_imp_conv rconv by auto
  show ?case
  proof (rule step.hyps)
    assume *: "valley_mod M y z"
    from \<open>(x, y) \<in> (sr a)\<^sup>\<leftrightarrow>\<close> consider "(x, y) \<in> sr a" | "(y, x) \<in> sr a" by auto
    then show ?thesis
    proof(cases)
      case 1
      from sr_cases[OF 1] consider "(x, y) \<in> r a \<and> a \<in> I" | "(x, y) \<in> s a \<and> a \<in> J" by auto
      then show ?thesis proof(cases)
        case 1
        with * have "valley_mod (add_mset a M) x z" by auto
        then show ?thesis by fact
      next
        case 2
        from * show ?thesis proof(cases)
          case (seql N w M')
          from seql(2) s.conv.step[of a x y] 2 have "s.conv (add_mset a N) x w" by auto
          from valley_mod.seql[OF this] seql(3) have "valley_mod (add_mset a M) x z"
            unfolding seql(1) by auto
          then show ?thesis by fact
        next
          case (left b w M')
          from this(2) this(3) 2 have 1:"mod_peak x b y a w" unfolding mod_peak_def by auto
          from valley_imp_conv[OF left(4)] have 3:"sr.conv M' w z" by auto
          from left(1) have 4:"add_mset a M = M' + {#b, a#}" by auto
          from 4 1 3 have *:"?peak {#} M' b a x y w" by auto
          then show ?thesis using step.prems(2)[of "{#}" M' b a] by blast
        qed
      qed
    next
      case 2
      from sr_cases[OF 2] consider "(y, x) \<in> r a \<and> a \<in> I" | "(y, x) \<in> s a \<and> a \<in> J" by auto
      then show ?thesis proof(cases)
        case 1
        from * show ?thesis proof(cases)
          case (seql N y' M')
          from this(2) show ?thesis proof(cases)
            case empty
            from seql(3) 1 have "r.seql (add_mset a M') x z"
              using r.seql.step[of a y x] unfolding empty(2) by auto
            with valley_mod.seql have "valley_mod (add_mset a M) x z"
              unfolding seql empty by fastforce
            then show ?thesis by fact
          next
            case (step b w K)
            with 1 have 1:"mod_peak x a y b w" unfolding mod_peak_def by auto
            from step(1) seql(1) have 2:"add_mset a M = K + M' + {#a, b#}" by auto
            from sconv[OF step(4)] seql(3) sr.conv_trans have 3:"sr.conv (K + M') w z" by auto
            from 1 2 3 have *:"?peak {#} (K + M') a b x y w" by auto
            then show ?thesis using step.prems(2) by blast
          qed
        next
          case (left b w M')
          with 1 have 1:"mod_peak x a y b w" unfolding mod_peak_def by auto
          from valley_imp_conv[OF left(4)] have 3:"sr.conv M' w z" by auto
          from left(1) have 4:"add_mset a M = M' + {#a, b#}" by auto
          from 4 1 3 have *:"?peak {#} M' a b x y w" by auto
          then show ?thesis using step.prems(2) by blast
        qed
      next
        case 2
        from * show ?thesis proof(cases)
          case (seql N w M')
          with 2 have "s.conv (add_mset a N) x w" using s.conv.step by auto
          from valley_mod.seql[OF this] seql have "valley_mod (add_mset a M) x z" by auto
          then show ?thesis by fact
        next
          case (left b w M')
          with 2 have 1:"mod_peak x b y a w" unfolding mod_peak_def by auto
          from valley_imp_conv[OF left(4)] have 3:"sr.conv M' w z" by auto
          from left(1) have 4:"add_mset a M = M' + {#b, a#}" by auto
          from 4 1 3 have *:"?peak {#} M' b a x y w" by auto
          then show ?thesis using step.prems(2) by blast
        qed
      qed
    qed
  next
    fix K L b c t u v
    assume [simp]: "M = K + L + {#b, c#}"
      and "sr.conv K y t" and peak:"mod_peak t b u c v" "sr.conv L v z"
    with step have 1:"sr.conv (add_mset a K) x t" by blast
    have [simp]:"add_mset a M = add_mset a K + L + {#b, c#}" by (auto simp: ac_simps)
    show ?thesis by (rule step.prems) fact+
  qed
qed
end

definition CRm where
  "CRm A B \<longleftrightarrow> (A \<union> B)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (A\<^sup>* O B\<^sup>\<leftrightarrow>\<^sup>* O (A\<inverse>)\<^sup>*)"

locale ars_mod_labeled_sn = ars_mod_labeled r s I J
  for r s :: "'a \<Rightarrow> 'b rel"        
  and I J :: "'a set" +
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50)
  assumes SN_less: "SN {(x, y). x \<succ> y}"
begin

sublocale ars_labeled_sn sr "I \<union> J" less using SN_less by unfold_locales

context
  assumes peak_decreasing_mod: "mod_peak x a y b z \<Longrightarrow> (x, z) \<in> (\<Union>c\<in>downset2 a b. sr c)\<^sup>\<leftrightarrow>\<^sup>*"
begin

lemma conv_join_mod_mless_convD:
  assumes "sr.conv M x y"
  shows "valley_mod M x y \<or> (\<exists>N. M \<succ>\<^sub>M N \<and> sr.conv N x y)"
using assms
proof (cases rule: conv_valley_mod_peak_cases)
  case (peak K L a b t u v)
  with peak_decreasing_mod consider "(t, v) \<in> (\<Union>c\<in> downset2 a b. sr c)\<^sup>\<leftrightarrow>\<^sup>*" by presburger
  then have "(t, v) \<in> (\<Union>c\<in> downset2 a b. sr c)\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with downset2_conversion_imp_conv obtain N where "{#a, b#} \<succ>\<^sub>M N" and "sr.conv N t v" by blast
  then have "M \<succ>\<^sub>M K + L + N"
    unfolding peak by (intro mless_mono) auto
  then have "M \<succ>\<^sub>M K + N + L" by (auto simp: ac_simps)
  moreover have "sr.conv (K + N + L) x y"
    using peak and \<open>sr.conv N t v\<close> by (blast intro: sr.conv_trans)
  ultimately show ?thesis by blast
qed simp

text \<open>A mixed conversion is either a valley modulo or can be made smaller w.r.t.\ @{const mless}.\<close>
lemma conv_join_mod_mless_conv_cases:
  assumes "sr.conv M x y"
  obtains
    (valley) "valley_mod M x y" |
    (conv) N
    where "M \<succ>\<^sub>M N" and "sr.conv N x y"
  using conv_join_mod_mless_convD [OF assms] by blast

lemma conv_imp_valley_mod:
  assumes "sr.conv M x y"
  shows "\<exists>N. M \<succeq>\<^sub>M N \<and> valley_mod N x y"
using SN_mless and assms
proof (induct)
  case (IH M)
  from \<open>sr.conv M x y\<close> show ?case
  proof (cases rule: conv_join_mod_mless_conv_cases)
    case valley then show ?thesis by auto
  next
    case (conv N)
    with IH(1) [of N] show ?thesis by (auto elim: mless_trans)
  qed
qed

text \<open>A pair of ARSs which is peak decreasing modulo is Church-Rosser modulo.\<close>
lemma CRm: "CRm R S"
proof-
  { fix x y
    assume "(x,y) \<in> (R \<union> S)\<^sup>\<leftrightarrow>\<^sup>*"
    with conversion_mono[OF RS_subset_sr] have "(x,y) \<in> (\<Union>a\<in>I \<union> J. sr a)\<^sup>\<leftrightarrow>\<^sup>*" by auto
    then obtain M where M:"sr.conv M x y" using sr.conversion_R_conv_iff by auto
    then have "(x,y) \<in> R\<^sup>* O S\<^sup>\<leftrightarrow>\<^sup>* O (R\<inverse>)\<^sup>*" proof(induct M rule: SN_induct [OF SN_mless])
      case (1 M)
      from 1(2) show ?case proof (cases rule:conv_join_mod_mless_conv_cases)
        case valley
        then show ?thesis unfolding join_mod_valley_mod_iff by auto
      next
        case (conv N)
        with 1(1)[OF _ conv(2)] show ?thesis by auto
      qed
    qed }
  then show ?thesis unfolding CRm_def by auto
qed

end
end
end
