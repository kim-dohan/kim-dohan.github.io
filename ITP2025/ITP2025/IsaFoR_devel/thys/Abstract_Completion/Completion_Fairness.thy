(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014-2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Fairness of Completion\<close>

theory Completion_Fairness
  imports
    Abstract_Completion
    Prime_Critical_Pairs
begin

locale kb_inf =
  kb less for less :: "('a, 'b :: infinite) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
begin

lemma CP_subset_imp_rstep_CP_subset:
  assumes "CP R \<subseteq> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)"
  shows "(rstep (CP R))\<^sup>\<leftrightarrow> \<subseteq> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)" (is "_ \<subseteq> ?A")
proof
  fix s t
  assume "(s, t) \<in> (rstep (CP R))\<^sup>\<leftrightarrow>"
  then have "(s, t) \<in> rstep (CP R) \<or> (t, s) \<in> rstep (CP R)" by auto
  moreover
  { fix s t
    assume "(s, t) \<in> rstep (CP R)"
    then have "(s, t) \<in> ?A"
    proof (rule rstepE)
      fix C \<sigma> l r
      presume cp: "(l, r) \<in> CP R"
        and [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      from assms [THEN subsetD, OF cp]
      show ?thesis by auto
    qed auto }
  ultimately show "(s, t) \<in> ?A" by (metis (no_types) Union_sym)
qed

lemma PCP_subset_imp_rstep_PCP_subset:
  assumes "PCP R \<subseteq> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)"
  shows "(rstep (PCP R))\<^sup>\<leftrightarrow> \<subseteq> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)" (is "_ \<subseteq> ?A")
proof
  fix s t
  assume "(s, t) \<in> (rstep (PCP R))\<^sup>\<leftrightarrow>"
  then have "(s, t) \<in> rstep (PCP R) \<or> (t, s) \<in> rstep (PCP R)" by auto
  moreover
  { fix s t
    assume "(s, t) \<in> rstep (PCP R)"
    then have "(s, t) \<in> ?A"
    proof (rule rstepE)
      fix C \<sigma> l r
      presume pcp: "(l, r) \<in> PCP R"
        and [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      from assms [THEN subsetD, OF pcp]
      show ?thesis by auto
    qed auto }
  ultimately show "(s, t) \<in> ?A" by (metis (no_types) Union_sym)
qed

lemma PCP_subset_imp_rstep_PCP_subset':
  assumes "PCP R \<subseteq> (rstep R)\<^sup>\<down> \<union> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)"
  shows "(rstep (PCP R))\<^sup>\<leftrightarrow> \<subseteq> (rstep R)\<^sup>\<down> \<union> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)" (is "_ \<subseteq> ?A")
proof
  fix s t
  assume "(s, t) \<in> (rstep (PCP R))\<^sup>\<leftrightarrow>"
  then have *: "(s, t) \<in> rstep (PCP R) \<or> (t, s) \<in> rstep (PCP R)" by auto
  moreover
  { fix s t
    assume "(s, t) \<in> rstep (PCP R)"
    then have "(s, t) \<in> ?A"
    proof (rule rstepE)
      fix C \<sigma> l r
      presume pcp: "(l, r) \<in> PCP R"
        and [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      from assms [THEN subsetD, OF pcp]
      show ?thesis by auto blast
    qed auto }
  ultimately
  show "(s, t) \<in> ?A" by (auto  intro: join_sym)
qed

lemma fair_imp_nabla:
  assumes "PCP R \<subseteq> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)"
  shows "\<And>s t u. (t, u) \<in> nabla R s \<Longrightarrow> (t, u) \<in> (rstep R)\<^sup>\<down> \<union> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)"
  using PCP_subset_imp_rstep_PCP_subset [OF assms]
  by (auto simp add: nabla_def)

lemma fair_new_imp_nabla:
  assumes "PCP R \<subseteq> (rstep R)\<^sup>\<down> \<union> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)"
  shows "\<And>s t u. (t, u) \<in> nabla R s \<Longrightarrow> (t, u) \<in> (rstep R)\<^sup>\<down> \<union> (\<Union>i\<le>n. (rstep (S i))\<^sup>\<leftrightarrow>)"
  using PCP_subset_imp_rstep_PCP_subset' [OF assms]
  by (auto simp: nabla_def)

lemma finite_run:
  assumes "R 0 = {}" and "E n = {}"
    and run: "\<forall>i<n. (E i, R i) \<turnstile>\<^sub>K\<^sub>B (E (Suc i), R (Suc i))"
    and nabla: "\<And>s t u. (t, u) \<in> nabla (R n) s \<Longrightarrow> (t, u) \<in> (rstep (R n))\<^sup>\<down> \<union> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)"
  shows "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>* \<and> SN (rstep (R n)) \<and> CR (rstep (R n))"
proof -
  have R_less: "\<And>i. i \<le> n \<Longrightarrow> R i \<subseteq> {(x, y). x \<succ> y}"
    and "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>*"
    and SN: "SN (rstep (R n))"
    by (fact finite_runD [OF assms(1-3)])+
  moreover
  have "CR (rstep (R n))"
  proof -
    define mless where "mless x y = mulex less\<inverse>\<inverse> y x" for x y
    write mless (infix "\<succ>''" 50)
    interpret lab: ars_labeled_sn "\<lambda>M. mstep M (R n)" UNIV "(\<succ>')"
      by (standard) (auto simp: mless_def intro: SN_less SN_mulex)
    interpret ars_peak_decreasing "\<lambda>M. mstep M (R n)" UNIV "(\<succ>')"
    proof
      fix s t u :: "('a, 'b) term" and M\<^sub>1 M\<^sub>2 :: "('a, 'b) term multiset"
      define M where "M = {#t, u#}"
      assume "(s, t) \<in> mstep M\<^sub>1 (R n)" and "(s, u) \<in> mstep M\<^sub>2 (R n)"
      then have *: "(s, t) \<in> (rstep (R n))" "(s, u) \<in> rstep (R n)" by (auto iff: mstep_iff)
      { fix v w
        assume "(v, w) \<in> nabla (R n) s"
        then have "(s, v) \<in> (rstep (R n))\<^sup>+" and "(s, w) \<in> (rstep (R n))\<^sup>+" by (auto simp: nabla_def)
        have "M\<^sub>1 \<succ>' {#v, w#}"
        proof -
          from \<open>(s, t) \<in> mstep M\<^sub>1 (R n)\<close> have ne1: "M\<^sub>1 \<noteq> {#}" by (auto iff: mstep_iff)
          have "\<forall>u. u \<in># {#v, w#} \<longrightarrow> (\<exists>z. z \<in># M\<^sub>1 \<and> z \<succ> u)"
          proof -
            { have "\<exists>z. z \<in># M\<^sub>1 \<and> z \<succ> v"
                using \<open>(s, t) \<in> mstep M\<^sub>1 (R n)\<close> and \<open>(s, v) \<in> (rstep (R n))\<^sup>+\<close>
                  and rsteps_subset_less [OF R_less [of n]] by (auto simp: mstep_iff dest: trans) }
            moreover
            { have "\<exists>z. z \<in># M\<^sub>1 \<and> z \<succ> w"
                using \<open>(s, t) \<in> mstep M\<^sub>1 (R n)\<close> and \<open>(s, w) \<in> (rstep (R n))\<^sup>+\<close>
                  and rsteps_subset_less [OF R_less [of n]] by (auto simp: mstep_iff dest: trans) }
            ultimately show ?thesis by (auto simp: M_def)
          qed
          from mulex_on_all_strict [OF ne1 _ _ this, of UNIV]
          have less1: "mulex less\<inverse>\<inverse> {#v, w#} M\<^sub>1" by auto (metis (lifting, no_types) conversep.intros mulex_on_mono)
          then show ?thesis by (simp add: mless_def)
        qed }
      note nabla_less = this

      let ?D = "(\<Union>c\<in>lab.downset2 M\<^sub>1 M\<^sub>2. mstep c (R n))\<^sup>\<leftrightarrow>\<^sup>*"

      { fix v w
        assume nabla': "(v, w) \<in> nabla (R n) s"
        let ?M = "{#v, w#}"
        from nabla [OF nabla']
        have "(v, w) \<in> (rstep (R n))\<^sup>\<down> \<union> (\<Union> i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)" .
        then have "(v, w) \<in> ?D"
        proof
          assume "(v, w) \<in> (rstep (R n))\<^sup>\<down>"
          then obtain u where 1: "(v, u) \<in> (rstep (R n))\<^sup>*"
            and 2: "(w, u) \<in> (rstep (R n))\<^sup>*" by auto
          from rsteps_imp_msteps [of _ ?M, OF _ 1 R_less]
          have "(v, u) \<in> (mstep ?M (R n))\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: M_def)
          from lab.conversion_in_downset2 [OF this] and nabla_less [OF nabla']
          have 3: "(v, u) \<in> ?D" by simp
          from rsteps_imp_msteps [of _ ?M, OF _ 2 R_less]
          have "(u, w) \<in> (mstep ?M (R n))\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: M_def) (metis conversion_def in_rtrancl_UnI rtrancl_converseI)
          from lab.conversion_in_downset2 [OF this] and nabla_less [OF nabla']
          have 4: "(u, w) \<in> ?D" by simp
          from 3 and 4 show ?thesis by (auto simp: conversion_def)
        next
          assume "(v, w) \<in> (\<Union>i \<le> n. (rstep (E i))\<^sup>\<leftrightarrow>)"
          then obtain i where "i \<le> n" and "(v, w) \<in> (rstep (E i))\<^sup>\<leftrightarrow>" by auto
          then have "(v, w) \<in> (mstep ?M (E i))\<^sup>\<leftrightarrow>" by (auto iff: mstep_iff simp: M_def)
          then have "(v, w) \<in> (mstep ?M (E i \<union> R i))\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: conversion_def)
          then show ?thesis using \<open>i \<le> n\<close>
          proof (induct "n - i" arbitrary: i)
            case 0
            with \<open>i \<le> n\<close> have [simp]: "i = n" by arith
            with 0 have "(v, w) \<in> (mstep ?M (R n))\<^sup>\<leftrightarrow>\<^sup>*" by (simp add: assms)
            from lab.conversion_in_downset2 [OF this] and nabla_less [OF nabla']
            show ?case by auto
          next
            case (Suc m)
            from \<open>Suc m = n - i\<close> have *: "m = n - Suc i" and leq: "Suc i \<le> n" by auto
            from run have **: "(E i, R i) \<turnstile>\<^sub>K\<^sub>B (E (Suc i), R (Suc i))" using leq by auto
            from \<open>(v, w) \<in> (mstep ?M (E i \<union> R i))\<^sup>\<leftrightarrow>\<^sup>*\<close>
            have "(v, w) \<in> (mstep ?M (E (Suc i) \<union> R (Suc i)))\<^sup>\<leftrightarrow>\<^sup>*"
              using msteps_subset [OF ** R_less [OF leq]] by blast
            from Suc.hyps(1) [OF * this leq]
            show ?case .
          qed
        qed }
      note ** = this

      from peak_imp_nabla2 [OF SN_imp_variable_condition [OF SN] *]
      show "(t, u) \<in> ?D"
        by (auto dest!: ** simp: conversion_def)
    qed
    from CR show "CR (rstep (R n))" by simp
  qed
  ultimately show ?thesis by blast
qed

text \<open>Every finite and fair run of abstract completion yields a complete TRS
for the given set of equations.\<close>
lemma finite_fair_run:
  assumes "R 0 = {}" and "E n = {}"
    and "\<forall>i<n. (E i, R i) \<turnstile>\<^sub>K\<^sub>B (E (Suc i), R (Suc i))"
    and fair: "PCP (R n) \<subseteq> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)"
  shows "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>* \<and> SN (rstep (R n)) \<and> CR (rstep (R n))"
  using finite_run [OF assms(1-3)] and fair_imp_nabla [OF fair] by blast

lemma finite_fair_new_run:
  assumes "R 0 = {}" and "E n = {}"
    and "\<forall>i<n. (E i, R i) \<turnstile>\<^sub>K\<^sub>B (E (Suc i), R (Suc i))"
    and fair: "PCP (R n) \<subseteq> (rstep (R n))\<^sup>\<down> \<union> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)"
  shows "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>* \<and> SN (rstep (R n)) \<and> CR (rstep (R n))"
  using finite_run [OF assms(1-3)] and fair_new_imp_nabla [OF fair] by blast

end

locale kb_irun_inf =
  kb_irun less for less :: "('a, 'b :: infinite) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
begin

lemma infinite_fair_run:
  assumes nonfail: "E\<^sub>\<omega> = {}"
    and fair: "PCP R\<^sub>\<omega> \<subseteq> (\<Union>i. (rstep (E i))\<^sup>\<leftrightarrow>) \<union> (rstep R\<^sub>\<omega>)\<^sup>\<down>"
  shows "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep R\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>* \<and> SN (rstep R\<^sub>\<omega>) \<and> CR (rstep R\<^sub>\<omega>)"
proof (intro conjI)
  show "SN (rstep R\<^sub>\<omega>)" by (rule SN_rstep_R_per)
  show "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep R\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*"
  proof -
    have "rstep ((\<Union>i. E i) \<union> (\<Union>i. R i)) \<subseteq> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*"
    proof
      fix s t assume "(s, t) \<in> rstep ((\<Union>i. E i) \<union> (\<Union>i. R i))"
      then obtain i where "(s, t) \<in> rstep (E i \<union> R i)" by (auto simp: rstep_union rstep_UN)
      then show "(s, t) \<in> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*"
      proof (induct i arbitrary: s t)
        case (Suc i)
        have "(rstep (E i \<union> R i))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> ((rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*)\<^sup>\<leftrightarrow>\<^sup>*"
          using Suc(1) by (intro conversion_mono) auto
        with Suc(2) and rstep_E_R_Suc_conversion [THEN equalityD2, of i]
        show ?case by auto
      qed (auto simp: R0)
    qed
    from conversion_mono [OF this]
    have "(rstep ((\<Union>i. E i) \<union> (\<Union>i. R i)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*" by simp
    moreover have "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep ((\<Union>i. E i) \<union> (\<Union>i. R i)))\<^sup>\<leftrightarrow>\<^sup>*"
      by (intro conversion_mono) (auto simp: rstep_union rstep_UN)
    ultimately have "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep ((\<Union>i. E i) \<union> (\<Union>i. R i)))\<^sup>\<leftrightarrow>\<^sup>*" by blast
    also have "\<dots> = (rstep (\<Union>i. R i))\<^sup>\<leftrightarrow>\<^sup>*"
    proof
      have "(rstep ((\<Union>i. E i) \<union> (\<Union>i. R i)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> ((rstep (\<Union>i. R i))\<^sup>\<leftrightarrow>\<^sup>*)\<^sup>\<leftrightarrow>\<^sup>*"
        using subset_trans [OF rstep_E_i_subset [OF nonfail] join_imp_conversion]
        by (intro conversion_mono) (auto simp: rstep_union rstep_UN)
      then show "(rstep ((\<Union>i. E i) \<union> (\<Union>i. R i)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (\<Union>i. R i))\<^sup>\<leftrightarrow>\<^sup>*" by simp
    qed (auto simp: rstep_union intro: conversion_mono [THEN subsetD])
    finally show ?thesis unfolding rstep_R_inf_conv_iff [OF nonfail] .
  qed
  interpret ars_source_decreasing "(\<succ>)" "rstep R\<^sub>\<omega>" UNIV
  proof
    have join_rstep:"\<And>s t. (s,t) \<in> rstep ((rstep R\<^sub>\<omega>)\<^sup>\<down>) = ((s,t) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>)"
      using join_ctxt join_subst_rstep by blast
    show "SN {\<succ>}" by (rule SN_less)
    have pcp: "\<And>s t. (s, t) \<in> rstep (PCP R\<^sub>\<omega>) \<Longrightarrow> (s, t) \<in> (\<Union>i. (rstep (E i))\<^sup>\<leftrightarrow>) \<union> (rstep R\<^sub>\<omega>)\<^sup>\<down>"
      using fair [THEN rstep_mono] rstep_rstep join_rstep
      by (auto simp: rstep_UN rstep_union rstep_rstep)
    fix s t u presume "(s, t) \<in> slab R\<^sub>\<omega> s" and "(s, u) \<in> slab R\<^sub>\<omega> s"
    then have "(t, u) \<in> nabla R\<^sub>\<omega> s ^^ 2" using R_per_varcond by (intro peak_imp_nabla2) auto
    moreover
    { fix v w assume *: "(v, w) \<in> nabla R\<^sub>\<omega> s" "v = t \<or> w = u"
      then have "s \<succ> v" and "s \<succ> w"
        using rsteps_subset_less [OF rstep_R_per_less]
        by (auto elim!: nablaE simp: rstep_rstep)
      have Ei:"(\<Union>i. (rstep (E i))\<^sup>\<leftrightarrow>) = (\<Union>i. rstep (E i))\<^sup>\<leftrightarrow>" using rstep_union rstep_UN by blast
      have "(v, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down> \<or> (v, w) \<in> (rstep (PCP R\<^sub>\<omega>))\<^sup>\<leftrightarrow>" using nablaE[OF *(1)] by auto
      then consider "(v, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>" | "(v,w) \<in> rstep (PCP R\<^sub>\<omega>)" | "(w,v) \<in> rstep (PCP R\<^sub>\<omega>)" 
        by auto
      hence "(v, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down> \<or> (v, w) \<in> (\<Union>i. rstep (E i))\<^sup>\<leftrightarrow>"
      proof cases
        case 2
        from pcp[OF this] show ?thesis by auto
      next
        case 3
        from pcp[OF this] join_sym[of w v "rstep R\<^sub>\<omega>"] show ?thesis unfolding Ei by blast
      qed auto
      then consider "(v, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>" | "(v, w) \<in> (\<Union>i. rstep (E i))\<^sup>\<leftrightarrow>" by auto
      then have "(v, w) \<in> (\<Union>v\<in>{v\<in>UNIV. s \<succ> v}. slab R\<^sub>\<omega> v)\<^sup>\<leftrightarrow>\<^sup>*"
      proof (cases)
        case 1
        then obtain x where "(v, x) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" and "(w, x) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" by blast
        then have "(v, x) \<in> (\<Union>a\<in>{a\<in>UNIV. v \<succeq> a}. slab R\<^sub>\<omega> a)\<^sup>\<leftrightarrow>\<^sup>*"
          and "(w, x) \<in> (\<Union>v\<in>{v\<in>UNIV. w \<succeq> v}. slab R\<^sub>\<omega> v)\<^sup>\<leftrightarrow>\<^sup>*"
          using rsteps_slabI [OF _ _ rstep_R_per_less] by auto
        then have "(v, x) \<in> (\<Union>a\<in>{a\<in>UNIV. s \<succ> a}. slab R\<^sub>\<omega> a)\<^sup>\<leftrightarrow>\<^sup>*"
          and "(x, w) \<in> (\<Union>a\<in>{a\<in>UNIV. s \<succ> a}. slab R\<^sub>\<omega> a)\<^sup>\<leftrightarrow>\<^sup>*"
          using \<open>s \<succ> v\<close> and \<open>s \<succ> w\<close>
          by (auto intro: slab_conv_less_label simp: conversion_inv)
        then show ?thesis by (auto simp: conversion_def)
      next
        let ?R = "\<Union>i. R i"
        case 2
        with rstep_E_i_subset [OF nonfail] have "(v, w) \<in> (rstep (\<Union>i. R i))\<^sup>\<down>" by blast
        then obtain x where "(v, x) \<in> (rstep ?R)\<^sup>*" and "(w, x) \<in> (rstep ?R)\<^sup>*" by blast
        then have "(v, x) \<in> (\<Union>a\<in>{a\<in>UNIV. v \<succeq> a}. slab ?R a)\<^sup>\<leftrightarrow>\<^sup>*"
          and "(x, w) \<in> (\<Union>v\<in>{v\<in>UNIV. w \<succeq> v}. slab ?R v)\<^sup>\<leftrightarrow>\<^sup>*"
          using rsteps_slabI [OF _ _ rstep_R_inf_less] by (auto simp: conversion_inv)
        with slab_R_inf_conv [OF nonfail]
        have "(v, x) \<in> (\<Union>a\<in>{a\<in>UNIV. v \<succeq> a}. slab R\<^sub>\<omega> a)\<^sup>\<leftrightarrow>\<^sup>*"
          and "(x, w) \<in> (\<Union>a\<in>{a\<in>UNIV. w \<succeq> a}. slab R\<^sub>\<omega> a)\<^sup>\<leftrightarrow>\<^sup>*" by auto
        then have "(v, x) \<in> (\<Union>a\<in>{a\<in>UNIV. s \<succ> a}. slab R\<^sub>\<omega> a)\<^sup>\<leftrightarrow>\<^sup>*"
          and "(x, w) \<in> (\<Union>a\<in>{a\<in>UNIV. s \<succ> a}. slab R\<^sub>\<omega> a)\<^sup>\<leftrightarrow>\<^sup>*"
          using \<open>s \<succ> v\<close> and \<open>s \<succ> w\<close>
          by (auto intro: slab_conv_less_label simp: conversion_inv)
        then show ?thesis by (auto simp: conversion_def)
      qed }
    ultimately show "(t, u) \<in> (\<Union>v\<in>{v\<in>UNIV. s \<succ> v}. slab R\<^sub>\<omega> v)\<^sup>\<leftrightarrow>\<^sup>*"
      by (auto simp: conversion_def) (blast dest: rtrancl_trans)
  qed
  show "CR (rstep R\<^sub>\<omega>)" using CR by (simp add: UN_source_step)
qed

end

end
