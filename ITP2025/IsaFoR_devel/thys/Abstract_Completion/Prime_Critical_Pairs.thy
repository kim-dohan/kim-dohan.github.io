(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Prime Critical Pairs\<close>

theory Prime_Critical_Pairs
  imports
    CP
    Peak_Decreasingness
begin

no_notation
  subset_mset (infix "#" 50)

text \<open>A prime critical pair is a critical pair s.t. the non-root step is innermost.\<close>
definition PCP :: "('a, 'b::infinite) trs \<Rightarrow> ('a, 'b) rule set"
  where
    "PCP R =
      {(replace_at (fst r') p (snd r) \<cdot> \<sigma>, snd r' \<cdot> \<sigma>) | r p r' \<sigma>.
        overlap R R r p r' \<and>
        \<sigma> = the_mgu (fst r) (fst r' |_ p) \<and>
        (\<forall>u \<lhd> fst r \<cdot> \<sigma>. u \<in> NF (rstep R))}"

lemma PCP_subset_CP:
  "PCP R \<subseteq> CP R"
  by (force simp: PCP_def CP2_def)

text \<open>A (non-empty) peak that is joinable or a prime critical pair.\<close>
definition nabla :: "('a, 'b::infinite) trs \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term rel"
  where
    "nabla R s = {(t, u).
      (s, t) \<in> (rstep R)\<^sup>+ \<and> (s, u) \<in> (rstep R)\<^sup>+ \<and>
      ((t, u) \<in> (rstep R)\<^sup>\<down> \<or> (t, u) \<in> (rstep (PCP R))\<^sup>\<leftrightarrow>)}"

lemma nablaE:
  assumes "(t, u) \<in> nabla R s"
  obtains "(s, t) \<in> (rstep R)\<^sup>+" and "(s, u) \<in> (rstep R)\<^sup>+" and "(t, u) \<in> (rstep R)\<^sup>\<down>"
  | "(s, t) \<in> (rstep R)\<^sup>+" and "(s, u) \<in> (rstep R)\<^sup>+" and "(t, u) \<in> (rstep (PCP R))\<^sup>\<leftrightarrow>"
  using assms by (auto simp: nabla_def)

lemma nabla_joinI [intro]:
  assumes "(t, u) \<in> (rstep R)\<^sup>\<down>"
    and "(s, t) \<in> (rstep R)\<^sup>+" and "(s, u) \<in> (rstep R)\<^sup>+"
  shows "(t, u) \<in> nabla R s"
  using assms by (auto simp: nabla_def)

lemma nabla_rstep_PCP_I [intro]:
  assumes "(t, u) \<in> (rstep (PCP R))\<^sup>\<leftrightarrow>"
    and "(s, t) \<in> (rstep R)\<^sup>+" and "(s, u) \<in> (rstep R)\<^sup>+"
  shows "(t, u) \<in> nabla R s"
  using assms by (auto simp: nabla_def)

lemma nabla_refl_on_rstep_trancl:
  "(s, t) \<in> (rstep R)\<^sup>+ \<Longrightarrow> (t, t) \<in> nabla R s"
  by auto

lemma nabla_imp_nabla_refl:
  assumes "(t, u) \<in> nabla R s"
  shows "(u, u) \<in> nabla R s"
proof -
  have "(s, u) \<in> (rstep R)\<^sup>+" using assms by (auto simp: nabla_def)
  from nabla_refl_on_rstep_trancl [OF this]
  show ?thesis .
qed

lemma nabla_ctxt:
  assumes "(t, u) \<in> nabla R s"
  shows "(C\<langle>t\<rangle>, C\<langle>u\<rangle>) \<in> nabla R (C\<langle>s\<rangle>)"
  using assms by (auto simp: nabla_def dest: trancl_rstep_ctxt)

lemma nabla_subst:
  assumes "(t, u) \<in> nabla R s"
  shows "(t \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> nabla R (s \<cdot> \<sigma>)"
  using assms by (auto simp: nabla_def dest: rsteps_subst_closed)

lemma nabla_sym:
  "(t, u) \<in> nabla R s \<Longrightarrow> (u, t) \<in> nabla R s"
  by (auto simp: nabla_def)

lemma cpeaks_max_imp_PCP:
  assumes cpeaks: "(t, p, s, u) \<in> cpeaks R"
    and max: "\<forall>v \<lhd> s |_ p. v \<in> NF (rstep R)"
  shows "(t, u) \<in> PCP R"
proof -
  from cpeaks obtain l\<^sub>1 r\<^sub>1 l\<^sub>2 r\<^sub>2 \<sigma>
    where "t = replace_at l\<^sub>2 p r\<^sub>1 \<cdot> \<sigma>"
      and s: "s = l\<^sub>2 \<cdot> \<sigma>" and "u = r\<^sub>2 \<cdot> \<sigma>"
      and \<sigma>: "\<sigma> = the_mgu l\<^sub>1 (l\<^sub>2 |_ p)"
      and ol: "overlap R R (l\<^sub>1, r\<^sub>1) p (l\<^sub>2, r\<^sub>2)"
    by (force simp: cpeaks2_def)
  moreover have "\<forall>u \<lhd> l\<^sub>1 \<cdot> \<sigma>. u \<in> NF (rstep R)"
  proof -
    have "p \<in> poss l\<^sub>2" using overlap_source_eq [OF ol] by simp
    then have p: "p \<in> poss (l\<^sub>2 \<cdot> \<sigma>)" by (rule poss_imp_subst_poss)
    from overlap_source_eq [OF ol, simplified, folded \<sigma>]
    have "l\<^sub>2 \<cdot> \<sigma> = replace_at (l\<^sub>2 \<cdot> \<sigma>) p (l\<^sub>1 \<cdot> \<sigma>)"
      by (auto simp: ctxt_of_pos_term_subst [symmetric])
    then have "l\<^sub>2 \<cdot> \<sigma> |_ p = l\<^sub>1 \<cdot> \<sigma>" using replace_at_subt_at [OF p, of "l\<^sub>1 \<cdot> \<sigma>"] by simp
    with max show ?thesis by (simp add: s)
  qed
  ultimately show ?thesis by (force simp: PCP_def)
qed

lemma cpeaks_imp_poss:
  assumes "(t, p, s, u) \<in> cpeaks R"
  shows "p \<in> poss s"
  using assms
  apply (auto simp: cpeaks2_def)
  by (metis fst_conv overlap_source_eq(1) poss_imp_subst_poss)

lemma S3_cpeaks_max_imp_rstep_PCP:
  assumes "(t, p, s, u) \<in> S3 (cpeaks R)"
    and "\<forall>v \<lhd> s |_ p. v \<in> NF (rstep R)"
  shows "(t, u) \<in> rstep (PCP R)"
  using assms
  apply (cases)
  apply auto
  by (metis NF_instance cpeaks_imp_poss cpeaks_max_imp_PCP rstep_rule rstep_subst subt_at_subst supt_subst)

lemma cpeaks_imp_nabla2:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes vc: "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and "(t, p, s, u) \<in> cpeaks R"
  shows "(t, u) \<in> nabla R s ^^ 2"
proof -
  from assms obtain l\<^sub>1 r\<^sub>1 p l\<^sub>2 r\<^sub>2 and \<sigma> :: "('f, 'v) subst"
    where ol: "overlap R R (l\<^sub>1, r\<^sub>1) p (l\<^sub>2, r\<^sub>2)"
      and \<sigma>: "\<sigma> = the_mgu l\<^sub>1 (l\<^sub>2 |_ p)"
      and s: "s = l\<^sub>2 \<cdot> \<sigma>" and t: "t = replace_at l\<^sub>2 p r\<^sub>1 \<cdot> \<sigma>" and u: "u = r\<^sub>2 \<cdot> \<sigma>"
    by (auto simp: cpeaks2_def)
  from ol have *: "(l\<^sub>1, r\<^sub>1) \<in> rstep R" "(l\<^sub>2, r\<^sub>2) \<in> rstep R"
    and **: "l\<^sub>2 \<cdot> \<sigma> = replace_at l\<^sub>2 p l\<^sub>1 \<cdot> \<sigma>"
    using overlap_source_eq [OF ol]
    by (auto dest: overlap_imp_rstep simp: \<sigma>)
  from ol have p: "p \<in> poss l\<^sub>2" by (auto simp: overlap_def dest: fun_poss_imp_poss)
  with ** have sp: "s |_ p = l\<^sub>1 \<cdot> \<sigma>"
    by (auto simp: s) (metis hole_pos_ctxt_of_pos_term hole_pos_subst subt_at_hole_pos)
  have peak: "(s, t) \<in> (rstep R)" "(s, u) \<in> (rstep R)"
    using * by (auto simp: s t u) (auto simp: **)
  from overlap_rstep_pos_left [OF ol]
  have stp: "(s, t) \<in> rstep_pos R p" by (auto simp: s t \<sigma>)
  from overlap_rstep_pos_right [OF ol]
  have sue: "(s, u) \<in> rstep_pos R []" by (auto simp: s u \<sigma>)
  show ?thesis
  proof (cases "\<forall>w \<lhd> s |_ p. w \<in> NF (rstep R)")
    txt \<open>@{term "(t, s, u)"} is a critical peak (at position @{term p}).\<close>
    case True
    with ol have "(t, u) \<in> PCP R" unfolding sp by (force simp: PCP_def s t u \<sigma>)
    with peak have "(t, u) \<in> nabla R s" by (auto)
    with nabla_imp_nabla_refl [OF this] show ?thesis by auto
  next
    case False
    then obtain w where w: "w \<lhd> s |_ p" and "w \<notin> NF (rstep R)" by blast
    then obtain v' where "(w, v') \<in> rstep R" by blast
    from rstep_imp_max_pos [OF this] obtain w' q'
      where "q' \<in> poss w" and q'_step: "(w, w') \<in> rstep_pos R q'"
        and max: "\<forall>v \<lhd> w |_ q'. v \<in> NF (rstep R)" by blast
    from supt_imp_subt_at_nepos [OF w] obtain p'
      where "p' \<noteq> []" and "p' \<in> poss (s |_ p)" and "s |_ p |_ p' = w" by blast
    then have 0: "(p @ p') \<in> poss s" and 1: "s |_ (p @ p') = w" using p by (auto simp: s)
    define q where "q = p @ p' @ q'"
    define v where "v = (ctxt_of_pos_term (p @ p') s)\<langle>w'\<rangle>"
    from rstep_pos_supt [OF q'_step 0 1]
    have svq: "(s, v) \<in> rstep_pos R q" by (auto simp: q_def v_def)
    then have "(s, v) \<in> rstep R" by (auto simp: rstep_rstep_pos_conv)
    have "p <\<^sub>p q" using \<open>p' \<noteq> []\<close> by (simp add: q_def)
    from max have max: "\<forall>v \<lhd> s |_ q. v \<in> NF (rstep R)"
      using 0 and 1 by (auto simp: q_def ac_simps)

    from peak_imp_join_or_S3_cpeaks [OF vc svq sue]
    have svu: "(v, u) \<in> nabla R s"
    proof (cases "(v, q, s, u) \<in> S3 (cpeaks R)")
      case True
      from S3_cpeaks_max_imp_rstep_PCP [OF this max]
      show ?thesis using \<open>(s, v) \<in> rstep R\<close> and \<open>(s, u) \<in> rstep R\<close> by auto
    next
      case False
      with peak_imp_join_or_S3_cpeaks [OF vc svq sue]
      have "(v, u) \<in> (rstep R)\<^sup>\<down>"
        using \<open>p <\<^sub>p q\<close> by (insert Nil_least [of p], auto simp del: Nil_least)
      then show ?thesis using \<open>(s, v) \<in> rstep R\<close> and \<open>(s, u) \<in> rstep R\<close> by auto
    qed

    from peak_imp_join_or_S3_cpeaks [OF vc stp svq]
    show ?thesis
    proof
      assume "(t, v) \<in> (rstep R)\<^sup>\<down>"
      then have *: "(t, v) \<in> nabla R s" using \<open>(s, t) \<in> rstep R\<close> and \<open>(s, v) \<in> rstep R\<close> by auto
      with svu show ?thesis by auto
    next
      assume "q \<le>\<^sub>p p \<and>
       (ctxt_of_pos_term q s)\<langle>t |_ q\<rangle> = t \<and>
       (ctxt_of_pos_term q s)\<langle>v |_ q\<rangle> = v \<and>
       (t |_ q, pos_diff p q, s |_ q, v |_ q) \<in> S3 (cpeaks R) \<or>
       p \<le>\<^sub>p q \<and>
       (ctxt_of_pos_term p s)\<langle>t |_ p\<rangle> = t \<and>
       (ctxt_of_pos_term p s)\<langle>v |_ p\<rangle> = v \<and>
       (v |_ p, pos_diff q p, s |_ p, t |_ p) \<in> S3 (cpeaks R)"
      with \<open>p <\<^sub>p q\<close> have t: "(ctxt_of_pos_term p s)\<langle>t |_ p\<rangle> = t"
        and v: "(ctxt_of_pos_term p s)\<langle>v |_ p\<rangle> = v"
        and *: "(v |_ p, pos_diff q p, s |_ p, t |_ p) \<in> S3 (cpeaks R)" by auto
      from S3_cpeaks_max_imp_rstep_PCP [OF *] and max
      have "(v |_ p,  t |_ p) \<in> rstep (PCP R)"
        using \<open>p <\<^sub>p q\<close> and 0 using subt_at_pos_diff [OF \<open>p <\<^sub>p q\<close>, of s] by simp
      then have "(t, v) \<in> (rstep (PCP R))\<^sup>\<leftrightarrow>"
        apply (subst t [symmetric])
        apply (subst v [symmetric])
        by (metis Un_iff converse_iff rstep_ctxt)
      then have *: "(t, v) \<in> nabla R s" using \<open>(s, t) \<in> rstep R\<close> and \<open>(s, v) \<in> rstep R\<close> by auto
      with svu show ?thesis by auto
    qed
  qed
qed

lemma CS3_cpeaks_imp_nabla2:
  assumes vc: "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and *: "(t, p, s, u) \<in> CS3 (cpeaks R)"
  shows "(t, u) \<in> nabla R s ^^ 2"
proof -
  from * obtain C t' s' p' u' \<sigma> where cp: "(t', p', s', u') \<in> cpeaks R"
    and t: "t = C\<langle>t' \<cdot> \<sigma>\<rangle>" and s: "s = C\<langle>s' \<cdot> \<sigma>\<rangle>" and u: "u = C\<langle>u' \<cdot> \<sigma>\<rangle>"
    and p: "p = hole_pos C @ p'"
    by (cases)
  from cpeaks_imp_nabla2 [OF vc cp] obtain v
    where "(t', v) \<in> nabla R s'" and "(v, u') \<in> nabla R s'" by auto
  then have "(t, C\<langle>v \<cdot> \<sigma>\<rangle>) \<in> nabla R s" and "(C\<langle>v \<cdot> \<sigma>\<rangle>, u) \<in> nabla R s"
    unfolding s t u by (auto intro: nabla_subst nabla_ctxt)
  then show ?thesis by auto
qed

  (*Lemma 5.1.15*)
lemma peak_imp_nabla2:
  assumes vc: "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and peak: "(s, t) \<in> rstep R" "(s, u) \<in> rstep R"
  shows "(t, u) \<in> nabla R s ^^ 2"
proof -
  { assume "(t, u) \<in> (rstep R)\<^sup>\<down>"
    with peak have "(t, u) \<in> nabla R s" by (auto simp: nabla_def)
    with nabla_imp_nabla_refl [OF this] have ?thesis by auto }
  moreover
  { fix p assume "(t, p, s, u) \<in> CS3 (cpeaks R)"
    from CS3_cpeaks_imp_nabla2 [OF vc this] have ?thesis . }
  moreover
  { fix p assume "(u, p, s, t) \<in> CS3 (cpeaks R)"
    from CS3_cpeaks_imp_nabla2 [OF vc this] have ?thesis
      by (auto dest: nabla_sym) }
  ultimately show ?thesis
    using peak_imp_join_or_CS3_cpeaks [OF vc peak] by blast
qed

lemma PCP_join_nabla_imp_join:
  assumes "PCP R \<subseteq> (rstep R)\<^sup>\<down>"
    and "(t, u) \<in> nabla R s"
  shows "(t, u) \<in> (rstep R)\<^sup>\<down>"
  using assms
  apply (auto simp: nabla_def elim!: rstepE)
  apply blast
  done

lemma conversion_trans':
  "(x, y) \<in> A\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> (y, z) \<in> A\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> (x, z) \<in> A\<^sup>\<leftrightarrow>\<^sup>*"
  by (auto simp: conversion_def)

lemma SN_PCP_join_imp_CR:
  assumes vc: "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and SN: "SN (rstep R)"
    and PCP_join: "PCP R \<subseteq> (rstep R)\<^sup>\<down>"
  shows "CR (rstep R)"
proof -
  define less (infix "\<succ>" 50) where "s \<succ> t \<longleftrightarrow> (s, t) \<in> (rstep R)\<^sup>+" for s t
  define lesseq (infix "\<succeq>" 50) where "s \<succeq> t \<longleftrightarrow> (s, t) \<in> (rstep R)\<^sup>*" for s t
  define prestep where "prestep = source_step (rstep R)"
  have [simp]: "(\<Union>a. prestep a) = rstep R" by (auto simp: prestep_def)
  define in_prestep ("_ \<rightarrow>\<^sub>_ _" [50, 50] 51)
    where
      [simp]: "s \<rightarrow>\<^sub>a t \<longleftrightarrow> (s, t) \<in> prestep a" for s a t
  have prestep_iff [iff]: "\<And>s t a. (s, t) \<in> prestep a \<longleftrightarrow> a = s \<and> (s, t) \<in> rstep R"
    by (auto simp: prestep_def)
  interpret lab: ars_labeled_sn prestep UNIV "(\<succ>)"
    by (standard, insert SN) (auto simp: SN_trancl_SN_conv less_def)
  write lab.downset2 ("\<or>'(_,/ _')")
  interpret ars_peak_decreasing "prestep" UNIV "(\<succ>)"
  proof
    fix a b s t u
    presume *: "s \<rightarrow>\<^sub>a t" "s \<rightarrow>\<^sub>b u"
    then have peak: "(s, t) \<in> rstep R" "(s, u) \<in> rstep R" by (auto)
    then have "s \<succ> t" and "s \<succ> u" by (auto simp: less_def)
    from * have "a \<succeq> s" and "b \<succeq> s" by (auto simp: lesseq_def)
    from peak_imp_nabla2 [OF vc peak] obtain v
      where "(t, v) \<in> nabla R s" and "(v, u) \<in> nabla R s" by auto
    with PCP_join have "(t, v) \<in> (rstep R)\<^sup>\<down>" and "(v, u) \<in> (rstep R)\<^sup>\<down>"
      by (auto dest: PCP_join_nabla_imp_join)
    then obtain x z
      where "(t, x) \<in> (rstep R)\<^sup>*" and "(v, x) \<in> (rstep R)\<^sup>*"
        and "(v, z) \<in> (rstep R)\<^sup>*" and "(u, z) \<in> (rstep R)\<^sup>*" by blast
    from \<open>(t, v) \<in> nabla R s\<close> have "(s, v) \<in> (rstep R)\<^sup>+" by (auto simp: nabla_def)
    then have "s \<succ> v" by (auto simp: less_def)
    { fix t u
      assume "(t, u) \<in> (rstep R)\<^sup>*" and "s \<succ> t"
      then have "(t, u) \<in> (\<Union>c\<in>\<or>(a, b). prestep c)\<^sup>\<leftrightarrow>\<^sup>*"
      proof (induct)
        case (step u v)
        then have "(u, v) \<in> prestep u" and "a \<succ> u"
          using \<open>a \<succeq> s\<close> and \<open>s \<succ> t\<close> by (auto simp: lesseq_def less_def)
        with step and \<open>a \<succeq> s\<close> show ?case
          by (auto simp: conversion_def iff del: prestep_iff)
            (metis (lifting, no_types) UN_I Un_iff mem_Collect_eq rtrancl.rtrancl_into_rtrancl)
      qed simp }
    note * = this
    from * [OF \<open>(t, x) \<in> (rstep R)\<^sup>*\<close> \<open>s \<succ> t\<close>]
      and * [OF \<open>(v, x) \<in> (rstep R)\<^sup>*\<close> \<open>s \<succ> v\<close>, THEN conversion_inv [THEN iffD1]]
      and * [OF \<open>(v, z) \<in> (rstep R)\<^sup>*\<close> \<open>s \<succ> v\<close>]
      and * [OF \<open>(u, z) \<in> (rstep R)\<^sup>*\<close> \<open>s \<succ> u\<close>, THEN conversion_inv [THEN iffD1]]
    show "(t, u) \<in> (\<Union>c\<in>\<or>(a, b). prestep c)\<^sup>\<leftrightarrow>\<^sup>*"
      by (blast dest: conversion_trans')
  qed auto
  show ?thesis using CR by simp
qed

lemma PCP_imp_peak:
  assumes "(t, u) \<in> PCP R"
  shows "\<exists>s. (s, t) \<in> (rstep R)\<^sup>* \<and> (s, u) \<in> (rstep R)\<^sup>*"
  using assms
  apply (auto simp: PCP_def)
  by (metis fst_conv overlap_imp_rstep(1) overlap_imp_rstep(2) overlap_source_eq(2) r_into_rtrancl rstep_ctxt rstep_subst subst_apply_term_ctxt_apply_distrib)

lemma CR_imp_PCP_join:
  assumes "CR (rstep R)"
  shows "PCP R \<subseteq> (rstep R)\<^sup>\<down>"
  using assms by (auto simp: CR_defs dest!: PCP_imp_peak)

    (*Corollary 5.1.16*)
lemma SN_imp_CR_iff_PCP_join:
  assumes "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and "SN (rstep R)"
  shows "CR (rstep R) \<longleftrightarrow> PCP R \<subseteq> (rstep R)\<^sup>\<down>"
  using SN_PCP_join_imp_CR [OF assms] and CR_imp_PCP_join [of R] by blast

definition
  "PCP_rules_pos R r p r' =
    {(replace_at (fst (\<pi>\<^sub>2 \<bullet> r')) p (snd (\<pi>\<^sub>1 \<bullet> r)) \<cdot> \<sigma>, snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>) | \<pi>\<^sub>1 \<pi>\<^sub>2 \<sigma>.
    mgu (fst (\<pi>\<^sub>1 \<bullet> r)) (fst (\<pi>\<^sub>2 \<bullet> r') |_ p) = Some \<sigma> \<and>
    overlap R R (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r') \<and>
    (\<forall>u \<lhd> fst (\<pi>\<^sub>1 \<bullet> r) \<cdot> \<sigma>. u \<in> NF (rstep R))}"

lemma PCP_rules_pos_perm:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes "x \<in> PCP_rules_pos R r p r'"
    and "y \<in> PCP_rules_pos R r p r'"
  shows "\<exists>\<pi>. \<pi> \<bullet> x = y"
proof -
  from assms [unfolded PCP_rules_pos_def] obtain \<pi>\<^sub>1 \<pi>\<^sub>2 \<pi>\<^sub>3 \<pi>\<^sub>4 and \<sigma> \<sigma>' :: "('f, 'v) subst"
    where mgu: "mgu (fst (\<pi>\<^sub>1 \<bullet> r)) (fst (\<pi>\<^sub>2 \<bullet> r') |_ p) = Some \<sigma>"
      "mgu (fst (\<pi>\<^sub>3 \<bullet> r)) (fst (\<pi>\<^sub>4 \<bullet> r') |_ p) = Some \<sigma>'"
      and ol: "overlap R R (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r')"
      "overlap R R (\<pi>\<^sub>3 \<bullet> r) p (\<pi>\<^sub>4 \<bullet> r')"
      and x: "x = (replace_at (fst (\<pi>\<^sub>2 \<bullet> r')) p (snd (\<pi>\<^sub>1 \<bullet> r)) \<cdot> \<sigma>, snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>)"
      and y: "y = (replace_at (fst (\<pi>\<^sub>4 \<bullet> r')) p (snd (\<pi>\<^sub>3 \<bullet> r)) \<cdot> \<sigma>', snd (\<pi>\<^sub>4 \<bullet> r') \<cdot> \<sigma>')"
    by blast
  show ?thesis
    using overlap_variants_imp_CP_variants [OF ol(2, 1) mgu(2, 1)]
    by (auto simp: x y eqvt)
qed

lemma PCP_rules_pos_join:
  assumes "x \<in> PCP_rules_pos R r p r'"
    and "y \<in> PCP_rules_pos R r p r'"
  shows "x \<in> (rstep S)\<^sup>\<down> \<longleftrightarrow> y \<in> (rstep S)\<^sup>\<down>"
  using PCP_rules_pos_perm [OF assms] by auto

text \<open>Auxiliary definition to obtain the result that only finitely many PCPs have to be
considered.\<close>
definition
  PCP' :: "('f, 'v::infinite) trs \<Rightarrow> ('f, 'v) rule set set"
  where
    "PCP' R = {PCP_rules_pos R r p r' | r p r'. r \<in> R \<and> r' \<in> R \<and> p \<in> poss (fst r')}"

lemma finite_PCP':
  assumes "finite R"
  shows "finite (PCP' R)"
proof -
  let ?R = "{(r, p, r'). r \<in> R \<and> r' \<in> R \<and> p \<in> poss (fst r')}"
  have *: "PCP' R = (\<lambda>(r, p, r'). PCP_rules_pos R r p r') ` ?R"
    by (force simp: PCP'_def)
  have "{(r, p, r'). r \<in> R \<and> r' \<in> R \<and> p \<in> poss (fst r')} \<subseteq> R \<times> \<Union>(poss ` lhss R) \<times> R"
    by auto
  moreover have "finite (R \<times> \<Union>(poss ` lhss R) \<times> R)"
    using assms and finite_poss by auto
  ultimately have "finite ?R" by (rule finite_subset)
  then show ?thesis unfolding * by (rule finite_imageI)
qed

lemma PCP_Union_PCP':
  "PCP R = \<Union>(PCP' R)"
proof
  show "\<Union>(PCP' R) \<subseteq> PCP R"
  proof
    fix s t
    assume "(s, t) \<in> \<Union>(PCP' R)"
    then obtain r p r' \<pi>\<^sub>1 \<pi>\<^sub>2 \<sigma>
      where "r \<in> R" and "r' \<in> R" and p: "p \<in> poss (fst (\<pi>\<^sub>2 \<bullet> r'))"
        and "mgu (\<pi>\<^sub>1 \<bullet> fst r) (\<pi>\<^sub>2 \<bullet> fst r' |_ p) = Some \<sigma>"
        and ol: "overlap R R (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r')"
        and s: "s = replace_at (fst (\<pi>\<^sub>2 \<bullet> r')) p (snd (\<pi>\<^sub>1 \<bullet> r)) \<cdot> \<sigma>"
        and t: "t = snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>"
        and NF: "\<forall>u \<lhd> fst (\<pi>\<^sub>1 \<bullet> r) \<cdot> \<sigma>. u \<in> NF (rstep R)"
      by (auto simp: PCP'_def PCP_rules_pos_def eqvt)
    then have "\<sigma> = the_mgu (\<pi>\<^sub>1 \<bullet> fst r) (\<pi>\<^sub>2 \<bullet> fst r' |_ p)" by (simp add: the_mgu_def)
    with ol and NF show "(s, t) \<in> PCP R"
      using p
      unfolding PCP_def s t by (force simp add: eqvt ctxt_of_pos_term_subst)
  qed
next
  show "PCP R \<subseteq> \<Union>(PCP' R)"
  proof
    fix s t
    assume "(s, t) \<in> PCP R"
    then obtain r p r' \<sigma>
      where ol: "overlap R R r p r'"
        and "\<sigma> = the_mgu (fst r) (fst r' |_ p)"
        and s: "s = replace_at (fst r') p (snd r) \<cdot> \<sigma>"
        and t: "t = snd r' \<cdot> \<sigma>"
        and NF: "\<forall>u \<lhd> fst r \<cdot> \<sigma>. u \<in> NF (rstep R)"
      by (auto simp: PCP_def)
    then have mgu: "mgu (fst r) (fst r' |_ p) = Some \<sigma>"
      unfolding overlap_def the_mgu_def
      using unify_complete and unify_sound by (force split: option.splits simp: is_imgu_def mgu_def unifiers_def)
    from ol obtain \<pi>\<^sub>1 \<pi>\<^sub>2
      where "\<pi>\<^sub>1 \<bullet> r \<in> R" (is "?r \<in> R")
        and "\<pi>\<^sub>2 \<bullet> r' \<in> R" (is "?r' \<in> R")
        and p: "p \<in> fun_poss (fst r')" by (auto simp: overlap_def)
    moreover
    have "overlap R R (-\<pi>\<^sub>1 \<bullet> ?r) p (-\<pi>\<^sub>2 \<bullet> ?r')" using ol by simp
    moreover
    have "s = (ctxt_of_pos_term p (fst (-\<pi>\<^sub>2 \<bullet> ?r')))\<langle>snd (-\<pi>\<^sub>1 \<bullet> ?r)\<rangle> \<cdot> \<sigma>"
      and "t = snd (-\<pi>\<^sub>2 \<bullet> ?r') \<cdot> \<sigma>"
      using p by (simp_all add: s t ctxt_of_pos_term_subst)
    moreover
    have "mgu (fst (-\<pi>\<^sub>1 \<bullet> ?r)) (fst (-\<pi>\<^sub>2 \<bullet> ?r') |_ p) = Some \<sigma>" using mgu by simp
    moreover have "p \<in> poss (fst ?r')" using fun_poss_imp_poss [OF p] by (simp add: eqvt [symmetric])
    moreover have "\<forall>u \<lhd> fst (-\<pi>\<^sub>1 \<bullet> ?r) \<cdot> \<sigma>. u \<in> NF (rstep R)" using NF by simp
    ultimately show "(s, t) \<in> \<Union>(PCP' R)"
      unfolding PCP'_def PCP_rules_pos_def by blast
  qed
qed

text \<open>If @{term R} is finite, then @{term "PCP' R"} is finite by @{thm finite_PCP'}.
Thus it suffices to prove joinability of finitely many prime critical pairs
in order to conclude joinability of all prime critical pairs @{term "PCP R"}.\<close>
lemma PCP'_representatives_join_imp_PCP_join:
  assumes "\<forall>C\<in>PCP' R. \<exists>(s, t)\<in>C. (s, t) \<in> (rstep S)\<^sup>\<down>"
  shows "\<forall>(s, t)\<in>PCP R. (s, t) \<in> (rstep S)\<^sup>\<down>"
  using assms
  by (auto simp: PCP'_def PCP_Union_PCP')
    (blast dest: PCP_rules_pos_join [of _ R _ _ _ _ S])

lemma PCP_imp_peak':
  fixes R :: "('f, 'v :: infinite) trs"
  assumes "(s, t) \<in> PCP R"
  shows "(s, t) \<in> (rstep R)\<inverse> O (rstep R)"
  using CP2_imp_peak [of s t R R] and assms and PCP_subset_CP [of R] by blast

lemma WCR_imp_PCP_join:
  assumes "(rstep R)\<inverse> O (rstep R) \<subseteq> (rstep R)\<^sup>\<down>"
    and "(s, t) \<in> PCP R"
  shows "(s, t) \<in> (rstep R)\<^sup>\<down>"
  using PCP_imp_peak' [OF assms(2)] and assms(1) by blast

lemma PCP_rules_pos_fair:
  assumes "x \<in> PCP_rules_pos R r p r'"
    and "y \<in> PCP_rules_pos R r p r'"
  shows "x \<in> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>) \<longleftrightarrow> y \<in> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)"
  using PCP_rules_pos_perm [OF assms]
  by (auto simp flip: rstep_converse)

text \<open>If @{term R} is finite, then @{term "PCP' R"} is finite by @{thm finite_PCP'}.
Thus it suffices to prove fairness of finitely many prime critical pairs in order to
conclude fairness of all prime critical pairs @{term "PCP R"}.\<close>
lemma PCP'_representatives_fair_imp_PCP_fair:
  assumes "\<forall>C\<in>PCP' R. \<exists>(s, t)\<in>C. (s, t) \<in> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)"
  shows "\<forall>(s, t)\<in>PCP R. (s, t) \<in> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)"
proof (unfold PCP_Union_PCP', intro ballI2)
  fix s t
  assume "(s, t) \<in> \<Union>(PCP' R)"
  then obtain C where "C \<in> PCP' R" and "(s, t) \<in> C" by auto
  from assms [THEN bspec, OF this(1)] obtain u v
    where "(u, v) \<in> C" and *: "(u, v) \<in> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)" by auto
  from \<open>(s, t) \<in> C\<close> and \<open>(u, v) \<in> C\<close> and \<open>C \<in> PCP' R\<close> obtain r p r'
    where "(s, t) \<in> PCP_rules_pos R r p r'"
      and "(u, v) \<in> PCP_rules_pos R r p r'" by (auto simp: PCP'_def)
  from * [folded PCP_rules_pos_fair [OF this]]
  show "(s, t) \<in> (\<Union>i\<le>n. (rstep (E i))\<^sup>\<leftrightarrow>)" .
qed

end

