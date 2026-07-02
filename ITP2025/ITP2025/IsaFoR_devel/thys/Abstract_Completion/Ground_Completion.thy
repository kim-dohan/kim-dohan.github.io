(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Ground Completion\<close>

theory Ground_Completion
  imports
    Abstract_Completion
    Norm_Equiv.Normalization_Equivalence
    Completion_Fairness
    First_Order_Rewriting.Multihole_Context
    TRS.Q_Restricted_Rewriting
    Ord.KBO_More
begin

definition "ground_trs R \<longleftrightarrow> (\<forall>(l, r) \<in> R. ground l \<and> ground r)"

lemma ground_trs_empty [simp]: "ground_trs {}" by (simp add: ground_trs_def)

lemma in_ground_trs: "ground_trs R \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> ground s \<and> ground t"
  by (auto simp: ground_trs_def)

lemma ground_trs_Diff [simp]:
  "ground_trs A \<Longrightarrow> ground_trs (A - B)"
  by (auto simp: ground_trs_def)

lemma ground_trs_insert [simp]:
  "ground_trs (insert (s, t) A) \<longleftrightarrow> ground s \<and> ground t \<and> ground_trs A"
  by (auto simp: ground_trs_def)

lemma ground_trs_rstep:
  assumes "ground_trs R" and "S \<subseteq> R" and "ground t" and "(t, u) \<in> rstep S"
  shows "ground u"
  using assms
    apply (auto elim!: rstepE dest!: in_ground_trs)
  by (metis ground_subst ground_subst_apply)

lemma left_reduced_unique:
  assumes "left_reduced R" and "(l, r) \<in> R" and "(l, s) \<in> R"
  shows "s = r"
  using assms unfolding left_reduced_def by blast

lemma left_reduced_WCR1:
  assumes "left_reduced R" and "ground_trs R"
  shows "(rstep R)\<inverse> O rstep R \<subseteq> (rstep R O (rstep R)\<inverse>)\<^sup>="
proof
  let ?R = "rstep R"
  fix t u assume "(t, u) \<in> ?R\<inverse> O ?R"
  then obtain s where "(s, t) \<in> ?R" and "(s, u) \<in> ?R" by blast
  with \<open>ground_trs R\<close> obtain C\<^sub>1 l\<^sub>1 r\<^sub>1 and C\<^sub>2 l\<^sub>2 r\<^sub>2
    where rule1: "(l\<^sub>1, r\<^sub>1) \<in> R" and s1: "s = C\<^sub>1\<langle>l\<^sub>1\<rangle>" and t: "t = C\<^sub>1\<langle>r\<^sub>1\<rangle>"
      and rule2: "(l\<^sub>2, r\<^sub>2) \<in> R" and s2: "s = C\<^sub>2\<langle>l\<^sub>2\<rangle>" and u: "u = C\<^sub>2\<langle>r\<^sub>2\<rangle>"
    by (auto elim!: rstepE) (metis ground_subst_apply in_ground_trs)

  have t_mctxt: "t = fill_holes (mctxt_of_ctxt C\<^sub>1) [r\<^sub>1]" by (simp add: t)
  have u_mctxt: "u = fill_holes (mctxt_of_ctxt C\<^sub>2) [r\<^sub>2]" by (simp add: u)

  from \<open>s = C\<^sub>1\<langle>l\<^sub>1\<rangle>\<close> and \<open>s = C\<^sub>2\<langle>l\<^sub>2\<rangle>\<close> show "(t, u) \<in> (?R O ?R\<inverse>)\<^sup>="
  proof (cases rule: two_subterms_cases)
    case eq
    then show ?thesis
      using left_reduced_unique [OF \<open>left_reduced R\<close> rule1] and rule2 by (auto simp: t u)
  next
    case (nested1 C')
    then have "(l\<^sub>1, r\<^sub>1) \<in> R - {(l\<^sub>2, r\<^sub>2)}"
      using s1 and s2 and rule1 by (auto dest: ctxt_supt)
    with nested1 have "l\<^sub>2 \<notin> NF_trs (R - {(l\<^sub>2, r\<^sub>2)})" using s1 and s2 by auto
    then show ?thesis
      using s1 and s2 and rule1 and rule2 and \<open>left_reduced R\<close>
      by (auto simp: t u left_reduced_def)
  next
    case (nested2 D')
    then have "(l\<^sub>2, r\<^sub>2) \<in> R - {(l\<^sub>1, r\<^sub>1)}"
      using s1 and s2 and rule2 by (auto dest: ctxt_supt)
    with nested2 have "l\<^sub>1 \<notin> NF_trs (R - {(l\<^sub>1, r\<^sub>1)})" using s1 and s2 by auto
    then show ?thesis
      using s1 and s2 and rule1 and rule2 and \<open>left_reduced R\<close>
      by (auto simp: t u left_reduced_def)
  next
    case [simp]: (parallel1 C)
    have "fill_holes C [r\<^sub>1, l\<^sub>2] =\<^sub>f (mctxt_of_ctxt C\<^sub>1, concat [[r\<^sub>1],[]])"
      unfolding parallel1 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
    then have t: "t = fill_holes C [r\<^sub>1, l\<^sub>2]" using t_mctxt by (auto dest: eqfE)
    have "fill_holes C [l\<^sub>1, r\<^sub>2] =\<^sub>f (mctxt_of_ctxt C\<^sub>2, concat [[], [r\<^sub>2]])"
      unfolding parallel1 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
    then have u: "u = fill_holes C [l\<^sub>1, r\<^sub>2]" using u_mctxt by (auto dest: eqfE)

    from ctxt_imp_mctxt [OF _ rule1 [THEN rstep_rule], of C "[]" "[r\<^sub>2]"]
    have "(u, fill_holes C [r\<^sub>1, r\<^sub>2]) \<in> ?R" by (auto simp: u)
    moreover from ctxt_imp_mctxt [OF _ rule2 [THEN rstep_rule], of C "[r\<^sub>1]" "[]"]
    have "(t, fill_holes C [r\<^sub>1, r\<^sub>2]) \<in> ?R" by (auto simp: t)
    ultimately show ?thesis by blast
  next
    case [simp]: (parallel2 C)
    have "fill_holes C [l\<^sub>2, r\<^sub>1] =\<^sub>f (mctxt_of_ctxt C\<^sub>1, concat [[],[r\<^sub>1]])"
      unfolding parallel2 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
    then have t: "t = fill_holes C [l\<^sub>2, r\<^sub>1]" using t_mctxt by (auto dest: eqfE)
    have "fill_holes C [r\<^sub>2, l\<^sub>1] =\<^sub>f (mctxt_of_ctxt C\<^sub>2, concat [[r\<^sub>2], []])"
      unfolding parallel2 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
    then have u: "u = fill_holes C [r\<^sub>2, l\<^sub>1]" using u_mctxt by (auto dest: eqfE)

    from ctxt_imp_mctxt [OF _ rule1 [THEN rstep_rule], of C "[r\<^sub>2]" "[]"]
    have "(u, fill_holes C [r\<^sub>2, r\<^sub>1]) \<in> ?R" by (auto simp: u)
    moreover from ctxt_imp_mctxt [OF _ rule2 [THEN rstep_rule], of C "[]" "[r\<^sub>1]"]
    have "(t, fill_holes C [r\<^sub>2, r\<^sub>1]) \<in> ?R" by (auto simp: t)
    ultimately show ?thesis by blast
  qed
qed

definition "WCR1 A \<longleftrightarrow> A\<inverse> O A \<subseteq> (A O A\<inverse>)\<^sup>="

inductive convlr for A
  where
    "convlr A 0 0 a a"
  | "(a, b) \<in> A \<Longrightarrow> convlr A l r b c \<Longrightarrow> convlr A l (Suc r) a c"
  | "(b, a) \<in> A \<Longrightarrow> convlr A l r b c \<Longrightarrow> convlr A (Suc l) r a c"

lemma convlr_imp_conversion:
  assumes "convlr A l r a b"
  shows "(a, b) \<in> A\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
    apply (induct) apply (auto simp: conversion_def)
  apply (meson Un_iff converse_rtrancl_into_rtrancl)
  by (metis converse_rtrancl_into_rtrancl in_rtrancl_UnI r_into_rtrancl rtrancl_converseI rtrancl_idemp)

lemma convlr_trans:
  assumes "convlr A l r a b" and "convlr A l' r' b c"
  shows "convlr A (l + l') (r + r') a c"
  using assms by (induct) (auto simp: convlr.intros)

lemma relpow_imp_convlr:
  assumes "(a, b) \<in> A ^^ n"
  shows "convlr A 0 n a b"
  using assms
  apply (induct n arbitrary: a)
    apply (auto simp: convlr.intros)
  by (meson convlr.intros(2) relpow_Suc_D2')

lemma conversion_imp_convlr:
  assumes "(a, b) \<in> A\<^sup>\<leftrightarrow>\<^sup>*"
  obtains l and r where "convlr A l r a b"
  using assms
  unfolding conversion_def
  apply (induct arbitrary: thesis)
  apply (meson convlr.intros(1))
  by (metis UnE converse_iff convlr.intros(3) convlr.simps convlr_trans)

lemma conversion_iff_convlr: "(a, b) \<in> A\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> (\<exists>l r. convlr A l r a b)"
  by (meson conversion_imp_convlr convlr_imp_conversion)

lemma convlr_rev:
  assumes "convlr A l r a b"
  shows "convlr A r l b a"
  using assms
  apply (induct)
  apply (simp add: convlr.intros(1))
  using convlr.intros(1) convlr.intros(3) convlr_trans apply fastforce
  using convlr.intros(1) convlr.intros(2) convlr_trans by fastforce

text \<open>The Random Descent property\<close>
definition RD :: "'a rel \<Rightarrow> bool"
  where
    "RD A \<longleftrightarrow> (\<forall>a b l r. convlr A l r a b \<and> b \<in> NF A \<longrightarrow> (\<exists>k. k + l = r \<and> (a, b) \<in> A ^^ k))"

text \<open>Balanced weakly Church-Rosser\<close>
definition "BWCR A \<longleftrightarrow> (\<forall>a b. (a, b) \<in> A\<inverse> O A \<longrightarrow> (\<exists>c n. (a, c) \<in> A ^^ n \<and> (b, c) \<in> A ^^ n))"

lemma BWCR_E:
  assumes "BWCR A" and "(a, b) \<in> A" and "(a, c) \<in> A"
  obtains d and n where "(b, d) \<in> A ^^ n" and "(c, d) \<in> A ^^ n"
  using assms unfolding BWCR_def by blast

lemma RD_E:
  assumes "RD A"
    and "convlr A l r a b" and "b \<in> NF A"
  obtains k where "r = k + l" and "(a, b) \<in> A ^^ k"
  using assms unfolding RD_def by blast

lemma BWCR_imp_WCR: "BWCR A \<Longrightarrow> WCR A"
  by (auto simp: WCR_defs) (meson BWCR_E joinI relpow_imp_rtrancl)

lemma WCR1_imp_BWCR:
  assumes "WCR1 r"
  shows "BWCR r"
proof (unfold BWCR_def, intro allI impI)
  fix a b assume "(a, b) \<in> r\<inverse> O r"
  with assms consider "a = b" | c where "(a, c) \<in> r " and "(b, c) \<in> r" by (auto simp: WCR1_def)
  then show "\<exists>c n. (a, c) \<in> r ^^ n \<and> (b, c) \<in> r ^^ n"
  proof (cases)
    case 1
    then show ?thesis by (intro exI [of _ a] exI [of _ 0]) simp
  next
    case 2
    then show ?thesis by (intro exI [of _ c] exI [of _ 1]) simp
  qed
qed

lemma steps_CR_on:
  assumes "CR_on r {a}" and "(a, b) \<in> r\<^sup>*"
  shows "CR_on r {b}"
  using assms
  by (meson CR_onE CR_on_singletonI rtrancl_trans singletonI)

lemma RD_NF:
  assumes "RD A" and "(a, b) \<in> A\<^sup>\<leftrightarrow>\<^sup>*" and "b \<in> NF A"
  shows "CR_on A {a}" and "SN_on A {a}" and "\<And>m n. (a, b) \<in> A ^^ m \<Longrightarrow> (a, b) \<in> A ^^ n \<Longrightarrow> m = n"
proof -
  note RD = RD_E [OF \<open>RD A\<close> _ \<open>b \<in> NF A\<close>]
  obtain l and r where convlr: "convlr A l r a b" using \<open>(a, b) \<in> A\<^sup>\<leftrightarrow>\<^sup>*\<close>
    by (meson conversion_imp_convlr)
  from RD [OF this] have le: "l \<le> r" by (metis le_add2)
  show "SN_on A {a}"
  proof
    fix f :: "nat \<Rightarrow> 'a" presume "f 0 = a" and *: "\<And>i. (f i, f (Suc i)) \<in> A"
    then have "(a, f i) \<in> A ^^ i" for i by (induct i) auto
    from relpow_imp_convlr [OF this, THEN convlr_rev, THEN convlr_trans, OF convlr]
      have "convlr A (l + i) r (f i) b" for i by (simp add: ac_simps)
    from RD [OF this , of "r - l"]
    have "f (r - l) = b" using le by auto
    moreover have "(f (r - l), f (Suc (r - l))) \<in> A" by fact
    ultimately show False using \<open>b \<in> NF A\<close> by auto
  qed force+
  show "CR_on A {a}"
  proof
    fix c d assume "(a, c) \<in> A\<^sup>*" and "(a, d) \<in> A\<^sup>*"
    then obtain m and n where "(a, c) \<in> A ^^ m" and "(a, d) \<in> A ^^ n" by blast
    from convlr_trans [OF relpow_imp_convlr [OF this(1), THEN convlr_rev]]
      and convlr_trans [OF relpow_imp_convlr [OF this(2), THEN convlr_rev]]
    have "convlr A (m + l) r c b" and "convlr A (n + l) r d b"
      using convlr by auto
    then obtain k and k' where "(c, b) \<in> A ^^ k" and "(d, b) \<in> A ^^ k'" by (metis RD)
    then show "(c, d) \<in> A\<^sup>\<down>" by (meson joinI relpow_imp_rtrancl)
  qed

  fix m n assume "(a, b) \<in> A ^^ m" and "(a, b) \<in> A ^^ n"
  from convlr_trans [OF relpow_imp_convlr [OF this(2), THEN convlr_rev]
      relpow_imp_convlr [OF this(1)], THEN RD]
  show "m = n" using \<open>b \<in> NF A\<close>
    by (simp) (metis NF_E add_cancel_left_left relpow_E2)
qed

lemma BWCR_NF:
  assumes "BWCR r" and "(a, b) \<in> r\<^sup>!"
  shows "CR_on r {a}" and "SN_on r {a}" and "\<And>m n. (a, b) \<in> r ^^ m \<Longrightarrow> (a, b) \<in> r ^^ n \<Longrightarrow> m = n"
proof -
  obtain n where "b \<in> NF r" and "(a, b) \<in> r ^^ n" using \<open>(a, b) \<in> r\<^sup>!\<close>
    by (meson normalizability_E rtrancl_len_E)
  { fix m n c assume "(a, b) \<in> r ^^ m" and "(a, c) \<in> r ^^ n"
    then have "n \<le> m \<and> (c, b) \<in> r ^^ (m - n)"
    proof (induct m arbitrary: a c n)
      case 0 then show ?case using \<open>b \<in> NF r\<close> by (auto elim: relpow_E2)
    next
      case IH: (Suc m)
      show ?case
      proof (cases n)
        case 0 then show ?thesis using IH by auto
      next
        case (Suc k)
        with \<open>(a, c) \<in> r ^^ n\<close> and \<open>(a, b) \<in> r ^^ Suc m\<close>
        obtain d and e where "(a, d) \<in> r" and "(a, e) \<in> r"
          and "(d, b) \<in> r ^^ m"
          and "(e, c) \<in> r ^^ k"
          by (meson relpow_Suc_E2)
        with \<open>BWCR r\<close> obtain l and f where "(d, f) \<in> r ^^ l" and "(e, f) \<in> r ^^ l"
          by (auto elim: BWCR_E)
        have "(d, b) \<in> r\<^sup>!" using \<open>b \<in> NF r\<close> and \<open>(d, b) \<in> r ^^ m\<close> by (auto dest: relpow_imp_rtrancl)
        from IH(1) [OF \<open>(d, b) \<in> r ^^ m\<close> \<open>(d, f) \<in> r ^^ l\<close>]
        have "l \<le> m" and "(f, b) \<in> r ^^ (m - l)" by auto
        with \<open>(e, f) \<in> r ^^ l\<close> have "(e, b) \<in> r ^^ m"
          using le_Suc_ex relpow_add by fastforce
        from IH(1) [OF \<open>(e, b) \<in> r ^^ m\<close> \<open>(e, c) \<in> r ^^ k\<close>]
        have "k \<le> m" and "(c, b) \<in> r ^^ (m - k)" by auto
        then show ?thesis unfolding Suc by simp
      qed
    qed }
  note * = this
  show "SN_on r {a}"
  proof
    fix f :: "nat \<Rightarrow> 'a" presume "f 0 = a" and **: "\<And>i. (f i, f (Suc i)) \<in> r"
    moreover then have "(a, f i) \<in> r ^^ i" for i by (induct i) auto
    ultimately have "f n = b" using * [OF \<open>(a, b) \<in> r ^^ n\<close> \<open>(a, f n) \<in> r ^^ n\<close>] by simp
    with \<open>b \<in> NF r\<close> and \<open>(f n, f (Suc n)) \<in> r\<close> show False by auto
  qed force+
  show "CR_on r {a}"
  proof
    fix c d assume "(a, c) \<in> r\<^sup>*" and "(a, d) \<in> r\<^sup>*"
    then obtain m and k where "(a, c) \<in> r ^^ m" and "(a, d) \<in> r ^^ k" by blast
    with * [OF \<open>(a, b) \<in> r ^^ n\<close>] have "(c, b) \<in> r ^^ (n - m)" and "(d, b) \<in> r ^^ (n - k)" by auto
    then have "(c, b) \<in> r\<^sup>*" and "(d, b) \<in> r\<^sup>*" by (auto simp: rtrancl_power)
    then show "(c, d) \<in> r\<^sup>\<down>" by blast
  qed
  show "(a, b) \<in> r ^^ k \<Longrightarrow> (a, b) \<in> r ^^ m \<Longrightarrow> k = m" for k m
    using * [of "max k m" b "min k m"] and \<open>b \<in> NF r\<close>
    by (cases "k \<le> m") (auto simp: max_def min_def elim: relpow_E2)
qed

locale ground_kb = kb_inf False
begin

notation KB (infix "\<turnstile>\<^sub>K\<^sub>B" 55)

lemma rstep_enc [simp]: "rstep_enc R = rstep R"
  unfolding rstep_enc_def by (simp)

inductive gkb ::
    "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> bool" (infix "\<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse>" 55)
  where
    orientl: "s \<succ> t \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E - {(s, t)}, R \<union> {(s, t)})" |
    orientr: "t \<succ> s \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E - {(s, t)}, R \<union> {(t, s)})" |
    delete: "(s, s) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E - {(s, s)}, R)" |
    compose: "(t, u) \<in> rstep (R - {(s, t)}) \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E, (R - {(s, t)}) \<union> {(s, u)})" |
    simplifyl: "(s, u) \<in> rstep R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> ((E - {(s, t)}) \<union> {(u, t)}, R)" |
    simplifyr: "(t, u) \<in> rstep R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> ((E - {(s, t)}) \<union> {(s, u)}, R)" |
    collapse: "(t, u) \<in> rstep_enc (R - {(t, s)}) \<Longrightarrow> (t, s) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E \<union> {(u, s)}, R - {(t, s)})"

lemma gkb_finite:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E', R')" and "finite (E \<union> R)"
  shows "finite (E' \<union> R')"
  using assms by (cases) auto

lemma gkb_imp_KB:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E', R')"
  shows "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')"
  using assms by (cases; blast intro: KB.intros)

definition MSET :: "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) term multiset"
  where
    "MSET R = \<Sum>\<^sub>#{#{#s, t#}. (s, t) \<in># mset_set (fst R)#} + \<Sum>\<^sub>#{#{#s, t#}. (s, t) \<in># mset_set (snd R)#}"

lemma MSET: "MSET (E, R) =
  \<Sum>\<^sub>#{#{#s, t#}. (s, t) \<in># mset_set E#} + \<Sum>\<^sub>#{#{#s, t#}. (s, t) \<in># mset_set R#}"
  by (auto simp: MSET_def)

fun PAIR :: "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) term multiset \<times> ('a, 'b) rule set"
  where
    "PAIR (E, R) = (MSET (E, R), E)"

abbreviation "GT \<equiv> lex_two (s_mul_ext Id {\<succ>}) Id ((measure card)\<inverse>)"

lemma E_subset_MSET: "finite E \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> {#s, t#} \<subseteq># MSET (E, R)"
  apply (auto simp: MSET_def)
  by (metis (mono_tags, lifting) finite_set_mset_mset_set mset_add mset_subset_eq_add_left old.prod.case subset_mset.add_increasing2 subset_mset.le_add_same_cancel1 sum_mset.insert)

lemma R_subset_MSET: "finite R \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> {#s, t#} \<subseteq># MSET (E, R)"
  by (metis E_subset_MSET MSET add.commute)

lemma MSET_Diff_insert:
  assumes "finite E" and "finite R"
    and "(s, t) \<in> E"
  shows "MSET (E - {(s, t)}, insert (s, t) R) =
    (if (s, t) \<in> R then MSET (E, R) - {#s, t#} else MSET (E, R))"
  using assms
  apply (auto simp: MSET_def mset_set_Diff image_mset_Diff)
   apply (subgoal_tac "{#{#s, t#}#} \<subseteq># {#{#s, t#}. (s, t) \<in># mset_set E#}")
    apply (auto simp: sum_mset.remove insert_absorb add_mset_commute)
  apply (subgoal_tac "{#{#s, t#}#} \<subseteq># {#{#s, t#}. (s, t) \<in># mset_set E#}")
   apply (auto simp: sum_mset.remove insert_absorb)
  done

lemma MSET_Diff_insert':
  assumes "finite E" and "finite R"
    and "(s, t) \<in> E"
  shows "MSET (E - {(s, t)}, insert (t, s) R) =
    (if (t, s) \<in> R then MSET (E, R) - {#s, t#} else MSET (E, R))"
  using assms
  apply (auto simp: MSET_def mset_set_Diff image_mset_Diff)
   apply (subgoal_tac "{#{#s, t#}#} \<subseteq># {#{#s, t#}. (s, t) \<in># mset_set E#}")
    apply (auto simp: sum_mset.remove insert_absorb add_mset_commute)
  apply (subgoal_tac "{#{#s, t#}#} \<subseteq># {#{#s, t#}. (s, t) \<in># mset_set E#}")
   apply (auto simp: sum_mset.remove insert_absorb)
  done

lemma MSET_E_Diff:
  assumes "finite E" and "(s, t) \<in> E" shows "MSET (E - {(s, t)}, R) = MSET (E, R) - {#s, t#}"
  using assms
  apply (auto simp: MSET_def mset_set_Diff image_mset_Diff)
  apply (subgoal_tac "{#{#s, t#}#} \<subseteq># {#{#s, t#}. (s, t) \<in># mset_set E#}")
   apply (auto simp: sum_mset.remove add_mset_commute)
  done

lemma MSET_R_Diff:
  assumes "finite R" and "(s, t) \<in> R" shows "MSET (E, R - {(s, t)}) = MSET (E, R) - {#s, t#}"
  using assms
  apply (auto simp: MSET_def mset_set_Diff image_mset_Diff)
  apply (subgoal_tac "{#{#s, t#}#} \<subseteq># {#{#s, t#}. (s, t) \<in># mset_set R#}")
   apply (auto simp: sum_mset.remove add_mset_commute)
  done

lemma MSET_E_insert:
  assumes "finite E"
  shows "MSET (insert (s, t) E, R) = (if (s, t) \<in> E then MSET (E, R) else MSET (E, R) + {#s, t#})"
  using assms
  apply (auto simp: MSET_def mset_set.insert_remove mset_set_Diff image_mset_Diff)
  apply (subgoal_tac "{#{#s, t#}#} \<subseteq># {#{#s, t#}. (s, t) \<in># mset_set E#}")
   apply (auto simp: sum_mset.remove add_mset_commute)
  done

lemma MSET_R_insert:
  assumes "finite R"
  shows "MSET (E, insert (s, t) R) = (if (s, t) \<in> R then MSET (E, R) else MSET (E, R) + {#s, t#})"
  using assms
  apply (auto simp: MSET_def mset_set.insert_remove mset_set_Diff image_mset_Diff)
  apply (subgoal_tac "{#{#s, t#}#} \<subseteq># {#{#s, t#}. (s, t) \<in># mset_set R#}")
   apply (auto simp: sum_mset.remove add_mset_commute)
  done

lemma R_MSET:
  assumes "finite R" and "(s, t) \<in> R"
  shows "s \<in># MSET (E, R) \<and> t \<in># MSET (E, R)"
  using assms by (force simp: MSET)

lemma E_MSET:
  assumes "finite E" and "(s, t) \<in> E"
  shows "s \<in># MSET (E, R) \<and> t \<in># MSET (E, R)"
  using assms by (force simp: MSET)

lemma add_mset_Diff2:
  "N = {#x, y#} \<Longrightarrow> {#x, y#} \<subseteq># M \<Longrightarrow> add_mset y (M - N) = M - {#x#}"
  by (auto simp: multiset_eq_iff subseteq_mset_def split: if_splits)

context
  fixes R
  assumes R_less: "R \<subseteq> {\<succ>}"
begin

lemma gkb_less:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E', R')"
  shows "R' \<subseteq> {\<succ>}"
  using gkb_imp_KB [OF assms] and R_less
  using kb.KB_rtrancl_rules_subset_less kb_axioms by blast

lemma rstep_less:
  assumes "S \<subseteq> R" and "(s, t) \<in> rstep S"
  shows "s \<succ> t"
  using assms
  using R_less compatible_rstep_imp_less by blast

lemma gkb_in_GT:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E', R')" and "finite (E \<union> R)"
  shows "(PAIR (E, R), PAIR (E', R')) \<in> GT"
  using assms
  apply (cases)
  subgoal for s t
    apply (cases "(s, t) \<in> R")
     apply (simp_all add: MSET_Diff_insert)
     apply (subgoal_tac "MSET (E, R) - {#s, t#} \<subset># MSET (E, R)")
      apply (rule disjI1)
      apply (rule subset_mset_imp_s_mul_ext_Id)
      apply assumption
     apply (metis (no_types, lifting) E_subset_MSET add_diff_cancel_left' add_mset_remove_trivial cancel_comm_monoid_add_class.diff_cancel diff_subset_eq_self multi_self_add_other_not_self subset_mset.diff_add subset_mset_def zero_diff)
    by (metis card_gt_0_iff diff_Suc_less equals0D)
  subgoal for t s
     apply (cases "(t, s) \<in> R")
     apply (simp_all add: MSET_Diff_insert')
     apply (subgoal_tac "MSET (E, R) - {#s, t#} \<subset># MSET (E, R)")
      apply (rule disjI1)
      apply (rule subset_mset_imp_s_mul_ext_Id)
      apply assumption
     apply (metis (no_types, lifting) E_subset_MSET add_diff_cancel_left' add_mset_remove_trivial cancel_comm_monoid_add_class.diff_cancel diff_subset_eq_self multi_self_add_other_not_self subset_mset.diff_add subset_mset_def zero_diff)
    by (metis card_gt_0_iff diff_Suc_less equals0D)
  subgoal for s
    apply (simp add: MSET_E_Diff)
    apply (rule disjI1)
    apply (rule subset_mset_imp_s_mul_ext_Id)
    by (metis (no_types, lifting) E_subset_MSET add_diff_cancel_left' add_mset_not_empty cancel_comm_monoid_add_class.diff_cancel diff_subset_eq_self subset_mset.diff_add subset_mset.dual_order.not_eq_order_implies_strict)
  subgoal for t u s
    apply (subgoal_tac "u \<noteq> t")
     apply (cases "(s, u) \<in> R")
      apply (simp_all add: MSET_R_insert MSET_R_Diff)
      apply (rule subset_mset_imp_s_mul_ext_Id)
      apply (metis (no_types, lifting) R_subset_MSET add_diff_cancel_left' add_mset_not_empty cancel_comm_monoid_add_class.diff_cancel diff_subset_eq_self subset_mset.diff_add subset_mset.not_eq_order_implies_strict)
     apply (rule s_mul_ext_IdI [of "{#t#}" _ "MSET (E, R) - {#t#}" _ "{#u#}"])
    using rstep_less [of "R - {(s, t)}" t u, OF Diff_subset]
        apply (simp_all add: R_MSET less_neq)
    apply (subgoal_tac "s \<in># MSET (E, R)")
     apply (simp add: multiset_eq_iff)
    using irrefl rstep_less apply auto[1] apply blast
     apply (simp add: R_MSET)
    done
  subgoal for s u t
    apply (subgoal_tac "u \<noteq> s")
     apply (cases "(u, t) \<in> E")
      apply (simp_all add: MSET_E_insert MSET_E_Diff)
      apply (rule disjI1)
      apply (rule subset_mset_imp_s_mul_ext_Id)
      apply (metis (no_types, lifting) E_subset_MSET add_diff_cancel_left' add_mset_not_empty cancel_comm_monoid_add_class.diff_cancel diff_subset_eq_self subset_mset.diff_add subset_mset.not_eq_order_implies_strict)
     apply (rule disjI1)
     apply (rule s_mul_ext_IdI [of "{#s#}" _ "MSET (E, R) - {#s#}" _ "{#u#}"])
    using rstep_less [of "R" s u, OF subset_refl]
        apply (simp_all add: E_MSET less_neq)
    apply (intro add_mset_Diff2 [OF refl])
    apply (simp add: E_subset_MSET)
    done
  subgoal for t u s
    apply (subgoal_tac "t \<noteq> u")
      apply (cases "(s, u) \<in> E")
      apply (simp_all add: MSET_E_insert MSET_E_Diff)
      apply (rule disjI1)
      apply (rule subset_mset_imp_s_mul_ext_Id)
      apply (metis (no_types, lifting) E_subset_MSET add_diff_cancel_left' add_mset_not_empty cancel_comm_monoid_add_class.diff_cancel diff_subset_eq_self subset_mset.diff_add subset_mset.not_eq_order_implies_strict)
           apply (rule disjI1)
     apply (rule s_mul_ext_IdI [of "{#t#}" _ "MSET (E, R) - {#t#}" _ "{#u#}"])
    using rstep_less [of "R" t u, OF subset_refl]
        apply (simp_all add: E_MSET less_neq)
    apply (intro add_mset_Diff2 [of "{#t, s#}"])
     apply (simp)
    apply (simp add: E_subset_MSET add_mset_commute)
    done
  subgoal for t u s
    apply (simp_all)
    apply (rule disjI1)
    apply (cases "(u, s) \<in> E")
      apply (simp add: insert_absorb)
     apply (rule s_mul_ext_IdI [of "{#t, s#}" _ "MSET (E, R) - {#t, s#}" _ "{#}"])
        apply (simp_all)
      apply (subgoal_tac "{#t, s#} \<subseteq># MSET (E, R)")
       apply (simp add: R_MSET add_mset_Diff2)
      apply (simp add: R_subset_MSET)
    using MSET_R_Diff apply blast
    apply (simp add: MSET_E_insert)
    apply (rule s_mul_ext_IdI [of "{#t#}" _ "MSET (E, R) - {#t#}" _ "{#u#}"])
       apply (simp_all add: R_MSET)
     apply (simp add: MSET_R_Diff R_subset_MSET add_mset_Diff2)
    by (meson Diff_subset kb.rstep_encD kb_axioms rstep_less)
  done

end

lemma SN_GT: "SN GT"
  apply (rule lex_two)
    apply simp
   apply (rule SN_s_mul_ext)
    apply (unfold_locales)
        apply (auto simp: refl_on_def trans_less SN_less trans_Id wf_imp_SN)
  done

lemmas SN_inv_image_GT_PAIR = SN_inv_image [OF SN_GT, of PAIR]

lemma gkb_ground_trs:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E', R')"
    and "ground_trs E" and "ground_trs R"
  shows "ground_trs E' \<and> ground_trs R'"
  using assms(1)
proof (cases)
  case (compose t u s)
  then show ?thesis
    using assms and ground_trs_rstep [of R "R - {(s, t)}" t u]
    by (simp_all add: in_ground_trs)
next
  case (simplifyl s u t)
  then show ?thesis
    using assms and ground_trs_rstep [of R "R" s u]
    by (simp_all add: in_ground_trs)
next
  case (simplifyr t u s)
  then show ?thesis
    using assms and ground_trs_rstep [of R "R" t u]
    by (simp_all add: in_ground_trs)
next
  case (collapse t u s)
  then show ?thesis
    using assms and ground_trs_rstep [of R "R - {(t, s)}" t u]
    by (simp_all add: in_ground_trs)
qed (insert assms, simp_all add: in_ground_trs)

abbreviation "GKB \<equiv> {(X, Y). X \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> Y}"

lemma SN_on_GKB:
  assumes "finite E\<^sub>0"
  shows "SN_on GKB {(E\<^sub>0, {})}"
proof
  fix f assume "f 0 \<in> {(E\<^sub>0, {})}" and "\<forall>i. (f i, f (Suc i)) \<in> GKB"
  then have f0: "f 0 = (E\<^sub>0, {})" and *: "\<And>i. (f i, f (Suc i)) \<in> GKB" by auto
  have "\<forall>i. f i = ((fst \<circ> f) i, (snd \<circ> f) i)" by auto
  then have "\<exists>E R. \<forall>i. f i = (E i, R i)" by blast
  then obtain E and R where [simp]: "f i = (E i, R i)" for i by blast
  have "finite (E i \<union> R i)" for i
    using f0 and * and assms by (induct i) (auto dest: gkb_finite)
  moreover have "R i \<subseteq> {\<succ>}" for i
    using f0 and * by (induct i) (auto dest: gkb_less [THEN subsetD])
  ultimately have "(PAIR (E i, R i), PAIR (E (Suc i), R (Suc i))) \<in> GT" for i
    using * by (intro gkb_in_GT) simp_all
  then have "(PAIR (f i), PAIR (f (Suc i))) \<in> GT" for i by simp
  with SN_inv_image_GT_PAIR show False unfolding SN_defs inv_image_def by blast
qed

lemma min_elt_Ex:
  assumes "finite E"
  shows "\<exists>E' R'. ((E, ({}::('a, 'b) trs)), (E', R')) \<in> GKB\<^sup>* \<and> (E', R') \<in> NF GKB"
proof (induct rule: SN_on_induct' [OF SN_on_GKB [OF assms]])
  case IH: (1 ER)
  show ?case
  proof (cases "ER \<in> NF GKB")
    case True
    show ?thesis
      by (rule exI [of _ "fst ER"], rule exI [of _ "snd ER"]) (auto simp: True)
  next
    case False
    then obtain E' R' where *: "(ER, (E', R')) \<in> GKB" by (force simp: NF_def)
    moreover obtain E'' R'' where "((E', R'), (E'', R'')) \<in> GKB\<^sup>*"
      and "(E'', R'') \<in> NF GKB"  using IH [OF *] by blast
    ultimately show ?thesis
      by (meson converse_rtrancl_into_rtrancl)
  qed
qed

definition "max_run n E R \<longleftrightarrow> (\<forall>i<n. (E i, R i) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E (Suc i), R (Suc i))) \<and> (E n, R n) \<in> NF GKB"

lemma max_run_Ex:
  assumes "finite E\<^sub>0"
  shows "\<exists>n E R. E 0 = E\<^sub>0 \<and> R 0 = {} \<and> max_run n E R"
proof -
  from min_elt_Ex [OF assms] obtain E' and R'
    where "((E\<^sub>0, {}), (E', R')) \<in> GKB\<^sup>*" and [simp]: "(E', R') \<in> NF GKB" by blast
  then obtain f and n where [simp]: "f 0 = (E\<^sub>0, {})" "f n = (E', R')"
    and *: "i < n \<Longrightarrow> (f i, f (Suc i)) \<in> GKB" for i unfolding rtrancl_fun_conv by auto
  show ?thesis
    by (rule exI [of _ n], rule exI [of _ "fst \<circ> f"], rule exI [of _ "snd \<circ> f"])
      (insert *, auto simp: max_run_def)
qed

lemma variant_in_ground_trs:
  assumes "ground_trs R" and "p \<bullet> r \<in> R"
  shows "p \<bullet> r = r"
proof -
  obtain u and v where [simp]: "r = (u, v)" by (cases r)
  have "p \<bullet> r = (p \<bullet> u, p \<bullet> v)" by (simp add: eqvt)
  with assms have "ground (p \<bullet> u)" and "ground (p \<bullet> v)" by (auto simp: ground_trs_def)
  then have "ground u" and "ground v" by (simp_all add: eqvt)
  then have "u \<cdot> sop p = u" and "v \<cdot> sop p = v"
    using ground_subst_apply by blast+
  moreover have "p \<bullet> r = (u \<cdot> sop p, v \<cdot> sop p)" by (simp add: eqvt)
  ultimately show ?thesis by simp
qed

lemma in_ground_trs_vars_rule:
  assumes "ground_trs R" and "r \<in> R"
  shows "vars_rule r = {}"
  using assms by (auto simp: vars_defs ground_trs_def ground_vars_term_empty)

lemma NF_GKB_PCP_empty:
  assumes "ground_trs R" and NF: "(E, R) \<in> NF GKB"
  shows "PCP R = {}"
proof (rule ccontr)
  assume "PCP R \<noteq> {}"
  then obtain s and t where "(s, t) \<in> PCP R" by auto
  then obtain l\<^sub>1 r\<^sub>1 and p and l\<^sub>2 r\<^sub>2 where o: "overlap R R (l\<^sub>1, r\<^sub>1) p (l\<^sub>2, r\<^sub>2)" by (auto simp: PCP_def)
  then have rules: "(l\<^sub>1, r\<^sub>1) \<in> R" "(l\<^sub>2, r\<^sub>2) \<in> R"
    and p: "p \<in> fun_poss l\<^sub>2"
    and *: "p = [] \<longrightarrow> (l\<^sub>1, r\<^sub>1) \<noteq> (l\<^sub>2, r\<^sub>2)"
    using \<open>ground_trs R\<close>
    by (auto simp: overlap_def dest: variant_in_ground_trs)
  then have "ground l\<^sub>1" and "ground (l\<^sub>2 |_ p)"
    using p [THEN fun_poss_imp_poss] and \<open>ground_trs R\<close>
    by (auto simp: in_ground_trs) (metis ctxt_supt_id ground_ctxt_apply in_ground_trs)+
  with o have [simp]: "l\<^sub>1 = l\<^sub>2 |_ p" by (auto simp: overlap_def ground_subst_apply)
  have rule1: "(l\<^sub>1, r\<^sub>1) \<in> R - {(l\<^sub>2, r\<^sub>2)}" (is "_ \<in> ?R")
    using * and rules and p [THEN fun_poss_imp_poss] apply auto
    using subt_at_id_imp_eps by blast
  have "(l\<^sub>2, replace_at l\<^sub>2 p r\<^sub>1) \<in> rstep_enc (R - {(l\<^sub>2, r\<^sub>2)})" (is "(_, ?r) \<in> _")
    using p [THEN fun_poss_imp_poss]
      and rstepI [OF rule1, of l\<^sub>2 "ctxt_of_pos_term p l\<^sub>2" Var, OF _ refl]
    by (auto simp: ctxt_supt_id)
  from gkb.collapse [OF this rules(2)] and NF show False by auto
qed

(* IWC 2017: Theorem 1*)
lemma ground_max_run_canonical:
  assumes max_run: "max_run n E R" and R0: "R 0 = {}"
    and ground: "ground_trs (E 0)"
    and total: "\<And>s t. (s, t) \<in> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> ground s \<Longrightarrow> ground t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"
  shows "ground_trs (R n) \<and> R n \<subseteq> {\<succ>} \<and> E n = {} \<and> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>* \<and> canonical (R n)"
proof -
  have gkb: "\<forall>i<n. (E i, R i) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E (Suc i), R (Suc i))"
    and NF: "(E n, R n) \<in> NF GKB"
    using max_run by (auto simp: max_run_def)

  have gtrs: "ground_trs (E i) \<and> ground_trs (R i)" if "i \<le> n" for i
    using that
  proof (induct i)
    case (Suc i)
    with gkb have "ground_trs (E i)" and "ground_trs (R i)"
      and "(E i, R i) \<turnstile>\<^sub>K\<^sub>B\<^sub>\<inverse> (E (Suc i), R (Suc i))" by auto
    with gkb_ground_trs show ?case by blast
  qed (simp add: ground R0)

  from gkb have KB: "\<forall>i<n. (E i, R i) \<turnstile>\<^sub>K\<^sub>B (E (Suc i), R (Suc i))" by (auto dest: gkb_imp_KB)
  then have KB_rtrancl: "KB\<^sup>*\<^sup>* (E 0, {}) (E n, R n)"
    unfolding rtrancl_fun_conv [to_pred]
    by (intro exI [of _ "\<lambda>i. (E i, R i)"] exI [of _ n]) (auto simp: R0)
  from KB_rtrancl_conversion [OF this]
  have E0: "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E n \<union> R n))\<^sup>\<leftrightarrow>\<^sup>*" by simp

  from KB_rtrancl_rules_subset_less [OF KB_rtrancl]
  have [dest]: "s \<succ> t" if "(s, t) \<in> R n" for s t using that by auto
  have En: "E n = {}"
  proof (rule ccontr)
    assume "E n \<noteq> {}"
    then obtain s t where eq: "(s, t) \<in> E n" by auto
    then have "(s, t) \<in> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*" unfolding E0 by blast
    moreover have "ground s" and "ground t" using gtrs [of n] and eq by (auto dest: in_ground_trs)
    ultimately consider "s = t" | "s \<succ> t" | "t \<succ> s" using total by blast
    then show False
    proof (cases)
      case 1
      from gkb.delete [OF eq [unfolded this]] show ?thesis using NF by blast
    next
      case 2
      from gkb.orientl [OF this eq] show ?thesis using NF by blast
    next
      case 3
      from gkb.orientr [OF this eq] show ?thesis using NF by blast
    qed
  qed
  have "ground_trs (E i)" "ground_trs (R i)" if "i \<le> n" for i
    using ground and R0 and gkb and that
    by (induct i) (auto dest: gkb_ground_trs Suc_le_lessD)
  then have ground_Rn: "ground_trs (R n)" by simp
  have [simp]: "PCP (R n) = {}"
    using max_run by (auto simp: max_run_def dest: NF_GKB_PCP_empty [OF ground_Rn])

  from finite_fair_run [of R E, OF R0 En KB]
  have "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>*"
    and "SN (rstep (R n))" and "CR (rstep (R n))" by auto
  moreover
  have "reduced (R n)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then consider "\<not> left_reduced (R n)" | "\<not> right_reduced (R n)" by (auto simp: reduced_def)
    then show False
    proof (cases)
      case 1
      then obtain l r where lr: "(l, r) \<in> R n" and "l \<notin> NF (rstep (R n - {(l, r)}))"
        by (auto simp: left_reduced_def)
      then obtain u where "(l, u) \<in> rstep (R n - {(l, r)})" by auto
      from gkb.collapse [unfolded rstep_enc, OF this lr] and NF show ?thesis by blast
    next
      case 2
      then obtain l r where lr: "(l, r) \<in> R n" and "r \<notin> NF (rstep (R n))"
        by (auto simp: right_reduced_def)
      then obtain u where *: "(r, u) \<in> rstep (R n)" by auto
      moreover have "(r, u) \<notin> rstep {(l, r)}"
      proof
        assume "(r, u) \<in> rstep {(l, r)}"
        then obtain C and \<sigma> where r: "r = C\<langle>l \<cdot> \<sigma>\<rangle>" and "u = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
        have "l \<succ> r" using lr by blast
        then have "r \<succ> C\<langle>r \<cdot> \<sigma>\<rangle>" by (subst r) (auto dest: subst ctxt)
        moreover define f where "f i = ((\<lambda>t. C\<langle>t \<cdot> \<sigma>\<rangle>) ^^ i) r" for i
        ultimately have "f i \<succ> f (Suc i)" for i
          using subst and ctxt by (induct i) (fastforce)+
        then show False using SN_less by (auto)
      qed
      ultimately have "(r, u) \<in> rstep (R n - {(l, r)})" by blast
      from gkb.compose [OF this lr] and NF show ?thesis by blast
    qed
  qed
  ultimately show ?thesis using ground_Rn and En by (auto simp: canonical_def)
qed

lemma max_run_equiv:
  assumes "egtotal_reduction_order (\<succ>) E"
    and "finite E"
    and "ground_trs E"
    and "R \<subseteq> {\<succ>}"
    and "ground_trs R"
    and "canonical R"
    and RE: "(rstep R)\<^sup>\<leftrightarrow>\<^sup>* = (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<exists>n E' R'. max_run n E' R' \<and> E' 0 = E \<and> R' 0 = {} \<and> E' n = {} \<and> R' n = R"
proof -
  interpret egtotal_reduction_order "(\<succ>)" E by fact
  interpret reduction_order_infinite "(\<succ>)" ..
  from max_run_Ex [OF \<open>finite E\<close>] obtain n E' R'
    where [simp]: "E' 0 = E" "R' 0 = {}" and max: "max_run n E' R'" by blast
  from ground_max_run_canonical [OF max \<open>R' 0 = {}\<close>, simplified, OF \<open>ground_trs E\<close>]
    and egtotal
  have "ground_trs (R' n)" and "R' n \<subseteq> {\<succ>}" and [simp]: "E' n = {}"
    and ER': "(rstep E)\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R' n))\<^sup>\<leftrightarrow>\<^sup>*" and "canonical (R' n)" by auto
  then have "\<forall>(l, r) \<in> R. vars_term r \<subseteq> vars_term l"
    and "\<forall>(l, r) \<in> R' n. vars_term r \<subseteq> vars_term l"
    using \<open>ground_trs R\<close>
    by (auto simp: ground_vars_term_empty dest: in_ground_trs)
  from EQ_imp_litsim [OF this \<open>canonical R\<close> \<open>canonical (R' n)\<close> _ \<open>R \<subseteq> {\<succ>}\<close> \<open>R' n \<subseteq> {\<succ>}\<close>]
  have "R \<doteq> R' n" by (simp add: RE ER')
  with \<open>ground_trs R\<close> and \<open>ground_trs (R' n)\<close> have "R' n = R"
    apply auto
    using litsim_mem and variant_in_ground_trs and subsumable_trs.litsim_sym by metis+
  then show ?thesis using max by force
qed

end

lemma right_reduced_ground_SN:
  assumes rr: "right_reduced R" and ground: "ground_trs R"
  shows "SN (rstep R)" (is "SN ?R")
proof (rule ccontr)
  assume "\<not> SN ?R"
  then obtain t where "t \<in> Tinf ?R" by (blast dest: not_SN_imp_Tinf)
  then have "t \<in> Tinf (qrstep True {} R)" by simp
  from Tinf_imp_SN_nr_first_root_step [OF this] obtain u and v
    where "(u, v) \<in> rrstep R" and "\<not> SN_on ?R {v}" by auto
  with rr and ground show False
    by (auto elim!: rrstepE simp: right_reduced_def)
      (metis NF_imp_SN_on case_prodD ground_subst_apply in_ground_trs)
qed

lemma left_reduced_ground_RD:
  assumes lr: "left_reduced R" and ground: "ground_trs R"
  shows "RD (rstep R)" (is "RD ?R")
proof (unfold RD_def, intro allI impI, elim conjE)
  fix s t and l r assume "convlr ?R l r s t"
    and "t \<in> NF_trs R"
  then show "\<exists>k. k + l = r \<and> (s, t) \<in> ?R ^^ k"
  proof (induct)
    case (1 a)
    then show ?case by auto
  next
    case (2 a b l r c)
    then show ?case by auto (metis relcomp.relcompI relpow_commute)
  next
    case (3 b a l r c)
    then obtain k where "k + l = r" and "(b, c) \<in> ?R ^^ k" by blast
    with \<open>(b, a) \<in> ?R\<close> show ?case
    proof (induct k arbitrary: a b l r)
      case 0
      with \<open>c \<in> NF_trs R\<close> show ?case by auto
    next
      case (Suc k)
      then obtain b' where "(b, b') \<in> ?R" and *: "(b', c) \<in> ?R ^^ k" by (meson relpow_Suc_E2)
      with \<open>(b, a) \<in> ?R\<close> consider "a = b'" | "(a, b') \<in> ?R O ?R\<inverse>"
        using left_reduced_WCR1 [OF lr ground] by blast
      then show ?case
      proof (cases)
        case 1
        then show ?thesis using Suc and * by auto
      next
        from \<open>Suc k + l = r\<close> have **: "k + l = r - 1" by force
        case 2
        then obtain a' where "(a, a') \<in> ?R" and "(b', a') \<in> ?R" by blast
        from Suc(1) [OF this(2) ** *] obtain k' where "k' + Suc l = r - 1"
          and "(a', c) \<in> ?R ^^ k'" by blast
        with \<open>(a, a') \<in> ?R\<close> have "(a, c) \<in> ?R ^^ Suc k'"
          and "Suc k' + Suc l = r"
          by (auto dest: relpow_Suc_I2)
        then show ?thesis by blast
      qed
    qed
  qed
qed

(* IWC 2017: Lemma 3 *)
lemma reduced_ground_RD_and_canonical:
  assumes "reduced R" and "ground_trs R"
  shows "RD (rstep R) \<and> canonical R"
proof -
  have "RD (rstep R)" and "SN (rstep R)" and "WCR1 (rstep R)"
    using assms
    by (auto simp: reduced_def left_reduced_ground_RD right_reduced_ground_SN left_reduced_WCR1 [folded WCR1_def])
  moreover have "WCR (rstep R)" using \<open>WCR1 (rstep R)\<close>
    unfolding WCR_defs and WCR1_def by blast
  ultimately show ?thesis using Newman and \<open>reduced R\<close> unfolding canonical_def by blast
qed

(* IWC 2017: Theorem 4 *)
lemma gkb_complete:
  fixes E :: "('f, 'v :: infinite) trs"
  assumes E: "finite E" "ground_trs E"
    and R: "ground_trs R" "reduced R"
    and eq: "(rstep R)\<^sup>\<leftrightarrow>\<^sup>* = (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" (is "?R\<^sup>\<leftrightarrow>\<^sup>* = ?E\<^sup>\<leftrightarrow>\<^sup>*")
  shows "\<exists>less n E' R'. reduction_order less \<and>
    ground_kb.max_run less n E' R' \<and>
    E' 0 = E \<and> R' 0 = {} \<and> E' n = {} \<and> R' n = R"
proof -
  have RD: "RD ?R" and "canonical R"
    using R by (auto dest: reduced_ground_RD_and_canonical)
  then have SN: "SN ?R" and CR: "CR ?R" by (auto simp: canonical_def)
  define d where "d t = (THE k. (t, the_NF ?R t) \<in> ?R ^^ k)" for t

  obtain P where wo: "well_order_on (UNIV :: ('f \<times> nat) set) P"
    using well_order_on by blast
  define prec where "prec s t \<longleftrightarrow> (t, s) \<in> P - Id" for s t
  have "trans P" using wo by (auto simp: well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def)
  then have prec_refl_trans: "prec x z \<or> x = z" if "prec x y \<or> x = y" and "prec y z \<or> y = z" for x y z
    using that by (auto simp: prec_def dest: transD)
  have prec_asym: "\<And>x y. prec x y \<Longrightarrow> prec y x \<Longrightarrow> False"
    using wo by (auto simp: well_order_on_def linear_order_on_def partial_order_on_def prec_def antisym_def)
  have prec_total: "\<And>x y. x = y \<or> prec x y \<or> prec y x"
    using wo by (auto simp: well_order_on_def linear_order_on_def Relation.total_on_def prec_def)
  have "SN {(x, y). prec x y}"
  proof -
    have "(P - Id) = {(x, y). (y, x) \<in> P \<and> y \<noteq> x}\<inverse>" by auto
    with wo show ?thesis by (auto simp: well_order_on_def prec_def SN_iff_wf)
  qed
  then interpret admissible_kbo "\<lambda>(f, n). 2" 1 prec "prec\<^sup>=\<^sup>=" "\<lambda>_. False" "\<lambda>_ _. 1"
    apply (unfold_locales)
            apply simp_all
     apply (erule prec_refl_trans, simp)
    apply (auto dest: prec_asym)
    done
  have SN: "SN ?R" by fact
  have "SN kbo_S" by (intro S_SN) 
  from S_ground_total[OF refl, of UNIV]
  have gtotal: "s = t \<or> S s t \<or> S t s" if "ground s" and "ground t" for s t :: "('f, 'v) term"
    using that prec_total by auto
  define less where "less s t \<longleftrightarrow> (s, t) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>* \<and> (d s > d t \<or> d s = d t \<and> S s t)" for s t

  have dist: "(t, the_NF ?R t) \<in> ?R ^^ d t" (is "(t, ?u) \<in> _") for t
  proof -
    have "(t, ?u) \<in> ?R\<^sup>!" using SN and CR by (rule the_NF)
    then obtain k where k: "(t, ?u) \<in> ?R ^^ k"
      and nf: "?u \<in> NF_trs R" by (auto simp: normalizability_def)
    then have "(t, ?u) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
      by (auto simp: conversionI' relpow_imp_rtrancl)
    from RD_NF(3) [OF RD this nf k] have "\<And>n. (t, ?u) \<in> ?R ^^ n \<Longrightarrow> k = n" by blast
    with k have "\<exists>!k. (t, ?u) \<in> ?R ^^ k" by blast
    then show ?thesis unfolding d_def by (rule theI')
  qed
  have uniq: "n = d t" if "(t, the_NF ?R t) \<in> ?R ^^ n" for t n
    using that and RD_NF(3) [OF RD _ _ _ dist, of t n] and the_NF [OF SN CR, of t] by auto

  have d_ctxt_subst: "d (C\<langle>t \<cdot> \<sigma>\<rangle>) = d (C\<langle>the_NF ?R t \<cdot> \<sigma>\<rangle>) + d t" (is "d ?t = d ?u + _") for C t \<sigma>
  proof -
    have u: "(?u, the_NF ?R ?u) \<in> ?R ^^ d ?u" by (rule dist)
    have t: "(t, the_NF ?R t) \<in> ?R ^^ d t" by (rule dist)
    then have *: "(?t, ?u) \<in> ?R ^^ d t"
      by (simp add: ctxt.closed_relpow [OF ctxt_closed_rstep] ctxt.closedD subst.closedD subst.closed_relpow subst_closed_rstep)
    then have "(?t, the_NF ?R ?t) \<in> ?R ^^ (d t + d ?u)"
      using the_NF_steps [OF SN CR relpow_imp_rtrancl [OF *]]
      using u and relpow_add by fastforce
    from uniq [OF this] show ?thesis by simp
  qed

  have d_ctxt_subst_eq: "d (C\<langle>s \<cdot> \<sigma>\<rangle>) = d (C\<langle>t \<cdot> \<sigma>\<rangle>)"
    if d: "d s = d t" and conv: "(s, t) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" for s t C \<sigma>
    by (subst (1 2) d_ctxt_subst) (simp add: that the_NF_conv [OF SN CR conv])

  have d_ctxt_subst_less: "d (C\<langle>s \<cdot> \<sigma>\<rangle>) > d (C\<langle>t \<cdot> \<sigma>\<rangle>)"
    if d: "d s > d t" and conv: "(s, t) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" for s t C \<sigma>
    by (subst (1 2) d_ctxt_subst) (simp add: that the_NF_conv [OF SN CR conv])

  have "d l > d r" if "(l, r) \<in> R" for l r
  proof -
    have "(r, the_NF ?R r) \<in> ?R ^^ d r" by (rule dist)
    moreover have "(l, r) \<in> ?R" using that by blast
    ultimately have "(l, the_NF ?R l) \<in> ?R ^^ Suc (d r)"
      using the_NF_step [OF SN CR \<open>(l, r) \<in> ?R\<close>]
      by (intro relpow_Suc_I2) auto
    from uniq [OF this] show ?thesis by simp
  qed
  then have *: "R \<subseteq> {(x, y). less x y}" by (auto simp: less_def)
  have egtro: "egtotal_reduction_order less E"
  proof
    fix s t :: "('f, 'v) term" assume "(s, t) \<in> ?E\<^sup>\<leftrightarrow>\<^sup>*" and gr: "ground s" "ground t"
    with gtotal [OF gr] 
    show "s = t \<or> less s t \<or> less t s" unfolding less_def and eq
      by (simp only: conversion_inv fst_conv) (metis linorder_neqE_nat)
  next
    show "SN {(x, y). less x y}"
    proof -
      have "SN ((inv_image (less_than <*lex*> (kbo_S\<inverse>)) (\<lambda>x. (d x, x)))\<inverse>)" (is "SN ?L")
        unfolding SN_iff_wf and converse_converse
        by (blast intro: SN_imp_wf \<open>SN kbo_S\<close>)
      moreover have "{(x, y). less x y} \<subseteq> ?L" by (auto simp: less_def)
      ultimately show ?thesis
        using SN_subset by blast
    qed
    fix s t C assume less: "less s t"
    then have st: "(s, t) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: less_def)
    then have ctxt_subst: "(C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" for C and \<sigma>
      by (metis CR CR_imp_conversionIff_join ctxt.closedD ctxt.closed_conversion ctxt_closed_rstep join_subst_rstep)
    consider "d s > d t" | "d s = d t" and "S s t"
      using less unfolding less_def by blast
    then show "less (C\<langle>s\<rangle>) (C\<langle>t\<rangle>)"
    proof (cases)
      case 1
      from d_ctxt_subst_less [OF this st, of _ Var] show ?thesis
        using ctxt_subst [of C Var] by (simp add: less_def)
    next
      case 2
      then have "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" and "S (C\<langle>s\<rangle>) (C\<langle>t\<rangle>)"
        using S_ctxt and ctxt_subst [of _ Var] by simp_all
      moreover have "d (C\<langle>s\<rangle>) = d (C\<langle>t\<rangle>)" using 2 and st and d_ctxt_subst_eq [of s t C Var] by simp
      ultimately show ?thesis unfolding less_def by blast
    qed
    fix s t \<sigma> assume less: "less s t"
    then have st: "(s, t) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: less_def)
    then have ctxt_subst: "(C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" for C and \<sigma>
      by (metis CR CR_imp_conversionIff_join ctxt.closedD ctxt.closed_conversion ctxt_closed_rstep join_subst_rstep)
    consider "d s > d t" | "d s = d t" and "S s t"
      using less unfolding less_def by blast
    then show "less (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
    proof (cases)
      case 1
      from d_ctxt_subst_less [OF this st, of \<box> \<sigma>] show ?thesis
        using ctxt_subst [of \<box> \<sigma>] by (simp add: less_def)
    next
      case 2
      then have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" and "S (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
        using S_subst and ctxt_subst [of \<box>] by simp_all
      moreover have "d (s \<cdot> \<sigma>) = d (t \<cdot> \<sigma>)" using 2 and st and d_ctxt_subst_eq [of s t \<box> \<sigma>] by simp
      ultimately show ?thesis unfolding less_def by blast
    qed
    fix s t u assume "less s t" and "less t u" then show "less s u"
      unfolding less_def
      using S_trans [of s t u] and conversion_trans' [of s t ?R u] by auto
  qed
  interpret egtotal_reduction_order less by fact
  interpret ground_kb less ..
  from max_run_equiv [OF egtro E * \<open>ground_trs R\<close> \<open>canonical R\<close> eq] show ?thesis
    using reduction_order_axioms by auto
qed

end
