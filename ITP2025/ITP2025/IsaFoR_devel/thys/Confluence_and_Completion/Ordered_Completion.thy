(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016, 2017)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2017, 2018)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Ordered Completion\<close>

theory Ordered_Completion
  imports
    Ord.Ordered_Rewriting
    Norm_Equiv.Encompassment
    Norm_Equiv.Normalization_Equivalence
    Knuth_Bendix_Order.Lexicographic_Extension
    Ord.KBO_More
    Weighted_Path_Order.Multiset_Extension2
    Abstract_Completion.Abstract_Completion
    Abstract_Completion.Prime_Critical_Pairs
    TRS.Q_Restricted_Rewriting
    TA.Exact_Tree_Automata_Completion (* for stuff on linearity *)
begin
hide_const (open) Exact_Tree_Automata_Completion.fground

locale ordered_completion = reduction_order
begin


definition lessencp (infix "\<cdot>\<succ>" 50) where "lessencp s t \<longleftrightarrow> (s, t) \<in> (relto ({\<cdot>\<rhd>} \<union> {\<succ>}) {\<cdot>\<unrhd>})\<^sup>+"
abbreviation lessenc ("{\<cdot>\<succ>}") where "lessenc \<equiv> {(s, t). s \<cdot>\<succ> t}"

definition leqencp (infix "\<cdot>\<succeq>" 50) where "leqencp s t \<longleftrightarrow> (s, t) \<in> (relto ({\<cdot>\<rhd>} \<union> {\<succ>}) {\<cdot>\<unrhd>})\<^sup>+ \<union> {\<cdot>\<unrhd>}\<^sup>*"
abbreviation leqenc ("{\<cdot>\<succeq>}") where "leqenc \<equiv> {(s, t). s \<cdot>\<succeq> t}"

lemma SN_lessenc: "SN {\<cdot>\<succ>}"
  using reduction_order.SN_encomp_Un_less_relto_encompeq
    SN_encomp_Un_less_relto_encompeq SN_trancl_SN_conv unfolding lessencp_def by auto

lemma lessenc_compat1: "{\<cdot>\<succ>} O {\<cdot>\<unrhd>} \<subseteq> {\<cdot>\<succ>}"
proof
  fix s t
  let ?R = "{\<cdot>\<unrhd>}\<^sup>* O ({\<cdot>\<rhd>} \<union> {\<succ>}) O {\<cdot>\<unrhd>}\<^sup>*"
  assume "(s, t) \<in> {\<cdot>\<succ>} O {\<cdot>\<unrhd>}"
  then obtain u where u: "(u, t) \<in> {\<cdot>\<unrhd>}" "s \<cdot>\<succ> u" by auto
  then obtain v where v: "(v, u) \<in> ?R" "(s, v) \<in> ?R\<^sup>*" using tranclD2 unfolding lessencp_def by metis
  from u(1) v(1) have "(v, t) \<in> ?R O {\<cdot>\<unrhd>}" by blast
  with u(1) v(1) have "(v, t) \<in> ?R" using O_assoc O_mono2 [of "{\<cdot>\<unrhd>} O {\<cdot>\<unrhd>}\<^sup>*" "{\<cdot>\<unrhd>}\<^sup>*"]
    by (smt r_into_rtrancl relcomp.relcompI rtrancl_idemp_self_comp u(1) v(1))
  with v(2) have "s \<cdot>\<succ> t" unfolding trancl_unfold_right lessencp_def by blast
  then show "(s, t) \<in> {\<cdot>\<succ>}" by auto
qed

lemma lessleqenc_compat1: "{\<cdot>\<succ>} O {\<cdot>\<succeq>} \<subseteq> {\<cdot>\<succ>}"
proof
  fix x z
  assume "(x, z) \<in> {\<cdot>\<succ>} O {\<cdot>\<succeq>}"
  then obtain y where y: "(x, y) \<in> {\<cdot>\<succ>}" "(y, z) \<in> {\<cdot>\<succeq>}" by auto
  then consider "y \<cdot>\<succ> z" | "(y, z) \<in> {\<cdot>\<unrhd>}\<^sup>*"
    unfolding leqencp_def lessencp_def Un_iff by blast
  then show "(x, z) \<in> {\<cdot>\<succ>}"
  proof (cases)
    case 1
    with y(1) show ?thesis using trancl_trans unfolding lessencp_def by auto
  next
    case 2
    from encompeq_trans trans_inv_image transI have t: "trans {\<cdot>\<unrhd>}"
      by (smt Pair_inject case_prodE case_prodI2 mem_Collect_eq)
    have "{\<cdot>\<unrhd>}\<^sup>* = {\<cdot>\<unrhd>}" by(rule trans_refl_imp_rtrancl_id, insert t encompeq_refl refl_O_iff, auto)
    with 2 [unfolded this] y(1) lessenc_compat1 show ?thesis by auto
  qed
qed

lemma lessenc_compat2: "{\<cdot>\<unrhd>} O {\<cdot>\<succ>} \<subseteq> {\<cdot>\<succ>}"
proof
  fix s t
  let ?R = "{\<cdot>\<unrhd>}\<^sup>* O ({\<cdot>\<rhd>} \<union> {\<succ>}) O {\<cdot>\<unrhd>}\<^sup>*"
  assume "(s, t) \<in> {\<cdot>\<unrhd>} O {\<cdot>\<succ>}"
  then obtain u where u: "(s, u) \<in> {\<cdot>\<unrhd>}" "u \<cdot>\<succ> t" by auto
  then obtain v where v: "(u, v) \<in> ?R" "(v, t) \<in> ?R\<^sup>*" using tranclD unfolding lessencp_def by metis
  from u(1) v(1) have "(s, v) \<in> {\<cdot>\<unrhd>} O ?R" by blast
  with u(1) v(1) have "(s, v) \<in> ?R" using O_assoc O_mono2 [of "{\<cdot>\<unrhd>} O {\<cdot>\<unrhd>}\<^sup>*" "{\<cdot>\<unrhd>}\<^sup>*"]
    by (smt r_into_rtrancl relcomp.relcompI rtrancl_idemp_self_comp u(1) v(1))
  with v(2) have "s \<cdot>\<succ> t" unfolding trancl_unfold_left lessencp_def by blast
  then show "(s, t) \<in> {\<cdot>\<succ>}" by auto
qed

lemma trans_less_enc: "trans {\<cdot>\<succ>}"
proof -
  from commutes_rewrel_encomp [of "{\<succ>}"] and ctxt and subst have "{\<cdot>\<unrhd>} O {\<succ>} \<subseteq>  {\<succ>} O {\<cdot>\<unrhd>}" by simp
  with trans_relto [of "{\<succ>}" "{\<cdot>\<unrhd>}"] and trans show ?thesis unfolding lessencp_def by auto
qed

lemma refl_encompeq: "refl {\<cdot>\<unrhd>}"
  using encompeq_refl reflpI reflp_refl_eq by fastforce

abbreviation "mulless \<equiv> s_mul_ext {\<cdot>\<unrhd>} {\<cdot>\<succ>}"
abbreviation "mulleq \<equiv> ns_mul_ext {\<cdot>\<unrhd>} {\<cdot>\<succ>}"

sublocale lessenc_op: SN_order_pair mulless "ns_mul_ext {\<cdot>\<unrhd>} {\<cdot>\<succ>}"
proof (intro SN_order_pair.mul_ext_SN_order_pair)
  show "SN_order_pair {\<cdot>\<succ>} {\<cdot>\<unrhd>}"
  proof
    show "trans {\<cdot>\<succ>}" using trans_less_enc by auto
  next
    show "refl {\<cdot>\<unrhd>}" using refl_encompeq .
  next
    show "trans {\<cdot>\<unrhd>}" using encomp_order.order_trans transpI transp_trans by metis
  next
    from SN_lessenc show "SN {\<cdot>\<succ>}" by auto
  next
    from lessenc_compat2 show "{\<cdot>\<unrhd>} O {\<cdot>\<succ>} \<subseteq> {\<cdot>\<succ>}" by auto
  next
    from lessenc_compat1 show "{\<cdot>\<succ>} O {\<cdot>\<unrhd>} \<subseteq> {\<cdot>\<succ>}" by auto
  qed
qed

lemma mset_two:
  assumes "s \<cdot>\<succ> u"
  shows "({#s, t#}, {#u, t#}) \<in> mulless"
proof -
  from assms s_mul_ext_singleton have su: "({#s#}, {#u#}) \<in> mulless" by auto
  from ns_mul_ext_refl [OF refl_encompeq] have "({#t#}, {#t#}) \<in> mulleq" by auto
  from s_ns_mul_ext_union_compat [OF su this] show ?thesis
    using add.commute add_mset_add_single by metis
qed

lemma mset_two2:
  assumes "s \<cdot>\<succ> u"
  shows "({#t, s#}, {#t, u#}) \<in> mulless"
  using mset_two [OF assms] add_mset_commute by (metis (no_types, lifting))


lemma mset_two3:
  assumes "s \<cdot>\<succ> u" and "s \<cdot>\<succ> v"
  shows "({#s, t#}, {#u, v#}) \<in> mulless"
proof -
  from assms all_s_s_mul_ext[of "{#s#}"] have su: "({#s#}, {#u,v#}) \<in> mulless" by auto
  with s_mul_ext_extend_left[OF this, of "{#t#}"] add_mset_commute[of t s "{#}"] show ?thesis by auto
qed


definition "ostep E R = rstep R \<union> ordstep {\<succ>} (E\<^sup>\<leftrightarrow>)"

lemma ostep_iff_ordstep:
  assumes "R \<subseteq> {\<succ>}"
  shows "ostep E R = ordstep {\<succ>} (R \<union> E\<^sup>\<leftrightarrow>)"
  using subst_closed_less and assms by (simp add: ordstep_Un ostep_def ordstep_rstep_conv)

lemma ostep_cases [consumes 1, cases pred: ostep]:
  assumes "(s, t) \<in> ostep E R"
  obtains (rstep) l r C \<sigma> where "(l, r) \<in> R" and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  | (ordstep) l r C \<sigma> where "(l, r) \<in> E\<^sup>\<leftrightarrow>" and "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  using assms by (fastforce simp: ostep_def elim: ordstep.cases)

lemma ostep_mono:
  "E \<subseteq> E' \<Longrightarrow> R \<subseteq> R'\<Longrightarrow> ostep E R \<subseteq> ostep E' R'"
  by (auto simp: ostep_def rstep_mono [THEN subsetD]
      intro: ordstep_mono [THEN subsetD, OF _ subset_refl, of "E\<^sup>\<leftrightarrow>" "E'\<^sup>\<leftrightarrow>"])

lemma rstep_imp_ostep: "(s, t) \<in> rstep R \<Longrightarrow> (s, t) \<in> ostep E R" by (auto simp: ostep_def)

lemma ostep_imp_rstep_sym:
  "(s, t) \<in> ostep E R \<Longrightarrow> (s, t) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>)"
  unfolding ostep_def using ordstep_imp_rstep by fast

lemma E_imp_ostep:
  "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma> \<Longrightarrow> (l, r) \<in> E\<^sup>\<leftrightarrow> \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> (s, t) \<in> ostep E R"
  by (auto simp: ostep_def intro: ordstep.intros)

lemma ostep_subst:
  "(s, t) \<in> ostep E R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ostep E R"
  using ordstep_subst [of "{\<succ>}", OF subst_closed_less] and rstep_subst
  by (auto simp: ostep_def)

lemma ostep_ctxt:
  "(s, t) \<in> ostep E R \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> ostep E R"
  using ordstep_ctxt [where ord = "{\<succ>}"] and rstep_ctxt
  by (auto simp: ostep_def)

lemma ostep_imp_less:
  "R \<subseteq> {\<succ>} \<Longrightarrow> (s, t) \<in> ostep E R \<Longrightarrow> s \<succ> t"
  by (force simp: ostep_def subst ctxt elim: ordstep.cases)

inductive
  oKB :: "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> bool" (infix "\<turnstile>\<^sub>o\<^sub>K\<^sub>B" 55)
  where
    deduce: "(s, t) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, u) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E \<union> {(t, u)}, R)" |
    orientl: "s \<succ> t \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E - {(s, t)}, R \<union> {(s, t)})" |
    orientr: "t \<succ> s \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E - {(s, t)}, R \<union> {(t, s)})" |
    delete: "(s, s) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E - {(s, s)}, R)" |
    compose: "(t, u) \<in> ostep E (R - {(s, t)}) \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E, (R - {(s, t)}) \<union> {(s, u)})" |
    simplifyl: "(s, u) \<in> ostep (E - {(s, t)}) R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B ((E - {(s, t)}) \<union> {(u, t)}, R)" |
    simplifyr: "(t, u) \<in> ostep (E - {(s, t)}) R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B ((E - {(s, t)}) \<union> {(s, u)}, R)" |
    collapse: "(t, u) \<in> ostep E (R - {(t, s)}) \<Longrightarrow> (t, s) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E \<union> {(u, s)}, R - {(t, s)})"

lemma oKB_less:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')" and "R \<subseteq> {\<succ>}"
  shows "R' \<subseteq> {\<succ>}"
proof -
  have [dest]: "(x, y) \<in> R \<Longrightarrow> x \<succ> y" for x y using \<open>R \<subseteq> {\<succ>}\<close> by auto
  note assms(1)
  moreover
  { fix s t u assume "(t, u) \<in> rstep (R - {(s, t)})" and "(s, t) \<in> R"
    then have "s \<succ> u" by (induct t u) (blast intro: subst ctxt dest: trans) }
  moreover
  { fix s t u assume "(t, u) \<in> ordstep {\<succ>} (E\<^sup>\<leftrightarrow>)" and "(s, t) \<in> R"
    then have "s \<succ> u" by (cases) (auto dest: trans ctxt) }
  ultimately show ?thesis by (cases) (fastforce simp: ostep_def)+
qed

lemma oKB_rtrancl_less:
  assumes "oKB\<^sup>*\<^sup>* (E, R) (E', R')" and "R \<subseteq> {\<succ>}"
  shows "R' \<subseteq> {\<succ>}"
  using assms by (induct "(E, R)" "(E', R')" arbitrary: E' R') (auto dest!: oKB_less)

lemma oKB_E:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "E \<subseteq> Id \<union> E' \<union> R'\<^sup>\<leftrightarrow> \<union> (ostep E' R') O E' \<union> E' O (ostep E' R')\<inverse>"
  using assms
proof (cases)
  case (simplifyl s u t)
  then have "(s, u) \<in> ostep E' R'"
    by (intro ostep_mono [THEN subsetD, OF _ _ simplifyl(3)]) auto
  then have "(s, t) \<in> (ostep E' R') O E'" using simplifyl by auto
  then show ?thesis using simplifyl by auto
next
  case (simplifyr t u s)
  then have "(t, u) \<in> ostep E' R'"
    by (intro ostep_mono [THEN subsetD, OF _ _ simplifyr(3)]) auto
  then have "(s, t) \<in> E' O (ostep E' R')\<inverse>" using simplifyr by blast
  then show ?thesis using simplifyr by blast
qed auto

lemma oKB_E_rev:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "E' \<subseteq> E \<union> (rstep (R \<union> E\<^sup>\<leftrightarrow>))\<inverse> O (rstep (R \<union> E\<^sup>\<leftrightarrow>)) \<union> (ostep E R)\<inverse> O E \<union> E O (ostep E R)"
  using assms
proof (cases)
  case (simplifyl s u t)
  have "(s, u) \<in> ostep E R"  by (intro ostep_mono [THEN subsetD, OF _ _ simplifyl(3)]) auto
  with simplifyl(4) have "(u, t) \<in> (ostep E R)\<inverse> O E" by auto
  then show ?thesis using simplifyl by auto
next
  case (simplifyr t u s)
  have "(t, u) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ simplifyr(3)]) auto
  with simplifyr(4) have "(s, u) \<in> E O (ostep E R)" by auto
  then show ?thesis using simplifyr by auto
next
  case (deduce u s t)
  then have "(s, t) \<in> (rstep (R \<union> E\<^sup>\<leftrightarrow>))\<inverse> O (rstep (R \<union> E\<^sup>\<leftrightarrow>))" by blast
  with deduce show ?thesis by auto
next
  case (collapse t u s)
  have "(t, u) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ collapse(3)]) auto
  from ostep_imp_rstep_sym [OF this] subsetD [OF rstep_mono, OF Un_upper1 rstep_rule [OF collapse(4)]]
  have "(u, s) \<in> (rstep (R \<union> E\<^sup>\<leftrightarrow>))\<inverse> O (rstep (R \<union> E\<^sup>\<leftrightarrow>))" by blast
  with collapse show ?thesis by auto
qed auto

lemma oKB_R:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "R \<subseteq> R' \<union> R' O (ostep E' R')\<inverse> \<union> ostep E' R' O E'"
  using assms
proof (cases)
  case (compose t u s)
  then have "(t, u) \<in> ostep E' R'"
    by (intro ostep_mono [THEN subsetD, OF _ _ compose(3)]) auto
  then have "(s, t) \<in> R' O (ostep E' R')\<inverse>" using compose by blast
  then show ?thesis using compose by blast
next
  case (collapse t u s)
  then have "(t, u) \<in> ostep E' R'"
    by (intro ostep_mono [THEN subsetD, OF _ _ collapse(3)]) auto
  then have "(t, s) \<in> ostep E' R' O E'" using collapse by auto
  then show ?thesis using collapse by blast
qed auto

lemma oKB_R_rev:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "R' \<subseteq> R \<union> E\<^sup>\<leftrightarrow> \<union> R O (ostep E R)"
  using assms
proof (cases)
  case (compose s t u)
  have "(s, t) \<in> ostep E R"
    by (intro ostep_mono [THEN subsetD, OF _ _ compose(3)]) auto
  with compose show ?thesis by fast
qed auto

lemma conversion2:
  "(x, y) \<in> r\<^sup>\<leftrightarrow> \<Longrightarrow> (y, z) \<in> r\<^sup>\<leftrightarrow> \<Longrightarrow> (x, z) \<in> r\<^sup>\<leftrightarrow>\<^sup>*"
  by (auto simp: conversion_def intro: rtrancl_trans)

lemma oKB_rstep_subset:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "rstep (E \<union> R) \<subseteq> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
  apply (auto elim!: rstepE dest!: oKB_E [OF oKB, THEN subsetD] oKB_R [OF oKB, THEN subsetD])
     apply (auto  dest!: ostep_imp_rstep_sym)
     apply (rule_tac y = "C\<langle>y \<cdot> \<sigma>\<rangle>" in conversion2; fast)+
  done

lemma oKB_conversion_subset:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "(rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using conversion_mono [OF oKB_rstep_subset [OF assms]] by simp

lemma oKB_rtrancl_conversion_subset:
  assumes "oKB\<^sup>*\<^sup>* (E, R) (E', R')"
  shows "(rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
  by (induct "(E, R)" "(E', R')" arbitrary: E' R')
    (force dest!: oKB_conversion_subset)+

lemma oKB_rstep_subset_rev:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "rstep (E' \<union> R') \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  let ?RE = "R \<union> E\<^sup>\<leftrightarrow>" 
  let ?RES = "(rstep ?RE)\<^sup>\<leftrightarrow>" 
  from oKB_R_rev[OF oKB] oKB_E_rev[OF oKB] ostep_imp_rstep_sym
  have "E' \<union> R' \<subseteq> ?RE \<union> (rstep ?RE)\<inverse> O rstep ?RE \<union> (ostep E R)\<inverse> O ?RE \<union> ?RE O ostep E R" by auto
  also have "\<dots> \<subseteq> rstep ?RE \<union> (rstep ?RE)\<inverse> O rstep ?RE \<union> rstep ?RE O rstep ?RE" 
    using ostep_imp_rstep_sym[of _ _ E R] by force
  also have "\<dots> \<subseteq> ?RES\<^sup>*" by regexp
  finally have "E' \<union> R' \<subseteq> ?RES\<^sup>*" .
  from rstep_mono[OF this]
  have "rstep (E' \<union> R') \<subseteq> rstep (?RES^*)" .
  also have "\<dots> = (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def
    by (metis rstep_rtrancl_idemp rstep_simps(5) sup_commute symcl_Un symcl_idemp)
  finally show ?thesis .
qed

lemma oKB_conversion_supset:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "(rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  using conversion_mono [OF oKB_rstep_subset_rev [OF assms]] by simp


section \<open>Abstract ordered completion according to proof for FSCD'17\<close>

inductive_set encstep1 for E :: "('a, 'b) trs" and R :: "('a, 'b) trs"
  where
    estep: "(l, r) \<in> E\<^sup>\<leftrightarrow> \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma> \<Longrightarrow> l \<lhd>\<cdot> s \<Longrightarrow> (s, t) \<in> encstep1 E R"
  | rstep: "(s, t) \<in> rstep R \<Longrightarrow> (s, t) \<in> encstep1 E R"

inductive_set encstep2 for E :: "('a, 'b) trs" and R :: "('a, 'b) trs"
  where
    estep: "(l, r) \<in> E\<^sup>\<leftrightarrow> \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma> \<Longrightarrow> l \<lhd>\<cdot> s \<Longrightarrow> (s, t) \<in> encstep2 E R"
  | rstep: "(l, r) \<in> R \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> l \<lhd>\<cdot> s \<Longrightarrow> (s, t) \<in> encstep2 E R"

lemma encstep1_less:
  assumes "(s, t) \<in> encstep1 E R" and "R \<subseteq> {\<succ>}"
  shows "s \<succ> t"
  using assms(1)
by (cases, insert compatible_rstep_imp_less [OF assms(2)] ctxt, blast+)

inductive oKBi ::
    "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> bool" (infix "\<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>" 55)
  where
    deduce: "(s, t) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, u) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E \<union> {(t, u)}, R)" |
    orientl: "s \<succ> t \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E - {(s, t)}, R \<union> {(s, t)})" |
    orientr: "t \<succ> s \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E - {(s, t)}, R \<union> {(t, s)})" |
    delete: "(s, s) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E - {(s, s)}, R)" |
    compose: "(t, u) \<in> ostep E (R - {(s, t)}) \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E, (R - {(s, t)}) \<union> {(s, u)})" |
    simplifyl: "(s, u) \<in> encstep1 (E - {(s, t)}) R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> ((E - {(s, t)}) \<union> {(u, t)}, R)" |
    simplifyr: "(t, u) \<in> encstep1 (E - {(s, t)}) R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> ((E - {(s, t)}) \<union> {(s, u)}, R)" |
    collapse: "(t, u) \<in> encstep2 E (R - {(t, s)}) \<Longrightarrow> (t, s) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E \<union> {(u, s)}, R - {(t, s)})"

lemma encstep2_encstep1:
  assumes "(s, t) \<in> encstep2 E R"
  shows "(s, t) \<in> encstep1 E R"
  unfolding encstep1.simps using assms by (cases) auto

lemma encstep1_ostep:
  assumes "(s, t) \<in> encstep1 E R"
  shows "(s, t) \<in> ostep E R"
  using assms
proof (cases)
  case (estep l r C \<sigma>)
  then show ?thesis unfolding ostep_def using ordstep.simps by fast
next
  case rstep
  then show ?thesis unfolding ostep_def rstep_def by fast
qed

lemma encstep2_ostep: "(s, t) \<in> encstep2 E R \<Longrightarrow> (s, t) \<in> ostep E R"
  using encstep2_encstep1 encstep1_ostep by blast

lemma encstep1_mono:
  "E \<subseteq> E' \<Longrightarrow> R \<subseteq> R'\<Longrightarrow> encstep1 E R \<subseteq> encstep1 E' R'"
  using rstep_mono [of R R']
  by (auto elim!: encstep1.cases intro: encstep1.intros)

lemma encstep2_mono:
  "E \<subseteq> E' \<Longrightarrow> R \<subseteq> R'\<Longrightarrow> encstep2 E R \<subseteq> encstep2 E' R'"
  by (auto elim!: encstep2.cases intro: encstep2.intros)

lemma encstep1_imp_rstep_sym:
  "(s, t) \<in> encstep1 E R \<Longrightarrow> (s, t) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>)"
  using encstep1_ostep ostep_imp_rstep_sym by force

lemma encstep2_imp_rstep_sym:
  "(s, t) \<in> encstep2 E R \<Longrightarrow> (s, t) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>)"
  using encstep2_ostep ostep_imp_rstep_sym by force

lemma oKBi_oKB:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  using assms
proof (cases)
  case (simplifyl s u t)
  then show ?thesis using oKB.simplifyl and encstep1_ostep by blast
next
  case (simplifyr t u s)
  then show ?thesis using oKB.simplifyr and encstep1_ostep by blast
next
  case (collapse t u s)
  then show ?thesis using oKB.collapse encstep2_ostep [OF collapse(3)] by blast
qed (blast intro: oKB.intros)+

lemma oKBi_subset:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "E' \<union> R' \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  using oKBi_oKB [OF assms] and oKB_rstep_subset_rev subset_rstep [of "E' \<union> R'"] by blast

lemma oKBi_rstep_subset:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "rstep(E' \<union> R') \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  using oKBi_oKB [OF assms] and oKB_rstep_subset_rev subset_rstep [of "E' \<union> R'"] by blast

lemma oKBi_conversion_subset:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "(rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>*"
  using oKBi_rstep_subset [OF assms] and conversion_mono and conversion_conversion_idemp by metis

lemma oKBi_E_supset:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "E - E' \<subseteq> (encstep1 E' R' O E'\<^sup>\<leftrightarrow>)\<^sup>\<leftrightarrow> \<union> R'\<^sup>\<leftrightarrow> \<union> Id"
  using assms by (cases) (use encstep1_mono [of "E - {(s, t)}" E' R R' for s t] in blast)+

lemma oKBi_E_supset':
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "E - E' \<subseteq> (encstep1 E' R' O E') \<union> (E' O (encstep1 E' R')\<inverse>) \<union> R'\<^sup>\<leftrightarrow> \<union> Id"
  using assms by (cases) (use encstep1_mono [of "E - {(s, t)}" E' R R' for s t] in blast)+

lemma oKBi_R_supset:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "R - R' \<subseteq> encstep2 E' R' O E' \<union> R' O (ostep E' R')\<inverse>"
  using assms
proof (cases)
  case (compose s t u)
  then have "(s, t) \<in> ostep E' R'"
    using ostep_mono [of E' E "R - {(u, s)}" R'] by auto
  with compose show ?thesis by fast
next
  case (collapse s t u)
  with encstep2_mono [of E "E \<union> {(t, u)}"] show ?thesis by fast
qed auto

lemma oKBi_supset:
  assumes step: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "E \<union> R \<subseteq> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms subset_rstep encstep1_imp_rstep_sym encstep2_imp_rstep_sym
  by (smt Diff_partition oKB_rstep_subset oKBi_oKB ordered_completion_axioms sup.boundedE)

lemma oKBi_rstep_supset:
  assumes step: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "rstep(E \<union> R) \<subseteq> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using oKBi_supset [OF assms]
  by (simp add: step oKB_rstep_subset oKBi_oKB ordered_completion_axioms)

lemma oKBi_conversion_supset:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "(rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using oKBi_rstep_supset [OF assms] and conversion_mono and conversion_conversion_idemp by metis

lemma oKBi_conversion:
  assumes oKB: "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "(rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms and oKBi_conversion_supset and oKBi_conversion_subset by blast

lemma oKBi_less:
  assumes "R \<subseteq> {\<succ>}" and "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  shows "R' \<subseteq> {\<succ>}"
  using assms(1) and oKBi_oKB [OF assms(2)] and oKB_less by auto

lemma oKBi_rtrancl_less:
  assumes "oKBi\<^sup>*\<^sup>* (E, R) (E', R')" and "R \<subseteq> {\<succ>}"
  shows "R' \<subseteq> {\<succ>}"
  using assms oKB_less
proof (induct "(E, R)" "(E', R')" arbitrary: E' R')
  case rtrancl_refl
  then show ?case by fast
next
  case (rtrancl_into_rtrancl S)
  obtain E2 R2 where S: "S = (E2, R2)" by force
  from rtrancl_into_rtrancl show ?case using oKBi_less unfolding S by metis
qed

end

locale okb_irun = ordered_completion +
  fixes R E
  assumes R0: "R 0 = {}"
    and irun: "\<And>i. (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E (Suc i), R (Suc i))"
begin

sublocale kb less enc ..

abbreviation Rinf ("R\<^sub>\<infinity>") where "R\<^sub>\<infinity> \<equiv> (\<Union>i. R i)"
abbreviation Einf ("E\<^sub>\<infinity>") where "E\<^sub>\<infinity> \<equiv> (\<Union>i. E i)"

definition "R\<^sub>\<omega> = (\<Union>i. \<Inter>j\<in>{j. j\<ge>i}. R j)"
definition "E\<^sub>\<omega> = (\<Union>i. \<Inter>j\<in>{j. j\<ge>i}. E j)"

lemma Rw_subset_Rinf: "R\<^sub>\<omega> \<subseteq> R\<^sub>\<infinity>"
  by (auto simp: R\<^sub>\<omega>_def)

lemma Ew_subset_Einf: "E\<^sub>\<omega> \<subseteq> E\<^sub>\<infinity>"
  by (auto simp: E\<^sub>\<omega>_def)

lemma oKBi_rtrancl_i: "oKBi\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)"
  using irun by (induct i) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma oKBi_conversion_ERi: "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E i \<union> R i))\<^sup>\<leftrightarrow>\<^sup>*"
  using irun and oKBi_conversion and R0 by (induct i) auto 

lemma oKBi_conversion_ERinf: "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>))\<^sup>\<leftrightarrow>\<^sup>*"
proof
  show "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>))\<^sup>\<leftrightarrow>\<^sup>*"
    using oKBi_conversion_ERi conversion_mono unfolding rstep_union
    by (metis (no_types, lifting) Sup_upper range_eqI rstep_mono subset_trans sup.cobounded1)
next
  have "rstep (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>) \<subseteq> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*"
  proof
    fix s t
    assume "(s,t) \<in> rstep (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>)"
    then obtain i where "(s,t) \<in> rstep (E i \<union> R i)" by fast
    with oKBi_conversion_ERi show "(s,t) \<in> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  qed
  then show "(rstep (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def
    by (metis converse_mono conversion_converse conversion_def le_supI rtrancl_subset_rtrancl)
qed

lemma Ri_less: "R i \<subseteq> {\<succ>}"
  using oKBi_rtrancl_less [OF oKBi_rtrancl_i] and R0 by auto

lemma Rinf_less: "R\<^sub>\<infinity> \<subseteq> {\<succ>}"
  using Ri_less by auto

lemma Rw_less: "R\<^sub>\<omega> \<subseteq> {\<succ>}"
  unfolding R\<^sub>\<omega>_def by (use Ri_less in auto)

lemma encstep2D:
  assumes "(s, t) \<in> encstep2 E\<^sub>\<infinity> R\<^sub>\<infinity>"
  shows "\<exists>C \<tau> l r. (l, r) \<in> R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow> \<and> s = C\<langle>l \<cdot> \<tau>\<rangle> \<and> t = C\<langle>r \<cdot> \<tau>\<rangle> \<and> l \<cdot> \<tau> \<succ> r \<cdot> \<tau> \<and> l \<lhd>\<cdot> s"
  using assms
proof (cases)
  case (estep l r C \<sigma>)
  then show ?thesis by blast
next
  case (rstep l r C \<sigma>)
  from rstep(1) and Ri_less and subst [of l r] have "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" by auto
  with rstep show ?thesis by blast
qed

lemma encstep1_lessenc:
  assumes "(s, t) \<in> encstep1 (E i) (R i)"
  shows "s \<cdot>\<succ> t"
  using assms encstep1_less[OF assms Ri_less] unfolding lessencp_def by fast

definition Sw ("S\<^sub>\<omega>") where "S\<^sub>\<omega> \<equiv> R\<^sub>\<omega> \<union> {(s \<cdot> \<sigma>, t \<cdot> \<sigma>) | s t \<sigma>. (s, t) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<and> s \<cdot> \<sigma> \<succ> t \<cdot> \<sigma>}"
  
lemma Sw_less: "S\<^sub>\<omega> \<subseteq> {\<succ>}"
  using Ri_less unfolding Sw_def R\<^sub>\<omega>_def by fast
  
lemma Sw_step_less: "rstep S\<^sub>\<omega> \<subseteq> {\<succ>}"
  using compatible_rstep_imp_less[OF Sw_less] by auto
    
lemma Sw_implies_REw: "rstep S\<^sub>\<omega> \<subseteq> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>"
proof -
  have "S\<^sub>\<omega> \<subseteq> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>" 
    unfolding rstep_simps(5)[symmetric]
    unfolding Sw_def by fastforce
  from rstep_mono[OF this] show ?thesis by (simp add: rstep_rstep rstep_simps(5))
qed
 

lemma SN_Sw_step: "SN (rstep S\<^sub>\<omega>)"
  using Sw_step_less SN_subset [OF SN_less] by fastforce
    
lemma rstep_imp_mstep:
  assumes "(t, u) \<in> rstep RR" and "\<exists>t' \<in># S. t' \<succeq> t" and "\<exists>u' \<in># S. u' \<succeq> u"
  shows "(t, u) \<in> mstep S RR"
  using assms by (auto simp: mstep_iff dest: trans)
    
lemma mstep_succeq_mono:
  assumes "\<forall>m \<in># M. \<exists>n \<in># N. n \<succeq> m"
  shows "mstep M RR \<subseteq> mstep N RR"
proof
  fix s t
  assume mstep: "(s, t) \<in> mstep M RR"
  with assms trans show "(s, t) \<in> mstep N RR" unfolding mstep_def mem_Collect_eq split
    by (smt sup2E sup2I1)
qed

lemma msteps_succeq_mono:
  assumes "\<forall>m \<in># M. \<exists>n \<in># N. n \<succeq> m"
  shows "(mstep M RR)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (mstep N RR)\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule mstep_succeq_mono [OF assms, THEN conversion_mono])

lemma mstep_subst_ctxt:
  assumes "(s, t) \<in> mstep S RR"
  shows "(C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> mstep {#C\<langle>u \<cdot> \<sigma>\<rangle>. u \<in># S #} RR"
proof -
  let ?S = "{#C\<langle>u \<cdot> \<sigma>\<rangle>. u \<in># S #}"
  from assms have step: "(C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> rstep RR" unfolding mstep_def by auto
  from assms have gt:"\<exists>s' \<in># S. s' \<succeq> s" "\<exists>t' \<in># S. t' \<succeq> t" unfolding mstep_def by auto
  with subst ctxt have s':"\<exists>s' \<in># ?S. s' \<succeq> C\<langle>s \<cdot> \<sigma>\<rangle>" by fast
  from gt(2) subst ctxt have "\<exists>t' \<in># ?S. t' \<succeq> C\<langle>t \<cdot> \<sigma>\<rangle>" by fast
  with step s' show ?thesis unfolding mstep_def by blast
qed

lemma msteps_subst_ctxt:
  assumes "(s, t) \<in> (mstep S RR)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> (mstep {#C\<langle>u \<cdot> \<sigma>\<rangle>. u \<in># S #} RR)\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  let ?S = "{#C\<langle>u \<cdot> \<sigma>\<rangle>. u \<in># S #}"
  from mstep_subst_ctxt have x: "\<And> s t. (s, t) \<in> (mstep S RR)\<^sup>\<leftrightarrow> \<Longrightarrow> (C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> (mstep ?S RR)\<^sup>\<leftrightarrow>" by auto
  from assms rtrancl_imp_relpow obtain n where "(s, t) \<in> (mstep S RR)\<^sup>\<leftrightarrow> ^^ n" by fast
  then have "(C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> (mstep ?S RR)\<^sup>\<leftrightarrow> ^^ n"
  proof (induct n arbitrary: s)
    case (Suc n)
    then obtain s' where s': "(s, s') \<in> (mstep S RR)\<^sup>\<leftrightarrow>" "(s', t) \<in> (mstep S RR)\<^sup>\<leftrightarrow> ^^ n"
      unfolding relpow_Suc by blast
    from x [OF s'(1)] Suc(1) [OF s'(2)] show ?case unfolding relpow_Suc by blast
  qed simp
  with relpow_imp_rtrancl show ?thesis by blast
qed

lemma Einf_without_Ew:
  assumes "(l,r) \<in> E\<^sub>\<infinity>" and "(l,r) \<notin>  E\<^sub>\<omega>"
  shows "\<exists>j. (l, r) \<in> (E j) \<and> (l, r) \<notin> (E (Suc j))"
proof-
  from assms obtain j where "(l, r) \<in> E j" and "\<exists>i>j. (l, r) \<notin> E i"
    unfolding E\<^sub>\<omega>_def le_eq_less_or_eq by blast
  moreover define i where "i = (LEAST i. i > j \<and> (l, r) \<notin> E i)"
  ultimately have "i > j" and not_i: "(l, r) \<notin> E i" by (metis (lifting) LeastI)+
  then have "i - 1 < i" and [simp]: "Suc (i - Suc 0) = i" by auto
  from not_less_Least [OF this(1) [unfolded i_def], folded i_def] and \<open>i > j\<close> and \<open>(l, r) \<in> E j\<close>
  have pred_i: "(l, r) \<in> E (i - 1)" by (cases "i = Suc j") auto
  have i_simp: "Suc (i - 1) = i" by auto
  show ?thesis by (rule exI[of _ "i - 1"], insert not_i pred_i i_simp, auto)
qed

lemma Rinf_without_Rw:
  assumes "(l,r) \<in> R\<^sub>\<infinity>" and "(l,r) \<notin>  R\<^sub>\<omega>"
  shows "\<exists>j. (l, r) \<in> (R j) \<and> (l, r) \<notin> (R (Suc j))"
proof-
  from assms obtain j where "(l, r) \<in> R j" and "\<exists>i>j. (l, r) \<notin> R i"
    unfolding R\<^sub>\<omega>_def le_eq_less_or_eq by blast
  moreover define i where "i = (LEAST i. i > j \<and> (l, r) \<notin> R i)"
  ultimately have "i > j" and not_i: "(l, r) \<notin> R i" by (metis (lifting) LeastI)+
  then have "i - 1 < i" and [simp]: "Suc (i - Suc 0) = i" by auto
  from not_less_Least [OF this(1) [unfolded i_def], folded i_def] and \<open>i > j\<close> and \<open>(l, r) \<in> R j\<close>
  have pred_i: "(l, r) \<in> R (i - 1)" by (cases "i = Suc j") auto
  have i_simp: "Suc (i - 1) = i" by auto
  show ?thesis by (rule exI[of _ "i - 1"], insert not_i pred_i i_simp, auto)
qed
  
lemma Ei_subset_EwRi: "mstep S E\<^sub>\<infinity> \<subseteq> (mstep S (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  { fix t0 u0
    assume "(t0, u0) \<in> rstep E\<^sub>\<infinity>" and St: "\<exists>s \<in># S. s \<succeq> t0" and Su: "\<exists>s \<in># S. s \<succeq> u0"
    with rstep_imp_C_s_r [OF this(1)] obtain C \<sigma> t u
      where Cs: "t0 = C\<langle>t \<cdot> \<sigma>\<rangle>" "u0 = C\<langle>u \<cdot> \<sigma>\<rangle>" and tu: "(t, u) \<in> E\<^sub>\<infinity>" by blast
    from tu St Su have "(C\<langle>t \<cdot> \<sigma>\<rangle>, C\<langle>u \<cdot> \<sigma>\<rangle>) \<in> (mstep S (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding Cs
    proof (induct "{#t, u#}" arbitrary: t u S C \<sigma> rule: SN_induct [OF lessenc_op.SN])
      case 1
      note sc = this
      let ?t = "C\<langle>t \<cdot> \<sigma>\<rangle>" and ?u = "C\<langle>u \<cdot> \<sigma>\<rangle>"
      have comm: "\<And>t u. {#t, u#} =  {#u, t#}" using add_mset_commute by auto
      note r_imp_msteps = rstep_imp_mstep [OF _ sc(4) sc(3)] rstep_imp_mstep [OF _ sc(3) sc(4)]
      show ?case
      proof (cases "(?t, ?u) \<in> rstep E\<^sub>\<omega>")
        case True
        with r_imp_msteps mstep_Un [of _ "R\<^sub>\<infinity>" "E\<^sub>\<omega>"] show ?thesis by auto
      next
        case False
        with rstep_imp_C_s_r have "(t, u) \<notin> E\<^sub>\<omega>" by auto
        from Einf_without_Ew[OF sc(2) this]  obtain i where
          pred_i:"(t, u) \<in> E i" and not_i: "(t, u) \<notin> E (Suc i)" by auto
        let ?enc = "encstep1 (E (Suc i)) (R (Suc i)) O (E (Suc i))\<^sup>\<leftrightarrow>"
        from pred_i oKBi_E_supset [OF irun [of i]] and not_i
        consider "(t, u) \<in> (R (Suc i))\<^sup>\<leftrightarrow>" | "u = t" | "(t, u) \<in> ?enc\<^sup>\<leftrightarrow>" by auto blast
        then show ?thesis
        proof (cases)
          case 1
          then have "(?t, ?u) \<in> rstep (R\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" by auto
          with r_imp_msteps [of "R\<^sub>\<infinity>"] converse_iff
          have "(?t, ?u) \<in> (mstep S R\<^sub>\<infinity>) \<or> (?u, ?t) \<in> (mstep S R\<^sub>\<infinity>)"
            using 1 by auto
          with mstep_Un conversion_inv show ?thesis by blast
        next
          case 3
          then have "(t, u) \<in> ?enc \<or> (u, t) \<in> ?enc" by auto
          with sc obtain t' u' where tu': "(t', u') \<in> ?enc" "(t=t' \<and> u=u') \<or> (t=u' \<and> u=t')" by blast
          then have tu_tu': "{# t, u #} = {# t', u' #}" by force
          from sc(3) sc(4) tu'(2) trans have Stu: "\<exists>s \<in># S. s \<succeq> C\<langle>u' \<cdot> \<sigma>\<rangle> \<and> (\<exists>s \<in># S. s \<succeq> C\<langle>t' \<cdot> \<sigma>\<rangle>)" by meson
          from tu'(1) obtain v where
            v: "(t', v) \<in> encstep1 (E (Suc i)) (R (Suc i))" "(v, u') \<in> (E (Suc i))\<^sup>\<leftrightarrow>" by auto
          from tu_tu' mset_two [OF encstep1_lessenc [OF v(1)]]
          have dec: "({# t, u #}, {# v, u' #}) \<in> mulless" by auto
          then have dec': "({# t, u #}, {# u', v #}) \<in> mulless" using add_mset_commute by metis
          from encstep1_ostep [OF v(1), THEN ostep_imp_less [OF Ri_less]] have tv: "t' \<succeq> v" by blast
          have vu: "(C\<langle>v\<cdot> \<sigma>\<rangle>, C\<langle>u'\<cdot> \<sigma>\<rangle>) \<in> (mstep S (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
          proof -
            from trans subst ctxt tv Stu have Sv: "\<exists>s \<in># S. s \<succeq> C\<langle>v\<cdot> \<sigma>\<rangle>" by fast
            from v(2) have "(v, u') \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" by auto
            with sc(1) [OF dec] sc(1) [OF dec'] Sv Stu show ?thesis
              unfolding Un_iff conversion_inv by blast
          qed
          from v(1) have "(C\<langle>t' \<cdot> \<sigma>\<rangle>, C\<langle>v \<cdot> \<sigma>\<rangle>) \<in> (mstep S (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
          proof (cases)
            case (estep l r D \<tau>)
            then have lr: "(l, r) \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" by auto
            with encompeq.intros [of t' D "l \<cdot> \<tau>" Var] estep(2) have tl: "l \<cdot> \<tau> \<unlhd>\<cdot> t'" by auto
            with encompeq.intros [of "r \<cdot> \<tau>" \<box>] estep(2) have "r \<unlhd>\<cdot> r \<cdot> \<tau>" by auto
            with estep(4) tl have tr: "t' \<cdot>\<succ> r" unfolding lessencp_def by blast
            from estep(5) have "t' \<cdot>\<succ> l" unfolding lessencp_def by blast
            with tr ns_s_mul_ext_union_multiset_l [OF ns_mul_ext_bottom [of "{#u'#}"], of _ "{#l, r#}"]
            have "({#u', t'#}, {#l, r#}) \<in> mulless" using multi_member_last by auto
            with tu_tu' have dec: "({#t, u#}, {#l, r#}) \<in> mulless" using comm by metis
            with comm [of l] have dec': "({#t, u#}, {#r, l#}) \<in> mulless" by presburger
            note ih = sc(1) [OF dec, of "{#l, r#}" \<box> Var] sc(1) [OF dec', of "{#l, r#}" \<box> Var]
            from lr [unfolded Un_iff] ih have "(l, r) \<in> (mstep {#l, r#} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
              unfolding conversion_inv [of r] ctxt.cop_nil subst_apply_term_empty by force
            from msteps_subst_ctxt [OF this] estep(2) estep(3)
            have mstep: "(t', v) \<in> (mstep {#t', v#} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
            from Stu tv trans ctxt [OF subst] have "\<exists>s\<in>#S. s \<succeq> C\<langle>v \<cdot> \<sigma>\<rangle>" by fast
            with Stu tv have S:"\<forall>m\<in>#{#C\<langle>t' \<cdot> \<sigma>\<rangle>, C\<langle>v \<cdot> \<sigma>\<rangle>#}. \<exists>n\<in>#S. n \<succeq> m" by auto
            have mset:"{#C\<langle>u \<cdot> \<sigma>\<rangle>. u \<in># {#t', v#}#} = {#C\<langle>t' \<cdot> \<sigma>\<rangle>, C\<langle>v \<cdot> \<sigma>\<rangle>#}" by simp
            with msteps_subst_ctxt [OF mstep, of C \<sigma>] conversion_mono [OF mstep_succeq_mono [OF S]]
              show ?thesis unfolding mset by blast
          next
            case rstep
            with rstep_subset_less [OF Ri_less] have tv': "t' \<succ> v" by blast
            from rstep have "(t', v) \<in> rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>)" by force
            from rstep_imp_mstep [OF this] tv'  have "(t', v) \<in> mstep {#t', t'#} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>)" by auto
            from mstep_subst_ctxt [OF this, of C \<sigma>] mstep_succeq_mono [of "{#C\<langle>t' \<cdot> \<sigma>\<rangle>, C\<langle>t' \<cdot> \<sigma>\<rangle>#}" S] Stu
            show ?thesis by fastforce
          qed
          from transD [OF conversion_trans, OF this vu] tu'(2) symD [OF conversion_sym]
          show ?thesis by metis
        qed auto
      qed
    qed
    with Cs have "(t0, u0) \<in> (mstep S (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  }
  then show ?thesis unfolding mstep_def by blast
qed

lemma Einf_sym_mstep: "mstep S (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>) \<subseteq> (mstep S (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  have inv: "mstep S (E\<^sub>\<infinity>\<inverse>) = (mstep S E\<^sub>\<infinity>)\<inverse>"
    unfolding mstep_def rstep_converse converse_iff by auto
  from Ei_subset_EwRi show ?thesis unfolding mstep_Un inv Un_subset_iff
    by (metis converse_mono conversion_converse)
qed

abbreviation "lexless \<equiv> lex_two {\<cdot>\<succ>} Id {\<cdot>\<succ>}"

lemma SN_lexless: "SN lexless"
  using SN_lessenc
  by (intro lex_two) (auto simp only: SN_trancl_SN_conv intro: SN_encomp_Un_less_relto_encompeq)

lemma Ri_subset_ERw: "mstep S R\<^sub>\<infinity> \<subseteq> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  { fix t u
    assume "(t, u) \<in> rstep R\<^sub>\<infinity>" and St: "\<exists>s \<in># S. s \<succeq> t" and Su: "\<exists>s \<in># S. s \<succeq> u"
    with rstep_imp_C_s_r [OF this(1)] obtain C \<sigma> l r
      where Cs: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" "u = C\<langle>r \<cdot> \<sigma>\<rangle>" and tu: "(l, r) \<in> R\<^sub>\<infinity>" by blast
    from tu St Su have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding Cs
    proof (induct "(l, r)" arbitrary: l r S C \<sigma> rule: SN_induct [OF SN_lexless])
      case 1
      note sc = this
      with Ri_less have lr: "l \<succ> r" by auto
      let ?t = "C\<langle>l \<cdot> \<sigma>\<rangle>" and ?u = "C\<langle>r \<cdot> \<sigma>\<rangle>"
      show ?case
      proof (cases "(l, r) \<in> R\<^sub>\<omega>")
        case True
          (* rule l \<rightarrow> r is persistent *)
        then have "(?t, ?u) \<in> rstep R\<^sub>\<omega>" by auto
        with rstep_imp_mstep [OF this sc(3) sc(4)] mstep_Un show ?thesis by auto
      next
        case False
        (* rule l \<rightarrow> r was removed in step (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E (i+1), R (i+1)) *)
        from Rinf_without_Rw[OF sc(2) False] obtain i where
          pred_i: "(l, r) \<in> R i" and not_i: "(l, r) \<notin> R (Suc i)" by auto
        (* first verify that (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>) conversion below l corresponds to a (R\<^sub>\<omega> \<union> E\<^sub>\<omega>) conversion *)
        { fix S'
          assume below_l: "\<forall> s' \<in># S'. l \<cdot>\<succ> s'"
          { fix s t
            assume "(s, t) \<in> mstep S' R\<^sub>\<infinity>"
            then have mstep: "(s, t) \<in> rstep R\<^sub>\<infinity>" "\<exists>s' \<in># S'. s' \<succeq> s" "\<exists>s' \<in># S'. s' \<succeq> t"
              unfolding mstep_def by auto
            then obtain C \<sigma> l1 r1 where l1r1: "s = C\<langle>l1 \<cdot> \<sigma>\<rangle>" "t = C\<langle>r1 \<cdot> \<sigma>\<rangle>" "(l1, r1) \<in> R\<^sub>\<infinity>" by fast
            from mstep obtain s' where s': "s' \<in># S'" "s' \<cdot>\<succeq> s" unfolding leqencp_def by blast
            from l1r1 encompeq.intros have sl1: "s \<cdot>\<unrhd> l1" by auto
            from s' below_l have ls': "l \<cdot>\<succ> s'" by auto
            with s' lessleqenc_compat1 have "l \<cdot>\<succ> s" by auto
            with sl1 lessenc_compat1 have "l \<cdot>\<succ> l1" by auto
            then have "((l, r), (l1, r1)) \<in> lexless" by force
            from sc(1) [OF this l1r1(3)] mstep have "(s, t) \<in> (mstep S' (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
              unfolding l1r1 by meson
          } note step = this
          from r_into_rtrancl have "mstep S' E\<^sub>\<omega> \<subseteq> (mstep S' E\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" by auto
          with step mstep_Un have "mstep S' (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>) \<subseteq> (mstep S' (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
          from conversion_mono [OF this] have R: "(mstep S' (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (mstep S' (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
            by simp
        } note mstep_Rinf_msteps_ERw = this
        (* derive equation (1): (R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>) steps below l correspond to a (R\<^sub>\<omega> \<union> E\<^sub>\<omega>) conversion *)
        { fix S'
          assume below_l: "\<forall> s' \<in># S'. l \<cdot>\<succ> s'"
          note R = mstep_Rinf_msteps_ERw [OF this]
          with Einf_sym_mstep have "mstep S' (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>) \<subseteq> (mstep S' (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
          with R mstep_Un have "mstep S' (R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>) \<subseteq> (mstep S' (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
          from conversion_mono [OF this] have "(mstep S' (R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (mstep S' (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
            by simp
        } note msteps_ERinf_mstep_Rw = this
        (* case distinction according to Lemma 31 *)
        let ?Ei = "E (Suc i)" and ?Ri = "R (Suc i)"
        from pred_i oKBi_R_supset [OF irun [of i]] and not_i
          consider "(l, r) \<in> encstep2 ?Ei ?Ri O ?Ei" | "(l, r) \<in> ?Ri O (ostep ?Ei ?Ri)\<inverse>" by blast
        then have "(l, r) \<in> (mstep {#l, r#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
        proof (cases)
          (* collapse step *)
          case 1
          then obtain u where u: "(l, u) \<in> encstep2 ?Ei ?Ri" "(u, r) \<in> ?Ei" by auto
          (* l \<longleftrightarrow>\<^sub>R\<^sub>\<omega> \<^sub>\<union> \<^sub>E\<^sub>\<omega>\<^sup>{\<^sup>l\<^sup>, \<^sup>r\<^sup>}\<^sup>* u *)
          with encstep2_mono [of ?Ei "E\<^sub>\<infinity>" ?Ri "R\<^sub>\<infinity>"] have lu: "(l, u) \<in> encstep2 E\<^sub>\<infinity> R\<^sub>\<infinity>" by auto
          from encstep2D [OF this] obtain D \<tau> l0 r0 where
            D: "(l0, r0) \<in> R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" "l = D\<langle>l0 \<cdot> \<tau>\<rangle>" "u = D\<langle>r0 \<cdot> \<tau>\<rangle>" " l0 \<cdot> \<tau> \<succ> r0 \<cdot> \<tau>" "l0 \<lhd>\<cdot> l" by blast
          then have l_l0: "l \<cdot>\<succ> l0" unfolding lessencp_def by auto
          from D encompeq.intros [of l D _ Var] have l_l0\<tau>: "l \<cdot>\<unrhd> l0 \<cdot> \<tau>" by auto
          from encompeq.intros [of _ \<box>] have "r0 \<cdot> \<tau> \<cdot>\<unrhd> r0" by auto
          with l_l0\<tau> D(4) have l_r0: "l \<cdot>\<succ> r0" unfolding lessencp_def by blast
          have "(l0, r0) \<in> (mstep {#l0, r0#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
          proof (cases "(l0, r0) \<in> R\<^sub>\<infinity>")
            case True
            with Ri_less have l_gt_r: "l0 \<succ> r0" by auto
            from l_l0 have "((l, r), (l0, r0)) \<in> lexless" by auto
            from sc(1) [OF this True, of "{#l0, r0#}" \<box> Var, simplified] l_gt_r show ?thesis by auto
          next
            case False
            with D(1) have "(l0, r0) \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" by auto
            then have "(l0, r0) \<in> mstep {#l0, r0#} (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" unfolding mstep_def by auto
            with in_mono [OF Einf_sym_mstep] have l0r0: "(l0, r0) \<in> (mstep {#l0, r0#} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
            from l_l0 l_r0 have "\<forall> s' \<in># {#l0, r0#}. l \<cdot>\<succ> s'" by auto
            from l0r0 mstep_Un mstep_Rinf_msteps_ERw [OF this] show ?thesis by auto
          qed
          from D msteps_subst_ctxt [OF this] have lu: "(l, u) \<in> (mstep {#l, u#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
          from u(1) encstep1_less [OF encstep2_encstep1 Ri_less] have l_succeq_u: "l \<succeq> u" by auto
          then have "\<forall>m\<in>#{#l, u#}. \<exists>n\<in>#{#l, r#}. n \<succeq> m" by auto
          from lu msteps_succeq_mono [OF this] have lu: "(l, u) \<in> (mstep {#l, r#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
              (* u \<longleftrightarrow>\<^sub>R\<^sub>\<omega> \<^sub>\<union> \<^sub>E\<^sub>\<omega>\<^sup>{\<^sup>l\<^sup>, \<^sup>r\<^sup>}\<^sup>* r *)
          from u(1) encstep1_lessenc [OF encstep2_encstep1] have "l \<cdot>\<succ> u" by auto
          with lr have lt_l: "\<forall> s' \<in># {#u, r#}. l \<cdot>\<succ> s'" unfolding lessencp_def by force
          from u(2) have "(u, r) \<in> mstep {#u, r#} (R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" unfolding mstep_def by auto
          from r_into_rtrancl [OF this] msteps_ERinf_mstep_Rw [OF lt_l]
          have ur: "(u, r) \<in> (mstep {#u, r#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
          from l_succeq_u have "\<forall>m\<in>#{#u, r#}. \<exists>n\<in>#{#l, r#}. n \<succeq> m" by auto
          from ur msteps_succeq_mono [OF this] have "(u, r) \<in> (mstep {#l, r#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
          with lu transD [OF conversion_trans] show ?thesis by auto
        next
          (* compose step *)
          case 2
          then obtain u where u: "(l, u) \<in> ?Ri" "(u, r) \<in> (ostep ?Ei ?Ri)\<inverse>" by auto
              (* l \<longleftrightarrow>\<^sub>R\<^sub>\<omega> \<^sub>\<union> \<^sub>E\<^sub>\<omega>\<^sup>{\<^sup>l\<^sup>, \<^sup>r\<^sup>}\<^sup>* u*)
          with ostep_imp_less [OF Ri_less] have ru: "r \<succ> u" by auto
          then have "r \<cdot>\<succ> u" unfolding lessencp_def by blast
          then have "((l, r), (l, u)) \<in> lexless" unfolding lex_two.simps mem_Collect_eq split by auto
          from trans [OF lr ru] sc(1) [OF this, of "{#l, r#}" \<box> Var, simplified] u(1)
          have lu: "(l, u) \<in> (mstep {#l, r#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
              (* u \<longleftrightarrow>\<^sub>R\<^sub>\<omega> \<^sub>\<union> \<^sub>E\<^sub>\<omega>\<^sup>{\<^sup>l\<^sup>, \<^sup>r\<^sup>}\<^sup>* r*)
          from ostep_imp_rstep_sym u(2) have "(r, u) \<in> rstep (?Ri \<union> ?Ei\<^sup>\<leftrightarrow>)" by auto
          with rstep_UN rstep_union have rstep: "(r, u) \<in> rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)"
            by (auto elim!: rstep.cases) blast
          from rstep have mstep: "(r, u) \<in> mstep {#u, r#} (R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)"
            unfolding mstep_def mem_Collect_eq split by auto
          from lr trans [OF lr ru] have lt_l: "\<forall> s' \<in># {#u, r#}. l \<cdot>\<succ> s'"
            unfolding lessencp_def by force
          from msteps_ERinf_mstep_Rw [OF this] r_into_rtrancl [OF mstep]
          have ur: "(u, r) \<in> (mstep {#u, r#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_inv [of u] by auto
          have "(u, r) \<in> (mstep {#l, r#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
            by(rule subsetD [OF msteps_succeq_mono], insert trans [OF lr ru] ur, auto)
          with lu transD [OF conversion_trans] show ?thesis by auto
        qed
        from msteps_subst_ctxt [OF this] have tu: "(?t, ?u) \<in> (mstep {#?t, ?u#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
        show ?thesis by(rule subsetD [OF msteps_succeq_mono], insert sc(3) sc(4) tu, auto)
      qed
    qed
    with Cs have "(t, u) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  }
  then show ?thesis using mstep_def by auto
qed

lemma RiEw_subset_ERw: "(mstep S (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from r_into_rtrancl have "mstep S E\<^sub>\<omega> \<subseteq> (mstep S E\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with Ri_subset_ERw mstep_Un have "mstep S (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>) \<subseteq> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  from conversion_mono [OF this] show ?thesis by auto
qed

lemma ERi_subset_ERw: "mstep S (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>) \<subseteq> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
  using Ei_subset_EwRi Ri_subset_ERw RiEw_subset_ERw unfolding mstep_Un [of _ "E\<^sub>\<infinity>"] by blast

lemma oKBi_conversion_ERw: "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof
  have "rstep (E 0) \<subseteq> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
  proof
    fix s t
    assume "(s, t) \<in> rstep (E 0)"
    with ERi_subset_ERw [of "{#s, t#}"] mstep_def have st: "(s, t) \<in> (mstep {#s, t#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by force
    have "mstep {#s, t#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>) \<subseteq> rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>)" using mstep_def by force
    from conversion_mono [OF this] st show "(s, t) \<in> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  qed
  from conversion_mono [OF this] show "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by simp
next
  have "rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>) \<subseteq> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*"
  proof
    fix s t
    assume "(s, t) \<in> rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>)"
    then obtain k where "(s, t) \<in> rstep (R k \<union> E k)" unfolding E\<^sub>\<omega>_def R\<^sub>\<omega>_def by blast
    with oKBi_conversion_ERi show "(s, t) \<in> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*" by blast
  qed
  from conversion_mono [OF this] show "(rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*" by simp
qed
end

locale okb_irun_nonfailing = okb_irun less
  for less :: "('a, 'b::infinite) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50) +
  assumes Ew_empty:"E\<^sub>\<omega> = {}"
  and fair:"PCP R\<^sub>\<omega> \<subseteq> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep R\<^sub>\<omega>)\<^sup>\<down>"
begin

lemma [simp]:"S\<^sub>\<omega> = R\<^sub>\<omega>" unfolding Ew_empty Sw_def by auto

lemma Ew_empty_implies_Rw_peak_decreasing:
  assumes "(s, t) \<in> slab R\<^sub>\<omega> s" and "(s, u) \<in> slab R\<^sub>\<omega> s"
  shows "(t, u) \<in> (\<Union> v \<in> {v. s \<succ> v}. slab R\<^sub>\<omega> v)\<^sup>\<leftrightarrow>\<^sup>*"
proof-
  from assms have rsteps: "(s, t) \<in> rstep R\<^sub>\<omega>" "(s, u) \<in> rstep R\<^sub>\<omega>" unfolding source_step_def by auto
  note vc = SN_imp_variable_condition [OF SN_Sw_step]
  from vc peak_imp_nabla2 [OF _ rsteps] have tu: "(t, u) \<in> nabla R\<^sub>\<omega> s ^^ 2" by auto
  from compatible_rstep_imp_less [OF Rw_less] have Sw_step_less: "rstep R\<^sub>\<omega> \<subseteq> {\<succ>}" by blast
  let ?less_s_conv = "(\<Union>z\<in>{z. s \<succ> z}. slab R\<^sub>\<omega> z)\<^sup>\<leftrightarrow>\<^sup>*"
  let ?leq_conv = "\<lambda> v. (\<Union>z\<in>{z. v \<succeq> z}. slab R\<^sub>\<omega> z)\<^sup>\<leftrightarrow>\<^sup>*"
  { fix v w
    assume vw: "(v, w) \<in> nabla R\<^sub>\<omega> s" and "s \<succ> v" and "s \<succ> w"
    then have vw: "(v, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down> \<or> (v, w) \<in> (rstep (PCP R\<^sub>\<omega>))\<^sup>\<leftrightarrow>" unfolding nabla_def by auto
    { assume "(v, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>"
      then obtain x where vx: "(v, x) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" and wx: "(w, x) \<in> (rstep R\<^sub>\<omega>)\<^sup>*"
        unfolding join_def rtrancl_converse by blast
      from rsteps_slabI [OF vx _ Sw_step_less, of v] have "(v, x) \<in> ?leq_conv v" by auto
      from slab_conv_less_label [OF this] \<open>s \<succ> v\<close> have vx: "(v, x) \<in> ?less_s_conv" by auto
      from rsteps_slabI [OF wx _ Sw_step_less, of w] have "(w, x) \<in> ?leq_conv w" by auto
      from slab_conv_less_label [OF this] \<open>s \<succ> w\<close> have "(x, w) \<in> ?less_s_conv"
        unfolding conversion_inv by auto
      from conversion_trans' [OF vx this] have "(v, w) \<in> ?less_s_conv" by auto
    } note if_joinable = this
    { assume "(v, w) \<in> (rstep (PCP R\<^sub>\<omega>))\<^sup>\<leftrightarrow>"
      then obtain v' w' C \<sigma> where step:"v = C\<langle>v'\<cdot>\<sigma>\<rangle>" "w = C\<langle>w'\<cdot>\<sigma>\<rangle>" "(v',w') \<in> (PCP R\<^sub>\<omega>)\<^sup>\<leftrightarrow>" by auto
      from this(3) fair have alt:"(v', w') \<in>  (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<or> (v', w') \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>" 
        unfolding Un_iff using join_sym converse_iff subsetCE[OF fair] by (metis UnE)
      from rstep_rstep rstep_union have 1:"(v', w') \<in>  (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<Longrightarrow> (v, w) \<in>  (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>"
        unfolding step by auto
      have 2:"(v', w') \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down> \<Longrightarrow> (v, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>" unfolding step by auto
      { assume vw:"(v, w) \<in>  (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>"
        then have "(v, w) \<in> (rstep (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>))\<^sup>\<leftrightarrow>" by blast
        then have vw:"(v, w) \<in> (mstep {#v, w#} (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>))\<^sup>\<leftrightarrow>"
          unfolding mstep_def mem_Collect_eq Un_iff converse_iff by auto
        from ERi_subset_ERw conversion_converse have "\<And>S. (mstep S (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>))\<^sup>\<leftrightarrow> \<subseteq> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
        from in_mono[OF this, rule_format, OF vw] have vw: "(v, w) \<in> (mstep {#v, w#} R\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*"
          unfolding Ew_empty by auto
        from \<open>s \<succ> v\<close> \<open>s \<succ> w\<close> have "\<forall> t \<in># {#v, w#}. s \<succ> t" by auto
        from vw msteps_imp_source_steps [OF this] have "(v, w) \<in> ?less_s_conv" by auto
      }
      with alt 1 2 if_joinable have "(v, w) \<in> ?less_s_conv" by auto
    }
    with vw if_joinable have "(v, w) \<in> ?less_s_conv" by auto
  } note nabla_slab = this
  from tu obtain v where v: "(t, v) \<in> nabla R\<^sub>\<omega> s" "(v, u) \<in> nabla R\<^sub>\<omega> s" by auto
  from v [unfolded nabla_def] have sv: "(s, v) \<in> (rstep R\<^sub>\<omega>)\<^sup>+" by auto
  from sv rsteps_subset_less [OF Sw_less] have sv: "s \<succ> v" by auto
  from Sw_step_less rsteps have st: "s \<succ> t" and su: "s \<succ> u" by auto
  note tv = nabla_slab [OF v(1) st sv]
  note vu = nabla_slab [OF v(2) sv su]
  with conversion_trans' [OF tv vu] show ?thesis by auto
qed

lemma Ew_empty_implies_CR_Rw:"CR (rstep R\<^sub>\<omega>)"
proof -
  interpret ars_peak_decreasing "slab R\<^sub>\<omega>" UNIV "(\<succ>)"
    by (unfold_locales, insert Ew_empty_implies_Rw_peak_decreasing SN_less, auto)
  from CR show ?thesis unfolding UN_source_step .
qed

end

locale gtotal_okb_irun = okb_irun + fgtotal_reduction_order less UNIV
begin

lemma fground_UNIV[simp]:"fground UNIV t = ground t"
  unfolding fground_def by auto

lemma FGROUND_UNIV[simp]:"FGROUND UNIV t = GROUND t"
  unfolding FGROUND_def GROUND_def by auto

lemma gmstep_ERw_Sw: "GROUND ((mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>) \<subseteq> GROUND (((mstep S S\<^sub>\<omega>)\<^sup>\<leftrightarrow>)\<^sup>=)"
proof
  fix s t
  assume "(s, t) \<in> GROUND ((mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>)"
  then have ground: "ground s" "ground t" and mstep: "(s, t) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>" unfolding GROUND_def by auto
  then have dom: "\<exists>s' t'. s' \<in># S \<and> t' \<in># S \<and> s' \<succeq> s \<and> t' \<succeq> t" unfolding mstep_def by auto
  from mstep rstep_converse have mstep: "(s, t) \<in> mstep S (R\<^sub>\<omega>\<^sup>\<leftrightarrow> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
    unfolding mstep_def Un_iff converse_iff mem_Collect_eq split rstep_union by blast
  from mstep mstep_Un consider "(s, t) \<in> mstep S (E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" | "(s, t) \<in> mstep S (R\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
  then show "(s, t) \<in> GROUND (((mstep S S\<^sub>\<omega>)\<^sup>\<leftrightarrow>)\<^sup>=)"
  proof (cases)
    case 1
    from ground fgtotal have "s \<succ> t \<or> t \<succ> s \<or> s = t" by auto
    from 1 rstepE obtain C \<sigma> l r where C: "(l, r) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      unfolding mstep_def by blast
    from ground [unfolded C ground_ctxt_apply] have "ground (l \<cdot> \<sigma>)" and "ground (r \<cdot> \<sigma>)" by auto
    with fgtotal[of "l \<cdot> \<sigma>" "r \<cdot> \<sigma>"] have oriented: "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma> \<or> r \<cdot> \<sigma> \<succ> l \<cdot> \<sigma> \<or> l \<cdot> \<sigma> = r \<cdot> \<sigma>" by auto
    from C(1) have rl: "(r, l) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" by auto
    have eq: "l \<cdot> \<sigma> = r \<cdot> \<sigma> \<Longrightarrow> s = t" unfolding C by auto
    have lr: "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma> \<Longrightarrow> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> S\<^sub>\<omega>" unfolding Sw_def
      by(rule UnI2, unfold mem_Collect_eq split, insert 1 C(1), auto)
    have rl: "r \<cdot> \<sigma> \<succ> l \<cdot> \<sigma> \<Longrightarrow> (r \<cdot> \<sigma>, l \<cdot> \<sigma>) \<in> S\<^sub>\<omega>" unfolding Sw_def
      by(rule UnI2, unfold mem_Collect_eq split, insert 1 C(1), auto)
    { assume "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma> \<or> r \<cdot> \<sigma> \<succ> l \<cdot> \<sigma>"
      with lr rl have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> S\<^sub>\<omega>\<^sup>\<leftrightarrow>" by auto
      with rstepI have "(s, t) \<in> (rstep S\<^sub>\<omega>)\<^sup>\<leftrightarrow>" unfolding C by auto
      with dom have "(s, t) \<in> (mstep S S\<^sub>\<omega>)\<^sup>\<leftrightarrow>" unfolding mstep_def mem_Collect_eq split by auto
      with ground have ?thesis unfolding GROUND_def by auto
    }
    with oriented eq ground show ?thesis using GROUND_def by blast
  next
    case 2
    with mstep [unfolded mstep_def] have "(s, t) \<in> (mstep S S\<^sub>\<omega>)\<^sup>\<leftrightarrow>"
      unfolding Sw_def mstep_Un mstep_def Un_iff converse_iff mem_Collect_eq split by auto
    with ground show ?thesis unfolding GROUND_def by auto
  qed
qed
  
lemma ground_Einf_Sw:
  assumes "(s, t) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>" and gs: "ground s" and gt: "ground t"
  shows "(s, t) \<in> (mstep {#s, t#} S\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  { fix s t
    assume a: "(s, t) \<in> rstep E\<^sub>\<infinity>" and gs: "ground s" and gt: "ground t"
    define S where "S = {#s, t#}"
    with a have "(s, t) \<in> rstep (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>)" unfolding rstep_union by auto
    then have "(s, t) \<in> mstep {#s, t#} (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>)" unfolding mstep_def by auto
    with ERi_subset_ERw have "(s, t) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding S_def by auto
    from this [unfolded conversion_def] have "(s, t) \<in> (mstep S S\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*"
    proof (induct)
      case base
      then show ?case by auto
    next
      case (step u v)
      note rsteps = step(2) [unfolded mstep_def Un_iff converse_iff mem_Collect_eq split]
      then have st_uv: "(s \<succeq> u \<or> t \<succeq> u) \<and> (s \<succeq> v \<or> t \<succeq> v)" unfolding S_def by force
      from ground_less have ground_leq: "\<And> s t. ground s \<Longrightarrow> s \<succeq> t \<Longrightarrow> ground t" by blast
      from st_uv ground_leq [OF gs] ground_leq [OF gt] have "ground u \<and> ground v" by metis
      with step(2) have "(u, v) \<in> GROUND ((mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>)" unfolding GROUND_def by auto
      with gmstep_ERw_Sw have uv: "(u, v) \<in> ((mstep S S\<^sub>\<omega>)\<^sup>\<leftrightarrow>)\<^sup>=" unfolding GROUND_def by auto
      with step(3) rtrancl_trans [OF step(3) [unfolded conversion_def] r_into_rtrancl] show ?case
        unfolding conversion_def by fast
    qed
    then have "(s, t) \<in> (mstep {#s, t#} S\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" unfolding S_def by auto
  } note estep = this
  from assms(1) estep [OF _ gs gt] estep [OF _ gt gs] show ?thesis
    unfolding Un_iff add_mset_commute [of t s "{#}"] converse_iff conversion_inv by auto
qed

end

locale ordered_completion_inf =
  ordered_completion less for less :: "('a, 'b::infinite) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
begin

lemma less_set_permute:
  "\<pi> \<bullet> {\<succ>} = {\<succ>}"
  apply (auto simp: )
   apply (metis inv_rule_mem_trs_simps(1) local.subst mem_Collect_eq old.prod.case term_apply_subst_Var_Rep_perm term_pt.permute_minus_cancel(1))
  by (metis case_prodI inv_rule_mem_trs_simps(1) mem_Collect_eq reduction_order.subst reduction_order_axioms term_apply_subst_Var_Rep_perm)

lemma ostep_permute:
  "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ostep (\<pi> \<bullet> E) (\<pi> \<bullet> R) \<longleftrightarrow> (s, t) \<in> ostep E R"
  using ordstep_permute [of \<pi> s t "{\<succ>}" "E\<^sup>\<leftrightarrow>"]
  unfolding less_set_permute
  by (simp add: eqvt [symmetric] ostep_def)

lemma ordstep_permute_litsim:
  assumes "(s, t) \<in> ordstep {\<succ>} R" and "R \<doteq> R'"
  shows "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ordstep {\<succ>} R'"
  using assms(1)
proof(cases)
  case (1 l r C \<sigma>)
  from litsim_mem[OF assms(2) 1(1)] obtain \<psi> where rule:"(\<psi> \<bullet> l, \<psi> \<bullet> r) \<in> R'" by (auto simp:eqvt)
  define D and \<tau> where "D = \<pi> \<bullet> C" and "\<tau> = sop (-\<psi>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop \<pi>"
  with 1 have s:"\<pi> \<bullet> s = D\<langle>(\<psi> \<bullet> l) \<cdot> \<tau>\<rangle>" and t:"\<pi> \<bullet> t = D\<langle>(\<psi> \<bullet> r) \<cdot> \<tau>\<rangle>"
    by (auto simp: eqvt [symmetric] term_pt.permute_flip)
  from 1(4) subst less_set_permute have "\<psi> \<bullet> l \<cdot> \<tau> \<succ> \<psi> \<bullet> r \<cdot> \<tau>" unfolding \<tau>_def by fastforce
  with ordstep.intros[OF rule s t] show ?thesis by auto
qed

lemma ordstep_join_permute_litsim:
  "(s, t) \<in> (ordstep {\<succ>} R)\<^sup>\<down> \<Longrightarrow> (\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> (ordstep {\<succ>} R)\<^sup>\<down>"
  using ordstep_permute_litsim
  by (metis join_subst subst_closed_less subst_closed_ordstep term_apply_subst_Var_Rep_perm)

lemma ground_joinable_permute_litsim:
  "ground_joinable S ord s t \<Longrightarrow> (ground_joinable S ord (\<pi> \<bullet> s) (\<pi> \<bullet> t))"
  unfolding fground_joinable_def using ordstep_join_permute_litsim ground_permute
  by (simp add: permute_term_subst_apply_term)

lemma encompeq_permute': "s \<unlhd>\<cdot> t \<Longrightarrow> (\<pi> \<bullet> s \<unlhd>\<cdot> \<psi> \<bullet> t)"
proof-
  assume "s \<unlhd>\<cdot> t"
  then obtain C \<sigma> where t:"t = C\<langle>s\<cdot>\<sigma>\<rangle>" by auto
  define D and \<tau> where "D = \<psi> \<bullet> C" and "\<tau> = sop (-\<pi>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop \<psi>"
  with t have t:"\<psi> \<bullet> t = D\<langle>(\<pi> \<bullet> s) \<cdot> \<tau>\<rangle>" by (auto simp: eqvt [symmetric] term_pt.permute_flip)
  then show "\<pi> \<bullet> s \<unlhd>\<cdot> \<psi> \<bullet> t" by blast
qed

lemma encompeq_permute: "s \<unlhd>\<cdot> t = (\<pi> \<bullet> s \<unlhd>\<cdot> \<psi> \<bullet> t)"
  by (metis encompeq_permute' term_pt.permute_minus_cancel(2))

lemma encomp_permute: "s \<lhd>\<cdot> t = (\<pi> \<bullet> s \<lhd>\<cdot> \<psi> \<bullet> t)"
  using encompeq_permute unfolding encomp_def by auto

lemma encstep1_permute_litsim:
  assumes "(s, t) \<in> encstep1 E R" and "E \<doteq> E'" and "R \<doteq> R'"
  shows "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> encstep1 E' R'"
  using assms(1)
proof(cases)
  case (estep l r C \<sigma>)
  from litsim_mem[OF litsim_symcl[OF assms(2)] estep(1)] obtain \<psi> where eq:"(\<psi> \<bullet> l, \<psi> \<bullet> r) \<in> E'\<^sup>\<leftrightarrow>" by (auto simp:eqvt)
  define D and \<tau> where "D = \<pi> \<bullet> C" and "\<tau> = sop (-\<psi>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop \<pi>"
  with estep have s:"\<pi> \<bullet> s = D\<langle>(\<psi> \<bullet> l) \<cdot> \<tau>\<rangle>" and t:"\<pi> \<bullet> t = D\<langle>(\<psi> \<bullet> r) \<cdot> \<tau>\<rangle>"
    by (auto simp: eqvt [symmetric] term_pt.permute_flip)
  from estep(4) subst less_set_permute have less:"\<psi> \<bullet> l \<cdot> \<tau> \<succ> \<psi> \<bullet> r \<cdot> \<tau>" unfolding \<tau>_def by fastforce
  from estep(5) encomp_permute have "\<psi> \<bullet> l \<lhd>\<cdot> \<pi> \<bullet> s" by auto
  with encstep1.intros(1)[OF eq s t less] show ?thesis .
next
  case rstep
  with litsim_rstep_eq[OF assms(3)] perm_rstep_conv encstep1.intros show ?thesis by auto
qed

lemma encstep2_permute_litsim:
  assumes "(s, t) \<in> encstep2 E R" and "E \<doteq> E'" and "R \<doteq> R'"
  shows "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> encstep2 E' R'"
  using assms(1)
proof(cases)
  case (estep l r C \<sigma>)
  from litsim_mem[OF litsim_symcl[OF assms(2)] estep(1)] obtain \<psi> where eq:"(\<psi> \<bullet> l, \<psi> \<bullet> r) \<in> E'\<^sup>\<leftrightarrow>" by (auto simp:eqvt)
  define D and \<tau> where "D = \<pi> \<bullet> C" and "\<tau> = sop (-\<psi>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop \<pi>"
  with estep have s:"\<pi> \<bullet> s = D\<langle>(\<psi> \<bullet> l) \<cdot> \<tau>\<rangle>" and t:"\<pi> \<bullet> t = D\<langle>(\<psi> \<bullet> r) \<cdot> \<tau>\<rangle>"
    by (auto simp: eqvt [symmetric] term_pt.permute_flip)
  from estep(4) subst less_set_permute have less:"\<psi> \<bullet> l \<cdot> \<tau> \<succ> \<psi> \<bullet> r \<cdot> \<tau>" unfolding \<tau>_def by fastforce
  from estep(5) encomp_permute have "\<psi> \<bullet> l \<lhd>\<cdot> \<pi> \<bullet> s" by auto
  with encstep2.intros(1)[OF eq s t less] show ?thesis .
next
  case (rstep l r C \<sigma>)
  from litsim_mem[OF assms(3) rstep(1)] obtain \<psi> where rule:"(\<psi> \<bullet> l, \<psi> \<bullet> r) \<in> R'" by (auto simp:eqvt)
  define D and \<tau> where "D = \<pi> \<bullet> C" and "\<tau> = sop (-\<psi>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop \<pi>"
  with rstep have s:"\<pi> \<bullet> s = D\<langle>(\<psi> \<bullet> l) \<cdot> \<tau>\<rangle>" and t:"\<pi> \<bullet> t = D\<langle>(\<psi> \<bullet> r) \<cdot> \<tau>\<rangle>"
    by (auto simp: eqvt [symmetric] term_pt.permute_flip)
  from rstep(4) encomp_permute have "\<psi> \<bullet> l \<lhd>\<cdot> \<pi> \<bullet> s" by auto
  with encstep2.intros(2)[OF rule s t] show ?thesis .
qed

lemma ostep_permute_litsim:
  assumes "(s, t) \<in> ostep E R" and "E \<doteq> E'" and "R \<doteq> R'"
  shows "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ostep E' R'"
  using assms ordstep_permute_litsim [of s t, OF _ litsim_symcl[OF assms(2)]]
  unfolding ostep_def
  by (metis UnE UnI1 UnI2 litsim_rstep_eq rstep_permute_iff)

lemma oKB_permute:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  shows "(\<pi> \<bullet> E, \<pi> \<bullet> R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (\<pi> \<bullet> E', \<pi> \<bullet> R')"
  using assms
proof (cases)
  case (deduce s t u)
  with oKB.deduce [of "\<pi> \<bullet> s" "\<pi> \<bullet> t" "\<pi> \<bullet> R" "\<pi> \<bullet> E" "\<pi> \<bullet> u"] show ?thesis
    by (simp add: eqvt) (metis (no_types, lifting) rstep_permute rstep_simps(5) rstep_union)
next
  case (orientl s t)
  with oKB.orientl [of "\<pi> \<bullet> s" "\<pi> \<bullet> t" "\<pi> \<bullet> E" "\<pi> \<bullet> R"] show ?thesis
    by (simp add: eqvt) (metis local.subst term_apply_subst_Var_Rep_perm)
next
  case (orientr t s)
  with oKB.orientr [of "\<pi> \<bullet> t" "\<pi> \<bullet> s" "\<pi> \<bullet> E" "\<pi> \<bullet> R"] show ?thesis
    by (simp add: eqvt) (metis local.subst term_apply_subst_Var_Rep_perm)
next
  case (delete s)
  with oKB.delete [of "\<pi> \<bullet> s" "\<pi> \<bullet> E" "\<pi> \<bullet> R"] show ?thesis by (simp add: eqvt)
next
  case (compose t u s)
  with oKB.compose [of "\<pi> \<bullet> t" "\<pi> \<bullet> u" "\<pi> \<bullet> E" "\<pi> \<bullet> R" "\<pi> \<bullet> s"] show ?thesis
    using ostep_permute [of \<pi> t u E "R - {(s, t)}"] by (simp add: eqvt)
next
  case (simplifyl s u t)
  with oKB.simplifyl [of "\<pi> \<bullet> s" "\<pi> \<bullet> u" "\<pi> \<bullet> E" "\<pi> \<bullet> t" "\<pi> \<bullet> R"] show ?thesis
    using ostep_permute [of \<pi> s u "E - {(s, t)}" R] by (simp add: eqvt)
next
  case (simplifyr t u s)
  with oKB.simplifyr [of "\<pi> \<bullet> t" "\<pi> \<bullet> u" "\<pi> \<bullet> E" "\<pi> \<bullet> s" "\<pi> \<bullet> R"] show ?thesis
    using ostep_permute [of \<pi> t u "E - {(s, t)}" R] by (simp add: eqvt)
next
  case (collapse t u s)
  with oKB.collapse [of "\<pi> \<bullet> t" "\<pi> \<bullet> u" "\<pi> \<bullet> E" "\<pi> \<bullet> R" "\<pi> \<bullet> s"] show ?thesis
    using ostep_permute [of \<pi> t u "E" "R - {(t, s)}"] by (simp add: eqvt)
qed

lemma oKB_permute':
  assumes "(\<pi> \<bullet> E, \<pi> \<bullet> R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (\<pi> \<bullet> E', \<pi> \<bullet> R')"
  shows "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B (E', R')"
  using oKB_permute[OF assms, of "- \<pi>"] by auto

inductive oKB' :: "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> bool"  (infix "\<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sup>\<pi>" 55)
  where
    deduce: "(s, t) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, u) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> oKB' (E, R) (E \<union> {(p \<bullet> t, p \<bullet> u)}, R)" |
    orientl: "s \<succ> t \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> oKB' (E, R) (E - {(s, t)}, R \<union> {(p \<bullet> s, p \<bullet> t)})" |
    orientr: "t \<succ> s \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> oKB' (E, R) (E - {(s, t)}, R \<union> {(p \<bullet> t, p \<bullet> s)})" |
    delete: "(s, s) \<in> E \<Longrightarrow> oKB' (E, R) (E - {(s, s)}, R)" |
    compose: "(t, u) \<in> ostep E (R - {(s, t)}) \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> oKB' (E, R) (E, (R - {(s, t)}) \<union> {(p \<bullet> s, p \<bullet> u)})" |
    simplifyl: "(s, u) \<in> ostep (E - {(s, t)}) R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> oKB' (E, R) ((E - {(s, t)}) \<union> {(p \<bullet> u, p \<bullet> t)}, R)" |
    simplifyr: "(t, u) \<in> ostep (E - {(s, t)}) R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> oKB' (E, R) ((E - {(s, t)}) \<union> {(p \<bullet> s, p \<bullet> u)}, R)" |
    collapse: "(t, u) \<in> ostep E (R - {(t, s)}) \<Longrightarrow> (t, s) \<in> R \<Longrightarrow> oKB' (E, R) (E \<union> {(p \<bullet> u, p \<bullet> s)}, R - {(t, s)})"

inductive
  oKBi' :: "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> bool"  (infix "\<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>\<pi>" 55)
  where
    deduce: "(s, t) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, u) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> oKBi' (E, R) (E \<union> {(p \<bullet> t, p \<bullet> u)}, R)" |
    orientl: "s \<succ> t \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> oKBi' (E, R) (E - {(s, t)}, R \<union> {(p \<bullet> s, p \<bullet> t)})" |
    orientr: "t \<succ> s \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> oKBi' (E, R) (E - {(s, t)}, R \<union> {(p \<bullet> t, p \<bullet> s)})" |
    delete: "(s, s) \<in> E \<Longrightarrow> oKBi' (E, R) (E - {(s, s)}, R)" |
    compose: "(t, u) \<in> ostep E (R - {(s, t)}) \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> oKBi' (E, R) (E, (R - {(s, t)}) \<union> {(p \<bullet> s, p \<bullet> u)})" |
    simplifyl: "(s, u) \<in> encstep1 (E - {(s, t)}) R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> oKBi' (E, R) ((E - {(s, t)}) \<union> {(p \<bullet> u, p \<bullet> t)}, R)" |
    simplifyr: "(t, u) \<in> encstep1 (E - {(s, t)}) R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> oKBi' (E, R) ((E - {(s, t)}) \<union> {(p \<bullet> s, p \<bullet> u)}, R)" |
    collapse: "(t, u) \<in> encstep2 E (R - {(t, s)}) \<Longrightarrow> (t, s) \<in> R \<Longrightarrow> oKBi' (E, R) (E \<union> {(p \<bullet> u, p \<bullet> s)}, R - {(t, s)})"

lemma oKB_step_variant_free':
  assumes "(E\<^sub>0, R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1, R\<^sub>1)"
    "variant_free_trs E\<^sub>0" and "variant_free_trs R\<^sub>0" and "\<not> (variant_free_trs E\<^sub>1 \<and> variant_free_trs R\<^sub>1)"
  shows "\<exists>E\<^sub>0' R\<^sub>0' E\<^sub>1' R\<^sub>1'. (E\<^sub>0', R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1', R\<^sub>1') \<and> E\<^sub>0' \<doteq> E\<^sub>0 \<and> R\<^sub>0' \<doteq> R\<^sub>0 \<and> E\<^sub>1' \<doteq> E\<^sub>1 \<and> R\<^sub>1' \<doteq> R\<^sub>1 \<and>
         variant_free_trs E\<^sub>0' \<and> variant_free_trs R\<^sub>0' \<and> variant_free_trs E\<^sub>1' \<and> variant_free_trs R\<^sub>1'"
proof-
  have insert:"\<And>S S' \<pi> s t. S' \<doteq> S \<Longrightarrow> S \<union> {(\<pi> \<bullet> s, \<pi> \<bullet> t)} \<doteq> S' \<union> {(s, t)}"
    using litsim_insert[OF _ rule_pt.permute_prod_eqvt[symmetric]] subsumable_trs.litsim_sym by fastforce
  { fix l r and S :: "('a, 'b) trs"
    assume v:"variant_free_trs S" and lr:"(l,r) \<in> S"
    from lr v[unfolded variant_free_trs_def, rule_format, of l r] have "\<forall>p. (p \<bullet> l, p \<bullet> r) \<notin> S - {(l,r)}" 
      by fastforce
    then have "\<forall>p p'. (p \<bullet> (p' \<bullet> l), p \<bullet> (p' \<bullet> r)) \<notin> S - {(l,r)}" by (metis term_pt.permute_plus)
    with variant_free_trs_insert[OF variant_free_trs_diff, OF v]
      have "\<And>\<pi>. variant_free_trs (S - {(l,r)} \<union> {(\<pi> \<bullet> l, \<pi> \<bullet> r)})" by auto
  }
  note vf = this
  note vfE = assms(2)[unfolded variant_free_trs_def, rule_format]
  note vfR = assms(3)[unfolded variant_free_trs_def, rule_format]
  { fix l r and S :: "('a, 'b) trs"
    assume lr:"(l,r) \<in> S"
    from litsim_insert[OF subsumable_trs.litsim_refl, of _ _ "(l,r)" "S - {(l, r)}"] insert_Diff[OF lr]
      have "\<And>\<pi>. S \<doteq> S - {(l,r)} \<union> {(\<pi> \<bullet> l, \<pi> \<bullet> r)}"  by (auto simp:eqvt)
    then have "\<And>\<pi>. S - {(l,r)} \<union> {(\<pi> \<bullet> l, \<pi> \<bullet> r)} \<doteq> S" using subsumable_trs.litsim_sym by fast
  }
  note permute_replace = this
  note eqrel = subsumable_trs.litsim_trans subsumable_trs.litsim_sym subsumable_trs.litsim_refl
  show ?thesis using assms proof(cases)
    case (deduce s t u)
    with assms(3) assms(2) assms(4) have "\<not> (variant_free_trs E\<^sub>1)" by auto
    with assms(2) variant_free_trs_insert have "\<exists>\<rho>. (\<rho> \<bullet> t, \<rho> \<bullet> u) \<in> E\<^sub>0" unfolding deduce by fastforce
    then obtain \<rho> where \<rho>:"(\<rho> \<bullet> t, \<rho> \<bullet> u) \<in> E\<^sub>0" by auto
    from insert_absorb[OF \<rho>] insert[OF eqrel(3), of E\<^sub>0 \<rho> t u] have litsim:"E\<^sub>0 \<doteq> E\<^sub>1" unfolding deduce(1) by force
    from deduce rstep_permute have "(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> rstep (R\<^sub>0 \<union> E\<^sub>0\<^sup>\<leftrightarrow>)" "(\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> rstep (R\<^sub>0 \<union> E\<^sub>0\<^sup>\<leftrightarrow>)" by auto
    from oKBi.deduce[OF this] insert_absorb[OF \<rho>] have step:"(E\<^sub>0, R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>0, R\<^sub>0)" by auto
    show ?thesis by (rule exI[of _ E\<^sub>0], rule exI[of _ R\<^sub>0], rule exI[of _ E\<^sub>0], rule exI[of _ R\<^sub>0],
                     insert step assms eqrel litsim deduce(2), auto)
next
  case (orientl s t)
    with assms(3) assms(2) assms(4) variant_free_trs_diff have "\<not> (variant_free_trs R\<^sub>1)" by auto
    with assms(3) variant_free_trs_insert have "\<exists>\<rho>. (\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> R\<^sub>0" unfolding orientl by fastforce
    then obtain \<rho> where \<rho>:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> R\<^sub>0" by auto
    from insert_absorb[OF \<rho>] insert[OF eqrel(3), of R\<^sub>0 \<rho> s t] have litsimR:"R\<^sub>0 \<doteq> R\<^sub>1" unfolding orientl by force
    let ?E0 = "E\<^sub>0 - {(s,t)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    from vfE[of s t] orientl(4) have "(\<rho> \<bullet> s, \<rho> \<bullet> t) \<notin> E\<^sub>0 \<or> (\<rho> \<bullet> s, \<rho> \<bullet> t) = (s,t)" by metis
    then have E:"?E0 - {(\<rho> \<bullet> s, \<rho> \<bullet> t)} = E\<^sub>1" unfolding orientl(1) by blast
    have mem:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> ?E" by auto
    from orientl(3) less_set_permute have "\<rho> \<bullet> s \<succ> \<rho> \<bullet> t" by auto
    from oKBi.orientl[OF this mem, of R\<^sub>0] insert_absorb[OF \<rho>] have step:"(?E, R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1, R\<^sub>0)" unfolding E by auto
    have litsimE:"?E \<doteq> E\<^sub>0" by (meson orientl(4) permute_replace eqrel)
    from vf[OF assms(2) orientl(4)] have vf0:"variant_free_trs ?E0" by auto
    from variant_free_trs_diff[OF assms(2)] orientl(1) have vf1:"variant_free_trs E\<^sub>1" by auto
    show ?thesis by (rule exI[of _ ?E0], rule exI[of _ R\<^sub>0], rule exI[of _ E\<^sub>1], rule exI[of _ R\<^sub>0],
                     insert step litsimE litsimR eqrel assms(2) assms(3) vf0 vf1, auto)
next
  case (orientr t s)
    with assms(3) assms(2) assms(4) variant_free_trs_diff have "\<not> (variant_free_trs R\<^sub>1)" by auto
    with assms(3) variant_free_trs_insert have "\<exists>\<rho>. (\<rho> \<bullet> t, \<rho> \<bullet> s) \<in> R\<^sub>0" unfolding orientr by fastforce
    then obtain \<rho> where \<rho>:"(\<rho> \<bullet> t, \<rho> \<bullet> s) \<in> R\<^sub>0" by auto
    from insert_absorb[OF \<rho>] insert[OF eqrel(3), of R\<^sub>0 \<rho> t s] have litsimR:"R\<^sub>0 \<doteq> R\<^sub>1" unfolding orientr by force
    let ?E0 = "E\<^sub>0 - {(s,t)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    from vfE[of s t] orientr(4) have "(\<rho> \<bullet> s, \<rho> \<bullet> t) \<notin> E\<^sub>0 \<or> (\<rho> \<bullet> s, \<rho> \<bullet> t) = (s,t)" by metis
    then have E:"?E0 - {(\<rho> \<bullet> s, \<rho> \<bullet> t)} = E\<^sub>1" unfolding orientr(1) by blast
    have mem:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> ?E" by auto
    from orientr(3) less_set_permute have "\<rho> \<bullet> t \<succ> \<rho> \<bullet> s" by auto
    from oKBi.orientr[OF this mem, of R\<^sub>0] insert_absorb[OF \<rho>] have step:"(?E, R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1, R\<^sub>0)" unfolding E by auto
    have litsimE:"?E \<doteq> E\<^sub>0" by (meson orientr(4) permute_replace eqrel)
    from vf[OF assms(2) orientr(4)] have vf0:"variant_free_trs ?E0" by auto
    from variant_free_trs_diff[OF assms(2)] orientr(1) have vf1:"variant_free_trs E\<^sub>1" by auto
    show ?thesis by (rule exI[of _ ?E0], rule exI[of _ R\<^sub>0], rule exI[of _ E\<^sub>1], rule exI[of _ R\<^sub>0],
                     insert step litsimE litsimR eqrel assms(2) assms(3) vf0 vf1, auto)
next
case (delete s)
  with variant_free_trs_diff[OF assms(2), of "{(s,s)}"] assms(3) assms(4) show ?thesis by fast
next
  case (compose t u s)
    with assms(3) assms(2) assms(4) variant_free_trs_diff have "\<not> (variant_free_trs R\<^sub>1)" by auto
    with assms(3) variant_free_trs_insert[OF variant_free_trs_diff[OF assms(3)], of s u "{(s, t)}"]
      have "\<exists>\<rho>. (\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> R\<^sub>0 - {(s,t)}" unfolding compose by auto
    then obtain \<rho> where \<rho>:"(\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> R\<^sub>0 - {(s,t)}" by auto
    define R\<^sub>0' where "R\<^sub>0' = R\<^sub>0 - {(s, t)} \<union> {(\<rho> \<bullet> s,\<rho> \<bullet> t)}"
    then have mem':"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> R\<^sub>0'" by auto
    from vf[OF assms(3)] compose(4) have vf0:"variant_free_trs R\<^sub>0'" unfolding R\<^sub>0'_def by auto
    define R\<^sub>1' where "R\<^sub>1' = R\<^sub>0 - {(s, t)}"
    from vfR[of s t] compose(4) have "(\<rho> \<bullet> s, \<rho> \<bullet> t) \<notin> R\<^sub>0 \<or> (\<rho> \<bullet> s, \<rho> \<bullet> t) = (s,t)" by metis
    then have R:"R\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)} = R\<^sub>1'" unfolding compose(2) R\<^sub>0'_def R\<^sub>1'_def by blast
    from R eqrel(3) R\<^sub>1'_def have R':"R\<^sub>0 - {(s, t)} \<doteq> R\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" by auto
    note ostep = ostep_permute_litsim[OF compose(3) eqrel(3) this] 
    from oKBi.compose[OF ostep] insert_absorb[OF \<rho>] R\<^sub>0'_def have step:"(E\<^sub>0, R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1, R\<^sub>1')"
      unfolding compose(1) R\<^sub>1'_def R by auto
    from vf[OF assms(3) compose(4)] have vf0:"variant_free_trs R\<^sub>0'" unfolding R\<^sub>0'_def by blast
    from variant_free_trs_diff[OF assms(3)] have vf1:"variant_free_trs R\<^sub>1'" unfolding R\<^sub>1'_def by blast
    from permute_replace[OF compose(4)] have litsim0:"R\<^sub>0' \<doteq> R\<^sub>0" unfolding R\<^sub>0'_def by blast
    from insert_absorb[OF \<rho>] insert[OF eqrel(3), of "R\<^sub>0 - {(s, t)}" \<rho> s u] have litsim1:"R\<^sub>1' \<doteq> R\<^sub>1"
      unfolding R\<^sub>1'_def compose(2) by force
    show ?thesis by (rule exI[of _ E\<^sub>0], rule exI[of _ R\<^sub>0'], rule exI[of _ E\<^sub>0], rule exI[of _ R\<^sub>1'],
          insert step compose(1) vf0 vf1 litsim0 litsim1 assms(2), auto)
next
  case (simplifyl s u t)
    with assms(3) assms(2) assms(4) have nvf:"\<not> (variant_free_trs E\<^sub>1)" by auto
    note vf' = variant_free_trs_insert[OF variant_free_trs_diff[OF assms(2)], of u t "{(s, t)}"]
    with nvf have "\<exists>\<rho>. (\<rho> \<bullet> u, \<rho> \<bullet> t) \<in> E\<^sub>0 - {(s, t)}" unfolding simplifyl by fastforce
    then obtain \<rho> where \<rho>:"(\<rho> \<bullet> u, \<rho> \<bullet> t) \<in> E\<^sub>0 - {(s, t)}" by auto
    define E\<^sub>0' where "E\<^sub>0' = E\<^sub>0 - {(s, t)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    then have mem:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> E\<^sub>0'" by auto
    define E\<^sub>1' where "E\<^sub>1' = E\<^sub>0 - {(s, t)}"
    from vfE[of s t] simplifyl(4) have "(\<rho> \<bullet> s, \<rho> \<bullet> t) \<notin> E\<^sub>0 \<or> (\<rho> \<bullet> s, \<rho> \<bullet> t) = (s,t)" by metis
    then have E:"E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)} = E\<^sub>1'" unfolding simplifyl(1) E\<^sub>0'_def E\<^sub>1'_def by blast
    from E eqrel(3) E\<^sub>1'_def have E':"E\<^sub>0 - {(s, t)} \<doteq> E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" by auto
    note encstep = encstep1_permute_litsim[OF simplifyl(3) this eqrel(3)]
    from oKBi.simplifyl[OF encstep mem] E insert_absorb[OF \<rho>] have step:"(E\<^sub>0', R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1', R\<^sub>1)"
      unfolding simplifyl(2) E\<^sub>1'_def by auto
    from vf[OF assms(2) simplifyl(4)] have vf0:"variant_free_trs E\<^sub>0'" unfolding E\<^sub>0'_def by blast
    from variant_free_trs_diff[OF assms(2)] have vf1:"variant_free_trs E\<^sub>1'" unfolding E\<^sub>1'_def by blast
    from permute_replace[OF simplifyl(4)] have litsim0:"E\<^sub>0' \<doteq> E\<^sub>0" unfolding E\<^sub>0'_def by blast
    from insert_absorb[OF \<rho>] insert[OF eqrel(3), of E\<^sub>1' \<rho> u t] have litsim1:"E\<^sub>1' \<doteq> E\<^sub>1"
      unfolding E\<^sub>1'_def simplifyl(1) by auto
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R\<^sub>0], rule exI[of _ E\<^sub>1'], rule exI[of _ R\<^sub>1],
          insert step vf0 vf1 litsim0 litsim1 assms(3), unfold simplifyl(2), auto)
next
  case (simplifyr t u s)
    with assms(3) assms(2) assms(4) have nvf:"\<not> (variant_free_trs E\<^sub>1)" by auto
    note vf' = variant_free_trs_insert[OF variant_free_trs_diff[OF assms(2)], of s u "{(s, t)}"]
    with nvf have "\<exists>\<rho>. (\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> E\<^sub>0 - {(s, t)}" unfolding simplifyr by fastforce
    then obtain \<rho> where \<rho>:"(\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> E\<^sub>0 - {(s, t)}" by auto
    define E\<^sub>0' where "E\<^sub>0' = E\<^sub>0 - {(s, t)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    then have mem:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> E\<^sub>0'" by auto
    define E\<^sub>1' where "E\<^sub>1' = E\<^sub>0 - {(s, t)}"
    from vfE[of s t] simplifyr(4) have "(\<rho> \<bullet> s, \<rho> \<bullet> t) \<notin> E\<^sub>0 \<or> (\<rho> \<bullet> s, \<rho> \<bullet> t) = (s,t)" by metis
    then have E:"E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)} = E\<^sub>1'" unfolding simplifyl(1) E\<^sub>0'_def E\<^sub>1'_def by blast
    from E eqrel(3) E\<^sub>1'_def have E':"E\<^sub>0 - {(s, t)} \<doteq> E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" by auto
    note encstep = encstep1_permute_litsim[OF simplifyr(3) this eqrel(3)] 
    from oKBi.simplifyr[OF encstep mem] E insert_absorb[OF \<rho>] have step:"(E\<^sub>0', R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1', R\<^sub>1)"
      unfolding simplifyr(2) E\<^sub>1'_def by auto
    from vf[OF assms(2) simplifyr(4)] have vf0:"variant_free_trs E\<^sub>0'" unfolding E\<^sub>0'_def by blast
    from variant_free_trs_diff[OF assms(2)] have vf1:"variant_free_trs E\<^sub>1'" unfolding E\<^sub>1'_def by blast
    from permute_replace[OF simplifyr(4)] have litsim0:"E\<^sub>0' \<doteq> E\<^sub>0" unfolding E\<^sub>0'_def by blast
    from insert_absorb[OF \<rho>] insert[OF eqrel(3), of E\<^sub>1' \<rho> s u] have litsim1:"E\<^sub>1' \<doteq> E\<^sub>1"
      unfolding E\<^sub>1'_def simplifyr(1) by auto
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R\<^sub>0], rule exI[of _ E\<^sub>1'], rule exI[of _ R\<^sub>1],
          insert step vf0 vf1 litsim0 litsim1 assms(3), unfold simplifyr(2), auto)
next
  case (collapse t u s)
    with assms(3) assms(2) assms(4) variant_free_trs_diff have "\<not> (variant_free_trs E\<^sub>1)" by auto
    with assms(2) variant_free_trs_insert have "\<exists>\<rho>. (\<rho> \<bullet> u, \<rho> \<bullet> s) \<in> E\<^sub>0" unfolding collapse by fastforce
    then obtain \<rho> where \<rho>:"(\<rho> \<bullet> u, \<rho> \<bullet> s) \<in> E\<^sub>0" by auto
    define R\<^sub>0' where "R\<^sub>0' = R\<^sub>0 - {(t, s)} \<union> {(\<rho> \<bullet> t, \<rho> \<bullet> s)}"
    then have mem:"(\<rho> \<bullet> t, \<rho> \<bullet> s) \<in> R\<^sub>0'" by auto
    from vfR[of t s] collapse(4) have R:"(\<rho> \<bullet> t, \<rho> \<bullet> s) \<notin> R\<^sub>0 \<or> (\<rho> \<bullet> t, \<rho> \<bullet> s) = (t,s)" by metis
    then have R':"R\<^sub>0' - {(\<rho> \<bullet> t, \<rho> \<bullet> s)} = R\<^sub>1" unfolding collapse(2) R\<^sub>0'_def by blast
    from R have "R\<^sub>0 - {(t, s)} \<doteq> R\<^sub>0' - {(\<rho> \<bullet> t, \<rho> \<bullet> s)}" unfolding R\<^sub>0'_def by fastforce
    note encstep = encstep2_permute_litsim[OF collapse(3) eqrel(3) this] 
    from oKBi.collapse[OF encstep mem] insert_absorb[OF \<rho>] have step:"(E\<^sub>0, R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>0, R\<^sub>1)"
      unfolding R' by auto
    from vf[OF assms(3) collapse(4)] have vf0:"variant_free_trs R\<^sub>0'" unfolding R\<^sub>0'_def by auto
    with R' variant_free_trs_diff have vf1:"variant_free_trs R\<^sub>1" by blast
    from collapse(4) permute_replace have litsimR:"R\<^sub>0' \<doteq> R\<^sub>0" unfolding R\<^sub>0'_def by auto
    from insert_absorb[OF \<rho>] insert[OF eqrel(3), of E\<^sub>0 \<rho> u s] have litsimE:"E\<^sub>0 \<doteq> E\<^sub>1" unfolding collapse(1) by auto
    show ?thesis by (rule exI[of _ E\<^sub>0], rule exI[of _ R\<^sub>0'], rule exI[of _ E\<^sub>0], rule exI[of _ R\<^sub>1],
          insert step vf0 vf1 litsimR litsimE assms(2) eqrel(3), auto)
  qed
qed

lemma oKB_step_variant_free:
  assumes "(E\<^sub>0, R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1, R\<^sub>1)"
    "variant_free_trs E\<^sub>0" and "variant_free_trs R\<^sub>0"
  shows "\<exists>E\<^sub>0' R\<^sub>0' E\<^sub>1' R\<^sub>1'. (E\<^sub>0', R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1', R\<^sub>1') \<and> E\<^sub>0' \<doteq> E\<^sub>0 \<and> R\<^sub>0' \<doteq> R\<^sub>0 \<and> E\<^sub>1' \<doteq> E\<^sub>1 \<and> R\<^sub>1' \<doteq> R\<^sub>1 \<and>
         variant_free_trs E\<^sub>0' \<and> variant_free_trs R\<^sub>0' \<and> variant_free_trs E\<^sub>1' \<and> variant_free_trs R\<^sub>1'"
proof(cases "\<not>(variant_free_trs E\<^sub>1 \<and> variant_free_trs R\<^sub>1)")
  case True
  then show ?thesis using oKB_step_variant_free'[OF assms] by auto
next
  case False            
  show ?thesis by (rule exI[of _ E\<^sub>0], rule exI[of _ R\<^sub>0], rule exI[of _ E\<^sub>1], rule exI[of _ R\<^sub>1], insert assms False, auto)
qed

lemma step_implies_litsim_step:
  assumes "(E\<^sub>0, R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E, R)" and "R' \<doteq> R" and "E' \<doteq> E" and
    "variant_free_trs E'" and "variant_free_trs R'" and "variant_free_trs E" and "variant_free_trs R"
and "variant_free_trs E\<^sub>0" and "variant_free_trs R\<^sub>0" and "R\<^sub>0 \<subseteq> {\<succ>}"
  shows "\<exists>E\<^sub>0' R\<^sub>0'. (E\<^sub>0', R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R') \<and> R\<^sub>0 \<doteq> R\<^sub>0' \<and> E\<^sub>0 \<doteq> E\<^sub>0' \<and> variant_free_trs E\<^sub>0' \<and> variant_free_trs R\<^sub>0'"
proof-
  have replace:"\<And>S S' \<pi> s t. S' \<doteq> S \<Longrightarrow> S \<union> {(\<pi> \<bullet> s, \<pi> \<bullet> t)} \<doteq> S' \<union> {(s, t)}"
    using litsim_insert[OF _ rule_pt.permute_prod_eqvt[symmetric]] subsumable_trs.litsim_sym by fastforce
  { fix l r and S :: "('a, 'b) trs"
    assume lr:"(l,r) \<in> S"
    from litsim_insert[OF subsumable_trs.litsim_refl, of _ _ "(l,r)" "S - {(l, r)}"] insert_Diff[OF lr]
      have "\<And>\<pi>. S \<doteq> S - {(l,r)} \<union> {(\<pi> \<bullet> l, \<pi> \<bullet> r)}"  by (auto simp:eqvt)
    then have "\<And>\<pi>. S - {(l,r)} \<union> {(\<pi> \<bullet> l, \<pi> \<bullet> r)} \<doteq> S" using subsumable_trs.litsim_sym by fast
  }
  note permute_replace = this
  note sym = subsumable_trs.litsim_sym
  { fix \<rho> t u E\<^sub>0 E\<^sub>0' E'
    assume \<rho>:"(\<rho> \<bullet> t, \<rho> \<bullet> u) \<in> E'" and E:"E\<^sub>0' = (if (t, u) \<in> E\<^sub>0 then E' else E' - {(\<rho> \<bullet> t, \<rho> \<bullet> u)})"
      and litsim:"E' \<doteq> E\<^sub>0 \<union> {(t, u)}"
      and vf:"variant_free_trs (E\<^sub>0 \<union> {(t, u)})" and vf':"variant_free_trs E'"
    have litsim:"E\<^sub>0 \<doteq> E\<^sub>0'" proof(cases "(t, u) \<in> E\<^sub>0")
      case True
      from sym True insert_absorb[OF True] insert_absorb[OF \<rho>] replace[OF litsim[THEN sym], of \<rho> t u]
      show "E\<^sub>0 \<doteq> E\<^sub>0'" unfolding E by force
    next
      case False
      with litsim_diff1[OF _ vf vf' _ _ \<rho>, of \<rho> "(t,u)"] litsim[THEN sym] show "E\<^sub>0 \<doteq> E\<^sub>0'"
        unfolding E using litsim by (auto simp:eqvt)
    qed
  } note Eaux = this
  note litsim_defs = subsumable_trs.litsim_def subsumeseq_trs_def
  { fix \<psi> s t E\<^sub>0 E E' G
    assume E:"E = E\<^sub>0 - {(s,t)} \<union> G" and G:"\<forall>\<pi>.(\<pi> \<bullet> s,\<pi> \<bullet> t) \<notin> G" and mem:"(s,t) \<in> E\<^sub>0" and litsim:"E' \<doteq> E" and
      vf:"variant_free_trs E\<^sub>0" and mem':"(\<psi> \<bullet> s, \<psi> \<bullet> t) \<in> E'" (is "(?s,?t) \<in> _")
    from mem' litsim obtain \<pi> where \<pi>:"(\<pi> \<bullet> ?s, \<pi> \<bullet> ?t) \<in> E" unfolding litsim_defs by (auto simp:eqvt)
    with E G[rule_format, of "\<pi> + \<psi>"] have "(\<pi> \<bullet> ?s, \<pi> \<bullet> ?t) \<in> E\<^sub>0" by force
    with vf[unfolded variant_free_trs_def] mem have "(\<pi> \<bullet> ?s, \<pi> \<bullet> ?t) = (s,t)" unfolding term_pt.permute_plus[symmetric] by metis
    with \<pi> E G[rule_format, of "\<pi> + \<psi>"] have False by force
  } note no_variant = this
  note no_variant' = no_variant[of _ _ _ _ "{}", simplified]
  { fix \<pi> u s
    fix z :: 'b
    assume less:"u \<succ> s" and "u = \<pi> \<bullet> s"
    with subst[OF less[unfolded this], of "\<lambda>_. Var z"] irrefl have False
      by (simp add: comp_def permute_term_subst_apply_term)
  } note less_perm = this
  from assms show ?thesis
  proof (cases)
    case (deduce s t u)
    with assms(3) obtain \<rho> where \<rho>:"(\<rho> \<bullet> t, \<rho> \<bullet> u) \<in> E'" unfolding litsim_defs by (auto simp:eqvt)
    define E\<^sub>0' where "E\<^sub>0' \<equiv> if (t, u) \<in> E\<^sub>0 then E' else E' - {(\<rho> \<bullet> t, \<rho> \<bullet> u)}"
    from Eaux[OF \<rho> _ assms(3)[unfolded deduce(1)] assms(6)[unfolded deduce(1)]] E\<^sub>0'_def assms(4)
    have litsim:"E\<^sub>0 \<doteq> E\<^sub>0'" by auto
    from litsim_rstep_eq[OF this] assms(2)[THEN litsim_rstep_eq] have rstep:"rstep (R\<^sub>0 \<union> E\<^sub>0\<^sup>\<leftrightarrow>) = rstep (R' \<union> E\<^sub>0'\<^sup>\<leftrightarrow>)"
      unfolding deduce(2) rstep_union rstep_converse by argo
    with deduce rstep_permute_iff have "(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> rstep (R' \<union> E\<^sub>0'\<^sup>\<leftrightarrow>)" "(\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> rstep (R' \<union> E\<^sub>0'\<^sup>\<leftrightarrow>)" by auto
    from oKBi.deduce[OF this] insert_absorb[OF \<rho>] have step:"(E\<^sub>0', R') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
      unfolding E\<^sub>0'_def by (cases "(t, u) \<in> E\<^sub>0", auto)
    from assms variant_free_trs_diff have vf:"variant_free_trs E\<^sub>0'" unfolding E\<^sub>0'_def by force
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R'], insert assms step litsim sym vf, unfold deduce(2), auto)
  next
    case (orientl s t)
    note o = this
    with assms(2) obtain \<rho> where \<rho>:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> R'" unfolding litsim_defs by (auto simp:eqvt)
    define R\<^sub>0' where "R\<^sub>0' \<equiv> if (s, t) \<in> R\<^sub>0 then R' else R' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    define E\<^sub>0' where "E\<^sub>0' \<equiv> E' \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    from Eaux[OF \<rho> _ assms(2)[unfolded o(2)] assms(7)[unfolded o(2)] assms(5)] R\<^sub>0'_def have litsimR:"R\<^sub>0 \<doteq> R\<^sub>0'" by auto
    from less_set_permute o(3) have less:"\<rho> \<bullet> s \<succ> \<rho> \<bullet> t" by auto
    note E'_variant = no_variant'[OF o(1) o(4) assms(3) assms(8)]
    then have E:"E' = E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" unfolding E\<^sub>0'_def by force
    have R:"R' = R\<^sub>0' \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" unfolding R\<^sub>0'_def using \<rho> by auto
    from oKBi.orientl[OF less, of E\<^sub>0' R\<^sub>0'] E\<^sub>0'_def have step:"(E\<^sub>0', R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E',R')" unfolding E R by auto
    from replace[OF assms(3)[THEN sym], of \<rho> s t] o sym insert_Diff have litsimE:"E\<^sub>0 \<doteq> E\<^sub>0'"
      unfolding E\<^sub>0'_def by fastforce
    from E'_variant variant_free_trs_insert[OF assms(4), of "\<rho> \<bullet> s" "\<rho> \<bullet> t"] term_pt.permute_plus
    have vfE:"variant_free_trs E\<^sub>0'" unfolding E\<^sub>0'_def by (metis Un_insert_right sup_bot.right_neutral)
    from assms variant_free_trs_diff have vfR:"variant_free_trs R\<^sub>0'" unfolding R\<^sub>0'_def by force
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R\<^sub>0'], insert step litsimR litsimE vfR vfE, auto)
  next
    case (orientr t s)
    note o = this
    with assms(2) obtain \<rho> where \<rho>:"(\<rho> \<bullet> t, \<rho> \<bullet> s) \<in> R'" unfolding litsim_defs by (auto simp:eqvt)
    define R\<^sub>0' where "R\<^sub>0' \<equiv> if (t, s) \<in> R\<^sub>0 then R' else R' - {(\<rho> \<bullet> t, \<rho> \<bullet> s)}"
    define E\<^sub>0' where "E\<^sub>0' \<equiv> E' \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    from Eaux[OF \<rho> _ assms(2)[unfolded o(2)] assms(7)[unfolded o(2)] assms(5)] R\<^sub>0'_def have litsimR:"R\<^sub>0 \<doteq> R\<^sub>0'" by auto
    from less_set_permute o(3) have less:"\<rho> \<bullet> t \<succ> \<rho> \<bullet> s" by auto
    note E'_variant = no_variant'[OF o(1) o(4) assms(3) assms(8)]
    then have E:"E' = E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" unfolding E\<^sub>0'_def by force
    have R:"R' = R\<^sub>0' \<union> {(\<rho> \<bullet> t, \<rho> \<bullet> s)}" unfolding R\<^sub>0'_def using \<rho> by auto
    from oKBi.orientr[OF less, of E\<^sub>0' R\<^sub>0'] E\<^sub>0'_def have step:"(E\<^sub>0', R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E',R')" unfolding E R by auto
    from replace[OF assms(3)[THEN sym], of \<rho> s t] o sym insert_Diff have litsimE:"E\<^sub>0 \<doteq> E\<^sub>0'"
      unfolding E\<^sub>0'_def by fastforce
    from E'_variant variant_free_trs_insert[OF assms(4), of "\<rho> \<bullet> s" "\<rho> \<bullet> t"] term_pt.permute_plus
    have vfE:"variant_free_trs E\<^sub>0'" unfolding E\<^sub>0'_def by (metis Un_insert_right sup_bot.right_neutral)
    from assms variant_free_trs_diff have vfR:"variant_free_trs R\<^sub>0'" unfolding R\<^sub>0'_def by force
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R\<^sub>0'], insert step litsimR litsimE vfR vfE, auto)
  next
    case (delete s)
    define E\<^sub>0' where "E\<^sub>0' \<equiv> E' \<union> {(s, s)}"
    note E'_variant = no_variant'[OF delete(1) delete(3) assms(3) assms(8)]
    from this[of 0] have "E\<^sub>0' - {(s, s)} = E'" using E\<^sub>0'_def by auto
    with oKBi.delete[of s E\<^sub>0'] have step:"(E\<^sub>0', R') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')" using E\<^sub>0'_def by auto
    from E'_variant variant_free_trs_insert[OF assms(4)]
    have vfE:"variant_free_trs E\<^sub>0'" unfolding E\<^sub>0'_def by auto
    from replace[OF assms(3)[THEN sym], of 0 s s] sym insert_Diff delete have litsimE:"E\<^sub>0 \<doteq> E\<^sub>0'"
      unfolding E\<^sub>0'_def by fastforce
    note facts = step assms litsimE vfE sym
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R'], insert facts, unfold delete(2), auto)
  next
    case (compose t u s)
    with assms(2) obtain \<rho> where \<rho>:"(\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> R'" unfolding litsim_defs by (auto simp:eqvt)
    define R\<^sub>0' where "R\<^sub>0' \<equiv> if (s, u) \<in> R\<^sub>0 then R' \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)} else R' - {(\<rho> \<bullet> s, \<rho> \<bullet> u)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    have mem:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> R\<^sub>0'" unfolding R\<^sub>0'_def by auto
    have litsim:"R\<^sub>0 \<doteq> R\<^sub>0'" proof(cases "(s, u) \<in> R\<^sub>0")
      case True
      with sym insert_absorb[OF True] insert_absorb[OF \<rho>] replace[OF sym[OF assms(2)], of \<rho> ] compose(4)
      show ?thesis unfolding compose(2) unfolding R\<^sub>0'_def
        by (smt Un_empty_right Un_insert_right insert_Diff insert_commute)
    next
      case False
      from False compose have R0:"R\<^sub>0 = R - {(s,u)} \<union> {(s,t)}" by (cases "t = u", auto)
      from litsim_diff1[OF assms(2)[THEN sym] assms(7) assms(5) _ _ \<rho>, of \<rho> "(s,u)"] compose(2)
      have "R - {(s, u)} \<doteq> R' - {(\<rho> \<bullet> s, \<rho> \<bullet> u)}" by (auto simp:eqvt)
      from litsim_insert[OF this] show "R\<^sub>0 \<doteq> R\<^sub>0'"
        unfolding R\<^sub>0'_def if_not_P[OF False] unfolding R0 by (auto simp:eqvt)
    qed
    from ostep_imp_less[OF _ compose(3)] assms(10) have "t \<succ> u" by auto
    from less_perm[OF this] have diff:"\<forall>\<pi>. (\<pi> \<bullet> s, \<pi> \<bullet> t) \<notin> {(s, u)}"
      by (metis Pair_inject singletonD term_pt.permute_minus_cancel(2))
    note no_st_variant =  no_variant[OF compose(2) diff compose(4) assms(2) assms(9)]
    have R':"R' = R\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> u)}"
      using \<rho> no_st_variant[of \<rho>] unfolding R\<^sub>0'_def by force
    have vf0:"variant_free_trs R\<^sub>0'" proof(cases "(s, u) \<in> R\<^sub>0")
      case True
      with no_st_variant variant_free_trs_insert[OF assms(5)] show ?thesis unfolding R\<^sub>0'_def
        by (smt Un_insert_right sup_bot.right_neutral term_pt.permute_plus)
    next
      case False
      with no_st_variant variant_free_trs_insert[OF variant_free_trs_diff[OF assms(5)]] show ?thesis
        unfolding R\<^sub>0'_def by (smt DiffE Un_insert_right sup_bot.comm_neutral term_pt.permute_plus)
    qed
    from litsim_diff1[OF litsim assms(9) vf0 _ compose(4) mem] have "R\<^sub>0 - {(s, t)} \<doteq> R\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" by (auto simp:eqvt)
    from ostep_permute_litsim[OF compose(3) _ this] sym[OF assms(3)]
    have step:"(\<rho> \<bullet> t, \<rho> \<bullet> u) \<in> ostep E' (R\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)})" unfolding compose(1) by auto
    from oKBi.compose[OF step mem] R' have "(E', R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E',R')" by auto
    note facts = this litsim assms(3)[unfolded compose(1), THEN sym] vf0 assms(4)
    show ?thesis by (rule exI[of _ E'], rule exI[of _ R\<^sub>0'], insert facts, auto)
  next
    case (simplifyl s u t)
    with assms(3) obtain \<rho> where \<rho>:"(\<rho> \<bullet> u, \<rho> \<bullet> t) \<in> E'" unfolding litsim_defs by (auto simp:eqvt)
    define E\<^sub>0' where "E\<^sub>0' \<equiv> if (u, t) \<in> E\<^sub>0 then E' \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)} else E' - {(\<rho> \<bullet> u, \<rho> \<bullet> t)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    have mem:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> E\<^sub>0'" unfolding E\<^sub>0'_def by auto
    have litsimE:"E\<^sub>0 \<doteq> E\<^sub>0'" proof(cases "(u, t) \<in> E\<^sub>0")
      case True
      with sym insert_absorb[OF True] insert_absorb[OF \<rho>] replace[OF sym[OF assms(3)], of \<rho> s t] simplifyl(4)
      show "E\<^sub>0 \<doteq> E\<^sub>0'" unfolding simplifyl(1) unfolding E\<^sub>0'_def
        by (smt Un_empty_right Un_insert_right insert_Diff insert_commute)
    next
      case False
      from False simplifyl have E0:"E\<^sub>0 = E - {(u,t)} \<union> {(s,t)}" by (cases "s = u", auto)
      from litsim_diff1[OF assms(3)[THEN sym] assms(6) assms(4) _ _ \<rho>, of \<rho> "(u,t)"] simplifyl(1)
      have "E - {(u, t)} \<doteq> E' - {(\<rho> \<bullet> u, \<rho> \<bullet> t)}" by (auto simp:eqvt)
      from litsim_insert[OF this] show "E\<^sub>0 \<doteq> E\<^sub>0'"
        unfolding E\<^sub>0'_def if_not_P[OF False] unfolding E0 by (auto simp:eqvt)
    qed
    note less = encstep1_less[OF simplifyl(3) assms(10)]
    from less_perm[OF this] have diff:"\<forall>\<pi>. (\<pi> \<bullet> s, \<pi> \<bullet> t) \<notin> {(u, t)}"
      by (metis Pair_inject singletonD term_pt.permute_minus_cancel(2))
    note no_st_variant = no_variant[OF simplifyl(1) diff simplifyl(4) assms(3) assms(8)]
    have E':"E' = E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)} \<union> {(\<rho> \<bullet> u, \<rho> \<bullet> t)}"
      using \<rho> no_st_variant[of \<rho>] unfolding E\<^sub>0'_def by force
    have vf0:"variant_free_trs E\<^sub>0'" proof(cases "(u, t) \<in> E\<^sub>0")
      case True
      with no_st_variant variant_free_trs_insert[OF assms(4)] show ?thesis unfolding E\<^sub>0'_def
        by (smt Un_insert_right sup_bot.right_neutral term_pt.permute_plus)
    next
      case False
      with no_st_variant variant_free_trs_insert[OF variant_free_trs_diff[OF assms(4)]] show ?thesis
        unfolding E\<^sub>0'_def by (smt DiffE Un_insert_right sup_bot.comm_neutral term_pt.permute_plus)
    qed
    from litsim_diff1[OF litsimE assms(8) vf0 _ simplifyl(4) mem] have "E\<^sub>0 - {(s, t)} \<doteq> E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" by (auto simp:eqvt)
    from encstep1_permute_litsim[OF simplifyl(3) this, of R'] sym[OF assms(2)]
    have step:"(\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> encstep1 (E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}) R'" unfolding simplifyl(2) by auto
    from oKBi.simplifyl[OF step mem] E' have "(E\<^sub>0', R') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E',R')" by auto
    note facts = this litsimE assms(2)[unfolded simplifyl(2), THEN sym] vf0 assms(5)
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R'], insert facts, auto)
  next
    case (simplifyr t u s)
    with assms(3) obtain \<rho> where \<rho>:"(\<rho> \<bullet> s, \<rho> \<bullet> u) \<in> E'" unfolding litsim_defs by (auto simp:eqvt)
    define E\<^sub>0' where "E\<^sub>0' \<equiv> if (s, u) \<in> E\<^sub>0 then E' \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)} else E' - {(\<rho> \<bullet> s, \<rho> \<bullet> u)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> t)}"
    have mem:"(\<rho> \<bullet> s, \<rho> \<bullet> t) \<in> E\<^sub>0'" unfolding E\<^sub>0'_def by auto
    have litsimE:"E\<^sub>0 \<doteq> E\<^sub>0'" proof(cases "(s, u) \<in> E\<^sub>0")
      case True
      with sym insert_absorb[OF True] insert_absorb[OF \<rho>] replace[OF sym[OF assms(3)], of \<rho> s t] simplifyr(4)
      show "E\<^sub>0 \<doteq> E\<^sub>0'" unfolding simplifyr(1) unfolding E\<^sub>0'_def
        by (smt Un_empty_right Un_insert_right insert_Diff insert_commute)
    next
      case False
      from False simplifyr have E0:"E\<^sub>0 = E - {(s,u)} \<union> {(s,t)}" by (cases "t = u", auto)
      from litsim_diff1[OF assms(3)[THEN sym] assms(6) assms(4) _ _ \<rho>, of \<rho> "(s,u)"] simplifyr(1)
      have "E - {(s, u)} \<doteq> E' - {(\<rho> \<bullet> s, \<rho> \<bullet> u)}" by (auto simp:eqvt)
      from litsim_insert[OF this] show "E\<^sub>0 \<doteq> E\<^sub>0'"
        unfolding E\<^sub>0'_def if_not_P[OF False] unfolding E0 by (auto simp:eqvt)
    qed
    note less = encstep1_less[OF simplifyr(3) assms(10)]
    from less_perm[OF this] have diff:"\<forall>\<pi>. (\<pi> \<bullet> s, \<pi> \<bullet> t) \<notin> {(s, u)}"
      by (metis Pair_inject singletonD term_pt.permute_minus_cancel(2))
    note no_st_variant = no_variant[OF simplifyr(1) diff simplifyr(4) assms(3) assms(8)]
    have E':"E' = E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)} \<union> {(\<rho> \<bullet> s, \<rho> \<bullet> u)}"
      using \<rho> no_st_variant[of \<rho>] unfolding E\<^sub>0'_def by force
    have vf0:"variant_free_trs E\<^sub>0'" proof(cases "(s, u) \<in> E\<^sub>0")
      case True
      with no_st_variant variant_free_trs_insert[OF assms(4)] show ?thesis unfolding E\<^sub>0'_def
        by (smt Un_insert_right sup_bot.right_neutral term_pt.permute_plus)
    next
      case False
      with no_st_variant variant_free_trs_insert[OF variant_free_trs_diff[OF assms(4)]] show ?thesis
        unfolding E\<^sub>0'_def by (smt DiffE Un_insert_right sup_bot.comm_neutral term_pt.permute_plus)
    qed
    from litsim_diff1[OF litsimE assms(8) vf0 _ simplifyr(4) mem] have "E\<^sub>0 - {(s, t)} \<doteq> E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}" by (auto simp:eqvt)
    from encstep1_permute_litsim[OF simplifyr(3) this, of R'] sym[OF assms(2)]
    have step:"(\<rho> \<bullet> t, \<rho> \<bullet> u) \<in> encstep1 (E\<^sub>0' - {(\<rho> \<bullet> s, \<rho> \<bullet> t)}) R'" unfolding simplifyr(2) by auto
    from oKBi.simplifyr[OF step mem] E' have "(E\<^sub>0', R') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E',R')" by auto
    note facts = this litsimE assms(2)[unfolded simplifyr(2), THEN sym] vf0 assms(5)
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R'], insert facts, auto)
  next
    case (collapse t u s)
    note c = this
    with assms(3) obtain \<rho> where \<rho>:"(\<rho> \<bullet> u, \<rho> \<bullet> s) \<in> E'" unfolding litsim_defs by (auto simp:eqvt)
    define E\<^sub>0' where "E\<^sub>0' \<equiv> if (u, s) \<in> E\<^sub>0 then E' else E' - {(\<rho> \<bullet> u, \<rho> \<bullet> s)}"
    define R\<^sub>0' where "R\<^sub>0' \<equiv> R' \<union> {(\<rho> \<bullet> t, \<rho> \<bullet> s)}"
    from Eaux[OF \<rho> _ assms(3)[unfolded c(1)] assms(6)[unfolded c(1)] assms(4)] E\<^sub>0'_def have litsimE:"E\<^sub>0 \<doteq> E\<^sub>0'" by auto
    from c have R0:"R\<^sub>0 = R \<union> {(t,s)}" by fast
    from litsim_insert[OF sym[OF assms(2)]] have litsimR:"R\<^sub>0 \<doteq> R\<^sub>0'" unfolding R\<^sub>0'_def R0 by (auto simp:eqvt)
    from variant_free_trs_diff assms(4) have vfE:"variant_free_trs E\<^sub>0'" unfolding E\<^sub>0'_def by auto
    note no_variant' = no_variant'[OF c(2) c(4) assms(2) assms(9)]
    from no_variant' variant_free_trs_insert[OF assms(5), of "\<rho> \<bullet> t" "\<rho> \<bullet> s"] have vfR:"variant_free_trs R\<^sub>0'"
      unfolding R\<^sub>0'_def using term_pt.permute_plus by (metis Un_insert_right sup_bot.right_neutral)
    from no_variant' have R:"R' = R\<^sub>0' - {(\<rho> \<bullet> t, \<rho> \<bullet> s)}" unfolding R\<^sub>0'_def by force
    have E:"E' = E\<^sub>0' \<union> {(\<rho> \<bullet> u, \<rho> \<bullet> s)}" unfolding E\<^sub>0'_def using \<rho> by auto
    from assms(2)[unfolded R c(2)] sym have "R\<^sub>0 - {(t, s)} \<doteq> R\<^sub>0' - {(\<rho> \<bullet> t, \<rho> \<bullet> s)}" by auto
    from encstep2_permute_litsim[OF collapse(3) litsimE this]
    have ostep:"(\<rho> \<bullet> t, \<rho> \<bullet> u) \<in> encstep2 E\<^sub>0' (R\<^sub>0' - {(\<rho> \<bullet> t, \<rho> \<bullet> s)})" by auto
    from oKBi.collapse[OF ostep] R\<^sub>0'_def have step:"(E\<^sub>0', R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E',R')" unfolding E R by auto
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ R\<^sub>0'], insert step litsimR litsimE vfR vfE, auto)
  qed
qed

lemma oKB_permute_step_oKB_step:
  assumes "(E\<^sub>0, R\<^sub>0) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>\<pi> (E\<^sub>1, R\<^sub>1)" and "E\<^sub>0 \<doteq> E\<^sub>0'" and "R\<^sub>0 \<doteq> R\<^sub>0'" and
    "variant_free_trs E\<^sub>0" and "variant_free_trs E\<^sub>0'" and
    "variant_free_trs R\<^sub>0" and "variant_free_trs R\<^sub>0'"
  shows "\<exists>E\<^sub>1' R\<^sub>1'. (E\<^sub>0', R\<^sub>0') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>1', R\<^sub>1') \<and> E\<^sub>1 \<doteq> E\<^sub>1' \<and> R\<^sub>1 \<doteq> R\<^sub>1'"
proof-
  note sym = subsumable_trs.litsim_sym
  note refl = subsumable_trs.litsim_refl
  have insert:"\<And>S S' \<pi> s t. S' \<doteq> S \<Longrightarrow> S \<union> {(\<pi> \<bullet> s, \<pi> \<bullet> t)} \<doteq> S' \<union> {(s, t)}"
    using litsim_insert[OF _ rule_pt.permute_prod_eqvt[symmetric]] sym by fastforce
  note insert_ER = insert[OF sym[OF assms(2)]] insert[OF sym[OF assms(3)]]
  note litsim = assms(2) assms(3) litsim_symcl litsim_union
  note diff_E = litsim_diff1[OF assms(2) assms(4) assms(5)]
  note diff_R = litsim_diff1[OF assms(3) assms(6) assms(7)]
  show ?thesis using assms(1)
  proof (cases)
    case (deduce s t u \<pi>)
    have "rstep (R\<^sub>0 \<union> E\<^sub>0\<^sup>\<leftrightarrow>) = rstep (R\<^sub>0' \<union> E\<^sub>0'\<^sup>\<leftrightarrow>)" by (rule litsim_rstep_eq, insert litsim, fast)
    note step = oKBi.deduce[OF deduce(3)[unfolded this] deduce(4)[unfolded this]] insert_ER assms(3)
    show ?thesis by (rule exI[of _ "E\<^sub>0' \<union> {(t, u)}"], rule exI[of _ R\<^sub>0'], insert step, unfold deduce, auto)
  next
    case (orientl s t \<pi>)
    from litsim_mem[OF assms(2) this(4)] obtain \<psi> where mem:"(\<psi> \<bullet> s, \<psi> \<bullet> t) \<in> E\<^sub>0'" by (auto simp:eqvt)
    from orientl(3) have "\<psi> \<bullet> s \<succ> \<psi> \<bullet> t" by (metis subst term_apply_subst_Var_Rep_perm)
    note step = oKBi.orientl[OF this mem, of R\<^sub>0']
    let ?E = "E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)}" and ?R = "R\<^sub>0' \<union> {(\<psi> \<bullet> s, \<psi> \<bullet> t)}"
    from diff_E[OF _ orientl(4) mem] have E:"E\<^sub>1 \<doteq> ?E" unfolding orientl(1)  by (auto simp:eqvt)
    from insert_ER(2)[of "\<pi> - \<psi>" "\<psi> \<bullet> s" "\<psi> \<bullet> t"] have R:"R\<^sub>1 \<doteq> ?R" unfolding orientl(2) by auto
    show ?thesis by (rule exI[of _ ?E], rule exI[of _ ?R], insert step E R, auto)
  next
    case (orientr t s \<pi>)
    from litsim_mem[OF assms(2) this(4)] obtain \<psi> where mem:"(\<psi> \<bullet> s, \<psi> \<bullet> t) \<in> E\<^sub>0'" by (auto simp:eqvt)
    from orientr(3) have "\<psi> \<bullet> t \<succ> \<psi> \<bullet> s" by (metis subst term_apply_subst_Var_Rep_perm)
    note step = oKBi.orientr[OF this mem, of R\<^sub>0']
    let ?E = "E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)}" and ?R = "R\<^sub>0' \<union> {(\<psi> \<bullet> t, \<psi> \<bullet> s)}"
    from diff_E[OF _ orientr(4) mem] have E:"E\<^sub>1 \<doteq> ?E" unfolding orientr(1)  by (auto simp:eqvt)
    from insert_ER(2)[of "\<pi> - \<psi>" "\<psi> \<bullet> t" "\<psi> \<bullet> s"] have R:"R\<^sub>1 \<doteq> ?R" unfolding orientr(2) by auto
    show ?thesis by (rule exI[of _ ?E], rule exI[of _ ?R], insert step E R, auto)
  next
    case (delete s)
    from litsim_mem[OF assms(2) this(3)] obtain \<psi> where mem:"(\<psi> \<bullet> s, \<psi> \<bullet> s) \<in> E\<^sub>0'" by (auto simp:eqvt)
    let ?E = "E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> s)}"
    from diff_E[OF _ _ mem] have E:"E\<^sub>1 \<doteq> ?E" using delete by (auto simp:eqvt)
    note step = oKBi.delete[OF mem, of R\<^sub>0']
    show ?thesis by (rule exI[of _ ?E], rule exI[of _ R\<^sub>0'], insert E step delete(2) assms(3), auto)
  next
    case (compose t u s \<pi>)
    from litsim_mem[OF assms(3) this(4)] obtain \<psi> where mem:"(\<psi> \<bullet> s, \<psi> \<bullet> t) \<in> R\<^sub>0'" by (auto simp:eqvt)
    from diff_R[OF _ compose(4) mem] have sim:"R\<^sub>0 - {(s, t)} \<doteq> R\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)}" by (auto simp:eqvt)
    note ostep = ostep_permute_litsim[OF compose(3) assms(2) this]
    then have "(\<psi> \<bullet> t, \<psi> \<bullet> u) \<in> ostep E\<^sub>0' (R\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)})" by (auto simp:eqvt)
    note step = oKBi.compose[OF this mem]
    let ?R = "R\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)} \<union> {(\<psi> \<bullet> s, \<psi> \<bullet> u)}"
    from insert[OF sim[THEN sym], of "\<pi> - \<psi>" "\<psi> \<bullet> s" "\<psi> \<bullet> u"] have R:"R\<^sub>1 \<doteq> ?R" unfolding compose(2) by auto
    show ?thesis by (rule exI[of _ E\<^sub>0'], rule exI[of _ ?R], insert step R compose(1) assms(2), auto)
  next
    case (simplifyl s u t \<pi>)
    from litsim_mem[OF assms(2) this(4)] obtain \<psi> where mem:"(\<psi> \<bullet> s, \<psi> \<bullet> t) \<in> E\<^sub>0'" by (auto simp:eqvt)
    from diff_E[OF _ simplifyl(4) mem] have sim:"E\<^sub>0 - {(s, t)} \<doteq> E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)}" by (auto simp:eqvt)
    note ostep = encstep1_permute_litsim[OF] simplifyl(3) this assms(3)
    then have "(\<psi> \<bullet> s, \<psi> \<bullet> u) \<in> encstep1 (E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)}) R\<^sub>0'" by (auto simp:eqvt)
    note step = oKBi.simplifyl[OF this mem]
    let ?E = "E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)} \<union> {(\<psi> \<bullet> u, \<psi> \<bullet> t)}"
    from insert[OF sim[THEN sym], of "\<pi> - \<psi>" "\<psi> \<bullet> u" "\<psi> \<bullet> t"] have E:"E\<^sub>1 \<doteq> ?E" unfolding simplifyl(1) by auto
    show ?thesis by (rule exI[of _ ?E], rule exI[of _ R\<^sub>0'], insert step E simplifyl(2) assms(3), auto)
  next
    case (simplifyr t u s \<pi>)
    from litsim_mem[OF assms(2) this(4)] obtain \<psi> where mem:"(\<psi> \<bullet> s, \<psi> \<bullet> t) \<in> E\<^sub>0'" by (auto simp:eqvt)
    from diff_E[OF _ simplifyr(4) mem] have sim:"E\<^sub>0 - {(s, t)} \<doteq> E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)}" by (auto simp:eqvt)
    note ostep = encstep1_permute_litsim[OF simplifyr(3) this assms(3)]
    then have "(\<psi> \<bullet> t, \<psi> \<bullet> u) \<in> encstep1 (E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)}) R\<^sub>0'" by (auto simp:eqvt)
    note step = oKBi.simplifyr[OF this mem]
    let ?E = "E\<^sub>0' - {(\<psi> \<bullet> s, \<psi> \<bullet> t)} \<union> {(\<psi> \<bullet> s, \<psi> \<bullet> u)}"
    from insert[OF sim[THEN sym], of "\<pi> - \<psi>" "\<psi> \<bullet> s" "\<psi> \<bullet> u"] have E:"E\<^sub>1 \<doteq> ?E" unfolding simplifyr(1) by auto
    show ?thesis by (rule exI[of _ ?E], rule exI[of _ R\<^sub>0'], insert step E simplifyr(2) assms(3), auto)
  next
    case (collapse t u s \<pi>)
    from litsim_mem[OF assms(3) this(4)] obtain \<psi> where mem:"(\<psi> \<bullet> t, \<psi> \<bullet> s) \<in> R\<^sub>0'" by (auto simp:eqvt)
    let ?E = "E\<^sub>0' \<union> {(\<psi> \<bullet> u, \<psi> \<bullet> s)}"
    let ?R = "R\<^sub>0' - {(\<psi> \<bullet> t, \<psi> \<bullet> s)}"
    from diff_R[OF _ collapse(4) mem] have R:"R\<^sub>0 - {(t, s)} \<doteq> ?R" by (auto simp:eqvt)
    note ostep = encstep2_permute_litsim[OF collapse(3) assms(2) this]
    then have "(\<psi> \<bullet> t, \<psi> \<bullet> u) \<in> encstep2 E\<^sub>0' ?R" by (auto simp:eqvt)
    note step = oKBi.collapse[OF this mem]
    from insert_ER(1)[of "\<pi> - \<psi>" "\<psi> \<bullet> u" "\<psi> \<bullet> s"] have E:"E\<^sub>1 \<doteq> ?E" unfolding collapse(1) by auto
    show ?thesis by (rule exI[of _ ?E], rule exI[of _ ?R], insert step E R collapse(2), auto)
  qed
qed

lemma oKB_run_rename:
  assumes "\<forall>i < n. (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E (Suc i), R (Suc i))" and "\<forall>i \<le> n. variant_free_trs (E i) \<and> variant_free_trs (R i)"
    and "Rf \<doteq> R n" and "Ef \<doteq> E n" and "variant_free_trs Ef" and "variant_free_trs Rf" and "R 0 \<subseteq> {\<succ>}"
  shows "\<exists>E' R'.((\<forall>i < n. (E' i, R' i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E' (Suc i), R' (Suc i))) \<and>
               (\<forall>i \<le> n. variant_free_trs (E' i) \<and> variant_free_trs (R' i) \<and> E i \<doteq> E' i \<and> R i \<doteq> R' i)) \<and>
               E' n = Ef \<and> R' n = Rf"
  using assms
proof(induct n arbitrary: Ef Rf)
  case 0
  show ?case by (rule exI[of _ "\<lambda>i. Ef"], rule exI[of _ "\<lambda>i. Rf"], insert subsumable_trs.litsim_sym 0, auto)
next
  case (Suc n)
  note eqrel = subsumable_trs.litsim_refl subsumable_trs.litsim_trans subsumable_trs.litsim_sym
  from Suc(2) have step:"(E n, R n) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E (Suc n), R (Suc n))" by auto
  from Suc(3) have vf:"variant_free_trs (E (Suc n))" "variant_free_trs (R (Suc n))" by auto
  from Suc(3) have vf':"variant_free_trs (E n)" "variant_free_trs (R n)" by auto
  from Suc(2) have "(oKBi ^^ n) (E 0, R 0) (E n, R n)" unfolding relpowp_fun_conv by auto
  from relpowp_imp_rtranclp[OF this] Suc(8) oKBi_rtrancl_less have "R n \<subseteq> {\<succ>}" by auto
  with step_implies_litsim_step[OF step Suc(4) Suc(5) Suc(6) Suc(7) vf vf'] eqrel obtain En Rn where
    ERn:"(En, Rn) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (Ef, Rf)" "Rn \<doteq> R n" "En \<doteq> E n" "variant_free_trs En" "variant_free_trs Rn" by blast
  from Suc have "\<forall>i < n. (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E (Suc i), R (Suc i))" and "\<forall>i \<le> n. variant_free_trs (E i) \<and> variant_free_trs (R i)" by auto
  from Suc(1)[OF this ERn(2) ERn(3) ERn(4) ERn(5) Suc(8)] obtain E' R' where prefix:
    "En = E' n" "Rn = R' n" "\<forall>i < n. (E' i, R' i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E' (Suc i), R' (Suc i))"
    "\<forall>i \<le> n. variant_free_trs (E' i) \<and> variant_free_trs (R' i) \<and> E i \<doteq> E' i \<and> R i \<doteq> R' i" by auto
  let ?E = "\<lambda>i. if i \<le> n then E' i else Ef"
  let ?R = "\<lambda>i. if i \<le> n then R' i else Rf"
  { fix i
    assume "i \<le> Suc n"
    from this[unfolded le_eq_less_or_eq] prefix(4)[rule_format, of i] Suc subsumable_trs.litsim_sym
    have "variant_free_trs (?E i) \<and> variant_free_trs (?R i) \<and> E i \<doteq> ?E i \<and> R i \<doteq> ?R i"
    by (cases "i \<le> n", auto)
  } note vf = this
  { fix i
    assume "i < Suc n"
    from this[unfolded le_eq_less_or_eq] prefix(3) ERn(1) have "(?E i, ?R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (?E (Suc i), ?R (Suc i))"
      unfolding prefix by (cases "i = n", auto)
  } note steps = this
  show ?case by (rule exI[of _ ?E], rule exI[of _ ?R], insert steps vf, auto)
qed

lemma R_less_litsim_R_less:
  assumes "R \<subseteq> {\<succ>}" and "R' \<doteq> R"
  shows "R' \<subseteq> {\<succ>}"
proof
  fix l r
  assume "(l,r) \<in> R'"
  with assms(2)[unfolded subsumable_trs.litsim_def subsumeseq_trs_def]
    obtain \<pi> where "(\<pi> \<bullet> l,\<pi> \<bullet> r) \<in> R" by (auto simp:eqvt)
  then have "\<pi> \<bullet> l \<succ> \<pi> \<bullet> r" using assms(1) by blast
  with less_set_permute show "(l, r) \<in> {\<succ>}" using eqvt by blast
qed

lemma oKB_permute_run:
  assumes "\<forall>i < n. (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>\<pi> (E (Suc i), R (Suc i))" and "\<forall>i \<le> n. variant_free_trs (E i) \<and> variant_free_trs (R i)" and "R 0 \<subseteq> {\<succ>}"
  shows "\<exists>E' R'.((\<forall>i < n. (E' i, R' i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E' (Suc i), R' (Suc i))) \<and> (\<forall>i \<le> n. variant_free_trs (E' i) \<and> variant_free_trs (R' i) \<and> E i \<doteq> E' i \<and> R i \<doteq> R' i))"
  using assms(1) assms(2)
proof(induct n)
  case 0
  show ?case by (rule exI[of _ "E"], rule exI[of _ "R"], insert subsumable_trs.litsim_refl 0, auto)
next
  case (Suc n)
  note eqrel = subsumable_trs.litsim_refl subsumable_trs.litsim_trans subsumable_trs.litsim_sym
  from Suc have all:"\<forall>i < n. (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>\<pi> (E (Suc i), R (Suc i))" "\<forall>i \<le> n. variant_free_trs (E i) \<and> variant_free_trs (R i)" by auto
  from Suc(1)[OF this] obtain E' R' where steps:"\<forall>i < n. (E' i, R' i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E' (Suc i), R' (Suc i))"
    "\<forall>i \<le> n. variant_free_trs (E' i) \<and> variant_free_trs (R' i) \<and> E i \<doteq> E' i \<and> R i \<doteq> R' i" by blast
  from R_less_litsim_R_less[OF assms(3)] steps(2) eqrel have less:"R' 0 \<subseteq> {\<succ>}" by blast
  from steps(2) have litsim:"E n \<doteq> E' n" "R n \<doteq> R' n" by auto
  from Suc(3) have vf:"variant_free_trs (E n)" "variant_free_trs (R n)" by auto
  from steps(2) have vf':"variant_free_trs (E' n)" "variant_free_trs (R' n)" by auto
  from Suc(2) have "(E n, R n) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>\<pi> (E (Suc n), R (Suc n))" by auto
  from oKB_permute_step_oKB_step[OF this litsim vf(1) vf'(1) vf(2) vf'(2)] obtain Ef Rf
    where t:"(E' n, R' n) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (Ef, Rf)" "R (Suc n) \<doteq> Rf" "E (Suc n) \<doteq> Ef" by auto
  from oKB_step_variant_free[OF this(1) vf'] obtain E\<^sub>n'' R\<^sub>n'' Ef'' Rf'' where
    s:"(E\<^sub>n'', R\<^sub>n'') \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (Ef'', Rf'')" "E\<^sub>n'' \<doteq> E' n" "R\<^sub>n'' \<doteq> R' n" "Ef'' \<doteq> Ef" "Rf'' \<doteq> Rf"
    "variant_free_trs E\<^sub>n''" "variant_free_trs R\<^sub>n''" "variant_free_trs Ef''" "variant_free_trs Rf''" by auto
  from oKB_run_rename[OF steps(1) _ s(3) s(2) s(6) s(7) less] steps(2) obtain E'' R'' where prefix:
    "\<forall>i < n. (E'' i, R'' i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E'' (Suc i), R'' (Suc i))"
    "\<forall>i \<le> n. variant_free_trs (E'' i) \<and> variant_free_trs (R'' i) \<and> E' i \<doteq> E'' i \<and> R' i \<doteq> R'' i" "E'' n = E\<^sub>n'' \<and> R'' n = R\<^sub>n''"
    by auto
  let ?E = "\<lambda>i. if i \<le> n then E'' i else Ef''"
  let ?R = "\<lambda>i. if i \<le> n then R'' i else Rf''"
  { fix i
    assume i:"i \<le> Suc n"
    have "variant_free_trs (?E i) \<and> variant_free_trs (?R i) \<and> E i \<doteq> ?E i \<and> R i \<doteq> ?R i" proof(cases "i = Suc n")
      case True
      from s(4) s(5) t(2) t(3) eqrel have "E (Suc n) \<doteq> Ef'' \<and> R (Suc n) \<doteq> Rf''" by fast
      with s show ?thesis unfolding True by simp
    next
      case False
      with i have i:"i \<le> n" by auto
      with prefix(2)[rule_format, of i] steps(2)[rule_format, of i] eqrel have "E i \<doteq> E'' i \<and> R i \<doteq> R'' i" by fast
      with i prefix(2)[rule_format, of i] show ?thesis by simp
    qed
  } note vf = this
  { fix i
    assume "i < Suc n"
    from this[unfolded le_eq_less_or_eq] prefix(3) s(1) prefix(1)[rule_format, of i]
      have "(?E i, ?R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (?E (Suc i), ?R (Suc i))" by (cases "i = n", auto)
  } note steps = this
  show ?case by (rule exI[of _ ?E], rule exI[of _ ?R], insert steps vf, auto)
qed
end

definition "E_ord ord E = {(s \<cdot> \<sigma>, t \<cdot> \<sigma>) | s t \<sigma>. (s, t) \<in> E\<^sup>\<leftrightarrow> \<and> ord (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)}"

lemma E_ord_mono: "E \<subseteq> E' \<Longrightarrow> E_ord ord E \<subseteq> E_ord ord E'" unfolding E_ord_def by auto

context ordered_completion
begin

context
  fixes \<R> \<E> :: "('a, 'b) trs"
  assumes rules: "\<R> \<subseteq> {\<succ>}"
begin

abbreviation "\<S> \<equiv> \<R> \<union> E_ord (\<succ>) \<E>"

lemma rstep_S_ordstep:
  assumes "(s, t) \<in> rstep \<S>"
  shows "(s, t) \<in> ordstep {\<succ>} \<S>"
  using assms
proof (cases rule: rstepE)
  case (rstep C \<sigma> l r)
  then show ?thesis
    using rules
    by (intro ordstep.intros [where C = C and l = l and r = r and \<sigma> = \<sigma>])
      (auto dest: subst simp: E_ord_def)
qed

lemma rstep_S_rstep_EW: "(s, t) \<in> rstep \<S> \<Longrightarrow> (s, t) \<in> rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)"
  unfolding E_ord_def by fast

lemma ordstep_subset_S:
  "ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>) \<subseteq> ordstep {\<succ>} \<S>"
proof -
  { fix s t assume "(s, t) \<in> ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)"
    then obtain C l r \<sigma> where "(l, r) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>"
      and [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" by (cases) auto
    then consider "(l, r) \<in> \<R>" | "(l, r) \<in> \<E>\<^sup>\<leftrightarrow>" by blast
    then have "(s, t) \<in> ordstep {\<succ>} \<S>"
    proof (cases)
      case 1
      then show ?thesis by (auto intro: ordstep.intros)
    next
      case 2
      then show ?thesis
        by (intro ordstep.intros [where C = C and \<sigma> = Var and l = "l \<cdot> \<sigma>" and r = "r \<cdot> \<sigma>"])
          (force simp: E_ord_def)+
    qed }
  then show ?thesis by auto
qed

lemma NF_ordstep_S_subset: "NF (ordstep {\<succ>} \<S>) \<subseteq> NF (ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))"
  using ordstep_subset_S by blast

lemma ordstep_S_conv [simp]:
  "ordstep {\<succ>} \<S> = rstep \<S>"
  using rstep_S_ordstep by (auto elim: ordstep.cases)

lemma S_less:"rstep \<S> \<subseteq> {\<succ>}"
  using ordstep_S_conv ordstep_imp_ord[OF ctxt_closed_less] by blast

end
end

lemma (in fgtotal_reduction_order) FGROUND_rstep_ordstep:
  "FGROUND F (rstep (RR \<union> EE\<^sup>\<leftrightarrow>)) \<subseteq> (FGROUND F (rstep (RR \<union> E_ord (\<succ>) EE)))\<^sup>\<leftrightarrow>\<^sup>*"
proof
  fix s t
  assume step: "(s, t) \<in> FGROUND F (rstep (RR \<union> EE\<^sup>\<leftrightarrow>))"
  then obtain C l r \<sigma> where C: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l, r) \<in> RR \<union> EE\<^sup>\<leftrightarrow>" "fground F s" "fground F t"
    unfolding FGROUND_def by auto
  show "(s, t) \<in> (FGROUND F (rstep (RR \<union> E_ord (\<succ>) EE)))\<^sup>\<leftrightarrow>\<^sup>*"
  proof (cases "(l, r) \<in> RR")
    case True
    with step have "(s, t) \<in> (rstep (RR \<union> E_ord (\<succ>) EE))" unfolding C rstep_union by blast
    with C(4) C(5) show ?thesis unfolding FGROUND_def by auto
  next
    case False
    with step rstep_union C(3) have in_E: "(l, r) \<in> EE\<^sup>\<leftrightarrow>" unfolding C by auto
    from C(4) C(5) have g': "fground F (l \<cdot> \<sigma>)" "fground F (r \<cdot> \<sigma>)" unfolding C by (auto simp:fground_def)
    from fgtotal [OF g'] consider " l \<cdot> \<sigma> = r \<cdot> \<sigma>" | "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" | "r \<cdot> \<sigma> \<succ> l \<cdot> \<sigma>" by auto
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis unfolding C by auto
    next
      case 2
      with in_E have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> E_ord (\<succ>) EE" unfolding E_ord_def mem_Collect_eq by auto
      then have "(s, t) \<in> rstep (RR \<union> E_ord (\<succ>) EE)" unfolding C by auto
      with C(4) C(5) show ?thesis unfolding FGROUND_def by auto
    next
      case 3
      with in_E have "(r \<cdot> \<sigma>, l \<cdot> \<sigma>) \<in> E_ord (\<succ>) EE" unfolding E_ord_def mem_Collect_eq by auto
      then have "(t, s) \<in> rstep (RR \<union> E_ord (\<succ>) EE)" unfolding C by auto
      with C(4) C(5) show ?thesis unfolding FGROUND_def by auto
    qed
  qed
qed

locale gtotal_okb_irun_inf =
  ordered_completion_inf less +
  gtotal_okb_irun less for less :: "('a, 'b::infinite) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
begin

sublocale fgtotal_reduction_order_inf less UNIV ..

definition "PCP_ext RR = {(u, v) | r r' p \<mu> u v.
    ooverlap {\<succ>} RR r r' p \<mu> u v \<and>
    (\<forall>u \<lhd> fst r \<cdot> \<mu>. u \<in> NF (ordstep {\<succ>} RR))}"

context
  fixes \<R> \<E> :: "('a, 'b) trs"
  assumes rules: "\<R> \<subseteq> {\<succ>}"
begin

lemma perm_R_less: "\<pi> \<bullet> (l, r) \<in> \<R> \<Longrightarrow> l \<succ> r"
  using rules by (auto simp: eqvt perm_less)


lemma perm_S_ordstep:
  assumes "\<pi> \<bullet> (s, t) \<in> \<S> \<R> \<E>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ordstep {\<succ>} (\<S> \<R> \<E>)"
  using assms
  by (intro ordstep.intros [where C = \<box> and \<sigma> = "sop (-\<pi>) \<circ>\<^sub>s \<sigma>" and l = "\<pi> \<bullet> s" and r = "\<pi> \<bullet> t"])
    (auto simp: eqvt perm_R_less E_ord_def subst, (metis perm_less subst)+)

lemma perm_R_ordstep:
  assumes "\<pi> \<bullet> (s, t) \<in> \<R>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)"
  using assms
  by (intro ordstep.intros [where C = \<box> and \<sigma> = "sop (-\<pi>) \<circ>\<^sub>s \<sigma>" and l = "\<pi> \<bullet> s" and r = "\<pi> \<bullet> t"])
    (auto simp: eqvt perm_R_less subst)

lemma E_ordstep:
  assumes "(s, t) \<in> \<E>\<^sup>\<leftrightarrow>" and "s \<cdot> \<sigma> \<succ> t \<cdot> \<sigma>"
  shows "(s \<cdot> \<sigma> \<circ>\<^sub>s \<tau>, t \<cdot> \<sigma> \<circ>\<^sub>s \<tau>) \<in> ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)"
  using assms
  by (intro ordstep.intros [where C = \<box> and \<sigma> = "\<sigma> \<circ>\<^sub>s \<tau>" and l = "s" and r = "t"])
    (auto simp: subst)

lemma PCP_xPCP:
  assumes "ground s" and "ground t"
    and "(s, t) \<in> (rstep (PCP (\<S> \<R> \<E>)))\<^sup>\<leftrightarrow>"
  shows "(s, t) \<in> (rstep (PCP_ext (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)))\<^sup>\<leftrightarrow> \<union> (rstep (\<S> \<R> \<E>))\<^sup>\<down>"
    (is "_ \<in> ?R")
proof -
  have S: "\<And>s t. (s, t) \<in> (\<S> \<R> \<E>) \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> (\<S> \<R> \<E>)"
    using rules by (auto simp: E_ord_def)
  have RE: "\<And>s t. (s, t) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow> \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>"
    using rules by (auto)
  let ?S = "ordstep {\<succ>} (\<S> \<R> \<E>)"
  let ?Eo = "E_ord (\<succ>) \<E>"
  let ?RE = "ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)"
  { fix s t and \<sigma> :: "('a, 'b) subst"
    assume "(s, t) \<in> PCP (\<S> \<R> \<E>)" and ground: "ground (s \<cdot> \<sigma>)" "ground (t \<cdot> \<sigma>)"
    then obtain \<mu> l\<^sub>1 r\<^sub>1 p l\<^sub>2 r\<^sub>2 where o: "overlap (\<S> \<R> \<E>) (\<S> \<R> \<E>) (l\<^sub>1, r\<^sub>1) p (l\<^sub>2, r\<^sub>2)"
      and "the_mgu l\<^sub>1 (l\<^sub>2 |_ p) = \<mu>"
      and s: "s = replace_at l\<^sub>2 p r\<^sub>1 \<cdot> \<mu>"
      and t: "t = r\<^sub>2 \<cdot> \<mu>"
      and NF: "\<forall>u \<lhd> l\<^sub>1 \<cdot> \<mu>. u \<in> NF (rstep (\<S> \<R> \<E>))"
      by (auto simp: PCP_def the_mgu_def mgu_def split: option.splits)
    then have mgu: "mgu l\<^sub>1 (l\<^sub>2 |_ p) = Some \<mu>"
      by (auto simp: the_mgu_def unifiers_def overlap_def split: option.splits dest!: mgu_complete)
    from mgu_sound [OF this]
    have "l\<^sub>1 \<cdot> \<mu> = (l\<^sub>2 |_ p) \<cdot> \<mu>" by (auto simp: is_imgu_def)
    moreover
    define C and \<tau> where "C = ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<mu>) \<cdot>\<^sub>c \<sigma>" and "\<tau> = \<mu> \<circ>\<^sub>s \<sigma>"
    ultimately
    have eq: "\<box>\<langle>l\<^sub>2 \<cdot> \<tau>\<rangle> = C\<langle>l\<^sub>1 \<cdot> \<tau>\<rangle>"
      using o
      by simp (metis ctxt_of_pos_term_subst ctxt_supt_id fst_conv overlap_source_eq(1) subst_apply_term_ctxt_apply_distrib)

    have s': "s \<cdot> \<sigma> = C\<langle>r\<^sub>1 \<cdot> \<tau>\<rangle>"
      using o by (simp add: s C_def \<tau>_def overlap_def ctxt_of_pos_term_subst fun_poss_imp_poss)

    have t': "t \<cdot> \<sigma> = \<box>\<langle>r\<^sub>2 \<cdot> \<tau>\<rangle>" by (simp add: t \<tau>_def)

    have p: "p \<in> fun_poss l\<^sub>2" using o by (auto simp: overlap_def)
    then have [simp]: "hole_pos C = p" by (auto simp: C_def fun_poss_imp_poss)

    have disj: "vars_rule (l\<^sub>2, r\<^sub>2) \<inter> vars_rule (l\<^sub>1, r\<^sub>1) = {}" using o by (auto simp: overlap_def)
    note Sconv[simp] = ordstep_S_conv[OF rules]
    note non_ooverlap_GROUND_joinable = non_ooverlap_FGROUND_joinable[unfolded fground_UNIV]

    { fix \<pi>\<^sub>1 and \<pi>\<^sub>2 assume *: "\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> \<R>" "\<pi>\<^sub>2 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> \<R>"
      then have rule1: "\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> \<S> \<R> \<E>" and rule2: "\<pi>\<^sub>2 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> \<S> \<R> \<E>" by auto
      have "(s \<cdot> \<sigma> , t \<cdot> \<sigma>) \<in> ?R"
      proof (cases "hole_pos C \<in> fun_poss l\<^sub>2")
        case False
        note non_ooverlap_joinable = non_ooverlap_GROUND_joinable [OF S eq refl False _ _ _ s' t']
        from this[OF _ _ _ _ ground rule2]
          and perm_S_ordstep [OF rule1, of \<tau>] and perm_S_ordstep [OF rule2, of \<tau>]
        show ?thesis by (auto, metis GROUND_subset Un_absorb1 Un_iff join_mono)
      next
        case True
        then have "ooverlap {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>) (l\<^sub>1, r\<^sub>1) (l\<^sub>2, r\<^sub>2) p \<mu> s t"
          using * and disj and p [THEN fun_poss_imp_poss] and irrefl
          by (auto simp: ooverlap_def mgu s t ctxt_of_pos_term_subst)
            (auto dest!: perm_R_less dest: subst trans)
        moreover have "\<forall>u \<lhd> l\<^sub>1 \<cdot> \<mu>. u \<in> NF (ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))"
          using NF and NF_ordstep_S_subset[OF rules] unfolding Sconv by force
        ultimately have "(s, t) \<in> PCP_ext (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)"
          by  (force simp: PCP_ext_def)
        then show ?thesis by blast
      qed }
    moreover
    { fix \<pi>\<^sub>1 and \<pi>\<^sub>2 assume rule1: "\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> \<R>" and "\<pi>\<^sub>2 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> ?Eo"
      then obtain u\<^sub>2 v\<^sub>2 \<tau>\<^sub>2' where rule2: "(u\<^sub>2, v\<^sub>2) \<in> \<E>\<^sup>\<leftrightarrow>"
        and "\<pi>\<^sub>2 \<bullet> l\<^sub>2 = u\<^sub>2 \<cdot> \<tau>\<^sub>2'" and "\<pi>\<^sub>2 \<bullet> r\<^sub>2 = v\<^sub>2 \<cdot> \<tau>\<^sub>2'"
        and "\<pi>\<^sub>2 \<bullet> l\<^sub>2 \<succ> \<pi>\<^sub>2 \<bullet> r\<^sub>2" and "u\<^sub>2 \<cdot> \<tau>\<^sub>2' \<succ> v\<^sub>2 \<cdot> \<tau>\<^sub>2'"
        by (auto simp: E_ord_def eqvt)
      moreover define \<tau>\<^sub>2 where "\<tau>\<^sub>2 = \<tau>\<^sub>2' \<circ>\<^sub>s sop (-\<pi>\<^sub>2)"
      ultimately have [simp]: "l\<^sub>2 = u\<^sub>2 \<cdot> \<tau>\<^sub>2" "r\<^sub>2 = v\<^sub>2 \<cdot> \<tau>\<^sub>2"
        and gr2: "u\<^sub>2 \<cdot> \<tau>\<^sub>2 \<succ> v\<^sub>2 \<cdot> \<tau>\<^sub>2" by (auto simp: term_pt.permute_flip perm_less)
      from eq have eq': "\<box>\<langle>u\<^sub>2 \<cdot> \<tau>\<^sub>2 \<circ>\<^sub>s \<tau>\<rangle> = C\<langle>l\<^sub>1 \<cdot> \<tau>\<rangle>" by simp

      have rule2': "0 \<bullet> (u\<^sub>2, v\<^sub>2) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>" using \<open>(u\<^sub>2, v\<^sub>2) \<in> \<E>\<^sup>\<leftrightarrow>\<close> by (auto)
      have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?R"
      proof (cases "hole_pos C \<in> fun_poss u\<^sub>2")
        case False

        from t' have t'': "t \<cdot> \<sigma> = \<box>\<langle>v\<^sub>2 \<cdot> \<tau>\<^sub>2 \<circ>\<^sub>s \<tau>\<rangle>" by simp
        from non_ooverlap_GROUND_joinable [OF RE eq' refl False _ _ _ s' t'' ground rule2']
          and perm_R_ordstep [OF rule1, of \<tau>] and E_ordstep [OF rule2 gr2, of \<tau>]
        have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (GROUND (ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)))\<^sup>\<down>" by auto
        then show ?thesis
          using join_mono [OF ordstep_subset_S, OF rules] and GROUND_subset unfolding Sconv
          by (metis (no_types, lifting) UnI2 join_mono set_mp)
      next
        case True
        obtain \<pi> where disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_rule (\<pi> \<bullet> u\<^sub>2, \<pi> \<bullet> v\<^sub>2) = {}"
          using vars_rule_disjoint unfolding eqvt [symmetric] by blast
        have rule2'': "-\<pi> \<bullet> (\<pi> \<bullet> u\<^sub>2, \<pi> \<bullet> v\<^sub>2) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>"
          using rule2' by (simp)
        then have rule2'': "\<exists>p. p \<bullet> (\<pi> \<bullet> u\<^sub>2, \<pi> \<bullet> v\<^sub>2) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>" ..
        define \<nu> where "\<nu> x = (if x \<in> vars_rule (l\<^sub>1, r\<^sub>1) then Var x else (sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>2) x)" for x
        have 1: "\<pi> \<bullet> u\<^sub>2 \<cdot> \<nu> = u\<^sub>2 \<cdot> \<tau>\<^sub>2"
        proof -
          have "\<pi> \<bullet> u\<^sub>2 \<cdot> \<nu> = \<pi> \<bullet> u\<^sub>2 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>2"
            using disj by (unfold term_subst_eq_conv) (auto simp add: \<nu>_def vars_defs)
          then show ?thesis by simp
        qed
        have 2: "\<pi> \<bullet> v\<^sub>2 \<cdot> \<nu> = v\<^sub>2 \<cdot> \<tau>\<^sub>2"
        proof -
          have "\<pi> \<bullet> v\<^sub>2 \<cdot> \<nu> = \<pi> \<bullet> v\<^sub>2 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>2"
            using disj by (unfold term_subst_eq_conv) (auto simp add: \<nu>_def vars_defs)
          then show ?thesis by simp
        qed
        have [simp]: "r\<^sub>1 \<cdot> \<nu> = r\<^sub>1"
        proof -
          have "r\<^sub>1 \<cdot> \<nu> = r\<^sub>1 \<cdot> Var" by (unfold term_subst_eq_conv) (simp add: \<nu>_def vars_defs)
          then show ?thesis by simp
        qed
        have r\<^sub>2: "r\<^sub>2 = \<pi> \<bullet> v\<^sub>2 \<cdot> \<nu>"
        proof -
          have "\<pi> \<bullet> v\<^sub>2 \<cdot> \<nu> = \<pi> \<bullet> v\<^sub>2 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>2"
            using disj
            by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def eqvt)
          then show ?thesis using p and True
            by (auto simp: eqvt dest!: fun_poss_imp_poss)
        qed
        have l\<^sub>2: "l\<^sub>2 = \<pi> \<bullet> u\<^sub>2 \<cdot> \<nu>"
        proof -
          have "\<pi> \<bullet> u\<^sub>2 \<cdot> \<nu> = \<pi> \<bullet> u\<^sub>2 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>2"
            using disj
            by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def eqvt)
          then show ?thesis using p and True
            by (auto simp: eqvt dest!: fun_poss_imp_poss)
        qed
        then have "l\<^sub>2 |_ p = (\<pi> \<bullet> u\<^sub>2 |_ p) \<cdot> \<nu>"
          using True by (auto dest!: fun_poss_imp_poss)
        moreover
        have "l\<^sub>1 \<cdot> \<nu> \<circ>\<^sub>s \<mu> = l\<^sub>1 \<cdot> \<mu>"
          by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def)
        ultimately
        have *: "l\<^sub>1 \<cdot> \<nu> \<circ>\<^sub>s \<mu> = (\<pi> \<bullet> u\<^sub>2 |_ p) \<cdot> \<nu> \<circ>\<^sub>s \<mu>" using \<open>l\<^sub>1 \<cdot> \<mu> = (l\<^sub>2 |_ p) \<cdot> \<mu>\<close> by simp
        then obtain \<mu>' where mgu: "mgu l\<^sub>1 (\<pi> \<bullet> u\<^sub>2 |_ p) = Some \<mu>'"
          using mgu_complete by (auto simp: unifiers_def simp del: subst_subst_compose)
        from mgu_sound [OF this, THEN is_imgu_imp_is_mgu] and * obtain \<delta> where \<mu>': " \<nu> \<circ>\<^sub>s \<mu> = \<mu>' \<circ>\<^sub>s \<delta>"
          by (auto simp: is_mgu_def unifiers_def simp del: subst_subst_compose)
        have l\<^sub>1: "l\<^sub>1 \<cdot> \<mu> = l\<^sub>1 \<cdot> \<mu>' \<circ>\<^sub>s \<delta>"
          by (unfold term_subst_eq_conv, fold \<mu>') (simp add: subst_compose \<nu>_def vars_defs)
        let ?s = "(ctxt_of_pos_term p (\<pi> \<bullet> u\<^sub>2 \<cdot> \<mu>'))\<langle>r\<^sub>1 \<cdot> \<mu>'\<rangle>"
        let ?t = "\<pi> \<bullet> v\<^sub>2 \<cdot> \<mu>'"
        have 3: "t \<cdot> \<mu>' \<cdot> \<delta> = t \<cdot> \<nu> \<cdot> \<mu>" for t by (fold subst_subst_compose) (simp add: \<mu>')
        have "p \<in> poss (\<pi> \<bullet> u\<^sub>2)" using True by (simp add: eqvt fun_poss_imp_poss)
        then have 4: "s \<cdot> \<sigma> = ?s \<cdot> \<delta> \<cdot> \<sigma>"
          by (simp add: s ctxt_of_pos_term_subst [symmetric] 1 3)
        have 5: "t \<cdot> \<sigma> = ?t \<cdot> \<delta> \<cdot> \<sigma>" by (simp add: t 2 3)

        have "\<not> \<pi> \<bullet> v\<^sub>2 \<cdot> \<mu>' \<succ> \<pi> \<bullet> u\<^sub>2 \<cdot> \<mu>'" (is "\<not> ?v \<cdot> _ \<succ> ?u \<cdot> _")
        proof
          presume "\<not> ?thesis"
          then have "?v \<cdot> \<nu> \<circ>\<^sub>s \<mu> \<succ> ?u \<cdot> \<nu> \<circ>\<^sub>s \<mu>"
            unfolding \<mu>' by (simp add: subst)
          then have "r\<^sub>2 \<cdot> \<mu> \<succ> l\<^sub>2 \<cdot> \<mu>" unfolding l\<^sub>2 r\<^sub>2 by simp
          moreover have "l\<^sub>2 \<succ> r\<^sub>2" using \<open>\<pi>\<^sub>2 \<bullet> l\<^sub>2 \<succ> \<pi>\<^sub>2 \<bullet> r\<^sub>2\<close> by (simp add: perm_less)
          ultimately show False using irrefl by (auto dest: subst trans)
        qed simp
        then have "ooverlap {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>) (l\<^sub>1, r\<^sub>1) (\<pi> \<bullet> u\<^sub>2, \<pi> \<bullet> v\<^sub>2) p \<mu>' ?s ?t"
          using mgu and disj and rule1 and rule2'' and True and irrefl
          by (auto simp: ooverlap_def perm_less)
            (auto dest!: perm_R_less dest: subst trans)
        moreover have "\<forall>u \<lhd> l\<^sub>1 \<cdot> \<mu>'. u \<in> NF (ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))"
          using NF and NF_ordstep_S_subset[OF rules]
          unfolding l\<^sub>1
          by auto (meson NF_instance contra_subsetD instance_no_supt_imp_no_supt)
        ultimately have "(?s, ?t) \<in> PCP_ext (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)" by (force simp: PCP_ext_def)
        then show ?thesis
          unfolding 4 and 5 by blast
      qed }
    moreover
    { fix \<pi>\<^sub>1 and \<pi>\<^sub>2 assume *: "\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> ?Eo" and rule2: "\<pi>\<^sub>2 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> \<R>"
      then have rule1: "\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> \<S> \<R> \<E>" and rule2': "\<pi>\<^sub>2 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> \<S> \<R> \<E>" by auto
      have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?R"
      proof (cases "hole_pos C \<in> fun_poss l\<^sub>2")
        case False
        from non_ooverlap_GROUND_joinable [OF S eq refl False _ _ _ s' t' ground rule2']
          and perm_S_ordstep [OF rule1, of \<tau>] and perm_S_ordstep [OF rule2', of \<tau>]
        show ?thesis by (auto) (metis GROUND_subset Un_absorb1 Un_iff join_mono)
      next
        from * obtain u\<^sub>1 v\<^sub>1 \<tau>\<^sub>1' where rule1: "(u\<^sub>1, v\<^sub>1) \<in> \<E>\<^sup>\<leftrightarrow>"
          and "\<pi>\<^sub>1 \<bullet> l\<^sub>1 = u\<^sub>1 \<cdot> \<tau>\<^sub>1'" and "\<pi>\<^sub>1 \<bullet> r\<^sub>1 = v\<^sub>1 \<cdot> \<tau>\<^sub>1'"
          and "\<pi>\<^sub>1 \<bullet> l\<^sub>1 \<succ> \<pi>\<^sub>1 \<bullet> r\<^sub>1" and "u\<^sub>1 \<cdot> \<tau>\<^sub>1' \<succ> v\<^sub>1 \<cdot> \<tau>\<^sub>1'"
          by (auto simp: E_ord_def eqvt)
        moreover define \<tau>\<^sub>1 where "\<tau>\<^sub>1 = \<tau>\<^sub>1' \<circ>\<^sub>s sop (-\<pi>\<^sub>1)"
        ultimately have [simp]: "l\<^sub>1 = u\<^sub>1 \<cdot> \<tau>\<^sub>1" "r\<^sub>1 = v\<^sub>1 \<cdot> \<tau>\<^sub>1"
          and gr2: "u\<^sub>1 \<cdot> \<tau>\<^sub>1 \<succ> v\<^sub>1 \<cdot> \<tau>\<^sub>1" by (auto simp: term_pt.permute_flip perm_less)
        case True
        obtain \<pi> where disj: "vars_rule (\<pi> \<bullet> u\<^sub>1, \<pi> \<bullet> v\<^sub>1) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}"
          using vars_rule_disjoint unfolding eqvt [symmetric] by blast
        have rule1'': "-\<pi> \<bullet> (\<pi> \<bullet> u\<^sub>1, \<pi> \<bullet> v\<^sub>1) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>"
          using rule1 by (simp)
        then have rule1'': "\<exists>p. p \<bullet> (\<pi> \<bullet> u\<^sub>1, \<pi> \<bullet> v\<^sub>1) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>" ..
        define \<nu> where "\<nu> x = (if x \<in> vars_rule (l\<^sub>2, r\<^sub>2) then Var x else (sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>1) x)" for x
        have [simp]: "l\<^sub>2 \<cdot> \<nu> = l\<^sub>2 \<cdot> Var" by (unfold term_subst_eq_conv) (simp add: \<nu>_def vars_defs)
        then have [simp]: "(l\<^sub>2 |_ p) \<cdot> \<nu> = l\<^sub>2 |_ p"
          using True by (auto dest!: fun_poss_imp_poss) (metis \<open>l\<^sub>2 \<cdot> \<nu> = l\<^sub>2 \<cdot> Var\<close> subst.cop_nil subt_at_subst)

        have [simp]: "r\<^sub>2 \<cdot> \<nu> = r\<^sub>2 \<cdot> Var" by (unfold term_subst_eq_conv) (simp add: \<nu>_def vars_defs)
        have [simp]: "\<pi> \<bullet> u\<^sub>1 \<cdot> \<nu> = u\<^sub>1 \<cdot> \<tau>\<^sub>1"
        proof -
          have "\<pi> \<bullet> u\<^sub>1 \<cdot> \<nu> = \<pi> \<bullet> u\<^sub>1 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>1"
            using disj
            by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def eqvt)
          then show ?thesis by simp
        qed
        have [simp]: "\<pi> \<bullet> v\<^sub>1 \<cdot> \<nu> = v\<^sub>1 \<cdot> \<tau>\<^sub>1"
        proof -
          have "\<pi> \<bullet> v\<^sub>1 \<cdot> \<nu> = \<pi> \<bullet> v\<^sub>1 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>1"
            using disj
            by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def eqvt)
          then show ?thesis by simp
        qed
        have l\<^sub>1: "l\<^sub>1 = \<pi> \<bullet> u\<^sub>1 \<cdot> \<nu>"
        proof -
          have "\<pi> \<bullet> u\<^sub>1 \<cdot> \<nu> = \<pi> \<bullet> u\<^sub>1 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>1"
            using disj
            by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def eqvt)
          then show ?thesis using p and True
            by (auto simp: eqvt dest!: fun_poss_imp_poss)
        qed
        have r\<^sub>1: "r\<^sub>1 = \<pi> \<bullet> v\<^sub>1 \<cdot> \<nu>"
        proof -
          have "\<pi> \<bullet> v\<^sub>1 \<cdot> \<nu> = \<pi> \<bullet> v\<^sub>1 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>1"
            using disj
            by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def eqvt)
          then show ?thesis using p and True
            by (auto simp: eqvt dest!: fun_poss_imp_poss)
        qed
        have *: "\<pi> \<bullet> u\<^sub>1 \<cdot> \<nu> \<circ>\<^sub>s \<mu> = (l\<^sub>2 |_ p) \<cdot> \<nu> \<circ>\<^sub>s \<mu>" using \<open>l\<^sub>1 \<cdot> \<mu> = (l\<^sub>2 |_ p) \<cdot> \<mu>\<close> by (simp)
        then obtain \<mu>' where mgu: "mgu (\<pi> \<bullet> u\<^sub>1) (l\<^sub>2 |_ p) = Some \<mu>'"
          using mgu_complete by (auto simp: unifiers_def simp del: subst_subst_compose)
        from mgu_sound [OF this, THEN is_imgu_imp_is_mgu] and * obtain \<delta> where \<mu>': " \<nu> \<circ>\<^sub>s \<mu> = \<mu>' \<circ>\<^sub>s \<delta>"
          by (auto simp: is_mgu_def unifiers_def simp del: subst_subst_compose)

        have 1: "t \<cdot> \<mu>' \<cdot> \<delta> = t \<cdot> \<nu> \<cdot> \<mu>" for t
          by (fold subst_subst_compose) (simp add: \<mu>')
        let ?s = "(ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<mu>'))\<langle>\<pi> \<bullet> v\<^sub>1 \<cdot> \<mu>'\<rangle>"
        let ?t = "r\<^sub>2 \<cdot> \<mu>'"
        have 2: "s \<cdot> \<sigma> = ?s \<cdot> \<delta> \<cdot> \<sigma>"
          using True [THEN fun_poss_imp_poss]
          by (simp add: s ctxt_of_pos_term_subst [symmetric] 1)
        have 3: "t \<cdot> \<sigma> = ?t \<cdot> \<delta> \<cdot> \<sigma>" by (simp add: t 1)

        have "\<not> \<pi> \<bullet> v\<^sub>1 \<cdot> \<mu>' \<succ> \<pi> \<bullet> u\<^sub>1 \<cdot> \<mu>'"
          (is "\<not> ?v \<cdot> _ \<succ> ?u \<cdot> _")
        proof
          presume "\<not> ?thesis"
          then have "?v \<cdot> \<nu> \<circ>\<^sub>s \<mu> \<succ> ?u \<cdot> \<nu> \<circ>\<^sub>s \<mu>"
            unfolding \<mu>' by (simp add: subst)
          then have "r\<^sub>1 \<cdot> \<mu> \<succ> l\<^sub>1 \<cdot> \<mu>" unfolding l\<^sub>1 r\<^sub>1 by simp
          moreover have "l\<^sub>1 \<succ> r\<^sub>1" using \<open>\<pi>\<^sub>1 \<bullet> l\<^sub>1 \<succ> \<pi>\<^sub>1 \<bullet> r\<^sub>1\<close> by (simp add: perm_less)
          ultimately show False using irrefl by (auto dest: subst trans)
        qed simp
        then have "ooverlap {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>) (\<pi> \<bullet> u\<^sub>1, \<pi> \<bullet> v\<^sub>1) (l\<^sub>2, r\<^sub>2) p \<mu>' ?s ?t"
          using mgu and disj and rule1'' and rule2 and True and irrefl
          by (auto simp: ooverlap_def perm_less) (auto dest!: perm_R_less dest: subst trans)
        moreover have "\<forall>u \<lhd> \<pi> \<bullet> u\<^sub>1 \<cdot> \<mu>'. u \<in> NF (ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))"
          using NF and NF_ordstep_S_subset[OF rules]
          unfolding l\<^sub>1 and 1 [symmetric]
          by auto (meson NF_instance contra_subsetD instance_no_supt_imp_no_supt)
        ultimately have "(?s, ?t) \<in> PCP_ext (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)" by (force simp: PCP_ext_def)
        then show ?thesis
          unfolding 2 and 3 by blast
      qed }
    moreover
    { fix \<pi>\<^sub>1 and \<pi>\<^sub>2 assume "\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> ?Eo" and "\<pi>\<^sub>2 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> ?Eo"
      then obtain u\<^sub>1 v\<^sub>1 \<tau>\<^sub>1' and u\<^sub>2 v\<^sub>2 \<tau>\<^sub>2'
        where rule1: "(u\<^sub>1, v\<^sub>1) \<in> \<E>\<^sup>\<leftrightarrow>" and "\<pi>\<^sub>1 \<bullet> l\<^sub>1 = u\<^sub>1 \<cdot> \<tau>\<^sub>1'" and "\<pi>\<^sub>1 \<bullet> r\<^sub>1 = v\<^sub>1 \<cdot> \<tau>\<^sub>1'"
          and "\<pi>\<^sub>1 \<bullet> l\<^sub>1 \<succ> \<pi>\<^sub>1 \<bullet> r\<^sub>1"
          and rule2: "(u\<^sub>2, v\<^sub>2) \<in> \<E>\<^sup>\<leftrightarrow>" and "\<pi>\<^sub>2 \<bullet> l\<^sub>2 = u\<^sub>2 \<cdot> \<tau>\<^sub>2'" and "\<pi>\<^sub>2 \<bullet> r\<^sub>2 = v\<^sub>2 \<cdot> \<tau>\<^sub>2'"
          and "\<pi>\<^sub>2 \<bullet> l\<^sub>2 \<succ> \<pi>\<^sub>2 \<bullet> r\<^sub>2"
        by (force simp: E_ord_def eqvt)
      moreover
      define \<tau>\<^sub>1 and \<tau>\<^sub>2 where "\<tau>\<^sub>1 = \<tau>\<^sub>1' \<circ>\<^sub>s sop (-\<pi>\<^sub>1)" and "\<tau>\<^sub>2 = \<tau>\<^sub>2' \<circ>\<^sub>s sop (-\<pi>\<^sub>2)"
      ultimately
      have [simp]: "u\<^sub>1 \<cdot> \<tau>\<^sub>1 = l\<^sub>1" "v\<^sub>1 \<cdot> \<tau>\<^sub>1 = r\<^sub>1" "u\<^sub>2 \<cdot> \<tau>\<^sub>2 = l\<^sub>2" "v\<^sub>2 \<cdot> \<tau>\<^sub>2 = r\<^sub>2"
        and gr1: "u\<^sub>1 \<cdot> \<tau>\<^sub>1 \<succ> v\<^sub>1 \<cdot> \<tau>\<^sub>1" and gr2: "u\<^sub>2 \<cdot> \<tau>\<^sub>2 \<succ> v\<^sub>2 \<cdot> \<tau>\<^sub>2"
        by (auto simp: term_pt.permute_flip [symmetric] perm_less)

      have rule2': "0 \<bullet> (u\<^sub>2, v\<^sub>2) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>" using rule2 by simp

      have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?R"
      proof (cases "hole_pos C \<in> fun_poss u\<^sub>2")
        case False

        from eq have eq': "\<box>\<langle>u\<^sub>2 \<cdot> \<tau>\<^sub>2 \<circ>\<^sub>s \<tau>\<rangle> = C\<langle>u\<^sub>1 \<cdot> \<tau>\<^sub>1 \<circ>\<^sub>s \<tau>\<rangle>" by simp
        from s' have s'': "s \<cdot> \<sigma> = C\<langle>v\<^sub>1 \<cdot> \<tau>\<^sub>1 \<circ>\<^sub>s \<tau>\<rangle>" by simp
        from t' have t'': "t \<cdot> \<sigma> = \<box>\<langle>v\<^sub>2 \<cdot> \<tau>\<^sub>2 \<circ>\<^sub>s \<tau>\<rangle>" by simp
        from non_ooverlap_GROUND_joinable [OF RE eq' refl False _ _ _ s'' t'' ground rule2']
          and E_ordstep [OF rule1 gr1, of \<tau>] and E_ordstep [OF rule2 gr2, of \<tau>]
        have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (GROUND (ordstep {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)))\<^sup>\<down>" by auto
        then show ?thesis
          using join_mono [OF ordstep_subset_S[OF rules]] and GROUND_subset
          by (metis (no_types, lifting) UnI2 join_mono Sconv set_mp)
      next
        case True
        obtain \<pi> where disj: "vars_rule (\<pi> \<bullet> u\<^sub>1, \<pi> \<bullet> v\<^sub>1) \<inter> vars_rule (u\<^sub>2, v\<^sub>2) = {}"
          using vars_rule_disjoint unfolding eqvt [symmetric] by blast
        have "-\<pi> \<bullet> (\<pi> \<bullet> u\<^sub>1, \<pi> \<bullet> v\<^sub>1) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>" using rule1 by simp
        then have rule1': "\<exists>p. p \<bullet> (\<pi> \<bullet> u\<^sub>1, \<pi> \<bullet> v\<^sub>1) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>" ..
        have rule2'': "\<exists>p. p \<bullet> (u\<^sub>2, v\<^sub>2) \<in> \<R> \<union> \<E>\<^sup>\<leftrightarrow>" using rule2' ..

        define \<nu> where "\<nu> x = (if x \<in> vars_rule (u\<^sub>2, v\<^sub>2) then \<tau>\<^sub>2 x else (sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>1) x)" for x

        have l\<^sub>1: "\<pi> \<bullet> u\<^sub>1 \<cdot> \<nu> = l\<^sub>1"
        proof -
          have "\<pi> \<bullet> u\<^sub>1 \<cdot> \<nu> = \<pi> \<bullet> u\<^sub>1 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>1"
            using disj
            by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def eqvt)
          then show ?thesis by simp
        qed
        have [simp]: "\<pi> \<bullet> v\<^sub>1 \<cdot> \<nu> = r\<^sub>1"
        proof -
          have "\<pi> \<bullet> v\<^sub>1 \<cdot> \<nu> = \<pi> \<bullet> v\<^sub>1 \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>\<^sub>1"
            using disj
            by (unfold term_subst_eq_conv) (auto simp: subst_compose vars_defs \<nu>_def eqvt)
          then show ?thesis by simp
        qed
        have [simp]: "u\<^sub>2 \<cdot> \<nu> = l\<^sub>2"
        proof -
          have "u\<^sub>2 \<cdot> \<nu> = u\<^sub>2 \<cdot> \<tau>\<^sub>2" by (unfold term_subst_eq_conv) (auto simp: \<nu>_def vars_defs)
          then show ?thesis by simp
        qed
        then have [simp]: "u\<^sub>2 |_ p \<cdot> \<nu> = l\<^sub>2 |_ p"
          using True [THEN fun_poss_imp_poss] by (auto) (metis \<open>u\<^sub>2 \<cdot> \<nu> = l\<^sub>2\<close> subt_at_subst)

        have [simp]: "v\<^sub>2 \<cdot> \<nu> = r\<^sub>2"
        proof -
          have "v\<^sub>2 \<cdot> \<nu> = v\<^sub>2 \<cdot> \<tau>\<^sub>2" by (unfold term_subst_eq_conv) (auto simp: \<nu>_def vars_defs)
          then show ?thesis by simp
        qed

        have *: "\<pi> \<bullet> u\<^sub>1 \<cdot> \<nu> \<circ>\<^sub>s \<mu> = (u\<^sub>2 |_ p) \<cdot> \<nu> \<circ>\<^sub>s \<mu>" using \<open>l\<^sub>1 \<cdot> \<mu> = (l\<^sub>2 |_ p) \<cdot> \<mu>\<close> by (simp add: l\<^sub>1)
        then obtain \<mu>' where mgu: "mgu (\<pi> \<bullet> u\<^sub>1) (u\<^sub>2 |_ p) = Some \<mu>'"
          using mgu_complete by (auto simp: unifiers_def simp del: subst_subst_compose)
        from mgu_sound [OF this, THEN is_imgu_imp_is_mgu] and * obtain \<delta> where \<mu>': " \<nu> \<circ>\<^sub>s \<mu> = \<mu>' \<circ>\<^sub>s \<delta>"
          by (auto simp: is_mgu_def unifiers_def simp del: subst_subst_compose)

        have 1: "t \<cdot> \<mu>' \<cdot> \<delta> = t \<cdot> \<nu> \<cdot> \<mu>" for t
          by (fold subst_subst_compose) (simp add: \<mu>')
        let ?s = "(ctxt_of_pos_term p (u\<^sub>2 \<cdot> \<mu>'))\<langle>\<pi> \<bullet> v\<^sub>1 \<cdot> \<mu>'\<rangle>"
        let ?t = "v\<^sub>2 \<cdot> \<mu>'"
        have 2: "s \<cdot> \<sigma> = ?s \<cdot> \<delta> \<cdot> \<sigma>"
          using True [THEN fun_poss_imp_poss] and p [THEN fun_poss_imp_poss]
          by (simp add: s ctxt_of_pos_term_subst [symmetric] 1)
        have 3: "t \<cdot> \<sigma> = ?t \<cdot> \<delta> \<cdot> \<sigma>" by (simp add: t 1)

        have "\<not> \<pi> \<bullet> v\<^sub>1 \<cdot> \<mu>' \<succ> \<pi> \<bullet> u\<^sub>1 \<cdot> \<mu>'" (is "\<not> ?v \<cdot> _ \<succ> ?u \<cdot> _")
        proof
          presume "\<not> ?thesis"
          then have "?v \<cdot> \<nu> \<circ>\<^sub>s \<mu> \<succ> ?u \<cdot> \<nu> \<circ>\<^sub>s \<mu>" unfolding \<mu>' by (simp add: subst)
          then have "r\<^sub>1 \<cdot> \<mu> \<succ> l\<^sub>1 \<cdot> \<mu>" by (simp add: l\<^sub>1)
          moreover have "l\<^sub>1 \<succ> r\<^sub>1" using \<open>\<pi>\<^sub>1 \<bullet> l\<^sub>1 \<succ> \<pi>\<^sub>1 \<bullet> r\<^sub>1\<close> by (simp add: perm_less)
          ultimately show False using irrefl by (auto dest: subst trans)
        qed simp
        moreover have "\<not> v\<^sub>2 \<cdot> \<mu>' \<succ> u\<^sub>2 \<cdot> \<mu>'" (is "\<not> ?v \<cdot> _ \<succ> ?u \<cdot> _")
        proof
          presume "\<not> ?thesis"
          then have "?v \<cdot> \<nu> \<circ>\<^sub>s \<mu> \<succ> ?u \<cdot> \<nu> \<circ>\<^sub>s \<mu>" unfolding \<mu>' by (simp add: subst)
          then have "r\<^sub>2 \<cdot> \<mu> \<succ> l\<^sub>2 \<cdot> \<mu>" by simp
          moreover have "l\<^sub>2 \<succ> r\<^sub>2" using \<open>\<pi>\<^sub>2 \<bullet> l\<^sub>2 \<succ> \<pi>\<^sub>2 \<bullet> r\<^sub>2\<close> by (simp add: perm_less)
          ultimately show False using irrefl by (auto dest: subst trans)
        qed simp
        ultimately
        have "ooverlap {\<succ>} (\<R> \<union> \<E>\<^sup>\<leftrightarrow>) (\<pi> \<bullet> u\<^sub>1, \<pi> \<bullet> v\<^sub>1) (u\<^sub>2, v\<^sub>2) p \<mu>' ?s ?t"
          using mgu and disj and rule1' and rule2'' and True
          by (auto simp: ooverlap_def perm_less)
        moreover
        have "\<forall>u \<lhd> \<pi> \<bullet> u\<^sub>1 \<cdot> \<mu>'. u \<in> NF ?RE"
          using NF and NF_ordstep_S_subset
          unfolding l\<^sub>1 [symmetric] and 1 [symmetric]
          by auto (meson NF_instance rules contra_subsetD instance_no_supt_imp_no_supt)
        ultimately have "(?s, ?t) \<in> PCP_ext (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)" by (force simp: PCP_ext_def)
        then show ?thesis
          unfolding 2 and 3 by blast
      qed }
    ultimately have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?R" using o by (auto simp: overlap_def) }
  then show ?thesis
    using assms by (auto elim!: rstepE) blast+
qed

abbreviation "\<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c" where "\<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c \<equiv> \<E>\<^sup>\<leftrightarrow> \<inter> {\<succ>}"
definition \<R>':: "('a, 'b) term rel" where "\<R>' \<equiv> {(l, r) | l r. (l, r) \<in> dot (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c) \<and> (\<nexists>u l0 r0. (l, u) \<in> rstep {(l0, r0)} \<and> (l0, r0) \<in> \<S> \<R> \<E> \<and> l0 \<lhd>\<cdot> l)}"
definition \<E>' :: "('a, 'b) term rel" where "\<E>' \<equiv> {(some_NF (rstep \<R>') s, some_NF (rstep \<R>') t) | s t. (s, t) \<in> \<E> \<and> some_NF (rstep \<R>') s \<noteq> some_NF (rstep \<R>') t }"
definition "\<S>'":: "('a, 'b) term rel" where "\<S>' = \<R>' \<union> E_ord (\<succ>) \<E>'"


lemma Esucc_E_ord: "\<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c \<subseteq> E_ord (\<succ>) \<E>"
proof
  fix s t
  assume "(s, t) \<in> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c"
  note ord = this [unfolded Int_iff split]
  show "(s, t) \<in> E_ord (\<succ>) \<E>" unfolding E_ord_def mem_Collect_eq
    by(rule exI [of _ s], rule exI [of _ t], rule exI [of _ Var], insert ord, auto)
qed

lemma encomp_perm: "u \<unlhd>\<cdot> s = (u \<unlhd>\<cdot> (\<pi> \<bullet> s))"
proof
  from term_apply_subst_Var_Rep_perm obtain \<sigma> where sub: "\<pi> \<bullet> s = s \<cdot> \<sigma>" by metis
  show "u \<unlhd>\<cdot> s \<Longrightarrow> u \<unlhd>\<cdot> \<pi> \<bullet> s" unfolding encompeq.simps sub
    by (metis subst_apply_term_ctxt_apply_distrib subst_subst)
next
  have "s = ( -\<pi>) \<bullet> \<pi> \<bullet> s" by auto
  with term_apply_subst_Var_Rep_perm obtain \<sigma> where sub: "s = (\<pi> \<bullet> s) \<cdot> \<sigma>" by metis
  show "u \<unlhd>\<cdot> \<pi> \<bullet> s \<Longrightarrow> u \<unlhd>\<cdot> s" unfolding encompeq.simps using sub
    by (metis subst_apply_term_ctxt_apply_distrib subst_subst)
qed

abbreviation "lexencomp \<equiv> lex_two {\<cdot>\<rhd>} {\<cdot>\<unrhd>}  {(a, b :: bool) . a \<and> \<not> b}"

lemma SN_lexencomp: "SN lexencomp"
proof-
  have t: "SN {(a, b). a \<and> \<not> b}" using SN_inv_image [OF SN_nat_gt, of "\<lambda>b. if b then 1 else 0"]
    by (metis (no_types, lifting) SN_onI mem_Collect_eq split_conv)
  then show ?thesis using SN_encomp encomp_order.less_le_trans encomp_order.le_less_trans
    by(intro lex_two, auto)
qed

lemma gterms_ER_conv_implies_S_conv:
  assumes RR_less: "RR \<subseteq> {\<succ>}"
  assumes ground: "ground s" "ground t"
  assumes conv: "(s, t) \<in> (rstep (RR \<union> EE\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" (is "_ \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*")
  shows "(s, t) \<in> (GROUND (rstep (RR \<union> E_ord (\<succ>) EE)))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from gterm_conv_GROUND_conv assms have "(s, t) \<in> (GROUND (rstep (RR \<union> EE\<^sup>\<leftrightarrow>)))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with conversion_mono [OF FGROUND_rstep_ordstep] show ?thesis
    unfolding conversion_conversion_idemp by auto
qed

lemma reduced_ground_complete:
  assumes "\<S> \<R> \<E> \<subseteq> {\<succ>}" and "GCR (rstep (\<S> \<R> \<E>)) \<and> SN (GROUND (rstep (\<S> \<R> \<E>)))"
  shows "GCR (rstep \<S>') \<and>
         SN (GROUND (rstep \<S>')) \<and>
         (GROUND (rstep (\<S> \<R> \<E>)))\<^sup>! = (GROUND (rstep \<S>'))\<^sup>!"
proof-
  let ?S = "\<R>' \<union> (E_ord (\<succ>) \<E>')"
  have sub_dot: "\<R>' \<subseteq> dot (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)" unfolding \<R>'_def by fast
  with rstep_subset_less \<open>\<R> \<subseteq> {\<succ>}\<close> have **: "\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c \<subseteq> {\<succ>}" unfolding rstep_union by auto
  with rstep_subset_less \<open>\<R> \<subseteq> {\<succ>}\<close> have *: "rstep (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c) \<subseteq> {\<succ>}" unfolding rstep_union by auto
  with SN_less SN_subset have "SN (rstep (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c))" by auto
  interpret SN_trs "\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c" by standard fact

  { fix l r
    assume a: "(l, r) \<in> dot' (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)"
    then have "\<exists> r'. (l, r') \<in> (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c) \<and> r = some_NF (rstep (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)) r'"
      unfolding dot'_def mem_Collect_eq by fast
    with some_NF_rtrancl rstep_rule [OF a] have "(l, r) \<in> (rstep (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c))\<^sup>+"
      by (meson rstep_rule rtrancl_into_trancl2)
  }
  with rsteps_subset_less [OF **] rm_variants_subset have "dot (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c) \<subseteq> {\<succ>}"
    unfolding dot_def by blast
  with sub_dot rstep_subset_less have R'succ: "\<R>' \<subseteq> {\<succ>}" by auto
  with rstep_subset_less have "rstep \<R>' \<subseteq> {\<succ>}" unfolding E_ord_def by blast
  with SN_less SN_subset have "SN (rstep \<R>')" unfolding \<S>'_def by metis
  from R'succ rstep_subset_less have "rstep ?S \<subseteq> {\<succ>}" unfolding E_ord_def by blast
  with SN_less SN_subset GROUND_subset have x: "SN (GROUND (rstep \<S>'))" unfolding \<S>'_def by metis

  { fix s t
    assume "(s, t) \<in> GROUND (rstep (\<S> \<R> \<E>))"
    then have g: "ground s" "ground t" "(s, t) \<in> rstep (\<S> \<R> \<E>)" unfolding GROUND_def by auto
    { fix l r
      assume in_S: "(l, r) \<in> \<S> \<R> \<E>"
      let ?orig = "\<lambda> rl. \<not> rl \<in> \<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c"
      from in_S have "\<exists> r'. (l, r') \<in> rstep \<S>'"
      proof (induct "(l, ?orig (l, r))" arbitrary: l r rule: SN_induct [OF SN_lexencomp])
        case (1 l)
        then show ?case
        proof (cases "(l, r) \<in> \<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c")
          case True
          note REsucc = this
          show ?thesis
          proof (cases "\<exists>u l0 r0. (l, u) \<in> rstep {(l0, r0)} \<and> (l0, r0) \<in> \<S> \<R> \<E> \<and> l0 \<lhd>\<cdot> l")
            case True
            then obtain u l0 r0 where step: "(l, u) \<in> rstep {(l0, r0)}" "(l0, r0) \<in> \<S> \<R> \<E>" and ll0: "l0 \<lhd>\<cdot> l" by blast
            then obtain C \<sigma> where C: "l = C\<langle>l0 \<cdot> \<sigma>\<rangle>" "(l0, r0) \<in> \<S> \<R> \<E>" using rstep.simps by auto
            from ll0 have "((l, ?orig (l, r)), (l0, ?orig (l0, r0))) \<in> lexencomp" by force
            with 1(1) [OF this] step have "\<exists> r0'. (l0, r0') \<in> rstep \<S>'" by auto
            with C(1) rstep_ctxt show ?thesis by force
          next
            case False
            from REsucc obtain u where in_dot: "(l, u) \<in> dot' (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)" unfolding dot'_def by auto
            from rm_variants_representative [OF this]
            obtain \<pi> l' r' where var: "(l', r') \<in> dot(\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)" "\<pi> \<bullet> (l, u) = (l', r')"
              unfolding dot_def by blast
            then have "\<pi> \<bullet> l = l' \<and> \<pi> \<bullet> u = r'" by (simp add: rule_pt.permute_prod.simps)
            then have lu: "l = ( - \<pi>) \<bullet> l'" "u = ( - \<pi>) \<bullet> r'" by auto
            { assume "\<exists>u l0 r0. (l', u) \<in> rstep {(l0, r0)} \<and> (l0, r0) \<in> \<S> \<R> \<E> \<and> l0 \<lhd>\<cdot> l'"
              then obtain v l0 r0 where step': "(l', v) \<in> rstep {(l0, r0)} "
                and in_S: "(l0, r0) \<in> \<S> \<R> \<E>" and enc: "l0 \<lhd>\<cdot> l'" by blast
              with rstep_r_p_s_imp_rstep have step: "(l', v) \<in> rstep {(l0, r0)}" by auto
              with permute_rstep lu have step: "(l, ( - \<pi>) \<bullet> v) \<in> rstep {(l0, r0)}" by auto
              from encomp_perm enc lu have enc: "l0 \<lhd>\<cdot> l" unfolding encomp_def
                by (metis encomp_def encomp_order.le_less_trans encompeq_refl)
              with False enc step in_S have False by blast
            }
            with var have "(l', r') \<in> \<R>'" unfolding \<R>'_def mem_Collect_eq by blast
            with var(2) perm_rstep_conv rstep_rule have "(l, u) \<in> rstep \<R>'" by metis
            then show ?thesis unfolding rstep_union \<S>'_def by fast
          qed
        next
          case False
          note unorientable = this
          with 1(2) obtain u v \<sigma> where uv: "(u, v) \<in> \<E>\<^sup>\<leftrightarrow>" "l = u \<cdot> \<sigma>" "r = v \<cdot> \<sigma>" "u \<cdot> \<sigma> \<succ> v \<cdot> \<sigma>"
            unfolding E_ord_def by blast
          let ?u = "some_NF (rstep \<R>') u"
          let ?v = "some_NF (rstep \<R>') v"
          interpret SN_R': SN_ars "rstep \<R>'" by standard fact
          from \<open>SN (rstep \<R>')\<close> have uu: "(u, ?u) \<in> (rstep \<R>')\<^sup>*"
            by (simp add: SN_ars.some_NF_rtrancl Normalization_Equivalence.SN_ars.intro)
          from \<open>SN (rstep \<R>')\<close> have vv: "(v, ?v) \<in> (rstep \<R>')\<^sup>*"
            by (simp add: SN_ars.some_NF_rtrancl Normalization_Equivalence.SN_ars.intro)
          show ?thesis
          proof (cases "?u = u")
            case True
            from vv rsteps_subset_less [OF \<open>\<R>' \<subseteq> {\<succ>}\<close>] have "v \<succeq> ?v"
              unfolding rtrancl_eq_or_trancl by auto
            with subst [of v ?v \<sigma>] trans [OF uv(4)] uv(4) have gt: "u \<cdot> \<sigma> \<succ> ?v \<cdot> \<sigma>" by auto
            with irrefl have "u \<noteq> ?v" by auto
            with uv(1) True have in_E': "(u, ?v) \<in> \<E>'\<^sup>\<leftrightarrow>"
              unfolding \<E>'_def Un_iff mem_Collect_eq converse_iff by metis
            from gt uv in_E' have "(l, ?v \<cdot> \<sigma>) \<in> E_ord (\<succ>) \<E>'"
              unfolding E_ord_def mem_Collect_eq by blast
            with uv show ?thesis unfolding rstep_union \<S>'_def by blast
          next
            case False
            with uu have "(u, ?u) \<in> (rstep \<R>')\<^sup>+" by (simp add: rtrancl_eq_or_trancl)
            with tranclD obtain w where "(u, w) \<in> (rstep \<R>')" "(w, ?u) \<in> (rstep \<R>')\<^sup>*"
              by (meson tranclD)
            then obtain l0 r0 C \<tau> where l0r0: "u = C\<langle>l0 \<cdot> \<tau>\<rangle>" "w = C\<langle>r0 \<cdot> \<tau>\<rangle>" "(l0, r0) \<in> \<R>'" by auto
            then have "(l0, r0) \<in> dot (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)" unfolding \<R>'_def by auto
            with lhss_dot obtain r0' where oriented: "(l0, r0') \<in> \<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c" by fastforce
            from Esucc_E_ord oriented have in_S: "(l0, r0') \<in> \<S> \<R> \<E>" unfolding Un_iff by auto
            from uv(2) have "l \<cdot>\<unrhd> l0" unfolding encompeq.simps l0r0(1)
                subst_apply_term_ctxt_apply_distrib subst_subst by fast
            with unorientable oriented have "((l, ?orig (l, r)), (l0, ?orig (l0, r0'))) \<in> lexencomp" by simp
            from 1(1) [OF this in_S] show ?thesis unfolding uv l0r0 by fast
          qed
        qed
      qed
    }
    with g have "\<exists>t'. (s, t') \<in> rstep \<S>'" by fast
    then obtain t' where step: "(s, t') \<in> rstep \<S>'" by auto
    with \<open>rstep ?S \<subseteq> {\<succ>}\<close> ground_less [OF g(1)] have "ground t'" unfolding \<S>'_def by auto
    with g step have "\<exists>t'.(s, t') \<in> GROUND (rstep \<S>')" unfolding GROUND_def by auto
  }
  then have NFs: "NF (GROUND (rstep \<S>')) \<subseteq> NF (GROUND (rstep (\<S> \<R> \<E>)))" unfolding NF_def by auto

  have step_conv: "GROUND(rstep \<S>') \<subseteq> (GROUND (rstep (\<S> \<R> \<E>)))\<^sup>\<leftrightarrow>\<^sup>*"
  proof
    fix s t
    assume "(s, t) \<in> GROUND(rstep \<S>')"
    then have g: "ground s" "ground t" "(s, t) \<in> rstep \<S>'" unfolding GROUND_def by auto
    then obtain l r \<sigma> C where C: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l, r) \<in> \<S>'" by auto
    { fix l r
      assume "(l, r) \<in> \<R>'"
      with rm_variants_subset have "(l, r) \<in> dot' (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)" unfolding \<R>'_def mem_Collect_eq dot_def by fast
      then obtain r' where r: "r = some_NF (rstep (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)) r'" "(l, r') \<in> \<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c" unfolding dot'_def  by auto
      interpret REsucc: SN_ars "rstep (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c)" by standard fact
      from \<open>SN (rstep (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c))\<close> have "(r', r) \<in> (rstep (\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c))\<^sup>*" unfolding r
        by (simp add: SN_ars.some_NF_rtrancl Normalization_Equivalence.SN_ars.intro)
      with rstep_mono [of "\<R> \<union> \<E>\<^sub>s\<^sub>u\<^sub>c\<^sub>c" "\<R> \<union> \<E>\<^sup>\<leftrightarrow>", THEN rtrancl_mono] have rr: "(r', r) \<in> (rstep  (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>*" by blast
      from r(2) have "(l, r') \<in> rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>)" by fastforce
      with rr have "(l, r) \<in> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def
        by (meson converse_rtrancl_into_rtrancl in_rtrancl_UnI)
    } note R'_RE = this
    {  fix s t
      assume "(s, t) \<in> rstep \<R>'"
      then obtain l r C \<sigma> where "(l, r) \<in> \<R>'" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
      with R'_RE [OF this(1)] ctxt.closed_conversion [OF ctxt_closed_rstep, THEN ctxt.closedD]
        subst.closed_conversion [OF subst_closed_rstep, THEN subst.closedD] have "(s, t) \<in> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" by metis
    } note R'_step_RE = this
    then have "rstep \<R>' \<subseteq> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    from conversion_conversion_idemp conversion_mono [OF this]
    have R'_steps_RE: "\<And> s t.(s, t) \<in> (rstep \<R>')\<^sup>* \<Longrightarrow> (s, t) \<in> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    show "(s, t) \<in> (GROUND (rstep (\<S> \<R> \<E>)))\<^sup>\<leftrightarrow>\<^sup>*"
    proof (cases "(l, r) \<in> \<R>'")
      case True
      from R'_RE [OF this] ctxt.closed_conversion [OF ctxt_closed_rstep, THEN ctxt.closedD]
        subst.closed_conversion [OF subst_closed_rstep, THEN subst.closedD]
      have "(s, t) \<in> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding C by metis
      with gterms_ER_conv_implies_S_conv [OF \<open>\<R> \<subseteq> {\<succ>}\<close> g(1) g(2)] show ?thesis .
    next
      case False
      with C(3) [unfolded \<S>'_def] have "(l, r) \<in> E_ord (\<succ>) \<E>'" by auto
      then obtain u v \<tau> where uv: "l = u\<cdot> \<tau>" "r = v \<cdot> \<tau>" "(u, v) \<in> \<E>'\<^sup>\<leftrightarrow>" "u\<cdot> \<tau> \<succ> v \<cdot> \<tau>"
        unfolding E_ord_def mem_Collect_eq by blast
      from uv(3) obtain u' v' where uv': "(u', v') \<in> \<E>\<^sup>\<leftrightarrow>" "u = some_NF (rstep \<R>') u'" "v = some_NF (rstep \<R>') v'"
        unfolding \<E>'_def Un_iff mem_Collect_eq by auto
      interpret SN_R': SN_ars "rstep \<R>'" by standard fact
      from \<open>SN (rstep \<R>')\<close> have "(u', u) \<in> (rstep \<R>')\<^sup>*" unfolding uv'
        by (simp add: SN_ars.some_NF_rtrancl Normalization_Equivalence.SN_ars.intro)
      with rsteps_closed_subst rsteps_closed_ctxt have "(C\<langle>u' \<cdot> \<tau> \<cdot> \<sigma>\<rangle>, C\<langle>u \<cdot> \<tau> \<cdot> \<sigma>\<rangle>) \<in> (rstep \<R>')\<^sup>*" by metis
      with R'_steps_RE conversion_inv have uconv: "(C\<langle>u \<cdot> \<tau> \<cdot> \<sigma>\<rangle>, C\<langle>u' \<cdot> \<tau> \<cdot> \<sigma>\<rangle>) \<in> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" by metis
      from \<open>SN (rstep \<R>')\<close> uv' have "(v', v) \<in> (rstep \<R>')\<^sup>*"
        by (simp add: SN_ars.some_NF_rtrancl Normalization_Equivalence.SN_ars.intro)
      with rsteps_closed_subst rsteps_closed_ctxt have "(C\<langle>v' \<cdot> \<tau> \<cdot> \<sigma>\<rangle>, C\<langle>v \<cdot> \<tau> \<cdot> \<sigma>\<rangle>) \<in> (rstep \<R>')\<^sup>*" by metis
      with R'_steps_RE have vconv: "(C\<langle>v' \<cdot> \<tau> \<cdot> \<sigma>\<rangle>, C\<langle>v \<cdot> \<tau> \<cdot> \<sigma>\<rangle>) \<in> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
      from uv' uv rstepI have "(C\<langle>u' \<cdot> \<tau> \<cdot>\<sigma>\<rangle>, C\<langle>v' \<cdot> \<tau> \<cdot>\<sigma>\<rangle>) \<in> rstep (\<E>\<^sup>\<leftrightarrow>)" by auto
      then have "(C\<langle>u' \<cdot> \<tau> \<cdot>\<sigma>\<rangle>, C\<langle>v' \<cdot> \<tau> \<cdot>\<sigma>\<rangle>) \<in> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*"
        unfolding conversion_def using r_into_rtrancl by (auto simp: rstep_simps)
      from conversion_trans' [OF uconv this, THEN conversion_trans'] vconv
      have "(s, t) \<in> (rstep (\<R> \<union> \<E>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding C uv by auto
      with gterms_ER_conv_implies_S_conv [OF \<open>\<R> \<subseteq> {\<succ>}\<close> g(1) g(2)] show ?thesis .
    qed
  qed

  from assms have CR_SN: "CR (GROUND (rstep (\<S> \<R> \<E>))) \<and> SN (GROUND (rstep (\<S> \<R> \<E>)))"
    by (meson GROUND_subset SN_subset)
  interpret complete_ars "GROUND (rstep (\<S> \<R> \<E>))" by (standard, insert CR_SN, auto)
  from complete_NE_intro1 [OF step_conv x NFs] complete_ars.CR show ?thesis
    unfolding complete_ars_def Normalization_Equivalence.SN_ars_def by auto
qed
end


    
lemma Einf_sym_without_Ew_sym: assumes "(l,r) \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" and "(l,r) \<notin>  E\<^sub>\<omega>\<^sup>\<leftrightarrow>"
  shows "\<exists>j. ((l, r) \<in> (E j) \<and> (l, r) \<notin> (E (Suc j))) \<or> ((r, l) \<in> (E j) \<and> (r, l) \<notin> (E (Suc j)))"
by (cases "(l,r) \<in> E\<^sub>\<infinity>", insert assms Einf_without_Ew, auto)

lemma Ew_reducible_aux:
  assumes "(\<exists>r'. (l,r') \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<and> l\<cdot>\<sigma> \<succ> r'\<cdot>\<sigma>) \<or> l \<notin> NF (ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))"
  shows "l\<cdot>\<sigma> \<notin> NF (ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))"
proof-
  from assms consider "\<exists>r'. (l,r') \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<and> l\<cdot>\<sigma> \<succ> r'\<cdot>\<sigma>" | "l \<notin> NF (ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))" by auto
  then show ?thesis proof(cases)
    case 1
    then obtain r' where r':"(l, r') \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "l \<cdot> \<sigma> \<succ> r' \<cdot> \<sigma>" by auto
    have "(l\<cdot>\<sigma>, r'\<cdot>\<sigma>) \<in> ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
      by (rule ordstep.intros[of _ _ _ _ \<box>], insert r', auto)
    then show ?thesis by auto
  next
    case 2
    then obtain t where "(l, t) \<in> ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
    from ordstep_subst_ctxt[OF subst_closed_less this, of \<box>]
      have "(l \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
    then show ?thesis by auto
  qed  
qed
  
lemma Ei_oriented_reducible_in_RiEw: 
  assumes "(l,r) \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" and "l\<cdot>\<sigma> \<succ> r\<cdot>\<sigma>"
  shows "(\<exists>r'. (l,r') \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<and> l\<cdot>\<sigma> \<succ> r'\<cdot>\<sigma>) \<or> l \<notin> NF (ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))"
  using assms
proof (induct "{#l, r#}" arbitrary: l r \<sigma> rule: SN_induct [OF lessenc_op.SN])
  case 1
  note IH = this
  have comm: "\<And>t u. {#t, u#} =  {#u, t#}" using add_mset_commute by auto
  show ?case
  proof (cases "(l, r) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>")
    case True
    with 1 show ?thesis by auto
  next
    case False
    with 1(2) Einf_sym_without_Ew_sym obtain j where lr_cases:
      "((l, r) \<in> (E j) \<and> (l, r) \<notin> (E (Suc j))) \<or> ((r, l) \<in> (E j) \<and> (r, l) \<notin> (E (Suc j)))" by auto
    define u' where "u' \<equiv> if (l, r) \<in> (E j) \<and> (l, r) \<notin> (E (Suc j)) then l else r"
    define v' where "v' \<equiv> if (l, r) \<in> (E j) \<and> (l, r) \<notin> (E (Suc j)) then r else l"
    from lr_cases have uv:"(u', v') \<in> (E j)" "(u', v') \<notin> E (Suc j)" by (auto simp: u'_def v'_def)
    have uv_cases:"(u' = l \<and> v' = r) \<or> (u' = r \<and> v' = l)" by (auto simp: u'_def v'_def)
    
    let ?ordstep = "ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
    from ordstep_rstep_conv[OF _ Rinf_less] subst.closedI[of "{\<succ>}"] subst have
      ordstep_rstep:"ordstep {\<succ>} R\<^sub>\<infinity> = rstep R\<^sub>\<infinity>" by auto
    note ordstep_mono = ordstep_mono[of _ "R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>", OF _ subset_refl, of _ "{\<succ>}"]
      
    from subst[of r l \<sigma>] trans[OF IH(3)] irrefl have not_r_succ_l:"\<not> (r \<succ> l)" by auto
    let ?enc = "encstep1 (E (Suc j)) (R (Suc j)) O (E (Suc j))\<^sup>\<leftrightarrow>"
    from uv oKBi_E_supset' [OF irun [of j]]
      consider "(u', v') \<in> R (Suc j)" | "(v', u') \<in> R (Suc j)" | "u' = v'" | "(u', v') \<in> ?enc\<^sup>\<leftrightarrow>"
      by auto blast
    then show ?thesis
    proof (cases)
      case 1
      from not_r_succ_l Ri_less[of "Suc j"] 1 have uv:"u' = l" "v' = r" using uv_cases by auto
      from 1 ordstep_rstep have "(l,r) \<in> ordstep {\<succ>} R\<^sub>\<infinity>" unfolding uv by auto
      with ordstep_mono show ?thesis by auto
    next
      case 2
      from not_r_succ_l Ri_less[of "Suc j"] 2 have uv:"u' = r" "v' = l" using uv_cases by auto
      from 2 ordstep_rstep have "(l,r) \<in> ordstep {\<succ>} R\<^sub>\<infinity>" unfolding uv by auto
      with ordstep_mono show ?thesis by auto
    next
      case 3
      from irrefl IH(3) uv_cases show ?thesis unfolding 3 by auto
    next
      case 4
      then obtain u v w where v: "(u, w) \<in> encstep1 (E (Suc j)) (R (Suc j))" "(w, v) \<in> (E (Suc j))\<^sup>\<leftrightarrow>"
        and uv_cases:"(u = l \<and> v = r) \<or> (u = r \<and> v = l)" using uv_cases by auto
          
      show ?thesis proof(cases "u = l")
        case True
        from v(1) have "u \<notin> NF (ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))"
        proof (cases)
          case (estep l\<^sub>0 r\<^sub>0 D \<tau>)
          from encompeq.intros [of u D "l\<^sub>0 \<cdot> \<tau>" Var] encompeq.intros [of "r\<^sub>0 \<cdot> \<tau>" \<box>] estep(2)
            have u_l0:"l\<^sub>0 \<cdot> \<tau> \<unlhd>\<cdot> u" "r\<^sub>0 \<unlhd>\<cdot> r\<^sub>0 \<cdot> \<tau>" by auto
          with estep have ur0: "u \<cdot>\<succ> r\<^sub>0" "u \<cdot>\<succ> l\<^sub>0" unfolding lessencp_def by blast+
          note mul = ns_s_mul_ext_union_multiset_l[OF ns_mul_ext_bottom, of "{#u#}" "{#l\<^sub>0, r\<^sub>0#}"]    
          with ur0 have "({#u, v#}, {#l\<^sub>0, r\<^sub>0#}) \<in> mulless" using multi_member_last by auto
          with uv_cases comm[of l r] have "({#l, r#}, {#l\<^sub>0, r\<^sub>0#}) \<in> mulless" by presburger
          from IH(1)[OF this _ estep(4)] estep(1) Ew_reducible_aux  
            have NF1:"l\<^sub>0 \<cdot> \<tau> \<notin> NF (ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))" by auto
          from u_l0 obtain C\<^sub>u \<sigma>\<^sub>u where u:"u = C\<^sub>u\<langle>l\<^sub>0 \<cdot> \<tau> \<cdot> \<sigma>\<^sub>u\<rangle>" unfolding encompeq.simps by auto
          from NF1 ordstep_subst_ctxt[OF subst_closed_less] show ?thesis unfolding u by blast
        next
          case rstep
          with ordstep_rstep have "(u, w) \<in> ordstep {\<succ>} R\<^sub>\<infinity>" by force
          with ordstep_mono[of "R\<^sub>\<infinity>"] show ?thesis by auto
        qed
        with True show ?thesis by auto
      next
        case False
        with uv_cases have uv:"u = r" "v = l" by auto
        from v(1) encstep1_less Ri_less have rw:"r \<succ> w" unfolding uv by auto
        from rw mset_two2[of r w l] have "({#l, r#}, {#l, w#}) \<in> mulless" using lessencp_def by fast
        from IH(1)[OF this _ trans[OF IH(3) subst, OF rw]] v(2) show ?thesis unfolding uv by fast
      qed
    qed
  qed
qed

lemma Sw_SS:"S\<^sub>\<omega> = \<S> R\<^sub>\<omega> E\<^sub>\<omega>" unfolding Sw_def E_ord_def by auto
  
lemma Ri_reducible_in_RwEw: 
  assumes "(l,r) \<in> R\<^sub>\<infinity>"
  shows "l \<notin> NF (rstep S\<^sub>\<omega>)"
  using assms
proof (induct "(l, r)" arbitrary: l r rule: SN_induct [OF SN_lexless])
  case 1
  note IH = this
  let ?ordstep = "ordstep {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
  show ?case 
  proof (cases "(l, r) \<in> R\<^sub>\<omega>")
    case True
    then show ?thesis unfolding Sw_def by auto
  next
    case False
    with Rinf_without_Rw[OF IH(2)] obtain i where
      not_i: "(l, r) \<notin> R (Suc i)" and pred_i: "(l, r) \<in> R i" by auto
    let ?Ri = "R (Suc i)" and ?Ei = "E (Suc i)"
    from pred_i oKBi_R_supset [OF irun [of i]] and not_i
      consider "(l, r) \<in> encstep2 ?Ei ?Ri O ?Ei" | "(l, r) \<in> ?Ri O (ostep ?Ei ?Ri)\<inverse>" by blast
    then show ?thesis
    proof (cases)
      case 1
      then obtain u where u: "(l, u) \<in> encstep2 ?Ei ?Ri" by auto
      then show ?thesis
      proof(cases)
        case (estep l\<^sub>0 r\<^sub>0 C \<sigma>)
        with Ei_oriented_reducible_in_RiEw[OF _ estep(4)] consider
          "\<exists>r'. (l\<^sub>0, r') \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<and> l\<^sub>0 \<cdot> \<sigma> \<succ> r' \<cdot> \<sigma>" | "l\<^sub>0 \<notin> NF (ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))" by auto
        then show ?thesis proof(cases)
          case 1
          then obtain r' where r':"(l\<^sub>0, r') \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "l\<^sub>0 \<cdot> \<sigma> \<succ> r' \<cdot> \<sigma>" by auto
          then have "(l\<^sub>0 \<cdot> \<sigma>, r' \<cdot> \<sigma>) \<in> rstep S\<^sub>\<omega>" unfolding Sw_def by auto
          then show ?thesis unfolding estep by fast
        next
          case 2
          then obtain t where "(l\<^sub>0, t) \<in> ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
          with ordstep_Un consider "(l\<^sub>0, t) \<in> ordstep {\<succ>} (E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" | "(l\<^sub>0, t) \<in> ordstep {\<succ>} R\<^sub>\<infinity>" by auto
          then show ?thesis proof(cases)
            case 1
            from ordstep_subst_ctxt[OF subst_closed_less 1] ordstep_mono
              have "(l, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> ordstep {\<succ>} (E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" unfolding estep by auto
            with ordstep_mono[of "E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>"]  have "(l, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> ?ordstep" by auto
            with Sw_SS ordstep_subset_S[OF Rw_less]
              have "(l, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> rstep S\<^sub>\<omega>" unfolding ordstep_S_conv[OF Rw_less] by auto
            then show ?thesis by fast
          next
            case 2
            from ordstep_imp_rstep[OF this] obtain l\<^sub>1 r\<^sub>1 D \<tau>
              where lr1:"l\<^sub>0 = D\<langle>l\<^sub>1\<cdot>\<tau>\<rangle>" "t = D\<langle>r\<^sub>1\<cdot>\<tau>\<rangle>" "(l\<^sub>1,r\<^sub>1) \<in> R\<^sub>\<infinity>" by fast
            from encompeq.intros[OF lr1(1)] estep(5) have "l \<cdot>\<succ> l\<^sub>1" using lessencp_def by auto
            then have "((l, r), l\<^sub>1, r\<^sub>1) \<in> lexless" by auto
            from IH(1)[OF this lr1(3)] obtain t' where lt:"(l\<^sub>1, t') \<in> rstep S\<^sub>\<omega>" by auto
            then show ?thesis unfolding lr1 estep by fast
          qed
        qed
      next
        case (rstep l\<^sub>0 r\<^sub>0 C \<sigma>)
        from rstep(4) have "l \<cdot>\<succ> l\<^sub>0" using lessencp_def by auto
        then have "((l, r), l\<^sub>0, r\<^sub>0) \<in> lexless" using lessencp_def by auto
        from IH(1)[OF this] rstep(1) have "l\<^sub>0 \<notin> NF_trs S\<^sub>\<omega>" by auto
        then show ?thesis unfolding rstep(2) by blast
      qed
    next
      case 2
      then obtain r' where r':"(l,r') \<in> ?Ri" "(r,r') \<in> ostep ?Ei ?Ri" by fast
      from ostep_imp_less[OF Ri_less this(2)] have "r \<cdot>\<succ> r'" using lessencp_def by fast
      then have "((l, r), l, r') \<in> lexless" by auto
      from IH(1)[OF this] r'(1) show ?thesis by auto
    qed
  qed
qed

lemma Ei_oriented_reducible_in_RwEw: 
  assumes "(l,r) \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" and "l\<cdot>\<sigma> \<succ> r\<cdot>\<sigma>"
  shows "l\<cdot>\<sigma> \<notin> NF_trs S\<^sub>\<omega>"
proof-
  from Ew_reducible_aux[OF Ei_oriented_reducible_in_RiEw[OF assms]]
    have "\<exists>t. (l\<cdot>\<sigma>, t) \<in> ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
  then obtain t where t:"(l\<cdot>\<sigma>, t) \<in> ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
  { assume "(l\<cdot>\<sigma>, t) \<in> ordstep {\<succ>} R\<^sub>\<infinity>"
    from ordstep_imp_rstep[OF this] obtain C \<tau> l\<^sub>0 r\<^sub>0 where
      lr0:"(l\<^sub>0, r\<^sub>0) \<in> R\<^sub>\<infinity>" and lt:"l \<cdot> \<sigma> = C\<langle>l\<^sub>0 \<cdot> \<tau>\<rangle>" by fast
    from Ri_reducible_in_RwEw[OF lr0] have "l \<cdot> \<sigma> \<notin> NF_trs S\<^sub>\<omega>" unfolding lt by fastforce
  } note Rinf = this
  { assume a:"(l\<cdot>\<sigma>, t) \<in> ordstep {\<succ>} (E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
    with ordstep_mono[of "E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>"]  have "(l\<cdot>\<sigma>, t) \<in> ordstep {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
            with Sw_SS ordstep_subset_S[OF Rw_less]
              have "(l\<cdot>\<sigma>, t) \<in> rstep S\<^sub>\<omega>" unfolding ordstep_S_conv[OF Rw_less] by auto
  }
  with t Rinf show ?thesis unfolding ordstep_Un by auto
qed
  
lemma NF_Sw_subset_NF_Sinf: "NF_trs S\<^sub>\<omega> \<subseteq> NF_trs (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)"
proof-
  { fix s t
    assume "(s,t) \<in> rstep (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)"
    then consider "(s,t) \<in> rstep R\<^sub>\<infinity>" | "(s,t) \<in> rstep (E_ord (\<succ>) E\<^sub>\<infinity>)"
      by (auto simp: rstep_simps)
    then have "s \<notin> NF_trs S\<^sub>\<omega>"
    proof (cases)
      case 1
      from rstepE[OF this] NF_subterm[of s "R\<^sub>\<infinity>"] show ?thesis using Ri_reducible_in_RwEw
        by (metis NF_instance NF_subterm ctxt_imp_supteq)
    next
      case 2
      then obtain l r C \<sigma> where "(l,r) \<in> E_ord (\<succ>) E\<^sub>\<infinity>" and st:"s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
      then obtain l' r' \<tau> where lr:"l = l' \<cdot> \<tau>" "r = r' \<cdot> \<tau>" and ord:"(l', r') \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" "l' \<cdot> \<tau> \<succ> r' \<cdot> \<tau>"
        unfolding E_ord_def by fast
      from subst[OF ord(2)] Ei_oriented_reducible_in_RwEw[OF ord(1), of "\<tau> \<circ>\<^sub>s \<sigma>"] show ?thesis
        unfolding st lr by fastforce
    qed
  }
  then show ?thesis unfolding NF_def by auto
qed

lemma Sw_subset_Sinf:"S\<^sub>\<omega> \<subseteq> \<S> R\<^sub>\<infinity> E\<^sub>\<infinity>"
  unfolding Sw_SS using Rw_subset_Rinf E_ord_mono[OF Ew_subset_Einf] by auto

lemma NF_Sw_NF_Sinf: "NF_trs S\<^sub>\<omega> = NF_trs (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)"
  using NF_Sw_subset_NF_Sinf NF_trs_mono[OF Sw_subset_Sinf] by auto

lemma SN_Sinf:"SN (rstep (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>))"
  using ordstep_S_conv[OF Rinf_less] by (metis SN_ordstep)

context
  assumes fair: "\<And>s t. (s, t)\<in> PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, t) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep S\<^sub>\<omega>)\<^sup>\<down>"
begin
  
lemma msteps_imp_source_steps:
  assumes "\<forall> t \<in># M. s \<succ> t"
  shows "(mstep M \<R>)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (\<Union>z \<in> {z. s \<succ> z}. slab \<R> z)\<^sup>\<leftrightarrow>\<^sup>*"
proof-
  have "mstep M \<R> \<subseteq> (\<Union>z \<in> {z. s \<succ> z}. slab \<R> z)"
  proof
    fix t u
    assume a: "(t, u) \<in> mstep M \<R>"
    then have tu: "(t, u) \<in> rstep \<R>" unfolding mstep_def mem_Collect_eq by auto
    from a have "\<exists> v \<in># M. v \<succeq> t" unfolding mstep_def mem_Collect_eq by auto
    with assms transD [OF trans_less] have st: "s \<succ> t" by blast
    from tu have "(t, u) \<in> slab \<R> t" unfolding source_step_def by auto
    with st show "(t, u) \<in> (\<Union>z \<in> {z. s \<succ> z}. slab \<R> z)" by auto
  qed
  from conversion_mono [OF this] show ?thesis by auto
qed

text \<open>Establish peak decreasingness of \<open>S\<^sub>\<omega>\<close> steps on ground terms for correctness result below.\<close>
lemma ground_Sw_peak_decreasing:
  assumes "ground s" and "(s, t) \<in> slab S\<^sub>\<omega> s" and "(s, u) \<in> slab S\<^sub>\<omega> s"
  shows "(t, u) \<in> (\<Union> v \<in> {v. ground v \<and> s \<succ> v}. slab S\<^sub>\<omega> v)\<^sup>\<leftrightarrow>\<^sup>*"
proof-
  from assms have rsteps: "(s, t) \<in> rstep S\<^sub>\<omega>" "(s, u) \<in> rstep S\<^sub>\<omega>" unfolding source_step_def by auto
  note vc = SN_imp_variable_condition [OF SN_Sw_step]
  from vc peak_imp_nabla2 [OF _ rsteps] have tu: "(t, u) \<in> nabla S\<^sub>\<omega> s ^^ 2" by auto
  have Sw_less: "S\<^sub>\<omega> \<subseteq> {\<succ>}" using Ri_less unfolding Sw_def R\<^sub>\<omega>_def by fast
  from compatible_rstep_imp_less [OF Sw_less] have Sw_step_less: "rstep S\<^sub>\<omega> \<subseteq> {\<succ>}" by blast
  let ?less_s_conv = "(\<Union>z\<in>{z. s \<succ> z}. slab S\<^sub>\<omega> z)\<^sup>\<leftrightarrow>\<^sup>*"
  let ?leq_conv = "\<lambda> v. (\<Union>z\<in>{z. v \<succeq> z}. slab S\<^sub>\<omega> z)\<^sup>\<leftrightarrow>\<^sup>*"
  { fix v w
    assume vw: "(v, w) \<in> nabla S\<^sub>\<omega> s" and "ground v" and "ground w" and "s \<succ> v" and "s \<succ> w"
    then have vw: "(v, w) \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down> \<or> (v, w) \<in> (rstep (PCP S\<^sub>\<omega>))\<^sup>\<leftrightarrow>" unfolding nabla_def by auto
    { assume "(v, w) \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down>"
      then obtain x where vx: "(v, x) \<in> (rstep S\<^sub>\<omega>)\<^sup>*" and wx: "(w, x) \<in> (rstep S\<^sub>\<omega>)\<^sup>*"
        unfolding join_def rtrancl_converse by blast
      from rsteps_slabI [OF vx _ Sw_step_less, of v] have "(v, x) \<in> ?leq_conv v" by auto
      from slab_conv_less_label [OF this] \<open>s \<succ> v\<close> have vx: "(v, x) \<in> ?less_s_conv" by auto
      from rsteps_slabI [OF wx _ Sw_step_less, of w] have "(w, x) \<in> ?leq_conv w" by auto
      from slab_conv_less_label [OF this] \<open>s \<succ> w\<close> have "(x, w) \<in> ?less_s_conv"
        unfolding conversion_inv by auto
      from conversion_trans' [OF vx this] have "(v, w) \<in> ?less_s_conv" by auto
    } note if_joinable = this
    { assume "(v, w) \<in> (rstep (PCP S\<^sub>\<omega>))\<^sup>\<leftrightarrow>"
      from PCP_xPCP [OF Rw_less \<open>ground v\<close> \<open>ground w\<close> this [unfolded Sw_def, folded E_ord_def]]
      have vw: "(v, w) \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down> \<or> (v, w) \<in> (rstep (PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)))\<^sup>\<leftrightarrow>"
        unfolding Sw_def E_ord_def by auto
      { assume "(v, w) \<in> (rstep (PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)))\<^sup>\<leftrightarrow>"
        then obtain v' w' C \<sigma> where step:"v = C\<langle>v'\<cdot>\<sigma>\<rangle>" "w = C\<langle>w'\<cdot>\<sigma>\<rangle>" "(v',w') \<in> (PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>" 
          unfolding Un_iff converse_iff by auto
        note pcp = this(3)[unfolded Un_iff converse_iff]
        with fair[of v' w'] fair[of w' v'] have alt:"(v', w') \<in>  (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<or> (v', w') \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down>" 
          using join_sym converse_iff subsetCE by blast
        from rstep_rstep rstep_union have 1:"(v', w') \<in>  (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<Longrightarrow> (v, w) \<in>  (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>"
          unfolding step by auto
        have 2:"(v', w') \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down> \<Longrightarrow> (v, w) \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down>" unfolding step by auto
        { assume "(v, w) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>" 
          from ground_Einf_Sw [OF this \<open>ground v\<close> \<open>ground w\<close>] have vw: "(v, w) \<in> (mstep {#v, w#} S\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" .
          from \<open>s \<succ> v\<close> \<open>s \<succ> w\<close> have "\<forall> t \<in># {#v, w#}. s \<succ> t" by auto
          from vw msteps_imp_source_steps [OF this] have "(v, w) \<in> ?less_s_conv" by auto
        }
        with alt vw 1 2 if_joinable have "(v, w) \<in> ?less_s_conv" by auto
      }
        with vw if_joinable have "(v, w) \<in> ?less_s_conv" by auto
      }
    with vw if_joinable have "(v, w) \<in> ?less_s_conv" by auto
  } note nabla_slab = this
  from tu obtain v where v: "(t, v) \<in> nabla S\<^sub>\<omega> s" "(v, u) \<in> nabla S\<^sub>\<omega> s" by auto
  note gimp = rstep_ground [OF _ \<open>ground s\<close>]
  from this [OF _ rsteps(1)] this [OF _ rsteps(2)] vc have "ground t" "ground u" by auto
  from v [unfolded nabla_def] rstep_ground [OF _ \<open>ground s\<close>] have sv: "(s, v) \<in> (rstep S\<^sub>\<omega>)\<^sup>+" by auto
  from rsteps_ground [OF _ \<open>ground s\<close> trancl_into_rtrancl [OF this]] vc have "ground v" by fast
  from sv rsteps_subset_less [OF Sw_less] have sv: "s \<succ> v" by auto
  from Sw_step_less rsteps have st: "s \<succ> t" and su: "s \<succ> u" by auto
  note tv = nabla_slab [OF v(1) \<open>ground t\<close> \<open>ground v\<close> st sv]
  note vu = nabla_slab [OF v(2) \<open>ground v\<close> \<open>ground u\<close> sv su]
  from ground_less [OF \<open>ground s\<close>] have "{v. ground v \<and> s \<succ> v} = {v. s \<succ> v}" by auto
  with conversion_trans' [OF tv vu] show ?thesis by auto
qed

lemma correctness_okb: "GCR (rstep S\<^sub>\<omega>) \<and> SN (rstep S\<^sub>\<omega>) \<and> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  interpret ars_peak_decreasing "slab S\<^sub>\<omega>" "{t. ground t}" "(\<succ>)"
    by (unfold_locales, insert ground_Sw_peak_decreasing SN_less, auto)
  from CR have CR: "CR (\<Union>t \<in> {t. ground t}. slab S\<^sub>\<omega> t)" by auto
  from rstep_ground SN_imp_variable_condition [OF SN_Sw_step]
  have "\<And> s t. ground s \<Longrightarrow> (s, t) \<in> rstep S\<^sub>\<omega> \<Longrightarrow> ground t" by fastforce
  then have "(\<Union>t \<in> {t. ground t}. slab S\<^sub>\<omega> t) = GROUND (rstep S\<^sub>\<omega>)" unfolding source_step_def GROUND_def
    by blast
  with CR have "GCR (rstep S\<^sub>\<omega>)" unfolding GROUND_def source_step_def by auto
  with SN_Sw_step oKBi_conversion_ERw show ?thesis by auto
qed

lemma PCP_oriented_xPCP:
  assumes R_less:"\<R> \<subseteq> {\<succ>}"
  shows "PCP \<R> \<subseteq> PCP_ext \<R>"
proof
  fix s t
  assume "(s, t) \<in> PCP \<R>"
  then obtain \<mu> l\<^sub>1 r\<^sub>1 p l\<^sub>2 r\<^sub>2 where o: "overlap \<R> \<R> (l\<^sub>1, r\<^sub>1) p (l\<^sub>2, r\<^sub>2)"
    and "the_mgu l\<^sub>1 (l\<^sub>2 |_ p) = \<mu>"
    and s: "s = replace_at l\<^sub>2 p r\<^sub>1 \<cdot> \<mu>"
    and t: "t = r\<^sub>2 \<cdot> \<mu>"
    and NF: "\<forall>u \<lhd> l\<^sub>1 \<cdot> \<mu>. u \<in> NF (rstep \<R>)"
    by (auto simp: PCP_def the_mgu_def mgu_def split: option.splits)
  then have mgu: "mgu l\<^sub>1 (l\<^sub>2 |_ p) = Some \<mu>"
    by (auto simp: the_mgu_def unifiers_def overlap_def split: option.splits dest!: mgu_complete)
  have p: "p \<in> fun_poss l\<^sub>2" using o by (auto simp: overlap_def)
  from o have rules:"\<exists>p. p \<bullet> (l\<^sub>1, r\<^sub>1) \<in> \<R>" "\<exists>p. p \<bullet> (l\<^sub>2, r\<^sub>2) \<in> \<R>" "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}"
    unfolding overlap_def by auto
  { fix l r p
    assume "p \<bullet> (l,r) \<in> \<R>"
    with R_less have "l \<succ> r" using perm_R_less perm_less by blast
    with subst have "l \<cdot> \<mu> \<succ> r \<cdot> \<mu>" by auto
    from trans[OF this] have "r \<cdot> \<mu> \<succ> l \<cdot> \<mu> \<Longrightarrow> l \<cdot> \<mu> \<succ> l \<cdot> \<mu>" by auto
    with SN_imp_acyclic[OF SN_less] trans have "(r \<cdot> \<mu>, l \<cdot> \<mu>) \<notin> {\<succ>}" unfolding acyclic_def by blast
  }
  then have orientation:"(r\<^sub>1 \<cdot> \<mu>, l\<^sub>1 \<cdot> \<mu>) \<notin> {\<succ>} \<and> (r\<^sub>2 \<cdot> \<mu>, l\<^sub>2 \<cdot> \<mu>) \<notin> {\<succ>}"
    using o[unfolded overlap_def] by auto
  from s[unfolded subst_apply_term_ctxt_apply_distrib]
  have s:"s = (ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<mu>))\<langle>r\<^sub>1 \<cdot> \<mu>\<rangle>"
    using ctxt_of_pos_term_subst[OF fun_poss_imp_poss[OF p]] by metis
  from rules p mgu orientation
  have ooverlap:"ooverlap {\<succ>} \<R> (l\<^sub>1, r\<^sub>1) (l\<^sub>2, r\<^sub>2) p \<mu> s t"
    unfolding ooverlap_def fst_conv snd_conv s t by simp
  from NF ordstep_rstep_conv[OF _ R_less] subst have prime: "\<forall>u\<lhd>l\<^sub>1 \<cdot> \<mu>. u \<in> NF (ordstep {\<succ>} \<R>)"
    by fastforce
  with ooverlap show "(s, t) \<in> PCP_ext \<R>" unfolding PCP_ext_def by force
qed

lemma Ew_empty_CR_Rw_gtotal:
  assumes "E\<^sub>\<omega> = {}"
  shows "CR (rstep R\<^sub>\<omega>)"
proof-
  have SR[simp]:"S\<^sub>\<omega> = R\<^sub>\<omega>" unfolding Sw_def assms by auto
  from fair PCP_oriented_xPCP[OF Rw_less] have fair:"PCP R\<^sub>\<omega> \<subseteq> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep R\<^sub>\<omega>)\<^sup>\<down>"
    unfolding assms SR by (simp add: subset_iff)
  interpret okb_irun_nonfailing by (unfold_locales, insert fair assms, auto)
  from Ew_empty_implies_CR_Rw show ?thesis by auto
qed

end
end

locale permuted_ordered_completion_inf = ordered_completion_inf + fgtotal_reduction_order less UNIV +
 fixes R E n
 assumes R0: "R 0 = {}"
    and ERn: "(E n \<union> R n) - Id \<noteq> {}"
    and permuted_run: "\<forall>i < n. (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>\<pi> (E (Suc i), R (Suc i))"
    and variant_free: "\<forall>i \<le> n. variant_free_trs (E i) \<and> variant_free_trs (R i)"
    and fair:"\<forall>(s, t) \<in> gtotal_okb_irun_inf.PCP_ext (\<succ>) (R n \<union> (E n)\<^sup>\<leftrightarrow>). (s, t) \<in> (rstep (\<Union>i\<le>n. E i))\<^sup>\<leftrightarrow>"
begin

abbreviation Sw_permuted ("S\<^sub>\<omega>\<^sup>\<pi>") where "S\<^sub>\<omega>\<^sup>\<pi> \<equiv> (R n) \<union> E_ord (\<succ>) (E n)"

lemma (in gtotal_okb_irun_inf) pcp_litsim :
  assumes "(s, t) \<in> PCP_ext \<R>\<^sub>1" and "\<R>\<^sub>1 \<doteq> \<R>\<^sub>2"
  shows "(s,t) \<in> PCP_ext \<R>\<^sub>2"
proof-
  note litsim_defs = subsumable_trs.litsim_def subsumeseq_trs_def
  from assms[unfolded PCP_ext_def] obtain \<rho> \<rho>' p \<mu> where
    o:"ooverlap {\<succ>} \<R>\<^sub>1 \<rho> \<rho>' p \<mu> s t" and prime:"\<forall>u\<lhd>fst \<rho> \<cdot> \<mu>. u \<in> NF (ordstep {\<succ>} \<R>\<^sub>1)" by auto
  from this(1)[unfolded ooverlap_def] have "(\<exists>p. p \<bullet> \<rho> \<in> \<R>\<^sub>1) \<and> (\<exists>p. p \<bullet> \<rho>' \<in> \<R>\<^sub>1)" by auto
  with assms(2) have "\<exists>p. p \<bullet> \<rho> \<in> \<R>\<^sub>2 \<and> (\<exists>p. p \<bullet> \<rho>' \<in> \<R>\<^sub>2)" unfolding litsim_defs
    by (metis rule_pt.permute_plus)
  with o have ooverlap:"ooverlap {\<succ>} \<R>\<^sub>2 \<rho> \<rho>' p \<mu> s t" unfolding ooverlap_def by meson
  have "\<forall>u\<lhd>fst \<rho> \<cdot> \<mu>. u \<in> NF (ordstep {\<succ>} \<R>\<^sub>2)"
  proof(rule, rule)
    fix u
    assume "fst \<rho> \<cdot> \<mu> \<rhd> u"
    with prime have nf:"u \<in> NF (ordstep {\<succ>} \<R>\<^sub>1)" by auto
    from ordstep_permute_litsim[OF _ subsumable_trs.litsim_sym[OF assms(2)], of _ _ 0]
    have "ordstep {\<succ>} \<R>\<^sub>2 \<subseteq> ordstep {\<succ>} \<R>\<^sub>1" by auto 
    from NF_anti_mono[OF this] nf show "u \<in> NF (ordstep {\<succ>} \<R>\<^sub>2)" by auto
  qed
  with ooverlap show ?thesis unfolding PCP_ext_def by blast
qed

lemma correctness_oKB_permute: "GCR (rstep S\<^sub>\<omega>\<^sup>\<pi>) \<and> SN (rstep S\<^sub>\<omega>\<^sup>\<pi>) \<and> (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n \<union> E n))\<^sup>\<leftrightarrow>\<^sup>*"
proof-
  note litsim_defs = subsumable_trs.litsim_def subsumeseq_trs_def
  from oKB_permute_run[OF permuted_run variant_free] R0 obtain E' R' where
    run:"\<forall>i<n. (E' i, R' i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E' (Suc i), R' (Suc i))" "\<forall>i\<le>n. E i \<doteq> E' i \<and> R i \<doteq> R' i" by force
  from run(2)[rule_format, of 0] R0 have "R' 0 = {}" unfolding litsim_defs by fast
  with run(1)[rule_format] oKBi_conversion R0 have conversion:"(rstep (E' 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E' n \<union> R' n))\<^sup>\<leftrightarrow>\<^sup>*" by (induct n) auto
  from run(2)[rule_format, of n] have ERn_litsim:"E n \<doteq> E' n" "R n \<doteq> R' n" by auto
  from ERn obtain s' t' where "(s',t') \<in> E n \<union> R n" "s' \<noteq> t'" by auto
  with ERn_litsim obtain s t where st:"(s,t) \<in> E' n \<union> R' n" "s \<noteq> t" unfolding litsim_defs
    by (metis UnE UnI1 UnI2 rule_pt.permute_prod.simps term_pt.permute_eq_iff)
  define Ei ("E\<^sub>i") where "E\<^sub>i \<equiv> \<lambda>i. if i \<le> n then E' i else if (t,t) \<in> E' n then E' n else if even (i - n) then E' n - {(t,t)} else E' n \<union> {(t,t)}"
  define Ri ("R\<^sub>i") where "R\<^sub>i \<equiv> \<lambda>i. if i \<le> n then R' i else R' n"
  { fix i
    have "(E\<^sub>i i, R\<^sub>i i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E\<^sub>i (Suc i), R\<^sub>i (Suc i))" proof(cases "i < n")
      case True
      with run(1)[rule_format, of i] show ?thesis unfolding Ri_def Ei_def by auto
    next
      case False
      then have "i \<ge> n" by auto
      then show ?thesis proof(cases "(t,t) \<in> E' n")
        case True
        with \<open>i \<ge> n\<close> have eqs:"E\<^sub>i i = E' n" "R\<^sub>i i = R' n" "E\<^sub>i (Suc i) = E' n" "R\<^sub>i (Suc i) = R' n"
          unfolding Ri_def Ei_def by auto
        from st have "(s,t) \<in> rstep (R' n \<union> (E' n)\<^sup>\<leftrightarrow>)" by auto
        from oKBi.deduce[OF this this] insert_absorb[OF True] show ?thesis unfolding eqs by auto
      next
        case False
        note tt_nomem = this
      then show ?thesis proof(cases "i=n")
        case True
        with \<open>i \<ge> n\<close> have eqs:"E\<^sub>i i = E' n" "R\<^sub>i i = R' n" "E\<^sub>i (Suc i) = E' n \<union> {(t,t)}" "R\<^sub>i (Suc i) = R' n"
          unfolding Ri_def Ei_def by auto
        from st have "(s,t) \<in> rstep (R' n \<union> (E' n)\<^sup>\<leftrightarrow>)" by auto
        with oKBi.deduce show ?thesis unfolding eqs by auto
      next
        case False
        show ?thesis proof(cases "even (i - n)")
        case True
        then have eqs:"E\<^sub>i i = E' n - {(t,t)}" "R\<^sub>i i = R' n" "E\<^sub>i (Suc i) = E' n \<union> {(t,t)}" "R\<^sub>i (Suc i) = R' n"
          using \<open>i \<ge> n\<close> False tt_nomem unfolding Ri_def Ei_def by auto
        from st have "(s,t) \<in> rstep (R' n \<union> (E' n - {(t,t)})\<^sup>\<leftrightarrow>)" by auto
        from st(2) oKBi.deduce[OF this this] show ?thesis unfolding eqs by force
      next
        case False
        then have eqs:"E\<^sub>i i = E' n \<union> {(t,t)}" "R\<^sub>i i = R' n" "E\<^sub>i (Suc i) = E' n - {(t,t)}" "R\<^sub>i (Suc i) = R' n" 
          using \<open>i \<noteq> n\<close> \<open>i \<ge> n\<close> tt_nomem unfolding Ri_def Ei_def by auto
        with oKBi.delete[of t "E\<^sub>i i"] show ?thesis unfolding eqs by auto
      qed
    qed
  qed
qed
  }
  note irun = this
  from \<open>R' 0 = {}\<close> have "R\<^sub>i 0 = {}" unfolding Ri_def by auto
  interpret gtotal_okb_irun_inf R\<^sub>i E\<^sub>i "(\<succ>)" by (standard, insert fgtotal irun \<open>R\<^sub>i 0 = {}\<close>, auto)
  have Rw:"R\<^sub>\<omega> = R' n" proof
    have "\<And>i. (\<Inter>j\<in>{j. j\<ge>i}. R\<^sub>i j) \<subseteq> R' n" by (rule Inter_lower, insert Ri_def, auto)
    then show "R\<^sub>\<omega> \<subseteq> R' n" unfolding R\<^sub>\<omega>_def by blast
  next
    have "R' n \<subseteq> (\<Inter>j\<in>{j. j\<ge>n}. R\<^sub>i j)" by (rule Inter_greatest, insert Ri_def, auto)
    then show "R' n \<subseteq> R\<^sub>\<omega>" unfolding R\<^sub>\<omega>_def by fast
  qed
  have Ew:"E\<^sub>\<omega> = E' n" proof(cases "(t,t) \<in> E' n")
    case True
    then have En:"\<And>i. i \<ge> n \<Longrightarrow> E\<^sub>i i = E' n" unfolding Ei_def by auto
    show ?thesis proof
      have "\<And>i. (\<Inter>j\<in>{j. j\<ge>i}. E\<^sub>i j) \<subseteq> E' n" by (rule Inter_lower, insert En Ei_def True, auto) 
      then show "E\<^sub>\<omega> \<subseteq> E' n" unfolding E\<^sub>\<omega>_def by blast
    next
      have "E' n \<subseteq> (\<Inter>j\<in>{j. j\<ge>n}. E\<^sub>i j)" by (rule Inter_greatest, insert En, force)
      then show "E' n \<subseteq> E\<^sub>\<omega>" unfolding E\<^sub>\<omega>_def by fast
    qed
  next
    case False
    then have En:"\<And>i. i>n \<Longrightarrow> E\<^sub>i i = E' n - {(t,t)} \<or> E\<^sub>i (Suc i) = E' n - {(t,t)}" unfolding Ei_def by auto
    with False have En':"E\<^sub>i (n + 2) = E' n - {(t,t)}" unfolding Ei_def by auto
    { fix i
      from En' have 1:"i \<le> n \<Longrightarrow> \<exists>j \<ge> i. E\<^sub>i j = E' n - {(t,t)}" by (meson trans_le_add1)
      from En[of i] have "i > n \<Longrightarrow> \<exists>j \<ge> i. E\<^sub>i j = E' n - {(t,t)}" by (meson le_SucI order_refl)
      with 1 have "\<exists>j \<ge> i. E\<^sub>i j = E' n - {(t,t)}" by (cases "i > n", auto)
    } note ex = this
    show ?thesis proof
      have "\<And>i. (\<Inter>j\<in>{j. j\<ge>i}. E\<^sub>i j) \<subseteq> E' n - {(t,t)}" by (rule Inter_lower, insert ex, force)
      then show "E\<^sub>\<omega> \<subseteq> E' n" unfolding E\<^sub>\<omega>_def by blast
    next
      from En have above_i:"\<And>i. i \<ge> n \<Longrightarrow> E' n - {(t,t)} \<subseteq> E\<^sub>i i" unfolding Ei_def by auto
      have "E' n - {(t,t)} \<subseteq> (\<Inter>j\<in>{j. j\<ge>n}. E\<^sub>i j)" by (rule Inter_greatest, insert above_i, force)
      with False show "E' n \<subseteq> E\<^sub>\<omega>" unfolding E\<^sub>\<omega>_def by fast
    qed
  qed
  have fair:"\<forall>(s, t) \<in> PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>). (s, t) \<in> (rstep Einf)\<^sup>\<leftrightarrow>"
  proof
    fix u v
    assume pcp:"(u, v) \<in> PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
    from ERn_litsim have litsim:"(R\<^sub>\<omega> \<union> (E\<^sub>\<omega>)\<^sup>\<leftrightarrow>) \<doteq> (R n \<union> (E n)\<^sup>\<leftrightarrow>)" using litsim_union litsim_symcl
      unfolding Ew Rw by (metis subsumable_trs.litsim_sym)
    with pcp pcp_litsim have "(u,v) \<in> PCP_ext (R n \<union> (E n)\<^sup>\<leftrightarrow>)" by auto
    with fair have in_Einf:"(u,v) \<in>  (rstep (\<Union>i\<le>n. E i))\<^sup>\<leftrightarrow>" by auto
    {fix k
      have "k \<le> n \<Longrightarrow> (\<Union>i\<le>k. E i) \<doteq> (\<Union>i\<le>k. E' i)" proof(induct k, insert run(2),simp)
        case (Suc k)
        then have k:"k \<le> n" by auto
        have "(\<Union>i\<le>Suc k. E i) = ((\<Union>i\<le>k. E i) \<union> E (Suc k))" by (simp add: atMost_Suc sup.commute)
        with Suc(1)[OF k, THEN litsim_union, of "E (Suc k)" "E' (Suc k)"] run(2)[rule_format, OF Suc(2)]
        show ?case by (simp add: atMost_Suc sup.commute)
      qed
    }
    then have "(\<Union>i\<le>n. E i) \<doteq> (\<Union>i\<le>n. E' i)" by auto
    with in_Einf litsim_rstep_eq have step:"(u,v) \<in> (rstep (\<Union>i\<le>n. E' i))\<^sup>\<leftrightarrow>" by metis
    have "(\<Union>i\<le>n. E' i) = (\<Union>i\<le>n. Ei i)" using Ei_def by auto
    then have "(\<Union>i\<le>n. E' i) \<subseteq> Einf" by auto
    from rstep_mono[OF this] have "rstep (\<Union>i\<le>n. E' i) \<subseteq> rstep Einf" by auto
    with step show "(u,v) \<in> (rstep Einf)\<^sup>\<leftrightarrow>" by blast
qed
  from fair correctness_okb have ground_complete:
    "GCR (rstep Sw) \<and> SN (rstep Sw) \<and> (rstep (E\<^sub>i 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by fastforce
  from ERn_litsim \<open>R\<^sub>\<omega> = R' n\<close> subsumable_trs.litsim_sym have "R\<^sub>\<omega> \<doteq> R n" by auto
  have Eord:"E_ord (\<succ>) (E n) = E_ord (\<succ>) E\<^sub>\<omega>" 
  proof(rule, rule)
    fix l r
    assume "(l,r) \<in> E_ord (\<succ>) (E n)"
    then obtain l' r' \<sigma> where lr:"l = l'\<cdot>\<sigma>" "r = r'\<cdot>\<sigma>" "(l', r') \<in> (E n)\<^sup>\<leftrightarrow>" "l \<succ> r"
      unfolding E_ord_def mem_Collect_eq by auto
    then have "l \<noteq> r"  using irrefl by auto
    from litsim_symcl[OF ERn_litsim(1)] lr(3) obtain \<pi>
      where pi:"(\<pi> \<bullet> l',\<pi> \<bullet> r') \<in> (E' n)\<^sup>\<leftrightarrow>" unfolding litsim_defs rule_pt.permute_prod.simps[symmetric] by meson
    with \<open>l \<noteq> r\<close> have "(\<pi> \<bullet> l',\<pi> \<bullet> r') \<in> (E' n - {(t,t)})\<^sup>\<leftrightarrow>" unfolding lr by fastforce
    note facts = less_set_permute pi irrefl lr
    show "(l,r) \<in> E_ord (\<succ>) E\<^sub>\<omega>" unfolding E_ord_def mem_Collect_eq Ew
      by (rule exI[of _ "\<pi> \<bullet> l'"], rule exI[of _ "\<pi> \<bullet> r'"], rule exI[of _ "sop (-\<pi>) \<circ>\<^sub>s \<sigma>"], insert facts, auto)
  next
    show "E_ord (\<succ>) E\<^sub>\<omega> \<subseteq> E_ord (\<succ>) (E n)" proof
      fix l r
      assume "(l,r) \<in> E_ord (\<succ>) E\<^sub>\<omega>"
      then obtain l' r' \<sigma> where lr:"l = l'\<cdot>\<sigma>" "r = r'\<cdot>\<sigma>" "(l', r') \<in> (E' n)\<^sup>\<leftrightarrow>" "l \<succ> r" 
        unfolding E_ord_def mem_Collect_eq using Ew by auto
    from litsim_symcl[OF ERn_litsim(1)] lr(3) obtain \<pi>
      where pi:"(\<pi> \<bullet> l',\<pi> \<bullet> r') \<in> (E n)\<^sup>\<leftrightarrow>" unfolding litsim_defs rule_pt.permute_prod.simps[symmetric] by metis
    note facts = less_set_permute pi irrefl lr
    show "(l,r) \<in> E_ord (\<succ>) (E n)" unfolding E_ord_def mem_Collect_eq
      by (rule exI[of _ "\<pi> \<bullet> l'"], rule exI[of _ "\<pi> \<bullet> r'"], rule exI[of _ "sop (-\<pi>) \<circ>\<^sub>s \<sigma>"], insert facts, auto)
    qed
  qed
  note facts = this \<open>R\<^sub>\<omega> \<doteq> R n\<close> litsim_union subsumable_trs.litsim_refl
  have Sw_eq:"Sw \<doteq> S\<^sub>\<omega>\<^sup>\<pi>" unfolding Sw_def Eord
    by (rule litsim_union, insert facts, unfold E_ord_def[of "(\<succ>)"], fast+)
  with litsim_rstep_eq have rstep:"rstep Sw = rstep S\<^sub>\<omega>\<^sup>\<pi>" by auto
  from run(2)[rule_format, of 0] litsim_rstep_eq[of "E 0" "E\<^sub>i 0"] have conversion0:"(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E' 0))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding Ei_def by force
  have conversion':"(rstep (R' n \<union> E' n))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
    by (metis Ei_def Un_commute conversion le0 oKBi_conversion_ERw)
  from run(2)[rule_format, of n] litsim_union subsumable_trs.litsim_sym have "R' n \<union> E' n \<doteq> R n \<union> E n" by blast
  with conversion' litsim_rstep_eq have "(rstep (R n \<union> E n))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by metis
  with conversion0 ground_complete have conversion:"(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n \<union> E n))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding Ei_def by auto
  with ground_complete show ?thesis unfolding litsim_rstep_eq[OF Sw_eq] by auto
qed
end

locale homomorphism =
  fixes h\<^sub>F :: "'a \<Rightarrow> 'c"
begin
definition h where "h \<equiv> map_funs_term h\<^sub>F"
definition h\<^sub>R where "h\<^sub>R \<equiv> map_funs_trs h\<^sub>F"
definition h\<^sub>s where "h\<^sub>s \<equiv> map_funs_subst h\<^sub>F"
definition h\<^sub>C where "h\<^sub>C \<equiv> map_funs_ctxt h\<^sub>F"

lemma [simp]: "h = map_funs_term h\<^sub>F" unfolding h_def by auto
lemma [simp]: "h\<^sub>C = map_funs_ctxt h\<^sub>F" unfolding h\<^sub>C_def by auto
lemma [simp]: "h\<^sub>s = map_funs_subst h\<^sub>F" unfolding h\<^sub>s_def by auto
lemma [simp]: "h\<^sub>R = map_funs_trs h\<^sub>F" unfolding h\<^sub>R_def by auto
  
lemma ctxt_apply_imp:"t = C\<langle>u\<rangle> \<Longrightarrow> (h t = (h\<^sub>C C)\<langle>h u\<rangle>)"
using map_funs_term_ctxt_distrib by auto

lemma hR_union [simp]: "h\<^sub>R (R1 \<union> R2) = h\<^sub>R R1 \<union> h\<^sub>R R2"
 by (simp add: map_funs_trs_union)

lemma hR_sym [simp]: "h\<^sub>R (R1\<^sup>\<leftrightarrow>) = (h\<^sub>R R1)\<^sup>\<leftrightarrow>"
  unfolding h\<^sub>R_def hR_union map_funs_trs.simps map_funs_rule.simps image_Un by force
    
lemma subst_apply_h:"h (t \<cdot> \<sigma>) = (h t) \<cdot> (h\<^sub>s \<sigma>)"
  using map_funs_subst_distrib by fastforce
end
  
locale inj_homomorphism = homomorphism "h\<^sub>F"
  for h\<^sub>F :: "'a \<Rightarrow> 'c" +
  assumes injF:"inj h\<^sub>F"
begin
  
lemma inj: "inj h"
proof-
  { fix s t::"('a, 'b) term"
    assume st:"s \<noteq> t"
    then have "h s \<noteq> h t" proof(induct s arbitrary:t)
      case (Var x)
      with term.simps show ?case by (cases t, auto)
    next
      case (Fun f ss)
      note Funs = this
      then show ?case proof(cases t)
        case (Var x)
        then show ?thesis by auto
      next
        case (Fun g ts)
        then show ?thesis proof(cases "f=g")
          case True
          from Funs[unfolded Fun True] have "ss \<noteq> ts" by auto
          then have diff:"(\<exists>i < length ss. ss ! i \<noteq> ts ! i) \<or> (length ss \<noteq> length ts)"
            using nth_equalityI by blast
          then show ?thesis proof(cases "length ss \<noteq> length ts")
            case True
            then show ?thesis unfolding Fun using map_eq_imp_length_eq by auto
          next
            case False
            with diff obtain i where i:"i < length ss \<and> ss ! i \<noteq> ts ! i" by auto
            then have "ss ! i \<in> set ss" by auto
            with Funs(1)[OF this] i have "h (ss ! i) \<noteq> h (ts ! i)" by auto
            with i show ?thesis unfolding Fun using map_nth_conv by fastforce
          qed
        next
          case False
          with Funs injF[unfolded inj_on_def] show ?thesis unfolding Fun by auto
        qed
      qed
        
    qed
  }
  then show ?thesis unfolding inj_on_def by auto
qed
  
definition h_inv ("h\<^sup>-\<^sup>1") where "h\<^sup>-\<^sup>1 \<equiv> map_funs_term (inv h\<^sub>F)"
abbreviation h\<^sub>s_inv ("h\<^sub>s\<^sup>-\<^sup>1") where "h\<^sub>s_inv \<sigma> \<equiv> map_funs_subst (inv h\<^sub>F) \<sigma>"
abbreviation h\<^sub>C_inv ("h\<^sub>C\<^sup>-\<^sup>1") where "h\<^sub>C_inv \<sigma> \<equiv> map_funs_ctxt (inv h\<^sub>F) \<sigma>"
  
lemma ctxt_apply_h:"t = C\<langle>u\<rangle> = (h t = (h\<^sub>C C)\<langle>h u\<rangle>)"
proof
  assume "t = C\<langle>u\<rangle>"
  then show "h t = (h\<^sub>C C)\<langle>h u\<rangle>" using ctxt_apply_imp by auto
next
  assume "h t = (h\<^sub>C C)\<langle>h u\<rangle>"
  then show "t = C\<langle>u\<rangle>" proof(induct C arbitrary:t u)
    case Hole
    with inj[unfolded inj_on_def] show ?case by auto
  next
    case (More f bef C aft)
    note h_t = More(2)[unfolded intp_actxt.simps]
    then obtain g ts where t:"t = Fun g ts" by (cases t, auto)
    from h_t injF[unfolded inj_on_def] have fg:"f = g" unfolding t by fastforce
    from h_t have lists:"map h ts = map h bef @ (h\<^sub>C C)\<langle>h u\<rangle> # map h aft" (is "?L = ?R")
      unfolding t by fastforce
    then have ith:"?L ! (length bef) = ?R ! (length bef)" by auto
    from lists have len:"length bef < length ts" using length_map[of h ts] by auto
    with ith have h_ti:"h (ts ! (length bef)) = (h\<^sub>C C)\<langle>h u\<rangle>" (is "h ?ti = _")
      unfolding nth_map[OF len, of h]
      by (metis length_map nth_append_length)
    with More(1) have ti:"?ti = C\<langle>u\<rangle>" by auto
    from lists[unfolded h_ti[symmetric]] have "map h ts = map h (bef @ (ts ! length bef) # aft)" by auto
    with map_injective[OF _ inj] have "ts = bef @ (?ti # aft)" by blast
    then show ?case using t ti fg by simp
  qed  
qed
  
lemma ctxt_apply_h':"h C\<langle>u\<rangle> = (h\<^sub>C C)\<langle>h u\<rangle>" using ctxt_apply_h by auto
 
lemma inv_h_h: "h\<^sup>-\<^sup>1 (h t) = t"
  unfolding h_def h_inv_def map_funs_term_comp inv_o_cancel[OF injF] by simp

lemma map_funs_subst_compose:
fixes \<sigma>::"('d,'e) subst" and f::"'d \<Rightarrow> 'f"
shows "map_funs_subst f (\<sigma> \<circ>\<^sub>s \<tau>) = (map_funs_subst f \<sigma> \<circ>\<^sub>s (map_funs_subst f \<tau>))"
proof-
  have "\<And>x f \<sigma> \<tau>. map_funs_subst f (\<sigma> \<circ>\<^sub>s \<tau>) x = ((map_funs_subst f \<sigma>) \<circ>\<^sub>s (map_funs_subst f \<tau>)) x"
    unfolding subst_compose_def using subst_apply_h by simp
  then show ?thesis unfolding h\<^sub>s_def by fast
qed

lemma ctxt_image:
  assumes "h t = C\<^sub>h\<langle>u\<^sub>h\<rangle>"
  shows "C\<^sub>h = h\<^sub>C (h\<^sub>C_inv C\<^sub>h) \<and> u\<^sub>h = h (h\<^sup>-\<^sup>1 u\<^sub>h)"
proof-
  from assms have "h\<^sup>-\<^sup>1 (h t) = (h\<^sub>C\<^sup>-\<^sup>1 C\<^sub>h)\<langle>h\<^sup>-\<^sup>1 u\<^sub>h\<rangle>" unfolding h_inv_def by simp
  from this[unfolded inv_h_h] have "t = (h\<^sub>C\<^sup>-\<^sup>1 C\<^sub>h)\<langle>h\<^sup>-\<^sup>1 u\<^sub>h\<rangle>" by auto
  then have "h t = (h\<^sub>C (h\<^sub>C\<^sup>-\<^sup>1 C\<^sub>h))\<langle>h (h\<^sup>-\<^sup>1 u\<^sub>h)\<rangle>" by auto
  with assms have eq:"C\<^sub>h\<langle>u\<^sub>h\<rangle> = (h\<^sub>C (h\<^sub>C\<^sup>-\<^sup>1 C\<^sub>h))\<langle>h (h\<^sup>-\<^sup>1 u\<^sub>h)\<rangle>" by auto
  then have "h\<^sub>C (h\<^sub>C\<^sup>-\<^sup>1 C\<^sub>h) = C\<^sub>h" by (induct C\<^sub>h, auto)
  with eq[unfolded this ctxt_eq] show ?thesis by argo
qed
  
lemma subst_image:
  fixes t::"('a, 'b) term"
  assumes "h t = (h u) \<cdot> \<sigma>\<^sub>h"
  shows "\<forall>x \<in> vars_term (h u). \<sigma>\<^sub>h x = h (h\<^sub>s\<^sup>-\<^sup>1 \<sigma>\<^sub>h x)"
proof -
  from map_funs_subst_distrib[of "inv h\<^sub>F" "h u" \<sigma>\<^sub>h] have t:"t = u \<cdot> (h\<^sub>s\<^sup>-\<^sup>1 \<sigma>\<^sub>h)"
    using map_funs_term_ident unfolding assms[symmetric] h_inv_def[symmetric] inv_h_h by auto
  from assms have "(h u) \<cdot> \<sigma>\<^sub>h = (h u) \<cdot> h\<^sub>s (h\<^sub>s\<^sup>-\<^sup>1 \<sigma>\<^sub>h)" unfolding t subst_apply_h by auto
  then show ?thesis unfolding term_subst_eq_conv by auto
qed
  
lemma rule_h:"(s,t) \<in> RR = ((h s, h t) \<in> (h\<^sub>R RR))"
  unfolding h\<^sub>R_def map_funs_trs.simps map_funs_rule.simps
  by (smt h_def image_iff inv_h_h prod.collapse snd_conv swap_simp)

lemma rstep_h:"(s,t) \<in> rstep RR = ((h s, h t) \<in> rstep (h\<^sub>R RR))"
proof
  assume rstep:"(s,t) \<in> rstep RR"
  then obtain C \<sigma> l r where lr:"(l, r) \<in> RR" and sC:"s = C\<langle>l \<cdot> \<sigma>\<rangle>" and tC:"t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from sC tC ctxt_apply_h have C:"h s = (h\<^sub>C C)\<langle>h (l \<cdot> \<sigma>)\<rangle>" "h t = (h\<^sub>C C)\<langle>h (r \<cdot> \<sigma>)\<rangle>" by auto
  from subst_apply_h have sub:"h (l \<cdot> \<sigma>) = h l \<cdot> (h\<^sub>s \<sigma>)" "h (r \<cdot> \<sigma>) = h r \<cdot> (h\<^sub>s \<sigma>)" by auto
  with lr[unfolded rule_h] C show "(h s, h t) \<in> rstep (h\<^sub>R RR)" by auto
next
  assume "(h s, h t) \<in> rstep (h\<^sub>R RR)"
  then obtain Ch \<sigma>h lh rh where lr:"(lh, rh) \<in> h\<^sub>R RR" and sC:"h s = Ch\<langle>lh \<cdot> \<sigma>h\<rangle>" and tC:"h t = Ch\<langle>rh \<cdot> \<sigma>h\<rangle>" by auto
  from lr obtain l r where lr:"(l, r) \<in> RR" "lh = h l" "rh = h r"
    unfolding h\<^sub>R_def map_funs_trs.simps map_funs_rule.simps by force
  with sC[THEN ctxt_image] obtain C u where C:"Ch = h\<^sub>C C" and lu:"h u = h l \<cdot> \<sigma>h" by metis
  from lr tC[THEN ctxt_image] obtain v where rv:"h v = h r \<cdot> \<sigma>h" by metis
  from lu[unfolded lr, THEN subst_image] rv[THEN subst_image] obtain \<sigma> where
    "\<forall>x \<in> vars_term (h l) \<union> vars_term (h r). (\<sigma>h x = h\<^sub>s \<sigma> x)" by force
  then have \<sigma>:"(h l) \<cdot> \<sigma>h = (h l) \<cdot> (h\<^sub>s \<sigma>)" "(h r) \<cdot> \<sigma>h = (h r) \<cdot> (h\<^sub>s \<sigma>)" using term_subst_eq_conv by (fast,fast)
  from sC[unfolded C lr] have s:"s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    unfolding \<sigma> subst_apply_h[symmetric] ctxt_apply_h[symmetric] by fast
  from tC[unfolded C lr] have t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    unfolding \<sigma> subst_apply_h[symmetric] ctxt_apply_h[symmetric] by fast
  with s lr(1) show "(s,t) \<in> rstep RR" by auto
qed

lemma subterm_h: "s \<unrhd> t = (h s \<unrhd> h t)"
proof
  assume "s \<unrhd> t"
  with ctxt_apply_h show "h s \<unrhd> h t" by fast
next
  assume "h s \<unrhd> h t"
  then obtain C\<^sub>h where ht:"h s = C\<^sub>h\<langle>h t\<rangle>" by auto
  from ctxt_image[OF this] obtain C u where C:"C\<^sub>h = h\<^sub>C C" and u:"h u = h s" by force
  from ht[unfolded C ctxt_apply_h[symmetric]] show "s \<unrhd> t" by auto
qed
  
lemma subterm_strict_h: "s \<rhd> t = (h s \<rhd> h t)"
  using subterm_h supt_supteq_set_conv by auto

lemma enc_h: "s \<unlhd>\<cdot> t = (h s \<unlhd>\<cdot> h t)"
proof
  assume "s \<unlhd>\<cdot> t"
  with encompeq_termE obtain C \<sigma> where "t = C\<langle>s \<cdot> \<sigma>\<rangle>" by auto
  with ctxt_apply_h have C:"h t = (h\<^sub>C C)\<langle>h (s \<cdot> \<sigma>)\<rangle>" by auto
  from subst_apply_h have "h (s \<cdot> \<sigma>) = h s \<cdot> (h\<^sub>s \<sigma>)" by auto
  with C show "h s \<unlhd>\<cdot> h t" unfolding encompeq.simps by force
next
  assume "h s \<unlhd>\<cdot> h t"
  with encompeq_termE obtain C\<^sub>h \<sigma>\<^sub>h where ht:"h t = C\<^sub>h\<langle>h s \<cdot> \<sigma>\<^sub>h\<rangle>" by auto
  from ctxt_image[OF this] obtain C u where C:"C\<^sub>h = h\<^sub>C C" and u:"h u = h s \<cdot> \<sigma>\<^sub>h" by metis
  with subst_image[OF u] have \<sigma>:"\<forall>x \<in> vars_term (h s). (\<sigma>\<^sub>h x = h\<^sub>s (h\<^sub>s\<^sup>-\<^sup>1 \<sigma>\<^sub>h) x)" by auto
  then have \<sigma>:"(h s) \<cdot> \<sigma>\<^sub>h = (h s) \<cdot> (h\<^sub>s (h\<^sub>s\<^sup>-\<^sup>1 \<sigma>\<^sub>h))" using term_subst_eq_conv by blast
  from ht[unfolded C] show "s \<unlhd>\<cdot> t"
    unfolding \<sigma> subst_apply_h[symmetric] ctxt_apply_h[symmetric] by fast
qed
  
lemma inv_hR_rule[simp]:
  assumes "(hl,hr) \<in> h\<^sub>R R"
  shows "(h\<^sup>-\<^sup>1 hl, h\<^sup>-\<^sup>1 hr) \<in> R \<and> h (h\<^sup>-\<^sup>1 hl) = hl \<and> h (h\<^sup>-\<^sup>1 hr) = hr"
proof-
  note hlr = assms[unfolded h\<^sub>R_def map_funs_trs.simps map_funs_rule.simps]
  from imageE[OF hlr, unfolded prod.inject] obtain l r where "(l, r) \<in> R" and hlr:"hl = h l" "hr = h r"
    unfolding h_def by (metis prod.collapse)
  then show ?thesis unfolding hlr inv_h_h by auto
qed
end
  
locale gtotal_okb_irun_h = gtotal_okb_irun_inf R E less + inj_homomorphism "h\<^sub>F"
  for R :: "nat \<Rightarrow> (('a, 'b::infinite) term \<times> ('a, 'b) term) set" 
  and E :: "nat \<Rightarrow> (('a, 'b) term \<times> ('a, 'b) term) set" 
  and less :: "('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
  and h\<^sub>F :: "'a \<Rightarrow> 'c" +
  fixes less_h :: "('c, 'b) term \<Rightarrow> ('c, 'b) term \<Rightarrow> bool" (infix "\<succ>\<^sub>h" 50)
  assumes SN_less_h: "SN {(x, y). x \<succ>\<^sub>h y}"
    and ctxt_h: "s \<succ>\<^sub>h t \<Longrightarrow> C\<langle>s\<rangle> \<succ>\<^sub>h C\<langle>t\<rangle>"
    and subst_h: "s \<succ>\<^sub>h t \<Longrightarrow> s \<cdot> \<sigma> \<succ>\<^sub>h t \<cdot> \<sigma>"
    and trans_h: "s \<succ>\<^sub>h t \<Longrightarrow> t \<succ>\<^sub>h u \<Longrightarrow> s \<succ>\<^sub>h u"
    and gtotal_h: "ground s \<and> ground t \<longrightarrow> s = t \<or> s \<succ>\<^sub>h t \<or> t \<succ>\<^sub>h s"
    and compat_h:"s' \<succ> t' \<Longrightarrow> (h s') \<succ>\<^sub>h (h t')"
begin
  
abbreviation less_sk_set ("{\<succ>\<^sub>h}") where "{\<succ>\<^sub>h} \<equiv> {(x, y). x \<succ>\<^sub>h y}"

abbreviation E\<^sub>h where "E\<^sub>h i \<equiv> h\<^sub>R (E i)"
abbreviation R\<^sub>h where "R\<^sub>h i \<equiv> h\<^sub>R (R i)"
abbreviation oKBi_h (infix "\<turnstile>\<^sub>h" 55)
  where "oKBi_h ER ER' \<equiv> ordered_completion.oKBi less_h ER ER'"
    
sublocale okb_h: ordered_completion less_h
  by (unfold_locales, insert SN_less_h ctxt_h subst_h trans_h gtotal_h, blast+)
  
lemma ordstep_h:
  assumes "(s,t) \<in> ordstep {\<succ>} EE"
  shows "(h s, h t) \<in> ordstep {\<succ>\<^sub>h} (h\<^sub>R EE)"
proof-
  from assms obtain C l r \<sigma> where lr:"(l, r) \<in> EE" and sC:"s = C\<langle>l \<cdot> \<sigma>\<rangle>" and tC:"t = C\<langle>r \<cdot> \<sigma>\<rangle>" and
    less:"l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" unfolding ordstep.simps by blast
  then have rule:"(h l, h r) \<in> h\<^sub>R EE" unfolding h\<^sub>R_def map_funs_trs.simps by force
  from sC tC ctxt_apply_h have C:"h s = (h\<^sub>C C)\<langle>h (l \<cdot> \<sigma>)\<rangle>" "h t = (h\<^sub>C C)\<langle>h (r \<cdot> \<sigma>)\<rangle>" by auto
  from subst_apply_h have sub:"h (l \<cdot> \<sigma>) = h l \<cdot> (h\<^sub>s \<sigma>)" "h (r \<cdot> \<sigma>) = h r \<cdot> (h\<^sub>s \<sigma>)" by auto
  with rule C compat_h[OF less] show "(h s, h t) \<in> ordstep {\<succ>\<^sub>h} (h\<^sub>R EE)"
    unfolding ordstep.simps by auto
qed
    
lemma ostep_h:
  assumes "(s,t) \<in> ostep EE RR"
  shows "(h s, h t) \<in> okb_h.ostep (h\<^sub>R (EE)) (h\<^sub>R RR)"
  using assms rstep_h[of s t RR] ordstep_h[of s t "EE\<^sup>\<leftrightarrow>"]
  unfolding ostep_def okb_h.ostep_def hR_sym by fast

lemma encstep2_h:
  assumes "(s,t) \<in> encstep2 EE RR"
  shows "(h s, h t) \<in> okb_h.encstep2 (h\<^sub>R EE) (h\<^sub>R RR)"
using assms proof(cases)
  case (estep l r C \<sigma>)
  then have rule:"(h l, h r) \<in> (h\<^sub>R EE)\<^sup>\<leftrightarrow>" unfolding h\<^sub>R_def map_funs_trs.simps by force
  from estep ctxt_apply_h have C:"h s = (h\<^sub>C C)\<langle>h (l \<cdot> \<sigma>)\<rangle>" "h t = (h\<^sub>C C)\<langle>h (r \<cdot> \<sigma>)\<rangle>" by auto
  from subst_apply_h have sub:"h (l \<cdot> \<sigma>) = h l \<cdot> (h\<^sub>s \<sigma>)" "h (r \<cdot> \<sigma>) = h r \<cdot> (h\<^sub>s \<sigma>)" by auto
  from enc_h estep(5) have "h l \<lhd>\<cdot> h s" unfolding encomp_def by auto
  with okb_h.encstep2.estep rule sub rule C compat_h[OF estep(4)] show ?thesis by auto
next
  case (rstep l r C \<sigma>)
  then have rule:"(h l, h r) \<in> h\<^sub>R RR" unfolding h\<^sub>R_def map_funs_trs.simps by force
  from rstep ctxt_apply_h have C:"h s = (h\<^sub>C C)\<langle>h (l \<cdot> \<sigma>)\<rangle>" "h t = (h\<^sub>C C)\<langle>h (r \<cdot> \<sigma>)\<rangle>" by auto
  from subst_apply_h have sub:"h (l \<cdot> \<sigma>) = h l \<cdot> (h\<^sub>s \<sigma>)" "h (r \<cdot> \<sigma>) = h r \<cdot> (h\<^sub>s \<sigma>)" by auto
  from enc_h rstep(4) have "h l \<lhd>\<cdot> h s" unfolding encomp_def by auto
  with okb_h.encstep2.rstep rule sub rule C show ?thesis by auto
qed

lemma enc_hstep1:
  assumes "(s,t) \<in> encstep1 EE RR"
  shows "(h s, h t) \<in> okb_h.encstep1 (h\<^sub>R EE) (h\<^sub>R RR)"
using assms proof(cases)
  case (estep l r C \<sigma>)
  then have rule:"(h l, h r) \<in> (h\<^sub>R EE)\<^sup>\<leftrightarrow>" unfolding h\<^sub>R_def map_funs_trs.simps by force
  from estep ctxt_apply_h have C:"h s = (h\<^sub>C C)\<langle>h (l \<cdot> \<sigma>)\<rangle>" "h t = (h\<^sub>C C)\<langle>h (r \<cdot> \<sigma>)\<rangle>" by auto
  from subst_apply_h have sub:"h (l \<cdot> \<sigma>) = h l \<cdot> (h\<^sub>s \<sigma>)" "h (r \<cdot> \<sigma>) = h r \<cdot> (h\<^sub>s \<sigma>)" by auto
  from enc_h estep(5) have "h l \<lhd>\<cdot> h s" unfolding encomp_def by auto
  with okb_h.encstep1.estep rule sub rule C compat_h[OF estep(4)] show ?thesis by auto
next
  case rstep
  from this[unfolded rstep_h] okb_h.encstep1.rstep show ?thesis by simp
qed

lemma oKBi_h: "(E\<^sub>h i, R\<^sub>h i) \<turnstile>\<^sub>h (E\<^sub>h (Suc i), R\<^sub>h (Suc i))"
proof-
  from hR_union hR_sym have s1 [simp]:"rstep (R\<^sub>h i \<union> (E\<^sub>h i)\<^sup>\<leftrightarrow>) = rstep (h\<^sub>R(R i \<union> (E i)\<^sup>\<leftrightarrow>))" by metis
  let ?h_rule = "\<lambda>(s,t).(h s, h t)"
  have h_rule:"\<And>A. h\<^sub>R A = ?h_rule ` A" unfolding h\<^sub>R_def map_funs_trs.simps by force
  from inj have inj':"inj ?h_rule" unfolding inj_on_def by (simp add: inj_on_def, auto)
  have hR_diff [simp]:"\<And>A B. h\<^sub>R (A - B) = h\<^sub>R A - h\<^sub>R B"
    using image_set_diff[OF inj'] unfolding h_rule by metis
  have h_rule [simp]:"\<And>s t. h\<^sub>R {(s,t)} = {(h s, h t)}" unfolding h\<^sub>R_def map_funs_trs.simps by force
  have h_lift [simp]:"\<And>s t S. (s, t) \<in> S \<Longrightarrow> (h s, h t) \<in> h\<^sub>R S" unfolding h\<^sub>R_def map_funs_trs.simps by force
  from irun[of i] show ?thesis proof(cases)
    case (deduce s t u)
    with rstep_h s1 have st:"(h s, h t) \<in> rstep (R\<^sub>h i \<union> (E\<^sub>h i)\<^sup>\<leftrightarrow>)" by blast
    from deduce rstep_h s1 have su:"(h s, h u) \<in> rstep (R\<^sub>h i \<union> (E\<^sub>h i)\<^sup>\<leftrightarrow>)" by blast
    from deduce(1) have "E\<^sub>h (Suc i) = E\<^sub>h i \<union> {(h t, h u)}" unfolding h\<^sub>R_def map_funs_trs.simps by force
    with okb_h.oKBi.deduce[OF st su] deduce(2) show ?thesis by simp
  next
    case (orientl s t)
    with compat_h have st:"h s \<succ>\<^sub>h h t" by auto
    from orientl(4) have st':"(h s, h t) \<in> E\<^sub>h i" using h_lift by force
    have E:"E\<^sub>h (Suc i) = E\<^sub>h i - {(h s, h t)}" unfolding orientl(1) hR_diff h_rule by auto
    have "R\<^sub>h (Suc i) = R\<^sub>h i \<union> {(h s, h t)}" unfolding orientl(2) hR_union h_rule by auto
    with okb_h.oKBi.orientl[OF st st'] E show ?thesis by auto
  next
    case (orientr t s)
    with compat_h have st:"h t \<succ>\<^sub>h h s" by auto
    from orientr(4) have st':"(h s, h t) \<in> E\<^sub>h i" using h_lift by force
    have E:"E\<^sub>h (Suc i) = E\<^sub>h i - {(h s, h t)}" unfolding orientr(1) hR_diff h_rule by auto
    have "R\<^sub>h (Suc i) = R\<^sub>h i \<union> {(h t, h s)}" unfolding orientr(2) hR_union h_rule by auto
    with okb_h.oKBi.orientr[OF st st'] E show ?thesis by auto
  next
    case (delete s)
    have E:"E\<^sub>h (Suc i) = E\<^sub>h i - {(h s, h s)}" unfolding delete(1) hR_diff h_rule by force
    from delete(3) h_lift have "(h s, h s) \<in> E\<^sub>h i" by force
    from okb_h.oKBi.delete[OF this] E delete(2) show ?thesis by auto
  next
    case (compose t u s)
    have R:"R\<^sub>h (Suc i) = R\<^sub>h i - {(h s, h t)} \<union> {(h s, h u)}"
      unfolding compose(2) hR_union hR_diff h_rule by simp
    from compose(3)[THEN ostep_h] h_rule
    have ostep:"(h t, h u) \<in> okb_h.ostep (E\<^sub>h i) (R\<^sub>h i - {(h s, h t)})"
      unfolding hR_diff h_rule by simp
    from okb_h.oKBi.compose[OF ostep h_lift[OF compose(4)]] R compose(1) show ?thesis by auto
  next
    case (simplifyl s u t)
    have E:"E\<^sub>h (Suc i) = E\<^sub>h i - {(h s, h t)} \<union> {(h u, h t)}"
      unfolding simplifyl(1) hR_union hR_diff h_rule by force
    from simplifyl(3)[THEN enc_hstep1]
      have "(h s, h u) \<in> okb_h.encstep1 (E\<^sub>h i - {(h s, h t)}) (R\<^sub>h i)" unfolding hR_diff h_rule by auto
    from okb_h.oKBi.simplifyl[OF this h_lift[OF simplifyl(4)]] E simplifyl(2) show ?thesis by argo
  next
    case (simplifyr t u s)
    have E:"E\<^sub>h (Suc i) = E\<^sub>h i - {(h s, h t)} \<union> {(h s, h u)}"
      unfolding simplifyr(1) hR_union hR_diff h_rule by force
    from simplifyr(3)[THEN enc_hstep1]
      have "(h t, h u) \<in> okb_h.encstep1 (E\<^sub>h i - {(h s, h t)}) (R\<^sub>h i)" unfolding hR_diff h_rule by auto
    from okb_h.oKBi.simplifyr[OF this h_lift[OF simplifyr(4)]] E simplifyr(2) show ?thesis by argo
  next
    case (collapse t u s)
    have E:"E\<^sub>h (Suc i) = E\<^sub>h i \<union> {(h u, h s)}" unfolding collapse(1) hR_union h_rule by force
    from h\<^sub>R_def have R:"R\<^sub>h (Suc i) = R\<^sub>h i - {(h t, h s)}" unfolding collapse(2) hR_diff h_rule by force
    from collapse(3)[THEN encstep2_h]
      have "(h t, h u) \<in> okb_h.encstep2 (E\<^sub>h i) (R\<^sub>h i - {(h t, h s)})" unfolding hR_diff h_rule by auto
    from okb_h.collapse[OF this h_lift[OF collapse(4)]] R E show ?thesis by auto
  qed
qed
  
sublocale irun_h: gtotal_okb_irun_inf R\<^sub>h E\<^sub>h less_h
proof(unfold_locales, unfold fground_UNIV)
  show "\<And>s t. ground s \<Longrightarrow> ground t \<Longrightarrow> s = t \<or> s \<succ>\<^sub>h t \<or> t \<succ>\<^sub>h s" using gtotal_h by auto
next
  show "\<And>i. okb_h.oKBi (E\<^sub>h i, R\<^sub>h i) (E\<^sub>h (Suc i), R\<^sub>h (Suc i))" using oKBi_h by auto
qed(auto simp:R0 map_funs_trs.simps)
    
lemma hEinf [simp]:"h\<^sub>R E\<^sub>\<infinity> = irun_h.Einf" unfolding h\<^sub>R_def
    by (smt SUP_cong image_UN map_funs_trs.simps)
    
lemma hRinf [simp]:"h\<^sub>R R\<^sub>\<infinity> = irun_h.Rinf" unfolding h\<^sub>R_def
    by (smt SUP_cong image_UN map_funs_trs.simps)

lemma hEw [simp]:"h\<^sub>R E\<^sub>\<omega> = irun_h.E\<^sub>\<omega>"
proof-
  have eq:"h\<^sub>R E\<^sub>\<omega> = (map_funs_rule h\<^sub>F) ` E\<^sub>\<omega>" unfolding h\<^sub>R_def map_funs_trs.simps by force
  from inj have inj_rule:"inj (map_funs_rule h\<^sub>F)" unfolding h_def map_funs_rule.simps inj_on_def by auto
  { fix j ::nat
    let ?C = "Collect ((\<le>) j)"
    have univ:"\<forall>x\<in>Collect ((\<le>) j). E x \<subseteq> UNIV" using subset_UNIV by blast
    from le0 have "0 \<in> {i. i \<le> j}" by simp
    with image_INT[OF inj_rule univ] have "map_funs_rule h\<^sub>F ` (\<Inter> (E ` ?C)) = (\<Inter>x\<in>?C. map_funs_rule h\<^sub>F ` E x)" by auto
  }
  with eq have "h\<^sub>R E\<^sub>\<omega> = (\<Union>i. \<Inter>j\<in>Collect ((\<le>) i). map_funs_rule h\<^sub>F ` E j)"
    unfolding E\<^sub>\<omega>_def image_UN by presburger
  then show ?thesis unfolding irun_h.E\<^sub>\<omega>_def unfolding h\<^sub>R_def map_funs_trs.simps by simp
qed

lemma hRw [simp]:"h\<^sub>R R\<^sub>\<omega> = irun_h.R\<^sub>\<omega>"
proof-
  have eq:"h\<^sub>R R\<^sub>\<omega> = (map_funs_rule h\<^sub>F) ` R\<^sub>\<omega>" unfolding h\<^sub>R_def map_funs_trs.simps by force
  from inj have inj_rule:"inj (map_funs_rule h\<^sub>F)" unfolding h_def map_funs_rule.simps inj_on_def by auto
  { fix j ::nat
    let ?C = "Collect ((\<le>) j)"
    have univ:"\<forall>x\<in>Collect ((\<le>) j). R x \<subseteq> UNIV" using subset_UNIV by blast
    from le0 have "0 \<in> {i. i \<le> j}" by simp
    with image_INT[OF inj_rule univ] have "map_funs_rule h\<^sub>F ` (\<Inter> (R ` ?C)) = (\<Inter>x\<in>?C. map_funs_rule h\<^sub>F ` R x)" by auto
  }
  with eq have "h\<^sub>R R\<^sub>\<omega> = (\<Union>i. \<Inter>j\<in>Collect ((\<le>) i). map_funs_rule h\<^sub>F ` R j)"
    unfolding R\<^sub>\<omega>_def image_UN by presburger
  then show ?thesis unfolding irun_h.R\<^sub>\<omega>_def unfolding h\<^sub>R_def map_funs_trs.simps by simp
qed

lemma perm_h:"p \<bullet> (h t) = h (p \<bullet> t)"
  by (induct t, unfold h_def, auto)

lemma perm_inv_h:"p \<bullet> (h\<^sup>-\<^sup>1 t) = h\<^sup>-\<^sup>1 (p \<bullet> t)"
  by (induct t, unfold h_inv_def, auto)
  
lemma poss_inv_h:"poss (h\<^sup>-\<^sup>1 t) = poss t" unfolding h_inv_def
  by (induct t, unfold term.map, auto)
      
lemma fun_poss_inv_h:"fun_poss (h\<^sup>-\<^sup>1 t) = fun_poss t" unfolding h_inv_def
  by (induct t, unfold term.map, auto)
    
lemma pos_term_h:"p \<in> poss t \<Longrightarrow> (h t |_ p) = h (t |_ p)" unfolding h_def
proof (induct t arbitrary:p)
  case (Var x)
  then have p:"p = []" by auto
  then show ?case unfolding p term.map subt_at.simps by auto
next
  case (Fun f ts)
  show ?case proof(cases p)
    case Nil
    show ?thesis unfolding Nil term.map subt_at.simps by auto
  next
    case (Cons i ps)
    from Fun(2) have "i < length ts" "ps \<in> poss (ts ! i)" unfolding Cons poss.simps by auto
    with Fun(1)[OF _ this(2)]  show ?thesis unfolding Cons using subt_at.simps by auto
  qed
qed

lemma unify_h:
  fixes es::"(('d, 'e) term \<times> ('d, 'e) term) list" and f::"'d \<Rightarrow> 'f"
  assumes "unify es bs = Some cs"
  defines "fh \<equiv> map_funs_term f"
  shows "unify (map (\<lambda>(u,v).(fh u, fh v)) es) (map (\<lambda>(x,t).(x, fh t)) bs) = Some (map (\<lambda>(x,t).(x, fh t)) cs)"
proof-
  let ?he = "(\<lambda>(u,v).(fh u, fh v))"
  let ?mhe = "map ?he"
  let ?hb = "(\<lambda>(x,t).(x, fh t))"
  let ?mhb = "map ?hb"
  { fix s t::"('d, 'e) term"
    fix us::"(('d, 'e) term \<times> ('d, 'e) term) list"
    assume "decompose s t = Some us"
    then have "decompose (fh s) (fh t) = Some (map ?he us)" proof(induct s arbitrary:t)
      case (Var x)
      then show ?case unfolding decompose_def h_def term.map by simp
    next
      case (Fun f ss)
      from Fun(2)[unfolded decompose_def] obtain g ts where t:"t = Fun g ts" by (cases t, auto)
      from Fun(2)[unfolded decompose_def t, simplified] option.simps(3) have fg:"f = g" by metis
      from Fun(2)[unfolded decompose_def t] have d:"decompose (Fun f ss) t = zip_option ss ts"
        unfolding t fg decompose_def h_def term.map by simp
      from Fun(2)[unfolded this] zip_option_zip_conv have
        l:"length ts = length ss" "length us = length ss" "us = zip ss ts" by auto
      from this(3) zip_map_map have z:"zip (map fh ss) (map fh ts) = map ?he us" by auto
      have zo:"zip_option (map fh ss) (map fh ts) = Some (map ?he us)"
        by (rule zip_option_intros(1), unfold length_map, insert l z, auto)
      have "decompose (fh (Fun f ss)) (fh t) = zip_option (map fh ss) (map fh ts)"
        unfolding t fg decompose_def fh_def term.map by simp
      with zo show ?case by auto
    qed
  } note dec = this
  {fix x::"'e" and t E
    { fix u v
      have "map_funs_subst f (Var(x := t)) = Var(x := fh t)" unfolding fh_def by auto
      then have "\<And>u. fh (u \<cdot> Var(x := t)) = (fh u) \<cdot> Var(x := fh t)"
        unfolding fh_def map_funs_subst_distrib by auto
      then have "(fh (u \<cdot> Var(x := t)), fh (v \<cdot> Var(x := t))) = ((fh u) \<cdot> Var(x := fh t), fh v \<cdot> Var(x := fh t))"
        by auto
    }
    then have "?mhe (subst_list (subst x t) E) = subst_list (subst x (fh t)) (?mhe E)"
      unfolding subst_list_def map_map subst_def o_def split by auto
  } note subst_list = this
show ?thesis using assms(1)
proof (induction es bs arbitrary: cs rule: unify.induct)
  case (1 bs)
  then show ?case by force
next
  case (2 f ss g ts E bs)
  then obtain us where d: "decompose (Fun f ss) (Fun g ts) = Some us"
    and [simp]: "f = g" "length ss = length ts" "us = zip ss ts"
    and u:"unify (us @ E) bs = Some cs" by (auto split: option.splits)
  from dec[OF this(1)] have
   "unify (?mhe ((Fun f ss, Fun g ts) # E)) (?mhb bs) = unify ((?mhe us) @ (?mhe E)) (?mhb bs)"
    unfolding list.map split fh_def term.map unify.simps unfolding fh_def[symmetric] by auto
  with 2(1)[OF d u] show ?case by auto
next
  case (3 x t E bs)
  show ?case
  proof (cases "t = Var x")
    assume t:"t = Var x"
    with 3(3) have u1:"unify E bs = Some cs" by simp
    have u2:"unify (?mhe ((Var x, t) # E)) (?mhb bs) = unify (?mhe E) (?mhb bs)"
      unfolding list.map split fh_def term.map t unify.simps by simp
    with 3(1)[OF t u1] show ?case by argo
  next
    assume t:"t \<noteq> Var x"
    let ?sub = "subst_list (subst x t) E"
    let ?sub' = "subst_list (subst x (fh t)) (?mhe E)"
    from t 3(3) have xt:"x \<notin> vars_term t" unfolding unify.simps by auto
    with 3(3) t have "unify (subst_list (subst x t) E) ((x, t) # bs) = Some cs" by auto
    with 3(2)[OF t xt] have u1:"unify (?mhe ?sub) ((x, fh t) # (?mhb bs)) = Some (?mhb cs)" by auto
    from t have ht:"fh t \<noteq> Var x" unfolding fh_def by (cases t, auto)
    with xt have u2:"unify (?mhe ((Var x, t) # E)) (?mhb bs) = unify ?sub' ((x, fh t) # (?mhb bs))"
      unfolding list.map split fh_def term.map unify.simps vars_term_map_funs_term2 by auto
    with u1 show ?case unfolding list.map subst_list[symmetric] split by argo
  qed
next
  case (4 f ss x E bs)
    let ?t = "Fun f ss"
    let ?sub = "subst_list (subst x ?t) E"
    let ?sub' = "subst_list (subst x (fh ?t)) (?mhe E)"
    from 4(2) have xt:"x \<notin> vars_term ?t" unfolding unify.simps by force
    with 4(2) have "unify (subst_list (subst x ?t) E) ((x, ?t) # bs) = Some cs" by auto
    with 4(1)[OF xt] have u1:"unify (?mhe ?sub) ((x, fh ?t) # (?mhb bs)) = Some (?mhb cs)" by auto
    have ht:"fh ?t \<noteq> Var x" unfolding fh_def by auto
    with xt have u2:"unify (?mhe ((?t, Var x) # E)) (?mhb bs) = unify ?sub' ((x, fh ?t) # (?mhb bs))"
      unfolding list.map split fh_def term.map unify.simps vars_term_map_funs_term2 by auto
    with u1 show ?case unfolding list.map subst_list[symmetric] split by argo
  qed
qed
  
lemma mgu_h:
  fixes s::"('a, 'b) term"
  assumes "mgu (h s) (h t) = Some \<mu>"
  shows "mgu s t = Some ((h\<^sub>s_inv \<mu>)) \<and> h\<^sub>s (h\<^sub>s_inv \<mu>) = \<mu>"
proof-
  let ?bmap = "map (\<lambda>(x,t). (x, h\<^sup>-\<^sup>1 t))"
  let ?bmap' = "map (\<lambda>(x,t). (x, h t))"
  from assms[unfolded mgu_def] obtain bs where
    uh:"unify [(h s, h t)] [] = Some bs" and mu:"\<mu> = subst_of bs" by (cases "unify [(h s, h t)] []", auto)
  from unify_h[OF this(1), of "inv h\<^sub>F"] have u:"unify [(s, t)] [] = Some (?bmap bs)"
    unfolding list.map split h_def map_funs_term_comp o_def inv_f_f[OF injF] term.map_ident h_inv_def
    by auto
  from unify_h[OF this, of h\<^sub>F] uh have bs:"bs = ?bmap' (?bmap bs)"
    unfolding list.map split h_def[symmetric] by auto
  have x:"\<And> x f t. subst x (map_funs_term f t) = map_funs_subst f (subst x t)" unfolding subst_def by auto
  { fix bs::"('e \<times> ('d, 'e) term) list"
    fix f::"'d \<Rightarrow> 'f"
    have "subst_of (map (\<lambda>(x, t). (x, map_funs_term f t)) bs) = map_funs_subst f (subst_of bs)"
    proof-
      let ?m = "\<lambda>(x, t). (x, map_funs_term f t)"
      show ?thesis proof(induct bs, simp)
        case (Cons xt bs)
        then obtain x t where xt:"xt = (x,t)" by fastforce
        have "subst_of (map ?m (xt # bs)) = subst_of (map ?m bs) \<circ>\<^sub>s (subst x (map_funs_term f t))"
          unfolding xt list.map split by auto
        also from Cons x[of x f] have "\<dots> = (map_funs_subst f (subst_of bs)) \<circ>\<^sub>s (map_funs_subst f (subst x t))" by simp
        also from map_funs_subst_compose[of f] have "\<dots> = map_funs_subst f (subst_of bs \<circ>\<^sub>s (subst x t))" by metis
        finally show ?case unfolding xt by auto
      qed
    qed
  }
  then have "subst_of (map (\<lambda>(x, t). (x, h\<^sup>-\<^sup>1 t)) bs) = h\<^sub>s\<^sup>-\<^sup>1 (subst_of bs)"
    unfolding h_inv_def by auto
  then have mgu:"mgu s t = Some ((h\<^sub>s_inv \<mu>))" unfolding mgu_def u mu by simp
  { fix y
    from bs have "map_funs_subst h\<^sub>F (map_funs_subst (inv h\<^sub>F) (subst_of bs)) y = (subst_of bs) y" (is "?l y = ?r y")
    proof(induct bs, simp)
      case (Cons xt bs)
      then obtain x t where xt:"xt = (x,t)" by fastforce
      let ?h = "map_funs_subst h\<^sub>F"
      let ?hi = "map_funs_subst (inv h\<^sub>F)"
      let ?xt = "subst x t"
      from Cons(2)[unfolded xt list.map split] have t:"h (h\<^sup>-\<^sup>1 t) = t" by auto
      have "?h (?hi (subst_of (xt # bs))) y = ?h (?hi (subst_of bs \<circ>\<^sub>s ?xt)) y" (is "?t = _ ")
        unfolding xt by auto
      with map_funs_subst_compose[of "inv h\<^sub>F"] have "?t = ?h (?hi (subst_of bs) \<circ>\<^sub>s (?hi ?xt)) y" by metis
      with map_funs_subst_compose[of h\<^sub>F] have "?t = (?h (?hi (subst_of bs)) \<circ>\<^sub>s (?h (?hi ?xt))) y" by metis
      then have "?t = (?h (?hi (subst_of bs)) y) \<cdot> (?h (?hi ?xt))" using subst_compose_def by metis
      with Cons have "?t = (subst_of bs y) \<cdot> (?h (?hi ?xt))" by auto
      with t have "?t = (subst_of bs y) \<cdot> (?h (?hi ?xt))" unfolding subst_of_def by auto
      with x[of x "inv h\<^sub>F"] have "?t = (subst_of bs y) \<cdot> (?h (subst x (h\<^sup>-\<^sup>1 t)))"
        unfolding subst_of_def h_inv_def by auto
      with x[of x h\<^sub>F] have "?t = (subst_of bs y) \<cdot> (subst x (h (h\<^sup>-\<^sup>1 t)))" unfolding subst_of_def by auto
      with t have "?t = (subst_of bs y) \<cdot> ?xt" by auto
      then have "?t = ((subst_of bs) \<circ>\<^sub>s ?xt) y" unfolding subst_compose_def by metis
      then show ?case unfolding xt by auto
    qed
  }
  then have "h\<^sub>s (h\<^sub>s_inv \<mu>) = \<mu>" unfolding h\<^sub>s_def mu by auto
  with mgu show ?thesis by auto
qed
   
lemma PCP_h:
  assumes "(hs,ht) \<in> irun_h.PCP_ext (h\<^sub>R R\<^sub>\<omega> \<union> ((h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>))"
  shows "(h\<^sup>-\<^sup>1 hs, h\<^sup>-\<^sup>1 ht) \<in> PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) \<and> hs = h (h\<^sup>-\<^sup>1 hs) \<and> ht = h (h\<^sup>-\<^sup>1 ht)"
proof-
  let ?s = "h\<^sup>-\<^sup>1 hs"
  let ?t = "h\<^sup>-\<^sup>1 ht"
  from assms[unfolded irun_h.PCP_ext_def] obtain hrl hrl' pos \<mu> where
    ooverlap:"ooverlap {\<succ>\<^sub>h} (h\<^sub>R R\<^sub>\<omega> \<union> (h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>) hrl hrl' pos \<mu> (hs) (ht)" and
    nf:"\<forall>hs\<lhd>fst hrl \<cdot> \<mu>. hs \<in> NF (ordstep {\<succ>\<^sub>h} (h\<^sub>R R\<^sub>\<omega> \<union> (h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>))" by blast
  (* ooverlap *)
  obtain hl hr hl' hr' where hrl:"hrl = (hl, hr)" "hrl' = (hl', hr')" by force
  { fix p hl hr
    assume p:"\<exists>p. p \<bullet> (hl, hr) \<in> h\<^sub>R R\<^sub>\<omega> \<union> (h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>"
    then obtain p where "(p \<bullet> hl, p \<bullet> hr) \<in> h\<^sub>R R\<^sub>\<omega> \<union> (h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>"
      unfolding rule_pt.permute_prod_eqvt by auto
    then have p:"(p \<bullet> hl, p \<bullet> hr) \<in> h\<^sub>R (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" using hR_union hR_sym by blast
    let ?l = "p \<bullet> hl" and ?r = "p \<bullet> hr"
    from inv_hR_rule[OF p] have x:"(h\<^sup>-\<^sup>1 ?l, h\<^sup>-\<^sup>1 ?r) \<in> (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" "h (h\<^sup>-\<^sup>1 ?l) = ?l \<and> h (h\<^sup>-\<^sup>1 ?r) = ?r"
      unfolding perm_inv_h by auto
    from this(2) have "h (h\<^sup>-\<^sup>1 hl) = hl \<and> h (h\<^sup>-\<^sup>1 hr) = hr"
      unfolding perm_inv_h[symmetric] perm_h[symmetric] term_pt.permute_eq_iff by auto
    with x have "(\<exists>p. p \<bullet> (h\<^sup>-\<^sup>1 hl, h\<^sup>-\<^sup>1 hr) \<in> R\<^sub>\<omega> \<union> (E\<^sub>\<omega>)\<^sup>\<leftrightarrow>) \<and> h (h\<^sup>-\<^sup>1 hl) = hl \<and> h (h\<^sup>-\<^sup>1 hr) = hr"
      unfolding rule_pt.permute_prod_eqvt perm_inv_h by meson
  } note perm_rule = this
  note ooverlap = ooverlap[unfolded ooverlap_def hrl snd_conv fst_conv]
  then have
    p:"\<exists>p. p \<bullet> (hl, hr) \<in> h\<^sub>R R\<^sub>\<omega> \<union> (h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>" and
    p':"\<exists>p'. p' \<bullet> (hl', hr') \<in> h\<^sub>R R\<^sub>\<omega> \<union> (h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>" and
    vars:"vars_rule (hl, hr) \<inter> vars_rule (hl', hr') = {}" and
    pos:"pos \<in> fun_poss hl'" and
    mgu:"mgu hl (hl' |_ pos) = Some \<mu>" and
    less:"(hr \<cdot> \<mu>, hl \<cdot> \<mu>) \<notin> {\<succ>\<^sub>h}" and less':"(hr' \<cdot> \<mu>, hl' \<cdot> \<mu>) \<notin> {\<succ>\<^sub>h}" and
    cs:"hs = (ctxt_of_pos_term pos (hl' \<cdot> \<mu>))\<langle>hr \<cdot> \<mu>\<rangle>" and ht_mu:"ht = hr' \<cdot> \<mu>" by auto
  note p = perm_rule[OF p] perm_rule[OF p']
  from p have 1:"\<exists>p. p \<bullet> (h\<^sup>-\<^sup>1 hl, h\<^sup>-\<^sup>1 hr) \<in> R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "\<exists>p. p \<bullet> (h\<^sup>-\<^sup>1 hl', h\<^sup>-\<^sup>1 hr') \<in> R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" by auto
  from p have inv:"h (h\<^sup>-\<^sup>1 hl) = hl" "h (h\<^sup>-\<^sup>1 hr) = hr" "h (h\<^sup>-\<^sup>1 hl') = hl'" "h (h\<^sup>-\<^sup>1 hr') = hr'" by auto
  have vt:"\<And>t. vars_term (h\<^sup>-\<^sup>1 t) = vars_term t" by (unfold h_inv_def, auto)
  from vars have 2:"vars_rule (h\<^sup>-\<^sup>1 hl, h\<^sup>-\<^sup>1 hr) \<inter> vars_rule (h\<^sup>-\<^sup>1 hl', h\<^sup>-\<^sup>1  hr') = {}"
    unfolding vars_rule_def fst_conv snd_conv vt by auto
  from pos have 3:"pos \<in> fun_poss (h\<^sup>-\<^sup>1 hl')" using fun_poss_inv_h by auto
  from mgu inv(3) have "mgu hl (h (h\<^sup>-\<^sup>1 hl') |_ pos ) = Some \<mu>" by argo
  with pos_term_h[OF fun_poss_imp_poss[OF 3]] have "mgu (h (h\<^sup>-\<^sup>1 hl)) (h (h\<^sup>-\<^sup>1 hl' |_ pos )) = Some \<mu>"
    using inv(1) by auto
  from mgu_h[OF this] have 4:"mgu (h\<^sup>-\<^sup>1 hl) (h\<^sup>-\<^sup>1 hl' |_ pos) = Some (h\<^sub>s_inv \<mu>)" and \<mu>:"\<mu> = h\<^sub>s (h\<^sub>s_inv \<mu>)"
    unfolding h\<^sub>s_def by auto
  let ?\<mu> = "h\<^sub>s_inv \<mu>"
  from \<mu> less inv have "(h (h\<^sup>-\<^sup>1 hr) \<cdot> (h\<^sub>s ?\<mu>), h (h\<^sup>-\<^sup>1 hl) \<cdot> (h\<^sub>s ?\<mu>)) \<notin> {\<succ>\<^sub>h}" by auto
  with subst_apply_h have "(h (h\<^sup>-\<^sup>1 hr \<cdot> ?\<mu>), h (h\<^sup>-\<^sup>1 hl \<cdot> ?\<mu>)) \<notin> {\<succ>\<^sub>h}" by auto
  with compat_h have 5:"((h\<^sup>-\<^sup>1 hr) \<cdot> ?\<mu>, (h\<^sup>-\<^sup>1 hl) \<cdot> ?\<mu>) \<notin> {\<succ>}" by fast
  from \<mu> less' inv have "(h (h\<^sup>-\<^sup>1 hr') \<cdot> (h\<^sub>s ?\<mu>), h (h\<^sup>-\<^sup>1 hl') \<cdot> (h\<^sub>s ?\<mu>)) \<notin> {\<succ>\<^sub>h}" by auto
  with subst_apply_h have "(h (h\<^sup>-\<^sup>1 hr' \<cdot> ?\<mu>), h (h\<^sup>-\<^sup>1 hl' \<cdot> ?\<mu>)) \<notin> {\<succ>\<^sub>h}" by auto
  with compat_h have 6:"((h\<^sup>-\<^sup>1 hr') \<cdot> ?\<mu>, (h\<^sup>-\<^sup>1 hl') \<cdot> ?\<mu>) \<notin> {\<succ>}" by fast
  let ?C = "ctxt_of_pos_term pos"
  from cs inv \<mu> have "hs = (ctxt_of_pos_term pos (h (h\<^sup>-\<^sup>1 hl') \<cdot> h\<^sub>s ?\<mu>))\<langle>h (h\<^sup>-\<^sup>1 hr) \<cdot> h\<^sub>s ?\<mu>\<rangle>" by auto
  with subst_apply_h have hs:"hs = (?C (h (h\<^sup>-\<^sup>1 hl' \<cdot> ?\<mu>)))\<langle>h (h\<^sup>-\<^sup>1 hr \<cdot> ?\<mu>)\<rangle>" by auto
      
  from ctxt_of_pos_term_map_funs_term_conv fun_poss_imp_poss[OF 3]
    have "?C (h (h\<^sup>-\<^sup>1 hl' \<cdot> ?\<mu>)) = h\<^sub>C (?C (h\<^sup>-\<^sup>1 hl' \<cdot> ?\<mu>))"
    unfolding h_def h\<^sub>C_def by auto
  with ctxt_apply_h have hs:"hs = h ((?C (h\<^sup>-\<^sup>1 hl' \<cdot> ?\<mu>))\<langle>h\<^sup>-\<^sup>1 hr \<cdot> ?\<mu>\<rangle>)" unfolding hs by auto
  note inv_subst_apply_h = map_funs_subst_distrib[of "inv h\<^sub>F", unfolded h_inv_def[symmetric]]
  note inv_ctxt_apply_h = map_funs_term_ctxt_distrib[of "inv h\<^sub>F", unfolded h_inv_def[symmetric]]
  from fun_poss_imp_poss[OF 3] have pos':"pos \<in> poss (hl' \<cdot> \<mu>)" unfolding poss_inv_h by auto
  from hs have "hs = h (h\<^sup>-\<^sup>1 (?C (hl' \<cdot> \<mu>))\<langle>hr \<cdot> \<mu>\<rangle>)"
    unfolding inv_subst_apply_h[symmetric] unfolding h_inv_def
    ctxt_of_pos_term_map_funs_term_conv[OF pos', symmetric]
    inv_ctxt_apply_h[symmetric, unfolded h_inv_def] by simp
  with cs have hs':"h (h\<^sup>-\<^sup>1 hs) = hs" by auto
  have 7:"h\<^sup>-\<^sup>1 hs = (ctxt_of_pos_term pos (h\<^sup>-\<^sup>1 hl' \<cdot> h\<^sub>s\<^sup>-\<^sup>1 \<mu>))\<langle>h\<^sup>-\<^sup>1 hr \<cdot> h\<^sub>s\<^sup>-\<^sup>1 \<mu>\<rangle>" unfolding hs inv_h_h by auto
  
  from ht_mu \<mu> inv(4) have "h (h\<^sup>-\<^sup>1 ht) = h (h\<^sup>-\<^sup>1 (h (h\<^sup>-\<^sup>1 hr') \<cdot> h\<^sub>s (h\<^sub>s_inv \<mu>)))" by auto
  with subst_apply_h have "h (h\<^sup>-\<^sup>1 ht) = h (h\<^sup>-\<^sup>1 (h (h\<^sup>-\<^sup>1 hr' \<cdot> h\<^sub>s_inv \<mu>)))" by auto
  then have "h (h\<^sup>-\<^sup>1 ht) = h (h\<^sup>-\<^sup>1 hr') \<cdot> (h\<^sub>s (h\<^sub>s_inv \<mu>))" unfolding inv_h_h unfolding subst_apply_h by auto
  with inv(4) \<mu> ht_mu have ht':"h (h\<^sup>-\<^sup>1 ht) = ht" by auto
  then have "?t = h\<^sup>-\<^sup>1 (hr' \<cdot> \<mu>)" unfolding ht_mu using inv_h_h by auto
  then have 8:"?t = h\<^sup>-\<^sup>1 hr' \<cdot> ?\<mu>" unfolding inv_subst_apply_h by blast   
  from 1 2 3 4 5 6 7 8 have o:"ooverlap {\<succ>} (R\<^sub>\<omega> \<union> (E\<^sub>\<omega>)\<^sup>\<leftrightarrow>) (h\<^sup>-\<^sup>1 hl, h\<^sup>-\<^sup>1 hr) (h\<^sup>-\<^sup>1 hl', h\<^sup>-\<^sup>1 hr') pos ?\<mu> ?s ?t"
    unfolding ooverlap_def fst_conv snd_conv by argo
  have nf:"\<forall>u \<lhd> (h\<^sup>-\<^sup>1 hl) \<cdot> ?\<mu>. u \<in> NF (ordstep {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))"
  proof(rule, rule)
    fix u
    assume "(h\<^sup>-\<^sup>1 hl) \<cdot> ?\<mu> \<rhd> u"
    with subterm_strict_h have "h ((h\<^sup>-\<^sup>1 hl) \<cdot> ?\<mu>) \<rhd> h u" by metis
    with inv(1) \<mu> subst_apply_h have a:"hl \<cdot> \<mu> \<rhd> h u" by auto
    { fix v
      assume "(u,v) \<in> ordstep {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
      then have False proof(cases)
        case (1 l r C \<sigma>)
        from 1(1) have "(h l, h r) \<in> h\<^sub>R (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
          unfolding h\<^sub>R_def h_def map_funs_trs.simps map_funs_rule.simps by force
        with hR_union hR_sym have hlr:"(h l, h r) \<in> h\<^sub>R R\<^sub>\<omega> \<union> (h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>" by blast
        from 1(2) subst_apply_h ctxt_apply_h have 2:"h u = (h\<^sub>C C)\<langle>h l \<cdot> h\<^sub>s \<sigma>\<rangle>" by auto
        from 1(3) subst_apply_h ctxt_apply_h have 3:"h v = (h\<^sub>C C)\<langle>h r \<cdot> h\<^sub>s \<sigma>\<rangle>" by auto
        from 1(4) compat_h subst_apply_h have 4:"(h l \<cdot> h\<^sub>s \<sigma>, h r \<cdot> h\<^sub>s \<sigma>) \<in> {\<succ>\<^sub>h}" by force
        from hlr 2 3 4 have "(h u,h v) \<in> ordstep {\<succ>\<^sub>h} (h\<^sub>R R\<^sub>\<omega> \<union> (h\<^sub>R E\<^sub>\<omega>)\<^sup>\<leftrightarrow>)"
          unfolding ordstep.simps by blast
        with nf a show False unfolding hrl fst_conv by auto
      qed
    }
    then show "u \<in> NF (ordstep {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))" by fast
  qed
  from o nf have "(?s,?t) \<in> PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" unfolding PCP_ext_def by force
  with hs' ht' show ?thesis by auto
qed
  
end


datatype ('a,'b) f_ext = FOrig 'a | FFresh 'b
  
text \<open>Towards completeness of ordered completion.\<close>
locale gtotal_okb_irun2 = gtotal_okb_irun_inf R E less
  for R :: "nat \<Rightarrow> (('a, 'b::infinite) term \<times> ('a, 'b) term) set" 
  and E :: "nat \<Rightarrow> (('a, 'b) term \<times> ('a, 'b) term) set" 
  and less :: "('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
  +
  fixes "c"::'a
  assumes c_min:"\<forall>(t::('a, 'b) term). t \<succeq> (Fun c [])"
begin

text \<open>Replace variables in a term by fresh function symbols.\<close>
  
sublocale sk: inj_homomorphism FOrig
  by (unfold_locales, insert inj_on_def, auto)

definition "\<sigma>\<^sub>s\<^sub>k" where "\<sigma>\<^sub>s\<^sub>k \<equiv> (\<lambda>x. Fun (FFresh x) [])"
    
definition sk :: "('a, 'b) term \<Rightarrow> (('a, 'b)f_ext, 'b) term"
  where "sk t = (sk.h t) \<cdot> \<sigma>\<^sub>s\<^sub>k"
  
lemma ground_sk [simp]: "ground (sk t)"
  by (induct t, insert sk_def sk.h_def, unfold \<sigma>\<^sub>s\<^sub>k_def, auto)
  
definition orig_sig :: "(('a,'b) f_ext, 'b) term \<Rightarrow> bool"
  where "orig_sig t = (\<forall>x. FFresh x \<notin> funs_term t)"

definition orig_sig\<^sub>C :: "(('a,'b) f_ext, 'b) ctxt \<Rightarrow> bool"
   where "orig_sig\<^sub>C t = (\<forall>x. FFresh x \<notin> funs_ctxt t)"
  
lemma inj_on_sigma_sk: "inj_on (\<lambda> t. t \<cdot> \<sigma>\<^sub>s\<^sub>k) {t|t. orig_sig t}"
proof-
  { fix s::"(('a,'b) f_ext, 'b) term"
    fix t
    assume st:"s \<noteq> t" and s_dom:"\<forall>x. FFresh x \<notin> funs_term s" and t_dom:"\<forall>x. FFresh x \<notin> funs_term t"
    then have "s \<cdot> \<sigma>\<^sub>s\<^sub>k \<noteq> t \<cdot> \<sigma>\<^sub>s\<^sub>k" proof(induct s arbitrary:t)
      case (Var x)
      then show ?case using eval_term.simps unfolding \<sigma>\<^sub>s\<^sub>k_def by (cases t, auto)
    next
      case (Fun f ss)
      note Funs = this
      then show ?case proof(cases t)
        case (Var x)
        from Funs show ?thesis unfolding Var eval_term.simps \<sigma>\<^sub>s\<^sub>k_def by auto
      next
        case (Fun g ts)
        then show ?thesis proof(cases "f=g")
          case True
          from Funs[unfolded Fun True] have "ss \<noteq> ts" by auto
          then have diff:"(\<exists>i < length ss. ss ! i \<noteq> ts ! i) \<or> (length ss \<noteq> length ts)"
            using nth_equalityI by blast
          then show ?thesis proof(cases "length ss \<noteq> length ts")
            case True
             then show ?thesis unfolding Fun eval_term.simps using map_eq_imp_length_eq by blast
          next
            case False
            with diff obtain i where i:"i < length ss" "ss ! i \<noteq> ts ! i" by auto
            from i have in_set:"ss ! i \<in> set ss" by auto
            from i False have in_set2:"ts ! i \<in> set ts" by auto
            with in_set Funs(3) Funs(4)
              have all:"\<forall>x. FFresh x \<notin> funs_term (ss ! i)" " \<forall>x. FFresh x \<notin> funs_term (ts ! i)"
              unfolding Fun by auto
            from Funs(1)[OF in_set i(2) all]
             i show ?thesis unfolding Fun using map_nth_conv by fastforce
          qed
        next
          case False
          with Funs show ?thesis unfolding Fun by auto
        qed
      qed
    qed
  }
  then show ?thesis unfolding inj_on_def orig_sig_def by auto
qed
    
lemma orig_sig_h:"orig_sig (sk.h t)"
  unfolding orig_sig_def sk.h_def using funs_term_map_funs_term[of FOrig t]
  by blast

lemma sk_Fun: "sk (Fun f ts) = Fun (FOrig f) (map sk ts)" unfolding sk_def by auto

lemma sk_ctxt_exists:
  fixes t::"('a, 'b) term"
  fixes u\<^sub>s::"(('a, 'b) f_ext, 'b) term"
  assumes "sk t = C\<^sub>s\<langle>u\<^sub>s\<rangle>"
  shows "\<exists> C u. C\<^sub>s = (sk.h\<^sub>C C) \<cdot>\<^sub>c \<sigma>\<^sub>s\<^sub>k \<and> u\<^sub>s = sk u"
  using assms
proof (induct C\<^sub>s arbitrary: t)
  case Hole
  show ?case unfolding orig_sig\<^sub>C_def by (rule exI[of _ Hole], rule exI[of _ t], insert Hole, auto)
next
  case (More g bef C aft)
  from More(2) obtain f ts where t: "t = Fun f ts" "g = FOrig f" unfolding sk_def \<sigma>\<^sub>s\<^sub>k_def by (cases t, auto)
  from More(2) sk_Fun have args:"bef @ C\<langle>u\<^sub>s\<rangle> # aft = map sk ts" unfolding t intp_actxt.simps by auto
  define i where "i \<equiv> length bef" let ?ti = "ts ! i"
  from arg_cong[OF args, of length] have l:"i < length ts" unfolding i_def by force
  from arg_cong[OF args, of "\<lambda>l. l ! i"] i_def have "sk ?ti = C\<langle>u\<^sub>s\<rangle>" unfolding nth_map[OF l] by simp
  from More(1)[OF this] obtain D v where D:"C = sk.h\<^sub>C D \<cdot>\<^sub>c \<sigma>\<^sub>s\<^sub>k" "u\<^sub>s = sk v" by auto
  let ?C = "More f (take i ts) D (drop (Suc i) ts)"
  from args l have b:"bef = map sk (take i ts)" by (metis append_eq_conv_conj take_map i_def)
  from l i_def arg_cong[OF args, of "\<lambda>l. drop (Suc i) l"]
    have a:"aft = map sk (drop (Suc i) ts)" unfolding drop_map by auto
  have *:"More g bef C aft = (sk.h\<^sub>C ?C) \<cdot>\<^sub>c \<sigma>\<^sub>s\<^sub>k"
    unfolding b a sk.h\<^sub>C_def actxt.map t(2) actxt.simps map_map sk_def D by auto
  show ?case by (rule exI[of _ ?C], rule exI[of _ v], insert * D, auto)
qed

fun deskolemize :: "(('a, 'b) f_ext, 'b) term \<Rightarrow> ('a, 'b) term"  where
    "deskolemize (Var x) = Var x"
  | "deskolemize (Fun (FOrig f) ts) = Fun f (map deskolemize ts)"
  | "deskolemize (Fun (FFresh f) _) = Var f"

lemma deskolemize_sk[simp]:"deskolemize (sk t) = t"
proof(induct t)
case (Var x)
  then show ?case unfolding sk_def \<sigma>\<^sub>s\<^sub>k_def by auto
next
  case (Fun f ts)
  then have "map (deskolemize \<circ> sk) ts = ts" by (simp add: map_idI)
  then show ?case unfolding sk_def sk.h_def term.map eval_term.simps map_map deskolemize.simps(2) o_def by simp
qed

lemma deskolemize_orig_sig: "orig_sig t \<Longrightarrow> deskolemize t = sk.h_inv t"
proof(induct t)
  case (Var x)
  then show ?case unfolding deskolemize.simps sk.h_inv_def term.map by simp
next
  case (Fun f' ts)
  from Fun(2) obtain f where f:"f' = FOrig f" unfolding orig_sig_def by (cases f', auto)
  from Fun have "map deskolemize ts = map sk.h_inv ts" unfolding orig_sig_def by (simp add: map_idI)
  then show ?case unfolding f deskolemize.simps sk.h_inv_def term.map by (simp add: sk.injF)
qed

lemma deskolemize_subst: "orig_sig t \<Longrightarrow> deskolemize (t \<cdot> \<sigma>) = (deskolemize t) \<cdot> (deskolemize \<circ> \<sigma>)"
proof(induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f' ts)
  then obtain f where f:"f' = FOrig f" unfolding orig_sig_def by (cases f', auto)
  from Fun have "\<And>t\<^sub>i. t\<^sub>i \<in> set ts \<Longrightarrow> orig_sig t\<^sub>i" using orig_sig_def by auto
  with Fun have "map (\<lambda>t\<^sub>i. deskolemize (t\<^sub>i \<cdot> \<sigma>)) ts = map (\<lambda>t\<^sub>i. (deskolemize t\<^sub>i) \<cdot> (deskolemize \<circ> \<sigma>)) ts"
    by (meson map_eq_conv)
  then show ?case unfolding f eval_term.simps deskolemize.simps by auto
qed

lemma sk_deskolemize_subst_vars:
  assumes "sk s = l \<cdot> \<tau>"
  shows "\<forall>x \<in> vars_term l. \<tau> x = sk (deskolemize (\<tau> x))"
  using assms
proof(induct l arbitrary:s)
  case (Var x)
  then have tx:"\<tau> x = sk s" by auto
  have "sk (deskolemize (\<tau> x)) = \<tau> x" using deskolemize_sk unfolding tx by metis
  then show ?case by auto
next
  case (Fun f ls)
  note Funl = this
  then have eq:"sk s = Fun f (map (\<lambda>ti. ti \<cdot> \<tau>) ls)" by auto
  show ?case proof(cases s)
    case (Var x)
    from eq[unfolded Var] have "f = FFresh x" unfolding sk_def \<sigma>\<^sub>s\<^sub>k_def by auto
    from eq[unfolded this] have "ls = []" unfolding sk_def Var \<sigma>\<^sub>s\<^sub>k_def by auto
    with Fun show ?thesis by auto
  next
    case (Fun g ss)
    from eq[unfolded Fun eval_term.simps] have
      fg:"f = FOrig g" "map sk ss = map (\<lambda>ti. ti \<cdot> \<tau>) ls" unfolding sk_Fun by auto
    then have len:"length ss = length (map (\<lambda>ti. ti \<cdot> \<tau>) ls)" using length_map by metis
    { fix i
      assume i:"i < length ls"
      from fg(2) map_nth_eq_conv[OF len] i have "sk (ss ! i) = (ls ! i) \<cdot> \<tau>" by force
      from Funl(1)[OF _ this] i have "\<forall>x\<in>vars_term (ls ! i). \<tau> x = sk (deskolemize (\<tau> x))" by auto
    }
    then show ?thesis using var_imp_var_of_arg[of _ f ls] by force
  qed
qed

lemma deskolemize_s:
  assumes "sk t  = sk.h (u :: ('a, 'b) term) \<cdot> \<sigma>"
  shows "t = u \<cdot> (deskolemize \<circ> \<sigma>)"
proof-
  have xs:"\<And>x. (deskolemize \<circ> \<sigma>\<^sub>s\<^sub>k) x = Var x" using deskolemize_sk[of "Var _"] unfolding sk_def by simp
  with term_subst_eq_conv[of t Var "deskolemize \<circ> \<sigma>\<^sub>s\<^sub>k"] have t:"t \<cdot> (deskolemize \<circ> \<sigma>\<^sub>s\<^sub>k) = t" by simp
  from assms[unfolded sk_def] have "deskolemize (sk.h t \<cdot> \<sigma>\<^sub>s\<^sub>k) = deskolemize (sk.h u \<cdot> \<sigma>)" by auto
  then show ?thesis
    using deskolemize_subst[OF orig_sig_h] deskolemize_orig_sig[OF orig_sig_h] sk.inv_h_h t by metis
qed

lemma rstep_imp_deskolemize_rstep:
  assumes "(s, t) \<in> rstep (sk.h\<^sub>R RR)"
  shows "(deskolemize s, deskolemize t) \<in> (rstep RR)\<^sup>="
proof-
  from assms obtain l r \<sigma> C where lr:"(l,r) \<in> sk.h\<^sub>R RR" and st:"s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  show ?thesis unfolding st proof(induct C)
    case Hole
    from orig_sig_h have sig:"orig_sig l" "orig_sig r" unfolding orig_sig_def by (metis lr sk.inv_hR_rule)+
    let ?l = "sk.h_inv l" and ?r = "sk.h_inv r"
    from sig deskolemize_orig_sig deskolemize_subst have d:
      "deskolemize (l \<cdot> \<sigma>) = ?l \<cdot> (deskolemize \<circ> \<sigma>)" "deskolemize (r \<cdot> \<sigma>) = ?r \<cdot> (deskolemize \<circ> \<sigma>)" by auto
    from sig lr deskolemize_orig_sig sk.inv_hR_rule have "(?l,?r) \<in> RR" by auto
    then show ?case unfolding intp_actxt.simps d by auto
  next
    case (More f' bef C aft)
    then show ?case proof(cases f')
      case (FOrig f)
      let ?C = "More f (map deskolemize bef) Hole (map deskolemize aft)"
      from More show ?thesis unfolding FOrig intp_actxt.simps deskolemize.simps map_append list.map
        using rstep_ctxt[of _ _ _ ?C] by auto
    next
      case (FFresh f)
      from More show ?thesis unfolding lr FFresh intp_actxt.simps deskolemize.simps by auto
    qed
  qed
qed

lemma rstep_imp_deskolemize_rsteps:
  assumes "(s, t) \<in> (rstep (sk.h\<^sub>R RR))\<^sup>*"
  shows "(deskolemize s, deskolemize t) \<in> (rstep RR)\<^sup>*"
  using assms
proof(induct, simp)
  case (step t u)
  with rstep_imp_deskolemize_rstep have "(deskolemize t, deskolemize u) \<in> (rstep RR)\<^sup>=" by auto
  with step show ?case by auto
qed

lemma rstep_imp_rstep_sk_h:"(s,t) \<in> rstep RR \<Longrightarrow> (sk.h s, sk.h t) \<in> rstep (sk.h\<^sub>R RR)"
  using sk.rstep_h[of s t RR] unfolding sk_def by auto

lemma rstep_imp_rstep_sk:"(s,t) \<in> rstep RR \<Longrightarrow> (sk s, sk t) \<in> rstep (sk.h\<^sub>R RR)"
  using sk.rstep_h[of s t RR] rstep_subst unfolding sk_def by auto

lemma rstep_sk_imp_rstep:"(sk s, sk t) \<in> rstep (sk.h\<^sub>R RR) \<Longrightarrow> (s,t) \<in> (rstep RR)\<^sup>="
  using rstep_imp_deskolemize_rstep deskolemize_sk by metis

lemma rstep_step_sk:"s \<noteq> t \<Longrightarrow> (s,t) \<in> rstep RR = ((sk s, sk t) \<in> rstep (sk.h\<^sub>R RR))"
  using rstep_imp_rstep_sk[of s t] rstep_sk_imp_rstep[of s t] by blast

lemma sk_C:
  assumes "sk s = C\<langle>t\<rangle>"
  shows "hole_pos C \<in> poss s \<and> sk (s |_ (hole_pos C)) = t"
  using assms
proof(induct C arbitrary: s t)
  case Hole
  then show ?case by auto
next
  case (More f bef ctx aft)
  then obtain g ts where f:"s = Fun g ts" "f = FOrig g" unfolding sk_def \<sigma>\<^sub>s\<^sub>k_def by (cases s, auto)
  let ?ti = "ts ! (length bef)"
  from More[unfolded f] sk_Fun have ts:"bef @ ctx\<langle>t\<rangle> # aft = map sk ts" by auto
  from ts have "length (bef @ ctx\<langle>t\<rangle> # aft) = length ts" by auto
  then have l:"length bef < length ts" unfolding length_append length_Cons by linarith
  with ts have "sk ?ti = ctx\<langle>t\<rangle>" by (metis nth_append_length nth_map)
  with More(1)[OF this] have ti:"hole_pos ctx \<in> poss ?ti" "sk (?ti |_ hole_pos ctx) = t" by auto
  with l have p:"hole_pos (More f bef ctx aft) \<in> poss s" unfolding f poss.simps(2) by simp
  with ti(2) show ?case unfolding f subt_at.simps by simp
qed

lemma sk_inj:"sk s = sk t \<Longrightarrow> s = t"
  using sk.inj inj_on_sigma_sk orig_sig_h unfolding sk_def inj_on_def by blast

definition sk_redord :: "((('a,'b) f_ext, 'b) term \<Rightarrow> (('a,'b) f_ext, 'b) term \<Rightarrow> bool) \<Rightarrow> bool"
  where "sk_redord Rel \<equiv>
  ((\<forall> s t. s \<succ> t \<longrightarrow> Rel (sk.h s) (sk.h t)) \<and>
   (\<forall> s t. ground s \<and> ground t \<longrightarrow> s = t \<or> Rel s t \<or> Rel t s) \<and>
   SN {(x, y). Rel x y} \<and>
   (\<forall> s t C. Rel s t \<longrightarrow> Rel C\<langle>s\<rangle> C\<langle>t\<rangle>) \<and>
   (\<forall> s t \<sigma>. Rel s t \<longrightarrow> Rel (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)) \<and>
   (\<forall> s t u. Rel s t \<longrightarrow> Rel t u \<longrightarrow> Rel s u) \<and>
   (\<forall> t. ground t \<longrightarrow> Rel\<^sup>=\<^sup>= t (sk.h (Fun c []))))"
  
text \<open>Assume a ground total extension of \<succ> on image of homomorphism terms .\<close>
  
definition prec\<^sub>o :: "(('a \<times> nat) \<times> ('a \<times> nat)) set" where
  "prec\<^sub>o \<equiv> (SOME Rel. well_order_on (UNIV - {(c,0)}) Rel) \<union> {((c,0),fn) |fn. True}"
  
definition prec\<^sub>f :: "(('b \<times> nat) \<times> ('b \<times> nat)) set" where
  "prec\<^sub>f \<equiv> (SOME Rel. well_order Rel)"
  
definition prec_set where
 "prec_set \<equiv> {((FOrig f, n), (FFresh g, m)) |f g n m. True} \<union>
             {((FFresh f, n), (FFresh g, m)) |f g n m. ((f,n),(g,m)) \<in> prec\<^sub>f - Id} \<union>
             {((FOrig f, n), (FOrig g, m)) |f g n m. ((f,n),(g,m)) \<in> prec\<^sub>o - Id}"

definition prec\<^sub>s\<^sub>k where "prec\<^sub>s\<^sub>k gm fn \<equiv> (fn, gm) \<in> prec_set"

lemma well_order_precf:"well_order prec\<^sub>f"
proof-
  from Zorn.well_order_on obtain r ::"(('b \<times> nat) \<times> ('b \<times> nat)) set" where r:"well_order r" by blast
  have "\<exists>Rel :: (('b \<times> nat) \<times> ('b \<times> nat)) set. well_order Rel" unfolding prec\<^sub>f_def
    by (rule exI[of _r], insert r, auto)
  from someI_ex[OF this] show ?thesis using prec\<^sub>f_def by auto
qed

lemma well_order_preco:"well_order prec\<^sub>o"
proof-  
  define R ::"(('a \<times> nat) \<times> ('a \<times> nat)) set" where "R \<equiv> SOME Rel. well_order_on (UNIV - {(c,0)}) Rel"
  have p:"prec\<^sub>o = R \<union> {((c,0),fn) |fn. True}" unfolding prec\<^sub>o_def R_def by auto
      
  from Zorn.well_order_on obtain r ::"(('a \<times> nat) \<times> ('a \<times> nat)) set" where r:"well_order_on (UNIV - {(c,0)}) r" by blast
  have ex:"\<exists>Rel ::(('a \<times> nat) \<times> ('a \<times> nat)) set. well_order_on (UNIV - {(c,0)}) Rel"
    by (rule exI[of _ r], insert r, auto)
  from someI_ex[OF ex] have x:"well_order_on (UNIV - {(c,0)}) R" unfolding R_def by auto
  then have wf1:"wf (R - Id)" (is "wf ?R1") unfolding well_order_on_def by auto 
  have wf0:"wf ({((c,0),fn) |fn. True} - Id)" (is "wf ?R0") unfolding wf_def
    by (smt CollectD DiffD1 DiffD2 Pair_inject pair_in_Id_conv)
  from well_order_on_Field[OF x, unfolded Field_def]
    have "Domain ({((c,0),fn) |fn. True} - Id) \<inter> Range (R - Id) = {}" by auto
  from wf_Un[OF wf0 wf1 this] have "wf (({((c,0),fn) |fn. True} - Id) \<union> (R - Id))" by metis
  then have wf:"wf (prec\<^sub>o - Id)" unfolding p Un_Diff using Un_commute by metis
  
  let ?U = "UNIV - {(c,0)}"
  from well_order_on_Field[OF x, unfolded Field_def] have c:"(c,0) \<notin> Range R" unfolding R_def by auto
  from x have "linear_order_on?U R" unfolding well_order_on_def by auto
  then have po:"partial_order_on ?U R" and total:"Relation.total_on ?U R"
    unfolding linear_order_on_def by auto
  from po[unfolded partial_order_on_def] have pre:"preorder_on ?U R" and antisym:"antisym R" by auto
  then have refl:"refl_on ?U R" and trans:"trans R" unfolding preorder_on_def by auto
  have total:"total prec\<^sub>o"
  proof
    fix f g :: "('a \<times> nat)"
    assume "f \<noteq> g"
    with total[unfolded Relation.total_on_def] show "(f, g) \<in> prec\<^sub>o \<or> (g, f) \<in> prec\<^sub>o"
      unfolding p by (cases "f = (c,0)", auto)
  qed
  from refl have refl:"refl prec\<^sub>o" unfolding p refl_on_def by auto
  from trans c have trans:"trans prec\<^sub>o" unfolding p trans_def by blast
  from refl trans have pre:"preorder_on UNIV prec\<^sub>o" unfolding preorder_on_def by auto
  have antisym:"antisym prec\<^sub>o" proof
    fix f g :: "('a \<times> nat)"
    assume "(f, g) \<in> prec\<^sub>o" and "(g, f) \<in> prec\<^sub>o"
    with antisym[unfolded antisym_def] c show "f = g" unfolding p by blast
  qed
  from pre antisym have partial:"partial_order_on UNIV prec\<^sub>o" unfolding partial_order_on_def by auto
  from partial total have "linear_order prec\<^sub>o" unfolding linear_order_on_def by auto
  with wf show ?thesis unfolding well_order_on_def by auto
qed
  
lemma SN_prec:"SN {(gm,fn) |fn gm. prec\<^sub>s\<^sub>k gm fn }"
proof-
  let ?R\<^sub>f = "{((FFresh f, n), (FFresh g, m)) |f g n m. ((f,n),(g,m)) \<in> prec\<^sub>f - Id}"
  let ?R\<^sub>o = "{((FOrig f, n), (FOrig g, m)) |f g n m. ((f,n),(g,m)) \<in> prec\<^sub>o - Id}"
  let ?R\<^sub>o\<^sub>f = "{((FOrig f, n), (FFresh g, m)) |f g n m. True}"
  let ?F = "\<lambda>C. (\<lambda>(f,n).(C f, n))"
  have inj:"inj (?F FFresh)" unfolding inj_on_def by auto
  have aux:"\<And>C P.(map_prod (?F C) (?F C) ` (P - Id)) = {(?F C (f,n), ?F C (g,m)) |f g n m. ((f,n), (g,m)) \<in> P - Id}"
    unfolding split by force
  from well_order_precf have "wf (prec\<^sub>f - Id)" using well_order_on_def by auto
  from wf_map_prod_image[OF this inj] have wf\<^sub>f:"wf ?R\<^sub>f" unfolding aux[of FFresh] split by auto
      
  have inj:"inj (?F FOrig)" unfolding inj_on_def by auto
  from well_order_preco have "wf (prec\<^sub>o - Id)" unfolding well_order_on_def by auto
  from wf_map_prod_image[OF this inj] have wf\<^sub>o:"wf ?R\<^sub>o" unfolding aux by simp
      
  have wf:"wf ?R\<^sub>o\<^sub>f" by (smt Pair_inject f_ext.distinct(1) mem_Collect_eq wf_def)
  have "?R\<^sub>o\<^sub>f O ?R\<^sub>f \<subseteq> ?R\<^sub>o\<^sub>f" by blast
  from wf_union_compatible[OF wf wf\<^sub>f this] have wf:"wf (?R\<^sub>o\<^sub>f \<union> ?R\<^sub>f)" by auto
  from wf_union_compatible[OF this wf\<^sub>o] have wf:"wf ((?R\<^sub>o\<^sub>f \<union> ?R\<^sub>f) \<union> ?R\<^sub>o)" by blast
  then have "wf prec_set" unfolding prec_set_def by auto
  then show ?thesis unfolding prec\<^sub>s\<^sub>k_def SN_iff_wf converse_unfold mem_Collect_eq split by simp
qed
  
text \<open>Replace Skolem constants by minimal constant c\<close>
definition D\<^sub>c :: "(('a, 'b) f_ext, 'b) term \<Rightarrow> ('a, 'b) term"
  where "D\<^sub>c t \<equiv> map_funs_term (\<lambda>f. case f of FOrig f \<Rightarrow> f | FFresh z \<Rightarrow> c) t"
    
definition Dc\<^sub>c :: "(('a, 'b) f_ext, 'b) ctxt \<Rightarrow> ('a, 'b) ctxt"
  where "Dc\<^sub>c C \<equiv> map_funs_ctxt (\<lambda>f. case f of FOrig f \<Rightarrow> f | FFresh z \<Rightarrow> c) C"
    
definition Ds\<^sub>c :: "(('a, 'b) f_ext, 'b) subst \<Rightarrow> ('a, 'b) subst"
  where "Ds\<^sub>c \<sigma> \<equiv> map_funs_subst (\<lambda>f. case f of FOrig f \<Rightarrow> f | FFresh z \<Rightarrow> c) \<sigma>"
     
lemma Dc_h: "D\<^sub>c (sk.h t) = t" unfolding D\<^sub>c_def sk.h_def map_funs_term_comp
  by (simp add: funs_term_map_funs_term_id)
    
abbreviation kbo_sk :: "(('a, 'b) f_ext, 'b) term \<Rightarrow> (('a, 'b) f_ext, 'b) term \<Rightarrow> bool \<times> bool"
  where "kbo_sk \<equiv> kbo.kbo (\<lambda>f.1) 1 (\<lambda>f n. 1) (\<lambda>f. f = FOrig c) prec\<^sub>s\<^sub>k prec\<^sub>s\<^sub>k\<^sup>=\<^sup>="

lemma irrefl_precsk:"\<forall>fn. \<not> (fn,fn) \<in> prec_set"
  using SN_prec unfolding refl_on_def  prec\<^sub>s\<^sub>k_def by fastforce
    
lemma trans_preceq_sk:
  assumes "fn = gm \<or> prec\<^sub>s\<^sub>k fn gm" and "gm = hk \<or> prec\<^sub>s\<^sub>k gm hk"
  shows "(fn = gm \<and> gm = hk) \<or> prec\<^sub>s\<^sub>k fn hk"
proof-
  obtain f n g m h k where fn:"fn = (f,n)" and gm:"gm = (g,m)" and hk:"hk = (h,k)" by fastforce
  from assms have a:"(f,n) = (g,m) \<or> prec\<^sub>s\<^sub>k (f,n) (g,m)" "(g,m) = (h,k) \<or> prec\<^sub>s\<^sub>k (g,m) (h,k)"
    unfolding fn gm hk by auto
  have "\<And>R. well_order R \<Longrightarrow> trans R"
    unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def by auto
  note trans = this[OF well_order_precf] this[OF well_order_preco]
  { assume p:"((h,k), (g,m)) \<in> prec_set" "((g,m),(f,n)) \<in> prec_set" and neq:"(h,k) \<noteq> (f,n)"
    have "((h,k),(f,n)) \<in> prec_set" proof(cases h)
      case (FFresh a)
      from p[unfolded this] prec_set_def obtain b where g:"g = FFresh b" by auto
      from p[unfolded this] prec_set_def obtain c where f:"f = FFresh c" by auto
      from p[unfolded FFresh g f] prec_set_def have "((a,k),(b,m)) \<in> prec\<^sub>f" "((b,m),(c,n)) \<in> prec\<^sub>f" by auto
      note t = trans(1)[unfolded trans_def, rule_format, OF this]
      with neq show ?thesis unfolding FFresh f prec_set_def by auto
    next
      case (FOrig a)
      note h = this
      then show ?thesis proof(cases g)
        case (FFresh b)
        then show ?thesis using neq p unfolding prec_set_def FOrig FFresh by (cases h, auto)
      next
        case (FOrig b)
        show ?thesis using neq trans(2)[unfolded trans_def, rule_format, of "(a,k)" "(b,m)"] p
          unfolding prec_set_def h FOrig by (cases f, auto)
      qed
    qed
  }
  note trans = this
  show ?thesis
  proof (cases "(g, m) = (h, k)")
    case True
    from a show ?thesis unfolding fn gm hk prec\<^sub>s\<^sub>k_def split True by auto
  next
    case False
    with a have p:"((h, k), g, m) \<in> prec_set" unfolding prec\<^sub>s\<^sub>k_def by auto
    show ?thesis proof (cases "(f, n) = (g, m)")
      case True
      with a p show ?thesis unfolding fn gm hk prec\<^sub>s\<^sub>k_def by auto
    next
      case False
      from False a have p':"((g, m), f, n) \<in> prec_set" unfolding prec\<^sub>s\<^sub>k_def by auto
      { assume eq:"(h, k) = (f, n)"
        have aux:"{(gm, fn) |fn gm. (fn, gm) \<in> prec_set}\<inverse> = prec_set" by fast
        from p p' have "(fn,fn) \<in> ({(gm, fn) |fn gm. (fn, gm) \<in> prec_set}\<inverse>)\<^sup>+" unfolding fn eq prec\<^sub>s\<^sub>k_def aux by auto
        then have False using wf_acyclic[OF SN_imp_wf[OF SN_prec]] unfolding prec\<^sub>s\<^sub>k_def
          unfolding acyclic_def by blast
      }
      with p p' trans show ?thesis unfolding fn gm hk prec\<^sub>s\<^sub>k_def by fast
    qed
  qed
qed
 
lemma trans_prec_sk:
  assumes "prec\<^sub>s\<^sub>k fn gm" and "prec\<^sub>s\<^sub>k gm hk"
  shows "prec\<^sub>s\<^sub>k fn hk"
proof-
  from trans_preceq_sk assms have "(fn = gm \<and> gm = hk) \<or> prec\<^sub>s\<^sub>k fn hk" by presburger
  with assms irrefl_precsk show ?thesis unfolding refl_on_def by auto
qed
 
lemma antisym_prec_sk:
  assumes "prec\<^sub>s\<^sub>k fn gm"
  shows "\<not> prec\<^sub>s\<^sub>k gm fn"
using trans_prec_sk[OF assms, of fn] irrefl_precsk unfolding prec\<^sub>s\<^sub>k_def by auto
    
lemma adm:"admissible_kbo (\<lambda>f.1) 1 prec\<^sub>s\<^sub>k prec\<^sub>s\<^sub>k\<^sup>=\<^sup>= (\<lambda>f. f = FOrig c) (\<lambda>f n. 1)"
proof-
  have min:"\<forall>g. g \<noteq> FOrig c \<longrightarrow> prec\<^sub>s\<^sub>k (g, 0) (FOrig c, 0)"
  proof(rule, rule)
    fix g :: "('a, 'b) f_ext"
    assume gc:"g \<noteq> FOrig c"
    have "\<And>a. a \<noteq> c \<Longrightarrow> ((FOrig c,0), (FOrig a,0)) \<in> prec_set" unfolding prec\<^sub>o_def prec_set_def by auto
    with gc show "prec\<^sub>s\<^sub>k (g, 0) (FOrig c, 0)" unfolding prec\<^sub>s\<^sub>k_def prec_set_def by (cases g, auto)
  qed
  { fix f
    assume a:"\<forall>g. g = f \<or> prec\<^sub>s\<^sub>k (g, 0) (f, 0)" "f \<noteq> FOrig c"
    then have p:"prec\<^sub>s\<^sub>k (FOrig c, 0) (f, 0)" by auto
    from min a(2) have p':"prec\<^sub>s\<^sub>k (f, 0) (FOrig c, 0)" by auto
    from trans_prec_sk[OF p p'] irrefl_precsk[unfolded refl_on_def] have False
      using SN_on_irrefl SN_prec unfolding prec\<^sub>s\<^sub>k_def by blast
  }
  with min irrefl_precsk[unfolded refl_on_def] have
    min:"\<And>f. (f = (FOrig c)) = (\<forall>g. g = f \<or> prec\<^sub>s\<^sub>k (g, 0) (f, 0))" by auto
  show ?thesis  
  proof(unfold_locales)
    fix fn gm hk
    from trans_preceq_sk show "prec\<^sub>s\<^sub>k\<^sup>=\<^sup>= fn gm \<Longrightarrow> prec\<^sub>s\<^sub>k\<^sup>=\<^sup>= gm hk \<Longrightarrow> prec\<^sub>s\<^sub>k\<^sup>=\<^sup>= fn hk" by fast
  next
    fix fn gm
    from antisym_prec_sk show "prec\<^sub>s\<^sub>k fn gm = strict prec\<^sub>s\<^sub>k\<^sup>=\<^sup>= fn gm" by blast
  next
    show "SN {(x, y). prec\<^sub>s\<^sub>k x y}" using SN_prec by fast
  next
  qed (insert min, auto)
qed
 
lemma precsk_gtotal:"fn = gm \<or> prec\<^sub>s\<^sub>k fn gm \<or> prec\<^sub>s\<^sub>k gm fn"
proof-
  { assume neq:"fn \<noteq> gm"
  obtain f g n m where p:"fn = (f,n)" "gm = (g,m)" by fastforce
  from well_order_preco well_order_precf have t:"total prec\<^sub>o" "total prec\<^sub>f"
    unfolding well_order_on_def linear_order_on_def by auto
  have "prec\<^sub>s\<^sub>k fn gm \<or> prec\<^sub>s\<^sub>k gm fn" proof(cases f)
    case (FOrig a)
    from t[unfolded Relation.total_on_def] neq show "prec\<^sub>s\<^sub>k fn gm \<or> prec\<^sub>s\<^sub>k gm fn"
      unfolding prec\<^sub>s\<^sub>k_def prec_set_def p FOrig by (cases g, auto)
  next
    case (FFresh a)
    note a = this
    show "prec\<^sub>s\<^sub>k fn gm \<or> prec\<^sub>s\<^sub>k gm fn" proof (cases g)
      case (FOrig b)
      show ?thesis unfolding prec\<^sub>s\<^sub>k_def prec_set_def p FFresh FOrig by force
    next
      case (FFresh b)
      from t(2)[unfolded Relation.total_on_def] neq show ?thesis  
        unfolding prec\<^sub>s\<^sub>k_def prec_set_def p FFresh a by auto
    qed
  qed
  }
  then show ?thesis by auto
qed

abbreviation lex_sk
  where "lex_sk \<equiv> lex_two {\<succ>} Id  {(s, t). fst (kbo_sk s t)}"
  
definition less_sk :: "(('a,'b) f_ext, 'b) term \<Rightarrow> (('a,'b) f_ext, 'b) term \<Rightarrow> bool" (infix "\<succ>\<^sub>s\<^sub>k" 50)
  where "less_sk s t = (((D\<^sub>c s, s), (D\<^sub>c t, t)) \<in> lex_sk)"
  
abbreviation less_sk_set ("{\<succ>\<^sub>s\<^sub>k}") where "less_sk_set \<equiv> {(s, t). s \<succ>\<^sub>s\<^sub>k t}"

abbreviation lesseq_sk (infix "\<succeq>\<^sub>s\<^sub>k" 50) where "s \<succeq>\<^sub>s\<^sub>k t \<equiv> (\<succ>\<^sub>s\<^sub>k)\<^sup>=\<^sup>= s t"

  
text \<open>There exists a ground total extension of \<succ> on skolemized terms.\<close>
lemma less_sk: "sk_redord less_sk"
proof-
  define \<sigma>\<^sub>c :: "'b \<Rightarrow> ('a, 'b) term" where "\<sigma>\<^sub>c \<equiv> (\<lambda>x. Fun c [])"
  have 1:"\<forall>s t. s \<succ> t \<longrightarrow> sk.h s \<succ>\<^sub>s\<^sub>k sk.h t"
  proof(rule, rule, rule)
    fix s t
    assume "s \<succ> t"
    with subst have "D\<^sub>c (sk.h s) \<succ> D\<^sub>c (sk.h t)" unfolding Dc_h by auto
    then show "sk.h s \<succ>\<^sub>s\<^sub>k sk.h t" unfolding less_sk_def by auto
  qed
    
  have 2:"\<forall>s t. ground s \<and> ground t \<longrightarrow> s = t \<or> s \<succ>\<^sub>s\<^sub>k t \<or> t \<succ>\<^sub>s\<^sub>k s"
  proof(rule, rule, rule)
    fix s t :: "(('a,'b) f_ext, 'b) term"
    assume "ground s \<and> ground t"
    then have g:"ground s" "ground t" by auto
    from admissible_kbo.S_ground_total[OF adm refl precsk_gtotal _ g(1) _ g(2)]
    have kbo_gtotal:"s = t \<or> fst (kbo_sk s t) \<or> fst (kbo_sk t s)" by force
    from g have g':"ground (D\<^sub>c s)" "ground (D\<^sub>c t)" unfolding D\<^sub>c_def by auto
    with fgtotal kbo_gtotal show "s = t \<or> s \<succ>\<^sub>s\<^sub>k t \<or> t \<succ>\<^sub>s\<^sub>k s"
      unfolding fground_UNIV less_sk_def by force
  qed 
    
  have 3:"SN {\<succ>\<^sub>s\<^sub>k}"
  proof-
    from admissible_kbo.S_SN[OF adm] have "SN {(s, t). fst (kbo_sk s t)}" by auto
    from lex_two[OF _ SN_less this, of Id] have "SN {(s,t).(s,t) \<in> lex_sk}" by auto
    then show ?thesis unfolding less_sk_def by fast
  qed
    
  have 4:"\<forall>s t C. s \<succ>\<^sub>s\<^sub>k t \<longrightarrow> C\<langle>s\<rangle> \<succ>\<^sub>s\<^sub>k C\<langle>t\<rangle>"
  proof(rule+)
    fix s t C
    assume "s \<succ>\<^sub>s\<^sub>k t"
    then consider "D\<^sub>c s \<succ> D\<^sub>c t" | "(D\<^sub>c s = D\<^sub>c t \<and> fst (kbo_sk s t))" unfolding less_sk_def by auto
    then show "C\<langle>s\<rangle> \<succ>\<^sub>s\<^sub>k C\<langle>t\<rangle>" proof(cases)
      case 1
      from ctxt[OF 1, of "Dc\<^sub>c C"] show ?thesis
        unfolding D\<^sub>c_def Dc\<^sub>c_def map_funs_term_ctxt_distrib[symmetric] 
        unfolding D\<^sub>c_def[symmetric] less_sk_def by auto
    next
      case 2
      then have eq:"D\<^sub>c C\<langle>s\<rangle> = D\<^sub>c C\<langle>t\<rangle>" unfolding D\<^sub>c_def by auto
      from 2 admissible_kbo.S_ctxt[OF adm, of s t C] have "fst (kbo_sk C\<langle>s\<rangle> C\<langle>t\<rangle>)" by blast
      with eq show "C\<langle>s\<rangle> \<succ>\<^sub>s\<^sub>k C\<langle>t\<rangle>" unfolding less_sk_def by force
    qed
  qed
    
  have 5:"\<forall>s t \<sigma>. s \<succ>\<^sub>s\<^sub>k t \<longrightarrow> s \<cdot> \<sigma> \<succ>\<^sub>s\<^sub>k t \<cdot> \<sigma>"
  proof(rule+)
    fix s t \<sigma>
    assume "s \<succ>\<^sub>s\<^sub>k t"
    then consider "D\<^sub>c s \<succ> D\<^sub>c t" | "(D\<^sub>c s = D\<^sub>c t \<and> fst (kbo_sk s t))" unfolding less_sk_def by auto
    then show "s \<cdot> \<sigma> \<succ>\<^sub>s\<^sub>k t \<cdot> \<sigma>" proof(cases)
      case 1
      from subst[OF 1, of "Ds\<^sub>c \<sigma>"] show ?thesis 
        unfolding D\<^sub>c_def Ds\<^sub>c_def map_funs_subst_distrib[symmetric] 
        unfolding D\<^sub>c_def[symmetric] less_sk_def by auto
    next
      case 2
      then have eq:"D\<^sub>c (s \<cdot> \<sigma>) = D\<^sub>c (t \<cdot> \<sigma>)" unfolding D\<^sub>c_def by auto
      from 2 admissible_kbo.S_subst[OF adm, of s t \<sigma>] have "fst (kbo_sk (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))" by blast
      with eq show ?thesis  unfolding less_sk_def by auto
    qed
  qed
    
  have 6:"\<forall>s t u. s \<succ>\<^sub>s\<^sub>k t \<longrightarrow> t \<succ>\<^sub>s\<^sub>k u \<longrightarrow> s \<succ>\<^sub>s\<^sub>k u"
  proof(rule+)
    fix s t u
    assume "s \<succ>\<^sub>s\<^sub>k t" and tu:"t \<succ>\<^sub>s\<^sub>k u"
    then consider "D\<^sub>c s \<succ> D\<^sub>c t" | "(D\<^sub>c s = D\<^sub>c t \<and> fst (kbo_sk s t))" unfolding less_sk_def by auto
    then show "s \<succ>\<^sub>s\<^sub>k u" proof(cases)
      case 1
      from tu have "D\<^sub>c t \<succeq> D\<^sub>c u" unfolding less_sk_def by auto
      with trans[unfolded trans_def, OF 1, of "D\<^sub>c u"] 1 show ?thesis unfolding less_sk_def by auto
    next
      case 2
      have S_NS:"fst (kbo_sk t u) \<longrightarrow> snd (kbo_sk t u)"
        using adm admissible_kbo.S_imp_NS by blast
      note trans = admissible_kbo.kbo_trans[OF adm, THEN conjunct1, rule_format, of s t u]
      with 2 S_NS have "fst (kbo_sk t u) \<Longrightarrow> fst (kbo_sk s u)" by blast
      with 2 tu show ?thesis unfolding less_sk_def by (cases "D\<^sub>c t \<succ> D\<^sub>c u", auto)
    qed
  qed
    
  have "\<forall>t. ground t \<longrightarrow> t \<succeq>\<^sub>s\<^sub>k Fun (FOrig c) []"
  proof(rule+)
    fix t :: "(('a,'b) f_ext, 'b) term"
    assume g:"ground t" and t_neq_c:"t \<noteq> Fun (FOrig c) []"
    have Dc_c:"D\<^sub>c (Fun (FOrig c) []) = Fun c []" unfolding D\<^sub>c_def by auto
    show "t \<succ>\<^sub>s\<^sub>k Fun (FOrig c) []" proof(cases "\<exists>a. t = Fun (FFresh a) []")
      case True
      then obtain a where t:"t = Fun (FFresh a) []" by auto
      have Dc_f:"D\<^sub>c t = Fun c []" unfolding t D\<^sub>c_def Nil by auto
      let ?w = "weight_fun.weight (\<lambda>f. 1) 1 (\<lambda>f n. 1)"
      have w:"?w (Fun (FOrig c) []) = ?w t" unfolding t Nil weight_fun.weight.simps by auto
      have p:"prec\<^sub>s\<^sub>k (FFresh a, 0) (FOrig c, 0)" unfolding prec\<^sub>s\<^sub>k_def prec_set_def by auto
      note kbo = kbo.kbo.simps[of _ _ _ _ _ _ t "Fun (FOrig c) []", simplified]
      from p w have "fst (kbo_sk t (Fun (FOrig c) []))"
        unfolding kbo unfolding t Nil by force
      with Dc_f show ?thesis unfolding less_sk_def Dc_c by auto
    next
      case False
      from g obtain f ts where t:"t = Fun f ts" by (cases t, auto)
      from False t_neq_c have "D\<^sub>c t \<noteq> Fun c []" unfolding D\<^sub>c_def t by (cases f, auto)
      with c_min[rule_format, of "D\<^sub>c t"] have "D\<^sub>c t \<succ> Fun c []" unfolding Dc_c by auto
      then show ?thesis unfolding less_sk_def Dc_c by auto
    qed
  qed
  then have 7:"\<forall>t. ground t \<longrightarrow> (\<succ>\<^sub>s\<^sub>k)\<^sup>=\<^sup>= t (sk.h (Fun c []))" by auto
  from 1 2 3 4 5 6 7 show ?thesis unfolding sk_redord_def by force
qed

lemma c_min_less_sk:"ground t \<longrightarrow> less_sk\<^sup>=\<^sup>= t (Fun (FOrig c) [])"
  using less_sk[unfolded sk_redord_def] sk.h_def by auto
    
sublocale sk_run:gtotal_okb_irun_h R E "(\<succ>)" FOrig less_sk
proof (unfold_locales)
  show "\<And>s t u. less_sk s t \<Longrightarrow> less_sk t u \<Longrightarrow> less_sk s u" using less_sk[unfolded sk_redord_def] by fast
qed (insert less_sk[unfolded sk_redord_def], auto)

lemma rsteps_sk:"(s,t) \<in> (rstep RR)\<^sup>* \<Longrightarrow> ((sk s, sk t) \<in> (rstep (sk.h\<^sub>R RR))\<^sup>*)"
  using rstep_imp_rstep_sk by (meson rtrancl_map)

lemma rsteps_sk_h:"(s,t) \<in> (rstep RR)\<^sup>* \<Longrightarrow> ((sk.h s, sk.h t) \<in> (rstep (sk.h\<^sub>R RR))\<^sup>*)"
  using rstep_imp_rstep_sk_h[of _ _ RR] rtrancl_map[of "rstep RR"] by blast

lemma sk_clean_step:
  fixes l'::"('a,'b) term"
  assumes "((sk t) :: (('a, 'b) f_ext, 'b) term) = l\<cdot>\<sigma>" "l\<cdot>\<sigma> \<succ>\<^sub>s\<^sub>k r\<cdot>\<sigma>" "l = sk.h l'" "r = sk.h r'" "ground (r\<cdot>\<sigma>)"
  shows "\<exists>\<tau> u. l\<cdot>\<sigma> = l\<cdot>\<tau> \<and> r\<cdot>\<tau> = sk u \<and> l\<cdot>\<tau> \<succ>\<^sub>s\<^sub>k r\<cdot>\<tau>"
proof-
  define \<tau> where "\<tau> \<equiv> ext_subst \<sigma> l (FOrig c)"
  from assms deskolemize_s have t:"t = l' \<cdot> (deskolemize \<circ> \<sigma>)" by auto
  from sk_deskolemize_subst_vars[OF assms(1)] have vs:"\<forall>x\<in>vars_term l. \<sigma> x = sk (deskolemize (\<sigma> x))" by auto
  from assms subst_ext_subst'[of l] have eq:"l\<cdot>\<sigma> = l \<cdot> \<tau>" unfolding \<tau>_def by metis
  from local.sk_run.okb_h.ext_subst_less[of "FOrig c" r \<sigma>] c_min_less_sk assms(5)
    have  "(\<succ>\<^sub>s\<^sub>k)\<^sup>=\<^sup>= (r \<cdot> \<sigma>) (r \<cdot> \<tau>)" unfolding \<tau>_def by auto
  with assms(2) sk_run.trans_h[OF assms(2)] have less:"l\<cdot>\<tau> \<succ>\<^sub>s\<^sub>k r\<cdot>\<tau>" unfolding eq by auto
  define u where "u \<equiv> deskolemize (r\<cdot>\<tau>)"
  { fix x
    assume x:"x \<in> vars_term r'"
    have "\<tau> x = (sk.h\<^sub>s (deskolemize \<circ> \<tau>) \<circ>\<^sub>s \<sigma>\<^sub>s\<^sub>k) x" proof(cases "x \<in> vars_term l")
      case True
      then have "sk (deskolemize (\<tau> x)) = \<tau> x" using vs eq[unfolded term_subst_eq_conv] by auto
      then show ?thesis unfolding sk_def subst_compose_def by auto
    next
      case False
      with \<tau>_def x have \<tau>x:"\<tau> x = Fun (FOrig c) []" unfolding ext_subst_def by auto
      then have sig:"orig_sig (\<tau> x)" unfolding orig_sig_def by auto
      have "(sk.h\<^sub>s (deskolemize \<circ> \<tau>) \<circ>\<^sub>s \<sigma>\<^sub>s\<^sub>k) x = sk (deskolemize(\<tau> x))" by (simp add: sk_def subst_compose_def)
      also have "\<dots> = \<tau> x" unfolding \<tau>x deskolemize.simps sk_def by simp
      finally show ?thesis by auto
    qed
  }
  then have "sk.h r' \<cdot> sk.h\<^sub>s (deskolemize \<circ> \<tau>) \<cdot> \<sigma>\<^sub>s\<^sub>k = sk.h r'  \<cdot> \<tau>"
    using term_subst_eq_conv[of "sk.h r'" \<tau>] by force
  then have eq':"sk u = r\<cdot>\<tau>" unfolding u_def assms(4) deskolemize_subst[OF orig_sig_h] sk_def
    deskolemize_orig_sig[OF orig_sig_h] sk.inv_h_h sk.subst_apply_h by auto
  show ?thesis by (rule exI[of _ \<tau>],rule exI[of _ u], insert eq eq' less, auto)
qed
    

context
  assumes fair:"\<forall>(s, t)\<in> PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>). (s, t) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep S\<^sub>\<omega>)\<^sup>\<down>"
begin
  
abbreviation "Sh\<^sub>\<omega> \<equiv> sk_run.irun_h.Sw"
abbreviation "Eh\<^sub>\<omega> \<equiv> sk_run.irun_h.E\<^sub>\<omega>"
abbreviation "Rh\<^sub>\<omega> \<equiv> sk_run.irun_h.R\<^sub>\<omega>"
abbreviation Ehinf ("Eh\<^sub>\<infinity>") where "Ehinf \<equiv> (\<Union>i. sk_run.E\<^sub>h i)"
abbreviation Rhinf ("Rh\<^sub>\<infinity>") where "Rhinf \<equiv> (\<Union>i. sk_run.R\<^sub>h i)"

lemma sk_Sw:"sk.h\<^sub>R S\<^sub>\<omega> \<subseteq> Sh\<^sub>\<omega>"
proof-
  let ?E = "{(s \<cdot> \<sigma>, t \<cdot> \<sigma>) | s t \<sigma>. (s, t) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<and> s \<cdot> \<sigma> \<succ> t \<cdot> \<sigma>}"
  let ?Eh = "{(s \<cdot> \<sigma>, t \<cdot> \<sigma>) | s t \<sigma>. (s, t) \<in> Eh\<^sub>\<omega>\<^sup>\<leftrightarrow> \<and> s \<cdot> \<sigma> \<succ>\<^sub>s\<^sub>k t \<cdot> \<sigma>}"
  have "sk.h\<^sub>R ?E \<subseteq> ?Eh"
  proof
    fix u v ::"(('a, 'b) f_ext, 'b) term"
    assume "(u,v) \<in> sk.h\<^sub>R ?E"
    then obtain s t \<sigma> where st:"u = sk.h (s \<cdot> \<sigma>)" "v = sk.h (t \<cdot> \<sigma>)" "(s, t) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "s \<cdot> \<sigma> \<succ> t \<cdot> \<sigma>"
      by (smt Pair_inject mem_Collect_eq sk.inv_hR_rule)
    from st(3) sk_run.hEw sk.rule_h have mem:"(sk.h s, sk.h t) \<in> Eh\<^sub>\<omega>\<^sup>\<leftrightarrow>" by auto
    from st(4) have "sk.h (s \<cdot> \<sigma>) \<succ>\<^sub>s\<^sub>k sk.h (t \<cdot> \<sigma>)" using sk_run.compat_h by blast
    note facts = this mem st[unfolded sk.subst_apply_h]
    show "(u,v) \<in> ?Eh" unfolding mem_Collect_eq
      by (rule exI[of _ "sk.h s"], rule exI[of _ "sk.h t"], insert facts, auto)
  qed
  with sk_run.hRw show ?thesis unfolding Sw_def sk.hR_union sk_run.irun_h.Sw_def by auto
qed
  
lemma sk_run_fair: "\<forall>(s, t)\<in> sk_run.irun_h.PCP_ext (sk_run.irun_h.R\<^sub>\<omega> \<union> sk_run.irun_h.E\<^sub>\<omega>\<^sup>\<leftrightarrow>). (s, t) \<in> (rstep Eh\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep Sh\<^sub>\<omega>)\<^sup>\<down>"
proof
  fix s t
  assume pcp:"(s, t) \<in> sk_run.irun_h.PCP_ext (Rh\<^sub>\<omega> \<union> Eh\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
  note Sw_mono = rstep_mono[OF sk_Sw, THEN join_mono]
  from sk_run.PCP_h[unfolded sk_run.hRw sk_run.hEw, OF pcp]
    have "(sk.h_inv s, sk.h_inv t)\<in> PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" and id:"s = sk.h (sk.h_inv s) \<and> t = sk.h (sk.h_inv t)" by auto
  with fair have step:"(sk.h_inv s, sk.h_inv t) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep S\<^sub>\<omega>)\<^sup>\<down>" by auto
  note Estep = sk.rstep_h[of _ _ "E\<^sub>\<infinity>"]
  from rsteps_sk_h have "\<And>s t RR. (s, t) \<in> (rstep RR)\<^sup>\<down> \<Longrightarrow> (sk.h s, sk.h t) \<in> (rstep (sk.h\<^sub>R RR))\<^sup>\<down>"
    unfolding join_def by (metis joinE joinI join_def)
  hence join:"(sk.h_inv s, sk.h_inv t) \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down> \<Longrightarrow> (sk.h (sk.h_inv s), sk.h (sk.h_inv t)) \<in> (rstep Sh\<^sub>\<omega>)\<^sup>\<down>"
 using Sw_mono by blast
  from step have "(sk.h (sk.h_inv s), sk.h (sk.h_inv t)) \<in> (rstep (sk.h\<^sub>R E\<^sub>\<infinity>))\<^sup>\<leftrightarrow> \<union> (rstep Sh\<^sub>\<omega>)\<^sup>\<down>"
    unfolding Un_iff[of _ "(rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>" "(rstep S\<^sub>\<omega>)\<^sup>\<down>"] using Estep using join by auto
  with sk_run.hEinf have  "(sk.h (sk.h_inv s), sk.h (sk.h_inv t)) \<in> (rstep Eh\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep Sh\<^sub>\<omega>)\<^sup>\<down>" by auto 
  with id show "(s,t) \<in> (rstep Eh\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep Sh\<^sub>\<omega>)\<^sup>\<down>" by auto    
qed

lemma ground_RE_conv_S_conv:
  assumes "(s,t) \<in> (GROUND (rstep (Rh\<^sub>\<omega> \<union> Eh\<^sub>\<omega>)))\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(s,t) \<in> (GROUND (rstep Sh\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof(cases "s=t")
  case True
  then show ?thesis by auto
next
  case False
  have "\<And>Rel. GROUND (Rel\<^sup>\<leftrightarrow>) = (GROUND Rel)\<^sup>\<leftrightarrow>" unfolding GROUND_def by blast
  with assms[unfolded conversion_def] have c:"(s, t) \<in> (GROUND ((rstep (Rh\<^sub>\<omega> \<union> Eh\<^sub>\<omega>))\<^sup>\<leftrightarrow>))\<^sup>*" by metis
  from False GROUND_rtrancl[OF c]  GROUND_not_ground[OF c] have g:"ground s" "ground t"
    and conv:"(s,t) \<in> (rstep (Rh\<^sub>\<omega> \<union> Eh\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def by auto
  have E:"\<And>E. (rstep (Rh\<^sub>\<omega> \<union> E\<^sup>\<leftrightarrow>))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (Rh\<^sub>\<omega> \<union> E))\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def
    by (metis (no_types, lifting) rstep_simps(5) sup.right_idem sup_left_idem symcl_Un symcl_converse)
  note Sconv = sk_run.irun_h.gterms_ER_conv_implies_S_conv[OF sk_run.irun_h.Rw_less sk_run.irun_h.Rw_less g]
  with E conv show ?thesis unfolding sk_run.irun_h.Sw_def E_ord_def by blast
qed
  
context
  fixes \<R>::"('a,'b) trs"
  assumes R_less:"\<R> \<subseteq> {\<succ>}" and CR_R:"CR (rstep \<R>)"
  and conv_eq:"(rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*"
begin

lemma SN_R:"SN (rstep \<R>)" 
  by (rule SN_subset [OF SN_less], insert compatible_rstep_imp_less[OF R_less], auto)
 
lemma R_NF_eq:
  assumes "(s,t) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>"
  shows "\<exists>u. (s,u) \<in> (rstep \<R>)\<^sup>! \<and> (t,u) \<in> (rstep \<R>)\<^sup>!"
proof-
  from assms obtain i where "(s,t) \<in> (rstep (E i \<union> R i))\<^sup>\<leftrightarrow>\<^sup>*" by fast
  with oKBi_conversion_ERi conv_eq have "(s, t) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*" by fastforce
  with CR_imp_conversionIff_join[OF CR_R] obtain w where
    w:"(s, w) \<in> (rstep \<R>)\<^sup>*" "(t, w) \<in> (rstep \<R>)\<^sup>*" by auto
  from SN_reaches_NF[of "rstep \<R>"] SN_R have "\<exists>w'. (w, w') \<in> (rstep \<R>)\<^sup>* \<and> w' \<in> NF_trs \<R>"
    unfolding normalizability_def by (simp add: SN_defs)
  then obtain w' where "(w, w') \<in> (rstep \<R>)\<^sup>*" and nf:"w' \<in> NF_trs \<R>" by auto
  with w have seqs:"(s, w') \<in> (rstep \<R>)\<^sup>*" "(t, w') \<in> (rstep \<R>)\<^sup>*" by auto
  show ?thesis by (rule exI[of _ w'], unfold normalizability_def, insert seqs nf, auto)
qed

lemma sk_less_compat:"s \<succ> t \<Longrightarrow> sk s \<succ>\<^sub>s\<^sub>k sk t"
  using sk_run.compat_h sk_run.subst_h unfolding sk_def by auto

lemma ground_ctxt_less:
  assumes "ground s" and "ground t" and "C\<langle>s\<rangle> \<succ>\<^sub>s\<^sub>k C\<langle>t\<rangle>"
  shows "s \<succ>\<^sub>s\<^sub>k t"
proof-
  from assms sk_run.gtotal_h consider "s = t" | "s \<succ>\<^sub>s\<^sub>k t"  | "t \<succ>\<^sub>s\<^sub>k s" by auto
  then show ?thesis proof(cases)
    case 3
    with sk_run.okb_h.ctxt have "C\<langle>t\<rangle> \<succ>\<^sub>s\<^sub>k C\<langle>s\<rangle>" by auto
    from sk_run.okb_h.irrefl sk_run.okb_h.trans[OF assms(3) this] show ?thesis by auto
  qed (insert assms(3) sk_run.okb_h.irrefl, auto)
qed 

lemma ground_subt_less:
  assumes "ground s" and "s \<rhd> t"
  shows "s \<succ>\<^sub>s\<^sub>k t"
proof-
  from assms have gt:"ground t" "s \<noteq> t" by auto
  from assms obtain C where s:"s = C\<langle>t\<rangle>" by auto
  { assume "t \<succ>\<^sub>s\<^sub>k s"
    then have less:"t \<succ>\<^sub>s\<^sub>k C\<langle>t\<rangle>" unfolding s by auto
    { fix i
      have "(C ^ i)\<langle>t\<rangle> \<succ>\<^sub>s\<^sub>k (C ^ (Suc i))\<langle>t\<rangle>" using less sk_run.ctxt_h by (induct i, auto)
    }
    with less sk_run.SN_less_h[unfolded SN_on_def] have False by fast
  }
  with sk_run.gtotal_h assms(1) gt \<open>s \<noteq> t\<close> show ?thesis by auto
qed 

lemma Sw_steps_lesseq:"(s,t) \<in> (rstep S\<^sub>\<omega>)\<^sup>* \<Longrightarrow> s \<succeq> t"
  unfolding rtrancl_eq_or_trancl using compatible_rstep_trancl_imp_less[OF Sw_less] by auto

lemma ooverlap_exists:
  assumes "C\<langle>l\<^sub>1\<cdot>\<sigma>\<^sub>1\<rangle> = l\<^sub>2'\<cdot>\<sigma>\<^sub>2'" and "hole_pos C \<in> fun_poss l\<^sub>2'" and "(l\<^sub>1,r\<^sub>1) \<in> RR" and "(l\<^sub>2',r\<^sub>2') \<in> RR"
  and "\<not>(r\<^sub>1\<cdot>\<sigma>\<^sub>1 \<succ> l\<^sub>1\<cdot>\<sigma>\<^sub>1)" and "\<not>(r\<^sub>2'\<cdot>\<sigma>\<^sub>2' \<succ> l\<^sub>2'\<cdot>\<sigma>\<^sub>2')"
  shows "\<exists>r r' \<mu> \<tau> s t. ooverlap {\<succ>} RR r r' (hole_pos C) \<mu> s t \<and> C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = s \<cdot> \<tau> \<and>
                        r\<^sub>2' \<cdot> \<sigma>\<^sub>2' = t \<cdot> \<tau> \<and> l\<^sub>1\<cdot>\<sigma>\<^sub>1 = (fst r) \<cdot> \<mu> \<cdot> \<tau>"
proof-
  have rl1:"\<exists>p. p \<bullet> (l\<^sub>1, r\<^sub>1) \<in> RR" by (rule exI[of _ 0], insert assms(3), auto)
  from vars_rule_disjoint obtain \<pi>
    where \<pi>: "vars_rule (\<pi> \<bullet> (l\<^sub>2', r\<^sub>2')) \<inter> vars_rule (l\<^sub>1, r\<^sub>1) = {}" ..
  define l\<^sub>2 and r\<^sub>2 and \<sigma>\<^sub>2
    where "l\<^sub>2 = \<pi> \<bullet> l\<^sub>2'" and "r\<^sub>2 = \<pi> \<bullet> r\<^sub>2'" and "\<sigma>\<^sub>2 = (Var \<circ> Rep_perm (-\<pi>)) \<circ>\<^sub>s \<sigma>\<^sub>2'"
  note rename = l\<^sub>2_def r\<^sub>2_def \<sigma>\<^sub>2_def
  from assms(4) have "-\<pi> \<bullet> (l\<^sub>2,r\<^sub>2) \<in> RR" unfolding rename by auto
  then have rl2:"\<exists>p. p \<bullet> (l\<^sub>2,r\<^sub>2) \<in> RR" by (rule exI[of _ "-\<pi>"])
  from \<pi> have vars:"vars_rule (l\<^sub>1,r\<^sub>1) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}"
    unfolding rename rule_pt.permute_prod_eqvt by auto
  define p where "p \<equiv> hole_pos C" 
  from assms(2) have p:"p \<in> fun_poss l\<^sub>2" by (auto simp:rename p_def)
  note poss_p = fun_poss_imp_poss [OF p]
    
  have r_l1:"l\<^sub>2' = -\<pi> \<bullet> l\<^sub>2" by (auto simp:rename)
  from assms(1) have eq:"l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = (l\<^sub>2' \<cdot> \<sigma>\<^sub>2' |_ p)" unfolding p_def by (metis subt_at_hole_pos)
  note subt_l1 = subt_at_subst[OF poss_p]
  from eq[unfolded r_l1 permute_term_subst_apply_term] have
    eq':"l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = l\<^sub>2 |_ p \<cdot> \<sigma>\<^sub>2" 
    unfolding subt_at_subst[OF poss_p] unfolding rename
    by (metis \<open>l\<^sub>2 \<equiv> \<pi> \<bullet> l\<^sub>2'\<close> eq r_l1 subst.cop_add subt_l1 term_apply_subst_Var_Rep_perm)
      
  note coinc = coincidence_lemma' [of _ "vars_rule (l\<^sub>1, r\<^sub>1)"]
  define \<sigma> where "\<sigma> x = (if x \<in> vars_rule (l\<^sub>1, r\<^sub>1) then \<sigma>\<^sub>1 x else \<sigma>\<^sub>2 x)" for x
  have "l\<^sub>1 \<cdot> \<sigma> = l\<^sub>1 \<cdot> (\<sigma> |s vars_rule (l\<^sub>1, r\<^sub>1))"
    using coinc[of l\<^sub>1] by (simp add: vars_rule_def)
  also have "\<dots> = l\<^sub>1 \<cdot> (\<sigma>\<^sub>1 |s vars_rule (l\<^sub>1, r\<^sub>1))" by (simp add: \<sigma>_def [abs_def])
  finally have l1_coinc:"l\<^sub>1 \<cdot> \<sigma> = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using coinc[of l\<^sub>1] by (simp add: vars_rule_def)
  have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term l\<^sub>2 = {}"
    using \<pi>[unfolded rename] by (auto simp: vars_rule_def rule_pt.permute_prod_eqvt l\<^sub>2_def)
  have unif: "l\<^sub>1 \<cdot> \<sigma> = (l\<^sub>2 |_ p) \<cdot> \<sigma>"
  proof -
    from disj have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term (l\<^sub>2 |_ p) = {}" 
      using vars_term_subt_at [OF poss_p] by auto
    from l1_coinc have "l\<^sub>1 \<cdot> \<sigma> = (l\<^sub>2 |_ p) \<cdot> \<sigma>\<^sub>2" using eq' by simp
    also have "\<dots> = (l\<^sub>2 |_ p) \<cdot> (\<sigma>\<^sub>2 |s vars_term (l\<^sub>2 |_ p))"
      by (simp add: coincidence_lemma [symmetric])
    also have "\<dots> = (l\<^sub>2 |_ p) \<cdot> (\<sigma> |s vars_term (l\<^sub>2 |_ p))" using disj by (simp add: \<sigma>_def [abs_def])
    finally show ?thesis by (simp add: coincidence_lemma [symmetric])
  qed
    
  define \<mu> where "\<mu> = the_mgu l\<^sub>1 (l\<^sub>2 |_ p)"
  have is_mgu:"is_mgu \<mu> {(l\<^sub>1, l\<^sub>2 |_ p)}" by (rule is_mguI, insert unif the_mgu, auto simp: \<mu>_def)
  with unif obtain \<tau> where \<sigma>: "\<sigma> = \<mu> \<circ>\<^sub>s \<tau>" by (auto simp: is_mgu_def unifiers_def)
  from unif have mgu: "mgu l\<^sub>1 (l\<^sub>2 |_ p) = Some \<mu>"
    unfolding \<mu>_def the_mgu_def
    using unify_complete and unify_sound by (force split: option.splits simp: is_imgu_def mgu_def unifiers_def)
      
  have "r\<^sub>1 \<cdot> \<sigma> = r\<^sub>1 \<cdot> (\<sigma> |s vars_rule (l\<^sub>1, r\<^sub>1))" using coinc[of r\<^sub>1] by (simp add: vars_rule_def)
  also have "\<dots> = r\<^sub>1 \<cdot> (\<sigma>\<^sub>1 |s vars_rule (l\<^sub>1, r\<^sub>1))" by (simp add: \<sigma>_def [abs_def])
  finally have r1_coinc:"r\<^sub>1 \<cdot> \<sigma> = r\<^sub>1 \<cdot> \<sigma>\<^sub>1" using coinc[of r\<^sub>1] by (simp add: vars_rule_def)
  from assms(5) subst have nonoriented1:"\<not> r\<^sub>1 \<cdot> \<mu> \<succ> l\<^sub>1 \<cdot> \<mu>"
    unfolding l1_coinc[symmetric] r1_coinc[symmetric] \<sigma> by auto
      
  note coinc = coincidence_lemma [symmetric]
  have "l\<^sub>2 \<cdot> \<sigma> = l\<^sub>2 \<cdot> (\<sigma> |s vars_term l\<^sub>2)" by (simp add: coinc)
  also have "\<dots> = l\<^sub>2 \<cdot> (\<sigma>\<^sub>2 |s vars_term l\<^sub>2)" using disj by (simp add: \<sigma>_def [abs_def])
  also have "\<dots> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" by (simp add: coinc)
  finally have l2_coinc:"l\<^sub>2 \<cdot> \<sigma> = l\<^sub>2' \<cdot> \<sigma>\<^sub>2'" unfolding rename by simp
  have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term r\<^sub>2 = {}"
    using vars_term_subt_at [OF poss_p] and \<pi>[unfolded rename]
    by (auto simp: vars_rule_def rule_pt.permute_prod_eqvt r\<^sub>2_def)
  have "r\<^sub>2 \<cdot> \<sigma> = r\<^sub>2 \<cdot> (\<sigma> |s vars_term r\<^sub>2)" by (simp add: coinc)
  also have "\<dots> = r\<^sub>2 \<cdot> (\<sigma>\<^sub>2 |s vars_term r\<^sub>2)" using disj by (simp add: \<sigma>_def [abs_def])
  also have "\<dots> = r\<^sub>2 \<cdot> \<sigma>\<^sub>2" by (simp add: coinc)
  finally have r2_coinc:"r\<^sub>2 \<cdot> \<sigma> = r\<^sub>2' \<cdot> \<sigma>\<^sub>2'" unfolding rename by simp
  from assms(6) subst have nonoriented2:"\<not> r\<^sub>2 \<cdot> \<mu> \<succ> l\<^sub>2 \<cdot> \<mu>"
    unfolding l2_coinc[symmetric] r2_coinc[symmetric] \<sigma> by auto
  from assms(1) poss_p hole_pos_id_ctxt have "C = ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<sigma>)"
    unfolding l1_coinc[symmetric] l2_coinc[symmetric] p_def by metis  
  then have cp_left:"C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = (ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<mu>))\<langle>r\<^sub>1 \<cdot> \<mu>\<rangle> \<cdot> \<tau>"
    unfolding subst_apply_term_ctxt_apply_distrib r1_coinc[symmetric]
      ctxt_of_pos_term_subst[OF poss_imp_subst_poss[OF poss_p], symmetric]
      subst_subst_compose[symmetric] \<sigma>[symmetric] by simp
  from subst_subst_compose have cp_right:"r\<^sub>2' \<cdot> \<sigma>\<^sub>2' = r\<^sub>2 \<cdot> \<mu> \<cdot> \<tau>" unfolding r2_coinc[symmetric] \<sigma> by auto
  let ?s = "(ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<mu>))\<langle>r\<^sub>1 \<cdot> \<mu>\<rangle>"
  let ?t = "r\<^sub>2 \<cdot> \<mu>"
  from l1_coinc \<sigma> have "l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = l\<^sub>1 \<cdot> \<mu> \<cdot> \<tau>" by auto
  note facts = rl1 rl2 vars p mgu nonoriented1 nonoriented2 cp_left cp_right this
  show ?thesis unfolding ooverlap_def
    by (rule exI[of _ "(l\<^sub>1,r\<^sub>1)"], rule exI[of _ "(l\<^sub>2,r\<^sub>2)"], rule exI[of _ \<mu>],
        rule exI[of _ \<tau>], rule exI[of _ ?s], rule exI[of _ ?t], insert facts,
        unfold fst_conv snd_conv p_def, auto)
qed

lemma less_imp_less_sk:"s \<succ> t \<Longrightarrow> sk s \<succ>\<^sub>s\<^sub>k sk t"
  using less_sk[unfolded sk_redord_def] unfolding sk_def by meson

lemma correctness_okb_sk:"GCR (rstep Sh\<^sub>\<omega>) \<and> (rstep (sk_run.E\<^sub>h 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (Rh\<^sub>\<omega> \<union> Eh\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
  using sk_run.irun_h.correctness_okb[OF] sk_run_fair by fast

abbreviation S_sk_inf ("\<S>\<^sub>s\<^sub>k\<^sup>\<infinity>") where "\<S>\<^sub>s\<^sub>k\<^sup>\<infinity> \<equiv> sk_run.irun_h.Rinf \<union> E_ord (\<succ>\<^sub>s\<^sub>k) sk_run.irun_h.Einf"

lemma S_sk_inf:
  assumes "(l,r) \<in> \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>"
  shows "\<exists>l' r' \<tau>. l = (sk.h l') \<cdot> \<tau> \<and> r = (sk.h r') \<cdot> \<tau> \<and> (l',r') \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow> \<union> R\<^sub>\<infinity> \<and> sk.h l' \<cdot> \<tau> \<succ>\<^sub>s\<^sub>k sk.h r' \<cdot> \<tau>"
proof-
  from assms consider "(l,r) \<in> sk_run.irun_h.Rinf" | "(l,r) \<in> E_ord (\<succ>\<^sub>s\<^sub>k) sk_run.irun_h.Einf" by auto
  then show ?thesis proof(cases)
    case 1
    then obtain i where lr:"(l, r) \<in> sk.h\<^sub>R (R i)" by auto
    with sk_run.irun_h.Ri_less have "l \<succ>\<^sub>s\<^sub>k r" by auto
    note rule = sk.inv_hR_rule[OF lr] this
    show ?thesis by (rule exI[of _ "sk.h_inv l"], rule exI[of _ "sk.h_inv r"], rule exI[of _ Var], insert rule, auto)
  next
    case 2
    then obtain l' r' \<tau> where lr:"l = l' \<cdot> \<tau>" "r = r' \<cdot> \<tau>" "l' \<cdot> \<tau> \<succ>\<^sub>s\<^sub>k r' \<cdot> \<tau>" "(l', r') \<in> sk_run.irun_h.Einf\<^sup>\<leftrightarrow>"
      unfolding E_ord_def mem_Collect_eq by blast
    then obtain i where lr':"(l', r') \<in> (sk.h\<^sub>R (E i))\<^sup>\<leftrightarrow>" unfolding E_ord_def by auto
    let ?l = "sk.h_inv l'" and ?r = "sk.h_inv r'"
    note sk_E = sk.inv_hR_rule[of l' r' "E i"] sk.inv_hR_rule[of r' l' "E i"] lr'
    then have "(?l, ?r) \<in> (E i)\<^sup>\<leftrightarrow> \<and> l' = (sk.h ?l) \<and> r' = (sk.h ?r)" unfolding Un_iff converse_iff by fastforce
    then have inE:"(?l, ?r) \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" and lr':"(sk.h ?l) = l'" "(sk.h ?r) = r'" by auto
    show ?thesis by (rule exI[of _ ?l], rule exI[of _ "?r"], rule exI[of _ \<tau>], insert inE lr(3), unfold lr lr', simp)
  qed
qed

lemma peak_cases:
  assumes step:"(s,t) \<in> rstep_r_p_s (E\<^sub>\<omega>\<^sup>\<leftrightarrow>) (l,r) [] \<sigma>" and irstep:"(t,u) \<in> irstep False S\<^sub>\<omega>"
    and "\<not>(l\<cdot>\<sigma> \<succ> r\<cdot>\<sigma>)"
  shows "s \<notin> NF_trs S\<^sub>\<omega> \<or> (\<exists>w. (s,w) \<in> (rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>))\<^sup>= \<and> u \<succeq> w)" (is "?A \<or> ?B")
proof-
  from step have lr:"(l,r) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "s = l\<cdot>\<sigma>" "t = r\<cdot>\<sigma>" unfolding rstep_r_p_s_def by auto
  from irstep[unfolded irstep_def, THEN qrstepE'] obtain D l\<^sub>2 r\<^sub>2 \<sigma>\<^sub>2 where
    lr2:"(l\<^sub>2,r\<^sub>2) \<in> S\<^sub>\<omega>" "t = D\<langle>l\<^sub>2\<cdot>\<sigma>\<^sub>2\<rangle>" "u = D\<langle>r\<^sub>2\<cdot>\<sigma>\<^sub>2\<rangle>" "\<forall>u\<lhd>l\<^sub>2 \<cdot> \<sigma>\<^sub>2. u \<in> NF_terms (lhss S\<^sub>\<omega>)" by blast 
  let ?p = "hole_pos D"
    (* do a CP Lemma-like analysis (standard CP lemma requires variable condition) *)
  show ?thesis proof(cases "?p \<in> fun_poss r")
    case False (* variable overlap *)
    note hole_D_not_in_fun_poss_r = this
    from lr(3) lr2(2) have p_r\<sigma>:"?p \<in> poss (r \<cdot> \<sigma>)" by fastforce
    from poss_subst_apply_term[OF this hole_D_not_in_fun_poss_r] obtain q\<^sub>1 q\<^sub>2 x
      where p[simp]: "?p = q\<^sub>1 @ q\<^sub>2" and q\<^sub>1: "q\<^sub>1 \<in> poss r"
        and rq\<^sub>1: "r |_ q\<^sub>1 = Var x" and q\<^sub>2: "q\<^sub>2 \<in> poss (\<sigma> x)" by auto
    note eq = lr(3)[unfolded lr2(2), simplified]
    then have [simp]: "r \<cdot> \<sigma> |_ ?p = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using subt_at_hole_pos by metis
    with rq\<^sub>1 q\<^sub>2 subt_at_append p_r\<sigma> q\<^sub>1 have [simp]: "\<sigma> x |_ q\<^sub>2 = l\<^sub>2 \<cdot>\<sigma>\<^sub>2" unfolding p by auto
    define \<sigma>' where "\<sigma>' y = (if y = x then replace_at (\<sigma> x) q\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2) else \<sigma> y)" for y
    have "(\<sigma> x, \<sigma>' x) \<in> rstep S\<^sub>\<omega>"
    proof -
      let ?C = "ctxt_of_pos_term q\<^sub>2 (\<sigma> x)"
      have "(?C\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>, ?C\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>) \<in> rstep S\<^sub>\<omega>" using lr2 by blast
      then show ?thesis using q\<^sub>2 by (simp add: \<sigma>'_def replace_at_ident)
    qed
    then have *: "\<And>x. (\<sigma> x, \<sigma>' x) \<in> (rstep S\<^sub>\<omega>)\<^sup>*" by (auto simp: \<sigma>'_def)
    then have left:"(l \<cdot> \<sigma>, l \<cdot> \<sigma>') \<in> (rstep S\<^sub>\<omega>)\<^sup>*" by (rule substs_rsteps)
    moreover
    have right:"(u, r \<cdot> \<sigma>') \<in> (rstep S\<^sub>\<omega>)\<^sup>*"
    proof -
      have "replace_at (r \<cdot> \<sigma>) ?p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2) = replace_at (r \<cdot> \<sigma>) q\<^sub>1 (\<sigma>' x)"
        using q\<^sub>1 and q\<^sub>2 by (simp add: \<sigma>'_def ctxt_of_pos_term_append rq\<^sub>1)
      moreover
      have "(replace_at (r \<cdot> \<sigma>) q\<^sub>1 (\<sigma>' x), r \<cdot> \<sigma>') \<in> (rstep S\<^sub>\<omega>)\<^sup>*"
        by (rule replace_at_subst_rsteps [OF * q\<^sub>1 rq\<^sub>1])
      ultimately
      have "(replace_at (r \<cdot> \<sigma>) ?p (r\<^sub>2 \<cdot> \<sigma>\<^sub>2), r \<cdot> \<sigma>') \<in> (rstep S\<^sub>\<omega>)\<^sup>*" by auto
      then show ?thesis unfolding lr2(3) unfolding eq[symmetric] ctxt_of_pos_term_hole_pos
        by blast 
    qed
    from lr(1) in_mono[OF Ew_subset_Einf] have E_step:"(l \<cdot> \<sigma>', r \<cdot> \<sigma>') \<in> rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" by fast
    from left right Sw_steps_lesseq have leq:"u \<succeq> r \<cdot> \<sigma>'" unfolding lr(2) by simp
    show ?thesis proof(cases "l \<cdot> \<sigma> = l \<cdot> \<sigma>'")
      case True
      have "?B" unfolding True lr(2) by (rule exI[of _ "r \<cdot> \<sigma>'"], insert E_step leq, auto)
      then show ?thesis by auto
    next
      case False
      with left[unfolded rtrancl_eq_or_trancl trancl_unfold_left] show ?thesis
        unfolding lr(2) by auto
    qed
  next
    case True (* proper overlap *)
    from lr lr2 have eq:"D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = r \<cdot> \<sigma>" by auto
    note st = lr[unfolded intp_actxt.simps]
    note tu = lr2[unfolded intp_actxt.simps]
    note rl_cases = lr2(1)[unfolded Sw_def Un_iff[of _ "R\<^sub>\<omega>"]]
    have "\<exists>\<tau> l\<^sub>3 r\<^sub>3. l\<^sub>2 = l\<^sub>3\<cdot>\<tau> \<and> r\<^sub>2 = r\<^sub>3\<cdot>\<tau> \<and> (l\<^sub>3, r\<^sub>3) \<in> R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>"
      by (cases "(l\<^sub>2, r\<^sub>2) \<in> R\<^sub>\<omega>", rule exI[of _ Var], insert rl_cases, auto)
    then obtain \<tau> l\<^sub>3 r\<^sub>3 where lr3:"l\<^sub>2 = l\<^sub>3\<cdot>\<tau>" "r\<^sub>2 = r\<^sub>3\<cdot>\<tau>" "(l\<^sub>3, r\<^sub>3) \<in> R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" by auto
    from eq[unfolded this] subst_subst have eq':"D\<langle>l\<^sub>3 \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>\<^sub>2)\<rangle> = r \<cdot> \<sigma>" by auto
    from lr(1) have rl0:"(r,l) \<in> R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" by auto
    from lr2(1) Sw_less have "l\<^sub>3 \<cdot> \<tau> \<succ> r\<^sub>3 \<cdot> \<tau>" unfolding lr3 by auto
    from subst[OF this] trans irrefl have unoriented':"\<not> r\<^sub>3 \<cdot> \<tau> \<circ>\<^sub>s \<sigma>\<^sub>2 \<succ> l\<^sub>3 \<cdot> \<tau> \<circ>\<^sub>s \<sigma>\<^sub>2"
      unfolding subst_subst[symmetric] by fast

    note ooverlap = ooverlap_exists[OF eq' True lr3(3) rl0 unoriented' assms(3)]
    then have ooverlap:"\<exists>r r' \<mu> \<tau> s t. ooverlap {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) r r' (hole_pos D) \<mu> s t \<and>
               D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = s \<cdot> \<tau> \<and> l \<cdot> \<sigma> = t \<cdot> \<tau> \<and> l\<^sub>2 \<cdot> \<sigma>\<^sub>2 = (fst r) \<cdot> \<mu> \<cdot> \<tau>" unfolding lr3 by auto
    then obtain rl\<^sub>1 rl\<^sub>2 \<mu> \<tau> s\<^sub>0 t\<^sub>0 where
      ooverlap:"ooverlap {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) rl\<^sub>1 rl\<^sub>2 (hole_pos D) \<mu> s\<^sub>0 t\<^sub>0"
      and dec:"D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = s\<^sub>0 \<cdot> \<tau>" "l \<cdot> \<sigma> = t\<^sub>0 \<cdot> \<tau>" "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 = (fst rl\<^sub>1) \<cdot> \<mu> \<cdot> \<tau>" by auto
    { fix u
      assume "u \<lhd> fst rl\<^sub>1 \<cdot> \<mu>"
      then have  "u \<cdot> \<tau> \<lhd> fst rl\<^sub>1 \<cdot> \<mu> \<cdot> \<tau>" by auto
      with lr2(4)[unfolded dec] have nf:"u \<in> NF_trs S\<^sub>\<omega>" unfolding NF_terms_lhss by fast
      have "\<And>s t. (s,t) \<in> ordstep {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) \<Longrightarrow> (s,t) \<in> rstep S\<^sub>\<omega>"
        unfolding Sw_def rstep_union ordstep.simps by blast
      from nf NF_anti_mono[OF subrelI[OF this]] have "u \<in> NF (ordstep {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))"
        by blast
    }
    then have prime:"(\<forall>u\<lhd>fst rl\<^sub>1 \<cdot> \<mu>. u \<in> NF (ordstep {\<succ>} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)))" by auto

    with ooverlap have "(s\<^sub>0, t\<^sub>0) \<in> PCP_ext (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" unfolding PCP_ext_def mem_Collect_eq
      by blast
    with fair have alt:"(s\<^sub>0, t\<^sub>0) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<or> (s\<^sub>0, t\<^sub>0) \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down>" by auto
    { assume "(s\<^sub>0, t\<^sub>0) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>"
      with dec have "(D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>, l \<cdot> \<sigma>) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>" by auto
      with lr(2) lr2(3) have Einf_step:"(s, u) \<in> rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" by (auto simp: rstep_simps)
    } note E = this
    { assume "(s\<^sub>0, t\<^sub>0) \<in> (rstep S\<^sub>\<omega>)\<^sup>\<down>"
      then obtain v where v:"(s\<^sub>0, v) \<in> (rstep S\<^sub>\<omega>)\<^sup>*" "(t\<^sub>0, v) \<in> (rstep S\<^sub>\<omega>)\<^sup>*" using joinD by auto
      note su = lr(2)[unfolded dec] tu(3)[unfolded dec]
      have "s \<notin> NF_trs S\<^sub>\<omega> \<or> (\<exists>w. (s, w) \<in> (rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>))\<^sup>= \<and> u \<succeq> w)" proof(cases "t\<^sub>0 = v")
        case True
        from v(1) Sw_steps_lesseq subst[of s\<^sub>0] have ge:"s\<^sub>0 \<cdot> \<tau> \<succeq> v \<cdot> \<tau>" by auto
        have "\<exists>w. (s, w) \<in> (rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>))\<^sup>= \<and> u \<succeq> w"
          by (rule exI[of _ "v \<cdot> \<tau>"], unfold su True, insert ge, auto)
        then show ?thesis by auto
      next
        case False
        with v(2)[unfolded rtrancl_eq_or_trancl] have "s \<notin> NF_trs S\<^sub>\<omega>" unfolding su
          by (meson NF_instance NF_no_trancl_step)
        thus ?thesis by auto
      qed
    }
    with alt E show ?thesis by auto
  qed
qed

lemma REinf_step_Sinf_step:
  assumes  "sk s \<succ>\<^sub>s\<^sub>k sk t" and "(s, t) \<in> rstep (R\<^sub>\<infinity> \<union> (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>))"
  shows "(sk s, sk t) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>"
proof(cases "(s, t) \<in> rstep(E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)")
  case True
  from rstep_imp_rstep_sk[OF this] sk_run.hEinf have "(sk s, sk t) \<in> rstep (Eh\<^sub>\<infinity>\<^sup>\<leftrightarrow>)"
    unfolding sk.hR_sym by auto
  then obtain l r \<sigma> D where *:"sk s = D\<langle>l\<cdot>\<sigma>\<rangle>" "sk t = D\<langle>r\<cdot>\<sigma>\<rangle>" "(l,r) \<in> Eh\<^sub>\<infinity>\<^sup>\<leftrightarrow>" by fast
  note g = ground_sk[of s, unfolded * ground_ctxt_apply] ground_sk[of t, unfolded * ground_ctxt_apply]
  with ground_ctxt_less assms(1) have "l\<cdot>\<sigma> \<succ>\<^sub>s\<^sub>k r\<cdot>\<sigma>" unfolding * by fast
  with * have "(l\<cdot>\<sigma>, r\<cdot>\<sigma>) \<in> E_ord (\<succ>\<^sub>s\<^sub>k) Eh\<^sub>\<infinity>" unfolding E_ord_def by fast
  then show ?thesis unfolding * by auto
next
  case False
  with assms have "(s, t) \<in> rstep R\<^sub>\<infinity>" unfolding rstep_union by auto
  from rstep_imp_rstep_sk[OF this] sk_run.hRinf have "(sk s, sk t) \<in> rstep Rh\<^sub>\<infinity>" by auto
  then show ?thesis unfolding rstep_union by auto
qed

lemma sk_step_exists':
  assumes "(sk t, u) \<in> rstep ((sk.h\<^sub>R \<R>) :: (('a,'b) f_ext, 'b) trs)"
  shows "\<exists>u'. (sk t, sk u') \<in> rstep (sk.h\<^sub>R \<R>)"
proof-
  from assms obtain l r D \<tau> where lr:"(l,r) \<in> sk.h\<^sub>R \<R>" and sk_t:"sk t = D\<langle>l\<cdot>\<tau>\<rangle>" "u = D\<langle>r\<cdot>\<tau>\<rangle>" by fast
  with sk.inv_hR_rule have **:"l = sk.h (sk.h_inv l)" "r = sk.h (sk.h_inv r)" "(sk.h_inv l,sk.h_inv r) \<in> \<R>" by metis+
  let ?l = "sk.h_inv l" and ?r = "sk.h_inv r"
  from sk_C[OF sk_t(1)] have p:"hole_pos D \<in> poss t" and sk_subt:"sk (t |_ hole_pos D) = l \<cdot> \<tau>" by auto
  let ?t = "t |_ hole_pos D"
  from sk_subt ** have 1:"sk ?t =  (sk.h ?l) \<cdot> \<tau>" by auto
  from SN_imp_variable_condition[OF SN_R] have "(\<And>l r. (l, r) \<in> sk.h\<^sub>R \<R> \<Longrightarrow> vars_term r \<subseteq> vars_term l)"
    by (metis case_prodD sk.h_def sk.inv_hR_rule vars_term_map_funs_term2)
  with rstep_ground[OF _ ground_sk assms] have "ground u" by auto
  then have 3:"ground (r \<cdot> \<tau>)" using sk_t **  by simp
  from ** R_less have "?l \<succ> ?r" by auto
  from sk_run.compat_h[OF this] sk_run.subst_h have 2:"l \<cdot> \<tau> \<succ>\<^sub>s\<^sub>k r \<cdot> \<tau>" unfolding **[symmetric] by auto
  from sk_clean_step[OF 1, unfolded **[symmetric], OF 2 _ _ 3, of ?l ?r] ** obtain u' \<tau>' where
    c:"l \<cdot> \<tau> = l \<cdot> \<tau>'" "r \<cdot> \<tau>' = sk u'" "l \<cdot> \<tau>' \<succ>\<^sub>s\<^sub>k r \<cdot> \<tau>'" by fastforce
  then have t':"sk t = D\<langle>sk.h ?l \<cdot> \<tau>'\<rangle>" using sk_t ** by auto
  from lr c(3) have "(l \<cdot> \<tau>',r \<cdot> \<tau>') \<in> rstep (sk.h\<^sub>R \<R>)" unfolding **[symmetric] by blast
  then have step:"(sk (t |_ hole_pos D), sk u') \<in> rstep (sk.h\<^sub>R \<R>)" using sk_subt ** c by auto
  from sk_ctxt_exists[OF sk_t(1)] obtain C v where Cv:"D = (sk.h\<^sub>C C) \<cdot>\<^sub>c \<sigma>\<^sub>s\<^sub>k" "l \<cdot> \<tau> = sk v" by auto
  from step have "(D\<langle>sk (t |_ hole_pos D)\<rangle>, D\<langle>sk u'\<rangle>) \<in> rstep (sk.h\<^sub>R \<R>)" by auto
  then have "(sk t, ((sk.h\<^sub>C C) \<cdot>\<^sub>c \<sigma>\<^sub>s\<^sub>k)\<langle>sk u'\<rangle>) \<in> rstep (sk.h\<^sub>R \<R>)" unfolding sk_subt sk_t using Cv by auto
  then have "(sk t, sk C\<langle>u'\<rangle>) \<in> rstep (sk.h\<^sub>R \<R>)"
    unfolding sk_def subst_apply_term_ctxt_apply_distrib sk.ctxt_apply_h' by auto
  then show ?thesis by auto
qed

lemma sk_step_exists:
  assumes "(sk t, u) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>"
  shows "\<exists>u'. (sk t, sk u') \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>"
proof-
  from assms obtain l r D \<tau> where lr:"(l,r) \<in> \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" and sk_t:"sk t = D\<langle>l\<cdot>\<tau>\<rangle>" "u = D\<langle>r\<cdot>\<tau>\<rangle>" by fast
  from S_sk_inf[OF this(1)] obtain l' r' \<mu> where
    **:"l = (sk.h l') \<cdot> \<mu>" "r = (sk.h r') \<cdot> \<mu>" "(l',r') \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow> \<union> R\<^sub>\<infinity>" "sk.h l' \<cdot> \<mu> \<succ>\<^sub>s\<^sub>k sk.h r' \<cdot> \<mu>" by fast+
  from sk_C[OF sk_t(1)] have p:"hole_pos D \<in> poss t" and sk_subt:"sk (t |_ hole_pos D) = l \<cdot> \<tau>" by auto
  let ?t = "t |_ hole_pos D"
  from sk_subt ** have 1:"sk ?t =  (sk.h l') \<cdot> (\<mu> \<circ>\<^sub>s \<tau>)" by auto
  from **(4) sk_run.subst_h have 2:"sk.h l' \<cdot> (\<mu> \<circ>\<^sub>s \<tau>) \<succ>\<^sub>s\<^sub>k sk.h r' \<cdot> (\<mu> \<circ>\<^sub>s \<tau>)" by auto
  from rstep_ground[OF _ ground_sk assms] SN_imp_variable_condition[OF SN_Sinf] have "ground u"
    by (metis SN_imp_variable_condition case_prod_conv sk_run.irun_h.SN_Sinf)
  then have 3:"ground (sk.h r' \<cdot> \<mu> \<circ>\<^sub>s \<tau>)" unfolding sk_t ** subst_subst_compose by simp
  from sk_clean_step[OF 1 2 _ _ 3] subst_subst_compose obtain u' \<tau>' where
    c:"sk.h l' \<cdot> \<mu> \<cdot> \<tau> = sk.h l' \<cdot> \<tau>'" "sk u' = sk.h r' \<cdot> \<tau>'" "sk.h l' \<cdot> \<tau>' \<succ>\<^sub>s\<^sub>k sk.h r' \<cdot> \<tau>'" by fastforce
  then have t':"sk t = D\<langle>sk.h l' \<cdot> \<tau>'\<rangle>" using sk_t ** by auto
  have "(sk.h l' \<cdot> \<tau>', sk.h r' \<cdot> \<tau>') \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" proof(cases "(l',r') \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>")
    case True
    then have "(sk.h l',sk.h r') \<in> Eh\<^sub>\<infinity>\<^sup>\<leftrightarrow>" using sk.rule_h sk_run.hEinf by auto
    with c(3) have "(sk.h l' \<cdot> \<tau>',sk.h r' \<cdot> \<tau>') \<in> E_ord (\<succ>\<^sub>s\<^sub>k) Eh\<^sub>\<infinity>"
      unfolding E_ord_def mem_Collect_eq by blast
    then show ?thesis by auto
  next
    case False
    then have "(l',r') \<in> R\<^sub>\<infinity>" using **(3) by auto
    then have "(sk.h l',sk.h r') \<in> Rh\<^sub>\<infinity>" using sk.rule_h sk_run.hEinf by auto
    then show ?thesis by auto
  qed
  then have step:"(sk (t |_ hole_pos D), sk u') \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" unfolding sk_subt ** c by auto
  from sk_ctxt_exists[OF sk_t(1)] obtain C v where Cv:"D = (sk.h\<^sub>C C) \<cdot>\<^sub>c \<sigma>\<^sub>s\<^sub>k" "l \<cdot> \<tau> = sk v" by auto
  from step have "(D\<langle>sk (t |_ hole_pos D)\<rangle>, D\<langle>sk u'\<rangle>) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" by auto
  then have "(sk t, ((sk.h\<^sub>C C) \<cdot>\<^sub>c \<sigma>\<^sub>s\<^sub>k)\<langle>sk u'\<rangle>) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" unfolding sk_subt sk_t using Cv by auto
  then have "(sk t, sk C\<langle>u'\<rangle>) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>"
    unfolding sk_def subst_apply_term_ctxt_apply_distrib sk.ctxt_apply_h' by auto
  then show ?thesis by auto
qed

lemma hR_less_sk: "sk.h\<^sub>R \<R> \<subseteq> {\<succ>\<^sub>s\<^sub>k}"
proof
  fix l r :: "(('a, 'b) f_ext, 'b) term"
  assume "(l, r) \<in> sk.h\<^sub>R \<R>"
  with sk.inv_hR_rule have **:"l = sk.h (sk.h_inv l)" "r = sk.h (sk.h_inv r)" "(sk.h_inv l,sk.h_inv r) \<in> \<R>" by metis+
  with R_less have "sk.h_inv l \<succ> sk.h_inv r" by auto
  with sk_run.compat_h[of "sk.h_inv l" "sk.h_inv r"] ** show "(l,r) \<in> {\<succ>\<^sub>s\<^sub>k}" by auto
qed

lemma NF_S_NF_R:
  assumes "sk t \<in> NF_trs Sh\<^sub>\<omega>"
  shows "sk t \<in> NF_trs (sk.h\<^sub>R \<R>)"
proof-
  { fix u :: "(('a, 'b) f_ext, 'b) term"
    assume step:"(sk t, u) \<in> rstep (sk.h\<^sub>R \<R>)"
    from sk_step_exists'[OF step] obtain v where v:"(sk t, sk v) \<in> rstep (sk.h\<^sub>R \<R>)" by auto
    with sk_run.irun_h.rstep_subset_less[OF hR_less_sk] have less:"sk t \<succ>\<^sub>s\<^sub>k sk v" by auto
    note acyclic = SN_subset[OF sk_run.SN_less_h sk_run.irun_h.rstep_subset_less[OF hR_less_sk],THEN SN_imp_acyclic]
    with r_into_trancl'[OF v] sk_inj have "t \<noteq> v" unfolding acyclic_def by auto
    with rstep_sk_imp_rstep[OF v] have "(t, v) \<in> rstep \<R>" by auto
    with conv_eq oKBi_conversion_ERw have "(t, v) \<in> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto

    with rsteps_sk have "(sk t, sk v) \<in> (rstep (sk.h\<^sub>R ((R\<^sub>\<omega> \<union> E\<^sub>\<omega>)\<^sup>\<leftrightarrow>)))\<^sup>*"
      unfolding conversion_def rstep_simps(5)[symmetric] by auto
    with sk_run.hRw sk_run.hEw have "(sk t, sk v) \<in> (rstep (Rh\<^sub>\<omega> \<union> Eh\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
      unfolding conversion_def sk.hR_sym using sk.hR_union rstep_simps(5) by metis
    note conv_ground = gterm_conv_GROUND_conv[OF ground_sk ground_sk this]
    with ground_RE_conv_S_conv have gconv:"(sk t, sk v) \<in> (GROUND (rstep Sh\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by simp
    from sk_run.irun_h.correctness_okb sk_run_fair have "GCR (rstep Sh\<^sub>\<omega>)" by fast
    with gconv CR_imp_conversionIff_join
    obtain w where w:"(sk t,w) \<in> (GROUND (rstep Sh\<^sub>\<omega>))\<^sup>*" "(sk v,w) \<in> (GROUND (rstep Sh\<^sub>\<omega>))\<^sup>*" by blast
    then have v:"(sk t,w) \<in> (rstep Sh\<^sub>\<omega>)\<^sup>*" "(sk v,w) \<in> (rstep Sh\<^sub>\<omega>)\<^sup>*" using rtrancl_mono[OF GROUND_subset]
      by auto
    note compat = sk_run.okb_h.compatible_rstep_trancl_imp_less[OF sk_run.irun_h.Sw_less]
    with v(2)[unfolded rtrancl_eq_or_trancl] have geq:"sk v \<succeq>\<^sub>s\<^sub>k w" by auto
    from less sk_run.trans_h geq have "w \<noteq> sk t" using sk_run.okb_h.irrefl by auto
    with v(1)[unfolded rtrancl_eq_or_trancl] have "\<exists>s. (sk t, s) \<in> rstep Sh\<^sub>\<omega>"
      unfolding trancl_unfold_left by auto
  }
  with assms show ?thesis by blast
qed

lemma sk_Swinf_step_imp_no_Sinf_NF:
  assumes "(sk s, sk t) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>"
  shows "s \<notin> NF_trs (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)"
  using assms
proof(induct "sk t" arbitrary:s t rule: SN_induct [OF sk_run.SN_less_h])
  case 1
  note ind_step = this
  then obtain l r C \<sigma> where lr:"(l,r) \<in> \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" and st:"sk s = C\<langle>l\<cdot>\<sigma>\<rangle>" "sk t = C\<langle>r\<cdot>\<sigma>\<rangle>" by fast
  from S_sk_inf[OF this(1)] obtain l' r' \<tau> where
    *:"l = (sk.h l') \<cdot> \<tau>" "r = (sk.h r') \<cdot> \<tau>" "(l',r') \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow> \<union> R\<^sub>\<infinity>" "sk.h l' \<cdot> \<tau> \<succ>\<^sub>s\<^sub>k sk.h r' \<cdot> \<tau>" by fast+
  note ordstep = sk_run.okb_h.ordstep_S_conv[OF sk_run.irun_h.Rinf_less]
    ordstep_imp_ord[OF sk_run.okb_h.ctxt_closed_less]
  from 1 ordstep have sk_less:"sk s \<succ>\<^sub>s\<^sub>k sk t" by blast
  let ?\<sigma> = "\<tau> \<circ>\<^sub>s \<sigma>" and ?l = "sk.h l'" and ?r = "sk.h r'"
  from * st have st:"sk s = C\<langle>?l\<cdot>?\<sigma>\<rangle>" "sk t = C\<langle>?r\<cdot>?\<sigma>\<rangle>" by auto
  show ?case proof(cases C)
    case Hole
    define \<rho> where "\<rho> \<equiv> deskolemize \<circ> (\<tau> \<circ>\<^sub>s \<sigma>)"
    note sk_t = st(2)[unfolded Hole intp_actxt.simps]
    from st deskolemize_s have s:"s = l' \<cdot> \<rho>" and t:"t = r' \<cdot> \<rho>" unfolding Hole \<rho>_def by auto
    from sk_deskolemize_subst_vars[OF sk_t] have sk_vs:"\<forall>x\<in>vars_term r'. ?\<sigma> x = sk (deskolemize (?\<sigma> x))"
      unfolding Hole \<rho>_def by auto
    show ?thesis proof (cases "l'\<cdot> \<rho> \<succ> r'\<cdot> \<rho>")
      case True
      from * consider "(l',r') \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" | "(l',r') \<in> R\<^sub>\<infinity>" by auto
      then show ?thesis proof(cases)
        case 1
        have "(l'\<cdot> \<rho>,r'\<cdot> \<rho>) \<in> (E_ord (\<succ>) E\<^sub>\<infinity>)" unfolding E_ord_def mem_Collect_eq
          by (rule exI[of _ l'], rule exI[of _ r'], rule exI[of _ \<rho>], insert True 1, auto)
        then show ?thesis unfolding s by auto
      next
        case 2
        then show ?thesis unfolding s by fast
      qed
    next
      case False
      note unoriented = this
      with *(3) subst Rinf_less have lr':"(l', r') \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>" by fast
      show ?thesis proof (cases "(l', r') \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>")
        case True
        show ?thesis proof(cases "sk t \<in> NF_trs \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>")
          case True
          with sk_run.irun_h.NF_Sw_NF_Sinf have "sk t \<in> NF_trs Sh\<^sub>\<omega>" by auto
          with NF_S_NF_R have nf:"sk t \<in> NF_trs (sk.h\<^sub>R \<R>)" by auto
          from lr' R_NF_eq[of s t] have "\<exists>u. (s, u) \<in> (rstep \<R>)\<^sup>! \<and> (t, u) \<in> (rstep \<R>)\<^sup>!"
            unfolding s t by fast
          then obtain u where "(s, u) \<in> (rstep \<R>)\<^sup>! \<and> (t, u) \<in> (rstep \<R>)\<^sup>!" by blast
          with normalizability_def have "(s, u) \<in> (rstep \<R>)\<^sup>* \<and> (t, u) \<in> (rstep \<R>)\<^sup>*" by fastforce
          with rsteps_sk have "(sk s, sk u) \<in> (rstep (sk.h\<^sub>R \<R>))\<^sup>* \<and> (sk t, sk u) \<in> (rstep (sk.h\<^sub>R \<R>))\<^sup>*" by fastforce
          with NF_join_imp_reach[OF nf] have steps:"(sk s, sk t) \<in> (rstep (sk.h\<^sub>R \<R>))\<^sup>*" by auto
          from sk_less SN_imp_acyclic[OF sk_run.SN_less_h] sk_inj have "s \<noteq> t" unfolding acyclic_def by auto
          with rstep_imp_deskolemize_rsteps[OF steps] have "(s, t) \<in> (rstep \<R>)\<^sup>+"
            unfolding deskolemize_sk rtrancl_eq_or_trancl by auto
          with compatible_rstep_trancl_imp_less[OF R_less] have "s \<succ> t" by auto
          with lr' unoriented show ?thesis using s t by blast
        next
          case False
          then obtain u where step:"(sk t, u) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" by blast
          from sk_step_exists[OF step] obtain u' where step:"(sk t, sk u') \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" by auto
          with ordstep have "sk t \<succ>\<^sub>s\<^sub>k sk u'" by blast
          with sk_run.trans_h[OF sk_less this] ind_step(1)[OF _ step] have "t \<notin> NF_trs (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)" by auto
          then obtain v where irstep:"(t, v) \<in> irstep False S\<^sub>\<omega>" by (metis NF_I NF_Sw_NF_Sinf rstep_imp_irstep)

          from True s t have root_step:"(s, t) \<in> rstep_r_p_s (E\<^sub>\<omega>\<^sup>\<leftrightarrow>) (l', r') [] \<rho>" unfolding rstep_r_p_s_def by force
          from unoriented peak_cases[OF root_step irstep] consider
            "s \<notin> NF_trs S\<^sub>\<omega>" | "\<exists>w. (s, w) \<in> (rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>))\<^sup>= \<and> v \<succeq> w" by auto
          then show ?thesis proof(cases,simp add: NF_Sw_NF_Sinf)
            case 2
            then obtain w where w:"(s, w) \<in> (rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>))\<^sup>=" "v \<succeq> w" by auto
            from irstep qrstep_subset_rstep compatible_rstep_imp_less[OF Sw_less] have "t \<succ> v"
              unfolding irstep_def by blast
            with less_imp_less_sk have tv:"sk t \<succ>\<^sub>s\<^sub>k sk v" by auto
            from less_imp_less_sk w have "sk v \<succ>\<^sub>s\<^sub>k sk w \<or> sk v = sk w" by auto
            with tv sk_run.trans_h have tw:"sk t \<succ>\<^sub>s\<^sub>k sk w" by metis
            with sk_less sk_run.trans_h have sw:"sk s \<succ>\<^sub>s\<^sub>k sk w" by metis
            with SN_imp_acyclic[OF sk_run.SN_less_h] have "s \<noteq> w" unfolding acyclic_def by auto
            with w have "(s, w) \<in> rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" by auto
            with REinf_step_Sinf_step[OF sw] have "(sk s, sk w) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>"
              unfolding rstep_union by fast
            from ind_step(1)[OF _ this] tw show ?thesis by auto
          qed
        qed
      next
        case False
        from Einf_sym_without_Ew_sym[OF lr' False] obtain j where lr_cases:
          "(l', r') \<in> E j \<and> (l', r') \<notin> E (Suc j) \<or> (r', l') \<in> E j \<and> (r', l') \<notin> E (Suc j)" by auto
        define u' where "u' \<equiv> if (l', r') \<in> (E j) \<and> (l', r') \<notin> (E (Suc j)) then l' else r'"
        define v' where "v' \<equiv> if (l', r') \<in> (E j) \<and> (l', r') \<notin> (E (Suc j)) then r' else l'"
        from lr_cases have uv:"(u', v') \<in> (E j)" "(u', v') \<notin> E (Suc j)" by (auto simp: u'_def v'_def)
        have uv_cases:"(u' = l' \<and> v' = r') \<or> (u' = r' \<and> v' = l')" by (auto simp: u'_def v'_def)
        { fix u v i
          assume "(u, v) \<in> encstep1 (E i) (R i)"
          then have "(u, v) \<in> ostep (E i) (R i)" using encstep1_ostep by simp
          with ostep_mono[of "E i" "E\<^sub>\<infinity>" "R i" "R\<^sub>\<infinity>"] have "(u, v) \<in> ostep E\<^sub>\<infinity> R\<^sub>\<infinity>" by auto
          with ostep_iff_ordstep[OF Rinf_less] have "(u, v) \<in> ordstep {\<succ>} (R\<^sub>\<infinity> \<union> E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" by blast
          with ordstep_subset_S[OF Rinf_less] have "(u, v) \<in> ordstep {\<succ>} (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)" by auto
          with ordstep_S_conv[OF Rinf_less] have "(u, v) \<in> rstep (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)" by auto
        } note encstep1_rstep_Sinf = this

        let ?enc = "encstep1 (E (Suc j)) (R (Suc j)) O (E (Suc j))\<^sup>\<leftrightarrow>"
        from uv oKBi_E_supset' [OF irun [of j]]
        have "(u', v') \<in> R (Suc j) \<or> (v', u') \<in> R (Suc j) \<or> u' = v' \<or> (u', v') \<in> ?enc\<^sup>\<leftrightarrow>" by auto
        with uv_cases consider "(l', r') \<in> R (Suc j)" | "(r', l') \<in> R (Suc j)" | "l' = r'" |
          "(l', r') \<in> ?enc" | "(r', l') \<in> ?enc" by auto
        then show ?thesis proof(cases)
          case 1
          then show ?thesis unfolding s by fast
        next
          case 2
          with Ri_less sk_run.compat_h have "sk.h r' \<succ>\<^sub>s\<^sub>k sk.h l'" by auto
          with st sk_run.subst_h[of _ _ "\<tau> \<circ>\<^sub>s \<sigma>"] have "sk t \<succ>\<^sub>s\<^sub>k sk s" unfolding Hole by auto
          from sk_run.trans_h[OF sk_less this] SN_imp_acyclic[OF sk_run.SN_less_h] show ?thesis
            unfolding acyclic_def by auto
        next
          case 3
          with st sk_less sk_run.subst_h[of _ _ "\<tau> \<circ>\<^sub>s \<sigma>"] have "sk s \<succ>\<^sub>s\<^sub>k sk s" unfolding Hole by auto
          with SN_imp_acyclic[OF sk_run.SN_less_h] show ?thesis unfolding acyclic_def by auto
        next
          case 4
          then obtain u where "(l', u) \<in> encstep1 (E (Suc j)) (R (Suc j))" by auto
          from encstep1_rstep_Sinf[OF this(1)] show ?thesis unfolding s by auto
        next
          case 5
          then obtain u where u:"(r', u) \<in> encstep1 (E (Suc j)) (R (Suc j))" "(u,l') \<in> (E (Suc j))\<^sup>\<leftrightarrow>" by auto
          from u encstep1_less[OF _ Ri_less] have less:"r' \<succ> u" by auto
          with subst have "r' \<cdot> \<rho> \<succ> u \<cdot> \<rho>" by auto
          with less_imp_less_sk have 1:"sk (r' \<cdot> \<rho>) \<succ>\<^sub>s\<^sub>k sk (u \<cdot> \<rho>)" by auto
          with sk_less sk_run.trans_h have 3:"sk s \<succ>\<^sub>s\<^sub>k sk (u \<cdot> \<rho>)" unfolding t by fast
          from u have "(l', u) \<in> E\<^sub>\<infinity>\<^sup>\<leftrightarrow> \<union> R\<^sub>\<infinity>" by auto
          then have 4:"(sk.h l', sk.h u) \<in> Eh\<^sub>\<infinity>\<^sup>\<leftrightarrow> \<union> Rh\<^sub>\<infinity>" using sk.rule_h[of l' u "E\<^sub>\<infinity>\<^sup>\<leftrightarrow> \<union> R\<^sub>\<infinity>"]
            using sk.hR_sym sk.hR_union sk_run.hEinf sk_run.hRinf by metis
          { fix x
            assume x:"x \<in> vars_term (sk.h u)"
            from rstep_subset_less SN_less[THEN SN_subset] less have "SN (rstep {(r',u)})" by force
            from x SN_imp_variable_condition[OF this] sk_vs have "?\<sigma> x = sk (deskolemize (?\<sigma> x))" by auto
            then have "?\<sigma> x = ((sk.h\<^sub>s (deskolemize \<circ> ?\<sigma>)) \<circ>\<^sub>s \<sigma>\<^sub>s\<^sub>k) x" unfolding sk_def subst_compose_def comp_def by simp
          }
          then have sku:"sk (u \<cdot> \<rho>) = sk.h u \<cdot> ?\<sigma>" unfolding sk_def sk.subst_apply_h \<rho>_def
            using term_subst_eq_conv[of "sk.h u" ?\<sigma>] by force
          have "(sk s, sk (u \<cdot> \<rho>)) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" proof (cases "(sk.h l', sk.h u) \<in> Eh\<^sub>\<infinity>\<^sup>\<leftrightarrow>")
            case True
            with 3 have "(sk s, sk (u \<cdot> \<rho>)) \<in> E_ord (\<succ>\<^sub>s\<^sub>k) Eh\<^sub>\<infinity>"
              unfolding st Hole sku intp_actxt.simps E_ord_def by fast
            then show ?thesis by auto
          next
            case False
            with 4 have "(sk.h l', sk.h u) \<in> Rh\<^sub>\<infinity>" by blast
            then show ?thesis unfolding st Hole sku intp_actxt.simps by fast
          qed
          with 1 ind_step(1) show ?thesis unfolding t by auto
        qed
      qed
    qed
  next
    case (More f bef D aft)
    from st have sk_s:"sk s = Fun f (bef @ D\<langle>?l \<cdot> ?\<sigma>\<rangle> # aft)" and sk_t:"sk t = Fun f (bef @ D\<langle>?r \<cdot> ?\<sigma>\<rangle> # aft)"
      unfolding More intp_actxt.simps by auto
    then obtain g where f:"f = FOrig g"  unfolding sk_def \<sigma>\<^sub>s\<^sub>k_def by (cases s, auto)
    let ?p = "Cons (length bef) []"
    let ?s = "s |_ ?p" and ?t = "t |_ ?p"
    from sk_C[of s "More f bef Hole aft"] sk_s have p:"?p \<in> poss s" and s:"sk ?s = D\<langle>?l \<cdot> ?\<sigma>\<rangle>" by auto
    from sk_C[of t "More f bef Hole aft"] sk_t have t:"sk ?t = D\<langle>?r \<cdot> ?\<sigma>\<rangle>" by auto
    from * have step:"(sk ?s, sk ?t) \<in> rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>" unfolding s t using lr by auto
    from ground_subt_less[OF ground_sk, of t, of "D\<langle>?r\<cdot>?\<sigma>\<rangle>"] have "sk t \<succ>\<^sub>s\<^sub>k D\<langle>?r \<cdot> ?\<sigma>\<rangle>" unfolding st More by auto
    with ind_step(1)[OF _ step] t have "?s \<notin> NF_trs (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)" unfolding t by auto
    with NF_subterm[OF _ subt_at_imp_supteq[OF p]] show ?thesis by auto
  qed
qed

lemma NF_Sw_subset_NF_R:"NF_trs S\<^sub>\<omega> \<subseteq> NF_trs \<R>"
proof-
  { fix s u
    assume su:"(s,u) \<in> rstep \<R>"
    with conv_eq oKBi_conversion_ERw have "(s, u) \<in> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    from rsteps_sk[OF this[unfolded conversion_def rstep_simps(5)[symmetric]]]
    have "(sk s, sk u) \<in> (rstep (sk.h\<^sub>R (R\<^sub>\<omega> \<union> E\<^sub>\<omega>)))\<^sup>\<leftrightarrow>\<^sup>*"
      unfolding conversion_def sk.hR_sym rstep_simps(5) by meson
    then have "(sk s, sk u) \<in> (rstep (Rh\<^sub>\<omega> \<union> Eh\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding sk_run.hRw sk_run.hEw sk.hR_union by auto
    note conv_ground = gterm_conv_GROUND_conv[OF ground_sk ground_sk this]
    with ground_RE_conv_S_conv have gconv:"(sk s, sk u) \<in> (GROUND (rstep Sh\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by simp
    with correctness_okb_sk[THEN conjunct1] CR_imp_conversionIff_join
    have join:"(sk s, sk u) \<in> (GROUND (rstep Sh\<^sub>\<omega>))\<^sup>\<down>" by auto
    then have join:"(sk s, sk u) \<in> (rstep Sh\<^sub>\<omega>)\<^sup>\<down>" using  GROUND_subset[of "rstep Sh\<^sub>\<omega>"] join_mono by blast
    then obtain t where t:"(sk s, t) \<in> (rstep Sh\<^sub>\<omega>)\<^sup>*" "(sk u, t) \<in> (rstep Sh\<^sub>\<omega>)\<^sup>*" by auto
    { assume eq:"sk s = t"
      with t(2) have geq:"sk u \<succeq>\<^sub>s\<^sub>k sk s" unfolding rtrancl_eq_or_trancl
        using sk_run.okb_h.compatible_rstep_trancl_imp_less sk_run.irun_h.Sw_less by auto
      from compatible_rstep_imp_less[OF R_less su] less_imp_less_sk have "sk s \<succ>\<^sub>s\<^sub>k sk u" by auto
      with sk_run.trans_h[OF this] geq sk_run.okb_h.irrefl have False by auto
    }
    with t(1) tranclD obtain v' where "(sk s, v') \<in> (rstep Sh\<^sub>\<omega>)" unfolding rtrancl_eq_or_trancl by metis
    with sk_run.irun_h.Sw_subset_Sinf rstep_mono have "(sk s, v') \<in> (rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>)" by blast
    with sk_step_exists obtain v where "(sk s, sk v) \<in> (rstep \<S>\<^sub>s\<^sub>k\<^sup>\<infinity>)" by blast
    from sk_Swinf_step_imp_no_Sinf_NF[OF this] NF_Sw_NF_Sinf have "s \<notin> NF_trs S\<^sub>\<omega>" by auto
  }
  then show ?thesis by auto
qed

lemma Einf_Sw_reducible_or_Ew:
  assumes st:"(s,t) \<in> E\<^sub>\<infinity>" and "(s,t) \<notin> E\<^sub>\<omega>"
  shows "s \<notin> NF_trs S\<^sub>\<omega> \<or> t \<notin> NF_trs S\<^sub>\<omega> \<or> s = t"
proof-
  from assms Einf_without_Ew[OF st] obtain i where i:"(s, t) \<in> E i" "(s, t) \<notin> E (Suc i)" by auto
  have S:"\<S> (R (Suc i)) (E (Suc i)) \<subseteq> \<S> R\<^sub>\<infinity> E\<^sub>\<infinity>" using E_ord_mono by (metis Sup_upper range_eqI sup.mono)
  let ?E = "E (Suc i)" and ?R = "R (Suc i)"
  note oostep = ostep_iff_ordstep[OF Ri_less]
  note Sstep = ordstep_subset_S[OF Ri_less, unfolded ordstep_S_conv[OF Ri_less]]
  from i oKBi_E_supset'[OF irun] consider
    "(s, t) \<in> (encstep1 ?E ?R) O ?E" | "(s, t) \<in> ?E O (encstep1 ?E ?R)\<inverse>" | "(s,t) \<in> (?R\<^sup>\<leftrightarrow>)\<^sup>=" by blast
  then have "s \<notin> NF_trs (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>) \<or> t \<notin> NF_trs (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>) \<or> s = t"
  proof(cases)
    case 1
    then obtain u where su:"(s,u) \<in> encstep1 ?E ?R" and ut:"(u,t) \<in> ?E" by auto
    from encstep1_ostep[OF su(1)] oostep have "(s,u) \<in> ordstep {\<succ>} (?R \<union> ?E\<^sup>\<leftrightarrow>)" by auto
    with Sstep have step:"(s,u) \<in> rstep (\<S> ?R ?E)" by auto
    with rstep_mono[of "\<S> ?R ?E" "\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>"] E_ord_mono[of ?E "E\<^sub>\<infinity>"] have step:"(s,u) \<in> rstep (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)" by blast
    thus ?thesis by auto
  next
    case 2
    then obtain u where ut:"(u,t) \<in> (encstep1 ?E ?R)\<inverse>" and ut:"(s,u) \<in> ?E" by auto
    with converse_iff have tu:"(t,u) \<in> encstep1 ?E ?R" by auto
    from encstep1_ostep[OF tu] oostep have "(t,u) \<in> ordstep {\<succ>} (?R \<union> ?E\<^sup>\<leftrightarrow>)" by auto
    with Sstep have "(u,t) \<in> (rstep (\<S> ?R ?E))\<inverse>" by auto
    with rstep_mono[of "\<S> ?R ?E" "\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>"] E_ord_mono[of ?E "E\<^sub>\<infinity>"] have step:"(t,u) \<in> rstep (\<S> R\<^sub>\<infinity> E\<^sub>\<infinity>)" by blast
    thus ?thesis by auto
  next
    case 3
    have "?R \<subseteq> rstep R\<^sub>\<infinity>" unfolding rstep_union using rstep_rule by auto
    with 3 show ?thesis by blast
  qed
  with NF_Sw_NF_Sinf show ?thesis by auto
qed

context
  assumes Ew_irreducible:"\<forall>s t. (s,t) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<longrightarrow> s \<in> NF_trs R\<^sub>\<omega>"
  and Ew_nontrivial:"\<forall>t. (t,t) \<notin> E\<^sub>\<omega>"
  and Ew_unorientable:"\<forall>s t. (s,t) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<longrightarrow> \<not> s \<succ> t"
begin

lemma NF_Rw_subset_NF_Sw: "NF_trs R\<^sub>\<omega> \<subseteq> NF_trs S\<^sub>\<omega>"
proof
  fix s
  assume s_NF_Rw:"s \<in> NF_trs R\<^sub>\<omega>"
  thus "s \<in> NF_trs S\<^sub>\<omega>" proof (induct s rule: SN_induct [OF SN_lessenc])
    case (1 s)
    let ?Ew = "{(s \<cdot> \<sigma>, t \<cdot> \<sigma>) | s t \<sigma>. (s, t) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<and> s \<cdot> \<sigma> \<succ> t \<cdot> \<sigma>}"
    note NF = 1(2)[unfolded NF_trs_union]
    { assume "s \<notin> NF_trs S\<^sub>\<omega>"
      with 1(2) have "s \<notin> NF_trs ?Ew" unfolding Sw_def NF_trs_union by auto
      then obtain l' r' C \<sigma> where lr':"s = C\<langle>l' \<cdot> \<sigma>\<rangle>" "(l',r') \<in> ?Ew" by fast
      then obtain l r \<tau> where lr:"l' = l \<cdot> \<tau>" "r' = r \<cdot> \<tau>" "(l,r) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "l \<cdot> \<tau> \<succ> r \<cdot> \<tau>" by auto
      with subst have gt:"l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>) \<succ> r \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)" by auto
      also have "r \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>) \<cdot>\<unrhd> r" using encompeq.intros[of _ \<box> r "\<tau> \<circ>\<^sub>s \<sigma>"] by auto
      with gt have gt:"l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>) \<cdot>\<succ> r" unfolding lessencp_def by fast
      from encompeq.intros[of _ C "l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)" Var] have "s \<cdot>\<unrhd> l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)" unfolding lr' lr by auto
      with gt have gt:"s \<cdot>\<succ> r" using lessenc_compat2 by auto
      from lr(3) Ew_irreducible have "r \<in> NF_trs R\<^sub>\<omega>" by auto
      with 1(1)[of r] gt NF_Sw_subset_NF_R have NF_r:"r \<in> NF_trs \<R>" by auto
      from conv_eq[unfolded oKBi_conversion_ERw] lr(3) have "(l,r) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*" by auto
      with CR_imp_conversionIff_join CR_R NF_join_imp_reach[OF NF_r] have "(l,r) \<in> (rstep \<R>)\<^sup>*" by auto
      note seq = this[unfolded rtrancl_eq_or_trancl]
      with compatible_rstep_trancl_imp_less[OF R_less] have " l = r \<or> l \<succ> r" by auto
      with Ew_nontrivial Ew_unorientable lr(3) have False by auto
    }
    then show ?case by auto
  qed
qed

lemma completeness:
  assumes "reduced \<R>" and "reduced R\<^sub>\<omega>"
  shows "E\<^sub>\<omega> = {} \<and> \<R> \<doteq> R\<^sub>\<omega>"
proof-
  { fix s t
    assume st:"(s,t) \<in> E\<^sub>\<omega>"
    note NFs = subset_trans[OF NF_Rw_subset_NF_Sw NF_Sw_subset_NF_R]
    with Ew_irreducible[rule_format] st have NF:"s \<in> NF_trs \<R>" "t \<in> NF_trs \<R>" by blast+
    from conv_eq[unfolded oKBi_conversion_ERw] st have "(s, t) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*" by auto
    with CR_imp_conversionIff_join CR_R NF_join_imp_reach[OF NF(2)] have "(s,t) \<in> (rstep \<R>)\<^sup>*" by auto
    note seq = this[unfolded rtrancl_eq_or_trancl]
    with NF(1) have "s = t" by (simp add: NF_no_trancl_step)
    with st Ew_nontrivial have False by auto
  }
  then have Ew_empty:"E\<^sub>\<omega> = {}" by auto
  have Sw_Rw:"S\<^sub>\<omega> = R\<^sub>\<omega>" using Ew_empty unfolding Sw_def by auto
  note SN_Rw = SN_Sw_step[unfolded Sw_Rw]
  note vars = SN_imp_variable_condition[OF SN_R] SN_imp_variable_condition[OF SN_Rw]
  interpret complete_ars "(rstep \<R>)" by (unfold_locales, insert CR_R SN_R, auto)
  from conv_eq[unfolded oKBi_conversion_ERw] have in_Rconv:"rstep R\<^sub>\<omega> \<subseteq> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
    by (auto simp: rstep_simps)
  from complete_NE_intro1[OF in_Rconv SN_Rw] have NE:" (rstep \<R>)\<^sup>! = (rstep R\<^sub>\<omega>)\<^sup>!"
    using NF_Sw_subset_NF_R unfolding Sw_Rw by auto
  with assms reduced_NE_imp_unique[OF vars] have "\<R> \<doteq> R\<^sub>\<omega>" by auto
  with Ew_empty show ?thesis by auto
qed
end

lemma Ew_empty_imp_CR_Rw:
  assumes "E\<^sub>\<omega> = {}"
  shows "CR (rstep R\<^sub>\<omega>)"
proof-
  from assms Sw_def sk_run.hRw have SR[simp]:"S\<^sub>\<omega> = R\<^sub>\<omega>" by auto
  have Eh:"Eh\<^sub>\<omega> = {}" unfolding sk_run.hEw[symmetric] assms
    unfolding sk.h\<^sub>R_def map_funs_trs.simps map_funs_rule.simps by simp
  from sk_run.irun_h.correctness_okb sk_run_fair have "GCR (rstep Sh\<^sub>\<omega>)" by fast
  hence GCR:"GCR (rstep Rh\<^sub>\<omega>)" unfolding sk_run.irun_h.Sw_def Eh by auto
  { fix s t u
    assume "(s,t) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" and "(s,u) \<in> (rstep R\<^sub>\<omega>)\<^sup>*"
    with rsteps_sk[of _ _ "R\<^sub>\<omega>"] have *:"(sk s,sk t) \<in> (rstep Rh\<^sub>\<omega>)\<^sup>*" and "(sk s,sk u) \<in> (rstep Rh\<^sub>\<omega>)\<^sup>*"
      using sk_run.hRw by auto
    then have "(sk s,sk t) \<in> (rstep Rh\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" and "(sk s,sk u) \<in> (rstep Rh\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" by auto
    then have "(sk t, sk u) \<in> (rstep Rh\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*"
      by (metis (no_types, lifting) conversion_def conversion_inv rtrancl_trans)
    with gterm_conv_GROUND_conv ground_sk have *:"(sk t, sk u) \<in> (GROUND(rstep Rh\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
    with GCR have "(sk t,sk u) \<in> (GROUND (rstep Rh\<^sub>\<omega>))\<^sup>\<down>" unfolding CR_iff_conversion_imp_join by auto
    then obtain v where v:"(sk t,v) \<in> (GROUND (rstep Rh\<^sub>\<omega>))\<^sup>*" "(sk u,v) \<in> (GROUND (rstep Rh\<^sub>\<omega>))\<^sup>*"
      by auto
    let ?v = "deskolemize v"
    from v rtrancl_mono[OF GROUND_subset] have *:"(sk t,v) \<in> (rstep Rh\<^sub>\<omega>)\<^sup>*" "(sk u,v) \<in> (rstep Rh\<^sub>\<omega>)\<^sup>*" by auto
    note d = rstep_imp_deskolemize_rsteps[of _ _ R\<^sub>\<omega>, unfolded sk_run.hRw] 
    from d[OF *(1)] d[OF *(2)] have "(t,?v) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" and "(u,?v) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" by auto
    with rtrancl_converse have "(t,u) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>" unfolding join_def by blast
  }
  then show ?thesis unfolding CR_on_def by auto
qed

end
end
end

lemma linear_term_replace:
  assumes "linear_term C\<langle>t\<rangle>" and "vars_term s \<subseteq> vars_term t" and "linear_term s"
  shows "linear_term C\<langle>s\<rangle>"
  using assms(1)
proof(induct C)
  case Hole
  then show ?case using assms by auto
next
  case (More f bef C aft)
  from More(2) have us:"\<And>u. u \<in> set (bef @ C\<langle>t\<rangle> # aft) \<Longrightarrow> linear_term u" 
    unfolding intp_actxt.simps linear_term.simps by auto
  then have "linear_term C\<langle>t\<rangle>" by simp
  from More(1)[OF this] us have lin:"\<And>u. u \<in> set (bef @ C\<langle>s\<rangle> # aft) \<Longrightarrow> linear_term u" by auto
  from assms(2) have subset:"vars_term C\<langle>s\<rangle> \<subseteq> vars_term C\<langle>t\<rangle>" unfolding vars_term_ctxt_apply by auto
  from More(2) have p:"is_partition (map vars_term (bef @ C\<langle>t\<rangle> # aft))" 
    unfolding intp_actxt.simps linear_term.simps by auto
  then have "is_partition (map vars_term (bef @ C\<langle>s\<rangle> # aft))" proof(induct bef)
    case Nil
    with subset show ?case unfolding append.left_neutral list.map(2) is_partition_Cons by auto
  next
    case (Cons u bef)
    let ?Vt = "\<Union>(set (map vars_term (bef @ C\<langle>t\<rangle> # aft)))"
    let ?Vs = "\<Union>(set (map vars_term (bef @ C\<langle>s\<rangle> # aft)))"
    from Cons(2) have "is_partition (map vars_term (bef @ C\<langle>t\<rangle> # aft))" and vs:"vars_term u \<inter> ?Vt = {}"
      unfolding append.append_Cons list.map(2) is_partition_Cons by auto
    with Cons have p:"is_partition (map vars_term (bef @ C\<langle>s\<rangle> # aft))" by auto
    from subset vs have "vars_term u \<inter> ?Vs = {}" by auto
    with p show ?case unfolding append.append_Cons list.map(2) is_partition_Cons by blast
  qed
  with lin show ?case unfolding intp_actxt.simps linear_term.simps by auto
qed

lemma linear_term_unique_var_pos:
  assumes "linear_term t" and "x \<in> vars_term t"
  shows "\<exists>!p. p \<in> poss t \<and> t |_ p = Var x"
proof-
  from assms(2) vars_term_poss_subt_at obtain p where p:"p \<in> poss t" "t |_ p = Var x" by metis
  { fix q
    assume q:"q \<noteq> p" "q \<in> poss t" "t |_ q = Var x"
    with p q have "parallel_pos p q"
      by (metis self_append_conv parallel_pos prefix_pos_diff var_pos_maximal)
    from parallel_remove_prefix[OF this] obtain pq i\<^sub>p i\<^sub>q p' q' where
      *:"p = pq @ i\<^sub>p # p'" "q = pq @ i\<^sub>q # q'" "i\<^sub>p \<noteq> i\<^sub>q" by auto
    let ?t = "t |_ pq"
    from p have pq:"pq \<in> poss t" unfolding * by auto
    with p(1) q(2) obtain f ts where t:"?t = Fun f ts" unfolding * by (cases ?t, auto)
    from p(1) q(2) subt_at_append[OF pq] have poss:"i\<^sub>p#p' \<in> poss ?t" "i\<^sub>q#q' \<in> poss ?t"
      unfolding * by auto
    from poss have ils:"i\<^sub>p < length ts" "i\<^sub>q < length ts" unfolding t * by auto
    with poss poss_Cons_poss have poss'':"p' \<in> poss (ts ! i\<^sub>p)" "q' \<in> poss (ts ! i\<^sub>q)"
      unfolding * t by auto

    from subt_at_append[OF pq] p(2) have "?t |_ (Cons i\<^sub>p p') = Var x" unfolding * by auto
    with vars_term_subt_at poss'' have x1:"x \<in> vars_term (ts ! i\<^sub>p)" unfolding t by fastforce
    from subt_at_append[OF pq] q(3) have "?t |_ (Cons i\<^sub>q q') = Var x" unfolding * by auto
    with vars_term_subt_at poss'' have "x \<in> vars_term (ts ! i\<^sub>q)" unfolding t by fastforce
    with x1 have "vars_term (ts ! i\<^sub>p) \<inter> vars_term (ts ! i\<^sub>q) \<noteq> {}" by auto

    with *(3) ils nth_map[OF ils(1)] nth_map[OF ils(2)] have "\<not> (is_partition (map vars_term ts))"
      unfolding t length_map is_partition_alt is_partition_alt_def by metis
    then have "\<not> linear_term ?t" unfolding t linear_term.simps by auto
    then have False using subterm_linear assms subt_at_imp_supteq[OF pq] by auto
  }
  with p show ?thesis by metis
qed


lemma linear_term_subst:
  assumes "linear_term l" and "linear_term r" and "vars_term r \<subseteq> vars_term l" and "linear_term (l\<cdot>\<sigma>)"
  shows "linear_term (r\<cdot>\<sigma>)"
  using assms(2) assms(3)
proof(induct r)
  case (Var x)
  then have "l \<unrhd> Var x" by auto
  with subterm_linear[OF _ assms(4), of "\<sigma> x"] show ?case by force
next
  case (Fun f rs)
  note IH = this
  then have p:"is_partition (map vars_term rs)" and lin_ri:"\<And>ri. ri \<in> (set rs) \<Longrightarrow> linear_term ri"
    unfolding linear_term.simps by auto
  { fix ri\<^sub>\<sigma>
    assume "ri\<^sub>\<sigma> \<in> set (map (\<lambda>t. t\<cdot>\<sigma>) rs)"
    then obtain ri where ri:"ri \<in> set rs" "ri\<^sub>\<sigma> = ri\<cdot>\<sigma>" by force
    with Fun(3) have "vars_term ri \<subseteq> vars_term l" by auto
    with ri Fun(1)[OF ri(1) lin_ri[OF ri(1)]] have "linear_term ri\<^sub>\<sigma>" by simp
  }
  note linear_subterms = this
  { assume "\<not> is_partition (map vars_term (map (\<lambda>t. t\<cdot>\<sigma>) rs))"
    from this[unfolded is_partition_alt is_partition_alt_def map_map length_map] obtain i j where
        i:"i < length rs" and j:"j < length rs" and ij:"i \<noteq> j" and
        inter:"vars_term ((rs ! i)\<cdot>\<sigma>) \<inter> vars_term ((rs ! j)\<cdot>\<sigma>) \<noteq> {}" by auto
      from inter obtain x where x:"x \<in> vars_term ((rs ! i)\<cdot>\<sigma>)" "x \<in> vars_term ((rs ! j)\<cdot>\<sigma>)" by auto
      then obtain y z where y:"y \<in> vars_term (rs ! i)" "x \<in> vars_term (\<sigma> y)" and
                z:"z \<in> vars_term (rs ! j)" "x \<in> vars_term (\<sigma> z)" unfolding vars_term_subst by auto
      from p i j ij y(1) z(1) have yz:"y \<noteq> z" unfolding is_partition_alt is_partition_alt_def by auto
      from i j y(1) z(1) IH(3) have yl:"y \<in> vars_term l" and zl:"z \<in> vars_term l"
        unfolding term.set(4) by fastforce+
      note vsub = vars_term_poss_subt_at
      from vsub[OF yl] obtain p where p:"p \<in> poss l" "l |_ p = Var y" by auto
      from vsub[OF zl] obtain q where q:"q \<in> poss l" "l |_ q = Var z" by auto
      with p yz have neq:"p \<noteq> q" by auto
      with p q have par:"parallel_pos p q"
        by (metis append_self_conv parallel_pos prefix_pos_diff var_pos_maximal)
      from vsub[OF y(2)] obtain p' where p':"p' \<in> poss (\<sigma> y)" "(\<sigma> y) |_ p' = Var x" by auto
      from vsub[OF z(2)] obtain q' where q':"q' \<in> poss (\<sigma> z)" "(\<sigma> z) |_ q' = Var x" by auto
      from par have neq:"p @ p' \<noteq> q @ q'"
        by (metis less_eq_pos_simps(1) pos_less_eq_append_not_parallel)
      from subt_at_append p p' have x1:"l\<cdot>\<sigma> |_ (p @ p') = Var x" by simp
      from subt_at_append q q' have x2:"l\<cdot>\<sigma> |_ (q @ q') = Var x" by simp
      from p p'(1) have pl:"p @ p' \<in> poss (l\<cdot>\<sigma>)" unfolding poss_append_poss by auto
      from q q'(1) have ql:"q @ q' \<in> poss (l\<cdot>\<sigma>)" unfolding poss_append_poss by auto
      from vars_term_subt_at[OF this] x2 have "x \<in> vars_term (l\<cdot>\<sigma>)" by auto
      from linear_term_unique_var_pos[OF assms(4) this] x1 x2 pl ql neq have False by blast
  }
  with linear_subterms show ?case by auto
qed

locale linear_ordered_completion1 = 
  ordered_completion less for less :: "('a, 'b::infinite) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
begin

text \<open>A linear critical pair as defined by Devie.\<close>
definition "lin_overlap R l r p l' r' \<sigma> \<equiv>
    (\<exists>p. p \<bullet> (l,r) \<in> R) \<and>
    (\<exists>p. p \<bullet> (l',r') \<in> R) \<and>
    vars_rule (l,r) \<inter> vars_rule (l',r') = {} \<and>
    p \<in> fun_poss l' \<and>
    mgu l (l' |_ p) = Some \<sigma> \<and>
    ((l \<succ> r \<and> \<not> (r' \<succ> l')) \<or> (l' \<succ> r' \<and> \<not> (r \<succ> l)))"

definition "LCP R =
  {(replace_at l' p r \<cdot> \<sigma>, r' \<cdot> \<sigma>) | l r p l' r' \<sigma>. lin_overlap R l r p l' r' \<sigma>}"

inductive oKBilin ::
    "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> bool" (infix "\<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n" 55)
  where
    deduce: "(s, t) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, u) \<in> rstep (R \<union> E\<^sup>\<leftrightarrow>) \<Longrightarrow> linear_term t \<Longrightarrow> linear_term u \<Longrightarrow> (E, R)\<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E \<union> {(t, u)}, R)" |
    orientl: "s \<succ> t \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E - {(s, t)}, R \<union> {(s, t)})" |
    orientr: "t \<succ> s \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R)\<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E - {(s, t)}, R \<union> {(t, s)})" |
    delete: "(s, s) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E - {(s, s)}, R)" |
    compose: "(t, u) \<in> rstep (R - {(s, t)}) \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E, (R - {(s, t)}) \<union> {(s, u)})" |
    simplifyl: "(s, u) \<in> rstep R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n ((E - {(s, t)}) \<union> {(u, t)}, R)" |
    simplifyr: "(t, u) \<in> rstep R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n ((E - {(s, t)}) \<union> {(s, u)}, R)" |
    collapse: "(t, u) \<in> encstep2 {} (R - {(t, s)}) \<Longrightarrow> (t, s) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E \<union> {(u, s)}, R - {(t, s)})"

lemma oKBilin_step_imp_oKBi_step:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E', R')"
  shows "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity> (E', R')"
  using assms
proof(cases)
  case (deduce s t u)
  then show ?thesis using oKBi.deduce by auto
next
  case (orientl s t)
  then show ?thesis using oKBi.orientl by auto
next
  case (orientr t s)
  then show ?thesis using oKBi.orientr by auto
next
  case (compose t u s)
  then show ?thesis using oKBi.compose rstep_imp_ostep[OF compose(3)] by auto
next
  case (simplifyl s u t)
  then show ?thesis using oKBi.simplifyl encstep1.rstep[OF simplifyl(3)] by auto
next
  case (simplifyr t u s)
  then show ?thesis using oKBi.simplifyr encstep1.rstep[OF simplifyr(3)] by auto
next
  case (collapse t u s)
  from collapse(3) have "(t, u) \<in> encstep2 E (R - {(t, s)})" using encstep2_mono[of "{}"] by auto
  with collapse show ?thesis using oKBi.collapse by auto
qed (auto intro!:oKBi.delete oKBi.orientl)

lemma oKBilin_less:
  assumes "(E, R)  \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E', R')" and "R \<subseteq> {\<succ>}"
  shows "R' \<subseteq> {\<succ>}"
  using oKBi_less[OF assms(2) oKBilin_step_imp_oKBi_step] assms by auto

lemma oKBilin_R_supset:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E', R')"
  shows "R - R' \<subseteq> encstep2 {} R' O E' \<union> R' O (rstep R')\<inverse>"
  using assms
proof (cases)
  case (compose s t u)
  then have "(s, t) \<in> rstep R'" by auto
  with compose show ?thesis by fast
next
  case (collapse s t u)
  with encstep2_mono [of E "E \<union> {(t, u)}"] show ?thesis by fast
qed auto

lemma linear_term_step:
  assumes "linear_term t" and "linear_trs R" and "R \<subseteq> {\<succ>}" and "(t,s) \<in> rstep R"
  shows "linear_term s"
proof-
  have "rstep {\<succ>} \<subseteq> {\<succ>}" using rstep_subset rstep_rstep subst ctxt by fastforce
  then have SN:"SN (rstep {\<succ>})" using SN_less SN_subset by auto
  note vc = SN_imp_variable_condition[OF SN]
  { assume "(t,s) \<in> rstep R"
    then obtain l r C \<sigma> where lr:"(l,r) \<in> R" and st:"t = C\<langle>l\<cdot>\<sigma>\<rangle>" "s = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
    from lr assms(3) vc have vs_rule:"vars_term r \<subseteq> vars_term l" by auto
    from var_cond_stable[OF this] have vars':"vars_term (r\<cdot>\<sigma>) \<subseteq> vars_term (l\<cdot>\<sigma>)" by fast
    from assms(1) subterm_linear[of t "l\<cdot>\<sigma>"] have lin_ls:"linear_term (l\<cdot>\<sigma>)" unfolding st by auto
    from lr linear_trsE[OF assms(2)] have "linear_term l" "linear_term r" by auto
    from linear_term_subst[OF this vs_rule lin_ls] have "linear_term (r\<cdot>\<sigma>)" by auto 
    with linear_term_replace[OF assms(1)[unfolded st] vars'] have "linear_term s" unfolding st by auto
  }
  with assms(4) show ?thesis by auto
qed

lemma linear_trs_remove_linear[simp]: "linear_trs R \<Longrightarrow> linear_trs (R - R')"
  unfolding linear_trs_def by auto

lemma linear_trs_union_linear[simp]: "linear_trs R \<Longrightarrow> linear_trs R' \<Longrightarrow> linear_trs (R \<union> R')"
  unfolding linear_trs_def by auto

lemma oKBilin_step_linearity_preserving:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E', R')" and R_less:"R \<subseteq> {\<succ>}" and lin:"linear_trs R" "linear_trs E"
  shows "linear_trs R' \<and> linear_trs E'"
proof-
  from ordstep_imp_rstep have ostep_rstep:"\<And>E R. ostep E R \<subseteq> rstep (R \<union> E\<^sup>\<leftrightarrow>)" unfolding ostep_def by fast
  have lin_add[simp]:"\<And>R s t. linear_trs R \<Longrightarrow> linear_term s \<Longrightarrow> linear_term t \<Longrightarrow> linear_trs (R \<union> {(s,t)})"
    unfolding linear_trs_def by auto
  show ?thesis using assms(1)
  proof(cases)
    case (deduce s t u)
    with lin show ?thesis unfolding deduce unfolding linear_trs_def by fast
  next
    case (orientl s t)
    then show ?thesis using assms unfolding linear_trs_def by auto
  next
    case (orientr t s)
    then show ?thesis using assms unfolding linear_trs_def by auto
  next
    case (delete s)
    then show ?thesis using assms unfolding linear_trs_def by auto
  next
    case (compose t u s)
    from compose(4) lin have t:"linear_term t" and s:"linear_term s" unfolding linear_trs_def by auto
    from lin have "linear_trs (R - {(s, t)})" by auto
    from linear_term_step[OF t this _ compose(3)] R_less have "linear_term u" by auto
    from lin lin_add[OF _ s this] show ?thesis unfolding compose by simp
  next
    case (simplifyl s u t)
    from simplifyl(4) lin have t:"linear_term t" and s:"linear_term s" unfolding linear_trs_def by auto
    from lin have "linear_trs (E - {(s, t)})" by auto
    note step = linear_term_step[OF s lin(1) R_less simplifyl(3)]
    from lin lin_add[OF _ this t, OF linear_trs_remove_linear] show ?thesis unfolding simplifyl by auto
  next
    case (simplifyr t u s)
    from simplifyr(4) lin have t:"linear_term t" and s:"linear_term s" unfolding linear_trs_def by auto
    from lin have "linear_trs (E - {(s, t)})" by auto
    note step = linear_term_step[OF t lin(1) R_less simplifyr(3)]
    from lin lin_add[OF _ s this, OF linear_trs_remove_linear] show ?thesis unfolding simplifyr by auto
  next
    case (collapse t u s)
    from collapse(4) lin have t:"linear_term t" and s:"linear_term s" unfolding linear_trs_def by auto
    from lin have "linear_trs (E - {(s, t)})" by auto
    from encstep2_imp_rstep_sym[OF collapse(3)] have "(t, u) \<in> rstep (R - {(t, s)})" by auto
    from linear_term_step[OF t _ _ this] R_less lin have "linear_term u" by auto
    from lin lin_add[OF _ this s] show ?thesis unfolding collapse by auto
  qed
qed

lemma oKBilin_rtrancl_linear:
  assumes "oKBilin\<^sup>*\<^sup>* (E, R) (E', R')" and R_less:"R \<subseteq> {\<succ>}" and lin:"linear_trs R" "linear_trs E"
  shows "R' \<subseteq> {\<succ>} \<and> linear_trs R' \<and> linear_trs E'"
  using assms 
proof (induct "(E, R)" "(E', R')" arbitrary: E' R')
  case rtrancl_refl
  then show ?case by auto
next
  case (rtrancl_into_rtrancl ER)
  then obtain E\<^sub>i R\<^sub>i where ER:"ER = (E\<^sub>i,R\<^sub>i)" by force
  from rtrancl_into_rtrancl have "linear_trs R\<^sub>i" "linear_trs E\<^sub>i" unfolding ER by auto
  with rtrancl_into_rtrancl oKBilin_step_linearity_preserving oKBilin_less show ?case unfolding ER by metis
qed

lemma oKBi_E_supset_lin:
  assumes "(E, R) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E', R')"
  shows "E - E' \<subseteq> (rstep R' O E') \<union> (E' O (rstep R')\<inverse>) \<union> R'\<^sup>\<leftrightarrow> \<union> Id"
  using assms by (cases, insert rstep_mono [of R R'], auto)

end

locale okblin_irun = linear_ordered_completion1 +
  fixes R E
  assumes R0: "R 0 = {}"
    and E0_linear:"linear_trs (E 0)"
    and lin_irun: "\<And>i. (E i, R i) \<turnstile>\<^sub>o\<^sub>K\<^sub>B\<^sub>\<infinity>\<^sup>l\<^sup>i\<^sup>n (E (Suc i), R (Suc i))"
begin

sublocale okb_irun less R E using R0 lin_irun oKBilin_step_imp_oKBi_step by (unfold_locales, auto)

lemma oKBilin_rtrancl_i: "oKBilin\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)"
  using lin_irun by (induct i, auto intro: rtranclp.rtrancl_into_rtrancl)

lemma Ri_linear:"linear_trs (R i)"
  using oKBilin_rtrancl_linear [OF oKBilin_rtrancl_i] and E0_linear and R0 by auto

lemma Ei_linear:"linear_trs (E i)"
  using oKBilin_rtrancl_linear [OF oKBilin_rtrancl_i] and E0_linear and R0 by auto

lemma Rinf_Einf_linear:"linear_trs R\<^sub>\<infinity> \<and> linear_trs E\<^sub>\<infinity>"
  using Ri_linear Ei_linear linear_trs_def by fast

lemma Rw_linear:"linear_trs R\<^sub>\<omega>"
  unfolding R\<^sub>\<omega>_def using Ri_linear linear_trs_def by fastforce

lemma Ew_linear:"linear_trs E\<^sub>\<omega>"
  unfolding E\<^sub>\<omega>_def using Ei_linear linear_trs_def by fastforce

context
  fixes \<R>::"('a,'b) trs"
  assumes R_less:"\<R> \<subseteq> {\<succ>}" and CR_R:"CR (rstep \<R>)" and "reduced \<R>"
  and conv_eq:"(rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>*"
begin

lemma SN_R:"SN (rstep \<R>)" 
  by (rule SN_subset [OF SN_less], insert compatible_rstep_imp_less[OF R_less], auto)

abbreviation "mulsucc \<equiv> s_mul_ext Id {\<succ>}" 
abbreviation "mulsucceq \<equiv> ns_mul_ext Id {\<succ>}"
abbreviation mulsucc_op (infix "\<succ>\<^sub>m\<^sub>u\<^sub>l" 55) where "mulsucc_op s t \<equiv> (s,t) \<in> mulsucc"
abbreviation mulsucceq_op (infix "\<succeq>\<^sub>m\<^sub>u\<^sub>l" 55) where "mulsucceq_op s t \<equiv> (s,t) \<in> mulsucceq"

interpretation mulsucc: SN_order_pair mulsucc mulsucceq using trans_less SN_less trans_Id refl_Id
  by (intro SN_order_pair.mul_ext_SN_order_pair, unfold_locales, auto)

definition "E_ord_lin \<E> = {(s \<cdot> \<sigma>, t \<cdot> \<sigma>) | s t \<sigma>. (s, t) \<in> \<E>\<^sup>\<leftrightarrow> \<and> linear_term (s \<cdot> \<sigma>) \<and> linear_term (t \<cdot> \<sigma>) \<and> (s \<cdot> \<sigma>) \<succ> (t \<cdot> \<sigma>)}"

lemma E_ord_lin_mono: "\<E> \<subseteq> \<E>' \<Longrightarrow> E_ord_lin \<E> \<subseteq> E_ord_lin \<E>'" unfolding E_ord_lin_def by auto

lemma mset_two:
  assumes "s \<succ> u"
  shows "{#s, t#} \<succ>\<^sub>m\<^sub>u\<^sub>l {#u, t#}"
proof -
  from assms s_mul_ext_singleton have su: "{#s#} \<succ>\<^sub>m\<^sub>u\<^sub>l {#u#}" by auto
  from ns_mul_ext_refl [OF refl_encompeq] have "({#t#}, {#t#}) \<in> mulsucceq" by auto
  from s_ns_mul_ext_union_compat [OF su this] show ?thesis
    using add.commute add_mset_add_single by metis
qed

lemma mset_two2:
  assumes "s \<succ> u"
  shows "{#t, s#} \<succ>\<^sub>m\<^sub>u\<^sub>l {#t, u#}"
  using mset_two [OF assms] add_mset_commute by (metis (no_types, lifting))

lemma Einf_to_Ew:"E\<^sub>\<infinity> \<subseteq> (rstep R\<^sub>\<infinity>)\<^sup>* O E\<^sub>\<omega>\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*"
proof-
  { fix s t
    assume "(s,t) \<in> E\<^sub>\<infinity>"
    then have "(s,t) \<in> (rstep R\<^sub>\<infinity>)\<^sup>* O E\<^sub>\<omega>\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*"
    proof (induct "{#s,t#}" arbitrary: s t rule: SN_induct [OF mulsucc.SN])
      case 1
      note IH = this
      show ?case proof(cases "(s,t) \<in> E\<^sub>\<omega>", fast)
        case False
        with Einf_without_Ew[OF 1(2)] obtain i where i:"(s, t) \<in> E i" "(s, t) \<notin> E (Suc i)" by auto
    have S:"\<S> (R (Suc i)) (E (Suc i)) \<subseteq> \<S> R\<^sub>\<infinity> E\<^sub>\<infinity>" using E_ord_mono by (metis Sup_upper range_eqI sup.mono)
        let ?E = "E (Suc i)" and ?R = "R (Suc i)"
        from i oKBi_E_supset_lin[OF lin_irun] consider
          "(s, t) \<in> rstep ?R O ?E" | "(s, t) \<in> ?E O (rstep ?R)\<inverse>" | "(s, t) \<in> (?R\<^sup>\<leftrightarrow>)\<^sup>=" by blast
        then show ?thesis proof(cases)
          case 1
          then obtain u where su:"(s,u) \<in> rstep ?R" and ut:"(u,t) \<in> ?E" by auto
          from su rstep_mono[of ?R "R\<^sub>\<infinity>"] have step:"(s,u) \<in> rstep R\<^sub>\<infinity>" by auto
          from compatible_rstep_imp_less[OF Ri_less su] mset_two have "{#s,t#} \<succ>\<^sub>m\<^sub>u\<^sub>l {#u,t#}" by auto
          with ut IH(1)[of u t] have "(u, t) \<in> (rstep R\<^sub>\<infinity>)\<^sup>* O E\<^sub>\<omega>\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*" by blast
          then obtain v where "(u, v) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" "(v, t) \<in> E\<^sub>\<omega>\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*" by auto
          with converse_rtrancl_into_rtrancl[OF step this(1)] show ?thesis by auto
        next
          case 2
          then obtain u where su:"(s,u) \<in> ?E" and tu:"(t,u) \<in> rstep ?R" by fast
          with rstep_mono[of ?R "R\<^sub>\<infinity>"] have step:"(t,u) \<in> rstep R\<^sub>\<infinity>" by auto
          from compatible_rstep_imp_less[OF Ri_less tu] mset_two2 have "{#s,t#} \<succ>\<^sub>m\<^sub>u\<^sub>l {#s,u#}" by auto
          with su IH(1)[of s u] have "(s, u) \<in> (rstep R\<^sub>\<infinity>)\<^sup>* O E\<^sub>\<omega>\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*" by blast
          then obtain v where "(v, u) \<in> ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*" "(s, v) \<in> (rstep R\<^sub>\<infinity>)\<^sup>* O E\<^sub>\<omega>\<^sup>=" by auto
          with rtrancl_into_rtrancl[OF this(1), of t] step show ?thesis by blast
        next
          case 3
          have "?R \<subseteq> rstep R\<^sub>\<infinity>" unfolding rstep_union using rstep_rule by auto
          with 3 show ?thesis by blast
        qed
      qed
    qed
  }
  then show ?thesis ..
qed

lemma Einf_to_Ew_rstep:"rstep E\<^sub>\<infinity> \<subseteq> (rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*"
proof
  fix s t
  assume "(s,t) \<in> rstep E\<^sub>\<infinity>"
  then obtain l r C \<sigma> where lr:"(l,r) \<in> E\<^sub>\<infinity>" "s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by fast
  with Einf_to_Ew have "(l,r) \<in> (rstep R\<^sub>\<infinity>)\<^sup>* O E\<^sub>\<omega>\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*" by blast
  then obtain u v where uv:"(l,u) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" "(u,v) \<in> E\<^sub>\<omega>\<^sup>=" "(v,r) \<in> ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*" by auto
  note c = ctxt.closedD[OF ctxt_closed_rsteps subst.closedD[OF subst_closed_rsteps]]
  with uv(1) have 1:"(C\<langle>l\<cdot>\<sigma>\<rangle>,C\<langle>u\<cdot>\<sigma>\<rangle>) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" by blast
  from uv(2) have 2:"(C\<langle>u\<cdot>\<sigma>\<rangle>,C\<langle>v\<cdot>\<sigma>\<rangle>) \<in> (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>=" by auto
  from c uv(3) have 3:"(C\<langle>v\<cdot>\<sigma>\<rangle>,C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*"
    by (metis rstep_converse)
  with 1 2 show "(s,t) \<in> (rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*" unfolding lr by auto
qed

lemma rsteps_R_NF_conv:
  assumes "(s, t) \<in> (rstep \<R>)\<^sup>!" and "(s, u) \<in> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(u, t) \<in> (rstep \<R>)\<^sup>!"
proof-
  from assms conv_eq[unfolded oKBi_conversion_ERw] conversion_sym have us:"(u, s) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding sym_def by metis
  from assms(1) have "(s, t) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*" unfolding normalizability_def using conversionI' by blast
  with us have "(u, t) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def by auto
  from CR_NF_conv[OF CR_R _ this] assms show ?thesis unfolding normalizability_def by auto
qed

lemma LCP_exists:
  fixes \<sigma>\<^sub>1 :: "'b \<Rightarrow> ('a, 'b) term" 
  assumes "C\<langle>l\<^sub>1\<cdot>\<sigma>\<^sub>1\<rangle> = l\<^sub>2'\<cdot>\<sigma>\<^sub>2'" and "hole_pos C \<in> fun_poss l\<^sub>2'" and "(l\<^sub>1,r\<^sub>1) \<in> RR" and "(l\<^sub>2',r\<^sub>2') \<in> RR"
  and "(l\<^sub>2' \<succ> r\<^sub>2' \<and> \<not>(r\<^sub>1 \<succ> l\<^sub>1)) \<or> (l\<^sub>1 \<succ> r\<^sub>1 \<and> \<not>(r\<^sub>2' \<succ> l\<^sub>2'))"
  shows "\<exists>\<tau> s t. (s,t) \<in> LCP RR \<and> C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = s \<cdot> \<tau> \<and> r\<^sub>2' \<cdot> \<sigma>\<^sub>2' = t \<cdot> \<tau>"
proof-
  have rl1:"\<exists>p. p \<bullet> (l\<^sub>1, r\<^sub>1) \<in> RR" by (rule exI[of _ 0], insert assms(3), auto)
  from vars_rule_disjoint obtain \<pi>
    where \<pi>: "vars_rule (\<pi> \<bullet> (l\<^sub>2', r\<^sub>2')) \<inter> vars_rule (l\<^sub>1, r\<^sub>1) = {}" ..
  define l\<^sub>2 and r\<^sub>2 and \<sigma>\<^sub>2
    where "l\<^sub>2 = \<pi> \<bullet> l\<^sub>2'" and "r\<^sub>2 = \<pi> \<bullet> r\<^sub>2'" and "\<sigma>\<^sub>2 = (Var \<circ> Rep_perm (-\<pi>)) \<circ>\<^sub>s \<sigma>\<^sub>2'"
  note rename = l\<^sub>2_def r\<^sub>2_def \<sigma>\<^sub>2_def
  from assms(4) have "-\<pi> \<bullet> (l\<^sub>2,r\<^sub>2) \<in> RR" unfolding rename by auto
  then have rl2:"\<exists>p. p \<bullet> (l\<^sub>2,r\<^sub>2) \<in> RR" by (rule exI[of _ "-\<pi>"])
  from \<pi> have vars:"vars_rule (l\<^sub>1,r\<^sub>1) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}"
    unfolding rename rule_pt.permute_prod_eqvt by auto
  define p where "p \<equiv> hole_pos C" 
  from assms(2) have p:"p \<in> fun_poss l\<^sub>2" by (auto simp:rename p_def)
  note poss_p = fun_poss_imp_poss [OF p]
    
  have r_l1:"l\<^sub>2' = -\<pi> \<bullet> l\<^sub>2" by (auto simp:rename)
  from assms(1) have eq:"l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = (l\<^sub>2' \<cdot> \<sigma>\<^sub>2' |_ p)" unfolding p_def by (metis subt_at_hole_pos)
  note subt_l1 = subt_at_subst[OF poss_p]
  from eq[unfolded r_l1 permute_term_subst_apply_term] have eq':"l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = l\<^sub>2 |_ p \<cdot> \<sigma>\<^sub>2"
    unfolding subt_at_subst[OF poss_p] rename using \<open>l\<^sub>2 \<equiv> \<pi> \<bullet> l\<^sub>2'\<close> eq r_l1 subt_l1
    by (metis (full_types) subst_subst_compose term_apply_subst_Var_Rep_perm)
      
  note coinc = coincidence_lemma' [of _ "vars_rule (l\<^sub>1, r\<^sub>1)"]
  define \<sigma> where "\<sigma> x = (if x \<in> vars_rule (l\<^sub>1, r\<^sub>1) then \<sigma>\<^sub>1 x else \<sigma>\<^sub>2 x)" for x
  have "l\<^sub>1 \<cdot> \<sigma> = l\<^sub>1 \<cdot> (\<sigma> |s vars_rule (l\<^sub>1, r\<^sub>1))"
    using coinc[of l\<^sub>1] by (simp add: vars_rule_def)
  also have "\<dots> = l\<^sub>1 \<cdot> (\<sigma>\<^sub>1 |s vars_rule (l\<^sub>1, r\<^sub>1))" by (simp add: \<sigma>_def [abs_def])
  finally have l1_coinc:"l\<^sub>1 \<cdot> \<sigma> = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using coinc[of l\<^sub>1] by (simp add: vars_rule_def)
  have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term l\<^sub>2 = {}"
    using \<pi>[unfolded rename] by (auto simp: vars_rule_def rule_pt.permute_prod_eqvt l\<^sub>2_def)
  have unif: "l\<^sub>1 \<cdot> \<sigma> = (l\<^sub>2 |_ p) \<cdot> \<sigma>"
  proof -
    from disj have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term (l\<^sub>2 |_ p) = {}" 
      using vars_term_subt_at [OF poss_p] by auto
    from l1_coinc have "l\<^sub>1 \<cdot> \<sigma> = (l\<^sub>2 |_ p) \<cdot> \<sigma>\<^sub>2" using eq' by simp
    also have "\<dots> = (l\<^sub>2 |_ p) \<cdot> (\<sigma>\<^sub>2 |s vars_term (l\<^sub>2 |_ p))"
      by (simp add: coincidence_lemma [symmetric])
    also have "\<dots> = (l\<^sub>2 |_ p) \<cdot> (\<sigma> |s vars_term (l\<^sub>2 |_ p))" using disj by (simp add: \<sigma>_def [abs_def])
    finally show ?thesis by (simp add: coincidence_lemma [symmetric])
  qed
    
  define \<mu> where "\<mu> = the_mgu l\<^sub>1 (l\<^sub>2 |_ p)"
  have is_mgu:"is_mgu \<mu> {(l\<^sub>1, l\<^sub>2 |_ p)}" by (rule is_mguI, insert unif the_mgu, auto simp: \<mu>_def)
  with unif obtain \<tau> where \<sigma>: "\<sigma> = \<mu> \<circ>\<^sub>s \<tau>" by (auto simp: is_mgu_def unifiers_def)
  from unif have mgu: "mgu l\<^sub>1 (l\<^sub>2 |_ p) = Some \<mu>"
    unfolding \<mu>_def the_mgu_def
    using unify_complete and unify_sound by (force split: option.splits simp: is_imgu_def mgu_def unifiers_def)
      
  have "r\<^sub>1 \<cdot> \<sigma> = r\<^sub>1 \<cdot> (\<sigma> |s vars_rule (l\<^sub>1, r\<^sub>1))" using coinc[of r\<^sub>1] by (simp add: vars_rule_def)
  also have "\<dots> = r\<^sub>1 \<cdot> (\<sigma>\<^sub>1 |s vars_rule (l\<^sub>1, r\<^sub>1))" by (simp add: \<sigma>_def [abs_def])
  finally have r1_coinc:"r\<^sub>1 \<cdot> \<sigma> = r\<^sub>1 \<cdot> \<sigma>\<^sub>1" using coinc[of r\<^sub>1] by (simp add: vars_rule_def)
      
  note coinc = coincidence_lemma [symmetric]
  have "l\<^sub>2 \<cdot> \<sigma> = l\<^sub>2 \<cdot> (\<sigma> |s vars_term l\<^sub>2)" by (simp add: coinc)
  also have "\<dots> = l\<^sub>2 \<cdot> (\<sigma>\<^sub>2 |s vars_term l\<^sub>2)" using disj by (simp add: \<sigma>_def [abs_def])
  also have "\<dots> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" by (simp add: coinc)
  finally have l2_coinc:"l\<^sub>2 \<cdot> \<sigma> = l\<^sub>2' \<cdot> \<sigma>\<^sub>2'" unfolding rename by simp
  have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term r\<^sub>2 = {}"
    using vars_term_subt_at [OF poss_p] and \<pi>[unfolded rename]
    by (auto simp: vars_rule_def rule_pt.permute_prod_eqvt r\<^sub>2_def)
  have "r\<^sub>2 \<cdot> \<sigma> = r\<^sub>2 \<cdot> (\<sigma> |s vars_term r\<^sub>2)" by (simp add: coinc)
  also have "\<dots> = r\<^sub>2 \<cdot> (\<sigma>\<^sub>2 |s vars_term r\<^sub>2)" using disj by (simp add: \<sigma>_def [abs_def])
  also have "\<dots> = r\<^sub>2 \<cdot> \<sigma>\<^sub>2" by (simp add: coinc)
  finally have r2_coinc:"r\<^sub>2 \<cdot> \<sigma> = r\<^sub>2' \<cdot> \<sigma>\<^sub>2'" unfolding rename by simp

  from assms(5) have oriented:"(l\<^sub>1 \<succ> r\<^sub>1 \<and> \<not> r\<^sub>2 \<succ> l\<^sub>2) \<or> (l\<^sub>2 \<succ> r\<^sub>2 \<and> \<not> r\<^sub>1 \<succ> l\<^sub>1)" unfolding l\<^sub>2_def r\<^sub>2_def
    unfolding permute_term_subst_apply_term
    by (metis subst term_apply_subst_Var_Rep_perm term_pt.permute_minus_cancel(2))

  from assms(1) poss_p hole_pos_id_ctxt have "C = ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<sigma>)"
    unfolding l1_coinc[symmetric] l2_coinc[symmetric] p_def by metis  
  then have cp_left:"C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = (ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<mu>))\<langle>r\<^sub>1 \<cdot> \<mu>\<rangle> \<cdot> \<tau>"
    unfolding subst_apply_term_ctxt_apply_distrib r1_coinc[symmetric]
      ctxt_of_pos_term_subst[OF poss_imp_subst_poss[OF poss_p], symmetric]
      subst_subst_compose[symmetric] \<sigma>[symmetric] by simp
  from subst_subst_compose have cp_right:"r\<^sub>2' \<cdot> \<sigma>\<^sub>2' = r\<^sub>2 \<cdot> \<mu> \<cdot> \<tau>" unfolding r2_coinc[symmetric] \<sigma> by auto
  let ?s = "(ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<mu>))\<langle>r\<^sub>1 \<cdot> \<mu>\<rangle>"
  let ?t = "r\<^sub>2 \<cdot> \<mu>"
  from l1_coinc \<sigma> have eq:"l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = l\<^sub>1 \<cdot> \<mu> \<cdot> \<tau>" by auto
  note facts = rl1 rl2 vars p mgu oriented
  have o:"lin_overlap RR l\<^sub>1 r\<^sub>1 p l\<^sub>2 r\<^sub>2 \<mu>" unfolding lin_overlap_def overlap_def fst_conv using facts
    unfolding the_mgu_def by simp
  show ?thesis unfolding LCP_def by (rule exI[of _ \<tau>], rule exI[of _ ?s], rule exI[of _ ?t],
   unfold mem_Collect_eq, rule conjI, rule exI[of _ l\<^sub>1], rule exI[of _ r\<^sub>1], rule exI[of _ p],
   rule exI[of _ l\<^sub>2], rule exI[of _ r\<^sub>2], rule exI[of _ \<mu>], insert o cp_left cp_right eq,
   unfold subst_apply_term_ctxt_apply_distrib, insert ctxt_of_pos_term_subst[OF poss_p, of \<mu>], auto)
qed


context
  assumes fair:"\<forall>(s, t)\<in> LCP (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>). (s, t) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep R\<^sub>\<omega>)\<^sup>\<down>"
begin

lemma PCP_LCP:
  assumes R_less:"RR \<subseteq> {\<succ>}"
  shows "PCP RR \<subseteq> LCP RR"
proof
  fix s t
  assume "(s, t) \<in> PCP RR"
  then obtain \<mu> l\<^sub>1 r\<^sub>1 p l\<^sub>2 r\<^sub>2 where o: "overlap RR RR (l\<^sub>1, r\<^sub>1) p (l\<^sub>2, r\<^sub>2)"
    and "the_mgu l\<^sub>1 (l\<^sub>2 |_ p) = \<mu>"
    and s: "s = replace_at l\<^sub>2 p r\<^sub>1 \<cdot> \<mu>"
    and t: "t = r\<^sub>2 \<cdot> \<mu>"
    and NF: "\<forall>u \<lhd> l\<^sub>1 \<cdot> \<mu>. u \<in> NF (rstep RR)"
    by (auto simp: PCP_def the_mgu_def mgu_def split: option.splits)
  then have mgu: "mgu l\<^sub>1 (l\<^sub>2 |_ p) = Some \<mu>"
    by (auto simp: the_mgu_def unifiers_def overlap_def split: option.splits dest!: mgu_complete)
  have p: "p \<in> fun_poss l\<^sub>2" using o by (auto simp: overlap_def)
  from o have rules:"\<exists>p. p \<bullet> (l\<^sub>1, r\<^sub>1) \<in> RR" "\<exists>p. p \<bullet> (l\<^sub>2, r\<^sub>2) \<in> RR" "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}"
    unfolding overlap_def by auto
  { fix l r p
    assume "p \<bullet> (l,r) \<in> RR" 
    then have "p \<bullet> l \<succ> p \<bullet> r" using R_less unfolding rule_pt.permute_prod_eqvt by auto
    then have lr:"l \<succ> r" using subst [of "p \<bullet> l" "p \<bullet> r" "sop (-p)"] by auto
    from trans[OF this] SN_imp_acyclic[OF SN_less] trans have "\<not>(r \<succ> l)" unfolding acyclic_def by blast
    with lr have "l \<succ> r \<and> \<not>(r \<succ> l)" by auto
  }
  with rules R_less have oriented:"l\<^sub>1 \<succ> r\<^sub>1" "\<not>(r\<^sub>2 \<succ> l\<^sub>2)" by auto
  from rules p mgu oriented
  have overlap:"lin_overlap RR l\<^sub>1 r\<^sub>1 p l\<^sub>2 r\<^sub>2 \<mu>"
    unfolding lin_overlap_def fst_conv snd_conv s t by auto
  then show "(s, t) \<in> LCP RR" unfolding LCP_def s t by fast
qed

lemma Ew_empty_CR_Rw_linear:
  assumes "E\<^sub>\<omega> = {}"
  shows "CR (rstep R\<^sub>\<omega>)"
proof-
  from fair PCP_LCP[OF Rw_less] have fair:"PCP R\<^sub>\<omega> \<subseteq> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow> \<union> (rstep R\<^sub>\<omega>)\<^sup>\<down>" unfolding assms by auto
  interpret okb_irun_nonfailing by (unfold_locales, insert fair assms, auto)
  from Ew_empty_implies_CR_Rw show ?thesis by auto
qed

lemma linear_peak_cases:
  assumes step:"(s,t) \<in> rstep_r_p_s (R\<^sub>\<omega>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) (l\<^sub>1,r\<^sub>1) p\<^sub>1 \<sigma>\<^sub>1" and Rstep:"(t,u) \<in> rstep R\<^sub>\<omega>" and "\<not> l\<^sub>1 \<succ> r\<^sub>1"
  shows "(s,u) \<in> (rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*"
proof-
  from step obtain C where lr:"(l\<^sub>1,r\<^sub>1) \<in> R\<^sub>\<omega>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "s = C\<langle>l\<^sub>1\<cdot>\<sigma>\<^sub>1\<rangle>" "t = C\<langle>r\<^sub>1\<cdot>\<sigma>\<^sub>1\<rangle>" "p\<^sub>1 = hole_pos C"
    unfolding rstep_r_p_s_def mem_Collect_eq split fst_conv snd_conv 
    by (metis (mono_tags, lifting) hole_pos_ctxt_of_pos_term)
  from lr Rw_subset_Rinf have lr':"(l\<^sub>1, r\<^sub>1) \<in> R\<^sub>\<infinity>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" by auto
  from Rstep obtain D l\<^sub>2 r\<^sub>2 \<sigma>\<^sub>2 where lr2:"(l\<^sub>2,r\<^sub>2) \<in> R\<^sub>\<omega>" "t = D\<langle>l\<^sub>2\<cdot>\<sigma>\<^sub>2\<rangle>" "u = D\<langle>r\<^sub>2\<cdot>\<sigma>\<^sub>2\<rangle>" by blast 
  let ?p2 = "hole_pos D"
  note eq = lr(3)[unfolded lr2(2), simplified]
  then have eq'[simp]: "C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> |_ ?p2 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using subt_at_hole_pos by metis
  (* do a CP Lemma-like analysis (standard CP lemma requires variable condition) *)
  consider "p\<^sub>1 \<le>\<^sub>p ?p2" | "?p2 \<le>\<^sub>p p\<^sub>1" | "parallel_pos p\<^sub>1 ?p2" using pos_cases[of p\<^sub>1 ?p2] by auto
  then show ?thesis proof(cases)
    case 1
    with suffix_exists obtain q where q:"?p2 = p\<^sub>1 @ q" by metis
    from lr(3) q have DC:"D = C \<circ>\<^sub>c (ctxt_of_pos_term q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1))" unfolding lr2 lr(4)
      by (metis ctxt_of_pos_term_append ctxt_of_pos_term_hole_pos hole_pos_poss subt_at_hole_pos)
    from eq[unfolded DC] have eq'':"(ctxt_of_pos_term q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1))\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = r\<^sub>1 \<cdot> \<sigma>\<^sub>1"
      unfolding ctxt_ctxt_compose by auto
    show ?thesis proof(cases "q \<in> fun_poss r\<^sub>1")
      case False (* variable overlap *)
      note q_not_in_fun_poss_r1 = this
      from lr lr2(2) q have p_r\<sigma>:"q \<in> poss (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)" by (metis hole_pos_poss hole_pos_poss_conv)
      from poss_subst_apply_term[OF this q_not_in_fun_poss_r1] obtain q\<^sub>1 q\<^sub>2 x
        where p[simp]: "q = q\<^sub>1 @ q\<^sub>2" and q\<^sub>1: "q\<^sub>1 \<in> poss r\<^sub>1"
          and rq\<^sub>1: "r\<^sub>1 |_ q\<^sub>1 = Var x" and q\<^sub>2: "q\<^sub>2 \<in> poss (\<sigma>\<^sub>1 x)" by auto
      from eq' have [simp]: "r\<^sub>1 \<cdot> \<sigma>\<^sub>1 |_ q = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using subt_at_hole_pos subt_at_append[OF hole_pos_poss]
        unfolding q lr(4) by metis
      with rq\<^sub>1 q\<^sub>2 subt_at_append p_r\<sigma> q\<^sub>1 have at_q2[simp]: "\<sigma>\<^sub>1 x |_ q\<^sub>2 = l\<^sub>2 \<cdot>\<sigma>\<^sub>2" unfolding p by auto

      let ?u = "replace_at (\<sigma>\<^sub>1 x) q\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)"
      define \<sigma>\<^sub>1' where "\<sigma>\<^sub>1' y = (if y = x then ?u else \<sigma>\<^sub>1 y)" for y
      have "(\<sigma>\<^sub>1 x, \<sigma>\<^sub>1' x) \<in> rstep R\<^sub>\<omega>"
      proof -
        let ?C = "ctxt_of_pos_term q\<^sub>2 (\<sigma>\<^sub>1 x)"
        have "(?C\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>, ?C\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>) \<in> rstep R\<^sub>\<omega>" using lr2 by blast
        then show ?thesis using q\<^sub>2 by (simp add: \<sigma>\<^sub>1'_def replace_at_ident)
      qed
      then have *: "\<And>x. (\<sigma>\<^sub>1 x, \<sigma>\<^sub>1' x) \<in> (rstep R\<^sub>\<omega>)\<^sup>=" by (auto simp: \<sigma>\<^sub>1'_def)

      then have "(l\<^sub>1 \<cdot> \<sigma>\<^sub>1, l\<^sub>1 \<cdot> \<sigma>\<^sub>1') \<in> (rstep R\<^sub>\<omega>)\<^sup>=" proof(cases "x \<in> vars_term l\<^sub>1")
        case True
        from lr(1) Ew_linear Rw_linear have lin:"linear_term l\<^sub>1" unfolding linear_trs_def by auto
        from linear_term_unique_var_pos[OF lin True] obtain q\<^sub>l where
          ql:"q\<^sub>l \<in> poss l\<^sub>1 \<and> l\<^sub>1 |_ q\<^sub>l = Var x" by auto
        let ?C = "ctxt_of_pos_term q\<^sub>l (l\<^sub>1\<cdot>\<sigma>\<^sub>1)"
        from linear_term_replace_in_subst[OF lin, of q\<^sub>l] ql \<sigma>\<^sub>1'_def have 1:"l\<^sub>1\<cdot>\<sigma>\<^sub>1' = ?C\<langle>?u\<rangle>" by metis
        have 2:"(?C\<langle>(ctxt_of_pos_term q\<^sub>2 (\<sigma>\<^sub>1 x))\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>\<rangle>,?C\<langle>?u\<rangle>) \<in> (rstep R\<^sub>\<omega>)" using lr2 by auto
        from ql q\<^sub>2 at_q2 have "?C\<langle>(ctxt_of_pos_term q\<^sub>2 (\<sigma>\<^sub>1 x))\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>\<rangle> = l\<^sub>1 \<cdot> \<sigma>\<^sub>1"
          by (simp add: replace_at_ident)
        with 1 2 show ?thesis by auto 
      next
        case False
        with term_subst_eq_conv show ?thesis unfolding \<sigma>\<^sub>1'_def by fastforce
      qed
      then have "(C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>, C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1'\<rangle>) \<in> (rstep R\<^sub>\<omega>)\<^sup>=" by auto
      with rstep_mono[OF Rw_subset_Rinf] have left:"(C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>, C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1'\<rangle>) \<in> (rstep R\<^sub>\<infinity>)\<^sup>=" by auto
      from lr(1) Rw_subset_Rinf have right':"(C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1'\<rangle>, C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1'\<rangle>) \<in> rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
        by (auto simp: rstep_simps)
      from lr(1) Ew_linear Rw_linear have lin:"linear_term r\<^sub>1" unfolding linear_trs_def by auto
      from linear_term_replace_in_subst[OF lin q\<^sub>1 rq\<^sub>1, of \<sigma>\<^sub>1] have "(ctxt_of_pos_term q\<^sub>1 (r\<^sub>1 \<cdot> \<sigma>\<^sub>1))\<langle>?u\<rangle> = r\<^sub>1 \<cdot> \<sigma>\<^sub>1'"
        using \<sigma>\<^sub>1'_def by auto
      with p rq\<^sub>1 q\<^sub>1 q\<^sub>2 have "(ctxt_of_pos_term q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1))\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = r\<^sub>1 \<cdot> \<sigma>\<^sub>1'"
        by (simp add: ctxt_of_pos_term_append)
      then have u:"C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1'\<rangle> = u" unfolding lr2 DC ctxt_ctxt_compose ctxt_eq by auto
      from right' have "(C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1'\<rangle>, C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1'\<rangle>) \<in> rstep (R\<^sub>\<infinity>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" unfolding rstep_converse
        using converse_iff[of _ _ "rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"] symcl_converse by (auto simp: rstep_simps)
      with left have "(s,u) \<in> (rstep R\<^sub>\<infinity>)\<^sup>= O (rstep (R\<^sub>\<infinity>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>="
        unfolding u lr(2)[symmetric] by auto
      then show ?thesis unfolding rstep_union[of "R\<^sub>\<infinity>\<inverse>"] unfolding relcomp_distrib by auto
    next
      case True (* proper overlap *)
      note st = lr[unfolded intp_actxt.simps]
      note tu = lr2[unfolded intp_actxt.simps]
      let ?C = "ctxt_of_pos_term q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
      from hole_pos_ctxt_of_pos_term[OF poss_imp_subst_poss, of q] True have qC:"hole_pos ?C = q"
        using fun_poss_imp_poss by auto
      let ?C = "ctxt_of_pos_term q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
      from Rw_less lr2 assms(3) have "l\<^sub>2 \<succ> r\<^sub>2 \<and> \<not> l\<^sub>1 \<succ> r\<^sub>1" by auto
      with LCP_exists[OF eq'', unfolded qC, OF True, of _ "R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>"] lr(1) lr2(1) have
        "\<exists>\<tau>' s t. (s, t) \<in> LCP (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) \<and> (ctxt_of_pos_term q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1))\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = s \<cdot> \<tau>' \<and> l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = t \<cdot> \<tau>'" by auto
      then obtain \<rho> s\<^sub>0 t\<^sub>0 where lcp:"(s\<^sub>0, t\<^sub>0) \<in> LCP (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" and
        id:"(ctxt_of_pos_term q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1))\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle> = s\<^sub>0 \<cdot> \<rho>" "l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = t\<^sub>0 \<cdot> \<rho>" by auto

      with fair consider "(s\<^sub>0, t\<^sub>0) \<in> rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" | "(s\<^sub>0, t\<^sub>0) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>" by (auto simp: rstep_simps)
      thus ?thesis proof(cases)
        case 1
      from rstep_ctxt[OF rstep_subst[OF this], of C \<rho>] id have "(D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>, C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>) \<in> rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)"
        unfolding DC ctxt_ctxt_compose lr by auto
      with lr(2) lr2(3) have Einf_step:"(s, u) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>" unfolding rstep_simps(5) by fastforce
      with Einf_to_Ew_rstep have su:"(s, u) \<in> ((rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*)\<^sup>\<leftrightarrow>" by blast
      have "((rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*)\<inverse> = ((rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*)"
        unfolding converse_relcomp rtrancl_converse converse_converse using O_assoc rstep_converse by blast
      with su show ?thesis by blast
      next
        case 2
        from join_ctxt[OF join_subst_rstep[OF 2]] lr(2) lr2(3) id have "(u, s) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>"
          by (simp add: \<open>l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = t\<^sub>0 \<cdot> \<rho>\<close> DC)
        with join_mono[OF rstep_mono[OF Rw_subset_Rinf]] have "(u, s) \<in> (rstep R\<^sub>\<infinity>)\<^sup>\<down>" by auto
        from joinD[OF this] obtain v where "(u, v) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" "(s, v) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" by auto
        with rtrancl_converse show ?thesis by blast 
      qed
    qed
  next
    case 2
    with suffix_exists obtain q where q:"p\<^sub>1 = ?p2 @ q" by metis
    from lr(3) q subt_at_hole_pos have DC:"C = D \<circ>\<^sub>c (ctxt_of_pos_term q (l\<^sub>2 \<cdot> \<sigma>\<^sub>2))" unfolding lr2 lr(4)
      using ctxt_of_pos_term_append[OF hole_pos_poss] ctxt_of_pos_term_hole_pos by metis
    from eq[unfolded DC] have eq'':"(ctxt_of_pos_term q (l\<^sub>2 \<cdot> \<sigma>\<^sub>2))\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
      unfolding ctxt_ctxt_compose by auto
    show ?thesis proof(cases "q \<in> fun_poss l\<^sub>2")
      case False (* variable overlap *)
      note q_not_in_fun_poss_l2 = this
      from lr lr2(2) q have q_l\<^sub>2\<sigma>:"q \<in> poss (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" by (metis hole_pos_poss hole_pos_poss_conv)
      from poss_subst_apply_term[OF this q_not_in_fun_poss_l2] obtain q\<^sub>1 q\<^sub>2 x
        where p[simp]: "q = q\<^sub>1 @ q\<^sub>2" and q\<^sub>1: "q\<^sub>1 \<in> poss l\<^sub>2"
          and l\<^sub>2q\<^sub>1: "l\<^sub>2 |_ q\<^sub>1 = Var x" and q\<^sub>2: "q\<^sub>2 \<in> poss (\<sigma>\<^sub>2 x)" by auto
      from eq have [simp]: "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 |_ q = r\<^sub>1 \<cdot> \<sigma>\<^sub>1"
        unfolding DC q ctxt_ctxt_compose ctxt_eq using replace_at_subt_at[OF q_l\<^sub>2\<sigma>] by metis
      with l\<^sub>2q\<^sub>1 q\<^sub>2 subt_at_append q_l\<^sub>2\<sigma> q\<^sub>1 have at_q2[simp]: "\<sigma>\<^sub>2 x |_ q\<^sub>2 = r\<^sub>1 \<cdot>\<sigma>\<^sub>1" unfolding p by auto

      let ?u = "replace_at (\<sigma>\<^sub>2 x) q\<^sub>2 (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
      define \<sigma>\<^sub>2' where "\<sigma>\<^sub>2' y = (if y = x then ?u else \<sigma>\<^sub>2 y)" for y
      have "(\<sigma>\<^sub>2 x, \<sigma>\<^sub>2' x) \<in> rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
      proof -
        let ?C = "ctxt_of_pos_term q\<^sub>2 (\<sigma>\<^sub>2 x)"
        from rstepI[OF lr', of _ ?C \<sigma>\<^sub>1] have "(?C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>, ?C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>) \<in> rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
          unfolding rstep_union rstep_converse[of "R\<^sub>\<infinity>", symmetric] by fastforce
        then show ?thesis using q\<^sub>2 by (simp add: \<sigma>\<^sub>2'_def replace_at_ident)
      qed
      then have *: "\<And>x. (\<sigma>\<^sub>2 x, \<sigma>\<^sub>2' x) \<in> (rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>=" by (auto simp: \<sigma>\<^sub>2'_def)

      then have "(r\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<sigma>\<^sub>2') \<in> (rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>=" proof(cases "x \<in> vars_term r\<^sub>2")
        case True
        from lr2(1) Rw_linear have lin:"linear_term r\<^sub>2" unfolding linear_trs_def by auto
        from linear_term_unique_var_pos[OF lin True] obtain q\<^sub>l where
          ql:"q\<^sub>l \<in> poss r\<^sub>2" "r\<^sub>2 |_ q\<^sub>l = Var x" by auto
        let ?C = "ctxt_of_pos_term q\<^sub>l (r\<^sub>2\<cdot>\<sigma>\<^sub>2)"
        from linear_term_replace_in_subst[OF lin ql] \<sigma>\<^sub>2'_def have 1:"r\<^sub>2\<cdot>\<sigma>\<^sub>2' = ?C\<langle>?u\<rangle>" by metis
        have 2:"(?C\<langle>(ctxt_of_pos_term q\<^sub>2 (\<sigma>\<^sub>2 x))\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>\<rangle>,?C\<langle>?u\<rangle>) \<in> rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" using lr' by auto
        from ql q\<^sub>2 at_q2 have "?C\<langle>(ctxt_of_pos_term q\<^sub>2 (\<sigma>\<^sub>2 x))\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>\<rangle> = r\<^sub>2 \<cdot> \<sigma>\<^sub>2"
          by (simp add: replace_at_ident)
        with 1 2 show ?thesis by auto 
      next
        case False
        with term_subst_eq_conv show ?thesis unfolding \<sigma>\<^sub>2'_def by fastforce
      qed
      then have right:"(D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>, D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2'\<rangle>) \<in> (rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>=" by auto
      then have right:"(D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2'\<rangle>, D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>) \<in> (rstep (R\<^sub>\<infinity>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>="
        unfolding rstep_union[of _ " E\<^sub>\<omega>\<^sup>\<leftrightarrow>"] Un_iff rstep_converse converse_iff by auto
      from lr2(1) have "(D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2'\<rangle>, D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2'\<rangle>) \<in> rstep R\<^sub>\<omega>" by fast
      with rstep_mono[OF Rw_subset_Rinf] have left:"(D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2'\<rangle>, D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2'\<rangle>) \<in> rstep R\<^sub>\<infinity>" by auto
      from lr2(1) Rw_linear have lin:"linear_term l\<^sub>2" unfolding linear_trs_def by auto
      from linear_term_replace_in_subst[OF lin q\<^sub>1 l\<^sub>2q\<^sub>1, of \<sigma>\<^sub>2] have "(ctxt_of_pos_term q\<^sub>1 (l\<^sub>2 \<cdot> \<sigma>\<^sub>2))\<langle>?u\<rangle> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2'"
        using \<sigma>\<^sub>2'_def by simp
      with p l\<^sub>2q\<^sub>1 q\<^sub>1 q\<^sub>2 have "(ctxt_of_pos_term q (l\<^sub>2 \<cdot> \<sigma>\<^sub>2))\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2'"
        by (simp add: ctxt_of_pos_term_append)
      with lr have s:"s = D\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2'\<rangle>" unfolding lr DC ctxt_ctxt_compose ctxt_eq by auto
      from right left have "(s,u) \<in> (rstep R\<^sub>\<infinity>) O (rstep (R\<^sub>\<infinity>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>="
        unfolding s lr2(3)[symmetric] using converse_iff by auto
      then show ?thesis unfolding rstep_union relcomp_distrib by auto
    next
      case True (* proper overlap *)
      note st = lr[unfolded intp_actxt.simps]
      note tu = lr2[unfolded intp_actxt.simps]
      let ?C = "ctxt_of_pos_term q (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)"
      from hole_pos_ctxt_of_pos_term[OF poss_imp_subst_poss, OF fun_poss_imp_poss, OF True] have qC:"hole_pos ?C = q"
        using fun_poss_imp_poss by auto
      let ?C = "ctxt_of_pos_term q (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
      from Rw_less lr2 assms(3) have "l\<^sub>2 \<succ> r\<^sub>2 \<and> \<not> l\<^sub>1 \<succ> r\<^sub>1" by auto
      with LCP_exists[OF eq'', unfolded qC, OF True, of l\<^sub>1 "R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>"] lr(1) lr2(1) have
        "\<exists>\<tau>' s t. (s, t) \<in> LCP (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) \<and> (ctxt_of_pos_term q (l\<^sub>2 \<cdot> \<sigma>\<^sub>2))\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = s \<cdot> \<tau>' \<and> r\<^sub>2 \<cdot> \<sigma>\<^sub>2 = t \<cdot> \<tau>'" by auto
      then obtain \<rho> s\<^sub>0 t\<^sub>0 where lcp:"(s\<^sub>0, t\<^sub>0) \<in> LCP (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" and
        id:"(ctxt_of_pos_term q (l\<^sub>2 \<cdot> \<sigma>\<^sub>2))\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = s\<^sub>0 \<cdot> \<rho>" "r\<^sub>2 \<cdot> \<sigma>\<^sub>2 = t\<^sub>0 \<cdot> \<rho>" by auto

      with fair consider "(s\<^sub>0, t\<^sub>0) \<in> rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)" | "(s\<^sub>0, t\<^sub>0) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>" by (auto simp: rstep_simps)
      thus ?thesis proof(cases)
        case 1
      from rstep_ctxt[OF rstep_subst[OF this], of D \<rho>] have "(C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>, D\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>) \<in> rstep (E\<^sub>\<infinity>\<^sup>\<leftrightarrow>)"
        unfolding id[symmetric] DC ctxt_ctxt_compose by auto
      then have Einf_step:"(s, u) \<in> (rstep E\<^sub>\<infinity>)\<^sup>\<leftrightarrow>" unfolding lr(2) lr2(3) rstep_simps(5) by simp
      with Einf_to_Ew_rstep have su:"(s, u) \<in> ((rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*)\<^sup>\<leftrightarrow>" by blast
      have "((rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*)\<inverse> = ((rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*)"
        unfolding converse_relcomp rtrancl_converse converse_converse using O_assoc rstep_converse by blast
      with su show ?thesis by blast
      next
        case 2
        from join_ctxt[OF join_subst_rstep[OF 2]] lr(2) lr2(3) id DC have "(u, s) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>"
          by (simp add: \<open>\<And>\<sigma> C. (C\<langle>s\<^sub>0 \<cdot> \<sigma>\<rangle>, C\<langle>t\<^sub>0 \<cdot> \<sigma>\<rangle>) \<in> (rstep R\<^sub>\<omega>)\<^sup>\<down>\<close> join_sym)
        with join_mono[OF rstep_mono[OF Rw_subset_Rinf]] have "(u, s) \<in> (rstep R\<^sub>\<infinity>)\<^sup>\<down>" by auto
        from joinD[OF this] obtain v where "(u, v) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" "(s, v) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" by auto
        with rtrancl_converse show ?thesis by blast 
      qed
    qed
  next
    case 3
    from lr' lr have ts:"(t, s) \<in> rstep_r_p_s (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) (r\<^sub>1, l\<^sub>1) p\<^sub>1 \<sigma>\<^sub>1"
      unfolding rstep_r_p_s_def mem_Collect_eq by auto
    from lr2 Rw_subset_Rinf have tu:"(t, u) \<in> rstep_r_p_s R\<^sub>\<infinity> (l\<^sub>2, r\<^sub>2) ?p2 \<sigma>\<^sub>2"
      unfolding rstep_r_p_s_def mem_Collect_eq by auto
    let ?v = "(ctxt_of_pos_term p\<^sub>1 u)\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>"
    from parallel_steps[OF ts tu 3] have sv:"(s,?v) \<in> rstep R\<^sub>\<infinity>" and "(u,?v) \<in> rstep (R\<^sub>\<infinity> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
      using rstep_r_p_s_imp_rstep by auto
    from this(2) rstep_converse converse_iff have "(?v,u) \<in> rstep (R\<^sub>\<infinity>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by blast
    with sv have "(s,u) \<in> (rstep R\<^sub>\<infinity> O rstep (R\<^sub>\<infinity>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>))" by auto
    then show ?thesis unfolding rstep_union[of "R\<^sub>\<infinity>\<inverse>"] relcomp_distrib Un_iff using r_into_rtrancl by auto
  qed
qed

lemma Rinf_Rw_msteps:"(l,r) \<in> R\<^sub>\<infinity> \<Longrightarrow> \<exists>y S. (l,y) \<in> rstep R\<^sub>\<omega> \<and> (\<forall>s \<in># S. l \<succ> s) \<and> (y,r) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" 
proof (induct "(l,r)" arbitrary: l r rule: SN_induct [OF SN_lexless])
  case 1
  note IH = this
  show ?case proof(cases "(l,r) \<in> R\<^sub>\<omega>")
    case True
    show ?thesis by (rule exI[of _ r],rule exI[of _ "{#}"], insert rstep_rule[OF True], auto)
  next
    case False
    with Rinf_without_Rw 1(2) obtain j where j:"(l, r) \<in> R j" "(l, r) \<notin> R (Suc j)" by auto
    let ?E = "E (Suc j)" and ?R = "R (Suc j)"
    from oKBilin_R_supset[OF lin_irun, of j] j consider
      "(l, r) \<in> encstep2 {} ?R O ?E" | "(l, r) \<in> ?R O (rstep ?R)\<inverse>" by auto
    then show ?thesis proof(cases)
      case 1
      then obtain u where u:"(l, u) \<in> encstep2 {} ?R" "(u,r) \<in> ?E" by blast
      from u(1) obtain l' r' C \<sigma> where lr':
        "(l',r') \<in> ?R" "l = C\<langle>l' \<cdot> \<sigma>\<rangle>" "u = C\<langle>r' \<cdot> \<sigma>\<rangle>" "l' \<lhd>\<cdot> l" unfolding encstep2.simps by auto
      then have l_l0: "l \<cdot>\<succ> l'" unfolding lessencp_def by auto
      then have "((l,r), (l',r')) \<in> lexless" by simp
      from IH(1)[OF this] lr'(1) obtain v S' where v:
        "(l', v) \<in> rstep R\<^sub>\<omega>" "\<forall>s\<in>#S'. l' \<succ> s" "(v, r') \<in> (mstep S' (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
      let ?v = "C\<langle>v\<cdot>\<sigma>\<rangle>"
      from v(1) have step:"(l, ?v) \<in> rstep R\<^sub>\<omega>" unfolding lr' by auto
      define S where "S \<equiv> {#C\<langle>u \<cdot> \<sigma>\<rangle>. u \<in># S'#}"
      define T where "T \<equiv> {#C\<langle>u \<cdot> \<sigma>\<rangle>. u \<in># S'#} + {#u,r#}"
      have ST:"\<forall>s\<in>#S. \<exists>t\<in>#T. t \<succeq> s" unfolding S_def T_def by auto
      from v(2) ctxt[OF subst, of _ _ C \<sigma>] have lS:"\<forall>s\<in>#S. l \<succ> s" unfolding S_def lr' by auto
      from msteps_subst_ctxt[OF v(3)] have "(?v, u) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
        unfolding lr' S_def by auto
      with msteps_succeq_mono[OF ST] have m1:"(?v, u) \<in> (mstep T (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
      from u(2) have "(u,r) \<in> mstep T (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>)" unfolding mstep_def mem_Collect_eq T_def by auto
      with ERi_subset_ERw[of T] have "(u, r) \<in> (mstep T (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
      with transD[OF conversion_trans] m1 have msteps:"(?v, r) \<in> (mstep T (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by metis
      from ostep_imp_less[OF Ri_less] Ri_less IH(2) encstep2_ostep[OF u(1)] have "l \<succ> u \<and> l \<succ> r"
        using Rinf_less by fast
      with lS have lT:"\<forall>t\<in>#T. l \<succ> t" unfolding T_def S_def by auto
      show ?thesis by (rule exI[of _ ?v], rule exI[of _ T], insert step lT msteps, auto)
    next
      case 2
      then obtain u where u:"(l, u) \<in> R (Suc j)" "(r,u) \<in> rstep (R (Suc j))" by blast
      with compatible_rstep_imp_less[OF Ri_less] have "r \<succ> u" by auto
      then have "((l,r), (l,u)) \<in> lexless" unfolding lex_two.simps mem_Collect_eq lessencp_def by fast
      from IH(1)[OF this] u(1) obtain y S 
        where yS:"(l, y) \<in> rstep R\<^sub>\<omega>" "\<forall>t\<in>#S. l \<succ> t" "(y, u) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
      define T where "T \<equiv> S + {#r,u#}"
      from Ri_less compatible_rstep_imp_less[OF Ri_less] IH(2) u(2) have gt:"l \<succ> r \<and> l \<succ> u"
        using trans[of l r u] by auto
      with yS(2) have T:"\<forall>t\<in>#T. l \<succ> t" unfolding T_def by simp
      from insert u(2) gt have "(r,u) \<in> mstep T ?R" unfolding mstep_def mem_Collect_eq T_def
        by auto
      then have "(r,u) \<in> mstep T (E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>)" using mstep_mono[of ?R "E\<^sub>\<infinity> \<union> R\<^sub>\<infinity>"] by fast
      with ERi_subset_ERw[of T] have ru:"(r, u) \<in> (mstep T (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
      have ST:"\<forall>s\<in>#S. \<exists>t\<in>#T. t \<succeq> s" unfolding T_def by auto
      from msteps_succeq_mono[OF ST] yS(3) have "(y, u) \<in> (mstep T (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
      with ru transD[OF conversion_trans] have msteps:"(y, r) \<in> (mstep T (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
        unfolding conversion_inv[of r] by metis
      show ?thesis by (rule exI[of _ y], rule exI[of _ T], insert step yS T msteps, auto)
    qed
  qed
qed

lemma Rinf_step_Rw_msteps:
  assumes "(s,t) \<in> rstep R\<^sub>\<infinity>"
  shows "\<exists>u S. (s,u) \<in> rstep R\<^sub>\<omega> \<and> (\<forall>t\<in>#S. s \<succ> t) \<and> (u,t) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" 
proof-
  from assms obtain C \<sigma> l r where lr:"(l,r) \<in> R\<^sub>\<infinity>" "s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by fast
  from Rinf_Rw_msteps[OF lr(1)] obtain u S where uS:
    "(l, u) \<in> rstep R\<^sub>\<omega>" "\<forall>t\<in>#S. l \<succ> t" "(u, r) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  then have step:"(s, C\<langle>u\<cdot>\<sigma>\<rangle>) \<in> rstep R\<^sub>\<omega>" unfolding lr by auto
  define T where "T \<equiv> {#C\<langle>u \<cdot> \<sigma>\<rangle>. u \<in># S#}"
  from uS(2) ctxt[OF subst, of _ _ C \<sigma>] have cover:"\<forall>t\<in>#T. s \<succ> t" unfolding T_def lr by auto
  from msteps_subst_ctxt[OF uS(3), of C \<sigma>] have "(C\<langle>u \<cdot> \<sigma>\<rangle>, t) \<in> (mstep T (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding T_def lr by argo
  with step cover show ?thesis by auto
qed

lemma Rinf_step_ERw_msteps_src:
  assumes "(s,t) \<in> rstep R\<^sub>\<infinity>"
  shows "(s,t) \<in> (mstep {#s#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof-
  from assms Rinf_step_Rw_msteps obtain u S where
    rstep\<^sub>0:"(s,u) \<in> rstep R\<^sub>\<omega>" and S:"\<forall>t\<in>#S. s \<succ> t" and ut:"(u,t) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
  from rstep\<^sub>0 compatible_rstep_imp_less Rw_less have "s \<succ> u" by auto
  with rstep\<^sub>0 have su:"(s,u) \<in> mstep {#s#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>)" unfolding mstep_def mem_Collect_eq by auto
  from mstep_succeq_mono[of S "{#s#}"] S have "mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>) \<subseteq> mstep {#s#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>)" by auto
  from conversion_mono[OF this] ut have "(u, t) \<in> (mstep {#s#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with r_into_rtrancl[OF su, THEN conversionI'] show ?thesis unfolding conversion_def
    using rtrancl_trans by auto
qed

lemma Rinf_steps_ERw_msteps_src:
  assumes "(s,t) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*"
  shows "(s,t) \<in> (mstep {#s#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
proof(induct rule:converse_rtrancl_induct)
case base
  then show ?case unfolding mstep_def by auto
next
  case (step s u)
  note lift = mstep_succeq_mono[of "{#u#}" "{#s#}",THEN conversion_mono, of "R\<^sub>\<omega> \<union> E\<^sub>\<omega>"]
  from step(1) compatible_rstep_imp_less Rinf_less have "s \<succ> u" by auto
  with lift step(3) have ut:"(u, t) \<in> (mstep {#s#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  from Rinf_step_ERw_msteps_src[OF step(1)] have "(s,u) \<in> (mstep {#s#} (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with ut conversion_O_conversion show ?case by force
qed

lemma mstep_conv_subset_add_mset: "(mstep S RR)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (mstep (S' + S) RR)\<^sup>\<leftrightarrow>\<^sup>*"
  using msteps_succeq_mono[of S "S' + S"] by auto

lemma Rinf_steps_Rw_msteps:
  assumes "(s,t) \<in> (rstep R\<^sub>\<infinity>)\<^sup>+"
  shows "\<exists>u S. (s,u) \<in> rstep R\<^sub>\<omega> \<and> (\<forall>t\<in>#S. s \<succ> t) \<and> (u,t) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" 
proof-
  from tranclD[OF assms] obtain u where u:"(s,u) \<in> rstep R\<^sub>\<infinity>" "(u,t) \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" by auto
  from Rinf_step_Rw_msteps[OF u(1)] obtain v S where
    v:"(s,v) \<in> rstep R\<^sub>\<omega>" "\<forall>t\<in>#S. s \<succ> t" "(v,u) \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  from Rinf_steps_ERw_msteps_src[OF u(2)] mstep_conv_subset_add_mset[of "{#u#}" _ S]
    have ut:"(u, t) \<in> (mstep ({#u#} + S) (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" unfolding add.commute[of S] by blast
  from v(3) mstep_conv_subset_add_mset[of S _ "{#u#}"] have "(v, u) \<in> (mstep ({#u#} + S) (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by blast
  with ut have vt:"(v, t) \<in> (mstep ({#u#} + S) (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by fastforce
  from compatible_rstep_imp_less[OF Rinf_less u(1)] v(2) have "\<forall>t\<in>#{#u#} +S. s \<succ> t" by auto
  with vt v(1) show ?thesis by blast
qed

context
  assumes Ew_unorientable:"E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<inter> {\<succ>} = {}" and Ew_nontrivial:"E\<^sub>\<omega> \<inter> Id = {}"
begin

definition mstep\<^sub>1 where "mstep\<^sub>1 M RR = {(x,y) |x y x'. (x,y) \<in> rstep RR \<and> M = {#x'#} \<and> x' \<succeq> x \<and> x' \<succeq> y}"
definition mstep\<^sub>2 where "mstep\<^sub>2 M RR = {(x,y) |x y x' y'. (x,y) \<in> rstep RR \<and> M = {#x',y'#} \<and> x' \<succeq> x \<and> y' \<succeq> y}"

lemma mstep\<^sub>1I:"(x,y) \<in> rstep RR \<Longrightarrow> x' \<succeq> x \<Longrightarrow> x' \<succeq> y \<Longrightarrow> (x,y) \<in> mstep\<^sub>1 {#x'#} RR"
  unfolding mstep\<^sub>1_def by force

lemma mstep\<^sub>2I:"(x,y) \<in> rstep RR \<Longrightarrow> x' \<succeq> x \<Longrightarrow> y' \<succeq> y \<Longrightarrow> (x,y) \<in> mstep\<^sub>2 {#x',y'#} RR"
  unfolding mstep\<^sub>2_def by force

lemma mstep\<^sub>1_dom:"(x, y) \<in> mstep\<^sub>1 M R\<^sub>\<omega> \<Longrightarrow> M \<succ>\<^sub>m\<^sub>u\<^sub>l {#y#}"
proof-
  assume a:"(x, y) \<in> mstep\<^sub>1 M R\<^sub>\<omega>"
  with compatible_rstep_imp_less[OF Rw_less] have xy:"x \<succ> y" unfolding mstep\<^sub>1_def by auto
  from a obtain x' where M:"M = {#x'#}" and "x' \<succeq> x" unfolding mstep\<^sub>1_def by auto
  with trans xy have "x' \<succ> y" by auto
  then show "M \<succ>\<^sub>m\<^sub>u\<^sub>l {#y#}" unfolding M using ns_mul_ext_singleton2 by fastforce
qed

lemma mstep\<^sub>2_dom:"(x, y) \<in> (mstep\<^sub>2 M RR)\<^sup>\<leftrightarrow> \<Longrightarrow> M \<succ>\<^sub>m\<^sub>u\<^sub>l {#y#}"
proof-
  assume a:"(x, y) \<in> (mstep\<^sub>2 M RR)\<^sup>\<leftrightarrow>"
  from a obtain x' y' x'' y'' where M:"M = {#x',y'#}" and "x'' \<in># M" and "y'' \<in># M" and "x'' \<succeq> x"  and "y'' \<succeq> y"
    unfolding mstep\<^sub>2_def by auto
  then show "M \<succ>\<^sub>m\<^sub>u\<^sub>l {#y#}" unfolding M using s_mul_ext_singleton
    by (smt add_mset_add_single add_mset_eq_singleton_iff all_s_s_mul_ext case_prodI empty_not_add_mset mem_Collect_eq mulsucc.rtrancl_NS multi_member_split rtrancl_eq_or_trancl s_ns_mul_ext_union_compat sup2E)
qed

lemma mstep\<^sub>1_rstep[simp]:"(x, y) \<in> mstep\<^sub>1 M RR \<Longrightarrow> (x, y) \<in> rstep RR" unfolding mstep\<^sub>1_def by auto

lemma mstep\<^sub>2_rstep[simp]:"(x, y) \<in> mstep\<^sub>2 M RR \<Longrightarrow> (x, y) \<in> rstep RR" unfolding mstep\<^sub>2_def by auto

lemma mstep1_subset_mstep: "mstep\<^sub>1 M R\<^sub>\<omega> \<subseteq> mstep M R\<^sub>\<omega>"
proof
  fix x y
  assume a:"(x, y) \<in> mstep\<^sub>1 M R\<^sub>\<omega>"
  then obtain x' where M:"M = {#x'#}" "x' \<succeq> x" "x' \<succeq> y" unfolding mstep\<^sub>1_def by auto
  with a M show "(x, y) \<in> mstep M R\<^sub>\<omega>" unfolding mstep_def mem_Collect_eq split by auto
qed

lemma mstep2_subset_mstep: "mstep\<^sub>2 M RR \<subseteq> mstep M RR"
proof
  fix x y
  assume a:"(x, y) \<in> mstep\<^sub>2 M RR"
  then show "(x, y) \<in> mstep M RR" unfolding mstep_def mstep\<^sub>2_def mem_Collect_eq split by force
qed

lemma mstep1_conv_mstep: "mstep\<^sub>1 {#z#} RR = mstep {#z#} RR"
proof-
  { fix x y
    assume a:"(x, y) \<in> mstep {#z#} RR"
    then have "(x, y) \<in> mstep\<^sub>1 {#z#} RR" unfolding mstep\<^sub>1_def mstep_def mem_Collect_eq split by auto
  } note A = this
  { fix x y
    assume a:"(x, y) \<in> mstep\<^sub>1 {#z#} RR"
    with a have "(x, y) \<in> mstep {#z#} RR" unfolding mstep\<^sub>1_def mstep_def mem_Collect_eq split by auto
  }
  with A show ?thesis by auto
qed

lemma mstep\<^sub>2_converse:"(mstep\<^sub>2 M RR)\<^sup>\<leftrightarrow> = mstep\<^sub>2 M (RR\<^sup>\<leftrightarrow>)"
unfolding mstep\<^sub>2_def mem_Collect_eq using add_mset_commute by fast

lemma mstep1_union:"mstep\<^sub>1 M (R1 \<union> R2) = mstep\<^sub>1 M R1 \<union> mstep\<^sub>1 M R2"
  unfolding mstep\<^sub>1_def by auto

interpretation A:ars_mod_labeled_sn "\<lambda>M. mstep\<^sub>1 M R\<^sub>\<omega>" "\<lambda>M. mstep\<^sub>2 M E\<^sub>\<omega>" UNIV UNIV "(\<succ>\<^sub>m\<^sub>u\<^sub>l)"
  using mulsucc.SN by unfold_locales auto

lemma succ_irrefl:"\<not> s \<succ> s"
  using SN_imp_acyclic[OF SN_less] unfolding  acyclic_irrefl irrefl_def by auto

lemma pdm:
  assumes "A.mod_peak s M w N t"
  shows "(s, t) \<in> (\<Union>K\<in>A.downset2 M N. (mstep\<^sub>1 K R\<^sub>\<omega> \<union> mstep\<^sub>2 K E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
proof-
  let ?J = "(rstep R\<^sub>\<infinity>)\<^sup>* O (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>= O ((rstep R\<^sub>\<infinity>)\<inverse>)\<^sup>*"
  from compatible_rstep_trancl_imp_less[OF Rinf_less] have succeq:"\<And>x y.(x,y) \<in> (rstep R\<^sub>\<infinity>)\<^sup>* \<Longrightarrow> x \<succeq> y"
    unfolding rtrancl_eq_or_trancl by blast
  from assms mstep_Un have "\<exists>s' t' M' N'. (w,s') \<in> (mstep\<^sub>1 M' R\<^sub>\<omega> \<union> mstep\<^sub>2 M' (E\<^sub>\<omega>\<^sup>\<leftrightarrow>)) \<and> (w,t') \<in> mstep\<^sub>1 N' R\<^sub>\<omega> \<and>
    ((s,t) = (s',t') \<or> (s,t) = (t',s')) \<and> (M' = M \<or> M' = N)"
    unfolding A.mod_peak_def mstep\<^sub>2_converse by blast
  then obtain s' t' M' N' where *:"(w,s') \<in> (mstep\<^sub>1 M' R\<^sub>\<omega> \<union> mstep\<^sub>2 M' (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))" "(w,t') \<in> mstep\<^sub>1 N' R\<^sub>\<omega>"
    "((s,t) = (s',t') \<or> (s,t) = (t',s'))" "M' = M \<or> M' = N" unfolding A.mod_peak_def by force
  from * have rstep:"(w, s') \<in> rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" "(w, t') \<in> rstep R\<^sub>\<omega>"
    using mstep\<^sub>1_rstep mstep\<^sub>2_rstep rstep_converse by blast+
  with rstep_converse have "(s', w) \<in> rstep (R\<^sub>\<omega>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
  then obtain l r p \<sigma> where 1:"(s', w) \<in> rstep_r_p_s (R\<^sub>\<omega>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>) (l,r) p \<sigma>"
    unfolding rstep_iff_rstep_r_p_s by fast
  then have lr:"(l,r) \<in> R\<^sub>\<omega>\<inverse> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" unfolding rstep_r_p_s_def mem_Collect_eq split by meson
  then have ngt_R:"(l,r) \<in> R\<^sub>\<omega>\<inverse> \<Longrightarrow> \<not> l \<succ> r" using SN_imp_acyclic[OF SN_less] trans[of r l r] Rw_less
    unfolding converse_iff acyclic_irrefl irrefl_def by (cases "l \<succ> r", auto)
  with lr Ew_unorientable have "\<not> l \<succ> r" by auto
  with linear_peak_cases[OF 1 rstep(2)] have valley:"(s', t') \<in> ?J" by auto
  have J_inv:"?J\<inverse> = ?J" using O_assoc symcl_converse
    unfolding converse_relcomp rtrancl_converse converse_converse converse_Un rstep_simps(5) by blast
  from *(3) have valley:"(s, t) \<in> ?J" by (rule disjE, insert valley J_inv converse_iff) blast+
  then obtain s'' t'' where **:"(s,s'') \<in> (rstep R\<^sub>\<infinity>)\<^sup>*" "(s'',t'') \<in> (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>=" "(t,t'') \<in> (rstep R\<^sub>\<infinity>)\<^sup>*"
    unfolding rtrancl_converse by auto
  let ?M = "\<lambda>M. (mstep M (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
  let ?M1 = "\<lambda>M. (mstep\<^sub>1 M (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
  from Rinf_steps_ERw_msteps_src **(1) **(3) have "(s, s'') \<in> ?M {#s#}" "(t, t'') \<in> ?M {#t#}" by auto
  with mstep1_conv_mstep have Rsteps:"(s, s'') \<in> ?M1 {#s#}" "(t, t'') \<in> ?M1 {#t#}" by auto
  note a = assms[unfolded A.mod_peak_def]
  from a mstep\<^sub>1_dom[of w s M] mstep\<^sub>2_dom have cover1:"M \<succ>\<^sub>m\<^sub>u\<^sub>l {#s#} \<or> N \<succ>\<^sub>m\<^sub>u\<^sub>l {#s#}" by blast
  from a mstep\<^sub>1_dom[of w t] mstep\<^sub>2_dom[of w t N] have cover2:"M \<succ>\<^sub>m\<^sub>u\<^sub>l {#t#} \<or> N \<succ>\<^sub>m\<^sub>u\<^sub>l {#t#}" by blast
  from *(2) compatible_rstep_imp_less[OF Rw_less] have wt:"w \<succ> t'" unfolding mstep\<^sub>1_def by auto
  have "M' \<succ>\<^sub>m\<^sub>u\<^sub>l {#s',t'#}" proof(cases "(w, s') \<in> mstep\<^sub>1 M' R\<^sub>\<omega>")
    case True
    then have "\<exists>u v. u \<in># M' \<and> u \<succeq> w  \<and> v \<in># M' \<and> v \<succeq> s'" unfolding mstep\<^sub>1_def by auto
    then obtain u v where uv:"u \<in># M'" "u \<succeq> w" "v \<in># M'" "v \<succeq> s'" unfolding mstep\<^sub>1_def mstep\<^sub>2_def by blast
    from True compatible_rstep_imp_less[OF Rw_less] have "w \<succ> s'" unfolding mstep\<^sub>1_def by auto
    with uv(2) wt trans[of u w] have "u \<succ> t' \<and> u \<succ> s'" by auto
    with uv(1) have u:"\<forall>b. b \<in># {#s', t'#} \<longrightarrow> (\<exists>a. a \<in># M' \<and> a \<succ> b)" by auto
    from multi_member_split[OF uv(1)] uv(1) empty_not_add_mset have "M' \<noteq> {#}" by auto
    from all_s_s_mul_ext[OF this, of "{#s',t'#}"] u show ?thesis by auto
  next
    case False
    with *(1) have step:"(w, s') \<in> mstep\<^sub>2 M' (E\<^sub>\<omega>\<^sup>\<leftrightarrow>)" by auto
    then obtain u v where uv:"M' = {#u,v#}" "u \<succeq> w" "v \<succeq> s'" unfolding mstep\<^sub>2_def by auto
    from uv(3) ns_mul_ext_singleton2[of v s'] have ns:"{#v#} \<succeq>\<^sub>m\<^sub>u\<^sub>l {#s'#}" by (cases "v = s'", auto)
    from uv trans wt have "u \<succ> t'" by auto
    then have "{#u#} \<succ>\<^sub>m\<^sub>u\<^sub>l {# t'#}" by auto
    with uv(3) s_ns_mul_ext_union_compat[OF this ns] show ?thesis
      unfolding uv add_mset_commute[of u v "{#}"] by auto
  qed
  with *(3) have "M' \<succ>\<^sub>m\<^sub>u\<^sub>l {#s,t#}" using add_mset_commute[of s' t' "{#}"] by fastforce  
  with *(4) have cover3:"(M \<succ>\<^sub>m\<^sub>u\<^sub>l {#s,t#} \<or> N \<succ>\<^sub>m\<^sub>u\<^sub>l {#s,t#})" by auto
  let ?D = "\<Union>K\<in>A.downset2 M N. (mstep\<^sub>1 K R\<^sub>\<omega> \<union> mstep\<^sub>2 K E\<^sub>\<omega>)"
  from ** succeq have "s \<succeq> s''" "t \<succeq> t''" by auto
  with **(2) have "(s'', t'') \<in> (mstep\<^sub>2 {#s,t#} (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))\<^sup>=" unfolding mstep\<^sub>2_def mem_Collect_eq by auto
  with cover3 have st:"(s'', t'') \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" using mstep\<^sub>2_converse by fast

  { fix u S
    assume u:"u = s \<or> u = t" and S:"\<forall>t \<in># S. u \<succ> t"
    have D1:"mstep S R\<^sub>\<omega> \<subseteq> ?D" proof
      fix x y
      assume step:"(x, y) \<in> mstep S R\<^sub>\<omega>"
      with u S trans[of u] have "u \<succ> x" "u \<succ> y" unfolding mstep_def mem_Collect_eq split by fast+
      with cover1 have "(x, y) \<in> mstep\<^sub>1 {#u#} R\<^sub>\<omega>" using step unfolding mstep_def by (auto intro!: mstep\<^sub>1I)
      with cover1 cover2 u show "(x,y) \<in> ?D" by auto
    qed
    have "mstep S E\<^sub>\<omega> \<subseteq> ?D" proof
      fix x y
      assume step:"(x, y) \<in> mstep S E\<^sub>\<omega>"
      with S u trans[of u] have s:"u \<succ> x" "u \<succ> y" unfolding mstep_def mem_Collect_eq split by fast+
      have dec:"{#u#} \<succ>\<^sub>m\<^sub>u\<^sub>l {#x,y#}" by (auto intro!:all_s_s_mul_ext simp:s)
      have "(x, y) \<in> mstep\<^sub>2 {#x,y#} E\<^sub>\<omega>" using step unfolding mstep_def by (auto intro!: mstep\<^sub>2I)
      with u mulsucc.trans_S_point[OF _ dec] cover1 cover2 show "(x,y) \<in> ?D" by blast
    qed
    with D1 have "mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>) \<subseteq> ?D" by auto
    from conversion_mono[OF this] have "(mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> ?D\<^sup>\<leftrightarrow>\<^sup>*" by auto
  } note conv_dec = this

  have ss:"(s, s'') \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" proof(cases "s=s''", simp)
    assume "s \<noteq> s''"
    with **(1) have "(s, s'') \<in> (rstep R\<^sub>\<infinity>)\<^sup>+" unfolding rtrancl_eq_or_trancl by auto
    from Rinf_steps_Rw_msteps[OF this] obtain s\<^sub>1 S where
      S:"(s, s\<^sub>1) \<in> rstep R\<^sub>\<omega>" "\<forall>t \<in># S. s \<succ> t" "(s\<^sub>1, s'') \<in> (mstep S (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    have "(s, s\<^sub>1) \<in> mstep\<^sub>1 {#s#} R\<^sub>\<omega>" using compatible_rstep_imp_less[OF Rw_less] S(1) by (auto intro!:mstep\<^sub>1I)
    with cover1 have 1:"(s, s\<^sub>1) \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" by auto
    from conv_dec[OF _ S(2)] S(3) have "(s\<^sub>1, s'') \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" by auto
    with conversion_trans'[OF 1] show "(s, s'') \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" by blast
  qed

  have "(t, t'') \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" proof(cases "t=t''", simp)
    assume "t \<noteq> t''"
    with **(3) have "(t, t'') \<in> (rstep R\<^sub>\<infinity>)\<^sup>+" unfolding rtrancl_eq_or_trancl by auto
    from Rinf_steps_Rw_msteps[OF this] obtain t\<^sub>1 T where
      S:"(t, t\<^sub>1) \<in> rstep R\<^sub>\<omega>" "\<forall>u \<in># T. t \<succ> u" "(t\<^sub>1, t'') \<in> (mstep T (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    have "(t, t\<^sub>1) \<in> mstep\<^sub>1 {#t#} R\<^sub>\<omega>" using compatible_rstep_imp_less[OF Rw_less] S(1) by (auto intro!:mstep\<^sub>1I)
    with cover2 have 1:"(t, t\<^sub>1) \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" by auto
    from conv_dec[OF _ S(2)] S(3) have "(t\<^sub>1, t'') \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" by auto
    with conversion_trans'[OF 1] show "(t, t'') \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" by blast
  qed
  then have tt:"(t'', t) \<in> ?D\<^sup>\<leftrightarrow>\<^sup>*" using conversion_sym[unfolded sym_def, rule_format, of t t''] by blast
  note t = conversion_trans[THEN transD]
  from t[OF t, OF ss st ] tt show ?thesis by auto
qed

lemma CRm: "CRm (rstep R\<^sub>\<omega>) (rstep E\<^sub>\<omega>)"
proof-
  from A.CRm pdm have CRm:"CRm (\<Union>a. mstep\<^sub>1 a R\<^sub>\<omega>) (\<Union>a. mstep\<^sub>2 a E\<^sub>\<omega>)" by force
  have id:"(\<Union>a. mstep\<^sub>1 a R\<^sub>\<omega>) = rstep R\<^sub>\<omega>"
    unfolding mstep\<^sub>1_def using compatible_rstep_imp_less[OF Rw_less] by auto
  have "(\<Union>a. mstep\<^sub>2 a E\<^sub>\<omega>) = rstep E\<^sub>\<omega>" unfolding mstep\<^sub>2_def by auto
  with id CRm show ?thesis by auto
qed

lemma NF_R_subset_NF_REw:"NF_trs \<R> \<subseteq> NF_trs R\<^sub>\<omega> \<inter> NF (rstep (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))"
proof-
  { fix t u
    assume NF:"t \<in> NF_trs \<R>" and "(t,u) \<in> rstep (R\<^sub>\<omega> \<union> (E\<^sub>\<omega>\<^sup>\<leftrightarrow>))"
    then obtain l r C \<sigma> where lr:"(l,r) \<in> R\<^sub>\<omega> \<union> E\<^sub>\<omega>\<^sup>\<leftrightarrow>" "t = C\<langle>l\<cdot>\<sigma>\<rangle>" "u = C\<langle>r\<cdot>\<sigma>\<rangle>" by blast
    from conv_eq[unfolded oKBi_conversion_ERw] lr(1) have "(l,r) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*" by auto
    with CR_R[unfolded CR_iff_conversion_imp_join] have "(l,r) \<in> (rstep \<R>)\<^sup>\<down>" by auto
    then obtain v where v:"(l,v) \<in> (rstep \<R>)\<^sup>*" "(r,v) \<in> (rstep \<R>)\<^sup>*" by auto
    from NF[unfolded lr, THEN NF_subterm,THEN NF_instance] have "l \<in> NF_trs \<R>" by auto
    with v(1)[unfolded rtrancl_eq_or_trancl] tranclD[of l v] have "v=l" by force
    from v(2)[unfolded this] compatible_rstep_trancl_imp_less[OF R_less] have succeq:"r \<succeq> l"
      unfolding rtrancl_eq_or_trancl by blast
    have False proof(cases "(l,r) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow>")
      case True
      with Ew_nontrivial have neq:"l \<noteq> r" by auto
      with succeq have "r \<succ> l" by blast
      with True Ew_unorientable show False by auto
    next
      case False
      with lr have "(l,r) \<in> R\<^sub>\<omega>" by auto
      with compatible_rstep_imp_less[OF Rw_less] have "l \<succ> r" by auto
      with SN_imp_acyclic[OF SN_less] succeq trans[OF this] show False
        unfolding acyclic_def by (cases "l=r", auto)
    qed
  }
  then show ?thesis using NF_trs_union[of R\<^sub>\<omega> E\<^sub>\<omega>] by blast
qed

lemma NF_Rw_subset_NF_R:"NF_trs R\<^sub>\<omega> \<subseteq> NF_trs \<R>"
proof-
  { fix s t
    assume "(s,t) \<in> rstep \<R>"
    then obtain l r C \<sigma> where st:"s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" and rule:"(l,r) \<in> \<R>" by auto
    from conv_eq[unfolded oKBi_conversion_ERw] have "(l,r) \<in> (rstep (R\<^sub>\<omega> \<union> E\<^sub>\<omega>))\<^sup>\<leftrightarrow>\<^sup>*"
      using rstep_rule[OF rule] by auto
    with CRm[unfolded CRm_def] have "(l,r) \<in> (rstep R\<^sub>\<omega>)\<^sup>* O (rstep E\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>* O ((rstep R\<^sub>\<omega>)\<inverse>)\<^sup>*"
      unfolding rstep_union by auto
    then obtain v u where vu:"(l,u) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" "(u,v) \<in> (rstep E\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" "(r,v) \<in> (rstep R\<^sub>\<omega>)\<^sup>*"
      unfolding rtrancl_converse using converse_iff by auto
    from rule \<open>reduced \<R>\<close> NF_R_subset_NF_REw have NF:"r \<in> NF_trs R\<^sub>\<omega>" "r \<in> NF_trs (E\<^sub>\<omega>\<^sup>\<leftrightarrow>)"
      unfolding reduced_def right_reduced_def by auto
    with vu(3) tranclD[of r v "rstep R\<^sub>\<omega>"] have "r = v" unfolding rtrancl_eq_or_trancl by auto
    from vu(2) have "(v,u) \<in> (rstep E\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" using conversion_sym[unfolded sym_def] by metis
    with NF_no_trancl_step[OF NF(2), rule_format, of u] have "v = u"
      unfolding conversion_def rtrancl_eq_or_trancl \<open>r = v\<close> rstep_simps(5) by auto
    from vu have lr:"(l,r) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" using \<open>r = v\<close> \<open>v = u\<close> by auto
    from R_less rule SN_imp_acyclic[OF SN_less, unfolded acyclic_def] have "l \<noteq> r" by auto
    then have "\<exists>t. (l,t) \<in> rstep R\<^sub>\<omega>"
      using lr[unfolded rtrancl_eq_or_trancl] tranclD[of l r "rstep R\<^sub>\<omega>"] by blast
    then have "\<exists>t. (s,t) \<in> rstep R\<^sub>\<omega>" unfolding st by blast
  }
  then show ?thesis by auto
qed

lemma linear_completeness:
  assumes Ew_irreducible:"\<forall>s t. (s,t) \<in> E\<^sub>\<omega>\<^sup>\<leftrightarrow> \<longrightarrow> s \<in> NF_trs R\<^sub>\<omega>"
  and Ew_nontrivial:"\<forall>t. (t,t) \<notin> E\<^sub>\<omega>"
  and "reduced \<R>" and "reduced R\<^sub>\<omega>"
  shows "E\<^sub>\<omega> = {} \<and> \<R> \<doteq> R\<^sub>\<omega>"
proof -
  interpret complete_ars "(rstep \<R>)" by (unfold_locales, insert CR_R SN_R, auto)
  have SN_Rw:"SN (rstep R\<^sub>\<omega>)" 
    by (rule SN_subset [OF SN_less], insert compatible_rstep_imp_less[OF Rw_less], auto)
  from conv_eq[unfolded oKBi_conversion_ERw] have "rstep R\<^sub>\<omega> \<subseteq> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: rstep_simps)
  from complete_NE_intro1[OF this SN_Rw NF_Rw_subset_NF_R] have
    complete:"complete_ars (rstep R\<^sub>\<omega>)" and norm:"(rstep \<R>)\<^sup>! = (rstep R\<^sub>\<omega>)\<^sup>!" by auto
  note vars = SN_imp_variable_condition[OF SN_R] SN_imp_variable_condition[OF SN_Rw]
  from reduced_NE_imp_unique[OF vars \<open>reduced \<R>\<close> _ norm] \<open>reduced R\<^sub>\<omega>\<close> have litsim:"\<R> \<doteq> R\<^sub>\<omega>" by auto
  { fix s t
    assume st:"(s,t) \<in> E\<^sub>\<omega>"
    with conv_eq[unfolded oKBi_conversion_ERw] have "(s,t) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*" by auto
    with CR_imp_conversionIff_join[OF CR_R] litsim_rstep_eq[OF litsim] obtain w where
      w:"(s, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" "(t, w) \<in> (rstep R\<^sub>\<omega>)\<^sup>*" by auto
    from st Ew_irreducible[rule_format] have nfs:"s \<in> NF_trs R\<^sub>\<omega>" "t \<in> NF_trs R\<^sub>\<omega>" by auto
    note nfs = nfs[unfolded NF_def] w[unfolded rtrancl_eq_or_trancl] tranclD
    then have "s = w \<and> t = w" by fast
    with st Ew_nontrivial have False by auto
  }
  with litsim show ?thesis by auto
qed
end
end
end
end
end
