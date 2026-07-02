(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016, 2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Ordered Rewriting\<close>

theory Ordered_Rewriting
  imports
    Reduction_Order
    TRS.Renaming_Interpretations
    First_Order_Rewriting.Multihole_Context
    TRS.Signature_Extension
begin

inductive_set ordstep for ord :: "('f, 'v) term rel" and R :: "('f, 'v) trs"
  where
    "(l, r) \<in> R \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ord \<Longrightarrow> (s, t) \<in> ordstep ord R"

lemma ordstep_Un:
  "ordstep ord (R \<union> R') = ordstep ord R \<union> ordstep ord R'"
  by (auto intro: ordstep.intros elim: ordstep.cases)

lemma ordstep_imp_rstep:
  "(s, t) \<in> ordstep ord R \<Longrightarrow> (s, t) \<in> rstep R"
  by (auto elim: ordstep.cases)

lemma ordstep_rstep_conv:
  assumes "subst.closed ord" and "R \<subseteq> ord"
  shows "ordstep ord R = rstep R"
  using assms by (fast elim: ordstep.cases intro: ordstep.intros)

lemma ordstep_subst:
  "subst.closed ord \<Longrightarrow> (s, t) \<in> ordstep ord R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ordstep ord R"
  by (elim ordstep.cases, intro ordstep.intros [where C = "C \<cdot>\<^sub>c \<sigma>" and \<sigma> = "\<tau> \<circ>\<^sub>s \<sigma>" for C \<tau>]) auto

lemma subst_closed_ordstep [intro]:
  "subst.closed ord \<Longrightarrow> subst.closed (ordstep ord R)"
  by (auto simp: ordstep_subst)

lemma ordstep_ctxt:
  "(s, t) \<in> ordstep ord R \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> ordstep ord R"
  by (elim ordstep.cases, intro ordstep.intros [where C = "C \<circ>\<^sub>c D" for D]) auto

lemma ordstep_subst_ctxt:
  "subst.closed ord \<Longrightarrow> (s, t) \<in> ordstep ord R \<Longrightarrow> (C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> ordstep ord R"
  using ordstep_ctxt[OF ordstep_subst] by fast

lemma ordsteps_ctxt:
  assumes "(s, t) \<in> (ordstep ord R)\<^sup>*"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (ordstep ord R)\<^sup>*"
  using assms by (induct) (auto simp: ordstep_ctxt rtrancl_into_rtrancl)

lemma ctxt_closed_ordstep [intro]:
  "ctxt.closed (ordstep ord R)"
  by (auto simp: ordstep_ctxt)

lemma all_ctxt_closed_ordsteps [simp]:
  "all_ctxt_closed UNIV ((ordstep ord R)\<^sup>*)"
  by (rule trans_ctxt_imp_all_ctxt_closed) (auto simp: trans_def refl_on_def)

lemma ordstep_join_ctxt [intro]:
  assumes "(s, t) \<in> (ordstep ord R)\<^sup>\<down>"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (ordstep ord R)\<^sup>\<down>"
proof -
  from assms obtain u where "(s, u) \<in> (ordstep ord R)\<^sup>*" and "(t, u) \<in> (ordstep ord R)\<^sup>*" by auto
  then have "(C\<langle>s\<rangle>, C\<langle>u\<rangle>) \<in> (ordstep ord R)\<^sup>*" and "(C\<langle>t\<rangle>, C\<langle>u\<rangle>) \<in> (ordstep ord R)\<^sup>*" by (auto intro: ordsteps_ctxt)
  then show ?thesis by blast
qed 

lemma ordstep_mono:
  "R \<subseteq> R' \<Longrightarrow> ord \<subseteq> ord' \<Longrightarrow> ordstep ord R \<subseteq> ordstep ord' R'"
  by (auto elim!: ordstep.cases intro: ordstep.intros)

lemma ordsteps_mono:
  assumes "R \<subseteq> R'" and "ord \<subseteq> ord'"
  shows "(ordstep ord R)\<^sup>* \<subseteq> (ordstep ord' R')\<^sup>*"
  using ordstep_mono[OF assms] by (simp add: rtrancl_mono)

lemma ordstep_imp_ord:
  "ctxt.closed ord \<Longrightarrow> (s, t) \<in> ordstep ord R \<Longrightarrow> (s, t) \<in> ord"
  by (elim ordstep.cases) auto

lemma ordsteps_imp_ordeq:
  assumes "ctxt.closed ord" and "trans ord" and "(s, t) \<in> (ordstep ord R)\<^sup>*"
  shows "(s, t) \<in> ord\<^sup>="
  using assms(3) by (induct) (auto dest: ordstep_imp_ord [OF assms(1)] assms(2) [THEN transD])

lemma ordstep_rstep_conv':
  assumes "subst.closed ord"
  shows "ordstep ord R = rstep {(l \<cdot> \<sigma>, r \<cdot> \<sigma>) | l r \<sigma>. (l, r) \<in> R \<and> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ord}"
proof -
  { fix l r \<sigma> \<tau> C assume "(l, r) \<in> R" and "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ord"
    then have "(l \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>), r \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)) \<in> ord" using \<open>subst.closed ord\<close> by auto
    with \<open>(l, r) \<in> R\<close> have "(C\<langle>l \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)\<rangle>, C\<langle>r \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)\<rangle>) \<in> ordstep ord R"
      by (intro ordstep.intros [where C = C and l = l and r = r and \<sigma> = "\<sigma> \<circ>\<^sub>s \<tau>"]) auto }
  then show ?thesis
    by (auto elim!: ordstep.cases) blast
qed

lemma ordstep_permute:
  "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ordstep (\<pi> \<bullet> ord) (\<pi> \<bullet> R) \<longleftrightarrow> (s, t) \<in> ordstep ord R"
proof
  assume "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ordstep (\<pi> \<bullet> ord) (\<pi> \<bullet> R)"
  then obtain C l r \<sigma> where "(l, r) \<in> \<pi> \<bullet> R" and "\<pi> \<bullet> s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "\<pi> \<bullet> t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> \<pi> \<bullet> ord" by (cases)
  moreover define D and \<tau> where "D = -\<pi> \<bullet> C" and "\<tau> = sop \<pi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop (-\<pi>)"
  ultimately have "s = D\<langle>-\<pi> \<bullet> l \<cdot> \<tau>\<rangle>" and "t = D\<langle>-\<pi> \<bullet> r \<cdot> \<tau>\<rangle>"
    and "(-\<pi> \<bullet> l, -\<pi> \<bullet> r) \<in> R" and "(-\<pi> \<bullet> l \<cdot> \<tau>, -\<pi> \<bullet> r \<cdot> \<tau>) \<in> ord"
    by (auto simp: eqvt [symmetric] term_pt.permute_flip)
  then show "(s, t) \<in> ordstep ord R" by (intro ordstep.intros)
next
  assume "(s, t) \<in> ordstep ord R"
  then show "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ordstep (\<pi> \<bullet> ord) (\<pi> \<bullet> R)"
    by (cases) (auto simp: eqvt, metis ordstep.intros rule_mem_trs_iff term_apply_subst_eqvt)
qed

lemma (in reduction_order) FGROUND_conversion_ordstep :
  fixes s t :: "('a, 'b) term"
  assumes fgtotal:"\<And>s t. Reduction_Order.fground F s \<Longrightarrow> Reduction_Order.fground F t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"
    and "R \<subseteq> {\<succ>}"
    and "(s, t) \<in> FGROUND F (rstep (E \<union> R))"
  shows "(s, t) \<in> ((FGROUND F ((ordstep {\<succ>} (E\<^sup>\<leftrightarrow> \<union> R))))\<^sup>\<leftrightarrow>)\<^sup>="
proof -
  from assms(3) have fground:"fground F s" "fground F t" and step:"(s, t) \<in> rstep (E \<union> R)"
    unfolding FGROUND_def by auto
  from step obtain l r C \<sigma> where step:"(l,r) \<in> E \<union> R" "s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by fast
  from fground have fg:"fground F (l\<cdot>\<sigma>)" "fground F (r\<cdot>\<sigma>)" unfolding step fground_def by simp+
  show ?thesis proof (cases "l \<cdot> \<sigma> = r \<cdot> \<sigma>")
    case True
    from fground(1) show ?thesis unfolding step True FGROUND_def by simp
  next
    case False
    with fgtotal[OF fg] consider "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" | "r \<cdot> \<sigma> \<succ> l \<cdot> \<sigma>" by auto
    thus ?thesis proof(cases)
      case 1
      with step have "(s, t) \<in> (ordstep {\<succ>} (E \<union> R))" unfolding ordstep.simps by auto
      with ordstep_mono[of "E \<union> R" "E\<^sup>\<leftrightarrow> \<union> R"] have "(s, t) \<in> (ordstep {\<succ>} (E\<^sup>\<leftrightarrow> \<union> R))" by auto
      with fground show ?thesis unfolding FGROUND_def by simp
    next
      case 2
      { assume "(l,r) \<in> R"
        with subst assms(2) have "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" by auto
        from trans[OF this 2] SN_imp_acyclic[OF SN_less] have False
          unfolding acyclic_irrefl irrefl_def by auto
      }
      with step(1) have "(r,l) \<in> E\<^sup>\<leftrightarrow>" by auto
      with 2 have "(t, s) \<in> (ordstep {\<succ>} (E\<^sup>\<leftrightarrow>))" unfolding ordstep.simps step by auto
      with ordstep_mono[of "E\<^sup>\<leftrightarrow>" "E\<^sup>\<leftrightarrow> \<union> R"] have "(t, s) \<in> (ordstep {\<succ>} (E\<^sup>\<leftrightarrow> \<union> R))" by auto
      with fground show ?thesis unfolding FGROUND_def by simp
    qed
  qed
qed

lemma (in reduction_order) FGROUND_conversion_ordsteps:
  assumes fgtotal:"\<And>s t. fground F s \<Longrightarrow> fground F t \<Longrightarrow> s = t \<or> s \<succ> t \<or> t \<succ> s"
    and "R \<subseteq> {\<succ>}"
  shows "(FGROUND F (rstep (E \<union> R)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND F (ordstep {\<succ>} (E\<^sup>\<leftrightarrow> \<union> R)))\<^sup>\<leftrightarrow>\<^sup>*"
proof-
  from FGROUND_conversion_ordstep[OF fgtotal assms(2)]
  have "FGROUND F (rstep (E \<union> R)) \<subseteq> ((FGROUND F ((ordstep {\<succ>} (E\<^sup>\<leftrightarrow> \<union> R))))\<^sup>\<leftrightarrow>)\<^sup>=" by auto
  hence "(FGROUND F (rstep (E \<union> R)))\<^sup>\<leftrightarrow> \<subseteq> ((FGROUND F ((ordstep {\<succ>} (E\<^sup>\<leftrightarrow> \<union> R))))\<^sup>\<leftrightarrow>)\<^sup>=" by auto
  from rtrancl_mono[OF this] show ?thesis unfolding conversion_def by simp
qed

definition "fground_joinable F ord R s t =
  (\<forall>\<sigma> :: ('a,'b) subst. fground F (s \<cdot> \<sigma>) \<and> fground F (t \<cdot> \<sigma>) \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep ord R)\<^sup>\<down>)"

abbreviation "ground_joinable \<equiv> fground_joinable UNIV"

definition "Req x (R :: ('f, 'v) trs) eq true false s t =
  {(Fun eq [Var x, Var x], Fun true [])} \<union>
  {(Fun eq [s, t], Fun false [])} \<union> R"

lemma rstep_Req_true:
  "(Fun eq [u, u], Fun true []) \<in> rstep (Req x R eq true false s t)" (is "_ \<in> rstep ?R")
  using rstepI [of "Fun eq [Var x, Var x]" "Fun true []" ?R, OF _ refl refl, of \<box> "subst x u"]
  by (simp add: Req_def)

lemma rstep_Req_false:
  "(Fun eq [s \<cdot> \<sigma>, t \<cdot> \<sigma>], Fun false []) \<in> rstep (Req x R eq true false s t)" (is "_ \<in> rstep ?R")
  using rstepI [of "Fun eq [s, t]" "Fun false []" ?R, OF _ refl refl, of \<box> \<sigma>]
  by (simp add: Req_def)

lemma subset_Req: "R \<subseteq> Req x R eq true false s t" by (auto simp: Req_def)

lemma subst_apply_set_const [simp]:
  "A \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<lambda>x. Fun f []) \<subseteq> {t. ground t}"
  by auto

definition "GROUND R = Restr R {t. ground t}"

text \<open>Ground confluence\<close>
abbreviation "GCR R \<equiv> CR (GROUND R)"

lemma gterm_conv_GROUND_conv:
  fixes s t :: "('f, 'v) term"
  assumes ground: "ground s" "ground t"
  assumes conv: "(s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" (is "_ \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*")
  shows "(s, t) \<in> (GROUND (rstep R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  define c :: "('f, 'v) term" where "c = Fun (SOME f. True) []"
  then have [simp]: "ground c" by simp
  let ?\<gamma> = "\<lambda>t. t \<cdot> (\<lambda>x. c)"
  have "(?\<gamma> s, ?\<gamma> t) \<in> (GROUND ?R)\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def
    by (intro rtrancl_map [OF _ conv [unfolded conversion_def], of ?\<gamma> "(GROUND ?R)\<^sup>\<leftrightarrow>"])
      (force simp: GROUND_def)
  then show ?thesis
    using ground by (simp add: ground_subst_apply)
qed

lemma fground_subst_apply:
  assumes "fground F t"
  shows "t \<cdot> \<sigma> = t"
proof -
  have "t = t \<cdot> Var" by simp
  also have "\<dots> = t \<cdot> \<sigma>"
    by (rule term_subst_eq, insert assms[unfolded fground_def ground_vars_term_empty], auto)
  finally show ?thesis by simp
qed

lemma fgterm_conv_FGROUND_conv:
  fixes s t :: "('f, 'v) term"
  assumes "funas_trs R \<subseteq> F"
    and fground: "fground F s" "fground F t"
    and conv: "(s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" (is "_ \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*")
  shows "(s, t) \<in> (FGROUND F (rstep R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  define c :: 'f where "c = (SOME f. (f, 0) \<in> funas_term s)"
  have "\<exists>f. (f, 0) \<in> funas_term s" using fground(1)
  proof (induct s)
    case (Fun f ts)
    show ?case
    proof (cases ts)
      case (Cons u us)
      then have "u \<in> set ts" and "fground F u" using Fun.prems by (auto simp: fground_def)
      with Fun.hyps [of u] obtain g where "(g, 0) \<in> funas_term u" by blast
      then show ?thesis using Cons by auto
    qed simp
  qed (simp add: fground_def)
  then have "(c, 0) \<in> funas_term s"
    unfolding c_def by (auto intro: someI_ex)
  then have [simp]: "(c, 0) \<in> F" using fground by (auto simp: fground_def)
  let ?c = "Fun c [] :: ('f, 'v) term"
  have "funas_term ?c \<subseteq> F" by (auto simp: fground_def)
  then have [simp]: "fground F ?c" "ground ?c" by (auto simp: fground_def c_def)
  interpret cleaning_const F "\<lambda>_. ?c" "?c" by (standard, fact) simp
  let ?\<gamma> = "\<lambda>t. clean_term t \<cdot> (\<lambda>x. ?c)"
  have [simp]: "fground F (?\<gamma> t)" for t by (auto simp: fground_def funas_term_subst)
  note * = rstep_imp_clean_rstep_or_Id [OF assms(1)]
  have "(?\<gamma> s, ?\<gamma> t) \<in> ((FGROUND F ?R)\<^sup>\<leftrightarrow>\<^sup>*)\<^sup>*"
    unfolding conversion_def
    apply (intro rtrancl_map [OF _ conv [unfolded conversion_def], of ?\<gamma> "((FGROUND F ?R)\<^sup>\<leftrightarrow>)\<^sup>*"])
    apply (auto simp: FGROUND_def)
     apply (drule *, auto)+
    done
  then have "(?\<gamma> s, ?\<gamma> t) \<in> (FGROUND F ?R)\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def by simp
  then show ?thesis
    using fground and fground_subst_apply
    by (metis clean_term_ident fground_def)
qed


lemma conversion_imp_ground_NF_eq:
  fixes R :: "('f, 'v) trs"
  assumes GCR: "GCR (ordstep ord S)"
    and "subst.closed ord"
    and gconv: "(GROUND (rstep (Req x R eq true false s t)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq>
     (GROUND (ordstep ord S))\<^sup>\<leftrightarrow>\<^sup>*" (is "(GROUND ?R)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (GROUND ?S)\<^sup>\<leftrightarrow>\<^sup>*")
    and conv: "\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<forall>u v. (Fun true [], u) \<in> (GROUND (ordstep ord S))\<^sup>! \<and>
    (Fun false [], v) \<in> (GROUND (ordstep ord S))\<^sup>! \<longrightarrow> u = v"
proof (intro allI impI; elim conjE)
  let ?true = "Fun true []"
  fix u v assume "(Fun true [], u) \<in> (GROUND ?S)\<^sup>!" (is "(?true, _) \<in> _")
    and "(Fun false [], v) \<in> (GROUND ?S)\<^sup>!" (is "(?false, _) \<in> _")
  then have NFs: "u \<in> NF (GROUND ?S)" "v \<in> NF (GROUND ?S)" by auto
  let ?\<gamma> = "\<lambda>t. t \<cdot> (\<lambda>x. ?true)"
  obtain \<sigma> where "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
    using conv and conversion_mono [of _ ?R, OF subset_Req [THEN rstep_mono]] by blast
  then have "(Fun eq [s \<cdot> \<sigma>, s \<cdot> \<sigma>], Fun eq [s \<cdot> \<sigma>, t \<cdot> \<sigma>]) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def by (intro args_steps_imp_steps) (auto simp: nth_Cons')
  moreover have "(?true, Fun eq [s \<cdot> \<sigma>, s \<cdot> \<sigma>]) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" and "(Fun eq [s \<cdot> \<sigma>, t \<cdot> \<sigma>], ?false) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
    using rstep_Req_true [of eq "s \<cdot> \<sigma>"] and rstep_Req_false
    by (force simp: conversion_inv [of "Fun true []"])+
  ultimately have "(?true, ?false) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" by (blast dest: rtrancl_trans)
  from gterm_conv_GROUND_conv [OF _ _ this]
  have "(?\<gamma> ?true, ?\<gamma> ?false) \<in> (GROUND ?R)\<^sup>\<leftrightarrow>\<^sup>*" by simp
  then have "(?true, ?false) \<in> (GROUND ?R)\<^sup>\<leftrightarrow>\<^sup>*" by simp
  with gconv have "(?true, ?false) \<in> (GROUND ?S)\<^sup>\<leftrightarrow>\<^sup>*" by blast
  with CR_imp_conversionIff_join [OF GCR [unfolded GROUND_def], folded GROUND_def]
  obtain w where "(?true, w) \<in> (GROUND ?S)\<^sup>*"
    and "(?false, w) \<in> (GROUND ?S)\<^sup>*" by blast
  moreover have "ground ?true" and "ground ?false" by auto
  ultimately have "(w, u) \<in> (GROUND ?S)\<^sup>*" and "(w, v) \<in> (GROUND ?S)\<^sup>*"
    using GCR and \<open>(?true, u) \<in> (GROUND ?S)\<^sup>!\<close> and \<open>(?false, v) \<in> (GROUND ?S)\<^sup>!\<close>
    by (meson CR_join_right_I NF_join_imp_reach joinI_right normalizability_E)+
  then show "u = v"
    using GCR and NFs by (auto simp: CR_defs dest: join_NF_imp_eq simp del: ground_subst)
qed

lemma conversion_imp_fground_NF_eq:
  fixes R :: "('f, 'v) trs"
  assumes F: "funas_term s \<subseteq> F" "funas_term t \<subseteq> F" "funas_trs R \<subseteq> F" "{(eq, 2), (true, 0), (false, 0)} \<subseteq> F"
  assumes FGCR: "CR (FGROUND F (ordstep ord S))"
    and "subst.closed ord"
    and gconv: "(FGROUND F (rstep (Req x R eq true false s t)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq>
     (FGROUND F (ordstep ord S))\<^sup>\<leftrightarrow>\<^sup>*" (is "(FGROUND F ?R)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (FGROUND F ?S)\<^sup>\<leftrightarrow>\<^sup>*")
    and conv: "\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<forall>u v. (Fun true [], u) \<in> (FGROUND F (ordstep ord S))\<^sup>! \<and>
    (Fun false [], v) \<in> (FGROUND F (ordstep ord S))\<^sup>! \<longrightarrow> u = v"
proof (intro allI impI; elim conjE)
  have funas_Req: "funas_trs (Req x R eq true false s t) \<subseteq> F"
    using F by (auto simp: Req_def funas_defs numeral_2_eq_2)
  let ?true = "Fun true []"
  fix u v assume "(Fun true [], u) \<in> (FGROUND F ?S)\<^sup>!" (is "(?true, _) \<in> _")
    and "(Fun false [], v) \<in> (FGROUND F ?S)\<^sup>!" (is "(?false, _) \<in> _")
  then have NFs: "u \<in> NF (FGROUND F ?S)" "v \<in> NF (FGROUND F ?S)" by auto
  let ?\<gamma> = "\<lambda>t. t \<cdot> (\<lambda>x. ?true)"
  obtain \<sigma> where "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
    using conv and conversion_mono [of _ ?R, OF subset_Req [THEN rstep_mono]] by blast
  then have "(Fun eq [s \<cdot> \<sigma>, s \<cdot> \<sigma>], Fun eq [s \<cdot> \<sigma>, t \<cdot> \<sigma>]) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def by (intro args_steps_imp_steps) (auto simp: nth_Cons')
  moreover have "(?true, Fun eq [s \<cdot> \<sigma>, s \<cdot> \<sigma>]) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" and "(Fun eq [s \<cdot> \<sigma>, t \<cdot> \<sigma>], ?false) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*"
    using rstep_Req_true [of eq "s \<cdot> \<sigma>"] and rstep_Req_false
    by (force simp: conversion_inv [of "Fun true []"])+
  ultimately have "(?true, ?false) \<in> ?R\<^sup>\<leftrightarrow>\<^sup>*" by (blast dest: rtrancl_trans)
  from fgterm_conv_FGROUND_conv [OF funas_Req _ _ this]
  have "(?\<gamma> ?true, ?\<gamma> ?false) \<in> (FGROUND F ?R)\<^sup>\<leftrightarrow>\<^sup>*" using F by (auto simp: fground_def)
  then have "(?true, ?false) \<in> (FGROUND F ?R)\<^sup>\<leftrightarrow>\<^sup>*" by simp
  with gconv have "(?true, ?false) \<in> (FGROUND F ?S)\<^sup>\<leftrightarrow>\<^sup>*" by blast
  with CR_imp_conversionIff_join [OF FGCR]
  obtain w where "(?true, w) \<in> (FGROUND F ?S)\<^sup>*"
    and "(?false, w) \<in> (FGROUND F ?S)\<^sup>*" by blast
  moreover have "ground ?true" and "ground ?false" by auto
  ultimately have "(w, u) \<in> (FGROUND F ?S)\<^sup>*" and "(w, v) \<in> (FGROUND F ?S)\<^sup>*"
    using FGCR and \<open>(?true, u) \<in> (FGROUND F ?S)\<^sup>!\<close> and \<open>(?false, v) \<in> (FGROUND F ?S)\<^sup>!\<close>
    by (meson CR_join_right_I NF_join_imp_reach joinI_right normalizability_E)+
  then show "u = v"
    using FGCR and NFs by (auto simp: CR_defs dest: join_NF_imp_eq simp del: ground_subst)
qed

lemma infeasibility_via_GCR:
  assumes "GCR (ordstep ord S)"
    and "subst.closed ord"
    and "(GROUND (rstep (Req x R eq true false s t)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq>
     (GROUND (ordstep ord S))\<^sup>\<leftrightarrow>\<^sup>*" (is "(GROUND ?R)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (GROUND ?S)\<^sup>\<leftrightarrow>\<^sup>*")
    and "(Fun true [], u) \<in> (GROUND (ordstep ord S))\<^sup>! \<and>
      (Fun false [], v) \<in> (GROUND (ordstep ord S))\<^sup>! \<and> u \<noteq> v"
  shows "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*)"
  using conversion_imp_ground_NF_eq [OF assms(1-3)] and assms(4) by blast

lemma infeasibility_via_FGCR:
  assumes F: "funas_term s \<subseteq> F" "funas_term t \<subseteq> F" "funas_trs R \<subseteq> F" "{(eq, 2), (true, 0), (false, 0)} \<subseteq> F"
    and "CR (FGROUND F (ordstep ord S))"
    and "subst.closed ord"
    and "(FGROUND F (rstep (Req x R eq true false s t)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq>
     (FGROUND F (ordstep ord S))\<^sup>\<leftrightarrow>\<^sup>*"
    and "(Fun true [], u) \<in> (FGROUND F (ordstep ord S))\<^sup>! \<and>
      (Fun false [], v) \<in> (FGROUND F (ordstep ord S))\<^sup>! \<and> u \<noteq> v"
  shows "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*)"
  using conversion_imp_fground_NF_eq [OF F assms(5-7)] and assms(8) by blast

locale least_element =
  fixes r A
  assumes SN: "SN (Restr r A)"
    and total: "total_on A r"
    and trans: "trans (Restr r A)"
begin

definition "least_elt = (THE x. x \<in> A \<and> (\<forall>y. (x, y) \<in> (Restr r A) \<longrightarrow> y = x))"

lemma least_ex:
  assumes "x \<in> A"
  shows "\<exists>y. (x, y) \<in> (Restr r A)\<^sup>= \<and> (\<forall>z. (y, z) \<in> (Restr r A) \<longrightarrow> z = y)"
  using SN and assms
proof (induct rule: SN_induct [consumes 1])
  case (1 x)
  then show ?case
  proof (cases "\<forall>y. (x, y) \<in> (Restr r A) \<longrightarrow> y = x")
    case False
    then obtain y where "(x, y) \<in> (Restr r A)" "y \<in> A" and "y \<noteq> x" by blast
    with 1 show ?thesis using trans [THEN transD] by blast
  qed blast
qed

lemma least_ex1:
  assumes "x \<in> A"
  shows "\<exists>!y. y \<in> A \<and> (\<forall>z. (y, z) \<in> (Restr r A) \<longrightarrow> z = y)"
  using least_ex [OF assms] and total [unfolded total_on_def] and assms by blast

lemma least_elt:
  assumes "x \<in> A"
  shows "least_elt \<in> A \<and> (\<forall>y. (least_elt, y) \<in> (Restr r A) \<longrightarrow> y = least_elt)"
  using theI' [OF least_ex1 [OF assms], folded least_elt_def] .

end

context reduction_order
begin

lemma infeasibility_via_GCR:
  assumes "GCR (ordstep {\<succ>} S)"
    and "(GROUND (rstep (Req x R eq true false s t)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (GROUND (ordstep {\<succ>} S))\<^sup>\<leftrightarrow>\<^sup>*"
    and "(Fun true [], u) \<in> (GROUND (ordstep {\<succ>} S))\<^sup>!"
    and "(Fun false [], v) \<in> (GROUND (ordstep {\<succ>} S))\<^sup>!"
    and "u \<noteq> v"
  shows "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*)"
  using infeasibility_via_GCR [OF assms(1) subst_closed_less assms(2)] and assms(3-) by simp

lemma infeasibility_via_FGCR:
  assumes F: "funas_term s \<subseteq> F" "funas_term t \<subseteq> F" "funas_trs R \<subseteq> F" "{(eq, 2), (true, 0), (false, 0)} \<subseteq> F"
    and FGCR: "CR (FGROUND F (ordstep {\<succ>} S))"
    and subset: "(FGROUND F (rstep (Req x R eq true false s t)))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq>
     (FGROUND F (ordstep {\<succ>} S))\<^sup>\<leftrightarrow>\<^sup>*"
    and neq_NF: "(Fun true [], u) \<in> (FGROUND F (ordstep {\<succ>} S))\<^sup>!"
      "(Fun false [], v) \<in> (FGROUND F (ordstep {\<succ>} S))\<^sup>!"
      "u \<noteq> v"
  shows "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*)"
  using infeasibility_via_FGCR [OF F FGCR subst_closed_less subset] and neq_NF by blast

end

definition ooverlap ::
    "('a, 'b::infinite) term rel \<Rightarrow> ('a, 'b) trs \<Rightarrow> ('a, 'b) rule \<Rightarrow> ('a, 'b) rule \<Rightarrow>
      pos \<Rightarrow> ('a, 'b) subst \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool"
  where
    "ooverlap ord R r r' p \<mu> u v \<longleftrightarrow>
      (\<exists>p. p \<bullet> r \<in> R) \<and> (\<exists>p. p \<bullet> r' \<in> R) \<and> vars_rule r \<inter> vars_rule r' = {} \<and>
      p \<in> fun_poss (fst r') \<and>
      mgu (fst r) (fst r' |_ p) = Some \<mu> \<and>
      (snd r \<cdot> \<mu>, fst r \<cdot> \<mu>) \<notin> ord \<and> (snd r' \<cdot> \<mu>, fst r' \<cdot> \<mu>) \<notin> ord \<and>
      u = replace_at (fst r' \<cdot> \<mu>) p (snd r \<cdot> \<mu>) \<and>
      v = snd r' \<cdot> \<mu>"

definition "xCP ord R \<equiv> {(u, v) |u v. \<exists>r r' p \<mu>. ooverlap ord R r r' p \<mu> u v}"

lemma ooverlapI:
  "\<pi> \<bullet> (l, r) \<in> R \<Longrightarrow> \<pi>' \<bullet> (l', r') \<in> R \<Longrightarrow> vars_rule (l, r) \<inter> vars_rule (l', r') = {} \<Longrightarrow>
    p \<in> fun_poss l' \<Longrightarrow> mgu l (l' |_ p) = Some \<mu> \<Longrightarrow>
    (r \<cdot> \<mu>, l \<cdot> \<mu>) \<notin> ord \<Longrightarrow> (r' \<cdot> \<mu>, l' \<cdot> \<mu>) \<notin> ord \<Longrightarrow>
    ooverlap ord R (l, r) (l', r') p \<mu> (replace_at (l' \<cdot> \<mu>) p (r \<cdot> \<mu>)) (r' \<cdot> \<mu>)"
  by (force simp: ooverlap_def)

lemma GROUND_subset: "GROUND R \<subseteq> R" by (auto simp: GROUND_def)

lemma GROUND_not_ground:
  assumes "(s, t) \<in> (GROUND R)\<^sup>*" and "\<not> ground s"
  shows "t = s"
  using assms by (induct) (auto simp: GROUND_def)

lemma GROUND_rtrancl:
  assumes "(s, t) \<in> (GROUND R)\<^sup>*" and "ground s"
  shows "ground t \<and> (s, t) \<in> R\<^sup>*"
  using assms by (induct) (auto simp: GROUND_def)

context reduction_order
begin

lemma ground_less:
  assumes "ground s" and "s \<succ> t"
  shows "ground t"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain x where "x \<in> vars_term t" by (induct t) auto
  then obtain C where "t = C\<langle>Var x\<rangle>" by (auto dest: supteq_Var)
  then have [simp]: "s \<succ> (C \<cdot>\<^sub>c subst x s)\<langle>s\<rangle>"
    using \<open>s \<succ> t\<close> [THEN subst, of "subst x s"] and \<open>ground s\<close> by (simp add: ground_subst_apply)
  define f where "f n = ((C \<cdot>\<^sub>c subst x s) ^ n)\<langle>s\<rangle>" for n
  then have "f i \<succ> f (Suc i)" for i
    by (induct i) (simp_all add: ctxt)
  with SN_less show False by (auto simp: SN_defs)
qed

lemma ordstep_GROUND:
  "ground s \<Longrightarrow> (s, t) \<in> ordstep {\<succ>} R \<Longrightarrow> (s, t) \<in> GROUND (ordstep {\<succ>} R)"
  by (auto simp: GROUND_def dest: ordstep_imp_ord [OF ctxt_closed_less] ground_less)

lemma ordsteps_GROUND:
  assumes "(s, t) \<in> (ordstep {\<succ>} R)\<^sup>*" and "ground s"
  shows "ground t \<and> (s, t) \<in> (GROUND (ordstep {\<succ>} R))\<^sup>*"
  using assms
  by (induct rule: rtrancl_induct)
    (auto dest!: ordstep_GROUND, auto simp: GROUND_def)

lemma ordstep_join_GROUND:
  assumes "ground s" and "ground t" and "(s, t) \<in> (ordstep {\<succ>} R)\<^sup>\<down>"
  shows "(s, t) \<in> (GROUND (ordstep {\<succ>} R))\<^sup>\<down>"
  using assms by (auto simp: join_def rtrancl_converse dest: ordsteps_GROUND)

lemma GCR_eq_CR_GROUND:
  "GCR (ordstep {\<succ>} R) = CR (GROUND (ordstep {\<succ>} R))"
  by (auto simp: CR_defs dest!: ordsteps_GROUND)

end

lemma (in reduction_order) funas_ordstep:
  assumes step: "(s, t) \<in> (ordstep {\<succ>} R)"
    and funas_less: "funas_trs {\<succ>} \<subseteq> F"
    and "funas_term s \<subseteq> F"
  shows "funas_term t \<subseteq> F"
  using assms funas_less unfolding ordstep.simps
  by (metis ctxt_closed_less step ordstep_imp_ord rhs_wf)

  (*TODO: move*)
locale fgtotal_reduction_order_inf =
  fgtotal_reduction_order less F
  for less :: "('a, 'b::infinite) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50)
  and F :: "('a \<times> nat) set"
begin


lemma fground_ordstep:
  assumes ground: "fground F s"
    and step: "(s, t) \<in> (ordstep {\<succ>} R)"
  shows "fground F t"
  using assms funas_ordstep[OF step funas_less] ordstep_GROUND[OF _ step]
  unfolding fground_def GROUND_def by auto

lemma ordstep_FGROUND:
  "fground F s \<Longrightarrow> (s, t) \<in> ordstep {\<succ>} R \<Longrightarrow> (s, t) \<in> FGROUND F (ordstep {\<succ>} R)"
  using fground_ordstep by (auto simp: FGROUND_def)

lemma ordsteps_FGROUND:
  assumes "(s, t) \<in> (ordstep {\<succ>} R)\<^sup>*" and "fground F s"
  shows "fground F t \<and> (s, t) \<in> (FGROUND F (ordstep {\<succ>} R))\<^sup>*"
  using assms
  by (induct rule: rtrancl_induct)
    (auto dest!: ordstep_FGROUND, auto simp: FGROUND_def)

lemma ordstep_join:
  assumes ground: "fground F s" "fground F t"
    and R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> R"
    and *: "(s, t) \<in> (ordstep {\<succ>} R)\<^sup>\<down> \<or> (\<exists>l r \<sigma>. (l, r) \<in> R\<^sup>\<leftrightarrow> \<and> s = l \<cdot> \<sigma> \<and> t = r \<cdot> \<sigma>)"
  shows "(s, t) \<in> (ordstep {\<succ>} R)\<^sup>\<down>"
  using *
proof (elim disjE exE conjE)
  fix l r \<sigma> assume "(l, r) \<in> R\<^sup>\<leftrightarrow>" and "s = l \<cdot> \<sigma>" and "t = r \<cdot> \<sigma>"
  then have "(s, t) \<in> ((ordstep {\<succ>} R)\<^sup>\<leftrightarrow>)\<^sup>="
    using fgtotal [OF ground]
    apply (auto simp del: ground_subst intro: ordstep.intros [where C = \<box> and \<sigma> = \<sigma>] simp: subst)
    apply (frule R)
    apply (auto intro: ordstep.intros [where C = \<box> and \<sigma> = \<sigma>] simp: subst)
    apply (frule R)
    apply (auto intro: ordstep.intros [where C = \<box> and \<sigma> = \<sigma>] simp: subst)
    done
  then show "(s, t) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" by blast
qed

lemma perm_less:
  "\<pi> \<bullet> s \<succ> \<pi> \<bullet> t \<longleftrightarrow> s \<succ> t"
  using subst [of "\<pi> \<bullet> s" "\<pi> \<bullet> t" "sop (-\<pi>)"]
    and subst [of s t "sop \<pi>"]
  by auto

lemma non_ooverlap_FGROUND_joinable:
  assumes R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> R"
    and s1: "s = C\<^sub>1\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>" and s2: "s = C\<^sub>2\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
    and vpos: "hole_pos C \<notin> fun_poss l\<^sub>2"
    and [simp]: "C\<^sub>1 = C\<^sub>2 \<circ>\<^sub>c C"
    and lr\<^sub>1: "(l\<^sub>1 \<cdot> \<sigma>\<^sub>1, r\<^sub>1 \<cdot> \<sigma>\<^sub>1) \<in> ordstep {\<succ>} R" (is "_ \<in> ?R")
    and lr\<^sub>2: "(l\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> ordstep {\<succ>} R"
    and t: "t = C\<^sub>1\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>"
    and u: "u = C\<^sub>2\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
    and fground: "fground F t" "fground F u"
    and "\<pi> \<bullet> (l\<^sub>2, r\<^sub>2) \<in> R"
  shows "(t, u) \<in> (FGROUND F ?R)\<^sup>\<down>" (is "_ \<in> ?G\<^sup>\<down>")
proof -
  note ordstep = ordstep.intros [where C = \<box> and ord = "{\<succ>}", OF _ refl refl, simplified]
  have rule\<^sub>2: "(\<pi> \<bullet> l\<^sub>2, \<pi> \<bullet> r\<^sub>2) \<in> R" using assms by (auto simp: eqvt)
  show ?thesis
  proof(cases "C = \<box>")
    case True
    then have "hole_pos C = []" by auto
    with vpos obtain x where x: "l\<^sub>2 = Var x" using poss_is_Fun_fun_poss
      by (metis empty_pos_in_poss is_VarE subt_at.simps(1))
    show ?thesis
    proof (cases "x \<in> vars_term r\<^sub>2")
      case True
      then obtain C where C:"r\<^sub>2 = C\<langle>Var x\<rangle>" by (auto dest: vars_term_supteq)
      from lr\<^sub>2 ctxt have [simp]: "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 \<succ> (C \<cdot>\<^sub>c \<sigma>\<^sub>2)\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" unfolding ordstep.simps x C by auto
      define h where "h n = ((C \<cdot>\<^sub>c \<sigma>\<^sub>2) ^ n)\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" for n
      then have "h i \<succ> h (Suc i)" for i by (induct i) (simp_all add: ctxt)
      with SN_less show ?thesis by (auto simp: SN_defs)
    next
      case False
      with R [OF rule\<^sub>2] and subst [of l\<^sub>2 r\<^sub>2 "subst x r\<^sub>2"] and SN_less
      have rl2: "(\<pi> \<bullet> r\<^sub>2, \<pi> \<bullet> l\<^sub>2) \<in> R"
        using perm_less [of \<pi> "Var x" r\<^sub>2]
        by (force simp: x)
      define \<tau> where "\<tau> = (\<lambda>z. if z = x then r\<^sub>1 \<cdot> \<sigma>\<^sub>1 else \<sigma>\<^sub>2 z)"
      have t1:"l\<^sub>2 \<cdot> \<tau> = r\<^sub>1 \<cdot> \<sigma>\<^sub>1" unfolding x \<tau>_def by auto
      from fground t u have fg:"fground F (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)" "fground F (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)" unfolding fground_def by auto
      with t1 assms fg(1) have g1: "fground F (l\<^sub>2 \<cdot> \<tau>)" by argo
      from False have t2: "r\<^sub>2 \<cdot> \<tau> = r\<^sub>2 \<cdot> \<sigma>\<^sub>2" unfolding \<tau>_def by (simp add: term_subst_eq_conv)
      with fg(2) assms have g2: "fground F (r\<^sub>2 \<cdot> \<tau>)" by simp
      from fgtotal [OF g2 g1] and ordstep [OF rl2, of "sop (-\<pi>) \<circ>\<^sub>s \<tau>"]
        and ordstep [OF rule\<^sub>2, of "sop (-\<pi>) \<circ>\<^sub>s \<tau>"]
      have "(l\<^sub>2 \<cdot> \<tau>, r\<^sub>2 \<cdot> \<tau>) \<in> ?R \<or> (r\<^sub>2 \<cdot> \<tau>, l\<^sub>2 \<cdot> \<tau>) \<in> ?R \<or> r\<^sub>2 \<cdot> \<tau> = l\<^sub>2 \<cdot> \<tau>" by force
      with ordstep_ctxt have "(u, t) \<in> ?R \<or> (t, u) \<in> ?R \<or> u = t"
        unfolding assms True t1 t2 by fastforce
      then show ?thesis
        using fground by (auto dest: ordstep_FGROUND)
    qed
  next
    case False
    have eq: "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 = C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>" using s1 and s2 by simp
    define p where "p = hole_pos C"
    have C: "C = ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" by (simp add: p_def eq)

    have "p \<notin> fun_poss l\<^sub>2" using vpos by (simp add: p_def)
    moreover have "p \<in> poss (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" by (simp add: eq p_def)
    ultimately obtain q\<^sub>1 and q\<^sub>2 and x where p: "p = q\<^sub>1 @ q\<^sub>2" and q\<^sub>1: "q\<^sub>1 \<in> poss l\<^sub>2"
      and lq\<^sub>1: "l\<^sub>2 |_ q\<^sub>1 = Var x" and q\<^sub>2: "q\<^sub>2 \<in> poss (\<sigma>\<^sub>2 x)"
      by (blast intro: poss_subst_apply_term)
    moreover have [simp]: "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 |_ p = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" by (simp add: eq p_def)
    ultimately have [simp]: "\<sigma>\<^sub>2 x |_ q\<^sub>2 = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" by simp

    define \<delta> where "\<delta> y = (if y = x then replace_at (\<sigma>\<^sub>2 x) q\<^sub>2 (r\<^sub>1 \<cdot> \<sigma>\<^sub>1) else \<sigma>\<^sub>2 y)" for y

    have \<delta>_x: "\<delta> x = replace_at (\<sigma>\<^sub>2 x) q\<^sub>2 (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)" by (simp add: \<delta>_def)
    have "(\<sigma>\<^sub>2 x, \<delta> x) \<in> ?R"
      using ordstep_ctxt [OF lr\<^sub>1, of "ctxt_of_pos_term q\<^sub>2 (\<sigma>\<^sub>2 x)"] and q\<^sub>2
      by (simp add: \<delta>_def replace_at_ident)
    then have *: "\<And>x. (\<sigma>\<^sub>2 x, \<delta> x) \<in> ?R\<^sup>*" by (auto simp: \<delta>_def)
    then have "(r\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<delta>) \<in> ?R\<^sup>*"
      using all_ctxt_closed_subst_step [OF all_ctxt_closed_ordsteps] by metis
    then have u1: "(u, C\<^sub>2\<langle>r\<^sub>2 \<cdot> \<delta>\<rangle>) \<in> ?R\<^sup>*" by (auto simp: u ordsteps_ctxt)
    have t1: "(t, C\<^sub>2\<langle>l\<^sub>2 \<cdot> \<delta>\<rangle>) \<in> ?R\<^sup>*"
    proof -
      have "C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle> = replace_at (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) q\<^sub>1 (\<delta> x)"
        using q\<^sub>1 and q\<^sub>2 by (simp add: \<delta>_def ctxt_of_pos_term_append lq\<^sub>1 C p)
      moreover
      have "(replace_at (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) q\<^sub>1 (\<delta> x), l\<^sub>2 \<cdot> \<delta>) \<in> ?R\<^sup>*"
        by (rule replace_at_subst_steps [OF all_ctxt_closed_ordsteps refl_rtrancl * q\<^sub>1 lq\<^sub>1])
      ultimately show ?thesis by (simp add: t ordsteps_ctxt)
    qed
    consider "(C\<^sub>2\<langle>l\<^sub>2 \<cdot> \<delta>\<rangle>, C\<^sub>2\<langle>r\<^sub>2 \<cdot> \<delta>\<rangle>) \<in> ?R\<^sup>=" | "(C\<^sub>2\<langle>r\<^sub>2 \<cdot> \<delta>\<rangle>, C\<^sub>2\<langle>l\<^sub>2 \<cdot> \<delta>\<rangle>) \<in> ?R"
    proof -
      have "fground F (C\<^sub>2\<langle>l\<^sub>2 \<cdot> \<delta>\<rangle>)" and "fground F (C\<^sub>2\<langle>r\<^sub>2 \<cdot> \<delta>\<rangle>)"
        using \<open>fground F t\<close> and \<open>fground F u\<close> and t1 and u1 by (auto dest: ordsteps_FGROUND)
      hence "fground F (l\<^sub>2 \<cdot> \<delta>)" and "fground F (r\<^sub>2 \<cdot> \<delta>)" by (simp add: fground_def)+
      from fgtotal [OF this]
      show ?thesis
        using R [OF rule\<^sub>2] and ordstep [OF rule\<^sub>2, of "sop (-\<pi>) \<circ>\<^sub>s \<delta>", simplified]
          and ordstep [of "\<pi> \<bullet> r\<^sub>2" "\<pi> \<bullet> l\<^sub>2" R "sop (-\<pi>) \<circ>\<^sub>s \<delta>", simplified]
          and irrefl
        by (auto dest: subst trans simp: perm_less ordstep_ctxt intro: that)
    qed
    then show ?thesis
    proof (cases)
      case 1
      with t1 have "(t, C\<^sub>2\<langle>r\<^sub>2 \<cdot> \<delta>\<rangle>) \<in> ?R\<^sup>*" by auto
      with u1 show ?thesis using \<open>fground F u\<close> and \<open>fground F t\<close> by (auto dest!: ordsteps_FGROUND)
    next
      case 2
      with u1 have "(u, C\<^sub>2\<langle>l\<^sub>2 \<cdot> \<delta>\<rangle>) \<in> ?R\<^sup>*" by auto
      with t1 show ?thesis using \<open>fground F u\<close> and \<open>fground F t\<close> by (auto dest!: ordsteps_FGROUND)
    qed
  qed
qed

lemma ground_joinable_ooverlaps_implies_GCR:
  assumes ooverlaps: "\<And>r r' p \<mu> u v. ooverlap {\<succ>} R r r' p \<mu> u v \<Longrightarrow> fground_joinable F {\<succ>} R u v"
  and R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> R"
  shows "CR (FGROUND F (ordstep {\<succ>} R))" (is "CR (FGROUND F ?R)" is "CR ?G")
proof
  fix s t' u' assume st: "(s, t') \<in> ?G\<^sup>*" and su: "(s, u') \<in> ?G\<^sup>*"
  then show "(t', u') \<in> ?G\<^sup>\<down>"
  proof (induct s arbitrary: t' u' rule: SN_induct [OF SN_less])
    case less: (1 s)
    have *: "r\<^sup>* = r O r\<^sup>* \<union> Id" for r :: "('a, 'b) term rel" by regexp
    consider t and u where "fground F s"
      and "(s, t) \<in> ?G" and "(t, t') \<in> ?G\<^sup>*" and "fground F t"
      and "(s, u) \<in> ?G" and "(u, u') \<in> ?G\<^sup>*" and "fground F u" | "s = t'" | "s = u'"
      using less.prems by (subst (asm) (3 4) *) (auto simp: FGROUND_def)
    then show ?case using less.prems
    proof (cases)
      case 1
      moreover have "s \<succ> t" and "s \<succ> u"
        using 1 by (auto simp: FGROUND_def dest: ordstep_imp_ord [OF ctxt_closed_less])
      moreover obtain v where tv: "(t, v) \<in> ?G\<^sup>*" and "(u, v) \<in> ?G\<^sup>*"
      proof -
        obtain C\<^sub>1 and C\<^sub>2 and \<sigma> and \<sigma>\<^sub>2 and l and l\<^sub>2 and r and r\<^sub>2
          where "(l, r) \<in> R" and "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" and s1: "s = C\<^sub>1\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<^sub>1\<langle>r \<cdot> \<sigma>\<rangle>"
            and "(l\<^sub>2, r\<^sub>2) \<in> R" and "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 \<succ> r\<^sub>2 \<cdot> \<sigma>\<^sub>2" and s2: "s = C\<^sub>2\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" and u: "u = C\<^sub>2\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>"
          using 1(2, 5) by (auto simp: FGROUND_def) (fast elim: ordstep.cases)
        then have lr: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ?R" and lr\<^sub>2: "(l\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> ?R"
          and "0 \<bullet> (l, r) \<in> R"
          by (auto intro: ordstep.intros [where C = \<box>])

        obtain \<pi> where "vars_rule (\<pi> \<bullet> (l, r)) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}"
          using vars_rule_disjoint by blast
        moreover define l\<^sub>1 and r\<^sub>1 and \<sigma>\<^sub>1 where "l\<^sub>1 = \<pi> \<bullet> l" and "r\<^sub>1 = \<pi> \<bullet> r" and "\<sigma>\<^sub>1 = sop (-\<pi>) \<circ>\<^sub>s \<sigma>"
        ultimately have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}" by (auto simp: eqvt)
        have "l\<^sub>1 \<cdot> \<sigma>\<^sub>1 \<succ> r\<^sub>1 \<cdot> \<sigma>\<^sub>1" using \<open>l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>\<close> by (simp add: l\<^sub>1_def \<sigma>\<^sub>1_def r\<^sub>1_def)
        have t': "t = C\<^sub>1\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>" by (auto simp: t r\<^sub>1_def \<sigma>\<^sub>1_def)

        have rule\<^sub>1: "-\<pi> \<bullet> (l\<^sub>1, r\<^sub>1) \<in> R" and rule\<^sub>2: "0 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> R"
          using \<open>(l, r) \<in> R\<close> and \<open>(l\<^sub>2, r\<^sub>2) \<in> R\<close> unfolding l\<^sub>1_def r\<^sub>1_def by simp_all

        define \<tau> where "\<tau> x = (if x \<in> vars_rule (l\<^sub>1, r\<^sub>1) then \<sigma>\<^sub>1 x else \<sigma>\<^sub>2 x)" for x
        then have \<tau>: "l\<^sub>1 \<cdot> \<tau> = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" "l\<^sub>2 \<cdot> \<tau> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" "r\<^sub>1 \<cdot> \<tau>  = r\<^sub>1 \<cdot> \<sigma>\<^sub>1" "r\<^sub>2 \<cdot> \<tau> = r\<^sub>2 \<cdot> \<sigma>\<^sub>2"
          using disj by (auto simp: vars_defs term_subst_eq_conv)

        have s_mctxt: "s = fill_holes (mctxt_of_ctxt C\<^sub>1) [l \<cdot> \<sigma>]" by (simp add: s1)
        have t_mctxt: "t = fill_holes (mctxt_of_ctxt C\<^sub>1) [r \<cdot> \<sigma>]" by (simp add: t)
        have u_mctxt: "u = fill_holes (mctxt_of_ctxt C\<^sub>2) [r\<^sub>2 \<cdot> \<sigma>\<^sub>2]" by (simp add: u)

        show ?thesis using s1 and s2
        proof (cases rule: two_subterms_cases)
          case eq
          then have "l\<^sub>2 \<cdot> \<tau> = l\<^sub>1 \<cdot> \<tau>" unfolding \<tau> by (auto simp: l\<^sub>1_def \<sigma>\<^sub>1_def)
          then obtain \<mu> where mgu: "mgu l\<^sub>2 l\<^sub>1 = Some \<mu>"
            using mgu_complete by (auto simp: unifiers_def)
          then have "is_mgu \<mu> {(l\<^sub>2, l\<^sub>1)}" by (simp add: mgu_sound is_imgu_imp_is_mgu)
          with \<open>l\<^sub>2 \<cdot> \<tau> = l\<^sub>1 \<cdot> \<tau>\<close> obtain \<delta> where \<tau>': "\<tau> = \<mu> \<circ>\<^sub>s \<delta>" by (auto simp: is_mgu_def unifiers_def)
          then have \<tau>'': "t \<cdot> \<mu> \<cdot> \<delta> = t \<cdot> \<tau>" for t by simp
          have not_less: "(r\<^sub>1 \<cdot> \<mu>, l\<^sub>1 \<cdot> \<mu>) \<notin> {\<succ>}" "(r\<^sub>2 \<cdot> \<mu>, l\<^sub>2 \<cdot> \<mu>) \<notin> {\<succ>}"
            using \<open>l\<^sub>1 \<cdot> \<sigma>\<^sub>1 \<succ> r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<close> and \<open>l\<^sub>2 \<cdot> \<sigma>\<^sub>2 \<succ> r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<close> and irrefl
            by (auto dest!: subst [of "r\<^sub>1 \<cdot> \<mu>" "l\<^sub>1 \<cdot> \<mu>" \<delta>] subst [of "r\<^sub>2 \<cdot> \<mu>" "l\<^sub>2 \<cdot> \<mu>" \<delta>] simp: \<tau>'' \<tau> dest: trans)
          show ?thesis
          proof (cases l\<^sub>1)
            case (Fun f ls)
            with ooverlapI [OF rule\<^sub>2 rule\<^sub>1 _ _ _ not_less(2,1), of "[]"] and mgu and disj
            have ooverlap:"ooverlap {\<succ>} R (l\<^sub>2, r\<^sub>2) (l\<^sub>1, r\<^sub>1) [] \<mu> (r\<^sub>2 \<cdot> \<mu>) (r\<^sub>1 \<cdot> \<mu>)" by auto
            have "fground F (r\<^sub>2 \<cdot> \<mu> \<cdot> \<delta>) \<and> fground F (r\<^sub>1 \<cdot> \<mu> \<cdot> \<delta>)" using 1 \<tau> \<tau>'' t' u
              by (auto simp:fground_def)
            from ooverlaps [OF ooverlap, unfolded fground_joinable_def, rule_format, OF this]
              have "(r\<^sub>1 \<cdot> \<tau>, r\<^sub>2 \<cdot> \<tau>) \<in> ?R\<^sup>\<down>" unfolding \<tau>'' by auto
            with ordstep_join [OF _ _ R] and 1 have "(r\<^sub>1 \<cdot> \<sigma>\<^sub>1, r\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> ?R\<^sup>\<down>" by (auto simp: \<tau> t' u)
            then have "(t, u) \<in> ?R\<^sup>\<down>" apply (auto simp: t' u)
              by (simp add: eq(1) join_ctxt ordstep_rstep_conv' subst_closed_less)
            then obtain v where "(t, v) \<in> ?G\<^sup>*" and "(u, v) \<in> ?G\<^sup>*"
              using 1 by (auto dest!: ordsteps_FGROUND)
            then show ?thesis by (intro that)
          next
            case (Var x)
            with \<open>l\<^sub>1 = \<pi> \<bullet> l\<close> have "hole_pos \<box> \<notin> fun_poss l"
              by (metis equals0D fun_poss.simps(1) fun_poss_perm_simp)
            from non_ooverlap_FGROUND_joinable [OF R s2 s1 this _ lr\<^sub>2 lr u t \<open>fground F u\<close> \<open>fground F t\<close> \<open>0 \<bullet> (l, r) \<in> R\<close>]
            have ut:"(t, u) \<in> ?G\<^sup>\<down>" unfolding eq by (auto simp:fground_def)
            then show ?thesis by (elim joinE) (blast intro: that)
          qed
        next
          case [simp]: (parallel1 C)
          have "fill_holes C [r \<cdot> \<sigma>, l\<^sub>2 \<cdot> \<sigma>\<^sub>2] =\<^sub>f (mctxt_of_ctxt C\<^sub>1, concat [[r \<cdot> \<sigma>],[]])"
            unfolding parallel1 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
          then have t: "t = fill_holes C [r \<cdot> \<sigma>, l\<^sub>2 \<cdot> \<sigma>\<^sub>2]" using t_mctxt by (auto dest: eqfE)
          have "fill_holes C [l \<cdot> \<sigma>, r\<^sub>2 \<cdot> \<sigma>\<^sub>2] =\<^sub>f (mctxt_of_ctxt C\<^sub>2, concat [[], [r\<^sub>2 \<cdot> \<sigma>\<^sub>2]])"
            unfolding parallel1 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
          then have u: "u = fill_holes C [l \<cdot> \<sigma>, r\<^sub>2 \<cdot> \<sigma>\<^sub>2]" using u_mctxt by (auto dest: eqfE)

          from ctxt_imp_mctxt [OF _ lr, of C "[]" "[r\<^sub>2 \<cdot> \<sigma>\<^sub>2]"] and ordstep_ctxt [of _ _ "{\<succ>}" R]
          have "(u, fill_holes C [r \<cdot> \<sigma>, r\<^sub>2 \<cdot> \<sigma>\<^sub>2]) \<in> ?G\<^sup>*" using 1 by (auto simp: u ordstep_FGROUND)
          moreover from ctxt_imp_mctxt [OF _ lr\<^sub>2, of C "[r \<cdot> \<sigma>]" "[]"] and ordstep_ctxt [of _ _ "{\<succ>}" R]
          have "(t, fill_holes C [r \<cdot> \<sigma>, r\<^sub>2 \<cdot> \<sigma>\<^sub>2]) \<in> ?G\<^sup>*" using 1 by (auto simp: t ordstep_FGROUND)
          ultimately show ?thesis by (intro that)
        next
          case [simp]: (parallel2 C)
          have "fill_holes C [l\<^sub>2 \<cdot> \<sigma>\<^sub>2, r \<cdot> \<sigma>] =\<^sub>f (mctxt_of_ctxt C\<^sub>1, concat [[], [r \<cdot> \<sigma>]])"
            unfolding parallel2 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
          then have t: "t = fill_holes C [l\<^sub>2 \<cdot> \<sigma>\<^sub>2, r \<cdot> \<sigma>]" using t_mctxt by (auto dest: eqfE)
          have "fill_holes C [r\<^sub>2 \<cdot> \<sigma>\<^sub>2, l \<cdot> \<sigma>] =\<^sub>f (mctxt_of_ctxt C\<^sub>2, concat [[r\<^sub>2 \<cdot> \<sigma>\<^sub>2], []])"
            unfolding parallel2 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
          then have u: "u = fill_holes C [r\<^sub>2 \<cdot> \<sigma>\<^sub>2, l \<cdot> \<sigma>]" using u_mctxt by (auto dest: eqfE)

          from ctxt_imp_mctxt [OF _ lr, of C "[r\<^sub>2 \<cdot> \<sigma>\<^sub>2]" "[]"] and ordstep_ctxt [of _ _ "{\<succ>}" R]
          have "(u, fill_holes C [r\<^sub>2 \<cdot> \<sigma>\<^sub>2, r \<cdot> \<sigma>]) \<in> ?G\<^sup>*" using 1 by (auto simp: u ordstep_FGROUND)
          moreover from ctxt_imp_mctxt [OF _ lr\<^sub>2, of C "[]" "[r \<cdot> \<sigma>]"] and ordstep_ctxt [of _ _ "{\<succ>}" R]
          have "(t, fill_holes C [r\<^sub>2 \<cdot> \<sigma>\<^sub>2, r \<cdot> \<sigma>]) \<in> ?G\<^sup>*" using 1 by (auto simp: t ordstep_FGROUND)
          ultimately show ?thesis by (intro that)
        next
          case [simp]: (nested1 C)
          have eq: "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 = C\<langle>l \<cdot> \<sigma>\<rangle>" using s1 and s2 by simp
          define p where "p = hole_pos C"
          have C: "C = ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" by (simp add: p_def eq)
          show ?thesis
          proof (cases "p \<in> fun_poss l\<^sub>2")
            case False
            from non_ooverlap_FGROUND_joinable [OF R s1 s2 False [unfolded p_def] nested1(2) lr lr\<^sub>2 t u \<open>fground F t\<close> \<open>fground F u\<close> \<open>0 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> R\<close>]
            have "(t, u) \<in> ?G\<^sup>\<down>" .
            then show ?thesis by (elim joinE) (blast intro: that)
          next
            case True
            have "l\<^sub>1 \<cdot> \<tau> = l\<^sub>2 |_ p \<cdot> \<tau>"
              unfolding fun_poss_imp_poss [OF True, THEN subt_at_subst, symmetric] \<tau> eq
              by (simp add: l\<^sub>1_def \<sigma>\<^sub>1_def p_def)
            then obtain \<mu> where mgu: "mgu l\<^sub>1 (l\<^sub>2 |_ p) = Some \<mu>"
              using mgu_complete by (auto simp: unifiers_def)
            then have "is_mgu \<mu> {(l\<^sub>1, l\<^sub>2 |_ p)}" by (simp add: mgu_sound is_imgu_imp_is_mgu)
            with \<open>l\<^sub>1 \<cdot> \<tau> = l\<^sub>2 |_ p \<cdot> \<tau>\<close> obtain \<delta> where \<tau>': "\<tau> = \<mu> \<circ>\<^sub>s \<delta>" by (auto simp: is_mgu_def unifiers_def)
            then have \<tau>'': "t \<cdot> \<mu> \<cdot> \<delta> = t \<cdot> \<tau>" for t by auto
            have not_less: "(r\<^sub>1 \<cdot> \<mu>, l\<^sub>1 \<cdot> \<mu>) \<notin> {\<succ>}" "(r\<^sub>2 \<cdot> \<mu>, l\<^sub>2 \<cdot> \<mu>) \<notin> {\<succ>}"
              using \<open>l\<^sub>1 \<cdot> \<sigma>\<^sub>1 \<succ> r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<close> and \<open>l\<^sub>2 \<cdot> \<sigma>\<^sub>2 \<succ> r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<close> and irrefl
              by (auto dest!: subst [of "r\<^sub>1 \<cdot> \<mu>" "l\<^sub>1 \<cdot> \<mu>" \<delta>] subst [of "r\<^sub>2 \<cdot> \<mu>" "l\<^sub>2 \<cdot> \<mu>" \<delta>] simp: \<tau>'' \<tau> dest: trans)

            let ?u = "r\<^sub>2 \<cdot> \<mu>" and ?v = "(ctxt_of_pos_term p (l\<^sub>2 \<cdot> \<mu>))\<langle>r\<^sub>1 \<cdot> \<mu>\<rangle>"
            have gu:"fground F (?u \<cdot> \<delta>)" using 1(7) \<tau> \<tau>'' t' u by (auto simp:fground_def)
            have gv:"fground F (?v \<cdot> \<delta>)" using 1(4) fun_poss_imp_poss [OF True]
              by (auto simp: t' u \<tau>'' ctxt_of_pos_term_subst [symmetric] \<tau> C fground_def)
            note ooverlap = ooverlapI [OF rule\<^sub>1 rule\<^sub>2 disj True mgu not_less]
            from ooverlaps[OF this, unfolded fground_joinable_def, rule_format, of \<delta>] gu gv
            have "(?u \<cdot> \<delta>, ?v \<cdot> \<delta>) \<in> ?R\<^sup>\<down>" by (auto simp:fground_def)
            then have "(u, t) \<in> ?R\<^sup>\<down>"
              using fun_poss_imp_poss [OF True]
              by (auto simp: t' u \<tau>'' ctxt_of_pos_term_subst [symmetric] \<tau> C join_ctxt ordstep_rstep_conv' subst_closed_less)
            then obtain v where "(t, v) \<in> ?G\<^sup>*" and "(u, v) \<in> ?G\<^sup>*"
              using 1 by (auto dest!: ordsteps_FGROUND)
            then show ?thesis by (intro that)
          qed
        next
          case [simp]: (nested2 C)
          have eq: "l \<cdot> \<sigma> = C\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" using s1 and s2 by (simp)
          have eq\<^sub>1: "l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = C\<langle>l\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>" using s1 and s2 by (simp add: l\<^sub>1_def \<sigma>\<^sub>1_def)
          define p where "p = hole_pos C"
          have C: "C = ctxt_of_pos_term p (l \<cdot> \<sigma>)" by (simp add: p_def eq)
          have C': "C = ctxt_of_pos_term p (l\<^sub>1 \<cdot> \<sigma>\<^sub>1)" by (simp add: p_def eq l\<^sub>1_def \<sigma>\<^sub>1_def)
          show ?thesis
          proof (cases "p \<in> fun_poss l")
            case False
            from non_ooverlap_FGROUND_joinable [OF R s2 s1 False [unfolded p_def] nested2(2) lr\<^sub>2 lr u t \<open>fground F u\<close> \<open>fground F t\<close> \<open>0 \<bullet> (l, r) \<in> R\<close>]
            have "(u, t) \<in> ?G\<^sup>\<down>" .
            then show ?thesis by (elim joinE) (blast intro: that)
          next
            case True
            then have fun_poss: "p \<in> fun_poss l\<^sub>1" by (auto simp: l\<^sub>1_def)
            have "l\<^sub>2 \<cdot> \<tau> = l\<^sub>1 |_ p \<cdot> \<tau>"
              unfolding fun_poss_imp_poss [OF fun_poss, THEN subt_at_subst, symmetric] \<tau> eq\<^sub>1
              by (simp add: p_def)
            then obtain \<mu> where mgu: "mgu l\<^sub>2 (l\<^sub>1 |_ p) = Some \<mu>"
              using mgu_complete by (auto simp: unifiers_def)
            then have "is_mgu \<mu> {(l\<^sub>2, l\<^sub>1 |_ p)}" by (simp add: mgu_sound is_imgu_imp_is_mgu)
            with \<open>l\<^sub>2 \<cdot> \<tau> = l\<^sub>1 |_ p \<cdot> \<tau>\<close> obtain \<delta> where \<tau>': "\<tau> = \<mu> \<circ>\<^sub>s \<delta>" by (auto simp: is_mgu_def unifiers_def)
            then have \<tau>'': "t \<cdot> \<mu> \<cdot> \<delta> = t \<cdot> \<tau>" for t by auto
            have not_less: "(r\<^sub>1 \<cdot> \<mu>, l\<^sub>1 \<cdot> \<mu>) \<notin> {\<succ>}" "(r\<^sub>2 \<cdot> \<mu>, l\<^sub>2 \<cdot> \<mu>) \<notin> {\<succ>}"
              using \<open>l\<^sub>1 \<cdot> \<sigma>\<^sub>1 \<succ> r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<close> and \<open>l\<^sub>2 \<cdot> \<sigma>\<^sub>2 \<succ> r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<close> and irrefl
              by (auto dest!: subst [of "r\<^sub>1 \<cdot> \<mu>" "l\<^sub>1 \<cdot> \<mu>" \<delta>] subst [of "r\<^sub>2 \<cdot> \<mu>" "l\<^sub>2 \<cdot> \<mu>" \<delta>] simp: \<tau>'' \<tau> dest: trans)

            let ?u = "r\<^sub>1 \<cdot> \<mu>" and ?v = "(ctxt_of_pos_term p (l\<^sub>1 \<cdot> \<mu>))\<langle>r\<^sub>2 \<cdot> \<mu>\<rangle>"
            from ooverlapI [OF rule\<^sub>2 rule\<^sub>1 _ fun_poss mgu not_less(2,1), THEN ooverlaps] disj
            have gj:"fground_joinable F {\<succ>} R ?v ?u" by auto
            from 1 have "fground F (?u \<cdot> \<delta>)" "fground F (?v \<cdot> \<delta>)" using fun_poss_imp_poss [OF fun_poss]
              by (auto simp: t' u \<tau>'' ctxt_of_pos_term_subst [symmetric] \<tau> C' join_ctxt ordstep_rstep_conv' subst_closed_less fground_def)
            with gj[unfolded fground_joinable_def, rule_format, of \<delta>] have "(?u \<cdot> \<delta>, ?v \<cdot> \<delta>) \<in> ?R\<^sup>\<down>" by fast
            then have "(u, t) \<in> ?R\<^sup>\<down>"
              using fun_poss_imp_poss [OF fun_poss]
              by (auto simp: t' u \<tau>'' ctxt_of_pos_term_subst [symmetric] \<tau> C' join_ctxt ordstep_rstep_conv' subst_closed_less)
            then obtain v where "(t, v) \<in> ?G\<^sup>*" and "(u, v) \<in> ?G\<^sup>*"
              using 1 by (auto dest!: ordsteps_FGROUND)
            then show ?thesis by (intro that)
          qed
        qed
      qed
      ultimately have "(t', v) \<in> ?G\<^sup>\<down>" and "(v, u') \<in> ?G\<^sup>\<down>" by (auto simp: less.hyps)
      then obtain t'' and u'' where t't'': "(t', t'') \<in> ?G\<^sup>*" and "(v, t'') \<in> ?G\<^sup>*"
        and "(v, u'') \<in> ?G\<^sup>*" and u'u'': "(u', u'') \<in> ?G\<^sup>*" by blast
      moreover have "s \<succ> v"
        using 1 and tv
        by (auto simp: FGROUND_def dest!: ordstep_imp_ord [OF ctxt_closed_less] ordsteps_imp_ordeq [OF ctxt_closed_less trans_less] rtrancl_Restr)
          (auto dest: trans)
      ultimately have "(t'', u'') \<in> ?G\<^sup>\<down>" by (auto simp: less.hyps)
      then show ?thesis using t't'' and u'u'' by (blast dest: join_rtrancl_join rtrancl_join_join)
    qed auto
  qed
qed

lemma ordstep_sym:
  assumes R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> R"
  shows "ordstep {\<succ>} (R\<^sup>\<leftrightarrow>) = ordstep {\<succ>} R"
proof(rule, rule)
  fix s t
  assume "(s, t) \<in> ordstep {\<succ>} (R\<^sup>\<leftrightarrow>)"
  from ordstep.cases[OF this]
    obtain l r C \<sigma> where ordstep:"s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "l \<cdot> \<sigma> \<succ> r \<cdot> \<sigma>" "(l, r) \<in> R\<^sup>\<leftrightarrow>"
    unfolding mem_Collect_eq split by metis
  from trans[OF subst[of r l \<sigma>] ordstep(3)] irrefl R ordstep(4) have "(l, r) \<in> R" by auto
  from ordstep ordstep.intros[OF this] show "(s, t) \<in> ordstep {\<succ>} R" by auto
qed (auto simp:ordstep_mono)

lemma rstep_ground_joinable:
  assumes "(s,t) \<in> rstep (R\<^sup>\<leftrightarrow>)"
  and R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> R"
  shows "fground_joinable F {\<succ>} R s t"
  unfolding fground_joinable_def
proof(rule, rule)
  fix \<sigma> :: "('a, 'b) subst"
  assume ground:"fground F (s \<cdot> \<sigma>) \<and> fground F (t \<cdot> \<sigma>)"
  from assms have "(s,t) \<in> rstep (R\<^sup>\<leftrightarrow>)" unfolding GROUND_def by auto
  then obtain l r C \<tau> where lr:"(l, r) \<in> R\<^sup>\<leftrightarrow>" "s = C\<langle>l \<cdot> \<tau>\<rangle>" "t = C\<langle>r \<cdot> \<tau>\<rangle>" by blast
  let ?l = "l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)" and ?r = "r \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)"
  from ground fgtotal[of ?l ?r] consider "?r \<succ> ?l" | "?l \<succ> ?r" | "?l = ?r"
    unfolding lr by (auto simp:fground_def)
  then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>\<down>"
  proof cases
    case 1
    from lr have "(r, l) \<in> R\<^sup>\<leftrightarrow>" by fast
    from 1 ordstep.intros[OF this, of _ "C \<cdot>\<^sub>c \<sigma>" "\<tau> \<circ>\<^sub>s \<sigma>" _] have "(t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<in> (ordstep {\<succ>} (R\<^sup>\<leftrightarrow>))"
      unfolding subst_subst lr by auto
    with ordstep_sym[OF R] show ?thesis unfolding fground_joinable_def by auto
  next
    case 2
    with ordstep.intros[OF lr(1), of _ "C \<cdot>\<^sub>c \<sigma>" "\<tau> \<circ>\<^sub>s \<sigma>" _] have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep {\<succ>} (R\<^sup>\<leftrightarrow>))"
      unfolding subst_subst lr by auto
    with ordstep_sym[OF R] show ?thesis by auto
  qed (auto simp:lr)
qed

lemma GCR_ordstep:
  assumes "\<And>r r' p \<mu> u v. ooverlap {\<succ>} R r r' p \<mu> u v \<Longrightarrow>
    (u, v) \<in> (ordstep {\<succ>} R)\<^sup>\<down> \<or> (\<exists>l r \<sigma>. (l, r) \<in> R\<^sup>\<leftrightarrow> \<and> u = l \<cdot> \<sigma> \<and> v = r \<cdot> \<sigma>)"
    and R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> R"
  shows "CR (FGROUND F (ordstep {\<succ>} R))" (is "CR (FGROUND F ?R)" is "CR ?G")
proof-
  { fix r r' p \<mu> u v
    assume ooverlap:"ooverlap {\<succ>} R r r' p \<mu> u v"
    have "fground_joinable F {\<succ>} R u v" unfolding fground_joinable_def proof(rule, rule)
      fix \<sigma> :: "('a, 'b) subst"
      let ?u = "u \<cdot> \<sigma>" and ?v = "v \<cdot> \<sigma>"
      assume ground:"fground F ?u \<and> fground F ?v"
      from assms(1)[OF ooverlap] consider
        "(u, v) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" | "(\<exists>l r \<sigma>. (l, r) \<in> R\<^sup>\<leftrightarrow> \<and> u = l \<cdot> \<sigma> \<and> v = r \<cdot> \<sigma>)" by blast
      thus "(?u, ?v) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" proof(cases)
        case 1
        show ?thesis using join_subst[OF subst_closed_ordstep, OF _ 1] subst by fastforce
      next
        case 2
        with rstep_ground_joinable[of u v R, OF _ R] ground show ?thesis
          unfolding fground_joinable_def by blast
      qed
    qed
  }
  with ground_joinable_ooverlaps_implies_GCR R show ?thesis by auto
qed
end

text \<open>Minimal ordered rewrite steps.\<close>
inductive_set mordstep for c and ord :: "('f, 'v) term rel" and R :: "('f, 'v) trs"
  where
    "(l, r) \<in> R \<Longrightarrow> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ord \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow>
      \<forall>x \<in> vars_term r - vars_term l. \<sigma> x = Fun c [] \<Longrightarrow>
      (s, t) \<in> mordstep c ord R"

lemma mordstep_mono:
  "ord \<subseteq> ord' \<Longrightarrow> mordstep c ord R \<subseteq> mordstep c ord' R"
  by (auto elim!: mordstep.cases intro: mordstep.intros)

lemma mordstep_ordstep:
  "mordstep c ord R \<subseteq> ordstep ord R"
  by (auto elim!: mordstep.cases intro: ordstep.intros)

definition "ext_subst \<sigma> t c x = (if x \<in> vars_term t then \<sigma> x else Fun c [])"

lemma subst_ext_subst:
  "vars_term s \<subseteq> vars_term t \<Longrightarrow> s \<cdot> ext_subst \<sigma> t c = s \<cdot> \<sigma>"
  by (intro term_subst_eq) (auto simp: ext_subst_def)

lemma subst_ext_subst': "t \<cdot> ext_subst \<sigma> t c = t \<cdot> \<sigma>"
  by (auto simp: subst_ext_subst)

lemma ext_subst_restrict [simp]:
  "ext_subst (\<sigma> |s vars_term t) t c = ext_subst \<sigma> t c"
  by (auto simp: ext_subst_def)

lemma ext_subst:
  "\<forall>x \<in> vars_term r - vars_term l. ext_subst \<sigma> l c x = Fun c []"
  by (auto simp: ext_subst_def)

lemma (in reduction_order) ext_subst_less:
  assumes min_const: "\<forall>t. ground t \<longrightarrow> t \<succeq> Fun c []"
    and "ground (t \<cdot> \<sigma>)"
  shows "t \<cdot> \<sigma> \<succeq> t \<cdot> ext_subst \<sigma> s c"
  using assms(2)
proof (induct t)
  case (Var x)
  then show ?case using min_const by (auto simp: ext_subst_def)
next
  case (Fun f ts)
  let ?\<Sigma> = "\<lambda>i. drop i (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
  let ?C = "\<lambda>i. take i (map (\<lambda>t. t \<cdot> ext_subst \<sigma> s c) ts)"
  have *: "\<forall>t \<in> set ts. t \<cdot> \<sigma> \<succeq> t \<cdot> ext_subst \<sigma> s c" using Fun by auto
  have "Fun f ts \<cdot> \<sigma> \<succeq> Fun f (?C i @ ?\<Sigma> i)" if "i \<le> length ts" for i
    using that
  proof (induct i)
    case (Suc i)
    then have "ts ! i \<cdot> \<sigma> \<succeq> ts ! i \<cdot> ext_subst \<sigma> s c" using * by force
    with ctxt [of "ts ! i \<cdot> \<sigma>" "ts ! i \<cdot> ext_subst \<sigma> s c" "More f (?C i) \<box> (?\<Sigma> (Suc i))"]
    have "Fun f (?C i @ ?\<Sigma> i) \<succeq> Fun f (?C (Suc i) @ ?\<Sigma> (Suc i))"
      using Suc.prems and Cons_nth_drop_Suc [of i "map (\<lambda>t. t \<cdot> \<sigma>) ts"]
      by (cases "i < length ts") (auto simp add: take_Suc_conv_app_nth)
    moreover have "Fun f ts \<cdot> \<sigma> \<succeq> Fun f (?C i @ ?\<Sigma> i)" using Suc by simp
    ultimately show ?case by (auto dest: trans)
  qed simp
  from this [of "length ts"] show ?case by simp
qed

lemma (in reduction_order) mordstep_complete:
  assumes min_const: "\<forall>t. ground t \<longrightarrow> t \<succeq> Fun c []"
    and ground: "ground s"
    and step: "(s, t) \<in> ordstep {\<succ>} R"
  shows "\<exists>u. (s, u) \<in> mordstep c {\<succ>} R"
  using ordstep_GROUND [OF ground step] and step
  apply (auto elim!: ordstep.cases)
  apply (rule_tac x = "C\<langle>r \<cdot> ext_subst \<sigma> l c\<rangle>" in exI)
  apply (rule_tac l = l and r = r and \<sigma> = "ext_subst \<sigma> l c" and C = C in mordstep.intros)
  apply (auto simp: subst_ext_subst)
  apply (subgoal_tac "r \<cdot> \<sigma> \<succeq> r \<cdot> ext_subst \<sigma> l c")
  apply (auto dest: trans)
  using ext_subst_less [OF min_const]
  apply (auto simp: GROUND_def ext_subst_def)
  done

lemma FGROUND_subset: "FGROUND F R \<subseteq> R" by (auto simp: FGROUND_def)

lemma mordstep_FGROUND:
  assumes "(c, 0) \<in> F" "funas_trs R \<subseteq> F" "fground F s"
    and "(s, t) \<in> mordstep c ord R"
  shows "(s, t) \<in> (FGROUND F (mordstep c ord R))"
  using assms
  apply (auto elim!: mordstep.cases simp: FGROUND_def fground_def)
  apply blast
  apply (auto simp: funas_term_subst)
  apply (meson contra_subsetD rhs_wf)
  apply (case_tac "x \<in> vars_term r - vars_term l")
  apply auto
  done

lemma FGROUND_GROUND:
  "(s, t) \<in> FGROUND F R \<Longrightarrow> (s, t) \<in> GROUND R"
  by (auto simp: FGROUND_def GROUND_def fground_def)

lemma GROUND_mono:
  "R \<subseteq> S \<Longrightarrow> GROUND R \<subseteq> GROUND S"
  by (auto simp: GROUND_def)

lemma FGROUND_mono:
  "R \<subseteq> S \<Longrightarrow> FGROUND F R \<subseteq> FGROUND F S"
  by (auto simp: FGROUND_def)

lemma rtrancl_FGROUND_GROUND:
  assumes "(s, t) \<in> (FGROUND F R)\<^sup>*"
  shows "(s, t) \<in> (GROUND R)\<^sup>*"
  using assms by (induct) (auto dest: FGROUND_GROUND)

lemma rtrancl_FGROUND_fground:
  assumes "(s, t) \<in> (FGROUND F R)\<^sup>*" and "fground F s"
  shows "fground F t \<and> (s, t) \<in> R\<^sup>*"
  using assms by (induct) (auto simp: FGROUND_def)

lemma mordsteps_FGROUND:
  assumes "(c, 0) \<in> F" "funas_trs R \<subseteq> F" "fground F s"
    and "(s, t) \<in> (mordstep c ord R)\<^sup>*"
  shows "(s, t) \<in> (FGROUND F (mordstep c ord R))\<^sup>*"
  using assms(4, 1-3) by (induct) (auto dest: rtrancl_FGROUND_fground mordstep_FGROUND)

lemma (in reduction_order) suborder_mordstep_NF:
  assumes *: "{(x, y). ord x y} \<subseteq> {\<succ>}" (is "?O \<subseteq> {\<succ>}") and "reduction_order ord"
    and fground: "\<forall>s t. fground F s \<and> fground F t \<longrightarrow> s = t \<or> ord s t \<or> ord t s"
    and min: "\<forall>t. ground t \<longrightarrow> t \<succeq> Fun c []"
    and F: "(c, 0) \<in> F" "funas_trs R \<subseteq> F" "fground F t"
    and NF: "t \<in> NF (FGROUND F (mordstep c {(x, y). ord x y} R))"
  shows "t \<in> NF (GROUND (ordstep {\<succ>} R))"
proof (rule ccontr)
  interpret ord: reduction_order ord by fact
  assume "\<not> ?thesis"
  then obtain u' where "(t, u') \<in> GROUND (ordstep {\<succ>} R)" by blast
  then have "ground t" and "(t, u') \<in> ordstep {\<succ>} R" by (auto simp: GROUND_def)
  from mordstep_complete [OF min this] obtain u where "(t, u) \<in> mordstep c {\<succ>} R" by blast
  from mordstep_FGROUND [OF F this] have "(t, u) \<in> FGROUND F (mordstep c {\<succ>} R)" .
  with * and fground have "(t, u) \<in> FGROUND F (mordstep c ?O R)"
    apply (auto simp: FGROUND_def fground_def simp del: ground_subst elim!: mordstep.cases)
    apply (subgoal_tac "ord (l \<cdot> \<sigma>) (r \<cdot> \<sigma>)")
    apply (auto simp del: ground_subst intro: mordstep.intros)
    by (metis (mono_tags, opaque_lifting) Collect_mono_iff irrefl local.trans old.prod.case)
  then show False using NF by blast
qed

lemma (in reduction_order) SN_ordstep:
  "SN (ordstep {\<succ>} R)"
  by (rule SN_subset [OF SN_less]) (auto dest: ordstep_imp_ord [OF ctxt_closed_less])

lemma (in reduction_order) SN_mordstep:
  "SN (mordstep c {\<succ>} R)"
  by (rule SN_subset [OF SN_less])
    (auto dest: mordstep_ordstep [THEN subsetD] ordstep_imp_ord [OF ctxt_closed_less])

lemma (in reduction_order) SN_FGROUND_ordstep:
  "SN (FGROUND F (ordstep {\<succ>} R))"
  by (rule SN_subset [OF SN_ordstep, of _ R]) (rule FGROUND_subset)

lemma (in reduction_order) SN_FGROUND_mordstep:
  "SN (FGROUND F (mordstep c {\<succ>} R))"
  by (rule SN_subset [OF SN_mordstep, of _ _ R]) (rule FGROUND_subset)

lemma (in reduction_order) GCR_imp_CR_FGROUND:
  assumes *: "{(x, y). ord x y} \<subseteq> {\<succ>}" (is "?O \<subseteq> _")
    and ro: "reduction_order ord"
    and fground: "\<forall>s t. fground F s \<and> fground F t \<longrightarrow> s = t \<or> ord s t \<or> ord t s"
    and min: "\<forall>t. ground t \<longrightarrow> t \<succeq> Fun c []"
    and F: "(c, 0) \<in> F" "funas_trs R \<subseteq> F"
    and GCR: "GCR (ordstep {\<succ>} R)" (is "CR (GROUND ?R)" is "CR ?G")
  shows "CR (FGROUND F (ordstep ?O R))" (is "CR (FGROUND F ?S)" is "CR ?F")
proof
  let ?M = "mordstep c ?O R"
  have [dest!]: "\<And>s t. (s, t) \<in> (GROUND (ordstep ?O R))\<^sup>* \<Longrightarrow> (s, t) \<in> ?G\<^sup>*"
    by (rule rtrancl_mono [of "GROUND (ordstep ?O R)", THEN subsetD], rule GROUND_mono)
      (auto dest!: mordstep_ordstep [THEN subsetD] ordstep_mono [OF subset_refl *, THEN subsetD])
  have [dest!]: "\<And>s t. (s, t) \<in> (FGROUND F ?M)\<^sup>* \<Longrightarrow> (s, t) \<in> ?F\<^sup>*"
    by (rule rtrancl_mono [of "FGROUND F ?M", THEN subsetD], rule FGROUND_mono)
      (auto dest: mordstep_ordstep [THEN subsetD])
  have [dest!]: "\<And>s t. (s, t) \<in> (GROUND ?M)\<^sup>* \<Longrightarrow> (s, t) \<in> ?G\<^sup>*"
    by (rule rtrancl_mono [of "GROUND ?M", THEN subsetD], rule GROUND_mono)
      (auto dest!: mordstep_ordstep [THEN subsetD] ordstep_mono [OF subset_refl *, THEN subsetD])
  fix s t u assume st: "(s, t) \<in> ?F\<^sup>*" and su: "(s, u) \<in> ?F\<^sup>*"
  then consider "s = t" | "fground F s"
    by (metis FGROUND_def Int_iff converse_rtranclE mem_Collect_eq mem_Sigma_iff)
  then show "(t, u) \<in> ?F\<^sup>\<down>"
  proof (cases)
    case 1 then show ?thesis using st and su by auto
  next
    case 2
    interpret ord: reduction_order ord by fact
    obtain t' and u' where tt': "(t, t') \<in> (FGROUND F ?M)\<^sup>!"
      and uu': "(u, u') \<in> (FGROUND F ?M)\<^sup>!"
      using SN_imp_WN [OF ord.SN_FGROUND_mordstep, of F c R]
      by (force simp: WN_on_def)
    then have "fground F t'" and "fground F u'"
      using st and su
      using 2 by (auto simp: normalizability_def dest: rtrancl_FGROUND_fground)
    then have "(s, t') \<in> ?G\<^sup>*" and "t' \<in> NF ?G" and "(s, u') \<in> ?G\<^sup>*" and "u' \<in> NF ?G"
      using tt' and uu' and st and su
      by (auto simp: normalizability_def dest!: rtrancl_FGROUND_GROUND
          intro!: suborder_mordstep_NF [OF * ro fground min F])
    with GCR have "t' = u'"
      by (meson CR_divergence_imp_join join_NF_imp_eq)
    then show ?thesis using tt' and uu' by (auto simp: normalizability_def)
  qed
qed

lemma GCR_imp_conversion_imp_join:
  assumes "GCR (rstep \<R>)" and "ground s" and "ground t" and "(s, t) \<in> (rstep \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>\<down>"
proof -
  from assms and gterm_conv_GROUND_conv have "(s, t) \<in> (GROUND (rstep \<R>))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  with assms(1) have "(s, t) \<in> (GROUND (rstep \<R>))\<^sup>\<down>" unfolding CR_iff_conversion_imp_join by force
  with GROUND_subset [THEN join_mono] show ?thesis by auto
qed

locale order_closure =
  fixes \<C> :: "('a, 'b::infinite) term rel \<Rightarrow> ('a, 'b) term rel"
  and repr :: "'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes C_cond:"\<And>ord. (s, t) \<in> \<C> ord \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> \<C> {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u,v) \<in> ord}"
  and C_mono:"\<And>ord ord'. ord \<subseteq> ord' \<Longrightarrow> \<C> ord \<subseteq> \<C> ord'"
  and repr:"\<And>\<rho> X x y. finite X \<Longrightarrow> equiv X \<rho> \<Longrightarrow> x \<in> X \<Longrightarrow> (x, repr X \<rho> x) \<in> \<rho> \<and> repr X \<rho> x \<in> X \<and> ((x,y) \<in> \<rho> \<longrightarrow> repr X \<rho> x = repr X \<rho> y)"
begin

lemma ordstep_subst_ord:
  "(s,t) \<in> ordstep (\<C> ord) R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ordstep (\<C> {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u,v) \<in> ord}) R"
proof-
  assume "(s,t) \<in> ordstep (\<C> ord) R"
  then obtain C \<tau> l r where ordstep:"(l,r) \<in> R" "s = C\<langle>l \<cdot> \<tau>\<rangle>" "t = C\<langle>r \<cdot> \<tau>\<rangle>" "(l \<cdot> \<tau>, r \<cdot> \<tau>) \<in> \<C> ord"
    unfolding ordstep.simps by auto
  let ?ord = "{(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u, v) \<in> ord}"
  from ordstep(4) C_cond have "(l \<cdot> \<tau> \<cdot> \<sigma>, r \<cdot> \<tau> \<cdot> \<sigma>) \<in> \<C> ?ord" by auto
  with ordstep.intros[OF ordstep(1), of "s \<cdot> \<sigma>" "C \<cdot>\<^sub>c \<sigma>" "\<tau> \<circ>\<^sub>s \<sigma>" "t \<cdot> \<sigma>" "\<C> ?ord"]
    show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ordstep (\<C> ?ord) R"
    unfolding ordstep(2) ordstep(3) subst_apply_term_ctxt_apply_distrib
    using subst_subst_compose by auto
qed

lemma fgterm_rtrancl_FGROUND_rtrancl:
  fixes s t :: "('f, 'v) term"
  assumes "funas_trs R \<subseteq> F"
    and fground: "fground F s" 
    and mordstep: "(s, t) \<in> mordstep c ord R" (is "_ \<in> ?R")
    and c:"(c, 0) \<in> F"
  shows "fground F t"
proof-
  from mordstep[unfolded mordstep.simps]
  obtain l r C \<sigma> where step:"(l,r) \<in> R" "s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ord"
    "\<forall>x\<in>vars_term r - vars_term l. \<sigma> x = Fun c []" by auto
  from assms(1) step(1) have rF:"funas_term r \<subseteq> F" unfolding funas_trs_def funas_rule_def by force
  from fground[unfolded step] have fC:"funas_ctxt C \<subseteq> F" "funas_term (l \<cdot> \<sigma>) \<subseteq> F"
    "ground (l\<cdot>\<sigma>)" "ground_ctxt C" unfolding fground_def funas_term_ctxt_apply by auto
  from fC(2) fC(3) have "\<And>x. x \<in> vars_term l \<Longrightarrow> fground F (\<sigma> x)"
    unfolding fground_def funas_term_subst by auto
  with step(5) c have "\<And>x. x \<in> vars_term r \<Longrightarrow> fground F (\<sigma> x)"
    unfolding fground_def funas_term_subst by force
  with rF have "fground F (r \<cdot> \<sigma>)" unfolding fground_def funas_term_subst by auto
  with fC show ?thesis unfolding step(3) fground_def funas_term_ctxt_apply ground_ctxt_apply by auto
qed

lemma ordsteps_subst_ord:
  assumes "(s,t) \<in> (ordstep (\<C> ord) R)\<^sup>*"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep (\<C> {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u,v) \<in> ord}) R)\<^sup>*"
  using assms by (induct) (auto simp: ordstep_subst_ord rtrancl_into_rtrancl)

lemma ordstep_join_subst_ord:
  assumes "(s,t) \<in> (ordstep (\<C> ord) R)\<^sup>\<down>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep (\<C> {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u,v) \<in> ord}) R)\<^sup>\<down>"
proof-
  from assms obtain u where "(s,u) \<in> (ordstep (\<C> ord) R)\<^sup>*" "(t,u) \<in> (ordstep (\<C> ord) R)\<^sup>*" by auto
  with ordsteps_subst_ord show ?thesis by blast
qed

definition "hat V \<rho> = (\<lambda>x. Var (repr V \<rho> x))"

abbreviation "\<T> var_ord \<equiv> {(Var x, Var y) |x y. (x,y) \<in> var_ord}"

definition "equiv_total V \<rho> ord \<equiv>
  (\<forall>x \<in> V. \<forall>y \<in> V. (x,y) \<in> \<rho> \<or> (x,y) \<in> ord \<or> (y,x) \<in> ord) \<and> wf (ord\<inverse>) \<and> trans ord"

abbreviation "instance_join ord R \<equiv> (ordstep ord R)\<^sup>* O (rstep R)\<^sup>= O ((ordstep ord R)\<inverse>)\<^sup>*"

definition var_order_joinable :: "('a, 'b) term rel \<Rightarrow> ('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool"
  where
    "var_order_joinable R s t =
      (let V = vars_term s \<union> vars_term t in
      (\<forall>\<rho> vord. equiv V \<rho> \<longrightarrow> equiv_total V \<rho> vord \<longrightarrow>
        (s \<cdot> hat V \<rho>, t \<cdot> hat V \<rho>) \<in> instance_join (\<C> (\<T> vord)) R))"

lemma subst_implies_equiv:"\<exists> \<rho>. equiv V \<rho> \<and> (\<forall>x \<in> V. \<forall>y \<in> V. (x,y) \<in> \<rho> \<longleftrightarrow> (\<sigma> x = \<sigma> y))"
proof-
  define \<rho> where "\<rho> = {(x,y) |x y. x \<in> V \<and> y \<in> V \<and> \<sigma> x = \<sigma> y}"
  have "refl_on V \<rho>" unfolding \<rho>_def refl_on_def mem_Collect_eq by blast
  hence "equiv V \<rho>" unfolding equiv_def sym_def trans_def \<rho>_def by auto
  thus ?thesis unfolding \<rho>_def by auto
qed

end

locale gtotal_reduction_order_inf_closure =
  fgtotal_reduction_order_inf less F + order_closure \<C> repr
  for less :: "('a, 'b::infinite) Term.term \<Rightarrow> ('a, 'b) Term.term \<Rightarrow> bool" (infix "\<succ>" 50)
  and F :: "('a \<times> nat) set"
  and \<C> :: "('a, 'b) term rel \<Rightarrow> ('a, 'b) term rel"
  and repr :: "'b set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> 'b \<Rightarrow> 'b"
begin

abbreviation "\<C>_compatible ord \<equiv> \<C>(ord) \<subseteq> ord"

lemma var_order_joinable_ground_joinable:
  assumes R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> s \<succ> t \<or> (t, s) \<in> R"
  and C_compat:"\<C>_compatible {(s,t) | s t. s \<succ> t}"
  and vo_joinable:"var_order_joinable R s t"
  shows "fground_joinable F {\<succ>} R s t"
proof-
  let ?V = "vars_term s \<union> vars_term t"
  { fix \<sigma> :: "('a,'b) subst"
    assume ground: "fground F (s \<cdot> \<sigma>)" "fground F (t \<cdot> \<sigma>)"
    { fix x
      assume x:"x \<in> ?V"
      with ground have g:"ground (\<sigma> x)" unfolding fground_def using ground_subst by auto
      from vars_term_poss_subt_at obtain C where "s = C\<langle>Var x\<rangle> \<or> t = C\<langle>Var x\<rangle>"
        by (meson Un_iff supteq_ctxt_conv vars_term_supteq x)
      with ground x have "funas_term (\<sigma> x) \<subseteq> F" using funas_term_subst unfolding fground_def by blast
      with g have "fground F (\<sigma> x)" unfolding fground_def by auto
    }
    hence vars_img_ground:"\<forall>x \<in> ?V. fground F (\<sigma> x)" by auto
    from subst_implies_equiv obtain \<rho> where
      \<rho>:"equiv ?V \<rho>" "\<forall>x \<in> ?V. \<forall>y \<in> ?V. (x,y) \<in> \<rho> \<longleftrightarrow> (\<sigma> x = \<sigma> y)" by metis
    have fin:"finite ?V" by simp
    define ord' where "ord' \<equiv> {(x, y) | x y. \<sigma> x \<succ> \<sigma> y }"
    { fix f
      assume "\<forall>i. (f i, f (Suc i)) \<in> ord'"
      hence "\<forall>i. \<sigma> (f i) \<succ> \<sigma> (f (Suc i))" unfolding ord'_def mem_Collect_eq by auto
      with SN_less have False by fast
    } hence wf:"wf (ord'\<inverse>)" unfolding SN_iff_wf[symmetric] SN_on_def by auto
    from trans have trans:"trans ord'" unfolding trans_def ord'_def mem_Collect_eq by blast
    { fix x y
      assume inV:"x \<in> ?V" "y \<in> ?V"
      with vars_img_ground[rule_format] fgtotal have "\<sigma> x = \<sigma> y \<or> \<sigma> x \<succ> \<sigma> y \<or> \<sigma> y \<succ> \<sigma> x" by simp
      with \<rho>(2) inV have "(x,y) \<in> \<rho> \<or> (x,y) \<in> ord' \<or> (y,x) \<in> ord'" unfolding ord'_def by auto
    }
    with wf trans have equiv_total:"equiv_total ?V \<rho> ord'" unfolding equiv_total_def by auto
    define ss where "ss \<equiv> s \<cdot> hat ?V \<rho>"
    define tt where "tt \<equiv> t \<cdot> hat ?V \<rho>"
    note repr = repr[OF fin \<rho>(1)]
    { fix x
      assume "x \<in> vars_term ss \<union> vars_term tt"
      hence "\<exists>u. (u :: ('a,'b) term) \<in> (hat ?V \<rho>) ` ?V \<and> x \<in> vars_term u"
        unfolding vars_term_subst UN_iff ss_def tt_def by auto
      then obtain u :: "('a,'b) term" where u:"u \<in> (hat ?V \<rho>) ` ?V" "x \<in> vars_term u" by auto
      then obtain y where y:"y \<in> ?V" and "u = hat ?V \<rho> y" by auto
      with repr[of y] have "u = Var (repr ?V \<rho> y)" unfolding hat_def by auto
      with u have x:"x = repr ?V \<rho> y" by auto
      with repr[of y] y have "x \<in> ?V" unfolding x by auto
    }
    note vars_subset = this
    with ground vars_img_ground have g:"ground (ss \<cdot> \<sigma>)" "ground (tt \<cdot> \<sigma>)"
      unfolding fground_def by auto
    from vars_subset vars_img_ground have vs:"\<forall>x\<in>vars_term ss \<union> vars_term tt. fground F (\<sigma> x)" by auto
    from ground have "funas_term ss \<subseteq> F" "funas_term tt \<subseteq> F"
      unfolding ss_def tt_def fground_def funas_term_subst hat_def by auto
    with ground(1) vs have funas:"funas_term (ss \<cdot> \<sigma>) \<subseteq> F" "funas_term (tt \<cdot> \<sigma>) \<subseteq> F"
      unfolding fground_def funas_term_subst by auto
    with g have fground:"fground F (ss \<cdot> \<sigma>)" "fground F (tt \<cdot> \<sigma>)" unfolding fground_def by auto
    note vo_joinable = vo_joinable[unfolded var_order_joinable_def Let_def, rule_format]
    from this[OF \<rho>(1) equiv_total] have ordjoin:"(ss, tt) \<in> instance_join (\<C> (\<T> ord')) R"
      unfolding ss_def tt_def by auto
    then obtain u v where ordjoin:
      "(ss, u) \<in> (ordstep (\<C> (\<T> ord')) R)\<^sup>*" "(tt, v) \<in> (ordstep (\<C> (\<T> ord')) R)\<^sup>*" and rstep:"(u,v) \<in> (rstep R)\<^sup>="
      using relcomp_def rtrancl_converseD[of _ _ "ordstep (\<C> (\<T> ord')) R"] by auto
    define ord_set where "ord_set \<equiv> {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u, v) \<in> {(Var x, Var y) |x y. (x, y) \<in> ord'}}"
    have "ord_set \<subseteq> {\<succ>}" unfolding ord_set_def ord'_def unfolding mem_Collect_eq by force
    from C_compat C_mono[OF this] have ord_subset:"\<C> ord_set \<subseteq> {\<succ>}" by auto
    note mono = ordstep_mono[OF subset_refl this, THEN rtrancl_mono, of R]
    with ordsteps_subst_ord[OF ordjoin(1)] ordsteps_subst_ord[OF ordjoin(2)]
      have j:"(ss \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>*" "(tt \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>*"
        unfolding ord_set_def by blast+
    with ordsteps_FGROUND fground have g:"fground F (u \<cdot> \<sigma>) \<and> fground F (v \<cdot> \<sigma>)" by blast+
    hence eq:"u \<cdot> \<sigma> = v \<cdot> \<sigma> \<Longrightarrow> fground_joinable F {\<succ>} R (u \<cdot> \<sigma>) (v \<cdot> \<sigma>)" unfolding fground_joinable_def by auto
    from rstep have "(u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (rstep R)\<^sup>=" by auto
    with eq rstep_ground_joinable[OF _ R] have "fground_joinable F {\<succ>} R (u \<cdot> \<sigma>) (v \<cdot> \<sigma>)"
      unfolding rstep_simps by auto
    note gjoin = this[unfolded fground_joinable_def, rule_format, of Var, unfolded subst_apply_term_empty]
    note * = rtrancl_join_join[OF j(1) join_rtrancl_join, OF _ j(2)]
    with gjoin[OF g] have join:"(ss \<cdot> \<sigma>, tt \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" by argo
    { fix x
      assume x_in_V:"x \<in> ?V"
      with \<rho>(1) have "(x, x) \<in> \<rho>" unfolding equiv_def refl_on_def by auto
      hence in_rho:"(x, repr ?V \<rho> x) \<in> \<rho>" using repr x_in_V someI_ex[of "\<lambda>y. (x,y) \<in> \<rho>"] by blast
      with \<rho>(1) have "repr ?V \<rho> x \<in> ?V" unfolding equiv_def repr_def by (meson refl_on_domain)
      from in_rho[unfolded \<rho>(2)[rule_format, OF x_in_V this]] have "(hat ?V \<rho> \<circ>\<^sub>s \<sigma>) x = \<sigma> x"
        unfolding hat_def subst_compose_def by simp
    }
    hence "s \<cdot> (hat ?V \<rho> \<circ>\<^sub>s  \<sigma>) = s \<cdot> \<sigma>" "t \<cdot> (hat ?V \<rho> \<circ>\<^sub>s  \<sigma>) = t \<cdot> \<sigma>"
      by (rule term_subst_eq, simp, rule term_subst_eq, auto)
    with join have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" unfolding subst_subst ss_def tt_def by auto
  }
  thus "fground_joinable F {\<succ>} R s t" unfolding fground_joinable_def by auto
qed

text \<open>Inductive criterion for ground joinability.\<close>
inductive_set ground_join_rel for R :: "('a, 'b) trs"
  where
    refl: "(t, t) \<in> ground_join_rel R"
  | var_order: "var_order_joinable R s t \<Longrightarrow> (s, t) \<in> ground_join_rel R"
  | step: "(l, r) \<in> R\<^sup>\<leftrightarrow> \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> (s, t) \<in> ground_join_rel R"
  | rewrite_left: "(s, t) \<in> ground_join_rel R \<Longrightarrow> (u, s) \<in> ordstep {\<succ>} R \<Longrightarrow> (u, t) \<in> ground_join_rel R"
  | rewrite_right: "(s, t) \<in> ground_join_rel R \<Longrightarrow> (u, t) \<in> ordstep {\<succ>} R \<Longrightarrow> (s, u) \<in> ground_join_rel R"
  | congg: "s = Fun f ss \<Longrightarrow> t = Fun f ts \<Longrightarrow> length ss = length ts \<Longrightarrow>
         (\<forall>i < length ss. (ss ! i, ts ! i) \<in> ground_join_rel R) \<Longrightarrow> (s, t) \<in> ground_join_rel R"

(* TODO: move *)
lemma all_ctxt_closed_join:
  assumes "all_ctxt_closed UNIV (A\<^sup>*)"
  shows "all_ctxt_closed UNIV (A\<^sup>\<down>)"
proof-
  { fix f ss ts
    assume len:"length ts = length ss" and join:"\<forall>i<length ts. (ts ! i, ss ! i) \<in> A\<^sup>\<down>"
    define us where "us \<equiv> map (\<lambda>i. SOME u\<^sub>i. (ts ! i, u\<^sub>i) \<in> A\<^sup>* \<and> (ss ! i, u\<^sub>i) \<in> A\<^sup>*) [0..<length ts]"
    then have len_us:"length us = length ts" by auto
    { fix i
      assume i:"i < length ts"
      from i nth_map_upt have ui:"us ! i = (SOME u\<^sub>i. (ts ! i, u\<^sub>i) \<in> A\<^sup>* \<and> (ss ! i, u\<^sub>i) \<in> A\<^sup>*)"
        unfolding us_def by fastforce
      from join[rule_format, OF i] have "\<exists>u\<^sub>i. (ts ! i, u\<^sub>i) \<in> A\<^sup>* \<and> (ss ! i, u\<^sub>i) \<in> A\<^sup>*" by auto
      from someI_ex[OF this] ui have "(ts ! i, us ! i) \<in> A\<^sup>* \<and> (ss ! i, us ! i) \<in> A\<^sup>*" by argo
    }
    with len have "\<forall>i<length ts. (ts ! i, us ! i) \<in> A\<^sup>*" "\<forall>i<length ss. (ss ! i, us ! i) \<in> A\<^sup>*" by auto
    with assms[unfolded all_ctxt_closed_def, simplified] len len_us
      have "(Fun f ts, Fun f us) \<in> A\<^sup>*" "(Fun f ss, Fun f us) \<in> A\<^sup>*" by auto
    hence "(Fun f ts, Fun f ss) \<in> A\<^sup>\<down>" by auto
  }
  thus ?thesis unfolding all_ctxt_closed_def by auto
qed

lemma ground_join_rel_fground_joinable:
  assumes "\<C>_compatible {\<succ>}" and "(s, t) \<in> ground_join_rel R"
  and R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> less s t \<or> (t, s) \<in> R"
  shows "fground_joinable F {\<succ>} R s t"
  using assms(2)
proof(induct)
  case (refl t)
  thus ?case unfolding fground_joinable_def by auto
next
  case (var_order s t)
  thus ?case using var_order_joinable_ground_joinable assms by auto
next
  case (step l r s C \<sigma> t)
  with rstep_ground_joinable[OF _ R, of s t] show ?case unfolding step by auto
next
  case (rewrite_left s t u)
  from this(3) have step:"(u, s) \<in> ordstep {\<succ>} R" unfolding ordstep_def by auto
  { fix \<sigma> :: "('a, 'b) subst"
    assume g:"fground F (u \<cdot> \<sigma>)" "fground F (t \<cdot> \<sigma>)"
    from subst have "subst.closed {\<succ>}" by auto
    note step' = ordstep_subst[OF this step]
    from ordstep_FGROUND[OF g(1) step'] have gs:"fground F (s \<cdot> \<sigma>)" unfolding FGROUND_def by auto
    with rewrite_left(2)[unfolded fground_joinable_def, rule_format] g have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" by auto
    from rtrancl_join_join[OF _ this] step' have "(u \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" by auto
  }
  thus ?case unfolding fground_joinable_def by auto
next
  case (rewrite_right s t u)
  from this(3) have step:"(u, t) \<in> ordstep {\<succ>} R" unfolding ordstep_def by auto
  { fix \<sigma> :: "('a, 'b) subst"
    assume g:"fground F (s \<cdot> \<sigma>)" "fground F (u \<cdot> \<sigma>)"
    from subst have "subst.closed {\<succ>}" by auto
    note step' = ordstep_subst[OF this step]
    from ordstep_FGROUND[OF g(2) step'] have gs:"fground F (t \<cdot> \<sigma>)" unfolding FGROUND_def by auto
    with rewrite_right(2)[unfolded fground_joinable_def, rule_format] g have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" by auto
    from join_rtrancl_join[OF this] step' have "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (ordstep {\<succ>} R)\<^sup>\<down>" by auto
  }
  thus ?case unfolding fground_joinable_def by auto
next
  case (congg s f ss t ts)
  show ?case unfolding fground_joinable_def proof(rule, rule)
    fix \<sigma> :: "('a, 'b) subst"
    assume ground:"fground F (s \<cdot> \<sigma>) \<and> fground F (t \<cdot> \<sigma>)"
    let ?R = "ordstep {\<succ>} R"
    from all_ctxt_closed_join[OF all_ctxt_closed_ordsteps] have "all_ctxt_closed UNIV (?R\<^sup>\<down>)" by auto
    note acc = this[unfolded all_ctxt_closed_def, simplified, THEN conjunct1, rule_format]
    { fix i
      assume i:"i < length ts"
      with congg have gj:"fground_joinable F {\<succ>} R (ss ! i) (ts ! i)" by auto
      note gj = this[unfolded fground_joinable_def, rule_format, of \<sigma>]
      let ?s = "map (\<lambda>t. t \<cdot> \<sigma>) ss ! i" and ?t = "map (\<lambda>t. t \<cdot> \<sigma>) ts ! i"
      from ground[unfolded congg eval_term.simps] i congg(3) have "fground F ?s \<and> fground F ?t"
        unfolding fground_def by force
      with gj nth_map i congg(3) have "(?s,  ?t) \<in> ?R\<^sup>\<down>" by force
    }
    note ith_ground_joinable = this
    show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?R\<^sup>\<down>" unfolding congg eval_term.simps
      by (rule acc, unfold length_map congg(3), insert ith_ground_joinable, auto)
  qed
qed

lemma xCPs_ground_join_rel_GCR:
  assumes xCPs: "xCP {\<succ>} R \<subseteq> ground_join_rel R"
  and compat:"\<C>_compatible {\<succ>}" and R: "\<And>s t. (s, t) \<in> R \<Longrightarrow> less s t \<or> (t, s) \<in> R"
  shows "CR (FGROUND F (ordstep {\<succ>} R))"
proof-
  from assms(1) ground_join_rel_fground_joinable[OF compat _ R] xCP_def
    have "\<And>r r' p \<mu> u v. ooverlap {\<succ>} R r r' p \<mu> u v \<Longrightarrow> fground_joinable F {\<succ>} R u v"
    by fast 
  thus ?thesis using ground_joinable_ooverlaps_implies_GCR R by auto
qed
end

end
