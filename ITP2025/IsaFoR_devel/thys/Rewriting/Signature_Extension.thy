(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Signature_Extension
  imports 
    DP_Transformation
    Auxx.Util
begin

definition sig_step_below :: "'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "sig_step_below F R = {(a, b). (a, b) \<in> R \<and> funas_args_term a \<subseteq> F \<and> funas_args_term b \<subseteq> F}"

lemma sig_step_belowI [intro]:
  "(a, b) \<in> R \<Longrightarrow> funas_args_term a \<subseteq> F \<Longrightarrow> funas_args_term b \<subseteq> F \<Longrightarrow> (a,b) \<in> sig_step_below F R"
  unfolding sig_step_below_def by auto

lemma sig_step_belowE [elim, consumes 1]:
  "(a, b) \<in> sig_step_below F R \<Longrightarrow> \<lbrakk>(a,b) \<in> R \<Longrightarrow> funas_args_term a \<subseteq> F \<Longrightarrow> funas_args_term b \<subseteq> F \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding sig_step_below_def by auto

lemma trancl_sig_subset: "(sig_step F R)\<^sup>+ \<subseteq> sig_step F (R\<^sup>+)"
proof
  fix x y
  assume "(x,y) \<in> (sig_step F R)\<^sup>+"
  then have "funas_term x \<subseteq> F \<and> (x,y) \<in> sig_step F (R\<^sup>+)"
    by (induct, auto simp: sig_step_def)
  then show "(x,y) \<in> sig_step F (R\<^sup>+)" ..
qed

lemma sig_trancl_subset:
  assumes Rstep: "\<And> s t. funas_term s \<subseteq> F \<Longrightarrow> (s,t) \<in> R \<Longrightarrow> funas_term t \<subseteq> F"
  shows "sig_step F (R\<^sup>+) \<subseteq> (sig_step F R)\<^sup>+"
proof
  fix x y
  assume "(x,y) \<in> sig_step F (R\<^sup>+)"
  from sig_stepE[OF this]
  have "(x,y) \<in> R\<^sup>+" "funas_term x \<subseteq> F" by auto
  then have "(x,y) \<in> (sig_step F R)\<^sup>+ \<and> funas_term y \<subseteq> F"
  proof (induct)
    case (base z)
    from Rstep[OF base(2) base(1)] base show ?case
      unfolding sig_step_def by auto
  next
    case (step y z)
    note IH = step(3)[OF step(4)]
    note y = IH[THEN conjunct2]
    note z = Rstep[OF y step(2)]
    from IH[THEN conjunct1] sig_stepI[OF step(2) y z] z
    show ?case by auto
  qed
  then show "(x,y) \<in> (sig_step F R)\<^sup>+" ..
qed

lemma sig_trancl: assumes Rstep: "\<And> s t. funas_term s \<subseteq> F \<Longrightarrow> (s,t) \<in> R \<Longrightarrow> funas_term t \<subseteq> F"
  shows "(sig_step F R)\<^sup>+ = sig_step F (R\<^sup>+)"
  using sig_trancl_subset[of F R, OF Rstep] trancl_sig_subset[of F R] by auto

lemma sig_qrstep_trancl:
  assumes wwf: "wwf_qtrs Q R" and F: "funas_trs R \<subseteq> F"
  shows "(sig_step F (qrstep nfs Q R))\<^sup>+ = sig_step F ((qrstep nfs Q R)\<^sup>+)"
  by (rule sig_trancl, rule qrstep_funas_term[OF wwf F])

lemma the_inv_id [simp]: "the_inv id = (id :: 'a \<Rightarrow> 'a)"
  by (metis inj_on_id inv_id surj_id surj_imp_inv_eq the_inv_f_f)

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

lemma lhs_DP_on_wf:
  fixes R :: "('f, 'v) trs"
  defines "F \<equiv> funas_trs R \<union> \<sharp> (funas_trs R)"
  assumes DP: "(s, t) \<in> DP_on \<sharp> D R"
  shows "funas_term s \<subseteq> F"
proof -
  have subset: "funas_trs (DP_on \<sharp> D R) \<subseteq> F"
    using funas_DP_on_subset [of \<sharp> D R] unfolding F_def by auto
  have "funas_term s \<subseteq> funas_trs (DP_on \<sharp> D R)"
    using DP unfolding funas_trs_def funas_rule_def [abs_def] by auto
  with subset show ?thesis by auto
qed

lemma DP_on_not_is_Var_t:
  fixes R :: "('f, 'v) trs"
  shows "(s, t) \<in> DP_on \<sharp> D R \<Longrightarrow> is_Fun t"
unfolding DP_on_def by auto

lemma DP_on_not_is_Var_s:
  fixes R :: "('f, 'v) trs"
  shows "wf_trs R \<Longrightarrow> (s, t) \<in> DP_on \<sharp> D R \<Longrightarrow> is_Fun s"
unfolding DP_on_def wf_trs_def by force

lemma sharp_term_subst_distr_2:
  "is_Fun t \<Longrightarrow> \<sharp> t \<cdot> \<sigma> = \<sharp> (t \<cdot> \<sigma>)"
  by (cases t) auto

lemma left_DP_is_sharped_term:
  assumes "(s, t) \<in> DP_on \<sharp> D R"
  shows "\<exists>u \<in> lhss R. s = \<sharp> u"
using assms unfolding DP_on_def by force

text \<open>An auxiliary function to stack contexts (and substitutions) in order to reconstruct
DP steps in the original TRS.\<close>
private fun
  D :: "(nat \<Rightarrow> ('f, 'v) ctxt) \<Rightarrow> (nat \<Rightarrow> ('f, 'v) subst) \<Rightarrow> nat \<Rightarrow> ('f, 'v) ctxt"
where
  "D C \<sigma> 0 = \<box>" |
  "D C \<sigma> (Suc i) = (D C \<sigma> i) \<circ>\<^sub>c ((C i) \<cdot>\<^sub>c (\<sigma> i))"

lemma D_subst_wf:
  fixes F::"'f sig" and f::"('g, 'v) subst \<Rightarrow> ('f, 'v) subst"
  assumes \<sigma>: "\<And> i x. funas_term (\<sigma> i x) \<subseteq> F"
  assumes "\<forall>i. funas_ctxt (C i) \<subseteq> F" shows "funas_ctxt (D C \<sigma> i) \<subseteq> F"
proof (induct i)
  case (Suc i)
  obtain s where s: "\<sigma> i = s" by auto
  from assms have Ci: "funas_ctxt (C i) \<subseteq> F" by simp
  have Ci: "funas_ctxt (C i \<cdot>\<^sub>c \<sigma> i) \<subseteq> F" using Ci \<sigma> by auto
  show ?case using Suc Ci by simp
qed auto

(* TODO: perhaps specialize to arbitrary \<sharp>-functions instead of id *)
theorem clean_ichain_imp_not_SN_sig_qrstep:
  fixes R::"('f, 'v) trs"
  assumes G: "funas_trs R \<subseteq> G"
    and chain: "ichain (nfs, m, DP \<sharp> R, {}, Q, {}, R) s t \<sigma>"
    and \<sigma>: "\<And> i x . funas_term (\<sigma> i x) \<subseteq> G"
    and id: "\<sharp> = (id :: 'f \<Rightarrow> 'f)"
    and nfs: "nfs \<Longrightarrow> wwf_qtrs Q R"
  shows "\<not> SN (sig_step G (qrstep nfs Q R))"
proof -
  let ?F = "funas_trs R \<union> \<sharp> (funas_trs R)"
  let ?F' = "G \<union> \<sharp> G"
  from id have inj: "inj shp" by auto
  from chain have P_seq: "\<And>i. (s i, t i) \<in> DP \<sharp> R"
    and seq: "\<forall>i. ((t i) \<cdot> \<sigma> i, (s (Suc i)) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q R)\<^sup>*"
    and NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NF_terms Q"
    by (auto simp: ichain.simps)
  let ?us = "sharp_term (the_inv shp)"
  have "\<forall>i. \<exists>C. funas_ctxt C \<subseteq> G \<and> (?us(s i), C\<langle>?us(t i)\<rangle>) \<in> R"
  proof
    fix i from P_seq have "(s i, t i) \<in> DP \<sharp> R" by simp
    from DP_on_step_in_R [OF this inj]
    have "\<exists>C. funas_ctxt C \<subseteq> funas_trs R \<and> (?us (s i), C\<langle>?us(t i)\<rangle>) \<in> R" .
    then show "\<exists>C. funas_ctxt C \<subseteq> G \<and> (?us (s i), C\<langle>?us(t i)\<rangle>) \<in> R" using G by blast
  qed
  from choice[OF this] obtain C
    where C: "\<forall>i. funas_ctxt (C i) \<subseteq> G \<and> (?us (s i), (C i)\<langle>?us(t i)\<rangle>) \<in> R" by best
  have wf_ctxt: "\<forall> i. funas_ctxt (C i) \<subseteq> G" using C by auto
  {
    fix i
    have R: "(?us(s i), (C i)\<langle>?us(t i)\<rangle>) \<in> R" (is "?lr \<in> R") using C by auto
    {
      assume "s i \<cdot> \<sigma> i \<in> NF_terms Q"
      have "NF_subst nfs (s i, (C i)\<langle>t i\<rangle>) (\<sigma> i) Q"
      proof
        fix x
        assume nfs
        assume x: "x \<in> vars_term (s i) \<or> x \<in> vars_term ((C i)\<langle>t i\<rangle>)"
        from only_applicable_rules[OF NF_imp_subt_NF[OF NF]]
        have app: "applicable_rule Q ?lr" unfolding id by simp
        from nfs[OF \<open>nfs\<close>] have "wwf_qtrs Q R" by auto
        from this[unfolded wwf_qtrs_def, rule_format, OF R, unfolded split, rule_format, OF app]
        have "vars_term ((C i)\<langle>t i\<rangle>) \<subseteq> vars_term (s i)" unfolding id by auto
        with x have x: "x \<in> vars_term (s i)" by auto
        have "Var x \<cdot> \<sigma> i \<in> NF_terms Q"
          by (rule NF_subterm[OF NF[of i]], rule supteq_subst, insert x, auto)
        then show "\<sigma> i x \<in> NF_terms Q" by simp
      qed
    } note nfs = this
    have root_steps:
      "(?us(s i) \<cdot> (\<sigma> i), (C i \<cdot>\<^sub>c (\<sigma> i))\<langle>?us(t i) \<cdot> (\<sigma> i)\<rangle>) \<in> qrstep nfs Q R"
      by (rule qrstepI[OF NF_imp_subt_NF R, of "(\<sigma> i)" _ _ Hole],
        insert NF[of i] nfs, auto simp: id)
  } note root_steps = this
  let ?C = "D C \<sigma>"
  let ?s = "\<lambda>i. (?C i)\<langle>?us(s i) \<cdot> (\<sigma> i)\<rangle>"
  let ?t = "\<lambda>i. (?C (Suc i))\<langle>?us(t i) \<cdot> (\<sigma> i)\<rangle>"
  {
    fix i
    from id have "\<sharp> (s i) \<cdot> \<sigma> i = \<sharp> (s i \<cdot> \<sigma> i)"
      by simp
  } note si = this
  {
    fix i
    from id have "\<sharp> (t i) \<cdot> \<sigma> i = \<sharp> (t i \<cdot> \<sigma> i)"
      by simp
  } note ti = this
  {
    fix i
    have ctxt_steps: "(?s i, ?t i) \<in> qrstep nfs Q R" using qrstep.ctxt[OF root_steps[of i], of "D C \<sigma> i"] unfolding D.simps ctxt_ctxt .
  } note siti = this
  have aux: "\<forall>i.
    ( (?us(t i) \<cdot> \<sigma> i), (?us(s (Suc i)) \<cdot> \<sigma> (Suc i))) \<in> (qrstep nfs Q R)\<^sup>*"
    (is "\<forall>i. ?Q i") using seq si ti unfolding id the_inv_id by auto
  have ctxt: "ctxt.closed ((qrstep nfs Q R)\<^sup>*)" by blast
  have "\<forall>i. (?us(t i) \<cdot> \<sigma> i, ?us(s (Suc i)) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q R)\<^sup>*"
    (is "\<forall>i. ?P i")
  proof
    fix i
    from aux have "?Q i" by simp
    then show "?P i"
      unfolding map_funs_subst_distrib o_def id by simp
  qed
  then have steps: "\<forall>i. (?t i, ?s (Suc i)) \<in> (qrstep nfs Q R)\<^sup>*" using
    ctxt.closedD[OF ctxt] by blast
  have big_step: "\<forall>i. (?s i, ?s(Suc i)) \<in> (qrstep nfs Q R)\<^sup>+"
  proof
    fix i
    from siti have "(?s i, ?t i) \<in> qrstep nfs Q R" by best
    moreover from steps have "(?t i, ?s (Suc i)) \<in> (qrstep nfs Q R)\<^sup>*" by blast
    ultimately show "(?s i, ?s (Suc i)) \<in> (qrstep nfs Q R)\<^sup>+" by (rule rtrancl_into_trancl2)
  qed
  have "\<forall>i. funas_ctxt (?C i) \<subseteq> G" using D_subst_wf[OF \<sigma> wf_ctxt]
    by auto
  moreover have "\<forall>i. funas_term (?us(s i) \<cdot> (\<sigma> i)) \<subseteq> G"
  proof
    fix i
    from lhs_DP_on_wf [of _ _ _ R] and P_seq have "funas_term (s i) \<subseteq> ?F" by best
    from this[unfolded]
    have "funas_term (?us(s i)) \<subseteq> funas_trs R" unfolding id by simp
    then have wf: "funas_term (?us(s i)) \<subseteq> G" using G by simp
    show "funas_term (?us(s i) \<cdot> \<sigma> i) \<subseteq> G" unfolding funas_term_subst
      using wf vars_sharp_eq_vars \<sigma> by auto
  qed
  ultimately have "\<forall>i. funas_term (?s i) \<subseteq> G" by auto
  with big_step
    have seq: "\<forall>i. (?s i, ?s(Suc i)) \<in> sig_step G ((qrstep nfs Q R)\<^sup>+)"
    (is "\<forall>i. _ \<in> ?steps") by blast
  have"?s 0 \<in> UNIV" by simp
  with seq have "?s 0 \<in> UNIV \<and> (\<forall>i. (?s i, ?s (Suc i)) \<in> ?steps)" by best
  then have "\<exists>S. S 0 \<in> UNIV \<and> (\<forall>i. (S i, S (Suc i)) \<in> ?steps)" by best
  then have nSN: "\<not> SN ?steps" unfolding SN_defs by blast
  show ?thesis
  proof (cases "wwf_qtrs Q R")
    case True
    from nSN have "\<not> SN ((sig_step G (qrstep nfs Q R))\<^sup>+)"
      using sig_qrstep_trancl[OF True subset_refl] G by (simp add: True sig_qrstep_trancl) 
    with SN_trancl_SN_conv show ?thesis by auto
  next
    case False
    with nfs SN_sig_qrstep_imp_wwf_trs[of G nfs Q R]
    show ?thesis using G by blast
  qed
qed

end

fun funas_dpp :: "('f, 'v) dpp \<Rightarrow> 'f sig"
where
  "funas_dpp (nfs, m, P, Pw, Q, Rw, R) = funas_trs P \<union> funas_trs Pw \<union> funas_trs R \<union> funas_trs Rw"

locale cleaning =
  fixes F :: "'f sig"
    and c :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
  assumes c [simp, intro]: "funas_term (c t) \<subseteq> F"
begin

fun clean_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "clean_term (Var y) = Var y" |
  "clean_term (Fun f ts) =
    (if (f, length ts) \<in> F then Fun f (map clean_term ts)
    else c (Fun f ts))"

fun clean_subst :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
where
  "clean_subst \<sigma> = (clean_term \<circ> \<sigma>)"

lemma funas_term_clean_term:
  "funas_term (clean_term t) \<subseteq> F"
  by (induct t, auto)

lemma funas_term_clean_termD [dest]:
  "f \<in> funas_term (clean_term t) \<Longrightarrow> f \<in> F"
using funas_term_clean_term by blast

lemma clean_subst_apply_term [simp]:
  assumes "funas_term t \<subseteq> F"
  shows "clean_term (t \<cdot> \<sigma>) = t \<cdot> (clean_subst \<sigma>)"
using assms
proof (induct t)
  case (Fun f ss)
  from Fun(2)
    have "\<forall>t\<in>set ss. funas_term t \<subseteq> F" by auto
  with Fun have IH: "\<And>t. t \<in> set ss \<Longrightarrow> clean_term (t \<cdot> \<sigma>) = t \<cdot> (clean_subst \<sigma>)" by best
  with Fun show ?case by auto
qed simp

lemma clean_term_ident [simp]:
  assumes t: "funas_term t \<subseteq> F"
  shows "clean_term t = t"
  using clean_subst_apply_term[OF t, of Var] by (auto simp: o_def)

lemma clean_term_idemp [simp]:
  "clean_term (clean_term t) = clean_term t"
  using clean_term_ident[OF funas_term_clean_term[of t]] .

lemma clean_ctxt_apply:
  assumes "funas_ctxt C \<subseteq> F" shows "clean_term (C\<langle>t\<rangle>) = C\<langle>clean_term t\<rangle>"
using assms
proof (induct C)
  fix clean
  case (More f ss1 E ss2)
  let ?C = "More f ss1 E ss2"
  from More have "(f,Suc(length(ss1@ss2))) \<in> F" by auto
  then have in_F: "(f, length (ss1 @ E\<langle>clean F t\<rangle> # ss2)) \<in> F" by auto
  from More have "clean_term (?C\<langle>t\<rangle>) = Fun f (map clean_term (ss1 @ E\<langle>t\<rangle> # ss2))" by auto
  have "clean_term (E\<langle>t\<rangle>) = E\<langle>clean_term t\<rangle>"
    by (rule More(1), insert More(2), auto)
  from More(2) have "\<And> t. t \<in> set (ss1 @ ss2) \<Longrightarrow> funas_term t \<subseteq> F" by auto
  note args = clean_term_ident[OF this]
  from args have "\<forall>t\<in>set ss1. clean_term t = t" by auto
  then have pre: "map clean_term ss1 = ss1" using map_idI[of ss1 clean_term] by best
  from args have "\<forall>t\<in>set ss2. clean_term t = t" by auto
  then have "map clean_term ss2 = ss2" using map_idI[of ss2 clean_term] by best
  with More \<open>clean_term (E\<langle>t\<rangle>) = E\<langle>clean_term t\<rangle>\<close>
  have post: "map clean_term (E\<langle>t\<rangle> # ss2) = E\<langle>clean_term t\<rangle> # ss2" by auto
  have "map clean_term (ss1 @ E\<langle>t\<rangle> # ss2)
    = map clean_term ss1 @ map clean_term (E\<langle>t\<rangle> # ss2)"
    by simp
  also have "\<dots> = ss1 @ E\<langle>clean_term t\<rangle> # ss2" unfolding pre post by simp
  finally have "map clean_term (ss1@ E\<langle>t\<rangle> # ss2) = ss1 @ E\<langle>clean_term t\<rangle> # ss2" .
  with in_F show ?case by simp
qed simp

lemma clean_term_if [simp]:
  "clean_term (if P then s else t) = (if P then clean_term s else clean_term t)"
  by simp

lemma funas_ichain_clean_subst:
  "funas_ichain s t (\<lambda> i. clean_subst (\<sigma> i)) \<subseteq> F"
  unfolding funas_ichain_def by (simp, insert funas_term_clean_term, blast)

lemma clean_term_Var_id [simp]:
  "clean_term \<circ> Var = Var" by (rule ext) (simp add: o_def)

end

locale cleaning_const =
  cleaning F c for F and c :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" +
  fixes const :: "('f, 'v) term"
  assumes const: "c t = const"
begin

lemma rstep_imp_clean_rstep_or_Id:
  fixes R::"('f, 'v) trs"
  defines [simp]: "ct \<equiv> clean_term"
  assumes subset: "funas_trs R \<subseteq> F"
    and step: "(s, t) \<in> rstep R"
  shows "(ct s, ct t) \<in> rstep R \<union> Id"
proof -
  from rstep_imp_C_s_r[OF step] obtain C l r \<sigma>
    where R: "(l,r) \<in> R"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>"
    and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  from s t show ?thesis
  proof (induct C arbitrary: s t)
    case Hole
    let ?c = "\<lambda>\<sigma>. (ct \<circ> \<sigma>)"
    from clean_subst_apply_term[OF lhs_wf[OF R subset]]
      have s: "ct(s) = l\<cdot>?c(\<sigma>)" unfolding Hole by simp
    from clean_subst_apply_term[OF rhs_wf[OF R subset]]
      have t: "ct(t) = r\<cdot>?c(\<sigma>)" unfolding Hole by simp
    from R have "(ct(s),ct(t)) \<in> subst.closure R" unfolding s t by auto
    then have "(ct(s),ct(t)) \<in> rstep R" using ctxt.closure.intros[where a=\<box>] unfolding rstep_eq_closure by simp
    then show ?case ..
  next
    case (More f ss1 D ss2)
    then have IH: "(ct(D\<langle>l\<cdot>\<sigma>\<rangle>),ct(D\<langle>r\<cdot>\<sigma>\<rangle>)) \<in> rstep R \<union> Id" by simp
    show ?case
    proof (cases "(f,Suc(length(ss1@ss2))) \<in> F")
      case False
      with More have "ct(s) = const" using const by auto
      moreover from False More have "ct(t) = const" using const by auto
      ultimately have "(ct(s),ct(t)) \<in> Id" by simp
      then show ?thesis ..
    next
      case True
      let ?s = "ct(D\<langle>l\<cdot>\<sigma>\<rangle>)"
      let ?t = "ct(D\<langle>r\<cdot>\<sigma>\<rangle>)"
      from IH show ?thesis
      proof
        assume "(?s,?t) \<in> Id" with True More show ?thesis by auto
      next
        let ?C = "More f (map ct ss1) \<box> (map ct ss2)"
        assume "(?s,?t) \<in> rstep R"
        from rstep_ctxt[OF this,where C="?C"]
          have "(ct(s),ct(t)) \<in> rstep R" unfolding More using True by simp
        then show ?thesis ..
      qed
    qed
  qed
qed

lemma rsteps_imp_clean_rsteps:
  fixes R::"('f, 'v) trs"
  defines [simp]: "ct \<equiv> clean_term"
  assumes subset: "funas_trs R \<subseteq> F"
  and steps: "(s,t) \<in> (rstep R)\<^sup>*"
  shows "(ct s, ct t) \<in> (rstep R)\<^sup>*"
using steps proof (induct rule: rtrancl_induct)
  case base show ?case by simp
next
  case (step y z)
  from subset have "funas_trs R \<subseteq> F" by auto
  from rstep_imp_clean_rstep_or_Id[OF this \<open>(y,z) \<in> rstep R\<close>]
  have "(ct(y),ct(z)) \<in> rstep R \<union> Id" by (simp only: ct_def)
  then show ?case
  proof
    assume "(ct y,ct z) \<in> Id" with step show ?thesis by simp
  next
    assume "(ct y,ct z) \<in> rstep R" with step show ?thesis by auto
  qed
qed

lemma ichain_imp_clean_ichain:
  fixes P R::"('f, 'v) trs" and nfs m :: bool
  defines "ct \<equiv> \<lambda>t::('f, 'v) term. clean_term t"
  defines "cs \<equiv> \<lambda>\<sigma>::('f, 'v) subst. clean_subst \<sigma>"
  assumes subset: "funas_dpp (nfs, m, P, Pw, {}, {}, R) \<subseteq> F"
    and ichain: "ichain (nfs,m, P, Pw, {}, {}, R) s t \<sigma>"
  shows "ichain (nfs,m, P, Pw, {}, {}, R) s t (\<lambda>i. cs (\<sigma> i))"
proof -
  let ?P = "P \<union> Pw"
  from ichain have dpstep: "\<forall>i. (s i, t i) \<in> ?P"
    and seq: "\<forall>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (rstep R)\<^sup>*"
    by (simp_all add: ichain.simps)
  from subset have subset_P: "funas_trs ?P \<subseteq> F" by (auto simp: funas_trs_def)
  from subset have subset_R: "funas_trs R \<subseteq> F" by simp
  {
    fix i
    from dpstep have "(s i, t i) \<in> ?P" by simp
    from lhs_wf[OF this subset_P] have "funas_term (s i) \<subseteq> F" .
  } note wf_s = this
  {
    fix i
    from dpstep have "(s i, t i) \<in> ?P" by simp
    from rhs_wf[OF this subset_P] have "funas_term (t i) \<subseteq> F" .
  } note wf_t = this
  have seq': "\<forall>i. (ct (t i \<cdot> (\<sigma> i)), ct (s (Suc i) \<cdot> (\<sigma> (Suc i)))) \<in> (rstep R)\<^sup>*"
    (is "\<forall>i. (ct (?t i), ct (?s i)) \<in> _")
    using seq rsteps_imp_clean_rsteps[OF subset_R] unfolding ct_def by blast
  have "\<forall>i. (t i \<cdot> cs (\<sigma> i), s (Suc i) \<cdot> cs (\<sigma> (Suc i))) \<in> (rstep R)\<^sup>*"
  proof
    fix i
    have cts: "ct (t i \<cdot> \<sigma> i) = t i \<cdot> cs (\<sigma> i)"
      using clean_subst_apply_term[OF wf_t[of i]]
      unfolding ct_def cs_def o_def by auto
    have css: "ct (s (Suc i) \<cdot> \<sigma> (Suc i)) = s (Suc i) \<cdot> cs (\<sigma> (Suc i))"
      using clean_subst_apply_term[OF wf_s[of "Suc i"]]
      unfolding ct_def cs_def o_def by auto
    from seq'[THEN spec[of _ i]]
      show "(t i \<cdot> cs (\<sigma> i), s (Suc i) \<cdot> cs (\<sigma> (Suc i))) \<in> (rstep R)\<^sup>*"
      unfolding cts css .
  qed
  with dpstep ichain show ?thesis by (simp add: ichain.simps)
qed
end

locale cleaning_same_var =
  cleaning_const F c const for F c and const :: "('f, 'v) term" +
  assumes var: "is_Var (const)"
begin

lemma clean_weak_match:
  "weak_match t (clean_term t)"
proof (induct t)
  case (Fun f ts)
  let ?n = "length ts"
  show ?case
  proof (cases "(f,?n) \<in> F")
    case False
    then have "clean_term (Fun f ts) = const" using const by simp
    then show ?thesis using var by (cases const, auto)
  next
    case True
    {
      fix i
      assume i: "i < ?n"
      then have "ts ! i \<in> set ts" by simp
      from Fun[OF this] have "weak_match (ts ! i) (clean_term (ts ! i))" .
    }
    with True show ?thesis by simp
  qed
qed simp

lemma left_linear_SN_on_imp_clean_SN_on:
  assumes ll: "left_linear_trs R"
  and SN: "SN_on (rstep R) {s}"
  shows "SN_on (rstep R) {clean_term s}"
  by (rule weak_match_SN[OF clean_weak_match ll SN])

lemma left_linear_min_ichain_imp_clean_min_ichain:
  defines "ct \<equiv> clean_term"
  defines "cs \<equiv> clean_subst"
  assumes subset: "funas_dpp (nfs, m, P, Pw, {}, {}, R) \<subseteq> F"
    and left_linear: "left_linear_trs R"
    and chain: "min_ichain (nfs,m,P, Pw, {}, {}, R) s t \<sigma>"
  shows "min_ichain (nfs,m,P, Pw, {}, {}, R) s t (\<lambda>i. cs (\<sigma> i))"
proof -
  from chain have ichain: "ichain (nfs,m,P, Pw, {}, {}, R) s t \<sigma>"
    and minimal: "m \<Longrightarrow> \<forall>i. SN_on (rstep R) {t i \<cdot> \<sigma> i}"
    by (auto simp: minimal_cond_def)
  from ichain_imp_clean_ichain[OF subset ichain]
    have ichain: "ichain (nfs,m,P, Pw, {}, {}, R) s t (\<lambda> i. cs (\<sigma> i))" unfolding cs_def .
  from subset have "funas_trs R \<subseteq> F" by simp
  from subset have subset_P: "funas_trs (P \<union> Pw) \<subseteq> F" and subset_R: "funas_trs R \<subseteq> F" by (auto simp: funas_trs_def)
  {
    fix i
    from ichain have "(s i,t i) \<in> P \<union> Pw" by (simp add: ichain.simps)
    from rhs_wf[OF this subset_P] have "funas_term (t i) \<subseteq> F" .
  } note wf_t = this
  have minimal: "m \<Longrightarrow> \<forall>i. SN_on (rstep R) {t i \<cdot> (cs(\<sigma> i))}"
  proof
    fix i assume m
    show "SN_on (rstep R) {(t i) \<cdot> cs(\<sigma> i)}"
    proof -
      from
        clean_subst_apply_term[OF wf_t[of i], of "\<sigma> i"]
        left_linear_SN_on_imp_clean_SN_on[OF left_linear minimal[OF \<open>m\<close>, THEN spec[of _ i]]]
        show ?thesis unfolding cs_def ct_def by simp
    qed
  qed
  with ichain show ?thesis by (auto simp: minimal_cond_def)
qed

lemma ichain_imp_clean_ichain_fcc:
  fixes P Pw R::"('f, 'v) trs"
  defines "ct \<equiv> clean_term"
  defines "cs \<equiv> clean_subst"
  assumes subset: "funas_args_trs (P \<union> Pw) \<union> funas_trs R \<subseteq> F"
  and non_var: "\<And>s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t \<and> \<not> defined R (the (root t))"
  and nvar: "\<forall>(l, r)\<in>R. is_Fun l"
  and chain: "ichain (nfs,m,P,Pw,{},{},R) s t \<sigma>"
  shows "ichain (nfs,m,P,Pw,{},{},R) s t (\<lambda> i. cs (\<sigma> i))"
proof -
  from chain have dpstep: "\<And> i. (s i,t i) \<in> P \<union> Pw"
    and seq: "\<And> i. (t i \<cdot> \<sigma> i,s(Suc i)\<cdot>\<sigma>(Suc i)) \<in> (rstep R)\<^sup>*"
    by (auto simp: ichain.simps)
  let ?split = "\<lambda> i f g ss ts. s i = Fun f ss \<and> t i = Fun g ts \<and> \<not> defined R (g, length ts)"
  have fs: "\<forall> i. \<exists> f g ss ts. ?split i f g ss ts"
  proof
    fix i
    from non_var dpstep have "is_Fun (s i) \<and> is_Fun (t i)" by auto
    with non_var[OF dpstep[of i]] obtain f ss g ts where "?split i f g ss ts" by force
    then show "\<exists> f g ss ts. ?split i f g ss ts" by blast
  qed
  from choice[OF fs] obtain f where fs: "\<forall> i. \<exists> g ss ts. ?split i (f i) g ss ts" ..
  from choice[OF fs] obtain g where fs: "\<forall> i. \<exists> ss ts. ?split i (f i) (g i) ss ts" ..
  from choice[OF fs] obtain ss where fs: "\<forall> i. \<exists> ts. ?split i (f i) (g i) (ss i) ts" ..
  from choice[OF fs] obtain ts where fs: "\<And> i. ?split i (f i) (g i) (ss i) (ts i)" by auto
  let ?s = "\<lambda> i. Fun (f i) (map ct (ss i))"
  let ?t = "\<lambda> i. Fun (g i) (map ct (ts i))"
  let ?ssj = "\<lambda> i j. ss i ! j \<cdot> \<sigma> i"
  let ?tsj = "\<lambda> i j. ts i ! j \<cdot> \<sigma> i"
  let ?ssc = "\<lambda> i j. ss i ! j \<cdot> cs(\<sigma> i)"
  let ?tsc = "\<lambda> i j. ts i ! j \<cdot> cs(\<sigma> i)"
  let ?cond = "\<lambda> i. length (ts i) = length (ss (Suc i)) \<and> g i = f (Suc i) \<and> (\<forall> j < length (ts i). (?tsj i j, ?ssj (Suc i) j) \<in> (rstep R)\<^sup>*)"
  have argsteps: "\<And> i. ?cond i"
  proof -
    fix i
    from fs have ndef: "\<not> defined R (g i, length (ts i))" by auto
    from nondef_root_imp_arg_steps[OF seq[of i, simplified fs, simplified] nvar, simplified, OF ndef]
      nth_map[where xs = "ts  i"]
    show "?cond i" by auto
  qed
  from subset have subset_P: "funas_args_trs (P \<union> Pw) \<subseteq> F" by simp
  from subset have subset_R: "funas_trs R \<subseteq> F" by simp
  have main: "\<And> i j. j < length (ts i) \<Longrightarrow> (?tsc i j, ?ssc (Suc i) j) \<in> (rstep R)\<^sup>*"
  proof -
    fix i j
    assume j: "j < length (ts i)"
    with fs have "?tsj i j \<in> set (args (t i \<cdot> \<sigma> i))" by simp
    from j fs[of "Suc i"] argsteps[of i] have "ss (Suc i) ! j \<in> set (args (s (Suc i)))" by auto
    with dpstep[of "Suc i"] subset_P have wf_s: "funas_term (ss (Suc i) ! j) \<subseteq> F"
      unfolding funas_args_defs [abs_def] by force
    from j fs[of i] have "ts i ! j \<in> set (args (t i))" by auto
    with dpstep[of i] subset_P have wf_t: "funas_term (ts i ! j) \<subseteq> F"
      unfolding funas_args_defs [abs_def] by force
    have c_t: "ct(?tsj i j) = (?tsc i j)" unfolding ct_def cs_def
      by (simp add: clean_subst_apply_term[OF wf_t])
    have c_s: "ct(?ssj (Suc i) j) = (?ssc (Suc i) j)" unfolding ct_def cs_def
      by (simp add: clean_subst_apply_term[OF wf_s])
    from argsteps[of i] j have "(?tsj i j, ?ssj (Suc i) j) \<in> (rstep R)\<^sup>*" by simp
    from rsteps_imp_clean_rsteps[OF subset_R this] show "(?tsc i j, ?ssc (Suc i) j) \<in> (rstep R)\<^sup>*"
      unfolding c_t[symmetric] c_s[symmetric] ct_def .
  qed
  {
    fix i
    from \<open>?cond i\<close> have len: "(length (ss (Suc i))) = length (ts i)" by simp
    have "(Fun (g i) (map (\<lambda> t. t \<cdot> cs (\<sigma> i)) (ts i)), Fun (g i) (map (\<lambda> t. t \<cdot> cs (\<sigma> (Suc i))) (ss (Suc i)))) \<in> (rstep R)\<^sup>*"
    proof (rule all_ctxt_closedD[OF all_ctxt_closed_rsteps[of UNIV R]], simp, simp add: \<open>?cond i\<close>, simp add: len)
      fix j
      assume "j < length (ts i)"
      from main[OF this]
      show "(?tsc i j, ?ssc (Suc i) j) \<in> (rstep R)\<^sup>*" .
    qed auto
    with \<open>?cond i\<close>
    have "(t i \<cdot> cs (\<sigma> i), s (Suc i) \<cdot> cs (\<sigma> (Suc i))) \<in> (rstep R)\<^sup>*" by (simp add: fs[of i] fs[of "Suc i"])
  }
  with dpstep chain show ?thesis by (auto simp: ichain.simps)
qed

(* it follows the crucial lemma for flat context closures *)
(* unfortunately, it does not hold for non-left-linear systems, see
   CSL'10 paper *)
(* and even more unfortunately, it does not hold for strict R rules:
   P = {}, Pw = {F(x,y) \<rightarrow> F(x,f(x))}, Q = {}, R = {a \<rightarrow> b}, Rw = {f(a) \<rightarrow> f(a)}
   inf min-chain: F(g(a),f(g(b))) \<rightarrow>Pw F(g(a),f(g(a))) \<rightarrow>R F(g(a),f(g(b))) \<rightarrow>Pw ...
   however, if we restrict substitution to non-top signature of DPP which
   here is {f,a,b}, then there is no inf. minimal chain:
   - if inf-chain, then there must be inf. many R-rules as P is empty.
   - if we can apply any R-rule, then \<sigma> x must contain a as subterm
   - with signature {f,a,b} \<Rightarrow> \<sigma> x = f^i(a)
   - f(x)\<sigma> contains f(a) as subterm, and hence f(x)\<sigma> is non-terminating w.r.t. Rw
   - hence, chain is not minimal
*)
lemma left_linear_min_ichain_imp_clean_min_ichain_fcc:
  fixes P Pw R::"('f,'v)trs"
  defines "ct \<equiv> clean_term"
  defines "cs \<equiv> clean_subst"
  assumes left_linear: "left_linear_trs R"
  and subset: "funas_args_trs (P \<union> Pw) \<union> funas_trs R \<subseteq> F"
  and non_var: "\<And>s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t \<and> \<not> defined R (the (root t))"
  and non_varR: "\<not> m \<Longrightarrow> \<forall>(l, r)\<in>R. is_Fun l"
  and chain: "min_ichain (nfs,m,P,Pw,{},{},R) s t \<sigma>"
  shows "min_ichain (nfs,m,P,Pw,{},{},R) s t (\<lambda> i. cs (\<sigma> i))"
proof (cases m)
  case True
  with chain have ichain: "ichain (nfs,m,P,Pw,{},{},R) s t \<sigma>"
    and min: "\<And> i. SN_on (rstep R) {t i \<cdot> \<sigma> i}" by (auto simp: minimal_cond_def)
  from left_var_imp_not_SN[where R = R and t = "t 0 \<cdot> \<sigma> 0"] min[of 0]
  have nvar: "\<forall>(l, r)\<in>R. is_Fun l" by force
  from ichain_imp_clean_ichain_fcc[OF subset non_var nvar ichain]
  have ichain: "ichain (nfs,m,P,Pw,{},{},R) s t (\<lambda> i. cs (\<sigma> i))" unfolding cs_def .
  from subset have subset_P: "funas_args_trs (P \<union> Pw) \<subseteq> F" unfolding funas_dpp.simps by auto
  from subset have subset_R: "funas_trs R \<subseteq> F" by simp
  {
    fix i
    from ichain have "(s i, t i) \<in> P \<union> Pw" by (simp add: ichain.simps)
    with subset_P non_var[OF this] obtain f ts where 
      ti: "t i = Fun f ts" and tiP: "funas_args_term (Fun f ts) \<subseteq> F" 
      and ndef: "\<not> defined R (f, length (map (\<lambda> t. t \<cdot> cs (\<sigma> i)) ts))"
      unfolding funas_args_trs_def funas_args_rule_def [abs_def]
      by (cases "t i") force+
    have "SN_on (rstep R) {t i  \<cdot> (cs(\<sigma> i))}"
    proof (simp add: ti, rule SN_args_imp_SN_rstep[OF _ nvar ndef])
      fix u
      assume "u \<in> set (map (\<lambda> t. t \<cdot> cs (\<sigma> i)) ts)" (is "_ \<in> set ?ts")
      then obtain uu where uu: "uu \<in> set ts" and u: "u = uu \<cdot> cs (\<sigma> i)" by auto
      from uu tiP have wuu: "funas_term uu \<subseteq> F" unfolding funas_args_term_def by auto
      from SN_imp_SN_arg[OF min[of i, simplified ti, simplified]] uu have "SN_on (rstep R) {uu \<cdot> \<sigma> i}" by auto
      from left_linear_SN_on_imp_clean_SN_on[OF left_linear this] show "SN_on (rstep R) {u}"
        unfolding clean_subst_apply_term[OF wuu] u cs_def .
    qed
  }
  with ichain show ?thesis by (simp add: minimal_cond_def)
next
  case False
  from chain have ichain: "ichain (nfs,m,P,Pw,{},{},R) s t \<sigma>" by simp
  from ichain_imp_clean_ichain_fcc[OF subset non_var non_varR[OF False] ichain]
  show ?thesis unfolding cs_def using False by simp
qed
end

interpretation clean_same_var: cleaning_same_var F "\<lambda> _. Var (SOME x. True)" "Var (SOME x. True)"
  by (unfold_locales, auto)

lemma left_linear_min_ichain_imp_min_ichain_sig:
  fixes P Pw R::"('f,'v)trs"
  assumes left_linear: "left_linear_trs R"
  and subset: "funas_args_trs (P \<union> Pw) \<union> funas_trs R \<subseteq> F"
  and non_var: "\<And>s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t \<and> \<not> defined R (the (root t))"
  and chain: "min_ichain (nfs,m,P,Pw,{},{},R) s t \<sigma>"
  and non_varR: "\<not> m \<Longrightarrow> \<forall>(l, r)\<in>R. is_Fun l"
  shows "\<exists> \<sigma>. min_ichain_sig (nfs,m,P,Pw,{},{},R) F s t \<sigma>"
   by (rule exI, unfold min_ichain_sig.simps, rule conjI[OF _ clean_same_var.funas_ichain_clean_subst],
    rule clean_same_var.left_linear_min_ichain_imp_clean_min_ichain_fcc[OF left_linear subset non_var non_varR chain])

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

lemma funas_dpp_initial_subset_sharp_sig:
  "funas_dpp (nfs, m, DP_on \<sharp> D R, {}, Q, {}, R) \<subseteq> funas_trs R \<union> \<sharp> (funas_trs R)"
using funas_DP_on_subset [of \<sharp> D R] by auto

end

lemma SN_sig_rstep_imp_SN_rstep:
  fixes R :: "('f, 'v) trs"
  assumes F: "funas_trs R \<subseteq> F"
  and SN: "SN (sig_step F (rstep R))"
  shows "SN (rstep R)"
proof (cases "wf_trs R")
  case False
  with SN_sig_step_imp_wf_trs[OF SN F] show ?thesis by blast
next
  case True
  obtain nfs m where nfs: "\<not> nfs" and m: "\<not> m" by auto
  show ?thesis
  proof (rule ccontr)
    assume "\<not> SN (rstep R)"
    from not_SN_imp_ichain_rstep[OF True this]
    obtain s t \<sigma> where ichain: "ichain (nfs,m,DP id R, {},{},{},R) s t \<sigma>" by blast
    interpret cleaning_same_var "F \<union> sharp_sig id (funas_trs R)" "\<lambda> _. (Var x) :: ('f,'v)term" "Var x" by (unfold_locales, auto)
    from funas_dpp_initial_subset_sharp_sig
    have "funas_dpp (nfs, m, DP id R, {}, {}, {}, R) \<subseteq> F \<union> sharp_sig id (funas_trs R)" using F by blast
    from ichain_imp_clean_ichain [OF this ichain]
    have ichain: "ichain (nfs,m,DP id R,{},{},{},R) s t (\<lambda>i. clean_subst (\<sigma> i))" .
    have  "\<not> SN (sig_step F (rstep R))" unfolding qrstep_rstep_conv[symmetric, of _ nfs]
    proof (rule clean_ichain_imp_not_SN_sig_qrstep[OF F ichain _ refl])
      fix i x
      show "funas_term (clean_subst (\<sigma> i) x) \<subseteq> F" unfolding clean_subst.simps
        o_def using funas_term_clean_term using F by auto 
    qed (insert nfs, auto)
    with assms show False by blast
  qed
qed

lemma SN_sig_rstep_SN_rstep_conv: "SN (sig_step (funas_trs R) (rstep R)) = SN (rstep R)" (is "SN ?R = _")
  using SN_subset[of "rstep R" ?R]  SN_sig_rstep_imp_SN_rstep unfolding sig_step_def by blast

lemma SN_wf_ground: assumes c: "(c,0) \<in> F" and F: "funas_trs R \<subseteq> F"
  and SN: "\<And> t. funas_term t \<subseteq> F \<Longrightarrow> ground t \<Longrightarrow> SN_on (rstep R) {t}"
  shows "SN (rstep R)"
proof (rule SN_sig_rstep_imp_SN_rstep[OF subset_refl], rule)
  fix f
  let ?R = "sig_step (funas_trs R) (rstep R)"
  assume steps: "\<forall> i. (f i, f (Suc i)) \<in> ?R"
  then have f0: "funas_term (f 0) \<subseteq> funas_trs R" and steps: "\<And> i. (f i, f (Suc i)) \<in> rstep R" unfolding sig_step_def by auto
  let ?\<sigma> = "(\<lambda> _. Fun c [])"
  from f0 c have wf: "funas_term (f 0 \<cdot> ?\<sigma>) \<subseteq> F" (is "funas_term ?t \<subseteq> _") unfolding funas_term_subst using F by auto
  have "ground ?t" by auto
  from SN[OF wf this] have "SN_on (rstep R) {?t}" by auto
  from SNinstance_imp_SN[OF this] steps
  show False unfolding SN_defs by auto
qed


fun aliens :: "'f sig \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term list"
  where "aliens F (Var x) = []"
     |  "aliens F (Fun f ts) = (if (f,length ts) \<in> F then concat (map (aliens F) ts) else [Fun f ts])"

fun aliens_below :: "'f sig \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term list"
  where
   "aliens_below F (Fun f ts) = concat (map (aliens F) ts)"
 | "aliens_below F (Var x) = []"

lemma aliens_root: assumes "a \<in> set (aliens F t)"
  shows "\<not> is_Var a \<and> the (root a) \<notin> F"
  using assms
proof (induct t)
  case (Fun f ts)
  show ?case
  proof (cases "(f,length ts) \<in> F")
    case False
    with Fun(2) show ?thesis by auto
  next
    case True
    with Fun(2) obtain t where t: "t \<in> set ts" and a: "a \<in> set (aliens F t)" by auto
    from Fun(1)[OF this] show ?thesis .
  qed
qed simp

lemma aliens_subst:
  assumes "funas_term t \<subseteq> F"
  shows "aliens F (t \<cdot> \<sigma>) = concat (map (\<lambda> x. aliens F (\<sigma> x)) (vars_term_list t))"
proof -
  let ?a = "aliens F"
  note vars_term_list.simps [simp]
  show ?thesis using assms
  proof (induct t)
    case Var show ?case by simp
  next
    case (Fun f ts)
    let ?n = "length ts"
    from Fun(2) have f: "(f,?n) \<in> F" by auto
    {
      fix t
      assume t: "t \<in> set ts"
      with Fun(2) have "funas_term t \<subseteq> F" by auto
      from Fun(1)[OF t this] have "?a (t \<cdot> \<sigma>) = concat (map (\<lambda> x. ?a (\<sigma> x)) (vars_term_list t))" .
    } note IH = this
    have "?a (Fun f ts \<cdot> \<sigma>) = concat (map (\<lambda> t. ?a (t \<cdot> \<sigma>)) ts)"
      by (simp add: f o_def)
    also have "map (\<lambda> t. ?a (t \<cdot> \<sigma>)) ts = map (\<lambda> t. concat (map (\<lambda> x. ?a (\<sigma> x)) (vars_term_list t))) ts" (is "_ = ?r")
      by (rule map_cong [OF refl IH])
    finally have id: "?a (Fun f ts \<cdot> \<sigma>) = concat ?r" .
    show ?case unfolding id
      by (unfold vars_term_list.simps, induct ts, auto)
  qed
qed

lemma aliens_below_subst: assumes tF: "funas_args_term t \<subseteq> F"
  and nvar: "is_Fun t"
  shows "aliens_below F (t \<cdot> \<sigma>) = concat (map (\<lambda> x. aliens F (\<sigma> x)) (vars_term_list t))"
proof -
  from nvar obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  have "aliens_below F (t \<cdot> \<sigma>) = concat (map (\<lambda>x. aliens F (x \<cdot> \<sigma>)) ts)" unfolding t by (simp add: comp_def)
  also have "map (\<lambda>t. aliens F (t \<cdot> \<sigma>)) ts = map (\<lambda> t. concat (map (\<lambda> x. aliens F (\<sigma> x)) (vars_term_list t))) ts"
  proof (rule map_cong[OF refl])
    fix t
    assume "t \<in> set ts"
    with tF t have "funas_term t \<subseteq> F" unfolding funas_args_term_def by auto
    from aliens_subst[OF this]
    show "aliens F (t \<cdot> \<sigma>) = concat (map (\<lambda>x. aliens F (\<sigma> x)) (vars_term_list t))" .
  qed
  finally have id: "aliens_below F (t \<cdot> \<sigma>) = concat (map (\<lambda> t. concat (map (\<lambda> x. aliens F (\<sigma> x)) (vars_term_list t))) ts)" .
  show ?thesis unfolding id unfolding t vars_term_list.simps by (induct ts, auto)
qed


lemma aliens_unary: assumes unary: "\<And> f n. (f,n) \<in> F \<Longrightarrow> n \<le> 1"
  shows "\<exists> a. aliens F t \<in> {[],[a]}"
proof (induct t)
  case Var show ?case by auto
next
  case (Fun f ss)
  let ?n = "length ss"
  show ?case
  proof (cases "(f,?n) \<in> F")
    case False
    then show ?thesis by auto
  next
    case True
    from unary[OF this] have n: "?n \<le> 1" by simp
    from True have id: "aliens F (Fun f ss) = concat (map (aliens F) ss)" (is "?l = ?r") by auto
    show ?thesis
    proof (cases ss)
      case Nil then show ?thesis unfolding id by auto
    next
      case (Cons t ts)
      with n have ss: "ss = [t]" by (cases ts, auto)
      with id have id: "?l = aliens F t" by auto
      with Fun[of t] show ?thesis unfolding id ss by auto
    qed
  qed
qed

lemma aliens_unary_subst: assumes t: "funas_term t \<subseteq> F"
  and unary: "\<And> f n. (f,n) \<in> F \<Longrightarrow> n \<le> 1"
  shows "aliens F (t \<cdot> \<sigma>) = [] \<and> vars_term t = {} \<or> (\<exists> x \<in> vars_term t. vars_term t = {x} \<and> aliens F (t \<cdot> \<sigma>) = aliens F (\<sigma> x))"
proof -
  note aliens = aliens_subst[OF t, of \<sigma>]
  from unary_vars_term_list[OF t unary]
  have "vars_term_list t = [] \<or> (\<exists> x \<in> vars_term t. vars_term_list t = [x])"
    by auto
  then show ?thesis
  proof
    assume empty: "vars_term_list t = []"
    with aliens have "aliens F (t \<cdot> \<sigma>) = []" by auto
    with arg_cong[OF empty, of set]
    show ?thesis by auto
  next
    assume "\<exists> x \<in> vars_term t. vars_term_list t = [x]"
    then obtain x where x: "x \<in> vars_term t" and v: "vars_term_list t = [x]" by auto
    from aliens[unfolded v] have aliens: "aliens F (t \<cdot> \<sigma>) = aliens F (\<sigma> x)" by auto
    then show ?thesis using x arg_cong[OF v, of set] by auto
  qed
qed


lemma aliens_imp_supteq: "a \<in> set (aliens F t) \<Longrightarrow> (t \<unrhd> a)"
proof (induct t)
  case (Fun f ss)
  let ?n = "length ss"
  show ?case
  proof (cases "(f,?n) \<in> F")
    case False
    then show ?thesis using Fun(2) by auto
  next
    case True
    with Fun(2) obtain s where s: "s \<in> set ss" and a: "a \<in> set (aliens F s)" by auto
    from Fun(1)[OF this] have "s \<unrhd> a" .
    with s show ?thesis by auto
  qed
qed auto

lemma aliens_below_imp_supteq: assumes "a \<in> set (aliens_below F t)" shows "(t \<unrhd> a)"
proof (cases t)
  case (Var x)
  with assms show ?thesis by auto
next
  case (Fun f ts)
  with assms obtain t where t: "t \<in> set ts" and a: "a \<in> set (aliens F t)" by auto
  from t aliens_imp_supteq[OF a] show ?thesis unfolding Fun by auto
qed


lemma rstep_unary_sig_aliens:
  assumes step: "(s,t) \<in> rstep R" and FR: "funas_trs R \<subseteq> F"
  and unary: "\<And> f n. (f,n) \<in> F \<Longrightarrow> n \<le> 1"
  and var_cond: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "aliens F t = [] \<or> (\<exists> a b. aliens F s = [a] \<and> aliens F t = [b] \<and> (a,b) \<in> (nrrstep R)\<^sup>*)"
proof -
  let ?a = "aliens F"
  from step obtain C l r \<sigma> where lr: "(l,r) \<in> R" and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  show ?thesis unfolding s t
  proof (induct C)
    case Hole
    from lr FR have l: "funas_term l \<subseteq> F" and r: "funas_term r \<subseteq> F"
      unfolding funas_trs_def funas_rule_def [abs_def] by force+
    from aliens_unary_subst[of r F \<sigma>, OF r unary]
    have choice: "?a (r \<cdot> \<sigma>) = [] \<or> (\<exists> x \<in> vars_term r. ?a (r \<cdot> \<sigma>) = ?a (\<sigma> x))" by auto
    show ?case
    proof (cases "?a (r \<cdot> \<sigma>) = []")
      case True then show ?thesis by simp
    next
      case False
      with choice obtain x where x: "x \<in> vars_term r" and ar: "?a (r \<cdot> \<sigma>) = ?a (\<sigma> x)" by auto
      from aliens_unary[of F "\<sigma> x", OF unary] False obtain a where a: "?a (\<sigma> x) = [a]" unfolding ar[symmetric] by force
      from var_cond[OF lr] x have x: "x \<in> vars_term l" by auto
      with aliens_unary_subst[of l F \<sigma>, OF l unary]
      have al: "?a (l \<cdot> \<sigma>) = ?a (\<sigma> x)" by force
      show ?thesis using al ar unfolding a by auto
    qed
  next
    case (More f bef C aft)
    let ?n = "Suc (length bef + length aft)"
    let ?t = "\<lambda> t. Fun f (bef @ C\<langle>t \<cdot> \<sigma>\<rangle> # aft)"
    let ?x = "Var (SOME x. True) :: ('f,'v)term"
    show ?case
    proof (cases "(f,?n) \<in> F")
      case False
      from False have aliens: "?a (?t l) = [?t l]" "?a (?t r) = [?t r]" by auto
      from nrrstepI[OF lr refl refl, of "More f bef C aft" \<sigma>] have step: "(?t l, ?t r) \<in> nrrstep R" by auto
      show ?thesis unfolding intp_actxt.simps aliens using step by auto
    next
      case True
      from unary[OF True] have ba: "bef = []" "aft = []" by auto
      with True have id: "?a (?t l) = ?a (C\<langle>l \<cdot> \<sigma>\<rangle>)"
                "?a (?t r) = ?a (C\<langle>r \<cdot> \<sigma>\<rangle>)" by auto
      show ?thesis unfolding intp_actxt.simps id using More .
    qed
  qed
qed

lemma rsteps_unary_sig_aliens:
  assumes steps: "(s,t) \<in> (rstep R)\<^sup>*" and FR: "funas_trs R \<subseteq> F"
  and unary: "\<And> f n. (f,n) \<in> F \<Longrightarrow> n \<le> 1"
  and var_cond: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "aliens F t = [] \<or> (\<exists> a b. aliens F s = [a] \<and> aliens F t = [b] \<and> (a,b) \<in> (nrrstep R)\<^sup>*)"
  using steps
proof (induct)
  case base
  from aliens_unary[of F s, OF unary] obtain a where a: "aliens F s \<in> {[], [a]}" by force
  then show ?case by auto
next
  case (step t u)
  let ?a = "aliens F"
  from rstep_unary_sig_aliens[OF step(2) FR unary var_cond]
  have choice: "aliens F u = [] \<or> (\<exists> a b. ?a t = [a] \<and> ?a u = [b] \<and> (a,b) \<in> (nrrstep R)\<^sup>*)" .
  show ?case
  proof (cases "aliens F u = []")
    case True then show ?thesis by auto
  next
    case False
    with choice obtain a b where t: "?a t = [a]" and u: "?a u = [b]" and steps: "(a,b) \<in> (nrrstep R)\<^sup>*" by auto
    from step(3) t obtain c where s: "?a s = [c]" and steps2: "(c,a) \<in> (nrrstep R)\<^sup>*" by auto
    show ?thesis
      by (intro disjI2 exI conjI, rule s, rule u, insert steps steps2, auto)
  qed
qed

context cleaning_const
begin
lemma rstep_sig_alien_nrrstep: fixes R :: "('f,'v)trs"
  assumes step: "(s,t) \<in> rstep R" and FR: "funas_trs R \<subseteq> F"
  shows "(clean_term s,clean_term t) \<in> sig_step F (rstep R) \<or> clean_term s = clean_term t \<and> (\<exists> xs a b ys. aliens F s = xs @ a # ys \<and> aliens F t = xs @ b # ys \<and> (a,b) \<in> nrrstep R)"
proof -
  let ?c = "clean_term"
  let ?a = "aliens F"
  from step obtain C l r \<sigma> where lr: "(l,r) \<in> R" and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  show ?thesis unfolding s t
  proof (induct C)
    case Hole
    let ?\<sigma> = "clean_subst \<sigma>"
    from lr FR have l: "funas_term l \<subseteq> F" and r: "funas_term r \<subseteq> F"
      unfolding funas_trs_def funas_rule_def [abs_def] by force+
    let ?pair = "(?c \<box>\<langle>l\<cdot>\<sigma>\<rangle>, ?c \<box>\<langle>r\<cdot>\<sigma>\<rangle>)"
    have id: "?pair = (l \<cdot> ?\<sigma>, r \<cdot> ?\<sigma>)"
      using clean_subst_apply_term[OF l] clean_subst_apply_term[OF r] by auto
    have rstep: "?pair \<in> (rstep R)" using lr unfolding id by auto
    have "?pair \<in> sig_step F (rstep R)"
      by (rule sig_stepI[OF rstep], auto)
    then show ?case ..
  next
    case (More f bef C aft)
    let ?n = "Suc (length bef + length aft)"
    let ?t = "\<lambda> t. Fun f (bef @ C\<langle>t \<cdot> \<sigma>\<rangle> # aft)"
    let ?x = "Var (SOME x. True) :: ('f,'v)term"
    show ?case
    proof (cases "(f,?n) \<in> F")
      case False
      then have id: "?c (?t l) = ?c (?t r)" using const by simp
      from False have aliens: "?a (?t l) = [] @ ?t l # []" "?a (?t r) = [] @ ?t r # []" by auto
      from nrrstepI[OF lr refl refl, of "More f bef C aft" \<sigma>]
      have step: "(?t l, ?t r) \<in> nrrstep R" by simp
      show ?thesis
        by (rule disjI2, unfold intp_actxt.simps id aliens, insert step, blast)
    next
      case True
      then have id: "?c (?t l) = Fun f (map ?c bef @ ?c (C\<langle>l \<cdot> \<sigma>\<rangle>) # map ?c aft)"
                "?c (?t r) = Fun f (map ?c bef @ ?c (C\<langle>r \<cdot> \<sigma>\<rangle>) # map ?c aft)" by auto
      from True have aliens:
        "?a (?t l) = concat (map ?a bef) @ ?a (C\<langle>l\<cdot>\<sigma>\<rangle>) @ concat (map ?a aft)"
        "?a (?t r) = concat (map ?a bef) @ ?a (C\<langle>r\<cdot>\<sigma>\<rangle>) @ concat (map ?a aft)"
        by auto
      from More show ?thesis
      proof
        assume "(?c (C\<langle>l\<cdot>\<sigma>\<rangle>), ?c (C\<langle>r\<cdot>\<sigma>\<rangle>)) \<in> sig_step F (rstep R)" (is "(?l,?r) \<in> ?SR")
        then have step: "(?l,?r) \<in> rstep R" by auto
        from rstep_ctxt[OF step, of "More f (map ?c bef) \<box> (map ?c aft)"]
          id have rstep: "(?c (?t l), ?c (?t r)) \<in> rstep R" by simp
        show ?thesis
          by (rule disjI1, unfold intp_actxt.simps, rule sig_stepI[OF rstep], (rule funas_term_clean_term)+)
      next
        assume "?c (C\<langle>l\<cdot>\<sigma>\<rangle>) = ?c (C\<langle>r \<cdot> \<sigma>\<rangle>) \<and> (\<exists> xs a b ys. ?a (C\<langle>l\<cdot>\<sigma>\<rangle>) = xs @ a # ys \<and> ?a (C\<langle>r \<cdot> \<sigma>\<rangle>) = xs @ b # ys \<and> (a,b) \<in> nrrstep R)"
        then obtain xs a b ys where id2: "?c (C\<langle>l\<cdot>\<sigma>\<rangle>) = ?c (C\<langle>r \<cdot> \<sigma>\<rangle>)" "?a (C\<langle>l\<cdot>\<sigma>\<rangle>) = xs @ a # ys" "?a (C\<langle>r \<cdot> \<sigma>\<rangle>) = xs @ b # ys" and step: "(a,b) \<in> nrrstep R" by auto
        show ?thesis
          unfolding intp_actxt.simps
          unfolding id aliens
          unfolding id2
          by (rule disjI2, rule conjI[OF refl],
            rule exI[of _ "concat (map ?a bef) @ xs"],
            rule exI[of _ a], rule exI[of _ b],
            rule exI[of _ "ys @ concat (map ?a aft)"], insert step, auto)
      qed
    qed
  qed
qed

lemma rsteps_sig_steps:
  assumes steps: "(s, t) \<in> (rstep R)\<^sup>*" and FR: "funas_trs R \<subseteq> F"
  shows "(clean_term s, clean_term t) \<in> (sig_step F (rstep R))\<^sup>*"
  using steps
proof (induct)
  case (step t u)
  from rstep_sig_alien_nrrstep[OF step(2) FR]
  have "(clean_term t, clean_term u) \<in> (sig_step F (rstep R))\<^sup>*" by auto
  with step(3) show ?case by auto
qed auto

lemma rel_rstep_alien_nrrstep:
  assumes step: "(s,t) \<in> relto (rstep R) (rstep S)" and FR: "funas_trs R \<subseteq> F"
  and FS: "funas_trs S \<subseteq> F"
  shows "(clean_term s,clean_term t) \<in> relto (sig_step F (rstep R)) (sig_step F (rstep S)) \<or> (clean_term s, clean_term t) \<in> (sig_step F (rstep S))\<^sup>* 
  \<and> (\<exists> u v xs a b ys. (s,u) \<in> (rstep S)\<^sup>* \<and> clean_term u = clean_term v \<and> aliens F u = xs @ a # ys \<and> aliens F v = xs @ b # ys \<and> (a,b) \<in> nrrstep R \<and> (v,t) \<in> (rstep S)\<^sup>*)"
proof -
  let ?c = "clean_term"
  let ?R = "sig_step F (rstep R)"
  let ?S = "sig_step F (rstep S)"
  from step obtain u v where su: "(s,u) \<in> (rstep S)\<^sup>*"
    and uv: "(u,v) \<in> rstep R" and vt: "(v,t) \<in> (rstep S)\<^sup>*" by auto
  from rsteps_sig_steps[OF su FS] have csu: "(?c s, ?c u) \<in> ?S\<^sup>*" .
  from rsteps_sig_steps[OF vt FS] have cvt: "(?c v, ?c t) \<in> ?S\<^sup>*" .
  from rstep_sig_alien_nrrstep[OF uv FR]
  show ?thesis
  proof
    assume "(?c u, ?c v) \<in> ?R"
    from csu this cvt
    have "(?c s, ?c t) \<in> ?S\<^sup>* O ?R O ?S\<^sup>*" by auto
    then show ?thesis by simp
  next
    let ?a = "aliens F"
    assume "?c u = ?c v \<and> (\<exists> xs a b ys. ?a u = xs @ a # ys \<and> ?a v = xs @ b # ys \<and> (a,b) \<in> nrrstep R)"
    then obtain xs a b ys where id: "?c u = ?c v" "?a u = xs @ a # ys" "?a v = xs @ b # ys" and step: "(a,b) \<in> nrrstep R" by auto
    from csu id(1) cvt have cst: "(?c s, ?c t) \<in> ?S\<^sup>*" by auto
    show ?thesis
      by (intro disjI2 exI conjI, rule cst, rule su, rule id(1), rule id(2), rule id(3), rule step, rule vt)
  qed
qed
end

lemma sig_ext_relative_rewriting_unary_var_cond:
  fixes R :: "('f,'v)trs"
  assumes unary: "\<And> f n. (f,n) \<in> F \<Longrightarrow> n \<le> 1"
  and FR: "funas_trs R \<subseteq> F"
  and FS: "funas_trs S \<subseteq> F"
  and varcondS: "\<And> l r. (l, r) \<in> S \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and relSN: "SN_rel (sig_step F (rstep R)) (sig_step F (rstep S))"
  shows "SN_rel (rstep R) (rstep S)"
  unfolding SN_rel_defs
proof(rule ccontr)
  let ?rel = "relto (rstep R) (rstep S)"
  let ?nrel = "relto (nrrstep R) (nrrstep S)"
  let ?S = "sig_step F (rstep S)"
  let ?R = "sig_step F (rstep R)"
  let ?srel = "relto ?R ?S"
  from SN_sig_step_imp_wf_trs[OF SN_rel_imp_SN[OF relSN] FR]
  have varcondR: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l" unfolding wf_trs_def by auto
  assume "\<not> SN ?rel"
  from not_SN_imp_Tinf[OF this]
  obtain t0 where t0: "t0 \<in> Tinf ?rel" by auto
  note Tinf = t0
  from t0[unfolded Tinf_def] have nSN: "\<not> SN_on ?rel {t0}" and min: "\<And> s.  s \<lhd> t0 \<Longrightarrow> SN_on ?rel {s}" by auto
  from nSN obtain ts where start: "ts 0 = t0" and step: "\<And> i. (ts i, ts (Suc i)) \<in> ?rel" by auto
  define x where "x = (undefined :: 'v)"
  interpret cleaning_same_var F "\<lambda> _. (Var x) :: ('f,'v)term" "Var x" by (unfold_locales, auto)
  let ?c = "clean_term"
  let ?a = "aliens F"
  let ?ct = "\<lambda> i. ?c (ts i)"
  note alien = rel_rstep_alien_nrrstep[OF step FR FS]
  {
    fix i
    from alien[of i]
    have "(?ct i, ?ct (Suc i)) \<in> ?S\<^sup>* \<union> ?srel" by auto
  } note csteps = this
  {
    fix i
    have "(ts 0, ts i) \<in> (rstep (R \<union> S))\<^sup>*"
    proof (induct i)
      case (Suc i)
      have "(ts i, ts (Suc i)) \<in> (rstep (R \<union> S))\<^sup>*"
        by (rule set_mp[OF _ step[of i]], unfold rstep_union, regexp)
      with Suc show ?case by auto
    qed simp
  } note union_steps = this
  {
    fix s t T
    assume T: "T \<subseteq> R \<union> S" and steps: "(s,t) \<in> (rstep T)\<^sup>*"
    from T FR FS have FT: "funas_trs T \<subseteq> F" unfolding funas_trs_def by blast
    from varcondS varcondR T have vc: "\<And> l r. (l,r) \<in> T \<Longrightarrow> vars_term r \<subseteq> vars_term l" by force
    from rsteps_unary_sig_aliens[OF steps FT unary vc]
    have disj: "?a t = [] \<or> (\<exists> a b. ?a s = [a] \<and> ?a t = [b] \<and> (a,b) \<in> (nrrstep T)\<^sup>*)" by auto
  } note alien_steps = this
  from relSN have SN: "SN_on ?srel {?ct 0}" unfolding SN_rel_defs SN_on_def by auto
  have compat: "?S\<^sup>* O ?srel \<subseteq> ?srel" by regexp
  from non_strict_ending[of ?ct, OF allI[OF csteps] compat SN]
  obtain j where not_srel: "\<And> i. i \<ge> j \<Longrightarrow> (?ct i, ?ct (Suc i)) \<notin> ?srel" by auto
  let ?h = "\<lambda> i. hd (?a (ts i))"
  {
    fix i
    assume ij: "i \<ge> j"
    from alien[of i] not_srel[OF this] obtain u v xs a b ys
      where steps1: "(ts i, u) \<in> (rstep S)\<^sup>*"
      and u: "?a u = xs @ a # ys"
      and v: "?a v = xs @ b # ys"
      and step: "(a,b) \<in> nrrstep R"
      and steps2: "(v,ts (Suc i)) \<in> (rstep S)\<^sup>*" by auto
    from aliens_unary[of F u,OF unary] obtain a' where u': "?a u \<in> {[],[a']}" by force
    with u have u: "?a u = [a]" by (cases xs, auto)
    from aliens_unary[of F v,OF unary] obtain b' where v': "?a v \<in> {[],[b']}" by force
    with v have v: "?a v = [b]" by (cases xs, auto)
    from alien_steps[OF _ steps1, unfolded u] obtain a' where a': "?a (ts i) = [a']"
      and a'a: "(a',a) \<in> (nrrstep S)\<^sup>*" by auto
    from ij have "Suc i \<ge> j" by auto
    from alien[of "Suc i"] not_srel[OF this] obtain uu xxs aa yys
      where steps3: "(ts (Suc i), uu) \<in> (rstep S)\<^sup>*"
      and uu: "?a uu = xxs @ aa # yys" by auto
    from alien_steps[OF _ steps3, unfolded uu] obtain b' where b': "?a (ts (Suc i)) = [b']" by auto
    from alien_steps[OF _ steps2, unfolded b' v] have bb': "(b,b') \<in> (nrrstep S)\<^sup>*" by auto
    from a'a step bb' have "(a',b') \<in> ?nrel" by auto
    with b' a' have "(?h i, ?h (Suc i)) \<in> ?nrel \<and> (\<exists> a. ?a (ts i) = [a])" by auto
  } note seq = this
  have nSN: "\<not> SN_on ?nrel {?h j}" unfolding SN_on_def not_not
    by (rule exI[of _ "\<lambda> i. ?h (j + i)"], insert seq, auto)
  from seq[of j] obtain aj where aj: "?a (ts j) = [aj]" by auto
  from alien_steps[OF _ union_steps[of j], unfolded aj] obtain a0 where
    a0: "?a (ts 0) = [a0]" and "(a0,aj) \<in> (nrrstep (R \<union> S))\<^sup>*" by auto
  then have steps: "(a0,?h j) \<in> (nrrstep (R \<union> S))\<^sup>*" unfolding aj by auto
  from steps_preserve_SN_on_relto[OF steps[unfolded nrrstep_union]] nSN
  have nSN: "\<not> SN_on ?nrel {a0}" by auto
  from a0 have "a0 \<in> set (?a (ts 0))" by auto
  from aliens_imp_supteq[OF this] have supteq: "ts 0 \<unrhd> a0" by auto
  from Tinf_imp_SN_nr_first_root_step_rel[of t0 False "{}" S "{}" R, simplified, OF Tinf]
  have SN: "SN_on ?nrel {ts 0}" unfolding start ..
  have ctxt: "ctxt.closed ?nrel" by blast 
  from ctxt_closed_SN_on_subt [OF ctxt SN supteq]
  have SN: "SN_on ?nrel {a0}" .
  with nSN show False ..
qed

locale cleaning_binary = 
  fixes F :: "'f sig"
  and g :: 'f
  and n :: nat
  assumes gn: "(g, Suc (Suc n)) \<in> F"
begin

fun comb :: "('f,'v)term list \<Rightarrow> ('f,'v)term" where 
  "comb [] = Var undefined"
| "comb (s # ss) = Fun g (s # comb ss # replicate n (Var undefined))"

lemma funas_term_comb: "(\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F) \<Longrightarrow> funas_term (comb ts) \<subseteq> F"
  by (induct ts, auto simp: gn)

fun clean_comb_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
where 
  "clean_comb_term (Var x) = Var x"
| "clean_comb_term (Fun f ts) =
    (if (f, length ts) \<in> F then Fun f (map clean_comb_term ts)
    else comb (map clean_comb_term ts))"

lemma funas_term_clean_comb_term: "funas_term (clean_comb_term t) \<subseteq> F"
proof (induct t)
  case (Fun f ts)
  then show ?case 
  proof (cases "(f,length ts) \<in> F")
    case False
    then have id: "clean_comb_term (Fun f ts) = comb (map clean_comb_term ts)" by simp
    show ?thesis unfolding id
      by (rule funas_term_comb, insert Fun, auto)
  qed auto
qed auto

fun clean_comb_subst :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
where
  "clean_comb_subst \<sigma> = clean_comb_term \<circ> \<sigma>"

lemma clean_comb_subst_apply_term[simp]:
  assumes "funas_term t \<subseteq> F"
  shows "clean_comb_term (t \<cdot> \<sigma>) = t \<cdot> (clean_comb_subst \<sigma>)"
using assms proof (induct t rule: term.induct)
  case (Fun f ss)
  from Fun(2) have "\<forall>t\<in>set ss. funas_term t \<subseteq> F" by auto
  with Fun have IH: "\<And>t. t \<in> set ss \<Longrightarrow> clean_comb_term (t \<cdot> \<sigma>) = t \<cdot> (clean_comb_subst \<sigma>)" by best
  with Fun show ?case by auto
qed simp

lemma rstep_sig_step:
  fixes R :: "('f, 'v) trs"
  assumes step: "(s, t) \<in> rstep R" and FR: "funas_trs R \<subseteq> F"
  shows "(clean_comb_term s, clean_comb_term t) \<in> sig_step F (rstep R)"
proof (rule sig_stepI[OF _ funas_term_clean_comb_term funas_term_clean_comb_term])
  let ?c = "clean_comb_term"
  let ?const = "Var undefined :: ('f,'v)term"
  from step obtain C l r \<sigma> where lr: "(l,r) \<in> R" and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  show "(?c s, ?c t) \<in> rstep R" unfolding s t
  proof (induct C)
    case Hole
    let ?\<sigma> = "clean_comb_subst \<sigma>"
    from lr FR have l: "funas_term l \<subseteq> F" and r: "funas_term r \<subseteq> F"
      unfolding funas_trs_def funas_rule_def [abs_def] by force+
    let ?pair = "(?c \<box>\<langle>l\<cdot>\<sigma>\<rangle>, ?c \<box>\<langle>r\<cdot>\<sigma>\<rangle>)"
    have id: "?pair = (l \<cdot> ?\<sigma>, r \<cdot> ?\<sigma>)"
      using clean_comb_subst_apply_term[OF l] clean_comb_subst_apply_term[OF r] by auto
    then show "?pair \<in> (rstep R)" using lr unfolding id by auto
  next
    case (More f bef C aft)
    let ?n = "Suc (length bef + length aft)"
    let ?t = "\<lambda> t. (More f bef C aft)\<langle>t \<cdot> \<sigma>\<rangle>"
    show ?case
    proof (cases "(f,?n) \<in> F")
      case True
      let ?C = "More f (map ?c bef) \<box> (map ?c aft)"
      from True have id: "?c (?t l) = ?C\<langle>?c (C\<langle>l \<cdot> \<sigma>\<rangle>)\<rangle>" "?c (?t r) = ?C\<langle>?c (C\<langle>r \<cdot> \<sigma>\<rangle>)\<rangle>"
        by auto
      from rstep_ctxt[OF More]
      show ?thesis unfolding id .
    next
      case False
      obtain a b where a: "a = map ?c aft" and b: "b = map ?c bef" by auto
      obtain ll rr where ll: "ll = ?c (C\<langle>l \<cdot> \<sigma>\<rangle>)" and rr: "rr = ?c (C\<langle>r \<cdot> \<sigma>\<rangle>)" by auto
      from More have step: "(ll,rr) \<in> rstep R" unfolding ll rr .
      from False have id: "?c (?t l) = comb (b @ ll # a)"
        "?c (?t r) = comb (b @ rr # a)" unfolding a b ll rr by auto
      let ?rep = "replicate n ?const"
      show ?thesis unfolding id
      proof (induct b)
        case Nil        
        show ?case using rstep_ctxt[OF step, of "More g [] \<box> (comb a # ?rep)"]
          by simp
      next
        case (Cons b bs)
        show ?case using rstep_ctxt[OF Cons, of "(More g [b] \<box> ?rep)"]
          by simp
      qed
    qed
  qed
qed
end

lemma sig_ext_relative_rewriting_non_unary:
  fixes R :: "('f, 'v) trs"
  assumes non_unary: "\<exists> f n. (f, n) \<in> F \<and> n > 1"
  and FR: "funas_trs R \<subseteq> F"
  and FS: "funas_trs S \<subseteq> F"
  and relSN: "SN_rel (sig_step F (rstep R)) (sig_step F (rstep S))"
  shows "SN_rel (rstep R) (rstep S)"
proof -
  fix x
  from non_unary obtain f n where fn: "(f, n) \<in> F" and n: "n > 1" by auto
  from n have "n = Suc (Suc (n - 2))" by auto
  with fn have "(f, Suc (Suc (n - 2))) \<in> F" by simp
  then obtain n where Fn: "(f, Suc (Suc n)) \<in> F" by auto
  interpret cleaning_binary F f n
    by (unfold_locales, insert Fn, auto)
  let ?c = "clean_comb_term"
  let ?R = "sig_step F (rstep R)"
  let ?S = "sig_step F (rstep S)"
  let ?B = "(?R \<union> ?S)\<^sup>*"
  show ?thesis
  proof (rule SN_rel_map[OF relSN, of _ ?c])
    fix s t
    assume "(s,t) \<in> rstep R"
    from rstep_sig_step[OF this FR]
    show "(?c s, ?c t) \<in> ?B O ?R O ?B" by auto
  next
    fix s t
    assume "(s,t) \<in> rstep S"
    from rstep_sig_step[OF this FS]
    show "(?c s, ?c t) \<in> ?B" by auto
  qed
qed

lemma sig_ext_relative_rewriting_var_cond:
  fixes R :: "('f,'v)trs"
  assumes varcondS: "\<And> l r. (l,r) \<in> S \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and FR: "funas_trs R \<subseteq> F"
  and FS: "funas_trs S \<subseteq> F"
  and relSN: "SN_rel (sig_step F (rstep R)) (sig_step F (rstep S))"
  shows "SN_rel (rstep R) (rstep S)"
proof (cases "\<forall> f n. (f,n) \<in> F \<longrightarrow> n \<le> 1")
  case True
  from sig_ext_relative_rewriting_unary_var_cond[OF _ FR FS varcondS relSN]
    True show ?thesis by auto
next
  case False
  then have "\<exists> f n. (f,n) \<in> F \<and> n > 1" by force
  from sig_ext_relative_rewriting_non_unary[OF this FR FS relSN]
  show ?thesis .
qed

(* note that the variable condition on S or non-unary signatures are essential,
   i.e., signature extensions are unsound for unary relative rewriting:
   e.g. take R = { a \<rightarrow> b } and S = { a \<rightarrow> x } and F = {a,b}
   or R = { f(a) \<rightarrow> b } and S = { f(a) \<rightarrow> x } and F = {f,a,b}
*)
lemma sig_ext_relative_rewriting_unsound:
  fixes a b :: "'f"
  assumes ab: "a \<noteq> b"
  shows "\<exists> (R :: ('f,'v)trs) S. 
    SN_rel (sig_step (funas_trs (R \<union> S)) (rstep R)) (sig_step (funas_trs (R \<union> S)) (rstep S)) \<and> 
  \<not> SN_rel (rstep R) (rstep S)"
proof -
  let ?R = "{(Fun a [], Fun b [])} :: ('f,'v)trs"
  let ?S = "{(Fun a [], Var undefined)} :: ('f,'v)trs"
  let ?F = "{(a,0),(b,0)}"
  let ?ss = "sig_step ?F"
  let ?sR = "?ss (rstep ?R)"
  let ?sS = "?ss (rstep ?S)"
  have F: "funas_trs (?R \<union> ?S) = ?F"
    unfolding funas_trs_def funas_rule_def [abs_def] by auto
  show ?thesis
  proof (rule exI[of _ ?R], rule exI[of _ ?S], unfold F, rule conjI)
    show "SN_rel ?sR ?sS" unfolding SN_rel_on_conv
    proof (rule ccontr)
      assume "\<not> SN_rel_alt ?sR ?sS"
      from this[unfolded SN_rel_on_alt_def]
      obtain f where steps: "\<And> i. (f i, f (Suc i)) \<in> ?sR \<union> ?sS"
        and R: "INFM i. (f i, f (Suc i)) \<in> ?sR" by blast
      from R[unfolded INFM_nat_le] obtain i where i: "(f i, f (Suc i)) \<in> ?sR" by auto
      from sig_stepE[OF this] have fi: "funas_term (f i) \<subseteq> ?F"
        and step: "(f i, f (Suc i)) \<in> rstep ?R" by auto
      from step obtain C l r \<sigma> where lr: "(l,r) \<in> ?R" and i: "f i = C\<langle>l\<cdot>\<sigma>\<rangle>" and si: "f (Suc i) = C\<langle>r \<cdot> \<sigma>\<rangle>" by force
      then have i: "f i = C\<langle>Fun a []\<rangle>" and si: "f (Suc i) = C\<langle>Fun b []\<rangle>" by auto
      from fi i have "C = \<box>" by (cases C, auto)
      with si have si: "f (Suc i) = Fun b []" by auto
      from steps[of "Suc i", unfolded si] have "(Fun b [], f (Suc (Suc i))) \<in> rstep (?R \<union> ?S)" unfolding sig_step_def by auto
      then obtain C l r \<sigma>
        where lr: "(l,r) \<in> ?R \<union> ?S" and si: "Fun b [] = C\<langle>l\<cdot>\<sigma>\<rangle>" and "f (Suc (Suc i)) = C\<langle>r\<cdot>\<sigma>\<rangle>" by force
      from lr  have l: "l = Fun a []" by auto
      from si[unfolded l] have "Fun b [] = Fun a []" by (cases C, auto)
      with ab show False by simp
    qed
  next
    have "\<not> wf_reltrs ?R ?S" by simp
    then show "\<not> SN_rel (rstep ?R) (rstep ?S)"
      using SN_rel_imp_wf_reltrs[of ?R ?S] by auto
  qed
qed

definition QF_cond :: "'f sig \<Rightarrow> ('f,'v)terms \<Rightarrow> bool"
where
  "QF_cond F Q \<longleftrightarrow> (\<forall> fn q. q \<in> Q \<longrightarrow> root q = Some fn \<longrightarrow> fn \<in> F \<longrightarrow> funas_term q \<subseteq> F)"

locale cleaning_innermost =
  fixes F :: "'f sig"
  and   c :: "('f,'v)term \<Rightarrow> 'v"
  assumes c_inj: "inj c"
begin

fun
  clean_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "clean_term (Var y) = Var (c (Var y))" |
  "clean_term (Fun f ts) =
    (if (f, length ts) \<in> F then Fun f (map clean_term ts)
     else Var (c (Fun f ts)))"

fun
  clean_subst :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
where
  "clean_subst \<sigma> = (clean_term \<circ> \<sigma>)"

definition unclean_subst :: "('f, 'v) subst"
where
  "unclean_subst = the_inv c"

lemma funas_term_clean_term[simp]: "funas_term (clean_term t) \<subseteq> F"
  by (induct t) auto

lemma unclean_subst: "clean_term t \<cdot> unclean_subst = t"
proof -
  {
    fix t
    have "Var (c t) \<cdot> unclean_subst = t" unfolding unclean_subst_def
      using the_inv_f_f[OF c_inj] by auto
  } note main = this
  show ?thesis
    by (induct t, insert main, auto simp: o_def intro: map_idI)
qed


lemma clean_subst_apply_term[simp]:
  assumes "funas_term t \<subseteq> F"
  shows "clean_term (t \<cdot> \<sigma>) = t \<cdot> (clean_subst \<sigma>)"
using assms proof (induct t rule: term.induct)
  case (Var x) show ?case by simp
next
  case (Fun f ss)
  from Fun(2)
    have "\<forall>t\<in>set ss. funas_term t \<subseteq> F" by auto
  with Fun have IH: "\<And>t. t \<in> set ss \<Longrightarrow> clean_term (t \<cdot> \<sigma>) = t \<cdot> (clean_subst \<sigma>)" by best
  with Fun show ?case by auto
qed

lemma clean_NF_term: assumes NF: "t \<in> NF_terms Q"
  shows "clean_term t \<in> NF_terms Q"
proof -
  obtain u where uu: "u = clean_term t" by auto
  from unclean_subst[of t] uu have u: "t = u \<cdot> unclean_subst" by simp
  from NF_instance[OF NF[unfolded u]] have "u \<in> NF_terms Q" .
  then show ?thesis unfolding uu .
qed

lemma clean_NF_subst: assumes nfs: "NF_subst nfs (l,r) \<sigma> Q"
  shows "NF_subst nfs (l,r) (clean_subst \<sigma>) Q"
proof
  fix x
  assume nfs and x: "x \<in> vars_term l \<or> x \<in> vars_term r"
  then have "\<sigma> x \<in> \<sigma> ` vars_rule (l,r)" unfolding vars_rule_def by auto
  with nfs[unfolded NF_subst_def, rule_format, OF \<open>nfs\<close>]
  have NF: "\<sigma> x \<in> NF_terms Q" by auto
  from clean_NF_term[OF this]
  show "clean_subst \<sigma> x \<in> NF_terms Q" by simp
qed

lemma clean_qrstep: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and wwf: "wwf_qtrs Q R" (* essentially, we need vars(r) \<subseteq> vars(l) *)
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> qrstep nfs Q R"
  shows "(clean_term s, clean_term t) \<in> qrstep nfs Q R \<and> set (aliens F t) \<subseteq> NF_terms Q"
proof -
  let ?QR = "qrstep nfs Q R"
  let ?Q = "NF_terms Q"
  from step obtain C l r \<sigma> where lr: "(l,r) \<in> R" and NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> ?Q"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  from lr F have l: "funas_term l \<subseteq> F" and r: "funas_term r \<subseteq> F"
    unfolding funas_trs_def funas_rule_def [abs_def] by force+
  note clr = clean_subst_apply_term[OF l] clean_subst_apply_term[OF r]
  from only_applicable_rules[OF NF, of r] wwf lr have vars: "vars_term r \<subseteq> vars_term l"
    unfolding wwf_qtrs_def by auto
  note NF_conv = NF_terms_args_conv
  let ?\<sigma> = "clean_subst \<sigma>"
  show ?thesis using aliens unfolding s t
  proof (induct C)
    case Hole
    show ?case unfolding intp_actxt.simps clr
    proof
      show "(l \<cdot> ?\<sigma>, r \<cdot> ?\<sigma>) \<in> ?QR"
      proof (rule qrstepI[OF _ lr, of _ _ _ \<box>])
        show "\<forall> u \<lhd> l \<cdot> ?\<sigma>. u \<in> ?Q"
          unfolding clr[symmetric]
          unfolding NF_conv[symmetric]
        proof
          fix u
          assume u: "u \<in> set (args (clean_term (l \<cdot> \<sigma>)))"
          then obtain f ls where l\<sigma>: "l \<cdot> \<sigma> = Fun f ls" by (cases "l \<cdot> \<sigma>", auto)
          from u[unfolded l\<sigma>] obtain la where la: "la \<in> set ls"
            and u: "u = clean_term la" by (cases "(f,length ls) \<in> F", auto)
          from NF[unfolded NF_conv[symmetric] l\<sigma>] la have la: "la \<in> ?Q" by auto
          from clean_NF_term[OF this] show "u \<in> ?Q" unfolding u .
        qed
      next
        show "NF_subst nfs (l,r) (clean_subst \<sigma>) Q"
          by (rule clean_NF_subst[OF nfs])
      qed auto
    next
      from Hole[unfolded intp_actxt.simps] vars
      show "set (aliens F (r \<cdot> \<sigma>)) \<subseteq> NF_terms Q"
        unfolding aliens_subst[OF l] aliens_subst[OF r] by auto
    qed
  next
    case (More f bef C aft)
    let ?n = "Suc (length bef + length aft)"
    let ?C = "More f bef C aft"
    show ?case
    proof (cases "(f,?n) \<in> F")
      case False
      with More(2) have "?C\<langle>l\<cdot>\<sigma>\<rangle> \<in> ?Q" by auto
      with inn have NF: "?C\<langle>l\<cdot>\<sigma>\<rangle> \<in> NF_trs R" by auto
      from rstepI[OF lr, of _ ?C \<sigma>] have "(?C\<langle>l\<cdot>\<sigma>\<rangle>,?C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R" by simp
      with NF have False by auto
      then show ?thesis by auto
    next
      case True
      from True More(2) have "set (aliens F C\<langle>l\<cdot>\<sigma>\<rangle>) \<subseteq> ?Q" by auto
      from More(1)[OF this] have step: "(clean_term C\<langle>l\<cdot>\<sigma>\<rangle>, clean_term C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> qrstep nfs Q R"
        and aliens: "set (aliens F C\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> ?Q" by auto
      from qrstep.ctxt[OF step, of "More f (map clean_term bef) \<box> (map clean_term aft)"] True
      have step: "(clean_term ?C\<langle>l\<cdot>\<sigma>\<rangle>, clean_term ?C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> qrstep nfs Q R" by simp
      from True More(2) aliens have aliens: "set (aliens F ?C\<langle>r\<cdot>\<sigma>\<rangle>) \<subseteq> ?Q" by auto
      from step aliens
      show ?thesis ..
    qed
  qed
qed

lemma clean_qrstep_sig_step: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and wwf: "wwf_qtrs Q R"
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> qrstep nfs Q R"
  shows "(clean_term s, clean_term t) \<in> sig_step F (qrstep nfs Q R) \<and> set (aliens F t) \<subseteq> NF_terms Q"
proof -
  from clean_qrstep[OF inn F wwf aliens step]
  show ?thesis unfolding sig_step_def by auto
qed

lemma clean_qrsteps_sig_steps: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and wwf: "wwf_qtrs Q R"
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(clean_term s, clean_term t) \<in> (sig_step F (qrstep nfs Q R))\<^sup>* \<and> set (aliens F t) \<subseteq> NF_terms Q"
  using step
proof (induct)
  case base then show ?case using aliens by auto
next
  case (step t u)
  let ?c = "clean_term"
  from step(3) have steps: "(?c s, ?c t) \<in> (sig_step F (qrstep nfs Q R))\<^sup>*" and aliens: "set (aliens F t) \<subseteq> NF_terms Q"
    by auto
  from steps clean_qrstep_sig_step[OF inn F wwf aliens step(2)] show ?case by auto
qed

lemma clean_qrsteps: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and wwf: "wwf_qtrs Q R"
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(clean_term s, clean_term t) \<in> (qrstep nfs Q R)\<^sup>* \<and> set (aliens F t) \<subseteq> NF_terms Q"
  using clean_qrsteps_sig_steps[OF inn F wwf aliens step] rtrancl_mono[of "sig_step F (qrstep nfs Q R)" "qrstep nfs Q R"] unfolding sig_step_def by auto

lemma clean_rel_qrsteps_sig_step: assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> S)"
  and F: "funas_trs (R \<union> S) \<subseteq> F"
  and wwf: "wwf_qtrs Q (R \<union> S)"
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> relto (qrstep nfs Q R) (qrstep nfs Q S)"
  shows "(clean_term s, clean_term t) \<in> relto (sig_step F (qrstep nfs Q R)) (sig_step F (qrstep nfs Q S)) \<and> set (aliens F t) \<subseteq> NF_terms Q"
proof -
  let ?QR = "qrstep nfs Q R"
  let ?QS = "qrstep nfs Q S"
  let ?QRS = "sig_step F (qrstep nfs Q R)"
  let ?QSS = "sig_step F (qrstep nfs Q S)"
  let ?Q = "NF_terms Q"
  let ?c = clean_term
  from inn have innR: "?Q \<subseteq> NF_trs R" and innS: "?Q \<subseteq> NF_trs S" unfolding NF_trs_union by auto
  from F have FR: "funas_trs R \<subseteq> F" and FS: "funas_trs S \<subseteq> F" unfolding funas_trs_union by auto
  from wwf have wwfR: "wwf_qtrs Q R" and wwfS: "wwf_qtrs Q S" unfolding wwf_qtrs_def by auto
  note qrsteps = clean_qrsteps_sig_steps[OF innS FS wwfS]
  from step obtain u v where
    su: "(s,u) \<in> ?QS\<^sup>*" and uv: "(u,v) \<in> ?QR" and vt: "(v,t) \<in> ?QS\<^sup>*" by auto
  from qrsteps[OF aliens su] have su: "(?c s, ?c u) \<in> ?QSS\<^sup>*" and aliens: "set (aliens F u) \<subseteq> ?Q" by auto
  from clean_qrstep_sig_step[OF innR FR wwfR aliens uv] have uv: "(?c u, ?c v) \<in> ?QRS" and aliens: "set (aliens F v) \<subseteq> ?Q" by auto
  from qrsteps[OF aliens vt] have vt: "(?c v, ?c t) \<in> ?QSS\<^sup>*" and aliens: "set (aliens F t) \<subseteq> ?Q" by auto
  from su uv vt aliens show ?thesis by auto
qed

lemma clean_rel_qrsteps:
  assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> S)"
    and F: "funas_trs (R \<union> S) \<subseteq> F"
    and wwf: "wwf_qtrs Q (R \<union> S)"
    and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
    and step: "(s,t) \<in> relto (qrstep nfs Q R) (qrstep nfs Q S)"
  shows "(clean_term s, clean_term t) \<in> relto (qrstep nfs Q R) (qrstep nfs Q S) \<and> set (aliens F t) \<subseteq> NF_terms Q"
proof -
  from clean_rel_qrsteps_sig_step[OF inn F wwf aliens step]
  show ?thesis using relto_mono[of "sig_step F (qrstep nfs Q R)" "qrstep nfs Q R" "sig_step F (qrstep nfs Q S)" "qrstep nfs Q S"] unfolding sig_step_def by auto
qed

lemma clean_SN_rel: fixes Q :: "('f,'v)terms"
  assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> S)"
  and F: "funas_trs (R \<union> S) \<subseteq> F"
  and wwf: "wwf_qtrs Q (R \<union> S)"
  and SN_rel: "SN_rel (sig_step F (qrstep nfs Q R)) (sig_step F (qrstep nfs Q S))"
  shows "SN_rel (qrstep nfs Q R) (qrstep nfs Q S)"
proof -
  let ?R = "qrstep nfs Q R"
  let ?S = "qrstep nfs Q S"
  let ?Q = "NF_terms Q"
  let ?RS = "relto (?R) (?S)"
  let ?RSs = "relto (sig_step F ?R) (sig_step F ?S)"
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    from this[unfolded SN_rel_defs]
    obtain t where tinf: "t \<in> Tinf ?RS" unfolding Tinf_SN_conv[symmetric] by auto
    from Tinf_imp_SN_nr_first_root_step_rel[OF tinf] obtain s t
      where st: "(s,t) \<in> rqrstep nfs Q R \<union> rqrstep nfs Q S" and nSN: "\<not> SN_on ?RS {t}" by auto
    from st have st: "(s,t) \<in> rqrstep nfs Q (R \<union> S)" by auto
    then obtain l r \<sigma> where NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> ?Q"
        and lr: "(l,r) \<in> R \<union> S" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" ..
    from s NF have NF: "\<And> u. u \<lhd> s \<Longrightarrow> u \<in> ?Q"  by auto
    {
      fix a
      assume a: "a \<in> set (aliens F s)"
      from aliens_imp_supteq[OF this] have sa: "s \<unrhd> a" by auto
      from sa have disj: "s \<rhd> a \<or> a = s" by auto
      {
        assume "a = s"
        with s have al: "a = l \<cdot> \<sigma>" by auto
        from wwf_qtrs_imp_left_fun[OF wwf lr] obtain f ls where l: "l = Fun f ls" by auto
        let ?f = "(f,length ls)"
        from F lr[unfolded l] have f: "?f \<in> F"
          unfolding funas_trs_def funas_rule_def [abs_def] by force
        then have "the (root a) \<in> F" unfolding al l by simp
        with aliens_root[OF a] have False by auto
      }
      with disj have "a \<lhd> s" by auto
      from NF[OF this] have "a \<in> ?Q" .
    }
    then have as: "set (aliens F s) \<subseteq> ?Q" by blast
    from st have st: "(s,t) \<in> qrstep nfs Q (R \<union> S)" unfolding qrstep_iff_rqrstep_or_nrqrstep ..
    from clean_qrstep[OF inn F wwf as st] have at: "set (aliens F t) \<subseteq> ?Q" ..
    from nSN obtain f where t: "t = f 0" and steps: "\<And> i. (f i, f (Suc i)) \<in> ?RS" by auto
    note conv = clean_rel_qrsteps_sig_step[OF inn F wwf]
    let ?c = "\<lambda> i. clean_term (f i)"
    {
      fix i
      have "(?c i, ?c (Suc i)) \<in> ?RSs \<and> set (aliens F (f (Suc i))) \<subseteq> ?Q"
      proof (induct i)
        case 0
        show ?case by (rule conv[OF _ steps[of 0]], insert t at, auto)
      next
        case (Suc i)
        show ?case by (rule conv[OF _ steps[of "Suc i"]], insert Suc, auto)
      qed
      then have "(?c i, ?c (Suc i)) \<in> ?RSs" ..
    }
    then have "\<not> SN ?RSs"
      by  (rule steps_imp_not_SN)
    with SN_rel show False unfolding SN_rel_defs by simp
  qed
qed

lemma clean_ichain: (* this lemma can be used to show completeness of Q-reduction *)
  assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> Rw)"
  and FR: "funas_trs (R \<union> Rw) \<subseteq> F"
  and FP: "funas_trs (P \<union> Pw) \<subseteq> F"
  and wwf: "wwf_qtrs Q (R \<union> Rw)"
  and vars: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  and ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows "ichain (nfs,m,P,Pw,Q,R,Rw) s t (\<lambda> i. clean_subst (\<sigma> i))"
proof -
  let ?\<sigma> = "\<lambda> i. clean_subst (\<sigma> i)"
  let ?c = clean_term
  note ichain = ichain[unfolded ichain.simps]
  let ?R = "qrstep nfs Q R"
  let ?Rw = "qrstep nfs Q (R \<union> Rw)"
  let ?rel = "?Rw\<^sup>* O ?R O ?Rw\<^sup>*"
  let ?Q = "NF_terms Q"
  from ichain have P: "\<And> i. (s i, t i) \<in> P \<union> Pw" by auto
  from ichain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?Rw\<^sup>*" by auto
  from ichain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> ?Q" by auto
  from ichain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
  from ichain have inf: "INFM i. (s i, t i) \<in> P \<or> (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?rel"
    unfolding INFM_disj_distrib by simp
  {
    fix i
    from P[of i] FP  have F: "funas_term (s i) \<subseteq> F" "funas_term (t i) \<subseteq> F"
      unfolding funas_trs_def funas_rule_def [abs_def] by force+
  } note F = this
  note subst = clean_subst_apply_term[OF F(1)] clean_subst_apply_term[OF F(2)]
  note qrsteps = clean_qrsteps[OF inn FR wwf, THEN conjunct1]
  from inn have innB: "?Q \<subseteq> NF_trs (R \<union> (R \<union> Rw))" by auto
  from FR have FRB: "funas_trs (R \<union> (R \<union> Rw)) \<subseteq> F" by auto
  from wwf have wwfB: "wwf_qtrs Q (R \<union> (R \<union> Rw))" by auto
  note qrelsteps = clean_rel_qrsteps[OF innB FRB wwfB, THEN conjunct1]
  {
    fix i
    from NF_subterm[OF NF[of i] aliens_imp_supteq]
      have "set (aliens F (s i \<cdot> \<sigma> i)) \<subseteq> ?Q" by auto
    then have "set (aliens F (t i \<cdot> \<sigma> i)) \<subseteq> ?Q"
      unfolding aliens_subst[OF F(1)]
      unfolding aliens_subst[OF F(2)] using vars[OF P[of i]] by auto
  } note aliens = this
  show ?thesis unfolding ichain.simps
  proof (intro conjI allI, rule P)
    fix i
    from qrsteps[OF aliens steps[of i]]
    show "(t i \<cdot> ?\<sigma> i, s (Suc i) \<cdot> ?\<sigma> (Suc i)) \<in> ?Rw\<^sup>*" unfolding subst .
    from NF[of i] have "?c (s i \<cdot> \<sigma> i) \<cdot> unclean_subst \<in> ?Q" unfolding unclean_subst .
    from NF_instance[OF this[unfolded subst]]
    show "s i \<cdot> ?\<sigma> i \<in> ?Q" .
  next
    let ?r = "\<lambda> i. (t i \<cdot> ?\<sigma> i, s (Suc i) \<cdot> ?\<sigma> (Suc i)) \<in> ?rel"
    show "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. ?r i)"
      unfolding INFM_disj_distrib[symmetric]
      unfolding INFM_nat_le
    proof
      fix m
      from inf[unfolded INFM_nat_le, rule_format, of m]
      obtain n where n: "n \<ge> m" and disj: "(s n, t n) \<in> P \<or> (t n \<cdot> \<sigma> n, s (Suc n) \<cdot> \<sigma> (Suc n)) \<in> ?rel" by auto
      show "\<exists> n \<ge> m. (s n, t n) \<in> P \<or> ?r n"
      proof (intro exI conjI, rule n)
        from disj qrelsteps[OF aliens[of n], of "s (Suc n) \<cdot> \<sigma> (Suc n)"]
        show "(s n, t n) \<in> P \<or> ?r n" unfolding subst by blast
      qed
    qed
  next
    fix i
    show "NF_subst nfs (s i, t i) (?\<sigma> i) Q"
      by (rule clean_NF_subst[OF nfs])
  qed
qed

fun
  clean_term_below :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "clean_term_below (Fun f ts) = Fun f (map clean_term ts)"
| "clean_term_below (Var x) = (Var x)"

lemma unclean_subst_below: assumes "is_Fun t" shows
  "clean_term_below t \<cdot> unclean_subst = t"
proof -
  from assms obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  have "?thesis = (map (\<lambda> t. clean_term t \<cdot> unclean_subst) ts = ts)" unfolding t by (simp add: comp_def)
  also have "..." using unclean_subst by (induct ts, auto)
  finally show ?thesis by simp
qed

lemma funas_args_term_clean_term_below[simp]: "funas_args_term (clean_term_below t) \<subseteq> F"
proof (cases t)
  case Var then show ?thesis by (simp add: funas_args_term_def)
next
  case (Fun f ts)
  from funas_term_clean_term show ?thesis unfolding Fun clean_term_below.simps funas_args_term_def
    by (simp, blast intro: funas_term_clean_term)
qed

lemma clean_subst_apply_term_below:
  assumes tF: "funas_args_term t \<subseteq> F"
    and t: "is_Fun t"
  shows "clean_term_below (t \<cdot> \<sigma>) = t \<cdot> (clean_subst \<sigma>)"
proof -
  from t obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  {
    fix t
    assume mem: "t \<in> set ts"
    have "clean_term (t \<cdot> \<sigma>) = t \<cdot> (clean_subst \<sigma>)"
      by (rule clean_subst_apply_term, insert t tF mem, auto simp: funas_args_term_def)
 }
 then show ?thesis unfolding t by auto
qed


lemma clean_qrstep_below: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and wwf: "wwf_qtrs Q R"
  and aliens: "set (aliens_below F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> nrqrstep nfs Q R"
  shows "(clean_term_below s, clean_term_below t) \<in> qrstep nfs Q R \<and> set (aliens_below F t) \<subseteq> NF_terms Q"
proof -
  from nrqrstep_imp_Fun_qrstep[OF step]
  obtain f bef aft si ti where s: "s = Fun f (bef @ si # aft)" and t: "t = Fun f (bef @ ti # aft)" and step: "(si, ti) \<in> qrstep nfs Q R"
    by blast
  from aliens[unfolded s] have "set (aliens F si) \<subseteq> NF_terms Q" by auto
  from clean_qrstep[OF inn F wwf this step] have step: "(clean_term si, clean_term ti) \<in> qrstep nfs Q R"
    and al: "set (aliens F ti) \<subseteq> NF_terms Q" by blast+
  from ctxt.closedD [OF ctxt_closed_qrstep step, of "More f (map clean_term bef) \<box> (map clean_term aft)"] aliens al
  show ?thesis unfolding s t by auto
qed

lemma clean_qrstep_sig_step_below: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and wwf: "wwf_qtrs Q R"
  and aliens: "set (aliens_below F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> nrqrstep nfs Q R"
  shows "(clean_term_below s, clean_term_below t) \<in> sig_step_below F (qrstep nfs Q R) \<and> set (aliens_below F t) \<subseteq> NF_terms Q"
proof -
  from clean_qrstep_below[OF inn F wwf aliens step]
  show ?thesis unfolding sig_step_below_def by auto
qed

lemma clean_qrsteps_sig_steps_below: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and wwf: "wwf_qtrs Q R"
  and aliens: "set (aliens_below F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> (nrqrstep nfs Q R)\<^sup>*"
  shows "(clean_term_below s, clean_term_below t) \<in> (sig_step_below F (qrstep nfs Q R))\<^sup>* \<and> set (aliens_below F t) \<subseteq> NF_terms Q"
  using step
proof (induct)
  case base then show ?case using aliens by auto
next
  case (step t u)
  let ?c = "clean_term_below"
  from step(3) have steps: "(?c s, ?c t) \<in> (sig_step_below F (qrstep nfs Q R))\<^sup>*" and aliens: "set (aliens_below F t) \<subseteq> NF_terms Q"
    by auto
  from steps clean_qrstep_sig_step_below[OF inn F wwf aliens step(2)] show ?case by auto
qed

lemma clean_qrsteps_below: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and wwf: "wwf_qtrs Q R"
  and aliens: "set (aliens_below F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> (nrqrstep nfs Q R)\<^sup>*"
  shows "(clean_term_below s, clean_term_below t) \<in> (qrstep nfs Q R)\<^sup>* \<and> set (aliens_below F t) \<subseteq> NF_terms Q"
  using clean_qrsteps_sig_steps_below[OF inn F wwf aliens step] rtrancl_mono[of "sig_step_below F (qrstep nfs Q R)" "qrstep nfs Q R"] unfolding sig_step_below_def by auto

lemma clean_rel_qrsteps_sig_step_below: assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> S)"
  and F: "funas_trs (R \<union> S) \<subseteq> F"
  and wwf: "wwf_qtrs Q (R \<union> S)"
  and aliens: "set (aliens_below F s) \<subseteq> NF_terms Q"
  and step: "(s,t) \<in> relto (nrqrstep nfs Q R) (nrqrstep nfs Q S)"
  shows "(clean_term_below s, clean_term_below t) \<in> relto (sig_step_below F (qrstep nfs Q R)) (sig_step_below F (qrstep nfs Q S)) \<and> set (aliens_below F t) \<subseteq> NF_terms Q"
proof -
  let ?QR = "nrqrstep nfs Q R"
  let ?QS = "nrqrstep nfs Q S"
  let ?QRS = "sig_step_below F (qrstep nfs Q R)"
  let ?QSS = "sig_step_below F (qrstep nfs Q S)"
  let ?Q = "NF_terms Q"
  let ?c = clean_term_below
  from inn have innR: "?Q \<subseteq> NF_trs R" and innS: "?Q \<subseteq> NF_trs S" unfolding NF_trs_union by auto
  from F have FR: "funas_trs R \<subseteq> F" and FS: "funas_trs S \<subseteq> F" unfolding funas_trs_union by auto
  from wwf have wwfR: "wwf_qtrs Q R" and wwfS: "wwf_qtrs Q S" unfolding wwf_qtrs_def by auto
  note qrsteps = clean_qrsteps_sig_steps_below[OF innS FS wwfS]
  from step obtain u v where
    su: "(s,u) \<in> ?QS\<^sup>*" and uv: "(u,v) \<in> ?QR" and vt: "(v,t) \<in> ?QS\<^sup>*" by auto
  from qrsteps[OF aliens su] have su: "(?c s, ?c u) \<in> ?QSS\<^sup>*" and aliens: "set (aliens_below F u) \<subseteq> ?Q" by auto
  from clean_qrstep_sig_step_below[OF innR FR wwfR aliens uv] have uv: "(?c u, ?c v) \<in> ?QRS" and aliens: "set (aliens_below F v) \<subseteq> ?Q" by auto
  from qrsteps[OF aliens vt] have vt: "(?c v, ?c t) \<in> ?QSS\<^sup>*" and aliens: "set (aliens_below F t) \<subseteq> ?Q" by auto
  from su uv vt aliens show ?thesis by auto
qed

lemma clean_rel_qrsteps_below:
  assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> S)"
    and F: "funas_trs (R \<union> S) \<subseteq> F"
    and wwf: "wwf_qtrs Q (R \<union> S)"
    and aliens: "set (aliens_below F s) \<subseteq> NF_terms Q"
    and step: "(s,t) \<in> relto (nrqrstep nfs Q R) (nrqrstep nfs Q S)"
  shows "(clean_term_below s, clean_term_below t) \<in> relto (qrstep nfs Q R) (qrstep nfs Q S) \<and> set (aliens_below F t) \<subseteq> NF_terms Q"
proof -
  from clean_rel_qrsteps_sig_step_below[OF inn F wwf aliens step]
  show ?thesis using relto_mono[of "sig_step_below F (qrstep nfs Q R)" "qrstep nfs Q R" "sig_step_below F (qrstep nfs Q S)" "qrstep nfs Q S"] unfolding sig_step_below_def by auto
qed


lemma clean_ichain_below:
  assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> Rw)"
  and FR: "funas_trs (R \<union> Rw) \<subseteq> F"
  and FP: "funas_args_trs (P \<union> Pw) \<subseteq> F"
  and wwf: "wwf_qtrs Q (R \<union> Rw)"
  and non_var: "\<And>s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t \<and> \<not> defined (applicable_rules Q (R \<union> Rw)) (the (root t))"
  and vars: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  and ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows "ichain (nfs,m,P,Pw,Q,R,Rw) s t (\<lambda> i. clean_subst (\<sigma> i))"
proof -
  from wwf have nvar: "\<forall>(l, r)\<in>R \<union> Rw. is_Fun l" by (rule wwf_var_cond)
  let ?\<sigma> = "\<lambda> i. clean_subst (\<sigma> i)"
  let ?c = clean_term_below
  note ichain = ichain[unfolded ichain.simps]
  let ?R = "qrstep nfs Q R"
  let ?Rw = "qrstep nfs Q (R \<union> Rw)"
  let ?rel = "?Rw\<^sup>* O ?R O ?Rw\<^sup>*"
  let ?Rb = "nrqrstep nfs Q R"
  let ?Rwb = "nrqrstep nfs Q (R \<union> Rw)"
  let ?relb = "?Rwb\<^sup>* O ?Rb O ?Rwb\<^sup>*"
  let ?Q = "NF_terms Q"
  from ichain have P: "\<And> i. (s i, t i) \<in> P \<union> Pw" by auto
  from ichain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?Rw\<^sup>*" by auto
  from ichain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> ?Q" by auto
  from ichain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
  from ichain have inf: "INFM i. (s i, t i) \<in> P \<or> (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?rel"
    unfolding INFM_disj_distrib by simp
  {
    fix i
    from non_var[OF P[of i]] have "\<not> defined (applicable_rules Q (R \<union> Rw)) (the (root (t i \<cdot> \<sigma> i)))" by auto
  } note ndef = this
  note steps = qrsteps_imp_nrqrsteps[OF nvar ndef steps]
  {
    fix i
    from P[of i] non_var[OF P[of i]] FP  have F: "funas_args_term (s i) \<subseteq> F" "is_Fun (s i)" "funas_args_term (t i) \<subseteq> F" "is_Fun (t i)"
      "is_Fun (s i \<cdot> \<sigma> i)"
      unfolding funas_args_trs_def funas_args_rule_def [abs_def] by force+
  } note F = this
  note subst = clean_subst_apply_term_below[OF F(1-2)] clean_subst_apply_term_below[OF F(3-4)]
  note qrsteps = clean_qrsteps_below[OF inn FR wwf, THEN conjunct1]
  from inn have innB: "?Q \<subseteq> NF_trs (R \<union> (R \<union> Rw))" by auto
  from FR have FRB: "funas_trs (R \<union> (R \<union> Rw)) \<subseteq> F" by auto
  from wwf have wwfB: "wwf_qtrs Q (R \<union> (R \<union> Rw))" by auto
  note qrelsteps = clean_rel_qrsteps_below[OF innB FRB wwfB, THEN conjunct1]
  {
    fix i
    from NF_subterm[OF NF[of i] aliens_below_imp_supteq] have "set (aliens_below F (s i \<cdot> \<sigma> i)) \<subseteq> ?Q" by auto
    then have "set (aliens_below F (t i \<cdot> \<sigma> i)) \<subseteq> ?Q"
      unfolding aliens_below_subst[OF F(1-2)]
      unfolding aliens_below_subst[OF F(3-4)] using vars[OF P[of i]] by auto
  } note aliens = this
  show ?thesis unfolding ichain.simps
  proof (intro conjI allI, rule P)
    fix i
    from qrsteps[OF aliens steps[of i]]
    show "(t i \<cdot> ?\<sigma> i, s (Suc i) \<cdot> ?\<sigma> (Suc i)) \<in> ?Rw\<^sup>*" unfolding subst .
    from NF[of i] have "?c (s i \<cdot> \<sigma> i) \<cdot> unclean_subst \<in> ?Q" unfolding unclean_subst_below[OF F(5)] .
    from NF_instance[OF this[unfolded subst]]
    show "s i \<cdot> ?\<sigma> i \<in> ?Q" .
  next
    let ?r = "\<lambda> i. (t i \<cdot> ?\<sigma> i, s (Suc i) \<cdot> ?\<sigma> (Suc i)) \<in> ?rel"
    show "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. ?r i)"
      unfolding INFM_disj_distrib[symmetric]
      unfolding INFM_nat_le
    proof
      fix m
      from inf[unfolded INFM_nat_le, rule_format, of m]
      obtain n where n: "n \<ge> m" and disj: "(s n, t n) \<in> P \<or> (t n \<cdot> \<sigma> n, s (Suc n) \<cdot> \<sigma> (Suc n)) \<in> ?rel" by auto
      from disj have disj: "(s n, t n) \<in> P \<or> (t n \<cdot> \<sigma> n, s (Suc n) \<cdot> \<sigma> (Suc n)) \<in> ?relb" using rel_qrsteps_imp_rel_nrqrsteps[OF nvar ndef[of n]]
        by auto
      show "\<exists> n \<ge> m. (s n, t n) \<in> P \<or> ?r n"
      proof (intro exI conjI, rule n)
        from disj qrelsteps[OF aliens[of n], of "s (Suc n) \<cdot> \<sigma> (Suc n)"]
        show "(s n, t n) \<in> P \<or> ?r n" unfolding subst by blast
      qed
    qed
  next
    fix i
    show "NF_subst nfs (s i, t i) (?\<sigma> i) Q"
      by (rule clean_NF_subst[OF nfs])
  qed
qed

lemma clean_term_match: assumes "clean_term t = l \<cdot> \<sigma>"
  shows "\<forall> x \<in> vars_term l. \<exists> s. \<sigma> x = clean_term s"
  using assms
proof (induct l arbitrary: t)
  case (Var x t)
  then have "\<sigma> x = clean_term t" by simp
  then show ?case by auto
next
  case (Fun f ls t)
  from Fun(2) obtain ts where t: "t = Fun f ts" and f: "(f,length ts) \<in> F" by (cases t, auto split: if_splits)
  note Fun = Fun[unfolded t]
  show ?case
  proof
    fix x
    assume "x \<in> vars_term (Fun f ls)"
    then obtain l where x: "x \<in> vars_term l" and l: "l \<in> set ls" by auto
    note IH = Fun(1)[OF l]
    from Fun(2) f have id: "map clean_term ts = map (\<lambda> t. t \<cdot> \<sigma>) ls" by simp
    from l have "l \<cdot> \<sigma> \<in> set (map clean_term ts)" using id by auto
    then obtain t where t: "t \<in> set ts" and id: "clean_term t = l \<cdot> \<sigma>" by auto
    note IH = IH[OF id]
    from IH[rule_format, OF x]
    show "\<exists> s. \<sigma> x = clean_term s" .
  qed
qed

lemma clean_qrstep_reverse: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and QF: "QF_cond F Q"
  and wwf: "wwf_qtrs Q R" (* essentially, we need vars(r) \<subseteq> vars(l) *)
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and step: "(clean_term s, u) \<in> qrstep nfs Q R"
  and nfs: "\<not> nfs" (* TODO: investigate whether this is crucial *)
  shows "\<exists> t. u = clean_term t \<and> (s,t) \<in> qrstep nfs Q R"
proof -
  let ?QR = "qrstep nfs Q R"
  let ?Q = "NF_terms Q"
  let ?c = clean_term
  from step obtain C l r \<sigma> where lr: "(l,r) \<in> R" and NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> ?Q"
    and s: "?c s = C\<langle>l\<cdot>\<sigma>\<rangle>" and u: "u = C\<langle>r\<cdot>\<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  from lr F have l: "funas_term l \<subseteq> F" and r: "funas_term r \<subseteq> F"
    unfolding funas_trs_def funas_rule_def [abs_def]
    by force+
  note clr = clean_subst_apply_term[OF l] clean_subst_apply_term[OF r]
  from only_applicable_rules[OF NF, of r] wwf lr have vars: "vars_term r \<subseteq> vars_term l"
    unfolding wwf_qtrs_def by auto
  note NF_conv = NF_terms_args_conv
  let ?\<sigma> = "clean_subst \<sigma>"
  show ?thesis using aliens s unfolding u
  proof (induct C arbitrary: s)
    case (More f bef C aft s)
    let ?i = "length bef"
    let ?n = "Suc (?i + length aft)"
    let ?C = "More f bef C aft"
    from More(3) obtain ss where s: "s = Fun f ss" by (cases s, auto split: if_splits)
    note More = More[unfolded s]
    from More(3) have f: "(f,length ss) \<in> F" by (auto split: if_splits)
    from More(3) f have id: "map clean_term ss = bef @ C\<langle>l\<cdot>\<sigma>\<rangle> # aft" by simp
    obtain sbef saft si where ss: "sbef = take ?i ss" "si = ss ! ?i" "saft = drop (Suc ?i) ss" by auto
    from arg_cong[OF id, of length] have len: "length ss = ?n" by auto
    then have i: "?i < length ss" by simp
    from id_take_nth_drop[OF i] have ss_split: "ss = sbef @ si # saft" unfolding ss .
    from i ss have lsbef: "length sbef = ?i" by auto
    from id[unfolded ss_split] lsbef have id: "bef = map ?c sbef" "?c si = C\<langle>l\<cdot>\<sigma>\<rangle>" "aft = map ?c saft" by auto
    from ss_split have mem: "si \<in> set ss" by auto
    from More(2) mem f have aliens: "set (aliens F si) \<subseteq> ?Q" by auto
    from More(1)[OF aliens id(2)]
    obtain t where C: "C\<langle>r\<cdot>\<sigma>\<rangle> = ?c t" and step: "(si,t) \<in> ?QR" by auto
    let ?t = "Fun f (sbef @ t # saft)"
    show ?case
    proof (rule exI[of _ ?t], rule conjI)
      show "(More f bef C aft)\<langle>r \<cdot> \<sigma>\<rangle> = ?c ?t" using id C f ss_split by simp
    next
      show "(s,?t) \<in> qrstep nfs Q R" using qrstep.ctxt[OF step, of "More f sbef \<box> saft"] unfolding s ss_split
        by simp
    qed
  next
    case Hole
    let ?u = "unclean_subst"
    let ?\<tau> = "\<sigma> \<circ>\<^sub>s ?u"
    from Hole have id: "?c s = l \<cdot> \<sigma>" by simp
    then have "?c s \<cdot> unclean_subst = l \<cdot> ?\<tau>" by simp
    from this[unfolded unclean_subst] have s: "s = l \<cdot> ?\<tau>" and s': "?c s \<cdot> ?u = s \<cdot> Var" using id by auto
    have step: "(s,r \<cdot> ?\<tau>) \<in> ?QR"
    proof (rule qrstepI[OF _ lr, of ?\<tau> _ _ \<box>])
      note NF_conv = NF_terms_args_conv[symmetric]
      from NF[unfolded id[symmetric] NF_conv] have NF: "\<And> u. u \<in> set (args (?c s)) \<Longrightarrow> u \<in> ?Q" ..
      from Hole(1) have aliens: "set (aliens F s) \<subseteq> ?Q" by auto
      show "\<forall> v \<lhd> l \<cdot> ?\<tau>. v \<in> ?Q" unfolding s[symmetric] NF_conv
      proof
        fix si
        assume si: "si \<in> set (args s)"
        then obtain f ss where s: "s = Fun f ss" by (cases s, auto)
        with si have si: "si \<in> set ss" by auto
        note aliens = aliens[unfolded s]
        show "si \<in> ?Q"
        proof (cases "(f,length ss) \<in> F")
          case False
          with aliens have NF: "Fun f ss \<in> ?Q" by auto
          show ?thesis
            by (rule NF_subterm[OF NF], insert si, auto)
        next
          case True
          from NF[unfolded s] True have NF: "\<And> s. s \<in> set ss \<Longrightarrow> ?c s \<in> ?Q" by auto
          from NF[OF si] have NF: "?c si \<in> ?Q" .
          from aliens True si have aliens: "set (aliens F si) \<subseteq> ?Q" by auto
          show "si \<in> ?Q"
          proof (rule, rule ccontr, unfold not_not)
            fix u
            assume "(si,u) \<in> rstep (Id_on Q)"
            then obtain C \<tau> q q'
              where q: "(q,q') \<in> Id_on Q" and si: "si = C\<langle>q\<cdot>\<tau>\<rangle>" and "u = C\<langle>q' \<cdot> \<tau>\<rangle>" by blast
            then have q: "q \<in> Q" by auto
            {
              fix x
              assume qx: "q = Var x"
              with q have y: "(Var x,Var x) \<in> Id_on Q" by auto
              have "(?c si, ?c si) \<in> rstep (Id_on Q)"
                by (rule rstepI[OF y, of _ \<box> "\<lambda> _. ?c si"], auto)
              with NF have False by auto
            }
            then obtain f qq where q_fun: "q = Fun f qq" by (cases q, auto)
            from si aliens NF
            show False
            proof (induct C arbitrary: si)
              case (More f bef C aft)
              let ?n = "Suc (length bef + length aft)"
              show ?case
              proof (cases "(f,?n) \<in> F")
                case True
                from More(2) have si: "si = Fun f (bef @ C\<langle>q\<cdot>\<tau>\<rangle> # aft)" by auto
                from NF_subterm[OF More(4)] True have NF: "?c (C\<langle>q \<cdot> \<tau>\<rangle>) \<in> ?Q" unfolding si by auto
                from More(3) True have aliens: "set (aliens F (C\<langle>q \<cdot> \<tau>\<rangle>)) \<subseteq> ?Q" unfolding si by auto
                from More(1)[OF refl aliens NF] show False .
              next
                case False
                with More(3) More(2) have "Fun f (bef @ C\<langle>q \<cdot> \<tau>\<rangle> # aft) \<in> ?Q" by auto
                with rstepI[of q q "Id_on Q" _ "More f bef C aft" \<tau>, OF _ refl refl] q
                show False by auto
              qed
            next
              case Hole
              then have si: "si = q \<cdot> \<tau>" by simp
              from Hole(2) have aliens: "set (aliens F si) \<subseteq> ?Q" by simp
              from Hole(3) have NF: "?c si \<in> ?Q" by auto
              from si q_fun
              obtain ss where si_fun: "si = Fun f ss" by (cases si, auto)
              {
                fix x
                assume id: "?c si = Var x"
                then have f: "(f,length ss) \<notin> F" and id': "?c si \<cdot> ?u = ?u x" unfolding si_fun by auto
                from f aliens have si_aliens: "si \<in> ?Q" unfolding si_fun by auto
                with si q have False by force
              }
              then have csi_fun: "?c si = Fun f (map ?c ss)" unfolding si_fun by (force split: if_splits)
              then have f: "(f,length ss) \<in> F" unfolding si_fun by (force split: if_splits)
              from QF[unfolded QF_cond_def, rule_format, OF q _ f] have qF: "funas_term q \<subseteq> F" using si unfolding si_fun q_fun by auto
              from si have "?c si = ?c (q \<cdot> \<tau>)" by simp
              from this[unfolded clean_subst_apply_term[OF qF]] q NF show False by force
            qed
          qed
        qed
      qed
    next
      show "NF_subst nfs (l, r) ?\<tau> Q" using \<open>\<not> nfs\<close> by simp
    qed (insert s, auto)
    have r\<sigma>: "?c (r \<cdot> ?\<tau>) = r \<cdot> \<sigma>" unfolding clr
    proof (rule term_subst_eq)
      fix x
      assume "x \<in> vars_term r"
      with vars have x: "x \<in> vars_term l" by auto
      from clean_term_match[OF id, rule_format, OF x] obtain s where x: "\<sigma> x = ?c s" by auto
      show "clean_subst ?\<tau> x = \<sigma> x" unfolding clean_subst.simps o_def subst_compose_def
        unfolding x unclean_subst ..
    qed
    show ?case
      by (intro exI, rule conjI[OF _ step], insert r\<sigma>, auto)
  qed
qed
end

context cleaning_innermost
begin
lemma clean_qrstep_preserves_SN_on: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and F: "funas_trs R \<subseteq> F"
  and QF: "QF_cond F Q"
  and wwf: "wwf_qtrs Q R" (* essentially, we need vars(r) \<subseteq> vars(l) *)
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and SN: "SN_on (qrstep nfs Q R) {s}"
  and nfs: "\<not> nfs"
  shows step: "SN_on (qrstep nfs Q R) {clean_term s}"
proof 
  let ?c = clean_term
  let ?Q = "NF_terms Q"
  let ?QR = "qrstep nfs Q R"
  fix f
  assume f0: "f 0 \<in> {?c s}" and steps: "\<forall>i. (f i, f (Suc i)) \<in> ?QR"
  let ?P = "\<lambda> s. set (aliens F s) \<subseteq> ?Q \<and> (\<exists> i. ?c s = f i)"
  from f0 aliens have "?P s" by (intro conjI exI[of _ 0], auto)
  have "\<not> SN_on ?QR {s}"
  proof (rule conditional_steps_imp_not_SN_on[of ?P, OF \<open>?P s\<close>])
    fix t
    assume "?P t" then obtain i where id: "?c t = f i" and  aliens: "set (aliens F t) \<subseteq> NF_terms Q" by auto
    from id steps have "(?c t, f (Suc i)) \<in> ?QR" by auto
    from clean_qrstep_reverse[OF inn F QF wwf aliens this nfs]
      obtain u where c: "?c u = f (Suc i)" and tu: "(t,u) \<in> ?QR" by auto
    from clean_qrstep[OF inn F wwf aliens tu] c tu
    show "\<exists>u. (t, u) \<in> ?QR \<and> ?P u" by (intro exI[of _ u], auto)
  qed
  with SN show False by simp
qed
end

context cleaning_innermost
begin

lemma clean_min_ichain:
  assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> Rw)"
  and QF: "QF_cond F Q"
  and FR: "funas_trs (R \<union> Rw) \<subseteq> F"
  and FP: "funas_trs (P \<union> Pw) \<subseteq> F"
  and wwf: "wwf_qtrs Q (R \<union> Rw)"
  and vars: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  and ichain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows "min_ichain_sig (nfs,m,P,Pw,Q,R,Rw) F s t (\<lambda> i. clean_subst (\<sigma> i))"
proof -
  let ?\<sigma> = "\<lambda> i. clean_subst (\<sigma> i)"
  from ichain
  have ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>" and SN: "\<And> i. m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {t i \<cdot> \<sigma> i}"
    by (auto simp: minimal_cond_def)
  show ?thesis
    unfolding min_ichain_sig.simps min_ichain.simps minimal_cond_def
  proof (intro allI conjI impI, rule clean_ichain[OF inn FR FP wwf vars ichain])
    show "funas_ichain s t ?\<sigma> \<subseteq> F" using funas_term_clean_term
      unfolding funas_ichain_def clean_subst.simps o_def by blast
  next
    fix i
    assume m
    note ichain = ichain[unfolded ichain.simps]
    let ?Rw = "qrstep nfs Q (R \<union> Rw)"
    let ?Q = "NF_terms Q"
    from ichain have P: "(s i, t i) \<in> P \<union> Pw" by auto
    from ichain have NF: "s i \<cdot> \<sigma> i \<in> ?Q" by auto
    from P FP  have F: "funas_term (s i) \<subseteq> F" "funas_term (t i) \<subseteq> F"
      unfolding funas_trs_def funas_rule_def [abs_def] by force+
    note subst = clean_subst_apply_term[OF F(1)] clean_subst_apply_term[OF F(2)]
    from NF_subterm[OF NF aliens_imp_supteq] have "set (aliens F (s i \<cdot> \<sigma> i)) \<subseteq> ?Q" by auto
    then have aliens: "set (aliens F (t i \<cdot> \<sigma> i)) \<subseteq> ?Q"
      unfolding aliens_subst[OF F(1)]
      unfolding aliens_subst[OF F(2)] using vars[OF P] by auto
    note switch = wwf_qtrs_imp_nfs_switch[OF wwf, of nfs False]
    from clean_qrstep_preserves_SN_on[OF inn FR QF wwf aliens SN[unfolded switch], unfolded subst, OF \<open>m\<close>]
    show "SN_on ?Rw {t i \<cdot> ?\<sigma> i}" unfolding switch by auto
  qed
qed

lemma clean_min_ichain_below:
  assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> Rw)"
  and QF: "QF_cond F Q"
  and FR: "funas_trs (R \<union> Rw) \<subseteq> F"
  and FP: "funas_args_trs (P \<union> Pw) \<subseteq> F"
  and wwf: "wwf_qtrs Q (R \<union> Rw)"
  and non_var: "\<And>s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t \<and> \<not> defined (applicable_rules Q (R \<union> Rw)) (the (root t))"
  and vars: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  and ichain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows "min_ichain_sig (nfs,m,P,Pw,Q,R,Rw) F s t (\<lambda> i. clean_subst (\<sigma> i))"
proof -
  let ?\<sigma> = "\<lambda> i. clean_subst (\<sigma> i)"
  from ichain
  have ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>" and SN: "\<And> i. m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {t i \<cdot> \<sigma> i}"
    by (auto simp: minimal_cond_def)
  show ?thesis
    unfolding min_ichain_sig.simps min_ichain.simps minimal_cond_def
  proof (intro allI conjI impI, rule clean_ichain_below[OF inn FR FP wwf non_var vars ichain])
    show "funas_ichain s t ?\<sigma> \<subseteq> F" using funas_term_clean_term
      unfolding funas_ichain_def clean_subst.simps o_def by blast
  next
    fix i
    assume m
    note ichain = ichain[unfolded ichain.simps]
    let ?Rw = "qrstep nfs Q (R \<union> Rw)"
    let ?Q = "NF_terms Q"
    from ichain have P: "(s i, t i) \<in> P \<union> Pw" by auto
    from ichain have NF: "s i \<cdot> \<sigma> i \<in> ?Q" by auto
    from P FP non_var[OF P] have F: "funas_args_term (s i) \<subseteq> F" "is_Fun (s i)" "funas_args_term (t i) \<subseteq> F" "is_Fun (t i)"
      and ndef: "\<not> defined (applicable_rules Q (R \<union> Rw)) (the (root (t i)))"
        "\<not> defined (applicable_rules Q (R \<union> Rw)) (the (root (t i \<cdot> clean_subst (\<sigma> i))))"
      unfolding funas_args_trs_def funas_args_rule_def [abs_def] by force+
    from F(4) obtain f ts where t: "t i = Fun f ts" by (cases "t i", auto)
    from NF_subterm[OF NF aliens_below_imp_supteq] have "set (aliens_below F (s i \<cdot> \<sigma> i)) \<subseteq> ?Q" by auto
    then have aliens: "set (aliens_below F (t i \<cdot> \<sigma> i)) \<subseteq> ?Q"
      unfolding aliens_below_subst[OF F(1-2)]
      unfolding aliens_below_subst[OF F(3-4)] using vars[OF P] by auto
    have ti: "t i \<cdot> ?\<sigma> i = Fun f (map (\<lambda> t. t \<cdot> ?\<sigma> i) ts)" unfolding t by simp
    show "SN_on ?Rw {t i \<cdot> clean_subst (\<sigma> i)}" unfolding ti
    proof (rule SN_args_imp_SN[OF _ wwf_var_cond[OF wwf]])
      show "\<not> defined (applicable_rules Q (R \<union> Rw)) (f,length (map (\<lambda> t. t \<cdot> ?\<sigma> i) ts))"
        using ndef unfolding t by simp
    next
      fix tjs
      assume "tjs \<in> set (map (\<lambda> t. t \<cdot> ?\<sigma> i) ts)"
      then obtain tj where tj: "tj \<in> set ts" and tjs: "tjs = tj \<cdot> ?\<sigma> i" by auto
      from ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep SN[OF \<open>m\<close>, of i, unfolded t], of "tj \<cdot> \<sigma> i"]
      have SN: "SN_on ?Rw {tj \<cdot> \<sigma> i}" using tj by auto
      from F(3) tj t have F: "funas_term tj \<subseteq> F" unfolding funas_args_term_def by auto
      from aliens tj t have aliens: "set (aliens F (tj \<cdot> \<sigma> i)) \<subseteq> ?Q" by auto
      note subst = clean_subst_apply_term[OF F]
      note switch = wwf_qtrs_imp_nfs_switch[OF wwf, of nfs False]
      from clean_qrstep_preserves_SN_on[OF inn FR QF wwf aliens SN[unfolded switch]]
      show "SN_on ?Rw {tjs}" unfolding tjs subst switch by auto
    qed
  qed
qed

end

end
