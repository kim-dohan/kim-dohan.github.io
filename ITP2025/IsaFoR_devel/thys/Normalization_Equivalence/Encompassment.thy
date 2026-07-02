(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015, 2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>The Encompassment Relation\<close>

theory Encompassment
  imports  
    Litsim_Trs
begin

inductive encompeq :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<unlhd>\<cdot>" 50)
  where
    [intro]: "t = C\<langle>s \<cdot> \<sigma>\<rangle> \<Longrightarrow> s \<unlhd>\<cdot> t"

lemma encompeq_termE [elim]:
  assumes "s \<unlhd>\<cdot> t"
  obtains C \<sigma> where "t = C\<langle>s \<cdot> \<sigma>\<rangle>"
  using assms by (cases)

lemma encompeq_refl:
  "t \<unlhd>\<cdot> t"
  by (rule encompeq.intros [of t \<box> t Var]) simp

lemma encompeq_trans:
  assumes "s \<unlhd>\<cdot> t"
    and "t \<unlhd>\<cdot> u"
  shows "s \<unlhd>\<cdot> u"
proof -
  obtain C D \<sigma> \<tau>
    where [simp]: "t = C\<langle>s \<cdot> \<sigma>\<rangle>" "u = D\<langle>t \<cdot> \<tau>\<rangle>" using assms by fastforce
  show ?thesis
    by (rule encompeq.intros [of _ "D \<circ>\<^sub>c (C \<cdot>\<^sub>c \<tau>)" _ "\<sigma> \<circ>\<^sub>s \<tau>"]) simp
qed

definition encomp (infix "\<lhd>\<cdot>" 50)
  where
    "t \<lhd>\<cdot> s \<longleftrightarrow> t \<unlhd>\<cdot> s \<and> \<not> s \<unlhd>\<cdot> t"

abbreviation (input) revencompeq  (infix "\<cdot>\<unrhd>" 50) where
  "x \<cdot>\<unrhd> y \<equiv> y \<unlhd>\<cdot> x"

abbreviation (input) revencomp (infix "\<cdot>\<rhd>" 50) where
  "x \<cdot>\<rhd> y \<equiv> y \<lhd>\<cdot> x"

abbreviation encompeq_set ("{\<unlhd>\<cdot>}")
  where
    "{\<unlhd>\<cdot>} \<equiv> {(x, y). x \<unlhd>\<cdot> y}"

abbreviation encomp_set ("{\<lhd>\<cdot>}")
  where
    "{\<lhd>\<cdot>} \<equiv> {(x, y). x \<lhd>\<cdot> y}"

abbreviation revencompeq_set ("{\<cdot>\<unrhd>}")
  where
    "{\<cdot>\<unrhd>} \<equiv> {(x, y). y \<unlhd>\<cdot> x}"

abbreviation revencomp_set ("{\<cdot>\<rhd>}")
  where
    "{\<cdot>\<rhd>} \<equiv> {(x, y). y \<lhd>\<cdot> x}"

interpretation encomp_order: preorder "(\<unlhd>\<cdot>)" "(\<lhd>\<cdot>)"
  by standard (auto simp: encomp_def encompeq_refl elim: encompeq_trans)

text \<open>Encompassment is the composition of subsumption and the subterm relation.\<close>
lemma encompeq_eq_subteq_instance:
  "s \<unlhd>\<cdot> t \<longleftrightarrow> ((\<le>\<cdot>) OO (\<unlhd>)) s t"
  by (force simp: OO_def subsumeseq_term_iff)

lemma subsumeseq_size:
  "s \<le>\<cdot> t \<Longrightarrow> size s \<le> size t"
  by (cases s t rule: subsumeseq_term.cases) (auto simp: size_subst)

lemma subsumeseq_imp_encompeq:
  "s \<le>\<cdot> t \<Longrightarrow> s \<unlhd>\<cdot> t"
  by (cases s t rule: subsumeseq_term.cases) (auto intro: encompeq.intros [of _ \<box>])

lemma encompeq_size:
  "s \<unlhd>\<cdot> t \<Longrightarrow> size s \<le> size t"
  by (force simp: encompeq_eq_subteq_instance dest: subsumeseq_size supteq_size)

lemma encompeq_subsumeseq_cases:
  "s \<unlhd>\<cdot> t \<longleftrightarrow> s \<le>\<cdot> t \<or> ((\<le>\<cdot>) OO (\<lhd>)) s t"
  by (auto simp: encompeq_eq_subteq_instance)

lemma revencompeq_set_cases:
  "{\<cdot>\<unrhd>} = {\<cdot>\<ge>} \<union> ({\<rhd>} O {\<cdot>\<ge>})"
  unfolding encompeq_subsumeseq_cases by blast

lemma encomp_subsumes_cases:
  "s \<lhd>\<cdot> t \<longleftrightarrow> s <\<cdot> t \<or> ((\<le>\<cdot>) OO (\<lhd>)) s t"
  by (auto simp: encomp_def term_subsumable.subsumes_def encompeq_subsumeseq_cases OO_def)
    (auto dest!: supt_size subsumeseq_size)

lemma wf_subsumeseq_O_subt:
  "wf ({\<le>\<cdot>} O {(x, y). x \<lhd> y})"
proof -
  have "\<And>x y. (x, y) \<in> {\<le>\<cdot>} O {(x, y). x \<lhd> y} \<Longrightarrow> size x < size y"
    by (auto simp: OO_def dest!: subsumeseq_size supt_size)
  then have "{\<le>\<cdot>} O {(x, y). x \<lhd> y} \<subseteq> inv_image {(x, y). x < y} size"
    by (auto simp: inv_image_def)
  moreover have "wf (inv_image {(x, y). x < y} size)" by (rule wf_inv_image [OF wf_less])
  ultimately show ?thesis by (metis wf_subset)
qed

lemma litsim_encompeq_iff:
  "s \<doteq> t \<longleftrightarrow> s \<unlhd>\<cdot> t \<and> t \<unlhd>\<cdot> s"
proof
  assume "s \<doteq> t"
  then show "s \<unlhd>\<cdot> t \<and> t \<unlhd>\<cdot> s"
    by (auto simp: term_subsumable.litsim_def dest: subsumeseq_imp_encompeq)
next
  presume "s \<unlhd>\<cdot> t" and "t \<unlhd>\<cdot> s"
  then have "s \<le>\<cdot> t" and "t \<le>\<cdot> s"
    by (auto simp: encompeq_subsumeseq_cases dest!: supt_size subsumeseq_size)
  then show "s \<doteq> t" by (auto simp: term_subsumable.litsim_def)
qed auto

lemma encompeq_litsim_encomp_iff:
  "s \<unlhd>\<cdot> t \<longleftrightarrow> s \<doteq> t \<or> s \<lhd>\<cdot> t"
  by (auto simp: litsim_encompeq_iff encomp_def)

lemmas encompeq_cases [consumes 1] = encompeq_litsim_encomp_iff [THEN iffD1]

lemma encomp_supt:
  assumes "s \<cdot>> t" and "t \<rhd> u"
  shows "\<exists>t \<lhd> s. t \<cdot>\<ge> u"
proof -
  from assms [unfolded term_subsumable.subsumes_def subsumeseq_term_iff] obtain \<sigma>
    where "s = t \<cdot> \<sigma>" and "\<not> (\<exists>\<sigma>. t = s \<cdot> \<sigma>)" by blast
  moreover with \<open>t \<rhd> u\<close> have "t \<cdot> \<sigma> \<rhd> u \<cdot> \<sigma>"
    by (metis instance_no_supt_imp_no_supt)
  ultimately have "s \<rhd> u \<cdot> \<sigma>" and "u \<cdot> \<sigma> \<cdot>\<ge> u"
    by (auto simp: term_subsumable.subsumes_def)
  then show ?thesis by blast
qed

lemma wf_encomp:
  "wf ({\<lhd>\<cdot>} :: ('f, 'v) term rel)"
proof -
  have "{\<rhd>} O {\<cdot>\<ge>} \<union> {\<cdot>>} = ({\<cdot>\<rhd>} :: ('f, 'v) term rel)" by (auto simp: encomp_subsumes_cases)
  moreover
  have "SN ({\<rhd>} O {\<cdot>\<ge>} \<union> ({\<cdot>>} :: ('f, 'v) term rel))"
  proof (rule quasi_commute_imp_SN)
    have [simp]: "{(s, u). \<exists>t. s \<le>\<cdot> t \<and> u \<rhd> t} = {(s, u). \<exists>t \<lhd> u. s \<le>\<cdot> t}" by auto
    show "SN ({\<rhd>} O {\<cdot>\<ge>})"
      using wf_subsumeseq_O_subt
      by (auto simp: SN_iff_wf converse_unfold OO_def relcomp_def)
    show "SN ({\<cdot>>} :: ('f, 'v) term rel)"
      using wf_subsumes by (auto simp: SN_iff_wf converse_unfold)
    show "quasi_commute ({\<rhd>} O {\<cdot>\<ge>}) ({\<cdot>>} :: ('f, 'v) term rel)"
    proof (unfold quasi_commute_def, intro subrelI)
      fix s t :: "('f, 'v) term"
      assume "(s, t) \<in> {\<cdot>>} O {\<rhd>} O {\<cdot>\<ge>}"
      moreover have "{\<cdot>>} O {\<rhd>} \<subseteq> {\<rhd>} O {\<cdot>\<ge>}"
        by (auto simp: relcomp_def OO_def dest: encomp_supt)
      ultimately have "(s, t) \<in> {\<rhd>} O {\<cdot>\<ge>} O {\<cdot>\<ge>}" by auto
      then have "(s, t) \<in> {\<rhd>} O {\<cdot>\<ge>}"
        by (auto simp: relcomp_def OO_def dest: subsumeseq_term_trans)
      then show "(s, t) \<in> ({\<rhd>} O {\<cdot>\<ge>}) O ({\<rhd>} O {\<cdot>\<ge>} \<union> {\<cdot>>})\<^sup>*" by auto
    qed
  qed
  ultimately
  show ?thesis by (auto simp: SN_iff_wf converse_unfold)
qed

lemmas encomp_induct = wfp_induct [OF wf_encomp [to_pred]]

lemma SN_encomp:
  "SN {\<cdot>\<rhd>}"
  using wf_encomp by (auto simp: SN_iff_wf converse_unfold)

lemma qc_SN_relto_encompeq:
  "SN r \<Longrightarrow> {\<cdot>\<unrhd>} O r \<subseteq> r O (r \<union> {\<cdot>\<unrhd>})\<^sup>* \<Longrightarrow> SN (relto r {\<cdot>\<unrhd>})"
  by (intro qc_SN_relto_iff [THEN iffD2])

context
  fixes r :: "('f, 'v) term rel"
  assumes r_ctxt: "(s, t) \<in> r \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> r"
    and r_subst: "(s, t) \<in> r \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> r"
begin

lemma commutes_rewrel_encomp:
  "{\<cdot>\<unrhd>} O r \<subseteq> r O {\<cdot>\<unrhd>}"
proof -
  { fix s t u
    assume "s \<cdot>\<unrhd> t" and "(t, u) \<in> r"
    then obtain C and \<sigma> :: "('f, 'v) subst" where "s = C\<langle>t \<cdot> \<sigma>\<rangle>"
      and "(C\<langle>t \<cdot> \<sigma>\<rangle>, C\<langle>u \<cdot> \<sigma>\<rangle>) \<in> r" by (auto simp: encomp_def r_ctxt r_subst)
    then have "(s, u) \<in> r O {\<cdot>\<unrhd>}" by auto }
  then show ?thesis by blast
qed

context
  assumes SN_rewrel: "SN r"
begin

lemma SN_rewrel_relto_encomp:
  "SN (relto r {\<cdot>\<unrhd>})"
  using SN_rewrel and commutes_rewrel_encomp
  by (intro qc_SN_relto_encompeq) auto

lemma SN_encomp_Un_rewrel:
  "SN ({\<cdot>\<rhd>} \<union> r)"
proof -
  have "{\<cdot>\<rhd>}\<^sup>* O r O {\<cdot>\<rhd>}\<^sup>* \<subseteq> {\<cdot>\<unrhd>}\<^sup>* O r O {\<cdot>\<unrhd>}\<^sup>*"
    by (intro relcomp_mono rtrancl_mono) (auto simp: encomp_def)
  with SN_rewrel_relto_encomp have "SN ({\<cdot>\<rhd>}\<^sup>* O r O {\<cdot>\<rhd>}\<^sup>*)" by (rule SN_subset)
  from SN_relto_split [of _ "{}" _ "{}", simplified, OF this SN_encomp]
  show ?thesis by (simp add: ac_simps)
qed

end

end

lemma revencompeq_set_eqvt [simp]:
  "\<pi> \<bullet> {\<cdot>\<unrhd>} = {\<cdot>\<unrhd>}"
  by (simp add: revencompeq_set_cases trs_pt.union_eqvt trs_pt.relcomp_eqvt)

end
