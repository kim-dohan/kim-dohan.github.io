(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Literal Similarity of TRSs\<close>

theory Litsim_Trs
  imports
    TRS.Renaming_Interpretations
    First_Order_Terms.Subsumption
begin

lemma listsim_equiv_on_terms:
  "equiv T {(x, y). x \<doteq> y \<and> x \<in> T \<and> y \<in> T}"
  by (rule equivI)
    (auto simp: refl_on_def sym_def trans_def
      dest: term_subsumable.litsim_sym term_subsumable.litsim_trans)

lemma equivp_litsim:
  "equivp ((\<doteq>) :: ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool)"
  by (rule equivpI) (auto simp: reflp_def symp_def transp_def
      dest: term_subsumable.litsim_sym term_subsumable.litsim_trans)

lemma litsim_term_iff:
  fixes s t :: "('f, 'v :: infinite) term"
  shows "s \<doteq> t \<longleftrightarrow> (\<exists>p. p \<bullet> s = t)"
proof
  assume "\<exists>p. p \<bullet> s = t"
  then obtain p where "p \<bullet> s = t" ..
  then have "t = s \<cdot> sop p" and "s = t \<cdot> sop (-p)" by auto
  from subsumeseq_term.intros [OF this(1)] and subsumeseq_term.intros [OF this(2)]
  show "s \<doteq> t" by (auto simp: term_subsumable.litsim_def)
next
  assume "s \<doteq> t"
  then obtain \<sigma> \<tau>
    where "s \<cdot> \<sigma> = t" and "t \<cdot> \<tau> = s" by (fastforce simp: term_subsumable.litsim_def)
  from variants_imp_renaming [OF this] obtain f
    where "bij f" and "finite {x. f x \<noteq> x}" and [simp]: "t = s \<cdot> (Var \<circ> f)" by blast
  then have "f \<in> perms" by (auto simp: perms_def)
  then have "Abs_perm f \<bullet> s = t" by (auto simp: term_apply_subst_Var_Abs_perm)
  then show "\<exists>p. p \<bullet> s = t" ..
qed

lemma instanceeq_set_eqvt [simp]:
  "\<pi> \<bullet> {\<cdot>\<ge>} = {\<cdot>\<ge>}"
proof (intro equalityI subrelI)
  fix s t :: "('a, 'b) term" assume "(s, t) \<in> \<pi> \<bullet> {\<cdot>\<ge>}"
  then have "-\<pi> \<bullet> s \<cdot>\<ge> -\<pi> \<bullet> t"
    by (auto simp: inv_rule_mem_trs_simps [where p = "\<pi>", symmetric])
  then obtain \<sigma> where "(-\<pi> \<bullet> t) \<cdot> \<sigma> = -\<pi> \<bullet> s" by auto
  then have "t \<cdot> conjugate_subst \<pi> \<sigma> = s"
    using term_apply_subst_eqvt [of \<pi> "-\<pi> \<bullet> t" \<sigma>] by simp
  then show "(s, t) \<in> {\<cdot>\<ge>}" by blast
next
  fix s t :: "('a, 'b) term" assume "(s, t) \<in> {\<cdot>\<ge>}"
  then obtain \<sigma> where "s = t \<cdot> \<sigma>" by auto
  then have "-\<pi> \<bullet> s = (-\<pi> \<bullet> t) \<cdot> conjugate_subst (-\<pi>) \<sigma>" by (auto simp: eqvt)
  then have "-\<pi> \<bullet> s \<cdot>\<ge> -\<pi> \<bullet> t" by blast
  then have "-\<pi> \<bullet> (s, t) \<in> {\<cdot>\<ge>}" by (auto simp: eqvt)
  then show "(s, t) \<in> \<pi> \<bullet> {\<cdot>\<ge>}" unfolding trs_pt.inv_mem_simps(1) [of \<pi>] .
qed

lemma subsumeseq_set_eqvt [simp]:
  "\<pi> \<bullet> {\<le>\<cdot>} = {\<le>\<cdot>}"
proof (intro equalityI subrelI)
  fix s t :: "('a, 'b) term" assume "(s, t) \<in> \<pi> \<bullet> {\<le>\<cdot>}"
  then have "-\<pi> \<bullet> s \<le>\<cdot> -\<pi> \<bullet> t"
    by (auto simp: inv_rule_mem_trs_simps [where p = "\<pi>", symmetric])
  then have "-\<pi> \<bullet> (t, s) \<in> {\<cdot>\<ge>}" by (auto simp: eqvt)
  then have "(t, s) \<in> \<pi> \<bullet> {\<cdot>\<ge>}" unfolding trs_pt.inv_mem_simps(1) [of \<pi>] .
  then show "(s, t) \<in> {\<le>\<cdot>}" by simp
next
  fix s t :: "('a, 'b) term" presume "(t, s) \<in> {\<cdot>\<ge>}"
  then have "(t, s) \<in> \<pi> \<bullet> {\<cdot>\<ge>}" by simp
  then have "(-\<pi> \<bullet> t, -\<pi> \<bullet> s) \<in> {\<cdot>\<ge>}" unfolding trs_pt.inv_mem_simps(1) [of \<pi>, symmetric] by (auto simp: eqvt)
  then have "(-\<pi> \<bullet> s, -\<pi> \<bullet> t) \<in> {\<le>\<cdot>}" by auto
  then have "-\<pi> \<bullet> (s, t) \<in> {\<le>\<cdot>}" by (auto simp: eqvt)
  then show "(s, t) \<in> \<pi> \<bullet> {\<le>\<cdot>}" unfolding trs_pt.inv_mem_simps(1) [of \<pi>] .
qed blast

lemma instance_term_set_conv:
  "{\<cdot>>} = {\<cdot>\<ge>} - {\<le>\<cdot>}"
  by (auto simp: term_subsumable.subsumes_def)

lemma subsumes_term_set_conv:
  "{<\<cdot>} = {\<le>\<cdot>} - {\<cdot>\<ge>}"
  by (auto simp: term_subsumable.subsumes_def)

lemma instance_term_set_eqvt [simp]:
  "\<pi> \<bullet> {\<cdot>>} = {\<cdot>>}"
  by (simp add: instance_term_set_conv trs_pt.Diff_eqvt)

lemma subsumes_term_set_eqvt [simp]:
  "\<pi> \<bullet> {<\<cdot>} = {<\<cdot>}"
  by (simp add: subsumes_term_set_conv trs_pt.Diff_eqvt)

definition subsumeseq_trs :: "('f, 'v :: infinite) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
  where
    "subsumeseq_trs R S \<longleftrightarrow> (\<forall>r \<in> R. \<exists>p. p \<bullet> r \<in> S)"

adhoc_overloading
  SUBSUMESEQ \<rightleftharpoons> subsumeseq_trs

lemma subsumeseq_trsI [intro]:
  assumes "\<And>r. r \<in> R \<Longrightarrow> \<exists>p. p \<bullet> r \<in> S"
  shows "R \<le>\<cdot> S"
  unfolding subsumeseq_trs_def by (rule ballI) (insert assms, auto)

lemma subsumeseq_trsE [elim]:
  assumes "R \<le>\<cdot> S" and "r \<in> R"
  obtains p where "p \<bullet> r \<in> S"
  using assms by (auto simp: subsumeseq_trs_def)

lemma subsumeseq_trs_refl:
  fixes R :: "('f, 'v :: infinite) trs"
  shows "R \<le>\<cdot> R"
  using trs_pt.subset_imp_ex_perm [of R, OF subset_refl]
  by (auto simp: subsumeseq_trs_def)

lemma subsumeseq_trs_trans:
  fixes R S T :: "('f, 'v :: infinite) trs"
  assumes "R \<le>\<cdot> S" and "S \<le>\<cdot> T"
  shows "R \<le>\<cdot> T"
proof
  fix r
  assume "r \<in> R"
  with \<open>R \<le>\<cdot> S\<close> obtain p where "p \<bullet> r \<in> S" by auto
  then obtain q where "q \<bullet> p \<bullet> r \<in> T" using \<open>S \<le>\<cdot> T\<close> by blast
  then have "(q + p) \<bullet> r \<in> T" by simp
  then show "\<exists>p. p \<bullet> r \<in> T" by blast
qed

interpretation subsumable_trs: subsumable subsumeseq_trs
  by standard (force simp: subsumeseq_trs_refl dest: subsumeseq_trs_trans)+

adhoc_overloading
  SUBSUMES \<rightleftharpoons> subsumable_trs.subsumes and
  LITSIM \<rightleftharpoons> subsumable_trs.litsim

end
