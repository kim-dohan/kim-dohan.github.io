(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2016)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014,2017)
Author:  Martin Avanzini <martin.avanzini@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Q_Restricted_Rewriting
  imports Sharp_Syntax    
begin

subsection \<open>Q-Restricted Rewriting\<close>

definition NF_subst :: "bool \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) terms \<Rightarrow> bool"
where
  "NF_subst b lr \<sigma> Q \<longleftrightarrow> (b \<longrightarrow> \<sigma> ` vars_rule lr \<subseteq> NF_terms Q)"

lemma NF_subst_False[simp]: "NF_subst False lr \<sigma> Q = True"
  unfolding NF_subst_def by simp

lemma NF_subst_Empty[simp]: "NF_subst nfs lr \<sigma> {} = True"
  unfolding NF_subst_def by simp

lemma NF_subst_right: "nfs \<Longrightarrow> NF_subst nfs (s,t) \<sigma> Q \<Longrightarrow> \<sigma> ` vars_term t \<subseteq> NF_terms Q"
  unfolding NF_subst_def vars_rule_def by auto

lemma NF_substI[intro]: assumes "\<And> x . nfs \<Longrightarrow> x \<in> vars_term l \<or> x \<in> vars_term r \<Longrightarrow> \<sigma> x \<in> NF_terms Q"
  shows "NF_subst nfs (l,r) \<sigma> Q"
  unfolding NF_subst_def
proof (intro impI allI subsetI)
  fix t
  assume nfs and t: "t \<in> \<sigma> ` (vars_rule (l,r))"
  then obtain x where t: "t = \<sigma> x" and x: "x \<in> vars_rule (l,r)" by auto
  from x assms[OF \<open>nfs\<close>, of x] show "t \<in> NF_terms Q" unfolding t
    unfolding vars_rule_def by simp
qed


inductive_set
  qrstep :: "bool \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
  for nfs and Q and R
where
  subst[intro]: "\<forall>u\<lhd>s \<cdot> \<sigma>. u \<in> NF_terms Q \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> NF_subst nfs (s,t) \<sigma> Q \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> qrstep nfs Q R" |
  ctxt[intro]: "(s, t) \<in> qrstep nfs Q R \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> qrstep nfs Q R"

hide_fact (open)
  qrstep.ctxt qrstep.subst
  qrstepp.ctxt qrstepp.subst

lemma qrstep_id[intro]: "\<forall> u \<lhd> s. u \<in> NF_terms Q \<Longrightarrow> (s,t) \<in> R \<Longrightarrow> NF_subst nfs (s,t) Var Q \<Longrightarrow> (s,t) \<in> qrstep nfs Q R"
  using qrstep.subst[of s Var Q t R nfs] by auto

lemma supteq_qrstep_subset:
  "{\<unrhd>} O qrstep nfs Q R \<subseteq> qrstep nfs Q R O {\<unrhd>}"
    (is "?lhs \<subseteq> ?rhs")
proof
  fix s t
  assume "(s, t) \<in> ?lhs"
  then obtain u where "s \<unrhd> u" and "(u, t) \<in> qrstep nfs Q R" by auto
  from \<open>s \<unrhd> u\<close> obtain C where s: "s = C\<langle>u\<rangle>" by auto
  from qrstep.ctxt[OF \<open>(u, t) \<in> qrstep nfs Q R\<close>]
    have "(s, C\<langle>t\<rangle>) \<in> qrstep nfs Q R" by (simp add: s)
  moreover have "C\<langle>t\<rangle> \<unrhd> t" by simp
  ultimately show "(s, t) \<in> ?rhs" by auto
qed

definition
  qrstep_r_p_s ::
    "bool \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) rule \<Rightarrow> pos \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) trs"
where
  "qrstep_r_p_s nfs Q R r p \<sigma> \<equiv> {(s, t).
    (\<forall>u\<lhd>fst r \<cdot> \<sigma>. u \<in> NF_terms Q) \<and>
    p \<in> poss s \<and> r \<in> R \<and> s |_ p = fst r \<cdot> \<sigma> \<and> t = replace_at s p (snd r \<cdot> \<sigma>) \<and> NF_subst nfs r \<sigma> Q}"

(* with the special case innermost rewriting *)
definition
  irstep :: "bool \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
where
  "irstep nfs R \<equiv> qrstep nfs (lhss R) R"

(* and the special case standard rewriting *)
lemma qrstep_rstep_conv[simp]: "qrstep nfs {} R = rstep R"
proof (intro equalityI subrelI)
  fix s t
  assume "(s, t) \<in> rstep R"
  then obtain C l r \<sigma> where s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>" and t: "t = C \<langle> r \<cdot> \<sigma> \<rangle>"
    and lr: "(l,r) \<in> R" by auto
  show "(s, t) \<in> qrstep nfs {} R" unfolding s t
    by (rule qrstep.ctxt[OF qrstep.subst[OF _ lr]], auto)
next
  fix s t assume "(s, t) \<in> qrstep nfs {} R" then show "(s, t) \<in> rstep R"
  by (induct) auto
qed

lemma qrstep_trancl_ctxt:
  assumes "(s, t) \<in> (qrstep nfs Q R)\<^sup>+"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (qrstep nfs Q R)\<^sup>+"
  using assms by (induct) (auto intro: trancl_into_trancl)

text \<open>
The inductive definition really corresponds to the intuitive definition of
Q-restricted rewriting.
\<close>
lemma qrstepE':
  assumes "(s, t) \<in> qrstep nfs Q R"
  shows "\<exists>C \<sigma> l r. (\<forall>u\<lhd>l\<cdot>\<sigma>. u \<in> NF_terms Q) \<and> (l, r) \<in> R \<and> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> NF_subst nfs (l,r) \<sigma> Q"
using assms proof (induct rule: qrstep.induct)
  case (ctxt s t C)
  then obtain D \<sigma> l r where nf: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and lr: "(l, r) \<in> R" and s: "s = D\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = D\<langle>r \<cdot> \<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  let ?C = "C \<circ>\<^sub>c D"
  have s: "C\<langle>s\<rangle> = ?C\<langle>l \<cdot> \<sigma>\<rangle>" by (simp add: s)
  have t: "C\<langle>t\<rangle> = ?C\<langle>r \<cdot> \<sigma>\<rangle>" by (simp add: t)
  show ?case using nf lr s t nfs by blast
next
  case (subst s \<sigma> t)
  show ?case
    apply (rule exI[of _ Hole])
    using subst by auto
qed

lemma qrstepE[elim]:
  assumes "(s, t) \<in> qrstep nfs Q R"
    and "\<And>C \<sigma> l r. \<lbrakk>\<forall>u\<lhd>l\<cdot>\<sigma>. u \<in> NF_terms Q; (l, r) \<in> R; s = C\<langle>l \<cdot> \<sigma>\<rangle>; t = C\<langle>r \<cdot> \<sigma>\<rangle>; NF_subst nfs (l,r) \<sigma> Q\<rbrakk> \<Longrightarrow> P"
  shows "P"
using qrstepE'[of s t nfs Q R] and assms by auto

lemma qrstepI[intro]:
  assumes nf: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and lr: "(l, r) \<in> R"
    and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q"
  shows "(s, t) \<in> qrstep nfs Q R"
  unfolding s t
  by (rule qrstep.ctxt[OF qrstep.subst[OF nf lr nfs]])

text\<open>Every Q-step takes place at a specific position and using a specific
rule and specific substitution.\<close>
lemma qrstep_qrstep_r_p_s_conv:
  "(s, t) \<in> qrstep nfs Q R \<longleftrightarrow> (\<exists>r p \<sigma>. (s, t) \<in> qrstep_r_p_s nfs Q R r p \<sigma>)"
proof
  assume "\<exists>r p \<sigma>. (s, t) \<in> qrstep_r_p_s nfs Q R r p \<sigma>"
  then obtain l r p \<sigma> where NF_terms: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and p: "p \<in> poss s" and lr: "(l, r) \<in> R"
    and s: "s |_ p = l \<cdot> \<sigma>"
    and t: "t = replace_at s p (r \<cdot> \<sigma>)"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q"
    unfolding qrstep_r_p_s_def  by auto
  from ctxt_supt_id[OF p] have s: "s = (ctxt_of_pos_term p s)\<langle>l \<cdot> \<sigma>\<rangle>" unfolding s
    by simp
  from s t NF_terms lr nfs show "(s, t) \<in> qrstep nfs Q R" by auto
next
  assume "(s, t) \<in> qrstep nfs Q R"
  then obtain C l r \<sigma> where "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q"
    by auto
  let ?p = "hole_pos C"
  have "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" by fact
  moreover have "?p \<in> poss s" unfolding s by simp
  moreover have "(l, r) \<in> R" by fact
  moreover have "s |_ ?p = l \<cdot> \<sigma>" by (simp add: s)
  moreover have "t = replace_at s ?p (r \<cdot> \<sigma>)" by (simp add: s t)
  ultimately have "(s, t) \<in> qrstep_r_p_s nfs Q R (l, r) ?p \<sigma>"
    by (simp add: qrstep_r_p_s_def nfs)
  then show "\<exists>r p \<sigma>. (s, t) \<in> qrstep_r_p_s nfs Q R r p \<sigma>" by auto
qed

lemma qrstep_induct[case_names IH, induct set: qrstep]:
  assumes "(s, t) \<in> qrstep nfs Q R"
    and IH: "\<And>C \<sigma> l r. \<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q \<Longrightarrow> (l, r) \<in> R \<Longrightarrow> NF_subst nfs (l,r) \<sigma> Q \<Longrightarrow> P C\<langle>l \<cdot> \<sigma>\<rangle> C\<langle>r \<cdot> \<sigma>\<rangle>"
  shows "P s t"
proof -
  from \<open>(s, t) \<in> qrstep nfs Q R\<close> obtain C \<sigma> l r where NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q"
    by auto
  from IH[OF NF \<open>(l, r) \<in> R\<close> nfs] show ?thesis unfolding s t .
qed

lemma qrstep_rule_conv: "((s,t) \<in> qrstep nfs Q R) = (\<exists> lr \<in> R. (s,t) \<in> qrstep nfs Q {lr})" (is "?l = ?r")
proof
  assume ?r then show ?l by auto
next
  assume ?l then show ?r by blast
qed

lemma qrstep_empty_r[simp]: "qrstep nfs Q {} = {}"
  using qrstep_rule_conv[of _ _ nfs Q "{}"] by auto

lemma qrstep_union: "qrstep nfs Q (R \<union> R') = qrstep nfs Q R \<union> qrstep nfs Q R'"
  using qrstep_rule_conv[of _ _ nfs Q R]
    qrstep_rule_conv[of _ _ nfs Q "R'"]
    qrstep_rule_conv[of _ _ nfs Q "R \<union> R'"]
  by auto

lemma qrstep_all_mono: assumes R: "R \<subseteq> R'" and Q: "NF_terms Q \<subseteq> NF_terms Q'" and n: "Q \<noteq> {} \<Longrightarrow> nfs' \<Longrightarrow> nfs"
  shows "qrstep nfs Q R \<subseteq> qrstep nfs' Q' R'"
proof
  fix s t assume "(s, t) \<in> qrstep nfs Q R"
  then obtain C \<sigma> l r where "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and "(l, r) \<in> R"
    and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  moreover with n Q R have "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q'"
  and "NF_subst nfs' (l,r) \<sigma> Q'" and "(l,r) \<in> R'" unfolding NF_subst_def by auto
  ultimately show "(s, t) \<in> qrstep nfs' Q' R'" by auto
qed

lemma qrstep_rules_mono:
  assumes "R \<subseteq> R'" shows "qrstep nfs Q R \<subseteq> qrstep nfs Q R'"
  by (rule qrstep_all_mono[OF assms], auto)

(* Lemma 2.4 in René's thesis *)
lemma qrstep_mono:
  assumes 1: "R \<subseteq> R'" and 2: "NF_terms Q \<subseteq> NF_terms Q'"
  shows "qrstep nfs Q R \<subseteq> qrstep nfs Q' R'"
  by (rule qrstep_all_mono[OF 1 2])

lemma qrstep_NF_anti_mono:
  assumes "Q \<subseteq> Q'" shows "qrstep nfs Q' R \<subseteq> qrstep nfs Q R"
  by (rule qrstep_mono[OF subset_refl NF_terms_anti_mono[OF assms]])

lemma qrstep_Id: "qrstep nfs Q Id \<subseteq> Id"
proof -
  have "qrstep nfs Q Id \<subseteq> qrstep nfs {} Id"
    by (rule qrstep_mono, auto)
  also have "... \<subseteq> Id" using rstep_id by auto
  finally show ?thesis by auto
qed

(* Lemma 2.6 in René's thesis *)
lemma NF_terms_subset_criterion:
  "Q' \<inter> NF_terms Q = {} \<longleftrightarrow> NF_terms Q \<subseteq> NF_terms Q'" (is "?lhs = ?rhs")
proof
  assume "?rhs" then show "?lhs"
  proof (rule contrapos_pp)
    assume "\<not> ?lhs"
    then obtain q where "q \<in> Q'" and "q \<in> NF_terms Q" by auto
    from \<open>q \<in> Q'\<close> have "q \<notin> NF_terms Q'" by auto
    with \<open>q \<in> NF_terms Q\<close> show "\<not> NF_terms Q \<subseteq> NF_terms Q'" by blast
  qed
next
  assume "?lhs" then show "?rhs"
  proof (rule contrapos_pp)
    assume "\<not> ?rhs"
    then obtain t where NF: "t \<in> NF_terms Q" and "t \<notin> NF_terms Q'" by auto
    then obtain s where "(t, s) \<in> rstep (Id_on Q')" by (auto simp: NF_def)
    then obtain C q \<sigma> where "q \<in> Q'" and t: "t = C\<langle>q \<cdot> \<sigma>\<rangle>" by auto
    have "q \<in> NF_terms Q"
    proof
      fix D l \<tau>
      assume q: "q = D \<langle> l \<cdot> \<tau> \<rangle>" and l: "l \<in> Q"
      have "(t,t) \<in> rstep (Id_on Q)" unfolding t q
        by (rule rstepI[of l l _ _ "C \<circ>\<^sub>c (D \<cdot>\<^sub>c \<sigma>)" "\<tau> \<circ>\<^sub>s \<sigma>"], insert l, auto)
      then have "t \<notin> NF_terms Q" by auto
      with \<open>t \<in> NF_terms Q\<close> show False by blast
    qed
    with \<open>q \<in> Q'\<close> show "Q' \<inter> NF_terms Q \<noteq> {}" by auto
  qed
qed

lemma qrstep_subset_rstep[intro,simp]: "qrstep nfs Q R \<subseteq> rstep R"
  by (simp only: qrstep_rstep_conv[symmetric, of R nfs], rule qrstep_NF_anti_mono, auto)

lemma qrstep_into_rstep: "(s,t) \<in> qrstep nfs Q R \<Longrightarrow> (s,t) \<in> rstep R"
  using qrstep_subset_rstep by auto

lemma qrsteps_into_rsteps: "(s,t) \<in> (qrstep nfs Q R)\<^sup>* \<Longrightarrow> (s,t) \<in> (rstep R)\<^sup>*"
  using rtrancl_mono[OF qrstep_subset_rstep] by auto

lemma qrstep_preserves_funas_terms:
  assumes r: "funas_term r \<subseteq> F"
  and sF: "funas_term s \<subseteq> F" and step: "(s,t) \<in> qrstep nfs Q {(l,r)}" and vars: "vars_term r \<subseteq> vars_term l"
  shows "funas_term t \<subseteq> F"
proof -
  from step obtain C \<sigma> where
    s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  have fs: "funas_term s = funas_ctxt C \<union> funas_term l \<union> \<Union>(funas_term ` \<sigma> ` vars_term l)" unfolding s using funas_term_subst by auto
  have "funas_term t = funas_ctxt C \<union> funas_term r \<union> \<Union>(funas_term ` \<sigma> ` vars_term r)" unfolding t using funas_term_subst by auto
  then have "funas_term t \<subseteq> funas_ctxt C \<union> funas_term r \<union> \<Union>(funas_term ` \<sigma> ` vars_term l)" using \<open>vars_term r \<subseteq> vars_term l\<close> by auto
  with \<open>funas_term r \<subseteq> F\<close> \<open>funas_term s \<subseteq> F\<close>
  show ?thesis unfolding fs by force
qed


lemma ctxt_of_pos_term_qrstep_below:
  assumes step: "(s,t) \<in> qrstep_r_p_s nfs Q R r p' \<sigma>" and le: "p \<le>\<^sub>p p'"
  shows "ctxt_of_pos_term p s = ctxt_of_pos_term p t"
proof -
  from step[unfolded qrstep_r_p_s_def] have p': "p' \<in> poss s" and t: "t = replace_at s p' (snd r \<cdot> \<sigma>)" by auto
  show ?thesis unfolding t
  proof (rule ctxt_of_pos_term_replace_at_below[OF _ le, of s, symmetric])
    from p' le show "p \<in> poss s" unfolding less_eq_pos_def by auto
  qed
qed

lemma parallel_qrstep_subt_at:
  fixes p :: pos
  assumes step: "(s,t) \<in> qrstep_r_p_s nfs Q R lr p \<sigma>"
    and par: "p \<bottom> q"
    and q: "q \<in> poss s"
  shows "s |_ q = t |_ q \<and> q \<in> poss t"
proof -
  note step = step[unfolded qrstep_r_p_s_def]
  from step have t: "t = replace_at s p (snd lr \<cdot> \<sigma>)" and p: "p \<in> poss s" by auto
  show ?thesis unfolding t
    by (rule conjI, rule parallel_replace_at_subt_at[symmetric, OF par p q], insert
      parallel_poss_replace_at[OF par p] q, auto)
qed


lemma qrstep_subt_at_gen:
  assumes step: "(s, t) \<in> qrstep_r_p_s nfs Q R lr (p @ q) \<sigma>"
  shows "(s |_ p, t |_ p) \<in> qrstep_r_p_s nfs Q R lr q \<sigma>"
proof -
  from step[unfolded qrstep_r_p_s_def]
  have NF: "\<forall> u \<lhd> fst lr \<cdot> \<sigma>. u \<in> NF_terms Q"
    and pq: "p @ q \<in> poss s"
    and lr: "lr \<in> R"
    and s: "s |_ (p @ q) = fst lr \<cdot> \<sigma>"
    and t: "t = replace_at s (p @ q) (snd lr \<cdot> \<sigma>)"
    and nfs: "NF_subst nfs lr \<sigma> Q"
    by auto
  from pq[unfolded poss_append_poss] have p: "p \<in> poss s" and q: "q \<in> poss (s |_ p)" by auto
  show ?thesis
    unfolding qrstep_r_p_s_def
    apply (intro CollectI, unfold split)
    apply (intro conjI NF q lr nfs)
    subgoal by (rule s[unfolded subt_at_append[OF p]])
    subgoal by (unfold t ctxt_of_pos_term_append[OF p], simp add: replace_at_subt_at[OF p])
    done
qed

lemma qrstep_r_p_s_imp_poss:
  assumes step: "(s,t) \<in> qrstep_r_p_s nfs Q R lr p \<sigma>"
  shows "p \<in> poss s \<and> p \<in> poss t"
proof -
  from step[unfolded qrstep_r_p_s_def]
  have ps: "p \<in> poss s"
    and t: "t = replace_at s p (snd lr \<cdot> \<sigma>)"
    by auto
  have pt: "p \<in> poss t" unfolding t
    using hole_pos_ctxt_of_pos_term[OF ps]
    hole_pos_poss[of "ctxt_of_pos_term p s"] by auto
  with ps show ?thesis by auto
qed


lemma qrstep_subt_at:
  assumes step: "(s, t) \<in> qrstep_r_p_s nfs Q R lr p \<sigma>"
  shows "(s |_ p, t |_ p) \<in> qrstep_r_p_s nfs Q R lr [] \<sigma>"
  by (rule qrstep_subt_at_gen, insert step, simp)


lemma parallel_qrstep_poss:
  fixes q :: pos
  assumes par: "q \<bottom> p"
    and q: "q \<in> poss s"
    and step: "(s, t) \<in> qrstep_r_p_s nfs Q R r p \<sigma>"
  shows "q \<in> poss t"
proof -
  from step[unfolded qrstep_r_p_s_def]
  have t: "t = replace_at s p (snd r \<cdot> \<sigma>)" and p: "p \<in> poss s" by auto
  from parallel_poss_replace_at[OF parallel_pos_sym[OF par] p]
  show ?thesis unfolding t using q by simp
qed


lemma parallel_qrstep_ctxt_to_term_list:
  fixes q :: pos
  assumes par: "q \<bottom> p"
    and poss: "q \<in> poss s"
    and step: "(s, t) \<in> qrstep_r_p_s nfs Q R r p \<sigma>"
  shows "\<exists>p'.  p' \<le>\<^sub>p p \<and> (\<exists> i. i < length (ctxt_to_term_list (ctxt_of_pos_term q s)) \<and>
  ctxt_to_term_list (ctxt_of_pos_term q s) ! i = s |_ p' \<and>
  ctxt_to_term_list (ctxt_of_pos_term q t) =
    (ctxt_to_term_list (ctxt_of_pos_term q s))[i := t |_ p'])"
proof -
  from parallel_remove_prefix[OF par] obtain pp i1 i2 q1 q2 where
    q: "q = pp @ i1 # q1" and p: "p = pp @ i2 # q2" and i12: "i1 \<noteq> i2"
    by blast
  let ?p1 = "i1 # q1"
  let ?p2 = "i2 # q2"
  let ?c = "ctxt_of_pos_term"
  let ?cc = "\<lambda> p t. ctxt_to_term_list (?c p t)"
  note qr_def = qrstep_r_p_s_def
  show ?thesis unfolding p q
  proof (intro exI, intro conjI)
    show "pp @ [i2] \<le>\<^sub>p pp @ ?p2" unfolding less_eq_pos_def by simp
  next
    show "\<exists> i < length (?cc (pp @ ?p1) s).
      ?cc (pp @ ?p1) s ! i = s |_ (pp @ [i2]) \<and>
      ?cc (pp @ ?p1) t =  (?cc (pp @ ?p1) s) [ i := t |_ (pp @ [i2])]"
      using step poss unfolding p q
    proof (induct pp arbitrary: s t)
      case (Cons i p s t)
      from Cons(2) have step: "(s,t) \<in> qrstep_r_p_s nfs Q R r ([i] @ (p @ ?p2)) \<sigma>" by simp
      note istep = qrstep_subt_at_gen[OF step]
      note step = step[unfolded qr_def]
      from step have p2: "i # p @ ?p2 \<in> poss s" by auto
      then obtain f ss where s: "s = Fun f ss" by (cases s, auto)
      with p2 have iss: "i < length ss" by auto
      from p2[unfolded s] have p2i: "p @ [i2] \<in> poss (ss ! i)" by simp
      from p2i iss have ip2: "i # p \<in> poss s" unfolding s by simp
      from iss have si: "s |_ [i] = ss ! i" unfolding s by simp
      from Cons(3) have "p @ ?p1 \<in> poss (s |_ [i])" unfolding s using iss by simp
      from Cons(1)[OF istep this]
      obtain i' where i': "i' < length (?cc (p @ ?p1) (s |_ [i]))" and
        id1: "?cc (p @ ?p1) (s |_ [i]) ! i' = s |_ [i] |_ (p @ [i2])" and
        id2: "?cc (p @ ?p1) (t |_ [i]) = (?cc (p @ ?p1) (s |_ [i]))[i' := t |_ [i]
        |_ (p @ [i2])]" by blast
      from step have tp2: "t = replace_at s (i # p @ ?p2) (snd r \<cdot> \<sigma>)" by simp
      have ipless: "i # (p @ [i2]) \<le>\<^sub>p i # p @ ?p2" by simp
      have ipt: "i # (p @ [i2]) \<in> poss t" unfolding tp2
        by (rule replace_at_below_poss[OF p2 ipless])
      have "t = replace_at t (i # (p @ [i2])) (t |_ (i # (p @ [i2])))"
        by (rule ctxt_supt_id[symmetric, OF ipt])
      also have "... = replace_at (Fun f ss) (i # (p @ [i2])) (t |_ (i # (p @
      [i2])))" (is "_ = ?t")
        unfolding s[symmetric]
        using ctxt_of_pos_term_qrstep_below[OF Cons(2), of "i # (p @ [i2])"] ipless by auto
      finally have t: "t = ?t" .
      have "t |_ [i] = ?t |_ [i]" using t by simp
      also have "... = replace_at (ss ! i) (p @ [i2]) (t |_ (i # (p @ [i2])))" (is "_ = ?ti")
        using iss by (simp add: nth_append)
      finally have ti: "t |_ [i] = ?ti" .
      have cs: "?c ((i # p) @ ?p2) s = More f (take i ss) (?c (p @ ?p2) (ss ! i)) (drop (Suc i) ss)"
        unfolding s by simp
      have i'': "i' < length (?cc ((i # p) @ ?p1) s)" using i' unfolding s si by simp
      show ?case
      proof (rule exI[of _ i'], intro conjI, rule i'')
        show "?cc ((i # p) @ ?p1) s ! i' = s |_ ((i # p) @ [i2])"
          unfolding s using si id1 i' by (simp add: nth_append)
      next
        from iss have min: "min (length ss) i = i" by simp
        note i' = i'[unfolded si]
        have i'': "i' < length (?cc (p @ i1 # q1) (ss ! i) @ take i ss @ drop (Suc i) ss)"
          using i' by simp
        have "?cc ((i # p) @ ?p1) t = ?cc ((i # p) @ ?p1) ?t" using t by simp
        also have "... = (?cc ((i # p) @ ?p1) s) [i' := t |_ (i # (p @ [i2]))]"
          unfolding s using min id2 i' iss si
          unfolding ti
          by (simp add: replace_at_subt_at[OF p2i] upd_conv_take_nth_drop[OF i''] upd_conv_take_nth_drop[OF i'] nth_append)
        finally show "?cc ((i # p) @ i1 # q1) t = (?cc ((i # p) @ i1 # q1) s)
        [i' := t |_ ((i # p) @ [i2])]" by simp
      qed
    next
      case Nil
      have eps: "\<And> p. [] @ p = p" "\<And> t. t |_ [] = t" by auto
      note Empty = Nil[unfolded eps]
      note step = Empty[unfolded qr_def]
      from step have p2: "i2 # q2 \<in> poss s" by auto
      from Empty have p1: "i1 # q1 \<in> poss s" by simp
      then obtain f ss where s: "s = Fun f ss" by (cases s, auto)
      from s p2 have i2: "i2 < length ss" by auto
      from s p1 have i1: "i1 < length ss" by auto
      from step have t: "t = replace_at (Fun f ss) (i2 # q2) (snd r \<cdot> \<sigma>)" unfolding s by simp
      have r\<sigma>: "snd r \<cdot> \<sigma> = t |_ (i2 # q2)" unfolding t
        by (rule replace_at_subt_at[symmetric], insert p2, unfold s)
      have tt: "t = replace_at (Fun f ss) (i2 # q2) (t |_ (i2 # q2))" (is "t = ?t")
        unfolding r\<sigma>[symmetric] unfolding t ..
      have "t |_ [i2] = ?t |_ [i2]" using tt by simp
      also have "... = replace_at (ss ! i2) q2 (t |_ (i2 # q2))" (is "_ = ?ti")
        using i2 by (simp add: nth_append)
      finally have ti: "t |_ [i2] = ?ti" .
      have i2ss: "take i2 ss @ ss ! i2 # drop (Suc i2) ss = ss"
        using upd_conv_take_nth_drop[OF i2, symmetric] list_update_id by auto
      let ?n = "length (?cc q1 (ss ! i1))"
      from i1 have min1: "min (length ss) i1 = i1" by simp
      from i2 have min2: "min (length ss) i2 = i2" by simp
      from i12 have i12: "i1 < i2 \<or> i2 < i1" by auto
      obtain i2' where i2': "i2' = (if i1 < i2 then i2 - Suc 0 else i2)" by auto
      {
        from i12
        have "(take i1 ss @ drop (Suc i1) ss) ! i2' = ss ! i2"
        proof
          assume "i2 < i1"
          then show ?thesis by (auto simp: nth_append i2' i2)
        next
          assume i12: "i1 < i2"
          then have "i2 = Suc i1 + (i2 - Suc i1)" by simp
          then obtain k where i2k: "i2 = Suc i1 + k" by blast
          from i2[unfolded i2k] have "Suc i1 + k \<le> length ss" by simp
          then show ?thesis 
            by (metis (no_types, lifting) Suc_less_eq Suc_pred i2k add_gr_0 add_leD1 diff_Suc_Suc 
                diff_add_inverse i12 i2' length_take min1 not_add_less1 nth_append nth_drop zero_less_Suc)
        qed
      } note i2'id = this
      from tt have tt: "\<And> p. ?cc p t = ?cc p ?t" by simp
      show ?case unfolding eps s ti unfolding tt
      proof (rule exI[of _ "?n + i2'"], intro conjI)
        show "?cc (i1 # q1) (Fun f ss) ! (?n + i2') = Fun f ss |_ [i2]"
          by (simp add: i2'id)
      next
        from i1 have len: "i1 + (length ss - Suc i1) = length ss - Suc 0" by auto
        from i12 have
          i2'len: "i2' < length ss - Suc 0" unfolding i2' using i1 i2 by auto
        show "length (?cc q1 (ss ! i1)) + i2' < length (?cc (i1 # q1) (Fun f ss))"
          by (auto simp: i2 i1 min1 len i2'len)
      next
        from i12
        show "?cc (i1 # q1) ?t = (?cc (i1 # q1) (Fun f ss)) [?n + i2' := ?ti]"
        proof
          assume i12: "i2 < i1"
          then have len: "?n + i2' < length (?cc (i1 # q1) (Fun f ss))"
            unfolding i2' using min1 i1 i2 by simp
          from i12 have min12: "min i2 i1 = i2" "min i1 i2 = i2" by auto
          have drop: "drop (Suc i2) ss ! (i1 - Suc i2) = ss ! i1" using i12 i1 by simp
          from i12 have "i1 = Suc i2 + (i1 - Suc i2)" by simp
          then obtain k where i1k: "i1 = Suc i2 + k" by blast
          show ?thesis using i12
            unfolding upd_conv_take_nth_drop[OF len]
            unfolding i2'
            by (simp add: min12 i1 i2 min1 min2 nth_append drop, simp add: i1k ac_simps take_drop)
        next
          assume i12: "i1 < i2"
          then have len: "?n + i2' < length (?cc (i1 # q1) (Fun f ss))"
            unfolding i2' using min1 i1 i2 by simp
          from i12 have min12: "min i2 i1 = i1" "min i1 i2 = i1" by auto
          from i12 have "i2 = Suc i1 + (i2 - Suc i1)" by simp
          then obtain k where i2k: "i2 = Suc i1 + k" by blast
          have minik: "min i1 (i1 + k) = i1" by simp
          show ?thesis using i12
            unfolding upd_conv_take_nth_drop[OF len]
            unfolding i2'
            by (simp add: min12 i1 i2 min1 min2 nth_append, simp add: i2k take_drop ac_simps minik)
        qed
      qed
    qed
  qed
qed

lemma parallel_qrstep:
  fixes p1 :: pos
  assumes p12: "p1 \<bottom> p2"
    and p1: "p1 \<in> poss t"
    and p2: "p2 \<in> poss t"
    and step2: "t |_ p2 = l2 \<cdot> \<sigma>2" "\<forall> u \<lhd> l2 \<cdot> \<sigma>2. u \<in> NF_terms Q" "(l2,r2) \<in> R" "NF_subst nfs (l2,r2) \<sigma>2 Q"
  shows "(replace_at t p1 v, replace_at (replace_at t p1 v) p2 (r2 \<cdot> \<sigma>2)) \<in> qrstep nfs Q R" (is "(?one,?two) \<in> _")
proof -
  show ?thesis unfolding qrstep_qrstep_r_p_s_conv
  proof (intro exI)
    show "(?one,?two) \<in> qrstep_r_p_s nfs Q R (l2,r2) p2 \<sigma>2"
      unfolding qrstep_r_p_s_def
      apply (intro CollectI, unfold split fst_conv snd_conv)
      apply (unfold parallel_replace_at_subt_at[OF p12 p1 p2])
      apply (unfold parallel_poss_replace_at[OF p12 p1])
      apply (intro conjI step2(2) refl p2)
        by (insert step2, auto)
  qed
qed

lemma parallel_qrstep_swap:
  fixes p1 :: pos
  assumes p12: "p1 \<bottom> p2"
    and two: "(t, s) \<in> qrstep_r_p_s nfs Q1 R1 r1 p1 \<sigma>1 O qrstep_r_p_s nfs Q2 R2 r2 p2 \<sigma>2"
  shows "(t, s) \<in> qrstep_r_p_s nfs Q2 R2 r2 p2 \<sigma>2 O qrstep_r_p_s nfs Q1 R1 r1 p1 \<sigma>1"
proof -
  let ?R1 = "qrstep_r_p_s nfs Q1 R1"
  let ?R2 = "qrstep_r_p_s nfs Q2 R2"
  from two obtain u where tu: "(t,u) \<in> ?R1 r1 p1 \<sigma>1" and us: "(u,s) \<in> ?R2 r2 p2 \<sigma>2" by auto
  from tu[unfolded qrstep_r_p_s_def]
  have step1: "t |_ p1 = fst r1 \<cdot> \<sigma>1" "\<forall> u \<lhd> fst r1 \<cdot> \<sigma>1. u \<in> NF_terms Q1" and r1: "r1 \<in> R1"
    and p1: "p1 \<in> poss t" and u: "u = replace_at t p1 (snd r1 \<cdot> \<sigma>1)"
    and nfs1: "NF_subst nfs r1 \<sigma>1 Q1" by auto
  from us[unfolded qrstep_r_p_s_def, simplified]
  have step2: "u |_ p2 = fst r2 \<cdot> \<sigma>2" "\<forall> u \<lhd> fst r2 \<cdot> \<sigma>2. u \<in> NF_terms Q2" and r2: "r2 \<in> R2"
    and p2: "p2 \<in> poss u" and s: "s = replace_at u p2 (snd r2 \<cdot> \<sigma>2)"
    and nfs2: "NF_subst nfs r2 \<sigma>2 Q2" by auto
  from parallel_poss_replace_at[OF p12 p1] p2 have p2': "p2 \<in> poss t" unfolding u by simp
  have one: "(t,replace_at t p2 (snd r2 \<cdot> \<sigma>2)) \<in> ?R2 r2 p2 \<sigma>2" (is "(t,?t) \<in> _") unfolding qrstep_r_p_s_def
    apply (intro CollectI, unfold split)
    apply (unfold step2(1)[symmetric] u parallel_replace_at_subt_at[OF p12 p1 p2'])
    apply (intro conjI p2' r2 refl nfs2)
    by (metis p1 p12 p2' parallel_replace_at_subt_at step2(1) step2(2) u)
  have p21: "p2 \<bottom> p1" by (rule parallel_pos_sym[OF p12])
  have p1': "p1 \<in> poss ?t" using parallel_poss_replace_at[OF p21 p2'] p1 by simp
  have two: "(?t,replace_at ?t p1 (snd r1 \<cdot> \<sigma>1)) \<in> ?R1 r1 p1 \<sigma>1" (is "(_,?t') \<in> _") unfolding qrstep_r_p_s_def
    apply (intro CollectI, unfold split)
    apply (intro conjI p1' r1 nfs1 refl)
    subgoal by (rule step1(2))
    subgoal by (unfold step1(1)[symmetric] parallel_replace_at_subt_at[OF p21 p2' p1], simp)
    done
  with one have steps: "(t,?t') \<in> ?R2 r2 p2 \<sigma>2 O ?R1 r1 p1 \<sigma>1" by auto
  have "s = ?t'" unfolding s u
    by (rule parallel_replace_at[OF p12 p1 p2'])
  then show ?thesis using steps  by auto
qed


lemma normalize_subterm_qrsteps_count:
  assumes p: "p \<in> poss t"
    and steps: "(t, s) \<in> (qrstep nfs Q R)^^n"
    and s: "s \<in> NF_terms Q"
  shows "\<exists> n1 n2 u. (t |_ p, u) \<in> (qrstep nfs Q R)^^n1 \<and> u \<in> NF_terms Q \<and> (replace_at t p u, s) \<in> (qrstep nfs Q R)^^n2 \<and> n = n1 + n2"
proof -
  let ?Q = "\<lambda> n n1 n2 t u s. (t |_ p, u) \<in> (qrstep nfs Q R)^^n1 \<and> u \<in> NF_terms Q \<and> (replace_at t p u, s) \<in> (qrstep nfs Q R)^^n2 \<and> n = n1 + n2"
  let ?P = "\<lambda> n t s. (\<exists> n1 n2 u. ?Q n n1 n2 t u s)"
  have "?P n t s" using steps s p
  proof (induct n arbitrary: t s)
    case 0
    then have t: "t \<in> NF_terms Q" and p: "p \<in> poss t" and s: "s = t" by auto
    show "\<exists> n1 n2 u. ?Q 0 n1 n2 t u s"
    proof (rule exI[of _ 0], rule exI[of _ 0], rule exI[of _ "t |_ p"], intro conjI)
      from p have "t |_ p \<unlhd> t" by (rule subt_at_imp_supteq)
      from NF_subterm[OF t this]
      show "t |_ p \<in> NF_terms Q" .
    next
      have "replace_at t p (t |_ p) = t" using p by (rule ctxt_supt_id)
      then show "(replace_at t p (t |_ p),s) \<in> (qrstep nfs Q R)^^0" unfolding s by simp
    qed auto
  next
    case (Suc n)
    then have p: "p \<in> poss t" by simp
    from relpow_Suc_D2[OF Suc(2)] obtain u where tu: "(t,u) \<in> qrstep nfs Q R" and us: "(u,s) \<in> qrstep nfs Q R ^^ n" by auto
    note ind = Suc(1)[OF us Suc(3)]
    from tu[unfolded qrstep_qrstep_r_p_s_conv]
    obtain r p' \<sigma> where tu': "(t,u) \<in> qrstep_r_p_s nfs Q R r p' \<sigma>" by auto
    from tu'[unfolded qrstep_r_p_s_def]
    have NF: "\<forall> u \<lhd> fst r \<cdot> \<sigma>. u \<in> NF_terms Q" and p': "p' \<in> poss t" and r: "r \<in> R" and t: "t |_ p' = fst r \<cdot> \<sigma>"
      and u: "u = replace_at t p' (snd r \<cdot> \<sigma>)"
      and nfsr: "NF_subst nfs r \<sigma> Q" by auto
    from pos_cases have cases: "p \<le>\<^sub>p p' \<or> p' <\<^sub>p p \<or> p \<bottom> p'" .
    {
      assume pp': "p \<le>\<^sub>p p'"
      then obtain p'' where p'': "p' = p @ p''" unfolding less_eq_pos_def by auto
      from p' p'' have tp'': "p'' \<in> poss (t |_ p)" by simp
      from t have t: "t |_ p |_ p'' = fst r \<cdot> \<sigma>" unfolding p'' subt_at_append[OF p] .
      from replace_at_below_poss[OF p' pp'] have pu: "p \<in> poss u" unfolding u .
      from ind[OF this] obtain n1 n2 w where steps1: "(u |_ p, w) \<in> qrstep nfs Q R ^^ n1" and w: "w \<in> NF_terms Q"
        and steps2: "(replace_at u p w, s) \<in> qrstep nfs Q R ^^ n2" and sum: "n = n1 + n2" by auto
      have tu: "ctxt_of_pos_term p t = ctxt_of_pos_term p u" unfolding u by
        (simp add: ctxt_of_pos_term_replace_at_below[OF p pp'])
      have "(t |_ p, u |_ p) \<in> qrstep_r_p_s nfs Q R r p'' \<sigma>" unfolding qrstep_r_p_s_def
        apply (intro CollectI, unfold split)
        apply (intro conjI NF tp'' r t nfsr)
        by (unfold u p'' ctxt_of_pos_term_append[OF p], simp add: replace_at_subt_at[OF p])
      then have "(t |_ p, u |_ p) \<in> qrstep nfs Q R" unfolding qrstep_qrstep_r_p_s_conv by blast
      from relpow_Suc_I2[OF this steps1] have steps1: "(t |_ p, w) \<in> qrstep nfs Q R ^^ Suc n1" .
      have ?case
        apply (intro exI conjI)
           apply (rule steps1)
          apply (rule w)
         apply (unfold tu, rule steps2)
        by (unfold sum, simp)
    } note above = this
    {
      assume p'p: "p' <\<^sub>p p"
      from less_pos_imp_supt[OF p'p p] have "t |_ p \<lhd> t |_ p'" .
      with NF[unfolded t[symmetric]] have tp: "t |_ p \<in> NF_terms Q" by blast
      have steps1: "(t |_ p, t |_ p) \<in> qrstep nfs Q R ^^ 0" by simp
      have ?case
        apply (intro exI conjI)
           apply (rule steps1)
          apply (rule tp)
         apply (unfold ctxt_supt_id[OF p], rule Suc(2))
        by simp
    } note below = this
    {
      assume pp': "p \<bottom> p'"
      from parallel_pos_sym[OF this] have p'p: "p' \<bottom> p" .
      from parallel_poss_replace_at[OF this p'] p  have pu: "p \<in> poss u" unfolding u by blast
      from ind[OF this] obtain n1 n2 w where steps1: "(u |_ p, w) \<in> qrstep nfs Q R ^^ n1" and w: "w \<in> NF_terms Q"
        and steps2: "(replace_at u p w, s) \<in> qrstep nfs Q R ^^ n2" and sum: "n = n1 + n2" by auto
      from parallel_replace_at_subt_at[OF p'p p' p] have uptp: "u |_ p = t |_ p" unfolding u .
      have ?case
      proof (intro exI conjI, rule steps1[unfolded uptp], rule w)
        show "Suc n = n1 + Suc n2" unfolding sum by simp
      next
        from r have r: "(fst r, snd r) \<in> R" by simp
        have "(replace_at t p w, replace_at u p w) \<in> qrstep nfs Q R" unfolding u
          unfolding parallel_replace_at[OF p'p p' p]
          by (rule parallel_qrstep[OF pp' p p' t NF r], insert nfsr, auto)
        from relpow_Suc_I2[OF this steps2]
        show "(replace_at t p w, s) \<in> qrstep nfs Q R ^^ (Suc n2)" .
      qed
    } note parallel = this
    from cases above below parallel show ?case by blast
  qed
  then show ?thesis by auto
qed

lemma normalize_subterm_qrsteps:
  assumes p: "p \<in> poss t"
    and steps: "(t, s) \<in> (qrstep nfs Q R)\<^sup>*"
    and s: "s \<in> NF_terms Q"
  shows "\<exists> u. (t |_ p, u) \<in> (qrstep nfs Q R)\<^sup>* \<and> u \<in> NF_terms Q \<and> (replace_at t p u, s) \<in> (qrstep nfs Q R)\<^sup>*"
proof -
  from rtrancl_imp_relpow[OF steps] obtain n where steps: "(t,s) \<in> qrstep nfs Q R ^^ n" by auto
  from normalize_subterm_qrsteps_count[OF p steps s]
  obtain n1 n2 u where steps1: "(t |_ p, u) \<in> qrstep nfs Q R ^^ n1" and u: "u \<in> NF_terms Q"
    and steps2: "(replace_at t p u, s) \<in> qrstep nfs Q R ^^ n2" by auto
  from relpow_imp_rtrancl[OF steps1] relpow_imp_rtrancl[OF steps2] u show ?thesis by blast
qed


lemma parallel_qrstep_r_p_s:
  fixes p1 :: pos
  assumes p12: "p1 \<bottom> p2"
    and p1: "p1 \<in> poss t"
    and step: "(t, s) \<in> qrstep_r_p_s nfs Q R lr p2 \<sigma>"
  shows "(replace_at t p1 w, replace_at s p1 w) \<in> qrstep nfs Q R" (is "(?one,?two) \<in> _")
proof -
  note d = qrstep_r_p_s_def
  from step[unfolded d] have NF: "\<forall> u \<lhd> fst lr \<cdot> \<sigma>. u \<in> NF_terms Q"
    and p2: "p2 \<in> poss t" and lr: "lr \<in> R" and subt: "t |_ p2 = fst lr \<cdot> \<sigma>"
    and s: "s = replace_at t p2 (snd lr \<cdot> \<sigma>)"
    and nfs: "NF_subst nfs lr \<sigma> Q" by auto
  show ?thesis unfolding qrstep_qrstep_r_p_s_conv
  proof (intro exI)
    show "(?one,?two) \<in> qrstep_r_p_s nfs Q R lr p2 \<sigma>"
      unfolding d
      apply (intro CollectI, unfold split fst_conv snd_conv)
      apply (unfold parallel_replace_at_subt_at[OF p12 p1 p2])
      apply (intro conjI NF subt lr nfs)
      using s parallel_poss_replace_at[OF p12 p1] p2 parallel_replace_at[OF p12 p1 p2]
      by auto
  qed
qed

text \<open>the advantage of the following lemma is the fact, that w.l.o.g. for
  termination analysis one can first reduce the argument s of the context to Q-normal form\<close>
(* on the first view it seems that SN_C is subsumed by SN_replace, but this is not the
   case, as it might be that all normal forms of s w.r.t. -Q\<rightarrow>R are not in Q-NF *)
lemma normalize_subterm_SN:
  assumes SN_s: "SN_on (qrstep nfs Q R) {s}"
  and SN_replace: "\<And> t. (s,t) \<in> (qrstep nfs Q R)\<^sup>* \<Longrightarrow> t \<in> NF_terms Q \<Longrightarrow> SN_on (qrstep nfs Q R) { C\<langle>t\<rangle> }"
  and SN_C: "SN_on (qrstep nfs Q R) (set (ctxt_to_term_list C))"
  shows "SN_on (qrstep nfs Q R) { C\<langle>s\<rangle> }" (is "SN_on ?R _")
proof
  fix f
  assume "f 0 \<in> {C\<langle>s\<rangle>}" and steps: "\<forall> i. (f i, f (Suc i)) \<in> ?R"
  then have zero: "f 0 = C\<langle>s\<rangle>" by auto
  from choice[OF steps[unfolded qrstep_qrstep_r_p_s_conv]]
  obtain lr where "\<forall> i. \<exists> p \<sigma>. (f i, f (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) p \<sigma>" by auto
  from choice[OF this] obtain p where "\<forall> i. \<exists> \<sigma>. (f i, f (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) \<sigma>" by auto
  from choice[OF this] obtain \<sigma> where steps: "\<And> i. (f i, f (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<sigma> i)" by auto
  let ?p = "hole_pos C"
  {
    fix i
    assume below_or_par: "\<And> j. j < i \<Longrightarrow> ?p \<le>\<^sub>p p j \<or> ?p \<bottom> p j"
    {
      fix j
      assume j: "j \<le> i"
      then have "?p \<in> poss (f j) \<and> (s,f j |_ ?p) \<in> ?R\<^sup>*"
      proof (induct j)
        case 0
        show ?case unfolding zero by simp
      next
        case (Suc j)
        then have p: "?p \<in> poss (f j)" and ssteps: "(s, f j |_ ?p) \<in> ?R\<^sup>*" by auto
        from Suc(2) have "j < i" by auto
        from below_or_par[OF this]
        show ?case
        proof
          assume True: "?p \<le>\<^sub>p p j"
          then obtain q where q: "?p @ q = p j" unfolding less_eq_pos_def by auto
          from qrstep_subt_at_gen[OF steps[of j, unfolded q[symmetric]]]
          have step: "(f j |_ ?p, f (Suc j) |_ ?p) \<in> ?R" unfolding qrstep_qrstep_r_p_s_conv by blast
          from steps[of j, unfolded qrstep_r_p_s_def]
          have id: "f (Suc j) = replace_at (f j) (p j) (snd (lr j) \<cdot> \<sigma> j)" and pi: "p j \<in> poss (f j)" by auto
          from replace_at_below_poss[OF pi True] ssteps step
          show ?thesis unfolding id by auto
        next
          assume par: "?p \<bottom> p j"
          from parallel_qrstep_subt_at[OF steps[of j] parallel_pos_sym[OF par] p] ssteps
          show ?thesis by auto
        qed
      qed
    }
    then have "?p \<in> poss (f i) \<and> (s, f i |_ ?p) \<in> ?R\<^sup>*" by auto
  } note poss_rewrite = this
  show False
  proof (cases "\<exists> i. p i <\<^sub>p ?p")
    case False
    {
      fix i
      from False have "\<not> (p i <\<^sub>p ?p)"  by auto
      with pos_cases[of ?p "p i"] have "?p \<le>\<^sub>p p i \<or> ?p \<bottom> p i" by auto
    } note below_or_par = this
    from poss_rewrite[OF this]
    have p: "\<And> i. ?p \<in> poss (f i)" ..
    from below_or_par
    have "(INFM i. ?p \<le>\<^sub>p p i) \<or> \<not> (INFM i. ?p \<le>\<^sub>p p i)" by auto
    then show False
    proof
      assume inf: "INFM i. ?p \<le>\<^sub>p p i"
      let ?i = "\<lambda> i. ?p \<le>\<^sub>p p i"
      interpret infinitely_many ?i
        by (unfold_locales, rule inf)
      obtain g where g: "g = (\<lambda> i. f i |_ ?p)" by auto
      {
        fix i
        from index_p[of i]
        obtain q where q: "?p @ q = p (index i)" unfolding less_eq_pos_def by auto
        from qrstep_subt_at_gen[OF steps[of "index i", unfolded q[symmetric]]]
        have "(g (index i), g (Suc (index i))) \<in> ?R" unfolding g qrstep_qrstep_r_p_s_conv by blast
      } note gsteps = this
      {
        fix i
        assume "\<not> ?i i"
        with below_or_par[of i] have par: "?p \<bottom> p i" by simp
        from parallel_qrstep_subt_at[OF steps[of i] parallel_pos_sym[OF par] p]
        have "g i = g (Suc i)" unfolding g by simp
      } note gid = this
      obtain h where h: "h = (\<lambda> i. g (index i))" by auto
      {
        fix i
        from index_ordered[of i] have "Suc (index i) \<le> index (Suc i)" by simp
        then have  "\<exists> j. index (Suc i) = Suc (index i) + j" by arith
        then obtain j where id: "index (Suc i) = Suc (index i) + j" by auto
        {
          fix j
          assume "Suc (index i) + j \<le> index (Suc i)"
          then have "g (Suc (index i)) = g (Suc (index i) + j)"
          proof (induct j)
            case 0 show ?case by simp
          next
            case (Suc j)
            then have "g (Suc (index i)) = g (Suc (index i) + j)" by simp
            also have "... = g (Suc (Suc (index i) + j))"
              by (rule gid[OF index_not_p_between, of i], insert Suc(2), auto)
            finally show ?case by simp
          qed
        }
        from this[of j] have "g (Suc (index i)) = h (Suc i)" unfolding h id by simp
        with gsteps[of i] have "(h i, h (Suc i)) \<in> ?R" unfolding h by simp
      }
      then have "\<not> SN_on ?R {h 0}" by auto
      then have nSN: "\<not> SN_on ?R {g (index 0)}" unfolding h .
      obtain iz where iz: "iz = index 0" by auto
      from gid[OF index_not_p_start] have "\<And> i. i < iz \<Longrightarrow> g i = g (Suc i)" unfolding iz by auto
      then have "g 0 = g iz"
        by (induct iz, auto)
      with nSN have nSN: "\<not> SN_on ?R {g 0}" unfolding iz  by simp
      with SN_s show False unfolding g zero by simp
    next
      assume inf: "\<not> (INFM i. ?p \<le>\<^sub>p p i)"
      let ?cc = "\<lambda> i. ctxt_to_term_list (ctxt_of_pos_term ?p (f i))"
      let ?step = "\<lambda> i j n. j < n \<and> (?cc i ! j, ?cc (Suc i) ! j) \<in> ?R \<and> (\<forall> k. k \<noteq> j \<longrightarrow> ?cc (Suc i) ! k = ?cc i ! k) \<and> length (?cc (Suc i)) = n"
      {
        fix i
        assume "?p \<bottom> p i"
        from parallel_qrstep_ctxt_to_term_list[OF this p steps]
        obtain p' j where p': "p' \<le>\<^sub>p p i" and j: "j < length (?cc i)"
          and i: "?cc i ! j = f i |_ p'"
          and si: "?cc (Suc i) = (?cc i) [ j := f (Suc i) |_ p']" by blast+
        from si have len: "length (?cc (Suc i)) = length (?cc i)" by simp
        from p' obtain q where p': "p' @ q = p i" unfolding less_eq_pos_def by blast
        then have pi: "p i = p' @ q" by simp
        from qrstep_subt_at_gen[OF steps[of i, unfolded pi]]
        have "(?cc i ! j, ?cc (Suc i) ! j) \<in> qrstep_r_p_s nfs Q R (lr i) q (\<sigma> i)" unfolding i si using j
          by auto
        then have step: "(?cc i ! j, ?cc (Suc i) ! j) \<in> ?R" unfolding qrstep_qrstep_r_p_s_conv by blast
        have id: "\<forall> k. k \<noteq> j \<longrightarrow> ?cc (Suc i) ! k = ?cc i ! k" unfolding si by auto
        from step id j have "\<exists> j. ?step i j (length (?cc i))"
          unfolding len by blast
      } note par_step = this
      {
        fix i
        assume "\<not> (?p \<bottom> p i)"
        with below_or_par have "?p \<le>\<^sub>p p i" by auto
        from ctxt_of_pos_term_qrstep_below[OF steps this]
        have "?cc (Suc i) = ?cc i" by simp
      } note below_step = this
      obtain n where n: "n = length (?cc 0)" by simp
      {
        fix i
        have "length (?cc i) = n"
        proof (induct i)
          case 0 show ?case unfolding n by simp
        next
          case (Suc i)
          then show ?case
            using below_step[of i] par_step[of i]
            by (cases "?p \<bottom> p i", auto)
        qed
      } note len = this
      from par_step have par_step: "\<And> i. ?p \<bottom> p i \<Longrightarrow> (\<exists> j. ?step i j n)" unfolding len by simp
      from inf obtain k where par: "\<And> j. j \<ge> k \<Longrightarrow> \<not> ?p \<le>\<^sub>p p j" unfolding INFM_nat_le by auto
      with below_or_par have par: "\<And> j. j \<ge> k \<Longrightarrow> ?p \<bottom> p j" by auto
      let ?jstep = "\<lambda> i j. (?cc (i + k) ! j, ?cc (Suc i + k) ! j) \<in> ?R"
      {
        fix i
        have "i + k \<ge> k" by simp
        from par_step[OF par[OF this]]
        obtain j where j: "j < n" and step: "?jstep i j" by auto
        then have "\<exists> j < n. ?jstep i j" by blast
      }
      then have "\<forall> i. \<exists> j < n. ?jstep i j" by blast
      from inf_pigeonhole_principle[OF this] obtain j where j: "j < n" and steps: "\<And> i. \<exists> i' \<ge> i. ?jstep i' j" by blast
      let ?t = "\<lambda> i. ?cc i ! j"
      {
        fix i
        have "(?t i, ?t (Suc i)) \<in> ?R^="
        proof (cases "?p \<bottom> p i")
          case False
          from below_step[OF this] show ?thesis by simp
        next
          case True
          from par_step[OF this]
          obtain k where "?step i k n" by auto
          then show ?thesis by (cases "k = j", auto)
        qed
      } then have rsteps: "\<forall> i. (?t i, ?t (Suc i)) \<in> Id \<union> ?R" by blast
      from j[unfolded len[of 0, symmetric]] have t0: "?t 0 \<in> set (ctxt_to_term_list C)"
        unfolding zero set_conv_nth by auto
      with SN_C have SN: "SN_on ?R {?t 0}" unfolding SN_on_def by simp
      from non_strict_ending[OF rsteps] SN
      obtain k'' where "\<forall> k' \<ge> k''. (?t k', ?t (Suc k')) \<notin> ?R" by blast
      with steps[of k''] show False by auto
    qed
  next
    case True
    let ?P = "\<lambda> i. p i <\<^sub>p ?p"
    from LeastI_ex[of ?P, OF True] have "?P (LEAST i. ?P i)" .
    then obtain i where i: "i = (LEAST i. ?P i)" and pi: "?P i" by auto
    {
      fix j
      assume j: "j < i"
      from not_less_Least[OF this[unfolded i]] have "\<not> ?P j" .
      with pos_cases[of ?p "p j"] have "?p \<le>\<^sub>p p j \<or> ?p \<bottom> p j" by auto
    } note below_or_par = this
    from poss_rewrite[OF this]
    have p: "?p \<in> poss (f i)" and rewr: "(s,f i |_ ?p) \<in> ?R\<^sup>*" by auto
    from steps[of i, unfolded qrstep_r_p_s_def] have NF: "\<And> u. u \<lhd> f i |_ p i \<Longrightarrow> u \<in> NF_terms Q" by auto
    from NF[OF less_pos_imp_supt[OF pi p]] have NF: "f i |_ ?p \<in> NF_terms Q" .
    from SN_replace[OF rewr NF] have SN: "SN_on ?R {C\<langle>f i |_ ?p\<rangle>}" .
    {
      fix w
      from below_or_par have "(C\<langle>w\<rangle>,replace_at (f i) ?p w) \<in> ?R\<^sup>*"
      proof (induct i)
        case 0
        show ?case unfolding zero by simp
      next
        case (Suc i)
        then have steps': "(C\<langle>w\<rangle>, replace_at (f i) ?p w) \<in> ?R\<^sup>*" by auto
        from poss_rewrite[OF Suc(2)] have p: "?p \<in> poss (f i)" by auto
        from Suc(2)[of i] have "?p \<le>\<^sub>p p i \<or> ?p \<bottom> p i" by auto
        then have "(replace_at (f i) ?p w, replace_at (f (Suc i)) ?p w) \<in> ?R\<^sup>*"
        proof
          assume "?p \<bottom> p i"
          from parallel_qrstep_r_p_s[OF this p  steps[of i]]
          show ?thesis by auto
        next
          assume "?p \<le>\<^sub>p p i"
          from ctxt_of_pos_term_replace_at_below[OF p this]
          have "replace_at (f (Suc i)) ?p w = replace_at (f i) ?p w"
            using steps[of i, unfolded qrstep_r_p_s_def] by auto
          then show ?thesis by auto
        qed
        with steps' show ?case by auto
      qed
    }
    from this[of "f i |_ ?p"] have steps': "(C\<langle>f i |_ ?p\<rangle>, f i) \<in> ?R\<^sup>*"
      unfolding ctxt_supt_id[OF p] .
    obtain g where g: "g = (\<lambda> j. f (j + i))" by auto
    from steps_preserve_SN_on[OF steps' SN] have SN: "SN_on ?R {g 0}" unfolding g by auto
    {
      fix j
      from steps[of "j + i"] have "(f (j + i), f (Suc (j + i))) \<in> ?R"
        unfolding qrstep_qrstep_r_p_s_conv by blast
      then have "(g j, g (Suc j)) \<in> ?R" unfolding g by auto
    }
    then have "\<not> SN_on ?R {g 0}" by auto
    with SN show False by simp
  qed
qed

lemma NF_rstep_supt_args_conv:
  "(\<forall>u\<lhd>t. u \<in> NF (rstep R)) = (\<forall>u\<in>set (args t). u \<in> NF (rstep R))"
proof (cases t)
  case (Var x) show ?thesis unfolding Var by auto
next
  case (Fun f ts)
  show ?thesis (is "?lhs = ?rhs")
  proof
    assume "?lhs" then show "?rhs" by (auto simp: Fun)
  next
    assume "?rhs" show "?lhs"
    proof (intro allI impI)
      fix u assume "u \<lhd> t"
      from supt_Fun_imp_arg_supteq[OF this[unfolded Fun]]
        obtain t where "t \<in> set ts" and "t \<unrhd> u" by best
      from \<open>?rhs\<close>[unfolded Fun] and \<open>t \<in> set ts\<close> have "t \<in> NF (rstep R)" by simp
      from this and \<open>t \<unrhd> u\<close> show "u \<in> NF (rstep R)" by (rule NF_subterm)
    qed
  qed
qed

lemma NF_terms_args_conv:
  "(\<forall>u\<in>set (args t). u \<in> NF_terms T) = (\<forall>u\<lhd>t. u \<in> NF_terms T)"
using NF_rstep_supt_args_conv[symmetric,of t "Id_on T"] .

lemma ctxt_closed_qrstep [intro]: "ctxt.closed (qrstep nfs Q R)"
unfolding ctxt.closed_def
proof (rule subrelI)
  fix s t
  assume "(s, t) \<in> ctxt.closure (qrstep nfs Q R)"
  then show "(s, t) \<in> qrstep nfs Q R" by induct auto
qed

lemma qrsteps_ctxt_closed:
  assumes "(s, t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (qrstep nfs Q R)\<^sup>*"
  by (rule ctxt.closedD[OF _ assms], blast)


lemma not_NF_rstep_minimal:
  assumes "s \<notin> NF (rstep R)"
  shows "\<exists>t\<unlhd>s. t \<notin> NF (rstep R) \<and> (\<forall>u\<lhd>t. u \<in> NF (rstep R))"
using assms proof (induct s rule: subterm_induct)
  case (subterm v)
  then show ?case
  proof (cases "\<forall>w\<lhd>v. w \<in> NF (rstep R)")
    case True with subterm(2) show ?thesis by auto
  next
    case False
    then obtain w where "v \<rhd> w" and "w \<notin> NF (rstep R)" by auto
    with subterm(1) obtain t where "w \<unrhd> t" and notNF: "t \<notin> NF (rstep R)"
      and NF: "\<forall>u\<lhd>t. u \<in> NF (rstep R)" by auto
    from \<open>v \<rhd> w\<close> and \<open>w \<unrhd> t\<close> have "v \<unrhd> t" using supt_supteq_trans[of v w t] by auto
    with notNF and NF show ?thesis by auto
  qed
qed

lemma Var_NF_terms: assumes no_lhs_var: "\<And> l. l \<in> Q \<Longrightarrow> is_Fun l"
  shows "Var x \<in> NF_terms Q"
proof (rule ccontr)
   assume "Var x \<notin> NF_terms Q"
   then obtain l C \<sigma> where l: "l \<in> Q" and x: "Var x = C \<langle> l \<cdot> \<sigma> \<rangle>" by blast
   from x have "Var x = l \<cdot> \<sigma>" by (cases C, auto)
   with no_lhs_var[OF l] show False by auto
qed

lemma rstep_imp_irstep:
  assumes st: "(s, t) \<in> rstep R" and no_lhs_var: "\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "\<exists>u. (s, u) \<in> irstep nfs R"
proof -
  from assms have "s \<notin> NF (rstep R)" by auto
  from not_NF_rstep_minimal[OF this] obtain u where "s \<unrhd> u" and notNF: "u \<notin> NF (rstep R)"
    and NF: "\<forall>w\<lhd>u. w \<in> NF (rstep R)" by auto
  from notNF obtain v where "(u, v) \<in> rstep R" by auto
  then obtain l r C \<sigma> where "(l, r) \<in> R" and u: "u = C\<langle>l \<cdot> \<sigma>\<rangle>" and v: "v = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from u have "u \<unrhd> l \<cdot> \<sigma>" by auto
  have nf: "\<forall>w\<lhd>l \<cdot> \<sigma>. w \<in> NF (rstep R)"
  proof (intro allI impI)
    fix w assume "l \<cdot> \<sigma> \<rhd> w"
   with \<open>u \<unrhd> l \<cdot> \<sigma>\<close> have "u \<rhd> w" by (rule supteq_supt_trans)
   with NF show "w \<in> NF (rstep R)" by auto
  qed
  let ?sigma = "\<lambda> x. if x \<in> vars_term l then \<sigma> x else Var x"
  obtain v where v: "v = C \<langle> r \<cdot> ?sigma \<rangle>" by auto
  have lsig: "l \<cdot> \<sigma> = l \<cdot> ?sigma"
    by (rule term_subst_eq, auto)
  have "NF_subst nfs (l,r) ?sigma (lhss R)"
    unfolding NF_subst_def
  proof (intro impI subsetI)
    fix t
    assume nfs: nfs
    assume "t \<in> ?sigma ` vars_rule (l,r)"
    then obtain x where x: "x \<in> vars_rule (l,r)" and t: "t = ?sigma x" by auto
    show "t \<in> NF_terms (lhss R)"
    proof (cases "x \<in> vars_term l")
      case True
      then have "Var x \<unlhd> l" by auto
      with no_lhs_var[OF nfs \<open>(l,r) \<in> R\<close>] have "Var x \<lhd> l" by (cases l, auto)
      then have "Var x \<cdot> \<sigma> \<lhd> l \<cdot> \<sigma>" by (rule supt_subst)
      with nf show ?thesis unfolding t using True by simp
    next
      case False
      then have t: "t = Var x" unfolding t by auto
      show ?thesis unfolding t
        by (rule Var_NF_terms, insert no_lhs_var[OF nfs], auto)
    qed
  qed
  with nf \<open>(l, r) \<in> R\<close> and u and v have "(u, v) \<in> irstep nfs R"
    unfolding irstep_def and NF_terms_lhss[symmetric, of R] lsig by blast
  from \<open>s \<unrhd> u\<close> obtain C where "s = C\<langle>u\<rangle>" by auto
  from \<open>(u, v) \<in> irstep nfs R\<close> have "(C\<langle>u\<rangle>, C\<langle>v\<rangle>) \<in> irstep nfs R" unfolding irstep_def by auto
  then show ?thesis unfolding \<open>s = C\<langle>u\<rangle>\<close> by best
qed

lemma NF_irstep_NF_rstep:
  assumes no_lhs_var: "\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "NF (irstep nfs R) = NF (rstep R)"
proof -
  have "irstep nfs R \<subseteq> rstep R" unfolding irstep_def ..
  from NF_anti_mono[OF this] have "NF (rstep R) \<subseteq> NF (irstep nfs R)" .
  moreover have "NF (irstep nfs R) \<subseteq> NF (rstep R)"
  proof
    fix s assume "s \<in> NF (irstep nfs R)" show "s \<in> NF (rstep R)"
    proof (rule ccontr)
      assume "s \<notin> NF (rstep R)"
      then obtain t where "(s, t) \<in> rstep R" by auto
      from rstep_imp_irstep[OF this no_lhs_var, of nfs]
        obtain u where "(s, u) \<in> irstep nfs R" by force
      with \<open>s \<in> NF (irstep nfs R)\<close> show False by auto
    qed
  qed
  ultimately show ?thesis by simp
qed


definition
  applicable_rule :: "('f, 'v) terms \<Rightarrow> ('f, 'v) rule \<Rightarrow> bool"
where
  "applicable_rule Q lr \<equiv> \<forall>s\<lhd>fst lr. s \<in> NF_terms Q"

lemma applicable_rule_empty: "applicable_rule {} lr"
unfolding applicable_rule_def by auto

lemma only_applicable_rules:
  assumes "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
  shows "applicable_rule Q (l, r)"
unfolding applicable_rule_def
proof (intro allI impI)
  fix s assume "fst (l, r) \<rhd> s"
  then have "l \<rhd> s" by simp
  then have "l \<cdot> \<sigma> \<rhd> s \<cdot> \<sigma>" by (rule supt_subst)
  with assms have "s \<cdot> \<sigma> \<in> NF_terms Q" by simp
  from NF_instance[OF this] show "s \<in> NF_terms Q" .
qed

definition
  applicable_rules :: "('f, 'v) terms \<Rightarrow> ('f, 'v) trs  \<Rightarrow> ('f, 'v) trs"
where
  "applicable_rules Q R \<equiv> {(l, r) | l r. (l, r) \<in> R \<and> applicable_rule Q (l, r)}"

lemma applicable_rules_union: "applicable_rules Q (R \<union> S) = applicable_rules Q R \<union> applicable_rules Q S"
  unfolding applicable_rules_def by auto

lemma applicable_rules_empty[simp]:
  "applicable_rules {} R = R"
unfolding applicable_rules_def using applicable_rule_empty by auto

lemma applicable_rules_subset: "applicable_rules Q R \<subseteq> R"
unfolding applicable_rules_def applicable_rule_def by auto

lemma qrstep_applicable_rules: "qrstep nfs Q (applicable_rules Q R) = qrstep nfs Q R"
proof -
  let ?U = "applicable_rules Q R"
  show ?thesis
  proof
    show "qrstep nfs Q ?U \<subseteq> qrstep nfs Q R" by (rule qrstep_rules_mono[OF applicable_rules_subset])
  next
    show "qrstep nfs Q R \<subseteq> qrstep nfs Q ?U"
    proof (rule subrelI)
      fix s t
      assume "(s,t) \<in> qrstep nfs Q R"
      then obtain l r C \<sigma> where "(l, r) \<in> R" and NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
        and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
        and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
      with only_applicable_rules[OF NF] have "(l, r) \<in> ?U" by (auto simp: applicable_rules_def)
      with NF and \<open>(l, r) \<in> R\<close> and s and t and nfs show "(s, t) \<in> qrstep nfs Q ?U" by auto
    qed
  qed
qed

lemma ndef_applicable_rules: "\<not> defined R x \<Longrightarrow> \<not> defined (applicable_rules Q R) x"
  unfolding defined_def applicable_rules_def by auto

lemma nvar_qrstep_Fun:
  assumes nvar: "\<forall> (l, r) \<in> R. is_Fun l"
    and step: "(s, t) \<in> qrstep nfs Q R"
  shows "\<exists>f ts. s = Fun f ts"
proof (cases s)
  case (Var x)
  from step obtain C \<sigma> l r where x: "Var x = C\<langle>l \<cdot> \<sigma>\<rangle>" and lr: "(l, r) \<in> R" unfolding Var
    by auto
  from nvar lr obtain f ls where l: "l = Fun f ls" by (cases l, auto)
  then show ?thesis using x by (cases C, auto)
qed auto


text \<open>weakly well-formedness (all applicable rules are well-formed).\<close>

definition
  wwf_rule :: "('f, 'v) terms \<Rightarrow> ('f, 'v) rule \<Rightarrow> bool"
where
  "wwf_rule Q lr \<equiv>
    applicable_rule Q lr \<longrightarrow> (is_Fun (fst lr) \<and> vars_term (snd lr) \<subseteq> vars_term (fst lr))"

definition
  wwf_qtrs :: "('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "wwf_qtrs Q R \<equiv> \<forall>(l, r)\<in>R. applicable_rule Q (l, r) \<longrightarrow> (is_Fun l \<and> vars_term r \<subseteq> vars_term l)"

lemma wwf_qtrs_wwf_rules: "wwf_qtrs Q R = (\<forall>(l, r)\<in>R. wwf_rule Q (l, r))"
unfolding wwf_qtrs_def wwf_rule_def by auto

lemma wwf_qtrs_wf_trs: "wwf_qtrs Q R = wf_trs (applicable_rules Q R)"
unfolding wwf_qtrs_def wf_trs_def applicable_rules_def by force

lemma wwf_qtrs_empty: "wwf_qtrs {} R = wf_trs R"
unfolding wwf_qtrs_wf_trs applicable_rules_empty by simp

lemma left_Var_imp_not_SN_qrstep:
  assumes xr: "(Var x, r) \<in> R" and nfs: "\<not> nfs" shows "\<not> (SN_on (qrstep nfs Q R) {t})"
proof -
  have steps: "\<forall>t. \<exists>s. (t, s) \<in> qrstep nfs Q R"
  proof
    fix t
    show "\<exists>s. (t, s) \<in> qrstep nfs Q R"
    proof (induct t)
      case (Var y)
      let ?xt = "subst x (Var y)"
      let ?rxt = "r \<cdot> ?xt"
      have NF: "\<forall>u\<lhd>Var x \<cdot> ?xt. u \<in> NF_terms Q" by auto
      have "(Var x \<cdot> ?xt, ?rxt) \<in> qrstep nfs Q R"
        by (rule qrstep.subst[OF NF xr, of nfs], insert nfs, simp)
      then show ?case by auto
    next
      case (Fun f ss)
      show ?case
      proof (cases ss)
        case Nil
        let ?xt = "subst x (Fun f ss)"
        let ?rxt = "r \<cdot> ?xt"
        have "\<forall>u\<lhd>Var x \<cdot> ?xt. u \<in> NF_terms Q" unfolding Nil by auto
        from qrstep.subst[OF this xr, of nfs]
        have "(Var x \<cdot> ?xt, ?rxt) \<in> qrstep nfs Q R" using nfs by simp
        then show ?thesis by auto
      next
        case (Cons s ts)
        with Fun obtain t where step: "(s, t) \<in> qrstep nfs Q R" by auto
        let ?C = "More f [] \<box> ts"
        from Cons have id: "Fun f ss = ?C\<langle>s\<rangle>" by auto
        have "(?C\<langle>s\<rangle>, ?C\<langle>t\<rangle>) \<in> ctxt.closure (qrstep nfs Q R)" by (blast intro: step)
        with ctxt_closed_qrstep[of nfs Q R]
        have "(Fun f ss, ?C\<langle>t\<rangle>) \<in> qrstep nfs Q R"
          unfolding ctxt.closed_def id by auto
        then show ?thesis by auto
      qed
    qed
  qed
  from choice[OF this]
  obtain f where steps: "\<And> t. (t, f t) \<in> qrstep nfs Q R" by blast
  show ?thesis
    by (rule steps_imp_not_SN_on, rule steps)
qed

lemma ctxt_compose_Suc: "(C ^ Suc i)\<langle>t\<rangle> = (C ^ i)\<langle>C\<langle>t\<rangle>\<rangle>"
using ctxt_power_compose_distr[of C i "Suc 0"] by simp

lemma SN_on_imp_wwf_rule:
  assumes SN: "SN_on (qrstep nfs Q R) {t}"
    and t: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" and lr: "(l, r) \<in> R" and NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and nfs: "\<not> nfs"
  shows "wwf_rule Q (l, r)"
proof (cases "vars_term r \<subseteq> vars_term l")
  case True
  from left_Var_imp_not_SN_qrstep[of _ _ R nfs Q t] lr SN nfs have "is_Fun l" by (induct l) auto
  with True show ?thesis unfolding wwf_rule_def by auto
next
  case False
  then obtain x where "x \<in> vars_term r - vars_term l" by auto
  then have not_in_l: "x \<notin> vars_term l" by auto
  from only_applicable_rules[OF NF] have "applicable_rule Q (l,r)" .
  let ?\<delta> = "(\<lambda>y. if y = x then l \<cdot> \<sigma> else \<sigma> y)"
  have "l \<cdot> \<sigma> = l \<cdot> (\<sigma> |s (vars_term l))" by (rule coincidence_lemma)
  also have "\<dots> = l \<cdot> (?\<delta> |s (vars_term l))"
  proof (rule arg_cong[of _ _ "(\<cdot>) l"])
    show "\<sigma> |s vars_term l = ?\<delta> |s vars_term l"
    proof -
      have main: "(if y \<in> vars_term l then \<sigma> y else Var y) = 
         (if y \<in> vars_term l then if y = x then l \<cdot> \<sigma> else \<sigma> y else Var y)" for y
        by (cases "y = x", auto simp: not_in_l)
      show ?thesis unfolding subst_restrict_def by (rule ext, simp add: main)
    qed
  qed
  also have "\<dots> = l \<cdot> ?\<delta>" by (rule coincidence_lemma[symmetric])
  finally have lsld: "l \<cdot> \<sigma> = l \<cdot>?\<delta>" .
  from \<open>x \<in> vars_term r - vars_term l\<close> have in_r: "x \<in> vars_term r" by auto
  from supteq_Var[OF in_r] obtain C where "r = C\<langle>Var x\<rangle>" by auto
  then have "r \<cdot> ?\<delta> = (C \<cdot>\<^sub>c ?\<delta>)\<langle>l \<cdot> ?\<delta>\<rangle>" by (auto simp: lsld)
  then obtain C where rd:  "r \<cdot> ?\<delta> = C\<langle>l \<cdot> ?\<delta>\<rangle>" by auto
  obtain ls where ls: "l \<cdot> \<sigma> = ls" by auto
  obtain f where f: "\<And>i. f i = (C^i)\<langle>l \<cdot> ?\<delta>\<rangle>" by auto
  have steps: "chain (qrstep nfs Q R) f"
  proof
    fix i
    show "(f i, f (Suc i)) \<in> qrstep nfs Q R"
    proof
      show "\<forall>u\<lhd>l \<cdot> ?\<delta>. u \<in> NF_terms Q" unfolding lsld[symmetric] by fact
      show "(l, r) \<in> R" by fact
      show "f i = (C^i)\<langle>l \<cdot> ?\<delta>\<rangle>" by fact
      show "f (Suc i) = (C ^ i)\<langle>r \<cdot> ?\<delta>\<rangle>" using f[of "Suc i", unfolded ctxt_compose_Suc rd[symmetric]] .
    qed (insert nfs, auto)
  qed
  have start: "f 0 = l \<cdot> \<sigma>"
    by (simp add: f lsld[symmetric] ls)
  from start steps have nSN: "\<not> (SN_on (qrstep nfs Q R) {l \<cdot> \<sigma>})" unfolding SN_on_def by auto
  from not_SN_subt_imp_not_SN[OF ctxt_closed_qrstep nSN ctxt_imp_supteq] SN[simplified t]
  have False ..
  then show ?thesis ..
qed

lemma SN_imp_wwf_qtrs:
  assumes "SN (qrstep nfs Q R)" and nfs: "\<not> nfs" shows "wwf_qtrs Q R"
proof (rule ccontr)
  assume "\<not> wwf_qtrs Q R"
  then obtain l r where lr: "(l, r) \<in> R" and not_wwf: "\<not> wwf_rule Q (l, r)"
    unfolding wwf_qtrs_wwf_rules by auto
  then have applicable: "applicable_rule Q (l, r)" unfolding wwf_rule_def by auto
  from assms have SN: "SN_on (qrstep nfs Q R) {l}" unfolding SN_defs by auto
  from SN_on_imp_wwf_rule[OF SN _ lr _ nfs, of \<box> Var] and not_wwf
    have "\<not> (\<forall>u\<lhd>l. u \<in> NF_terms Q)" by auto
  then obtain u where "l \<rhd> u" and not_NF: "u \<notin> NF_terms Q" by auto
  from not_NF obtain v where "(u, v) \<in> rstep (Id_on Q)" by auto
  from \<open>l \<rhd> u\<close> obtain D where "D \<noteq> \<box>" and "l = D\<langle>u\<rangle>" by auto
  with applicable[unfolded applicable_rule_def] and \<open>(u, v) \<in> rstep (Id_on Q)\<close> show False by auto
qed

lemma left_Var_applicable: "applicable_rule Q (Var x,r)"
unfolding applicable_rule_def using Var_supt[of x] by auto

lemma wwf_qtrs_imp_left_fun:
  assumes "wwf_qtrs Q R" and "(l, r) \<in> R" shows "\<exists>f ls. l = Fun f ls"
using assms unfolding wwf_qtrs_def
using left_Var_applicable[of Q _ r] by (cases l) auto

lemma wwf_var_cond:
  assumes wwf: "wwf_qtrs Q R" shows "\<forall>(l, r)\<in>R. is_Fun l"
  using wwf_qtrs_imp_left_fun[OF wwf] by auto

definition
  rqrstep :: "bool \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
where
  "rqrstep nfs Q R =
    {(s, t). \<exists>l r \<sigma>. (\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q) \<and> (l, r) \<in> R \<and> s = l \<cdot> \<sigma> \<and> t = r \<cdot> \<sigma> \<and> NF_subst nfs (l,r) \<sigma> Q}"

lemma rqrstep_union: "rqrstep nfs Q (R \<union> S) = rqrstep nfs Q R \<union> rqrstep nfs Q S"
  unfolding rqrstep_def by blast

lemma rqrstep_rrstep_conv[simp]:
  "rqrstep nfs {} R = rrstep R"
  by (auto simp: rrstep_def' rqrstep_def)


definition
  nrqrstep :: "bool \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
where
  "nrqrstep nfs Q R =
    {(s, t). \<exists>l r C \<sigma>.
    (\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q) \<and> (l, r) \<in> R \<and> C \<noteq> \<box> \<and> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> NF_subst nfs (l,r) \<sigma> Q}"

lemma rqrstepI[intro]:
  assumes "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and "(l, r) \<in> R"
    and "s = l \<cdot> \<sigma>" and "t = r \<cdot> \<sigma>"
    and "NF_subst nfs (l,r) \<sigma> Q"
  shows "(s, t) \<in> rqrstep nfs Q R"
  using assms unfolding rqrstep_def by auto

lemma nrqrstepI[intro]:
  assumes "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and "(l, r) \<in> R"
    and "C \<noteq> \<box>" and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and "NF_subst nfs (l,r) \<sigma> Q"
  shows "(s, t) \<in> nrqrstep nfs Q R"
  using assms unfolding nrqrstep_def by auto

lemma rqrstepE[elim]:
  assumes "(s, t) \<in> rqrstep nfs Q R"
    and "\<And>l r \<sigma>. \<lbrakk>\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q; (l, r) \<in> R; s = l \<cdot> \<sigma>; t = r \<cdot> \<sigma>; NF_subst nfs (l,r) \<sigma> Q\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms unfolding rqrstep_def by auto

lemma nrqrstepE[elim]:
  assumes "(s, t) \<in> nrqrstep nfs Q R"
    and "\<And>l r C \<sigma>.
    \<lbrakk>\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q; (l, r) \<in> R; C \<noteq> \<box>; s = C\<langle>l \<cdot> \<sigma>\<rangle>; t = C\<langle>r \<cdot> \<sigma>\<rangle>; NF_subst nfs (l,r) \<sigma> Q\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms unfolding nrqrstep_def by auto

lemma rqrstep_all_mono:
  assumes R: "R \<subseteq> R'" and Q: "NF_terms Q \<subseteq> NF_terms Q'" and n: "Q \<noteq> {} \<Longrightarrow> nfs' \<Longrightarrow> nfs"
  shows "rqrstep nfs Q R \<subseteq> rqrstep nfs' Q' R'"
proof
  fix s t
  assume "(s,t) \<in> rqrstep nfs Q R"
  then obtain l r \<sigma> where s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" and lr: "(l,r) \<in> R"
    and NF: "\<And> u. u \<lhd> l \<cdot> \<sigma> \<Longrightarrow> u \<in> NF_terms Q"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q"
    by auto
  from nfs n Q have nfs: "NF_subst nfs' (l,r) \<sigma> Q'" unfolding NF_subst_def by auto
  from NF Q have NF: "\<And> u. u \<lhd> l \<cdot> \<sigma> \<Longrightarrow> u \<in> NF_terms Q'" by auto
  from lr R have lr: "(l,r) \<in> R'" by auto
  from s t lr NF nfs show "(s,t) \<in> rqrstep nfs' Q' R'" by auto
qed

lemma rqrstep_mono:
  assumes R: "R \<subseteq> R'" and Q: "NF_terms Q \<subseteq> NF_terms Q'"
  shows "rqrstep nfs Q R \<subseteq> rqrstep nfs Q' R'"
  by (rule rqrstep_all_mono[OF R Q])

lemma nrqrstep_all_mono:
  assumes "NF_terms Q \<subseteq> NF_terms Q'" and "R \<subseteq> R'" and "Q \<noteq> {} \<Longrightarrow> nfs' \<Longrightarrow> nfs"
  shows "nrqrstep nfs Q R \<subseteq> nrqrstep nfs' Q' R'"
proof
  fix s t
  assume "(s,t) \<in> nrqrstep nfs Q R"
  then obtain l r C \<sigma>
   where nf: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
   and lr: "(l, r) \<in> R" and id: "C \<noteq> \<box>" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
   and nfs: "NF_subst nfs (l,r) \<sigma> Q"
   by auto
  from assms nfs have nfs: "NF_subst nfs' (l,r) \<sigma> Q'" unfolding NF_subst_def by auto
  show "(s,t) \<in> nrqrstep nfs' Q' R'"
    by (rule nrqrstepI[OF _ _ id], insert nf nfs lr assms, unfold NF_subst_def, auto)
qed

lemma nrqrstep_mono:
  assumes "NF_terms Q \<subseteq> NF_terms Q'" and "R \<subseteq> R'"
  shows "nrqrstep nfs Q R \<subseteq> nrqrstep nfs Q' R'"
  by (rule nrqrstep_all_mono[OF assms])

lemma nrqrstep_imp_Fun_qrstep: assumes "(s,t) \<in> nrqrstep nfs Q R"
  shows "\<exists> f bef aft si ti. s = Fun f (bef @ si # aft) \<and> t = Fun f (bef @ ti # aft) \<and> (si,ti) \<in> qrstep nfs Q R"
proof -
  from nrqrstepE[OF assms] obtain l r C \<sigma> where
    nf: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and lr: "(l, r) \<in> R" and C: "C \<noteq> \<box>"
    and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and nfs:  "NF_subst nfs (l, r) \<sigma> Q" .
  from C obtain f bef D aft where C: "C = More f bef D aft" by (cases C, auto)
  from qrstepI[OF nf lr refl refl nfs, of D] show ?thesis unfolding s t C by auto
qed

lemma qrstep_funas_term: assumes wwf: "wwf_qtrs Q R"
  and RF: "funas_trs R \<subseteq> F"
  and sF: "funas_term s \<subseteq> F"
  and step: "(s,t) \<in> qrstep nfs Q R"
  shows "funas_term t \<subseteq> F"
proof -
  from qrstepE[OF step] obtain C \<sigma> l r
    where nf: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and lr: "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and nfs: "NF_subst nfs (l, r) \<sigma> Q" .
  from only_applicable_rules[OF nf] lr wwf[unfolded wwf_qtrs_def] have vars: "vars_term r \<subseteq> vars_term l" by auto
  from RF lr have rF: "funas_term r \<subseteq> F"
    unfolding funas_trs_def funas_rule_def [abs_def] by force
  from sF show ?thesis unfolding s t using vars rF by (force simp: funas_term_subst)
qed

lemma qrsteps_funas_term: assumes wwf: "wwf_qtrs Q R"
  and RF: "funas_trs R \<subseteq> F"
  and sF: "funas_term s \<subseteq> F"
  and steps: "(s,t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "funas_term t \<subseteq> F"
  using steps
proof (induct)
  case base
  show ?case by fact
next
  case (step t u)
  from qrstep_funas_term[OF wwf RF step(3) step(2)] show ?case .
qed

lemma nrqrstep_funas_args_term: assumes wwf: "wwf_qtrs Q R"
  and RF: "funas_trs R \<subseteq> F"
  and sF: "funas_args_term s \<subseteq> F"
  and step: "(s,t) \<in> nrqrstep nfs Q R"
  shows "funas_args_term t \<subseteq> F"
proof -
  from nrqrstep_imp_Fun_qrstep[OF step] obtain
    f bef aft si ti where s: "s = Fun f (bef @ si # aft)" and t: "t = Fun f (bef @ ti # aft)" and step: "(si, ti) \<in> qrstep nfs Q R"
    by blast
  from sF s have "funas_term si \<subseteq> F" unfolding funas_args_term_def by force
  from qrstep_funas_term[OF wwf RF this step] show ?thesis using sF unfolding s t funas_args_term_def by force
qed


lemma qrstep_iff_rqrstep_or_nrqrstep:
  "qrstep nfs Q R = rqrstep nfs Q R \<union> nrqrstep nfs Q R" (is "?step = ?root \<union> ?nonroot")
proof
  show "?step \<subseteq> ?root \<union> ?nonroot"
  proof
    fix s t assume "(s, t) \<in> ?step"
    then obtain C l r \<sigma> where NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and
       in_R: "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
       and "NF_subst nfs (l,r) \<sigma> Q" by auto
    then show "(s, t) \<in> ?root \<union> ?nonroot" by (cases "C = \<box>") auto
  qed
next
  show "?root \<union> ?nonroot \<subseteq> ?step"
  proof (intro subrelI, elim UnE)
    fix s t assume "(s, t) \<in> rqrstep nfs Q R"
    then obtain l r \<sigma> where NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and
      in_R: "(l, r) \<in> R" and s: "s = \<box>\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = \<box>\<langle>r \<cdot> \<sigma>\<rangle>"
       and "NF_subst nfs (l,r) \<sigma> Q" by auto
    then show "(s, t) \<in> qrstep nfs Q R" using qrstepI[of l \<sigma> Q r R s \<box> t] by simp
  next
    fix s t assume "(s, t) \<in> nrqrstep nfs Q R" then show "(s, t) \<in> qrstep nfs Q R" by auto
  qed
qed


lemma qrstep_imp_ctxt_nrqrstep:
  assumes "(s,t) \<in> qrstep nfs Q R"
  shows "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> nrqrstep nfs Q R"
  using assms
proof
  fix C \<sigma> l r
  assume nf: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms Q" and
    lr:"(l,r) \<in> R"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q"
  have C: "More f bef C aft \<noteq> \<box>" by auto
  show ?thesis
    unfolding nrqrstep_def
    apply (intro CollectI, unfold split)
    apply (intro exI conjI)
         apply (rule nf) 
        apply (rule lr)
       apply (rule C)
    by (auto simp: s t nfs)
qed

lemma qrsteps_imp_ctxt_nrqrsteps:
  assumes "(s,t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> (nrqrstep nfs Q R)\<^sup>*"
  using assms
proof (induct)
  case (step t u)
  from step(3) qrstep_imp_ctxt_nrqrstep[OF step(2), of f bef aft]
  show ?case by auto
qed simp

lemma ctxt_closed_nrqrstep [intro]: "ctxt.closed (nrqrstep nfs Q R)"
proof (rule one_imp_ctxt_closed)
  fix f bef s t aft
  assume "(s,t) \<in> nrqrstep nfs Q R"
  from this[unfolded nrqrstep_def] obtain l r C \<sigma>
    where NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms Q" and lr: "(l,r) \<in> R" and C: "C \<noteq> \<box>"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> nrqrstep nfs Q R"
  proof (rule nrqrstepI[OF NF lr _ _ _ nfs])
    show "More f bef C aft \<noteq> \<box>" by simp
  qed (insert s t, auto)
qed

lemma nrqrstep_union: "nrqrstep nfs Q (R \<union> S) = nrqrstep nfs Q R \<union> nrqrstep nfs Q S"
  unfolding nrqrstep_def by blast

lemma nrqrstep_imp_arg_qrstep:
  assumes "(s, t) \<in> nrqrstep nfs Q R"
  shows "\<exists> i < length (args s). (args s ! i, args t ! i) \<in> (qrstep nfs Q R)"
proof -
  from assms obtain l r C \<sigma> where NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and in_R: "(l, r) \<in> R" and ne: "C \<noteq> \<box>" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
   and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  from ne obtain f ss1 D ss2 where C: "C = More f ss1 D ss2" by (cases C) auto
  let ?i = "length ss1"
  show ?thesis
    by (rule exI[of _ ?i], unfold s C t, insert in_R NF nfs, auto)
qed

lemma nrqrstep_imp_arg_qrsteps:
  assumes "(s, t) \<in> nrqrstep nfs Q R"
  shows "(args s ! i, args t ! i) \<in> (qrstep nfs Q R)^="
proof -
  from assms obtain l r C \<sigma> where NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and in_R: "(l, r) \<in> R" and ne: "C \<noteq> \<box>" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  from ne obtain f ss1 D ss2 where C: "C = More f ss1 D ss2" by (cases C) auto
  let ?i = "length ss1"
  have "i < ?i \<or> i = ?i \<or> i > ?i" by auto
  then show ?thesis
  proof (elim disjE)
    assume "i < ?i"
    with append_Cons_nth_left[OF this] show ?thesis by (simp add: s t C)
  next
    assume "i = ?i"
    with append_Cons_nth_middle[OF this] show ?thesis using NF in_R s t nfs by (auto simp: C)
  next
    assume "i > ?i"
    with append_Cons_nth_right[OF this] show ?thesis by (simp add: s t C)
  qed
qed

lemma nrqrsteps_imp_arg_qrsteps:
  assumes "(s, t) \<in> (nrqrstep nfs Q R)\<^sup>*" shows "(args s ! i, args t ! i) \<in> (qrstep nfs Q R)\<^sup>*"
using assms proof (induct rule: rtrancl_induct)
  case (step u v)
  with nrqrstep_imp_arg_qrsteps[of u v nfs Q R i] show ?case by auto
qed simp

lemma nrqrsteps_imp_arg_qrsteps_count:
  assumes "(s, t) \<in> (nrqrstep nfs Q R)^^n" shows "\<exists> m. m \<le> n \<and> (args s ! i, args t ! i) \<in> (qrstep nfs Q R)^^m"
using assms proof (induct n arbitrary: t)
  case (Suc n u)
  from Suc(2) obtain t where st: "(s, t) \<in> (nrqrstep nfs Q R)^^n" and tu: "(t,u) \<in> nrqrstep nfs Q R" by auto
  from Suc(1)[OF st] obtain m where m: "m \<le> n" and st: "(args s ! i, args t ! i) \<in> (qrstep nfs Q R)^^m" by auto
  from nrqrstep_imp_arg_qrsteps[OF tu, of i] have "(args t ! i, args u ! i) \<in> Id \<union> qrstep nfs Q R" (is "?tu \<in> _") by auto
  then show ?case
  proof
    assume "?tu \<in> Id" with st m show ?case by (intro exI[of _ m], auto)
  next
    assume "?tu \<in> qrstep nfs Q R" with st m show ?case by (intro exI[of _ "Suc m"], auto)
  qed
qed simp

lemma nrqrstep_preserves_root:
  assumes "(s, t) \<in> nrqrstep nfs Q R"
  shows "root s = root t"
  using assms
proof (standard, goal_cases)
  case (1 l r C \<sigma>)
  hence t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and "C \<noteq> \<box>" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" by auto
  then obtain f ss1 D ss2 where "C = More f ss1 D ss2" by (cases C) auto
  then show ?thesis unfolding s t by auto
qed

lemma nrqrsteps_preserve_root:
 assumes "(s,t) \<in> (nrqrstep nfs Q R)\<^sup>*"
 shows "root s = root t"
using assms by induct (auto simp: nrqrstep_preserves_root)

(* TODO: perhaps delete the _fun variants *)
lemma nrqrstep_preserves_root_fun:
  assumes step: "(Fun f ss, t) \<in> nrqrstep nfs Q R"
  shows "\<exists>ts. t = Fun f ts"
  using nrqrstep_preserves_root[OF step] by (cases t, auto)

lemma nrqrsteps_preserve_root_fun:
  assumes step: "(Fun f ss, t) \<in> (nrqrstep nfs Q R)\<^sup>*"
  shows "\<exists>ts. t = Fun f ts"
  using nrqrsteps_preserve_root[OF step] by (cases t, auto)

lemma nrqrstep_num_args:
  assumes "(s, t) \<in> nrqrstep nfs Q R" shows "num_args s = num_args t"
proof -
  from assms obtain l r C \<sigma> where "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and "(l, r) \<in> R" and "C \<noteq> \<box>" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  show ?thesis unfolding s t by (cases C) (auto simp: \<open>C \<noteq> \<box>\<close>)
qed

lemma nrqrsteps_num_args:
  assumes "(s, t) \<in> (nrqrstep nfs Q R)\<^sup>*" shows "num_args s = num_args t"
using assms by (induct rule: rtrancl.induct) (auto simp: nrqrstep_num_args)

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

lemma nrqrstep_imp_sharp_qrstep:
  assumes step: "(s,t) \<in> nrqrstep nfs Q R"
  shows "(\<sharp> s, \<sharp> t) \<in> nrqrstep nfs Q R"
proof -
  let ?qr = "qrstep nfs Q R"
  let ?nr = "nrqrstep nfs Q R"
  let ?Q = "Q"
  let ?R = "R"
  let ?Iqr = "nrqrstep nfs ?Q ?R"
  from step obtain l r C \<sigma> where C: "C \<noteq> \<box>" and  lr: "(l,r) \<in> R" and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>"
    and NF: "\<forall>u\<lhd>l \<cdot> \<sigma>.  u \<in> NF_terms Q" "NF_subst nfs (l,r) \<sigma> Q"
    unfolding nrqrstep_def rstep_r_c_s_def by auto
  from C obtain D f bef aft where C: "C = More f bef D aft" by (cases C, auto)
  let ?Dl = "D\<langle>l \<cdot> \<sigma>\<rangle>"
  let ?Dr = "D\<langle>r \<cdot> \<sigma>\<rangle>"
  let ?C = "More (\<sharp> f) bef \<box> aft"
  from s t C have s: "s = Fun f (bef @ ?Dl # aft)" and t: "t = Fun f (bef @ ?Dr # aft)" by auto
  from lr NF have "(?Dl,?Dr) \<in> ?qr" by auto
  from qrstep_imp_ctxt_nrqrstep[OF this]
  have "(?C\<langle>?Dl\<rangle>,?C\<langle>?Dr\<rangle>) \<in> ?Iqr" by simp
  with s t show ?thesis by auto
qed

lemma nrqrsteps_imp_sharp_qrsteps:
  assumes step: "(s,t) \<in> (nrqrstep nfs Q R)\<^sup>*"
  shows "(\<sharp> s, \<sharp> t) \<in> (nrqrstep nfs Q R)\<^sup>*"
using step
proof (induct rule: rtrancl_induct)
  case (step u v)
  from nrqrstep_imp_sharp_qrstep[OF step(2)] and step(3)
    show ?case by auto
qed simp

end

lemma qrstep_imp_nrqrstep:
  assumes nvar: "\<forall>(l, r)\<in>R. is_Fun l"
    and ndef: "\<not> defined (applicable_rules Q R) (the (root s))"
    and step: "(s, t) \<in> qrstep nfs Q R"
  shows "(s, t) \<in> nrqrstep nfs Q R"
proof -
  from step[unfolded qrstep_iff_rqrstep_or_nrqrstep]
  show ?thesis
  proof
    assume "(s,t) \<in> rqrstep nfs Q R"
    then show ?thesis
    proof
      fix l r \<sigma>
      assume lr: "(l,r) \<in> R" and id: "s = l \<cdot> \<sigma>" and
        nf: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms Q"
      with nvar have "is_Fun l" by auto
      then obtain f ll where l: "l = Fun f ll" by (cases l, auto)
      with id obtain ss where s: "s = Fun f ss" "length ll = length ss" by (cases s, auto)
      from only_applicable_rules[OF nf] lr have ulr: "(l,r) \<in> applicable_rules Q R"
        unfolding applicable_rules_def by auto
      from id[unfolded l s] ndef[unfolded s] ulr[unfolded l]
      have False unfolding defined_def by force
      then show ?thesis by simp
    qed
  qed
qed

lemma qrsteps_imp_nrqrsteps:
  assumes nvar: "\<forall>(l, r)\<in>R. is_Fun l"
    and ndef: "\<not> defined (applicable_rules Q R) (the (root s))"
    and steps: "(s,t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(s,t) \<in> (nrqrstep nfs Q R)\<^sup>*"
  using steps
proof (induct)
  case (step t u)
  have "(t,u) \<in> nrqrstep nfs Q R"
  proof (rule qrstep_imp_nrqrstep[OF nvar _ step(2)])
    show "\<not> defined (applicable_rules Q R) (the (root t))"
      using ndef unfolding nrqrsteps_num_args[OF step(3)]
      nrqrsteps_preserve_root[OF step(3)]
      .
  qed
  with step(3) show ?case by auto
qed simp

lemma rel_qrsteps_imp_rel_nrqrsteps:
  assumes nvar: "\<forall>(l, r)\<in>R \<union> Rw. is_Fun l"
    and ndef: "\<not> defined (applicable_rules Q (R \<union> Rw)) (the (root s))"
    and steps: "(s,t) \<in> (qrstep nfs Q (R \<union> Rw))\<^sup>* O (qrstep nfs Q R) O (qrstep nfs Q (R \<union> Rw))\<^sup>*"
  shows "(s,t) \<in> (nrqrstep nfs Q (R \<union> Rw))\<^sup>* O nrqrstep nfs Q R O (nrqrstep nfs Q (R \<union> Rw))\<^sup>*"
proof -
  let ?Rw = "qrstep nfs Q (R \<union> Rw)"
  let ?R  = "qrstep nfs Q R"
  let ?Rwb = "nrqrstep nfs Q (R \<union> Rw)"
  let ?Rb  = "nrqrstep nfs Q R"
  from steps obtain u v where su: "(s,u) \<in> ?Rw\<^sup>*" and uv: "(u,v) \<in> ?R" and vt: "(v,t) \<in> ?Rw\<^sup>*" by blast
  from qrsteps_imp_nrqrsteps[OF nvar ndef su] have su: "(s,u) \<in> ?Rwb\<^sup>*" .
  note ndef = ndef[unfolded nrqrsteps_preserve_root[OF su]]
  then have ndefR: "\<not> defined (applicable_rules Q R) (the (root u))" unfolding defined_def applicable_rules_def by auto
  have uv: "(u,v) \<in> ?Rb"
    by (rule qrstep_imp_nrqrstep[OF _ ndefR uv], insert nvar, auto)
  note ndef = ndef[unfolded nrqrstep_preserves_root[OF uv]]
  from qrsteps_imp_nrqrsteps[OF nvar ndef vt] have vt: "(v,t) \<in> ?Rwb\<^sup>*" .
  from su uv vt show ?thesis by auto
qed

lemma nrqrstep_nrrstep[simp]: "nrqrstep nfs {} = nrrstep"
  by (intro ext, unfold nrrstep_def' nrqrstep_def, auto)


lemma args_steps_imp_nrqrsteps:
  assumes steps: "\<And> i. i < length ss \<Longrightarrow> (ts ! i, ss ! i) \<in> (qrstep nfs Q R)\<^sup>*"
    and len: "length ts = length ss"
  shows "(Fun f ts, Fun f ss) \<in> (nrqrstep nfs Q R)\<^sup>*"
  by (rule args_steps_imp_steps_gen[OF qrsteps_imp_ctxt_nrqrsteps len steps], auto)

lemma qrsteps_rqrstep_cases_n:
  assumes "(Fun f ss, t) \<in> (qrstep nfs Q R)^^n"
  shows "(\<exists>ts.
    length ts = length ss \<and>
    t = Fun f ts \<and>
    (\<forall>i<length ss. \<exists>m \<le> n. (ss ! i, ts ! i) \<in> (qrstep nfs Q R)^^m) \<and>
    (Fun f ss, t) \<in> (nrqrstep nfs Q R)^^n)
    \<or> (\<exists>m1 < n. \<exists>m2 < n. (Fun f ss, t) \<in> (nrqrstep nfs Q R)^^m1 O (rqrstep nfs Q R) O (qrstep nfs Q R)^^m2)"
using assms proof (induct n arbitrary: t)
  case 0 then show ?case by auto
next
  let ?QR = "qrstep nfs Q R"
  let ?RQR = "rqrstep nfs Q R"
  let ?NRQR = "nrqrstep nfs Q R"
  case (Suc m)
  then obtain u where su:"(Fun f ss, u) \<in> ?QR ^^ m" and ut:"(u, t) \<in> ?QR" by auto
  from Suc(1)[OF su] show ?case
  proof
    assume "\<exists>m1 < m. \<exists>m2 < m. (Fun f ss, u) \<in> ?NRQR^^m1 O ?RQR O ?QR^^m2"
    then obtain v m1 m2 where sv:"(Fun f ss, v) \<in> ?NRQR^^m1 O ?RQR \<and> m1 < m" and "(v, u) \<in> ?QR^^m2 \<and> m2 < m"  by auto
    with \<open>(u, t) \<in> ?QR\<close> have "(v, t) \<in> ?QR^^(Suc m2) \<and> Suc m2 < Suc m" by auto
    with sv have "(Fun f ss, t) \<in> ?NRQR^^m1 O ?RQR O ?QR ^^ Suc m2 \<and> m1 < Suc m \<and> Suc m2 < Suc m" by auto
    then show ?thesis by metis
  next
    assume "\<exists>us. length us = length ss \<and> u = Fun f us \<and> (\<forall>i<length ss. \<exists>k \<le> m. (ss!i, us!i) \<in> ?QR^^k) \<and> (Fun f ss, u) \<in> ?NRQR ^^ m"
    then obtain us where len: "length us = length ss" and u: "u = Fun f us"
      and isteps: "\<forall>i<length ss. \<exists>k \<le> m. (ss!i, us!i) \<in> ?QR^^k" and nrsteps:"(Fun f ss, u) \<in> ?NRQR ^^ m" by auto
    from ut have "(u, t) \<in> ?RQR \<or> (u, t) \<in> ?NRQR" unfolding qrstep_iff_rqrstep_or_nrqrstep by simp
    then show ?thesis
    proof
      assume "(u, t) \<in> ?RQR"
      with \<open>(Fun f ss, u) \<in> ?NRQR^^m\<close> have "(Fun f ss, t) \<in> ?NRQR^^m O ?RQR" by blast
      then have "(Fun f ss, t) \<in> ?NRQR^^m O ?RQR O ?QR ^^ 0" by auto
      then show ?thesis by blast
    next
      assume ut:"(u, t) \<in> ?NRQR"
      then have st:"(Fun f ss, t) \<in> ?NRQR ^^ Suc m" using nrsteps by auto
      have *: "(Fun f ss, t) \<in> ?NRQR\<^sup>*" by (rule relpow_imp_rtrancl[OF st])
      {
        fix i
        assume "i < length ss"
        with isteps obtain k where k: "k \<le> m" and ssus:"(ss ! i, us ! i) \<in> ?QR^^k" by auto
        from nrqrstep_imp_arg_qrsteps[OF ut] u have "(us ! i, args t ! i) \<in> ?QR^=" by auto
        then have "us ! i = args t ! i \<or> (us ! i, args t ! i) \<in> ?QR" by auto
        then have "\<exists>k \<le> Suc m. (ss ! i, args t ! i) \<in> ?QR^^k"
        proof
          assume "us ! i = args t ! i"
          then have "(ss ! i, args t ! i) \<in> ?QR^^k" using ssus by auto
          then show ?thesis using k le_SucI by fast
        next
          assume "(us ! i, args t ! i) \<in> ?QR"
          with ssus have "(ss ! i, args t ! i) \<in> ?QR^^(Suc k)" by auto
          then show ?thesis using k Suc_le_mono by blast
        qed
      }
      then show ?thesis using nrqrsteps_num_args[OF *] nrqrsteps_preserve_root_fun[OF *] st by auto
    qed
  qed
qed

lemma qrsteps_rqrstep_cases_nrqrstep:
  assumes "(Fun f ss, t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(\<exists>ts.
    length ts = length ss \<and>
    t = Fun f ts \<and>
    (\<forall>i<length ss. (ss ! i, ts ! i) \<in> (qrstep nfs Q R)\<^sup>*))
    \<or> (Fun f ss, t) \<in> (nrqrstep nfs Q R)\<^sup>* O (rqrstep nfs Q R) O (qrstep nfs Q R)\<^sup>*"
using assms proof (induct)
  case base then show ?case by auto
next
  case (step u t)
  then have "(\<exists>ts. length ts = length ss \<and> u = Fun f ts
    \<and> (\<forall>i<length ss. (ss!i, ts!i) \<in> (qrstep nfs Q R)\<^sup>*))
    \<or> (Fun f ss, u) \<in> (nrqrstep nfs Q R)\<^sup>* O rqrstep nfs Q R O (qrstep nfs Q R)\<^sup>*" by simp
  then show ?case
  proof
    assume "(Fun f ss, u) \<in> (nrqrstep nfs Q R)\<^sup>* O rqrstep nfs Q R O (qrstep nfs Q R)\<^sup>*"
    then obtain v where "(Fun f ss, v) \<in> (nrqrstep nfs Q R)\<^sup>* O rqrstep nfs Q R"
      and "(v, u) \<in> (qrstep nfs Q R)\<^sup>*" by auto
    with \<open>(u, t) \<in> qrstep nfs Q R\<close> have "(v, t) \<in> (qrstep nfs Q R)\<^sup>*" by auto
    with \<open>(Fun f ss, v) \<in> (nrqrstep nfs Q R)\<^sup>* O rqrstep nfs Q R\<close> show ?thesis by auto
  next
    assume "\<exists>ts. length ts = length ss \<and> u = Fun f ts
      \<and> (\<forall>i<length ss. (ss!i, ts!i) \<in> (qrstep nfs Q R)\<^sup>*)"
    then obtain ts where len: "length ts = length ss" and u: "u = Fun f ts"
      and steps: "\<forall>i<length ss. (ss!i, ts!i) \<in> (qrstep nfs Q R)\<^sup>*" by auto
    from len steps have "(Fun f ss, u) \<in> (nrqrstep nfs Q R)\<^sup>*" unfolding u
      by (simp add: args_steps_imp_nrqrsteps)
    from \<open>(u, t) \<in> qrstep nfs Q R\<close> have "(u, t) \<in> rqrstep nfs Q R \<or> (u, t) \<in> nrqrstep nfs Q R"
      unfolding qrstep_iff_rqrstep_or_nrqrstep by simp
    then show ?thesis
    proof
      assume "(u, t) \<in> rqrstep nfs Q R"
      with \<open>(Fun f ss, u) \<in> (nrqrstep nfs Q R)\<^sup>*\<close> have "(Fun f ss, t) \<in> (nrqrstep nfs Q R)\<^sup>* O rqrstep nfs Q R"
        by auto
      then show ?thesis by auto
    next
      assume "(u, t) \<in> nrqrstep nfs Q R"
      from nrqrstep_preserves_root[OF this[unfolded u]]
        obtain us where t: "t = Fun f us" by (cases t, auto)
      from nrqrstep_num_args[OF \<open>(u, t) \<in> nrqrstep nfs Q R\<close>]
        have "num_args u = num_args t" by simp
      then have "length ts = length us" unfolding u t by simp
      with len have len': "length ss = length ts" by simp
      from nrqrstep_imp_arg_qrsteps[OF \<open>(u, t) \<in> nrqrstep nfs Q R\<close>]
        have "\<forall>i<length ts. (ts!i, args t ! i) \<in> (qrstep nfs Q R)^=" unfolding u by auto
      then have "\<forall>i<length ts. (ts!i, us!i) \<in> (qrstep nfs Q R)^=" unfolding t by simp
      then have next_steps: "\<forall>i<length ts. (ts!i, us!i) \<in> (qrstep nfs Q R)\<^sup>*" by auto
      have "length us = length ss" using \<open>length ts = length us\<close> and len by simp
      moreover have "t = Fun f us" by fact
      moreover have "\<forall>i<length ss. (ss!i, us!i) \<in> (qrstep nfs Q R)\<^sup>*"
      proof (intro allI impI)
        fix i assume "i < length ss"
        with steps have "(ss ! i, ts ! i) \<in> (qrstep nfs Q R)\<^sup>*" by simp
        moreover from \<open>i < length ss\<close> and next_steps have "(ts!i, us!i) \<in> (qrstep nfs Q R)\<^sup>*"
          unfolding len' by simp
        ultimately show "(ss ! i, us ! i) \<in> (qrstep nfs Q R)\<^sup>*" by auto
      qed
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma qrsteps_rqrstep_cases:
  assumes "(Fun f ss, t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(\<exists>ts.
    length ts = length ss \<and>
    t = Fun f ts \<and>
    (\<forall>i<length ss. (ss ! i, ts ! i) \<in> (qrstep nfs Q R)\<^sup>*))
    \<or> (Fun f ss, t) \<in> (qrstep nfs Q R)\<^sup>* O (rqrstep nfs Q R) O (qrstep nfs Q R)\<^sup>*"
proof -
  have "(nrqrstep nfs Q R)\<^sup>* \<subseteq> (qrstep nfs Q R)\<^sup>*" unfolding qrstep_iff_rqrstep_or_nrqrstep
    by regexp
  then show ?thesis
    using qrsteps_rqrstep_cases_nrqrstep[OF assms] by auto
qed

(* generalizes nondef_root_imp_arg_steps from rstep to qrstep nfs *)
lemma nondef_root_imp_arg_qrsteps:
  assumes steps: "(Fun f ss, t) \<in> (qrstep nfs Q R)\<^sup>*"
    and vars: "\<forall>(l, r)\<in>R. is_Fun l"
    and ndef: "\<not> defined R (f, length ss)"
  shows "\<exists> ts. length ts = length ss \<and> t = Fun f ts \<and> (\<forall>i<length ss. (ss ! i, ts ! i) \<in> (qrstep nfs Q R)\<^sup>*)"
proof -
  from qrsteps_rqrstep_cases[OF steps]
  show ?thesis
  proof
    assume "(Fun f ss, t) \<in> (qrstep nfs Q R)\<^sup>* O rqrstep nfs Q R O (qrstep nfs Q R)\<^sup>*"
    then obtain u v where su: "(Fun f ss, u) \<in> (qrstep nfs Q R)\<^sup>*" and uv: "(u,v) \<in> rqrstep nfs Q R" by auto
    from first_step[OF _ su uv, unfolded qrstep_iff_rqrstep_or_nrqrstep, OF Un_commute]
    obtain u v where su: "(Fun f ss, u) \<in> (nrqrstep nfs Q R)\<^sup>*" and uv: "(u,v) \<in> rqrstep nfs Q R" by auto
    from nrqrsteps_preserve_root[OF su] nrqrsteps_num_args[OF su] obtain us where u: "u = Fun f us"
      and us: "length ss = length us" by (cases u, auto)
    from uv[unfolded u] rqrstep_def obtain l r \<sigma> where lr: "(l,r) \<in> R" and fus: "Fun f us = l \<cdot> \<sigma>" by auto
    from vars[THEN bspec[OF _ lr]] fus obtain ls where "l = Fun f ls" by (cases l, auto)
    with fus lr have "defined R (f,length ss)" unfolding us defined_def by auto
    with ndef
    show ?thesis by auto
  qed simp
qed

lemmas args_qrsteps_imp_qrsteps = args_steps_imp_steps[OF ctxt_closed_qrstep]

lemmas qrstep_imp_map_rstep = rstep_imp_map_rstep[OF qrstep_into_rstep]
lemmas qrsteps_imp_map_rsteps = rsteps_imp_map_rsteps[OF qrsteps_into_rsteps]

lemma NF_imp_subt_NF: assumes "t \<in> NF_terms Q" shows "\<forall>u\<lhd>t. u \<in> NF_terms Q"
proof(intro allI impI)
  fix u
  assume t: "t \<rhd> u"
  {
    fix v
    assume uv: "(u,v) \<in> rstep (Id_on Q)"
    from t obtain C where t: "t = C\<langle>u\<rangle>" by auto
    from uv have "(t,C\<langle>v\<rangle>) \<in> rstep (Id_on Q)" unfolding t by auto
    with assms have False by auto
  }
  thus "u \<in> NF_terms Q" by auto
qed

lemma qrstep_diff: assumes "R \<subseteq> S" shows "qrstep nfs Q R - qrstep nfs Q (D \<inter> S) \<subseteq> qrstep nfs Q (R - D)" (is "?L \<subseteq> ?R")
proof -
  {
    fix s t
    assume "(s,t) \<in> ?L"
    then have yes: "(s,t) \<in> qrstep nfs Q R" and no: "(s,t) \<notin> qrstep nfs Q (D \<inter> S)" by auto
    from yes no have "(s,t) \<in> ?R"
      unfolding qrstep_rule_conv[where R = R]
      unfolding qrstep_rule_conv[where R = "D \<inter> S"]
      unfolding qrstep_rule_conv[where R = "R - D"]
      using assms
      by blast
  }
  then show ?thesis by auto
qed

lemma wwf_qtrs_qrstep_Fun:
  assumes "wwf_qtrs Q R" and "(s, t) \<in> qrstep nfs Q R"
  shows "\<exists>f ss. s = Fun f ss"
proof -
  from assms obtain C \<sigma> l r where "(l, r) \<in> R" and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" by auto
  from wwf_qtrs_imp_left_fun[OF assms(1) \<open>(l, r) \<in> R\<close>]
    obtain f ls where l: "l = Fun f ls" by auto
  show ?thesis unfolding \<open>s = C\<langle>l \<cdot> \<sigma>\<rangle>\<close> l by (induct C) simp_all
qed

lemma qrstep_preserves_undefined_root:
  assumes  ndef: "\<not> defined (applicable_rules Q R) (the (root s))"
    and nvar: "\<forall>(l,r) \<in> R. is_Fun l"
    and step: "(s, t) \<in> qrstep nfs Q R"
  shows "\<not> defined (applicable_rules Q R) (the (root t))"
proof -
  from qrstep_imp_nrqrstep[OF nvar ndef step] have step: "(s,t) \<in> nrqrstep nfs Q R"
    .
  from ndef[unfolded nrqrstep_preserves_root[OF step] nrqrstep_num_args[OF step]] show ?thesis .
qed

lemma qrsteps_preserve_undefined_root:
  assumes  ndef: "\<not> defined (applicable_rules Q R) (the (root s))"
    and nvar: "\<forall>(l,r) \<in> R. is_Fun l"
    and step: "(s, t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "\<not> defined (applicable_rules Q R) (the (root t))"
proof -
  from qrsteps_imp_nrqrsteps[OF nvar ndef step] have step: "(s,t) \<in> (nrqrstep nfs Q R)\<^sup>*"
    .
  from ndef[unfolded nrqrsteps_preserve_root[OF step] nrqrsteps_num_args[OF step]] show ?thesis .
qed

lemma wf_trs_imp_wwf_qtrs:
  assumes "wf_trs R" shows "wwf_qtrs Q R"
  using assms by (auto simp: wwf_qtrs_def wf_trs_def)

lemma SN_on_imp_qrstep_wf_rules:
  assumes "SN_on (qrstep nfs Q R) {s}" and "(s, t) \<in> qrstep nfs Q R" and nfs: "\<not> nfs"
  shows "(s, t) \<in> qrstep nfs Q (wf_rules R)"
using \<open>(s, t) \<in> qrstep nfs Q R\<close>
proof
  fix C \<sigma> l r
  assume NF_terms: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q"
    and "(l, r) \<in> R"
    and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  show ?thesis
  proof (cases "(l, r) \<in> wf_rules R")
    case True then show ?thesis unfolding s t using NF_terms nfs by auto
  next
    case False
    with \<open>(l, r) \<in> R\<close>
      have "is_Var l \<or> (\<exists>x. x \<in> vars_term r - vars_term l)"
      unfolding wf_rules_def wf_rule_def by auto
    then show ?thesis
    proof
      assume "is_Var l"
      then obtain x where l: "l = Var x" by auto
      from left_Var_imp_not_SN_qrstep[OF \<open>(l, r) \<in> R\<close>[unfolded l]]
        and assms show ?thesis by simp
    next
      assume "\<exists>x. x \<in> vars_term r - vars_term l"
      then obtain x where "x \<in> vars_term r - vars_term l"
        and empty: "vars_term l \<inter> {x} = {}" by auto
      with SN_on_imp_wwf_rule[OF assms(1) s \<open>(l, r) \<in> R\<close> NF_terms nfs]
        and only_applicable_rules[OF NF_terms]
        show ?thesis unfolding wwf_rule_def by auto
    qed
  qed
qed

lemma SN_on_imp_qrsteps_wf_rules:
  assumes "(s, t) \<in> (qrstep nfs Q R)\<^sup>*" and "SN_on (qrstep nfs Q R) {s}" and nfs: "\<not> nfs"
  shows "(s, t) \<in> (qrstep nfs Q (wf_rules R))\<^sup>*"
using \<open>(s, t) \<in> (qrstep nfs Q R)\<^sup>*\<close>
proof (induct)
  case base show ?case ..
next
  case (step u v)
  from steps_preserve_SN_on[OF \<open>(s, u) \<in> (qrstep nfs Q R)\<^sup>*\<close> \<open>SN_on (qrstep nfs Q R) {s}\<close>]
    have "SN_on (qrstep nfs Q R) {u}" .
  from SN_on_imp_qrstep_wf_rules[OF this \<open>(u, v) \<in> qrstep nfs Q R\<close> nfs]
    have "(u, v) \<in> qrstep nfs Q (wf_rules R)" .
  with \<open>(s, u) \<in> (qrstep nfs Q (wf_rules R))\<^sup>*\<close> show ?case ..
qed

lemmas wwf_qtrs_wf_rules =  wf_trs_imp_wwf_qtrs[OF wf_trs_wf_rules]
lemmas qrstep_wf_rules_subset = qrstep_mono[OF wf_rules_subset subset_refl]


lemma SN_on_qrstep_imp_SN_on_supt_union_qrstep:
  "SN_on (qrstep nfs Q R) {t} \<Longrightarrow> SN_on ({\<rhd>} \<union> qrstep nfs Q R) {t}"
  by (rule SN_on_r_imp_SN_on_supt_union_r[OF ctxt_closed_qrstep])

lemma supt_qrstep_subset:
  "{\<rhd>} O qrstep nfs Q R \<subseteq> qrstep nfs Q R O {\<rhd>}"
  using supteq_qrstep_subset[of nfs Q R, unfolded supteq_supt_set_conv] by best

lemma supt_Un_qrstep_trancl_subset:
  "({\<rhd>} \<union> qrstep nfs Q R)\<^sup>+ \<subseteq> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}"
    (is "?lhs \<subseteq> ?rhs")
proof
  fix s t
  assume "(s, t) \<in> ?lhs"
  then show "(s, t) \<in> ?rhs"
  proof (induct s t)
    case (r_into_trancl s t)
    then show ?case by (rule UnE) auto
  next
    case (trancl_into_trancl s t u)
    from \<open>(t, u) \<in> {\<rhd>} \<union> qrstep nfs Q R\<close>
    show ?case
    proof
      assume "t \<rhd> u"
      with \<open>(s, t) \<in> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}\<close>
        show ?case using supteq_trans[of _ t u] by auto
    next
      assume "(t, u) \<in> qrstep nfs Q R"
      from \<open>(s, t) \<in> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}\<close>
        obtain v where "(s, v) \<in> (qrstep nfs Q R)\<^sup>*" and "v \<unrhd> t" by blast
      with \<open>(t, u) \<in> qrstep nfs Q R\<close> have "(v, u) \<in> {\<unrhd>} O qrstep nfs Q R" by blast
      with supteq_qrstep_subset[of nfs Q R]
        have "(v, u) \<in> qrstep nfs Q R O {\<unrhd>}" by blast
      with rtrancl.rtrancl_into_rtrancl[OF \<open>(s, v) \<in> (qrstep nfs Q R)\<^sup>*\<close>]
        show ?case by blast
    qed
  qed
qed

lemma supteq_Un_qrstep_trancl_subset:
  "({\<unrhd>} \<union> qrstep nfs Q R)\<^sup>+ \<subseteq> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}"
    (is "?lhs \<subseteq> ?rhs")
proof
  fix s t
  assume "(s, t) \<in> ?lhs"
  then show "(s, t) \<in> ?rhs"
  proof (induct s t)
    case (r_into_trancl s t)
    then show ?case by (rule UnE) auto
  next
    case (trancl_into_trancl s t u)
    from \<open>(t, u) \<in> {\<unrhd>} \<union> qrstep nfs Q R\<close>
    show ?case
    proof
      assume "t \<unrhd> u"
      with \<open>(s, t) \<in> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}\<close>
        show ?case using supteq_trans[of _ t u] by auto
    next
      assume "(t, u) \<in> qrstep nfs Q R"
      from \<open>(s, t) \<in> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}\<close>
        obtain v where "(s, v) \<in> (qrstep nfs Q R)\<^sup>*" and "v \<unrhd> t" by blast
      with \<open>(t, u) \<in> qrstep nfs Q R\<close> have "(v, u) \<in> {\<unrhd>} O qrstep nfs Q R" by blast
      with supteq_qrstep_subset[of nfs Q R]
        have "(v, u) \<in> qrstep nfs Q R O {\<unrhd>}" by blast
      with rtrancl.rtrancl_into_rtrancl[OF \<open>(s, v) \<in> (qrstep nfs Q R)\<^sup>*\<close>]
        show ?case by blast
    qed
  qed
qed

lemma supteq_Un_qrstep_rtrancl_subset:
  "({\<unrhd>} \<union> qrstep nfs Q R)\<^sup>* \<subseteq> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}"
proof -
  from supteq_Un_qrstep_trancl_subset[of nfs Q R]
    have "Id \<union> ({\<unrhd>} \<union> qrstep nfs Q R)\<^sup>* O ({\<unrhd>} \<union> qrstep nfs Q R) \<subseteq> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}"
    unfolding rtrancl_comp_trancl_conv
    unfolding supteq_supt_set_conv by auto
  then show ?thesis by auto
qed

lemma supt_Un_qrstep_subset:
  "{\<rhd>} \<union> qrstep nfs Q R \<subseteq> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}"
  by auto

lemma supt_Un_qrstep_rtrancl_subset:
  "({\<rhd>} \<union> qrstep nfs Q R)\<^sup>* \<subseteq> (qrstep nfs Q R)\<^sup>* O {\<unrhd>}"
    (is "?lhs \<subseteq> ?rhs")
proof
  fix s t assume "(s, t) \<in> ?lhs"
  then show "(s, t) \<in> ?rhs"
  proof (induct s t)
    case (rtrancl_refl t)
    show ?case by auto
  next
    case (rtrancl_into_rtrancl s t u)
    from \<open>(t, u) \<in> {\<rhd>} \<union> qrstep nfs Q R\<close>
      show ?case
    proof
      assume "t \<rhd> u"
      then have "t \<unrhd> u" by auto
      with \<open>(s, t) \<in> ?rhs\<close> show ?case
        using supteq_trans by blast
    next
      assume "(t, u) \<in> qrstep nfs Q R"
      from \<open>(s, t) \<in> ?rhs\<close>
        obtain v where "(s, v) \<in> (qrstep nfs Q R)\<^sup>*" and "v \<unrhd> t" by auto
      with \<open>(t, u) \<in> qrstep nfs Q R\<close> have "(v, u) \<in> {\<unrhd>} O qrstep nfs Q R" by auto
      with supteq_qrstep_subset have "(v, u) \<in> qrstep nfs Q R O {\<unrhd>}" by blast
      with rtrancl.rtrancl_into_rtrancl[OF \<open>(s, v) \<in> (qrstep nfs Q R)\<^sup>*\<close>]
        show ?case by auto
    qed
  qed
qed

lemma qrsteps_comp_supteq_subset:
  "(qrstep nfs Q R)\<^sup>* O {\<unrhd>} \<subseteq> ({\<unrhd>} \<union> qrstep nfs Q R)\<^sup>*"
  by regexp

lemma qrsteps_comp_supteq_subset':
  "(qrstep nfs Q R)\<^sup>* O {\<unrhd>} \<subseteq> ({\<unrhd>} \<union> qrstep nfs Q R)\<^sup>+"
  by regexp

lemma qrsteps_comp_supteq_supt_subset:
  "(qrstep nfs Q R)\<^sup>* O {\<unrhd>} \<subseteq> ({\<rhd>} \<union> qrstep nfs Q R)\<^sup>*"
  unfolding supteq_supt_set_conv by (regexp)

lemma qrsteps_comp_supteq_conv:
  "(qrstep nfs Q R)\<^sup>* O {\<unrhd>} = ({\<unrhd>} \<union> qrstep nfs Q R)\<^sup>+"
  using qrsteps_comp_supteq_subset' supteq_Un_qrstep_trancl_subset by blast

lemma qrsteps_comp_supteq_conv':
  "(qrstep nfs Q R)\<^sup>* O {\<unrhd>} = ({\<unrhd>} \<union> qrstep nfs Q R)\<^sup>*"
  using qrsteps_comp_supteq_subset supteq_Un_qrstep_rtrancl_subset by blast

lemma qrsteps_comp_supteq_conv'':
  "(qrstep nfs Q R)\<^sup>* O {\<unrhd>} = ({\<rhd>} \<union> qrstep nfs Q R)\<^sup>*"
  using qrsteps_comp_supteq_supt_subset supt_Un_qrstep_rtrancl_subset by blast

(*subterm steps may always be postponed until the very end*)
lemmas supteq_Un_qrstep_trancl_conv = qrsteps_comp_supteq_conv[symmetric]
lemmas supteq_Un_qrstep_rtrancl_conv = qrsteps_comp_supteq_conv'[symmetric]
lemmas supt_Un_qrstep_rtrancl_conv = qrsteps_comp_supteq_conv''[symmetric]

lemma rhs_free_vars_imp_sig_qrstep_not_SN_on:
  assumes R: "(l,r) \<in> applicable_rules Q R" and free: "\<not> vars_term r \<subseteq> vars_term l"
  and F: "funas_trs R \<subseteq> F"
  and nfs: "\<not> nfs"
  shows "\<not> SN_on (sig_step F (qrstep nfs Q R)) {l}"
proof -
  from free obtain x where x: "x \<in> vars_term r - vars_term l" by auto
  then have "x \<in> vars_term r" by simp
  from supteq_Var[OF this] have "r \<unrhd> Var x" .
  then obtain C where r: "C\<langle>Var x\<rangle> = r" by auto
  let ?\<sigma> = "\<lambda>y. if y = x then l else Var y"
  let ?t = "\<lambda>i. ((C \<cdot>\<^sub>c ?\<sigma>)^i)\<langle>l\<rangle>"
  from R have R': "(l,r) \<in> R" unfolding applicable_rules_def by auto
  from rhs_wf[OF R' F] have wf_r: "funas_term r \<subseteq> F" by fast
  from lhs_wf[OF R' F] have wf_l: "funas_term l \<subseteq> F" by fast
  from wf_r[unfolded r[symmetric]]
  have wf_C: "funas_ctxt C \<subseteq> F" by simp
  from x have neq: "\<forall>y\<in>vars_term l. y \<noteq> x" by auto
  have "l\<cdot>?\<sigma> = l \<cdot> Var"
    by (rule term_subst_eq, insert neq, auto)
  then have l: "l\<cdot> ?\<sigma> = l" by simp
  have rsigma: "r\<cdot>?\<sigma> = (C \<cdot>\<^sub>c ?\<sigma>)\<langle>l\<rangle>" unfolding r[symmetric] by simp
  from wf_C have wf_C: "funas_ctxt (C \<cdot>\<^sub>c ?\<sigma>) \<subseteq> F" using wf_l by auto
  show ?thesis
  proof (rule wf_loop_imp_sig_ctxt_rel_not_SN[OF _ wf_l wf_C ctxt_closed_qrstep])
    show "(l,(C \<cdot>\<^sub>c ?\<sigma>)\<langle>l\<rangle>) \<in> qrstep nfs Q R"
    proof (rule qrstepI[OF _ R', of ?\<sigma> _ _ Hole], unfold l rsigma)
      show "\<forall>u\<lhd>l. u \<in> NF_terms Q" using R unfolding applicable_rules_def applicable_rule_def by auto
    qed (insert nfs, auto)
  qed
qed

lemma lhs_var_imp_sig_qrstep_not_SN:
  assumes rule: "(Var x, r) \<in> R" and F: "funas_trs R \<subseteq> F" and nfs: "\<not> nfs"
  shows "\<not> SN (sig_step F (qrstep nfs Q R))"
proof -
  from get_var_or_const[of r]
  obtain C t where r: "r = C\<langle>t\<rangle>" and args: "args t = []" by auto
  from rhs_wf[OF rule subset_refl] F have wfr: "funas_term r \<subseteq> F" by auto
  from wfr[unfolded r] F
  have wfC: "funas_ctxt C \<subseteq> F" and wft: "funas_term t \<subseteq> F" by auto
  let ?\<sigma> = "(\<lambda>x. t)"
  from wfC wft have wfC: "funas_ctxt (C \<cdot>\<^sub>c ?\<sigma>) \<subseteq> F" by auto
  have tsig: "t \<cdot> ?\<sigma> = t" using args by (cases t, auto)
  have "\<not> SN_on (sig_step F (qrstep nfs Q R)) {t}"
  proof (rule wf_loop_imp_sig_ctxt_rel_not_SN[OF _ wft wfC ctxt_closed_qrstep])
    show "(t,(C \<cdot>\<^sub>c ?\<sigma>)\<langle>t\<rangle>) \<in> qrstep nfs Q R"
      by (rule qrstepI[OF _ rule, of ?\<sigma> _ _ Hole], unfold NF_terms_args_conv[symmetric] r, auto simp: nfs tsig args)
  qed
  then show ?thesis unfolding SN_def by auto
qed

lemma SN_sig_qrstep_imp_wwf_trs: assumes SN: "SN (sig_step F (qrstep nfs Q R))" and F: "funas_trs R \<subseteq> F" and nfs: "\<not> nfs"
  shows "wwf_qtrs Q R"
proof (rule ccontr)
  assume "\<not> wwf_qtrs Q R"
  then obtain l r where R: "(l,r) \<in> applicable_rules Q R"
    and not_wf: "(\<forall>f ts. l \<noteq> Fun f ts) \<or> \<not>(vars_term r \<subseteq> vars_term l)" unfolding wwf_qtrs_def applicable_rules_def
    by auto
  from not_wf have "\<not> SN (sig_step F (qrstep nfs Q R))"
  proof
    assume free: "\<not> vars_term r \<subseteq> vars_term l"
    from rhs_free_vars_imp_sig_qrstep_not_SN_on[OF R free F nfs] show ?thesis unfolding SN_on_def by auto
  next
    assume "\<forall>f ts. l \<noteq> Fun f ts"
    then obtain x where l:"l = Var x" by (cases l) auto
    with R have "(Var x,r) \<in> R" unfolding l applicable_rules_def by simp
    from lhs_var_imp_sig_qrstep_not_SN[OF this F nfs] show ?thesis .
  qed
  with assms show False by blast
qed

lemma linear_term_weak_match_match:
  assumes "linear_term t" and "weak_match s t"
  shows "\<exists>\<sigma>. s = t \<cdot> \<sigma>"
using assms
proof (induct t arbitrary: s)
  case (Var x) then show ?case by auto
next
  case (Fun f ts)
  note Fun' = this
  show ?case
  proof (cases s)
    case (Var y) show ?thesis using Fun by (simp add: Var)
  next
    case (Fun g ss)
    from Fun' have "f = g" and len: "length ss = length ts" by (simp add: Fun)+
    from Fun' have "\<forall>i<length ts. weak_match (ss ! i) (ts ! i)" by (simp add: len Fun)
    with Fun' have "\<forall>i. \<exists>\<sigma>. i < length ts \<longrightarrow> (ss ! i) = (ts ! i) \<cdot> \<sigma>" by auto
    from choice[OF this] obtain \<tau> where substs: "\<forall>i<length ts. ss ! i = (ts ! i) \<cdot> \<tau> i" by blast
    from subst_merge[OF Fun'(2)[unfolded linear_term.simps, THEN conjunct1]]
      obtain \<sigma> where vars: "\<forall>i<length ts. \<forall>x\<in>vars_term (ts ! i). \<sigma> x = \<tau> i x" ..
    have "\<forall>i<length ts. (ts ! i) \<cdot> \<sigma> = (ts ! i) \<cdot> \<tau> i"
    proof (intro allI impI)
      fix i assume "i < length ts"
      with vars have "\<forall>x\<in>vars_term (ts ! i). \<sigma> x = \<tau> i x" by simp
      then show "(ts ! i) \<cdot> \<sigma> = (ts ! i) \<cdot> \<tau> i" unfolding term_subst_eq_conv .
    qed
    with substs have "\<forall>i<length ss. (ts ! i) \<cdot> \<sigma> = ss ! i" by (simp add: len)
    with map_nth_eq_conv[OF len[symmetric], of "\<lambda>t. t \<cdot> \<sigma>"]
      have "map (\<lambda>t. t \<cdot> \<sigma>) ts = ss" by simp
    then have "s = Fun f ts \<cdot> \<sigma>" by (simp add: Fun \<open>f = g\<close>)
    then show ?thesis by auto
  qed
qed

lemma NF_terms_instance:
  assumes "\<forall>s\<lhd>l \<cdot> \<sigma>. s \<in> NF_terms Q"
  shows "\<forall>s\<lhd>l. s \<in> NF_terms Q"
proof (intro allI impI)
  fix s assume "l \<rhd> s"
  then have "l \<cdot> \<sigma> \<rhd> s \<cdot> \<sigma>" by (rule supt_subst)
  with assms have "s \<cdot> \<sigma> \<in> NF_terms Q" by simp
  from NF_instance[OF this] show "s \<in> NF_terms Q" .
qed

lemma NF_terms_ctxt:
  assumes "\<forall>s\<lhd>C\<langle>l\<rangle>. s \<in> NF_terms Q"
  shows "\<forall>s\<lhd>l. s \<in> NF_terms Q"
proof (intro impI allI)
  fix s assume "l \<rhd> s"
  from ctxt_imp_supteq[of C l] have "C\<langle>l\<rangle> \<unrhd> l" .
  from this and \<open>l \<rhd> s\<close> have "s \<lhd> C\<langle>l\<rangle>" by (rule supteq_supt_trans)
  with assms show "s \<in> NF_terms Q" by simp
qed


lemma Q_subset_R_imp_same_NF:
  assumes subset: "NF_trs R \<subseteq> NF_terms Q"
  and no_lhs_var: "\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "NF_trs R = NF (qrstep nfs Q R)"
proof
  show "NF_trs R \<subseteq> NF (qrstep nfs Q R)"
    by (rule NF_anti_mono, auto)
next
  show "NF (qrstep nfs Q R) \<subseteq> NF_trs R"
  proof
    fix t
    assume NFt: "t \<in> NF (qrstep nfs Q R)"
    show "t \<in> NF_trs R"
    proof (rule ccontr)
      assume "t \<notin> NF_trs R"
      then obtain s where "(t,s) \<in> rstep R" by auto
      from rstep_imp_irstep[OF this no_lhs_var, of nfs] obtain s where step: "(t,s) \<in> qrstep nfs (lhss R) R" unfolding irstep_def by force
      have "(t,s) \<in> qrstep nfs Q R"
        by (rule set_mp[OF qrstep_mono step], insert subset, auto)
      with NFt show False by auto
    qed
  qed
qed

lemma all_ctxt_closed_qrsteps[intro]: "all_ctxt_closed F ((qrstep nfs Q R)\<^sup>*)"
  by (rule trans_ctxt_imp_all_ctxt_closed[OF trans_rtrancl refl_rtrancl], blast)

lemma subst_qrsteps_imp_qrsteps: fixes \<sigma> :: "('f,'v)subst" 
  assumes "\<And> x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x,\<tau> x) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (qrstep nfs Q R)\<^sup>*"
  using all_ctxt_closed_subst_step[OF all_ctxt_closed_qrsteps, of t \<sigma> \<tau>,
      OF assms] .

lemma subst_qrsteps_imp_qrsteps_at_pos: fixes \<sigma> :: "('f,'v)subst" 
  assumes "p \<in> poss l"
  and "\<And> x. x \<in> vars_term l \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(l |_ p \<cdot> \<sigma>, l |_ p \<cdot> \<tau>) \<in> (qrstep nfs Q R)\<^sup>*"
proof -
  {
    fix y
    assume a:"y \<in> vars_term (l |_ p)"
    from supteq_trans[OF subt_at_imp_supteq[OF assms(1)] vars_term_supteq(1)[OF a]]
    have "y \<in> vars_term l" using subteq_Var_imp_in_vars_term by fast
    with assms have "(\<sigma> y, \<tau> y) \<in> (qrstep nfs Q R)\<^sup>*" by blast
  }
  then show ?thesis using subst_qrsteps_imp_qrsteps by blast
qed


lemma instance_weak_match:
  "s = t \<cdot> \<sigma> \<Longrightarrow> weak_match s t"
  by (induct s t rule: weak_match.induct) auto

text \<open>For linear terms, matching and weak matching are the same.\<close>
lemma linear_term_weak_match_instance_conv:
  assumes "linear_term t"
  shows "weak_match s t \<longleftrightarrow> (\<exists>\<sigma>. s = t \<cdot> \<sigma>)"
  using linear_term_weak_match_match[OF assms] and instance_weak_match by blast

lemma qrsteps_rules_conv:
  "((s,t) \<in> (qrstep nfs Q R)\<^sup>*) = (\<exists> n ts lr. ts 0 = s \<and> ts n = t \<and> (\<forall>i<n. (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> R))" (is "?L = ?R")
proof
  assume ?L
  from this[unfolded rtrancl_fun_conv] obtain n ts where first: "ts 0 = s" and last: "ts n = t" and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q R" by auto
  {
    fix i
    assume i: "i < n"
    from steps[OF this, unfolded qrstep_rule_conv[where R = R]]
    have "\<exists> lr. lr \<in> R \<and> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr}" by auto
  }
  then have "\<forall>i. \<exists> lr. i < n \<longrightarrow> lr \<in> R \<and> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr}" by auto
  from choice[OF this] obtain lr where lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> R" and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}" by auto
  show ?R using first last lr steps by blast
next
  assume ?R
  then obtain n ts lr where first: "ts 0 = s" and last: "ts n = t"
    and steps: "\<forall>i<n. (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> R"
    by auto
  from steps have steps: "\<forall>i<n. (ts i, ts (Suc i)) \<in> qrstep nfs Q R"
    unfolding qrstep_rule_conv[where R = R] by auto
  show ?L unfolding rtrancl_fun_conv using first last steps by blast
qed

lemma qrsteps_rules_conv':
  assumes left: "((s,t) \<in> (qrstep nfs Q R)\<^sup>* O qrstep nfs Q R' O (qrstep nfs Q R)\<^sup>*)"
  shows "(\<exists> n ts lr i. ts 0 = s \<and> ts n = t \<and> (\<forall>i<n. (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> R \<union> R') \<and> i < n \<and> lr i \<in> R')" (is "?Right")
proof -
  let ?Q = "qrstep nfs Q"
  let ?R = "?Q R"
  let ?R' = "?Q R'"
  show ?thesis
  proof -
    from left
    obtain u v where su: "(s, u) \<in> ?R\<^sup>*" and uv: "(u,v) \<in> ?R'" and vt: "(v,t) \<in> ?R\<^sup>*" by auto
    from su[unfolded qrsteps_rules_conv]
    obtain lr ts n where first: "ts 0 = s" and last: "ts n = u" and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> ?Q {lr i}" and lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> R"
      by blast
    from vt[unfolded qrsteps_rules_conv]
    obtain lr' ts' n' where first': "ts' 0 = v" and last': "ts' n' = t" and steps': "\<And> i. i < n' \<Longrightarrow> (ts' i, ts' (Suc i)) \<in> ?Q {lr' i}" and lr': "\<And> i. i < n' \<Longrightarrow> lr' i \<in> R"
      by blast
    from uv[unfolded qrstep_rule_conv[where R = R']] obtain lr'' where lr'': "lr'' \<in> R'" and uv: "(u,v) \<in> qrstep nfs Q {lr''}" by auto
    let ?lr = "\<lambda> i. if i < n then lr i else if i = n then lr'' else lr' (i - Suc n)"
    let ?ts = "\<lambda> i. if i \<le> n then ts i else ts' (i - Suc n)"
    let ?n = "Suc (n + n')"
    show ?Right
    proof (intro exI conjI)
      show "\<forall>i < ?n. (?ts i, ?ts (Suc i)) \<in> ?Q {?lr i} \<and> ?lr i \<in> R \<union> R'"
      proof (intro allI impI)
        fix i
        assume i: "i < ?n"
        show "(?ts i, ?ts (Suc i)) \<in> ?Q {?lr i} \<and> ?lr i \<in> R \<union> R'"
        proof (cases "i < n")
          case True
          with steps lr show ?thesis by simp
        next
          case False
          show ?thesis
          proof (cases "i = n")
            case True
            with uv lr'' first' last show ?thesis by simp
          next
            case False
            with \<open>\<not> i < n\<close> have "i > n" by auto
            then have "i = Suc n + (i - Suc n)" by auto
            then obtain k where i': "i = Suc n + k" by auto
            with i have k: "k < n'" by auto
            from steps'[OF k] lr'[OF k] show ?thesis unfolding i'
              by simp
          qed
        qed
      qed
    next
      show "?ts 0 = s" using first by auto
    next
      show "?ts ?n = t" using last' by auto
    next
      show "n < ?n" by auto
    next
      show "?lr n \<in> R'" using lr'' by auto
    qed
  qed
qed

lemma qrsteps_rules_conv'':
  assumes first: "ts 0 = s"
    and last: "ts n = t"
    and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}"
    and lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> R' \<union> R"
    and i: "i < n"
    and i': "lr i \<in> R'"
  shows "(s, t) \<in> (qrstep nfs Q (R' \<union> R))\<^sup>* O qrstep nfs Q R' O (qrstep nfs Q (R' \<union> R))\<^sup>*"
proof -
  let ?Q = "qrstep nfs Q"
  let ?R = "?Q (R' \<union> R)"
  let ?R' = "?Q R'"
  have one: "(s,ts i) \<in> ?R\<^sup>*"
    unfolding qrsteps_rules_conv using first steps lr i 
    by (intro exI[of _ i] exI[of _ ts] exI[of _ lr], auto)
  have two: "(ts i, ts (Suc i)) \<in> ?R'"
    unfolding qrstep_rule_conv[where R = R'] using steps[OF i] i' by auto
  from i have n: "n = (n - Suc i) + Suc i" by auto
  then obtain k where n: "n = k + Suc i" by auto
  have three: "(ts (Suc i), t) \<in> ?R\<^sup>*"
    unfolding qrsteps_rules_conv using insert last lr steps n
    by (intro exI[of _ k] exI[of _ "shift ts (Suc i)"] exI[of _ "shift lr (Suc i)"], auto)
  from one two three
  show ?thesis by auto
qed

lemma normalize_subst_qrsteps_inn_partial:
  fixes Q R R' \<sigma> nfs b
  defines \<tau>: "\<tau> \<equiv> \<lambda> x. if b x then some_NF (qrstep nfs Q R') (\<sigma> x) else \<sigma> x"
  assumes UNF: "UNF (qrstep nfs Q R')"
  and R': "\<And> x u. x \<in> vars_term t \<Longrightarrow> b x \<Longrightarrow> (\<sigma> x,u) \<in> (qrstep nfs Q R)\<^sup>* \<Longrightarrow> (\<sigma> x,u) \<in> (qrstep nfs Q R')\<^sup>*"
  and steps: "(t \<cdot> \<sigma>,s) \<in> (qrstep nfs Q R)\<^sup>*"
  and s: "s \<in> NF_terms Q"
  and inn: "NF_terms Q \<subseteq> NF_trs R'"
  shows "(\<forall>x \<in> vars_term t. (\<sigma> x, \<tau> x) \<in> (qrstep nfs Q R')\<^sup>* \<and> (b x \<longrightarrow> \<tau> x \<in> NF_terms Q)) \<and> (t \<cdot> \<tau>, s) \<in> (qrstep nfs Q R)\<^sup>*"
  using steps s R'
proof (induct t arbitrary: s)
  case (Var x)
  let ?QR = "qrstep nfs Q R"
  let ?QR' = "qrstep nfs Q R'"
  from Var(2) inn have sNF: "s \<in> NF_trs R'" by auto
  with NF_anti_mono[OF qrstep_mono[OF subset_refl, of Q "{}" nfs R']]
  have sNF': "s \<in> NF ?QR'" by auto
  show ?case
  proof (cases "b x")
    case True
    from Var(1) Var(3)[OF _ True] have steps: "(\<sigma> x, s) \<in> ?QR'\<^sup>*" by auto
    from some_NF_UNF[OF UNF steps sNF'] have s: "s = \<tau> x" unfolding \<tau> using True by auto
    then show ?thesis using steps Var(2) by auto
  next
    case False
    then show ?thesis using steps Var unfolding \<tau> by auto
  qed
next
  case (Fun f ts)
  let ?QR = "qrstep nfs Q R"
  let ?QR' = "qrstep nfs Q R'"
  let ?P = "\<lambda> ss i. (\<forall> x \<in> vars_term (ts ! i). (\<sigma> x, \<tau> x) \<in> ?QR'\<^sup>* \<and> (b x \<longrightarrow> \<tau> x \<in> NF_terms Q)) \<and> (ts ! i \<cdot> \<tau>, ss ! i) \<in> ?QR\<^sup>*"
  {
    fix ss
    assume len: "length ss = length ts"
    and steps: "\<And> i. i < length ts \<Longrightarrow> (ts ! i \<cdot> \<sigma>, ss ! i) \<in> ?QR\<^sup>*"
    and NF: "\<And> i. i < length ts \<Longrightarrow> ss ! i \<in> NF_terms Q"
    let ?p = "?P ss"
    {
      fix i
      assume i: "i < length ts"
      with len have mem: "ts ! i \<in> set ts" by auto
      have "?p i"
        by (rule Fun(1)[OF mem steps[OF i] NF[OF i] Fun(4)], insert mem, auto)
    } note p = this
    then have "\<forall> i < length ts. ?p i" by auto
  } note main = this
  {
    fix s
    assume steps: "(Fun f ts \<cdot> \<sigma>, s) \<in> (nrqrstep nfs Q R)\<^sup>*" and NF: "\<And> u. u \<lhd> s \<Longrightarrow>  u \<in> NF_terms Q"
    from nrqrsteps_preserve_root[OF steps]
    obtain ss where s: "s = Fun f ss" and len: "length ss = length ts" by (cases s, auto)
    note main = main[OF len]
    {
      fix i
      assume i: "i < length ts"
      from nrqrsteps_imp_arg_qrsteps[OF steps, of i] i len
      have steps: "(ts ! i \<cdot> \<sigma>, ss ! i) \<in> ?QR\<^sup>*" unfolding s by auto
      have NF: "ss ! i \<in> NF_terms Q"
        by (rule NF, unfold s, insert i len, auto)
      note steps NF
    }
    note main = main[OF this]
    then have \<tau>: "\<And> i. i < length ts \<Longrightarrow> ?P ss i" by blast
    have "(\<forall>x\<in>vars_term (Fun f ts).
             (\<sigma> x, \<tau> x) \<in> ?QR'\<^sup>* \<and> (b x \<longrightarrow> \<tau> x \<in> NF_terms Q)) \<and>
             (Fun f ts \<cdot> \<tau>, s) \<in> ?QR\<^sup>*"
    proof (intro conjI, intro ballI)
      fix x
      assume "x \<in> vars_term (Fun f ts)"
      then obtain i where i: "i < length ts" and x: "x \<in> vars_term (ts ! i)"
        by (auto simp: set_conv_nth)
      with \<tau> show "(\<sigma> x, \<tau> x) \<in> ?QR'\<^sup>* \<and> (b x \<longrightarrow> \<tau> x \<in> NF_terms Q)" by auto
    next
      from len have len: "length (map (\<lambda> t. t \<cdot> \<tau>) ts) = length ss" by simp
      show "(Fun f ts \<cdot> \<tau>, s) \<in> ?QR\<^sup>*" unfolding s
        using \<tau>[THEN conjunct2]
        using args_qrsteps_imp_qrsteps[OF len, of nfs Q R f] by auto
    qed
  } note main = this
  from firstStep[OF qrstep_iff_rqrstep_or_nrqrstep Fun(2)]
  show ?case
  proof
    assume steps: "(Fun f ts \<cdot> \<sigma>, s) \<in> (nrqrstep nfs Q R)\<^sup>*"
    show ?thesis
    proof (rule main[OF steps])
      fix u
      assume sub: "s \<rhd> u"
      then have "s \<unrhd> u" by auto
      show "u \<in> NF_terms Q"
        by (rule NF_subterm[OF Fun(3)], insert sub, auto)
    qed
  next
    assume steps: "(Fun f ts \<cdot> \<sigma>, s) \<in> (nrqrstep nfs Q R)\<^sup>* O rqrstep nfs Q R O ?QR\<^sup>*"
    then obtain u v where one: "(Fun f ts \<cdot> \<sigma>, u) \<in> (nrqrstep nfs Q R)\<^sup>*"
      and two: "(u,v) \<in> rqrstep nfs Q R"
      and three: "(v,s) \<in> ?QR\<^sup>*" by auto
    {
      fix u'
      assume "u \<rhd> u'"
      then have "u' \<in> NF_terms Q" using two[unfolded rqrstep_def] by auto
    }
    from main[OF one this]
    have first: "\<forall> x \<in> vars_term (Fun f ts). (\<sigma> x, \<tau> x) \<in> ?QR'\<^sup>* \<and> (b x \<longrightarrow> \<tau> x \<in> NF_terms Q)"
      and steps: "(Fun f ts \<cdot> \<tau>, u) \<in> ?QR\<^sup>*" by blast+
    from two have "(u,v) \<in> ?QR" unfolding qrstep_iff_rqrstep_or_nrqrstep by auto
    with three have steps2: "(u,s) \<in> ?QR\<^sup>*" by auto
    show ?thesis
      by (intro conjI, rule first, insert steps steps2, auto)
  qed
qed

lemma normalize_subst_qrsteps_inn:
  fixes Q R R' \<sigma> nfs
  defines \<tau>: "\<tau> \<equiv> \<lambda> x. some_NF (qrstep nfs Q R') (\<sigma> x)"
  assumes UNF: "UNF (qrstep nfs Q R')"
  and R': "\<And> x u. x \<in> vars_term t \<Longrightarrow> (\<sigma> x,u) \<in> (qrstep nfs Q R)\<^sup>* \<Longrightarrow> (\<sigma> x,u) \<in> (qrstep nfs Q R')\<^sup>*"
  and steps: "(t \<cdot> \<sigma>,s) \<in> (qrstep nfs Q R)\<^sup>*"
  and s: "s \<in> NF_terms Q"
  and inn: "NF_terms Q \<subseteq> NF_trs R'"
  shows "(\<forall>x \<in> vars_term t. (\<sigma> x, \<tau> x) \<in> (qrstep nfs Q R')\<^sup>* \<and> \<tau> x \<in> NF_terms Q) \<and> (t \<cdot> \<tau>, s) \<in> (qrstep nfs Q R)\<^sup>*"
  using normalize_subst_qrsteps_inn_partial[OF UNF R' steps s inn, of "\<lambda> _. True", unfolded if_True]
  unfolding \<tau> by blast

lemma Tinf_imp_SN_nr_first_root_step_rel:
  assumes Tinf: "t \<in> Tinf (relto (qrstep nfs Q R) (qrstep nfs Q' S))"
  shows "SN_on (relto (nrqrstep nfs Q R) (nrqrstep nfs Q' S)) {t} \<and> (\<exists> s u. (t,s) \<in> (nrqrstep nfs Q R \<union> nrqrstep nfs Q' S)\<^sup>* \<and> (s,u) \<in> rqrstep nfs Q R \<union> rqrstep nfs Q' S \<and> \<not> SN_on (relto (qrstep nfs Q R) (qrstep nfs Q' S)) {u})"
proof -
  let ?R = "qrstep nfs Q R"
  let ?S = "qrstep nfs Q' S"
  let ?rel = "relto ?R ?S"
  let ?nR = "nrqrstep nfs Q R"
  let ?nS = "nrqrstep nfs Q' S"
  let ?nrel = "relto ?nR ?nS"
  let ?rR = "rqrstep nfs Q R"
  let ?rS = "rqrstep nfs Q' S"
  let ?N = "?nR \<union> ?nS"
  let ?RO = "?rR \<union> ?rS"
  from Tinf[unfolded Tinf_def] have notSN: "\<not> SN_on ?rel {t}" and min: "\<And> s. s \<lhd> t \<Longrightarrow> SN_on ?rel {s}" by auto
  from this[unfolded SN_rel_on_def[symmetric] SN_rel_on_conv]
    have nSN: "\<not> SN_rel_on_alt ?R ?S {t}" and min2: "\<And> s. s \<lhd> t \<Longrightarrow> SN_rel_on_alt ?R ?S {s}" by auto
  from nSN[unfolded SN_rel_on_alt_def] obtain ts where start: "ts 0 = t" and steps: "\<And> i. (ts i, ts (Suc i)) \<in> ?R \<union> ?S" and inf: "INFM i. (ts i, ts (Suc i)) \<in> ?R" by auto
  show ?thesis
  proof (cases "SN_on ?nrel {t}")
    case True
    from True[unfolded SN_rel_on_def[symmetric] SN_rel_on_conv]
    have "SN_rel_on_alt ?nR ?nS {ts 0}" unfolding start .
    note SN = this[unfolded SN_rel_on_alt_def, rule_format, of ts]
    let ?P = "\<lambda> i. (ts i, ts (Suc i)) \<in> ?RO"
    have "\<exists> i. ?P i"
    proof (rule ccontr)
      assume nthesis: "\<not> ?thesis"
      then have "\<And> i. (ts i, ts (Suc i)) \<in> ?N" using steps[unfolded qrstep_iff_rqrstep_or_nrqrstep] by auto
      with SN have "\<not> (INFM i. (ts i, ts (Suc i)) \<in> ?nR)" by auto
      then show False
      proof (elim notE, unfold INFM_nat_le, intro allI)
        fix m
        from inf[unfolded INFM_nat_le] obtain n where n: "n \<ge> m" and step: "(ts n, ts (Suc n)) \<in> ?R" by auto
        from step nthesis have "(ts n, ts (Suc n)) \<in> ?nR" unfolding qrstep_iff_rqrstep_or_nrqrstep by auto
        then show "\<exists> n \<ge> m. (ts n, ts (Suc n)) \<in> ?nR" using n by auto
      qed
    qed
    then obtain i where step: "?P i" by auto
    from LeastI[of ?P, OF step] have step: "?P (LEAST i. ?P i)" .
    obtain i where i: "i = (LEAST i. ?P i)" by auto
    from step have step: "?P i" unfolding i .
    {
      fix j
      assume "j < i"
      from not_less_Least[OF this[unfolded i]] have "\<not> ?P j" .
      with steps[of j] have "(ts j, ts (Suc j)) \<in> ?N"
        unfolding qrstep_iff_rqrstep_or_nrqrstep by auto
    } note nsteps = this
    show ?thesis
    proof -
      have "(ts 0, ts i) \<in> ?N\<^sup>*" unfolding rtrancl_fun_conv
        by (rule exI[of _ ts], rule exI[of _ i], insert nsteps, auto)
      moreover
      let ?ss = "shift ts (Suc i)"
      have "\<not> SN_on (relto ?R ?S) {ts (Suc i)}"
        unfolding SN_rel_on_def[symmetric]
        unfolding SN_rel_on_conv SN_rel_on_alt_def
        unfolding not_all not_imp not_not
      proof (rule exI[of _ ?ss], intro conjI allI)
        fix j
        show "(?ss j, ?ss (Suc j)) \<in> ?R \<union> ?S" using steps[of "j + Suc i"] by auto
      next
        show "?ss 0 \<in> {ts (Suc i)}" by simp
      next
        show "INFM j. (?ss j, ?ss (Suc j)) \<in> ?R"
          unfolding INFM_nat_le
        proof (rule allI)
          fix m
          from inf[unfolded INFM_nat_le, rule_format, of "m + Suc i"]
          obtain n where n: "n \<ge> m + Suc i" and step: "(ts n, ts (Suc n)) \<in> ?R" by auto
          show "\<exists> n \<ge> m. (?ss n, ?ss (Suc n)) \<in> ?R"
            by (rule exI[of _ "n - Suc i"], insert n step, auto)
        qed
      qed
      ultimately show ?thesis
        using True step start by blast
    qed
  next
    case False
    from this[unfolded SN_rel_on_def[symmetric] SN_rel_on_conv]
    have nSN: "\<not> SN_rel_on_alt ?nR ?nS {t}" .
    from nSN[unfolded SN_rel_on_alt_def] obtain ts where start: "ts 0 = t" and nsteps: "\<And> i. (ts i, ts (Suc i)) \<in> ?N" and inf: "INFM i. (ts i, ts (Suc i)) \<in> ?nR" by auto
    obtain f ss where init: "ts 0 = Fun f ss"
      using nrqrstep_imp_arg_qrstep[of "ts 0" "ts (Suc 0)"] nsteps[of 0]
      by (cases "ts 0", auto)
    let ?n = "length ss"
    obtain n where n: "n = ?n" by auto
    {
      fix i
      have "\<exists> ssi. ts i = Fun f ssi \<and> length ssi = n"
      proof (induct i)
        case 0
        then show ?case unfolding init n by auto
      next
        case (Suc i)
        from Suc obtain ssi where tsi: "ts i = Fun f ssi"  and n: "length ssi = n" by auto
        from nrqrstep_preserves_root[of "ts i" "ts (Suc i)"] nsteps[of i]
        have "root (ts (Suc i)) = root (ts i)" by auto
        then show ?case unfolding tsi root.simps n by (cases "ts (Suc i)", auto)
      qed
    }
    from choice[OF allI[OF this]] obtain sss where ts: "\<And> i. ts i = Fun f (sss i)" and len: "\<And> i. length (sss i) = n" by force
    let ?strict = "\<lambda> i. \<exists> j < n. (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    have inf: "INFM i. ?strict i"
      unfolding INFM_nat_le
    proof (intro allI)
      fix i
      from inf[unfolded INFM_nat_le, rule_format, of i] obtain k where
        k: "k \<ge> i" and step: "(ts k, ts (Suc k)) \<in> ?nR" by auto
      show "\<exists> k \<ge> i. ?strict k"
        by (rule exI, rule conjI[OF k],
          insert nrqrstep_imp_arg_qrstep[OF step] ts len, auto)
    qed
    let ?idx = "\<lambda> i. if ?strict i then (SOME j. j < n \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R)
      else 0"
    obtain idx where idx: "idx = ?idx" by auto
    {
      fix i
      assume stri: "?strict i"
      then have idxi: "idx i = (SOME j. j < n \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R)" unfolding idx by simp
      from someI_ex[OF stri] have "idx i < n \<and> (sss i ! idx i, sss (Suc i) ! idx i) \<in> ?R" unfolding idxi .
    } note idx_strict = this
    {
      fix i
      have "idx i \<le> n" using idx_strict[of i] by (cases "?strict i", auto simp: idx)
    } note idx_n = this
    {
      fix X
      have "finite (idx ` X)"
      proof (rule finite_subset)
        show "idx ` X \<subseteq> { i . i \<le> n}" using idx_n by auto
      next
        have id: "{i. i \<le> n} = set [0 ..< Suc n]" by auto
        show "finite {i. i \<le> n}" unfolding id by (rule finite_set)
      qed
    } note fin = this
    note pigeon = pigeonhole_infinite[OF inf[unfolded INFM_iff_infinite] fin]
    then obtain j where "infinite { i \<in> {i. ?strict i}. idx i = j}" by auto
    then have inf: "INFM i. ?strict i \<and> idx i = j" unfolding INFM_iff_infinite by simp
    note inf = inf[unfolded INFM_nat_le, rule_format]
    {
      from inf[of 0] obtain k where stri: "?strict k" and idx: "idx k = j" by auto
      from idx_strict[OF stri] idx have "j < n" by auto
    } note jn = this
    with n have "ss ! j \<in> set ss" by auto
    with init have "ss ! j \<lhd> ts 0" by auto
    from min[unfolded start[symmetric], OF this] have SN: "SN_on ?rel {ss ! j}" by auto
    let ?ss = "\<lambda> i. sss i ! j"
    let ?RS = "?R \<union> ?S"
    from SN have SN: "SN_on ?rel {?ss 0}" using ts[of 0] init by simp
    {
      fix i
      have "(?ss i, ?ss (Suc i)) \<in> ?RS^="
      proof (cases "(ts i, ts (Suc i)) \<in> ?nS")
        case True
        from nrqrstep_imp_arg_qrsteps[OF True, of j]
        show ?thesis unfolding ts by simp
      next
        case False
        with nsteps[of i]
        have "(ts i, ts (Suc i)) \<in> ?nR" by auto
        from nrqrstep_imp_arg_qrsteps[OF this, of j]
        show ?thesis unfolding ts by auto
      qed
    } note j_steps = this
    let ?Rel = "?RS\<^sup>* O ?R O ?RS\<^sup>*"
    {
      fix i
      have "(?ss i, ?ss (Suc i)) \<in> ?RS\<^sup>* \<union> ?Rel"
        by (rule set_mp[OF _ j_steps[of i]], regexp)
    } note jsteps = this
    from SN_on_trancl[OF SN, unfolded relto_trancl_conv]
    have SN: "SN_on ?Rel {?ss 0}" .
    have compat: "?RS\<^sup>* O ?Rel \<subseteq> ?Rel" by regexp
    from non_strict_ending[of ?ss "?RS\<^sup>*" ?Rel, OF allI[OF jsteps] compat SN]
    obtain k where k: "\<And> l. l \<ge> k \<Longrightarrow> (?ss l, ?ss (Suc l)) \<notin> ?Rel" by auto
    from inf[of k] obtain l where lk: "l \<ge> k" and strict: "?strict l"  and lj: "idx l = j" by auto
    from k[OF lk] have no_step: "(?ss l, ?ss (Suc l)) \<notin> ?R" by auto
    with idx_strict[OF strict] lj have False by auto
    then show ?thesis by auto
  qed
qed

lemma nrqrstep_empty[simp]: "nrqrstep nfs Q {} = {}" unfolding nrqrstep_def by auto

lemma Tinf_imp_SN_nr_first_root_step:
  assumes Tinf: "t \<in> Tinf (qrstep nfs Q R)"
  shows "SN_on (nrqrstep nfs Q R) {t} \<and> (\<exists> s u. (t,s) \<in> (nrqrstep nfs Q R)\<^sup>* \<and> (s,u) \<in> rqrstep nfs Q R \<and> \<not> SN_on (qrstep nfs Q R) {u})"
  using Tinf_imp_SN_nr_first_root_step_rel[of t nfs Q "{}" Q R]
  using Tinf by auto

lemma SN_on_subterms_imp_SN_on_nrqrstep:
  fixes R :: "('f, 'v) trs"
  assumes "\<forall>s\<lhd>t. SN_on (qrstep nfs Q R) {s}"
  shows "SN_on (nrqrstep nfs Q R) {t}"
proof (cases "SN_on (qrstep nfs Q R) {t}")
  case True
  then show ?thesis unfolding qrstep_iff_rqrstep_or_nrqrstep unfolding SN_defs by auto
next
  case False
  with assms have "t \<in> Tinf (qrstep nfs Q R)" unfolding Tinf_def by auto
  from Tinf_imp_SN_nr_first_root_step[OF this]
  show ?thesis by simp
qed


lemma SN_args_imp_SN_rel:
  assumes SN: "\<And>s. s \<in> set ss \<Longrightarrow> SN_on (relto (qrstep nfs Q R) (qrstep nfs Q S)) {s}"
  and nvar: "\<forall>(l, r)\<in>R \<union> S. is_Fun l"
  and ndef: "\<not> defined (applicable_rules Q (R \<union> S)) (f,length ss)"
  shows "SN_on (relto (qrstep nfs Q R) (qrstep nfs Q S)) {Fun f ss}"
proof (rule ccontr)
  assume nSN: "\<not> ?thesis"
  let ?RS = "relto (qrstep nfs Q R) (qrstep nfs Q S)"
  have "Fun f ss \<in> Tinf ?RS" unfolding Tinf_def
  proof (intro CollectI conjI nSN allI impI)
    fix s
    assume "Fun f ss \<rhd> s"
    then obtain si where si: "si \<in> set ss" and supteq: "si \<unrhd> s" by auto
    from ctxt_closed_SN_on_subt[OF ctxt.closed_relto[OF ctxt_closed_qrstep ctxt_closed_qrstep] SN[OF si] supteq]
    show "SN_on ?RS {s}" .
  qed
  from Tinf_imp_SN_nr_first_root_step_rel[OF this]
  obtain s u where steps: "(Fun f ss, s) \<in> (nrqrstep nfs Q (R \<union> S))\<^sup>*" and su: "(s,u) \<in> rqrstep nfs Q (R \<union> S)"
    unfolding nrqrstep_union rqrstep_union by auto
  from nrqrsteps_preserve_root[OF steps] obtain ts where
    s: "s = Fun f ts" and
    len: "length ss = length ts" by (cases s, auto)
  note ndef = ndef[unfolded len]
  note su = su[unfolded s]
  from rqrstepE[OF su] obtain l r \<sigma> where lr: "(l,r) \<in> (R \<union> S)" and id: "Fun f ts = l \<cdot> \<sigma>"
    and NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms Q" .
  from only_applicable_rules[OF NF] have app: "applicable_rule Q (l,r)" .
  from nvar lr id obtain ls where l: "l = Fun f ls" and len: "length ts = length ls" by (cases l; force)
  note ndef = ndef[unfolded len]
  from app lr ndef show False unfolding l unfolding applicable_rules_def defined_def by force
qed

lemma SN_args_imp_SN:
  assumes "\<And>s. s \<in> set ss \<Longrightarrow> SN_on (qrstep nfs Q R) {s}"
  and "\<forall>(l, r)\<in>R. is_Fun l"
  and "\<not> defined (applicable_rules Q R) (f,length ss)"
  shows "SN_on (qrstep nfs Q R) {Fun f ss}"
  using SN_args_imp_SN_rel[of ss nfs Q "{}" R f] assms by auto

lemma SN_args_imp_SN_rel_rstep:
  assumes "\<And>s. s \<in> set ss \<Longrightarrow> SN_on (relto (rstep R) (rstep S)) {s}"
  and "\<forall>(l, r)\<in>R \<union> S. is_Fun l"
  and "\<not> defined (R \<union> S) (f,length ss)"
  shows "SN_on (relto (rstep R) (rstep S)) {Fun f ss}"
  using SN_args_imp_SN_rel[of ss False "{}" S R f] assms by auto

lemma SN_args_imp_SN_rstep :
  assumes SN: "\<And>s. s \<in> set ss \<Longrightarrow> SN_on (rstep R) {s}"
    and nvar: "\<forall>(l, r)\<in>R. is_Fun l"
    and ndef: "\<not> defined R (f, length ss)"
  shows "SN_on (rstep R) {Fun f ss}"
  using SN_args_imp_SN[of ss False "{}" _ f, OF _ nvar] SN ndef by auto

lemma normalize_subst_qrsteps_inn_infinite:
  fixes Q R R' \<sigma> nfs
  defines \<tau>: "\<tau> \<equiv> \<lambda> x. some_NF (qrstep nfs Q R') (\<sigma> x)"
  assumes UNF: "UNF (qrstep nfs Q R')"
  and R': "\<And> x u. x \<in> vars_term t \<Longrightarrow> (\<sigma> x,u) \<in> (qrstep nfs Q R)\<^sup>* \<Longrightarrow> (\<sigma> x,u) \<in> (qrstep nfs Q R')\<^sup>*"
  and steps: "\<not> SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}"
  and SN: "\<And> x. x \<in> vars_term t \<Longrightarrow> SN_on (qrstep nfs Q R) {\<sigma> x}"
  and inn: "NF_terms Q \<subseteq> NF_trs R'"
  shows "\<not> SN_on (qrstep nfs Q R) {t \<cdot> \<tau>}"
proof -
  let ?R = "qrstep nfs Q R"
  let ?R' = "qrstep nfs Q R'"
  from not_SN_imp_subt_Tinf[OF steps] obtain s
    where subt: "t \<cdot> \<sigma> \<unrhd> s" and s_inf: "s \<in> Tinf ?R" by auto
  from supteq_imp_subt_at[OF subt] obtain p where p: "p \<in> poss (t \<cdot> \<sigma>)"
    and subt: "s = t \<cdot> \<sigma> |_ p" by auto
  show ?thesis
  proof (cases "p \<in> poss t \<and> is_Fun (t |_ p)")
    case True
    obtain tp where tp: "tp = t |_ p" by auto
    with True have p: "p \<in> poss t" and is_fun: "is_Fun tp" by auto
    then have s: "s = tp \<cdot> \<sigma>" by (simp add: subt tp)
    from subt_at_imp_supteq[OF p] have subt: "t \<unrhd> tp" unfolding tp .
    from s_inf[unfolded s] have tp_inf: "tp \<cdot> \<sigma> \<in> Tinf ?R" .
    {
      fix x
      assume "x \<in> vars_term tp"
      then have "x \<in> vars_term t" using supteq_imp_vars_term_subset [OF subt] by auto
    } note vars = this
    let ?n = "nrqrstep nfs Q R"
    let ?r = "rqrstep nfs Q R"
    from tp_inf[unfolded Tinf_def] have SN: "\<forall> s \<lhd> tp \<cdot> \<sigma>. SN_on ?R {s}"
      and nSN: "\<not> SN_on ?R {tp \<cdot> \<sigma>}" by auto
    from SN_on_subterms_imp_SN_on_nrqrstep[OF SN] have SN: "SN_on ?n {tp \<cdot> \<sigma>}"
      by auto
    from nSN obtain f where start: "f 0 = tp \<cdot> \<sigma>"
      and steps: "\<forall> i. (f i, f (Suc i)) \<in> ?R" by auto
    from chain_Un_SN_on_imp_first_step[OF steps[unfolded qrstep_iff_rqrstep_or_nrqrstep], OF SN[unfolded start[symmetric]]]
    obtain i where root: "(f i, f (Suc i)) \<in> ?r" and nroot: "\<And> j. j < i \<Longrightarrow> (f j, f (Suc j)) \<in> ?n" by auto
    have nroot: "(tp \<cdot> \<sigma>, f i) \<in> ?n\<^sup>*" unfolding rtrancl_fun_conv
      by (intro exI[of _ f] exI[of _ i], unfold start, insert nroot, auto)
    from is_fun obtain g ts where is_fun: "tp = Fun g ts" by (cases tp, auto)
    note nroot = nroot[unfolded is_fun]
    from nrqrsteps_preserve_root[OF nroot] obtain ss where fi: "f i = Fun g ss" and len: "length ss = length ts" by (cases "f i", auto)
    note root = root[unfolded fi]
    from root[unfolded rqrstep_def] have NF:  "\<And> u. u \<lhd> Fun g ss \<Longrightarrow> u \<in> NF_terms Q" by auto
    let ?ts = "map (\<lambda> t. t \<cdot> \<tau>) ts"
    let ?lts = "length ?ts"
    {
      fix i
      assume i: "i < ?lts"
      from nrqrsteps_imp_arg_qrsteps[OF nroot, of i] i len
      have steps: "(ts ! i \<cdot> \<sigma>, ss ! i) \<in> ?R\<^sup>*" unfolding fi by auto
      have NF: "ss ! i \<in> NF_terms Q"
        by (rule NF, insert i len, auto)
      {
        fix x
        assume "x \<in> vars_term (ts ! i)"
        with i have "x \<in> vars_term (Fun g ts)" by auto
        with vars have "x \<in> vars_term t" unfolding is_fun by auto
      } note vars = this
      from normalize_subst_qrsteps_inn[OF UNF R'[OF vars] steps NF inn]
      have "(ts ! i \<cdot> \<tau>, ss ! i) \<in> ?R\<^sup>*" unfolding \<tau> ..
      then have "(?ts ! i, ss ! i) \<in> ?R\<^sup>*" using i by auto
    } note \<tau>steps = this
    from len have len: "?lts = length ss" by simp
    from args_qrsteps_imp_qrsteps[OF len, of nfs Q R g] \<tau>steps
    have tpfi: "(tp \<cdot> \<tau>, f i) \<in> ?R\<^sup>*" unfolding is_fun fi by simp
    obtain g where g: "g \<equiv> \<lambda> j. f (i + j)" by auto
    from steps have "\<And> i. (g i, g (Suc i)) \<in> ?R" unfolding g by auto
    then have "\<not> SN_on ?R {g 0}" by auto
    then have nSN: "\<not> SN_on ?R {f i}" unfolding g by auto
    with steps_preserve_SN_on[OF tpfi]
    have "\<not> SN_on ?R {tp \<cdot> \<tau>}" by auto
    with ctxt_closed_SN_on_subt[OF ctxt_closed_qrstep _ supteq_subst[OF subt], of nfs Q R \<tau>]
    show ?thesis by auto
  next
    case False
    from pos_into_subst[OF refl p False]
    obtain q q' x where pq: "p = q @ q'" and q: "q \<in> poss t" and t: "t |_ q = Var x" by auto
    from subteq_Var_imp_in_vars_term [OF subt_at_imp_supteq [OF q, unfolded t]]
      have x: "x \<in> vars_term t" .
    have "s = \<sigma> x |_ q' \<and> q' \<in> poss (\<sigma> x)"
      using p
      unfolding poss_append_poss subt pq
        and subt_at_append [OF poss_imp_subst_poss [OF q]]
        and subt_at_subst [OF q] t by simp
    then have s: "\<sigma> x \<unrhd> s" using subt_at_imp_supteq by auto
    from ctxt_closed_SN_on_subt[OF ctxt_closed_qrstep SN[OF x] s]
    have "SN_on ?R {s}" by auto
    with s_inf[unfolded Tinf_def] show ?thesis by auto
  qed
qed

lemma qrstep_r_p_s_conv:
  fixes s t
  assumes step: "(s, t) \<in> qrstep_r_p_s nfs Q R lr p \<sigma>"
  defines [simp]: "C \<equiv> ctxt_of_pos_term p s"
  shows "p \<in> poss s" and "p \<in> poss t" and "s = C\<langle>fst lr \<cdot> \<sigma>\<rangle>" and "t = C\<langle>snd lr \<cdot> \<sigma>\<rangle>" and "NF_subst nfs lr \<sigma> Q" and "ctxt_of_pos_term p t = C"
proof -
  from step have p_in_s: "p \<in> poss s" unfolding qrstep_r_p_s_def by simp
  have p_in_t: "p \<in> poss t" using qrstep_r_p_s_imp_poss[OF step] by simp
  have C: "C = ctxt_of_pos_term p t" using ctxt_of_pos_term_qrstep_below[OF step] by simp

  from p_in_s show "p \<in> poss s".
  show "p \<in> poss t" using qrstep_r_p_s_imp_poss[OF step] by simp
  from step show "s = C\<langle>fst lr \<cdot> \<sigma>\<rangle>" unfolding qrstep_r_p_s_def using ctxt_supt_id[OF p_in_s] by simp
  from C show "t = C\<langle>snd lr \<cdot> \<sigma>\<rangle>" using step unfolding qrstep_r_p_s_def using ctxt_supt_id[OF p_in_t] by simp
  from step show "NF_subst nfs lr \<sigma> Q" unfolding qrstep_r_p_s_def by simp
  from C show "ctxt_of_pos_term p t = C" by simp
qed

lemma qrstep_r_p_s_redex_reduct:
  assumes step: "(s,t) \<in> qrstep_r_p_s nfs Q R lr p \<sigma>"
  shows "t|_p = snd lr \<cdot> \<sigma>"
  using qrstep_r_p_s_conv[OF step]
  by (metis replace_at_subt_at)

lemma qrstep_r_p_s_imp_nrqrstep:
  assumes step: "(s, t) \<in> qrstep_r_p_s nfs Q R lr p \<sigma>" and ne: "p \<noteq> []"
  shows "(s, t) \<in> nrqrstep nfs Q R"
proof -
  from step[unfolded qrstep_r_p_s_def]
  have NF: "\<forall> u \<lhd> fst lr \<cdot> \<sigma>. u \<in> NF_terms Q"
    and p: "p \<in> poss s"
    and lr: "lr \<in> R"
    and s: "s |_ p = fst lr \<cdot> \<sigma>"
    and t: "t = replace_at s p (snd lr \<cdot> \<sigma>)"
    and nfs: "NF_subst nfs lr \<sigma> Q" by auto
  show ?thesis
  proof (rule nrqrstepI[OF NF _ _ _ t])
    show "(fst lr, snd lr) \<in> R" using lr by simp
  next
    from ne obtain i q where ne: "p = (i # q)" by (cases p, auto)
    with p show "ctxt_of_pos_term p s \<noteq> \<box>" by (cases s, auto)
  qed (insert ctxt_supt_id[OF p, unfolded s] nfs, auto)
qed

lemma qrsteps_imp_qrsteps_r_p_s:
  assumes "(s, t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "\<exists> n ts lr p \<sigma>. ts 0 = s \<and> ts n = t \<and> (\<forall> i < n. (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<sigma> i))"
proof -
  from assms[unfolded qrsteps_rules_conv]
  obtain n ts lr where
    first: "ts 0 = s"
    and last: "ts n = t"
    and steps: "\<forall> i < n. (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> R" by auto
  let ?ts = "\<lambda> i. (ts i, ts (Suc i))"
  {
    fix i
    assume "i < n"
    from steps[rule_format, OF this]
    have "?ts i \<in> qrstep nfs Q (R \<inter> {lr i})" by auto
    from this[unfolded qrstep_qrstep_r_p_s_conv] obtain lr' p \<sigma> where "?ts i \<in> qrstep_r_p_s nfs Q (R \<inter> {lr i}) lr' p \<sigma>" by auto
    then have "\<exists> p \<sigma>. ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) p \<sigma>" unfolding qrstep_r_p_s_def by auto
  }
  then have "\<forall> i. \<exists> p \<sigma>. i < n \<longrightarrow> ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) p \<sigma>" by simp
  from choice[OF this] obtain p where "\<forall> i. \<exists> \<sigma>. i < n \<longrightarrow> ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) (p i) \<sigma>" by auto
  from choice[OF this] obtain \<sigma> where steps: "\<And> i. i < n \<Longrightarrow> ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<sigma> i)" by auto
  show ?thesis
  proof (intro exI conjI)
    show "\<forall> i < n. ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<sigma> i)" using steps by simp
  qed (insert first last, auto)
qed

lemma qrsteps_r_p_s_imp_qrsteps:
  assumes first: "ts 0 = s"
    and last: "ts n = t"
    and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<sigma> i)"
  shows "(s, t) \<in> (qrstep nfs Q R)\<^sup>*"
  unfolding qrsteps_rules_conv
proof (intro exI[of _ n] exI[of _ ts] exI[of _ lr] conjI first last allI, intro allI impI)
  fix i
  assume i: "i < n"
  show "(ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> R" using steps[OF i] unfolding qrstep_qrstep_r_p_s_conv
    unfolding qrstep_r_p_s_def by blast
qed

lemma qrstep_r_p_s_imp_applicable_rule: "(s,t) \<in> qrstep_r_p_s nfs Q R lr p \<sigma> \<Longrightarrow> applicable_rule Q lr"
  using only_applicable_rules[of "fst lr" \<sigma> Q]
  unfolding qrstep_r_p_s_def
  by (cases lr, simp)

lemma SN_on_qrstep_r_p_s_imp_wf_rule:
  assumes SN: "SN_on (qrstep nfs Q R) {t}"
    and step: "(t, s) \<in> qrstep_r_p_s nfs Q R lr p \<sigma>"
    and nfs: "\<not> nfs"
  shows "vars_term (snd lr) \<subseteq> vars_term (fst lr) \<and> is_Fun (fst lr)"
proof -
  obtain l r where lr: "lr = (l,r)" by force
  from qrstep_r_p_s_imp_applicable_rule[OF step] have u: "applicable_rule Q lr" .
  from step[unfolded lr qrstep_r_p_s_def] have p: "p \<in> poss t" and t: "t |_ p = l \<cdot> \<sigma>" and mem: "(l,r) \<in> R" and NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms Q" by auto
  from SN_on_imp_wwf_rule[OF SN ctxt_supt_id[OF p, unfolded t, symmetric] mem NF nfs]
  have "wwf_rule Q (l,r)" .
  then show ?thesis using u unfolding lr wwf_rule_def by auto
qed

lemma SN_on_Var_gen:
   assumes "Ball (fst ` R) is_Fun" shows "SN_on (qrstep nfs Q R) {Var x}" (is "SN_on _ {?x}")
proof -
  let ?qr = "qrstep nfs Q R"
  show "SN_on ?qr {?x}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain A where "A 0 = ?x" and rsteps: "chain ?qr A"
      unfolding SN_on_def by best
    then have "(?x,A 1) \<in> ?qr" using spec[OF rsteps, of 0] by auto
    then obtain l r C \<sigma> where "(l,r) \<in> R" and x: "Var x = C\<langle>l \<cdot> \<sigma>\<rangle>" by auto
    with assms obtain f ls where "l = Fun f ls" by force
    with x obtain ls where "Var x = C\<langle>Fun f ls\<rangle>" by auto
    then show False by (cases C, auto)
  qed
qed

lemma SN_on_Var:
  assumes "wwf_qtrs Q R" shows "SN_on (qrstep nfs Q R) {Var x}" (is "SN_on _ {?x}")
  by (rule SN_on_Var_gen, insert wwf_qtrs_imp_left_fun[OF assms], force)

lemma wwf_qtrs_imp_nfs_switch_r_p_s: assumes wwf: "wwf_qtrs Q R"
  shows "qrstep_r_p_s nfs Q R = qrstep_r_p_s nfs' Q R"
proof -
  {
    fix nfs nfs' lr p \<sigma> s t
    assume step: "(s,t) \<in> qrstep_r_p_s nfs Q R lr p \<sigma>"
    obtain l r where lr: "lr = (l,r)" by force
    from step[unfolded qrstep_r_p_s_def lr] have *: "(\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q)"
      "p \<in> poss s" "(l,r) \<in> R" "s |_ p = l \<cdot> \<sigma>" "t = (ctxt_of_pos_term p s)\<langle>r \<cdot> \<sigma>\<rangle>" and NF: "NF_subst nfs (l,r) \<sigma> Q" by auto
    have "applicable_rule Q (l,r)" using only_applicable_rules * by auto
    with wwf[unfolded wwf_qtrs_def] * have l: "is_Fun l" and rl: "vars_term r \<subseteq> vars_term l" by auto
    have NF: "NF_subst nfs' (l,r) \<sigma> Q"
      unfolding NF_subst_def
    proof (intro impI subsetI)
      fix u
      assume u: "u \<in> \<sigma> ` vars_rule (l,r)"
      then obtain x where u: "u = \<sigma> x" and x: "x \<in> vars_rule (l,r)" by auto
      from x rl have x: "x \<in> vars_term l" by (cases "x \<in> vars_term l", auto simp: vars_rule_def)
      then have "Var x \<unlhd> l" by auto
      with l have "Var x \<lhd> l" by auto
      from supt_subst[OF this, of \<sigma>] *
      show "u \<in> NF_terms Q" unfolding u by auto
    qed
    with * have "(s,t) \<in> qrstep_r_p_s nfs' Q R lr p \<sigma>" unfolding lr qrstep_r_p_s_def by auto
  } note main = this
  from main[of _ _ nfs _ _ _ nfs'] main[of _ _ nfs' _ _ _ nfs] show ?thesis
    by (intro ext, auto)
qed

lemma wwf_qtrs_imp_nfs_switch: assumes wwf: "wwf_qtrs Q R"
  shows "qrstep nfs Q R = qrstep nfs' Q R"
  using
    qrstep_qrstep_r_p_s_conv[of _ _ nfs Q R]
    qrstep_qrstep_r_p_s_conv[of _ _ nfs' Q R]
    wwf_qtrs_imp_nfs_switch_r_p_s[OF wwf, of nfs nfs'] by auto

lemma wwf_qtrs_imp_nfs_False_switch: assumes "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R"
  shows "qrstep nfs Q R = qrstep False Q R"
proof (cases "nfs \<and> Q \<noteq> {}")
  case True
  from wwf_qtrs_imp_nfs_switch[OF assms] True show ?thesis by auto
next
  case False
  show ?thesis
  proof (cases nfs)
    case True
    with False have "Q = {}" by auto
    then show ?thesis by simp
  qed simp
qed

lemma rqrstep_rename_vars: assumes R: "\<And> st. st \<in> R \<Longrightarrow> \<exists> st'. st' \<in> R' \<and> st =\<^sub>v st'"
  shows "rqrstep nfs Q R \<subseteq> rqrstep nfs Q R'"
proof
  fix x y
  assume "(x,y) \<in> rqrstep nfs Q R"
  from rqrstepE[OF this]
  obtain l r \<sigma> where NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and x: "x = l \<cdot> \<sigma>" and y: "y = r \<cdot> \<sigma>" and lr: "(l,r) \<in> R"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q" .
  from R[OF lr] obtain l' r' where lr': "(l',r') \<in> R'" and eq: "(l,r) =\<^sub>v (l',r')" by auto
  from eq_rule_mod_varsE[OF eq]
    obtain \<sigma>1 \<sigma>2 where 1: "l = l' \<cdot> \<sigma>1" "r = r' \<cdot> \<sigma>1" and 2: "l' = l \<cdot> \<sigma>2" "r' = r \<cdot> \<sigma>2" by auto
  from x y have xy: "x = l' \<cdot> (\<sigma>1 \<circ>\<^sub>s \<sigma>)" "y = r' \<cdot> (\<sigma>1 \<circ>\<^sub>s \<sigma>)" unfolding 1 by auto
  show "(x,y) \<in> rqrstep nfs Q R'"
  proof (rule rqrstepI[OF _ lr' xy])
    show "\<forall>u\<lhd>l' \<cdot> \<sigma>1 \<circ>\<^sub>s \<sigma>. u \<in> NF_terms Q" using NF[unfolded 1] by simp
    show "NF_subst nfs (l', r') (\<sigma>1 \<circ>\<^sub>s \<sigma>) Q"
    proof
      fix x
      assume nfs and x: "x \<in> vars_term l' \<or> x \<in> vars_term r'"
      have  "l' \<cdot> \<sigma>1 \<cdot> \<sigma>2 = l'" "r' \<cdot> \<sigma>1 \<cdot> \<sigma>2 = r'" unfolding 1[symmetric] 2[symmetric] by auto
      then have l': "l' \<cdot> (\<sigma>1 \<circ>\<^sub>s \<sigma>2) = l' \<cdot> Var" and r': "r' \<cdot> (\<sigma>1 \<circ>\<^sub>s \<sigma>2) = r' \<cdot> Var" by auto
      from term_subst_eq_rev[OF l'] term_subst_eq_rev[OF r'] x have "(\<sigma>1 \<circ>\<^sub>s \<sigma>2) x = Var x" by blast
      then have id: "\<sigma>1 x \<cdot> \<sigma>2 = Var x" unfolding subst_compose_def by auto
      then obtain y where x1: "\<sigma>1 x = Var y" by (cases "\<sigma>1 x", auto)
      from x
      have y: "y \<in> vars_term l \<or> y \<in> vars_term r" unfolding 1 using x1 unfolding vars_term_subst by force
      then have y: "y \<in> vars_rule (l,r)" unfolding vars_rule_def by simp
      from nfs[unfolded NF_subst_def] \<open>nfs\<close> y have "\<sigma> y \<in> NF_terms Q" by auto
      then show "(\<sigma>1 \<circ>\<^sub>s \<sigma>) x \<in> NF_terms Q" unfolding subst_compose_def x1 by simp
    qed
  qed
qed

lemma qrstep_rename_vars: assumes R: "\<And> st. st \<in> R \<Longrightarrow> \<exists> st'. st' \<in> R' \<and> st =\<^sub>v st'"
  shows "qrstep nfs Q R \<subseteq> qrstep nfs Q R'"
proof
  fix s t
  assume "(s,t) \<in> qrstep nfs Q R"
  from qrstepE[OF this] obtain C \<sigma> l r where
    "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" "(l, r) \<in> R" and st: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and "NF_subst nfs (l, r) \<sigma> Q" .
  then have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rqrstep nfs Q R" by auto
  from set_mp[OF rqrstep_rename_vars[OF R] this] have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rqrstep nfs Q R'" .
  then have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> qrstep nfs Q R'" unfolding qrstep_iff_rqrstep_or_nrqrstep ..
  with st show "(s,t) \<in> qrstep nfs Q R'" by auto
qed


lemma NF_subst_qrstep: assumes "\<And> fn . fn \<in> funas_term t \<Longrightarrow> \<not> defined (applicable_rules Q R) fn"
  and varsNF: "\<And> x. x \<in> vars_term t \<Longrightarrow> \<sigma> x \<in> NF (qrstep nfs Q R)"
  and var_cond: "\<forall>(l, r) \<in> R. is_Fun l"
  shows "(t \<cdot> \<sigma>) \<in> NF (qrstep nfs Q R)"
proof
  fix s
  show "(t \<cdot> \<sigma>, s) \<notin> qrstep nfs Q R"
  proof
    assume "(t \<cdot> \<sigma>, s) \<in> qrstep nfs Q R"
    from qrstepE[OF this]
    obtain C \<sigma>' l r where nf: "\<forall>u\<lhd>l \<cdot> \<sigma>'. u \<in> NF_terms Q"
      and lr: "(l, r) \<in> R" and t: "t \<cdot> \<sigma> = C\<langle>l \<cdot> \<sigma>'\<rangle>" and nfs: "NF_subst nfs (l, r) \<sigma>' Q" .
    from var_cond lr
      obtain f ls where l: "l = Fun f ls" by (cases l, auto)
    let ?f = "(f,length ls)"
    from l lr only_applicable_rules[OF nf] have "defined (applicable_rules Q R) ?f"
      unfolding applicable_rules_def defined_def by force
    with assms have f: "?f \<notin> funas_term t" by auto
    with varsNF t
    show False
    proof (induct t arbitrary: C)
      case (Var x)
      from Var(1)[of x] Var(2) have NF: "C\<langle>l \<cdot> \<sigma>'\<rangle> \<in> NF (qrstep nfs Q R)" by auto
      with qrstepI[OF nf lr refl refl nfs, of C] show False by auto
    next
      case (Fun g ts)
      from Fun(3-4) arg_cong[OF Fun(3), of root, unfolded l, simplified] l obtain bef D aft where
        C: "C = More g bef D aft" and len: "length ts = Suc (length bef + length aft)" by (cases C, auto)
      from Fun(3)[unfolded C] have id: "map (\<lambda>t. t \<cdot> \<sigma>) ts = bef @ D\<langle>l \<cdot> \<sigma>'\<rangle> # aft" by auto
      let ?i = "length bef"
      let ?t = "ts ! ?i"
      from len have mem: "?t \<in> set ts" by auto
      from len arg_cong[OF id, of "\<lambda> ts. ts ! ?i"] have idt: "?t \<cdot> \<sigma> = D \<langle>l \<cdot> \<sigma>' \<rangle>" by simp
      show False
        by (rule Fun(1)[OF mem Fun(2) idt], insert Fun(4) mem, auto)
    qed
  qed
qed

lemma NF_subst_from_NF_args:
  assumes wf: "Q \<noteq> {} \<Longrightarrow> nfs \<Longrightarrow> wf_rule (s,t)"
  and NF: "set (args (s \<cdot> \<sigma>)) \<subseteq> NF_terms Q"
  shows "NF_subst nfs (s, t) \<sigma> Q"
proof (cases "Q = {} \<or> \<not> nfs")
  case False
  with wf obtain f ss where s: "s = Fun f ss" and vars: "vars_term s \<supseteq> vars_term t"
    unfolding wf_rule_def by (cases s, auto)
  show ?thesis
  proof
    fix x
    assume "x \<in> vars_term s \<or> x \<in> vars_term t"
    with vars have "x \<in> vars_term s" by auto
    with s obtain si where si: "si \<in> set ss" and "x \<in> vars_term si" by auto
    then have "si \<unrhd> Var x" by auto
    then have sub: "si \<cdot> \<sigma> \<unrhd> \<sigma> x" by auto
    from si NF s have "si \<cdot> \<sigma> \<in> NF_terms Q" by auto
    from NF_subterm[OF this sub] show "\<sigma> x \<in> NF_terms Q" .
  qed
qed auto

end
