(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Abstract Completion\<close>

theory Abstract_Completion
  imports
    Ord.Reduction_Order
    Peak_Decreasingness
    Norm_Equiv.Encompassment
    Weighted_Path_Order.Multiset_Extension2
    Knuth_Bendix_Order.Lexicographic_Extension
begin

lemma (in reduction_order) SN_encomp_Un_less:
  "SN ({\<cdot>\<rhd>} \<union> {\<succ>})"
  using SN_encomp_Un_rewrel [of "{\<succ>}"]
    and ctxt and subst and SN_less by blast

lemma (in reduction_order) SN_encomp_Un_less_relto_encompeq:
  "SN (relto ({\<cdot>\<rhd>} \<union> {\<succ>}) {\<cdot>\<unrhd>})"
  using commutes_rewrel_encomp [of "{\<succ>}"] and ctxt and subst
  by (intro qc_SN_relto_encompeq SN_encomp_Un_less)
    (auto dest: encomp_order.less_le_trans)

locale kb = reduction_order less
  for less :: "('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool" (infix "\<succ>" 50) +
  fixes enc :: bool \<comment> \<open>\<open>True\<close> if encompassment condition is used\<close>
begin

definition "rstep_enc R =
  (if enc then {(s, t). \<exists>(l, r)\<in>R. (s, t) \<in> rstep_rule (l, r) \<and> s \<cdot>\<rhd> l}
  else rstep R)"

lemma rstep_encD [dest]:
  "(s, t) \<in> rstep_enc R \<Longrightarrow> (s, t) \<in> rstep R"
  by (auto simp: rstep_enc_def rstep_rule.simps split: if_splits)

inductive KB ::
    "('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> ('a, 'b) trs \<times> ('a, 'b) trs \<Rightarrow> bool" (infix "\<turnstile>\<^sub>K\<^sub>B" 55)
  where
    deduce: "(u, s) \<in> rstep R \<Longrightarrow> (u, t) \<in> rstep R \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B (E \<union> {(s, t)}, R)" |
    orientl: "s \<succ> t \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B (E - {(s, t)}, R \<union> {(s, t)})" |
    orientr: "t \<succ> s \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B (E - {(s, t)}, R \<union> {(t, s)})" |
    delete: "(s, s) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B (E - {(s, s)}, R)" |
    compose: "(t, u) \<in> rstep (R - {(s, t)}) \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B (E, (R - {(s, t)}) \<union> {(s, u)})" |
    simplifyl: "(s, u) \<in> rstep R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B ((E - {(s, t)}) \<union> {(u, t)}, R)" |
    simplifyr: "(t, u) \<in> rstep R \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B ((E - {(s, t)}) \<union> {(s, u)}, R)" |
    collapse: "(t, u) \<in> rstep_enc (R - {(t, s)}) \<Longrightarrow> (t, s) \<in> R \<Longrightarrow> (E, R) \<turnstile>\<^sub>K\<^sub>B (E \<union> {(u, s)}, R - {(t, s)})"

lemma deduce_subset:
  assumes "E' = E \<union> {(s, t)}" and "R' = R"
    and "(u, s) \<in> rstep R" and "(u, t) \<in> rstep R"
  shows "E \<union> R \<subseteq> E' \<union> R'"
  using assms by fast

lemma deduce':
  assumes "E' = E \<union> {(s, t)}" and "R' = R"
    and "(u, s) \<in> rstep R" and "(u, t) \<in> rstep R"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> (rstep R)\<inverse> O rstep R"
  using assms by fast

lemma orientl_subset:
  assumes "E' = E - {(s, t)}" and "R' = R \<union> {(s, t)}"
    and "s \<succ> t" and "(s, t) \<in> E"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> R'\<inverse>"
  using assms by fast

lemma orientl':
  assumes "E' = E - {(s, t)}" and "R' = R \<union> {(s, t)}"
    and "s \<succ> t" and "(s, t) \<in> E"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> E\<inverse>"
  using assms by fast

lemma orientr_subset:
  assumes "E' = E - {(s, t)}" and "R' = R \<union> {(t, s)}"
    and "t \<succ> s" and "(s, t) \<in> E"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> R'\<inverse>"
  using assms by fast

lemma orientr':
  assumes "E' = E - {(s, t)}" and "R' = R \<union> {(t, s)}"
    and "t \<succ> s" and "(s, t) \<in> E"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> E\<inverse>"
  using assms by fast

lemma delete_subset:
  assumes "E' = E - {(s, s)}" and "R' = R"
    and "(s, s) \<in> E"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> Id"
  using assms by fast

lemma delete':
  assumes "E' = E - {(s, s)}" and "R' = R"
    and "(s, s) \<in> E"
  shows "E' \<union> R' \<subseteq> E \<union> R"
  using assms by fast

lemma compose_subset:
  assumes "E' = E" and "R' = (R - {(s, t)}) \<union> {(s, u)}"
    and "(t, u) \<in> rstep (R - {(s, t)})" and "(s, t) \<in> R"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> rstep R' O (rstep R')\<inverse>"
  using assms by fast

lemma compose':
  assumes "E' = E" and "R' = (R - {(s, t)}) \<union> {(s, u)}"
    and "(t, u) \<in> rstep (R - {(s, t)})" and "(s, t) \<in> R"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> rstep R O rstep R"
  using assms by fast

lemma simplifyl_subset:
  assumes "E' = (E - {(s, t)}) \<union> {(u, t)}" and "R' = R"
    and "(s, u) \<in> rstep R" and "(s, t) \<in> E"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> rstep R' O rstep E' \<union> rstep E' O (rstep R')\<inverse>"
  using assms by fast

lemma simplifyl':
  assumes "E' = (E - {(s, t)}) \<union> {(u, t)}" and "R' = R"
    and "(s, u) \<in> rstep R" and "(s, t) \<in> E"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> (rstep R)\<inverse> O rstep E \<union> rstep E O rstep R"
  using assms by fast

lemma simplifyr_subset:
  assumes "E' = (E - {(s, t)}) \<union> {(s, u)}" and "R' = R"
    and "(t, u) \<in> rstep R" and "(s, t) \<in> E"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> rstep R' O rstep E' \<union> rstep E' O (rstep R')\<inverse>"
  using assms by fast

lemma simplifyr':
  assumes "E' = (E - {(s, t)}) \<union> {(s, u)}" and "R' = R"
    and "(t, u) \<in> rstep R" and "(s, t) \<in> E"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> (rstep R)\<inverse> O rstep E \<union> rstep E O rstep R"
  using assms by fast

lemma collapse_subset:
  assumes "E' = E \<union> {(u, s)}" and "R' = R - {(t, s)}"
    and "(t, u) \<in> rstep_enc (R - {(t, s)})" and "(t, s) \<in> R"
  shows "E \<union> R \<subseteq> E' \<union> R' \<union> rstep_enc R' O rstep E'"
  using assms by fast

lemma collapse':
  assumes "E' = E \<union> {(u, s)}" and "R' = R - {(t, s)}"
    and "(t, u) \<in> rstep_enc (R - {(t, s)})" and "(t, s) \<in> R"
  shows "E' \<union> R' \<subseteq> E \<union> R \<union> (rstep R)\<inverse> O rstep R"
  using assms by fast

lemma rstep_reflcl_symcl_Un_idemp [simp]:
  "rstep (((rstep R \<union> rstep S)\<^sup>\<leftrightarrow>)\<^sup>*) = ((rstep R \<union> rstep S)\<^sup>\<leftrightarrow>)\<^sup>*"
  unfolding symcl_Un
  unfolding rstep_simps(5) [symmetric]
  unfolding rstep_union [symmetric]
  unfolding rstep_rtrancl_idemp
  by (rule refl)

lemma KB_subset:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')"
  shows "rstep (E \<union> R) \<subseteq> (rstep R')\<^sup>= O (rstep (E' \<union> R'))\<^sup>= O ((rstep R')\<inverse>)\<^sup>="
proof -
  have "E \<union> R \<subseteq> (rstep R')\<^sup>= O (rstep (E' \<union> R'))\<^sup>= O ((rstep R')\<inverse>)\<^sup>=" (is "?L \<subseteq> ?R")
  proof
    fix s t
    assume *: "(s, t) \<in> ?L"
    from assms show "(s, t) \<in> ?R"
    proof (cases)
      case deduce
      from deduce_subset [OF this] show ?thesis using * by blast
    next
      case orientl
      from orientl_subset [OF this] show ?thesis using * by blast
    next
      case orientr
      from orientr_subset [OF this] show ?thesis using * by blast
    next
      case delete
      from delete_subset [OF this] show ?thesis using * by blast
    next
      case compose
      from compose_subset [OF this] show ?thesis using * by blast
    next
      case simplifyl
      from simplifyl_subset [OF this] show ?thesis using * by blast
    next
      case simplifyr
      from simplifyr_subset [OF this] show ?thesis using * by blast
    next
      case collapse
      from collapse_subset [OF this] show ?thesis using * by (blast 11)
    qed
  qed
  from rstep_mono [OF this] show ?thesis
    by (auto simp: rstep_simps simp flip: rstep_converse)
qed

lemma KB_subset':
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')"
  shows "rstep (E' \<union> R') \<subseteq> ((rstep (E \<union> R))\<^sup>\<leftrightarrow>)\<^sup>*"
    (is "?L \<subseteq> ?R")
proof -
  have "E' \<union> R' \<subseteq> ((rstep (E \<union> R))\<^sup>\<leftrightarrow>)\<^sup>*" (is "?L \<subseteq> ?R")
  proof
    fix s t
    assume *: "(s, t) \<in> ?L"
    from assms show "(s, t) \<in> ?R"
    proof (cases)
      case deduce
      from deduce' [OF this] and *
      have "(s, t) \<in> E \<union> R \<or> (s, t) \<in> (rstep R)\<inverse> O rstep R" by auto
      then show ?thesis
      proof
        assume "(s, t) \<in> (rstep R)\<inverse> O rstep R"
        then obtain u where "(s, u) \<in> (rstep R)\<inverse>" and "(u, t) \<in> rstep R" by auto
        then have "(s, u) \<in> ?R" and "(u, t) \<in> ?R" by auto
        then show ?thesis by simp
      qed blast
    next
      case orientl
      from orientl' [OF this] show ?thesis using * by blast
    next
      case orientr
      from orientr' [OF this] show ?thesis using * by blast
    next
      case delete
      from delete' [OF this] show ?thesis using * by blast
    next
      case compose
      from compose' [OF this] and *
      have "(s, t) \<in> E \<union> R \<or> (s, t) \<in> rstep R O rstep R" by auto
      then show ?thesis
      proof
        assume "(s, t) \<in> rstep R O rstep R"
        then obtain u where "(s, u) \<in> rstep R" and "(u, t) \<in> rstep R" by auto
        then have "(s, u) \<in> ?R" and "(u, t) \<in> ?R" by auto
        then show ?thesis by simp
      qed blast
    next
      case simplifyl
      from simplifyl' [OF this] and *
      have "(s, t) \<in> E \<union> R \<or> (s, t) \<in> (rstep R)\<inverse> O rstep E \<or> (s, t) \<in> rstep E O rstep R" by auto
      then show ?thesis
      proof (elim disjE)
        assume "(s, t) \<in> (rstep R)\<inverse> O rstep E"
        then obtain u where "(s, u) \<in> (rstep R)\<inverse>" and "(u, t) \<in> rstep E" by auto
        then have "(s, u) \<in> ?R" and "(u, t) \<in> ?R" by auto
        then show ?thesis by simp
      next
        assume "(s, t) \<in> rstep E O rstep R"
        then obtain u where "(s, u) \<in> rstep E" and "(u, t) \<in> rstep R" by auto
        then have "(s, u) \<in> ?R" and "(u, t) \<in> ?R" by auto
        then show ?thesis by simp
      qed blast
    next
      case simplifyr
      from simplifyr' [OF this] and *
      have "(s, t) \<in> E \<union> R \<or> (s, t) \<in> (rstep R)\<inverse> O rstep E \<or> (s, t) \<in> rstep E O rstep R" by auto
      then show ?thesis
      proof (elim disjE)
        assume "(s, t) \<in> (rstep R)\<inverse> O rstep E"
        then obtain u where "(s, u) \<in> (rstep R)\<inverse>" and "(u, t) \<in> rstep E" by auto
        then have "(s, u) \<in> ?R" and "(u, t) \<in> ?R" by auto
        then show ?thesis by simp
      next
        assume "(s, t) \<in> rstep E O rstep R"
        then obtain u where "(s, u) \<in> rstep E" and "(u, t) \<in> rstep R" by auto
        then have "(s, u) \<in> ?R" and "(u, t) \<in> ?R" by auto
        then show ?thesis by simp
      qed blast
    next
      case collapse
      from collapse' [OF this] and *
      have "(s, t) \<in> E \<union> R \<or> (s, t) \<in> (rstep R)\<inverse> O rstep R" by auto
      then show ?thesis
      proof
        assume "(s, t) \<in> (rstep R)\<inverse> O rstep R"
        then obtain u where "(s, u) \<in> (rstep R)\<inverse>" and "(u, t) \<in> rstep R" by auto
        then have "(s, u) \<in> ?R" and "(u, t) \<in> ?R" by auto
        then show ?thesis by auto
      qed blast
    qed
  qed
  from rstep_mono [OF this] show ?thesis by (simp add: rstep_simps)
qed

lemma step_subset:
  "(rstep R')\<^sup>= O (rstep (E' \<union> R'))\<^sup>= O ((rstep R')\<inverse>)\<^sup>= \<subseteq> ((rstep (E' \<union> R'))\<^sup>\<leftrightarrow>)\<^sup>*"
  (is "?L \<subseteq> ?R")
proof
  fix s t assume "(s, t) \<in> ?L"
  then obtain u and v where "(s, u) \<in> (rstep R')\<^sup>="
    and "(u, v) \<in> (rstep (E' \<union> R'))\<^sup>="
    and "(v, t) \<in> ((rstep R')\<inverse>)\<^sup>=" by auto
  then have "(s, u) \<in> ?R" and "(u, v) \<in> ?R" and "(v, t) \<in> ?R" by auto
  then show "(s, t) \<in> ?R" by auto
qed

lemma KB_conversion:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')"
  shows "(rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*" (is "?L = ?R")
proof
  note * = subset_trans [OF KB_subset [OF assms] step_subset]
  with converse_mono [THEN iffD2, OF *]
  have "(rstep (E \<union> R))\<^sup>\<leftrightarrow> \<subseteq> ?R"
    unfolding conversion_def
    unfolding rtrancl_converse [symmetric]
    unfolding symcl_converse by blast
  from rtrancl_mono [OF this] show "?L \<subseteq> ?R"
    unfolding conversion_def and rtrancl_idemp .
next
  note * = KB_subset' [OF assms]
  with converse_mono [THEN iffD2, OF *]
  have "(rstep (E' \<union> R'))\<^sup>\<leftrightarrow> \<subseteq> ?L"
    unfolding conversion_def
    unfolding rtrancl_converse [symmetric]
    unfolding symcl_converse by blast
  from rtrancl_mono [OF this] show "?R \<subseteq> ?L"
    unfolding conversion_def and rtrancl_idemp .
qed

lemma KB_rtrancl_conversion:
  assumes "KB\<^sup>*\<^sup>* (E, R) (E', R')"
  shows "(rstep (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
  by (induct "(E, R)" "(E', R')" arbitrary: E' R')
    (force dest: KB_conversion)+

lemma KB_rtrancl_rules_subset_less:
  assumes "KB\<^sup>*\<^sup>* (E, R) (E', R')" and "R \<subseteq> {\<succ>}"
  shows "R' \<subseteq> {\<succ>}"
  using assms
proof (induction "(E, R)" "(E', R')" arbitrary: E' R')
  case (rtrancl_into_rtrancl ER'')
  moreover then obtain E'' and R''
    where [simp]: "ER'' = (E'', R'')" by force
  ultimately have "(E'', R'') \<turnstile>\<^sub>K\<^sub>B (E', R')" and "R'' \<subseteq> {\<succ>}" by simp+
  moreover
  {
    fix s t u
    assume "(t, u) \<in> rstep (R'' - {(s, t)})" and "(s, t) \<in> R''" and "R'' \<subseteq> {\<succ>}"
    then have "s \<succ> u" by (induct t u) (blast intro: subst ctxt dest: trans)
  }
  ultimately show ?case by (cases) auto
qed

definition mstep :: "('a, 'b) term multiset \<Rightarrow> ('a, 'b) trs \<Rightarrow> ('a, 'b) term rel"
  where
    "mstep M R = {(s, t). (s, t) \<in> rstep R \<and> (\<exists>s' t'. s' \<in># M \<and> t' \<in># M \<and> s' \<succeq> s \<and> t' \<succeq> t)}"

lemma mstep_iff:
  "(x, y) \<in> mstep M R \<longleftrightarrow> (x, y) \<in> rstep R \<and> (\<exists>s' t'. s' \<in># M \<and> t' \<in># M \<and> s' \<succeq> x \<and> t' \<succeq> y)"
  by (auto simp: mstep_def)

lemma UN_mstep:
  "(\<Union>x\<in>R. mstep M {x}) = mstep M R"
  by (auto simp add: mstep_iff) blast+

lemma mstep_Un [simp]:
  "mstep M (R \<union> R') = mstep M R \<union> mstep M R'"
  by (auto iff: mstep_iff)

lemma mstep_mono [simp]:
  "R \<subseteq> R' \<Longrightarrow> mstep M R \<subseteq> mstep M R'"
  unfolding mstep_def by fast

lemma step_subset':
  "(mstep M R')\<^sup>= O (mstep M (E' \<union> R'))\<^sup>= O ((mstep M R')\<inverse>)\<^sup>= \<subseteq> ((mstep M (E' \<union> R'))\<^sup>\<leftrightarrow>)\<^sup>*"
  (is "?L \<subseteq> ?R")
proof
  fix s t assume "(s, t) \<in> ?L"
  then obtain u and v where "(s, u) \<in> (mstep M R')\<^sup>="
    and "(u, v) \<in> (mstep M (E' \<union> R'))\<^sup>="
    and "(v, t) \<in> ((mstep M R')\<inverse>)\<^sup>=" by auto
  then have "(s, u) \<in> ?R" and "(u, v) \<in> ?R" and "(v, t) \<in> ?R" by auto
  then show "(s, t) \<in> ?R" by auto
qed

lemma mstep_converse:"(mstep M R)\<^sup>\<leftrightarrow> = mstep M (R\<^sup>\<leftrightarrow>)"
  unfolding mstep_def by auto

lemma rstep_subset_less:
  assumes "R \<subseteq> {(x, y). x \<succ> y}"
  shows "rstep R \<subseteq> {(x, y). x \<succ> y}"
proof
  fix x y assume "(x, y) \<in> rstep R" then show "(x, y) \<in> {(x, y). x \<succ> y}"
    using assms by (induct) (auto intro: subst ctxt)
qed

lemma rsteps_subset_less:
  assumes "R \<subseteq> {(x, y). x \<succ> y}"
  shows "(rstep R)\<^sup>+ \<subseteq> {(x, y). x \<succ> y}"
proof
  fix s t
  assume "(s, t) \<in> (rstep R)\<^sup>+"
  then show "(s, t) \<in> {(x, y). x \<succ> y}"
  proof (induct)
    case (base u)
    with rstep_subset_less [OF assms] show ?case by auto
  next
    case (step t u)
    then show ?case
      using rstep_subset_less [OF assms]
      by auto (metis in_mono mem_Collect_eq split_conv trans)
  qed
qed

lemma mstep_subset:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')" and "R' \<subseteq> {(x, y). x \<succ> y}"
  shows "mstep M (E \<union> R) \<subseteq> (mstep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
proof
  fix s t
  assume "(s, t) \<in> mstep M (E \<union> R)"
  then obtain s' and t' where "s' \<in># M" and "t' \<in># M"
    and "s' \<succeq> s" and "t' \<succeq> t" and "(s, t) \<in> rstep (E \<union> R)"
    by (auto simp: mstep_def)
  with KB_subset [OF assms(1)] obtain u and v
    where "(s, u) \<in> (rstep R')\<^sup>=" and "(u, v) \<in> (rstep (E' \<union> R'))\<^sup>="
      and "(v, t) \<in> ((rstep R')\<inverse>)\<^sup>=" by blast
  moreover then have "(t, v) \<in> (rstep R')\<^sup>=" by auto
  ultimately have "s \<succeq> u" and "t \<succeq> v" using rstep_subset_less [OF assms(2)] by auto
  with \<open>s' \<succeq> s\<close> and \<open>t' \<succeq> t\<close> have "s' \<succeq> u" and "t' \<succeq> v" using trans by blast+
  then have "(s, u) \<in> (mstep M R')\<^sup>="
    and "(u, v) \<in> (mstep M (E' \<union> R'))\<^sup>="
    and "(v, t) \<in> ((mstep M R')\<inverse>)\<^sup>="
    using \<open>s' \<in># M\<close> and \<open>t' \<in># M\<close>
      and \<open>s' \<succeq> s\<close> and \<open>t' \<succeq> t\<close>
      and \<open>(s, u) \<in> (rstep R')\<^sup>=\<close>
      and \<open>(u, v) \<in> (rstep (E' \<union> R'))\<^sup>=\<close>
      and \<open>(v, t) \<in> ((rstep R')\<inverse>)\<^sup>=\<close>
    unfolding mstep_def by (blast)+
  then have "(s, t) \<in> (mstep M R')\<^sup>= O ((mstep M (E' \<union> R')))\<^sup>= O ((mstep M R')\<inverse>)\<^sup>=" by blast
  with step_subset' [of M R' E'] show "(s, t) \<in> (mstep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def by blast
qed

lemma mstep_subset':
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')" and "R' \<subseteq> {(x, y). x \<succ> y}"
  shows "(mstep M (E \<union> R))\<inverse> \<subseteq> (mstep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using converse_mono [THEN iffD2, OF mstep_subset [OF assms, of M]]
  by simp

lemma mstep_symcl_subset:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')" and "R' \<subseteq> {(x, y). x \<succ> y}"
  shows "(mstep M (E \<union> R))\<^sup>\<leftrightarrow> \<subseteq> (mstep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using mstep_subset [OF assms] and mstep_subset' [OF assms] by blast

lemma msteps_subset:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')" and "R' \<subseteq> {(x, y). x \<succ> y}"
  shows "(mstep M (E \<union> R))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (mstep M (E' \<union> R'))\<^sup>\<leftrightarrow>\<^sup>*"
  using mstep_symcl_subset [OF assms, THEN rtrancl_mono] by (simp add: conversion_def)

lemma UNIV_mstep_rstep_iff [simp]:
  "(\<Union>M\<in>UNIV. mstep M R) = rstep R"
proof -
  have *: "\<And>s t. (s, t) \<in> rstep R \<Longrightarrow>
    s \<in># {#s, t#} \<and> t \<in># {#s, t#} \<and> s \<succeq> s \<and> t \<succeq> t \<and>
  (s, t) \<in> mstep {#s, t#} R" by (auto iff: mstep_iff)
  show ?thesis by (auto iff: mstep_iff) (insert *, blast)
qed

lemma rstep_imp_mstep:
  assumes "(t, u) \<in> rstep R" and "s \<in># M" and "s \<succeq> t" and "t \<succ> u"
  shows "(t, u) \<in> mstep M R"
  using assms by (auto simp: mstep_iff dest: trans)

lemma rsteps_imp_msteps:
  assumes "t \<in># M" and "(t, u) \<in> (rstep R)\<^sup>*" and "R \<subseteq> {(x, y). x \<succ> y}"
  shows "(t, u) \<in> (mstep M R)\<^sup>*"
  using assms(2, 1)
proof (induct)
  case base show ?case by simp
next
  note less = rstep_subset_less [OF assms(3)]
  case (step u v)
  have "(u, v) \<in> rstep R" by fact
  moreover have "t \<in># M" by fact
  moreover
  from \<open>(t, u) \<in> (rstep R)\<^sup>*\<close> and less
  have "t \<succeq> u" by (induct) (auto dest: trans)
  moreover have "u \<succ> v" using less and step by blast
  ultimately have "(u, v) \<in> mstep M R" by (rule rstep_imp_mstep)
  with step show ?case by auto
qed

lemma mstep_conv_imp_rstep_conv:"(mstep M R)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule conversion_mono, insert mstep_iff, auto)

subsection \<open>Finite runs\<close>

lemma finite_runD:
  assumes "R 0 = {}" and "E n = {}"
    and run: "\<forall>i<n. (E i, R i) \<turnstile>\<^sub>K\<^sub>B (E (Suc i), R (Suc i))"
  shows finite_run_imp_conversion_eq: "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>*"
    and finite_run_imp_SN: "SN (rstep (R n))"
    and finite_run_imp_R_less: "\<And>i. i \<le> n \<Longrightarrow> R i \<subseteq> {(x, y). x \<succ> y}"
proof -
  have *: "\<And>i. i \<le> n \<Longrightarrow> KB\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)"
  proof -
    fix i assume "i \<le> n"
    with run show "KB\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)"
      by (induct i) (auto, metis (opaque_lifting, no_types) Suc_le_eq rtranclp.rtrancl_into_rtrancl)
  qed
  from * [THEN KB_rtrancl_rules_subset_less] and \<open>R 0 = {}\<close>
  show "\<And>i. i \<le> n \<Longrightarrow> R i \<subseteq> {(x, y). x \<succ> y}" by auto
  with rstep_subset_less [of "R n"]
  show "SN (rstep (R n))" using SN_less by (simp add: assms) (metis SN_subset)
  from KB_rtrancl_conversion [OF * [of n]]
  show "(rstep (E 0))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (R n))\<^sup>\<leftrightarrow>\<^sup>*" by (simp add: assms)
qed

end


subsection \<open>Infinite runs\<close>

context kb
begin

lemma KB_E_subset:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')"
  shows "E \<subseteq> E' \<union> (rstep R' O E') \<union> (E' O (rstep R')\<inverse>) \<union> R'\<^sup>\<leftrightarrow> \<union> Id"
  using assms by (cases) blast+

lemma KB_R_subset:
  assumes "(E, R) \<turnstile>\<^sub>K\<^sub>B (E', R')"
  shows "R \<subseteq> R' \<union> rstep_enc R' O E' \<union> R' O (rstep R')\<inverse>"
proof -
  { fix s t u
    assume "R' = R - {(s, t)} \<union> {(s, u)}" and "(t, u) \<in> rstep (R - {(s, t)})" and "(s, t) \<in> R"
    then have "(s, u) \<in> R'" and "(t, u) \<in> rstep R'" by auto
    then have "(s, t) \<in> R' O (rstep R')\<inverse>" by blast }
  with assms show ?thesis by (cases) blast+
qed

text \<open>Source labeling of rewrite steps.\<close>
abbreviation "slab S \<equiv> source_step (rstep S)"

lemma slab_conv_below_ctxt_subst:
  assumes "(s, t) \<in> (\<Union>v\<in>{v. u \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> (\<Union>v\<in>{v. C\<langle>u \<cdot> \<sigma>\<rangle> \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
  unfolding conversion_def
proof (induct)
  case (step y z)
  then have "(C\<langle>y \<cdot> \<sigma>\<rangle>, C\<langle>z \<cdot> \<sigma>\<rangle>) \<in> (\<Union>v\<in>{v. C\<langle>u \<cdot> \<sigma>\<rangle> \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>"
    by (blast intro: ctxt subst)
  with step show ?case by (blast intro: rtrancl_into_rtrancl)
qed blast

lemma rsteps_slabI:
  assumes "(s, t) \<in> (rstep S)\<^sup>*" "w \<succeq> s" and "rstep S \<subseteq> {\<succ>}"
  shows "w \<succeq> t \<and> (s, t) \<in> (\<Union>v\<in>{v. w \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
proof (induct)
  case (step t u)
  from step(3, 4, 5) have "w \<succeq> t" and "(s, t) \<in> (\<Union>v\<in>{v. w \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*" by (blast)+
  moreover with step(2, 5) have "t \<succ> u" and "(t, u) \<in> (\<Union>v\<in>{v. w \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*" by auto
  ultimately show ?case by (blast intro: trans rtrancl_trans)
qed simp

lemma slab_conv_below_label:
  assumes "(s, t) \<in> (\<Union>v\<in>{v. u \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*" and "w \<succeq> u"
  shows "(s, t) \<in> (\<Union>v\<in>{v. w \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms unfolding conversion_def
proof (induct)
  case (step t v)
  from step(2, 4) have "(t, v) \<in> (\<Union>v\<in>{v. w \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>" by (blast dest: trans)
  with step(3) [OF step(4)] show ?case by (blast intro: rtrancl_into_rtrancl)
qed simp

lemma slab_conv_less_label:
  assumes "(s, t) \<in> (\<Union>v\<in>{v. u \<succeq> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*" and "w \<succ> u"
  shows "(s, t) \<in> (\<Union>v\<in>{v. w \<succ> v}. slab S v)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms unfolding conversion_def
proof (induct)
  case (step t v)
  from step(2, 4) have "(t, v) \<in> (\<Union>v\<in>{v. w \<succ> v}. slab S v)\<^sup>\<leftrightarrow>" by (blast dest: trans)
  with step(3) [OF step(4)] show ?case by (blast intro: rtrancl_into_rtrancl)
qed simp

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

end

locale kb_irun = kb +
  fixes R E
  assumes R0: "R 0 = {}" and enc: enc
    and irun: "\<And>i. (E i, R i) \<turnstile>\<^sub>K\<^sub>B (E (Suc i), R (Suc i))"
begin

lemma rstep_encE [elim]:
  assumes "(s, t) \<in> rstep_enc S"
  obtains C and \<sigma> and l and r where "(l, r) \<in> S" and "s \<cdot>\<rhd> l"
    and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  using assms by (auto simp: rstep_enc_def) (insert enc, auto elim: rstep_rule.cases)

lemma rstep_encI [intro]:
  assumes "s \<cdot>\<rhd> l" and "(l, r) \<in> S" and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  shows "(s, t) \<in> rstep_enc S"
  using assms by (auto simp: rstep_enc_def)

lemma rstep_E_R_Suc_conversion:
  "(rstep (E i \<union> R i))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (E (Suc i) \<union> R (Suc i)))\<^sup>\<leftrightarrow>\<^sup>*"
  using KB_conversion [OF irun [of i]] by blast

abbreviation Rinf ("R\<^sub>\<infinity>") where "R\<^sub>\<infinity> \<equiv> (\<Union>i. R i)"
abbreviation Einf ("E\<^sub>\<infinity>") where "E\<^sub>\<infinity> \<equiv> (\<Union>i. E i)"

definition "R\<^sub>\<omega> = (\<Union>i. \<Inter>j\<in>{j. j\<ge>i}. R j)"
definition "E\<^sub>\<omega> = (\<Union>i. \<Inter>j\<in>{j. j\<ge>i}. E j)"

lemma R_per_subset_R_inf: "R\<^sub>\<omega> \<subseteq> R\<^sub>\<infinity>"
  by (auto simp: R\<^sub>\<omega>_def)

lemma E_per_subset_E_inf: "E\<^sub>\<omega> \<subseteq> E\<^sub>\<infinity>"
  by (auto simp: E\<^sub>\<omega>_def)

lemma rstep_R_per_subset_rstep_R_inf: "rstep R\<^sub>\<omega> \<subseteq> rstep R\<^sub>\<infinity>"
  using R_per_subset_R_inf and rstep_mono by blast

lemma run_R_less: "R i \<subseteq> {\<succ>}"
proof -
  { fix i
    have "KB\<^sup>*\<^sup>* (E 0, R 0) (E i, R i)"
      using irun by (induct i) (auto intro: rtranclp.rtrancl_into_rtrancl) }
  from KB_rtrancl_rules_subset_less [OF this] and R0
  show ?thesis by auto
qed

lemma rstep_R_inf_less: "rstep R\<^sub>\<infinity> \<subseteq> {\<succ>}"
  using run_R_less by (auto elim!: rstepE intro: ctxt subst)

lemma SN_rstep_R_per:
  "SN (rstep R\<^sub>\<omega>)"
  by (rule ccontr)
    (insert SN_less rstep_R_per_subset_rstep_R_inf rstep_R_inf_less, auto simp: SN_defs)

lemma R_per_varcond:
  "\<forall>(l, r) \<in> R\<^sub>\<omega>. vars_term r \<subseteq> vars_term l"
  using SN_rstep_R_per by (rule SN_imp_variable_condition)

lemma rstep_R_per_less: "rstep R\<^sub>\<omega> \<subseteq> {\<succ>}"
proof
  fix s t assume "(s, t) \<in> rstep R\<^sub>\<omega>"
  then obtain C \<sigma> l r where "(l, r) \<in> R\<^sub>\<omega>" and [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
  then obtain i where "(l, r) \<in> R i" by (auto simp: R\<^sub>\<omega>_def)
  then show "(s, t) \<in> {\<succ>}" using run_R_less [of i] by (auto simp: ctxt subst)
qed

abbreviation "termless \<equiv> (relto ({\<cdot>\<rhd>} \<union> {\<succ>}) {\<cdot>\<unrhd>})\<^sup>+"

abbreviation "lexless \<equiv> lex_two termless Id termless"

abbreviation "mulless \<equiv> s_mul_ext Id {\<succ>}"

sublocale mlessop: SN_order_pair mulless "ns_mul_ext Id {\<succ>}"
proof (intro SN_order_pair.mul_ext_SN_order_pair)
  show "SN_order_pair {\<succ>} Id"
    by (standard) (auto simp: refl_on_def trans_def SN_less dest: trans)
qed

context
  assumes nonfail: "E\<^sub>\<omega> = {}"
begin

lemma E_i_subset_join_R_inf:
  "E i \<subseteq> (rstep R\<^sub>\<infinity>)\<^sup>\<down>" (is "_ \<subseteq> ?R\<^sup>\<down>")
proof
  fix s t assume "(s, t) \<in> E i"
  then show "(s, t) \<in> ?R\<^sup>\<down>"
  proof (induct "{#s, t#}" arbitrary: s t i rule: SN_induct [OF mlessop.SN])
    case less: 1
    note IH = this(1)

    from nonfail have "\<exists>j>i. (s, t) \<notin> E j" using Suc_le_eq unfolding E\<^sub>\<omega>_def by blast
    moreover define j where "j = (LEAST j. j > i \<and> (s, t) \<notin> E j)"
    ultimately have "j > i" and not_j: "(s, t) \<notin> E j" by (metis (lifting) LeastI)+
    then have "j - 1 < j" and [simp]: "Suc (j - Suc 0) = j" by auto
    from not_less_Least [OF this(1) [unfolded j_def], folded j_def] and \<open>(s, t) \<in> E i\<close> and \<open>j > i\<close>
    have "(s, t) \<in> E (j - 1)" by (cases "j = Suc i") auto
    with KB_E_subset [OF irun [of "j - 1"]] and not_j
    consider "(s, t) \<in> ((R j)\<^sup>\<leftrightarrow>)\<^sup>=" | "(s, t) \<in> rstep (R j) O E j" | "(s, t) \<in> E j O (rstep (R j))\<inverse>"
      by auto blast
    then show ?case
    proof (cases)
      case 2
      then obtain u where su: "(s, u) \<in> rstep (R j)" and ut: "(u, t) \<in> E j" by blast
      then have "s \<succ> u" using run_R_less [of j] by (blast intro: ctxt subst)
      then have "({#s, t#}, {#u, t#}) \<in> mulless"
        by (intro s_mul_ext_IdI [of "{#s#}" _ "{#t#}" _ "{#u#}"]) simp_all
      from IH [OF this ut] have "(u, t) \<in> ?R\<^sup>\<down>" by blast
      moreover have "(s, u) \<in> ?R\<^sup>*" using su by blast
      ultimately show ?thesis by (blast intro: rtrancl_join_join)
    next
      case 3
      then obtain u where su: "(s, u) \<in> E j" and tu: "(t, u) \<in> rstep (R j)" by blast
      then have "t \<succ> u" using run_R_less [of j] by (blast intro: ctxt subst)
      then have "({#s, t#}, {#s, u#}) \<in> mulless"
        by (intro s_mul_ext_IdI [of "{#t#}" _ "{#s#}" _ "{#u#}"]) simp_all
      from IH [OF this su] have "(s, u) \<in> ?R\<^sup>\<down>" by blast
      moreover have "(t, u) \<in> ?R\<^sup>*" using tu by blast
      ultimately show ?thesis by (blast intro: join_rtrancl_join)
    qed blast
  qed
qed

lemma rstep_E_i_subset:
  "rstep (E i) \<subseteq> (rstep R\<^sub>\<infinity>)\<^sup>\<down>" (is "?E \<subseteq> ?R\<^sup>\<down>")
proof
  fix s t assume "(s, t) \<in> ?E"
  then obtain C \<sigma> l r where "(l, r) \<in> E i" and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
  moreover with E_i_subset_join_R_inf [of i] have "(l, r) \<in> ?R\<^sup>\<down>" by blast
  ultimately show "(s, t) \<in> ?R\<^sup>\<down>" by auto
qed

lemma SN_lexless: "SN lexless"
  by (intro lex_two)
    (auto simp only: SN_trancl_SN_conv intro: SN_encomp_Un_less_relto_encompeq)

lemma source_step_R_inf_subset:
  "source_step R\<^sub>\<infinity> l \<subseteq> (\<Union>t\<in>{t. l \<succeq> t}. slab R\<^sub>\<omega> t)\<^sup>\<leftrightarrow>\<^sup>*" (is "source_step ?R l \<subseteq> ?L l")
proof
  fix t u assume "(t, u) \<in> source_step R\<^sub>\<infinity> l"
  then obtain r where "(l, r) \<in> ?R" and [simp]: "t = l" "u = r" by blast
  have "(l, r) \<in> ?L l" using \<open>(l, r) \<in> ?R\<close>
  proof (induct "(l, r)" arbitrary: l r rule: SN_induct [OF SN_lexless])
    case less: 1
    note IH = this(1)
    have lr: "(l, r) \<in> ?R" using less by blast
    show ?case
    proof (cases "(l, r) \<in> R\<^sub>\<omega>")
      case False
      with lr obtain j where "(l, r) \<in> R j" and "\<exists>i>j. (l, r) \<notin> R i"
        by (force simp: R\<^sub>\<omega>_def le_eq_less_or_eq)
      moreover define i where "i = (LEAST i. i > j \<and> (l, r) \<notin> R i)"
      ultimately have "i > j" and not_i: "(l, r) \<notin> R i" by (metis (lifting) LeastI)+
      then have "i - 1 < i" and [simp]: "Suc (i - Suc 0) = i" by auto
      from not_less_Least [OF this(1) [unfolded i_def], folded i_def] and \<open>i > j\<close> and \<open>(l, r) \<in> R j\<close>
      have "(l, r) \<in> R (i - 1)" by (cases "i = Suc j") auto
      with KB_R_subset [OF irun [of "i - 1"]] and not_i
      consider "(l, r) \<in> rstep_enc (R i) O E i" | "(l, r) \<in> R i O (rstep (R i))\<inverse>" by force
      then show ?thesis
      proof (cases)
        case 1
        then obtain u where lu: "(l, u) \<in> rstep_enc (R i)" and "(u, r) \<in> E i" by blast
        with E_i_subset_join_R_inf have "(u, r) \<in> (rstep ?R)\<^sup>\<down>" by blast
        then obtain v where uv: "(u, v) \<in> (rstep ?R)\<^sup>*" and rv: "(r, v) \<in> (rstep ?R)\<^sup>*" by blast
        have "(l, r) \<in> (rstep ?R)\<^sup>+" using lr by auto
        from trancl_mono [OF this rstep_R_inf_less] have "l \<succ> r" by simp
        with rv have rv_L: "(r, v) \<in> ?L l"
        proof (induct)
          case (step x y)
          with rtrancl_mono [OF rstep_R_inf_less] have "l \<succ> x" by (auto dest: trans)
          from step have "(r, x) \<in> ?L l" by blast
          moreover have "(x, y) \<in> ?L l"
          proof -
            obtain C \<sigma> l' r' where *: "(l', r') \<in> ?R" and x: "x = C\<langle>l' \<cdot> \<sigma>\<rangle>" and y: "y = C\<langle>r' \<cdot> \<sigma>\<rangle>"
              using step(2) by fast
            then have "x \<cdot>\<unrhd> l'" by auto
            then have "(l, l') \<in> termless" using \<open>l \<succ> x\<close> by blast
            then have "((l, r), (l', r')) \<in> lexless" by auto
            from IH [OF this *] have "(l', r') \<in> ?L l'" .
            then have "(x, y) \<in> ?L x"
              unfolding x y conversion_def [symmetric] by (rule slab_conv_below_ctxt_subst)
            with slab_conv_below_label [OF \<open>(x, y) \<in> ?L x\<close>, of l] and \<open>l \<succ> x\<close> show ?thesis by simp
          qed
          ultimately show ?case by (auto simp: conversion_def)
        qed simp
        from uv have "(l, v) \<in> ?L l"
        proof (induct)
          case base
          from lu obtain l' r' where *: "(l', r') \<in> ?R" and lu': "(l, u) \<in> rstep_enc {(l', r')}" by fast
          then have "((l, r), (l', r')) \<in> lexless" by auto
          from IH [OF this *] have "(l', r') \<in> ?L l'" .
          moreover obtain C \<sigma> where "l = C\<langle>l' \<cdot> \<sigma>\<rangle>" and "u = C\<langle>r' \<cdot> \<sigma>\<rangle>" using lu' by blast
          ultimately show ?case
            using slab_conv_below_ctxt_subst [of l' r' R\<^sub>\<omega> l' C \<sigma>] by simp
        next
          case (step x w)
          then obtain l' r' where *: "(l', r') \<in> ?R"
            and "(u, x) \<in> (rstep ?R)\<^sup>*" and xw: "(x, w) \<in> rstep {(l', r')}" by blast
          moreover have "(l, u) \<in> (rstep ?R)\<^sup>+" using lu by (blast)
          ultimately have "(l, x) \<in> (rstep ?R)\<^sup>+" by auto
          then have "l \<succ> x" using trancl_mono_set [OF rstep_R_inf_less] by auto
          moreover with xw have "x \<cdot>\<unrhd> l'" by blast
          ultimately have "(l, l') \<in> termless" by blast
          then have "((l, r), (l', r')) \<in> lexless" by auto
          from IH [OF this *] have "(l', r') \<in> ?L l'" .
          moreover obtain C \<sigma> where "x = C\<langle>l' \<cdot> \<sigma>\<rangle>" and "w = C\<langle>r' \<cdot> \<sigma>\<rangle>" using xw by blast
          ultimately have "(x, w) \<in> ?L x" using slab_conv_below_ctxt_subst [of l' r' R\<^sub>\<omega> l' C \<sigma>] by simp
          moreover have "l \<succeq> x" using \<open>l \<succ> x\<close> by simp
          ultimately have "(x, w) \<in> ?L l" by (metis slab_conv_below_label)
          moreover have "(l, x) \<in> ?L l" using step by blast
          ultimately show ?case by (auto simp: conversion_def)
        qed
        moreover have "(v, r) \<in> ?L l" using rv_L by (simp add: conversion_inv)
        ultimately show ?thesis unfolding conversion_def by (blast dest: rtrancl_trans)
      next
        case 2
        then obtain u l' r' where l'r': "(l', r') \<in> R i"
          and lv: "(l, u) \<in> R i" and rv: "(r, u) \<in> rstep {(l', r')}" by blast
        then have "r \<succ> u" and "r \<cdot>\<unrhd> l'" and "l \<succ> r" using \<open>(l, r) \<in> R (i - 1)\<close>
          using run_R_less [THEN compatible_rstep_imp_less, of r u i] and run_R_less by auto
        then have "(r, u) \<in> termless" and "(l, l') \<in> termless" by blast+
        then have "((l, r), (l, u)) \<in> lexless" and "((l, r), (l', r')) \<in> lexless" by auto
        with IH and l'r' and lv have "(l, u) \<in> ?L l" and "(l', r') \<in> ?L l'" by blast+
        moreover obtain C and \<sigma> where "r = C\<langle>l' \<cdot> \<sigma>\<rangle>" and "u = C\<langle>r' \<cdot> \<sigma>\<rangle>" using rv by blast
        ultimately have "(r, u) \<in> ?L r"
          using slab_conv_below_ctxt_subst by auto
        with \<open>l \<succ> r\<close> have "(r, u) \<in> ?L l" using slab_conv_below_label by blast
        then have "(u, r) \<in> ?L l" by (auto simp: conversion_inv)
        with \<open>(l, u) \<in> ?L l\<close> show ?thesis unfolding conversion_def by (blast dest: rtrancl_trans)
      qed
    qed blast
  qed
  then show "(t, u) \<in> ?L l" by simp
qed

lemma slab_R_inf_subset:
  "slab R\<^sub>\<infinity> s \<subseteq> (\<Union>t\<in>{t. s \<succeq> t}. slab R\<^sub>\<omega> t)\<^sup>\<leftrightarrow>\<^sup>*" (is "slab ?R s \<subseteq> ?L s")
proof
  fix t u assume "(t, u) \<in> slab ?R s"
  then obtain C \<sigma> l r where "(l, r) \<in> ?R"
    and [simp]: "s = t" "t = C\<langle>l \<cdot> \<sigma>\<rangle>" "u = C\<langle>r \<cdot> \<sigma>\<rangle>" by fast
  with source_step_R_inf_subset [of l]
  have "(l, r) \<in> ?L l" by blast
  from slab_conv_below_ctxt_subst [OF this] show "(t, u) \<in> ?L s" by simp
qed

lemma slab_R_inf_conv:
  assumes "(t, u) \<in> (\<Union>a\<in>{a. s \<succeq> a}. slab R\<^sub>\<infinity> a)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(t, u) \<in> (\<Union>a\<in>{a. s \<succeq> a}. slab R\<^sub>\<omega> a)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms
  unfolding conversion_def
proof (induct)
  case (step u v)
  from step(2) obtain a where "s \<succeq> a" and "(u, v) \<in> (slab R\<^sub>\<infinity> a)\<^sup>\<leftrightarrow>" by blast
  with slab_R_inf_subset [of a]
  have "(u, v) \<in> (\<Union>x\<in>{x. a \<succeq> x}. slab R\<^sub>\<omega> x)\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: conversion_inv)
  with \<open>s \<succeq> a\<close> have "(u, v) \<in> (\<Union>x\<in>{x. s \<succeq> x}. slab R\<^sub>\<omega> x)\<^sup>\<leftrightarrow>\<^sup>*"
    using slab_conv_below_label by blast
  with step(3) show ?case by (auto simp: conversion_def)
qed simp

lemma rstep_R_inf_conv_iff:
  "(rstep R\<^sub>\<infinity>)\<^sup>\<leftrightarrow>\<^sup>* = (rstep R\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*"
proof
  show "(rstep R\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep R\<^sub>\<infinity>)\<^sup>\<leftrightarrow>\<^sup>*"
    using rstep_R_per_subset_rstep_R_inf
    by (intro conversion_mono) auto
  have "(rstep R\<^sub>\<infinity>)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (\<Union>s. slab R\<^sub>\<infinity> s)\<^sup>\<leftrightarrow>\<^sup>*"
    by (intro conversion_mono) auto
  also have "\<dots> \<subseteq> ((\<Union>s. slab R\<^sub>\<omega> s)\<^sup>\<leftrightarrow>\<^sup>*)\<^sup>\<leftrightarrow>\<^sup>*"
    apply (intro conversion_mono)
    apply (auto dest!: slab_R_inf_subset [THEN subsetD])
    apply (rule conversion_mono [THEN subsetD])
     apply auto
    done
  also have "\<dots> \<subseteq> ((rstep R\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*)\<^sup>\<leftrightarrow>\<^sup>*" by (intro conversion_mono) auto
  finally show "(rstep R\<^sub>\<infinity>)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep R\<^sub>\<omega>)\<^sup>\<leftrightarrow>\<^sup>*" by simp
qed

end

end

end
