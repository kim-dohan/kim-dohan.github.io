(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015, 2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Critical Pairs\<close>

theory CP
  imports
    First_Order_Rewriting.Unification_More
    TRS.Renaming_Interpretations
begin

definition overlap ::
    "('f, 'v :: infinite) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) rule \<Rightarrow> pos \<Rightarrow> ('f, 'v) rule \<Rightarrow> bool"
where
  "overlap R R' r p r' \<longleftrightarrow>
    (\<exists>p. p \<bullet> r \<in> R) \<and>
    (\<exists>p. p \<bullet> r' \<in> R') \<and>
    vars_rule r \<inter> vars_rule r' = {} \<and>
    p \<in> fun_poss (fst r') \<and>
    (\<exists>\<sigma> :: ('f, 'v) subst. fst r \<cdot> \<sigma> = (fst r' |_  p) \<cdot> \<sigma>) \<and>
    (p = [] \<longrightarrow> \<not> (\<exists>p. p \<bullet> r = r'))"

lemma overlap_right:
  fixes R\<^sub>1 R\<^sub>2 :: "('f, 'v::infinite) trs"
  assumes "overlap R\<^sub>1 R\<^sub>2 r\<^sub>1 p r\<^sub>2"
  obtains \<pi> where "overlap R\<^sub>1 R\<^sub>2 (\<pi> \<bullet> r\<^sub>1) p (\<pi> \<bullet> r\<^sub>2)" and "(\<pi> \<bullet> r\<^sub>2) \<in> R\<^sub>2"
proof -
  obtain \<pi>\<^sub>1 and \<pi>\<^sub>2
    where "\<pi>\<^sub>1 \<bullet> r\<^sub>1 \<in> R\<^sub>1" and "\<pi>\<^sub>2 \<bullet> r\<^sub>2 \<in> R\<^sub>2"
    and "vars_rule r\<^sub>1 \<inter> vars_rule r\<^sub>2 = {}"
    and "p \<in> fun_poss (fst r\<^sub>2)"
    and "\<exists>\<sigma>::('f, 'v) subst. fst r\<^sub>1 \<cdot> \<sigma> = (fst r\<^sub>2 |_ p) \<cdot> \<sigma>"
    and "p = [] \<longrightarrow> \<not> (\<exists>p. p \<bullet> r\<^sub>1 = r\<^sub>2)"
    using assms unfolding overlap_def by blast
  then have "(\<pi>\<^sub>1 + -\<pi>\<^sub>2) \<bullet> (\<pi>\<^sub>2 \<bullet> r\<^sub>1) \<in> R\<^sub>1" and "0 \<bullet> (\<pi>\<^sub>2 \<bullet> r\<^sub>2) \<in> R\<^sub>2"
    and "vars_rule (\<pi>\<^sub>2 \<bullet> r\<^sub>1) \<inter> vars_rule (\<pi>\<^sub>2 \<bullet> r\<^sub>2) = {}"
    and "p \<in> fun_poss (fst (\<pi>\<^sub>2 \<bullet> r\<^sub>2))"
    and "\<exists>\<sigma>::('f, 'v) subst. fst (\<pi>\<^sub>2 \<bullet> r\<^sub>1) \<cdot> \<sigma> = (fst (\<pi>\<^sub>2 \<bullet> r\<^sub>2) |_ p) \<cdot> \<sigma>"
    and "p = [] \<longrightarrow> \<not> (\<exists>p. p \<bullet> (\<pi>\<^sub>2 \<bullet> r\<^sub>1) = \<pi>\<^sub>2 \<bullet> r\<^sub>2)"
         apply (auto simp: eqvt [symmetric])
      apply (rule_tac x = "sop (-\<pi>\<^sub>2) \<circ>\<^sub>s \<sigma>" in exI)
      apply (simp add: fun_poss_imp_poss subt_at_eqvt)
     apply (rule_tac x = "sop (-\<pi>\<^sub>2) \<circ>\<^sub>s \<sigma>" in exI)
     apply (simp add: fun_poss_imp_poss subt_at_eqvt)
    by (metis rule_pt.permute_minus_cancel(2) rule_pt.permute_plus)
  then show thesis
    apply (intro that [of \<pi>\<^sub>2])
     apply (unfold overlap_def)
     apply blast
    apply auto
    done
qed

text \<open>Critical peaks are single-step rewrite peaks originating from overlaps.\<close>
definition cpeaks2 ::
    "('f, 'v :: infinite) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    (('f, 'v) term \<times> pos \<times> ('f, 'v) term \<times> ('f, 'v) term) set"
where
  "cpeaks2 R R' = {(replace_at (fst r') p (snd r) \<cdot> \<sigma>, p, fst r' \<cdot> \<sigma>, snd r' \<cdot> \<sigma>) |
    r p r' \<sigma>. overlap R R' r p r' \<and> \<sigma> = the_mgu (fst r) (fst r' |_ p)}"

abbreviation "cpeaks R \<equiv> cpeaks2 R R"

lemma cpeaks2_I:
  assumes "overlap R R' r p r'" and "\<sigma> = the_mgu (fst r) (fst r' |_ p)"
  shows "(replace_at (fst r') p (snd r) \<cdot> \<sigma>, p, fst r' \<cdot> \<sigma>, snd r' \<cdot> \<sigma>) \<in> cpeaks2 R R'"
  using assms by (force simp: cpeaks2_def)

inductive_set S3 for A
where
  subst: "(t, p, s, u) \<in> A \<Longrightarrow> (t \<cdot> \<sigma>, p, s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> S3 A"

lemma peak_above_imp_join_or_cpeaks:
  fixes R :: "('f, 'v :: infinite) trs"
    and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "('f, 'v) subst"
  assumes rule_variants: "\<exists>\<pi>. \<pi> \<bullet> (l\<^sub>1, r\<^sub>1) \<in> R" "\<exists>\<pi>. \<pi> \<bullet> (l\<^sub>2, r\<^sub>2) \<in> R"
    and disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}"
    and "p\<^sub>2 \<le>\<^sub>p p\<^sub>1"

    and "vars_term r\<^sub>1 \<subseteq> vars_term l\<^sub>1"
    and p\<^sub>1: "p\<^sub>1 \<in> poss s"
    and sp\<^sub>1: "s |_ p\<^sub>1 = l\<^sub>1 \<cdot> \<sigma>\<^sub>1"
    and t: "t = replace_at s p\<^sub>1 (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)"

    and p\<^sub>2: "p\<^sub>2 \<in> poss s"
    and sp\<^sub>2: "s |_ p\<^sub>2 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
    and u: "u = replace_at s p\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)"

  shows "(t, u) \<in> (rstep R)\<^sup>\<down> \<or>
    (p\<^sub>2 \<in> poss s \<and>
    (ctxt_of_pos_term p\<^sub>2 s)\<langle>t |_ p\<^sub>2\<rangle> = t \<and>
    (ctxt_of_pos_term p\<^sub>2 s)\<langle>u |_ p\<^sub>2\<rangle> = u \<and>
    (t |_ p\<^sub>2, pos_diff p\<^sub>1 p\<^sub>2, s |_ p\<^sub>2, u |_ p\<^sub>2) \<in> S3 (cpeaks R))"
proof -
  define p where "p = pos_diff p\<^sub>1 p\<^sub>2"
  have p\<^sub>1_eq: "p\<^sub>1 = p\<^sub>2 @ p" using \<open>p\<^sub>2 \<le>\<^sub>p p\<^sub>1\<close> by (simp add: p_def)
  then have t: "t = replace_at s p\<^sub>2 (replace_at (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) p (r\<^sub>1 \<cdot> \<sigma>\<^sub>1))"
    by (simp add: t ctxt_of_pos_term_append p\<^sub>2 sp\<^sub>2)
  show ?thesis
  proof (cases "p \<in> fun_poss l\<^sub>2 \<and> (p = [] \<longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> (l\<^sub>1, r\<^sub>1) = (l\<^sub>2, r\<^sub>2)))")
    case True
    define \<sigma>' where "\<sigma>' x = (if x \<in> vars_rule (l\<^sub>1, r\<^sub>1) then \<sigma>\<^sub>1 x else \<sigma>\<^sub>2 x)" for x

    have p: "p \<in> fun_poss l\<^sub>2" and "p = [] \<Longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> (l\<^sub>1, r\<^sub>1) = (l\<^sub>2, r\<^sub>2))" using True by auto
    moreover
    have unif: "l\<^sub>1 \<cdot> \<sigma>' = (l\<^sub>2 |_ p) \<cdot> \<sigma>'"
    proof -
      note coinc = coincidence_lemma' [of l\<^sub>1 "vars_rule (l\<^sub>1, r\<^sub>1)"]
      have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term (l\<^sub>2 |_ p) = {}"
        using vars_term_subt_at [OF fun_poss_imp_poss [OF p]] and disj
        by (auto simp: vars_rule_def)
      have "l\<^sub>1 \<cdot> \<sigma>' = l\<^sub>1 \<cdot> (\<sigma>' |s vars_rule (l\<^sub>1, r\<^sub>1))"
        using coinc by (simp add: vars_rule_def)
      also have "\<dots> = l\<^sub>1 \<cdot> (\<sigma>\<^sub>1 |s vars_rule (l\<^sub>1, r\<^sub>1))" by (simp add: \<sigma>'_def [abs_def])
      also have "\<dots> = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using coinc by (simp add: vars_rule_def)
      also have "\<dots> = (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) |_ p" using subt_at_append [OF p\<^sub>2] and sp\<^sub>1 by (simp add: p\<^sub>1_eq sp\<^sub>2)
      also have "\<dots> = (l\<^sub>2 |_ p) \<cdot> \<sigma>\<^sub>2" using fun_poss_imp_poss [OF p] by simp
      also have "\<dots> = (l\<^sub>2 |_ p) \<cdot> (\<sigma>\<^sub>2 |s vars_term (l\<^sub>2 |_ p))"
        by (simp add: coincidence_lemma [symmetric])
      also have "\<dots> = (l\<^sub>2 |_ p) \<cdot> (\<sigma>' |s vars_term (l\<^sub>2 |_ p))" using disj by (simp add: \<sigma>'_def [abs_def])
      finally show ?thesis by (simp add: coincidence_lemma [symmetric])
    qed
    ultimately
    have overlap: "overlap R R (l\<^sub>1, r\<^sub>1) p (l\<^sub>2, r\<^sub>2)"
      using disj and rule_variants by (auto simp: overlap_def)

    define \<sigma> where "\<sigma> = the_mgu l\<^sub>1 (l\<^sub>2 |_ p)"
    have cpeaks: "(replace_at l\<^sub>2 p r\<^sub>1 \<cdot> \<sigma>, p, l\<^sub>2 \<cdot> \<sigma>, r\<^sub>2 \<cdot> \<sigma>) \<in> cpeaks R"
      using cpeaks2_I [OF overlap refl] by (simp add: \<sigma>_def)

    have "is_mgu \<sigma> {(l\<^sub>1, l\<^sub>2 |_ p)}" by (rule is_mguI) (insert unif the_mgu, auto simp: \<sigma>_def)
    with unif obtain \<tau> where \<sigma>': "\<sigma>' = \<sigma> \<circ>\<^sub>s \<tau>" by (auto simp: is_mgu_def unifiers_def)
    have "(replace_at (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) p (r\<^sub>1 \<cdot> \<sigma>\<^sub>1), p, l\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<sigma>\<^sub>2) \<in> S3 (cpeaks R)"
    proof -
      have "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 = l\<^sub>2 \<cdot> \<sigma>'"
      proof -
        have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term l\<^sub>2 = {}" using disj by (auto simp: vars_rule_def)
        have "l\<^sub>2 \<cdot> \<sigma>' = l\<^sub>2 \<cdot> (\<sigma>' |s vars_term l\<^sub>2)" by (rule coincidence_lemma)
        also have "\<dots> = l\<^sub>2 \<cdot> (\<sigma>\<^sub>2 |s vars_term l\<^sub>2)" using disj by (simp add: \<sigma>'_def [abs_def])
        also have "\<dots> = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" by (simp add: coincidence_lemma [symmetric])
        finally show ?thesis ..
      qed
      moreover
      have "r\<^sub>1 \<cdot> \<sigma>\<^sub>1 = r\<^sub>1 \<cdot> \<sigma>'"
      proof -
        note coinc = coincidence_lemma' [of r\<^sub>1 "vars_rule (l\<^sub>1, r\<^sub>1)"]
        have "r\<^sub>1 \<cdot> \<sigma>' = r\<^sub>1 \<cdot> (\<sigma>' |s vars_rule (l\<^sub>1, r\<^sub>1))"
          using coinc by (simp add: vars_rule_def)
        also have "\<dots> = r\<^sub>1 \<cdot> (\<sigma>\<^sub>1 |s vars_rule (l\<^sub>1, r\<^sub>1))" by (simp add: \<sigma>'_def [abs_def])
        also have "\<dots> = r\<^sub>1 \<cdot> \<sigma>\<^sub>1" using coinc by (simp add: vars_rule_def)
        finally show ?thesis ..
      qed
      moreover
      have "r\<^sub>2 \<cdot> \<sigma>\<^sub>2 = r\<^sub>2 \<cdot> \<sigma>'"
      proof -
        have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_term r\<^sub>2 = {}" using disj by (auto simp: vars_rule_def)
        have "r\<^sub>2 \<cdot> \<sigma>' = r\<^sub>2 \<cdot> (\<sigma>' |s vars_term r\<^sub>2)" by (rule coincidence_lemma)
        also have "\<dots> = r\<^sub>2 \<cdot> (\<sigma>\<^sub>2 |s vars_term r\<^sub>2)" using disj by (simp add: \<sigma>'_def [abs_def])
        also have "\<dots> = r\<^sub>2 \<cdot> \<sigma>\<^sub>2" by (simp add: coincidence_lemma [symmetric])
        finally show ?thesis ..
      qed
      ultimately
      show ?thesis using cpeaks
        using S3.intros [OF cpeaks, of \<tau>]
        and fun_poss_imp_poss [OF p]
        by (simp add: \<sigma>' ctxt_of_pos_term_subst)
    qed
    moreover have "p\<^sub>2 \<in> poss s" by fact
    ultimately show ?thesis using p\<^sub>2 and sp\<^sub>2 by (auto simp: t u p_def replace_at_subt_at)
  next
    case False
    then have "(p = [] \<and> (\<exists>\<pi>. \<pi> \<bullet> (l\<^sub>1, r\<^sub>1) = (l\<^sub>2, r\<^sub>2))) \<or> p \<notin> fun_poss l\<^sub>2" by blast
    then show ?thesis
    proof (elim disjE conjE exE)
      txt \<open>The variable condition is only needed here.\<close>
      fix \<pi>
      assume [simp]: "p = []" and "\<pi> \<bullet> (l\<^sub>1, r\<^sub>1) = (l\<^sub>2, r\<^sub>2)"
      then have "p\<^sub>2 = p\<^sub>1" and "l\<^sub>2 = \<pi> \<bullet> l\<^sub>1" and [simp]: "r\<^sub>2 = \<pi> \<bullet> r\<^sub>1" by (simp_all add: p\<^sub>1_eq eqvt)
      then have "l\<^sub>1 \<cdot> \<sigma>\<^sub>1 = l\<^sub>1 \<cdot> (\<sigma>\<^sub>2 \<circ> Rep_perm \<pi>)"
        using sp\<^sub>1 and sp\<^sub>2 by (simp add: permute_term_subst_apply_term)
      moreover
      have "vars_term r\<^sub>1 \<subseteq> vars_term l\<^sub>1" by fact
      ultimately
      have "r\<^sub>1 \<cdot> \<sigma>\<^sub>1 = r\<^sub>1 \<cdot> (\<sigma>\<^sub>2 \<circ> Rep_perm \<pi>)" using vars_term_subset_subst_eq by blast
      then have "r\<^sub>1 \<cdot> \<sigma>\<^sub>1 = \<pi> \<bullet> r\<^sub>1 \<cdot> \<sigma>\<^sub>2" by (simp add: permute_term_subst_apply_term)
      then show ?thesis by (auto simp: t u)
    next
      txt \<open>Variable overlap.\<close>
      have step1: "(l\<^sub>1, r\<^sub>1) \<in> rstep R" and step2: "(l\<^sub>2, r\<^sub>2) \<in> rstep R"
        using rule_variants by (auto simp: eqvt) (metis rstep_rule rstep_permute_iff)+
      have "p \<in> poss (l\<^sub>2 \<cdot> \<sigma>\<^sub>2)" by (metis p\<^sub>1_eq p\<^sub>1 poss_append_poss sp\<^sub>2)
      moreover
      assume "p \<notin> fun_poss l\<^sub>2"
      ultimately
      obtain q\<^sub>1 q\<^sub>2 x
        where [simp]: "p = q\<^sub>1 @ q\<^sub>2" and q\<^sub>1: "q\<^sub>1 \<in> poss l\<^sub>2"
        and l\<^sub>2q\<^sub>1: "l\<^sub>2 |_ q\<^sub>1 = Var x" and q\<^sub>2: "q\<^sub>2 \<in> poss (\<sigma>\<^sub>2 x)"
        by (rule poss_subst_apply_term)
      moreover
      have [simp]: "l\<^sub>2 \<cdot> \<sigma>\<^sub>2 |_ p = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" by (metis p\<^sub>1_eq p\<^sub>2 sp\<^sub>1 sp\<^sub>2 subt_at_append)
      ultimately
      have [simp]: "\<sigma>\<^sub>2 x |_ q\<^sub>2 = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" by simp

      define \<sigma>\<^sub>2' where "\<sigma>\<^sub>2' y = (if y = x then replace_at (\<sigma>\<^sub>2 x) q\<^sub>2 (r\<^sub>1 \<cdot> \<sigma>\<^sub>1) else \<sigma>\<^sub>2 y)" for y

      have "(\<sigma>\<^sub>2 x, \<sigma>\<^sub>2' x) \<in> rstep R"
      proof -
        let ?C = "ctxt_of_pos_term q\<^sub>2 (\<sigma>\<^sub>2 x)"
        have "(?C\<langle>l\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>, ?C\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>) \<in> rstep R" using step1 by blast
        then show ?thesis using q\<^sub>2 by (simp add: \<sigma>\<^sub>2'_def replace_at_ident)
      qed
      then have *: "\<And>x. (\<sigma>\<^sub>2 x, \<sigma>\<^sub>2' x) \<in> (rstep R)\<^sup>*" by (auto simp: \<sigma>\<^sub>2'_def)
      then have "(r\<^sub>2 \<cdot> \<sigma>\<^sub>2, r\<^sub>2 \<cdot> \<sigma>\<^sub>2') \<in> (rstep R)\<^sup>*" by (rule substs_rsteps)
      then have "(u, replace_at s p\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2')) \<in> (rstep R)\<^sup>*" by (auto simp: u rsteps_closed_ctxt)
      moreover
      have "(t, replace_at s p\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2')) \<in> (rstep R)\<^sup>*"
      proof -
        have "replace_at (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) p (r\<^sub>1 \<cdot> \<sigma>\<^sub>1) = replace_at (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) q\<^sub>1 (\<sigma>\<^sub>2' x)"
          using q\<^sub>1 and q\<^sub>2 by (simp add: \<sigma>\<^sub>2'_def ctxt_of_pos_term_append l\<^sub>2q\<^sub>1)
        moreover
        have "(replace_at (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) q\<^sub>1 (\<sigma>\<^sub>2' x), l\<^sub>2 \<cdot> \<sigma>\<^sub>2') \<in> (rstep R)\<^sup>*"
          by (rule replace_at_subst_rsteps [OF * q\<^sub>1 l\<^sub>2q\<^sub>1])
        moreover
        have "(l\<^sub>2 \<cdot> \<sigma>\<^sub>2', r\<^sub>2 \<cdot> \<sigma>\<^sub>2') \<in> rstep R" using step2 by blast
        ultimately
        have "(replace_at (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) p (r\<^sub>1 \<cdot> \<sigma>\<^sub>1), r\<^sub>2 \<cdot> \<sigma>\<^sub>2') \<in> (rstep R)\<^sup>*" by auto
        then show ?thesis by (auto simp: p\<^sub>2 t rsteps_closed_ctxt)
      qed
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma parallel_peak_imp_join:
  fixes p\<^sub>1 p\<^sub>2 :: "pos"
  assumes parallel: "p\<^sub>1 \<bottom> p\<^sub>2"
    and peak: "(s, t) \<in> rstep_pos R p\<^sub>1" "(s, u) \<in> rstep_pos R p\<^sub>2"
  shows "(t, u) \<in> (rstep R)\<^sup>\<down>"
  using parallel_steps [OF _ _ parallel, of s t R _ _ _ u] and peak
  apply (auto simp: join_def rstep_pos_rstep_r_p_s_conv )
  apply (intro relcompI r_into_rtrancl)
  by (fastforce simp add: rstep_iff_rstep_r_p_s)+

text \<open>Peaks are either joinable or contain an instance of a critical peak.\<close>
(*Lemma 5.1.9*)
lemma peak_imp_join_or_S3_cpeaks:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes variable_condition: "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and peak: "(s, t) \<in> rstep_pos R p\<^sub>1" "(s, u) \<in> rstep_pos R p\<^sub>2"
  shows "(t, u) \<in> (rstep R)\<^sup>\<down> \<or> (
    (p\<^sub>2 \<le>\<^sub>p p\<^sub>1 \<and> (ctxt_of_pos_term p\<^sub>2 s)\<langle>t |_ p\<^sub>2\<rangle> = t \<and> (ctxt_of_pos_term p\<^sub>2 s)\<langle>u |_ p\<^sub>2\<rangle> = u \<and>
      (t |_ p\<^sub>2, pos_diff p\<^sub>1 p\<^sub>2, s |_ p\<^sub>2, u |_ p\<^sub>2) \<in> S3 (cpeaks R)) \<or>
    (p\<^sub>1 \<le>\<^sub>p p\<^sub>2 \<and> (ctxt_of_pos_term p\<^sub>1 s)\<langle>t |_ p\<^sub>1\<rangle> = t \<and> (ctxt_of_pos_term p\<^sub>1 s)\<langle>u |_ p\<^sub>1\<rangle> = u \<and>
      (u |_ p\<^sub>1, pos_diff p\<^sub>2 p\<^sub>1, s |_ p\<^sub>1, t |_ p\<^sub>1) \<in> S3 (cpeaks R)))"
proof -
  obtain l\<^sub>1' r\<^sub>1' \<sigma>\<^sub>1' l\<^sub>2 r\<^sub>2 \<sigma>\<^sub>2
    where rule1': "(l\<^sub>1', r\<^sub>1') \<in> R" and rule2: "(l\<^sub>2, r\<^sub>2) \<in> R"
    and p\<^sub>1: "p\<^sub>1 \<in> poss s" and p\<^sub>2: "p\<^sub>2 \<in> poss s"
    and s1': "replace_at s p\<^sub>1 (l\<^sub>1' \<cdot> \<sigma>\<^sub>1') = s" and t': "t = replace_at s p\<^sub>1 (r\<^sub>1' \<cdot> \<sigma>\<^sub>1')"
    and s2: "replace_at s p\<^sub>2 (l\<^sub>2 \<cdot> \<sigma>\<^sub>2) = s" and u: "u = replace_at s p\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)"
    using rstep_pos.cases [OF peak(1)]
      and rstep_pos.cases [OF peak(2)]
      by (metis ctxt_supt_id)

  from vars_rule_disjoint obtain \<pi>\<^sub>1
    where \<pi>\<^sub>1: "vars_rule (\<pi>\<^sub>1 \<bullet> (l\<^sub>1', r\<^sub>1')) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}" ..
  define l\<^sub>1 and r\<^sub>1 and \<sigma>\<^sub>1
    where "l\<^sub>1 = \<pi>\<^sub>1 \<bullet> l\<^sub>1'" and "r\<^sub>1 = \<pi>\<^sub>1 \<bullet> r\<^sub>1'" and "\<sigma>\<^sub>1 = (Var \<circ> Rep_perm (-\<pi>\<^sub>1)) \<circ>\<^sub>s \<sigma>\<^sub>1'"
  note rename = l\<^sub>1_def r\<^sub>1_def \<sigma>\<^sub>1_def

  have disj: "vars_rule (l\<^sub>1, r\<^sub>1) \<inter> vars_rule (l\<^sub>2, r\<^sub>2) = {}" using \<pi>\<^sub>1 by (auto simp: eqvt rename)
  have s1: "replace_at s p\<^sub>1 (l\<^sub>1 \<cdot> \<sigma>\<^sub>1) = s" and t: "t = replace_at s p\<^sub>1 (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
    by (simp_all add: s1' t' rename)

  have "-\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> R" and "0 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> R"
    using rule1' and rule2 by (simp_all add: rename)
  then have rule_variants: "\<exists>\<pi>. \<pi> \<bullet> (l\<^sub>1, r\<^sub>1) \<in> R" "\<exists>\<pi>. \<pi> \<bullet> (l\<^sub>2, r\<^sub>2) \<in> R" by blast+

  show ?thesis
  proof (cases "p\<^sub>1 \<bottom> p\<^sub>2")
    assume "p\<^sub>1 \<bottom> p\<^sub>2"
    moreover
    have "(s, t) \<in> rstep_r_p_s R (l\<^sub>1', r\<^sub>1') p\<^sub>1 \<sigma>\<^sub>1'"
      by (simp add: p\<^sub>1 rstep_r_p_s_def s1' t' rule1')
    moreover
    have "(s, u) \<in> rstep_r_p_s R (l\<^sub>2, r\<^sub>2) p\<^sub>2 \<sigma>\<^sub>2"
      by (simp add: p\<^sub>2 rstep_r_p_s_def s2 u rule2)
    ultimately
    obtain v where "(t, v) \<in> rstep R" and "(u, v) \<in> rstep R"
      by (blast dest: parallel_steps rstep_r_p_s_imp_rstep)
    then show ?thesis by blast
  next
    have sp\<^sub>1: "s |_ p\<^sub>1 = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using s1 and p\<^sub>1 by (metis replace_at_subt_at)
    have sp\<^sub>2: "s |_ p\<^sub>2 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using s2 and p\<^sub>2 by (metis replace_at_subt_at)

    assume "\<not> (p\<^sub>1 \<bottom> p\<^sub>2)"
    then have "p\<^sub>1 \<le>\<^sub>p p\<^sub>2 \<or> p\<^sub>2 \<le>\<^sub>p p\<^sub>1" by (metis parallel_pos)
    then show ?thesis
    proof
      have vars: "vars_term r\<^sub>1 \<subseteq> vars_term l\<^sub>1"
        using variable_condition [THEN bspec, OF rule1']
        and atom_set_pt.permute_set_subset [of "vars_term r\<^sub>1'" "vars_term l\<^sub>1'"]
        by (auto simp add: rename supp_vars_term_eq [symmetric] term_fs.supp_eqvt [symmetric])
      assume "p\<^sub>2 \<le>\<^sub>p p\<^sub>1"
      with peak_above_imp_join_or_cpeaks [OF rule_variants disj this vars p\<^sub>1 sp\<^sub>1 t p\<^sub>2 sp\<^sub>2 u]
        show ?thesis by (auto simp: s2)
    next
      have vars: "vars_term r\<^sub>2 \<subseteq> vars_term l\<^sub>2"
        using variable_condition [THEN bspec, OF rule2] by blast
      have disj: "vars_rule (l\<^sub>2, r\<^sub>2) \<inter> vars_rule (l\<^sub>1, r\<^sub>1) = {}" using disj by blast
      assume "p\<^sub>1 \<le>\<^sub>p p\<^sub>2"
      with peak_above_imp_join_or_cpeaks [OF rule_variants(2, 1) disj this vars p\<^sub>2 sp\<^sub>2 u p\<^sub>1 sp\<^sub>1 t]
        show ?thesis by (auto simp: s1)
    qed
  qed
qed

inductive_set CS3 for A
where
  "(t, p, s, u) \<in> A \<Longrightarrow> (C\<langle>t \<cdot> \<sigma>\<rangle>, hole_pos C @ p, C\<langle>s \<cdot> \<sigma>\<rangle>, C\<langle>u \<cdot> \<sigma>\<rangle>) \<in> CS3 A"

lemma CS3_imp_rstep:
  assumes "(t, p, s, u) \<in> CS3 A"
  shows "(t, u) \<in> rstep ((\<lambda>(w, x, y, z). (w, z)) ` A)"
  using assms by (cases) force

lemma S3_imp_CS3:
  assumes "p \<in> poss s"
    and S3: "(v, q, s |_ p, w) \<in> S3 A"
  shows "((ctxt_of_pos_term p s)\<langle>v\<rangle>, p @ q, s, (ctxt_of_pos_term p s)\<langle>w\<rangle>) \<in> CS3 A"
using S3
proof (cases)
  case (subst t' s' u' \<sigma>)
  with CS3.intros [OF subst(4), of "ctxt_of_pos_term p s" \<sigma>]
    show ?thesis by (simp add: assms replace_at_ident)
qed

lemma peak_imp_join_or_CS3_cpeaks:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes vc: "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and peak: "(s, t) \<in> rstep R" "(s, u) \<in> rstep R"
  shows "(t, u) \<in> (rstep R)\<^sup>\<down> \<or> (\<exists>p. (t, p, s, u) \<in> CS3 (cpeaks R) \<or> (u, p, s, t) \<in> CS3 (cpeaks R))"
proof -
  from peak obtain p q
    where peak: "(s, t) \<in> rstep_pos R p" "(s, u) \<in> rstep_pos R q"
    by (auto simp: rstep_rstep_pos_conv)
  then have "p \<in> poss s" and "q \<in> poss s" by (auto elim: rstep_pos.cases)
  with peak_imp_join_or_S3_cpeaks [OF vc peak]
    show ?thesis by (auto dest: S3_imp_CS3)
qed

definition CP2 :: "('f, 'v::infinite) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) rule set"
where
  "CP2 R R' = {(replace_at (fst r') p (snd r) \<cdot> \<sigma>, snd r' \<cdot> \<sigma>) |
    r p r' \<sigma>. overlap R R' r p r' \<and> \<sigma> = the_mgu (fst r) (fst r' |_ p)}"

abbreviation "CP R \<equiv> CP2 R R"

lemma CP2_I:
  assumes "overlap R R' r p r'" and "\<sigma> = the_mgu (fst r) (fst r' |_ p)"
  shows "(replace_at (fst r') p (snd r) \<cdot> \<sigma>, snd r' \<cdot> \<sigma>) \<in> CP2 R R'"
  using assms by (force simp: CP2_def)

lemma CP2_cpeaks2_conv:
  "CP2 R R' = (\<lambda>(t, p, s, u). (t, u)) ` cpeaks2 R R'"
  by (force simp: CP2_def cpeaks2_def)

lemma peak_imp_join_or_CP:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and "(s, t) \<in> rstep R" "(s, u) \<in> rstep R"
  shows "(t, u) \<in> (rstep R)\<^sup>\<down> \<or> (t, u) \<in> (rstep (CP R))\<^sup>\<leftrightarrow>"
  using peak_imp_join_or_CS3_cpeaks [OF assms]
  by (auto simp: CP2_cpeaks2_conv dest: CS3_imp_rstep )

lemma CP_join_imp_peak_join:
  assumes "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and *: "\<forall>(s, t)\<in>CP R. (s, t) \<in> (rstep R)\<^sup>\<down>"
  shows "(rstep R)\<inverse> O (rstep R) \<subseteq> (rstep R)\<^sup>\<down>"
proof -
  have "(rstep (CP R))\<^sup>\<leftrightarrow> \<subseteq> (rstep R)\<^sup>\<down>"
  proof (intro subrelI)
    fix s t
    assume "(s, t) \<in> (rstep (CP R))\<^sup>\<leftrightarrow>"
    then have "(s, t) \<in> rstep (CP R) \<or> (t, s) \<in> rstep (CP R)" by auto
    then show "(s, t) \<in> (rstep R)\<^sup>\<down>"
    proof
      assume "(s, t) \<in> rstep (CP R)"
      then obtain C \<sigma> u v where cp: "(u, v) \<in> CP R"
        and [simp]: "s = C\<langle>u \<cdot> \<sigma>\<rangle>" "t = C\<langle>v \<cdot> \<sigma>\<rangle>" by auto
      from * [THEN bspec, OF cp] show ?thesis by auto
    next
      assume "(t, s) \<in> rstep (CP R)"
      then obtain C \<sigma> u v where cp: "(u, v) \<in> CP R"
        and [simp]: "t = C\<langle>u \<cdot> \<sigma>\<rangle>" "s = C\<langle>v \<cdot> \<sigma>\<rangle>" by auto
      show ?thesis by (rule join_sym) (insert * [THEN bspec, OF cp], auto)
    qed
  qed
  with peak_imp_join_or_CP [OF assms(1)] show ?thesis by blast
qed

lemma CP2_imp_peak:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes "(s, t) \<in> CP2 R S"
  shows "(s, t) \<in> (rstep R)\<inverse> O (rstep S)"
proof -
  from assms obtain r p r' \<sigma>
    where overlap: "overlap R S r p r'"
    and \<sigma>: "\<sigma> = the_mgu (fst r) (fst r' |_ p)"
    and s: "s = replace_at (fst r') p (snd r) \<cdot> \<sigma>"
    and t: "t = snd r' \<cdot> \<sigma>"
    by (auto simp: CP2_def)
  obtain l\<^sub>1 r\<^sub>1 l\<^sub>2 r\<^sub>2
    where [simp]: "r = (l\<^sub>1, r\<^sub>1)" "r' = (l\<^sub>2, r\<^sub>2)" by (cases r, cases r') auto
  from overlap obtain \<pi>\<^sub>1 \<pi>\<^sub>2 and \<tau> :: "('f, 'v) subst"
    where "\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> R" and "\<pi>\<^sub>2 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> S"
    and p: "p \<in> fun_poss l\<^sub>2"
    and unif: "l\<^sub>1 \<cdot> \<tau> = l\<^sub>2 |_ p \<cdot> \<tau>"
    by (auto simp: overlap_def)
  then have "\<pi>\<^sub>1 \<bullet> (l\<^sub>1, r\<^sub>1) \<in> rstep R" and "\<pi>\<^sub>2 \<bullet> (l\<^sub>2, r\<^sub>2) \<in> rstep S"
    by (metis rstep_rule surjective_pairing)+
  then have "(l\<^sub>1, r\<^sub>1) \<in> rstep R" and "(l\<^sub>2, r\<^sub>2) \<in> rstep S"
    by (metis perm_rstep_imp_rstep rule_pt.permute_prod.simps)+
  then have "((ctxt_of_pos_term p l\<^sub>2)\<langle>l\<^sub>1\<rangle> \<cdot> \<sigma>, s) \<in> rstep R"
    and "(l\<^sub>2 \<cdot> \<sigma>, t) \<in> rstep S" by (auto simp: s t)
  moreover
  have "replace_at (l\<^sub>2) p (l\<^sub>1) \<cdot> \<sigma> = l\<^sub>2 \<cdot> \<sigma>"
    using the_mgu [OF unif] and fun_poss_imp_poss [OF p]
    by (auto simp: \<sigma>) (metis replace_at_ident subst_apply_term_ctxt_apply_distrib)
  ultimately
  show ?thesis by (auto)
qed

lemma WCR_imp_CP_join:
  assumes "(rstep R)\<inverse> O (rstep R) \<subseteq> (rstep R)\<^sup>\<down>"
   and "(s, t) \<in> CP R"
  shows "(s, t) \<in> (rstep R)\<^sup>\<down>"
  using CP2_imp_peak [OF assms(2)] and assms(1) by blast

text \<open>The Critical Pair Lemma\<close>
lemma CP:
  assumes "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
  shows "(rstep R)\<inverse> O (rstep R) \<subseteq> (rstep R)\<^sup>\<down> \<longleftrightarrow> (\<forall>(s, t)\<in>CP R. (s, t) \<in> (rstep R)\<^sup>\<down>)"
  using CP_join_imp_peak_join [OF assms] and WCR_imp_CP_join [of R] by auto

text \<open>A terminating TRS is confluent iff all critical pairs are joinable.\<close>
corollary SN_imp_CR_iff_CP_join:
  assumes "\<forall>(l, r)\<in>R. vars_term r \<subseteq> vars_term l"
    and "SN (rstep R)"
  shows "CR (rstep R) \<longleftrightarrow> (\<forall>(s, t)\<in>CP R. (s, t) \<in> (rstep R)\<^sup>\<down>)"
  using Newman [OF assms(2)] and CP [OF assms(1)]
  unfolding WCR_alt_def [symmetric]
  by (simp) (metis CR_on_def WCR_onI r_into_rtrancl)

definition
  "CP2_rules_pos R R' r p r' =
    {(replace_at (fst (\<pi>\<^sub>2 \<bullet> r')) p (snd (\<pi>\<^sub>1 \<bullet> r)) \<cdot> \<sigma>, snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>) | \<pi>\<^sub>1 \<pi>\<^sub>2 \<sigma>.
    mgu (fst (\<pi>\<^sub>1 \<bullet> r)) (fst (\<pi>\<^sub>2 \<bullet> r') |_ p) = Some \<sigma> \<and>
    overlap R R' (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r')}"

(*Auxiliary definition to obtain the result that only finitely many CPs have to be
considered.*)
definition
  CP2' :: "('f, 'v::infinite) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) rule set set"
where
  "CP2' R R' = {CP2_rules_pos R R' r p r' | r p r'. r \<in> R \<and> r' \<in> R' \<and> p \<in> fun_poss (fst r')}"

lemma finite_CP2':
  assumes "finite R" and "finite R'"
  shows "finite (CP2' R R')"
proof -
  let ?R = "{(r, p, r'). r \<in> R \<and> r' \<in> R' \<and> p \<in> fun_poss (fst r')}"
  have *: "CP2' R R' = (\<lambda>(r, p, r'). {(replace_at (fst (\<pi>\<^sub>2 \<bullet> r')) p (snd (\<pi>\<^sub>1 \<bullet> r)) \<cdot> \<sigma>, snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>) |
    \<pi>\<^sub>1 \<pi>\<^sub>2 \<sigma>. mgu (fst (\<pi>\<^sub>1 \<bullet> r)) (fst (\<pi>\<^sub>2 \<bullet> r') |_ p) = Some \<sigma> \<and>
    overlap R R' (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r')}) ` ?R"
    by (fastforce simp: CP2'_def CP2_rules_pos_def)
  have "{(r, p, r'). r \<in> R \<and> r' \<in> R' \<and> p \<in> fun_poss (fst r')} \<subseteq> R \<times> \<Union>(fun_poss ` lhss R') \<times> R'"
    by auto
  moreover have "finite (R \<times> \<Union>(fun_poss ` lhss R') \<times> R')"
    using assms and finite_fun_poss by auto
  ultimately have "finite ?R" by (rule finite_subset)
  then show ?thesis unfolding * by (rule finite_imageI)
qed

lemma overlap_permute_rules:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes "overlap R R' r p r'"
  shows "overlap R R' (\<pi> \<bullet> r) p (\<pi> \<bullet> r')"
  (is "overlap R R' ?r p ?r'")
proof -
  obtain \<pi>\<^sub>1' \<pi>\<^sub>2' and \<sigma> :: "('f, 'v) subst"
    where rules: "\<pi>\<^sub>1' \<bullet> r \<in> R" "\<pi>\<^sub>2' \<bullet> r' \<in> R'"
    and disj: "vars_rule r \<inter> vars_rule r' = {}"
    and pos: "p \<in> fun_poss (fst r')"
    and unif: "fst r \<cdot> \<sigma> = fst r' |_ p \<cdot> \<sigma>"
    and triv: "p = [] \<Longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> r = r')"
    using assms by (auto simp: overlap_def)
  have "(\<pi>\<^sub>1' + -\<pi>) \<bullet> ?r \<in> R" and "(\<pi>\<^sub>2' + -\<pi>) \<bullet> ?r' \<in> R'"
    using rules by auto
  then have "\<exists>\<pi>. \<pi> \<bullet> ?r \<in> R" and "\<exists>\<pi>. \<pi> \<bullet> ?r' \<in> R'" by blast+
  moreover have "vars_rule ?r \<inter> vars_rule ?r' = {}"
    unfolding vars_rule_eqvt [symmetric] using disj
    unfolding atom_set_pt.inter_eqvt [symmetric] by (simp)
  moreover have pos': "p \<in> fun_poss (fst ?r')" using pos by (simp add: rule_pt.fst_eqvt [symmetric])
  moreover have "fst ?r \<cdot> conjugate_subst \<pi> \<sigma> = fst ?r' |_ p \<cdot> conjugate_subst \<pi> \<sigma>"
    using unif and fun_poss_imp_poss [OF pos'] and fun_poss_imp_poss [OF pos]
    by (simp add: eqvt [symmetric])
  moreover have "p = [] \<Longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> ?r = ?r')"
    using triv by (auto) (metis left_minus rule_pt.permute_plus rule_pt.permute_zero)
  ultimately show ?thesis
    by (auto simp: overlap_def)
qed

lemma overlap_permuted_rules:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes "overlap R R' (\<pi> \<bullet> r) p (\<pi> \<bullet> r')" (is "overlap R R' ?r p ?r'")
  shows "overlap R R' r p r'"
proof -
  obtain \<pi>\<^sub>1' \<pi>\<^sub>2' and \<sigma> :: "('f, 'v) subst"
    where rules: "\<pi>\<^sub>1' \<bullet> ?r \<in> R" "\<pi>\<^sub>2' \<bullet> ?r' \<in> R'"
    and disj: "vars_rule ?r \<inter> vars_rule ?r' = {}"
    and pos: "p \<in> fun_poss (fst ?r')"
    and unif: "fst ?r \<cdot> \<sigma> = fst ?r' |_ p \<cdot> \<sigma>"
    and triv: "p = [] \<Longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> ?r = ?r')"
    using assms by (auto simp: overlap_def)
  have "(\<pi>\<^sub>1' + \<pi>) \<bullet> r \<in> R" and "(\<pi>\<^sub>2' + \<pi>) \<bullet> r' \<in> R'"
    using rules by auto
  then have "\<exists>\<pi>. \<pi> \<bullet> r \<in> R" and "\<exists>\<pi>. \<pi> \<bullet> r' \<in> R'" by blast+
  moreover have "vars_rule r \<inter> vars_rule r' = {}"
    using disj unfolding eqvt [symmetric]
    by (metis atom_set_pt.empty_eqvt atom_set_pt.permute_eq_iff)
  moreover have pos': "p \<in> fun_poss (fst r')" using pos by (simp add: rule_pt.fst_eqvt [symmetric])
  moreover have "fst r \<cdot> ((Var \<circ> Rep_perm \<pi>) \<circ>\<^sub>s \<sigma>) = fst r' |_ p \<cdot> ((Var \<circ> Rep_perm \<pi>) \<circ>\<^sub>s \<sigma>)"
    using unif and fun_poss_imp_poss [OF pos'] by (simp add: eqvt [symmetric])
  moreover have "p = [] \<Longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> r = r')"
    using triv by (auto) (metis diff_add_cancel rule_pt.permute_plus)
  ultimately show ?thesis
    unfolding overlap_def by blast
qed

lemma overlap_perm_simp [simp]:
  "overlap R R' (\<pi> \<bullet> r) p (\<pi> \<bullet> r') = overlap R R' r p r'"
  by (metis overlap_permute_rules overlap_permuted_rules)

text \<open>Overlaps that origin from the same rules at the same position are variants.\<close>
lemma same_rule_pos_overlap_imp_perm:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes "overlap R R' (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r')"
    and "overlap R R' (\<pi>\<^sub>3 \<bullet> r) p (\<pi>\<^sub>4 \<bullet> r')"
  shows "\<exists>\<pi>. \<pi> \<bullet> (\<pi>\<^sub>1 \<bullet> r) = \<pi>\<^sub>3 \<bullet> r \<and> \<pi> \<bullet> (\<pi>\<^sub>2 \<bullet> r') = \<pi>\<^sub>4 \<bullet> r'"
proof -
  from assms obtain \<tau> \<tau>' :: "('f, 'v) subst"
    where "vars_rule (\<pi>\<^sub>1 \<bullet> r) \<inter> vars_rule (\<pi>\<^sub>2 \<bullet> r') = {}"
      and "vars_rule (\<pi>\<^sub>3 \<bullet> r) \<inter> vars_rule (\<pi>\<^sub>4 \<bullet> r') = {}"
    by (auto simp: overlap_def dest!: fun_poss_imp_poss)
  from rule_variants_imp_perm [OF this(2, 1)] show ?thesis .
qed

text \<open>Critical pairs that origin from overlaps which are variants are also variants
of each other.\<close>
lemma overlap_variants_imp_CP_variants:
  fixes R R' :: "('f, 'v :: infinite) trs"
  assumes ol: "overlap R R' (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r')"
              "overlap R R' (\<pi>\<^sub>3 \<bullet> r) p (\<pi>\<^sub>4 \<bullet> r')"
    and mgu: "mgu (fst (\<pi>\<^sub>1 \<bullet> r)) (fst (\<pi>\<^sub>2 \<bullet> r') |_ p) = Some \<sigma>" (is "mgu ?s ?t = _")
             "mgu (fst (\<pi>\<^sub>3 \<bullet> r)) (fst (\<pi>\<^sub>4 \<bullet> r') |_ p) = Some \<sigma>'" (is "mgu ?u ?v = _")
  shows "\<exists>\<pi>.
    replace_at (fst (\<pi>\<^sub>2 \<bullet> r')) p (snd (\<pi>\<^sub>1 \<bullet> r)) \<cdot> \<sigma> =
    \<pi> \<bullet> (replace_at (fst (\<pi>\<^sub>4 \<bullet> r')) p (snd (\<pi>\<^sub>3 \<bullet> r)) \<cdot> \<sigma>') \<and>
    snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma> = \<pi> \<bullet> (snd (\<pi>\<^sub>4 \<bullet> r') \<cdot> \<sigma>')"
proof -
  have "p \<in> poss (fst (\<pi>\<^sub>2 \<bullet> r'))" using ol(1) by (auto simp: overlap_def dest: fun_poss_imp_poss)
  then have p: "p \<in> poss (fst r')" by (simp add: eqvt [symmetric])
  have mgu': "is_mgu \<sigma> {(?s, ?t)}" "is_mgu \<sigma>' {(?u, ?v)}"
    using mgu_sound [THEN is_imgu_imp_is_mgu] and mgu by auto
  have unif: "?s \<cdot> \<sigma> = ?t \<cdot> \<sigma>" "?u \<cdot> \<sigma>' = ?v \<cdot> \<sigma>'"
    using mgu' by (auto simp: is_mgu_def)
  define s and t where "s = fst r" and "t = fst r' |_ p"
  have unif: "(\<pi>\<^sub>1 \<bullet> s) \<cdot> \<sigma> = (\<pi>\<^sub>2 \<bullet> t) \<cdot> \<sigma>" "(\<pi>\<^sub>3 \<bullet> s) \<cdot> \<sigma>' = (\<pi>\<^sub>4 \<bullet> t) \<cdot> \<sigma>'"
    using unif and p by (simp add: s_def t_def eqvt)+
  have mgu': "is_mgu \<sigma> {(\<pi>\<^sub>1 \<bullet> s, \<pi>\<^sub>2 \<bullet> t)}" "is_mgu \<sigma>' {(\<pi>\<^sub>3 \<bullet> s, \<pi>\<^sub>4 \<bullet> t)}"
    using mgu' and p by (simp add: s_def t_def eqvt)+
  from same_rule_pos_overlap_imp_perm [OF ol(2, 1)] obtain \<pi> :: "'v perm"
    where 0: "\<pi>\<^sub>1 \<bullet> r = \<pi> \<bullet> \<pi>\<^sub>3 \<bullet> r" "\<pi>\<^sub>2 \<bullet> r' = \<pi> \<bullet> \<pi>\<^sub>4 \<bullet> r'" by metis
  then have *: "\<pi>\<^sub>1 \<bullet> s = \<pi> \<bullet> \<pi>\<^sub>3 \<bullet> s" "\<pi>\<^sub>2 \<bullet> t = \<pi> \<bullet> \<pi>\<^sub>4 \<bullet> t"
    using p by (simp_all add: s_def t_def eqvt)
  then have **: "\<pi>\<^sub>3 \<bullet> s = (-\<pi>) \<bullet> \<pi>\<^sub>1 \<bullet> s" "\<pi>\<^sub>4 \<bullet> t = (-\<pi>) \<bullet> \<pi>\<^sub>2 \<bullet> t" by auto

  have "is_mgu (sop \<pi> \<circ>\<^sub>s \<sigma>) {(\<pi>\<^sub>3 \<bullet> s, \<pi>\<^sub>4 \<bullet> t)}"
  proof (unfold is_mgu_def, intro conjI ballI)
    fix \<tau> :: "('f, 'v) subst"
    assume "\<tau> \<in> unifiers {(\<pi>\<^sub>3 \<bullet> s, \<pi>\<^sub>4 \<bullet> t)}"
    then have "\<pi>\<^sub>3 \<bullet> s \<cdot> \<tau> = \<pi>\<^sub>4 \<bullet> t \<cdot> \<tau>" by (simp add: unifiers_def)
    then have "(-\<pi>) \<bullet> \<pi>\<^sub>1 \<bullet> s \<cdot> \<tau> = (-\<pi>) \<bullet> \<pi>\<^sub>2 \<bullet> t \<cdot> \<tau>" by (simp add: ** )
    then have "\<pi>\<^sub>1 \<bullet> s \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau> = \<pi>\<^sub>2 \<bullet> t \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<tau>" by simp
    with mgu'(1) obtain \<mu> :: "('f, 'v) subst"
      where "sop (-\<pi>) \<circ>\<^sub>s \<tau> = \<sigma> \<circ>\<^sub>s \<mu>"
      unfolding is_mgu_def and unifiers_def by force
    then have "sop \<pi> \<circ>\<^sub>s sop (-\<pi>) \<circ>\<^sub>s \<tau> = sop \<pi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<mu>" by (simp add: ac_simps)
    then have "\<tau> = sop \<pi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<mu>" apply (simp add: subst_compose_def)
      by (metis inv_Rep_perm_simp permute_atom_def)
    then show "\<exists>\<mu>. \<tau> = sop \<pi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<mu>" by blast
  qed (simp add: unif ** unifiers_def)
  moreover have "finite (subst_domain (sop \<pi> \<circ>\<^sub>s \<sigma>))"
  proof -
    have "subst_domain (sop \<pi> \<circ>\<^sub>s \<sigma>) \<subseteq> subst_domain (sop \<pi> :: ('f, 'v) subst) \<union> subst_domain \<sigma>"
      using subst_domain_compose [of "sop \<pi>" \<sigma>] using [[show_sorts]] .
    moreover have "finite (subst_domain (sop \<pi>))" by (metis finite_subst_domain_sop)
    moreover have "finite (subst_domain \<sigma>)" using mgu_finite_subst_domain [OF mgu(1)] .
    ultimately show ?thesis by (metis infinite_Un infinite_super)
  qed
  moreover have "finite (subst_domain \<sigma>')" using mgu_finite_subst_domain [OF mgu(2)] .
  ultimately obtain \<pi>' where 1: "\<pi>' \<bullet> \<sigma>' = sop \<pi> \<circ>\<^sub>s \<sigma>"
    using is_mgu_imp_perm [OF mgu'(2)] by blast

  have "replace_at (fst (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>) p (snd (\<pi>\<^sub>1 \<bullet> r) \<cdot> \<sigma>) =
    \<pi>' \<bullet> (replace_at (fst (\<pi>\<^sub>4 \<bullet> r')) p (snd (\<pi>\<^sub>3 \<bullet> r)) \<cdot> \<sigma>')"
  proof -
    have "replace_at (fst (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>) p (snd (\<pi>\<^sub>1 \<bullet> r) \<cdot> \<sigma>) =
      \<pi> \<bullet> replace_at (fst (\<pi>\<^sub>4 \<bullet> r')) p (snd (\<pi>\<^sub>3 \<bullet> r)) \<cdot> \<sigma>"
      using p by (simp add: 0 eqvt ctxt_of_pos_term_subst)
    also have "\<dots> = \<pi>' \<bullet> (replace_at (fst (\<pi>\<^sub>4 \<bullet> r')) p (snd (\<pi>\<^sub>3 \<bullet> r)) \<cdot> \<sigma>')"
      using 1 apply auto
      by (metis permute_subst_subst_compose subst_apply_term_ctxt_apply_distrib subst_subst term_apply_subst_Var_Rep_perm)
    finally show ?thesis .
  qed
  moreover
  have "snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma> = \<pi>' \<bullet> (snd (\<pi>\<^sub>4 \<bullet> r') \<cdot> \<sigma>')"
  proof -
    have "snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma> = \<pi> \<bullet> snd (\<pi>\<^sub>4 \<bullet> r') \<cdot> \<sigma>" by (simp add: 0 eqvt)
    also have "\<dots> = \<pi>' \<bullet> (snd (\<pi>\<^sub>4 \<bullet> r') \<cdot> \<sigma>')"
      using 1 by (metis permute_subst_subst_compose subst_subst term_apply_subst_Var_Rep_perm)
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by (metis ctxt_of_pos_term_subst p poss_perm_prod_simps(1) subst_apply_term_ctxt_apply_distrib)
qed

lemma CP2_Union_CP2':
  "CP2 R R' = \<Union>(CP2' R R')"
proof
  show "\<Union>(CP2' R R') \<subseteq> CP2 R R'"
  proof
    fix s t
    assume "(s, t) \<in> \<Union>(CP2' R R')"
    then obtain r p r' \<pi>\<^sub>1 \<pi>\<^sub>2 \<sigma>
      where "r \<in> R" and "r' \<in> R'" and p: "p \<in> fun_poss (fst (\<pi>\<^sub>2 \<bullet> r'))"
      and "mgu (\<pi>\<^sub>1 \<bullet> fst r) (\<pi>\<^sub>2 \<bullet> fst r' |_ p) = Some \<sigma>"
      and ol: "overlap R R' (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r')"
      and s: "s = replace_at (fst (\<pi>\<^sub>2 \<bullet> r')) p (snd (\<pi>\<^sub>1 \<bullet> r)) \<cdot> \<sigma>"
      and t: "t = snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>"
      by (auto simp: CP2'_def CP2_rules_pos_def eqvt)
    then have "\<sigma> = the_mgu (\<pi>\<^sub>1 \<bullet> fst r) (\<pi>\<^sub>2 \<bullet> fst r' |_ p)" by (simp add: the_mgu_def)
    with ol show "(s, t) \<in> CP2 R R'"
      using fun_poss_imp_poss [OF p]
      unfolding CP2_def s t by (force simp add: eqvt ctxt_of_pos_term_subst)
  qed
next
  show "CP2 R R' \<subseteq> \<Union>(CP2' R R')"
  proof
    fix s t
    assume "(s, t) \<in> CP2 R R'"
    then obtain r p r' \<sigma>
      where ol: "overlap R R' r p r'"
      and "\<sigma> = the_mgu (fst r) (fst r' |_ p)"
      and s: "s = replace_at (fst r') p (snd r) \<cdot> \<sigma>"
      and t: "t = snd r' \<cdot> \<sigma>"
      by (auto simp: CP2_def)
    then have mgu: "mgu (fst r) (fst r' |_ p) = Some \<sigma>"
      unfolding overlap_def the_mgu_def
      using unify_complete and unify_sound by (force split: option.splits simp: mgu_def is_imgu_def unifiers_def)
    from ol obtain \<pi>\<^sub>1 \<pi>\<^sub>2
      where "\<pi>\<^sub>1 \<bullet> r \<in> R" (is "?r \<in> R")
      and "\<pi>\<^sub>2 \<bullet> r' \<in> R'" (is "?r' \<in> R'")
      and p: "p \<in> fun_poss (fst r')" by (auto simp: overlap_def)
    moreover
    have "overlap R R' (-\<pi>\<^sub>1 \<bullet> ?r) p (-\<pi>\<^sub>2 \<bullet> ?r')" using ol by simp
    moreover
    have "s = (ctxt_of_pos_term p (fst (-\<pi>\<^sub>2 \<bullet> ?r')))\<langle>snd (-\<pi>\<^sub>1 \<bullet> ?r)\<rangle> \<cdot> \<sigma>"
      and "t = snd (-\<pi>\<^sub>2 \<bullet> ?r') \<cdot> \<sigma>"
      using fun_poss_imp_poss [OF p] by (simp_all add: s t ctxt_of_pos_term_subst)
    moreover
    have "mgu (fst (-\<pi>\<^sub>1 \<bullet> ?r)) (fst (-\<pi>\<^sub>2 \<bullet> ?r') |_ p) = Some \<sigma>" using mgu by simp
    moreover have "p \<in> fun_poss (fst ?r')" using p by (simp add: eqvt [symmetric])
    ultimately show "(s, t) \<in> \<Union>(CP2' R R')"
      unfolding CP2'_def CP2_rules_pos_def by blast
  qed
qed

lemma CP2_rules_pos_perm:
  fixes R R' :: "('f, 'v :: infinite) trs"
  assumes "x \<in> CP2_rules_pos R R' r p r'"
    and "y \<in> CP2_rules_pos R R' r p r'"
  shows "\<exists>\<pi>. \<pi> \<bullet> x = y"
proof -
  from assms [unfolded CP2_rules_pos_def] obtain \<pi>\<^sub>1 \<pi>\<^sub>2 \<pi>\<^sub>3 \<pi>\<^sub>4 and \<sigma> \<sigma>' :: "('f, 'v) subst"
  where mgu: "mgu (fst (\<pi>\<^sub>1 \<bullet> r)) (fst (\<pi>\<^sub>2 \<bullet> r') |_ p) = Some \<sigma>"
             "mgu (fst (\<pi>\<^sub>3 \<bullet> r)) (fst (\<pi>\<^sub>4 \<bullet> r') |_ p) = Some \<sigma>'"
    and ol: "overlap R R' (\<pi>\<^sub>1 \<bullet> r) p (\<pi>\<^sub>2 \<bullet> r')"
            "overlap R R' (\<pi>\<^sub>3 \<bullet> r) p (\<pi>\<^sub>4 \<bullet> r')"
    and x: "x = (replace_at (fst (\<pi>\<^sub>2 \<bullet> r')) p (snd (\<pi>\<^sub>1 \<bullet> r)) \<cdot> \<sigma>, snd (\<pi>\<^sub>2 \<bullet> r') \<cdot> \<sigma>)"
    and y: "y = (replace_at (fst (\<pi>\<^sub>4 \<bullet> r')) p (snd (\<pi>\<^sub>3 \<bullet> r)) \<cdot> \<sigma>', snd (\<pi>\<^sub>4 \<bullet> r') \<cdot> \<sigma>')"
    by blast
  show ?thesis
    using overlap_variants_imp_CP_variants [OF ol(2, 1) mgu(2, 1)]
    by (auto simp: x y eqvt)
qed

lemma CP2_rules_pos_join:
  assumes "x \<in> CP2_rules_pos R R' r p r'"
    and "y \<in> CP2_rules_pos R R' r p r'"
  shows "x \<in> (rstep S)\<^sup>\<down> \<longleftrightarrow> y \<in> (rstep S)\<^sup>\<down>"
  using CP2_rules_pos_perm [OF assms] by auto

abbreviation "CP' R \<equiv> CP2' R R"

text \<open>If @{term R} and @{term R'} are finite, then @{term "CP2' R R'"} is finite
by @{thm finite_CP2'}. Thus it suffices to prove joinability of finitely many
critical pairs in order to conclude joinability of all critical pairs @{term "CP2 R R'"}.\<close>
lemma CP2'_representatives_join_imp_CP2_join:
  assumes "\<forall>C\<in>CP2' R R'. \<exists>(s, t)\<in>C. (s, t) \<in> (rstep S)\<^sup>\<down>"
  shows "\<forall>(s, t)\<in>CP2 R R'. (s, t) \<in> (rstep S)\<^sup>\<down>"
  using assms
  by (auto simp: CP2'_def CP2_Union_CP2')
     (blast dest: CP2_rules_pos_join [of _ R R' _ _ _ _ S])

lemma CS3_ctxt:
  assumes "(t, p, s, u) \<in> CS3 A"
  shows "(C\<langle>t\<rangle>, hole_pos C @ p, C\<langle>s\<rangle>, C\<langle>u\<rangle>) \<in> CS3 A"
proof -
  from assms obtain D \<sigma> t' s' u' p'
    where "(t', p', s', u') \<in> A" and "t = D\<langle>t' \<cdot> \<sigma>\<rangle>" "s = D\<langle>s' \<cdot> \<sigma>\<rangle>" "u = D\<langle>u' \<cdot> \<sigma>\<rangle>"
    and "p = hole_pos D @ p'"
    by (cases)
  with CS3.intros [OF this(1), of "C \<circ>\<^sub>c D" \<sigma>] show ?thesis by simp
qed

lemma overlap_imp_rstep:
  assumes "overlap R R' r p r'"
  shows "r \<in> rstep R" and "r' \<in> rstep R'"
  apply (insert assms)
  apply (case_tac [!] r, case_tac [!] r')
  apply (auto simp: overlap_def)
  by (metis perm_rstep_conv rstep_rule surj_pair)+

lemma overlap_imp_rstep_pos_Empty:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes "overlap R R' r p r'"
  shows "r \<in> rstep_pos R []" and "r' \<in> rstep_pos R' []"
proof -
  from assms [unfolded overlap_def] obtain \<pi>\<^sub>1 \<pi>\<^sub>2 l\<^sub>1 r\<^sub>1 l\<^sub>2 r\<^sub>2 and \<sigma> :: "('f, 'v) subst"
    where p: "p \<in> poss l\<^sub>2"
      and [simp]: "r = (l\<^sub>1, r\<^sub>1)" "r' = (l\<^sub>2, r\<^sub>2)"
      and 1: "(l\<^sub>1, r\<^sub>1) \<in> -\<pi>\<^sub>1 \<bullet> R" and 2: "(l\<^sub>2, r\<^sub>2) \<in> -\<pi>\<^sub>2 \<bullet> R'"
      by (cases r, cases r') (fastforce dest: fun_poss_imp_poss)
  from rstep_pos.intros [OF 1, of "[]" l\<^sub>1 Var]
    show "r \<in> rstep_pos R []" by simp
  from rstep_pos.intros [OF 2, of "[]" l\<^sub>2 Var]
    show "r' \<in> rstep_pos R' []" by simp
qed

lemma overlap_source_eq:
  fixes R :: "('f, 'v :: infinite) trs" and r p r'
  defines "\<sigma> \<equiv> the_mgu (fst r) (fst r' |_ p)"
  assumes "overlap R R' r p r'"
  shows "p \<in> poss (fst r')" (is ?A)
    and "fst r' \<cdot> \<sigma> = replace_at (fst r') p (fst r) \<cdot> \<sigma>" (is ?B)
proof -
  from assms obtain \<tau> :: "('f, 'v) subst"
    where p: "p \<in> poss (fst r')"
    and "fst r \<cdot> \<tau> = (fst r' |_ p) \<cdot> \<tau>"
    by (auto simp: overlap_def dest: fun_poss_imp_poss)
  from the_mgu [OF this(2)] and assms
    have "fst r \<cdot> \<sigma> = (fst r' |_ p) \<cdot> \<sigma>" by simp
  with p show ?B by (metis ctxt_supt_id subst_apply_term_ctxt_apply_distrib)
  show ?A by fact
qed

lemma overlap_rstep_pos_right:
  fixes R :: "('f, 'v :: infinite) trs" and r p r'
  defines "\<sigma> \<equiv> the_mgu (fst r) (fst r' |_ p)"
  assumes ol: "overlap R R' r p r'"
  shows "(fst r' \<cdot> \<sigma>, snd r' \<cdot> \<sigma>) \<in> rstep_pos R' []"
  using overlap_imp_rstep_pos_Empty(2) [OF ol]
    and overlap_source_eq [OF ol, folded \<sigma>_def]
    and rstep_pos_subst [of "fst r'" "snd r'" R' "[]" \<sigma>]
    by simp

lemma overlap_rstep_pos_left:
  fixes R :: "('f, 'v :: infinite) trs" and r p r'
  defines "\<sigma> \<equiv> the_mgu (fst r) (fst r' |_ p)"
  assumes ol: "overlap R R' r p r'"
  shows "(fst r' \<cdot> \<sigma>, (ctxt_of_pos_term p (fst r'))\<langle>snd r\<rangle> \<cdot> \<sigma>) \<in> rstep_pos R p"
  using overlap_imp_rstep_pos_Empty(1) [OF ol]
    and overlap_source_eq [OF ol, folded \<sigma>_def]
    and rstep_pos_supt [of "fst r \<cdot> \<sigma>" "snd r \<cdot> \<sigma>"  R "[]" p "fst r' \<cdot> \<sigma>"]
    apply (cases r, cases r')
    apply auto
    by (metis ctxt_of_pos_term_subst poss_imp_subst_poss rstep_pos_subst subt_at_ctxt_of_pos_term)

end

