(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015, 2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Normalization Equivalence\<close>

theory Normalization_Equivalence
  imports
    Encompassment
    Representative_System
    Ord.Reduction_Order
begin

definition "left_reduced R \<longleftrightarrow> (\<forall>(l, r)\<in>R. l \<in> NF (rstep (R - {(l, r)})))"
definition "right_reduced R \<longleftrightarrow> (\<forall>(l, r)\<in>R. r \<in> NF (rstep R))"
definition "reduced R \<longleftrightarrow> left_reduced R \<and> right_reduced R"
definition "canonical R \<longleftrightarrow> reduced R \<and> SN (rstep R) \<and> CR (rstep R)"

definition variant_free_trs :: "('f, 'v :: infinite) trs \<Rightarrow> bool"
  where
    "variant_free_trs R \<longleftrightarrow> (\<forall>l r l' r'.
    (l, r) \<in> R \<and> (l', r') \<in> R \<and> (\<exists>p. p \<bullet> l = l' \<and> p \<bullet> r = r') \<longrightarrow> l = l' \<and> r = r')"

lemma litsim_mem:
  assumes "R \<doteq> S" and "r \<in> R"
  obtains p where "p \<bullet> r \<in> S"
  using assms by (auto simp: subsumable_trs.litsim_def)

lemma variant_free_trs_insert:
  assumes "variant_free_trs R" and "\<forall>p. (p \<bullet> l, p \<bullet> r) \<notin> R"
  shows "variant_free_trs (insert (l, r) R)"
  using assms
  unfolding variant_free_trs_def eqvt [symmetric]
  by (metis (no_types, lifting) assms(2) insert_iff prod.sel(1) prod.sel(2) term_pt.permute_minus_cancel(2))

lemma variant_free_trs_diff:
  "variant_free_trs R \<Longrightarrow> variant_free_trs (R - S)"
  unfolding variant_free_trs_def by blast

lemma litsim_rstep_eq:
  fixes R S :: "('f, 'v::infinite) trs"
  assumes "R \<doteq> S"
  shows "rstep R = rstep S"
proof -
  { fix R S s t C l r and \<sigma> :: "('f, 'v) subst" assume "R \<doteq> S" and "(l, r) \<in> R"
      and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    then obtain \<pi> where "(\<pi> \<bullet> l, \<pi> \<bullet> r) \<in> S"
      by (metis rule_pt.permute_prod.simps subsumable_trs.litsim_def subsumeseq_trsE)
    moreover have "s = C\<langle>\<pi> \<bullet> l \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<sigma>\<rangle>" and "t = C\<langle>\<pi> \<bullet> r \<cdot> sop (-\<pi>) \<circ>\<^sub>s \<sigma>\<rangle>"
      using s and t
      by (simp_all add: eqvt [symmetric])
    ultimately have "(s, t) \<in> rstep S" by blast }
  then show ?thesis using assms by (auto elim!: rstepE dest: subsumable_trs.litsim_sym)
qed

lemma litsim_insert:
  assumes "R \<doteq> R'" and "r' = p \<bullet> r "
  shows "insert r R \<doteq> insert r' R'"
  using assms
  apply (auto simp: subsumeseq_trs_def subsumable_trs.litsim_def)
  using rule_pt.permute_minus_cancel(2) by blast

lemma litsim_insert':
  assumes "R \<doteq> R'" and "p \<bullet> r \<in> R'"
  shows "insert r R \<doteq> R'"
  using assms
  by (auto simp: subsumeseq_trs_def subsumable_trs.litsim_def)

lemma litsim_diff1:
  assumes "R \<doteq> R'" and "variant_free_trs R" and "variant_free_trs R'" and "r' = p \<bullet> r"
    and "r \<in> R" and "r' \<in> R'"
  shows "R - {r} \<doteq> R' - {r'}"
proof -
  { fix s assume "s \<in> R - {r}"
    then have "\<exists>p. p \<bullet> s \<in> R' - {r'}"
      using assms
      apply (cases "s = r")
       apply (force simp: variant_free_trs_def)
      apply (auto elim!: litsim_mem)
      apply (rule_tac x = pa in exI)
      unfolding variant_free_trs_def
      by (metis (no_types, opaque_lifting) prod.collapse rule_pt.fst_eqvt rule_pt.permute_minus_cancel(2) rule_pt.permute_plus rule_pt.snd_eqvt) }
  moreover
  { fix s assume "s \<in> R' - {r'}"
    moreover have "R' \<doteq> R" and "r = -p \<bullet> r'" using assms by (auto dest: subsumable_trs.litsim_sym)
    ultimately have "\<exists>p. p \<bullet> s \<in> R - {r}"
      using assms(2-3,5-)
      apply (cases "s = r'")
       apply (force simp: variant_free_trs_def)
      apply (auto elim!: litsim_mem)
      apply (rule_tac x = pa in exI)
      unfolding variant_free_trs_def
      by (metis (no_types, opaque_lifting) prod.collapse rule_pt.fst_eqvt rule_pt.permute_minus_cancel(2) rule_pt.permute_plus rule_pt.snd_eqvt) }
  ultimately
  show ?thesis
    by (auto simp: subsumable_trs.litsim_def subsumeseq_trs_def)
qed

lemma litsim_union:
  assumes "R \<doteq> R'" and "S \<doteq> S'"
  shows "R \<union> S \<doteq> R' \<union> S'"
  using assms by (auto simp: subsumeseq_trs_def subsumable_trs.litsim_def)

lemma litsim_symcl:
  assumes "R \<doteq> R'"
  shows "R\<^sup>\<leftrightarrow> \<doteq> R'\<^sup>\<leftrightarrow>"
  using assms
  apply (auto simp: subsumable_trs.litsim_def subsumeseq_trs_def)
   apply (metis converse.intros rule_pt.permute_prod.simps)+
  done

definition rm_variants :: "('f, 'v :: infinite) trs \<Rightarrow> ('f, 'v) trs"
  where
    "rm_variants R = repsys R (rule_pt.variants \<inter> R \<times> R)"

definition "dot' R = {(l, some_NF (rstep R) r) | l r. (l, r) \<in> R}"

definition dot :: "('f, 'v::infinite) trs \<Rightarrow> ('f, 'v) trs"
  where
    "dot R = rm_variants (dot' R)"

definition ddot :: "('f, 'v::infinite) trs \<Rightarrow> ('f, 'v) trs"
  where
    "ddot R = {(l, r) \<in> dot R. l \<in> NF (rstep (dot R - {(l, r)}))}"

lemma rm_variants_subset:
  "rm_variants R \<subseteq> R"
  using rule_pt.variants_equiv_on_TRS [of R, THEN repsys_subset] by (simp add: rm_variants_def)

lemma rm_variants_unique_modulo:
  assumes "x \<in> rm_variants R" and "y \<in> rm_variants R" and "x \<noteq> y"
  shows "\<not> (\<exists>p. p \<bullet> x = y)"
  using repsys_unique_modulo [of R, OF rule_pt.variants_equiv_on_TRS, folded rm_variants_def, OF assms]
    and assms and rm_variants_subset [of R]
  by (auto simp: rule_pt.variants_def)

lemma rm_variants_representative:
  "(l, r) \<in> R \<Longrightarrow> \<exists>p. \<exists>(l', r') \<in> rm_variants R. p \<bullet> (l, r) = (l', r')"
  using repsys_representative [of R, OF rule_pt.variants_equiv_on_TRS, folded rm_variants_def]
  by (fastforce simp: eqvt rule_pt.variants_def)

lemma variant_free_rm_variants:
  "variant_free_trs (rm_variants R)"
  using rm_variants_unique_modulo [of _ R] by (fastforce simp: variant_free_trs_def eqvt)

lemma variant_free_ddot:
  shows "variant_free_trs (ddot R)"
  using variant_free_rm_variants
  unfolding ddot_def dot_def variant_free_trs_def by fast

lemma right_reduced_mono:
  assumes "R \<subseteq> S" and "right_reduced S"
  shows "right_reduced R"
  using assms apply (auto simp: right_reduced_def)
  by (metis NF_anti_mono in_mono rstep_mono split_conv)

lemma ddot_subset_dot:
  "ddot R \<subseteq> dot R"
  by (auto simp: ddot_def)

lemma lhss_dot:
  "lhss (dot R) \<subseteq> lhss R"
  using rm_variants_subset by (force simp: dot_def dot'_def)

lemma lhss_variants:
  "\<forall>l \<in> lhss R. \<exists>p. \<exists>l' \<in> lhss (dot R). p \<bullet> l = l'"
proof
  fix l
  assume *: "l \<in> lhss R"
  from * obtain r where "(l, r) \<in> dot' R" by (force simp: dot'_def)
  with rm_variants_representative [of l r "dot' R"] obtain p l' r'
    where "(l', r') \<in> rm_variants (dot' R)"
      and "p \<bullet> l = l'" by (force simp: eqvt)
  moreover then have "l' \<in> lhss (dot R)" by (force simp add: dot_def dot'_def eqvt)
  ultimately show "\<exists>p. \<exists>l' \<in> lhss (dot R). p \<bullet> l = l'" by blast
qed

lemma lhss_eq_imp_NF_subset:
  assumes "\<forall>l \<in> lhss S. \<exists>p. \<exists>l' \<in> lhss R. p \<bullet> l = l'"
  shows "NF (rstep R) \<subseteq> NF (rstep S)"
proof
  fix t
  assume "t \<in> NF (rstep R)"
  show "t \<in> NF (rstep S)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain s where "(t, s) \<in> rstep S" by blast
    then obtain C \<sigma> l r where "(l, r) \<in> S"
      and [simp]: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" and [simp]: "s = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
    with assms obtain p l' r' where "(l', r') \<in> R" and "p \<bullet> l = l'" by force
    then have "(p \<bullet> l, r') \<in> rstep R" by auto
    from rstep_subst [OF this, of "sop (-p)"]
    have "(l, -p \<bullet> r') \<in> rstep R" by simp
    then have "(t, C\<langle>(-p \<bullet> r') \<cdot> \<sigma>\<rangle>) \<in> rstep R" by auto
    with \<open>t \<in> NF (rstep R)\<close> show False by blast
  qed
qed

lemma NF_rstep_dot:
  "NF (rstep (dot R)) = NF (rstep R)"
  using term_set_pt.subset_imp_ex_perm [OF lhss_dot, THEN lhss_eq_imp_NF_subset, of R]
    and lhss_eq_imp_NF_subset [OF lhss_variants, of R] by blast

lemma NF_eq_imp_left_reduced:
  assumes "NF (rstep (ddot R)) = NF (rstep (dot R))"
  shows "left_reduced (ddot R)"
proof (unfold left_reduced_def, intro ballI2)
  fix l r
  assume "(l, r) \<in> ddot R"
  then have "(l, r) \<in> dot R"
    and *: "l \<in> NF (rstep (dot R - {(l, r)}))" by (auto simp: ddot_def)
  show "l \<in> NF (rstep (ddot R - {(l, r)}))"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain u where "(l, u) \<in> rstep (ddot R - {(l, r)})" by auto
    from rstepE [OF this]
    obtain C \<sigma> l' r' where "(l', r') \<in> ddot R - {(l, r)}"
      and [simp]: "l = C\<langle>l' \<cdot> \<sigma>\<rangle>" "u = C\<langle>r' \<cdot> \<sigma>\<rangle>" by metis
    then have "(l', r') \<in> dot R - {(l, r)}" using ddot_subset_dot [of R] by auto
    then have "(l, u) \<in> rstep (dot R - {(l, r)})" by auto
    with * show False by blast
  qed
qed

locale SN_ars =
  fixes A :: "'a rel"
  assumes SN: "SN A"
begin

lemma some_NF_rtrancl:
  "(x, some_NF A x) \<in> A\<^sup>*"
  apply (auto simp: some_NF_def normalizability_def)
  by (metis (lifting) SN SN_imp_WN UNIV_I WN_onD normalizability_E someI)

lemma Ex_NF:
  "\<exists>y. (x, y) \<in> A\<^sup>!"
  by (metis SN SN_imp_WN UNIV_I WN_on_def)

lemma some_NF_NF:
  "some_NF A x \<in> NF A"
  apply (auto simp: some_NF_def)
  by (metis (lifting, no_types) Ex_NF normalizability_E someI)

lemma some_NF_NF':
  "(x, some_NF A x) \<in> A\<^sup>!"
  using some_NF_rtrancl [of x] and some_NF_NF [of x] by (simp add: normalizability_def)

end

locale SN_trs =
  SN_ars "rstep R" for R :: "('f, 'v :: infinite) trs"
begin

lemma dot_imp_rhs_NF:
  assumes "(l, r) \<in> dot R"
  shows "r \<in> NF (rstep (dot R))"
  using assms and rm_variants_subset
  unfolding NF_rstep_dot by (auto simp: dot_def dot'_def intro: some_NF_NF)

lemma dot_right_reduced:
  "right_reduced (dot R)"
  by (auto simp: right_reduced_def dest: dot_imp_rhs_NF)

end

lemma WN_NE_imp_step_subset_conv:
  assumes "WN A"
    and "A\<^sup>! = B\<^sup>!"
  shows "A \<subseteq> B\<^sup>\<leftrightarrow>\<^sup>*"
proof
  fix a b assume "(a, b) \<in> A"
  moreover obtain c where "(b, c) \<in> A\<^sup>!" using \<open>WN A\<close> by blast
  ultimately have "(a, c) \<in> A\<^sup>!" by blast
  with \<open>(b, c) \<in> A\<^sup>!\<close> show "(a, b) \<in> B\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding assms
    unfolding normalizability_def
    by (auto intro: join_imp_conversion [THEN subsetD])
qed

text \<open>Normalization equivalent normalizing ARSs are equivalent.\<close>
lemma WN_NE_imp_conv_eq:
  assumes "WN A" and "WN B"
    and NE: "A\<^sup>! = B\<^sup>!"
  shows "A\<^sup>\<leftrightarrow>\<^sup>* = B\<^sup>\<leftrightarrow>\<^sup>*"
  using WN_NE_imp_step_subset_conv [OF assms(1) NE, THEN conversion_mono]
    and WN_NE_imp_step_subset_conv [OF assms(2) NE [symmetric], THEN conversion_mono]
  by simp

locale complete_ars =
  SN_ars A for A :: "'a rel" +
  assumes CR: "CR A"
begin

lemma complete_NE_intro2:
  assumes "SN B" and "B\<^sup>! \<subseteq> A\<^sup>!"
  shows "complete_ars B \<and> A\<^sup>! = B\<^sup>!"
proof -
  have "A\<^sup>! \<subseteq> B\<^sup>!"
  proof
    interpret SN_ars B by standard fact
    fix a b
    obtain c where "(a, c) \<in> B\<^sup>!" using Ex_NF by blast
    with \<open>B\<^sup>! \<subseteq> A\<^sup>!\<close> have "(a, c) \<in> A\<^sup>!" by blast
    moreover
    assume "(a, b) \<in> A\<^sup>!"
    ultimately have [simp]: "b = c" using CR by (metis CR_imp_UNF UNF_onD UNIV_I)
    with \<open>(a, c) \<in> B\<^sup>!\<close> show "(a, b) \<in> B\<^sup>!" by simp
  qed
  with \<open>B\<^sup>! \<subseteq> A\<^sup>!\<close> have **: "A\<^sup>! = B\<^sup>!" by blast
  with \<open>SN B\<close> [THEN SN_imp_WN] and \<open>B\<^sup>! \<subseteq> A\<^sup>!\<close> have "B \<subseteq> A\<^sup>\<leftrightarrow>\<^sup>*"
    by (metis SN [THEN SN_imp_WN] WN_NE_imp_conv_eq conversionI' r_into_rtrancl subrelI)
  have "CR B"
  proof (rule Newman [OF \<open>SN B\<close>], rule)
    fix x y z
    assume "(x, y) \<in> B" and "(x, z) \<in> B"
    with subsetD[OF \<open>B \<subseteq> A\<^sup>\<leftrightarrow>\<^sup>*\<close>] rtrancl_trans have "(y, z) \<in>  A\<^sup>\<leftrightarrow>\<^sup>*"
      by (metis converse.intros conversion_converse conversion_rtrancl)
    then obtain u where "(y, u) \<in> A\<^sup>*" and "(z, u) \<in> A\<^sup>*"
      unfolding CR_imp_conversionIff_join[OF CR] by auto
    moreover obtain v where "(u, v) \<in> A\<^sup>!" using Ex_NF by blast
    ultimately have "(y, v) \<in> A\<^sup>!" and "(z, v) \<in> A\<^sup>!" by (metis normalizability_I')+
    then have "(y, v) \<in> B\<^sup>!" and "(z, v) \<in> B\<^sup>!" unfolding ** by auto
    then show "(y, z) \<in> B\<^sup>\<down>" by auto
  qed
  have "complete_ars B" by standard fact+
  with ** show ?thesis by simp
qed

lemma complete_NE_intro1:
  assumes "B \<subseteq> A\<^sup>\<leftrightarrow>\<^sup>*" and "SN B" and "NF B \<subseteq> NF A"
  shows "complete_ars B \<and> A\<^sup>! = B\<^sup>!"
proof -
  from \<open>B \<subseteq> A\<^sup>\<leftrightarrow>\<^sup>*\<close> conversion_rtrancl in_rtrancl_UnI have "B\<^sup>! \<subseteq> A\<^sup>\<leftrightarrow>\<^sup>*"
    by (metis normalizability_E subrelI subset_Un_eq)
  with CR_NF_conv[OF CR] have "B\<^sup>! \<subseteq> A\<^sup>!"
    by (meson \<open>NF B \<subseteq> NF A\<close> normalizability_E set_mp subrelI)
  from complete_NE_intro2[OF \<open>SN B\<close> this] show ?thesis .
qed

(*Lemma 2.4 of IWC paper*)
lemma complete_NE_intro:
  assumes "B \<subseteq> A\<^sup>+" and "NF B \<subseteq> NF A"
  shows "complete_ars B \<and> A\<^sup>! = B\<^sup>!"
proof -
  have "SN B" by (rule SN_subset [OF SN_imp_SN_trancl [OF SN] \<open>B \<subseteq> A\<^sup>+\<close>])
  moreover have "B\<^sup>* \<subseteq> A\<^sup>*" using \<open>B \<subseteq> A\<^sup>+\<close>
    by (auto) (metis rtrancl_mono set_rev_mp trancl_rtrancl_absorb)
  ultimately have "B\<^sup>! \<subseteq> A\<^sup>!" using \<open>NF B \<subseteq> NF A\<close> by best
  from complete_NE_intro2[OF \<open>SN B\<close> this] show ?thesis .
qed

end

locale complete_trs =
  complete_ars "rstep R" for R :: "('f, 'v :: infinite) trs"
begin

lemma dot_subset_rstep_trancl:
  "dot R \<subseteq> (rstep R)\<^sup>+"
proof
  fix l r
  assume "(l, r) \<in> dot R"
  then obtain "(l, r) \<in> dot' R" using rm_variants_subset by (auto simp: dot_def)
  { fix l r
    assume "(l, r) \<in> R"
    then have "(l, r) \<in> rstep R" by auto
    moreover have "(r, some_NF (rstep R) r) \<in> (rstep R)\<^sup>*" by (rule some_NF_rtrancl)
    ultimately have "(l, some_NF (rstep R) r) \<in> (rstep R)\<^sup>+" by auto }
  then have "dot' R \<subseteq> (rstep R)\<^sup>+" by (auto simp: dot'_def)
  with \<open>(l, r) \<in> dot' R\<close> show "(l, r) \<in> (rstep R)\<^sup>+" by auto
qed

lemma rstep_dot_subset_rstep_trancl:
  "rstep (dot R) \<subseteq> (rstep R)\<^sup>+"
  using dot_subset_rstep_trancl
  by (auto elim!: rstepE)
    (metis rsteps_subst_closed set_rev_mp trancl_rstep_ctxt)

lemma
  complete_ars_rstep_dot: "complete_ars (rstep (dot R))" and
  NE_dot [simp]: "(rstep (dot R))\<^sup>! = (rstep R)\<^sup>!"
  using complete_NE_intro [OF rstep_dot_subset_rstep_trancl] by (auto simp: NF_rstep_dot)

end

lemma not_NF_minus_rule:
  assumes "l \<notin> NF (rstep (R - {(l, r)}))"
  shows "\<exists>(l', r') \<in> R. (l, r) \<noteq> (l', r') \<and> l \<cdot>\<unrhd> l'"
proof -
  from assms obtain u where "(l, u) \<in> rstep (R - {(l, r)})" by auto
  from rstepE [OF this] obtain C \<sigma> l' r'
    where "(l', r') \<in> R - {(l, r)}" and [simp]: "l = C\<langle>l' \<cdot> \<sigma>\<rangle>" "u = C\<langle>r' \<cdot> \<sigma>\<rangle>" by metis
  then show ?thesis by (blast)
qed

sublocale complete_trs \<subseteq> SN_trs ..

sublocale complete_trs \<subseteq> complete_ars "rstep R" ..

context complete_trs
begin

lemma variant_free_dot:
  "variant_free_trs (dot R)"
  using variant_free_rm_variants by (simp add: dot_def)

text \<open>If @{term R} is a complete TRS than @{term "ddot R"} is a (normalization) equivalent
canonical TRS.\<close>
(*Theorem 3.3 of IWC paper*)
lemma canonical_NE_conv_eq:
  "canonical (ddot R) \<and> (rstep (ddot R))\<^sup>! = (rstep R)\<^sup>! \<and> (rstep (ddot R))\<^sup>\<leftrightarrow>\<^sup>* = (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
proof (intro conjI)
  interpret dot_ars: complete_ars "(rstep (dot R))" by (rule complete_ars_rstep_dot)
  interpret dot_trs: complete_trs "dot R" ..
  from ddot_subset_dot [THEN rstep_mono, of R]
  have SN_ddot: "SN (rstep (ddot R))" by (metis SN_subset dot_ars.SN)
  have "NF (rstep R) = NF (rstep (dot R))"
    using NF_rstep_dot [of R] by simp
  { fix s t
    assume "(s, t) \<in> rstep (dot R)"
    then obtain C \<sigma> l r where "(l, r) \<in> dot R"
      and [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
    from \<open>(l, r) \<in> dot R\<close> have "l \<notin> NF (rstep (ddot R))"
    proof (induct l arbitrary: r rule: encomp_induct)
      case (1 l)
      show ?case
      proof (cases "(l, r) \<in> ddot R")
        assume "(l, r) \<notin> ddot R"
        then have "l \<notin> NF (rstep (dot R - {(l, r)}))"
          using \<open>(l, r) \<in> dot R\<close> by (auto simp: ddot_def)
        from not_NF_minus_rule [OF this] obtain l' r'
          where "(l', r') \<in> dot R"
            and "(l, r) \<noteq> (l', r')"
            and "l \<cdot>\<unrhd> l'" using \<open>(l, r) \<in> dot R\<close> by auto
        then have "l \<cdot>\<rhd> l' \<or> l \<doteq> l'" by (auto simp: term_subsumable.litsim_def dest: encompeq_cases)
        then show ?thesis
        proof
          assume "l \<cdot>\<rhd> l'"
          with 1 and \<open>(l', r') \<in> dot R\<close> have "l' \<notin> NF (rstep (ddot R))" by auto
          with \<open>l \<cdot>\<rhd> l'\<close> show ?thesis
            by (auto simp: encomp_def NF_iff_no_step elim!: encompeq.cases)
              (metis rstep_ctxt rstep_subst)
        next
          assume "l \<doteq> l'"
          then obtain \<pi> where \<pi>_l: "\<pi> \<bullet> l = l'" by (auto simp: litsim_term_iff)
          have "r \<in> NF (rstep (dot R))" and "r' \<in> NF (rstep (dot R))"
            using \<open>(l, r) \<in> dot R\<close> and \<open>(l', r') \<in> dot R\<close> and dot_imp_rhs_NF by blast+
          then have "\<pi> \<bullet> r \<in> NF (rstep (dot R))"
            by (auto simp: NF_iff_no_step) (metis perm_rstep_imp_rstep perm_rstep_perm)
          have "(\<pi> \<bullet> l, \<pi> \<bullet> r) \<in> (rstep (dot R))\<^sup>*"
            and "(l', r') \<in> (rstep (dot R))\<^sup>*" using \<open>(l, r) \<in> dot R\<close> and \<open>(l', r') \<in> dot R\<close> by auto
          with dot_ars.CR and \<open>\<pi> \<bullet> r \<in> NF (rstep (dot R))\<close> and \<open>r' \<in> NF (rstep (dot R))\<close>
          have "\<pi> \<bullet> r = r'"
            by (auto simp: \<pi>_l CR_defs NF_iff_no_step) (metis converse_rtranclE joinD)
          then have "\<pi> \<bullet> (l, r) = (l', r')" by (simp add: eqvt \<pi>_l)
          with \<open>(l, r) \<in> dot R\<close> and \<open>(l', r') \<in> dot R\<close> and variant_free_dot
          have False
            by (simp add: variant_free_trs_def) (metis \<pi>_l \<open>\<pi> \<bullet> r = r'\<close> \<open>(l, r) \<noteq> (l', r')\<close>)
          then show ?thesis by blast
        qed
      qed auto
    qed
    then have "s \<notin> NF (rstep (ddot R))"
      by (auto simp: NF_iff_no_step) blast }
  then have *: "NF (rstep (ddot R)) \<subseteq> NF (rstep (dot R))" by blast
  then have **: "NF (rstep (ddot R)) = NF (rstep (dot R))"
    using ddot_subset_dot [of R]
    by (auto) (metis NF_anti_mono order_class.order.antisym rstep_mono)
  from complete_NE_intro [OF _ * [simplified NF_rstep_dot]]
    and ddot_subset_dot [THEN rstep_mono, of R] and rstep_dot_subset_rstep_trancl
  have "complete_ars (rstep (ddot R))" and ***: "(rstep (ddot R))\<^sup>! = (rstep R)\<^sup>!" by auto
  then interpret ddot_trs: complete_ars "rstep (ddot R)" by simp
  interpret ddot_trs: complete_trs "ddot R" ..
  show "(rstep (ddot R))\<^sup>! = (rstep R)\<^sup>!" by fact
  from WN_NE_imp_conv_eq [OF SN_ddot [THEN SN_imp_WN] SN [THEN SN_imp_WN] ***]
  show "(rstep (ddot R))\<^sup>\<leftrightarrow>\<^sup>* = (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" .
  have "right_reduced (ddot R)" by (fact right_reduced_mono [OF ddot_subset_dot dot_right_reduced])
  from NF_eq_imp_left_reduced [OF **]
  have "left_reduced (ddot R)" .
  have "reduced (ddot R)" by (auto simp: reduced_def) fact+
  then show "canonical (ddot R)" by (auto simp: canonical_def SN_ddot ddot_trs.CR)
qed

end

lemma size_permute_term [simp]:
  fixes t :: "('f, 'v :: infinite) term"
  shows "size (p \<bullet> t) = size t"
proof (induct t)
  case (Fun g ts)
  then have *: "\<And>t. t \<in> set ts \<Longrightarrow> size (p \<bullet> t) \<le> size t"
    and **: "\<And>t. t \<in> set ts \<Longrightarrow> size t \<le> size (p \<bullet> t)" by auto
  from size_list_pointwise [of ts _ size, OF *]
    and size_list_pointwise [of ts size, OF **]
  show ?case by (simp add: o_def)
qed simp

lemma permute_term_size:
  fixes s t :: "('f, 'v :: infinite) term"
  assumes "p \<bullet> s = t"
  shows "size s = size t"
  unfolding assms [symmetric] by simp

lemma size_ctxt_Hole [simp]:
  assumes "size (C\<langle>t\<rangle>) = size t"
  shows "C = \<box>"
  using assms
  apply (induct C) apply (auto)
  using supteq_size [OF ctxt_imp_supteq, of t]
  by (metis Suc_n_not_le_n le_SucI add.commute trans_le_add2)

lemma ctxt_permute_term:
  assumes "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "p \<bullet> l = s"
  shows "C = \<box> \<and> (\<forall>x \<in> vars_term l. sop p x = \<sigma> x)"
proof -
  from \<open>s = C\<langle>l \<cdot> \<sigma>\<rangle>\<close> have "s \<unrhd> l \<cdot> \<sigma>" by auto
  then have "size s \<ge> size (l \<cdot> \<sigma>)" using supteq_size by blast
  moreover have "size s = size l" using permute_term_size [OF \<open>p \<bullet> l = s\<close>] ..
  moreover have "size (l \<cdot> \<sigma>) \<ge> size l" by (auto simp: size_subst)
  ultimately have "size (C\<langle>l \<cdot> \<sigma>\<rangle>) = size (l \<cdot> \<sigma>)" unfolding assms by auto
  then have "C = \<box>" by simp
  moreover then have "\<forall>x \<in> vars_term l. sop p x = \<sigma> x" using \<open>p \<bullet> l = s\<close>
    using assms
    by (metis assms(1) intp_actxt.simps(1) term_apply_subst_Var_Rep_perm term_subst_eq_rev)
  ultimately show ?thesis by blast
qed

(*Lemma 3.5 of IWC paper*)
lemma right_reduced_min_step_rule:
  assumes vc: "\<forall>(l, r) \<in> R. vars_term r \<subseteq> vars_term l"
    and rr: "right_reduced R"
    and min: "\<forall>t. s \<cdot>\<rhd> t \<longrightarrow> t \<in> NF (rstep R)"
    and steps: "(s, t) \<in> (rstep R)\<^sup>+"
  shows "\<exists>p. \<exists>(l, r) \<in> R. s = p \<bullet> l \<and> t = p \<bullet> r"
proof -
  from steps obtain u
    where "(s, u) \<in> rstep R" and "(u, t) \<in> (rstep R)\<^sup>*" by (auto dest: tranclD)
  then obtain C \<sigma> l r where "(l, r) \<in> R"
    and [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "u = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  then have "s \<cdot>\<unrhd> l" by auto
  moreover have "l \<notin> NF (rstep R)" using \<open>(l, r) \<in> R\<close> by auto
  ultimately have "l \<doteq> s" using min unfolding encompeq_litsim_encomp_iff by auto
  then obtain p where "s = p \<bullet> l" unfolding litsim_term_iff by blast
  then have [simp]: "C = \<box>"
    and *: "\<forall>x \<in> vars_term l. sop p x = \<sigma> x" using ctxt_permute_term [of s]
    by auto metis+
  then have "s = l \<cdot> \<sigma>" by simp
  have "\<forall>x \<in> vars_term r. sop p x = \<sigma> x" using * and vc and \<open>(l, r) \<in> R\<close> by blast
  then have "p \<bullet> r = r \<cdot> \<sigma>"
    by (metis term_apply_subst_Var_Rep_perm term_subst_eq)
  then have "(s, p \<bullet> r) \<in> rstep R" and "u = p \<bullet> r" using \<open>(l, r) \<in> R\<close> by auto
  have "r \<in> NF (rstep R)" using \<open>(l, r) \<in> R\<close> and rr by (auto simp: right_reduced_def)
  then have "p \<bullet> r \<in> NF (rstep R)"
    by (auto simp: NF_iff_no_step) (metis perm_rstep_perm rstep_permute_iff)
  with \<open>(u, t) \<in> (rstep R)\<^sup>*\<close> [unfolded \<open>u = p \<bullet> r\<close>, THEN NF_not_suc]
  have "t = p \<bullet> r" by simp
  with \<open>(l, r) \<in> R\<close> and \<open>s = p \<bullet> l\<close>
  show ?thesis by auto
qed

lemma left_reduced_imp_lhs_min:
  assumes "left_reduced R"
    and "(l, r) \<in> R"
  shows "\<forall>t. l \<cdot>\<rhd> t \<longrightarrow> t \<in> NF (rstep R)"
proof (intro allI impI)
  fix t
  have *: "l \<in> NF (rstep (R - {(l, r)}))" using assms by (auto simp: left_reduced_def)
  assume "l \<cdot>\<rhd> t"
  show "t \<in> NF (rstep R)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain C \<sigma> l' r' where "(l', r') \<in> R"
      and [simp]: "t = C\<langle>l' \<cdot> \<sigma>\<rangle>" by (auto simp: NF_iff_no_step)
    have "(l', r') \<in> R - {(l, r)}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with \<open>(l', r') \<in> R\<close> have [simp]: "l' = l" "r' = r" by auto
      with \<open>t = C\<langle>l' \<cdot> \<sigma>\<rangle>\<close> have "t \<cdot>\<unrhd> l" by (auto simp: encompeq.intros)
      with \<open>l \<cdot>\<rhd> t\<close> show False by (auto simp: encomp_def)
    qed
    then have "(t, C\<langle>r' \<cdot> \<sigma>\<rangle>) \<in> rstep (R - {(l, r)})" by auto
    moreover from \<open>l \<cdot>\<rhd> t\<close> obtain D \<tau> where "l = D\<langle>t \<cdot> \<tau>\<rangle>"
      by (auto simp: encomp_def elim: encompeq.cases)
    ultimately have "(l, D\<langle>(C\<langle>r' \<cdot> \<sigma>\<rangle>)\<cdot>\<tau>\<rangle>) \<in> rstep (R - {(l, r)})" by blast
    with * show False by (auto simp: NF_iff_no_step)
  qed
qed

lemma reduced_NE_imp_unique':
  assumes vc: "\<forall>(l, r) \<in> S. vars_term r \<subseteq> vars_term l"
  assumes "reduced R" and "right_reduced S"
    and NE: "(rstep R)\<^sup>! = (rstep S)\<^sup>!"
  shows "R \<le>\<cdot> S"
proof
  fix rule assume "rule \<in> R"
  then obtain l and r where [simp]: "rule = (l, r)" and "(l, r) \<in> R" by (cases rule) auto
  with \<open>reduced R\<close> have "r \<in> NF (rstep R)"
    and "(l, r) \<in> rstep R" by (auto simp: reduced_def right_reduced_def)
  then have "l \<noteq> r" and "(l, r) \<in> (rstep R)\<^sup>!" by (auto simp: NF_iff_no_step)
  then have "(l, r) \<in> (rstep S)\<^sup>+" and "r \<in> NF (rstep S)"
    unfolding NE by (auto dest: rtranclD simp: normalizability_def)
  from left_reduced_imp_lhs_min [OF _ \<open>(l, r) \<in> R\<close>] and \<open>reduced R\<close>
  have "\<forall>t. l \<cdot>\<rhd> t \<longrightarrow> t \<in> NF (rstep R)" by (auto simp: reduced_def)
  with NE have "\<forall>t. l \<cdot>\<rhd> t \<longrightarrow> t \<in> NF (rstep S)" by auto
  from right_reduced_min_step_rule [OF vc \<open>right_reduced S\<close> this \<open>(l, r) \<in> (rstep S)\<^sup>+\<close>]
  obtain p and l' r' where "(l', r') \<in> S" and "l = p \<bullet> l'" and "r = p \<bullet> r'" by blast
  then have "-p \<bullet> rule \<in> S" by simp
  then show "\<exists>p. p \<bullet> rule \<in> S" by blast
qed

text \<open>Normalization equivalent reduced TRSs are unique up to renaming.\<close>
(*Theorem 3.6 of IWC paper.*)
lemma reduced_NE_imp_unique:
  assumes vc: "\<forall>(l, r) \<in> R. vars_term r \<subseteq> vars_term l" "\<forall>(l, r) \<in> S. vars_term r \<subseteq> vars_term l"
    and "reduced R" and "reduced S"
    and NE: "(rstep R)\<^sup>! = (rstep S)\<^sup>!"
  shows "R \<doteq> S"
  using reduced_NE_imp_unique' [OF vc(2) \<open>reduced R\<close> _ NE]
    and reduced_NE_imp_unique' [OF vc(1) \<open>reduced S\<close> _ NE [symmetric]]
    and \<open>reduced R\<close> and \<open>reduced S\<close> unfolding reduced_def subsumable_trs.litsim_def by force

locale reduction_order_infinite =
  reduction_order less
  for less :: "('f, 'v :: infinite) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<succ>" 50)
begin

lemma EQ_compat_imp_NE:
  assumes "canonical R" and "canonical S"
    and EQ: "(rstep R)\<^sup>\<leftrightarrow>\<^sup>* = (rstep S)\<^sup>\<leftrightarrow>\<^sup>*"
    and compat: "R \<subseteq> {(x, y). x \<succ> y}" "S \<subseteq> {(x, y). x \<succ> y}"
  shows "(rstep R)\<^sup>! \<subseteq> (rstep S)\<^sup>!"
proof -
  have "reduced R" and "SN (rstep R)" and "CR (rstep R)"
    using \<open>canonical R\<close> by (auto simp: canonical_def)
  have "reduced S" and "SN (rstep S)" and "CR (rstep S)"
    using \<open>canonical S\<close> by (auto simp: canonical_def)
  interpret cR: complete_trs R by standard fact+
  interpret cS: complete_trs S by standard fact+

  show "(rstep R)\<^sup>! \<subseteq> (rstep S)\<^sup>!"
  proof
    fix s t
    assume "(s, t) \<in> (rstep R)\<^sup>!"
    then have "t \<in> NF (rstep R)" by auto
    define u where "u = some_NF (rstep S) t"
    have "(t, u) \<in> (rstep S)\<^sup>!" unfolding u_def by (rule cS.some_NF_NF')
    then have "(t, u) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" by (auto simp: EQ)
    then have "(u, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" by (metis conversion_inv)
    with \<open>t \<in> NF (rstep R)\<close> have "(u, t) \<in> (rstep R)\<^sup>!"
      using CR_NF_conv [OF cR.CR] by blast
    have "t = u"
    proof (rule ccontr)
      assume "t \<noteq> u"
      with \<open>(t, u) \<in> (rstep S)\<^sup>!\<close> and \<open>(u, t) \<in> (rstep R)\<^sup>!\<close>
      have "(t, u) \<in> (rstep S)\<^sup>+" and "(u, t) \<in> (rstep R)\<^sup>+" by (metis normalizability_E rtranclD)+
      with compatible_rstep_trancl_imp_less and compat
      have "t \<succ> u" and "u \<succ> t" by auto
      then show False by (metis irrefl trans)
    qed
    with \<open>(t, u) \<in> (rstep S)\<^sup>!\<close> have "t \<in> NF (rstep S)" by auto
    moreover have "(s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using \<open>(s, t) \<in> (rstep R)\<^sup>!\<close> by auto
    ultimately show "(s, t) \<in> (rstep S)\<^sup>!"
      unfolding EQ using CR_NF_conv [OF cS.CR] by blast
  qed
qed

(*Theorem 3.7 of IWC paper*)
lemma EQ_imp_litsim:
  assumes vc: "\<forall>(l, r) \<in> R. vars_term r \<subseteq> vars_term l"
    "\<forall>(l, r) \<in> S. vars_term r \<subseteq> vars_term l"
    and canonical: "canonical R" "canonical S"
    and "(rstep R)\<^sup>\<leftrightarrow>\<^sup>* = (rstep S)\<^sup>\<leftrightarrow>\<^sup>*"
    and "R \<subseteq> {\<succ>}" and "S \<subseteq> {\<succ>}"
  shows "R \<doteq> S"
proof -
  from EQ_compat_imp_NE and assms(2-) have "(rstep R)\<^sup>! = (rstep S)\<^sup>!" by blast
  from reduced_NE_imp_unique [OF vc _ _ this] and canonical
  show ?thesis by (auto simp: canonical_def)
qed

end

end
