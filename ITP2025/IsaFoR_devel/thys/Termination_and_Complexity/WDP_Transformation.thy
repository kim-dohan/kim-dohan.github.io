(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Weak Dependency Pairs\<close>

theory WDP_Transformation
imports        
  First_Order_Rewriting.Multihole_Context
  TRS.Q_Restricted_Rewriting
  Ord.Complexity
  Auxx.Util
begin

context sharp_syntax
begin

adhoc_overloading
  SHARP \<rightleftharpoons> "map (sharp_term shp)"

end

locale pre_wdps =
  fixes shp :: "'f \<Rightarrow> 'f"
    and \<C> :: "'f sig" \<comment> \<open>constructors and compound symbols\<close>
begin

interpretation sharp_syntax .

abbreviation "ccap \<equiv> cap_till_funas (- \<C>) :: ('f, 'v) term \<Rightarrow> _"
abbreviation "dmax \<equiv> uncap_till_funas (- \<C>) :: ('f, 'v) term \<Rightarrow> _"

definition is_WDP_of :: "('f, 'a) rule \<Rightarrow> ('f, 'a) rule \<Rightarrow> bool"
where
  "is_WDP_of p r \<longleftrightarrow>
    fst p = \<sharp> (fst r) \<and> (\<exists>C. ground_mctxt C \<and> funas_mctxt C \<subseteq> \<C> \<and> snd p =\<^sub>f (C, \<sharp>(dmax (snd r))))"

end

locale wdps =
  pre_wdps shp for shp :: "'f \<Rightarrow> 'f" +
  fixes \<F> :: "'f sig" \<comment> \<open>signature\<close>
    and \<R> :: "('f, 'v) trs"
    and \<Q> :: "('f, 'v) terms"
    and \<Q>' :: "('f, 'v) terms"
  assumes sig_R: "funas_trs \<R> \<subseteq> \<F>"
    and C_fresh: "({f. defined \<R> f} \<union> sharp_sig shp \<F>) \<inter> \<C> = {}"
    and wf_R: "wf_trs \<R>"
    and Q': "\<Q>' \<subseteq> \<Q> \<union> {Fun f ts | f ts. (f, length ts) \<notin> \<F>}"
begin

interpretation sharp_syntax shp .

abbreviation le_sharp :: "('f, 'v) term list \<Rightarrow> ('f, 'v) term list \<Rightarrow> bool" (infix "\<le>\<^sub>\<sharp>" 50)
where
  "xs \<le>\<^sub>\<sharp> ys \<equiv> list_all2 (\<lambda>x y. y = x \<or> y = \<sharp> x) xs ys"

definition good_for :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<lless>" 55)
where
  "s \<lless> t \<longleftrightarrow>
    (\<exists>C ts. ground_mctxt C \<and> funas_mctxt C \<subseteq> \<C> \<and> funas_term s \<subseteq> \<F> \<and> dmax s \<le>\<^sub>\<sharp> ts \<and> t =\<^sub>f (C, ts))"

abbreviation "compose_ccap \<equiv> compose_cap_till_funas (- \<C>) :: ('f, 'v) term \<Rightarrow> _"

lemma if_Fun_in_set [dest]:
  "funas_term t \<subseteq> \<F> \<Longrightarrow> if_Fun_in_set \<F> t"
  by (cases t) (auto simp:)

lemma dmax_sharp_singleton [simp]:
  assumes "funas_term t \<subseteq> \<F>" and "s \<in> set (dmax t)"
  shows "dmax (\<sharp> s) = [\<sharp> s]"
proof -
  from funas_uncap_till_subset and assms
    have "funas_term s \<subseteq> \<F>" by blast
  moreover from uncap_till and \<open>s \<in> set (dmax t)\<close>
    have "if_Fun_in_set (- \<C>) s" by blast
  ultimately show ?thesis using C_fresh by (cases s) auto
qed

lemma le_sharp_dmax_singleton:
  assumes "funas_term t \<subseteq> \<F>" and "dmax t \<le>\<^sub>\<sharp> us" and "u \<in> set us"
  shows "dmax u = [u]"
proof -
  from assms(2-) obtain s where "s \<in> set (dmax t)"
    and "u = s \<or> u = \<sharp> s" by (cases rule: list_all2_in_set2)
  then show ?thesis
    using assms(1) by (elim disjE) (simp_all add: uncap_till_singleton)
qed

lemma le_sharp_map_dmax_sharp [simp]:
  assumes "funas_term t \<subseteq> \<F>" and "dmax t \<le>\<^sub>\<sharp> us"
  shows "map dmax us = map (\<lambda>x. [x]) us"
  using le_sharp_dmax_singleton [OF assms] by simp

lemma le_sharp_concat_map [simp]:
  assumes "\<forall>x \<in> set xs. f x \<le>\<^sub>\<sharp> g x"
  shows "concat (map f xs) \<le>\<^sub>\<sharp> concat (map g xs)"
  using assms by (induct xs) (auto intro: list_all2_appendI)

lemma le_sharp_refl [simp]:
  "ts \<le>\<^sub>\<sharp> ts"
  by (metis (mono_tags, lifting) list_all2_all_nthI)

context
  fixes R :: "('f, 'v) trs"
    and WDP :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
  assumes WDP: "\<forall>r \<in> R. \<exists>p \<in> WDP R. is_WDP_of p r"
    and "R \<subseteq> \<R>"
begin

lemma in_R:
  "x \<in> R \<Longrightarrow> x \<in> \<R>"
  using \<open>R \<subseteq> \<R>\<close> by auto

lemma le_sharp_dmax_subst:
  assumes "funas_term (t \<cdot> \<sigma>) \<subseteq> \<F>"
  shows "dmax (t \<cdot> \<sigma>) \<le>\<^sub>\<sharp> concat (map dmax (map (\<lambda>s. s \<cdot> \<sigma>) (\<sharp>(dmax t))))"
using assms
proof (induct t)
  case (Fun f ts)
  then have "\<forall>t \<in> set ts. dmax (t \<cdot> \<sigma>) \<le>\<^sub>\<sharp> concat (map dmax (map (\<lambda>s. s \<cdot> \<sigma>) (\<sharp>(dmax t))))"
    by fastforce
  then have *: "concat (map (dmax \<circ> (\<lambda>s. s \<cdot> \<sigma>)) ts) \<le>\<^sub>\<sharp>
    concat (map (concat \<circ> (map dmax \<circ> (map (\<lambda>s. s \<cdot> \<sigma>) \<circ> (\<sharp> \<circ> dmax)))) ts)" by simp
  show ?case
  proof (cases "(f, length ts) \<in> (- \<C>)")
    case True
    with Fun.prems and C_fresh show ?thesis by auto
  next
    case False
    then show ?thesis using * by (simp add: map_concat concat_concat_map)
  qed
qed simp

lemma NF_terms_Q':
  assumes "t \<in> NF_terms \<Q>" and "funas_term t \<subseteq> \<F>"
  shows "t \<in> NF_terms \<Q>'"
proof
  fix C l \<sigma>
  assume [simp]: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" and "l \<in> \<Q>'"
  with Q' have "l \<in> \<Q> \<or> l \<in> {Fun f ts | f ts. (f, length ts) \<notin> \<F>}" by blast
  then show False using assms by auto
qed

lemma NF_subst_Q':
  assumes "\<Union>(funas_term ` \<sigma> ` vars_rule r) \<subseteq> \<F>" and "NF_subst nfs r \<sigma> \<Q>"
  shows "NF_subst nfs r \<sigma> \<Q>'"
  using assms and NF_terms_Q' by (auto simp add: NF_subst_def vars_rule_def UN_subset_iff)

lemma qrstep_good_for:
  assumes "(s, t) \<in> qrstep nfs \<Q> R" and "s \<lless> u"
  shows "\<exists>v. t \<lless> v \<and> (u, v) \<in> qrstep nfs \<Q>' (WDP R \<union> R)"
proof -
  from assms obtain C l r \<sigma>
    where args: "\<forall>u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms \<Q>" and nfs: "NF_subst nfs (l, r) \<sigma> \<Q>"
    and rule: "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  then obtain f and n where root: "root (l \<cdot> \<sigma>) = Some (f, n)" and "defined \<R> (f, n)"
    using wf_R and sig_R
    by (cases l, auto simp: wf_trs_def defined_def dest!: in_R) (metis root.simps(2))
  then have "(f, n) \<in> - \<C>" using C_fresh and sig_R by blast
  from in_uncap_till_funas [OF root this s] obtain i and D
    where i: "i < length (dmax s)" "dmax s ! i = D\<langle>l \<cdot> \<sigma>\<rangle>"
      and C: "mctxt_of_ctxt C = compose_ccap s i (mctxt_of_ctxt D)" by blast
  define ss\<^sub>1 where "ss\<^sub>1 = take i (dmax s)"
  define ss\<^sub>2 where "ss\<^sub>2 = drop (Suc i) (dmax s)"
  have [simp]: "length ss\<^sub>1 = i" using i by (simp add: ss\<^sub>1_def)
  have dmax_s: "dmax s = ss\<^sub>1 @ D\<langle>l \<cdot> \<sigma>\<rangle> # ss\<^sub>2"
    using i by (auto simp: ss\<^sub>1_def ss\<^sub>2_def dest: id_take_nth_drop)
  have "t =\<^sub>f (compose_ccap s i (mctxt_of_ctxt D), [r \<cdot> \<sigma>])"
    using t unfolding C [symmetric] by (metis mctxt_of_ctxt)
  from eqfE [OF this]
    have "t =\<^sub>f (ccap s, ss\<^sub>1 @ D\<langle>r \<cdot> \<sigma>\<rangle> # ss\<^sub>2)"
    using fill_holes_compose_cap_till [of i "if_Fun_in_set (- \<C>)" s "mctxt_of_ctxt D" "[r \<cdot> \<sigma>]"] and i
    by (auto simp: ss\<^sub>1_def ss\<^sub>2_def)
  from eqfE [OF this]
    have t': "t = fill_holes (ccap s) (ss\<^sub>1 @ D\<langle>r \<cdot> \<sigma>\<rangle> # ss\<^sub>2)"
    and *: "num_holes (ccap s) = length (ss\<^sub>1 @ D\<langle>r \<cdot> \<sigma>\<rangle> # ss\<^sub>2)" by simp_all
  from \<open>s \<lless> u\<close> obtain F and us
    where us: "dmax s \<le>\<^sub>\<sharp> us" and u_eqf: "u =\<^sub>f (F, us)" and funas_s: "funas_term s \<subseteq> \<F>"
    and F: "ground_mctxt F" "funas_mctxt F \<subseteq> \<C>"
    by (auto simp: good_for_def)
  moreover then have "u = fill_holes F us" and "num_holes F = length us" by (auto dest: eqfE)
  ultimately have dmax_u: "dmax u = us"
    using uncap_till_funas_fill_holes_cancel [of _ _ "- \<C>"] by simp
  define us\<^sub>1 where "us\<^sub>1 = take i us"
  define us\<^sub>2 where "us\<^sub>2 = drop (Suc i) us"
  from us have le_sharp: "ss\<^sub>1 \<le>\<^sub>\<sharp> us\<^sub>1" "ss\<^sub>2 \<le>\<^sub>\<sharp> us\<^sub>2"
    and shp: "us ! i = D\<langle>l \<cdot> \<sigma>\<rangle> \<or> us ! i = \<sharp>(D\<langle>l \<cdot> \<sigma>\<rangle>)"
    using i by (auto simp: ss\<^sub>1_def ss\<^sub>2_def us\<^sub>1_def us\<^sub>2_def dest: list_all2_nthD)
  have [simp]: "length us = length (dmax s)" using us by (simp add: list_all2_lengthD)
  have [simp]: "length us\<^sub>1 = i" "length us\<^sub>2 = length ss\<^sub>2"
    using le_sharp by (auto dest: list_all2_lengthD)
  have "dmax t = concat (map (dmax) (ss\<^sub>1 @ D\<langle>r \<cdot> \<sigma>\<rangle> # ss\<^sub>2))" using * by (simp add: t')
  also have "\<dots> = ss\<^sub>1 @ dmax (D\<langle>r \<cdot> \<sigma>\<rangle>) @ ss\<^sub>2"
    by (simp add: ss\<^sub>1_def ss\<^sub>2_def drop_map [symmetric] take_map [symmetric])
       (simp add: drop_map take_map)
  finally have dmax_t: "dmax t = ss\<^sub>1 @ dmax (D\<langle>r \<cdot> \<sigma>\<rangle>) @ ss\<^sub>2" .
  have funas_t: "funas_term t \<subseteq> \<F>"
    using wf_R and sig_R and funas_s and rule
    by (auto simp add: s t dest: funas_term_subst_rhs in_R)
  then have "funas_ctxt C \<subseteq> \<F>" and "funas_term (r \<cdot> \<sigma>) \<subseteq> \<F>"
    by (simp_all add: t)
  have "funas_term (D\<langle>l \<cdot> \<sigma>\<rangle>) \<subseteq> \<F>"
    using funas_s and i and funas_uncap_till_subset [of "dmax s ! i" "if_Fun_in_set (- \<C>)" s]
    by (auto dest: nth_mem iff: subset_iff)
  then have "funas_ctxt D \<subseteq> \<F>" and "funas_term (l \<cdot> \<sigma>) \<subseteq> \<F>" by simp_all
  with \<open>funas_term (r \<cdot> \<sigma>) \<subseteq> \<F>\<close> have funas_i: "funas_term (D\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> \<F>" by simp
  have "\<forall>u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms \<Q>'"
    using args and NF_terms_Q' and \<open>funas_term (l \<cdot> \<sigma>) \<subseteq> \<F>\<close> and supt_imp_funas_term_subset [of "l \<cdot> \<sigma>"]
    by (auto) (metis order_trans)
  have "NF_subst nfs (l, r) \<sigma> \<Q>'"
    using \<open>funas_term (l \<cdot> \<sigma>) \<subseteq> \<F>\<close> 
    by (intro NF_subst_Q' [OF _ nfs])
       (simp add: funas_term_subst vars_rule_lhs [OF wf_R in_R [OF rule]])
  show ?thesis using shp
  proof
    assume us_i: "us ! i = \<sharp> (D\<langle>l \<cdot> \<sigma>\<rangle>)"
    show ?thesis
    proof (cases "D = \<box>")
      case False
      with i and uncap_till [of "if_Fun_in_set (- \<C>)" s]
        have [simp]: "dmax (D\<langle>r \<cdot> \<sigma>\<rangle>) = [D\<langle>r \<cdot> \<sigma>\<rangle>]"
        and [simp]: "ccap (D\<langle>r \<cdot> \<sigma>\<rangle>) = MHole"
        by (case_tac [!] D) (force dest: nth_mem)+
      let ?u = "\<sharp> (D\<langle>r \<cdot> \<sigma>\<rangle>)"
      define v where "v = fill_holes (ccap u) (us\<^sub>1 @ ?u # us\<^sub>2)"
  
      have **: "fill_holes (ccap u) (us\<^sub>1 @ ?u # us\<^sub>2) =\<^sub>f (ccap u, us\<^sub>1 @ ?u # us\<^sub>2)"
        by (auto simp: dmax_u dmax_s)
      have "t \<lless> v"
      proof -
        have "funas_mctxt (ccap u) \<subseteq> \<C>"
          using cap_till_funas [of _ u] by blast
        moreover have "ground_mctxt (ccap u)" by auto
        moreover have "funas_term t \<subseteq> \<F>" by fact
        moreover have "v =\<^sub>f (ccap u, us\<^sub>1 @ ?u # us\<^sub>2)"
          using ** by (auto simp: v_def)
        moreover have "dmax t \<le>\<^sub>\<sharp> us\<^sub>1 @ ?u # us\<^sub>2"
          using le_sharp by (auto simp: dmax_t intro: list_all2_appendI)
        ultimately show ?thesis unfolding good_for_def by blast
      qed
      moreover
      have "(u, v) \<in> qrstep nfs \<Q>' (WDP R \<union> R)"
      proof -
        from fill_holes_ctxt_main [of "ccap u" "us\<^sub>1" "us\<^sub>2"] obtain C
          where [simp]: "\<And>t. fill_holes (ccap u) (us\<^sub>1 @ t # us\<^sub>2) = C\<langle>t\<rangle>"
          using * by (auto simp: dmax_u)
        have "u = fill_holes (ccap u) (us\<^sub>1 @ \<sharp>(D\<langle>l \<cdot> \<sigma>\<rangle>) # us\<^sub>2)"
          using fill_holes_cap_till_uncap_till_id [of "if_Fun_in_set (- \<C>)" u]
            and us_i and i and id_take_nth_drop [of i us]
            by (simp add: dmax_u us\<^sub>1_def us\<^sub>2_def)
        then have "u = (C \<circ>\<^sub>c \<sharp> D)\<langle>l \<cdot> \<sigma>\<rangle>" using False by simp
        have "v = fill_holes (ccap u) (us\<^sub>1 @ ?u # us\<^sub>2)" by (simp add: v_def)
        then have "v = (C \<circ>\<^sub>c \<sharp> D)\<langle>r \<cdot> \<sigma>\<rangle>" using False by simp
        have "(l, r) \<in> WDP R \<union> R" using rule by blast
        show ?thesis by (rule qrstepI) fact+
      qed
      ultimately
      show ?thesis by blast
    next
      case True
      obtain E and q
        where wdp: "(\<sharp> l, q) \<in> WDP R"
        and E: "ground_mctxt E" "funas_mctxt E \<subseteq> \<C>"
        and "q =\<^sub>f (E, \<sharp>(dmax r))"
        using WDP [THEN bspec, OF rule] by (auto simp: is_WDP_of_def)
      then have q: "q = fill_holes E (\<sharp>(dmax r))"
        and [simp]: "num_holes E = length (\<sharp>(dmax r))" by (auto dest: eqfE)
      have [simp]: "\<sharp>(l \<cdot> \<sigma>) = (\<sharp> l) \<cdot> \<sigma>"
        using rule and wf_R by (cases l) (auto simp: wf_trs_def dest: in_R)
      define v where "v = fill_holes (ccap u) (us\<^sub>1 @ q \<cdot> \<sigma> # us\<^sub>2)"
      define vs where "vs = concat (map dmax (map (\<lambda>s. s \<cdot> \<sigma>) (\<sharp>(dmax r))))"
      have "t \<lless> v"
      proof -
        define Cs where "Cs = map ccap (map (\<lambda>s. s \<cdot> \<sigma>) (\<sharp>(dmax r)))"
        define C where "C = compose_mctxt (ccap u) i (fill_holes_mctxt E Cs)"
        have "funas_mctxt C \<subseteq> \<C>"
          using cap_till_funas [of "(- \<C>)" u] and E and cap_till_funas [of "(- \<C>)"]
          and funas_uncap_till_subset [of _ "if_Fun_in_set (- \<C>)" r]
          and \<open>funas_term (D\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> \<F>\<close>
          by (auto simp: C_def True Cs_def) (case_tac "i = x", auto)+
        moreover have "ground_mctxt C"
          using i and E by (auto simp: C_def dmax_u Cs_def)
        moreover have "funas_term t \<subseteq> \<F>" by fact
        moreover have "v =\<^sub>f (C, us\<^sub>1 @ vs @ us\<^sub>2)"
        proof (unfold C_def dmax_t True intp_actxt.simps map_append list.map, rule compose_mctxt_sound)
          show "v =\<^sub>f (ccap u, us\<^sub>1 @ q \<cdot> \<sigma> # us\<^sub>2)" by (auto simp: v_def dmax_u dmax_s)
        next
          have "fill_holes E (map (\<lambda>s. s \<cdot> \<sigma>) (\<sharp>(dmax r))) =\<^sub>f
            (fill_holes_mctxt E Cs, vs)" (is "_ =\<^sub>f (?C, vs)")
            unfolding vs_def by (rule fill_holes_mctxt_sound) (auto simp: Cs_def split_term_eqf)
          moreover
          have "fill_holes E (map (\<lambda>s. s \<cdot> \<sigma>) (\<sharp>(dmax r))) = fill_holes E (\<sharp>(dmax r)) \<cdot> \<sigma>"
            using E by (auto simp: subst_apply_mctxt_fill_holes)
          ultimately have "(fill_holes E (\<sharp>(dmax r))) \<cdot> \<sigma> =\<^sub>f (fill_holes_mctxt E Cs, vs)"
            unfolding vs_def by auto
          then show "q \<cdot> \<sigma> =\<^sub>f (fill_holes_mctxt E Cs, vs)" by (simp add: q) 
        next
          show "i = length us\<^sub>1" by simp
        qed
        moreover have "dmax t \<le>\<^sub>\<sharp> us\<^sub>1 @ vs @ us\<^sub>2"
        proof -
          have "dmax (D\<langle>r \<cdot> \<sigma>\<rangle>) \<le>\<^sub>\<sharp> vs"
            using \<open>funas_term (D\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> \<F>\<close>
            using le_sharp_dmax_subst [of r \<sigma>] by (simp add: vs_def True)
          then show ?thesis using le_sharp by (auto simp: dmax_t intro!: list_all2_appendI)
        qed
        ultimately show ?thesis unfolding good_for_def by blast
      qed
      moreover have "(u, v) \<in> qrstep nfs \<Q>' (WDP R \<union> R)"
      proof -
        obtain C where C: "\<And>s. fill_holes (ccap u) (us\<^sub>1 @ s # us\<^sub>2) = C\<langle>s\<rangle>"
          using fill_holes_ctxt_main [of "ccap u" "us\<^sub>1" "us\<^sub>2"] by (auto simp: dmax_u dmax_s)
        have u: "u = fill_holes (ccap u) (dmax u)"
          by (metis fill_holes_cap_till_uncap_till_id)
        have "(u, v) \<in> qrstep nfs \<Q>' (WDP R)"
        proof (rule qrstepI [OF _ wdp, of \<sigma> \<Q>' u _ v nfs])
          show "\<forall>u \<lhd> \<sharp> l \<cdot> \<sigma>. u \<in> NF_terms \<Q>'"
            using args and \<open>funas_term (l \<cdot> \<sigma>) \<subseteq> \<F>\<close> by (force intro!: NF_terms_Q')
        next
          have "(\<Union>t \<in> set (dmax r). vars_term t) \<subseteq> vars_term r"
            by (induct r) auto
          then have *: "(\<Union>t \<in> set (dmax r). vars_term t) \<subseteq> vars_term l"
          using in_R [OF rule] and wf_R by (auto simp: wf_trs_def)
          then have "NF_subst nfs (\<sharp> l, q) \<sigma> \<Q>"
            using nfs and E by (auto simp: q NF_subst_def vars_defs)
          moreover have "\<Union>(funas_term ` \<sigma> ` vars_rule (\<sharp> l, q)) \<subseteq> \<F>"
            using E and * and \<open>funas_term (l \<cdot> \<sigma>) \<subseteq> \<F>\<close>
            by (auto simp add: vars_defs q funas_term_subst dest!: contra_subsetD iff: SUP_le_iff)
          ultimately show "NF_subst nfs (\<sharp> l, q) \<sigma> \<Q>'" by (intro NF_subst_Q') simp_all
        next
          have "u =\<^sub>f (ccap u, us\<^sub>1 @ \<sharp> l \<cdot> \<sigma> # us\<^sub>2)"
            using i and us_i
            apply (subst u)
            apply (auto simp: dmax_u dmax_s True)
            by (metis \<open>length us = length (dmax s)\<close> dmax_u eq_fill.intros i(1) id_take_nth_drop num_holes_cap_till us\<^sub>1_def us\<^sub>2_def)
          then show "u = C\<langle>\<sharp> l \<cdot> \<sigma>\<rangle>" using C [of "\<sharp> l \<cdot> \<sigma>"] by (auto dest: eqfE)
        next
          have "v =\<^sub>f (ccap u, us\<^sub>1 @ q \<cdot> \<sigma> # us\<^sub>2)"
            by (auto simp: v_def True dmax_s dmax_u)
          then show "v = C\<langle>q \<cdot> \<sigma>\<rangle>" using C [of "q \<cdot> \<sigma>"] by (auto dest: eqfE)
        qed
        then show ?thesis by blast
      qed
      ultimately show ?thesis by blast
    qed
  next
    assume us_i: "us ! i = D\<langle>l \<cdot> \<sigma>\<rangle>"
 
    have us': "us\<^sub>1 @ D\<langle>l \<cdot> \<sigma>\<rangle> # us\<^sub>2 = us"
      by (metis \<open>length us = length (dmax s)\<close> \<open>length us\<^sub>1 = i\<close> append_eq_conv_conj Cons_nth_drop_Suc i(1) us\<^sub>1_def us\<^sub>2_def us_i)

    have "i < length us" by (simp add: dmax_s)
    let ?D = "ccap (D\<langle>r \<cdot> \<sigma>\<rangle>)"
    let ?u = "dmax (D\<langle>r \<cdot> \<sigma>\<rangle>)"
    define G where "G = compose_mctxt (ccap u) i ?D"
    define v where "v = fill_holes G (us\<^sub>1 @ ?u @ us\<^sub>2)"

    have **: "fill_holes (ccap u) (us\<^sub>1 @ D\<langle>r \<cdot> \<sigma>\<rangle> # us\<^sub>2) =\<^sub>f (G, us\<^sub>1 @ ?u @ us\<^sub>2)"
    proof (unfold G_def, rule compose_mctxt_sound [OF _ split_term_eqf])
      show "fill_holes (ccap u) (us\<^sub>1 @ D\<langle>r \<cdot> \<sigma>\<rangle> # us\<^sub>2) =\<^sub>f (ccap u, us\<^sub>1 @ D\<langle>r \<cdot> \<sigma>\<rangle> # us\<^sub>2)"
        by (auto simp: dmax_u dmax_s)
    next
      show "i = length us\<^sub>1" by simp
    qed
    then have "v =\<^sub>f (G, us\<^sub>1 @ ?u @ us\<^sub>2)" by (auto simp: v_def dest: eqfE)
    moreover have "dmax t \<le>\<^sub>\<sharp> us\<^sub>1 @ ?u @ us\<^sub>2"
      using le_sharp by (auto simp: dmax_t intro!: list_all2_appendI)
    moreover have "ground_mctxt G" by (auto simp: G_def)
    moreover
    have "funas_mctxt G \<subseteq> \<C>"
      unfolding G_def
      unfolding funas_mctxt_compose_mctxt [of i "ccap u" ?D, unfolded num_holes_cap_till dmax_u, OF \<open>i < length us\<close>]
      using cap_till_funas [of "(- \<C>)" u] and cap_till_funas [of "(- \<C>)"]
      and funas_cap_till_subset [of "if_Fun_in_set (- \<C>)" "D\<langle>r \<cdot> \<sigma>\<rangle>"]
      and \<open>funas_term (D\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> \<F>\<close>
      by blast
    moreover
    have "(u, v) \<in> qrstep nfs \<Q>' (WDP R \<union> R)"
    proof -
      from fill_holes_ctxt_main [of "ccap u" us\<^sub>1 us\<^sub>2] obtain C
        where [simp]: "\<And>t. fill_holes (ccap u) (us\<^sub>1 @ t # us\<^sub>2) = C\<langle>t\<rangle>"
        using * by (auto simp: dmax_u)
      have "u = fill_holes (ccap u) (us\<^sub>1 @ D\<langle>l \<cdot> \<sigma>\<rangle> # us\<^sub>2)"
        using fill_holes_cap_till_uncap_till_id [of "if_Fun_in_set (- \<C>)" u]
        and us_i and i
        unfolding dmax_u by (simp add: us')
      then have "u = (C \<circ>\<^sub>c D)\<langle>l \<cdot> \<sigma>\<rangle>" by simp
      have "v = fill_holes (ccap u) (us\<^sub>1 @ D\<langle>r \<cdot> \<sigma>\<rangle> # us\<^sub>2)"
        using ** by (auto simp: v_def dest: eqfE)
      then have "v = (C \<circ>\<^sub>c D)\<langle>r \<cdot> \<sigma>\<rangle>" by simp
      have "(u, v) \<in> qrstep nfs \<Q>' R" by (rule qrstepI) fact+
      then show ?thesis by (metis UnI2 qrstep_union)
    qed
    moreover have "funas_term t \<subseteq> \<F>" by fact
    ultimately
    show ?thesis unfolding good_for_def by blast
  qed
qed

end

context
  fixes S W :: "('f, 'v) trs"
    and WDP_S :: "('f, 'v) trs"
    and WDP_W :: "('f, 'v) trs"
  assumes WDP_S: "\<forall>r \<in> S. \<exists>p \<in> WDP_S. is_WDP_of p r"
    and WDP_W: "\<forall>r \<in> W. \<exists>p \<in> WDP_W. is_WDP_of p r"
    and S: "S \<subseteq> \<R>"
    and W: "W \<subseteq> \<R>"
begin

lemma rel_qrsteps_good_for:
  assumes steps: "(s, t) \<in> (relto (qrstep nfs \<Q> S) (qrstep nfs \<Q> W)) ^^ n" (is "_ \<in> ?R ^^ n")
    and good: "s \<lless> u"
  shows "\<exists>v. t \<lless> v \<and> (u, v) \<in> (relto (qrstep nfs \<Q>' (WDP_S \<union> S)) (qrstep nfs \<Q>' (WDP_W \<union> W))) ^^ n"
  by (rule simulate_conditional_relative_steps_count[of "\<lambda> s t. s \<lless> t", 
    OF qrstep_good_for[OF WDP_S S] qrstep_good_for[OF WDP_W W] steps good])

lemma WDPs_sound:
  assumes bound: "deriv_bound_measure_class
    (relto (qrstep nfs \<Q>' (WDP_S \<union> S)) (qrstep nfs \<Q>' (WDP_W \<union> W)))
    (Runtime_Complexity C' D'') cc"
    and D': "set D' \<inter> \<C> = {}"
    and CD'_F: "set C' \<union> set D' \<subseteq> \<F>"
    and D'': "set D'' = \<sharp>(set D')"
  shows "deriv_bound_measure_class
    (relto (qrstep nfs \<Q> S) (qrstep nfs \<Q> W))
    (Runtime_Complexity C' D') cc"  
proof -
  let ?D = "relto (qrstep nfs \<Q>' (WDP_S \<union> S)) (qrstep nfs \<Q>' (WDP_W \<union> W))"
  let ?R = "relto (qrstep nfs \<Q> S) (qrstep nfs \<Q> W)"
  let ?T = "terms_of_nat (Runtime_Complexity C' D')"
  let ?TS = "terms_of_nat (Runtime_Complexity C' D'')"
  note d = deriv_bound_measure_class_def deriv_bound_rel_class_def
  note d' = deriv_bound_rel_def
  note d'' = deriv_bound_def
  from bound [unfolded d] obtain f where
    f: "f \<in> O_of cc" and bound: "deriv_bound_rel ?D ?TS f" by blast
  show ?thesis unfolding d
  proof (intro exI [of _ f] conjI [OF f], unfold d' d'', clarify)
    fix n s t
    assume sT: "s \<in> ?T n" and st: "(s, t) \<in> ?R ^^ Suc (f n)"
    from sT CD'_F have sF: "funas_term s \<subseteq> \<F>"
      by (cases s) (auto simp: funas_args_term_def)
    from relpow_Suc_E2 [OF st] obtain u where "(s, u) \<in> ?R" by metis
    then have "(s, u) \<in> (qrstep nfs \<Q> (S \<union> W))\<^sup>+" unfolding qrstep_union by regexp
    then obtain u where "(s, u) \<in> qrstep nfs \<Q> (S \<union> W)" by (induct, auto)
    with S W qrstep_all_mono [OF _ subset_refl, of "S \<union> W" \<R> \<Q> nfs nfs] 
    have su: "(s, u) \<in> qrstep nfs \<Q> \<R>" by auto
    from sT obtain g ss where [simp]: "s = Fun g ss" and "(g, length ss) \<in> set D'"
      by (cases s) simp_all
    then have *: "dmax s = [Fun g ss]" using D' by (auto)
    have ss: "\<sharp> s \<in> ?TS n"
      using sT by (cases s) (auto simp: D'' funas_args_term_def)
    have "s \<lless> \<sharp> s"
      unfolding good_for_def and *
      by (rule exI [of _ MHole], rule exI [of _ "[\<sharp> s]"], insert sF) auto
    from rel_qrsteps_good_for [OF st this] obtain v
      where "(\<sharp> s, v) \<in> ?D ^^ Suc (f n)" by auto
    from deriv_bound_steps [OF this bound [unfolded d', rule_format, OF ss]]
    show False by simp
  qed
qed

end

end

end
