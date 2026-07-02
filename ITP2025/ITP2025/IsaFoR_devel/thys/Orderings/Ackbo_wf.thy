(*
Author:  Alexander Lochmann <alexander.lochmann@uibk.ac.at> (2018)
License: LGPL (see file COPYING.LESSER)
*)
theory Ackbo_wf
  imports Ackbo
begin

context admissible_weight_fun_ac
begin

lemma bighead_smaller_sn:
  assumes "order_pair s_rel ns_rel"
    and "SN s_rel"
  shows "SN {(S,T). filtered_nless_rel_s S T h ns_rel s_rel}"
proof (rule ccontr)
  let ?cond = "\<lambda> S T. filtered_nless_rel_s S T h ns_rel s_rel"
  assume a:"\<not> SN {(S,T). ?cond  S T}"
  then obtain f where f: "\<And> n :: nat. ?cond (f n) (f (Suc n))" unfolding SN_defs by auto
  then have "\<And> n ::nat. (f n\<restriction>\<^sub>n h + f n\<restriction>\<^sub>v, (f (Suc n)\<restriction>\<^sub>n h + f (Suc n)\<restriction>\<^sub>v - f n\<restriction>\<^sub>v) + f n\<restriction>\<^sub>v) \<in> s_mul_ext ns_rel s_rel"
    using assms(1) order_pair.axioms(1) pre_order_pair.refl_NS s_ns_mul_ext_union_compat supseteq_imp_ns_mul_ext by fastforce 
  then have sn:"\<And> n ::nat. (f n\<restriction>\<^sub>n h + f n\<restriction>\<^sub>v,f (Suc n)\<restriction>\<^sub>n h + f (Suc n)\<restriction>\<^sub>v) \<in> s_mul_ext ns_rel s_rel"
    by (smt assms(1) diff_zero s_mul_ext_subset_trans subset_relation)
  let ?f = "\<lambda> x. f x\<restriction>\<^sub>n h + f x\<restriction>\<^sub>v"
  from SN_s_mul_ext[OF assms(1,2)] have "SN (s_mul_ext ns_rel s_rel)" by auto
  then show False
    using sn chain_imp_not_SN_on[of ?f "s_mul_ext ns_rel s_rel" 0]
    by (simp add: SN_def)
qed

lemma bighead_equal_dec_size_sn:
  shows "SN {(S,T). filtered_nless_rel_ns S T h ns s \<and> size S > size T}"
proof (rule ccontr)
  let ?cond = "\<lambda> S T. filtered_nless_rel_ns S T h ns s \<and> size S > size T"
  assume a:"\<not> SN {(S,T). ?cond  S T}"
  then obtain f where f: "\<And> n :: nat. ?cond (f n) (f (Suc n))" unfolding SN_defs by auto
  then have nt_sn:"(\<forall>i. (size (f i), size (f (Suc i))) \<in> {(g, l). l < g})" by blast
  from wf_imp_SN[of "{(g ::nat , l). g > l}"] have "SN {(g::nat , l). g > l}"
    using SN_nat_gt by blast
  then show False using nt_sn unfolding SN_on_def by auto
qed


lemma smallhead_sn:
  assumes "order_pair s ns"
    and "SN s"
  shows "SN {(S,T). filtered_nless_rel_ns S T h ns s \<and> size S = size T \<and> filtered_less_rel_s S T h ns s}"
proof (rule ccontr)
  let ?cond = "\<lambda> S T. filtered_nless_rel_ns S T h ns s \<and> size S = size T \<and> filtered_less_rel_s S T h ns s"
  assume a:"\<not> SN {(S,T). ?cond  S T}"
  then obtain f where f: "\<And> n :: nat. ?cond (f n) (f (Suc n))" unfolding SN_defs by auto
  from SN_s_mul_ext[OF assms(1,2)] have "SN (s_mul_ext ns s)" by auto
  then show False
    using f chain_imp_not_SN_on [of "\<lambda>x. filter_fun (f x) (\<lambda> x y. pr_strict y x) h" "s_mul_ext ns s", of 0]
    unfolding SN_on_def by auto
qed

lemma bighead_equal_smallhead_qc:
  assumes "order_pair s ns"
  shows "quasi_commute {(S,T). filtered_nless_rel_ns S T h ns s \<and> size S > size T}
                       {(S,T). filtered_nless_rel_ns S T h ns s \<and> size S = size T \<and>
                          filtered_less_rel_s S T h ns s}"
    (is "quasi_commute ?r ?s")
  unfolding quasi_commute_def
proof
  fix S U
  assume ass:"(S, U)\<in> ?s O ?r"
  then have "\<exists> t. (S, t) \<in> ?s \<and> (t, U) \<in> ?r" by auto
  then obtain T where "(S, T) \<in> ?s \<and> (T, U) \<in> ?r" by auto
  then have l:"(S \<restriction>\<^sub>n h, T \<restriction>\<^sub>n h + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s" and size: "size S = size T \<and> size T > size U" and
   r: "(T \<restriction>\<^sub>n h, U \<restriction>\<^sub>n h + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s"
    by auto
  then have "(S, U) \<in> ?r" using ns_ns_help_lemma[OF _ _ _ _ _ l r] assms(1)
    unfolding order_pair_def pre_order_pair_def compat_pair_def
    by (auto simp add: cl_lcl compatible_l_def compatible_r_def cr_lcr refl_on_def tr_ltr)
  then show "(S, U) \<in> (?r O (?r \<union> ?s)\<^sup>*)" by auto
qed

lemma bighead_big_equal_smallhead_qc:
  assumes "order_pair s ns"
  shows "quasi_commute {(S,T). filtered_nless_rel_s S T h ns s}
                       {(S,T). filtered_nless_rel_ns S T h ns s \<and> size S > size T \<or> filtered_nless_rel_ns S T h ns s \<and> size S = size T \<and> filtered_less_rel_s S T h ns s}"
    (is "quasi_commute ?r ?s")
  unfolding quasi_commute_def
proof
  fix S U
  assume ass:"(S, U)\<in> ?s O ?r"
  then have "\<exists> t. (S, t) \<in> ?s \<and> (t, U) \<in> ?r" by auto
  then obtain T where "(S, T) \<in> ?s \<and> (T, U) \<in> ?r" by auto
  then have l:"(S \<restriction>\<^sub>n h, T \<restriction>\<^sub>n h + (T \<restriction>\<^sub>v - S \<restriction>\<^sub>v)) \<in> ns_mul_ext ns s" and
   r: "(T \<restriction>\<^sub>n h, U \<restriction>\<^sub>n h + (U \<restriction>\<^sub>v - T \<restriction>\<^sub>v)) \<in> s_mul_ext ns s" by auto
  then have "(S, U) \<in> ?r" using assms(1) ns_s_help_lemma[OF _ _ _ _ _ l r]
    unfolding order_pair_def pre_order_pair_def compat_pair_def
    by (auto simp add: cl_lcl compatible_l_def compatible_r_def cr_lcr refl_on_def tr_ltr)
  then show "(S, U) \<in> (?r O (?r \<union> ?s)\<^sup>*)" by auto
qed

lemma bighead_equal_smallhead_sn:
  assumes "order_pair s ns"
    and "SN s"
  shows "SN ({(S,T). filtered_nless_rel_ns S T h ns s \<and> size S > size T} \<union>
           {(S,T). filtered_nless_rel_ns S T h ns s \<and> size S = size T \<and> filtered_less_rel_s S T h ns s})"
  using quasi_commute_imp_SN[OF bighead_equal_dec_size_sn smallhead_sn bighead_equal_smallhead_qc] assms by blast

lemma case3_filtered_rel_sn:
  assumes "order_pair s ns"
    and "SN s"
  shows "SN {(S, T). ac_case_filtered_rel S T h ns s}"
proof -
  from bighead_equal_smallhead_sn[OF assms, of h] have
    "SN ({(S, T). filtered_nless_rel_ns S T h ns s \<and> size T < size S \<or>
                filtered_nless_rel_ns S T h ns s \<and> size S = size T \<and> filtered_less_rel_s S T h ns s})" using old.prod.case
    by (simp add: SN_defs)
  from quasi_commute_imp_SN[OF bighead_smaller_sn this bighead_big_equal_smallhead_qc]
  show ?thesis using assms old.prod.case by (simp add: SN_defs ac_case_filtered_rel_def)
qed

lemma S_trans: "ackbo s t \<Longrightarrow> ackbo t u \<Longrightarrow> ackbo s u" using ackbo_trans by blast 
lemma NS_S_compat: "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> ackbo t u \<Longrightarrow> ackbo s u" using ackbo_compat_l by blast
lemma S_NS_compat: "ackbo s t \<Longrightarrow> (t, u) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> ackbo s u" using ackbo_compat_r by blast

lemma case3_SN:
  assumes "order_pair {(x :: ('f,'v) term,y). s_ord x y} {(x,y). ns_ord x y}"
  and "sym {(x,y). ns_ord x y}"
shows "SN {(s, t). (\<forall>u \<lhd> s. SN_on {(x,y). s_ord x y} {u}) \<and> root s = root t \<and> root t = Some (h, 2) \<and> h \<in> AC \<and>
           ac_case_filtered_rel (actop h s) (actop h t) (h, 2) {(x,y). ns_ord x y} {(x,y). s_ord x y}}"
    (is "SN {(s, t). ?cond s t }")
proof (rule ccontr)
  assume n:"\<not> ?thesis"
  let ?s_rel = "{(x ::('f,'v) term ,y). s_ord x y}"
  let ?ns_rel = "{(x ::('f,'v) term ,y). ns_ord x y}"
  let ?SN_sub = "\<lambda> s. \<forall>u \<lhd> s . SN_on ?s_rel {u}"
  let ?cas3 = "\<lambda> x y. root x = root y \<and> root y = Some (h, 2) \<and> h \<in> AC \<and>
        ac_case_filtered_rel (actop h x) (actop h y) (h, 2) {(x,y). ns_ord x y} {(x,y). s_ord x y}"
  from n obtain f where f: "\<And> n :: nat. ?cond (f n) (f (Suc n))" unfolding SN_defs by blast
  let ?sn_terms = "\<Union> {{s. s \<lhd> f n} | n. True}"
  let ?sn_ac_terms = "{s. (\<exists> t.  t \<in> ?sn_terms \<and> (s, t) \<in> ?ns_rel)}"
  let ?sn_rel = "{(s,t). s \<in> ?sn_ac_terms \<and> s_ord s t}"
  have trans_ns: "trans ?ns_rel" using assms order_pair.axioms(1) pre_order_pair_def by blast 
  have refl_ns: "refl ?ns_rel" using assms order_pair.axioms(1) pre_order_pair_def by blast
  from f have cas3: "\<And> n :: nat. ?cas3 (f n) (f (Suc n))" by blast
  from f have sn_sub: "\<And> n :: nat. ?SN_sub (f n)" by blast
  have "SN_on ?s_rel ?sn_ac_terms"
  proof (rule ccontr)
    assume ass:"\<not> SN_on ?s_rel ?sn_ac_terms"
    then obtain g where g: "\<And> n :: nat. g 0 \<in> ?sn_ac_terms \<and> s_ord (g n) (g (Suc n))" unfolding SN_defs by blast
    then have w:"\<exists> n. g 0 \<in> {s. \<exists> t. t \<lhd> f n \<and> (s, t) \<in> ?ns_rel}" by blast
    from chain_imp_not_SN_on[of g ?s_rel 0] have nt_sn: "\<not> SN_on ?s_rel {g 0}" using g by blast
    have "\<exists> n t. t \<lhd> f n \<and> (t, g 0) \<in> ?ns_rel" using w assms(2) by (smt mem_Collect_eq symE)
    then obtain n t where t_sub: "t \<lhd> f n" and ns: "(t, g 0) \<in> ?ns_rel" by blast
    then have r_ns: "(t, g 0) \<in> (?s_rel \<union> ?ns_rel)\<^sup>*" by blast
    from t_sub sn_sub have "SN_on (?ns_rel\<^sup>* O ?s_rel O ?ns_rel\<^sup>*) {t}"
      by (metis assms(1) compat_pair.S_O_rtrancl_NS(1) compat_pair.rtrancl_NS_O_S(2) order_pair_def)
    from steps_preserve_SN_on_relto[OF r_ns this]
    show False using nt_sn by (metis assms(1) compat_pair.S_O_rtrancl_NS(1) compat_pair.rtrancl_NS_O_S(2) order_pair_def) 
  qed
  then have sn_rel:"SN {(s,t). s \<in> ?sn_ac_terms \<and> s_ord s t}" by (smt SN_defs case_prodD case_prodI mem_Collect_eq)
  obtain g where f_h: "\<exists> us .(f 0) = Fun g us \<and> length us = 2" and ac: "g \<in> AC" and eq: "h = g"
    using cas3 by (metis prod.sel(1, 2) root_Some) 
  have head: "\<And> n. \<exists> us .(f n) = Fun g us \<and> length us = 2" using f_h  by (metis cas3 root_Some term.inject(2))
  let ?Flat = "\<lambda> t. actop g t"
  let ?cond_2 = "\<lambda> s t. ac_case_filtered_rel (?Flat s) (?Flat t) (h,2) ?ns_rel ?sn_rel"
  let ?cond2_rel = "{(S,T). ac_case_filtered_rel S T (h, 2) ?ns_rel ?sn_rel}"
  {
    fix n ::nat
    have rec_act: "actop h (f n) \<noteq> {#f n#}" using head[of n] Bin_cases[of "f n"]
      apply (cases rule:actop.cases) apply (auto simp add: eq)
      by (metis (no_types, lifting) length_0_conv length_Suc_conv numeral_2_eq_2)  
    then have flat_sub: "\<And> x. x \<in># actop h (f n) \<Longrightarrow> f n \<rhd> x" using actop_impl_subterm by fastforce 
    {fix s t
      assume a1: "s \<in># actop h (f n)"
      assume a2: "t \<in># actop h (f (Suc n))"
      from a1 have "f n \<rhd> s" "ns_ord s s" using flat_sub assms(1) refl_onD
        unfolding order_pair_def pre_order_pair_def by fastforce+
      then have "s \<in> {s. \<exists>t. t \<in> \<Union>{{s. f n \<rhd> s} |n. True} \<and> (s, t) \<in> {(x, y). ns_ord x y}}" by auto
      then have "(s, t) \<in> ?s_rel \<longrightarrow> (s, t) \<in> ?sn_rel" by blast}
    then have "?cond_2 (f n) (f (Suc n))" using cas3[of n]
        eq ac_case_filtered_rel_cong[of "actop h (f n)" "actop h (f n)" "actop h (f (Suc n))" "actop h (f (Suc n))"
          "{(x, y). s_ord x y}" ?sn_rel] by fastforce}
  from this chain_imp_not_SN_on[of "\<lambda> i. actop h (f i)" ?cond2_rel]
  have "\<not> SN_on ?cond2_rel {actop h (f 0)}" by (auto simp add: eq)
  then have nt_sn:"\<not> SN ?cond2_rel" unfolding SN_def by blast
  have "order_pair ?sn_rel ?ns_rel"
  proof
    show "refl ?ns_rel" using refl_ns by auto
    show "trans ?ns_rel" using trans_ns by auto
    show "trans ?sn_rel" unfolding trans using assms
      by (smt case_prodD case_prodI mem_Collect_eq order_pair.axioms(1) pre_order_pair_def trans_def) 
    {
      fix s u t
      assume a:"(s, t) \<in> ?ns_rel \<and> (t, u) \<in> ?sn_rel"
      then have "(s, u) \<in> ?s_rel" using order_pair.axioms[OF assms(1)] unfolding compat_pair_def by blast 
      then have "(s, u) \<in> ?sn_rel" using a by (smt case_prodD case_prodI mem_Collect_eq trans_def trans_ns) 
    }
    then show "?ns_rel O ?sn_rel \<subseteq> ?sn_rel" by (smt relcompE subrelI)
    show "?sn_rel O ?ns_rel \<subseteq> ?sn_rel"
      using order_pair.axioms[OF assms(1)] unfolding compat_pair_def by blast
  qed
  from case3_filtered_rel_sn[OF this sn_rel] nt_sn show False unfolding SN_on_def by blast
qed


lemma ackbo_strongly_normalizing:
  fixes s :: "('f, 'v) term" 
  shows "SN_on {(s, t). ackbo s t} {s}"
proof -
  let ?SN = "\<lambda> t :: ('f,'v)term. SN_on {(s,t). ackbo s t} {t}"
  let ?ac_rel = "(acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
  let ?m1 = "\<lambda> (f,ss). weight (Fun f ss)"
  let ?m2 = "\<lambda> (f,ss). (f,length ss)"
  let ?rel' = "lex_two {(fss,gts). ?m1 fss > ?m1 gts} {(fss,gts). ?m1 fss \<ge> ?m1 gts} {(fss,gts). pr_strict (?m2 fss) (?m2 gts)}"
  let ?rel = "inv_image ?rel' (\<lambda> x. (x,x))"
  have SN_rel: "SN ?rel"
    by (rule SN_inv_image, rule lex_two, insert SN_inv_image[OF pr_SN, of ?m2]  SN_inv_image[OF SN_nat_gt, of ?m1],
        auto simp: inv_image_def)
  note conv = SN_on_all_reducts_SN_on_conv
  show "?SN s"
  proof (induct s rule: subterm_induct)
    case (subterm s)
    then show ?case
    proof (cases "is_Var s")
      case True
      then show ?thesis
        by (metis Product_Type.Collect_case_prodD ackbo_lhs_var_false prod.sel(1) step_reflects_SN_on) 
    next
      case False
      then obtain f ss where term_s: "s = Fun f ss" by blast
      then have subset: "{x. (Fun f ss) \<rhd> x} \<subseteq> {s. ?SN s}" using subterm by blast
      let ?P = "\<lambda> (f,ss). {x. (Fun f ss) \<rhd> x} \<subseteq> {s. ?SN s} \<longrightarrow> ?SN (Fun f ss)"
      {
        fix fss
        have "?P fss"
        proof (induct fss rule: SN_induct[OF SN_rel])
          case (1 fss)
          obtain f ss where fss: "fss = (f,ss)" by force
          {
            fix g ts
            assume "?m1 (f,ss) > ?m1 (g,ts) \<or> ?m1 (f,ss) \<ge> ?m1 (g,ts) \<and> pr_strict (?m2 (f,ss)) (?m2 (g,ts))"
              and "{x. (Fun g ts) \<rhd> x} \<subseteq> {s. ?SN s}"
            then have "?SN (Fun g ts)"
              using 1[rule_format, of "(g,ts)", unfolded fss split]  by auto
          } note IH = this[unfolded split]
          thm IH
          show ?case unfolding fss split
          proof
            assume SN_s: "{x. (Fun f ss) \<rhd> x} \<subseteq> {s. ?SN s}"
            let ?f = "(f,length ss)"
            let ?s = "Fun f ss"
            let ?SNt = "\<lambda> g ts. ?SN (Fun g ts)"
            let ?sym = "\<lambda> g ts. (g,length ts)"
            let ?ack = "\<lambda> l r. (ackbo l r, (l,r) \<in> ?ac_rel)"
            let ?lex = "lex_ext ?ack (weight ?s)"
            let ?lexu = "lex_ext_unbounded ?ack"
            let ?lex_SN = "{(ys, xs). (\<forall> y \<in> set ys. ?SN y) \<and> fst (?lex ys xs)}"
            from lex_ext_SN[of ?ack "weight ?s"]
            have SN: "SN ?lex_SN" using NS_S_compat by auto
            {
              fix g and ts :: "('f,'v)term list"
              assume "(g \<notin> AC \<or> length ts \<noteq> 2) \<and> (pr_strict ?f (?sym g ts) \<or> ?f = (?sym g ts)) \<and> weight (Fun g ts) \<le> weight ?s \<and> {x. Fun g ts \<rhd> x} \<subseteq> {s. ?SN s}"
              hence "?SNt g ts"
              proof (induct ts arbitrary: g rule: SN_induct[OF SN])
                case (1 ts g)
                note inner_IH = 1(1)
                let ?g = "(g,length ts)"
                let ?t = "Fun g ts"
                from 1(2) have fg: "pr_strict ?f ?g \<or> ?f = ?g" and not_ac: "g \<notin> AC \<or> length ts \<noteq> 2" and w: "weight ?t \<le> weight ?s" and 
                  SN: "{x. Fun g ts \<rhd> x} \<subseteq> {s. ?SN s}" by auto
                show "?SNt g ts" unfolding conv[of _ ?t]
                proof (intro allI impI)
                  fix u
                  assume "(?t,u) \<in> {(s,t). ackbo s t}"
                  hence tu: "ackbo ?t u" by auto
                  then show "?SN u"
                  proof (induct u rule:subterm_induct)
                    case (subterm u)
                    then show ?case
                    proof (cases "is_Var u")
                      case True
                      then show ?thesis
                         by (metis Product_Type.Collect_case_prodD ackbo_lhs_var_false prod.sel(1) step_reflects_SN_on) 
                     next
                      case False
                      then obtain h us where term_u: "u = Fun h us" by blast
                      let ?h = "(h,length us)"
                      let ?u = "Fun h us"
                      have "ackbo ?t ?u" using subterm(2) unfolding term_u by simp 
                      note tu = this
                      {
                        fix sub
                        assume u: "?u \<rhd> sub"
                        then have "ackbo ?u sub" by (simp add: ackbo_subterm_property) 
                        then have "ackbo ?t sub" using tu S_trans by auto
                        then have "?SN sub" using subterm u term_u by blast
                      } 
                      then have SNu: "{x. Fun h us \<rhd> x} \<subseteq> {s . ?SN s}" by blast
                      note IH = IH[OF _ this]
                      from tu have wut: "weight ?u \<le> weight ?t" using ackbo_weight_eq by fastforce 
                      show ?thesis
                      proof (cases "?m1 (f,ss) > ?m1 (h,us) \<or> ?m1 (f,ss) \<ge> ?m1 (h,us) \<and> pr_strict (?m2 (f,ss)) (?m2 (h,us))")
                        case True
                        from IH[OF True[unfolded split]] show ?thesis using term_u by simp
                      next
                        case False
                        with wut w have wut: "weight ?t = weight ?u" "weight ?s = weight ?u" by auto
                        note False = False[unfolded split wut]
                        note tu = tu[unfolded ackbo.simps[of ?t] wut, unfolded term.simps, simplified]
                        from tu have gh: "pr_strict ?g ?h \<or> ?g = ?h"
                          using ackbo_no_var_impl_prstrict_or_eq_root subterm.prems term_u wut(1) by blast 
                        from False wut have "\<not> pr_strict ?f ?h" by blast
                        from this have gh2: "\<not> pr_strict ?g ?h" using gh by (metis "1.prems" pr_trans)
                        from not_ac tu gh2 have lex: "fst (?lexu ts us)"
                          by (smt False lex_ext_def weight.simps(2) wut(1))
                        have "(h \<notin> AC \<or> length us \<noteq> 2) \<and> (pr_strict (f, length ss) (h, length us) \<or> ?f = ?h) \<and> weight ?u \<le> weight ?s \<and> {x. Fun h us \<rhd> x} \<subseteq> {s. ?SN s}"
                          using wut SNu not_ac gh gh2  "1.prems" by auto
                        note inner_IH = inner_IH[of us h, OF _ this]
                        show ?thesis unfolding term_u
                        proof (rule inner_IH, rule, unfold split, intro conjI ballI)
                          have "fst (?lexu ts us)" by (rule lex)
                          moreover have "length us \<le> weight ?s"
                          proof -
                            have "length us \<le> sum_list (map weight us)" 
                            proof (induct us)
                              case (Cons a us)
                              have "w0 \<le> weight a \<and> 1 \<le> w0" using weight_w0 Suc_leI[OF w0(2)] by auto 
                              then show ?case using Cons w0(2) weight_w0 by auto
                            qed simp
                            then show ?thesis using wut(2) by simp
                          qed                          
                          ultimately show "fst (?lex ts us)" unfolding lex_ext_def Let_def by auto
                        next
                          fix t
                          assume t: "t \<in> set ts" 
                          with SN show "?SN t" by blast
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            }
            note partA = this
            let ?mul_SN = "{(s, t). (\<forall> u. s \<rhd> u \<longrightarrow> ?SN u) \<and> root s = root t \<and> root t = Some (f, 2) \<and> f \<in> AC \<and>
                 ac_case_filtered_rel (actop f s) (actop f t) (f, 2) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y}}"
            have SN: "SN ?mul_SN" using case3_SN[of ackbo "(\<lambda> x y. (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"]
              ackbo_order_pair by (simp add: conversion_sym)
            {
              fix g and ts :: "('f,'v)term list"
              assume "g \<in> AC \<and> length ts = 2 \<and> (pr_strict ?f (?sym g ts) \<or> ?f = (?sym g ts)) \<and>
                 weight (Fun g ts) \<le> weight ?s \<and> {x. Fun g ts \<rhd> x} \<subseteq> {s. ?SN s}"
              hence "?SNt g ts"
              proof (induct "Fun g ts" arbitrary: g ts rule: SN_induct[OF SN])
                case (1 g ts)
                note inner_IH = 1(1)
                let ?g = "(g,length ts)"
                let ?t = "Fun g ts"
                from 1(2) have fg: "(pr_strict ?f ?g \<or> ?f = ?g)" and w: "weight ?t \<le> weight ?s" and ac: "g \<in> AC \<and> length ts = 2" and
                  SN: "{x. Fun g ts \<rhd> x} \<subseteq> {s. ?SN s}" by auto
                show "?SNt g ts" unfolding conv[of _ ?t]
                proof (intro allI impI)
                  fix u
                  assume "(?t,u) \<in> {(s,t). ackbo s t}"
                  hence tu: "ackbo ?t u" by auto
                  then show "?SN u"
                  proof (induct u rule:subterm_induct)
                    case (subterm u)
                    then show ?case
                    proof (cases "is_Var u")
                      case True
                      then show ?thesis
                        by (metis Product_Type.Collect_case_prodD admissible_weight_fun_ac.ackbo_lhs_var_false admissible_weight_fun_ac_axioms fst_conv step_reflects_SN_on)
                    next
                      case False
                      then obtain h us where term_u: "u = Fun h us" by blast
                      let ?h = "(h,length us)"
                      let ?u = "Fun h us"
                      have "ackbo ?t ?u" using subterm(2) unfolding term_u by simp 
                      note tu = this
                      {
                        fix sub
                        assume u: "?u \<rhd> sub"
                        then have "ackbo ?u sub" by (simp add: ackbo_subterm_property) 
                        then have "ackbo ?t sub" using tu S_trans by auto
                        then have "?SN sub" using subterm u term_u by blast
                      } 
                      then have SNu: "{x. Fun h us \<rhd> x} \<subseteq> {s . ?SN s}" by blast
                      note IH = IH[OF _ this]
                      from tu have wut: "weight ?u \<le> weight ?t" using ackbo_weight_eq by fastforce 
                      show ?thesis
                      proof (cases "?m1 (f,ss) > ?m1 (h,us) \<or> ?m1 (f,ss) \<ge> ?m1 (h,us) \<and> pr_strict (?m2 (f,ss)) (?m2 (h,us))")
                        case True
                        from IH[OF True[unfolded split]] show ?thesis using term_u by simp
                      next
                        case False
                        with wut w have wut: "weight ?t = weight ?u" "weight ?s = weight ?u" by auto
                        note False = False[unfolded split wut]
                        note tu = tu[unfolded ackbo.simps[of ?t] wut, unfolded term.simps, simplified]
                        from tu have gh: "pr_strict ?g ?h \<or> ?g = ?h"
                          using ackbo_no_var_impl_prstrict_or_eq_root subterm.prems term_u wut(1) by blast 
                        from False wut have "\<not> pr_strict ?f ?h" by blast
                        from this have gh2: "\<not> pr_strict ?g ?h" using gh by (metis "1.prems" pr_trans)
                        from ac tu gh2 have cas3: "ac_case_filtered_rel (actop f  (Fun g ts)) (actop f (Fun h us)) (f, 2) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y}"
                          using "1.prems" \<open>\<not> pr_strict (f, length ss) (h, length us)\<close> wut(1) by auto                
                        have "h \<in> AC \<and> length us = 2 \<and> (pr_strict (f, length ss) (h, length us) \<or> ?f = ?h) \<and> weight ?u \<le> weight ?s \<and> {x. Fun h us \<rhd> x} \<subseteq> {s. ?SN s}"
                          using wut SNu ac gh gh2  "1.prems" by auto
                        note inner_IH = inner_IH[of h us, OF _ this]
                        show ?thesis unfolding term_u
                        proof (rule inner_IH, rule, unfold split, rule conjI ballI)
                          {
                            fix t
                            assume t: "t \<lhd> Fun g ts" 
                            with SN have "?SN t" by blast
                          }
                          then show "\<forall>u \<lhd> Fun g ts. SN_on {(x, y). ackbo x y} {u}" by blast
                        next
                          show "root (Fun g ts) = root (Fun h us) \<and> root (Fun h us) = Some (f, 2) \<and>  f \<in> AC \<and>
                           ac_case_filtered_rel (actop f  (Fun g ts)) (actop f (Fun h us)) (f, 2) ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) {(x,y). ackbo x y}" using cas3
                            using \<open>\<not> pr_strict (f, length ss) (h, length us)\<close> \<open>h \<in> AC \<and> length us = 2 \<and> (pr_strict (f, length ss) (h, length us) \<or> (f, length ss) = (h, length us)) \<and> weight (Fun h us) \<le> weight (Fun f ss) \<and> {x. Fun h us \<rhd> x} \<subseteq> {s. SN_on {(x, y). ackbo x y} {s}}\<close> gh gh2 by auto
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            }
            from this partA SN_s show "?SN ?s" by auto
          qed
        qed
      }
      then show ?thesis using term_s subterm by blast
    qed
  qed
qed

lemma ackbo_sn:
  shows "SN {(s, t). ackbo s t}"
  using ackbo_strongly_normalizing unfolding SN_def by blast

end

end
