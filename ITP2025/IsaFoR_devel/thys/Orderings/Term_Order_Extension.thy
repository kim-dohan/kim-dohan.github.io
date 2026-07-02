(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Term_Order_Extension
  imports
    Term_Order
    TRS.Signature_Extension
    Argument_Filter
    RPO_More
    Reduction_Pair
begin

lift_definition only_unary_afs :: "('f \<times> nat) set \<Rightarrow> 'f afs" is
  "\<lambda> F. ((\<lambda> (f :: 'f, n). if n = 0 then AFList [] else 
     if (f,n) \<in> F then Collapse 0 else AFList [0 ..< n]), UNIV)"
  by auto

lemma only_unary_afs: "afs (only_unary_afs F) =
  (\<lambda> (f :: 'f, n). if n = 0 then AFList [] else 
     if (f,n) \<in> F then Collapse 0 else AFList [0 ..< n])"
  by (transfer, auto)

context redtriple_order
begin

lemma sig_mono_imp_SN_rel:
  fixes R Rw :: "('f, 'v) trs"
  assumes sig_mono:
    "\<And> s t f bef aft. \<lbrakk>(s, t) \<in> S; (f, Suc (length bef + length aft)) \<in> F\<rbrakk> \<Longrightarrow>
    (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> S"
    and orient: "R \<subseteq> S" "Rw \<subseteq> NS"
    and var_cond: "\<And> l r. (l, r) \<in> NS \<inter> Rw \<Longrightarrow> vars_term r \<subseteq> vars_term l" 
    and F: "funas_trs R \<subseteq> F" "funas_trs Rw \<subseteq> F"
  shows "SN_rel (rstep R) (rstep Rw)"
proof -
  let ?R = "rstep R"
  let ?FR = "sig_step F ?R"
  let ?S = "rstep Rw"
  let ?FS = "sig_step F ?S"
  have S: "?FR \<subseteq> S"
  proof
    fix s t
    assume st: "(s, t) \<in> ?FR"
    then have st: "(s, t) \<in> ?R" and sF: "funas_term s \<subseteq> F" and tF: "funas_term t \<subseteq> F" using sig_stepE[OF st] by auto
    from st obtain C l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
    from orient lr have lr: "(l, r) \<in> S" by auto
    from subst.closedD[OF subst_S lr] have gt: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> S" .
    from sF[unfolded s] have "funas_ctxt C \<subseteq> F" by auto
    then have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> S"
    proof (induction C)
      case Hole
      show ?case using gt by simp
    next
      case (More f bef C aft)
      from More.prems have C: "funas_ctxt C \<subseteq> F" and f: "(f, Suc (length bef + length aft)) \<in> F" by auto
      from sig_mono[OF More.IH[OF C] f] show ?case by simp
    qed
    then show st: "(s, t) \<in> S" unfolding s t .
  qed
  from rstep_subset[OF ctxt_NS subst_NS orient(2)]
    have NS: "?S \<subseteq> NS" .
  then have NS_sig: "?FS \<subseteq> NS" by auto
  from relto_mono[OF S NS_sig]
    have subset: "relto (?FR) (?FS) \<subseteq> S" by (simp add: order_simps)
  have "SN (relto (?FR) (?FS))"
    by (rule SN_subset[OF SN subset])
  then have relSN: "SN_rel (?FR) (?FS)" unfolding SN_rel_defs .
  {
    fix l r
    assume lr: "(l, r) \<in> Rw"
    with orient have "(l, r) \<in> NS \<inter> Rw" by auto
    from var_cond[OF this] 
    have "vars_term r \<subseteq> vars_term l" .
  } note var_cond = this
  show ?thesis        
    by (rule sig_ext_relative_rewriting_var_cond[OF var_cond F relSN])
qed

lemma manna_ness_relative:
  assumes orient: "R \<subseteq> S" "Rw \<subseteq> NS"
    and mono: "ctxt.closed S"
  shows "SN_rel (rstep R) (rstep Rw)"
proof -
  from rstep_subset[OF ctxt_NS subst_NS orient(2)] have NS: "rstep Rw \<subseteq> NS" .
  from rstep_subset[OF mono subst_S orient(1)] have S: "rstep R \<subseteq> S" .
  from SN_subset[OF SN relto_mono[OF S NS, unfolded order_simps]]
  show ?thesis unfolding SN_rel_defs .
qed

lemma sig_mono_imp_SN_rel_subterm: 
  assumes sig_mono:
    "\<And> s t f bef aft. \<lbrakk>(s, t) \<in> S; (f, Suc (length bef + length aft)) \<in> F\<rbrakk> \<Longrightarrow>
    (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> S"
    and F_unary: "\<And> fn. fn \<in> F \<Longrightarrow> snd fn \<le> Suc 0"
    and orient: "R \<subseteq> S" "Rw \<subseteq> NS"
    and var_cond: "\<And> l r. (l, r) \<in> NS \<inter> Rw \<Longrightarrow> vars_term r \<subseteq> vars_term l" 
    and F: "funas_trs R \<subseteq> F" "funas_trs Rw \<subseteq> F"
    and ST: "ST \<subseteq> {(Fun f ts, t) | f ts t. t \<in> set ts \<and> (f,length ts) \<notin> F}" 
  shows "SN_rel (rstep (R \<union> ST)) (rstep (Rw \<union> ST))"
proof -
  let ?c = ST
  from sig_mono_imp_SN_rel[OF sig_mono orient var_cond F]
    have SN_rel_R_Rw: "SN_rel (rstep R) (rstep Rw)" .
  then have SN: "SN_qrel (False, {}, R, Rw)" unfolding SN_qrel_def by simp
  have "SN_qrel (False, {}, R \<union> ?c, Rw \<union> ?c)"
  proof (rule SN_qrel_split[where D = ?c])
    show "SN_qrel (False, {}, R \<union> ?c - ?c, Rw \<union> ?c - ?c)"
      by (rule SN_qrel_mono[OF _ _ _ SN], auto)
  next
    show "SN_qrel (False, {}, ?c \<inter> (R \<union> ?c \<union> (Rw \<union> ?c)), R \<union> ?c \<union> (Rw \<union> ?c) - ?c)"
    proof (rule SN_qrel_mono[where Q = "{}" and Q' = "{}"], unfold SN_qrel_def split qrstep_rstep_conv)
      obtain prc :: "'f filtered \<times> nat \<Rightarrow> nat" where prc: "prc = (\<lambda> _ . 0)"  by auto
      obtain c :: "'f filtered \<times> nat \<Rightarrow> order_tag" where c: "c = (\<lambda> _ . Lex)" by auto
      obtain n :: nat where True by auto
      interpret rpo_with_assms "prc_nat prc" "prl_nat prc" c n ..
      let ?af = "only_unary_afs F"
      let ?S = "RPO_S prc c n"
      let ?NS = "RPO_NS prc c n"
      interpret mono_ce_af_redtriple ?S ?NS ?NS full_af ..
      interpret afs_redtriple ?af ?S ?NS ?NS ..
      let ?pi = "afs_rel ?af"
      show "SN_rel (rstep ?c) (rstep (R \<union> Rw))" 
      proof (rule manna_ness_relative[OF _ _ ctxt_closed[OF _ rpo_pr_prc.RPO_S_pr_ctxt_closed]]) 
        show "mono_afs ?af" unfolding mono_afs_def using F_unary
          by (auto simp: only_unary_afs)
        show "?c \<subseteq> ?pi ?S"
        proof
          fix s t
          assume st: "(s, t) \<in> ?c"
          with ST obtain f ts where s: "s = Fun f ts" and t: "t \<in> set ts" and f: "(f,length ts) \<notin> F" by auto
          show "(s, t) \<in> ?pi ?S" unfolding afs_rel_def
          proof(rule, rule exI, rule conjI[OF refl]) 
            let ?s = "afs_term ?af s"
            let ?t = "afs_term ?af t"
            have pi: "afs ?af (f, length ts) = AFList [0 ..< length ts]"
              using f by (auto simp: only_unary_afs)
            have "?t \<in> set (args ?s)" unfolding s using t[unfolded set_conv_nth]
              by (force simp: Let_def pi) 
            then have "?s \<rhd> ?t" by (cases ?s, auto)
            from rpo_pr_prc.supt_imp_rpo_stri[OF this, of prc c n]
            have "(?s, ?t) \<in> ?S" unfolding rpo_pr_prc.RPO_S_pr_def by auto
            then show "afs_rule ?af (s, t) \<in> ?S"
              unfolding afs_rule_def fst_conv snd_conv .
          qed
        qed
        show "R \<union> Rw \<subseteq> ?pi ?NS"
        proof
          fix l r
          assume lr: "(l, r) \<in> R \<union> Rw"
          with F have F: "funas_term l \<subseteq> F" "funas_term r \<subseteq> F"
            unfolding funas_trs_def funas_rule_def [abs_def] by force+
          from SN_rel_imp_wf_reltrs[OF SN_rel_R_Rw]
          have "wf_reltrs (R) (Rw)" .
          with var_cond[of l r] lr orient(2) have vars: "vars_term r \<subseteq> vars_term l"
            unfolding wf_reltrs.simps wf_trs_def by auto
          let ?pi = "afs_term ?af"
          { fix t :: "('f, 'v) term" and x
            assume "funas_term t \<subseteq> F" and "x \<in> vars_term t"
            then have "?pi t = Var x"
            proof (induction t)
              case (Var y)
              then show ?case by simp
            next
              case (Fun f ts)
              from Fun.prems(1) have f: "(f, length ts) \<in> F" by auto
              from F_unary[OF this] obtain t where ts: "ts = [t]"
                using Fun.prems(2) by (cases ts, auto)
              from Fun.prems[unfolded ts] have F: "funas_term t \<subseteq> F"
                and x: "x \<in> vars_term t" by auto
              from Fun.IH[OF _ F x] f show ?case unfolding ts 
                by (auto simp: only_unary_afs)
            qed }
          note var = this
          have "(?pi l, ?pi r) \<in> ?NS"
          proof (cases "vars_term r = {}")
            case False
            then obtain x where xr: "x \<in> vars_term r" by auto
            with vars have xl: "x \<in> vars_term l" by auto
            show ?thesis
              unfolding var[OF F(1) xl] var[OF F(2) xr]
              by (rule rpo_pr_prc.RPO_refl)
          next
            case True
            with F(2) have "\<exists> c. ?pi r = Fun c []"
            proof (induction r)
              case (Fun f ts)
              from Fun.prems(1) have f: "(f, length ts) \<in> F" by auto
              from F_unary[OF this] obtain t where ts: "ts = [t] \<or> ts = []"
                using Fun.prems(2) by (cases ts, auto)
              then show ?case
              proof
                assume ts: "ts = [t]"
                from Fun.prems[unfolded ts] have F: "funas_term t \<subseteq> F"
                  and vars: "vars_term t = {}" by auto
                from Fun.IH[OF _ F vars] f show ?case unfolding ts 
                  by (simp add: only_unary_afs)
              next
                assume ts: "ts = []"
                show ?case unfolding ts 
                  by (simp add: only_unary_afs)
              qed
            qed auto
            then obtain f where pir: "?pi r = Fun f []" by auto
            have f: "prl_nat prc (f,0)" unfolding prc prl_nat_def by simp
            show ?thesis unfolding pir 
              using rpo_pr_prc.RPO_least_1[OF f]
              by (cases "?pi l", auto)
          qed
          then show "(l, r) \<in> afs_rel ?af ?NS" 
            unfolding afs_rel_def afs_rule_def by auto
        qed
      qed
    qed auto
  qed
  then show ?thesis unfolding SN_qrel_def by simp
qed

end

lemma ce_SN_rel_imp_redtriple:
  fixes R Rw :: "('f, 'v) trs"
  assumes SN_rel: "SN_rel (rstep R) (rstep Rw)"
    and ce: "\<Union>(ce_trs ` UNIV) \<subseteq> R \<inter> Rw"
    and pi: "\<And> f n. pi (f, n) = {0 ..< n}"
  shows "mono_ce_af_redtriple_order ((relto (rstep R) (rstep Rw))\<^sup>+) ((rstep R \<union> rstep Rw)\<^sup>*) ((rstep R \<union> rstep Rw)\<^sup>*) pi"
proof -
  let ?R = "relto (rstep R) (rstep Rw)"
  let ?Rw = "rstep R \<union> rstep Rw"
  from SN_rel have SN: "SN (?R^+)" unfolding SN_rel_defs
    by (rule SN_imp_SN_trancl)
  note conv = relto_trancl_conv
  note subst = subst.closed_rtrancl subst.closed_Un subst.closed_comp subst_closed_rstep
  let ?ce = "\<Union>(range ce_trs) :: ('f, 'v)trs"
  from ce have "?ce \<subseteq> rstep R \<inter> rstep Rw" by auto
  also have "... \<subseteq> ?R^+ \<inter> ?Rw^*" unfolding conv by auto
  finally have ce: "?ce \<subseteq> ?R^+ \<inter> ?Rw^*" .
  {
    fix c d m
    have "ce_trs (c, m) \<subseteq> ?ce" by auto
    also have "... \<subseteq> ?R^+ \<inter> ?Rw^*" by (rule ce)
    finally have "ce_trs (c, m) \<subseteq> ?R^+ \<inter> ?Rw^*" .
  } 
  hence ce: "ce_compatible (?R^+)" "ce_compatible (?Rw^*)" 
    unfolding ce_compatible_def by blast+
  show ?thesis
  proof(unfold_locales)
    show "SN (?R^+)" by (rule SN)
    show "ctxt.closed (?Rw^*)" by blast
    show "ctxt.closed (?R^+)" by blast
    show "subst.closed (?R^+)" unfolding conv by (blast)
    show "subst.closed (?Rw^*)" by (blast)
    show "refl (?Rw^*)" by (auto intro: refl_rtrancl)
    show "trans (?Rw^*)" by (auto intro: trans_rtrancl)
    show "?Rw^* O ?R^+ \<subseteq> ?R^+" unfolding conv by regexp
    show "af_compatible pi (?Rw^*)" unfolding af_compatible_def  using pi by auto
    have "?R^+ O ?R^+ \<subseteq> ?R^+" unfolding conv by regexp
    show "?R^+ \<subseteq> ?Rw^*" by regexp 
  qed (insert ce)
qed

end
