(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Innermost_Switch
imports
  TRS.QDP_Framework
  First_Order_Rewriting.Critical_Pairs
  TRS.DP_Transformation
  Sem_Lab.Labelings
  Auxx.Name
begin

(* it might be tempting to require just WCR (rstep R) instead
   of WCR (qrstep nfs Q R), since then one can use standard 
   joinability of critical pairs to show WCR (rstep R).
   However, this is unsound!
   Consider P = {G(a,f(d),x) \<rightarrow> G(x,x,x)}
            Q = {c}
            R = {b \<rightarrow> a, b \<rightarrow> f(c), c \<rightarrow> d, f(c) \<rightarrow> b}
   Then obviously there is no innermost P-R-chain, so all 
   preconditions of the following lemma are satisfied except
   WCR (qrstep nfs Q R). Instead WCR (rstep R) is satisfied as all
   critical pairs are joinable (w.r.t. rstep R).
   But G(a,f(d),b) \<rightarrow>P G(b,b,b) -Q\<rightarrow>R^* G(a,f(d),b) is an infinite
   minimal (P,Q,R) chain. *)
lemma switch_to_innermost_proc: fixes R :: "('f,'v :: infinite)trs"
  assumes WCR: "WCR_on (qrstep nfs Q R) {t. SN_on (qrstep nfs Q R) {t}}"
  and NF_subset: "NF_trs R \<subseteq> NF_terms Q"
  and no_overlap: "critical_pairs ren (P \<union> Pw) R = {}"
  and m: m
  and vars: "\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  and fin: "finite_dpp (nfs,m,P,Pw,lhss R,{},R)"
  shows "finite_dpp (nfs,m,P,Pw,Q,{},R)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain s t \<sigma> where chain: "min_ichain (nfs,m,P,Pw,Q,{},R) s t \<sigma>" unfolding finite_dpp_def by blast
  let ?t = "\<lambda> i. t i \<cdot> \<sigma> i"
  let ?s = "\<lambda> i. s (Suc i) \<cdot> \<sigma> (Suc i)"
  from chain m have SN: "\<And> i. SN_on (qrstep nfs Q R) {?t i}"
              and Q: "\<And> i. ?s i \<in> NF_terms Q" 
              and steps: "\<And> i. (?t i, ?s i) \<in> (qrstep nfs Q R)^*"
              and P: "\<And> i. (s i, t i) \<in> P \<union> Pw"
              and inf: "INFM i. (s i, t i) \<in> P"
    by (auto simp: ichain.simps minimal_cond_def)
  let ?\<sigma> = "\<lambda> i x. some_NF (qrstep nfs Q R) (\<sigma> i x)"
  let ?t' = "\<lambda> i. t i \<cdot> ?\<sigma> i"
  let ?s' = "\<lambda> i. s (Suc i) \<cdot> ?\<sigma> (Suc i)"
  {
    fix i x
    assume "x \<in> vars_term (t i)"
    then have "t i \<unrhd> Var x" by auto
    then have "?t i \<unrhd> Var x \<cdot> \<sigma> i" by auto
    from ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep SN this]
    have SN: "SN_on (qrstep nfs Q R) {\<sigma> i x}" by auto
    from some_NF[OF this] have stepsx: "(\<sigma> i x, ?\<sigma> i x) \<in> (qrstep nfs Q R)^*"
      and NFx: "?\<sigma> i x \<in> NF (qrstep nfs Q R)" by auto
  } note steps_NF_x_t = this
  {
    fix i x
    assume "x \<in> vars_term (s (Suc i))"
    then have "s (Suc i) \<unrhd> Var x" by auto
    then have "?s i \<unrhd> Var x \<cdot> \<sigma> (Suc i)" by auto
    from ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep steps_preserve_SN_on[OF steps SN] this]
    have SN: "SN_on (qrstep nfs Q R) {\<sigma> (Suc i) x}" by auto
    from some_NF[OF this] have stepsx: "(\<sigma> (Suc i) x, ?\<sigma> (Suc i) x) \<in> (qrstep nfs Q R)^*"
      and NFx: "?\<sigma> (Suc i) x \<in> NF (qrstep nfs Q R)" by auto
  } note steps_NF_x_s = this
  {
    fix i
    have "(?t i, ?t' i) \<in> (qrstep nfs Q R)^*"
      by (rule subst_qrsteps_imp_qrsteps, insert steps_NF_x_t(1)[of _ i], auto)
  } note stepst = this
  {
    fix i
    have "?s' i \<in> NF (qrstep nfs Q R)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain v where "(?s' i, v) \<in> qrstep nfs Q R" by auto
      then obtain l r \<tau> C where si: "?s' i = C\<langle>l \<cdot> \<tau>\<rangle>" and "v = C\<langle>r \<cdot> \<tau>\<rangle>" and lr: "(l,r) \<in> R" 
      and NF: "\<forall> u \<lhd> l \<cdot> \<tau>. u \<in> NF_terms Q" and nfs: "NF_subst nfs (l,r) \<tau> Q" by auto
      from si have subt: "?s' i \<unrhd> l \<cdot> \<tau>" by auto
      {
        fix x
        assume x: "x \<in> vars_term (s (Suc i))" and subt: "?\<sigma> (Suc i) x \<unrhd> l \<cdot> \<tau>"
        from subt obtain C where "?\<sigma> (Suc i) x = C\<langle>l\<cdot>\<tau>\<rangle>" by auto
        with NF nfs lr have "(?\<sigma> (Suc i) x, C\<langle>r\<cdot>\<tau>\<rangle>) \<in> qrstep nfs Q R" by auto
        with steps_NF_x_s(2)[OF x] have False by auto
      } note not_in_vars = this
      have "\<exists> u \<unlhd> s (Suc i). l \<cdot> \<tau> = u \<cdot> ?\<sigma> (Suc i)"
        by (rule subt_instance_and_not_subst_imp_subt[OF subt], insert not_in_vars, auto)
      then obtain u where subt: "s (Suc i) \<unrhd> u" and u: "u \<cdot> ?\<sigma> (Suc i) = l \<cdot> \<tau>"
        by auto
      have nvar: "is_Fun u"
      proof
        assume "is_Var u"
        then obtain x where ux: "u = Var x" by auto
        from subt have x: "x \<in> vars_term (s (Suc i))" unfolding ux 
          by (rule subteq_Var_imp_in_vars_term)
        show False  
          by (rule not_in_vars[OF x], unfold u[symmetric] ux, auto)
      qed
      from subt obtain C where subt: "s (Suc i) = C\<langle>u\<rangle>" by auto
      from critical_pairs_exI[OF P lr subt nvar u refl, of ren] no_overlap
      show False by simp
    qed
  } note NF_s = this
  let ?sh = "\<lambda> t i. t (Suc i)"
  from inf have inf: "INFM i. (s (Suc i), t (Suc i)) \<in> P"
    using Infm_shift[of "\<lambda> i. (s i, t i) \<in> P" id "Suc 0"]
    by simp
  from Q_subset_R_imp_same_NF[OF NF_subset vars]
  have NF_conv: "NF_terms (lhss R) = NF (qrstep nfs Q R)" by simp
  { 
    fix i
    have "SN_on (qrstep nfs (lhss R) R) {?t' i}"
      by (rule SN_on_mono[OF steps_preserve_SN_on[OF stepst SN] qrstep_mono],
      insert NF_subset, auto)
  } note SN_t' = this
  have "min_ichain (nfs,m,P,Pw,fst ` R,{},R) (?sh s) (?sh t) (?sh ?\<sigma>)"
    unfolding min_ichain.simps ichain.simps minimal_cond_def Un_empty_left
  proof (intro conjI allI impI, rule P, rule disjI1[OF inf])
    fix i 
    from NF_s[of i] have NFs: "?s' i \<in> NF_terms (lhss R)"
      unfolding NF_conv .
    show "?s' i \<in> NF_terms (lhss R)" by fact
    show "SN_on (qrstep nfs (lhss R) R) {?t' i}" using SN_t'[of i] by simp
    show "NF_subst nfs (s (Suc i), t (Suc i)) (?\<sigma> (Suc i)) (lhss R)"
    proof
      fix x
      assume "x \<in> vars_term (s (Suc i)) \<or> x \<in> vars_term (t (Suc i))"
      then show "?\<sigma> (Suc i) x \<in> NF_terms (lhss R)"
      proof
        assume x: "x \<in> vars_term (t (Suc i))"
        from steps_NF_x_t(2)[OF x]
        show ?thesis unfolding NF_conv .
      next
        assume x: "x \<in> vars_term (s (Suc i))"
        from steps_NF_x_s(2)[OF x]
        show ?thesis unfolding NF_conv .
      qed
    qed
    let ?QR = "qrstep nfs Q R"
    let ?RR = "qrstep nfs (lhss R) R"
    have ts': "(?t i, ?s' i) \<in> ?QR^*"
      by (rule rtrancl_trans[OF steps subst_qrsteps_imp_qrsteps], insert steps_NF_x_s(1)[of _ i], auto)
    from some_NF_WCR[OF SN WCR ts' NF_s]
    have s'i_NF: "?s' i = some_NF ?QR (?t i)" .
    obtain w where w: "w = some_NF ?RR (?t' i)" by auto
    from some_NF[OF SN_t', of i] have stepsw: "(?t' i, w) \<in> ?RR^*" and w: "w \<in> NF ?RR"
      unfolding w by auto
    have stepsw': "(?t i, w) \<in> ?QR^*"
      by (rule rtrancl_trans[OF stepst set_mp[OF rtrancl_mono[OF qrstep_mono] stepsw]], insert NF_subset, auto)
    have w_NF: "w \<in> NF ?QR" unfolding NF_conv[symmetric] using w 
      using Q_subset_R_imp_same_NF[of R "lhss R"] vars by auto
    from some_NF_WCR[OF SN WCR stepsw' w_NF] have w_NF: "w = some_NF ?QR (?t i)" .
    from stepsw show "(?t' i, ?s' i) \<in> ?RR^*" unfolding s'i_NF w_NF .
  qed
  then have "\<not> finite_dpp (nfs,m,P,Pw,lhss R, {}, R)" unfolding finite_dpp_def by blast
  with fin show False by simp
qed

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

lemma switch_to_innermost_locally_confluent_overlay_main:
  fixes R :: "('f, 'v :: infinite) trs"
  assumes WCR: "WCR_on (rstep R) {t. SN_on (rstep R) {t}}"
    and overlay: "\<And> l r. (False,l,r) \<notin> critical_pairs ren R R"
    and SN: "SN (qrstep nfs (lhss R) R)"
    and shp: "\<And> f n. defined R (f, n) \<Longrightarrow> \<not> defined R (\<sharp> f, n)"
    and unshp: "\<And> f n. defined R (f, n) \<Longrightarrow> unshp (\<sharp> f) = f"
    and wf: "wf_trs R"
  shows "SN (rstep R)"
proof (rule ccontr)
  let ?conv = "Inl :: 'v \<Rightarrow> 'v + 'v"
  assume nSN: "\<not> ?thesis"
  have switch: "qrstep nfs (lhss R) R = qrstep False (lhss R) R"
    by (rule wwf_qtrs_imp_nfs_False_switch[OF wf_trs_imp_wwf_qtrs[OF wf]])
  from nSN have nSN: "\<not> SN (qrstep nfs {} R)" by auto
  from wf have wfq: "wf_qtrs nfs {} R" unfolding wf_qtrs_wf_trs_conv .
  from wf_trs_imp_lhs_Fun[OF wf] have no_Var: "(l,r) \<in> R \<Longrightarrow> \<not> is_Var l" for l r by auto
  have "\<exists> s t \<sigma>. min_ichain (initial_dpp \<sharp> nfs True {} R) s t \<sigma>"
    by (rule not_SN_imp_min_ichain[of nfs "{}" R \<sharp>, OF wfq nSN, unfolded applicable_rules_empty],
      insert shp, auto) 
  from this[unfolded initial_dpp.simps applicable_rules_empty]
  have nfin: "\<not> finite_dpp (nfs,True,DP \<sharp> R,{},{},{},R)" unfolding finite_dpp_def by auto
  have fin: "finite_dpp (nfs,True,DP \<sharp> R, {},{},{},R)"
  proof (rule switch_to_innermost_proc[OF _ _ _ _ no_Var], 
      unfold qrstep_rstep_conv, rule WCR, simp, unfold Un_empty_right)
    {
      fix s t u and \<sigma> \<tau> :: "('f,'v :: infinite)subst" and l r
      assume st: "(s,t) \<in> DP \<sharp> R" and lr: "(l,r) \<in> R" and su: "s \<unrhd> u" and u: "is_Fun u"    
      from u obtain g us where ug: "u = Fun g us" by (cases u, auto) 
      from lr wf obtain f ls where l: "l = Fun f ls" unfolding wf_trs_def by (cases l, auto)
      from lr[unfolded l] have f: "defined R (f,length ls)" unfolding defined_def by auto
      from st[unfolded DP_on_def] obtain l' r' where sl: "s = \<sharp> l'"
        and lr': "(l',r') \<in> R" by auto
      from su ug  obtain H ss where s: "s = Fun H ss" by (cases s, auto)
      with sl obtain h where l': "l' = Fun h ss" and H: "H = \<sharp> h" by (cases l', auto)
      from lr'[unfolded l'] have defh: "defined R (h,length ss)" unfolding defined_def
        by auto
      from shp[OF this] have H: "\<not> defined R (H, length ss)" unfolding H by auto
      have "u \<cdot> \<sigma> \<noteq> l \<cdot> \<tau>" 
      proof (cases "s = u")
        case True
        then have "u \<cdot> \<sigma> = s \<cdot> \<sigma>" by simp
        also have "... = Fun H ss \<cdot> \<sigma>" unfolding s ..
        also have "... \<noteq> Fun f ls \<cdot> \<tau>" 
        proof
          assume "Fun H ss \<cdot> \<sigma> = Fun f ls \<cdot> \<tau>"
          from arg_cong[OF this, of root] H f show False by simp
        qed
        finally show ?thesis unfolding l .
      next
        case False
        with su have "s \<rhd> u" by auto
        then obtain C where su: "s = C\<langle>u\<rangle>" and C: "C \<noteq> \<box>" by auto
        then obtain bef D aft where C: "C = More H bef D aft" and 
          ss: "ss = bef @ D\<langle>u\<rangle> # aft" unfolding s 
          by (cases C, auto)
        then have l'u: "l' = (More h bef D aft)\<langle>u\<rangle>" unfolding l' by simp
        then obtain C where l'u: "l' = C\<langle>u\<rangle>" and C: "False = (C = \<box>)" by force
        show ?thesis
        proof
          assume id: "u \<cdot> \<sigma> = l \<cdot> \<tau>"
          have "\<exists> x y. (False,x,y) \<in> critical_pairs ren R R"
            by (rule critical_pairs_exI[OF lr' lr l'u u id C])
          with overlay show False by auto
        qed
      qed      
    } note main = this
    show "critical_pairs ren (DP \<sharp> R) R = {}" 
    proof (rule ccontr)
      assume "\<not> ?thesis"
      from this[unfolded critical_pairs_def, simplified]
      obtain C s t l r \<sigma> \<tau> where P: "(C\<langle>s\<rangle>,t) \<in> DP \<sharp> R" and R: "(l,r) \<in> R"
        and s: "is_Fun s" and mgu: "mgu_vd ren s l = Some (\<sigma>,\<tau>)" by auto
      have subt: "C\<langle>s\<rangle> \<unrhd> s" by auto
      from main[OF P R subt s] have neq: "\<And> \<sigma>1 \<sigma>2 :: ('f,'v)subst. s \<cdot> \<sigma>1 \<noteq> l \<cdot> \<sigma>2" .
      from mgu_vd_sound[OF mgu] have "s \<cdot> \<sigma> = l \<cdot> \<tau>" by simp
      with neq show False by simp
    qed
  next
    show "finite_dpp (nfs,True,DP \<sharp> R, {}, lhss R, {}, R)"
      by (rule SN_imp_finite_dpp[OF SN[unfolded shp] shp, of unshp], 
          insert unshp no_Var, auto)
  qed simp
  from fin nfin show False by simp
qed

end

lemma switch_to_innermost_locally_confluent_overlay_finite: fixes R :: "('f,'v :: infinite)trs"
  assumes WCR: "WCR_on (rstep R) {t. SN_on (rstep R) {t}}"
  and overlay: "\<And> l r. (False,l,r) \<notin> critical_pairs ren R R" 
  and SN: "SN (qrstep nfs (lhss R) R)"
  and wf: "wf_trs R"
  and finite: "finite R"
  and infsig: "infinite (UNIV :: 'f set)"
  shows "SN (rstep R)"
proof -
  let ?Fn = "{fn. defined R fn}" 
  let ?F = "fst ` ?Fn"
  have "finite ?Fn"
    by (rule finite_subset[OF _ finite_funas_trs[OF finite]], insert defined_funas_trs[of R], auto)
  then have fin: "finite ?F" by auto
  from finite_fresh_names_infinite_univ[OF this infsig]
  obtain shp unshp where shp: "\<And> x. x \<in> ?F \<Longrightarrow> shp x \<notin> ?F" and unshp: "\<And> x. x \<in> ?F \<Longrightarrow> unshp (shp x) = x" by blast
  show ?thesis 
  proof (rule switch_to_innermost_locally_confluent_overlay_main[OF WCR overlay SN _ _ wf,
      of shp unshp])
    fix f n
    assume "defined R (f,n)"
    then have "f \<in> ?F" by force
    from shp[OF this] show "\<not> defined R (shp f, n)" by force
  next
    fix f n
    assume "defined R (f,n)"
    then have "f \<in> ?F" by force
    from unshp[OF this] show "unshp (shp f) = f" .
  qed
qed

(* use that the lab-datatype is infinite *)
lemma switch_to_innermost_locally_confluent_overlay: fixes R :: "(('f,'l)lab,'v :: infinite)trs"
  assumes WCR: "WCR_on (rstep R) {t. SN_on (rstep R) {t}}"
  and overlay: "\<And> l r. (False,l,r) \<notin> critical_pairs ren R R" 
  and SN: "SN (qrstep nfs (lhss R) R)"
  and wf: "wf_trs R"
  and finite: "finite R"
  shows "SN (rstep R)"
  by (rule switch_to_innermost_locally_confluent_overlay_finite[OF WCR overlay SN wf finite infinite_lab])

end
