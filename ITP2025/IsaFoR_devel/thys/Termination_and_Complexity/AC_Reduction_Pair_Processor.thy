(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory AC_Reduction_Pair_Processor
imports
  Framework.Relative_DP_Framework
  Ord.Reduction_Pair
  Usable_Rules
begin
 
lemma (in ce_af_redpair) i_trans_sound_dp_ac: 
  assumes
  fin_R: "finite R"
  and mode: "mode_cond mode m"
  and m: "m \<ge> n"
  and P: "(s,t) \<in> P"
  and steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (rstep RE)^*"
  and SN: "SN_on (relstep R E) {t \<cdot> \<sigma>}"
  and ur_closed: "ur_closed_af RE ur us \<pi>"
  and ur_P_closed: "ur_P_closed_af RE ur us \<pi> P"
  and orient: "ur \<subseteq> mode_left mode"
  and RE: "RE = R \<union> E"
  and sym_E: "symmetric_trs E"
  and AC_E: "AC_theory E"
  shows  "(t \<cdot> itrans.i_trans_subst {} R RE E ur us (c,m) \<sigma>, 
    u \<cdot> itrans.i_trans_subst {} R RE E ur us (c,m) \<tau>) \<in> mode_NS mode"
proof -
  let ?cn = "(c,m)"
  note pre = fin_R RE sym_E AC_E
  interpret itrans "{}" R RE E ur us ?cn by (rule itrans[OF pre])
  let ?s = "s \<cdot> \<sigma>"
  let ?t = "t \<cdot> \<sigma>"
  let ?u = "u \<cdot> \<tau>"
  let ?I = "i_trans"
  let ?Is = "i_trans_subst"
  let ?ssig = "s \<cdot> ?Is \<sigma>"
  let ?tsig = "t \<cdot> ?Is \<sigma>"
  let ?utau = "u \<cdot> ?Is \<tau>"
  let ?QR = "qrelac {} R E"
  have switch': "relstep R E = ?QR" unfolding qrelac_def  by auto
  have switch: "rstep RE = qrstep False {} R \<union> rstep E" unfolding RE by auto
  note SN' = SN[unfolded switch']
  note steps' = steps[unfolded switch]
  from SN_ac_preservation_steps[OF pre SN' steps'] 
  have SNu: "SN_on (qrelac {} R E) {u \<cdot> \<tau>}" .
  from i_transVI[OF pre mode m SN' steps' ur_closed orient]
  have one: "(?I ?t, ?I ?u) \<in> mode_NS mode" by simp
  from P ur_P_closed have "ur_closed_term_af RE ur us \<pi> t" by auto
  from i_transI[OF pre this SN'] have two: "(?tsig, ?I ?t) \<in> NS^*" by simp
  from i_transII[OF SNu, THEN conjunct1] ce_orient[OF m]
  have three: "(?I ?u, ?utau ) \<in> NS^*" by auto    
  from one two three have "(?tsig,?utau) \<in> NS^* O mode_NS mode O NS^*" by blast
  then show ?thesis by simp
qed

context
  fixes R E :: "('f,'v)trs"
  assumes fin_R: "finite R" 
  and sym_E: "symmetric_trs E"
  and AC_E: "AC_theory E"
begin

lemma ac_redtriple_proc_main: 
  assumes ur: "ur \<subseteq> NS"
  and oP: "P \<subseteq> NST \<union> S"
  and D: "D \<inter> P \<subseteq> S" (* D = deleted pairs *)
  and redtriple: "ce_af_redtriple S NS NST \<pi>"
  and ur_closed: "ur_closed_af (R \<union> E) ur us \<pi>"
  and ur_P_closed: "ur_P_closed_af (R \<union> E) ur us \<pi> P"
  shows "finite_rel_dpp (D \<inter> P, P - D, {}, R, E)"
proof   
  define mode where "mode = False" 
  fix s t \<sigma>
  assume chain: "min_relchain (D \<inter> P, P - D, {}, R, E) s t \<sigma>"
  interpret ce_af_redtriple S NS NST \<pi> by fact
  let ?I = "itrans.i_trans_subst {} R (R \<union> E) E ur us (c,n)"
  define \<tau> where "\<tau> = (\<lambda> i. ?I (\<sigma> i))"
  let ?R = "rstep (R \<union> E)"
  have mode: "mode_cond mode n" unfolding mode_def mode_cond_def by auto
  note chain = chain[unfolded min_relchain_via_ichain ichain.simps minimal_cond_def]
  from chain have P: "\<And> i. (s i, t i) \<in> P" by auto
  from chain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R^*" by auto
  from chain have SNt: "\<And> i. SN_on (relstep R E) {t i \<cdot> \<sigma> i}" by auto
  let ?s = "\<lambda> i. s i \<cdot> \<tau> i"
  let ?t = "\<lambda> i. t i \<cdot> \<tau> i"
  let ?next = "\<lambda> i. (s (Suc i), t (Suc i))"
  from ur have NS: "ur \<subseteq> mode_left mode" unfolding mode_def mode_left_def by auto
  from i_trans_sound_dp_ac[OF fin_R mode le_refl P steps SNt ur_closed ur_P_closed NS _ sym_E AC_E]
  have "\<And> i. (?t i, ?s (Suc i)) \<in> mode_NS mode" unfolding \<tau>_def by auto
  then have stepsNS: "\<And> i. (?t i, ?s (Suc i)) \<in> NS^*" unfolding mode_NS_def mode_def by auto
  from oP P have allP: "\<And> i. (s i, t i) \<in> NST \<union> S" by (auto simp: ichain.simps)
  from chain have inf: "INFM i. (s i, t i) \<in> D \<inter> P" by simp
  have piece1: "\<forall> i. (?t i, ?t (Suc i)) \<in> S \<or> (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* \<and> (?next i) \<notin> D"
  proof
    fix i
    show "(?t i, ?t (Suc i)) \<in> S \<or> (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* \<and> (?next i) \<notin> D" 
    proof (cases "?next i \<in> S")
      case True
      then have "(?s (Suc i), ?t (Suc i)) \<in> S" using subst_S by (auto simp: subst.closed_def)
      with stepsNS NS.trCompat show ?thesis by auto 
    next
      case False
      with stepsNS allP[of "Suc i"]
      have one: "?next i \<in> NST" and two: "?next i \<notin> S" by auto
      from one have "(?s (Suc i), ?t (Suc i)) \<in> NST" using subst_NST by (auto simp: subst.closed_def)
      with stepsNS[of i] have steps: "(?t i, ?t (Suc i)) \<in> NS^* O NST" by auto
      have "(?t i, ?t (Suc i)) \<in> (NS \<union> NST)^*"
        by (rule set_mp[OF _ steps], regexp)
      with two D P show ?thesis by auto
    qed
  qed  
  then have infSeq: "\<forall> i. (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* \<union> S" by auto
  from SN have "SN_on S {?t 0}" unfolding SN_defs by blast
  from infSeq both.trCompat this have "\<exists> j. \<forall> i \<ge> j. (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* - S" by (rule non_strict_ending)  
  from this obtain j where one: "\<forall> i \<ge> j. (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* - S" ..
  with piece1 have ns: "\<forall> i \<ge> j. ?next i \<notin> D" by blast
  from inf[unfolded INFM_nat] obtain n where n: "n > j" and s: "(s n, t n) \<in> D" by auto
  from n obtain m where n: "n = Suc m" and m: "m \<ge> j" by (cases n, auto)
  from ns[THEN spec[of _ m]] s show False unfolding n using m by auto
qed

lemma ac_redtriple_proc: 
  assumes ur: "ur \<subseteq> NS"
  and PQ: "P \<union> Q \<subseteq> NST \<union> S"
  and D: "D \<inter> (P \<union> Q) \<subseteq> S"
  and redtriple: "ce_af_redtriple S NS NST \<pi>"
  and ur_closed: "ur_closed_af (R \<union> E) ur us \<pi>"
  and ur_P_closed: "ur_P_closed_af (R \<union> E) ur us \<pi> (P \<union> Q)"
  and R: "R = Rs \<union> Rw"
  and fin: "finite_rel_dpp (P - D, Q - D, Rs, Rw, E)"
  shows "finite_rel_dpp (P, Q, Rs, Rw, E)"
    by (rule finite_rel_dpp_split_top[OF fin], unfold R[symmetric], 
    rule ac_redtriple_proc_main[OF ur PQ D redtriple ur_closed ur_P_closed])

lemma ac_redtriple_mono_proc_main: 
  assumes ur: "ur \<subseteq> NS \<union> S"
  and orient: "P \<subseteq> NS \<union> S"
  and DP: "(D_P \<inter> P) - {lr | lr. \<not> funas_term (fst lr) \<subseteq> us} \<subseteq> S"
  and DR: "(D_R \<inter> ur) - {lr | lr. \<not> funas_term (fst lr) \<subseteq> us} \<subseteq> S"
  and redtriple: "mono_ce_af_redtriple S NS NST \<pi>"
  and ur_closed: "ur_closed_af (R \<union> E) ur us \<pi>"
  and ur_P_closed: "ur_P_closed_af (R \<union> E) ur us \<pi> P"
  shows "finite_rel_dpp (D_P \<inter> P, P - D_P, D_R \<inter> R, R - D_R, E)"
proof
  define mode where "mode = True" 
  fix s t \<sigma>
  assume chain: "min_relchain (D_P \<inter> P, P - D_P, D_R \<inter> R, R - D_R, E) s t \<sigma>"
  interpret mono_ce_af_redtriple S NS NST \<pi> by fact
  let ?R = "rstep (R \<union> E)"
  have [simp]: "D_R \<inter> R \<union> (R - D_R \<union> E) = R \<union> E" "D_R \<inter> R \<union> (R - D_R) = R" by auto
  from ce_compatibleE[OF S_ce_compat] obtain n' where 
    S_compat: "\<And> m. m \<ge> n' \<Longrightarrow> ce_trs (c,m) \<subseteq> S" by metis
  obtain k where k: "k = max n n'" by auto
  then have n: "n \<le> k"  by simp
  from S_compat k have mode: "mode_cond mode k" unfolding mode_cond_def using ctxt_S by auto
  let ?cn = "(c,k)"
  note pre = fin_R refl sym_E AC_E
  interpret itrans "{}" R "R \<union> E" E ur us ?cn by (rule itrans[OF pre])
  let ?I = "i_trans_subst"
  let ?i = i_trans
  define \<tau> where "\<tau> = (\<lambda> i. ?I (\<sigma> i))"
  note chain = chain[unfolded min_relchain_via_ichain ichain.simps minimal_cond_def]
  from chain have P: "\<And> i. (s i, t i) \<in> P" by auto
  from chain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R^*" by auto
  from chain have SNt: "\<And> i. SN_on (relstep R E) {t i \<cdot> \<sigma> i}" by auto
  let ?s = "\<lambda> i. s i \<cdot> \<tau> i"
  let ?t = "\<lambda> i. t i \<cdot> \<tau> i"
  let ?next = "\<lambda> i. (s (Suc i), t (Suc i))"
  from ur have NS: "ur \<subseteq> mode_left mode" unfolding mode_def mode_left_def by auto
  {
    fix i    
    from i_trans_sound_dp_ac[OF fin_R mode n P steps SNt ur_closed ur_P_closed NS _ sym_E AC_E]
    have steps: "(?t i, ?s (Suc i)) \<in> mode_NS mode" unfolding \<tau>_def by auto
    also have "mode_NS mode \<subseteq> monoNS" unfolding mode_NS_def mode_def by auto
    also have "\<dots> \<subseteq> (rstep (NS \<union> S))^*" 
      using rtrancl_mono[OF subset_rstep[of "NS \<union> S"]] by auto 
    finally have "(?t i, ?s (Suc i)) \<in> (rstep (NS \<union> S))^*" .
  } note steps = this
  
  define nfs m where "nfs = False" and "m = False" 
  have idS: "S \<union> NS = NS \<union> S" by auto
  have chain: "ichain (nfs,m,S,NS,{},S,NS) s t \<tau>"
    unfolding ichain.simps qrstep_rstep_conv idS
  proof (intro conjI allI)
    fix i
    from P[of i] orient show "(s i, t i) \<in> NS \<union> S" by auto 
  next
    let ?Q = "qrstep False {} R \<union> rstep E"
    let ?QQ = "?Q^* O qrstep False {} (D_R \<inter> R) O ?Q^*"
    let ?R = "rstep (NS \<union> S)"
    let ?RR = "?R^* O rstep S O ?R^*"
    let ?QR = "qrelac {} R E"
    have switch: "relto (rstep R) (rstep E)= ?QR" unfolding qrelac_empty_is_qrstep qrelac_def by auto
    have url: "ur \<subseteq> mode_left mode" using ur by (auto simp: mode_def mode_left_def)
    show "(INFM i. (s i, t i) \<in> S) \<or> 
      (INFM i. (t i \<cdot> \<tau> i, s (Suc i) \<cdot> \<tau> (Suc i)) \<in> ?RR)" unfolding INFM_disj_distrib[symmetric] 
      unfolding INFM_nat
    proof (intro allI)
      fix m
      from chain 
      have "(INFM i. (s i, t i) \<in> D_P \<inter> P) \<or>
        (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QQ)" by (simp add: rstep_union)
      from this[unfolded INFM_disj_distrib[symmetric], unfolded INFM_nat]
      obtain l where l: "Suc m < l" and alt:"(s l, t l) \<in> D_P \<inter> P \<or> 
        (t l \<cdot> \<sigma> l, s (Suc l) \<cdot> \<sigma> (Suc l)) \<in> ?QQ" by blast
      then have l': "m < l" by auto
      from chain have SN: "\<And> l. SN_on ?QR {t l \<cdot> \<sigma> l}" by (simp add: switch)
      from alt show "\<exists> l > m. (s l, t l) \<in> S \<or> (t l \<cdot> \<tau> l, s (Suc l) \<cdot> \<tau> (Suc l)) \<in> ?RR"
      proof
        assume Ssteps: "(t l \<cdot> \<sigma> l, s (Suc l) \<cdot> \<sigma> (Suc l)) \<in> ?QQ"
        let ?tt = "t l \<cdot> \<tau> l"
        let ?st = "s (Suc l) \<cdot> \<tau> (Suc l)"
        have "(?tt, ?st) \<in> monoS" unfolding \<tau>_def
          by (rule i_trans_strict_step[OF pre mode _ n SN Ssteps ur_closed ur_P_closed P url],
            insert DR, auto simp: mode_def)
        with rtrancl_mono[OF subset_rstep[of "NS \<union> S"]] subset_rstep[of S] have "(?tt, ?st) \<in> ?RR" by auto
        with l' show ?thesis by auto
      next
        assume "(s l, t l) \<in> D_P \<inter> P"
        with DP have "(s l, t l) \<in> S \<or> \<not> funas_term (s l) \<subseteq> us" by force
        then show ?thesis
        proof
          assume nwf: "\<not> funas_term (s l) \<subseteq> us"
          from l obtain ll where ll: "l = Suc ll" by (cases l, auto)
          let ?ts = "t ll \<cdot> \<sigma> ll"
          let ?tt = "t ll \<cdot> \<tau> ll"
          let ?ss = "s (Suc ll) \<cdot> \<sigma> (Suc ll)"      
          let ?st = "s (Suc ll) \<cdot> \<tau> (Suc ll)"              
          from P ur_P_closed have urt: "ur_closed_term_af (R \<union> E) ur us \<pi> (t ll)" by force
          from chain have steps: "(?ts, ?ss) \<in> ?Q^*" by (simp add: rstep_union)
          from steps_preserve_SN_on_relto[OF steps] SN have SNs: "SN_on ?QR {?ss}" by (simp add: switch)
          from i_transI[OF pre urt] have ns0: "(?tt, ?i ?ts) \<in> NS^*" unfolding \<tau>_def using SN by simp
          from i_transVI[OF pre mode n SN steps ur_closed url] 
          have ns1: "(?i ?ts, ?i ?ss) \<in> monoNS" unfolding mode_def mode_NS_def by simp
          from i_transII[OF SNs, THEN conjunct2] nwf[unfolded ll]
          have "(?i ?ss, ?st) \<in> (rstep (ce_trs (c,k)))^+" unfolding \<tau>_def by auto
          from trancl_mono[OF this mono_ce[OF mode[unfolded mode_cond_def, THEN mp[OF _ _]]]]
          have strict: "(?i ?ss, ?st) \<in> S^+" unfolding mode_def by simp
          from ns0 ns1 strict have strict: "(?tt,?st) \<in> NS^* O monoNS O S^+" by auto
          then have "(?tt,?st) \<in> monoS" by regexp
          with rtrancl_mono[OF subset_rstep[of "NS \<union> S"]] subset_rstep[of S] 
          have strict: "(?tt, ?st) \<in> ?RR" by auto
          from l ll have "m < ll" by auto
          with strict show ?thesis by blast
        qed (insert l', auto)
      qed
    qed
  qed (auto simp: steps)
  have idS: "S \<inter> (NS \<union> S) = S" by auto
  from ichain_mono[OF chain subset_refl _ subset_refl subset_refl, of "NS \<union> S - S" "NS \<union> S - S"] 
    mono_redpair_sound_ichain[OF subset_refl subset_refl, of nfs m "{}" s t \<tau>]
  show False unfolding idS by blast
qed
  
lemma ac_redtriple_mono_proc: 
  assumes ur: "ur \<subseteq> NS \<union> S"
  and PQ: "P \<union> Q \<subseteq> NS \<union> S"
  and DP: "(D_P \<inter> (P \<union> Q)) - {lr | lr. \<not> funas_term (fst lr) \<subseteq> us} \<subseteq> S"
  and DR: "(D_R \<inter> ur) - {lr | lr. \<not> funas_term (fst lr) \<subseteq> us} \<subseteq> S"
  and redtriple: "mono_ce_af_redtriple S NS NST \<pi>"
  and ur_closed: "ur_closed_af (R \<union> E) ur us \<pi>"
  and ur_P_closed: "ur_P_closed_af (R \<union> E) ur us \<pi> (P \<union> Q)"
  and R: "R = Rs \<union> Rw"
  and fin: "finite_rel_dpp (P - D_P, Q - D_P, Rs - D_R, Rw - D_R, E)"
  shows "finite_rel_dpp (P, Q, Rs, Rw, E)"
  by (rule finite_rel_dpp_split[OF fin], unfold R[symmetric],
    rule ac_redtriple_mono_proc_main[OF ur PQ DP DR redtriple ur_closed ur_P_closed])
end

lemma SN_rel_AOCEQ: "SN_rel R (aoc_rewriting.AOCEQ A C) = 
  SN_rel R (acrstep A C)"
  unfolding SN_rel_defs conversion_def rtrancl_idemp symcl_acstep ..

lemma (in mono_redpair) ac_rule_removal: 
  assumes re: "R \<union> E \<subseteq> NS \<union> S"
  and r: "r \<subseteq> S"
  and E: "acrstep A C \<subseteq> rstep E"
  and SN_rel: "SN_rel (rstep (R - r)) (aoc_rewriting.AOCEQ A C)"
  shows "SN_rel (rstep R) (aoc_rewriting.AOCEQ A C)"
  unfolding SN_rel_AOCEQ
  unfolding SN_rel_ideriv
proof 
  let ?AC = "acrstep A C"
  assume "\<exists> f. ideriv (rstep R) ?AC f"
  then obtain f where f: "ideriv (rstep R) ?AC f" by auto
  {
    assume "\<exists>i. ideriv (rstep R - rstep r) (?AC - rstep r) (shift f i)"
    then obtain i where f: "ideriv (rstep R - rstep r) (?AC - rstep r) (shift f i)" ..
    have "ideriv (rstep (R - r)) ?AC (shift f i)"
      by (rule ideriv_mono[OF _ _ f], auto)
    with SN_rel[unfolded SN_rel_AOCEQ, unfolded SN_rel_ideriv] have False by blast
  }
  with ideriv_split[OF f, of "rstep r"] have 
    f: "ideriv (rstep r \<inter> (rstep R \<union> ?AC)) (rstep R \<union> ?AC - rstep r) f" by blast
  have f: "ideriv (rstep r) (rstep (R \<union> E)) f"
    by (rule ideriv_mono[OF _ _ f], insert E, auto simp: rstep_union)
  have f: "ideriv S (NS \<union> S) f"
    by (rule ideriv_mono[OF rstep_subset[OF ctxt_S subst_S r] 
      rstep_subset[OF ctxt.closed_Un[OF ctxt_NS ctxt_S] subst.closed_Un[OF subst_NS subst_S] re] f])    
  from compatible_SN'[OF compat_NS_S SN] have "SN_rel S (NS \<union> S)" unfolding SN_rel_defs .
  from this[unfolded SN_rel_ideriv] f show False by blast
qed
end
