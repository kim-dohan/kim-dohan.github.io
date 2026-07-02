(*
Author:  Alexander Krauss <krauss@in.tum.de> (2009)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Reduction_Pair
imports
  Term_Order
  TRS.QDP_Framework
begin


lemma (in redtriple) SN_rel:   
  shows "SN_rel S NS"
  unfolding SN_rel_defs
  by (rule SN_subset[OF compatible_SN'[OF NS.compat SN]], regexp)

context mono_redpair
begin

lemma SN_rel_rstep: "SN_rel (rstep S) (rstep NS)" 
  apply (rule SN_rel_mono[OF rstep_subset[OF ctxt_S subst_S subset_refl] rstep_subset[OF ctxt_NS subst_NS subset_refl]])
  apply (unfold SN_rel_defs)
  apply (rule SN_subset[OF compatible_SN'[OF compat_NS_S SN]])
  apply regexp
  done

lemma mono_redpair_sound_ichain: 
  assumes R: "R \<subseteq> NS \<union> S"
  and P: "P \<subseteq> NS \<union> S"
  shows "\<not> ichain (nfs,m,S \<inter> P, P - S, Q, S \<inter> R, R - S) s t \<sigma>"
  by (rule SN_rel_ichain, rule SN_rel_mono[OF qrstep_mono[of _ S _ "{}"] qrstep_mono[of _ NS _ "{}"]], insert R P SN_rel_rstep, auto)

lemma mono_redpair_sound_ideriv: 
  assumes R: "R \<subseteq> NS \<union> S"
  shows "\<not> qrs_ideriv nfs Q (S \<inter> R) (R - S) ts"
  using SN_rel_rstep qrs_ideriv_mono[of "S \<inter> R" S "R - S" NS Q "{}", of nfs ts]
    R unfolding qrs_ideriv_def SN_rel_ideriv by auto
end

fun mono_redpair_proc :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)dpp \<Rightarrow> ('f,'v)dpp \<Rightarrow> bool"
 where "mono_redpair_proc S NS Ps Rs (nfs,m,P,Pw,Q,R,Rw) (nfs',m',P',Pw',Q',R',Rw') = 
   (R \<union> Rw' \<subseteq> NS \<union> S \<and> P \<union> Pw \<subseteq> NS \<union> S \<and> (P \<union> Pw) \<inter> Ps \<subseteq> S 
    \<and> (R \<union> Rw) \<inter> Rs \<subseteq> S \<and> P' = P - Ps \<and> Pw' = Pw - Ps \<and> R' = R - Rs 
    \<and> Rw' = Rw - Rs \<and> Q' = Q \<and> nfs' = nfs \<and> (m' \<longrightarrow> m))"

fun mono_redpair_tt :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)qreltrs \<Rightarrow> ('f,'v)qreltrs \<Rightarrow> bool"
 where "mono_redpair_tt S NS Rs (nfs,Q,R,Rw) (nfs',Q',R',Rw') = 
  (R \<union> Rw' \<subseteq> NS \<union> S \<and> (R \<union> Rw) \<inter> Rs \<subseteq> S \<and> R' = R - Rs \<and> Rw' = Rw - Rs 
   \<and> Q' = Q \<and> nfs' = nfs)"

lemma (in mono_redpair) manna_ness:
  assumes strict: "R \<subseteq> S"
  shows "SN (rstep R)"
proof -
  from ctxt_S strict subst_S have "(rstep R) \<subseteq> S" by (intro rstep_subset)
  from SN_subset[OF SN this] show "SN (rstep R)"  .
qed

lemma (in redtriple) rule_shift_complexity: 
  assumes mono: "ctxt.closed S"
  and strict: "R1 \<subseteq> S"
  and non_strict: "Rw \<union> R2 \<subseteq> NS"
  and cpx: "deriv_bound_measure_class S cm cc'"
  and cc': "cc' \<le> cc"
  and rec: "deriv_bound_measure_class (relto (qrstep nfs Q R2) (qrstep nfs Q (Rw \<union> R1))) cm cc"
  shows "deriv_bound_measure_class (relto (qrstep nfs Q (R1 \<union> R2)) (qrstep nfs Q Rw)) cm cc"
proof -
  from mono strict subst_S have one: "rstep R1 \<subseteq> S" by (intro rstep_subset)
  then have one: "qrstep nfs Q R1 \<subseteq> S" using qrstep_subset_rstep[of nfs Q R1] by blast
  from rstep_subset[OF ctxt_NS subst_NS non_strict] have two: "rstep (Rw \<union> R2) \<subseteq> NS" .
  then have two: "qrstep nfs Q (Rw \<union> R2) \<subseteq> NS" using qrstep_subset_rstep[of nfs Q "Rw \<union> R2"] by blast
  from relto_mono[OF one two] have rel: "relto (qrstep nfs Q R1) (qrstep nfs Q Rw \<union> qrstep nfs Q R2) \<subseteq> relto S NS" unfolding qrstep_union .
  then have rel: "relto (qrstep nfs Q R1) (qrstep nfs Q Rw \<union> qrstep nfs Q R2) \<subseteq> S" by (simp add: order_simps)
  have bound: "deriv_bound_measure_class (relto (qrstep nfs Q R1) (qrstep nfs Q Rw \<union> qrstep nfs Q R2)) cm cc"
    by (rule deriv_bound_measure_class_mono[OF rel subset_refl _ cpx], insert cc', auto)
  show ?thesis using bound rec unfolding qrstep_union by (rule deriv_bound_relto_measure_class_union)
qed
  
context mono_redtriple
begin
lemma mono_redpair_proc_subset: "subset_proc (mono_redpair_proc S NS Ps Rs)"
unfolding subset_proc_def
proof (intro allI impI)
  fix P Pw Q R Rw P' Pw' Q' R' Rw' and nfs nfs' m m' :: bool
  assume proc: "mono_redpair_proc S NS Ps Rs (nfs,m,P,Pw,Q,R,Rw) (nfs',m',P',Pw',Q',R',Rw')"  
  from proc have R: "R' = R - Rs" and Rw: "Rw' = Rw - Rs" and Q: "Q' = Q" and P: "P' = P - Ps"
    and Pw: "Pw' = Pw - Ps" and id: "nfs' = nfs" and m: "m' \<longrightarrow> m" by auto
  show "R' \<union> Rw' \<subseteq> R \<union> Rw \<and> Q' = Q \<and> nfs' = nfs \<and> (m' \<longrightarrow> m) \<and> 
    (\<forall> s t \<sigma> . min_ichain (nfs,m,P, Pw, Q, R, Rw) s t \<sigma> \<longrightarrow> (\<exists> i. ichain (nfs,m',P',Pw',Q',R', Rw') (shift s i) (shift t i) (shift \<sigma> i)))"  
    unfolding id[symmetric]
  proof (intro conjI, unfold R Rw Q P Pw, rule subsetI, blast, simp, rule refl, rule m,
    intro allI impI)
    fix s t \<sigma>
    assume min: "min_ichain (nfs',m,P,Pw,Q,R,Rw) s t \<sigma>"
    then have ichain: "ichain (nfs',m',P,Pw,Q,R,Rw) s t \<sigma>" by (simp add: ichain.simps)
    show "\<exists> i. ichain (nfs',m',P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs) (shift s i) (shift t i) (shift \<sigma> i)"
    proof (rule ichain_split[OF ichain], rule)
      assume chain: "ichain (nfs',m',Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps ,Q,Rs \<inter> (R \<union> Rw) ,R \<union> Rw - Rs) s t \<sigma>"
      have "ichain (nfs',m',S \<inter> (P \<union> Pw), P \<union> Pw - S ,Q, S \<inter> (R \<union> Rw), R \<union> Rw - S) s t \<sigma>"
        by (rule ichain_mono[OF chain], insert proc, auto)
      moreover have "\<not> ichain (nfs',m',S \<inter> (P \<union> Pw), P \<union> Pw - S ,Q, S \<inter> (R \<union> Rw),R \<union> Rw - S) s t \<sigma>"
        by (rule mono_redpair_sound_ichain, insert proc, auto)
      ultimately show False by simp
    qed
  qed
qed

lemma mono_redpair_tt:
  "rel_tt (mono_redpair_tt S NS Rs)"
unfolding rel_tt_def
proof (intro allI impI)
  fix Q R Rw Q' R' Rw' ts nfs nfs'
  assume proc: "mono_redpair_tt S NS Rs (nfs,Q,R,Rw) (nfs',Q',R',Rw')" 
    and ideriv: "qrs_ideriv nfs Q R Rw ts"
  from proc have R: "R' = R - Rs" and Rw: "Rw' = Rw - Rs" and 
   Q: "Q' = Q" and Rns: "R \<union> Rw \<subseteq> NS \<union> S" and nfs: "nfs = nfs'" by auto
  from qrs_ideriv_split[OF ideriv mono_redpair_sound_ideriv[OF Rns]]
  obtain i where ideriv: "qrs_ideriv nfs Q (R - S) (Rw - S) (shift ts i)" ..
  have "qrs_ideriv nfs Q (R - Rs) (Rw - Rs) (shift ts i)"
    by (rule qrs_ideriv_mono[OF _ _ _ ideriv], insert proc, auto)
  then show "Ex (qrs_ideriv nfs' Q' R' Rw')" unfolding R Rw Q nfs by auto
qed
end

end