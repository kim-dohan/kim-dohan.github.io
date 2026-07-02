(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Split_Impl
imports
  Framework.QDP_Framework_Impl
begin

definition
  split_proc ::
    "('dpp, 'f :: showl, 'v :: showl) dpp_ops \<Rightarrow> 'dpp
    \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f,'v) rules \<Rightarrow> 'dpp \<times> 'dpp"
where
  "split_proc I d P_remove R_remove \<equiv>
     let (P,Pw) = dpp_ops.split_pairs I d P_remove;
         (R,Rw) = dpp_ops.split_rules I d R_remove;
         dpp1 = dpp_ops.mk I (dpp_ops.nfs I d) (dpp_ops.minimal I d) P Pw (dpp_ops.Q I d) R Rw;
         dpp2 = dpp_spec.delete_pairs_rules I d P_remove R_remove
       in (dpp1,dpp2)"

context dpp_spec
begin
lemma split_proc: assumes s: "split_proc I d P_remove R_remove = (d1,d2)"
  and f1: "finite_dpp (dpp d1)"
  and f2: "finite_dpp (dpp d2)"
  shows "finite_dpp (dpp d)"
proof -
  let ?Pr = "set P_remove"
  let ?Rr = "set R_remove"
  let ?nfs = "NFS d"
  let ?m = "M d"
  obtain Ps Pws where sP: "split_pairs d P_remove = (Ps,Pws)" by force
  obtain Rs Rws where sR: "split_rules d R_remove = (Rs,Rws)" by force
  from s[unfolded split_proc_def Let_def sP sR split]
  have d1: "d1 = mk ?nfs ?m Ps Pws (Q d) Rs Rws" 
    and d2: "d2 = delete_pairs_rules d P_remove R_remove"
    by auto
  from 
    f1[unfolded d1 mk_sound] 
    split_pairs_sound[OF sP] split_rules_sound[OF sR]
  have f1: "finite_dpp (?nfs,?m,
    (set (P d) \<union> set (Pw d)) \<inter> ?Pr,
    set (P d) \<union> set (Pw d) - ?Pr,
    set (Q d),
    (set (R d) \<union> set (Rw d)) \<inter> ?Rr,
    set (R d) \<union> set (Rw d) - ?Rr)" unfolding pairs_sound rules_sound
    by auto
  show ?thesis 
    unfolding dpp_sound
    by (rule finite_dpp_split,
      rule f1[unfolded Int_commute[of _ ?Pr] Int_commute[of _ ?Rr]],
      insert f2[unfolded d2], simp)
qed
end

definition
  split_tt ::
    "('tp, 'f :: showl, 'v :: showl) tp_ops \<Rightarrow> 'tp
    \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'tp \<times> 'tp"
where
  "split_tt I tp R_remove \<equiv>
     let (R,Rw) = tp_ops.split_rules I tp R_remove;
         tp1 = tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) R Rw;
         tp2 = tp_spec.delete_rules I tp R_remove
       in (tp1,tp2)"

context tp_spec
begin
lemma split_tt: assumes s: "split_tt I tp R_remove = (tp1,tp2)"
  and sn1: "SN_qrel (qreltrs tp1)"
  and sn2: "SN_qrel (qreltrs tp2)"
  shows "SN_qrel (qreltrs tp)"
proof -
  let ?Rr = "set R_remove"
  let ?nfs = "NFS tp"
  obtain Rs Rws where sR: "split_rules tp R_remove = (Rs,Rws)" by force
  from s[unfolded split_tt_def Let_def sR split]
  have tp1: "tp1 = mk ?nfs (Q tp) Rs Rws" 
    and tp2: "tp2 = delete_rules tp R_remove"
    by auto
  from 
    sn1[unfolded tp1 mk_sound] 
    split_rules_sound[OF sR]
  have sn1: "SN_qrel (?nfs,
    set (Q tp),
    (set (R tp) \<union> set (Rw tp)) \<inter> ?Rr,
    set (R tp) \<union> set (Rw tp) - ?Rr)" unfolding rules_sound
    by auto
  show ?thesis 
    unfolding qreltrs_sound
    by (rule SN_qrel_split, 
      rule sn1[unfolded Int_commute[of _ ?Rr]],
      insert sn2[unfolded tp2], simp)
qed
end
end
