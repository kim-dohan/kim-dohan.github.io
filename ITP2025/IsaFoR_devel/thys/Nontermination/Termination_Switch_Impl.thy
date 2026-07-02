(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
License: LGPL (see file COPYING.LESSER)
*)
theory Termination_Switch_Impl
imports
  Innermost_Switch_Impl
  Termination_Switch
begin

context
  fixes ren :: "'v :: {infinite,showl} renaming2" 
begin

definition
  switch_termination_proc :: "('dpp, 'f::{compare_order,showl}, 'v) dpp_ops \<Rightarrow> ('f,'v) join_info \<Rightarrow> 'dpp proc"
where
  "switch_termination_proc I joins_i dpp \<equiv> let 
       P = dpp_ops.pairs I dpp;
       R = dpp_ops.rules I dpp;
       Q = dpp_ops.Q I dpp
     in 
  check_return (do {
     let cp = critical_pairs_impl ren R R;
     check_allm (\<lambda> (b,st). check b (showsl_lit (STR ''rules are not overlay''))) cp;
     check_wf_trs R;
     check_critical_pairs R cp joins_i;
     check (critical_pairs_impl ren P R = []) (showsl_lit (STR ''there are overlaps between P and R''));
     check_NF_trs_subset R Q
          <+? (\<lambda> q. showsl q \<circ> showsl_lit (STR '' is not in normal form w.r.t. R''))
   }) (dpp_ops.mk I (dpp_ops.nfs I dpp) False P [] [] [] R)"

definition
  switch_termination_tt :: "('tp, 'f::{compare_order,showl}, 'v) tp_ops \<Rightarrow> ('f,'v) join_info \<Rightarrow> 'tp proc"
where
  "switch_termination_tt I joins_i tp \<equiv> let 
       R = tp_ops.rules I tp;
       Q = tp_ops.Q I tp
     in 
  check_return (do {
     let cp = critical_pairs_impl ren R R;
     check_allm (\<lambda> (b,st). check b (showsl_lit (STR ''rules are not overlay''))) cp;
     check_wf_trs R;
     check_critical_pairs R cp joins_i;
     check_NF_trs_subset R Q
          <+? (\<lambda> q. showsl q \<circ> showsl_lit (STR '' is not in normal form w.r.t. R''))
   }) (tp_ops.mk I (tp_ops.nfs I tp) [] R [])"

lemma switch_termination_proc: fixes I :: "('a,'f :: {compare_order,showl},'v)dpp_ops"
  assumes I: "dpp_spec I" 
  and inf: "infinite (UNIV :: 'f set)"
  and ok: "switch_termination_proc I joins_i dpp = return dpp'"
  and infinite: "infinite_dpp (dpp_ops.nfs I dpp', set (dpp_ops.pairs I dpp'), set (dpp_ops.Q I dpp'), set (dpp_ops.rules I dpp'))"
  shows "infinite_dpp (dpp_ops.nfs I dpp, set (dpp_ops.pairs I dpp), set (dpp_ops.Q I dpp), set (dpp_ops.rules I dpp))"
proof -
  interpret dpp_spec I by (rule I)
  let ?P = "set (pairs dpp)"
  let ?R = "set (rules dpp)"
  let ?nfs = "NFS dpp"
  let ?Q = "set (Q dpp)"
  note ok = ok[unfolded switch_termination_proc_def Let_def, simplified]
  from ok infinite have infinite: "infinite_dpp (?nfs,?P, {}, ?R)"  by simp
  from ok critical_pairs_impl[of ren "pairs dpp" "rules dpp"] 
  have cps_empty: "critical_pairs ren ?P ?R = {}" by simp
  from ok check_critical_pairs[of "rules dpp"] have WCR: "WCR (rstep ?R)" by auto
  from ok have NF: "NF_trs ?R \<subseteq> NF_terms ?Q" by auto
  from WCR have WCR_SN: "WCR_on (rstep ?R) {t. SN_on (rstep ?R) {t}}"
    unfolding WCR_on_def by auto
  from ok have overlay: "\<And> l r. (False,l,r) \<notin> critical_pairs ren ?R ?R" by auto 
  from ok have wf: "wf_trs ?R" by auto
  note innermost_switch = switch_to_innermost_locally_confluent_overlay_finite[OF WCR_SN overlay _ wf finite_set inf]
  have SN: "(SN (qrstep ?nfs ?Q ?R)) \<Longrightarrow> SN (rstep ?R)" 
  proof (rule innermost_switch)
    assume SN: "SN (qrstep ?nfs ?Q ?R)"
    show "SN (qrstep ?nfs (lhss ?R) ?R)"
      by (rule SN_subset[OF SN qrstep_mono], insert NF, auto)
  qed
  show ?thesis
  proof (rule termination_switch_proc[OF infinite cps_empty WCR NF _ SN])
    fix l r
    assume "(l,r) \<in> ?R" with wf show "is_Fun l" unfolding wf_trs_def by (cases l, auto)
  qed
qed

lemma switch_termination_tt: fixes I :: "('a,'f :: {compare_order,showl},'v)tp_ops"
  assumes I: "tp_spec I" 
  and inf: "infinite (UNIV :: 'f set)"
  and ok: "switch_termination_tt I joins_i tp = return tp'"
  and nSN: "\<not> SN (qrstep (tp_ops.nfs I tp') (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))"
    (is "\<not> ?SN'")
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
    (is "\<not> ?SN")
proof 
  interpret tp_spec I by fact
  assume ?SN
  let ?R' = "set (rules tp')"
  let ?R = "set (rules tp)"
  let ?nfs = "NFS tp"
  let ?Q = "set (Q tp)"
  note ok = ok[unfolded switch_termination_tt_def Let_def, simplified]
  from ok check_critical_pairs[of "rules tp"] have WCR: "WCR (rstep ?R)" by auto
  from ok have NF: "NF_trs ?R \<subseteq> NF_terms ?Q" by auto
  from WCR have WCR_SN: "WCR_on (rstep ?R) {t. SN_on (rstep ?R) {t}}"
    unfolding WCR_on_def by auto
  from ok have overlay: "\<And> l r. (False,l,r) \<notin> critical_pairs ren ?R ?R" by auto 
  from ok have wf: "wf_trs ?R" by auto
  note innermost_switch = switch_to_innermost_locally_confluent_overlay_finite[OF WCR_SN overlay _ wf finite_set inf]
  from nSN ok have "\<not> SN (rstep ?R)" by auto
  with innermost_switch[of ?nfs] have "\<not> SN (qrstep ?nfs (lhss ?R) ?R)" by auto
  with SN_subset[OF \<open>?SN\<close> qrstep_mono[OF subset_refl], of "lhss ?R"] NF show False by auto
qed

end
end