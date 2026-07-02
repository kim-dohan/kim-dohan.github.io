(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Argument_Filter_Impl
imports 
  Ord.Argument_Filter
  Framework.QDP_Framework_Impl
  Defaults
begin

definition
  argument_filter_tt :: "('tp, 'f::compare_order, 'v) tp_ops \<Rightarrow> 'f afs_list \<Rightarrow> 'tp proc"
where
  "argument_filter_tt I pi tp \<equiv> 
    case afs_of pi of
      None \<Rightarrow> error (showsl_lit (STR ''invalid argument filter''))
    | Some af \<Rightarrow> do {
      check (permutation_afs af) (showsl_lit (STR ''argument filter is not a permutation''));
      let \<pi> = af_rules af;
      return (tp_ops.mk I default_nfs_trs [] (\<pi> (tp_ops.R I tp)) (\<pi> (tp_ops.Rw I tp)))
  }"

lemma argument_filter_tt:
  assumes I: "tp_spec I"
  shows "tp_spec.sound_tt_impl I (argument_filter_tt I pi)"
proof -
  interpret tp_spec I by fact
  show ?thesis
  proof
    fix tp tp'
    assume ok: "argument_filter_tt I pi tp = return tp'"
      and fin: "SN_qrel (qreltrs tp')"
    let ?Q = "set (Q tp)"
    let ?R = "set (R tp)"
    let ?S = "set (Rw tp)"
    let ?RS = "?R \<union> ?S"
    note ok = ok[unfolded argument_filter_tt_def Let_def, simplified]
    from ok obtain af where pi: "afs_of pi = Some af" by (cases "afs_of pi", auto)
    note ok = ok[unfolded pi, simplified]
    let ?pir = "af_rules af"
    from ok have perm: "permutation_afs af"
      and res: "tp' = mk default_nfs_trs [] (?pir (R tp)) (?pir (Rw tp))" by auto
    from fin res have "SN_rel (rstep (af_rule af ` set (R tp))) (rstep (af_rule af ` set (Rw tp)))" by simp
    from af_SN_relto_rstep[OF perm this[unfolded SN_rel_on_def]]
    have SN: "SN_qrel (NFS tp, {}, set (R tp), set (Rw tp))" by (simp add: SN_rel_on_def)
    show "SN_qrel (qreltrs tp)" unfolding qreltrs_sound
      by (rule SN_qrel_mono[OF _ _ _ SN], auto)
  qed
qed
end
