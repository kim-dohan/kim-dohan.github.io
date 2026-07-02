(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
License: LGPL (see file COPYING.LESSER)
*)
theory Innermost_Switch_Impl
imports
  Innermost_Switch
  CR.Critical_Pairs_Impl
  Framework.QDP_Framework_Impl
begin

(* silently transforms weak intro strict rules *)
context
  fixes ren :: "'v :: {infinite,showl} renaming2" 
begin
definition
  switch_innermost_tt :: "('tp, 'f:: showl, 'v) tp_ops \<Rightarrow> ('f,'v) join_info \<Rightarrow> 'tp proc"
where
  "switch_innermost_tt I joins_i trs \<equiv> let r = tp_ops.rules I trs in
  check_return (do {
     let cp = critical_pairs_impl ren r r;
     check_allm (\<lambda> (b,st). check b (showsl_lit (STR ''rules are not overlay''))) cp;
     check_critical_pairs r cp joins_i;
     check_wf_trs r
   }) (tp_ops.mk I True (map fst r) (r) [])"


lemma switch_innermost_tt: fixes I :: "('a,'f :: showl,'v)tp_ops"
  assumes I: "tp_spec I" 
  and inf: "infinite (UNIV :: 'f set)"
  shows
  "tp_spec.sound_tt_impl I (switch_innermost_tt I joins_i)"
proof -
  interpret tp_spec I by (rule I)
  show ?thesis
  proof
    fix tp tp'
    assume ok: "switch_innermost_tt I joins_i tp = return tp'"
      and fin: "SN_qrel (qreltrs tp')"
    let ?R = "set (rules tp)"
    let ?nfs = "NFS tp"
    let ?Q = "set (Q tp)"
    let ?cp = "critical_pairs ren ?R ?R"
    note ok = ok[unfolded switch_innermost_tt_def Let_def, simplified]
    from ok have tp': "tp' = mk True (map fst (rules tp)) (rules tp) []" by auto
    from ok have cp: "isOK (check_critical_pairs (rules tp) (critical_pairs_impl ren (rules tp) (rules tp)) joins_i)" by simp
    from ok have overlay: "\<And> st. (False,st) \<notin> ?cp" by auto
    from ok have wf: "wf_trs (set (rules tp))" by auto
    from check_critical_pairs[OF cp] have WCR: "WCR_on (rstep ?R) {t. SN_on (rstep ?R) {t}}" unfolding WCR_on_def by auto
    from fin[unfolded tp'] have SN: "SN (qrstep True (lhss ?R) ?R)" by simp
    from switch_to_innermost_locally_confluent_overlay_finite[OF WCR overlay SN wf finite_set inf] have SN: "SN_qrel (?nfs,{},?R,{})" by simp
    show "SN_qrel (qreltrs tp)"
      unfolding qreltrs_sound
      by (rule SN_qrel_mono[OF _ _ _ SN], unfold rules_sound, auto)
  qed
qed


definition
  switch_innermost_proc :: "('dpp, 'f:: showl, 'v) dpp_ops \<Rightarrow> ('f,'v) join_info \<Rightarrow> 'dpp proc"
where
  "switch_innermost_proc I joins_i dpp \<equiv> 
  let r = dpp_ops.Rw I dpp;
      p = dpp_ops.P I dpp;
      pw = dpp_ops.Pw I dpp;
      nfs = dpp_ops.nfs I dpp in
  check_return (do {
     check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''left variables in R forbidden''))) (if nfs then r else []);
     check (dpp_ops.minimal I dpp) (showsl_lit (STR ''minimality required''));
     check (dpp_ops.Q I dpp = []) (showsl_lit (STR ''non-empty Q not yet supported''));
     check (dpp_ops.R I dpp = []) (showsl_lit (STR ''strict rules not allowed''));
     check (critical_pairs_impl ren (p @ pw) r = []) (showsl_lit (STR ''overlaps between P and R not allowed''));
     check_critical_pairs r (critical_pairs_impl ren r r) joins_i
   }) (dpp_ops.mk I nfs True p pw (map fst r) [] r)"

lemma switch_innermost_proc: fixes I :: "('a,'f :: showl,'v)dpp_ops"
  assumes I: "dpp_spec I" 
  shows
  "dpp_spec.sound_proc_impl I (switch_innermost_proc I joins_i)"
proof -
  interpret dpp_spec I by (rule I)
  show ?thesis
  proof
    fix d d'
    assume ok: "switch_innermost_proc I joins_i d = return d'"
      and fin: "finite_dpp (dpp d')"
    let ?Rw = "set (Rw d)"
    let ?R = "set (R d)"
    let ?Pw = "set (Pw d)"
    let ?P = "set (P d)"
    let ?Q = "{}"
    let ?nfs = "NFS d"
    let ?m = "M d"
    let ?cp = "critical_pairs ren ?Rw ?Rw"
    note ok = ok[unfolded switch_innermost_proc_def Let_def, simplified]
    from ok have d': "d' = mk ?nfs ?m (P d) (Pw d) (map fst (Rw d)) [] (Rw d)" by auto
    from ok have cp: "isOK (check_critical_pairs (Rw d) (critical_pairs_impl ren (Rw d) (Rw d)) joins_i)" by simp
    from ok have no_overlay: "set (critical_pairs_impl ren (P d @ Pw d) (Rw d)) = {}" by auto
    from ok have vars: "\<And> l r. ?nfs \<Longrightarrow> (l,r) \<in> ?Rw \<Longrightarrow> is_Fun l" by auto
    from ok have m: ?m by auto
    from check_critical_pairs[OF cp] have WCR: "WCR_on (qrstep ?nfs ?Q ?Rw) {t. SN_on (qrstep ?nfs ?Q ?Rw) {t}}" unfolding WCR_on_def by auto
    from fin[unfolded d'] have fin: "finite_dpp (?nfs,?m,?P,?Pw,lhss ?Rw,{},?Rw)" by simp
    from switch_to_innermost_proc[OF WCR _ _ \<open>?m\<close> vars fin] no_overlay 
    have fin: "finite_dpp (?nfs, ?m, ?P, ?Pw, {}, {}, ?Rw)" by auto
    show "finite_dpp (dpp d)"
      unfolding dpp_sound using fin ok by auto
  qed
qed


end
end
