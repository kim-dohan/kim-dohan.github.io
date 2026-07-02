(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Reduction_Pair_Proc_Impl
imports
  Ord.Reduction_Pair
  Ord.Term_Order_Impl
  Framework.QDP_Framework_Impl
  Auxx.Map_Choice
  TRS.Q_Restricted_Rewriting_Impl
  Usable_Replacement_Map_Impl
begin

definition
  mono_redpair_proc ::
    "('dpp, 'f, 'v) dpp_ops \<Rightarrow> ('f:: showl, 'v:: showl) rel_impl \<Rightarrow> 
     ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'dpp proc"
where
  "mono_redpair_proc I rp Premove Rremove dpp = check_return (do {
     let (ps,pns) = dpp_ops.split_pairs I dpp Premove;
     let (rs,rns) = dpp_ops.split_rules I dpp Rremove;
     rel_impl_mono_redpair rp (ps @ rs) (pns @ rns);
     rel_impl_ns rp rns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting TRS\<newline>'') \<circ> s);
     rel_impl_s rp  rs
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting TRS\<newline>'') \<circ> s);
     rel_impl_ns rp  pns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s);
     rel_impl_s rp ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the reduction pair processor with the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s))
   (dpp_spec.delete_pairs_rules I dpp Premove Rremove)"

definition
  mono_urm_redpair_proc ::
    "('dpp, 'f, string) dpp_ops \<Rightarrow> ('f::{showl, compare_order}, string) rel_impl \<Rightarrow> 
     ('f, string) rules \<Rightarrow> ('f, string) rules \<Rightarrow> 'dpp proc"
where
  "mono_urm_redpair_proc I rp Premove Rremove dpp = check_return (do {
     let (ps,pns) = dpp_ops.split_pairs I dpp Premove;
     let (rs,rns) = dpp_ops.split_rules I dpp Rremove;
     let r = dpp_ops.rules I dpp;
     let q = dpp_ops.Q I dpp;
     let p = dpp_ops.pairs I dpp;
     check_wf_trs p;
     check_wf_trs r;
     check (dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''innermost required''));
     let (fs,\<mu>,info) = get_innermost_strict_repl_map_dpp I dpp rs;
     rel_impl_redpair rp;
     let \<mu>' = rel_impl.mono_af rp;
     (check_allm (\<lambda> f. check (\<mu> f \<subseteq> \<mu>' f) 
       (showsl_lit (STR ''error in monotonicity: strict order for '') \<circ> showsl f
       \<circ> showsl_lit (STR '' ensures monotonicity in positions '') \<circ> showsl_position_set f (\<mu>' f)
       \<circ> showsl_lit (STR ''\<newline>but usable replacement map is '') \<circ> showsl_position_set f (\<mu> f))) fs) <+? 
     (\<lambda> s. s \<circ> showsl_lit (STR ''\<newline>the computed usable replacement map ('') \<circ> showsl info \<circ> showsl_lit (STR '') is\<newline>'') \<circ>
       showsl_sep (\<lambda> f. showsl_lit (STR ''mu('') \<circ> showsl f \<circ> showsl_lit (STR '') = '') \<circ> showsl_position_set f (\<mu> f)) showsl_nl fs
       \<circ> showsl_lit (STR ''\<newline>and mu(f) = {} for all other symbols f''));
     rel_impl_ns rp rns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting TRS\<newline>'') \<circ> s);
     rel_impl_s rp rs
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting TRS\<newline>'') \<circ> s);
     rel_impl_ns rp pns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s);
     rel_impl_s rp ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the reduction pair processor with usable repl. maps and the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s))
   (dpp_spec.delete_pairs_rules I dpp Premove Rremove)"

definition
  rule_removal_tt ::
    "('tp, 'f, 'v) tp_ops \<Rightarrow> ('f:: showl, 'v:: showl) rel_impl \<Rightarrow> 
    ('f, 'v) rules \<Rightarrow> 'tp proc"
where
  "rule_removal_tt I rp Rremove trs = check_return (do {
     let (rs,rns) = tp_ops.split_rules I trs Rremove;
     rel_impl_mono_redpair rp rs rns;
     rel_impl_ns rp rns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting TRS\<newline>'') \<circ> s);
     rel_impl_s rp  rs
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting TRS\<newline>'') \<circ> s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the reduction pair processor with the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s))
   (tp_spec.delete_rules I trs Rremove)"
    
definition
  rule_shift_complexity_tt ::
    "('tp, 'f, 'v) tp_ops \<Rightarrow> ('f::{showl, compare_order}, 'v::{showl, compare_order}) rel_impl \<Rightarrow> ('f,'v)rules \<Rightarrow>
    ('f,'v)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp proc"
where
  "rule_shift_complexity_tt I rp Rdelete cm cc tp \<equiv> let 
      R = tp_ops.R I tp;
      Rw = tp_ops.Rw I tp;
      R2 = ceta_list_diff R Rdelete in
 check_return (do {
     rel_impl_mono_redpair rp Rdelete (Rw @ R2)
       <+? (\<lambda>s. showsl_lit (STR ''problem with monotonicity of strict order\<newline>'') \<circ> s);
     rel_impl_s rp Rdelete
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting strict TRS\<newline>'') \<circ> s);
     rel_impl_ns rp (Rw @ R2)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting non-strict TRS\<newline>'') \<circ> s);
     rel_impl.cpx rp cm cc
       <+? (\<lambda>s. showsl_lit (STR ''problem when ensuring complexity of order\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not derive the intended complexity '') \<circ> showsl cc \<circ> showsl_lit (STR '' from the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s))
     (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) R2 (list_union Rw Rdelete))"


lemma (in dpp_spec) mono_redpair_proc:
  assumes rp: "rel_impl rp"
  shows "sound_proc_impl (mono_redpair_proc I rp ps rs)"
proof 
  fix d d'
  assume fin: "finite_dpp (dpp d')"
  and ok: "mono_redpair_proc I rp ps rs d = return d'"
  let ?Ps = "set ps"
  let ?Rs = "set rs"
  let ?P = "set (P d)"
  let ?Pw = "set (Pw d)"
  let ?Q = "set (Q d)"
  let ?R = "set (R d)"
  let ?Rw = "set (Rw d)"
  let ?nfs = "NFS d"
  let ?m = "M d"
  obtain Ps Pr where p: "split_pairs d ps = (Ps,Pr)" by force
  from split_pairs_sound[OF this] have Ps: "set Ps = (?P \<union> ?Pw) \<inter> ?Ps" 
    and Pr: "set Pr = (?P \<union> ?Pw) - ?Ps" by auto
  obtain Rs Rr where r: "split_rules d rs = (Rs,Rr)" by force
  from split_rules_sound[OF this] have Rs: "set Rs = (?R \<union> ?Rw) \<inter> ?Rs" 
    and Rr: "set Rr = (?R \<union> ?Rw) - ?Rs" by auto
  note ok = ok[unfolded mono_redpair_proc_def, simplified, simplified p r split]
  from ok have valid: "isOK (rel_impl_mono_redpair rp (Ps @ Rs) (Pr @ Rr))" 
    and orient: "isOK (rel_impl_s rp (Ps @ Rs))" "isOK (rel_impl_ns rp (Pr @ Rr))"  
    and d': "d' = delete_pairs_rules d ps rs" by (auto simp: rel_impl_list)
  from rel_impl_mono_redpair[OF rp valid orient, of undefined undefined]
  obtain S NS NST where S: "(?P \<union> ?Pw) \<inter> ?Ps \<subseteq> S" "(?R \<union> ?Rw) \<inter> ?Rs \<subseteq> S" and 
    NS: "?P \<union> ?Pw - ?Ps \<subseteq> NS" "?R \<union> ?Rw - ?Rs \<subseteq> NS" 
    and mono: "mono_redtriple_order S NS NST" 
    by (auto simp: Pr Ps Rr Rs)
  interpret mono_redtriple_order S NS NST by fact
  have proc: "Reduction_Pair.mono_redpair_proc S NS ?Ps ?Rs (?nfs,?m,?P,?Pw,?Q,?R,?Rw) (?nfs,?m,?P-?Ps,?Pw-?Ps,?Q,?R-?Rs,?Rw-?Rs)" using NS S ctxt_S by auto
  note fin =  fin[unfolded d' delete_simps]
  show "finite_dpp (dpp d)" unfolding d' dpp_sound
    by (rule subset_proc[OF fin proc mono_redpair_proc_subset])
qed


lemma mono_urm_redpair_proc:
  assumes "rel_impl rp"
    and I: "dpp_spec I"
  shows "dpp_spec.sound_proc_impl I (mono_urm_redpair_proc I rp ps rs)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof
    fix d d'
    assume fin: "finite_dpp (dpp d')"
    and ok: "mono_urm_redpair_proc I rp  ps rs d = return d'"
    let ?rp = "rp"
    let ?Ps = "set ps"
    let ?Rs = "set rs"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?Q = "set (Q d)"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?nfs = "NFS d"
    let ?m = "M d"
    obtain Ps Pr where p: "split_pairs d ps = (Ps,Pr)" by force
    from split_pairs_sound[OF this] have Ps: "set Ps = (?P \<union> ?Pw) \<inter> ?Ps" 
      and Pr: "set Pr = (?P \<union> ?Pw) - ?Ps" by auto
    obtain Rs Rr where r: "split_rules d rs = (Rs,Rr)" by force
    from split_rules_sound[OF this] have Rs: "set Rs = (?R \<union> ?Rw) \<inter> ?Rs" 
      and Rr: "set Rr = (?R \<union> ?Rw) - ?Rs" and Rs_sub: "set Rs \<subseteq> ?R \<union> ?Rw" by auto
    let ?urm = "get_innermost_strict_repl_map_dpp I d Rs"
    obtain fs \<mu> info where urm: "?urm = (fs,\<mu>,info)" by (cases ?urm, auto)
    let ?\<mu> = "rel_impl.mono_af ?rp"
    let ?cpx = "\<lambda> cm cc. isOK(rel_impl.cpx ?rp cm cc)"
    let ?af = "rel_impl.af ?rp"
    note ok = ok[unfolded mono_urm_redpair_proc_def, simplified, simplified p r split urm]
    from ok have valid: "isOK (rel_impl_redpair rp)" 
      and NS: "isOK (rel_impl_ns ?rp (Pr @ Rr))"
      and S: "isOK(rel_impl_s ?rp (Ps @ Rs))" 
      and inn: "NF_terms ?Q \<subseteq> NF_trs (?R \<union> ?Rw)"
      and wfR: "wf_trs (?R \<union> ?Rw)"
      and wfP: "wf_trs (?P \<union> ?Pw)"
      and d': "d' = delete_pairs_rules d ps rs" by (auto simp: rel_impl_list)
    from rel_impl_redpair[OF assms(1) valid S NS, of undefined undefined]
    obtain S NS where S: "set Ps \<subseteq> S" "set Rs \<subseteq> S"
      and NS: "set Pr \<union> set Rr \<subseteq> NS" 
      and rt: "compat_redpair_order S NS" 
      and \<mu>: "af_monotone ?\<mu> S" 
      by (auto simp: Pr Ps Rr Rs)
    interpret compat_redpair_order S NS by fact
    have NSR: "?R \<union> ?Rw - set Rs \<subseteq> NS" using NS unfolding Rr Rs by auto
    have NSP: "?P \<union> ?Pw \<subseteq> NS \<union> S" using NS S(1) unfolding Pr Ps by auto
    note urm = get_innermost_strict_repl_map_dpp[OF I, of d, unfolded dpp_spec_sound, 
      OF inn wfP wf_trs_imp_wwf_qtrs[OF wfR] Rs_sub urm]
    have \<mu>': "af_subset \<mu> ?\<mu>" using urm ok unfolding af_subset_def by auto
    {
      fix s t \<sigma>
      assume st: "(s, t) \<in> ?P \<union> ?Pw"
      and sQ: "s \<cdot> \<sigma> \<in> NF_terms ?Q"
      from Rs_sub have id: "set Rs \<inter> (?R \<union> ?Rw) = set Rs" by auto
      from urm(2)[OF st sQ] have "usable_replacement_map \<mu> {t \<cdot> \<sigma>} ?nfs (?R \<union> ?Rw) ?Q (set Rs)" .
      then have "usable_replacement_map \<mu> {t \<cdot> \<sigma>} ?nfs (?R \<union> ?Rw) ?Q (set Rs \<inter> (?R \<union> ?Rw))" unfolding id .
    } note urm = this
    note main = urm_mono_redpair_sound[of ?R ?Rw "set Rs" ?P ?Pw "set Ps" ?Q \<mu> ?nfs ?\<mu> ?m,
      OF NSR NSP S inn urm \<mu>' \<mu>]
    let ?d = "(NFS d, M d, set (P d) - set Ps, set (Pw d) - set Ps, set (Q d), set (R d) - set Rs, set (Rw d) - set Rs)"
    from d' Rs Rr Ps Pr have d': "dpp d' = ?d" by auto
    show "finite_dpp (dpp d)" unfolding finite_dpp_def
    proof (rule, elim exE)
      fix s t \<sigma>
      assume "min_ichain (dpp d) s t \<sigma>"
      from main[OF _ _ this[unfolded dpp_sound]] 
      have "\<exists> j. min_ichain ?d (shift s j) (shift t j) (shift \<sigma> j)" .
      with fin[unfolded d'] show False unfolding finite_dpp_def by blast
    qed
  qed
qed


lemma (in tp_spec) rule_removal_tt:
  assumes rp: "rel_impl rp"
  shows "sound_tt_impl (rule_removal_tt I rp rs)"
proof 
  fix trs trs'
  assume fin: "SN_qrel (qreltrs trs')"
  and ok: "rule_removal_tt I rp rs trs = return trs'"
  let ?rp = "rp"
  let ?Rs = "set rs"
  let ?Q = "set (Q trs)"
  let ?R = "set (R trs)"
  let ?Rw = "set (Rw trs)"
  let ?nfs = "NFS trs"
  show "SN_qrel (qreltrs trs)"
  proof (cases "split_rules trs rs")
    case (Pair Rs Rr) 
    from split_rules_sound[OF this] have Rs: "set Rs = (?R \<union> ?Rw) \<inter> ?Rs" 
      and Rr: "set Rr = (?R \<union> ?Rw) - ?Rs" by auto
    note ok = ok[unfolded rule_removal_tt_def,simplified, simplified Pair, simplified]
    from ok have valid: "isOK (rel_impl_mono_redpair rp Rs Rr)"
      and orient: "isOK (rel_impl_s rp Rs)" "isOK (rel_impl_ns rp Rr)" 
      and trs': "trs' = delete_rules trs rs" by auto
    from rel_impl_mono_redpair[OF rp valid orient, of undefined undefined]
    obtain S NS NST where S: "(?R \<union> ?Rw) \<inter> ?Rs \<subseteq> S" 
      and NS: "?R \<union> ?Rw - ?Rs \<subseteq> NS" and "mono_redtriple_order S NS NST" 
      by (auto simp: Rr Rs)
    interpret mono_redtriple_order S NS NST by fact
    have proc: "mono_redpair_tt S NS ?Rs (?nfs,?Q,?R,?Rw) (?nfs,?Q,?R-?Rs,?Rw-?Rs)" using NS S ctxt_S by auto
    note fin =  fin[unfolded trs' delete_R_Rw_sound]
    show ?thesis unfolding trs' qreltrs_sound
      by (rule rel_tt[OF mono_redpair_tt _ fin], rule proc)
  qed
qed

lemma rule_shift_complexity_tt:
  assumes "tp_spec I"
  and rp: "rel_impl rp"
  and res: "rule_shift_complexity_tt I rp Rdelete cm cc tp = return tp'"
  and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  interpret tp_spec I by fact
  note res = res[unfolded rule_shift_complexity_tt_def Let_def, simplified]
  let ?rp = rp
  let ?R = "set (R tp)"
  let ?Rw = "set (Rw tp)"
  let ?D = "ceta_list_diff (R tp) Rdelete"
  let ?RwD = "Rw tp @ ?D"
  let ?nfs = "NFS tp"
  let ?Q = "qrstep ?nfs (set (Q tp))"
  from res have valid: "isOK (rel_impl_mono_redpair rp Rdelete ?RwD)"
    and S: "isOK(rel_impl_s rp Rdelete)" 
    and NS: "isOK(rel_impl_ns rp ?RwD)"
    by (auto simp: rel_impl_list)
  let ?cpx = "rel_impl.cpx rp cm"
  let ?Cpx = "\<lambda> cm cc. isOK(rel_impl.cpx rp cm cc)"
  from res have tp': "tp' = mk ?nfs (Q tp) ?D (list_union (Rw tp) Rdelete)" by simp
  from cpx[unfolded tp', simplified] 
  have bound: "deriv_bound_measure_class (relto (?Q (?R - set Rdelete)) (?Q (?Rw \<union> set Rdelete))) cm cc" .
  from res have cpx: "isOK(?cpx cc)" by auto
  from rel_impl_mono_redpair[OF rp valid S NS, of cm cc] cpx
  obtain S NS NST where "mono_redtriple_order S NS NST" 
    and S: "set Rdelete \<subseteq> S" and NS: "?Rw \<union> set ?D \<subseteq> NS"   
    and cpx: "deriv_bound_measure_class S cm cc" 
    by auto
  interpret mono_redtriple_order S NS NST by fact
  from rule_shift_complexity[OF ctxt_S S NS cpx, of cc ?nfs "set (Q tp)"] bound 
  have bound: "deriv_bound_measure_class (relto (?Q (set Rdelete \<union> set ?D)) (?Q ?Rw)) cm cc" by simp
  have bound: "deriv_bound_measure_class (relto (?Q ?R) (?Q ?Rw)) cm cc" 
    by (rule deriv_bound_measure_class_mono[OF relto_mono[OF qrstep_mono[OF _ subset_refl] subset_refl] subset_refl subset_refl bound], auto)
  then show ?thesis by simp
qed

end