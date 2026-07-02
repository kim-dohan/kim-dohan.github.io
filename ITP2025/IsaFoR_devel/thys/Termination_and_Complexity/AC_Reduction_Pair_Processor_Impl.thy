(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory AC_Reduction_Pair_Processor_Impl
imports
  AC_Reduction_Pair_Processor
  Framework.AC_Dependency_Pair_Problem_Spec
  Framework.AC_Termination_Problem_Spec
  Ord.Term_Order_Impl
  Usable_Rules_Impl
  AC_TRS.AC_Rewriting_Impl
begin

definition
  ac_mono_ur_redpair_proc ::
    "('dpp, 'f, 'v) ac_dpp_ops \<Rightarrow> ('f:: showl, 'v:: showl) rel_impl \<Rightarrow> 
     ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 'dpp proc"
where
  "ac_mono_ur_redpair_proc I rp P_remove R_remove ur dpp = check_return (do {
     let P = ac_dpp_ops.pairs I dpp;
     let R = ac_dpp_ops.rules I dpp;
     let E = ac_dpp_ops.E I dpp;
     let Premove = set P_remove;
     let Rremove = set R_remove;
     let us = \<Union> (set (map (funas_term o snd) (P @ ur)));
     let filt = (\<lambda> lr. (\<forall> f \<in> funas_term (fst lr). f \<in> us));
     let (ps, pns) = partition (\<lambda> lr. lr \<in> Premove \<and> filt lr) P;
     let (urs, urns) = partition (\<lambda> lr. lr \<in> Rremove \<and> filt lr) ur;
     let rm = ac_dpp_ops.eq_rules_map I dpp;
     rel_impl_mono_ce_redpair rp (ps @ urs) (urns @ pns);
     check_symmetric_AC_theory E 
       <+? (\<lambda> s. showsl_lit (STR ''usable rules demand symmetric AC theory\<newline>'') o s);
     check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''variables as lhss not allowed''))) 
       (ac_dpp_ops.R I dpp @ ac_dpp_ops.Rw I dpp);
     check_ur_P_closed_rm_af rm ur full_af P;
     rel_impl_ns rp urns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') o s);
     rel_impl_s rp urs
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') o s);
     rel_impl_ns rp pns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') o s);
     rel_impl_s rp ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the monotonic AC reduction pair processor with usable rules and the following\<newline>'') 
       o rel_impl.desc rp o showsl_nl o s))
   (ac_dpp_ops.delete_pairs_rules I dpp P_remove R_remove)"

lemma (in ac_dpp_spec) ac_mono_ur_redpair_proc:
  assumes rp: "rel_impl rp"
  shows "sound_proc_impl (ac_mono_ur_redpair_proc I rp ps rs ur)"
proof 
  fix d d'
  assume fin: "finite_rel_dpp (ac_dpp d')"
    and ok: "ac_mono_ur_redpair_proc I rp ps rs ur d = return d'"
  let ?P = "set (P d)"
  let ?Pw = "set (Pw d)"
  let ?PP = "?P \<union> ?Pw"
  let ?R = "set (R d)"
  let ?Rw = "set (Rw d)"
  obtain us where us: "us = \<Union> ( set (map (funas_term o snd) (ac_dpp_ops.pairs I d @ ur)))" by auto
  let ?filt = "\<lambda> lr. (\<forall> f \<in> funas_term (fst lr). f \<in> us)"
  let ?filtP = "\<lambda> lr. lr \<in> set ps \<and> ?filt lr"
  let ?filtR = "\<lambda> lr. lr \<in> set rs \<and> ?filt lr"
  obtain Ps Pns where p: "partition ?filtP (pairs d) = (Ps,Pns)" by force
  obtain Rs Rns where r: "partition ?filtR ur = (Rs,Rns)" by force
  note ok = ok[unfolded ac_mono_ur_redpair_proc_def Let_def us[symmetric] p split r, simplified]
  let ?\<pi> = "full_af"
  let ?allS = "Ps @ Rs" let ?allNS = "Rns @ Pns"
  from ok have valid: "isOK(rel_impl_mono_ce_redpair rp ?allS ?allNS)" 
      and compat: "isOK(check_ur_P_closed_rm_af (ac_dpp_ops.eq_rules_map I d) ur ?\<pi> (ac_dpp_ops.pairs I d))"
      and NS: "isOK (rel_impl_ns rp ?allNS)"
      and S: "isOK(rel_impl_s rp ?allS)" 
      and var: "(\<forall>(l, r)\<in>set (R d) \<union> (set (Rw d)). is_Fun l)"
      and AC: "AC_theory (set (E d))"
      and sym: "symmetric_trs (set (E d))"
      and d': "d' = ac_dpp_ops.delete_pairs_rules I d ps rs"
    by (auto simp: rel_impl_list)
  let ?E = "set (E d)"
  let ?RE = "?R \<union> ?Rw \<union> ?E"
  have id: "?PP = set (pairs d)" "?RE = set (R d @ Rw d @ E d)" by auto
  have ur_cl: "ur_closed_af ?RE (set ur) us ?\<pi> \<and> 
    ur_P_closed_af ?RE (set ur) us ?\<pi> ?PP " (is "?ur1 \<and> ?ur2")
    unfolding us id 
    by (rule check_ur_P_closed_rm_af_sound[OF _ _ compat], insert var AC_theory.no_left_var[OF AC], force+)
  then have ?ur1 and ?ur2 by auto
  from rel_impl_mono_ce_redpair[OF rp valid S NS]
  obtain S NS NST where redt: "mono_ce_af_redtriple_order S NS NST full_af" and S: "set Ps \<union> set Rs \<subseteq> S" 
    and NS: "set Rns \<union> set Pns \<subseteq> NS" 
    by auto
  then interpret mono_ce_af_redtriple_order S NS NST full_af by simp
  have redt: "mono_ce_af_redtriple S NS NST full_af" ..
  from partition_filter1[of ?filtP "pairs d", unfolded p] S
  have ps: "set ps \<inter> ?PP - {lr |lr. \<not> funas_term (fst lr) \<subseteq> us} \<subseteq> S" by auto
  from partition_filter1[of ?filtR ur, unfolded r] S
  have rs: "set rs \<inter> set ur - {lr |lr. \<not> funas_term (fst lr) \<subseteq> us} \<subseteq> S" by auto
  from S NS have ur: "set ur \<subseteq> NS \<union> S" using partition_set[OF r] by auto
  from S NS have p: "?PP \<subseteq> NS \<union> S" using partition_set[OF p] by auto
  note fin = fin[unfolded d' delete_pairs_rules_sound]
  have finR: "finite (?R \<union> ?Rw)" by auto
  show "finite_rel_dpp (ac_dpp d)" unfolding ac_dpp_sound
    by (rule ac_redtriple_mono_proc[OF finR sym AC ur p ps rs redt \<open>?ur1\<close> \<open>?ur2\<close> refl fin])
qed

definition
  ac_ur_redpair_proc ::
    "('dpp, 'f, 'v) ac_dpp_ops \<Rightarrow> ('f:: showl, 'v:: showl) rel_impl \<Rightarrow> 
     ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 'dpp proc"
where
  "ac_ur_redpair_proc I rp P_remove ur dpp = check_return (do {
     let P = ac_dpp_ops.pairs I dpp;
     let R = ac_dpp_ops.rules I dpp;
     let E = ac_dpp_ops.E I dpp;
     let Premove = set P_remove;
     let (ps, pns) = partition (\<lambda> lr. lr \<in> Premove) P;
     let rm = ac_dpp_ops.eq_rules_map I dpp;
     let pi = rel_impl.af rp;
     rel_impl_redtriple rp;
     rel_impl.ce_compat rp;
     check_symmetric_AC_theory E 
       <+? (\<lambda> s. showsl_lit (STR ''usable rules demand symmetric AC theory\<newline>'') o s);
     check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''variables as lhss not allowed''))) 
       (ac_dpp_ops.R I dpp @ ac_dpp_ops.Rw I dpp);
     check_ur_P_closed_rm_af rm ur pi P;
     rel_impl_ns rp ur
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') o s);
     rel_impl_nst rp pns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') o s);
     rel_impl_s rp ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the AC reduction pair processor with usable rules and the following\<newline>'') 
       o rel_impl.desc rp o showsl_nl o s))
   (ac_dpp_ops.delete_pairs_rules I dpp P_remove [])"

lemma (in ac_dpp_spec) ac_ur_redpair_proc:
  assumes rp: "rel_impl rp"
  shows "sound_proc_impl (ac_ur_redpair_proc I rp ps ur)"
proof 
  fix d d'
  assume fin: "finite_rel_dpp (ac_dpp d')"
    and ok: "ac_ur_redpair_proc I rp ps ur d = return d'"
  let ?P = "set (P d)"
  let ?Pw = "set (Pw d)"
  let ?PP = "?P \<union> ?Pw"
  let ?R = "set (R d)"
  let ?Rw = "set (Rw d)"
  obtain Ps Pns where p: "partition (\<lambda> lr. lr \<in> set ps) (pairs d) = (Ps,Pns)" by force
  note ok = ok[unfolded ac_ur_redpair_proc_def Let_def p split, simplified]
  let ?\<pi> = "rel_impl.af rp"
  from ok have valid: "isOK(rel_impl_redtriple rp)"
      and ce: "isOK (rel_impl.ce_compat rp)" 
      and compat: "isOK(check_ur_P_closed_rm_af (ac_dpp_ops.eq_rules_map I d) ur ?\<pi> (ac_dpp_ops.pairs I d))"
      and NS: "isOK (rel_impl_ns rp ur)"
      and NST: "isOK (rel_impl_nst rp Pns)"
      and S: "isOK(rel_impl_s rp Ps)" 
      and var: "(\<forall>(l, r)\<in>set (R d) \<union> (set (Rw d)). is_Fun l)"
      and AC: "AC_theory (set (E d))"
      and sym: "symmetric_trs (set (E d))"
      and d': "d' = ac_dpp_ops.delete_pairs_rules I d ps []"
    by auto
  let ?E = "set (E d)"
  let ?RE = "?R \<union> ?Rw \<union> ?E"
  have id: "?PP = set (pairs d)" "?RE = set (R d @ Rw d @ E d)" by auto
  define us where "us = (\<Union> ( set (map (funas_term o snd) (ac_dpp_ops.pairs I d @ ur))))"
  have ur_cl: "ur_closed_af ?RE (set ur) us ?\<pi> \<and> 
    ur_P_closed_af ?RE (set ur) us ?\<pi> ?PP " (is "?ur1 \<and> ?ur2")
    unfolding us_def id 
    by (rule check_ur_P_closed_rm_af_sound[OF _ _ compat], insert var AC_theory.no_left_var[OF AC], force+)
  then have ?ur1 and ?ur2 by auto
  from rel_impl_redtriple[OF rp valid S NS NST] ce  
  obtain S NS NST where "af_redtriple_order S NS NST ?\<pi>" and S: "set Ps \<subseteq> S" 
    and NS: "set ur \<subseteq> NS" and NST: "set Pns \<subseteq> NST" 
    and ce: "ce_compatible NS" 
    by auto 
  interpret af_redtriple_order S NS NST ?\<pi> by fact
  from S NST have NST: "?PP \<subseteq> NST \<union> S" using partition_set[OF p] by auto
  from S have S: "set ps \<inter> ?PP \<subseteq> S" using partition_filter1[of "\<lambda> lr. lr \<in> set ps" "pairs d", unfolded p]
    by auto
  have redt: "ce_af_redtriple S NS NST ?\<pi>"
    by (unfold_locales, rule ce)
  note fin = fin[unfolded d' delete_pairs_rules_sound, simplified]
  have finR: "finite (?R \<union> ?Rw)" by auto
  show "finite_rel_dpp (ac_dpp d)" unfolding ac_dpp_sound
    by (rule ac_redtriple_proc[OF finR sym AC NS NST S redt \<open>?ur1\<close> \<open>?ur2\<close> refl fin])
qed


definition
  ac_rule_removal ::
    "('tp, 'f, 'v) ac_tp_ops \<Rightarrow> ('f:: showl, 'v:: showl) rel_impl \<Rightarrow> 
     ('f,'v)rules \<Rightarrow> 'tp \<Rightarrow> 'tp result"
where
  "ac_rule_removal I rp R_remove tp = check_return (do {
     let R = ac_tp_ops.R I tp;
     let E = ac_tp_ops.E I tp;
     let Rremove = set R_remove;
     let rns = filter (\<lambda> lr. lr \<notin> Rremove) R;
     rel_impl_mono_redpair rp R_remove (rns @ E);
     rel_impl_ns rp rns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting weak rules\<newline>'') o s);
     rel_impl_ns rp E
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting equations\<newline>'') o s);
     rel_impl_s rp R_remove
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting strict rules\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply AC rule removal with the following\<newline>'') 
       o rel_impl.desc rp o showsl_nl o s))
   (ac_tp_ops.delete_rules I tp R_remove)"

lemma (in ac_tp_spec) ac_rule_removal:
  assumes rp: "rel_impl rp"
  and rr: "ac_rule_removal I rp rs tp = return tp'"
  and SN_tp': "SN (relation_ac_tp (ac_tp_ops.ac_tp I tp'))"
  shows "SN (relation_ac_tp (ac_tp_ops.ac_tp I tp))"
proof -
  let ?A = "set (A tp)"
  let ?C = "set (C tp)"
  let ?R = "set (R tp)"
  let ?E = "set (E tp)"
  let ?Rns = "filter (\<lambda> lr. lr \<notin> set rs) (R tp)"
  interpret aoc_rewriting ?A ?C .
  note rr = rr[unfolded ac_rule_removal_def Let_def split, simplified]
  let ?\<pi> = "rel_impl.af rp"
  from rr have valid: "isOK (rel_impl_mono_redpair rp rs (?Rns @ E tp))" 
    and NS: "isOK (rel_impl_ns rp (?Rns @ E tp))"
    and S: "isOK(rel_impl_s rp rs)" 
    and tp': "tp' = ac_tp_ops.delete_rules I tp rs"
    by (auto simp: rel_impl_list)
  have tp': "ac_tp tp' = (?R - set rs, ?A, ?C)" unfolding tp' delete_rules_sound ..
  from rel_impl_mono_redpair[OF rp valid S NS]
  obtain S NS NST where "mono_redtriple_order S NS NST" and S: "set rs \<subseteq> S" 
    and NS': "set (?Rns @ E tp) \<subseteq> NS" 
    by blast
  from NS' have NS: "set ?Rns \<union> ?E \<subseteq> NS"  by auto
  from S NS have RE: "?R \<union> ?E \<subseteq> NS \<union> S" by auto
  interpret mono_redtriple_order S NS NST by fact
  show ?thesis unfolding SN_relation_ac_tp
    by (rule ac_rule_removal[OF RE S], insert SN_tp'[unfolded tp'], auto simp: relaoc_def SN_rel_defs)
qed

end
