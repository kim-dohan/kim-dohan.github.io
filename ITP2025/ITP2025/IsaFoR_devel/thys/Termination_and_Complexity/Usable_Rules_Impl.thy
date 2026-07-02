(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Rules_Impl
imports
  Usable_Rules
  Framework.QDP_Framework_Impl
  TRS.Tcap_Impl
  TRS.Q_Restricted_Rewriting_Impl
  Ord.Term_Order_Impl
begin

fun matchCapRMBelow :: "('f \<times> nat \<Rightarrow> ('f,'v)rules) \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "matchCapRMBelow rm l (Fun f ts) = Ground_Context.match (GCFun f (map (tcapRM2 rm) ts)) l"

lemma matchCapRMBelow:
  assumes noLeftVars: "\<And> lr. lr \<in> set R \<Longrightarrow> is_Fun (fst lr)"
    and rm: "\<And>f n. set (rm (f, n)) = {(l, r). (l, r) \<in> set R \<and> root l = Some (f, n)}"
  shows "matchCapRMBelow rm l (Fun f ts) = match_tcap_below l (set R) (Fun f ts)"
proof -
  from tcapRM2_sound[OF noLeftVars rm] have id: "tcapRM2 rm = tcap (set R)" 
    by (intro ext, auto)
  show ?thesis unfolding matchCapRMBelow.simps match_tcap_below.simps id ..
qed

fun
  check_ur_closed_term_rm_af :: "(('f \<times> nat) \<Rightarrow> ('f, 'v) rules) \<Rightarrow> ('f:: showl, 'v:: showl) rules \<Rightarrow> 'f af \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
where
  "check_ur_closed_term_rm_af _ _ _ (Var x) = succeed" |
  "check_ur_closed_term_rm_af rm ur \<pi> (Fun f ts) = do {
     let n = length ts;
     let pi = \<pi> (f, n);
     check_allm_index (\<lambda>t i. if i \<in> pi then check_ur_closed_term_rm_af rm ur \<pi> t else succeed) ts;
     check_allm (\<lambda>lr.
       check (lr \<in> set ur \<or> \<not> matchCapRMBelow rm (fst lr) (Fun f ts)) 
        (showsl_lit (STR ''due to the subterm '') \<circ> showsl (Fun f ts) \<circ> showsl_lit (STR '' of some usable rhs, rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' should be usable.''))
     ) (rm (f,n))
   }"


lemma check_ur_closed_term_rm_af_sound:
  assumes noLeftVars: "\<And>lr. lr \<in> set R \<Longrightarrow> is_Fun (fst lr)"
  and rm: "\<And>f n. set (rm (f,n)) = {(l, r). (l, r) \<in> set R \<and> root l = Some (f, n)}"
  and check: "isOK(check_ur_closed_term_rm_af rm ur \<pi> t)" 
    and tus: "funas_term t \<subseteq> us"
  shows "ur_closed_term_af (set R) (set ur) us \<pi> t"
using check tus proof (induct t)
  case (Fun f ts)
  from Fun(3) have fus: "(f, length ts) \<in> us" by auto
  from Fun(3) have "\<forall> i < length ts. funas_term (ts ! i) \<subseteq> us" by force
  with Fun(1) Fun(2)
  have rls: "\<forall> (l,r) \<in> set (rm (f,length ts)). (l,r) \<in> set ur \<or> \<not> matchCapRMBelow rm l (Fun f ts)"
    and ind: " (\<forall>i<length ts. i \<in> \<pi> (f, (length ts)) \<longrightarrow> ur_closed_term_af (set R) (set ur) us \<pi> (ts ! i))" by (auto simp: Let_def) 
  have "\<forall> (l,r) \<in> set R. (l,r) \<in> set ur \<or> \<not> matchCapRMBelow rm l (Fun f ts)" (is "\<forall>(l, r) \<in> set R. ?P l r") 
  proof
    fix l r
    assume lr: "(l, r) \<in> set R"
    show "?P l r"
    proof (cases "(l, r) \<in> set (rm (f, length ts))")
      case True
      with rls show ?thesis by auto
    next
      case False
      from noLeftVars[OF lr] obtain g ss where l: "l = Fun g ss" by (cases l, auto)
      with rm False lr have "\<not> (f = g \<and> length ss = length ts)" by auto
      with l rm have "\<not> matchCapRMBelow rm l  (Fun f ts)" by (auto simp: Ground_Context.match_def)
      with rls show ?thesis by auto
    qed
  qed
  with ind fus show ?case
    using matchCapRMBelow[OF noLeftVars rm] by auto
qed simp

definition
  check_ur_P_closed_rm_af ::
    "('f \<times> nat \<Rightarrow> ('f,'v)rules) \<Rightarrow> ('f :: showl, 'v :: showl) rules \<Rightarrow> 'f af \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "check_ur_P_closed_rm_af rm ur \<pi> P \<equiv> do {
       check_allm (\<lambda>lr. check_ur_closed_term_rm_af rm ur \<pi> (snd lr)) ur
         <+? (\<lambda>s. showsl_lit (STR ''error when checking closure properties of rhs of usable rules\<newline>'') \<circ> s);
       check_allm (\<lambda>st. check_ur_closed_term_rm_af rm ur \<pi> (snd st)) P
         <+? (\<lambda>s. showsl_lit (STR ''error when checking closure properties of rhs of DPs\<newline>'') \<circ> s)
     }"

lemma check_ur_P_closed_rm_af_sound:
  assumes noLeftVars: "\<And>lr. lr \<in> set R \<Longrightarrow> is_Fun (fst lr)"
  and rm: "\<And>f n. set (rm (f, n)) = {(l, r). (l, r) \<in> set R \<and> root l = Some (f, n)}"
  and check: "isOK(check_ur_P_closed_rm_af rm ur \<pi> P)"
    and us: "(\<Union>((funas_term o snd) ` (set ur \<union> set P))) \<subseteq> us"
  shows "ur_closed_af (set R) (set ur) us \<pi> \<and> ur_P_closed_af (set R) (set ur) us \<pi> (set P)"
proof -
  note closure = check_ur_closed_term_rm_af_sound[OF noLeftVars rm]
  {
    fix l r
    assume lr: "(l, r) \<in> set ur"
    with us have rus: "funas_term r \<subseteq> us" by force
    from closure[OF _ _ rus] check lr
    have "ur_closed_term_af (set R) (set ur) us \<pi> r" unfolding check_ur_P_closed_rm_af_def by auto
  } note part1 = this
  {
    fix l r
    assume lr: "(l,r) \<in> set P"
    with us have rus: "funas_term r \<subseteq> us" by force
    from closure[OF _ _ rus] check lr
    have "ur_closed_term_af (set R) (set ur) us \<pi> r" unfolding check_ur_P_closed_rm_af_def by auto
  } note part2 = this
  from part1 part2 show ?thesis by auto
qed

definition
  mono_ur_redpair_proc ::
    "('dpp, 'f, 'v) dpp_ops \<Rightarrow> ('f:: showl, 'v:: showl) rel_impl \<Rightarrow> 
     ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 'dpp proc"
where
  "mono_ur_redpair_proc I rp Premove Rrem ur dpp = (let 
       R = dpp_ops.rules I dpp;
       Ur = set ur;
       non_ur = filter (\<lambda> r. r \<notin> Ur) R;
       Rremove = non_ur @ Rrem
     in 
check_return (do {
     check (dpp_ops.minimal I dpp) (showsl_lit (STR ''minimality required''));
     check (dpp_ops.nfs I dpp \<longrightarrow> \<not> dpp_ops.Q_empty I dpp \<longrightarrow> dpp_ops.wwf_rules I dpp) (showsl_lit (STR ''well formedness required''));
     let P = dpp_ops.pairs I dpp;
     let us = \<Union> (set (map (funas_term o snd) (P @ ur)));
     let RR = set Rremove;
     let filt = (\<lambda> lr. (\<forall> f \<in> funas_term (fst lr). f \<in> us));
     let (pms, pns) = dpp_ops.split_pairs I dpp Premove;
     let (ps, pnwf) = partition filt pms;
     let (urms, urns) = partition (\<lambda> u. u \<in> RR) ur;
     let (urs, urnwf) = partition filt urms;
     let rm = dpp_ops.rules_map I dpp;          
     rel_impl_mono_ce_redpair rp (ps @ urs) (urns @ urnwf @ pns @ pnwf);
     check_ur_P_closed_rm_af rm ur full_af P;
     check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''variables as lhss not allowed''))) (dpp_ops.rules I dpp);
     rel_impl_ns rp (urns @ urnwf)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') \<circ> s);
     rel_impl_s rp urs
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') \<circ> s);
     rel_impl_ns rp (pns @ pnwf)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s);
     rel_impl_s rp ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the monotonic reduction pair processor with the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s))
   (dpp_spec.delete_pairs_rules I dpp Premove Rremove))"

context dpp_spec
begin

lemma mono_ur_redpair_proc:
  assumes rp: "rel_impl rp"
  shows "sound_proc_impl (mono_ur_redpair_proc I rp ps rr ur)"
proof 
  fix d d'
  assume fin: "finite_dpp (dpp d')"
    and ok: "mono_ur_redpair_proc I rp ps rr ur d = return d'"
  define rs where "rs = filter (\<lambda>r. r \<notin> set ur) (rules d) @ rr" 
  let ?S = "set ps"
  let ?P = "set (P d)"
  let ?Pw = "set (Pw d)"
  let ?S' = "(?P \<union> ?Pw) \<inter> ?S"
  let ?Pb = "set (dpp_ops.pairs I d)"
  let ?PP = "?P \<union> ?Pw"
  let ?Q = "set (Q d)"
  let ?R = "set (R d)"
  let ?Rw = "set (Rw d)"
  let ?Sr = "set rs"
  let ?Rb = "set (dpp_ops.rules I d)"
  let ?RR = "set (dpp_ops.R I d @ dpp_ops.Rw I d)"
  let ?RR' = "set (dpp_ops.R I d) \<union> set (dpp_ops.Rw I d)"
  have RR': "?RR' = ?RR" by auto
  let ?nfs = "NFS d"
  let ?m = "M d"
  note ok = ok[unfolded mono_ur_redpair_proc_def Let_def, folded rs_def]
  have RR_conv: "?RR = ?Rb" unfolding dpp_spec_sound by auto
  have PP_conv: "?PP = ?Pb" unfolding dpp_spec_sound by auto
  obtain us where us: "us = \<Union> ( set (map (funas_term o snd) (dpp_ops.pairs I d @ ur)))" by auto
  let ?filt = "\<lambda> lr. (\<forall> f \<in> funas_term (fst lr). f \<in> us)"
  let ?WF = "{lr. ?filt lr}"
  obtain Pms Pns where p1: "dpp_ops.split_pairs I d ps = (Pms,Pns)" by force
  obtain Ps Pnwf where p2: "partition ?filt Pms = (Ps,Pnwf)" by force
  obtain Rms Rns where r1: "partition (\<lambda> r. r \<in> set rs) ur = (Rms,Rns)" by force
  obtain Rs Rnwf where r2: "partition ?filt Rms = (Rs,Rnwf)" by force    
  from r1 r2 have ur: "set ur = set Rs \<union> set Rnwf \<union> set Rns" and Rs: "set Rs = (set ur \<inter> set rs) \<inter> ?WF" by auto
  from split_pairs_sound[OF p1] have Pms: "set Pms = (?P \<union> ?Pw) \<inter> ?S" and Pns: "set Pns = (?P \<union> ?Pw) - ?S" by auto
  from p2 have Ps: "set Ps = ((?P \<union> ?Pw) \<inter> ?S) \<inter> ?WF" and Pnwf: "set Pnwf = ((?P \<union> ?Pw) \<inter> ?S) - ?WF" unfolding Pms[symmetric] by auto
  note P = Ps Pnwf Pns
  note ok = ok[unfolded p1 r1 split p2[unfolded us] r2[unfolded us], simplified]
  let ?\<pi> = "full_af"
  let ?all = "(Ps @ Rs) @ (Rns @ Rnwf @ Pns @ Pnwf) @ []"
  from ok have valid: "isOK(rel_impl_mono_ce_redpair rp (Ps @ Rs) (Rns @ Rnwf @ Pns @ Pnwf))" 
      and compat: "isOK(check_ur_P_closed_rm_af (dpp_ops.rules_map I d) ur ?\<pi> (dpp_ops.pairs I d))"
      and NS: "isOK (rel_impl_ns rp (Rns @ Rnwf @ Pns @ Pnwf))"
      and S: "isOK(rel_impl_s rp (Ps @ Rs))" 
      and d': "d' = dpp_spec.delete_pairs_rules I d ps rs"
      and vars: "\<And> l r. (l,r) \<in> ?R \<union> ?Rw \<Longrightarrow> is_Fun l"
      and wwf: "?nfs \<Longrightarrow> ?Q \<noteq> {} \<Longrightarrow> wwf_qtrs ?Q (set (R d) \<union> set (Rw d))"
      and m: ?m by (auto simp: rel_impl_list)
  let ?us = "(\<Union> ( (funas_term o snd) ` (set ur \<union> ?Pb)))"
  have ur_cl: "ur_closed_af ?RR' (set ur) ?us ?\<pi> \<and> 
    ur_P_closed_af ?RR' (set ur) ?us ?\<pi> ?PP " (is "?ur1 \<and> ?ur2")
    unfolding RR' RR_conv PP_conv
  by (rule check_ur_P_closed_rm_af_sound[OF _ _ compat subset_refl], insert vars,  
      unfold dpp_spec_sound, force+)
  then have ?ur1 and ?ur2 by auto
  from rel_impl_mono_ce_redpair[OF rp valid S NS]
  obtain S NS NST where "mono_ce_af_redtriple_order S NS NST full_af" 
    and S: "set Ps \<union> set Rs \<subseteq> S" and NS: "set Rns \<union> set Rnwf \<union> set Pns \<union> set Pnwf \<subseteq> NS"
    by auto
  then interpret mono_ce_af_redtriple_order S NS NST full_af by simp
  from S NS have ur: "set ur \<subseteq> NS \<union> S" unfolding ur by auto
  have P: "?P \<union> ?Pw = set Ps \<union> set Pns \<union> set Pnwf" unfolding P by blast
  from S NS have p: "?P \<union> ?Pw \<subseteq> NS \<union> S" unfolding P by auto
  let ?NWF = "{lr | lr. \<not> funas_term (fst lr) \<subseteq> ?us}"
  have swap: "set ur \<union> ?Pb = ?Pb \<union> set ur" by auto
  have "?S' - ?NWF \<subseteq> set Ps" unfolding Ps us pairs_sound[symmetric] swap by auto
  also have "... \<subseteq> S" using S by auto
  finally have Ps: "?S' - ?NWF \<subseteq> S" .
  have "(?Sr \<inter> set ur) - ?NWF = (set ur \<inter> ?Sr) - ?NWF" by auto
  also have "... \<subseteq> set Rs" unfolding Rs us swap by auto
  also have "... \<subseteq> S" using S by auto
  finally have Rs: "(?Sr \<inter> set ur) - ?NWF \<subseteq> S" .
  note proc = mono_redpair_ur_sound[OF _ ur p Ps Rs \<open>?ur1\<close> \<open>?ur2\<close> m wwf]
  show "finite_dpp (dpp d)"
    unfolding finite_dpp_def
  proof(rule, elim exE)
    fix s t \<sigma>
    assume "min_ichain (dpp_ops.dpp I d) s t \<sigma>"
    from proc[OF _ _ _ this[unfolded dpp_spec_sound]]
    obtain i where chain: "min_ichain (?nfs,?m,?P - ?S',?Pw - ?S',?Q,?R - ?Sr,?Rw - ?Sr) (shift s i) (shift t i) (shift \<sigma> i)" 
      by auto
    have "min_ichain (?nfs,?m,?P - ?S,?Pw - ?S,?Q,?R - ?Sr,?Rw - ?Sr) (shift s i) (shift t i) (shift \<sigma> i)" 
      by (rule min_ichain_mono[OF chain], auto)
    with fin[unfolded d' delete_simps finite_dpp_def]
    show False by blast
  qed
qed
end


end