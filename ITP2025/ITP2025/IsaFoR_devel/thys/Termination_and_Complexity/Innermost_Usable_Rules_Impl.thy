(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Innermost_Usable_Rules_Impl
imports
  Innermost_Usable_Rules 
  Icap_Impl
  Framework.QDP_Framework_Impl
  Ord.Term_Order_Impl
  Auxx.Inductive_Set_Impl
begin

definition rule_match_impl where
  "rule_match_impl NFQ e_cap S f ts l \<equiv> case mgu_class (Fun f (map e_cap ts)) l of
     None \<Rightarrow> False
   | Some \<mu> \<Rightarrow> (\<forall> u \<in> set (args l). NFQ (mv_yvar u \<cdot> \<mu>)) \<and> (\<forall> u \<in> set S. NFQ (u \<cdot> \<mu>))"

lemma rule_match_impl_cong: assumes "\<And> t. t \<in> set ts \<Longrightarrow> ecap t = ecap' t"
  shows "rule_match_impl NFQ ecap S f ts = rule_match_impl NFQ ecap' S f ts"
proof -
  from assms have id: "map ecap ts = map ecap' ts"
    by (induct ts, auto)
  show ?thesis 
    by (intro ext, unfold rule_match_impl_def id, auto) 
qed


lemma rule_match_impl: "rule_match_impl (\<lambda> t. t \<in> NF_terms Q) (ecap R Q (set S)) S
  = rule_match R Q ecap (set S)"
  by (intro ext, unfold rule_match_impl_def rule_match_def, auto split: option.split)

definition rule_match_impl_aux where
  "rule_match_impl_aux NFQ S fts l \<equiv> case mgu fts (map_vars_term y_var l) of
     None \<Rightarrow> False
   | Some \<mu> \<Rightarrow> (\<forall> u \<in> set (args l). NFQ (mv_yvar u \<cdot> \<mu>)) \<and> (\<forall> u \<in> set S. NFQ (u \<cdot> \<mu>))"

fun is_ur_closed_term_impl where
  "is_ur_closed_term_impl NFQ e_cap R U S (Var x) = True"
| "is_ur_closed_term_impl NFQ e_cap R U S (Fun f ts) = 
    ((\<forall> t \<in> set ts. is_ur_closed_term_impl NFQ e_cap R U S t) \<and>                
    (\<forall>(l, r) \<in> set R. (l, r) \<in> U \<or> \<not> rule_match_impl NFQ e_cap S f ts l))"


lemma is_ur_closed_term_impl_code[code]: 
 "is_ur_closed_term_impl NFQ e_cap R U S (Var x) = True"
 "is_ur_closed_term_impl NFQ e_cap R U S (Fun f ts) = 
    ((\<forall> t \<in> set ts. is_ur_closed_term_impl NFQ e_cap R U S t) \<and>     
           (let fts = class_to_term (CHR ''z'') (Fun f (map e_cap ts)) in  
              (\<forall> (l,r) \<in> set R. (l,r) \<in> U \<or> \<not> rule_match_impl_aux NFQ S fts l)))"
  unfolding is_ur_closed_term_impl.simps Let_def rule_match_impl_aux_def rule_match_impl_def 
    mgu_class_def by auto

fun is_ur_closed_term_af_impl 
  where "is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S (Var x) = True"
     |  "is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S (Fun f ts) = (let n = length ts; \<pi>f = \<pi> (f,n) in
              ((\<forall> (i,t) \<in> set (zip [0 ..< n] ts). i \<in> \<pi>f \<longrightarrow> is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S t) \<and>                
              (\<forall> (l,r) \<in> set R. (l,r) \<in> U \<or> \<not> rule_match_impl NFQ e_cap S f ts l)))"

lemma is_ur_closed_term_af_impl_code[code]: 
  "is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S (Var x) = True"
  "is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S (Fun f ts) = (let n = length ts; \<pi>f = \<pi> (f,n) in
              ((\<forall> (i,t) \<in> set (zip [0 ..< n] ts). i \<in> \<pi>f \<longrightarrow> is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S t) \<and> 
           (let fts = class_to_term (CHR ''z'') (Fun f (map e_cap ts)) in               
              (\<forall> (l,r) \<in> set R. (l,r) \<in> U \<or> \<not> rule_match_impl_aux NFQ S fts l))))"
  unfolding is_ur_closed_term_af_impl.simps Let_def rule_match_impl_aux_def rule_match_impl_def 
    mgu_class_def by auto

context
  fixes R :: "('f,string)rules" and Q S :: "('f,string)term list"
    and NFQ :: "('f,string)term \<Rightarrow> bool"
    and e_cap :: "('f, string) term  \<Rightarrow> ('f, unit + string) term"
  assumes NFQ: "NFQ = (\<lambda> t. t \<in> NF_terms (set Q))"
    and e_cap: "e_cap = icap (set R) (set Q) (set S)"
begin

lemma rule_match_impl_e_cap[simp]: "rule_match_impl NFQ e_cap S = rule_match (set R) (set Q) icap (set S)"
  unfolding NFQ e_cap by (rule rule_match_impl)

lemma is_ur_closed_term_impl: 
  "is_ur_closed_term_impl NFQ e_cap R U S = is_ur_closed_term' (set R) U (set Q) icap full_af (set S)"
proof -
  let ?is_ur_closed_term = "is_ur_closed_term' (set R) U (set Q) icap full_af"
  {
    fix t
    have "is_ur_closed_term_impl NFQ e_cap R U S t = ?is_ur_closed_term (set S) t"
    proof (induct t)
      case (Fun f ts)
      then have ball: "Ball (set ts) (is_ur_closed_term_impl NFQ e_cap R U S) = 
         (\<forall>i<length ts.
        i \<in> full_af (f, length ts) \<longrightarrow> ?is_ur_closed_term (set S) (ts ! i))" 
        unfolding full_af_def[of "(f,length ts)"] set_conv_nth[of ts] by auto
      show ?case 
        unfolding is_ur_closed_term_impl.simps is_ur_closed_term'.simps
        unfolding rule_match_impl_e_cap ball ..
    qed simp
  } 
  then show ?thesis by (intro ext, auto)
qed

lemma is_ur_closed_term_af_impl: 
  "is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S = is_ur_closed_term' (set R) U (set Q) icap \<pi> (set S)"
proof -
  let ?is_ur_closed_term = "is_ur_closed_term' (set R) U (set Q) icap \<pi>"
  {
    fix t
    have "is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S t = ?is_ur_closed_term (set S) t"
    proof (induct t)
      case (Fun f ts)
      then have ball: "(\<forall> i < length ts. i \<in> \<pi> (f,length ts) \<longrightarrow> is_ur_closed_term_af_impl NFQ e_cap \<pi> R U S (ts ! i)) = 
         (\<forall>i<length ts.
        i \<in> \<pi> (f, length ts) \<longrightarrow> ?is_ur_closed_term (set S) (ts ! i))" (is "?l' = ?r")
        using Fun[unfolded set_conv_nth[of ts]] by auto
      show ?case 
        unfolding is_ur_closed_term_af_impl.simps is_ur_closed_term'.simps Let_def
        unfolding rule_match_impl_e_cap ball[symmetric] set_zip
          by force
    qed simp
  } 
  then show ?thesis by (intro ext, auto)
qed
end

definition is_ur_closed_term_impl_mv 
  where "is_ur_closed_term_impl_mv NFQ e_cap R U S \<equiv> let urc = is_ur_closed_term_impl NFQ e_cap R U (map mv_xvar S) in (\<lambda> t. urc (mv_xvar t))"

definition is_ur_closed_term_af_impl_mv 
  where "is_ur_closed_term_af_impl_mv NFQ e_cap \<pi> R U S \<equiv> let urc = is_ur_closed_term_af_impl NFQ e_cap \<pi> R U (map mv_xvar S) in (\<lambda> t. urc (mv_xvar t))"

lemma is_ur_closed_term_impl_mv: fixes R :: "('f,string)rules" and Q :: "('f,string)term list"
  assumes NFQ: "NFQ = (\<lambda> t. t \<in> NF_terms (set Q))"
  and e_cap: "e_cap = icap (set R) (set Q) (set (map mv_xvar S))"
  shows "is_ur_closed_term_impl_mv NFQ e_cap R U S t = is_ur_closed_term_mv' (set R) U (set Q) icap' full_af (set S) t" 
  unfolding
    is_ur_closed_term_impl_mv_def 
    is_ur_closed_term_impl[OF NFQ e_cap]
    set_map
    is_ur_closed_term_mv_icap' Let_def ..

lemma is_ur_closed_term_af_impl_mv: fixes R :: "('f,string)rules" and Q :: "('f,string)term list"
  assumes NFQ: "NFQ = (\<lambda> t. t \<in> NF_terms (set Q))"
  and e_cap: "e_cap = icap (set R) (set Q) (set (map mv_xvar S))"
  shows "is_ur_closed_term_af_impl_mv NFQ e_cap \<pi> R U S t = is_ur_closed_term_mv' (set R) U (set Q) icap' \<pi> (set S) t" 
  unfolding
    is_ur_closed_term_af_impl_mv_def 
    is_ur_closed_term_af_impl[OF NFQ e_cap]
    set_map
    is_ur_closed_term_mv_icap' Let_def ..

definition is_ur_closed_impl_dpp_mv   :: "('d, 'f :: {compare_order,showl}, string) dpp_ops \<Rightarrow> 'd
  \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> bool"
  where "is_ur_closed_impl_dpp_mv I d U \<equiv>
  let ic = icap_impl_dpp I d;
      qnf = dpp_ops.is_QNF I d;
      r = dpp_ops.rules I d;
      urc = (\<lambda> S. is_ur_closed_term_impl qnf (ic S) r (set U))
    in (\<lambda> S. let S' = map mv_xvar S in (\<lambda> t. urc S' S' (mv_xvar t)))"

definition is_ur_closed_af_impl_dpp_mv   :: "('d, 'f :: {compare_order,showl}, string) dpp_ops \<Rightarrow> 'd \<Rightarrow> 'f af
  \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> bool"
  where "is_ur_closed_af_impl_dpp_mv I d \<pi> U \<equiv>
  let ic = icap_impl_dpp I d;
      qnf = dpp_ops.is_QNF I d;
      r = dpp_ops.rules I d;
      urc = (\<lambda> S. is_ur_closed_term_af_impl qnf (ic S) \<pi> r (set U))
    in (\<lambda> S. let S' = map mv_xvar S in (\<lambda> t. urc S' S' (mv_xvar t)))"

lemma is_ur_closed_impl_dpp_mv:
  fixes I::"('d, 'f::{showl,compare_order}, string) dpp_ops" and d::"'d"
  defines q: "q \<equiv> dpp_ops.Q I d"
      and r: "r \<equiv> dpp_ops.rules I d"
  assumes I: "dpp_spec I"
  shows "is_ur_closed_impl_dpp_mv I d u s t = is_ur_closed_term_mv' (set r) (set u) (set q) icap' full_af (set s) t" 
proof -
  interpret dpp_spec I by fact
  show ?thesis
    unfolding is_ur_closed_term_impl_mv[OF refl refl, symmetric]
      is_ur_closed_impl_dpp_mv_def Let_def is_QNF_sound icap_impl_dpp_icap[OF I] r q 
    unfolding is_ur_closed_term_impl_mv_def Let_def ..
qed    

lemma is_ur_closed_af_impl_dpp_mv:
  fixes I::"('d, 'f::{showl,compare_order}, string) dpp_ops" and d::"'d"
  defines q: "q \<equiv> dpp_ops.Q I d"
      and r: "r \<equiv> dpp_ops.rules I d"
  assumes I: "dpp_spec I"
  shows "is_ur_closed_af_impl_dpp_mv I d \<pi> u s t = is_ur_closed_term_mv' (set r) (set u) (set q) icap' \<pi> (set s) t" 
proof -
  interpret dpp_spec I by fact
  show ?thesis
    unfolding is_ur_closed_term_af_impl_mv[OF refl refl, symmetric]
      is_ur_closed_af_impl_dpp_mv_def Let_def is_QNF_sound icap_impl_dpp_icap[OF I] r q 
    unfolding is_ur_closed_term_af_impl_mv_def Let_def ..
qed    

definition is_ur_closed_af_impl_tp_mv   :: "('d, 'f :: {compare_order,showl}, string) tp_ops \<Rightarrow> 'd \<Rightarrow> 'f af
  \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> bool"
  where "is_ur_closed_af_impl_tp_mv I d \<pi> U =
  (let ic = icap_impl_tp I d;
      qnf = tp_ops.is_QNF I d;
      r = tp_ops.rules I d;
      urc = (\<lambda> S. is_ur_closed_term_af_impl qnf (ic S) \<pi> r (set U))
    in (\<lambda> S. let S' = map mv_xvar S in (\<lambda> t. urc S' S' (mv_xvar t))))"

lemma is_ur_closed_af_impl_tp_mv:
  fixes I::"('d, 'f::{showl,compare_order}, string) tp_ops" and d::"'d"
  defines q: "q \<equiv> tp_ops.Q I d"
      and r: "r \<equiv> tp_ops.rules I d"
  assumes I: "tp_spec I"
  shows "is_ur_closed_af_impl_tp_mv I d \<pi> u s = is_ur_closed_term_mv' (set r) (set u) (set q) icap' \<pi> (set s)" 
proof -
  interpret tp_spec I by fact
  show ?thesis
    unfolding is_ur_closed_term_af_impl_mv[OF refl refl, symmetric]
      is_ur_closed_af_impl_tp_mv_def Let_def is_QNF_sound icap_impl_tp_icap[OF I] r q 
    unfolding is_ur_closed_term_af_impl_mv_def Let_def ..
qed    

definition
  usable_rules_proc ::
    "('dpp, 'f :: {showl,compare_order}, string) dpp_ops \<Rightarrow> 
     ('f,string)rules \<Rightarrow> 'dpp proc"
where
  "usable_rules_proc I U dpp \<equiv> 
    check_return (do {
     check (dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''innermost rewriting required''));
     check (dpp_ops.nfs I dpp \<or> dpp_ops.minimal I dpp \<or> dpp_ops.wwf_rules I dpp) (showsl_lit (STR ''normal form subst, minimality or well-formedness required''));
     let P = dpp_ops.pairs I dpp;
     let urc = is_ur_closed_impl_dpp_mv I dpp U;
     let check_urc = (\<lambda> S t. check (urc S t) (showsl_lit (STR ''term '') \<circ> showsl t \<circ> showsl_lit (STR '' is not closed under usable rules'')));
     let nfs = dpp_ops.nfs I dpp;
     check_allm (\<lambda>(l, r). do {
        (if nfs then succeed else check_subseteq (vars_term_list r) (vars_term_list l) <+? (\<lambda> x. showsl_lit (STR ''variable condition in P violated'')));
        check_urc [l] r
     }) P;       
     check_allm (\<lambda>(l,r). check_urc (args l) r) U
   })
   (dpp_ops.intersect_rules I dpp U)"


lemma usable_rules_proc_main: assumes I: "dpp_spec I"
  and ok: "usable_rules_proc I U d = return d'"
  shows "R_Q_U_ecap (set (dpp_ops.rules I d)) (set (dpp_ops.Q I d)) icap'"
  and "R_Q_U_ecap.usable_rules_precond (set (dpp_ops.rules I d)) (set U) (set (dpp_ops.Q I d)) icap' (dpp_ops.dpp I d)"
proof -
  interpret dpp_spec I by fact
  let ?P = "set (P d)"
  let ?Pw = "set (Pw d)"
  let ?Q = "set (Q d)"
  let ?R = "set (R d)"
  let ?Rw = "set (Rw d)"
  let ?U = "set U"
  let ?Rb = "?R \<union> ?Rw"
  let ?Rb' = "set (rules d)" 
  note ok = ok[unfolded usable_rules_proc_def dpp_spec_sound Let_def
    is_ur_closed_impl_dpp_mv[OF I], simplified] 
  from ok have NF: "NF_terms ?Q \<subseteq> NF_trs ?Rb" and NF': "NF_terms ?Q \<subseteq> NF_trs ?Rb'" by auto
  show "R_Q_U_ecap ?Rb' ?Q icap'"
    by (unfold_locales, rule icap, rule NF')
  interpret R_Q_U_ecap ?Rb' ?U ?Q icap' by fact
  show "usable_rules_precond (dpp_ops.dpp I d)" 
    unfolding dpp_sound
    unfolding usable_rules_precond.simps
  proof (intro allI conjI impI)
    have Rb: "?Rb = ?Rb'" by simp
    show "?Rb \<subseteq> ?Rb'" by simp
  next
    fix l r
    assume lr: "(l,r) \<in> ?P \<union> ?Pw" 
    from lr ok show "is_ur_closed_term_mv full_af {l} r" by auto
    assume "\<not> NFS d"
    with lr ok 
    show "vars_term r \<subseteq> vars_term l" by force
  next
    fix l r
    assume "(l,r) \<in> ?U"
    with ok
    show "is_ur_closed_term_mv full_af (set (args l)) r" by auto    
  qed (insert ok, auto)
qed

  
lemma usable_rules_proc: assumes I: "dpp_spec I"
 shows "dpp_spec.sound_proc_impl I (usable_rules_proc I (U :: ('f :: {showl,compare_order},string)rules))"
proof -
  from assms interpret dpp_spec I .
  show ?thesis
  proof
    fix d d'    
    assume ok: "usable_rules_proc I U d = Inr d'" and fin: "finite_dpp (dpp d')"
    note us = usable_rules_proc_main[OF I ok]    
    let ?Q = "set (Q d)"
    let ?U = "set U"
    interpret R_Q_U_ecap "set (rules d)" ?U ?Q icap' by fact
    note ok = ok[unfolded usable_rules_proc_def dpp_spec_sound Let_def] 
    from ok have d': "d' = intersect_rules d U" by auto
    have d': "dpp d' = (NFS d, M d, set (P d), set (Pw d), ?Q, set (R d) \<inter> ?U, set (Rw d) \<inter> ?U)" 
      unfolding d' unfolding intersect_rules_sound ..
    note fin = fin[unfolded this]
    show "finite_dpp (dpp d)" unfolding dpp_spec_sound
      by (rule usable_rules_proc[OF fin us(2)[unfolded dpp_sound]])
  qed
qed 

definition
  mono_inn_usable_rules_ce_proc ::
    "('dpp, 'f, string) dpp_ops \<Rightarrow> ('f::{showl,compare_order}, string) rel_impl \<Rightarrow> 
     ('f,string)rules \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)rules \<Rightarrow> 'dpp proc"
where
  "mono_inn_usable_rules_ce_proc I rp Premove Rrem ur dpp = (let 
       R = dpp_ops.rules I dpp;
       Ur = set ur;
       non_ur = filter (\<lambda> r. r \<notin> Ur) R;
       Rremove = non_ur @ Rrem
     in check_return (do {
     usable_rules_proc I ur dpp;
     let P = dpp_ops.pairs I dpp;
     let us = \<Union> (set (map (funas_term o snd) (P @ ur)));
     let filt = (\<lambda> lr. (\<forall> f \<in> funas_term (fst lr). f \<in> us));
     let (pms, pns) = dpp_ops.split_pairs I dpp Premove;
     let (ps, pnwf) = partition filt pms;
     let (urms, urns) = partition (\<lambda> u. u \<in> set Rremove) ur;
     let (urs, urnwf) = partition filt urms;
     rel_impl_mono_ce_redpair rp (ps @ urs) (urns @ urnwf @ pns @ pnwf);
     rel_impl_ns rp (urns @ urnwf)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') \<circ> s);
     rel_impl_s rp urs
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting usable rules\<newline>'') \<circ> s);
     rel_impl_ns rp (pns @ pnwf)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s);
     rel_impl_s rp ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the innermost usable rules reduction pair processor with the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s))
   (dpp_spec.delete_pairs_rules I dpp Premove Rremove))"

lemma mono_inn_usable_rules_ce_proc:
  assumes I: "dpp_spec I"
    and rp: "rel_impl rp"
  shows "dpp_spec.sound_proc_impl I (mono_inn_usable_rules_ce_proc I rp ps rr ur)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof
    fix d d'
    assume fin: "finite_dpp (dpp d')"
      and ok: "mono_inn_usable_rules_ce_proc I rp ps rr ur d = return d'"
    define rs where "rs = filter (\<lambda>r. r \<notin> set ur) (rules d) @ rr" 
    let ?S = "set ps"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?S' = "(?P \<union> ?Pw) \<inter> ?S"
    let ?Pb = "set (pairs d)"
    let ?Q = "set (Q d)"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?Sr = "set rs"
    let ?U = "set ur"
    obtain us where us: "us = \<Union> ( set (map (funas_term o snd) (dpp_ops.pairs I d @ ur)))" by auto
    let ?filt = "\<lambda> lr. (\<forall> f \<in> funas_term (fst lr). f \<in> us)"
    let ?WF = "{lr. ?filt lr}"
    note ok = ok[unfolded mono_inn_usable_rules_ce_proc_def Let_def, folded rs_def]

    obtain Pms Pns where p1: "dpp_ops.split_pairs I d ps = (Pms,Pns)" by force
    obtain Ps Pnwf where p2: "partition ?filt Pms = (Ps,Pnwf)" by force
    obtain Rms Rns where r1: "partition (\<lambda> r. r \<in> ?Sr) ur = (Rms,Rns)" by force
    obtain Rs Rnwf where r2: "partition ?filt Rms = (Rs,Rnwf)" by force    
    from r1 r2 have ur: "?U = set Rs \<union> set Rnwf \<union> set Rns" and Rs: "set Rs = (?U \<inter> ?Sr) \<inter> ?WF" by auto
    from split_pairs_sound[OF p1] have Pms: "set Pms = (?P \<union> ?Pw) \<inter> ?S" and Pns: "set Pns = (?P \<union> ?Pw) - ?S" by auto
    from p2 have Ps: "set Ps = ((?P \<union> ?Pw) \<inter> ?S) \<inter> ?WF" and Pnwf: "set Pnwf = ((?P \<union> ?Pw) \<inter> ?S) - ?WF" unfolding Pms[symmetric] by auto
    note P = Ps Pnwf Pns
    note ok = ok[unfolded mono_inn_usable_rules_ce_proc_def Let_def p1 r1 split p2[unfolded us] r2[unfolded us], simplified]
    from ok obtain dpp' where urp: "usable_rules_proc I ur d = return dpp'" by (cases "usable_rules_proc I ur d", auto)
    note urp = usable_rules_proc_main[OF I urp]
    interpret R_Q_U_ecap "set (rules d)" ?U ?Q icap' by fact
    let ?all = "(Ps @ Rs) @ (Rns @ Rnwf @ Pns @ Pnwf) @ []"
    from ok have valid: "isOK(rel_impl_mono_ce_redpair rp (Ps @ Rs) (Rns @ Rnwf @ Pns @ Pnwf))" 
      and NS: "isOK (rel_impl_ns rp (Rns @ Rnwf @ Pns @ Pnwf))"
      and S: "isOK(rel_impl_s rp (Ps @ Rs))" 
      and d': "d' = dpp_spec.delete_pairs_rules I d ps rs"
      by (auto simp: rel_impl_list)
    let ?us = "(\<Union> ( (funas_term o snd) ` (?U \<union> ?Pb)))"
    from rel_impl_mono_ce_redpair[OF rp valid S NS]
    obtain S NS NST where "mono_ce_af_redtriple_order S NS NST full_af" 
      and S: "set Ps \<union> set Rs \<subseteq> S" and NS: "set Rns \<union> set Rnwf \<union> set Pns \<union> set Pnwf \<subseteq> NS"
      by auto
    then interpret mono_ce_af_redtriple_order S NS NST full_af by simp
    have redp: "mono_ce_af_redtriple S NS NST full_af" ..
    from S NS have ur: "?U \<subseteq> NS \<union> S" unfolding ur by auto
    have P: "?P \<union> ?Pw = set Ps \<union> set Pns \<union> set Pnwf" unfolding P by blast
    from S NS have p: "?P \<union> ?Pw \<subseteq> NS \<union> S" unfolding P by auto
    let ?NWF = "{lr | lr. \<not> funas_term (fst lr) \<subseteq> ?us}"
    have swap: "?U \<union> ?Pb = ?Pb \<union> ?U" by auto
    have "?S' - ?NWF \<subseteq> set Ps" unfolding Ps us pairs_sound[symmetric] swap by auto
    also have "... \<subseteq> S" using S by auto
    finally have Ps: "?S' - ?NWF \<subseteq> S" .
    have "(?Sr \<inter> ?U) - ?NWF = (?U \<inter> ?Sr) - ?NWF" by auto
    also have "... \<subseteq> set Rs" unfolding Rs us swap by auto
    also have "... \<subseteq> S" using S by auto
    finally have Rs: "(?Sr \<inter> ?U) - ?NWF \<subseteq> S" .
    from p ur have or: "?P \<union> ?Pw \<union> ?U \<subseteq> NS \<union> S" by auto
    show "finite_dpp (dpp d)" unfolding dpp_sound
      by (rule usable_rules_finite_dpp_ce[OF urp(2)[unfolded dpp_sound] redp 
            or _ _ refl fin[unfolded d' delete_simps]], insert Rs Ps, auto)
  qed
qed


fun ur_term :: "('f,string)trs \<Rightarrow> ('f,string)terms \<Rightarrow> ('f,string)cap_fun \<Rightarrow> 'f af \<Rightarrow> ('f,string)terms \<Rightarrow> ('f,string)term \<Rightarrow> ('f,string)trs"
  where "ur_term R Q ecap \<pi> S (Var x) = {}"
     |  "ur_term R Q ecap \<pi> S (Fun f ts) = (let rec = map (ur_term R Q ecap \<pi> S) ts in 
             \<Union>{rec ! i | i. i < length ts \<and> i \<in> \<pi> (f,length ts)} \<union> { (l,r) | l r. (l,r) \<in> R 
             \<and> rule_match R Q ecap S f ts l })"

lemma ur_term_subset: "ur_term R Q ecap \<pi> S t \<subseteq> R"
  by (induct t, auto simp: Let_def, auto simp: set_conv_nth)

lemma is_ur_closed'_ur_term: assumes U: "ur_term R Q ecap \<pi> S t \<subseteq> U"
  shows "is_ur_closed_term' R U Q ecap \<pi> S t"
  using U 
proof (induct t)
  case (Fun f ts)
  let ?match = "rule_match R Q ecap S f ts"
  {
    fix l r
    assume "(l,r) \<in> R"
    with Fun(2)[simplified]
    have "(l,r) \<in> U \<or> \<not> ?match l" by blast
  } note two = this
  show ?case unfolding is_ur_closed_term'.simps
  proof (intro conjI ballI allI impI)
    fix i
    assume i: "i < length ts"
    and \<pi>: "i \<in> \<pi> (f,length ts)"
    from i have mem: "ts ! i \<in> set ts" by auto
    from Fun(2)[simplified] i \<pi> have sub: "map (ur_term R Q ecap \<pi> S) ts ! i \<subseteq> U"
      by blast
    show "is_ur_closed_term' R U Q ecap \<pi> S (ts ! i)"
      by (rule Fun(1)[OF mem], insert sub i, simp)
  qed (insert two, auto)
qed auto

lemma ur_term_is_ur_closed': assumes U: "is_ur_closed_term' R U Q ecap \<pi> S t"
  shows "ur_term R Q ecap \<pi> S t \<subseteq> U"
  using U
proof (induct t)
  case (Var x) then show ?case by auto
next
  case (Fun f ts)
  let ?match = "rule_match R Q ecap S f ts"
  {
    fix l r
    assume "(l,r) \<in> \<Union> {map (ur_term R Q ecap \<pi> S) ts ! i | i. i < length ts \<and> i \<in> \<pi> (f,length ts)}"
    then obtain i where i: "i < length ts" and \<pi>: "i \<in> \<pi> (f,length ts)" and lr: "(l,r) \<in> map (ur_term R Q ecap \<pi> S) ts ! i" by auto
    from lr i have lr: "(l,r) \<in> ur_term R Q ecap \<pi> S (ts ! i)" by auto
    also have "... \<subseteq> U"
      by (rule Fun(1), insert \<pi> i Fun(2), auto)
    finally have "(l,r) \<in> U" .
  } note one = this
  {
    fix l r
    assume "(l,r) \<in> { u. \<exists> l r. u = (l,r) \<and> (l,r) \<in> R \<and> ?match l}"
    then have lr: "(l,r) \<in> R" and P: "?match l" by auto
    with Fun(2)
    have "(l,r) \<in> U" by auto
  } note two = this
  show ?case using one two by auto
qed

lemma ur_term_least_is_ur_closed': "ur_term R Q ecap \<pi> S t = 
  (LEAST U. is_ur_closed_term' R U Q ecap \<pi> S t)"
  by (rule Least_equality[symmetric],
    rule is_ur_closed'_ur_term[OF subset_refl],
    rule ur_term_is_ur_closed')

fun ur_term_impl 
  where "ur_term_impl NFQ e_cap R \<pi> S (Var x) = []"
     |  "ur_term_impl NFQ e_cap R \<pi> S (Fun f ts) = (let n = length ts; rec = map (ur_term_impl NFQ e_cap R \<pi> S) ts in 
             remdups (concat (map (\<lambda> (i,urs). if i \<in> \<pi> (f,n) then urs else []) (zip [0 ..< n] rec)) @ filter (\<lambda> (l,r). 
             rule_match_impl NFQ e_cap S f ts l) R))"

lemma ur_term_impl: fixes R Q ecap
  assumes NFQ: "NFQ = (\<lambda> t. t \<in> NF_terms Q)"
  and e_cap: "e_cap = ecap (set R) Q (set S)"
  shows "set (ur_term_impl NFQ e_cap R \<pi> S t) = ur_term (set R) Q ecap \<pi> (set S) t"
proof (induct t)
  case (Var x)
  show ?case by simp
next
  case (Fun f ts)
  let ?impl = "ur_term_impl NFQ e_cap R \<pi> S"
  let ?sem = "ur_term (set R) Q ecap \<pi> (set S)"
  have rm: "rule_match_impl NFQ e_cap S = rule_match (set R) Q ecap (set S)"
    unfolding NFQ e_cap by (rule rule_match_impl)
  have cong: "\<And> a b c d. c = d \<Longrightarrow> a = b \<Longrightarrow> a \<union> c = b \<union> d" by auto
  have "set (concat
          (map (\<lambda>(i, urs). if i \<in> \<pi> (f, length ts) then urs else [])
            (zip [0..<length ts] (map (ur_term_impl NFQ e_cap R \<pi> S) ts)))) = 
        {x. (\<exists> i. i < length ts \<and> i \<in> \<pi> (f, length ts) \<and> x \<in> set (?impl (ts ! i)))}"
    by (auto simp: set_zip)
  also have "\<dots> = 
    {x. (\<exists> i. i < length ts \<and> i \<in> \<pi> (f, length ts) \<and> x \<in> ?sem (ts ! i))}"
    using Fun[unfolded set_conv_nth[of ts]] by blast
  also have "\<dots> = \<Union>{map ?sem ts ! i |i. i < length ts \<and> i \<in> \<pi> (f, length ts)}" by auto
  finally 
  show ?case unfolding ur_term_impl.simps Let_def rm ur_term.simps set_remdups set_append
    by (intro cong, force)
qed

context
  fixes R :: "('f,string)trs"
  and Q :: "('f,string)terms"
  and init :: "(('f,string)term list \<times> ('f,string)term)set"
begin
private abbreviation (input) calc where "calc \<equiv> (\<lambda> (argsl,t) ur. ur \<in> ur_term R Q icap full_af (mv_xvar ` set argsl) (mv_xvar t))"
private abbreviation (input) nxt where "nxt \<equiv> (\<lambda> (l,r). {(args l, r)})"

definition "usable_rules_calc \<equiv> {ur . \<exists> ss_t \<in> init. generic_inductive_set.the_set R 
    calc nxt ss_t ur}"

lemma usable_rules_calc_ur_closed_init:
  assumes init: "(ss,t) \<in> init" 
  shows "is_ur_closed_term_mv' R usable_rules_calc Q icap full_af (set ss) t"
  by (rule is_ur_closed'_ur_term, unfold usable_rules_calc_def split, 
  auto intro!: generic_inductive_set.non_rec bexI init, rule set_mp[OF ur_term_subset])

lemma usable_rules_calc_ur_closed_U: assumes lr: "(l,r) \<in> usable_rules_calc"
   shows "is_ur_closed_term_mv' R usable_rules_calc Q icap full_af (set (args l)) r"
proof -
  interpret generic_inductive_set R calc nxt .
  note d = usable_rules_calc_def split
  from lr[unfolded d] obtain ss_t
  where ss_t: "ss_t \<in> init" and set: "the_set ss_t (l,r)" by auto
  note rec = rec_rec[OF set]
  show ?thesis
  proof (rule is_ur_closed'_ur_term, rule)
    fix l' r'
    assume ur: "(l',r') \<in> ur_term R Q icap full_af (mv_xvar ` set (args l)) (mv_xvar r)"
    with ur_term_subset have "(l',r') \<in> R" by force
    note non_rec = non_rec[OF this]
    show "(l',r') \<in> usable_rules_calc"
      unfolding d
      by (rule, rule bexI[OF _ ss_t], rule rec[OF _ non_rec], insert ur, auto)
  qed
qed

lemma usable_rules_calc: assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and NFs: "set ss \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
  and ss_t: "(ss,t) \<in> init"
  and nfsigma: "nfs \<Longrightarrow> \<sigma> ` vars_term t \<subseteq> NF_terms Q" 
  and varsR: "\<not> nfs \<Longrightarrow> wwf_qtrs Q R \<or> SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}"
  and vars: "\<not> nfs \<Longrightarrow> vars_term t \<subseteq> \<Union> (vars_term ` set ss)"
  and steps: "(t \<cdot> \<sigma> ,u) \<in> (qrstep nfs Q R)^*"
  shows "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q usable_rules_calc)^*"
    "(u, v) \<in> qrstep_r_p_s nfs Q R lr' p \<tau> \<Longrightarrow> lr' \<in> usable_rules_calc"
proof -
  let ?U = usable_rules_calc
  interpret R_Q_U_ecap R usable_rules_calc Q icap'
    by (unfold_locales, auto simp: icap inn)
  have NFt: "\<sigma> ` vars_term t \<subseteq> NF_terms Q"
  proof (cases nfs)
    case False
    show ?thesis
    proof (rule subsetI)
      fix u
      assume "u \<in> \<sigma> ` vars_term t"
      then obtain x where u: "u = \<sigma> x" and "x \<in> vars_term t" by auto
      with vars[OF False] obtain s where s: "s \<in> set ss" and x: "x \<in> vars_term s" by auto
      from supteq_subst[OF supteq_Var[OF x], of \<sigma>] u have "s \<cdot> \<sigma> \<unrhd> u" by auto
      from NF_subterm[OF _ this] NFs s
      show "u \<in> NF_terms Q" by auto
    qed
  qed (rule nfsigma)
  let ?both = "init \<union> {(args l,r) | l r. (l,r) \<in> ?U}"
  {
    fix ss t
    assume "(ss,t) \<in> ?both"
    with usable_rules_calc_ur_closed_U[of _ t] usable_rules_calc_ur_closed_init[of ss t]
    have "is_ur_closed_term_mv' R ?U Q icap full_af (set ss) t"
      by auto
    then have "is_ur_closed_term_mv' R ?U Q icap' full_af (set ss) t"
      unfolding is_ur_closed_term_mv_icap' .
  } note closed = this
  from ss_t have ss_t: "(ss,t) \<in> ?both" by auto
  have lr: "\<And> l r. (l,r) \<in> ?U \<Longrightarrow> (args l, r) \<in> ?both" by auto
  note main = is_ur_closed_term_last is_ur_closed_term
  note main = main[OF steps NFt NFs closed[OF lr] subset_refl varsR closed[OF ss_t]]
  from main(2) show "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q ?U)^*" using rtrancl_mono[OF qrstep_mono[OF _ subset_refl]] by blast
  assume "(u, v) \<in> qrstep_r_p_s nfs Q R lr' p \<tau> "
  with main(1) show "lr' \<in> ?U" by auto
qed
end

context 
  fixes NFQ :: "('f :: compare_order,string)term \<Rightarrow> bool"
  and e_cap :: "('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,unit + string)term"
  and R :: "('f,string)rules"
begin
definition usable_rules_calc_impl where
  "usable_rules_calc_impl \<equiv> 
    let
      urt = (\<lambda> (S,t). let S' = map mv_xvar S in 
        ur_term_impl NFQ (e_cap S') R full_af S' (mv_xvar t));
      urules = map (\<lambda> (l,r). (args l,r)) R;
      ufun = precompute_fun urt urules
    in inductive_set_impl_lazy ufun (\<lambda> (l,r). [(args l,r)])"

definition ur_calc_singleton 
  where "ur_calc_singleton st \<equiv> usable_rules_calc_impl [st]"

definition inn_usable_rules_wf :: "bool \<Rightarrow> ('f, string)term list \<times> ('f,string)term \<Rightarrow> ('f,string)rules"
  where "inn_usable_rules_wf nfs \<equiv> 
   (\<lambda> (ss,t). if nfs \<or> (\<forall> x \<in> set (remdups (vars_term_list t)). \<exists> s \<in> set ss. x \<in> vars_term s) then ur_calc_singleton (ss,t)
     else R)"

context
  fixes Q :: "('f,string)terms"
  assumes NFQ: "NFQ = (\<lambda> t. t \<in> NF_terms Q)"
    and e_cap: "\<And> S. e_cap S = icap (set R) Q (set S)"
begin
lemma usable_rules_calc_impl:
  "set (usable_rules_calc_impl init) = usable_rules_calc (set R) Q (set init)"
  unfolding usable_rules_calc_impl_def Let_def split usable_rules_calc_def 
    using ur_term_impl[OF NFQ, of _ icap, OF e_cap]
  by (intro inductive_set_impl_lazy[of R], insert ur_term_subset[of "set R"], force+)

lemma ur_calc_singleton:
  assumes U: "U = ur_calc_singleton (ss,t)"
      and NF: "NF_terms Q \<subseteq> NF_trs (set R)"
      and NFs: "set ss \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
      and nfsigma: "nfs \<Longrightarrow> \<sigma> ` vars_term t \<subseteq> NF_terms Q"
      and varsR: "\<not> nfs \<Longrightarrow> wwf_qtrs Q (set R) \<or> SN_on (qrstep nfs Q (set R)) {t \<cdot> \<sigma>}"
      and vars: "\<not> nfs \<Longrightarrow> vars_term t \<subseteq> \<Union>(vars_term ` set ss)"
      and steps: "(t \<cdot> \<sigma> ,u) \<in> (qrstep nfs Q (set R))^*"
  shows "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q (set U))^*"
    "(u, v) \<in> qrstep_r_p_s nfs Q (set R) lr' p \<tau> \<Longrightarrow> lr' \<in> set U"
proof -
  let ?R = "set R"
  let ?Q = "Q"
  let ?nfs = "nfs"
  let ?U = "usable_rules_calc ?R Q (set [(ss, t)])"
  note main = usable_rules_calc[OF NF NFs _ nfsigma varsR vars steps, of "{(ss,t)}"] 
  from main(1) have steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs ?Q ?U)\<^sup>*" by simp
  have U: "?U = set U" unfolding U 
     usable_rules_calc_impl[symmetric]
     ur_calc_singleton_def Let_def split ..
  from steps U show "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs ?Q (set U))^*" by simp
  assume "(u, v) \<in> qrstep_r_p_s nfs ?Q ?R lr' p \<tau>"
  from main(2)[OF _ _ _ _ this] vars NFs show "lr' \<in> set U" unfolding U[symmetric] by simp
qed

context 
  assumes inn: "NF_terms Q \<subseteq> NF_trs (set R)"
      and wf: "wwf_qtrs Q (set R)"
begin
lemma inn_usable_rules_wf:
  assumes steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q (set R))^*"
      and NFss: "set ss \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"      
      and NFt: "nfs \<Longrightarrow> \<sigma> ` vars_term t \<subseteq> NF_terms Q"
      and step: "(u, v) \<in> qrstep_r_p_s nfs Q (set R) lr' p \<tau>"
      shows "lr' \<in> set (inn_usable_rules_wf nfs (ss,t))"
proof -
  let ?R = "set R"
  let ?Q = "Q"
  let ?nfs = nfs
  let ?U = "inn_usable_rules_wf  nfs (ss,t)"
  show ?thesis 
  proof (cases "nfs \<or> vars_term t \<subseteq> \<Union> (vars_term `  set ss)")
    case False
    then have U: "?U = R" unfolding inn_usable_rules_wf_def Let_def split by auto
    show ?thesis using step unfolding U by (auto simp: qrstep_r_p_s_def)
  next
    case True
    then have U: "?U = ur_calc_singleton (ss,t)" unfolding inn_usable_rules_wf_def Let_def split by auto 
    from True have "\<not> nfs \<Longrightarrow> vars_term t \<subseteq> \<Union> (vars_term `  set ss)" by blast
    from ur_calc_singleton(2)[OF U, OF inn NFss NFt disjI1[OF wf] this steps step] 
    show ?thesis .
  qed
qed

lemma inn_usable_rules_wf_approx: "usable_rules_approx Q (set R) nfs
  (\<lambda> ss t. set (inn_usable_rules_wf nfs (ss,t)))"
  unfolding usable_rules_approx_def
  by (intro allI impI, rule inn_usable_rules_wf, auto)
end
end
end

definition inn_usable_rules_pair :: "('d, 'f :: compare_order, string) dpp_ops
      \<Rightarrow> 'd \<Rightarrow> ('f, string)rule \<Rightarrow> ('f,string)rules"
  where "inn_usable_rules_pair I d \<equiv> 
  let inn = dpp_ops.NFQ_subset_NF_rules I d;
      R = dpp_ops.rules I d;
      qnf = dpp_ops.is_QNF I d;
      ic = icap_impl_dpp I d;
      calc = ur_calc_singleton qnf ic R;
      nfs = dpp_ops.nfs I d;
      wwf = dpp_ops.wwf_rules I d;
      m   = dpp_ops.minimal I d
   in (\<lambda> (s,t). if inn \<and> (nfs \<or> (vars_term t \<subseteq> vars_term s)) \<and> (nfs \<or> m \<or> wwf) then
          calc ([s],t) else R)"

lemma inn_usable_rules_pair:
  fixes I::"('d, 'f::{showl,compare_order}, string) dpp_ops" and d::"'d" 
  defines q: "q \<equiv> dpp_ops.Q I d"
      and R: "R \<equiv> dpp_ops.rules I d"
      and nfs: "nfs \<equiv> dpp_ops.nfs I d"
  assumes I: "dpp_spec I"
      and U: "U = inn_usable_rules_pair I d (s,t)"
      and steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs (set q) (set R))^*"
      and NFs: "s \<cdot> \<sigma> \<in> NF_terms (set q)"      
      and NFt: "nfs \<Longrightarrow> \<sigma> ` vars_term t \<subseteq> NF_terms (set q)"
      and SN: "dpp_ops.minimal I d \<Longrightarrow> SN_on (qrstep nfs (set q) (set R)) {t \<cdot> \<sigma>}"
  shows "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs (set q) (set U))^*"
proof -
  interpret dpp_spec I by fact
  let ?R = "set (rules d)"
  let ?Q = "set (Q d)"
  let ?nfs = "NFS d"
  let ?m = "M d"
  let ?wwf = "wwf_rules d"
  let ?ic = "icap_impl_dpp I d"
  let ?nf = "is_QNF d"
  let ?inn = "dpp_ops.NFQ_subset_NF_rules I d"
  show ?thesis 
  proof (cases "?inn \<and> (nfs \<or> vars_term t \<subseteq> vars_term s) \<and> (nfs \<or> ?m \<or> ?wwf)")
    case False
    then have "U = rules d" unfolding U inn_usable_rules_pair_def Let_def nfs split by auto
    then show ?thesis using steps unfolding R by auto
  next
    case True
    then have U: "U = ur_calc_singleton ?nf ?ic (rules d) ([s],t)" unfolding U inn_usable_rules_pair_def Let_def split nfs by auto 
    from True have inn: "NF_terms ?Q \<subseteq> NF_trs ?R" by auto
    show ?thesis unfolding q nfs
      by (rule ur_calc_singleton(1)[OF _ _ U inn, OF _ icap_impl_dpp_icap[OF I]], 
      insert steps SN NFs NFt q R True nfs, auto)
  qed
qed

definition inn_usable_rules_wf_dpp :: "('d, 'f :: compare_order, string) dpp_ops
      \<Rightarrow> 'd \<Rightarrow> bool \<Rightarrow> ('f, string)term list \<times> ('f,string)term \<Rightarrow> ('f,string)rules" where 
  "inn_usable_rules_wf_dpp I d nfs \<equiv> inn_usable_rules_wf (dpp_ops.is_QNF I d) (icap_impl_dpp I d) (dpp_ops.rules I d) nfs"

lemma inn_usable_rules_wf_dpp_approx: 
  assumes I: "dpp_spec I"
    and inn: "NF_terms (set (dpp_ops.Q I d)) \<subseteq> NF_trs (set (dpp_ops.rules I d))"
    and wf: "wwf_qtrs (set (dpp_ops.Q I d)) (set (dpp_ops.rules I d))"
  shows "usable_rules_approx (set (dpp_ops.Q I d)) (set (dpp_ops.rules I d)) nfs
    (\<lambda> ss t. set (inn_usable_rules_wf_dpp I d nfs (ss,t)))"
proof -
  interpret dpp_spec I by fact
  show ?thesis
    unfolding inn_usable_rules_wf_dpp_def
    by (rule inn_usable_rules_wf_approx[OF _ icap_impl_dpp_icap[OF I] inn wf], simp)
qed

definition inn_usable_rules_wf_tp :: "('d, 'f :: compare_order, string) tp_ops
      \<Rightarrow> 'd \<Rightarrow> bool \<Rightarrow> ('f, string)term list \<times> ('f,string)term \<Rightarrow> ('f,string)rules" where 
  "inn_usable_rules_wf_tp I d nfs \<equiv> inn_usable_rules_wf (tp_ops.is_QNF I d) (icap_impl_tp I d) (tp_ops.rules I d) nfs"

lemma inn_usable_rules_wf_tp_approx: 
  assumes I: "tp_spec I"
    and inn: "NF_terms (set (tp_ops.Q I d)) \<subseteq> NF_trs (set (tp_ops.rules I d))"
    and wf: "wwf_qtrs (set (tp_ops.Q I d)) (set (tp_ops.rules I d))"
  shows "usable_rules_approx (set (tp_ops.Q I d)) (set (tp_ops.rules I d)) nfs
    (\<lambda> ss t. set (inn_usable_rules_wf_tp I d nfs (ss,t)))"
proof -
  interpret tp_spec I by fact
  show ?thesis
    unfolding inn_usable_rules_wf_tp_def
    by (rule inn_usable_rules_wf_approx[OF _ icap_impl_tp_icap[OF I] inn wf], simp)
qed

end
