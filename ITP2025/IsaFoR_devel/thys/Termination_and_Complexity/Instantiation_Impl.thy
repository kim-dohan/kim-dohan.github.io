(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Instantiation_Impl
imports
  Innermost_Usable_Rules_Impl
  Dependency_Graph_Impl
  Instantiation
  Not_SN.Nontermination
begin


definition
  instantiation_proc ::
    "('dpp, 'f :: {showl, compare_order}, string) dpp_ops \<Rightarrow> 
     ('f,string)rule \<Rightarrow> ('f,string)rules \<Rightarrow> 'dpp proc"
where
  "instantiation_proc I st sts dpp \<equiv> 
    check_return (do {
     let ic = icap_impl_dpp_mv I dpp;
     let isnf = dpp_ops.is_QNF I dpp;
     let (s,t) = st;
     let sy = mv_yvar s;
     let ty = mv_yvar t;
     let iedg = is_iedg_edge_dpp I dpp; 
     check_allm (\<lambda> (u,v). 
          case mgu_class (ic [u] v) s of
             None \<Rightarrow> succeed
          |  Some \<mu> \<Rightarrow> check (\<not> isnf (sy \<cdot> \<mu>) \<or> \<not> isnf (mv_xvar u \<cdot> \<mu>) \<or> (\<exists> st' \<in> set sts. instance_rule st' st \<and> instance_rule (sy \<cdot> \<mu>, ty \<cdot> \<mu>) st')) 
                (showsl_lit (STR ''could not find instance of pair '') \<circ> showsl_rule (sy \<cdot> \<mu>, ty \<cdot> \<mu>)
                \<circ> showsl_lit (STR ''\<newline>which resulted from DP '') \<circ> showsl_rule (u,v))
                ) (filter (\<lambda> (u,v). iedg (u,v) s) (dpp_ops.pairs I dpp))
   })
   (dpp_ops.replace_pair I dpp st sts)"

lemma instantiation_proc: assumes I: "dpp_spec I"
 shows "dpp_spec.sound_proc_impl I (instantiation_proc I (st :: ('f :: {showl, compare_order},string)rule)
  sts)"
proof -
  from assms interpret dpp_spec I .
  show ?thesis
  proof
    fix d d'    
    assume ok: "instantiation_proc I st sts d = Inr d'" and fin: "finite_dpp (dpp d')"
    let ?Pb = "set (pairs d)"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?Q = "set (Q d)"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?Rb = "?R \<union> ?Rw"
    let ?Rb' = "set (rules d)" 
    let ?nfs = "NFS d"
    let ?m = "M d"
    obtain s t where st: "st = (s,t)" by force
    let ?sy = "mv_yvar s"
    let ?ty = "mv_yvar t"
    note ok = ok[unfolded instantiation_proc_def st icap_impl_dpp_icap_mv[OF I] Let_def dpp_spec_sound, simplified] 
    from ok have d': "d' = replace_pair d (s,t) sts" by auto
    have d': "dpp d' = (?nfs,?m,replace (s,t) (set sts) ?P, replace (s,t) (set sts) ?Pw, ?Q, ?R, ?Rw)" 
      unfolding d' unfolding replace_pair_sound by simp
    note fin = fin[unfolded this]
    show "finite_dpp (dpp d)" unfolding dpp_spec_sound
    proof (rule instantiation_proc[OF icap fin])
      fix u v \<mu> 
      assume uv: "(u,v) \<in> ?P \<union> ?Pw" and DG: "((u,v),(s,t)) \<in> DG (NFS d) (M d) (?P \<union> ?Pw) ?Q ?Rb" and 
      mgu: "mgu_class (icap' ?Rb ?Q (mv_xvar ` {u}) (mv_xvar v)) s = Some \<mu>" and NF: "?sy \<cdot> \<mu> \<in> NF_terms ?Q" "mv_xvar u \<cdot> \<mu> \<in> NF_terms ?Q"
      from DG have DG: "((u,v),(s,t)) \<in> DG (NFS d) (M d) (?P \<union> ?Pw) ?Q ?Rb'" by simp
      from is_iedg_edge_dpp_DG_sound[OF I DG] have iedg: "is_iedg_edge_dpp I d (u, v) s" .
      from ok[THEN conjunct1, rule_format, of u v] uv iedg
        NF mgu[unfolded icap']
      have "Bex (set sts) (\<lambda> st. instance_rule st (s,t) \<and> instance_rule (?sy \<cdot> \<mu>, ?ty \<cdot> \<mu>) st)" 
        unfolding icap_mv_def isOK_check by auto
      then show "\<exists> (s',t') \<in> set sts.
        instance_rule (s',t') (s,t) \<and> instance_rule (?sy \<cdot> \<mu>, ?ty \<cdot> \<mu>) (s',t')" by auto
    qed
  qed
qed


definition
  forward_instantiation_proc ::
    "('dpp, 'f :: {showl, compare_order}, string) dpp_ops \<Rightarrow> 
     ('f,string)rule \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)rules option \<Rightarrow> 'dpp proc"
where
  "forward_instantiation_proc I st sts U_opt dpp \<equiv> 
    check_return (do {
     let isnf = dpp_ops.is_QNF I dpp;
     let (s,t) = st;
     let iedg = is_iedg_edge_dpp I dpp (s,t); 
     let sy = mv_yvar s;
     let ty = mv_yvar t;
     let U = (case U_opt of None \<Rightarrow> dpp_ops.rules I dpp | Some U \<Rightarrow> U);
     (if U_opt = None then succeed else 
         let urc = is_ur_closed_impl_dpp_mv I dpp U;
             check_urc = (\<lambda> S t. check (urc S t) (showsl_lit (STR ''term '') \<circ> showsl t \<circ> showsl_lit (STR '' is not closed under usable rules'')))
 in
         do {
            check (dpp_ops.nfs I dpp \<or> dpp_ops.minimal I dpp) (showsl_lit (STR ''minimality or normal subst required''));
            check (dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''innermost rewriting required''));
            check_allm (\<lambda>(l,r). check_urc (args l) r) U;
            check_urc [s] t;
            (if dpp_ops.nfs I dpp then succeed else check_subseteq (vars_term_list t) (vars_term_list s) <+? (\<lambda> x. showsl_lit (STR ''variable condition in pair violated'')))
         });
     let Ur = map (\<lambda> (l,r). (r,l)) U;
     let ic = icap_impl' (is_NF_terms []) Ur [];
     check_allm (\<lambda> (u,v). 
          case mgu_class (ic u) t of
             None \<Rightarrow> succeed
          |  Some \<mu> \<Rightarrow> check (\<not> isnf (sy \<cdot> \<mu>) \<or> \<not> isnf (mv_xvar u \<cdot> \<mu>) \<or> (\<exists> st' \<in> set sts. instance_rule st' st \<and> instance_rule (sy \<cdot> \<mu>, ty \<cdot> \<mu>) st')) 
                (showsl_lit (STR ''could not find instance of pair '') \<circ> showsl_rule (sy \<cdot> \<mu>, ty \<cdot> \<mu>)
                \<circ> showsl_lit (STR ''\<newline>which resulted from DP '') \<circ> showsl_rule (u,v))
                ) (filter (\<lambda> (u,v). iedg u) (dpp_ops.pairs I dpp))
   })
   (dpp_ops.replace_pair I dpp st sts)"

lemma forward_instantiation_proc: assumes I: "dpp_spec I"
 shows "dpp_spec.sound_proc_impl I (forward_instantiation_proc I (st :: ('f :: {showl, compare_order},string)rule)
  sts U_opt)"
proof -
  note Id_on_empty[simp del]
  from assms interpret dpp_spec I .
  show ?thesis
  proof
    fix d d'    
    assume ok: "forward_instantiation_proc I st sts U_opt d = Inr d'" and fin: "finite_dpp (dpp d')"
    let ?Pb = "set (pairs d)"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?Q = "set (Q d)"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?Rb = "?R \<union> ?Rw"
    let ?Rb' = "set (rules d)"
    let ?nfs = "NFS d"
    let ?m = "M d"
    obtain s t where st: "st = (s,t)" by force
    let ?sy = "mv_yvar s"
    let ?ty = "mv_yvar t"
    note ok = ok[unfolded forward_instantiation_proc_def st is_ur_closed_impl_dpp_mv[OF I] icap_impl_dpp_icap_mv[OF I] Let_def dpp_spec_sound, simplified] 
    let ?U = "case U_opt of None \<Rightarrow> rules d | Some U \<Rightarrow> U"
    let ?Ur = "map (\<lambda> (l,r). (r,l)) ?U"
    let ?U_opt = "case U_opt of None \<Rightarrow> None | Some U \<Rightarrow> Some (set U)"
    from ok have d': "d' = replace_pair d (s,t) sts" by auto
    have d': "dpp d' = (?nfs,?m,replace (s,t) (set sts) ?P, replace (s,t) (set sts) ?Pw, ?Q, ?R, ?Rw)" 
      unfolding d' unfolding replace_pair_sound by simp
    note fin = fin[unfolded this]
    show "finite_dpp (dpp d)" unfolding dpp_spec_sound
    proof (rule forward_instantiation_proc[OF icap _ _ _ fin])
      assume "?U_opt = None" then show "set ?U = ?Rb" by (cases U_opt, auto)
    next
      show "?U_opt = None \<or> ?U_opt = Some (set ?U)" by (cases U_opt, auto)
    next
      assume some: "?U_opt = Some (set ?U)"
      then obtain U where U_opt: "U_opt = Some U" "?U = U" by (cases U_opt, auto)
      from ok[THEN conjunct1, unfolded U_opt, simplified]
      show "(\<not> ?nfs \<longrightarrow> vars_term t \<subseteq> vars_term s) \<and> (\<not> ?nfs \<longrightarrow> ?m) \<and> NF_terms ?Q \<subseteq> NF_trs ?Rb \<and> 
         is_ur_closed_term' ?Rb (set ?U) ?Q icap' full_af (mv_xvar ` {s}) (mv_xvar t) \<and> (\<forall> (l,r) \<in> set ?U. 
        is_ur_closed_term' ?Rb (set ?U) ?Q icap' full_af (mv_xvar ` (set (args l))) (mv_xvar r))" unfolding U_opt by auto
    next
      fix u v \<mu> 
      assume uv: "(u,v) \<in> ?P \<union> ?Pw" and DG: "((s,t),(u,v)) \<in> DG (NFS d) (M d) (?P \<union> ?Pw) ?Q ?Rb" and
        mgu: "mgu_class (icap' ((set ?U)^-1) {} {} (mv_xvar u)) t = Some \<mu>" and NF: "?sy \<cdot> \<mu> \<in> NF_terms ?Q" "mv_xvar u \<cdot> \<mu> \<in> NF_terms ?Q"
      have rev: "(\<lambda> (l,r). (r,l)) ` set ?U = (set ?U)^-1" by auto
      have mgu: "mgu_class (icap_mv ((\<lambda>(l, r). (r, l)) ` set ?U) {} {} u) t = Some \<mu>" unfolding mgu[symmetric] icap_mv_def using icap'[of "(set ?U)^-1" "{}" "{}"] unfolding rev by simp
      from DG have DG: "((s,t),(u,v)) \<in> DG (NFS d) (M d) (?P \<union> ?Pw) ?Q ?Rb'" by simp
      from is_iedg_edge_dpp_DG_sound[OF I DG] have iedg: "is_iedg_edge_dpp I d (s,t) u" .
      from ok[THEN conjunct2, THEN conjunct1, rule_format, of u v, unfolded split mgu] iedg uv NF 
      have "Bex (set sts) (\<lambda> st. instance_rule st (s,t) \<and> instance_rule (?sy \<cdot> \<mu>, ?ty \<cdot> \<mu>) st)" 
        unfolding icap_mv_def isOK_check by auto
      then show "\<exists> (s',t') \<in> set sts.
        instance_rule (s',t') (s,t) \<and>
        instance_rule (?sy \<cdot> \<mu>, ?ty \<cdot> \<mu>) (s',t')" by auto
    qed
  qed
qed

definition 
  check_instance :: "('f:: showl, 'v:: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
  where 
  "check_instance P P' \<equiv> check_allm 
    (\<lambda> st'. check (\<exists> st \<in> set P. instance_rule st' st) 
    (showsl_rule st' \<circ> showsl_lit (STR '' is not an instance of any original pair''))) P'"

lemma check_instance: 
  "isOK(check_instance P P') = 
  (\<forall> (s',t') \<in> set P'. \<exists> (s,t) \<in> set P. \<exists> \<sigma>. s \<cdot> \<sigma> = s' \<and> t \<cdot> \<sigma> = t')"
  unfolding check_instance_def
  by (force split: prod.split simp: instance_rule_def)

datatype ('f,'v)instantiation_complete_proc_prf = Instantiation_complete_proc_prf "('f,'v)rules"

fun instantiation_complete_proc where
  "instantiation_complete_proc I dpp (Instantiation_complete_proc_prf P') = (do {
    let P    = dpp_ops.pairs I dpp;
    let Q    = dpp_ops.Q I dpp;
    let R    = dpp_ops.rules I dpp;
    let nfs  = dpp_ops.nfs I dpp;
    check (\<not> nfs \<or> Q = []) (showsl_lit (STR ''normal form subst. currently not supported for innermost''));
    check_instance P P';
    return (dpp_ops.mk I nfs False P' [] Q [] R)
  })"

lemma instantiation_complete_proc: assumes I: "dpp_spec I"
  and ok: "instantiation_complete_proc I dpp prf = return dpp'"
  and infin: "infinite_dpp (dpp_ops.nfs I dpp', set (dpp_ops.pairs I dpp'), set (dpp_ops.Q I dpp'), set (dpp_ops.rules I dpp'))" 
    (is "infinite_dpp ?dpp'")
  shows "infinite_dpp (dpp_ops.nfs I dpp, set (dpp_ops.pairs I dpp), set (dpp_ops.Q I dpp), set (dpp_ops.rules I dpp))"
    (is "infinite_dpp ?dpp")
proof -
  obtain P' where id: "prf = Instantiation_complete_proc_prf P'" by (cases "prf") auto
  interpret dpp_spec I by fact
  let ?P    = "set (pairs dpp)"
  let ?nfs  = "NFS dpp"
  let ?dpp' = "(mk ?nfs False P' [] (Q dpp) [] (rules dpp))"
  note ok = ok[unfolded id instantiation_complete_proc.simps Let_def]
  with check_instance[of "pairs dpp" P'] have 
    inst: "(\<forall> (s',t') \<in> set P'. \<exists> (s,t) \<in> ?P. \<exists> \<sigma>. s \<cdot> \<sigma> = s' \<and> t \<cdot> \<sigma> = t')" by auto
  from ok have nfs: "\<not> ?nfs \<or> set (Q dpp) = {}" by auto
  from ok have dpp': "dpp' = mk ?nfs False P' [] (Q dpp) [] (rules dpp)" by simp
  show ?thesis
    by (rule instantiation_inf[OF _ inst nfs], insert infin[unfolded dpp'], auto)
qed

end
