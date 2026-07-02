(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Rules_Complexity_Impl
imports 
  Usable_Rules_Complexity
  Usable_Replacement_Map_Impl
  Innermost_Usable_Rules_Impl
  Framework.Termination_Problem_Spec
  Framework.QDP_Framework_Impl
begin

definition usable_rules_complexity_usymbols ::
    "('tp, 'f:: showl, 'v:: showl) tp_ops \<Rightarrow> ('f,'v)rules \<Rightarrow>
    ('f,'v)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp proc"
 where "usable_rules_complexity_usymbols I NUr cm cc cp \<equiv> do {
    let S = tp_ops.R I cp;
    let W = tp_ops.Rw I cp;
    let R = S @ W;
    check_subseteq NUr R <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rules NUr \<circ> showsl_lit (STR '' does not occur in problem''));
    let Ur = list_diff R NUr;
    let US = set (concat (map (funas_term_list o snd) Ur) @ get_signature_of_cm cm);
    let Urs = set Ur;
    check_varcond_subset Ur;
    check_allm (\<lambda> lr. check (funas_term (fst lr) \<subseteq> US \<longrightarrow> lr \<in> Urs) (showsl_lit (STR ''rule '') 
      \<circ> showsl_rule lr \<circ> showsl_lit (STR '' should be usable''))) R;
    return (tp_ops.mk I (tp_ops.nfs I cp) (tp_ops.Q I cp) (list_diff S NUr) (list_diff W NUr))
  }
    <+? (\<lambda> e. showsl_lit (STR ''error when restricting to usable rules w.r.t. usable symbols\<newline>'') \<circ> e)"

lemma usable_rules_complexity_usymbols:
  assumes "tp_spec I"
  and res: "usable_rules_complexity_usymbols I NUr cm cc tp = return tp'"
  and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  note res = res[unfolded usable_rules_complexity_usymbols_def Let_def, simplified]
  interpret tp_spec I by fact
  let ?S = "set (R tp)"
  let ?W = "set (Rw tp)"
  let ?R = "?S \<union> ?W"
  let ?nfs = "NFS tp"
  let ?Q = "set (Q tp)"
  let ?Ur = "list_diff (R tp @ Rw tp) NUr"
  let ?US = "(\<Union>x\<in> set ?Ur. funas_term (snd x)) \<union> set (get_signature_of_cm cm)"
  have US: "usable_symbols_closed ?US (set ?Ur)"
    unfolding usable_symbols_closed_def usable_symbols_rule_closed_def by auto
  from res have NUr: "set NUr \<subseteq> ?R" and 
    wf: "\<And> l r. (l,r) \<in> set ?Ur \<Longrightarrow> vars_term r \<subseteq> vars_term l" and  
    tp': "tp' =  mk (NFS tp) (Q tp) (list_diff (R tp) NUr) (list_diff (Rw tp) NUr)" and 
    Ur: "\<And> lr. lr \<in> ?R \<Longrightarrow>
      funas_term (fst lr) \<subseteq> ?US \<Longrightarrow> lr \<in> set ?Ur" by force+
  from NUr have id: "?S - set NUr = ?S \<inter> set ?Ur" "?W - set NUr = ?W \<inter> set ?Ur" by auto
  note bound = cpx[unfolded tp' mk_sound split set_list_diff, unfolded id]
  show ?thesis unfolding qreltrs_sound split
  proof (rule usable_rules_complexity[OF _ US wf _ _ _ bound])
    show "U_usable ?US (set ?Ur) ?R" using Ur unfolding U_usable_def by auto
  qed auto
qed

fun extract_rt_C_D :: "('f,'v)complexity_measure \<Rightarrow> (('f \<times> nat) list \<times> ('f \<times> nat) list) result" where
  "extract_rt_C_D (Runtime_Complexity C D) = return (C,D)"
| "extract_rt_C_D _ = error (showsl_lit (STR ''runtime complexity required''))"


definition usable_rules_complexity_innermost ::
    "('tp, 'f::{showl, compare_order}, string) tp_ops \<Rightarrow> ('f,string)rules \<Rightarrow>
    ('f,string)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp proc"
 where "usable_rules_complexity_innermost I NUr cm cc cp \<equiv> do {
    let S = tp_ops.R I cp;
    let W = tp_ops.Rw I cp;
    let R = S @ W;
    check (tp_ops.NFQ_subset_NF_rules I cp) (showsl_lit (STR ''innermost required''));
    check_wf_trs R;
    (Cl,Dl) <- extract_rt_C_D cm;
    let C = set Cl;
    let D = set Dl;
    let isnf = tp_ops.is_QNF I cp;
    check (list_inter Cl (defined_list R) = []) (showsl_lit (STR ''constructors '') \<circ> showsl Cl \<circ> showsl_lit (STR '' must not be defined''));
    check_subseteq NUr R <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rules NUr \<circ> showsl_lit (STR '' does not occur in problem''));
    let Ur = list_diff R NUr;
    check_allm (\<lambda> (l,r). check (\<not> (the (root l) \<in> D \<and> (\<Union> (set (map funas_term (args l))) \<subseteq> C))) 
      (showsl_rule (l,r) \<circ> showsl_lit (STR '' should be usable''))) NUr; 
    let (fs,\<mu>,info) = usable_replacement_map.get_fs_\<mu> R (icap_impl' isnf R) True cm;
    let is_urc = is_ur_closed_af_impl_tp_mv I cp \<mu> Ur;
    check_allm (\<lambda> (l,r). check (is_urc (args l) r) (showsl_lit (STR ''problem with closure properties of usable rule '') 
      \<circ> showsl_rule (l,r) \<circ> showsl_lit (STR '': rhs is not closed under usable rules''))) Ur;    
    return (tp_ops.mk I (tp_ops.nfs I cp) (tp_ops.Q I cp) (list_diff S NUr) (list_diff W NUr))
  }
    <+? (\<lambda> e. showsl_lit (STR ''error when restricting to innermost usable rules\<newline>'') \<circ> e)"

lemma usable_rules_complexity_innermost:
  assumes I: "tp_spec I"
  and res: "usable_rules_complexity_innermost I NUr cm cc tp = return tp'"
  and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  note res = res[unfolded usable_rules_complexity_innermost_def Let_def, simplified]
  interpret tp_spec I by fact
  let ?S = "set (R tp)"
  let ?W = "set (Rw tp)"
  let ?R = "?S \<union> ?W"
  let ?RR = "R tp @ Rw tp"
  let ?nfs = "NFS tp"
  let ?Q = "set (Q tp)"
  let ?nf = "\<lambda> t. t \<in> NF_terms ?Q"
  let ?Ur = "list_diff (R tp @ Rw tp) NUr"
  let ?us = "usable_replacement_map.get_fs_\<mu> ?RR (icap_impl' ?nf ?RR)
         True cm"
  from res obtain Cl Dl where ex: "extract_rt_C_D cm = return (Cl,Dl)" by auto
  obtain fs \<mu> info where us: "?us = (fs,\<mu>,info)" by (cases ?us)
  from ex have cm: "cm = Runtime_Complexity Cl Dl" by (cases cm, auto)
  note res = res[unfolded ex, simplified, unfolded us, simplified]
  from res have NUr: "set NUr \<subseteq> ?R" and 
    wf: "wf_trs ?R" and  
    tp': "tp' = mk (NFS tp) (Q tp) (list_diff (R tp) NUr) (list_diff (Rw tp) NUr)" and
    inn: "NF_terms ?Q \<subseteq> NF_trs ?R" and
    d: "list_inter Cl (defined_list (R tp @ Rw tp)) = []" 
      by force+
  from usable_replacement_map.get_fs_\<mu>[OF refl us] wf inn
  have urm: "usable_replacement_map \<mu> (terms_of cm) (NFS tp) ?R (set (Q tp)) ?R" by auto
  from NUr have id: "?S - set NUr = ?S \<inter> set ?Ur" "?W - set NUr = ?W \<inter> set ?Ur" by auto
  from arg_cong[OF d, of set] have d: "\<And> c. c \<in> set Cl \<Longrightarrow> \<not> defined (set (R tp) \<union> set (Rw tp)) c" by auto
  note bound = cpx[unfolded tp' mk_sound split set_list_diff, unfolded id]
  interpret R_Q_U_ecap ?R "set ?Ur" ?Q icap'
    by (unfold_locales, rule icap, rule inn)
  show ?thesis unfolding qreltrs_sound split
  proof (rule usable_rules_innermost_complexity_urm[OF _ wf cm d _ _ urm bound])
    fix l r
    assume "(l, r) \<in> set ?Ur"
    with res have "is_ur_closed_af_impl_tp_mv I tp \<mu> (list_diff (R tp @ Rw tp) NUr) (args l) r" by auto
    from this[unfolded is_ur_closed_af_impl_tp_mv[OF I]]
    show "is_ur_closed_term' ?R (set ?Ur) ?Q icap'
            \<mu> (map_vars_term ((#) CHR ''x'') ` set (args l)) (map_vars_term ((#) CHR ''x'') r)" by auto
  qed (insert res, auto)
qed

definition usable_rules_complexity ::
    "('tp, 'f::{showl, compare_order}, string) tp_ops \<Rightarrow> ('f,string)rules \<Rightarrow>
    ('f,string)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp proc"
 where "usable_rules_complexity I NUr cm cc cp \<equiv> 
   case usable_rules_complexity_usymbols I NUr cm cc cp of
     Inr cp' \<Rightarrow> Inr cp'
   | Inl e \<Rightarrow> (case usable_rules_complexity_innermost I NUr cm cc cp of
     Inr cp' \<Rightarrow> Inr cp'
   | Inl e' \<Rightarrow> Inl (showsl_lit (STR ''neither of the usable rules processors is applicable:\<newline>'')
     \<circ> showsl_lit (STR ''the one via usable symbols complains as follows\<newline>'') \<circ> e
     \<circ> showsl_lit (STR ''\<newline>\<newline>and the one via icap and innermost says\<newline>'') \<circ> e'))"

lemma usable_rules_complexity:
  assumes I: "tp_spec I"
  and res: "usable_rules_complexity I NUr cm cc cp = return cp'"
  and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I cp')) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I cp)) cm cc"
proof -
  let ?one = "usable_rules_complexity_usymbols I NUr cm cc cp"
  let ?two = "usable_rules_complexity_innermost I NUr cm cc cp"
  note res = res[unfolded usable_rules_complexity_def]
  show ?thesis
  proof (cases ?one)
    case (Inr cpp)
    with res usable_rules_complexity_usymbols[OF I Inr] cpx
      show ?thesis by auto
  next
    case (Inl e)
    note res = res[unfolded this]
    show ?thesis
    proof (cases ?two)
      case (Inr cpp)
      with res usable_rules_complexity_innermost[OF I Inr] cpx
      show ?thesis by auto
    qed (insert res, auto)
  qed
qed

definition
  rule_shift_complexity_urm_ur_tt ::
    "('tp, 'f, string) tp_ops \<Rightarrow> ('f::{showl, compare_order}, string) rel_impl \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)rules 
    \<Rightarrow> ('f,string)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp proc"
where
  "rule_shift_complexity_urm_ur_tt I rp Rdelete Ur cm cc tp = (let 
      Rb = tp_ops.rules I tp;
      R = tp_ops.R I tp;
      Rw = tp_ops.Rw I tp;
      R2 = ceta_list_diff R Rdelete;
      Rremain = Rw @ R2;
      isnf = tp_ops.is_QNF I tp;
      inn = tp_ops.NFQ_subset_NF_rules I tp in
 check_return (do {
     check_subseteq Rdelete Rb 
        <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ> 
          showsl_lit (STR '' should be deleted, but does not occur in problem''));
     check_wf_trs Rb;
     check (tp_ops.NFQ_subset_NF_rules I tp) (showsl_lit (STR ''innermost required''));
     let (fs,\<mu>,info) = usable_replacement_map.get_fs_\<mu>_DP Rb (icap_impl' isnf Rb) inn Rdelete cm;
     let (fs',\<pi>',info') = usable_replacement_map.get_fs_\<mu>_DP Rb (icap_impl' isnf Rb) inn Rremain cm;
     (Cl,Dl) <- extract_rt_C_D cm;
     let C = set Cl;
     let D = set Dl;
     check (list_inter Cl (defined_list Rb) = []) (showsl_lit (STR ''constructors '') \<circ> showsl Cl \<circ> showsl_lit (STR '' must not be defined''));
     rel_impl_redpair rp;
     check_allm (\<lambda> (l,r). check (\<not> (the (root l) \<in> D \<and> (\<Union> (set (map funas_term (args l))) \<subseteq> C))) 
       (showsl_rule (l,r) \<circ> showsl_lit (STR '' should be usable''))) (list_diff Rb Ur); 
     let is_urc = is_ur_closed_af_impl_tp_mv I tp \<mu> Ur;
     let \<pi> = af_inter (rel_impl.af rp) \<pi>';
     let is_urc\<pi> = is_ur_closed_af_impl_tp_mv I tp \<pi> Ur;
     check_allm (\<lambda> (l,r). check (is_urc (args l) r \<and> is_urc\<pi> (args l) r) 
       (showsl_lit (STR ''problem with closure properties of usable rule '') 
        \<circ> showsl_rule (l,r) \<circ> showsl_lit (STR '': rhs is not closed under usable rules''))) Ur;    
     (check_allm (\<lambda> f. check (\<mu> f \<subseteq> rel_impl.mono_af rp f) 
       (showsl_lit (STR ''error in monotonicity: strict order for '') \<circ> showsl f
       \<circ> showsl_lit (STR '' ensures monotonicity in positions '') \<circ> showsl_position_set f (rel_impl.mono_af rp f)
       \<circ> showsl_lit (STR ''\<newline>but usable replacement map is '') \<circ> showsl_position_set f (\<mu> f))) fs) <+? 
     (\<lambda> s. s \<circ> showsl_lit (STR ''\<newline>the computed usable replacement map ('') \<circ> showsl info \<circ> showsl_lit (STR '') is\<newline>'') \<circ>
       showsl_sep (\<lambda> f. showsl_lit (STR ''mu('') \<circ> showsl f \<circ> showsl_lit (STR '') = '') \<circ> showsl_position_set f (\<mu> f)) showsl_nl fs
       \<circ> showsl_lit (STR ''\<newline>and mu(f) = {} for all other symbols f''));
     rel_impl_s rp (list_inter Rdelete Ur)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting strict TRS\<newline>'') \<circ> s);
     rel_impl_ns rp (list_inter Rremain Ur)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting non-strict TRS\<newline>'') \<circ> s);
     rel_impl.cpx rp cm cc
       <+? (\<lambda>s. showsl_lit (STR ''problem when ensuring complexity of order\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not derive the intended complexity '') \<circ> showsl cc \<circ> showsl_lit (STR '' from the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s \<circ> showsl_lit (STR ''\<newline>with usable rules\<newline>'') \<circ> showsl_trs Ur))
     (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) R2 (list_union Rw Rdelete)))"

definition "is_ur_closed_af_impl_tp_mv_impl ic qnf r \<pi> =
  (let urc = (\<lambda> S. is_ur_closed_term_af_impl qnf (ic S) \<pi> r)
    in (\<lambda> U S. let S' = map mv_xvar S in (\<lambda> t. urc S' U S' (mv_xvar t))))"

lemma rule_shift_complexity_urm_ur_tt_code[code]: 
  "rule_shift_complexity_urm_ur_tt I rp Rdelete Ur cm cc tp = (let 
      Rb = tp_ops.rules I tp;
      R = tp_ops.R I tp;
      Rw = tp_ops.Rw I tp;
      R2 = ceta_list_diff R Rdelete;
      Rremain = Rw @ R2;
      isnf = tp_ops.is_QNF I tp;
      inn = tp_ops.NFQ_subset_NF_rules I tp in
 check_return (do {
     check_subseteq Rdelete Rb 
        <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ>
          showsl_lit (STR '' should be deleted, but does not occur in problem''));
     check_wf_trs Rb;
     check (tp_ops.NFQ_subset_NF_rules I tp) (showsl_lit (STR ''innermost required''));
     let (fs,\<mu>,info) = usable_replacement_map.get_fs_\<mu>_DP Rb (icap_impl' isnf Rb) inn Rdelete cm;
     let (fs',\<pi>',info') = usable_replacement_map.get_fs_\<mu>_DP Rb (icap_impl' isnf Rb) inn Rremain cm;
     (Cl,Dl) <- extract_rt_C_D cm;
     let C = set Cl;
     let D = set Dl;
     check (list_inter Cl (defined_list Rb) = []) (showsl_lit (STR ''constructors '') \<circ> showsl Cl \<circ> showsl_lit (STR '' must not be defined''));
     rel_impl_redpair rp;
     check_allm (\<lambda> (l,r). check (\<not> (the (root l) \<in> D \<and> (\<Union> (set (map funas_term (args l))) \<subseteq> C))) 
       (showsl_rule (l,r) \<circ> showsl_lit (STR '' should be usable''))) (list_diff Rb Ur); 
     let ic = icap_impl_tp I tp;
     let qnf = tp_ops.is_QNF I tp;
     let r = tp_ops.rules I tp;
     let UU = set Ur;
     let is_urc = is_ur_closed_af_impl_tp_mv_impl ic qnf r \<mu> UU;
     let \<pi> = af_inter (rel_impl.af rp) \<pi>';
     let is_urc\<pi> = is_ur_closed_af_impl_tp_mv_impl ic qnf r \<pi> UU;
     check_allm (\<lambda> (l,r). check (is_urc (args l) r \<and> is_urc\<pi> (args l) r) 
       (showsl_lit (STR ''problem with closure properties of usable rule '') 
        \<circ> showsl_rule (l,r) \<circ> showsl_lit (STR '': rhs is not closed under usable rules''))) Ur;    
     (check_allm (\<lambda> f. check (\<mu> f \<subseteq> rel_impl.mono_af rp f) 
       (showsl_lit (STR ''error in monotonicity: strict order for '') \<circ> showsl f
       \<circ> showsl_lit (STR '' ensures monotonicity in positions '') \<circ> showsl_position_set f (rel_impl.mono_af rp f)
       \<circ> showsl_lit (STR ''\<newline>but usable replacement map is '') \<circ> showsl_position_set f (\<mu> f))) fs) <+? 
     (\<lambda> s. s \<circ> showsl_lit (STR ''\<newline>the computed usable replacement map ('') \<circ> showsl info \<circ> showsl_lit (STR '') is\<newline>'') \<circ>
       showsl_sep (\<lambda> f. showsl_lit (STR ''mu('') \<circ> showsl f \<circ> showsl_lit (STR '') = '') \<circ> showsl_position_set f (\<mu> f)) showsl_nl fs
       \<circ> showsl_lit (STR ''\<newline>and mu(f) = {} for all other symbols f''));
     rel_impl_s rp (list_inter Rdelete Ur)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting strict TRS\<newline>'') \<circ> s);
     rel_impl_ns rp (list_inter Rremain Ur)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting non-strict TRS\<newline>'') \<circ> s);
     rel_impl.cpx rp cm cc
       <+? (\<lambda>s. showsl_lit (STR ''problem when ensuring complexity of order\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not derive the intended complexity '') \<circ> showsl cc \<circ> showsl_lit (STR '' from the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s \<circ> showsl_lit (STR ''\<newline>with usable rules\<newline>'') \<circ> showsl_trs Ur))
     (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) R2 (list_union Rw Rdelete)))"
  unfolding rule_shift_complexity_urm_ur_tt_def Let_def is_ur_closed_af_impl_tp_mv_impl_def
    is_ur_closed_af_impl_tp_mv_def by simp

lemma rule_shift_complexity_urm_ur_tt:
  assumes I: "tp_spec I"
  and rp: "rel_impl rp"
  and res: "rule_shift_complexity_urm_ur_tt I rp Rdelete Ur cm cc tp = return tp'"
  and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  interpret tp_spec I by fact
  note res = res[unfolded rule_shift_complexity_urm_ur_tt_def Let_def, simplified]
  let ?R = "set (R tp)"
  let ?Rw = "set (Rw tp)"
  let ?D = "ceta_list_diff (R tp) Rdelete"
  let ?RwD = "Rw tp @ ?D"
  let ?nfs = "NFS tp"
  let ?U = "set Ur"
  let ?Q = "set (Q tp)"
  let ?nf = "\<lambda> t. t \<in> NF_terms ?Q"
  let ?QS = "qrstep ?nfs ?Q"
  let ?usgen = "\<lambda> rls. usable_replacement_map.get_fs_\<mu>_DP (rules tp) (icap_impl' ?nf (rules tp))
         (NF_terms (set (Q tp)) \<subseteq> NF_trs (set (R tp) \<union> set (Rw tp))) rls cm"
  let ?us = "?usgen Rdelete"
  let ?usW = "?usgen ?RwD"
  let ?pi = "rel_impl.mono_af rp"
  from res obtain Cl Dl where ex: "extract_rt_C_D cm = return (Cl,Dl)" by auto
  obtain fs \<mu> info where us: "?us = (fs,\<mu>,info)" by (cases ?us)
  obtain fs' \<pi>' info' where usW: "?usW = (fs',\<pi>',info')" by (cases ?usW)
  let ?\<pi> = "af_inter (rel_impl.af rp) \<pi>'"
  note res = res[unfolded us usW ex, simplified]
  from res have valid: "isOK (rel_impl_redpair rp)"
    and S: "isOK(rel_impl_s rp (list_inter Rdelete Ur))" 
    and NS: "isOK(rel_impl_ns rp (list_inter ?RwD Ur))"
    and af: "\<And> f. f \<in> set fs \<Longrightarrow> \<mu> f \<subseteq> ?pi f"
    and inn: "NF_terms ?Q \<subseteq> NF_trs (?R \<union> ?Rw)"
    and wf: "wf_trs (set (rules tp))" "wf_trs (?R \<union> ?Rw)"
    and subset: "set Rdelete \<union> (?Rw \<union> set ?D) \<subseteq> ?R \<union> ?Rw" "set Rdelete \<subseteq> ?R \<union> ?Rw" "set ?RwD \<subseteq> ?R \<union> ?Rw"
    and init: "(\<forall>(l, r)\<in> (?R \<union> ?Rw) - ?U.
      the (root l) \<in> set Dl \<longrightarrow> \<not> \<Union> (funas_term ` set (args l)) \<subseteq> set Cl)"
    and Ur: "(\<forall>(l, r) \<in> ?U.
      is_ur_closed_af_impl_tp_mv I tp \<mu> Ur (args l) r \<and>
      is_ur_closed_af_impl_tp_mv I tp ?\<pi> Ur (args l) r)"
    by (auto simp: rel_impl_list)
  from ex have cm: "cm = Runtime_Complexity Cl Dl" by (cases cm, auto)
  have rules: "set (rules tp) = ?R \<union> ?Rw" by auto
  note urm = usable_replacement_map.get_fs_\<mu>_DP[OF refl us wf(1), unfolded rules, OF subset(2) refl]
  note urm2 = usable_replacement_map.get_fs_\<mu>_DP(2)[OF refl usW wf(1), unfolded rules, OF subset(3) refl]
  interpret R_Q_U_ecap "?R \<union> ?Rw" ?U ?Q icap'
    by (unfold_locales, rule icap, rule inn)
  have af: "af_subset \<mu> ?pi" unfolding af_subset_def
  proof 
    fix f
    show "\<mu> f \<subseteq> ?pi f"
      by (cases "f \<in> set fs", rule af, insert urm(1), auto)
  qed
  let ?cpx = "rel_impl.cpx rp cm cc"
  from res have tp': "tp' = mk ?nfs (Q tp) ?D (list_union (Rw tp) Rdelete)" by simp
  from cpx[unfolded tp', simplified] 
  have bound: "deriv_bound_measure_class (relto (?QS (?R - set Rdelete)) (?QS (?Rw \<union> set Rdelete))) cm cc" .
  from res have cpx: "isOK(?cpx)" by auto
  from res have d: "list_inter Cl (defined_list (rules tp)) = []" by auto
  from arg_cong[OF this, of set] have c: "\<And> c. c \<in> set Cl \<Longrightarrow> \<not> defined (set (R tp) \<union> set (Rw tp)) c" by auto
  from rel_impl_redpair[OF rp valid S NS, of cm cc] cpx
  obtain S NS where redpair: "compat_redpair_order S NS" 
  and S: "set Rdelete \<inter> ?U \<subseteq> S" and NS: "(?Rw \<union> set ?D) \<inter> ?U \<subseteq> NS" 
  and bnd: "deriv_bound_measure_class S cm cc" 
  and af_mono: "af_monotone (rel_impl.mono_af rp) S" 
  and af_compat: "af_compatible (rel_impl.af rp) NS" 
    by auto
  interpret rp: compat_redpair_order S NS by fact
  let ?full = "(\<lambda> _. UNIV) :: 'f af"
  have full: "\<And> \<mu>. af_subset \<mu> ?full" unfolding af_subset_def by auto 
  have mono: "af_monotone ?full NS" using ctxt_closed_one[OF rp.ctxt_NS] unfolding af_monotone_def by blast
  have bound1: "deriv_bound_measure_class (relto (?QS (set Rdelete)) (?QS (?Rw \<union> set ?D))) cm cc"
  proof (rule usable_rules_innermost_complexity_urm_redpair[OF subset(1) wf(2) cm c _ S NS 
        af_subset_af_monotone[OF af af_mono] af_subset_af_monotone[OF full mono] bnd urm(2) _ _ _ redpair af_compat])
    fix l r
    assume "(l, r) \<in> ?R \<union> ?Rw" and "the (root l) \<in> set Dl" and "\<Union>(funas_term ` set (args l)) \<subseteq> set Cl"
    then show "(l, r) \<in> ?U"
      using init by force
  next
    fix l r
    assume lr: "(l, r) \<in> ?U"
    note Ur = Ur[rule_format, OF lr, unfolded split, unfolded  is_ur_closed_af_impl_tp_mv[OF I]]
    show "is_ur_closed_term' (?R \<union> ?Rw) ?U ?Q icap' \<mu> (mv_xvar ` set (args l)) (mv_xvar r)"
      using Ur by auto
    show "is_ur_closed_term' (?R \<union> ?Rw) ?U ?Q icap' ?\<pi> (mv_xvar ` set (args l)) (mv_xvar r)"
      using Ur by auto
  qed (insert urm2, auto)
  have bound: "deriv_bound_measure_class (relto (?QS (set Rdelete \<union> set ?D)) (?QS ?Rw)) cm cc"
    unfolding qrstep_union
    by (rule deriv_bound_relto_measure_class_union, insert bound bound1, auto simp: qrstep_union)
  have bound: "deriv_bound_measure_class (relto (?QS ?R) (?QS ?Rw)) cm cc" 
    by (rule deriv_bound_measure_class_mono[OF relto_mono[OF qrstep_mono[OF _ subset_refl] subset_refl] subset_refl subset_refl bound], auto)
  then show ?thesis by simp
qed

fun smart_rule_shift_complexity :: "('tp, 'f, string) tp_ops \<Rightarrow> ('f::{showl, compare_order}, string) rel_impl \<Rightarrow> ('f,string)rules 
  \<Rightarrow> ('f,string)rules option
  \<Rightarrow> ('f,string)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp proc" where
  "smart_rule_shift_complexity I rp Rdelete (Some Ur) cm cc tp = rule_shift_complexity_urm_ur_tt I rp Rdelete Ur cm cc tp"
| "smart_rule_shift_complexity I rp Rdelete None cm cc tp = rule_shift_complexity_urm_tt I rp Rdelete cm cc tp"

lemma smart_rule_shift_complexity:
  assumes I: "tp_spec I"
  and rp: "rel_impl rp"
  and res: "smart_rule_shift_complexity I rp Rdelete Ur_opt cm cc tp = return tp'"
  and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
  using rule_shift_complexity_urm_ur_tt[OF I rp _ cpx]
    rule_shift_complexity_urm_tt[OF I rp _ cpx]
    res
  by (cases Ur_opt, auto)

end
