(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Complexity
imports
  SN.Reduction_Pair_Proc_Impl
  Ord.Reduction_Pair_Implementations
  SN.Matchbounds_Impl
  SN.DT_Transformation_Impl
  SN.WDP_Transformation_Impl
  SN.Usable_Replacement_Map_Impl
  Sem_Lab.Labelings_Impl
  SN.Complexity_Impl
  Check_Termination_Common
begin

subsection \<open>Assumption\<close>

fun showsl_complexity_measure where
  "showsl_complexity_measure (Runtime_Complexity C D) = (
    showsl_lit (STR ''basic terms f(c1,..,cn) where f in\<newline>'') \<circ> showsl (sort D) \<circ> 
    showsl_lit (STR ''\<newline> and ci is term over signature\<newline> '') \<circ> showsl (sort C) \<circ> showsl_nl)"
| "showsl_complexity_measure (Derivational_Complexity F) = (
    showsl_lit (STR ''all terms over signature\<newline>'') \<circ> showsl (sort F) \<circ> showsl_nl)"

fun showsl_complexityLL :: "('f :: {showl, compare_order}, 'l :: {showl, compare_order}, 'v :: {showl, compare_order})complexityLL \<Rightarrow> showsl" where
  "showsl_complexityLL (Q,S,W,cm,cc) = 
    (showsl_lit (STR ''strict rules\<newline>'') \<circ> showsl_rules (sort S) \<circ> 
    showsl_lit (STR ''\<newline>\<newline>weak rules\<newline>'') \<circ> showsl_rules (sort W) \<circ>
    showsl_lit (STR ''\<newline>\<newline>innermost lhss (Q)\<newline>'') \<circ> showsl_lines (STR ''empty'') (sort Q) \<circ>
    showsl_lit (STR ''\<newline>\<newline>starting terms: '') \<circ> showsl_complexity_measure cm \<circ> 
    showsl_lit (STR ''\<newline>intended complexity: '') \<circ> showsl cc \<circ> showsl_nl
    )
  "

fun check_complexity_subsumes :: "('f :: {showl, compare_order}, 'l :: {showl, compare_order}, 'v :: {showl, compare_order})complexityLL \<Rightarrow> 
  ('f, 'l, 'v)complexityLL
  \<Rightarrow> showsl check" where
  "check_complexity_subsumes (Q1,S1,W1,cm1,cc1) (Q2,S2,W2,cm2,cc2) = do {
    check_subseteq S2 S1 <+? (\<lambda> r. (showsl_lit (STR ''strict rule '') \<circ> showsl_rule r \<circ> showsl_lit (STR '' is missing'')));
    check_subseteq W2 W1 <+? (\<lambda> r. (showsl_lit (STR ''weak rule '') \<circ> showsl_rule r \<circ> showsl_lit (STR '' is missing'')));
    check_NF_terms_subset (is_NF_terms Q2) Q1 <+? (\<lambda> q. showsl_lit (STR ''NF(Q) differs due to term '') \<circ> showsl q);
    check (cc1 \<le> cc2) (showsl_lit (STR ''complexity classes do not match''));
    check_terms_of_nat cm2 cm1
   } <+? (\<lambda> e. showsl_lit (STR ''could not ensure that assumption matches current complexity problem\<newline>'') 
      \<circ> e \<circ> showsl_lit (STR ''\<newline>\<newline>assumption is\<newline>'') \<circ>
      showsl_complexityLL (Q1,S1,W1,cm1,cc1) \<circ> 
      showsl_lit (STR ''\<newline>\<newline>current problem is\<newline>'') \<circ> showsl_complexityLL (Q2,S2,W2,cm2,cc2))"

lemma check_complexity_subsumes: assumes h: "satisfied (Complexity_Problem ass)"
  and ok: "isOK(check_complexity_subsumes ass (Q,S,W,cm,cc))"
  shows "deriv_bound_measure_class (rel_qrstep (nfs, set Q, set S, set W)) cm cc"
proof (cases ass)
  case (fields Q1 S1 W1 cm1 cc1) note ass = this
  from h[unfolded this, simplified]
  have bound: "deriv_bound_measure_class
   (rel_qrstep (False, set Q1, set S1, set W1))
   cm1 cc1" by auto
  from ok[unfolded ass] have 
    S: "set S \<subseteq> set S1" and
    W: "set W \<subseteq> set W1" and
    Q: "NF_terms (set Q) \<subseteq> NF_terms (set Q1)" and
    cc: "O_of cc1 \<subseteq> O_of cc" and
    cm: "isOK (check_terms_of_nat cm cm1)" by auto
  show ?thesis
    by (rule deriv_bound_measure_class_mono[OF _ check_terms_of_nat[OF cm] cc bound], unfold split, 
    rule relto_mono[OF qrstep_all_mono[OF S Q] qrstep_all_mono[OF W Q]], auto)
qed

subsection \<open>Proving complexity of TRSs\<close>

datatype ('f, 'l, 'v) complexity_proof =
  Rule_Shift_Complexity "('f,'l)lab redtriple_impl" "('f,'l,'v) trsLL" "('f,'l,'v)trsLL option" "('f,'l,'v) complexity_proof" |
  RisEmpty_Complexity |
  Remove_Nonapplicable_Rules_Complexity "('f,'l,'v)trsLL" "('f,'l,'v) complexity_proof" |
  Matchbounds_Complexity "(('f,'l)lab,'v)bounds_info" |
  Matchbounds_Rel_Complexity "(('f,'l)lab,'v)bounds_info" "('f,'l,'v)trsLL" "('f,'l,'v) complexity_proof" |
  DT_Transformation "(('f,'l)lab,'v)dt_transformation_info" "('f,'l,'v)complexity_proof" |
  WDP_Transformation "(('f, 'l) lab, 'v) wdp_trans_info" "('f, 'l, 'v) complexity_proof" |
  Complexity_Assumption "('f,'l,'v)complexityLL" "('f,'l,'v,('f,'l,'v)complexity_proof)cpx_assm_proof list" |
  Usable_Rules_Complexity "('f,'l,'v)trsLL" "('f,'l,'v) complexity_proof" |
  Split_Complexity "('f,'l,'v)trsLL" "('f,'l,'v) complexity_proof" "('f,'l,'v) complexity_proof"
  
fun collect_assms :: "('cpx \<Rightarrow> ('f,'l,'v) assm list) 
  \<Rightarrow> ('f,'l,'v,'cpx) cpx_assm_proof \<Rightarrow> ('f,'l,'v) assm list" where
  "collect_assms cpx (Complexity_assm_proof cp prf) = cpx prf"
| "collect_assms _ _ = []"

lemma collect_assms_cong[fundef_cong]: 
  assumes 
  "\<And> t p. i = Complexity_assm_proof t p \<Longrightarrow> cpx p = cpx' p" 
  shows "collect_assms cpx i = collect_assms cpx' i" 
  using assms by (cases i, auto)
  
fun complexity_assms :: "bool \<Rightarrow> ('f,'l,'v)complexity_proof \<Rightarrow> ('f,'l,'v) assm list" where
  "complexity_assms a (Rule_Shift_Complexity _ _ _ p) = complexity_assms a p"
| "complexity_assms a RisEmpty_Complexity  = []"
| "complexity_assms a (Remove_Nonapplicable_Rules_Complexity _ p) = complexity_assms a p"
| "complexity_assms a (Usable_Rules_Complexity _ p) = complexity_assms a p"
| "complexity_assms a (Matchbounds_Complexity _) = []"
| "complexity_assms a (Matchbounds_Rel_Complexity _ _ p) = complexity_assms a p"
| "complexity_assms a (DT_Transformation _ p) = complexity_assms a p"
| "complexity_assms a (WDP_Transformation _ p) = complexity_assms a p"
| "complexity_assms a (Complexity_Assumption assm ps) = (if a then 
  Complexity_assm (map assm_proof_to_problem ps) assm #
  concat (map (collect_assms (complexity_assms a)) ps) else [])"
| "complexity_assms a (Split_Complexity _ p1 p2) = complexity_assms a p1 @ complexity_assms a p2"

lemma complexity_assms_False[simp]: "complexity_assms False p = []"
  by (induct p, auto)


context 
  fixes I :: "('tp, ('f :: {showl, compare_order}, 'l :: {showl, compare_order})lab, string) tp_ops"
  and assms :: bool
begin

fun mk_cpx where
  "mk_cpx (q, s, w, cm, cc) = (tp_ops.mk I False q s w, cm, cc)"

fun check_assm :: "('tp \<times> (('f, 'l) lab, char list) complexity_measure \<times> complexity_class \<Rightarrow> 'cpx_prf \<Rightarrow> showsl check)
  \<Rightarrow> ('f,'l,string, 'cpx_prf) cpx_assm_proof \<Rightarrow> showsl check" where
  "check_assm cpx_check (Complexity_assm_proof cp prf) = cpx_check (mk_cpx cp) prf"
| "check_assm _ _ = error (showsl_lit (STR ''no support for termination or non-termination assumptions in complexity proof''))"

lemma check_assms_cong[fundef_cong]: 
  assumes 
  "\<And> t p. i = Complexity_assm_proof t p \<Longrightarrow> cpx (mk_cpx t) p = cpx' (mk_cpx t) p" 
  shows "check_assm cpx i = check_assm cpx' i" 
  using assms 
  by (cases i, auto)

lemma check_assm: 
  assumes 
  "\<And> t p. i = Complexity_assm_proof t p \<Longrightarrow> isOK(cpx (mk_cpx t) p) \<Longrightarrow> satisfied (Complexity_Problem t)"
  shows "isOK(check_assm cpx i) \<Longrightarrow> satisfied (assm_proof_to_problem i)"
  using assms 
  by (cases i, auto)

abbreviation (input) check_subproofs where 
  "check_subproofs 
    check_complexity_proof
    i \<equiv> check_allm_index (\<lambda> as j. check_assm  (check_complexity_proof (add_index i (Suc j))) as)"

fun
  check_complexity_proof ::
    "showsl \<Rightarrow>
     'tp \<times>
     (('f,'l)lab, string)complexity_measure \<times> complexity_class \<Rightarrow>
     ('f,'l, string) complexity_proof \<Rightarrow>
     showsl check" 
where
  "check_complexity_proof i (tp, cm, cc) (Rule_Shift_Complexity redp Rdelete Ur_opt prf) = debug i (STR ''Rule Removal Complexity'') (do {
         tp' \<leftarrow> smart_rule_shift_complexity I (get_rel_impl redp) Rdelete Ur_opt cm cc tp
          <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the rule shifting technique on\<newline>'')
             \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s);
         check_complexity_proof (add_index i 1) (tp',cm,cc) prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the rule shifting processor\<newline>'') \<circ> s)}
)" 
 | "check_complexity_proof i (tp,cm,cc) (RisEmpty_Complexity) = debug i (STR ''R is empty for complexity'') (do {
     check (tp_ops.R I tp = []) (i \<circ> showsl_lit (STR '': R is not empty in\<newline>'') \<circ> showsl_tp I tp) })"
 | "check_complexity_proof i (tp,cm,cc) (Remove_Nonapplicable_Rules_Complexity r prf) = debug i (STR ''Removing non-applicable rules'') (do {
       let R = tp_ops.R I tp;
       check_non_applicable_rules (tp_ops.is_QNF I tp) r
         <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error when removing non-applicable rules\<newline>'') \<circ> (showsl_rule s \<circ> showsl_lit (STR '' is applicable'')));
       let tp' = tp_spec.delete_rules I tp r;
       check_complexity_proof (add_index i 1) (tp',cm,cc) prf
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the non-applicable rules removal\<newline>'')
           \<circ> s)})"
 | "check_complexity_proof i (tp,cm,cc) (Matchbounds_Complexity info) = debug i (STR ''Matchbounds'') (
       bounds_complexity I info cm cc tp 
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying matchbounds\<newline>'') \<circ> s))"
 | "check_complexity_proof i (tp,cm,cc) (Matchbounds_Rel_Complexity info Rdel prf) = debug i (STR ''Matchbounds-Rel'') (
      do {
        tp' <- bounds_complexity_rel I info Rdel cm cc tp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying relative matchbounds\<newline>'') \<circ> s);
        check_complexity_proof (add_index i 1) (tp',cm,cc) prf
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below applying relative matchbounds\<newline>'') \<circ> s)})"
| "check_complexity_proof i (tp,cm,cc) (DT_Transformation info prf) = debug i (STR ''DT Transformation'') (do {
         (cm',tp') \<leftarrow> dt_transformation Sharp I info cm cc tp
          <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the DT transformation on\<newline>'')
             \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s);
         check_complexity_proof (add_index i 1) (tp',cm',cc) prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the DT transformation\<newline>'') \<circ> s)}
  )"
| "check_complexity_proof i (tp, cm, cc) (WDP_Transformation info prf) = debug i (STR ''WDP Transformation'') (do {
    (cm', tp') \<leftarrow> check_wdp_trans Sharp I info cm cc tp
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the WDP transformation on\<newline>'')
           \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s);
    check_complexity_proof (add_index i 1) (tp', cm', cc) prf
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the WDP transformation\<newline>'') \<circ> s)
  })"
 | "check_complexity_proof i (tp,cm,cc) (Usable_Rules_Complexity Ur prf) = debug i (STR ''Usable Rules'') (
      do {
        tp' <- usable_rules_complexity I Ur cm cc tp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying usable rules\<newline>'') \<circ> s);
        check_complexity_proof (add_index i 1) (tp',cm,cc) prf
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below applying usable rules\<newline>'') \<circ> s)})"
| "check_complexity_proof i (tp,cm,cc) (Complexity_Assumption a ass) = debug i (STR ''Complexity Assumption'') (
    if assms then do { 
      check_complexity_subsumes a (tp_ops.Q I tp, tp_ops.R I tp, tp_ops.Rw I tp, cm, cc)
        <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error in complexity assumption or unknown proof\<newline>'') \<circ> s);
      check_subproofs 
            check_complexity_proof
            i ass
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below unknown proof\<newline>'') \<circ> s)
    }
    else error (showsl_lit (STR ''the proof contains an assumption or unknown proof which have to be manually allowed''))
  )" 
| "check_complexity_proof i (tp,cm,cc) (Split_Complexity info prf1 prf2) = debug i (STR ''Split'') (
      do {
        (tp1,tp2) <- split_proc_complexity I info tp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying split processor\<newline>'') \<circ> s);
        check_complexity_proof (add_index i 1) (tp1,cm,cc) prf1
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below applying split processor\<newline>'') \<circ> s);
        check_complexity_proof (add_index i 2) (tp2,cm,cc) prf2
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below applying split processor\<newline>'') \<circ> s)})"


lemma check_complexity_proof_with_assms: 
  assumes I: "tp_spec I" 
  and inf: "infinite (UNIV :: (('f,'l)lab) set)"
  and ok: "isOK (check_complexity_proof i (tp,cm,cc) prf)"
  and assm: "Ball (set (complexity_assms assms prf)) holds"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) (cm :: (('f :: {showl, compare_order},'l :: {showl, compare_order})lab,string)complexity_measure) cc"
proof -
  interpret tp_spec I by fact
  from ok assm show ?thesis
  proof (induct "prf" arbitrary: tp i cm cc)
    case RisEmpty_Complexity
    then show ?case by simp
  next
    case (Rule_Shift_Complexity rp Rdelete Ur_opt prof)
    note IH = this 
    note res = IH(2)[simplified]    
    from res obtain tp' where rs: "smart_rule_shift_complexity I (get_rel_impl rp) Rdelete Ur_opt cm cc tp = return tp'" by auto
    from res[unfolded rs, simplified] have rec: "isOK(check_complexity_proof (add_index i 1) (tp',cm,cc) prof)" by auto
    from IH(1)[OF this] IH(3) have IH: "deriv_bound_measure_class (rel_qrstep (qreltrs tp')) cm cc" by auto
    from smart_rule_shift_complexity[OF I get_rel_impl, OF rs IH] show ?case .
  next
    case (Usable_Rules_Complexity Ur prof)
    note IH = this 
    note res = IH(2)[simplified]    
    from res obtain tp' where rs: "usable_rules_complexity I Ur cm cc tp = return tp'" by auto
    from res[unfolded rs, simplified] have rec: "isOK(check_complexity_proof (add_index i 1) (tp',cm,cc) prof)" by auto
    from IH(1)[OF this] IH(3) have IH: "deriv_bound_measure_class (rel_qrstep (qreltrs tp')) cm cc" by auto
    from usable_rules_complexity[OF I rs IH] show ?case .
  next
    case (Remove_Nonapplicable_Rules_Complexity Rdelete prof)
    note IH = this
    note res = IH(2)[simplified]
    from res have check: "isOK (check_non_applicable_rules (\<lambda>t. t \<in> NF_terms (set (Q tp))) Rdelete)" 
      and rec: " isOK (check_complexity_proof (add_index i 1) (delete_rules tp Rdelete, cm, cc) prof)" by auto
    note IH = IH(1)[OF rec] IH(3)
    from check_non_applicable_rules[OF refl check] have id: "\<And> R. qrstep (NFS tp) (set (Q tp)) (R - set Rdelete) = qrstep (NFS tp) (set (Q tp)) R" .
    from IH show ?case by (simp add: id)
  next
    case (Matchbounds_Complexity info) note IH = this
    show ?case 
      by (rule bounds_complexity[OF I], insert IH inf, auto)
  next
    case (Matchbounds_Rel_Complexity info del) note IH = this
    show ?case 
      by (rule bounds_complexity_rel[OF I], insert IH inf, auto)
  next
    case (DT_Transformation info prof)
    note IH = DT_Transformation 
    note res = IH(2)[simplified]    
    from res obtain cm' tp' where rs: "dt_transformation Sharp I info cm cc tp = return (cm', tp')" by auto
    from res[unfolded rs, simplified] have rec: "isOK(check_complexity_proof (add_index i 1) (tp', cm', cc) prof)" by auto
    from IH(1)[OF this] IH(3) have IH: "deriv_bound_measure_class (rel_qrstep (qreltrs tp')) cm' cc" by simp
    from dt_transformation[OF I rs IH] show ?case .
  next
    case (WDP_Transformation info prof)
    note IH = this
    note res = IH(2) [simplified]
    from res obtain cm' and tp'
      where rs: "check_wdp_trans Sharp I info cm cc tp = return (cm', tp')" by auto
    from res [unfolded rs, simplified] have rec: "isOK (check_complexity_proof (add_index i 1) (tp', cm', cc) prof)" by auto
    from IH(1) [OF this] and IH(3) have IH: "deriv_bound_measure_class (rel_qrstep (qreltrs tp')) cm' cc" by simp
    from wdp_trans [OF I rs IH] show ?case .
  next
    case (Complexity_Assumption ass assm)
    note IH = this
    let ?j = "\<lambda> j. add_index i (Suc j)"
    from IH(2) 
    have assms and ok: "isOK (check_complexity_subsumes ass (Q tp, R tp, Rw tp, cm, cc))"
      and ok_ass: "\<And> j. j<length assm \<Longrightarrow>
      isOK (check_assm (check_complexity_proof (?j j)) (assm ! j))" by (auto split: if_splits)
    with IH(3) have ass: "holds (Complexity_assm (map assm_proof_to_problem assm) ass)" 
     and ass2: "\<And> x a. a \<in> set assm \<Longrightarrow> x \<in> set (collect_assms (complexity_assms assms) a) \<Longrightarrow>
        holds x" by auto
    {
      fix p
      assume p: "p \<in> set assm"
      then obtain j where j: "j < length assm" and pj: "p = assm ! j" unfolding set_conv_nth by auto      
      have "satisfied (assm_proof_to_problem p)"
      proof (rule check_assm[OF _ ok_ass[OF j, folded pj]])
        fix t pa
        assume p_t: "p = Complexity_assm_proof t pa"
        and ok: "isOK (check_complexity_proof (?j j) (mk_cpx t) pa)"
        obtain q s w cm cc where t: "t = (q,s,w,cm,cc)" by (cases t, auto)
        from p_t have pa: "pa \<in> set1_generic_assm_proof p" by auto
        note ok = ok[unfolded t mk_cpx.simps]
        have "\<forall>a\<in>set (complexity_assms assms pa). holds a"
          using ass2[OF p, unfolded p_t] by auto
        from IH(1)[OF p pa ok this]
        show "satisfied (Complexity_Problem t)" unfolding t satisfied.simps
          by simp
      qed
    }
    with ass have ass: "satisfied (Complexity_Problem ass)" by simp
    from check_complexity_subsumes[OF ass ok, of "NFS tp"]
    show ?case by auto
  next
    case (Split_Complexity info prf1 prf2)
    note IH = this
    note res = IH(3)[simplified]
    from res obtain tp1 tp2
      where rs: "split_proc_complexity I info tp = return (tp1, tp2)" by auto
    from res [unfolded rs, simplified] have 
      rec1: "isOK (check_complexity_proof (add_index i 1) (tp1, cm, cc) prf1)" and
      rec2: "isOK (check_complexity_proof (add_index i 2) (tp2, cm, cc) prf2)" by auto
    from IH(1)[OF rec1] IH(4) have IH1: "deriv_bound_measure_class (rel_qrstep (qreltrs tp1)) cm cc" by simp
    from IH(2)[OF rec2] IH(4) have IH2: "deriv_bound_measure_class (rel_qrstep (qreltrs tp2)) cm cc" by simp
    from split_proc_complexity[OF I rs IH1 IH2] show ?case .
  qed
qed
end

lemma check_complexity_proof: 
  assumes I: "tp_spec I" 
  and inf: "infinite (UNIV :: (('f,'l)lab) set)"
  and ok: "isOK (check_complexity_proof I False i (tp,cm,cc) prf)"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) (cm :: (('f :: {showl, compare_order},'l :: {showl, compare_order})lab,string)complexity_measure) cc"
  by (rule check_complexity_proof_with_assms[OF I inf ok], simp)

end
