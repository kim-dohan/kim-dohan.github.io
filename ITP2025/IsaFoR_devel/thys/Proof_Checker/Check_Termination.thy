(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015, 2018)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Termination
  imports Check_Termination_Common
begin

fun collect_assms :: "('tp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('dpp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('fptp \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('unk \<Rightarrow> ('f, 'l, 'v) assm list)
  \<Rightarrow> ('f, 'l, 'v, 'tp, 'dpp, 'fptp, 'unk) assm_proof \<Rightarrow> ('f, 'l, 'v) assm list"
  where
    "collect_assms tp dpp fptp unk (SN_assm_proof t prf) = tp prf"
  | "collect_assms tp dpp fptp unk (SN_FP_assm_proof t prf) = fptp prf"
  | "collect_assms tp dpp fptp unk (Finite_assm_proof d prf) = dpp prf"
  | "collect_assms tp dpp fptp unk (Unknown_assm_proof p prf) = unk prf"
  | "collect_assms _ _ _ _ _ = []"

lemma collect_assms_cong [fundef_cong]: 
  assumes "\<And> t p. i = SN_assm_proof t p \<Longrightarrow> tp p = tp' p" 
    and "\<And> t p. i = Finite_assm_proof t p \<Longrightarrow> dpp p = dpp' p" 
    and "\<And> t p. i = SN_FP_assm_proof t p \<Longrightarrow> fptp p = fptp' p" 
    and "\<And> t p. i = Unknown_assm_proof t p \<Longrightarrow> unk p = unk' p" 
  shows "collect_assms tp dpp fptp unk i = collect_assms tp' dpp' fptp' unk' i" 
  using assms by (cases i) (auto)

subsection \<open>Proving finiteness in the QDP Framework\<close>

fun
  check_dpp_subsumes ::
    "('d, ('f::{showl, compare_order}, 'l::{showl, compare_order}) lab, 'v:: showl) dpp_ops
    \<Rightarrow> ('f, 'l, 'v) dppLL \<Rightarrow> 'd \<Rightarrow> showsl check"
where
  "check_dpp_subsumes I (nfs', m', p', pw', q', r', rw') d = (do {
    let p   = dpp_ops.P I d;
    let pw  = dpp_ops.Pw I d;
    let q   = dpp_ops.Q I d;
    let r   = dpp_ops.R I d;
    let rw  = dpp_ops.Rw I d;
    let nfs = dpp_ops.nfs I d;
    let m   = dpp_ops.minimal I d;
    let pb' = p' @ pw';
    let rb  = r  @ rw;
    let rb' = r' @ rw';
    check (m = m') (showsl_lit (STR ''incompatible minimality flags''));
    check (nfs = nfs') (showsl_lit (STR ''incompatible substitutions-in-normal-form flags''));
    check_subseteq p p'    <+? (\<lambda>r. toomuch (STR ''pair'') (showsl_rule r));
    check_subseteq pw pb'  <+? (\<lambda>r. toomuch (STR ''weak pair'') (showsl_rule r));
    check_NF_terms_eq q q' <+? (\<lambda>r. showsl_lit (STR ''NF(Q) differs due to term '') \<circ> showsl r);
    check_subseteq r r'    <+? (\<lambda>r. toomuch (STR ''strict rule'') (showsl_rule r));
    check_subseteq rb rb'  <+? (\<lambda>r. toomuch (STR ''strict/weak rule'') (showsl_rule r));
    check_subseteq rb' rb  <+? (\<lambda>r. missing (STR ''strict/weak rule'') (showsl_rule r));
    succeed
  }) <+? (\<lambda>s. showsl_lit (STR ''finiteness of the problem\<newline>'') \<circ> showsl_dpp I d 
           \<circ> showsl_lit (STR ''\<newline>may not be concluded from assuming finiteness of the problem\<newline>'')
           \<circ> showsl_dpp I (dpp_ops.mk I nfs' m' p' pw' q' r' rw') \<circ> showsl_nl
           \<circ> s \<circ> showsl_nl)"

lemma check_dpp_subsumesD [dest]:
  assumes 1: "dpp_spec I"
    and 2: "isOK (check_dpp_subsumes I (nfs, m, p, pw, q, r, rw) d)"
  shows
    "dpp_ops.minimal I d = m"
    "dpp_ops.nfs I d = nfs"
    "set (dpp_ops.P I d) \<subseteq> set p"
    "set (dpp_ops.Pw I d) \<subseteq> set p \<union> set pw"
    "NF_terms (set (dpp_ops.Q I d)) = NF_terms (set q)"
    "set (dpp_ops.R I d) \<subseteq> set r"
    "set (dpp_ops.R I d) \<union> set (dpp_ops.Rw I d) = set r \<union> set rw"
  by (insert 1 2, auto simp: Let_def)

lemma check_dpp_subsumes_sound:
  assumes I: "dpp_spec I"
    and ok: "isOK (check_dpp_subsumes I dpp' dpp)"
    and fin: "finite_dpp (mk_dpp_set dpp')"
  shows "finite_dpp (dpp_ops.dpp I dpp)"
proof -
  obtain nfs m p pw q r rw where
    dpp': "dpp' = (nfs, m, p, pw, q, r, rw)" by (cases dpp') force+

  let ?m   = "dpp_ops.minimal I dpp"
  let ?nfs = "dpp_ops.nfs I dpp"

  let ?P   = "set (dpp_ops.P I dpp)"
  let ?Pw  = "set (dpp_ops.Pw I dpp)"
  let ?Q   = "set (dpp_ops.Q I dpp)"
  let ?R   = "set (dpp_ops.R I dpp)"
  let ?Rw  = "set (dpp_ops.Rw I dpp)"

  let ?P'  = "set p"
  let ?Pw' = "set pw"
  let ?Q'  = "set q"
  let ?R'  = "set r"
  let ?Rw' = "set rw"

  from check_dpp_subsumesD [OF I ok [unfolded dpp']]
    have flags: "?m = m" "?nfs = nfs"
    and 1: "?P \<subseteq> ?P'"
       "?P \<union> ?Pw \<subseteq> ?P' \<union> ?Pw'"
       "NF_terms ?Q' = NF_terms ?Q"
       "?R \<subseteq> ?R'"
       "?R \<union> ?Rw = ?R' \<union> ?Rw'" 
    by auto
  let ?dppg = "\<lambda> nfs m. (nfs, m, ?P', ?Pw', ?Q', ?R', ?Rw')"
  show ?thesis
    unfolding dpp_spec.dpp_sound [OF I]
  proof (rule finite_dpp_mono [OF _ 1], rule ccontr)
    assume "\<not> finite_dpp (?dppg ?nfs ?m)"
    then obtain s t \<sigma> where "min_ichain (?dppg ?nfs ?m) s t \<sigma>"
      unfolding finite_dpp_def by auto
    then have "min_ichain (?dppg ?nfs ?m) s t \<sigma>" by auto
    then have "\<not> finite_dpp (?dppg ?nfs ?m)"
      unfolding finite_dpp_def by auto
    with fin [unfolded dpp'] show False
      unfolding flags by simp
  qed
qed

definition check_compatible_nfs :: "bool \<Rightarrow> (('f :: showl,'v :: showl)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)rules \<Rightarrow> bool \<Rightarrow> ('f,'v)term list \<Rightarrow> bool" where
  "check_compatible_nfs nfs1 nf1 R1 nfs2 Q2 \<equiv> nfs1 = nfs2 \<or> Q2 = [] \<or> 
     isOK(check_wwf_qtrs nf1 R1)"

lemma check_compatible_nfs: assumes compat: "check_compatible_nfs nfs1 (\<lambda> t. t \<in> NF_terms (set Q1)) R1 nfs2 Q2"
  and R: "R \<subseteq> set R1"
 shows "qrstep nfs1 (set Q1) R = qrstep nfs2 (set Q1) R \<or> qrstep nfs2 (set Q2) R2 = qrstep nfs1 (set Q2) R2" 
proof (cases "nfs1 = nfs2 \<or> Q2 = []")
  case False
  from False compat[unfolded check_compatible_nfs_def] have "wwf_qtrs (set Q1) (set R1)" by auto
  with R have "wwf_qtrs (set Q1) R" unfolding wwf_qtrs_def by auto
  from wwf_qtrs_imp_nfs_switch[OF this, of nfs1 nfs2] show ?thesis by auto
qed auto

lemma check_compatible_nfs_SN_qrel: assumes compat: "check_compatible_nfs nfs1 (\<lambda> t. t \<in> NF_terms (set Q1)) (R @ Rw) nfs2 Q2"
 shows "SN_qrel (nfs1, set Q1, set R, set Rw) = SN_qrel (nfs2, set Q1, set R, set Rw)
  \<or> SN_qrel (nfs2, set Q2, R', Rw') = SN_qrel (nfs1, set Q2, R', Rw')"
proof -
  from check_compatible_nfs[OF compat]
  have choice: "\<And> R1 R2. R1 \<subseteq> set (R @ Rw) \<Longrightarrow>
    qrstep nfs1 (set Q1) R1 = qrstep nfs2 (set Q1) R1 \<or> qrstep nfs2 (set Q2) R2 = qrstep nfs1 (set Q2) R2" .
  show ?thesis 
  proof (cases "qrstep nfs1 (set Q1) (set R) = qrstep nfs2 (set Q1) (set R) \<and>
    qrstep nfs1 (set Q1) (set Rw) = qrstep nfs2 (set Q1) (set Rw)")
    case True
    then show ?thesis unfolding SN_qrel_def split by auto
  next
    case False
    {
      fix R2      
      have "qrstep nfs2 (set Q2) R2 = qrstep nfs1 (set Q2) R2"
      using choice[of "set R" R2] choice[of "set Rw" R2] using False by auto
    }
    then show ?thesis unfolding SN_qrel_def split by auto
  qed
qed

fun
  check_tp_subsumes ::
    "('tp, ('f:: showl, 'l:: showl) lab, 'v:: showl) tp_ops \<Rightarrow> ('f, 'l, 'v) qreltrsLL \<Rightarrow>
    'tp \<Rightarrow> showsl check"
where
  "check_tp_subsumes I (nfs', q', r', rw') tp = (do {
    let nfs = tp_ops.nfs I tp;
    let q   = tp_ops.is_QNF I tp;
    let r   = tp_ops.R I tp;
    let rw  = tp_ops.Rw I tp;
    let rb' = r' @ rw';
    let nf1 = tp_ops.is_QNF I tp;
    check (check_compatible_nfs nfs nf1 (r @ rw) nfs' q') (showsl_lit (STR ''incompatible substitutions-in-normal-form flags''));
    check_NF_terms_subset q q' <+? (\<lambda>r. showsl_lit (STR ''problem with innermost strategy due to term '') \<circ> showsl r);
    check_subseteq r r'        <+? (\<lambda>r. toomuch (STR ''rule'') (showsl_rule r));
    check_subseteq rw rb'      <+? (\<lambda>r. toomuch (STR ''relative rule'') (showsl_rule r));
    succeed
  }) <+? (\<lambda>s. showsl_lit (STR ''termination of the problem\<newline>'') \<circ> showsl_tp I tp 
           \<circ> showsl_lit (STR ''\<newline>may not be concluded from assuming termination of the problem\<newline>'') 
           \<circ> showsl_tp I (tp_ops.mk I nfs' q' r' rw') \<circ> showsl_nl
           \<circ> s \<circ> showsl_nl)"

lemma check_tp_subsumesE[elim]:
  assumes 1: "tp_spec I"
    and 2: "isOK (check_tp_subsumes I (nfs, q, r, rw) t)"
    and 3: "check_compatible_nfs (tp_ops.nfs I t) (tp_ops.is_QNF I t) (tp_ops.R I t @ tp_ops.Rw I t) nfs q
    \<Longrightarrow> NF_terms (set (tp_ops.Q I t)) \<subseteq> NF_terms (set q)
    \<Longrightarrow> set (tp_ops.R I t) \<subseteq> set r
    \<Longrightarrow> set (tp_ops.Rw I t) \<subseteq> set r \<union> set rw
    \<Longrightarrow> P"
  shows "P"
proof -
  interpret tp_spec I by fact
  show ?thesis
  by (rule 3, insert 2) (auto simp: Let_def)
qed

lemma check_tp_subsumes_sound:
  assumes I: "tp_spec I"
    and ok: "isOK (check_tp_subsumes I tp' tp)"
    and fin: "SN_qrel (mk_tp_set tp')"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  obtain nfs q r rw where tp': "tp' = (nfs, q, r, rw)" by (cases tp') force+

  let ?nfs = "tp_ops.nfs I tp"

  let ?Q   = "set (Q tp)"
  let ?R   = "set (R tp)"
  let ?Rw  = "set (Rw tp)"
  
  let ?Q'  = "set q"
  let ?R'  = "set r"
  let ?Rw' = "set rw"

  from I and ok
    have compat: "check_compatible_nfs ?nfs (\<lambda> t. t \<in> NF_terms (set (Q tp))) (tp_ops.R I tp @ tp_ops.Rw I tp) nfs q"
    and 1: "NF_terms ?Q \<subseteq> NF_terms ?Q'" "?R \<subseteq> ?R'" "?Rw \<subseteq> ?R' \<union> ?Rw'"
    unfolding tp' by auto
  note compat = check_compatible_nfs_SN_qrel[OF compat, of "set r" "set rw"]
  then show ?thesis
  proof
    assume id: "SN_qrel (nfs, set q, set r, set rw) = SN_qrel (?nfs, set q, set r, set rw)"
    show ?thesis unfolding tp_spec.qreltrs_sound[OF I]
      by (rule SN_qrel_mono[OF 1], unfold id[symmetric], insert fin[unfolded tp'], auto)
  next
    assume id: "SN_qrel (?nfs, ?Q, ?R, ?Rw) = SN_qrel (nfs, ?Q, ?R, ?Rw)"
    show ?thesis unfolding tp_spec.qreltrs_sound[OF I] id
      by (rule SN_qrel_mono[OF 1], insert fin[unfolded tp'], auto)
  qed
qed

fun mk_tp where
  "mk_tp I (nfs, q, r, rw) = tp_ops.mk I nfs q r rw"

fun mk_dpp where
  "mk_dpp I (nfs, m, p, pw, q, r, rw) = dpp_ops.mk I nfs m p pw q r rw"


lemma SN_rel_imp_finite_dpp: assumes SN: "SN_rel (qrstep nfs Q (P \<union> R)) (qrstep nfs Q (Pw \<union> Rw))"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
proof (rule SN_rel_ext_imp_finite_dpp[OF SN_rel_ext_mono[OF _ _ subset_refl subset_refl]])
  show "rqrstep nfs Q P \<inter> {(s, t). s \<in> NF_terms Q} \<subseteq> qrstep nfs Q P" by auto
  show "rqrstep nfs Q Pw \<inter> {(s, t). s \<in> NF_terms Q} \<subseteq> qrstep nfs Q Pw" by auto
  show "SN_rel_ext (qrstep nfs Q P) (qrstep nfs Q Pw) (qrstep nfs Q R) (qrstep nfs Q Rw)
     (\<lambda>x. m \<longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {x})"
    unfolding SN_rel_ext_def
  proof (clarify)
    fix t k
    assume strict: "\<exists>\<^sub>\<infinity>i. k (i :: nat) \<in> {top_s, normal_s}"
      and steps: "\<forall> i. (t i, t (Suc i))
           \<in> SN_rel_ext_step (qrstep nfs Q P) (qrstep nfs Q Pw) (qrstep nfs Q R) (qrstep nfs Q Rw) (k i)"
    {
      fix i
      have "(t i, t (Suc i)) \<in> qrstep nfs Q (P \<union> R) \<union> qrstep nfs Q (Pw \<union> Rw)" 
        using steps[rule_format, of i]
        by (cases "k i", auto simp: qrstep_union)
    }
    with SN_rel_on_imp_SN_rel_on_alt[OF SN, unfolded SN_rel_on_alt_def, rule_format, of t]
    have noninf: "\<not> (\<exists>\<^sub>\<infinity>j. (t j, t (Suc j)) \<in> qrstep nfs Q (P \<union> R))" by auto
    {
      fix i
      assume "k i \<in> {top_s, normal_s}"
      with steps[rule_format, of i]
      have "(t i, t (Suc i)) \<in> qrstep nfs Q (P \<union> R)"
        by (cases "k i", auto simp: qrstep_union)
    }
    with strict noninf
    show False unfolding INFM_nat by blast
  qed
qed
  

datatype (dead 'f, dead 'l, dead 'v) dp_termination_proof =
  P_is_Empty
| Subterm_Criterion_Proc "('f, 'l) lab projL" "('f, 'l, 'v) rseqL"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
| Gen_Subterm_Criterion_Proc "('f, 'l) lab status_impl"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
| Redpair_Proc "('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL"  "('f, 'l, 'v) dp_termination_proof"
| Redpair_UR_Proc "('f, 'l) lab redtriple_impl"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof" 
| Usable_Rules_Proc "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof" 
| Dep_Graph_Proc "(('f, 'l, 'v) dp_termination_proof option \<times> ('f, 'l, 'v) trsLL) list"
| Mono_Redpair_Proc "('f, 'l) lab redtriple_impl"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof" 
| Mono_URM_Redpair_Proc "('f, 'l) lab redtriple_impl"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof" 
| Mono_Redpair_UR_Proc "('f, 'l) lab redtriple_impl"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
| Size_Change_Subterm_Proc "((('f, 'l) lab, 'v) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list"
| Size_Change_Redpair_Proc "('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL option"
    "((('f, 'l) lab, 'v) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list"
| Uncurry_Proc "nat option" "(('f, 'l) lab, 'v) uncurry_info"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
| Fcc_Proc "('f, 'l) lab" "(('f, 'l) lab, 'v) ctxt list"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
| Split_Proc
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" 
    "('f, 'l, 'v) dp_termination_proof" "('f, 'l, 'v) dp_termination_proof"
| Semlab_Proc
    "(('f, 'l) lab, 'v) sl_variant" "('f, 'l, 'v) trsLL"
    "(('f, 'l) lab, 'v) term list" "('f, 'l, 'v) trsLL"
    "('f, 'l, 'v) dp_termination_proof"
| Switch_Innermost_Proc "(('f, 'l) lab,'v) join_info" "('f, 'l, 'v) dp_termination_proof"
| Rewriting_Proc
    "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) ruleLL"
    "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) ruleLL" pos "('f, 'l, 'v) dp_termination_proof"
| Instantiation_Proc "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
| Forward_Instantiation_Proc
    "('f, 'l, 'v) ruleLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL option" "('f, 'l, 'v) dp_termination_proof"
| Narrowing_Proc "('f, 'l, 'v) ruleLL" pos "('f, 'l, 'v) trsLL" "('f, 'l, 'v) dp_termination_proof"
| Assume_Finite
    "('f, 'l, 'v) dppLL" "('f,'l,'v,('f, 'l, 'v) trs_termination_proof,('f, 'l, 'v) dp_termination_proof,('f, 'l, 'v) fptrs_termination_proof,('f, 'l, 'v) unknown_proof) assm_proof list"
| Q_Reduction_Proc "('f, 'l, 'v) termsLL" "('f, 'l, 'v) dp_termination_proof"
| Complex_Constant_Removal_Proc "(('f,'l)lab,'v)complex_constant_removal_prf" "('f, 'l, 'v) dp_termination_proof"
| General_Redpair_Proc
    "('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL"
    "(('f, 'l) lab, 'v) cond_red_pair_prf" "('f, 'l, 'v) dp_termination_proof list" 
| To_Trs_Proc "('f, 'l, 'v) trs_termination_proof"
and ('f, 'l, 'v) trs_termination_proof =
  DP_Trans bool bool "(('f, 'l) lab, 'v) rules" "('f, 'l, 'v) dp_termination_proof"
| Rule_Removal "('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL" "('f, 'l, 'v)trs_termination_proof"
| String_Reversal "('f, 'l, 'v) trs_termination_proof"
| Constant_String "(('f,'l)lab,'v)const_string_sound_proof" "('f,'l,'v) trs_termination_proof"
| Bounds "(('f, 'l) lab, 'v) bounds_info"
| Uncurry "(('f, 'l) lab, 'v) uncurry_info" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
| Semlab
    "(('f, 'l) lab, 'v) sl_variant" "(('f, 'l) lab, 'v) term list"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
| R_is_Empty
| Fcc "(('f, 'l) lab, 'v) ctxt list" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
| Split "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof" "('f, 'l, 'v) trs_termination_proof"
| Switch_Innermost "(('f, 'l) lab,'v) join_info" "('f, 'l, 'v) trs_termination_proof" 
| Drop_Equality "('f, 'l, 'v) trs_termination_proof"
| Remove_Nonapplicable_Rules "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof"
| Permuting_AFS "('f,'l)lab afs_list" "('f, 'l, 'v) trs_termination_proof"
| Right_Ground_Termination
| Assume_SN "('f, 'l, 'v) qreltrsLL" "('f,'l,'v,('f, 'l, 'v) trs_termination_proof,('f, 'l, 'v) dp_termination_proof,('f, 'l, 'v) fptrs_termination_proof,('f, 'l, 'v) unknown_proof) assm_proof list"
and ('f, 'l, 'v) unknown_proof =
  Assume_Unknown unknown_info "('f,'l,'v,('f, 'l, 'v) trs_termination_proof,('f, 'l, 'v) dp_termination_proof,('f, 'l, 'v) fptrs_termination_proof,('f, 'l, 'v) unknown_proof) assm_proof list"
and ('f, 'l, 'v) fptrs_termination_proof =
  Assume_FP_SN "('f,'l,'v)fptrsLL" "('f,'l,'v,('f, 'l, 'v) trs_termination_proof,('f, 'l, 'v) dp_termination_proof,('f, 'l, 'v) fptrs_termination_proof,('f, 'l, 'v) unknown_proof) assm_proof list"


fun dp_assms :: "bool \<Rightarrow> ('f, 'l, 'v) dp_termination_proof \<Rightarrow> ('f, 'l, 'v) assm list" 
  and sn_assms :: "bool \<Rightarrow> ('f,'l,'v) trs_termination_proof \<Rightarrow> ('f,'l,'v) assm list" 
  and sn_fp_assms :: "bool \<Rightarrow> ('f,'l,'v) fptrs_termination_proof \<Rightarrow> ('f,'l,'v) assm list" 
  and unknown_assms :: "bool \<Rightarrow> ('f,'l,'v) unknown_proof \<Rightarrow> ('f,'l,'v) assm list" 
  where
  "dp_assms a P_is_Empty = []"
| "dp_assms a (Subterm_Criterion_Proc _ _ _ p) = dp_assms a p"
| "dp_assms a (Gen_Subterm_Criterion_Proc _ _ p) = dp_assms a p"
| "dp_assms a (Redpair_Proc _ _ p) = dp_assms a p"
| "dp_assms a (Redpair_UR_Proc _ _ _ p) = dp_assms a p"
| "dp_assms a (Usable_Rules_Proc _ p) = dp_assms a p"
| "dp_assms a (Dep_Graph_Proc ps) =
    concat (concat (map (map (dp_assms a) \<circ> option_to_list \<circ> fst) ps))"
| "dp_assms a (Mono_Redpair_Proc _ _ _ p) = dp_assms a p"
| "dp_assms a (Mono_URM_Redpair_Proc _ _ _ p) = dp_assms a p"
| "dp_assms a (Mono_Redpair_UR_Proc _ _ _ _ p) = dp_assms a p"
| "dp_assms a (Size_Change_Subterm_Proc _) = []"
| "dp_assms a (Size_Change_Redpair_Proc _ _ _) = []"
| "dp_assms a (Uncurry_Proc _ _ _ _ p) = dp_assms a p"
| "dp_assms a (Fcc_Proc _ _ _ _ p) = dp_assms a p"
| "dp_assms a (Split_Proc _ _ p q) = dp_assms a p @ dp_assms a q"
| "dp_assms a (Semlab_Proc _ _ _ _ p) = dp_assms a p"
| "dp_assms a (Switch_Innermost_Proc _ p) = dp_assms a p"
| "dp_assms a (Rewriting_Proc _ _ _ _ _ _ p) = dp_assms a p"
| "dp_assms a (Narrowing_Proc _ _ _ p) = dp_assms a p"
| "dp_assms a (Instantiation_Proc _ _ p) = dp_assms a p"
| "dp_assms a (Forward_Instantiation_Proc _ _ _ p) = dp_assms a p"
| "dp_assms a (Q_Reduction_Proc _ p) = dp_assms a p"
| "dp_assms a (General_Redpair_Proc _ _ _ _ ps) = concat (map (dp_assms a) ps)"
| "dp_assms a (Complex_Constant_Removal_Proc _ p) = dp_assms a p"
| "dp_assms a (To_Trs_Proc p) = sn_assms a p"
| "dp_assms a (Assume_Finite d dps) = (if a then Finite_assm (map assm_proof_to_problem dps) d 
    # concat (map (collect_assms (sn_assms a) (dp_assms a) (sn_fp_assms a) (unknown_assms a)) dps) else [])"
| "sn_assms a (DP_Trans _ _ _ p) = dp_assms a p"
| "sn_assms a (Rule_Removal _ _ p) = sn_assms a p"
| "sn_assms a (String_Reversal p) = sn_assms a p"
| "sn_assms a (Constant_String _ p) = sn_assms a p"
| "sn_assms a (Bounds _) = []"
| "sn_assms a (Uncurry _ _ p) = sn_assms a p"
| "sn_assms a (Semlab _ _ _ p) = sn_assms a p"
| "sn_assms a R_is_Empty = []"
| "sn_assms a (Fcc _ _ p) = sn_assms a p"
| "sn_assms a (Split _ p q) = sn_assms a p @ sn_assms a q"
| "sn_assms a (Switch_Innermost _ p) = sn_assms a p"
| "sn_assms a (Drop_Equality p) = sn_assms a p"
| "sn_assms a (Remove_Nonapplicable_Rules _ p) = sn_assms a p"
| "sn_assms a (Permuting_AFS _ p) = sn_assms a p"
| "sn_assms a Right_Ground_Termination = []"
| "sn_assms a (Assume_SN t tps) = (if a then SN_assm (map assm_proof_to_problem tps) t 
    # concat (map (collect_assms (sn_assms a) (dp_assms a) (sn_fp_assms a) (unknown_assms a)) tps) else [])"
| "sn_fp_assms a (Assume_FP_SN t tps) = (if a then SN_FP_assm (map assm_proof_to_problem tps) t 
    # concat (map (collect_assms (sn_assms a) (dp_assms a) (sn_fp_assms a)  (unknown_assms a)) tps) else [])"
| "unknown_assms a (Assume_Unknown t tps) = (if a then Unknown_assm (map assm_proof_to_problem tps) t 
    # concat (map (collect_assms (sn_assms a) (dp_assms a) (sn_fp_assms a)  (unknown_assms a)) tps) else [])"

lemma assms_False [simp]: 
  "dp_assms False (p :: ('f,'l,'v)dp_termination_proof) = []" 
  "sn_assms False (q :: ('f,'l,'v)trs_termination_proof) = []"
  "sn_fp_assms False (r :: ('f,'l,'v)fptrs_termination_proof) = []"
  "unknown_assms False (s :: ('f,'l,'v)unknown_proof) = []"
  by (induct p and q and r and s
  rule: dp_assms_sn_assms_sn_fp_assms_unknown_assms.induct[of 
    "\<lambda> a p. dp_assms False p = []" 
    "\<lambda> a q. sn_assms False q = []" 
    "\<lambda> a q. sn_fp_assms False q = []" 
    "\<lambda> a q. unknown_assms False q = []"], auto)


fun
  get_fcc_option ::
    "('f, 'l, 'v) dp_termination_proof \<Rightarrow>
    (('f, 'l) lab \<times> (('f, 'l) lab, 'v) ctxt list \<times> ('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) dp_termination_proof)option"
where
  "get_fcc_option (Fcc_Proc f fcs Pb' Rb' prf) = Some (f, fcs, Pb', Rb', prf)" |
  "get_fcc_option _ = None"

lemma (in tp_spec) mk_tp_set: "mk_tp_set t = tp_ops.qreltrs I (mk_tp I t)" by (cases t, auto)
lemma (in dpp_spec) mk_dpp_set: "mk_dpp_set t = dpp_ops.dpp I (mk_dpp I t)" by (cases t, auto)

hide_const (open) AC_Subterm_Criterion.proj_term

text \<open>The parameter "assms" is a flag that specifies whether partial proofs
(i.e, containing assumptions) are accepted or not.\<close>
context 
  fixes   J :: "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops"
  and I :: "('dpp, ('f, label_type) lab, string) dpp_ops"
  and assms :: bool
begin

fun check_assm :: "('tp \<Rightarrow> 'tp_prf \<Rightarrow> showsl check)
  \<Rightarrow> ('dpp \<Rightarrow> 'dpp_prf \<Rightarrow> showsl check)
  \<Rightarrow> (('f,label_type,string)fptrsLL \<Rightarrow> 'fptp_prf \<Rightarrow> showsl check)
  \<Rightarrow> (unknown_info \<Rightarrow> 'unk_prf \<Rightarrow> showsl check)
  \<Rightarrow> ('f,label_type,string, 'tp_prf, 'dpp_prf, 'fptp_prf, 'unk_prf) assm_proof \<Rightarrow> showsl check" where
  "check_assm tp_check dp_check fptp_check unk_check (SN_assm_proof t prf) = tp_check (mk_tp J t) prf"
| "check_assm tp_check dp_check fptp_check unk_check (Finite_assm_proof t prf) = dp_check (mk_dpp I t) prf"
| "check_assm tp_check dp_check fptp_check unk_check (Unknown_assm_proof t prf) = unk_check t prf"
| "check_assm tp_check dp_check fptp_check unk_check (SN_FP_assm_proof t prf) = fptp_check t prf"
| "check_assm _ _ _ _ _ = error (showsl_lit (STR ''no support for non-termination assumptions in termination proof''))"

lemma check_assms_cong[fundef_cong]: 
  assumes 
  "\<And> t p. i = SN_assm_proof t p \<Longrightarrow> tp (mk_tp J t) p = tp' (mk_tp J t) p" 
  "\<And> t p. i = Finite_assm_proof t p \<Longrightarrow> dpp (mk_dpp I t) p = dpp' (mk_dpp I t) p" 
  "\<And> t p. i = SN_FP_assm_proof t p \<Longrightarrow> fptp t p = fptp' t p" 
  "\<And> t p. i = Unknown_assm_proof t p \<Longrightarrow> unk t p = unk' t p" 
  shows "check_assm tp dpp fptp unk i = check_assm tp' dpp' fptp' unk' i" 
  using assms 
  by (cases i, auto)

lemma check_assm: 
  assumes 
  "\<And> t p. i = SN_assm_proof t p \<Longrightarrow> isOK(tp (mk_tp J t) p) \<Longrightarrow> SN_qrel (mk_tp_set t)"
  "\<And> d p. i = Finite_assm_proof d p \<Longrightarrow> isOK(dpp (mk_dpp I d) p) \<Longrightarrow> finite_dpp (mk_dpp_set d)" 
  "\<And> t p. i = SN_FP_assm_proof t p \<Longrightarrow> isOK(fptp t p) \<Longrightarrow> SN_fpstep (mk_fptp_set t)"
  "\<And> d p. i = Unknown_assm_proof d p \<Longrightarrow> isOK(unk d p) \<Longrightarrow> unknown_satisfied d" 
  shows "isOK(check_assm tp dpp fptp unk i) \<Longrightarrow> satisfied (assm_proof_to_problem i)"
  using assms 
  by (cases i, auto)

function
  check_dp_termination_proof ::
    "showsl \<Rightarrow> 'dpp \<Rightarrow>
    ('f, label_type, string) dp_termination_proof \<Rightarrow>
    showsl check"
  and check_trs_termination_proof ::
    "showsl \<Rightarrow> 'tp \<Rightarrow>
     ('f, label_type, string) trs_termination_proof \<Rightarrow>
     showsl check" 
  and check_fptrs_termination_proof ::
    "showsl \<Rightarrow> ('f,label_type,string)fptrsLL \<Rightarrow>
     ('f, label_type, string) fptrs_termination_proof \<Rightarrow>
     showsl check" 
  and check_unknown_proof ::
    "showsl \<Rightarrow> unknown_info \<Rightarrow>
     ('f, label_type, string) unknown_proof \<Rightarrow>
     showsl check" 
where
  "check_dp_termination_proof i dpp P_is_Empty = debug i (STR ''P is empty'')
     (if dpp_ops.P I dpp = [] \<and> (dpp_ops.Pw I dpp = [] \<or> dpp_ops.R I dpp = []) 
          then succeed
          else error (i \<circ> showsl_lit (STR '': P is not empty in the following DP-problem\<newline>'') \<circ> showsl_dpp I dpp))"
| "check_dp_termination_proof i dpp (Subterm_Criterion_Proc p rseq Pr prf) =
    debug i (STR ''Subterm_Criterion_Proc'') (do {
      let P  = dpp_ops.pairs I dpp;
      dpp' \<leftarrow> subterm_criterion_proc I p rseq Pr dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the subterm criterion to the DP problem\<newline>'')
          \<circ> showsl_dpp I dpp 
          \<circ> showsl_lit (STR ''\<newline>and trying to remove the pairs\<newline>'') \<circ> showsl_rules Pr
          \<circ> showsl_nl \<circ> s);
      check_dp_termination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the subterm criterion\<newline>'')
          \<circ>  s)
    })"
| "check_dp_termination_proof i dpp (Gen_Subterm_Criterion_Proc p Pr prf) =
    debug i (STR ''Gen_Subterm_Criterion_Proc'') (do {
      dpp' \<leftarrow> generalized_subterm_proc I p Pr dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the generalized subterm criterion to the DP problem\<newline>'')
          \<circ> showsl_dpp I dpp
          \<circ> showsl_lit (STR ''\<newline>and trying to remove the pairs\<newline>'') \<circ> showsl_rules Pr
          \<circ> showsl_nl \<circ> s);
      check_dp_termination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the generalized subterm criterion\<newline>'')
          \<circ>  s)
    })"
| "check_dp_termination_proof i dpp (Redpair_Proc redp Pr prf) = debug i (STR ''Redpair_Proc'') (do {
         let P = dpp_ops.pairs I dpp;
         let Proc = (let rp = get_rel_impl redp in if isOK(rel_impl.standard rp) then
                    generic_ur_af_redtriple_proc I rp None
                   else generic_ur_af_root_redtriple_proc I rp None);
         dpp' \<leftarrow> Proc Pr dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the reduction pair processor to remove from the DP problem\<newline>'')
             \<circ> showsl_dpp I dpp
             \<circ> showsl_lit (STR ''\<newline> the pairs\<newline>'') \<circ> showsl_rules Pr \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the reduction pair processor\<newline>'') \<circ>  s)
   })" 
| "check_dp_termination_proof i dpp (Usable_Rules_Proc U prf) = debug i (STR ''Usable_Rules_Proc'') (do {
         dpp' \<leftarrow> usable_rules_proc I U dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the usable rules processor to restrict the DP problem\<newline>'')
             \<circ> showsl_dpp I dpp
             \<circ> showsl_lit (STR ''\<newline>to the usable rules\<newline>'') \<circ> showsl_rules U \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the usable rules processor\<newline>'') \<circ>  s)
   })"
| "check_dp_termination_proof i dpp (Q_Reduction_Proc Q prf) = debug i (STR ''Q_Reduction_Proc'') (do {
         dpp' \<leftarrow> q_reduction_proc I Q dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the Q-reduction processor\<newline>'') \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the Q-reduction processor\<newline>'') \<circ>  s)
   })"
|  "check_dp_termination_proof i dpp (Mono_Redpair_Proc redp Pr Rr prf) = debug i (STR ''Mono_Redpair_Proc'') (do {
         dpp' \<leftarrow> mono_redpair_proc I (get_rel_impl redp) Pr Rr dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the mono reduction pair processor to remove from the DP problem\<newline>'')
             \<circ> showsl_dpp I dpp
             \<circ> showsl_lit (STR ''\<newline> the pairs\<newline>'') \<circ> showsl_rules Pr
             \<circ> showsl_lit (STR ''\<newline> and the rules\<newline>'') \<circ> showsl_rules Rr \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the mono reduction pair processor\<newline>'') \<circ>  s)
   })" 
|  "check_dp_termination_proof i dpp (Mono_URM_Redpair_Proc redp Pr Rr prf) = debug i (STR ''Mono_URM_Redpair_Proc'') (do {
         dpp' \<leftarrow> mono_urm_redpair_proc I (get_rel_impl redp) Pr Rr dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the mono reduction pair processor with usable repl. map to remove from the DP problem\<newline>'')
             \<circ> showsl_dpp I dpp
             \<circ> showsl_lit (STR ''\<newline> the pairs\<newline>'') \<circ> showsl_rules Pr 
             \<circ> showsl_lit (STR ''\<newline> and the rules\<newline>'') \<circ> showsl_rules Rr \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the mono reduction pair processor\<newline>'') \<circ>  s)
   })" 
| "check_dp_termination_proof i dpp (Dep_Graph_Proc edpts) =
     debug i (STR ''Dep_Graph_Proc'') (do {
        pdpps \<leftarrow> dep_graph_proc I dpp edpts
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error while trying to perform Sctxt_closure-decomposition  on\<newline>'') \<circ>
           showsl_dpp I dpp \<circ> showsl_nl \<circ> s);
        check_allm_index (\<lambda> (prof,dpp') j. check_dp_termination_proof (add_index i (Suc j)) dpp' prof) pdpps
          <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the dependency graph processor\<newline>'') \<circ>  s)
  })"
| "check_dp_termination_proof i dpp (Redpair_UR_Proc redp Pr ur prf) = debug i (STR ''Redpair_UR_Proc'') (do {
         let Proc = (let rp = get_rel_impl redp in 
                       if isOK(rel_impl.standard rp) then generic_ur_af_redtriple_proc I rp (Some ur) 
                        else generic_ur_af_root_redtriple_proc I rp (Some ur));
         dpp' \<leftarrow> Proc Pr dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the reduction pair processor with usable rules to remove from the DP problem\<newline>'')
             \<circ> showsl_dpp I dpp 
             \<circ> showsl_lit (STR ''\<newline> the pairs\<newline>'') \<circ> showsl_rules Pr \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the reduction pair processor\<newline>'') \<circ>  s)
   })" 
|  "check_dp_termination_proof i dpp (Mono_Redpair_UR_Proc redp Pr Rr ur prf) = debug i (STR ''Mono_Redpair_UR_Proc'') (do {
         dpp' \<leftarrow> generic_mono_ur_redpair_proc I (get_rel_impl redp) Pr Rr ur dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the mono reduction pair processor with usable rules to remove from the DP problem\<newline>'')
             \<circ> showsl_dpp I dpp
             \<circ> showsl_lit (STR ''\<newline> the pairs\<newline>'') \<circ> showsl_rules Pr
             \<circ> showsl_lit (STR ''\<newline> and the rules\<newline>'') \<circ> showsl_rules Rr \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the mono reduction pair processor with usable rules\<newline>'')
             \<circ>  s)
   })" 
| "check_dp_termination_proof i dpp (Uncurry_Proc mode u_info P' R' prf) = 
    debug i (STR ''Uncurry_Proc'') (do {
      dpp' \<leftarrow> uncurry_proc_both I mode u_info P' R' dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the uncurrying processor on the DP problem\<newline>'') 
        \<circ> showsl_dpp I dpp \<circ> showsl_nl \<circ> s);
      check_dp_termination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the uncurrying processor\<newline>'') \<circ>  s)
    })"
| "check_dp_termination_proof i dpp (Size_Change_Subterm_Proc graphs) =
     debug i (STR ''Size_Change_Subterm_Proc'') (sct_subterm_proc I graphs dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the size-change (subterm) processor on the DP problem\<newline>'')
          \<circ> showsl_dpp I dpp \<circ> showsl_nl \<circ> s))"
| "check_dp_termination_proof i dpp (Size_Change_Redpair_Proc redp U_opt graphs) =
     debug i (STR ''Size_Change_Redpair_Proc'') (sct_ur_af_proc I (get_rel_impl redp) graphs U_opt dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the size-change (redpair) processor on the DP problem\<newline>'')
          \<circ> showsl_dpp I dpp \<circ> showsl_nl \<circ> s))"
| "check_dp_termination_proof i dpp (Fcc_Proc f fcs Pb' R' prf) = debug i (STR ''Fcc_Proc'') (do {
    dpp' \<leftarrow> fcc_proc I f fcs Pb' R' dpp
      <+? (\<lambda>s. i \<circ>
        showsl_lit (STR '': error when applying the flat context closure processor on the DP problem\<newline>'')
        \<circ> showsl_dpp I dpp \<circ> showsl_nl \<circ> s);
    check_dp_termination_proof (add_index i 1) dpp' prf
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the flat context closure processor\<newline>'')
        \<circ>  s)
  })"
| "check_dp_termination_proof i dpp (Split_Proc Prem Rrem prf1 prf2) = debug i (STR ''Split_Proc'') (case get_fcc_option prf1 of 
          Some (f,fcs,Pb',Rb',prf1') \<Rightarrow> debug i (STR ''Split_ProcFcc'') (do {
            (dpp1,dpp2) \<leftarrow> fcc_split_proc I f fcs Pb' Rb' Prem Rrem dpp;
            check_dp_termination_proof (add_index (add_index i 1) 1) dpp1 prf1'
              <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the split and fcc processor\<newline>'') \<circ>  s);
            check_dp_termination_proof (add_index i 2) dpp2 prf2
              <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the split processor\<newline>'') \<circ>  s)
          })
       | None \<Rightarrow> do {
    let (dpp1,dpp2) = split_proc I dpp Prem Rrem;
    check_dp_termination_proof (add_index i 1) dpp1 prf1
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the split processor\<newline>'') \<circ>  s);
    check_dp_termination_proof (add_index i 2) dpp2 prf2
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the split processor\<newline>'') \<circ>  s)
  })" 
| "check_dp_termination_proof i dpp (Semlab_Proc sli lP lQ lR prf) = 
    debug i (STR ''Semlab_Proc'') (do {
      dpp' \<leftarrow> semlab_fin_proc I sli lP lQ lR dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the semlab processor on the DP problem\<newline>'')
          \<circ> showsl_dpp I dpp \<circ> showsl_nl \<circ> s);
      check_dp_termination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the semlab processor\<newline>'')
          \<circ>  s)
    })"
| "check_dp_termination_proof i dpp (Switch_Innermost_Proc joins prf) = 
    debug i (STR ''Switch_Innermost_Proc'') (do {
      dpp' \<leftarrow> switch_innermost_proc string_rename I joins dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the processor to switch to innermost on the DP problem\<newline>'')
          \<circ> showsl_dpp I dpp \<circ> showsl_nl \<circ> s);
      check_dp_termination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the switch to innermost processor\<newline>'') \<circ>  s)
    })"
| "check_dp_termination_proof i dpp (Assume_Finite dpp' ass) =
    debug i (STR ''Finiteness Assumption or Unknown Proof'') (
      if assms
        then (do {
          check_dpp_subsumes I dpp' dpp
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in finiteness assumption or unknown proof\<newline>'') \<circ> s \<circ> showsl_nl);
          check_allm_index (\<lambda> as j. check_assm 
             (check_trs_termination_proof (add_index i (Suc j)))
             (check_dp_termination_proof (add_index i (Suc j)))
             (check_fptrs_termination_proof (add_index i (Suc j)))
             (check_unknown_proof (add_index i (Suc j)))
             as)
             ass
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below unknown proof\<newline>'')
                 \<circ>  s)
        }) else error (i \<circ> showsl_lit (STR '': the proof contains a finiteness assumption or unknown proof\<newline>''))
    )"
| "check_dp_termination_proof i dpp (Rewriting_Proc U_opt st st' st'' lr p prf) = debug i (STR ''Rewriting_Proc'') (do {
         dpp' \<leftarrow> rewriting_proc I U_opt st st' st'' lr p dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the rewriting processor to rewrite the pair \<newline>'')
             \<circ> showsl_rule st \<circ> 
             showsl_lit (STR ''\<newline> to the pair \<newline>'') \<circ> showsl_rule st'' \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the rewriting processor\<newline>'') \<circ>  s)
   })" 
| "check_dp_termination_proof i dpp (Narrowing_Proc st p sts prf) = debug i (STR ''Narrowing_Proc'') (do {
         dpp' \<leftarrow> narrowing_proc I st p sts dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the narrowing processor to narrow the pair \<newline>'')
             \<circ> showsl_rule st \<circ> 
             showsl_lit (STR ''\<newline> to the pairs \<newline>'') \<circ> showsl_trs sts \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the narrowing processor\<newline>'') \<circ>  s)
   })" 
| "check_dp_termination_proof i dpp (Instantiation_Proc st sts prf) = debug i (STR ''Instantiation_Proc'') (do {
         dpp' \<leftarrow> instantiation_proc I st sts dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the instantiation processor to instantiate the pair \<newline>'')
             \<circ> showsl_rule st \<circ> 
             showsl_lit (STR ''\<newline> to the pairs \<newline>'') \<circ> showsl_trs sts \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the instantiation processor\<newline>'') \<circ>  s)
   })" 
| "check_dp_termination_proof i dpp (Forward_Instantiation_Proc st sts u_opt prf) = debug i (STR ''Forward_Instantiation_Proc'') (do {
         dpp' \<leftarrow> forward_instantiation_proc I st sts u_opt dpp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the forward_instantiation processor to instantiate the pair \<newline>'')
             \<circ> showsl_rule st \<circ> 
             showsl_lit (STR ''\<newline> to the pairs \<newline>'') \<circ> showsl_trs sts \<circ> showsl_nl \<circ> s);
         check_dp_termination_proof (add_index i 1) dpp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the forward instantiation processor\<newline>'') \<circ>  s)
   })" 
| "check_dp_termination_proof i dpp (General_Redpair_Proc rp ps pb prof prfs) =
    debug i (STR ''General_Redpair_ProcProc'') (do {
      let n = length prfs;
      check (n > 0) (showsl_lit (STR ''at least one subproof is required''));
      let Merge = (n = 1);
      dpps \<leftarrow> conditional_general_reduction_pair_proc I (get_non_inf_order rp) ps pb prof Merge dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the generic reduction pair processor to the DP problem\<newline>'')
          \<circ> showsl_dpp I dpp \<circ> showsl_nl \<circ> s);
      check_dp_termination_proof (add_index i 1) (dpps ! 0) (prfs ! 0)
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the generic reduction pair processor\<newline>'') \<circ>  s);
      if Merge then succeed else (
        check_dp_termination_proof (add_index i 2) (dpps ! 1) (prfs ! 1)
          <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the generic reduction pair processor\<newline>'')
            \<circ>  s))
    })"
| "check_dp_termination_proof i dpp (Complex_Constant_Removal_Proc p prf) =
    debug i (STR ''Complex_Constant_Removal_Proc'') (do {
      dpp' \<leftarrow> complex_constant_removal_proc string_rename I p dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the complex constant removal processor to the DP problem\<newline>'')
          \<circ> showsl_dpp I dpp
          \<circ> showsl_nl \<circ> s);
      check_dp_termination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the complex constant removal processor\<newline>'')
          \<circ>  s)
    })"
| "check_dp_termination_proof i dpp (To_Trs_Proc prf) =
    debug i (STR ''To_Trs_Proc'') (do {      
      check_trs_termination_proof (add_index i 1) 
        (mk_tp J (dpp_ops.nfs I dpp, dpp_ops.Q I dpp, dpp_ops.P I dpp @ dpp_ops.R I dpp, dpp_ops.Pw I dpp @ dpp_ops.Rw I dpp)) prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the To-Trs processor\<newline>'') \<circ>  s)
    })"
| "check_trs_termination_proof i tp R_is_Empty = debug i (STR ''R is empty'')
     (if tp_ops.R J tp = []
          then succeed 
          else error (i \<circ> showsl_lit (STR '': R is not empty in the following termination-problem \<newline>'')
            \<circ> showsl_tp J tp))"
|  "check_trs_termination_proof i tp (Rule_Removal redp Rr prf) = debug i (STR ''Rule Removal'') (do {
         tp' \<leftarrow> rule_removal_tt J (get_rel_impl redp) Rr tp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying the rule removal technique on \<newline>'')
             \<circ> showsl_tp J tp \<circ> 
             showsl_lit (STR ''\<newline> to remove the rules \<newline>'') \<circ> showsl_rules Rr \<circ> showsl_nl \<circ> s);
         check_trs_termination_proof (add_index i 1) tp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the rule removal technique\<newline>'') \<circ>  s)
   })" 
| "check_trs_termination_proof i tp (DP_Trans nfs m P prf) = debug i (STR ''DP trans'') (do {
     dpp \<leftarrow> dependency_pairs_tt Sharp J I tp nfs m P
       <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when switching from the TRS\<newline>'') \<circ> showsl_tp J tp
         \<circ> showsl_lit (STR ''\<newline>to the initial DP problem with pairs \<newline>'') \<circ> showsl_rules P \<circ> showsl_nl \<circ> s);
     check_dp_termination_proof (add_index i 1) dpp prf
       <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below switch to dependency pairs\<newline>'') \<circ>  s)
   })" 
|  "check_trs_termination_proof i tp (String_Reversal prf) = debug i (STR ''String Reversal'') (do {
         tp' \<leftarrow> string_reversal_tt J tp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying string reversal on \<newline>'')
             \<circ> showsl_tp J tp \<circ> showsl_nl \<circ> s);
         check_trs_termination_proof (add_index i 1) tp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the string reversal technique\<newline>'') \<circ>  s)
   })" 
|  "check_trs_termination_proof i tp (Constant_String p prf) = debug i (STR ''Constant to Unary'') (do {
         tp' \<leftarrow> const_to_string_sound_tt p J tp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when turning constants into unary symbols on '')
             \<circ> showsl_nl \<circ> showsl_tp J tp \<circ> showsl_nl \<circ> s);
         check_trs_termination_proof (add_index i 1) tp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the constant to unary technique\<newline>'')\<circ>  s)
   })" 
|  "check_trs_termination_proof i tp (Semlab sli lQ lAll prf) = debug i (STR ''Semlab'') (do {
         tp' \<leftarrow> semlab_fin_tt J sli lQ lAll tp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying semantic labelling on '')
             \<circ> showsl_nl \<circ> showsl_tp J tp \<circ> showsl_nl \<circ> s);
         check_trs_termination_proof (add_index i 1) tp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the sem.lab technique\<newline>'')
             \<circ>  s)
   })" 
| "check_trs_termination_proof i tp (Bounds info) = debug i (STR ''Bounds'') (do {
     bounds_tt J info tp 
       <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying bounds on the termination problem \<newline>'') \<circ> showsl_tp J tp \<circ> showsl_nl \<circ> s)})" 
| "check_trs_termination_proof i tp (Uncurry u_info rR prf) = debug i (STR ''Uncurry'') (do {
     tp' \<leftarrow> uncurry_tt J u_info rR tp
       <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying currying transformation\<newline>'') \<circ> s);
     check_trs_termination_proof (add_index i 1) tp' prf
       <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the uncurrying technique\<newline>'') \<circ>  s)
   })"
| "check_trs_termination_proof i tp (Fcc fcs R' prf) = debug i (STR ''Fcc'') (do {
    tp' \<leftarrow> fcc_tt J fcs R' tp
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying flat context closure\<newline>'') \<circ> s);
    check_trs_termination_proof (add_index i 1) tp' prf
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below flat context closure\<newline>'') \<circ>  s)
  })"
| "check_trs_termination_proof i tp (Split Rrem prf1 prf2) = debug i (STR ''Split'') (do {
    let (tp1,tp2) = split_tt J tp Rrem;
    check_trs_termination_proof (add_index i 1) tp1 prf1
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the splitting\<newline>'') \<circ>  s);
    check_trs_termination_proof (add_index i 2) tp2 prf2
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the splitting\<newline>'') \<circ>  s)
  })"
|  "check_trs_termination_proof i tp (Switch_Innermost joins prf) = debug i (STR ''Switch Innermost'') (do {
         tp' \<leftarrow> switch_innermost_tt string_rename J joins tp 
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when switching to innermost on \<newline>'')
             \<circ> showsl_tp J tp \<circ> showsl_nl \<circ> s);
         check_trs_termination_proof (add_index i 1) tp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the switch to innermost\<newline>'') \<circ>  s)
   })" 
|  "check_trs_termination_proof i tp (Drop_Equality prf) = debug i (STR ''Drop Equality'') (do {
         let tp' = tp_ops.mk J (tp_ops.nfs J tp) (tp_ops.Q J tp) (tp_ops.R J tp) (filter (\<lambda> (l,r). l \<noteq> r) (tp_ops.Rw J tp));
         check_trs_termination_proof (add_index i 1) tp' prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below dropping equality rules\<newline>'') \<circ>  s)
   })" 
| "check_trs_termination_proof i tp (Remove_Nonapplicable_Rules r prf) = debug i (STR ''Removing non-applicable rules'') (do {
       let R = tp_ops.R J tp;
       check_non_applicable_rules (tp_ops.is_QNF J tp) r
         <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error when removing non-applicable rules\<newline>'') \<circ>  (showsl_rule s \<circ> showsl_lit (STR '' is applicable'')));
       let tp' = tp_spec.delete_rules J tp r;
       check_trs_termination_proof (add_index i 1) tp' prf
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the non-applicable rules removal\<newline>'') \<circ>  s)})"
| "check_trs_termination_proof i tp (Permuting_AFS pi prf) = debug i (STR ''Permuting some rules'') (do {
       tp' \<leftarrow> argument_filter_tt J pi tp 
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when permuting arguments on \<newline>'') \<circ> showsl_tp J tp \<circ> showsl_nl \<circ> s);
       check_trs_termination_proof (add_index i 1) tp' prf
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the permutation of arguments\<newline>'') \<circ>  s)})"
| "check_trs_termination_proof i tp Right_Ground_Termination = debug i (STR ''Right_Ground_Termination'') (do {
       right_ground_tt J tp 
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying right-ground decision procedure \<newline>'') \<circ> showsl_tp J tp \<circ> showsl_nl \<circ> s);
       succeed}
         )"
| "check_trs_termination_proof i tp (Assume_SN tp' ass) =
    debug i (STR ''Termination Assumption or Unknown Proof'') (
      if assms
        then (do {
          check_tp_subsumes J tp' tp
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in termination assumption or unknown proof\<newline>'') \<circ> s \<circ> showsl_nl);
          check_allm_index (\<lambda> as j. check_assm 
             (check_trs_termination_proof (add_index i (Suc j)))
             (check_dp_termination_proof (add_index i (Suc j)))
             (check_fptrs_termination_proof (add_index i (Suc j)))
             (check_unknown_proof (add_index i (Suc j)))
             as)
             ass
        }) else error (i \<circ> showsl_lit (STR '': the proof contains a termination assumption or unknown proof\<newline>''))
    )"
| "check_fptrs_termination_proof i tp (Assume_FP_SN tp' ass) =
    debug i (STR ''Outermost Termination Assumption or Unknown Proof'') (
      if assms
        then (do {
          check (tp = tp') (showsl_lit (STR ''outermost assumption does not match current goal''));
          check_allm_index (\<lambda> as j. check_assm 
             (check_trs_termination_proof (add_index i (Suc j)))
             (check_dp_termination_proof (add_index i (Suc j)))
             (check_fptrs_termination_proof (add_index i (Suc j)))
             (check_unknown_proof (add_index i (Suc j)))
             as)
             ass
        }) else error (i \<circ> showsl_lit (STR '': the proof contains a termination assumption or unknown proof\<newline>''))
    )"
| "check_unknown_proof i tp (Assume_Unknown tp' ass) =
    debug i (STR ''Unknown Proof'') (
      if assms
        then (do {
          check (tp = tp') (showsl_lit (STR ''unknown problems are not identical: \<newline>'') \<circ> showsl tp \<circ> showsl_nl
            \<circ> showsl_lit (STR '' vs \<newline>'') \<circ> showsl tp')
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in termination assumption or unknown proof\<newline>'') \<circ> s \<circ> showsl_nl);
          check_allm_index (\<lambda> as j. check_assm
             (check_trs_termination_proof (add_index i (Suc j)))
             (check_dp_termination_proof (add_index i (Suc j)))
             (check_fptrs_termination_proof (add_index i (Suc j)))
             (check_unknown_proof (add_index i (Suc j)))
             as)
             ass
        }) else error (i \<circ> showsl_lit (STR '': the proof contains an unknown proof\<newline>''))
    )"
  by pat_completeness auto

termination
proof -
  let ?dpp = "\<lambda> x. Inl (Inl x)"
  let ?trs = "\<lambda> x. Inl (Inr x)"
  let ?fptrs = "\<lambda> x. Inr (Inl x)"
  let ?unk = "\<lambda> x. Inr (Inr x)"
  let ?M = "(\<lambda> c. case c of ?dpp (i, dpp, prof) \<Rightarrow> size prof
     | ?trs (i, tp, prof) \<Rightarrow> size prof
     | ?fptrs (i, tp, prof) \<Rightarrow> size prof
     | ?unk (i, tp, prof) \<Rightarrow> size prof)"
  show ?thesis
  proof (rule, unfold update_error_return)
    fix i dpp
      and edpts :: "(('f, label_type, string) dp_termination_proof option
        \<times> ('f, label_type, string ) trsLL) list" 
      and pdpps pdpp i' prof dpp' j
    assume proc: "dep_graph_proc I dpp edpts = Inr pdpps"
      and mem: "pdpp \<in> set pdpps" and pdpp: "(prof, dpp') = pdpp"
    show "(?dpp (add_index i (Suc j), dpp', prof), 
      ?dpp (i, dpp, Dep_Graph_Proc edpts))
      \<in> measure ?M" 
    proof -
      from proc mem [unfolded pdpp [symmetric]]
      have "Some prof \<in> set (map fst edpts)" unfolding dep_graph_proc_def by force
      then obtain P where "(Some prof, P) \<in> set edpts" by auto
      then show ?thesis
        by (induct edpts, auto)
    qed 
  next
    fix i dpp Prem Rrem prf1 prf2 a x y xa ya xb yb xc yc yd xd ye
    assume ass1: "get_fcc_option prf1 = Some a" and ass2: "(x, y) = a" "(xa, ya) = y"
           "(xb, yb) = ya" "(xc, yc) = yb"
           "fcc_split_proc I x xa xb xc Prem Rrem dpp = Inr yd" "(xd, ye) = yd"
    show "(?dpp (add_index (add_index i 1) 1, xd, yc), 
           ?dpp (i, dpp, Split_Proc Prem Rrem prf1 prf2))
             \<in> measure ?M" 
    proof -
      from ass1 obtain f fcs Pb' Rb' prf1a 
        where prf1: "prf1 = Fcc_Proc f fcs Pb' Rb' prf1a" by (cases prf1, force+)
      from ass1 ass2 
      show ?thesis unfolding prf1 by auto
    qed
  next
    fix i dpp rp ps pb c prfs x y xa ya
    show  "x = length prfs \<Longrightarrow>
         check (0 < x) (showsl_lit (STR ''at least one subproof is required'')) = Inr y \<Longrightarrow>
         xa = (x = 1) \<Longrightarrow>
         conditional_general_reduction_pair_proc I (get_non_inf_order rp) ps pb c xa dpp = Inr ya \<Longrightarrow>
         (?dpp (add_index i 1, ya ! 0, prfs ! 0), 
          (?dpp (i, dpp, General_Redpair_Proc rp ps pb c prfs)))
         \<in> measure ?M"
      by (cases prfs, auto simp: check_def)
  next
    fix x prfs xa y rp ps pb c assms i dpp ya
    show "x = length prfs \<Longrightarrow>
      check (0 < x) (showsl_lit (STR ''at least one subproof is required'')) = Inr y \<Longrightarrow>
      xa = (x = 1) \<Longrightarrow> \<not> xa \<Longrightarrow> 
      (?dpp (add_index i 2, ya ! 1, prfs ! 1), 
       ?dpp (i, dpp, General_Redpair_Proc rp ps pb c prfs))
      \<in> measure ?M"
      by (cases prfs, simp add: check_def, cases "tl prfs", auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow> x = Finite_assm_proof t p \<Longrightarrow>
         (?dpp (add_index i (Suc ia), mk_dpp I t, p), ?trs (i, tp, Assume_SN tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = SN_assm_proof t p \<Longrightarrow>
             (?trs (add_index i (Suc ia), mk_tp J t, p), ?trs (i, tp, Assume_SN tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = SN_FP_assm_proof t p \<Longrightarrow>
             (?fptrs (add_index i (Suc ia), t, p), ?trs (i, tp, Assume_SN tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = Unknown_assm_proof t p \<Longrightarrow>
             (?unk (add_index i (Suc ia), t, p), ?trs (i, tp, Assume_SN tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow> x = Finite_assm_proof t p \<Longrightarrow>
         (?dpp (add_index i (Suc ia), mk_dpp I t, p), ?dpp (i, tp, Assume_Finite tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = SN_FP_assm_proof t p \<Longrightarrow>
             (?fptrs (add_index i (Suc ia), t, p), ?dpp (i, tp, Assume_Finite tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = SN_assm_proof t p \<Longrightarrow>
             (?trs (add_index i (Suc ia), mk_tp J t, p), ?dpp (i, tp, Assume_Finite tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = Unknown_assm_proof t p \<Longrightarrow>
             (?unk (add_index i (Suc ia),  t, p), ?dpp (i, tp, Assume_Finite tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow> x = Finite_assm_proof t p \<Longrightarrow>
         (?dpp (add_index i (Suc ia), mk_dpp I t, p), ?fptrs (i, tp, Assume_FP_SN tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = SN_assm_proof t p \<Longrightarrow>
             (?trs (add_index i (Suc ia), mk_tp J t, p), ?fptrs (i, tp, Assume_FP_SN tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = SN_FP_assm_proof t p \<Longrightarrow>
             (?fptrs (add_index i (Suc ia), t, p), ?fptrs (i, tp, Assume_FP_SN tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = Unknown_assm_proof t p \<Longrightarrow>
             (?unk (add_index i (Suc ia), t, p), ?fptrs (i, tp, Assume_FP_SN tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow> x = Finite_assm_proof t p \<Longrightarrow>
         (?dpp (add_index i (Suc ia), mk_dpp I t, p), ?unk (i, tp, Assume_Unknown tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = SN_assm_proof t p \<Longrightarrow>
             (?trs (add_index i (Suc ia), mk_tp J t, p), ?unk (i, tp, Assume_Unknown tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = SN_FP_assm_proof t p \<Longrightarrow>
             (?fptrs (add_index i (Suc ia),  t, p), ?unk (i, tp, Assume_Unknown tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  next
    fix i tp tp' ass y x ia t p
    show "x \<in> set ass \<Longrightarrow>
             x = Unknown_assm_proof t p \<Longrightarrow>
             (?unk (add_index i (Suc ia),  t, p), ?unk (i, tp, Assume_Unknown tp' ass)) \<in> measure ?M"
      by (induct ass, auto)
  qed auto
qed

lemma isOK_check_dp_termination_proof_Assume_Finite_False [simp]:
  assumes "\<not> assms"
  shows "isOK (check_dp_termination_proof i dpp (Assume_Finite dpp' dps)) = False" 
  by (simp, insert assms, auto)

lemma check_dp_trs_unknown_termination_proof_with_assms: 
  assumes I: "dpp_spec I" and J: "tp_spec J"
  shows "isOK (check_dp_termination_proof i dpp prf) \<Longrightarrow> \<forall>assm\<in>set (dp_assms assms prf). holds assm
    \<Longrightarrow> finite_dpp (dpp_ops.dpp I dpp)" (is "_ \<Longrightarrow> ?P prf \<Longrightarrow> _")
    "isOK (check_trs_termination_proof i' tp prf') \<Longrightarrow> \<forall>assm\<in>set (sn_assms assms prf'). holds assm
    \<Longrightarrow> SN_qrel (tp_ops.qreltrs J tp)" (is "_ \<Longrightarrow> ?Q prf' \<Longrightarrow> _")
    "isOK (check_fptrs_termination_proof i'' fptp prf'') \<Longrightarrow> \<forall>assm\<in>set (sn_fp_assms assms prf''). holds assm
    \<Longrightarrow> SN_fpstep (mk_fptp_set fptp)" (is "_ \<Longrightarrow> ?R prf'' \<Longrightarrow> _")
    "isOK (check_unknown_proof i''' unk prf''') \<Longrightarrow> \<forall>assm\<in>set (unknown_assms assms prf'''). holds assm
    \<Longrightarrow> unknown_satisfied unk" (is "_ \<Longrightarrow> ?R prf''' \<Longrightarrow> _")
proof (induct i dpp "prf" and i' tp prf' and i'' fptp prf'' and i''' unk prf''' 
  rule: check_dp_termination_proof_check_trs_termination_proof_check_fptrs_termination_proof_check_unknown_proof.induct)
  case (1 i dpp)
  note IH = this
  interpret dpp_spec I by fact
  from IH(1) show ?case by (auto simp:
    finite_dpp_def ichain.simps)
next
  case (2 i dpp p rseq Pr prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2)
    obtain dpp' where proc: "subterm_criterion_proc I p rseq Pr dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case
    by (rule sound_proc_impl[OF subterm_criterion_proc[OF I] proc],
      rule IH(1)[OF HOL.refl _ rec fin], insert proc, simp)
next
  case (3 i dpp p Pr prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2)
    obtain dpp' where proc: "generalized_subterm_proc I p Pr dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case
    by (rule sound_proc_impl[OF generalized_subterm_proc proc],
      rule IH(1)[OF  _ rec fin], insert proc, simp)
next
  case (4 i dpp rp Pr prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH have fin: "?P prof" by simp
  let ?rp = "get_rel_impl rp"
  let ?test = "isOK(rel_impl.standard ?rp)" 
  note IH' = IH(1)[OF HOL.refl HOL.refl _ _ fin, unfolded Let_def, unfolded update_error_return sum.simps]
  show ?case 
  proof (cases ?test)
    case True
    with IH(2)
    obtain dpp' where proc: "generic_ur_af_redtriple_proc I ?rp None Pr dpp = return dpp'"
      and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
      by (auto simp: Let_def)
    from True have "?test = True" by auto
    from IH'[OF _ rec, unfolded this if_True, OF proc]
    have fin: "finite_dpp (dpp_ops.dpp I dpp')" .
    show ?thesis      
      by (rule sound_proc_impl[OF generic_ur_af_redtriple_proc[OF I get_rel_impl] _ fin], 
        rule proc)
  next
    case False
    with IH(2)
    obtain dpp' where proc: "generic_ur_af_root_redtriple_proc I ?rp None Pr dpp = return dpp'"
      and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
      by (auto simp: Let_def)
    from False have "?test = False" by auto
    from IH'[OF _ rec, unfolded this if_False, OF proc] 
    have fin: "finite_dpp (dpp_ops.dpp I dpp')" .
    show ?thesis
      by (rule sound_proc_impl[OF generic_ur_af_root_redtriple_proc[OF I get_rel_impl] _ fin], rule proc)
  qed
next
  case (5 i dpp ur prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "usable_rules_proc I ur dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case
    by (rule sound_proc_impl[OF usable_rules_proc[OF I] proc IH(1)[OF _ rec fin]], insert proc, auto)
next
  case (6 i dpp q prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2)
    obtain dpp' where proc: "q_reduction_proc I q dpp = return dpp'"
      and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
      by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case      
    by (rule sound_proc_impl[OF q_reduction_proc[OF I], OF proc IH(1), 
      unfolded update_error_return, OF proc rec fin]) 
next
  case (7 i dpp rp Pr Rr prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2)
    obtain dpp' where proc: "mono_redpair_proc I (get_rel_impl rp) Pr Rr dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case      
    by (rule sound_proc_impl[OF mono_redpair_proc[OF get_rel_impl],
      OF proc IH(1)[OF _ rec fin]],
      unfold update_error_return, rule proc)
next
  case (8 i dpp rp Pr Rr prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2)
    obtain dpp' where proc: "mono_urm_redpair_proc I (get_rel_impl rp) Pr Rr dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case   
    by (rule sound_proc_impl[OF mono_urm_redpair_proc[OF get_rel_impl I] proc IH(1)[OF _ rec fin]],
    unfold update_error_return, rule proc)
next
  case (9 i dpp edpts)
  note IH = this
  interpret dpp_spec I by fact
  from IH(2) obtain pdpps where proc: "dep_graph_proc I dpp edpts = return pdpps" 
    and rec: "\<And>j. j < length pdpps \<Longrightarrow>
      isOK ((\<lambda>(prof, dpp') j.
        check_dp_termination_proof (add_index i (Suc j)) dpp' prof) (pdpps ! j) j)"
    by auto
  show ?case
  proof (rule dep_graph_proc[OF I proc])
    fix p dpp'
    assume mem: "(p, dpp') \<in> set pdpps"
    from this[unfolded set_conv_nth]
      obtain j where j: "j < length pdpps" and pair: "pdpps ! j = (p, dpp')" by auto
    from rec[OF j] have rec: "isOK (check_dp_termination_proof (add_index i (Suc j)) dpp' p)"
      unfolding pair by simp
    from proc[unfolded dep_graph_proc_def, simplified]
      have pdpps: "pdpps =
      map (\<lambda>aP. (the (fst aP), dpp_ops.intersect_pairs I dpp (snd aP)))
          [aP\<leftarrow>edpts . \<exists>y. fst aP = Some y]" by simp
    from mem IH(3) and proc
      have fin: "?P p" by (simp add: dep_graph_proc_def) force
    show "finite_dpp (dpp_ops.dpp I dpp')" 
      by (rule IH(1)[unfolded update_error_return, OF proc mem HOL.refl rec fin])
  qed
next
  case (10 i dpp rp Pr ur prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH have fin: "?P prof" by simp
  let ?rp = "get_rel_impl rp"
  let ?test = "isOK(rel_impl.standard ?rp)" 
  note IH' = IH(1)[OF HOL.refl _ _ fin, unfolded Let_def, unfolded update_error_return sum.simps]
  show ?case 
  proof (cases ?test)
    case True
    with IH(2)
    obtain dpp' where proc: "generic_ur_af_redtriple_proc I ?rp (Some ur) Pr dpp = return dpp'"
      and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
      by (auto simp: Let_def)
    from True have id: "?test = True" by auto
    show ?thesis      
      by (rule sound_proc_impl[OF generic_ur_af_redtriple_proc[OF I get_rel_impl],
        OF proc IH'[OF _ rec, unfolded id if_True, OF proc]])
  next
    case False
    with IH(2)
    obtain dpp' where proc: "generic_ur_af_root_redtriple_proc I ?rp (Some ur) Pr dpp = return dpp'"
      and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
      by (auto simp: Let_def)
    from False have id: "?test = False" by auto
    show ?thesis      
      by (rule sound_proc_impl[OF generic_ur_af_root_redtriple_proc[OF I get_rel_impl],
            OF proc IH'[OF _ rec, unfolded id if_False, OF proc]])
  qed
next
  case (11 i dpp rp Pr Rr ur prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "generic_mono_ur_redpair_proc I (get_rel_impl rp) Pr Rr ur dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case
    by (rule sound_proc_impl[OF generic_mono_ur_redpair_proc[OF I get_rel_impl],
      OF proc IH(1)[OF _ rec fin]],
      unfold update_error_return, rule proc)
next
  case (12 i dpp mode u_info P' R' prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain
    dpp' where proc: "uncurry_proc_both I mode u_info P' R'  dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case      
    by (rule sound_proc_impl[OF uncurry_proc_both[OF I], OF proc IH(1)],
      unfold update_error_return, rule proc, rule rec, rule fin)
next
  case (13 i dpp graphs)
  note IH = this
  from IH(1) have proc: "isOK (sct_subterm_proc I graphs dpp)" by auto
  show ?case 
    by (rule sct_subterm_proc_sound[OF \<open>dpp_spec I\<close> proc])
next
  case (14 i dpp rp u_opt graphs)
  note IH = this
  interpret dpp_spec I by fact
  from IH(1) have proc: "isOK (sct_ur_af_proc I (get_rel_impl rp) graphs u_opt dpp)" by auto
  show ?case
    by (rule sct_ur_af_proc[OF I get_rel_impl, OF proc])
next
  case (15 i dpp f fcs Pb' R' prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "fcc_proc I f fcs Pb' R' dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)" by auto
  from IH have fin: "?P prof" by simp
  from IH(1)[OF _ rec fin, simplified, OF proc] have "finite_dpp (dpp_ops.dpp I dpp')"
    by simp
  from sound_proc_impl[OF fcc_proc, OF proc this] show ?case .
next
  case (16 i dpp P' R' prof1 prof2)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i"
  let ?i1 = "?i 1"
  let ?i11 = "add_index (?i 1) 1"
  let ?i2 = "?i 2"
  note res = IH(5)[unfolded check_dp_termination_proof.simps debug.simps]
  note ass = IH(6)[unfolded dp_assms.simps]
  show ?case
  proof (cases "get_fcc_option prof1")
    case None
    obtain dpp1 dpp2 where s: "split_proc I dpp P' R' = (dpp1, dpp2)" by force
    note ss = s[symmetric]
    note res = res[unfolded None s option.simps Let_def split]
    from res have ok1: "isOK (check_dp_termination_proof ?i1 dpp1 prof1)"
    and ok2: "isOK (check_dp_termination_proof ?i2 dpp2 prof2)" by auto
    from ass have fin1: "?P prof1" and fin2: "?P prof2" by simp_all
    from IH(1)[OF None ss refl ok1 fin1]
    have fin1': "finite_dpp (dpp_ops.dpp I dpp1)" .
    from IH(2)[OF None ss refl _ ok2 fin2] ok1
    have fin2': "finite_dpp (dpp_ops.dpp I dpp2)" by auto
    show ?thesis
      by (rule split_proc[OF s fin1' fin2'])
  next
    case (Some fcco)
    from Some obtain f fcs Pb' Rb' prf1a where prof1: "prof1 = Fcc_Proc f fcs Pb' Rb' prf1a" by (cases prof1, force+)
    then have fcco: "get_fcc_option prof1 = Some (f,fcs,Pb',Rb',prf1a)" by simp
    note res = res[unfolded option.simps fcco Let_def split]
    let ?call = "fcc_split_proc I f fcs Pb' Rb' P' R' dpp"
    from res obtain dpp1 dpp2 where proc: "?call = Inr (dpp1,dpp2)" 
      by (cases ?call, auto)
    note res = res[unfolded proc, simplified]
    from res have ok1: "isOK (check_dp_termination_proof ?i11 dpp1 prf1a)"
      and ok2: "isOK (check_dp_termination_proof ?i2 dpp2 prof2)" by auto
    from ass have fin1: "?P prf1a" and fin2: "?P prof2" 
      unfolding prof1 by simp_all
    from IH(3)[OF fcco refl refl refl refl proc refl ok1 fin1]
    have fin1': "finite_dpp (dpp_ops.dpp I dpp1)" .
    from IH(4)[OF fcco refl refl refl refl proc refl _ ok2 fin2] ok1
    have fin2': "finite_dpp (dpp_ops.dpp I dpp2)" by auto
    show ?thesis
      by (rule fcc_split_proc[OF I proc fin1' fin2'])
  qed
next
  case (17 i dpp sli lP lQ lR prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "semlab_fin_proc I sli lP lQ lR dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case
    by (rule sound_proc_impl[OF semlab_fin_proc[OF I], OF proc IH(1)],
      unfold update_error_return, rule proc, rule rec, rule fin)
next
  case (18 i dpp joins prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "switch_innermost_proc string_rename I joins dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case    
    by (rule sound_proc_impl[OF switch_innermost_proc[OF I] _ IH(1)], rule proc, unfold update_error_return, rule proc, rule rec, rule fin)
next
  case (19 i dpp dpp' ass)
  note IH = this
  interpret dpp_spec I by fact
  interpret J: tp_spec J by fact
  show ?case
  proof (cases assms)
    assume not: "\<not> assms"
    show ?thesis
      using \<open>isOK (check_dp_termination_proof i dpp (Assume_Finite dpp' ass))\<close>
      by (simp, insert not, auto)
  next
    assume "assms"
    have ok: "isOK (check_dp_termination_proof i dpp (Assume_Finite dpp' ass))" by fact
    then have subsumes: "isOK (check_dpp_subsumes I dpp' dpp)" by simp
    have "(try check_dpp_subsumes I dpp' dpp catch (\<lambda>x. Inl (i \<circ>
      showsl_lit (STR '': error in finiteness assumption or unknown proof\<newline>'') \<circ> x \<circ>
      showsl_nl))) = Inr ()" using subsumes by auto
    note IH' = IH(1-4) [OF \<open>assms\<close> this]
    from IH(6) \<open>assms\<close> have "holds (Finite_assm (map assm_proof_to_problem ass) dpp')" by auto
    from this have *: "(\<And> x. x \<in> set ass \<Longrightarrow> satisfied (assm_proof_to_problem x)) \<Longrightarrow> finite_dpp (mk_dpp_set dpp')"
      by auto
    show ?thesis
    proof (rule check_dpp_subsumes_sound [OF I subsumes *])
      fix as
      assume as: "as \<in> set ass"
      then obtain j where asj: "as = ass ! j" and j: "j < length ass" unfolding set_conv_nth by auto
      note IH' = IH'[OF as]
      from IH(5)[simplified] asj j have ok: 
         "isOK (check_assm 
           (check_trs_termination_proof (add_index i (Suc j)))
           (check_dp_termination_proof (add_index i (Suc j))) 
           (check_fptrs_termination_proof (add_index i (Suc j)))
           (check_unknown_proof (add_index i (Suc j))) 
           as)" by auto
      from IH(6) \<open>assms\<close> as have ass: "\<forall>x\<in>set (collect_assms (sn_assms assms) (dp_assms assms) (sn_fp_assms assms) (unknown_assms assms) as). holds x" 
        by simp
      show "satisfied (assm_proof_to_problem as)"
      proof (rule check_assm[OF _ _ _ _ ok])
        fix d p
        show "as = Finite_assm_proof d p \<Longrightarrow>
           isOK (check_dp_termination_proof (add_index i (Suc j)) (mk_dpp I d) p) \<Longrightarrow>
           finite_dpp (mk_dpp_set d)"
          by (rule IH'(2)[folded mk_dpp_set, of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = SN_assm_proof t p \<Longrightarrow>
           isOK (check_trs_termination_proof (add_index i (Suc j)) (mk_tp J t) p) \<Longrightarrow>
           SN_qrel (mk_tp_set t)"
          by (rule IH'(1)[folded J.mk_tp_set, of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = SN_FP_assm_proof t p \<Longrightarrow>
           isOK (check_fptrs_termination_proof (add_index i (Suc j)) t p) \<Longrightarrow>
           SN_fpstep (mk_fptp_set t)"
          by (rule IH'(3)[of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = Unknown_assm_proof t p \<Longrightarrow>
           isOK (check_unknown_proof (add_index i (Suc j)) t p) \<Longrightarrow>
           unknown_satisfied t"
          by (rule IH'(4)[of _ p j], insert ass, auto simp: o_def)
      qed
    qed
  qed
next
  case (20 i dpp U st st' st'' lr p prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "rewriting_proc I U st st' st'' lr p dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case    
    by (rule sound_proc_impl[OF rewriting_proc[OF I] _ IH(1)], rule proc, unfold update_error_return, rule proc, rule rec, rule fin)  
next
  case (21 i dpp st p sts prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "narrowing_proc I st p sts dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case    
    by (rule sound_proc_impl[OF narrowing_proc[OF I] _ IH(1)], 
      rule proc, unfold update_error_return, rule proc, rule rec, rule fin)  
next
  case (22 i dpp st sts prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "instantiation_proc I st sts dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case    
    by (rule sound_proc_impl[OF instantiation_proc[OF I] _ IH(1)], rule proc, 
      unfold update_error_return, rule proc, rule rec, rule fin)  
next
  case (23 i dpp st sts u_opt prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "forward_instantiation_proc I st sts u_opt dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)"
    by (auto simp: Let_def)
  from IH have fin: "?P prof" by simp
  show ?case    
    by (rule sound_proc_impl[OF forward_instantiation_proc[OF I] _ IH(1)], rule proc, unfold update_error_return, 
      rule proc, rule rec, rule fin)
next
  case (24 i dpp rp Ps Pb prof prfs)
  note IH = this
  interpret dpp_spec I by fact
  let ?i1 = "add_index i 1"
  let ?i2 = "add_index i 2"
  note prems = IH(3)[simplified, unfolded Let_def check_def, simplified]
  from prems obtain dpps
    where proc: "conditional_general_reduction_pair_proc I (get_non_inf_order rp) Ps Pb prof (length prfs = 1) dpp = return dpps"
      and len: "length prfs \<noteq> 0"
    by auto
  from len obtain p1 ps where prfs: "prfs = p1 # ps" by (cases prfs, auto)
  from conditional_general_reduction_pair_proc_len[OF proc] have len: "length dpps = (if length prfs = 1 then 1 else 2)" .
  from len obtain d1 ds where dpps: "dpps = d1 # ds" by (cases dpps, cases "length prfs = 1", auto)
  from prems proc prfs dpps have ok1: "isOK(check_dp_termination_proof ?i1 (dpps ! 0) (prfs ! 0))" by simp
  note IH1 = IH(1)[OF refl _ refl _ ok1, unfolded proc prfs]
  from IH(4)[unfolded prfs] have ass1: "?P p1" by auto
  show ?case
  proof (rule conditional_general_reduction_pair_proc[OF I get_non_inf_order proc])
    fix d
    assume d: "d \<in> set dpps"
    show "finite_dpp (dpp_ops.dpp I d)"
    proof (cases "d = d1")
      case True
      then have d: "d = (dpps ! 0)" unfolding dpps by simp
      show ?thesis unfolding d
        by (rule IH1, insert proc ass1 prfs, auto simp: check_def)
    next
      case False
      with d dpps have d: "d \<in> set ds" by auto
      with len dpps prfs have dpps: "dpps = [d1,d]" by (cases ps, auto, cases ds, auto)
      with len obtain p2 pps where prfs: "prfs = p1 # p2 # pps" unfolding prfs dpps by (cases ps, auto)
      from dpps have d: "d = dpps ! 1" by simp
      from prems proc prfs dpps have ok2: "isOK(check_dp_termination_proof ?i2 (dpps ! 1) (prfs ! 1))" by auto
      from IH(4)[unfolded prfs] have ass2: "?P p2" by auto
      show ?thesis unfolding d
        by (rule IH(2)[OF refl _ refl _ _ _ ok2], insert proc prfs ok1 ass2 dpps, auto simp: check_def)
    qed
  qed
next
  case (25 i dpp cprf prof)
  note IH = this
  interpret dpp_spec I by fact
  let ?i = "add_index i 1"
  from IH(2) obtain dpp'
    where proc: "complex_constant_removal_proc string_rename I cprf dpp = return dpp'"
    and rec: "isOK (check_dp_termination_proof ?i dpp' prof)" by auto
  from IH have fin: "?P prof" by simp
  from IH(1)[OF _ rec fin, simplified, OF proc] have "finite_dpp (dpp_ops.dpp I dpp')"
    by simp
  from sound_proc_impl[OF complex_constant_removal_proc[OF I] proc this] show ?case .
next
  case (26 i dpp prof)
  note IH = this
  interpret tp_spec J by fact
  interpret I: dpp_spec I by fact
  from IH(2) have ok: "isOK (check_trs_termination_proof (add_index i 1)
         (mk_tp J
           (dpp_ops.nfs I dpp, dpp_ops.Q I dpp, dpp_ops.P I dpp @ dpp_ops.R I dpp, dpp_ops.Pw I dpp @ dpp_ops.Rw I dpp))
         prof)" by auto
  from IH(3) have "?Q prof" by simp
  from IH(1)[OF ok this, unfolded SN_qrel_def]
  have "SN_rel (qrstep (dpp_ops.nfs I dpp) (set (dpp_ops.Q I dpp)) (set (dpp_ops.P I dpp) \<union> set (dpp_ops.R I dpp)))
     (qrstep (dpp_ops.nfs I dpp) (set (dpp_ops.Q I dpp)) (set (dpp_ops.Pw I dpp) \<union> set (dpp_ops.Rw I dpp)))"
     by simp
  from SN_rel_imp_finite_dpp[OF this]
  show ?case unfolding I.dpp_sound .
next
  case (27 i tp)
  note IH = this
  interpret tp_spec J by fact
  from IH show ?case by (simp add: SN_qrel_def SN_rel_on_def)
next
  case (28 i tp rp Rr prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  from IH(2) obtain tp' where
    tt: "rule_removal_tt J (get_rel_impl rp) Rr tp = return tp'"
    and rec: "isOK (check_trs_termination_proof ?i tp' prof)" by (auto simp: Let_def)
  from IH(3) have fin: "?Q prof" by simp
  show ?case
    apply (rule sound_tt_impl [OF rule_removal_tt [OF get_rel_impl], OF tt])
    apply (rule IH(1) [OF _ rec fin])
    apply (unfold update_error_return)
    apply (rule tt)
  done
next
  case (29 i tp nfs m P prof)
  note IH = this
  let ?i = "add_index i 1"
  from IH obtain dpp where
      tt: "dependency_pairs_tt Sharp J I tp nfs m P = return dpp" 
      and rec: "isOK (check_dp_termination_proof ?i dpp prof)" by auto
  from IH have fin: "?P prof" by simp
  show ?case
    apply (rule dependency_pairs_tt [OF J I tt])
    apply (rule IH(1)[OF _ rec fin])
    apply (unfold update_error_return)
    apply (rule tt)
  done
next
  case (30 i tp prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  from IH(2) obtain tp' where tt: "string_reversal_tt J tp = return tp'"
      and rec: "isOK (check_trs_termination_proof ?i tp' prof)"
      by (auto simp: Let_def)
  from IH(3) have fin: "?Q prof" by simp
  show ?case
    apply (rule sound_tt_impl [OF string_reversal_tt tt])
    apply (rule IH(1) [OF _ rec fin])
    apply (unfold update_error_return)
    apply (rule tt)
  done
next
  case (31 i tp p prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  from IH(2) obtain tp' where tt: "const_to_string_sound_tt p J tp = return tp'"
      and rec: "isOK (check_trs_termination_proof ?i tp' prof)"
      by (auto simp: Let_def)
  from IH(3) have fin: "?Q prof" by simp
  show ?case
    apply (rule sound_tt_impl [OF const_to_string_sound_tt tt])
    apply (rule IH(1) [OF _ rec fin])
    apply (unfold update_error_return)
    apply (rule tt)
  done
next
  case (32 i tp sli lQ lAll prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  from IH obtain tp' where
    tt: "semlab_fin_tt J sli lQ lAll tp = return tp'"
    and rec: "isOK (check_trs_termination_proof ?i tp' prof)"
      by (auto simp: Let_def)
   from IH(3) have fin: "?Q prof" by simp
   show ?case
     apply (rule sound_tt_impl)
     apply (rule semlab_fin_tt)
     apply fact
     apply (rule tt)
     apply (rule IH(1) [OF _ rec fin])
     apply (unfold update_error_return)
     apply (rule tt)
   done
next
  case (33 i tp info)
  then have tt: "isOK (bounds_tt J info tp)"
    by (auto simp: Let_def)
  show ?case
    by (rule bounds_tt [OF J tt infinite_lab])
next
  case (34 i tp mode info prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  from IH(2) obtain tp' where
    tt: "uncurry_tt J mode info tp = return tp'"
    and rec: "isOK (check_trs_termination_proof ?i tp' prof)"
    by (auto simp: Let_def)
  from IH(3) have fin: "?Q prof" by simp
  show ?case
    apply (rule sound_tt_impl)
    apply (rule uncurry_tt)
    apply (fact)
    apply (rule tt)
    apply (rule IH(1) [OF _ rec fin])
    apply (unfold update_error_return)
    apply (rule tt)
  done
next
  case (35 i tp fcs R' prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  from IH(2) obtain tp' where tt: "fcc_tt J fcs R' tp = return tp'"
      and rec: "isOK (check_trs_termination_proof ?i tp' prof)" by auto
  from IH(3) have fin: "?Q prof" by simp
  show ?case
    apply (rule sound_tt_impl)
    apply (rule fcc_tt)
    apply (rule tt)
    apply (rule IH(1) [OF _ rec fin])
    apply (unfold update_error_return)
    apply (rule tt)
  done
next
  case (36 i tp R' prof1 prof2)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i"
  let ?i1 = "?i 1"
  let ?i2 = "?i 2"
  obtain tp1 tp2 where s: "split_tt J tp R' = (tp1, tp2)" by force
  from IH(3) s have ok1: "isOK (check_trs_termination_proof ?i1 tp1 prof1)" 
      and ok2: "isOK (check_trs_termination_proof ?i2 tp2 prof2)" by auto
  from IH(4) have fin1: "?Q prof1" and fin2: "?Q prof2" by simp_all
  show ?case
    apply (rule split_tt)
    apply (rule s)
    apply (rule IH(1) [OF _ refl ok1 fin1])
    apply (rule s [symmetric])
    apply (rule IH(2) [OF _ refl _ ok2 fin2])
    apply (rule s [symmetric])
    apply (unfold update_error_return)
    using ok1
    apply auto
  done
next
  case (37 i tp joins prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  from IH(2) obtain tp' where
    tt: "switch_innermost_tt string_rename J joins tp = return tp'"
    and rec: "isOK (check_trs_termination_proof ?i tp' prof)"
    by (auto simp: Let_def)
  from IH(3) have fin: "?Q prof" by simp
  show ?case
    apply (rule sound_tt_impl)
    apply (rule switch_innermost_tt [OF J])
    apply (rule infinite_lab)
    apply (rule tt)
    apply (rule IH(1) [OF _ rec fin])
    apply (unfold update_error_return)
    apply (rule tt)
  done
next
  case (38 i tp prof)
  note IH = this
  interpret tp_spec J by fact
  let ?Rw = "filter (\<lambda> (l,r). l \<noteq> r) (Rw tp)"
  let ?Rw' = "filter (\<lambda> (l,r). l = r) (Rw tp)"
  let ?nfs = "NFS tp"
  let ?tp = "mk ?nfs (Q tp) (R tp) ?Rw"
  let ?i = "add_index i 1"
  from IH(3) have fin: "?Q prof" by simp
  from IH(2) have ok: "isOK (check_trs_termination_proof ?i ?tp prof)" by auto
  have SN: "SN_qrel (qreltrs ?tp)"
    apply (rule IH(1) [OF _ ok fin])
    apply simp_all
  done
  let ?Q = "qrstep ?nfs (set (Q tp))"
  let ?QR = "?Q (set (R tp))"
  let ?QRw = "?Q (set (Rw tp))"
  let ?QRw' = "?Q (set ?Rw)"
  note d = qreltrs_sound SN_qrel_def mk_simps split
  from SN [unfolded d] have "SN_rel ?QR ?QRw'" .
  then have SN: "SN_rel ?QR (?QRw'^=)" unfolding SN_rel_Id . 
  have id: "set (Rw tp) = set ?Rw \<union> set ?Rw'" by auto
  show "SN_qrel (qreltrs tp)" unfolding d
  proof (rule SN_rel_mono [OF subset_refl _ SN], unfold id qrstep_union, rule Un_mono [OF subset_refl])
    have "?Q (set ?Rw') \<subseteq> ?Q Id" by (rule qrstep_mono, auto) 
    also have "... \<subseteq> Id" by (rule qrstep_Id)
    finally show "?Q (set ?Rw') \<subseteq> Id" .
  qed
next
  case (39 i tp Rdelete prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  let ?R = "delete_rules tp Rdelete"
  from IH(2) have ok: "isOK (check_non_applicable_rules (\<lambda>t. t \<in> NF_terms (set (Q tp))) Rdelete)"
    and rec: "isOK (check_trs_termination_proof ?i ?R prof)" by auto
  from IH(3) have fin: "?Q prof" by simp
  from check_non_applicable_rules [OF refl ok]
    have id: "\<And>R. qrstep (NFS tp) (set (Q tp)) (R - set Rdelete) = qrstep (NFS tp) (set (Q tp)) R" .
  have "SN_qrel (tp_ops.qreltrs J
   (tp_ops.delete_R_Rw J tp Rdelete
     Rdelete))"
    apply (rule IH(1) [OF _ _ refl rec fin])
    using ok by auto
  then show ?case
    by (simp add: id SN_qrel_def)
next
  case (40 i tp pi prof)
  note IH = this
  interpret tp_spec J by fact
  let ?i = "add_index i 1"
  from IH(2) obtain tp' where
    tt: "argument_filter_tt J pi tp = return tp'"
    and rec: "isOK (check_trs_termination_proof ?i tp' prof)"
    by (auto simp: Let_def)
  from IH(3) have fin: "?Q prof" by simp
  show ?case
    by (rule sound_tt_impl[OF argument_filter_tt[OF J] tt IH(1)[OF _ rec fin]], insert tt, auto)
next
  case (41 i tp)
  then have tt: "isOK (right_ground_tt J tp)"
    by (auto simp: Let_def)
  interpret tp_spec J by fact
  show ?case by (rule right_ground_tt [OF tt])
next
  case (42 i tp tp' ass)
  note IH = this
  interpret J: tp_spec J by fact
  interpret dpp_spec I by fact
  show ?case
  proof (cases assms)
    assume False: "\<not> assms"
    show ?thesis using IH(5) by (simp, insert False, auto)
  next
    assume "assms"
    have ok: "isOK (check_trs_termination_proof i tp (Assume_SN tp' ass))" by fact
    then have subsumes: "isOK (check_tp_subsumes J tp' tp)" by simp
    have "(try check_tp_subsumes J tp' tp catch (\<lambda>x. Inl (i \<circ>
      showsl_lit (STR '': error in termination assumption or unknown proof\<newline>'') \<circ> x \<circ>
      showsl_nl))) = Inr ()" using subsumes by auto
    note IH' = IH(1-4)[OF \<open>assms\<close> this]
    from IH(6) \<open>assms\<close> have "holds (SN_assm (map assm_proof_to_problem ass) tp')" by auto
    from this have *: "(\<And> x. x \<in> set ass \<Longrightarrow> satisfied (assm_proof_to_problem x)) \<Longrightarrow> SN_qrel (mk_tp_set tp')"
      by auto
    show ?thesis
    proof (rule check_tp_subsumes_sound [OF J subsumes *])
      fix as
      assume as: "as \<in> set ass"
      then obtain j where asj: "as = ass ! j" and j: "j < length ass" unfolding set_conv_nth by auto
      note IH' = IH'[OF as]
      from IH(5)[simplified] asj j have ok: 
         "isOK (check_assm 
           (check_trs_termination_proof (add_index i (Suc j)))
           (check_dp_termination_proof (add_index i (Suc j))) 
           (check_fptrs_termination_proof (add_index i (Suc j)))
           (check_unknown_proof (add_index i (Suc j)))
           as)" by auto
      from IH(6) \<open>assms\<close> as have ass: "\<forall>x\<in>set (collect_assms (sn_assms assms) (dp_assms assms) (sn_fp_assms assms) (unknown_assms assms) as). holds x" 
        by simp
      show "satisfied (assm_proof_to_problem as)"
      proof (rule check_assm[OF _ _ _ _ ok])
        fix d p
        show "as = Finite_assm_proof d p \<Longrightarrow>
           isOK (check_dp_termination_proof (add_index i (Suc j)) (mk_dpp I d) p) \<Longrightarrow>
           finite_dpp (mk_dpp_set d)"
          by (rule IH'(2)[folded mk_dpp_set, of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = SN_assm_proof t p \<Longrightarrow>
           isOK (check_trs_termination_proof (add_index i (Suc j)) (mk_tp J t) p) \<Longrightarrow>
           SN_qrel (mk_tp_set t)"
          by (rule IH'(1)[folded J.mk_tp_set, of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = SN_FP_assm_proof t p \<Longrightarrow>
           isOK (check_fptrs_termination_proof (add_index i (Suc j)) t p) \<Longrightarrow>
           SN_fpstep (mk_fptp_set t)"
          by (rule IH'(3)[of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = Unknown_assm_proof t p \<Longrightarrow>
           isOK (check_unknown_proof (add_index i (Suc j)) t p) \<Longrightarrow>
           unknown_satisfied t"
          by (rule IH'(4)[of _ p j], insert ass, auto simp: o_def)
      qed
    qed
  qed
next
  case (43 i tp tp' ass)
  note IH = this
  interpret J: tp_spec J by fact
  interpret dpp_spec I by fact
  show ?case
  proof (cases assms)
    assume False: "\<not> assms"
    show ?thesis using IH(5) by (simp, insert False, auto)
  next
    assume "assms"
    have ok: "isOK (check_fptrs_termination_proof i tp (Assume_FP_SN tp' ass))" by fact
    then have subsumes: "tp = tp'" by simp
    have "check (tp = tp') (showsl_lit (STR ''outermost assumption does not match current goal'')) = Inr ()" using subsumes 
      by (auto simp: check_def)
    note IH' = IH(1-4)[OF \<open>assms\<close> this]
    from IH(6) \<open>assms\<close> have "holds (SN_FP_assm (map assm_proof_to_problem ass) tp')" by auto
    from this have *: "(\<And> x. x \<in> set ass \<Longrightarrow> satisfied (assm_proof_to_problem x)) \<Longrightarrow> SN_fpstep (mk_fptp_set tp')"
      by auto
    show ?thesis unfolding subsumes
    proof (rule *)
      fix as
      assume as: "as \<in> set ass"
      then obtain j where asj: "as = ass ! j" and j: "j < length ass" unfolding set_conv_nth by auto
      note IH' = IH'[OF as]
      from IH(5)[simplified] asj j have ok: 
         "isOK (check_assm 
           (check_trs_termination_proof (add_index i (Suc j)))
           (check_dp_termination_proof (add_index i (Suc j))) 
           (check_fptrs_termination_proof (add_index i (Suc j)))
           (check_unknown_proof (add_index i (Suc j))) 
           as)" by auto
      from IH(6) \<open>assms\<close> as have ass: "\<forall>x\<in>set (collect_assms (sn_assms assms) (dp_assms assms) (sn_fp_assms assms) (unknown_assms assms) as). holds x" 
        by simp
      show "satisfied (assm_proof_to_problem as)"
      proof (rule check_assm[OF _ _ _ _ ok])
        fix d p
        show "as = Finite_assm_proof d p \<Longrightarrow>
           isOK (check_dp_termination_proof (add_index i (Suc j)) (mk_dpp I d) p) \<Longrightarrow>
           finite_dpp (mk_dpp_set d)"
          by (rule IH'(2)[folded mk_dpp_set, of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = SN_assm_proof t p \<Longrightarrow>
           isOK (check_trs_termination_proof (add_index i (Suc j)) (mk_tp J t) p) \<Longrightarrow>
           SN_qrel (mk_tp_set t)"
          by (rule IH'(1)[folded J.mk_tp_set, of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = SN_FP_assm_proof t p \<Longrightarrow>
           isOK (check_fptrs_termination_proof (add_index i (Suc j)) t p) \<Longrightarrow>
           SN_fpstep (mk_fptp_set t)"
          by (rule IH'(3)[of _ p j], insert ass, auto simp: o_def)
      next
        fix t p
        show "as = Unknown_assm_proof t p \<Longrightarrow>
           isOK (check_unknown_proof (add_index i (Suc j)) t p) \<Longrightarrow>
           unknown_satisfied t"
          by (rule IH'(4)[of _ p j], insert ass, auto simp: o_def)
      qed
    qed
  qed
next
  case (44 i tp tp' ass)
  note IH = this
  interpret J: tp_spec J by fact
  interpret dpp_spec I by fact
  show ?case
  proof (cases assms)
    assume "\<not> assms"
    show ?thesis using IH(5) by (simp, insert \<open>\<not> assms\<close>, auto)
  next
    assume assms
    have ok: "isOK (check_unknown_proof i tp (Assume_Unknown tp' ass))" by fact
    then have tp: "tp = tp'" by auto
    note IH' = IH(1-4)[OF \<open>assms\<close>, unfolded tp]
    from IH(6) \<open>assms\<close> have "holds (Unknown_assm (map assm_proof_to_problem ass) tp')" by auto
    from this have *: "(\<And> x. x \<in> set ass \<Longrightarrow> satisfied (assm_proof_to_problem x)) \<Longrightarrow> unknown_satisfied tp'"
      by auto
    show ?thesis unfolding tp
    proof (rule *)
      fix as
      assume as: "as \<in> set ass"
      then obtain j where asj: "as = ass ! j" and j: "j < length ass" unfolding set_conv_nth by auto
      note IH' = IH'[OF _ as]
      from IH(5)[simplified] asj j have ok: 
         "isOK (check_assm 
           (check_trs_termination_proof (add_index i (Suc j)))
           (check_dp_termination_proof (add_index i (Suc j))) 
           (check_fptrs_termination_proof (add_index i (Suc j)))
           (check_unknown_proof (add_index i (Suc j))) 
           as)" by auto
      from IH(6) \<open>assms\<close> as have ass: "\<forall>x\<in>set (collect_assms (sn_assms assms) (dp_assms assms) (sn_fp_assms assms) (unknown_assms assms) as). holds x" 
        by simp
      show "satisfied (assm_proof_to_problem as)"
      proof (rule check_assm[OF _ _ _ _ ok])
        fix d p
        show "as = Finite_assm_proof d p \<Longrightarrow>
           isOK (check_dp_termination_proof (add_index i (Suc j)) (mk_dpp I d) p) \<Longrightarrow>
           finite_dpp (mk_dpp_set d)"
          by (rule IH'(2)[folded mk_dpp_set, of _ _ p j], insert ass, auto simp: o_def check_def)
      next
        fix t p
        show "as = SN_assm_proof t p \<Longrightarrow>
           isOK (check_trs_termination_proof (add_index i (Suc j)) (mk_tp J t) p) \<Longrightarrow>
           SN_qrel (mk_tp_set t)"
          by (rule IH'(1)[folded J.mk_tp_set, of _ _ p j], insert ass, auto simp: o_def check_def)
      next
        fix t p
        show "as = SN_FP_assm_proof t p \<Longrightarrow>
           isOK (check_fptrs_termination_proof (add_index i (Suc j)) t p) \<Longrightarrow>
           SN_fpstep (mk_fptp_set t)"
          by (rule IH'(3)[of _ _ p j], insert ass, auto simp: o_def check_def)
      next
        fix t p
        show "as = Unknown_assm_proof t p \<Longrightarrow>
           isOK (check_unknown_proof (add_index i (Suc j)) t p) \<Longrightarrow>
           unknown_satisfied t"
          by (rule IH'(4)[of _ _ p j], insert ass, auto simp: o_def check_def)
      qed
    qed
  qed
qed

end

lemma check_dp_termination_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_dp_termination_proof I J a i dpp prf)"
    and ass: "\<forall>assm\<in>set (dp_assms a prf). holds assm"
  shows "finite_dpp (dpp_ops.dpp J dpp)"
  by (rule check_dp_trs_unknown_termination_proof_with_assms(1)[OF J I ok ass])

lemma check_dp_termination_proof:
  assumes "tp_spec I" and "dpp_spec J"
    and "isOK (check_dp_termination_proof I J False i dpp prf)"
  shows "finite_dpp (dpp_ops.dpp J dpp)"
  using check_dp_termination_proof_with_assms[OF assms] by simp

lemma check_trs_termination_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_trs_termination_proof I J a i tp prf)"
    and ass: "\<forall>assm\<in>set (sn_assms a prf). holds assm"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
  by (rule check_dp_trs_unknown_termination_proof_with_assms(2)[OF J I ok ass])

lemma check_trs_termination_proof:
  assumes "tp_spec I" and "dpp_spec J"
    and "isOK (check_trs_termination_proof I J False i tp prf)"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
  using check_trs_termination_proof_with_assms[OF assms] by simp

lemma check_fptrs_termination_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_fptrs_termination_proof I J a i tp prf)"
    and ass: "\<forall>assm\<in>set (sn_fp_assms a prf). holds assm"
  shows "SN_fpstep (mk_fptp_set tp)"
  by (rule check_dp_trs_unknown_termination_proof_with_assms(3)[OF J I ok ass])

lemma check_fptrs_termination_proof:
  assumes "tp_spec I" and "dpp_spec J"
    and "isOK (check_fptrs_termination_proof I J False i tp prf)"
  shows "SN_fpstep (mk_fptp_set tp)"
  using check_fptrs_termination_proof_with_assms[OF assms] by simp

lemma check_unknown_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_unknown_proof I J a i u prf)"
    and ass: "\<forall>assm\<in>set (unknown_assms a prf). holds assm"
  shows "unknown_satisfied u"
  by (rule check_dp_trs_unknown_termination_proof_with_assms(4)[OF J I ok],
    insert ass, auto)

lemma check_unknown_proof:
  assumes "tp_spec I" and "dpp_spec J"
    and "isOK (check_unknown_proof I J False i u prf)"
  shows "unknown_satisfied u"
  using check_unknown_proof_with_assms[OF assms] by simp

end
