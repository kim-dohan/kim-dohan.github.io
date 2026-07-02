(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Nontermination
imports
  Check_Termination_Common
begin

datatype (dead 'f, dead 'l, dead 'v) dp_nontermination_proof =
  DP_Loop "(('f,'l)lab, 'v)dp_loop_prf"
| DP_Nonloop "(('f,'l)lab, 'v)non_loop_prf"
| DP_Rule_Removal "(('f,'l)lab,'v)rule_removal_nonterm_dp_prf" "('f,'l,'v) dp_nontermination_proof"
| DP_Q_Increase "(('f,'l)lab,'v)q_increase_nonterm_dp_prf" "('f,'l,'v) dp_nontermination_proof"
| DP_Q_Reduction "(('f,'l)lab,'v)dp_q_reduction_nonterm_prf" "('f,'l,'v) dp_nontermination_proof"
| DP_Termination_Switch "(('f,'l)lab,'v) join_info" "('f,'l,'v) dp_nontermination_proof"
| DP_Instantiation "(('f,'l)lab,'v)instantiation_complete_proc_prf" "('f,'l,'v) dp_nontermination_proof"
| DP_Rewriting "(('f,'l)lab,'v)rewriting_complete_proc_prf" "('f,'l,'v) dp_nontermination_proof"
| DP_Narrowing "(('f,'l)lab,'v)narrowing_complete_proc_prf" "('f,'l,'v) dp_nontermination_proof"
| DP_Assume_Infinite  "('f, 'l, 'v) dppLL"
    "('f,'l,'v,('f, 'l, 'v) trs_nontermination_proof,
     ('f, 'l, 'v) dp_nontermination_proof,
     ('f, 'l, 'v) reltrs_nontermination_proof,
     ('f, 'l, 'v) fp_trs_nontermination_proof,
     ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"
 and
('f,'l,'v) "trs_nontermination_proof" =
  TRS_Loop "(('f,'l)lab,'v)trs_loop_prf"
| TRS_Not_Well_Formed
| TRS_Rule_Removal "(('f,'l)lab,'v)rule_removal_nonterm_trs_prf" "('f,'l,'v) trs_nontermination_proof"
| TRS_String_Reversal "('f,'l,'v) trs_nontermination_proof"
| TRS_Constant_String "(('f,'l)lab,'v)const_string_complete_proof" "('f,'l,'v) trs_nontermination_proof"
| TRS_DP_Trans "('f,'l,'v)dp_trans_nontermination_tt_prf" "('f,'l,'v) dp_nontermination_proof"
| TRS_Termination_Switch "(('f,'l)lab,'v) join_info" "('f,'l,'v) trs_nontermination_proof"
| TRS_Nonloop "(('f,'l)lab,'v) non_loop_prf"
| TRS_Nonloop_SRS "('f,'l)lab  non_loop_srs_proof"
| TRS_Q_Increase "(('f,'l)lab,'v)q_increase_nonterm_trs_prf" "('f,'l,'v) trs_nontermination_proof"
| TRS_Uncurry "('f, 'l , 'v)uncurry_nt_proof" "('f, 'l, 'v) trs_nontermination_proof"
| TRS_Not_WN_Tree_Automaton "(('f,'l)lab,'v) not_wn_ta_prf"
| TRS_Not_RG_Decision
| TRS_Assume_Not_SN  "('f, 'l, 'v)qtrsLL"
    "('f,'l,'v,('f, 'l, 'v) trs_nontermination_proof,
     ('f, 'l, 'v) dp_nontermination_proof,
     ('f, 'l, 'v) reltrs_nontermination_proof,
     ('f, 'l, 'v) fp_trs_nontermination_proof,
     ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"
 and
('f,'l,'v)"reltrs_nontermination_proof" =
  Rel_Loop "(('f,'l)lab,'v)rel_trs_loop_prf"
| Rel_TRS_String_Reversal "('f,'l,'v)reltrs_nontermination_proof"
| Rel_Not_Well_Formed
| Rel_Rule_Removal "(('f,'l)lab,'v)rule_removal_nonterm_reltrs_prf" "('f,'l,'v) reltrs_nontermination_proof"
| Rel_R_Not_SN "('f,'l,'v) trs_nontermination_proof"
| Rel_TRS_Assume_Not_SN  "('f, 'l, 'v)qreltrsLL"
    "('f,'l,'v,('f, 'l, 'v) trs_nontermination_proof,
     ('f, 'l, 'v) dp_nontermination_proof,
     ('f, 'l, 'v) reltrs_nontermination_proof,
     ('f, 'l, 'v) fp_trs_nontermination_proof,
     ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"
 and
('f,'l,'v) "fp_trs_nontermination_proof" =
  FP_TRS_Loop "(('f,'l)lab,'v)trs_loop_prf"
| FP_TRS_Rule_Removal "(('f,'l)lab,'v)rule_removal_nonterm_trs_prf" "('f,'l,'v) fp_trs_nontermination_proof"
| FPTRS_Assume_Not_SN  "('f, 'l, 'v)fptrsLL"
    "('f,'l,'v,('f, 'l, 'v) trs_nontermination_proof,
     ('f, 'l, 'v) dp_nontermination_proof,
     ('f, 'l, 'v) reltrs_nontermination_proof,
     ('f, 'l, 'v) fp_trs_nontermination_proof,
     ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"
 and
 ('f, 'l, 'v) neg_unknown_proof =
  Assume_NT_Unknown unknown_info
    "('f,'l,'v,('f, 'l, 'v) trs_nontermination_proof,
     ('f, 'l, 'v) dp_nontermination_proof,
     ('f, 'l, 'v) reltrs_nontermination_proof,
     ('f, 'l, 'v) fp_trs_nontermination_proof,
     ('f, 'l, 'v) neg_unknown_proof) generic_assm_proof list"

fun collect_assms :: "('tp \<Rightarrow> ('f,'l,'v) assm list)
  \<Rightarrow> ('dpp \<Rightarrow> ('f,'l,'v) assm list)
  \<Rightarrow> ('rtp \<Rightarrow> ('f,'l,'v) assm list)
  \<Rightarrow> ('fptp \<Rightarrow> ('f,'l,'v) assm list)
  \<Rightarrow> ('unk \<Rightarrow> ('f,'l,'v) assm list)
  \<Rightarrow> ('f,'l,'v,'tp,'dpp,'rtp,'fptp,'unk) generic_assm_proof \<Rightarrow> ('f,'l,'v) assm list" where
  "collect_assms tp dpp rtp fptp unk (Not_SN_assm_proof t prf) = tp prf"
| "collect_assms tp dpp rtp fptp unk (Infinite_assm_proof d prf) = dpp prf"
| "collect_assms tp dpp rtp fptp unk (Not_RelSN_assm_proof t prf) = rtp prf"
| "collect_assms tp dpp rtp fptp unk (Not_SN_FP_assm_proof t prf) = fptp prf"
| "collect_assms tp dpp rtp fptp unk (Unknown_assm_proof p prf) = unk prf"
| "collect_assms tp dpp rtp fptp unk _ = []"

lemma collect_assms_cong[fundef_cong]:
  assumes
  "\<And> t p. i = Not_SN_assm_proof t p \<Longrightarrow> tp p = tp' p"
  "\<And> t p. i = Infinite_assm_proof t p \<Longrightarrow> dpp p = dpp' p"
  "\<And> t p. i = Not_RelSN_assm_proof t p \<Longrightarrow> rtp p = rtp' p"
  "\<And> t p. i = Not_SN_FP_assm_proof t p \<Longrightarrow> fptp p = fptp' p"
  "\<And> t p. i = Unknown_assm_proof t p \<Longrightarrow> unk p = unk' p"
  shows "collect_assms tp dpp rtp fptp unk i = collect_assms tp' dpp' rtp' fptp' unk' i"
  using assms by (cases i, auto)


fun neg_dp_assms :: "bool \<Rightarrow> ('f, 'l, 'v) dp_nontermination_proof \<Rightarrow> ('f, 'l, 'v) assm list"
  and neg_sn_assms :: "bool \<Rightarrow> ('f,'l,'v) trs_nontermination_proof \<Rightarrow> ('f,'l,'v) assm list"
  and neg_rel_sn_assms :: "bool \<Rightarrow> ('f,'l,'v) reltrs_nontermination_proof \<Rightarrow> ('f,'l,'v) assm list"
  and neg_fp_assms :: "bool \<Rightarrow> ('f,'l,'v) fp_trs_nontermination_proof \<Rightarrow> ('f,'l,'v) assm list"
  and neg_unknown_assms :: "bool \<Rightarrow> ('f,'l,'v) neg_unknown_proof \<Rightarrow> ('f,'l,'v) assm list"
  where
  "neg_dp_assms a (DP_Loop _) = []"
| "neg_dp_assms a (DP_Nonloop _) = []"
| "neg_dp_assms a (DP_Rule_Removal _ p) = neg_dp_assms a p"
| "neg_dp_assms a (DP_Q_Increase _ p) = neg_dp_assms a p"
| "neg_dp_assms a (DP_Q_Reduction _ p) = neg_dp_assms a p"
| "neg_dp_assms a (DP_Termination_Switch _ p) = neg_dp_assms a p"
| "neg_dp_assms a (DP_Instantiation _ p) = neg_dp_assms a p"
| "neg_dp_assms a (DP_Rewriting _ p) = neg_dp_assms a p"
| "neg_dp_assms a (DP_Narrowing _ p) = neg_dp_assms a p"
| "neg_dp_assms a (DP_Assume_Infinite dp ps) = (if a then Infinite_assm (map assm_proof_to_problem ps) dp
    # concat (map (collect_assms
     (neg_sn_assms a)
     (neg_dp_assms a)
     (neg_rel_sn_assms a)
     (neg_fp_assms a)
     (neg_unknown_assms a)) ps)  else [])"
| "neg_sn_assms a (TRS_Loop _) = []"
| "neg_sn_assms a TRS_Not_Well_Formed = []"
| "neg_sn_assms a (TRS_Nonloop _) = []"
| "neg_sn_assms a (TRS_Nonloop_SRS _) = []"
| "neg_sn_assms a (TRS_Rule_Removal _ p) = neg_sn_assms a p"
| "neg_sn_assms a (TRS_String_Reversal p) = neg_sn_assms a p"
| "neg_sn_assms a (TRS_Constant_String _ p) = neg_sn_assms a p"
| "neg_sn_assms a (TRS_DP_Trans _ p) = neg_dp_assms a p"
| "neg_sn_assms a (TRS_Q_Increase _ p) = neg_sn_assms a p"
| "neg_sn_assms a (TRS_Termination_Switch _ p) = neg_sn_assms a p"
| "neg_sn_assms a (TRS_Uncurry _ p) = neg_sn_assms a p"
| "neg_sn_assms a (TRS_Not_WN_Tree_Automaton _) = []"
| "neg_sn_assms a TRS_Not_RG_Decision = []"
| "neg_sn_assms a (TRS_Assume_Not_SN tp ps) = (if a then Not_SN_assm (map assm_proof_to_problem ps) tp
    # concat (map (collect_assms
    (neg_sn_assms a)
    (neg_dp_assms a)
    (neg_rel_sn_assms a)
    (neg_fp_assms a)
    (neg_unknown_assms a)) ps) else [])"
| "neg_rel_sn_assms a (Rel_Loop _) = []"
| "neg_rel_sn_assms a Rel_Not_Well_Formed = []"
| "neg_rel_sn_assms a (Rel_TRS_String_Reversal p) = neg_rel_sn_assms a p"
| "neg_rel_sn_assms a (Rel_Rule_Removal _ p) = neg_rel_sn_assms a p"
| "neg_rel_sn_assms a (Rel_R_Not_SN p) = neg_sn_assms a p"
| "neg_rel_sn_assms a (Rel_TRS_Assume_Not_SN tp ps) = (if a then Not_RelSN_assm (map assm_proof_to_problem ps) tp
    # concat (map (collect_assms
    (neg_sn_assms a)
    (neg_dp_assms a)
    (neg_rel_sn_assms a)
    (neg_fp_assms a)
    (neg_unknown_assms a)) ps) else [])"
| "neg_fp_assms a (FP_TRS_Loop _) = []"
| "neg_fp_assms a (FP_TRS_Rule_Removal _ p) = neg_fp_assms a p"
| "neg_fp_assms a (FPTRS_Assume_Not_SN tp ps) = (if a then Not_SN_FP_assm (map assm_proof_to_problem ps) tp
    # concat (map (collect_assms
    (neg_sn_assms a)
    (neg_dp_assms a)
    (neg_rel_sn_assms a)
    (neg_fp_assms a)
    (neg_unknown_assms a)) ps) else [])"
| "neg_unknown_assms a (Assume_NT_Unknown t tps) = (if a then Unknown_assm (map assm_proof_to_problem tps) t
    # concat (map (collect_assms
    (neg_sn_assms a)
    (neg_dp_assms a)
    (neg_rel_sn_assms a)
    (neg_fp_assms a)
    (neg_unknown_assms a)) tps) else [])"

lemma assms_False [simp]:
  "neg_dp_assms False (p :: ('f,'l,'v)dp_nontermination_proof) = []"
  "neg_sn_assms False (q :: ('f,'l,'v)trs_nontermination_proof) = []"
  "neg_rel_sn_assms False (r :: ('f,'l,'v)reltrs_nontermination_proof) = []"
  "neg_fp_assms False (u :: ('f,'l,'v)fp_trs_nontermination_proof) = []"
  "neg_unknown_assms False (v :: ('f,'l,'v)neg_unknown_proof) = []"
  by (induct p and q and r and u and v
  rule: neg_dp_assms_neg_sn_assms_neg_rel_sn_assms_neg_fp_assms_neg_unknown_assms.induct[of
    "\<lambda> a p. neg_dp_assms False p = []"
    "\<lambda> a q. neg_sn_assms False q = []"
    "\<lambda> a r. neg_rel_sn_assms False r = []"
    "\<lambda> a u. neg_fp_assms False u = []"
    "\<lambda> a v. neg_unknown_assms False v = []"], auto)

fun mk_tp where
  "mk_tp I (nfs, q, r) = tp_ops.mk I nfs q r []"

fun mk_rel_tp where
  "mk_rel_tp I (nfs, q, r, rw) = tp_ops.mk I nfs q r rw"

fun mk_dpp where
  "mk_dpp I (nfs, m, p, pw, q, r, rw) = dpp_ops.mk I nfs m p pw q r rw"

context
  fixes I :: "('tp, ('f::{showl, compare_order}, 'l::{showl, compare_order}) lab, string) tp_ops"
  and J :: "('dpp, ('f, 'l) lab, string) dpp_ops"
  and assms :: bool
begin

definition check_dpp_subsumes :: "('f,'l,string)dppLL \<Rightarrow> 'dpp \<Rightarrow> showsl check" where
  "check_dpp_subsumes dp dpp \<equiv>
    case dp of (nfs,m,P,Pw,q,R,Rw) \<Rightarrow>
      (let pairs = P @ Pw;
           rules = R @ Rw;
           nfs' = dpp_ops.nfs J dpp;
           pairs' = dpp_ops.pairs J dpp;
           rules' = dpp_ops.rules J dpp;
           q' = dpp_ops.Q J dpp
       in do {
          check (q \<noteq> [] \<longrightarrow> nfs' \<longrightarrow> nfs) (showsl_lit (STR ''incompatible substitutions-in-normal-form flags''));
          check_subseteq pairs pairs'    <+? (\<lambda>r. toomuch (STR ''pair'') (showsl_rule r));
          check_subseteq rules rules'  <+? (\<lambda>r. toomuch (STR ''rule'') (showsl_rule r));
          check_NF_terms_subset  (is_NF_terms q) q' <+? (\<lambda>r. showsl_lit (STR ''NF(Q) differs due to term '') \<circ> showsl r)
        } <+? (\<lambda> s. showsl_lit (STR ''problem is showing subsumption for non-termination\<newline>'') \<circ> s))"

lemma check_dpp_subsumes: assumes ok: "isOK(check_dpp_subsumes dp dpp)"
  and inf: "infinite_dpp (mk_dpp_nt_set dp)"
  shows "infinite_dpp (dpp_ops.nfs J dpp, set (dpp_ops.pairs J dpp), set (dpp_ops.Q J dpp), set (dpp_ops.rules J dpp))"
proof (cases dp)
  case (fields nfs m p pw q r rw)
  note ok = ok[unfolded check_dpp_subsumes_def fields split Let_def, simplified]
  from inf[unfolded fields] have inf: "infinite_dpp (nfs, set p \<union> set pw, set q, set r \<union> set rw)" by simp
  show ?thesis
    by (rule infinite_dpp_mono[OF _ _ _ _ inf], insert ok, auto)
qed

definition check_tp_subsumes :: "('f, 'l, string) qtrsLL \<Rightarrow> 'tp \<Rightarrow> showsl check"
  where
    "check_tp_subsumes t tp = (case t of (nfs, q, rs) \<Rightarrow>
      (let nfs' = tp_ops.nfs I tp;
        rs' = tp_ops.rules I tp;
        q' = tp_ops.Q I tp
      in do {
        check (q \<noteq> [] \<longrightarrow> nfs' \<longrightarrow> nfs) (showsl_lit (STR ''incompatible substitutions-in-normal-form flags''));
        check_subseteq rs rs'  <+? (\<lambda>r. toomuch (STR ''rule'') (showsl_rule r));
        check_NF_terms_subset (is_NF_terms q) q' <+? (\<lambda>r. showsl_lit (STR ''NF(Q) differs due to term '') \<circ> showsl r)
      } <+? (\<lambda> s. showsl_lit (STR ''problem in showing subsumption for non-termination\<newline>'') \<circ> s)))"

lemma check_tp_subsumes: assumes ok: "isOK(check_tp_subsumes t tp)"
  and not: "satisfied (Not_SN_TRS t)"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))" (is "\<not> ?SN")
proof
  assume SN: ?SN
  obtain nfs q rules where t: "t = (nfs,q,rules)" by (cases t, auto)
  note ok = ok[unfolded check_tp_subsumes_def t split Let_def, simplified]
  have "SN (qrstep nfs (set q) (set rules))"
    by (rule SN_subset[OF SN qrstep_all_mono], insert ok, auto)
  with not[unfolded t] show False by auto
qed

definition check_rel_tp_subsumes :: "('f,'l,string)qreltrsLL \<Rightarrow> 'tp \<Rightarrow> showsl check" where
  "check_rel_tp_subsumes t tp \<equiv> case t of (nfs,q,r,rw) \<Rightarrow>
      (let nfs' = tp_ops.nfs I tp;
           rules' = tp_ops.rules I tp;
           r' = tp_ops.R I tp;
           q' = tp_ops.Q I tp
       in do {
          check (q \<noteq> [] \<longrightarrow> nfs' \<longrightarrow> nfs) (showsl_lit (STR ''incompatible substitutions-in-normal-form flags''));
          check_subseteq rw rules'  <+? (\<lambda>r. toomuch (STR ''rule'') (showsl_rule r));
          check_subseteq r r'  <+? (\<lambda>r. toomuch (STR ''rule'') (showsl_rule r));
          check_NF_terms_subset  (is_NF_terms q) q' <+? (\<lambda>r. showsl_lit (STR ''NF(Q) differs due to term '') \<circ> showsl r)
        } <+? (\<lambda> s. showsl_lit (STR ''problem in showing subsumption for non-termination\<newline>'') \<circ> s))"

lemma check_rel_tp_subsumes: assumes "tp_spec I"
  and ok: "isOK(check_rel_tp_subsumes t tp)"
  and not: "satisfied (Not_RelSN_TRS t)"
  shows "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))" (is "\<not> ?SN")
proof
  assume SN: ?SN
  obtain nfs q r rw where t: "t = (nfs,q,r,rw)" by (cases t, auto)
  interpret tp_spec I by fact
  note ok = ok[unfolded check_rel_tp_subsumes_def t split Let_def, simplified]
  note d = SN_qrel_def split
  have "SN_qrel (nfs, set q, set r, set rw)" unfolding d
    by (rule SN_rel_mono'[OF _ _ SN[unfolded d], folded qrstep_union, OF qrstep_all_mono qrstep_all_mono],
      insert ok, auto)
  with not[unfolded t] show False by auto
qed

definition check_fp_tp_subsumes :: "('f,'l,string)fptrsLL \<Rightarrow> ('f,'l,string)fptrsLL \<Rightarrow> showsl check" where
  "check_fp_tp_subsumes t t' \<equiv> case (t,t') of ((p,r),(p',r')) \<Rightarrow>
      (do {
          check (p = p') (showsl_lit (STR ''difference in forbidden patterns strategy''));
          check_subseteq r r'  <+? (\<lambda>r. toomuch (STR ''rule'') (showsl_rule r))
        } <+? (\<lambda> s. showsl_lit (STR ''problem in showing subsumption for non-termination\<newline>'') \<circ> s))"

lemma check_fp_tp_subsumes:
  assumes ok: "isOK(check_fp_tp_subsumes t t')"
  and not: "satisfied (Not_SN_FP_TRS t)"
  shows "\<not> SN_fpstep (mk_fptp_set t')" (is "\<not> ?SN")
proof
  assume SN: ?SN
  obtain p r where t: "t = (p,r)" by force
  obtain p' r' where t': "t' = (p',r')" by force
  note ok = ok[unfolded check_fp_tp_subsumes_def t t' split Let_def, simplified]
  from ok have id: "p = p'" by auto
  note d = SN_fpstep_def split
  have "SN_fpstep (set p, set r)" unfolding d
    by (rule SN_subset[OF SN[unfolded d t', simplified]], unfold id, rule fpstep_mono, insert ok, auto)
  with not show False unfolding t by simp
qed

fun check_assm :: "('tp \<Rightarrow> 'tp_prf \<Rightarrow> showsl check)
  \<Rightarrow> ('dpp \<Rightarrow> 'dpp_prf \<Rightarrow> showsl check)
  \<Rightarrow> ('tp \<Rightarrow> 'rtp_prf \<Rightarrow> showsl check)
  \<Rightarrow> (('f,'l,string)fptrsLL \<Rightarrow> 'fptp_prf \<Rightarrow> showsl check)
  \<Rightarrow> (unknown_info \<Rightarrow> 'unk_prf \<Rightarrow> showsl check)
  \<Rightarrow> ('f,'l,string, 'tp_prf, 'dpp_prf, 'rtp_prf, 'fptp_prf, 'unk_prf) generic_assm_proof \<Rightarrow> showsl check" where
  "check_assm tp_check dp_check rtp_check fptp_check unk_check (Not_SN_assm_proof t prf) = tp_check (mk_tp I t) prf"
| "check_assm tp_check dp_check rtp_check fptp_check unk_check (Not_RelSN_assm_proof t prf) = rtp_check (mk_rel_tp I t) prf"
| "check_assm tp_check dp_check rtp_check fptp_check unk_check (Infinite_assm_proof t prf) = dp_check (mk_dpp J t) prf"
| "check_assm tp_check dp_check rtp_check fptp_check unk_check (Not_SN_FP_assm_proof t prf) = fptp_check t prf"
| "check_assm tp_check dp_check rtp_check fptp_check unk_check (Unknown_assm_proof t prf) = unk_check t prf"
| "check_assm _ _ _ _ _ _ = error (showsl_lit (STR ''no support for termination assumptions in non-termination proof''))"

lemma check_assms_cong[fundef_cong]:
  assumes
  "\<And> t p. i = Not_SN_assm_proof t p \<Longrightarrow> tp (mk_tp I t) p = tp' (mk_tp I t) p"
  "\<And> t p. i = Infinite_assm_proof t p \<Longrightarrow> dpp (mk_dpp J t) p = dpp' (mk_dpp J t) p"
  "\<And> t p. i = Not_RelSN_assm_proof t p \<Longrightarrow> rtp (mk_rel_tp I t) p = rtp' (mk_rel_tp I t) p"
  "\<And> t p. i = Not_SN_FP_assm_proof t p \<Longrightarrow> fptp t p = fptp' t p"
  "\<And> t p. i = Unknown_assm_proof t p \<Longrightarrow> unk t p = unk' t p"
  shows "check_assm tp dpp rtp fptp unk i = check_assm tp' dpp' rtp' fptp' unk' i"
  using assms
  by (cases i, auto)

lemma check_assm:
  assumes
  "\<And> t p. i = Not_SN_assm_proof t p \<Longrightarrow> isOK(tp (mk_tp I t) p) \<Longrightarrow> \<not> SN_qrel (mk_tp_nt_set t)"
  "\<And> d p. i = Infinite_assm_proof d p \<Longrightarrow> isOK(dpp (mk_dpp J d) p) \<Longrightarrow> infinite_dpp (mk_dpp_nt_set d)"
  "\<And> t p. i = Not_RelSN_assm_proof t p \<Longrightarrow> isOK(rtp (mk_rel_tp I t) p) \<Longrightarrow> \<not> SN_qrel (mk_tp_set t)"
  "\<And> t p. i = Not_SN_FP_assm_proof t p \<Longrightarrow> isOK(fptp t p) \<Longrightarrow> \<not> SN_fpstep (mk_fptp_set t)"
  "\<And> d p. i = Unknown_assm_proof d p \<Longrightarrow> isOK(unk d p) \<Longrightarrow> unknown_satisfied d"
  shows "isOK(check_assm tp dpp rtp fptp unk i) \<Longrightarrow> satisfied (assm_proof_to_problem i)"
  using assms
  by (cases i, force+)

abbreviation (input) check_subproofs where
  "check_subproofs
    check_trs_nontermination_proof
    check_dp_nontermination_proof
    check_reltrs_nontermination_proof
    check_fptrs_nontermination_proof
    check_unknown_disproof i \<equiv> check_allm_index (\<lambda> as j. check_assm
             (check_trs_nontermination_proof (add_index i (Suc j)))
             (check_dp_nontermination_proof (add_index i (Suc j)))
             (check_reltrs_nontermination_proof (add_index i (Suc j)))
             (check_fptrs_nontermination_proof (add_index i (Suc j)))
             (check_unknown_disproof (add_index i (Suc j)))
             as)"

fun
  check_dp_nontermination_proof ::
    "showsl \<Rightarrow> 'dpp \<Rightarrow> ('f,'l, string) dp_nontermination_proof \<Rightarrow> showsl check"
   and
  check_trs_nontermination_proof ::
    "showsl \<Rightarrow> 'tp \<Rightarrow> ('f,'l, string) trs_nontermination_proof \<Rightarrow> showsl check"
   and
  check_reltrs_nontermination_proof ::
    "showsl \<Rightarrow> 'tp \<Rightarrow> ('f,'l, string) reltrs_nontermination_proof \<Rightarrow> showsl check"
   and
  check_fp_nontermination_proof ::
    "showsl \<Rightarrow> ('f,'l,string)fptrsLL \<Rightarrow> ('f, 'l, string) fp_trs_nontermination_proof \<Rightarrow> showsl check"
 and
  check_unknown_disproof ::
    "showsl \<Rightarrow> unknown_info \<Rightarrow>
     ('f, 'l, string) neg_unknown_proof \<Rightarrow>
     showsl check"
where
  "check_dp_nontermination_proof i dpp (DP_Loop p) = debug i (STR ''Loop'') (
    check_dp_loop J dpp p
      <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error in checking loop for the following DP-problem\<newline>'') 
         \<circ> showsl_dpp J dpp \<circ> showsl_nl \<circ> s))"
| "check_dp_nontermination_proof i dpp (DP_Nonloop p) = debug i (STR ''Nonloop'') (
      check_non_loop_dp_prf J dpp p
        <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error in checking nonloop for the following DP-problem\<newline>'') \<circ>
         showsl_dpp J dpp \<circ> showsl_nl \<circ> s)
  )"
| "check_dp_nontermination_proof i dpp (DP_Rule_Removal p prf) = debug i (STR ''Rule Removal'') (do {
    dpp' \<leftarrow> rule_removal_nonterm_dp J dpp p;
    check_dp_nontermination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the pair and rule removal\<newline>'') \<circ> s)
  })" 
| "check_dp_nontermination_proof i dpp (DP_Q_Reduction p prf) = debug i (STR ''Q reduction'') (do {
    dpp' \<leftarrow> dp_q_reduction_nonterm J dpp p
      <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error in reducing the innermost lhss in the following DP-problem\<newline>'') \<circ>
         showsl_dpp J dpp \<circ> showsl_nl \<circ> s);
    check_dp_nontermination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the Q reduction\<newline>'') \<circ> s)
  })"
| "check_dp_nontermination_proof i dpp (DP_Q_Increase p prf) = debug i (STR ''Q increase'') (do {
    dpp' \<leftarrow> q_increase_nonterm_dp J dpp p;
    check_dp_nontermination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the Q increase\<newline>'') \<circ> s)
  })"
| "check_dp_nontermination_proof i dpp (DP_Termination_Switch p prf) = debug i (STR ''Switch to Termination'') (do {
    dpp' \<leftarrow> switch_termination_proc string_rename J p dpp
      <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error in switching to full strategy for the DP-problem\<newline>'') \<circ>
         showsl_dpp J dpp \<circ> showsl_nl \<circ> s);
    check_dp_nontermination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the termination switch processor\<newline>'') \<circ> s)
  })"
| "check_dp_nontermination_proof i dpp (DP_Instantiation p prf) = debug i (STR ''Instantiation'') (do {
      dpp' \<leftarrow> instantiation_complete_proc J dpp p
        <+? ( \<lambda> s. i \<circ> showsl_lit (STR '': error when applying the instantiation processor on\<newline>'') \<circ>
         showsl_dpp J dpp \<circ> showsl_nl \<circ> s);
    check_dp_nontermination_proof (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the instantiation processor\<newline>'') \<circ> s)
  })"
| "check_dp_nontermination_proof i dpp (DP_Rewriting p prf) = debug i (STR ''Rewriting'') (do {
      dpp' \<leftarrow> rewriting_complete_proc J p dpp
        <+? ( \<lambda> s. i \<circ> showsl_lit (STR '': error when applying the rewriting processor\<newline>'') \<circ> s);
      check_dp_nontermination_proof (add_index i 1) dpp' prf
        <+? ( \<lambda> s. i \<circ> showsl_lit (STR '': error below the rewriting processor\<newline>'') \<circ> s)
  })"
| "check_dp_nontermination_proof i dpp (DP_Narrowing p prf) = debug i (STR ''Narrowing'') (do {
      dpp' \<leftarrow> narrowing_complete_proc J p dpp
        <+? ( \<lambda> s. i \<circ> showsl_lit (STR '': error when applying the narrowing processor\<newline>'') \<circ> s);
      check_dp_nontermination_proof (add_index i 1) dpp' prf
        <+? ( \<lambda> s. i \<circ> showsl_lit (STR '': error below the rewriting processor'') \<circ> s)
  })"
| "check_dp_nontermination_proof i dpp (DP_Assume_Infinite dp ass) =
    debug i (STR ''Finiteness Assumption or Unknown Proof'') (
      if assms
        then (do {
          check_dpp_subsumes dp dpp
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in finiteness assumption or unknown proof\<newline>'') \<circ> s \<circ> showsl_nl);
          check_subproofs
            check_trs_nontermination_proof
            check_dp_nontermination_proof
            check_reltrs_nontermination_proof
            check_fp_nontermination_proof
            check_unknown_disproof
            i ass
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below unknown proof\<newline>'') \<circ> s)
        }) else error (i \<circ> showsl_lit (STR '': the proof contains an assumption or unknown proof\<newline>''))
    )"
| "check_trs_nontermination_proof i tp (TRS_Loop p) = debug i (STR ''Loop'') (do {
    check_trs_loop I tp p
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when checking loop of\<newline>'') \<circ> showsl_tp I tp \<circ> showsl_nl
        \<circ> s)
  })"
| "check_trs_nontermination_proof i tp (TRS_Nonloop p) = debug i (STR ''Nonloop'') (
     check_non_loop_trs_prf I tp p
       <+? (\<lambda> s. showsl_lit (STR ''problem in checking possibly non-looping infinite reduction for\<newline>'') \<circ> showsl_tp I tp \<circ> s))"
| "check_trs_nontermination_proof i tp (TRS_Nonloop_SRS p) = debug i (STR ''Nonloop SRS'') (
     check_non_loop_srs_prf I tp p
       <+? (\<lambda> s. showsl_lit (STR ''problem in checking possibly non-looping infinite reduction for\<newline>'') \<circ> showsl_tp I tp \<circ> s))"
| "check_trs_nontermination_proof i tp TRS_Not_Well_Formed = debug i (STR ''Not Well-Formed'') (
    check_not_wwf_qtrs I tp
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in not well-formed proof\<newline>'') \<circ> s))"
| "check_trs_nontermination_proof i tp (TRS_Termination_Switch p prf) = debug i (STR ''Switch to Termination'') (do {
    tp' \<leftarrow> switch_termination_tt string_rename I p tp
      <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error in switching to full strategy for the DP-problem\<newline>'') \<circ>
         showsl_tp I tp \<circ> showsl_nl \<circ> s);
    check_trs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the termination switch technique\<newline>'')
          \<circ> s)
  })"
| "check_trs_nontermination_proof i tp (TRS_Rule_Removal p prf) = debug i (STR ''Rule Removal'') (do {
     tp' \<leftarrow> rule_removal_nonterm_trs I tp p;
     check_trs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the rule removal\<newline>'') \<circ> s)
  })"
| "check_trs_nontermination_proof i tp (TRS_String_Reversal prf) =
    debug i (STR ''String Reversal'') (do {
      tp' \<leftarrow> string_reversal_complete_tt I tp <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying string reversal on\<newline>'')
        \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s);
      check_trs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the string reversal technique\<newline>'')
          \<circ> s)
    })"
| "check_trs_nontermination_proof i tp (TRS_Constant_String p prf) =
    debug i (STR ''Constants into Unary'') (do {
      tp' \<leftarrow> const_to_string_complete_tt I tp p <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when turning constants into strings on\<newline>'')
        \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s);
      check_trs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the constants into string technique\<newline>'')
          \<circ> s)
    })"
| "check_trs_nontermination_proof i tp (TRS_DP_Trans p prf) = debug i (STR ''DP Transformation'') (do {
    dpp \<leftarrow> dp_trans_nontermination_tt I J tp p <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in DP transformation on\<newline>'')
        \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s);
    check_dp_nontermination_proof (add_index i 1) dpp prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the DP transformation\<newline>'')
          \<circ> s)
  })"
| "check_trs_nontermination_proof i tp (TRS_Q_Increase p prf) =
    debug i (STR ''Q increase'') (do {
      tp' \<leftarrow> q_increase_nonterm_trs I tp p;
      check_trs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the Q increase technique\<newline>'')
          \<circ> s)
    })"
| "check_trs_nontermination_proof i tp (TRS_Uncurry p prf) =
    debug i (STR ''Uncurrying'') (do {
      tp' \<leftarrow> uncurry_nonterm_tt I p tp;
      check_trs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the uncurrying technique\<newline>'')
          \<circ> s)
    })"
| "check_trs_nontermination_proof i tp (TRS_Not_WN_Tree_Automaton prf) =
     check_not_wn_ta_prf I tp prf
       <+? (\<lambda> s. showsl_lit (STR ''error in tree automaton based non-termination proof for\<newline>'') \<circ> showsl_tp I tp \<circ> s)"
| "check_trs_nontermination_proof i tp TRS_Not_RG_Decision =
     right_ground_nonterm I tp
       <+? (\<lambda> s. showsl_lit (STR ''error in application of right-ground decision procedure for\<newline>'') \<circ> showsl_tp I tp \<circ> s)"
| "check_trs_nontermination_proof i tp (TRS_Assume_Not_SN t ass) =
    debug i (STR ''Finiteness Assumption or Unknown Proof'') (
      if assms
        then (do {
          check_tp_subsumes t tp
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in non-termination assumption or unknown proof\<newline>'') \<circ> s \<circ> showsl_nl);
          check_subproofs
            check_trs_nontermination_proof
            check_dp_nontermination_proof
            check_reltrs_nontermination_proof
            check_fp_nontermination_proof
            check_unknown_disproof
            i ass
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below unknown proof\<newline>'')
                 \<circ> s)
        }) else error (i \<circ> showsl_lit (STR '': the proof contains an assumption or unknown proof\<newline>''))
    )"
| "check_reltrs_nontermination_proof i tp (Rel_Loop p) = debug i (STR ''Loop'') (do {
    check_rel_trs_loop I tp p
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in loop proof\<newline>'') \<circ> s)
  })"
| "check_reltrs_nontermination_proof i tp (Rel_R_Not_SN prf) = do {
    tp' \<leftarrow> reltrs_as_trs I tp;
    check_trs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the nontermination proof for R\<newline>'')
          \<circ> s)
  }"
| "check_reltrs_nontermination_proof i tp Rel_Not_Well_Formed = debug i (STR ''Not Well-Formed'') (do {
    check_not_wf_reltrs I tp
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in not-well-formed proof\<newline>'') \<circ> s)
  })"
| "check_reltrs_nontermination_proof i tp (Rel_TRS_String_Reversal prf) =
    debug i (STR ''String Reversal'') (do {
      tp' \<leftarrow> string_reversal_complete_rel_tt I tp <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying string reversal on\<newline>'')
        \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s);
      check_reltrs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the string reversal technique\<newline>'')
          \<circ> s)
    })"
| "check_reltrs_nontermination_proof i tp (Rel_Rule_Removal p prf) =
    debug i (STR ''Rule Removal'') (do {
      tp' \<leftarrow> rule_removal_nonterm_reltrs I tp p;
      check_reltrs_nontermination_proof (add_index i 1) tp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the rule removal\<newline>'')
          \<circ> s)
    })"
| "check_reltrs_nontermination_proof i tp (Rel_TRS_Assume_Not_SN t ass) =
    debug i (STR ''Finiteness Assumption or Unknown Proof'') (
      if assms
        then (do {
          check_rel_tp_subsumes t tp
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in non-termination assumption or unknown proof\<newline>'') \<circ> s \<circ> showsl_nl);
          check_subproofs
            check_trs_nontermination_proof
            check_dp_nontermination_proof
            check_reltrs_nontermination_proof
            check_fp_nontermination_proof
            check_unknown_disproof
            i ass
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below unknown proof\<newline>'')
                 \<circ> s)
        }) else error (i \<circ> showsl_lit (STR '': the proof contains an assumption or unknown proof\<newline>''))
    )"
| "check_fp_nontermination_proof i (P, r) (FP_TRS_Loop p) = (
  case p of TRS_loop_prf a b c d \<Rightarrow>
 debug i (STR ''Loop'') (do {
    check_fploop r P (FP_loop_prf d c a b)
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when checking forbidden pattern loop\<newline>'')
          \<circ> s)
  }))"
| "check_fp_nontermination_proof i (P, r) (FP_TRS_Rule_Removal p prf) = debug i (STR ''Rule Removal'') (do {
     tp' \<leftarrow> rule_removal_nonterm_fp_trs I (tp_ops.mk I False [] r []) p;
     check_fp_nontermination_proof (add_index i 1) (P, tp_ops.rules I tp') prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the rule removal\<newline>'')
          \<circ> s)
   })"
| "check_fp_nontermination_proof i tp (FPTRS_Assume_Not_SN t ass) =
    debug i (STR ''Finiteness Assumption or Unknown Proof'') (
      if assms
        then (do {
          check_fp_tp_subsumes t tp
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in non-termination assumption or unknown proof\<newline>'') \<circ> s \<circ> showsl_nl);
          check_subproofs
            check_trs_nontermination_proof
            check_dp_nontermination_proof
            check_reltrs_nontermination_proof
            check_fp_nontermination_proof
            check_unknown_disproof
            i ass
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below unknown proof\<newline>'')
                 \<circ> s)
        }) else error (i \<circ> showsl_lit (STR '': the proof contains an assumption or unknown proof\<newline>''))
    )"
| "check_unknown_disproof i tp (Assume_NT_Unknown tp' ass) =
    debug i (STR ''Unknown Proof'') (
      if assms
        then (do {
          check (tp = tp') (showsl_lit (STR ''unknown problems are not identical:\<newline>'') \<circ> showsl tp
            \<circ> showsl_lit (STR ''\<newline> vs\<newline>'') \<circ> showsl tp')
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in nontermination assumption or unknown proof\<newline>'') \<circ> s \<circ> showsl_nl);
          check_subproofs
            check_trs_nontermination_proof
            check_dp_nontermination_proof
            check_reltrs_nontermination_proof
            check_fp_nontermination_proof
            check_unknown_disproof
            i ass
        }) else error (i \<circ> showsl_lit (STR '': the proof contains an unknown proof\<newline>''))
    )"


lemma deal_with_assms:
    assumes I: "tp_spec I" and J: "dpp_spec J"
    and 1: "\<And> x t p i'.
           x \<in> set prof \<Longrightarrow>
           x = Not_SN_assm_proof t p \<Longrightarrow>
           isOK (local.check_trs_nontermination_proof i' (mk_tp I t) p) \<Longrightarrow>
           Ball (set (neg_sn_assms assms p)) holds \<Longrightarrow>
           \<not> SN (qrstep (tp_ops.nfs I (mk_tp I t)) (set (tp_ops.Q I (mk_tp I t)))
                   (set (tp_ops.rules I (mk_tp I t))))"
    and 2: "\<And> x t p i'.
           x \<in> set prof \<Longrightarrow>
           x = Infinite_assm_proof t p \<Longrightarrow>
           isOK (local.check_dp_nontermination_proof i' (mk_dpp J t) p) \<Longrightarrow>
           Ball (set (neg_dp_assms assms p)) holds \<Longrightarrow>
           infinite_dpp
            (dpp_ops.nfs J (mk_dpp J t), set (dpp_ops.pairs J (mk_dpp J t)), set (dpp_ops.Q J (mk_dpp J t)),
             set (dpp_ops.rules J (mk_dpp J t)))"
     and 3: "\<And>x t p i'.
           x \<in> set prof \<Longrightarrow>
           x = Not_RelSN_assm_proof t p \<Longrightarrow>
           isOK (local.check_reltrs_nontermination_proof i' (mk_rel_tp I t) p) \<Longrightarrow>
           Ball (set (neg_rel_sn_assms assms p)) holds \<Longrightarrow>
           \<not> SN_qrel
               (tp_ops.nfs I (mk_rel_tp I t), set (tp_ops.Q I (mk_rel_tp I t)), set (tp_ops.R I (mk_rel_tp I t)),
                set (tp_ops.Rw I (mk_rel_tp I t)))"
    and 4: "\<And> x t p i'.
           x \<in> set prof \<Longrightarrow>
           x = Not_SN_FP_assm_proof t p \<Longrightarrow>
           isOK (local.check_fp_nontermination_proof i' t p) \<Longrightarrow>
           Ball (set (neg_fp_assms assms p)) holds \<Longrightarrow>
           \<not> SN_fpstep (mk_fptp_set t)"
     and 5: "\<And>x t p i'.
           x \<in> set prof \<Longrightarrow>
           x = Unknown_assm_proof t p \<Longrightarrow>
           isOK (local.check_unknown_disproof i' t p) \<Longrightarrow>
           Ball (set (neg_unknown_assms assms p)) holds \<Longrightarrow> unknown_satisfied t"
     and ass: "\<And> x. x \<in> set prof \<Longrightarrow> Ball (set (collect_assms
       (neg_sn_assms assms)
       (neg_dp_assms assms)
       (neg_rel_sn_assms assms)
       (neg_fp_assms assms)
       (neg_unknown_assms assms) x)) holds"
    and x: "x \<in> set prof"
    and ok: "isOK (check_assm
             (check_trs_nontermination_proof i)
             (check_dp_nontermination_proof i)
             (check_reltrs_nontermination_proof i)
             (check_fp_nontermination_proof i)
             (check_unknown_disproof i)
             x)"
  shows "satisfied (assm_proof_to_problem x)"
proof (rule check_assm[OF _ _ _ _ _ ok])
  fix ps tp
  assume id: "x = Not_SN_assm_proof tp ps"
  assume ok: "isOK (check_trs_nontermination_proof i (mk_tp I tp) ps)"
  from id ass x have ass: "\<forall>a\<in>set (neg_sn_assms assms ps). holds a" by auto
  interpret tp_spec I by fact
  show "\<not> SN_qrel (mk_tp_nt_set tp)"
    using 1[OF x id ok ass]
    by (cases tp, auto simp: check_def)
next
  fix ps dp
  assume id: "x = Infinite_assm_proof dp ps"
  assume ok: "isOK (check_dp_nontermination_proof i (mk_dpp J dp) ps)"
  from id ass x have ass: "\<forall>a\<in>set (neg_dp_assms assms ps). holds a" by auto
  interpret dpp_spec J by fact
  show "infinite_dpp (mk_dpp_nt_set dp)"
    using 2[OF x id ok ass] by (cases dp, auto simp: check_def)
next
  fix ps tp
  assume id: "x = Not_RelSN_assm_proof tp ps"
  assume ok: "isOK (check_reltrs_nontermination_proof i (mk_rel_tp I tp) ps)"
  from id ass x have ass: "\<forall>a\<in>set (neg_rel_sn_assms assms ps). holds a" by auto
  interpret tp_spec I by fact
  show "\<not> SN_qrel (mk_tp_set tp)"
    using 3[OF x id ok ass] by (cases tp, auto simp: check_def)
next
  fix t ps
  assume id: "x = Not_SN_FP_assm_proof t ps"
  assume ok: "isOK (check_fp_nontermination_proof i t ps)"
  from id ass x have ass: "\<forall>a\<in>set (neg_fp_assms assms ps). holds a" by auto
  show "\<not> SN_fpstep (mk_fptp_set t)"
    using 4[OF x id ok ass] by auto
next
  fix ps u
  assume id: "x = Unknown_assm_proof u ps"
  assume ok: "isOK (check_unknown_disproof i u ps)"
  from id ass x have ass: "\<forall>a\<in>set (neg_unknown_assms assms ps). holds a" by auto
  show "unknown_satisfied u"
    using 5[OF x id ok ass] by (auto simp: check_def)
qed

lemma check_dp_trs_unk_nontermination_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
  shows "isOK (check_dp_nontermination_proof i dpp prf)
    \<Longrightarrow> Ball (set (neg_dp_assms assms prf)) holds
    \<Longrightarrow> infinite_dpp (dpp_ops.nfs J dpp, set (dpp_ops.pairs J dpp), set (dpp_ops.Q J dpp), set (dpp_ops.rules J dpp))"
  and "isOK (check_trs_nontermination_proof i' tp prf')
    \<Longrightarrow> Ball (set (neg_sn_assms assms prf')) holds
    \<Longrightarrow> \<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
  and "isOK (check_reltrs_nontermination_proof i'' tp' prf'')
    \<Longrightarrow> Ball (set (neg_rel_sn_assms assms prf'')) holds
    \<Longrightarrow> \<not> SN_qrel (tp_ops.nfs I tp', set (tp_ops.Q I tp'), set (tp_ops.R I tp'),  set (tp_ops.Rw I tp'))"
  and "isOK (check_fp_nontermination_proof i''' tp'' prf''')
    \<Longrightarrow> Ball (set (neg_fp_assms assms prf''')) holds
    \<Longrightarrow> \<not> SN_fpstep (mk_fptp_set tp'')"
  and "isOK (check_unknown_disproof i'''' unkp prf'''') \<Longrightarrow> \<forall>assm\<in>set (neg_unknown_assms assms prf''''). holds assm
    \<Longrightarrow> unknown_satisfied unkp"
proof (induct dpp "prf" and tp prf' and tp' prf'' and tp'' prf''' and unkp prf''''
  arbitrary: i and i' and i'' and i''' and i''''
  rule: check_dp_nontermination_proof_check_trs_nontermination_proof_check_reltrs_nontermination_proof_check_fp_nontermination_proof_check_unknown_disproof.induct)
  case (1 i dpp p)
  then have "isOK (check_dp_loop J dpp p)"
    unfolding check_dp_nontermination_proof.simps Let_def by simp
  from check_dp_loop[OF J this]
  show ?case by blast
next
  case (2 i dpp p)
  then have "isOK (check_non_loop_dp_prf J dpp p)"
    unfolding check_dp_nontermination_proof.simps Let_def by simp
  from check_non_loop_dp_prf[OF this]
  show ?case by blast
next
  case (3 i dpp p "prf")
  note IH = this
  let ?call = "rule_removal_nonterm_dp J dpp p"
  from IH(2) obtain dpp' where call: "?call = return dpp'" by (cases ?call, auto)
  from rule_removal_nonterm_dp[OF J call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (4 i dpp p prof)
  note IH = this
  let ?call = "dp_q_reduction_nonterm J dpp p"
  from IH(2) obtain dpp' where call: "?call = return dpp'" by (cases ?call, auto)
  from dp_q_reduction_nonterm[OF J call IH(1) infinite_lab] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (5 i dpp p prof)
  note IH = this
  let ?call = "q_increase_nonterm_dp J dpp p"
  from IH(2) obtain dpp' where call: "?call = return dpp'" by (cases ?call, auto)
  from q_increase_nonterm_dp[OF J call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (6 i dpp p prof)
  note IH = this
  let ?call = "switch_termination_proc string_rename J p dpp"
  from IH(2) obtain dpp' where call: "?call = return dpp'" by (cases ?call, auto)
  from switch_termination_proc[OF J infinite_lab call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (7 i dpp p prof)
  note IH = this
  let ?call = "instantiation_complete_proc J dpp p"
  from IH(2) obtain dpp' where call: "?call = return dpp'" by (cases ?call, auto)
  from instantiation_complete_proc[OF J call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (8 i dpp p prof)
  note IH = this
  let ?call = "rewriting_complete_proc J p dpp"
  from IH(2) obtain dpp' where call: "?call = return dpp'" by (cases ?call, auto)
  from rewriting_complete_proc[OF J call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (9 i dpp p  prof)
  note IH = this
  let ?call = "narrowing_complete_proc J p dpp"
  from IH(2) obtain dpp' where call: "?call = return dpp'" by (cases ?call, auto)
  from narrowing_complete_proc[OF J call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (10 i dpp dp prof)
  note IH = this
  from IH(6) have assms and subsumes: "isOK(check_dpp_subsumes dp dpp)" by auto
  note IHH = IH(1-5)[OF \<open>assms\<close>]
  from IH(7) \<open>assms\<close> have ass: "\<lbrakk> \<And> x. x \<in> set prof \<Longrightarrow> satisfied (assm_proof_to_problem x)\<rbrakk> \<Longrightarrow> infinite_dpp (mk_dpp_nt_set dp)"
    by auto
  from IH(7) \<open>assms\<close> have sub_ass: "\<And> x. x \<in> set prof \<Longrightarrow> Ball (set (collect_assms
    (neg_sn_assms assms)
    (neg_dp_assms assms)
    (neg_rel_sn_assms assms)
    (neg_fp_assms assms)
    (neg_unknown_assms assms) x)) holds"
    by auto
  show ?case
  proof (rule check_dpp_subsumes[OF subsumes ass])
    fix x
    assume mem: "x \<in> set prof"
    then obtain i where i: "i < length prof" and x: "x = prof ! i" unfolding set_conv_nth by auto
    show "satisfied (assm_proof_to_problem x)"
      by (rule deal_with_assms[OF I J IHH(1-5) sub_ass mem], insert IH(6) i x subsumes, auto simp: check_def)
  qed
next
  case (11 i tp p)
  then have "isOK (check_trs_loop I tp p)" by simp
  from check_trs_loop_sound[OF this] show ?case by simp
next
  case (12 i tp "prf")
  then have "isOK (check_non_loop_trs_prf I tp prf)" by simp
  from check_non_loop_trs_prf[OF this] show ?case by simp
next
  case (13 i tp p)
  then have "isOK (check_non_loop_srs_prf I tp p)" by simp
  from check_non_loop_srs_prf[OF this] show ?case by simp
next
  case (14 i tp)
  then have "isOK (check_not_wwf_qtrs I tp)" by simp
  from check_not_wwf_qtrs_sound[OF I this]
  show ?case by auto
next
  case (15 i tp p prof)
  note IH = this
  let ?call = "switch_termination_tt string_rename I p tp"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from switch_termination_tt[OF I infinite_lab call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (16 i tp p "prf")
  note IH = this
  let ?call = "rule_removal_nonterm_trs I tp p"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from rule_removal_nonterm_trs[OF I call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (17 i tp "prf")
  note IH = this
  let ?call = "string_reversal_complete_tt I tp"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from string_reversal_complete_tt[OF I call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (18 i tp p "prf")
  note IH = this
  let ?call = "const_to_string_complete_tt I tp p"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from const_to_string_complete_tt[OF I call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (19 i tp p "prf")
  note IH = this
  let ?call = "dp_trans_nontermination_tt I J tp p"
  from IH obtain dpp where call: "?call = return dpp" by (cases ?call, auto)
  from dp_trans_nontermination_tt[OF I J call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (20 i tp p "prf")
  note IH = this
  let ?call = "q_increase_nonterm_trs I tp p"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from q_increase_nonterm_trs[OF I call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (21 i tp p "prf")
  note IH = this
  let ?call = "uncurry_nonterm_tt I p tp"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from uncurry_nonterm_tt[OF I call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (22 i tp "prf")
  then have "isOK (check_not_wn_ta_prf I tp prf)" by simp
  from check_not_wn_ta_prf[OF this] show ?case by simp
next
  case (23 i tp)
  then have ok: "isOK (right_ground_nonterm I tp)" by simp
  interpret tp_spec I by fact
  from right_ground_nonterm[OF ok] show ?case .
next
  case (24 i tp t prof)
  note IH = this
  from IH(6) have assms and subsumes: "isOK(check_tp_subsumes t tp)" by auto
  note IHH = IH(1-5)[OF \<open>assms\<close>]
  from IH(7) \<open>assms\<close> have ass: "\<lbrakk> \<And> x. x \<in> set prof \<Longrightarrow> satisfied (assm_proof_to_problem x)\<rbrakk> \<Longrightarrow> satisfied (Not_SN_TRS t)"
    by auto
  from IH(7) \<open>assms\<close> have sub_ass: "\<And> x. x \<in> set prof \<Longrightarrow> Ball (set (collect_assms
    (neg_sn_assms assms)
    (neg_dp_assms assms)
    (neg_rel_sn_assms assms)
    (neg_fp_assms assms)
    (neg_unknown_assms assms) x)) holds"
    by auto
  show ?case
  proof (rule check_tp_subsumes[OF subsumes ass])
    fix x
    assume mem: "x \<in> set prof"
    then obtain i where i: "i < length prof" and x: "x = prof ! i" unfolding set_conv_nth by auto
    show "satisfied (assm_proof_to_problem x)"
      by (rule deal_with_assms[OF I J IHH sub_ass mem], insert IH(6) i x subsumes, auto simp: check_def)
  qed
next
  case (25 i tp p)
  then have "isOK (check_rel_trs_loop I tp p)" by simp
  from check_rel_trs_loop[OF I this] show ?case .
next
  case (26 i tp "prf")
  note IH = this
  let ?call = "reltrs_as_trs I tp"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from reltrs_as_trs[OF I call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (27 i tp)
  then have "isOK(check_not_wf_reltrs I tp)" by auto
  from check_not_wf_reltrs[OF I this] show ?case by simp
next
  case (28 i tp "prf")
  note IH = this
  let ?call = "string_reversal_complete_rel_tt I tp"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from string_reversal_complete_rel_tt[OF I call IH(1)] IH(2-3) call
  show ?case by simp
next
  case (29 i tp p "prf")
  note IH = this
  let ?call = "rule_removal_nonterm_reltrs I tp p"
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  from rule_removal_nonterm_reltrs[OF I call IH(1)] IH(2-3) call
  show ?case by (auto simp: o_def)
next
  case (30 i tp t prof)
  note IH = this
  from IH(6) have assms and subsumes: "isOK(check_rel_tp_subsumes t tp)" by auto
  note IHH = IH(1-5)[OF \<open>assms\<close>]
  from IH(7) \<open>assms\<close> have ass: "\<lbrakk> \<And> x. x \<in> set prof \<Longrightarrow> satisfied (assm_proof_to_problem x)\<rbrakk> \<Longrightarrow> satisfied (Not_RelSN_TRS t)"
    by auto
  from IH(7) \<open>assms\<close> have sub_ass: "\<And> x. x \<in> set prof \<Longrightarrow> Ball (set (collect_assms
    (neg_sn_assms assms)
    (neg_dp_assms assms)
    (neg_rel_sn_assms assms)
    (neg_fp_assms assms)
    (neg_unknown_assms assms) x)) holds"
    by auto
  show ?case
  proof (rule check_rel_tp_subsumes[OF I subsumes ass])
    fix x
    assume mem: "x \<in> set prof"
    then obtain i where i: "i < length prof" and x: "x = prof ! i" unfolding set_conv_nth by auto
    show "satisfied (assm_proof_to_problem x)"
      by (rule deal_with_assms[OF I J IHH sub_ass mem], insert IH(6) i x subsumes, auto simp: check_def)
  qed
next
  case (31 i fp a p b)
  note IH = this
  obtain c d e f where p[simp]: "p = TRS_loop_prf c d e f" by (cases p, auto) 
  note [simp del] = check_fploop.simps
  from IH[simplified] have "isOK (check_fploop a fp (FP_loop_prf f e c d))" by simp
  from check_fploop_not_SN[OF this]
  show ?case by (simp add: SN_fpstep_def)
next
  case (32 i fp r p "prf")
  note IH = this
  let ?tp = "tp_ops.mk I False [] r []"
  let ?call = "rule_removal_nonterm_fp_trs I ?tp p"
  interpret tp_spec I by fact
  from IH(2) obtain tp' where call: "?call = return tp'" by (cases ?call, auto)
  have "\<not> SN_fpstep (mk_fptp_set (fp, tp_ops.rules I tp'))"
    by (rule IH(1)[OF call], insert IH(2-3) call, auto)
  then have "\<not> SN (fpstep (set fp) (set (tp_ops.rules I tp')))"
    unfolding SN_fpstep_def by simp
  from rule_removal_nonterm_fp_trs[OF I call this]
  show ?case by (simp add: SN_fpstep_def)
next
  case (33 i tp t prof)
  note IH = this
  from IH(6) have assms and subsumes: "isOK(check_fp_tp_subsumes t tp)" by auto
  note IHH = IH(1-5)[OF \<open>assms\<close>]
  from IH(7) \<open>assms\<close> have ass: "\<lbrakk> \<And> x. x \<in> set prof \<Longrightarrow> satisfied (assm_proof_to_problem x)\<rbrakk> \<Longrightarrow> satisfied (Not_SN_FP_TRS t)"
    by auto
  from IH(7) \<open>assms\<close> have sub_ass: "\<And> x. x \<in> set prof \<Longrightarrow> Ball (set (collect_assms
    (neg_sn_assms assms)
    (neg_dp_assms assms)
    (neg_rel_sn_assms assms)
    (neg_fp_assms assms)
    (neg_unknown_assms assms) x)) holds"
    by auto
  show ?case
  proof (rule check_fp_tp_subsumes[OF subsumes ass])
    fix x
    assume mem: "x \<in> set prof"
    then obtain i where i: "i < length prof" and x: "x = prof ! i" unfolding set_conv_nth by auto
    show "satisfied (assm_proof_to_problem x)"
      by (rule deal_with_assms[OF I J IHH sub_ass mem], insert IH(6) i x subsumes, auto simp: check_def)
  qed
next
  case (34 i unk un prof)
  note IH = this
  from IH(6) have assms and subsumes: "unk = un" by auto
  note IHH = IH(1-5)[OF \<open>assms\<close>]
  from IH(7) \<open>assms\<close> have ass: "\<lbrakk> \<And> x. x \<in> set prof \<Longrightarrow> satisfied (assm_proof_to_problem x)\<rbrakk> \<Longrightarrow> unknown_satisfied un"
    by auto
  from IH(7) \<open>assms\<close> have sub_ass: "\<And> x. x \<in> set prof \<Longrightarrow> Ball (set (collect_assms
    (neg_sn_assms assms)
    (neg_dp_assms assms)
    (neg_rel_sn_assms assms)
    (neg_fp_assms assms)
    (neg_unknown_assms assms) x)) holds"
    by auto
  show ?case unfolding subsumes
  proof (rule ass)
    fix x
    assume mem: "x \<in> set prof"
    then obtain i where i: "i < length prof" and x: "x = prof ! i" unfolding set_conv_nth by auto
    show "satisfied (assm_proof_to_problem x)"
      by (rule deal_with_assms[OF I J IHH sub_ass mem], insert IH(6) i x subsumes, auto simp: check_def)
  qed
qed
end

lemma check_trs_nontermination_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ass: "\<forall>assm\<in>set (neg_sn_assms a prf). holds assm"
    and ok: "isOK (check_trs_nontermination_proof I J a i tp prf)"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
  by (rule check_dp_trs_unk_nontermination_proof_with_assms[OF I J], insert ass ok, auto)

lemma check_trs_nontermination_proof:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_trs_nontermination_proof I J False i tp prf)"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
  by (rule check_trs_nontermination_proof_with_assms[OF I J _ ok], simp)

lemma check_reltrs_nontermination_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ass: "\<forall>assm\<in>set (neg_rel_sn_assms a prf). holds assm"
    and ok: "isOK (check_reltrs_nontermination_proof I J a i tp prf)"
  shows "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))"
  by (rule check_dp_trs_unk_nontermination_proof_with_assms[OF I J], insert ass ok, auto)

lemma check_reltrs_nontermination_proof:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_reltrs_nontermination_proof I J False i tp prf)"
  shows "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))"
  by (rule check_reltrs_nontermination_proof_with_assms[OF I J _ ok], simp)

lemma check_fp_nontermination_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ass: "\<forall>assm\<in>set (neg_fp_assms a prf). holds assm"
    and ok: "isOK (check_fp_nontermination_proof I J a i tp prf)"
  shows "\<not> SN_fpstep (mk_fptp_set tp)"
  by (rule check_dp_trs_unk_nontermination_proof_with_assms[OF I J], insert ass ok, auto)

lemma check_fp_nontermination_proof:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_fp_nontermination_proof I J False i tp prf)"
  shows "\<not> SN_fpstep (mk_fptp_set tp)"
  by (rule check_fp_nontermination_proof_with_assms[OF I J _ ok], auto)

lemma check_dp_nontermination_proof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ass: "\<forall>assm\<in>set (neg_dp_assms a prf). holds assm"
  and ok: "isOK (check_dp_nontermination_proof I J a i dpp prf)"
  shows "infinite_dpp (dpp_ops.nfs J dpp, set (dpp_ops.pairs J dpp), set (dpp_ops.Q J dpp), set (dpp_ops.rules J dpp))"
  by (rule check_dp_trs_unk_nontermination_proof_with_assms[OF I J], insert ass ok, auto)

lemma check_dp_nontermination_proof:
  assumes I: "tp_spec I" and J: "dpp_spec J"
  and ok: "isOK (check_dp_nontermination_proof I J False i dpp prf)"
  shows "infinite_dpp (dpp_ops.nfs J dpp, set (dpp_ops.pairs J dpp), set (dpp_ops.Q J dpp), set (dpp_ops.rules J dpp))"
  by (rule check_dp_nontermination_proof_with_assms[OF I J _ ok], simp)

lemma check_unknown_disproof_with_assms:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_unknown_disproof I J a i u prf)"
    and ass: "\<forall>assm\<in>set (neg_unknown_assms a prf). holds assm"
  shows "unknown_satisfied u"
  by (rule check_dp_trs_unk_nontermination_proof_with_assms[OF I J], insert ass ok, auto)

lemma check_unknown_proof:
  assumes "tp_spec I" and "dpp_spec J"
    and "isOK (check_unknown_disproof I J False i u prf)"
  shows "unknown_satisfied u"
  using check_unknown_disproof_with_assms[OF assms] by simp

fun trs_nontermination_proof_to_fp :: "(_,_,_)trs_nontermination_proof \<Rightarrow> showsl + (_,_,_)fp_trs_nontermination_proof" where
  "trs_nontermination_proof_to_fp (TRS_Loop x) = return (FP_TRS_Loop x)"
| "trs_nontermination_proof_to_fp (TRS_Rule_Removal x p) = do { p' \<leftarrow> trs_nontermination_proof_to_fp p;
       return (FP_TRS_Rule_Removal x p')}"
| "trs_nontermination_proof_to_fp _ = error 
     (showsl_lit (STR ''for the given strategy, only loops and rule removal are supported as nontermination techniques''))"

end
