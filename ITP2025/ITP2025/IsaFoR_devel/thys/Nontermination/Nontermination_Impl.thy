(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2012)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2013)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
License: LGPL (see file COPYING.LESSER)
*)
theory Nontermination_Impl
imports
  Nontermination
  TRS.Outermost_Rewriting
  TRS.Q_Restricted_Rewriting_Impl
  Q_Reduction_Nonterm_Impl
  Sem_Lab.Labelings_Impl
  Auxx.Map_Choice
begin

definition
  check_dps ::
    "('f \<Rightarrow> 'f) \<Rightarrow> ('f:: showl, 'v:: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rule check"
where
  "check_dps unshp r p = (
    let D = defined_list r in (
    check_all (\<lambda>(ll, rr). is_Fun rr \<and> (the (root rr)) \<notin> set D
      \<and> Bex (set r) (\<lambda>(l, r). l = sharp_term unshp ll \<and> r \<unrhd> sharp_term unshp rr)) p))"

lemma check_dps_sound:
  assumes check: "isOK (check_dps unshp r p)" 
    and infinite: "infinite_dpp (nfs,set p, set q, set r)"
    and nfs: "\<not> nfs"
  shows "\<not> SN (qrstep nfs (set q) (set r))"
  by (rule infinite_dpp_imp_not_SN[OF _ infinite nfs],
  insert check[unfolded check_dps_def], auto)

fun unsharp :: "('f, 'l) lab \<Rightarrow> ('f, 'l) lab" where
  "unsharp (Sharp f) = f"
| "unsharp f = f"

datatype ('f,'l,'v)dp_trans_nontermination_tt_prf = DP_trans_nontermination_tt_prf "(('f,'l)lab,'v)rules"

fun dp_trans_nontermination_tt where 
  "dp_trans_nontermination_tt I J tp (DP_trans_nontermination_tt_prf P) = (do {
     let R = tp_ops.rules I tp;
     let Q = tp_ops.Q I tp;
     check (Q = [] \<or> \<not> tp_ops.nfs I tp) (showsl_lit (STR ''strategies and normal form substitutions problem''));
     check_dps unsharp R P
       <+? (\<lambda>lr. showsl_lit (STR ''problematic rule: '') \<circ> showsl_rule lr);
     return (dpp_ops.mk J False False P [] Q [] R)
  })"

lemma dp_trans_nontermination_tt:
  assumes "tp_spec I" "dpp_spec J"
   and ok: "dp_trans_nontermination_tt I J tp prf = return dpp"
   and inf: "infinite_dpp (dpp_ops.nfs J dpp, set (dpp_ops.pairs J dpp), set (dpp_ops.Q J dpp), set (dpp_ops.rules J dpp))"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
proof -
  obtain P where id: "prf = DP_trans_nontermination_tt_prf P" by (cases "prf")
  interpret tp_spec I by fact
  note ok = ok[unfolded id dp_trans_nontermination_tt.simps Let_def, simplified]
  let ?R = "rules tp"
  let ?Q = "Q tp"
  let ?dpp = "dpp_ops.mk J False False P [] ?Q [] ?R"
  from ok have ok_dps: "isOK (check_dps unsharp ?R P)" by simp
  from ok have nfs: "\<not> NFS tp \<or> set ?Q = {}" by auto
  from ok have dpp: "dpp = ?dpp" by auto
  interpret dpp: dpp_spec J by fact
  from inf[unfolded dpp]
  have inf: "infinite_dpp (False,set P, set ?Q, set ?R)"
   by simp
  have "\<not> SN (qrstep False (set (Q tp)) (set (rules tp)))"
    using check_dps_sound[OF ok_dps inf] by simp
  then show ?thesis using nfs by auto
qed
 
definition
  check_not_wwf_qtrs :: "('tp,'f::{compare_order,showl}, 'v::{compare_order,showl})tp_ops \<Rightarrow> 'tp \<Rightarrow> showsl check"
where
  "check_not_wwf_qtrs I tp \<equiv> do {
    check (tp_ops.Q I tp = [] \<or> \<not> tp_ops.nfs I tp) (showsl_lit (STR ''strategies and normal form substitutions problem''));
    check (\<not> isOK (check_wwf_qtrs (tp_ops.is_QNF I tp) (tp_ops.rules I tp))) (showsl_lit (STR ''The Q-TRS is well formed'') \<circ> showsl_nl)
  }"

lemma check_not_wwf_qtrs_sound:
  assumes "tp_spec I"
  assumes ok: "isOK (check_not_wwf_qtrs I tp)"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
proof -
  interpret tp_spec I by fact
  note ok = ok[unfolded check_not_wwf_qtrs_def]
  from ok have "\<not> wwf_qtrs (set (Q tp)) (set (rules tp))" by auto
  moreover have choice: "\<not> NFS tp \<or> set (Q tp) = {}" using ok by auto
  ultimately show ?thesis using SN_imp_wwf_qtrs[of False "set (Q tp)" "set (rules tp)"] by auto
qed

datatype ('f,'v)rule_removal_nonterm_dp_prf = Rule_removal_nonterm_dp_prf "('f, 'v) rules" "('f,'v)rules"

fun rule_removal_nonterm_dp :: "('dpp, 'f :: {compare_order,showl}, 'v :: {compare_order,showl}) dpp_ops \<Rightarrow> 'dpp \<Rightarrow> ('f, 'v)rule_removal_nonterm_dp_prf \<Rightarrow> showsl + 'dpp"
  where
  "rule_removal_nonterm_dp I dpp (Rule_removal_nonterm_dp_prf Prm Rrm) = (do {
    return (dpp_spec.delete_pairs_rules I dpp Prm Rrm)
  })"

lemma rule_removal_nonterm_dp: 
  assumes I: "dpp_spec I" 
  and ok: "rule_removal_nonterm_dp I dpp prf = return dpp'"
  and inf: "infinite_dpp (dpp_ops.nfs I dpp', set (dpp_ops.pairs I dpp'), set (dpp_ops.Q I dpp'), set (dpp_ops.rules I dpp'))"
  shows "infinite_dpp (dpp_ops.nfs I dpp, set (dpp_ops.pairs I dpp), set (dpp_ops.Q I dpp), set (dpp_ops.rules I dpp))"
proof -
  interpret dpp_spec I by fact
  obtain Prm Rrm where id: "prf = Rule_removal_nonterm_dp_prf Prm Rrm" by (cases "prf", auto)
  note ok = ok[unfolded id rule_removal_nonterm_dp.simps Let_def]  
  let ?P   = "pairs dpp"
  let ?Q   = "set (Q dpp)"
  let ?R   = "rules dpp"
  let ?P'  = "set ?P - set Prm"
  let ?R'  = "set ?R - set Rrm"
  let ?nfs    = "NFS dpp"
  let ?dpp = "delete_pairs_rules dpp Prm Rrm"
  from inf ok
  have "infinite_dpp (NFS ?dpp, set (dpp_ops.pairs I ?dpp), set (dpp_ops.Q I ?dpp), set (dpp_ops.rules I ?dpp))"
    by simp
  then have inf: "infinite_dpp (?nfs,?P', ?Q, ?R')" unfolding delete_simps .
  show ?thesis
    by (rule infinite_dpp_mono[OF _ _ _ _ inf], auto)
qed

datatype ('f,'v)rule_removal_nonterm_reltrs_prf = 
  Rule_removal_nonterm_reltrs_prf "('f,'v)rules" "('f,'v)rules"

fun rule_removal_nonterm_reltrs :: "('tp, 'f :: {compare_order,showl}, 'v :: {compare_order,showl}) tp_ops \<Rightarrow> 'tp \<Rightarrow> 
  ('f, 'v)rule_removal_nonterm_reltrs_prf \<Rightarrow> showsl + 'tp" where
  "rule_removal_nonterm_reltrs I tp (Rule_removal_nonterm_reltrs_prf Rrm Srm) = do {
    return (tp_ops.delete_R_Rw I tp Rrm Srm)
  }"

lemma rule_removal_nonterm_reltrs: 
  assumes I: "tp_spec I" 
  and ok: "rule_removal_nonterm_reltrs I tp prf = return tp'"
  and inf: "\<not> SN_qrel (tp_ops.nfs I tp', set (tp_ops.Q I tp'), set (tp_ops.R I tp'), set (tp_ops.Rw I tp'))"
    (is "\<not> ?SN'")
  shows "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))"
    (is "\<not> ?SN")
proof 
  obtain Rrm Srm where id: "prf = Rule_removal_nonterm_reltrs_prf Rrm Srm" by (cases "prf")
  assume SN: "?SN"
  interpret tp_spec I by fact
  note ok = ok[unfolded id rule_removal_nonterm_reltrs.simps Let_def]
  from ok have tp': "tp' = delete_R_Rw tp Rrm Srm" by auto
  then have nfs: "NFS tp' = NFS tp" by auto
  have "?SN'" unfolding nfs
    by (rule SN_qrel_mono[OF _ _ _ SN], unfold tp', auto)
  with inf show False by blast
qed

datatype ('f,'v)rule_removal_nonterm_trs_prf = Rule_removal_nonterm_trs_prf "('f,'v)rules"

fun rule_removal_nonterm_trs :: "('tp, 'f :: {compare_order,showl}, 'v :: {compare_order,showl}) tp_ops \<Rightarrow> 'tp \<Rightarrow> 
  ('f, 'v)rule_removal_nonterm_trs_prf \<Rightarrow> showsl + 'tp" where
  "rule_removal_nonterm_trs I tp (Rule_removal_nonterm_trs_prf Rrm) = (do {
    return (tp_spec.delete_rules I tp Rrm)
  })"

lemma rule_removal_nonterm_trs_id: assumes "tp_spec I" and ok: "rule_removal_nonterm_trs I tp prf = return tp'"
  shows "tp_ops.nfs I tp' = tp_ops.nfs I tp" 
  "set (tp_ops.Q I tp') = set (tp_ops.Q I tp)"
  "set (tp_ops.rules I tp') \<subseteq> set (tp_ops.rules I tp)"
proof -
  obtain Rrm where id: "prf = Rule_removal_nonterm_trs_prf Rrm" by (cases "prf")
  interpret tp_spec I by fact
  from ok[unfolded id rule_removal_nonterm_trs.simps Let_def]
  have tp': "tp' = delete_rules tp Rrm" by auto
  show "tp_ops.nfs I tp' = tp_ops.nfs I tp" 
  "set (tp_ops.Q I tp') = set (tp_ops.Q I tp)"
  "set (tp_ops.rules I tp') \<subseteq> set (tp_ops.rules I tp)" unfolding tp' by auto
qed

lemma rule_removal_nonterm_trs: 
  assumes I: "tp_spec I" 
  and ok: "rule_removal_nonterm_trs I tp R' = return tp'"
  and nSN: "\<not> SN (qrstep (tp_ops.nfs I tp') (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))" (is "\<not> SN ?tp'")
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))" (is "\<not> SN ?tp")
proof -
  note * = rule_removal_nonterm_trs_id[OF I ok]
  show ?thesis
  proof
    assume SN: "SN ?tp"
    have "SN ?tp'"
      by (rule SN_subset[OF SN], unfold *(1-2), rule qrstep_mono[OF *(3)], auto)
    with nSN show False by blast
  qed
qed

definition [code_unfold]: "rule_removal_nonterm_otrs = rule_removal_nonterm_trs"

lemma rule_removal_nonterm_otrs: 
  assumes I: "tp_spec I" 
  and ok: "rule_removal_nonterm_otrs I tp R' = return tp'"
  and nSN: "\<not> SN (ostep (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))" (is "\<not> SN ?tp'")
  shows "\<not> SN (ostep (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))" (is "\<not> SN ?tp")
proof -
  note ok = ok[unfolded rule_removal_nonterm_otrs_def]
  note * = rule_removal_nonterm_trs_id[OF I ok]
  show ?thesis
  proof
    assume SN: "SN ?tp"
    have "SN ?tp'"
      by (rule SN_subset[OF SN], unfold *(1-2), rule ostep_mono, insert *(3), auto)
    with nSN show False by blast
  qed
qed

datatype ('f,'v)q_increase_nonterm_dp_prf = Q_increase_nonterm_dp_prf "('f,'v)term list"

fun q_increase_nonterm_dp :: "('dpp, 'f, 'v) dpp_ops \<Rightarrow> 'dpp \<Rightarrow> ('f, 'v)q_increase_nonterm_dp_prf \<Rightarrow> showsl + 'dpp"  where
  "q_increase_nonterm_dp I dpp (Q_increase_nonterm_dp_prf Q') = (do {
    let P = dpp_ops.pairs I dpp;
    let R = dpp_ops.rules I dpp;
    let Q = dpp_ops.Q I dpp;
    let nfs  = dpp_ops.nfs I dpp;
    return (dpp_ops.mk I nfs False P [] (list_union Q Q') [] R)
  })"

lemma q_increase_nonterm_dp: 
  assumes I: "dpp_spec I" 
  and ok: "q_increase_nonterm_dp I dpp prf = return dpp'"
  and inf: "infinite_dpp (dpp_ops.nfs I dpp', set (dpp_ops.pairs I dpp'), set (dpp_ops.Q I dpp'), set (dpp_ops.rules I dpp'))"
  shows "infinite_dpp (dpp_ops.nfs I dpp, set (dpp_ops.pairs I dpp), set (dpp_ops.Q I dpp), set (dpp_ops.rules I dpp))"
proof -
  obtain Q' where id: "prf = Q_increase_nonterm_dp_prf Q'" by (cases "prf", auto)
  interpret dpp_spec I by fact
  note ok = ok[unfolded id q_increase_nonterm_dp.simps Let_def]
  from ok have dpp': "dpp' = mk (NFS dpp) False (pairs dpp) [] (list_union (Q dpp) Q') [] (rules dpp)" by auto
  show ?thesis
    by (rule infinite_dpp_mono[OF subset_refl subset_refl NF_anti_mono[OF rstep_mono]], insert inf dpp', auto)
qed

datatype ('f,'v)q_increase_nonterm_trs_prf = Q_increase_nonterm_trs_prf "('f,'v)term list"

fun q_increase_nonterm_trs :: "('tp, 'f :: {compare_order,showl}, 'v :: {compare_order,showl}) tp_ops \<Rightarrow> 'tp \<Rightarrow> ('f, 'v)q_increase_nonterm_trs_prf \<Rightarrow> showsl + 'tp" where
  "q_increase_nonterm_trs I dpp (Q_increase_nonterm_trs_prf Q') = (do {
    let R = tp_ops.rules I dpp;
    let Q = tp_ops.Q I dpp;
    let nfs  = tp_ops.nfs I dpp;
    return (tp_ops.mk I nfs (list_union Q Q') R [])
  })"

lemma q_increase_nonterm_trs: 
  assumes I: "tp_spec I" 
  and ok: "q_increase_nonterm_trs I tp prf = return tp'"
  and nSN: "\<not> SN (qrstep (tp_ops.nfs I tp') (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))" (is "\<not> SN ?tp'")
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))" (is "\<not> SN ?tp")
proof -
  obtain Q' where id: "prf = Q_increase_nonterm_trs_prf Q'" by (cases "prf") auto
  interpret tp_spec I by fact
  note ok = ok[unfolded id q_increase_nonterm_trs.simps Let_def]
  from ok have tp': "tp' = mk (NFS tp) (list_union (Q tp) Q') (rules tp) []" by auto
  then have rules: "set (rules tp') = set (rules tp)" "NFS tp' = NFS tp" by auto
  show ?thesis
  proof
    assume SN: "SN ?tp"
    have "SN ?tp'"
      by (rule SN_subset[OF SN], unfold rules, rule qrstep_NF_anti_mono, unfold tp', auto)
    with nSN show False by blast
  qed
qed



definition
  check_not_wf_reltrs :: "('tp,'f::{compare_order,showl}, 'v::{compare_order,showl})tp_ops \<Rightarrow> 'tp \<Rightarrow> showsl check"
where
  "check_not_wf_reltrs I tp \<equiv> do {
     check (tp_ops.Q_empty I tp) (showsl_lit (STR ''currently only empty Q is supported''));
     check (\<not> isOK (check_wf_reltrs (tp_ops.R I tp, tp_ops.Rw I tp))) (showsl_lit (STR ''The TRSs R and S are well formed'') \<circ> showsl_nl)
   }"

lemma check_not_wf_reltrs:
  assumes "tp_spec I"
  and check: "isOK (check_not_wf_reltrs I tp)"
  shows "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))"
proof -
  interpret tp_spec I by fact 
  note check = check[unfolded check_not_wf_reltrs_def]
  from check have "\<not> wf_reltrs (set (tp_ops.R I tp)) (set (tp_ops.Rw I tp))" and Q: "set (tp_ops.Q I tp) = {}" by auto
  with SN_rel_imp_wf_reltrs have "\<not> SN_rel (rstep (set (tp_ops.R I tp))) (rstep (set (tp_ops.Rw I tp)))" by blast
  then show ?thesis unfolding Q by auto  
qed

definition reltrs_as_trs :: "('tp, 'f, 'v ) tp_ops \<Rightarrow> 'tp \<Rightarrow> showsl + 'tp" where
  "reltrs_as_trs I tp \<equiv> do {
    let Q = tp_ops.Q I tp;
    let R = tp_ops.R I tp;
    let nfs = tp_ops.nfs I tp;
    let tp' = tp_ops.mk I nfs Q R [];
    return tp'
  }"

lemma reltrs_as_trs:
  assumes "tp_spec I"
  and tp': "reltrs_as_trs I tp = return tp'"
  and nSN: "\<not> SN (qrstep (tp_ops.nfs I tp') (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))" (is "\<not> ?SN'")
  shows "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))" (is "\<not> ?SN")
proof
  assume SN: "?SN"
  interpret tp_spec I by fact
  from tp'[unfolded reltrs_as_trs_def Let_def]
  have tp': "tp' = mk (NFS tp) (Q tp) (R tp) []" by auto
  then have nfs: "NFS tp' = NFS tp" "set (Q tp') = set (Q tp)" by auto
  have "?SN'" using SN_qrel_imp_SN_qrstep[OF SN] unfolding nfs
    by (rule SN_subset[OF _ qrstep_mono], unfold tp', auto)
  with nSN show False by blast
qed

end
