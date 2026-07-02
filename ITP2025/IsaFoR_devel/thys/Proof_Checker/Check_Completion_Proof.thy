(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Completion_Proof
  imports
    Check_Termination
    CR.Equational_Reasoning_Impl
begin

subsection \<open>Proving completion of TRSs\<close>

type_synonym ('f, 'v) conversion = "('f, 'v) equation \<times> ('f, 'v) term list"
type_synonym ('f, 'v) subsumption_proof = "('f, 'v) conversion list"

datatype ('f, 'l, 'v) completion_proof =
  SN_WCR_Eq
    "(('f, 'l) lab, 'v) join_info"
    "('f, 'l, 'v) trs_termination_proof"
    "(('f, 'l) lab, 'v) subsumption_proof"
    "(('f, 'l) lab, 'v) subsumption_proof option"

primrec
  check_completion_proof ::
    "bool \<Rightarrow> showsl \<Rightarrow>
     ('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
     ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
     (('f, label_type) lab, string) equation list \<Rightarrow>
     (('f, label_type) lab, string) rules \<Rightarrow>
     ('f, label_type, string) completion_proof \<Rightarrow>
     showsl check" 
where
  "check_completion_proof a i I J E R (SN_WCR_Eq joins_i prf conv1 conv2) = debug i (STR ''SN_WCR_Eq'') (do {
    let tp = tp_ops.mk I False [] R []; \<comment> \<open>FIXME: default value\<close>
    check_trs_termination_proof I J a (add_index i 1) tp prf
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below strong normalization + wcr\<newline>'') \<circ> s);
    check_subsumption_guided R E conv1
      <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error when showing that rewrite relation can be simulated by equations\<newline>'') \<circ> s);
    check_subsumption E R conv2
      <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error when showing that equations can be simulated by rewrite system\<newline>'') \<circ> s);
    check_critical_pairs R (critical_pairs_impl string_rename R R) joins_i
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving local confluence of \<newline>'') \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s)
  })"

primrec completion_assms :: "bool \<Rightarrow> ('f, 'l, 'v) completion_proof \<Rightarrow> (('f, 'l, 'v) assm) list"
  where
    "completion_assms a (SN_WCR_Eq _ p _ _) = sn_assms a p"

lemma check_completion_proof_with_assms_sound: 
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (completion_assms a prf). holds p"
    and ok: "isOK (check_completion_proof a i I J E R prf)"
  shows "completed_rewrite_system (set E) (set R)"
proof -
  interpret tp_spec I by fact
  from ok fin show ?thesis
  proof (induct "prf" arbitrary: i)
    case (SN_WCR_Eq joins_i prof c1 c2 i)
    from SN_WCR_Eq(1)
    have cp: "isOK (check_critical_pairs R (critical_pairs_impl string_rename R R) joins_i)"
      and ok: "isOK (check_trs_termination_proof I J a (add_index i 1) (mk False [] R []) prof)" 
      and ok1: "isOK (check_subsumption_guided R E c1)"
      and ok2: "isOK (check_subsumption E R c2)" by (auto simp: Let_def)
    from SN_WCR_Eq(2) have a: "\<forall>a\<in>set (sn_assms a prof). holds a" by auto
    from check_critical_pairs[OF cp] have WCR: "WCR (rstep (set R))" .
    from check_trs_termination_proof_with_assms[OF I J ok a] have SN: "SN (rstep (set R))" by simp
    show ?case
      by (rule completion_via_WCR_SN_simulation[OF check_subsumption_guided[OF ok1] check_subsumption[OF ok2]  WCR SN])
  qed
qed

lemma completion_assms_False[simp]: "completion_assms False prf = []"
  by (induct "prf") simp_all

lemma check_completion_proof_sound: 
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_completion_proof False i I J E R prf)"
  shows "completed_rewrite_system (set E) (set R)"
  by (rule check_completion_proof_with_assms_sound[OF I J _ ok], simp)

subsection \<open>approximated completion for equational disproof\<close>

datatype ('f, 'l, 'v) approx_completion_proof =
  SN_WCR_Subsumption
    "(('f, 'l) lab, 'v) join_info"
    "('f, 'l, 'v) trs_termination_proof"
    "(('f, 'l) lab, 'v) subsumption_proof option"

primrec
  check_approx_completion_proof ::
    "bool \<Rightarrow> showsl \<Rightarrow>
     ('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
     ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow> (('f, label_type) lab, string) equation list \<Rightarrow> (('f, label_type) lab, string) rules \<Rightarrow>
     ('f, label_type, string) approx_completion_proof \<Rightarrow>
     showsl check" 
where
  "check_approx_completion_proof a i I J E R (SN_WCR_Subsumption joins_i prf conv') = debug i (STR ''SN_WCR_Subsumption'') (do {
    let tp = tp_ops.mk I False [] R []; \<comment> \<open>FIXME: default value\<close>
    check_trs_termination_proof I J a (add_index i 1) tp prf
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below strong normalization + wcr\<newline>'') \<circ> s);
    check_subsumption E R conv'
      <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error when showing that equations can be simulated by rewrite system\<newline>'') \<circ> s);
    check_critical_pairs R (critical_pairs_impl string_rename R R) joins_i
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving local confluence of \<newline>'') \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s)
  })"

primrec approx_completion_assms :: "bool \<Rightarrow> ('f, 'l, 'v) approx_completion_proof \<Rightarrow> (('f, 'l, 'v) assm) list"
  where
    "approx_completion_assms a (SN_WCR_Subsumption _ p _) = sn_assms a p"

(* TODO: move to Equational_Reasoning.thy *)
definition
  approx_completed_rewrite_system :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "approx_completed_rewrite_system E R \<equiv> subsumes R E \<and> CR (rstep R) \<and> SN (rstep R)"

lemma approx_completion_via_WCR_SN_simulation:
  assumes 1: "subsumes R E"
    and 2: "WCR (rstep R)"
    and 3: "SN (rstep R)"
  shows "approx_completed_rewrite_system E R"
  unfolding approx_completed_rewrite_system_def 
  using Newman[OF 3 2] 1 3 by blast

lemma approx_completion_assms_False[simp]: "approx_completion_assms False prf = []"
  by (induct "prf") simp_all

lemma check_approx_completion_proof_with_assms_sound: 
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (approx_completion_assms a prf). holds p"
    and ok: "isOK (check_approx_completion_proof a i I J E R prf)"
  shows "approx_completed_rewrite_system (set E) (set R)"
proof -
  interpret tp_spec I by fact
  from ok fin show ?thesis
  proof (induct "prf" arbitrary: i)
    case (SN_WCR_Subsumption joins_i prof c i)
    from SN_WCR_Subsumption(1)
    have cp: "isOK (check_critical_pairs R (critical_pairs_impl string_rename R R) joins_i)"
      and ok: "isOK (check_trs_termination_proof I J a (add_index i 1) (mk False [] R []) prof)" 
      and ok2: "isOK (check_subsumption E R c)" by (auto simp: Let_def)
    from SN_WCR_Subsumption(2) have a: "\<forall>a\<in>set (sn_assms a prof). holds a" by auto
    from check_critical_pairs[OF cp] have WCR: "WCR (rstep (set R))" .
    from check_trs_termination_proof_with_assms[OF I J ok a] have SN: "SN (rstep (set R))" by simp
    show ?case
      by (rule approx_completion_via_WCR_SN_simulation[OF check_subsumption[OF ok2]  WCR SN])
  qed
qed

end
