(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Quasi_Reductive
imports 
  Check_Termination
  CTRS.Unraveling_Impl
begin

subsection \<open>Proving that a conditional TRS is quasi reductive\<close>

datatype ('f, 'l, 'v) quasi_reductive_proof =
  Unravel 
    "((('f,'l)lab,'v)crule \<times> (('f,'l)lab,'v) rules) list"
    "('f, 'l, 'v) trs_termination_proof"

primrec
  check_quasi_reductive_proof ::
    "bool \<Rightarrow> showsl \<Rightarrow>
     ('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
     ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow> (('f,label_type)lab,string)crules \<Rightarrow> 
     ('f, label_type, string) quasi_reductive_proof \<Rightarrow>
     showsl check" 
where
  "check_quasi_reductive_proof a i I J ctrs (Unravel u_info prf) = debug i (STR ''Unravel'') (do {
    r \<leftarrow> check_unraveling u_info ctrs
      <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error in unraveling\<newline>'') \<circ> s);
    let tp = tp_ops.mk I False [] r [];
    check_trs_termination_proof I J a (i \<circ> showsl_lit (STR ''.1'')) tp prf
      <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below strong normalization + wcr\<newline>'') \<circ> s)
  })"

primrec quasi_reductive_assms :: "bool \<Rightarrow> ('f, 'l, 'v) quasi_reductive_proof \<Rightarrow> (('f, 'l, 'v) assm) list" where
  "quasi_reductive_assms a (Unravel _ p) = sn_assms a p"

lemma check_quasi_reductive_proof_with_assms_sound: 
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (quasi_reductive_assms a prf). holds p"
    and ok: "isOK (check_quasi_reductive_proof a i I J ctrs prf)"
  shows "quasi_reductive (set ctrs)"
proof -
  interpret tp_spec I by fact
  from ok fin show ?thesis
  proof (induct "prf" arbitrary: i)
    case (Unravel u_info prof)
    note check = Unravel(1)[simplified]
    from check obtain R where R: "check_unraveling u_info ctrs = return R" by (cases "check_unraveling u_info ctrs", auto)
    from check[unfolded R]
    have ok: "isOK (check_trs_termination_proof I J a (i \<circ> showsl_lit (STR ''.1'')) (mk False [] R []) prof)" by simp
    from Unravel(2) have a: "\<forall>a\<in>set (sn_assms a prof). holds a" by auto
    from check_trs_termination_proof_with_assms[OF I J ok a] have SN: "SN (rstep (set R))" by simp
    show ?case
      by (rule check_unraveling[OF R SN])
  qed
qed

lemma quasi_reductive_assms_False[simp]: "quasi_reductive_assms False prf = []"
  by (induct "prf") simp_all

lemma check_quasi_reductive_proof_sound: 
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_quasi_reductive_proof False i I J ctrs prf)"
  shows "quasi_reductive (set ctrs)"
  by (rule check_quasi_reductive_proof_with_assms_sound[OF I J _ ok], simp)

end
