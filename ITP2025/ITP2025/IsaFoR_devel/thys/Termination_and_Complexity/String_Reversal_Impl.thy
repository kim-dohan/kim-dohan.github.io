(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory String_Reversal_Impl
imports
  First_Order_Rewriting.Trs_Impl
  Not_SN.String_Reversal
  Framework.QDP_Framework_Impl
  Not_SN.Nontermination
  Defaults
begin

definition
  check_unary_signature :: "('f:: showl, 'v:: showl) rules \<Rightarrow> showsl check"
where
  "check_unary_signature R \<equiv>
     check_all (\<lambda>(l, r). unary_term l \<and> unary_term r) R
       <+? (\<lambda>r. showsl_lit (STR ''the rule\<newline>'') \<circ> showsl_rule r 
          \<circ> showsl_lit (STR ''\<newline>violates the condition that all function symbols\<newline>have to be unary''))"
  
lemma check_unary_signature_sound[simp]: "isOK(check_unary_signature R) = unary_sig (funas_trs (set R))" (is "_ = ?r")
proof -
  have "(\<forall> x \<in> set R. (\<lambda>(l,r). unary_term l \<and> unary_term r) x) = ?r" (is "?l = _")
  proof
    assume ?l
    show ?r unfolding unary_sig_def funas_trs_def funas_rule_def [abs_def]
    proof (rule ballI2)
      fix f i
      assume "(f,i) \<in> (\<Union>r \<in> set R. funas_term (fst r) \<union> funas_term (snd r))"
      then obtain r where r: "r \<in> set R" and lr: "(f,i) \<in> funas_term (fst r) \<union> funas_term (snd r)" by auto
      from lr show "i = 1"
      proof
        assume "(f,i) \<in> funas_term (fst r)"
        then show "i = 1" using \<open>?l\<close> unary_funas_conv[of "fst r" f i] r by auto
      next
        assume "(f,i) \<in> funas_term (snd r)"
        then show "i = 1" using \<open>?l\<close> unary_funas_conv[of "snd r" f i] r by auto
      qed
    qed
  next
    assume ?r
    show ?l (is "\<forall> x \<in> set R. ?P x")
    proof
      fix l r
      assume lr: "(l, r) \<in> set R"
      with \<open>?r\<close> lr have l: "\<forall> (f,i) \<in> funas_term l. i = 1" and r: "\<forall> (f,i) \<in> funas_term r. i = 1"
        unfolding unary_sig_def funas_trs_def funas_rule_def [abs_def] by auto
      show "unary_term l \<and> unary_term r" using funas_unary_conv[OF l] funas_unary_conv[OF r] ..
    qed
  qed
  then show ?thesis
   by (auto simp: check_unary_signature_def)
qed

definition
  string_reversal_tt :: "('tp, 'f:: showl, 'v:: showl) tp_ops \<Rightarrow> 'tp proc"
where
  "string_reversal_tt I trs \<equiv> (let
    rs = tp_ops.rules I trs;
    r  = tp_ops.R I trs;
    s  = tp_ops.Rw I trs
  in check_return (do {
     check_unary_signature rs
  }) (tp_ops.mk I default_nfs_trs [] (map rev_rule r) (map rev_rule s)))"

context tp_spec
begin
lemma string_reversal_tt:
  "sound_tt_impl (string_reversal_tt I)"
proof 
  fix tp tp'
  assume ok: "string_reversal_tt I tp = return tp'"
    and fin: "SN_qrel (qreltrs tp')"
  let ?Q = "set (Q tp)"
  let ?R = "set (R tp)"
  let ?S = "set (Rw tp)"
  let ?RS = "?R \<union> ?S"
  from ok[unfolded string_reversal_tt_def Let_def, simplified]
  have unary: "unary_sig (funas_trs ?RS)" 
    and tp': "tp' = mk default_nfs_trs [] (map rev_rule (R tp)) (map rev_rule (Rw tp))" 
    by auto
  from fin have "SN_qrel (False, {}, rev_trs ?R, rev_trs ?S)" unfolding tp'
    unfolding mk_sound
    by (auto simp: rev_trs_def)
  from string_reversal_qrstep_SN_rel[OF unary this]
  show "SN_qrel (qreltrs tp)"
    unfolding qreltrs_sound .
qed
end

definition "string_reversal_complete_tt I tp \<equiv> do {
    let R = tp_ops.rules I tp;
    check (tp_ops.Q_empty I tp) (showsl_lit (STR ''Q is not empty''));
    check_unary_signature R;
    return (tp_ops.mk I default_nfs_nt_trs [] (map rev_rule R) [])
  }"

lemma string_reversal_complete_tt:
  assumes I: "tp_spec I" 
  and ok: "string_reversal_complete_tt I tp = return tp'"
  and nSN: "\<not> SN (qrstep (tp_ops.nfs I tp') (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))" (is "\<not> SN ?tp'")
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))" (is "\<not> SN ?tp")
proof -
  interpret tp_spec I by fact
  note ok = ok[unfolded string_reversal_complete_tt_def Let_def, simplified]
  let ?R = "set (rules tp)"
  let ?tp' = "mk False [] (map rev_rule (tp_ops.rules I tp)) []"
  from ok have Q: "set (Q tp) = {}" by simp
  from ok have sig: "unary_sig (funas_trs ?R)" by simp
  from ok have tp': "tp' = tp_ops.mk I default_nfs_nt_trs [] (map rev_rule (rules tp)) []" by simp
  have rev: "set (rules ?tp') = rev_trs ?R" unfolding tp'
    by (auto simp: rev_trs_def)
  from string_reversal[OF sig] Q rev nSN show ?thesis unfolding tp' by auto
qed

definition "string_reversal_complete_rel_tt I tp \<equiv> do {
    check (tp_ops.Q_empty I tp) (showsl_lit (STR ''Q is not empty''));
    check_unary_signature (tp_ops.rules I tp);
    return (tp_ops.mk I default_nfs_nt_trs [] (map rev_rule (tp_ops.R I tp)) (map rev_rule (tp_ops.Rw I tp)))
  }"

lemma string_reversal_complete_rel_tt:
  assumes I: "tp_spec I" 
  and ok: "string_reversal_complete_rel_tt I tp = return tp'"
  and nSN: "\<not> SN_qrel (tp_ops.nfs I tp', set (tp_ops.Q I tp'), set (tp_ops.R I tp'), set (tp_ops.Rw I tp'))" (is "\<not> SN_qrel ?tp'")
  shows "\<not> SN_qrel (tp_ops.nfs I tp, set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp))" (is "\<not> SN_qrel ?tp")
proof 
  assume SN: "SN_qrel ?tp"
  interpret tp_spec I by fact
  note ok = ok[unfolded string_reversal_complete_rel_tt_def Let_def, simplified]
  let ?R = "set (R tp) \<union> set (Rw tp)"
  from ok have Q: "set (Q tp) = {}" by simp
  from ok have sig: "unary_sig (funas_trs ?R)" by simp
  from ok have tp': "tp' = tp_ops.mk I default_nfs_nt_trs [] (map rev_rule (R tp)) (map rev_rule (Rw tp))" by simp
  from SN[unfolded Q] have "SN_rel (rstep (set (R tp))) (rstep (set (Rw tp)))" by auto
  from this[folded string_reversal_SN_rel[OF sig]] have "SN_rel (rstep (rev_trs (set (R tp)))) (rstep (rev_trs (set (Rw tp))))" .
  also have "rev_trs (set (R tp)) = set (R tp')" unfolding tp' by (auto simp: rev_trs_def)
  also have "rev_trs (set (Rw tp)) = set (Rw tp')" unfolding tp' by (auto simp: rev_trs_def)
  finally have SN: "SN_rel (rstep (set (R tp'))) (rstep (set (Rw tp')))" .
  have "SN_qrel ?tp'" unfolding SN_qrel_def split
    by (rule SN_rel_mono[OF _ _ SN], auto)
  with nSN show False ..
qed

end

