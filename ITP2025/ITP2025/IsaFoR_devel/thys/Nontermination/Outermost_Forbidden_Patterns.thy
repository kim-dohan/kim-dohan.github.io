(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Outermost_Forbidden_Patterns
imports 
  TRS.Outermost_Rewriting
  TRS.Forbidden_Patterns
  TRS.Q_Restricted_Rewriting
begin

definition o_to_fp_term :: "('f,'v)term \<Rightarrow> ('f,'v) forb_pattern" where
  "o_to_fp_term t = (Hole, t, Forbidden_Patterns.B)"

definition o_to_fp :: "('f,'v)terms \<Rightarrow> ('f,'v) forb_patterns" where
  "o_to_fp Q = o_to_fp_term ` Q"

definition o_to_fp_impl :: "('f,'v)term list \<Rightarrow> ('f,'v) forb_pattern list" where
  "o_to_fp_impl = map o_to_fp_term"

lemma o_to_fp_impl[simp]: "set (o_to_fp_impl Q) = o_to_fp (set Q)" 
  unfolding o_to_fp_impl_def o_to_fp_def by auto

lemma o_to_fp_term_single: assumes p: "p \<in> poss t"
  shows "ostep_cond_single q p t = fpstep_cond_single (o_to_fp_term q) p t"
proof -
  {
    fix \<sigma>
    have "(\<forall>qa. qa <\<^sub>p p \<longrightarrow> t |_ qa \<noteq> q \<cdot> \<sigma>) = (\<forall>C'. hole_pos C' <\<^sub>p p \<longrightarrow> (t \<noteq> C'\<langle>q \<cdot> \<sigma>\<rangle>) )" (is "?l = ?r")
    proof
      assume ?r
      show ?l
      proof (intro allI impI)
        fix p'
        assume p': "p' <\<^sub>p p"
        let ?C = "ctxt_of_pos_term p' t"
        from \<open>?r\<close>[THEN spec, of ?C] p' have "t \<noteq> (ctxt_of_pos_term p' t)\<langle>q \<cdot> \<sigma>\<rangle>"
          using less_pos_def' p by auto
        with p p'
        show "t |_ p' \<noteq> q \<cdot> \<sigma>"
          by (metis ctxt_supt_id less_pos_def replace_at_below_poss)
      qed
    next
      assume ?l
      show ?r
      proof (intro allI impI)
        fix C'
        show "hole_pos C' <\<^sub>p p \<Longrightarrow> t \<noteq> C'\<langle>q \<cdot> \<sigma>\<rangle>"
          using \<open>?l\<close>[rule_format, of "hole_pos C'"] by auto
      qed
    qed
  }
  then show ?thesis
    unfolding o_to_fp_term_def fpstep_cond_single_def ostep_cond_single_def split
    by auto
qed

lemma o_to_fp_cond: assumes p: "p \<in> poss t"
  shows "ostep_cond q p t = fpstep_cond (o_to_fp q) p t"
  using o_to_fp_term_single[OF p] unfolding ostep_cond_def fpstep_cond_def o_to_fp_def by auto


lemma o_to_fp_step_p: "ostep_p q r p = fpstep_p (o_to_fp q) r p"
  unfolding ostep_p_def fpstep_p_def rstep_r_p_s_def Let_def
  using o_to_fp_cond[of p _ q] by auto

lemma ostep_iff_fpstep: "ostep q = fpstep (o_to_fp q)"
  by (intro ext, simp add: o_to_fp_step_p ostep_def fpstep_def)

lemma ostep_iff_fpstep_impl: "ostep (set q) = fpstep (set (o_to_fp_impl q))"
  by (simp add: ostep_iff_fpstep)
end

