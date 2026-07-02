(* author: René Thiemann *)

theory Right_Ground_Termination_Impl
  imports
    Right_Ground_Termination
    Framework.QDP_Framework_Impl
    TRS.Q_Restricted_Rewriting_Impl
begin

definition check_right_ground :: "('f :: showl, 'v :: showl) rules \<Rightarrow> showsl check" where
  "check_right_ground = check_allm ( \<lambda> (l,r). 
      check (ground r) (showsl_rule (l,r) o showsl (STR '' is not right ground'')))" 

lemma check_right_ground[simp]: "isOK(check_right_ground R) = (right_ground_TRS (set R))" 
  unfolding check_right_ground_def right_ground_TRS_def by force
 
definition
  right_ground_tt ::
    "('tp, 'f :: showl, 'v :: showl) tp_ops \<Rightarrow> 'tp
    \<Rightarrow> showsl check"
where
  "right_ground_tt I tp \<equiv>
     let R = tp_ops.rules I tp; nfs = tp_ops.nfs I tp; qnf = tp_ops.is_QNF I tp in 
      do {
         check_right_ground R;
         check (right_ground_termination (qrewrite nfs qnf R) R) (showsl (STR ''TRS is not terminating'')) 
      }" 

definition
  right_ground_nonterm ::
    "('tp, 'f :: showl, 'v :: showl) tp_ops \<Rightarrow> 'tp
    \<Rightarrow> showsl check"
where
  "right_ground_nonterm I tp \<equiv>
     let R = tp_ops.rules I tp; nfs = tp_ops.nfs I tp; qnf = tp_ops.is_QNF I tp in 
      do {
         check_right_ground R;
         check (\<not> right_ground_termination (qrewrite nfs qnf R) R) (showsl (STR ''TRS is terminating'')) 
      }" 

context tp_spec
begin
lemma right_ground_tt: assumes s: "isOK(right_ground_tt I tp)"
  shows "SN_qrel (qreltrs tp)"
proof -
  from s[unfolded right_ground_tt_def Let_def]
  have dp: "right_ground_termination (qrewrite (NFS tp) (is_QNF tp) (rules tp)) (rules tp)" and 
    rg: "right_ground_TRS (set (rules tp))" 
    by auto
  have "right_ground_termination (qrewrite (NFS tp) (is_QNF tp) (rules tp)) (rules tp) 
    = SN (qrstep (NFS tp) (set (Q tp)) (set (rules tp)))" 
  proof (rule right_ground_termination[OF rg qrewrite])
    fix l r
    assume "(l,r) \<in> set (rules tp)" 
    hence "ground r" using rg unfolding right_ground_TRS_def by force
    thus "vars_term r \<subseteq> vars_term l" by (simp add: ground_vars_term_empty)
  qed auto
  hence SN: "SN (qrstep (NFS tp) (set (Q tp)) (set (rules tp)))" using dp by auto
  show "SN_qrel (qreltrs tp)" unfolding qreltrs_sound
    apply (rule SN_qrel_split[where D = "set (rules tp)"])
    subgoal using SN SN_subset[OF _ qrstep_subset_rstep] by auto
    subgoal by (auto simp: SN_qrel_def SN_rel_defs)
    done
qed

lemma right_ground_nonterm: assumes s: "isOK(right_ground_nonterm I tp)"
  shows "\<not> SN (qrstep (NFS tp) (set (Q tp)) (set (rules tp)))"
proof -
  from s[unfolded right_ground_nonterm_def Let_def]
  have dp: "\<not> right_ground_termination (qrewrite (NFS tp) (is_QNF tp) (rules tp)) (rules tp)" and 
    rg: "right_ground_TRS (set (rules tp))" 
    by auto
  have "right_ground_termination (qrewrite (NFS tp) (is_QNF tp) (rules tp)) (rules tp) 
    = SN (qrstep (NFS tp) (set (Q tp)) (set (rules tp)))" 
  proof (rule right_ground_termination[OF rg qrewrite])
    fix l r
    assume "(l,r) \<in> set (rules tp)" 
    hence "ground r" using rg unfolding right_ground_TRS_def by force
    thus "vars_term r \<subseteq> vars_term l" by (simp add: ground_vars_term_empty)
  qed auto
  thus ?thesis using dp by auto
qed

end

end