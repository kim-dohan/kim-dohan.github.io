theory Tcap_Dpp_Impl
  imports 
    TRS.Tcap_Impl
    Framework.Dependency_Pair_Problem_Spec
    Framework.AC_Dependency_Pair_Problem_Spec
begin

definition
  tcapRM_dpp ::
    "('dpp, 'f, 'v) dpp_ops \<Rightarrow> 'dpp \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, 'v) gctxt"
where
  "tcapRM_dpp I dpp = tcapRM (dpp_ops.rules_no_left_var I dpp) (dpp_ops.rules_map I dpp)"

definition
  tcapRM_ac_dpp ::
    "('dpp, 'f, 'v) ac_dpp_ops \<Rightarrow> 'dpp \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, 'v) gctxt"
where
  "tcapRM_ac_dpp I dpp = tcapRM (ac_dpp_ops.eq_rules_no_left_var I dpp) (ac_dpp_ops.eq_rules_map I dpp)"

definition
  reverse_tcapRM_dpp ::
    "('dpp, 'f, 'v) dpp_ops \<Rightarrow> 'dpp \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, 'v) gctxt"
where
  "reverse_tcapRM_dpp I dpp =
    tcapRM (dpp_ops.rules_non_collapsing I dpp) (dpp_ops.reverse_rules_map I dpp)"

definition
  reverse_tcapRM_ac_dpp ::
    "('dpp, 'f, 'v) ac_dpp_ops \<Rightarrow> 'dpp \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, 'v) gctxt"
where
  "reverse_tcapRM_ac_dpp I dpp =
    tcapRM (ac_dpp_ops.eq_rules_non_collapsing I dpp) (ac_dpp_ops.reverse_eq_rules_map I dpp)"

context dpp_spec
begin

lemma tcapRM_dpp[simp]:   
  shows "tcapRM_dpp I d = tcap (set (rules d))"
  unfolding tcapRM_dpp_def
  by (rule tcapRM, insert rules_no_left_var_sound rules_map_sound, force+)

lemma reverse_tcapRM_dpp[simp]:   
  shows "reverse_tcapRM_dpp I d = tcap ((set (rules d))^-1)"
  unfolding reverse_tcapRM_dpp_def reverse_rules[symmetric]
  by (rule tcapRM, unfold reverse_rules_def,
      unfold rules_non_collapsing_sound reverse_rules_map_sound, force+)
end

context ac_dpp_spec
begin
lemma tcapRM_ac_dpp[simp]:   
  shows "tcapRM_ac_dpp I d = tcap (set (R d @ Rw d @ E d))"
  unfolding tcapRM_ac_dpp_def
  by (rule tcapRM, insert eq_rules_no_left_var_sound eq_rules_map_sound, force+)

lemma reverse_tcapRM_ac_dpp[simp]:   
  shows "reverse_tcapRM_ac_dpp I d = tcap ((set (R d @ Rw d @ E d))^-1)"
proof -
  obtain r where r: "R d @ Rw d @ E d = r" by blast
  show ?thesis
  unfolding reverse_tcapRM_ac_dpp_def reverse_rules[symmetric]
  by (rule tcapRM, unfold reverse_rules_def,
      unfold eq_rules_non_collapsing_sound reverse_eq_rules_map_sound r)
    force+
qed
end


end
