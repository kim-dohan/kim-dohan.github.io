text\<open>Okui Subsumes Development Closedness\<close>

theory Okui_subsumes_DC
imports
  Development_Closed_Impl
  Okui_Criterion
begin

text\<open>Introduce definition to abbreviate Okui's criterion.\<close>
definition
  "sim_cp_closed ren R \<longleftrightarrow> left_lin_wf_trs R \<and> 
  (\<forall>A B. (A, B) \<in> ren.sim_cp ren R \<longrightarrow> (\<exists>v. (target A, v) \<in> (rstep R)\<^sup>* \<and> (target B, v) \<in> mstep R))"

text\<open>Use definition from above to show confluence.\<close>
lemma sim_cp_closed:
  assumes "sim_cp_closed renN R" 
  shows "CR (rstep R)" 
  using assms okui_imp_CR unfolding sim_cp_closed_def by auto

text\<open>Any TRS that passes the check for development closedness fulfills all requirements for Okui's 
criterion\<close>
lemma dc_imp_sim_cp_closed:
  assumes "isOK(check_development_closed ren2 R n)" 
  shows "sim_cp_closed renN (set R)" 
proof-
  note assms = assms[unfolded check_development_closed_def, simplified, unfolded wf_trs_def']
  from assms have "\<And>l r. (l, r) \<in> set R \<Longrightarrow> is_Fun l" by auto
  moreover from assms have "\<And>l r. (l, r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l" by auto 
  moreover from assms have "left_linear_trs (set R)" by auto
  ultimately have wf_trs:"left_lin_wf_trs (set R)" 
    unfolding left_lin_wf_trs_def left_lin_def wf_trs_def no_var_lhs_def var_rhs_subset_lhs_def by blast
  moreover from assms have "\<And>s t. (True, s, t) \<in> critical_pairs ren2 (set R) (set R) \<Longrightarrow> \<exists>v. (s, v) \<in> mstep (set R) \<and> (t, v) \<in> (rstep (set R))\<^sup>*" 
    using is_mstep_join by fastforce
  moreover from assms have "\<And>s t. (False, s, t) \<in> critical_pairs ren2 (set R) (set R) \<Longrightarrow> (s,t) \<in> mstep (set R)"
    by fastforce
  ultimately have *:"strongly_commute (mstep (set R)) (mstep (set R))" 
    using mstep_closed_strongly_commute by (metis (full_types) mstep_imp_rsteps mstep_refl) 
  {fix A B assume sim_cp:"(A, B) \<in> ren.sim_cp renN (set R)" 
    from sim_cp have src:"source A = source B"
      using wf_trs ren_wf_trs.intro ren_wf_trs.sim_cp_co_init by blast
    from sim_cp have "A \<in> wf_pterm (set R)" and "B \<in> wf_pterm (set R)" 
      unfolding ren.sim_cp_def by fastforce+
    then have "(source A, target A) \<in> mstep (set R)" and "(source B, target B) \<in> mstep (set R)"
      by (simp add: pterm_to_mstep)+
    with * src obtain v where 1:"(target A, v) \<in> (mstep (set R))\<^sup>*" and 2:"(target B, v) \<in> (mstep (set R))\<^sup>=" 
      unfolding strongly_commute_def by metis  
    from 1 have "(target A, v) \<in> (rstep (set R))\<^sup>*"
      by (meson in_mono mstep_rsteps_subset rtrancl_subset_rtrancl) 
    with 2 have "\<exists>v. (target A, v) \<in> (rstep (set R))\<^sup>* \<and> (target B, v) \<in> mstep (set R)"
      by force
  }
  with wf_trs show ?thesis unfolding sim_cp_closed_def by simp
qed

end