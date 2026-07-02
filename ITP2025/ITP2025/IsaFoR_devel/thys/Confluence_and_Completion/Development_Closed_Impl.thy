(*
Author:  Christina Kohl <christina.kohl@uibk.ac.at> (2023)
License: LGPL (see file COPYING.LESSER)
*)

text\<open>Check functions for confluence and commutation via development closed critical pairs.
Analogous to Parallel_Closed_Impl.thy\<close>

theory Development_Closed_Impl
imports
  Development_Closed
  Critical_Pairs_Impl
  Check_Joins
  Commutation
begin

context 
  fixes ren :: "'v :: {showl,infinite} renaming2" 
begin

definition check_development_closed where
  "check_development_closed R n = do {
     check_wf_trs R;
     check_left_linear_trs R;
     check_allm (\<lambda> (b, s, t). do {
       if b then check (is_mstep_join R R n s t)
         (showsl_lit (STR ''the critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' <- . -> '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not almost development closed within '') \<circ> showsl n \<circ> showsl_lit (STR '' steps.''))
       else check ((s,t) \<in> mstep (set R))
         (showsl_lit (STR ''the inner critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' S<- . ->R '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not closed with a multi-step over R'') \<circ> showsl n)
     }) (critical_pairs_impl ren R R)
     }  <+? (\<lambda>s. s \<circ> showsl_lit (STR ''\<newline>hence the following TRS is not development closed\<newline>'') \<circ> showsl_trs R)"


lemma check_development_closed:
  assumes "isOK(check_development_closed R n)"
  shows "CR (rstep (set R))"
proof (intro mstep_closed_imp_CR)
  note assms = assms[unfolded check_development_closed_def, simplified, unfolded wf_trs_def']
  from assms have "\<And>l r. (l, r) \<in> set R \<Longrightarrow> is_Fun l" by auto
  moreover from assms have "\<And>l r. (l, r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l" by auto 
  moreover from assms have "left_linear_trs (set R)" by auto
  ultimately show "left_lin_wf_trs (set R)" 
    unfolding left_lin_wf_trs_def left_lin_def wf_trs_def no_var_lhs_def var_rhs_subset_lhs_def by blast
  from assms show "\<And>s t. (True, s, t) \<in> critical_pairs ren (set R) (set R) \<Longrightarrow> \<exists>v. (s, v) \<in> mstep (set R) \<and> (t, v) \<in> (rstep (set R))\<^sup>*" 
    using is_mstep_join by fastforce
  from assms show "\<And>s t. (False, s, t) \<in> critical_pairs ren (set R) (set R) \<Longrightarrow> (s,t) \<in> mstep (set R)"
    by fastforce
qed

definition check_development_closed_comm where
  "check_development_closed_comm R S n = do {
     check_wf_trs R;
     check_wf_trs S;
     check_left_linear_trs R;
     check_left_linear_trs S;
     check_allm (\<lambda> (b, s, t). do {
       check (is_mstep_join S R n s t)
         (showsl_lit (STR ''the critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' R<- . ->S '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not almost development closed within '') \<circ> showsl n \<circ> showsl_lit (STR '' steps.''))
     }) (critical_pairs_impl ren S R);
     check_allm (\<lambda> (b, s, t). do {
       check (b \<or> (s,t) \<in> mstep (set R))
         (showsl_lit (STR ''the inner critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' S<- . ->R '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not closed with multi-step over R'') \<circ> showsl n)
     }) (critical_pairs_impl ren R S)
     }  <+? (\<lambda>s. s \<circ> showsl_lit (STR ''\<newline>hence the almost development closed check for the following TRSs could not be proven\<newline>R: '') \<circ> 
        showsl_trs R o showsl_lit (STR ''\<newline>\<newline>S: '') o showsl_trs S)"

lemma check_development_closed_comm:
  assumes "isOK(check_development_closed_comm R S n)"
  shows "sig_commute F (set R) (set S)"
proof (intro commute_imp_sig_commute mstep_closed_imp_commute)
  note assms = assms[unfolded check_development_closed_comm_def, simplified, unfolded wf_trs_def']
  from assms have "\<And>l r. (l, r) \<in> set R \<Longrightarrow> is_Fun l" by auto
  moreover from assms have "\<And>l r. (l, r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l" by auto 
  moreover from assms have "left_linear_trs (set R)" by auto
  ultimately show "left_lin_wf_trs (set R)" 
    unfolding left_lin_wf_trs_def left_lin_def wf_trs_def no_var_lhs_def var_rhs_subset_lhs_def by blast
  from assms have "\<And>l r. (l, r) \<in> set S \<Longrightarrow> is_Fun l" by auto
  moreover from assms have "\<And>l r. (l, r) \<in> set S \<Longrightarrow> vars_term r \<subseteq> vars_term l" by auto 
  moreover from assms have "left_linear_trs (set S)" by auto
  ultimately show "left_lin_wf_trs (set S)" 
    unfolding left_lin_wf_trs_def left_lin_def wf_trs_def no_var_lhs_def var_rhs_subset_lhs_def by blast
  from assms show "(b, p, q) \<in> critical_pairs ren (set S) (set R) \<Longrightarrow> \<exists>v. (p, v) \<in> mstep (set S) \<and> (q, v) \<in> (rstep (set R))\<^sup>*" for b p q
    by force
  from assms show "\<And>p q. (False, p, q) \<in> critical_pairs ren (set R) (set S) \<Longrightarrow> (p,q) \<in> mstep (set R)"
    by force
qed

end
end
