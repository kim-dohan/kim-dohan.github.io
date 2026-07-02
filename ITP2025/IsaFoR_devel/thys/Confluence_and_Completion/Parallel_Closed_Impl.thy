(*
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2015-2017)
         René Thiemann <rene.thiemann@uibk.ac.at> (2022-2023)
License: LGPL (see file COPYING.LESSER)
*)

theory Parallel_Closed_Impl
imports
  Parallel_Closed
  Critical_Pair_Closure_Impl
  Commutation
  Check_Joins
begin

context 
  fixes ren :: "'v :: {showl,infinite} renaming2" 
begin
definition check_parallel_closed where
  "check_parallel_closed R n = do {
     check_left_linear_trs R;
     check_allm (\<lambda> (b, s, t). do {
       if b then  check (is_par_rsteps_join R R n s t)
         (showsl_lit (STR ''the critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' <- . -> '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not almost parallel closed within '') \<circ> showsl n \<circ> showsl_lit (STR '' steps.''))
       else check ((s,t) \<in> par_rstep (set R))
         (showsl_lit (STR ''the inner critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' S<- . ->R '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not closed with a parallel step over R'') \<circ> showsl n)
     }) (critical_pairs_impl ren R R)
     }  <+? (\<lambda>s. s \<circ> showsl_lit (STR ''\<newline>hence the following TRS is not (almost) parallel closed\<newline>'') \<circ> showsl_trs R)"

lemma check_parallel_closed:
  assumes "isOK(check_parallel_closed R n)"
  shows "CR (rstep (set R))"
proof (intro parallel_closed_imp_CR)
  note assms = assms[unfolded check_parallel_closed_def, simplified, unfolded wf_trs_def']
  from assms show "left_linear_trs (set R)" by auto
  from assms show "\<And>s t. (True, s, t) \<in> critical_pairs ren (set R) (set R) \<Longrightarrow> \<exists>v. (s, v) \<in> par_rstep (set R) \<and> (t, v) \<in> (rstep (set R))\<^sup>*" 
    using is_mstep_join by fastforce
  from assms show "\<And>s t. (False, s, t) \<in> critical_pairs ren (set R) (set R) \<Longrightarrow> (s,t) \<in> par_rstep (set R)"
    by fastforce
qed

definition check_parallel_closed_comm where
  "check_parallel_closed_comm R S n = do {
     check_left_linear_trs R;
     check_left_linear_trs S;
     check_allm (\<lambda> (b, s, t). do {
       check (is_par_rsteps_join S R n s t)
         (showsl_lit (STR ''the critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' R<- . ->S '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not almost parallel closed within '') \<circ> showsl n \<circ> showsl_lit (STR '' steps.''))
     }) (critical_pairs_impl ren S R);
     check_allm (\<lambda> (b, s, t). do {
       check (b \<or> (s,t) \<in> par_rstep (set R))
         (showsl_lit (STR ''the inner critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' S<- . ->R '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not closed with parallel R step'') \<circ> showsl n)
     }) (critical_pairs_impl ren R S)
     }  <+? (\<lambda>s. s \<circ> showsl_lit (STR ''\<newline>hence the almost parallel closed check for the following TRSs could not be proven\<newline>R: '') \<circ> 
        showsl_trs R o showsl_lit (STR ''\<newline>\<newline>S: '') o showsl_trs S)"

lemma check_parallel_closed_comm:
  assumes "isOK(check_parallel_closed_comm R S n)"
  shows "sig_commute F (set R) (set S)"
proof (intro commute_imp_sig_commute parallel_closed_commute is_par_rsteps_join[of _ _ n])
  note assms = assms[unfolded check_parallel_closed_comm_def, simplified]
  from assms show "left_linear_trs (set R)" "left_linear_trs (set S)" by auto
  from assms show "(b, p, q) \<in> critical_pairs ren (set S) (set R) \<Longrightarrow> is_par_rsteps_join S R n p q" for b p q
    by force
  from assms show "\<And>p q. (False, p, q) \<in> critical_pairs ren (set R) (set S) \<Longrightarrow> (p,q) \<in> par_rstep (set R)" 
    by force
qed

end
end