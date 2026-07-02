(*
Author:  Julian Nagele 
*)
theory Strongly_Closed_Impl
imports
  Critical_Pairs_Impl
  Strongly_Closed
  First_Order_Rewriting.Rewrite_Relations_Impl
begin

definition check_strongly_closed where
  "check_strongly_closed ren R n = do {
     check_linear_trs R;
     check_allm (\<lambda> (b, s, t). do {
       check (\<not> Option.is_none (List.find (\<lambda>x. List.member (reachable_terms R s n) x) (reachable_terms R t (Suc 0))) \<and>
         \<not> Option.is_none (List.find (\<lambda>x. List.member (reachable_terms R t n) x) (reachable_terms R s (Suc 0))))
       (showsl_lit (STR ''the critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' <- . -> '') \<circ> showsl t \<circ>
        showsl_lit (STR '' is not strongly closed within '') \<circ> showsl n \<circ> showsl_lit (STR '' steps.''))
     }) (critical_pairs_impl ren R R)
     }  <+? (\<lambda>s. s \<circ> showsl_lit (STR ''\<newline>hence the following TRS is not strongly closed\<newline>'') \<circ> showsl_trs R)"

lemma check_strongly_closed:
  assumes "isOK(check_strongly_closed ren R n)"
  shows "CR (rstep (set R))"
proof (rule strongly_closed_linear_CR)
  from assms show "linear_trs (set R)" unfolding check_strongly_closed_def by auto
  let ?red = "\<lambda>s n. reachable_terms R s n"
  let ?opt = "\<lambda>s t. List.find (\<lambda>x. List.member (?red s n) x) (?red t (Suc 0))"
  { fix s t
    assume "\<not> Option.is_none (?opt s t)"
    then obtain r where r: "?opt s t = Some r" by (cases "?opt s t") auto
    then have "List.member (?red s n) r" unfolding find_Some_iff by auto
    then have mem:"r \<in> set (?red s n)" using in_set_member by fast
    from r have "\<exists>i<length (?red t (Suc 0)). r = (?red t (Suc 0)) ! i" unfolding find_Some_iff by auto
    then have "r \<in> set (?red t (Suc 0))" using nth_mem by blast
    with mem have "\<exists>r. (s, r) \<in> (rstep (set R))\<^sup>* \<and> (t, r) \<in> (rstep (set R))\<^sup>="
      using reachable_terms reachable_terms_one by metis
  } note sound=this
  { fix b s t
    assume "(b, s, t) \<in> critical_pairs ren (set R) (set R)"
    with assms have *:"\<not> Option.is_none (?opt s t) \<and> \<not> Option.is_none (?opt t s)"
      unfolding check_strongly_closed_def by fastforce
    with sound have "\<exists>r. (s, r) \<in> (rstep (set R))\<^sup>* \<and> (t, r) \<in> (rstep (set R))\<^sup>="
      and  "\<exists>u. (t, u) \<in> (rstep (set R))\<^sup>* \<and> (s, u) \<in> (rstep (set R))\<^sup>=" by blast+
  }
  then show "strongly_closed ren (set R)" unfolding strongly_closed_def by blast
qed

end
