(*
Author:  Christina Kohl <christina.kohl@uibk.ac.at> (2022)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2013-2017)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015, 2023)
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2023)

License: LGPL (see file COPYING.LESSER)
*)
theory Critical_Pair_Closure_Impl
imports
  Critical_Pairs_Impl
  Critical_Pair_Closing_Systems
  Framework.QDP_Framework_Impl
  First_Order_Rewriting.Rewrite_Relations_Impl
begin

fun is_critical_pair_closing_cp where
  "is_critical_pair_closing_cp C n (False, s, t) =
    (\<not> Option.is_none (List.find (\<lambda>v. (s,v) \<in> par_rstep (set C)) (reachable_terms C t n)))"
| "is_critical_pair_closing_cp C n (True, s, t) =
    (\<not> Option.is_none (List.find (\<lambda>x. List.member (reachable_terms C t n) x) (reachable_terms C s n)))"

definition check_critical_pair_closing :: "_ \<Rightarrow> ('f:: showl, _) rules \<Rightarrow> ('f, _) rules \<Rightarrow> nat \<Rightarrow> showsl check"
where
  "check_critical_pair_closing ren R C n = do {
     check_left_linear_trs R;
     check_subseteq C R <+? (\<lambda>t. showsl_lit (STR ''C not a subsystem of R''));
     check_allm (\<lambda> (b, s, t). do {
       check (is_critical_pair_closing_cp C n (b, s, t))
         (showsl_lit (STR ''the critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' <- . -> '') \<circ> showsl t \<circ>
          showsl_lit (STR '' is not closed within '') \<circ> showsl n \<circ> showsl_lit (STR '' steps.''))
     }) (critical_pairs_impl ren R R)
     }  <+? (\<lambda>s. s \<circ> showsl_lit (STR ''\<newline>hence the following TRS is not critical pair closing\<newline>'') \<circ> showsl_trs R)"

lemma check_critical_pair_closing:
  assumes "isOK(check_critical_pair_closing ren R C n)"
    "SN (rstep (set C))"
  shows "CR (rstep (set R))"
proof (rule cpcs_sn)
  from assms show "left_linear_trs (set R)" unfolding check_critical_pair_closing_def by auto
  from assms show "SN (rstep (set C))" ..
  from assms[unfolded check_critical_pair_closing_def,simplified]
  have closed:"\<And> b p q. (b, p, q) \<in> critical_pairs ren (set R) (set R) \<Longrightarrow> is_critical_pair_closing_cp C n (b, p, q)"
    by fast
  let ?find = "\<lambda> p v. (p,v) \<in> par_rstep (set C)" 
  show "critical_pair_closing ren (set C) (set R)" unfolding critical_pair_closing_def
  proof
    from assms show "set C \<subseteq> set R"  unfolding check_critical_pair_closing_def by auto
    { fix b p q
      assume cp:"(b, p, q) \<in> critical_pairs ren (set R) (set R)"
      have "(p, q) \<in> (rstep (set C))\<^sup>\<down>"
      proof (cases b)
        case True
        with closed[of b p q] cp
        have "\<not> Option.is_none (find (List.member (reachable_terms C q n)) (reachable_terms C p n))" by auto
        then obtain v where  "find (List.member (reachable_terms C q n)) (reachable_terms C p n) = Some v"
          by force
        then have "v \<in> set (reachable_terms C q n) \<and> v \<in> set (reachable_terms C p n)"
          unfolding find_Some_iff by (meson in_set_member nth_mem)
        then show ?thesis by (auto dest: reachable_terms)
      next
        case False
        with closed[of b p q] cp
        have "\<not> Option.is_none (find (?find p) (reachable_terms C q n))" by auto
        then obtain v where  "find (?find p) (reachable_terms C q n) = Some v"
          by force
        then have "(p,v) \<in> par_rstep (set C)" and "v \<in> set (reachable_terms C q n)"
          unfolding find_Some_iff by auto
        then show ?thesis using reachable_terms par_rstep_rsteps by blast
      qed
    }
    then show "\<forall>(b, p, q) \<in> critical_pairs ren (set R) (set R). (p, q) \<in> (rstep (set C))\<^sup>\<down>" by auto
  qed
  show "\<And>p q. (False, q, p) \<in> critical_pairs ren (set R) (set R) \<Longrightarrow>
           \<exists>v. (q, v) \<in> par_rstep (set C) \<and> (p, v) \<in> (rstep (set C))\<^sup>*"
  proof -
    fix p q
    assume "(False, p, q) \<in> critical_pairs ren (set R) (set R)"
    with closed[of False p q]
    have "\<not> Option.is_none (find (?find p) (reachable_terms C q n))" by auto
    then obtain v where  "find (?find p) (reachable_terms C q n) = Some v"
      by force
    then have "(p,v) \<in> par_rstep (set C)" and "v \<in> set (reachable_terms C q n)"
      unfolding find_Some_iff by auto
    then show "\<exists>v. (p, v) \<in> par_rstep (set C) \<and> (q, v) \<in> (rstep (set C))\<^sup>*"
      using reachable_terms par_rstep_rsteps by blast
  qed
qed

end
