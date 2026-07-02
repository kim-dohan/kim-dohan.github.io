(*
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Redundant_Rules_Impl
imports
  Redundant_Rules
  Equational_Reasoning_Impl
  First_Order_Rewriting.Trs_Impl
begin

definition
  check_redundant_rules :: "('f :: showl, 'v :: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> nat \<Rightarrow> ('f, 'v) term list list \<Rightarrow> showsl check"
where
  "check_redundant_rules R R' n convs = do {
     let S = list_diff R' R;
     let T = list_diff R R';
     check_allm (\<lambda> (l, r). 
      check (List.member (reachable_terms R l n) r)
        (showsl_lit (STR ''could not simulate rule '') \<circ> showsl_rule (l, r))) S;
     check_allm (\<lambda> (l, r). 
       (try existsM (\<lambda>conv. check_conversion_sequence R' l r conv) convs catch
       (\<lambda>e. check_join_BFS_limit n R' l r))) T
   }"

lemma check_redundant_rules:
  assumes "isOK(check_redundant_rules R R' n convs)"
  and "CR (rstep (set R'))"
  shows "CR (rstep (set R))"
proof -
  let ?S = "list_diff R' R"
  let ?T = "list_diff R R'"
  note ok = assms(1)[unfolded check_redundant_rules_def, simplified]
  from ok have "\<forall> (l, r) \<in> set ?S. List.member (reachable_terms R l n) r"
    by auto
  then have "\<forall> (l, r) \<in> set ?S. r \<in> set (reachable_terms R l n)"
    using in_set_member by fast+
  then have S:"\<forall> (l, r) \<in> set ?S. (l, r) \<in> (rstep (set R))^*"
    using reachable_terms by blast+
  have eq:"set R \<union> set ?S = set R' \<union> set ?T" by auto
  {
    fix l r
    assume "(l, r) \<in> set ?T"
    then have "(l, r) \<in> set R - set R'" by auto
    with bspec[OF conjunct2[OF ok] this]
    have "isOK (existsM (\<lambda>conv. check_conversion_sequence R' l r conv) convs) \<or> isOK (check_join_BFS_limit n R' l r)"
      (is "?C \<or> ?J")
      by (auto split: catch_splits simp del: isOK_existsM)
    then have "(l, r) \<in> (rstep (set R'))\<^sup>\<leftrightarrow>\<^sup>*"
    proof
      assume ?J
      then have "(l, r) \<in> join (rstep (set R'))"
        using check_join_BFS_limit_sound by blast
      then show ?thesis by (metis CR_imp_conversionIff_join assms(2))
    next
      assume ?C
      with check_conversion_sequence show ?thesis by auto
    qed
  }
  from redundant_rules_removal[OF this assms(2), of "set ?T"]
    redundant_rules[OF S] assms eq
  show ?thesis by auto
qed

definition
  check_redundant_rules_ncr :: "('f :: showl, 'v :: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> nat \<Rightarrow> showsl check"
where
  "check_redundant_rules_ncr R R' n = do {
     check_subseteq R R' <+? (\<lambda> _. showsl_lit (STR ''old TRS is not a subsystem of given TRS''));
     let S = list_diff R' R;
     let T = list_diff R R';
     check_allm (\<lambda> (l, r).
      check (List.member (reachable_terms R l n) r)
        (showsl_lit (STR ''could not simulate rule '') \<circ> showsl_rule (l, r))
     ) S;
     check_allm (\<lambda> (l, r).
      check (List.member (reachable_terms R' l n) r)
        (showsl_lit (STR ''could not simulate rule '') \<circ> showsl_rule (l, r))
     ) T
   }"

lemma check_redundant_rules_ncr:
  assumes "isOK(check_redundant_rules_ncr R R' n)"
  and "\<not> CR (rstep (set R'))"
  shows "\<not> CR (rstep (set R))"
proof -
  let ?S = "list_diff R' R"
  let ?T = "list_diff R R'"
  note ok = assms[unfolded check_redundant_rules_ncr_def]
  from ok have "\<forall> (l, r) \<in> set ?S. List.member (reachable_terms R l n) r"
    by simp
  then have "\<forall> (l, r) \<in> set ?S. r \<in> set (reachable_terms R l n)"
    using in_set_member by fast+  
  then have S:"\<forall> (l, r) \<in> set ?S. (l, r) \<in> (rstep (set R))^*"
    using reachable_terms by blast+
  from ok have "\<forall> (l, r) \<in> set ?T. List.member (reachable_terms R' l n) r"
    by simp
  then have "\<forall> (l, r) \<in> set ?T. r \<in> set (reachable_terms R' l n)"
    using in_set_member by fast+
  then have T:"\<forall> (l, r) \<in> set ?T. (l, r) \<in> (rstep (set R'))^*"
    using reachable_terms by blast+
  have "set R \<union> set ?S = set R' \<union> set ?T" by auto
  with redundant_rules[OF S] redundant_rules[OF T] assms(2) show ?thesis
    by simp
qed

end
