(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Rules_NJ_Impl
imports
  Usable_Rules_NJ
  TRS.Tcap_Impl
  Auxx.Inductive_Set_Impl
begin

context usable_rules_reachability
begin
lemma U0_generic: "U0 lr t = generic_inductive_set.the_set R 
  (\<lambda> t (l,r). is_Var l \<or> (\<exists> s. t \<unrhd> s \<and> is_Fun s \<and> match_tcap_below l R s)) (\<lambda> lr. {snd lr}) t lr"
  (is "_ = generic_inductive_set.the_set R ?P ?Q t lr")
proof -
  interpret generic_inductive_set R ?P ?Q .
  show ?thesis
  proof
    assume "the_set t lr"
    then show "U0 lr t"
      by (induct rule: the_set.induct, auto intro: U0.intros)
  next
    assume "U0 lr t"
    then show "the_set t lr"
    proof (induct rule: U0.induct)
      case match
      then show ?case
        by (intro non_rec, auto)
    next
      case lvar
      then show ?case
        by (intro non_rec, auto)
    next
      case rec
      show ?case
        by (rule rec_rec[OF rec(2) _ rec(4)], auto)
    qed
  qed
qed
end

definition usable_rules_reach_U0_impl :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)rules" where
  "usable_rules_reach_U0_impl R t = inductive_set_impl 
    R 
    (\<lambda>t (l,r). is_Var l \<or> (\<exists> u \<in> set (supteq_list t). is_Fun u \<and> match_tcap_below_impl l R u)) 
    (\<lambda> lr. [snd lr]) 
    [t]"

definition usable_rules_reach_impl :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)rules" where
  "usable_rules_reach_impl R t \<equiv> let U0t = usable_rules_reach_U0_impl R t in
    if (\<forall> (l,r) \<in> set U0t. vars_term r \<subseteq> vars_term l) then U0t else R"

lemma usable_rules_reach_impl[simp]: "set (usable_rules_reach_impl R t) = usable_rules_reach (set R) t"
proof -
  interpret usable_rules_reachability "set R" .
  have [simp]: "set (usable_rules_reach_U0_impl R t) = {lr. U0 lr t}"
    unfolding U0_generic usable_rules_reach_U0_impl_def
      by (rule inductive_set_impl_single, auto)  
  show ?thesis unfolding usable_rules_reach_impl_def Ur_def Let_def varcond_def
    by (auto split: if_splits)
qed

end
