(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Set_Order_Impl
imports 
  Set_Order
  Weighted_Path_Order.List_Order
begin

definition set_ext :: "'a list_ext_impl" where "set_ext s_ns \<equiv> \<lambda> as bs. 
  (as \<noteq> [] \<and> (\<forall> b \<in> set bs. \<exists> a \<in> set as. fst (s_ns a b)),  
  (\<forall> b \<in> set bs. \<exists> a \<in> set as. snd (s_ns a b)))"


lemma set_ext_list_ext: "\<exists> s ns. list_order_extension_impl s ns set_ext"
proof(intro exI)
  let ?s = "set_s_order"
  let ?ns = "set_ns_order"
  show "list_order_extension_impl ?s ?ns set_ext"
  proof
    fix s ns
    show "?s {(a,b). s a b} {(a,b). ns a b} = {(as,bs). fst (set_ext (\<lambda> a b. (s a b, ns a b)) as bs)}" unfolding set_ext_def set_s_order_def by auto
  next
    fix s ns
    show "?ns {(a,b). s a b} {(a,b). ns a b} = {(as,bs). snd (set_ext (\<lambda> a b. (s a b, ns a b)) as bs)}" unfolding set_ext_def set_ns_order_def by auto
  next
    fix s ns s' ns' as bs
    assume "set as \<times> set bs \<inter> ns \<subseteq> ns'"
           "set as \<times> set bs \<inter> s \<subseteq> s'"
           "(as,bs) \<in> ?s s ns"
    then show "(as,bs) \<in> ?s s' ns'" unfolding set_s_order_def by blast
  next
    fix s ns s' ns' as bs
    assume "set as \<times> set bs \<inter> ns \<subseteq> ns'"
           "set as \<times> set bs \<inter> s \<subseteq> s'"
           "(as,bs) \<in> ?ns s ns"
    then show "(as,bs) \<in> ?ns s' ns'" unfolding set_ns_order_def by blast
  qed
qed

end
