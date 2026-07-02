(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Min_Set_Order_Impl
imports
  Min_Set_Order
begin

definition min_set_ext :: "'a list_ext_impl" where
  "min_set_ext s_ns = (\<lambda> as bs. 
  (bs \<noteq> [] \<and> (\<forall> a \<in> set as. \<exists> b \<in> set bs. fst (s_ns a b)),  
  (\<forall> a \<in> set as. \<exists> b \<in> set bs. snd (s_ns a b))))"

lemma min_set_ext_list_ext:
  "\<exists> s ns. list_order_extension_impl s ns min_set_ext"
proof(intro exI)
  interpret list_order_extension min_set_s_order min_set_ns_order by (rule min_set_order)
  show "list_order_extension_impl min_set_s_order min_set_ns_order min_set_ext"
    by (unfold_locales, (force simp: min_set_ext_def min_set_s_order_def min_set_ns_order_def)+)
qed

end

