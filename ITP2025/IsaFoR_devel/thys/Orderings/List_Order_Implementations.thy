(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory List_Order_Implementations
imports
  Set_Order_Impl
  Min_Set_Order_Impl
  Weighted_Path_Order.Multiset_Extension2_Impl
  Dual_Multiset_Impl
begin

datatype list_order_type = MS_Ext | Max_Ext | Min_Ext  | Dms_Ext 

fun list_ext :: "nat \<Rightarrow> list_order_type \<Rightarrow> 'a list_ext_impl"
  where "list_ext _ MS_Ext = mul_ext"
     |  "list_ext _ Max_Ext = set_ext"
     |  "list_ext _ Min_Ext = min_set_ext"
     |  "list_ext n Dms_Ext = dms_order_ext n" 

fun list_ext_name :: "list_order_type \<Rightarrow> String.literal"
  where "list_ext_name MS_Ext = STR ''MS''"
     |  "list_ext_name Dms_Ext = STR ''DMS''"
     |  "list_ext_name Min_Ext = STR ''MIN''"
     |  "list_ext_name Max_Ext = STR ''MAX''"

lemma list_ext: "\<exists> s ns. list_order_extension_impl s ns (list_ext n t)"
proof (cases t)
  case MS_Ext
  then show ?thesis using mul_ext_list_ext by auto
next
  case Max_Ext 
  then show ?thesis using set_ext_list_ext by auto
next
  case Min_Ext 
  then show ?thesis using min_set_ext_list_ext by auto
next
  case Dms_Ext
  then show ?thesis using dms_order_ext_list_ext by auto 
qed
end
