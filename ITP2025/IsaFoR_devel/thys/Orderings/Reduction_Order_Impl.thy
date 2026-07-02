(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory Reduction_Order_Impl
  imports
    Reduction_Order
    Certification_Monads.Check_Monad
    Show.Shows_Literal
begin

text \<open>Ground-total reduction orders with respect to a given signature.\<close>
record ('f, 'v) redord =
  valid :: "showsl check"
  less :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  min_const :: "'f"

hide_const (open) valid less min_const

locale reduction_order_impl =
  fixes ro :: "'a \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f::showl, 'v::showl) redord"
  assumes valid: "isOK (redord.valid (ro r F)) \<Longrightarrow>
     (redord.min_const (ro r F), 0) \<in> set F \<and>
     reduction_order (redord.less (ro r F)) \<and>
     (\<forall>s t. fground (set F) s \<and> fground (set F) t \<longrightarrow>
       s = t \<or> redord.less (ro r F) s t \<or> redord.less (ro r F) t s) \<and>
     (\<exists>less.
       gtotal_reduction_order less \<and>
       (\<forall>s t. redord.less (ro r F) s t \<longrightarrow> less s t) \<and>
       (\<forall>t. ground t \<longrightarrow> less\<^sup>=\<^sup>= t (Fun (redord.min_const (ro r F)) [])))"

end
