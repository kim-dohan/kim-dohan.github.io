(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Non_Inf_Order_Impl
imports
  Non_Inf_Order
  Show.Show
  Certification_Monads.Check_Monad
  Show.Shows_Literal
begin

datatype ('f,'v) c_constraint =
  Conditional_C bool "('f, 'v) rule" "('f, 'v) rule" |
  Unconditional_C bool "('f, 'v) rule"

fun cc_satisfied :: "'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) c_constraint \<Rightarrow> bool" where
  "cc_satisfied F S NS (Unconditional_C stri (s, t)) =
    (\<forall> \<sigma>. \<Union>(funas_term ` range \<sigma>) \<subseteq> F \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (if stri then S else NS))"
| "cc_satisfied F S NS (Conditional_C stri (u, v) (s, t)) =
  (\<forall> \<sigma>. \<Union>(funas_term ` range \<sigma>) \<subseteq> F \<longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (if stri then S else NS) \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (if stri then S else NS))"

record ('f, 'v) non_inf_order =
  valid :: "showsl check"
  ns :: "('f, 'v) rule \<Rightarrow> showsl check"
  cc :: "('f, 'v) c_constraint \<Rightarrow> showsl check"
  af :: "'f dep"
  desc :: showsl

hide_const (open) valid ns af desc cc

locale generic_non_inf_order_impl = 
  fixes generate_non_inf_order :: "'a \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f :: showl,'v :: showl)non_inf_order" 
  assumes generate_non_inf_order: "isOK(non_inf_order.valid (generate_non_inf_order rp F)) 
  \<Longrightarrow> isOK (check_allm (non_inf_order.ns (generate_non_inf_order rp F)) ns_list)
  \<Longrightarrow> isOK (check_allm (non_inf_order.cc (generate_non_inf_order rp F)) cc)
  \<Longrightarrow> \<exists> S NS. 
  non_inf_order_trs S NS (set F) (non_inf_order.af (generate_non_inf_order rp F)) \<and> 
  set ns_list \<subseteq> NS \<and>
  Ball (set cc) (cc_satisfied (set F) S NS)"

end

