(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Labelings_Impl
imports
  Labelings
  First_Order_Rewriting.Trs_Impl
begin

derive compare_order lab

instantiation lab :: (showl,showl)showl
begin
fun showsl_lab where
  "showsl_lab (UnLab f) = showsl f"
| "showsl_lab (Lab f l) = (showsl_lab f \<circ> showsl_lit (STR ''['') \<circ> showsl l \<circ> showsl_lit (STR '']''))"
| "showsl_lab (Sharp f) = (showsl_lab f \<circ> showsl_lit (STR ''#''))"
| "showsl_lab (FunLab f l) = (showsl_lab f \<circ> default_showsl_list id (map showsl_lab l))"
definition "showsl_list (xs :: (_,_)lab list) = default_showsl_list showsl xs"
instance ..
end

text \<open>Resolve problems with recursive dependencies in generated code.\<close>
lemma [code]:
  "HOL.eq (FunLab f ls) (FunLab g ks) \<longleftrightarrow> HOL.eq f g \<and> list_all2 HOL.eq ls ks"
  by (simp_all add: list_all2_eq [symmetric])

abbreviation unlab_rules :: "(('f, 'l) lab, 'v) rules \<Rightarrow> (('f, 'l) lab, 'v) rules" where
  "unlab_rules \<equiv> map (map_funs_rule unlab)"

abbreviation init_lab_rules :: "('f, 'v) rules \<Rightarrow> (('f, 'l) lab, 'v) rules" where
  "init_lab_rules \<equiv> map init_lab_rule"

end

