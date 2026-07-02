(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Operations on AC termination problems (AC-TPs)\<close>

theory AC_Termination_Problem_Spec
imports
  First_Order_Rewriting.Trs_Impl
  AC_TRS.AC_Rewriting
begin

subsection \<open>Record-Based Interface\<close>

type_synonym ('f,'v)ac_tp = "('f,'v)trs \<times> 'f set \<times> 'f set"

fun relation_ac_tp :: "('f,'v) ac_tp \<Rightarrow> ('f,'v)trs" where 
  "relation_ac_tp (R,A,C) = aoc_rewriting.relaoc A C R"

record ('p, 'f, 'v) ac_tp_ops =
  ac_tp :: "'p \<Rightarrow> ('f,'v)ac_tp"
  R :: "'p \<Rightarrow> ('f, 'v) rules"
  A :: "'p \<Rightarrow> 'f list"
  C :: "'p \<Rightarrow> 'f list"
  mk :: "('f, 'v) rules \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'p"
  delete_rules :: "'p \<Rightarrow> ('f,'v)rules \<Rightarrow> 'p"
  E :: "'p \<Rightarrow> ('f,'v)rules"


hide_const (open)
  R A C mk ac_tp delete_rules E

locale ac_tp_defs =
  fixes I :: "('p, 'f::showl, 'v::showl) ac_tp_ops"
begin
  abbreviation R where "R \<equiv> ac_tp_ops.R I"
  abbreviation A where "A \<equiv> ac_tp_ops.A I"
  abbreviation C where "C \<equiv> ac_tp_ops.C I"
  abbreviation E where "E \<equiv> ac_tp_ops.E I"
  abbreviation ac_tp where "ac_tp \<equiv> ac_tp_ops.ac_tp I"
  abbreviation mk where "mk \<equiv> ac_tp_ops.mk I"
  abbreviation delete_rules where "delete_rules \<equiv> ac_tp_ops.delete_rules I"
end

locale ac_tp_spec = ac_tp_defs I for I +
  assumes ac_tp_sound: "ac_tp tp = (set (R tp), set (A tp), set (C tp))"
    and mk_sound: 
      "set (R (mk r a c)) = (set r)"
      "set (A (mk r a c)) = (set a)"
      "set (C (mk r a c)) = (set c)"
    and delete_rules_sound: "ac_tp (delete_rules tp dr) = 
      (set (R tp) - set dr, set (A tp), set (C tp))"
    and E_sound: "rstep (set (E tp)) = acrstep (set (A tp)) (set (C tp))"
begin

lemmas ac_tp_spec_sound[simp] =
  ac_tp_sound
  mk_sound
  delete_rules_sound
  E_sound

lemma SN_relation_ac_tp: "SN (relation_ac_tp (ac_tp_ops.ac_tp I tp)) = 
  SN_rel (rstep (set (R tp))) (aoc_rewriting.AOCEQ (set (A tp)) (set (C tp)))"
  by (auto simp: aoc_rewriting.relaoc_def SN_rel_defs)

end


end
