(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Operations on AC termination problems (AC-TPs)\<close>

theory AC_Termination_Problem_Impl
imports
  AC_Termination_Problem_Spec
  Show.Shows_Literal
begin

subsection \<open>A list based, minimal implementation\<close>

definition A_trs_impl :: "'f list \<Rightarrow> ('f,string)rules" where
  "A_trs_impl A = (let x = Var ''x''; y = Var ''y''; z = Var ''z'' in
    map (\<lambda> f. (Bin f (Bin f x y) z, Bin f x (Bin f y z))) A
  @ map (\<lambda> f. (Bin f x (Bin f y z), Bin f (Bin f x y) z)) A)"

definition C_rules_impl :: "'f list \<Rightarrow> ('f,string)rules" where
  "C_rules_impl C = (let x = Var ''x''; y = Var ''y'' in
    map (\<lambda> f. (Bin f x y, Bin f y x)) C)"

definition AC_trs_impl :: "'f list \<Rightarrow> 'f list \<Rightarrow> ('f,string)rules" where
  "AC_trs_impl A C = A_trs_impl A @ C_rules_impl C"

lemma C_rules_impl: "rstep (set (C_rules_impl (C :: 'f list))) = rstep (C_rules (set C))" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
    by (rule rstep_mono, auto simp: C_rules_impl_def Let_def)
  show "?r \<subseteq> ?l"
  proof (rule rstep_subset[OF ctxt_closed_rstep subst_closed_rstep], standard)
    fix l r :: "('f,string)term"
    assume "(l,r) \<in> C_rules (set C)"
    then obtain f s t where l: "l = Bin f s t" and r: "r = Bin f t s" and f: "f \<in> set C" 
      unfolding C_rules_def by auto
    let ?x = "''x''" let ?y = "''y''"
    show "(l,r) \<in> ?l"
      by (rule rstepI[of "Bin f (Var ?x) (Var ?y)" "Bin f (Var ?y) (Var ?x)" _ _ Hole 
        "\<lambda> x. if x = ?x then s else t"], insert f,
        auto simp: l r C_rules_impl_def Let_def)
  qed
qed
    
lemma A_trs_impl: "rstep (set (A_trs_impl (A :: 'f list))) = rstep (A_trs (set A))" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
    by (rule rstep_mono, auto simp: A_trs_impl_def Let_def A_trs_def)
  let ?x = "''x''" let ?y = "''y''" let ?z = "''z''"
  show "?r \<subseteq> ?l"
  proof (rule rstep_subset[OF ctxt_closed_rstep subst_closed_rstep], standard)
    fix l r :: "('f,string)term"
    assume "(l,r) \<in> A_trs (set A)"
    then consider (A) f s t u where "l = Bin f (Bin f s t) u" "r = Bin f s (Bin f t u)" "f \<in> set A" 
      | (inv) f s t u where "r = Bin f (Bin f s t) u" "l = Bin f s (Bin f t u)" "f \<in> set A"
      unfolding A_trs_def A_rules_def by auto
    then show "(l,r) \<in> ?l"
    proof (cases)
      case (A f s t u)
      show ?thesis
        by (rule rstepI[of "Bin f (Bin f (Var ?x) (Var ?y)) (Var ?z)" "Bin f (Var ?x) (Bin f (Var ?y) (Var ?z))" _ _ Hole 
          "\<lambda> x. if x = ?x then s else if x = ?y then t else u"], insert A,
          auto simp: A_trs_impl_def Let_def)
    next
      case (inv f s t u)
      show ?thesis
        by (rule rstepI[of "Bin f (Var ?x) (Bin f (Var ?y) (Var ?z))" "Bin f (Bin f (Var ?x) (Var ?y)) (Var ?z)" _ _ Hole 
          "\<lambda> x. if x = ?x then s else if x = ?y then t else u"], insert inv,
          auto simp: A_trs_impl_def Let_def)
    qed
  qed
qed

lemma AC_trs_impl[simp]: "rstep (set (AC_trs_impl A C)) = rstep (AC_trs (set A) (set C))" 
  unfolding AC_trs_impl_def set_append rstep_union A_trs_impl C_rules_impl AC_trs_def ..


definition
  ac_tp_list_impl ::
    "(('f, string) rules \<times> 'f list \<times> 'f list, 'f, string) ac_tp_ops"
where
  "ac_tp_list_impl \<equiv> \<lparr>
    ac_tp_ops.ac_tp = (\<lambda>(r, a, c) . (set r, set a, set c)),
    ac_tp_ops.R = (\<lambda>(r, _, _). r),
    ac_tp_ops.A = (\<lambda>(_, a, _). a),
    ac_tp_ops.C = (\<lambda>(r, _, c). c),
    ac_tp_ops.mk = (\<lambda> r a c. (r,a,c)),
    ac_tp_ops.delete_rules = (\<lambda> (r, a, c) dr. (list_diff r dr, a, c)),
    ac_tp_ops.E = (\<lambda>(_,a,c). AC_trs_impl a c)
    \<rparr>"

lemma ac_tp_list_impl: "ac_tp_spec ac_tp_list_impl"
  by (standard, auto simp: ac_tp_list_impl_def)

end
