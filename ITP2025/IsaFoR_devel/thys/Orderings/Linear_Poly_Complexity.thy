(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Linear_Poly_Complexity
imports 
  Complexity
  Certification_Monads.Check_Monad
  Matrix.Ordered_Semiring
  Show.Shows_Literal
begin
record 'a lpoly_order_semiring = "'a ordered_semiring" +
  plus_single_mono :: "bool" ("psm\<index>")
  default :: 'a 
  arcpos :: "'a \<Rightarrow> bool" ("arc'_pos\<index>")
  checkmono :: "'a \<Rightarrow> bool" ("check'_mono\<index>")
  bound :: "'a \<Rightarrow> nat" 
  check_complexity :: "'a \<Rightarrow> nat \<Rightarrow> showsl check" 
  description :: showsl 

locale lpoly_order = ordered_semiring R for R :: "('a :: showl) lpoly_order_semiring" (structure) + 
  assumes plus_gt_left_mono: "\<lbrakk>x \<succ> y; psm; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<oplus> z \<succ> y \<oplus> z"
  and plus_gt_both_mono: "\<lbrakk>x \<succ> y; z \<succ> u; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R; u \<in> carrier R\<rbrakk> \<Longrightarrow> x \<oplus> z \<succ> y \<oplus> u"
  and times_gt_left_mono: "\<lbrakk>x \<succ> y; \<not> psm; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<otimes> z \<succ> y \<otimes> z"
  and times_gt_right_mono: "\<lbrakk>x \<succ> y; \<not> psm; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> z \<otimes> x  \<succ> z \<otimes> y"
  and zero_leastI: "\<lbrakk>\<not> psm; x \<in> carrier R\<rbrakk> \<Longrightarrow> x \<succ> \<zero>" 
  and zero_leastII: "\<lbrakk>\<zero> \<succ> x; \<not> psm; x \<in> carrier R\<rbrakk> \<Longrightarrow> x = \<zero>" 
  and SN: "SN {(x,y) . x \<in> carrier R \<and> y \<in> carrier R \<and> y \<succeq> \<zero> \<and> arc_pos y \<and> x \<succ> y}"
  and wf_default[simp, intro]: "default R \<in> carrier R"
  and default_geq_zero: "default R \<succeq> \<zero>"
  and arc_pos_plus: "\<lbrakk>arc_pos x; x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow> arc_pos (x \<oplus> y)"
  and arc_pos_mult: "\<lbrakk>arc_pos x; arc_pos y; x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow> arc_pos (x \<otimes> y)"
  and arc_pos_max0: "x \<in> carrier R \<Longrightarrow> arc_pos (Max \<zero> x) = arc_pos x" 
  and arc_pos_default: "arc_pos (default R)"
  and arc_pos_one: "arc_pos \<one>"
  and arc_pos_zero: "\<not> psm \<Longrightarrow> \<not> arc_pos \<zero>"
  and not_all_ge: "\<And> x y. \<not> psm \<Longrightarrow> x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> arc_pos y 
    \<Longrightarrow> \<exists> z. z \<in> carrier R \<and> z \<succeq> \<zero> \<and> arc_pos z \<and> \<not> x \<succeq> (y \<otimes> z)"
begin
lemma max0_npsm_id: assumes psm: "\<not> psm"
  and x: "x \<in> carrier R"
  shows "Max \<zero> x = x"
  unfolding max_comm[OF zero_closed x]
  by (rule max_id[OF _ _ gt_imp_ge[OF zero_leastI[OF psm]]], insert x, auto)  
end

locale mono_linear_poly_order_carrier = lpoly_order +
  assumes plus_single_mono: "psm"
  and check_mono: "\<lbrakk>check_mono x; y \<succ> z; x \<succeq> \<zero>; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<otimes> y \<succ> x \<otimes> z" 
  and default_gt_zero: "default R \<succ> \<zero>"
  and arc_pos_True: "arc_pos x"

locale complexity_linear_poly_order_carrier = mono_linear_poly_order_carrier + 
  assumes bound: "deriv_bound {(x,y) . (x :: 'a :: showl) \<in> carrier R \<and> y \<in> carrier R \<and> y \<succeq> \<zero> \<and> arc_pos y \<and> x \<succ> y} x (bound R x)"
  and bound_plus: "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> bound R (x \<oplus> y) \<le> bound R x + bound R y"
  and bound_0[simp]: "bound R \<zero> = 0"
  and bound_mono: "x \<succeq> y \<Longrightarrow> x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> bound R x \<ge> bound R y"
  and complexity_cond: "bc \<in> carrier R \<Longrightarrow> bcv \<in> carrier R \<Longrightarrow> bd \<in> carrier R \<Longrightarrow>
    bc \<succeq> \<zero> \<Longrightarrow> bcv \<succeq> \<zero> \<Longrightarrow> bd \<succeq> \<zero> \<Longrightarrow>
    isOK(check_complexity R bc deg) \<Longrightarrow> 
    \<exists> g. g \<in> O_of (Comp_Poly deg) \<and> (\<forall> n. bound R (bd \<otimes> (bc [^] n \<otimes> bcv)) \<le> g n)"

end
