(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Systems of Representatives of Equivalence Relations\<close>

theory Representative_System
  imports 
    Main
begin

definition repsys :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set"
where
  "repsys A R = {(SOME x. x \<in> X) | X. X \<in> A // R}"

text \<open>Equivalence classes of an equivalence relation are nonempty.\<close>
lemma class_nonempty:
  assumes "equiv A R" and "X \<in> A // R"
  shows "\<exists>x. x \<in> X"
  using assms by (metis equiv_class_self quotientE)

lemma repsys_subset:
  assumes "equiv A R"
  shows "repsys A R \<subseteq> A"
  using class_nonempty [OF assms]
  by (auto simp: repsys_def) (metis UnionI Union_quotient assms someI_ex)

lemma mem_repsys_class:
  assumes "equiv A R" and "x \<in> repsys A R"
  shows "\<exists>X \<in> A // R. x \<in> X"
  using class_nonempty [OF assms(1)] and assms(2)
  by (auto simp: repsys_def) (metis someI_ex)

lemma repsys_unique_modulo:
  assumes "equiv A R"
    and "x \<in> repsys A R" and "y \<in> repsys A R" and "x \<noteq> y"
  shows "(x, y) \<notin> R"
  using assms by (auto simp: repsys_def) (metis (lifting) class_nonempty quotient_eq_iff someI_ex)

lemma repsys_representative:
  assumes "equiv A R"
    and "x \<in> A"
  shows "\<exists>y \<in> repsys A R. (x, y) \<in> R"
proof -
  from Union_quotient [OF assms(1)] and \<open>x \<in> A\<close> obtain X
    where "X \<in> A // R" and "x \<in> X" by auto
  then have "(x, (SOME x. x \<in> X)) \<in> R"
    using quotient_eq_iff [OF assms(1)] by (metis someI_ex)
  moreover have "(SOME x. x \<in> X) \<in> repsys A R"
    using \<open>X \<in> A // R\<close> by (auto simp: repsys_def)
  ultimately show ?thesis by blast
qed

end
