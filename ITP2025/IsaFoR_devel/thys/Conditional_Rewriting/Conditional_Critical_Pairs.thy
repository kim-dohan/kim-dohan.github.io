(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Conditional Critical Pairs\<close>

theory Conditional_Critical_Pairs
imports
  Conditional_Rewriting
  TRS.More_Abstract_Rewriting
begin

(*TODO: move*)
lemma greaterThanLessThan_all_conv:
  "(\<forall>i\<in>{m <..< n}. P i) \<longleftrightarrow> (\<forall>i. m < i \<and> i < n \<longrightarrow> P i)"
by auto

subsection \<open>Conditional Overlaps and Conditional Critical Pairs\<close>

definition "overlap R r r' p \<longleftrightarrow>
  (\<exists>p. p \<bullet> r \<in> R) \<and> (\<exists>p. p \<bullet> r' \<in> R) \<and> vars_crule r \<inter> vars_crule r' = {} \<and>
  p \<in> fun_poss (clhs r) \<and> (\<exists>\<sigma>. mgu (clhs r |_ p) (clhs r') = Some \<sigma>)"

definition
  CCP :: "('f, 'v :: infinite) ctrs \<Rightarrow> ('f, 'v) crule set"
where
  "CCP R =
    {((crhs \<rho>\<^sub>1 \<cdot> \<sigma>, replace_at (clhs \<rho>\<^sub>1) p (crhs \<rho>\<^sub>2) \<cdot> \<sigma>), subst_list \<sigma> (snd \<rho>\<^sub>1 @ snd \<rho>\<^sub>2)) | \<rho>\<^sub>1 \<rho>\<^sub>2 \<sigma> p.
      overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p \<and> mgu (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some \<sigma> \<and> (p = [] \<longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2))}"

lemma overlapI [intro]:
  assumes "\<exists>\<pi>. \<pi> \<bullet> \<rho>\<^sub>1 \<in> R" and "\<exists>\<pi>. \<pi> \<bullet> \<rho>\<^sub>2 \<in> R"
    and "vars_crule \<rho>\<^sub>1 \<inter> vars_crule \<rho>\<^sub>2 = {}"
    and "p \<in> fun_poss (clhs \<rho>\<^sub>1)"
    and "mgu (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some \<sigma>"
  shows "overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p"
using assms unfolding overlap_def by blast

lemma overlap_mguD:
  assumes "overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p"
  obtains \<sigma> where "mgu (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some \<sigma>"
using assms by (auto simp: overlap_def)

lemma CCP_I:
  assumes "\<exists>\<pi>. \<pi> \<bullet> \<rho>\<^sub>1 \<in> R" and "\<exists>\<pi>. \<pi> \<bullet> \<rho>\<^sub>2 \<in> R"
    and "vars_crule \<rho>\<^sub>1 \<inter> vars_crule \<rho>\<^sub>2 = {}"
    and "p \<in> fun_poss (clhs \<rho>\<^sub>1)"
    and "mgu (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some \<sigma>"
    and "p = [] \<Longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2)"
  shows "((crhs \<rho>\<^sub>1 \<cdot> \<sigma>, replace_at (clhs \<rho>\<^sub>1) p (crhs \<rho>\<^sub>2) \<cdot> \<sigma>), subst_list \<sigma> (snd \<rho>\<^sub>1 @ snd \<rho>\<^sub>2)) \<in> CCP R"
using assms unfolding CCP_def by blast

text \<open>
  Almost orthogonality modulo infeasibility (that is, all overlaps are either trivial,
  we have a root-overlap of two variants of the same rule,
  or the corresponding conditions are not all satisfiable at the same time).
\<close>
definition almost_orthogonal :: "('f, 'v :: infinite) ctrs \<Rightarrow> bool"
where
  "almost_orthogonal R \<longleftrightarrow>
    left_linear_trs (Ru R) \<and> (\<forall>\<rho>\<^sub>1 \<rho>\<^sub>2 p. overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p \<longrightarrow>
      (let \<mu> = the (mgu (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2)) in
      p = [] \<and> crhs \<rho>\<^sub>1 \<cdot> \<mu> = crhs \<rho>\<^sub>2 \<cdot> \<mu> \<or>
      p = [] \<and> (\<exists>p. p \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2) \<or>
      (\<forall>m n. comm ((cstep_n R m)\<^sup>*) ((cstep_n R n)\<^sup>*) \<longrightarrow>
        \<not> (\<exists>\<sigma>. conds_n_sat R m (subst_list \<mu> (snd \<rho>\<^sub>1)) \<sigma> \<and>
               conds_n_sat R n (subst_list \<mu> (snd \<rho>\<^sub>2)) \<sigma>))))"

lemma almost_orthogonal_imp_linear [simp]:
  "almost_orthogonal R \<Longrightarrow> ((l, r), cs) \<in> R \<Longrightarrow> linear_term l"
  by (auto simp: almost_orthogonal_def left_linear_trs_def Ru_def)

lemma almost_orthogonal_overlap_cases [consumes 2, cases pred: almost_orthogonal]:
  assumes "almost_orthogonal R" and "overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p"
  obtains (trivial) \<sigma> where "p = []" and "mgu (clhs \<rho>\<^sub>1) (clhs \<rho>\<^sub>2) = Some \<sigma>"
    and "crhs \<rho>\<^sub>1 \<cdot> \<sigma> = crhs \<rho>\<^sub>2 \<cdot> \<sigma>"
  | (variants) \<pi> where "p = []" and "\<pi> \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  | (infeasible) \<sigma> where "mgu (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some \<sigma>"
    and "\<And>m n. comm ((cstep_n R m)\<^sup>*) ((cstep_n R n)\<^sup>*) \<Longrightarrow>
      \<not> (\<exists>\<tau>. conds_n_sat R m (subst_list \<sigma> (snd \<rho>\<^sub>1)) \<tau> \<and>
             conds_n_sat R n (subst_list \<sigma> (snd \<rho>\<^sub>2)) \<tau>)"
apply (rule overlap_mguD [OF \<open>overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p\<close>])
apply (insert assms)
apply (simp only: almost_orthogonal_def Let_def)
  by (metis option.sel subt_at.simps(1))

lemma CCP_E:
  fixes s :: "('f, 'v :: infinite) term"
  assumes "((s, t), cs) \<in> CCP R"
  shows "\<exists>\<rho>\<^sub>1 \<rho>\<^sub>2 p \<sigma>. s = crhs \<rho>\<^sub>1 \<cdot> \<sigma> \<and> t = replace_at (clhs \<rho>\<^sub>1) p (crhs \<rho>\<^sub>2) \<cdot> \<sigma> \<and>
    cs = subst_list \<sigma> (snd \<rho>\<^sub>1 @ snd \<rho>\<^sub>2) \<and>
    overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p \<and> mgu (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some \<sigma> \<and> (p = [] \<longrightarrow> \<not> (\<exists>\<pi>. \<pi> \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2))"
using assms unfolding CCP_def by blast

end
