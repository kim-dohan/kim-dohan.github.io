(*
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

theory Non_Confluence2
imports
  Conditional_Critical_Pairs
begin

lemma rsteps_peak_non_join_non_confluence:
  assumes "(s, t) \<in> (rstep R)\<^sup>*" and "(s, u) \<in> (rstep R)\<^sup>*" and "(t, u) \<notin> (rstep R)\<^sup>\<down>"
  shows "\<not> CR (rstep R)"
  using assms by blast

lemma csteps_peak_non_join_non_confluence:
  assumes "(s, t) \<in> (cstep R)\<^sup>*" and "(s, u) \<in> (cstep R)\<^sup>*" and "(t, u) \<notin> (cstep R)\<^sup>\<down>"
  shows "\<not> CR (cstep R)"
using assms by blast

lemma rstep_Ru_non_join_cstep_non_join:
  assumes "(s, t) \<notin> (rstep (Ru R))\<^sup>\<down>"
  shows "(s, t) \<notin> (cstep R)\<^sup>\<down>"
  using assms by (meson cstep_imp_Ru_step joinE joinI rtrancl_mono subsetCE)

lemma csteps_peak_non_rstep_Ru_join_non_CR:
  assumes "(s, t) \<in> (cstep R)\<^sup>*" and "(s, u) \<in> (cstep R)\<^sup>*" and "(t, u) \<notin> (rstep (Ru R))\<^sup>\<down>"
  shows "\<not> CR (cstep R)"
  using assms rstep_Ru_non_join_cstep_non_join csteps_peak_non_join_non_confluence by metis

(* TODO: move *)
lemma csteps_subst:
  assumes "(s, t) \<in> (cstep R)\<^sup>*"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  using assms
proof (induct rule: rtrancl_induct)
  case (step y z)
  from step(2) have "(y \<cdot> \<sigma>, z \<cdot> \<sigma>) \<in> cstep R" by (auto simp: cstep_subst)
  with step(3) show ?case by simp
qed (auto simp: cstep_subst)

lemma ucpdnf:
  assumes "(s, t) \<in> (cstep R)\<^sup>*"
    and "(s, u) \<in> (cstep R)\<^sup>*"
    and "t \<in> NF_trs (Ru R)"
    and "u \<in> NF_trs (Ru R)"
    and "t \<noteq> u"
  shows "\<not> CR (cstep R)"
  using assms by (meson csteps_peak_non_rstep_Ru_join_non_CR join_NF_imp_eq)

(* Consider an unconditional rule l \<rightarrow> r \<in> R, where V(r) is not a subset of V(l).
   If r \<in> NF(Ru) then R is non-confluent *)
lemma urnf:
  fixes R :: "('f, 'v :: infinite) ctrs"
  assumes vc: "\<forall>((l, r), cs) \<in> R. is_Fun l"
    and rule: "((l, r), Nil) \<in> R"
    and vars: "\<not> vars_term r \<subseteq> vars_term l"
    and nf: "r \<in> NF_trs (Ru R)"
  shows "\<not> CR (cstep R)"
proof -
  from vars obtain x where xr: "x \<in> vars_term r" and xl: "x \<notin> vars_term l" by auto
  obtain y :: 'v where "y \<sharp> (l, r)" using finite_rule_supp rule_pt.fresh_ex by blast
  then have y: "y \<notin> vars_term l \<union> vars_term r" by (simp add: rule_pt.fresh_def supp_vars_term_eq)
  let ?\<sigma> = "sop (x \<rightleftharpoons> y)"
  have l: "l \<cdot> ?\<sigma> = l" using xl y
    by (metis (no_types, lifting) UnI1 prod.sel(1) permutation_type.swap_fresh_fresh
        rule_pt.fresh_def rule_pt.fst_eqvt rule_pt.permutation_type_axioms rule_pt.supp_Un
        sup_idem supp_vars_term_eq term_apply_subst_Var_Rep_perm)
  from cstepI [OF rule, of Var l \<box> r] have 0: "(l, r) \<in> (cstep R)\<^sup>*" by simp
  from 0 have "(l \<cdot> ?\<sigma>, r) \<in> (cstep R)\<^sup>*" using l by auto
  moreover from 0 have "(l \<cdot> ?\<sigma>, r \<cdot> ?\<sigma>) \<in> (cstep R)\<^sup>*" by (rule csteps_subst) 
  moreover from nf have "r \<cdot> ?\<sigma> \<in> NF_trs (Ru R)" by simp
  moreover have "r \<noteq> r \<cdot> ?\<sigma>"
    by (metis (no_types, lifting) xr Rep_perm_swap UnI2 comp_apply subst.cop_nil term.inject(1) term_subst_eq_rev y)
  ultimately show ?thesis using ucpdnf nf by metis
qed

end
