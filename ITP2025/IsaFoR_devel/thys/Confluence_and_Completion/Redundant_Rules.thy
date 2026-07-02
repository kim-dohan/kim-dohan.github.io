(*
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Redundant_Rules
imports
  First_Order_Rewriting.Trs
begin

lemma rsteps_union_simulate:
  assumes "\<forall>(l, r) \<in> S. (l, r) \<in> (rstep R)^*"
  shows "(rstep R)^* = (rstep (R \<union> S))^*"
proof
  show "(rstep R)^* \<subseteq> (rstep (R \<union> S))^*"
    using rstep_mono[of R "R \<union> S"] rtrancl_mono by blast
  show "(rstep R)^* \<supseteq> (rstep (R \<union> S))^*"
  proof
    fix s t
    assume "(s, t) \<in> (rstep (R \<union> S))^*"
    then show "(s, t) \<in> (rstep R)^*"
    proof (induct rule: rtrancl_induct)
      case (step u t)
      then obtain l r C \<sigma> where ut: "(u, t) \<in> rstep_r_c_s (l, r) C \<sigma>" and lr: "(l, r) \<in> R \<union> S"
        unfolding rstep_iff_rstep_r_c_s by auto
      from lr have "(u, t) \<in> (rstep R)^*"
      proof
        assume "(l, r) \<in> R"
        with ut have "(u, t) \<in> rstep R" unfolding rstep_iff_rstep_r_c_s by auto
        then show ?thesis by auto
      next
        assume "(l, r) \<in> S"
        with assms have "(l, r) \<in> (rstep R)^*" by auto
        moreover from ut have "u = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>" unfolding rstep_r_c_s_def by auto
        ultimately show ?thesis using rsteps_closed_ctxt rsteps_closed_subst by metis
      qed
      then show ?case using step(3) by auto
    qed auto
  qed
qed

corollary redundant_rules:
  assumes "\<forall>(l, r) \<in> S. (l, r) \<in> (rstep R)^*"
  shows "CR (rstep (R \<union> S)) \<longleftrightarrow> CR (rstep R)"
  unfolding CR_on_def join_def rtrancl_converse
  using rsteps_union_simulate[OF assms] by auto

lemma redundant_rules_removal:
  assumes "\<And> l r. (l, r) \<in> S \<Longrightarrow> (l, r) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  and "CR (rstep R)"
  shows "CR (rstep (R \<union> S))"
  using conv_union_simulate[OF assms(1)]
    CR_imp_conversionIff_join[OF assms(2)]
    join_mono[OF rstep_mono[of R "R \<union> S"]]
  unfolding CR_iff_conversion_imp_join
  by simp

end
