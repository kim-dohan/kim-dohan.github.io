(*
Author:  Alexander Lochmann <alexander.lochmann@uibk.ac.at> (2018)
License: LGPL (see file COPYING.LESSER)
*)
theory Ackbo_more
  imports Ackbo_wf
begin

context admissible_weight_fun_ac
begin

abbreviation ackbo_S where "ackbo_S \<equiv> {(x, y). ackbo x y}"
abbreviation NS where "NS \<equiv> ackbo_S \<union> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"

lemma ackbo_ce_compat: "ce_trs cn \<subseteq> ackbo_S \<inter> NS"
proof -
  obtain c n where cn: "cn = (c,n)" by force
  {
    fix s t :: "('f,'v) term"
    assume "(s,t) \<in> ce_trs cn"
    hence "s \<rhd> t" unfolding cn ce_trs.simps by auto
    then have "(s, t) \<in> ackbo_S" using ackbo_subterm_property by blast 
    then have "(s,t) \<in> ackbo_S \<inter> NS" by auto
  }
  thus ?thesis by auto
qed

lemma S_ce_compat: "ce_trs cn \<subseteq> ackbo_S" using ackbo_ce_compat by blast
lemma NS_ce_compat: "ce_trs cn \<subseteq> NS" using ackbo_ce_compat by blast

lemma ackbo_S_mono: "ctxt.closed ackbo_S"
  using ackbo_ctxt by blast

lemma ackbo_redpair: "mono_ce_af_redtriple_order ackbo_S NS NS full_af"
proof unfold_locales
  show "SN ackbo_S" using ackbo_strongly_normalizing unfolding SN_defs by blast
  show "subst.closed ackbo_S" using ackbo_subst by blast 
  show "subst.closed NS" by (simp add: \<open>subst.closed ackbo_S\<close> subst.closed_Un subst.closed_conversion subst_closed_rstep) 
  show "ctxt.closed NS" by (metis UnCI UnE ackbo_ctxt case_prodD case_prodI conversion_ctxt_closed ctxt.closedI mem_Collect_eq) 
  show "NS O ackbo_S \<subseteq> ackbo_S" by (metis ackbo_rel_compat_l ackbo_rel_trans le_sup_iff relcomp_distrib2 trans_O_iff)  
  show "ackbo_S O NS \<subseteq> ackbo_S" by (metis Un_subset_iff ackbo_rel_compat_r ackbo_rel_trans relcomp_distrib trans_O_iff) 
  show "trans ackbo_S" using S_trans unfolding trans_def by auto
  show "trans NS"
  proof -
    have "(ackbo_S::(('f, 'b) Term.term \<times> ('f, _) Term.term) set) O (ackbo_S \<union> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) \<union> ackbo_S = ackbo_S"
      by (meson \<open>ackbo_S O (ackbo_S \<union> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*) \<subseteq> ackbo_S\<close> subset_Un_eq)
    then show ?thesis
      by (simp add: ackbo_order_pair order_pair.NS_O_S(1) sup_commute sup_left_commute trans_O_iff)
  qed 
  show "refl NS" by (simp add: refl_on_def) 
  show "af_compatible full_af NS" by (rule full_af)
  show "ce_compatible NS" 
    using NS_ce_compat unfolding ce_compatible_def by blast
  show "ce_compatible ackbo_S"
    using S_ce_compat unfolding ce_compatible_def by blast
  show "ackbo_S \<subseteq> NS" by auto
  show "ctxt.closed ackbo_S" by (rule ackbo_S_mono)
qed

lemma NS_supteq: "s \<unrhd> t \<Longrightarrow> (s,t) \<in> NS"
  by (metis CollectI UnCI acconv_iff ackbo_subterm_property case_prodI subterm.le_imp_less_or_eq)

lemma ackbo_S_supt: "s \<rhd> t \<Longrightarrow> (s,t) \<in> ackbo_S"
  by (simp add: ackbo_subterm_property)
end
end
