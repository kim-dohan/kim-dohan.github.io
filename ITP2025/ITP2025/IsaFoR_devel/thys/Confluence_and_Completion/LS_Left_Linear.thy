(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Main result for left-linear TRSs\<close>

theory LS_Left_Linear
  imports 
    LS_Common
begin

locale weakly_layered_induct_left_linear = weakly_layered_induct \<F> \<LL> \<R> rk
  for \<F> :: "('f \<times> nat) set" and \<LL> :: "('f, 'v :: infinite) mctxt set" and \<R> :: "('f, 'v) trs" and
      rk :: nat +
  fixes R :: "('f, 'v) term rel"
  assumes ll: "left_linear_trs \<R>"
  defines "R \<equiv> {}"
begin

lemma expand_mirror_step:
  assumes "C' \<in> shallow_context" "C \<le> C'" "C' \<le> mctxt_of_term s" "((s, C), (t, D)) \<in> mirror_step"
  obtains D' where "D' \<in> shallow_context" "D \<le> D'" "D' \<le> mctxt_of_term t" "((s, C'), (t, D')) \<in> mirror_step"
proof -
  obtain l r p \<sigma> \<tau> where *: "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>"
    using mirror_step.cases[OF assms(4)] by metis
  then have "linear_term l" using ll by (force simp: left_linear_trs_def case_prod_unfold)
  moreover have 2: "p \<in> all_poss_mctxt C" using *(2)
    by (metis hole_pos_poss poss_mctxt_term_conv rstep_r_p_s'.cases)
  moreover then have 3: "subm_at C p \<le> subm_at C' p" "p \<in> all_poss_mctxt C'"
    using \<open>C \<le> C'\<close> all_poss_mctxt_mono[OF \<open>C \<le> C'\<close>] by (auto simp: less_eq_subm_at) 
  moreover have "mctxt_term_conv C |_ p = l \<cdot> \<tau>" using *(2) by auto
  ultimately obtain \<tau>' where 4: "mctxt_term_conv C' |_ p = l \<cdot> \<tau>'"
    using linear_weak_match[of l "mctxt_term_conv C' |_ p" "mctxt_term_conv C |_ p" \<tau>]
      weak_match_mctxt_term_conv_mono[of "subm_at C p" "subm_at C' p"]
    by (auto simp: left_linear_trs_def case_prod_unfold subt_at_mctxt_term_conv)
  let ?d' = "replace_at (mctxt_term_conv C') p (r \<cdot> \<tau>')"
  have 5: "(replace_at (mctxt_term_conv C') p (l \<cdot> \<tau>'),?d') \<in> rstep_r_p_s' \<R> (l, r) p \<tau>'"
    by (metis *(2) 3(2) fst_conv hole_pos_ctxt_of_pos_term poss_mctxt_term_conv prod.sel(2) rstep_r_p_s'E rstep_r_p_s'I)
  have "term_mctxt_conv ?d' \<in> shallow_context"
    by (metis 3(2) 4 5 rstep'_iff_rstep_r_p_s' shallow_context_closed[OF assms(1)] mctxt_term_conv_inv ctxt_supt_id poss_mctxt_term_conv)
  moreover have "((s, C'), t, term_mctxt_conv ?d') \<in> mirror_step"
    using 3 5 *(1) by (auto simp: 4[symmetric] ctxt_supt_id)
  moreover have "D \<le> term_mctxt_conv ?d'"
    using 3 5 *(2) assms(2) by (auto simp: 4[symmetric] ctxt_supt_id mirrored_steps_preserve_prefix)
  ultimately show ?thesis using assms(3)
    by (auto intro!: that[of "term_mctxt_conv ?d'"] simp: mirror_step_preserves_prefix)
qed

lemma short_step_from_mirror_steps:
  assumes "C \<in> shallow_context"
    "C \<le> mctxt_of_term s" "(s0, s) \<in> (rstep \<R>)\<^sup>*" "s \<in> native_terms" "((s, C), (t, D)) \<in> mirror_step\<^sup>*"
  shows "(s, t) \<in> short_step_s s0"
proof -
  obtain B ss where B: "(B, ss) = base_decomp s" by (metis prod.collapse)
  then have "B \<in> shallow_context" "C \<le> B" "B \<le> mctxt_of_term s" using assms(1,2,4)
    by (auto simp: native_terms_def base_decomp_shallow base_decomp_max base_decomp_prefix)
  with assms(5)
  obtain D' where "((s, B), (t, D')) \<in> mirror_step\<^sup>*"
  proof (induct "(s, C)" arbitrary: s B C thesis rule: converse_rtrancl_induct)
    case (step z) show ?case using step(3)[OF prod.collapse[symmetric]]
      expand_mirror_step[OF step(5,6,7), of "fst z" "snd z"] step(1,4)
      by (metis converse_rtrancl_into_rtrancl prod.collapse)
  qed auto
  from short_step_sI[OF assms(3,4) B this] show ?thesis .
qed

lemma short_short_peak:
  assumes "(s, t) \<in> short_step_s s0" "(s, u) \<in> short_step_s s1"
  shows "(t, u) \<in> ((\<Union>i\<in>under R s0. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>* O (short_step_s s1)\<^sup>= O
    ((\<Union>i\<in>under R s0 \<union> under R s1. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>* O
    ((short_step_s s0)\<inverse>)\<^sup>= O ((\<Union>i\<in>under R s1. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>*"
proof -
  obtain C D E v where "C \<in> shallow_context" "C \<le> mctxt_of_term t"
     "D \<in> shallow_context" "D \<le> mctxt_of_term u"
     "t \<in> native_terms" "(s1, t) \<in> (rstep \<R>)\<^sup>*" "((t, C), v, E) \<in> mirror_step\<^sup>*"
     "u \<in> native_terms" "(s0, u) \<in> (rstep \<R>)\<^sup>*" "((u, D), v, E) \<in> mirror_step\<^sup>*"
    using short_short_pre[OF assms, of thesis] by blast
  then have "(t, v) \<in> short_step_s s1" "(u, v) \<in> short_step_s s0"
    by (auto intro: short_step_from_mirror_steps)
  then have "(t, u) \<in> (short_step_s s1)\<^sup>= O ((short_step_s s0)\<inverse>)\<^sup>=" by blast
  then show ?thesis by regexp
qed

sublocale weakly_layered_induct_dd
  using short_short_peak by unfold_locales (auto simp: R_def)

end

sublocale weakly_layered \<subseteq> weakly_layered_cr_ll
proof (standard, unfold rstep_eq_rstep', intro CR_main_lemma[where R = "\<lambda>_. {}"], goal_cases _ step)
  case (step rk)
  then interpret weakly_layered_induct_left_linear \<F> \<LL> \<R> rk "{}" by (unfold_locales) simp_all
  show ?case by unfold_locales
qed simp_all

lemmas (in weakly_layered) CR_ll = CR_ll

text \<open>{cite \<open>Theorem 4.1\<close> FMZvO15}\<close>
thm weakly_layered.CR_ll

end
