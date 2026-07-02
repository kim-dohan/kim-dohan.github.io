(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Main result for general TRSs\<close>

theory LS_General
  imports 
    LS_Common
begin

locale weakly_layered_induct_general = weakly_layered_induct \<F> \<LL> \<R> rk
  for \<F> :: "('f \<times> nat) set" and \<LL> :: "('f, 'v :: infinite) mctxt set" and \<R> :: "('f, 'v) trs" and
      rk :: nat +
  fixes R :: "('f, 'v) term rel"
  assumes layered: "layered \<F> \<LL> \<R>"
  defines "R \<equiv> {}"
begin

sublocale layered using layered .

text \<open>{cite \<open>Lemma 4.34\<close> FMZvO15}\<close>

lemma mirror_step_preserves_base:
  assumes "s \<in> native_terms" "(B, ss) = base_decomp s" "((s, B), (t, C)) \<in> mirror_step"
  shows "C = MHole \<or> C = fst (base_decomp t)"
  using assms
proof -
  from mirror_step.cases[OF assms(3)] obtain l r p \<sigma> \<tau> where
    st: "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>" and
    BC: "(mctxt_term_conv B, mctxt_term_conv C) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>" by metis
  then have "t \<in> native_terms" by (force simp: rstep'_iff_rstep_r_p_s' intro!: native_terms_closed[OF assms(1)])
  with assms(1) have "s \<in> \<T>" "t \<in> \<T>" by (auto simp: native_terms_def)
  have "C \<le> mctxt_of_term t" using mirror_step_preserves_prefix[OF base_decomp_prefix[OF assms(2)] assms(3)] .
  have "num_holes (max_top s) = length (aliens s)" "(fill_holes (max_top s) (aliens s), t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    by (auto simp: fill_unfill_holes st max_top_prefix)
  with trs show ?thesis
  proof (cases rule: rewrite_cases_wf)
    case outer
    obtain \<tau>' N where N: "(mctxt_term_conv (max_top s), mctxt_term_conv N) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>'"
      "N = max_top t \<or> N = MHole" using C\<^sub>1[OF \<open>s \<in> \<T>\<close> \<open>t \<in> \<T>\<close> outer(1) st] by metis
    have *: "N \<le> mctxt_of_term t" "map_vars_mctxt f N \<le> mctxt_of_term (t \<cdot> (Var \<circ> f))" for f
      using map_vars_mctxt_mono[of N "mctxt_of_term t" f] N(2)
      by (auto simp: mctxt_of_term_var_subst max_top_prefix)
    let ?f = "\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole"
    let ?C = "fill_holes_mctxt N (map ?f (unfill_holes N t))"
    obtain \<sigma>' where BC': "(mctxt_term_conv B, mctxt_term_conv ?C) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>'"
    proof (cases rule: rewrite_balanced_aliens'[
      OF trs length_unfill_holes[OF max_top_prefix] length_unfill_holes[OF *(2)],
      of "s \<cdot> (Var \<circ> (from_option \<circ> Some))" "from_option \<circ> Some" l r p
         "\<sigma> \<circ>\<^sub>s (Var \<circ> (from_option \<circ> Some))" "\<tau>' \<circ>\<^sub>s (Var \<circ> map_option (from_option \<circ> Some))"
         "map_vars_term from_option \<circ> mctxt_term_conv \<circ> ?f \<circ> map_vars_term (the \<circ> to_option)"])
      case 1 show ?case using st
        by (auto simp: fill_unfill_holes max_top_prefix * intro: rstep_r_p_s'_stable)
    next
      case 2 show ?case using N(1)
        by (auto simp: max_top_var_subst mctxt_term_conv_map_vars_mctxt_subst intro: rstep_r_p_s'_stable)
    next
      note [simp] = * max_top_prefix map_vars_term_compose term.map_ident
      case (3 \<sigma>') show ?thesis using rstep_r_p_s'_stable[OF 3, of "Var \<circ> to_option"]
        apply (intro that[of "\<sigma>' \<circ>\<^sub>s (Var \<circ> to_option)"])
        apply (subst (asm) (1 2) subst_apply_mctxt_fill_holes, simp, simp)
        unfolding max_top_var_subst
        apply (subst (asm) (1 2) unfill_holes_var_subst, simp, simp)
        unfolding map_vars_term_eq[symmetric] subst_apply_mctxt_map_vars_mctxt_conv
        using arg_cong[OF assms(2), of fst]
        by (auto simp: base_decomp_def Let_def comp_def mctxt_term_conv_fill_holes_mctxt cong: if_cong)
    qed
    show ?thesis using N(2) rstep_r_p_s'_deterministic[OF trs BC BC', THEN arg_cong, of term_mctxt_conv]
    proof (elim disjE, goal_cases)
      case 1 then show ?case by (auto simp: base_decomp_def Let_def)
    next
      have [simp]:
        "rank t \<le> rk \<Longrightarrow> map (\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole) (aliens t) = map mctxt_of_term (aliens t)"
        using rank.simps[of t] \<open>t \<in> \<T>\<close> max_list_bound_set[of "map rank (aliens t)" rk] by auto
      case 2 then show ?case by (auto simp: base_decomp_def Let_def max_top_prefix fill_unfill_holes)
    qed
  next
    case (inner i ti)
    let ?f = "(\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole)"
    note [simp] = max_top_prefix
    note B = arg_cong[OF assms(2), of fst, unfolded base_decomp_def Let_def fst_conv]
    have rsi: "rank (aliens s ! i) \<le> rk" using inner(1,4) wf_trs_implies_fun_poss[OF trs BC]
      poss_append_fun_poss[of "hole_poss' (max_top s) ! i" "pos_diff p (hole_poss' (max_top s) ! i)" "mctxt_term_conv B"]
      by (auto split: if_splits simp: B
        mctxt_term_conv_fill_holes_mctxt subt_at_fill_holes[of _ "map_vars_mctxt _ _", unfolded hole_poss'_map_vars_mctxt])
    have "(mctxt_term_conv B, mctxt_term_conv (fill_holes_mctxt (max_top s) ((map ?f (aliens s))[i := mctxt_of_term ti]))) \<in> rstep_r_p_s' \<R> (l, r) p (\<sigma> \<circ>\<^sub>s (Var \<circ> Some))"
      using rstep_r_p_s'_mono[OF rstep_r_p_s'_stable[OF inner(3), of "Var \<circ> Some"], of "ctxt_of_pos_term (hole_poss' (max_top s) ! i) (mctxt_term_conv B)"]
        inner(1,4) rsi unfolding B
      apply (subst (asm) (1 2 3) mctxt_term_conv_fill_holes_mctxt, simp)
      apply (subst (asm) (1 2) replace_at_fill_holes[of "map_vars_mctxt _ _", unfolded hole_poss'_map_vars_mctxt], simp, simp)
      using list_update_id[of "map (mctxt_term_conv \<circ> ?f) (aliens s)" i]
        hole_poss_in_poss_fill_holes[of "map_vars_mctxt Some (max_top s)" _ i]
      by (auto simp: mctxt_term_conv_fill_holes_mctxt map_update simp del: list_update_id)
    note C = arg_cong[OF rstep_r_p_s'_deterministic[OF trs BC this], of term_mctxt_conv, unfolded term_mctxt_conv_inv]
    have "B \<in> shallow_context" "C \<in> shallow_context" using base_decomp_shallow[OF \<open>s \<in> \<T>\<close> assms(2)]
      shallow_context_closed[of B C] BC by (auto simp: rstep'_iff_rstep_r_p_s')
    have *: "j < num_holes (max_top s) \<Longrightarrow>
      hole_poss ((map ?f (aliens s))[i := mctxt_of_term ti] ! j) = hole_poss (map ?f (aliens s) ! j)" for j
      using inner(1) rsi by (auto simp: nth_list_update)
    have "hole_poss C = hole_poss B" by (force simp: B C * hole_poss_fill_holes_mctxt)
    moreover {
      have *: "max_top s \<le> max_top t" using inner(1,2) by (auto simp: topsC_def max_top_prefix)
      fix q assume p: "q \<in> hole_poss B"
      have "hole_poss B \<subseteq> hole_poss (max_top s)" using \<open>s \<in> native_terms\<close> arg_cong[OF assms(2), of fst]
        shallow_to_base_no_new_holes[of "max_top s" "aliens s", OF _ _ aliens_short_terms prod.collapse]
        shallow_context.intros[of "max_top s" "replicate (num_holes (max_top s)) MHole", OF _ _ _ refl]
        by (auto simp: set_replicate_conv_if fill_unfill_holes)
      then obtain j where j: "j < num_holes (max_top s)" "q = hole_poss' (max_top s) ! j"
        by (metis in_set_conv_nth p set_mp set_hole_poss'[of "max_top s"] length_hole_poss'[of "max_top s"])
      have "rank (aliens s ! j) > rk" using p j by (auto simp: B hole_poss_fill_holes_mctxt_conv split: if_splits)
      then have j': "i \<noteq> j" using rsi by auto
      let ?L = "mreplace_at (max_top s) q (subm_at (max_top t) (hole_poss' (max_top s) ! j))"
      have **: "q \<in> all_poss_mctxt (max_top s)" using j all_poss_mctxt_conv
        by (fastforce simp: set_hole_poss'[symmetric] j)
      moreover have ***: "q \<in> all_poss_mctxt ?L"
        using ** all_poss_mctxt_mreplace_atI1 by blast
      moreover have "mreplace_at (mctxt_of_term s) q (mctxt_of_term (aliens s ! j)) = mctxt_of_term s"
        using subsetD[OF all_poss_mctxt_mono[OF max_top_prefix] **]
        by (auto simp: subm_at_mctxt_of_term[symmetric] unfill_holes_conv[OF max_top_prefix] j)
      then have "?L \<le> mctxt_of_term s"
        using compare_mreplace_atI'[OF max_top_prefix[of s] less_eq_subm_at[OF _ max_top_prefix[of t]], of q q]
          * ** *** subsetD[OF all_poss_mctxt_mono[OF *], of q]
        unfolding inner(2) using inner(1) j j' replace_at_subm_at[of q "mctxt_of_term s"]
        by (auto simp: subm_at_fill_holes_mctxt mctxt_of_term_fill_holes' simp del: fill_holes_mctxt_map_mctxt_of_term_conv)
      ultimately have "subm_at (max_top t) q = MHole"
        using C\<^sub>2[OF max_top_layer max_top_layer * nth_mem[of _ "hole_poss' _", unfolded set_hole_poss' length_hole_poss'], of j]
          less_eq_subm_at[OF _ max_topC_props(2), of q "?L" "mctxt_of_term s"]
          inner(1) j subm_at_hole_poss[unfolded set_hole_poss'[symmetric], OF nth_mem, of _ "max_top s"]
        by (auto simp: topsC_def mctxt_order_bot.bot_unique)
      then have "q \<in> hole_poss (max_top t)" using subsetD[OF all_poss_mctxt_mono[OF *], OF **]
        by (induct ("max_top t") arbitrary: q; case_tac p) auto
      then obtain k where k: "k < num_holes (max_top t)" "q = hole_poss' (max_top t) ! k"
        by (metis in_set_conv_nth p set_mp set_hole_poss'[of "max_top t"] length_hole_poss'[of "max_top t"])
      have "t |_ hole_poss' (max_top s) ! j = s |_ hole_poss' (max_top s) ! j" using \<open>i \<noteq> j\<close>
        by (auto simp: inner(2) subt_at_fill_holes unfill_holes_conv j(1) k(1))
      then have "aliens t ! k = aliens s ! j" using \<open>i \<noteq> j\<close>
        by (auto simp: unfill_holes_conv j(1) k(1) j(2) k(2)[symmetric])
      then have "rank (aliens t ! k) > rk" using \<open>rank (aliens s ! j) > rk\<close> by simp
      then have "q \<in> hole_poss (fst (base_decomp t))"
        by (force simp: base_decomp_def Let_def k hole_poss_fill_holes_mctxt)
    }
    ultimately have "hole_poss C \<subseteq> hole_poss (fst (base_decomp t))" by blast
    moreover have "C \<in> shallow_context" using base_decomp_shallow[OF \<open>s \<in> \<T>\<close> assms(2)]
      shallow_context_closed[of B C] BC by (auto simp: rstep'_iff_rstep_r_p_s')
    then have "C \<le> fst (base_decomp t)"
      by (metis mirror_step_preserves_prefix base_decomp_prefix assms(2,3) base_decomp_max \<open>t \<in> native_terms\<close> prod.collapse)
    ultimately show ?thesis by (simp add: prefix_and_fewer_holes_implies_equal_mctxt)
  qed
qed

lemma mirror_steps_MHole_empty:
  "((s, MHole), (t, C)) \<in> mirror_step\<^sup>* \<Longrightarrow> t = s \<and> C = MHole"
proof (induct "(t, C)" arbitrary: t C rule: rtrancl_induct)
  case (step tC) show ?case using step(2,3) NF_Var'[OF trs]
    by (cases tC) (force elim!: mirror_step.cases simp: rstep'_iff_rstep_r_p_s')
qed auto

lemma short_short_peak:
  assumes "(s, t) \<in> short_step_s s0" "(s, u) \<in> short_step_s s1"
  shows "(t, u) \<in> ((\<Union>i\<in>under R s0. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>* O (short_step_s s1)\<^sup>= O
    ((\<Union>i\<in>under R s0 \<union> under R s1. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>* O
    ((short_step_s s0)\<inverse>)\<^sup>= O ((\<Union>i\<in>under R s1. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>*"
proof -
  obtain B ss C D E v where s: "s \<in> native_terms" "(B, ss) = base_decomp s" and
    st: "((s, B), (t, C)) \<in> mirror_step\<^sup>*" "C \<in> shallow_context" "C \<le> mctxt_of_term t" and
    su: "((s, B), (u, D)) \<in> mirror_step\<^sup>*" "D \<in> shallow_context" "D \<le> mctxt_of_term u" and
    tv: "t \<in> native_terms" "(s1, t) \<in> (rstep \<R>)\<^sup>*" "((t, C), (v, E)) \<in> mirror_step\<^sup>*" and
    uv: "u \<in> native_terms" "(s0, u) \<in> (rstep \<R>)\<^sup>*" "((u, D), (v, E)) \<in> mirror_step\<^sup>*"
    using short_short_pre[OF assms] by metis
  { fix t C assume "((s, B), (t, C)) \<in> mirror_step\<^sup>*"
    then have "C = MHole \<or> C = fst (base_decomp t)" using s(1,2)
    proof (induct "(s, B)" arbitrary: s B ss rule: converse_rtrancl_induct)
      case base show ?case using base(2)[symmetric] by simp
    next
      case (step sB)
      obtain s' B' where sB: "sB = (s', B')" by (metis prod.collapse)
      show ?case using native_terms_closed[OF _ mirror_step_imp_rstep[OF step(1)]]
        mirror_step_preserves_base[of s B ss "fst sB" "snd sB"]
        step(1,2,4,5) step(3)[OF prod.collapse[symmetric], of "snd (base_decomp (fst sB))"]
        mirror_steps_MHole_empty[of "fst sB" t C]
        by (simp add: sB) fastforce
    qed
  } note * = this
  have "(t, v) \<in> short_step_s s1" using *[OF st(1)] tv mirror_steps_MHole_empty[of t v E]
    short_step_sI[OF tv(2,1) prod.collapse, of v "fst (base_decomp t)"]
    short_step_sI[OF tv(2,1) prod.collapse, of v E] by auto
  moreover have "(u, v) \<in> short_step_s s0" using *[OF su(1)] uv mirror_steps_MHole_empty[of u v E]
    short_step_sI[OF uv(2,1) prod.collapse, of v "fst (base_decomp u)"]
    short_step_sI[OF uv(2,1) prod.collapse, of v E] by auto
  ultimately have "(t, u) \<in> (short_step_s s1)\<^sup>= O ((short_step_s s0)\<inverse>)\<^sup>=" by auto
  then show ?thesis by regexp
qed

sublocale weakly_layered_induct_dd
  using short_short_peak by unfold_locales (auto simp: R_def)

end (* weakly_layered_induct_general *)

sublocale layered \<subseteq> layered_cr
proof (standard, unfold rstep_eq_rstep', intro CR_main_lemma[where R = "\<lambda>_. {}"], goal_cases _ step)
  case (step rk)
  then interpret weakly_layered_induct_general \<F> \<LL> \<R> rk "{}" by (unfold_locales) simp_all
  show ?case by unfold_locales
qed simp_all

lemmas (in layered) CR = CR

text \<open>{cite \<open>Theorem 4.6\<close> FMZvO15}\<close>
thm layered.CR

end (* theory LS_General *)
