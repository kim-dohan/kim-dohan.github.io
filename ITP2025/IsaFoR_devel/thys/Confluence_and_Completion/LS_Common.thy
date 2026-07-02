(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

text \<open>Shared analysis for main results\<close>

theory LS_Common
  imports 
    LS_Basics 
    "Decreasing-Diagrams-II.Decreasing_Diagrams_II"
    TRS.More_Abstract_Rewriting
begin

text \<open>"We fix r and assume terms with rank at most r to be confluent."\<close>

locale weakly_layered_induct = weakly_layered \<F> \<LL> \<R>
  for \<F> :: "('f \<times> nat) set" and \<LL> :: "('f, 'v :: infinite) mctxt set" and \<R> :: "('f, 'v) trs" +
  fixes rk :: nat
  assumes IH_rk: "CR_on (rstep' \<R>) {t \<in> \<T>. rank t \<le> Suc rk}"
begin

text \<open>{cite \<open>Definition 4.7\<close> FMZvO15}, native and short terms\<close>

definition native_terms :: "('f, 'v) term set" where
  "native_terms = {t \<in> \<T>. rank t \<le> Suc (Suc rk)}"

definition short_terms :: "('f, 'v) term set" where
  "short_terms = {t \<in> \<T>. rank t \<le> Suc rk}"

definition shorter_terms :: "('f, 'v) term set" where
  "shorter_terms = {t \<in> \<T>. rank t \<le> rk}"

lemma shorter_imp_short[simp]:
  "t \<in> shorter_terms \<Longrightarrow> t \<in> short_terms"
  by (auto simp: short_terms_def shorter_terms_def)

lemma native_terms_closed [simp]:
  "s \<in> native_terms \<Longrightarrow> (s, t) \<in> rstep' \<R> \<Longrightarrow> t \<in> native_terms"
  unfolding native_terms_def using rank_preservation \<T>_preservation le_trans by blast

lemma short_terms_closed [simp]:
  "s \<in> short_terms \<Longrightarrow> (s, t) \<in> rstep' \<R> \<Longrightarrow> t \<in> short_terms"
  unfolding short_terms_def using rank_preservation \<T>_preservation le_trans by blast

lemma short_terms_closed':
  assumes "s \<in> short_terms" "(s, t) \<in> (rstep' \<R>)\<^sup>*" shows "t \<in> short_terms"
  using assms(2,1) by (induct t rule: rtrancl_induct) simp_all

lemma shorter_terms_closed:
  "s \<in> shorter_terms \<Longrightarrow> (s, t) \<in> rstep' \<R> \<Longrightarrow> t \<in> shorter_terms"
  unfolding shorter_terms_def using rank_preservation \<T>_preservation le_trans by blast

lemma shorter_terms_closed':
  assumes "s \<in> shorter_terms" "(s, t) \<in> (rstep' \<R>)\<^sup>*" shows "t \<in> shorter_terms"
  using assms(2,1) by (induct t rule: rtrancl_induct) (simp_all add: shorter_terms_closed)

lemma shorter_terms_short:
  "shorter_terms \<subseteq> short_terms"
  by auto

lemma aliens_short_terms:
  assumes "t \<in> native_terms"
  shows "set (aliens t) \<subseteq> short_terms"
proof -
  note * = assms[unfolded native_terms_def arg_cong[OF rank.simps, of "(\<le>)"]]
  { fix t' assume t': "t' \<in> set (aliens t)"
    have "t' \<in> \<T>" using * supt_imp_funas_term_subset[OF unfill_holes_max_top_subt[of t t']] t'
      by (auto simp: \<T>_def)
    moreover have "rank t' \<le> Suc rk" using t' *
      by auto (metis (no_types, lifting) dual_order.trans imageI max_list set_map)
    moreover note calculation
  }
  then show ?thesis by (auto simp: short_terms_def)
qed

inductive_set mirror_step :: "(('f, 'v) term \<times> ('f, 'v) mctxt) rel" where
  [intro]: "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma> \<Longrightarrow>
    (mctxt_term_conv L, mctxt_term_conv M) \<in> rstep_r_p_s' \<R> (l, r) p \<tau> \<Longrightarrow> ((s, L), (t, M)) \<in> mirror_step"

declare mirror_step.cases[elim]

lemma mirror_step_to_max_top:
  assumes "s \<in> \<T>" "L \<in> tops s" "((s, L), (t, M)) \<in> mirror_step"
  obtains M' where "M' \<in> \<LL>" "((s, max_top s), (t, M')) \<in> mirror_step"
proof -
  obtain l r p \<sigma> \<tau> where *: "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    "(mctxt_term_conv L, mctxt_term_conv M) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>"
    using mirror_step.cases[OF assms(3)] by metis
  have "t \<in> \<T>" using \<T>_preservation[OF assms(1)] *(1) rstep'_iff_rstep_r_p_s' by metis
  from *(2) obtain C where "(l, r) \<in> \<R>" "p = hole_pos C" "mctxt_term_conv L = C\<langle>l \<cdot> \<tau>\<rangle>" by auto
  then have "p \<in> fun_poss_mctxt L" using hole_pos_in_filled_fun_poss[of "l \<cdot> \<tau>" C Var] trs
    by (force simp: wf_trs_def' fun_poss_mctxt_def)
  then have "p \<in> fun_poss_mctxt (max_top s)" using max_topC_props(2)[OF assms(2)] fun_poss_mctxt_mono by metis
  from W[OF \<open>s \<in> \<T>\<close> \<open>t \<in> \<T>\<close> this *(1)] obtain M' \<tau>' where
    **: "M' \<in> \<LL>" "(mctxt_term_conv (max_top s), mctxt_term_conv M') \<in> rstep_r_p_s' \<R> (l, r) p \<tau>'"
    by metis
  moreover have "((s, max_top s), (t, M')) \<in> mirror_step" using *(1) **(2) by auto
  ultimately show ?thesis using **(1) by (intro that)
qed

lemma mirrored_steps_preserve_prefix:
  fixes C :: "('f, 'v) mctxt"
  assumes "C \<le> C'"
    "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>"
    "(mctxt_term_conv C', mctxt_term_conv D') \<in> rstep_r_p_s' \<R> (l, r) p \<tau>'"
  shows "D \<le> D'"
proof -
  note 1 = assms(3,2)
  have 2: "num_holes C = length (unfill_holes_mctxt C C')" "l \<cdot> \<tau>' = mctxt_term_conv (fill_holes_mctxt C (unfill_holes_mctxt C C')) |_ p"
    using assms(1,3) by (auto simp: fill_unfill_holes_mctxt)
  from rewrite_aliens_mctxt[OF trs 1(2) this] obtain Ds where
    3: "num_holes D = length Ds" "(mctxt_term_conv (fill_holes_mctxt C (unfill_holes_mctxt C C')), mctxt_term_conv (fill_holes_mctxt D Ds)) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>'"
    by metis
  with fill_holes_mctxt_suffix[OF this(1)[symmetric]] this(2) have [simp]: "D' = fill_holes_mctxt D Ds"
    using 2(1) rstep_r_p_s'_deterministic[OF trs 1(1)] assms(1)
    by (simp add: fill_unfill_holes_mctxt) (metis term_mctxt_conv_inv) 
  show ?thesis using 3(1) 1(2) assms(1)
    by (simp add: mrstep.simps rstep'_iff_rstep_r_p_s')
qed

lemma mirror_step_preserves_prefix:
  assumes "C \<le> mctxt_of_term s" "((s, C), (t, D)) \<in> mirror_step"
  shows "D \<le> mctxt_of_term t"
proof -
  from assms(2) obtain l r p \<sigma> \<tau> where
    1: "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>" "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>" by auto
  have "(mctxt_term_conv (mctxt_of_term s),mctxt_term_conv (mctxt_of_term t)) \<in> rstep_r_p_s' \<R> (l, r) p (\<sigma> \<circ>\<^sub>s (Var \<circ> Some))"
    using rstep_r_p_s'_stable[OF 1(1), of "Var \<circ> Some"] by auto
  from mirrored_steps_preserve_prefix[OF assms(1) 1(2) this] show ?thesis .
qed

lemma mirror_steps_preserve_prefix:
  assumes "C \<le> mctxt_of_term s" "((s, C), (t, D)) \<in> mirror_step\<^sup>*"
  shows "D \<le> mctxt_of_term t"
  using assms(2,1)
proof (induct "(t, D)" arbitrary: t D rule: rtrancl_induct)
  case (step tD)
  then show ?case using mirror_step_preserves_prefix[of "snd tD" "fst tD" t D] by auto
qed auto

lemma mirror_step_aliens_mono:
  assumes "length ss = num_holes L" "length ts = num_holes M"
    "((fill_holes L ss, L), (fill_holes M ts, M)) \<in> mirror_step"
  shows "set ts \<subseteq> set ss"
proof -
  from assms(3) obtain l r p \<sigma> \<tau> where
    1: "(fill_holes L ss, fill_holes M ts) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
       "(mctxt_term_conv L, mctxt_term_conv M) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>" by auto
  obtain ts' where ts': "num_holes M = length ts'" "set ts' \<subseteq> set ss"
    "(fill_holes L ss, fill_holes M ts') \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    using 1(1) assms(1) rewrite_aliens[OF trs 1(2), of ss \<sigma> thesis] by auto 
  have "fill_holes M ts = fill_holes M ts'" by (metis 1(1) ts'(3) trs rstep_r_p_s'_deterministic)
  from arg_cong[OF this, of "unfill_holes M"] show ?thesis
    using ts'(1,2) assms(2) by (auto simp: unfill_fill_holes)
qed

lemma mirror_step_stable:
  assumes "length ss = num_holes L" "length ts = num_holes M"
    "((fill_holes L ss, L), (fill_holes M ts, M)) \<in> mirror_step"
  shows "((fill_holes L (map f ss), L), (fill_holes M (map f ts), M)) \<in> mirror_step"
  by (metis assms(3) rewrite_balanced_aliens'[OF trs assms(1,2)] mirror_step.simps)

lemma mirror_step_imp_rstep:
  "(sL, tM) \<in> mirror_step \<Longrightarrow> (fst sL , fst tM) \<in> rstep' \<R>"
  by (cases sL; cases tM) (auto 0 5 simp: rstep'_iff_rstep_r_p_s')

lemma mirror_step_imp_rstep':
  "(sL, tM) \<in> mirror_step \<Longrightarrow> (mctxt_term_conv (snd sL) , mctxt_term_conv (snd tM)) \<in> rstep' \<R>"
  by (cases sL; cases tM) (auto 0 5 simp: rstep'_iff_rstep_r_p_s')

lemma mirror_steps_imp_rsteps:
  "((s, L), (t, M)) \<in> mirror_step\<^sup>* \<Longrightarrow> (s, t) \<in> (rstep' \<R>)\<^sup>*"
  by (induct "(s, L)" "(t, M)" arbitrary: t M rule: rtrancl.induct)
    (force dest!: mirror_step_imp_rstep intro: rtrancl_into_rtrancl)+

lemma mirror_steps_imp_rsteps':
  "((s, L), (t, M)) \<in> mirror_step\<^sup>* \<Longrightarrow> (mctxt_term_conv L, mctxt_term_conv M) \<in> (rstep' \<R>)\<^sup>*"
  by (induct "(s, L)" "(t, M)" arbitrary: t M rule: rtrancl.induct)
    (force dest!: mirror_step_imp_rstep' intro: rtrancl_into_rtrancl)+

text \<open>{cite \<open>Definition 4.8\<close> FMZvO15}, decomposition into base context and base vector\<close>

definition base_decomp :: "('f, 'v) term \<Rightarrow> ('f, 'v) mctxt \<times> ('f, 'v) term list" where
  "base_decomp t = (let M = max_top t in let as = unfill_holes M t in
    (fill_holes_mctxt M (map (\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole) as),
     filter (\<lambda>t. \<not> rank t \<le> rk) as))"

text \<open>{cite \<open>Definition 4.10\<close> FMZvO15}, short step\<close>

inductive_set short_step :: "('f, 'v) term rel" where
  "s \<in> native_terms \<Longrightarrow>
   (B, ss) = base_decomp s \<Longrightarrow>
   ((s, B), (t, C)) \<in> mirror_step\<^sup>* \<Longrightarrow> (s, t) \<in> short_step"

lemmas short_stepI = short_step.intros[unfolded rtranclp_rtrancl_eq case_prod_unfold prod.collapse Collect_mem_eq]
lemmas short_stepE = short_step.cases[unfolded rtranclp_rtrancl_eq case_prod_unfold prod.collapse Collect_mem_eq]

inductive_set short_step_s :: "('f, 'v) term \<Rightarrow> ('f, 'v) term rel" for s0 where
  "(s0, s) \<in> (rstep \<R>)\<^sup>* \<Longrightarrow>
   s \<in> native_terms \<Longrightarrow>
   (B, ss) = base_decomp s \<Longrightarrow>
   ((s, B), (t, C)) \<in> mirror_step\<^sup>* \<Longrightarrow> (s, t) \<in> short_step_s s0"

lemmas short_step_sI = short_step_s.intros[unfolded rtranclp_rtrancl_eq case_prod_unfold prod.collapse Collect_mem_eq]
lemmas short_step_sE = short_step_s.cases[unfolded rtranclp_rtrancl_eq case_prod_unfold prod.collapse Collect_mem_eq]

lemma short_step_s_imp_short_step:
  "(s, t) \<in> short_step_s s0 \<Longrightarrow> (s, t) \<in> short_step"
  by (auto intro: short_stepI elim: short_step_sE)

lemma short_step_implies_short_step_s:
  assumes "(s, t) \<in> short_step"
  obtains s0 where "(s, t) \<in> short_step_s s0"
  using short_stepE[OF assms] short_step_sI rtrancl_refl by metis

lemma short_step_iff_short_step_s:
  "(s, t) \<in> short_step \<longleftrightarrow> (\<exists>s0. (s, t) \<in> short_step_s s0)"
  by (auto intro: short_step_s_imp_short_step elim: short_step_implies_short_step_s)

text \<open>{cite \<open>Definition 4.11\<close> FMZvO15}, tall step\<close>

inductive_set tall_step :: "('f, 'v) term rel" where
  "s \<in> native_terms \<Longrightarrow>
   (B, ss) = base_decomp s \<Longrightarrow>
   length ts = num_holes B \<Longrightarrow> t = fill_holes B ts \<Longrightarrow>
   (\<And>i. i < num_holes B \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*) \<Longrightarrow>
   (s, t) \<in> tall_step"

inductive_set tall_step_i :: "nat \<Rightarrow> ('f, 'v) term rel" for \<iota> where
  "(B, ss) = base_decomp s \<Longrightarrow>
   s \<in> native_terms \<Longrightarrow>
   length ts = num_holes B \<Longrightarrow> t = fill_holes B ts \<Longrightarrow>
   (\<And>i. i < num_holes B \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*) \<Longrightarrow>
   \<iota> = imbalance ts \<Longrightarrow>
   (s, t) \<in> tall_step_i \<iota>"

lemma tall_step_i_imp_tall_step:
  "(s, t) \<in> tall_step_i \<iota> \<Longrightarrow> (s, t) \<in> tall_step"
  by (auto intro: tall_step.intros elim: tall_step_i.cases)

lemma tall_step_implies_tall_step_i:
  assumes "(s, t) \<in> tall_step"
  obtains \<iota> where "(s, t) \<in> tall_step_i \<iota>"
  using tall_step.cases[OF assms] tall_step_i.intros by metis

lemma tall_step_iff_tall_step_i:
  "(s, t) \<in> tall_step \<longleftrightarrow> (\<exists>\<iota>. (s, t) \<in> tall_step_i \<iota>)"
  by (auto intro: tall_step_i_imp_tall_step elim: tall_step_implies_tall_step_i)

lemma short_terms_rsteps:
  assumes "s \<in> short_terms" "(s, t) \<in> (rstep' \<R>)\<^sup>*"
  shows "t \<in> short_terms \<and> (s, t) \<in> (Restr (rstep' \<R>) short_terms)\<^sup>*"
  using rtrancl_on_iff_rtrancl_restr[OF _ assms(2,1)] short_terms_closed by metis

lemma native_terms_rsteps:
  assumes "s \<in> native_terms" "(s, t) \<in> (rstep' \<R>)\<^sup>*"
  shows "t \<in> native_terms \<and> (s, t) \<in> (Restr (rstep' \<R>) native_terms)\<^sup>*"
  using rtrancl_on_iff_rtrancl_restr[OF _ assms(2,1)] native_terms_closed by metis

lemma short_sequence_rsteps:
  assumes "length ts = length ss" "set ss \<subseteq> short_terms"
    "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*"
  shows "set ts \<subseteq> short_terms"
    "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (Restr (rstep' \<R>) short_terms)\<^sup>*"
  using assms short_terms_rsteps[OF subsetD, OF _ nth_mem] by (auto simp: in_set_conv_nth)

lemma IH_rk':
  "CR (Restr (rstep' \<R>) short_terms)"
  using IH_rk short_terms_rsteps[OF _ r_into_rtrancl]
  by (subst CR_on_iff_CR_Restr[symmetric]) (auto simp: short_terms_def[symmetric])

text \<open>{cite \<open>Lemma 4.15\<close> FMZvO15}\<close>

lemma balance_short_sequences:
  assumes "length ts = length ss" "length us = length ss"
    "set ss \<subseteq> short_terms"
    "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*"
    "\<And>i. i < length ss \<Longrightarrow> (ss ! i, us ! i) \<in> (rstep' \<R>)\<^sup>*"
  obtains (vs) vs where
    "length vs = length ss"
    "\<And>i. i < length ss \<Longrightarrow> (ts ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
    "\<And>i. i < length ss \<Longrightarrow> (us ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
    "ts \<propto> vs" "us \<propto> vs"
    "set ts \<subseteq> short_terms" "set us \<subseteq> short_terms" "set vs \<subseteq> short_terms"
proof -
  let ?R' = "Restr (rstep' \<R>) short_terms"
  note * = rtrancl_mono[of ?R' "rstep' \<R>", OF Int_lower1, THEN subsetD]
  from assms have "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> ?R'\<^sup>*"
    "\<And>i. i < length ss \<Longrightarrow> (ss ! i, us ! i) \<in> ?R'\<^sup>*"
    and s: "set ts \<subseteq> short_terms" "set us \<subseteq> short_terms"
    using short_sequence_rsteps by meson+
  from balance_sequences[OF IH_rk' assms(1,2) this(1,2)]
  obtain vs where "length vs = length ss"
    "\<And>i. i < length ss \<Longrightarrow> (ts ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
    "\<And>i. i < length ss \<Longrightarrow> (us ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
    "ts \<propto> vs" "us \<propto> vs" 
    by (metis *)
  moreover from this have
    "set vs \<subseteq> short_terms" using short_sequence_rsteps[of vs ts] assms(1) s by simp
  ultimately show ?thesis using s by (intro vs)
qed

text \<open>{cite \<open>Definition 4.17\<close> FMZvO15}, shallow context\<close>

inductive_set shallow_context :: "('f, 'v) mctxt set" where
  "L \<in> \<LL> \<Longrightarrow> length Cs = num_holes L \<Longrightarrow> set Cs \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms
   \<Longrightarrow> C = fill_holes_mctxt L Cs \<Longrightarrow> C \<in> shallow_context" 

lemma funas_shallow_context:
  "C \<in> shallow_context \<Longrightarrow> funas_mctxt C \<subseteq> \<F>"
using \<LL>_sig by (force elim!: shallow_context.cases simp: \<C>_def \<T>_def shorter_terms_def)

lemma base_decomp_shallow':
  assumes "t \<in> \<T>" "(B, ts) = base_decomp t"
  obtains Ds where "length Ds = num_holes (max_top t)"
    and "set Ds \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms"
    and "B = fill_holes_mctxt (max_top t) Ds"
proof -
  let ?ts = "map (\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole) (aliens t)"
  have "length ?ts = num_holes (max_top t)"
    using assms by (auto intro!: length_unfill_holes simp: max_topC_prefix)
  moreover have "set ?ts \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms"
    using assms subset_trans[OF supteq_imp_funas_term_subset[OF unfill_holes_subt[OF max_topC_prefix]], of _ t \<F>]
    by (force simp: base_decomp_def Let_def image_def \<T>_def shorter_terms_def)
  moreover have "B = fill_holes_mctxt (max_top t) ?ts"
    using assms by (auto simp: base_decomp_def Let_def)
  ultimately show ?thesis ..
qed

lemma base_decomp_shallow:
  assumes "t \<in> \<T>" "(B, ts) = base_decomp t"
  shows "B \<in> shallow_context"
  by (metis assms shallow_context.intros base_decomp_shallow' max_top_layer)

lemma base_decomp_aliens:
  assumes "t \<in> \<T>" "(B, ts) = base_decomp t"
  shows "set ts \<subseteq> set (aliens t)"
  using assms by (auto simp: base_decomp_def Let_def)

lemma base_decomp_fill_holes:
  assumes "(B, ts) = base_decomp t"
  shows "length ts = num_holes B" "fill_holes B ts = t"
proof -
  let ?M = "max_top t"
  define as where [simp]: "as = unfill_holes ?M t"
  let ?as' = "map (\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole) as"
  have B[simp]: "B = fill_holes_mctxt ?M ?as'" and ts[simp]: "ts = filter (\<lambda>t. \<not> rank t \<le> rk) as"
    using assms by (auto simp: base_decomp_def Let_def)
  show *: "length ts = num_holes B"
    using num_holes_fill_holes_mctxt[of ?M "?as'"]
    by (auto simp: length_unfill_holes[OF max_topC_prefix] length_filter_sum_list comp_def intro: arg_cong[of _ _ sum_list])
  have **: "partition_holes (filter (\<lambda>t. \<not> rank t \<le> rk) as) ?as' = map (\<lambda>t. if rank t \<le> rk then [] else [t]) as"
    by (induct as) auto
  have ***: "map (\<lambda>i. fill_holes (map (\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole) as ! i)
                 (map (\<lambda>t. if rank t \<le> rk then [] else [t]) as ! i)) [0..<length as] = as"
    by (intro nth_equalityI) auto
  show "fill_holes B ts = t"
    unfolding B
    apply (subst fill_holes_mctxt_fill_holes)
    subgoal by (auto simp: length_unfill_holes[OF max_topC_prefix])
    subgoal using * by auto
    subgoal unfolding ts ** using ***
      by (auto simp: length_unfill_holes[OF max_topC_prefix] fill_unfill_holes[OF max_topC_prefix])
  done
qed

lemma base_decomp_prefix:
  assumes "(B, ts) = base_decomp t"
  shows "B \<le> mctxt_of_term t"
  using base_decomp_fill_holes[OF assms] by auto

lemma fill_shallow_context_imp_native:
  assumes "C \<in> shallow_context" "num_holes C = length ts" "set ts \<subseteq> short_terms"
  shows "fill_holes C ts \<in> native_terms"
proof -
  have "fill_holes C ts \<in> \<T>" using assms funas_mctxt_fill_holes[of C ts]
    by (auto simp: \<T>_def short_terms_def funas_shallow_context)
  moreover obtain L Cs where *: "L \<in> \<LL>" "length Cs = num_holes L"
    "set Cs \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms" "C = fill_holes_mctxt L Cs"
    using assms(1) by (elim shallow_context.cases) simp
  { fix i assume "i < num_holes L"
    then have "fill_holes (Cs ! i) (partition_holes ts Cs ! i) \<in> short_terms"
    using *(2) subsetD[OF *(3), OF nth_mem, of i] shorter_terms_short subsetD[OF assms(3), OF nth_mem]
      *(4) num_holes_fill_holes_mctxt[OF *(2)[symmetric]]
      sum_list_append[of "take i (map num_holes Cs)" "drop i (map num_holes Cs)", symmetric]
      sum_list_take'[of 1 "drop i (map num_holes Cs)"] assms(2)
    by (force simp: image_def partition_by_nth take1 hd_drop_conv_nth) }
  then have "set (map (\<lambda>i. fill_holes (Cs ! i) (partition_holes ts Cs ! i)) [0..<num_holes L])
    \<subseteq> short_terms" by auto
  note subsetD[OF this, OF nth_mem]
  moreover have "L \<le> max_top (fill_holes C ts)" using *(1,2,4) assms(2)
    order.trans[OF fill_holes_mctxt_suffix[of Cs L] fill_holes_mctxt_suffix[of "map mctxt_of_term ts" "fill_holes_mctxt L Cs"]]
    by (auto intro!: max_top_props(2) simp: topsC_def)
  ultimately show ?thesis using assms(2) fill_holes_mctxt_fill_holes[of Cs L ts]
    order.trans[OF rank_by_top[of "fill_holes C ts" L], of "rk+2"]
    by (simp add: *(2,4) short_terms_def native_terms_def unfill_fill_holes max_list_bound_set)
qed

lemma max_topC_max_top_conv:
  "max_top (mctxt_term_conv C \<cdot> (Var \<circ> from_option)) =
   fill_holes_mctxt (map_vars_mctxt (from_option \<circ> Some) (max_topC C)) (map (\<lambda>D. if D = MHole then MVar (from_option None) else MHole) (aliensC C))"
  (is "max_top ?t = fill_holes_mctxt ?C ?Cs")
proof -
  let ?M = "fill_holes_mctxt ?C ?Cs"
  have [simp]: "length (aliensC C) = num_holes (max_topC C)"
    using max_topC_prefix[of C] by simp
  have "set ?Cs \<subseteq> {MHole} \<union> range MVar" by auto
  then have 1: "?M \<in> \<LL>" using vars_to_holes'_layer[of ?M] vars_to_holes'_layer[of "max_topC C"]
    vars_to_holes'_fill_holes[of "?C" "?Cs"] by (auto)
  moreover
  have "?M \<le> mctxt_of_term (mctxt_term_conv (fill_holes_mctxt (max_topC C) (aliensC C)) \<cdot> (Var \<circ> from_option))"
    apply (subst mctxt_term_conv_fill_holes_mctxt, simp)
    apply (subst subst_apply_mctxt_fill_holes, simp)
    apply (subst mctxt_of_term_fill_holes', simp add: subst_apply_mctxt_map_vars_mctxt_conv)
    unfolding subst_apply_mctxt_map_vars_mctxt_conv map_vars_mctxt_map_vars_mctxt
    by (intro less_eq_fill_holesI) simp_all
  then have 2: "?M \<le> mctxt_of_term ?t" using max_topC_prefix[of C] by (auto simp: fill_unfill_holes_mctxt)
  moreover {
    fix D assume 3: "D \<in> \<LL>" "D \<le> mctxt_of_term ?t"
    let ?E = "D \<squnion> ?M" and ?C = "map_vars_mctxt (from_option \<circ> Some) (max_topC C)"
    have c: "(D, ?M) \<in> comp_mctxt" using 2 3 by (auto simp: prefix_mctxt_sup prefix_comp_mctxt)
    have "vars_to_holes (mctxt_of_term ?t) \<le> C" by (induct C) (auto intro: less_eq_mctxtI1)
    with vars_to_holes'_mono[OF 3(2)] have "vars_to_holes D \<le> C" by simp
    then have "vars_to_holes D \<le> max_topC C" using 3(1) by (simp add: topsC_def vars_to_holes_layer)
    moreover have "vars_to_holes ?M \<le> max_topC C" using vars_to_holes_prefix[of "max_topC C"]
      by (subst vars_to_holes_fill_holes) auto
    ultimately have l': "vars_to_holes ?E \<le> max_topC C" using c by (auto simp: prefix_mctxt_sup vars_to_holes_sup)
    have "?C \<le> ?M" by (subst fill_holes_mctxt_suffix) auto
    then have "?C \<le> ?E" using sup_mctxt_ge2[OF c] using order.trans by blast
    from fill_unfill_holes_mctxt[OF this] length_unfill_holes_mctxt[OF this]
    obtain Es where [simp]: "length Es = num_holes ?C" and *: "?E = fill_holes_mctxt ?C Es" by metis
    have 4: "num_holes C = length Cs \<Longrightarrow>
      vars_to_holes (fill_holes_mctxt (map_vars_mctxt f C) Cs) = vars_to_holes (fill_holes_mctxt C Cs)" for f C Cs
      by (induct C Cs rule: fill_holes_induct) (auto simp: comp_def)
    have 5: "num_holes C = length Cs \<Longrightarrow> num_holes C = length Ds \<Longrightarrow>
      vars_to_holes (fill_holes_mctxt C Cs) \<le> fill_holes_mctxt C Ds \<longleftrightarrow>
      fill_holes_mctxt C (map vars_to_holes Cs) \<le> fill_holes_mctxt C Ds" for C Cs Ds
      by (induct C Cs Ds rule: fill_holes_induct2) (auto intro!: less_eq_mctxtI1 elim!: less_eq_mctxtE1)
    have "num_holes C = length Cs \<Longrightarrow> mctxt_of_term (mctxt_term_conv (fill_holes_mctxt C Cs) \<cdot> (Var \<circ> from_option)) =
         fill_holes_mctxt (map_vars_mctxt (from_option \<circ> Some) C)
            (map (\<lambda>D. mctxt_of_term (mctxt_term_conv D \<cdot> (Var \<circ> from_option))) Cs)"
      for C Cs by (induct C Cs rule: fill_holes_induct) (auto simp: comp_def)
    from this[of "max_topC C" "unfill_holes_mctxt (max_topC C) C"] 3(2) max_topC_prefix[of C]
    have "D \<le> fill_holes_mctxt (map_vars_mctxt (from_option \<circ> Some) (max_topC C)) (map (\<lambda>D. mctxt_of_term (mctxt_term_conv D \<cdot> (Var \<circ> from_option))) (aliensC C))"
      (is "_ \<le> ?U") by (simp add: fill_unfill_holes_mctxt)
    moreover have "?M \<le> ?U" by (subst less_eq_fill_holesI) auto
    ultimately have "?E \<le> ?U" by (auto intro: prefix_mctxt_sup)
    then have "?E \<le> ?M" using l' unfolding *
      apply (subst less_eq_fill_holesI, simp, simp)
      apply (subst (asm) 4, simp)
      apply (subst (asm) (5) fill_holes_mctxt_replicate_MHole[of "max_topC C", symmetric])
      apply (subst (asm) 5, simp, simp)
      apply (subst (asm) less_eq_fill_holes_iff, simp, simp)
      apply (subst (asm) less_eq_fill_holes_iff, simp, simp)
      subgoal premises p for i
        using spec[OF p(1), of i] spec[OF p(2), of i] p(3) aliens_not_varC[of _ C]
        apply (cases "Es ! i"; cases "aliensC C ! i")
        apply (auto simp: set_conv_nth elim: less_eq_mctxtE1)
        done
      apply auto
      done
    then have "D \<le> ?M" using sup_mctxt_ge1[OF c] by simp
  }
  ultimately show ?thesis by (auto intro: max_topCI simp: topsC_def)
qed

lemma shallow_context_decomp:
  assumes "C \<in> shallow_context"
  obtains (1) L Cs where "L = max_topC C" "length Cs = num_holes L"
    "set Cs \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms - MVar ` UNIV" "fill_holes_mctxt L Cs = C"
proof -
  from assms(1) obtain L' Cs' where *: "L' \<in> \<LL>" "length Cs' = num_holes L'"
    "set Cs' \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms" "C = fill_holes_mctxt L' Cs'"
    by (metis (no_types, lifting) shallow_context.cases)
  then have "C \<in> \<C>" using \<LL>_sig unfolding shorter_terms_def \<C>_def \<T>_def by (auto simp: image_def subset_iff)
  have T: "mctxt_term_conv C \<cdot> (Var \<circ> from_option) \<in> \<T>"
    using assms(1) by (auto simp: funas_term_subst funas_shallow_context \<T>_def)
  have aux: "C \<le> term_mctxt_conv t \<Longrightarrow> unfill_holes (map_vars_mctxt (f \<circ> Some) C) (t \<cdot> (Var \<circ> f)) =
    map (\<lambda>D. mctxt_term_conv D \<cdot> (Var \<circ> f)) (unfill_holes_mctxt C (term_mctxt_conv t))" for C t f
    by (induct t arbitrary: C rule: term_mctxt_conv.induct; case_tac C)
      (auto elim!: less_eq_mctxtE2 simp: map_concat intro!: arg_cong[of _ _ concat])
  have [simp]: "rank (mctxt_term_conv (mctxt_of_term t) \<cdot> (Var \<circ> from_option)) = rank t" for t
    by (simp add: rank_var_subst[unfolded comp_def] subst_subst_compose[symmetric] subst_compose_def del: subst_subst_compose)
  have [intro]: "D \<in> set Cs' \<Longrightarrow> D \<noteq> MHole \<Longrightarrow> rank (mctxt_term_conv D \<cdot> (Var \<circ> from_option)) \<le> rk" for D
    using *(3) by (auto dest!: subsetD simp del: subst_subst_compose simp: shorter_terms_def
      subst_subst_compose[symmetric] subst_compose_def rank_var_subst[unfolded comp_def] rank_var)
  have "map_vars_mctxt (from_option \<circ> Some) L' \<le> mctxt_of_term (mctxt_term_conv C \<cdot> (Var \<circ> from_option))"
    using fill_holes_mctxt_suffix[OF *(2)] unfolding *(4)[symmetric]
    by (induct L' C rule: less_eq_mctxt_induct) (auto intro: less_eq_mctxtI1)
  then have "map_vars_mctxt (from_option \<circ> Some) L' \<le> max_top (mctxt_term_conv C \<cdot> (Var \<circ> from_option))"
    by (auto simp: topsC_def *(1))
  from rank_by_top'[OF T this] have "rank (mctxt_term_conv C \<cdot> (Var \<circ> from_option))
    \<le> 1 + max_list (map rank (filter is_Fun (map (\<lambda>D. mctxt_term_conv D \<cdot> (Var \<circ> from_option)) Cs')))"
    by (subst (asm) (2) *(4), subst (asm) aux)
      (auto simp: fill_holes_mctxt_suffix[OF *(2)] comp_def unfill_fill_holes_mctxt[OF *(2)])
  then have "rank (mctxt_term_conv C \<cdot> (Var \<circ> from_option)) \<le> 1 + rk"
    using max_list_bound_set[of "map rank (filter is_Fun (map (\<lambda>D. mctxt_term_conv D \<cdot> (Var \<circ> from_option)) Cs'))" rk]
    by auto
  from this[unfolded rank.simps[of "mctxt_term_conv C \<cdot> (Var \<circ> from_option)"]]
  have rk: "D \<in> set (aliens (mctxt_term_conv C \<cdot> (Var \<circ> from_option))) \<Longrightarrow> rank D \<le> rk" for D
    using T by (auto simp: max_list_bound set_conv_nth)
  note [simp] = length_unfill_holes_mctxt[OF max_topC_prefix]
  note fill_holes_mctxt_suffix[OF *(2), folded *(4)]
  then have "L' \<le> max_topC C" by (auto intro!: max_topC_props(2) simp: topsC_def *(1))
  with max_topC_prefix[of C]
     unfill_holes_mctxt_by_prefix'[of L' "unfill_holes_mctxt L' (max_topC C)" C] *(2)
  have "aliensC C = concat (map (\<lambda>(x, y). unfill_holes_mctxt x y)
    (zip (unfill_holes_mctxt L' (max_topC C)) Cs'))"
    and "i < num_holes L' \<Longrightarrow> unfill_holes_mctxt L' (max_topC C) ! i \<le> Cs' ! i" for i
    using less_eq_fill_holes_iff[of "unfill_holes_mctxt L' (max_topC C)" L' Cs']
    by (auto simp: fill_unfill_holes_mctxt *(4) unfill_fill_holes_mctxt[OF *(2)])
  have "D \<in> set (aliensC C) \<Longrightarrow> D = MHole \<or> mctxt_term_conv D \<cdot> (Var \<circ> from_option) \<in> set (aliens (mctxt_term_conv C \<cdot> (Var \<circ> from_option)))" for D
    using max_top_prefix[of "mctxt_term_conv C \<cdot> (Var \<circ> from_option)"]
    by (auto simp: max_topC_max_top_conv unfill_holes_by_prefix' zip_map1 zip_map2 zip_same_conv_map aux max_topC_prefix)
  moreover {
    fix D
    define E where "E = max_topC C"
    assume D: "mctxt_term_conv D \<cdot> (Var \<circ> from_option) \<in> set (aliens (mctxt_term_conv C \<cdot> (Var \<circ> from_option)))" "D \<noteq> MHole"
    have "num_holes D = 0"
      using *(2)[symmetric] *(3,4) \<open>L' \<le> max_topC C\<close> max_topC_prefix[of C] D
        unfolding max_topC_max_top_conv E_def[symmetric]
      proof (induct L' Cs' arbitrary: C E rule: fill_holes_induct)
        case (MHole C')
        obtain t where C': "C = mctxt_of_term t" using MHole by (auto elim: less_eq_mctxtE2)
        show ?case using MHole(4) C' MHole(5,6)
        proof (induct E C arbitrary: t rule: less_eq_mctxt_induct)
          case (1 C) show ?case using 1(1,2)
          proof (induct t arbitrary: C D)
            case (Var x) then show ?case
              using surj_imp_inj_inv[OF bij_is_surj, OF bij_from_option]
              by (cases D) (auto simp: inj_on_def from_option_def)
          next
            case (Fun f ts) then show ?case
              by (cases D) (auto simp: map_eq_conv' set_conv_nth, blast)
          qed
        next
          case (2 x) then show ?case by (cases t) auto
        next
          case (3 Es Cs f)
          obtain ts where t: "t = Fun f ts" "length Cs = length ts" using 3 by (cases t) auto
          { fix i assume "i < length ts"
            then have "(partition_holes (map (\<lambda>D. if D = MHole then MVar (from_option None) else MHole)
              (concat (map (\<lambda>i. unfill_holes_mctxt (Es ! i) (map mctxt_of_term ts ! i)) [0..<length ts]))) Es) ! i =
              map (\<lambda>D. if D = MHole then MVar (from_option None) else MHole)
              (unfill_holes_mctxt (Es ! i) (map mctxt_of_term ts ! i))"
              unfolding map_map_partition_by[symmetric] using 3(1,2,4) t
              apply (subst (2) nth_map, simp)
              apply (subst partition_holes_concat_id, simp, simp)
              by simp
          } note [simp] = this
          show ?case using 3 t by (auto simp: comp_def)
        qed
      next
        case (MFun f Ls xs)
        from MFun(5) obtain Es where [simp]: "E = MFun f Es" "length Ls = length Es" and
          *: "\<And>i. i < length Es \<Longrightarrow> Ls ! i \<le> Es ! i" by (auto elim: less_eq_mctxtE1)
        from MFun(6) obtain Cs where [simp]: "C = MFun f Cs" "length Es = length Cs" and
          **: "\<And>i. i < length Cs \<Longrightarrow> Es ! i \<le> Cs ! i" by (auto elim: less_eq_mctxtE1)
        { fix i assume "i < length Cs"
          then have "partition_holes (map (\<lambda>D. if D = MHole then MVar (from_option None) else MHole)
            (concat (map (\<lambda>i. unfill_holes_mctxt (Es ! i) (Cs ! i)) [0..<length Cs]))) Es ! i =
            map (\<lambda>D. if D = MHole then MVar (from_option None) else MHole)
            (unfill_holes_mctxt (Es ! i) (Cs ! i))"
            unfolding map_map_partition_by[symmetric]
              by (subst partition_holes_concat_id) (auto simp: **)
        } note [simp] = this
        from MFun(7) obtain i where [simp]: "i < length Cs" and
          ***: "mctxt_term_conv D \<cdot> (Var \<circ> from_option) \<in> set (unfill_holes
             (fill_holes_mctxt (map_vars_mctxt (from_option \<circ> Some) (Es ! i))
               (map (\<lambda>D. if D = MHole then MVar (from_option None) else MHole)
                 (unfill_holes_mctxt (Es ! i) (Cs ! i))))
             (mctxt_term_conv (Cs ! i) \<cdot> (Var \<circ> from_option)))"
          by (auto simp: comp_def)
        show ?case using MFun(1,3,4) nth_subset_concat[of i "partition_holes xs Ls"]
        by (auto intro!: MFun(2)[of i, OF _ _ _ * ** ***]
          simp: MFun(8) dest: arg_cong[of Cs _ "\<lambda>Cs. Cs ! i"])
      qed auto
    then obtain t where D': "D = mctxt_of_term t" by (metis mctxt_of_term_term_of_mctxt_id)
    have [simp]: "t \<in> \<T>" using \<open>C \<in> \<C>\<close> D' imageI[OF D(1), of funas_term]
      arg_cong[OF fill_unfill_holes[OF max_topC_prefix, of "mctxt_term_conv C \<cdot> (Var \<circ> from_option)"], of funas_term]
      by (auto simp: \<T>_def \<C>_def funas_mctxt_fill_holes funas_term_subst length_unfill_holes[OF max_topC_prefix])
    have "D \<in> mctxt_of_term ` shorter_terms" using rk[OF D(1)] D
      by (auto intro!: exI[of _ "term_of_mctxt D"] simp del: subst_subst_compose
        simp: shorter_terms_def subst_subst_compose[symmetric] subst_compose_def rank_var_subst[unfolded comp_def] D')
  }
  ultimately have "D \<in> set (aliensC C) \<Longrightarrow> D \<in> {MHole} \<union> mctxt_of_term ` shorter_terms - range MVar" for D
    by (auto simp: aliens_not_varC image_def)
  then show ?thesis
    by (auto intro!: 1[of "max_topC C" "aliensC C"] simp: fill_unfill_holes_mctxt[OF max_topC_prefix])
qed

text \<open>{cite \<open>Lemma 4.18\<close> FMZvO15}\<close>

lemma shallow_context_closed:
  assumes "C \<in> shallow_context" "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep' \<R>"
  shows "D \<in> shallow_context"
proof -
  from assms(2) obtain l r p \<sigma> where assms2:
    "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>" by (metis rstep'_iff_rstep_r_p_s')
  from assms(1) obtain L Cs
    where *: "L = max_topC C" "length Cs = num_holes L"
     "set Cs \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms - MVar ` UNIV" "fill_holes_mctxt L Cs = C"
    using shallow_context_decomp by (metis (no_types, lifting))
  then have **: "set Cs \<inter> MVar ` UNIV = {}" by auto
  show ?thesis using trs *(2)[symmetric] assms2[folded *(4)]
  proof (cases rule: rewrite_cases_mctxt_wf)
    case outer
    let ?to_c = "map_vars_mctxt (from_option \<circ> Some)"
    let ?to_t = "\<lambda>C. mctxt_term_conv C \<cdot> (Var \<circ> from_option)"
    have "(?to_t C, ?to_t D) \<in> rstep_r_p_s' \<R> (l, r) p (\<sigma> \<circ>\<^sub>s (Var \<circ> from_option))"
      using assms2 by (intro rstep_r_p_s'_stable)
    moreover have "mctxt_term_conv C \<cdot> (Var \<circ> from_option) \<in> \<T>"
      using assms(1) by (elim shallow_context.cases, auto simp: shorter_terms_def \<T>_def funas_term_subst subset_eq)
        (insert \<LL>_sig, auto simp: \<C>_def)
    moreover
    let ?C' = "?to_t C"
    let ?L' = "fill_holes_mctxt (?to_c L) (map (\<lambda>C. if C = MHole then MVar (from_option None) else MHole) Cs)"
    let ?Cs' = "concat (map (\<lambda>C. if C = MHole then [] else [?to_t C]) Cs)"
    have "partition_by ?Cs' (map (\<lambda>C. if C = MHole then 0 else 1) Cs) =
      map (\<lambda>C. if C = MHole then [] else [?to_t C]) Cs"
      by (auto intro: partition_by_concat_id)
    then have C': "fill_holes ?L' ?Cs' = ?C'" "num_holes ?L' = length ?Cs'"
      using fill_holes_mctxt_fill_holes[of
        "map (\<lambda>C. if C = MHole then MVar (from_option None) else MHole) Cs" "?to_c L" ?Cs']
        *(2) num_holes_fill_holes_mctxt[of "map_vars_mctxt (from_option \<circ> Some) L"
        "map (\<lambda>C. if C = MHole then MVar (from_option None) else MHole) Cs"]
      by (auto simp: *(4)[symmetric] comp_def length_concat if_distrib mctxt_term_conv_fill_holes_mctxt
        subst_apply_mctxt_fill_holes subst_apply_mctxt_map_vars_mctxt_conv[unfolded comp_def]
        cong: if_cong intro!: arg_cong[of _ _ "fill_holes _"] nth_equalityI)
    { have "vars_to_holes ?L' = vars_to_holes L" using *(2)[symmetric]
        by (induct L Cs rule: fill_holes_induct) (auto intro!: nth_equalityI simp: comp_def)
      from vars_to_holes_layer[of ?L', unfolded this]
      have "?L' \<in> \<LL>" using *(1) by (simp add: vars_to_holes_layer)
      moreover have "?L' \<le> mctxt_of_term ?C'" using fill_holes_suffix[OF C'(2)] C'(1) by simp
      moreover {
        fix L' assume "L' \<in> tops ?C'"
        then have "L' \<in> \<LL>" "L' \<le> mctxt_of_term ?C'" by (auto simp: topsC_def)
        from vars_to_holes'_mono[OF this(2)] have "vars_to_holes L' \<le> C"
        proof (induct L' arbitrary: C)
          case o: (MFun f Ls) then show ?case
          proof (cases C)
            case (MFun g Cs)
            then show ?thesis using o(1)[of "Ls ! i" "Cs ! i" for i] o(2)
              by (auto intro!: less_eq_mctxtI1(3)[of _ _ Cs] elim: less_eq_mctxtE1)
          qed (auto elim: less_eq_mctxtE1)
        qed auto
        then have "vars_to_holes L' \<le> L"
          using *(1) max_topC_props(2) vars_to_holes_layer topsC_def \<open>L' \<in> \<LL>\<close> by blast
        with *(2)[symmetric] \<open>L' \<le> mctxt_of_term ?C'\<close> ** have "L' \<le> ?L'" unfolding *(4)[symmetric]
        proof (induct L Cs arbitrary: L' rule: fill_holes_induct)
          case (MHole C) then show ?case by (cases C; cases L') (auto elim: less_eq_mctxtE1)
        next
          case (MFun f Ls Cs)
          have "i < length Ls \<Longrightarrow> set (partition_holes Cs Ls ! i) \<inter> MVar ` UNIV = {}" for i
            using MFun(1,4) nth_subset_concat[of i "partition_holes Cs Ls"] by auto
          with MFun show ?case
            by (cases L') (auto elim!: less_eq_mctxtE1 intro: less_eq_mctxtI1(3) nth_equalityI simp: comp_def)
        qed auto
      }
      ultimately have "max_top ?C' = ?L'" by (auto intro: max_topCI simp: topsC_def)
    } note max_top_C' = this
    have "p \<in> fun_poss_mctxt (max_top ?C')" using *(2)[symmetric] outer(1) unfolding max_top_C'
      by (induct L Cs arbitrary: p rule: fill_holes_induct)
         (auto simp: fun_poss_mctxt_def comp_def)
    ultimately obtain M \<tau> where M: "M \<in> \<LL>"
       "(mctxt_term_conv (max_top ?C'), mctxt_term_conv M)
        \<in> rstep_r_p_s' \<R> (l, r) p \<tau>"
       by (auto dest: W')
    have ***: "(mctxt_term_conv L, mctxt_term_conv (term_mctxt_conv (mctxt_term_conv M \<cdot> (Var \<circ> case_option None to_option))))
      \<in> rstep_r_p_s' \<R> (l, r) p (\<tau> \<circ>\<^sub>s (\<lambda>x. case x of None \<Rightarrow> Var None | Some x \<Rightarrow> Var (to_option x)))"
      (is "(_, mctxt_term_conv ?M') \<in> _ p ?\<tau>'")
      using M[unfolded max_top_C'] *(2) fill_holes_mctxt_replicate_MHole[of L]
        mctxt_term_conv_fill_holes_mctxt[of L "map (\<lambda>_. MHole) Cs", symmetric]
      apply (subst (asm) mctxt_term_conv_fill_holes_mctxt, simp add: C'[folded max_top_C'])
      apply (drule rstep_r_p_s'_stable[where \<tau> = "Var \<circ> case_option None to_option"])
      apply (simp add: subst_apply_mctxt_fill_holes subst_apply_mctxt_map_vars_mctxt_conv)
      apply (simp add: comp_def if_distrib if_distrib[of "\<lambda>x. x _"] option.case_distrib map_replicate_const cong: if_cong)
      done
    have "vars_to_holes ?M' = vars_to_holes M"
    proof (induct M)
      case (MVar x) then show ?case by (cases "to_option x") auto
    qed auto
    then have "?M' \<in> \<LL>" by (metis M(1) vars_to_holes_layer)
    moreover
    thm rstep_r_p_s'_stable[OF ***, where \<tau> = "Var \<circ> from_option"]
    from rewrite_aliens_mctxt[OF trs *** *(2)[symmetric], of \<sigma>]
    obtain Ds where
      "num_holes (term_mctxt_conv (mctxt_term_conv M \<cdot> (Var \<circ> case_option None to_option))) = length Ds"
      "(mctxt_term_conv (fill_holes_mctxt L Cs), mctxt_term_conv (fill_holes_mctxt (term_mctxt_conv (mctxt_term_conv M \<cdot> (Var \<circ> case_option None to_option))) Ds)) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
      "set Ds \<subseteq> set Cs"
      using assms2 by (auto simp: *(4) elim!: rstep_r_p_s'.cases) blast
    ultimately show ?thesis using *(3)
      arg_cong[OF rstep_r_p_s'_deterministic[OF trs assms2], where f = term_mctxt_conv]
      by (auto intro!: shallow_context.intros[of "?M'" Ds] simp: *(4))
  next
    case (inner i Ci)
    moreover have "L \<in> \<LL>" using * by auto
    moreover
    have **: "(term_of_mctxt (Cs ! i), term_of_mctxt Ci) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' L ! i)) (\<sigma> \<circ>\<^sub>s term_of_mctxt_subst)"
      using inner(3) unfolding term_of_mctxt_to_mctxt_term_conv by (intro rstep_r_p_s'_stable)
    have "Cs ! i \<in> {MHole} \<union> mctxt_of_term ` shorter_terms"
      using *(3) nth_mem[OF inner(1)] by auto
    then have ***: "term_of_mctxt (Cs ! i) \<in> shorter_terms" "mctxt_of_term (term_of_mctxt (Cs ! i)) = Cs ! i"
      using inner(3) NF_Var'[OF trs, unfolded rstep'_iff_rstep_r_p_s'] by force+
    { have "term_of_mctxt Ci \<in> shorter_terms"
        using ** ***(1) rank_preservation[of "term_of_mctxt (Cs ! i)" "term_of_mctxt Ci"]
          \<T>_preservation[of "term_of_mctxt (Cs ! i)" "term_of_mctxt Ci"]
        unfolding rstep'_iff_rstep_r_p_s' shorter_terms_def by force
      moreover have "mctxt_term_conv (mctxt_of_term (term_of_mctxt Ci)) = mctxt_term_conv Ci"
        using arg_cong[OF ***(2), of mctxt_term_conv] inner(3) trs
          rstep_r_p_s'_stable[OF inner(3), of "term_of_mctxt_subst \<circ>\<^sub>s (Var \<circ> Some)"]
        by (auto simp: term_of_mctxt_to_mctxt_term_conv intro: rstep_r_p_s'_deterministic)
      note arg_cong[OF this, of term_mctxt_conv, unfolded term_mctxt_conv_inv]
      ultimately have "Ci \<in> mctxt_of_term ` shorter_terms" by (auto simp: shorter_terms_def image_def)
    }
    then have "set (Cs[i := Ci]) \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms"
      using inner *(3) by (intro set_update_subsetI) auto
    ultimately show ?thesis using * by (intro shallow_context.intros[of L "Cs[i := Ci]"]) auto
  qed
qed

lemma shallow_context_closed':
  assumes "C \<in> shallow_context" "(mctxt_term_conv C, mctxt_term_conv D) \<in> (rstep' \<R>)\<^sup>*"
  shows "D \<in> shallow_context"
  using assms(2,1)
proof (induct "mctxt_term_conv D" arbitrary: D rule: rtrancl_induct)
  case base show ?case by (metis base term_mctxt_conv_inv)
next
  case (step c') show ?case by (metis step(2-4) shallow_context_closed mctxt_term_conv_inv)
qed

lemma set_aliensC_conv:
  "set (aliensC L) \<subseteq> {MHole} \<union> (\<lambda>t. term_mctxt_conv (t \<cdot> (Var \<circ> to_option))) ` set (aliens (mctxt_term_conv L \<cdot> (Var \<circ> from_option)))"
  unfolding max_topC_max_top_conv using max_topC_prefix[of L]
proof (induct ("max_topC L") L rule: less_eq_mctxt_induct)
  case (3 Cs Ds f) then show ?case
    apply (auto 0 0 del: subsetI simp del: UN_simps(1) intro!: UN_mono
      simp: image_UN UN_extend_simps(1) map_concat)
    by (subst partition_by_concat_id) auto
qed (auto simp: subst_subst_compose[symmetric] subst_compose_def simp del: subst_subst_compose)

lemma map_vars_mctxt_id[simp]:
  "map_vars_mctxt id = id"
proof
  fix C show "map_vars_mctxt id C = id C" by (induct C) auto
qed

lemma shallow_context_subset_\<C>:
  "shallow_context \<subseteq> \<C>"
  by (intro subsetI, elim shallow_context.cases)
    (auto simp: \<C>_def \<T>_def shorter_terms_def dest!: subsetD[OF \<LL>_sig] simp: subsetD)

lemma factor_prefix_of_map_vars_mctxt:
  assumes "C \<le> map_vars_mctxt f D"
  obtains C' where "C = map_vars_mctxt f C'" "C' \<le> D"
  using assms
proof (induct C "map_vars_mctxt f D" arbitrary: D thesis rule: less_eq_mctxt_induct)
  case 1 show ?case by (auto intro: 1[of MHole])
next
  case (3 Cs fDs g)
  from 3(1,4) obtain Ds where [simp]: "length Cs = length Ds" "D = MFun g Ds" by (cases D) auto
  have "\<And>i. i < length Cs \<Longrightarrow> fDs ! i = map_vars_mctxt f (Ds ! i)" using 3(4) by auto
  from 3(3)[OF _ this] have "\<And>i. i < length Cs \<Longrightarrow> \<exists>C'. Cs ! i = map_vars_mctxt f C' \<and> C' \<le> Ds ! i" by metis
  then obtain iCs where "\<And>i. i < length Cs \<Longrightarrow> Cs ! i = map_vars_mctxt f (iCs i) \<and> iCs i \<le> Ds ! i" by metis
  then show ?case by (auto intro!: 3(5)[of "MFun g (map iCs [0..<length Cs])"] nth_equalityI intro!: less_eq_mctxtI1)
qed auto

lemma shallow_context_union:
  assumes "C \<in> shallow_context" "D \<in> shallow_context" "(C, D) \<in> comp_mctxt"
  shows "C \<squnion> D \<in> shallow_context"
proof -
  obtain L Cs M Ds where
    C: "L \<in> \<LL>" "length Cs = num_holes L" "set Cs \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms" "C = fill_holes_mctxt L Cs" and
    D: "M \<in> \<LL>" "length Ds = num_holes M" "set Ds \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms" "D = fill_holes_mctxt M Ds" and
    *: "L \<le> C" "M \<le> D"
    using assms(1,2) by (auto elim!: shallow_context.cases)
  from C(1) D(1) * assms(3) have **: "(L, M) \<in> comp_mctxt" "L \<squnion> M \<le> C \<squnion> D" "L \<squnion> M \<in> \<LL>"
    by (meson order.trans dual_order.trans prefix_mctxt_sup prefix_comp_mctxt sup_mctxt_ge1 sup_mctxt_ge2 sup_mctxt_LL)+
  obtain N Es where ***: "N \<le> L \<squnion> M" "C \<squnion> D = fill_holes_mctxt N Es" "num_holes N = length Es"
    "set Es \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms"
    using **(1) C(2-) D(2-) assms(3)
  proof (induct L M arbitrary: C D Cs Ds thesis rule: comp_mctxt.induct)
    case (MHole1 M)
    then consider (h) "Cs = [MHole]" | (t) t where "t \<in> shorter_terms" "Cs = [mctxt_of_term t]" by (cases Cs) auto
    then show ?case
    proof (cases)
      case h then show ?thesis using MHole1(2-) by (intro MHole1(1)[of M Ds]) auto
    next
      case t then show ?thesis using MHole1(2-)
        by (intro MHole1(1)[of "MHole" "Cs"]) (auto simp: mctxt_of_term_leq_imp_eq less_eq_mctxt_sup_conv2[symmetric])
    qed
  next
    case (MHole2 L)
    then consider (h) "Ds = [MHole]" | (t) t where "t \<in> shorter_terms" "Ds = [mctxt_of_term t]" by (cases Ds) auto
    then show ?case
    proof (cases)
      case h then show ?thesis using MHole2(2-) by (intro MHole2(1)[of L Cs]) auto
    next
      case t then show ?thesis using MHole2(2-)
        by (intro MHole2(1)[of "MHole" "Ds"]) (auto simp: mctxt_of_term_leq_imp_eq less_eq_mctxt_sup_conv1[symmetric])
    qed
  next
    case (MVar x y)
    show ?case using MVar(1,3,5,6,8) by (intro MVar(2)[of "MVar x" "[]"]) auto
  next
    case (MFun f g Ls Ms)
    { fix i x y assume "i < length Ms"
      note * = MFun(3)[rule_format, OF this, THEN conjunct1]
        MFun(3)[rule_format, OF this, THEN conjunct2, rule_format,
          OF _ _ _ refl _ _ refl,
          of "partition_holes Cs Ls ! i" "partition_holes Ds Ms ! i"]
      have [dest!]: "x \<in> set (partition_holes Cs Ls ! i) \<Longrightarrow> x \<in> set Cs" for x
        using \<open>i < length Ms\<close> MFun(5)[unfolded num_holes.simps]
        by (metis MFun.hyps(2) in_set_idx length_map length_partition_by_nth partition_by_nth_nth_elem)
      have [dest!]: "x \<in> set (partition_holes Ds Ms ! i) \<Longrightarrow> x \<in> set Ds" for x
        using \<open>i < length Ms\<close> MFun(8)[unfolded num_holes.simps]
        by (metis MFun.hyps(2) in_set_idx length_map length_partition_by_nth partition_by_nth_nth_elem)
      have "\<exists>Ni Esi. Ni \<le> Ls ! i \<squnion> Ms ! i \<and>
         fill_holes_mctxt (Ls ! i) (partition_holes Cs Ls ! i) \<squnion>
         fill_holes_mctxt (Ms ! i) (partition_holes Ds Ms ! i) = fill_holes_mctxt Ni Esi \<and>
         num_holes Ni = length Esi \<and>
         set Esi \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms"
        using \<open>i < length Ms\<close> MFun(1,2,5-11) by (subst *(2)) (auto dest!: comp_MFunD)
    }
    then obtain Nf Esf where
      *: "i < length Ms \<Longrightarrow> Nf i \<le> Ls ! i \<squnion> Ms ! i \<and>
         fill_holes_mctxt (Ls ! i) (partition_holes Cs Ls ! i) \<squnion>
         fill_holes_mctxt (Ms ! i) (partition_holes Ds Ms ! i) = fill_holes_mctxt (Nf i) (Esf i) \<and>
         num_holes (Nf i) = length (Esf i) \<and>
         set (Esf i) \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms" for i by metis
    let ?Ns = "map Nf [0..<length Ms]" and ?Ess = "map Esf [0..<length Ms]"
    show ?case
      using * MFun(1,2,5-) partition_by_concat_id[of ?Ess "map num_holes ?Ns"]
      apply (intro MFun(4)[OF less_eq_mctxtI1(3), of f "map (\<lambda>(x,y). x \<squnion> y) (zip Ls Ms)" ?Ns "concat ?Ess"])
      apply (auto intro!: nth_equalityI[of "map _ _"] arg_cong[of _ _ sum_list]
        arg_cong[of _ _ "fill_holes_mctxt (Nf _)"]
        simp: length_concat in_set_conv_nth[of _ ?Ess])
      apply blast
      done
  qed
  have "mctxt_term_conv (C \<squnion> D) \<cdot> (Var \<circ> from_option) \<in> \<T>" using assms
    by (auto simp: \<T>_def funas_term_subst funas_mctxt_sup_mctxt \<C>_def dest!: subsetD[OF shallow_context_subset_\<C>])
  moreover {
    have "N \<le> max_topC (C \<squnion> D)"
      by (metis (no_types, lifting) **(2,3) ***(1) dual_order.trans max_topC_props(2) mem_Collect_eq topsC_def)
    note map_vars_mctxt_mono[OF this, of "from_option \<circ> Some"]
    moreover have "map_vars_mctxt (from_option \<circ> Some) (max_topC (C \<squnion> D)) \<le> mctxt_of_term (mctxt_term_conv (C \<squnion> D) \<cdot> (Var \<circ> from_option))"
      using map_vars_mctxt_mono[OF max_topC_prefix, of "from_option \<circ> Some" "C \<squnion> D"]
        map_vars_mctxt_mono[OF map_vars_Some_le_mctxt_of_term_mctxt_term_conv, of from_option "C \<squnion> D"]
      by (simp add: mctxt_of_term_var_subst)
    then have "map_vars_mctxt (from_option \<circ> Some) (max_topC (C \<squnion> D)) \<in> tops (mctxt_term_conv (C \<squnion> D) \<cdot> (Var \<circ> from_option))"
      by (simp add: topsC_def)
    note max_topC_props(2)[OF this]
    ultimately have "map_vars_mctxt (from_option \<circ> Some) N \<le> max_top (mctxt_term_conv (C \<squnion> D) \<cdot> (Var \<circ> from_option))"
      by simp
  } note N = this
  moreover have "max_list (map rank (filter is_Fun (map (\<lambda>E. mctxt_term_conv E \<cdot> (\<lambda>x. Var (from_option x))) Es))) \<le> rk"
    using ***(1-3) subsetD[OF ***(4), simplified, dest!]
    by (auto intro!: max_list_mono[of _ "[rk]", unfolded max_list.simps max_0R]
      simp del: subst_subst_compose simp: subst_subst_compose[symmetric] subst_compose_def rank_var_subst[unfolded comp_def] rank_var shorter_terms_def)
  ultimately have rk: "max_list (map rank (aliens (mctxt_term_conv (C \<squnion> D) \<cdot> (Var \<circ> from_option)))) \<le> rk"
    using rank_by_top'[of "mctxt_term_conv (C \<squnion> D) \<cdot> (Var \<circ> from_option)" "map_vars_mctxt (from_option \<circ> Some) N", unfolded rank.simps[of "_ \<cdot> _"]]
       *** unfill_holes_var_subst[of "map_vars_mctxt Some N" "mctxt_term_conv (C \<squnion> D)" from_option]
       order.trans[OF map_vars_mctxt_mono[of N "C \<squnion> D" Some] map_vars_Some_le_mctxt_of_term_mctxt_term_conv[of "C \<squnion> D"]]
    by (auto simp: comp_def unfill_holes_map_vars_mctxt_Some_mctxt_term_conv_conv unfill_fill_holes_mctxt)
  { { fix f s t
      assume "map_vars_term f s \<unrhd> t" "s \<in> \<T>"
      then consider s' where "s' \<in> \<T>" "map_vars_term f s' = t" unfolding \<T>_def
      proof (induct "map_vars_term f s" t arbitrary: s thesis)
        case (subt u ss t f) then show ?case by (cases s) (auto simp: UN_subset_iff, blast)
      qed simp
    } note [elim] = this
    fix M s t f
    assume x: "M \<le> mctxt_of_term (s \<cdot> (Var \<circ> f))" "t \<in> set (unfill_holes M (s \<cdot> (Var \<circ> f)))" "s \<in> \<T>"
    then have "\<exists>s'. s' \<in> \<T> \<and> t = s' \<cdot> (Var \<circ> f)"
      by (auto dest!: unfill_holes_subt simp: map_vars_term_eq[symmetric])
  } note **** = this[unfolded comp_def]
  { fix s
    define M where "M = max_top (mctxt_term_conv (fill_holes_mctxt N Es) \<cdot> (Var \<circ> from_option))"
    from max_top_prefix[of "mctxt_term_conv (fill_holes_mctxt N Es) \<cdot> (Var \<circ> from_option)", folded M_def]
      obtain M' where M': "M = map_vars_mctxt from_option M'" "M' \<le> mctxt_of_term (mctxt_term_conv (fill_holes_mctxt N Es))"
      by (auto simp: mctxt_of_term_var_subst elim: factor_prefix_of_map_vars_mctxt)
    assume s: "s \<in> set (aliens (mctxt_term_conv (C \<squnion> D) \<cdot> (Var \<circ> from_option)))"
    have "s = Var (from_option None) \<or> (\<exists>s'. s' \<in> \<T> \<and> s = s' \<cdot> (Var \<circ> from_option \<circ> Some))"
      using ***(3) s map_vars_mctxt_mono[OF N, of to_option] M'(2)
      unfolding ***(2) M_def[symmetric] M'(1)
      apply (subst (asm) unfill_holes_var_subst, simp add: M'(2))
      unfolding map_vars_mctxt_map_vars_mctxt comp_def to_from_option map_vars_mctxt_id Multihole_Context.map_vars_mctxt_id
      apply (subst (asm) (2) mctxt_term_conv_fill_holes_mctxt; (simp; fail)?)
      apply (subst (asm) (1) mctxt_of_term_fill_holes'; (simp; fail)?)
      apply (subst (asm) (1 3) fill_unfill_holes_mctxt[of "map_vars_mctxt Some N" M', symmetric]; (simp; fail)?)
      apply (subst (asm) less_eq_fill_holes_iff; (simp; fail)?)
      apply (subst (asm) unfill_holes_by_prefix'; (simp add: fill_unfill_holes_mctxt M'(2); fail)?)
      using subsetD[OF ***(4), OF nth_mem]
      by (force simp: shorter_terms_def set_conv_nth[of "zip _ _"]
        mctxt_term_conv_fill_holes_mctxt unfill_fill_holes comp_def
        subst_subst_compose[symmetric] subst_compose_def simp del: subst_subst_compose
        elim!: less_eq_mctxt_MVarE2
        dest!: ****[of "unfill_holes_mctxt (map_vars_mctxt Some N) M' ! _" _ Some]
      )
    with s order.trans[OF imageI[OF s, of rank, folded set_map, THEN max_list] rk]
    have "s \<in> {Var (from_option None)} \<union> (shorter_terms \<cdot>\<^sub>s\<^sub>e\<^sub>t (Var \<circ> from_option \<circ> Some))"
      by (auto simp: shorter_terms_def image_def rank_var_subst[of _ "_ \<circ> _", unfolded o_assoc])
  }
  note [dest!] = this show ?thesis
  by (intro shallow_context.intros[of "max_topC (C \<squnion> D)" "aliensC (C \<squnion> D)"]
    length_unfill_holes_mctxt max_topC_prefix fill_unfill_holes_mctxt[symmetric] max_topC_layer
    subset_trans[OF set_aliensC_conv])
    (auto simp: image_def subst_subst_compose[symmetric] subst_compose_def
    term_mctxt_conv_mctxt_of_term_conv[unfolded comp_def] simp del: subst_subst_compose)
qed

lemma max_top_le_base:
  assumes "(B, ts) = base_decomp t"
  shows "max_top t \<le> B"
  using assms
  by (auto simp: base_decomp_def Let_def intro!: fill_holes_mctxt_suffix length_unfill_holes max_top_prefix)

text \<open>{cite \<open>Lemma 4.19\<close> FMZvO15}\<close>

lemma base_decomp_max:
  assumes t: "t \<in> native_terms" and C: "C \<in> shallow_context" "C \<le> mctxt_of_term t"
    and bd: "(B, ts) = base_decomp t"
  shows "C \<le> B"
proof -
  have B: "B \<in> shallow_context" "B \<le> mctxt_of_term t" using assms(1,4)
    using t C by (auto simp: native_terms_def base_decomp_shallow base_decomp_prefix)
  have c: "(B, C) \<in> comp_mctxt" using B C by (intro prefix_comp_mctxt)
  have mt: "max_topC (B \<squnion> C) = max_top t"
    using B C max_top_le_base[OF bd] sup_mctxt_ge1[OF c]
    by (auto intro!: antisym intro: max_topC_mono prefix_mctxt_sup max_topC_props(2) simp: topsC_def)
  have "B \<squnion> C \<in> shallow_context" using B C c by (intro shallow_context_union)
  from shallow_context_decomp[OF this]
  obtain Ds where Ds: "length Ds = num_holes (max_top t)"
    "set Ds \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms - range MVar"
    "B \<squnion> C = fill_holes_mctxt (max_top t) Ds" by (metis mt)
  note * = trans[OF arg_cong[OF fill_unfill_holes[of "max_top t" t], of mctxt_of_term, symmetric]
      mctxt_of_term_fill_holes'[of "max_top t" "aliens t"], OF max_top_prefix length_unfill_holes[symmetric, OF max_top_prefix]]
  have "B \<ge> B \<squnion> C"
    using B(2) sup_mctxt_least[OF c B(2) C(2)] max_top_prefix[of t] Ds(1) subsetD[OF Ds(2), OF nth_mem] bd
    unfolding Ds(3)
    apply (simp only: base_decomp_def Let_def prod.inject native_terms_def)
    apply (subst (asm) (3 5) *)
    apply (subst (asm) (1 2) less_eq_fill_holes_iff; (simp; fail)?)
    apply (subst (1) less_eq_fill_holes_iff; (simp; fail)?)
    apply (auto simp: native_terms_def max_list_bound shorter_terms_def image_def intro!: less_eq_mctxtI2)
    by (metis mctxt_of_term_inj mctxt_of_term_leq_imp_eq)
  then show ?thesis using c antisym sup_mctxt_ge2 by fastforce
qed

text \<open>This is a refinement of {cite \<open>Lemma 3.8\<close> FMZvO15} (@{thm rank_by_top}}, but seems hard to
  extract from the existing proof.\<close>

lemma shallow_to_base_no_new_holes:
  assumes "C \<in> shallow_context" "num_holes C = length ts" "set ts \<subseteq> short_terms"
    "(B, ss) = base_decomp (fill_holes C ts)"
  shows "hole_poss B \<subseteq> hole_poss C"
proof (intro subsetI, rule ccontr)
  let ?t = "fill_holes C ts"
  have t: "?t \<in> native_terms" using assms by (intro fill_shallow_context_imp_native)
  then have "C \<le> B" using assms
    by (auto intro: base_decomp_max[of ?t C B ss])
  fix p assume p: "p \<in> hole_poss B" "p \<notin> hole_poss C"
  then obtain q where q: "q \<in> hole_poss C" "q <\<^sub>p p"
    by (auto elim: factor_hole_pos_by_prefix[OF \<open>C \<le> B\<close>] simp: less_pos_def)
  then have "fill_holes C ts |_ q \<in> set ts"
    using subt_at_fill_holes[OF assms(2)[symmetric]] set_hole_poss'
    by (metis assms(2) in_set_conv_nth length_hole_poss')
  then have "rank (fill_holes C ts |_ q) \<le> Suc rk" using assms(3) by (auto simp: short_terms_def)
  with q(2) show False
  proof (induct "size p - size q" arbitrary: q rule: less_induct)
    case less note q = less(2,3)
    obtain i where i: "i < num_holes (max_top ?t)" "p = hole_poss' (max_top ?t) ! i"
      "\<not> rank (aliens ?t ! i) \<le> rk"
      using assms(2,4) p(1) hole_poss_fill_holes_mctxt[of "max_top ?t"
        "map (\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole) (aliens ?t)"]
      by (auto simp: base_decomp_def Let_def max_top_prefix split: if_splits)
    then have r: "rank (aliens ?t ! i) = Suc rk" and p': "p \<in> hole_poss (max_top ?t)"
      using subsetD[OF aliens_short_terms[OF t], OF nth_mem, of i]
      by (auto simp: short_terms_def max_top_prefix set_hole_poss'[symmetric])
    have "q \<in> fun_poss_mctxt (max_top ?t)" using q(1) i
      proper_prefix_hole_poss_imp_fun_poss[of p "max_top ?t" q]
      nth_mem[of i "hole_poss' (max_top ?t)", unfolded set_hole_poss']
      by auto
    note x = this subsetD[OF fun_poss_mctxt_subset_poss_mctxt, OF this]
      subsetD[OF fun_poss_mctxt_subset_all_poss_mctxt, OF this]
    moreover have y: "q \<in> poss ?t" using q(1) assms(2)
      using all_poss_mctxt_mctxt_of_term all_poss_mctxt_mono max_topC_prefix x(3) by blast
    moreover have "(subm_at (max_top (fill_holes C ts)) q, max_top (fill_holes C ts |_ q)) \<in> comp_mctxt"
      using less_eq_subm_at[OF _ max_top_prefix[of ?t], of q] x
        subm_at_mctxt_of_term[of q ?t]
      by (auto intro!: prefix_comp_mctxt[of _ "mctxt_of_term (?t |_ q)"] max_top_prefix simp: y)
    ultimately have "max_top (fill_holes C ts |_ q) \<le> subm_at (max_top (fill_holes C ts)) q"
      using L\<^sub>3[of "max_top ?t" "max_top (?t |_ q)" q, OF max_top_layer max_top_layer]
      apply (subst less_eq_mctxt_sup_conv2, simp add: comp_mctxt_sym)
      apply (subst (1) sup_mctxt_idem[symmetric, of "subm_at _ _"])
      apply (subst sup_mctxt_assoc; (simp add: comp_mctxt_refl comp_mctxt_sym; fail)?)
      apply (subst less_eq_mctxt_sup_conv2[symmetric])
      apply (intro prefix_comp_mctxt[of _ "subm_at (max_top ?t) q"])
      apply (auto simp: merge_mreplace_at replace_at_subm_at[unfolded all_poss_mctxt_conv, OF UnI1]
        intro!: iffD1[OF compare_mreplace_at[of q "max_top ?t" _ "subm_at _ _"]] max_top_props(2))
      using compare_mreplace_atI[OF max_top_prefix max_top_prefix, of q ?t "?t |_ q"]
        subm_at_mctxt_of_term[of q ?t] replace_at_subm_at[of q "mctxt_of_term ?t"]
      by (auto simp:  topsC_def max_top_prefix intro!: prefix_mctxt_sup)
    moreover have "pos_diff p q \<in> hole_poss (subm_at (max_top (fill_holes C ts)) q)"
      using p' q(1) by (auto intro: pos_diff_hole_possI)
    ultimately obtain "q'" where q': "q' \<le>\<^sub>p pos_diff p q" "q' \<in> hole_poss (max_top (?t |_ q))"
      using factor_hole_pos_by_prefix by blast
    moreover have sig: "mctxt_of_term (?t |_ q) \<in> \<C>" "?t |_ q \<in> \<T>" using x y t
      by (auto simp: \<C>_def native_terms_def \<T>_def funas_term_subt_at)
    ultimately have q'': "q' \<noteq> []" using non_empty_max_top_non_empty[of "mctxt_of_term (?t |_ q)"]
      by (cases "max_top (fill_holes C ts |_ q)") auto
    have "?t |_ (q @ q') \<in> set (aliens (?t |_ q))" using y q'
      by (auto simp: unfill_holes_conv max_top_prefix image_def set_hole_poss')
    then have qq': "rank (?t |_ (q @ q')) \<le> rk"
      using q(2) sig by (subst (asm) rank.simps) (auto simp: max_list_bound_set)
    show ?case
    proof (cases "q' = pos_diff p q")
      case True
      moreover have "rank (?t |_ p) = Suc rk" using r i by (simp add: unfill_holes_conv max_top_prefix)
      ultimately show ?thesis using qq' q by simp
    next
      case False then show ?thesis using q q' qq' q''
        by (auto intro!: less(1)[of "q @ q'"] simp: diff_less_mono2)
          (metis less_pos_def less_pos_simps(2) prefix_pos_diff)
    qed
  qed
qed

text \<open>{cite \<open>Lemma 4.16\<close> FMZvO15}\<close>

lemma single_step_to_short_step:
  assumes "s \<in> native_terms"
    "(B, ss) = base_decomp s" "p \<in> poss_mctxt B" "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  shows "(s, t) \<in> short_step"
proof -
  note trs
  moreover have "num_holes (max_top s) = length (aliens s)"
    by (simp add: max_top_prefix)
  moreover have "(fill_holes (max_top s) (aliens s), t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    using assms(4) by (simp add: max_top_prefix fill_unfill_holes)
  ultimately
    obtain \<tau> C where "(mctxt_term_conv B, mctxt_term_conv C) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>"
  proof (cases rule: rewrite_cases_wf)
    case outer
    let ?ss = "map (\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole) (aliens s)"
    have "s \<in> \<T>" using assms(1) by (auto simp: native_terms_def)
    from W'[OF this outer(1) assms(4)] obtain D \<tau> where
      D: "D \<in> \<LL>" "(mctxt_term_conv (max_top s), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>"
      by blast
    have x: "l \<cdot> \<sigma> = s |_ p" "p \<in> poss s" using assms(4) by auto
    have "mctxt_term_conv B = fill_holes (map_vars_mctxt Some (max_top s)) (map mctxt_term_conv ?ss)"
      using assms(2) by (auto simp: base_decomp_def Let_def mctxt_term_conv_fill_holes_mctxt max_top_prefix)
    moreover have "map (map_vars_term Some) (aliens s) \<propto> map mctxt_term_conv ?ss"
      by (intro refines_trans[OF refines_map[of _ "map_vars_term (the_inv Some)"]])
        (auto simp: refines_def inj_map_vars_term_the_inv[OF inj_Some])
    ultimately obtain ts' \<tau>' where "num_holes D = length ts'"
      "(mctxt_term_conv B, mctxt_term_conv (term_mctxt_conv (
         fill_holes (map_vars_mctxt Some D) ts'))) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>'"
      "set ts' \<subseteq> set (map mctxt_term_conv ?ss)"
      using rewrite_balanced_aliens[OF trs, of
        "map_vars_mctxt Some (max_top s)" "map_vars_mctxt Some D" l r p
        "map_vars_term (map_option Some) \<circ> \<tau>" "map (map_vars_term Some) (aliens s)"
        "map_vars_term Some \<circ> \<sigma>" "map mctxt_term_conv ?ss"]
        rstep_r_p_s'_stable[OF D(2), of "Var \<circ> map_option Some"]
        arg_cong[OF x(1), of "\<lambda>t. t \<cdot> (Var \<circ> Some)"] x(2)
      by (auto simp: subst_compose_def comp_def mctxt_term_conv_map_vars_mctxt_subst
        map_vars_term_eq max_top_prefix map_vars_term_fill_holes[symmetric] fill_unfill_holes
        subst_subst_compose[symmetric] simp del: subst_subst_compose)
    then show ?thesis using that by blast
  next
    case (inner i ti)
    obtain q where *:  "p = hole_poss' (max_top s) ! i @ q" and [simp]: "pos_diff p (hole_poss' (max_top s) ! i) = q"
      using inner(4) by (auto intro!: that)
    let ?ss' = "map (\<lambda>t. if rank t \<le> rk then mctxt_of_term t else MHole) (aliens s)"
    have B: "B = fill_holes_mctxt (max_top s) ?ss'" using assms(1,2) by (auto simp: base_decomp_def Let_def)
    have r: "rank (aliens s ! i) \<le> rk"
      using assms(3) inner unfolding B * poss_mctxt_append_poss_mctxt
      by (subst (asm) subm_at_fill_holes_mctxt) (auto simp: max_top_prefix split: if_splits)
    show ?thesis
      apply (intro that[of "fill_holes_mctxt (max_top s) (?ss'[i := mctxt_of_term ti])" "mctxt_term_conv \<circ> mctxt_of_term \<circ> \<sigma>"])
      apply (subst B)
      apply (subst (1 2) mctxt_term_conv_fill_holes_mctxt; (simp add: max_top_prefix; fail)?)
      unfolding map_update *
      apply (subst hole_poss'_map_vars_mctxt[of Some "max_top s", symmetric])
      apply (subst fill_holes_rstep_r_p_s')
      using inner(1-2) rstep_r_p_s'_stable[OF inner(3), of "Var \<circ> Some"]
      apply (auto simp: max_top_prefix comp_def subst_compose_def r)
      done
  qed
  then show ?thesis
    by (auto intro!: mirror_step.intros[OF assms(4)] short_stepI[OF assms(1,2), OF r_into_rtrancl])
qed

lemma single_step_to_tall_step:
  assumes "s \<in> native_terms"
    "(B, ss) = base_decomp s" "p \<notin> poss_mctxt B" "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  shows "(s, t) \<in> tall_step"
proof -
  obtain i ti where "i < length ss" "t = fill_holes B (ss[i := ti])"
    "(ss ! i, ti) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' B ! i)) \<sigma>"
    using assms rewrite_cases[of B ss t \<R> l r p \<sigma>]
    by (simp only: base_decomp_fill_holes) metis
  then show ?thesis using assms
    by (intro tall_step.intros[of s B ss "ss[i := ti]" t])
      (fastforce simp: base_decomp_fill_holes nth_list_update rstep'_iff_rstep_r_p_s')+
qed

lemma single_step_to_any_step:
  "s \<in> native_terms \<Longrightarrow> (s, t) \<in> rstep' \<R> \<Longrightarrow> (s, t) \<in> short_step \<union> tall_step"
  using single_step_to_short_step[of s] single_step_to_tall_step[of s]
  by (auto simp: rstep'_iff_rstep_r_p_s') (metis surj_pair)

lemma mirror_step_to_short_step:
  assumes "L \<in> shallow_context" "set ss \<subseteq> short_terms"
    "length ss = num_holes L" "length ts = num_holes M"
    "((fill_holes L ss, L), (fill_holes M ts, M)) \<in> mirror_step"
  shows "(fill_holes L ss, fill_holes M ts) \<in> short_step"
proof -
  obtain l r p \<sigma> \<tau> where *: "(fill_holes L ss, fill_holes M ts) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    "(mctxt_term_conv L, mctxt_term_conv M) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>"
    using assms(5) by auto
  note ** = fill_shallow_context_imp_native[OF assms(1) assms(3)[symmetric] assms(2)]
  moreover have "p \<in> poss_mctxt L" using  wf_trs_implies_fun_poss[OF trs *(2)]
    fun_poss_mctxt_subset_poss_mctxt by (auto simp: fun_poss_mctxt_def[symmetric])
  then have "p \<in> poss_mctxt (fst (base_decomp (fill_holes L ss)))"
    using base_decomp_max[OF ** assms(1) _ prod.collapse] assms(3) poss_mctxt_mono by fastforce
  ultimately show ?thesis
    by (intro single_step_to_short_step[OF _ prod.collapse _ *(1)])
qed

lemma mirror_steps_to_short_steps:
  assumes "L \<in> shallow_context" "set ss \<subseteq> short_terms"
    "length ss = num_holes L" "length ts = num_holes M"
    "((fill_holes L ss, L), (fill_holes M ts, M)) \<in> mirror_step\<^sup>*"
  shows "(fill_holes L ss, fill_holes M ts) \<in> short_step\<^sup>*"
  using assms(5,1-4)
proof (induct "(fill_holes L ss, L)" arbitrary: L ss rule: converse_rtrancl_induct)
  case (step z)
  obtain z1 z2 where z: "z = (z1, z2)" by (metis prod.collapse)
  note mirror_step_preserves_prefix[OF _ step(1)[unfolded z]]
  moreover then have "(fill_holes z2 (unfill_holes z2 z1), fill_holes M ts) \<in> short_step\<^sup>*"
    using step(1,4,5,6) assms(4) mirror_step_aliens_mono[OF step(6), of "unfill_holes z2 z1" z2]
    by (intro step(3))
      (auto simp: fill_unfill_holes z rstep'_iff_rstep_r_p_s' intro!: shallow_context_closed[OF step(4), of z2], blast)
  ultimately show ?case
    using mirror_step_to_short_step[OF step(4,5,6), of "unfill_holes z2 z1" z2] step(1,6)
    by (auto simp: z fill_unfill_holes)
qed auto

text \<open>{cite \<open>Lemma 4.21\<close> FMZvO15}\<close>

lemma tall_short:
  assumes
    "C \<in> shallow_context" "set ss \<subseteq> short_terms"
    "num_holes C = length ss" "num_holes C = length ts"
    "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*"
  obtains ss' \<iota> where
    "num_holes C = length ss'"
    "(fill_holes C ss, fill_holes C ss') \<in> tall_step_i \<iota>" "\<iota> \<le> imbalance ts"
    "(fill_holes C ss', fill_holes C ts) \<in> short_step\<^sup>*"
proof -
  let ?s = "fill_holes C ss"
  have "?s \<in> native_terms" "?s \<in> \<T>"
    using fill_shallow_context_imp_native[OF assms(1,3,2)] by (simp_all add: native_terms_def)
  obtain B ss0 where B: "(B, ss0) = base_decomp ?s" "hole_poss B \<subseteq> hole_poss C"
    using shallow_to_base_no_new_holes[OF assms(1,3,2)] by (metis surj_pair)
  let ?Bs = "unfill_holes_mctxt C B"
  have "C \<le> B" using base_decomp_max[OF \<open>?s \<in> native_terms\<close> assms(1) fill_holes_suffix[OF assms(3)] B(1)] .
  let ?ss' = "map (\<lambda>i. if ?Bs ! i = MHole then ts ! i else ss ! i) [0..<num_holes C]"
  let ?ts' = "map (\<lambda>i. ts ! i) (filter (\<lambda>i. ?Bs ! i = MHole) [0..<num_holes C])"
  have hp: "[p\<leftarrow>hole_poss' C . subm_at B p = MHole] = hole_poss' B"
    using \<open>C \<le> B\<close> \<open>hole_poss B \<subseteq> hole_poss C\<close> unfolding set_hole_poss'[symmetric]
  proof (induct C B rule: less_eq_mctxt_induct)
    case (1 B)
    then show ?case by (cases B, auto simp: UN_subset_iff image_subset_iff)
  next
   case (3 cs ds f) show ?case using 3(1,4)
      by (auto simp: filter_concat filter_map comp_def intro!: arg_cong[of _ _ "concat"] arg_cong[of _ _ "map _"] 3(3))
         (auto dest!: subsetD)
  qed auto
  have ss0: "ss0 = map ((!) ss) [i\<leftarrow>[0..<num_holes C] . unfill_holes_mctxt C B ! i = MHole]"
    using assms(3) filter_map[of "\<lambda>p. subm_at B p = MHole" "(!) (hole_poss' C)" "[0..<num_holes C]", unfolded comp_def]
      map_nth[of "hole_poss' C"]
    unfolding unfill_holes_mctxt_conv[OF \<open>C \<le> B\<close>] hp[symmetric]
      unfill_fill_holes[OF base_decomp_fill_holes(1)[OF B(1)], symmetric, unfolded filter_map base_decomp_fill_holes(2)[OF B(1)] unfill_holes_conv[OF base_decomp_prefix[OF B(1)]]]
    by (auto simp: comp_def) (auto intro!: map_cong subt_at_fill_holes filter_cong)
  have "p \<in> hole_poss C \<Longrightarrow> subm_at B p \<noteq> MHole \<Longrightarrow> subm_at (mctxt_of_term ?s) p = subm_at B p" for p
    unfolding base_decomp_fill_holes(2)[OF B(1), symmetric] using \<open>C \<le> B\<close> B(2) base_decomp_fill_holes(1)[OF B(1), symmetric]
  proof (induct C B arbitrary: p ss0 rule: less_eq_mctxt_induct)
    case (1 B) moreover then have "hole_poss B = {}"
      by auto (metis 1(1,2) empty_iff hole_poss.simps(2) subm_at_hole_poss subset_singletonD)
    ultimately show ?case using length_hole_poss'[of B] set_hole_poss'[of B]
      by (auto simp del: length_hole_poss') (metis fill_holes_suffix list.size(3) unfill_by_itselfD unfill_fill_holes)
  next
    case (3 cs ds f) show ?case using 3(1,2,4,5,6,7) by (auto intro!: 3(3)) auto
  qed auto
  from this[OF nth_mem[of _ "hole_poss' C", unfolded set_hole_poss']]
  have B': "B = fill_holes_mctxt C (map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then MHole else mctxt_of_term (ss ! i)) [0..<num_holes C])"
    apply (subst fill_unfill_holes_mctxt[OF \<open>C \<le> B\<close>, symmetric])
    using \<open>C \<le> B\<close> subm_at_fill_holes_mctxt[of "map mctxt_of_term ss" C, symmetric]
    by (auto intro!: nth_equalityI arg_cong[of _ _ "fill_holes_mctxt C"] simp: unfill_holes_mctxt_conv assms(3))
  have ts: "set ts \<subseteq> short_terms" by (metis assms(2-5) short_sequence_rsteps(1))
  show thesis
  proof (intro that[of ?ss' "imbalance ?ts'"], goal_cases)
    case 2 then show ?case
    proof (intro tall_step_i.intros[OF B(1) \<open>?s \<in> native_terms\<close> _ _ _ refl, of ?ts'], goal_cases)
      case 1
      have *: "filter (\<lambda>p. subm_at B p = MHole) (hole_poss' C) =
        map ((!) (hole_poss' C)) [i\<leftarrow>[0..<num_holes C] . map (subm_at B) (hole_poss' C) ! i = MHole]"
        using filter_map[of "\<lambda>p. subm_at B p = MHole" "(!) (hole_poss' C)" "[0..<num_holes C]"]
        by (auto simp: comp_def length_hole_poss'[of C, symmetric] map_nth simp del: length_hole_poss'
          cong: map_cong intro!: arg_cong[of _ _ "map ((!) (hole_poss' C))"] filter_cong)
      from arg_cong[OF hp, of length] show ?case using \<open>C \<le> B\<close> by (simp add: unfill_holes_mctxt_conv *)
    next
      case 2
      show ?case using \<open>C \<le> B\<close>
        apply (subst (2) B')
        apply (subst fill_holes_mctxt_fill_holes, simp, simp add: num_holes_fill_holes_mctxt comp_def if_distrib length_filter_sum_list cong: if_cong)
        apply (intro arg_cong[of _ _ "fill_holes _"] map_cong refl)
        using arg_cong[OF partition_by_predicate[of _ "[0..<num_holes C]" "\<lambda>i. unfill_holes_mctxt C B ! i = MHole"], of _ "map ((!) ts)"]
        by (simp add: comp_def if_distrib cong: if_cong)
    next
      case (3 i)
      show ?case using 3 base_decomp_fill_holes(1)[OF B(1), symmetric] assms(3,4) \<open>C \<le> B\<close>
        nth_mem[of i "[i\<leftarrow>[0..<length ss] . unfill_holes_mctxt C B ! i = MHole]"] by (auto intro!: assms(5) simp: ss0)
    qed
  next
    case 3 then show ?case using assms(4) by (auto simp: imbalance_def image_def intro!: card_mono)
  next
    case 4
    have *: "fill_holes_mctxt C (map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then MHole else mctxt_of_term (ss ! i)) [0..<num_holes C]) \<in> shallow_context"
      unfolding B'[symmetric] using base_decomp_shallow[OF \<open>?s \<in> \<T>\<close> B(1)] .
    { fix n
      assume "\<And>i. n \<le> i \<Longrightarrow> i < num_holes C \<Longrightarrow> ss ! i = ts ! i"
      then have
       "(fill_holes C (map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then ts ! i else ss ! i)
        [0..<num_holes C]), fill_holes C ts) \<in> short_step\<^sup>*" (is "?X ss")
        using assms(3,5,2) *
      proof (induct n arbitrary: ss)
        case 0
        then have "(map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then ts ! i else ss ! i) [0..<num_holes C]) = ts"
          using assms(4) by (auto intro!: nth_equalityI)
        then show ?case by simp
      next
        case (Suc n) then show ?case
        proof (cases "n < length ss")
          case True
          from Suc(2) have **: "n \<le> i \<Longrightarrow> i < num_holes C \<Longrightarrow> ss[n := ts ! n] ! i = ts ! i"
            "i < length ss \<Longrightarrow> (ss[n := ts ! n] ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*" for i
            using assms(4) Suc(3,4) by (cases "n = i"; simp)+
          moreover have "set (ss[n := ts ! n]) \<subseteq> short_terms"
            using True Suc(3,5) ts assms(4) by (auto simp: set_conv_nth nth_list_update)
          moreover
          have *: "fill_holes_mctxt C (map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then MHole else mctxt_of_term (ss[n := ts ! n] ! i)) [0..<num_holes C]) \<in> shallow_context"
            using Suc(3) Suc(4)[of n] True
            by (auto simp: mctxt_term_conv_fill_holes_mctxt nth_list_update intro!: shallow_context_closed'[OF Suc(6)] fill_holes_rsteps rsteps'_stable)
          ultimately have "?X (ss[n := ts ! n])" (is "(?F (ss[n := ts ! n]), _) \<in> _")
            using Suc(1)[of "ss[n := ts ! n]"] Suc(3,5) by auto
          moreover have "(?F ss, ?F (ss[n := ts ! n])) \<in> short_step\<^sup>*"
            using Suc(4)[OF True] True Suc(5,3,6)
          proof (induct "ss ! n" arbitrary: ss rule: converse_rtrancl_induct)
            case (step ssn')
            obtain l r p \<sigma> where sss: "(ss ! n, ssn') \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
              using step(1)[unfolded rstep'_iff_rstep_r_p_s'] by blast 
            have "(?F ss, ?F (ss[n := ssn'])) \<in> short_step\<^sup>="
            proof (cases "unfill_holes_mctxt C B ! n = MHole")
              case True then show ?thesis
                using step(4) by (intro UnI2) (auto simp: nth_list_update intro!: arg_cong[of _ _ "fill_holes _"])
            next
              case False
              then have *: "map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then ts ! i else ss[n := ssn'] ! i) [0..<num_holes C] =
                (map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then ts ! i else ss ! i) [0..<num_holes C])[n := ssn']"
                using step(4) by (auto simp: nth_list_update intro!: nth_equalityI)
              show ?thesis using step(4-) ts assms(4) unfolding *
              proof (intro UnI1 single_step_to_short_step[OF _ prod.collapse, of _ "hole_poss' C ! n @ p" _ l r \<sigma>] fill_shallow_context_imp_native, goal_cases)
                case 4
                let ?B' = "fill_holes_mctxt C (map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then MHole else mctxt_of_term (ss ! i)) [0..<num_holes C])"
                show ?case
                proof (subst subsetD[OF poss_mctxt_mono[OF base_decomp_max], OF _ _ _ prod.collapse, of _ ?B'], goal_cases)
                  case 1 then show ?case
                    using assms(1,4) step(5,6) ts by (intro fill_shallow_context_imp_native) auto
                next
                  case 2 then show ?case using step(7) .
                next
                  case 4 then show ?case using step(4) step(6)[symmetric] set_hole_poss'[of C]
                    unfolding poss_mctxt_append_poss_mctxt
                    using subsetD[OF _ nth_mem, of _ "hole_poss C"] wf_trs_implies_fun_poss[OF trs sss] False
                    by (intro conjI subsetD[OF fill_holes_mctxt_extends_all_poss])
                      (auto simp: all_poss_mctxt_conv subm_at_fill_holes_mctxt fun_poss_imp_poss)
                qed (auto simp: mctxt_of_term_fill_holes' less_eq_fill_holes_iff)
              next
                case 5
                then show ?case using sss False
                  apply (subst replace_at_fill_holes[symmetric], simp, simp)
                  apply (intro HOL.subst[of _ _ "\<lambda>t. (t, _) \<in> _", OF _ HOL.subst[of _ _ "\<lambda>p. _ \<in> rstep_r_p_s' _ _ (p @ _) _", OF _ rstep_r_p_s'_mono]],
                    subst ctxt_supt_id)
                  by (auto simp: hole_poss_in_poss_fill_holes subt_at_fill_holes)
              qed (auto simp: assms(1))
            qed
            moreover have "set (ss[n := ssn']) \<subseteq> short_terms"
              using short_terms_closed[OF _ step(1)] step(4,5) set_update_subset_insert[of ss n ssn']
              by (auto simp: subset_eq)
            moreover note step(7)
            then have "fill_holes_mctxt C (map (\<lambda>i. if unfill_holes_mctxt C B ! i = MHole then MHole else mctxt_of_term (ss[n := ssn'] ! i)) [0..<num_holes C]) \<in> shallow_context"
              using step(1,4)
              by (auto 0 3 simp: mctxt_term_conv_fill_holes_mctxt nth_list_update
                intro!: shallow_context_closed'[OF step(7)] fill_holes_rsteps rsteps'_stable)
            ultimately show ?case using step(3)[of "ss[n := ssn']"] step(4-6) by (auto cong: if_cong)
          qed (auto cong: if_cong)
          ultimately show ?thesis by auto
        qed auto
      qed
    } note this[of "num_holes C"]
    then show ?case by auto
  qed auto
qed

text \<open>{cite \<open>Lemma 4.23\<close> FMZvO15}\<close>

lemma tall_tall_peak:
  assumes "(s, t) \<in> tall_step_i \<iota>" "(s, u) \<in> tall_step_i \<kappa>"
  obtains \<iota>' \<kappa>' t' u' v where "\<iota>' \<le> \<iota>" "\<kappa>' \<le> \<kappa>"
    "(t, t') \<in> tall_step_i \<kappa>'" "(t', v) \<in> short_step\<^sup>*"
    "(u, u') \<in> tall_step_i \<iota>'" "(u', v) \<in> short_step\<^sup>*"
proof -
  from assms obtain B ss ts us where
    s: "s \<in> native_terms" "(B, ss) = base_decomp s" and
    t: "length ts = num_holes B" "t = fill_holes B ts"
      "\<And>i. i < num_holes B \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*" "\<iota> = imbalance ts" and
    u: "length us = num_holes B" "u = fill_holes B us"
      "\<And>i. i < num_holes B \<Longrightarrow> (ss ! i, us ! i) \<in> (rstep' \<R>)\<^sup>*" "\<kappa> = imbalance us"
    by (elim tall_step_i.cases) (auto, metis prod.inject)
  have B: "B \<in> shallow_context" "set ss \<subseteq> short_terms" "num_holes B = length ss"
    using s aliens_short_terms[of s] base_decomp_aliens[OF _ s(2)]
    by (auto simp: native_terms_def base_decomp_shallow base_decomp_fill_holes)
  then obtain vs where *: "length vs = length ss"
    "\<And>i. i < length ss \<Longrightarrow> (ts ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
    "\<And>i. i < length ss \<Longrightarrow> (us ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
    "ts \<propto> vs" "us \<propto> vs"
    "set ts \<subseteq> short_terms" "set us \<subseteq> short_terms" "set vs \<subseteq> short_terms"
    using balance_short_sequences[of ts ss us] t(1-3) u(1-3) by auto
  moreover obtain ts' \<iota>' where "num_holes B = length ts'"
    "(fill_holes B ts, fill_holes B ts') \<in> tall_step_i \<iota>'"
    "\<iota>' \<le> imbalance vs" "(fill_holes B ts', fill_holes B vs) \<in> short_step\<^sup>*"
    using tall_short[OF B(1) *(6) t(1)[symmetric], of vs thesis] *(1,2) t(1) B(3) by auto
  moreover obtain us' \<kappa>' where "num_holes B = length us'"
    "(fill_holes B us, fill_holes B us') \<in> tall_step_i \<kappa>'"
    "\<kappa>' \<le> imbalance vs" "(fill_holes B us', fill_holes B vs) \<in> short_step\<^sup>*"
    using tall_short[OF B(1) *(7) u(1)[symmetric], of vs thesis] *(1,3) u(1) B(3) by auto
  ultimately show ?thesis
    by (intro that[of \<kappa>' \<iota>' "fill_holes B ts'" "fill_holes B vs" "fill_holes B us'"])
      (auto dest!: refines_imbalance_mono simp: t(2,4) u(2,4))
qed

text \<open>{cite \<open>Lemma 4.25\<close> FMZvO15}\<close>

lemma base_decomp_short:
  assumes "t \<in> native_terms" "(B, ss) = base_decomp t"
  shows "set ss \<subseteq> short_terms"
  using aliens_short_terms[OF assms(1)] assms(2) by (auto simp: base_decomp_def Let_def)

lemma tall_short_peak:
  assumes "(s, t) \<in> tall_step_i \<iota>" "(s, u) \<in> short_step"
  obtains \<iota>' \<iota>'' t' u' v where "\<iota>' \<le> \<iota>"
    "t = t' \<or> \<iota>'' < \<iota> \<and> (t, t') \<in> tall_step_i \<iota>''" "(t', v) \<in> short_step\<^sup>*"
    "(u, u') \<in> tall_step_i \<iota>'" "(u', v) \<in> short_step\<^sup>*"
proof -
  obtain B ss where B: "base_decomp s = (B, ss)" by (metis prod.exhaust)
  obtain ts where ts: "s \<in> native_terms" "length ts = num_holes B" "t = fill_holes B ts"
    "\<And>i. i < num_holes B \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*" "\<iota> = imbalance ts" "s \<in> \<T>"
    using assms(1) by (auto simp: B native_terms_def elim!: tall_step_i.cases)
  have ss: "set ss \<subseteq> short_terms" "length ss = num_holes B" and s: "s = fill_holes B ss"
    using base_decomp_short[OF ts(1)] by (auto simp: B base_decomp_fill_holes[OF B[symmetric]])
  obtain C where C: "((s, B), (u, C)) \<in> mirror_step\<^sup>*"
    using assms(2) by (auto simp: B elim!: short_stepE)
  obtain us where us: "length us = num_holes C" "u = fill_holes C us" "set us \<subseteq> set ss"
    "((fill_holes B (map f ss), B), (fill_holes C (map f us), C)) \<in> mirror_step\<^sup>*"
    "C \<in> shallow_context" for f
    using C ss(2) base_decomp_shallow[OF \<open>s \<in> \<T>\<close> B(1)[symmetric]] unfolding s
  proof (induct "(u, C)" arbitrary: u C thesis rule: rtrancl_induct)
    case (step y)
    obtain y1 y2 where [simp]: "y = (y1, y2)" by (metis prod.collapse)
    obtain us where us: "length us = num_holes y2" "y1 = fill_holes y2 us" "set us \<subseteq> set ss"
      "\<And>f. ((fill_holes B (map f ss), B), (fill_holes y2 (map f us), y2)) \<in> mirror_step\<^sup>*"
      "y2 \<in> shallow_context"
      using step(3)[OF prod.collapse[symmetric] _ step(5)] step(6) unfolding \<open>y = (y1, y2)\<close> fst_conv snd_conv by blast
    have "(mctxt_term_conv y2, mctxt_term_conv C) \<in> rstep' \<R>"
      by (metis step(2) \<open>y = (y1, y2)\<close> mirror_step.simps rstep'_iff_rstep_r_p_s')
    moreover have "((fill_holes B (map f ss), B), fill_holes C (map f (unfill_holes C u)), C) \<in> mirror_step\<^sup>*" for f
      using mirror_step_preserves_prefix[of "y2" "y1" u C] step(2) us(1,2,4)
      by simp (metis (no_types, lifting) fill_unfill_holes length_unfill_holes mirror_step_stable rtrancl.simps)
    ultimately show ?case using mirror_step_aliens_mono[of us "y2" "unfill_holes C u" C]
      mirror_step_preserves_prefix[of "y2" "y1" u C] step(2) us(1-3)
      by (auto intro!: step(4)[of "unfill_holes C u"] shallow_context_closed[OF us(5)] simp: fill_unfill_holes)
  qed auto
  obtain vs where vs:
    "\<And>i. i < length ss \<Longrightarrow> (ts ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
    "ss \<propto> vs" "ts = vs \<or> imbalance vs < imbalance ts"
  proof (cases "ss \<propto> ts" rule: case_split)
    case True then show ?thesis by (auto intro: that[of ts])
  next
    case False
    moreover obtain vs where "\<And>i. i < length ss \<Longrightarrow> (ts ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
      "ss \<propto> vs" "ts \<propto> vs" "set ts \<subseteq> short_terms"
      by (metis balance_short_sequences[of ss ss ts] ss ts(2,4) rtrancl_refl)
    ultimately show ?thesis using refines_imbalance_strict_mono[of ts vs] refines_trans[of ss vs ts]
      by (auto intro!: that[of vs])
  qed
  then have *: "\<And>i. i < length ss \<Longrightarrow> (ss ! i, vs ! i) \<in> (rstep' \<R>)\<^sup>*"
    using ts(2) ts(4) ss(2) by force
  obtain f where f: "vs = map f ss" using \<open>ss \<propto> vs\<close> by (auto elim: refines_imp_map)
  have "((fill_holes B (map f ss), B), (fill_holes C (map f us), C)) \<in> mirror_step\<^sup>*" using us(4) .
  have "i < length us \<Longrightarrow> (us ! i, map f us ! i) \<in> (rstep' \<R>)\<^sup>*" for i
    using f ss(2) us(1) * subsetD[OF us(3), unfolded in_set_conv_nth] by auto metis
  with tall_short[of C us "map f us", OF us(5) subset_trans[OF us(3) ss(1)]]
  (* right tall-short sequence *)
  obtain us' \<iota>' where us':
    "num_holes C = length us'" "(fill_holes C us, fill_holes C us') \<in> tall_step_i \<iota>'"
    "\<iota>' \<le> imbalance (map f us)"
    "(fill_holes C us', fill_holes C (map f us)) \<in> short_step\<^sup>*" unfolding length_map us(1) by blast
  moreover have "\<iota>' \<le> \<iota>" using us'(3) us(3) ts(5) vs(3) imbalance_mono[of "map f us" "map f ss"]
    by (auto simp: image_mono f)
  (* left tall-short sequence *)
  moreover have "set ts \<subseteq> short_terms" using ss(1,2) ts(2,4)
    by (auto simp: in_set_conv_nth) (metis nth_mem short_terms_closed' subset_code(1))
  then obtain ts' \<iota>'' where ts':
    "num_holes B = length ts'" "(fill_holes B ts, fill_holes B ts') \<in> tall_step_i \<iota>''"
    "\<iota>'' \<le> imbalance vs"
    "(fill_holes B ts', fill_holes B vs) \<in> short_step\<^sup>*"
    using base_decomp_shallow[OF ts(6) B[symmetric]] vs(1) tall_short[of B ts vs thesis]
    unfolding ss(2) ts(2) conjunct1[OF \<open>ss \<propto> vs\<close>[unfolded refines_def]] by blast
  moreover have "ts = vs \<or> \<iota>'' < \<iota>" using vs(3) ts'(3) ts(5) by auto
  moreover have "set (map f ss) \<subseteq> short_terms" using ss(1) short_terms_closed'[OF _ *]
    using "*" f length_map short_sequence_rsteps(1) by blast
  then have "(fill_holes B vs, fill_holes C (map f us)) \<in> short_step\<^sup>*"
    using us(4)[of f] base_decomp_shallow[OF ts(6) B[symmetric]] ss(2) us(1) unfolding f
    by (intro mirror_steps_to_short_steps) simp_all
  ultimately show ?thesis
    by (intro that[of \<iota>' "fill_holes B (if ts = vs then vs else ts')" \<iota>'' "fill_holes C (map f us)" "fill_holes C us'"])
      (auto simp: ts(3) us(2))
qed

text \<open>Common analysis for short-short peaks.\<close>

lemma rsteps_to_mirror_steps:
  "(s, t) \<in> (rstep' \<R>)\<^sup>* \<Longrightarrow> ((s \<cdot> \<sigma>, term_mctxt_conv (s \<cdot> \<tau>)), (t \<cdot> \<sigma>, term_mctxt_conv (t \<cdot> \<tau>))) \<in> mirror_step\<^sup>*"
proof (induct t rule: rtrancl_induct)
  case (step t t')
  obtain l r p \<sigma>' where "(t, t') \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>'"
    using step(2) by (auto simp: rstep'_iff_rstep_r_p_s')
  then show ?case using mirror_step.intros[of "t \<cdot> \<sigma>" "t' \<cdot> \<sigma>" l r p "\<sigma>' \<circ>\<^sub>s \<sigma>"
      "term_mctxt_conv (t \<cdot> \<tau>)" "term_mctxt_conv (t' \<cdot> \<tau>)" "\<sigma>' \<circ>\<^sub>s \<tau>"] step(3)
    by (force intro: rstep_r_p_s'_stable)
qed auto

lemma short_term_from_shallow_context:
  assumes "B \<in> shallow_context" "length ss = num_holes B" "\<And>s. s \<in> set ss \<Longrightarrow> is_Var s"
  shows "fill_holes B ss \<in> short_terms"
proof -
  obtain L Cs where L: "L \<in> \<LL>" "length Cs = num_holes L" "B = fill_holes_mctxt L Cs"
    "set Cs \<subseteq> {MHole} \<union> mctxt_of_term ` shorter_terms" by (metis shallow_context.cases[OF assms(1)])
  have *: "fill_holes B ss \<in> \<T>" using subsetD[OF funas_shallow_context[OF assms(1)]] assms(2,3)
    by (force simp: \<T>_def funas_term_fill_holes_iff is_Var_def)
  define ss' where "ss' = map (\<lambda>i. fill_holes (Cs ! i) (partition_holes ss Cs ! i)) [0..<num_holes L]"
  have s: "fill_holes B ss = fill_holes L ss'" "length ss' = num_holes L"
    using L(2) assms(2) by (auto simp add: fill_holes_mctxt_fill_holes L(3) ss'_def)
  have "i < num_holes L \<Longrightarrow> is_Fun (ss' ! i) \<Longrightarrow> ss' ! i \<in> shorter_terms" for i
    unfolding ss'_def using length_partition_by_nth[of "map num_holes Cs" ss i] assms(2,3)
      partition_by_nth_nth_elem[of "map num_holes Cs" ss i 0] subsetD[OF L(4), OF nth_mem, of i]
    by (cases "partition_holes ss Cs ! i") (auto simp: L(2,3) num_holes_fill_holes_mctxt)
  then have "set (filter is_Fun ss') \<subseteq> shorter_terms" by auto (auto simp: s(2) set_conv_nth)
  from subsetD[OF this] have "rank (fill_holes B ss) \<le> Suc rk" using L(1)
    by (subst le_trans[OF rank_by_top'[OF * max_top_props(2), of L]])
      (auto simp: s shorter_terms_def ss'_def[symmetric] unfill_fill_holes topsC_def max_list_bound_set)
  then show ?thesis using * by (simp add: short_terms_def)
qed

lemma short_short_pre:
  assumes "(s, t) \<in> short_step_s s0" "(s, u) \<in> short_step_s s1"
  obtains B ss C D E v where
    "s \<in> native_terms" "(B, ss) = base_decomp s"
    "((s, B),(t, C)) \<in> mirror_step\<^sup>*" "((s, B),(u, D)) \<in> mirror_step\<^sup>*"
    "C \<in> shallow_context" "C \<le> mctxt_of_term t"
    "D \<in> shallow_context" "D \<le> mctxt_of_term u"
    "t \<in> native_terms" "(s1, t) \<in> (rstep \<R>)\<^sup>*" "((t, C), (v, E)) \<in> mirror_step\<^sup>*"
    "u \<in> native_terms" "(s0, u) \<in> (rstep \<R>)\<^sup>*" "((u, D), (v, E)) \<in> mirror_step\<^sup>*"
proof -
  obtain B ss C D where
    st: "(s0, s) \<in> (rstep \<R>)\<^sup>*" "((s, B),(t, C)) \<in> mirror_step\<^sup>*" and
    su: "(s1, s) \<in> (rstep \<R>)\<^sup>*" "((s, B),(u, D)) \<in> mirror_step\<^sup>*" and
    s: "s \<in> native_terms" "(B, ss) = base_decomp s"
    by (metis short_step_sE[OF assms(1)] short_step_sE[OF assms(2)] Pair_inject)
  have "B \<in> shallow_context" using base_decomp_shallow[OF _ s(2)] s(1)
    by (simp add: native_terms_def)
  have "B \<le> mctxt_of_term s" using base_decomp_prefix[OF s(2)] .
  have "ss = unfill_holes B s"using base_decomp_fill_holes[OF s(2)] by (metis unfill_fill_holes)
  obtain b0 \<sigma> where b0: "b0 \<cdot> \<sigma> = mctxt_term_conv B" "\<And>x. \<sigma> x \<in> {Var (Some x), Var None}"
    "\<And>D. B \<le> D \<Longrightarrow> \<exists>\<tau>. b0 \<cdot> \<tau> = mctxt_term_conv D \<and> (\<forall>x. \<sigma> x = Var None \<or> \<tau> x = Var (Some x))"
    using represent_context_by_term[of B] by blast
  obtain \<tau> where \<tau>: "b0 \<cdot> \<tau> = s \<cdot> (Var \<circ> Some)" "\<And>x. \<sigma> x = Var None \<or> \<tau> x = Var (Some x)"
    using b0(3)[OF base_decomp_prefix[OF s(2)]] by auto
  define f where "f \<equiv> \<lambda>s. Var (SOME x. \<sigma> x = Var None \<and> \<tau> x = s \<cdot> (Var \<circ> Some)) :: ('f, 'v) term"
  define b where "b = fill_holes B (map f ss)"
  have *: "s = b0 \<cdot> \<tau> \<circ>\<^sub>s (Var \<circ> the)" using \<open>B \<le> mctxt_of_term s\<close> \<tau>(1)
    by simp (simp del: subst_subst_compose add: subst_subst_compose[symmetric] subst_compose_def fill_unfill_holes)
  have "b \<in> short_terms" using \<open>B \<in> shallow_context\<close> base_decomp_fill_holes(1)[OF s(2)]
    unfolding b_def f_def by (auto intro!: short_term_from_shallow_context simp: is_Var_def)
  have "b0 \<cdot> (\<tau> \<circ>\<^sub>s (Var \<circ> the) \<circ>\<^sub>s (Var \<circ> Some)) = b0 \<cdot> \<tau>" using \<tau>
    by simp (simp del: subst_subst_compose add: subst_subst_compose[symmetric] subst_compose_def)
  then have [simp]: "x \<in> vars_term b0 \<Longrightarrow> \<sigma> x = Var None \<Longrightarrow> \<tau> x \<cdot> (\<lambda>x. Var (Some (the x))) = \<tau> x" for x
    by (auto simp del: subst_subst_compose simp: term_subst_eq_conv subst_subst_compose[symmetric] subst_compose_def)
  have "x \<in> vars_term b0 \<Longrightarrow> \<sigma> x = Var None \<Longrightarrow> f (\<tau> x \<cdot> (Var \<circ> the)) \<cdot> \<sigma> = Var None" for x
    using someI[of "\<lambda>y. \<sigma> y = Var None \<and> \<tau> y = \<tau> x \<cdot> (Var \<circ> the) \<cdot> (Var \<circ> Some)" x]
    unfolding f_def subst_subst_compose[symmetric] subst_compose_def by auto
  then have bB: "b \<cdot> \<sigma> = mctxt_term_conv B"
    unfolding b_def \<open>ss = unfill_holes B s\<close>
    apply (subst alien_map_by_substitution[OF b0(1)[symmetric], of _ "\<tau> \<circ>\<^sub>s (Var \<circ> the)"])
    subgoal using b0(2) by (auto simp: is_Var_def)
    subgoal using \<open>B \<le> mctxt_of_term s\<close> by simp
    subgoal using \<open>B \<le> mctxt_of_term s\<close> by (simp add: fill_unfill_holes *)
    using \<open>B \<le> mctxt_of_term s\<close> b0(2) \<tau>(2)
    unfolding b0(1)[symmetric] subst_subst_compose[symmetric] term_subst_eq_conv
    by (force simp: subst_compose_def)
  have "x \<in> vars_term b0 \<Longrightarrow> \<sigma> x = Var None \<Longrightarrow> f (\<tau> x \<cdot> (Var \<circ> the)) \<cdot> \<tau> = \<tau> x" for x
    using someI[of "\<lambda>y. \<sigma> y = Var None \<and> \<tau> y = \<tau> x \<cdot> (Var \<circ> the) \<cdot> (Var \<circ> Some)" x]
    unfolding f_def subst_subst_compose[symmetric] subst_compose_def by auto
  then have bs: "b \<cdot> \<tau> = s \<cdot> (Var \<circ> Some)"
    unfolding b_def \<open>ss = unfill_holes B s\<close>
    apply (subst alien_map_by_substitution[OF b0(1)[symmetric], of _ "\<tau> \<circ>\<^sub>s (Var \<circ> the)"])
    subgoal using b0(2) by (auto simp: is_Var_def)
    subgoal using \<open>B \<le> mctxt_of_term s\<close> by simp
    subgoal using \<open>B \<le> mctxt_of_term s\<close> by (simp add: fill_unfill_holes *)
    using \<open>B \<le> mctxt_of_term s\<close> b0(2) \<tau>(2)
    unfolding \<tau>(1)[symmetric] subst_subst_compose[symmetric] term_subst_eq_conv
    by (force simp: subst_compose_def)
  { fix t C assume "((s, B),(t, C)) \<in> mirror_step\<^sup>*"
    then have "\<exists>c. (b, c) \<in> (rstep' \<R>)\<^sup>* \<and> c \<cdot> \<sigma> = mctxt_term_conv C \<and> c \<cdot> \<tau> = t \<cdot> (Var \<circ> Some)"
      using bB bs \<open>B \<le> mctxt_of_term s\<close> unfolding b_def \<open>ss = unfill_holes B s\<close>
    proof (induct "(s, B)" arbitrary: s B rule: converse_rtrancl_induct)
      case (step sB)
      from step(1) obtain s' B' l r p \<sigma>' \<tau>' where
        sB: "sB = (s', B')" and
        ss': "(s, s') \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>'" and
        BB': "(mctxt_term_conv B, mctxt_term_conv B') \<in> rstep_r_p_s' \<R> (l, r) p \<tau>'"
        using mirror_step.cases prod.collapse by metis
      have "B' \<le> mctxt_of_term s'" using mirror_step_preserves_prefix[OF \<open>B \<le> mctxt_of_term s\<close> step(1)[unfolded sB]] .
      let ?sf = "fill_holes B (map f (unfill_holes B s))"
      let ?sf' = "fill_holes B' (map f (unfill_holes B' s'))"
      obtain \<rho> where x: "(?sf, ?sf') \<in> rstep_r_p_s' \<R> (l, r) p \<rho>"
        using \<open>B \<le> mctxt_of_term s\<close> \<open>B' \<le> mctxt_of_term s'\<close> ss' BB' 
          rewrite_balanced_aliens'[OF trs, of "unfill_holes B s" B "unfill_holes B' s'" B' l r p \<sigma>' \<tau>' f]
        by (auto simp: fill_unfill_holes)
      have "(?sf, ?sf') \<in> rstep' \<R>" "?sf' \<cdot> \<sigma> = mctxt_term_conv B'" "?sf' \<cdot> \<tau> = s' \<cdot> (Var \<circ> Some)"
        using rstep_r_p_s'_stable[OF ss', of "Var \<circ> Some"] BB'
          rstep_r_p_s'_stable[OF x, of \<sigma>] rstep_r_p_s'_stable[OF x, of \<tau>] x unfolding step(4,5)
        by (auto intro: rstep_r_p_s'_deterministic[OF trs] simp: rstep'_iff_rstep_r_p_s')
      then show ?case using step(3)[OF sB] \<open>B' \<le> mctxt_of_term s'\<close> by (meson converse_rtrancl_into_rtrancl) 
    qed auto
  }
  from this[OF st(2)] this[OF su(2)] obtain c d where
    c: "(b, c) \<in> (rstep' \<R>)\<^sup>*" "c \<cdot> \<sigma> = mctxt_term_conv C" "c \<cdot> \<tau> = t \<cdot> (Var \<circ> Some)" and
    d: "(b, d) \<in> (rstep' \<R>)\<^sup>*" "d \<cdot> \<sigma> = mctxt_term_conv D" "d \<cdot> \<tau> = u \<cdot> (Var \<circ> Some)" by blast
  let ?p = "\<lambda>t . (t \<cdot> (\<tau> \<circ>\<^sub>s (Var \<circ> the)), term_mctxt_conv (t \<cdot> \<sigma>))"
  obtain e where "(c, e) \<in> (rstep' \<R>)\<^sup>*" "(d, e) \<in> (rstep' \<R>)\<^sup>*" using c(1) d(1) \<open>b \<in> short_terms\<close>
    by (metis CR_on_def joinE IH_rk' CR_on_iff_CR_Restr[of short_terms "rstep' \<R>", symmetric] short_terms_closed)
  then have "(?p c, ?p e) \<in> mirror_step\<^sup>*" "(?p d, ?p e) \<in> mirror_step\<^sup>*"
    by (metis rsteps_to_mirror_steps)+
  moreover have "C \<le> mctxt_of_term t" "D \<le> mctxt_of_term u"
    using mirror_steps_preserve_prefix[OF base_decomp_prefix, OF s(2)] st(2) su(2) by auto
  moreover have "C \<in> shallow_context" "D \<in> shallow_context" using st(2) su(2)
    shallow_context_closed'[OF \<open>B \<in> shallow_context\<close> mirror_steps_imp_rsteps'] by simp_all
  moreover have "(s, t) \<in> (rstep' \<R>)\<^sup>*" "(s, u) \<in> (rstep' \<R>)\<^sup>*"
    using st(2) su(2) by (auto simp: mirror_steps_imp_rsteps)
  then have "t \<in> native_terms" "u \<in> native_terms" "(s1, t) \<in> (rstep \<R>)\<^sup>*" "(s0, u) \<in> (rstep \<R>)\<^sup>*"
    using native_terms_rsteps[of s t] native_terms_rsteps[of s u] st(1) su(1) s(1)
    unfolding rstep_eq_rstep' by simp_all
  ultimately show ?thesis
    using arg_cong[OF c(3), of "\<lambda>t. t \<cdot> (Var \<circ> the)"] arg_cong[OF d(3), of "\<lambda>t. t \<cdot> (Var \<circ> the)"]
    unfolding c(2) d(2) subst_subst_compose[symmetric] subst_compose_def
    by (simp add: that[OF s st(2) su(2)])
qed

end (* weakly_layered_induct *)

locale weakly_layered_induct_dd = weakly_layered_induct \<F> \<LL> \<R> rk
  for \<F> :: "('f \<times> nat) set" and \<LL> :: "('f, 'v :: infinite) mctxt set" and \<R> :: "('f, 'v) trs" 
  and rk :: nat +
  fixes R :: "('f, 'v) term rel"
  assumes wf_R: "wf R" and trans_R: "trans R" and
    short_short_peak: "\<And>s t u. (s, t) \<in> short_step_s s0 \<Longrightarrow> (s, u) \<in> short_step_s s1 \<Longrightarrow>
      (t, u) \<in> ((\<Union>i\<in>under R s0. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>* O
       (short_step_s s1)\<^sup>= O
       ((\<Union>i\<in>under R s0 \<union> under R s1. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>* O
       ((short_step_s s0)\<inverse>)\<^sup>= O ((\<Union>i\<in>under R s1. short_step_s i)\<^sup>\<leftrightarrow>)\<^sup>*"
begin

inductive_set R' :: "(('f, 'v) term + nat) rel" where
  R'r: "x < y \<Longrightarrow> (Inr x, Inr y) \<in> R'"
| R's: "(Inl x, Inr y) \<in> R'"
| R'l: "(s, t) \<in> R \<Longrightarrow> (Inl s, Inl t) \<in> R'"

lemma R'_simps [simp]:
  "(Inr x, Inr y) \<in> R' \<longleftrightarrow> x < y"
  "(Inl s, Inr y) \<in> R'"
  "(Inr x, Inl t) \<notin> R'"
  "(Inl s, Inl t) \<in> R' \<longleftrightarrow> (s, t) \<in> R"
  by (auto intro: R'.intros elim: R'.cases)

lemma R'_cases:
  "(x, y) \<in> R' \<longleftrightarrow> (case (x, y) of
     (Inl s, Inl t) \<Rightarrow> (s, t) \<in> R
   | (Inr x, Inl t) \<Rightarrow> False
   | (Inl s, Inr y) \<Rightarrow> True
   | (Inr x, Inr y) \<Rightarrow> x < y)"
  by (cases x; cases y; simp)

primrec any_step :: "('f, 'v) term + nat \<Rightarrow> ('f, 'v) term rel" where
  "any_step (Inl s0) = short_step_s s0"
| "any_step (Inr \<iota>) = tall_step_i \<iota>"

lemma wf_R':
  "wf R'"
proof -
  have [simp]: "R' = inv_image
     ({(x, y). x < y} <*lex*> (map_prod Inl Inl ` R \<union> map_prod Inr Inr ` {(x, y). x < y}))
     (\<lambda>i. case i of Inl x \<Rightarrow> (0 :: nat, i) | Inr x \<Rightarrow> (1, i))"
    by (force split: sum.splits prod.splits simp: map_prod_def image_def)
  show ?thesis by (auto intro!: wf_less wf_Un wf_map_prod_image wf_R)
qed

lemma trans_R':
  "trans R'"
  by (auto simp: trans_def R'_cases split: sum.splits(2)) (metis trans_R trans_def)

lemma under_Inl:
  "(\<Union>i\<in>under R' (Inl s0). any_step i) = (\<Union>i\<in>under R s0. short_step_s i)"
  by (force simp: under_def elim: R'.cases intro: R'.intros)

lemma under_Inr:
  "(\<Union>i\<in>under R' (Inr \<iota>). any_step i) = (\<Union>i<\<iota>. tall_step_i i) \<union> short_step"
  by (force simp: under_def short_step_iff_short_step_s elim: R'.cases intro: R'.intros)

lemma CR_any_step: "CR (\<Union>i. any_step i)"
proof (intro dd_cr[OF wf_R' trans_R'], goal_cases peak)
  have [dest!]: "(x, y) \<in> short_step\<^sup>* \<Longrightarrow> (x, y) \<in> (short_step\<^sup>\<leftrightarrow>)\<^sup>*" for x y
    by (simp add: in_rtrancl_UnI)
  have [simp]: "(x, y) \<in> (R\<^sup>\<leftrightarrow>)\<^sup>* \<longleftrightarrow> (y, x) \<in> (R\<^sup>\<leftrightarrow>)\<^sup>*" for x y R
    by (metis rtrancl_converseI symcl_converse)
  note [intro] = subsetD[OF rtrancl_mono, of "short_step\<^sup>\<leftrightarrow>"] 
  have reflcl_refl: "(x, x) \<in> R\<^sup>=" for x R by simp
  case (peak a b s t u)
  show ?case
  proof ((cases a; cases b), goal_cases ll lr rl rr)
    case (rr \<iota> \<kappa>)
    from peak tall_tall_peak[of s t \<iota> u \<kappa>] obtain \<iota>' \<kappa>' t' u' v where
      *: "\<iota>' \<le> \<iota>" "\<kappa>' \<le> \<kappa>" "(t, t') \<in> tall_step_i \<kappa>'" "(t', v) \<in> short_step\<^sup>*"
      "(u, u') \<in> tall_step_i \<iota>'" "(u', v) \<in> short_step\<^sup>*"
      unfolding rr any_step.simps by metis
    then show ?case unfolding rr UN_Un under_Inr order.order_iff_strict
    apply (elim disjE)
    subgoal
      apply (intro relcompI[of _ t _, OF _ relcompI[of _ t, OF _ relcompI[of _ u, OF _ relcompI[of _ u]]]] rtrancl_refl reflcl_refl)
      apply (subst rtrancl_trans[of _ u', OF rtrancl_trans[of _ v, OF rtrancl_trans[of _ t']]])
      by auto
    subgoal
      apply (intro relcompI[of _ t _, OF _ relcompI[of _ t', OF _ relcompI[of _ u, OF _ relcompI[of _ u]]]] rtrancl_refl reflcl_refl)
      defer
      apply (subst rtrancl_trans[of _ u', OF rtrancl_trans[of _ v]])
      by auto
    subgoal
      apply (intro relcompI[of _ t _, OF _ relcompI[of _ t, OF _ relcompI[of _ u', OF _ relcompI[of _ u]]]] rtrancl_refl reflcl_refl)
      apply (subst rtrancl_trans[of _ u', OF rtrancl_trans[of _ v, OF rtrancl_trans[of _ t']]])
      by auto
    subgoal
      apply (intro relcompI[of _ t _, OF _ relcompI[of _ t', OF _ relcompI[of _ u', OF _ relcompI[of _ u]]]] rtrancl_refl reflcl_refl)
      defer
      apply (subst rtrancl_trans[of _ v])
      by auto
    done
  next
    case (rl \<iota> s1)
    from peak tall_short_peak[of s t \<iota> u] obtain \<iota>' \<iota>'' t' u' v where
      "\<iota>' \<le> \<iota>" "t = t' \<or> \<iota>'' < \<iota> \<and> (t, t') \<in> tall_step_i \<iota>''" "(t', v) \<in> short_step\<^sup>*"
      "(u, u') \<in> tall_step_i \<iota>'" "(u', v) \<in> short_step\<^sup>*"
      unfolding rl any_step.simps by (metis short_step_s_imp_short_step)
    then show ?case unfolding rl UN_Un under_Inr order.order_iff_strict
    apply (elim disjE[of "_ < _"])
    subgoal
      apply (intro relcompI[of _ t _, OF _ relcompI[of _ t, OF _ relcompI[of _ u, OF _ relcompI[of _ u]]]] rtrancl_refl reflcl_refl)
      apply (subst rtrancl_trans[of _ u', OF rtrancl_trans[of _ v, OF rtrancl_trans[of _ t']]])
      by auto
    subgoal
      apply (intro relcompI[of _ t _, OF _ relcompI[of _ t, OF _ relcompI[of _ u', OF _ relcompI[of _ u]]]] rtrancl_refl reflcl_refl)
      apply (subst rtrancl_trans[of _ u', OF rtrancl_trans[of _ v, OF rtrancl_trans[of _ t']]])
      by auto
    done
  next
    case (lr s0 \<kappa>)
    from peak tall_short_peak[of s u \<kappa> t] obtain \<kappa>' \<kappa>'' t' u' v where
      "\<kappa>' \<le> \<kappa>" "u = u' \<or> \<kappa>'' < \<kappa> \<and> (u, u') \<in> tall_step_i \<kappa>''" "(u', v) \<in> short_step\<^sup>*"
      "(t, t') \<in> tall_step_i \<kappa>'" "(t', v) \<in> short_step\<^sup>*"
      unfolding lr any_step.simps by (metis short_step_s_imp_short_step)
    then show ?case unfolding lr UN_Un under_Inr order.order_iff_strict
    apply (elim disjE[of "_ < _"])
    subgoal
      apply (intro relcompI[of _ t _, OF _ relcompI[of _ t, OF _ relcompI[of _ u, OF _ relcompI[of _ u]]]] rtrancl_refl reflcl_refl)
      apply (subst rtrancl_trans[of _ u', OF rtrancl_trans[of _ v, OF rtrancl_trans[of _ t']]])
      by auto
    subgoal
      apply (intro relcompI[of _ t _, OF _ relcompI[of _ t', OF _ relcompI[of _ u, OF _ relcompI[of _ u]]]] rtrancl_refl reflcl_refl)
      defer
      apply (subst rtrancl_trans[of _ u', OF rtrancl_trans[of _ v]])
      by auto
    done
  next
    case (ll s0 s1)
    from peak short_short_peak[of s t s0 u s1]
    show ?case by (simp only: ll UN_Un under_Inl any_step.simps)
  qed
qed

lemma tall_step_imp_rsteps:
  "(s, t) \<in> tall_step \<Longrightarrow> (s, t) \<in> (Restr (rstep' \<R>) native_terms)\<^sup>*"
  apply (elim tall_step.cases)
  apply (subst base_decomp_fill_holes(2)[symmetric])
  by (auto intro!: fill_holes_rsteps conjunct2[OF native_terms_rsteps] simp: base_decomp_fill_holes)

lemma short_step_imp_rsteps:
  "(s, t) \<in> short_step \<Longrightarrow> (s, t) \<in> (Restr (rstep' \<R>) native_terms)\<^sup>*"
  by (auto elim!: short_stepE intro!: conjunct2[OF native_terms_rsteps] dest: mirror_steps_imp_rsteps)

lemma any_step_short_tall:
  "(\<Union>i. any_step i) = short_step \<union> tall_step"
  by auto (metis short_step_iff_short_step_s tall_step_iff_tall_step_i any_step.simps sum.exhaust)+

lemma any_step_rsteps:
  "short_step \<union> tall_step \<subseteq> (Restr (rstep' \<R>) native_terms)\<^sup>*"
  by (auto dest: short_step_imp_rsteps tall_step_imp_rsteps)

lemma rstep_any_step:
  "Restr (rstep' \<R>) native_terms \<subseteq> short_step \<union> tall_step"
  using single_step_to_any_step by blast

lemma CR_Suc_rk:
  "CR_on (rstep' \<R>) native_terms"
  by (auto intro!: CR_between_imp_CR[OF _ rstep_any_step any_step_rsteps]
    CR_any_step[unfolded any_step_short_tall] iffD2[OF CR_on_iff_CR_Restr])

end

text \<open>{cite \<open>Lemma 4.27\<close> FMZvO15}\<close>

lemma (in weakly_layered) CR_main_lemma:
  assumes base: "CR_on (rstep' \<R>) {t. mctxt_of_term t \<in> \<LL>}"
  and step: "\<And>rk. CR_on (rstep' \<R>) {t \<in> \<T>. rank t \<le> Suc rk} \<Longrightarrow> weakly_layered_induct_dd \<F> \<LL> \<R> rk (R rk)"
  shows "CR_on (rstep' \<R>) \<T>"
proof -
  have "CR_on (rstep' \<R>) {t \<in> \<T>. rank t \<le> Suc rk}" for rk
  proof (induct rk)
    case 0
    have "t \<in> \<T> \<and> rank t \<le> Suc 0 \<longleftrightarrow> mctxt_of_term t \<in> \<LL>" for t
      using rank_1[of t] rank_gt_0[of t] \<LL>_sig by (fastforce simp: \<C>_def \<T>_def)
    then show ?case using base by simp
  next
    case (Suc rk)
    then interpret weakly_layered_induct_dd \<F> \<LL> \<R> rk "R rk" by (rule step)
    show ?case using CR_Suc_rk by (simp only: native_terms_def)
  qed
  then show ?thesis by (auto simp: CR_on_def) (metis less_Suc_eq less_Suc_eq_le less_Suc_eq_le) 
qed

end
