theory SPO_Impl
  imports
    SPO
    Term_Order_Impl
    Status_Impl
    First_Order_Rewriting.Term_Impl
    Auxx.Name
    Show.Shows_Literal
    Efficient_Weighted_Path_Order.WPO_Approx
begin

context
  fixes cS cNS cH :: "('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool" \<comment> \<open>sufficient criteria\<close>
begin

fun spo_ub :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "spo_ub (Var _) _ = False" |
    "spo_ub (Fun f ss) t = ((\<exists> si \<in> set ss. si = t \<or> spo_ub si t) \<or>
      (case t of
        Var _ \<Rightarrow> False
      | Fun g ts \<Rightarrow> (\<forall> tj \<in> set ts. spo_ub (Fun f ss) tj) \<and>
                     (cS (Fun f ss) t \<or>
                      (cNS (Fun f ss) t \<and> fst (lex_ext_unbounded (\<lambda> s' t'. (spo_ub s' t', s' = t')) ss ts)))))"

declare spo_ub.simps [simp del]

abbreviation "spo_orig n S NS \<equiv> spo.spo n S NS"

text \<open>soundness of approximation: @{const spo_ub} can be simulated by @{const spo_orig}
  if the arities are small.\<close>

lemma spo_ub:
  "(\<forall> si tj. s \<unrhd> si \<longrightarrow> t \<unrhd> tj \<longrightarrow>(cS si tj, cNS si tj) \<le>\<^sub>c\<^sub>b ((si, tj) \<in> S, (si, tj) \<in> NS)) \<longrightarrow>
   (\<forall> f us. (s \<unrhd> Fun f us \<or> t \<unrhd> Fun f us) \<longrightarrow> length us \<le> n ) \<longrightarrow>
   spo_ub s t \<longrightarrow> spo_orig n S NS s t"
proof (induct "(s, t)" arbitrary: s t rule: wf_induct[OF wf_measure[of "\<lambda> (s, t). size s + size t"]])
  case (1 s t)
  show ?case
  proof (intro impI)
    assume assms: "spo_ub s t"
      "\<forall> f us. (s \<unrhd> Fun f us \<or> t \<unrhd> Fun f us) \<longrightarrow> length us \<le> n"
      "\<forall> si tj. s \<unrhd> si \<longrightarrow> t \<unrhd> tj \<longrightarrow>(cS si tj, cNS si tj) \<le>\<^sub>c\<^sub>b ((si, tj) \<in> S, (si, tj) \<in> NS)"
    then have IH:
      "\<forall> s' t' . s \<unrhd> s' \<longrightarrow> t \<unrhd> t' \<longrightarrow> size s' + size t' < size s + size t \<longrightarrow> spo_ub s' t' \<longrightarrow> spo_orig n S NS s' t'"
    proof (intro allI impI)
      fix s' t'
      assume *: "s \<unrhd> s'" "t \<unrhd> t'" "spo_ub s' t'" "size s' + size t' < size s + size t"
      have "(\<forall> si tj. s' \<unrhd> si \<longrightarrow> t' \<unrhd> tj \<longrightarrow>(cS si tj, cNS si tj) \<le>\<^sub>c\<^sub>b ((si, tj) \<in> S, (si, tj) \<in> NS))"
        using * assms supteq_trans by meson
      moreover
      have "\<forall> f us. (s' \<unrhd> Fun f us \<or> t' \<unrhd> Fun f us) \<longrightarrow> length us \<le> n"
        using assms * supteq_trans by meson
      ultimately show "spo_orig n S NS s' t'" using 1 * by simp
    qed
    show "spo_orig n S NS s t"
    proof (cases s)
      case (Var )
      then have "\<not> spo_ub s t" by (simp add: spo_ub.simps)
      then show ?thesis using assms by blast
    next
      case (Fun f ss)
      note [simp] = this
      then show ?thesis
      proof (cases "\<exists> si \<in> set ss. si = t \<or> spo_ub si t")
        case True
        then obtain si where *: "si \<in> set ss" "si = t \<or> spo_ub si t" by auto
        from *(2) show ?thesis
        proof (rule disjE, goal_cases)
          case 1
          then have "\<exists> si \<in> set ss. si = t \<or> spo_orig n S NS si t" using * by blast
          then show ?case by (simp add: spo.spo.simps)
        next
          case 2
          have "s \<unrhd> si" using * by simp
          moreover
          have "size si + size t < size s + size t" using *
            by (metis Fun add_mono_thms_linordered_field(1) supt.arg supt_size)
          ultimately have "spo_orig n S NS si t" using IH 2 supteq.refl by blast
          then have "\<exists> si \<in> set ss. si = t \<or> spo_orig n S NS si t" using * by blast
          then show ?case by (simp add: spo.spo.simps)
        qed
      next
        case False
        then show ?thesis
        proof (cases t)
          case (Var)
          then have "\<exists> si \<in> set ss. si = t \<or> spo_ub si t"
            using spo_ub.simps assms by auto
          then show ?thesis using False by blast
        next
          case (Fun g ts)
          note [simp] = this
          have spo_ub_ts: "\<forall> tj \<in> set ts. spo_ub (Fun f ss) tj" 
            using assms False by (simp add: spo_ub.simps)
          have spo_orig_ts: "\<forall> tj \<in> set ts. spo_orig n S NS (Fun f ss) tj"
          proof (rule ballI)
            fix tj
            assume "tj \<in> set ts"
            then have "size s + size tj < size s + size t"
              using elem_size_size_list_size by fastforce
            moreover
            have "spo_ub (Fun f ss) tj" using \<open>tj \<in> set ts\<close> spo_ub_ts by blast
            moreover
            have "t \<unrhd> tj" using \<open>tj \<in> set ts\<close> by simp
            ultimately show "spo_orig n S NS (Fun f ss) tj" using IH by fastforce
          qed
          have "cS (Fun f ss) t \<or>
               (cNS (Fun f ss) t \<and> fst (lex_ext_unbounded (\<lambda> s' t'. (spo_ub s' t', s' = t')) ss ts))"
            using assms False by (simp add: spo_ub.simps)
          then show ?thesis
          proof (rule disjE, goal_cases)
            case 1
            then have "((Fun f ss), t) \<in> S" using assms(3) unfolding compare_bools_def by force
            then show ?case using spo_orig_ts by (simp add: spo.spo.simps)
          next
            case 2
            then have "((Fun f ss), t) \<in> NS" using assms(3) unfolding compare_bools_def by force
            moreover
            have "fst (lex_ext (\<lambda> s' t'. (spo_orig n S NS s' t', s' = t')) n ss ts)"
            proof (rule lex_ext_incr[unfolded order_pair_eq_def, of _ _ "spo_ub"])
              show "\<forall>s' \<in>set ss. \<forall>t' \<in> set ts. spo_ub s' t' \<longrightarrow> spo_orig n S NS s' t'"
              proof (intro ballI impI)
                fix s' t'
                assume *: "s' \<in> set ss" "t' \<in> set ts" "spo_ub s' t'"
                have "s \<unrhd> s'" using * by simp
                moreover
                have "t \<unrhd> t'" using * by simp
                moreover
                have "size s' + size t' < size s + size t" using *
                  by (metis Fun add_le_less_mono calculation(1) supt.arg supt_size supteq_size)
                ultimately show "spo_orig n S NS s' t'" using IH * by blast
              qed
              have "length ss \<le> n \<and> length ts \<le> n" using assms(2) by auto
              thus "fst (lex_ext (\<lambda>s' t'. (spo_ub s' t', s' = t')) n ss ts)"
                using lex_ext_to_lex_ext_unbounded 2 by fastforce
            qed
            ultimately show ?case using spo_orig_ts by (simp add: spo.spo.simps)
          qed
        qed
      qed
    qed
  qed
qed

definition mspo_ub :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where "mspo_ub s t \<equiv> (cH s t \<and> spo_ub s t)"

text \<open>soundness of approximation: @{const mspo_ub} can be simulated by @{const mspo.mspo}
  if the arities are small.\<close>

lemma mspo_ub:
  "(\<forall> si tj. s \<unrhd> si \<longrightarrow> t \<unrhd> tj \<longrightarrow>(cS si tj, cNS si tj) \<le>\<^sub>c\<^sub>b ((si, tj) \<in> S, (si, tj) \<in> NS)) \<Longrightarrow>
   (\<forall> si tj. s \<unrhd> si \<longrightarrow> t \<unrhd> tj \<longrightarrow> cH si tj  \<longrightarrow> (si, tj) \<in> H) \<Longrightarrow>
   (\<forall> f us. (s \<unrhd> Fun f us \<or> t \<unrhd> Fun f us) \<longrightarrow> length us \<le> n ) \<Longrightarrow>
   mspo_ub s t \<Longrightarrow> mspo.mspo n S NS H s t"
  unfolding mspo_ub_def mspo.mspo_def using spo_ub by auto

end

definition mspo_rel_impl :: "('f :: {compare_order, showl}, string) rel_impl \<Rightarrow> ('f, string) rel_impl"
  where
    "mspo_rel_impl rt = (
        \<comment> \<open>rt is the underlying order-pair of this (instance of) SPO\<close>
        let s' = (\<lambda> l r. isOK(rel_impl.s rt (l, r))); \<comment> \<open>extract strict part\<close>
            ns' = (\<lambda> l r. isOK(rel_impl.nst rt (l, r)));  \<comment> \<open>extract quasi part\<close>
            h' = (\<lambda> l r. isOK(rel_impl.ns rt (l, r))); \<comment> \<open>extract harmony part\<close>
            mspo_s = \<lambda> lr. check (mspo_ub s' ns' h' (fst lr) (snd lr)) (showsl_lit (STR ''cannot strictly orient '') o showsl lr);
            mspo_ns = \<lambda> (l,r). check (l = r \<or> mspo_ub s' ns' h' l r) (showsl_lit (STR ''cannot weakly orient '') o showsl (l,r))
          in \<lparr>
            rel_impl.valid = rel_impl_quasi_reduction_triple rt, \<comment> \<open>try to remove SN assumption\<close>            
                \<comment> \<open>declare the properties that MSPO can afford\<close>
                \<comment> \<open>comment TS: NS is just refl. closure of S, useful for co-rewrite?\<close>
            standard = succeed,
            desc = showsl_lit (STR ''MSPO over the following quasi-reduction triple:\<newline>'') o rel_impl.desc rt,
            s = mspo_s,
            ns = mspo_ns,
            nst = mspo_ns,
            af = full_af,
            top_af = full_af,
            SN = succeed,  \<comment> \<open>try to propagate, i.e., SN = rel_impl.SN rt\<close>
            subst_s = succeed,
            ce_compat = error (showsl_lit (STR ''ce is not supported by MSPO'')),
            co_rewr = error (showsl_lit (STR ''co rewrite is not supported by MSPO'')), \<comment> \<open>try to support\<close>
            top_mono = error (showsl_lit (STR ''top-mono is not supported by MSPO'')),
            top_refl = error (showsl_lit (STR ''top-refl is not supported by MSPO'')),
            mono_af = empty_af,
            mono = (\<lambda> _. succeed),
            not_wst = None,
            not_sst = None,
            cpx = no_complexity_check
          \<rparr>)"

lemma spo_on_subterms:
  assumes "spo.spo n S NS s t" and
   "(\<forall> u \<in> set (supteq_list s). \<forall> v \<in> set (supteq_list t). (u, v) \<in> S \<longrightarrow> (u, v) \<in> S')" and
   "(\<forall> u \<in> set (supteq_list s). \<forall> v \<in> set (supteq_list t). (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS')"
 shows "spo.spo n S' NS' s t"
 using assms spo_on_subterms by force

lemma mspo_on_subterms:
  assumes mspo: "mspo.mspo n S NS H s t" and
    SS': "\<forall> u \<in> set (supteq_list s). \<forall> v \<in> set (supteq_list t). (u, v) \<in> S \<longrightarrow> (u, v) \<in> S'" and
    NSNS': "\<forall> u \<in> set (supteq_list s). \<forall> v \<in> set (supteq_list t). (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS'" and
    HH': "\<forall> u \<in> set (supteq_list s). \<forall> v \<in> set (supteq_list t). (u, v) \<in> H \<longrightarrow> (u, v) \<in> H'"
  shows "mspo.mspo n S' NS' H' s t"
  using assms mspo_on_subterms by force

lemma mspo_rel_impl: assumes rt: "rel_impl rt"
  shows "rel_impl (mspo_rel_impl rt)"
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case *: (1 U)
  note * = *[unfolded mspo_rel_impl_def, simplified, unfolded Let_def, simplified]
  from * have quasi_red: "isOK(rel_impl_quasi_reduction_triple rt)"
    by (metis (no_types, lifting))
  then have rt_props: "isOK(rel_impl.valid rt) \<and> isOK(rel_impl.subst_s rt) \<and> isOK(rel_impl.SN rt) \<and> isOK(rel_impl.top_refl rt) \<and> isOK(rel_impl.top_mono rt)"
    unfolding rel_impl_quasi_reduction_triple_def by force
  define U_subterms where "U_subterms = [(u,v) . (s,t) <- U, u <- supteq_list s, v <- supteq_list t]"
  let ?s = "(\<lambda> st. isOK(rel_impl.s rt st))"
  let ?ns =  "(\<lambda> st. isOK(rel_impl.nst rt st))"
  let ?h = "(\<lambda> st. isOK(rel_impl.ns rt st))"
    (* uncurried versions *)
  let ?s' = "(\<lambda> s t. ?s (s, t))"
  let ?ns' =  "(\<lambda> s t. ?ns (s, t))"
  let ?h' =  "(\<lambda> s t. ?h (s, t))"
  let ?s_list = "filter (\<lambda> (s, t). ?s' s t) U_subterms"
  let ?ns_list =  "filter (\<lambda> (s, t). ?ns' s t) U_subterms"
  let ?h_list = "filter (\<lambda> (s, t). ?h' s t) U_subterms"
    (* Isabelle does not immediately see that these lists are made of subterms ... *)
  have U_subterms: "\<forall> s t. (s, t) \<in> set U \<longrightarrow>  (\<forall> s' \<unlhd> s. \<forall> t' \<unlhd> t. (s', t') \<in> set U_subterms)"
    unfolding U_subterms_def by force (* TODO: force works, but it's very time comsuming *)
  define n where "n = max_list [ n . (s,t) <- U, (_, n) <- funas_term_list s @ funas_term_list t ]"
  have n_maximum_arity:
    "\<forall> s t. (s, t) \<in> set U \<longrightarrow> (\<forall>f us. (s \<unrhd> Fun f us \<or> t \<unrhd> Fun f us) \<longrightarrow> length us \<le> n)"
    unfolding n_def 
    apply (intro allI impI, rule max_list) by force
  have orient: "isOK(rel_impl_s rt ?s_list)" "isOK(rel_impl_nst rt ?ns_list)" "isOK(rel_impl_ns rt ?h_list)"
    by (auto simp: rel_impl_list)
  obtain S NS H where
    rt: "trans H \<and> refl H \<and> subst.closed H \<and> ctxt.closed H \<and> \<comment> \<open>H is a rewrite preorder\<close>
             trans NS \<and> refl NS \<and> subst.closed NS \<and> \<comment> \<open>NS is a stable quasi-order\<close>
             trans S \<and> irrefl S \<and> subst.closed S \<and> SN S \<and> \<comment> \<open>S is a stable well-founded order\<close>
             NS O S \<subseteq> S \<and> S O NS \<subseteq> S \<and> \<comment> \<open>S and NS forms an order-pair\<close>
             top_mono H NS \<and> \<comment> \<open>top-mono/harmony property\<close>
             set ?s_list \<subseteq> S \<and> set ?ns_list \<subseteq> NS \<and> set ?h_list \<subseteq> H"
    using rel_impl_quasi_reduction_triple orient quasi_red rt
    by blast
  interpret mspo_with_basic_assms n S NS H
  proof (unfold_locales) (* TODO: proof should be trivial *)
    show "refl NS" using rt by blast
    show "trans S" using rt by blast
    show "trans NS" using rt by blast
    show "NS O S \<subseteq> S" using rt by blast
    show "S O NS \<subseteq> S" using rt by blast
    {
      fix s t \<sigma>
      assume "(s, t) \<in>  S"
      thus " (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S" using rt by auto
    }
    {
      fix s t \<sigma>
      assume "(s, t) \<in>  NS"
      thus " (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS" using rt by auto
    }
    show "irrefl S" using rt by blast
    show "refl H" using rt by blast
    show "trans H" using rt by blast
    {
      fix s t \<sigma>
      assume "(s, t) \<in>  H"
      thus " (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> H" using rt by auto
    }
    {
      fix s t f bef aft
      assume "(s, t) \<in>  H"
      thus "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> H" using rt
        by (meson ctxt_closed_one)
    }
    {
      fix s t f bef aft
      assume "(s, t) \<in>  H"
      thus "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS" using rt Term_Order.top_mono_def
        by (meson ctxt_closed_one)
    }
  qed
  let ?MSPO_REFL = "MSPO \<union> { (s, t) . s = t }"
  have trans_MSPO: "trans MSPO" unfolding trans_def using mspo_trans by blast
  have trans_MSPO': "MSPO O MSPO \<subseteq> MSPO" using mspo_trans by blast
  have trans_MSPO_REFL: "trans (MSPO \<union> {(s, t). s = t})"
    unfolding trans_def Un_iff using mspo_trans by blast
  have subst_closed_MSPO_REFL: "subst.closed (MSPO \<union> {(s, t). s = t})"
    using mspo_stable subst.closed_Un by fast
  have rt_mspo: "\<forall>l r. (l, r) \<in> set U \<longrightarrow>
          mspo_ub ?s' ?ns' ?h' l r \<longrightarrow>
          mspo_s l r"
  proof (intro allI impI, rule mspo_ub[of _ _ ?s' ?ns' S NS ?h' H n])
    fix l r
    assume lr_U: "(l, r) \<in> set U"
    thus "\<forall> l' r'. l \<unrhd> l' \<longrightarrow> r \<unrhd> r' \<longrightarrow> (?s' l' r', ?ns' l' r') \<le>\<^sub>c\<^sub>b ((l', r') \<in> S, (l', r') \<in> NS)"
      using rt lr_U unfolding compare_bools_def using U_subterms by force
    show "\<forall> l' r'. l \<unrhd> l' \<longrightarrow> r \<unrhd> r' \<longrightarrow> ?h' l' r' \<longrightarrow> (l', r') \<in> H"
      using rt lr_U U_subterms by force
    show "\<forall>f us. (l \<unrhd> Fun f us \<or> r \<unrhd> Fun f us) \<longrightarrow> length us \<le> n"
      using n_maximum_arity lr_U by blast
  qed auto
  show ?case
    apply (rule exI[of _ MSPO], intro exI[of _ ?MSPO_REFL])
    apply (simp add: rel_impl_list no_complexity_check_def full_af empty_af quasi_red rt_props
        mspo_rel_impl_def Let_def reflI trans_MSPO trans_MSPO' trans_MSPO_REFL
        subst_closed_MSPO_REFL)
  proof (intro conjI)
    show "irrefl MSPO" unfolding irrefl_def using mspo_irrefl by fast
    show "\<forall>s t. (s, t) \<in> set U \<longrightarrow>
          (mspo_ub ?s' ?ns' ?h' s t \<longrightarrow> mspo_s s t) \<and> (mspo_ub ?s' ?ns' ?h'  s t \<longrightarrow> mspo_s s t \<or> s = t)"
      using rt_mspo by blast
    show "ctxt.closed (MSPO \<union> {(s, t). s = t})"
      apply (rule Term_Order.af_monotone_full_af_imp_ctxt_closed)
      unfolding af_monotone_def using mspo_mono by simp
    show "subst.closed MSPO" using mspo_stable by auto
    show "SN MSPO" using MSPO_SN rt by blast
    show "(\<exists>sig. funas_trs (set U) \<subseteq> set sig) \<longrightarrow> ctxt.closed MSPO"
      apply (rule impI, rule Term_Order.af_monotone_full_af_imp_ctxt_closed)
      unfolding af_monotone_def using mspo_mono by simp
  qed auto
qed

end
