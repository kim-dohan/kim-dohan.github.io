theory GWPO_Impl
  imports
    Term_Order_Impl
    Status_Impl
    TRS.Sharp_Syntax
    First_Order_Rewriting.Trs_Impl
    Show.Shows_Literal
    Lexicographic_Extension_More
begin

text \<open>abstract construction of a quasi-reduction triple for a GWPO\<close>

locale gwpo_quasi_reduction_triple = sharp_syntax + 
  fixes S :: "('f, 'v) term rel"
    and NS :: "('f, 'v) term rel"
    and prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
  constrains shp:: "'f \<Rightarrow> 'f" 
begin

abbreviation lift_sharp :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel"
  where "lift_sharp rel \<equiv> { (l ,r) | l r. (\<sharp> l, \<sharp> r) \<in> rel}"

definition S_sharp :: "('f, 'v) term rel"
  where "S_sharp = lift_sharp S"

definition NS_sharp :: "('f, 'v) term rel"
  where "NS_sharp = lift_sharp NS"

definition PRC_S :: "('f, 'v) term rel"
  where "PRC_S = { (l, r) | l r. is_Fun l \<and> is_Fun r \<and> fst (prc (the (root l)) (the (root r))) }"

definition PRC_NS :: "('f, 'v) term rel" (* l = r seems strange... *)
  where "PRC_NS = { (l, r) | l r. l = r \<or> (is_Fun l \<and> is_Fun r \<and> snd (prc (the (root l)) (the (root r)))) }"

definition GWPO_S :: "('f, 'v) term rel"
  where "GWPO_S = { (l ,r) | l r. is_Fun l \<and> is_Fun r \<and> ((l, l), (r, r)) \<in> lex_two S_sharp NS_sharp PRC_S }"

definition GWPO_NS :: "('f, 'v) term rel"
  where "GWPO_NS = { (l ,r) | l r. l = r \<or> (is_Fun l \<and> is_Fun r \<and> ((l, l), (r, r)) \<in> lex_two S_sharp NS_sharp PRC_NS) }"

end

locale gwpo_quasi_reduction_triple_with_assms = gwpo_quasi_reduction_triple + order_pair + precedence +
  constrains S :: "('f, 'v) term rel"
    and NS :: _
    and shp:: "'f \<Rightarrow> 'f" 
    and prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
    and prl :: "'f \<times> nat \<Rightarrow> bool" (* useless, but comes automatically from the locale 'precedence' *)
  assumes subst_S: "(s,t) \<in> S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S"
    and subst_NS: "(s,t) \<in> NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS"
    and irrefl_S: "irrefl S"
    and S_imp_NS: "S \<subseteq> NS" (* automatically satisfied if S and NS are induced from the same algebra *)
    and mono_NS: "(s, t) \<in> NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS"
begin

lemma sharp_subst: assumes "is_Fun s" shows " (\<sharp> s) \<cdot> \<delta> = \<sharp> (s \<cdot> \<delta>)"
proof (cases s)
  case (Var x1)
  then show ?thesis using assms by blast
next
  case (Fun x21 x22)
  then show ?thesis by simp
qed

lemma S_sharp_trans: "trans S_sharp"
  apply (rule transI)
  using trans_S unfolding S_sharp_def trans_def by fast

lemma NS_sharp_trans: "trans NS_sharp"
  apply (rule transI)
  using trans_NS unfolding NS_sharp_def trans_def by fast

lemma NS_S_sharp_compat: "NS_sharp O S_sharp \<subseteq> S_sharp"
  using compat_NS_S_point unfolding NS_sharp_def S_sharp_def by fast

lemma S_NS_sharp_compat: "S_sharp O NS_sharp \<subseteq> S_sharp"
  using compat_S_NS_point unfolding NS_sharp_def S_sharp_def by fast

lemma S_sharp_SN: "SN S \<Longrightarrow> SN S_sharp"
  unfolding S_sharp_def by fastforce

lemma NS_sharp_refl: "refl NS_sharp"
  apply (rule reflI)
  using refl_NS_point unfolding NS_sharp_def by blast

lemma PRC_S_irrefl: "irrefl PRC_S"
  unfolding PRC_S_def
  by (simp add: irreflI prc_refl)

lemma PRC_S_trans: "trans PRC_S"
proof (rule transI)
  fix s t u
  assume "(s, t) \<in> PRC_S" "(t, u) \<in> PRC_S"
  then have
    *: "is_Fun s \<and> is_Fun t \<and>  is_Fun u \<and> 
        fst (prc (the (root s)) (the (root t)))  \<and> fst (prc (the (root t)) (the (root u)))"
    unfolding PRC_S_def by fast
  then have "snd (prc (the (root s)) (the (root t)))"
    using prc_stri_imp_nstri by blast
  with * prc_compat have " fst (prc (the (root s)) (the (root u)))"
    by (metis prod.collapse)
  with * show "(s, u) \<in> PRC_S" unfolding PRC_S_def by blast
qed

lemma PRC_S_stable: "subst.closed PRC_S"
  unfolding PRC_S_def apply (rule subst.closedI) by fastforce

lemma PRC_NS_refl: "refl PRC_NS"
  unfolding PRC_NS_def by (simp add: reflI)

lemma PRC_NS_trans: "trans PRC_NS"
proof (rule transI)
  fix s t u
  assume "(s, t) \<in> PRC_NS"
  then have
    a1: "s = t \<or> (is_Fun s \<and> is_Fun t \<and> snd (prc (the (root s)) (the (root t))))"
    unfolding PRC_NS_def by fast
  assume "(t, u) \<in> PRC_NS"
  then have
    a2: "t = u \<or> (is_Fun t \<and> is_Fun u \<and> snd (prc (the (root t)) (the (root u))))"
    unfolding PRC_NS_def by fast
  from a1 a2 show "(s, u) \<in> PRC_NS"
    unfolding PRC_NS_def
  proof (elim disjE, goal_cases)
    case 4
    then have "snd (prc (the (root s)) (the (root u)))" using prc_compat
      by (metis prod.collapse)
    then show ?case using 4 by blast
  qed auto
qed

lemma PRC_NS_stable: "subst.closed PRC_NS"
  unfolding PRC_NS_def apply (rule subst.closedI) by fastforce

lemma PRC_S_NS_compat: "PRC_NS O PRC_S O PRC_NS \<subseteq> PRC_S"
proof (rule subsetI)
  fix x
  assume "x \<in> PRC_NS O PRC_S O PRC_NS"
  then obtain s1 s2 s3 s4 where
    *: "x = (s1, s4)" "(s1, s2) \<in> PRC_NS" "(s2, s3) \<in> PRC_S" "(s3, s4) \<in> PRC_NS" by blast
  then have
    s12: "s1 = s2 \<or> (is_Fun s1 \<and> is_Fun s2 \<and> snd (prc (the (root s1)) (the (root s2))))"
    unfolding PRC_NS_def by force
  from * have s23: "is_Fun s2 \<and> is_Fun s3 \<and> fst (prc (the (root s2)) (the (root s3)))"
    unfolding PRC_S_def by force
  from * have s34: "s3 = s4 \<or> (is_Fun s3 \<and> is_Fun s4 \<and> snd (prc (the (root s3)) (the (root s4))))"
    unfolding PRC_NS_def by force
  with s12 have "(s1, s4) \<in> PRC_S"
  proof (elim disjE, goal_cases)
    case 1
    then show ?case using * by fast
  next
    case 2
    then have "is_Fun s1 \<and> is_Fun s3 \<and> fst (prc (the (root s1)) (the (root s3)))"
      using s23 by fast
    then have "is_Fun s1 \<and> is_Fun s4 \<and> fst (prc (the (root s1)) (the (root s4)))"
      using 2(2) prc_compat prod.collapse by metis
    then show ?case unfolding PRC_S_def by simp
  next
    case 3
    then have "is_Fun s2 \<and> is_Fun s4 \<and> fst (prc (the (root s2)) (the (root s4)))"
      using s23 by fast
    then have "is_Fun s1 \<and> is_Fun s4 \<and> fst (prc (the (root s1)) (the (root s4)))"
      using 3(1) prc_compat prod.collapse by metis
    then show ?case unfolding PRC_S_def by simp
  next
    case 4
    then have "is_Fun s1 \<and> is_Fun s3 \<and> fst (prc (the (root s1)) (the (root s3)))"
      using 4(1) s23 prc_compat prod.collapse by metis
    then have "is_Fun s1 \<and> is_Fun s4 \<and> fst (prc (the (root s1)) (the (root s4)))"
      using 4(2) prc_compat prod.collapse by metis
    then show ?case unfolding PRC_S_def by simp
  qed
  with \<open>x = (s1, s4)\<close> show "x \<in> PRC_S" by auto
qed

lemma PRC_S_SN: "SN PRC_S"
  using prc_SN unfolding PRC_S_def by fast

text \<open>the triple (NS, GWPO_NS, GWPO_S) is a quasi-reduction triple\<close>

lemma GWPO_S_irrefl: "irrefl GWPO_S"
  using PRC_S_irrefl irrefl_S unfolding irrefl_def GWPO_S_def S_sharp_def by simp

lemma GWPO_S_trans: "trans GWPO_S"
proof (rule transI)
  fix s t u
  assume assms: "(s, t) \<in> GWPO_S" "(t, u) \<in> GWPO_S"
  then have st: "(s, t) \<in> S_sharp \<or> (s, t) \<in> NS_sharp \<and> (s, t) \<in> PRC_S"
    unfolding GWPO_S_def by auto
  have tu: "(t, u) \<in> S_sharp \<or> (t, u) \<in> NS_sharp \<and> (t, u) \<in> PRC_S"
    using \<open>(t, u) \<in> GWPO_S\<close> unfolding GWPO_S_def by auto
  with st show "(s, u) \<in> GWPO_S"
  proof (elim disjE, goal_cases)
    case 1
    then have "(s, u) \<in> S_sharp" using S_sharp_trans unfolding trans_def by blast
    then show ?case using assms unfolding GWPO_S_def by fastforce
  next
    case 2
    then have "(s, u) \<in> S_sharp" using S_NS_sharp_compat unfolding trans_def by auto
    then show ?case using assms unfolding GWPO_S_def by fastforce
  next
    case 3
    then have "(s, u) \<in> S_sharp" using NS_S_sharp_compat unfolding trans_def by auto
    then show ?case using assms unfolding GWPO_S_def by fastforce
  next
    case 4
    then have "(s, u) \<in> NS_sharp" using NS_sharp_trans unfolding trans_def by blast
    moreover
    from 4 have "(s, u) \<in> PRC_S" using PRC_S_trans unfolding trans_def by blast
    ultimately show ?case using assms unfolding GWPO_S_def by simp
  qed
qed

lemma GWPO_S_stable: "subst.closed GWPO_S"
proof (rule subst.closedI)
  fix s t \<delta>
  assume assms: "(s, t) \<in> GWPO_S"
  then have "(s, t) \<in> S_sharp \<or> ((s, t) \<in> NS_sharp \<and> (s, t) \<in> PRC_S)"
    unfolding GWPO_S_def by simp
  thus "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> GWPO_S"
  proof (elim disjE, goal_cases)
    case 1
    then have "(\<sharp> s, \<sharp> t) \<in> S" unfolding S_sharp_def by blast
    then have "((\<sharp> s) \<cdot> \<delta>, (\<sharp> t)\<cdot> \<delta>) \<in> S" using subst_S by blast
    then have "(\<sharp> (s \<cdot> \<delta>), \<sharp> (t \<cdot> \<delta>)) \<in> S" 
      using assms sharp_subst unfolding GWPO_S_def by fastforce
    then have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> S_sharp" unfolding S_sharp_def by blast
    moreover
    have "is_Fun (s \<cdot> \<delta>) \<and> is_Fun (t \<cdot> \<delta>)" using assms unfolding GWPO_S_def by auto
    ultimately show ?case using assms unfolding GWPO_S_def by auto
  next
    case 2
    have "is_Fun (s \<cdot> \<delta>) \<and> is_Fun (t \<cdot> \<delta>)" using assms unfolding GWPO_S_def by auto
    moreover
    have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> PRC_S" using assms 2 PRC_S_stable by blast
    moreover
    from 2 have "(\<sharp> s, \<sharp> t) \<in> NS" unfolding NS_sharp_def by blast
    then have "((\<sharp> s) \<cdot> \<delta>, (\<sharp> t)\<cdot> \<delta>) \<in> NS" using subst_NS by blast
    then have "(\<sharp> (s \<cdot> \<delta>), \<sharp> (t \<cdot> \<delta>)) \<in> NS" 
      using assms sharp_subst unfolding GWPO_S_def by fastforce
    then have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> NS_sharp" unfolding NS_sharp_def by blast
    ultimately show ?case using assms unfolding GWPO_S_def by auto
  qed
qed

lemma GWPO_NS_refl: "refl GWPO_NS"
  apply (rule reflI)
  unfolding GWPO_NS_def by simp

lemma GWPO_NS_trans: "trans GWPO_NS"
proof (rule transI)
  fix s t u
  assume assms: "(s, t) \<in> GWPO_NS" "(t, u) \<in> GWPO_NS"
  then have st: "s = t \<or> (s, t) \<in> S_sharp \<or> (s, t) \<in> NS_sharp \<and> (s, t) \<in> PRC_NS"
    unfolding GWPO_NS_def by auto
  have tu: "t = u \<or> (t, u) \<in> S_sharp \<or> (t, u) \<in> NS_sharp \<and> (t, u) \<in> PRC_NS"
    using \<open>(t, u) \<in> GWPO_NS\<close> unfolding GWPO_NS_def by auto
  with st show "(s, u) \<in> GWPO_NS"
  proof (elim disjE, goal_cases)
    case 1
    then show ?case using GWPO_NS_refl reflD by meson 
  next
    case 2
    then have "(s, u) \<in> S_sharp" by blast
    then show ?case using assms unfolding GWPO_NS_def by auto 
  next
    case 3
    then have "(s, u) \<in> NS_sharp \<and> (s, u) \<in> PRC_NS" by blast
    then show ?case using assms unfolding GWPO_NS_def by auto 
  next
    case 4
    then have "(s, u) \<in> S_sharp" by blast
    then show ?case using assms unfolding GWPO_NS_def by auto
  next
    case 5
    then have "(s, u) \<in> NS_sharp \<and> (s, u) \<in> PRC_NS" by blast
    then show ?case using assms unfolding GWPO_NS_def by auto 
  next
    case 6
    then have "(s, u) \<in> S_sharp" using S_sharp_trans unfolding trans_def by blast
    then show ?case using assms unfolding GWPO_NS_def by auto
  next
    case 7
    then have "(s, u) \<in> S_sharp" using S_NS_sharp_compat unfolding trans_def by auto
    then show ?case using assms unfolding GWPO_NS_def by auto
  next
    case 8
    then have "(s, u) \<in> S_sharp" using NS_S_sharp_compat unfolding trans_def by auto
    then show ?case using assms unfolding GWPO_NS_def by auto
  next
    case 9
    then have "(s, u) \<in> NS_sharp" using NS_sharp_trans unfolding trans_def by blast
    moreover
    from 9 have "(s, u) \<in> PRC_NS" using PRC_NS_trans unfolding trans_def by blast
    ultimately show ?case using assms unfolding GWPO_NS_def by auto
  qed
qed

lemma GWPO_NS_stable: "subst.closed GWPO_NS"
proof (rule subst.closedI)
  fix s t \<delta>
  assume assms: "(s, t) \<in> GWPO_NS"
  show "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> GWPO_NS"
  proof (cases "s = t")
    case True
    then show ?thesis using GWPO_NS_refl reflD by fast
  next
    case False
    with assms have "(s, t) \<in> S_sharp \<or> ((s, t) \<in> NS_sharp \<and> (s, t) \<in> PRC_NS)"
      unfolding GWPO_NS_def by auto
    then show ?thesis 
    proof (elim disjE, goal_cases)
      case 1
      then have "(\<sharp> s, \<sharp> t) \<in> S" unfolding S_sharp_def by blast
      then have "((\<sharp> s) \<cdot> \<delta>, (\<sharp> t)\<cdot> \<delta>) \<in> S" using subst_S by blast
      then have "(\<sharp> (s \<cdot> \<delta>), \<sharp> (t \<cdot> \<delta>)) \<in> S" 
        using False assms sharp_subst unfolding GWPO_NS_def by fastforce
      then have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> S_sharp" unfolding S_sharp_def by blast
      moreover
      have "is_Fun (s \<cdot> \<delta>) \<and> is_Fun (t \<cdot> \<delta>)" using False assms unfolding GWPO_NS_def by fastforce
      ultimately show ?case using assms unfolding GWPO_NS_def by auto
    next
      case 2
      have "is_Fun (s \<cdot> \<delta>) \<and> is_Fun (t \<cdot> \<delta>)" using assms False unfolding GWPO_NS_def by auto
      moreover
      have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> PRC_NS" using assms 2 PRC_NS_stable by blast
      moreover
      from 2 have "(\<sharp> s, \<sharp> t) \<in> NS" unfolding NS_sharp_def by blast
      then have "((\<sharp> s) \<cdot> \<delta>, (\<sharp> t)\<cdot> \<delta>) \<in> NS" using subst_NS by blast
      then have "(\<sharp> (s \<cdot> \<delta>), \<sharp> (t \<cdot> \<delta>)) \<in> NS" 
        using assms sharp_subst False unfolding GWPO_NS_def by fastforce
      then have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> NS_sharp" unfolding NS_sharp_def by blast
      ultimately show ?case using assms unfolding GWPO_NS_def by auto
    qed
  qed
qed

lemma GWPO_S_NS_compat: "GWPO_S O GWPO_NS \<subseteq> GWPO_S"
proof (rule subsetI)
  fix x
  assume "x \<in> GWPO_S O GWPO_NS"
  then obtain s t u where *: "x = (s, u)" "(s, t) \<in> GWPO_S" "(t, u) \<in> GWPO_NS" by blast
  have "(s, u) \<in> GWPO_S"
  proof (cases "t = u")
    case True
    then show ?thesis using * by presburger
  next
    case False
    from * have st: "(s, t) \<in> S_sharp \<or> ((s, t) \<in> NS_sharp \<and> (s, t) \<in> PRC_S)"
      unfolding GWPO_S_def by simp
    from * False have "(t, u) \<in> S_sharp \<or> ((t, u) \<in> NS_sharp \<and> (t, u) \<in> PRC_NS)"
      unfolding GWPO_NS_def by auto
    with st show ?thesis
    proof (elim disjE, goal_cases)
      case 1
      then have "(s, u) \<in> S_sharp" using S_sharp_trans unfolding trans_def by blast
      then show ?case using * False unfolding GWPO_S_def GWPO_NS_def by fastforce
    next
      case 2
      then have "(s, u) \<in> S_sharp" using S_NS_sharp_compat by blast
      then show ?case using * False unfolding GWPO_S_def GWPO_NS_def by fastforce
    next
      case 3
      then have "(s, u) \<in> S_sharp" using NS_S_sharp_compat by blast
      then show ?case using * False unfolding GWPO_S_def GWPO_NS_def by fastforce
    next
      case 4
      then have "(s, u) \<in> NS_sharp" using NS_sharp_trans unfolding trans_def by blast
      moreover
      from 4 have "(s, u) \<in> PRC_S" using PRC_S_NS_compat PRC_NS_refl reflD unfolding relcomp_def by fast  
      ultimately show ?case using * False unfolding GWPO_S_def GWPO_NS_def by auto
    qed
  qed
  thus "x \<in> GWPO_S" using * by fast
qed

lemma GWPO_NS_S_compat: "GWPO_NS O GWPO_S \<subseteq> GWPO_S"
proof (rule subsetI)
  fix x
  assume "x \<in> GWPO_NS O GWPO_S"
  then obtain s t u where *: "x = (s, u)" "(s, t) \<in> GWPO_NS" "(t, u) \<in> GWPO_S" by blast
  have "(s, u) \<in> GWPO_S"
  proof (cases "s = t")
    case True
    then show ?thesis using * by blast 
  next
    case False
    with * have st: "(s, t) \<in> S_sharp \<or> ((s, t) \<in> NS_sharp \<and> (s, t) \<in> PRC_NS)"
      unfolding GWPO_NS_def by simp
    from * have "(t, u) \<in> S_sharp \<or> ((t, u) \<in> NS_sharp \<and> (t, u) \<in> PRC_S)"
      unfolding GWPO_S_def by auto
    with st show ?thesis
    proof (elim disjE, goal_cases)
      case 1
      then have "(s, u) \<in> S_sharp" using S_sharp_trans unfolding trans_def by blast
      then show ?case using * False unfolding GWPO_S_def GWPO_NS_def by fastforce
    next
      case 2
      then have "(s, u) \<in> S_sharp" using S_NS_sharp_compat by blast
      then show ?case using * False unfolding GWPO_S_def GWPO_NS_def by fastforce
    next
      case 3
      then have "(s, u) \<in> S_sharp" using NS_S_sharp_compat by blast
      then show ?case using * False unfolding GWPO_S_def GWPO_NS_def by fastforce
    next
      case 4
      then have "(s, u) \<in> NS_sharp" using NS_sharp_trans unfolding trans_def by blast
      moreover
      from 4 have "(s, u) \<in> PRC_S" using PRC_S_NS_compat PRC_NS_refl reflD unfolding relcomp_def by fast  
      ultimately show ?case using * False unfolding GWPO_S_def GWPO_NS_def by auto
    qed
  qed
  thus "x \<in> GWPO_S" using * by fast
qed

lemma NS_GWPO_NS_top_mono:
  "top_mono NS GWPO_NS"
  unfolding Term_Order.top_mono_def
proof (intro impI allI)
  fix s t f bef aft
  assume *: " (s, t) \<in> NS"
  let ?cs = "Fun f (bef @ s # aft)"
  let ?ct = "Fun f (bef @ t # aft)"
  have "(?cs, ?ct) \<in> NS_sharp" using * mono_NS unfolding NS_sharp_def by simp
  moreover
  have "(?cs, ?ct) \<in> PRC_NS" using prc_refl unfolding PRC_NS_def by simp  
  ultimately show "(?cs, ?ct) \<in> GWPO_NS" unfolding GWPO_NS_def by auto
qed

lemma GWPO_S_SN: assumes "SN S" shows "SN GWPO_S"
proof -
  have "SN (lex_two S_sharp NS_sharp PRC_S)"
    by (rule lex_two[OF NS_S_sharp_compat S_sharp_SN[OF assms] PRC_S_SN])
  thus ?thesis unfolding GWPO_S_def by fast
qed

end

text \<open>soundness of approximation: \<close>

context
  fixes cS cNS :: "('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool" \<comment> \<open>sufficient criteria\<close>
    and prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
    and shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

fun gwpo_s :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "gwpo_s l r = (is_Fun l \<and> is_Fun r \<and>
                    (cS (\<sharp> l) (\<sharp> r) \<or>
                    (cNS (\<sharp> l) (\<sharp> r) \<and> fst (prc (the (root l)) (the (root r))))))"

fun gwpo_ns :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "gwpo_ns l r = (l = r \<or> (is_Fun l \<and> is_Fun r \<and>
                              (cS (\<sharp> l) (\<sharp> r) \<or>
                              (cNS (\<sharp> l) (\<sharp> r) \<and> snd (prc (the (root l)) (the (root r)))))))"

abbreviation "GWPO_S_orig S NS \<equiv> gwpo_quasi_reduction_triple.GWPO_S shp S NS prc"
abbreviation "GWPO_NS_orig S NS \<equiv> gwpo_quasi_reduction_triple.GWPO_NS shp S NS prc"

lemma gwpo_s:
  assumes "cS (\<sharp> s) (\<sharp> t) \<longrightarrow> (\<sharp> s, \<sharp> t) \<in> S" and (* NOTE: cS s t \<longrightarrow> (s, t) \<in> S is not enough, according to nitpick *)
          "cNS (\<sharp> s) (\<sharp> t) \<longrightarrow> (\<sharp> s, \<sharp> t) \<in> NS" and
          "gwpo_s s t"
  shows "(s, t) \<in> GWPO_S_orig S NS"
proof -
  from assms(3) have "is_Fun s \<and> is_Fun t" by simp
  note [simp] = this
  from assms(3) have "cS (\<sharp> s) (\<sharp> t) \<or> (cNS (\<sharp> s) (\<sharp> t) \<and> fst (prc (the (root s)) (the (root t))))"
    by simp
  thus ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then have "(\<sharp> s, \<sharp> t) \<in> S" using assms(1) by simp
    then show ?case
      unfolding gwpo_quasi_reduction_triple.GWPO_S_def gwpo_quasi_reduction_triple.S_sharp_def
      using assms(1) by simp
  next
    case 2
    then have "(\<sharp> s, \<sharp> t) \<in> NS \<and> fst (prc (the (root s)) (the (root t)))"
      using assms(2) by blast
    then show ?case
      unfolding gwpo_quasi_reduction_triple.GWPO_S_def gwpo_quasi_reduction_triple.NS_sharp_def 
                gwpo_quasi_reduction_triple.PRC_S_def
      using assms(2) by simp
  qed
qed

lemma gwpo_ns:
  assumes "cS (\<sharp> s) (\<sharp> t) \<longrightarrow> (\<sharp> s, \<sharp> t) \<in> S" and (* NOTE: cS s t \<longrightarrow> (s, t) \<in> S is not enough, according to nitpick *)
          "cNS (\<sharp> s) (\<sharp> t) \<longrightarrow> (\<sharp> s, \<sharp> t) \<in> NS" and
          "gwpo_ns s t"
  shows "(s, t) \<in> GWPO_NS_orig S NS"
proof (cases "s = t")
  case True
  then show ?thesis unfolding  gwpo_quasi_reduction_triple.GWPO_NS_def using assms(3) by simp
next
  case False
  with assms(3) have "is_Fun s \<and> is_Fun t" by simp
  note [simp] = this
  with False assms(3) have "cS (\<sharp> s) (\<sharp> t) \<or> (cNS (\<sharp> s) (\<sharp> t) \<and> snd (prc (the (root s)) (the (root t))))"
    by simp
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then have "(\<sharp> s, \<sharp> t) \<in> S" using assms(1) by simp
    then show ?case
      unfolding gwpo_quasi_reduction_triple.GWPO_NS_def gwpo_quasi_reduction_triple.S_sharp_def
      using assms(1) by simp
  next
    case 2
    then have "(\<sharp> s, \<sharp> t) \<in> NS \<and> snd (prc (the (root s)) (the (root t)))"
      using assms(2) by simp
    then show ?case
      unfolding gwpo_quasi_reduction_triple.GWPO_NS_def gwpo_quasi_reduction_triple.NS_sharp_def 
                gwpo_quasi_reduction_triple.PRC_NS_def
      using assms(2) by simp
  qed
qed

end

text \<open>concrete construction of a quasi-reduction triple for a GWPO\<close>

text \<open>the first item is precedence, and the second is the sharp function \<sharp>\<close>

type_synonym 'f gwpo_params = "(('f \<times> nat) \<times> nat) list \<times> ('f \<Rightarrow> 'f)" (* f' x nat -- pair of function symbol and arity *)

definition "prc pr_list \<equiv> prc_nat (fun_of_map (ceta_map_of pr_list) 0)"
definition "prl pr_list \<equiv> prl_nat (fun_of_map (ceta_map_of pr_list) 0)"

definition showsl_gwpo_params :: "('f :: showl) gwpo_params \<Rightarrow> showsl" where
  "showsl_gwpo_params params = showsl_lit (STR ''precedence:\<newline>'') \<circ>
    showsl_sep (\<lambda>(f, p).
      showsl_lit (STR ''precedence('') \<circ> showsl_funa f \<circ> showsl_lit (STR '') = '') \<circ> showsl p \<circ> showsl_nl
    ) showsl_nl (fst params)"

definition gwpo_rel_impl :: "('f :: {compare_order, showl}, string) rel_impl \<Rightarrow> 'f gwpo_params \<Rightarrow> ('f, string) rel_impl"
  where
    "gwpo_rel_impl rt params = (case params of (pr_list, shp) \<Rightarrow>
        let s' = (\<lambda> l r. isOK(rel_impl.s rt (l, r))); \<comment> \<open>underlying orders\<close>
            ns' = (\<lambda> l r. isOK(rel_impl.ns rt (l, r)))
          in \<lparr>
            \<comment> \<open>from the standard flag S \<subseteq> NS is required, but this is automatically satisfied
                if rel_impl.s and rel_impl.ns are induced by the same algebra.\<close>
            rel_impl.valid = rel_impl_redpair rt,
            \<comment> \<open>returns a quasi-reduction triple\<close>
            standard = error (showsl_lit (STR ''standard is not supported by GWPO'')),
            desc = showsl_lit (STR ''quasi-reduction triple for GWPO with '') o
                   showsl_gwpo_params params o
                   showsl_lit (STR ''\<newline>over the following reduction pair:\<newline>'') o
                   rel_impl.desc rt,
            s = (\<lambda> (l, r). check (gwpo_s s' ns' (prc pr_list) shp l r) (showsl_lit (STR ''cannot strictly orient '') o showsl (l, r))),
            ns =  (\<lambda> (l, r). check (ns' l r) (showsl_lit (STR ''cannot weakly orient (nst)'') o showsl (l, r))),
            nst = (\<lambda> (l, r). check (gwpo_ns s' ns' (prc pr_list) shp l r) (showsl_lit (STR ''cannot weakly orient (ns)'') o showsl (l, r))),
            af = full_af,
            top_af = full_af,
            SN = succeed,
            subst_s = succeed,
            ce_compat = error (showsl_lit (STR ''ce is not supported by GWPO'')),
            co_rewr = error (showsl_lit (STR ''co rewrite is not supported by GWPO'')),
            top_mono = succeed,
            top_refl = succeed,
            mono_af = empty_af,
            mono = (\<lambda> _. error (showsl_lit (STR ''mono is not supported by GWPO''))),
            not_wst = None,
            not_sst = None,
            cpx = no_complexity_check
          \<rparr>)"

text \<open>a copy of @{thm rel_impl_redpair} because I could not make it work...\<close>
lemma rel_impl_redpair: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_redpair ri)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)"  
shows "\<exists> S NS. set s \<subseteq> S \<and> set ns \<subseteq> NS 
     \<and> S \<subseteq> NS \<and> S O NS \<subseteq> S \<and> NS O S \<subseteq> S
     \<and> ctxt.closed NS  \<and> trans NS \<and> refl NS \<and> subst.closed NS
     \<and> trans S \<and> irrefl S \<and> subst.closed S \<and> SN S"
proof - 
  from checks[unfolded rel_impl_redpair_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and std: "isOK(rel_impl.standard ri)" 
    and sn: "isOK (rel_impl.SN ri)" 
    and subst: "isOK (rel_impl.subst_s ri)" 
    by auto
  let ?U = "s @ ns" 
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient subst sn std
  have "set s \<subseteq> S" "set ns \<subseteq> NS" 
     "S \<subseteq> NS" "S O NS \<subseteq> S" "NS O S \<subseteq> S"
     "ctxt.closed NS" 
     "trans NS" 
     "refl NS" 
     "subst.closed NS" "subst.closed S"
     "SN S" "trans S" "irrefl S"
    by (auto simp: rel_impl_list)
  thus ?thesis by blast
qed

lemma gwpo_rel_impl: assumes rt: "rel_impl rt"
  shows "rel_impl (gwpo_rel_impl rt params)"
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case *: (1 U)
  note * = *[unfolded gwpo_rel_impl_def, simplified, unfolded Let_def, simplified]
  show ?case
  proof (cases params)
    case (Pair prc_list shp) (* TODO: sharp_syntax does not work ? *)
    from * have redpair: "isOK(rel_impl_redpair rt)"
      by (simp add: split_beta)
    then have rt_props: "isOK(rel_impl.valid rt) \<and> isOK(rel_impl.standard rt) \<and> isOK(rel_impl.subst_s rt) \<and> isOK(rel_impl.SN rt)"
      unfolding rel_impl_redpair_def by auto
    let ?s = "(\<lambda> st. isOK(rel_impl.s rt st))"
    let ?ns = "(\<lambda> st. isOK(rel_impl.ns rt st))"
    let ?s_list = "[ (s, t) . (s, t) <- U, ?s (s, t) ] @
                   [ (sharp_term shp s, sharp_term shp t) . (s, t) <- U, ?s (sharp_term shp s, sharp_term shp t) ]"
    let ?ns_list = "[ (s, t) . (s, t) <- U, ?ns (s, t) ] @
                    [ (sharp_term shp s, sharp_term shp t) . (s, t) <- U, ?ns (sharp_term shp s, sharp_term shp t) ]"
    have orient: "isOK(rel_impl_s rt ?s_list)" "isOK(rel_impl_ns rt ?ns_list)"
      by (auto simp: rel_impl_list)
    obtain S NS where
      rt: "set ?s_list \<subseteq> S \<and> set ?ns_list \<subseteq> NS \<and> S \<subseteq> NS \<and> ctxt.closed NS  \<and> trans NS  \<and>
           refl NS \<and> subst.closed NS \<and> trans S \<and> irrefl S \<and> subst.closed S \<and>
           S O NS \<subseteq> S \<and> NS O S \<subseteq> S \<and> SN S"
      using rel_impl_redpair[of rt ?s_list ?ns_list, OF rt redpair orient] by meson
    let ?prl = "\<lambda> _ . True"
    interpret precedence "prc prc_list" "prl prc_list"
      unfolding prc_def prl_def using precedence_nat.precedence_axioms .
    interpret gwpo_quasi_reduction_triple_with_assms shp S NS "prc prc_list" "prl prc_list"
    proof (unfold_locales)
      show "refl NS" using rt by blast
      show "trans S" using rt by blast
      show "trans NS" using rt by blast
      show "NS O S \<subseteq> S" using rt by blast
      show "S O NS \<subseteq> S" using rt by blast
      show "\<And>s t \<sigma>. (s, t) \<in> S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S" using rt by blast
      show "\<And>s t \<sigma>. (s, t) \<in> NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS" using rt by blast
      show "irrefl S" using rt by blast
      show "S \<subseteq> NS" using rt by blast
      show "\<And>s t f bef aft. (s, t) \<in> NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS"
        using rt ctxt_closed_one by meson
    qed
    have S_approx: "\<forall> s t. (s, t) \<in> set U \<longrightarrow> isOK (rel_impl.s rt (sharp_term shp s, sharp_term shp t)) \<longrightarrow>
                           (sharp_term shp s, sharp_term shp t) \<in> S"
    proof -
      have "\<forall> s t. (s, t) \<in> set U \<longrightarrow> isOK (rel_impl.s rt (sharp_term shp s, sharp_term shp t)) \<longrightarrow>
                   (sharp_term shp s, sharp_term shp t) \<in> set ?s_list"
        by auto
      moreover
      from rt have  "\<forall> s t. (s, t) \<in> set ?s_list \<longrightarrow> (s, t) \<in> S" by blast
      ultimately show ?thesis by blast
    qed
    have NS_approx: "\<forall> s t. (s, t) \<in> set U \<longrightarrow> isOK (rel_impl.ns rt (sharp_term shp s, sharp_term shp t)) \<longrightarrow>
                            (sharp_term shp s, sharp_term shp t) \<in> NS"
    proof -
      have "\<forall> s t. (s, t) \<in> set U \<longrightarrow> isOK (rel_impl.ns rt (sharp_term shp s, sharp_term shp t)) \<longrightarrow>
                   (sharp_term shp s, sharp_term shp t) \<in> set ?ns_list"
        by auto
      moreover
      from rt have  "\<forall> s t. (s, t) \<in> set ?ns_list \<longrightarrow> (s, t) \<in> NS" by blast
      ultimately show ?thesis by blast
    qed
    from rt have SN: "SN S" by auto
    show ?thesis
      apply (rule exI[of _ GWPO_S], rule exI[of _  NS],rule exI[of _ GWPO_NS])
      apply (simp add: rel_impl_list no_complexity_check_def full_af empty_af rt_props Let_def reflI
                       gwpo_rel_impl_def rel_impl_redpair_def redpair Pair
                       GWPO_S_irrefl GWPO_S_trans GWPO_S_stable GWPO_S_SN[OF SN]
                       refl_NS trans_NS GWPO_NS_stable GWPO_NS_trans GWPO_NS_refl
                       GWPO_S_NS_compat GWPO_NS_S_compat NS_GWPO_NS_top_mono)
    proof (intro conjI, goal_cases)
      case 1 (* soundness of finite approximation *)
      show ?case 
        using gwpo_s[of "\<lambda> s t. ?s (s, t)" shp _ _ S "\<lambda> s t. ?ns (s, t)" NS  "prc prc_list"] S_approx NS_approx
              gwpo_ns[of "\<lambda> s t. ?s (s, t)" shp _ _ S "\<lambda> s t. ?ns (s, t)" NS  "prc prc_list"] rt
        by auto
    next
      case 2
      then show ?case
        apply (rule af_monotone_full_af_imp_ctxt_closed)
        unfolding af_monotone_def full_af_def using mono_NS by simp
    next
      case 3
      then show ?case
        apply (rule subst.closedI) using subst_NS by simp
    qed
  qed
qed

end
