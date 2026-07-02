theory KBO_More
  imports Knuth_Bendix_Order.KBO
    Term_Order
    Simple_Termination
    Lexicographic_Extension_More
    TRS.More_Abstract_Rewriting
    Auxx.Multiset2
begin

text \<open>Incrementality of KBO w.r.t. precedence.\<close>
locale two_kbos = kbo1: kbo w w0 scf least1 S1 W1 + kbo2: kbo w w0 scf least2 S2 W2
  for w w0 scf and least1 :: "'f \<Rightarrow> bool" and S1 W1 least2 S2 W2
begin
lemma kbo_prec_mono: 
  assumes least_imp: "\<And>f::'f. least1 f \<Longrightarrow> least2 f"
    and S_imp: "\<And>fn gm. S1 fn gm \<Longrightarrow> S2 fn gm"
    and W_imp: "\<And>fn gm. W1 fn gm \<Longrightarrow> W2 fn gm"
  shows "(kbo1.S s t \<longrightarrow> kbo2.S s t) \<and> (kbo1.NS s t \<longrightarrow> kbo2.NS s t)"
    (is "(?S s t \<longrightarrow> ?S' s t) \<and> (?N s t \<longrightarrow> ?N' s t)")
proof (induct rule: kbo1.kbo.induct)
  case (1 s t)
  note simps = kbo1.kbo.simps kbo2.kbo.simps
  note [simp del] = simps
  note lex_mono = lex_ext_unbounded_mono[of _ _ "kbo1.kbo" "kbo2.kbo"]
  note lex_mono1 = lex_mono[THEN conjunct1, rule_format]
  note lex_mono2 = lex_mono[THEN conjunct2, rule_format]
  show ?case unfolding simps[of s t] using 1 
    by (auto split: term.splits simp: least_imp S_imp W_imp intro!: lex_mono1 lex_mono2)
qed
end

context admissible_kbo
begin


section \<open>use KBO as ce-compatible reduction pair / triple\<close>

abbreviation kbo_S where "kbo_S \<equiv> {(s,t). S s t}"
abbreviation kbo_NS where "kbo_NS \<equiv> {(s,t). NS s t}"

lemma kbo_NS_supteq: "s \<unrhd> t \<Longrightarrow> (s,t) \<in> kbo_NS"
  using NS_supteq by blast

lemma kbo_S_supteq: "s \<rhd> t \<Longrightarrow> (s,t) \<in> kbo_S"
  using S_supt by blast

lemma kbo_S_mono: "ctxt.closed kbo_S"
  by (rule, insert S_ctxt, blast)

lemma kbo_ce_compat: "ce_trs cn \<subseteq> kbo_S \<inter> kbo_NS"
proof -
  obtain c n where cn: "cn = (c,n)" by force
  {
    fix s t
    assume "(s,t) \<in> ce_trs cn"
    then have "s \<rhd> t" unfolding cn ce_trs.simps by auto
    from S_supt[OF this] have "(s,t) \<in> kbo_S" by simp
    with S_imp_NS[of s t] have "(s,t) \<in> kbo_S \<inter> kbo_NS" by auto
  }
  then show ?thesis by auto
qed

lemma S_ce_compat: "ce_trs cn \<subseteq> kbo_S" using kbo_ce_compat by blast
lemma NS_ce_compat: "ce_trs cn \<subseteq> kbo_NS" using kbo_ce_compat by blast

lemma kbo_redpair: "mono_ce_af_redtriple_order kbo_S kbo_NS kbo_NS full_af"
proof (unfold_locales)
  show "subst.closed kbo_S" using S_subst by auto
  show "subst.closed kbo_NS" using NS_subst by auto
  show "ctxt.closed kbo_NS" 
    by (rule, insert NS_ctxt, blast)
  show "kbo_NS O kbo_S \<subseteq> kbo_S" using NS_S_compat by auto
  show "trans kbo_NS" using NS_trans unfolding trans_def by auto
  show "refl kbo_NS" using NS_refl unfolding refl_on_def by auto
  show "af_compatible full_af kbo_NS" by (rule full_af)
  show "ce_compatible kbo_NS"
    using NS_ce_compat unfolding ce_compatible_def by blast
  show "ce_compatible kbo_S"
    using S_ce_compat unfolding ce_compatible_def by blast
  show "kbo_S \<subseteq> kbo_NS" using S_imp_NS by blast
  show "ctxt.closed kbo_S" by (rule kbo_S_mono)
qed



section \<open>Strong Normalization via Kruskal\<close>

lemma pr_strict_reflclp_imp_pr_weak:
  assumes "pr_strict\<^sup>=\<^sup>= x y" shows "pr_weak x y"
  using assms by (auto simp: pr_strict)

lemma pr_strict_trans:
  "pr_strict fn gm \<Longrightarrow> pr_strict gm hk \<Longrightarrow> pr_strict fn hk"
  using pr_weak_trans
  unfolding pr_strict by blast

lemma transp_on_pr_strict: "transp_on UNIV pr_strict"
  using pr_strict_trans unfolding transp_on_def by blast

lemma irreflp_on_pr_strict: "irreflp_on UNIV pr_strict"
  using pr_strict_irrefl unfolding irreflp_on_def by blast

lemma po_on_pr_strict: "po_on pr_strict\<inverse>\<inverse> UNIV"
proof
  show "irreflp_on UNIV pr_strict\<inverse>\<inverse>"
    by (simp) (rule irreflp_on_pr_strict)
next
  show "transp_on UNIV pr_strict\<inverse>\<inverse>"
    by (simp) (rule transp_on_pr_strict)
qed

lemma wfp_on_pr_strict: "wfp_on pr_strict\<inverse>\<inverse> (UNIV::('f \<times> nat) set)"
  using pr_SN unfolding wfp_on_SN_conv by auto

definition "scfs fn = map (scf fn) [0 ..< snd fn]"

lemma weight_list_conv:
  "sum_list (map (\<lambda>(t\<^sub>i, i). weight t\<^sub>i * scf (f, n) i) (zip ts [0 ..< n])) =
   sum_list (map (\<lambda>(t\<^sub>i, c\<^sub>i). weight t\<^sub>i * c\<^sub>i) (zip ts (scfs (f, n))))"
  by (auto simp: scfs_def zip_map2 o_def intro: arg_cong)

lemma S_subterm_one:
  assumes "t \<in> set ts"
  shows "S (Fun f ts) t"
proof -
  from \<open>t \<in> set ts\<close> have "Fun f ts \<rhd> t" by auto
  with S_supt show ?thesis by blast
qed

text \<open>Lemmas for \emph{simple weights} (i.e., without subterm coefficient functions).\<close>
context
  assumes scf_1: "i < n \<Longrightarrow> scf (f, n) i = 1"
begin

lemma weight_simp' [simp]:
  "weight (Fun f ts) = w (f, length ts) + (\<Sum>t\<leftarrow>ts. weight t)"
proof -
  define n where "n = length ts"
  have *: "zip (map weight ts) (map (scf (f, n)) [0..<n]) = map (\<lambda>t. (weight t, 1)) ts"
    (is "?xs = ?ys")
  proof (rule nth_equalityI)
    show length_eq: "length ?xs = length ?ys" by (simp add: n_def)
    fix i
    assume "i < length ?xs"
    then have *: "i < length (map weight ts)" "i < length (map (scf (f, n)) [0..<n])"
      and "i < n"
      by auto
    then have len': "i < length [0..<n]" by (simp add: nth_def)
    from \<open>i < n\<close> have ith: "[0..<n] ! i = i" by simp
    have map_ith: "map (scf (f, n)) [0..<n] ! i = 1"
      using scf_1 [OF \<open>i < n\<close>] by (simp add: ith nth_map [OF len'])
    show "?xs ! i = ?ys ! i"
      unfolding nth_zip [OF *] map_ith
      using \<open>i < n\<close> unfolding n_def by simp
  qed
  have "(\<Sum>(ti, i)\<leftarrow>zip ts [0..<n]. weight ti * scf (f, n) i) =
    (\<Sum>tii\<leftarrow>zip ts [0..<n]. weight (fst tii) * scf (f, n) (snd tii))"
    unfolding split_def ..
  also have "\<dots> = (\<Sum>wic\<leftarrow>zip (map weight ts) (map (scf (f, n)) [0..<n]). fst wic * snd wic)"
    by (simp add: zip_map_map split_def o_def)
  also have "\<dots> = (\<Sum>wic\<leftarrow>map (\<lambda>t. (weight t, 1)) ts. fst wic * snd wic)" unfolding * ..
  also have "\<dots> = (\<Sum>wic\<leftarrow>map (\<lambda>t. (weight t, 1::nat)) ts. fst wic * 1)" by (induct ts) auto
  also have "\<dots> = (\<Sum>t\<leftarrow>ts. weight t)" by (induct ts) auto
  finally show ?thesis unfolding weight.simps by (simp add: n_def)
qed

lemma subseq_weight:
  assumes "subseq ss ts"
  shows "(\<Sum>s\<leftarrow>ss. weight s) \<le> (\<Sum>t\<leftarrow>ts. weight t)"
  using assms by (induct) simp+

lemma concat_map_singleton:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = [g x]"
  shows "concat (map f xs) = map g xs"
  using assms by (induct xs) simp_all

lemma wqo_on_map':
  fixes P and Q and h
  defines "P' \<equiv> \<lambda>x y. P x y \<and> Q (h x) (h y)"
  assumes "wqo_on P\<^sup>=\<^sup>= A"
    and "wqo_on Q B"
    and subset: "h ` A \<subseteq> B"
  shows "wqo_on P'\<^sup>=\<^sup>= A"
proof
  let ?Q = "\<lambda>x y. Q (h x) (h y)"
  from \<open>wqo_on P\<^sup>=\<^sup>= A\<close> have "transp_on A P\<^sup>=\<^sup>="
    by (rule wqo_on_imp_transp_on)
  then show "transp_on A P'\<^sup>=\<^sup>="
    using \<open>wqo_on Q B\<close> and subset
    unfolding wqo_on_def transp_on_def P'_def by blast

  from \<open>wqo_on P\<^sup>=\<^sup>= A\<close> have "almost_full_on P\<^sup>=\<^sup>= A"
    by (rule wqo_on_imp_almost_full_on)
  from \<open>wqo_on Q B\<close> have "almost_full_on Q B"
    by (rule wqo_on_imp_almost_full_on)

  show "almost_full_on P'\<^sup>=\<^sup>= A"
  proof
    fix f
    assume *: "\<forall>i::nat. f i \<in> A"
    from almost_full_on_imp_homogeneous_subseq [OF \<open>almost_full_on P\<^sup>=\<^sup>= A\<close> this]
      obtain g :: "nat \<Rightarrow> nat"
      where g: "\<And>i j. i < j \<Longrightarrow> g i < g j"
      and **: "\<forall>i. f (g i) \<in> A \<and> P\<^sup>=\<^sup>= (f (g i)) (f (g (Suc i)))"
        using * by auto
    from chain_transp_on_less [OF ** \<open>transp_on A P\<^sup>=\<^sup>=\<close>]
      have **: "\<And>i j. i < j \<Longrightarrow> P\<^sup>=\<^sup>= (f (g i)) (f (g j))" .
    let ?g = "\<lambda>i. h (f (g i))"
    from * and subset have B: "\<And>i. ?g i \<in> B" by auto
    with \<open>almost_full_on Q B\<close> [unfolded almost_full_on_def good_def, THEN bspec, of ?g]
      obtain i j :: nat
      where "i < j" and "Q (?g i) (?g j)" by blast
    with ** [OF \<open>i < j\<close>] have "P'\<^sup>=\<^sup>= (f (g i)) (f (g j))"
      by (auto simp: P'_def)
    with g [OF \<open>i < j\<close>] show "good P'\<^sup>=\<^sup>= f" by (auto simp: good_def)
  qed
qed

lemma scf_list_id [simp]:
  "scf_list (scf (f, length ss)) ss = ss"
proof -
  let ?scf = "scf (f, length ss)"
  have [simp]: "\<And>i x. i < length ss \<Longrightarrow> replicate (?scf i) x = [x]"
    using scf_1 [of _ "length ss" f] by simp
  have "concat (map (\<lambda>(x, i). replicate (?scf i) x) (zip ss [0 ..< length ss]))
    = map fst (zip ss [0 ..< length ss])"
    by (rule concat_map_singleton) (auto simp: in_set_zip)
  also have "\<dots> = ss" by (auto)
  finally show ?thesis by (simp add: scf_list_def)
qed

lemma SCF_id [simp]:
  "SCF = (\<lambda>x. x)"
proof
  fix t :: "('f, 'v) term"
  show "SCF t = t" by (induct t) (auto simp: map_idI)
qed

lemma subseq_vars_term_ms:
  assumes "subseq ts ss"
  shows "vars_term_ms (SCF (Fun g ts)) \<subseteq># vars_term_ms (SCF (Fun f ss))"
  using assms
proof (induct)
  case (list_emb_Cons xs ys y)
  obtain m1 m2 where id: "\<Sum>\<^sub>#(image_mset vars_term_ms (mset xs)) = m1" 
    "\<Sum>\<^sub># (image_mset vars_term_ms (mset ys)) = m2" by auto
  from list_emb_Cons
  have IH: "m1 \<subseteq># m2" by (auto simp: id)
  also have "\<dots> \<subseteq># vars_term_ms y + m2" by (rule mset_subset_eq_add_right)
  finally show ?case by (simp add: id)
qed auto  

text \<open>
  Without subterm coefficient functions, @{term S} is a simplification-order.
\<close>
lemma simplification_order:
  assumes "wqo_on pr_strict\<inverse>\<inverse>\<^sup>=\<^sup>= UNIV"
  shows "simplification_order {(x :: ('f, 'v) term, y). S x y}"
  (is "simplification_order ?kbo")
proof (unfold simplification_order_def)
  let ?P = "\<lambda>x y. pr_strict x y \<and> w x \<ge> w y"
  have "range w \<subseteq> UNIV" by auto
  from wqo_on_map' [OF assms wqo_on_UNIV_nat this]
    have "wqo_on ?P\<inverse>\<inverse>\<^sup>=\<^sup>= UNIV" by (auto simp: conversep_iff [abs_def])
  moreover
  have "emb UNIV ?P \<subseteq> ?kbo"
  proof (rule emb_subsetI)
    show "\<And>s t u. (s, t) \<in> ?kbo \<Longrightarrow> (t, u) \<in> ?kbo \<Longrightarrow> (s, u) \<in> ?kbo"
      and "\<And>C s t. (s, t) \<in> ?kbo \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> ?kbo"
      and "\<And>\<sigma> s t. (s, t) \<in> ?kbo \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?kbo"
      by (auto simp del: kbo.simps dest: S_trans S_ctxt S_subst)
  next
    fix t f and ts :: "('f, 'v) term list"
    assume "t \<in> set ts"
    from S_subterm_one [OF this]
      show "(Fun f ts, t) \<in> ?kbo" by simp
  next
    fix f g and ss ts :: "('f, 'v) term list"
    presume strict: "pr_strict (f, length ss) (g, length ts)"
      and w: "w (f, length ss) \<ge> w (g, length ts)"
      and "subseq ts ss"
    have "vars_term_ms (SCF (Fun g ts)) \<subseteq># vars_term_ms (SCF (Fun f ss))"
      by (rule subseq_vars_term_ms) fact
    moreover
    have "weight (Fun f ss) \<ge> weight (Fun g ts)"
      using subseq_weight [OF \<open>subseq ts ss\<close>] and w
      unfolding weight_simp' by simp
    ultimately
    show "(Fun f ss, Fun g ts) \<in> ?kbo" using strict by (simp add: kbo.simps)
  qed simp_all
  moreover
  have "rewrite_order ?kbo"
    by (auto simp del: kbo.simps
             simp: rewrite_order_def rewrite_relation_def irrefl_def S_irrefl trans_def
             dest: S_ctxt S_subst S_trans)
  ultimately
  show "rewrite_order ?kbo \<and> (\<exists>Q. wqo_on Q\<inverse>\<inverse>\<^sup>=\<^sup>= UNIV \<and> emb UNIV Q \<subseteq> ?kbo)" by blast
qed

text \<open>
  Alternative termination proof for the case that @{term "pr_strict\<inverse>\<inverse>\<^sup>=\<^sup>="} is a
  well-quasi-order.
\<close>
lemma 
  assumes "wqo_on pr_strict\<inverse>\<inverse>\<^sup>=\<^sup>= UNIV"
  shows "SN {(x :: ('f, 'v) term, y). S x y}"
  by (rule simplification_order_imp_SN [OF simplification_order [OF assms]])

declare weight_simp' [simp del]
end
end


section \<open>KBO Closures\<close>

context kbo
begin

text \<open>The next definition forms a closure of a given relation gt with respect to a KBO
      (following Martin/Nipkow CADE 1990, where gt is instantiated by an order on variables.\<close>
fun kbo_closure :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<times> bool" where
  "kbo_closure gt s t = (
    if (s, t) \<in> gt then (True, True)
    else if (vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s)
    then if (weight t < weight s)
      then (True, True)
      else (case s of
        Var y \<Rightarrow> (False, (case t of Var x \<Rightarrow> x = y | Fun g ts \<Rightarrow> ts = [] \<and> least g)) 
      | Fun f ss \<Rightarrow> (case t of
          Var x \<Rightarrow> (True, True)
        | Fun g ts \<Rightarrow> if pr_strict (f, length ss) (g, length ts)
          then (True, True)
          else if pr_weak (f, length ss) (g, length ts)
          then lex_ext_unbounded (kbo_closure gt) ss ts
          else (False, False)))
    else (False, False))"

lemma kbo_kbo_closure:
  "(S s t \<longrightarrow> fst (kbo_closure ord s t)) \<and> (NS s t \<longrightarrow> snd (kbo_closure ord s t))"
proof (induct s t rule: kbo.induct)
  case (1 s t)
  { assume "S s t"
    note kbo = this[unfolded kbo.simps[of s t]]
    hence vars:"vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s" by (cases, auto)
    have "fst (kbo_closure ord s t)" proof(cases "(s,t) \<in> ord")
      case True
      with kbo_closure.simps[of ord s t] show ?thesis by force
    next
      case False
      hence "(s, t) \<in> ord = False" by auto
      note kboc = kbo_closure.simps[of ord s t, unfolded eqTrueI[OF vars] this if_False if_True]
      note defs = kbo[unfolded eqTrueI[OF vars] if_True] kboc
      show ?thesis proof(cases "weight t < weight s", simp add:kboc vars)
        case False
        note w_False = this
        have "weight t < weight s = False" using False by auto
          note defs = defs[unfolded eqTrueI[OF vars] this, unfolded if_True if_False]
        show ?thesis proof(cases s)
          case (Var x)
          with defs show ?thesis unfolding Var term.case by (cases t, auto)
        next
          case (Fun f ss)
          note s = this
          note defs = defs[unfolded Fun, unfolded term.case]
          show ?thesis proof(cases t)
            case (Fun g ts)
            note defs = defs[unfolded Fun, unfolded term.case]
            from defs(2) show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)", simp add:s Fun)
              case False
              hence ps:"pr_strict (f, length ss) (g, length ts) = False" by auto
              show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
              case False
                with defs(1) show ?thesis unfolding s Fun defs ps by simp
              next
                case True
                note lex_ext_mono = lex_ext_unbounded_mono[of ss ts kbo "kbo_closure ord"]
                from defs(1) True have "fst (lex_ext_unbounded kbo ss ts)" unfolding ps by auto
                with 1[OF vars w_False s Fun False True] lex_ext_mono True show ?thesis
                  unfolding s Fun unfolding defs(2) unfolding ps by force
              qed
          qed
        qed (unfold Fun defs(2), auto)
      qed
    qed
  qed
  }
  note S = this
  { assume "NS s t"
    note kbo = this[unfolded kbo.simps[of s t]]
    hence vars:"vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s" by (cases, auto)
    have "snd (kbo_closure ord s t)" proof(cases "(s,t) \<in> ord")
      case True
      with kbo_closure.simps[of ord s t] show ?thesis by force
    next
      case False
      hence "(s, t) \<in> ord = False" by auto
      note kboc = kbo_closure.simps[of ord s t, unfolded this if_False]
      note defs = kbo kboc
      show ?thesis proof(cases "weight t < weight s", simp add:kboc vars)
        case False
        note w_False = this
        have "weight t < weight s = False" using False by auto
          note defs = defs[unfolded eqTrueI[OF vars] this, unfolded if_True if_False]
        show ?thesis proof(cases s)
          case (Var x)
          with defs show ?thesis unfolding Var term.case by (cases t, auto)
        next
          case (Fun f ss)
          note s = this
          note defs = defs[unfolded Fun, unfolded term.case]
          show ?thesis proof(cases t)
            case (Fun g ts)
            note defs = defs[unfolded Fun, unfolded term.case]
            from defs(2) show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)", simp add:s Fun)
              case False
              hence ps:"pr_strict (f, length ss) (g, length ts) = False" by auto
              show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
              case False
                with defs(1) show ?thesis unfolding s Fun defs ps by simp
              next
                case True
                note lex_ext_mono = lex_ext_unbounded_mono[of ss ts kbo "kbo_closure ord"]
                from defs(1) True have "snd (lex_ext_unbounded kbo ss ts)" unfolding ps by auto
                with 1[OF vars w_False s Fun False True] lex_ext_mono True show ?thesis
                  unfolding s Fun unfolding defs(2) unfolding ps by force
              qed
          qed
        qed (unfold Fun defs(2), auto)
      qed
    qed
  qed
  }
  with S show ?case by simp
qed

end

locale kbo_closure = admissible_kbo w w0 pr_strict pr_weak least scf
  for w w0 scf and least :: "'f \<Rightarrow> bool" and pr_strict pr_weak
begin

sublocale kbo .

context
  fixes X :: "'v set" and vord :: "'v rel" and f :: "'f"
  assumes total:"total_on X vord" and part_ord:"partial_order_on X vord" and
  wf:"wf (vord - Id)" and fin:"finite X" and non_empty:"vord \<noteq> {}" and f_least:"least f"
begin

abbreviation "ord \<equiv> {(Var x, Var y) |x y. (y, x) \<in> vord \<and> x \<noteq> y}"

lemma vord_X:"vord \<subseteq> X \<times> X"
  using part_ord unfolding partial_order_on_def preorder_on_def refl_on_def by auto

interpretation wo_rel vord
proof(unfold_locales)
  from part_ord have "vord \<subseteq> X \<times> X" unfolding partial_order_on_def preorder_on_def refl_on_def by auto
  with part_ord fin have fin:"finite vord" unfolding partial_order_on_def by (meson finite_SigmaI finite_subset)
  from total part_ord have "linear_order_on X vord"
    unfolding linear_order_on_def total_on_def Relation.total_on_def by auto
  with linear_order_on_well_order_on[OF fin] have wo:"well_order_on X vord" by auto
  show "Well_order vord" by (insert wo well_order_on_Well_order, auto)
qed

fun t\<^sub>i where "t\<^sub>i x 0 = Var x" | "t\<^sub>i x (Suc n) = Fun f [t\<^sub>i x n]"

lemma kbo_kbo_var_closure:
  "\<exists>\<sigma> :: ('f, 'v) subst. (\<forall>s t.(fst (kbo_closure ord s t) \<longrightarrow> S (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)) \<and> (snd (kbo_closure ord s t) \<longrightarrow> NS (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)))"
proof -
  fix x :: "'v"
  from non_empty have ne:"Field vord \<noteq> {}" unfolding Field_def Domain_def Range_def by fast
  with Well_order_isMinim_exists[OF _ this] vord_X obtain z :: "'v" where
    z:"isMinim (Field vord) z" by auto
  define \<T> where "\<T> \<equiv> {t\<^sub>i x n |n::nat. True}"
  have ti_supt:"t\<^sub>i x (Suc n) \<rhd> t\<^sub>i x n" for n by (induct n, auto)
  { fix n m
    from ti_supt have "n > m \<Longrightarrow> (t\<^sub>i x n) \<rhd> (t\<^sub>i x m)"
      by (induct "n - m", insert subterm.lift_Suc_mono_less, blast+)
  } note nm = this
  { fix ti tj
    assume "ti \<in> \<T>" and "tj \<in> \<T>"
    then obtain n m where ids:"ti = t\<^sub>i x n" "tj = t\<^sub>i x m"  unfolding \<T>_def by auto
    have "ti \<rhd> tj \<or> tj \<rhd> ti \<or> ti = tj" unfolding ids using nm by (cases "n > m", auto, cases "n = m", auto)
  }
  with S_supt have total:"Relation.total_on \<T> ((kbo_S\<inverse>)\<^sup>=)"
    unfolding Relation.total_on_converse unfolding Relation.total_on_def by blast
  let ?R = "((kbo_S\<inverse>)\<^sup>=) \<restriction> \<T>"
  from total have total:"Relation.total_on \<T> ?R" unfolding restrict_def Relation.total_on_def by auto
  from S_trans trans_on_converse have trans:"trans ?R" unfolding trans_def by blast
  { fix s t
    assume "(t, s) \<in> (kbo_S\<inverse>)\<^sup>= \<restriction> \<T>" "(s, t) \<in> (kbo_S\<inverse>)\<^sup>= \<restriction> \<T>" and neq:"s \<noteq> t"
    hence  "(t, s) \<in> kbo_S" "(s, t) \<in> kbo_S" unfolding restrict_def mem_Collect_eq split converse_iff by auto
    with S_trans[of s t s] SN_imp_acyclic[OF S_SN] have False unfolding acyclic_def by auto
  }
  hence antisym:"antisym ?R" unfolding antisym_def by auto
  from refl_reflcl trans antisym have po:"partial_order_on \<T> ?R"
    unfolding partial_order_on_def preorder_on_def refl_on_def by auto
  have eq:"(kbo_S\<inverse>)\<^sup>= \<restriction> \<T> - Id = (kbo_S\<^sup>= \<restriction> \<T> - Id)\<inverse>" by auto
  have "kbo_S\<^sup>= \<restriction> \<T> - Id \<subseteq> kbo_S" unfolding restrict_def by auto
  from SN_subset[unfolded SN_iff_wf, OF _ this]  S_SN[unfolded SN_iff_wf] have "wf (?R - Id)"
    unfolding SN_iff_wf eq by auto
  with total po have won:"well_order_on \<T> ?R" unfolding well_order_on_def linear_order_on_def by auto
  have aux:"Field ?R = \<T>" using nm unfolding Field_def by auto 
  from well_order_on_Well_order[OF won] have wo_f:"Well_order ?R" by auto
  have "inj (t\<^sub>i x)" proof
    fix n m
    assume id:"t\<^sub>i x n = t\<^sub>i x m"
    have 1:"n < m \<Longrightarrow> (t\<^sub>i x m) \<rhd> (t\<^sub>i x m)" using nm[of n m] unfolding id by auto
    have 2:"m < n \<Longrightarrow> (t\<^sub>i x m) \<rhd> (t\<^sub>i x m)" using nm[of m n] unfolding id by auto
    from 1 2 show "n = m" using nm supt_irrefl by force
  qed
  from range_inj_infinite[OF this] have inf:"infinite (Field ?R)"
    unfolding aux unfolding \<T>_def image_def by simp
  from finite_subset[of "Field vord" X] vord_X fin have "finite (Field vord)"
    unfolding Field_def by auto
  from finite_ordLess_infinite[OF WELL _ this inf] wo_f have "ordLess2 vord ?R" by auto
  then obtain \<sigma> :: "'v \<Rightarrow> ('f, 'v) term" where "embedS vord ?R \<sigma>" unfolding ordLess_def by auto
  hence emb:"embed vord ?R \<sigma>" unfolding embedS_def by auto
  note compat = embed_compat[OF emb, unfolded BNF_Wellorder_Embedding.compat_def]
  note is_emb = emb[unfolded embed_iff_compat_inj_on_ofilter[OF WELL wo_f]]
  { fix x y
    assume xy:"(x,y) \<in> vord" "\<sigma> y = \<sigma> x"
    from is_emb xy have "x = y" unfolding Field_def inj_on_def by auto
  }
  with compat have compat:"\<And>x y. (x,y) \<in> vord \<Longrightarrow> x = y \<or> S (\<sigma> y) (\<sigma> x)"
    unfolding restrict_def mem_Collect_eq split Un_iff converse_iff by fastforce
  from is_emb have "\<sigma> ` Field vord \<subseteq> Field ((kbo_S\<inverse>)\<^sup>= \<restriction> \<T>)" unfolding Order_Relation.ofilter_def by auto
  hence sigma_T:"\<And>x. x \<in> X \<Longrightarrow> \<sigma> x \<in> \<T>" unfolding aux using part_ord[unfolded order_on_defs refl_on_def]
    by (metis FieldI1 image_iff subset_eq)
  { fix s t :: "('f, 'v) term" and gt :: "('f, 'v) term rel"
    assume "gt = {(Var y, Var x) |x y. (x,y) \<in> vord \<and> x \<noteq> y }"
    with compat have "(fst (kbo_closure gt s t) \<longrightarrow> S (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)) \<and> (snd (kbo_closure gt s t) \<longrightarrow> NS (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))"
    proof (induct s t rule: kbo_closure.induct)
      case (1 gt s t)
      have gt_ord:"gt \<subseteq> ord" unfolding 1 by (rule, unfold 1 mem_Collect_eq, auto)
      { assume kc_st:"fst (kbo_closure gt s t)"
        note kboc = this[unfolded kbo_closure.simps[of gt s t]]
        have "S (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)" proof(cases "(s,t) \<in> gt")
          case True
          with 1 obtain x y where st:"s = Var x" "t = Var y" and xy:"(y,x) \<in> vord" "x \<noteq> y" by auto
          with 1(2)[OF xy(1)] show ?thesis unfolding st by simp
        next
          case False
          note n_gt = this
          note kboc = kboc[unfolded False[unfolded eq_False[symmetric]] if_False]
          let ?vw = "\<lambda>s t. vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s"
          from kboc False have vars:"?vw s t" by (cases, auto)
          hence "vars_term_ms (SCF (t \<cdot> \<sigma>)) \<subseteq># vars_term_ms (SCF (s \<cdot> \<sigma>))"
            using vars_term_ms_subst_mono scf_term_subst by metis
          with vars weight_stable_le have vars':"?vw (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)" by auto
          note kbo = kbo.simps[of "s \<cdot> \<sigma>" "t \<cdot> \<sigma>", unfolded eqTrueI[OF vars'] this if_False if_True]
          show ?thesis proof(cases "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>)")
            case True
            with vars' show ?thesis unfolding kbo by auto
          next
            case False
            hence "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>) = False" by auto
            note defs = kboc[unfolded eqTrueI[OF vars] if_True] kbo[unfolded this if_False]
            from False weight_stable_lt vars have w_False:"\<not> weight t < weight s" by auto
            hence "weight t < weight s = False" by auto
            note defs = defs[unfolded eqTrueI[OF vars] this, unfolded if_True if_False]
            show ?thesis proof(cases s)
              case (Var x)
              with defs show ?thesis unfolding Var term.case by (cases t, auto)
            next
              case (Fun f ss)
              note s = this
              note defs = defs[unfolded Fun, unfolded term.case]
              show ?thesis proof(cases t)
                case (Fun g ts)
                note defs = defs[unfolded Fun, unfolded eval_term.simps, unfolded term.case, unfolded length_map]
                from defs(2) show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)", simp add:s Fun)
                  case False
                  hence ps:"pr_strict (f, length ss) (g, length ts) = False" by auto
                  show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
                    case False
                    with defs(1) show ?thesis unfolding s Fun defs ps by simp
                  next
                    case True
                    note lex_ext_mono = lex_ext_unbounded_mono[of ss ts "kbo_closure gt" "\<lambda>s t. kbo (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"]
                    from defs True have "fst (lex_ext_unbounded (kbo_closure gt) ss ts)" unfolding ps by auto
                    with 1(1)[OF n_gt vars w_False s Fun False True _ _ 1(2) 1(3)] lex_ext_mono
                    have lex:"fst (lex_ext_unbounded (\<lambda>s t. kbo (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)) ss ts)"
                      unfolding s Fun unfolding defs unfolding ps by auto
                    from lex True show ?thesis unfolding s Fun eval_term.simps defs unfolding ps
                      by (simp add: lex_ext_unbounded_map2)
                  qed
                qed
              next
                case (Var y)
                from vars[unfolded Var] have "y \<in> vars_term s" using vars_term_scf_subset by force
                hence "s \<rhd> Var y" using s by force
                from S_subst S_supt[OF this] show ?thesis unfolding Var by fast
              qed
            qed
          qed
        qed
      }
  note S = this
  { assume kc_st:"snd (kbo_closure gt s t)"
    note kboc = this[unfolded kbo_closure.simps[of gt s t]]
    have "NS (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)" proof(cases "(s,t) \<in> gt")
      case True
      with 1 obtain x y where st:"s = Var x" "t = Var y" and xy:"(y,x) \<in> vord" "x \<noteq> y" by auto
      with 1(2)[OF xy(1)] S_imp_NS show ?thesis unfolding st by simp
    next
      case False
      note n_gt = this
      note kboc = kboc[unfolded False[unfolded eq_False[symmetric]] if_False]
      let ?vw = "\<lambda>s t. vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s"
      from kboc False have vars:"?vw s t" by (cases, auto)
      hence "vars_term_ms (SCF (t \<cdot> \<sigma>)) \<subseteq># vars_term_ms (SCF (s \<cdot> \<sigma>))"
        using vars_term_ms_subst_mono scf_term_subst by metis
      with vars weight_stable_le have vars':"?vw (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)" by auto
      note kbo = kbo.simps[of "s \<cdot> \<sigma>" "t \<cdot> \<sigma>", unfolded eqTrueI[OF vars'] this if_False if_True]
      show ?thesis proof(cases "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>)")
        case True
        with vars' show ?thesis unfolding kbo by auto
      next
        case False
        hence "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>) = False" by auto
        note defs = kboc[unfolded eqTrueI[OF vars] if_True] kbo[unfolded this if_False]
        from False weight_stable_lt vars have w_False:"\<not> weight t < weight s" by auto
        hence "weight t < weight s = False" by auto
        note defs = defs[unfolded eqTrueI[OF vars] this, unfolded if_True if_False]
        show ?thesis proof(cases s)
          case (Var x)
          from defs(1) consider "t = Var x" | "(\<exists>g. t = Fun g [] \<and> least g)"
            unfolding Var term.case by (cases t, auto)
          thus ?thesis proof(cases, simp add:NS_refl 1 Var)
            case 2
            then obtain g where "t \<cdot> \<sigma> = Fun g []" "least g" by auto
            with NS_all_least show ?thesis by auto
          qed
        next
          case (Fun f ss)
          note s = this
          note defs = defs[unfolded Fun, unfolded term.case]
          show ?thesis proof(cases t)
            case (Fun g ts)
            note defs = defs[unfolded Fun, unfolded eval_term.simps, unfolded term.case, unfolded length_map]
            from defs(2) show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)", simp add:s Fun)
              case False
              hence ps:"pr_strict (f, length ss) (g, length ts) = False" by auto
              show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
                case False
                with defs(1) show ?thesis unfolding s Fun defs ps by simp
              next
                case True
                note lex_ext_mono = lex_ext_unbounded_mono[of ss ts "kbo_closure gt" "\<lambda>s t. kbo (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"]
                from defs True have "snd (lex_ext_unbounded (kbo_closure gt) ss ts)" unfolding ps by auto
                with 1(1)[OF n_gt vars w_False s Fun False True _ _ 1(2) 1(3)] lex_ext_mono
                have lex:"snd (lex_ext_unbounded (\<lambda>s t. kbo (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)) ss ts)"
                  unfolding s Fun unfolding defs unfolding ps by auto
                from lex True show ?thesis unfolding s Fun eval_term.simps defs unfolding ps
                  by (simp add: lex_ext_unbounded_map2)
              qed
            qed
          next
            case (Var y)
            from vars[unfolded Var] have "y \<in> vars_term s" using vars_term_scf_subset by force
            hence "s \<rhd> Var y" using s by force
            from S_subst[OF S_supt[OF this]] S_imp_NS show ?thesis unfolding Var by fast
          qed
        qed
      qed
    qed
  }
  with S show ?case by simp
qed
} note key = this
  show ?thesis by (rule exI[of _ \<sigma>], insert key[of ord], blast)
qed

lemma kbo_closure_SN:"SN {(s, t) | s t. fst (kbo_closure ord s t)}"
proof
  fix ts
  assume a:"\<forall>i. (ts i, ts (Suc i)) \<in> {(s, t) | s t. fst (local.kbo_closure ord s t)}"
  from kbo_kbo_var_closure obtain \<sigma> :: "('f, 'v) subst" where
    \<sigma>:"\<forall>s t. (fst (local.kbo_closure ord s t) \<longrightarrow> S (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))" by auto
  define f where "f = (\<lambda>i. (ts i) \<cdot> \<sigma>)"
  from \<sigma> a have "\<And>i. S (f i) (f (Suc i))" unfolding f_def by fast
  with S_SN show False by auto
qed
end


lemma kbo_closure_compatible:
  "(fst (kbo_closure kbo_S s t) \<longrightarrow> S s t) \<and> (snd (kbo_closure kbo_S s t) \<longrightarrow> NS s t)"
proof (induct s t rule: kbo.induct)
  case (1 s t)
  { assume "fst (kbo_closure kbo_S s t)"
    note defs = this[unfolded kbo_closure.simps[of kbo_S s t]] kbo.simps[of s t]
    have "S s t" proof(cases "(s,t) \<in> kbo_S = False")
      case True
      with defs have vars:"vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s" by (cases, auto)
      note defs = defs[unfolded eqTrueI[OF this] True if_False if_True]
    show ?thesis proof(cases "weight t < weight s")
      case False
      note weight = this
      hence "weight t < weight s = False" by auto
      note defs = defs[unfolded this if_False]
        show ?thesis proof(cases s)
          case (Fun f ss)
          note s = this
          note defs = defs[unfolded Fun, unfolded term.case]
          show ?thesis proof(cases t)
            case (Fun g ts)
            note defs = defs[unfolded Fun, unfolded term.case]
            from defs(2) show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)", simp add:s defs Fun)
              case False
              hence ps:"pr_strict (f, length ss) (g, length ts) = False" by auto
              show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
                case True
                note defs = defs[unfolded ps eqTrueI[OF this] if_False if_True]
                note lex_ext_mono = lex_ext_unbounded_mono[of ss ts "kbo_closure kbo_S" kbo]
                with 1[OF vars weight s Fun _ True] ps defs show ?thesis unfolding s Fun by auto
              qed (unfold s Fun ps, insert defs ps, auto)
          qed
        qed (unfold Fun defs(2), auto)
      qed (insert defs, auto)
    qed (insert defs, auto)
  qed (insert defs, auto)
  }
  note S = this
  { assume "snd (kbo_closure kbo_S s t)"
    note defs = this[unfolded kbo_closure.simps[of kbo_S s t]] kbo.simps[of s t]
    have "NS s t" proof(cases "(s,t) \<in> kbo_S = False")
      case True
      with defs have vars:"vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s" by (cases, auto)
      note defs = defs[unfolded eqTrueI[OF this] True if_False if_True]
    show ?thesis proof(cases "weight t < weight s")
      case False
      note weight = this
      hence "weight t < weight s = False" by auto
      note defs = defs[unfolded this if_False]
        show ?thesis proof(cases s)
          case (Fun f ss)
          note s = this
          note defs = defs[unfolded Fun, unfolded term.case]
          show ?thesis proof(cases t)
            case (Fun g ts)
            note defs = defs[unfolded Fun, unfolded term.case]
            from defs(2) show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)", simp add:s defs Fun)
              case False
              hence ps:"pr_strict (f, length ss) (g, length ts) = False" by auto
              show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
                case True
                note defs = defs[unfolded ps eqTrueI[OF this] if_False if_True]
                note lex_ext_mono = lex_ext_unbounded_mono[of ss ts "kbo_closure kbo_S" kbo]
                with 1[OF vars weight s Fun _ True] ps defs show ?thesis unfolding s Fun by auto
              qed (unfold s Fun ps, insert defs ps, auto)
          qed
        qed (unfold Fun defs(2), auto)
      qed (insert defs, auto)
    qed (insert defs, auto)
  qed (insert defs S_imp_NS[of s t], auto)
  }
  with S show ?case by blast
qed

lemma kbo_closure_mono:
  assumes "\<O> \<subseteq> \<O>'"
  shows "(fst (kbo_closure \<O> s t) \<longrightarrow> fst (kbo_closure \<O>' s t)) \<and>
  (snd (kbo_closure \<O> s t) \<longrightarrow> snd (kbo_closure \<O>' s t))"
proof (induct s t rule: kbo.induct)
  case (1 s t)
  { assume *:"fst (kbo_closure \<O> s t)"
    have "fst (kbo_closure \<O>' s t)" proof(cases "(s, t) \<in> \<O>'", simp add: kbo_closure.simps[of \<O>' s t])
      case False
      with assms have "\<not> (s, t) \<in> \<O>" by auto
      note kboc\<^sub>1 = kbo_closure.simps[of \<O> s t, unfolded this[unfolded eq_False[symmetric]] if_False]
      note kboc\<^sub>2 = kbo_closure.simps[of \<O>' s t, unfolded False[unfolded eq_False[symmetric]] if_False]
      note kboc = kboc\<^sub>1 kboc\<^sub>2
      let ?vs = "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s"
      have "fst (kbo_closure \<O> s t) = fst (kbo_closure \<O>' s t)" proof(cases ?vs)
        case True
        note kboc = True kboc[unfolded eqTrueI[OF True] if_True]
        show ?thesis proof(cases "weight t < weight s")
          case False
          note kboc = False kboc[unfolded False[unfolded eq_False[symmetric]] if_False]
          show ?thesis proof(cases s)
            case (Fun f ss)
            note kboc = this kboc[unfolded Fun term.case]
            show ?thesis proof(cases t)
              case (Fun g ts)
              note kboc = this kboc[unfolded Fun term.case]
              show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)")
                case False
                note kboc = False kboc[unfolded False[unfolded eq_False[symmetric]] if_False]
                show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
                  case True
                  note IH = 1[unfolded kboc, OF kboc(5) kboc(4) refl refl kboc(1) True]
                  note lex = lex_ext_unbounded_mono[of ss ts "kbo_closure \<O>" "kbo_closure \<O>'"]
                  with * True IH show ?thesis unfolding kboc eqTrueI[OF True] if_True by blast
                qed (unfold kboc, auto)
              qed (unfold kboc, auto)
            qed (unfold kboc, auto)
        qed (unfold kboc, auto)
      qed (unfold kboc, auto)
    qed (unfold kboc, auto)
    with * show ?thesis by auto
  qed
  } note S = this
  { assume *:"snd (kbo_closure \<O> s t)"
    have "snd (kbo_closure \<O>' s t)" proof(cases "(s, t) \<in> \<O>'", simp add: kbo_closure.simps[of \<O>' s t])
      case False
      with assms have "\<not> (s, t) \<in> \<O>" by auto
      note kboc\<^sub>1 = kbo_closure.simps[of \<O> s t, unfolded this[unfolded eq_False[symmetric]] if_False]
      note kboc\<^sub>2 = kbo_closure.simps[of \<O>' s t, unfolded False[unfolded eq_False[symmetric]] if_False]
      note kboc = kboc\<^sub>1 kboc\<^sub>2
      let ?vs = "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s"
      have "snd (kbo_closure \<O> s t) = snd (kbo_closure \<O>' s t)" proof(cases ?vs)
        case True
        note kboc = True kboc[unfolded eqTrueI[OF True] if_True]
        show ?thesis proof(cases "weight t < weight s")
          case False
          note kboc = False kboc[unfolded False[unfolded eq_False[symmetric]] if_False]
          show ?thesis proof(cases s)
            case (Fun f ss)
            note kboc = this kboc[unfolded Fun term.case]
            show ?thesis proof(cases t)
              case (Fun g ts)
              note kboc = this kboc[unfolded Fun term.case]
              show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)")
                case False
                note kboc = False kboc[unfolded False[unfolded eq_False[symmetric]] if_False]
                show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
                  case True
                  note IH = 1[unfolded kboc, OF kboc(5) kboc(4) refl refl kboc(1) True]
                  note lex = lex_ext_unbounded_mono[of ss ts "kbo_closure \<O>" "kbo_closure \<O>'"]
                  with * True IH show ?thesis unfolding kboc eqTrueI[OF True] if_True by blast
                qed (unfold kboc, auto)
              qed (unfold kboc, auto)
            qed (unfold kboc, auto)
        qed (unfold kboc, auto)
      qed (unfold kboc, auto)
    qed (unfold kboc, auto)
    with * show ?thesis by auto
  qed
  }
  with S show ?case by auto
qed

lemma kbo_closure_subst:
 "(fst (kbo_closure \<O> s t) \<longrightarrow> fst (kbo_closure {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u,v) \<in> \<O>} (s \<cdot> \<sigma>) (t \<cdot> (\<sigma> :: ('f, 'v) subst)))) \<and>
  (snd (kbo_closure \<O> s t) \<longrightarrow> snd (kbo_closure {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u,v) \<in> \<O>} (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)))"
proof (induct s t rule: kbo.induct)
  case (1 s t)
  define \<O>\<^sub>\<sigma> where "\<O>\<^sub>\<sigma> \<equiv> {(u \<cdot> \<sigma>, v \<cdot> \<sigma>) |u v. (u,v) \<in> \<O>}"
  let ?s = "s \<cdot> \<sigma>" and ?t = "t \<cdot> \<sigma>"
  { assume *:"fst (kbo_closure \<O> s t)"
    have "fst (kbo_closure \<O>\<^sub>\<sigma> (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))" proof(cases "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> \<O>\<^sub>\<sigma>", simp add: kbo_closure.simps[of \<O>\<^sub>\<sigma> ?s ?t])
      case False
      hence "\<not> (s, t) \<in> \<O>" unfolding \<O>\<^sub>\<sigma>_def by auto
      note kbc = kbo_closure.simps[of \<O> s t, unfolded this[unfolded eq_False[symmetric]] if_False]
        kbo_closure.simps[of \<O>\<^sub>\<sigma> ?s ?t, unfolded False[unfolded eq_False[symmetric]] if_False]
      from * kbc(1) have v:"vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s" by (cases, auto)
      from weight_stable_le v have w\<sigma>: "weight (t \<cdot> \<sigma>) \<le> weight (s \<cdot> \<sigma>)" by auto
      from vars_term_ms_subst_mono[of _ _ "\<lambda> x. SCF (\<sigma> x)"] v have v\<sigma>: "vars_term_ms (SCF (t \<cdot> \<sigma>)) \<subseteq># vars_term_ms (SCF (s \<cdot> \<sigma>))"
         unfolding scf_term_subst by auto
      show ?thesis proof(cases "weight t < weight s", simp add: weight_stable_lt[of t s] v kbc v\<sigma> w\<sigma>)
        case False
        note w_False = this
        show ?thesis proof (cases "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>)", simp add:kbc(2) v\<sigma>)
          case False
          hence "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>) = False" "weight t < weight s = False" using w_False by auto
          note kbc = kbc[unfolded eqTrueI[OF v] eqTrueI[OF v\<sigma>] eqTrueI[OF w\<sigma>] this, unfolded simp_thms(22) if_True if_False]
          show ?thesis proof(cases s)
            case (Var x)
            from *[unfolded kbc] show ?thesis unfolding Var by auto
          next
            case (Fun f ss)
            note s = this
            show ?thesis proof(cases t)
              case (Var y)
              from set_mset_mono[OF conjunct1[OF v]] have "y \<in> vars_term (SCF s)" unfolding Var by (auto simp: o_def)
              also have "\<dots> \<subseteq> vars_term s" by (rule vars_term_scf_subset)
              finally have "y \<in> vars_term s" by auto
              hence "s \<rhd> Var y" unfolding Fun using subterm.dual_order.order_iff_strict by force
              with supt_subst Var have "?s \<rhd> ?t" by blast
              from S_supt[OF this] kbo_kbo_closure show ?thesis by fast
            next
              case (Fun g ts)
              note kbc = kbc[unfolded Fun s, unfolded term.case eval_term.simps length_map]
              note * = *[unfolded Fun s kbc]
              from kbc(2) show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)", simp add:s Fun)
                case False
                note ps_False = this
                hence ps:"pr_strict (f, length ss) (g, length ts) = False" by auto
                show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
                  case False
                  with * show ?thesis unfolding ps by simp
                next
                  case True
                  note kbc = kbc[unfolded ps eqTrueI[OF True] if_True if_False]
                  from * True have *:"fst (lex_ext_unbounded (kbo_closure \<O>) ss ts)" unfolding ps by auto
                  note IH = 1[OF v w_False s Fun ps_False True]
                  let ?subst = "map (\<lambda>t. t \<cdot> \<sigma>)"
                  { fix i
                    assume i:"i < length ss" "i < length ts" and S:"fst (kbo_closure \<O> (ss ! i) (ts ! i))"
                    from IH[OF i] S have "fst (kbo_closure \<O>\<^sub>\<sigma> (?subst ss ! i) (?subst ts ! i))"
                      unfolding \<O>\<^sub>\<sigma>_def using nth_map[of _ _ "\<lambda>t. t \<cdot> \<sigma>"] i by presburger
                  }
                  note S_imply = this
                  { fix i
                    assume i:"i < length ss" "i < length ts" and NS:"snd (kbo_closure \<O> (ss ! i) (ts ! i))"
                    from IH[OF i] NS have "snd (kbo_closure \<O>\<^sub>\<sigma> (?subst ss ! i) (?subst ts ! i))"
                      unfolding \<O>\<^sub>\<sigma>_def using nth_map[of _ _ "\<lambda>t. t \<cdot> \<sigma>"] i by presburger
                  }
                  from lex_ext_unbounded_map2[of ss ts "kbo_closure \<O>" "kbo_closure \<O>\<^sub>\<sigma>", OF S_imply this] *
                  show ?thesis unfolding s Fun eval_term.simps unfolding kbc(2) by fast 
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  } note S = this
  { assume *:"snd (kbo_closure \<O> s t)"
    have "snd (kbo_closure \<O>\<^sub>\<sigma> (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))" proof(cases "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> \<O>\<^sub>\<sigma>", simp add: kbo_closure.simps[of \<O>\<^sub>\<sigma> ?s ?t])
      case False
      hence "\<not> (s, t) \<in> \<O>" unfolding \<O>\<^sub>\<sigma>_def by auto
      note kbc = kbo_closure.simps[of \<O> s t, unfolded this[unfolded eq_False[symmetric]] if_False]
        kbo_closure.simps[of \<O>\<^sub>\<sigma> ?s ?t, unfolded False[unfolded eq_False[symmetric]] if_False]
      from * kbc(1) have v:"vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s" by (cases, auto)
      from weight_stable_le v have w\<sigma>: "weight (t \<cdot> \<sigma>) \<le> weight (s \<cdot> \<sigma>)" by auto
      from vars_term_ms_subst_mono[of _ _ "\<lambda> x. SCF (\<sigma> x)"] v have v\<sigma>: "vars_term_ms (SCF (t \<cdot> \<sigma>)) \<subseteq># vars_term_ms (SCF (s \<cdot> \<sigma>))"
         unfolding scf_term_subst by auto
      show ?thesis proof(cases "weight t < weight s", simp add: weight_stable_lt[of t s] v kbc v\<sigma> w\<sigma>)
        case False
        note w_False = this
        show ?thesis proof (cases "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>)", simp add:kbc(2) v\<sigma>)
          case False
          hence "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>) = False" "weight t < weight s = False" using w_False by auto
          note kbc = kbc[unfolded eqTrueI[OF v] eqTrueI[OF v\<sigma>] eqTrueI[OF w\<sigma>] this, unfolded simp_thms(22) if_True if_False]
          show ?thesis proof(cases s)
            case (Var x)
            note s = this
            show ?thesis proof(cases t)
              case (Var y)
              with *[unfolded kbc] s have st:"s=t" by auto
              from NS_refl[of ?t] kbo_kbo_closure show ?thesis unfolding st by fast
            next
              case (Fun g ts)
              with *[unfolded kbc] s have least:"ts = [] \<and> least g" by auto
              hence t\<sigma>:"?t = Fun g ts" unfolding Fun eval_term.simps by auto
              with NS_all_least least kbo_kbo_closure show ?thesis by metis
            qed
          next
            case (Fun f ss)
            note s = this
            show ?thesis proof(cases t)
              case (Var y)
              from set_mset_mono[OF conjunct1[OF v]] have "y \<in> vars_term (SCF s)" unfolding Var by (auto simp: o_def)
              also have "\<dots> \<subseteq> vars_term s" by (rule vars_term_scf_subset)
              finally have "y \<in> vars_term s" by auto
              hence "s \<unrhd> Var y" unfolding Fun using subterm.dual_order.order_iff_strict by force
              with supt_subst Var have "?s  \<unrhd> ?t" by blast
              from NS_supteq[OF this] kbo_kbo_closure show ?thesis by fast
            next
              case (Fun g ts)
              note kbc = kbc[unfolded Fun s, unfolded term.case eval_term.simps length_map]
              note * = *[unfolded Fun s kbc]
              from kbc(2) show ?thesis proof(cases "pr_strict (f, length ss) (g, length ts)", simp add:s Fun)
                case False
                note ps_False = this
                hence ps:"pr_strict (f, length ss) (g, length ts) = False" by auto
                show ?thesis proof(cases "pr_weak (f, length ss) (g, length ts)")
                  case False
                  with * show ?thesis unfolding ps by simp
                next
                  case True
                  note kbc = kbc[unfolded ps eqTrueI[OF True] if_True if_False]
                  from * True have *:"snd (lex_ext_unbounded (kbo_closure \<O>) ss ts)" unfolding ps by auto
                  note IH = 1[OF v w_False s Fun ps_False True]
                  let ?subst = "map (\<lambda>t. t \<cdot> \<sigma>)"
                  { fix i
                    assume i:"i < length ss" "i < length ts" and S:"fst (kbo_closure \<O> (ss ! i) (ts ! i))"
                    from IH[OF i] S have "fst (kbo_closure \<O>\<^sub>\<sigma> (?subst ss ! i) (?subst ts ! i))"
                      unfolding \<O>\<^sub>\<sigma>_def using nth_map[of _ _ "\<lambda>t. t \<cdot> \<sigma>"] i by presburger
                  }
                  note S_imply = this
                  { fix i
                    assume i:"i < length ss" "i < length ts" and NS:"snd (kbo_closure \<O> (ss ! i) (ts ! i))"
                    from IH[OF i] NS have "snd (kbo_closure \<O>\<^sub>\<sigma> (?subst ss ! i) (?subst ts ! i))"
                      unfolding \<O>\<^sub>\<sigma>_def using nth_map[of _ _ "\<lambda>t. t \<cdot> \<sigma>"] i by presburger
                  }
                  from lex_ext_unbounded_map2[of ss ts "kbo_closure \<O>" "kbo_closure \<O>\<^sub>\<sigma>", OF S_imply this] *
                  show ?thesis unfolding s Fun eval_term.simps unfolding kbc(2) by fast 
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  }
  with S show ?case unfolding \<O>\<^sub>\<sigma>_def by fast
qed
end

declare kbo.kbo_closure.simps[code] 

locale two_kbo_closures = kbo1: kbo_closure w w0 scf least1 S1 W1 + kbo2: kbo_closure w w0 scf least2 S2 W2
  for w w0 scf and least1 :: "'f \<Rightarrow> bool" and S1 W1 least2 S2 W2
begin

lemma kbo_closure_prec_mono: 
  assumes least_imp: "\<And>f::'f. least1 f \<Longrightarrow> least2 f"
    and S_imp: "\<And>fn gm. S1 fn gm \<Longrightarrow> S2 fn gm"
    and W_imp: "\<And>fn gm. W1 fn gm \<Longrightarrow> W2 fn gm"
  shows "(fst (kbo1.kbo_closure \<O> s t) \<longrightarrow> fst (kbo2.kbo_closure \<O> s t)) \<and> 
               (snd (kbo1.kbo_closure \<O> s t) \<longrightarrow> snd (kbo2.kbo_closure \<O> s t))"
    (is "(?S \<O> s t \<longrightarrow> ?S' \<O> s t) \<and> (?N \<O> s t \<longrightarrow> ?N' \<O> s t)")
proof (induct rule: kbo1.kbo_closure.induct)
  case (1 \<O> s t)
  note simps = kbo1.kbo_closure.simps[] kbo2.kbo_closure.simps[]
  note [simp del] = simps
  note lex_mono = lex_ext_unbounded_mono[of _ _ "kbo1.kbo_closure \<O>" "kbo2.kbo_closure \<O>"]
  note lex_mono1 = lex_mono[THEN conjunct1, rule_format]
  note lex_mono2 = lex_mono[THEN conjunct2, rule_format]
  show ?case proof(cases "(s,t) \<in> \<O>")
    case True
    thus ?thesis unfolding simps[of \<O> s t] by auto
  next
    case False
    hence f:"(s,t) \<in> \<O> = False" by auto
    show ?thesis unfolding simps[of \<O> s t, unfolded f] using 1[OF False] 
      by (auto split: term.splits simp: least_imp S_imp W_imp intro!: lex_mono1 lex_mono2)
  qed
qed
end

end
