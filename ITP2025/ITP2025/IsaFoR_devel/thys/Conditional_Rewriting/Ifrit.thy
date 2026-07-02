(*
Author:  Florian Meßner <florian.messner@outlook.com> (2020)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Ifrit - Inductive Feasible Rule InTroduction\<close>

theory Ifrit
  imports
    Nonreach.Gtcap_Impl
    Conditional_Rewriting_Impl
begin

inductive Ifrit
  for P
  where
    "((l, r), cs) \<in> R \<Longrightarrow>
    R' \<subseteq> R \<Longrightarrow>
    (\<And>rl. rl \<in> R' \<Longrightarrow> Ifrit P R n rl) \<Longrightarrow>
    (P R' cs) \<Longrightarrow>
    Ifrit P R (Suc n) ((l,r),cs)"

print_theorems

definition "Ifrit_R P R n = {r . Ifrit P R n r}"

lemma Ifrit_Suc:
  assumes "Ifrit P R n rl"
  shows "Ifrit P R (Suc n) rl"
  using assms(1) proof (induction rule: Ifrit.induct)
  case (1 l r cs R R' n)
  then show ?case
    using Ifrit.intros[of l r cs R R' P "Suc n"]
    by auto
qed

lemma Ifrit_subset:
  assumes "Ifrit P R n rl"
  shows "rl \<in> R"
  using Ifrit.cases assms(1) by blast

lemma Ifrit_R_subset:
  assumes "rl \<in> (Ifrit_R P R n)"
  shows "rl \<in> R"
  using Ifrit_subset assms Ifrit_R_def by blast

lemma Ifrit_R_R':
  assumes  "R' = (Ifrit_R P R n)"
    and "rl \<in> R'"
  shows "R' \<subseteq> R" and "Ifrit P R n rl"
proof-
  show "R' \<subseteq> R"
    using Ifrit_R_subset assms by blast
next
  show "Ifrit P R n rl"
    using assms Ifrit_R_def by blast
qed

lemma Ifrit:
  assumes "(s, t) \<in> (cstep_n R n)"
    and P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and R: "finite R"
  shows "(s, t) \<in> (cstep_n (Ifrit_R P R n) n)"
  using assms(1,3) proof (induction n arbitrary: R s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have Ifrit_R_mono: "\<And> s t R . (s,t) \<in> (Ifrit_R P R n) \<Longrightarrow> (s,t) \<in> (Ifrit_R P R (Suc n))"
    using Ifrit_Suc unfolding Ifrit_R_def by blast
  then have "\<And> R. Ifrit_R P R n \<subseteq>  Ifrit_R P R (Suc n)" by auto
  then have "\<And> s t R . finite R \<Longrightarrow> (s, t) \<in> cstep_n R n \<Longrightarrow> (s, t) \<in> cstep_n (Ifrit_R P R (Suc n)) n"
    using Suc(1)[of _ _ R]
    by (meson Suc.IH cstep_n_subset subset_iff)
  then have "\<And> R . finite R \<Longrightarrow> (cstep_n R n)\<^sup>* \<subseteq> (cstep_n (Ifrit_R P R (Suc n)) n)\<^sup>*"
    by (auto simp: subrelI rtrancl_mono_rightI rtrancl_subset_rtrancl)
  then have "(\<And> R s t . finite R \<Longrightarrow> ((s, t) \<in> (cstep_n R n)\<^sup>* \<Longrightarrow> (s, t) \<in> (cstep_n (Ifrit_R P R (Suc n)) n)\<^sup>*))"
    by auto
  moreover obtain C l r \<sigma> cs where  cstep: "s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<and>
      ((l, r), cs) \<in> R \<and> (\<forall> (u, v) \<in> set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*)"
    using Suc cstep_n_Suc[of R n] by auto
  moreover obtain R' where R':"R' = Ifrit_R P R n " by auto
  moreover have "Ifrit_R P R n \<subseteq> Ifrit_R P R (Suc n)"
    by (simp add: \<open>Ifrit_R P R n \<subseteq> Ifrit_R P R (Suc n)\<close>)
  moreover have "\<And> s t R . finite R \<Longrightarrow> (s, t) \<in> cstep_n R n \<Longrightarrow> (s, t) \<in> cstep_n (Ifrit_R P R (n)) n"
    using Suc by auto
  moreover have "(\<forall>(u, v)\<in>set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep_n R' n)\<^sup>*)"
  proof
    fix u v
    show "(u, v) \<in> set cs \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep_n R' n)\<^sup>*"
      by (metis (no_types, lifting) R' Suc.IH Suc.prems(2) case_prodD cstep old.prod.exhaust rtrancl_mono subset_eq)
  qed
  moreover have "finite R'"
  proof-
    have "R' \<subseteq> R"
      unfolding R' using Ifrit_R_subset[of _ P R n] by auto
    then show ?thesis
      using finite_subset[of R' R] Suc(3) by blast
  qed
  moreover have "Ifrit P R (Suc n) ((l, r), cs)"
    using calculation(2) Ifrit.intros[of l r cs R R' P n ] P[of R' cs \<sigma> n ]
      calculation(3,6,7) unfolding Ifrit_R_def
    using P[of R' cs \<sigma> n] Ifrit_subset
    by blast
  moreover have "((l, r), cs) \<in> Ifrit_R P R (Suc n)" using calculation
    unfolding Ifrit_R_def by auto
  ultimately show ?case using cstep_n_SucI[of l r cs "(Ifrit_R P R (Suc n))" \<sigma> n s C t]
    using Suc.prems(2) by blast
qed

lemma Ifrit_arg:
  assumes "(\<And>rl. rl \<in> R' \<Longrightarrow> Ifrit P R n rl)"
    and "P R' cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    and R: "finite R"
  shows "P (Ifrit_R P R n) cs"
proof-
  have "R' \<subseteq> Ifrit_R P R n"
    using Ifrit_R_def assms by blast
  moreover have "finite (Ifrit_R P R n)"
  proof-
    have "Ifrit_R P R n \<subseteq> R"
      using Ifrit_R_subset by auto
    then show ?thesis
      using R finite_subset[of "Ifrit_R P R n" R] by blast
  qed
  ultimately show ?thesis
    using P_mono[of "Ifrit_R P R n" R' cs] assms by blast
qed

lemma Ifrit_conds:
  assumes "Ifrit P R (Suc n) ((l,r),cs)"
    and P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    and R: "finite R"
  shows "P (Ifrit_R P R n) cs"
proof-
  obtain S where "S = Ifrit_R P R n" by blast
  moreover have "S \<subseteq> R"
    using Ifrit_R_R'(1) using calculation by blast
  moreover have "(\<forall>x. x \<in> S \<longrightarrow> Ifrit P R n x)"
    by (simp add: Ifrit_R_R'(2) calculation(1))
  moreover have "(\<And>rl. rl \<in> S \<Longrightarrow> Ifrit P R n rl)"
    using calculation by auto
  moreover obtain R' where "((l, r), cs) \<in> R" and
    "R' \<subseteq> R" and
    "(\<And>rl. rl \<in> R' \<Longrightarrow> Ifrit P R n rl)" and
    "P R' cs"
    using assms(1) Ifrit.simps[of P R "Suc n" "((l,r),cs)"] by blast
  moreover have "R' \<subseteq> Ifrit_R P R n" using calculation
    by (metis Ifrit_R_def mem_Collect_eq subrelI)
  moreover have "P S cs"
    using Ifrit_arg[of R' P S n] P_mono calculation(1,2,7,8,9) R finite_subset[of S R]
    by blast
  moreover have "P (Ifrit_R P R n) cs"
    using calculation by auto
  moreover have "P S cs"
    using calculation by auto
  ultimately show ?thesis
    using assms(2) by blast
qed

lemma inc_fun:
  fixes m :: nat
  assumes f: "\<And>n. n \<le> k \<Longrightarrow> f n < f (Suc n)"
    and k: "m \<le> k"
  shows "\<exists>n. m < f n"
proof-
  have "(\<forall> n . (n \<le> k \<longrightarrow> n \<le> f n))"
  proof
    fix n
    show "n \<le> k \<longrightarrow> n \<le> f n"
    proof (induction n)
      case 0
      then show ?case by auto
    next
      case (Suc n)
      then show ?case by (meson Suc_leD Suc_le_eq dual_order.strict_trans2 f)
    qed
  qed
  then show ?thesis using assms
    using Suc_le_eq
    by (meson le_less_trans)
qed

lemma Ifrit_n:
  assumes R: "finite R"
  shows "\<exists>n \<le> card R. Ifrit_R P R n = Ifrit_R P R (Suc n)"
proof-
  have sub: "\<And>n. Ifrit_R P R n \<subseteq> R"
    using Ifrit_R_subset by blast
  then have finite: "\<And>n. finite (Ifrit_R P R n)" using R
    by (meson finite_subset)
  have "\<And>n. Ifrit_R P R n \<subseteq> Ifrit_R P R (Suc n)"
    unfolding Ifrit_R_def using Ifrit_Suc[of P R ] assms by auto
  then consider  "\<forall>n \<le> card R. Ifrit_R P R n \<subset> Ifrit_R P R (Suc n)"
    | "\<exists>n \<le> card R. Ifrit_R P R n = Ifrit_R P R (Suc n)"
    using R sub finite
    by blast
  then show ?thesis
  proof (cases)
    case 1
    then have "\<forall>n \<le> card R. card (Ifrit_R P R n) < card (Ifrit_R P R (Suc n))"
      by (simp add: psubset_card_mono finite)
    then have "\<forall>n \<le> card R.(\<exists>m. n < card (Ifrit_R P R m))"
      using inc_fun[of "card R" "\<lambda>m. card (Ifrit_R P R m)"] by auto
    then obtain n where "card R < card (Ifrit_R P R n)"
      by blast
    moreover have "\<not> ((Ifrit_R P R n) \<subseteq> R)"
      using calculation R card_mono leD by auto
    then show ?thesis
      using sub by blast
  next
    case 2
    then show ?thesis by blast
  qed
qed

lemma Ifrit_n_trans:
  assumes "Ifrit_R P R n = Ifrit_R P R (Suc n)"
    and R: "finite R"
    and P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
  shows "Ifrit_R P R (Suc n) = Ifrit_R P R (Suc (Suc n))"
proof (rule ccontr)
  assume "Ifrit_R P R (Suc n) \<noteq> Ifrit_R P R (Suc (Suc n))"
  moreover have "Ifrit_R P R (Suc n) \<subseteq> Ifrit_R P R (Suc (Suc n))"
    by (simp add: Collect_mono_iff Ifrit_R_def Ifrit_Suc)
  ultimately have "Ifrit_R P R (Suc n) \<subset> Ifrit_R P R (Suc (Suc n))"
    by blast
  then obtain l r cs  where rl: "((l,r),cs) \<in> Ifrit_R P R (Suc (Suc n))"
    and wrong: "((l,r),cs) \<notin> Ifrit_R P R (Suc n)"
    by auto
  have "P (Ifrit_R P R (Suc n)) cs"
      using Ifrit_conds[of P R "Suc n" l r cs] rl unfolding Ifrit_R_def using P P_mono R
      by blast
  then have cs_P: "P (Ifrit_R P R n) cs"
    using assms(1) by auto
  have "((l,r),cs) \<in> Ifrit_R P R (Suc n)"
  proof-
    have "((l,r),cs) \<in> R"
      using rl Ifrit_R_subset by auto
    then have "Ifrit P R (Suc n) ((l,r),cs)"
      using Ifrit.intros[of l r cs R "Ifrit_R P R n" P n]
        Ifrit_R_subset[of _ P R n] cs_P
      unfolding Ifrit_R_def
      by blast
    then show ?thesis
      unfolding Ifrit_R_def by simp
  qed
  then show "False"
    using wrong by blast
qed

lemma Ifrit_n_all':
  fixes m :: nat
  assumes "Ifrit_R P R n = Ifrit_R P R (Suc n)"
    and R: "finite R"
    and P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
  shows "Ifrit_R P R n = Ifrit_R P R (n + m) \<and> Ifrit_R P R (n + m) = Ifrit_R P R (n + Suc m)"
  using assms
proof (induction m arbitrary: n)
  case 0
  then show ?case
    by (simp add: "0.prems")
next
  case (Suc m)
  then have n_Suc_m: "Ifrit_R P R n = Ifrit_R P R (n + m) \<and> Ifrit_R P R (n + m) = Ifrit_R P R (n + Suc m)"
    by blast
  then have n_m_Suc: "Ifrit_R P R n = Ifrit_R P R (n + m) \<and> Ifrit_R P R (n + m) = Ifrit_R P R (Suc (n + m))"
    by simp
  have Suc_m: "Ifrit_R P R n = Ifrit_R P R (n + Suc m)"
    and "Ifrit_R P R (Suc (n + m)) = Ifrit_R P R (Suc (Suc (n + m)))"
  proof-
    show "Ifrit_R P R n = Ifrit_R P R (n + Suc m)"
      using n_Suc_m by blast
  next
    show "Ifrit_R P R (Suc (n + m)) = Ifrit_R P R (Suc (Suc (n + m)))"
      using Ifrit_n_trans[of P R "n + m"] n_m_Suc R P P_mono by blast
  qed
  then show ?case
    by auto
qed

lemma Ifrit_n_all:
  fixes m :: nat
  assumes "Ifrit_R P R n = Ifrit_R P R (Suc n)"
    and m: "n \<le> m"
    and R: "finite R"
    and P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
  shows "Ifrit_R P R n = Ifrit_R P R (m)"
proof-
  obtain k where k: "m = n + k" using m
    using le_Suc_ex by blast
  then show ?thesis
    using assms Ifrit_n_all'[of P R n k] R by blast
qed


definition "Ifrit_R_full P R = Ifrit_R P R (card R)"

lemma Ifrit_full:
  assumes R: "finite R"
    and P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
  shows "Ifrit_R P R n \<subseteq> Ifrit_R_full P R"
proof-
  obtain m where m_card: "m \<le> card R" and m: "Ifrit_R P R m = Ifrit_R P R (Suc m)"
    using Ifrit_n[of R P ] R by auto
  have "\<forall> n \<ge> m. Ifrit_R P R m = Ifrit_R P R n"
  proof
    fix n
    show "m \<le> n \<longrightarrow> Ifrit_R P R m = Ifrit_R P R n"
    proof
      assume "m \<le> n"
      then show "Ifrit_R P R m = Ifrit_R P R n"
        using Ifrit_n_all[of P R m] R P P_mono m by blast
    qed
  qed
  then show ?thesis
    using Ifrit_R_full_def
    by (metis Ifrit_R_def Ifrit_Suc m_card lift_Suc_mono_le mem_Collect_eq nat_le_linear subst_conjugate_pt.subsetCI)
qed

lemma Ifrit_iff:
  assumes P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and R: "finite R"
  shows "(cstep_n R n) = (cstep_n (Ifrit_R P R n) n)"
proof
  show "cstep_n R n \<subseteq> cstep_n (Ifrit_R P R n) n"
    using Ifrit assms
    by (metis (mono_tags, lifting) subrelI)
next
  have "Ifrit_R P R n \<subseteq> R"
    using Ifrit_R_subset by blast
  then show "cstep_n (Ifrit_R P R n) n \<subseteq> cstep_n R n"
    by (simp add: cstep_n_subset)
qed

lemma Ifrit_full_iff:
  assumes P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    and R: "finite R"
  shows "(cstep R) = (cstep (Ifrit_R_full P R))"
proof
  show "cstep R \<subseteq> cstep (Ifrit_R_full P R)"
  proof
    fix x y
    obtain n where "(x, y) \<in> cstep R \<Longrightarrow> (x, y) \<in> cstep_n R n"
      by (simp add: cstep_iff) blast
    then have "(x, y) \<in> cstep R \<Longrightarrow> (x, y) \<in> cstep_n (Ifrit_R P R n) n"
      using assms Ifrit_iff[of P R n] by blast
    then have "(x, y) \<in> cstep R \<Longrightarrow> (x, y) \<in> cstep (Ifrit_R P R n)"
      by (auto simp: cstep_iff)
    moreover have "Ifrit_R P R n \<subseteq> Ifrit_R_full P R"
      using assms Ifrit_full[of R P n] by blast
    ultimately show "(x, y) \<in> cstep R \<Longrightarrow> (x, y) \<in> cstep (Ifrit_R_full P R)"
      using cstep_subset by auto
  qed
next
  have "Ifrit_R_full P R \<subseteq> R"
    using Ifrit_R_subset Ifrit_R_full_def by blast
  then show "cstep (Ifrit_R_full P R) \<subseteq> cstep R"
    by (simp add: cstep_subset)
qed

subsection \<open>Combining P\<close>

lemma P_and:
  assumes P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and S: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> S R cs"
  shows "finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs \<and> S R cs"
  using assms by blast

lemma P_and_mono:
  assumes  P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    and  S_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> S R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> S R' cs"
  shows  "\<And>R R' n cs. finite R' \<Longrightarrow> (P R cs \<and> S R cs) \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs \<and> S R' cs"
  using assms by blast


subsection \<open>Gtcap as P\<close>

lemma match_mono:
  assumes "equiv_class C \<subseteq> equiv_class C'"
  shows "Ground_Context.match C t \<Longrightarrow> Ground_Context.match C' t"
  using assms by (auto simp: Ground_Context.match_def)

lemma tcap_mono:
  assumes "R \<subseteq> S"
  shows "equiv_class (tcap R t) \<subseteq> equiv_class (tcap S t)"
  using assms
  apply (induct t)
   apply (auto simp: Let_def Ground_Context.match_def)
   apply (smt fst_conv nth_mem subsetD)
  using nth_mem by blast

lemma Tc_mono:
  assumes "R \<subseteq> S"
  shows "Ground_Context.match (tcap R t) u \<Longrightarrow> Ground_Context.match (tcap S t) u"
  using assms and match_mono and tcap_mono by blast

lemma GT1_mono:
  assumes "R \<subseteq> S"
  shows "GT1 R \<subseteq> GT1 S"
  unfolding GT1_def
  using assms by auto

lemma GT_mono:
  assumes "R \<subseteq> S"
  shows "GT R \<subseteq> GT S"
  unfolding GT_def using GT1_mono
  by (auto split: term.splits simp: GT1_mono assms trancl_mono )

definition "P_gt (S::('f, 'v) crule set) (s::('f, 'v) term) (t::('f, 'v) term)
  = (case (s,t) of
    (Fun f ss, Fun g ts) \<Rightarrow> (let R = Ru S in
     (Ground_Context.match (tcap R s) t) \<and>
    ((f, length ss) = (g, length ts) \<or>
    (s,t) \<in> (GT R \<inter> {(s, t). \<exists>(l, r)\<in>R. Ground_Context.match (tcap R s) l})))
  | _ \<Rightarrow> True)"

lemma P_gt:
  assumes R: "finite R"
    and cstep: "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
  shows "P_gt R s t"
proof-
  obtain S where S: "S = Ru R" by blast
  then have rstep: "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep S)\<^sup>*"
    using cstep_imp_Ru_step cstep csteps_n_imp_csteps rtrancl_mono_mp
    by blast
  consider "P_gt R s t = True"
    | "\<not> (Ground_Context.match (tcap S s) t)"
    | f ss g ts where "(s,t) = (Fun f ss, Fun g ts) \<and> \<not>((f, length ss) = (g, length ts)
    \<or> (s,t) \<in> (GT S \<inter> {(s, t). \<exists>(l, r)\<in>S. Ground_Context.match (tcap S s) l}))"
  proof (cases "P_gt R s t")
    case True
    then show ?thesis
      by (simp add: that(1))
  next
    case False
    then obtain f ss g ts where st: "(s,t) = (Fun f ss, Fun g ts)"
      unfolding P_gt_def by (auto split:term.splits)
    then have "\<not>((Ground_Context.match (tcap S s) t) \<and>
    ((f, length ss) = (g, length ts) \<or>
    (s,t) \<in> (GT S \<inter> {(s, t). \<exists>(l, r)\<in>S. Ground_Context.match (tcap S s) l})))"
      using False unfolding P_gt_def S
      by force
    then show ?thesis
      using that(2,3)
      using st by blast
  qed
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis
      by blast
  next
    case 2
    then have "False"
      using rstep
      using match_tcap_sound by blast
    then show ?thesis
      by blast
  next
    case 3
    then have "rd_gtcap.S_op S s t"
      using rstep rd_gtcap.nonreach[of _ _ _ _ "S" \<sigma> \<sigma>]
      by blast
    then show ?thesis
      using 3 S by auto
  qed
qed

lemma P_gt_mono:
  assumes S: "finite S"
    and subset: "R \<subseteq> S"
    and P: "P_gt R s t"
  shows "P_gt S s t"
proof-
  have Ru: "Ru R \<subseteq> Ru S"
    using subset unfolding Ru_def
    by blast
  consider f ss g ts where "(s,t) = (Fun f ss, Fun g ts) \<and> (f, length ss) = (g, length ts) \<and> (Ground_Context.match (tcap (Ru R) s) t)"
    | f ss g ts where "(s,t) = (Fun f ss, Fun g ts) \<and> (Ground_Context.match (tcap (Ru R) s) t) \<and> (let R' = Ru R in
    (s,t) \<in> (GT R' \<inter> {(s, t). \<exists>(l, r)\<in>R'. Ground_Context.match (tcap R' s) l}))"
    | "is_Var s" | "is_Var t"
    using P unfolding P_gt_def by (auto split: term.splits simp: Let_def)
  then show ?thesis
  proof(cases)
    case 1
    moreover have "Ground_Context.match (tcap (Ru S) s) t"
      using 1 subset Tc_mono[of "Ru R" "Ru S" s t] Ru by auto
    ultimately show ?thesis
      using P_gt_def[of S s t] by auto
  next
    case 2
    have tcap: "Ground_Context.match (tcap (Ru S) s) t"
      using 2 subset Tc_mono[of "Ru R" "Ru S" s t] Ru by auto
    have elem: "(s, t)
          \<in> GT (Ru R) \<inter>
             {(s, t).
              \<exists>(l, r)\<in>(Ru R). Ground_Context.match (tcap (Ru R) s) l}"
      using 2 by meson
    then have "(s,t) \<in> GT (Ru R)"
      by blast
    then have gt: "(s,t) \<in> GT (Ru S)"
      using Ru GT_mono by blast
    have "(s,t) \<in> {(s, t). \<exists>(l, r)\<in>(Ru R). Ground_Context.match (tcap (Ru R) s) l}"
      using 2 by (meson IntE)
    then have "(s,t) \<in> {(s, t). \<exists>(l, r)\<in>(Ru S). Ground_Context.match (tcap (Ru S) s) l}"
      using Ru Tc_mono[of "Ru R" "Ru S" s] by blast
    moreover obtain f ss g ts where "(s, t) = (Fun f ss, Fun g ts)" using 2 by auto
    ultimately show ?thesis
      using gt P_gt_def[of S s t] tcap by auto
  next
    case 3
    then show ?thesis
      using P_gt_def[of S s t] by auto
  next
    case 4
    then show ?thesis
      using P_gt_def[of S s t] by (auto split: term.splits)
  qed
qed

definition "P_gt_cs (S::('f, 'v) crule set) (cs::(('f, 'v) term \<times> ('f, 'v) term) list)
  = (\<forall>(s,t) \<in> set cs. P_gt S s t)"

lemma P_gt_cs:
  assumes R: "finite R"
    and csteps: "\<And>s t. (s,t) \<in> set cs \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
  shows "P_gt_cs R cs"
  using P_gt P_gt_cs_def
  by (metis R ballI2 csteps)

lemma P_gt_cs_mono:
  assumes S: "finite S"
    and P: "P_gt_cs R cs"
    and subset: "R \<subseteq> S"
  shows "P_gt_cs S cs"
  using P_gt_mono
  by (metis (no_types, lifting) P P_gt_cs_def S case_prodD case_prodI2 subset)


subsection \<open>Joinability of conditions as P\<close>

definition "P_Join (R::('f, 'v) crule set) (cs::(('f, 'v) term \<times> ('f, 'v) term) list)
  = (\<forall>(s,u) \<in> set cs. \<forall>(t,v) \<in> set cs. (s \<noteq> t \<and> u = v)
  \<longrightarrow> Ground_Context.unifiable (tcap (Ru R) s) (tcap (Ru R) t))"

lemma P_Join:
  assumes R: "finite R"
    and csteps: "\<And>s t. (s,t) \<in> set cs \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
  shows "P_Join R cs"
proof (rule ccontr)
  assume "\<not> P_Join R cs"
  then obtain s t u v where su: "(s,u) \<in> set cs" and tv: "(t,v) \<in> set cs" and stuv: "(s \<noteq> t \<and> u = v)" and "\<not> Ground_Context.unifiable (tcap (Ru R) s) (tcap (Ru R) t)"
    unfolding P_Join_def by auto
  then have "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (Ru R))\<^sup>\<down>)"
    by (auto simp: join_imp_unifiable_tcaps [of s _ t])
  then have "\<nexists>\<sigma> n. conds_n_sat R n cs \<sigma>"
    using csteps_n_imp_csteps [of _ _ "R"]  cstep_imp_Ru_step [THEN rtrancl_mono, of "R"] su tv stuv
    by (blast dest: conds_n_satD)
  then show "False"
    using csteps
    by (metis (no_types, lifting) case_prodI2 conds_n_sat_iff)
qed

lemma unif_mono:
  assumes "equiv_class C \<subseteq> equiv_class C'"
    and "equiv_class D \<subseteq> equiv_class D'"
  shows "Ground_Context.unifiable C D \<Longrightarrow> Ground_Context.unifiable C' D'"
  using assms by (auto simp: Ground_Context.unifiable_def)

lemma gc_unif_mono:
  assumes "R \<subseteq> S"
  shows "Ground_Context.unifiable (tcap R t) (tcap R u) \<Longrightarrow> Ground_Context.unifiable (tcap S t) (tcap S u)"
  using assms and unif_mono and tcap_mono by blast

lemma P_Join_mono:
  assumes S: "finite S"
    and P: "P_Join R cs"
    and subset: "R \<subseteq> S"
  shows "P_Join S cs"
proof-
  have Ru: "Ru R \<subseteq> Ru S"
    unfolding Ru_def using subset by blast
  then show ?thesis
    using P
    unfolding P_Join_def
    using gc_unif_mono[of "Ru R" "Ru S"] by blast
qed

subsection \<open>combination of previous methods\<close>

definition "P_full (R::('f, 'v) crule set) (cs::(('f, 'v) term \<times> ('f, 'v) term) list)
  = (P_gt_cs R cs \<and> P_Join R cs)"

lemma P_full:
  assumes R: "finite R"
    and csteps: "\<And>s t. (s,t) \<in> set cs \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
  shows "P_full R cs"
  using assms P_full_def P_gt_cs P_Join P_and by blast

lemma P_full_mono:
  assumes S: "finite S"
    and subset: "R \<subseteq> S"
    and P: "P_full R cs"
  shows "P_full S cs"
  using assms P_full_def
    P_gt_cs_mono[of S R cs]
    P_Join_mono[of S R cs]
    P_and_mono[of P_gt_cs P_Join S R cs]
  by blast

end