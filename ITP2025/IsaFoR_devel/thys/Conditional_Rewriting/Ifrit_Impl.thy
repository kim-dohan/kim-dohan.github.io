(*
Author:  Florian Meßner <florian.messner@outlook.com> (2020)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Ifrit - Inductive Feasible Rule InTroduction - Implementation\<close>

theory Ifrit_Impl
  imports
    Ifrit
begin

fun Ifrit_impl
  where
    "Ifrit_impl P R (Suc n) = (filter (\<lambda>(rl, cs). P (Ifrit_impl P R n) cs) R)"
  | "Ifrit_impl P R 0 = []"

definition "Ifrit_impl_full P R = Ifrit_impl P R (length R)"

print_theorems

lemma Ifrit_impl:
  assumes "Ifrit P (set R) n rl"
    and P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    and P': "\<And>R R' cs. P R cs \<Longrightarrow> R \<subseteq> set R' \<Longrightarrow> P' R' cs"
  shows "rl \<in> set (Ifrit_impl P' R n)"
  using assms(1)
proof (induction n arbitrary: rl)
  case 0
  then show ?case
    using Ifrit.cases by blast
next
  case (Suc n)
  then obtain l r cs where rl:"rl = ((l,r),cs)"
    using crule_cases by blast
  then have "P (Ifrit_R P (set R) n) cs"
    using Ifrit_conds[of P "set R" n l r cs ] rl Suc P P_mono by blast
  then have "P' (Ifrit_impl P' R n) cs"
    by (metis (no_types, opaque_lifting) Ifrit_R_def P' Suc.IH mem_Collect_eq subset_eq)
  then show ?case
    using Ifrit_impl.simps(1)[of P' R n]
    using Ifrit_subset Suc.prems rl by fastforce
qed

lemma Ifrit_impl_full:
  assumes ass: "Ifrit P (set R) n rl"
  assumes P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    and P': "\<And>R R' cs. P R cs \<Longrightarrow> R \<subseteq> set R' \<Longrightarrow> P' R' cs"
  shows "rl \<in> set (Ifrit_impl_full P' R)"
proof-
  have R: "finite (set R)" by auto
  have "rl \<in> Ifrit_R P (set R) n"
    using ass Ifrit_R_def by blast
  then have "rl \<in> Ifrit_R_full P (set R)"
    using Ifrit_full[of "set R" P n] R P P_mono
    by blast
  then have "rl \<in> Ifrit_R P (set R) (card (set R))"
    using Ifrit_R_full_def by blast
  moreover have "Ifrit_R P (set R) (card (set R)) = Ifrit_R P (set R) (Suc (card (set R)))"
  proof-
    have "Ifrit_R P (set R) (card (set R)) \<subseteq> Ifrit_R P (set R) (Suc (card (set R)))"
      unfolding Ifrit_R_def using Ifrit_Suc
      by auto
    moreover have "Ifrit_R P (set R) (Suc (card (set R))) \<subseteq> Ifrit_R P (set R) (card (set R))"
      using Ifrit_full[of "set R" P "Suc (card (set R))"] P P_mono R unfolding Ifrit_R_full_def
      by blast
    ultimately show ?thesis
      by blast
  qed
  moreover have "card (set R) \<le> length R"
    using card_length by blast
  ultimately have "rl \<in> Ifrit_R P (set R) (length R)"
    using Ifrit_n_all[of P "set R" "card (set R)" "length R"]
      P P_mono by blast
  then have "Ifrit P (set R) (length R) rl"
    using Ifrit_R_R'[of _ P "set R" "length R" rl]
    by simp
  then show ?thesis
    unfolding Ifrit_impl_full_def
    using Ifrit_impl[of P R "length R" rl P'] P P_mono P'
    by simp blast
qed


lemma Ifrit_impl_sound:
  assumes "(s, t) \<in> (cstep (set R))"
  assumes P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    and P': "\<And>R R' cs. P R cs \<Longrightarrow> R \<subseteq> set R' \<Longrightarrow> P' R' cs"
  shows "(s, t) \<in> (cstep (set (Ifrit_impl_full P' R)))"
proof-
  obtain n where n: "(s, t) \<in> (cstep_n (set R) n)"
    using assms(1) cstep_iff by blast
  then have "(s, t) \<in> cstep_n (Ifrit_R P (set R) n) n"
    using assms Ifrit[of s t "set R" n P]
    by blast
  moreover have "Ifrit_R P (set R) n \<subseteq> set (Ifrit_impl_full P' R)"
  proof
    fix x y
    have "Ifrit P (set R) n (x,y) \<Longrightarrow> (x, y) \<in> set (Ifrit_impl_full P' R)"
      using Ifrit_impl_full[of P R n "(x,y)" P'] P P_mono P'
        calculation by simp blast
    then show "(x, y) \<in> Ifrit_R P (set R) n \<Longrightarrow> (x, y) \<in> set (Ifrit_impl_full P' R)"
      using Ifrit_R_def by auto
  qed
  ultimately have "(s, t) \<in> cstep_n (set (Ifrit_impl_full P' R)) n"
    using cstep_n_subset by blast
  then show ?thesis
    using cstep_iff by blast
qed

lemma Ifrit_impl_iff:
  assumes P: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    and P_mono: "\<And>R R' n cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    and P': "\<And>R R' cs. P R cs \<Longrightarrow> R \<subseteq> set R' \<Longrightarrow> P' R' cs"
  shows "(cstep (set R)) = (cstep (set (Ifrit_impl_full P' R)))"
proof
  show "cstep (set R) \<subseteq> cstep (set (Ifrit_impl_full P' R))"
  proof
    fix x y
    show "(x,y) \<in> cstep (set R) \<Longrightarrow> (x,y) \<in> cstep (set (Ifrit_impl_full P' R))"
      using Ifrit_impl_sound[of x y R P P'] assms by simp blast
  qed
next
  have "set (Ifrit_impl_full P' R) \<subseteq> set R"
    unfolding Ifrit_impl_full_def
    by (metis (no_types, lifting) Ifrit_impl.elims length_greater_0_conv mem_Collect_eq neq0_conv set_filter subsetI)
  then show "cstep (set (Ifrit_impl_full P' R)) \<subseteq> cstep (set R)"
    using cstep_subset by auto
qed

subsection \<open>Alternative Lemma for proving with focus on P_impl\<close>

definition "(mk_P_Set P' = (\<lambda>R cs. P' (sorted_list_of_set R) cs))"

lemma Ifrit_impl_sound_P':
  fixes R :: "('f::compare_order, 'v::compare_order) crule list" and s t :: "('f, 'v) term"
  assumes "(s, t) \<in> (cstep (set R))"
  assumes P': "\<And>R R' n cs \<sigma>. (\<And>s t. (s,t) \<in> set cs \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> R \<subseteq> set R' \<Longrightarrow> P' R' cs"
    and P'_subset: "\<And>R R' cs. P' R cs \<Longrightarrow> set R \<subseteq> set R' \<Longrightarrow> P' R' cs"
  shows "(s, t) \<in> (cstep (set (Ifrit_impl_full P' R)))"
proof-
  obtain P where P: "P = mk_P_Set P'" by blast
  have P_to_P': "\<And>R R' cs. P R cs \<Longrightarrow> R \<subseteq> set R' \<Longrightarrow> P' R' cs"
    unfolding P mk_P_Set_def
    by (simp add: P'_subset finite_subset)
  moreover have P_sound: "\<And>R n cs \<sigma>. finite R \<Longrightarrow> (\<And>s t. (s,t) \<in> set cs \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*) \<Longrightarrow> P R cs"
    unfolding P mk_P_Set_def
    using P' set_sorted_list_of_set by blast
  moreover have P_subset: "\<And>R R' cs. finite R' \<Longrightarrow> P R cs \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> P R' cs"
    unfolding P mk_P_Set_def
    using P'_subset
    by (simp add: finite_subset)
  ultimately show ?thesis
    using assms Ifrit_impl_sound[of s t R P P']
    by blast
qed

subsection \<open>Combining P\<close>

lemma P_and_impl:
  assumes  P': "\<And>R S cs. P R cs \<Longrightarrow> R \<subseteq> set S \<Longrightarrow> P' S cs"
    and  Q': "\<And>R S cs. Q R cs \<Longrightarrow> R \<subseteq> set S \<Longrightarrow> Q' S cs"
    and "R \<subseteq> set S"
  shows "P R cs \<and> Q R cs \<Longrightarrow> P' S cs \<and> Q' S cs"
  using assms by blast

subsection \<open>Gtcap as P\<close>

definition "GT_impl R s t = (is_Var s \<or> is_Var t
  \<or> mk_gt_fun R (root s) (root t) \<or> mk_gt_fun R (root s) None
  \<or> mk_gt_fun R None (root t) \<or> mk_gt_fun R None None)"


definition  "P_gt_impl S s t =
(case (s,t) of
  (Fun f ss, Fun g ts) \<Rightarrow> (let R = (map fst S) in
   (Ground_Context.match (tcapI R s) t) \<and>
    ((f, length ss) = (g, length ts) \<or>
    (GT_impl R s t \<and> (\<exists>(l, r)\<in> set R. Ground_Context.match (tcapI R s) l))))
  | _ \<Rightarrow> True)"

lemma GT_impl:
  "(s,t) \<in> GT (set R) \<longleftrightarrow> GT_impl R s t"
  using GT_set_iff GT_impl_def by blast

lemma P_gt_impl:
  assumes P: "P_gt R s t"
    and S: "R \<subseteq> set S"
  shows "P_gt_impl S s t"
proof-
  have Ru: "Ru R \<subseteq> Ru (set S)" using S
    by (simp add: Ru_def image_mono)
  have Ru': "Ru R \<subseteq> set (map fst S)"
    unfolding Ru_def using S by auto
  consider f ss g ts where "(s,t) = (Fun f ss, Fun g ts) \<and> (f, length ss) = (g, length ts) \<and> (Ground_Context.match (tcap (Ru R) s) t)"
    | f ss g ts where "(s,t) = (Fun f ss, Fun g ts) \<and> (Ground_Context.match (tcap (Ru R) s) t) \<and>
    ((s,t) \<in> (GT (Ru R) \<inter> {(s, t). \<exists>(l, r)\<in>(Ru R). Ground_Context.match (tcap (Ru R) s) l}))"
    | "is_Var s" | "is_Var t"
    using P unfolding P_gt_def by (auto split: term.splits simp: Let_def)
  then show ?thesis
  proof(cases)
    case 1
    moreover have "(Ground_Context.match (tcapI (map fst S) s) t)"
      using 1 tcapI_sound[of "map fst S"] Ru' Tc_mono[of "Ru R" "set (map fst S)"] by fastforce
    ultimately show ?thesis
      using P_gt_impl_def[of S s t] by auto
  next
    case 2
    have tcap: "(Ground_Context.match (tcapI (map fst S) s) t)"
       using 2 tcapI_sound[of "map fst S"] Ru' Tc_mono[of "Ru R" "set (map fst S)"] by fastforce
    have elem: "(s, t) \<in> GT (Ru R) \<inter> {(s, t). \<exists>(l, r)\<in>Ru R. Ground_Context.match (tcap (Ru R) s) l}"
      using 2 by meson
    then have "(s, t) \<in> GT (Ru R)" by blast
    then have "(s, t) \<in> GT (Ru (set S))" using Ru GT_mono[of "Ru R" "Ru (set S)"]
      by auto
    then have gt: "GT_impl (map fst S) s t"
      using GT_impl
      by (metis (no_types, opaque_lifting) Ru_def set_map)
    from elem have "\<exists>(l, r)\<in>Ru R. Ground_Context.match (tcap (Ru R) s) l" by blast
    then have "\<exists>(l, r)\<in>Ru (set S). Ground_Context.match (tcap (Ru (set S)) s) l"
      using Ru Tc_mono[of "Ru R" "Ru (set S)" s] by blast
    then have "\<exists>(l, r)\<in> set (map fst S). Ground_Context.match (tcapI (map fst S) s) l"
      by (simp add: Ru_def)
    then show ?thesis
      using P_gt_impl_def[of S s t] gt tcap 2 by simp
  next
    case 3
    then show ?thesis
      using P_gt_impl_def[of S s t] by auto
  next
    case 4
    then show ?thesis
      using P_gt_impl_def[of S s t] by (auto split: term.splits)
  qed
qed

definition "P_gt_cs_impl (S::('f, 'v) crule list) (cs::(('f, 'v) term \<times> ('f, 'v) term) list)
  = (\<forall>(s,t) \<in> set cs. P_gt_impl S s t)"

lemma P_gt_cs_impl:
  assumes P: "P_gt_cs R cs"
    and S: "R \<subseteq> set S"
  shows "P_gt_cs_impl S cs"
  using assms unfolding P_gt_cs_impl_def P_gt_cs_def
  using P_gt_impl by blast

subsection \<open>Joinability of conditions as P\<close>

definition "P_Join_impl (R::('f, 'v) crule list) (cs::(('f, 'v) term \<times> ('f, 'v) term) list)
  = (\<forall>(s,u) \<in> set cs. \<forall>(t,v) \<in> set cs. (s \<noteq> t \<and> u = v)
  \<longrightarrow> Ground_Context.unifiable (tcapI (map fst R) s) (tcapI (map fst R) t))"

lemma P_Join_impl:
assumes P: "P_Join R cs"
    and S: "R \<subseteq> set S"
  shows "P_Join_impl S cs"
proof-
  have subset: "(fst ` R) \<subseteq> set (map fst S)"
    using S by auto
  have P': "\<And> s u. (s, u)\<in>set cs \<Longrightarrow>
     (\<And> t v. (t, v)\<in>set cs \<Longrightarrow>
        s \<noteq> t \<and> u = v \<longrightarrow>
        Ground_Context.unifiable (tcap (fst ` R) s)
         (tcap (fst ` R) t))"
    using P
    unfolding P_Join_impl_def P_Join_def Ru_def tcapI_sound
    by auto
  show ?thesis
    unfolding P_Join_impl_def P_Join_def tcapI_sound Ru_def
  proof
    fix s u
    show "(s, u) \<in> set cs \<Longrightarrow>
           \<forall>(t, v)\<in>set cs.
              s \<noteq> t \<and> u = v \<longrightarrow>
              Ground_Context.unifiable (tcap (set (map fst S)) s)
               (tcap (set (map fst S)) t)"
    proof
      fix t v
      show "(s, u) \<in> set cs \<Longrightarrow>
           (t, v) \<in> set cs \<Longrightarrow>
           s \<noteq> t \<and> u = v \<longrightarrow>
           Ground_Context.unifiable (tcap (set (map fst S)) s)
            (tcap (set (map fst S)) t)"
        using subset unif_mono
          P'[of s u t v] tcap_mono[of "fst ` R" "set (map fst S)"]
        by blast
      qed
    qed
qed

subsection \<open>combination of previous methods\<close>

definition "P_full_impl (R::('f, 'v) crule list) (cs::(('f, 'v) term \<times> ('f, 'v) term) list)
  = (P_gt_cs_impl R cs \<and> P_Join_impl R cs)"

lemma P_full_impl:
assumes P: "P_full R cs"
    and S: "R \<subseteq> set S"
  shows "P_full_impl S cs"
  using assms unfolding P_full_def P_full_impl_def
  using P_and_impl[of P_Join P_Join_impl P_gt_cs P_gt_cs_impl R S cs]
    P_Join_impl[of R cs S] P_gt_cs_impl[of R cs S]
  by simp

subsection \<open>Executable Ifrit Implementations\<close>

definition "Ifrit_gt_impl R = Ifrit_impl_full P_gt_cs_impl R"
definition "Ifrit_full_impl R = Ifrit_impl_full P_full_impl R"

lemma Ifrit_impl_sound_gt:
  fixes R :: "('f::compare_order, 'v::compare_order) crule list" and s t :: "('f, 'v) term"
  assumes "(s, t) \<in> (cstep (set R))"
  shows "(s, t) \<in> (cstep (set (Ifrit_gt_impl R)))"
  unfolding Ifrit_gt_impl_def
  using assms P_gt_cs  P_gt_cs_impl P_gt_cs_mono
    Ifrit_impl_sound[of s t R P_gt_cs P_gt_cs_impl]
  by metis

lemma Ifrit_full_impl_sound:
  fixes R :: "('f::compare_order, 'v::compare_order) crule list" and s t :: "('f, 'v) term"
  shows "(cstep (set R)) = (cstep (set (Ifrit_full_impl R)))"
  unfolding Ifrit_full_impl_def
  using P_full  P_full_impl P_full_mono Ifrit_impl_iff[of P_full P_full_impl R]
  by metis

definition "check_Ifrit_rules R S = (set (Ifrit_full_impl R) \<subseteq> set S)"

lemma check_Ifrit_rules:
  fixes R :: "('f::compare_order, 'v::compare_order) crule list" and s t :: "('f, 'v) term"
  assumes "check_Ifrit_rules R S"
  shows "cstep (set R) \<subseteq> cstep (set S)"
  using assms Ifrit_full_impl_sound[of R] cstep_subset
  unfolding check_Ifrit_rules_def
  by simp

definition "check_Ifrit_rules_iff R S = ((set S \<subseteq> set R) \<and> (set (Ifrit_full_impl R) \<subseteq> set S))"

lemma check_Ifrit_rules_iff:
  fixes R :: "('f::compare_order, 'v::compare_order) crule list"
  assumes "check_Ifrit_rules_iff R S"
  shows "cstep (set R) = cstep (set S)"
  using assms
  unfolding check_Ifrit_rules_iff_def
  using Ifrit_full_impl_sound[of R]
  using cstep_subset by auto

end