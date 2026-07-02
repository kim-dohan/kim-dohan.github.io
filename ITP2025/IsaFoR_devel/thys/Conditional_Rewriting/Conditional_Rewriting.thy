(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2017)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2014, 2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Conditional_Rewriting
  imports
    First_Order_Rewriting.Trs
    Ord.Reduction_Pair
    TRS.Renaming_Interpretations
    Auxx.Util
begin

type_synonym ('f, 'v) condition = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) crule = "('f, 'v) rule \<times> ('f, 'v) condition list"
type_synonym ('f, 'v) ctrs = "('f, 'v) crule set"

text \<open>A conditional rewrite step of level @{term n}.\<close>
fun cstep_n :: "('f, 'v) ctrs \<Rightarrow> nat \<Rightarrow> ('f, 'v) term rel"
where
  "cstep_n R 0 = {}" |
  cstep_n_Suc: "cstep_n R (Suc n) =
    {(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) | C l r \<sigma> cs.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*)}"

definition conds_n_sat
where
  conds_n_sat_iff: "conds_n_sat R n cs \<sigma> \<longleftrightarrow> (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*)"

lemma conds_n_sat_0 [simp]: "conds_n_sat R 0 c \<sigma> \<longleftrightarrow> (\<forall>(s, t)\<in>set c. s \<cdot> \<sigma> = t \<cdot> \<sigma>)"
  by (auto simp: conds_n_sat_iff)

lemma conds_n_satD:
  assumes "conds_n_sat R n cs \<sigma>" and "(s, t) \<in> set cs"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
using assms by (auto simp: conds_n_sat_iff)

lemma conds_n_sat_append [simp]:
  "conds_n_sat R n (cs @ ds) \<sigma> \<longleftrightarrow> conds_n_sat R n cs \<sigma> \<and> conds_n_sat R n ds \<sigma>"
by (auto simp add: conds_n_sat_iff)

lemma conds_n_sat_Nil [simp]:
  "conds_n_sat R n [] \<sigma>"
by (simp add: conds_n_sat_iff)

lemma conds_n_sat_singleton [simp]:
  "conds_n_sat R n [c] \<sigma> \<longleftrightarrow> (fst c \<cdot> \<sigma>, snd c \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
by (auto simp: conds_n_sat_iff)

lemma conds_n_sat_subst_list:
  "conds_n_sat R n (subst_list \<sigma> cs) \<tau> = conds_n_sat R n cs (\<sigma> \<circ>\<^sub>s \<tau>)"
by (auto simp: conds_n_sat_iff subst_set_def)

lemma cstep_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
    and "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  shows "(s, t) \<in> cstep_n R (Suc n)"
  using assms by (auto) blast

lemma cstep_nE:
  assumes "(s, t) \<in> cstep_n R n"
  obtains C l r \<sigma> cs n' where "((l, r), cs) \<in> R" and "n = Suc n'"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n')\<^sup>*"
    and "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  using assms by (cases n) auto

lemma cstep_n_SucE:
  assumes "(s, t) \<in> cstep_n R (Suc n)"
  obtains C l r \<sigma> cs where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
    and "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  using assms by auto

declare cstep_n_Suc [simp del]

lemma cstep_n_Suc_mono:
  "cstep_n R n \<subseteq> cstep_n R (Suc n)"
proof (induct n)
  case (Suc n)
  show ?case
    using rtrancl_mono [OF Suc] by (auto elim!: cstep_n_SucE intro!: cstep_n_SucI)
qed simp

lemma cstep_n_mono:
  assumes "i \<le> n"
  shows "cstep_n R i \<subseteq> cstep_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  then have "k = n - Suc i" and "Suc i \<le> n" by arith+
  from Suc.hyps(1) [OF this] show ?case using cstep_n_Suc_mono by blast
qed simp

lemma csteps_n_mono:
  assumes "m \<le> n"
  shows "(cstep_n R m)\<^sup>* \<subseteq> (cstep_n R n)\<^sup>*"
using assms by (intro rtrancl_mono cstep_n_mono)

lemma conds_n_sat_mono:
  "m \<le> n \<Longrightarrow> conds_n_sat R m cs \<sigma> \<Longrightarrow> conds_n_sat R n cs \<sigma>"
using csteps_n_mono [of m n R]
by (auto simp: conds_n_sat_iff)

lemma cstep_n_mono':
  "cstep_n R m \<subseteq> cstep_n R (m + k)"
  using cstep_n_mono [of "m" "m + k"] by simp

lemma cstep_n_ctxt:
  assumes "(s, t) \<in> cstep_n R n"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> cstep_n R n"
  using assms by (cases n) (auto elim!: cstep_n_SucE intro: cstep_n_SucI [where C = "C \<circ>\<^sub>c D" for D])

lemma all_ctxt_closed_csteps_n [intro]:
  "all_ctxt_closed UNIV ((cstep_n R n)\<^sup>*)"
by (rule trans_ctxt_imp_all_ctxt_closed)
   (auto simp: ctxt.closed_def elim!: ctxt.closure.cases intro: trans_rtrancl refl_rtrancl cstep_n_ctxt [THEN rtrancl_map])

lemma cstep_n_subst:
  assumes "(s, t) \<in> cstep_n R n"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> cstep_n R n"
using assms
proof (induct n arbitrary: s t \<sigma>)
  case (Suc n)
  from \<open>(s, t) \<in> cstep_n R (Suc n)\<close> obtain C l r cs \<tau>
    where "((l, r), cs) \<in> R" and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<tau>, t\<^sub>i \<cdot> \<tau>) \<in> (cstep_n R n)\<^sup>*"
    and "s = C\<langle>l \<cdot> \<tau>\<rangle>" and "t = C\<langle>r \<cdot> \<tau>\<rangle>" by (rule cstep_n_SucE)
  then show ?case
    using Suc.hyps and rtrancl_map [of "cstep_n R n" "\<lambda>t. t \<cdot> \<sigma>"]
    by (auto intro!: cstep_n_SucI [of l r cs R "\<tau> \<circ>\<^sub>s \<sigma>" _ _ "C \<cdot>\<^sub>c \<sigma>"])
qed simp

lemma cstep_n_ctxt_subst:
  assumes "(s, t) \<in> cstep_n R n"
  shows "(D \<langle>s \<cdot> \<sigma>\<rangle>, D \<langle>t \<cdot> \<sigma>\<rangle>) \<in> cstep_n R n"
  by (intro cstep_n_ctxt cstep_n_subst) fact

definition "cstep R = (\<Union>n. cstep_n R n)"

lemma cstep_iff:
  "(s, t) \<in> cstep R \<longleftrightarrow> (\<exists>n. (s, t) \<in> cstep_n R n)"
  by (auto simp: cstep_def)

definition conds_sat
where
  conds_sat_iff: "conds_sat R cs \<sigma> \<longleftrightarrow> (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*)"

lemma conds_sat_subst_list:
  "conds_sat R (subst_list \<sigma> cs) \<tau> = conds_sat R cs (\<sigma> \<circ>\<^sub>s \<tau>)"
by (auto simp: conds_sat_iff subst_set_def)

lemma conds_sat_append [simp]:
  "conds_sat R (cs\<^sub>1 @ cs\<^sub>2) \<sigma> \<longleftrightarrow> conds_sat R cs\<^sub>1 \<sigma> \<and> conds_sat R cs\<^sub>2 \<sigma>"
by (auto simp: conds_sat_iff)
  
lemma NF_cstep_subterm:
  assumes "t \<in> NF (cstep R)" and "t \<unrhd> s"
  shows "s \<in> NF (cstep R)"
proof (rule ccontr)  
  assume "\<not> ?thesis"
  then obtain u where "(s, u) \<in> cstep R" by auto
  from \<open>t \<unrhd> s\<close> obtain C where "t = C\<langle>s\<rangle>" by auto
  with \<open>(s, u) \<in> cstep R\<close> have "(t, C\<langle>u\<rangle>) \<in> cstep R"
    using cstep_iff cstep_n_ctxt by blast
  then have "t \<notin> NF (cstep R)" by auto
  with assms show False by simp
qed

lemma cstep_n_empty [simp]: "cstep_n {} n = {}"
  by (induct n) (auto simp: cstep_n_Suc)

lemma cstep_empty [simp]: "cstep {} = {}"
  unfolding cstep_def by simp

lemma csteps_n_trans:
  assumes "(s, t) \<in> (cstep_n R m)\<^sup>*" and "(t, u) \<in> (cstep_n R n)\<^sup>*"
  shows "(s, u) \<in> (cstep_n R (max m n))\<^sup>*"
  using assms
    and cstep_n_mono [of m "max m n" R, THEN rtrancl_mono]
    and cstep_n_mono [of n "max m n" R, THEN rtrancl_mono]
    by (auto dest!: set_mp)

lemma csteps_imp_csteps_n:
  assumes "(s, t) \<in> (cstep R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (cstep_n R n)\<^sup>*"
  using assms by (induct) (auto intro: csteps_n_trans simp: cstep_iff)

lemma cstep_n_imp_cstep:
  assumes "(s, t) \<in> cstep_n R n"
  shows "(s, t) \<in> cstep R"
using assms by (auto simp: cstep_iff)

lemma csteps_n_imp_csteps:
  assumes "(s, t) \<in> (cstep_n R n)\<^sup>*"
  shows "(s, t) \<in> (cstep R)\<^sup>*"
using assms by (induct; auto dest: cstep_n_imp_cstep)

lemma csteps_n_subset_csteps:
  "(cstep_n R n)\<^sup>* \<subseteq> (cstep R)\<^sup>*"
by (auto dest: csteps_n_imp_csteps)

lemma all_cstep_imp_cstep_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (cstep R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (cstep_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms by (auto intro: csteps_imp_csteps_n)
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using cstep_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * by blast
  then show ?thesis ..
qed

lemma cstepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
    and "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  shows "(s, t) \<in> cstep R"
proof -
  obtain n where "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
  using all_cstep_imp_cstep_n[of "length cs" "\<lambda>i. fst (cs ! i) \<cdot> \<sigma>" "\<lambda>i. snd (cs ! i) \<cdot> \<sigma>" R]
  and conds
    by (auto simp: all_set_conv_all_nth split_beta')
  then have "(s, t) \<in> cstep_n R (Suc n)" using assms by (intro cstep_n_SucI) (assumption)+
  then show ?thesis using cstep_iff by auto
qed

lemma cstepE [elim]:
  assumes "(s, t) \<in> cstep R"
    and imp: "\<And>C \<sigma> l r cs. \<lbrakk>((l, r), cs) \<in> R; \<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*; s = C\<langle>l \<cdot> \<sigma>\<rangle>; t = C\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  obtain n where *: "(s, t) \<in> cstep_n R n" using assms by (auto simp: cstep_iff)
  then show ?thesis
  proof (cases n)
    case (Suc n')
    have **: "(cstep_n R n')\<^sup>* \<subseteq> (cstep R)\<^sup>*" by (rule rtrancl_mono) (auto simp: cstep_iff)
    show ?thesis
      by (rule cstep_n_SucE [OF * [unfolded Suc]], rule imp, insert **) auto
  qed simp
qed

lemma Var_NF_cstep:
  assumes "\<forall> ((l, r), cs) \<in> R. is_Fun l"
  shows "Var x \<in> NF (cstep R)"
proof
  fix s
  show "(Var x, s) \<notin> cstep R"
  proof
    assume "(Var x, s) \<in> cstep R"
    then show "False" using assms supteq_var_imp_eq by fastforce
  qed
qed

lemma cstep_ctxt_closed:
  "ctxt.closed (cstep R)"
  by (rule ctxt.closedI) (auto intro: cstep_n_ctxt simp: cstep_iff)

lemma csteps_all_ctxt_closed[intro]: "all_ctxt_closed UNIV ((cstep r)^*)"
  using  cstep_ctxt_closed by (blast intro: trans_ctxt_imp_all_ctxt_closed trans_rtrancl refl_rtrancl)

lemma join_csteps_all_ctxt_closed: "all_ctxt_closed UNIV ((cstep r)\<^sup>\<down>)" 
proof -
 have var:"\<forall>x. (Var x, Var x) \<in> (cstep r)\<^sup>\<down>" by fast
 { fix f ss ts
   assume a:"length ts = length ss" "\<forall>i<length ts. (ts ! i, ss ! i) \<in> (cstep r)\<^sup>\<down>"
   from a(2) have "\<forall>i<length ts. \<exists> ui. (ts ! i, ui)\<in> (cstep r)^* \<and>  (ss ! i, ui) \<in> (cstep r)^*" by blast
   with choice have "\<exists>ui. \<forall>i<length ts. (ts ! i, ui i)\<in> (cstep r)^* \<and>  (ss ! i, ui i) \<in> (cstep r)^*" by meson
   then obtain ui where ui:"\<And>i. i<length ts \<Longrightarrow> (ts ! i, ui i)\<in> (cstep r)^* \<and>  (ss ! i, ui i) \<in> (cstep r)^*" by blast
   let ?us = "map ui [0 ..<length ts]"
   have lus: "length ts = length ?us" by simp
   from ui have uss:"\<And>j. j < length ts \<Longrightarrow> (ss ! j, ?us ! j) \<in> (cstep r)^*" by auto
   from ui have ust:"\<And>j. j < length ts \<Longrightarrow> (ts ! j, ?us ! j) \<in> (cstep r)^*" by auto
   note acc = conjunct1[OF csteps_all_ctxt_closed[unfolded all_ctxt_closed_def], rule_format]
   from acc[OF _ lus ust] have tseq:"(Fun f ts, Fun f ?us) \<in> (cstep r)\<^sup>*" by blast
   from acc[OF _ lus[unfolded a(1)] uss[unfolded a(1)]] a(1) have sseq:"(Fun f ss, Fun f ?us) \<in> (cstep r)\<^sup>*" by force
   with tseq have "(Fun f ts, Fun f ss) \<in> (cstep r)\<^sup>\<down>" by blast
 }
 with var show ?thesis  unfolding all_ctxt_closed_def by auto
qed

abbreviation clhs :: "('f, 'v) crule \<Rightarrow> ('f, 'v) term"
where
  "clhs \<rho> \<equiv> fst (fst \<rho>)"

abbreviation crhs :: "('f, 'v) crule \<Rightarrow> ('f, 'v) term"
where
  "crhs \<rho> \<equiv> snd (fst \<rho>)"

definition X_vars :: "('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v set"
where
  "X_vars \<rho> i = vars_term (clhs \<rho>) \<union> \<Union>(vars_term ` rhss (set (take i (snd \<rho>))))"

lemma X_vars_mono:
  "i \<le> j \<Longrightarrow> X_vars \<rho> i \<subseteq> X_vars \<rho> j"
by (fastforce simp: X_vars_def dest: set_take_subset_set_take)

definition Y_vars ::"('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v set"
where
  "Y_vars \<rho> i =
    vars_term (crhs \<rho>) \<union> vars_term (snd (snd \<rho> ! i)) \<union> (vars_trs (set (drop (Suc i) (snd \<rho>))))"

lemma X_vars_alt : 
  assumes "i \<le> length (snd \<rho>)"
  shows "X_vars \<rho> i = vars_term (clhs \<rho>) \<union> \<Union>((\<lambda>j. vars_term (snd (snd \<rho> ! j))) ` {j. j < i})"
proof -
  let ?L = "\<Union>(vars_term ` (rhss (set (List.take i (snd \<rho>)))))"
  let ?R = "\<Union>((\<lambda>j. vars_term (snd (snd \<rho> ! j))) ` {j. j < i})"
  { fix x
   assume "x \<in> ?L" 
   then have "\<exists>j. j < i \<and> x \<in> vars_term (snd ((snd \<rho>) ! j))" unfolding set_conv_nth using nth_take[of _ i "snd \<rho>"] by fastforce
   then obtain j where j:"j < i" and x:"x \<in> vars_term (snd (snd \<rho> ! j))" by blast
   then have "x \<in> ?R"  by blast
  } then have *: "?L \<subseteq> ?R" by auto
  { fix x
   assume "x \<in> ?R"
   then have "\<exists>j. j < i \<and> x \<in> vars_term (snd ((snd \<rho>) ! j))" by blast
   then obtain j where  j:"j < i" and x:"x \<in> vars_term (snd (snd \<rho> ! j))" by blast
   then have "x \<in> vars_term (snd (take i (snd \<rho>) ! j))"  using nth_take[OF j(1)] by force
   with j(1)  have "x \<in> ?L" unfolding set_conv_nth length_take min_absorb2[OF assms] by blast
  } then have "?R \<subseteq> ?L" by auto
  with * have *:"?L = ?R" by blast
  show ?thesis unfolding X_vars_def * by blast
qed

lemma set_drop_nth: "set (drop i xs) = {xs ! j | j. j \<ge> i \<and> j < length xs}"
proof -
  have "i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> \<exists>ia. xs ! j = drop i xs ! ia \<and> ia < length xs - i" for j
    using le_Suc_ex by fastforce
  then show ?thesis unfolding set_conv_nth by auto
qed

lemma Y_vars_alt : 
  assumes i: "i < length (snd \<rho>)"
  shows "Y_vars \<rho> i = vars_term (crhs \<rho>) \<union> 
    \<Union> {vars_term (fst (snd \<rho> ! j)) | j. i < j \<and> j < length (snd \<rho>)} \<union>
    \<Union> {vars_term (snd (snd \<rho> ! j)) | j. i \<le> j \<and> j < length (snd \<rho>)}"
    (is "_ = ?A \<union> ?B \<union> ?C")
proof -  
  {
    fix x
    have "(x \<in> Y_vars \<rho> i) = (x \<in> ?A \<or> x \<in> vars_term (snd (snd \<rho> ! i)) 
      \<or> x \<in> vars_trs (set (drop (Suc i) (snd \<rho>))))" (is "_ = (_ \<or> x \<in> ?B' \<or> x \<in> ?C')") 
      unfolding Y_vars_def by auto
    also have "?C' = \<Union> (vars_rule ` (set (drop (Suc i) (snd \<rho>))))" unfolding vars_trs_def by auto
    also have "set (drop (Suc i) (snd \<rho>)) = {snd \<rho> ! j | j. j \<ge> Suc i \<and> j < length (snd \<rho>)}"
      (is "_ = ?C''") unfolding set_drop_nth ..
    also have "(x \<in> ?B' \<or> x \<in> \<Union> (vars_rule ` ?C'')) = (x \<in> ?B \<union> ?C)" 
    proof -
      {
        assume "x \<in> ?B'"
        then have "x \<in> ?C" using i by auto
      } moreover {
        assume "x \<in> \<Union> (vars_rule ` ?C'')"
        then obtain j where "x \<in> vars_rule (snd \<rho> ! j)" 
          and *: "j > i" "j \<ge> i" "j < length (snd \<rho>)" by auto
        then have "x \<in> vars_term (fst (snd \<rho> ! j)) \<union> vars_term (snd (snd \<rho> ! j))" 
          by (auto simp: vars_rule_def)
        with * have "x \<in> ?B \<union> ?C" by blast
      } moreover {
        assume "x \<in> ?B"
        then obtain j where "x \<in> vars_term (fst (snd \<rho> ! j))" 
          and *: "Suc i \<le> j" "j < length (snd \<rho>)" by auto
        then have "x \<in> vars_rule (snd \<rho> ! j)" 
          by (auto simp: vars_rule_def)
        with * have "x \<in> \<Union> (vars_rule ` ?C'')" by blast
      } moreover {
        assume "x \<in> ?C"
        then obtain j where xx: "x \<in> vars_term (snd (snd \<rho> ! j))" 
          and *: "i \<le> j" "j < length (snd \<rho>)" by auto
        then have x: "x \<in> vars_rule (snd \<rho> ! j)" 
          by (auto simp: vars_rule_def)
        have "x \<in> ?B' \<union> \<Union> (vars_rule ` ?C'')"
        proof (cases "j = i")
          case False
          with * have "Suc i \<le> j" by auto
          with * x show ?thesis by blast
        qed (insert xx, auto)
      }
      ultimately show ?thesis by blast
    qed
    finally have "(x \<in> Y_vars \<rho> i) = (x \<in> ?A \<union> ?B \<union> ?C)" by auto
  }
  then show ?thesis by blast
qed
   
definition type3 :: "('f, 'v) ctrs \<Rightarrow> bool"
where
  "type3 R \<longleftrightarrow> (\<forall> \<rho> \<in> R. vars_term (crhs \<rho>) \<subseteq> (vars_term (clhs \<rho>) \<union> vars_trs (set (snd \<rho>))))"

definition dctrs :: "('f, 'v) ctrs \<Rightarrow> bool"
where
  "dctrs R \<longleftrightarrow> (\<forall> \<rho> \<in> R. \<forall> i < length (snd \<rho>). vars_term (fst (snd \<rho> ! i)) \<subseteq> X_vars \<rho> i)"

definition wf_ctrs :: "('f, 'v) ctrs \<Rightarrow> bool"
where
  "wf_ctrs R \<longleftrightarrow> (\<forall>((l, r), cs) \<in> R. is_Fun l) \<and> type3 R \<and> dctrs R"

definition funs_crule :: "('f, 'v) crule \<Rightarrow> 'f set"
where
  "funs_crule \<rho> = funs_rule (fst \<rho>) \<union> funs_trs (set (snd \<rho>))"

definition funas_crule :: "('f, 'v) crule \<Rightarrow> ('f \<times> nat) set"
where
  "funas_crule \<rho> = funas_rule (fst \<rho>) \<union> funas_trs (set (snd \<rho>))"

definition funs_ctrs :: "('f, 'v) ctrs \<Rightarrow> 'f set"
where
  "funs_ctrs R = \<Union>(funs_crule ` R)"

definition funas_ctrs :: "('f, 'v) ctrs \<Rightarrow> ('f \<times> nat) set"
where
  "funas_ctrs R = \<Union>(funas_crule ` R)"

definition vars_crule :: "('f, 'v) crule \<Rightarrow> 'v set"
where
  "vars_crule \<rho> = vars_rule (fst \<rho>) \<union> vars_trs (set (snd \<rho>))"

definition vars_ctrs :: "('f, 'v) ctrs \<Rightarrow> 'v set"
where
  "vars_ctrs R = \<Union>(vars_crule ` R)"

text \<open>The underlying unconditional TRS\<close>
definition Ru :: "('f, 'v) ctrs \<Rightarrow> ('f, 'v) trs"
where
  "Ru R = fst ` R"

lemma defined_R_imp_Ru: "root l = Some fn \<Longrightarrow> ((l, r), cs) \<in> R \<Longrightarrow> defined (Ru R) fn"
  by (force simp: Ru_def defined_def)

lemma cstep_imp_Ru_step: "(cstep R) \<subseteq> (rstep (Ru R))"
proof
  fix s t
  assume "(s, t) \<in> cstep R"
  with cstep_iff cstep_n.simps(1) obtain n where n: "(s, t) \<in> cstep_n R (Suc n)"
    by (metis empty_iff not0_implies_Suc)
  then have "\<exists>C l r \<sigma> cs. (s, t) = (C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<and> ((l, r), cs) \<in> R" unfolding Ru_def cstep_n.simps(2) by fast
  then have "\<exists>C l r \<sigma>. (s, t) = (C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<and> (l, r) \<in> Ru R" unfolding Ru_def by force
  then show "(s, t) \<in> rstep (Ru R)" by auto
qed

lemma Ru_NF_imp_R_NF: "t \<in> NF (rstep (Ru R)) \<Longrightarrow> t \<in> NF (cstep R)"
using NF_anti_mono [OF cstep_imp_Ru_step] by blast

lemma funas_ctrs_cond:
 assumes rho:"\<rho> \<in> R" and i:"i < length (snd \<rho>)" shows "funas_rule (snd \<rho> ! i) \<subseteq> funas_ctrs R"
   using assms funas_crule_def unfolding funas_ctrs_def funas_trs_def set_conv_nth by blast

lemma wf_ctrs_steps_preserves_funas:
 assumes wf: "wf_ctrs R" and s: "funas_term s \<subseteq> F" and R: "funas_ctrs R \<subseteq> F"
   and st:"(s, t) \<in> (cstep R)\<^sup>*"
 shows "funas_term t \<subseteq> F"
proof- 
 from wf[unfolded wf_ctrs_def] have t3:"type3 R" and dctrs:"dctrs R" by auto
 let ?rfuns = "\<lambda> v. funas_term v \<subseteq> F"
 from rtrancl_power csteps_imp_csteps_n[OF st]  obtain n k where st':"(s,t) \<in> (cstep_n R n) ^^ k" by blast
 let ?P = "\<lambda> (n,k). \<forall> s t. ?rfuns s \<longrightarrow> (s,t) \<in> (cstep_n R n) ^^ k \<longrightarrow> ?rfuns t"
 have "?P (n,k)" proof(induct rule: wf_induct[OF wf_measures, of "[fst, snd]" ?P])
  case (1 nk) note ind = this
   obtain n k where nk: "nk = (n,k)" by force
   { fix s t
     assume s:"?rfuns s" and st:"(s, t) \<in> (cstep_n R n) ^^ k"
     then have "?rfuns t" proof(cases k)
      case 0
       with s st show ?thesis by simp
      next
      case (Suc m)
       from relpow_Suc_E[OF st[unfolded Suc]] obtain u where u:"(s,u) \<in> (cstep_n R n) ^^ m" "(u,t) \<in> cstep_n R n" by blast 
       have "((n,m), nk) \<in> measures [fst, snd]" unfolding nk Suc by auto
       from ind[rule_format, OF this, unfolded split, rule_format, OF s u(1)] have fu:"?rfuns u" by auto
       show ?thesis proof (cases n)
        case 0
         from u(2)[unfolded 0 cstep_n.simps] show ?thesis by auto
        next
        case (Suc n)
          from u(2)[unfolded Suc cstep_n.simps] obtain C l r \<sigma> cs where step:"(u,t) = (C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>)"
           "((l, r), cs) \<in> R" "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*" by force
          from this(1) fu have fl:"?rfuns (l \<cdot> \<sigma>)" by auto
          with supteq_imp_funas_term_subset supteq_Var
            have fx:"\<And>x. x \<in> vars_term l \<Longrightarrow> ?rfuns (\<sigma> x)" by fastforce
          { fix i
            assume i:"i < length cs"
            let ?stm = " \<lambda> m. (fst (cs ! m) \<cdot> \<sigma>, snd (cs ! m) \<cdot> \<sigma>)"
            from i have "funas_rule (?stm i) \<subseteq> F" proof (induct i rule:nat_less_induct)
             fix i
             assume ind2:"\<forall>m<i. (m < length cs \<longrightarrow> funas_rule (?stm m) \<subseteq> F)" and i:"i < length cs"
             from dctrs[unfolded dctrs_def, rule_format, OF step(2), of i] i have 
              vs:"vars_term (fst (cs ! i)) \<subseteq> vars_term l \<union> X_vars ((l, r), cs) i" by auto
             { fix j x
               assume "x \<in> \<Union>(vars_term ` rhss (set (take i cs)))" 
               then have "\<exists>j. j < i \<and> x \<in> vars_term (snd (cs ! j))" unfolding set_conv_nth using nth_take[of _ i cs] by fastforce
               then obtain j where j:"j < i" and x:"x \<in> vars_term (snd (cs ! j))" by blast
               from ind2[rule_format, OF j] i j have "funas_term (snd (cs ! j) \<cdot> \<sigma>) \<subseteq> F" unfolding funas_rule_def by auto
               with x supteq_imp_funas_term_subset supteq_Var have "?rfuns (\<sigma> x)" by fastforce
             } note vt = this
             { fix x assume "x \<in> vars_term (fst (cs ! i))"
               with vs[unfolded X_vars_def] fx vt have "?rfuns (\<sigma> x)" by auto
             }
             with funas_ctrs_cond[OF step(2), unfolded snd_conv, OF i] R have lhs:"?rfuns (fst (cs ! i) \<cdot> \<sigma>)" 
              unfolding funas_term_subst funas_rule_def by blast
             from i have "(fst (cs ! i), snd (cs ! i)) \<in> set cs" by auto
             from  step(3)[rule_format, OF this, unfolded split] obtain l where 
              st:"(fst (cs ! i) \<cdot> \<sigma>, snd (cs ! i) \<cdot> \<sigma>) \<in> (cstep_n R n) ^^ l" unfolding rtrancl_power by blast
             have "((n,l), nk) \<in> measures [fst, snd]" unfolding nk Suc by auto
             from ind[rule_format, OF this, unfolded split, rule_format, OF lhs st]
               have rhs:"funas_term (snd (cs ! i) \<cdot> \<sigma>) \<subseteq> F" by auto
             from lhs rhs show "funas_rule (?stm i) \<subseteq> F" unfolding funas_rule_def by auto
            qed
          } note aux = this
          from t3[unfolded type3_def, rule_format, OF step(2)] 
           have vr:"vars_term r \<subseteq> vars_term l \<union> vars_trs (set cs )" by auto
           from funas_rule_def[of "(l,r)"] have "funas_term r \<subseteq> funas_crule ((l, r), cs)" unfolding funas_crule_def by auto
           with  step(2) have fr:"funas_term r \<subseteq> funas_ctrs R" unfolding funas_ctrs_def by auto
          { fix j x
            assume j:"j < length cs" and "x \<in> vars_rule (cs ! j)"
            with supteq_Var have "fst (cs ! j) \<unrhd> Var x \<or> snd (cs ! j) \<unrhd> Var x" unfolding vars_rule_def by fastforce
            then have x:"fst (cs ! j) \<cdot> \<sigma> \<unrhd> Var x \<cdot> \<sigma> \<or> snd (cs ! j) \<cdot> \<sigma> \<unrhd> Var x \<cdot> \<sigma>" by auto
            from aux j have "funas_rule (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<subseteq> F" unfolding funas_rule_def by auto
            with x supteq_imp_funas_term_subset  have "?rfuns (\<sigma> x)" unfolding funas_rule_def by force
          }
          with vr[unfolded set_conv_nth vars_trs_def] fx have "\<And>x. x \<in> vars_term r \<Longrightarrow> ?rfuns (\<sigma> x)" by blast
          with step(2) fr R have lhs:"?rfuns (r \<cdot> \<sigma>)" unfolding funas_term_subst funas_rule_def by blast
          from step(1) have t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>" and u:"u = C\<langle>l \<cdot> \<sigma>\<rangle>" by (fast,fast)
          from lhs fu show "?rfuns t" unfolding t u by auto
         qed
      qed
   }
   then show ?case unfolding nk split by blast
 qed
 from this[unfolded split, rule_format, OF s st'] show ?thesis by auto
qed

lemma funs_crule_funas_crule:
  "funs_crule r = fst ` funas_crule r" 
  unfolding funs_crule_def funas_crule_def  funs_trs_funas_trs funs_rule_funas_rule by blast

lemma funs_ctrs_funas_ctrs:
  "funs_ctrs R = fst ` funas_ctrs R" 
proof -
 from funs_crule_funas_crule have "\<Union>(funs_crule ` R) = \<Union>(((\<lambda>x. fst ` x) \<circ> funas_crule) ` R)" by (metis comp_apply)
 then show ?thesis unfolding funs_ctrs_def funas_ctrs_def image_Union by force
qed

lemma wf_ctrs_steps_preserves_funs:
  assumes wf: "wf_ctrs R" and s: "funs_term s \<subseteq> F"
    and R: "funs_ctrs R \<subseteq> F" and st: "(s, t) \<in> (cstep R)\<^sup>*"
  shows "funs_term t \<subseteq> F"
proof -
  from s R wf_ctrs_steps_preserves_funas[OF wf _ _ st, of "F \<times> UNIV"]
  show ?thesis unfolding funs_term_funas_term funs_ctrs_funas_ctrs by fastforce
qed

lemma cstep_map_funs_term:
  assumes R: "\<And> f. f \<in> funs_ctrs R \<Longrightarrow> h f = f" and "(s, t) \<in> cstep R"
  shows "(map_funs_term h s, map_funs_term h t) \<in> cstep R"
proof -
  let ?h = "map_funs_term h"
  from assms[unfolded cstep_def] obtain n where "(s,t) \<in> cstep_n R n" by auto
  then have "(?h s, ?h t) \<in> cstep_n R n"
  proof (induct n arbitrary: s t)
    case (Suc n)
    from cstep_n_SucE[OF Suc(2)]
      obtain C l r \<sigma> cs
      where rule: "((l,r), cs) \<in> R" and cs: "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*" 
      and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" . 
    let ?\<sigma> = "map_funs_subst h \<sigma>"
    note funs_defs = funs_ctrs_def funs_crule_def[abs_def] funs_rule_def[abs_def] funs_trs_def
    from rule have lr: "funs_term l \<union> funs_term r \<subseteq> funs_ctrs R" unfolding funs_defs
      by auto
    have hl: "?h l = l"
      by (rule funs_term_map_funs_term_id[OF R], insert lr, auto)
    have hr: "?h r = r"
      by (rule funs_term_map_funs_term_id[OF R], insert lr, auto)
    show ?case unfolding s t
      unfolding map_funs_subst_distrib map_funs_term_ctxt_distrib hl hr
    proof (rule cstep_n_SucI[OF rule _ refl refl], rule)
      fix s\<^sub>i t\<^sub>i
      assume in_cs: "(s\<^sub>i,t\<^sub>i) \<in> set cs"
      from in_cs rule have st: "funs_term s\<^sub>i \<union> funs_term t\<^sub>i \<subseteq> funs_ctrs R" unfolding funs_defs by force
      have hs: "?h s\<^sub>i = s\<^sub>i"
        by (rule funs_term_map_funs_term_id[OF R], insert st, auto)
      have ht: "?h t\<^sub>i = t\<^sub>i"
        by (rule funs_term_map_funs_term_id[OF R], insert st, auto)
      from in_cs cs have steps: "(s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*" by auto
      have "(?h (s\<^sub>i \<cdot> \<sigma>), ?h (t\<^sub>i \<cdot> \<sigma>)) \<in> (cstep_n R n)\<^sup>*"
        by (rule rtrancl_map[OF Suc(1) steps])
      then show "(s\<^sub>i \<cdot> ?\<sigma>, t\<^sub>i \<cdot> ?\<sigma>) \<in> (cstep_n R n)\<^sup>*" unfolding map_funs_subst_distrib hs ht .
    qed
  qed simp
  then show ?thesis unfolding cstep_def by auto
qed

definition normalized :: "('f, 'v) ctrs \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool"
where
  "normalized R \<sigma> \<longleftrightarrow> (\<forall>x. \<sigma> x \<in> NF (cstep R))"

lemma empty_subst_normalized:
  assumes "\<forall>((l, r), cs) \<in> R. is_Fun l"
  shows "normalized R Var"
  by (simp add: Var_NF_cstep assms normalized_def)
  
definition "strongly_irreducible R t \<longleftrightarrow> (\<forall>\<sigma>. normalized R \<sigma> \<longrightarrow> t \<cdot> \<sigma> \<in> NF (cstep R))"

lemma strongly_irreducible_I [Pure.intro?]:
  assumes "\<And>\<sigma>. normalized R \<sigma> \<Longrightarrow> t \<cdot> \<sigma> \<in> NF (cstep R)"
  shows "strongly_irreducible R t"
using assms by (auto simp add: strongly_irreducible_def)

lemma Var_strongly_irreducible_cstep:
  "\<forall> ((l, r), cs) \<in> R. is_Fun l \<Longrightarrow> strongly_irreducible R (Var x)"
by (rule strongly_irreducible_I) (simp add: normalized_def)

lemma constructor_term_imp_strongly_irreducible:
  fixes t R
  assumes varcond: "\<forall>((l, r), cs) \<in> R. is_Fun l"
    and constr: "funas_term t \<subseteq> funas_ctrs R - { f. defined (Ru R) f }"
  shows "strongly_irreducible R t"
using constr
proof (induction t)
  case (Var x)
  show ?case using varcond Var_strongly_irreducible_cstep[of R x] by simp
next
  case (Fun f ts)
  show ?case
  proof
    fix \<sigma>
    assume norm: "normalized R \<sigma>"
    show "Fun f ts \<cdot> \<sigma> \<in> NF (cstep R)"
    proof
      fix s
      show "(Fun f ts \<cdot> \<sigma>, s) \<notin> cstep R"
      proof
        assume "(Fun f ts \<cdot> \<sigma>, s) \<in> cstep R"
        with cstepE [of "Fun f ts \<cdot> \<sigma>" s "R"] obtain C \<tau> l r cs
        where "((l, r), cs) \<in> R" and "Fun f ts \<cdot> \<sigma> = C\<langle>l \<cdot> \<tau>\<rangle>" and "s = C\<langle>r \<cdot> \<tau>\<rangle>"
        and "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i \<cdot> \<tau>, t\<^sub>i \<cdot> \<tau>) \<in> (cstep R)\<^sup>*" by auto
        from varcond \<open>((l, r), cs) \<in> R\<close> Ru_def have "is_Fun l" by fastforce
        show "False"
        proof (cases C)
          case (Hole)
          with \<open>Fun f ts \<cdot> \<sigma> = C\<langle>l \<cdot> \<tau>\<rangle>\<close> have "Fun f ts \<cdot> \<sigma> = l \<cdot> \<tau>" by auto
          with \<open>is_Fun l\<close> \<open>((l, r), cs) \<in> R\<close>
            have "(f, length ts) \<in> {f. defined (Ru R) f}"
            using map_eq_imp_length_eq [of "\<lambda>t. t \<cdot> \<sigma>" ts]
            by (cases l) (force intro: defined_R_imp_Ru)+
          with Fun.prems show "False" by auto
        next
          case (More g lts D rts)
          {
            fix u
            assume "u \<in> set ts"
            then have "funas_term u \<subseteq> funas_term (Fun f ts)" by auto
            with Fun.prems have "funas_term u \<subseteq> funas_ctrs R - {f. defined (Ru R) f}" by auto
          }
          note * = this
          {
            fix u
            assume "u \<in> set ts"
            from * [OF this] and Fun.IH[OF this]
            have "strongly_irreducible R u" by auto
          }
          note IH = this
          from More \<open>Fun f ts \<cdot> \<sigma> = C\<langle>l \<cdot> \<tau>\<rangle>\<close> have "map (\<lambda>t. t \<cdot> \<sigma>) ts = lts @ D\<langle>l \<cdot> \<tau>\<rangle> # rts" by simp
          then obtain u where u: "u \<in> set ts" and "u \<cdot> \<sigma> = D\<langle>l \<cdot> \<tau>\<rangle>"
            by (induct ts arbitrary: lts rts) (auto simp: Cons_eq_append_conv)
          then have "u \<cdot> \<sigma> \<unrhd> l \<cdot> \<tau>" by simp
          then show "False"
          proof (cases rule: supteq_subst_cases)
            note supteq_imp_funas_term_subset [simp del]
            case (in_term v)
            with \<open>is_Fun l\<close> and * [OF u] and defined_R_imp_Ru[OF _ \<open>((l, r), cs) \<in> R\<close>]
            show ?thesis
            using supteq_imp_funas_term_subset [OF \<open>u \<unrhd> v\<close>] and map_eq_imp_length_eq
            by (cases l; cases v) (fastforce)+
          next
            have "(l \<cdot> \<tau>, r \<cdot> \<tau>) \<in> cstep R" by (rule cstepI [of _ _ _ _ _ _ \<box>], fact+) (simp_all)
            moreover
            case (in_subst x)
            ultimately show ?thesis using norm NF_cstep_subterm[of "\<sigma> x" R "l \<cdot> \<tau>"]
              by (auto simp: normalized_def)
          qed
        qed
      qed
    qed
  qed
qed

lemma strongly_irreducible_imp_NF:
  assumes vc: "\<forall>((l, r), cs) \<in> R. is_Fun l"
    and si: "strongly_irreducible R t"
  shows "t \<in> NF (cstep R)"
by (metis empty_subst_normalized si strongly_irreducible_def subst_apply_term_empty vc)

lemma constructor_term_NF_cstep:
  assumes varcond: "\<forall>((l, r), cs) \<in> R. is_Fun l"
    and  constr: "funas_term t \<subseteq> funas_ctrs R - { f. defined (Ru R) f}"
  shows "t \<in> NF (cstep R)"
by (auto simp: assms constructor_term_imp_strongly_irreducible strongly_irreducible_imp_NF)

lemma ground_Ru_NF_imp_strongly_irreducible:
  assumes varcond: "\<forall>((l, r), cs) \<in> R. is_Fun l"
    and ground: "ground t"
    and ru_nf: "t \<in> NF (rstep (Ru R))"
  shows "strongly_irreducible R t"
using ground ru_nf
proof (induction t)
  case (Fun f ts)
  from Fun.prems(1) have "\<forall>\<sigma>. Fun f ts \<cdot> \<sigma> = Fun f ts"
  using ground_subst_apply by blast
  then show ?case
    using Fun.prems(2) Ru_NF_imp_R_NF [of "Fun f ts" R] strongly_irreducible_I[of R "Fun f ts"]
    by fastforce
qed simp

context
  fixes R :: "('f, 'v) ctrs"
  assumes vc: "\<forall>((l, r), cs) \<in> R. is_Fun l"
begin

lemma syntactic_det_imp_strong_det:
  assumes "(\<forall> ((l, r), cs) \<in> R. \<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs.
    ((funas_term t\<^sub>i \<subseteq> ((funas_ctrs R) - { f. defined (Ru R) f }) \<or>
    (ground t\<^sub>i \<and> t\<^sub>i \<in> NF (rstep (Ru R))))))"
  shows str_det: "(\<forall> ((l, r), cs) \<in> R. \<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. strongly_irreducible R t\<^sub>i)"
proof -
  {
    fix l r cs s\<^sub>i t\<^sub>i
    assume "((l, r), cs) \<in> R" and "(s\<^sub>i, t\<^sub>i) \<in> set cs"
    moreover
    {
      assume *: "funas_term t\<^sub>i \<subseteq> funas_ctrs R - { f. defined (Ru R) f }"
      from vc have **: "\<forall>((l, r), cs) \<in> R. is_Fun l" by auto
      have "strongly_irreducible R t\<^sub>i"
        using constructor_term_imp_strongly_irreducible [OF ** *] by auto
    }
    moreover
    {
      assume "ground t\<^sub>i \<and> t\<^sub>i \<in> NF (rstep (Ru R))"
      then have "strongly_irreducible R t\<^sub>i"
        using ground_Ru_NF_imp_strongly_irreducible
        by (simp add: Ru_NF_imp_R_NF ground_subst_apply strongly_irreducible_I)
    }
    ultimately
    have "strongly_irreducible R t\<^sub>i" using assms by fastforce
  }
  then show ?thesis by force
qed

end

lemma Var_cstep_n [dest]:
  assumes "(Var x, t) \<in> cstep_n R n"
    and "\<forall>((l, r), cs) \<in> R. is_Fun l"
  shows "False"
using assms by (auto simp: elim!: cstep_nE) (case_tac C; case_tac l; force)

lemma Var_rtrancl_cstep_n [dest]:
  assumes "(Var x, t) \<in> (cstep_n R n)\<^sup>*"
    and "\<forall>((l, r), cs) \<in> R. is_Fun l"
  shows "t = Var x"
using assms by (induct) auto


subsection \<open>TRS for level @{term n}.\<close>

fun trs_n :: "('f, 'v) ctrs \<Rightarrow> nat \<Rightarrow> ('f, 'v) trs"
where
  "trs_n R 0 = {}" |
  "trs_n R (Suc n) =
    {(l \<cdot> \<sigma>, r \<cdot> \<sigma>) | l r \<sigma> cs.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (rstep (trs_n R n))\<^sup>*)}"

lemma trs_n_SucI:
  assumes "((l, r), cs) \<in> R"
    and "\<And>s\<^sub>i t\<^sub>i. (s\<^sub>i, t\<^sub>i) \<in> set cs \<Longrightarrow> (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (rstep (trs_n R n))\<^sup>*"
  shows "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> trs_n R (Suc n)"
  using assms by (simp) blast

lemma trs_nE:
  assumes "(s, t) \<in> trs_n R n"
  obtains l r \<sigma> cs n' where "n = Suc n'" and "s = l \<cdot> \<sigma>" and "t = r \<cdot> \<sigma>" and "((l, r), cs) \<in> R"
    and "\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (rstep (trs_n R n'))\<^sup>*"
  using assms by (cases n; simp) blast

lemma trs_n_SucE:
  assumes "(s, t) \<in> trs_n R (Suc n)"
  obtains l r \<sigma> cs where "s = l \<cdot> \<sigma>" and "t = r \<cdot> \<sigma>" and "((l, r), cs) \<in> R"
    and "\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (rstep (trs_n R n))\<^sup>*"
  using assms by (simp) blast

declare trs_n.simps(2) [simp del]

lemma trs_n_subst:
  assumes "(l, r) \<in> trs_n R n"
  shows "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> trs_n R n"
using assms
proof (induction n)
  case (Suc n)
  from Suc.prems obtain l' r' \<sigma>' cs
    where [simp]: "l = l' \<cdot> \<sigma>'" "r = r' \<cdot> \<sigma>'" and "((l', r'), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>', t\<^sub>i \<cdot> \<sigma>') \<in> (rstep (trs_n R n))\<^sup>*"
    by (auto elim: trs_n_SucE)
  moreover then have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs.
    (s\<^sub>i \<cdot> (\<sigma>' \<circ>\<^sub>s \<sigma>), t\<^sub>i \<cdot> (\<sigma>' \<circ>\<^sub>s \<sigma>)) \<in> (rstep (trs_n R n))\<^sup>*" by (auto intro: rsteps_closed_subst)
  ultimately have "(l' \<cdot> (\<sigma>' \<circ>\<^sub>s \<sigma>), r' \<cdot> (\<sigma>' \<circ>\<^sub>s \<sigma>)) \<in> trs_n R (Suc n)"
    by (blast intro: trs_n_SucI)
  then show ?case by simp
qed simp

lemma no_step_from_constructor:
  assumes vc: "\<forall>((l, r), cs) \<in> R. is_Fun l"
    and "funas_term t \<subseteq> funas_ctrs R - { f. defined (Ru R) f }"
    and fp: "p \<in> fun_poss t"
  shows "(t \<cdot> \<sigma> |_ p, u) \<notin> trs_n R n"
proof
  assume "(t \<cdot> \<sigma> |_ p, u) \<in> trs_n R n"
  from trs_nE [OF this] obtain l r \<tau> cs where *: "((l, r), cs) \<in> R" and **: "t \<cdot> \<sigma> |_ p = l \<cdot> \<tau>"
    by metis
  then obtain f ts where [simp]: "l = Fun f ts" using vc by (cases l, auto)
  have "defined (Ru R) (f, length ts)" using * by (intro defined_R_imp_Ru) (auto)
  moreover from fp ** have "(f, length ts) \<in> funas_term t"
  proof -
    from fun_poss_fun_conv [OF fp] obtain g ss where ***: "t |_ p = Fun g ss" by blast
    with fun_poss_imp_poss [OF fp] have "t \<cdot> \<sigma> |_ p = Fun g (map (\<lambda>x. x \<cdot> \<sigma>) ss)" by auto
    then have [simp]: "g = f" "length ts = length ss" using ** map_eq_imp_length_eq by (force)+
    from *** fun_poss_imp_poss [OF fp] show ?thesis by (auto simp add: funas_term_poss_conv)   
  qed
  ultimately show "False" using assms(2) by blast
qed

lemma cstep_n_rstep_trs_n_conv:
  "cstep_n R n = rstep (trs_n R n)"
proof (induction n)
  case (Suc n)
  { fix s t
    assume "(s, t) \<in> cstep_n R (Suc n)"
    then have "(s, t) \<in> rstep (trs_n R (Suc n))"
      by (auto elim!: cstep_n_SucE simp: Suc split: prod.splits)
         (metis rstep_ctxt rstep_rule trs_n_SucI) }
  moreover
  { fix s t
    assume "(s, t) \<in> rstep (trs_n R (Suc n))"
    then obtain u v C \<sigma> where "(u, v) \<in> trs_n R (Suc n)"
      and [simp]: "s = C\<langle>u \<cdot> \<sigma>\<rangle>""t = C\<langle>v \<cdot> \<sigma>\<rangle>" by blast
    then obtain l r cs \<tau> where "((l, r), cs) \<in> R"
      and [simp]: "u = l \<cdot> \<tau>" "v = r \<cdot> \<tau>"
      and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<tau>, t\<^sub>i \<cdot> \<tau>) \<in> (rstep (trs_n R n))\<^sup>*"
      by (auto elim: trs_n_SucE)
    moreover then have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>), t\<^sub>i \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)) \<in> (cstep_n R n)\<^sup>*"
      by (auto intro: rsteps_closed_subst simp: Suc)
    ultimately have "(C\<langle>l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)\<rangle>, C\<langle>r \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)\<rangle>) \<in> cstep_n R (Suc n)" by (blast intro: cstep_n_SucI)
    then have "(s, t) \<in> cstep_n R (Suc n)" by simp }
  ultimately show ?case by auto
qed simp

lemma trs_n_Suc_mono:
  "trs_n R n \<subseteq> trs_n R (Suc n)"
proof (induct n)
  case (Suc n)
  then have "rstep (trs_n R n) \<subseteq> rstep (trs_n R (Suc n))" by (metis rstep_mono)
  from rtrancl_mono [OF this]
    show ?case by (auto elim!: trs_n_SucE intro!: trs_n_SucI)
qed simp

lemma rrstep_trs_n [simp]:
  "rrstep (trs_n R n) = trs_n R n"
  by (auto simp: CS_rrstep_conv [symmetric]
    elim: subst.closure.cases intro: subst.closureI2 [of _ _ _ _ Var] trs_n_subst)

lemma cstep_rstep_UN_trs_n_conv: "cstep R = rstep (\<Union>n. trs_n R n)"
by (auto simp: cstep_def cstep_n_rstep_trs_n_conv rstep_UN)

lemma Var_trs_n [dest]:
  assumes "(Var x, t) \<in> trs_n R n"
    and "\<forall>((l, r), cs) \<in> R. is_Fun l"
  shows "False"
using assms by (induct n) (force elim!: trs_n_SucE split: prod.splits)+

lemma linear_term_cstep_n_cases':
  assumes "linear_term s"
    and cstep: "(s \<cdot> \<sigma>, u) \<in> cstep_n R n"
  shows "(\<exists>\<tau>. s \<cdot> \<tau> = u \<and> (\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*)) \<or>
    (\<exists>p \<in> fun_poss s. (s \<cdot> \<sigma> |_ p, u |_ p) \<in> trs_n R n)"
proof -
  from cstep [THEN cstep_nE] obtain C l r \<sigma>' cs k
    where rule: "((l, r), cs) \<in> R" and [simp]: "n = Suc k"
    and conds: "conds_n_sat R k cs \<sigma>'"
    and s_\<sigma>: "s \<cdot> \<sigma> = C\<langle>l \<cdot> \<sigma>'\<rangle>" and u: "u = C\<langle>r \<cdot> \<sigma>'\<rangle>"
    unfolding conds_n_sat_iff by metis (*only metis works; investigate!*)
  define p where "p \<equiv> hole_pos C"
  have *: "p \<in> poss (s \<cdot> \<sigma>)" by (simp add: assms s_\<sigma> p_def)
  show ?thesis
  proof (cases "p \<in> fun_poss s")
    case False
    with * obtain q\<^sub>1 q\<^sub>2 x
      where p: "p = q\<^sub>1 @ q\<^sub>2" and q\<^sub>1: "q\<^sub>1 \<in> poss s"
      and lq\<^sub>1: "s |_ q\<^sub>1 = Var x" and q\<^sub>2: "q\<^sub>2 \<in> poss (\<sigma> x)"
        by (rule poss_subst_apply_term)
    moreover
    have [simp]: "s \<cdot> \<sigma> |_ p = l \<cdot> \<sigma>'" using assms p_def s_\<sigma> by auto 
    ultimately
    have [simp]: "\<sigma> x |_ q\<^sub>2 = l \<cdot> \<sigma>'" by simp
    
    define \<tau> where "\<tau> \<equiv> \<lambda>y. if y = x then replace_at (\<sigma> x) q\<^sub>2 (r \<cdot> \<sigma>') else \<sigma> y"
    have \<tau>_x: "\<tau> x = replace_at (\<sigma> x) q\<^sub>2 (r \<cdot> \<sigma>')" by (simp add: \<tau>_def)
    have [simp]: "\<And>y. y \<noteq> x \<Longrightarrow> \<tau> y = \<sigma> y" by (simp add: \<tau>_def)
    have "(\<sigma> x, \<tau> x) \<in> cstep_n R n"
    proof -
      let ?C = "ctxt_of_pos_term q\<^sub>2 (\<sigma> x)"
      have "(?C\<langle>l \<cdot> \<sigma>'\<rangle>, ?C\<langle>r \<cdot> \<sigma>'\<rangle>) \<in> cstep_n R n"
        using conds by (auto intro!: cstep_n_SucI rule simp: conds_n_sat_iff)
      then show ?thesis using q\<^sub>2 by (simp add: \<tau>_def replace_at_ident)
    qed
    then have "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*" by (auto simp: \<tau>_def)
    moreover have "s \<cdot> \<tau> = u"
    proof -
      have [simp]: "ctxt_of_pos_term p (s \<cdot> \<sigma>) = C" by (simp add: assms s_\<sigma> p_def)
      have "s \<cdot> \<sigma> |_ q\<^sub>1 = \<sigma> x" by (simp add: lq\<^sub>1 q\<^sub>1)
      from linear_term_replace_in_subst [OF \<open>linear_term s\<close> q\<^sub>1 lq\<^sub>1, of \<sigma> \<tau>, OF _ \<tau>_x, folded ctxt_ctxt_compose]
        and q\<^sub>1 and ctxt_of_pos_term_append [of q\<^sub>1 "s \<cdot> \<sigma>" q\<^sub>2, folded p, unfolded this, symmetric]
        show "s \<cdot> \<tau> = u" by (simp add: u)
    qed
    ultimately show ?thesis by blast
  next
    case True
    moreover have "(s \<cdot> \<sigma> |_ p, u |_ p) \<in> trs_n R (Suc k)"
      using conds
      by (auto simp: conds_n_sat_iff p_def s_\<sigma> u
               intro: trs_n_SucI [OF rule] simp: cstep_n_rstep_trs_n_conv)
    ultimately show ?thesis by auto
  qed
qed

lemma linear_term_cstep_n_cases [consumes 2]:
  assumes "linear_term s"
    and "(s \<cdot> \<sigma>, u) \<in> cstep_n R n"
  obtains (var_poss) \<tau> where "s \<cdot> \<tau> = u"
    and "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*"
  | (fun_poss) p where "p \<in> fun_poss s" and "(s \<cdot> \<sigma> |_ p, u |_ p) \<in> trs_n R n"
using linear_term_cstep_n_cases' [OF assms] by blast

lemma linear_term_rtrancl_cstep_n_cases':
  assumes "linear_term s"
    and "(s \<cdot> \<sigma>, t) \<in> (cstep_n R n)\<^sup>*"
  shows "(\<exists>\<tau>. s \<cdot> \<tau> = t \<and> (\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*)) \<or>
    (\<exists>\<tau> p u. (\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*) \<and>
      p \<in> fun_poss s \<and> (s \<cdot> \<tau> |_ p, u) \<in> trs_n R n)"
using assms(2)
proof (induct)
  case base
  let ?\<tau> = "\<sigma>"
  have "s \<cdot> \<sigma> = s \<cdot> ?\<tau>" using coincidence_lemma by blast
  moreover have "\<forall>x. (\<sigma> x, ?\<tau> x) \<in> (cstep_n R n)\<^sup>*" by auto
  ultimately show ?case by auto
next
  case (step t u)
  show ?case using step(3)
  proof
    assume "\<exists>\<tau>. s \<cdot> \<tau> = t \<and> (\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*)"
    then obtain \<tau> where t: "t = s \<cdot> \<tau>" and *: "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*" by blast
    then have "(s \<cdot> \<tau>, u) \<in> cstep_n R n" using \<open>(t, u) \<in> cstep_n R n\<close> by auto
    with \<open>linear_term s\<close>
      show ?thesis
      using * by (cases rule: linear_term_cstep_n_cases; blast dest: rtrancl_trans)
  qed blast
qed

lemma linear_term_rtrancl_cstep_n_cases [consumes 2]:
  assumes "linear_term s"
    and "(s \<cdot> \<sigma>, t) \<in> (cstep_n R n)\<^sup>*"
  obtains (var_poss) \<tau> where "s \<cdot> \<tau> = t" and "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*"
  | (fun_poss) \<tau> p u where "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep_n R n)\<^sup>*"
    and "p \<in> fun_poss s" and "(s \<cdot> \<tau> |_ p, u) \<in> trs_n R n"
using linear_term_rtrancl_cstep_n_cases' [OF assms] by blast

definition properly_oriented :: "('f, 'v) ctrs \<Rightarrow> bool"
where
  "properly_oriented R \<longleftrightarrow> (\<forall>\<rho> \<in> R.
    vars_term (crhs \<rho>) \<subseteq> vars_term (clhs \<rho>) \<or>
    (\<forall>i < length (snd \<rho>). vars_term (fst (snd \<rho> ! i)) \<subseteq> X_vars \<rho> i))"

definition extended_properly_oriented :: "('f, 'v) ctrs \<Rightarrow> bool"
where
 "extended_properly_oriented R \<longleftrightarrow> (\<forall>\<rho> \<in> R. vars_term (crhs \<rho>) \<subseteq> vars_term (clhs \<rho>) \<or>
    (\<exists>m \<le> length (snd \<rho>).
      (\<forall>i < m. vars_term (fst (snd \<rho> ! i)) \<subseteq> X_vars \<rho> i) \<and>
      (\<forall>i\<in>{m ..< length (snd \<rho>)}. vars_term (crhs \<rho>) \<inter> vars_rule (snd \<rho> ! i) \<subseteq> X_vars \<rho> m)))"

definition right_stable :: "('f, 'v) ctrs \<Rightarrow> bool"
where
  "right_stable R \<longleftrightarrow> (\<forall> \<rho> \<in> R. \<forall> i < length (snd \<rho>).
    let t\<^sub>i = snd (snd \<rho> ! i) in
    (vars_term (clhs \<rho>) \<union> \<Union>(vars_term ` lhss (set (take (Suc i) (snd \<rho>)))) \<union>
    \<Union>(vars_term ` (rhss (set (take i (snd \<rho>)))))) \<inter> vars_term t\<^sub>i = {} \<and>
    (linear_term t\<^sub>i \<and> funas_term t\<^sub>i \<subseteq> funas_ctrs R - { f. defined (Ru R) f } \<or>
    ground t\<^sub>i \<and> t\<^sub>i \<in> NF (rstep (Ru R))))"

lemma right_stable_rhsD:
  assumes "right_stable R" and "\<rho> \<in> R" and "i < length (snd \<rho>)"
  shows "(vars_term (clhs \<rho>) \<union> \<Union>(vars_term ` lhss (set (take (Suc i) (snd \<rho>)))) \<union>
    \<Union>(vars_term ` (rhss (set (take i (snd \<rho>)))))) \<inter> vars_term (snd (snd \<rho> ! i)) = {}"
using assms by (auto simp: right_stable_def Let_def)

lemma right_stable_rhs_cases [consumes 3, case_names lct [linear cterm] gnf [ground nf]]:
  assumes "right_stable R" and "\<rho> \<in> R"
    and "t \<in> rhss (set (snd \<rho>))"
  obtains
    (lct) "linear_term t" and "funas_term t \<subseteq> funas_ctrs R - {f. defined (Ru R) f}" |
    (gnf) "ground t" and "t \<in> NF (rstep (Ru R))"
proof -
  obtain i where "i < length (snd \<rho>)" and "t = snd (snd \<rho> ! i)"
    using assms(3) by (auto dest: in_set_idx)
  with assms(1, 2) show ?thesis using lct and gnf by (auto simp: right_stable_def Let_def)
qed

lemma crule_cases:
  assumes "\<And>l r cs. \<rho> = ((l, r), cs) \<Longrightarrow> P"
  shows "P"
using assms by (cases \<rho>; auto)

lemma cstep_subst:
  assumes "(s, t) \<in> cstep R"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> cstep R"
using assms
by (auto simp: cstep_def dest: cstep_n_subst)

lemma subst_closed_cstep [intro]:
  "subst.closed (cstep R)"
using cstep_subst subst.closedI by blast

lemma cstep_ctxt:
  assumes "(s, t) \<in> cstep R"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> cstep R"
using assms
by (simp add: cstep_ctxt_closed ctxt.closedD)

lemma csteps_ctxt:
  assumes "(s, t) \<in> (cstep R)\<^sup>*"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (cstep R)\<^sup>*"
using assms
by (simp add: cstep_ctxt_closed ctxt.closedD ctxt.closed_rtrancl)

abbreviation conds :: "('f, 'v) crule \<Rightarrow> ('f, 'v) rule list"
where
  "conds \<rho> \<equiv> snd \<rho>"

lemma conds_n_sat_mono':
  assumes "conds_n_sat R n cs \<sigma>"
    and "set ds \<subseteq> set cs"
  shows "conds_n_sat R n ds \<sigma>"
using assms by (auto simp: conds_n_sat_iff)

definition evars_crule :: "('f, 'v) crule \<Rightarrow> 'v set"
where "evars_crule \<rho> = vars_trs (set (conds \<rho>)) - vars_term (clhs \<rho>)"

lemmas args_csteps_imp_csteps = args_steps_imp_steps [OF cstep_ctxt_closed]

lemma substs_csteps:
  assumes "\<And>x. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"
proof (induct t)
  case (Var y)
  show ?case using assms by simp_all
next
  case (Fun f ts)
  then have "\<forall>i<length (map (\<lambda>t. t \<cdot> \<sigma>) ts).
    (map (\<lambda>t. t \<cdot> \<sigma> ) ts ! i, map (\<lambda>t. t \<cdot> \<tau>) ts ! i) \<in> (cstep R)\<^sup>*" by auto
  from args_csteps_imp_csteps [OF _ this] show ?case by simp
qed

lemma term_subst_cstep:
  assumes "\<And>x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> cstep R" 
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"
using assms
proof (induct t)
  case (Fun f ts)
  { fix t\<^sub>i
    assume t\<^sub>i: "t\<^sub>i \<in> set ts"
    with Fun(2) have "\<And>x. x \<in> vars_term t\<^sub>i \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> cstep R" by auto
    from Fun(1) [OF t\<^sub>i this] have "(t\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<tau>) \<in> (cstep R)\<^sup>*" by blast
  }
  then show ?case by (simp add: args_csteps_imp_csteps) 
qed (auto)

lemma term_subst_csteps:
  assumes "\<And>x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*" 
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"
using assms
proof (induct t)
  case (Fun f ts)
  { fix t\<^sub>i
    assume t\<^sub>i: "t\<^sub>i \<in> set ts"
    with Fun(2) have "\<And>x. x \<in> vars_term t\<^sub>i \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*" by auto
    from Fun(1) [OF t\<^sub>i this] have "(t\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<tau>) \<in> (cstep R)\<^sup>*" by blast
  }
  then show ?case by (simp add: args_csteps_imp_csteps) 
qed (auto)

lemma term_subst_csteps_join:
  assumes "\<And>y. y \<in> vars_term u \<Longrightarrow> (\<sigma>\<^sub>1 y, \<sigma>\<^sub>2 y) \<in> (cstep R)\<^sup>\<down>"
  shows "(u \<cdot> \<sigma>\<^sub>1, u \<cdot> \<sigma>\<^sub>2) \<in> (cstep R)\<^sup>\<down>"
using assms
proof -
  { fix x
    assume "x \<in> vars_term u"
    from assms [OF this] have "\<exists>\<sigma>. (\<sigma>\<^sub>1 x, \<sigma> x) \<in> (cstep R)\<^sup>* \<and> (\<sigma>\<^sub>2 x, \<sigma> x) \<in> (cstep R)\<^sup>*" by auto
  }
  then have "\<forall>x \<in> vars_term u. \<exists>\<sigma>. (\<sigma>\<^sub>1 x, \<sigma> x) \<in> (cstep R)\<^sup>* \<and> (\<sigma>\<^sub>2 x, \<sigma> x) \<in> (cstep R)\<^sup>*" by blast
  then obtain s where "\<forall>x \<in> vars_term u. (\<sigma>\<^sub>1 x, (s x) x) \<in> (cstep R)\<^sup>* \<and> (\<sigma>\<^sub>2 x, (s x) x) \<in> (cstep R)\<^sup>*" by metis
  then obtain \<sigma> where "\<forall>x \<in> vars_term u. (\<sigma>\<^sub>1 x, \<sigma> x) \<in> (cstep R)\<^sup>* \<and> (\<sigma>\<^sub>2 x, \<sigma> x) \<in> (cstep R)\<^sup>*" by fast
  then have "(u \<cdot> \<sigma>\<^sub>1, u \<cdot> \<sigma>) \<in> (cstep R)\<^sup>* \<and> (u \<cdot> \<sigma>\<^sub>2, u \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*" using term_subst_csteps by metis
  then show ?thesis by blast 
qed

lemma subst_csteps_imp_csteps:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "\<forall>x\<in>vars_term t. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"
  by (rule all_ctxt_closed_subst_step)
     (insert assms, auto)

lemma replace_at_subst_csteps:
  fixes \<sigma> \<tau> :: "('f, 'v) subst"
  assumes *: "\<And>x. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*"
    and "p \<in> poss t"
    and "t |_ p = Var x"
  shows "(replace_at (t \<cdot> \<sigma>) p (\<tau> x), t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"
using assms(2-)
proof (induction t arbitrary: p)
  case (Fun f ts)
  then obtain i q where [simp]: "p = i # q" and i: "i < length ts"
    and q: "q \<in> poss (ts ! i)" and [simp]: "ts ! i |_ q = Var x" by (cases p) auto
  let ?C = "ctxt_of_pos_term q (ts ! i \<cdot> \<sigma>)"
  let ?ts = "map (\<lambda>t. t \<cdot> \<tau>) ts"
  let ?ss = "take i (map (\<lambda>t. t \<cdot> \<sigma>) ts) @ ?C\<langle>\<tau> x\<rangle> # drop (Suc i) (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
  have "\<forall>j<length ts. (?ss ! j, ?ts ! j) \<in> (cstep R)\<^sup>*"
  proof (intro allI impI)
    fix j
    assume j: "j < length ts"
    moreover
    { assume [simp]: "j = i"
      have "?ss ! j = ?C\<langle>\<tau> x\<rangle>" using i by (simp add: nth_append_take)
      with Fun.IH [of "ts ! i" q]
      have "(?ss ! j, ?ts ! j) \<in> (cstep R)\<^sup>*" using q and i by simp }
    moreover
    { assume "j < i"
      with i have "?ss ! j = ts ! j \<cdot> \<sigma>"
        and "?ts ! j = ts ! j \<cdot> \<tau>" by (simp_all add: nth_append_take_is_nth_conv)
      then have "(?ss ! j, ?ts ! j) \<in> (cstep R)\<^sup>*" by (auto simp: * subst_csteps_imp_csteps) }
    moreover
    { assume "j > i"
      with i and j have "?ss ! j = ts ! j \<cdot> \<sigma>"
        and "?ts ! j = ts ! j \<cdot> \<tau>" by (simp_all add: nth_append_drop_is_nth_conv)
      then have "(?ss ! j, ?ts ! j) \<in> (cstep R)\<^sup>*" by (auto simp: * subst_csteps_imp_csteps) }
    ultimately show "(?ss ! j, ?ts ! j) \<in> (cstep R)\<^sup>*" by arith
  qed
  moreover have "i < length ts" by fact
  ultimately show ?case
    by (simp add: args_csteps_imp_csteps)
qed simp

definition map_funs_crule :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) crule \<Rightarrow> ('g, 'v) crule"
where
  "map_funs_crule f r = ((map_funs_term f (clhs r), map_funs_term f (crhs r)), map (map_funs_rule f) (conds r))"

lemma map_funs_crule_id [simp]: "map_funs_crule id = id"
  by (auto simp: map_funs_crule_def)

fun map_funs_ctrs :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) ctrs \<Rightarrow> ('g, 'v) ctrs"
where
  "map_funs_ctrs f R = map_funs_crule f ` R"

lemma conds_sat_Cons:
  "conds_sat R (c # cs) \<sigma> \<longleftrightarrow> (fst c \<cdot> \<sigma>, snd c \<cdot> \<sigma>) \<in> (cstep R)\<^sup>* \<and> conds_sat R cs \<sigma>"
by (auto simp: conds_sat_iff)

lemma conds_n_sat_Cons:
  "conds_n_sat R n (c # cs) \<sigma> \<longleftrightarrow>
    (fst c \<cdot> \<sigma>, snd c \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>* \<and> conds_n_sat R n cs \<sigma>"
by (auto simp: conds_n_sat_iff)

lemma conds_sat_conds_n_sat:
  "conds_sat R cs \<sigma> \<longleftrightarrow> (\<exists>n. conds_n_sat R n cs \<sigma>)" (is "?P = ?Q")
proof
  assume "?Q" then show "?P"
    by (auto simp: conds_sat_iff conds_n_sat_iff dest: csteps_n_imp_csteps)
next
  assume "?P" then show "?Q"
  proof (induct cs)
    case (Cons c cs)
    then show ?case
      apply (auto simp: conds_sat_Cons conds_n_sat_Cons dest!: csteps_imp_csteps_n)
      apply (rule_tac x = "max n na" in exI)
      apply (auto simp: max_def conds_n_sat_iff conds_sat_iff
        dest!: csteps_n_mono)
      apply (rule_tac m1 = na and n1 = n in csteps_n_mono [THEN subsetD])
      apply force+
      done
  qed simp
qed

subsection \<open>Permutation Types for Conditional Rules and CTRSs\<close>

interpretation crule_pt: prod_pt rule_pt.permute_prod rules_pt.permute_list ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> crule_pt.permute_prod and
  FRESH \<rightleftharpoons> crule_pt.fresh crule_pt.fresh_set

interpretation ctrs_pt: set_pt crule_pt.permute_prod ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> ctrs_pt.permute_set and
  FRESH \<rightleftharpoons> ctrs_pt.fresh

lemma finite_crule_supp:
  "finite (crule_pt.supp ((l, r), cs))"
  by (simp add: finite_term_supp rule_fs.finite_supp)

interpretation crule_fs: finitely_supported crule_pt.permute_prod
  by standard (auto simp: finite_rule_supp finite_term_supp)

lemma conds_n_sat_perm_shift:
  "conds_n_sat R n (\<pi> \<bullet> cs) \<sigma> = conds_n_sat R n cs (\<sigma> \<circ> Rep_perm \<pi>)"
by (auto simp: conds_n_sat_iff permute_term_subst_apply_term eqvt split: prod.splits)

lemma supp_vars_crule_eq:
  fixes r :: "('f, 'v :: infinite) crule"
  shows "crule_pt.supp r = vars_crule r"
by (cases r; auto simp: vars_crule_def vars_trs_def supp_vars_term_eq vars_rule_def)

lemma vars_crule_disjoint:
  fixes l r u v :: "('f, 'v :: infinite) term"
    and cs ds :: "('f, 'v) rule list"
  shows "\<exists>p. vars_crule (p \<bullet> ((l, r), cs)) \<inter> vars_crule ((u, v), ds) = {}"
proof -
  from crule_fs.supp_fresh_set obtain p
    where "crule_pt.supp (p \<bullet> ((l, r), cs)) \<sharp> ((u, v), ds)" by blast
  from crule_pt.fresh_set_disjoint [OF this]
    show ?thesis
    by (auto simp: supp_vars_crule_eq vars_rule_def)
qed

lemma X_vars_eqvt [eqvt]:
  fixes p :: "'v::infinite perm"
  shows "p \<bullet> X_vars r i = X_vars (p \<bullet> r) i"
proof -
  have "take i (snd (p \<bullet> r)) = p \<bullet> take i (snd r)"
    by (metis (no_types, opaque_lifting) crule_pt.snd_eqvt rules_pt.permute_list_def take_map)
  then show ?thesis
    by (simp_all add: X_vars_def eqvt)
qed

lemma variant_conds_n_sat_cstep_n:
  assumes "\<pi> \<bullet> \<rho> \<in> R"
    and "conds_n_sat R n (conds \<rho>) \<sigma>"
  shows "(clhs \<rho> \<cdot> \<sigma>, crhs \<rho> \<cdot> \<sigma>) \<in> cstep_n R (Suc n)"
proof -
  from assms(1) have r: "((\<pi> \<bullet> clhs \<rho>, \<pi> \<bullet> crhs \<rho>), \<pi> \<bullet> conds \<rho>) \<in> R"
    by (simp add: eqvt split: prod.split)
       (metis crule_pt.snd_eqvt prod.collapse rules_pt.permute_list_def)
  from assms(2) have "conds_n_sat R n (- \<pi> \<bullet> \<pi> \<bullet> conds \<rho>) \<sigma>"
    by (metis rules_pt.permute_minus_cancel(2))
  from conds_n_sat_perm_shift [THEN iffD1, OF this]
    have "conds_n_sat R n (\<pi> \<bullet> conds \<rho>) (\<sigma> \<circ> Rep_perm (- \<pi>))" (is "conds_n_sat _ _ _ ?\<tau>") by auto
  from conds_n_sat_iff [THEN iffD1, OF this]
    have "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set (\<pi> \<bullet> conds \<rho>). (s\<^sub>i \<cdot> ?\<tau>, t\<^sub>i \<cdot> ?\<tau>) \<in> (cstep_n R n)\<^sup>*" .
  from cstep_n_SucI [OF r this, of _ \<box>]
    have "(\<pi> \<bullet> clhs \<rho> \<cdot> ?\<tau>, \<pi> \<bullet> crhs \<rho> \<cdot> ?\<tau>) \<in> cstep_n R (Suc n)" by force
  then have "(clhs \<rho> \<cdot> (sop \<pi> \<circ>\<^sub>s ?\<tau>), crhs \<rho> \<cdot> (sop \<pi> \<circ>\<^sub>s ?\<tau>)) \<in> cstep_n R (Suc n)" by simp
  then show ?thesis
    by (metis (no_types, lifting) permute_term_subst_apply_term subst_subst
        term_apply_subst_Var_Rep_perm term_pt.permute_minus_cancel(2))
qed

lemma variant_conds_sat_cstep:
  assumes "\<pi> \<bullet> \<rho> \<in> R"
    and "conds_sat R (conds \<rho>) \<sigma>"
  shows "(clhs \<rho> \<cdot> \<sigma>, crhs \<rho> \<cdot> \<sigma>) \<in> cstep R"
using assms conds_sat_conds_n_sat cstep_n_imp_cstep variant_conds_n_sat_cstep_n by blast

lemma rsteps_eqvt:
  "\<pi> \<bullet> (rstep R)\<^sup>* = (rstep (\<pi> \<bullet> R))\<^sup>*"
using rstep_eqvt [of \<pi> R]
by (metis permute_rstep rstep_rtrancl_idemp)

lemma trs_n_eqvt_aux:
  "\<pi> \<bullet> (trs_n (-\<pi> \<bullet> R) n) = trs_n R n"
proof (induct n)
  case (Suc n)
  then have IH: "\<pi> \<bullet> (trs_n (-\<pi> \<bullet> R) n) = trs_n R n" by blast
  show ?case
  proof (intro equalityI subrelI, goal_cases)
    case (1 s t)
    then have "(-\<pi> \<bullet> s, -\<pi> \<bullet> t) \<in> trs_n (-\<pi> \<bullet> R) (Suc n)"
      using inv_rule_mem_trs_simps(1) by blast
    then show ?case unfolding trs_n.simps apply (simp add: IH [symmetric])
      apply auto
      apply (rule_tac x = "\<pi> \<bullet> l" in exI)
      apply (rule_tac x = "\<pi> \<bullet> r" in exI)
      apply (rule_tac x = "sop (-\<pi>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop \<pi>" in exI)
      apply (auto simp:)
      apply (metis term_pt.permute_minus_cancel(1))
      apply (metis term_pt.permute_minus_cancel(1))
      apply (rule_tac x = "\<pi> \<bullet> cs" in exI)
      apply (auto simp: eqvt)
      by (metis (no_types, lifting) case_prodD rstep_imp_perm_rstep rstep_rtrancl_idemp term_apply_subst_eqvt)
  next
    case (2 s t)
    then have "(-\<pi> \<bullet> s, -\<pi> \<bullet> t) \<in> trs_n (-\<pi> \<bullet> R) (Suc n)"
      apply (auto simp: trs_n.simps(2))
      apply (rule_tac x = "-\<pi> \<bullet> l" in exI)
      apply (rule_tac x = "-\<pi> \<bullet> r" in exI)
      apply (rule_tac x = "sop \<pi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop (-\<pi>)" in exI)
      apply auto
      apply (rule_tac x = "-\<pi> \<bullet> cs" in exI)
      apply (auto simp: eqvt map_idI rsteps_eqvt IH)
      by force
    then show ?case using inv_rule_mem_trs_simps(1) by blast
  qed
qed simp

lemma rstep_perm_trs_n:
  shows "rstep (\<pi> \<bullet> (trs_n R n)) = rstep (trs_n (\<pi> \<bullet> R) n)"
using trs_n_eqvt_aux [of "-\<pi>" R n]
apply (simp)
by (metis rstep_permute)

lemma cstep_permute:
  "cstep (\<pi> \<bullet> R) = cstep R"
proof -
  have "cstep (\<pi> \<bullet> R) = (\<Union>n. rstep (trs_n (\<pi> \<bullet> R) n))"
    by (auto simp: cstep_def cstep_n_rstep_trs_n_conv)
  also have "\<dots> = (\<Union>n. rstep (\<pi> \<bullet> (trs_n R n)))" unfolding rstep_perm_trs_n ..
  also have "\<dots> = (\<Union>n. rstep (trs_n R n))" unfolding rstep_permute ..
  also have "\<dots> = cstep R" by (auto simp: cstep_def cstep_n_rstep_trs_n_conv)
  finally show ?thesis .
qed

lemma cstep_eqvt [eqvt]:
  "\<pi> \<bullet> cstep R = cstep (\<pi> \<bullet> R)"
proof -
  have "\<pi> \<bullet> cstep R = \<pi> \<bullet> (\<Union>n. rstep (trs_n R n))"
    by (auto simp: cstep_def cstep_n_rstep_trs_n_conv)
  also have "\<dots> = (\<Union>n. rstep (\<pi> \<bullet> (trs_n R n)))" by (auto simp: eqvt)
  also have "\<dots> = (\<Union>n. rstep (trs_n (\<pi> \<bullet> R) n))" unfolding rstep_perm_trs_n ..
  also have "\<dots> = cstep (\<pi> \<bullet> R)" by (auto simp: cstep_def cstep_n_rstep_trs_n_conv)
  finally show ?thesis .
qed

lemma permute_cstep [simp]:
  "\<pi> \<bullet> cstep R = cstep R"
by (simp add: eqvt cstep_permute)

lemma csteps_eqvt:
  "\<pi> \<bullet> (cstep R)\<^sup>* = (cstep (\<pi> \<bullet> R))\<^sup>*"
proof (intro equalityI subrelI)
  fix s t assume "(s, t) \<in> \<pi> \<bullet> (cstep R)\<^sup>*"
  then have "(-\<pi> \<bullet> s, -\<pi> \<bullet> t) \<in> (cstep R)\<^sup>*" by auto
  then show "(s, t) \<in> (cstep (\<pi> \<bullet> R))\<^sup>*"
    apply (induct "-\<pi> \<bullet> s" "-\<pi> \<bullet> t" arbitrary: t)
    apply auto
    by (metis (no_types, lifting) cstep_eqvt inv_rule_mem_trs_simps(2) minus_minus rtrancl.rtrancl_into_rtrancl term_pt.permute_minus_cancel(1))
next
  fix s t assume "(s, t) \<in> (cstep (\<pi> \<bullet> R))\<^sup>*"
  then show "(s, t) \<in> \<pi> \<bullet> (cstep R)\<^sup>*"
    apply (induct)
    using inv_rule_mem_trs_simps(1) apply blast
    by (metis cstep_eqvt inv_rule_mem_trs_simps(1) rtrancl.rtrancl_into_rtrancl)
qed

lemma cstep_n_permute_iff:
  "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> cstep_n R n \<longleftrightarrow> (s, t) \<in> cstep_n R n"
by (auto simp: cstep_n_rstep_trs_n_conv split: prod.splits)

lemma subst_compose_o_assoc:
  "(\<sigma> \<circ>\<^sub>s \<tau>) \<circ> f = (\<sigma> \<circ> f) \<circ>\<^sub>s \<tau>"
by (rule ext) (simp add: subst_compose)

lemma perm_csteps_n_perm:
  assumes "(\<pi> \<bullet> s, t) \<in> (cstep_n R n)\<^sup>*"
  shows "\<exists>u. t = \<pi> \<bullet> u"
  using assms by (metis term_pt.permute_minus_cancel(1))

lemma subst_list_subst_compose:
  "subst_list (\<sigma> \<circ>\<^sub>s \<tau>) xs = subst_list \<tau> (subst_list \<sigma> xs)"
by (simp add: subst_list_def)

lemma subst_list_Rep_perm:
  "subst_list (\<sigma> \<circ> Rep_perm \<pi>) xs = subst_list \<sigma> (\<pi> \<bullet> xs)"
  by (auto simp: subst_list_def permute_term_subst_apply_term [symmetric] eqvt)


lemma finite_vars_crule: "finite (vars_crule r)"
by (auto simp: vars_crule_def vars_defs)

lemma nth_subst_list [simp]:
  "i < length ts \<Longrightarrow> subst_list \<sigma> ts ! i = (fst (ts ! i) \<cdot> \<sigma>, snd (ts ! i) \<cdot> \<sigma>)"
by (auto simp: subst_list_def)

lemma length_subst_list [simp]:
  "length (subst_list \<sigma> ts) = length ts"
by (auto simp: subst_list_def)

lemma vars_conds_vars_crule_subset:
  "x \<in> vars_term (fst (conds r ! i)) \<Longrightarrow> i < length (conds r) \<Longrightarrow> x \<in> vars_crule r"
  "x \<in> vars_term (snd (conds r ! i)) \<Longrightarrow> i < length (conds r) \<Longrightarrow> x \<in> vars_crule r"
by (auto simp: vars_crule_def vars_defs)

lemma permute_conds_set [simp]:
  fixes cs :: "('f, 'v::infinite) rule list"
  shows "\<pi> \<bullet> set cs = set (\<pi> \<bullet> cs)"
by (induct cs) (auto simp: eqvt)

lemma cstep_imp_map_cstep:
  assumes "(s, t) \<in> cstep R"
  shows "(map_funs_term h s, map_funs_term h t) \<in> cstep (map_funs_ctrs h R)"
    (is "(?h s, ?h t) \<in> cstep (?H R)")
proof -
  obtain n where "(s, t) \<in> cstep_n R n" using assms by (auto simp: cstep_iff)
  then have "(?h s, ?h t) \<in> cstep_n (?H R) n"
  proof (induct n arbitrary: s t)
    case (Suc n)
    then obtain C \<sigma> l r cs where rule: "((l, r), cs) \<in> R"
      and *: "\<forall>(u, v) \<in> set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
      and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by (auto elim: cstep_n_SucE)
    let ?\<sigma> = "?h \<circ> \<sigma>"
    let ?C = "map_funs_ctxt h C"
    let ?cs = "map (map_funs_rule h) cs"
    have "((?h l, ?h r), ?cs) \<in> ?H R" using rule by (force simp: map_funs_crule_def)
    moreover have "?h s = ?C\<langle>?h l \<cdot> ?\<sigma>\<rangle>" and "?h t = ?C\<langle>?h r \<cdot> ?\<sigma>\<rangle>" by (auto simp: s t o_def)
    moreover have "\<forall>(u, v) \<in> set ?cs. (u \<cdot> ?\<sigma>, v \<cdot> ?\<sigma>) \<in> (cstep_n (?H R) n)\<^sup>*"
      using rtrancl_map [where f = ?h and r = "cstep_n R n", OF Suc.hyps]
        and * by (auto simp: o_def) force
    ultimately show ?case by (blast intro: cstep_n_SucI)
  qed simp
  then show ?thesis by (auto simp: cstep_iff)
qed

definition "trs2ctrs R = { (r, []) | r. r \<in> R }"

lemma cstep_n_subset:
  assumes "R \<subseteq> S"
  shows "cstep_n R n \<subseteq> cstep_n S n"
  using assms and rtrancl_mono [of "cstep_n R n" "cstep_n S n" for n]
  by (induct n) (auto elim!: cstep_n_SucE intro!: cstep_n_SucI split: prod.splits, blast)

lemma cstep_subset:
  assumes "R \<subseteq> S"
  shows "cstep R \<subseteq> cstep S"
  using cstep_n_subset [OF assms] by (force simp: cstep_iff)

lemma conds_sat_mono:
  assumes "R \<subseteq> S"
  shows "conds_sat R cs \<sigma> \<Longrightarrow> conds_sat S cs \<sigma>"
  using rtrancl_mono [OF cstep_subset [OF assms]] by (auto simp: conds_sat_iff)

definition "infeasible_at R i \<rho> \<longleftrightarrow> \<not> (\<exists>\<sigma>. conds_n_sat R (i - 1) (conds \<rho>) \<sigma>)"
definition "infeasible_rules_wrt S R \<longleftrightarrow> (\<forall>\<rho>\<in>R. \<forall>i. infeasible_at S i \<rho>)"

lemma inf_cstep_n:
  assumes "\<forall>\<rho>\<in>R. infeasible_at S n \<rho>" and "i \<le> n"
  shows "cstep_n (S - R) i = cstep_n S i"
  using assms
proof (induct i)
  case (Suc i)
  then have "(s, t) \<in> cstep_n (S - R) (Suc i)" if "(s, t) \<in> cstep_n S (Suc i)" for s t
    using that and cstep_n_mono [of i "n - 1" S, THEN rtrancl_mono, THEN subsetD]
    apply (cases n)
    apply (auto elim!: cstep_n_SucE intro!: cstep_n_SucI simp: infeasible_at_def conds_n_sat_iff)
    by (metis (no_types, lifting) case_prodI2 old.prod.case snd_conv)
  then show ?case using Suc
    using cstep_n_subset [THEN subsetD, of "S - R" S, OF Diff_subset, of _ "Suc i"]
    by (auto elim: cstep_n_SucE intro: cstep_n_SucI)
qed simp

lemma infeasible_rules_wrt_minimize:
  "infeasible_rules_wrt S R \<longleftrightarrow> infeasible_rules_wrt (S - R) R"
proof
  assume "infeasible_rules_wrt S R"
  then show "infeasible_rules_wrt (S - R) R"
    apply (auto simp: conds_n_sat_iff infeasible_rules_wrt_def infeasible_at_def)
    subgoal for l r c i \<sigma>
      using rtrancl_mono [OF cstep_n_subset, of "S - R" S, OF Diff_subset, of "i - Suc 0"]
      apply (drule_tac x = "((l, r), c)" in bspec)
       apply auto
      apply (drule_tac x = i in spec)
      apply (drule_tac x = \<sigma> in spec)
      apply auto
      done
    done
next
  assume assms: "infeasible_rules_wrt (S - R) R"
  show "infeasible_rules_wrt S R"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have *: "\<exists>i. \<exists>\<rho>\<in>R. \<not> infeasible_at S i \<rho>" by (auto simp: infeasible_rules_wrt_def)
    define m where "m = (LEAST i. \<exists>\<rho>\<in>R. \<not> infeasible_at S i \<rho>)"
    from LeastI_ex [OF *, folded m_def] obtain l r c
      where rule: "((l, r), c) \<in> R" and **: "\<not> infeasible_at S m ((l, r), c)" by force
    then have inf: "infeasible_at S i \<rho>" if "i < m" and "\<rho> \<in> R" for i \<rho>
      using that and not_less_Least [of i] unfolding m_def by blast
    show False
    proof (cases m)
      case 0
      then show ?thesis using assms and ** and rule
        apply (auto simp add: infeasible_at_def infeasible_rules_wrt_def)
        apply (drule_tac x = "((l, r), c)" in bspec)
         apply auto
        apply (drule_tac x = 0 in spec)
        apply auto
        done
    next
      case [simp]: (Suc k)
      have [simp]: "cstep_n (S - R) k = cstep_n S k"
        using inf by (intro inf_cstep_n [of _ _ k]) auto
      show ?thesis using ** and assms and rule
        apply (auto simp: infeasible_at_def infeasible_rules_wrt_def conds_n_sat_iff)
        apply (drule_tac x = "((l, r), c)" in bspec)
         apply auto
        apply (drule_tac x = m in spec)
        apply auto
        done
    qed
  qed
qed

lemma infeasible_rules_wrt_cstep_conv:
  assumes "infeasible_rules_wrt S R"
  shows "cstep S = cstep (S - R)"
  using assms and inf_cstep_n [of R S]
  by (auto simp: infeasible_rules_wrt_def cstep_iff) blast+

lemma goal_lifting:
  assumes
    "(Fun T [], Fun F []) \<notin> cstep (R \<union> { ((Fun T [], Fun F []), cs)})"  
  shows "\<not> conds_sat R cs \<sigma>"
proof
  let ?T = "Fun T []"
  let ?F = "Fun F []"
  let ?R = "{ ((?T,?F), cs)} \<union> R"
  assume "conds_sat R cs \<sigma>"
  from this[unfolded conds_sat_iff]
  have "\<forall> (s, t)\<in>set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*" by auto
  hence steps: "\<forall> (s, t)\<in>set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep ?R)\<^sup>*"
    using rtrancl_mono[OF cstep_subset[of R ?R]] by auto
  have "((?T,?F), cs) \<in> ?R" by auto
  from cstepI[OF this steps, of ?T Hole ?F]
  have "(?T,?F) \<in> cstep ?R" by auto
  with assms show False by auto
qed

end
