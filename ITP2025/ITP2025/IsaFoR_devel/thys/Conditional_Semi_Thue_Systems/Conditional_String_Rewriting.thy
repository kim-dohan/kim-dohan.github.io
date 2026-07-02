(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Conditional String Rewriting\<close>

theory Conditional_String_Rewriting
  imports
   "HOL-Library.Sublist"
   String_Rewriting
   ShortLex
begin

type_synonym csrule = "srule \<times> srule list"

text \<open>A conditional semi-Thue system\<close>
type_synonym csts = "csrule set"

text \<open>A conditional join string rewriting step of level @{term n}.\<close>
fun csr_p_join_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_p_join_step_n R 0 = {}" |
  csr_p_join_step_n_Suc: "csr_p_join_step_n R (Suc n) =
    {(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>)}"

(* Definition 24, second part *)
definition "csr_p_join_step R = (\<Union>n. csr_p_join_step_n R n)"

fun csr_semi_equational_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_semi_equational_step_n R 0 = {}" |
  csr_semi_equational_step_n_Suc: "csr_semi_equational_step_n R (Suc n) =
    {(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"

(* Definition 24, first part *)
definition "csr_semi_equational_step R = (\<Union>n. csr_semi_equational_step_n R n)"

fun csr_r_join_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_r_join_step_n R 0 = {}" |
  csr_r_join_step_n_Suc: "csr_r_join_step_n R (Suc n) =
    {(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) | C l r cs w.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n)\<^sup>\<down>)}"

(* Definition 23, second part *)
definition "csr_r_join_step R = (\<Union>n. csr_r_join_step_n R n)"

fun csr_r_semi_equational_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_r_semi_equational_step_n R 0 = {}" |
  csr_r_semi_equational_step_n_Suc: "csr_r_semi_equational_step_n R (Suc n) =
    {(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) | C l r cs w.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"

(* Definition 23, first part *)
definition "csr_r_semi_equational_step R = (\<Union>n. csr_r_semi_equational_step_n R n)"

fun csr_lr_semi_equational_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_lr_semi_equational_step_n R 0 = {}" |
  csr_lr_semi_equational_step_n_Suc: "csr_lr_semi_equational_step_n R (Suc n) =
    {(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) | C l r cs u w.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"

(* Definition 22, first part *)
definition "csr_lr_semi_equational_step R = (\<Union>n. csr_lr_semi_equational_step_n R n)"

fun csr_lr_join_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_lr_join_step_n R 0 = {}" |
  csr_lr_join_step_n_Suc: "csr_lr_join_step_n R (Suc n) =
    {(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) | C l r cs u w.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step_n R n)\<^sup>\<down>)}"

(* Definition 22, second part *)
definition "csr_lr_join_step R = (\<Union>n. csr_lr_join_step_n R n)"

definition app_list :: "string \<Rightarrow> srule list \<Rightarrow> srule list"
where
  "app_list y ls = map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) ls"

lemma csr_p_join_step_iff:
  "(s, t) \<in> csr_p_join_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_p_join_step_n R n)"
  by (auto simp: csr_p_join_step_def)

lemma csr_semi_equational_step_iff:
  "(s, t) \<in> csr_semi_equational_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_semi_equational_step_n R n)"
  by (auto simp: csr_semi_equational_step_def)

lemma csr_lr_join_step_iff:
  "(s, t) \<in> csr_lr_join_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_lr_join_step_n R n)"
  by (auto simp: csr_lr_join_step_def)

lemma csr_r_join_step_iff:
  "(s, t) \<in> csr_r_join_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_r_join_step_n R n)"
  by (auto simp: csr_r_join_step_def)

lemma csr_r_semi_equational_step_iff:
  "(s, t) \<in> csr_r_semi_equational_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_r_semi_equational_step_n R n)"
  by (auto simp: csr_r_semi_equational_step_def)

lemma csr_lr_semi_equational_step_iff:
  "(s, t) \<in> csr_lr_semi_equational_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_lr_semi_equational_step_n R n)"
  by (auto simp: csr_lr_semi_equational_step_def)

lemma csr_p_join_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_p_join_step_n R n"
  shows "(s, t) \<in> csr_p_join_step R"
  using assms by (auto simp: csr_p_join_step_iff)

lemma csr_semi_equational_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_semi_equational_step_n R n"
  shows "(s, t) \<in> csr_semi_equational_step R"
  using assms by (auto simp: csr_semi_equational_step_iff)

lemma csr_lr_join_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_lr_join_step_n R n"
  shows "(s, t) \<in> csr_lr_join_step R"
  using assms by (auto simp: csr_lr_join_step_iff)

lemma csr_r_join_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_r_join_step_n R n"
  shows "(s, t) \<in> csr_r_join_step R"
  using assms by (auto simp: csr_r_join_step_iff)

lemma csr_r_semi_equational_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_r_semi_equational_step_n R n"
  shows "(s, t) \<in> csr_r_semi_equational_step R"
  using assms by (auto simp: csr_r_semi_equational_step_iff)

lemma csr_lr_semi_equational_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_lr_semi_equational_step_n R n"
  shows "(s, t) \<in> csr_lr_semi_equational_step R"
  using assms by (auto simp: csr_lr_semi_equational_step_iff)

lemma csr_p_join_steps_n_imp_csteps:
  assumes "(s, t) \<in> (csr_p_join_step_n R n)\<^sup>*"
  shows "(s, t) \<in> (csr_p_join_step R)\<^sup>*"
  using assms by (induct; auto dest: csr_p_join_step_n_imp_cstep)

lemma csr_semi_equational_steps_n_imp_csr_semi_equational_steps:
  assumes "(s, t) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(s, t) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms by (induct; auto dest: csr_semi_equational_step_n_imp_cstep) 
    (metis conversion_mono csr_semi_equational_step_n_imp_cstep old.prod.exhaust subset_eq)

lemma csr_lr_join_steps_n_imp_csteps:
  assumes "(s, t) \<in> (csr_lr_join_step_n R n)\<^sup>*"
  shows "(s, t) \<in> (csr_lr_join_step R)\<^sup>*"
  using assms by (induct; auto dest: csr_lr_join_step_n_imp_cstep)

lemma csr_r_join_steps_n_imp_csteps:
  assumes "(s, t) \<in> (csr_r_join_step_n R n)\<^sup>*"
  shows "(s, t) \<in> (csr_r_join_step R)\<^sup>*"
  using assms by (induct; auto dest: csr_r_join_step_n_imp_cstep)

lemma csr_r_semi_equational_steps_n_imp_csteps:
  assumes "(s, t) \<in> (csr_r_semi_equational_step_n R n)\<^sup>*"
  shows "(s, t) \<in> (csr_r_semi_equational_step R)\<^sup>*"
  using assms by (induct; auto dest: csr_r_semi_equational_step_n_imp_cstep)

lemma csr_lr_semi_equational_steps_n_imp_csteps:
  assumes "(s, t) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>*"
  shows "(s, t) \<in> (csr_lr_semi_equational_step R)\<^sup>*"
  using assms by (induct; auto dest: csr_lr_semi_equational_step_n_imp_cstep)

lemma csr_p_join_steps_n_subset_csteps:
  "(csr_p_join_step_n R n)\<^sup>* \<subseteq> (csr_p_join_step R)\<^sup>*"
  by (auto dest: csr_p_join_steps_n_imp_csteps)

lemma csr_semi_equational_steps_n_subset_csr_semi_equational_steps:
  "(csr_semi_equational_step_n R n)\<^sup>* \<subseteq> (csr_semi_equational_step R)\<^sup>*"
  by (auto, metis csr_semi_equational_step_iff rtrancl_mono subset_eq surj_pair)

lemma csr_lr_join_steps_n_subset_csteps:
  "(csr_lr_join_step_n R n)\<^sup>* \<subseteq> (csr_lr_join_step R)\<^sup>*"
  by (auto dest: csr_lr_join_steps_n_imp_csteps)

lemma csr_r_join_steps_n_subset_csteps:
  "(csr_r_join_step_n R n)\<^sup>* \<subseteq> (csr_r_join_step R)\<^sup>*"
  by (auto dest: csr_r_join_steps_n_imp_csteps)

lemma csr_r_semi_equational_steps_n_subset_csteps:
  "(csr_r_semi_equational_step_n R n)\<^sup>* \<subseteq> (csr_r_semi_equational_step R)\<^sup>*"
  by (auto dest: csr_r_semi_equational_steps_n_imp_csteps)

lemma csr_lr_semi_equational_steps_n_subset_csteps:
  "(csr_lr_semi_equational_step_n R n)\<^sup>* \<subseteq> (csr_lr_semi_equational_step R)\<^sup>*"
  by (auto dest: csr_lr_semi_equational_steps_n_imp_csteps)

lemma csr_p_join_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>"
    and "s = C\<llangle>l\<rrangle> "
    and "t = C\<llangle>r\<rrangle>"
  shows "(s, t) \<in> csr_p_join_step_n R (Suc n)"
  using assms by auto

lemma csr_semi_equational_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>l\<rrangle> "
    and "t = C\<llangle>r\<rrangle>"
  shows "(s, t) \<in> csr_semi_equational_step_n R (Suc n)"
  using assms by auto

lemma csr_lr_join_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step_n R n)\<^sup>\<down>"
    and "s = C\<llangle>u @ l @ w\<rrangle> "
    and "t = C\<llangle>u @ r @ w\<rrangle>"
  shows "(s, t) \<in> csr_lr_join_step_n R (Suc n)"
  using assms by fastforce

lemma csr_r_join_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n)\<^sup>\<down>"
    and "s = C\<llangle>l @ w\<rrangle> "
    and "t = C\<llangle>r @ w\<rrangle>"
  shows "(s, t) \<in> csr_r_join_step_n R (Suc n)"
  using assms by fastforce

lemma csr_r_semi_equational_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>l @ w\<rrangle>"
    and "t = C\<llangle>r @ w\<rrangle>"
  shows "(s, t) \<in> csr_r_semi_equational_step_n R (Suc n)"
  using assms by fastforce

lemma csr_lr_semi_equational_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>u @ l @ w\<rrangle>"
    and "t = C\<llangle>u @ r @ w\<rrangle>"
  shows "(s, t) \<in> csr_lr_semi_equational_step_n R (Suc n)"
  using assms by fastforce

lemma csr_p_join_step_n_SucE:
  assumes "(s, t) \<in> csr_p_join_step_n R (Suc n)"
  obtains C l r cs where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>"
    and "s = C\<llangle>l\<rrangle>"
    and "t = C\<llangle>r\<rrangle>"
  using assms by auto

lemma csr_semi_equational_step_n_SucE:
  assumes "(s, t) \<in> csr_semi_equational_step_n R (Suc n)"
  obtains C l r cs where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>l\<rrangle>"
    and "t = C\<llangle>r\<rrangle>"
  using assms by auto

lemma csr_lr_join_step_n_SucE:
  assumes "(s, t) \<in> csr_lr_join_step_n R (Suc n)"
  obtains C D l r cs u w where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step_n R n)\<^sup>\<down>"
    and "s = C\<llangle>u @ l @ w\<rrangle>"
    and "t = C\<llangle>u @ r @ w\<rrangle>"
  using assms by auto

lemma csr_r_join_step_n_SucE:
  assumes "(s, t) \<in> csr_r_join_step_n R (Suc n)"
  obtains C l r w cs where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n)\<^sup>\<down>"
    and "s = C\<llangle>l @ w\<rrangle>"
    and "t = C\<llangle>r @ w\<rrangle>"
  using assms by auto

lemma csr_r_semi_equational_step_n_SucE:
  assumes "(s, t) \<in> csr_r_semi_equational_step_n R (Suc n)"
  obtains C l r w cs where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>l @ w\<rrangle>"
    and "t = C\<llangle>r @ w\<rrangle>"
  using assms by auto

lemma csr_lr_semi_equational_step_n_SucE:
  assumes "(s, t) \<in> csr_lr_semi_equational_step_n R (Suc n)"
  obtains C l r u w cs where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>u @ l @ w\<rrangle>"
    and "t = C\<llangle>u @ r @ w\<rrangle>"
  using assms by auto

lemma csr_p_join_step_n_E:
  assumes "(s, t) \<in> csr_p_join_step_n R n"
  obtains C l r w cs n' where "((l, r), cs) \<in> R" and "n = Suc n'"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n')\<^sup>\<down>"
    and "s = C\<llangle>l\<rrangle>"
    and "t = C\<llangle>r\<rrangle>"
  using assms by (cases n, auto)

lemma csr_semi_equational_step_n_E:
  assumes "(s, t) \<in> csr_semi_equational_step_n R n"
  obtains C l r w cs n' where "((l, r), cs) \<in> R" and "n = Suc n'"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n')\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>l\<rrangle>"
    and "t = C\<llangle>r\<rrangle>"
  using assms by (cases n, auto)

lemma csr_r_join_step_n_E:
  assumes "(s, t) \<in> csr_r_join_step_n R n"
  obtains C l r w cs n' where "((l, r), cs) \<in> R" and "n = Suc n'"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n')\<^sup>\<down>"
    and "s = C\<llangle>l @ w\<rrangle>"
    and "t = C\<llangle>r @ w\<rrangle>"
  using assms by (cases n, auto)

lemma csr_lr_join_step_n_E:
  assumes "(s, t) \<in> csr_lr_join_step_n R n"
  obtains C l r u w cs n' where "((l, r), cs) \<in> R" and "n = Suc n'"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step_n R n')\<^sup>\<down>"
    and "s = C\<llangle>u @ l @ w\<rrangle>"
    and "t = C\<llangle>u @ r @ w\<rrangle>"
  using assms by (cases n, auto)

lemma csr_r_semi_equational_step_n_E:
  assumes "(s, t) \<in> csr_r_semi_equational_step_n R n"
  obtains C l r w cs n' where "((l, r), cs) \<in> R" and "n = Suc n'"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n')\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>l @ w\<rrangle>"
    and "t = C\<llangle>r @ w\<rrangle>"
  using assms by (cases n, auto)

lemma csr_lr_semi_equational_step_n_E:
  assumes "(s, t) \<in> csr_lr_semi_equational_step_n R n"
  obtains C l r u w cs n' where "((l, r), cs) \<in> R" and "n = Suc n'"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n')\<^sup>\<leftrightarrow>\<^sup>*"
    and "s = C\<llangle>u @ l @ w\<rrangle>"
    and "t = C\<llangle>u @ r @ w\<rrangle>"
  using assms by (cases n, auto)

lemma csr_p_join_step_n_Suc_mono:
  "csr_p_join_step_n R n \<subseteq> csr_p_join_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  show ?case
    using rtrancl_mono [OF Suc] 
    by (auto, smt (z3) in_mono join_def join_mono rtrancl_converse rtrancl_idemp)
qed simp

lemma csr_semi_equational_step_n_Suc_mono:
  "csr_semi_equational_step_n R n \<subseteq> csr_semi_equational_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  then show ?case by (auto, smt (verit, ccfv_threshold) conversion_mono in_mono)
qed simp

lemma csr_lr_join_step_n_Suc_mono:
  "csr_lr_join_step_n R n \<subseteq> csr_lr_join_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  show ?case
    using rtrancl_mono [OF Suc] 
    by (auto elim!: csr_lr_join_step_n_SucE intro!: csr_lr_join_step_n_SucI) 
      (smt (z3) case_prodD case_prodI2 in_mono joinD joinI)
qed simp

lemma csr_r_join_step_n_Suc_mono:
  "csr_r_join_step_n R n \<subseteq> csr_r_join_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  then show ?case
    by (auto, smt (z3) case_prodD case_prodI2 in_mono join_mono) 
qed simp

lemma csr_r_semi_equational_step_n_Suc_mono:
  "csr_r_semi_equational_step_n R n \<subseteq> csr_r_semi_equational_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  then show ?case using conversion_mono
    by (auto, smt (z3) case_prodD case_prodI2 in_mono) 
qed simp

lemma csr_lr_semi_equational_step_n_Suc_mono:
  "csr_lr_semi_equational_step_n R n \<subseteq> csr_lr_semi_equational_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  then show ?case using conversion_mono
    by (auto, smt (z3) case_prodD case_prodI2 in_mono) 
qed simp

lemma csr_p_join_step_n_mono:
  assumes "i \<le> n"
  shows "csr_p_join_step_n R i \<subseteq> csr_p_join_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_p_join_step_n R (Suc i) \<subseteq> csr_p_join_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_p_join_step_n_Suc_mono in_mono)
qed simp

lemma csr_semi_equational_step_n_mono:
  assumes "i \<le> n"
  shows "csr_semi_equational_step_n R i \<subseteq> csr_semi_equational_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_semi_equational_step_n R (Suc i) \<subseteq> csr_semi_equational_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_semi_equational_step_n_Suc_mono in_mono)
qed simp

lemma csr_lr_join_step_n_mono:
  assumes "i \<le> n"
  shows "csr_lr_join_step_n R i \<subseteq> csr_lr_join_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_lr_join_step_n R (Suc i) \<subseteq> csr_lr_join_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_lr_join_step_n_Suc_mono in_mono)
qed simp

lemma csr_r_join_step_n_mono:
  assumes "i \<le> n"
  shows "csr_r_join_step_n R i \<subseteq> csr_r_join_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_r_join_step_n R (Suc i) \<subseteq> csr_r_join_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_r_join_step_n_Suc_mono in_mono)
qed simp

lemma csr_r_semi_equational_step_n_mono:
  assumes "i \<le> n"
  shows "csr_r_semi_equational_step_n R i \<subseteq> csr_r_semi_equational_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_r_semi_equational_step_n R (Suc i) \<subseteq> csr_r_semi_equational_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_r_semi_equational_step_n_Suc_mono in_mono)
qed simp

lemma csr_lr_semi_equational_step_n_mono:
  assumes "i \<le> n"
  shows "csr_lr_semi_equational_step_n R i \<subseteq> csr_lr_semi_equational_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_lr_semi_equational_step_n R (Suc i) \<subseteq> csr_lr_semi_equational_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_lr_semi_equational_step_n_Suc_mono in_mono)
qed simp

lemma csr_p_join_steps_imp_csr_steps_n:
  assumes "(s, t) \<in> (csr_p_join_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_p_join_step_n R n)\<^sup>*"
  using assms csr_p_join_step_iff 
  by (induct, auto, meson csr_p_join_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD)

lemma csr_semi_equational_steps_imp_csr_semi_equational_steps_n:
  assumes "(s, t) \<in> (csr_semi_equational_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_semi_equational_step_n R n)\<^sup>*"
  using assms csr_semi_equational_step_iff 
  by (induct, auto, meson csr_semi_equational_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD)

lemma csr_lr_join_steps_imp_csr_lr_steps_n:
  assumes "(s, t) \<in> (csr_lr_join_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_lr_join_step_n R n)\<^sup>*"
  using assms csr_lr_join_step_iff 
  by (induct, auto, meson csr_lr_join_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD) 

lemma csr_r_join_steps_imp_csr_r_steps_n:
  assumes "(s, t) \<in> (csr_r_join_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_r_join_step_n R n)\<^sup>*"
  using assms csr_r_join_step_iff 
  by (induct, auto, meson csr_r_join_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD)

lemma csr_r_semi_equational_steps_imp_csr_r_semi_equational_steps_n:
  assumes "(s, t) \<in> (csr_r_semi_equational_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_r_semi_equational_step_n R n)\<^sup>*"
  using assms csr_r_semi_equational_step_iff 
  by (induct, auto, meson csr_r_semi_equational_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD)

lemma csr_lr_semi_equational_steps_imp_csr_lr_semi_equational_steps_n:
  assumes "(s, t) \<in> (csr_lr_semi_equational_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>*"
  using assms csr_lr_semi_equational_step_iff 
  by (induct, auto, meson csr_lr_semi_equational_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD)

lemma csr_p_join_steps_imp_csr_p_join_steps_n:
  assumes "(s, t) \<in> (csr_p_join_step R)\<^sup>\<down>"
  shows "\<exists>n. (s, t) \<in> (csr_p_join_step_n R n)\<^sup>\<down>"
proof -
  from assms obtain u where su:"(s, u) \<in> (csr_p_join_step R)\<^sup>*" and tu:"(t, u) \<in> (csr_p_join_step R)\<^sup>*" by auto
  from su have *:"\<exists>m. (s, u) \<in> (csr_p_join_step_n R m)\<^sup>*" using csr_p_join_steps_imp_csr_steps_n by blast
  from tu have **:"\<exists>n. (t, u) \<in> (csr_p_join_step_n R n)\<^sup>*" using csr_p_join_steps_imp_csr_steps_n by blast
  from * ** have "\<exists>max. (s, u) \<in> (csr_p_join_step_n R max)\<^sup>* \<and> (t, u) \<in> (csr_p_join_step_n R max)\<^sup>*" 
    by (meson csr_p_join_step_n_mono in_mono linorder_le_cases rtrancl_mono)
  then show ?thesis by auto
qed

lemma csr_semi_equational_conv_steps_imp_csr_semi_equational_conv_steps_n:
  assumes "(s, t) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" 
proof -
  from assms obtain m where "(s, t) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>^^m" by auto
  then show ?thesis
  proof(induct m arbitrary: t)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    from Suc(2) obtain u where su:"(s, u) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow> ^^ m" and ut:"(u, t) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>" by auto
    from su Suc(1) obtain n where *:"(s, u) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" by blast
    from ut obtain k where **:"(u, t) \<in> (csr_semi_equational_step_n R k)\<^sup>\<leftrightarrow>"
      using csr_semi_equational_step_iff by blast+
    from * ** have max:"\<exists>max. (s, u) \<in> (csr_semi_equational_step_n R max)\<^sup>\<leftrightarrow>\<^sup>* \<and> (u, t) \<in> (csr_semi_equational_step_n R max)\<^sup>\<leftrightarrow>"
      using conversion_mono csr_semi_equational_step_n_mono nat_le_linear linorder_le_cases subsetD 
      by (auto, (smt (verit, best) conversion_mono subset_iff)+)
    then show ?case 
      by (auto, (metis conversion_def rtrancl.rtrancl_into_rtrancl)+)    
  qed
qed

lemma csr_r_join_steps_imp_csr_r_join_steps_n:
  assumes st:"(s, t) \<in> (csr_r_join_step R)\<^sup>\<down>"
  shows "\<exists>n. (s, t) \<in> (csr_r_join_step_n R n)\<^sup>\<down>"
proof -
  from st have "\<exists>u. (s, u) \<in> (csr_r_join_step R)\<^sup>* \<and> (t, u) \<in> (csr_r_join_step R)\<^sup>*" by auto
  then obtain u where su:"(s, u) \<in> (csr_r_join_step R)\<^sup>*" and tu:"(t, u) \<in> (csr_r_join_step R)\<^sup>*" by auto
  from su have *:"\<exists>m. (s, u) \<in> (csr_r_join_step_n R m)\<^sup>*" using csr_r_join_steps_imp_csr_r_steps_n by blast
  from tu have **:"\<exists>n. (t, u) \<in> (csr_r_join_step_n R n)\<^sup>*" using csr_r_join_steps_imp_csr_r_steps_n by blast
  from * ** have "\<exists>max. (s, u) \<in> (csr_r_join_step_n R max)\<^sup>* \<and> (t, u) \<in> (csr_r_join_step_n R max)\<^sup>*" 
    by (meson csr_r_join_step_n_mono in_mono linorder_le_cases rtrancl_mono)
  then show ?thesis by auto
qed

lemma csr_lr_join_steps_imp_csr_lr_join_steps_n:
  assumes st:"(s, t) \<in> (csr_lr_join_step R)\<^sup>\<down>"
  shows "\<exists>n. (s, t) \<in> (csr_lr_join_step_n R n)\<^sup>\<down>"
proof -
  from st have "\<exists>u. (s, u) \<in> (csr_lr_join_step R)\<^sup>* \<and> (t, u) \<in> (csr_lr_join_step R)\<^sup>*" by auto
  then obtain u where su:"(s, u) \<in> (csr_lr_join_step R)\<^sup>*" and tu:"(t, u) \<in> (csr_lr_join_step R)\<^sup>*" by auto
  from su have *:"\<exists>m. (s, u) \<in> (csr_lr_join_step_n R m)\<^sup>*" using csr_lr_join_steps_imp_csr_lr_steps_n by blast
  from tu have **:"\<exists>n. (t, u) \<in> (csr_lr_join_step_n R n)\<^sup>*" using csr_lr_join_steps_imp_csr_lr_steps_n by blast
  from * ** have "\<exists>max. (s, u) \<in> (csr_lr_join_step_n R max)\<^sup>* \<and> (t, u) \<in> (csr_lr_join_step_n R max)\<^sup>*" 
    by (meson csr_lr_join_step_n_mono in_mono linorder_le_cases rtrancl_mono)
  then show ?thesis by auto
qed

lemma csr_r_semi_equational_conv_steps_imp_csr_r_semi_equational_conv_steps_n:
  assumes "(s, t) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" 
proof -
  from assms obtain m where "(s, t) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>^^m" by auto
  then show ?thesis
  proof(induct m arbitrary: t)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    from Suc(2) obtain u where su:"(s, u) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow> ^^ m" and ut:"(u, t) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>" by auto
    from su Suc(1) obtain n where *:"(s, u) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" by blast
    from ut obtain k where **:"(u, t) \<in> (csr_r_semi_equational_step_n R k)\<^sup>\<leftrightarrow>"
      using csr_r_semi_equational_step_iff by blast+
    from * ** have max:"\<exists>max. (s, u) \<in> (csr_r_semi_equational_step_n R max)\<^sup>\<leftrightarrow>\<^sup>* \<and> (u, t) \<in> (csr_r_semi_equational_step_n R max)\<^sup>\<leftrightarrow>"
      using conversion_mono csr_r_semi_equational_step_n_mono nat_le_linear linorder_le_cases subsetD 
      by (auto, (smt (verit, best) conversion_mono subset_iff)+)
    then show ?case 
      by (auto, (metis conversion_def rtrancl.rtrancl_into_rtrancl)+)    
  qed
qed

lemma csr_lr_semi_equational_conv_steps_imp_csr_lr_semi_equational_conv_steps_n:
  assumes "(s, t) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" 
proof -
  from assms obtain m where "(s, t) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>^^m" by auto
  then show ?thesis
  proof(induct m arbitrary: t)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    from Suc(2) obtain u where su:"(s, u) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow> ^^ m" and ut:"(u, t) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>" by auto
    from su Suc(1) obtain n where *:"(s, u) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" by blast
    from ut obtain k where **:"(u, t) \<in> (csr_lr_semi_equational_step_n R k)\<^sup>\<leftrightarrow>"
      using csr_lr_semi_equational_step_iff by blast+
    from * ** have max:"\<exists>max. (s, u) \<in> (csr_lr_semi_equational_step_n R max)\<^sup>\<leftrightarrow>\<^sup>* \<and> (u, t) \<in> (csr_lr_semi_equational_step_n R max)\<^sup>\<leftrightarrow>"
      using conversion_mono csr_lr_semi_equational_step_n_mono nat_le_linear linorder_le_cases subsetD 
      by (auto, (smt (verit, best) conversion_mono subset_iff)+)
    then show ?case 
      by (auto, (metis conversion_def rtrancl.rtrancl_into_rtrancl)+)    
  qed
qed


lemma all_csr_p_join_step_imp_csr_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_p_join_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_p_join_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms csr_p_join_steps_imp_csr_steps_n by auto
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_p_join_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * 
    by (meson joinD joinI subset_eq)
  then show ?thesis ..
qed

lemma all_csr_semi_equational_step_imp_csr_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_semi_equational_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_semi_equational_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms csr_semi_equational_steps_imp_csr_semi_equational_steps_n by auto
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_semi_equational_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * 
    by (meson joinD joinI subset_eq)
  then show ?thesis ..
qed

lemma all_csr_p_join_step_imp_csr_p_join_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_p_join_step R)\<^sup>\<down>"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms csr_p_join_steps_imp_csr_p_join_steps_n by auto 
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_p_join_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * 
    by (meson joinD joinI subset_eq)
  then show ?thesis ..
qed

lemma all_csr_semi_equational_step_imp_csr_semi_equational_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms using csr_semi_equational_conv_steps_imp_csr_semi_equational_conv_steps_n by auto
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_semi_equational_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * 
      by (meson conversion_mono csr_semi_equational_step_n_mono subset_iff)
  then show ?thesis ..
qed

lemma all_csr_lr_join_step_imp_csr_lr_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_join_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_join_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms by (auto intro: csr_lr_join_steps_imp_csr_lr_steps_n)
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_lr_join_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * by blast
  then show ?thesis ..
qed

lemma all_csr_r_join_step_imp_csr_r_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_join_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_join_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms by (auto intro: csr_r_join_steps_imp_csr_r_steps_n)
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_r_join_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * by blast
  then show ?thesis ..
qed

lemma all_csr_r_join_step_imp_csr_r_join_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_join_step R)\<^sup>\<down>"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_join_step_n R n)\<^sup>\<down>" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms by (auto intro: csr_r_join_steps_imp_csr_r_join_steps_n)
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_r_join_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and *
    by (meson in_mono joinD joinI)
  then show ?thesis ..
qed

lemma all_csr_lr_join_step_imp_csr_lr_join_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_join_step R)\<^sup>\<down>"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_join_step_n R n)\<^sup>\<down>" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms by (auto intro: csr_lr_join_steps_imp_csr_lr_join_steps_n)
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_lr_join_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and *
    by (meson in_mono joinD joinI)
  then show ?thesis ..
qed

lemma all_csr_r_semi_equational_step_imp_csr_r_semi_equational_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_semi_equational_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_semi_equational_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms using csr_r_semi_equational_steps_imp_csr_r_semi_equational_steps_n by auto
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  hence "\<forall>i < k. ?P i n"
    using csr_r_semi_equational_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * 
      by (meson conversion_mono subset_iff)
  then show ?thesis ..
qed

lemma all_csr_lr_semi_equational_step_imp_csr_lr_semi_equational_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_semi_equational_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms using csr_lr_semi_equational_steps_imp_csr_lr_semi_equational_steps_n by auto
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  hence "\<forall>i < k. ?P i n"
    using csr_lr_semi_equational_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * 
      by (meson conversion_mono subset_iff)
  then show ?thesis ..
qed

lemma all_csr_r_semi_equational_step_imp_csr_semi_equational_conv_r_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms using csr_r_semi_equational_conv_steps_imp_csr_r_semi_equational_conv_steps_n by auto
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  hence "\<forall>i < k. ?P i n"
    using csr_r_semi_equational_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * 
      by (meson conversion_mono csr_r_semi_equational_step_n_mono subset_iff)
  then show ?thesis ..
qed

lemma all_csr_lr_semi_equational_step_imp_csr_semi_equational_conv_lr_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms using csr_lr_semi_equational_conv_steps_imp_csr_lr_semi_equational_conv_steps_n by auto
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  hence "\<forall>i < k. ?P i n"
    using csr_lr_semi_equational_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * 
      by (meson conversion_mono csr_lr_semi_equational_step_n_mono subset_iff)
  then show ?thesis ..
qed

lemma csr_p_join_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step R)\<^sup>\<down>"
  shows "(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) \<in> csr_p_join_step R" using assms 
proof -
  obtain n where ncs:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>"
  using all_csr_p_join_step_imp_csr_p_join_step_n[of "length cs" "\<lambda>i. fst (cs ! i)" "\<lambda>i. snd (cs ! i)" R]
  and conds
    by (auto simp: all_set_conv_all_nth split_beta')
  hence "(l, r) \<in> csr_p_join_step_n R (Suc n)" using assms csr_p_join_step_n_SucI
    by (auto, metis  sctxt.cop_nil)
  then show ?thesis using csr_p_join_step_iff 
    by (metis ncs assms(1) csr_p_join_step_n_SucI)
qed

lemma csr_semi_equational_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) \<in> csr_semi_equational_step R" using assms 
proof -
  obtain n where ncs:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
  using all_csr_semi_equational_step_imp_csr_semi_equational_step_n[of "length cs" "\<lambda>i. fst (cs ! i)" "\<lambda>i. snd (cs ! i)" R]
  and conds
    by (auto simp: all_set_conv_all_nth split_beta')
  hence "(l, r) \<in> csr_semi_equational_step_n R (Suc n)" using assms csr_p_join_step_n_SucI
    by (auto, metis  sctxt.cop_nil)
  then show ?thesis using csr_semi_equational_step_iff 
    by (metis ncs assms(1) csr_semi_equational_step_n_SucI)
qed

lemma csr_r_join_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step R)\<^sup>\<down>"
  shows "(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) \<in> csr_r_join_step R" using assms 
proof -
  obtain n where "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n)\<^sup>\<down>"
  using all_csr_r_join_step_imp_csr_r_join_step_n[of "length cs" "\<lambda>i. fst (cs ! i) @ w" "\<lambda>i. snd (cs ! i) @ w" R]
  and conds assms
    by (auto simp: all_set_conv_all_nth split_beta')
  hence "(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) \<in> csr_r_join_step_n R (Suc n)" using assms csr_r_join_step_n_SucI 
    by blast
  then show ?thesis using csr_r_join_step_iff by blast
qed

lemma csr_lr_join_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step R)\<^sup>\<down>"
  shows "(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) \<in> csr_lr_join_step R" using assms 
proof -
  obtain n where "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step_n R n)\<^sup>\<down>"
  using all_csr_lr_join_step_imp_csr_lr_join_step_n[of "length cs" "\<lambda>i. u @ fst (cs ! i) @ w" "\<lambda>i. u @ snd (cs ! i) @ w" R]
  and conds assms
    by (auto simp: all_set_conv_all_nth split_beta')
  hence "(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) \<in> csr_lr_join_step_n R (Suc n)" using assms csr_lr_join_step_n_SucI 
    by blast
  then show ?thesis using csr_lr_join_step_iff by blast
qed

lemma csr_r_semi_equational_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) \<in> csr_r_semi_equational_step R" using assms 
proof -
  obtain n where "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
  using all_csr_r_semi_equational_step_imp_csr_semi_equational_conv_r_step_n[of "length cs" "\<lambda>i. fst (cs ! i) @ w" "\<lambda>i. snd (cs ! i) @ w" R]
  and conds assms by (auto simp: all_set_conv_all_nth split_beta')
  hence "(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) \<in> csr_r_semi_equational_step_n R (Suc n)" using assms csr_r_semi_equational_step_n_SucI 
    by blast
  then show ?thesis using csr_r_semi_equational_step_iff by blast
qed

lemma csr_lr_semi_equational_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) \<in> csr_lr_semi_equational_step R" using assms 
proof -
  obtain n where "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
  using all_csr_lr_semi_equational_step_imp_csr_semi_equational_conv_lr_step_n[of "length cs" "\<lambda>i. u @ fst (cs ! i) @ w" "\<lambda>i. u @ snd (cs ! i) @ w" R]
  and conds assms by (auto simp: all_set_conv_all_nth split_beta')
  hence "(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) \<in> csr_lr_semi_equational_step_n R (Suc n)" using assms csr_lr_semi_equational_step_n_SucI 
    by blast
  then show ?thesis using csr_lr_semi_equational_step_iff by blast
qed

lemma csr_p_join_step_n_ctxt:
  assumes "(s, t) \<in> csr_p_join_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_p_join_step_n R n" using assms
  by (cases n, auto, metis sctxt.cop_add, insert csr_p_join_step_n_SucE)

lemma csr_semi_equational_step_n_ctxt:
  assumes "(s, t) \<in> csr_semi_equational_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_semi_equational_step_n R n" using assms
  by (cases n, auto, metis sctxt.cop_add)

lemma csr_r_join_step_n_ctxt:
  assumes "(s, t) \<in> csr_r_join_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_r_join_step_n R n" using assms csr_r_join_step_n_SucE
  by (cases n, auto, metis (no_types, lifting) sctxt.cop_add)

lemma csr_lr_join_step_n_ctxt:
  assumes "(s, t) \<in> csr_lr_join_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_lr_join_step_n R n" using assms
  by (cases n, auto, metis (no_types, lifting) sctxt.cop_add)

lemma csr_r_semi_equational_step_n_ctxt:
  assumes "(s, t) \<in> csr_r_semi_equational_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_r_semi_equational_step_n R n" using assms csr_r_semi_equational_step_n_SucE
  by (cases n, auto, metis (no_types, lifting) sctxt.cop_add)

lemma csr_lr_semi_equational_step_n_ctxt:
  assumes "(s, t) \<in> csr_lr_semi_equational_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_lr_semi_equational_step_n R n" using assms csr_lr_semi_equational_step_n_SucE
  by (cases n, auto, metis (no_types, lifting) sctxt.cop_add)

lemma csr_p_join_step_ctxt_closed:
  "sctxt.closed (csr_p_join_step R)"
  by (rule sctxt.closedI) (auto intro: csr_p_join_step_n_ctxt simp: csr_p_join_step_iff)

lemma csr_semi_equational_step_ctxt_closed:
  "sctxt.closed (csr_semi_equational_step R)"
  by (rule sctxt.closedI) (auto intro: csr_semi_equational_step_n_ctxt simp: csr_semi_equational_step_iff)

lemma csr_r_semi_equational_step_ctxt_closed:
  "sctxt.closed (csr_r_semi_equational_step R)"
  by (rule sctxt.closedI) (auto intro: csr_r_semi_equational_step_n_ctxt simp: csr_r_semi_equational_step_iff)

lemma csr_lr_semi_equational_step_ctxt_closed:
  "sctxt.closed (csr_lr_semi_equational_step R)"
  by (rule sctxt.closedI) (auto intro: csr_lr_semi_equational_step_n_ctxt simp: csr_lr_semi_equational_step_iff)

lemma csr_join_sctxt_closed: assumes "(s, t) \<in> (csr_p_join_step R)\<^sup>*"
  shows "(u @ s @ v, u @ t @ v) \<in> (csr_p_join_step R)\<^sup>*" using assms csr_p_join_step_ctxt_closed 
    sctxt.closed_rtrancl sctxt_closed_strings by auto

lemma csr_semi_equational_sctxt_closed: assumes "(s, t) \<in> (csr_semi_equational_step R)\<^sup>*"
  shows "(u @ s @ v, u @ t @ v) \<in> (csr_semi_equational_step R)\<^sup>*" using assms csr_semi_equational_step_ctxt_closed 
    sctxt.closed_rtrancl sctxt_closed_strings by auto

lemma csr_r_semi_equational_sctxt_closed: assumes "(s, t) \<in> (csr_r_semi_equational_step R)\<^sup>*"
  shows "(u @ s @ v, u @ t @ v) \<in> (csr_r_semi_equational_step R)\<^sup>*" using assms csr_r_semi_equational_step_ctxt_closed
  by (simp add: sctxt.closed_rtrancl sctxt_closed_strings)

lemma csr_lr_semi_equational_sctxt_closed: assumes "(s, t) \<in> (csr_lr_semi_equational_step R)\<^sup>*"
  shows "(u @ s @ v, u @ t @ v) \<in> (csr_lr_semi_equational_step R)\<^sup>*" using assms csr_lr_semi_equational_step_ctxt_closed
   by (simp add: sctxt.closed_rtrancl sctxt_closed_strings)

lemma csr_lr_join_step_ctxt_closed:
  "sctxt.closed (csr_lr_join_step R)"
  by (rule sctxt.closedI) (auto intro: csr_lr_join_step_n_ctxt simp: csr_lr_join_step_iff)

lemma csr_r_join_step_ctxt_closed:
  "sctxt.closed (csr_r_join_step R)"
  by (rule sctxt.closedI) (auto intro: csr_r_join_step_n_ctxt simp: csr_r_join_step_iff)

lemma csr_lr_join_sctxt_closed: assumes "(s, t) \<in> (csr_lr_join_step R)\<^sup>*"
  shows "(u @ s @ v, u @ t @ v) \<in> (csr_lr_join_step R)\<^sup>*" using assms csr_lr_join_step_ctxt_closed 
    sctxt.closed_rtrancl sctxt_closed_strings by auto

lemma csr_r_join_sctxt_closed: assumes "(s, t) \<in> (csr_r_join_step R)\<^sup>*"
  shows "(u @ s @ v, u @ t @ v) \<in> (csr_r_join_step R)\<^sup>*" using assms csr_r_join_step_ctxt_closed 
    sctxt.closed_rtrancl sctxt_closed_strings by auto

lemma csr_p_join_stepE [elim]:
  assumes "(s, t) \<in> (csr_p_join_step R)"
    and imp: "\<And>C l r cs. \<lbrakk>((l, r), cs) \<in> R; \<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step R)\<^sup>\<down>; 
      s = C\<llangle>l\<rrangle>; t = C\<llangle>r\<rrangle>\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  obtain n where *: "(s, t) \<in> csr_p_join_step_n R n" using assms by (auto simp: csr_p_join_step_iff)
  then show ?thesis
  proof (cases n)
    case (Suc n')
    have **: "(csr_p_join_step_n R n')\<^sup>* \<subseteq> (csr_p_join_step R)\<^sup>*" by (rule rtrancl_mono) (auto simp: csr_p_join_step_iff)
    then show ?thesis using csr_p_join_step_n_SucE [OF * [unfolded Suc]] 
      by (metis (no_types, lifting) csr_p_join_steps_n_imp_csteps imp joinD joinI split_beta')
  qed simp
qed

lemma csr_r_join_stepE [elim]:
  assumes "(s, t) \<in> (csr_r_join_step R)"
    and imp: "\<And>C l r cs w. \<lbrakk>((l, r), cs) \<in> R; \<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step R)\<^sup>\<down>; 
      s = C\<llangle>l @ w\<rrangle>; t = C\<llangle>r @ w\<rrangle>\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  obtain n where *: "(s, t) \<in> csr_r_join_step_n R n" using assms by (auto simp: csr_r_join_step_iff)
  then show ?thesis
  proof (cases n)
    case (Suc n')
    have **: "(csr_r_join_step_n R n')\<^sup>* \<subseteq> (csr_r_join_step R)\<^sup>*" by (rule rtrancl_mono) (auto simp: csr_r_join_step_iff)
    then show ?thesis using csr_r_join_step_n_SucE [OF * [unfolded Suc]] 
      by (metis (no_types, lifting) csr_r_join_steps_n_imp_csteps imp joinD joinI split_beta')
  qed simp
qed

lemma csr_semi_equational_stepE [elim]:
  assumes "(s, t) \<in> (csr_semi_equational_step R)"
    and imp: "\<And>C l r cs. \<lbrakk>((l, r), cs) \<in> R; \<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*; 
      s = C\<llangle>l\<rrangle>; t = C\<llangle>r\<rrangle>\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  obtain n where *: "(s, t) \<in> csr_semi_equational_step_n R n" using assms by (auto simp: csr_semi_equational_step_iff)
  then show ?thesis
  proof (cases n)
    case (Suc n')
    have **: "(csr_semi_equational_step_n R n')\<^sup>* \<subseteq> (csr_semi_equational_step R)\<^sup>*" by (rule rtrancl_mono) 
        (auto simp: csr_semi_equational_step_iff)
    then show ?thesis using csr_semi_equational_step_n_SucE [OF * [unfolded Suc]] csr_semi_equational_steps_n_imp_csr_semi_equational_steps
      by (metis (no_types, lifting) case_prodD case_prodI2 imp)
  qed simp
qed

lemma csr_r_semi_equational_stepE [elim]:
  assumes "(s, t) \<in> (csr_r_semi_equational_step R)"
    and imp: "\<And>C l r cs w. \<lbrakk>((l, r), cs) \<in> R; \<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*; 
      s = C\<llangle>l @ w\<rrangle>; t = C\<llangle>r @ w\<rrangle>\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  obtain n where *: "(s, t) \<in> csr_r_semi_equational_step_n R n" using assms by (auto simp: csr_r_semi_equational_step_iff)
  then show ?thesis
  proof (cases n)
    case (Suc n')
    have **: "(csr_r_semi_equational_step_n R n')\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*" using csr_r_semi_equational_step_iff
      by (meson conversion_mono in_mono subrelI)
    then show ?thesis using csr_r_semi_equational_step_n_SucE [OF * [unfolded Suc]]
      by (smt (verit, best) imp split_beta' subset_iff)
  qed simp
qed

lemma csr_lr_semi_equational_stepE [elim]:
  assumes "(s, t) \<in> (csr_lr_semi_equational_step R)"
    and imp: "\<And>C l r cs u w. \<lbrakk>((l, r), cs) \<in> R; \<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*; 
      s = C\<llangle>u @ l @ w\<rrangle>; t = C\<llangle>u @ r @ w\<rrangle>\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  obtain n where *: "(s, t) \<in> csr_lr_semi_equational_step_n R n" using assms by (auto simp: csr_lr_semi_equational_step_iff)
  then show ?thesis
  proof (cases n)
    case (Suc n')
    have **: "(csr_lr_semi_equational_step_n R n')\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*" using csr_lr_semi_equational_step_iff
      by (meson conversion_mono in_mono subrelI)
    then show ?thesis using csr_lr_semi_equational_step_n_SucE [OF * [unfolded Suc]]
      by (smt (verit, best) imp split_beta' subset_iff)
  qed simp
qed


text \<open>A conditional oriented string rewriting step of level @{term n}.\<close>
fun csr_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_step_n R 0 = {}" |
  csr_step_n_Suc: "csr_step_n R (Suc n) =
    {(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_step_n R n)\<^sup>*)}"

definition "csr_step R = (\<Union>n. csr_step_n R n)"

fun csr_lr_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_lr_step_n R 0 = {}" |
  csr_lr_step_n_Suc: "csr_lr_step_n R (Suc n) =
    {(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) | C l r u w cs.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_step_n R n)\<^sup>*)}"

definition "csr_lr_step R = (\<Union>n. csr_lr_step_n R n)"

fun csr_r_step_n :: "csts \<Rightarrow> nat \<Rightarrow> string rel"
where
  "csr_r_step_n R 0 = {}" |
  csr_r_step_n_Suc: "csr_r_step_n R (Suc n) =
    {(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) | C l r cs w.
      ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_step_n R n)\<^sup>*)}"

definition "csr_r_step R = (\<Union>n. csr_r_step_n R n)"

lemma csr_step_iff:
  "(s, t) \<in> csr_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_step_n R n)"
  by (auto simp: csr_step_def)

lemma csr_lr_step_iff:
  "(s, t) \<in> csr_lr_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_lr_step_n R n)"
  by (auto simp: csr_lr_step_def)

lemma csr_r_step_iff:
  "(s, t) \<in> csr_r_step R \<longleftrightarrow> (\<exists>n. (s, t) \<in> csr_r_step_n R n)"
  by (auto simp: csr_r_step_def)

lemma csr_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_step_n R n"
  shows "(s, t) \<in> csr_step R"
  using assms by (auto simp: csr_step_iff)

lemma csr_lr_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_lr_step_n R n"
  shows "(s, t) \<in> csr_lr_step R"
  using assms by (auto simp: csr_lr_step_iff)

lemma csr_r_step_n_imp_cstep:
  assumes "(s, t) \<in> csr_r_step_n R n"
  shows "(s, t) \<in> csr_r_step R"
using assms by (auto simp: csr_r_step_iff)

lemma csr_steps_n_imp_csteps:
  assumes "(s, t) \<in> (csr_step_n R n)\<^sup>*"
  shows "(s, t) \<in> (csr_step R)\<^sup>*"
  using assms by (induct; auto dest: csr_step_n_imp_cstep)

lemma csr_lr_steps_n_imp_csteps:
  assumes "(s, t) \<in> (csr_lr_step_n R n)\<^sup>*"
  shows "(s, t) \<in> (csr_lr_step R)\<^sup>*"
  using assms by (induct; auto dest: csr_lr_step_n_imp_cstep)

lemma csr_r_steps_n_imp_csteps:
  assumes "(s, t) \<in> (csr_r_step_n R n)\<^sup>*"
  shows "(s, t) \<in> (csr_r_step R)\<^sup>*"
using assms by (induct; auto dest: csr_r_step_n_imp_cstep)

lemma csr_steps_n_subset_csteps:
  "(csr_step_n R n)\<^sup>* \<subseteq> (csr_step R)\<^sup>*"
  by (auto dest: csr_steps_n_imp_csteps)

lemma csr_lr_steps_n_subset_csteps:
  "(csr_lr_step_n R n)\<^sup>* \<subseteq> (csr_lr_step R)\<^sup>*"
  by (auto dest: csr_lr_steps_n_imp_csteps)

lemma csr_r_steps_n_subset_csteps:
  "(csr_r_step_n R n)\<^sup>* \<subseteq> (csr_r_step R)\<^sup>*"
  by (auto dest: csr_r_steps_n_imp_csteps)

lemma csr_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_step_n R n)\<^sup>*"
    and "s = C\<llangle>l\<rrangle> "
    and "t = C\<llangle>r\<rrangle>"
  shows "(s, t) \<in> csr_step_n R (Suc n)"
  using assms by auto

lemma csr_lr_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_step_n R n)\<^sup>*"
    and "s = C\<llangle>u @ l @ w\<rrangle> "
    and "t = C\<llangle>u @ r @ w\<rrangle>"
  shows "(s, t) \<in> csr_lr_step_n R (Suc n)"
  using assms by fastforce

lemma csr_r_step_n_SucI [Pure.intro?]:
  assumes "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_step_n R n)\<^sup>*"
    and "s = C\<llangle>l @ w\<rrangle> "
    and "t = C\<llangle>r @ w\<rrangle>"
  shows "(s, t) \<in> csr_r_step_n R (Suc n)"
  using assms by fastforce

lemma csr_step_n_SucE:
  assumes "(s, t) \<in> csr_step_n R (Suc n)"
  obtains C l r \<sigma> cs where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_step_n R n)\<^sup>*"
    and "s = C\<llangle>l\<rrangle>"
    and "t = C\<llangle>r\<rrangle>"
  using assms by auto

lemma csr_lr_step_n_SucE:
  assumes "(s, t) \<in> csr_lr_step_n R (Suc n)"
  obtains C D l r cs u w where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_step_n R n)\<^sup>*"
    and "s = C\<llangle>u @ l @ w\<rrangle>"
    and "t = C\<llangle>u @ r @ w\<rrangle>"
  using assms by auto

lemma csr_r_step_n_SucE:
  assumes "(s, t) \<in> csr_r_step_n R (Suc n)"
  obtains C l r w cs where "((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_step_n R n)\<^sup>*"
    and "s = C\<llangle>l @ w\<rrangle>"
    and "t = C\<llangle>r @ w\<rrangle>"
  using assms by auto

lemma csr_r_step_n_E:
  assumes "(s, t) \<in> csr_r_step_n R n"
  obtains C l r w cs n' where "((l, r), cs) \<in> R" and "n = Suc n'"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_step_n R n')\<^sup>*"
    and "s = C\<llangle>l @ w\<rrangle>"
    and "t = C\<llangle>r @ w\<rrangle>"
  using assms by (cases n, auto)

lemma csr_step_n_Suc_mono:
  "csr_step_n R n \<subseteq> csr_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  show ?case
    using rtrancl_mono [OF Suc] by (auto elim!: csr_step_n_SucE intro!: csr_step_n_SucI, blast)
qed simp

lemma csr_lr_step_n_Suc_mono:
  "csr_lr_step_n R n \<subseteq> csr_lr_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  show ?case
    using rtrancl_mono [OF Suc] by (auto elim!: csr_lr_step_n_SucE intro!: csr_lr_step_n_SucI, blast)
qed simp

lemma csr_r_step_n_Suc_mono:
  "csr_r_step_n R n \<subseteq> csr_r_step_n R (Suc n)"
proof (induct n)
  case (Suc n)
  show ?case
    using rtrancl_mono [OF Suc] by (auto elim!: csr_r_step_n_SucE intro!: csr_r_step_n_SucI, blast)
qed simp

lemma csr_step_n_mono:
  assumes "i \<le> n"
  shows "csr_step_n R i \<subseteq> csr_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_step_n R (Suc i) \<subseteq> csr_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_step_n_Suc_mono in_mono)
qed simp

lemma csr_lr_step_n_mono:
  assumes "i \<le> n"
  shows "csr_lr_step_n R i \<subseteq> csr_lr_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_lr_step_n R (Suc i) \<subseteq> csr_lr_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_lr_step_n_Suc_mono in_mono)
qed simp

lemma csr_r_step_n_mono:
  assumes "i \<le> n"
  shows "csr_r_step_n R i \<subseteq> csr_r_step_n R n"
using assms
proof (induct "n - i" arbitrary: i)
  case (Suc k)
  hence "k = n - Suc i" and "Suc i \<le> n" by arith+
  hence "csr_r_step_n R (Suc i) \<subseteq> csr_r_step_n R n" using Suc.hyps by blast
  then show ?case 
    by (auto, meson csr_r_step_n_Suc_mono in_mono)
qed simp

lemma csr_steps_imp_csr_steps_n:
  assumes "(s, t) \<in> (csr_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_step_n R n)\<^sup>*"
  using assms csr_step_iff 
  by (induct, auto, meson csr_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD)

lemma csr_lr_steps_imp_csr_lr_steps_n:
  assumes "(s, t) \<in> (csr_lr_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_lr_step_n R n)\<^sup>*"
  using assms csr_lr_step_iff 
  by (induct, auto, meson csr_lr_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD) 

lemma csr_r_steps_imp_csr_r_steps_n:
  assumes "(s, t) \<in> (csr_r_step R)\<^sup>*"
  shows "\<exists>n. (s, t) \<in> (csr_r_step_n R n)\<^sup>*"
  using assms csr_r_step_iff 
  by (induct, auto, meson csr_r_step_n_mono linorder_linear rtrancl.rtrancl_into_rtrancl rtrancl_mono subsetD) 

lemma all_csr_step_imp_csr_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms by (auto intro: csr_steps_imp_csr_steps_n)
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * by blast
  then show ?thesis ..
qed

lemma all_csr_lr_step_imp_csr_lr_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_lr_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms by (auto intro: csr_lr_steps_imp_csr_lr_steps_n)
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_lr_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * by blast
  then show ?thesis ..
qed

lemma all_csr_r_step_imp_csr_r_step_n:
  assumes "\<forall>i < (k::nat). (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_step R)\<^sup>*"
  shows "\<exists>n. \<forall>i < k. (s\<^sub>i i, t\<^sub>i i) \<in> (csr_r_step_n R n)\<^sup>*" (is "\<exists>n. \<forall>i < k. ?P i n")  using assms 
proof -
  have "\<forall>i < k. \<exists>n\<^sub>i. ?P i n\<^sub>i"
    using assms by (auto intro: csr_r_steps_imp_csr_r_steps_n)
  then obtain f where *: "\<forall>i < k. ?P i (f i)" by metis
  define n where "n \<equiv> Max (set (map f [0 ..< k]))"
  have "\<forall>i < k. f i \<le> n" by (auto simp: n_def)
  then have "\<forall>i < k. ?P i n"
    using csr_r_step_n_mono [of "f i" n R for i, THEN rtrancl_mono] and * by blast
  then show ?thesis ..
qed

lemma csr_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_step R)\<^sup>*"
  shows "(l, r) \<in> csr_step R" using assms 
proof -
  obtain n where "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_step_n R n)\<^sup>*"
  using all_csr_step_imp_csr_step_n[of "length cs" "\<lambda>i. fst (cs ! i)" "\<lambda>i. snd (cs ! i)" R]
  and conds
    by (auto simp: all_set_conv_all_nth split_beta')
  hence "(l, r) \<in> csr_step_n R (Suc n)" using assms csr_step_n_SucI
    by (metis sctxt.cop_nil)
  then show ?thesis using csr_step_iff by blast
qed

lemma csr_lr_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_step R)\<^sup>*"
  shows "(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) \<in> csr_lr_step R" using assms 
proof -
  obtain n where "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_step_n R n)\<^sup>*"
  using all_csr_lr_step_imp_csr_lr_step_n[of "length cs" "\<lambda>i. u @ fst (cs ! i) @ w" "\<lambda>i. u @ snd (cs ! i) @ w" R]
  and conds assms
  by (auto simp: all_set_conv_all_nth split_beta') 
  hence "(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) \<in> csr_lr_step_n R (Suc n)" using assms csr_lr_step_n_SucI 
    by blast
  then show ?thesis using csr_lr_step_iff by blast
qed

lemma csr_r_stepI:
  assumes "((l, r), cs) \<in> R"
    and conds: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_step R)\<^sup>*"
  shows "(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) \<in> csr_r_step R" using assms 
proof -
  obtain n where "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_step_n R n)\<^sup>*"
  using all_csr_r_step_imp_csr_r_step_n[of "length cs" "\<lambda>i. fst (cs ! i) @ w" "\<lambda>i. snd (cs ! i) @ w" R]
  and conds assms
  by (auto simp: all_set_conv_all_nth split_beta') 
  then have "(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) \<in> csr_r_step_n R (Suc n)" using assms csr_r_step_n_SucI 
    by blast
  then show ?thesis using csr_r_step_iff by blast
qed

lemma csr_step_n_ctxt:
  assumes "(s, t) \<in> csr_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_step_n R n" using assms
  by (cases n, auto, metis sctxt.cop_add, insert csr_step_n_SucE)

lemma csr_lr_step_n_ctxt:
  assumes "(s, t) \<in> csr_lr_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_lr_step_n R n" using assms
  by (cases n, auto, metis (no_types, lifting) sctxt.cop_add)

lemma csr_r_step_n_ctxt:
  assumes "(s, t) \<in> csr_r_step_n R n"
  shows "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> csr_r_step_n R n" using assms csr_r_step_n_SucE
  by (cases n, auto, metis (no_types, lifting) sctxt.cop_add)

lemma csr_step_ctxt_closed:
  "sctxt.closed (csr_step R)"
  by (rule sctxt.closedI) (auto intro: csr_step_n_ctxt simp: csr_step_iff)

lemma csr_lr_step_ctxt_closed:
  "sctxt.closed (csr_lr_step R)"
  by (rule sctxt.closedI) (auto intro: csr_lr_step_n_ctxt simp: csr_lr_step_iff)

lemma csr_r_step_ctxt_closed:
  "sctxt.closed (csr_r_step R)"
  by (rule sctxt.closedI) (auto intro: csr_r_step_n_ctxt simp: csr_r_step_iff)

end
