(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Conditional Equational Theories\<close>

theory Conditional_Equational_Theories
  imports
   Conditional_String_Rewriting
   CSTS_P_Critical_Pairs
   ShortLex
begin

(* Definition 19 *)
inductive cond_eq_lr_theory :: "csts \<Rightarrow> (string \<times> string) \<Rightarrow> bool" (infix "\<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r" 55) where
  refl:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, s)"
| symmetry:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, t)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (t, s)"
| transitive:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, u)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, t) \<and> R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (t, u)"
| congruence:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (u @ s @ v, u @ t @ v)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, t)"
| replacement:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (u @ l @ w, u @ r @ w)" 
    if "((l, r), cs) \<in> R \<and> (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w))"

(* Definition 20 *)
inductive cond_eq_r_theory :: "csts \<Rightarrow> (string \<times> string) \<Rightarrow> bool" (infix "\<turnstile>\<^sub>c\<^sub>e\<^sub>r" 55) where
  refl:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, s)"
| symmetry:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, t)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (t, s)"
| transitive:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, u)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, t) \<and> R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (t, u)"
| congruence:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (u @ s @ v, u @ t @ v)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, t)"
| replacement:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (l @ w, r @ w)" 
    if "((l, r), cs) \<in> R \<and> (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s\<^sub>i @ w, t\<^sub>i @ w))"

(* Definition 21 *)
inductive cond_eq_p_theory :: "csts \<Rightarrow> (string \<times> string) \<Rightarrow> bool" (infix "\<turnstile>\<^sub>c\<^sub>e\<^sub>p" 55) where
  refl:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, s)"
| symmetry:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, t)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (t, s)"
| transitive:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, u)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, t) \<and> R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (t, u)"
| congruence:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (u @ s @ v, u @ t @ v)" 
    if "R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, t)"
| replacement:"R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (l, r)" 
    if "((l, r), cs) \<in> R \<and> (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s\<^sub>i, t\<^sub>i))"

lemmas cond_eq_p_theoryI = cond_eq_p_theory.intros [intro]
lemmas cond_eq_p_theoryE = cond_eq_p_theory.cases [elim]

lemmas cond_eq_r_theoryI = cond_eq_r_theory.intros [intro]
lemmas cond_eq_r_theoryE = cond_eq_r_theory.cases [elim]

lemmas cond_eq_lr_theoryI = cond_eq_lr_theory.intros [intro]
lemmas cond_eq_lr_theoryE = cond_eq_lr_theory.cases [elim]

definition cond_eq_p_theory_rel::"csts \<Rightarrow> (string \<times> string) set"  where
  "cond_eq_p_theory_rel R = {(s, t). R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, t)}"

definition cond_eq_r_theory_rel::"csts \<Rightarrow> (string \<times> string) set"  where
  "cond_eq_r_theory_rel R = {(s, t). R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, t)}"

definition cond_eq_lr_theory_rel::"csts \<Rightarrow> (string \<times> string) set"  where
  "cond_eq_lr_theory_rel R = {(s, t). R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, t)}"

lemma cond_eq_theory_p_refl_sym_tran_closed: assumes "(s, t) \<in> (cond_eq_p_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(s, t) \<in> (cond_eq_p_theory_rel R)"
proof -
  from assms obtain n where "(s, t) \<in> (cond_eq_p_theory_rel R)\<^sup>\<leftrightarrow>^^n" by auto
  then show ?thesis
  proof(induct n arbitrary: t)
    case 0
    then show ?case 
      by (simp add: cond_eq_p_theory.refl cond_eq_p_theory_rel_def)
  next
    case (Suc n)
    from Suc(2) obtain u where su:"(s, u) \<in> (cond_eq_p_theory_rel R)\<^sup>\<leftrightarrow> ^^ n" and ut:"(u, t) \<in> (cond_eq_p_theory_rel R)\<^sup>\<leftrightarrow>" by auto
    from su Suc(1) have "(s, u) \<in> (cond_eq_p_theory_rel R)" by auto
    moreover from ut have "(u, t) \<in> (cond_eq_p_theory_rel R)"
      by (auto, metis case_prod_conv cond_eq_p_theory.symmetry cond_eq_p_theory_rel_def mem_Collect_eq)
    ultimately show ?case
      by (metis case_prod_conv cond_eq_p_theory.transitive cond_eq_p_theory_rel_def mem_Collect_eq)
  qed
qed

lemma cond_eq_theory_r_refl_sym_tran_closed: assumes "(s, t) \<in> (cond_eq_r_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(s, t) \<in> (cond_eq_r_theory_rel R)"
proof -
  from assms obtain n where "(s, t) \<in> (cond_eq_r_theory_rel R)\<^sup>\<leftrightarrow>^^n" by auto
  then show ?thesis
  proof(induct n arbitrary: t)
    case 0
    then show ?case 
      by (simp add: cond_eq_r_theory.refl cond_eq_r_theory_rel_def)
  next
    case (Suc n)
    from Suc(2) obtain u where su:"(s, u) \<in> (cond_eq_r_theory_rel R)\<^sup>\<leftrightarrow> ^^ n" and ut:"(u, t) \<in> (cond_eq_r_theory_rel R)\<^sup>\<leftrightarrow>" by auto
    from su Suc(1) have "(s, u) \<in> (cond_eq_r_theory_rel R)" by auto
    moreover from ut have "(u, t) \<in> (cond_eq_r_theory_rel R)" using cond_eq_r_theory_rel_def by auto
    ultimately show ?case
      by (metis case_prod_conv cond_eq_r_theory.transitive cond_eq_r_theory_rel_def mem_Collect_eq)
  qed
qed

lemma cond_eq_theory_lr_refl_sym_tran_closed: assumes "(s, t) \<in> (cond_eq_lr_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(s, t) \<in> (cond_eq_lr_theory_rel R)"
proof -
  from assms obtain n where "(s, t) \<in> (cond_eq_lr_theory_rel R)\<^sup>\<leftrightarrow>^^n" by auto
  then show ?thesis
  proof(induct n arbitrary: t)
    case 0
    then show ?case 
      by (simp add: cond_eq_lr_theory.refl cond_eq_lr_theory_rel_def)
  next
    case (Suc n)
    from Suc(2) obtain u where su:"(s, u) \<in> (cond_eq_lr_theory_rel R)\<^sup>\<leftrightarrow> ^^ n" and ut:"(u, t) \<in> (cond_eq_lr_theory_rel R)\<^sup>\<leftrightarrow>" by auto
    from su Suc(1) have "(s, u) \<in> (cond_eq_lr_theory_rel R)" by auto
    moreover from ut have "(u, t) \<in> (cond_eq_lr_theory_rel R)" using cond_eq_lr_theory_rel_def by auto
    ultimately show ?case
      by (metis case_prod_conv cond_eq_lr_theory.transitive cond_eq_lr_theory_rel_def mem_Collect_eq)
  qed
qed

lemma cond_membership_cond_eq_p_theory_rel_refl_sym_tran_closed: 
  assumes "\<forall>s t. (s, t) \<in> S \<longrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, t)"
  shows "\<forall>s t. (s, t) \<in> S\<^sup>\<leftrightarrow>\<^sup>* \<longrightarrow> (s, t) \<in> (cond_eq_p_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*"
  unfolding cond_eq_p_theory_rel_def using assms 
  by (auto, metis conversion_mono mem_Collect_eq subset_eq surj_pair)

lemma cond_membership_cond_eq_r_theory_rel_refl_sym_tran_closed: 
  assumes "\<forall>s t. (s, t) \<in> S \<longrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, t)"
  shows "\<forall>s t. (s, t) \<in> S\<^sup>\<leftrightarrow>\<^sup>* \<longrightarrow> (s, t) \<in> (cond_eq_r_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*"
  unfolding cond_eq_r_theory_rel_def using assms 
  by (auto, metis conversion_mono mem_Collect_eq subset_eq surj_pair)

lemma cond_membership_cond_eq_lr_theory_rel_refl_sym_tran_closed: 
  assumes "\<forall>s t. (s, t) \<in> S \<longrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, t)"
  shows "\<forall>s t. (s, t) \<in> S\<^sup>\<leftrightarrow>\<^sup>* \<longrightarrow> (s, t) \<in> (cond_eq_lr_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*"
  unfolding cond_eq_lr_theory_rel_def using assms 
    by (auto, metis conversion_mono mem_Collect_eq subset_eq surj_pair)

lemma CR_semi_equational_join_equiv: assumes cr:"CR (csr_p_join_step R)"
  shows "\<forall>l r cs n s\<^sub>i t\<^sub>i w. ((l, r), cs) \<in> R \<longrightarrow> (s\<^sub>i, t\<^sub>i) \<in> set cs \<longrightarrow>  
  ((s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step R)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step R)\<^sup>\<down>)"
  using cr[unfolded CR_on_def] CR_imp_conversionIff_join cr by blast+

lemma csr_semi_equational_cond_eq_p_theory_single:
  assumes "(s, t) \<in> csr_semi_equational_step R"
  shows "R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, t)"
proof -
  from assms obtain n where "(s, t) \<in> (csr_semi_equational_step_n R (Suc n))" 
    using csr_semi_equational_step_iff csr_semi_equational_step_n_E by metis
  then obtain l r cs C where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and s:"s = C\<llangle>l\<rrangle>" and t:"t = C\<llangle>r\<rrangle>" by auto
  then show ?thesis
  proof(induct n arbitrary: l r cs C s t)
    case 0
    then show ?case by (auto, metis (mono_tags, lifting) case_prodI2 cond_eq_p_theory.congruence 
          cond_eq_p_theory.refl cond_eq_p_theory.replacement old.prod.case sctxt_app_step)
  next
    case (Suc n)
    let ?S = "{(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"
    have "?S = csr_semi_equational_step_n R (Suc n)" by auto
    moreover have *:"\<forall>a b. (a, b) \<in> ?S \<longrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (a, b)" using Suc(1) by auto
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (?S)\<^sup>\<leftrightarrow>\<^sup>*" using Suc by auto
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (cond_eq_p_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*" unfolding cond_eq_p_theory_rel_def 
      using cond_membership_cond_eq_p_theory_rel_refl_sym_tran_closed[OF *] Suc
      by (auto, simp add: cond_eq_p_theory_rel_def)
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s\<^sub>i, t\<^sub>i)" using cond_eq_theory_p_refl_sym_tran_closed
      using calculation(4) cond_eq_p_theory_rel_def by auto
    ultimately show ?case
    proof -
      have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (l, r)"
        using Suc.prems(1) \<open>\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s\<^sub>i, t\<^sub>i)\<close> by blast
      then show ?thesis
        using Suc.prems(3) Suc.prems(4) cond_eq_p_theory.congruence sctxt_app_step by metis
    qed
  qed
qed

lemma csr_r_semi_equational_cond_eq_r_theory_single:
  assumes "(s, t) \<in> csr_r_semi_equational_step R"
  shows "R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, t)"
proof -
  from assms obtain n where "(s, t) \<in> (csr_r_semi_equational_step_n R (Suc n))" 
    using csr_r_semi_equational_step_iff csr_r_semi_equational_step_n_E by metis
  then obtain l r cs C w where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and s:"s = C\<llangle>l @ w\<rrangle>" and t:"t = C\<llangle>r @ w\<rrangle>" by auto
  then show ?thesis
  proof(induct n arbitrary: l r cs C w s t)
    case 0
    hence "R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (l @ w, r @ w)" by fastforce
    then show ?case by (metis "0.prems"(3) "0.prems"(4) cond_eq_r_theory.congruence sctxt_app_step)
  next
    case (Suc n)
    let ?S = "{(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) | C l r cs w.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"
    have "?S = csr_r_semi_equational_step_n R (Suc n)" by auto
    moreover have *:"\<forall>a b. (a, b) \<in> ?S \<longrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (a, b)" using Suc(1) by (auto split:prod.splits) 
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (?S)\<^sup>\<leftrightarrow>\<^sup>*" using Suc by (auto split:prod.splits)
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (cond_eq_r_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*" unfolding cond_eq_r_theory_rel_def 
      using cond_membership_cond_eq_r_theory_rel_refl_sym_tran_closed[OF *] Suc cond_eq_r_theory_rel_def by fastforce
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s\<^sub>i @ w, t\<^sub>i @ w)" using cond_eq_theory_r_refl_sym_tran_closed
      using calculation(4) cond_eq_r_theory_rel_def by (auto split:prod.splits)
    ultimately show ?case
    proof -
      have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (l @ w, r @ w)"
        using Suc.prems(1) \<open>\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s\<^sub>i @ w, t\<^sub>i @ w)\<close> by blast
      then show ?thesis
        using Suc.prems(3) Suc.prems(4) cond_eq_r_theory.congruence sctxt_app_step by metis
    qed
  qed
qed

lemma csr_lr_semi_equational_cond_eq_lr_theory_single:
  assumes "(s, t) \<in> csr_lr_semi_equational_step R"
  shows "R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, t)"
proof -
  from assms obtain n where "(s, t) \<in> (csr_lr_semi_equational_step_n R (Suc n))" 
    using csr_lr_semi_equational_step_iff csr_lr_semi_equational_step_n_E by metis
  then obtain l r cs C u w where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
    and s:"s = C\<llangle>u @ l @ w\<rrangle>" and t:"t = C\<llangle>u @ r @ w\<rrangle>" by auto
  then show ?thesis
  proof(induct n arbitrary: l r cs C w u s t)
    case 0
    hence "R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (u @ l @ w, u @ r @ w)" by fastforce
    then show ?case by (metis "0.prems"(3) "0.prems"(4) cond_eq_lr_theory.congruence sctxt_app_step)
  next
    case (Suc n)
    let ?S = "{(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) | C l r cs u w.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"
    have "?S = csr_lr_semi_equational_step_n R (Suc n)" by auto
    moreover have *:"\<forall>a b. (a, b) \<in> ?S \<longrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (a, b)" using Suc(1) by (auto split:prod.splits) 
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (?S)\<^sup>\<leftrightarrow>\<^sup>*" using Suc by (auto split:prod.splits)
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (cond_eq_lr_theory_rel R)\<^sup>\<leftrightarrow>\<^sup>*" unfolding cond_eq_lr_theory_rel_def 
      using cond_membership_cond_eq_lr_theory_rel_refl_sym_tran_closed[OF *] Suc cond_eq_lr_theory_rel_def by fastforce
    moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w)" using cond_eq_theory_lr_refl_sym_tran_closed
      using calculation(4) cond_eq_lr_theory_rel_def by (auto split:prod.splits)
    ultimately show ?case
    proof -
      have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (u @ l @ w, u @ r @ w)"
        using Suc.prems(1) \<open>\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w)\<close> by blast
      then show ?thesis
        using Suc.prems(3) Suc.prems(4) cond_eq_lr_theory.congruence sctxt_app_step by metis
    qed
  qed
qed

(* Lemma 25(iii) *)
lemma csr_semi_equational_cond_eq_p_theory_equiv:
  "(s, t) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, t)" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume asm:?LHS
  then obtain n where "(s, t) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>^^n" by auto
  then show ?RHS
  proof (induct n arbitrary:t)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain u where su:"(s, u) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow> ^^ n" and ut:"(u, t) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>" by auto
    with Suc(1) have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, u)" by auto
    moreover from ut have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (u, t)" using csr_semi_equational_cond_eq_p_theory_single by auto
    ultimately show ?case by auto 
  qed
next
  assume asm:?RHS
  then show ?LHS
  proof induct
    case (refl R s)
    then show ?case by auto
  next
    case (symmetry R t s)
    then show ?case by (simp add: conversion_inv)
  next
    case (transitive R s t u)
    then show ?case by (meson conversion_trans transD)
  next
    case (congruence R s t u v)
    then show ?case by (simp add: csr_semi_equational_step_ctxt_closed sctxt.closed_conversion sctxt_closed_strings)
  next
    case (replacement l r cs R)
    hence "(\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs.  (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*)" by auto
    hence "\<forall>C. (C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) \<in> (csr_semi_equational_step R)" using csr_semi_equational_stepI replacement by auto
    then show ?case by (metis ShortLex.hole conversionI' r_into_rtrancl)
  qed
qed

(* Lemma 25(ii) *)
lemma csr_semi_equational_cond_eq_r_theory_equiv:
  "(s, t) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, t)" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume asm:?LHS
  then obtain n where "(s, t) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>^^n" by auto
  then show ?RHS
  proof (induct n arbitrary:t)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain u where su:"(s, u) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow> ^^ n" and ut:"(u, t) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>" by auto
    with Suc(1) have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, u)" by auto
    moreover from ut have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (u, t)" using csr_r_semi_equational_cond_eq_r_theory_single by auto
    ultimately show ?case by auto 
  qed
next
  assume asm:?RHS
  then show ?LHS
  proof induct
    case (refl R s)
    then show ?case by auto
  next
    case (symmetry R t s)
    then show ?case by (simp add: conversion_inv)
  next
    case (transitive R s t u)
    then show ?case by (meson conversion_trans transD)
  next
    case (congruence R s t u v)
    then show ?case by (simp add: csr_r_semi_equational_step_ctxt_closed sctxt.closed_conversion sctxt_closed_strings)
  next
    case (replacement l r cs R w)
    hence "(\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*)" by auto
    hence "\<forall>C. (C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) \<in> (csr_r_semi_equational_step R)" using csr_r_semi_equational_stepI replacement by auto
    then show ?case by (metis ShortLex.hole conversionI' r_into_rtrancl)
  qed
qed

(* Lemma 25(i) *)
lemma csr_semi_equational_cond_eq_lr_theory_equiv:
  "(s, t) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, t)" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume asm:?LHS
  then obtain n where "(s, t) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>^^n" by auto
  then show ?RHS
  proof (induct n arbitrary:t)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain u where su:"(s, u) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow> ^^ n" and ut:"(u, t) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>" by auto
    with Suc(1) have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, u)" by auto
    moreover from ut have "R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (u, t)" using csr_lr_semi_equational_cond_eq_lr_theory_single by auto
    ultimately show ?case by auto 
  qed
next
  assume asm:?RHS
  then show ?LHS
  proof induct
    case (refl R s)
    then show ?case by auto
  next
    case (symmetry R t s)
    then show ?case by (simp add: conversion_inv)
  next
    case (transitive R s t u)
    then show ?case by (meson conversion_trans transD)
  next
    case (congruence R s t u v)
    then show ?case by (simp add: csr_lr_semi_equational_step_ctxt_closed sctxt.closed_conversion sctxt_closed_strings)
  next
    case (replacement l r cs  R u w)
    hence "(\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*)" by auto
    hence "\<forall>C. (C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) \<in> (csr_lr_semi_equational_step R)" using csr_lr_semi_equational_stepI replacement by auto
    then show ?case by (metis ShortLex.hole conversionI' r_into_rtrancl)
  qed
qed

(* Lemma 26(iii) *)
lemma csr_semi_equational_csr_join_CR_equiv:
  assumes cr:"CR (csr_p_join_step R)"
  shows "(s, t) \<in> (csr_semi_equational_step R) \<longleftrightarrow> (s, t) \<in> (csr_p_join_step R)" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume asm:?LHS
  then show ?RHS
  proof
    from asm obtain n where "(s, t) \<in> (csr_semi_equational_step_n R (Suc n))" 
      using csr_semi_equational_step_iff csr_semi_equational_step_n_E by metis
    then obtain l r cs C where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
      and s:"s = C\<llangle>l\<rrangle>" and t:"t = C\<llangle>r\<rrangle>" by auto
    then show ?thesis
    proof(induct n arbitrary: l r cs C s t)
      case 0
      then show ?case  using csr_p_join_stepI by (auto split:prod.splits, fastforce)
    next
      case (Suc n)
      let ?S = "{(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"
      have "?S = csr_semi_equational_step_n R (Suc n)" by auto
      moreover have "\<forall>a b. (a, b) \<in> ?S \<longrightarrow> (a, b) \<in> csr_p_join_step R" using Suc(1) by auto
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (?S)\<^sup>\<leftrightarrow>\<^sup>*" using Suc by auto 
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step R)\<^sup>\<leftrightarrow>\<^sup>*"
        by (auto, metis (no_types, lifting) calculation(2) calculation(3) case_prod_conv conversion_mono subrelI subset_eq)
      ultimately show ?case using cr[unfolded CR_on_def]
        using CR_imp_conversionIff_join Suc.prems(1) Suc.prems(3) Suc.prems(4) cr csr_p_join_stepI by fastforce      
    qed
  qed
next 
  assume asm: ?RHS
  then show ?LHS
    proof
      from asm obtain n where "(s, t) \<in> (csr_p_join_step_n R (Suc n))" 
      using csr_p_join_step_iff csr_p_join_step_n_E by metis
    then obtain l r cs C where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>"
      and s:"s = C\<llangle>l\<rrangle>" and t:"t = C\<llangle>r\<rrangle>" by auto
    then show ?thesis
    proof(induct n arbitrary: l r cs C s t)
      case 0
      then show ?case by (auto, metis (no_types, lifting) case_prodI2 converse_rtranclE 
            conversion_rtrancl csr_semi_equational_stepI empty_iff joinD rtrancl.rtrancl_refl)
    next
      case (Suc n)
      let ?T = "{(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>)}"
      have "?T = csr_p_join_step_n R (Suc n)" by auto
      moreover have "\<forall>a b. (a, b) \<in> ?T \<longrightarrow> (a, b) \<in> csr_semi_equational_step R" using Suc(1) by auto
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (?T)\<^sup>\<leftrightarrow>\<^sup>*" using Suc join_imp_conversion by (auto, blast)
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*" 
        by (auto, metis (no_types, lifting) calculation(2) calculation(3) case_prod_conv conversion_mono subset_eq surj_pair)
      ultimately show ?case using Suc.prems(1) Suc.prems(3) Suc.prems(4) csr_semi_equational_stepI by auto
    qed
  qed
qed

(* Lemma 26(ii) *)
lemma csr_r_semi_equational_csr_r_join_CR_equiv:
  assumes cr:"CR (csr_r_join_step R)"
  shows "(s, t) \<in> (csr_r_semi_equational_step R) \<longleftrightarrow> (s, t) \<in> (csr_r_join_step R)" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume asm:?LHS
  then show ?RHS
  proof
    from asm obtain n where "(s, t) \<in> (csr_r_semi_equational_step_n R (Suc n))" 
      using csr_r_semi_equational_step_iff csr_r_semi_equational_step_n_E by metis
    then obtain l r cs C w where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
      and s:"s = C\<llangle>l @ w\<rrangle>" and t:"t = C\<llangle>r @ w\<rrangle>" by auto
    then show ?thesis
    proof(induct n arbitrary: l r cs C w s t)
      case 0
      then show ?case  using csr_r_join_stepI by (auto split:prod.splits, fastforce)
    next
      case (Suc n)
      let ?S = "{(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) | C l r cs w.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"
      have "?S = csr_r_semi_equational_step_n R (Suc n)" by auto
      moreover have "\<forall>a b. (a, b) \<in> ?S \<longrightarrow> (a, b) \<in> csr_r_join_step R" using Suc(1) by auto
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (?S)\<^sup>\<leftrightarrow>\<^sup>*" using Suc by auto 
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step R)\<^sup>\<leftrightarrow>\<^sup>*"
        by (auto, metis (no_types, lifting) calculation(2) calculation(3) case_prod_conv conversion_mono subrelI subset_eq)
      ultimately show ?case using cr[unfolded CR_on_def]
        using CR_imp_conversionIff_join Suc.prems(1) Suc.prems(3) Suc.prems(4) cr csr_r_join_stepI by fastforce      
    qed
  qed
next 
  assume asm: ?RHS
  then show ?LHS
    proof -
      from asm obtain n where "(s, t) \<in> (csr_r_join_step_n R (Suc n))" 
      using csr_r_join_step_iff csr_r_join_step_n_E by metis
    then obtain l r cs C w where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n)\<^sup>\<down>"
      and s:"s = C\<llangle>l @ w\<rrangle>" and t:"t = C\<llangle>r @ w\<rrangle>" by auto
    then show ?thesis
    proof(induct n arbitrary: l r cs C w s t)
      case 0
      then show ?case using csr_r_semi_equational_stepI by (auto split:prod.splits, fastforce)
    next
      case (Suc n)
      let ?T = "{(C\<llangle>l @ w\<rrangle>, C\<llangle>r @ w\<rrangle>) | C l r cs w.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n)\<^sup>\<down>)}"
      have "?T = csr_r_join_step_n R (Suc n)" by auto
      moreover have "\<forall>a b. (a, b) \<in> ?T \<longrightarrow> (a, b) \<in> csr_r_semi_equational_step R" using Suc(1) by auto
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (?T)\<^sup>\<leftrightarrow>\<^sup>*" using Suc join_imp_conversion by (auto, blast)
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*" 
        by (auto, metis (no_types, lifting) calculation(2) calculation(3) case_prod_conv conversion_mono subset_eq surj_pair)
      ultimately show ?case using Suc.prems(1) Suc.prems(3) Suc.prems(4) csr_r_semi_equational_stepI by auto
    qed
  qed
qed

(* Lemma 26(i) *)
lemma csr_lr_semi_equational_csr_lr_join_CR_equiv:
  assumes cr:"CR (csr_lr_join_step R)"
  shows "(s, t) \<in> (csr_lr_semi_equational_step R) \<longleftrightarrow> (s, t) \<in> (csr_lr_join_step R)" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume asm:?LHS
  then show ?RHS
  proof
    from asm obtain n where "(s, t) \<in> (csr_lr_semi_equational_step_n R (Suc n))" 
      using csr_lr_semi_equational_step_iff csr_lr_semi_equational_step_n_E by metis
    then obtain l r cs C w u where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*"
      and s:"s = C\<llangle>u @ l @ w\<rrangle>" and t:"t = C\<llangle>u @ r @ w\<rrangle>" by auto
    then show ?thesis
    proof(induct n arbitrary: l r cs C w u s t)
      case 0
      then show ?case  using csr_lr_join_stepI by (auto split:prod.splits, fastforce)
    next
      case (Suc n)
      let ?S = "{(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) | C l r cs u w.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step_n R n)\<^sup>\<leftrightarrow>\<^sup>*)}"
      have "?S = csr_lr_semi_equational_step_n R (Suc n)" by auto
      moreover have "\<forall>a b. (a, b) \<in> ?S \<longrightarrow> (a, b) \<in> csr_lr_join_step R" using Suc(1) by auto
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (?S)\<^sup>\<leftrightarrow>\<^sup>*" using Suc by auto 
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step R)\<^sup>\<leftrightarrow>\<^sup>*"
        by (auto, metis (no_types, lifting) calculation(2) calculation(3) case_prod_conv conversion_mono subrelI subset_eq)
      ultimately show ?case using cr[unfolded CR_on_def]
        using CR_imp_conversionIff_join Suc.prems(1) Suc.prems(3) Suc.prems(4) cr csr_lr_join_stepI by fastforce      
    qed
  qed
next 
  assume asm: ?RHS
  then show ?LHS
    proof -
      from asm obtain n where "(s, t) \<in> (csr_lr_join_step_n R (Suc n))" 
      using csr_lr_join_step_iff csr_lr_join_step_n_E by metis
    then obtain l r cs C u w where lr:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step_n R n)\<^sup>\<down>"
      and s:"s = C\<llangle>u @ l @ w\<rrangle>" and t:"t = C\<llangle>u @ r @ w\<rrangle>" by auto
    then show ?thesis
    proof(induct n arbitrary: l r cs C u w s t)
      case 0
      then show ?case using csr_lr_semi_equational_stepI by (auto split:prod.splits, fastforce)
    next
      case (Suc n)
      let ?T = "{(C\<llangle>u @ l @ w\<rrangle>, C\<llangle>u @ r @ w\<rrangle>) | C l r cs u w.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_join_step_n R n)\<^sup>\<down>)}"
      have "?T = csr_lr_join_step_n R (Suc n)" by auto
      moreover have "\<forall>a b. (a, b) \<in> ?T \<longrightarrow> (a, b) \<in> csr_lr_semi_equational_step R" using Suc(1) by auto
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (?T)\<^sup>\<leftrightarrow>\<^sup>*" using Suc join_imp_conversion by (auto, blast)
      moreover have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (u @ s\<^sub>i @ w, u @ t\<^sub>i @ w) \<in> (csr_lr_semi_equational_step R)\<^sup>\<leftrightarrow>\<^sup>*" 
        by (auto, metis (no_types, lifting) calculation(2) calculation(3) case_prod_conv conversion_mono subset_eq surj_pair)
      ultimately show ?case using Suc.prems(1) Suc.prems(3) Suc.prems(4) csr_lr_semi_equational_stepI by auto
    qed
  qed
qed

theorem csr_join_cond_eq_p_theory_equiv:
  assumes cr:"CR (csr_p_join_step R)"
  shows "(s, t) \<in> (csr_p_join_step R)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>p (s, t)"
  using assms csr_semi_equational_csr_join_CR_equiv[of R s t] csr_semi_equational_cond_eq_p_theory_equiv[of s t R]
    by (metis conversion_mono csr_semi_equational_csr_join_CR_equiv old.prod.exhaust subset_iff)

theorem csr_join_cond_eq_r_theory_equiv:
  assumes cr:"CR (csr_r_join_step R)"
  shows "(s, t) \<in> (csr_r_join_step R)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>r (s, t)"
  using assms csr_r_semi_equational_csr_r_join_CR_equiv[of R s t] csr_semi_equational_cond_eq_r_theory_equiv[of s t R]
  by (meson conversion_mono csr_r_semi_equational_csr_r_join_CR_equiv in_mono subrelI)

theorem csr_join_cond_eq_lr_theory_equiv:
  assumes cr:"CR (csr_lr_join_step R)"
  shows "(s, t) \<in> (csr_lr_join_step R)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> R \<turnstile>\<^sub>c\<^sub>e\<^sub>l\<^sub>r (s, t)"
  using assms csr_lr_semi_equational_csr_lr_join_CR_equiv[of R s t] csr_semi_equational_cond_eq_lr_theory_equiv[of s t R]
    by (meson conversion_mono csr_lr_semi_equational_csr_lr_join_CR_equiv in_mono subrelI)

definition normalized_p :: "csts \<Rightarrow> string \<Rightarrow> bool" where
  "normalized_p R w \<longleftrightarrow> (w \<in> NF (csr_p_join_step R))"

definition "strongly_p_irreducible R s \<longleftrightarrow> (\<forall>((l, r), cs) \<in> R. \<not> (subseq l s))"

lemma sp_irreducible_imp_normalized_p: 
  assumes sp:"strongly_p_irreducible R s"
  shows "normalized_p R s"
proof(rule ccontr)
  assume "\<not> ?thesis"
  hence "\<exists>t. (s, t) \<in> (csr_p_join_step R)" unfolding normalized_p_def by auto
  then obtain t where "(s, t) \<in> (csr_p_join_step R)" by auto
  then obtain n where "(s, t) \<in> (csr_p_join_step_n R (Suc n))" 
    by (meson csr_p_join_step_iff csr_p_join_step_n_Suc_mono subsetD)
  then obtain C l r cs where lr:"((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>" and s:"s = C\<llangle>l\<rrangle>" and "t = C\<llangle>r\<rrangle>" by auto
  from s sp[unfolded strongly_p_irreducible_def] 
  show False by (auto split:prod.splits, metis lr list_emb_append2 list_emb_prefix sctxt_app subseq_order.dual_order.refl)
qed

definition strongly_p_deterministic where
  "strongly_p_deterministic R \<longleftrightarrow> (\<forall>((l, r), cs) \<in> R. \<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. normalized_p R t\<^sub>i)"

lemma strongly_p_deterministic_equiv: assumes sp:"strongly_p_deterministic R"
  shows "\<forall>l r cs n s\<^sub>i t\<^sub>i w. ((l, r), cs) \<in> R \<longrightarrow> (s\<^sub>i, t\<^sub>i) \<in> set cs \<longrightarrow>  
  ((s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down> \<longleftrightarrow> (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>*)" using assms[unfolded strongly_p_deterministic_def]
  by (auto split:prod.splits simp add: NF_iff_no_step NF_join_imp_reach csr_p_join_step_iff normalized_p_def)

proposition csr_join_csr_step_equiv:
  assumes sp:"strongly_p_deterministic R"
  shows "(s, t) \<in> (csr_p_join_step R) \<longleftrightarrow> (s, t) \<in> (csr_step R)" (is "?LHS \<longleftrightarrow> ?RHS")
proof -
  from strongly_p_deterministic_equiv[of R]
  have *:"\<forall>l r cs n s\<^sub>i t\<^sub>i w. ((l, r), cs) \<in> R \<longrightarrow> (s\<^sub>i, t\<^sub>i) \<in> set cs \<longrightarrow>  
    ((s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down> \<longleftrightarrow> (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>*)" using sp by auto
  have zero:"csr_p_join_step_n R 0 = csr_step_n R 0" by auto
  have "\<forall>n. csr_p_join_step_n R n = csr_step_n R n"
  proof(intro allI impI)
    fix n
    show "csr_p_join_step_n R n = csr_step_n R n"
    proof(induct n)
      case 0
      then show ?case using zero by auto
    next
      case (Suc n)
      have IH:"\<forall> l r cs s\<^sub>i t\<^sub>i w. ((l, r), cs) \<in> R \<longrightarrow> (s\<^sub>i, t\<^sub>i) \<in> set cs \<longrightarrow>
        ((s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down> \<longleftrightarrow> (s\<^sub>i, t\<^sub>i) \<in> (csr_step_n R n)\<^sup>*)" using * Suc(1) by metis
      moreover have "csr_p_join_step_n R (Suc n) = {(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>)}" by auto
      moreover have "csr_p_join_step_n R (Suc n) = {(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>*)}" using * remove_suffix.cases
        by (auto, metis+)
      moreover have "csr_step_n R (Suc n) = {(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_step_n R n)\<^sup>*)}" by auto
      moreover have "csr_step_n R (Suc n) = {(C\<llangle>l\<rrangle>, C\<llangle>r\<rrangle>) | C l r cs.
        ((l, r), cs) \<in> R \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>*)}" using IH Suc by auto
      ultimately show ?case by auto
    qed
  qed
  then show ?thesis using csr_p_join_step_iff csr_step_n_imp_cstep csr_step_iff by auto
qed

end
