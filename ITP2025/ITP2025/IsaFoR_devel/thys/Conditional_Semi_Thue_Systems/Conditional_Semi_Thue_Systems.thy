(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Conditional Semi-Thue Systems\<close>

theory Conditional_Semi_Thue_Systems
  imports
    Conditional_Equational_Theories
    Semi_Thue_Systems
    CSTS_P_Critical_Pairs
    CSTS_R_Critical_Pairs
begin

no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)

locale conditional_semi_Thue = 
  fixes R :: csts
    and S :: "char set" (* alphabet *)
  assumes "finite S"
    and "S \<noteq> {}"
    and fnR:"finite R"
    
locale conditional_r_join_semi_Thue =  reductive_r_join + conditional_semi_Thue R S 
  for R :: csts and S :: "char set" + 
  fixes Thue_R_Congruence :: sts
  assumes cong:"Thue_R_Congruence = (csr_r_join_step R)\<^sup>\<leftrightarrow>\<^sup>*"
    and T_sig:"Thue_R_Congruence \<subseteq> S\<^sup>\<star> \<times> S\<^sup>\<star>"
begin

sublocale equiv_r: equivalence "S\<^sup>\<star>" "Thue_R_Congruence"
proof(unfold_locales)
  show "Thue_R_Congruence \<subseteq> S\<^sup>\<star> \<times> S\<^sup>\<star>" using T_sig by auto 
  show "\<And>s. s \<in> S\<^sup>\<star> \<Longrightarrow> (s, s) \<in> Thue_R_Congruence" 
    by (simp add: local.cong)
  show "\<And>s t. (s, t) \<in> Thue_R_Congruence \<Longrightarrow> (t, s) \<in> Thue_R_Congruence"
    by (simp add: conversion_inv local.cong)
  show "\<And>s t u. (s, t) \<in> Thue_R_Congruence \<Longrightarrow> (t, u) \<in> Thue_R_Congruence \<Longrightarrow> (s, u) \<in> Thue_R_Congruence" 
    by (metis conversion_def local.cong relto_pair.trans_NS_point)
qed

lemma csr_r_join_step_ctxt_closed: assumes "(u, v) \<in> (csr_r_join_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(b @ u @ a, b @ v @ a) \<in> (csr_r_join_step R)\<^sup>\<leftrightarrow>\<^sup>*" using assms 
  using csr_r_join_step_ctxt_closed sctxt.closed_conversion sctxt_closed_strings by presburger

sublocale mcT: monoid_congruence "S\<^sup>\<star>" "append" \<epsilon> Thue_R_Congruence
proof(unfold_locales)
  show "\<And>a b. a \<in> S\<^sup>\<star> \<Longrightarrow> b \<in> S\<^sup>\<star> \<Longrightarrow> a @ b \<in> S\<^sup>\<star>" using T_sig local.cong by blast
  show "\<epsilon> \<in> S\<^sup>\<star>" by (simp add: Kleene_star.Kleen_star_basis)
  show "\<And>a b c. a \<in> S\<^sup>\<star> \<Longrightarrow> b \<in> S\<^sup>\<star> \<Longrightarrow> c \<in> S\<^sup>\<star> \<Longrightarrow> (a @ b) @ c = a @ b @ c" by auto
  show "\<And>a. a \<in> S\<^sup>\<star> \<Longrightarrow> \<epsilon> @ a = a" by simp
  show "\<And>a. a \<in> S\<^sup>\<star> \<Longrightarrow> a @ \<epsilon> = a" by simp
  show "\<And>a a' b b'. (a, a') \<in> Thue_R_Congruence \<Longrightarrow> (b, b') \<in> Thue_R_Congruence \<Longrightarrow> (a @ b, a' @ b') \<in> Thue_R_Congruence"
  proof -
    fix s s' t t'
    assume ss':"(s, s') \<in> Thue_R_Congruence" and tt':"(t, t') \<in> Thue_R_Congruence"
    then show "(s @ t, s' @ t') \<in> Thue_R_Congruence"
    proof -
      have "(s @ t, s' @ t) \<in> Thue_R_Congruence" using cong csr_r_join_step_ctxt_closed 
        by (metis append.right_neutral empty_append ss')
      moreover have "(s' @ t, s' @ t') \<in> Thue_R_Congruence" using tt' cong csr_r_join_step_ctxt_closed 
        by (metis append.right_neutral)
      ultimately show ?thesis using equiv_r.transitive by blast
    qed
  qed
qed

abbreviation quotient_composition (infixl "[\<cdot>]\<^sub>r" 70) where "s [\<cdot>]\<^sub>r t \<equiv> mcT.quotient_composition s t"

(* Lemma 36(i) *)
sublocale quotR: monoid "S\<^sup>\<star>/Thue_R_Congruence" "([\<cdot>]\<^sub>r)" "equiv_r.Class \<epsilon>"
  using mcT.quotient.monoid_axioms by fastforce

(* Theorem 38(i) *)
theorem conditional_r_semi_Thue_monoid_word_problem: assumes r: "reductive R" and cr:"CR (csr_r_join_step R)" 
  shows "monoid (S\<^sup>\<star>/Thue_R_Congruence) ([\<cdot>]\<^sub>r) (equiv_r.Class \<epsilon>)"  and fn:"\<forall>u \<in> S\<^sup>\<star>. finite (csr_r_join_desc u R)"
    and "(the_NF (csr_r_join_step R) s = the_NF (csr_r_join_step R) t) \<Longrightarrow> equiv_r.Class s = equiv_r.Class t"
    and "(the_NF (csr_r_join_step R) s \<noteq> the_NF (csr_r_join_step R) t) \<Longrightarrow> equiv_r.Class s \<noteq> equiv_r.Class t"
proof -
  have sn:"SN (csr_r_join_step R)" using r SN_and_finite_descendants_csr_r_join_steps fnR by blast
  show "\<forall>u \<in> S\<^sup>\<star>. finite (csr_r_join_desc u R)" using SN_and_finite_descendants_csr_r_join_steps[of R] using fnR r by blast
  show "monoid (S\<^sup>\<star>/Thue_R_Congruence) ([\<cdot>]\<^sub>r) (equiv_r.Class \<epsilon>)" using mcT.quotient.monoid_axioms by blast
  assume theNF:"(the_NF (csr_r_join_step R) s = the_NF (csr_r_join_step R) t)"
  from cr sn theNF obtain u where su:"(s, u) \<in> (csr_r_join_step R)\<^sup>*" and tu:"(t, u) \<in> (csr_r_join_step R)\<^sup>*" and "u \<in> NF(csr_r_join_step R)"
    unfolding the_NF_def by (metis normalizability_E theNF the_NF)
  hence "(s, t) \<in> (csr_r_join_step R)\<^sup>* O ((csr_r_join_step R)\<inverse>)\<^sup>*" using su tu by (metis joinI join_def)
  hence "(s, t) \<in> Thue_R_Congruence" using cong 
    by (simp add: CR_imp_conversionIff_join cr join_def)
  then show "equiv_r.Class s = equiv_r.Class t" 
    using equiv_r.equivalence_axioms equivalence.Class_eq by metis 
next
  assume "(the_NF (csr_r_join_step R) s \<noteq> the_NF (csr_r_join_step R) t)"
  then show "equiv_r.Class s \<noteq> equiv_r.Class t" 
    using equiv_r.equivalence_axioms by (metis SN_and_finite_descendants_csr_r_join_steps conversion_def cr 
    equiv_r.ClassD equiv_r.Class_self equiv_r.left_closed fnR local.cong r rtrancl.rtrancl_refl the_NF_conv)
qed

end

locale conditional_p_semi_Thue = reductive_p_join + conditional_semi_Thue R S 
  for R :: csts and S :: "char set" +
  fixes Thue_P_Congruence :: sts
  assumes cong:"Thue_P_Congruence = (csr_p_join_step R)\<^sup>\<leftrightarrow>\<^sup>*"
    and Thue_P_Congruence_sig:"Thue_P_Congruence \<subseteq> S\<^sup>\<star> \<times> S\<^sup>\<star>"
begin

sublocale equiv_p: equivalence "S\<^sup>\<star>" "Thue_P_Congruence"
proof(unfold_locales)
  show "Thue_P_Congruence \<subseteq> S\<^sup>\<star> \<times> S\<^sup>\<star>" using Thue_P_Congruence_sig by auto 
  show "\<And>s. s \<in> S\<^sup>\<star> \<Longrightarrow> (s, s) \<in> Thue_P_Congruence" 
    by (simp add: local.cong)
  show "\<And>s t. (s, t) \<in> Thue_P_Congruence \<Longrightarrow> (t, s) \<in> Thue_P_Congruence"
    by (simp add: conversion_inv local.cong)
  show "\<And>s t u. (s, t) \<in> Thue_P_Congruence \<Longrightarrow> (t, u) \<in> Thue_P_Congruence \<Longrightarrow> (s, u) \<in> Thue_P_Congruence" 
    by (metis conversion_def local.cong relto_pair.trans_NS_point)
qed

lemma csr_r_join_step_ctxt_closed: assumes "(u, v) \<in> (csr_r_join_step R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(b @ u @ a, b @ v @ a) \<in> (csr_r_join_step R)\<^sup>\<leftrightarrow>\<^sup>*" using assms 
  using csr_r_join_step_ctxt_closed sctxt.closed_conversion sctxt_closed_strings by presburger

sublocale mcP: monoid_congruence "S\<^sup>\<star>" "append" \<epsilon> Thue_P_Congruence
proof(unfold_locales)
  show "\<And>a b. a \<in> S\<^sup>\<star> \<Longrightarrow> b \<in> S\<^sup>\<star> \<Longrightarrow> a @ b \<in> S\<^sup>\<star>" using Thue_P_Congruence_sig local.cong by blast
  show "\<epsilon> \<in> S\<^sup>\<star>" by (simp add: Kleene_star.Kleen_star_basis)
  show "\<And>a b c. a \<in> S\<^sup>\<star> \<Longrightarrow> b \<in> S\<^sup>\<star> \<Longrightarrow> c \<in> S\<^sup>\<star> \<Longrightarrow> (a @ b) @ c = a @ b @ c" by auto
  show "\<And>a. a \<in> S\<^sup>\<star> \<Longrightarrow> \<epsilon> @ a = a" by simp
  show "\<And>a. a \<in> S\<^sup>\<star> \<Longrightarrow> a @ \<epsilon> = a" by simp
  show "\<And>a a' b b'. (a, a') \<in> Thue_P_Congruence \<Longrightarrow> (b, b') \<in> Thue_P_Congruence \<Longrightarrow> (a @ b, a' @ b') \<in> Thue_P_Congruence"
  proof -
    fix s s' t t'
    assume ss':"(s, s') \<in> Thue_P_Congruence" and tt':"(t, t') \<in> Thue_P_Congruence"
    then show "(s @ t, s' @ t') \<in> Thue_P_Congruence"
    proof -
      have "(s @ t, s' @ t) \<in> Thue_P_Congruence" using cong csr_p_join_step_ctxt_closed 
        by (metis append_self_conv2 sctxt.closed_conversion sctxt_closed_strings ss')
      moreover have "(s' @ t, s' @ t') \<in> Thue_P_Congruence" using tt' cong csr_p_join_step_ctxt_closed 
        by (metis sctxt.closed_conversion sctxt_closed_strings self_append_conv)
      ultimately show ?thesis using equiv_p.transitive by blast
    qed
  qed
qed

abbreviation quotient_composition (infixl "[\<cdot>]\<^sub>p" 70) where "s [\<cdot>]\<^sub>p t \<equiv> mcP.quotient_composition s t"

(* Lemma 36(ii) *)
sublocale quotP: monoid "S\<^sup>\<star>/Thue_P_Congruence" "([\<cdot>]\<^sub>p)" "equiv_p.Class \<epsilon>"
  using mcP.quotient.monoid_axioms by fastforce

(* Theorem 38(ii) *)
theorem conditional_p_semi_Thue_monoid_word_problem: assumes r: "reductive R" and cr:"CR (csr_p_join_step R)"
  shows "monoid (S\<^sup>\<star>/Thue_P_Congruence) ([\<cdot>]\<^sub>p) (equiv_p.Class \<epsilon>)" and fn:"\<forall>u \<in> S\<^sup>\<star>. finite (csr_p_join_desc u R)"
    and "(the_NF (csr_p_join_step R) s = the_NF (csr_p_join_step R) t) \<Longrightarrow> equiv_p.Class s \<in> (S\<^sup>\<star>/Thue_P_Congruence) \<and> equiv_p.Class t \<in> (S\<^sup>\<star>/Thue_P_Congruence) \<and> 
        equiv_p.Class s = equiv_p.Class t"
    and "(the_NF (csr_p_join_step R) s \<noteq> the_NF (csr_p_join_step R) t) \<Longrightarrow> equiv_p.Class s \<in> (S\<^sup>\<star>/Thue_P_Congruence) \<and> equiv_p.Class t \<in> (S\<^sup>\<star>/Thue_P_Congruence) \<and> 
        equiv_p.Class s \<noteq> equiv_p.Class t"
proof -
  have sn:"SN (csr_p_join_step R)" using r fnR by (simp add: SN_and_finite_descendants_csr_p_join_steps)
  show "\<forall>u \<in> S\<^sup>\<star>. finite (csr_p_join_desc u R)" using SN_and_finite_descendants_csr_p_join_steps using fnR r by blast
  show "monoid (S\<^sup>\<star>/Thue_P_Congruence) ([\<cdot>]\<^sub>p) (equiv_p.Class \<epsilon>)" using mcP.quotient.monoid_axioms by blast
  assume theNF:"(the_NF (csr_p_join_step R) s = the_NF (csr_p_join_step R) t)"
  from cr sn theNF obtain u where su:"(s, u) \<in> (csr_p_join_step R)\<^sup>*" and tu:"(t, u) \<in> (csr_p_join_step R)\<^sup>*" and "u \<in> NF(csr_p_join_step R)"
    unfolding the_NF_def by (metis normalizability_E theNF the_NF)
  hence "(s, t) \<in> (csr_p_join_step R)\<^sup>* O ((csr_p_join_step R)\<inverse>)\<^sup>*" using su tu by (metis joinI join_def)
  hence "(s, t) \<in> Thue_P_Congruence" using cong 
    by (simp add: CR_imp_conversionIff_join cr join_def)
  then show "equiv_p.Class s \<in> (S\<^sup>\<star>/Thue_P_Congruence) \<and> equiv_p.Class t \<in> (S\<^sup>\<star>/Thue_P_Congruence) \<and> equiv_p.Class s = equiv_p.Class t" 
    using equiv_p.equivalence_axioms equivalence.Class_eq 
    by (metis equiv_p.left_closed equiv_p.natural.map_closed)
next
  assume "(the_NF (csr_p_join_step R) s \<noteq> the_NF (csr_p_join_step R) t)"
  then show "equiv_p.Class s \<in> (S\<^sup>\<star>/Thue_P_Congruence) \<and> equiv_p.Class t \<in> (S\<^sup>\<star>/Thue_P_Congruence) \<and> equiv_p.Class s \<noteq> equiv_p.Class t" 
    using equiv_p.equivalence_axioms equiv_p.natural.map_closed equiv_p.right_closed local.cong fnR
    by (metis SN_and_finite_descendants_csr_p_join_steps conversion_refl cr equiv_p.ClassD equivalence.ClassI r the_NF_conv)
qed

end

end