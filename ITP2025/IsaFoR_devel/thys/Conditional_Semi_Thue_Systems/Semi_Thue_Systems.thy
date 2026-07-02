(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Semi_Thue Systems\<close>

theory Semi_Thue_Systems
  imports
    String_Rewriting
    ShortLex
    Jacobson_Basic_Algebra.Group_Theory
    Jacobson_Basic_Algebra.Set_Theory
begin

hide_const inverse

no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)
no_notation subst_apply_term (infixl "\<cdot>" 67)

inductive_set Kleene_star :: "char set \<Rightarrow> string set"  ("(_\<^sup>\<star>)" [1000] 999)
  for S :: "char set"
  where
    Kleen_star_basis: "[] \<in> S\<^sup>\<star>"
  | Kleene_star_step: "a \<in> S\<^sup>\<star> \<Longrightarrow> b \<in> S \<Longrightarrow> a @ [b] \<in> S\<^sup>\<star>"

lemmas  Kleene_starI =  Kleene_star.intros [intro]
lemmas  Kleene_starE =  Kleene_star.cases [elim]

notation Nil ("\<epsilon>")

locale semi_Thue = 
  fixes R :: sts (* A semi-Thue system *)
    and T:: sts
    and S:: "char set" (* alphabet *)
  assumes cong:"T = (ststep R)\<^sup>\<leftrightarrow>\<^sup>*" (* Thue relation *)
    and "finite S"
    and "S \<noteq> {}"
    and "finite R"
    and R_sig:"(ststep R)\<^sup>* \<subseteq> S\<^sup>\<star> \<times> S\<^sup>\<star>"
begin

sublocale mo: monoid "S\<^sup>\<star>" append \<epsilon> 
proof(unfold_locales)
  show "\<And>s t. s \<in> S\<^sup>\<star> \<Longrightarrow> t \<in> S\<^sup>\<star> \<Longrightarrow> s @ t \<in> S\<^sup>\<star>"
    using R_sig local.cong by blast
  show "\<epsilon> \<in> S\<^sup>\<star>" by (simp add: Kleene_star.Kleen_star_basis)
  show "\<And>s t u. s \<in> S\<^sup>\<star> \<Longrightarrow> t \<in> S\<^sup>\<star> \<Longrightarrow> u \<in> S\<^sup>\<star> \<Longrightarrow> (s @ t) @ u = s @ t @ u" by simp
  show "\<And>s. s \<in> S\<^sup>\<star> \<Longrightarrow> \<epsilon> @ s = s" by simp
  show "\<And>s. s \<in> S\<^sup>\<star> \<Longrightarrow> s @ \<epsilon> = s" by simp
qed

sublocale eq: equivalence "S\<^sup>\<star>" "T"
proof(unfold_locales)
  show "T \<subseteq> S\<^sup>\<star> \<times> S\<^sup>\<star>" using R_sig by auto
  show "\<And>s. s \<in> S\<^sup>\<star> \<Longrightarrow> (s, s) \<in> T" 
    by (simp add: local.cong)
  show "\<And>s t. (s, t) \<in> T \<Longrightarrow> (t, s) \<in> T"
    by (simp add: conversion_inv local.cong)
  show "\<And>s t u. (s, t) \<in> T \<Longrightarrow> (t, u) \<in> T \<Longrightarrow> (s, u) \<in> T" 
    by (metis conversion_def local.cong relto_pair.trans_NS_point)
qed

sublocale pt: partition "S\<^sup>\<star>" "(S\<^sup>\<star>/T)"
  by (simp add: eq.partition_axioms)

sublocale mc: monoid_congruence "S\<^sup>\<star>" "append" \<epsilon> T 
proof(unfold_locales)
  show "\<And>s s' t t'. (s, s') \<in> T \<Longrightarrow> (t, t') \<in> T \<Longrightarrow> (s @ t, s' @ t') \<in> T"
  proof -
    fix s s' t t'
    assume ss':"(s, s') \<in> T" and tt':"(t, t') \<in> T"
    then show "(s @ t, s' @ t') \<in> T"
    proof -
      have  "(s @ t, s' @ t) \<in> T" using cong sclosed_trancl ss' by blast
      moreover have "(s' @ t, s' @ t') \<in> T" using tt' 
        by (metis append.right_neutral local.cong sclosed_trancl ststepI)
      ultimately show ?thesis using eq.transitive by blast
    qed
  qed
qed

abbreviation quotient_composition (infixl "[\<cdot>]" 70) where "s [\<cdot>] t \<equiv> mc.quotient_composition s t"

(* Lemma 1 *)
sublocale quot: monoid "S\<^sup>\<star>/T" "([\<cdot>])" "eq.Class \<epsilon>"
  using mc.quotient.monoid_axioms by blast

definition monoid_presentation
  where "monoid_presentation M compos unit \<longleftrightarrow> (\<exists>\<eta>. monoid_isomorphism \<eta> M compos unit (S\<^sup>\<star>/T) ([\<cdot>]) (equivalence.Class (S\<^sup>\<star>) T \<epsilon>))"

definition monoid_finite_presented_by
  where "monoid_finite_presented_by M compos unit \<longleftrightarrow> (\<exists>\<eta>. monoid_isomorphism \<eta> M compos unit (S\<^sup>\<star>/T) ([\<cdot>]) (equivalence.Class (S\<^sup>\<star>) T \<epsilon>) \<and> finite S \<and> finite R)"

definition monoid_presented_by
  where "monoid_presented_by M compos unit = (if (\<exists>\<eta>. monoid_isomorphism \<eta> M compos unit (S\<^sup>\<star>/T) ([\<cdot>]) (equivalence.Class (S\<^sup>\<star>) T \<epsilon>)) then Some (S, R) else None)"

definition "invertible_S \<longleftrightarrow> (\<forall>u \<in> S. mc.quotient.invertible (eq.Class [u]))"

lemma assumes inv_S_imp_inv_S_star:"\<forall>u. u \<in> S \<longrightarrow> (\<exists>v. ([u] @ v, \<epsilon>) \<in> T \<and> (v @ [u], \<epsilon>) \<in> T \<and> v \<in> S\<^sup>\<star>)"
  shows "\<forall>u. u \<in> S\<^sup>\<star> \<longrightarrow> (\<exists>v. (u @ v, \<epsilon>) \<in> T \<and> (v @ u, \<epsilon>) \<in> T \<and> v \<in> S\<^sup>\<star>)"
proof(intro impI allI)
  fix u
  assume "u \<in> S\<^sup>\<star>"
  then show "(\<exists>v. (u @ v, \<epsilon>) \<in> T \<and> (v @ u, \<epsilon>) \<in> T \<and> v \<in> S\<^sup>\<star>)"
  proof(induct)
    case Kleen_star_basis
    then show ?case 
      by auto
  next
    case (Kleene_star_step a b)
    then obtain v where bv:"([b] @ v, \<epsilon>) \<in> T" and vg:"(v @ [b], \<epsilon>) \<in> T" and v:"v \<in> S\<^sup>\<star>" using assms by auto
    from Kleene_star_step obtain w where aw:"(a @ w, \<epsilon>) \<in> T" and wa:"(w @ a, \<epsilon>) \<in> T" and w:"w \<in> S\<^sup>\<star>" by auto
    from bv aw have *:"(a @ [b] @ v @ w, \<epsilon>) \<in> T" 
      by (metis (mono_tags, opaque_lifting) Kleene_star_step.hyps(1) append_Nil append_eq_Cons_conv eq.reflexive eq.transitive mc.cong w)
    moreover have **:"(v @ w @ a @ [b], \<epsilon>) \<in> T"
    proof -
      have "(w @ a @ [b], \<epsilon> @ [b]) \<in> T" using wa by (smt (verit, del_insts) Kleene_star.Kleene_star_step 
            Kleene_star_step.hyps(1) Kleene_star_step.hyps(3) append.assoc append.right_neutral 
            empty_append eq.Class_equivalence mc.Class_cong mo.composition_closed mo.unit_closed w)
      moreover have "(v @ w @ a @ [b], v @ \<epsilon> @ [b]) \<in> T" using calculation mc.cong v by auto
      ultimately show ?thesis using vg eq.transitive by (metis self_append_conv2)
    qed
    show ?case using * ** exI[of _ "v @ w"] by (simp add: v w)
  qed
qed

lemma inv_S_imp_invertible_S: assumes "\<forall>u. u \<in> S \<longrightarrow> (\<exists>v. ([u] @ v, \<epsilon>) \<in> T \<and> (v @ [u], \<epsilon>) \<in> T \<and> v \<in> S\<^sup>\<star>)"
  shows "invertible_S"
proof -
  {
    fix u
    assume uS:"u \<in> S"
    from assms uS obtain v where "([u] @ v, \<epsilon>) \<in> T" and "(v @ [u], \<epsilon>) \<in> T" and "v \<in> S\<^sup>\<star>" by auto
    hence "invertible_S" unfolding invertible_S_def 
      by auto (smt (verit, ccfv_SIG) Kleene_star.Kleen_star_basis Kleene_star.Kleene_star_step append_eq_Cons_conv 
        eq.Block_self eq.Class_eq eq.block_exists assms mc.natural.commutes_with_composition mc.quotient.invertibleI)
  }
  then show ?thesis using invertible_S_def by blast
qed

lemma inv_compose: assumes "invertible_S"
  shows "\<lbrakk>a \<in> S\<^sup>\<star>; mc.quotient.invertible (eq.Class a); b \<in> S\<rbrakk> \<Longrightarrow> mc.quotient.invertible (eq.Class (a @ [b]))"
proof -
  assume aS:"a \<in> S\<^sup>\<star>" and invertible_a:"mc.quotient.invertible (eq.Class a)" and bS:"b \<in> S"
  then show ?thesis
  proof -
    have "mc.quotient.invertible (eq.Class [b])" using assms[unfolded invertible_S_def] bS by auto
    then show ?thesis by (smt (verit, best) Kleene_star.Kleene_star_step aS append_eq_append_conv2 bS 
          eq.natural.map_closed invertible_a mc.Class_commutes_with_composition mc.quotient.composition_invertible 
          mo.right_unit mo.unit_closed same_append_eq)
  qed
qed

lemma invertible_S_imp_invertible_S_star: assumes "invertible_S"
  shows "\<forall>u. u \<in> S\<^sup>\<star>  \<longrightarrow> mc.quotient.invertible (eq.Class u)" 
proof (intro impI allI)
  fix u
  assume asm:"u \<in> S\<^sup>\<star>" 
  then show "mc.quotient.invertible (eq.Class u)"
  proof(induction rule:Kleene_star.induct)
    case Kleen_star_basis
    then show ?case by blast
  next
    case (Kleene_star_step a b)
    then show ?case unfolding mc.quotient.invertible_def using inv_compose[OF assms] by auto
  qed
qed

lemma invertible_S_imp_quotient_invertible: assumes "invertible_S"
  shows "\<forall>u. u \<in> S\<^sup>\<star>/T \<longrightarrow> mc.quotient.invertible u"
proof (intro impI allI)
  fix u
  assume asm:"u \<in> S\<^sup>\<star>/T"
  then show "mc.quotient.invertible u" using invertible_S_imp_invertible_S_star[OF assms] by auto
qed


lemma quotient_monoid_group: assumes "\<forall>u. u \<in> S\<^sup>\<star>/T \<longrightarrow> mc.quotient.invertible u"
  shows "group (S\<^sup>\<star>/T) ([\<cdot>]) (eq.Class \<epsilon>)" using assms
  by (meson Group_Theory.group.intro Group_Theory.group_axioms_def mc.quotient.monoid_axioms)

(* Lemma 3 *)
lemma quotient_monoid_group_invertible: assumes "\<forall>u. u \<in> S \<longrightarrow> (\<exists>v. ([u] @ v, \<epsilon>) \<in> T \<and> (v @ [u], \<epsilon>) \<in> T \<and> v \<in> S\<^sup>\<star>)"
  shows "group (S\<^sup>\<star>/T) ([\<cdot>]) (eq.Class \<epsilon>)"
proof -
  from assms have "invertible_S" using inv_S_imp_invertible_S by fastforce
  hence "\<forall>u. u \<in> S\<^sup>\<star>/T \<longrightarrow> mc.quotient.invertible u" using invertible_S_imp_quotient_invertible by auto
  then show ?thesis using quotient_monoid_group by auto
qed

corollary Thue_word_problem_pre: assumes "(u, v) \<in> T"
  shows "eq.Class u = eq.Class v" using assms eq.Class_eq by blast

corollary Thue_word_problem_pre2: assumes "(u, v) \<in> T"
  shows "\<forall>w. w \<in> S\<^sup>\<star>/T \<longrightarrow> ((u \<in> w \<and> v \<in> w) \<or> (u \<notin> w \<and> v \<notin> w))" using assms Thue_word_problem_pre
  by (metis eq.Block_self eq.ClassI eq.Class_revI)

(* Theorem 10 *)
theorem Semi_Thue_monoid_word_problem: assumes cr:"CR (ststep R)" and sn:"SN (ststep R)"
  shows "monoid (S\<^sup>\<star>/T) ([\<cdot>]) (eq.Class \<epsilon>)" 
    "(the_NF (ststep R) s = the_NF (ststep R) t) \<Longrightarrow> eq.Class s = eq.Class t"
    "(the_NF (ststep R) s \<noteq> the_NF (ststep R) t) \<Longrightarrow> eq.Class s \<noteq> eq.Class t"
proof -
  show "monoid (S\<^sup>\<star>/T) ([\<cdot>]) (eq.Class \<epsilon>)" using mc.quotient.monoid_axioms by blast
  assume theNF:"(the_NF (ststep R) s = the_NF (ststep R) t)"
  from cr sn theNF obtain u where su:"(s, u) \<in> (ststep R)\<^sup>*" and tu:"(t, u) \<in> (ststep R)\<^sup>*" and "u \<in> NF(ststep R)"
    unfolding the_NF_def by (metis normalizability_E theNF the_NF)
  hence "(s, t) \<in> (ststep R)\<^sup>* O ((ststep R)\<inverse>)\<^sup>*" using su tu by (metis joinI join_def)
  hence "(s, t) \<in> T" using cong 
    by (simp add: CR_imp_conversionIff_join cr join_def)
  then show "eq.Class s = eq.Class t"
    using eq.equivalence_axioms equivalence.Class_eq by metis
next
  assume "(the_NF (ststep R) s \<noteq> the_NF (ststep R) t)"
  then show "eq.Class s \<noteq> eq.Class t" 
    using eq.equivalence_axioms by (metis conversion_refl cr eq.Class_equivalence 
        equivalence.left_closed local.cong sn the_NF_conv)
qed

end

end