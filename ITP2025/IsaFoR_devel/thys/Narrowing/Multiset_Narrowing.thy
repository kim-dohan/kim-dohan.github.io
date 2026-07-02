(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Formalization of multiset narrowing and multiset reduction for E-unification and reachability problems\<close>

theory Multiset_Narrowing
  imports
    Equational_Narrowing_Unification
begin

definition multiset_singleton_ext :: "'a rel \<Rightarrow> 'a multiset rel" where
  "multiset_singleton_ext R = {({#a#} + A, {#b#} + A) | a b A. (a, b) \<in> R}" 

lemma multiset_singleton_ext_mult1: "multiset_singleton_ext R \<subseteq> (mult1 (R^-1))^-1" 
  unfolding multiset_singleton_ext_def 
  by (auto, metis add_mset_add_single converseI mult1_singleton mult1_union)

lemma multiset_singleton_ext_mult: "multiset_singleton_ext R \<subseteq> (mult (R^-1))^-1"
  using multiset_singleton_ext_mult1[of R] 
  using mult_def r_into_trancl' by blast

lemma SN_mult: assumes "SN R" shows "SN ((mult (R^-1))^-1)" 
  using assms unfolding SN_iff_wf converse_converse using wf_mult by auto 

lemma SN_multiset_singleton_ext_mult: assumes "SN R" shows "SN (multiset_singleton_ext R)" 
  by (rule SN_subset[OF SN_mult[OF assms] multiset_singleton_ext_mult])

locale multiset_narrowing =  equational_narrowing R DOTEQ TOP R' F D x
  for R::"('f, 'v:: infinite) trs" 
    and DOTEQ :: 'f ("\<doteq>")
    and TOP :: "'f" ("\<top>") 
    and R' :: "('f, 'v:: infinite) trs" 
    and F :: "'f sig" 
    and D :: "'f sig"
    and x :: 'v
begin

(* Multiset rewriting and multiset narrowing *)

inductive_set multiset_reduction_step where 
    "s \<in># S \<and> T = ((S - {#s#}) + {#t#}) \<and> (s, t) \<in> rstep R \<Longrightarrow> (S, T) \<in> multiset_reduction_step"

inductive_set multiset_narrowing_step where
    "(s \<in># S \<and> T = (subst_term_multiset \<sigma> (S - {#s#}) + {#t#}) \<and> (s, t, \<sigma>) \<in> narrowing_step)
      \<Longrightarrow> (S, T, \<sigma>) \<in> multiset_narrowing_step"

definition multiset_narrowing_rel where 
  "multiset_narrowing_rel = {(S, T) | S T \<sigma>. (S, T, \<sigma>) \<in> multiset_narrowing_step}"

lemmas multiset_reduction_stepI = multiset_reduction_step.intros [intro]
lemmas multiset_reduction_stepE = multiset_reduction_step.cases [elim]
lemmas multiset_narrowing_stepI = multiset_narrowing_step.intros [intro]
lemmas multiset_narrowing_stepE = multiset_narrowing_step.cases [elim]

lemma rm_correspondence:assumes sL:"s \<in># L"
  and st:"(s, t) \<in> (rstep R)\<^sup>*"
shows "(L, L - {#s#} + {#t#}) \<in> (multiset_reduction_step)\<^sup>*"
proof -
  from st obtain n where "(s, t) \<in> (rstep R)^^n" by auto
  then show ?thesis using sL
  proof(induct n arbitrary:t)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    from Suc(2) obtain u where su:"(s, u) \<in> rstep R ^^ n" and ut:"(u, t) \<in>  rstep R" by auto
    hence "(L, L - {#s#} + {#u#}) \<in> multiset_reduction_step\<^sup>*" using Suc(1) sL by auto
    with ut show ?case
      by (metis (no_types, lifting) add_diff_cancel_right' multiset_reduction_stepI rtrancl.simps union_mset_add_mset_right union_single_eq_member)
  qed
qed

(* Acknowledgement: This lemma was formalized by René Thiemann *)
lemma SN_R_imp_SN_multiset_reduction_step: assumes "SN (rstep R)" 
  shows "SN multiset_reduction_step" 
proof (rule SN_subset[OF SN_multiset_singleton_ext_mult[OF assms]], clarify)
  fix a b 
  show "(a, b) \<in> multiset_reduction_step \<Longrightarrow> (a, b) \<in> multiset_singleton_ext (rstep R)"
    apply (cases a b rule: multiset_reduction_step.cases)
    by (auto simp: multiset_singleton_ext_def) (metis insert_DiffM)
qed

lemma CR_correspondence:assumes cr:"CR (rstep R)"
  and snm:"SN (rstep R)"
shows "CR (multiset_reduction_step)"
proof (rule Newman[OF SN_R_imp_SN_multiset_reduction_step[OF snm]])
  from  cr have wcr:"WCR (rstep R)"
    by (meson CR_onD WCR_on_def r_into_rtrancl)
  then show "WCR (multiset_reduction_step)"
  proof -
    { fix L M N
      assume "(L, M) \<in> (multiset_reduction_step) \<and> (L, N) \<in> (multiset_reduction_step)"
      hence LM:"(L, M) \<in> (multiset_reduction_step)" and LN:"(L, N) \<in> (multiset_reduction_step)" by auto
      from LM obtain s1 t1 where s1L:"s1 \<in># L" and M:"M = ((L - {#s1#}) + {#t1#})" and s1t1:"(s1, t1) \<in> rstep R" by auto
      from LN obtain s2 t2 where s2L:"s2 \<in># L" and N:"N = ((L - {#s2#}) + {#t2#})" and s2t2:"(s2, t2) \<in> rstep R" by auto
      hence "(M, N) \<in> join (multiset_reduction_step)" using cr
      proof(cases "s1 = s2")
        case True
        with s1t1 s2t2 have "(t1, t2) \<in> (rstep R)\<^sup>\<down>" using cr by auto
        then obtain t3 where t1t3:"(t1, t3) \<in> (rstep R)\<^sup>*" and t2t3:"(t2, t3) \<in> (rstep R)\<^sup>*" by auto
        from t1t3 rm_correspondence have Ms:"(M, M - {#t1#} + {#t3#}) \<in> (multiset_reduction_step)\<^sup>*" 
          by (metis M add_implies_diff add_mset_add_single add_mset_remove_trivial_eq)
        from t2t3 rm_correspondence have Ns:"(N, N - {#t2#} + {#t3#}) \<in> (multiset_reduction_step)\<^sup>*" 
          by (metis N add_implies_diff add_mset_add_single add_mset_remove_trivial_eq)
        have "M - {#t1#} + {#t3#} = N - {#t2#} + {#t3#}" using M N True by auto
        then show ?thesis using rm_correspondence using Ms Ns by auto
      next
        case False
        with M s2L s2t2 have Ms:"(M, M  - {#s2#} + {#t2#}) \<in> (multiset_reduction_step)" 
          by (metis (no_types, lifting) False add_mset_add_single insert_DiffM insert_noteq_member multiset_reduction_stepI s1L union_iff)
        with N s1L s1t1 have Ns:"(N, N  - {#s1#} + {#t1#}) \<in> (multiset_reduction_step)"
          by (metis (no_types, lifting) False add_mset_add_single insert_DiffM insert_noteq_member multiset_reduction_stepI s2L union_iff)
        have "M  - {#s2#} + {#t2#} = N  - {#s1#} + {#t1#}" using M N 
          by (auto, smt (verit) False add_eq_conv_diff add_mset_remove_trivial diff_union_swap insert_DiffM s1L s2L)
        then show ?thesis using Ms Ns by auto
      qed
    } then show ?thesis 
      by (simp add: WCR_on_def)
  qed
qed

inductive_set multiset_reduction_step_pos::"(('f, 'v) term multiset) rel"
  where 
    "(s \<in># S \<and> T = ((S - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}) \<and> 
    rl \<in> R \<and>  p \<in> poss s \<and> (s |_ p = (fst rl) \<cdot> \<sigma>)) \<Longrightarrow> (S, T) \<in> multiset_reduction_step_pos"

inductive_set multiset_narrowing_step_pos::"(('f, 'v) term multiset \<times> ('f, 'v) term multiset \<times> ('f, 'v) subst) set"
  where
    "(s \<in># S \<and> T = subst_term_multiset \<delta> ((S - {#s#}) + {#replace_at s p (snd rl)#}) \<and>  
         \<omega> \<bullet> rl \<in> R \<and> (vars_term s \<inter> vars_rule rl = {}) \<and> p \<in> fun_poss s \<and> mgu (s |_ p) (fst rl) = Some \<delta>)
      \<Longrightarrow> (S, T, \<delta>) \<in> multiset_narrowing_step_pos"

lemmas multiset_reduction_step_posI = multiset_reduction_step_pos.intros [intro]
lemmas multiset_reduction_step_posE = multiset_reduction_step_pos.cases [elim]
lemmas multiset_narrowing_step_posI = multiset_narrowing_step_pos.intros [intro]
lemmas multiset_narrowing_step_posE = multiset_narrowing_step_pos.cases [elim]

lemma mul_reduction_correspondence [simp]:"(S, T) \<in> multiset_reduction_step \<Longrightarrow> (S, T) \<in> multiset_reduction_step_pos" and
      "(S, T) \<in> multiset_reduction_step_pos \<Longrightarrow> (S, T) \<in> multiset_reduction_step" 
proof -
  show "(S, T) \<in> multiset_reduction_step \<Longrightarrow> (S, T) \<in> multiset_reduction_step_pos"
  proof -
    assume asm:"(S, T) \<in> multiset_reduction_step"
    then show "(S, T) \<in> multiset_reduction_step_pos"
    proof -
      from asm obtain s t where "s \<in># S \<and> T = ((S - {#s#}) + {#t#}) \<and> (s, t) \<in> rstep R" by auto
      hence "\<exists>p rl \<sigma>. (s \<in># S \<and> T = ((S - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}) \<and> 
        rl \<in> R \<and>  p \<in> poss s \<and> (s |_ p = (fst rl) \<cdot> \<sigma>))" 
        by (smt (verit) ctxt_of_pos_term_hole_pos fst_conv hole_pos_poss rstep.simps snd_conv subt_at_hole_pos)
      then show ?thesis by blast
    qed
  qed
  show "(S, T) \<in> multiset_reduction_step_pos \<Longrightarrow> (S, T) \<in> multiset_reduction_step"
  proof -
    assume asm:"(S, T) \<in> multiset_reduction_step_pos"
    then show "(S, T) \<in> multiset_reduction_step"
    proof -
      from asm obtain s  rl p \<sigma> where "(s \<in># S \<and> T = ((S - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}) \<and> 
        rl \<in> R \<and>  p \<in> poss s \<and> (s |_ p = (fst rl) \<cdot> \<sigma>))" by auto
      then show ?thesis by (metis multiset_reduction_stepI prod.exhaust_sel replace_at_ident rstepI)
    qed
  qed
qed

lemma mul_narrowing_correspondence [simp]:"(S, T, \<delta>) \<in> multiset_narrowing_step \<Longrightarrow> (S, T, \<delta>) \<in> multiset_narrowing_step_pos" and
  "(S, T, \<delta>) \<in> multiset_narrowing_step_pos \<Longrightarrow> (S, T, \<delta>) \<in> multiset_narrowing_step"
proof -
  show "(S, T, \<delta>) \<in> multiset_narrowing_step \<Longrightarrow> (S, T, \<delta>) \<in> multiset_narrowing_step_pos"
  proof -
    assume asm:"(S, T, \<delta>) \<in> multiset_narrowing_step"
    show "(S, T, \<delta>) \<in> multiset_narrowing_step_pos"
    proof -
      from asm obtain  s t where s:"s \<in># S" and ST:"T = (subst_term_multiset \<delta> (S - {#s#}) + {#t#})" and st\<delta>:"(s, t, \<delta>) \<in> narrowing_step" by auto
      from st\<delta> obtain \<omega> rl p where t:"t = (replace_at s p (snd rl)) \<cdot> \<delta>" and rl:"\<omega> \<bullet> rl \<in> R" and srl:"(vars_term s \<inter> vars_rule rl = {})"
        and p:"p \<in> fun_poss s" and mgu:"mgu (s |_ p) (fst rl) = Some \<delta>" by auto
      have T:"T = subst_term_multiset \<delta> ((S - {#s#}) + {#replace_at s p (snd rl)#})" 
        by (metis ST t add_mset_add_single image_mset_add_mset subst_term_multiset_def)
      show ?thesis using multiset_narrowing_step_pos.intros[of s S T \<delta> p rl \<omega>]
        using T mgu p rl s srl by auto
    qed
  qed
  show "(S, T, \<delta>) \<in> multiset_narrowing_step_pos \<Longrightarrow> (S, T, \<delta>) \<in> multiset_narrowing_step"
  proof -
    assume asm:"(S, T, \<delta>) \<in> multiset_narrowing_step_pos"
    show "(S, T, \<delta>) \<in> multiset_narrowing_step"
    proof -
      from asm obtain s p rl  \<omega> where *:"(s \<in># S \<and> T = subst_term_multiset \<delta> ((S - {#s#}) + {#replace_at s p (snd rl)#}) \<and>  
         \<omega> \<bullet> rl \<in> R \<and> (vars_term s \<inter> vars_rule rl = {}) \<and> p \<in> fun_poss s \<and> mgu (s |_ p) (fst rl) = Some \<delta>)" by auto
      then show ?thesis unfolding subst_term_multiset_def 
        by (smt (verit)* add_mset_add_single image_mset_add_mset multiset_narrowing.multiset_narrowing_step.simps 
            multiset_narrowing_axioms narrowing_stepI subst_term_multiset_def)
    qed
  qed
qed

definition multiset_narrowing_step'::"(('f, 'v) term multiset) rel" where 
  "multiset_narrowing_step' = {(S, T) | S T \<sigma>. (S, T, \<sigma>) \<in> multiset_narrowing_step}"

definition multiset_narrowing_derivation :: "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "multiset_narrowing_derivation S S' \<sigma> \<longleftrightarrow> (\<exists>n. (S,  S') \<in> (multiset_narrowing_step')^^n \<and> (\<exists>f \<tau>. f 0 = S \<and> f n = S' \<and> 
  (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"
term n
definition multiset_narrowing_derivation_num :: "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset \<Rightarrow> ('f, 'v) subst \<Rightarrow> nat \<Rightarrow> bool" where
  "multiset_narrowing_derivation_num S S' \<sigma> n \<longleftrightarrow> ((S,  S') \<in> (multiset_narrowing_step')^^n \<and> (\<exists>f \<tau>. f 0 = S \<and> f n = S' \<and> 
  (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

lemma n0_multiset_narrowing_derivation_num:"multiset_narrowing_derivation_num S S' \<sigma> 0 \<Longrightarrow> S = S' \<and> \<sigma> = Var" 
  unfolding multiset_narrowing_derivation_num_def by auto

lemma multiset_narrowing_deriv_implication: assumes "multiset_narrowing_derivation_num S S' \<sigma> n"
  shows "multiset_narrowing_derivation S S' \<sigma>" 
  unfolding multiset_narrowing_derivation_num_def multiset_narrowing_derivation_def
  using assms multiset_narrowing_derivation_num_def by metis

lemma multiset_narrowing_set_imp_rtran: assumes "(S, T, \<sigma>) \<in> multiset_narrowing_step"
  shows "multiset_narrowing_derivation_num S T \<sigma> 1"
proof -
  have *:"(S, T) \<in> multiset_narrowing_step'" using assms 
    using multiset_narrowing_step'_def by auto
  then obtain f where f0:"f 0 = S" and f1:"f 1 = T" and rel_chain:"(f 0,  f (Suc 0)) \<in> multiset_narrowing_step'" 
    by (metis One_nat_def relpow_0_I relpow_Suc_I relpow_fun_conv)
  let ?\<tau> = "\<lambda>i. (if i = 0 then \<sigma> else Var)"
  show ?thesis  unfolding multiset_narrowing_derivation_num_def
  proof(intro conjI, goal_cases)
    case 1
    then show ?case by (simp add: *)
  next
    case 2
    then show ?case by (rule exI[of _ f], rule exI[of _ ?\<tau>], insert assms f0 f1, auto)
  qed
qed

lemma subst_term_multiset_perm_conv_main: fixes xs::"('f, 'v)rule list"
  shows "{#t \<cdot> sop \<omega>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset xs#}#} = 
    {#Fun \<doteq> [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #}"
proof -
  have "{#t \<cdot> sop \<omega>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset xs#}#} = 
          {# (Fun \<doteq> [u, v]) \<cdot> sop \<omega>. (u, v) \<in># mset xs #}"
  proof(auto split:prod.splits, induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case by (auto split:prod.splits)
  qed
  also have "... = {#Fun \<doteq> [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #}"
  proof(auto split:prod.splits, induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case by (auto split:prod.splits simp add: rule_pt.permute_prod.simps ) 
  qed
  finally show ?thesis by auto
qed

lemma subst_term_multiset_perm_conv_pre: fixes xs::"('f, 'v)rule list"
  shows "{# (t \<cdot> \<theta>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (xs) #}#} = 
  {# (t \<cdot> (sop \<omega> \<circ>\<^sub>s \<theta>)). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> xs) #} #}"
proof -
  let ?M = "{# Fun (\<doteq>) [u, v]. (u, v) \<in># mset xs #}"
  let ?Q = "{# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> xs) #}"
  have "?Q = subst_term_multiset (sop (- \<omega>)) ?M"
  proof -
    have "{#Fun \<doteq> [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> xs) #} = {#t \<cdot> sop (- \<omega>). t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset xs#}#}" 
      using subst_term_multiset_perm_conv_main by metis 
    then show ?thesis 
      by (simp add: subst_term_multiset_def)
  qed
  then show ?thesis
    by (smt (verit) comp_apply multiset.map_comp multiset.map_cong0 subst_subst_compose 
        subst_term_multiset_def term_apply_subst_Var_Rep_perm term_pt.permute_minus_cancel(1))
qed

lemma subst_compose_o_assoc:
  "(\<sigma> \<circ>\<^sub>s \<tau>) \<circ> f = (\<sigma> \<circ> f) \<circ>\<^sub>s \<tau>"
  by (rule ext) (simp add: subst_compose)

lemma subst_term_multiset_perm_conv: fixes xs::"('f, 'v)rule list"
  assumes "\<theta> = sop \<omega> \<circ>\<^sub>s \<sigma>"
  shows "subst_term_multiset \<sigma> {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #} = subst_term_multiset \<theta> {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset xs #}"
proof -
  have \<sigma>:"\<sigma> = sop (- \<omega>) \<circ>\<^sub>s \<theta>" using assms  
    by (metis permute_subst_subst_compose subst_compose_o_assoc subst_monoid_mult.mult.left_neutral subst_pt.permute_minus_cancel(2))
  have "subst_term_multiset \<sigma> {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #} = {# (t \<cdot> \<sigma>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #} #}"
    unfolding subst_term_multiset_def by auto
  also have "... = {# (t \<cdot> sop (- \<omega>) \<circ>\<^sub>s \<theta>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #} #}" using \<sigma> by force
  also have "... = {# (t \<cdot> sop \<omega> \<circ>\<^sub>s sop (- \<omega>) \<circ>\<^sub>s \<theta>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> \<omega> \<bullet> xs) #} #}" 
    using \<sigma> subst_term_multiset_perm_conv_pre 
    by (metis subst_compose_assoc)
  also have "... = {# (t \<cdot>  \<theta>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> \<omega> \<bullet> xs) #} #}" by auto
  finally show ?thesis by (simp add: subst_term_multiset_def)
qed

lemma subst_subtract_term_multiset: assumes "subst_domain \<sigma> \<subseteq> vars_term_set (set_mset S)"
  and "u \<in># S"
shows "subst_term_multiset \<sigma> (S - {#u#}) = subst_term_multiset \<sigma> S - subst_term_multiset \<sigma> {#u#}" 
proof -
  have "subst_term_multiset \<sigma> (S - {#u#}) \<subseteq># subst_term_multiset \<sigma> S - subst_term_multiset \<sigma> {#u#}"
    unfolding subst_term_multiset_def using assms 
    by (simp add: image_mset_Diff)
  moreover have "subst_term_multiset \<sigma> S - subst_term_multiset \<sigma> {#u#} \<subseteq># subst_term_multiset \<sigma> (S - {#u#})"
    unfolding subst_term_set_def using assms
    by (simp add: image_mset_Diff subst_term_multiset_def)
  ultimately show ?thesis by simp
qed

lemma subst_term_multiset_union: "subst_term_multiset \<sigma> (M + N) = subst_term_multiset \<sigma> M + subst_term_multiset \<sigma> N" 
  unfolding subst_term_multiset_def by simp

lemma multiset_nar_vars_finite: assumes "multiset_narrowing_derivation_num S S' \<sigma> n"
  and "finite (vars_term_set (set_mset S))"
shows "finite (vars_term_set (set_mset S'))" using assms
proof( induct n arbitrary: S' \<sigma>)
  case 0
  then show ?case 
    using n0_multiset_narrowing_derivation_num by auto
next
  case (Suc n)
  from Suc have "multiset_narrowing_derivation_num S S' \<sigma> (Suc n)" by auto
  hence SS':"(S,  S') \<in> (multiset_narrowing_step')^^(Suc n)" and relchain':"(\<exists>f \<tau>. f 0 = S \<and> f (Suc n) = S' \<and> 
    (\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step) \<and> (\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (Suc n)])))"
    unfolding multiset_narrowing_derivation_num_def by auto
  from relchain' obtain f \<tau> where f0:"f 0 = S" and fsucn:"f (Suc n) = S'" and 
    relchain:"\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step" 
    and \<sigma>:"(\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (Suc n)]))" by auto
  let ?\<tau> = "compose (map (\<lambda>i. (\<tau> i)) [0 ..< n])"
  let ?\<sigma> = "if n = 0 then Var else ?\<tau>"
  let ?f = "\<lambda>i. (if i \<le> n then f i else undefined)"
  from relchain obtain U where U:"f n = U" by simp
  from relchain have nchain:"\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step" by simp
  hence f0fn:"(f 0, f n) \<in> (multiset_narrowing_step')^^n" unfolding multiset_narrowing_step'_def 
    by (smt (verit, del_insts) mem_Collect_eq relpow_fun_conv)
  have "(S,  U) \<in> (multiset_narrowing_step')^^n" using f0 U f0fn by auto
  moreover have "(\<exists>f \<tau>. f 0 = S \<and> f n = U \<and> (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step))"
    by (rule exI[of _ "?f"] rule exI[of _ "?\<sigma>"], insert U f0 nchain, auto)
  moreover have "multiset_narrowing_derivation_num S U ?\<sigma> n" unfolding multiset_narrowing_derivation_num_def
    using U calculation f0 nchain by auto 
  ultimately have finiteU:"finite (vars_term_set (set_mset U))" using Suc by auto
  have "\<exists>\<delta>. (U, S', \<delta>) \<in> multiset_narrowing_step" using relchain fsucn U by auto
  then obtain \<delta> where "(U, S', \<delta>) \<in> multiset_narrowing_step" by auto
  then obtain s rl \<omega> p where "s \<in># U" and S'eq:"S' = subst_term_multiset \<delta> ((U - {#s#}) + {#replace_at s p (snd rl)#})"
    and "\<omega> \<bullet> rl \<in> R" and "(vars_term s \<inter> vars_rule rl = {})" and "p \<in> fun_poss s" and  mgu:"mgu (s |_ p) (fst rl) = Some \<delta>" 
    using mul_narrowing_correspondence by blast
  from S'eq have *:"S' = subst_term_multiset \<delta> (U - {#s#}) + subst_term_multiset \<delta> {#replace_at s p (snd rl)#}" (is "S' = ?A + ?B")
    by (metis subst_term_multiset_union)
  have "vars_term_set (set_mset S') = vars_term_set (set_mset ?A) \<union> vars_term_set (set_mset ?B)"
    unfolding vars_term_set_def using "*" by auto
  moreover have "finite (vars_term_set (set_mset ?A))" 
    unfolding vars_term_set_def using finiteU mgu_finite_range_vars[OF mgu] finite_vars_term by blast
  moreover have "finite (vars_term_set (set_mset ?B))" unfolding vars_term_set_def by simp
  ultimately show ?case using * by auto
qed

lemma wf_eq_mset_subst_inv: fixes \<theta>:: "('f, 'v) subst"
  assumes "wf_equational_term_mset M"
  shows "wf_equational_term_mset (subst_term_multiset \<theta> M)" 
proof -
  let ?M = "subst_term_multiset \<theta> M"
  from assms have "(\<forall>t \<in># M. wf_equational_term t)" unfolding wf_equational_term_mset_def by simp
  moreover have "?M = {# (t \<cdot> \<theta>). t \<in># M #}" unfolding subst_term_multiset_def by auto
  moreover have "\<forall>s \<in># M. wf_equational_term s" by (simp add: calculation)
  then show ?thesis unfolding subst_term_multiset_def wf_equational_term_mset_def 
    using wf_eq_subst by auto
qed

lemma wf_equational_term_mset_add: assumes "wf_equational_term_mset A" and "wf_equational_term_mset B"
  shows "wf_equational_term_mset (A + B)" using assms
  using wf_equational_term_mset_def by (metis union_iff)

lemma root_not_special_symbols: assumes "rl \<in> R'"
  and "funas_rule rl \<subseteq> F"
  and rnone:"root (fst rl) \<noteq> None"
shows "root (fst rl) \<noteq> Some (\<doteq>, 2) \<and> root (fst rl) \<noteq> Some (\<top>, 0)" 
  using assms root_special_notin_F unfolding  D D_fresh R_sig 
    funas_rule_def funas_trs_def by auto 

lemma vars_cond_perm:"vars_trs (trs) \<subseteq> vars_term t \<Longrightarrow> vars_trs (\<omega> \<bullet> trs) \<subseteq> vars_term (\<omega> \<bullet> t)"
  unfolding vars_trs_def vars_rule_def by auto (smt (verit, ccfv_threshold) SUP_le_iff atom_set_pt.subset_eqvt 
      fst_conv le_supE rule_pt.fst_eqvt subsetD term_pt.permute_minus_cancel(1) trs_pt.eq_eqvt trs_pt.inv_mem_simps(1) 
      vars_term_eqvt, smt (verit, ccfv_threshold) SUP_le_iff atom_set_pt.subset_eqvt le_supE rule_pt.snd_eqvt 
      snd_conv subsetD term_pt.permute_minus_cancel(1) trs_pt.eq_eqvt trs_pt.inv_mem_simps(1) vars_term_eqvt)

lemma multiset_narrowing_based_reachable_single: 
  assumes nar:"(S, T, \<sigma>) \<in> multiset_narrowing_step"
  shows "(subst_term_multiset \<sigma> S, T) \<in> multiset_reduction_step"
proof -
  from nar obtain s p rl \<omega> where s:"s \<in># S" and T:"T = subst_term_multiset \<sigma> ((S - {#s#}) + {#replace_at s p (snd rl)#})" and 
    rl:"\<omega> \<bullet> rl \<in> R" and varcond:"(vars_term s \<inter> vars_rule rl = {})" and p:"p \<in> fun_poss s" and mgu:"mgu (s |_ p) (fst rl) = Some \<sigma>"
    using mul_narrowing_correspondence by blast
  let ?S = "subst_term_multiset \<sigma> S"
  let ?s = "s \<cdot> \<sigma>"
  let ?T = "(?S - {#?s#}) + {#replace_at ?s p (snd rl \<cdot> (((sop \<omega>) \<circ>\<^sub>s \<sigma>)))#}"
  have perm_fst_rl:"fst (\<omega> \<bullet> rl) \<cdot> ((sop (- \<omega>)) \<circ>\<^sub>s \<sigma>) = fst rl \<cdot> \<sigma>" by (simp add: rule_pt.fst_eqvt)
  have perm_snd_rl:"snd (\<omega> \<bullet> rl) \<cdot> ((sop (- \<omega>)) \<circ>\<^sub>s \<sigma>) = snd rl \<cdot> \<sigma>" by (simp add: rule_pt.snd_eqvt)
  from mgu have sp:"(s |_ p) \<cdot> \<sigma> = (fst rl) \<cdot> \<sigma>" using mgu subst_apply_term_eq_subst_apply_term_if_mgu by auto
  have sS:"?s \<in># ?S" unfolding subst_term_multiset_def using s by auto
  have T_new:"T = ?S - {#?s#} + {#replace_at ?s p (snd (\<omega> \<bullet> rl) \<cdot> (sop (- \<omega>) \<circ>\<^sub>s \<sigma>))#}" using T  perm_snd_rl 
    by (smt (verit) add_mset_add_single add_mset_remove_trivial ctxt_of_pos_term_subst fun_poss_imp_poss 
        image_mset_add_mset insert_DiffM p s subst_apply_term_ctxt_apply_distrib subst_term_multiset_def)
  have pfun:"p \<in> fun_poss ?s" using p by (metis (no_types, opaque_lifting) fun_poss_fun_conv fun_poss_imp_poss 
    funas_term.cases is_FunI poss_imp_subst_poss poss_is_Fun_fun_poss subst_apply_eq_Var subt_at_subst term.distinct(1))
  have "(s |_ p) \<cdot> \<sigma> = (?s |_ p)" using p pfun by (simp add: fun_poss_imp_poss)
  hence *:"?s |_ p = (fst (\<omega> \<bullet> rl)) \<cdot> (sop (- \<omega>) \<circ>\<^sub>s \<sigma>)" using sp perm_fst_rl by auto
  have "(subst_term_multiset \<sigma> S, T) \<in> multiset_reduction_step_pos"
  proof(rule multiset_reduction_step_pos.intros, intro conjI)
    show "?s \<in># subst_term_multiset \<sigma> S" using sS by auto
    show "T = subst_term_multiset \<sigma> S - {#s \<cdot> \<sigma>#} + {#(ctxt_of_pos_term p (s \<cdot> \<sigma>))\<langle>snd (\<omega> \<bullet> rl) \<cdot> (sop (- \<omega>) \<circ>\<^sub>s \<sigma>)\<rangle>#}"
      using T_new by auto 
    show "\<omega> \<bullet> rl \<in> R" using rl by auto
    show "p \<in> poss (s \<cdot> \<sigma>)" using pfun 
      by (simp add: fun_poss_imp_poss)
    show "s \<cdot> \<sigma> |_ p = fst (\<omega> \<bullet> rl) \<cdot> sop (- \<omega>) \<circ>\<^sub>s \<sigma>" by (simp add: *)
  qed
  then show ?thesis 
    by (smt (verit, ccfv_SIG) multiset_narrowing.multiset_reduction_step.simps multiset_narrowing.multiset_reduction_step_posE 
        multiset_narrowing_axioms prod.exhaust_sel replace_at_ident rstepI)
qed

lemma subst_closed_multiset_reduction: assumes st:"(S, T) \<in> (multiset_reduction_step)\<^sup>*"
  shows "(subst_term_multiset \<sigma> S, subst_term_multiset \<sigma> T) \<in> (multiset_reduction_step)\<^sup>*"
proof -
  from st obtain n where "(S, T) \<in> (multiset_reduction_step)^^n" by auto
  then show ?thesis
  proof(induct n arbitrary: T)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain U where SU:"(S, U) \<in> multiset_reduction_step ^^ n" and UT:"(U, T) \<in> multiset_reduction_step" by auto
    have "(subst_term_multiset \<sigma> S, subst_term_multiset \<sigma> U) \<in> multiset_reduction_step\<^sup>*" using Suc SU by auto
    moreover
    { 
      from UT obtain s p rl \<theta> where sU:"s \<in># U" and T:"T = ((U - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<theta>)#})" and 
        rl:"rl \<in> R" and p:"p \<in> poss s" and sp:"(s |_ p = (fst rl) \<cdot> \<theta>)" using mul_reduction_correspondence by blast
      let ?U = "subst_term_multiset \<sigma> U"
      let ?T = "subst_term_multiset \<sigma> T"
      let ?s = "s \<cdot> \<sigma>"
      have pfun:"p \<in> fun_poss ?s" using p
        by (metis Un_iff fun_root_not_None is_VarE local.wf poss_imp_subst_poss poss_simps(2) prod.collapse rl 
            root.simps(1) root_subst_inv sp subt_at_subst var_poss_iff weak_match.simps(2) weak_match_match wf_trs_imp_lhs_Fun)
      have T_new:"?T = ((?U - {#?s#}) + {#replace_at ?s p (((snd rl) \<cdot> \<theta>) \<cdot> \<sigma>)#})" unfolding subst_term_multiset_def using T
        by (simp add: sU ctxt_of_pos_term_subst fun_poss_imp_poss image_mset_Diff p)
      have *:"(?s |_ p = ((fst rl) \<cdot> \<theta>) \<cdot> \<sigma>)" using sp pfun by (simp add: fun_poss_imp_poss p)
      have "(subst_term_multiset \<sigma> U, subst_term_multiset \<sigma> T) \<in> (multiset_reduction_step_pos)"
      proof(rule multiset_reduction_step_pos.intros, intro conjI)
        show "?s \<in># subst_term_multiset \<sigma> U" 
          by (simp add: sU subst_term_multiset_def)
        show "subst_term_multiset \<sigma> T = subst_term_multiset \<sigma> U - {#s \<cdot> \<sigma>#} + {#replace_at ?s p ((snd rl) \<cdot> (\<theta> \<circ>\<^sub>s \<sigma>))#}" 
          using T_new by auto
        show "rl \<in> R" using rl by auto
        show "p \<in> poss (s \<cdot> \<sigma>)" using p by auto
        show "s \<cdot> \<sigma> |_ p = fst rl \<cdot> \<theta> \<circ>\<^sub>s \<sigma>" by (simp add: *)
      qed
    }
    ultimately show ?case by (smt (verit, ccfv_SIG) multiset_narrowing.multiset_reduction_step.simps 
      multiset_narrowing.multiset_reduction_step_pos.simps multiset_narrowing_axioms prod.exhaust_sel 
      replace_at_ident rstepI rtrancl.rtrancl_into_rtrancl)
  qed
qed

lemma multiset_narrowing_reduction: 
  assumes nd:"multiset_narrowing_derivation S S' \<sigma>"
  shows "(subst_term_multiset \<sigma> S, S') \<in> (multiset_reduction_step)\<^sup>*" 
proof -
  from nd obtain n where "multiset_narrowing_derivation_num S S' \<sigma> n" unfolding multiset_narrowing_derivation_def 
      multiset_narrowing_derivation_num_def by auto
  then show ?thesis
  proof(induct n arbitrary: S' \<sigma>)
    case 0
    then show ?case using n0_multiset_narrowing_derivation_num unfolding subst_term_multiset_def
      by (metis multiset.map_ident_strong rtrancl.simps subst.cop_nil)
  next
    case (Suc n)
    from \<open>multiset_narrowing_derivation_num S S' \<sigma> (Suc n)\<close>
    have "(\<exists>f \<tau>. f 0 = S \<and> f (Suc n) = S' \<and> 
      (\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step) \<and> (\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< Suc n])))"
      unfolding multiset_narrowing_derivation_num_def by auto
    then obtain f \<tau> where f0:"f 0 = S" and fsucn:"f (Suc n) = S'" and 
      relchain:"\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step" 
      and \<sigma>:"(\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (Suc n)]))" by auto
    let ?\<tau> = "compose (map (\<lambda>i. (\<tau> i)) [0 ..< n])"
    let ?\<sigma> = "if n = 0 then Var else ?\<tau>"
    let ?f = "\<lambda>i. (if i \<le> n then f i else undefined)"
     from relchain obtain U where U:"f n = U" by simp
    from relchain have nchain:"\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step" by simp
    have "(\<exists>f \<tau>. f 0 = S \<and> f n = U \<and> (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step))"
      by (rule exI[of _ "?f"] rule exI[of _ "?\<sigma>"], insert U f0 nchain, auto)
    moreover have "multiset_narrowing_derivation_num S U ?\<sigma> n" unfolding multiset_narrowing_derivation_num_def
      using U calculation f0 nchain by (auto, smt (verit, ccfv_threshold) CollectI multiset_narrowing_step'_def relpow_fun_conv)
    ultimately have IH:"(subst_term_multiset ?\<sigma> S, U) \<in> multiset_reduction_step\<^sup>*" using Suc(1) by auto
    have "(U, S', \<tau> n) \<in> multiset_narrowing_step" using relchain fsucn U by auto
    from multiset_narrowing_based_reachable_single[OF this]
    have *:"(subst_term_multiset (\<tau> n) U, S') \<in> multiset_reduction_step" by auto
    have \<sigma>:"\<sigma> = ?\<sigma> \<circ>\<^sub>s (\<tau> n)" using \<sigma> by auto 
    from subst_closed_multiset_reduction[of "subst_term_multiset ?\<sigma> S" U "\<tau> n"]
    have "(subst_term_multiset \<sigma> S, subst_term_multiset (\<tau> n) U) \<in> multiset_reduction_step\<^sup>*" using \<sigma>
      by (simp add: IH subst_term_multiset_compose)
    then show ?case using * by auto
  qed
qed

lemma addFunT:assumes "(\<forall>s\<in>#S. s = Fun \<top> [])"
  and "(\<forall>t\<in>#T. t = Fun \<top> [])"
shows "\<forall>u \<in># S + T. u = Fun \<top> []" using assms 
  by (meson union_iff)

lemma multiset_red_add:assumes st:"(S, T) \<in> (multiset_reduction_step)\<^sup>*"
  shows "(S + U, T + U) \<in> (multiset_reduction_step)\<^sup>*" using assms
proof (induct rule:rtrancl.induct)
  case (rtrancl_refl a)
  then show ?case by auto
next
  case (rtrancl_into_rtrancl a b c)
  from \<open>(b, c) \<in> multiset_reduction_step\<close>
  obtain s rl \<sigma> p where s:"s \<in># b" and c:"c = ((b - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#})" and rl:"rl \<in> R" and 
    p:"p \<in> poss s" and sp:"(s |_ p = (fst rl) \<cdot> \<sigma>)" using mul_reduction_correspondence by blast
  hence "(b + U, c + U) \<in> multiset_reduction_step"
    by (smt (verit, ccfv_threshold) add.assoc add.commute add_mset_remove_trivial insert_DiffM 
        multiset_reduction_step.simps rtrancl_into_rtrancl.hyps(3) union_iff union_mset_add_mset_right)
  then show ?case using rtrancl_into_rtrancl by auto
qed

lemma multiset_red_combine_goal: assumes UT:"(U, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])"
  and VT':"(V, T') \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T'. t = Fun (\<top>) [])"
shows "\<exists>P. (U + V, P) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># P. t = Fun (\<top>) [])" using assms
proof -
  have "(U + V, T + V) \<in> (multiset_reduction_step)\<^sup>*" using multiset_red_add UT by auto
  moreover have "(T + V, T + T') \<in> (multiset_reduction_step)\<^sup>*" using multiset_red_add VT' by (metis add.commute)
  moreover have "(U + V, T + T') \<in> (multiset_reduction_step)\<^sup>*" using calculation(1) calculation(2) by auto
  ultimately show ?thesis by (meson UT VT' union_iff)
qed

lemma multiset_red_refl: "({#Fun \<doteq> [u, u]#}, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)" 
proof -
  have "\<exists>x. ((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])) \<in> R" using R' by auto
  then obtain x::'v where rl:"((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])) \<in> R" by auto
  have "is_Fun (Fun \<doteq> [u, u])" by auto
  let ?p = "[]::pos"
  let ?s = "Fun \<doteq> [u, u]"
  let ?\<sigma> = "Var (x := u)" 
  let ?rl = "(Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
  have *:"snd ?rl \<cdot> ?\<sigma> = Fun (\<top>) []" by auto
  have "({#Fun \<doteq> [u, u]#}, {#Fun \<top> []#}) \<in> multiset_reduction_step_pos"
  proof(intro multiset_reduction_step_pos.intros conjI)
    show "?s \<in># {#Fun \<doteq> [u, u]#}" by auto
    show "{#Fun \<top> []#} = {#Fun \<doteq> [u, u]#} - {#?s#} + {#(ctxt_of_pos_term ?p ?s)\<langle>snd ?rl \<cdot> ?\<sigma>\<rangle>#}" 
      using empty_not_add_mset unfolding subst_term_multiset_def by auto
    show "?rl \<in> R" using rl by auto
    show "?p \<in> poss ?s" by simp
    show "?s |_ ?p = fst ?rl \<cdot> ?\<sigma>" using * by auto
  qed
  then show ?thesis using mul_reduction_correspondence 
    by (smt (verit, best) multiset_narrowing.multiset_reduction_step.simps multiset_narrowing.multiset_reduction_step_posE multiset_narrowing_axioms prod.exhaust_sel replace_at_ident rstepI)
qed

lemma trans_reachable_cond_red_step:assumes "(P, Q) \<in> (multiset_reduction_step)"
  and "(Q, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])"
shows "(P, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])" using assms by auto

lemma cond_red_combine_fun: assumes "({#Fun \<doteq> [s\<^sub>1 \<cdot> \<sigma>, t\<^sub>1 \<cdot> \<sigma>]#}, T (s\<^sub>1, t\<^sub>1)) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T (s\<^sub>1, t\<^sub>1). t = Fun \<top> [])" 
  and "({#Fun \<doteq> [s\<^sub>2 \<cdot> \<sigma>, t\<^sub>2 \<cdot> \<sigma>]#}, T (s\<^sub>2, t\<^sub>2)) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T (s\<^sub>2, t\<^sub>2). t = Fun \<top> [])" 
shows "({#Fun \<doteq> [s\<^sub>1 \<cdot> \<sigma>, t\<^sub>1 \<cdot> \<sigma>], Fun \<doteq> [s\<^sub>2 \<cdot> \<sigma>, t\<^sub>2 \<cdot> \<sigma>] #},
    T (s\<^sub>1, t\<^sub>1) + T (s\<^sub>2, t\<^sub>2)) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in># T (s\<^sub>1, t\<^sub>1) + T (s\<^sub>2, t\<^sub>2). t = Fun \<top> [])" using multiset_red_combine_goal 
  by (smt (verit, ccfv_SIG) addFunT add_mset_add_single assms(1) assms(2) multiset_red_add converse_rtrancl_into_rtrancl rtrancl_idemp union_commute)

lemma cond_red_combine_fun_mset: assumes "\<forall>(s\<^sub>i, t\<^sub>i)\<in># mset xs. ({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]#}, T (s\<^sub>i, t\<^sub>i)) \<in> (multiset_reduction_step)\<^sup>*" 
  shows "({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset xs #},
    \<Sum>(u, v)\<in># mset xs. T (u, v)) \<in> (multiset_reduction_step)\<^sup>*" using assms 
proof (induct xs)
  case (Cons pair xs)
  then show ?case using cond_red_combine_fun multiset_red_add union_commute
    by auto (smt (verit) add_mset_add_single converse_rtrancl_into_rtrancl 
        rtrancl_idemp union_commute)
qed auto 

lemma normRR':"normal_subst R \<sigma> \<Longrightarrow> normal_subst R' \<sigma>" using R' unfolding normal_subst_def by blast

lemma not_reducible_T_erstep:"\<not> (\<exists>M. ({#Fun (\<top>) []#}, M) \<in> multiset_reduction_step)" 
proof(rule ccontr)
  assume "\<not> ?thesis"
  then obtain M where *:"({#Fun (\<top>) []#}, M) \<in> multiset_reduction_step" by auto
  then obtain s S p rl \<sigma> where s:"s = Fun (\<top>) []" and S:"S = {#Fun (\<top>) []#}" and sS:"s \<in># S" and 
    M:"M = ((S - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#})" and rl:"rl \<in> R" and p:"p \<in> fun_poss s" and 
    sp:"(s |_ p = (fst rl) \<cdot> \<sigma>)" using mul_reduction_correspondence not_reducible_T by auto
  from M S s have "M = {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}" by auto
  have "\<forall>t. (Fun (\<top>) [], t) \<notin> (rstep R)" using R_sig not_reducible_T by auto
  then show False using s S sS M rl p sp ctxt_supt_id fun_poss_imp_poss prod.exhaust_sel rstep.rstep
    by metis
qed

definition subst_equations_list :: "('f, 'v) subst \<Rightarrow> ('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list" where 
  "subst_equations_list \<sigma> xs = map (\<lambda>p.  subst_equation \<sigma> p) xs"

fun convert_equations_into_term_multiset:: "('f, 'v) rule list \<Rightarrow> ('f, 'v) term multiset"
  where 
    "convert_equations_into_term_multiset [] = {#}"
  | "convert_equations_into_term_multiset xs = {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset xs #}"

lemma convert_equations_into_rule_list_sound: fixes rl::"('f, 'v) rule list"
  assumes "funas_trs (set rl) \<subseteq> F"
  shows "wf_equational_term_mset (convert_equations_into_term_multiset rl)" 
proof(cases "rl = []")
  case True
  then show ?thesis 
    by (simp add: wf_equational_term_def wf_equational_term_mset_def)
next
  case False
  have "funas_trs (set rl) \<subseteq> F" 
    unfolding funas_trs_def using assms funas_trs_def by blast
  moreover have *:"(\<doteq>, 2) \<notin> funas_trs (set rl) \<and> (\<top>, 0) \<notin> funas_trs (set rl)"
    using D D_fresh calculation by auto
  let ?C = "convert_equations_into_term_multiset rl"
  have "\<forall>t \<in># ?C. \<exists>(u::('f, 'v)term) v::('f, 'v)term. t = Fun (\<doteq>) [u, v] \<and> (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v \<and>
     (\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v"
  proof
    fix t
    assume "t \<in># ?C"
    hence "t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset rl #}" 
      using False by (smt (verit, ccfv_threshold) convert_equations_into_term_multiset.simps(2) list.exhaust)
    then obtain u v where t:"t = Fun (\<doteq>) [u, v]" and uv:"(u, v) \<in># mset rl" by auto
    have "(\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v" using * uv lhs_wf rhs_wf by fastforce
    moreover have "(\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v" using * uv lhs_wf rhs_wf by fastforce
    ultimately show "\<exists> u v. t = Fun (\<doteq>) [u, v] \<and> (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v \<and>
       (\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v" using t by auto
  qed  
  then show ?thesis by (simp add: wf_equational_term_def wf_equational_term_mset_def) 
qed

definition "multiset_narrowing_reaches_to_success C \<longleftrightarrow>  (\<exists>\<sigma> S'. multiset_narrowing_derivation (convert_equations_into_term_multiset C) S' \<sigma> \<and> 
    (\<forall> s \<in># S'. s = Fun (\<top>) []))"

lemma subst_Fun_mset_equiv: fixes \<tau>::"('f, 'v)subst"
  shows "{#t \<cdot> \<tau>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset S#}#} = {#Fun \<doteq> [u \<cdot> \<tau>, v \<cdot> \<tau>]. (u, v) \<in># mset S#}"
proof(induct S)
  case Nil
  then show ?case by auto
next
  case (Cons p S)
  then show ?case by (auto split:prod.splits)
qed

lemma multiset_reduction_step_divide:
  assumes AB:"(A + B, T) \<in> (multiset_reduction_step)\<^sup>*"
    and T:"(\<forall>t \<in># T. t = Fun (\<top>) [])"
  shows "\<exists>T'. (A, T') \<in> (multiset_reduction_step)\<^sup>* \<and> T' \<subseteq># T" using assms 
proof -
  from AB T obtain n where nstep:"(A + B, T) \<in> (multiset_reduction_step)^^n" and 
    goal:"(\<forall>t \<in># T. t = Fun (\<top>) [])" by auto
  hence "\<exists>T'. (A, T') \<in> (multiset_reduction_step)\<^sup>* \<and> T' \<subseteq># T"
  proof(induct n arbitrary:A B)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain U where step:"(A + B, U) \<in> multiset_reduction_step" and UT:"(U, T) \<in> (multiset_reduction_step)^^n" 
      by (meson relpow_Suc_E2)
    from step obtain s p rl \<sigma> where sS:"s \<in># A + B" and U:"U = ((A + B - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#})"
      and rl:"rl \<in> R" and pfun:"p \<in> poss s" and sp:"(s |_ p = (fst rl) \<cdot> \<sigma>)" using mul_reduction_correspondence by blast
    from sS have "s \<in># A \<or> s \<in># B" by auto
    then show ?case
    proof
      assume sB:"s \<in># B"
      let ?B = "B - {#s#} + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}"
      from sB have U:"U = A + ?B" using U by auto
      then show ?thesis using Suc(1) UT goal by blast 
    next
      assume sA:"s \<in># A"
      let ?A = "A - {#s#} + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}"
      from sA have U:"U = ?A + B" using U by auto
      then show ?thesis using Suc(1) UT goal 
        by (smt (verit, del_insts) converse_rtrancl_into_rtrancl ctxt_supt_id multiset_reduction_stepI pfun prod.exhaust_sel rl rstepI sA sp)
    qed
  qed
  then show ?thesis by auto
qed

lemma multiset_reduction_step_pre_unifiability: fixes C::"(('f, 'v) term \<times> ('f, 'v) term) list"
  assumes funas_C:"funas_trs (set C) \<subseteq> F"
    and uv:"(u, v) \<in> set C"                                      
    and ersteps:"({#Fun \<doteq> [u, v]. (u, v) \<in># mset C#}, T) \<in> (multiset_reduction_step)\<^sup>+ \<and> (\<forall>t \<in># T. t = Fun (\<top>) [])"
  shows "({#Fun \<doteq> [u, v]#}, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)\<^sup>+"
proof -
  from uv have neq:"Fun \<doteq> [u, v] \<noteq> Fun (\<top>) []" by auto
  have funas_uv:"funas_rule (u, v) \<subseteq> F" using funas_C uv unfolding funas_defs by auto
    (meson funas_C lhs_wf subsetD, meson funas_C in_mono rhs_wf)
  let ?A = "{#Fun \<doteq> [u, v]#}"
  let ?C = "mset C - {#(u, v)#}"
  let ?B = "{#Fun \<doteq> [u, v]. (u, v) \<in># ?C#}"
  have "(?A + ?B, T) \<in> (multiset_reduction_step)\<^sup>+" using ersteps 
    by (auto, metis (no_types, lifting) case_prod_conv image_mset_add_mset in_multiset_in_set insert_DiffM uv)
  hence *:"(?A + ?B, T) \<in> (multiset_reduction_step)\<^sup>*" by auto
  have **:"(\<forall>t \<in># T. t = Fun (\<top>) [])" using ersteps ..
  from multiset_reduction_step_divide[OF * ** ]
  have ***:"\<exists>T'. (?A, T') \<in> (multiset_reduction_step)\<^sup>* \<and> T' \<subseteq># T" by auto
  then obtain T' where AT':"(?A, T') \<in> (multiset_reduction_step)\<^sup>* \<and> T' \<subseteq># T" using *** by auto
  from AT' obtain n where "(?A, T') \<in> (multiset_reduction_step)^^n" and T':"T' \<subseteq># T" by auto
  hence "T' = {#Fun (\<top>) []#}" using ** T' funas_uv
  proof(induct n arbitrary:u v T')
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain U where uvU:"({#Fun \<doteq> [u, v]#}, U) \<in> multiset_reduction_step"
      and UT':"(U, T') \<in> multiset_reduction_step ^^ n" by (meson relpow_Suc_E2)
    from uvU obtain  s p rl \<sigma> where s:"s = Fun \<doteq> [u, v]" and U:"U = {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}" and rl:"rl \<in> R" 
      and pfun:"p \<in> poss s" and sp:"s|_ p = (fst rl) \<cdot> \<sigma>"  by (smt (verit) add_mset_add_single add_mset_eq_single 
          insert_DiffM mul_reduction_correspondence multiset_reduction_step_posE)
    have wf_s:"wf_equational_term s" unfolding wf_equational_term_def funas_defs using funas_uv 
      by (metis Suc.prems(5) convert_equation_into_term_sound fst_conv s snd_conv wf_equational_term_def)
    have nu:"(\<doteq>, 2) \<notin> funas_term u" and nv:"(\<doteq>, 2) \<notin> funas_term v" using Suc(6) D D_fresh unfolding funas_defs 
      using subset_eq D D_fresh Suc.prems(5) funas_defs(2) by fastforce+
    have poss_us:"\<forall>q \<in> poss u. u |_ q = s |_ (0 # q)" using s by auto  
    have poss_vs:"\<forall>q' \<in> poss v. v |_ q' = s |_ (1 # q')" using s by auto
    let ?srule = "\<lambda>x. (Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
    have fr:"\<forall>x. funas_rule (?srule x) = {(\<doteq>, 2), (\<top>, 0)}" using D 
      unfolding funas_defs by (auto simp add: numeral_2_eq_2)
    have cd:"\<forall>x. funas_rule (?srule x) \<subseteq> D" using D 
      unfolding funas_defs by (auto simp add: numeral_2_eq_2)
    have rlR':"rl \<in> R' \<or> (\<exists>x. rl = ?srule x)" using R' rl by fastforce
    moreover have rlR'_un:"funas_rule rl \<subseteq> F \<or> (\<exists>x. rl = ?srule x)" 
      using R_sig by (metis funas_defs(2) le_supI lhs_wf prod.exhaust_sel rhs_wf rlR')
    ultimately have funas_rl:"funas_rule rl \<subseteq> F \<or> funas_rule rl = {(\<doteq>, 2), (\<top>, 0)}"
      using fr by metis
    then consider (ordinary) "funas_rule rl \<subseteq> F" | (special) "funas_rule rl = {(\<doteq>, 2), (\<top>, 0)}" by auto
    then show ?case
    proof(cases)
      case (special)
      have "funas_rule rl = {(\<doteq>, 2), (\<top>, 0)}"
      proof(rule ccontr)
        assume asm:"\<not> ?thesis"
        have "funas_rule rl = D" using special
          by (simp add: D)
        then show False using asm D by simp
      qed
      hence "(\<exists>x. rl = ?srule x)" using s sp rl funas_rl R' R_sig D D_fresh unfolding funas_defs 
        using rlR'_un special by force
      then obtain x where rlx:"rl = ?srule x" by auto
      with pfun have root_s:"root (s|_ p) = Some (\<doteq>, 2)" using sp funas_uv unfolding funas_defs by auto
      have ptop:"p = []"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "u \<unrhd> (s |_ p) \<or> v \<unrhd> (s |_ p)" using pfun s by auto
            (metis diff_Suc_1 less_Suc0 less_Suc_eq nth_Cons' subt_at_imp_supteq)
        then show False using root_s nu nv unfolding funas_defs
          by (meson root_symbol_in_funas subset_eq supteq_imp_funas_term_subset)
      qed
      hence *:"replace_at s p ((snd rl) \<cdot> \<sigma>) = Fun (\<top>) []" using s rlx by auto
      hence "U = {#Fun (\<top>) []#}" using U by fastforce
      then show ?thesis using not_reducible_T_erstep UT' by (metis relpow_E2)
    next
      case ordinary
      hence rlR':"rl \<in> R'" using R' D R_sig D_fresh 
        by (metis fr inf.orderE insert_not_empty rlR')
      from fun_root_not_None have nroot:"root (fst rl) \<noteq> None" 
        by (metis is_Fun_Fun_conv local.wf prod.collapse rl wf_trs_imp_lhs_Fun)
      from root_not_special_symbols[OF rlR' ordinary nroot]
      have *:"root (fst rl) \<noteq> Some (\<doteq>, 2) \<and> root (fst rl) \<noteq>  Some (\<top>, 0)" by simp
      hence root_eq:"root (s |_ p) = root(fst rl)" using s
        by (metis (no_types, opaque_lifting) R' empty_pos_in_poss le_sup_iff local.wf poss_is_Fun_fun_poss 
            prod.exhaust_sel rlR' root_subst_inv sp subset_iff subt_at.simps(1) term.disc(2) wf_trs_def)
      hence "root (s |_ p) \<noteq> Some (\<doteq>, 2) \<and> root (s |_ p) \<noteq> Some (\<top>, 0)" using * by force
      hence np:"p \<noteq> []" using wf_s[unfolded wf_equational_term_def] by force
      hence "\<exists>q r. (q \<in> poss u \<and> p = 0 # q) \<or> (r \<in> poss v \<and> p = 1 # r)" using s ordinary pfun 
      proof(auto, goal_cases)
        case (1 x p)
        then show ?case using less_2_cases numeral_2_eq_2 by fastforce
      next
        case (2 x p)
        then show ?case by (metis less_2_cases nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
      next
        case (3 x p)
        then show ?case by (metis  less_2_cases nth_Cons_0 numeral_2_eq_2)
      qed
      then obtain q r where qpos:"(q \<in> poss u \<and> p = 0 # q) \<or> (r \<in> poss v \<and> p = 1 # r)" (is "?A \<or> ?B") by auto
      then show ?thesis 
      proof
        assume asm:?A
        hence *:"replace_at s p ((snd rl) \<cdot> \<sigma>) = Fun \<doteq> [(replace_at u q ((snd rl) \<cdot> \<sigma>)), v]"  using s by auto
        hence "U = {#Fun \<doteq> [(replace_at u q ((snd rl) \<cdot> \<sigma>)), v]#}" using U by auto
        moreover have "funas_rule (replace_at u q ((snd rl) \<cdot> \<sigma>), v) \<subseteq> F" using funas_uv wf_F_subst ordinary unfolding funas_defs
          by auto (metis Suc.prems(5) asm ctxt_supt_id fst_conv funas_rule_def funas_term_ctxt_apply le_supE subsetD,
              metis Suc.prems(5) funas_rule_def le_sup_iff snd_conv subsetD)
        ultimately show ?thesis using ** Suc UT' by auto
      next
        assume asm:?B
        hence "replace_at s p ((snd rl) \<cdot> \<sigma>) = Fun \<doteq> [u , (replace_at v r ((snd rl) \<cdot> \<sigma>))]" using s by auto
         hence "U = {#Fun \<doteq> [u , (replace_at v r ((snd rl) \<cdot> \<sigma>))]#}" using U by auto
        moreover have "funas_rule (u , (replace_at v r ((snd rl) \<cdot> \<sigma>))) \<subseteq> F" using funas_uv wf_F_subst ordinary unfolding funas_defs
          by auto (metis Suc.prems(5) fst_conv funas_rule_def le_sup_iff subsetD,
           metis Suc.prems(5) asm ctxt_supt_id funas_rule_def funas_term_ctxt_apply le_supE snd_conv subsetD)
        ultimately show ?thesis using ** Suc.hyps Suc.prems(2) UT' by auto
      qed
    qed
  qed
  then show ?thesis using AT' by (meson neq add_mset_eq_single rtranclD)
qed

lemma multiset_reduction_single: assumes funas_uv:"funas_rule (u, v) \<subseteq> F"
    and ersteps:"({#Fun \<doteq> [u, v]#}, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)\<^sup>+"
  shows "((u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" 
proof -
  from ersteps obtain n where step:"({#Fun \<doteq> [u, v]#}, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)^^n" and n1:"n \<ge> 1" 
    by (metis add_mset_eq_single less_one list.simps(3) relpow_0_E rtrancl_imp_relpow term.inject(2) trancl_into_rtrancl verit_comp_simplify1(3))
  then show ?thesis using funas_uv
  proof(induct n arbitrary:u v)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    with step obtain U where uvU:"({#Fun \<doteq> [u, v]#}, U) \<in> (multiset_reduction_step)" and 
      UG:"(U, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)^^n" by (meson relpow_Suc_D2)
    from uvU obtain  s p rl \<sigma> where s:"s = Fun \<doteq> [u, v]" and U:"U = {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}" and rl:"rl \<in> R" 
      and pfun:"p \<in> poss s" and sp:"s|_ p = (fst rl) \<cdot> \<sigma>" 
      by (smt (verit) add_mset_add_single add_mset_eq_single insert_DiffM mul_reduction_correspondence multiset_reduction_step_posE)
    have wf_s:"wf_equational_term s" unfolding wf_equational_term_def funas_defs using funas_uv 
      by (metis Suc.prems(3) convert_equation_into_term_sound fst_conv s snd_conv wf_equational_term_def) 
    have nu:"(\<doteq>, 2) \<notin> funas_term u" and nv:"(\<doteq>, 2) \<notin> funas_term v" using Suc(4) D D_fresh unfolding funas_defs by auto 
    have poss_us:"\<forall>q \<in> poss u. u |_ q = s |_ (0 # q)" using s by auto  
    have poss_vs:"\<forall>q' \<in> poss v. v |_ q' = s |_ (1 # q')" using s by auto
    let ?srule = "\<lambda>x. (Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
    have fr:"\<forall>x. funas_rule (?srule x) = {(\<doteq>, 2), (\<top>, 0)}" using D 
      unfolding funas_defs by (auto simp add: numeral_2_eq_2)
    have cd:"\<forall>x. funas_rule (?srule x) \<subseteq> D" using D 
      unfolding funas_defs by (auto simp add: numeral_2_eq_2)
    have rlR':"rl \<in> R' \<or> (\<exists>x. rl = ?srule x)" using R' rl by fastforce
    moreover have rlR'_un:"funas_rule rl \<subseteq> F \<or> (\<exists>x. rl = ?srule x)" 
      using R_sig by (metis funas_defs(2) le_supI lhs_wf prod.exhaust_sel rhs_wf rlR')
    ultimately have funas_rl:"funas_rule rl \<subseteq> F \<or> funas_rule rl = {(\<doteq>, 2), (\<top>, 0)}"
      using fr by metis
    then consider (ordinary) "funas_rule rl \<subseteq> F" | (special) "funas_rule rl = {(\<doteq>, 2), (\<top>, 0)}" by auto
    then show ?case
    proof(cases)
      case (special)
      have "funas_rule rl = {(\<doteq>, 2), (\<top>, 0)}"
      proof(rule ccontr)
        assume asm:"\<not> ?thesis"
        have "funas_rule rl = D" using special
          by (simp add: D)
        then show False using asm D by simp
      qed
      hence "(\<exists>x. rl = ?srule x)" using s sp rl funas_rl R' R_sig D D_fresh unfolding funas_defs 
        using rlR'_un special by force
      then obtain x where rlx:"rl = ?srule x" by auto
      with pfun have root_s:"root (s|_ p) = Some (\<doteq>, 2)" using sp funas_uv unfolding funas_defs by auto
      have ptop:"p = []"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "u \<unrhd> (s |_ p) \<or> v \<unrhd> (s |_ p)" using pfun s by auto
            (metis diff_Suc_1 less_Suc0 less_Suc_eq nth_Cons' subt_at_imp_supteq)
        then show False using root_s nu nv unfolding funas_defs
          by (meson root_symbol_in_funas subset_eq supteq_imp_funas_term_subset)
      qed
      hence *:"replace_at s p ((snd rl) \<cdot> \<sigma>) = Fun (\<top>) []" using s rlx by auto
      hence "u = v" using s rlx sp by (simp add: ptop)
      then show ?thesis by auto
    next
      case ordinary
      hence rlR':"rl \<in> R'" using R' D R_sig D_fresh 
        by (metis fr inf.orderE insert_not_empty rlR')
      from fun_root_not_None have nroot:"root (fst rl) \<noteq> None" 
        by (metis is_Fun_Fun_conv local.wf prod.collapse rl wf_trs_imp_lhs_Fun)
      from root_not_special_symbols[OF rlR' ordinary nroot]
      have *:"root (fst rl) \<noteq> Some (\<doteq>, 2) \<and> root (fst rl) \<noteq>  Some (\<top>, 0)" by simp
      hence root_eq:"root (s |_ p) = root(fst rl)" using s
        by (metis (no_types, opaque_lifting) R' empty_pos_in_poss le_sup_iff local.wf poss_is_Fun_fun_poss 
            prod.exhaust_sel rlR' root_subst_inv sp subset_iff subt_at.simps(1) term.disc(2) wf_trs_def)
      hence "root (s |_ p) \<noteq> Some (\<doteq>, 2) \<and> root (s |_ p) \<noteq> Some (\<top>, 0)" using * by force
      hence np:"p \<noteq> []" using wf_s[unfolded wf_equational_term_def] by force
      hence "\<exists>q r. (q \<in> poss u \<and> p = 0 # q) \<or> (r \<in> poss v \<and> p = 1 # r)" using s ordinary pfun 
      proof(auto, goal_cases)
        case (1 x p)
        then show ?case using less_2_cases numeral_2_eq_2 by fastforce
      next
        case (2 x p)
        then show ?case by (metis less_2_cases nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
      next
        case (3 x p)
        then show ?case by (metis less_2_cases nth_Cons_0 numeral_2_eq_2)
      qed
      then obtain q r where qpos:"(q \<in> poss u \<and> p = 0 # q) \<or> (r \<in> poss v \<and> p = 1 # r)" (is "?A \<or> ?B") by auto
      then show ?thesis
      proof
        assume asm:?A
        hence *:"replace_at s p ((snd rl) \<cdot> \<sigma>) = Fun \<doteq> [(replace_at u q ((snd rl) \<cdot> \<sigma>)), v]"  using s by auto
        hence "U = {#Fun \<doteq> [(replace_at u q ((snd rl) \<cdot> \<sigma>)), v]#}" using U by auto
        moreover have "funas_rule (replace_at u q ((snd rl) \<cdot> \<sigma>), v) \<subseteq> F" using funas_uv wf_F_subst ordinary unfolding funas_defs
          by auto (metis Suc.prems(3) asm ctxt_supt_id fst_conv funas_rule_def funas_term_ctxt_apply le_sup_iff subsetD,
              metis Suc.prems(3) UnI2 funas_rule_def in_mono snd_eqD)
        moreover have "(replace_at u q ((snd rl) \<cdot> \<sigma>), v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using Suc(1) UG 
          by (metis One_nat_def Suc.prems(2) calculation(1) calculation(2) le_SucE list.simps(3) 
              nat.inject relpow_0_E single_eq_single term.inject(2))
        ultimately show ?thesis 
          by (metis (no_types, lifting) asm conversionI' conversion_rtrancl ctxt_supt_id poss_us 
              prod.collapse r_into_rtrancl rl rstepI rtrancl.rtrancl_into_rtrancl sp)
      next
        assume asm:?B
        hence "replace_at s p ((snd rl) \<cdot> \<sigma>) = Fun \<doteq> [u , (replace_at v r ((snd rl) \<cdot> \<sigma>))]" using s by auto
         hence "U = {#Fun \<doteq> [u , (replace_at v r ((snd rl) \<cdot> \<sigma>))]#}" using U by auto
        moreover have "funas_rule (u , (replace_at v r ((snd rl) \<cdot> \<sigma>))) \<subseteq> F" using funas_uv wf_F_subst ordinary unfolding funas_defs
          by auto (metis Suc.prems(3) UnI1 fst_eqD funas_rule_def in_mono, metis Suc.prems(3) asm ctxt_supt_id 
              funas_rule_def funas_term_ctxt_apply le_sup_iff snd_conv subsetD)
        moreover have "(u , (replace_at v r ((snd rl) \<cdot> \<sigma>))) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using Suc(1) UG 
          by (metis One_nat_def Suc.prems(2) calculation(1) calculation(2) le_SucE list.simps(3) 
              nat.inject relpow_0_E single_eq_single term.inject(2))
        ultimately show ?thesis 
          by (smt (verit, ccfv_SIG) asm conversionI' conversion_ctxt_closed conversion_inv conversion_rtrancl 
              conversion_subst_closed ctxt_supt_id poss_vs prod.exhaust_sel r_into_rtrancl rl 
              rtrancl.rtrancl_into_rtrancl sp subsetD subset_rstep)
      qed
    qed
  qed
qed

lemma multiset_reduction_step_unifiability: 
  assumes funas_C:"funas_trs (set C) \<subseteq> F"
    and ersteps:"({#Fun \<doteq> [u, v]. (u, v) \<in># mset C#}, T) \<in> (multiset_reduction_step)\<^sup>+ \<and> (\<forall>t \<in># T. t = Fun (\<top>) [])"
  shows "\<forall>u v. (u, v) \<in> set C \<longrightarrow> ((u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)"
proof -
  { fix u v
    assume asm:"(u, v) \<in> set C"
    with ersteps have *:"({#Fun \<doteq> [u, v]#}, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)\<^sup>+"
      using multiset_reduction_step_pre_unifiability funas_C by auto
    have "funas_rule (u, v) \<subseteq> F" unfolding funas_defs using asm funas_C by auto (meson in_mono lhs_wf, 
          meson rhs_wf subsetD)
    hence "((u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" using multiset_reduction_single * by auto
  } then show ?thesis by auto
qed

(* A sufficient condition of satisfying the R-unification problem *)
lemma multiset_narrowing_based_R_unifiable: assumes funas_C:"funas_trs (set C) \<subseteq> F"
  and not_empty:"set C \<noteq> {}"
  and nd:"(\<exists>\<sigma> S'. multiset_narrowing_derivation (convert_equations_into_term_multiset C) S' \<sigma> \<and> (\<forall> s \<in># S'. s = Fun (\<top>) []))"
shows "R_unifiable C" 
proof -
  let ?C = "convert_equations_into_term_multiset C"
  from assms obtain \<sigma> S' where nd:"multiset_narrowing_derivation ?C S' \<sigma>" and goal:"(\<forall> s \<in># S'. s = Fun (\<top>) [])" by auto
  have neq:"\<forall>u v \<sigma>. Fun (\<top>) [] \<noteq> Fun (\<doteq>) [u \<cdot> \<sigma>, v \<cdot> \<sigma>]" by auto 
  from multiset_narrowing_reduction[OF nd]
  have estep:"(subst_term_multiset \<sigma> ?C, S') \<in> (multiset_reduction_step)\<^sup>*" by auto
  moreover have estep_trans:"(subst_term_multiset \<sigma> ?C, S') \<in> (multiset_reduction_step)\<^sup>+"
  proof -
    have "(subst_term_multiset \<sigma> ?C, S') \<notin> (multiset_reduction_step)^^0"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence "(subst_term_multiset \<sigma> ?C, S') \<in> (multiset_reduction_step)^^0" by auto
      hence eq:"subst_term_multiset \<sigma> ?C =  S'" by auto
      have *:"(\<top>, 0) \<notin> funas_trs (set C)" using funas_C D D_fresh by auto
      have Cq:"?C = {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset C #}" 
        by (metis (no_types, lifting) convert_equations_into_term_multiset.elims image_mset_is_empty_iff mset.simps(1))
      hence **:"subst_term_multiset \<sigma> ?C = {# Fun (\<doteq>) [u \<cdot> \<sigma>, v \<cdot> \<sigma>]. (u, v) \<in># mset C #}" unfolding subst_term_multiset_def
        using subst_Fun_mset_equiv by auto
      hence root1:"\<forall>s \<in># subst_term_multiset \<sigma> ?C. (\<doteq>, 2) \<in> funas_term s" using eq goal by fastforce 
      moreover have root2:"\<forall> s \<in># S'. funas_term s = {(\<top>, 0)}" using goal  ** eq by auto
      moreover have "subst_term_multiset \<sigma> ?C \<noteq> {#}" using funas_C not_empty  unfolding funas_defs subst_term_multiset_def  
        by (simp add: Cq)
      moreover have "S' \<noteq> {#}" using goal calculation(3) eq by auto
      ultimately show False using eq by auto
    qed
    then show ?thesis by (metis estep relpow_0_I rtranclD)
  qed
  moreover have subC:"subst_term_multiset \<sigma> ?C = {#Fun \<doteq> [u \<cdot> \<sigma>, v \<cdot> \<sigma>]. (u, v) \<in># mset C#}" unfolding subst_term_multiset_def 
    by (metis (no_types, lifting) convert_equations_into_term_multiset.elims image_mset_is_empty_iff mset_zero_iff subst_Fun_mset_equiv)
  moreover have subC2:"... = {#Fun \<doteq> [u , v]. (u, v) \<in># mset (subst_equations_list \<sigma> C)#}" unfolding subst_equations_list_def subst_equation_def 
      subst_term_multiset_def by (auto, smt (verit, ccfv_SIG) fstI multiset.map_comp multiset.map_cong0 o_apply sndI split_beta)
  ultimately have *:"({#Fun \<doteq> [u , v]. (u, v) \<in># mset (subst_equations_list \<sigma> C)#}, S') \<in> (multiset_reduction_step)\<^sup>*" by auto
  have **:"funas_trs (set (subst_equations_list \<sigma> C)) \<subseteq> F" unfolding funas_defs subst_equations_list_def subst_equation_def
    using wf_F_subst by auto (meson funas_C in_mono lhs_wf, meson funas_C rhs_wf subsetD)
  from multiset_reduction_step_unifiability[of "subst_equations_list \<sigma> C" S']
  have "\<forall>u v. (u, v) \<in> set (subst_equations_list \<sigma> C) \<longrightarrow> ((u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" using funas_C * ** goal 
    estep_trans subC subC2 by auto
  then show ?thesis unfolding R_unifiable_def subst_equations_list_def subst_equation_def 
    by (auto, smt (verit, ccfv_threshold) fst_conv image_eqI snd_conv)
qed

(* The following lemma shows the soundness of multiset narrowing *)
lemma lifting_lemma_for_multiset_narrowing:
  fixes V::"('v::infinite) set" and S::"('f, 'v)term multiset" and T::"('f, 'v)term multiset"
  assumes "normal_subst R \<theta>"
    and "T = subst_term_multiset \<theta> S"
    and "vars_term_set (set_mset S) \<union> subst_domain \<theta> \<subseteq> V"
    and mrsteps:"(T,  T') \<in> (multiset_reduction_step)\<^sup>*"
    and fv:"finite V"
  shows "\<exists>\<sigma> \<theta>' S'. multiset_narrowing_derivation S S' \<sigma> \<and> T' = subst_term_multiset \<theta>' S' \<and>
      normal_subst R \<theta>' \<and> (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V"
proof -
  from mrsteps obtain f n where f0:"f 0 = T" and fn:"f n = T'" and rel_chain:"\<forall>i < n. (f i,  f (Suc i)) \<in> multiset_reduction_step" 
    by (metis rtrancl_imp_seq)
  hence "\<exists>\<sigma> \<theta>' S'. multiset_narrowing_derivation_num S S' \<sigma> n \<and> subst_term_multiset \<theta>' S' = T' \<and> normal_subst R \<theta>' \<and>
    (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V" using assms
  proof(induct n arbitrary: S T T' \<theta> f V rule: wf_induct[OF wf_measure [of "\<lambda> n. n"]])
    case (1 n)
    note IH1 = 1(1)[rule_format]
    then show ?case
    proof(cases "n = 0")
      case True
      show ?thesis by (rule exI[of _ Var], rule exI[of _ \<theta>], rule exI[of _ S], 
            simp add:multiset_narrowing_derivation_num_def, insert True 1, auto)
    next
      case False
      hence f0f1:"(f 0, f 1) \<in> multiset_reduction_step" using 1 by auto
      then show ?thesis
      proof -
        from f0f1 obtain T T1 s \<sigma> rl p  where f0:"f 0 = T" and f1:"f 1 = T1" and s:"s \<in># T" and 
          T':"T1 = ((T - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#})" and rl:"rl \<in> R" and 
          red_pos:"p \<in> poss s" and s1p:"s |_ p = (fst rl) \<cdot> \<sigma>"
            by (meson mul_reduction_correspondence multiset_reduction_step_posE)
        have norm\<theta>:"normal_subst R \<theta>" by fact
        hence Ts:"T = subst_term_multiset \<theta> S" using f0 1 by auto
        have "\<exists>\<omega>. V \<inter> vars_rule (\<omega> \<bullet> rl) = {}" using 1(9) 
          by (metis rule_fs.rename_avoiding supp_vars_rule_eq vars_rule_def)
        then obtain \<omega> where varempty':"V \<inter> vars_rule (\<omega> \<bullet> rl) = {}" by auto
        hence "\<exists>\<omega>r. \<omega>r \<bullet> \<omega> \<bullet> rl \<in> R" using rl
          by (metis (no_types, opaque_lifting) rule_pt.permute_minus_cancel(2) rule_pt.permute_plus)
        then obtain \<omega>r where \<omega>r:"\<omega>r \<bullet> (\<omega> \<bullet> rl) \<in> R" by auto
        from red_pos have pfs1:"p \<in> poss s" by blast
        have ps1:"p \<in> poss s" using fun_poss_imp_poss pfs1 by blast
        hence nt:"((fst rl) \<cdot> \<sigma>) \<notin> NF (rstep R)"
        proof - 
          have *:"is_Fun (fst rl)" using wf[unfolded wf_trs_def] using rl 
            by (metis is_Fun_Fun_conv prod.collapse)
          let ?C = "Hole::('f, 'v)ctxt"
          from  rl * have "(fst rl \<cdot> \<sigma>, snd rl \<cdot> \<sigma>) \<in> rstep R" 
            by (metis prod.collapse rstep_rule rstep_subst)
          then show ?thesis by auto
        qed
        obtain u where uS':"u \<in># S" and us1:"u \<cdot> \<theta> = s" using Ts s unfolding subst_term_multiset_def by auto
        have sub_eq:"(u \<cdot> \<theta>) |_ p = (fst rl) \<cdot> \<sigma>" using us1 s1p by auto
        have pu:"p \<in> fun_poss (u \<cdot> \<theta>)" using pfs1 us1
          by (metis NF_I is_VarE local.wf nt poss_is_Fun_fun_poss rstep_imp_Fun sub_eq term.distinct(1))
        have p:"p \<in> poss u" 
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence pnu:"p \<notin> poss u" by simp
          hence pnfu:"p \<notin> fun_poss u" using fun_poss_imp_poss by blast
          from poss_subst_apply_term[of p u \<theta>]
          obtain q r x where qpr:"p = q @ r" and qu:"q \<in> poss u" and uqx:"u |_ q = Var x" and r:"r \<in> poss (\<theta> x)"
            using pnfu ps1 us1 by blast
          hence *:"(u \<cdot> \<theta>) |_ p = (Var x) \<cdot> \<theta> |_ r" by force
          have "((Var x) \<cdot> \<theta>) \<in> NF (rstep R)" using norm\<theta> 
            by (simp add: normal_subst_def, metis NF_I local.wf no_Var_rstep notin_subst_domain_imp_Var)
          hence "((Var x) \<cdot> \<theta> |_ r) \<in> NF (rstep R)"  
            by (auto simp add: normal_subst_def, insert r, goal_cases) 
              (meson NF_rstep_subterm subt_at_imp_supteq')
          then show False using nt * using s1p us1 by auto
        qed
        hence pfun:"p \<in> fun_poss u"  using ps1 us1 red_pos nt norm\<theta> unfolding normal_subst_def
          by (metis pu eval_term.simps(1) fun_poss_fun_conv is_VarE notin_subst_domain_imp_Var poss_is_Fun_fun_poss sub_eq subt_at_subst term.distinct(1))
        hence vuS':"vars_term (u |_ p) \<subseteq> vars_term_set (set_mset S)" 
        proof -
          have "vars_term (u |_ p) \<subseteq> vars_term u" using p 
            by (simp add: vars_term_subt_at)
          then show ?thesis using uS' vars_term_set_def by fastforce
        qed
        with varempty' have varcond:"vars_term (u |_ p) \<inter> vars_rule (\<omega> \<bullet> rl) = {}" using 1(7) by auto
        from vuS' have vuV:"vars_term (u |_ p) \<subseteq> V" using 1(7) by auto
        have "\<exists>\<sigma>r. \<forall>t. \<sigma>r (\<omega> \<bullet> t) = \<sigma> t" using atom_pt.permute_minus_cancel(2) by (metis o_apply)
        then obtain \<sigma>r where \<sigma>rdef:"\<forall>t. \<sigma>r (\<omega> \<bullet> t) = \<sigma> t" by auto
        hence "\<sigma>r = (\<lambda>x. \<sigma> (- \<omega> \<bullet> x))" by (metis atom_pt.permute_minus_cancel(1))
        hence \<sigma>r:"\<sigma>r = (\<lambda>x. (sop (- \<omega>) \<circ>\<^sub>s \<sigma>) x)" 
          by (metis comp_apply permute_atom_def subst_compose_o_assoc subst_monoid_mult.mult.left_neutral)
        hence "\<forall>S. subst_term_set \<sigma> S = subst_term_set \<sigma>r (\<omega> \<bullet> S)" unfolding subst_term_set_def 
        proof(auto, goal_cases)
          case (1 S t)
          then show ?case 
            by (metis term_pt.permute_flip term_set_pt.mem_permute_iff)
        next
          case (2 S xa)
          then show ?case by force
        qed
        hence pc:"fst rl \<cdot> \<sigma> = fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          by (simp add: \<sigma>r rule_pt.fst_eqvt)
        have pc':"snd rl \<cdot> \<sigma> = snd (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          by (simp add: \<sigma>r rule_pt.snd_eqvt rule_pt.fst_eqvt)
        let ?\<sigma>r = "\<sigma>r |s vars_rule (\<omega> \<bullet> rl)"
        let ?\<sigma>dom = "vars_rule (\<omega> \<bullet> rl)"
        have sub_\<sigma>r:"subst_domain ?\<sigma>r \<subseteq> (vars_rule (\<omega> \<bullet> rl))" 
          using subst_domain_restrict_subst_domain by fastforce 
        let ?\<theta> = "\<theta> |s V"
        have sub_\<theta>:"subst_domain ?\<theta> \<subseteq> V" using subst_domain_restrict_subst_domain by fastforce
        have inter_empty:"subst_domain ?\<sigma>r \<inter> subst_domain ?\<theta> = {}" using varempty' 1(7) sub_\<sigma>r by auto
        have crl:"(snd (\<omega> \<bullet> rl)) \<cdot> \<sigma>r = ((snd rl) \<cdot> \<sigma>)" 
          by (simp add: \<sigma>r rule_pt.fst_eqvt rule_pt.snd_eqvt)
        note subst_rest_domain1 = subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
        have subinter:"subst_domain ?\<sigma>r = subst_domain \<sigma>r \<inter> ?\<sigma>dom" using subst_rest_domain1 by auto
        from us1 s1p have *:"(u \<cdot> \<theta> |_ p) = fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r"
          by (simp add: pc subst_apply_term_restrict_subst_domain) 
        have varcond':"vars_term (u |_ p) \<inter> vars_term (fst (\<omega> \<bullet> rl)) = {}" 
        proof -
          have "vars_term (fst (\<omega> \<bullet> rl)) \<subseteq> vars_rule (\<omega> \<bullet> rl)"
            by (metis (mono_tags, opaque_lifting) dual_order.refl le_sup_iff vars_rule_def vars_defs(2))
          then show ?thesis using varcond by auto
        qed
        with norm\<theta> * have u_p:"(u |_ p) \<cdot> \<theta> = fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          using p by simp
        have sub_eq:"(u |_ p) \<cdot> ?\<theta> = fst (\<omega> \<bullet> rl) \<cdot> ?\<sigma>r" using u_p 
          by (metis (no_types, lifting) 1(7) Un_upper1 coincidence_lemma' le_supE subst_domain_neutral vars_rule_def vars_defs(2))
        from subst_union_sound[OF sub_eq]
        have subst_eq_\<theta>\<sigma>:"(u |_ p) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)  = (fst (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using sub_\<sigma>r sub_\<theta> inter_empty
          by (smt (verit, ccfv_threshold) Int_assoc inf.orderE inf_bot_right inf_commute local.wf rl rule_pt.fst_eqvt sub_comm sub_eq subst_union_term_reduction varcond varempty' vars_rule_eqvt vars_rule_lhs vars_term_eqvt)
        then obtain \<delta> where mgu_uv:"mgu (u |_ p) (fst (\<omega> \<bullet> rl)) = Some \<delta>" using mgu_ex 
          by (meson ex_mgu_if_subst_apply_term_eq_subst_apply_term)
        hence up\<omega>rl:"(u |_ p) \<cdot> \<delta> =  fst (\<omega> \<bullet> rl) \<cdot> \<delta>" using subst_apply_term_eq_subst_apply_term_if_mgu by blast
        from mgu_sound[OF mgu_uv] have \<delta>:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) =  \<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using subst_eq_\<theta>\<sigma> 
          by (smt (verit, ccfv_SIG) is_imgu_def subst_monoid_mult.mult_assoc the_mgu the_mgu_is_imgu)
        have subst_domain\<delta>:"subst_domain \<delta> \<subseteq> vars_term (u |_ p) \<union> vars_term (fst (\<omega> \<bullet> rl))" 
          using mgu_subst_domain mgu_uv by blast
        have subst_range_disj\<delta>:"subst_domain \<delta> \<inter> range_vars \<delta> = {}" using mgu_uv mgu_subst_domain_range_vars_disjoint by blast
        let ?S = "subst_term_multiset \<delta> ((S - {#u#}) + {#replace_at u p (snd (\<omega> \<bullet> rl))#})"
        have url:"vars_term u \<inter> vars_rule (\<omega> \<bullet> rl) = {}" using vuV varempty' vuS' 1(7) 
          by (auto, metis Int_iff UN_I equals0D in_mono uS' vars_term_set_def)
        have nar:"(S, ?S, \<delta>) \<in>  multiset_narrowing_step_pos"
          using \<omega>r url mgu_uv pfun uS' by blast
        hence  nar:"(S, ?S, \<delta>) \<in>  multiset_narrowing_step"
          by (smt (verit, ccfv_threshold) \<omega>r url add_mset_add_single 
              image_mset_add_mset mgu_uv multiset_narrowing.multiset_narrowing_step.simps multiset_narrowing_axioms 
              narrowing_stepI pfun subst_term_multiset_def uS')
        from multiset_narrowing_set_imp_rtran[OF nar]
        have condn1:"multiset_narrowing_derivation_num S ?S \<delta> 1" by auto
        let ?V = "(V - subst_domain \<delta>) \<union> range_vars \<delta>"
        let ?\<theta>1 = "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s ?V"
        have sub\<theta>1:"subst_domain ?\<theta>1 \<subseteq> ?V" 
          by (metis inf_le1 restrict_subst subst_domain_restrict_subst_domain)
        have reseq:"?\<theta>1 |s ?V = (?\<theta> \<union>\<^sub>s ?\<sigma>r) |s  ?V" 
          by (simp add: restrict_subst_domain_def)
        have reseq\<delta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1) |s V  = (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) |s V " 
          using reseq r_subst_compose by blast
        have reseq\<theta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1)|s V = \<theta> |s V" using  \<delta> 1(7) by auto (smt (verit) \<delta> disjoint_iff notin_subst_domain_imp_Var 
              reseq\<delta> sub_\<sigma>r subset_iff subst_domain_neutral subst_ext subst_union.elims varempty')
        have "normal_subst R (?\<theta>1 |s ?V)"
        proof -
          let ?\<delta> = "\<delta> |s V"
          let ?B = "(V - subst_domain \<delta>) \<union> range_vars ?\<delta>"
          have normV:"normal_subst R (\<theta> |s V)" using norm\<theta> 1(7) by auto
          have BV:"?B \<subseteq> V - subst_domain \<delta> \<union> range_vars (\<delta> |s V)" by auto
          from restricted_normalized[OF normV reseq\<theta> BV]
          have normB:"normal_subst R (?\<theta>1 |s ?B)" by auto 
          have ranB:"range_vars \<delta> \<subseteq> ?B"
          proof
            fix x
            assume asm:"x \<in> range_vars \<delta>"
            hence xn\<delta>:"x \<notin> subst_domain \<delta>" using \<delta>
              by (meson disjoint_iff mgu_subst_domain_range_vars_disjoint mgu_uv)
            have subst_x:"x \<in> vars_term (u |_ p) \<union> vars_term (fst (\<omega> \<bullet> rl))" using mgu_uv 
                asm mgu_range_vars by auto
            then show "x \<in> ?B"
            proof
              assume "x \<in> vars_term (u |_ p)"
              hence "x \<in> V - subst_domain \<delta>" using 1(7) xn\<delta> vuS' by auto
              then show ?thesis by auto
            next
              assume asm2:"x \<in> vars_term (fst (\<omega> \<bullet> rl))"
              hence xnu:"x \<notin> vars_term (u |_ p)" using varcond' by blast
              from vars_term_range[OF asm asm2 subst_range_disj\<delta>]
              have xv\<delta>:"x \<in> vars_term (fst (\<omega> \<bullet> rl) \<cdot> \<delta>)" by auto
              have *:"x \<in> vars_term (u |_ p \<cdot> \<delta>)" using mgu_uv xv\<delta>
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu) 
              hence "vars_term (fst (\<omega> \<bullet> rl) \<cdot> \<delta>) = vars_term (u |_ p \<cdot> \<delta>)" using mgu_uv 
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu)
              from subst_restricted_range_vars[OF * subst_range_disj\<delta> xnu asm]
              have "x \<in> range_vars (\<delta> |s vars_term (u |_ p))" by auto
              moreover have upV:"vars_term (u |_ p) \<subseteq> V" using 1(7) vuS' by auto
              ultimately have "x \<in> range_vars (\<delta> |s V)" unfolding range_vars_def subst_restrict_def
                by (auto simp add: subsetD subst_domain_def) 
              then show ?thesis by auto
            qed
          qed
          hence "?B = ?V"
          proof -
            have "range_vars ?\<delta> \<subseteq> range_vars \<delta>"  unfolding subst_restrict_def range_vars_def  
              by (auto, smt (verit) mem_Collect_eq subst_domain_def, simp add: subst_domain_def)
            then show ?thesis using ranB by blast
          qed
          then show ?thesis using normB by auto
        qed
        hence norm\<theta>1:"normal_subst R ?\<theta>1" using sub\<theta>1 reseq by fastforce
        have rel_chain':"\<And>i. i < n - 1 \<Longrightarrow> (f (i + 1), f (Suc i + 1)) \<in> multiset_reduction_step" using rel_chain 
          by (simp add: 1(4))
        let ?f = "\<lambda>i. f (i + 1)"
        have relstar:"(f 1, f n) \<in> (multiset_reduction_step)\<^sup>*" using False 1(4) less_Suc_eq 
          by (induct n, blast, metis (no_types, lifting) One_nat_def rtrancl.simps)
        have vars\<theta>:"vars_term_set (set_mset S) \<union> subst_domain \<theta> \<subseteq> V" by fact
        have scomp:"?S = subst_term_multiset \<delta> (S - {#u#}) + subst_term_multiset \<delta> {#replace_at u p (snd (\<omega> \<bullet> rl))#}" (is "?S = ?fst + ?snd")
          unfolding subst_term_multiset_def by auto
        have "subst_term_multiset \<delta> {#replace_at u p (snd (\<omega> \<bullet> rl))#} \<subseteq># ?S"
          by (simp add: subst_term_multiset_def)
        hence vars_subS:"vars_term_set (set_mset (subst_term_multiset \<delta> {#replace_at u p (snd (\<omega> \<bullet> rl))#})) \<subseteq> ?V"  
        proof -
          have "vars_term (snd rl) \<subseteq> vars_term (fst rl)" using wf[unfolded wf_trs_def] rl by auto
          hence *:"vars_term (snd (\<omega> \<bullet> rl)) \<subseteq> vars_term (fst (\<omega> \<bullet> rl))" using rl by auto
              (metis UnCI rule_pt.fst_eqvt rule_pt.fst_eqvt sup.absorb_iff1 vars_defs(2) vars_rule_eqvt vars_term_eqvt)
          from var_cond_stable[OF this]
          have "vars_term (snd (\<omega> \<bullet> rl) \<cdot> \<delta> ) \<subseteq> vars_term (snd (\<omega> \<bullet> rl) \<cdot> \<delta>)" by fastforce
          from replace_var_stable[OF this] 
          have "vars_term(replace_at u p (snd (\<omega> \<bullet> rl)) \<cdot> \<delta>) \<subseteq> vars_term (replace_at u p (fst (\<omega> \<bullet> rl)) \<cdot> \<delta>)" 
            by (meson "*" replace_var_stable var_cond_stable)
          moreover have "vars_term (replace_at u p (fst (\<omega> \<bullet> rl)) \<cdot> \<delta>) = vars_term (u \<cdot> \<delta>)" using up\<omega>rl
            by (metis ctxt_supt_id p subst_apply_term_ctxt_apply_distrib)
          moreover have "vars_term (u \<cdot> \<delta>) \<subseteq> ?V" using uS' 1(7)  vars_term_set_def vars_term_subst_apply_term_subset
            by auto (fastforce, meson Diff_iff UnE subsetD vars_term_subst_apply_term_subset)
          ultimately show ?thesis unfolding vars_term_set_def subst_term_multiset_def by auto
        qed    
        have "subst_term_multiset \<delta> (S - {#u#}) \<subseteq># ?S" by (simp add: subst_term_multiset_def)
        hence vars_subSu:"vars_term_set (set_mset (subst_term_multiset \<delta> (S - {#u#}))) \<subseteq> ?V" 
        proof -
          have "vars_term_set (set_mset S) \<subseteq> V" using vars\<theta> by auto
          hence "vars_term_set (set_mset (subst_term_multiset \<delta> S)) \<subseteq> ?V" unfolding vars_term_set_def
              subst_term_multiset_def set_mset_def using vars_term_subst_apply_term_subset by fastforce+
          then show ?thesis by (smt (verit, del_insts) SUP_le_iff add_mset_add_single insert_DiffM 
                subst_term_multiset_union uS' union_iff vars_term_set_def)
        qed
        have varSV:"vars_term_set (set_mset ?S) \<subseteq> ?V"
        proof -
          have *:"vars_term_set (set_mset ?S) = vars_term_set (set_mset ?fst) \<union> vars_term_set (set_mset ?snd)"
            using scomp unfolding vars_term_set_def by auto
          then show ?thesis using vars_subS vars_subSu by auto
        qed
        from subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
        have subinter:"subst_domain ?\<sigma>r = subst_domain \<sigma>r \<inter> ?\<sigma>dom" by auto
        have inempty:"subst_domain ?\<sigma>r \<inter> V = {}" using varempty' subinter by auto
        hence \<theta>sv:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s V = \<theta> |s V"
          using \<delta> reseq\<delta> reseq\<theta> by auto
        have \<theta>varr:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s (vars_term (\<omega> \<bullet> snd rl)) = ?\<sigma>r |s (vars_term (\<omega> \<bullet> snd rl))" 
        proof -
          { fix v :: 'v
            have "vars_rule (\<omega> \<bullet> (fst rl, snd rl)) - V = vars_rule (\<omega> \<bullet> (fst rl, snd rl))" using varempty' unfolding funas_defs 
              by (auto simp add: rule_pt.fst_eqvt disjoint_iff vars_rule_def)
            then have "V \<inter> vars_term (\<omega> \<bullet> snd rl) = {}"
              by (metis Un_Int_eq(4) inf_bot_right inf_left_commute rule_pt.snd_eqvt varempty' vars_rule_def)
            then have "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s (vars_term (\<omega> \<bullet> snd rl)) = ?\<sigma>r |s (vars_term (\<omega> \<bullet> snd rl))"
              by (smt (verit, best) Int_iff disjoint_iff inf.absorb_iff2 sub_\<theta> subst_ext subst_union.simps)
          } then show ?thesis by fastforce
        qed
        have subeq:"subst_rule \<sigma>r (\<omega> \<bullet> (fst rl, snd rl)) = subst_rule \<sigma> (fst rl, snd rl)" 
          unfolding subst_rule_def subst_list_def using pc' pc rule_pt.fst_eqvt by simp
        have sub_eq1:"subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) = f 0 - {#s#}"
        proof -  
          have "vars_term_set (set_mset (subst_term_multiset \<delta> (S - {#u#}))) \<subseteq> ?V" using vars_subSu by auto
          hence subm_eq:"subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) = subst_term_multiset (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) (S - {#u#})" using reseq\<delta> 
            by (metis (no_types, opaque_lifting) restrict_subst subst_term_multiset_compose subst_term_multiset_rest_domain)
          hence "... = subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (S - {#u#})" using \<delta> by auto
          have *:"subst_domain ?\<theta> \<subseteq> V" by fact
          have **:"subst_domain ?\<sigma>r \<inter> vars_term_set (set_mset (S - {#u#})) = {}" unfolding vars_term_set_def set_mset_def           
            by (smt (verit, ccfv_threshold) "1.prems"(6) SUP_le_iff count_greater_zero_iff disjoint_iff 
                in_diffD inempty le_supE mem_Collect_eq subsetD vars_term_set_def)
          from subst_union_term_multiset_reduction[of ?\<theta> ?\<sigma>r S]
          have ***:"subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) S = f 0" 
            by (metis Ts \<theta>sv f0 le_supE restrict_subst subst_term_multiset_rest_domain vars\<theta>)
          from subst_union_term_multiset_reduction[OF inter_empty **]
          have "subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (S - {#u#}) = subst_term_multiset ?\<theta> (S - {#u#})" by (metis inter_empty sub_comm)
          also have "... = subst_term_multiset ?\<theta> S - subst_term_multiset ?\<theta> {#u#}" 
            by (simp add: image_mset_Diff subst_term_multiset_def uS')
          also have "... = subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) S - subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) {#u#}"
            by (metis calculation image_mset_Diff mset_subset_eq_single subst_term_multiset_def uS')
          also have "... = f 0 - subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) {#u#}" using *** by auto
          also have "... = f 0 - {#s#}" unfolding subst_term_multiset_def
            by (metis (no_types, lifting) 1(7) SUP_le_iff \<theta>sv coincidence_lemma' 
                image_mset_add_mset image_mset_empty le_supE uS' us1 vars_term_set_def)
          finally show ?thesis using \<delta> subm_eq by auto
        qed
        have sub_eq2:"{#replace_at s p ((snd rl) \<cdot> \<sigma>)#} = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) {#replace_at u p (snd (\<omega> \<bullet> rl))#}" 
        proof -
          have "(snd rl) \<cdot> \<sigma> = snd (\<omega> \<bullet> rl) \<cdot> \<sigma>r" using subeq by (simp add: pc')
          have "{#replace_at s p ((snd rl) \<cdot> \<sigma>)#} = {#replace_at s p ((snd (\<omega> \<bullet> rl)) \<cdot> \<sigma>r)#}" using \<sigma>rdef pc  pc' by auto 
          also have "... = {#replace_at (u \<cdot> \<theta>) p ((snd (\<omega> \<bullet> rl)) \<cdot> \<sigma>r)#}" using us1 by auto
          also have "... = {#replace_at (u \<cdot> \<theta>) p ((snd (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r))#}" using \<theta>sv \<theta>varr vuV vars\<theta> uS'  in_subst_restrict 
            by (simp add: vars_defs(2), smt (verit, ccfv_SIG) Un_Int_eq(2) eval_same_vars in_mono in_subst_restrict rule_pt.snd_eqvt) 
          also have "... = {#replace_at (u \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)) p ((snd (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r))#}" using \<theta>sv \<theta>varr vuV vars\<theta> uS' 
            by (smt (verit, best) Int_absorb1 UN_I Un_upper1 rule_pt.fst_eqvt in_subst_restrict 
                le_supE rule_pt.snd_eqvt subsetD term_subst_eq_conv uS' vars\<theta> vars_rule_def vars_defs(2) vars_term_set_def)
          also have "... = {#replace_at u p (snd (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)#}" by (simp add: ctxt_of_pos_term_subst p)
          also have "... = {#replace_at u p (snd (\<omega> \<bullet> rl)) \<cdot> (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r))#}" using \<delta> by auto
          also have "... = {#replace_at u p (snd (\<omega> \<bullet> rl)) \<cdot> (\<delta> \<circ>\<^sub>s ?\<theta>1)#}" using vars_subS unfolding vars_term_set_def subst_term_multiset_def 
            using coincidence_lemma' by fastforce
          finally show ?thesis unfolding subst_term_multiset_def by auto
        qed
        have f1S:"subst_term_multiset ?\<theta>1 ?S = f 1"
        proof -
          have "subst_term_multiset ?\<theta>1 ?S = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) ((S - {#u#}) + {#replace_at u p (snd (\<omega> \<bullet> rl))#})"
            using subst_term_multiset_compose by blast
          also have "... = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) + subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) {#replace_at u p (snd (\<omega> \<bullet> rl))#} "(is "_ = ?A + ?B")
            unfolding subst_term_multiset_def using subst_term_multiset_union by auto
          also have "... = (T - {#s#}) + ?B" using sub_eq1 f0 by auto
          also have "... = (T - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}" using sub_eq2 by auto
          ultimately show ?thesis using f1 T' by auto
        qed
        have "\<exists>\<delta>' \<theta>' S'. multiset_narrowing_derivation_num ?S S' \<delta>' (n - 1) \<and> subst_term_multiset \<theta>' S' = f n \<and> normal_subst R \<theta>' \<and>
         (\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V"
        proof (rule IH1[of "n - 1"  ?f "f 1" "f n" ?\<theta>1 ?S ?V], goal_cases)
          case 1
          then show ?case using False by force
        next
          case 2
          then show ?case by force
        next
          case 3
          then show ?case using False by auto
        next
          case (4 i)
          then show ?case using rel_chain' by auto
        next
          case 5
          then show ?case using norm\<theta>1 by blast
        next
          case 6
          have "f 1 = subst_term_multiset ?\<theta>1 ?S" using f1S by auto
          then show ?case by blast
        next
          case 7
          then show ?case using varSV sub\<theta>1 by blast
        next
          case 8
          then show ?case using relstar by auto
        next
          case 9
          then show ?case by (meson 1(9) finite_Diff finite_UnI mgu_finite_range_vars mgu_uv)
        qed 
        then obtain \<delta>' \<theta>' S' where condn2:"multiset_narrowing_derivation_num ?S S' \<delta>' (n - 1)" and sub\<theta>':"subst_term_multiset \<theta>' S' = f n"
          and norm\<theta>':"normal_subst R \<theta>'" and sub_rel:"(\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V" by auto
        from n0_multiset_narrowing_derivation_num have n1:"n = 1 \<Longrightarrow> S' = ?S \<and> \<delta>' = Var" 
          using False using condn2 by (metis diff_self_eq_0)
        from condn2 obtain g \<tau> where "(?S,  S') \<in> (multiset_narrowing_step')^^(n - 1)" and g0:"g 0 = ?S" and gnm1:"g (n - 1) = S'"
          and gcond_chain:"\<forall>i < n - 1. ((g i), (g (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step" and comp\<delta>':"if n = 1 then \<delta>' = Var else \<delta>' = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (n - 1)])"
          using False n1 unfolding multiset_narrowing_derivation_num_def by auto
        let ?g = "\<lambda>i. if i = 0 then S else g (i - 1)"
        let ?\<tau> = "\<lambda>i. if i = 0 then \<delta> else \<tau> (i - 1)"
        have "\<delta>' = compose (map ?\<tau> [1..< n])"
          by (smt (verit) Suc_pred add_cancel_left_left add_diff_cancel_left' bot_nat_0.not_eq_extremum comp\<delta>' 
              compose_simps(1) diff_Suc_eq_diff_pred length_upt list.simps(8) map_equality_iff not_less_eq nth_upt plus_1_eq_Suc upt_0)
        hence \<delta>\<delta>'comp:"\<delta> \<circ>\<^sub>s \<delta>' = compose (map ?\<tau> [0..< n])" using False upt_conv_Cons by fastforce
        have condn:"multiset_narrowing_derivation_num S S' (\<delta> \<circ>\<^sub>s \<delta>') n" 
        proof -
          have "(S, S') \<in> multiset_narrowing_step' ^^ n" using condn1 condn2 n1 False 
            by (metis (no_types, lifting) One_nat_def Suc_pred bot_nat_0.not_eq_extremum 
                multiset_narrowing_derivation_num_def relpow_1 relpow_Suc_I2)
          moreover have "(\<exists>f. f 0 = S \<and> f n = S' \<and> (\<exists>\<tau>. (\<forall>i<n. (f i, f (Suc i), \<tau> i) \<in> multiset_narrowing_step) \<and>
            \<delta> \<circ>\<^sub>s \<delta>' = compose (map \<tau> [0..<n])))" 
            by (rule exI[of _ ?g], insert \<delta>\<delta>'comp False One_nat_def gnm1) (smt (verit, ccfv_SIG) Suc_pred gcond_chain 
                bot_nat_0.not_eq_extremum diff_Suc_1 g0 less_nat_zero_code nar not_less_eq)
          ultimately show ?thesis 
            by (simp add: multiset_narrowing_derivation_num_def False local.wf)
        qed
        show ?thesis
        proof(rule exI[of _ "\<delta> \<circ>\<^sub>s \<delta>'"], rule exI[of _ \<theta>'], rule exI[of _ S'], intro conjI, goal_cases)
          case 1
          then show ?case using condn by auto
        next
          case 2
          then show ?case using 1(3) sub\<theta>' by blast
        next
          case 3
          then show ?case using norm\<theta>' by auto
        next
          case 4
          then show ?case 
            by (metis Un_upper1 r_subst_compose reseq\<theta> sub_rel subst_monoid_mult.mult_assoc sup.orderE)
        qed
      qed
    qed
  qed
  then show ?thesis using multiset_narrowing_deriv_implication by blast
qed
  
lemma lifting_lemma_for_multiset_narrowing_for_equational_terms:
  fixes V::"('v::infinite) set" and S::"('f, 'v)term multiset" and T::"('f, 'v)term multiset"
  assumes "normal_subst R \<theta>"
    and "wf_equational_term_mset S"
    and "T = subst_term_multiset \<theta> S"
    and "vars_term_set (set_mset S) \<union> subst_domain \<theta> \<subseteq> V"
    and mrsteps:"(T,  T') \<in> (multiset_reduction_step)\<^sup>*"
    and fv:"finite V"
  shows "\<exists>\<sigma> \<theta>' S'. multiset_narrowing_derivation S S' \<sigma> \<and> T' = subst_term_multiset \<theta>' S' \<and> wf_equational_term_mset S' \<and>
      normal_subst R \<theta>' \<and> (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V" 
proof -
  from mrsteps obtain f n where f0:"f 0 = T" and fn:"f n = T'" and rel_chain:"\<forall>i < n. (f i,  f (Suc i)) \<in> multiset_reduction_step" 
    by (metis rtrancl_imp_seq)
  then have "\<exists>\<sigma> \<theta>' S'. multiset_narrowing_derivation_num S S' \<sigma> n \<and> subst_term_multiset \<theta>' S' = T' \<and> normal_subst R \<theta>' \<and> wf_equational_term_mset S' \<and>
    (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V" using assms
  proof(induct n arbitrary: S T T' \<theta> f V rule: wf_induct[OF wf_measure [of "\<lambda> n. n"]])
    case (1 n)
    note IH1 = 1(1)[rule_format]
    then show ?case
    proof(cases "n = 0")
      case True
      show ?thesis by (rule exI[of _ Var], rule exI[of _ \<theta>], rule exI[of _ S], 
            simp add:multiset_narrowing_derivation_num_def, insert True 1, auto)
    next
      case False
      hence f0f1:"(f 0, f 1) \<in> multiset_reduction_step" using 1 by auto
      then show ?thesis
      proof -
        from f0f1 obtain T T1 s \<sigma> rl p  where f0:"f 0 = T" and f1:"f 1 = T1" and s:"s \<in># T" and 
          T':"T1 = ((T - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#})" and rl:"rl \<in> R" and 
          red_pos:"p \<in> poss s" and s1p:"s |_ p = (fst rl) \<cdot> \<sigma>" 
          by (meson mul_reduction_correspondence multiset_reduction_step_posE)
        have norm\<theta>:"normal_subst R \<theta>" by fact
        hence Ts:"T = subst_term_multiset \<theta> S" using f0 1 by auto
        have "\<exists>\<omega>. V \<inter> vars_rule (\<omega> \<bullet> rl) = {}" using 1(10) 
          by (metis rule_fs.rename_avoiding supp_vars_rule_eq vars_rule_def)
        then obtain \<omega> where varempty':"V \<inter> vars_rule (\<omega> \<bullet> rl) = {}" by auto
        hence "\<exists>\<omega>r. \<omega>r \<bullet> \<omega> \<bullet> rl \<in> R" using rl
          by (metis (no_types, opaque_lifting) rule_pt.permute_minus_cancel(2) rule_pt.permute_plus)
        then obtain \<omega>r where \<omega>r:"\<omega>r \<bullet> (\<omega> \<bullet> rl) \<in> R" by auto
        from red_pos have pfs1:"p \<in> poss s" by blast
        have ps1:"p \<in> poss s" using fun_poss_imp_poss pfs1 by blast
        hence nt:"((fst rl) \<cdot> \<sigma>) \<notin> NF (rstep R)"
        proof - 
          have *:"is_Fun (fst rl)" using wf[unfolded wf_trs_def] using rl 
            by (metis is_Fun_Fun_conv prod.collapse)
          let ?C = "Hole::('f, 'v)ctxt"
          from  rl * have "(fst rl \<cdot> \<sigma>, snd rl \<cdot> \<sigma>) \<in> rstep R" 
            by (metis prod.collapse rstep_rule rstep_subst)
          then show ?thesis by auto
        qed
        obtain u where uS':"u \<in># S" and us1:"u \<cdot> \<theta> = s" using Ts s unfolding subst_term_multiset_def by auto
        have sub_eq:"(u \<cdot> \<theta>) |_ p = (fst rl) \<cdot> \<sigma>" using us1 s1p by auto
        have pu:"p \<in> fun_poss (u \<cdot> \<theta>)" using pfs1 us1
          by (metis NF_I is_VarE local.wf nt poss_is_Fun_fun_poss rstep_imp_Fun sub_eq term.distinct(1))
        have p:"p \<in> poss u" 
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence pnu:"p \<notin> poss u" by simp
          hence pnfu:"p \<notin> fun_poss u" using fun_poss_imp_poss by blast
          from poss_subst_apply_term[of p u \<theta>]
          obtain q r x where qpr:"p = q @ r" and qu:"q \<in> poss u" and uqx:"u |_ q = Var x" and r:"r \<in> poss (\<theta> x)"
            using pnfu ps1 us1 by blast
          hence *:"(u \<cdot> \<theta>) |_ p = (Var x) \<cdot> \<theta> |_ r" by force
          have "((Var x) \<cdot> \<theta>) \<in> NF (rstep R)" using norm\<theta> 
            by (simp add: normal_subst_def, metis NF_I local.wf no_Var_rstep notin_subst_domain_imp_Var)
          hence "((Var x) \<cdot> \<theta> |_ r) \<in> NF (rstep R)"  
            by (auto simp add: normal_subst_def, insert r, goal_cases) 
              (meson NF_rstep_subterm subt_at_imp_supteq')
          then show False using nt * using s1p us1 by auto
        qed
        hence pfun:"p \<in> fun_poss u"  using ps1 us1 red_pos nt norm\<theta> unfolding normal_subst_def
          by (metis pu eval_term.simps(1) fun_poss_fun_conv is_VarE notin_subst_domain_imp_Var poss_is_Fun_fun_poss sub_eq subt_at_subst term.distinct(1))
        hence vuS':"vars_term (u |_ p) \<subseteq> vars_term_set (set_mset S)" 
        proof -
          have "vars_term (u |_ p) \<subseteq> vars_term u" using p 
            by (simp add: vars_term_subt_at)
          then show ?thesis using uS' vars_term_set_def by fastforce
        qed
        with varempty' have varcond:"vars_term (u |_ p) \<inter> vars_rule (\<omega> \<bullet> rl) = {}" using 1(8) by auto
        from vuS' have vuV:"vars_term (u |_ p) \<subseteq> V" using 1(8) by auto
        have "\<exists>\<sigma>r. \<forall>t. \<sigma>r (\<omega> \<bullet> t) = \<sigma> t" using atom_pt.permute_minus_cancel(2) by (metis o_apply)
        then obtain \<sigma>r where \<sigma>rdef:"\<forall>t. \<sigma>r (\<omega> \<bullet> t) = \<sigma> t" by auto
        hence "\<sigma>r = (\<lambda>x. \<sigma> (- \<omega> \<bullet> x))" by (metis atom_pt.permute_minus_cancel(1))
        hence \<sigma>r:"\<sigma>r = (\<lambda>x. (sop (- \<omega>) \<circ>\<^sub>s \<sigma>) x)" 
          by (metis comp_apply permute_atom_def subst_compose_o_assoc subst_monoid_mult.mult.left_neutral)
        hence "\<forall>S. subst_term_set \<sigma> S = subst_term_set \<sigma>r (\<omega> \<bullet> S)" unfolding subst_term_set_def 
        proof(auto, goal_cases)
          case (1 S t)
          then show ?case 
            by (metis term_pt.permute_flip term_set_pt.mem_permute_iff)
        next
          case (2 S xa)
          then show ?case by force
        qed
        hence pc:"fst rl \<cdot> \<sigma> = fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          by (simp add: \<sigma>r rule_pt.fst_eqvt)
        have pc':"snd rl \<cdot> \<sigma> = snd (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          by (simp add: \<sigma>r rule_pt.snd_eqvt rule_pt.fst_eqvt)
        let ?\<sigma>r = "\<sigma>r |s vars_rule (\<omega> \<bullet> rl)"
        let ?\<sigma>dom = "vars_rule (\<omega> \<bullet> rl)"
        have sub_\<sigma>r:"subst_domain ?\<sigma>r \<subseteq> (vars_rule (\<omega> \<bullet> rl))" 
          using subst_domain_restrict_subst_domain by fastforce 
        let ?\<theta> = "\<theta> |s V"
        have sub_\<theta>:"subst_domain ?\<theta> \<subseteq> V" using subst_domain_restrict_subst_domain by fastforce
        have inter_empty:"subst_domain ?\<sigma>r \<inter> subst_domain ?\<theta> = {}" using varempty' 1(8) sub_\<sigma>r by auto
        have crl:"(snd (\<omega> \<bullet> rl)) \<cdot> \<sigma>r = ((snd rl) \<cdot> \<sigma>)" 
          by (simp add: \<sigma>r rule_pt.fst_eqvt rule_pt.snd_eqvt)
        note subst_rest_domain1 = subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
        have subinter:"subst_domain ?\<sigma>r = subst_domain \<sigma>r \<inter> ?\<sigma>dom" using subst_rest_domain1 by auto
        from us1 s1p have *:"(u \<cdot> \<theta> |_ p) = fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r"
          by (simp add: pc subst_apply_term_restrict_subst_domain) 
        have varcond':"vars_term (u |_ p) \<inter> vars_term (fst (\<omega> \<bullet> rl)) = {}" 
        proof -
          have "vars_term (fst (\<omega> \<bullet> rl)) \<subseteq> vars_rule (\<omega> \<bullet> rl)"
            by (metis (mono_tags, opaque_lifting) dual_order.refl le_sup_iff vars_rule_def vars_defs(2))
          then show ?thesis using varcond by auto
        qed
        with norm\<theta> * have u_p:"(u |_ p) \<cdot> \<theta> = fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          using p by simp
        have sub_eq:"(u |_ p) \<cdot> ?\<theta> = fst (\<omega> \<bullet> rl) \<cdot> ?\<sigma>r" using u_p 
          by (metis (no_types, lifting) 1(8) Un_upper1 coincidence_lemma' le_supE subst_domain_neutral vars_rule_def vars_defs(2))
        from subst_union_sound[OF sub_eq]
        have subst_eq_\<theta>\<sigma>:"(u |_ p) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)  = (fst (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using sub_\<sigma>r sub_\<theta> inter_empty
          by (smt (verit, ccfv_threshold) Int_assoc inf.orderE inf_bot_right inf_commute local.wf rl rule_pt.fst_eqvt sub_comm sub_eq subst_union_term_reduction varcond varempty' vars_rule_eqvt vars_rule_lhs vars_term_eqvt)
        then obtain \<delta> where mgu_uv:"mgu (u |_ p) (fst (\<omega> \<bullet> rl)) = Some \<delta>" using mgu_ex 
          by (meson ex_mgu_if_subst_apply_term_eq_subst_apply_term)
        hence up\<omega>rl:"(u |_ p) \<cdot> \<delta> =  fst (\<omega> \<bullet> rl) \<cdot> \<delta>" using subst_apply_term_eq_subst_apply_term_if_mgu by blast
        from mgu_sound[OF mgu_uv] have \<delta>:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) =  \<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using subst_eq_\<theta>\<sigma> 
          by (smt (verit, ccfv_SIG) is_imgu_def subst_monoid_mult.mult_assoc the_mgu the_mgu_is_imgu)
        have subst_domain\<delta>:"subst_domain \<delta> \<subseteq> vars_term (u |_ p) \<union> vars_term (fst (\<omega> \<bullet> rl))" 
          using mgu_subst_domain mgu_uv by blast
        have subst_range_disj\<delta>:"subst_domain \<delta> \<inter> range_vars \<delta> = {}" using mgu_uv mgu_subst_domain_range_vars_disjoint by blast
        let ?S = "subst_term_multiset \<delta> ((S - {#u#}) + {#replace_at u p (snd (\<omega> \<bullet> rl))#})"
        have url:"vars_term u \<inter> vars_rule (\<omega> \<bullet> rl) = {}" using vuV varempty' vuS' 1(8) 
          by (auto, metis Int_iff UN_I equals0D in_mono uS' vars_term_set_def)
        have "(S, ?S, \<delta>) \<in>  multiset_narrowing_step_pos"
          using \<omega>r url mgu_uv pfun uS' by blast
        hence nar:"(S, ?S, \<delta>) \<in>  multiset_narrowing_step" using mul_narrowing_correspondence
          by (smt (verit, ccfv_threshold) \<omega>r add_mset_add_single image_mset_add_mset mgu_uv 
              multiset_narrowing.multiset_narrowing_step.simps multiset_narrowing_axioms narrowing_stepI 
              pfun subst_term_multiset_def uS' url)
        from multiset_narrowing_set_imp_rtran[OF nar]
        have condn1:"multiset_narrowing_derivation_num S ?S \<delta> 1" by auto
        let ?V = "(V - subst_domain \<delta>) \<union> range_vars \<delta>"
        let ?\<theta>1 = "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s ?V"
        have sub\<theta>1:"subst_domain ?\<theta>1 \<subseteq> ?V" 
          by (metis inf_le1 restrict_subst subst_domain_restrict_subst_domain)
        have reseq:"?\<theta>1 |s ?V = (?\<theta> \<union>\<^sub>s ?\<sigma>r) |s  ?V" 
          by (simp add: restrict_subst_domain_def)
        have reseq\<delta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1) |s V  = (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) |s V " 
          using reseq r_subst_compose by blast
        have reseq\<theta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1)|s V = \<theta> |s V" using  \<delta> 1(8) by auto (smt (verit) \<delta> disjoint_iff notin_subst_domain_imp_Var 
              reseq\<delta> sub_\<sigma>r subset_iff subst_domain_neutral subst_ext subst_union.elims varempty')
        have "normal_subst R (?\<theta>1 |s ?V)"
        proof -
          let ?\<delta> = "\<delta> |s V"
          let ?B = "(V - subst_domain \<delta>) \<union> range_vars ?\<delta>"
          have normV:"normal_subst R (\<theta> |s V)" using norm\<theta> 1(8) by auto
          have BV:"?B \<subseteq> V - subst_domain \<delta> \<union> range_vars (\<delta> |s V)" by auto
          from restricted_normalized[OF normV reseq\<theta> BV]
          have normB:"normal_subst R (?\<theta>1 |s ?B)" by auto 
          have ranB:"range_vars \<delta> \<subseteq> ?B"
          proof
            fix x
            assume asm:"x \<in> range_vars \<delta>"
            hence xn\<delta>:"x \<notin> subst_domain \<delta>" using \<delta>
              by (meson disjoint_iff mgu_subst_domain_range_vars_disjoint mgu_uv)
            have subst_x:"x \<in> vars_term (u |_ p) \<union> vars_term (fst (\<omega> \<bullet> rl))" using mgu_uv 
                asm mgu_range_vars by auto
            then show "x \<in> ?B"
            proof
              assume "x \<in> vars_term (u |_ p)"
              hence "x \<in> V - subst_domain \<delta>" using 1(8) xn\<delta> vuS' by auto
              then show ?thesis by auto
            next
              assume asm2:"x \<in> vars_term (fst (\<omega> \<bullet> rl))"
              hence xnu:"x \<notin> vars_term (u |_ p)" using varcond' by blast
              from vars_term_range[OF asm asm2 subst_range_disj\<delta>]
              have xv\<delta>:"x \<in> vars_term (fst (\<omega> \<bullet> rl) \<cdot> \<delta>)" by auto
              have *:"x \<in> vars_term (u |_ p \<cdot> \<delta>)" using mgu_uv xv\<delta>
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu) 
              hence "vars_term (fst (\<omega> \<bullet> rl) \<cdot> \<delta>) = vars_term (u |_ p \<cdot> \<delta>)" using mgu_uv 
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu)
              from subst_restricted_range_vars[OF * subst_range_disj\<delta> xnu asm]
              have "x \<in> range_vars (\<delta> |s vars_term (u |_ p))" by auto
              moreover have upV:"vars_term (u |_ p) \<subseteq> V" using 1(8) vuS' by auto
              ultimately have "x \<in> range_vars (\<delta> |s V)" unfolding range_vars_def subst_restrict_def
                by (auto simp add: subsetD subst_domain_def) 
              then show ?thesis by auto
            qed
          qed
          hence "?B = ?V"
          proof -
            have "range_vars ?\<delta> \<subseteq> range_vars \<delta>"  unfolding subst_restrict_def range_vars_def  
              by (auto, smt (verit) mem_Collect_eq subst_domain_def, simp add: subst_domain_def)
            then show ?thesis using ranB by blast
          qed
          then show ?thesis using normB by auto
        qed
        hence norm\<theta>1:"normal_subst R ?\<theta>1" using sub\<theta>1 reseq by fastforce
        have rel_chain':"\<And>i. i < n - 1 \<Longrightarrow> (f (i + 1), f (Suc i + 1)) \<in> multiset_reduction_step" using rel_chain 
          by (simp add: 1(4))
        let ?f = "\<lambda>i. f (i + 1)"
        have relstar:"(f 1, f n) \<in> (multiset_reduction_step)\<^sup>*" using False 1(4) less_Suc_eq 
          by (induct n, blast, metis (no_types, lifting) One_nat_def rtrancl.simps)
        have vars\<theta>:"vars_term_set (set_mset S) \<union> subst_domain \<theta> \<subseteq> V" by fact
        have scomp:"?S = subst_term_multiset \<delta> (S - {#u#}) + subst_term_multiset \<delta> {#replace_at u p (snd (\<omega> \<bullet> rl))#}" (is "?S = ?fst + ?snd")
          unfolding subst_term_multiset_def by auto
        have "subst_term_multiset \<delta> {#replace_at u p (snd (\<omega> \<bullet> rl))#} \<subseteq># ?S"
          by (simp add: subst_term_multiset_def)
        hence vars_subS:"vars_term_set (set_mset (subst_term_multiset \<delta> {#replace_at u p (snd (\<omega> \<bullet> rl))#})) \<subseteq> ?V"  
        proof -
          have "vars_term (snd rl) \<subseteq> vars_term (fst rl)" using wf[unfolded wf_trs_def] rl by auto
          hence *:"vars_term (snd (\<omega> \<bullet> rl)) \<subseteq> vars_term (fst (\<omega> \<bullet> rl))" using rl by auto
              (metis UnCI rule_pt.fst_eqvt rule_pt.fst_eqvt sup.absorb_iff1 vars_defs(2) vars_rule_eqvt vars_term_eqvt)
          from var_cond_stable[OF this]
          have "vars_term (snd (\<omega> \<bullet> rl) \<cdot> \<delta> ) \<subseteq> vars_term (snd (\<omega> \<bullet> rl) \<cdot> \<delta>)" by fastforce
          from replace_var_stable[OF this] 
          have "vars_term(replace_at u p (snd (\<omega> \<bullet> rl)) \<cdot> \<delta>) \<subseteq> vars_term (replace_at u p (fst (\<omega> \<bullet> rl)) \<cdot> \<delta>)" 
            by (meson "*" replace_var_stable var_cond_stable)
          moreover have "vars_term (replace_at u p (fst (\<omega> \<bullet> rl)) \<cdot> \<delta>) = vars_term (u \<cdot> \<delta>)" using up\<omega>rl
            by (metis ctxt_supt_id p subst_apply_term_ctxt_apply_distrib)
          moreover have "vars_term (u \<cdot> \<delta>) \<subseteq> ?V" using uS' 1(8)  vars_term_set_def vars_term_subst_apply_term_subset
            by auto (fastforce, meson Diff_iff UnE subsetD vars_term_subst_apply_term_subset)
          ultimately show ?thesis unfolding vars_term_set_def subst_term_multiset_def by auto
        qed    
        have "subst_term_multiset \<delta> (S - {#u#}) \<subseteq># ?S" by (simp add: subst_term_multiset_def)
        hence vars_subSu:"vars_term_set (set_mset (subst_term_multiset \<delta> (S - {#u#}))) \<subseteq> ?V" 
        proof -
          have "vars_term_set (set_mset S) \<subseteq> V" using vars\<theta> by auto
          hence "vars_term_set (set_mset (subst_term_multiset \<delta> S)) \<subseteq> ?V" unfolding vars_term_set_def
              subst_term_multiset_def set_mset_def using vars_term_subst_apply_term_subset by fastforce+
          then show ?thesis by (smt (verit, del_insts) SUP_le_iff add_mset_add_single insert_DiffM 
                subst_term_multiset_union uS' union_iff vars_term_set_def)
        qed
        have varSV:"vars_term_set (set_mset ?S) \<subseteq> ?V"
        proof -
          have *:"vars_term_set (set_mset ?S) = vars_term_set (set_mset ?fst) \<union> vars_term_set (set_mset ?snd)"
            using scomp unfolding vars_term_set_def by auto
          then show ?thesis using vars_subS vars_subSu by auto
        qed
        have wfeq_S:"wf_equational_term_mset ?S"
        proof -
          have wf_eq_S:"wf_equational_term_mset S" by fact
          have *:"?S = subst_term_multiset \<delta> (S - {#u#}) + subst_term_multiset \<delta> {#replace_at u p (snd (\<omega> \<bullet> rl))#}"
            (is "?S = ?A + ?B") by (metis subst_term_multiset_union)
          have "wf_equational_term_mset ?A"
          proof -
            have "wf_equational_term_mset (S - {#u#})"
              by (meson in_diffD wf_eq_S wf_equational_term_mset_def)
            then show ?thesis unfolding wf_equational_term_mset_def using wf_eq_subst
              by (metis wf_eq_mset_subst_inv wf_equational_term_mset_def)
          qed
          moreover  
          {
            let ?rule = "(Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
            have cr:"funas_rule ?rule = {(\<doteq>, 2), (\<top>, 0)}" using D 
              unfolding funas_defs by (auto simp add: numeral_2_eq_2)
            have cd:"funas_rule ?rule \<subseteq> D" using D 
              unfolding funas_defs by (auto simp add: numeral_2_eq_2)
            have wf_u:"wf_equational_term u" using uS' wf_eq_S wf_equational_term_mset_def by auto
            have \<omega>rl:"rl \<in> R' \<or> (rl = ?rule)" using R' rl by auto
            moreover have \<omega>rl_un:"funas_rule (rl) \<subseteq> F  \<or> (rl = ?rule) \<and> rl \<notin> R'" 
              using R_sig calculation by (metis funas_defs(2) le_supI lhs_wf prod.exhaust_sel rhs_wf)
            ultimately have "funas_rule rl \<subseteq> F \<or> funas_rule rl = {(\<doteq>, 2), (\<top>, 0)} \<and> rl \<notin> R'"
              using cr by metis
            then consider (ordinary) "funas_rule (rl) \<subseteq> F" | (special) "funas_rule rl = {(\<doteq>, 2), (\<top>, 0)} \<and> rl \<notin> R'" 
              using \<omega>rl by auto
            hence "wf_equational_term (replace_at u p (snd (\<omega> \<bullet> rl)))"
            proof(cases)
              case ordinary
              hence rlR':"rl \<in> R'" using R' D R_sig D_fresh 
                by (metis Int_absorb2 \<omega>rl cr insert_not_empty)
              from ordinary have *:"funas_rule (\<omega> \<bullet> rl) \<subseteq> F" using funas_rule_perm by blast
              have **:"root (fst (\<omega> \<bullet> rl)) = root (fst (rl))" using root_perm_inv
                by (metis rule_pt.fst_eqvt rule_pt.fst_eqvt)
              have ***:"is_Fun (fst rl)"  using ** wf[unfolded wf_trs_def]
                using rl by (metis is_FunI prod.exhaust_sel)
              from fun_root_not_None[OF ***] have nroot:"root (fst rl) \<noteq> None" by auto
              from root_not_special_symbols[OF rlR' ordinary nroot]
              have "root(fst rl) \<noteq> Some (\<doteq>, 2) \<and> root(fst rl) \<noteq>  Some (\<top>, 0)" by simp
              hence rn:"root(fst (\<omega> \<bullet> rl)) \<noteq> Some (\<doteq>, 2) \<and> root(fst (\<omega> \<bullet> rl)) \<noteq> Some (\<top>, 0)" 
                by (simp add: "**")
              have "root (u |_ p) = root (fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r)" using u_p 
                by (metis pfun root_subst_inv)
              also have "... = root(fst (\<omega> \<bullet> rl))" 
                using wf[unfolded wf_trs_def] root_subst_inv ** *** pc by auto
              finally have root_eq:"root (u |_ p) = root(fst (\<omega> \<bullet> rl))" by auto
              with u_p pfun have "root (u |_ p) \<noteq> Some (\<doteq>, 2) \<and> root (u |_ p) \<noteq> Some (\<top>, 0)"
                using rn by auto
              hence np:"p \<noteq> []" using wf_u[unfolded wf_equational_term_def] by force
              hence uf:"u \<noteq> Fun (\<top>) []" using pfun by auto
              from wf_u[unfolded wf_equational_term_def]
              obtain v w where u:"u = Fun \<doteq> [v, w] \<and> (\<doteq>, 2) \<notin> funas_term v \<and> (\<doteq>, 2) \<notin> funas_term w"
                using uf by auto
              have "funas_term (snd (\<omega> \<bullet> rl)) \<subseteq> F" using * unfolding funas_defs by blast
              then show ?thesis by (simp add: np wf_equational_term_safe_replace wf_u uf pfun)
            next
              case special
              with rl have rl: "rl = ?rule" unfolding R' by auto
              define y where "y = \<omega> \<bullet> x" 
              let ?ruley = "(Fun \<doteq> [Var y, Var y], Fun \<top> [])" 
              from rl have \<omega>'rl: "\<omega> \<bullet> rl = ?ruley" by (simp add: rule_pt.permute_prod_eqvt y_def)
              have lhs:"root (fst (\<omega> \<bullet> rl)) = Some (\<doteq>, 2)" using \<omega>'rl by auto
              have rhs_\<omega>'rl:"snd (\<omega> \<bullet> rl) = Fun (\<top>) []" using \<omega>'rl by auto
              have isFun\<omega>':"is_Fun (fst (\<omega> \<bullet> rl))" by (simp add: \<omega>'rl)
              from fun_root_not_None[OF isFun\<omega>'] have nroot:"root (fst (\<omega> \<bullet> rl)) \<noteq> None" by auto
              have rhs\<sigma>r:"root(fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r) = Some (\<doteq>, 2)" using \<omega>'rl by auto
              have "root (u |_ p) = root (fst (\<omega> \<bullet> rl) \<cdot> \<sigma>r)" using u_p 
                by (metis pfun root_subst_inv)
              also have "... = root(fst (\<omega> \<bullet> rl))" 
                using wf[unfolded wf_trs_def] root_subst_inv lhs rhs\<sigma>r by auto
              finally have root_eq:"root (u |_ p) = root(fst (\<omega> \<bullet> rl))" by auto
              with u_p pfun have root_u:"root (u |_ p) = Some (\<doteq>, 2)" using lhs by auto
              have un:"u \<noteq> Fun (\<top>) []"
              proof(rule ccontr)
                assume "\<not> ?thesis"
                hence "u = Fun (\<top>) []" by auto
                hence "funas_term u = {(\<top>, 0)}" by auto
                then show False using root_u subterm_funas pfun by fastforce
              qed
              from wf_u[unfolded wf_equational_term_def] 
              obtain v w where u:"u = Fun (\<doteq>) [v, w]" and nv:"(\<doteq>, 2) \<notin> funas_term v" and 
                nw:"(\<doteq>, 2) \<notin> funas_term w" using un by auto
              have p:"p = []"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                hence "v \<unrhd> (u |_ p) \<or> w \<unrhd> (u |_ p)" using pfun u by auto
                    (metis diff_Suc_1 fun_poss_imp_poss less_Suc0 less_Suc_eq nth_Cons' subt_at_imp_supteq)
                then show False using root_u nv nw 
                  by (meson root_symbol_in_funas subset_eq supteq_imp_funas_term_subset)
              qed
              hence "replace_at u p (snd (\<omega> \<bullet> rl)) = snd (\<omega> \<bullet> rl)" by auto
              then show ?thesis using rhs_\<omega>'rl wf_u[unfolded wf_equational_term_def] 
                by (simp add: wf_equational_term_def)
            qed
            hence "wf_equational_term_mset ?B" unfolding wf_equational_term_mset_def subst_term_multiset_def 
              using wf_eq_subst by fastforce
          }   
         ultimately show ?thesis using "*" wf_equational_term_mset_add by auto
        qed
        from subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
        have subinter:"subst_domain ?\<sigma>r = subst_domain \<sigma>r \<inter> ?\<sigma>dom" by auto
        have inempty:"subst_domain ?\<sigma>r \<inter> V = {}" using varempty' subinter by auto
        hence \<theta>sv:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s V = \<theta> |s V"
          using \<delta> reseq\<delta> reseq\<theta> by auto
        have \<theta>varr:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s (vars_term (\<omega> \<bullet> snd rl)) = ?\<sigma>r |s (vars_term (\<omega> \<bullet> snd rl))" 
        proof -
          { fix v :: 'v
            have "vars_rule (\<omega> \<bullet> (fst rl, snd rl)) - V = vars_rule (\<omega> \<bullet> (fst rl, snd rl))" using varempty' unfolding funas_defs 
              by (auto simp add: rule_pt.fst_eqvt disjoint_iff vars_rule_def)
            then have "V \<inter> vars_term (\<omega> \<bullet> snd rl) = {}"
              by (metis Un_Int_eq(4) inf_bot_right inf_left_commute rule_pt.snd_eqvt varempty' vars_rule_def)
            then have "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s (vars_term (\<omega> \<bullet> snd rl)) = ?\<sigma>r |s (vars_term (\<omega> \<bullet> snd rl))"
              by (smt (verit, best) Int_iff disjoint_iff inf.absorb_iff2 sub_\<theta> subst_ext subst_union.simps)
          } then show ?thesis by fastforce
        qed
        have subeq:"subst_rule \<sigma>r (\<omega> \<bullet> (fst rl, snd rl)) = subst_rule \<sigma> (fst rl, snd rl)" 
          unfolding subst_rule_def subst_list_def using pc' pc rule_pt.fst_eqvt by simp
        have sub_eq1:"subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) = f 0 - {#s#}"
        proof -  
          have "vars_term_set (set_mset (subst_term_multiset \<delta> (S - {#u#}))) \<subseteq> ?V" using vars_subSu by auto
          hence subm_eq:"subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) = subst_term_multiset (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) (S - {#u#})" using reseq\<delta> 
            by (metis (no_types, opaque_lifting) restrict_subst subst_term_multiset_compose subst_term_multiset_rest_domain)
          hence "... = subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (S - {#u#})" using \<delta> by auto
          have *:"subst_domain ?\<theta> \<subseteq> V" by fact
          have **:"subst_domain ?\<sigma>r \<inter> vars_term_set (set_mset (S - {#u#})) = {}" unfolding vars_term_set_def set_mset_def           
            by (smt (verit, ccfv_threshold) "1.prems"(7) SUP_le_iff count_greater_zero_iff disjoint_iff 
                in_diffD inempty le_supE mem_Collect_eq subsetD vars_term_set_def)
          from subst_union_term_multiset_reduction[of ?\<theta> ?\<sigma>r S]
          have ***:"subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) S = f 0" 
            by (metis Ts \<theta>sv f0 le_supE restrict_subst subst_term_multiset_rest_domain vars\<theta>)
          from subst_union_term_multiset_reduction[OF inter_empty **]
          have "subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (S - {#u#}) = subst_term_multiset ?\<theta> (S - {#u#})" by (metis inter_empty sub_comm)
          also have "... = subst_term_multiset ?\<theta> S - subst_term_multiset ?\<theta> {#u#}" 
            by (simp add: image_mset_Diff subst_term_multiset_def uS')
          also have "... = subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) S - subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) {#u#}"
            by (metis calculation image_mset_Diff mset_subset_eq_single subst_term_multiset_def uS')
          also have "... = f 0 - subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) {#u#}" using *** by auto
          also have "... = f 0 - {#s#}" unfolding subst_term_multiset_def
            by (metis (no_types, lifting) 1(8) SUP_le_iff \<theta>sv coincidence_lemma' 
                image_mset_add_mset image_mset_empty le_supE uS' us1 vars_term_set_def)
          finally show ?thesis using \<delta> subm_eq by auto
        qed
        have sub_eq2:"{#replace_at s p ((snd rl) \<cdot> \<sigma>)#} = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) {#replace_at u p (snd (\<omega> \<bullet> rl))#}" 
        proof -
          have "(snd rl) \<cdot> \<sigma> = snd (\<omega> \<bullet> rl) \<cdot> \<sigma>r" using subeq by (simp add: pc')
          have "{#replace_at s p ((snd rl) \<cdot> \<sigma>)#} = {#replace_at s p ((snd (\<omega> \<bullet> rl)) \<cdot> \<sigma>r)#}" using \<sigma>rdef pc  pc' by auto 
          also have "... = {#replace_at (u \<cdot> \<theta>) p ((snd (\<omega> \<bullet> rl)) \<cdot> \<sigma>r)#}" using us1 by auto
          also have "... = {#replace_at (u \<cdot> \<theta>) p ((snd (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r))#}" using \<theta>sv \<theta>varr vuV vars\<theta> uS'  in_subst_restrict 
            by (simp add: vars_defs(2), smt (verit, ccfv_SIG) Un_Int_eq(2) eval_same_vars in_mono in_subst_restrict rule_pt.snd_eqvt) 
          also have "... = {#replace_at (u \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)) p ((snd (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r))#}" using \<theta>sv \<theta>varr vuV vars\<theta> uS' 
            by (smt (verit, best) Int_absorb1 UN_I Un_upper1 rule_pt.fst_eqvt in_subst_restrict 
                le_supE rule_pt.snd_eqvt subsetD term_subst_eq_conv uS' vars\<theta> vars_rule_def vars_defs(2) vars_term_set_def)
          also have "... = {#replace_at u p (snd (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)#}" by (simp add: ctxt_of_pos_term_subst p)
          also have "... = {#replace_at u p (snd (\<omega> \<bullet> rl)) \<cdot> (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r))#}" using \<delta> by auto
          also have "... = {#replace_at u p (snd (\<omega> \<bullet> rl)) \<cdot> (\<delta> \<circ>\<^sub>s ?\<theta>1)#}" using vars_subS unfolding vars_term_set_def subst_term_multiset_def 
            using coincidence_lemma' by fastforce
          finally show ?thesis unfolding subst_term_multiset_def by auto
        qed
        have f1S:"subst_term_multiset ?\<theta>1 ?S = f 1"
        proof -
          have "subst_term_multiset ?\<theta>1 ?S = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) ((S - {#u#}) + {#replace_at u p (snd (\<omega> \<bullet> rl))#})"
            using subst_term_multiset_compose by blast
          also have "... = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) + subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) {#replace_at u p (snd (\<omega> \<bullet> rl))#} "(is "_ = ?A + ?B")
            unfolding subst_term_multiset_def using subst_term_multiset_union by auto
          also have "... = (T - {#s#}) + ?B" using sub_eq1 f0 by auto
          also have "... = (T - {#s#}) + {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}" using sub_eq2 by auto
          ultimately show ?thesis using f1 T' by auto
        qed
        have "\<exists>\<delta>' \<theta>' S'. multiset_narrowing_derivation_num ?S S' \<delta>' (n - 1) \<and> subst_term_multiset \<theta>' S' = f n \<and> normal_subst R \<theta>' \<and> wf_equational_term_mset S' \<and>
         (\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V"
        proof (rule IH1[of "n - 1"  ?f "f 1" "f n" ?\<theta>1 ?S ?V], goal_cases)
          case 1
          then show ?case using False by force
        next
          case 2
          then show ?case by force
        next
          case 3
          then show ?case using False by auto
        next
          case (4 i)
          then show ?case using rel_chain' by auto
        next
          case 5
          then show ?case using norm\<theta>1 by blast
        next
          case 6
          have "wf_equational_term_mset ?S" using wfeq_S by blast
          then show ?case by auto
        next
          case 7
          have "f 1 = subst_term_multiset ?\<theta>1 ?S" using f1S by auto
          then show ?case by blast
        next
          case 8
          then show ?case using varSV sub\<theta>1 by blast
        next
          case 9
          then show ?case using relstar by auto
        next
          case 10
          then show ?case by (meson 1(10) finite_Diff finite_UnI mgu_finite_range_vars mgu_uv)
        qed 
        then obtain \<delta>' \<theta>' S' where condn2:"multiset_narrowing_derivation_num ?S S' \<delta>' (n - 1)" and sub\<theta>':"subst_term_multiset \<theta>' S' = f n"
          and norm\<theta>':"normal_subst R \<theta>'" and wfS':"wf_equational_term_mset S'" and sub_rel:"(\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V" by auto
        from n0_multiset_narrowing_derivation_num have n1:"n = 1 \<Longrightarrow> S' = ?S \<and> \<delta>' = Var" 
          using False using condn2 by (metis diff_self_eq_0)
        from condn2 obtain g \<tau> where "(?S,  S') \<in> (multiset_narrowing_step')^^(n - 1)" and g0:"g 0 = ?S" and gnm1:"g (n - 1) = S'"
          and gcond_chain:"\<forall>i < n - 1. ((g i), (g (Suc i)), (\<tau> i)) \<in> multiset_narrowing_step" and comp\<delta>':"if n = 1 then \<delta>' = Var else \<delta>' = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (n - 1)])"
          using False n1 unfolding multiset_narrowing_derivation_num_def by auto
        let ?g = "\<lambda>i. if i = 0 then S else g (i - 1)"
        let ?\<tau> = "\<lambda>i. if i = 0 then \<delta> else \<tau> (i - 1)"
        have "\<delta>' = compose (map ?\<tau> [1..< n])"
          by (smt (verit) Suc_pred add_cancel_left_left add_diff_cancel_left' bot_nat_0.not_eq_extremum comp\<delta>' 
              compose_simps(1) diff_Suc_eq_diff_pred length_upt list.simps(8) map_equality_iff not_less_eq nth_upt plus_1_eq_Suc upt_0)
        hence \<delta>\<delta>'comp:"\<delta> \<circ>\<^sub>s \<delta>' = compose (map ?\<tau> [0..< n])" using False upt_conv_Cons by fastforce
        have condn:"multiset_narrowing_derivation_num S S' (\<delta> \<circ>\<^sub>s \<delta>') n" 
        proof -
          have "(S, S') \<in> multiset_narrowing_step' ^^ n" using condn1 condn2 n1 False 
            by (metis (no_types, lifting) One_nat_def Suc_pred bot_nat_0.not_eq_extremum 
                multiset_narrowing_derivation_num_def relpow_1 relpow_Suc_I2)
          moreover have "(\<exists>f. f 0 = S \<and> f n = S' \<and> (\<exists>\<tau>. (\<forall>i<n. (f i, f (Suc i), \<tau> i) \<in> multiset_narrowing_step) \<and>
            \<delta> \<circ>\<^sub>s \<delta>' = compose (map \<tau> [0..<n])))" 
            by (rule exI[of _ ?g], insert \<delta>\<delta>'comp False One_nat_def gnm1) (smt (verit, ccfv_SIG) Suc_pred gcond_chain 
                bot_nat_0.not_eq_extremum diff_Suc_1 g0 less_nat_zero_code nar not_less_eq)
          ultimately show ?thesis 
            by (simp add: multiset_narrowing_derivation_num_def False local.wf)
        qed
        show ?thesis
        proof(rule exI[of _ "\<delta> \<circ>\<^sub>s \<delta>'"], rule exI[of _ \<theta>'], rule exI[of _ S'], intro conjI, goal_cases)
          case 1
          then show ?case using condn by auto
        next
          case 2
          then show ?case using 1(3) sub\<theta>' by blast
        next
          case 3
          then show ?case using norm\<theta>' by auto
        next
          case 4
          then show ?case using wfS' by blast
        next
          case 5
          then show ?case 
            by (metis Un_upper1 r_subst_compose reseq\<theta> sub_rel subst_monoid_mult.mult_assoc sup.orderE)
        qed
      qed
    qed
  qed
  then show ?thesis using multiset_narrowing_deriv_implication by blast
qed

end
end