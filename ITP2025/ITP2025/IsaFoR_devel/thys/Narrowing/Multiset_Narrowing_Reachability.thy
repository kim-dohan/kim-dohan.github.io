(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Formalization of multiset narrowing based (multiset) reachability analysis\<close>

theory Multiset_Narrowing_Reachability
  imports
    Multiset_Narrowing
begin

locale multiset_narrowing_reachability =  multiset_narrowing R DOTEQ TOP R' F D x
  for R::"('f, 'v:: infinite) trs" 
    and DOTEQ :: 'f ("\<doteq>")
    and TOP :: "'f" ("\<top>") 
    and R' :: "('f, 'v:: infinite) trs" 
    and F :: "'f sig" 
    and D :: "'f sig"
    and x :: 'v
begin

(* We consider multiset narrowing on multisets of ordinary terms, multisets of equational terms, and multisets of pairs of terms.
  First, consider multiset narrowing on multisets of pairs of terms for (ordinary) reachability analysis.*)

definition subst_pairs_multiset :: "('f, 'v) subst \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term) multiset \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term) multiset" where
  "subst_pairs_multiset \<sigma> M = {# (s \<cdot> \<sigma>, t \<cdot> \<sigma>). (s, t) \<in># M #}"

inductive_set multiset_pair_reduction_step where 
    "(s, t) \<in># S \<and> T = (S - {#(s,t)#} + {#(u, t)#}) \<and> (s, u) \<in> rstep R \<Longrightarrow> (S, T) \<in> multiset_pair_reduction_step"

inductive_set multiset_pair_narrowing_step where 
    "(s, t) \<in># S \<and> T = (subst_pairs_multiset \<sigma> (S - {#(s,t)#}) + {#(u, t \<cdot> \<sigma>)#}) \<and> (s, u, \<sigma>) \<in> narrowing_step  
        \<Longrightarrow> (S, T, \<sigma>) \<in> multiset_pair_narrowing_step"

lemmas multiset_pair_reduction_stepI = multiset_pair_reduction_step.intros [intro]
lemmas multiset_pair_reduction_stepE = multiset_pair_reduction_step.cases [elim]
lemmas multiset_pair_narrowing_stepI = multiset_pair_narrowing_step.intros [intro]
lemmas multiset_pair_narrowing_stepE = multiset_pair_narrowing_step.cases [elim]

definition multiset_pair_narrowing_derivation where
  "multiset_pair_narrowing_derivation G G' \<sigma> \<longleftrightarrow> (\<exists>n. (\<exists>f \<tau>. f 0 = G \<and> f n = G' \<and> 
  (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_pair_narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

definition multiset_pair_narrowing_derivation_num where
  "multiset_pair_narrowing_derivation_num G G' \<sigma> n \<longleftrightarrow> (\<exists>f \<tau>. f 0 = G \<and> f n = G' \<and> 
  (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_pair_narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n])))"

definition syntactically_unifiable where
  "syntactically_unifiable \<sigma> S \<longleftrightarrow> (\<forall> (s, t) \<in># S. s \<cdot> \<sigma> = t \<cdot> \<sigma>)"

definition trivially_unifiable where
  "trivially_unifiable S \<longleftrightarrow> (\<forall> (s, t) \<in># S. s = t)"

definition R_solution_of_goal where
  "R_solution_of_goal \<sigma> S \<longleftrightarrow> (\<forall> (s, t) \<in># S. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*)"

lemma n0_multiset_pair_narrowing_derivation_num:"multiset_pair_narrowing_derivation_num G G' \<sigma> 0 \<Longrightarrow> G = G' \<and> \<sigma> = Var"
  unfolding multiset_pair_narrowing_derivation_num_def by auto

lemma multiset_reachability_narrowing_deriv_implication: assumes "multiset_pair_narrowing_derivation_num G G' \<sigma> n"
  shows "multiset_pair_narrowing_derivation G G' \<sigma>" 
  unfolding multiset_pair_narrowing_derivation_num_def multiset_pair_narrowing_derivation_def 
  using assms multiset_pair_narrowing_derivation_num_def by metis

lemma multiset_reachability_reduction_trivial_solution: assumes gr_steps:"(G, G') \<in> multiset_pair_reduction_step\<^sup>*"
    and un:"trivially_unifiable G'"
  shows "(\<forall> (s, t) \<in># G. (s, t) \<in> (rstep R)\<^sup>*)"
proof -
  note gdefs = subst_pairs_multiset_def trivially_unifiable_def R_solution_of_goal_def 
  from gr_steps obtain n where "(G, G') \<in> (multiset_pair_reduction_step)^^n" by auto
  then show ?thesis using un
  proof(induct n arbitrary: G G' rule: wf_induct[OF wf_measure [of "\<lambda> n. n"]])
    case (1 n)
    note IH1 = 1(1)[rule_format]
    then show ?case
    proof(cases "n = 0")
      case True
      with step have "G = G'" using 1 by auto
      then show ?thesis unfolding gdefs using 1 trivially_unifiable_def
        by (smt (verit, ccfv_SIG) case_prodD case_prodI2 rtrancl.simps)
    next
      case False
      with 1(2) obtain U where step:"(G, U) \<in> (multiset_pair_reduction_step)" and
        UG':"(U, G') \<in> (multiset_pair_reduction_step)^^ (n - 1)" by (metis False One_nat_def diff_Suc_1 relpow_E2)
      with 1(2) obtain s t u where stG:"(s, t) \<in># G" and U:"U = (G - {#(s,t)#} + {#(u, t)#})" and 
        su:"(s, u) \<in> rstep R" by auto
      have IH:"(\<forall> (s, t) \<in># U. (s, t) \<in> (rstep R)\<^sup>*)" 
      proof
        fix v w
        assume asm:"(v, w) \<in># U"
        then show "(v, w) \<in> (rstep R)\<^sup>*" using IH1[of "n-1" U G' "(v, w)"] 1(3) False UG' by fastforce
      qed
      hence *:"(\<forall> (s, t) \<in># (G - {#(s,t)#}). (s, t) \<in> (rstep R)\<^sup>*)" using U by auto
      have "(u, t) \<in> (rstep R)\<^sup>*" using U IH by auto
      hence "(s, t) \<in> (rstep R)\<^sup>*" using su by auto
      then show ?thesis using *
      by (metis stG add_mset_remove_trivial_eq case_prodI insert_noteq_member)
    qed
  qed
qed

lemma multiset_reachability_reduction_solution: assumes gr_steps:"(subst_pairs_multiset \<sigma> G, G') \<in> multiset_pair_reduction_step\<^sup>*"
    and un:"trivially_unifiable G'"
  shows "R_solution_of_goal \<sigma> G" 
proof (rule ccontr)
  note gdefs = subst_pairs_multiset_def trivially_unifiable_def R_solution_of_goal_def 
  assume "\<not> ?thesis"
  hence "(\<exists> (s, t) \<in># G. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<notin> (rstep R)\<^sup>*)" unfolding gdefs by auto
  then obtain s t where "(s, t) \<in># G" and "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<notin> (rstep R)\<^sup>*" by auto
  then show False using multiset_reachability_reduction_trivial_solution[OF gr_steps un] unfolding gdefs by auto 
qed

lemma subst_closed_multiset_reachability_reduction: assumes "(S, T) \<in> (multiset_pair_reduction_step)\<^sup>*"
shows "(subst_pairs_multiset \<sigma> S, subst_pairs_multiset \<sigma> T) \<in> (multiset_pair_reduction_step)\<^sup>*"
proof -
  from assms obtain n where "(S, T) \<in> (multiset_pair_reduction_step)^^n" by auto
  then show ?thesis
  proof(induct n arbitrary:T \<sigma>)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    from Suc(2) obtain U where SU:"(S, U) \<in> multiset_pair_reduction_step ^^ n" and UT:"(U, T) \<in> multiset_pair_reduction_step" by auto
    from Suc(1) have gstep:"(subst_pairs_multiset \<sigma> S, subst_pairs_multiset \<sigma> U) \<in> multiset_pair_reduction_step\<^sup>*" by (simp add: SU)
    from UT obtain s t u where st:"(s, t) \<in># U" and T:"T = (U - {#(s,t)#} + {#(u, t)#})" and su:"(s, u) \<in> rstep R" by auto
    let ?s = "s \<cdot> \<sigma>"
    let ?t = "t \<cdot> \<sigma>"
    let ?u = "u \<cdot> \<sigma>"
    let ?U = "subst_pairs_multiset \<sigma> U"
    let ?T = "subst_pairs_multiset \<sigma> T"
    have *:"(?s, ?t) \<in># ?U" using st unfolding subst_pairs_multiset_def by auto
    have **:"?T = ?U - {#(?s, ?t)#} + {#(?u, ?t)#}" unfolding subst_pairs_multiset_def using T 
      by (auto, metis (no_types, lifting) add_mset_remove_trivial case_prod_conv image_mset_add_mset insert_DiffM st)
    have "(?s, ?u) \<in> rstep R" using su by auto
    with UT have "(subst_pairs_multiset \<sigma> U, subst_pairs_multiset \<sigma> T) \<in> multiset_pair_reduction_step" 
      using multiset_pair_reduction_step.intros[of ?s ?t ?U ?T ?u] * ** by auto
    then show ?case using gstep by force
  qed
qed

lemma subst_multiset_equiv: "{# (s \<cdot> \<theta>, t \<cdot> \<theta>). (s, t) \<in># {# (s \<cdot> \<sigma>, t \<cdot> \<sigma>). (s, t) \<in># S #} #} = {# (s \<cdot> \<sigma> \<cdot> \<theta>, t \<cdot> \<sigma> \<cdot> \<theta>). (s, t) \<in># S #}" 
proof -
  have "{# (s \<cdot> \<theta>, t \<cdot> \<theta>). (s, t) \<in># {# (s \<cdot> \<sigma>, t \<cdot> \<sigma>). (s, t) \<in># S #} #} = {# (s , t ). (s, t) \<in># {# (s \<cdot> \<sigma> \<cdot> \<theta>, t \<cdot> \<sigma> \<cdot> \<theta>). (s, t) \<in># S #} #}"
    by (auto, smt (verit, ccfv_SIG) comp_apply multiset.map_comp multiset.map_cong0 prod.sel(1) prod.sel(2) split_beta)
  then show ?thesis by auto
qed

lemma subst_closed_compose: "subst_pairs_multiset \<theta> (subst_pairs_multiset \<sigma> S) = subst_pairs_multiset (\<sigma> \<circ>\<^sub>s \<theta>) S"
  by (simp add: subst_multiset_equiv subst_pairs_multiset_def)

lemma multiset_reachability_narrowing_reduction: assumes gnd:"multiset_pair_narrowing_derivation G G' \<sigma>"
  shows "(subst_pairs_multiset \<sigma> G, G') \<in> (multiset_pair_reduction_step)\<^sup>*"
proof -
  note gdefs = subst_pairs_multiset_def trivially_unifiable_def R_solution_of_goal_def 
  from gnd obtain n where "multiset_pair_narrowing_derivation_num G G' \<sigma> n" unfolding multiset_pair_narrowing_derivation_num_def
    multiset_pair_narrowing_derivation_def by auto
  then show ?thesis
  proof(induct n arbitrary: G' \<sigma>)
    case 0
    hence "G' = G" and "\<sigma> = Var" using n0_multiset_pair_narrowing_derivation_num by blast+
    then show ?case unfolding gdefs by auto
  next
    case (Suc n)
    from \<open>multiset_pair_narrowing_derivation_num G G' \<sigma> (Suc n)\<close>
    have "(\<exists>f \<tau>. f 0 = G \<and> f (Suc n) = G' \<and> 
      (\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_pair_narrowing_step) \<and> (\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< Suc n])))"
      unfolding multiset_pair_narrowing_derivation_num_def by auto
    then obtain f \<tau> where f0:"f 0 = G" and fsucn:"f (Suc n) = G'" and 
      relchain:"\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_pair_narrowing_step" 
      and \<sigma>:"(\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (Suc n)]))" by auto
    let ?\<tau> = "compose (map (\<lambda>i. (\<tau> i)) [0 ..< n])"
    let ?\<sigma> = "if n = 0 then Var else ?\<tau>"
    let ?f = "\<lambda>i. (if i \<le> n then f i else undefined)"
    from relchain obtain U where U:"f n = U" by simp
    from relchain have nchain:"\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_pair_narrowing_step" by simp
    have "(\<exists>f \<tau>. f 0 = G \<and> f n = U \<and> (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> multiset_pair_narrowing_step))"
      by (rule exI[of _ "?f"] rule exI[of _ "?\<sigma>"], insert U f0 nchain, auto)
    moreover have "multiset_pair_narrowing_derivation_num G U ?\<sigma> n" unfolding multiset_pair_narrowing_derivation_num_def
      using U calculation f0 nchain by auto 
    ultimately have IH:"(subst_pairs_multiset ?\<sigma> G, U) \<in> multiset_pair_reduction_step\<^sup>*" using Suc(1) by auto
    have "(U, G', \<tau> n) \<in> multiset_pair_narrowing_step" using relchain fsucn U by auto
    then obtain s t u  where st:"(s, t) \<in># U" and G':"G' = subst_pairs_multiset (\<tau> n) (U - {#(s,t)#}) + {#(u, t \<cdot> (\<tau> n))#}"
     and su:"(s, u, (\<tau> n)) \<in> narrowing_step" by auto
    let ?s = "s \<cdot> (\<tau> n)"
    let ?t = "t \<cdot> (\<tau> n)"
    let ?U = "subst_pairs_multiset (\<tau> n) U"
    have *:"(?s, ?t) \<in># ?U" using st subst_pairs_multiset_def by (smt (verit) add_mset_remove_trivial_eq 
      case_prod_conv image_mset_add_mset union_single_eq_member)
    have "G' = {#(u, ?t)#} + (?U - {#(?s, ?t)#})" using G' unfolding gdefs 
      by (simp add: image_mset_Diff st)
    hence G':"G' = ?U - {#(?s, ?t)#} + {#(u, ?t)#}" by auto
    have "(s \<cdot> (\<tau> n),  u) \<in> rstep R" using su
    proof -
      from su obtain rl \<omega> p where t':"u = (replace_at s p (snd rl)) \<cdot> (\<tau> n)" and \<omega>rl:"\<omega> \<bullet> rl \<in> R"
        and disj:"(vars_term s \<inter> vars_rule rl = {})" and p:"p \<in> fun_poss s" and mgu:"mgu (s |_ p) (fst rl) = Some (\<tau> n)" by auto
      from t' have t:"u = replace_at (s \<cdot> (\<tau> n)) p (snd rl \<cdot> (\<tau> n))" using p 
        by (simp add: ctxt_of_pos_term_subst fun_poss_imp_poss)
      let ?C = "ctxt_of_pos_term p (s \<cdot> (\<tau> n))"
      from mgu have "(s |_ p) \<cdot> (\<tau> n) = fst rl \<cdot> (\<tau> n)" using subst_apply_term_eq_subst_apply_term_if_mgu by auto
      then show ?thesis using rstep.intros[of "fst rl" "snd rl" R "s \<cdot> (\<tau> n)" ?C "(\<tau> n)" u] 
        by (smt (verit) \<omega>rl fun_poss_imp_poss p perm_rstep_conv poss_imp_subst_poss prod.exhaust_sel 
            replace_at_ident rstep_ctxt rstep_subst subset_iff subset_rstep subt_at_subst t)
    qed
    hence **:"(?U, G') \<in> multiset_pair_reduction_step" using multiset_pair_reduction_step.intros * G' by auto
    have \<sigma>:"\<sigma> = ?\<sigma> \<circ>\<^sub>s (\<tau> n)" using \<sigma> by auto
    let ?G = "subst_pairs_multiset ?\<sigma> G"
    from subst_closed_compose[of "(\<tau> n)" ?\<sigma> G]
    have "subst_pairs_multiset (\<tau> n) ?G = subst_pairs_multiset (?\<sigma> \<circ>\<^sub>s (\<tau> n)) G" by auto
    from subst_closed_multiset_reachability_reduction[of "subst_pairs_multiset ?\<sigma> G" U "\<tau> n"]
    have "(subst_pairs_multiset \<sigma> G, subst_pairs_multiset (\<tau> n) U) \<in> multiset_pair_reduction_step\<^sup>*" 
      using IH \<sigma> subst_closed_compose by metis
    then show ?case using IH ** unfolding gdefs by auto 
  qed
qed

(* A sufficient condition for reachability for multiple goals,  MT2005 *)

proposition reachable_condition_multiple_goals:assumes gnd:"multiset_pair_narrowing_derivation G G' \<sigma>"
    and un:"syntactically_unifiable \<eta> G'"
  shows "R_solution_of_goal (\<sigma> \<circ>\<^sub>s \<eta>) G"
proof -
  note gdefs = subst_pairs_multiset_def syntactically_unifiable_def trivially_unifiable_def R_solution_of_goal_def
  from multiset_reachability_narrowing_reduction[of G G' \<sigma>]
  have srstep:"(subst_pairs_multiset \<sigma> G, G') \<in> multiset_pair_reduction_step\<^sup>*" using gnd by auto
  from subst_closed_multiset_reachability_reduction[of "subst_pairs_multiset \<sigma> G" G' \<eta>]
  have subcom:"(subst_pairs_multiset \<eta> (subst_pairs_multiset \<sigma> G), subst_pairs_multiset \<eta> G') \<in> multiset_pair_reduction_step\<^sup>*" using srstep by auto
  from subst_closed_compose[of \<eta> \<sigma> G]
  have *:"(subst_pairs_multiset (\<sigma> \<circ>\<^sub>s \<eta>) G, subst_pairs_multiset \<eta> G') \<in> multiset_pair_reduction_step\<^sup>*" using subcom by auto
  have "trivially_unifiable (subst_pairs_multiset \<eta> G')" unfolding gdefs using un[unfolded syntactically_unifiable_def] by auto 
  with multiset_reachability_reduction_solution show ?thesis using * by simp
qed

(* Next, consider multiset narrowing on multisets of ordinary terms and multisets of equational terms *)

definition "multiset_narrowing_reachable_from_to S G \<longleftrightarrow>  (\<exists>\<sigma> \<eta> S'. multiset_narrowing_derivation S S' \<sigma> \<and> 
    subst_term_multiset \<eta> S' = G)"

lemma multiset_narrowing_based_reachable_sufficient_condition_pre:
  assumes nd:"multiset_narrowing_derivation S S' \<sigma>"
    and "subst_term_multiset \<eta> S' = G"
  shows "(subst_term_multiset (\<sigma> \<circ>\<^sub>s \<eta>) S, G) \<in> (multiset_reduction_step)\<^sup>*"
  using assms by (metis multiset_narrowing_reduction subst_closed_multiset_reduction subst_term_multiset_compose)

proposition multiset_narrowing_based_reachable_sufficient_condition:
  assumes "multiset_narrowing_reachable_from_to S G"
  shows "\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*"
  using assms by (metis multiset_narrowing_reduction multiset_narrowing_reachable_from_to_def subst_closed_multiset_reduction subst_term_multiset_compose)
                                                               
proposition multiset_narrowing_based_infeasibility_condition:
  assumes "\<not> multiset_narrowing_reachable_from_to S G"
  shows "\<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence "(\<exists>\<theta>. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)" by auto
  then obtain \<theta> where norm\<theta>:"normal_subst R \<theta>" and \<theta>SG:"(subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*" by auto
  from \<theta>SG have *:"(subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*" by blast
  from assms have "(\<forall>\<sigma> \<eta> S'. multiset_narrowing_derivation S S' \<sigma> \<longrightarrow> 
    subst_term_multiset \<eta> S' \<noteq> G)" unfolding multiset_narrowing_reachable_from_to_def by auto
  let ?V = "vars_term_set (set_mset S) \<union> subst_domain \<theta>"
  have fnV:"finite ?V" unfolding vars_term_set_def
    by (simp add: finite_subst_domain)
  from lifting_lemma_for_multiset_narrowing
  have "\<exists>\<tau> \<tau>' S'. multiset_narrowing_derivation S S' \<tau> \<and> G = subst_term_multiset \<tau>' S' \<and>
     normal_subst R \<tau>' \<and> \<tau> \<circ>\<^sub>s \<tau>' |s ?V = \<theta> |s ?V" 
    using "*" fnV using norm\<theta> by auto
  then show False
    using \<open>\<forall>\<sigma> \<eta> S'. multiset_narrowing_derivation S S' \<sigma> \<longrightarrow> subst_term_multiset \<eta> S' \<noteq> G\<close> by blast
qed

(* The following lemma is the weak completeness of multiset narrowing
  w.r.t. the multiset reachability problem *)

lemma multiset_narrowing_based_reachability_weak_completeness:
 "multiset_narrowing_reachable_from_to S G \<longrightarrow> (\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
 "\<not> multiset_narrowing_reachable_from_to S G \<longrightarrow> \<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
proof -
  show "multiset_narrowing_reachable_from_to S G \<longrightarrow> (\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
    by (simp add: multiset_narrowing_based_reachable_sufficient_condition)
  show "\<not> multiset_narrowing_reachable_from_to S G \<longrightarrow> \<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
    by (simp add: multiset_narrowing_based_infeasibility_condition)
qed

lemma multiset_reduction_single_reachability: assumes wn: "WN (rstep R)"
    and cr: "CR (multiset_reduction_step)"
    and funas_uv:"funas_rule (u, v) \<subseteq> F"
    and nf:"v \<in> NF (rstep R)"
    and ersteps:"({#Fun \<doteq> [u, v]#}, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)\<^sup>+"
  shows "((u, v) \<in> (rstep R)\<^sup>*)"
proof -
  from ersteps obtain n where step:"({#Fun \<doteq> [u, v]#}, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)^^n" and n1:"n \<ge> 1" 
    by (metis add_mset_eq_single less_one list.simps(3) relpow_0_E rtrancl_imp_relpow term.inject(2) trancl_into_rtrancl verit_comp_simplify1(3))
  then show ?thesis using funas_uv nf
  proof(induct n arbitrary:u v)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    with step obtain U where uvU:"({#Fun \<doteq> [u, v]#}, U) \<in> (multiset_reduction_step)" and 
      UG:"(U, {#Fun (\<top>) []#}) \<in> (multiset_reduction_step)^^n" by (meson relpow_Suc_D2)
    from uvU obtain s p rl \<sigma> where s:"s = Fun \<doteq> [u, v]" and U:"U = {#replace_at s p ((snd rl) \<cdot> \<sigma>)#}" and rl:"rl \<in> R" 
      and pfun:"p \<in> poss s" and sp:"s|_ p = (fst rl) \<cdot> \<sigma>" 
      by (smt (verit) add_mset_eq_single insert_DiffM mul_reduction_correspondence multiset_reduction_step_posE union_is_single)
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
        then show ?case using fun_poss_imp_poss less_2_cases numeral_2_eq_2 by fastforce
      next
        case (2 x p)
        then show ?case by (metis less_2_cases nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
      next
        case (3 x p)
        then show ?case by (metis less_2_cases nth_Cons_0 numeral_2_eq_2)
      qed
      then obtain q r where qpos:"(q \<in> poss u \<and> p = 0 # q) \<or> (r \<in> poss v \<and> p = 1 # r)" (is "?A \<or> ?B") by auto
      hence qp:"(q \<in> poss u \<and> p = 0 # q)" using Suc(5) by (metis NF_instance NF_rstep_subterm One_nat_def 
            lhs_notin_NF_rstep nth_Cons_0 nth_Cons_Suc prod.collapse rl s sp subt_at.simps(2) subt_at_imp_supteq')
      hence *:"replace_at s p ((snd rl) \<cdot> \<sigma>) = Fun \<doteq> [(replace_at u q ((snd rl) \<cdot> \<sigma>)), v]"  using s by auto
      hence "U = {#Fun \<doteq> [(replace_at u q ((snd rl) \<cdot> \<sigma>)), v]#}" using U by auto
      moreover have "funas_rule (replace_at u q ((snd rl) \<cdot> \<sigma>), v) \<subseteq> F" using funas_uv wf_F_subst ordinary unfolding funas_defs
        by auto (metis Suc.prems(3) qp ctxt_supt_id fst_conv funas_rule_def funas_term_ctxt_apply le_sup_iff subsetD,
              metis Suc.prems(3) UnI2 funas_rule_def in_mono snd_eqD)
      moreover have "(replace_at u q ((snd rl) \<cdot> \<sigma>), v) \<in> (rstep R)\<^sup>*" using Suc(1) UG 
        by (metis One_nat_def Suc.prems(2) Suc.prems(4) calculation(1) calculation(2) le_SucE list.simps(3) 
            nat.inject relpow_0_E single_eq_add_mset term.inject(2))
      ultimately show ?thesis using uvU
        by (metis converse_rtrancl_into_rtrancl ctxt_supt_id poss_us prod.collapse qp rl rstepI sp)
    qed
  qed
qed

lemma infeasibility_using_multiset_narrowing: assumes wf_S:"wf_equational_term_mset S"
  and "\<not> (\<exists>\<sigma> S'. multiset_narrowing_derivation S S' \<sigma> \<and> (\<forall> s \<in># S'. s = Fun (\<top>) []))"
shows "\<not> (\<exists>\<theta> T. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> S, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))"
proof(rule ccontr)
  assume asm:"\<not>?thesis"
  hence "\<exists>\<theta> T. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> S, T) \<in> multiset_reduction_step\<^sup>* \<and> (\<forall> t \<in>#  T. t = Fun (\<top>) [])" by auto
  then obtain \<theta> T  where norm\<theta>:"normal_subst R \<theta>" and relsteps:"(subst_term_multiset \<theta> S, T) \<in> multiset_reduction_step\<^sup>*" 
    and eqsat:"\<forall> t \<in># T. t = Fun (\<top>) []"  by auto
  let ?V = "vars_term_set (set_mset S) \<union> subst_domain \<theta>"
  have "finite (vars_term_set (set_mset S))" unfolding vars_term_set_def by simp
  moreover have "finite (subst_domain \<theta>)" using finite_subst_domain by simp
  ultimately have fV:"finite ?V" by simp
  have "wf_equational_term_mset T" unfolding wf_equational_term_mset_def[unfolded wf_equational_term_def] 
    using eqsat by auto
  define U where U:"U = subst_term_multiset \<theta> S" 
  have wf_U:"wf_equational_term_mset U" using wf_eq_mset_subst_inv by (simp add: U wf_S)
  have reltran:"(U, T) \<in> multiset_reduction_step\<^sup>*" using relsteps by (simp add: U)
  from lifting_lemma_for_multiset_narrowing_for_equational_terms [OF norm\<theta> wf_S U, of ?V T ]
  have "\<exists>\<sigma> \<theta>' S'. multiset_narrowing_derivation S S' \<sigma> \<and> subst_term_multiset \<theta>' S' = T \<and> 
    normal_subst R \<theta>' \<and> wf_equational_term_mset S'" using asm fV reltran by blast
  then obtain \<theta>' S' where cond:"\<exists>\<sigma>. multiset_narrowing_derivation S S' \<sigma>" and sub:"subst_term_multiset \<theta>' S' = T" and "normal_subst R \<theta>'"
    and T:"\<forall> t \<in># T. t = Fun (\<top>) []" and wfS':"wf_equational_term_mset S'" using eqsat by blast
  from T have *:"\<forall>t \<in># T. wf_equational_term t" unfolding wf_equational_term_def by auto
  from sub[unfolded subst_term_multiset_def]
  have *:"{#t \<cdot> \<theta>'. t \<in># S'#} = T" by auto
  have "(\<forall>u v \<theta>. Fun \<doteq> [u, v] \<cdot> \<theta> \<noteq> Fun (\<top>) [])" using wf_eq_subst by simp
  from wfS'[unfolded wf_equational_term_mset_def[unfolded wf_equational_term_def]]
  have "\<forall>t\<in>#S'. t = Fun \<top> []" using * using wf_eq_subst using eqsat by fastforce
  then show False using assms cond by auto
qed

lemma rstep_single_eq_reduction_step_eq: assumes uv:"(u::('f, 'v)term, v::('f, 'v)term) \<in> (rstep R')\<^sup>*"
  shows "(\<exists>T. ({#Fun \<doteq> [u, v]#}, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))"
proof -
  from uv show ?thesis
  proof(induct rule: converse_rtrancl_induct)
    case base
    then show ?case using multiset_red_refl 
      by (meson add_mset_eq_single insert_DiffM r_into_rtrancl)
  next
    case (step P Q)
    from step(3) obtain T' where T:"({#Fun \<doteq> [Q, v]#}, T') \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T'. t = Fun \<top> [])" by auto
    from step(1) obtain C rl \<sigma> where rl:"rl \<in> R'" and P:"P = C\<langle>(fst rl) \<cdot> \<sigma>\<rangle>" and Q:"Q = C\<langle>(snd rl) \<cdot> \<sigma>\<rangle>" by auto
    let ?F = "\<lambda> q T. ({#Fun \<doteq> [(fst q)\<cdot> \<sigma>, (snd q)\<cdot> \<sigma>]#}, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])"
    have "is_Fun (fst rl)" using wf[unfolded wf_trs_def] rl R' by (metis Un_iff eq_fst_iff is_FunI)
    hence hf:"hole_pos C \<in> fun_poss P" using P 
      by (metis hole_pos_poss is_VarE is_VarI poss_is_Fun_fun_poss subst_apply_eq_Var subt_at_hole_pos)
    let ?p = "0 # hole_pos C"
    let ?S = "{# Fun \<doteq> [P, v] #}"
    let ?s = "Fun \<doteq> [P, v]"
    let ?rl = rl
    let ?\<sigma> = \<sigma>
    let ?T = "(?S - {#?s#}) + {#replace_at ?s  ?p ((snd ?rl) \<cdot> ?\<sigma>)#}"
    have sp\<sigma>:"?s |_ ?p = (fst ?rl) \<cdot> ?\<sigma>" using P by auto
    have rlR:"rl \<in> R" using R' rl by fastforce
    have pps:"?p \<in> poss ?s" using hf using fun_poss_imp_poss by auto
    have "(?S, ?T) \<in> multiset_reduction_step_pos" 
    proof - 
      have "?s \<in># {#Fun \<doteq> [P, v]#}" by simp
      moreover have "?rl \<in> R" using R' rl by fastforce
      moreover have "?p \<in> poss ?s" using hf pps by blast
      moreover have "?s |_ ?p = fst ?rl \<cdot> ?\<sigma>" using sp\<sigma> by auto
      ultimately show ?thesis by blast
    qed
    hence st_step:"(?S, ?T) \<in> multiset_reduction_step" using mul_reduction_correspondence 
      by (metis rlR multiset_reduction_stepI pps replace_at_ident rstepI sp\<sigma> surjective_pairing union_single_eq_member) 
    have "replace_at (Fun \<doteq> [P, v])  ?p ((snd rl) \<cdot> \<sigma>) = (Fun \<doteq> [Q, v])" using Q by (auto simp add: P)
    hence "?T = {#Fun \<doteq> [Q, v]#}"by fastforce
    hence *:"({#Fun \<doteq> [P, v]#}, {#Fun \<doteq> [Q, v]#}) \<in> multiset_reduction_step" 
      using st_step by simp
    then show ?case using T trans_reachable_cond_red_step by blast
  qed
qed

lemma rstep_multiset_reduction_step_eq: fixes C::"(('f, 'v) term \<times> ('f, 'v) term) list"
  assumes funas_A:"funas_trs (set C) \<subseteq> F"
    and "\<forall>u v. (u, v) \<in> set C \<longrightarrow> ((u, v) \<in> (rstep R)\<^sup>* \<and> v \<in> NF(rstep R))"
  shows "(\<exists>T. ({#Fun \<doteq> [u, v]. (u, v) \<in># mset C#}, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t \<in># T. t = Fun (\<top>) []))" using assms
proof(induct C)
  case Nil
  then show ?case by auto
next
  case (Cons pair C)
  hence ftC:"funas_trs (set C) \<subseteq> F" unfolding funas_trs_def funas_rule_def by auto
  from Cons have *:"\<forall>u v. (u, v) \<in> set C \<longrightarrow> ((u, v) \<in> (rstep R)\<^sup>* \<and> v \<in> NF(rstep R))" by auto
  obtain u v where pair:"pair = (u, v)" by (meson surj_pair)
  have funas_u:"funas_term u \<subseteq> F" by (metis Cons.prems(1) lhs_wf list.set_intros(1) pair)
  have funas_v:"funas_term v \<subseteq> F" by (metis Cons.prems(1) list.set_intros(1) pair rhs_wf)
  have uvR:"(u, v) \<in> (rstep R)\<^sup>*" using Cons by (simp add: pair)
  hence uv:"(u, v) \<in> (rstep R')\<^sup>*" using funas_rstep_R' funas_u funas_v uvR by (simp add: funas_defs(2))
  obtain T where **:"({#Fun \<doteq> [u, v]. (u, v) \<in># mset C#}, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" 
    using Cons * ftC by auto
  have "v \<in> NF(rstep R)" using Cons pair by auto
  hence v:"v \<in> NF(rstep R')" using normRR' by (metis NF_iff_no_step R' Un_iff rstep_union)
  hence uvv:"(u, v) \<in> (rstep R')\<^sup>* \<and> v \<in> NF(rstep R')" using uv v by auto
  from rstep_single_eq_reduction_step_eq
  obtain T' where ***:"({#Fun \<doteq> [u, v]#}, T') \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T'. t = Fun \<top> [])" using uv v by blast
  have multiset_step_ctxt1:"({#Fun \<doteq> [u, v]#} + {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset C#},   
    T'+ {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset C#}) \<in> (multiset_reduction_step)\<^sup>*" 
    using *** multiset_red_add by blast
  have multiset_step_ctxt2:"(T'+ {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset C#}, T' + T) \<in> (multiset_reduction_step)\<^sup>*" using multiset_red_add ** add.commute by metis
  show ?case by (auto split:prod.splits, rule exI[of _ "T' + T"], insert ** *** pair addFunT[of T' T] 
        multiset_step_ctxt1 multiset_step_ctxt2, fastforce)
qed                                                                                        

lemma rstep_multiset_reduction_equiv:
  assumes funas_A:"funas_trs (set A) \<subseteq> F"
    and cstep_A:"(\<forall>u v. ((u, v) \<in> set A) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*))"
    and wn: "WN (rstep R)"
    and cr: "CR (rstep R)"
    and norm\<tau>: "normal_subst R \<tau>"
    and sti:"\<forall> (u, v) \<in> set A. strongly_irreducible_term R v"
  shows "\<exists>T. (subst_term_multiset \<tau> (convert_equations_into_term_multiset A), T) \<in> (multiset_reduction_step)\<^sup>*
          \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])" using assms
proof(induct A)
  case Nil
  then show ?case by auto
next
  case (Cons pair U)
  obtain u v where pair:"pair = (u, v)" using surjective_pairing by blast
  from funas_A have funU:"funas_trs (set U) \<subseteq> F" unfolding funas_trs_def funas_rule_def 
    using Cons unfolding funas_defs by auto
  have rstep\<tau>:"\<forall>s t. ((s, t) \<in> set ((u, v) # U)) \<longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" using Cons pair by fastforce
  have ft\<tau>:"funas_trs (set (subst_equations_list \<tau> ((u, v) # U))) \<subseteq> F" 
    unfolding subst_equations_list_def[unfolded subst_equation_def] funas_trs_def funas_rule_def 
    using wf_F_subst Cons(2) pair lhs_wf rhs_wf funas_A funU by (auto, smt (verit, ccfv_SIG) insertCI lhs_wf subsetD, 
        smt (verit, best) insertCI rhs_wf subsetD, blast, smt (verit) rhs_wf subsetD)
  have sruv:"\<forall>(s, t) \<in> set ((u, v) # U). strongly_irreducible_term R t" using pair Cons by fastforce
  then show ?case
  proof(auto split:prod.splits, goal_cases)
    case (1 x1 x2)
    have pair:"x1 = u \<and> x2 = v" using 1 pair by force
    have *:"\<forall>s t. (s, t) \<in> set (subst_equations_list \<tau> ((u, v) # U)) \<longrightarrow> (s, t) \<in> (rstep R)\<^sup>*" 
      using rstep\<tau> unfolding subst_equations_list_def[unfolded subst_equation_def] by auto 
    have nfcond:"\<forall>(s, t) \<in> set (subst_equations_list \<tau> ((u, v) # U)). t \<in> NF (rstep R)" using rstep\<tau> norm\<tau> sruv
      unfolding subst_equations_list_def[unfolded subst_equation_def] strongly_irreducible_term_def by auto
    from rstep_multiset_reduction_step_eq[of "subst_equations_list \<tau> ((u, v) # U)"]
    obtain T where **:"(({#Fun \<doteq> [u, v]. (u, v) \<in># mset (subst_equations_list \<tau> ((u, v) # U)) #}, T) \<in> 
      (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))" using * ft\<tau> nfcond by (metis case_prodD)
    have equiv:"{#t \<cdot> \<tau>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset U#}#} =
        {#Fun \<doteq> [u, v]. (u, v) \<in># {#(fst p \<cdot> \<tau>, snd p \<cdot> \<tau>). p \<in># mset U#}#}"
    proof -
      have "{#t \<cdot> \<tau>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset U#}#} = {#Fun \<doteq> [u \<cdot> \<tau>, v \<cdot> \<tau>]. (u, v) \<in># mset U#}"
      proof -
        have "{#t \<cdot> \<tau>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset U#}#} = {#(Fun \<doteq> [u, v]) \<cdot> \<tau>. (u, v) \<in># mset U#}" 
          using subst_Fun_mset_equiv by auto
        also have "... = {#(Fun \<doteq> [u \<cdot> \<tau>, v \<cdot> \<tau>]). (u, v) \<in># mset U#}" by auto
        ultimately show ?thesis by auto
      qed
      then show ?thesis by (smt (verit, best) case_prod_conv comp_apply multiset.map_comp multiset.map_cong0 prod.collapse)
    qed     
    show ?case  unfolding subst_term_multiset_def subst_equations_list_def using ** pair 
      by (simp add:subst_equations_list_def subst_equation_def, insert equiv, auto) 
  qed
qed

lemma multiset_narrowing_based_infeasibility: assumes wn:"WN (rstep R)"
  and cr:"CR (rstep R)"
  and funas_C:"funas_trs (set C) \<subseteq> F"
  and sti:"\<forall> (u, v) \<in> set C. strongly_irreducible_term R v"
shows "\<not> multiset_narrowing_reaches_to_success C \<Longrightarrow> infeasibility C" 
proof -
  assume "\<not> multiset_narrowing_reaches_to_success C"
  hence ncs:"(\<not> (\<exists>\<sigma> S'. multiset_narrowing_derivation (convert_equations_into_term_multiset C) S' \<sigma> \<and> 
    (\<forall> s \<in># S'. s = Fun (\<top>) [])))" unfolding multiset_narrowing_reaches_to_success_def by simp
  from convert_equations_into_rule_list_sound[OF funas_C]
  have wfC:"wf_equational_term_mset (convert_equations_into_term_multiset C)" by auto
  from infeasibility_using_multiset_narrowing[OF wfC ncs]
  have *:"\<not> (\<exists>\<theta> T V. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> (convert_equations_into_term_multiset C), T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))" by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "\<not> funas_trs (set C) \<subseteq> F \<or> (\<exists>\<tau>. (\<forall>u v. ((u, v) \<in> set C) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*)))" 
      unfolding infeasibility_def by auto
    with funas_C have "(\<exists>\<tau>. (\<forall>u v. ((u, v) \<in> set C) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*)))" by auto
    then obtain \<tau> where \<tau>:"(\<forall>u v. ((u, v) \<in> set C) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*))" by auto
    from WN_obtains_normalizable_subst[OF wn]
    have norm\<tau>:"normalizable_subst R \<tau>" by auto
    from obtains_normalized_subst[OF norm\<tau>]
    obtain \<tau>' where norm\<tau>':"normal_subst R \<tau>'" and subst_r:"(\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*)" by auto
    have uvC:"(\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>*)"
    proof -
      { fix u v
        assume asm:"(u, v) \<in> set C"
        from * have **:"(u \<cdot> \<tau>', v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using subst_r 
          by (smt (verit, ccfv_threshold) \<tau> asm meetI meet_imp_conversion subset_iff substs_rsteps)
        from * have uv\<tau>':"(u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using subst_r 
          by (meson ** conversionI' conversion_trans term_subst_rsteps transD)
        from sti[unfolded strongly_irreducible_term_def]
        have "v \<cdot> \<tau>' \<in> NF (rstep R)" using asm norm\<tau>' by auto
        hence "(u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using cr uv\<tau>'
          by (meson CR_NF_conv normalizability_E)
      } then show ?thesis by auto
    qed
    from rstep_multiset_reduction_equiv[OF funas_C uvC wn cr norm\<tau>' sti]
    have **:"\<exists> T. (subst_term_multiset  \<tau>' (convert_equations_into_term_multiset C), T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" by auto
    then obtain T where ***:"(subst_term_multiset  \<tau>' (convert_equations_into_term_multiset C), T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" by auto
    have "(\<exists>\<theta> T V. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> (convert_equations_into_term_multiset C), T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))"
      by (rule exI[of _ \<tau>'], rule exI[of _ T], insert * *** norm\<tau>', auto)
    then show False using * by auto
  qed
qed

lemma multiset_narrowing_based_reachable: assumes wn:"WN (rstep R)"
  and cr:"CR (rstep R)"
  and funas_C:"funas_trs (set C) \<subseteq> F"
  and sti:"\<forall> (u, v) \<in> set C. strongly_irreducible_term R v"
shows "multiset_narrowing_reaches_to_success C \<Longrightarrow> reachability C"
proof -
  assume "multiset_narrowing_reaches_to_success C"
  hence "R_unifiable C" by (metis R_unifiable_def emptyE funas_C multiset_narrowing_based_R_unifiable multiset_narrowing_reaches_to_success_def)
  then obtain \<tau> where *:"(\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" unfolding R_unifiable_def by auto
  from WN_obtains_normalizable_subst[OF wn]
  have norm\<tau>:"normalizable_subst R \<tau>" by auto
  from obtains_normalized_subst[OF norm\<tau>]
  obtain \<tau>' where norm\<tau>':"normal_subst R \<tau>'" and subst_r:"(\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*)" by auto
  have "(\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>*)"
  proof -
    { fix u v
      assume asm:"(u, v) \<in> set C"
      from * have **:"(u \<cdot> \<tau>', v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using subst_r 
        by (metis (no_types, lifting) asm conversionI' conversion_inv conversion_rtrancl rtrancl.simps substs_rsteps)
      from * have uv\<tau>':"(u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using subst_r 
        by (meson ** conversionI' conversion_trans term_subst_rsteps transD)
      from sti[unfolded strongly_irreducible_term_def]
      have "v \<cdot> \<tau>' \<in> NF (rstep R)" using asm norm\<tau>' by auto
      hence "(u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using cr uv\<tau>'
        by (meson CR_NF_conv normalizability_E)
    } then show ?thesis by auto
  qed
  then show ?thesis unfolding reachability_def by auto
qed

lemma complete_rstep_mulrstep_correspondence: assumes comp: "complete (rstep R)"
  shows  "complete (multiset_reduction_step)"
proof -
  from comp have sn:"SN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: complete_on_def, insert comp, auto)
  from sn have sn_mul:"SN (multiset_reduction_step)" 
    by (simp add: SN_R_imp_SN_multiset_reduction_step)
  from cr sn_mul have "CR (multiset_reduction_step)"
    by (simp add: CR_correspondence sn)
  then show ?thesis using sn_mul
    by (simp add: complete_on_def)
qed

lemma mulr_closed_addition: assumes A1B1:"(A1, B1) \<in> (multiset_reduction_step)\<^sup>*"
    and A2B2:"(A2, B2) \<in> (multiset_reduction_step)\<^sup>*"
  shows "(A1 + A2, B1 + B2) \<in> (multiset_reduction_step)\<^sup>*" using assms
proof -
  from A1B1 have "(A1 + A2, B1 + A2) \<in> multiset_reduction_step\<^sup>*" 
    by (meson multiset_narrowing.multiset_red_add multiset_narrowing_axioms)
  moreover have "(B1 + A2, B1 + B2) \<in> multiset_reduction_step\<^sup>*"
    by (metis A2B2 add.commute multiset_red_add)
  ultimately show ?thesis by auto
qed

lemma mulr_subst_normal_subst_equiv: assumes comp: "complete (rstep R)"
  and subst: "(\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
  and G:"G \<in> NF (multiset_reduction_step)"
shows  "(\<exists>\<theta>'. normal_subst R \<theta>' \<and> (subst_term_multiset \<theta>' S, G) \<in> (multiset_reduction_step)\<^sup>*)"
proof -
  from comp have sn:"SN (rstep R)" and cr:"CR (rstep R)" by (simp add: complete_on_def, insert comp, auto)
  from comp have comp_mult:"complete (multiset_reduction_step)" using complete_rstep_mulrstep_correspondence by simp
  from comp_mult have cr_mul:"CR (multiset_reduction_step)" and sn_mul:"SN (multiset_reduction_step)"
    by (simp add: complete_on_def, insert comp_mult, auto) 
  from subst obtain \<theta> where *:"(subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*" by auto
  from SN_obtains_normalizable_subst[OF sn]
  have norm\<theta>:"normalizable_subst R \<theta>" by auto
  from obtains_normalized_subst[OF norm\<theta>]
  obtain \<theta>' where norm\<tau>':"normal_subst R \<theta>'" and subst_r:"(\<forall>x. (\<theta> x, \<theta>' x) \<in> (rstep R)\<^sup>*)" by auto
  have t\<theta>\<theta>':"\<forall>t. (t \<cdot> \<theta>, t \<cdot> \<theta>') \<in> (rstep R)\<^sup>*" using subst_r using substs_rsteps by blast
  hence "(subst_term_multiset \<theta> S, subst_term_multiset \<theta>' S) \<in> (multiset_reduction_step)\<^sup>*"
  proof -
    let ?size = "size (subst_term_multiset \<theta> S)"
    have *:"subst_term_multiset \<theta> S = {# (t \<cdot> \<theta>). t \<in># S #}" unfolding subst_term_multiset_def by auto
    have **:"subst_term_multiset \<theta>' S = {# (t \<cdot> \<theta>'). t \<in># S #}" unfolding subst_term_multiset_def by simp
    have St\<theta>\<theta>':"\<forall>t \<in># S. ({# t \<cdot> \<theta> #}, {# t \<cdot> \<theta>' #}) \<in> (multiset_reduction_step)\<^sup>*" using t\<theta>\<theta>' rm_correspondence
      by (auto, metis add_mset_remove_trivial union_single_eq_member)
    moreover have "({# (t \<cdot> \<theta>). t \<in># S #}, {# (t \<cdot> \<theta>'). t \<in># S #}) \<in> (multiset_reduction_step)\<^sup>*"
    proof(induct "?size" arbitrary:S)
      case 0
      then show ?case using * 
        by (simp add: subst_term_multiset_def)
    next
      case (Suc x)
      then obtain u where u:"u \<in># S" by fastforce
      let ?S = "S - {#u#}"
      have u\<theta>\<theta>':"({# u \<cdot> \<theta> #}, {# u \<cdot> \<theta>' #}) \<in> (multiset_reduction_step)\<^sup>*" using St\<theta>\<theta>' u 
        by (metis add_mset_add_single add_mset_remove_trivial rm_correspondence t\<theta>\<theta>' union_single_eq_member)
      have "size ?S = size S - 1" using u 
        by (simp add: size_Diff_singleton)
      hence "({#t \<cdot> \<theta>. t \<in># ?S#}, {#t \<cdot> \<theta>'. t \<in># ?S#}) \<in> multiset_reduction_step\<^sup>*"
        using Suc by (simp add: subst_term_multiset_def)
      moreover have "({#t \<cdot> \<theta>. t \<in># ?S#} + {# u \<cdot> \<theta> #}, {#t \<cdot> \<theta>'. t \<in># ?S#} + {# u \<cdot> \<theta>' #}) \<in> multiset_reduction_step\<^sup>*"
        using mulr_closed_addition calculation u\<theta>\<theta>' by blast
      then show ?case using * ** u 
        by (auto, metis (no_types, lifting) image_mset_add_mset insert_DiffM)
    qed
    then show ?thesis using G comp_mult by (simp add: * **)
  qed
  then show ?thesis using *
    by (metis G NF_not_suc cr_mul norm\<tau>' normalizability_E sn_mul the_NF the_NF_steps)
qed

(*  Strong completeness of multiset narrowing w.r.t. ordinary reachability analysis,
    assuming that a semi-complete rewrite system R is given with the strongly irreducibility condition *)

theorem multiset_narrowing_based_reachability: assumes semi_comp:"semi_complete (rstep R)"
  and funas_C:"funas_trs (set C) \<subseteq> F"
  and sti:"\<forall> (u, v) \<in> set C. strongly_irreducible_term R v"
shows "multiset_narrowing_reaches_to_success C \<Longrightarrow> reachability C"
  "\<not> multiset_narrowing_reaches_to_success C \<Longrightarrow> infeasibility C"
proof -
  from semi_comp have wn:"WN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: semi_complete_on_def, insert semi_comp, auto)
  show "multiset_narrowing_reaches_to_success C \<Longrightarrow> reachability C" 
    using assms cr multiset_narrowing_based_reachable reachability_def wn by blast
  show "\<not> multiset_narrowing_reaches_to_success C \<Longrightarrow> infeasibility C"
    using assms by (simp add: cr multiset_narrowing_based_infeasibility wn)
qed

(* The following theorem is the strong completeness of multiset narrowing
  w.r.t. multiset reachability analysis, assuming that a complete R is given and the goal G
  is in normal form w.r.t. the multiset_reduction_step *)

lemma multiset_narrowing_based_non_reachability_strong_completeness: 
  assumes comp: "complete (rstep R)"
    and G:"G \<in> NF multiset_reduction_step"
  shows "\<not> multiset_narrowing_reachable_from_to S G \<Longrightarrow> \<not> (\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
proof -
  have "\<not> multiset_narrowing_reachable_from_to S G \<Longrightarrow> \<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
    by (simp add: multiset_narrowing_based_infeasibility_condition)
  then show "\<not> multiset_narrowing_reachable_from_to S G \<Longrightarrow> \<not> (\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
    using mulr_subst_normal_subst_equiv comp G by blast
qed

theorem multiset_narrowing_based_reachability_strong_completeness: 
  assumes comp: "complete (rstep R)"
    and G:"G \<in> NF multiset_reduction_step"
  shows "multiset_narrowing_reachable_from_to S G \<Longrightarrow> (\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
        "\<not> multiset_narrowing_reachable_from_to S G \<Longrightarrow> \<not> (\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
proof -
  show "multiset_narrowing_reachable_from_to S G \<Longrightarrow> (\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
    by (simp add: multiset_narrowing_based_reachable_sufficient_condition)
  have "\<not> multiset_narrowing_reachable_from_to S G \<Longrightarrow> \<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
    by (simp add: multiset_narrowing_based_infeasibility_condition)
  then show "\<not> multiset_narrowing_reachable_from_to S G \<Longrightarrow> \<not> (\<exists>\<theta>. (subst_term_multiset \<theta> S, G) \<in> (multiset_reduction_step)\<^sup>*)"
    using mulr_subst_normal_subst_equiv comp G by blast
qed

end
end