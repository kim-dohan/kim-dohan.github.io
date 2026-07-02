(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Formalization of equational narrowing based reachability\<close>

theory Equational_Narrowing_Reachability
  imports
    Equational_Narrowing
begin

locale equational_narrowing_reachability = equational_narrowing R DOTEQ TOP R' F D x
  for R::"('f, 'v:: infinite) trs" 
    and DOTEQ :: 'f ("\<doteq>")
    and TOP :: "'f" ("\<top>") 
    and R' :: "('f, 'v:: infinite) trs" 
    and F :: "'f sig" 
    and D :: "'f sig"
    and x :: 'v
begin

(* First consider  narrowing based reachability without using equational terms. 
  If a narrowing derivation reaches the target state, then a solution of the reachability problem exists. 
  No CR or SN or WN of R is required. *)

lemma narrowing_based_reachable_single: 
  assumes nar:"(s, t, \<sigma>) \<in> narrowing_step"
  shows "(s \<cdot> \<sigma>, t) \<in> rstep R"
proof -
  from nar obtain rl \<omega> p where t':"t = (replace_at s p (snd rl)) \<cdot> \<sigma>" and \<omega>rl:"\<omega> \<bullet> rl \<in> R"
    and disj:"(vars_term s \<inter> vars_rule rl = {})" and p:"p \<in> fun_poss s" and mgu:"mgu (s |_ p) (fst rl) = Some \<sigma>" by auto
  from t' have t:"t = replace_at (s \<cdot> \<sigma>) p (snd rl \<cdot> \<sigma>)" using p 
    by (simp add: ctxt_of_pos_term_subst fun_poss_imp_poss)
  let ?C = "ctxt_of_pos_term p (s \<cdot> \<sigma>)"
  from mgu have "(s |_ p) \<cdot> \<sigma> = fst rl \<cdot> \<sigma>" using subst_apply_term_eq_subst_apply_term_if_mgu by auto
  then show ?thesis using rstep.intros[of "fst rl" "snd rl" R "s \<cdot> \<sigma>" ?C "\<sigma>" t] 
  by (smt (verit) \<omega>rl fun_poss_imp_poss p perm_rstep_conv poss_imp_subst_poss prod.exhaust_sel 
    replace_at_ident rstep_ctxt rstep_subst subset_iff subset_rstep subt_at_subst t)
qed

lemma narrowing_based_reachable': 
  assumes nar:"narrowing_derivation s t \<sigma>"
  shows "(s \<cdot> \<sigma>, t) \<in> (rstep R)\<^sup>*"
proof -
  from nar obtain n where "narrowing_derivation_num s t \<sigma> n" unfolding narrowing_derivation_def 
      narrowing_derivation_num_def by auto
  then show ?thesis
  proof(induct n arbitrary: t \<sigma>)
    case 0
    then show ?case by (metis n0_narrowing_derivation_num rtrancl.simps subst.cop_nil)
  next
    case (Suc n)
    from \<open>narrowing_derivation_num s t \<sigma> (Suc n)\<close>
    have "(\<exists>f \<tau>. f 0 = s \<and> f (Suc n) = t \<and> 
      (\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> narrowing_step) \<and> (\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< Suc n])))"
      unfolding narrowing_derivation_num_def by auto
    then obtain f \<tau> where f0:"f 0 = s" and fsucn:"f (Suc n) = t" and 
      relchain:"\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> narrowing_step" 
      and \<sigma>:"(\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (Suc n)]))" by auto
    let ?\<tau> = "compose (map (\<lambda>i. (\<tau> i)) [0 ..< n])"
    let ?\<sigma> = "if n = 0 then Var else ?\<tau>"
    let ?f = "\<lambda>i. (if i \<le> n then f i else undefined)"
    from relchain obtain u where u:"f n = u" by simp
    from relchain have nchain:"\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> narrowing_step" by simp
    have "(\<exists>f \<tau>. f 0 = s \<and> f n = u \<and> (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> narrowing_step))"
      by (rule exI[of _ "?f"] rule exI[of _ "?\<sigma>"], insert u f0 nchain, auto)
    moreover have "narrowing_derivation_num s u ?\<sigma> n" unfolding narrowing_derivation_num_def
      using u calculation f0 nchain by auto 
    ultimately have IH:"(s \<cdot> ?\<sigma>, u) \<in> (rstep R)\<^sup>*" using Suc(1) by auto
    have "(u, t, \<tau> n) \<in> narrowing_step" using relchain fsucn u by auto
    from narrowing_based_reachable_single[OF this] 
    have *:"(u \<cdot> (\<tau> n), t) \<in> (rstep R)" by auto
    have "\<sigma> = ?\<sigma> \<circ>\<^sub>s (\<tau> n)" using \<sigma> by auto  
    then show ?case using IH by (smt (verit, del_insts) * rstep_rtrancl_idemp rstep_subst 
      rtrancl.rtrancl_into_rtrancl subst_subst_compose)
  qed
qed

lemma narrowing_based_reachable: 
  assumes nar:"\<exists>\<sigma>. narrowing_derivation s (t \<cdot> \<sigma>) \<sigma>"
  shows "\<exists>\<theta>. (s \<cdot> \<theta> , t \<cdot> \<theta>) \<in> (rstep R)\<^sup>*"
proof -
  from nar obtain \<sigma> where nd:"narrowing_derivation s (t \<cdot> \<sigma>) \<sigma>" by auto
  from narrowing_based_reachable'[OF nd]
  have *:"(s \<cdot> \<sigma> , t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*" by auto
  then show ?thesis by (rule exI[of _ \<sigma>])
qed

(* A sufficient condition of satisfying the reachability problem *)

lemma narrowing_based_reachable_with_unification: 
  assumes nar:"\<exists>\<sigma>. narrowing_derivation s (t' \<cdot> \<sigma>) \<sigma> \<and> mgu (t' \<cdot> \<sigma>) (t \<cdot> \<sigma>) \<noteq> None"
  shows "\<exists>\<theta>. (s \<cdot> \<theta> , t \<cdot> \<theta>) \<in> (rstep R)\<^sup>*"
proof -
  from nar obtain \<sigma> \<delta> where nd:"narrowing_derivation s (t' \<cdot> \<sigma>) \<sigma>" and mgu:"mgu (t' \<cdot> \<sigma>) (t \<cdot> \<sigma>) = Some \<delta>" by auto
  from narrowing_based_reachable'[OF nd]
  have "(s \<cdot> \<sigma> , t' \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*" by auto
  moreover from mgu have "(t' \<cdot> \<sigma>) \<cdot> \<delta> = (t \<cdot> \<sigma>) \<cdot> \<delta>" 
    using subst_apply_term_eq_subst_apply_term_if_mgu by auto
  ultimately have *: "(s \<cdot> (\<sigma> \<circ>\<^sub>s \<delta>) , t \<cdot> (\<sigma> \<circ>\<^sub>s \<delta>)) \<in> (rstep R)\<^sup>*" 
    by (metis (mono_tags, lifting) rsteps_closed_subst subst_subst_compose)
  show ?thesis by (rule exI[of _ "(\<sigma> \<circ>\<^sub>s \<delta>)"], insert *, auto)
qed

(* Narrowing based reachability using equational terms. If a narrowing derivation reaches the target state, 
  then a solution of the reachability problem exists. *)

lemma equational_narrowing_based_reachability_pre: 
  assumes wf_S:"wf_equational_term S"
    and nd:"narrowing_derivation S (Fun \<top> []) \<sigma>"
  shows "(S \<cdot> \<sigma>, Fun \<top> []) \<in> (rstep R)\<^sup>*" using narrowing_based_reachable' nd wf_S by auto

lemma equational_narrowing_based_reachability': 
  assumes wf_S:"wf_equational_term S"
    and nd:"\<exists>\<sigma>. narrowing_derivation S (Fun \<top> []) \<sigma>"
  shows "\<exists>\<theta>. (S \<cdot> \<theta>, Fun \<top> []) \<in> (rstep R)\<^sup>*" using narrowing_based_reachable' nd wf_S by auto

lemma infeasibility_using_narrowing: assumes wf_S:"wf_equational_term S"
  and "\<not> (\<exists>\<sigma>. narrowing_derivation S (Fun \<top> []) \<sigma>)"
shows "\<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (S \<cdot> \<theta>, Fun \<top> []) \<in> (rstep R)\<^sup>*)"
proof(rule ccontr)
  assume asm:"\<not>?thesis"
  then obtain \<theta> T  where norm\<theta>:"normal_subst R \<theta>" and relsteps:"(S \<cdot> \<theta>, T) \<in> (rstep R)\<^sup>*" and goal:"(T = Fun (\<top>) [])" by auto
  let ?V = "vars_term S \<union> subst_domain \<theta>"
  have "finite (vars_term S)" unfolding vars_term_set_def by simp
  moreover have "finite (subst_domain \<theta>)" using finite_subst_domain by auto 
  ultimately have fV:"finite ?V" by simp
  define U where U:"U = S \<cdot> \<theta>" 
  have wf_U:"wf_equational_term U" using U wf_S wf_eq_subst by blast
  have reltran:"(U, T) \<in> (rstep R)\<^sup>*" using relsteps by (simp add: U)
  from lifting_lemma_equational_terms [OF norm\<theta> wf_S U, of ?V T ]
  have "\<exists>\<sigma> \<theta>' S'. narrowing_derivation S S' \<sigma> \<and> T =  S' \<cdot> \<theta>' \<and> normal_subst R \<theta>' \<and> wf_equational_term S'" using asm fV reltran by blast
  then obtain \<sigma> \<theta>' S' where nar:"narrowing_derivation S S' \<sigma>" and T:"T =  S' \<cdot> \<theta>'" and norm\<theta>':"normal_subst R \<theta>'" 
    and wf_S':"wf_equational_term S'" by auto
  have "(\<forall>u v \<theta>. Fun \<doteq> [u, v] \<cdot> \<theta> \<noteq> Fun (\<top>) [])" using wf_eq_subst by simp
  from wf_S'[unfolded wf_equational_term_mset_def[unfolded wf_equational_term_def]]
  have "S'= Fun \<top> []" using wf_eq_subst using T goal wf_equational_term_def by fastforce
  then show False using asm goal using assms(2) nar by auto
qed

lemma equational_narrowing_based_infeasibility_using_normalized_subst_reachability_property: 
  assumes nsrp:"normalized_subst_reachability_property s t"
    and funas_C:"funas_rule (s, t) \<subseteq> F"
  shows "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> infeasible (s, t)" 
proof -
  assume "\<not> narrowing_derivation_reaches_to_success (s, t)"
  hence ncs:"\<not> (\<exists>\<sigma>. narrowing_derivation (Fun (\<doteq>) [s, t]) ( Fun (\<top>) []) \<sigma>) " unfolding narrowing_derivation_reaches_to_success_def by auto
  from convert_equation_into_term_sound[OF funas_C]
  have wfC:"wf_equational_term (Fun (\<doteq>) [s, t])" by auto
  from infeasibility_using_narrowing[OF wfC ncs]
  have *:"\<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun (\<doteq>) [s, t] \<cdot> \<theta>, Fun (\<top>) []) \<in> (rstep R)\<^sup>*)" by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "(\<not> funas_rule (s, t) \<subseteq> F \<or> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*))"
      unfolding infeasible_def by auto
    with funas_C have reach:"\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" by auto
    hence "\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R')\<^sup>*" using R' R_sig unfolding funas_defs 
      by (metis (no_types, lifting) Un_subset_iff fst_eqD funas_C funas_rstep_R' funas_rule_def snd_eqD wf_F_subst)
    then obtain \<tau> where "(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R')\<^sup>*" by auto
    with nsrp[unfolded normalized_subst_reachability_property_def] obtain \<tau>' where 
      \<tau>':"(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" and norm\<tau>':"normal_subst R \<tau>'" and "\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*" 
      by (metis (no_types, opaque_lifting) Int_iff R' Un_upper1 inf.orderE rstep_union rtrancl_mono)
    from rstep_reduction_step_eq
    have "\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun (\<top>) []) \<in> (rstep R)\<^sup>*" using \<tau>' norm\<tau>' funas_C by blast
    then show False using * by auto
  qed
qed

(* Sufficient condition for normalized_subst_reachability property *)

lemma normalized_subst_reachability_cond: assumes wn:"WN (rstep R)"
  and cr: "CR (rstep R)"
  and funas_C:"funas_rule (s, t) \<subseteq> F"
  and sti:"strongly_irreducible_term R t"
shows "normalized_subst_reachability_property s t" 
proof -
  { fix \<tau>
    assume asm:"(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
    from WN_obtains_normalizable_subst[OF wn]
    have norm\<tau>:"normalizable_subst R \<tau>" by auto
    from obtains_normalized_subst[OF norm\<tau>]
    obtain \<tau>' where norm\<tau>':"normal_subst R \<tau>'" and \<tau>\<tau>':"\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*" by auto
    have rstep\<tau>':"(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*"
    proof -
      have "(s \<cdot> \<tau>, s \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using \<tau>\<tau>' 
        by (simp add: substs_rsteps)
      moreover have "(t \<cdot> \<tau>, t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using \<tau>\<tau>'  
        by (simp add: substs_rsteps)
      moreover have "t \<cdot> \<tau>' \<in> NF (rstep R)" using sti[unfolded strongly_irreducible_term_def] norm\<tau>' by auto
      moreover have "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
        by (meson asm calculation(1) calculation(2) meetI meet_imp_conversion subset_eq transD trans_rtrancl)
      ultimately show "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using cr[unfolded CR_on_def]
        by (meson CR_NF_conv cr normalizability_E)
    qed
    hence "(\<exists> \<tau>'. normal_subst R \<tau>' \<and> (s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>* \<and> (\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*))" 
      using norm\<tau>' \<tau>\<tau>' rstep\<tau>' by auto
  } then show ?thesis unfolding normalized_subst_reachability_property_def by auto
qed

(* Equational narrowing-based infeasibility *)

lemma narrowing_based_infeasibility_implies_infeasibility: assumes wn:"WN (rstep R)"
  and cr: "CR (rstep R)"
  and funas_C:"funas_rule (s, t) \<subseteq> F"
  and sti:"strongly_irreducible_term R t"
shows "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> (\<not> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*))" 
proof -
  assume "\<not> narrowing_derivation_reaches_to_success (s, t)"
  hence ncs:"\<not> (\<exists>\<sigma>. narrowing_derivation (Fun (\<doteq>) [s, t]) ( Fun (\<top>) []) \<sigma>) " unfolding narrowing_derivation_reaches_to_success_def by auto
  from convert_equation_into_term_sound[OF funas_C]
  have wfC:"wf_equational_term (Fun (\<doteq>) [s, t])" by auto
  from infeasibility_using_narrowing[OF wfC ncs]
  have *:"\<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun (\<doteq>) [s, t] \<cdot> \<theta>, Fun (\<top>) []) \<in> (rstep R)\<^sup>*)" by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "(\<not> funas_rule (s, t) \<subseteq> F \<or> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*))"
      unfolding infeasible_def by auto
    with funas_C have reach:"\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" by auto
    from rstep_reduction_equiv[OF wn cr sti funas_C reach]
    have "\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun (\<top>) []) \<in> (rstep R)\<^sup>*" by auto
    then show False using * by auto
  qed
qed

(* No SN or WN required for the following theorem *)
theorem narrowing_based_infeasibility_implies_normalizable_infeasibility: assumes cr: "CR (rstep R)"
  and funas_C:"funas_rule (s, t) \<subseteq> F"
shows "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> normalizable_infeasibility (s, t)" 
proof -
  assume "\<not> narrowing_derivation_reaches_to_success (s, t)"
  hence ncs:"\<not> (\<exists>\<sigma>. narrowing_derivation (Fun (\<doteq>) [s, t]) ( Fun (\<top>) []) \<sigma>) " unfolding narrowing_derivation_reaches_to_success_def by auto
  from convert_equation_into_term_sound[OF funas_C]
  have wfC:"wf_equational_term (Fun (\<doteq>) [s, t])" by auto
  from infeasibility_using_narrowing[OF wfC ncs]
  have *:"\<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun (\<doteq>) [s, t] \<cdot> \<theta>, Fun (\<top>) []) \<in> (rstep R)\<^sup>*)" by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "(\<not> funas_rule (s, t) \<subseteq> F \<or> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>* \<and> normalizable_subst R \<tau>) )"
      unfolding normalizable_infeasibility_def by auto
    with funas_C have reach:"\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>* \<and> normalizable_subst R \<tau>" by auto
    from rstep_reduction_normalizable_equiv[OF cr reach]
    have "\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun (\<top>) []) \<in> (rstep R)\<^sup>*" by auto
    then show False using * by auto
  qed
qed

lemma narrowing_based_infeasibility_implies_infeasible: assumes "semi_complete (rstep R)" 
  and funas_C:"funas_rule (s, t) \<subseteq> F"
  and nd: "\<not> narrowing_derivation_reaches_to_success (s, t)"
shows "infeasible (s, t)" using assms narrowing_based_infeasibility_implies_normalizable_infeasibility 
  by (meson equational_narrowing.WN_obtains_normalizable_subst equational_narrowing_axioms infeasible_def normalizable_infeasibility_def semi_complete_on_def)

(* Equational narrowing-based reachable *)

lemma equational_narrowing_based_reachable:
  assumes wn: "WN (rstep R)"
    and cr: "CR (rstep R)"
    and nd:"\<exists>\<sigma>. narrowing_derivation (Fun \<doteq> [s, t]) (Fun \<top> []) \<sigma>"
    and funas_st:"funas_rule (s, t) \<subseteq> F"
    and sti:"strongly_irreducible_term R t"
  shows "\<exists>\<theta>. (s \<cdot> \<theta>, t \<cdot> \<theta>) \<in> (rstep R)\<^sup>*"
proof -
  have wf:"wf_equational_term (Fun \<doteq> [s, t])" unfolding wf_equational_term_def using funas_st D D_fresh 
      funas_defs(2) by fastforce+
  from equational_narrowing_based_reachability'[OF wf nd]
  obtain \<theta> where *: "(Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun \<top> []) \<in> (rstep R)\<^sup>+"
    by (auto, simp add: rtrancl_eq_or_trancl)
  hence fr':"funas_rule (s \<cdot> \<theta>, t \<cdot> \<theta>) \<subseteq> F" using funas_st unfolding funas_defs wf_F_subst 
    by (auto, (meson subsetD wf_F_subst)+) 
  from wn have norm\<theta>:"normalizable_subst R \<theta>"
    using WN_obtains_normalizable_subst by auto
  from obtains_normalized_subst[OF norm\<theta>]
  obtain \<theta>' where norm\<theta>':"normal_subst R \<theta>'" and \<theta>\<theta>':"(\<forall>x. (\<theta> x, \<theta>' x) \<in> (rstep R)\<^sup>*)" by auto
  have fr:"funas_rule (s \<cdot> \<theta>', t \<cdot> \<theta>') \<subseteq> F" using funas_st unfolding funas_defs wf_F_subst 
    by (auto, (meson subsetD wf_F_subst)+)
  from norm_subst_rstep_preserve[OF norm\<theta>' \<theta>\<theta>']
  have "(Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun \<doteq> [s \<cdot> \<theta>', t \<cdot> \<theta>']) \<in> (rstep R)\<^sup>*" using fr unfolding funas_defs by auto
  hence **:"(Fun \<doteq> [s \<cdot> \<theta>', t \<cdot> \<theta>'], Fun \<top> []) \<in> (rstep R)\<^sup>*" using * cr[unfolded CR_on_def]
    by (metis CR_NF_conv CR_imp_conversionIff_join NF_I cr iso_tuple_UNIV_I normalizability_E not_reducible_T 
        r_into_rtrancl trancl_rtrancl_absorb)
  have "t \<cdot> \<theta>' \<in> NF (rstep R)" using sti[unfolded strongly_irreducible_term_def] 
    using norm\<theta>' by auto 
  hence nt:"t \<cdot> \<theta>' \<in> NF (rstep R')" using R' NF_trs_mono[of R' R] by auto 
  from rstep_red_equiv[OF fr ** nt] 
  have "(s \<cdot> \<theta>', t \<cdot> \<theta>') \<in> (rstep R')\<^sup>*" using ** by auto
  hence "(s \<cdot> \<theta>', t \<cdot> \<theta>') \<in> (rstep R)\<^sup>*" using R' by (metis R' in_rtrancl_UnI rstep_union)
  then show ?thesis by (rule exI[of _ \<theta>'])
qed

(* Equational narrowing based reachability, providing a decision procedure  
   for strongly irreducible terms t *)

theorem narrowing_based_reachability: 
  assumes semi_comp:"semi_complete (rstep R)"
    and funas_C:"funas_rule (s, t) \<subseteq> F"
    and sti:"strongly_irreducible_term R t"
  shows "narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> reachable (s, t)"
    "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> infeasible (s, t)"
proof -
  from semi_comp have wn:"WN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: semi_complete_on_def, insert semi_comp, auto)
  show "narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> reachable (s, t)"
    by (simp add: cr funas_C equational_narrowing_based_reachable narrowing_derivation_reaches_to_success_def reachable_def sti wn)
  show "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> infeasible (s, t)"
    using narrowing_based_infeasibility_implies_infeasible[OF semi_comp funas_C] .
qed

end
end
