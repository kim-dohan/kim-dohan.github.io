(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Formalization of equational narrowing based E-unification\<close>

theory Equational_Narrowing_Unification
  imports
    Equational_Narrowing_Reachability
begin

locale equational_narrowing_unification = equational_narrowing_reachability R DOTEQ TOP R' F D x
  for R::"('f, 'v:: infinite) trs" 
    and DOTEQ :: 'f ("\<doteq>")
    and TOP :: "'f" ("\<top>") 
    and R' :: "('f, 'v:: infinite) trs" 
    and F :: "'f sig" 
    and D :: "'f sig"
    and x :: 'v
begin

lemma R_unifiable: assumes funas_uv:"funas_rule (u, v) \<subseteq> F"
  and fun_uv:"(Fun (\<doteq>) [u, v], Fun (\<top>) []) \<in> (rstep R)\<^sup>+" (* It needs at least one rewrite step *)
shows "(u, v) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" 
proof -
  let ?srule = "\<lambda>x. (Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
  have fr:"\<forall>x. funas_rule (?srule x) = {(\<doteq>, 2), (\<top>, 0)}" using D 
    unfolding funas_defs by (auto simp add: numeral_2_eq_2)
  have frD:"\<forall>x. funas_rule (?srule x) \<subseteq> D" using D 
    unfolding funas_defs by (auto simp add: numeral_2_eq_2)
  from fun_uv obtain n where n1:"n \<ge> 1" and fuv:"(Fun (\<doteq>) [u, v], Fun (\<top>) []) \<in> (rstep R)^^n"
    by (metis order_refl relpow_1 trancl_steps_relpow)
  then show ?thesis using funas_uv
  proof(induct n arbitrary:u v)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(4) have funas_u:"funas_term u \<subseteq> F" unfolding funas_defs by auto
    from Suc(4) have funas_v:"funas_term v \<subseteq> F" unfolding funas_defs by auto
    from Suc(3) obtain U where U1:"(Fun \<doteq> [u, v], U) \<in> rstep R" and U2:"(U, Fun (\<top>) []) \<in> (rstep R)^^ n"
      using Suc(2) by (meson relpow_Suc_E2)
    then show ?case
    proof(cases "Suc n = Suc 0")
      case True
      with Suc(3) have "(Fun \<doteq> [u, v], Fun \<top> []) \<in> rstep R" by simp
      then obtain C \<sigma> l r where lr:"(l, r) \<in> R" and lhs:"Fun \<doteq> [u, v] = C\<langle>l \<cdot> \<sigma>\<rangle>" and rhs:"Fun \<top> [] = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
      have rule_type:"(l, r) \<in> R' \<or> (\<exists>x. (l, r) = ?srule x)" using R' lr by fastforce
      hence frule_type:"funas_rule (l, r) \<subseteq> F \<or> (\<exists>x. (l, r) = ?srule x)" using R_sig 
        by (metis fst_conv funas_rule_def le_supI lhs_wf rhs_wf snd_conv)
      have fnlr:"\<not> funas_rule (l, r) \<subseteq> F"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence flr:"funas_rule (l, r) \<subseteq> F" using D D_fresh by auto
        from rhs have "funas_term  (C\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> D" using D by auto
        hence *:"funas_term (r \<cdot> \<sigma>) \<subseteq> D" by auto
        from flr have "funas_term r \<subseteq> F" unfolding funas_defs by auto
        hence **:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using wf_F_subst by simp
        have "C = Hole" using rhs by (metis nectxt_imp_supt_ctxt supt_const)
        hence "funas_term (r \<cdot> \<sigma>) \<noteq> {}" using rhs by auto 
        then show False using * ** D_fresh by auto
      qed
      hence **:"(\<exists>x. (l, r) = ?srule x)" using fr frule_type by auto
      hence "u = v" using lr lhs rhs by auto
      then show ?thesis by auto
    next
      case False
      hence UN:"U \<noteq> Fun (\<top>) []" using not_reducible_T U2 by (metis relpow_E2)
      have *:"(Fun \<doteq> [u, v], U) \<in> rstep R'"
      proof(rule ccontr)
        assume asm:"\<not> ?thesis"
        hence "(Fun \<doteq> [u, v], U) \<notin> rstep R'" by auto
        hence "\<exists>x. (Fun \<doteq> [u, v], U) \<in> rstep {?srule x}" using R' by (metis U1 Un_iff rstep_union)
        then obtain x where "(Fun \<doteq> [u, v], U) \<in> rstep {?srule x}" by auto
        then obtain C' \<sigma>' l' r' where l'r':"(l', r') \<in> {?srule x}" and fuv:"Fun \<doteq> [u, v] = C'\<langle>l' \<cdot> \<sigma>'\<rangle>" 
          and UC':"U = C'\<langle>r' \<cdot> \<sigma>'\<rangle>" by auto
        have "r' \<cdot> \<sigma>' =  Fun (\<top>) []" using l'r' by auto
        with UN UC' have NC':"C' \<noteq> Hole" by auto
        hence "l' \<cdot> \<sigma>' \<lhd> Fun \<doteq> [u, v]" using fuv by auto
        hence *:"l' \<cdot> \<sigma>' \<unlhd> u \<or> l' \<cdot> \<sigma>' \<unlhd> v" by auto
        have "(\<doteq>, 2) \<in> funas_term (l' \<cdot> \<sigma>')" using l'r' by auto
        then show False using funas_u funas_v D D_fresh *
          by (meson insert_disjoint(1) subset_iff supteq_imp_funas_term_subset) 
      qed         
      from funas_R_reachable_case[OF funas_u funas_v this]
      obtain u' v' where U:"U = (Fun \<doteq> [u', v'])" and uu'vv':"(u = u' \<or> v = v')" and fu':"funas_term u' \<subseteq> F" 
        and fv':"funas_term v' \<subseteq> F" using funas_u funas_v by blast
      have IH:"(u', v') \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using Suc n1 U2 fu' fv'
        by (metis (no_types, lifting) False One_nat_def U fst_conv funas_rule_def le_Suc_eq le_sup_iff snd_conv)
      show ?thesis using uu'vv'
      proof
        assume asm:"u = u'"
        hence vv':"(v, v') \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using U U1 asm fun_rstep_case1 * funas_u funas_v by blast
        then show ?thesis using IH asm by (meson conversion_inv conversion_trans transD)
      next
        assume asm:"v = v'"
        hence uu':"(u, u') \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*"  using fun_rstep_case2 U U1 * funas_u funas_v by blast
        then show ?thesis using IH asm by (meson conversion_trans transD)
      qed
    qed
  qed
qed

lemma narrowing_based_E_unif_infeasibility: 
  assumes ensrp:"E_unif_normalized_subst_reachability_property s t"
    and funas_C:"funas_rule (s, t) \<subseteq> F"
    and cr:"CR (rstep R)"
  shows "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> \<not> E_unifiable (s, t)" 
proof -
  assume "\<not> narrowing_derivation_reaches_to_success (s, t)"
  hence ncs:"\<not> (\<exists>\<sigma>. narrowing_derivation (Fun (\<doteq>) [s, t]) ( Fun (\<top>) []) \<sigma>) " unfolding narrowing_derivation_reaches_to_success_def by auto
  from convert_equation_into_term_sound[OF funas_C]
  have wfC:"wf_equational_term (Fun (\<doteq>) [s, t])" by auto
  from infeasibility_using_narrowing[OF wfC ncs]
  have *:"\<not> (\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun (\<doteq>) [s, t] \<cdot> \<theta>, Fun (\<top>) []) \<in> (rstep R)\<^sup>*)" by auto
  show ?thesis
  proof
    assume "E_unifiable (s, t)"
    hence "(\<not> funas_rule (s, t) \<subseteq> F \<or> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*))"
      unfolding E_unifiable_def by auto
    with funas_C have reach:"\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" by auto
    hence "\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using funas_C funas_rstep_R'_conv unfolding funas_defs 
      by (auto, meson wf_F_subst)
    then obtain \<tau> where "(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" by auto
    with ensrp[unfolded E_unif_normalized_subst_reachability_property_def] obtain \<tau>' where 
      \<tau>':"(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" and norm\<tau>':"normal_subst R \<tau>'" and "\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*" 
      by (metis (no_types, opaque_lifting) R' Un_upper1 conversion_mono rstep_union subsetD)
    from rstep_reduction_R_unif_normalized_equiv
    have "\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun (\<top>) []) \<in> (rstep R)\<^sup>*" using \<tau>' norm\<tau>' funas_C cr by blast
    then show False using * by auto
  qed
qed

(* Sufficient condition for E_unif_normalized_subst_reachability_property. Only WN is needed. *)

lemma E_unif_normalized_subst_reachability_cond: assumes wn:"WN (rstep R)"
  shows "E_unif_normalized_subst_reachability_property s t"
proof -
  { fix \<tau>
    assume asm:"(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
    from WN_obtains_normalizable_subst[OF wn]
    have norm\<tau>:"normalizable_subst R \<tau>" by auto
    from obtains_normalized_subst[OF norm\<tau>]
    obtain \<tau>' where norm\<tau>':"normal_subst R \<tau>'" and \<tau>\<tau>':"\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*" by auto
    have rstep\<tau>':"(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
    proof -
      have "(s \<cdot> \<tau>, s \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using \<tau>\<tau>' 
        by (simp add: conversionI' substs_rsteps)
      moreover have "(t \<cdot> \<tau>, t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using \<tau>\<tau>'  
        by (simp add: substs_rsteps)
      moreover have "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
        by (meson asm calculation(1) calculation(2) conversionI' conversion_inv conversion_trans transD)
      ultimately show ?thesis by auto
    qed
    hence "\<exists>\<tau>'. (normal_subst R \<tau>' \<and> (s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>* \<and> (\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*))" 
      using norm\<tau>' \<tau>\<tau>' by auto
  } then show ?thesis unfolding E_unif_normalized_subst_reachability_property_def by auto
qed

(* If a narrowing derivation reaches the 'success' state,then the solution of an E-unifiability problem exists. *)

lemma narrowing_based_E_unifiable:
  assumes funas_uv:"funas_rule (u, v) \<subseteq> F"
    and nd:"\<exists>\<sigma>. narrowing_derivation (Fun \<doteq> [u, v]) (Fun \<top> []) \<sigma>"
  shows "\<exists>\<theta>. (u \<cdot> \<theta>, v \<cdot> \<theta>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  let ?S = "Fun (\<doteq>) [u, v]"
  from funas_uv have "(\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v" using D D_fresh R_sig
    unfolding funas_defs by auto
  moreover from funas_uv  have "(\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v" using D D_fresh R_sig
    unfolding funas_defs by auto
  ultimately have wf_eq:"wf_equational_term ?S" unfolding wf_equational_term_def by auto
  from nd obtain \<sigma> where nar:"narrowing_derivation ?S (Fun (\<top>) []) \<sigma>" by auto
  from equational_narrowing_based_reachability'[of ?S]
  have "\<exists>\<theta>. (?S \<cdot> \<theta>, Fun (\<top>) []) \<in> (rstep R)\<^sup>*"
    by (simp add: nd wf_eq)
  then obtain \<theta> where *:"(?S \<cdot> \<theta>, Fun (\<top>) []) \<in> (rstep R)\<^sup>*" by auto
  have "?S \<cdot> \<theta> = Fun (\<doteq>) [u \<cdot> \<theta>, v \<cdot> \<theta>]" by auto
  have "funas_term (u \<cdot> \<theta>) \<subseteq> F" using wf_F_subst funas_uv unfolding funas_defs by simp
  moreover have "funas_term (v \<cdot> \<theta>) \<subseteq> F" using wf_F_subst funas_uv unfolding funas_defs by simp
  ultimately have fuv\<theta>:"funas_rule (u \<cdot> \<theta>, v \<cdot> \<theta>) \<subseteq> F" unfolding funas_defs by simp
  from R_unifiable[OF fuv\<theta>]
  have "(u \<cdot> \<theta>, v \<cdot> \<theta>) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using * by (simp add: rtrancl_eq_or_trancl)
  hence "(u \<cdot> \<theta>, v \<cdot> \<theta>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using R'
    by (metis (no_types, opaque_lifting) Un_upper1 conversion_mono in_mono rstep_mono)
  then show ?thesis by (rule exI[of _ \<theta>])
qed

(* Hullot's completeness of E-unification via narrowing, where R is viewed as a set of equations E. 
  If \<sigma> is an R-unifier of s and t, then a narrowing derivation provides a more general unifier than \<sigma> if it reaches to \<top>. *)

theorem narrowing_based_completeness_of_E_unification:
  assumes semi_comp:"semi_complete (rstep R)"
    and funas_st:"funas_rule (s, t) \<subseteq> F"
    and st_unif:"(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows nd:"\<exists>\<tau> \<theta>. narrowing_derivation (Fun \<doteq> [s, t]) (Fun \<top> []) \<tau> \<and> 
            (\<tau> \<circ>\<^sub>s \<theta>) |s (vars_term s \<union> vars_term t) =\<^sub>R \<sigma> |s (vars_term s \<union> vars_term t)"
proof -
  from semi_comp have wn:"WN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: semi_complete_on_def, insert semi_comp, auto)
  from wn have norm\<sigma>:"normalizable_subst R \<sigma>"
    using WN_obtains_normalizable_subst by auto
  from obtains_normalized_subst[OF norm\<sigma>]
  obtain \<sigma>' where norm\<sigma>':"normal_subst R \<sigma>'" and \<sigma>\<sigma>':"(\<forall>x. (\<sigma> x, \<sigma>' x) \<in> (rstep R)\<^sup>*)" by auto
  with st_unif have *:"(s \<cdot> \<sigma>', t \<cdot> \<sigma>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
    by (metis (no_types, opaque_lifting) all_ctxt_closed_rsteps all_ctxt_closed_subst_step converse_iff 
        conversionI' conversion_converse conversion_rtrancl r_r_into_trancl rtrancl_trancl_absorb)
  hence "(s \<cdot> \<sigma>', t \<cdot> \<sigma>') \<in> (rstep R)\<^sup>\<down>" using cr wn by (simp add: CR_imp_conversionIff_join)
  hence **:"(Fun \<doteq> [s \<cdot> \<sigma>', t \<cdot> \<sigma>'], Fun \<top> []) \<in> (rstep R)\<^sup>*"
    by (metis * cr fst_eqD funas_rule_def funas_st le_sup_iff rstep_reduction_step_R_unif_eq snd_eqD wf_F_subst)
  let ?S = "Fun \<doteq> [s, t]"
  have wf:"wf_equational_term ?S" using funas_st convert_equation_into_term_sound by force
  let ?V = "vars_term ?S \<union> subst_domain \<sigma>'"
  have varcond':"vars_term ?S \<union> subst_domain \<sigma>' \<subseteq> ?V" ..
  have fn:"finite ?V" by (simp add: finite_subst_domain)
  have ***:"(?S \<cdot> \<sigma>',  Fun \<top> []) \<in> (rstep R)\<^sup>*" using ** by auto
  have wf_eq:"wf_equational_term (Fun \<top> [])" unfolding wf_equational_term_def by auto
  have vacuous_subst:"\<forall>\<theta>. Fun \<top> [] = (Fun \<top> []) \<cdot> \<theta>" by auto
  from lifting_lemma_equational_terms[of \<sigma>' ?S "?S \<cdot> \<sigma>'" "?V" "Fun \<top> []"]
  have "\<exists>\<tau> \<theta> S'. narrowing_derivation (Fun \<doteq> [s, t]) S' \<tau> \<and> Fun \<top> [] = S' \<cdot> \<theta> \<and> wf_equational_term S' \<and>
       normal_subst R \<theta> \<and> \<tau> \<circ>\<^sub>s \<theta> |s (vars_term (Fun \<doteq> [s, t]) \<union> subst_domain \<sigma>') = \<sigma>' |s (vars_term (Fun \<doteq> [s, t]) \<union> subst_domain \<sigma>')" 
    using "***" fn local.wf norm\<sigma>' by fastforce
  then obtain S' where ob:"\<exists>\<tau> \<theta>. narrowing_derivation (Fun \<doteq> [s, t]) S' \<tau> \<and> Fun \<top> [] = S' \<cdot> \<theta> \<and> wf_equational_term S' \<and>
       normal_subst R \<theta> \<and> \<tau> \<circ>\<^sub>s \<theta> |s (vars_term (Fun \<doteq> [s, t]) \<union> subst_domain \<sigma>') = \<sigma>' |s (vars_term (Fun \<doteq> [s, t]) \<union> subst_domain \<sigma>')"
    by auto
  hence"S' = Fun \<top> []" using vacuous_subst using wf_equational_term_def by fastforce
  hence "\<exists>\<tau> \<theta>. narrowing_derivation ?S (Fun \<top> []) \<tau> \<and> (\<tau> \<circ>\<^sub>s \<theta>) |s ?V = \<sigma>' |s ?V" using ob wf wf_eq *** fn varcond' by auto
  then obtain \<tau> \<theta> where nd:"narrowing_derivation ?S (Fun \<top> []) \<tau>" and subst_cond:"(\<tau> \<circ>\<^sub>s \<theta>) |s ?V = \<sigma>' |s ?V" by auto
  let ?Vst = "(vars_term s \<union> vars_term t)"
  from subst_cond have subVst:"(\<tau> \<circ>\<^sub>s \<theta>) |s ?Vst = \<sigma>' |s ?Vst"
    by (auto, metis Un_Int_eq(1) subst_restrict_Int)
  have "\<forall>x. (\<sigma> x, \<sigma>' x) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using \<sigma>\<sigma>' by auto
  hence var_rest_cond:"(\<tau> \<circ>\<^sub>s \<theta>) |s ?Vst  =\<^sub>R \<sigma> |s ?Vst" using subVst
    by (smt (verit, ccfv_threshold) conversion_def conversion_inv in_subst_restrict 
        notin_subst_restrict rtrancl.simps subst_modulo_def)
  show ?thesis by (rule exI[of _ \<tau>], rule exI[of _ \<theta>], insert nd var_rest_cond, auto) 
qed

lemma narrowing_based_non_E_unifiability: 
  assumes semi_comp:"semi_complete (rstep R)"
    and funas_C:"funas_rule (s, t) \<subseteq> F"
  shows "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> \<not> E_unifiable (s, t)"
proof -
  from semi_comp have wn:"WN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: semi_complete_on_def, insert semi_comp, auto)
  then show "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> \<not> E_unifiable (s, t)"
    by (simp add: cr funas_C narrowing_based_E_unif_infeasibility E_unif_normalized_subst_reachability_cond wn)
qed

(* Narrowing based E-unifiability, providing a decision procedure of E-unifiability. 
  Here, (rstep R)\<^sup>\<leftrightarrow> is viewed as (rstep E)\<^sup>\<leftrightarrow> *)

theorem narrowing_based_E_unifiability: 
  assumes semi_comp:"semi_complete (rstep R)"
    and funas_C:"funas_rule (s, t) \<subseteq> F"
  shows "narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> E_unifiable (s, t)"
        "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> \<not> E_unifiable (s, t)"
proof -
  from semi_comp have wn:"WN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: semi_complete_on_def, insert semi_comp, auto)
  show "\<not> narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> \<not> E_unifiable (s, t)" 
    by (simp add: cr funas_C narrowing_based_E_unif_infeasibility E_unif_normalized_subst_reachability_cond wn)
  show "narrowing_derivation_reaches_to_success (s, t) \<Longrightarrow> E_unifiable (s, t)"
    by (simp add: E_unifiable_def funas_C narrowing_based_E_unifiable narrowing_derivation_reaches_to_success_def)
qed  

end
end
