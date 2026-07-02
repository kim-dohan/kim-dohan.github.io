(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Formalization of multiset narrowing based (multiset) E-unification and E-unifiability\<close>

theory Multiset_Narrowing_Unification
  imports
    Multiset_Narrowing_Reachability
begin

locale multiset_narrowing_unification =  multiset_narrowing_reachability R DOTEQ TOP R' F D x
  for R::"('f, 'v:: infinite) trs" 
    and DOTEQ :: 'f ("\<doteq>")
    and TOP :: "'f" ("\<top>") 
    and R' :: "('f, 'v:: infinite) trs" 
    and F :: "'f sig" 
    and D :: "'f sig"
    and x :: 'v
begin

lemma rstep_single_R_unifiability_step_eq: assumes cr: "CR (multiset_reduction_step)"
  and funas_uv: "funas_rule (u, v) \<subseteq> F"
  and  uv:"(u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(\<exists>T. ({#Fun \<doteq> [u, v]#}, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))" 
proof -
  from uv obtain n where "(u::('f, 'v)term, v::('f, 'v)term) \<in> ((rstep R)\<^sup>\<leftrightarrow>)^^n" by auto
  then show ?thesis
  proof(induct n arbitrary:u v)
    case 0
    then show ?case 
      by (metis multiset_red_refl insert_DiffM r_into_rtrancl relpow_0_E single_eq_add_mset)
  next
    case (Suc n)
    from Suc(2) obtain w where uw:"(u, w) \<in> (rstep R)\<^sup>\<leftrightarrow>" and wv:"(w, v) \<in> (rstep R)\<^sup>\<leftrightarrow> ^^ n"
      by (meson relpow_Suc_E2)
    from wv have vw:"(v, w) \<in> (rstep R)\<^sup>\<leftrightarrow> ^^ n" by (metis converseI converse_power symcl_converse)
    from uw obtain C rl \<sigma> where rl:"rl \<in> R" and uw:"(u = C\<langle>(fst rl) \<cdot> \<sigma>\<rangle> \<and> w = C\<langle>(snd rl) \<cdot> \<sigma>\<rangle>) \<or> 
      (w = C\<langle>(fst rl) \<cdot> \<sigma>\<rangle> \<and> u = C\<langle>(snd rl) \<cdot> \<sigma>\<rangle>)" by fastforce
    then obtain T where IH:"({#Fun \<doteq> [w, v]#}, T) \<in> multiset_reduction_step\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" using Suc(1) 
      using wv by blast
    from uw show ?case
    proof
      assume asm:"u = C\<langle>(fst rl) \<cdot> \<sigma>\<rangle> \<and> w = C\<langle>(snd rl) \<cdot> \<sigma>\<rangle>"
      have "is_Fun (fst rl)" using wf[unfolded wf_trs_def] rl
        by (metis is_Fun_Fun_conv prod.collapse)
      hence hf:"hole_pos C \<in> fun_poss u" 
        by (metis asm hole_pos_poss is_Var_def poss_is_Fun_fun_poss subst_apply_eq_Var subt_at_hole_pos)
      let ?p = "0 # hole_pos C"
      let ?S = "{# Fun \<doteq> [u, v] #}"
      let ?s = "Fun \<doteq> [u, v]"
      let ?rl = rl
      let ?\<sigma> = \<sigma>
      let ?T = "(?S - {#?s#}) + {#replace_at ?s  ?p ((snd ?rl) \<cdot> ?\<sigma>)#}"
      have sp\<sigma>:"?s |_ ?p = (fst ?rl) \<cdot> ?\<sigma>" using asm by auto
      have "rl \<in> R" using R' rl by fastforce
      have pfun:"?p \<in> poss ?s" using hf by (simp add: asm)
      have st_step:"(?S, ?T) \<in> multiset_reduction_step_pos" 
      proof - 
        have "?s \<in># {#Fun \<doteq> [u, v]#}" by simp
        moreover have "?rl \<in> R" using R' rl by fastforce
        moreover have "?p \<in> poss ?s" using hf pfun by fastforce
        moreover have "?s |_ ?p = fst ?rl \<cdot> ?\<sigma>" using sp\<sigma> by auto
        ultimately show ?thesis by blast
      qed
      hence st_step:"(?S, ?T) \<in> multiset_reduction_step" by (metis ctxt_supt_id multiset_reduction_stepI 
        pfun rl rstep_rule.intros rstep_rule_imp_rstep sp\<sigma> union_single_eq_member) 
      hence "replace_at (Fun \<doteq> [u, v])  ?p ((snd rl) \<cdot> \<sigma>) = (Fun \<doteq> [w, v])" using asm by auto
      hence "?T = {#Fun \<doteq> [w, v]#}"by fastforce
      hence *:"({#Fun \<doteq> [u, v]#}, {#Fun \<doteq> [w, v]#}) \<in> multiset_reduction_step" 
        using st_step by simp
      then show ?case using IH by (meson * converse_rtrancl_into_rtrancl)
    next
      assume asm:"w = C\<langle>(fst rl) \<cdot> \<sigma>\<rangle> \<and> u = C\<langle>(snd rl) \<cdot> \<sigma>\<rangle>"
      have "is_Fun (fst rl)" using wf[unfolded wf_trs_def] rl 
        by (metis is_Fun_Fun_conv prod.collapse)
      hence hf:"hole_pos C \<in> fun_poss w" 
        by (metis asm hole_pos_poss is_Var_def poss_is_Fun_fun_poss subst_apply_eq_Var subt_at_hole_pos)
      let ?p = "0 # hole_pos C"
      let ?S = "{# Fun \<doteq> [w, v] #}"
      let ?s = "Fun \<doteq> [w, v]"
      let ?rl = rl
      let ?\<sigma> = \<sigma>
      let ?T = "(?S - {#?s#}) + {#replace_at ?s  ?p ((snd ?rl) \<cdot> ?\<sigma>)#}"
      have sp\<sigma>:"?s |_ ?p = (fst ?rl) \<cdot> ?\<sigma>" using asm by auto
      have "rl \<in> R" using R' rl by fastforce
      have pfun:"?p \<in> poss ?s" using hf asm by auto
      have st_step:"(?S, ?T) \<in> multiset_reduction_step_pos" 
      proof - 
        have "?s \<in># {#Fun \<doteq> [w, v]#}" by simp
        moreover have "?rl \<in> R" using R' rl by fastforce
        moreover have "?p \<in> poss ?s" using hf pfun by blast
        moreover have "?s |_ ?p = fst ?rl \<cdot> ?\<sigma>" using sp\<sigma> by auto
        ultimately show ?thesis by blast
      qed
      hence "replace_at (Fun \<doteq> [w, v])  ?p ((snd rl) \<cdot> \<sigma>) = (Fun \<doteq> [u, v])" using asm by auto
      hence "?T = {#Fun \<doteq> [u, v]#}"by fastforce
      hence "({#Fun \<doteq> [w, v]#}, {#Fun \<doteq> [u, v]#}) \<in> multiset_reduction_step_pos" 
        using st_step by simp
      hence *:"({#Fun \<doteq> [w, v]#}, {#Fun \<doteq> [u, v]#}) \<in> multiset_reduction_step" 
        using st_step mul_reduction_correspondence  by (smt (verit, ccfv_threshold) ctxt_supt_id 
            multiset_narrowing.multiset_reduction_step.simps multiset_narrowing.multiset_reduction_step_pos.cases 
            multiset_narrowing_axioms rstep_rule.intros rstep_rule_imp_rstep)
      have "\<forall>t\<in>#T. t = Fun \<top> []" using IH ..
      hence "T \<in> NF (multiset_reduction_step)" using not_reducible_T_erstep by fastforce
      then show ?case using IH cr[unfolded CR_on_def] exI[of _ T]  * 
        by (auto, metis NF_join_imp_reach r_into_rtrancl)
    qed
  qed
qed

lemma rstep_single_eq_reduction_step_eq_normal: assumes cr_mul:"CR (multiset_reduction_step)"
  and uv:"(u::('f, 'v)term, v::('f, 'v)term) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(\<exists>T. ({#Fun \<doteq> [u, v]#}, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))"
proof -
  from uv obtain n where "(u::('f, 'v)term, v::('f, 'v)term) \<in> (rstep R')\<^sup>\<leftrightarrow>^^n" by auto
  then show ?thesis
  proof(induct n arbitrary: v)
    case 0
    hence "u = v" by auto
    then show ?case 
      by (metis add_mset_eq_single multi_member_split multiset_red_refl r_into_rtrancl)
  next
    case (Suc n)
    from Suc(2) obtain w where "(u, w) \<in> (rstep R')\<^sup>\<leftrightarrow> ^^ n" and wv:"(w, v) \<in> (rstep R')\<^sup>\<leftrightarrow>" by auto
    then obtain T where uwT:"({#Fun \<doteq> [u, w]#}, T) \<in> multiset_reduction_step\<^sup>*" and tT:"(\<forall>t\<in>#T. t = Fun \<top> [])" 
      using Suc(1) by auto
    hence TNF:"T \<in> NF (multiset_reduction_step)" using not_reducible_T by fastforce
    from wv have "(w, v) \<in> (rstep R') \<or> (v, w) \<in> (rstep R')" by auto
    then show ?case
    proof
      assume "(w, v) \<in> (rstep R')"
      hence wv:"(w, v) \<in> (rstep R)" using R' by blast
      hence "(Fun \<doteq> [u, w], Fun \<doteq> [u, v]) \<in> (rstep R)" using rstep.intros
      proof -
        let ?C = "ctxt_of_pos_term [1] (Fun \<doteq> [u, w])"
        from wv have "(?C\<langle>w\<rangle>, ?C\<langle>v\<rangle>) \<in> (rstep R)" by blast
        then show ?thesis by auto
      qed
      hence *:"({#Fun \<doteq> [u, w]#}, {#Fun \<doteq> [u, v]#}) \<in> multiset_reduction_step" by auto
      show ?thesis by (rule exI[of _T], insert cr_mul[unfolded CR_on_def] TNF uwT tT *,  
        meson NF_join_imp_reach cr_mul partially_localize_CR)
    next
      assume "(v, w) \<in> (rstep R')"
      hence vw:"(v, w) \<in> (rstep R)" using R' by blast
      hence "(Fun \<doteq> [u, v], Fun \<doteq> [u, w]) \<in> (rstep R)" using rstep.intros
      proof -
        let ?C = "ctxt_of_pos_term [1] (Fun \<doteq> [u, v])"
        from vw have "(?C\<langle>v\<rangle>, ?C\<langle>w\<rangle>) \<in> (rstep R)" by blast
        then show ?thesis by auto
      qed
      hence *:"({#Fun \<doteq> [u, v]#}, {#Fun \<doteq> [u, w]#}) \<in> multiset_reduction_step" by fastforce
      show ?thesis by (rule exI[of _T], insert cr_mul TNF uwT tT *, auto) 
    qed
  qed
qed

lemma rstep_multiset_R_unifiability_eq: assumes funas_A:"funas_trs (set A) \<subseteq> F"
    and "\<forall>u v. (u, v) \<in> set A \<longrightarrow> ((u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)"
    and cr:"CR (multiset_reduction_step)"
  shows "(\<exists>T. ({#Fun \<doteq> [u, v]. (u, v) \<in># mset A#}, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t \<in># T. t = Fun (\<top>) []))" using assms
proof(induct A)
  case Nil
  then show ?case by auto
next
  case (Cons pair A)
  hence ftA:"funas_trs (set A) \<subseteq> F" unfolding funas_trs_def funas_rule_def by auto
  from Cons have *:"\<forall>u v. (u, v) \<in> set A \<longrightarrow> ((u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" by auto
  obtain u v where pair:"pair = (u, v)" by (meson surj_pair)
  have funas_u:"funas_term u \<subseteq> F" by (metis Cons.prems(1) lhs_wf list.set_intros(1) pair)
  have funas_v:"funas_term v \<subseteq> F" by (metis Cons.prems(1) list.set_intros(1) pair rhs_wf)
  have uvR:"(u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using Cons by (simp add: pair)
  hence uv:"(u, v) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using funas_rstep_R' funas_u funas_v uvR 
    by (simp add: funas_defs(2) funas_rstep_R'_conv)
  obtain T where **:"({#Fun \<doteq> [u, v]. (u, v) \<in># mset A#}, T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" 
    using Cons * ftA by auto
  hence "(u, v) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using uv by auto
  hence uvv:"(u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using uv R' using uvR by blast
  have funas_uv: "funas_rule (u, v) \<subseteq> F" 
    by (simp add: funas_defs(2) funas_u funas_v)
  from rstep_single_R_unifiability_step_eq
  obtain T' where ***:"({#Fun \<doteq> [u, v]#}, T') \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T'. t = Fun \<top> [])" using uv cr funas_uv 
    using uvv by blast
  have multiset_step_ctxt1:"({#Fun \<doteq> [u, v]#} + {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset A#},   
    T'+ {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset A#}) \<in> (multiset_reduction_step)\<^sup>*" 
    using *** multiset_red_add by blast
  have multiset_step_ctxt2:"(T'+ {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset A#}, T' + T) \<in> (multiset_reduction_step)\<^sup>*" using multiset_red_add ** add.commute by metis
  show ?case by (auto split:prod.splits, rule exI[of _ "T' + T"], insert ** *** pair addFunT[of T' T] 
        multiset_step_ctxt1 multiset_step_ctxt2, fastforce)
qed          

lemma rstep_multiset_unifiability_equiv:
  assumes funas_A:"funas_trs (set A) \<subseteq> F"
    and cstep_A:"\<exists>\<tau>. (\<forall>u v. ((u, v) \<in> set A) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*))"
    and sn: "SN (rstep R)"
    and cr: "CR (multiset_reduction_step)"
  shows "\<exists>\<theta> T. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> (convert_equations_into_term_multiset A), T) \<in> (multiset_reduction_step)\<^sup>*
          \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])" using assms
proof(induct A)
  case Nil
  hence nVar:"normal_subst R Var" using wf[unfolded wf_trs_def] 
    by (simp add: empty_subst_normalized normal_subst_def) 
  show ?case unfolding subst_term_multiset_def
    by (rule exI[of _ Var], rule exI[of _ "convert_equations_into_term_multiset []"], insert nVar, auto)
next
  case (Cons pair U)
  obtain u v where pair:"pair = (u, v)" using surjective_pairing by blast
  from funas_A have funU:"funas_trs (set U) \<subseteq> F" unfolding funas_trs_def funas_rule_def 
    using Cons by (meson lhs_wf rhs_wf subsetD subset_insertI, simp add: funas_rule_def funas_trs_def) 
  have rstepU':"\<exists>\<tau>. (\<forall>s t. ((s, t) \<in> set ((u, v) # U)) \<longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" 
    using assms Cons pair by auto
  then obtain \<tau> where \<tau>:"\<forall>s t. ((s, t) \<in> set ((u, v) # U)) \<longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"  by auto
  from SN_obtains_normalizable_subst[OF sn]
  have norm\<tau>:"normalizable_subst R \<tau>" by auto
  from obtains_normalized_subst[OF norm\<tau>]
  obtain \<tau>' where norm\<tau>':"normal_subst R \<tau>'" and subst_r:"(\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*)" by auto
  hence \<tau>\<tau>':"(\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" by auto
  have rstep\<tau>':"\<forall>s t. ((s, t) \<in> set ((u, v) # U)) \<longrightarrow> (s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
  proof(intro impI allI)
    fix s t
    assume asm:"(s, t) \<in> set ((u, v) # U)"
    hence *:"(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using \<tau> asm by auto
    have "(s \<cdot> \<tau>, s \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using \<tau>\<tau>' substs_rsteps subst_r by blast
    moreover have "(t \<cdot> \<tau>, t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using \<tau>\<tau>' 
      by (simp add: conversionI' subst_r substs_rsteps)
    ultimately show "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
      by (meson "*" conversion_inv conversion_trans transD)
  qed
  have ft\<tau>':"funas_trs (set (subst_equations_list \<tau>' ((u, v) # U))) \<subseteq> F" 
    unfolding subst_equations_list_def[unfolded subst_equation_def] funas_trs_def funas_rule_def 
    using wf_F_subst Cons(2) pair lhs_wf rhs_wf funas_A funU by (auto, smt (verit, ccfv_SIG) insertCI lhs_wf subsetD, 
        smt (verit, best) insertCI rhs_wf subsetD, blast, smt (verit) rhs_wf subsetD)
  show ?case
  proof(rule exI[of _ \<tau>'], auto split:prod.splits, goal_cases)
    case (1 x1 x2)
    then show ?case 
      using norm\<tau>' by auto
  next
    case (2 x1 x2)
    have pair:"x1 = u \<and> x2 = v" using 2 pair by force
    have *:"\<forall>s t. (s, t) \<in> set (subst_equations_list \<tau>' ((u, v) # U)) \<longrightarrow> (s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
      using rstep\<tau>' unfolding subst_equations_list_def[unfolded subst_equation_def] by auto 
    from rstep_multiset_R_unifiability_eq[of "subst_equations_list \<tau>' ((u, v) # U)"]
    obtain T where **:"(({#Fun \<doteq> [u, v]. (u, v) \<in># mset (subst_equations_list \<tau>' ((u, v) # U)) #}, T) \<in> 
      (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))" using * ft\<tau>' cr by auto
    have equiv:"{#t \<cdot> \<tau>'. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset U#}#} =
        {#Fun \<doteq> [u, v]. (u, v) \<in># {#(fst p \<cdot> \<tau>', snd p \<cdot> \<tau>'). p \<in># mset U#}#}"
    proof -
      have "{#t \<cdot> \<tau>'. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset U#}#} = {#Fun \<doteq> [u \<cdot> \<tau>', v \<cdot> \<tau>']. (u, v) \<in># mset U#}"
      proof -
        have "{#t \<cdot> \<tau>'. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset U#}#} = {#(Fun \<doteq> [u, v]) \<cdot> \<tau>'. (u, v) \<in># mset U#}" 
          using subst_Fun_mset_equiv by auto
        also have "... = {#(Fun \<doteq> [u \<cdot> \<tau>', v \<cdot> \<tau>']). (u, v) \<in># mset U#}" by auto
        ultimately show ?thesis by auto
      qed
      then show ?thesis by (smt (verit, best) case_prod_conv comp_apply multiset.map_comp multiset.map_cong0 prod.collapse)
    qed     
    show ?case  unfolding subst_term_multiset_def subst_equations_list_def using ** pair 
      by (simp add:subst_equations_list_def subst_equation_def, insert equiv, auto) 
  qed
qed

lemma rstep_multiset_reduction_equiv_normal:
  assumes funas_A:"funas_trs (set A) \<subseteq> F"
    and cstep_A:"(\<forall>u v. ((u, v) \<in> set A) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*))"
    and sn: "SN (rstep R)"
    and cr: "CR (rstep R)"
    and norm\<tau>: "normal_subst R \<tau>"
  shows "\<exists>T. (subst_term_multiset \<tau> (convert_equations_into_term_multiset A), T) \<in> (multiset_reduction_step)\<^sup>*
          \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])" using assms
proof(induct A)
  case Nil
  then show ?case by auto
next
  case (Cons pair U)
  from sn have sn_mul:"SN (multiset_reduction_step)" 
    by (simp add: SN_R_imp_SN_multiset_reduction_step)
  from sn_mul cr have cr_mul:"CR (multiset_reduction_step)" 
    by (simp add: CR_correspondence sn)
  obtain u v where pair:"pair = (u, v)" using surjective_pairing by blast
  from funas_A have funU:"funas_trs (set U) \<subseteq> F" unfolding funas_trs_def funas_rule_def 
    using Cons unfolding funas_defs by auto
  have rstep\<tau>:"\<forall>s t. ((s, t) \<in> set ((u, v) # U)) \<longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using Cons pair by fastforce
  have ft\<tau>:"funas_trs (set (subst_equations_list \<tau> ((u, v) # U))) \<subseteq> F" 
    unfolding subst_equations_list_def[unfolded subst_equation_def] funas_trs_def funas_rule_def 
    using wf_F_subst Cons(2) pair lhs_wf rhs_wf funas_A funU by (auto, smt (verit, ccfv_SIG) insertCI lhs_wf subsetD, 
        smt (verit, best) insertCI rhs_wf subsetD, blast, smt (verit) rhs_wf subsetD)
  then show ?case
  proof(auto split:prod.splits, goal_cases)
   case (1 x1 x2)
    have pair:"x1 = u \<and> x2 = v" using 1 pair by force
    have *:"\<forall>s t. (s, t) \<in> set (subst_equations_list \<tau> ((u, v) # U)) \<longrightarrow> (s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
      using rstep\<tau> unfolding subst_equations_list_def[unfolded subst_equation_def] by auto 
    from rstep_multiset_R_unifiability_eq [of "subst_equations_list \<tau> ((u, v) # U)"]
    obtain T where **:"(({#Fun \<doteq> [u, v]. (u, v) \<in># mset (subst_equations_list \<tau> ((u, v) # U)) #}, T) \<in> 
      (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))" using * ft\<tau> cr_mul by auto 
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
    show ?case unfolding subst_term_multiset_def subst_equations_list_def using ** pair 
      by (simp add:subst_equations_list_def subst_equation_def, insert equiv, auto) 
  qed
qed

lemma funas_term_pos_included:assumes "p \<in> poss t"
  and "funas_term t \<subseteq> F"
shows "funas_term (t |_ p) \<subseteq> F" using assms
  by (meson fun_poss_imp_poss subset_trans subt_at_imp_supteq' supteq_imp_funas_term_subset)

lemma funas_mgu_F:assumes fun_s:"funas_term s \<subseteq> F"
  and fun_t:"funas_term t \<subseteq> F"
  and fun_u:"funas_term u \<subseteq> F"
shows "funas_term (u \<cdot> (the (mgu s t)::('v \<Rightarrow> ('f, 'v) Term.term))) \<subseteq> F" using assms wf_F_subst by auto

lemma mulr_single_correspondence:assumes LM:"(L, M) \<in> multiset_reduction_step"
  shows "\<exists>s t. s \<in># L \<and> (s, t) \<in> rstep R \<and> t \<in># M" using assms
proof -
  from LM obtain s t where *:"s \<in># L \<and> M = ((L - {#s#}) + {#t#}) \<and> (s, t) \<in> rstep R" by auto
  hence "t \<in># M" by simp
  then show ?thesis using * by auto
qed

lemma mulr_cor:assumes LM:"(L, M) \<in> (multiset_reduction_step)\<^sup>*"
  shows "\<forall> u. u \<in># L \<longrightarrow> (\<exists> u'. u' \<in># M \<and> (u, u') \<in> (rstep R)\<^sup>*)" 
proof -
  from LM obtain n where LMn:"(L, M) \<in> (multiset_reduction_step)^^n" by auto
  then show ?thesis
  proof(induct n arbitrary:M)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain U where LU:"(L, U) \<in> multiset_reduction_step ^^ n" and UM:"(U, M) \<in> multiset_reduction_step" by auto
    have "\<forall>u. u \<in># L \<longrightarrow> (\<exists>u'. u' \<in># U \<and> (u, u') \<in> (rstep R)\<^sup>*)" using Suc(1) LU by auto
    then obtain u' where *:"\<forall>u. u \<in># L \<longrightarrow> (u' u \<in># U \<and> (u, u' u) \<in> (rstep R)\<^sup>*)" by metis
    from UM obtain v w where vw:"v \<in># U \<and> M = ((U - {#v#}) + {#w#}) \<and> (v, w) \<in> rstep R" by auto
    hence "\<forall>u. u \<in># L \<longrightarrow> (\<exists>u'. u' \<in># M \<and> (u, u') \<in> (rstep R)\<^sup>*)"
    proof -
      { fix u
        assume "u \<in># L"
        hence u'u:"(u' u \<in># U \<and> (u, u' u) \<in> (rstep R)\<^sup>*)" using * by auto
        hence "(\<exists>u'. u' \<in># M \<and> (u, u') \<in> (rstep R)\<^sup>*)"
        proof(cases "u' u = v")
          case True
          hence "(u, w) \<in> (rstep R)\<^sup>*" using vw u'u by auto
          then show ?thesis using True vw diff_single_trivial by auto
        next
          case False
          hence "(u' u) \<in># M" using vw 
            by (auto, metis insert_DiffM insert_noteq_member u'u)
          then show ?thesis using False u'u by auto
        qed
      } then show ?thesis by auto
    qed
    then show ?case by auto
  qed
qed

lemma mulr_cor_rev:assumes LM:"(L, M) \<in> (multiset_reduction_step)\<^sup>*"
  shows "\<forall> u. u \<in># M \<longrightarrow> (\<exists> w. w \<in># L \<and> (w, u) \<in> (rstep R)\<^sup>*)"
proof -
  from LM obtain n where "(L, M) \<in> (multiset_reduction_step)^^n" by auto
  then show ?thesis
  proof(induct n arbitrary:L M)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain U where LU:"(L, U) \<in> multiset_reduction_step" and UM:"(U, M) \<in> multiset_reduction_step ^^ n"
      by (meson relpow_Suc_E2)
    have "\<forall>u. u \<in># M \<longrightarrow> (\<exists>w. w \<in># U \<and> (w, u) \<in> (rstep R)\<^sup>*)" using UM Suc(1) by auto
    then obtain w where IH:"\<forall>u. u \<in># M \<longrightarrow> (w u \<in># U \<and> (w u, u) \<in> (rstep R)\<^sup>*)" by metis
    from LU obtain v v' where vw:"v \<in># L \<and> U = ((L - {#v#}) + {#v'#}) \<and> (v, v') \<in> rstep R" by auto
    hence "\<forall> u. u \<in># M \<longrightarrow> (\<exists> w. w \<in># L \<and> (w, u) \<in> (rstep R)\<^sup>*)"
    proof -
      { fix u
        assume "u \<in># M"
        hence u'u:"(w u \<in># U \<and> (w u, u) \<in> (rstep R)\<^sup>*)" using IH by auto
        hence "(\<exists> w'. w' \<in># L \<and> (w', u) \<in> (rstep R)\<^sup>*)"
        proof(cases "w u \<in># L")
          case True
          then show ?thesis using vw
            by (meson converse_rtrancl_into_rtrancl u'u) 
        next
          case False
          hence "w u = v'" using vw by (auto, metis Multiset.diff_right_commute 
                diff_single_trivial diff_union_swap multi_drop_mem_not_eq u'u)
          then show ?thesis using u'u vw by auto
        qed
      } then show ?thesis by simp
    qed
    then show ?case by auto
  qed
qed

lemma not_nf_step_possible:assumes "u \<in># M \<and> \<not> u \<in> NF (rstep R)"
  shows "\<exists>N. (M, N)\<in> (multiset_reduction_step)" using assms 
  by (meson NF_I multiset_reduction_step.simps)

lemma some_nf_step_possible:assumes sn:"SN (rstep R)"
  and uM:"u \<in># M \<and> \<not> u \<in> NF (rstep R)"
  shows "\<exists>N u'. (M, N)\<in> (multiset_reduction_step)\<^sup>* \<and> u' \<in># N \<and> (u, u') \<in> (rstep R)\<^sup>* \<and> u' \<in> NF (rstep R)" using assms 
proof -
  obtain u' where u':"u' \<in> NF (rstep R) \<and> (u, u') \<in> (rstep R)\<^sup>* \<and> u' \<in> NF (rstep R)" using sn 
    by (meson SN_imp_WN UNIV_I WN_on_def normalizability_E)
  from rm_correspondence uM show ?thesis 
    by (metis (no_types, opaque_lifting) u' union_mset_add_mset_right union_single_eq_member)
qed

lemma reach_nf:assumes sn:"SN (rstep R)"
  shows  "\<forall>u. u \<in># M \<longrightarrow>(\<exists>N u'. (M, N) \<in> (multiset_reduction_step)\<^sup>* \<and> u' \<in># N \<and> (u, u') \<in> (rstep R)\<^sup>* \<and> u' \<in> NF (rstep R))"
  using some_nf_step_possible sn by auto

lemma no_step_possible:assumes LM:"\<not> (\<exists>M. (P, M) \<in> (multiset_reduction_step))"
  shows "\<forall> u. u \<in># P \<longrightarrow> u \<in> NF (rstep R)" using assms by auto

lemma multiset_narrowing_based_not_R_unifiable: 
  assumes comp:"complete (rstep R)"
    and funas_C:"funas_trs (set C) \<subseteq> F"
  shows "\<not> multiset_narrowing_reaches_to_success C \<Longrightarrow> (\<not> (\<exists>\<tau>. (\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)))" 
proof -
  from comp have sn:"SN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: complete_on_def, insert comp, auto)
  assume "\<not> multiset_narrowing_reaches_to_success C"
  hence ncs:"(\<not> (\<exists>\<sigma> S'. multiset_narrowing_derivation (convert_equations_into_term_multiset C) S' \<sigma> \<and> 
    (\<forall> s \<in># S'. s = Fun (\<top>) [])))" unfolding multiset_narrowing_reaches_to_success_def by simp
  from convert_equations_into_rule_list_sound[OF funas_C]
  have wfC:"wf_equational_term_mset (convert_equations_into_term_multiset C)" by auto
  from infeasibility_using_multiset_narrowing[OF wfC ncs]
  have *:"\<not> (\<exists>\<theta> T V. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> (convert_equations_into_term_multiset C), T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []) \<and>
      vars_term_set (set_mset (convert_equations_into_term_multiset C)) \<union> subst_domain \<theta> \<subseteq> V \<and> finite V)" by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "\<not> funas_trs (set C) \<subseteq> F \<or> (\<exists>\<tau>. (\<forall>u v. ((u, v) \<in> set C) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)))"
      unfolding R_unifiable_def by auto
    with funas_C have **:"(\<exists>\<tau>. (\<forall>u v. ((u, v) \<in> set C) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)))" by auto
    have cr:"CR (multiset_reduction_step)" using sn CR_correspondence by (simp add: cr)
    from rstep_multiset_unifiability_equiv[OF funas_C ** sn cr]
    have **:"\<exists>\<theta> T. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> (convert_equations_into_term_multiset C), T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" by auto
    then obtain \<theta> T where ***:"normal_subst R \<theta> \<and> (subst_term_multiset \<theta> (convert_equations_into_term_multiset C), T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" by auto
    let ?V = "vars_term_set (set_mset (convert_equations_into_term_multiset C)) \<union> subst_domain \<theta>"
    from *** have "normal_subst R \<theta>" by auto
    have "finite (subst_domain \<theta>)" using finite_subst_domain by simp
    hence fV:"finite ?V" 
      using ** infeasibility_using_multiset_narrowing[OF wfC ncs] by blast
    have "(\<exists>\<theta> T V. normal_subst R \<theta> \<and> (subst_term_multiset \<theta> (convert_equations_into_term_multiset C), T) \<in> (multiset_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []) \<and>
      vars_term_set (set_mset (convert_equations_into_term_multiset C)) \<union> subst_domain \<theta> \<subseteq> V \<and> finite V)"
      by (rule exI[of _ \<theta>], rule exI[of _ T], rule exI[of _ ?V], insert fV * ***, auto)
    then show False using * by auto
  qed
qed

lemma vars_preserve_convert_equations:"(vars_trs (set C)) = vars_term_set (set_mset (convert_equations_into_term_multiset C))"
proof(induct C)
  case Nil
  then show ?case unfolding vars_trs_def vars_term_set_def vars_rule_def by auto
next
  case (Cons pair C)
  have "vars_trs (set [pair]) = vars_term_set (set_mset (convert_equations_into_term_multiset [pair]))"
    unfolding vars_trs_def vars_term_set_def vars_rule_def by (auto split:prod.splits) 
  then show ?case unfolding vars_trs_def vars_term_set_def vars_rule_def using Cons by auto
qed

(* Completeness of E-unification w.r.t. multiset narrowing. If a (multi)set of equations has an R-unifier,
  then multiset narrowing can find a more general solution w.r.t. R *)

theorem multiset_narrowing_based_completeness_of_E_unification:
  assumes comp:"complete (rstep R)"
    and funas_C:"funas_trs (set C) \<subseteq> F"
    and R_unif:"(\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)"
  shows mnd:"\<exists>\<sigma> \<theta> S'. multiset_narrowing_derivation (convert_equations_into_term_multiset C) S' \<sigma> \<and> 
    (\<forall> s \<in># S'. s = Fun (\<top>) []) \<and> (\<sigma> \<circ>\<^sub>s \<theta>) |s (vars_trs (set C)) =\<^sub>R \<tau> |s (vars_trs (set C))"
proof -
  from comp have sn:"SN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: complete_on_def, insert comp, auto)
  have sn_mul:"SN (multiset_reduction_step)" using sn 
    by (simp add: SN_R_imp_SN_multiset_reduction_step)
  have cr_mul:"CR (multiset_reduction_step)" using cr sn_mul
    by (simp add: CR_correspondence sn)
  from sn have norm\<tau>:"normalizable_subst R \<tau>"
    using SN_obtains_normalizable_subst by auto
  from obtains_normalized_subst[OF norm\<tau>]
  obtain \<tau>' where norm\<tau>':"normal_subst R \<tau>'" and \<tau>\<tau>':"(\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*)" by auto
  with R_unif have *:"(\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)"
  proof -
    { fix u :: "('f, 'v) Term.term" and v :: "('f, 'v) Term.term"
      have "\<forall>t. (t \<cdot> \<tau>, t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*"
        by (simp add: \<tau>\<tau>' term_subst_rsteps)
      hence "(u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
        by (smt (z3) R_unif conversionI' conversion_inv conversion_rtrancl rtrancl.rtrancl_into_rtrancl) 
    } then show ?thesis by auto
  qed
  let ?C = "convert_equations_into_term_multiset C"
  have wf_C:"wf_equational_term_mset ?C"
    by (simp add: convert_equations_into_rule_list_sound funas_C)
  let ?C\<tau>'= "subst_term_multiset \<tau>' ?C"
  have C\<tau>':"?C\<tau>'= subst_term_multiset \<tau>' ?C" ..
  from R_unif have "(\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" using * by auto
  hence "(\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>', v \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<down>)"
    by (simp add: CR_imp_conversionIff_join cr)
  from rstep_multiset_reduction_equiv_normal[of C \<tau>']
  have reltran:"\<exists>U. (?C\<tau>', U) \<in> multiset_reduction_step\<^sup>* \<and> (\<forall> s \<in># U. s = Fun (\<top>) [])"
    using cr sn norm\<tau>' * funas_C by auto
  then obtain U where mstep:"(?C\<tau>', U) \<in> multiset_reduction_step\<^sup>*" and U:"(\<forall> s \<in># U. s = Fun (\<top>) [])" by auto
  let ?V = "vars_term_set (set_mset ?C) \<union> subst_domain \<tau>'"
  have "vars_term_set (set_mset ?C) \<union> subst_domain \<tau>' \<subseteq> ?V" ..
  have "finite (vars_term_set (set_mset ?C))" unfolding vars_term_set_def by simp
  moreover have "finite (subst_domain \<tau>')" using finite_subst_domain by simp
  ultimately have fV:"finite ?V" by simp
  from lifting_lemma_for_multiset_narrowing_for_equational_terms [OF norm\<tau>' wf_C C\<tau>', of ?V U ]
  have "\<exists>\<sigma> \<theta> S'. multiset_narrowing_derivation ?C S' \<sigma> \<and> subst_term_multiset \<theta> S' = U \<and> 
    normal_subst R \<theta> \<and> wf_equational_term_mset S' \<and> (\<sigma> \<circ>\<^sub>s \<theta>) |s ?V = \<tau>' |s ?V" using mstep fV by auto
  then obtain \<sigma> \<theta> S' where mnd:"multiset_narrowing_derivation ?C S' \<sigma>" and sub:"subst_term_multiset \<theta> S' = U"
    and "normal_subst R \<theta>" and wf:"wf_equational_term_mset S'" and sub\<sigma>\<theta>:"(\<sigma> \<circ>\<^sub>s \<theta>) |s ?V = \<tau>' |s ?V" by auto
  from wf[unfolded wf_equational_term_mset_def]
  have wfS':"\<forall> s \<in># S'. wf_equational_term s" by auto
  have no_subst_true:"\<forall>u v. (Fun \<doteq> [u, v]) \<cdot> \<theta> \<noteq> Fun (\<top>) []" by auto
  have wf_eq:"wf_equational_term (Fun \<top> [])" unfolding wf_equational_term_def by auto
  have vacuous_subst:"\<forall>\<theta>. Fun \<top> [] = (Fun \<top> []) \<cdot> \<theta>" by auto
  from sub have "{# (t \<cdot> \<theta>). t \<in># S' #} = U" using sub unfolding subst_term_multiset_def by auto
  hence *:"\<forall>s \<in># S'. s \<cdot> \<theta> = Fun (\<top>) []" using U by auto
  have sS':"(\<forall> s \<in># S'. s = Fun (\<top>) [])"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "\<exists>s. s \<in># S' \<and> (s \<noteq> Fun (\<top>) [])" by auto
    then obtain s where s:"s \<in># S'" and ns:"(s \<noteq> Fun (\<top>) [])" by auto
    from ns wfS' have "\<exists>u v. s = Fun \<doteq> [u, v] \<and> 
    (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v \<and> (\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v" 
      using s wf_equational_term_def by auto
    then obtain u v where "s = Fun \<doteq> [u, v]" by auto
    then show False using * s by auto
  qed
  have vars:"(vars_trs (set C)) = vars_term_set (set_mset (convert_equations_into_term_multiset C))" 
    using vars_preserve_convert_equations by auto
  hence vars:"(vars_trs (set C)) \<subseteq> ?V"  by auto
  have *:"(\<sigma> \<circ>\<^sub>s \<theta>) |s (vars_trs (set C)) = \<tau>' |s (vars_trs (set C))" using sub\<sigma>\<theta> 
    by (metis vars inf.absorb_iff2 subst_restrict_Int)
  have **:"(\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" using \<tau>\<tau>' by auto
  hence "\<tau>' |s vars_trs (set C) =\<^sub>R \<tau> |s vars_trs (set C)" unfolding subst_modulo_def subst_restrict_def 
    by (simp add: conversion_inv)
  hence "(\<sigma> \<circ>\<^sub>s \<theta>) |s (vars_trs (set C)) =\<^sub>R \<tau> |s (vars_trs (set C))" using * by auto 
  then show ?thesis using sS' mnd by auto
qed

(* Completeness of E-unifiability w.r.t. multiset narrowing, where R is viewed as a set of equations *)

theorem multiset_narrowing_based_R_unifiability: 
  assumes comp:"complete (rstep R)"
    and funas_C:"funas_trs (set C) \<subseteq> F"
  shows "multiset_narrowing_reaches_to_success C \<Longrightarrow> R_unifiable C" 
        "\<not> multiset_narrowing_reaches_to_success C \<Longrightarrow> \<not> R_unifiable C" 
proof -
  from comp have sn:"SN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: complete_on_def, insert comp, auto)
  from sn cr show "multiset_narrowing_reaches_to_success C \<Longrightarrow> R_unifiable C"
    by (metis R_unifiable_def ex_in_conv funas_C multiset_narrowing.multiset_narrowing_reaches_to_success_def multiset_narrowing_axioms multiset_narrowing_based_R_unifiable)
  show "\<not> multiset_narrowing_reaches_to_success C \<Longrightarrow> \<not> R_unifiable C" 
    by (simp add: comp funas_C multiset_narrowing_based_not_R_unifiable R_unifiable_def)
qed

end
end