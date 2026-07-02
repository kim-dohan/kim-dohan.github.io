(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Formalization of equational narrowing and lifting lemma\<close>

theory Equational_Narrowing
  imports
    Narrowing
begin

(* First, consider the unconditional narrowing *)
(* An equation s \<approx> t is converted into the equation-term \<doteq>(s, t). 
  Also, the rewrite rule "\<doteq>(x, x) \<longrightarrow> \<top>" is added to the rewrite system. *)

(*  Acknowledgement: Defining the following locale is done by René Thiemann *)
locale additional_narrowing_symbols =
  fixes DOTEQ :: 'f ("\<doteq>")
  and TOP :: "'f" ("\<top>")
begin
definition wf_equational_term where
  "wf_equational_term t \<longleftrightarrow> ((t = Fun \<top> []) \<or> (\<exists>u v. t = Fun \<doteq> [u::('f, 'v)term, v::('f, 'v)term] \<and> 
    (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v \<and> (\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v))"

definition wf_equational_term_mset::"('f, 'v::infinite) term multiset \<Rightarrow> bool" where
  "wf_equational_term_mset M \<longleftrightarrow> (\<forall>t \<in># M. wf_equational_term t)"
end

locale equational_narrowing = narrowing R + additional_narrowing_symbols DOTEQ TOP 
  for R::"('f, 'v:: infinite) trs"  
    and DOTEQ :: 'f ("\<doteq>")
    and TOP :: "'f" ("\<top>") +
  fixes R' :: "('f, 'v:: infinite) trs"
    and F :: "'f sig"
    and D :: "'f sig"
    and x :: 'v
  assumes  wf: "wf_trs R" (* Add the rewrite rule  x \<doteq> x \<longrightarrow> \<top> *)
    and R':"R = (R' \<union> {(Fun \<doteq> [Var x, Var x], Fun \<top> [])})"
    and R_sig: "funas_trs R' \<subseteq> F"
    and D:"D = {(\<doteq>, 2),(\<top>, 0)}" 
    (* The special symbols (\<doteq>, 2) and (\<top>, 0) should be distinct from the original signature *)
    and D_fresh:"D \<inter> F = {}"
    (* Any substitution does not introduce the special symbols \<doteq> and \<top> *)
    and wf_eq_subst:"\<forall>(\<theta>::('f, 'v:: infinite)subst) t::('f, 'v:: infinite)term. wf_equational_term t \<longrightarrow> wf_equational_term (t \<cdot> \<theta>)"
    and wf_F_subst:"\<forall>t (\<theta>::('f, 'v)subst). funas_term t \<subseteq> F \<longleftrightarrow> funas_term (t \<cdot> \<theta>) \<subseteq> F"
    (* Any substitution has a finite substitution domain because only finite terms are considered.*)
    and finite_subst_domain:"\<forall>s (\<theta>::('f, 'v)subst). (finite (vars_term (s \<cdot> \<theta>)) \<longrightarrow> (finite (vars_term s) \<and> finite (subst_domain \<theta>)))"    
begin

definition "narrowing_derivation_reaches_to_success eq \<longleftrightarrow> (\<exists>\<sigma>. narrowing_derivation (Fun \<doteq> [fst eq, snd eq]) (Fun \<top> []) \<sigma>)"

(* E is represented by R *)

definition "E_unifiable eq \<longleftrightarrow> (\<exists>\<tau>. ((fst eq) \<cdot> \<tau>, (snd eq) \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)"
definition "R_unifiable C \<longleftrightarrow> (\<exists>\<tau>. (\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*))"


definition "reachable eq \<longleftrightarrow> (\<exists>\<tau>. ((fst eq) \<cdot> \<tau>, (snd eq) \<cdot> \<tau>) \<in> (rstep R)\<^sup>*)"
definition "infeasible eq \<longleftrightarrow> (\<not> (\<exists>\<tau>. ((fst eq) \<cdot> \<tau>, (snd eq) \<cdot> \<tau>) \<in> (rstep R)\<^sup>*))"
definition "reachability C \<longleftrightarrow> (\<exists>\<tau>. (\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*))"
definition "infeasibility C \<longleftrightarrow> (\<not> (\<exists>\<tau>. (\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*)))"


definition "normalizable_infeasibility eq \<longleftrightarrow> (\<not> (\<exists>\<tau>. ((fst eq) \<cdot> \<tau>, (snd eq) \<cdot> \<tau>) \<in> (rstep R)\<^sup>* \<and> normalizable_subst R \<tau>))"

definition "normalizable_reachability_property s t \<longleftrightarrow> (\<forall>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>* \<longrightarrow> normalizable_subst R \<tau>)"

definition "normalized_subst_reachability_property s t \<longleftrightarrow> (\<forall>\<tau>. \<exists>\<tau>'. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>* \<longrightarrow> 
    (normal_subst R \<tau>' \<and> (s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>* \<and> (\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*)))"

definition "E_unif_normalized_subst_reachability_property s t \<longleftrightarrow> (\<forall>\<tau>. \<exists>\<tau>'. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>* \<longrightarrow> 
    (normal_subst R \<tau>' \<and> (s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>* \<and> (\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*)))"

definition subst_modulo :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" (infix "=\<^sub>R" 55) 
  where "\<sigma> =\<^sub>R \<theta> = (\<forall>x. (\<sigma> x, \<theta> x) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)"

lemma root_special_notin_F: assumes "root t = Some (\<doteq>, 2) \<or> root t = Some (\<top>, 0)"
  shows "\<not> funas_term t \<subseteq> F" using root_symbol_in_funas D assms D_fresh 
  by (auto simp add: root_symbol_in_funas subset_iff, fastforce+) 

lemma root_not_special_symbols: assumes "(l, r) \<in> R'"
  and "funas_rule (l, r) \<subseteq> F"
  and rnone:"root l \<noteq> None"
shows "root l \<noteq> Some (\<doteq>, 2) \<and> root l \<noteq> Some (\<top>, 0)" 
  using assms root_special_notin_F unfolding funas_rule_def D D_fresh R_sig 
    funas_rule_def funas_trs_def by auto

lemma wf_equational_term_safe_replace: assumes wf_s:"wf_equational_term s"
  and ft:"funas_term t \<subseteq> F"
  and pn:"p \<noteq> []"
  and pfun:"p \<in> fun_poss s"
  and snF:"s \<noteq> Fun (\<top>) []"
shows "wf_equational_term (replace_at s p t)" 
proof -
  from wf_s[unfolded wf_equational_term_def] snF
  have "(\<exists>u v. s = Fun \<doteq> [u, v] \<and> (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v)" by auto
  then obtain u v where s:"s = Fun \<doteq> [u, v]" and nu:"(\<doteq>, 2) \<notin> funas_term u" and nv:"(\<doteq>, 2) \<notin> funas_term v" by auto
  have poss_us:"\<forall>q \<in> poss u. u |_ q = s |_ (0 # q)" using s by auto  
  have poss_vs:"\<forall>q' \<in> poss v. v |_ q' = s |_ (1 # q')" using s by auto
  have "\<exists>q r. (q \<in> poss u \<and> p = 0 # q) \<or> (r \<in> poss v \<and> p = 1 # r)" using s pn pfun 
  proof(auto, goal_cases)
    case (1 x p)
    then show ?case by (metis fun_poss_imp_poss length_nth_simps(3) less_2_cases nth_Cons_Suc numeral_2_eq_2)
  next
    case (2 x p)
    then show ?case by (metis fun_poss_imp_poss less_2_cases nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
  next
    case (3 x p)
    then show ?case by (metis fun_poss_imp_poss less_2_cases nth_Cons_0 numeral_2_eq_2)
  qed
  then obtain q r where qpos:"(q \<in> poss u \<and> p = 0 # q) \<or> (r \<in> poss v \<and> p = 1 # r)" (is "?A \<or> ?B") by auto
  then show ?thesis
  proof
    assume asm:?A
    hence "replace_at s p t = Fun \<doteq> [(replace_at u q t), v]"  using s by auto
    moreover have "(\<doteq>, 2) \<notin> funas_term (replace_at u q t)" using D D_fresh qpos ft nu 
      by (smt (verit) UnCI UnE asm ctxt_supt_id funas_term_ctxt_apply insert_disjoint(1) subset_iff)
    moreover have "(\<top>, 0) \<notin> funas_term (replace_at u q t)" using D D_fresh qpos ft nu
      by (metis (no_types, lifting) UnCI UnE  wf_s[unfolded wf_equational_term_def] asm ctxt_supt_id 
          funas_term_ctxt_apply insert_disjoint(1) list.inject s snF subset_iff term.inject(2))
    then show ?thesis using assms s nv unfolding wf_s[unfolded wf_equational_term_def] 
      using calculation wf_equational_term_def by (simp add: wf_equational_term_def)
  next
    assume asm:?B
    hence "replace_at s p t = Fun \<doteq> [u , (replace_at v r t)]" using s by auto
    moreover have "(\<doteq>, 2) \<notin> funas_term (replace_at v r t)" using D D_fresh qpos ft nv  
      by (smt (verit) UnCI UnE asm ctxt_supt_id funas_term_ctxt_apply insert_disjoint(1) subset_iff)
    moreover have "(\<top>, 0) \<notin> funas_term (replace_at v r t)" using D D_fresh qpos ft nu
      by (metis (no_types, lifting) UnCI UnE  wf_s[unfolded wf_equational_term_def] asm ctxt_supt_id 
          funas_term_ctxt_apply insert_disjoint(1) list.inject s snF subset_iff term.inject(2))
    then show ?thesis using assms s nu unfolding wf_s[unfolded wf_equational_term_def] 
      using calculation wf_equational_term_def by (simp add: wf_equational_term_def)
  qed
qed

lemma convert_equation_into_term_sound: fixes rl::"('f, 'v) rule"
  assumes "funas_rule rl \<subseteq> F"
  shows "wf_equational_term (Fun (\<doteq>) [fst rl, snd rl])" 
proof -
  have *:"(\<doteq>, 2) \<notin> funas_rule rl \<and> (\<top>, 0) \<notin> funas_rule rl"
    using D D_fresh assms by blast
  let ?C = "Fun (\<doteq>) [fst rl, snd rl]"
  have "(\<doteq>, 2) \<notin> funas_term (fst rl) \<and> (\<doteq>, 2) \<notin> funas_term (snd rl)" using * lhs_wf rhs_wf 
    by (simp add: funas_defs(2))
  moreover have "(\<top>, 0) \<notin> funas_term (fst rl) \<and> (\<top>, 0) \<notin> funas_term (snd rl)" using * lhs_wf rhs_wf 
    by (simp add: funas_defs(2))
  then show ?thesis by (simp add: wf_equational_term_def wf_equational_term_mset_def, insert calculation, auto)
qed

lemma WN_obtains_normalizable_subst: fixes \<sigma>::"('f, 'v)subst"
  assumes "WN (rstep R)"
  obtains "normalizable_subst R \<sigma>" using assms unfolding normalizable_subst_def WN_on_def
  by (auto, meson normalizability_E)

lemma SN_obtains_normalizable_subst: fixes \<sigma>::"('f, 'v)subst"
  assumes "SN (rstep R)"
  obtains "normalizable_subst R \<sigma>" using assms unfolding normalizable_subst_def SN_on_def
    by (meson SN_imp_WN assms equational_narrowing.WN_obtains_normalizable_subst equational_narrowing_axioms that)

lemma obtains_normalized_subst: 
  assumes "normalizable_subst R \<sigma>"
  obtains \<tau> where "normal_subst R \<tau>" and "(\<forall>x. (\<sigma> x, \<tau> x) \<in> (rstep R)\<^sup>*)"
proof -
  let ?F = "\<lambda>x y. (\<sigma> x, y) \<in> (rstep R)\<^sup>* \<and> y \<in> NF (rstep R)"
  from assms[unfolded normalizable_subst_def] have "\<forall>x \<in> subst_domain \<sigma>. \<exists>y. ?F x y" by auto
  from bchoice[OF this] 
  obtain \<tau>' where *:"\<forall>x \<in> subst_domain \<sigma>.  (\<sigma> x, \<tau>' x) \<in> (rstep R)\<^sup>* \<and> \<tau>' x \<in> NF (rstep R)" by auto
  define \<tau> where "\<tau> \<equiv> \<tau>' |s (subst_domain \<sigma>)"
  have "subst_domain \<tau> \<subseteq> subst_domain \<sigma>" unfolding \<tau>_def by auto
      (metis Int_iff restrict_subst subst_domain_restrict_subst_domain)
  hence "normal_subst R \<tau> \<and> (\<forall>x. (\<sigma> x, \<tau> x) \<in> (rstep R)\<^sup>*)" unfolding some_NF_def normal_subst_def \<tau>_def
    using * by auto 
      (metis in_subst_restrict notin_subst_domain_imp_Var notin_subst_restrict rtrancl.simps)
  then show ?thesis using that by auto
qed

lemma funas_preserve_rstep: assumes fun_u:"funas_term u \<subseteq> F"
  and uv:"(u, v) \<in> (rstep R')\<^sup>*"
shows "funas_term v \<subseteq> F" using uv 
proof (induct, insert fun_u)
  case base
  then show ?case by (simp add: assms(1))
next
  case (step s t)
  from \<open>(s, t) \<in> rstep R'\<close>
  obtain C \<sigma> l r where "(l, r) \<in> R'" and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  then show ?case using R_sig R' step unfolding funas_defs by auto 
      (meson R_sig rhs_wf subsetD wf_F_subst)  
qed

lemma funas_reverse_preserve_rstep: assumes fun_v:"funas_term v \<subseteq> F"
  and uv:"(u, v) \<in> (rstep R')\<^sup>*"
shows "funas_term u \<subseteq> F" using uv
proof -
  from uv obtain n where "(u, v) \<in> (rstep R')^^n" by auto
  then show ?thesis
  proof (induct n arbitrary: u)
    case 0
    then show ?case using fun_v by auto 
  next
    case (Suc n)
    from Suc (2) obtain w where uw:"(u, w) \<in> rstep R'" and wv:"(w, v) \<in> (rstep R')^^ n"
      by (meson relpow_Suc_D2)
    from Suc(1) have fw:"funas_term w \<subseteq> F" using wv by auto
    from uw obtain C \<sigma> l r where "(l, r) \<in> R'" and "u = C\<langle>l \<cdot> \<sigma>\<rangle>" and "w = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
    then show ?case using R_sig R' step unfolding funas_defs using fw 
      by (auto, smt (verit) R_sig lhs_wf subsetD wf_F_subst)
  qed
qed

lemma funas_term_restrict: "funas_term s \<subseteq> F \<Longrightarrow> (s, t) \<in> rstep R \<Longrightarrow> (s, t) \<in> rstep R'"
proof -
  assume funas_s:"funas_term s \<subseteq> F"
    and st:"(s, t) \<in> rstep R"
  from st obtain C \<sigma> l r where lr:"(l, r) \<in> R"  and s:"s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  let ?srule = "\<lambda>x. (Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
  have fr:"\<forall>x. funas_rule (?srule x) = {(\<doteq>, 2), (\<top>, 0)}" using D 
    unfolding funas_defs by (auto simp add: numeral_2_eq_2)
  have cd:"\<forall>x. funas_rule (?srule x) \<subseteq> D" using D 
    unfolding funas_defs by (auto simp add: numeral_2_eq_2)
  have rule_type:"(l, r) \<in> R' \<or> (\<exists>x. (l, r) = ?srule x)" using R' lr by fastforce
  hence frule_type:"funas_rule (l, r) \<subseteq> F \<or> (\<exists>x. (l, r) = ?srule x)" using R_sig 
    by (metis fst_conv funas_rule_def le_supI lhs_wf rhs_wf snd_conv)
  have fnlr:"funas_rule (l, r) \<noteq> {(\<doteq>, 2), (\<top>, 0)}"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence flr:"funas_rule (l, r) = {(\<doteq>, 2), (\<top>, 0)}" by auto
    hence "funas_rule (l, r) = D" using D by auto
    have *:"\<exists>x. l = (Fun (\<doteq>) [Var x, Var x])" and "r = Fun (\<top>) []"
      using R' lr R_sig D D_fresh flr frule_type unfolding funas_defs by force+
    hence fl:"funas_term l = {(\<doteq>, 2)}" by auto
    obtain x where l:"l = (Fun (\<doteq>) [Var x, Var x])" using "*" by auto
    have l\<sigma>s:"l \<cdot> \<sigma> \<unlhd> s" using s by simp
    hence "l \<unlhd> s" using l wf_F_subst R_sig D D_fresh by auto 
        (metis l\<sigma>s fl funas_s insert_subset subset_trans supteq_imp_funas_term_subset)
    hence "funas_term l \<subseteq> F" using funas_s
      by (meson subset_trans supteq_imp_funas_term_subset)
    then show False using fl D D_fresh by auto
  qed 
  hence **:"funas_rule (l, r) \<subseteq> F" using fr by (metis frule_type)
  then show ?thesis
  proof -
    have "funas_rule (l, r) \<noteq> {(\<doteq>, 2), (\<top>, 0)}" unfolding funas_defs using ** R' R_sig D D_fresh  wf_F_subst 
      by (metis fnlr funas_rule_def)
    then show ?thesis using R' R_sig D D_fresh  wf_F_subst 
      by (metis fr rstepI rule_type s t)
  qed
qed

lemma funas_term_reverse_restrict: "funas_term t \<subseteq> F \<Longrightarrow> (s, t) \<in> rstep R \<Longrightarrow> (s, t) \<in> rstep R'" 
proof -
  assume funas_t:"funas_term t \<subseteq> F"
    and st:"(s, t) \<in> rstep R"
  from st obtain C \<sigma> l r where lr:"(l, r) \<in> R"  and s:"s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  let ?srule = "\<lambda>x. (Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
  have fr:"\<forall>x. funas_rule (?srule x) = {(\<doteq>, 2), (\<top>, 0)}" using D 
    unfolding funas_defs by (auto simp add: numeral_2_eq_2)
  have cd:"\<forall>x. funas_rule (?srule x) \<subseteq> D" using D 
    unfolding funas_defs by (auto simp add: numeral_2_eq_2)
  have rule_type:"(l, r) \<in> R' \<or> (\<exists>x. (l, r) = ?srule x)" using R' lr by fastforce
  hence frule_type:"funas_rule (l, r) \<subseteq> F \<or> (\<exists>x. (l, r) = ?srule x)" using R_sig 
    by (metis fst_conv funas_rule_def le_supI lhs_wf rhs_wf snd_conv)
  have fnlr:"funas_rule (l, r) \<noteq> {(\<doteq>, 2), (\<top>, 0)}"
  proof(rule ccontr)
    assume asm:"\<not> ?thesis"
    hence flr:"funas_rule (l, r) = {(\<doteq>, 2), (\<top>, 0)}" by auto
    hence flr:"funas_rule (l, r) = D" using D by auto
    have *:"\<exists>x. l = (Fun (\<doteq>) [Var x, Var x])" and "r = Fun (\<top>) []"
      using R' lr R_sig D D_fresh flr frule_type unfolding funas_defs by force+
    hence fl:"funas_term l = {(\<doteq>, 2)}" by auto
    obtain x where l:"l = (Fun (\<doteq>) [Var x, Var x])" using "*" by auto
    have l\<sigma>s:"l \<cdot> \<sigma> \<unlhd> s" using s by simp
    hence "l \<unlhd> s" using l wf_F_subst R_sig D D_fresh flr funas_t t unfolding funas_defs  by auto
    hence "funas_term l \<subseteq> F" using funas_t asm D D_fresh fl unfolding funas_defs
      by (metis (no_types, lifting) Int_absorb2 fst_conv funas_term_ctxt_apply insertCI insert_absorb 
          insert_disjoint(1) insert_is_Un le_sup_iff singleton_insert_inj_eq snd_conv t wf_F_subst zero_neq_numeral)
    then show False using fl D D_fresh by auto
  qed 
  hence **:"funas_rule (l, r) \<subseteq> F" using fr by (metis frule_type)
  then show ?thesis
  proof -
    have "funas_rule (l, r) \<noteq> {(\<doteq>, 2), (\<top>, 0)}" unfolding funas_defs using ** R' R_sig D D_fresh  wf_F_subst 
      by (metis fnlr funas_rule_def)
    then show ?thesis using R' R_sig D D_fresh  wf_F_subst 
      by (metis fr rstepI rule_type s t)
  qed
qed

lemma funas_rstep_R':assumes funas_uv:"funas_rule (u, v) \<subseteq> F"
  and uv:"(u, v) \<in> (rstep R)\<^sup>*" 
shows "(u, v) \<in> (rstep R')\<^sup>*" using uv
proof (induct)
  case base
  then show ?case by simp
next
  case (step s t)
  from funas_uv have funas_u:"funas_term u \<subseteq> F" by (simp add: funas_rule_def)
  from \<open>(u, s) \<in> (rstep R')\<^sup>*\<close>
  have funas_s:"funas_term s \<subseteq> F"
    by (simp add:funas_preserve_rstep[OF funas_u \<open>(u, s) \<in> (rstep R')\<^sup>*\<close>])
  from funas_term_restrict[OF funas_s \<open>(s, t) \<in> rstep R\<close>]
  have "(s, t) \<in> rstep R'" by auto
  then show ?case using step by auto
qed

lemma funas_rstep_R'_conv:assumes funas_uv:"funas_rule (u, v) \<subseteq> F"
  and uv:"(u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
shows "(u, v) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from uv obtain n where "(u, v) \<in> ((rstep R)\<^sup>\<leftrightarrow>)^^n" by auto
  then show ?thesis using funas_uv
  proof(induct n arbitrary: v)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from Suc(2) obtain w where uwn:"(u, w) \<in> (rstep R)\<^sup>\<leftrightarrow> ^^ n" and wv:"(w, v) \<in> (rstep R)\<^sup>\<leftrightarrow>" by auto
    from Suc(3) have fuF:"funas_term u \<subseteq> F" unfolding funas_defs by auto
    from uwn have fuwF:"funas_rule (u, w) \<subseteq> F"
    proof(induct n arbitrary: w)
      case 0
      then show ?case using fuF funas_term_restrict unfolding funas_defs by auto
    next
      case (Suc n)
      from Suc(2) obtain v where "(u, v) \<in> (rstep R)\<^sup>\<leftrightarrow> ^^ n" and vw:"(v, w) \<in> (rstep R)\<^sup>\<leftrightarrow>" by auto
      hence "funas_rule (u, v) \<subseteq> F" using Suc(1) by auto
      hence fvF:"funas_term v \<subseteq> F" unfolding funas_defs by auto
      from vw have "(v, w) \<in> (rstep R) \<or> (w, v) \<in> (rstep R)" by auto
      then show ?case (*using fuF funas_term_restrict funas_reverse_preserve_rstep unfolding funas_defs apply auto*)
      proof
        assume "(v, w) \<in> (rstep R)"
        with fvF have "funas_term w \<subseteq> F" using funas_preserve_rstep funas_term_restrict r_into_rtrancl by blast
        then show ?thesis unfolding funas_defs using fuF by simp
      next
        assume "(w, v) \<in> (rstep R)"
        with fvF have "funas_term w \<subseteq> F" using funas_reverse_preserve_rstep funas_term_reverse_restrict 
            r_into_rtrancl r_into_rtrancl by blast
        then show ?thesis unfolding funas_defs using fuF by simp
      qed
    qed
    from Suc(1) have *:"(u, w) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using uwn fuwF by auto
    have fwF:"funas_term w \<subseteq> F" using fuF 
      by (auto, metis UnI2 funas_defs(2) fuwF in_mono snd_eqD)
    from wv have "(w, v) \<in> (rstep R) \<or> (v, w) \<in> (rstep R)" by auto
    then show ?case
    proof
      assume "(w, v) \<in> (rstep R)"
      then show ?thesis using fuF fwF *
        by (meson conversionI' conversion_trans funas_term_restrict narrowing_axioms r_into_rtrancl transD)
    next
      assume "(v, w) \<in> (rstep R)"
      then show ?thesis using fuF fwF * Suc(3) by (metis (no_types, lifting) conversionI' conversion_inv 
            conversion_trans funas_defs(2) le_supE funas_term_restrict r_into_rtrancl snd_eqD transD)
    qed
  qed
qed

lemma rstep_reduction_step_eq: assumes uv:"((u, v) \<in> (rstep R)\<^sup>*)"
  shows "(Fun \<doteq> [u, v], Fun \<top> []) \<in> (rstep R)\<^sup>*"
proof -
  from rsteps_closed_ctxt[OF uv, of "More \<doteq> [] Hole [v]"]
  have "(Fun \<doteq> [u, v], Fun \<doteq> [v, v]) \<in> (rstep R)\<^sup>*" by auto
  moreover have "(Fun \<doteq> [v, v], Fun \<top> []) \<in> rstep R" 
    by (intro rstepI[where C = Hole and \<sigma> = "\<lambda> _. v"], unfold R', auto)
  ultimately show ?thesis by simp
qed

lemma not_reducible_T:"\<not> (\<exists>t. (Fun (\<top>) [], t) \<in> (rstep R))"
proof(rule ccontr)
  assume "\<not> ?thesis"
  then obtain t where *:"(Fun (\<top>) [], t) \<in> (rstep R)" by auto
  have "\<not> funas_term (Fun (\<top>) []) \<subseteq> F" using D D_fresh R_sig by auto
  hence "(Fun (\<top>) [], t) \<notin> (rstep R')" using R_sig by (smt (verit) lhs_wf rrstep_imp_rule_subst 
        rstep_args_NF_imp_rrstep supt_const wf_F_subst) 
  hence "\<exists>x. (Fun (\<top>) [], t) \<in> (rstep {((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []))})" using * R' 
    by (metis R' Un_iff rstep_union)
  then obtain x where "(Fun (\<top>) [], t) \<in> (rstep {((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []))})" by auto
  then obtain C \<sigma> l r where l:"l = Fun (\<doteq>) [Var x, Var x]" and r:"r = Fun (\<top>) []" and eq:"Fun (\<top>) [] = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>" by (smt (verit) Pair_inject rstep.simps singletonD)
  from t eq have "C = Hole" by (metis nectxt_imp_supt_ctxt supt_const)
  then show False using eq l by auto
qed

lemma rstep_reduction_step_R_unif_eq: assumes funas_uv:"funas_rule (u, v) \<subseteq> F"
  and uv:"((u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*)"
  and cr:"CR (rstep R)"
shows "(Fun \<doteq> [u, v], Fun \<top> []) \<in> (rstep R)\<^sup>*" using assms
proof -
  from funas_rstep_R'_conv[OF funas_uv uv]
  have uvR':"(u, v) \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" by auto
  then obtain n where "(u, v) \<in> (rstep R')\<^sup>\<leftrightarrow>^^n" by auto
  then show ?thesis using funas_uv
  proof (induct n arbitrary:u v)
    case 0
    have "\<exists>x. (Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []) \<in> R" using R' by auto
    then obtain x::'v where rl:"(Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []) \<in> R" by auto
    have "is_Fun (Fun \<doteq> [v, v])" by auto
    let ?p = "[]::pos"
    let ?s = "Fun \<doteq> [v, v]"
    let ?\<sigma> = "Var (x := v)" 
    let ?rl = "(Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
    let ?C = "Hole"
    let ?t = "Fun (\<top>) []"
    have "u = v" using 0 by auto
    have *:"snd ?rl \<cdot> ?\<sigma> = Fun (\<top>) []" by auto
    then show ?case using rl rstep.intros[of "fst ?rl" "snd ?rl" R ?s ?C ?\<sigma> ?t] using 0(1) by force
  next
    case (Suc n)
    note ** = this
    have fuv:"funas_rule (u, v) \<subseteq> F" using Suc(3) by auto
    from \<open>(u, v) \<in> (rstep R')\<^sup>\<leftrightarrow> ^^ Suc n\<close>
    obtain w where uw:"(u, w) \<in> (rstep R')\<^sup>\<leftrightarrow> ^^ n" and wv:"(w, v) \<in> (rstep R')\<^sup>\<leftrightarrow>" by auto
    from uw have "funas_rule (u, w) \<subseteq> F"
    proof(induct n arbitrary:w)
      case 0
      have "funas_term u \<subseteq> F" unfolding funas_defs using **(3) 
        using funas_rule_def by fastforce
      then show ?case  unfolding funas_defs using 0 by auto
    next
      case (Suc n)
      from Suc(2) obtain w' where uw':"(u, w') \<in> (rstep R')\<^sup>\<leftrightarrow> ^^ n" and w'w:"(w', w) \<in> (rstep R')\<^sup>\<leftrightarrow>" by auto
      from Suc(1) have fuw':"funas_rule (u, w') \<subseteq> F" using uw' by auto
      from w'w have *:"(w', w) \<in> (rstep R') \<or> (w, w') \<in> (rstep R')" by auto
      show ?case using *
      proof
        assume "(w', w) \<in> (rstep R')"
        then show ?thesis unfolding funas_defs using fuw' funas_preserve_rstep
          by (metis Un_subset_iff fst_conv funas_rule_def r_into_rtrancl snd_conv) 
      next
        assume "(w, w') \<in> (rstep R')"
        with fuw' have "funas_term w \<subseteq> F" unfolding funas_defs using funas_reverse_preserve_rstep by auto
        moreover from fuw' have "funas_term u \<subseteq> F" unfolding funas_defs by auto
        ultimately show ?thesis unfolding funas_defs by auto
      qed 
    qed
    hence *:"(Fun \<doteq> [u, w], Fun \<top> []) \<in> (rstep R)\<^sup>*" using Suc(1) uw by auto
    from wv have "(w, v) \<in> (rstep R') \<or> (v, w) \<in> (rstep R')" by auto
    then show ?case 
    proof
      assume "(w, v) \<in> (rstep R')"
      hence wv:"(w, v) \<in> rstep R" using R' by blast
      hence "(Fun \<doteq> [u, w], Fun \<doteq> [u, v]) \<in> (rstep R)" 
      proof -
        from wv obtain C \<sigma> l r where lr:"(l, r) \<in> R" and w:"w = C\<langle>l \<cdot> \<sigma>\<rangle>" and v:"v = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
        let ?p = "1 # hole_pos C"
        let ?w = "Fun \<doteq> [u, w]"
        let ?v = "Fun \<doteq> [u, v]"
        let ?C = "ctxt_of_pos_term ?p ?w"
        have "?w = ?C\<langle>l \<cdot> \<sigma>\<rangle>" using w by auto
        moreover have "?v = ?C\<langle>r \<cdot> \<sigma>\<rangle>" using w v wv by auto 
        ultimately have "(Fun \<doteq> [u, w], Fun \<doteq> [u, v]) \<in> rstep R" using lr by blast
        then show ?thesis by auto
      qed
      then show ?thesis using * cr[unfolded CR_on_def] 
        by (meson CR_divergence_imp_join NF_I NF_join_imp_reach cr not_reducible_T r_into_rtrancl)
    next
      assume vw:"(v, w) \<in> (rstep R')"
      hence vw:"(v, w) \<in> rstep R" using R' by blast
      hence "(Fun \<doteq> [u, v], Fun \<doteq> [u, w]) \<in> (rstep R)"
      proof -
        from vw obtain C \<sigma> l r where lr:"(l, r) \<in> R" and v:"v = C\<langle>l \<cdot> \<sigma>\<rangle>" and w:"w = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
        let ?p = "1 # hole_pos C"
        let ?v = "Fun \<doteq> [u, v]"
        let ?w = "Fun \<doteq> [u, w]"
        let ?C = "ctxt_of_pos_term ?p ?v"
        have "?v = ?C\<langle>l \<cdot> \<sigma>\<rangle>" using v by auto
        moreover have "?w = ?C\<langle>r \<cdot> \<sigma>\<rangle>" using w v wv by auto 
        ultimately have "(Fun \<doteq> [u, v], Fun \<doteq> [u, w]) \<in> rstep R" using lr by blast
        then show ?thesis by auto
      qed
      then show ?thesis by (simp add: "*" converse_rtrancl_into_rtrancl)
    qed
  qed
qed

lemma rstep_reduction_R_unif_normalized_equiv: assumes funas_st:"funas_rule (s, t) \<subseteq> F"
  and "\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>* \<and> normal_subst R \<tau>"
  and cr:"CR (rstep R)"
shows "\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun (\<top>) []) \<in> (rstep R)\<^sup>*"
proof -
  from assms obtain \<tau> where st:"(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" and norm\<tau>:"normal_subst R \<tau>" by auto
  have *:"funas_rule (s \<cdot> \<tau>, t \<cdot> \<tau>) \<subseteq> F" using funas_st wf_F_subst unfolding funas_defs by auto
  from rstep_reduction_step_R_unif_eq[of "s \<cdot> \<tau>" "t \<cdot> \<tau>"]
  show ?thesis using * norm\<tau> st cr by auto
qed

lemma rstep_reduction_equiv: assumes wn:"WN (rstep R)"
  and cr: "CR (rstep R)"
  and sti:"strongly_irreducible_term R t"
  and funas_st:"funas_rule (s, t) \<subseteq> F"
  and rstep_st:"\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
shows "\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun (\<top>) []) \<in> (rstep R)\<^sup>*"
proof -
  from rstep_st obtain \<tau> where st\<tau>:"(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" by auto
  from WN_obtains_normalizable_subst[OF wn]
  have norm\<tau>:"normalizable_subst R \<tau>" by auto
  from obtains_normalized_subst[OF norm\<tau>]
  obtain \<tau>' where norm\<tau>':"normal_subst R \<tau>'" and \<tau>\<tau>':"(\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*)" by auto
  have rstep\<tau>':"(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*"
  proof -
    have "(s \<cdot> \<tau>, s \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using \<tau>\<tau>' 
      by (simp add: substs_rsteps)
    moreover have "(t \<cdot> \<tau>, t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using \<tau>\<tau>'  
      by (simp add: substs_rsteps)
    moreover have "t \<cdot> \<tau>' \<in> NF (rstep R)" using sti[unfolded strongly_irreducible_term_def] norm\<tau>' by auto
    moreover have "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
      by (meson calculation(1) calculation(2) in_mono meetI meet_imp_conversion rtrancl_trans st\<tau>)
    ultimately show "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using cr[unfolded CR_on_def] 
      by (meson CR_NF_conv cr normalizability_E)
  qed
  have fr\<tau>':"funas_rule (s \<cdot> \<tau>', t \<cdot> \<tau>') \<subseteq> F" using wf_F_subst unfolding funas_defs 
    by (metis Un_subset_iff fst_conv funas_st funas_rule_def snd_conv)
  have t\<tau>':"t \<cdot> \<tau>' \<in> NF (rstep R)" using norm\<tau>' sti 
    by (simp add: strongly_irreducible_term_def)
  show ?thesis
  proof(rule exI[of _ \<tau>'], intro conjI)
    show "normal_subst R \<tau>'" by (simp add: norm\<tau>')
    from rstep_reduction_step_eq[of "s \<cdot> \<tau>'" "t \<cdot> \<tau>'"]
    show "(Fun \<doteq> [s \<cdot> \<tau>', t \<cdot> \<tau>'], Fun \<top> []) \<in> (rstep R)\<^sup>*" using fr\<tau>' rstep\<tau>' t\<tau>' by auto
  qed
qed

lemma rstep_reduction_normalizable_equiv: assumes cr: "CR (rstep R)"
  and rstep_st:"\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>* \<and> normalizable_subst R \<tau>"
shows "\<exists>\<theta>. normal_subst R \<theta> \<and> (Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun (\<top>) []) \<in> (rstep R)\<^sup>*"
proof -
  from rstep_st obtain \<tau> where st\<tau>:"(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" and norm\<tau>:"normalizable_subst R \<tau>" by auto
  from obtains_normalized_subst[OF norm\<tau>]
  obtain \<tau>' where norm\<tau>':"normal_subst R \<tau>'" and \<tau>\<tau>':"(\<forall>x. (\<tau> x, \<tau>' x) \<in> (rstep R)\<^sup>*)" by auto
  have rstep\<tau>':"(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> join (rstep R)"
  proof -
    have "(s \<cdot> \<tau>, s \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using \<tau>\<tau>' 
      by (simp add: substs_rsteps)
    moreover have "(t \<cdot> \<tau>, t \<cdot> \<tau>') \<in> (rstep R)\<^sup>*" using \<tau>\<tau>'  
      by (simp add: substs_rsteps)
    ultimately show "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> join (rstep R)" using st\<tau> 
      by (metis CR_divergence_imp_join CR_join_right_I cr)
  qed
  then obtain u where su: "(s \<cdot> \<tau>', u) \<in> (rstep R)^*" and tu: "(t \<cdot> \<tau>', u) \<in> (rstep R)^*" by auto  
  have all: "all_ctxt_closed UNIV ((rstep R)^*)" by blast
  have "(Fun \<doteq> [s \<cdot> \<tau>', t \<cdot> \<tau>'], Fun \<doteq> [u, u]) \<in> (rstep R)\<^sup>*" 
    by (rule all_ctxt_closedD[OF all], insert su tu, auto simp: less_Suc_eq)
  moreover have "(Fun \<doteq> [u, u], Fun (\<top>) []) \<in> rstep R" unfolding R'
    by (intro rstepI[of _ _ _ _ Hole "\<lambda> _. u"], auto)
  ultimately show ?thesis
    by (intro exI[of _ \<tau>'], insert norm\<tau>', auto)
qed


lemma F_term_not_reachable_by_additional_rule: fixes u::"('f, 'v) term"
  assumes funas_u:"funas_term u \<subseteq> F"
  shows "\<not> (\<exists>t. (u, t) \<in> rstep {(Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])})" 
proof(rule ccontr)
  assume "\<not> ?thesis"
  then obtain t where ut:"(u, t) \<in> rstep {(Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])}" by auto
  hence "(u, t) \<in> rstep R" using R' by blast
  hence "(u, t) \<in> rstep R'" using funas_rstep_R' funas_u 
    using funas_term_restrict by auto
  then obtain C \<sigma> l r where lrR':"(l, r) \<in> R'" and u:"u = C\<langle>l \<cdot> \<sigma>\<rangle>" and t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from funas_u u have "funas_ctxt C \<subseteq> F" by auto
  hence funas_t:"funas_term t \<subseteq> F" using t by auto
      (meson R_sig lrR' rhs_wf subsetD wf_F_subst)
  from ut obtain C' \<sigma>' l' r' where lrR':"(l', r') \<in> {(Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])}" and 
    u:"u = C'\<langle>l' \<cdot> \<sigma>'\<rangle>" and t:"t = C'\<langle>r' \<cdot> \<sigma>'\<rangle>" by auto
  hence "t = C'\<langle>Fun (\<top>) []\<rangle>" by auto
  then show False using funas_t D D_fresh by auto 
qed

lemma obtain_hole_pos_fun_uv:assumes fuv:"Fun \<doteq> [u, v] = C\<langle>l \<cdot> \<sigma>\<rangle>"
  and lr:"(l, r) \<in> R'"
  and nC:"C \<noteq> Hole"
obtains q w where "(q \<in> poss u \<and> hole_pos C = 0 # q) \<or> (w \<in> poss v \<and> hole_pos C = 1 # w)"
proof -
  have hcne:"hole_pos C \<noteq> []" using nC 
    by (metis ctxt_of_pos_term.simps(1) ctxt_of_pos_term_hole_pos)
  have "is_Fun l" using wf[unfolded wf_trs_def] lr R' by auto
  hence "is_Fun (l \<cdot> \<sigma>)" by auto
  moreover have *:"hole_pos C \<in> poss C\<langle>l \<cdot> \<sigma>\<rangle>" by simp
  moreover have **:"is_Fun (C\<langle>l \<cdot> \<sigma>\<rangle> |_ (hole_pos C))" 
    by (simp add: calculation(1))
  from poss_is_Fun_fun_poss[OF * **]
  have hcfun:"hole_pos C \<in> fun_poss C\<langle>l \<cdot> \<sigma>\<rangle>" by auto
  have poss_us:"\<forall>q \<in> poss u. u |_ q = Fun \<doteq> [u, v] |_ (0 # q)" by auto  
  have poss_vs:"\<forall>q' \<in> poss v. v |_ q' = Fun \<doteq> [u, v] |_ (1 # q')"  by auto
  have "\<exists>q r. (q \<in> poss u \<and> hole_pos C = 0 # q) \<or> (r \<in> poss v \<and> hole_pos C = 1 # r)" using fuv nC hcne hcfun 
  proof(auto, goal_cases)
    case (1 x p)
    then show ?case 
      by (metis fun_poss_imp_poss length_nth_simps(3) less_Suc0 less_SucE nth_Cons_Suc)
  next
    case (2 x p)
    then show ?case 
      by (metis diff_Suc_1 fun_poss_imp_poss less_Suc0 less_SucE nth_Cons')
  next
    case (3 x p)
    then show ?case
      by (metis fun_poss_imp_poss length_nth_simps(3) less_Suc0 less_SucE)
  qed  
  then show ?thesis using that by auto
qed

lemma obtain_hole_pos_fun_uv_right_irreducible:assumes fuv:"Fun \<doteq> [u, v] = C\<langle>l \<cdot> \<sigma>\<rangle>"
  and lr:"(l, r) \<in> R'"
  and nC:"C \<noteq> Hole"
  and vNF:"v \<in> NF (rstep R')"
obtains q w where "(q \<in> poss u \<and> hole_pos C = 0 # q)"
proof -
  have hcne:"hole_pos C \<noteq> []" using nC 
    by (metis ctxt_of_pos_term.simps(1) ctxt_of_pos_term_hole_pos)
  have "is_Fun l" using wf[unfolded wf_trs_def] lr R' by auto
  hence "is_Fun (l \<cdot> \<sigma>)" by auto
  moreover have *:"hole_pos C \<in> poss C\<langle>l \<cdot> \<sigma>\<rangle>" by simp
  moreover have **:"is_Fun (C\<langle>l \<cdot> \<sigma>\<rangle> |_ (hole_pos C))" 
    by (simp add: calculation(1))
  from poss_is_Fun_fun_poss[OF * **]
  have hcfun:"hole_pos C \<in> fun_poss C\<langle>l \<cdot> \<sigma>\<rangle>" by auto
  have poss_us:"\<forall>q \<in> poss u. u |_ q = Fun \<doteq> [u, v] |_ (0 # q)" by auto  
  have poss_vs:"\<forall>q' \<in> poss v. v |_ q' = Fun \<doteq> [u, v] |_ (1 # q')"  by auto
  have "\<exists>q r. (q \<in> poss u \<and> hole_pos C = 0 # q) \<or> (r \<in> poss v \<and> hole_pos C = 1 # r)" using fuv nC hcne hcfun 
  proof(auto, goal_cases)
    case (1 x p)
    then show ?case 
      by (metis fun_poss_imp_poss length_nth_simps(3) less_Suc0 less_SucE nth_Cons_Suc)
  next
    case (2 x p)
    then show ?case 
      by (metis diff_Suc_1 fun_poss_imp_poss less_Suc0 less_SucE nth_Cons')
  next
    case (3 x p)
    then show ?case
      by (metis fun_poss_imp_poss length_nth_simps(3) less_Suc0 less_SucE)
  qed  
  hence "\<exists>q r. (q \<in> poss u \<and> hole_pos C = 0 # q)" using vNF 
    by (metis NF_iff_no_step One_nat_def fuv lr poss_vs replace_at_ident rstepI subt_at_hole_pos)
  then show ?thesis using that by auto
qed

lemma funas_R_reachable_case:assumes funas_u:"funas_term u \<subseteq> F"
  and funas_v:"funas_term v \<subseteq> F"
  and uvU:"(Fun \<doteq> [u, v], U) \<in> rstep R'"
shows "\<exists>u' v'. (U = Fun \<doteq> [u', v] \<and> funas_term u' \<subseteq> F) \<or> (U = Fun \<doteq> [u, v'] \<and> funas_term v' \<subseteq> F)"
proof -
  from uvU obtain C l r \<sigma> where lr:"(l, r) \<in> R'" and fuv:"Fun \<doteq> [u, v] = C\<langle>l \<cdot> \<sigma>\<rangle>" and U:"U = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from lr have fl\<sigma>:"funas_term (l \<cdot> \<sigma>) \<subseteq> F" and fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using wf_F_subst 
    by (simp add: R_sig lhs_wf, meson R_sig lr rhs_wf wf_F_subst) 
  with fuv have nC:"C \<noteq> Hole" using D D_fresh numeral_2_eq_2 by force
  from obtain_hole_pos_fun_uv[OF fuv lr nC]
  obtain q w where qpos:"(q \<in> poss u \<and> hole_pos C = 0 # q) \<or> (w \<in> poss v \<and> hole_pos C = 1 # w)" by auto
  then show ?thesis
  proof
    assume asm:"q \<in> poss u \<and> hole_pos C = 0 # q"
    have U':"U = replace_at C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos C) (r \<cdot> \<sigma>)" using U by auto
    have l\<sigma>uq:"l \<cdot> \<sigma> = u |_ q" using asm fuv by (metis nth_Cons_0 subt_at.simps(2) subt_at_hole_pos)
    let ?u = "replace_at u q (r \<cdot> \<sigma>)"
    have fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using R_sig wf_F_subst fr\<sigma> unfolding funas_defs by auto
    have *:"U = Fun \<doteq> [?u, v]" using U' fuv rule exI[of _ ?u] asm l\<sigma>uq by auto
    have **:"funas_term ?u \<subseteq> F" using funas_u * fr\<sigma> by (metis asm ctxt_supt_id funas_term_ctxt_apply le_sup_iff)
    show ?thesis by (rule exI[of _ ?u], rule exI[of _ v], insert * **, auto) 
  next
    assume asm:"w \<in> poss v \<and> hole_pos C = 1 # w"
    have U':"U = replace_at C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos C) (r \<cdot> \<sigma>)" using U by auto
    have l\<sigma>uq:"l \<cdot> \<sigma> = v |_ w" using asm fuv
      by (metis One_nat_def nth_Cons_0 nth_Cons_Suc subt_at.simps(2) subt_at_hole_pos)
    let ?v = "replace_at v w (r \<cdot> \<sigma>)"
    have fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using R_sig wf_F_subst fr\<sigma> unfolding funas_defs by auto
    have *:"U = Fun \<doteq> [u, ?v]" using U' fuv rule exI[of _ ?v] asm l\<sigma>uq by auto
    have **:"funas_term ?v \<subseteq> F" using funas_v * fr\<sigma> by (metis asm ctxt_supt_id funas_term_ctxt_apply le_sup_iff)
    show ?thesis by (rule exI[of _ u], rule exI[of _ ?v], insert * **, auto) 
  qed
qed

lemma funas_R_reachable_case_right_irreducible:assumes funas_u:"funas_term u \<subseteq> F"
  and funas_v:"funas_term v \<subseteq> F"
  and uvU:"(Fun \<doteq> [u, v], U) \<in> rstep R'"
  and vNF:"v \<in> NF (rstep R')"
shows "\<exists>u'. (U = Fun \<doteq> [u', v] \<and> funas_term u' \<subseteq> F)"
proof -
  from uvU obtain C l r \<sigma> where lr:"(l, r) \<in> R'" and fuv:"Fun \<doteq> [u, v] = C\<langle>l \<cdot> \<sigma>\<rangle>" and U:"U = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from lr have fl\<sigma>:"funas_term (l \<cdot> \<sigma>) \<subseteq> F" and fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using wf_F_subst 
    by (simp add: R_sig lhs_wf, meson R_sig lr rhs_wf wf_F_subst) 
  with fuv have nC:"C \<noteq> Hole" using D D_fresh numeral_2_eq_2 by force
  from obtain_hole_pos_fun_uv_right_irreducible[OF fuv lr nC vNF]
  obtain q  where qpos:"(q \<in> poss u \<and> hole_pos C = 0 # q)" by auto
  have U':"U = replace_at C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos C) (r \<cdot> \<sigma>)" using U by auto
  have l\<sigma>uq:"l \<cdot> \<sigma> = u |_ q" using qpos fuv by (metis nth_Cons_0 subt_at.simps(2) subt_at_hole_pos)
  let ?u = "replace_at u q (r \<cdot> \<sigma>)"
  have fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using R_sig wf_F_subst fr\<sigma> unfolding funas_defs by auto
  have *:"U = Fun \<doteq> [?u, v]" using U' fuv rule exI[of _ ?u] qpos l\<sigma>uq by auto
  have **:"funas_term ?u \<subseteq> F" using funas_u * fr\<sigma> by (metis qpos ctxt_supt_id funas_term_ctxt_apply le_sup_iff)
  show ?thesis by (rule exI[of _ ?u], insert * **, auto)
qed

lemma fun_rstep_case1': assumes funas_u:"funas_term u \<subseteq> F"
  and funas_v:"funas_term v \<subseteq> F"
shows "(Fun \<doteq> [u, v], Fun \<doteq> [u, v']) \<in> rstep R' \<Longrightarrow> (v, v') \<in> (rstep R')\<^sup>*" using assms
proof -
  assume "(Fun \<doteq> [u, v], Fun \<doteq> [u, v']) \<in> rstep R'"
  then obtain C \<sigma> l r where lr:"(l, r) \<in> R'" and fuv:"Fun \<doteq> [u, v] = C\<langle>l \<cdot> \<sigma>\<rangle>" and fuv':"Fun \<doteq> [u, v'] = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from lr have fl\<sigma>:"funas_term (l \<cdot> \<sigma>) \<subseteq> F" and fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using wf_F_subst 
    by (simp add: R_sig lhs_wf, meson R_sig lr rhs_wf wf_F_subst) 
  with fuv have nC:"C \<noteq> Hole" using D D_fresh numeral_2_eq_2 by force
  from obtain_hole_pos_fun_uv[OF fuv lr nC]
  obtain q w where qpos:"(q \<in> poss u \<and> hole_pos C = 0 # q) \<or> (w \<in> poss v \<and> hole_pos C = 1 # w)" by auto
  then show ?thesis 
  proof
    assume asm:"q \<in> poss u \<and> hole_pos C = 0 # q"
    have fuv'eq:"Fun \<doteq> [u, v'] = replace_at C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos C) (r \<cdot> \<sigma>)" using fuv' by auto
    have l\<sigma>uq:"l \<cdot> \<sigma> = u |_ q" using asm fuv by (metis nth_Cons_0 subt_at.simps(2) subt_at_hole_pos)
    let ?u = "replace_at u q (r \<cdot> \<sigma>)"
    have *:"Fun \<doteq> [u, v'] = Fun \<doteq> [?u, v]" using fuv' fuv asm l\<sigma>uq fuv'eq by auto
    have "v = v'" using * by auto
    then show ?thesis by auto
  next
    assume asm:"w \<in> poss v \<and> hole_pos C = 1 # w"
    have fuv'eq:"Fun \<doteq> [u, v'] = replace_at C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos C) (r \<cdot> \<sigma>)" using fuv' by auto
    have l\<sigma>vw:"l \<cdot> \<sigma> = v |_ w" using asm fuv 
      by (metis One_nat_def nth_Cons_0 nth_Cons_Suc subt_at.simps(2) subt_at_hole_pos)
    let ?v = "replace_at v w (r \<cdot> \<sigma>)"
    have fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using R_sig wf_F_subst fr\<sigma> unfolding funas_defs by auto
    have *:"Fun \<doteq> [u, v'] = Fun \<doteq> [u, ?v]" using fuv' fuv fuv'eq asm l\<sigma>vw by auto
    let ?D = "ctxt_of_pos_term w v"
    have "?D\<langle>l \<cdot> \<sigma>\<rangle> = v" using asm by (simp add: ctxt_supt_id l\<sigma>vw)
    moreover have "?D\<langle>r \<cdot> \<sigma>\<rangle> = ?v" using * asm by auto 
    moreover have "(v, ?v) \<in> (rstep R')" using rstep.intros[of l r R' v ?D \<sigma> ?v] 
      using calculation lr by fastforce
    ultimately show ?thesis using * by blast
  qed
qed

lemma fun_rstep_case1: assumes funas_u:"funas_term u \<subseteq> F"
  and funas_v:"funas_term v \<subseteq> F"
shows "(Fun \<doteq> [u, v], Fun \<doteq> [u, v']) \<in> rstep R' \<Longrightarrow> (v, v') \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using assms fun_rstep_case1' by auto

lemma fun_rstep_case2': assumes funas_u:"funas_term u \<subseteq> F"
  and funas_v:"funas_term v \<subseteq> F"
shows "(Fun \<doteq> [u, v], Fun \<doteq> [u', v]) \<in> rstep R' \<Longrightarrow> (u, u') \<in> (rstep R')\<^sup>*" 
proof -
  assume "(Fun \<doteq> [u, v], Fun \<doteq> [u', v]) \<in> rstep R'"
  then obtain C \<sigma> l r where lr:"(l, r) \<in> R'" and fuv:"Fun \<doteq> [u, v] = C\<langle>l \<cdot> \<sigma>\<rangle>" and fuv':"Fun \<doteq> [u', v] = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from lr have fl\<sigma>:"funas_term (l \<cdot> \<sigma>) \<subseteq> F" and fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using wf_F_subst 
    by (simp add: R_sig lhs_wf, meson R_sig lr rhs_wf wf_F_subst) 
  with fuv have nC:"C \<noteq> Hole" using D D_fresh numeral_2_eq_2 by force
  from obtain_hole_pos_fun_uv[OF fuv lr nC]
  obtain q w where qpos:"(q \<in> poss u \<and> hole_pos C = 0 # q) \<or> (w \<in> poss v \<and> hole_pos C = 1 # w)" by auto
  then show ?thesis 
  proof
    assume asm:"q \<in> poss u \<and> hole_pos C = 0 # q"
    have fu'veq:"Fun \<doteq> [u', v] = replace_at C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos C) (r \<cdot> \<sigma>)" using fuv' by auto
    have l\<sigma>uq:"l \<cdot> \<sigma> = u |_ q" using asm fuv
      by (metis nth_Cons_0 subt_at.simps(2) subt_at_hole_pos)
    let ?u = "replace_at u q (r \<cdot> \<sigma>)"
    have fr\<sigma>:"funas_term (r \<cdot> \<sigma>) \<subseteq> F" using R_sig wf_F_subst fr\<sigma> unfolding funas_defs by auto
    have *:"Fun \<doteq> [u', v] = Fun \<doteq> [?u, v]" using fuv' fuv fu'veq asm l\<sigma>uq by auto
    let ?D = "ctxt_of_pos_term q u"
    have "?D\<langle>l \<cdot> \<sigma>\<rangle> = u" using asm by (simp add: ctxt_supt_id l\<sigma>uq)
    moreover have "?D\<langle>r \<cdot> \<sigma>\<rangle> = ?u" using * asm by auto 
    moreover have "(u, ?u) \<in> (rstep R')" using rstep.intros[of l r R' u ?D \<sigma> ?u] 
      using calculation lr by fastforce
    ultimately show ?thesis using * by auto
  next
    assume asm:"w \<in> poss v \<and> hole_pos C = 1 # w"
    have fu'veq:"Fun \<doteq> [u', v] = replace_at C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos C) (r \<cdot> \<sigma>)" using fuv' by auto
    have l\<sigma>uq:"l \<cdot> \<sigma> = v |_ w" using asm fuv 
      by (metis One_nat_def nth_Cons_0 nth_Cons_Suc subt_at.simps(2) subt_at_hole_pos)
    let ?v = "replace_at v w (r \<cdot> \<sigma>)"
    have *:"Fun \<doteq> [u', v] = Fun \<doteq> [u, ?v]" using fuv' fuv asm l\<sigma>uq fu'veq by simp
    have "u = u'" using * by auto
    then show ?thesis by auto
  qed
qed

lemma fun_rstep_case2: assumes funas_u:"funas_term u \<subseteq> F"
  and funas_v:"funas_term v \<subseteq> F"
shows "(Fun \<doteq> [u, v], Fun \<doteq> [u', v]) \<in> rstep R' \<Longrightarrow> (u, u') \<in> (rstep R')\<^sup>\<leftrightarrow>\<^sup>*" using fun_rstep_case2' assms by auto

lemma rstep_red_equiv: assumes fun_uv:"funas_rule (u, v) \<subseteq> F"
  and fr:"(Fun \<doteq> [u, v], Fun \<top> []) \<in> (rstep R)\<^sup>*"
  and vNF:"v \<in> NF (rstep R')"
shows "((u, v) \<in> (rstep R')\<^sup>*)" using fr
proof -
  let ?srule = "\<lambda>x. (Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
  have fr:"\<forall>x. funas_rule (?srule x) = {(\<doteq>, 2), (\<top>, 0)}" using D 
    unfolding funas_defs by (auto simp add: numeral_2_eq_2)
  have frD:"\<forall>x. funas_rule (?srule x) \<subseteq> D" using D 
    unfolding funas_defs by (auto simp add: numeral_2_eq_2)
  from fun_uv obtain n where n1:"n \<ge> 1" and fuv:"(Fun (\<doteq>) [u, v], Fun (\<top>) []) \<in> (rstep R)^^n"
    by (metis One_nat_def Suc_leI assms(2) bot_nat_0.not_eq_extremum list.distinct(1) relpow_0_E 
        rtrancl_power term.inject(2))
  then show ?thesis using fun_uv vNF
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
      from funas_R_reachable_case_right_irreducible[OF funas_u funas_v this Suc(5)]
      obtain u'  where U:"U = (Fun \<doteq> [u', v])" and fu':"funas_term u' \<subseteq> F" 
        using funas_u funas_v vNF by auto
      have IH:"(u', v) \<in> (rstep R')\<^sup>*" 
      proof (rule Suc(1))
        show "1 \<le> n" using False by auto
        show "(Fun \<doteq> [u', v], Fun \<top> []) \<in> rstep R ^^ n" 
          using U U2 by auto
        show "funas_rule (u', v) \<subseteq> F" 
          by (simp add: fu' funas_rule_def funas_v)
        show "v \<in> NF_trs R'" using Suc(5) by auto
      qed
      have "(u, u') \<in> (rstep R')\<^sup>*"  using fun_rstep_case2' U U1 * funas_u funas_v by blast
      then show ?thesis using IH by auto
    qed
  qed
qed

lemma norm_subst_rstep_preserve: assumes norm\<theta>':"normal_subst R \<theta>'" 
  and norm:"(\<forall>x. (\<theta> x, \<theta>' x) \<in> (rstep R)\<^sup>*)"
shows "(Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun \<doteq> [s \<cdot> \<theta>', t \<cdot> \<theta>']) \<in> (rstep R)\<^sup>*" 
proof -
  have s\<theta>s\<theta>':"(s \<cdot> \<theta>, s \<cdot> \<theta>') \<in> (rstep R)\<^sup>*" using norm by (simp add: substs_rsteps)
  have t\<theta>t\<theta>':"(t \<cdot> \<theta>, t \<cdot> \<theta>') \<in> (rstep R)\<^sup>*" using norm by (simp add: substs_rsteps)
  let ?C = "ctxt_of_pos_term [0] (Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>])"
  let ?C' = "ctxt_of_pos_term [1] (Fun \<doteq> [s \<cdot> \<theta>', t \<cdot> \<theta>])"
  from rsteps_closed_ctxt[OF s\<theta>s\<theta>', of ?C]
  have "(Fun \<doteq> [s \<cdot> \<theta>, t \<cdot> \<theta>], Fun \<doteq> [s \<cdot> \<theta>', t \<cdot> \<theta>]) \<in> (rstep R)\<^sup>*" by auto
  moreover from rsteps_closed_ctxt[OF t\<theta>t\<theta>', of ?C']
  have "(Fun \<doteq> [s \<cdot> \<theta>', t \<cdot> \<theta>], Fun \<doteq> [s \<cdot> \<theta>', t \<cdot> \<theta>']) \<in> (rstep R)\<^sup>*" by auto
  ultimately show ?thesis by auto
qed

(* Lemma 3.4 in MH94 using equational terms *)
lemma lifting_lemma_equational_terms:
  fixes V::"('v::infinite) set" and S::"('f, 'v)term" and T::"('f, 'v)term"
  assumes "normal_subst R \<theta>"
    and "wf_equational_term S"
    and "T = S \<cdot> \<theta>"
    and "vars_term S \<union> subst_domain \<theta> \<subseteq> V"
    and rs:"(T,  T') \<in> (rstep R)\<^sup>*"
    and fv:"finite V"
  shows "\<exists>\<sigma> \<theta>' S'. narrowing_derivation S S' \<sigma> \<and> T' = S' \<cdot> \<theta>' \<and> wf_equational_term S' \<and>
      normal_subst R \<theta>' \<and> (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V "
proof -
  from rs
  obtain f n where f0:"f 0 = T" and fn:"f n = T'" and rel_chain:"\<forall>i < n. (f i,  f (Suc i)) \<in> rstep R" 
    by (metis rtrancl_imp_seq)
  then have "\<exists>\<sigma> \<theta>' S'. narrowing_derivation_num S S' \<sigma> n \<and> T' = S' \<cdot> \<theta>' \<and> wf_equational_term S' \<and> 
    normal_subst R \<theta>' \<and> (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V" using assms
  proof(induct n arbitrary: S T T' \<theta> f V rule: wf_induct[OF wf_measure [of "\<lambda> n. n"]])
    case (1 n)
    note IH1 = 1(1)[rule_format]
    then show ?case
    proof(cases "n = 0")
      case True
      show ?thesis
        by (rule exI[of _ Var], rule exI[of _ \<theta>], rule exI[of _ "S"], insert 1 True)
          (simp add: narrowing_derivation_num_def subst_rule_def relpow_fun_conv, force) 
    next
      case False
      hence f0f1:"(f 0, f 1) \<in> rstep R" using 1 by auto
      then show ?thesis
      proof -
        from f0f1 obtain C \<sigma> l r  where f0:"f 0 = C\<langle>l \<cdot> \<sigma>\<rangle>" and f1:"f 1 = C\<langle>r \<cdot> \<sigma>\<rangle>"
          and rl:"(l, r) \<in> R" by auto
        have norm\<theta>:"normal_subst R \<theta>" by fact
        have s\<theta>t:"S \<cdot> \<theta> = T" using f0 1 by auto
        obtain \<omega> where varempty':"V \<inter> vars_rule (\<omega> \<bullet> (l, r)) = {}" using \<open>finite V\<close>
          by (metis rule_fs.rename_avoiding supp_vars_rule_eq vars_rule_def)
        have "is_Fun l" using wf[unfolded wf_trs_def] rl 
          by (simp add: is_Fun_Fun_conv wf_trs_imp_lhs_Fun)
        hence hpC:"hole_pos C \<in> fun_poss (f 0)" 
          by (metis f0 hole_pos_poss is_VarE is_VarI poss_is_Fun_fun_poss subst_apply_eq_Var subt_at_hole_pos)
        obtain \<omega>r where \<omega>r:"\<omega>r \<bullet> (\<omega> \<bullet> (l, r)) \<in> R" by (metis rl rule_pt.permute_minus_cancel(2))
        let ?p = "hole_pos C"
        have f0p:"(f 0) |_ ?p = l \<cdot> \<sigma>" using f0 by auto
        have pf0:"?p \<in> fun_poss (f 0)" using hpC by auto
        hence pp0:"?p \<in> poss (f 0)" by (simp add: fun_poss_imp_poss) 
        have p:"?p \<in> poss S" 
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence pns:"?p \<notin> poss S" by simp
          hence pnfs:"?p \<notin> fun_poss S" using fun_poss_imp_poss by blast
          have sub_eq:"(S \<cdot> \<theta>) |_ ?p = l \<cdot> \<sigma>" by (metis 1(2) 1(7) f0 subt_at_hole_pos)
          have ps\<theta>:"?p \<in> fun_poss (S \<cdot> \<theta>)" using 1(2) 1(7) pf0 by auto
          from poss_subst_apply_term[of ?p S \<theta>]
          obtain q r x where qpr:"?p = q @ r" and qs:"q \<in> poss S" and sqx:"S |_ q = Var x" and r:"r \<in> poss (\<theta> x)"
            using fun_poss_imp_poss pnfs ps\<theta> by blast
          hence *:"(S \<cdot> \<theta>) |_ ?p = (Var x) \<cdot> \<theta> |_ r" by force
          have "((Var x) \<cdot> \<theta>) \<in> NF (rstep R)" using norm\<theta> by (simp add: normal_subst_def)
              (metis NF_I NF_Var local.wf notin_subst_domain_imp_Var)
          hence "((Var x) \<cdot> \<theta> |_ r) \<in> NF (rstep R)" unfolding normal_subst_def using r
            by (metis NF_subterm eval_term.simps(1) subt_at_imp_supteq)
          then show False by (metis * NF_instance lhs_notin_NF_rstep rl sub_eq)
        qed
        hence pfun':"?p \<in> fun_poss (S \<cdot> \<theta>)" using p pp0 pf0 s\<theta>t f0p f0 \<open> f 0 = T\<close> \<open>is_Fun l\<close> norm\<theta>[unfolded normal_subst_def]
          by auto 
        have sub:"is_Fun S" using 1(6)[unfolded wf_equational_term_def] by auto 
        hence pfun:"?p \<in> fun_poss S" using pfun' p  p norm\<theta>[unfolded normal_subst_def]
          by (smt (verit, ccfv_SIG) "1.prems"(1) NF_instance eval_term.simps(1) f0p fun_poss_fun_conv is_Fun_Fun_conv is_Var_def lhs_notin_NF_rstep notin_subst_domain_imp_Var poss_is_Fun_fun_poss rl s\<theta>t subt_at_subst)
        hence vuS':"vars_term (S |_ ?p) \<subseteq> vars_term S"
        proof -
          from vars_term_subt_at[OF p]
          have "vars_term (S |_ ?p) \<subseteq> vars_term S" by auto
          then show ?thesis by auto
        qed
        with varempty' have varcond:"vars_term (S |_ ?p) \<inter> vars_rule (\<omega> \<bullet> (l, r)) = {}" using 1(10) 1(8) by blast
        have "\<exists>\<sigma>r. \<forall>x. \<sigma>r (\<omega> \<bullet> x) = \<sigma> x" using atom_pt.permute_minus_cancel(2) by (metis o_apply)
        then obtain \<sigma>r where \<sigma>rdef:"\<forall>t. \<sigma>r (\<omega> \<bullet> t) = \<sigma> t" by auto
        hence "\<forall>xs. subst_list \<sigma>r (\<omega> \<bullet> xs) = subst_list \<sigma> xs" unfolding subst_list_def
        proof(auto, goal_cases)
          case (1 xs s t)
          hence "(\<omega> \<bullet> s) \<cdot> \<sigma>r = s \<cdot> \<sigma>" 
            by (metis permute_term.simps(1) permute_term_subst_apply_term 
                subst_compose_def subst_monoid_mult.mult.left_neutral term_subst_eq_conv) 
          then show ?case 
            by (metis fst_conv rule_pt.fst_eqvt)
        next
          case (2 xs s t)
          hence "(\<omega> \<bullet> t) \<cdot> \<sigma>r = t \<cdot> \<sigma>" 
            by (metis permute_term.simps(1) permute_term_subst_apply_term 
                subst_compose_def subst_monoid_mult.mult.left_neutral term_subst_eq_conv) 
          then show ?case 
            by (metis snd_conv rule_pt.snd_eqvt)
        qed
        hence \<sigma>r1:"subst_list \<sigma>r [\<omega> \<bullet> (l,r)]  = subst_list \<sigma> [(l,r)]" unfolding subst_list_def  
          using rule_pt.fst_eqvt rule_pt.snd_eqvt 
          by (smt (verit) list.simps(8) list.simps(9) rules_pt.permute_list_def)
        hence subeq:"subst_rule \<sigma>r (\<omega> \<bullet> (l,r))  = subst_rule \<sigma> (l, r)" unfolding subst_rule_def subst_list_def by auto
        let ?\<sigma>dom = "vars_rule (\<omega> \<bullet> (l, r))"
        let ?\<sigma>r = "\<sigma>r |s (?\<sigma>dom)"
        let ?\<theta> = " \<theta> |s V"
        have sub_\<sigma>r:"subst_domain ?\<sigma>r \<subseteq> (vars_rule (\<omega> \<bullet> (l, r)))"
          by (metis inf_le1 restrict_subst subst_domain_restrict_subst_domain)
        have sub_\<theta>:"subst_domain ?\<theta> \<subseteq> V" using 1(8) by auto
        have inter_empty:"subst_domain ?\<sigma>r \<inter> subst_domain ?\<theta> = {}" using varempty' sub_\<sigma>r sub_\<theta> by auto
        from  s\<theta>t f0p have *:"(S \<cdot> \<theta> |_ ?p) = fst (\<omega> \<bullet> (l, r)) \<cdot> \<sigma>r" using subeq
          by (simp add: 1(2) subst_rule_def)
        have varcond':"vars_term (S |_ ?p) \<inter> vars_term (\<omega> \<bullet> l) = {}" 
        proof -
          have "vars_term (\<omega> \<bullet> l) \<subseteq> vars_rule (\<omega> \<bullet> (l, r))" 
            by (metis fst_conv rule_pt.fst_eqvt sup_ge1 vars_rule_def)
          then show ?thesis using varcond by auto
        qed
        with norm\<theta> * have **:"(S |_ ?p) \<cdot> \<theta> = fst (\<omega> \<bullet> (l, r)) \<cdot> \<sigma>r" by (simp add: p)
        have sub_eq:"(S |_ ?p) \<cdot> ?\<theta> = (\<omega> \<bullet> l) \<cdot> ?\<sigma>r" using **
          by (metis 1(8) coincidence_lemma' fst_conv le_sup_iff rule_pt.permute_prod.simps subst_domain_neutral sup_ge1 vars_rule_def)
        from subst_union_sound[OF sub_eq]
        have subst_eq_\<theta>\<sigma>:"(S |_ ?p) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)  = (\<omega> \<bullet> l) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using inter_empty sub_\<sigma>r sub_\<theta> inter_empty 
          by (smt (verit, best) disjoint_iff fst_conv local.wf rl sub_comm sub_eq subsetD subst_union.elims 
              term_subst_eq_conv varcond' varempty' vars_rule_eqvt vars_rule_lhs vars_term_eqvt)
        then obtain \<delta> where mgu_uv:"mgu (S |_ ?p) (\<omega> \<bullet> l) = Some \<delta>" using mgu_ex 
          by (meson ex_mgu_if_subst_apply_term_eq_subst_apply_term)
        from mgu_sound[OF mgu_uv] have \<delta>:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) =  \<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using subst_eq_\<theta>\<sigma> 
          by (smt (verit, ccfv_SIG) is_imgu_def subst_monoid_mult.mult_assoc the_mgu the_mgu_is_imgu)
        have subst_range_disj\<delta>:"subst_domain \<delta> \<inter> range_vars \<delta> = {}" using mgu_uv mgu_subst_domain_range_vars_disjoint by blast
        have crl:"(\<omega> \<bullet> r) \<cdot> \<sigma>r = (r \<cdot> \<sigma>)" by (metis rule_pt.snd_eqvt snd_conv subeq subst_rule_def)
        from subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
        have subinter:"subst_domain ?\<sigma>r = subst_domain \<sigma>r \<inter> ?\<sigma>dom" by auto
        have sndeq:"(\<omega> \<bullet> r) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r) = r \<cdot> \<sigma>" by (smt (verit, ccfv_threshold) Un_Int_eq(4) coincidence_lemma' crl 
              inf.absorb_iff2 inf_bot_right inf_commute inf_left_commute restrict_subst rule_pt.snd_eqvt snd_conv 
              subst_domain_restrict_subst_domain subst_union_term_reduction varempty' vars_rule_def)
        let ?S1 = "(replace_at S ?p (\<omega> \<bullet> r))\<cdot> \<delta>"
        have nar:"(S, ?S1, \<delta>) \<in> narrowing_step" unfolding subst_rule_def narrowing_step_def using  \<omega>r mgu_uv rl varempty' pfun by auto 
            (smt (verit, ccfv_threshold) 1(8) Int_assoc fst_conv inf.orderE inf_bot_right le_sup_iff narrowing_step.simps 
              narrowing_stepp_narrowing_step_eq rule_pt.fst_eqvt rule_pt.snd_eqvt snd_conv subst_apply_term_ctxt_apply_distrib)
        from narrowing_set_imp_rtran[OF nar]
        have condn1:"narrowing_derivation_num S ?S1 \<delta> 1" by auto
        let ?V = "(V - subst_domain \<delta>) \<union> range_vars \<delta>"
        let ?\<theta>1 = "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s ?V"
        have sub\<theta>1:"subst_domain ?\<theta>1 \<subseteq> ?V" unfolding subst_restrict_def 
          by (smt (verit, del_insts) mem_Collect_eq subset_eq subst_domain_def)
        have reseq:"?\<theta>1 |s ?V = (?\<theta> \<union>\<^sub>s ?\<sigma>r)|s ?V" 
          by (simp add: restrict_subst_domain_def)
        have reseq\<delta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1) |s V = (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r))|s V" 
          using r_subst_compose reseq by blast
        have reseq\<theta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1) |s V = \<theta> |s V " using 1(8) \<delta> by auto (smt (verit, best) \<delta> disjoint_iff notin_subst_domain_imp_Var 
              reseq\<delta> restrict_subst restrict_subst_domain_def subst_domain_neutral subst_ext subst_union.elims varempty')
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
            have subst_x:"x \<in> vars_term (S |_ ?p) \<union> vars_term (\<omega> \<bullet> l)" using mgu_uv 
                asm mgu_range_vars by auto
            then show "x \<in> ?B"
            proof
              assume "x \<in> vars_term (S |_ ?p)"
              hence "x \<in> V - subst_domain \<delta>" using 1(8) xn\<delta> vuS' by auto
              then show ?thesis by auto
            next
              assume asm2:"x \<in> vars_term (\<omega> \<bullet> l)"
              hence xnu:"x \<notin> vars_term (S |_ ?p)" using varcond' by blast
              from vars_term_range[OF asm asm2 subst_range_disj\<delta>]
              have xv\<delta>:"x \<in> vars_term ((\<omega> \<bullet> l) \<cdot> \<delta>)" by auto
              have *:"x \<in> vars_term (S |_ ?p \<cdot> \<delta>)" using mgu_uv xv\<delta>
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu) 
              hence "vars_term ((\<omega> \<bullet> l) \<cdot> \<delta>) = vars_term (S |_ ?p \<cdot> \<delta>)" using mgu_uv 
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu)
              from subst_restricted_range_vars[OF * subst_range_disj\<delta> xnu asm]
              have "x \<in> range_vars (\<delta> |s vars_term (S |_ ?p))" by auto
              moreover have upV:"vars_term (S |_ ?p) \<subseteq> V" using 1(8) vuS' by auto
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
        have wf_S1:"wf_equational_term ?S1"
        proof - 
          let ?srule = "\<lambda>x. (Fun (\<doteq>) [Var x, Var x], Fun (\<top>) [])"
          have fr:"\<forall>x. funas_rule (?srule x) = {(\<doteq>, 2), (\<top>, 0)}" using D 
            unfolding funas_defs by (auto simp add: numeral_2_eq_2)
          have cd:"\<forall>x. funas_rule (?srule x) \<subseteq> D" using D 
            unfolding funas_defs by (auto simp add: numeral_2_eq_2)
          have wf_S:"wf_equational_term S" by (simp add: 1(6))
          have \<omega>rl:"(l, r) \<in> R' \<or> (\<exists>x. (l, r) = ?srule x)" using R' rl by fastforce
          moreover have \<omega>rl_un:"funas_rule (l, r) \<subseteq> F  \<or> (\<exists>x. (l, r) = ?srule x)" 
            using R_sig by (metis Trs.funas_defs(2) calculation fst_conv le_sup_iff lhs_wf rhs_wf snd_conv)
          ultimately have "funas_rule (l, r) \<subseteq> F \<or> funas_rule (l, r) = {(\<doteq>, 2), (\<top>, 0)}"
            using fr by metis
          then consider (ordinary) "funas_rule (l, r) \<subseteq> F" | (special) "funas_rule (l, r) = {(\<doteq>, 2), (\<top>, 0)}" 
            using \<omega>rl by auto
          hence "wf_equational_term (replace_at S ?p (\<omega> \<bullet> r))"
          proof(cases)
            case ordinary
            hence rlR':"(l, r) \<in> R'" using R' D R_sig D_fresh 
              by (metis Int_absorb2 \<omega>rl fr insert_not_empty)
            from ordinary have *:"funas_rule (\<omega> \<bullet> (l, r)) \<subseteq> F" using funas_rule_perm by blast
            have **:"root (\<omega> \<bullet> l) = root l" using root_perm_inv by metis
            from fun_root_not_None[OF \<open>is_Fun l\<close>] have nroot:"root l \<noteq> None" by auto
            from root_not_special_symbols[OF rlR' ordinary nroot]
            have "root l \<noteq> Some (\<doteq>, 2) \<and> root l \<noteq>  Some (\<top>, 0)" by simp
            hence rn:"root(\<omega> \<bullet> l) \<noteq> Some (\<doteq>, 2) \<and> root(\<omega> \<bullet> l) \<noteq> Some (\<top>, 0)" 
              by (simp add: "**")
            have "root (S |_ ?p) = root ((\<omega> \<bullet> l) \<cdot> \<sigma>r)" using root_subst_inv 
              by (metis coincidence_lemma fst_conv pfun local.wf rl sub_eq vars_rule_eqvt vars_rule_lhs vars_term_eqvt)
            also have "... = root(\<omega> \<bullet> l)" using wf[unfolded wf[unfolded wf_trs_def]] root_subst_inv 
              by (metis ** empty_pos_in_poss is_Var_def nroot poss_is_Fun_fun_poss root.simps(1) subt_at.simps(1))
            finally have root_eq:"root (S |_ ?p) = root(\<omega> \<bullet> l)" by auto
            hence "root (S |_ ?p) \<noteq> Some (\<doteq>, 2) \<and> root (S |_ ?p) \<noteq> Some (\<top>, 0)" using rn by auto
            hence np:"?p \<noteq> []" using wf_S[unfolded wf_equational_term_def] by force
            hence uf:"S \<noteq> Fun (\<top>) []" using pfun by auto
            from wf_S[unfolded wf_equational_term_def]
            obtain v w where u:"S = Fun \<doteq> [v, w] \<and> (\<doteq>, 2) \<notin> funas_term v \<and> (\<doteq>, 2) \<notin> funas_term w"
              using uf by auto
            have "funas_term (\<omega> \<bullet> r) \<subseteq> F" using * unfolding funas_defs 
              by (metis R_sig funas_term_perm rhs_wf rlR')
            then show ?thesis by (simp add: np wf_equational_term_safe_replace wf_S uf pfun)
          next
            case special
            have "funas_rule (\<omega> \<bullet> (l,r)) = {(\<doteq>, 2), (\<top>, 0)}"
            proof(rule ccontr)
              assume asm:"\<not> ?thesis"
              have "funas_rule (l, r) = D" using special
                by (simp add: D)
              hence "funas_rule (\<omega> \<bullet> (l, r)) = D" using funas_rule_perm 
                by (metis rule_pt.permute_minus_cancel(2) subsetI subset_antisym)
              then show False using asm D by simp
            qed
            hence "\<exists>x. fst (\<omega> \<bullet> (l, r)) = fst (?srule x)"
            proof -
              from special have "\<exists>y. l = fst (?srule y)" using \<omega>rl
                using D D_fresh \<omega>rl_un by auto
              then obtain y where "l = fst (?srule y)" by auto
              hence "l \<cdot> ((sop \<omega>)::('f, 'v) subst) = (fst (?srule y)) \<cdot> ((sop \<omega>)::('f, 'v) subst)" by auto
              hence "\<omega> \<bullet> l = (fst (?srule y)) \<cdot> ((sop \<omega>)::('f, 'v) subst) "
                by (simp add: rule_pt.fst_eqvt rule_pt.snd_eqvt subst_equation_def)
              moreover have "\<exists>x. (fst (?srule y)) \<cdot> ((sop \<omega>)::('f, 'v) subst) =
                  fst (?srule x)" unfolding subst_equation_def by auto
              ultimately show ?thesis by (smt (verit, best) fst_conv rule_pt.fst_eqvt)
            qed
            then obtain x where \<omega>'rl:"fst (\<omega> \<bullet> (l, r)) = fst (?srule x)" by auto
            have rclhs:"root (fst (\<omega> \<bullet> (l, r))) = Some (\<doteq>, 2)" using \<omega>'rl by auto
            have crhs_\<omega>'rl:"(snd (\<omega> \<bullet> (l, r))) = Fun (\<top>) []" using \<omega>'rl
              by (metis D D_fresh \<omega>rl_un insert_disjoint(1) insert_subset list.simps(8) permute_Fun 
                  rule_pt.snd_eqvt snd_conv special terms_pt.permute_list_def)
            have isFun\<omega>':"is_Fun (\<omega> \<bullet> l)" using \<open>is_Fun l\<close>  \<omega>'rl by auto
            from fun_root_not_None[OF isFun\<omega>'] have nroot:"root (\<omega> \<bullet> l) \<noteq> None" by auto
            have rclhs\<sigma>r:"root ((\<omega> \<bullet> l) \<cdot> \<sigma>r) = Some (\<doteq>, 2)" using \<omega>'rl 
              by (metis empty_pos_in_poss fst_conv is_Fun_Fun_conv poss_is_Fun_fun_poss rclhs root_subst_inv 
                  rule_pt.fst_eqvt subt_at.simps(1))
            have "root (S |_ ?p) = root ((\<omega> \<bullet> l) \<cdot> \<sigma>r)" using pfun root_subst_inv 
              by (metis ** fst_conv rule_pt.fst_eqvt)
            also have "... = root(\<omega> \<bullet> l)" using wf[unfolded wf_trs_def] root_subst_inv 
              by (metis fst_conv rclhs rclhs\<sigma>r rule_pt.fst_eqvt)
            finally have root_eq:"root (S |_ ?p) = root(\<omega> \<bullet> l)" by auto
            with ** pfun have root_u:"root (S|_ ?p) = Some (\<doteq>, 2)" using rclhs 
              by (metis fst_conv rule_pt.fst_eqvt)
            have un:"S \<noteq> Fun (\<top>) []"
            proof(rule ccontr)
              assume "\<not> ?thesis"
              hence "S = Fun (\<top>) []" by auto
              hence "funas_term S = {(\<top>, 0)}" by auto
              then show False using root_u subterm_funas pfun by fastforce
            qed
            from wf_S[unfolded wf_equational_term_def] 
            obtain v w where u:"S = Fun (\<doteq>) [v, w]" and nv:"(\<doteq>, 2) \<notin> funas_term v" and 
              nw:"(\<doteq>, 2) \<notin> funas_term w" using un by auto
            have p:"?p = []"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence "v \<unrhd> (S |_ ?p) \<or> w \<unrhd> (S |_ ?p)" using pfun u by auto
                  (metis diff_Suc_1 fun_poss_imp_poss less_Suc0 less_Suc_eq nth_Cons' subt_at_imp_supteq)
              then show False using root_u nv nw 
                by (meson root_symbol_in_funas subset_eq supteq_imp_funas_term_subset)
            qed
            hence "replace_at S ?p (\<omega> \<bullet> r) = (\<omega> \<bullet> r)" by auto
            then show ?thesis using crhs_\<omega>'rl wf_S[unfolded wf_equational_term_def] 
              by (simp add: wf_equational_term_def rule_pt.permute_prod.simps)
          qed
          then show ?thesis unfolding wf_equational_term_def using wf_eq_subst
            by (metis wf_equational_term_def)
        qed
        have vars_s1:"vars_term ?S1 \<subseteq> ?V" 
        proof -
          have *:"vars_term (\<omega> \<bullet> r) \<subseteq> vars_term (\<omega> \<bullet> l)" using wf[unfolded wf_trs_def] 
            by (metis fst_eqD local.wf rl rule_pt.fst_eqvt rule_pt.snd_eqvt snd_eqD sup.orderI vars_rule_def 
                vars_rule_eqvt vars_rule_lhs vars_term_eqvt)
          from var_cond_stable[OF this]
          have "vars_term ((\<omega> \<bullet> r) \<cdot> \<delta> ) \<subseteq> vars_term ((\<omega> \<bullet> l) \<cdot> \<delta>)" by fastforce
          from replace_var_stable[OF this]
          have "vars_term ?S1 \<subseteq> vars_term (replace_at S ?p ((\<omega> \<bullet> l))\<cdot> \<delta>)" 
            by (meson * replace_var_stable var_cond_stable)
          moreover have "vars_term ((replace_at S ?p (\<omega> \<bullet> l))\<cdot> \<delta>) = vars_term (S \<cdot> \<delta>)"
            by (metis ctxt_supt_id mgu_uv p subst_apply_term_ctxt_apply_distrib subst_apply_term_eq_subst_apply_term_if_mgu)
          moreover have "vars_term (S \<cdot> \<delta>) \<subseteq> ?V" 
            by (smt (verit) 1(8) Un_Diff Un_iff subsetI subset_Un_eq vars_term_subst_apply_term_subset)
          ultimately show ?thesis by auto
        qed
        have rel_chain':"\<And>i. i < n - 1 \<Longrightarrow> (f (i + 1), f (Suc i + 1)) \<in> rstep R" using rel_chain 
          by (simp add: 1(4))
        let ?f = "\<lambda>i. f (i + 1)"
        have relstar:"(f 1, f n) \<in> (rstep R)\<^sup>*" using False 1(4) less_Suc_eq 
          by (induct n, blast, metis (no_types, lifting) One_nat_def rtrancl.simps)
        have "\<exists>\<delta>' \<theta>' S'. narrowing_derivation_num ?S1 S' \<delta>' (n - 1) \<and>  f n = S' \<cdot> \<theta>' \<and> wf_equational_term S' \<and> normal_subst R \<theta>' \<and>
         (\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V"
        proof (rule IH1[of "n - 1"  ?f "f 1" "f n" ?\<theta>1 ?S1], goal_cases)
          case 1
          then show ?case using False by auto
        next
          case 2
          then show ?case by simp
        next
          case 3
          then show ?case using False by auto
        next
          case (4 i)
          then show ?case using rel_chain' by auto
        next
          case 5
          then show ?case using norm\<theta>1 by auto
        next
          case 6
          then show ?case using wf_S1 by auto
        next
          case 7
          have inempty:"subst_domain ?\<sigma>r \<inter> V = {}" using varempty' subinter by auto
          hence \<theta>sv:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s V = \<theta> |s V"
            using \<delta> reseq\<delta> reseq\<theta> by auto
          have "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s (vars_term (\<omega> \<bullet> r)) = ?\<sigma>r |s (vars_term (\<omega> \<bullet> r))" 
          proof -
            { fix v :: 'v
              have "vars_rule (\<omega> \<bullet> (l, r)) - V = vars_rule (\<omega> \<bullet> (l, r))" using varempty' by fastforce
              then have "V \<inter> vars_term (\<omega> \<bullet> r) = {}"  by (metis (no_types, lifting) disjoint_iff 
                    rule_pt.snd_eqvt snd_conv subsetD sup_ge2 varempty' vars_rule_def)
              then have "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s (vars_term (\<omega> \<bullet> r)) = ?\<sigma>r |s (vars_term (\<omega> \<bullet> r))"
                by (smt (verit, best) Int_iff disjoint_iff inf.absorb_iff2 sub_\<theta> subst_ext subst_union.simps)
            } then show ?thesis by fastforce
          qed
          have "f 1 = ?S1 \<cdot> ?\<theta>1"
          proof -
            have "f 1 = replace_at (S \<cdot> \<theta>) ?p ((\<omega> \<bullet> r) \<cdot> \<sigma>r)" using crl f1 s\<theta>t 
              by (metis 1(2) ctxt_of_pos_term_hole_pos f0) 
            also have "...  = replace_at (S \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)) ?p ((\<omega> \<bullet> r) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r))" 
              by (metis 1(8) \<theta>sv coincidence_lemma' crl sndeq sup.boundedE)
            also have "... = replace_at S ?p (\<omega> \<bullet> r) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" by (simp add: ctxt_of_pos_term_subst p)
            also have "... = replace_at S ?p (\<omega> \<bullet> r) \<cdot> (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r))" using \<delta> by auto
            also have "... = ?S1 \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" by simp
            also have *:"f 1 = ?S1 \<cdot> ?\<theta>1" using vars_s1 using calculation subst_apply_term_restrict_subst_domain by fastforce
            finally show ?thesis using * by fastforce
          qed
          then show ?case by auto
        next
          case 8
          then show ?case using vars_s1 sub\<theta>1 by auto
        next
          case 9
          then show ?case using relstar by blast
        next
          case 10
          then show ?case by (metis 1(10) finite_Diff2 infinite_Un mgu_finite_range_vars mgu_finite_subst_domain mgu_uv)
        qed
        then obtain \<delta>' \<theta>' S' where condn2:"narrowing_derivation_num ?S1 S' \<delta>' (n - 1)" and sub\<theta>':"S'\<cdot> \<theta>' = f n"
          and norm\<theta>':"normal_subst R \<theta>'" and wfS':"wf_equational_term S'" and sub_rel:"(\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V" by auto
        from n0_narrowing_derivation_num have n1:"n = 1 \<Longrightarrow> S' = ?S1 \<and> \<delta>' = Var" 
          using False using condn2 by (metis diff_self_eq_0)
        from condn2 obtain g \<tau> where g0:"g 0 = ?S1" and gnm1:"g (n - 1) = S'"
          and gcond_chain:"\<forall>i < n - 1. ((g i), (g (Suc i)), (\<tau> i)) \<in> narrowing_step" and comp\<delta>':"if n = 1 then \<delta>' = Var 
          else \<delta>' = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (n - 1)])" using False n1 unfolding narrowing_derivation_num_def by auto
        let ?g = "\<lambda>i. if i = 0 then S else g (i - 1)"
        let ?\<tau> = "\<lambda>i. if i = 0 then \<delta> else \<tau> (i - 1)"
        have "\<delta>' = compose (map ?\<tau> [1..< n])" 
          by (smt (verit) One_nat_def comp\<delta>' add_diff_cancel_left' add_diff_inverse_nat compose_simps(1) diff_zero length_upt 
              less_Suc_eq_0_disj list.simps(8) map_equality_iff nth_upt plus_1_eq_Suc upt_eq_Nil_conv)      
        hence \<delta>\<delta>'comp:"\<delta> \<circ>\<^sub>s \<delta>' = compose (map ?\<tau> [0..< n])" using False upt_conv_Cons by fastforce
        have condn:"narrowing_derivation_num S S' (\<delta> \<circ>\<^sub>s \<delta>') n" 
        proof -
          have "(\<exists>f. f 0 = S \<and> f n = S' \<and> (\<exists>\<tau>. (\<forall>i<n. (f i, f (Suc i), \<tau> i) \<in> narrowing_step) \<and>
            \<delta> \<circ>\<^sub>s \<delta>' = compose (map \<tau> [0..<n])))" 
            by (rule exI[of _ ?g], insert \<delta>\<delta>'comp False One_nat_def gnm1) (smt (verit, ccfv_SIG) Suc_pred gcond_chain 
                bot_nat_0.not_eq_extremum diff_Suc_1 g0 less_nat_zero_code nar not_less_eq)
          then show ?thesis 
            by (simp add: narrowing_derivation_num_def False local.wf)
        qed
        show ?thesis
        proof(rule exI[of _ "\<delta> \<circ>\<^sub>s \<delta>'"], rule exI[of _ \<theta>'], rule exI[of _ S'], intro conjI, goal_cases)
          case 1
          then show ?case using condn by auto
        next
          case 2
          then show ?case using 1(3) sub\<theta>' by auto
        next
          case 3
          then show ?case using norm\<theta>' using wfS' by auto
        next
          case 4
          then show ?case using wfS' norm\<theta>' by blast
        next
          case 5
          then show ?case 
            by (metis Un_upper1 r_subst_compose reseq\<theta> sub_rel subst_monoid_mult.mult_assoc sup.orderE)
        qed
      qed
    qed
  qed
  then show ?thesis using narrowing_deriv_implication by blast
qed

end

end