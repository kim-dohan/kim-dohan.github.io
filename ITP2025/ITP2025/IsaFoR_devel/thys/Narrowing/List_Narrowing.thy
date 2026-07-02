(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Narrowing with special encoding\<close>

theory List_Narrowing
  imports
    Multiset_Narrowing
begin

lemma args_convs_impl_full_conv: 
  assumes conv: "\<And> u v. (u,v) \<in> set pairs \<Longrightarrow> (u, v) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
  shows "(Fun c (map fst pairs), Fun c (map snd pairs)) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
proof -
  have all: "all_ctxt_closed UNIV ((rstep R)\<^sup>\<leftrightarrow>\<^sup>*)"
    by (simp add: all_ctxt_closed_rstep_conversion)
  show ?thesis 
    by (rule all_ctxt_closedD[OF all], insert conv, auto) 
      (metis nth_mem surj_pair)
qed

lemma args_convs_impl_full_conv_subst: 
  assumes conv: "\<And> u v. (u,v) \<in> set pairs \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
  shows "(Fun c (map fst pairs) \<cdot> \<sigma>, Fun c (map snd pairs) \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
proof -
  let ?pairs = "map (\<lambda> (u,v). (u \<cdot> \<sigma>, v \<cdot> \<sigma>)) pairs" 
  have id: "(Fun c (map fst pairs) \<cdot> \<sigma>, Fun c (map snd pairs) \<cdot> \<sigma>)
    = (Fun c (map fst ?pairs), Fun c (map snd ?pairs))" 
    apply (simp, intro conjI)
    subgoal by (induct pairs, auto)
    subgoal by (induct pairs, auto)
    done
  show ?thesis unfolding id
    by (rule args_convs_impl_full_conv, insert conv, auto)
qed

lemma args_rewr_impl_full_rewr: assumes conv: "\<And> u v. (u,v) \<in> set pairs \<Longrightarrow> (u, v) \<in> (rstep R)\<^sup>*" 
  shows "(Fun c (map fst pairs), Fun c (map snd pairs)) \<in> (rstep R)\<^sup>*" 
proof -
  have all: "all_ctxt_closed UNIV ((rstep R)\<^sup>*)"
    by (simp add: all_ctxt_closed_rsteps)
  show ?thesis  
    by (rule all_ctxt_closedD[OF all], insert conv, auto)
      (metis nth_mem surj_pair)
qed

lemma args_join_iff_full_join: assumes "wf_trs R" and "(c,length pairs) \<notin> funas_trs R" 
  shows "(Fun c (map fst pairs), Fun c (map snd pairs)) \<in> join (rstep R)
     \<longleftrightarrow> (\<forall> u v. (u,v) \<in> set pairs \<longrightarrow> (u, v) \<in> join (rstep R))" (is "?A = ?B")
proof
  assume B: ?B
  let ?n = "length pairs" 
  {
    fix i
    assume i: "i < ?n" 
    hence "(fst (pairs ! i), snd (pairs ! i)) \<in> set pairs" by auto
    from B[rule_format, OF this] 
    have  "\<exists> w. (fst (pairs ! i), w) \<in> (rstep R)^* \<and> (snd (pairs ! i), w) \<in> (rstep R)^*" by blast
  }
  hence "\<forall> i. \<exists> w. i < ?n \<longrightarrow> (fst (pairs ! i), w) \<in> (rstep R)^* \<and> (snd (pairs ! i), w) \<in> (rstep R)^*" 
    by blast
  from choice[OF this] obtain w where w: "\<And> i. i < ?n \<Longrightarrow> (fst (pairs ! i), w i) \<in> (rstep R)^* \<and> (snd (pairs ! i), w i) \<in> (rstep R)^*"
    by auto
  let ?p1 = "map (\<lambda> i. (fst (pairs ! i), w i)) [0 ..< ?n]" 
  have p1: "\<And> u v. (u,v) \<in> set ?p1 \<Longrightarrow> (u, v) \<in> (rstep R)\<^sup>*" using w by auto
  let ?p2 = "map (\<lambda> i. (snd (pairs ! i), w i)) [0 ..< ?n]" 
  have p2: "\<And> u v. (u,v) \<in> set ?p2 \<Longrightarrow> (u, v) \<in> (rstep R)\<^sup>*" using w by auto
  have [simp]: "map (\<lambda>x. fst (pairs ! x)) [0..<?n] = map fst pairs" by (intro nth_equalityI, auto)
  have [simp]: "map (\<lambda>x. snd (pairs ! x)) [0..<?n] = map snd pairs" by (intro nth_equalityI, auto)
  from args_rewr_impl_full_rewr[of ?p1 R c, OF p1] 
    args_rewr_impl_full_rewr[of ?p2 R c, OF p2] 
  show ?A by (auto simp: o_def)
next
  assume ?A
  define n where n: "n = length pairs" 
  define ls where "ls = map fst pairs" 
  define rs where "rs = map snd pairs" 
  have len: "length ls = n" "length rs = n" using n unfolding ls_def rs_def by auto
  from \<open>?A\<close> have "(Fun c ls, Fun c rs) \<in> join (rstep R)" unfolding ls_def rs_def by auto
  then obtain u where ls: "(Fun c ls, u) \<in> (rstep R)^*" and rs: "(Fun c rs, u) \<in> (rstep R)^*" by auto
  from assms have wf: "\<forall>(l, r)\<in>R. is_Fun l" unfolding wf_trs_def by auto
  from assms[folded n] have ndef: "\<not> defined R (c, n)" 
    using defined_funas_trs by blast
  from nondef_root_imp_arg_steps[OF ls wf, unfolded len, OF ndef]
    nondef_root_imp_arg_steps[OF rs wf, unfolded len, OF ndef]
  obtain us where lenu: "length us = n" and u: "u = Fun c us"
    and ls: "(\<forall>i<n. (ls ! i, us ! i) \<in> (rstep R)\<^sup>*)" 
    and rs: "(\<forall>i<n. (rs ! i, us ! i) \<in> (rstep R)\<^sup>*)" 
    by auto
  {
    fix i
    assume "i < n" 
    with ls rs have "(ls ! i, us ! i) \<in> (rstep R)\<^sup>*" "(rs ! i, us ! i) \<in> (rstep R)\<^sup>*" by auto
    hence "(ls ! i, rs ! i) \<in> join (rstep R)" by auto
  } note main = this
  show ?B 
  proof (intro allI impI)
    fix u v
    assume "(u,v) \<in> set pairs" 
    then obtain i where i: "i < n" and id: "u = ls ! i" "v = rs ! i" 
      using \<open>n = length pairs\<close> unfolding ls_def rs_def by (metis fst_conv in_set_conv_nth nth_map snd_conv)
    from main[OF i]
    show "(u, v) \<in> (rstep R)\<^sup>\<down>" unfolding id .
  qed
qed

lemma args_join_iff_full_join_subst: assumes "wf_trs R" and "(c,length pairs) \<notin> funas_trs R" 
  shows "(Fun c (map fst pairs) \<cdot> \<sigma>, Fun c (map snd pairs) \<cdot> \<sigma>) \<in> join (rstep R)
     \<longleftrightarrow> (\<forall> u v. (u,v) \<in> set pairs \<longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> join (rstep R))" 
proof -
  let ?pairs = "map (\<lambda> (u,v). (u \<cdot> \<sigma>, v \<cdot> \<sigma>)) pairs" 
  have id: "(Fun c (map fst pairs) \<cdot> \<sigma>, Fun c (map snd pairs) \<cdot> \<sigma>)
    = (Fun c (map fst ?pairs), Fun c (map snd ?pairs))" 
    apply (simp, intro conjI)
    subgoal by (induct pairs, auto)
    subgoal by (induct pairs, auto)
    done
  have id2: "(u, v) \<in> set (map (\<lambda>(u, v). (u \<cdot> \<sigma>, v \<cdot> \<sigma>)) pairs) \<longleftrightarrow> (\<exists> u' v'. (u',v') \<in> set pairs \<and> u = u' \<cdot> \<sigma> \<and> v = v' \<cdot> \<sigma>)"
    for u v by auto
  show ?thesis unfolding id
    apply (subst args_join_iff_full_join[OF assms(1)])
    subgoal using assms by auto
    subgoal unfolding id2 by blast
    done
qed

locale list_narrowing = equational_narrowing_unification R DOTEQ TOP R' F D x + multiset_narrowing R DOTEQ TOP R' F D x
  for R::"('f, 'v:: infinite) trs" 
    and DOTEQ :: 'f ("\<doteq>")
    and TOP :: "'f" ("\<top>") 
    and R' :: "('f, 'v:: infinite) trs" 
    and F :: "'f sig" 
    and D :: "'f sig"
    and x :: 'v
begin

context
  fixes c :: 'f and n :: nat
  assumes c: "(c,n) \<notin> F \<union> D" 
begin

lemma funas_trs_R: "funas_trs R \<subseteq> F \<union> D" 
  unfolding R' using R_sig by (auto simp: D funas_trs_def funas_rule_def)

lemma narrowing_step_to_multiset_narrowing_step: assumes "length ts = n" 
  and "(Fun c ts, d, \<sigma>) \<in> narrowing_step" 
shows "\<exists> ss. d = Fun c ss \<and> length ss = n \<and> (mset ts, mset ss, \<sigma>) \<in> multiset_narrowing_step" 
  using assms(2)
proof cases
  case (1 p rl \<omega>)
  show ?thesis
  proof (cases p)
    case Nil
    obtain l r where rl: "rl = (l,r)" by force
    from 1 have mem: "\<omega> \<bullet> rl \<in> R" by auto
    hence "funas_rule (\<omega> \<bullet> rl) \<subseteq> funas_trs R" 
      by (metis SUP_le_iff funas_defs(1) order_le_less)
    also have "\<dots> \<subseteq> F \<union> D" by (simp add: funas_trs_R)
    finally have "funas_rule (\<omega> \<bullet> rl) \<subseteq> F \<union> D" by auto
    from funas_rule_perm[OF this, of "- \<omega>"]
    have "funas_rule rl \<subseteq> F \<union> D" by auto
    with c have c: "(c,n) \<notin> funas_rule rl" by auto
    from rl mem have "(\<omega> \<bullet> l, \<omega> \<bullet> r) \<in> R" by (simp add: rule_pt.permute_prod_eqvt)
    from wf this obtain f ls where "\<omega> \<bullet> l = Fun f ls" unfolding wf_trs_def by blast
    from arg_cong[OF this, of "\<lambda> t. -\<omega> \<bullet> t", simplified] obtain
      ls where l: "l = Fun f ls" by auto
    from 1[unfolded Nil rl l]
    have "mgu (Fun c ts) (Fun f ls) = Some \<sigma>" 
      by simp
    from mgu_sound[OF this, unfolded is_imgu_def, simplified] assms 
    have "(f,length ls) = (c,n)" by auto
    with l have "(c,n) \<in> funas_term l" by auto
    with c have False unfolding rl funas_rule_def by auto
    thus ?thesis by auto
  next
    case (Cons i p')
    let ?n = "length ts" 
    from Cons 1 have 
      i: "i < ?n" and
      p: "p' \<in> fun_poss (ts ! i)" and
      rl: "\<omega> \<bullet> rl \<in> R" and
      vars: "vars_term (Fun c ts) \<inter> vars_rule rl = {}" and
      mgu: "mgu (ts ! i |_ p') (fst rl) = Some \<sigma>" by auto
    let ?ssi = "(ctxt_of_pos_term p' (ts ! i))\<langle>snd rl\<rangle> \<cdot> \<sigma>" 
    from vars and i have vars: "vars_term (ts ! i) \<inter> vars_rule rl = {}" by fastforce
    from narrowing_stepI[OF conjI[OF refl conjI[OF rl conjI[OF vars conjI[OF p mgu]]]]]
    have narrow: "(ts ! i, ?ssi, \<sigma>) \<in> (\<leadsto>)" .
    from 1[unfolded Cons, simplified]
    have d: "d = Fun c (map (\<lambda>s. s \<cdot> \<sigma>) (take i ts) @ ?ssi # map (\<lambda>s. s \<cdot> \<sigma>) (drop (Suc i) ts))" by auto
    have id: "mset ts - {#ts ! i#} = mset (take i ts) + mset (drop (Suc i) ts)" using i
      by (metis add_diff_cancel_right' mset_remove_nth remove_nth_def union_code)
    show ?thesis
      apply (intro exI conjI, rule d)
      subgoal using i assms by auto 
      subgoal apply (intro multiset_narrowing_step.intros[OF conjI[OF _ conjI[OF _ narrow]]])
        subgoal using i by auto
        subgoal using i id by (simp add: subst_term_multiset_def)
        done
      done
  qed
qed

(* Comments by Dohan Kim: Multiset narrowing cannot be simulated by narrowing with the special encoding 
    due to the following reasons. *)

(* this lemma currently is not valid because of different variable conditions, e.g.
   {x,f(a)} multiset-narrows-to {a,b} for R = {f(x) \<rightarrow> b}, but
   c(x,f(a)) just narrows to c(x,b), but not to c(a,b). *)
lemma multiset_narrowing_step_to_narrowing_step:  
  assumes "(S,T,\<sigma>) \<in> multiset_narrowing_step" 
  and S: "S = mset ss" 
shows "\<exists> ts. T = mset ts \<and> (Fun c ss, Fun c ts, \<sigma>) \<in> narrowing_step" 
  using assms(1)
proof cases
  case (1 s t)
  from 1[unfolded S]
  have "s \<in> set ss" by auto
  from split_list[OF this] obtain ss1 ss2 where ss: "ss = ss1 @ s # ss2" by auto
  with S have Ss: "S - {# s #} = mset (ss1 @ ss2)" by auto
  from 1 Ss have narrow: "(s, t, \<sigma>) \<in> (\<leadsto>)" and 
      T: "T = subst_term_multiset \<sigma> (mset (ss1 @ ss2)) + {#t#}" by auto  
  let ?i = "length ss1" 
  show ?thesis
  proof (intro exI[of _ "map (\<lambda> u. u \<cdot> \<sigma>) ss1 @ t # map (\<lambda> u. u \<cdot> \<sigma>) ss2"] conjI)
    show "T = mset (map (\<lambda>u. u \<cdot> \<sigma>) ss1 @ t # map (\<lambda>u. u \<cdot> \<sigma>) ss2)" 
      unfolding T subst_term_multiset_def by auto
    show "(Fun c ss, Fun c (map (\<lambda>u. u \<cdot> \<sigma>) ss1 @ t # map (\<lambda>u. u \<cdot> \<sigma>) ss2), \<sigma>) \<in> (\<leadsto>)" 
      using narrow
    proof (cases)
      case *: (1 p rl \<omega>)
      from * have vars: "vars_term s \<inter> vars_rule rl = {}" by auto
      show ?thesis 
      proof (intro narrowing_step.intros[where rl = rl and \<omega> = \<omega> and p = "?i # p"] conjI)
        show "mgu (Fun c ss |_ (length ss1 # p)) (fst rl) = Some \<sigma>" unfolding ss using * by auto
        show "length ss1 # p \<in> fun_poss (Fun c ss)" unfolding ss using * by auto
        show "Fun c (map (\<lambda>u. u \<cdot> \<sigma>) ss1 @ t # map (\<lambda>u. u \<cdot> \<sigma>) ss2) =
          (ctxt_of_pos_term (length ss1 # p) (Fun c ss))\<langle>snd rl\<rangle> \<cdot> \<sigma>" unfolding ss using * by simp
        show "\<omega> \<bullet> rl \<in> R" using * by simp
        show "vars_term (Fun c ss) \<inter> vars_rule rl = {}" using vars
            (* here there is some deviation in the variable condition of multiset-narrowing and usual narrowing *)
          oops
end

lemma R_unif_to_E_unif: assumes "n = length (pairs :: ('f,'v)rule list)" 
  and c: "(c,n) \<notin> funas_trs R" 
  and "CR (rstep R)" (* only required for the right-to-left direction *)
shows "R_unifiable pairs = E_unifiable (Fun c (map fst pairs), Fun c (map snd pairs))" 
  using args_join_iff_full_join_subst[OF wf c[unfolded assms(1)]] 
    CR_imp_conversionIff_join[OF assms(3)]
  unfolding R_unifiable_def E_unifiable_def by auto

theorem narrowing_based_R_unifiability: 
  assumes semi_comp:"semi_complete (rstep R)"
    and funas_trs:"funas_trs (set C) \<subseteq> F"
    and c: "(c,length C) \<in> F" "(c,length C) \<notin> funas_trs R" 
  shows "narrowing_derivation_reaches_to_success (Fun c (map fst C), Fun c (map snd C)) \<Longrightarrow> R_unifiable C" (is "?A \<Longrightarrow> ?B")
        "\<not> narrowing_derivation_reaches_to_success (Fun c (map fst C), Fun c (map snd C)) \<Longrightarrow> \<not> R_unifiable C" (is "?C \<Longrightarrow> ?D")
proof -
  from semi_comp have wn:"WN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: semi_complete_on_def, insert semi_comp, auto)
  let ?s = "Fun c (map fst C)" 
  let ?t = "Fun c (map snd C)" 
  let ?c = "(c,length C)" 
  have "funas_rule (?s,?t) = insert ?c (funas_trs (set C))" 
    unfolding funas_rule_def funas_trs_def by auto
  also have "\<dots> \<subseteq> F" using assms by auto
  finally have funas: "funas_rule (?s,?t) \<subseteq> F" .
  from R_unif_to_E_unif[OF refl c(2) cr]
  have "R_unifiable C = E_unifiable (?s,?t)" .
  from narrowing_based_E_unifiability[OF semi_comp funas, folded this]
  show "?A \<Longrightarrow> ?B" "?C \<Longrightarrow> ?D" by auto
qed

theorem narrowing_based_completeness_of_E_unification_multiple_pairs:
  assumes semi_comp:"semi_complete (rstep R)"
    and "funas_trs (set C) \<subseteq> F"
    and "(c,length C) \<in> F"  
    and R_unif:"\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"    
  shows "\<exists>\<tau> \<theta>. narrowing_derivation (Fun \<doteq> [Fun c (map fst C), Fun c (map snd C)]) (Fun \<top> []) \<tau> \<and> 
            \<tau> \<circ>\<^sub>s \<theta> |s vars_trs (set C) =\<^sub>R \<sigma> |s vars_trs (set C)"
proof - 
  from semi_comp have wn:"WN (rstep R)" and cr:"CR (rstep R)" 
    by (simp add: semi_complete_on_def, insert semi_comp, auto)
  let ?s = "Fun c (map fst C)" 
  let ?t = "Fun c (map snd C)" 
  let ?c = "(c,length C)" 
  have "funas_rule (?s,?t) = insert ?c (funas_trs (set C))" 
    unfolding funas_rule_def funas_trs_def by auto
  also have "\<dots> \<subseteq> F" using assms by auto
  finally have funas: "funas_rule (?s,?t) \<subseteq> F" .
  have vars: "vars_term ?s \<union> vars_term ?t = vars_trs (set C)" 
    by (auto simp: vars_trs_def vars_rule_def)
  from R_unif args_convs_impl_full_conv_subst[of C \<sigma>]
  have conv: "(?s \<cdot> \<sigma>, ?t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" by auto
  from narrowing_based_completeness_of_E_unification[OF semi_comp funas conv, unfolded vars]
  show ?thesis .
qed

lemma reachability_to_reachable: assumes "n = length (pairs :: ('f,'v)rule list)" 
  and "(c,n) \<notin> funas_trs R" 
shows "reachability pairs = reachable (Fun c (map fst pairs), Fun c (map snd pairs))" 
proof
  assume "reachability pairs" 
  from this[unfolded reachability_def] obtain \<tau> where 
    rewr: "(u,v) \<in> set pairs \<Longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)^*" for u v by auto
  let ?pairs = "map (\<lambda> (u,v). (u \<cdot> \<tau>, v \<cdot> \<tau>)) pairs" 
  from rewr have rewr: "(u,v) \<in> set ?pairs \<Longrightarrow> (u, v) \<in> (rstep R)^*" for u v by auto
  have [simp]: "fst (case x of (u, v) \<Rightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>)) = fst x \<cdot> \<tau>" for x by (cases x, auto)
  have [simp]: "snd (case x of (u, v) \<Rightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>)) = snd x \<cdot> \<tau>" for x by (cases x, auto)
  from args_rewr_impl_full_rewr[OF rewr, of ?pairs c]
  show "reachable (Fun c (map fst pairs), Fun c (map snd pairs))" 
    unfolding reachable_def by (intro exI[of _ \<tau>], auto simp: o_def)
next
  let ?ls = "map fst pairs" 
  let ?rs = "map snd pairs" 
  assume "reachable (Fun c ?ls, Fun c ?rs)"
  from this[unfolded reachable_def] obtain \<tau> where 
    conv: "(Fun c ?ls \<cdot> \<tau>, Fun c ?rs \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" by auto
  define ls where "ls = map (\<lambda> t. t \<cdot> \<tau>) ?ls" 
  define rs where "rs = map (\<lambda> t. t \<cdot> \<tau>) ?rs" 
  have len: "length ls = n" "length rs = n" using assms unfolding ls_def rs_def by auto
  from conv have rewr: "(Fun c ls, Fun c rs) \<in> (rstep R)\<^sup>*" unfolding ls_def rs_def by auto
  from wf have wf: "\<forall>(l, r)\<in>R. is_Fun l" unfolding wf_trs_def by auto
  from assms(2) have ndef: "\<not> defined R (c, n)" 
    using defined_funas_trs by blast
  from nondef_root_imp_arg_steps[OF rewr wf, unfolded len, OF ndef]    
  have main: "\<And> i. i < n \<Longrightarrow> (ls ! i, rs ! i) \<in> (rstep R)\<^sup>*" 
    by auto
  show "reachability pairs" unfolding reachability_def  
  proof (intro exI[of _ \<tau>] allI impI)
    fix u v
    assume "(u,v) \<in> set pairs" 
    then obtain i where i: "i < n" and id: "u = ?ls ! i" "v = ?rs ! i" 
      using \<open>n = length pairs\<close> by (metis fst_conv in_set_conv_nth nth_map snd_conv)
    from main[OF i]
    show "(u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" 
      unfolding id ls_def rs_def using i \<open>n = length pairs\<close> by force
  qed
qed

theorem narrowing_based_reachability_multiple_term_pairs: 
  assumes semi_comp:"semi_complete (rstep R)"
    and funas_trs:"funas_trs (set C) \<subseteq> F"
    and c: "(c,length C) \<in> F" "(c,length C) \<notin> funas_trs R" 
shows "\<forall> (u, v) \<in> set C. strongly_irreducible_term R v \<Longrightarrow>
   narrowing_derivation_reaches_to_success (Fun c (map fst C), Fun c (map snd C)) \<Longrightarrow> reachability C" (is "?sti \<Longrightarrow> ?A \<Longrightarrow> ?B")
    "\<not> narrowing_derivation_reaches_to_success (Fun c (map fst C), Fun c (map snd C)) \<Longrightarrow> infeasibility C" (is "?C \<Longrightarrow> ?D")
proof -
  let ?s = "Fun c (map fst C)" 
  let ?t = "Fun c (map snd C)" 
  let ?c = "(c,length C)" 
  have "funas_rule (?s,?t) = insert ?c (funas_trs (set C))" 
    unfolding funas_rule_def funas_trs_def by auto
  also have "\<dots> \<subseteq> F" using assms by auto
  finally have funas: "funas_rule (?s,?t) \<subseteq> F" .
  from reachability_to_reachable[OF refl c(2)]
  have id1: "reachability C = reachable (?s,?t)" .
  hence id2: "infeasibility C = infeasible (?s,?t)" 
    unfolding infeasibility_def infeasible_def reachability_def reachable_def by blast
  from narrowing_based_infeasibility_implies_infeasible[OF semi_comp funas, folded id1 id2]
  show "?C \<Longrightarrow> ?D" .
  assume sti: ?sti
  have "strongly_irreducible_term R ?t" unfolding strongly_irreducible_term_def
  proof (intro allI impI NF_I notI)
    fix \<sigma> b
    assume sig: "normal_subst R \<sigma>" and step: "(?t \<cdot> \<sigma>, b) \<in> rstep R" 
    from wf have wf: "\<forall>(l, r)\<in>R. is_Fun l" unfolding wf_trs_def by auto
    from c(2) have ndef: "\<not> defined R ?c" using defined_funas_trs by blast
    from step have "(Fun c (map (\<lambda> t. t \<cdot> \<sigma>) (map snd C)), b) \<in> rstep R" by auto
    from nondef_root_imp_arg_step[OF this wf, unfolded length_map, OF ndef]
    obtain i b where i: "i < length C" and step: "((map snd C) ! i \<cdot> \<sigma>, b) \<in> rstep R" by auto
    from i have "(map fst C ! i, map snd C ! i) \<in> set C" by auto
    from sti[rule_format, OF this] have "strongly_irreducible_term R (map snd C ! i)" by auto
    with step sig show False unfolding strongly_irreducible_term_def by auto
  qed    
  from narrowing_based_reachability[OF semi_comp funas this, folded id1 id2]
  show "?A \<Longrightarrow> ?B" by auto
qed

end
end

