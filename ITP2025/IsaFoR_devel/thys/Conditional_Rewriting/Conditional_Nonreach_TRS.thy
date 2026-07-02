theory Conditional_Nonreach_TRS
  imports Ord.Term_Order
    Conditional_Rewriting
    Ord.Poly_Order
    Ord.Poly_Order_Neg
    Ord.CoWPO
begin

context co_rewrite_pair
begin

lemma cstep_NS:assumes "\<forall>s t. (s, t) \<in> (cstep_n R n) \<longrightarrow> (s, t) \<in> NS"
  shows "(u, v) \<in> (cstep_n R n)\<^sup>* \<Longrightarrow> (u, v) \<in> NS"
proof -
  assume "(u, v) \<in> (cstep_n R n)\<^sup>*"
  then show "(u, v) \<in> NS" 
  proof(induct)
    case base
    then show ?case by (simp add: reflD refl_NS)
  next
    case (step y z)
    from step(2) have "(y, z) \<in> NS" using assms by auto
    then show ?case using \<open>(u, y) \<in> NS\<close> \<open>(y, z) \<in> NS\<close> 
      by (metis refl_NS rtrancl_trans trans_NS trans_refl_imp_rtrancl_id)
  qed
qed

lemma cstep_ns_star: assumes "\<forall>l r cs. ((l, r), cs) \<in> R \<longrightarrow> ((l, r) \<in> NS \<or> (\<exists> u v. (u, v) \<in> set cs \<and> (u, v) \<in> S^-1))"
  and st:"(s, t) \<in> (cstep R)\<^sup>*"
shows "(s, t) \<in> NS" using st
proof(induct)
  case base
  then show ?case using refl_NS trans_NS trans_refl_imp_rtrancl_id by auto
next
  case (step y z)
  from step(2)  obtain n where yz:"(y, z) \<in> (cstep_n R n)"
    using cstep_iff by blast
  have "(y, z) \<in> NS" using yz
  proof(induct n arbitrary:y z)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    from \<open>(y, z) \<in> cstep_n R (Suc n)\<close> obtain C l r cs \<tau>
      where lrcs:"((l, r), cs) \<in> R" and cond:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<tau>, t\<^sub>i \<cdot> \<tau>) \<in> (cstep_n R n)\<^sup>*"
        and y:"y = C\<langle>l \<cdot> \<tau>\<rangle>" and z:"z = C\<langle>r \<cdot> \<tau>\<rangle>" by (rule cstep_n_SucE)
    have "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<tau>, t\<^sub>i \<cdot> \<tau>) \<in> NS" using cond Suc(1) 
      by (auto split:prod.splits, insert cstep_NS, metis)
    hence "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. \<not> (s\<^sub>i \<cdot> \<tau>, t\<^sub>i \<cdot> \<tau>) \<in> S^-1" using disj_NS_S by auto
    hence "\<forall>l r. ((l, r), cs) \<in> R \<longrightarrow> (l, r) \<in> NS" using assms(1) 
      by (auto, metis S_stable old.prod.case)
    hence "\<forall>l r \<tau>. ((l, r), cs) \<in> R \<longrightarrow> (l \<cdot> \<tau>, r \<cdot> \<tau>) \<in> NS" using NS_stable by blast
    hence "\<forall>l r \<tau> C. ((l, r), cs) \<in> R \<longrightarrow> (C\<langle>l \<cdot> \<tau>\<rangle>, C\<langle>r \<cdot> \<tau>\<rangle>) \<in> NS" using ctxt_NS by blast
    then show ?case using Suc lrcs y z by (auto split:prod.splits)
  qed
  then show ?case using yz step 
    by (metis refl_NS rtrancl_trans trans_NS trans_refl_imp_rtrancl_id)
qed

(* The following theorem is a formalization of Proposition 4 in Term Orderings for Non-reachability of (Conditional) Rewriting by Yamada *)
theorem conditional_nonreach: assumes "\<forall>l r cs. ((l, r), cs) \<in> R \<longrightarrow> ((l, r) \<in> NS \<or> (\<exists> u v. (u, v) \<in> set cs \<and> (u, v) \<in> S^-1))"
  and "(s, t) \<in> S^-1"
shows "\<not> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)" 
  using cstep_ns_star S_stable converseI disj_NS_S disjoint_iff_not_equal assms 
  by (metis (no_types, lifting) converseD)

(* Proposition 6.1 *)
proposition conditional_nonreach_prop: assumes "\<forall>l r cs. ((l, r), cs) \<in> R \<longrightarrow> ((l, r) \<in> NS)"
  and "\<forall>i \<le> n. (s i, t i) \<in> S^-1"
shows "\<forall>i \<le> n. \<not> (\<exists>\<tau>. ((s i) \<cdot> \<tau>, (t i)\<cdot> \<tau>) \<in> (cstep R)\<^sup>*)" 
  using assms conditional_nonreach by (auto, meson)
end

(* Theorem 2 in Term Orderings for Non-reachability of (Conditional) Rewriting by Yamada *)
theorem co_rewrite_non_reach:"\<not> (\<exists> \<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)^*) \<Longrightarrow> \<exists>S NS. co_rewrite_pair S NS \<and> R \<subseteq> NS \<and> (s, t) \<in> S^-1"
  "\<exists>S NS. co_rewrite_pair S NS \<and> R \<subseteq> NS \<and> (s, t) \<in> S^-1 \<Longrightarrow> \<not> (\<exists> \<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)^*)"
proof(goal_cases)
  case 1
  then show ?case
  proof -
    let ?NS = "(rstep R)^*"
    let ?rstep_unsat = "\<lambda>R. {(t, s) | s t . \<not> (\<exists> \<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)^*)}"
    let ?S = "(?rstep_unsat R)"
    have co:"co_rewrite_pair ?S ?NS"
    proof
      show "ctxt.closed ((rstep R)\<^sup>*)" by auto
      show "subst.closed ?S"  
        by (smt (verit, ccfv_threshold) fst_conv mem_Collect_eq snd_conv subst.closedI subst_subst)
      show "subst.closed ((rstep R)\<^sup>*)" by auto
      show "refl ((rstep R)\<^sup>*)" by (simp add: refl_rtrancl)
      show "trans ((rstep R)\<^sup>*)" using trans_rtrancl by blast
      show "?NS \<inter> (?S)\<inverse> = {}"  using rstep_rtrancl_idemp by blast
    qed
    have R_NS:"R \<subseteq> ?NS" by auto
    have *: "(t, s) \<in> ?S" using 1 by blast
    show ?thesis by (rule exI[of _ ?S], rule exI[of _ ?NS], insert co R_NS *, auto)
  qed
next
  case 2
  then obtain S NS where co:"co_rewrite_pair S NS" and R_NS:"R \<subseteq> NS" and st:"(s, t) \<in> S\<inverse>" by auto
  then show ?case
  proof (intro notI, elim exE)
    fix \<sigma>
    assume asm:"(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*"
    have rstep_imp_NS: "rstep R \<subseteq> NS" using R_NS
      by (meson co co_rewrite_pair.axioms(1) rewrite_pair_def rstep_subset)
    moreover have rsteps_imp_NS: "(rstep R)^* \<subseteq> NS" 
      using co by (auto, metis co_rewrite_pair.refl_NS co_rewrite_pair.trans_NS rstep_imp_NS 
          rtrancl_mono_mp trans_refl_imp_rtrancl_id)
    ultimately  have "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS" unfolding co_rewrite_pair_def
      using asm by blast
    hence "(t \<cdot> \<sigma>, s \<cdot> \<sigma>) \<notin> S" 
      using co co_rewrite_pair.disj_NS_S by auto
    then show False using co 
      by (simp add: co_rewrite_pair_def rewrite_pair_def subst.closedD, insert st, auto) 
  qed
qed


context cowpo_with_assms
begin

corollary corollary_WPO_co_WP: assumes ss:"strictly_simple_status \<pi> NS"
  and ctxt_NS: "ctxt.closed NS"
  and prc_compat: "prc_compat' gt_prc ge_prc"
  and cLex: "c = (\<lambda> _. Lex)"
  and *:"\<forall>l r cs. ((l, r), cs) \<in> R \<longrightarrow> ((l, r) \<in> WPO_NS \<or> (\<exists> u v. (u, v) \<in> set cs \<and> (u, v) \<in> COWPO_S^-1))"
  and **:"(s, t) \<in> COWPO_S^-1"
shows "\<not> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)" 
proof -
  from assms have "co_rewrite_pair COWPO_S WPO_NS" using co_rewrite_pair_wpo_cowpo by auto
  then show ?thesis using co_rewrite_pair.conditional_nonreach[of COWPO_S WPO_NS R s t] using * ** by auto
qed

end

locale poly_order_co_rewrite =  pre_poly_order default gt power_mono discrete I UNIV 
  for default :: "'a :: large_ordered_semiring_1" and gt (infix "\<succ>" 50) 
    and power_mono :: bool
    and discrete :: bool 
    and I :: "('f, 'a) poly_inter" +
  assumes mono_I:"\<And>fn. poly_weak_mono_all (I fn)"
    and irrefl: "x \<succ> x \<Longrightarrow> False"
begin

lemma irrefl_poly_gt: "\<not> s >p s"
proof
  assume "s >p s" 
  thus False unfolding poly_gt_def
  proof (induct s)
    case Nil
    have ea:"eval_poly \<alpha> [] \<succ> eval_poly \<alpha> [] \<Longrightarrow> False" for \<alpha>:: "('b :: linorder, 'a :: large_ordered_semiring_1 )assign" 
    proof -
      assume asm:"(eval_poly \<alpha> []) \<succ> (eval_poly \<alpha> [])"
      have "eval_poly \<alpha> [] = 0" by simp
      then show ?thesis using asm irrefl by auto
    qed
    from Nil show ?case unfolding pos_assign_def using  ge_refl ea by force
  next
    case (Cons a s)
    have pe:"pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> s \<succ> eval_poly \<alpha> s \<Longrightarrow> False" for \<alpha>::"('b::linorder,'a :: large_ordered_semiring_1)assign"
      using irrefl by auto
    hence pe_app:"pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (a # s)  \<succ> eval_poly \<alpha> (a # s) \<Longrightarrow> False" for \<alpha>:: "('b::linorder,'a :: large_ordered_semiring_1)assign" 
      using irrefl by blast
    show ?case unfolding pos_assign_def eval_poly.simps using Cons pe pe_app by force
  qed
qed

lemma co_rewrite_pair_poly: "co_rewrite_pair inter_s inter_ns"
proof
  show "ctxt.closed inter_ns"
  proof (rule one_imp_ctxt_closed)
    fix f bef and s t :: "('f,'v :: linorder)term" and aft 
    assume st: "(s,t) \<in> inter_ns"
    show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> inter_ns" (is "(Fun f ?s, Fun f ?t) \<in> _")
      unfolding inter_ns_def poly_ge_def
    proof (clarify)
      fix \<alpha> :: "('v,'a)assign"
      assume pos: "pos_assign \<alpha>"
      let ?n = "Suc (length bef + length aft)"
      let ?i = "length bef"
      from mono_I[of "(f,?n)"] have mono: "poly_weak_mono (I (f,?n)) ?i" by (rule poly_weak_mono_all)
      let ?exp = "\<lambda> w s.  (if w < ?n then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! w else zero_poly)"
      {
        fix w
        assume "?i \<noteq> w"
        then have "?exp w s = ?exp w t" by (simp add: nth_append)
      } note one = this
      {
        fix w
        have "\<exists> ts. (?exp w t = (if w < length ts then (map (eval_term I) ts) ! w else zero_poly))"
          by (rule exI[of _ ?t], simp only: map_append, simp)
        then obtain ts where id: "?exp w t = (if w < length ts then (map (eval_term I) ts) ! w else zero_poly)" by blast
        have "?exp w t \<ge>p zero_poly" 
          by (simp only: id, unfold poly_ge_def zero_poly_def, simp add: ge_refl, intro impI allI, force simp: eval_term_pos[unfolded poly_ge_def zero_poly_def, simplified])
      } note two = this 
      have "eval_poly \<alpha> (poly_subst (\<lambda>i. if i < ?n then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! i else zero_poly) (I (f,?n))) \<ge>
        eval_poly \<alpha> (poly_subst (\<lambda>i. if i < ?n then (map (eval_term I) bef @ eval_term I t # map (eval_term I) aft) ! i else zero_poly) (I (f,?n)))"
        by (rule poly_weak_mono_E[OF mono, unfolded poly_ge_def, rule_format, OF _ _ _ pos])
          ((auto simp: one two ge_refl two[unfolded poly_ge_def])[2], simp add: nth_append st[unfolded inter_ns_def poly_ge_def, simplified])
      then show "eval_poly \<alpha> (eval_term I (Fun f ?s)) \<ge> eval_poly \<alpha> (eval_term I (Fun f ?t))" by simp
    qed
  qed
  show "subst.closed inter_s" using F_subst_closed_UNIV F_subst_closed_inter_s by auto
  show "subst.closed inter_ns" using F_subst_closed_UNIV F_subst_closed_inter_ns by auto
  show "refl inter_ns" using refl_inter_ns by auto
  show "trans inter_ns" using trans_inter_ns by auto
  show "inter_ns \<inter> inter_s\<inverse> = {}" unfolding inter_ns_def inter_s_def
  proof(safe)
    fix a b::"('f,'v::linorder)term"
    assume asm1:"eval_term I a \<ge>p eval_term I b"
    assume asm2:"eval_term I b >p eval_term I a"
    from asm1 asm2 have "eval_term I a >p eval_term I a"
      using poly_compat by blast
    then show "(a, b) \<in> {}" using irrefl_poly_gt by auto 
  qed
qed

corollary poly_order_infeasibility: fixes s t::"('f,'v::linorder) term" 
  assumes "\<forall>l r cs. ((l, r), cs) \<in> R \<longrightarrow> ((l, r) \<in> inter_ns \<or> (\<exists> u v. (u, v) \<in> set cs \<and> (u, v) \<in> inter_s^-1))"
    and "(s, t) \<in> inter_s^-1"
  shows "\<not> (\<exists>(\<tau>::('f,'v)subst). (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)" 
proof -
  have co:"co_rewrite_pair inter_s inter_ns"
    by (simp add: co_rewrite_pair_poly)
  have "\<not> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)" using co_rewrite_pair.conditional_nonreach[of inter_s inter_ns R s t] 
    using co assms by auto
  then show ?thesis by auto
qed

end

context poly_order_neg
begin

corollary poly_order_neg_infeasibility: fixes s t::"('f,'v::linorder) term" 
  assumes "\<forall>l r cs. ((l, r), cs) \<in> R \<longrightarrow> ((l, r) \<in> inter_neg_ns \<or> (\<exists> u v. (u, v) \<in> set cs \<and> (u, v) \<in> inter_neg_s^-1))"
    and "(s, t) \<in> inter_neg_s^-1"
  shows "\<not> (\<exists>(\<tau>::('f,'v)subst). (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)" 
proof -
  have co:"co_rewrite_pair inter_neg_s inter_neg_ns"
    using F_Univ co_rewrite_pair_poly by blast
  have "\<not> (\<exists>\<tau>. (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)" using co_rewrite_pair.conditional_nonreach[of inter_neg_s inter_neg_ns R s t] 
    using co assms by auto
  then show ?thesis by auto
qed

end

end