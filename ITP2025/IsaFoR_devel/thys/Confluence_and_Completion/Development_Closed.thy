(*
Author:  Christina Kirk (Kohl) <christina.kirk@uibk.ac.at> (2022-2023)
License: LGPL (see file COPYING.LESSER)
*)
theory Development_Closed
imports
  Proof_Terms_Term_Rewriting.Labels_and_Overlaps    
  First_Order_Rewriting.Critical_Pairs
  Weighted_Path_Order.Relations
  First_Order_Rewriting.Unification_More
  TRS.More_Abstract_Rewriting
  Auxx.Util
begin

context
  fixes ren :: "'v :: infinite renaming2" 
begin
abbreviation "rename_x \<equiv> map_vars_term (rename_1 ren)"
abbreviation "rename_y \<equiv> map_vars_term (rename_2 ren)"

lemma inj_rename[simp,intro]: "inj_on (rename_1 ren) S"  "inj_on (rename_2 ren) S" 
  using rename_12[of ren] by (metis injD inj_on_def)+

lemma linear_rename_x: "linear_term s \<Longrightarrow> linear_term (rename_x s)" 
  by (auto intro!: linear_term_map_inj_on_linear_term)

lemma linear_rename_y: "linear_term s \<Longrightarrow> linear_term (rename_y s)" 
  by (auto intro!: linear_term_map_inj_on_linear_term)

lemma distinct_vars:
  assumes "linear_term s" "linear_term t"
  shows "distinct (vars_term_list (rename_x s) @ vars_term_list (rename_y t))" (is "distinct (?xs @ ?ys)") 
proof-
  from assms(1) have "linear_term (rename_x s)" by (rule linear_rename_x)
  then have dist1:"distinct ?xs" 
    using linear_term_var_vars_term_list by (metis comp_eq_dest_lhs distinct_remdups distinct_rev)
  from assms(2) have "linear_term (rename_y t)" by (rule linear_rename_y)
  then have dist2:"distinct ?ys" 
    using linear_term_var_vars_term_list by (metis comp_eq_dest_lhs distinct_remdups distinct_rev)
  {fix x assume xs:"x \<in> vars_term (rename_x s)" and xt:"x \<in> vars_term (rename_y t)"
    from xs have "x \<in> range (rename_1 ren)" 
      by (metis image_mono subsetD term.set_map(2) top_greatest)
    moreover from xt have "x \<in> range (rename_2 ren)"
      by (metis image_mono subsetD term.set_map(2) top_greatest)
    ultimately have False using rename_12[of ren] by auto
  }
  then have "set ?xs \<inter> set ?ys = {}" 
    unfolding set_vars_term_list by blast 
  with dist1 dist2 show ?thesis by simp
qed

lemma mk_subst_rename_x:
  assumes "length (vars_distinct t) = length xs"
  shows "t \<cdot> (mk_subst Var (zip (vars_distinct t) xs)) = (rename_x t) \<cdot> (mk_subst Var (zip (vars_distinct (rename_x t)) xs))" 
proof-
  {fix x assume "x \<in> vars_term t" 
    then obtain i where i:"x = (vars_distinct t)!i" "i < length (vars_distinct t)"
      by (metis in_set_conv_nth set_vars_term_list vars_term_list_vars_distinct) 
    with assms have 1:"(mk_subst Var (zip (vars_distinct t) xs)) x = xs!i" 
      using mk_subst_distinct by (metis comp_apply distinct_remdups distinct_rev) 
    have "vars_distinct (rename_x t) = map (rename_1 ren) (vars_distinct t)" 
      unfolding vars_map_vars_term[symmetric] comp_apply
      by (metis distinct_map distinct_remdups distinct_remdups_id inj_rename(1) remdups_map_remdups rev_map) 
    with assms i have 2:"(mk_subst Var (zip (vars_distinct (rename_x t)) xs)) ((rename_1 ren) x) = xs!i"
      by (metis (mono_tags, lifting) comp_apply distinct_remdups distinct_rev length_map mk_subst_same nth_map) 
    from 1 2 have "(mk_subst Var (zip (vars_distinct t) xs)) x = (mk_subst Var (zip (vars_distinct (rename_x t)) xs)) ((rename_1 ren) x)"
      by presburger
  }
  then show ?thesis
    by (simp add: apply_subst_map_vars_term term_subst_eq_conv) 
qed

(*TODO: refactor since this is copy of lemma above!*)
lemma mk_subst_rename_y:
  assumes "length (vars_distinct t) = length xs"
  shows "t \<cdot> (mk_subst Var (zip (vars_distinct t) xs)) = (rename_y t) \<cdot> (mk_subst Var (zip (vars_distinct (rename_y t)) xs))" 
proof-
  {fix x assume "x \<in> vars_term t" 
    then obtain i where i:"x = (vars_distinct t)!i" "i < length (vars_distinct t)"
      by (metis in_set_conv_nth set_vars_term_list vars_term_list_vars_distinct) 
    with assms have 1:"(mk_subst Var (zip (vars_distinct t) xs)) x = xs!i" 
      using mk_subst_distinct by (metis comp_apply distinct_remdups distinct_rev) 
    have "vars_distinct (rename_y t) = map (rename_2 ren) (vars_distinct t)" 
      unfolding vars_map_vars_term[symmetric] comp_apply
      by (metis distinct_map distinct_remdups distinct_remdups_id inj_rename(2) remdups_map_remdups rev_map) 
    with assms i have 2:"(mk_subst Var (zip (vars_distinct (rename_y t)) xs)) ((rename_2 ren) x) = xs!i"
      by (metis (mono_tags, lifting) comp_apply distinct_remdups distinct_rev length_map mk_subst_same nth_map) 
    from 1 2 have "(mk_subst Var (zip (vars_distinct t) xs)) x = (mk_subst Var (zip (vars_distinct (rename_y t)) xs)) ((rename_2 ren) x)"
      by presburger
  }
  then show ?thesis
    by (simp add: apply_subst_map_vars_term term_subst_eq_conv) 
qed

text\<open>Define critical peak as pair of two proof terms.\<close>
(*New definition here since the other definition of critical_peaks in Decreasing_Diagrams2 is not 
sufficient (it is not defined for two different TRSs R and S). Using proof terms here to see
if it is simpler than using something like the ('f, 'v) step type in Decreasing_Diagrams2.*)
definition pterm_cpeaks :: "('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> (('f, 'v) pterm \<times> ('f, 'v) pterm) set"
  where "pterm_cpeaks R S = {(C\<langle>Prule \<alpha> (map (to_pterm \<circ> \<tau>) (var_rule \<alpha>))\<rangle>, Prule \<beta> (map (to_pterm \<circ> \<sigma>) (var_rule \<beta>))) 
  | \<alpha> \<beta> p C \<sigma> \<tau>. to_rule \<alpha> \<in> R \<and> to_rule \<beta> \<in> S \<and> p \<in> fun_poss (lhs \<beta>) \<and>
  C = to_pterm_ctxt (ctxt_of_pos_term p (lhs \<beta> \<cdot> \<sigma>)) \<and> 
  mgu_vd ren ((lhs \<beta>)|_p) (lhs \<alpha>) = Some (\<sigma>, \<tau>) }"

lemma pterm_cpeaksI:
  assumes "to_rule \<alpha> \<in> R" and "to_rule \<beta> \<in> S"
    and "p \<in> fun_poss (lhs \<beta>)"
    and "mgu_vd ren ((lhs \<beta>)|_p) (lhs \<alpha>) = Some (\<sigma>, \<tau>)"
    and "C = to_pterm_ctxt (ctxt_of_pos_term p (lhs \<beta> \<cdot> \<sigma>))"
  shows "(C\<langle>Prule \<alpha> (map (to_pterm \<circ> \<tau>) (var_rule \<alpha>))\<rangle>, Prule \<beta> (map (to_pterm \<circ> \<sigma>) (var_rule \<beta>))) \<in> pterm_cpeaks R S"
  using assms unfolding pterm_cpeaks_def by blast

lemma pterm_cpeak_rstep1:
  assumes "(A, B) \<in> pterm_cpeaks R S"
  shows "(source A, target A) \<in> rstep R"
proof-
  from assms obtain \<alpha> \<beta> p C \<sigma> \<tau> where alpha:"to_rule \<alpha> \<in> R" and "to_rule \<beta> \<in> S"
    and p:"p \<in> fun_poss (lhs \<beta>)"
    and C:"C = to_pterm_ctxt (ctxt_of_pos_term p (lhs \<beta> \<cdot> \<sigma>))"
    and A:"A = C\<langle>Prule \<alpha> (map (to_pterm \<circ> \<tau>) (var_rule \<alpha>))\<rangle>" 
    unfolding pterm_cpeaks_def by blast
  show ?thesis unfolding A C source_to_pterm_ctxt target_to_pterm_ctxt source.simps target.simps map_map using alpha p
    by (smt (verit, ccfv_SIG) comp_apply map_eq_conv rstep.simps source_to_pterm target_to_pterm) 
qed

lemma pterm_cpeak_rstep2:
  assumes "(A, B) \<in> pterm_cpeaks R S"
  shows "(source B, target B) \<in> rstep S"
proof-
  from assms obtain \<beta> \<sigma> where beta:"to_rule \<beta> \<in> S"
    and B:"B = Prule \<beta> (map (to_pterm \<circ> \<sigma>) (var_rule \<beta>))" 
    unfolding pterm_cpeaks_def by blast
  show ?thesis unfolding B source.simps target.simps map_map using beta
    by (smt (verit, ccfv_SIG) comp_apply map_eq_conv rstep_rule rstep_subst source_to_pterm target_to_pterm) 
qed


text\<open>Connection between proof term peaks and the critical pairs.\<close>
lemma pterm_cpeak_to_critical_pair:
  (*use varcond to avoid strange cases when instantiating the right-hand sides of rules*)
  assumes varcond:"\<And>l r. (l, r) \<in> R \<union> S \<Longrightarrow> vars_term r \<subseteq> vars_term l" 
  and "(A, B) \<in> pterm_cpeaks R S" 
  shows "(is_Prule A, target A, target B) \<in> critical_pairs ren S R"
proof-
  from assms obtain \<alpha> \<beta> p C \<sigma> \<tau> where rules:"to_rule \<beta> \<in> S" "to_rule \<alpha> \<in> R" and
  C:"C = to_pterm_ctxt (ctxt_of_pos_term p (lhs \<beta> \<cdot> \<tau>))" and fun_poss:"p \<in> fun_poss (lhs \<beta>)" and
  mgu:"mgu_vd ren ((lhs \<beta>)|_p) (lhs \<alpha>) = Some (\<tau>, \<sigma>)" and
  A:"A = C\<langle>Prule \<alpha> (map (to_pterm \<circ> \<sigma>) (var_rule \<alpha>))\<rangle>" and 
  B:"B = Prule \<beta> (map (to_pterm \<circ> \<tau>) (var_rule \<beta>))"
    unfolding pterm_cpeaks_def by blast
  let ?l="lhs \<alpha>" and ?r="rhs \<alpha>" and ?l'="lhs \<beta>" and ?r'="rhs \<beta>" and ?l''="(lhs \<beta>)|_p" 
  let ?C="ctxt_of_pos_term p ?l'"
  have C_l':"?l' = ?C\<langle>?l''\<rangle>" 
    using fun_poss by (simp add: ctxt_supt_id fun_poss_imp_poss) 
  have is_Fun:"is_Fun (?l' |_ p)"
    by (simp add: fun_poss fun_poss_fun_conv is_Fun_Fun_conv)  
  have tgt_A:"target A = (?C \<cdot>\<^sub>c \<tau>)\<langle>?r \<cdot> \<sigma>\<rangle>" 
    unfolding A C target_to_pterm_ctxt target.simps using lhs_subst_var_rule varcond rules
    unfolding ctxt_of_pos_term_subst[OF fun_poss_imp_poss[OF fun_poss], symmetric]
    by (smt (verit, ccfv_SIG) List.map.compositionality Un_iff target_empty_apply_subst target_to_pterm to_pterm_empty to_pterm_subst)
  have tgt_B:"target B = ?r' \<cdot> \<tau>" unfolding B target.simps using lhs_subst_var_rule varcond rules
    by (smt (verit, del_insts) Un_iff list.map_comp target_empty_apply_subst target_to_pterm to_pterm_empty to_pterm_subst)
  have b:"is_Prule A = (?C = \<box>)" proof(cases p)
    case Nil
    show ?thesis unfolding A C Nil by simp
  next
    case (Cons i p')
    from fun_poss obtain f ts where f:"lhs \<beta> = Fun f ts"
      by (metis Cons_poss_Var fun_poss_imp_poss local.Cons term.exhaust_sel)
    show ?thesis 
      unfolding A C Cons f by simp
  qed               
  show ?thesis using critical_pairsI[OF rules C_l' is_Fun mgu tgt_B tgt_A b] .
qed

text\<open>The set of critical peak steps of TRS S for R.\<close>
definition CPS :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term) set"
  where "CPS R S = {(s,u). \<exists>A B. ((A,B) \<in> pterm_cpeaks R S \<or> (B,A) \<in> pterm_cpeaks S R) \<and> 
                    source B = s \<and> target B = u }"

text\<open>The set of all non-closed critical peak steps of TRS S for R\<close>
definition CPS' :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term) set"
  where "CPS' R S = {(s,u). \<exists>A B.(((A,B) \<in> pterm_cpeaks R S \<and> (target A, target B) \<notin> mstep S) \<or> 
                                 ((B,A) \<in> pterm_cpeaks S R \<and> (target B, target A) \<notin> mstep R)) \<and>
                                  source B = s \<and> target B = u }"

lemma CPS'_subset_CPS: "CPS' R S \<subseteq> CPS R S"
  unfolding CPS'_def CPS_def by auto

text\<open>The set of all non-closed critical peak steps of TRS S for R, using weakening for overlays\<close>
context
  fixes R S :: "('f, 'v) trs" (*Fix R and S, since order matters here. Only one of the TRSs is allowed to have multiple steps.*)
begin

fun is_R_S_closed :: "(('f, 'v) pterm \<times> ('f, 'v) pterm) \<Rightarrow> bool" where
  "is_R_S_closed (A, Prule \<beta> Bs) = (\<exists>v. (target A, v) \<in> mstep S \<and> (target (Prule \<beta> Bs), v) \<in> (rstep R)\<^sup>*)" (* all cases where root step is on the right, including overlays*)
| "is_R_S_closed (Prule \<alpha> As, B) = ((target B, target (Prule \<alpha> As)) \<in> mstep R)"
| "is_R_S_closed _ = False"

definition CPS_R :: "(('f, 'v) term \<times> ('f, 'v) term) set"
  where "CPS_R = {(s,u). \<exists>A B.((A,B) \<in> pterm_cpeaks R S \<or> (B,A) \<in> pterm_cpeaks S R) \<and> \<not> is_R_S_closed (A,B) \<and> source A = s \<and> target A = u}"

definition CPS_S :: "(('f, 'v) term \<times> ('f, 'v) term) set"
  where "CPS_S = {(s,u). \<exists>A B.((A,B) \<in> pterm_cpeaks R S \<or> (B,A) \<in> pterm_cpeaks S R) \<and> \<not> is_R_S_closed (A,B) \<and> source B = s \<and> target B = u}"

lemma CPS_stepI:
  assumes "(A, B) \<in> pterm_cpeaks R S" "\<not> is_R_S_closed (A,B)"
  shows "(source A, target A) \<in> CPS_R" "(source B, target B) \<in> CPS_S" 
proof-
  from assms show "(source A, target A) \<in> CPS_R" unfolding CPS_R_def by blast
  from assms show "(source B, target B) \<in> CPS_S" unfolding CPS_S_def by blast 
qed

lemma CPS_stepI':
  assumes "(B, A) \<in> pterm_cpeaks S R" "\<not> is_R_S_closed (A,B)"
  shows "(source A, target A) \<in> CPS_R" "(source B, target B) \<in> CPS_S" 
proof-
  from assms show "(source A, target A) \<in> CPS_R" unfolding CPS_R_def by blast
  from assms show "(source B, target B) \<in> CPS_S" unfolding CPS_S_def by blast 
qed

lemma CPS_R_rstep:
  assumes "(s, t) \<in> rstep CPS_R"
  shows "(s, t) \<in> rstep R"
proof-
  from rstep_imp_C_s_r[OF assms] obtain C \<sigma> l r where "(l, r) \<in> CPS_R" and s:"s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    by blast
  then obtain A B where "(A,B) \<in> pterm_cpeaks R S \<or> (B,A) \<in> pterm_cpeaks S R"
    and "source A = l \<and> target A = r"
    unfolding CPS_R_def by force
  with pterm_cpeak_rstep1 pterm_cpeak_rstep2  have "(l, r) \<in> rstep R"
    by blast 
  with s t show ?thesis by auto
qed

lemma CPS_S_rstep:
  assumes "(s, t) \<in> rstep CPS_S"
  shows "(s, t) \<in> rstep S"
proof-
  from rstep_imp_C_s_r[OF assms] obtain C \<sigma> l r where "(l, r) \<in> CPS_S" and s:"s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    by blast
  then obtain A B where "(A,B) \<in> pterm_cpeaks R S \<or> (B,A) \<in> pterm_cpeaks S R"
    and "source B = l \<and> target B = r"
    unfolding CPS_S_def by force
  with pterm_cpeak_rstep1 pterm_cpeak_rstep2  have "(l, r) \<in> rstep S"
    by blast 
  with s t show ?thesis by auto
qed

lemma CPS_R_subset_CPS': "CPS_R \<subseteq> CPS' S R"
proof
  fix s t assume "(s,t) \<in> CPS_R" 
  then obtain A B where "((A, B) \<in> pterm_cpeaks R S \<or> (B, A) \<in> pterm_cpeaks S R)" and not_closed:"\<not> is_R_S_closed (A, B)"
    and src_tgt:"source A = s \<and> target A = t"
    unfolding CPS_R_def by fastforce
  then consider "(A, B) \<in> pterm_cpeaks R S" | "(B, A) \<in> pterm_cpeaks S R"
    by fastforce 
  then show "(s,t) \<in> CPS' S R" proof(cases)
    case 1
    then obtain \<beta> Bs where B:"B = Prule \<beta> Bs"  
      unfolding pterm_cpeaks_def by blast 
    with not_closed have "((target A, target B) \<notin> mstep S)" 
      unfolding B using is_R_S_closed.simps by blast 
    with 1 src_tgt show ?thesis unfolding CPS'_def by blast
  next
    case 2
     then obtain \<alpha> As where A:"A = Prule \<alpha> As"  
      unfolding pterm_cpeaks_def by blast 
    then show ?thesis proof(cases "\<exists>\<beta> Bs. B = Prule \<beta> Bs")
      case True
      then obtain \<beta> Bs where B:"B = Prule \<beta> Bs" by fastforce
      with 2 not_closed src_tgt show ?thesis 
        unfolding A B is_R_S_closed.simps CPS'_def using mstep_imp_rsteps by force
    next
      case False
      with not_closed have "((target B, target A) \<notin> mstep R)" unfolding A
        using is_R_S_closed.simps by (smt (verit) Pair_inject is_R_S_closed.elims(3))
      with 2 src_tgt show ?thesis unfolding CPS'_def by blast
    qed
  qed
qed

lemma CPS_S_subset_CPS': "CPS_S \<subseteq> CPS' R S"
proof
  fix s t assume "(s,t) \<in> CPS_S" 
  then obtain A B where "((A, B) \<in> pterm_cpeaks R S \<or> (B, A) \<in> pterm_cpeaks S R)" and not_closed:"\<not> is_R_S_closed (A, B)"
    and src_tgt:"source B = s \<and> target B = t"
    unfolding CPS_S_def by fastforce
  then consider "(A, B) \<in> pterm_cpeaks R S" | "(B, A) \<in> pterm_cpeaks S R"
    by fastforce 
  then show "(s,t) \<in> CPS' R S" proof(cases)
    case 1
    then obtain \<beta> Bs where B:"B = Prule \<beta> Bs"  
      unfolding pterm_cpeaks_def by blast 
    with not_closed have "((target A, target B) \<notin> mstep S)" 
      unfolding B using is_R_S_closed.simps by blast 
    with 1 src_tgt show ?thesis unfolding CPS'_def by blast
  next
    case 2
     then obtain \<alpha> As where A:"A = Prule \<alpha> As"  
      unfolding pterm_cpeaks_def by blast 
    then show ?thesis proof(cases "\<exists>\<beta> Bs. B = Prule \<beta> Bs")
      case True
      then obtain \<beta> Bs where B:"B = Prule \<beta> Bs" by fastforce
      with 2 not_closed src_tgt show ?thesis 
        unfolding A B is_R_S_closed.simps CPS'_def using mstep_imp_rsteps by force
    next
      case False
      with not_closed have "((target B, target A) \<notin> mstep R)" unfolding A
        using is_R_S_closed.simps by (smt (verit) Pair_inject is_R_S_closed.elims(3))
      with 2 src_tgt show ?thesis unfolding CPS'_def by blast
    qed
  qed
qed

end
 
end

locale innermost_overlap =
  fixes ren :: "'v :: infinite renaming2" 
    and R S :: "('a, 'v) trs"
    and A B p q q' p\<^sub>\<alpha> q\<^sub>\<beta> \<alpha> \<beta>
  assumes R:"left_lin_wf_trs R" and S:"left_lin_wf_trs S"
    and co_init:"source A = source B" and A:"A \<in> wf_pterm R" and B:"B \<in> wf_pterm S"
    and pq:"(p, q) \<in> overlaps_pos (labeled_source A) (labeled_source B)"
    and maximal:"\<forall>b\<in> overlaps_pos (labeled_source A) (labeled_source B). (p,q) \<le>\<^sub>o b \<longrightarrow> (p,q) = b"
    and q':"Some q' = remove_prefix q p"
    and alpha:"get_label (labeled_source A |_ p) = Some (\<alpha>, 0)"
    and beta:"get_label (labeled_source B |_ q) = Some (\<beta>, 0)"
    and p\<^sub>\<alpha>:"p\<^sub>\<alpha> \<in> poss A" "ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term p\<^sub>\<alpha> A)" "A|_p\<^sub>\<alpha> = Prule \<alpha> (map (\<lambda>i. A|_(p\<^sub>\<alpha>@[i])) [0..<length (var_rule \<alpha>)])"
    and q\<^sub>\<beta>:"q\<^sub>\<beta> \<in> poss B" "ctxt_of_pos_term q (source B) = source_ctxt (ctxt_of_pos_term q\<^sub>\<beta> B)" "B|_q\<^sub>\<beta> = Prule \<beta> (map (\<lambda>i. B|_(q\<^sub>\<beta>@[i])) [0..<length (var_rule \<beta>)])"
begin

lemma ll_no_var_lhs_R:"left_lin_no_var_lhs R" 
  using R by (simp add: left_lin_no_var_lhs_def left_lin_wf_trs_def wf_trs.axioms(1))

lemma ll_no_var_lhs_S:"left_lin_no_var_lhs S" 
  using S by (simp add: left_lin_no_var_lhs_def left_lin_wf_trs_def wf_trs.axioms(1))

lemma wf_trs_R:"wf_trs R" 
  using R by (simp add: left_lin_wf_trs.axioms(2))

lemma wf_trs_S:"wf_trs S" 
  using S by (simp add: left_lin_wf_trs.axioms(2))

definition "s = source A"

lemma p:"p = q@q'" 
  using q' by (metis remove_prefix_Some) 

lemma le:"q \<le>\<^sub>p p"
  by (metis less_eq_pos_def q' remove_prefix_Some) 

lemma p_q_pos:"p \<in> poss s" "q \<in> poss s" using pq
  using co_init fun_poss_imp_poss s_def by (fastforce)+

abbreviation "\<Delta>1 \<equiv> ll_single_redex s p \<alpha>"
abbreviation "\<Delta>2 \<equiv> ll_single_redex s q \<beta>"

abbreviation "As \<equiv> map (\<lambda>i. A|_(p\<^sub>\<alpha>@[i])) [0..<length (var_rule \<alpha>)]"
abbreviation "Bs \<equiv> map (\<lambda>i. B|_(q\<^sub>\<beta>@[i])) [0..<length (var_rule \<beta>)]"

interpretation single_\<Delta>1:single_redex "R" "A" "\<Delta>1" "p" "p\<^sub>\<alpha>" "\<alpha>"
proof-
  from p_q_pos(1) s_def p\<^sub>\<alpha> show "single_redex R A \<Delta>1 p p\<^sub>\<alpha> \<alpha>" 
    using single_redex.intro[OF ll_no_var_lhs_R] single_redex_axioms.intro[OF A] by simp
qed

interpretation single_\<Delta>2:single_redex "S" "B" "\<Delta>2" "q" "q\<^sub>\<beta>" "\<beta>"
proof-
  from p_q_pos(2) s_def co_init q\<^sub>\<beta> show "single_redex S B \<Delta>2 q q\<^sub>\<beta> \<beta>" 
     using single_redex.intro[OF ll_no_var_lhs_S] single_redex_axioms.intro[OF B] by simp
qed

lemma q'_poss:"q' \<in> fun_poss (lhs \<beta>)"
proof-
  let ?n="length q'"
  from beta pq p have n:"get_label ((labeled_source B)|_p) = Some (\<beta>, ?n)" 
    by force
  have q:"q \<in> poss (labeled_source B)"
    using co_init p_q_pos(2) s_def by auto
  have "labeled_source (B|_q\<^sub>\<beta>) = (labeled_source B)|_q"
    using single_\<Delta>2.labeled_source_at_pq by blast 
  moreover have "is_Fun (lhs \<beta>)"
    using single_\<Delta>2.rule_in_TRS single_\<Delta>2.no_var_lhs by auto 
  moreover have "Prule \<beta> Bs \<in> wf_pterm S"
    by (metis B single_\<Delta>2.aq single_\<Delta>2.q subt_at_is_wf_pterm) 
  ultimately show ?thesis 
    using labeled_poss_in_lhs single_\<Delta>2.a
    by (metis (no_types, lifting) co_init n p p_q_pos(1) q s_def single_\<Delta>2.aq single_\<Delta>2.source_at_pq subt_at_append subterm_poss_conv) 
qed

lemma source_d1: "source \<Delta>1 = s" 
  using s_def single_\<Delta>1.source_delta by simp

lemma source_d2: "source \<Delta>2 = s"
  using s_def co_init single_\<Delta>2.source_delta by simp

abbreviation "l \<equiv> rename_x ren (lhs \<beta>)"
abbreviation "l' \<equiv> rename_y ren (lhs \<alpha>)" 
abbreviation "l'' \<equiv> l|_q'"

lemma l''_alt:"l'' = rename_x ren ((lhs \<beta>)|_q')"
  by (simp add: fun_poss_imp_poss q'_poss)

lemma linear_l:"linear_term l"
  apply (rule linear_rename_x) 
  using single_\<Delta>2.lin_lhs by blast

lemma linear_l':"linear_term l'"
  apply (rule linear_rename_y) 
  using single_\<Delta>1.lin_lhs by blast

lemma linear_l'':"linear_term l''"
  using q'_poss linear_l by (simp add: fun_poss_imp_poss subt_at_linear)

lemma distinct:"distinct ((vars_term_list l) @ (vars_term_list l'))"
  using distinct_vars single_\<Delta>1.lin_lhs single_\<Delta>2.lin_lhs by blast

lemma disjoint_vars:"vars_term l'' \<inter> vars_term l' = {}"
  by (metis distinct_append distinct_vars fun_poss_imp_poss l''_alt q'_poss set_vars_term_list single_\<Delta>1.lin_lhs single_\<Delta>2.lin_lhs subt_at_linear)

lemma length:"length ((map ((|_) (s |_ q)) (var_poss_list l)) @ (map ((|_) (s |_ p)) (var_poss_list l'))) = length (vars_term_list l @ vars_term_list l')"
  by (simp add: length_var_poss_list)

definition "\<tau> = (subst_of ((left_substs l'' l') @ (right_substs l'' l')))"
definition "\<sigma> = mk_subst Var ((match_substs l (s|_q)) @ (match_substs l' (s|_p)))"

lemma \<sigma>_simp:"\<sigma> = mk_subst Var (zip (vars_term_list l @ vars_term_list l') ((map ((|_) (s |_ q)) (var_poss_list l)) @ (map ((|_) (s |_ p)) (var_poss_list l'))))"
  unfolding \<sigma>_def match_substs_def by (simp add: length_var_poss_list)

lemma sigma_vars:
  shows "(\<forall>i<length (vars_term_list l).  \<sigma> (vars_term_list l ! i) = s |_ (q @ var_poss_list l ! i)) \<and>
        (\<forall>i<length (vars_term_list l').  \<sigma> (vars_term_list l' ! i) = s |_ (p @ var_poss_list l' ! i))" (is "?ys \<and> ?xs") 
proof
  {fix j assume j:"j < length (vars_term_list l)"
    let ?y="(vars_term_list l)!j" and ?qj="(var_poss_list l)!j"
    from j have sigma_subst:"\<sigma> ?y = s|_(q@?qj)" 
      unfolding \<sigma>_simp by (smt (z3) append_eq_append_conv distinct filter_cong length length_map length_var_poss_list map_append map_nth_conv mk_subst_same p_q_pos(2) subt_at_append) 
  } then show ?ys by simp
  {fix i assume i:"i < length (vars_term_list l')"
    let ?x="(vars_term_list l')!i" and ?pi="(var_poss_list l')!i"
    from i have sigma_subst:"\<sigma> ?x = s|_(p@?pi)" 
      unfolding \<sigma>_simp by (smt (z3) append_eq_append_conv distinct filter_cong length length_map length_var_poss_list map_append map_nth_conv mk_subst_same p_q_pos(1) subt_at_append) 
  } then show ?xs by simp
qed

lemma apply_tau:
  assumes "(x, u) \<in> set (left_substs l'' l')"
  shows "\<tau> x = u"
proof-
  from assms have "x \<in> vars_term l''"
    using map_fst_left_substs by (metis fst_conv image_eqI list.set_map subsetD) 
  then have "x \<notin> vars_term l'" using distinct_vars
    by (smt (verit, best) disjoint_iff distinct_append fun_poss_imp_poss l''_alt single_\<Delta>1.lin_lhs single_\<Delta>2.lin_lhs q'_poss set_vars_term_list subt_at_linear) 
  moreover have "set (map fst (right_substs l'' l')) \<subseteq> vars_term l'" 
    unfolding right_substs_def using zip_fst by fastforce
  ultimately have "x \<notin> set (map fst (right_substs l'' l'))"
    by blast 
  then have sub1:"subst_of (right_substs l'' l') x = Var x"
    by (meson not_elem_subst_of) 
  have "distinct (map fst (left_substs l'' l'))"
    by (simp add: distinct_map_fst_left_substs linear_l'') 
  then have *:"\<forall>(y, s)\<in>set (left_substs l'' l'). y = x \<longrightarrow> s = u"
    using assms eq_key_imp_eq_value by fastforce 
  have "set (map fst (left_substs l'' l')) \<subseteq> vars_term l''"
    by (meson map_fst_left_substs) 
  moreover have "vars_term l'' \<inter> vars_term u = {}"
  proof-
    from assms have "vars_term u \<subseteq> vars_term l'"
      by (metis left_substs_imp_props vars_term_subt_at)
    then show ?thesis 
      using disjoint_vars by blast 
  qed
  ultimately have "subst_of (left_substs l'' l') x = u"  
    using subst_of_apply[OF assms *] by blast 
  then show ?thesis 
    unfolding \<tau>_def subst_of_append subst_compose using sub1 by simp 
qed

lemma apply_tau2:
  assumes "(y, v) \<in> set (right_substs l'' l')"
  shows "\<tau> y = v"
proof-
  have "distinct (map fst (right_substs l'' l'))"
    by (simp add: distinct_map_fst_right_substs linear_l') 
  then have *:"\<forall>(x, s)\<in>set (right_substs l'' l'). x = y \<longrightarrow> s = v"
    using assms eq_key_imp_eq_value by fastforce 
  have "set (map fst (right_substs l'' l')) \<subseteq> vars_term l'"
    unfolding right_substs_def using zip_fst by fastforce
  moreover have "vars_term l' \<inter> vars_term v = {}"
  proof-
    from assms have "vars_term v \<subseteq> vars_term l''"
      by (metis fun_poss_imp_poss right_substs_imp_props vars_term_subt_at)
    then show ?thesis 
      using disjoint_vars by blast 
  qed
  ultimately have sub1:"subst_of (right_substs l'' l') y = v"  
    using subst_of_apply[OF assms *] by blast
  {fix x assume "x \<in> vars_term v"
    with assms have "x \<notin> set (map fst (left_substs l'' l'))" 
      using distinct_fst_lsubsts_snd_rsubsts[OF linear_l''] by fastforce 
    then have "subst_of (left_substs l'' l') x = Var x" 
      using not_elem_subst_of by metis
  }
  then show ?thesis 
    unfolding \<tau>_def subst_of_append subst_compose sub1 by (simp add: term_subst_eq)
qed

lemma var_in_l'_in_domain_tau:
  assumes "\<tau> x \<noteq> Var x"
    and "x \<in> vars_term l'"
  shows "\<exists>u. (x, u) \<in> set (right_substs l'' l')"
proof-
  from assms(2) have "x \<notin> vars_term l''"
    by (smt (verit, best) disjoint_iff distinct distinct_append fun_poss_imp_poss poss_map_vars_term q'_poss set_vars_term_list subsetD vars_term_subt_at)
  then have "x \<notin> set (map fst (left_substs l'' l'))"
    by (meson in_mono map_fst_left_substs) 
  then have "(subst_of (left_substs l'' l')) x = Var x"
    by (meson not_elem_subst_of) 
  with assms(1) have "x \<in> set (map fst (right_substs l'' l'))" 
    unfolding \<tau>_def subst_of_append by (metis not_elem_subst_of subst_compose_def subst_monoid_mult.mult.left_neutral) 
  then show ?thesis
    by auto 
qed

lemma var_in_domain_tau:
  assumes "\<tau> x \<noteq> Var x"
    and "i < length (vars_term_list l')" and "vars_term_list l'!i = x"
  shows "(var_poss_list l'!i) \<in> fun_poss l''"
proof-
  from assms obtain u where "(x, u) \<in> set (right_substs l'' l')" 
    using var_in_l'_in_domain_tau by (metis nth_mem set_vars_term_list) 
  then obtain q where q:"q \<in> fun_poss l''" "l'' |_ q = u" "q \<in> poss l'" "l' |_ q = Var x" 
    using right_substs_imp_props by force 
  with linear_l' have "q = (var_poss_list l'!i)"
    by (metis assms(2) assms(3) length_var_poss_list linear_term_unique_vars nth_mem var_poss_imp_poss var_poss_list_sound vars_term_list_var_poss_list) 
  then show ?thesis 
    using q(1) by force 
qed

lemma l_sigma_subst:"l \<cdot> \<sigma> = s|_q"
proof-
  let ?xs="map source (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>)))"
  from source_d2 have "(lhs \<beta>) \<cdot> \<langle>?xs\<rangle>\<^sub>\<beta>  = s|_q" 
    unfolding ll_single_redex_def by (metis (no_types, lifting) p_q_pos(2) replace_at_subt_at source.simps(3) source_to_pterm_ctxt to_pterm_ctxt_at_pos)
  then have "l \<cdot> (mk_subst Var (zip (vars_distinct l) ?xs)) = s|_q"
    by (metis (mono_tags, lifting) length_map length_var_poss_list linear_term_var_vars_term_list mk_subst_rename_x single_\<Delta>2.lin_lhs) 
  with sigma_vars show ?thesis using substitution_subterm_at
    by (smt (verit, best) filter_cong p_q_pos(2) subt_at_append)
qed

lemma l'_sigma_subst:"l' \<cdot> \<sigma> = s|_p"
proof-
  let ?xs="map source (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>)))"
  from source_d1 have "(lhs \<alpha>) \<cdot> \<langle>?xs\<rangle>\<^sub>\<alpha>  = s|_p" 
    unfolding ll_single_redex_def by (metis (no_types, lifting) p_q_pos(1) replace_at_subt_at source.simps(3) source_to_pterm_ctxt to_pterm_ctxt_at_pos) 
  then have "l' \<cdot> (mk_subst Var (zip (vars_distinct l') ?xs)) = s|_p"
    by (metis (mono_tags, lifting) length_map length_var_poss_list linear_term_var_vars_term_list mk_subst_rename_y single_\<Delta>1.lin_lhs)
  with sigma_vars show ?thesis using substitution_subterm_at
    by (smt (verit, best) filter_cong p_q_pos(1) subt_at_append)
qed

lemma l''_sigma_subst:"l'' \<cdot> \<sigma> = s|_p"
proof-
  from q' have "p = q@q'"
    by (metis remove_prefix_Some) 
  then have "s|_p = (s|_q)|_q'" using p_q_pos
    by simp 
  then show ?thesis
    by (metis l_sigma_subst poss_map_vars_term q'_poss fun_poss_imp_poss subt_at_subst) 
qed

lemma mgu:"mgu l'' l' = Some \<tau>"
proof-
  from l''_sigma_subst have un:"unifiers {(l'', l')} \<noteq> {}" 
    unfolding l'_sigma_subst[symmetric] using unifiers_def by fastforce 
  from distinct have "distinct (vars_term_list (l |_ q') @ vars_term_list l')"
    by (metis distinct_vars fun_poss_imp_poss l''_alt q'_poss single_\<Delta>1.lin_lhs single_\<Delta>2.lin_lhs subt_at_linear) 
  then show ?thesis 
    using mgu_distinct_vars_term_list[OF un] distinct unfolding \<tau>_def by simp
qed

lemma ctxt_l_at_q':"ctxt_of_pos_term q' l \<cdot>\<^sub>c \<tau> = ctxt_of_pos_term q' l"
proof-
  {fix x assume x:"x \<in> vars_ctxt (ctxt_of_pos_term q' l)"
    then have "x \<notin> vars_term l''" 
      using linear_term_ctxt by (metis disjoint_iff fun_poss_imp_poss linear_l poss_map_vars_term q'_poss)
    then have l:"x \<notin> set (map fst (left_substs l'' l'))" 
      using map_fst_left_substs by (metis subset_code(1))
    have "x \<notin> vars_term l'"
      using disjoint_iff distinct fun_poss_imp_poss q'_poss vars_ctxt_pos_term x by fastforce
    then have r:"x \<notin> set (map fst (right_substs l'' l'))"
      unfolding right_substs_def using zip_fst by fastforce
    from l r have "\<tau> x = Var x" unfolding \<tau>_def 
      using not_elem_subst_of by (metis Un_iff map_append set_append)  
  }
  then show ?thesis
    by (simp add: ctxt_subst_eq) 
qed

abbreviation x_var :: "'v \<Rightarrow> 'v" where "x_var \<equiv> rename_1 ren" 
abbreviation y_var :: "'v \<Rightarrow> 'v" where "y_var \<equiv> rename_2 ren"

lemma x_diff_y[simp]: "x_var v \<noteq> y_var w" 
  using rename_12[of ren] by blast

abbreviation rename_x where "rename_x \<equiv> map_vars_term (rename_1 ren)"
abbreviation rename_y where "rename_y \<equiv> map_vars_term (rename_2 ren)"

abbreviation "a \<equiv> (to_pterm_ctxt (ctxt_of_pos_term q' l)) \<langle>Prule \<alpha> (map (to_pterm \<circ> \<tau> \<circ> y_var) (var_rule \<alpha>))\<rangle>"
abbreviation "b \<equiv> Prule \<beta> (map (to_pterm \<circ> \<tau> \<circ> x_var) (var_rule \<beta>))"

lemma critical_peak:
  shows "(a, b) \<in> pterm_cpeaks ren R S"
proof-
  from mgu have mgu':"mgu_vd ren (lhs \<beta> |_ q') (lhs \<alpha>) = Some (\<tau> \<circ> x_var, \<tau> \<circ> y_var)" 
    unfolding mgu_vd_def mgu_var_disjoint_generic_def using l''_alt by simp
  have C:"to_pterm_ctxt (ctxt_of_pos_term q' (lhs \<beta> \<cdot> (\<tau> \<circ> x_var))) = to_pterm_ctxt (ctxt_of_pos_term q' l)"
    by (metis apply_subst_map_vars_term ctxt_l_at_q' ctxt_of_pos_term_subst fun_poss_imp_poss poss_map_vars_term q'_poss)
  from pterm_cpeaksI[OF single_\<Delta>1.rule_in_TRS single_\<Delta>2.rule_in_TRS q'_poss mgu'] show ?thesis 
    unfolding C by (simp add: comp_assoc) 
qed

lemma critical_pair: 
  shows "(p=q, replace_at l q' ((rename_y (rhs \<alpha>)) \<cdot> \<tau>), (rename_x (rhs \<beta>)) \<cdot> \<tau>) \<in> critical_pairs ren S R"
proof-
  have "(p=q) = is_Prule a" proof(cases "q'")
    case Nil
    with p show ?thesis by simp
  next
    case (Cons i q'')
    with p have *:"p \<noteq> q"
      by simp 
    from Cons q'_poss obtain f ts where l:"l = Fun f ts"
      by (metis empty_iff fun_poss.simps(1) fun_poss_map_vars_term term_to_term_lab.cases) 
    from * show ?thesis unfolding Cons l by simp 
  qed
  moreover have "target a = replace_at l q' ((rename_y (rhs \<alpha>)) \<cdot> \<tau>)" 
  proof-
    {fix x assume "x \<in> vars_term (rhs \<alpha>)"
      then have "x \<in> vars_term (lhs \<alpha>)"
        using single_\<Delta>1.rule_in_TRS wf_trs_R unfolding wf_trs_def var_rhs_subset_lhs_def by fastforce 
      then obtain i where "i < length (var_rule \<alpha>)" and "x = (var_rule \<alpha>)!i"
        by (metis in_set_idx linear_term_var_vars_term_list set_vars_term_list single_\<Delta>1.lin_lhs) 
      then have "\<langle>map (target \<circ> (to_pterm \<circ> \<tau> \<circ> y_var)) (var_rule \<alpha>)\<rangle>\<^sub>\<alpha> x = (\<tau> \<circ> y_var) x" 
        using lhs_subst_var_i target_to_pterm by (metis (no_types, lifting) comp_apply length_map nth_map) 
      }
      then show ?thesis 
        unfolding target_to_pterm_ctxt by (simp add: apply_subst_map_vars_term term_subst_eq_conv)
    qed
  moreover have "target b = (rename_x (rhs \<beta>)) \<cdot> \<tau>" proof-
    {fix x assume "x \<in> vars_term (rhs \<beta>)"
      then have "x \<in> vars_term (lhs \<beta>)"
        using single_\<Delta>2.rule_in_TRS wf_trs_S unfolding wf_trs_def var_rhs_subset_lhs_def by fastforce 
      then obtain i where "i < length (var_rule \<beta>)" and "x = (var_rule \<beta>)!i"
        by (metis in_set_idx linear_term_var_vars_term_list set_vars_term_list single_\<Delta>2.lin_lhs) 
      then have "\<langle>map (target \<circ> (to_pterm \<circ> \<tau> \<circ> x_var)) (var_rule \<beta>)\<rangle>\<^sub>\<beta> x = (\<tau> \<circ> x_var) x" 
        using lhs_subst_var_i target_to_pterm by (metis (no_types, lifting) comp_apply length_map nth_map) 
    }
    then show ?thesis 
      unfolding target_to_pterm_ctxt by (simp add: apply_subst_map_vars_term term_subst_eq_conv)
  qed
  moreover have "(\<And>l r. (l, r) \<in> R \<union> S \<Longrightarrow> vars_term r \<subseteq> vars_term l)" 
    using wf_trs_R wf_trs_S unfolding wf_trs_def var_rhs_subset_lhs_def by blast 
  ultimately show ?thesis using pterm_cpeak_to_critical_pair critical_peak
    by (smt (verit, best)) 
qed

lemma sigma_tau_vars:
  shows "(\<forall>i < length (vars_term_list l). (\<tau> \<circ>\<^sub>s \<sigma>) ((vars_term_list l)!i) = s|_(q@(var_poss_list l)!i)) \<and>
         (\<forall>i < length (vars_term_list l'). (\<tau> \<circ>\<^sub>s \<sigma>) ((vars_term_list l')!i) = s|_(p@(var_poss_list l')!i)) " (is "?ys \<and> ?xs")
proof
  let ?l_substs="left_substs l'' l'"
  let ?r_substs="right_substs l'' l'"
  have disj:"vars_term l \<inter> vars_term l' = {}" 
    by (simp add: disjoint_iff_not_equal term.set_map(2)) 
  
  {fix j assume j:"j < length (vars_term_list l)"
    let ?y="(vars_term_list l)!j" and ?qj="(var_poss_list l)!j"
    from j have var:"l|_?qj = Var ?y"
      by (metis vars_term_list_var_poss_list) 
    have "set (map fst (?r_substs)) \<subseteq> vars_term l'"
      unfolding right_substs_def using zip_fst by fastforce
    then have right:"?y \<notin> set (map fst (?r_substs))"
      using j disj nth_mem by fastforce
    have "(\<tau> \<circ>\<^sub>s \<sigma>) ?y = s |_ (q @ ?qj)" proof (cases "?y \<in> set (map fst ?l_substs)")
      case True
      then obtain u where u:"(?y, u) \<in> set ?l_substs"
        by fastforce  
      then obtain qj' where qj':"qj' \<in> poss l''" "l'' |_ qj' = Var ?y" "qj' \<in> poss l'" "l' |_ qj' = u" 
        using left_substs_imp_props by metis 
      with u have tau_subst:"\<tau> ?y = l'|_qj'" 
        using apply_tau by blast
      from var qj'(2) have qj:"?qj = q'@qj'" using linear_term_unique_vars[OF linear_l] j qj'(1) q'_poss
        by (metis fun_poss_imp_poss length_var_poss_list nth_mem pos_append_poss poss_map_vars_term subt_at_append var_poss_imp_poss var_poss_list_sound)
      then have "(\<tau> \<circ>\<^sub>s \<sigma>) ?y = (l' \<cdot> \<sigma>)|_qj'" 
        unfolding subst_compose tau_subst using qj'(3) subt_at_subst by metis
      then show ?thesis unfolding l'_sigma_subst qj using q' subt_at_append p_q_pos
        by (metis append.assoc remove_prefix_Some)
    next
      case False
      with right have tau_subst:"\<tau> ?y = Var ?y" 
        unfolding \<tau>_def using not_elem_subst_of by (metis Un_iff map_append set_append)
      from j have sigma_subst:"\<sigma> ?y = s|_(q@?qj)" 
        using sigma_vars by blast 
      then show ?thesis 
        unfolding subst_compose tau_subst eval_term.simps by blast
    qed
  } 
  then show ?ys by simp
  {fix i assume i:"i < length (vars_term_list l')"
    let ?x="(vars_term_list l')!i" and ?pi="(var_poss_list l')!i"
    from i have var:"l'|_?pi = Var ?x"
      by (metis vars_term_list_var_poss_list) 
    have "set (map fst (?l_substs)) \<subseteq> vars_term l''"
      unfolding left_substs_def using zip_fst by fastforce
    then have "set (map fst (?l_substs)) \<subseteq> vars_term l"
      by (smt (verit, best) fun_poss_imp_poss poss_map_vars_term q'_poss subsetD subsetI vars_term_subt_at)
    then have left:"?x \<notin> set (map fst (?l_substs))"
      using i disj nth_mem by fastforce
    have "(\<tau> \<circ>\<^sub>s \<sigma>) ?x = s |_ (p @ ?pi)" proof (cases "?x \<in> set (map fst ?r_substs)")
      case True
      then obtain u where u:"(?x, u) \<in> set ?r_substs"
        by fastforce  
      then obtain pi' where pi':"pi' \<in> poss l'" "l' |_ pi' = Var ?x" "pi' \<in> fun_poss l''" "l'' |_ pi' = u" 
        using right_substs_imp_props by metis 
      with u have tau_subst:"\<tau> ?x = l''|_pi'" 
        using apply_tau2 by blast
      from var pi'(2) have pi:"?pi = pi'" using linear_term_unique_vars[OF linear_l'] i pi'(1)
        by (metis length_var_poss_list nth_mem var_poss_imp_poss var_poss_list_sound) 
      then have "(\<tau> \<circ>\<^sub>s \<sigma>) ?x = (l'' \<cdot> \<sigma>)|_pi'" 
        unfolding subst_compose tau_subst using pi'(3) by (simp add: fun_poss_imp_poss)
      then show ?thesis unfolding l''_sigma_subst pi 
        using subt_at_append p_q_pos by simp
    next
      case False
      with left have tau_subst:"\<tau> ?x = Var ?x" 
        unfolding \<tau>_def using not_elem_subst_of by (metis Un_iff map_append set_append)
      from i have sigma_subst:"\<sigma> ?x = s|_(p@?pi)" 
        using sigma_vars by blast
      then show ?thesis 
        unfolding subst_compose tau_subst eval_term.simps by blast
    qed
  } then show ?xs by simp
qed

lemma l_tau_sigma:
  shows "l \<cdot> \<tau> \<cdot> \<sigma> = s|_q"
proof-
  {fix x assume "x \<in> vars_term l"
    then obtain i where "i < length (vars_term_list l)" "x = (vars_term_list l ! i)"
      by (metis in_set_idx set_vars_term_list)
    with sigma_tau_vars sigma_vars have "(\<tau> \<circ>\<^sub>s \<sigma>) x = \<sigma> x"
      by simp
  }
  then show ?thesis using l_sigma_subst
    by (metis (no_types, lifting) subst_subst term_subst_eq) 
qed

lemma l'_tau_sigma:
  shows "l' \<cdot> \<tau> \<cdot> \<sigma> = s|_p"
proof-
  {fix x assume "x \<in> vars_term l'"
    then obtain i where "i < length (vars_term_list l')" "x = (vars_term_list l' ! i)"
      by (metis in_set_idx set_vars_term_list)
    with sigma_tau_vars sigma_vars have "(\<tau> \<circ>\<^sub>s \<sigma>) x = \<sigma> x"
      by simp
  }
  then show ?thesis using l'_sigma_subst
    by (metis (no_types, lifting) subst_subst term_subst_eq) 
qed

text\<open>Preparation for Lemma 4.1 of 'Commutation via Relative Termination'\<close>
lemma \<Delta>1_is_rstep:
  assumes "(source a, target a) \<in> X"
  shows "(source \<Delta>1, target \<Delta>1) \<in> rstep X"
proof-
  have *:"vars_term (rhs \<alpha>) \<subseteq> vars_term (lhs \<alpha>)" 
     using wf_trs_R single_\<Delta>1.rule_in_TRS unfolding wf_trs_def var_rhs_subset_lhs_def by blast  
  from q'_poss have q':"q' \<in> poss l"
     by (simp add: fun_poss_imp_poss) 
  have src:"source a = (ctxt_of_pos_term q' l) \<langle>rename_y (lhs \<alpha>) \<cdot> \<tau>\<rangle>"
    unfolding source_to_pterm_ctxt source.simps map_map lhs_subst_var_rule[OF subset_refl[of "vars_term (lhs \<alpha>)"]] 
    by (simp add: apply_subst_map_vars_term term_subst_eq_conv) 
  have tgt:"target a = (ctxt_of_pos_term q' l) \<langle>rename_y (rhs \<alpha>) \<cdot> \<tau>\<rangle>"
    unfolding target_to_pterm_ctxt target.simps map_map lhs_subst_var_rule[OF *] 
    by (simp add: apply_subst_map_vars_term term_subst_eq_conv)
  have "source \<Delta>1 = (ctxt_of_pos_term q s) \<langle>(source a) \<cdot> \<sigma>\<rangle>"
    unfolding src by (metis ctxt_supt_id l''_sigma_subst l'_tau_sigma l_sigma_subst p_q_pos(2) q' s_def single_\<Delta>1.source_delta subst_apply_term_ctxt_apply_distrib)
  moreover have "target \<Delta>1 = (ctxt_of_pos_term q s) \<langle>(target a) \<cdot> \<sigma>\<rangle>"
    unfolding tgt using *
    by (smt (z3) apply_subst_map_vars_term calculation ctxt_apply_ctxt_apply ctxt_of_pos_term_subst l'_tau_sigma l_sigma_subst p p_q_pos(1) p_q_pos(2) q' replace_at_subt_at s_def single_\<Delta>1.source_delta source_single_redex subst_apply_term_ctxt_apply_distrib subst_subst_compose target_single_redex vars_term_subset_subst_eq)
  ultimately show ?thesis using assms by blast
qed

lemma \<Delta>2_is_rstep: 
   assumes "(source b, target b) \<in> X"
   shows "(source \<Delta>2, target \<Delta>2) \<in> rstep X" 
proof-
  have *:"vars_term (rhs \<beta>) \<subseteq> vars_term (lhs \<beta>)" 
    using single_\<Delta>2.rule_in_TRS wf_trs_S unfolding wf_trs_def var_rhs_subset_lhs_def by blast 
  have src:"source b = rename_x (lhs \<beta>) \<cdot> \<tau>"
    unfolding source.simps map_map lhs_subst_var_rule[OF subset_refl[of "vars_term (lhs \<beta>)"]]
    by (simp add: apply_subst_map_vars_term term_subst_eq_conv) 
  have tgt:"target b = rename_x (rhs \<beta>) \<cdot> \<tau>"
    unfolding target.simps map_map lhs_subst_var_rule[OF *] by (simp add: apply_subst_map_vars_term term_subst_eq_conv)
  have "source \<Delta>2 = (ctxt_of_pos_term q s) \<langle>(source b) \<cdot> \<sigma>\<rangle>"
    unfolding src by (simp add: l_tau_sigma p_q_pos(2) replace_at_ident source_d2) 
  moreover have "target \<Delta>2 = (ctxt_of_pos_term q s) \<langle>(target b) \<cdot> \<sigma>\<rangle>"
    unfolding tgt target_single_redex[OF p_q_pos(2)]
    by (smt (verit) "*" filter_cong l_tau_sigma map_eq_conv map_vars_term_eq p_q_pos(2) replace_at_subt_at source_d2 source_single_redex subst_subst_compose vars_term_subset_subst_eq)
  ultimately show ?thesis using assms by blast
qed
 
context 
  fixes D'
  assumes d'_well:"D' \<in> wf_pterm S" 
    and src_d':"source D' = replace_at l q' (rename_y (rhs \<alpha>) \<cdot> \<tau>)" 
begin

definition "D = replace_at (to_pterm s) q (D' \<cdot> (to_pterm \<circ> \<sigma>))"

lemma d_well:"D \<in> wf_pterm S"
proof-
  have "(D' \<cdot> (to_pterm \<circ> \<sigma>)) \<in> wf_pterm S" 
    using apply_subst_wf_pterm using d'_well by force 
   then show ?thesis 
     by (simp add: ctxt_wf_pterm D_def p_in_poss_to_pterm p_q_pos(2))
qed

lemma source_D:  
  "source D = target \<Delta>1" 
proof-
  have \<alpha>:"to_rule \<alpha> \<in> R"
    using single_\<Delta>1.rule_in_TRS by blast 
  {fix x assume "x \<in> vars_term (rhs \<alpha>)"
    with \<alpha> have x:"x \<in> vars_term (lhs \<alpha>)" using wf_trs_R unfolding wf_trs_def var_rhs_subset_lhs_def by blast
    then have "(\<langle>map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>) x = ((Var \<circ> y_var) x) \<cdot> \<tau> \<cdot> \<sigma>"
    proof-
      from x obtain i where i:"x = var_rule \<alpha>!i" and len:"i < length (var_rule \<alpha>)"
        by (metis in_set_conv_nth linear_term_var_vars_term_list single_\<Delta>1.lin_lhs set_vars_term_list)
      then have len2:"i < length (var_poss_list (lhs \<alpha>))"
        by (metis length_var_poss_list linear_term_var_vars_term_list single_\<Delta>1.lin_lhs)  
      then have left:"(\<langle>map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>) x = s |_ (p @ (var_poss_list (lhs \<alpha>)!i))" 
        using lhs_subst_var_i[OF i len] by (smt (z3) length_map nth_map) 
      from i have "x = vars_term_list (lhs \<alpha>) ! i"
        by (metis linear_term_var_vars_term_list single_\<Delta>1.lin_lhs) 
      with len2 have "((y_var) x) = vars_term_list (rename_y (lhs \<alpha>))!i" 
        using vars_map_vars_term by (metis length_var_poss_list nth_map)
      with len2 have right:"((Var \<circ> y_var) x) \<cdot> \<tau> \<cdot> \<sigma> = s |_ (p @ (var_poss_list (lhs \<alpha>)!i))" 
        using sigma_tau_vars var_poss_list_map_vars_term
        by (smt (verit, best) comp_apply filter_cong length_var_poss_list eval_term.simps(1) subst_subst_compose) 
      show ?thesis unfolding left right by simp
    qed
  }
  then have "rhs \<alpha> \<cdot> \<langle>map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha> = (rename_y (rhs \<alpha>)) \<cdot> \<tau> \<cdot> \<sigma>"
    using term_subst_eq_conv[where \<tau>="(Var \<circ> y_var) \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<sigma>"] 
    unfolding map_vars_term_eq by (simp add: subst_compose)
  then have target:"target (ll_single_redex s p \<alpha>) = replace_at s p ((rename_y (rhs \<alpha>)) \<cdot> \<tau> \<cdot> \<sigma>)"
    using p_q_pos target_single_redex by fastforce
  have "source D = (ctxt_of_pos_term q s)\<langle>source (D' \<cdot> (to_pterm \<circ> \<sigma>))\<rangle>" 
    unfolding D_def using p_q_pos source_to_pterm_ctxt to_pterm_ctxt_at_pos by metis
  also have "... = (ctxt_of_pos_term q s)\<langle>(replace_at l q' ((rename_y (rhs \<alpha>)) \<cdot> \<tau>)) \<cdot> \<sigma>\<rangle>" 
    using d'_well source_apply_subst src_d' by (metis source_to_pterm to_pterm_subst to_pterm_wf_pterm)
  also have "... = (ctxt_of_pos_term q s)\<langle>replace_at (l\<cdot>\<sigma>) q' ((rename_y (rhs \<alpha>)) \<cdot> \<tau> \<cdot> \<sigma>)\<rangle>" 
    using q'_poss by (simp add: ctxt_of_pos_term_subst fun_poss_imp_poss) 
  also have "... = (ctxt_of_pos_term p s)\<langle>(rename_y (rhs \<alpha>)) \<cdot> \<tau> \<cdot> \<sigma>\<rangle>" 
    unfolding l_sigma_subst ctxt_ctxt using p_q_pos q' ctxt_of_pos_term_append by (metis (no_types, lifting) remove_prefix_Some) 
  finally show ?thesis using target by auto 
qed

section\<open>Introducing \<rho>\<close>

abbreviation "lhs\<^sub>\<beta>' \<equiv> (lhs \<beta>)|_q'"
definition "rho_substs = match_substs (to_pterm l') ((to_pterm lhs\<^sub>\<beta>') \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)"
abbreviation "\<rho> \<equiv> mk_subst Var ((zip (vars_distinct l) Bs)@rho_substs)"

lemma innermost_ov_contr:
  assumes "r \<in> fun_poss l'"
  shows "r \<notin> possL (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)"
proof
  assume r:"r \<in> possL (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)"
  {fix x assume "x \<in> vars_term lhs\<^sub>\<beta>'"
    then have "(\<langle>Bs\<rangle>\<^sub>\<beta>) x \<in> wf_pterm S"
      by (metis lhs_subst_var_well_def single_\<Delta>2.as_well) 
  }
  then obtain p1 p2 x \<gamma> where p1:"p1 \<in> poss lhs\<^sub>\<beta>'" and x:"lhs\<^sub>\<beta>' |_ p1 = Var x" and p1p2:"p1 @ p2 \<le>\<^sub>p r" and
    p2:"p2 \<in> possL ((\<langle>Bs\<rangle>\<^sub>\<beta>) x)" and lab0:"get_label (labeled_source ((\<langle>Bs\<rangle>\<^sub>\<beta>) x) |_ p2) = Some (\<gamma>, 0)"
    using labeled_source_to_pterm_subst[OF r] by blast 
  from p1 x have x_beta:"x \<in> set (var_rule \<beta>)"
    by (metis fun_poss_imp_poss in_mono linear_term_var_vars_term_list q'_poss set_vars_term_list single_\<Delta>2.lin_lhs term.set_intros(3) vars_term_subt_at)
  from p2 obtain f' ts where fun_f':"(labeled_source ((\<langle>Bs\<rangle>\<^sub>\<beta>) x))|_p2 = Fun f' ts"
    using labelposs_subs_fun_poss fun_poss_fun_conv by blast
  with lab0 have f':"snd f' = Some (\<gamma>, 0)"
    by simp 
  have q'p1_pos:"(q' @ p1) \<in> poss (labeled_lhs \<beta>)" 
    using q'_poss p1 by (simp add: fun_poss_imp_poss) 
  then have "labeled_lhs \<beta> |_ (q'@p1) = Var x" using x
    by (smt (verit) DiffE fun_poss_label_term is_VarE label_term_to_term labeled_source_pos poss_is_Fun_fun_poss poss_simps(3) poss_term_lab_to_term q'_poss subt_at_append term.inject(1) term_lab_to_term.simps(1) var_poss_iff)
  then have "(labeled_source (Prule \<beta> Bs))|_(q'@p1@p2) = ((\<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>) x) |_ p2" 
    unfolding labeled_source.simps using q'p1_pos subt_at_append[of "q'@p1"]
    by (smt (verit, best) poss_append_poss poss_imp_subst_poss eval_term.simps(1) subt_at_append subt_at_subst)
  with fun_f' have lab:"(labeled_source (Prule \<beta> Bs))|_(q'@p1@p2) = Fun f' ts" 
    using x_beta single_\<Delta>2.length_as by (smt (verit) in_set_idx length_map lhs_subst_var_i nth_map) 
  moreover from p1 x p1p2 have q'p1p2:"q' @ p1 @ p2 \<in> poss (source (Prule \<beta> Bs))" 
    unfolding source.simps using q'_poss labelposs_subs_fun_poss_source[OF p2]
    by (smt (verit, best) fun_mk_subst fun_poss_imp_poss o_apply poss_append_poss poss_imp_subst_poss source_to_pterm eval_term.simps(1) subt_at_subst to_pterm.simps(1))
  then have overlap:"(p, p@p1@p2) \<in> overlaps_pos (labeled_source A) (labeled_source B)" proof-
    have "p @ p1 @ p2 \<in> fun_poss (labeled_source B)"
      using single_\<Delta>2.labeled_source_at_pq lab q'p1p2 unfolding single_\<Delta>2.aq p
      by (metis (no_types, lifting) append_assoc is_FunI labeled_source_to_term pos_append_poss poss_is_Fun_fun_poss poss_term_lab_to_term single_\<Delta>2.p subt_at_append) 
    moreover have p_pos:"p \<in> fun_poss (labeled_source A)"
      using pq by force 
    moreover have "get_label ((labeled_source B) |_ (p @ p1 @ p2)) = Some (\<gamma>, 0)" 
      using single_\<Delta>2.labeled_source_at_pq lab q'p1p2 f' unfolding single_\<Delta>2.aq p by (simp add: single_\<Delta>2.p) 
    moreover have "get_label ((labeled_source A) |_ p) = Some (\<alpha>, 0)"
      by (simp add: alpha)
    moreover have "get_label ((labeled_source A) |_ (p @ p1 @ p2)) = Some (\<alpha>, length (p1@p2))" proof-
      from assms have "r \<in> fun_poss (lhs \<alpha>)"
        by (simp add: fun_poss_map_vars_term)
      then have "p1@p2 \<in> fun_poss (lhs \<alpha>)" using p1p2
        by (metis fun_poss_append_poss fun_poss_imp_poss prefix_pos_diff self_append_conv)  
      moreover have "labeled_source A|_p = labeled_lhs \<alpha> \<cdot> \<langle>map labeled_source As\<rangle>\<^sub>\<alpha>"
        using single_\<Delta>1.labeled_source_at_pq single_\<Delta>1.aq by simp 
      ultimately show ?thesis 
        using label_term_increase p_pos by (metis (no_types, lifting) add_0 fun_poss_imp_poss subt_at_append)
    qed
    ultimately show ?thesis 
      using overlaps_pos_intro overlaps_pos_symmetric by blast
  qed
  have "p1 \<noteq> []" 
    using x q'_poss fun_poss_fun_conv by fastforce 
  moreover have "(p, q) \<le>\<^sub>o (p, p@p1@p2)"
    unfolding less_eq_overlap_def by (metis fstI le less_eq_pos_simps(1) order_pos.eq_refl order_pos.order.trans sndI)
  ultimately show False  
    using maximal using le overlap by fastforce 
qed

lemma apply_tau_rho:
  assumes j:"j < length (vars_term_list l)" and y:"y = vars_term_list l!j"
  shows "(to_pterm (\<tau> y)) \<cdot> \<rho> = Bs!j"
proof-
  let ?qj="var_poss_list l!j" 
  have qj:"l|_?qj = Var y"
    by (simp add: j vars_term_list_var_poss_list y) 
  have y':"y = vars_distinct l ! j" 
    using linear_l linear_term_var_vars_term_list y by force 
  have l'_rho:"to_pterm l' \<cdot> \<rho> = ((to_pterm (lhs \<beta>)|_q') \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)" proof-
    {fix x assume x:"x \<in> vars_term l'"
      then have "x \<notin> set (vars_distinct l)" 
        using distinct by auto 
      then have "x \<notin> set (map fst (zip (vars_distinct l) Bs))"
        by (smt (verit, best) length_map linear_l linear_term_var_vars_term_list map_fst_zip single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term) 
      then have "\<rho> x = (mk_subst Var rho_substs) x" 
        using mk_subst_concat by fastforce
    }
    moreover have "to_pterm l' \<cdot> (mk_subst Var rho_substs) = (to_pterm (lhs \<beta>)|_q') \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>" proof-
      have well:"to_pterm (lhs \<beta>) |_ q' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta> \<in> wf_pterm S" 
        using lhs_subst_var_well_def[OF single_\<Delta>2.as_well] p_in_poss_to_pterm q'_poss subt_at_is_wf_pterm
        by (smt (verit, ccfv_SIG) fun_poss_imp_poss lhs_subst_well_def single_\<Delta>2.as_well to_pterm_wf_pterm)
      have src:"source (to_pterm (lhs \<beta>) |_ q' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) = l' \<cdot> \<sigma>" proof-
        have "source (to_pterm (lhs \<beta>) |_ q' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) = (source (Prule \<beta> Bs)) |_q'"
          unfolding source.simps using subt_at_subst source_apply_subst q'_poss
          using ctxt_supt_id fun_mk_subst fun_poss_imp_poss p_in_poss_to_pterm replace_at_subt_at source.simps(1) source_to_pterm to_pterm_ctxt_apply_term to_pterm_ctxt_at_pos to_pterm_wf_pterm
          by (metis (no_types, lifting))
        then show ?thesis unfolding l'_sigma_subst
          by (metis co_init innermost_overlap.p_q_pos(2) innermost_overlap_axioms p s_def single_\<Delta>2.aq single_\<Delta>2.source_at_pq subt_at_append)
      qed
      have "to_pterm (lhs \<beta>) |_ q' = to_pterm lhs\<^sub>\<beta>'"
        by (metis fun_poss_imp_poss p_in_poss_to_pterm q'_poss replace_at_ident replace_at_subt_at to_pterm_ctxt_of_pos_apply_term)
      moreover then have "\<forall>p\<in>fun_poss l'. p \<notin> possL (to_pterm (lhs \<beta>) |_ q' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)"
        using innermost_ov_contr by simp
      ultimately show ?thesis
        using linear_l' rho_substs_def single_\<Delta>2.pterm_source_substitution src well by force
    qed
    ultimately show ?thesis
      by (smt (verit, ccfv_SIG) set_vars_term_list term_subst_eq_conv vars_to_pterm)
  qed
  have y_Bsj:"\<rho> y = Bs!j" proof-
    have "j < length (vars_distinct l)" 
      using j linear_l by (metis linear_term_var_vars_term_list) 
    moreover have "length (vars_distinct l) = length Bs"
      by (smt (verit, best) length_map linear_l linear_term_var_vars_term_list single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term) 
    ultimately have *:"map_of (zip (vars_distinct l) Bs) y = Some (Bs!j)" 
      using map_of_zip_nth distinct y' by force 
    then show ?thesis unfolding mk_subst_def map_of_append map_add_def * by fastforce
  qed
  show ?thesis proof (cases "y \<in> set (map fst (left_substs l'' l'))")
    case True
    then obtain u where u:"(y, u) \<in> set (left_substs l'' l')"
      by fastforce  
    then obtain qj' where qj':"qj' \<in> poss l''" "l'' |_ qj' = Var y" "qj' \<in> poss l'" "l' |_ qj' = u" 
      using left_substs_imp_props by metis
    with u have "\<tau> y = l'|_qj'" 
      using apply_tau by blast
    then have "(to_pterm (\<tau> y)) \<cdot> \<rho> = ((to_pterm (lhs \<beta>)|_q') \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) |_qj'" 
      using l'_rho by (smt (verit, best) p_in_poss_to_pterm qj'(3) replace_at_ident replace_at_subt_at subt_at_subst to_pterm_ctxt_of_pos_apply_term)
    moreover have "((to_pterm (lhs \<beta>)|_q') \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) |_qj' = Bs!j" proof-
      from qj'(1) have qj'_pos:"qj' \<in> poss ((lhs \<beta>)|_q')"
        by (simp add: l''_alt)  
      with qj'(2) have "(to_pterm (lhs \<beta>)|_q')|_qj' = Var ((vars_term_list (lhs \<beta>))!j)"  
        unfolding y
        by (smt (verit) fun_poss_imp_poss j length_var_poss_list linear_l linear_term_unique_vars nth_mem p_in_poss_to_pterm pos_append_poss poss_map_vars_term q'_poss subt_at_append var_poss_imp_poss var_poss_list_map_vars_term var_poss_list_sound var_poss_list_to_pterm vars_term_list_var_poss_list vars_to_pterm)  
      with qj'_pos show ?thesis
        by (smt (verit, ccfv_threshold) apply_lhs_subst_var_rule fun_poss_imp_poss j length_map linear_term_var_vars_term_list nth_map p_in_poss_to_pterm poss_append_poss q'_poss single_\<Delta>2.length_as single_\<Delta>2.lin_lhs eval_term.simps(1) subt_at_subst vars_map_vars_term) 
    qed
    ultimately show ?thesis by presburger 
  next
    case False
    have "set (map fst (right_substs l'' l')) \<subseteq> vars_term l'"
      unfolding right_substs_def using zip_fst by fastforce
    moreover have "vars_term l \<inter> vars_term l' = {}" 
      by (simp add: disjoint_iff_not_equal term.set_map(2)) 
    ultimately have right:"y \<notin> set (map fst (right_substs l'' l'))"
      using j nth_mem y by fastforce
    with False have "\<tau> y = Var y" 
      unfolding \<tau>_def using not_elem_subst_of by (metis Un_iff map_append set_append)
    then show ?thesis using y_Bsj by simp
  qed 
qed

lemma var_l_rho:
  assumes j:"j < length (vars_distinct l)"
  shows "\<rho> (vars_distinct l ! j) = Bs!j"
proof-
  have "length Bs = length (vars_distinct l)"
    by (smt (verit, ccfv_threshold) length_map linear_l linear_term_var_vars_term_list single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term) 
  then have "map_of (zip (vars_distinct l) Bs) (vars_distinct l !j) = Some (Bs ! j)"
    by (metis (no_types, lifting) distinct distinct_append j(1) linear_l linear_term_var_vars_term_list map_of_zip_nth single_\<Delta>2.length_as) 
  then show ?thesis 
    unfolding mk_subst_def map_of_append by simp
qed

lemma var_l'_rho:
  assumes i:"i < length (vars_term_list l')"
  shows "\<rho> (vars_term_list l' ! i) = (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>single_\<Delta>2.As\<rangle>\<^sub>\<beta>)|_(var_poss_list l' !i)"
proof-
  let ?xi="vars_term_list l' !i"
  let ?pi="var_poss_list l' !i"
  from i have i':"i < length (vars_term_list (to_pterm l'))"
    by (metis vars_to_pterm)
  moreover then have "i < length (var_poss_list (to_pterm l'))"
    by (simp add: length_var_poss_list) 
  ultimately have match_subst:"(?xi, (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)|_?pi) = (match_substs (to_pterm l') (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>))!i" 
    unfolding match_substs_def var_poss_list_to_pterm vars_to_pterm by simp 
  have "?xi \<notin> vars_term l"
    by (metis (no_types, lifting) i' disjoint_iff distinct distinct_append nth_mem set_vars_term_list vars_to_pterm) 
  then have "\<rho> ?xi = (mk_subst Var (match_substs (to_pterm l') (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>single_\<Delta>2.As\<rangle>\<^sub>\<beta>))) ?xi" 
    unfolding rho_substs_def using mk_subst_concat
    by (smt (verit) length_map linear_l linear_term_var_vars_term_list map_fst_zip set_vars_term_list single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term)
  moreover have "distinct (map fst (match_substs (to_pterm l') (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>single_\<Delta>2.As\<rangle>\<^sub>\<beta>)))"
    by (smt (verit, best) distinct_rev length_map length_var_poss_list linear_l' linear_term_var_vars_term_list map_fst_zip match_substs_def o_apply remdups_id_iff_distinct rev_swap vars_to_pterm) 
  ultimately show ?thesis 
    using i' mk_subst_distinct by (smt (z3) length_map length_var_poss_list map_fst_zip match_subst match_substs_def nth_zip prod.simps(1)) 
qed

lemma source_rho: "l \<cdot> (source \<circ> \<rho>) = s|_q" 
proof-
  {fix y assume "y \<in> vars_term (lhs \<beta>)"
    then obtain j where j:"j < length (var_rule \<beta>)" "var_rule \<beta> !j = y"
      by (metis in_set_conv_nth single_\<Delta>2.lin_lhs linear_term_var_vars_term_list set_vars_term_list) 
    then have "vars_distinct l ! j = x_var y"
      by (metis linear_l linear_term_var_vars_term_list nth_map single_\<Delta>2.lin_lhs vars_map_vars_term) 
    then have "\<rho> (x_var y) = Bs!j" 
      using var_l_rho j by (smt (verit, best) length_map linear_l linear_term_var_vars_term_list single_\<Delta>2.lin_lhs vars_map_vars_term) 
    then have "(\<rho> \<circ> x_var) y = (\<langle>Bs\<rangle>\<^sub>\<beta>) y"
      using j by (smt (verit, ccfv_SIG) length_map lhs_subst_var_i map_map nth_map single_\<Delta>2.length_as) 
    then have "(source \<circ> \<rho> \<circ> x_var) y = (\<langle>map source Bs\<rangle>\<^sub>\<beta>) y"
      using j by (metis (no_types, lifting) length_map lhs_subst_var_i nth_map o_apply single_\<Delta>2.length_as) 
  }
  then have "l \<cdot> (source \<circ> \<rho>) = source (Prule \<beta> Bs)" 
    unfolding apply_subst_map_vars_term source.simps using term_subst_eq_conv by blast 
  then show ?thesis
    using co_init s_def single_\<Delta>2.aq single_\<Delta>2.source_at_pq by presburger
qed

lemma source_rho_sigma:"source \<circ> \<rho> = \<sigma>" 
proof
  fix x
  show "(source \<circ> \<rho>) x = \<sigma> x" proof(cases "x \<in> vars_term l")
    case True
    then show ?thesis using source_rho
      by (smt (verit, best) l_sigma_subst term_subst_eq_conv) 
  next
    case False
    note false'=this
    then have rho:"\<rho> x = (mk_subst Var rho_substs) x"
      by (smt (verit) length_map linear_l linear_term_var_vars_term_list map_fst_zip mk_subst_concat set_vars_term_list single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term) 
    then show ?thesis proof(cases "x \<in> vars_term l'")
      case True
      have well:"to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta> \<in> wf_pterm S" 
        using single_\<Delta>2.as_well lhs_subst_well_def to_pterm_wf_pterm by blast
      from True obtain i where i:"i < length (vars_term_list l')" "(vars_term_list l')!i = x"
        by (metis in_set_conv_nth set_vars_term_list) 
      let ?q="var_poss_list l' ! i"
      let ?u="(to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)|_?q"
      from i have rho:"\<rho> x = ?u"
        using var_l'_rho by blast 
      have q_facts:"?q \<in> poss (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) \<and> labeled_source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) |_ ?q = labeled_source ((to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) |_ ?q)" proof-
          have "?q \<in> poss (source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>))" proof-
          have "source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) = s|_p"
            unfolding p by (metis (no_types, lifting) co_init fun_mk_subst fun_poss_imp_poss p_q_pos(2) q'_poss s_def single_\<Delta>2.aq single_\<Delta>2.source_at_pq source.simps(1) source.simps(3) source_apply_subst source_to_pterm subt_at_append subt_at_subst to_pterm_wf_pterm) 
          moreover have "?q \<in> poss (s|_p)" 
            using l'_sigma_subst by (metis i(1) length_var_poss_list nth_mem poss_imp_subst_poss var_poss_imp_poss var_poss_list_sound)
          ultimately show ?thesis by presburger 
        qed
        moreover 
        {fix r assume le:"r <\<^sub>p ?q"
          have "?q \<in> poss l'"
            by (metis i(1) length_var_poss_list nth_mem var_poss_imp_poss var_poss_list_sound) 
          with le have "r \<in> fun_poss l'"  
            using fun_poss_append_poss by (metis less_pos_def') 
          then have "r \<notin> possL (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)" 
            using innermost_ov_contr by blast 
        }
        ultimately show ?thesis
          using single_\<Delta>2.unlabeled_above_p well by blast 
      qed
      have "source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) = s|_p"
        by (metis (no_types, lifting) co_init fun_mk_subst fun_poss_imp_poss p p_q_pos(2) q'_poss s_def single_\<Delta>2.aq single_\<Delta>2.source_at_pq source.simps(1) source.simps(3) source_apply_subst source_to_pterm subt_at_append subt_at_subst to_pterm_wf_pterm) 
      moreover have "\<sigma> x = s|_(p@?q)"
        using i sigma_vars by blast
      moreover from q_facts have "source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) |_ ?q = source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta> |_ ?q)"
        unfolding labeled_source_to_term var_poss_list_map_vars_term
        by (smt (verit, del_insts) calculation(1) i(1) l'_sigma_subst labeled_source_to_term length_var_poss_list nth_mem poss_imp_subst_poss poss_term_lab_to_term term_lab_to_term_subt_at var_poss_imp_poss var_poss_list_map_vars_term var_poss_list_sound)  
      ultimately have "source ?u = \<sigma> x"
        using labeled_source_to_term term_lab_to_term_subt_at  by (simp add: p_q_pos(1) term_lab_to_term_subt_at) 
      with rho show ?thesis
        by simp 
    next
      case False
      with false' have "x \<notin> set (vars_term_list l @ vars_term_list l')" 
        unfolding set_append by simp
      then have "\<sigma> x = Var x"
        unfolding \<sigma>_simp using mk_subst_not_mem by (metis (no_types, lifting)) 
      moreover have "\<rho> x = Var x"
        unfolding rho rho_substs_def match_substs_def using false' False
        by (smt (verit, del_insts) length_map linear_l linear_term_var_vars_term_list map_fst_zip mk_subst_concat mk_subst_not_mem set_vars_term_list single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term vars_to_pterm) 
      ultimately show ?thesis by simp
    qed
  qed
qed

abbreviation "A' \<equiv> the (A re \<Delta>1)"
abbreviation "B' \<equiv> (ctxt_of_pos_term q\<^sub>\<beta> B) \<langle>D'\<cdot>\<rho>\<rangle>"

lemma source_B': "source B' = source A'"
proof-
  have "source B' = replace_at s p ((rename_y (rhs \<alpha>)) \<cdot> \<tau> \<cdot> \<sigma>)" 
  proof- 
    have well_ctxt:"ctxt_of_pos_term q\<^sub>\<beta> B \<in> wf_pterm_ctxt S"
      using B ctxt_of_pos_term_well single_\<Delta>2.q by auto 
    have src_d'_rho:"source (D' \<cdot> \<rho>) = (ctxt_of_pos_term q' (l \<cdot> (source \<circ> \<rho>)))\<langle>rename_y (rhs \<alpha>) \<cdot> \<tau> \<cdot> \<sigma>\<rangle>"
      unfolding source_apply_subst[OF d'_well] src_d' subst_apply_term_ctxt_apply_distrib 
      using ctxt_of_pos_term_subst source_rho_sigma 
      by (metis fun_poss_imp_poss poss_map_vars_term q'_poss)
    show ?thesis
      using single_\<Delta>2.source_ctxt_apply_term[OF well_ctxt] single_\<Delta>2.pq[symmetric] src_d'_rho source_rho co_init s_def
      by (metis ctxt_apply_ctxt_apply ctxt_supt_id p p_q_pos(2)) 
  qed
  moreover have "source A' = replace_at s p ((rename_y (rhs \<alpha>)) \<cdot> \<tau> \<cdot> \<sigma>)"
  proof-
    {fix x assume "x \<in> vars_term (rhs \<alpha>)"
      with single_\<Delta>1.rule_in_TRS have x:"x \<in> vars_term (lhs \<alpha>)" 
        using wf_trs_R unfolding wf_trs_def var_rhs_subset_lhs_def by blast
      then have "(\<langle>map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>) x = ((Var \<circ> y_var) x) \<cdot> \<tau> \<cdot> \<sigma>"
      proof-
        from x obtain i where i:"x = var_rule \<alpha>!i" and len:"i < length (var_rule \<alpha>)"
          by (metis in_set_conv_nth linear_term_var_vars_term_list single_\<Delta>1.lin_lhs set_vars_term_list)
        then have len2:"i < length (var_poss_list (lhs \<alpha>))"
          by (metis length_var_poss_list linear_term_var_vars_term_list single_\<Delta>1.lin_lhs)  
        then have left:"(\<langle>map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha>) x = s |_ (p @ (var_poss_list (lhs \<alpha>)!i))" 
          using lhs_subst_var_i[OF i len] by (smt (z3) length_map nth_map) 
        from i have "x = vars_term_list (lhs \<alpha>) ! i"
          by (metis linear_term_var_vars_term_list single_\<Delta>1.lin_lhs) 
        with len2 have "((y_var) x) = vars_term_list (rename_y (lhs \<alpha>))!i" 
          using vars_map_vars_term by (metis length_var_poss_list nth_map)
        with len2 have right:"((Var \<circ> y_var) x) \<cdot> \<tau> \<cdot> \<sigma> = s |_ (p @ (var_poss_list (lhs \<alpha>)!i))" 
          using sigma_tau_vars var_poss_list_map_vars_term
          by (smt (verit, best) comp_apply filter_cong length_var_poss_list eval_term.simps(1) subst_subst_compose) 
        show ?thesis unfolding left right by simp
      qed
    }
    then have "rhs \<alpha> \<cdot> \<langle>map (\<lambda>pi. s |_ (p @ pi)) (var_poss_list (lhs \<alpha>))\<rangle>\<^sub>\<alpha> = (rename_y (rhs \<alpha>)) \<cdot> \<tau> \<cdot> \<sigma>"
      using term_subst_eq_conv[where \<tau>="(Var \<circ> y_var) \<circ>\<^sub>s \<tau> \<circ>\<^sub>s \<sigma>"] 
      unfolding map_vars_term_eq by (simp add: subst_compose)
    then have "target \<Delta>1 = replace_at s p ((rename_y (rhs \<alpha>)) \<cdot> \<tau> \<cdot> \<sigma>)"
      using p_q_pos target_single_redex by fastforce
    then show ?thesis
      using A residual_src_tgt single_\<Delta>1.delta_trs_wf_pterm single_\<Delta>1.residual by fastforce
  qed
  ultimately show ?thesis by simp
qed

lemma B'_well: "B' \<in> wf_pterm S" 
proof-
  have vars_d':"vars_term D' = vars_term (ctxt_of_pos_term q' l)\<langle>(rename_y (rhs \<alpha>) \<cdot> \<tau>)\<rangle>" 
    using src_d' vars_term_source by (metis d'_well)
  have vars_d:"vars_term D' \<subseteq> (vars_term l) \<union> (vars_term l')" proof-
    have "vars_term (rhs \<alpha>) \<subseteq> vars_term (lhs \<alpha>)" 
      using single_\<Delta>1.rule_in_TRS wf_trs_R unfolding wf_trs_def var_rhs_subset_lhs_def by blast
    then have "vars_term (rename_y (rhs \<alpha>)) \<subseteq> vars_term l'"
       by (simp add: image_mono term.set_map(2)) 
    moreover 
    {fix x assume x:"x \<in> vars_term l'"
      then have "vars_term (\<tau> x) \<subseteq> vars_term l \<union> vars_term l'" proof(cases "x \<in> set (map fst (right_substs l'' l'))")
        case True
        then obtain u where u:"(x, u) \<in> set (right_substs l'' l')" by auto
        then have "vars_term u \<subseteq> vars_term l"
          by (smt (verit, best) fun_poss_imp_poss poss_map_vars_term q'_poss right_substs_imp_props subset_trans vars_term_subt_at) 
        with u show ?thesis
          using innermost_overlap.apply_tau2 innermost_overlap_axioms by blast 
      next
        case False
        moreover from x have "x \<notin> set (map fst (left_substs l'' l'))"
          by (metis imageE l''_alt list.set_map map_fst_left_substs set_vars_term_list subsetD vars_map_vars_term x_diff_y)
        ultimately have "\<tau> x = Var x" unfolding \<tau>_def
          by (metis Un_iff map_append not_elem_subst_of set_append) 
        then show ?thesis 
          using x by simp
      qed
    }
    ultimately show ?thesis using vars_d' unfolding vars_term_ctxt_apply vars_term_subst
      by (smt (verit, del_insts) UN_extend_simps(10) UN_iff UnCI UnE ctxt_supt_id fun_poss_imp_poss poss_map_vars_term q'_poss subset_eq vars_term_ctxt_apply)
  qed         
  {fix x assume "x \<in> vars_term D'"
    then consider "x \<in> vars_term l" | "x \<in> vars_term l'" 
      using vars_d by blast
    then have "\<rho> x \<in> wf_pterm S" proof(cases)
      case 1
      then obtain j where j:"j < length (vars_distinct l)" "vars_distinct l ! j = x"
        by (metis in_set_idx linear_l linear_term_var_vars_term_list set_vars_term_list) 
      then show ?thesis
        using var_l_rho by (smt (verit, best) length_map linear_l linear_term_var_vars_term_list single_\<Delta>2.as_well single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term)
    next
      case 2
      then obtain i where i:"i < length (vars_term_list (to_pterm l'))" "vars_term_list (to_pterm l')!i = x"
        by (metis in_set_conv_nth set_vars_term_list vars_to_pterm)
      then have i':"i < length (vars_term_list l')"
        by (metis vars_to_pterm)
      from i have i'':"vars_term_list l'!i = x"
        by (metis vars_to_pterm)
      have well:"to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta> \<in> wf_pterm S" 
        using single_\<Delta>2.as_well lhs_subst_well_def to_pterm_wf_pterm by blast
      let ?q="var_poss_list (to_pterm l') ! i"
      let ?u="(to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)|_?q"
      have q_facts:"?q \<in> poss (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)" proof-
          have "?q \<in> poss (source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>))" proof-
          have "source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) = s|_p"
            unfolding p by (metis (no_types, lifting) co_init fun_mk_subst fun_poss_imp_poss p_q_pos(2) q'_poss s_def single_\<Delta>2.aq single_\<Delta>2.source_at_pq source.simps(1) source.simps(3) source_apply_subst source_to_pterm subt_at_append subt_at_subst to_pterm_wf_pterm) 
          moreover have "?q \<in> poss (s|_p)" 
            using l'_sigma_subst by (metis i' length_var_poss_list nth_mem poss_imp_subst_poss var_poss_imp_poss var_poss_list_sound var_poss_list_to_pterm)
          ultimately show ?thesis by presburger 
        qed
        moreover 
        {fix r assume le:"r <\<^sub>p ?q"
          have "?q \<in> poss l'" 
            using i by (metis length_var_poss_list nth_mem var_poss_imp_poss var_poss_list_sound var_poss_list_to_pterm)
          with le have "r \<in> fun_poss l'"  
            using fun_poss_append_poss by (metis less_pos_def') 
          then have "r \<notin> possL (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)" 
            using innermost_ov_contr by blast 
        }
        ultimately show ?thesis 
          using single_\<Delta>2.unlabeled_above_p well by blast 
      qed
      with well show ?thesis
        by (metis i' i'' subt_at_is_wf_pterm var_l'_rho var_poss_list_to_pterm)
    qed
  }
  then have "D' \<cdot> \<rho> \<in> wf_pterm S"
    using d'_well by (meson apply_subst_wf_pterm) 
  then show ?thesis
    using ctxt_wf_pterm[OF B single_\<Delta>2.q] by blast
qed

lemma measure_helper:
  assumes r1:"r \<in> possL A'" and r2:"r \<in> possL B'"
  shows "\<not> p \<le>\<^sub>p r"
proof
  assume "p \<le>\<^sub>p r" 
  then obtain r' where r':"r = p@r'"
    using less_eq_pos_def by auto 
  from r1 single_\<Delta>1.label_ctxt[OF A single_\<Delta>1.pq single_\<Delta>1.p single_\<Delta>1.q] have "r' \<in> possL (to_pterm (rhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>)"
    unfolding single_\<Delta>1.residual option.sel r' by force 
  then consider "r' \<in> possL (to_pterm (rhs \<alpha>))" | 
     "\<exists> r1 r2 x. r' = r1@r2 \<and> r1 \<in> poss (labeled_source (to_pterm (rhs \<alpha>))) \<and> (labeled_source (to_pterm (rhs \<alpha>)))|_r1 = Var x \<and> 
                 r2 \<in> labelposs ((labeled_source \<circ> \<langle>As\<rangle>\<^sub>\<alpha>) x)"
    using labelposs_subst labeled_source_apply_subst  by (metis (no_types, lifting) to_pterm_wf_pterm)
  then show False proof(cases)
    case 1
    then have False
      by (simp add: labeled_source_simple_pterm) 
    then show ?thesis by simp
  next
    case 2
    then obtain r1 r2 x where r1r2:"r' = r1@r2" and r1_pos:"r1 \<in> poss (labeled_source (to_pterm (rhs \<alpha>)))"
       "(labeled_source (to_pterm (rhs \<alpha>)))|_r1 = Var x" and r2_lab:"r2 \<in> labelposs ((labeled_source \<circ> \<langle>As\<rangle>\<^sub>\<alpha>) x)"
      by blast
    then have "x \<in> vars_term (rhs \<alpha>)"
      by (metis in_mono labeled_source_to_term poss_term_lab_to_term source_to_pterm term.set_intros(3) var_term_lab_to_term vars_term_subt_at)
    then have "x \<in> vars_term (lhs \<alpha>)" 
      using single_\<Delta>1.rule_in_TRS wf_trs_R unfolding wf_trs_def var_rhs_subset_lhs_def by blast
    then obtain i where i:"i < length (var_rule \<alpha>)" "(var_rule \<alpha>)!i = x"
      by (metis in_set_idx linear_term_var_vars_term_list set_vars_term_list single_\<Delta>1.lin_lhs) 
    with r2_lab have r2_lab':"r2 \<in> possL (As!i)"
      by (metis lhs_subst_var_i o_apply single_\<Delta>1.length_as) 
    then obtain \<gamma> n where \<gamma>:"get_label (labeled_source (As!i) |_r2) = Some (\<gamma>, n)"
      using possL_obtain_label by blast 
    let ?r\<gamma>="take (length r2 - n) r2"
    let ?pi="var_poss_list (labeled_lhs \<alpha>)!i"
    from \<gamma> have n:"n \<le> length (r2)"
      using i(1) label_term_max_value labelposs_subs_poss r2_lab' single_\<Delta>1.as_well by fastforce 
    from \<gamma> have oc5:"n \<le> length (p@?pi@r2)"
      using i(1) label_term_max_value labelposs_subs_poss r2_lab' single_\<Delta>1.as_well by fastforce 
    have i':"i < length (vars_term_list (labeled_lhs \<alpha>))"
      by (metis i(1) linear_term_var_vars_term_list single_\<Delta>1.lin_lhs vars_term_list_labeled_lhs) 
    then have pi_pos:"?pi \<in> poss (labeled_lhs \<alpha>)"
      by (metis length_var_poss_list nth_mem var_poss_imp_poss var_poss_list_sound)  
    have pi_not_empty:"?pi \<noteq> []" proof-
      from single_\<Delta>1.rule_in_TRS have "is_Fun (lhs \<alpha>)"
        using wf_trs_R unfolding wf_trs_def no_var_lhs_def by force 
      then have "[] \<notin> var_poss (lhs \<alpha>)"
        by fastforce
      moreover have "var_poss_list (labeled_lhs \<alpha>) = var_poss_list (lhs \<alpha>)"
        using var_poss_list_labeled_lhs by blast
      ultimately show ?thesis
        by (metis i' length_var_poss_list nth_mem var_poss_list_sound) 
    qed
    have as_i:"(\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) (vars_term_list (labeled_lhs \<alpha>) ! i) = labeled_source (As!i)"
      by (smt (verit, ccfv_SIG) i(1) length_map lhs_subst_var_i linear_term_var_vars_term_list nth_map single_\<Delta>1.length_as single_\<Delta>1.lin_lhs vars_term_list_labeled_lhs) 
    with r2_lab' i' have "?pi@r2 \<in> possL (Prule \<alpha> As)" 
      unfolding labeled_source.simps set_labelposs_subst by (smt (verit, ccfv_threshold) UN_iff UnCI lessThan_iff mem_Collect_eq)
    then have oc1:"p@?pi@r2 \<in> possL A" 
      using single_\<Delta>1.a single_\<Delta>1.label_ctxt[OF A single_\<Delta>1.pq single_\<Delta>1.p single_\<Delta>1.q]
      by (metis (no_types, lifting) get_label_imp_labelposs in_mono labeled_source_to_term labelposs_subs_poss option.discI p_q_pos(1) pos_append_poss possL_obtain_label poss_term_lab_to_term s_def single_\<Delta>1.aq single_\<Delta>1.labeled_source_at_pq subt_at_append)
    from \<gamma> have "get_label (labeled_source (Prule \<alpha> As) |_(?pi@r2)) = Some (\<gamma>, n)" 
      unfolding labeled_source.simps using as_i subt_at_append subt_at_subst pi_pos
      by (smt (verit, best) filter_cong fun_poss_imp_poss i' labeled_source.simps(3) labeled_source_to_term labelposs_subs_fun_poss_source oc1 poss_append_poss poss_term_lab_to_term single_\<Delta>1.aq single_\<Delta>1.labeled_source_at_pq eval_term.simps(1) vars_term_list_var_poss_list) 
    then have oc3:"get_label (labeled_source A |_(p@?pi@r2)) = Some (\<gamma>, n)" 
      using single_\<Delta>1.a single_\<Delta>1.pq  single_\<Delta>1.labeled_source_at_pq by (simp add: single_\<Delta>1.aq single_\<Delta>1.p)
    from r1_pos have yx:"rename_y (rhs \<alpha>) |_r1 = Var (y_var x)"
      by (metis Term.term.simps(9) labeled_source_to_term map_vars_term_subt_at poss_term_lab_to_term source_to_pterm var_term_lab_to_term) 
    then have li:"y_var x = vars_term_list l' ! i"
      by (metis i linear_term_var_vars_term_list nth_map single_\<Delta>1.lin_lhs vars_map_vars_term) 
    from r2 single_\<Delta>2.label_ctxt[OF B single_\<Delta>2.pq single_\<Delta>2.p single_\<Delta>2.q] have "q'@r' \<in> possL (D' \<cdot> \<rho>)"
      unfolding r' p by force 
    then consider "q'@r' \<in> possL D'" | 
     "\<exists> r1 r2 x. q'@r' = r1@r2 \<and> r1 \<in> poss (labeled_source D') \<and> (labeled_source D')|_r1 = Var x \<and> 
                 r2 \<in> labelposs ((labeled_source \<circ> \<rho>) x)"
    using labelposs_subst labeled_source_apply_subst d'_well by (metis (no_types, lifting))
    then show ?thesis proof(cases)
      case 1
      then have "q'@r' \<in> fun_poss (source D')"
        using labelposs_subs_fun_poss_source by auto 
      then have r'_pos:"r' \<in> fun_poss (rename_y (rhs \<alpha>) \<cdot> \<tau>)" 
        unfolding src_d' using fun_poss_in_ctxt fun_poss_imp_poss hole_pos_ctxt_of_pos_term poss_map_vars_term q'_poss by blast 
      from yx have "rename_y (rhs \<alpha>) \<cdot> \<tau> |_r1 = \<tau> (y_var x)"
        using r1_pos(1) by force 
      then have r2_funp:"r2 \<in> fun_poss (\<tau> (y_var x))"
        unfolding r1r2 by (metis fun_poss_in_ctxt fun_poss_imp_poss hole_pos_ctxt_of_pos_term poss_append_poss r'_pos r1r2 replace_at_ident)  
      then have "\<tau> (y_var x) \<noteq> Var (y_var x)"
        by force  
      then have "var_poss_list l' ! i \<in> fun_poss l''" 
        using var_in_domain_tau li i' by (smt (verit, del_insts) length_map vars_map_vars_term vars_term_list_labeled_lhs) 
      then have *:"?pi \<in> fun_poss l''"
        by (metis var_poss_list_labeled_lhs var_poss_list_map_vars_term) 
      have "((y_var x), l''|_?pi) \<in> set (right_substs l'' l')" proof-
        have "?pi \<in> poss l'" 
          using pi_pos by auto 
        moreover have "l'|_?pi = Var (y_var x)"
          by (smt (verit, ccfv_SIG) Term.term.simps(9) calculation filter_cong i' i(2) label_term_to_term linear_term_var_vars_term_list map_vars_term_subt_at pi_pos poss_map_vars_term single_\<Delta>1.lin_lhs var_term_lab_to_term vars_term_list_labeled_lhs vars_term_list_var_poss_list) 
        ultimately show ?thesis
          using props_imp_right_substs[OF *] by metis
      qed
      then have "\<tau> (y_var x) = l''|_?pi"
        using apply_tau2 by blast 
      with r2_funp have "r2 \<in> fun_poss (l''|_?pi)"
        by simp 
      then have "q'@?pi@r2 \<in> fun_poss l"
        by (smt (verit, del_insts) Diff_iff \<open>var_poss_list (labeled_lhs \<alpha>) ! i \<in> fun_poss (l |_ q')\<close> fun_poss_map_vars_term pos_append_poss poss_simps(3) q'_poss subterm_poss_conv var_poss_iff)
      then have funpos:"q'@?pi@r2 \<in> fun_poss (lhs \<beta>)"
        using fun_poss_map_vars_term by blast
      then have lab_beta:"get_label (labeled_source (Prule \<beta> Bs) |_(q'@?pi@r2)) = Some (\<beta>, length (q'@?pi@r2))" 
        using label_term_increase unfolding labeled_source.simps
        by (metis (no_types, lifting) length_0_conv length_append self_append_conv2)
      then have oc4:"get_label (labeled_source B |_(p@?pi@r2)) = Some (\<beta>, length (q'@?pi@r2))" proof-
        have "labeled_source B = (ctxt_of_pos_term q (labeled_source B))\<langle>labeled_source (Prule \<beta> Bs)\<rangle>"
          using single_\<Delta>2.a single_\<Delta>2.label_source_ctxt[OF B single_\<Delta>2.pq] by (metis single_\<Delta>2.p single_\<Delta>2.q)
        then have "labeled_source B |_(p@?pi@r2) = labeled_source (Prule \<beta> Bs) |_(q'@?pi@r2)"
          unfolding p using co_init p_q_pos(2) s_def single_\<Delta>2.aq single_\<Delta>2.labeled_source_at_pq by auto      
        then show ?thesis
          using lab_beta unfolding p by simp 
      qed
      then have oc2:"p @ ?pi @ r2 \<in> possL B"
        by (metis co_init fun_poss_imp_poss get_label_imp_labelposs labeled_source_to_term labelposs_subs_fun_poss_source oc1 option.discI poss_term_lab_to_term)
      have **:"take (length (p @ ?pi @ r2) - n) (p @ ?pi @ r2) = p@?pi@?r\<gamma>" 
        using n by simp
      have *:"take (length (p @ ?pi @ r2) - length (q' @ var_poss_list (labeled_lhs \<alpha>) ! i @ r2)) (p @ var_poss_list (labeled_lhs \<alpha>) ! i @ r2) = q"
        unfolding p by simp     
      have "(p@?pi@?r\<gamma>, q) \<in> overlaps_pos (labeled_source A) (labeled_source B)"
        using obtain_overlap[OF oc1 oc2 oc3 oc4 oc5] A B unfolding * ** using p
        by (smt (verit, ccfv_SIG) "*" append.assoc diff_is_0_eq less_eq_pos_simps(1) nat_le_linear self_append_conv2 take_eq_Nil2) 
      then show ?thesis using maximal pi_not_empty
        by (metis (no_types, lifting) append_is_Nil_conv fst_conv less_eq_overlap_def less_eq_pos_simps(1) self_append_conv snd_conv) 
    next
      case 2
      then obtain r3 r4 y where r3r4:"q' @ r' = r3 @ r4" "r3 \<in> poss (labeled_source D')" 
        "labeled_source D' |_ r3 = Var y" "r4 \<in> labelposs ((labeled_source \<circ> \<rho>) y)" 
        by blast 
      then have r3_pos:"r3 \<in> poss (source D')" by simp
      from r3r4 have y:"source D' |_r3 = Var y"
        by (metis labeled_source_to_term var_term_lab_to_term) 
      have "q'@r1 \<le>\<^sub>p r3" proof-
        from r3r4(1) have "q'@r1@r2 = r3@r4" 
          unfolding r1r2 by simp
        then consider "q'@r1 \<le>\<^sub>p r3" | "r3 <\<^sub>p q'@r1"
          by (metis append.assoc less_eq_pos_simps(1) pos_cases pos_less_eq_append_not_parallel) 
        then show ?thesis proof(cases)
          case 2
          have "q'@r1 \<in> poss (ctxt_of_pos_term q' l)\<langle>rename_y (rhs \<alpha>)\<rangle>"
            using r1_pos poss_term_lab_to_term
            by (metis fun_poss_imp_poss hole_pos_ctxt_of_pos_term hole_pos_poss labeled_source_to_term pos_append_poss poss_map_vars_term q'_poss replace_at_subt_at source_to_pterm) 
          then have "r3 \<in> fun_poss (source D')" 
            unfolding src_d' by (metis "2" ctxt_l_at_q' fun_poss_append_poss less_pos_def' poss_imp_subst_poss subst_apply_term_ctxt_apply_distrib) 
          then have False using r3r4
            by (metis fun_poss_fun_conv fun_poss_term_lab_to_term labeled_source_to_term term.distinct(1)) 
          then show ?thesis by simp
        qed simp
      qed
      then obtain r3' where r3:"r3 = q'@r1@r3'"
        using less_eq_pos_def by auto 
      have r3'_pos:"r3' \<in> poss (\<tau> (y_var x))" 
        using r3_pos y unfolding r3 src_d' using yx
        by (metis fun_poss_imp_poss labeled_source_to_term poss_map_vars_term poss_term_lab_to_term q'_poss r1_pos(1) replace_at_subt_at source_to_pterm eval_term.simps(1) subt_at_subst subterm_poss_conv) 
      have r3'_y:"(\<tau> (y_var x))|_r3' = Var y" 
        using r3_pos y unfolding r3 src_d' using yx
        by (metis fun_poss_imp_poss labeled_source_to_term poss_map_vars_term poss_term_lab_to_term q'_poss r1_pos(1) replace_at_subt_at source_to_pterm eval_term.simps(1) subt_at_subst subterm_poss_conv)
      then show ?thesis proof(cases "?pi \<in> fun_poss l''")
        case True
        have "((y_var x), l''|_?pi) \<in> set (right_substs l'' l')" proof-
          have "?pi \<in> poss l'" 
            using pi_pos by auto 
          moreover have "l'|_?pi = Var (y_var x)"
            by (smt (verit, ccfv_SIG) Term.term.simps(9) calculation filter_cong i' i(2) label_term_to_term linear_term_var_vars_term_list map_vars_term_subt_at pi_pos poss_map_vars_term single_\<Delta>1.lin_lhs var_term_lab_to_term vars_term_list_labeled_lhs vars_term_list_var_poss_list) 
          ultimately show ?thesis
            using props_imp_right_substs[OF True] by metis
        qed
        then have l''_pi:"\<tau> (y_var x) = l''|_?pi"
          using apply_tau2 by blast 
        with r3'_pos y yx have "y \<in> vars_term l''" 
          unfolding src_d' r3
          by (smt (verit, ccfv_SIG) True fun_poss_imp_poss labeled_source_to_term pos_append_poss poss_map_vars_term poss_term_lab_to_term q'_poss r1_pos(1) r3 r3_pos replace_at_subt_at source_to_pterm src_d' eval_term.simps(1) subt_at_subst subterm_poss_conv var_poss_iff vars_term_var_poss_iff) 
        then obtain j where j:"vars_term_list l ! j = y" "j < length (vars_term_list l)"
          by (smt (verit, best) fun_poss_imp_poss in_set_conv_nth poss_map_vars_term q'_poss set_vars_term_list subsetD vars_term_subt_at) 
        then have bsj:"\<rho> y = Bs!j" 
          using var_l_rho linear_l by (metis (no_types, lifting) linear_term_var_vars_term_list) 

        from r3r4 obtain \<delta> m where \<delta>:"get_label (labeled_source (\<rho> y) |_r4) = Some (\<delta>, m)"
          using possL_obtain_label by fastforce 
        then have oc6:"m \<le> length r4" 
          unfolding bsj using label_term_max_value
          by (smt (verit, best) bsj in_mono j(2) labelposs_subs_poss length_map linear_term_var_vars_term_list o_apply r3r4(4) single_\<Delta>2.as_well single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term) 
        let ?r\<delta>="take (length r4 - m) r4"
        have qj:"q' @ ?pi @ r3' = var_poss_list (labeled_lhs \<beta>) !j" proof-
          have "l |_ (q' @ var_poss_list (labeled_lhs \<alpha>) ! i @ r3') = \<tau> (y_var x) |_ r3'"
            using l''_pi by (simp add: True fun_poss_imp_poss q'_poss) 
          then have "l|_(q' @ ?pi @ r3') = Var y"
            using r3'_y by presburger
          with j have "q' @ ?pi @ r3' = var_poss_list l !j"
            using linear_l
            by (smt (verit, ccfv_SIG) True fun_poss_imp_poss l''_pi length_var_poss_list linear_term_unique_vars nth_mem pos_append_poss poss_map_vars_term q'_poss r3'_pos var_poss_imp_poss var_poss_list_sound vars_term_list_var_poss_list)
          then show ?thesis
            by (metis var_poss_list_labeled_lhs var_poss_list_map_vars_term)  
        qed
        have "get_label (labeled_source (Prule \<beta> Bs) |_(q'@?pi@r3'@r4)) = Some (\<delta>, m)"
        proof-
          from qj have sub_pos:"q' @ ?pi @ r3' \<in> poss (labeled_lhs \<beta>)"
            by (metis True \<open>\<tau> (y_var x) = l |_ q' |_ ?pi\<close> fun_poss_imp_poss label_term_to_term pos_append_poss poss_map_vars_term poss_term_lab_to_term q'_poss r3'_pos) 
          from qj have "labeled_lhs \<beta> |_(q' @ ?pi @ r3') = Var (vars_term_list (labeled_lhs \<beta>) ! j)"
            by (smt (verit) filter_cong j(2) length_map vars_map_vars_term vars_term_list_labeled_lhs vars_term_list_var_poss_list) 
          moreover have "(\<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>) (vars_term_list (labeled_lhs \<beta>) ! j) = labeled_source (Bs ! j)" 
            using j by (smt (verit, del_insts) length_map lhs_subst_var_i linear_term_var_vars_term_list nth_map single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term vars_term_list_labeled_lhs) 
          then have "labeled_source (Prule \<beta> Bs) |_(q'@?pi@r3') = labeled_source (Bs ! j)" 
            unfolding labeled_source.simps subt_at_subst[OF sub_pos] using calculation by force
          then have "labeled_source (Prule \<beta> Bs) |_(q'@?pi@r3'@r4) = labeled_source (Bs ! j) |_r4" 
            using sub_pos by (smt (verit, ccfv_SIG) labeled_source.simps(3) poss_append_poss poss_imp_subst_poss subt_at_append)
          with bsj \<delta> show ?thesis 
            by presburger
        qed
        then have oc4:"get_label (labeled_source B |_((p@?pi)@r3'@r4)) = Some (\<delta>, m)"
          unfolding p using single_\<Delta>2.a co_init p_q_pos(2) s_def single_\<Delta>2.aq single_\<Delta>2.labeled_source_at_pq by auto 
        have "((p@?pi)@r3'@r4) \<in> possL B" proof-
          have "r4 \<in> possL (Bs!j)" 
            using qj r3r4(4) \<delta> bsj
            by (smt (verit, ccfv_SIG) \<delta> get_label_imp_labelposs in_mono j(2) labelposs_subs_poss length_map linear_term_var_vars_term_list o_apply obtain_label_root option.discI single_\<Delta>2.as_well single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term)
          moreover have "(\<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>) (vars_term_list (labeled_lhs \<beta>) ! j) = labeled_source (Bs!j)" 
            using j(2)
            by (smt (verit, del_insts) apply_lhs_subst_var_rule length_map linear_term_var_vars_term_list nth_map single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term vars_term_list_labeled_lhs) 
          ultimately have "q' @ ?pi @ r3'@r4 \<in> possL (Prule \<beta> Bs)"
            unfolding labeled_source.simps set_labelposs_subst using qj j(2)
            by (smt (verit, ccfv_threshold) UN_iff UnCI append_assoc length_map lessThan_iff mem_Collect_eq vars_map_vars_term vars_term_list_labeled_lhs)
          then show ?thesis 
            using single_\<Delta>2.a single_\<Delta>2.label_ctxt[OF B single_\<Delta>2.pq single_\<Delta>2.p single_\<Delta>2.q] qj unfolding p
            by (metis (no_types, lifting) append.assoc labeled_source_to_term labelposs_subt_at poss_term_lab_to_term single_\<Delta>2.aq single_\<Delta>2.labeled_source_at_pq single_\<Delta>2.p) 
        qed
        moreover have r2:"r2 = r3'@r4"
          using r3 r3r4(1) r1r2 by auto 
        ultimately have oc2:"(p@?pi@r2) \<in> possL B" 
          by simp
        from r2 oc4 have oc4:"get_label (labeled_source B |_ (p @ ?pi @ r2)) = Some (\<delta>, m)" 
          by simp
        have *:"take (length (p @ ?pi @ r2) - n) (p @ ?pi @ r2) = p@?pi@?r\<gamma>" 
          using n by simp
        have **:"take (length (p @ ?pi @ r2) - m) (p @ ?pi @ r2) = p@?pi@r3'@?r\<delta>" 
          unfolding r2 using oc6 by simp
        from r2 consider "r3'@?r\<delta> \<le>\<^sub>p ?r\<gamma>" | "?r\<gamma> <\<^sub>p r3'@?r\<delta>"
          by (metis append_take_drop_id less_eq_pos_def less_eq_pos_simps(2) pos_cases pos_less_eq_append_not_parallel) 
        then have "(p@?pi@?r\<gamma>, p@?pi@r3'@?r\<delta>) \<in> overlaps_pos (labeled_source A) (labeled_source B)" proof(cases)
          case 1
            show ?thesis 
              using obtain_overlap[OF oc1 oc2 oc3 oc4 oc5] using r2 oc6 1 A B unfolding * **
              by (metis (no_types, lifting) "**" append_is_Nil_conv diff_is_0_eq less_eq_pos_simps(2) nat_le_linear pi_not_empty take_eq_Nil2) 
          next
            case 2 
            from oc6 r2 have oc6:"m \<le> length (p @ var_poss_list (labeled_lhs \<alpha>) ! i @ r2)" 
              by simp
            have "(p@?pi@r3'@?r\<delta>, p@?pi@?r\<gamma>) \<in> overlaps_pos (labeled_source B) (labeled_source A)"  
              using obtain_overlap[OF oc2 oc1 oc4 oc3 oc6 oc5] using r2 2 A B unfolding * **
              by (meson less_eq_pos_simps(2) order_pos.less_le_not_le) 
            then show ?thesis 
              using overlaps_pos_symmetric by blast 
        qed
        then show ?thesis using maximal pi_not_empty
          by (smt (verit) append.assoc append_is_Nil_conv fst_conv less_eq_overlap_def less_eq_pos_simps(1) p self_append_conv snd_conv) 
      next
        case False
        moreover have "\<forall>q \<in> poss l'. q \<noteq> (var_poss_list l'!i) \<longrightarrow> l'|_q \<noteq> Var (y_var x)" 
          using linear_l' by (metis i(1) length_var_poss_list li linear_term_unique_vars linear_term_var_vars_term_list nth_mem single_\<Delta>1.lin_lhs var_poss_imp_poss var_poss_list_map_vars_term var_poss_list_sound vars_term_list_var_poss_list)
        ultimately have "\<not> (\<exists>q. q \<in> fun_poss l'' \<and> q \<in> poss l' \<and> l' |_ q = Var (y_var x))"
          by (metis var_poss_list_labeled_lhs var_poss_list_map_vars_term) 
        then have "(y_var x) \<notin> set (map fst (right_substs l'' l'))" 
          using right_substs_imp_props by fastforce
        moreover have "(y_var x) \<notin> set (map fst (left_substs l'' l'))" 
          using li by (smt (verit, ccfv_threshold) disjoint_iff distinct distinct_append fun_poss_imp_poss i(1) in_mono length_map linear_term_var_vars_term_list map_fst_left_substs nth_mem poss_map_vars_term q'_poss set_vars_term_list single_\<Delta>1.lin_lhs vars_map_vars_term vars_term_subt_at) 
        ultimately have "\<tau> (y_var x) = Var (y_var x)" 
          unfolding \<tau>_def subst_of_append
          by (metis Un_iff map_append not_elem_subst_of set_append subst_of_append)  
        moreover with r3'_pos have r3':"r3' = []" 
          by simp
        ultimately have "(y_var x) = y"
          using r3'_y by simp 
        then have "y = vars_term_list l' !i"
          using li by simp
        moreover have pi_alt:"?pi = var_poss_list l' ! i"
          by (metis var_poss_list_labeled_lhs var_poss_list_map_vars_term) 
        ultimately have "\<rho> y = (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)|_?pi" 
          using var_l'_rho i' by (smt (verit, del_insts) i(1) length_map linear_term_var_vars_term_list single_\<Delta>1.lin_lhs vars_map_vars_term) 
        with r3r4(4) have "r4 \<in> possL ((to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)|_?pi)"
          by simp 
        moreover have pi_pos:"?pi \<in> poss (labeled_source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>))" proof-
          have "source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) = s|_p"
            by (metis (no_types, lifting) co_init fun_mk_subst fun_poss_imp_poss p p_q_pos(2) q'_poss s_def single_\<Delta>2.aq single_\<Delta>2.source_at_pq source.simps(1) source.simps(3) source_apply_subst source_to_pterm subt_at_append subt_at_subst to_pterm_wf_pterm) 
          moreover have "?pi \<in> poss (s|_p)"
            by (metis l'_sigma_subst label_term_to_term pi_pos poss_imp_subst_poss poss_map_vars_term poss_term_lab_to_term) 
          ultimately show ?thesis
            by force 
        qed
        moreover have "labeled_source (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>) |_ ?pi = labeled_source ((to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)|_?pi)" proof-
          have "to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta> \<in> wf_pterm S" 
            using single_\<Delta>2.as_well by (meson lhs_subst_well_def to_pterm_wf_pterm) 
          moreover
          {fix r assume "r <\<^sub>p ?pi"
            then have "r \<in> fun_poss l'" 
              using pi_alt
              by (metis fun_poss_append_poss i(1) length_var_poss_list less_pos_def' linear_term_var_vars_term_list nth_mem single_\<Delta>1.lin_lhs var_poss_imp_poss var_poss_list_map_vars_term var_poss_list_sound) 
            then have "r \<notin> possL (to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>)" 
              using innermost_ov_contr by simp
          }
          ultimately show ?thesis using single_\<Delta>2.unlabeled_above_p pi_pos
            by (smt (verit, del_insts) labeled_source_to_term poss_term_lab_to_term)        
        qed
        ultimately have "?pi@r4 \<in> possL ((to_pterm lhs\<^sub>\<beta>' \<cdot> \<langle>Bs\<rangle>\<^sub>\<beta>))"
          using labelposs_subt_at by metis 
        then have "?pi@r4 \<in> possL (to_pterm lhs\<^sub>\<beta>') \<or> (\<exists>p1 p2 x. ?pi@r4 = p1 @ p2 \<and> p1 \<in> poss (labeled_source (to_pterm lhs\<^sub>\<beta>'))  \<and> (labeled_source (to_pterm lhs\<^sub>\<beta>')) |_ p1 = Var x \<and> p2 \<in> possL ((\<langle>Bs\<rangle>\<^sub>\<beta>) x))"
          unfolding labeled_source_apply_subst[OF to_pterm_wf_pterm[of "lhs\<^sub>\<beta>'"]] using labelposs_subst[of "?pi@r4"] by (smt (verit, best) o_apply)
        then obtain r5 r6 y' where r5r6:"?pi@r4 = r5 @ r6" "r5 \<in> poss (labeled_source (to_pterm lhs\<^sub>\<beta>'))" "(labeled_source (to_pterm lhs\<^sub>\<beta>')) |_ r5 = Var y'" "r6 \<in> possL ((\<langle>Bs\<rangle>\<^sub>\<beta>) y')"
          using labeled_source_simple_pterm by blast
        from r5r6(2) have "q'@r5 \<in> poss (lhs \<beta>)"
          by (simp add: fun_poss_imp_poss q'_poss) 
        moreover from r5r6(3) have "lhs \<beta> |_(q'@r5) = Var y'"
          by (metis fun_poss_imp_poss labeled_source_to_term q'_poss r5r6(2) source_to_pterm subt_at_append var_term_lab_to_term) 
        ultimately obtain j where j:"q'@r5 = var_poss_list (lhs \<beta>) ! j" "j < length (vars_term_list (lhs \<beta>))"
          by (metis in_set_idx length_var_poss_list var_poss_iff var_poss_list_sound)
        with r5r6(3) have "vars_term_list (lhs \<beta>) ! j = y'"
          by (metis \<open>lhs \<beta> |_ (q' @ r5) = Var y'\<close> term.inject(1) vars_term_list_var_poss_list)  
        with j have bsj:"(\<langle>Bs\<rangle>\<^sub>\<beta>) y' = Bs!j"
          by (metis (no_types, lifting) lhs_subst_var_i linear_term_var_vars_term_list single_\<Delta>2.length_as single_\<Delta>2.lin_lhs) 
        with r5r6(4) obtain \<delta> m where \<delta>:"get_label (labeled_source (Bs!j)|_r6) = Some (\<delta>, m)"
          by (metis possL_obtain_label) 
        with bsj have m:"m \<le> length r6"
          by (metis (no_types, lifting) fun_poss_imp_poss j(2) label_term_max_value labeled_source_to_term labelposs_subs_fun_poss_source linear_term_var_vars_term_list poss_term_lab_to_term r5r6(4) single_\<Delta>2.as_well single_\<Delta>2.length_as single_\<Delta>2.lin_lhs) 
        let ?r\<delta>="take (length r6 - m) r6"
        let ?qj="var_poss_list (lhs \<beta>) ! j"
        have r2:"r2 = r4"
          using r3 r3r4(1) r1r2 r3' by auto 
        have oc2:"p @ ?pi @ r2 \<in> possL B" proof-
          from bsj r5r6(4) have "r6 \<in> possL (Bs!j)"
            by presburger 
          moreover have "(\<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>) (vars_term_list (labeled_lhs \<beta>) ! j) = labeled_source (Bs!j)" 
            using j(2)
            by (smt (verit, del_insts) apply_lhs_subst_var_rule length_map linear_term_var_vars_term_list nth_map single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_map_vars_term vars_term_list_labeled_lhs) 
          ultimately have "?qj@r6 \<in> possL (Prule \<beta> Bs)" 
            unfolding labeled_source.simps set_labelposs_subst 
            by (smt (z3) UN_iff UnCI filter_cong j(2) lessThan_iff mem_Collect_eq var_poss_list_labeled_lhs vars_term_list_labeled_lhs)
          then show ?thesis 
            using single_\<Delta>2.a single_\<Delta>2.label_ctxt[OF B single_\<Delta>2.pq single_\<Delta>2.p single_\<Delta>2.q] unfolding p r2 r5r6 append.assoc using j(1)
            by (metis (mono_tags, lifting) UnCI append.assoc mem_Collect_eq) 
        qed 
        have "get_label (labeled_source (Prule \<beta> Bs) |_(?qj@r6)) = Some (\<delta>, m)" 
        proof-
          have "labeled_source (Prule \<beta> Bs) |_(?qj) = labeled_source (Bs ! j)" 
            unfolding labeled_source.simps subt_at_subst
            by (smt (verit, ccfv_SIG) apply_lhs_subst_var_rule filter_cong j(2) length_map length_var_poss_list linear_term_var_vars_term_list map_nth_conv nth_mem single_\<Delta>2.length_as single_\<Delta>2.lin_lhs eval_term.simps(1) subt_at_subst var_poss_iff var_poss_list_labeled_lhs var_poss_list_sound vars_term_list_labeled_lhs vars_term_list_var_poss_list) 
          then have "labeled_source (Prule \<beta> Bs) |_(?qj@r6) = labeled_source (Bs ! j) |_r6"
            by (metis (no_types, lifting) \<open>q' @ r5 \<in> poss (lhs \<beta>)\<close> j(1) labeled_source_to_term poss_imp_subst_poss poss_term_lab_to_term source.simps(3) subt_at_append) 
          with bsj \<delta> show ?thesis 
            by presburger
        qed
        then have oc4:"get_label (labeled_source B |_(p @ ?pi @ r2)) = Some (\<delta>, m)"
          unfolding p r2 r5r6 append.assoc using j(1)
          by (metis append.assoc co_init labeled_source_to_term p_q_pos(2) poss_term_lab_to_term s_def single_\<Delta>2.aq single_\<Delta>2.labeled_source_at_pq subt_at_append) 
        have oc6:"m \<le> length (p @ ?pi @ r2)" 
          unfolding p r2 r5r6 append.assoc using j(1) m by simp
        have *:"take (length (p @ ?pi @ r2) - n) (p @ ?pi @ r2) = p@?pi@?r\<gamma>"
          using n by simp
        have **:"take (length (p @ ?pi @ r2) - m) (p @ ?pi @ r2) = q@?qj@?r\<delta>" 
          unfolding p r2 r5r6 append.assoc using j(1) m by simp
        from r5r6(1) consider "?qj@?r\<delta> \<le>\<^sub>p q'@?pi@ ?r\<gamma>" | "q'@?pi@ ?r\<gamma> <\<^sub>p ?qj@?r\<delta>"
          unfolding j(1)[symmetric] r2
          by (metis append_assoc append_take_drop_id less_eq_pos_simps(1) pos_cases pos_less_eq_append_not_parallel) 
        then have "(p@?pi@?r\<gamma>, q@?qj@?r\<delta>) \<in> overlaps_pos (labeled_source A) (labeled_source B)" proof(cases)
          case 1
          then show ?thesis using obtain_overlap[OF oc1 oc2 oc3 oc4 oc5 oc6] unfolding * ** using A B
            by (metis (no_types, lifting) append.assoc less_eq_pos_simps(2) p)
        next
          case 2
          have "(q@?qj@?r\<delta>, p@?pi@?r\<gamma>) \<in> overlaps_pos (labeled_source B) (labeled_source A)"  
            using obtain_overlap[OF oc2 oc1 oc4 oc3 oc6 oc5] using r2 2 A B unfolding * **
            by (metis (no_types, lifting) append.assoc less_eq_pos_simps(2) order_pos.less_le_not_le p)
          then show ?thesis 
            using overlaps_pos_symmetric by blast 
        qed
        then show ?thesis 
          using maximal pi_not_empty by (smt (verit) append.assoc append_is_Nil_conv fst_conv less_eq_overlap_def less_eq_pos_simps(1) p self_append_conv snd_conv)
      qed
    qed
  qed 
qed

lemma measure_dec: "measure_ov A' B' < measure_ov A B"
proof-
  {fix r assume "r \<in> possL A' \<inter> possL B'"
    then have r1:"r \<in> possL A'" and r2:"r \<in> possL B'" by blast+
    then have r_not_below:"\<not> p \<le>\<^sub>p r"
      using measure_helper by blast 
    with r1 single_\<Delta>1.label_ctxt[OF A single_\<Delta>1.pq single_\<Delta>1.p single_\<Delta>1.q] have rA:"r \<in> possL A"
      unfolding single_\<Delta>1.residual option.sel by force 
    have rB:"r \<in> possL B" proof(cases "q \<le>\<^sub>p r")
      case True
      from True obtain r' where r':"r = q@r'"
        using less_eq_pos_remove_prefix by auto 
      with r2 single_\<Delta>2.label_ctxt[OF B single_\<Delta>2.pq single_\<Delta>2.p single_\<Delta>2.q] have "r' \<in> possL (D' \<cdot> \<rho>)"
        unfolding r' by force 
      then have "r' \<in> labelposs (labeled_source D' \<cdot> (labeled_source \<circ> \<rho>))"
        by (metis d'_well labeled_source_apply_subst)
      then consider "r' \<in> labelposs (labeled_source D')" | 
         "\<exists> r1 r2 x. r' = r1@r2 \<and> r1 \<in> poss (labeled_source D') \<and> (labeled_source D')|_r1 = Var x \<and> 
                     r2 \<in> labelposs ((labeled_source \<circ> \<rho>) x)"
        using labelposs_subst by blast
      then show ?thesis proof(cases)
        case 1
        then have r'_fun:"r' \<in> fun_poss ((ctxt_of_pos_term q' l)\<langle>rename_y (rhs \<alpha>) \<cdot> \<tau>\<rangle>)"
          using labelposs_subs_fun_poss_source src_d' by fastforce 
        with r_not_below have "r' \<in> fun_poss l"
          unfolding r' p using replace_at_fun_poss_not_below  q'_poss fun_poss_imp_poss by (metis less_eq_pos_simps(2) poss_map_vars_term) 
        then have "r' \<in> fun_poss (lhs \<beta>)"
          by (simp add: fun_poss_map_vars_term)
        then have "r' \<in> labelposs (labeled_lhs \<beta>)"
          by (simp add: label_poss_labeled_lhs) 
        then have "r' \<in> possL (Prule \<beta> Bs)" 
          unfolding labeled_source.simps set_labelposs_subst by simp
        then have "r \<in> possL B"                              
          using single_\<Delta>2.label_ctxt[OF B single_\<Delta>2.pq single_\<Delta>2.p single_\<Delta>2.q] r' single_\<Delta>2.a
          by (metis (mono_tags, lifting) Un_iff mem_Collect_eq) 
        with rA show ?thesis by simp
      next
        case 2
        then obtain r1 r2 x where r12:"r' = r1@r2" and r1_pos:"r1 \<in> poss (source D')" and x:"source D' |_ r1 = Var x"
          and r2_lab:"r2 \<in> labelposs ((labeled_source \<circ> \<rho>) x)" 
          using poss_term_lab_to_term labeled_source_to_term var_term_lab_to_term by metis
        from r_not_below consider "r <\<^sub>p p" | "r \<bottom> p"
          using parallel_pos by fastforce 
        then show ?thesis proof(cases)
          case 1
          then have le:"r1 <\<^sub>p q'"
            unfolding p r' r12 using less_eq_pos_simps(1) less_pos_simps(2) order_pos.dual_order.strict_trans2 by blast 
          moreover have "q' \<in> poss (source D')"
            by (simp add: fun_poss_imp_poss q'_poss replace_at_below_poss src_d') 
          ultimately have False 
            using x by (metis less_pos_def' r1_pos var_pos_maximal) 
          then show ?thesis by simp
        next
          case 2
          from r_not_below have r1_not_below:"\<not> q' \<le>\<^sub>p r1"
            unfolding p r' r12 using less_eq_pos_simps(1) less_eq_pos_simps(2) order_pos.order_trans by blast
          with r1_pos have r1_pos':"r1 \<in> poss l" 
            unfolding src_d' using fun_poss_imp_poss poss_map_vars_term q'_poss 
            by (metis order_pos.less_le parallel_poss_replace_at pos_cases replace_at_below_poss replace_at_ident) 
          then have x':"l|_r1 = Var x" 
            using x r1_not_below unfolding src_d'
            by (metis fun_poss_imp_poss less_eq_pos_def order_pos.dual_order.eq_iff parallel_pos parallel_replace_at_subt_at poss_map_vars_term q'_poss replace_at_below_poss var_pos_maximal) 
          with r1_pos' obtain j where j:"j < length (var_poss_list l)" "var_poss_list l ! j = r1"
            by (metis in_set_conv_nth var_poss_iff var_poss_list_sound)
          with linear_l x' have "vars_distinct l ! j = x"
            by (metis length_var_poss_list linear_term_var_vars_term_list term.inject(1) vars_term_list_var_poss_list) 
          then have "\<rho> x = Bs!j" 
            using var_l_rho j(1) by (metis (no_types, lifting) length_var_poss_list linear_l linear_term_var_vars_term_list) 
          with r2_lab have r2_pos:"r2 \<in> possL (Bs!j)"
            by auto  
          from j have j1:"j < length (vars_term_list (labeled_lhs \<beta>))"
            by (metis length_map length_var_poss_list vars_map_vars_term vars_term_list_labeled_lhs) 
          from j have j2:"var_poss_list (labeled_lhs \<beta>) ! j = r1"
            by (metis var_poss_list_labeled_lhs var_poss_list_map_vars_term) 
          moreover have "(\<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>) (vars_term_list (labeled_lhs \<beta>)!j) = labeled_source (Bs!j)"
          using j1
          by (smt (verit, best) apply_lhs_subst_var_rule fun_mk_subst labeled_source.simps(1) linear_term_var_vars_term_list nth_map o_apply single_\<Delta>2.length_as single_\<Delta>2.lin_lhs vars_term_list_labeled_lhs) 
          ultimately have "r1@r2 \<in> possL (Prule \<beta> Bs)" 
            unfolding labeled_source.simps using j1 j2 r2_pos set_labelposs_subst[of "labeled_lhs \<beta>" "\<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>"]
            by (smt (verit, del_insts) UN_iff UnCI lessThan_iff mem_Collect_eq)
          then show ?thesis using single_\<Delta>2.a unfolding r' r12
            using single_\<Delta>2.label_ctxt[OF B single_\<Delta>2.pq single_\<Delta>2.p single_\<Delta>2.q] by (metis (mono_tags, lifting) UnCI mem_Collect_eq)
        qed
      qed
    next
      case False
      then show ?thesis 
        using r2 single_\<Delta>2.label_ctxt[OF B single_\<Delta>2.pq single_\<Delta>2.p single_\<Delta>2.q] by force 
    qed
    from rA rB have "r \<in> possL A \<inter> possL B" by simp
  }
  moreover from pq have "p \<in> possL A \<inter> possL B"
    using co_init get_label_imp_labelposs le p_q_pos(1) s_def by force
  moreover have "p \<notin> possL A' \<inter> possL B'" 
    using measure_helper parallel_pos by auto
  ultimately show ?thesis 
    using psubset_card_mono finite_possL by (metis finite_Int psubsetI subsetI) 
qed

lemma target_beta_Bs:
  shows "target (Prule \<beta> Bs) = target (to_pterm (rename_x (rhs \<beta>) \<cdot> \<tau>) \<cdot> \<rho>)" 
proof-
  {fix y assume "y \<in> vars_term (rhs \<beta>)"
    then have y:"y \<in> vars_term (lhs \<beta>)"
      using single_\<Delta>2.rule_in_TRS wf_trs_S unfolding wf_trs_def var_rhs_subset_lhs_def by blast
    then obtain j where j:"j < length (vars_term_list (lhs \<beta>))" "(vars_term_list (lhs \<beta>))!j = y"
      by (metis in_set_conv_nth set_vars_term_list) 
    let ?y="x_var y"
    from j have "vars_term_list l ! j = ?y"
      by (metis nth_map vars_map_vars_term) 
    with j(1) have "to_pterm (\<tau> ?y) \<cdot> \<rho> = Bs!j" 
      using apply_tau_rho  by (smt (verit, best) length_map vars_map_vars_term)
    moreover from j have "(\<langle>Bs\<rangle>\<^sub>\<beta>) y = Bs!j"
      by (metis (no_types, lifting) lhs_subst_var_i linear_term_var_vars_term_list single_\<Delta>2.length_as single_\<Delta>2.lin_lhs) 
    ultimately have "((to_pterm \<circ> (\<tau> \<circ> x_var)) \<circ>\<^sub>s \<rho>) y = (\<langle>Bs\<rangle>\<^sub>\<beta>) y"
      by (simp add: subst_compose_def)  
  }note args_beta=this
  have "target (to_pterm (rename_x (rhs \<beta>) \<cdot> \<tau>) \<cdot> \<rho>) = (rhs \<beta>) \<cdot> (target \<circ> ((to_pterm \<circ> (\<tau> \<circ> x_var)) \<circ>\<^sub>s \<rho>))" 
    using var_rhs_subset_lhs.target_apply_subst wf_trs_S 
    unfolding apply_subst_map_vars_term to_pterm_subst subst_subst wf_trs_def
    by (metis (no_types, lifting) target_to_pterm to_pterm_wf_pterm) 
  also have "... = target (Prule \<beta> Bs)" 
    unfolding target.simps using args_beta by (smt (verit) fun_mk_subst o_apply target.simps(1) term_subst_eq)
  finally show ?thesis by simp
qed

lemma rewrite_target_B':
  assumes "(rename_x (rhs \<beta>) \<cdot> \<tau>, target D') \<in> (rstep R)\<^sup>*"
  shows "(target B, target B') \<in> (rstep R)\<^sup>*"
proof-
  have "target B = target (replace_at B q\<^sub>\<beta> ((to_pterm (rename_x (rhs \<beta>) \<cdot> \<tau>) \<cdot> \<rho>)))"
    using target_beta_Bs by (metis context_target single_\<Delta>2.a)
  moreover have "target B' = target (replace_at B q\<^sub>\<beta> ((to_pterm (target D') \<cdot> \<rho>)))"
    using context_target var_rhs_subset_lhs.tgt_subst_simp wf_trs_S d'_well unfolding wf_trs_def by metis
  ultimately show ?thesis 
    using assms rewrite_tgt by metis
qed

lemma target_B':
  assumes "target D' = rename_x (rhs \<beta>) \<cdot> \<tau>"
  shows "target B' = target B"
proof-
  have "target (D'\<cdot>\<rho>) = target (to_pterm (rename_x (rhs \<beta>) \<cdot> \<tau>) \<cdot> \<rho>)" 
    using var_rhs_subset_lhs.tgt_subst_simp wf_trs_S d'_well assms unfolding wf_trs_def by metis
  then show ?thesis using target_beta_Bs by (metis context_target single_\<Delta>2.a)
qed

end

lemma exists_A'_B'_w:
  assumes mstep:"((ctxt_of_pos_term q' l)\<langle>rename_y (rhs \<alpha>) \<cdot> \<tau>\<rangle>, v'') \<in> mstep S"  
      and rstep:"(rename_x (rhs \<beta>) \<cdot> \<tau>, v'') \<in> (rstep R)\<^sup>*"
    shows "\<exists>A' B'. A' \<in> wf_pterm R \<and> B' \<in> wf_pterm S \<and> 
  source A' = source B' \<and> target A' = target A \<and> (target B, target B') \<in> (rstep R)\<^sup>* \<and> measure_ov A' B' < measure_ov A B \<and> source A' = target \<Delta>1"
proof-
  from mstep obtain D' where D':"D' \<in> wf_pterm S \<and> source D' = (ctxt_of_pos_term q' l)\<langle>rename_y (rhs \<alpha>) \<cdot> \<tau>\<rangle> \<and> target D' = v''"
    using var_rhs_subset_lhs.mstep_to_pterm wf_trs_S unfolding wf_trs_def by blast 
  let ?v'="replace_at s p (v'' \<cdot> \<sigma>)"
  from D' obtain B'' w where "B'' \<in> wf_pterm S" and "measure_ov A' B'' < measure_ov A B" and "source B'' = source A'"
    and "target B'' = w" and "(target B, w) \<in> (rstep R)\<^sup>*" 
    using rewrite_target_B' rstep by (metis B'_well measure_dec source_B')
  moreover have "source A' = target \<Delta>1"
    using A residual_src_tgt single_\<Delta>1.delta_trs_wf_pterm single_\<Delta>1.residual by fastforce 
  ultimately show ?thesis
    by (metis single_\<Delta>1.residual_well single_\<Delta>1.target_residual) 
qed

lemma exists_A'_B':
  assumes "(replace_at l q' (rename_y (rhs \<alpha>) \<cdot> \<tau>), rename_x (rhs \<beta>) \<cdot> \<tau>) \<in> mstep S"
  shows "\<exists>A' B'. A' \<in> wf_pterm R \<and> B' \<in> wf_pterm S \<and> 
  source A' = source B' \<and> target A' = target A \<and> target B' = target B \<and> measure_ov A' B' < measure_ov A B \<and> source A' = target \<Delta>1"
proof-
  from assms obtain D' where "D' \<in> wf_pterm S \<and> 
    source D' = replace_at l q' (rename_y (rhs \<alpha>) \<cdot> \<tau>) \<and> 
    target D' = rename_x (rhs \<beta>) \<cdot> \<tau>"
    using var_rhs_subset_lhs.mstep_to_pterm wf_trs_S unfolding wf_trs_def by blast 
  then obtain B'' where "B'' \<in> wf_pterm S" and "measure_ov A' B'' < measure_ov A B" and "source B'' = source A'"
    and "target B'' = target B" using measure_dec source_B' target_B' B'_well by meson
  moreover have "source A' = target \<Delta>1"
    using A residual_src_tgt single_\<Delta>1.delta_trs_wf_pterm single_\<Delta>1.residual by fastforce 
  ultimately show ?thesis
    by (metis single_\<Delta>1.residual_well single_\<Delta>1.target_residual) 
qed

end

section\<open>Main Proof\<close>
lemma mstep_closed_strongly_commute:
assumes closed_1:"\<And>s t b. (b, s, t) \<in> critical_pairs ren R2 R1 \<Longrightarrow> \<exists>v. (s, v) \<in> mstep R2 \<and> (t, v) \<in> (rstep R1)\<^sup>*"
    and closed_2:"\<And>s t. (False, s, t) \<in> critical_pairs ren R1 R2 \<Longrightarrow> (s, t) \<in> mstep R1"
    and R1:"left_lin_wf_trs R1" and R2:"left_lin_wf_trs R2"
  shows "strongly_commute (mstep R1) (mstep R2)"
proof (rule strongly_commuteI)
  fix s t u assume "(s, t) \<in> mstep R1" and "(s, u) \<in> mstep R2"
  from R1 \<open>(s,t) \<in> mstep R1\<close> obtain A where A:"A \<in> wf_pterm R1 \<and> source A = s" and t_a:"target A = t"
    using var_rhs_subset_lhs.mstep_to_pterm unfolding left_lin_wf_trs_def wf_trs_def by blast 
  from R2 \<open>(s,u) \<in> mstep R2\<close> obtain B where B:"B \<in> wf_pterm R2 \<and> source B = s" and t_b:"target B = u"
    using var_rhs_subset_lhs.mstep_to_pterm unfolding left_lin_wf_trs_def wf_trs_def by blast 
  from A B t_a t_b have "\<exists>v. (t, v) \<in> mstep R2 \<and> (u, v) \<in> (rstep R1)\<^sup>*"
  proof(induct "measure_ov A B" arbitrary: A B s u rule:less_induct)
    case less
    show ?case proof(cases "measure_ov A B")
      case 0
      from 0 less.prems have "A re B \<noteq> None"
        using measure_zero_imp_orthogonal R1 R2 orth_imp_residual_defined
        by (metis wf_trs_def case_prodD left_lin_no_var_lhs_def left_lin_wf_trs_def no_var_lhs.no_var_lhs) 
      with less.prems obtain D where d:"A re B = Some D \<and> target B = source D \<and> D \<in> wf_pterm R1"
        by (metis not_Some_eq residual_src_tgt residual_well_defined) 
      from 0 less.prems have "B re A \<noteq> None"
        using measure_zero_imp_orthogonal R1 R2 orth_imp_residual_defined
        by (metis Int_commute Proof_Terms.wf_trs_def case_prodD left_lin_no_var_lhs_def left_lin_wf_trs_def no_var_lhs.no_var_lhs)
      with less.prems obtain C where c:"B re A = Some C \<and> target A = source C \<and> C \<in> wf_pterm R2"
        by (metis not_Some_eq residual_src_tgt residual_well_defined) 
      from c d less.prems have "target C = target D" 
        using residual_tgt_tgt by blast 
      with c d less.prems(3,4) show ?thesis 
        using pterm_to_mstep by (metis mstep_imp_rsteps)
    next
      case (Suc n)
      with less(2,3) have "overlaps_pos (labeled_source A) (labeled_source B) \<noteq> {}"
        using empty_overlaps_imp_measure_zero by force 
      then have "\<exists>m\<in>overlaps_pos (labeled_source A) (labeled_source B).
         \<forall>b\<in>overlaps_pos (labeled_source A) (labeled_source B). m \<le>\<^sub>o b \<longrightarrow> m = b"
        by (simp add: finite_fun_poss order_overlaps.finite_has_maximal) 
      then obtain p q where pq:"(p, q) \<in> overlaps_pos (labeled_source A) (labeled_source B)" and 
          innermost:"(\<forall>b\<in>overlaps_pos (labeled_source A) (labeled_source B). (p,q) \<le>\<^sub>o b \<longrightarrow> (p,q) = b)"
        by (metis (no_types, lifting) prod.collapse)
      then have "p \<in> poss (labeled_source A)"
        by (meson fun_poss_imp_poss mem_Sigma_iff member_filter) 
      moreover obtain \<alpha> where alpha:"get_label (labeled_source A |_ p) = Some (\<alpha>, 0)" 
        using pq by auto 
      ultimately obtain p\<^sub>\<alpha> where p\<^sub>\<alpha>:"p\<^sub>\<alpha> \<in> poss A" "ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term p\<^sub>\<alpha> A)"
        "A|_p\<^sub>\<alpha> = Prule \<alpha> (map (\<lambda>i. A|_(p\<^sub>\<alpha>@[i])) [0..<length (var_rule \<alpha>)])"
        using left_lin.poss_labeled_source R1 less.prems(1) unfolding wf_trs_def left_lin_wf_trs_def by fastforce
      from pq have "q \<in> poss (labeled_source B)"
        by (meson fun_poss_imp_poss mem_Sigma_iff member_filter) 
      moreover obtain \<beta> where beta:"get_label (labeled_source B |_ q) = Some (\<beta>, 0)" 
        using pq by auto 
      ultimately obtain q\<^sub>\<beta> where q\<^sub>\<beta>:"q\<^sub>\<beta> \<in> poss B" "ctxt_of_pos_term q (source B) = source_ctxt (ctxt_of_pos_term q\<^sub>\<beta> B)"
        "B|_q\<^sub>\<beta> = Prule \<beta> (map (\<lambda>i. B|_(q\<^sub>\<beta>@[i])) [0..<length (var_rule \<beta>)])"
        using left_lin.poss_labeled_source R2 less.prems(2) unfolding wf_trs_def left_lin_wf_trs_def by fastforce
      consider "q \<le>\<^sub>p p" | "p <\<^sub>p q"
        using pq less_pos_def by fastforce
      then show ?thesis proof(cases)
        case 1
        then obtain q' where q':"Some q' = remove_prefix q p"
          by (metis less_eq_pos_remove_prefix)
        then have io:"innermost_overlap R1 R2 A B p q q' p\<^sub>\<alpha> q\<^sub>\<beta> \<alpha> \<beta>" 
          unfolding innermost_overlap_def using R1 R2 less.prems pq innermost q' alpha beta p\<^sub>\<alpha> q\<^sub>\<beta> by auto
        obtain A' B' where "A' \<in> wf_pterm R1"  "B' \<in> wf_pterm R2"
            "source A' = source B'" "target A' = target A" and tgt:"(target B, target B') \<in> (rstep R1)\<^sup>*" and m:" measure_ov A' B' < measure_ov A B"
          using innermost_overlap.exists_A'_B'_w[OF io] innermost_overlap.critical_pair[OF io] closed_1 by meson 
        with less.hyps[OF m] obtain v where "(t, v) \<in> mstep R2 \<and> (target B', v) \<in> (rstep R1)\<^sup>*"
            using less.prems(3) by presburger
        with tgt show ?thesis
          by (metis less.prems(4) mstep_rsteps_subset rstep_mstep_subset rtrancl_subset rtrancl_trans) 
      next
        case 2
        then have p_not_q:"p \<noteq> q" by simp
        from 2 obtain q' where q':"Some q' = remove_prefix p q"
          using less_pos_def' by auto
        have qp:"(q, p) \<in> overlaps_pos (labeled_source B) (labeled_source A)"
          using overlaps_pos_symmetric[OF pq].
        have innermost':"(\<forall>b\<in>overlaps_pos (labeled_source B) (labeled_source A). (q,p) \<le>\<^sub>o b \<longrightarrow> (q,p) = b)" proof-
          {fix b1 b2 assume assm:"(b1, b2) \<in> overlaps_pos (labeled_source B) (labeled_source A)" 
                        and le:"(q,p) \<le>\<^sub>o (b1, b2)" and ne:"(q,p) \<noteq> (b1, b2)"
            then have *:"(b2, b1) \<in> overlaps_pos (labeled_source A) (labeled_source B)"
              using overlaps_pos_symmetric by blast 
            from le have "(p,q) \<le>\<^sub>o (b2, b1)" unfolding less_eq_overlap_def less_overlap_def fst_conv snd_conv
              by (smt (z3) "2" assm case_prodD less_pos_def member_filter ne order_pos.leD order_pos.max_def order_pos.min_def)
            with innermost * ne have False by fastforce 
          }then show ?thesis
            by (metis (no_types, lifting) SigmaE member_filter) 
        qed
        have io:"innermost_overlap R2 R1 B A q p q' q\<^sub>\<beta> p\<^sub>\<alpha> \<beta> \<alpha>" 
          unfolding innermost_overlap_def using R1 R2 less.prems qp innermost' q' beta alpha p\<^sub>\<alpha> q\<^sub>\<beta> by auto
        obtain A' B' where "A' \<in> wf_pterm R1" and "B' \<in> wf_pterm R2"
          and "source A' = source B'" and "target A' = target A" and "target B' = target B" and m:"measure_ov A' B' < measure_ov A B"
          using innermost_overlap.exists_A'_B'[OF io] p_not_q innermost_overlap.critical_pair[OF io] closed_2 by (smt (verit) measure_ov_symm)
        with less.prems less.hyps[OF m] show ?thesis by simp
      qed
    qed 
  qed
  then show "\<exists>v. (t, v) \<in> (mstep R2)\<^sup>= \<and> (u, v) \<in> (mstep R1)\<^sup>*"
    by (metis Un_iff mstep_rsteps_subset rstep_mstep_subset rtrancl_subset) 
qed

corollary mstep_closed_imp_commute:
 assumes closed_1:"\<And>s t b. (b, s, t) \<in> critical_pairs ren R2 R1 \<Longrightarrow> \<exists>v. (s, v) \<in> mstep R2 \<and> (t, v) \<in> (rstep R1)\<^sup>*"
    and closed_2:"\<And>s t. (False, s, t) \<in> critical_pairs ren R1 R2 \<Longrightarrow> (s, t) \<in> mstep R1"
    and R1:"left_lin_wf_trs R1" and R2:"left_lin_wf_trs R2"
  shows "commute (rstep R1) (rstep R2)"
proof
  fix x y\<^sub>1 y\<^sub>2
  assume "(x, y\<^sub>1) \<in> (rstep R1)\<^sup>*" and "(x, y\<^sub>2) \<in> (rstep R2)\<^sup>*"
  then have "(x, y\<^sub>1) \<in> (mstep R1)\<^sup>*" and "(x, y\<^sub>2) \<in> (mstep R2)\<^sup>*"
    using rtrancl_mono[OF rstep_mstep_subset] by auto
  from commuteE[OF strongly_commute_imp_commute[OF mstep_closed_strongly_commute[OF assms]] this]
  obtain z where "(y\<^sub>1, z) \<in> (mstep R2)\<^sup>* \<and> (y\<^sub>2, z) \<in> (mstep R1)\<^sup>*"  by fast
  then show "\<exists>z. (y\<^sub>1, z) \<in> (rstep R2)\<^sup>* \<and> (y\<^sub>2, z) \<in> (rstep R1)\<^sup>*"
    using rtrancl_mono[OF mstep_rsteps_subset] rtrancl_idemp by auto
qed

corollary mstep_closed_imp_CR:
  assumes "\<And>s t. (False, s, t) \<in> critical_pairs ren R R \<Longrightarrow> (s, t) \<in> mstep R"
    and "\<And>s t. (True, s, t) \<in> critical_pairs ren R R \<Longrightarrow> \<exists>v. (s, v) \<in> mstep R \<and> (t, v) \<in> (rstep R)\<^sup>*"
    and "left_lin_wf_trs R"
  shows "CR (rstep R)"
proof-
  from assms(1,2) have "\<And>b s t. (b, s, t) \<in> critical_pairs ren R R \<Longrightarrow> \<exists>v. (s, v) \<in> mstep R \<and> (t, v) \<in> (rstep R)\<^sup>*"
    by (metis rtrancl.rtrancl_refl) 
  with assms(1,3-) show ?thesis using mstep_closed_imp_commute[of ren R R]
    using CR_iff_self_commute[of "rstep R"] by blast
qed

section\<open>Commutation via Relative Termination\<close>
(*Extending the proofs in "Commutation via Relative Termination"@IWC2013 to 'almost' version.*)

(*Key Lemma (generalizing Lemma 4.1. of IWC2013)*)
lemma critical_peak_step_cases:
  assumes t:"(s,t) \<in> mstep R" and u:"(s,u) \<in> mstep S"
    and R:"left_lin_wf_trs R" and S:"left_lin_wf_trs S"
  shows "(\<exists>v. (t,v) \<in> mstep S \<and> (u,v) \<in> (rstep R)\<^sup>*) \<or> 
         (\<exists>s' t' u' w .(s,s') \<in> (rstep (R \<union> S))\<^sup>* \<and> (s', t') \<in> rstep (CPS_R ren R S) \<and> (t', t) \<in> mstep R 
                           \<and> (u, w) \<in> (rstep R)\<^sup>* \<and> (s', u') \<in> rstep (CPS_S ren R S) \<and> (u', w) \<in> mstep S)"
proof-
  from t obtain A where A:"A \<in> wf_pterm R" "source A = s" "target A = t"
    using var_rhs_subset_lhs.mstep_to_pterm R unfolding wf_trs_def left_lin_wf_trs_def by blast
  from u  obtain B where B:"B \<in> wf_pterm S" "source B = s" "target B = u"
    using var_rhs_subset_lhs.mstep_to_pterm S unfolding wf_trs_def left_lin_wf_trs_def by blast
  from A B show ?thesis
  proof(induct "measure_ov A B" arbitrary: A B s u rule:less_induct)
    case less
    show ?case proof(cases "measure_ov A B")
      case 0
      from 0 less.prems have "A re B \<noteq> None"
        using measure_zero_imp_orthogonal orth_imp_residual_defined R S unfolding left_lin_wf_trs_def
        by (metis case_prodD left_lin_no_var_lhs.intro no_var_lhs.no_var_lhs wf_trs.axioms(1)) 
      with less.prems obtain D where d:"A re B = Some D \<and> target B = source D \<and> D \<in> wf_pterm R"
        using residual_well_defined[OF less.prems(1,4)] not_Some_eq residual_src_tgt by metis
      from 0 less.prems have "B re A \<noteq> None"
        using measure_zero_imp_orthogonal orth_imp_residual_defined R S unfolding left_lin_wf_trs_def
        by (metis Int_commute case_prodD left_lin_no_var_lhs.intro no_var_lhs.no_var_lhs wf_trs.axioms(1)) 
      with less.prems obtain C where c:"B re A = Some C \<and> target A = source C \<and> C \<in> wf_pterm S"
        using residual_well_defined[OF less.prems(4,1)] not_Some_eq residual_src_tgt by metis
      from c d less.prems have "target C = target D" 
        using residual_tgt_tgt by blast 
      with c d less.prems(3,6) show ?thesis
        by (metis mstep_imp_rsteps pterm_to_mstep) 
    next
      case (Suc n)
      with less(2,5) have "overlaps_pos (labeled_source A) (labeled_source B) \<noteq> {}"
        using empty_overlaps_imp_measure_zero by force 
      then have "\<exists>m\<in>overlaps_pos (labeled_source A) (labeled_source B).
         \<forall>b\<in>overlaps_pos (labeled_source A) (labeled_source B). m \<le>\<^sub>o b \<longrightarrow> m = b"
        by (simp add: finite_fun_poss order_overlaps.finite_has_maximal) 
      then obtain p q where pq:"(p, q) \<in> overlaps_pos (labeled_source A) (labeled_source B)" and 
          innermost:"(\<forall>b\<in>overlaps_pos (labeled_source A) (labeled_source B). (p,q) \<le>\<^sub>o b \<longrightarrow> (p,q) = b)"
        by (metis (no_types, lifting) prod.collapse)
      then have p:"p \<in> poss (labeled_source A)"
        by (meson fun_poss_imp_poss mem_Sigma_iff member_filter) 
      moreover obtain \<alpha> where alpha:"get_label (labeled_source A |_ p) = Some (\<alpha>, 0)" 
        using pq by auto 
      ultimately obtain p\<^sub>\<alpha> where p\<^sub>\<alpha>:"p\<^sub>\<alpha> \<in> poss A" "ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term p\<^sub>\<alpha> A)"
        "A|_p\<^sub>\<alpha> = Prule \<alpha> (map (\<lambda>i. A|_(p\<^sub>\<alpha>@[i])) [0..<length (var_rule \<alpha>)])"
        using left_lin.poss_labeled_source less.prems(1) R unfolding wf_trs_def left_lin_wf_trs_def by fastforce
      from alpha less.prems(1) have \<alpha>:"to_rule \<alpha> \<in> R"
        using labeled_wf_pterm_rule_in_TRS p by blast  
      from pq have q:"q \<in> poss (labeled_source B)"
        by (meson fun_poss_imp_poss mem_Sigma_iff member_filter) 
      moreover obtain \<beta> where beta:"get_label (labeled_source B |_ q) = Some (\<beta>, 0)" 
        using pq by auto 
      ultimately obtain q\<^sub>\<beta> where q\<^sub>\<beta>:"q\<^sub>\<beta> \<in> poss B" "ctxt_of_pos_term q (source B) = source_ctxt (ctxt_of_pos_term q\<^sub>\<beta> B)"
        "B|_q\<^sub>\<beta> = Prule \<beta> (map (\<lambda>i. B|_(q\<^sub>\<beta>@[i])) [0..<length (var_rule \<beta>)])"
        using left_lin.poss_labeled_source less.prems(4) S unfolding wf_trs_def left_lin_wf_trs_def by fastforce
      from beta less.prems(4) have \<beta>:"to_rule \<beta> \<in> S"
        using labeled_wf_pterm_rule_in_TRS q by blast  
      consider "q \<le>\<^sub>p p" | "p <\<^sub>p q"
        using pq less_pos_def by fastforce
      then show ?thesis proof(cases)
        case 1
        then obtain q' where q':"Some q' = remove_prefix q p"
          by (metis less_eq_pos_remove_prefix)
        then have io:"innermost_overlap R S A B p q q' p\<^sub>\<alpha> q\<^sub>\<beta> \<alpha> \<beta>" 
          unfolding innermost_overlap_def using R S less.prems pq innermost q' alpha beta p\<^sub>\<alpha> q\<^sub>\<beta> by auto
        let ?a="(to_pterm_ctxt (ctxt_of_pos_term q' (rename_x ren (lhs \<beta>))))\<langle>Prule \<alpha> (map (to_pterm \<circ> innermost_overlap.\<tau> ren q' \<alpha> \<beta> \<circ> rename_2 ren) (var_rule \<alpha>))\<rangle>"
        let ?b="Prule \<beta> (map (to_pterm \<circ> innermost_overlap.\<tau> ren q' \<alpha> \<beta> \<circ> rename_1 ren) (var_rule \<beta>))"
        let ?\<Delta>1="ll_single_redex s p \<alpha>"
        let ?\<Delta>2="ll_single_redex s q \<beta>"
        have *:"vars_term (rhs \<alpha>) \<subseteq> vars_term (lhs \<alpha>)" 
          using \<alpha> R var_rhs_subset_lhs.varcond unfolding wf_trs_def left_lin_wf_trs_def by fastforce 
        have tgt_a:"target ?a = (ctxt_of_pos_term q' (rename_x ren (lhs \<beta>)))\<langle>rename_y ren (rhs \<alpha>) \<cdot> innermost_overlap.\<tau> ren q' \<alpha> \<beta>\<rangle>"
          unfolding target_to_pterm_ctxt target.simps map_map lhs_subst_var_rule[OF *]
          by (smt (verit) apply_subst_map_vars_term comp_assoc target_empty_apply_subst target_to_pterm to_pterm_empty to_pterm_subst) 
        have **:"vars_term (rhs \<beta>) \<subseteq> vars_term (lhs \<beta>)" 
          using \<beta> S var_rhs_subset_lhs.varcond unfolding wf_trs_def left_lin_wf_trs_def by fastforce 
        have tgt_b:"target ?b = rename_x ren (rhs \<beta>) \<cdot> innermost_overlap.\<tau> ren q' \<alpha> \<beta>"
          unfolding target.simps map_map lhs_subst_var_rule[OF **]
          by (smt (verit) apply_subst_map_vars_term comp_assoc target_empty_apply_subst target_to_pterm to_pterm_empty to_pterm_subst)
        from innermost_overlap.critical_peak[OF io] have cp:"(?a, ?b) \<in> pterm_cpeaks ren R S".
        show ?thesis proof(cases "is_R_S_closed R S (?a, ?b)")
          case True
          then obtain v'' where v'':"(target ?a,v'') \<in> mstep S" "(target ?b,v'') \<in> (rstep R)\<^sup>*" 
            unfolding is_R_S_closed.simps by blast 
          obtain A' B' where A':"A' \<in> wf_pterm R" and B':"B' \<in> wf_pterm S" and src_A':"source A' = target ?\<Delta>1"
            and "source A' = source B'" and "target A' = target A" and tgt:"(target B, target B') \<in> (rstep R)\<^sup>*" and m:"measure_ov A' B' < measure_ov A B"
            using innermost_overlap.exists_A'_B'_w[OF io v''[unfolded tgt_a tgt_b]] by (metis innermost_overlap.s_def io less.prems(2))
          with less.hyps[OF m A'] consider "\<exists>v. (t, v) \<in> mstep S \<and> (target B', v) \<in> (rstep R)\<^sup>*" |
            "(\<exists>s' t' u' w .(source A',s') \<in> (rstep (R \<union> S))\<^sup>* \<and> (s', t') \<in> rstep (CPS_R ren R S) \<and> (t', t) \<in> mstep R 
            \<and> (target B', w) \<in> (rstep R)\<^sup>* \<and> (s', u') \<in> rstep (CPS_S ren R S) \<and> (u', w) \<in> mstep S)"
            using less.prems(3) less.prems(6) by fastforce
          then show ?thesis proof(cases)
            case 1
            then show ?thesis using tgt less(7) by auto
          next
            case 2
            then obtain s' t' u' w where steps:"(source A', s') \<in> (rstep (R \<union> S))\<^sup>*" "(s', t') \<in> rstep (CPS_R ren R S)" "(t', t) \<in> mstep R" 
                "(target B', w) \<in> (rstep R)\<^sup>*" "(s', u') \<in> rstep (CPS_S ren R S)" "(u', w) \<in> mstep S"
              by blast
            have "(s, source A') \<in> rstep R"
              by (metis \<alpha> innermost_overlap.s_def innermost_overlap.source_d1 io labeled_source_to_term less.prems(2) p poss_term_lab_to_term single_redex_rstep src_A')
            with steps(1) have s':"(s, s') \<in> (rstep (R \<union> S))\<^sup>*"
              by (metis UnCI converse_rtrancl_into_rtrancl rstep_union) 
            from steps(4) tgt less.prems(6) have "(u, w) \<in> (rstep R)\<^sup>*"
              by auto 
            with steps show ?thesis
              using s' by blast  
          qed
        next
          case False
          then have "(source ?a, target ?a) \<in> CPS_R ren R S" 
            unfolding CPS_R_def using cp by blast 
          with innermost_overlap.\<Delta>1_is_rstep[OF io] 
          have cps_R:"(source ?\<Delta>1, target ?\<Delta>1) \<in> rstep (CPS_R ren R S)"
            by (metis innermost_overlap.s_def io less.prems(2)) 
          from False have "(source ?b, target ?b) \<in> CPS_S ren R S" 
            unfolding CPS_S_def using cp by blast 
          with innermost_overlap.\<Delta>2_is_rstep[OF io] 
          have cps_S:"(source ?\<Delta>2, target ?\<Delta>2) \<in> rstep (CPS_S ren R S)"
            by (metis innermost_overlap.s_def io less.prems(2))
          from p\<^sub>\<alpha> have d1:"single_redex R A ?\<Delta>1 p p\<^sub>\<alpha> \<alpha>"
            using single_redex.intro R single_redex_axioms.intro[OF less.prems(1)]
            by (metis innermost_overlap.ll_no_var_lhs_R io labeled_source_to_term less.prems(2) p poss_term_lab_to_term)
          then have A':"the (A re ?\<Delta>1) \<in> wf_pterm R" 
            by (simp add: single_redex.residual_well)
          from q\<^sub>\<beta> have d2:"single_redex S B ?\<Delta>2 q q\<^sub>\<beta> \<beta>"
            using single_redex.intro S single_redex_axioms.intro[OF less.prems(4)]
            by (metis innermost_overlap.ll_no_var_lhs_S io labeled_source_to_term less.prems(5) poss_term_lab_to_term q) 
          then have B':"the (B re ?\<Delta>2) \<in> wf_pterm S"
            by (simp add: single_redex.residual_well) 
          have "(\<exists>t' u'. (s, t') \<in> rstep (CPS_R ren R S) \<and> (t', t) \<in> mstep R 
                       \<and> (s, u') \<in> rstep (CPS_S ren R S) \<and> (u', u) \<in> mstep S)" 
            using cps_R cps_S pterm_to_mstep[OF A'] pterm_to_mstep[OF B'] less.prems
            by (smt (verit) d1 d2 innermost_overlap.s_def innermost_overlap.source_d1 innermost_overlap.source_d2 io option.sel residual_src_tgt single_redex.delta_trs_wf_pterm single_redex.residual single_redex.target_residual)
          then show ?thesis by blast
        qed
      next
        case 2
        then have p_not_q:"p \<noteq> q" by simp
        from 2 obtain q' where q':"Some q' = remove_prefix p q"
          using less_pos_def' by auto
        have qp:"(q, p) \<in> overlaps_pos (labeled_source B) (labeled_source A)"
          using overlaps_pos_symmetric[OF pq].
        have innermost':"(\<forall>b\<in>overlaps_pos (labeled_source B) (labeled_source A). (q,p) \<le>\<^sub>o b \<longrightarrow> (q,p) = b)" proof-
          {fix b1 b2 assume assm:"(b1, b2) \<in> overlaps_pos (labeled_source B) (labeled_source A)" 
                        and le:"(q,p) \<le>\<^sub>o (b1, b2)" and ne:"(q,p) \<noteq> (b1, b2)"
            then have *:"(b2, b1) \<in> overlaps_pos (labeled_source A) (labeled_source B)"
              using overlaps_pos_symmetric by blast 
            from le have "(p,q) \<le>\<^sub>o (b2, b1)" unfolding less_eq_overlap_def less_overlap_def fst_conv snd_conv
              by (smt (z3) "2" assm case_prodD less_pos_def member_filter ne order_pos.leD order_pos.max_def order_pos.min_def)
            with innermost * ne have False by fastforce 
          }then show ?thesis
            by (metis (no_types, lifting) SigmaE member_filter) 
        qed
        have io:"innermost_overlap S R B A q p q' q\<^sub>\<beta> p\<^sub>\<alpha> \<beta> \<alpha>" 
          unfolding innermost_overlap_def using R S less.prems qp innermost' q' beta alpha p\<^sub>\<alpha> q\<^sub>\<beta> by auto
        let ?\<tau>="innermost_overlap.\<tau> ren q' \<beta> \<alpha>"
        let ?b="(to_pterm_ctxt (ctxt_of_pos_term q' (rename_x ren (lhs \<alpha>))))\<langle>Prule \<beta> (map (to_pterm \<circ> ?\<tau> \<circ> rename_2 ren) (var_rule \<beta>))\<rangle>"
        let ?a="Prule \<alpha> (map (to_pterm \<circ> ?\<tau> \<circ> rename_1 ren) (var_rule \<alpha>))"
        let ?\<Delta>1="ll_single_redex s p \<alpha>"
        let ?\<Delta>2="ll_single_redex s q \<beta>"  
        have *:"vars_term (rhs \<alpha>) \<subseteq> vars_term (lhs \<alpha>)" 
          using \<alpha> R var_rhs_subset_lhs.varcond unfolding left_lin_wf_trs_def wf_trs_def by fastforce 
        have **:"vars_term (rhs \<beta>) \<subseteq> vars_term (lhs \<beta>)" 
          using \<beta> S var_rhs_subset_lhs.varcond unfolding left_lin_wf_trs_def wf_trs_def by fastforce  
        from \<alpha> obtain f ts where lhsa:"lhs \<alpha> = Fun f ts"
          using no_var_lhs.no_var_lhs R unfolding left_lin_wf_trs_def wf_trs_def by fastforce 
         have "q' \<noteq> []"
           by (metis append.right_neutral p_not_q q' remove_prefix_Some) 
         moreover have "q' \<in> poss (lhs \<alpha>)"
           using fun_poss_imp_poss innermost_overlap.q'_poss io by blast 
         ultimately obtain i q'' where iq:"q' = i#q''" and "i < length ts" and "q'' \<in> poss (ts!i)"
           using lhsa by auto
         then obtain ts' where b_fun:"?b = Pfun f ts'" 
           unfolding lhsa iq by force
        have tgt_a:"target ?b = (ctxt_of_pos_term q' (rename_x ren (lhs \<alpha>)))\<langle>rename_y ren (rhs \<beta>) \<cdot> ?\<tau>\<rangle>"
          unfolding target_to_pterm_ctxt target.simps map_map lhs_subst_var_rule[OF **]
          by (smt (verit) apply_subst_map_vars_term comp_assoc target_empty_apply_subst target_to_pterm to_pterm_empty to_pterm_subst)  
        have tgt_b:"target ?a = rename_x ren (rhs \<alpha>) \<cdot> ?\<tau>"
          unfolding target.simps map_map lhs_subst_var_rule[OF *]
          by (smt (verit) apply_subst_map_vars_term comp_assoc target_empty_apply_subst target_to_pterm to_pterm_empty to_pterm_subst)
        from innermost_overlap.critical_peak[OF io] have cp:"(?b, ?a) \<in> pterm_cpeaks ren S R".
        show ?thesis proof(cases "is_R_S_closed R S (?a, ?b)")
          case True
          then have "(target ?b, target ?a) \<in> mstep R" unfolding b_fun is_R_S_closed.simps .
          then obtain A' B' where A':"A' \<in> wf_pterm R" and B':"B' \<in> wf_pterm S" and src_A':"source B' = target ?\<Delta>2"
            and "source A' = source B'" and tgt:"target A' = target A" "target B' = target B" and m:"measure_ov A' B' < measure_ov A B"
            using innermost_overlap.exists_A'_B'[OF io] unfolding tgt_a tgt_b
            by (metis innermost_overlap.s_def io less.prems(5) measure_ov_symm) 
          with less.hyps[OF m A'] consider "\<exists>v. (t, v) \<in> mstep S \<and> (target B', v) \<in> (rstep R)\<^sup>*" |
            "(\<exists>s' t' u' w .(source B',s') \<in> (rstep (R \<union> S))\<^sup>* \<and> (s', t') \<in> rstep (CPS_R ren R S) \<and> (t', t) \<in> mstep R 
            \<and> (target B', w) \<in> (rstep R)\<^sup>* \<and> (s', u') \<in> rstep (CPS_S ren R S) \<and> (u', w) \<in> mstep S)"
            using less.prems(3) less.prems(6) by fastforce
          then show ?thesis proof(cases)
            case 1
            then show ?thesis using tgt less(7) by auto
          next
            case 2
            then obtain s' t' u' w where steps:"(source B', s') \<in> (rstep (R \<union> S))\<^sup>*" "(s', t') \<in> rstep (CPS_R ren R S)" "(t', t) \<in> mstep R" 
                "(target B', w) \<in> (rstep R)\<^sup>*" "(s', u') \<in> rstep (CPS_S ren R S)" "(u', w) \<in> mstep S"
              by blast
            have "(s, source B') \<in> rstep S"
              by (metis \<beta> innermost_overlap.s_def innermost_overlap.source_d1 io labeled_source_to_term less.prems(5) poss_term_lab_to_term q single_redex_rstep src_A') 
            with steps(1) have s':"(s, s') \<in> (rstep (R \<union> S))\<^sup>*"
              by (metis UnCI converse_rtrancl_into_rtrancl rstep_union) 
            from steps(4) tgt less.prems(6) have "(u, w) \<in> (rstep R)\<^sup>*"
              by auto 
            with steps show ?thesis
              using s' by blast  
          qed
        next
          case False
          then have "(source ?a, target ?a) \<in> CPS_R ren R S" 
            unfolding CPS_R_def using cp by blast 
          with innermost_overlap.\<Delta>2_is_rstep[OF io] 
          have cps_R:"(source ?\<Delta>1, target ?\<Delta>1) \<in> rstep (CPS_R ren R S)"
            by (metis innermost_overlap.s_def io less.prems(5)) 
          from False have "(source ?b, target ?b) \<in> CPS_S ren R S" 
            unfolding CPS_S_def using cp by blast 
          with innermost_overlap.\<Delta>1_is_rstep[OF io] False
          have cps_S:"(source ?\<Delta>2, target ?\<Delta>2) \<in> rstep (CPS_S ren R S)"
            by (metis innermost_overlap.s_def io less.prems(5))
          from p\<^sub>\<alpha> have d1:"single_redex R A ?\<Delta>1 p p\<^sub>\<alpha> \<alpha>"
            using single_redex.intro R single_redex_axioms.intro[OF less.prems(1)]
            by (metis innermost_overlap.ll_no_var_lhs_S io labeled_source_to_term less.prems(2) p poss_term_lab_to_term)
          then have A':"the (A re ?\<Delta>1) \<in> wf_pterm R" 
            by (simp add: single_redex.residual_well)
          from q\<^sub>\<beta> have d2:"single_redex S B ?\<Delta>2 q q\<^sub>\<beta> \<beta>"
            using single_redex.intro S single_redex_axioms.intro[OF less.prems(4)] less.prems(5) q
            by (metis innermost_overlap.ll_no_var_lhs_R io labeled_source_to_term poss_term_lab_to_term) 
          then have B':"the (B re ?\<Delta>2) \<in> wf_pterm S"
            by (simp add: single_redex.residual_well)
          have "(\<exists>t' u'. (s, t') \<in> rstep (CPS_R ren R S) \<and> (t', t) \<in> mstep R 
                       \<and> (s, u') \<in> rstep (CPS_S ren R S) \<and> (u', u) \<in> mstep S)" 
            using cps_R cps_S pterm_to_mstep[OF A'] pterm_to_mstep[OF B'] less.prems
            by (smt (verit) d1 d2 innermost_overlap.s_def innermost_overlap.source_d1 innermost_overlap.source_d2 io option.sel residual_src_tgt single_redex.delta_trs_wf_pterm single_redex.residual single_redex.target_residual)
          then show ?thesis by blast
        qed
      qed
    qed 
  qed
qed

lemma CPS''_SN_rel_imp_comm:
  assumes SN_rel:"SN_rel (rstep (CPS_R ren R S) \<union> rstep (CPS_S ren R S)) (rstep (R \<union> S))"
  and lc:"locally_commute (rstep R) (rstep S)"
  and R_wf:"left_lin_wf_trs R" and S_wf:"left_lin_wf_trs S"
shows "commute (rstep R) (rstep S)"
proof-
  let ?R = "\<lambda>(n, s). {(t,u) |t u. (t,u) \<in> mstep R \<and> (s,t) \<in> (rstep (R \<union> S))\<^sup>* \<and> n = 0}"
  let ?S = "\<lambda>(n, s). {(t,u) |t u. (t,u) \<in> mstep S \<and> (s,t) \<in> (rstep (R \<union> S))\<^sup>* \<and> n = 1}"
 (*s > t if s rewrites to t using the rules of R and S and the rewrite sequence contains at least one CPS step*)
  let ?r' = "((relto (rstep (CPS_R ren R S) \<union> rstep (CPS_S ren R S)) (rstep (R \<union> S)))\<inverse>)\<^sup>+" 
  let ?r = "lex_prod less_than ?r'"
  have R: "(\<Union>i. ?R i) = mstep R" and S: "(\<Union>i. ?S i) = mstep S" by auto
  have "commute (mstep R) (mstep S)" proof (induct rule:dd_commute[of ?r ?R ?S, unfolded R S])
    case 1
    from SN_rel show ?case
      using SN_iff_wf SN_rel_imp_SN_relto wf_trancl by blast
  next
    case 2
    then show ?case by simp
  next
    case (3 a b s t u)
    from 3(1) obtain s1 where s1_s:"(s1, s) \<in> (rstep (R \<union> S))\<^sup>*" and a:"a = (0, s1)" 
      by blast 
    from 3(2) obtain s2 where s2_s:"(s2, s) \<in> (rstep (R \<union> S))\<^sup>*" and b:"b = (1, s2)"
      by blast 
    (*apply Key Lemma*)
    from 3(1) have m1:"(s, t) \<in> mstep R"
      by force 
    from 3(2) have m2:"(s, u) \<in> mstep S"
      by force
    let ?conv="conversion'' ?R ?S (under ?r a \<union> under ?r b)"
    (*helper lemma for sequences of steps over R*)
    {fix x y assume ms:"(x,y) \<in> (mstep R)\<^sup>*" and "(s2, x) \<in> (rstep (R \<union> S))\<^sup>*"
      from rtrancl_imp_seq[OF ms] obtain f n where "f 0 = x" "f n = y" "(\<forall>i<n. (f i, f (Suc i)) \<in> mstep R)" by blast
      then have "(y,x) \<in> ((\<Union>i \<in> (under ?r b). ?R i)\<inverse>)\<^sup>*" proof(induct n arbitrary: y)
        case 0
        then show ?case by fastforce
      next
        case (Suc n)
        obtain y' where y':"f n = y'"
          by simp 
        from Suc(1)[OF Suc(2) y'] Suc(4) have IH:"(y', x) \<in> ((\<Union>i \<in> (under ?r b). ?R i)\<inverse>)\<^sup>*"
          using less_Suc_eq by presburger
        have "(x, y') \<in> (mstep R)\<^sup>*"
          using Suc.prems(1) Suc.prems(3) less_SucI rtrancl_fun_conv y' by metis
        then have "(x, y') \<in> (rstep (R \<union> S))\<^sup>*"
          by (metis in_rtrancl_UnI mstep_rsteps_subset rstep_mstep_subset rstep_union rtrancl_subset)
        with y' Suc(3,4) have "(y', y) \<in> ?R (0,x)"
          by blast
        moreover have "(0, x) \<in> under ?r b" unfolding b under_def by simp
        ultimately have "(y', y) \<in> (\<Union>i \<in> (under ?r b). ?R i)"
          by blast 
        with IH show ?case
          by (meson converse_iff converse_rtrancl_into_rtrancl)
      qed
      then have "(y, x) \<in> ?conv"  
        by (metis (no_types, lifting) UN_Un in_rtrancl_UnI rtrancl_converseD rtrancl_converseI) 
    }note seq_steps_R=this
   (*analogous helper lemma for sequences of steps over S*)
    {fix x y assume ms:"(x,y) \<in> (mstep S)\<^sup>*" and under:"(x, s2) \<in> ?r'"
      from rtrancl_imp_seq[OF ms] obtain f n where "f 0 = x" and "f n = y" and "(\<forall>i<n. (f i, f (Suc i)) \<in> mstep S)"
          by blast        
        then have "(x, y) \<in> (\<Union>i \<in> (under ?r b). ?S i)\<^sup>*" proof(induct n arbitrary: y) 
          case 0
          then show ?case
            by fastforce
        next
          case (Suc n)
          obtain y' where v':"f n = y'"
            by simp 
          from Suc(1)[OF Suc(2) v'] Suc(4) have IH:"(x, y') \<in> (\<Union>i \<in> (under ?r b). ?S i)\<^sup>*"
            using less_Suc_eq by presburger
          have "(x, y') \<in> (mstep S)\<^sup>*"
            by (metis (no_types, opaque_lifting) Suc.prems(1) Suc.prems(3) less_SucI rtrancl_fun_conv v')
          then have "(x, y') \<in> (rstep (R \<union> S))\<^sup>*"
            by (metis in_rtrancl_UnI mstep_rsteps_subset rstep_mstep_subset rstep_union rtrancl_subset)
          with v' Suc(3,4) have "(y', y) \<in> ?S (1, x)"
            by blast
          moreover from under have "(1, x) \<in> under ?r b"
            unfolding b under_def by simp
          ultimately have "(y', y) \<in> (\<Union>i \<in> (under ?r b). ?S i)"
            by blast
          with IH show ?case
            by (meson rtrancl.rtrancl_into_rtrancl)
        qed
    }note seq_steps_S=this
    consider "\<exists>v. (t, v) \<in> mstep S \<and> (u, v) \<in> (rstep R)\<^sup>*" | 
        "\<exists>s' t' u' w. (s, s') \<in> (rstep (R \<union> S))\<^sup>* \<and> (s', t') \<in> rstep (CPS_R ren R S) \<and> (t', t) \<in> mstep R \<and> (u, w) \<in> (rstep R)\<^sup>* \<and> (s', u') \<in> rstep (CPS_S ren R S) \<and> (u', w) \<in> mstep S"
      using critical_peak_step_cases[OF m1 m2] R_wf S_wf by blast
    then show ?case proof(cases)
      case 1 (*corresponds to Figure 1(a)*)
      then obtain v where m3:"(t, v) \<in> mstep S" and m4:"(u, v) \<in> (rstep R)\<^sup>*"
        by auto
      from s2_s m1 have "(s2, t) \<in> (rstep (R \<union> S))\<^sup>*"
        by (metis in_rtrancl_UnI mstep_imp_rsteps rstep_union rtrancl_trans)
      with m3 have "(t,v) \<in> {(t, u) |t u. (t, u) \<in> mstep S \<and> (s2, t) \<in> (rstep (R \<union> S))\<^sup>*}\<^sup>="
        by blast 
      then have *:"(t, v) \<in> (?S b)\<^sup>="
        unfolding b by blast
      from m4 have "(u,v) \<in> (mstep R)\<^sup>*"
        by (meson rstep_mstep_subset rtrancl_mono subsetD) 
      moreover from s2_s m2 have "(s2, u) \<in> (rstep (R \<union> S))\<^sup>*"
        by (metis in_rtrancl_UnI mstep_imp_rsteps rstep_union rtrancl_trans)
      ultimately have "(v, u) \<in> ?conv" 
        using seq_steps_R by simp
      with * show ?thesis by blast
    next
      case 2 (*corresponds to diagram in proof of Theorem 4.3*)
      then obtain s' t' u' w where s':"(s, s') \<in> (rstep (R \<union> S))\<^sup>*" 
                             and cps1:"(s', t') \<in> rstep (CPS_R ren R S)" and mstep1:"(t', t) \<in> mstep R" 
                             and w:"(u, w) \<in> (rstep R)\<^sup>*" and cps2:"(s', u') \<in> rstep (CPS_S ren R S)" and mstep2:"(u', w) \<in> mstep S"
        by blast 
      from cps1 CPS_R_rstep have "(s', t') \<in> rstep R" 
        by blast 
      moreover from cps2 CPS_S_rstep have s'u':"(s',u') \<in> rstep S" 
        by blast
      ultimately obtain v where "(t', v) \<in> (rstep S)\<^sup>*" and "(u', v) \<in> (rstep R)\<^sup>*" 
        using locally_commute_E11[OF lc] by meson 
      then have msteps:"(t', v) \<in> (mstep S)\<^sup>*" "(u', v) \<in> (mstep R)\<^sup>*" 
        by (metis mstep_rsteps_subset rstep_mstep_subset rtrancl_subset)+ 
      have c1:"(t, t') \<in> ?conv" proof-
        from cps1 have "(t', s1) \<in> ?r'"
          using rtrancl_trans[OF s1_s s'] by blast
        then have "(0, t') \<in> under ?r a"
          unfolding a by (simp add: under_def)
        with mstep1 have "(t, t') \<in> (\<Union>i \<in> (under ?r a). ?R i)\<inverse>"
          by blast
        then show ?thesis using UN_Un by blast 
      qed
      have c2:"(u', w) \<in> ?conv" proof-
        from cps2 have "(u', s2) \<in> ?r'" 
          using rtrancl_trans[OF s2_s s'] by blast
        then have "(1, u') \<in> under ?r b"
          unfolding b by (simp add: under_def)
        with mstep2 have "(u', w) \<in> (\<Union>i \<in> (under ?r b). ?S i)"
          by blast
        then show ?thesis using UN_Un by blast 
      qed
      have c3:"(t', v) \<in> ?conv" proof-
        from cps1 have "(t', s2) \<in> ?r'"
          using rtrancl_trans[OF s2_s s'] by blast
        from seq_steps_S[OF msteps(1) this] have "(t', v) \<in> (\<Union>i \<in> (under ?r b). ?S i)\<^sup>*"
          by blast 
        then show ?thesis by (simp add: in_rtrancl_UnI)
      qed
      have c4:"(v, u') \<in> ?conv" proof-
        have "(s2, u') \<in> (rstep (R \<union> S))\<^sup>*" using s2_s s'u' s'
          by (metis (no_types, lifting) UnCI rstep_union rtrancl.simps rtrancl_trans) 
        then show ?thesis using seq_steps_R[OF msteps(2)] by simp
      qed
      have c5:"(w, u) \<in> ?conv" proof-
        from w have w:"(u,w) \<in> (mstep R)\<^sup>*"
          by (metis mstep_rsteps_subset rstep_mstep_subset rtrancl_subset)
        have "(s2, u) \<in> (rstep (R \<union> S))\<^sup>*"
          by (metis in_rtrancl_UnI m2 mstep_imp_rsteps rstep_union rtrancl_trans s2_s)   
        then show ?thesis using seq_steps_R[OF w] by simp
      qed
      from c1 c2 c3 c4 c5 have "(t, u) \<in> ?conv"
        by (simp add: relcomp.relcompI)
      then show ?thesis by blast
    qed
  qed
  then show ?thesis
    by (meson commute_between_imp_commute mstep_rsteps_subset rstep_mstep_subset) 
qed

corollary CPS'_SN_rel_imp_comm:
  assumes SN_rel:"SN_rel (rstep (CPS' ren R S) \<union> rstep (CPS' ren S R)) (rstep (R \<union> S))"
  and lc:"locally_commute (rstep R) (rstep S)"
  and R_wf:"left_lin_wf_trs R" and S_wf:"left_lin_wf_trs S"
shows "commute (rstep R) (rstep S)"
proof-
  have "rstep (CPS_R ren R S) \<union> rstep (CPS_S ren R S) \<subseteq> rstep (CPS' ren R S) \<union> rstep (CPS' ren S R)"
    by (simp add: CPS_R_subset_CPS' CPS_S_subset_CPS' le_supI1 le_supI2 rstep_mono)
  with SN_rel have "SN_rel (rstep (CPS_R ren R S) \<union> rstep (CPS_S ren R S)) (rstep (R \<union> S))"
    by (meson SN_rel_on_mono subset_refl)
  with assms show ?thesis using CPS''_SN_rel_imp_comm by blast
qed

corollary CPS_SN_rel_imp_comm:
  assumes SN_rel:"SN_rel (rstep (CPS ren R S) \<union> rstep (CPS ren S R)) (rstep (R \<union> S))"
  and lc:"locally_commute (rstep R) (rstep S)"
  and R_wf:"left_lin_wf_trs R" and S_wf:"left_lin_wf_trs S"
shows "commute (rstep R) (rstep S)"
proof-
  have "rstep (CPS' ren R S) \<union> rstep (CPS' ren S R) \<subseteq> rstep (CPS ren R S) \<union> rstep (CPS ren S R)"
    by (meson CPS'_subset_CPS rstep_mono sup.mono)
  with SN_rel have "SN_rel (rstep (CPS' ren R S) \<union> rstep (CPS' ren S R)) (rstep (R \<union> S))"
    by (meson SN_rel_on_mono subset_refl)
  with assms show ?thesis using CPS'_SN_rel_imp_comm by blast
qed

end
