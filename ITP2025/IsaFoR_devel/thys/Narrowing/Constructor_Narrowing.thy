section \<open>Constructor-based narrowing and conditional Narrowing for constructing conditional narrowing trees\<close>

theory Constructor_Narrowing
imports
  Narrowing
  CTRS.AL94
  CTRS.Conditional_Rewriting
begin

(* First, consider the unconditional constructor-based narrowing *)

locale constructor_based_unconditional_narrowing =
  fixes R :: "('f, 'v:: infinite) trs"
  assumes wf: "wf_trs R"
begin

definition constr_term::"('f, 'v:: infinite)term \<Rightarrow> bool"
  where "constr_term t \<longleftrightarrow> (funas_term t \<subseteq> funas_trs R - {f. defined R f})"

definition constr_subst:: "('f, 'v:: infinite)subst \<Rightarrow> bool"
  where "constr_subst \<sigma> \<longleftrightarrow> (\<forall>x. constr_term (\<sigma> x))"

inductive_set constr_reduction_step::"(('f, 'v:: infinite) term) rel" 
 where 
  "(t = replace_at s p ((snd rl) \<cdot> \<sigma>) \<and> rl \<in> R \<and> p \<in> fun_poss s \<and> (s |_ p = (fst rl) \<cdot> \<sigma>) \<and> constr_subst \<sigma>) \<Longrightarrow> (s, t) \<in> constr_reduction_step"

lemmas constr_reduction_stepI = constr_reduction_step.intros [intro]
lemmas constr_reduction_stepE = constr_reduction_step.cases [elim]

inductive_set constr_narrowing_step::"(('f, 'v:: infinite) term \<times> ('f, 'v) term \<times> ('f, 'v) subst) set" 
  where 
    "(t = (replace_at s p (snd rl)) \<cdot> \<delta> \<and> \<omega> \<bullet> rl \<in> R \<and> (vars_term s \<inter> vars_rule rl = {}) \<and> 
        p \<in> fun_poss s \<and> mgu (s |_ p) (fst rl) = Some \<delta>) \<Longrightarrow> (s, t, \<delta>) \<in> constr_narrowing_step"

lemmas constr_narrowing_stepI = constr_narrowing_step.intros [intro]
lemmas constr_narrowing_stepE = constr_narrowing_step.cases [elim]

definition constr_narrowing_rel::"(('f, 'v:: infinite) term) rel" where 
  "constr_narrowing_rel = {(s, t) | s t \<sigma>. (s, t, \<sigma>) \<in> constr_narrowing_step}"

definition constr_narrowing_subst_rtran :: "('f, 'v:: infinite) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "constr_narrowing_subst_rtran s s' \<sigma> \<longleftrightarrow> (\<exists>n. (s,  s') \<in> (constr_narrowing_rel)^^n \<and> (\<exists>f \<tau>. f 0 = s \<and> f n = s' \<and> 
    (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> constr_narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

definition constr_narrowing_subst_rtran_num :: "('f, 'v:: infinite) term  \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) subst \<Rightarrow> nat \<Rightarrow> bool" where
  "constr_narrowing_subst_rtran_num s s' \<sigma> n \<longleftrightarrow> ((s,  s') \<in> (constr_narrowing_rel)^^n \<and> (\<exists>f \<tau>. f 0 = s \<and> f n = s' \<and> 
    (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> constr_narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

lemma n0_constr_narrowing_subst_rtran_num:"constr_narrowing_subst_rtran_num s s' \<sigma> 0 \<Longrightarrow> s = s' \<and> \<sigma> = Var" 
  unfolding constr_narrowing_subst_rtran_num_def by auto

lemma narrowing_rtran_impl: assumes "constr_narrowing_subst_rtran_num s s' \<sigma> n"
  shows "constr_narrowing_subst_rtran s s' \<sigma>" 
  unfolding constr_narrowing_subst_rtran_num_def constr_narrowing_subst_rtran_def 
  using assms constr_narrowing_subst_rtran_num_def by metis

lemma constr_subst_apply:
  assumes csubst:"constr_subst \<alpha>"
    and cterm:"constr_term t"
  shows "constr_term (t \<cdot> \<alpha>)" using assms unfolding constr_subst_def constr_term_def
proof(induct t)
  case (Var v)
  then show ?case unfolding constr_term_def csubst constr_subst_def by auto
next
  case (Fun f ss)
  then show ?case
  proof -{ 
    fix s
    assume asm:"s \<in> set ss" 
    with Fun(3) have "constr_term s" unfolding constr_term_def by auto
    hence cs:"constr_term (s \<cdot> \<alpha>)" using Fun asm csubst
      by (simp add: constr_term_def)
    hence "constr_term (Fun f ss \<cdot> \<alpha>)" unfolding constr_term_def
      by (smt (verit, ccfv_threshold) Fun.prems(1) Fun.prems(2) 
          UN_E UN_simps(10) Un_iff funas_term_subst subset_eq)
  } then show ?thesis using Fun.prems(2) constr_term_def by auto
  qed
qed

lemma constr_subst_compose:
  assumes \<alpha>:"constr_subst \<alpha>"
    and \<beta>:"constr_subst \<beta>"
  shows "constr_subst (\<alpha> \<circ>\<^sub>s \<beta>)" using assms unfolding constr_subst_def
proof (safe, goal_cases)
  case (1 u)
  then show ?case
  proof -
    have *:"constr_term (\<alpha> u)" using \<alpha> 1 by force
    have **:"constr_term (\<beta> u)" using \<beta> 1 by force
    from constr_subst_apply[OF \<beta> *]
    have "constr_term ((\<alpha> u) \<cdot> \<beta>)" by simp
    then show "constr_term ((\<alpha> \<circ>\<^sub>s \<beta>) u)" by (simp add: subst_compose)
  qed
qed

lemma constr_subst_union:
  assumes \<alpha>:"constr_subst \<alpha>"
    and \<beta>:"constr_subst \<beta>"
  shows "constr_subst (\<alpha> \<union>\<^sub>s \<beta>)" using assms unfolding constr_subst_def
proof (safe, goal_cases)
  case (1 u)
  then show ?case
  proof -
    have *:"constr_term (\<alpha> u)" using \<alpha> 1 by force
    have **:"constr_term (\<beta> u)" using \<beta> 1 by force
    from constr_subst_apply[OF \<beta> *]
    have "constr_term ((\<alpha> u) \<cdot> \<beta>)" by simp
    then show "constr_term ((\<alpha> \<union>\<^sub>s \<beta>) u)" using  * ** by force
  qed
qed

lemma def_imp_not_constructor: assumes def:"defined R (f, n)"
  and root:"root t = Some (f, n)"
shows "\<not> constr_term t"
proof (rule notI)
  assume asm:"constr_term t"
  hence *:"funas_term t \<subseteq> funas_trs R - {fn. defined R fn}" unfolding constr_term_def by auto
  from root have **:"(f, n) \<in> {fn. defined R fn}" by (simp add: def)
  have "(f, n) \<in> funas_term t" using root 
    by (metis UnI1 funas_term.simps(2) insertCI option.distinct(1) option.inject root.elims)
  then show False using * ** by blast
qed

lemma not_constructor_term_lhs: assumes rl:"rl \<in> R"
  shows "\<not> constr_term (fst rl)"   
proof(rule notI)
  assume asm:"constr_term (fst rl)"
  have "\<exists>f n. root (fst rl) = Some (f, n)" using rl 
    by (metis local.wf prod.collapse root.simps(2) wf_trs_imp_lhs_Fun)
  then obtain f n where root_rl:"root (fst rl) = Some (f, n)" by auto
  hence def:"defined R (f, n)"
    by (metis defined_def prod.collapse rl)
  then show False using asm root_rl def def_imp_not_constructor
    by (simp add: constr_term_def defined_def) 
qed

lemma vars_cont_seq[simp]: assumes S:"S = (u, v)"
  shows "vars_term u \<subseteq> vars_rule S \<and> vars_term v \<subseteq> vars_rule S"
proof(intro conjI, goal_cases)
  case 1
  have *:"vars_term u \<subseteq> vars_rule (u, v)" 
    by (simp add: vars_defs(2))
  then show ?case using vars_rule_def S by auto
next
  case 2
  have **:"vars_term v \<subseteq> vars_rule (u, v)" 
    by (simp add: vars_defs(2))
  then show ?case using vars_rule_def S by auto
qed

lemma narrowing_set_imp_rtran:assumes "(s, t, \<sigma>) \<in>  constr_narrowing_step"
  shows "constr_narrowing_subst_rtran_num s t \<sigma> 1"
proof -
  have *:"(s, t) \<in> constr_narrowing_rel" using assms 
    using constr_narrowing_rel_def by auto
  then obtain f where f0:"f 0 = s" and f1:"f 1 = t" and rel_chain:"(f 0,  f (Suc 0)) \<in> constr_narrowing_rel" 
    by (metis One_nat_def relpow_0_I relpow_Suc_I relpow_fun_conv)
  let ?\<tau> = "\<lambda>i. (if i = 0 then \<sigma> else Var)"
  show ?thesis  unfolding constr_narrowing_subst_rtran_num_def
  proof(intro conjI, goal_cases)
    case 1
    then show ?case by (simp add: *)
  next
    case 2
    then show ?case by (rule exI[of _ f], rule exI[of _ ?\<tau>], insert assms f0 f1, auto)
  qed
qed

lemma vars_disj:"finite V \<Longrightarrow> (\<exists>\<omega>. V \<inter> vars_rule (\<omega> \<bullet> rl) = {})" 
proof -
  assume asm:"finite V"
  show "(\<exists>\<omega>. V \<inter> vars_rule (\<omega> \<bullet> rl) = {})"
  proof -
    from rule_fs.rename_avoiding[OF asm]
    obtain \<omega> rl'  where rl':"rl' = \<omega> \<bullet> rl" and disj:"V \<inter> rule_pt.supp rl' = {}" by metis
    from supp_vars_rule_eq
    have "rule_pt.supp rl' = vars_rule rl'" unfolding vars_rule_def by blast
    then show ?thesis by (intro exI[of _ \<omega>], insert disj rl', blast) 
  qed
qed

lemma unconditional_constructor_based_lifting_lemma:
  fixes V::"('v::infinite) set" and s::"('f, 'v)term" and t::"('f, 'v)term"
  assumes "t = s \<cdot> \<theta>"
    and "constr_subst \<theta>"
    and "vars_term s \<union> subst_domain \<theta> \<subseteq> V"
    and cr:"(t,  t') \<in> (constr_reduction_step)\<^sup>*"
    and "finite V"
  shows "\<exists>\<sigma> \<theta>' s'. constr_narrowing_subst_rtran s s' \<sigma> \<and> t' =  s' \<cdot> \<theta>' \<and> constr_subst \<theta>' \<and> 
  (\<forall>x. restrict_subst_domain V (\<sigma> \<circ>\<^sub>s \<theta>') x = restrict_subst_domain V \<theta> x)"
proof -
  from cr
  obtain f n where f0T:"f 0 = t" and fn:"f n = t'" and rel_chain:"\<forall>i < n. (f i,  f (Suc i)) \<in> constr_reduction_step" 
    by (metis rtrancl_imp_seq)
  then have "\<exists>\<sigma> \<theta>' s'. constr_narrowing_subst_rtran_num s s' \<sigma> n \<and> t' = s' \<cdot> \<theta>'  \<and> constr_subst \<theta>' \<and> 
  (\<forall>x. restrict_subst_domain V (\<sigma> \<circ>\<^sub>s \<theta>') x = restrict_subst_domain V \<theta> x)" using assms
  proof(induct n arbitrary: s t t' \<theta> f V rule: wf_induct[OF wf_measure [of "\<lambda> n. n"]])
    case (1 n)
    note IH1 = 1(1)[rule_format]
    then show ?case
    proof(cases "n = 0")
      case True
      show ?thesis
        by (rule exI[of _ Var], rule exI[of _ \<theta>], rule exI[of _ "s"], insert 1 True)
          (simp add: constr_narrowing_subst_rtran_num_def subst_rule_def relpow_fun_conv, force) 
    next
      case False
      hence f0f1:"(f 0, f 1) \<in> constr_reduction_step" using 1 by auto
      then show ?thesis
      proof -
        from f0f1 obtain t  \<sigma>' rl p  where f0:"f 0 = t" and f1:"f 1 = replace_at t p ((snd rl) \<cdot> \<sigma>')"
          and red_pos:"p \<in> fun_poss t" and rl:"rl \<in> R"
          and s1p:"t |_ p = (fst rl) \<cdot> \<sigma>'" and  con\<sigma>':"constr_subst \<sigma>'"
          using constr_reduction_step.simps by blast
        have con\<theta>:"constr_subst \<theta>" by fact
        hence us1:"s \<cdot> \<theta> = t" using 1(2) 1(5) f0 by auto
        have "\<exists>\<omega>'. V \<inter> vars_rule (\<omega>' \<bullet> rl) = {}" using vars_disj 
          using 1(9) by blast
        then obtain \<omega>' where varempty':"V \<inter> vars_rule (\<omega>' \<bullet> rl) = {}" by auto
        hence "\<exists>\<omega>r. \<omega>r \<bullet> \<omega>'\<bullet> rl \<in> R" using rl  
          by (metis rule_pt.permute_minus_cancel(2))
        then obtain \<omega>r where \<omega>r:"\<omega>r \<bullet> (\<omega>'\<bullet> rl) \<in> R" by auto
        from red_pos have pfs1:"p \<in> fun_poss t" using red_pos by blast
        have ps1:"p \<in> poss t" using fun_poss_imp_poss pfs1 by blast
        from not_constructor_term_lhs[OF \<omega>r]
        have "\<not> constr_term (\<omega>r \<bullet> (\<omega>'\<bullet> (fst rl)))" using \<omega>r unfolding constr_term_def
          by (simp add: rule_pt.fst_eqvt)
        hence "\<not> constr_term (\<omega>'\<bullet> (fst rl))" using constr_term_def by auto
        hence "\<not> constr_term (fst rl)" using constr_term_def by auto
        hence nc:"\<not> constr_term ((fst rl) \<cdot> \<sigma>')" 
          by (simp add: constr_term_def funas_term_subst)
        have p:"p \<in> poss s" 
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence pnu:"p \<notin> poss s" by simp
          hence pnfu:"p \<notin> fun_poss s" using fun_poss_imp_poss by blast
          have sub_eq:"(s \<cdot> \<theta>) |_ p = (fst rl) \<cdot> \<sigma>'" using us1 s1p by auto
          have "p \<in> fun_poss (s \<cdot> \<theta>)" using pfs1 us1 by auto
          from poss_subst_apply_term[of p s \<theta>]
          obtain q r x where qpr:"p = q @ r" and qu:"q \<in> poss s" and uqx:"s |_ q = Var x" and r:"r \<in> poss (\<theta> x)"
          using pnfu ps1 us1 by blast
          hence *:"(s \<cdot> \<theta>) |_ p = (Var x) \<cdot> \<theta> |_ r" by force
          have "constr_term ((Var x) \<cdot> \<theta>)" using con\<theta>
          by (simp add: constr_subst_def constr_term_def)
          hence "constr_term ((Var x) \<cdot> \<theta> |_ r)" 
          proof(auto simp add: constr_subst_def constr_term_def, insert r, goal_cases)
            case (1 f n)
            then show ?case 
              by (metis "*"constr_term_def ctxt_supt_id 
                eval_term.simps(1) funas_term_ctxt_apply le_sup_iff nc s1p us1)
          next
            case (2 f n)
            then show ?case 
              by (metis DiffD2 Int_Diff Un_iff ctxt_supt_id funas_term_ctxt_apply 
                  inf.orderE mem_Collect_eq)
          qed
          then show False using nc * using s1p us1 by auto
        qed
        hence funp:"p \<in> fun_poss s" using ps1 pfs1 us1 
          by (metis DiffI constr_subst_def con\<theta> eval_term.simps(1) nc poss_simps(4) s1p subt_at_subst var_poss_iff)
        hence vuS':"vars_term (s |_ p) \<subseteq> vars_term s"
        proof -
          from vars_term_subt_at[OF p]
          have "vars_term (s |_ p) \<subseteq> vars_term s" by auto
          then show ?thesis by auto
        qed
        with varempty' have varcond:"vars_term (s |_ p) \<inter> vars_rule (\<omega>' \<bullet> rl) = {}" using 1(7) by blast
        have "\<exists>\<sigma>r. \<forall>x. \<sigma>r (\<omega>' \<bullet> x) = \<sigma>' x" using atom_pt.permute_minus_cancel(2) by (metis o_apply)
        then obtain \<sigma>r where \<sigma>rdef:"\<forall>t. \<sigma>r (\<omega>' \<bullet> t) = \<sigma>' t" by auto
        hence "\<forall>xs. subst_list \<sigma>r (\<omega>' \<bullet> xs) = subst_list \<sigma>' xs" unfolding subst_list_def
        proof(auto, goal_cases)
          case (1 xs s t)
          hence "(\<omega>' \<bullet> s) \<cdot> \<sigma>r = s \<cdot> \<sigma>'" 
            by (metis permute_term.simps(1) permute_term_subst_apply_term 
              subst_compose_def subst_monoid_mult.mult.left_neutral term_subst_eq_conv) 
          then show ?case 
            by (metis fst_conv rule_pt.fst_eqvt)
        next
          case (2 xs s t)
          hence "(\<omega>' \<bullet> t) \<cdot> \<sigma>r = t \<cdot> \<sigma>'" 
            by (metis permute_term.simps(1) permute_term_subst_apply_term 
              subst_compose_def subst_monoid_mult.mult.left_neutral term_subst_eq_conv) 
          then show ?case 
            by (metis snd_conv rule_pt.snd_eqvt)
        qed
        hence \<sigma>r1:"subst_list \<sigma>r [\<omega>' \<bullet> rl]  = subst_list \<sigma>' [rl]" unfolding subst_list_def  
          using rule_pt.fst_eqvt rule_pt.snd_eqvt 
          by (smt (verit) list.simps(8) list.simps(9) rules_pt.permute_list_def)
        hence subeq:"subst_rule \<sigma>r (\<omega>' \<bullet> rl)  = subst_rule \<sigma>' rl" unfolding subst_rule_def subst_list_def by simp
        let ?\<sigma>dom = "vars_rule (\<omega>' \<bullet> rl)"
        let ?\<sigma>r = "\<lambda>x. restrict_subst_domain (?\<sigma>dom) \<sigma>r x"
        let ?\<theta> = "\<lambda>x. restrict_subst_domain V \<theta> x"
        have sub_\<sigma>r:"subst_domain ?\<sigma>r \<subseteq> (vars_rule (\<omega>' \<bullet> rl))" 
          by (metis Int_lower1 subst_domain_restrict_subst_domain)
        have sub_\<theta>:"subst_domain ?\<theta> \<subseteq> V" by (metis inf_le1 subst_domain_restrict_subst_domain)
        have inter_empty:"subst_domain ?\<sigma>r \<inter> subst_domain ?\<theta> = {}" using varempty'
          using 1(7) using sub_\<sigma>r by auto
        from  us1 s1p have *:"(s \<cdot> \<theta> |_ p) = fst (\<omega>' \<bullet> rl) \<cdot> \<sigma>r" 
          by (metis subeq fst_conv subst_rule_def)
        have varcond':"vars_term (s |_ p) \<inter> vars_term (fst (\<omega>' \<bullet> rl)) = {}" 
        proof -
          have "vars_term (fst (\<omega>' \<bullet> rl)) \<subseteq> vars_rule (\<omega>' \<bullet> rl)"
            by (metis vars_cont_seq prod.exhaust_sel)
          then show ?thesis using varcond by auto
        qed
        with con\<theta> * have **:"(s |_ p) \<cdot> \<theta> = fst (\<omega>' \<bullet> rl) \<cdot> \<sigma>r" by (simp add: p)
        have sub_eq:"(s |_ p) \<cdot> ?\<theta> = fst (\<omega>' \<bullet> rl) \<cdot> ?\<sigma>r" using **
          using 1(7) dual_order.trans fst_conv surj_pair vars_cont_seq 
          by (metis (no_types, opaque_lifting) Un_subset_iff 
              subst_apply_term_restrict_subst_domain vuS')
        from subst_union_sound[OF sub_eq]
        have subst_eq_\<theta>\<sigma>:"(s |_ p) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)  = (fst (\<omega>' \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)"
          using inter_empty sub_\<sigma>r sub_\<theta> inter_empty 
          by (smt (z3) 1(7) Un_upper1 disjoint_iff sub_comm sub_eq subset_eq subst_union.simps 
              term_subst_eq_conv varcond varempty' vars_rule_def)
        then obtain \<delta> where mgu_uv:"mgu (s |_ p) (fst (\<omega>' \<bullet> rl)) = Some \<delta>" using mgu_ex 
          by (meson ex_mgu_if_subst_apply_term_eq_subst_apply_term)
        from mgu_sound[OF mgu_uv] have \<delta>:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) =  \<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using subst_eq_\<theta>\<sigma> 
        by (smt (verit, ccfv_SIG) is_imgu_def subst_monoid_mult.mult_assoc the_mgu the_mgu_is_imgu)
        have crl:"(snd (\<omega>' \<bullet> rl)) \<cdot> \<sigma>r = ((snd rl) \<cdot> \<sigma>')" 
          by (smt (verit) \<sigma>r1 list.inject list.simps(9) prod.inject subst_list_def)
        from subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
        have subinter:"subst_domain ?\<sigma>r = subst_domain \<sigma>r \<inter> ?\<sigma>dom" by auto
        have sndeq:"snd (\<omega>' \<bullet> rl) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r) = (snd rl) \<cdot> \<sigma>'" 
          by (smt (verit) 1(7) UnCI crl disjoint_iff inf.absorb_iff2 inf.orderE inf_aci(2) inf_commute 
              inf_le1 inf_left_commute inter_empty restrict_subst_domain_def sub_\<theta> subst_union.simps sup.boundedE 
               term_subst_eq_conv varempty' vars_defs(2))
        let ?s1 = "(replace_at s p (snd (\<omega>' \<bullet> rl)))\<cdot> \<delta>"
        have con\<theta>':"constr_subst ?\<theta>" using con\<theta> 1(7) by force
        have "constr_subst \<sigma>r" 
          by (auto simp add: constr_subst_def , insert con\<sigma>' \<sigma>r1) 
           (metis \<sigma>rdef atom_pt.permute_minus_cancel(1) constr_subst_def)
        hence con\<sigma>r:"constr_subst ?\<sigma>r" 
          by (simp add: constr_subst_def constr_term_def restrict_subst_domain_def subst_restrict_def)
        from constr_subst_union[OF con\<theta>' con\<sigma>r]
        have con_main:"constr_subst (?\<theta> \<union>\<^sub>s ?\<sigma>r)"  
          by (simp add: vars_crule_def vars_defs(2))
        have nar:"(s, ?s1, \<delta>) \<in> constr_narrowing_step"
          unfolding subst_rule_def using 1(7) mgu_uv rl varempty' \<omega>r funp 
          by (smt (verit, ccfv_SIG) constr_narrowing_step.intros disjoint_iff 
              subset_iff sup.bounded_iff)
        from narrowing_set_imp_rtran[OF nar]
        have condn1:"constr_narrowing_subst_rtran_num s ?s1 \<delta> 1" by auto
        let ?V = "(V - subst_domain \<delta>) \<union> range_vars \<delta>"
        let ?\<theta>1 = "\<lambda>x. restrict_subst_domain ?V (?\<theta> \<union>\<^sub>s ?\<sigma>r) x"
        have "subst_domain ?\<theta>1 \<subseteq> ?V"
          by (metis inf_le1 subst_domain_restrict_subst_domain)
        have reseq:"\<forall>x. restrict_subst_domain ?V ?\<theta>1 x = restrict_subst_domain ?V (?\<theta> \<union>\<^sub>s ?\<sigma>r) x" 
          by (simp add: restrict_subst_domain_def)
        have reseq\<delta>:"\<forall>x. restrict_subst_domain V (\<delta> \<circ>\<^sub>s ?\<theta>1) x = restrict_subst_domain V (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) x" 
          using reseq restrict_subst_compose by blast
        have reseq\<theta>:"\<forall>x. restrict_subst_domain V (\<delta> \<circ>\<^sub>s ?\<theta>1) x = restrict_subst_domain V \<theta> x" using 1(7) \<delta> 
          by (metis disjoint_iff notin_subst_domain_imp_Var reseq\<delta> restrict_subst_domain_def subst_union.simps varempty')
        have con\<theta>1:"constr_subst ?\<theta>1" 
          by (smt (z3) con\<sigma>r con\<theta>' con_main constr_subst_def disjoint_iff inter_empty 
              notin_subst_domain_imp_Var restrict_subst_domain_def vars_crule_def vars_rule_def)
        have rel_chain':"\<And>i. i < n - 1 \<Longrightarrow> (f (i + 1), f (Suc i + 1)) \<in> constr_reduction_step" using rel_chain 
          by (simp add: 1(4))
        let ?f = "\<lambda>i. f (i + 1)"
        have relstar:"(f 1, f n) \<in> (constr_reduction_step)\<^sup>*" using False 1(4) less_Suc_eq 
          by (induct n, blast, metis (no_types, lifting) One_nat_def rtrancl.simps)
        have vars1:"vars_term ?s1 \<subseteq> ?V"
        proof -
          have *:"vars_term (snd (\<omega>' \<bullet> rl)) \<subseteq> vars_term (fst (\<omega>' \<bullet> rl))" using wf 
            by (metis rl rule_pt.fst_eqvt sup.orderI vars_rule_def vars_rule_eqvt vars_rule_lhs vars_term_eqvt)            
          from var_cond_stable[OF this]
          have "vars_term (snd (\<omega>' \<bullet> rl) \<cdot> \<delta> ) \<subseteq> vars_term (fst (\<omega>' \<bullet> rl) \<cdot> \<delta>)" by fastforce
          from replace_var_stable[OF this]
          have "vars_term ?s1 \<subseteq> vars_term ((replace_at s p (fst (\<omega>' \<bullet> rl)))\<cdot> \<delta>)" 
            by (meson * replace_var_stable var_cond_stable)
          moreover have "vars_term ((replace_at s p (fst (\<omega>' \<bullet> rl)))\<cdot> \<delta>) = vars_term (s \<cdot> \<delta>)"
            by (metis ctxt_supt_id mgu_uv p subst_apply_term_ctxt_apply_distrib subst_apply_term_eq_subst_apply_term_if_mgu)
          moreover have "vars_term (s \<cdot> \<delta>) \<subseteq> ?V" 
            by (smt (verit) 1(7) Diff_partition Un_Diff Un_iff subset_iff vars_term_subst_apply_term_subset)
          ultimately show ?thesis by auto
        qed
        have "\<exists> \<delta>' \<theta>' s'. constr_narrowing_subst_rtran_num ?s1 s' \<delta>' (n - 1) \<and> f n = s' \<cdot> \<theta>' \<and> constr_subst \<theta>' \<and>
          (\<forall>x. restrict_subst_domain ?V (\<delta>' \<circ>\<^sub>s \<theta>') x = restrict_subst_domain ?V ?\<theta>1 x)"
        proof (rule IH1[of "n - 1"  ?f "f 1" "f n"], goal_cases)
          case 1
          then show ?case using False by auto
        next
          case 2
          then show ?case by auto
        next
          case 3
          then show ?case using False by auto
        next
          case (4 i)
          then show ?case using rel_chain' by blast
        next
          case 5
          have inempty:"subst_domain ?\<sigma>r \<inter> V = {}" using varempty' subinter by auto
          hence "\<forall>x. restrict_subst_domain V (?\<theta> \<union>\<^sub>s ?\<sigma>r) x = restrict_subst_domain V \<theta> x"
            using \<delta> reseq\<delta> reseq\<theta> by auto
          have "\<forall>x. restrict_subst_domain (vars_term (snd (\<omega>' \<bullet> rl))) (?\<theta> \<union>\<^sub>s ?\<sigma>r) x = restrict_subst_domain (vars_term (snd (\<omega>' \<bullet> rl))) ?\<sigma>r  x" 
          proof -
            { fix v :: 'v
              have "vars_rule (\<omega>' \<bullet> rl) - V = vars_rule (\<omega>' \<bullet> rl)"
                using varempty' by fastforce
              then have "V \<inter> vars_term (snd (\<omega>' \<bullet> rl)) = {}"
                by (smt (z3) Diff_disjoint Int_Diff Un_Int_eq(4) vars_rule_def)
              then have "restrict_subst_domain (vars_term (snd (\<omega>' \<bullet> rl))) (?\<theta> \<union>\<^sub>s ?\<sigma>r) v = restrict_subst_domain (vars_term (snd (\<omega>' \<bullet> rl))) ?\<sigma>r v"
                by (simp add: Int_def restrict_subst_domain_def subst_domain_def subst_restrict_def) 
            } then show ?thesis by fastforce
          qed
          have "f 1 = ?s1 \<cdot> ?\<theta>1"
          proof -
            have "f 1 = replace_at (s \<cdot> \<theta>) p (snd (\<omega>' \<bullet> rl) \<cdot> \<sigma>r)" using crl f1 us1 by auto
            also have "...  = replace_at (s \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)) p (snd (\<omega>' \<bullet> rl) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r))" 
              by (smt (verit) 1(7)  inempty crl inf.absorb_iff1 inf_commute inf_left_commute inter_empty 
                  le_supE sndeq sub_comm subst_apply_term_restrict_subst_domain subst_union_term_reduction varcond' vuS')
            also have "... = replace_at s p (snd (\<omega>' \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" by (simp add: ctxt_of_pos_term_subst p)
            also have "... = replace_at s p (snd (\<omega>' \<bullet> rl)) \<cdot> (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r))" using \<delta> by auto
            also have "... = ?s1 \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" by simp
            also have *:"f 1 = ?s1 \<cdot> ?\<theta>1" using vars1 using calculation subst_apply_term_restrict_subst_domain by fastforce
            finally show ?thesis using * by fastforce
          qed
          then show ?case by auto
        next
          case 6
          then show ?case using con\<theta>1 by blast
        next
          case 7
          have "subst_domain ?\<theta>1 \<subseteq> ?V" by (metis inf_le1 subst_domain_restrict_subst_domain)
          then show ?case using vars1 by auto
        next
          case 8
          then show ?case using relstar by auto
        next
          case 9
          have *:"finite (subst_domain \<delta>)" 
            using mgu_finite_subst_domain mgu_uv by blast
          have "finite (range_vars \<delta>)" using mgu_finite_range_vars mgu_uv by blast
          then show ?case using vars_disj rl using * 1(9) by blast
        qed
        then obtain \<delta>' \<theta>' s' where condn2:"constr_narrowing_subst_rtran_num ?s1 s' \<delta>' (n - 1)" and sub:"f n = s' \<cdot> \<theta>'" and con\<theta>':"constr_subst \<theta>'" and 
          rest_IH:"(\<forall>x. restrict_subst_domain ?V (\<delta>' \<circ>\<^sub>s \<theta>') x = restrict_subst_domain ?V ?\<theta>1 x)" by auto
        from n0_constr_narrowing_subst_rtran_num have n1:"n = 1 \<Longrightarrow> s' = ?s1 \<and> \<delta>' = Var" 
          using False using condn2 by (metis diff_self_eq_0)
        from condn2 obtain g \<tau> where "(?s1,  s') \<in> (constr_narrowing_rel)^^(n - 1)" and g0:"g 0 = ?s1" and gnm1:"g (n - 1) = s'"
          and gcond_chain:"\<forall>i < n - 1. ((g i), (g (Suc i)), (\<tau> i)) \<in> constr_narrowing_step" and comp\<delta>':"if n = 1 then \<delta>' = Var else \<delta>' = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (n - 1)])"
          using False n1 unfolding constr_narrowing_subst_rtran_num_def by auto
        let ?g = "\<lambda>i. if i = 0 then s else g (i - 1)"
        let ?\<tau> = "\<lambda>i. if i = 0 then \<delta> else \<tau> (i - 1)"
        have "\<delta>' = compose (map ?\<tau> [1..< n])" 
          by (smt (verit) One_nat_def comp\<delta>' add_diff_cancel_left' add_diff_inverse_nat 
              compose_simps(1) diff_zero length_upt less_Suc_eq_0_disj list.simps(8) 
              map_equality_iff nth_upt plus_1_eq_Suc upt_eq_Nil_conv) 
        hence \<delta>\<delta>'comp:"\<delta> \<circ>\<^sub>s \<delta>' = compose (map ?\<tau> [0..< n])" using False upt_conv_Cons by fastforce
        have condn:"constr_narrowing_subst_rtran_num s s' (\<delta> \<circ>\<^sub>s \<delta>') n" 
        proof -
          have "(s, s') \<in> constr_narrowing_rel ^^ n" using condn1 condn2 n1 False 
            by (metis (no_types, lifting) One_nat_def Suc_pred bot_nat_0.not_eq_extremum 
                constr_narrowing_subst_rtran_num_def relpow_1 relpow_Suc_I2)
          moreover have "(\<exists>f. f 0 = s \<and> f n = s' \<and> (\<exists>\<tau>. (\<forall>i<n. (f i, f (Suc i), \<tau> i) \<in> constr_narrowing_step) \<and>
              \<delta> \<circ>\<^sub>s \<delta>' = compose (map \<tau> [0..<n])))" 
            by (rule exI[of _ ?g], insert \<delta>\<delta>'comp False One_nat_def gnm1) (smt (verit, ccfv_SIG) Suc_pred gcond_chain 
                bot_nat_0.not_eq_extremum diff_Suc_1 g0 less_nat_zero_code nar not_less_eq)
          ultimately show ?thesis 
            by (simp add: constr_narrowing_subst_rtran_num_def False local.wf)
        qed
        have "s' \<cdot> \<theta>' = t'" using 1 sub by auto
        have "\<forall>x. restrict_subst_domain ?V (?\<theta> \<union>\<^sub>s ?\<sigma>r) x = restrict_subst_domain ?V ?\<theta>1 x" using reseq by auto
        hence "\<forall>x. restrict_subst_domain V (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) x = restrict_subst_domain V (\<delta> \<circ>\<^sub>s ?\<theta>1) x" 
          using reseq\<delta> by metis
        have res_main:"(\<forall>x. restrict_subst_domain V ((\<delta> \<circ>\<^sub>s \<delta>') \<circ>\<^sub>s \<theta>') x = restrict_subst_domain V \<theta> x)"
        proof(intro impI allI)
          fix x
          show "restrict_subst_domain V ((\<delta> \<circ>\<^sub>s \<delta>') \<circ>\<^sub>s \<theta>') x = restrict_subst_domain V \<theta> x"
          proof -
            have *:"(V - subst_domain \<delta>) \<union> range_vars \<delta> \<subseteq> ?V" by (simp add: 1(7))
            have **:"restrict_subst_domain ?V (\<delta>' \<circ>\<^sub>s \<theta>') x = restrict_subst_domain ?V ?\<theta>1 x" using rest_IH by auto
            from restrict_subst_compose [OF *, of "\<delta>' \<circ>\<^sub>s \<theta>'" ?\<theta>1]
            have ***:"restrict_subst_domain V (\<delta> \<circ>\<^sub>s (\<delta>' \<circ>\<^sub>s \<theta>')) x =  restrict_subst_domain V (\<delta> \<circ>\<^sub>s ?\<theta>1) x" 
              using rest_IH by blast
            have "... = restrict_subst_domain V \<theta> x" using reseq\<delta> reseq\<theta> by auto
            then show ?thesis using "***" by (metis subst_monoid_mult.mult_assoc)
          qed   
        qed  
        show ?thesis 
          by (rule exI[of _ "\<delta> \<circ>\<^sub>s \<delta>'"], rule exI[of _ \<theta>'], rule exI[of _ s'], insert sub con\<theta>' 1 res_main condn, blast)
      qed
    qed
  qed
  then show ?thesis using narrowing_rtran_impl by blast
qed

end
(* Next, consider the conditional constructor-based narrowing *)

locale conditional_narrowing =
  fixes R :: "('f, 'v:: infinite) ctrs"
  assumes wf: "sdtrs R" (* strongly deterministic oriented 3-ctrs *)
begin

definition constructor_term::"('f, 'v:: infinite)term \<Rightarrow> bool"
  where "constructor_term t \<longleftrightarrow> (funas_term t \<subseteq> funas_ctrs R - {f. defined (Ru R) f})"

definition constructor_subst:: "('f, 'v:: infinite)subst \<Rightarrow> bool"
  where "constructor_subst \<sigma> \<longleftrightarrow> (\<forall>x. constructor_term (\<sigma> x))"

definition wf_constructor_subst:: "('f, 'v:: infinite)subst \<Rightarrow> bool"
  where "wf_constructor_subst \<sigma> \<longleftrightarrow> (\<forall>x. constructor_term (\<sigma> x) \<and> (subst_domain \<sigma> \<inter> range_vars \<sigma> = {}))"

definition vars_seq::"('f, 'v) rule list \<Rightarrow> 'v set" where
  "vars_seq S = \<Union> (set (map (vars_rule) S))"

(* \<leadsto>*)
(* Assuming all right_hand sides are constructor terms, possibly using variable abstraction *)
inductive_set cond_reduction_step::"(('f, 'v) rule list) rel" 
  where 
  "(S = (s\<^sub>1, t\<^sub>1) # xs \<and> 
    T = subst_list \<sigma> (snd rl) @ (replace_at s\<^sub>1 p ((crhs rl) \<cdot> \<sigma>), t\<^sub>1) # xs \<and> 
    rl \<in> R \<and> p \<in> fun_poss s\<^sub>1 \<and> 
    (s\<^sub>1 |_ p = (clhs rl) \<cdot> \<sigma>) \<and> constructor_subst \<sigma>) \<Longrightarrow> (S, T) \<in> cond_reduction_step"

lemmas cond_reduction_stepI = cond_reduction_step.intros [intro]
lemmas cond_reduction_stepE = cond_reduction_step.cases [elim]

inductive_set cond_matching_step::"(('f, 'v) rule list) rel"
  where
  "(S = (s\<^sub>1, t\<^sub>1) # xs \<and> T = subst_list \<sigma> xs \<and> constructor_term s\<^sub>1 \<and> s\<^sub>1 = t\<^sub>1 \<cdot> \<sigma> \<and> wf_constructor_subst \<sigma>)
      \<Longrightarrow> (S, T) \<in> cond_matching_step"

lemmas cond_matching_stepI = cond_matching_step.intros [intro]
lemmas cond_matching_stepE = cond_matching_step.cases [elim]

definition cond_reduction_set::"(('f, 'v) rule list) rel" 
  where 
  "cond_reduction_set = {(S, T) | S T. (S, T) \<in> cond_reduction_step \<or> (S, T) \<in> cond_matching_step}"

inductive_set cond_narrowing_step::"(('f, 'v) rule list \<times> ('f, 'v) rule list \<times> ('f, 'v) subst) set"  
  where
  "(S = (s\<^sub>1, t\<^sub>1) # xs \<and>
    T = subst_list \<delta> ((snd rl) @ (replace_at s\<^sub>1 p (crhs rl), t\<^sub>1) # xs) \<and>
     \<omega> \<bullet> rl \<in> R \<and> (vars_seq S \<inter> vars_crule rl = {}) \<and> p \<in> fun_poss s\<^sub>1 \<and> mgu (s\<^sub>1 |_ p) (clhs rl) = Some \<delta>)
    \<Longrightarrow> (S, T, \<delta>) \<in> cond_narrowing_step"

lemmas cond_narrowing_stepI = cond_narrowing_step.intros [intro]
lemmas cond_narrowing_stepE = cond_narrowing_step.cases [elim]

inductive_set cond_unification_step::"(('f, 'v) rule list \<times> ('f, 'v) rule list \<times> ('f, 'v) subst) set"  
  where
  "S = (s\<^sub>1, t\<^sub>1) # xs \<and> T = subst_list \<sigma> xs \<and> constructor_term s\<^sub>1 \<and> mgu s\<^sub>1 t\<^sub>1 = Some \<sigma>
    \<Longrightarrow> (S, T, \<sigma>) \<in> cond_unification_step"

lemmas cond_unification_stepI = cond_unification_step.intros [intro]
lemmas cond_unification_stepE = cond_unification_step.cases [elim]

definition cond_narrowing_step_set::"(('f, 'v) rule list \<times> ('f, 'v) rule list \<times> ('f, 'v) subst) set" where 
  "cond_narrowing_step_set = {(S, T, \<delta>) |S T \<delta>. (S, T, \<delta>) \<in> cond_narrowing_step}"

definition cond_narrowing_set::"(('f, 'v) rule list \<times> ('f, 'v) rule list \<times> ('f, 'v) subst) set" where 
  "cond_narrowing_set = {(S, T, \<delta>) |S T \<delta>. (S, T, \<delta>) \<in> cond_narrowing_step \<or> (S, T, \<delta>) \<in> cond_unification_step}"

definition cond_constr_narrowing_rel::"(('f, 'v) rule list) rel" where 
  "cond_constr_narrowing_rel = {(S, T) | S T \<sigma>. (S, T, \<sigma>) \<in> cond_narrowing_set}"

definition cond_constr_narrowing_subst_rtran :: "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "cond_constr_narrowing_subst_rtran S S' \<sigma> \<longleftrightarrow> (\<exists>n. (S,  S') \<in> (cond_constr_narrowing_rel)^^n \<and> (\<exists>f \<tau>. f 0 = S \<and> f n = S' \<and> 
    (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> cond_narrowing_set) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

definition cond_constr_narrowing_subst_rtran_num :: "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow> ('f, 'v) subst \<Rightarrow> nat \<Rightarrow> bool" where
  "cond_constr_narrowing_subst_rtran_num S S' \<sigma> n \<longleftrightarrow> ((S,  S') \<in> (cond_constr_narrowing_rel)^^n \<and> (\<exists>f \<tau>. f 0 = S \<and> f n = S' \<and> 
    (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> cond_narrowing_set) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

lemma n0_cond_constr_narrowing_subst_rtran_num:"cond_constr_narrowing_subst_rtran_num S S' \<sigma> 0 \<Longrightarrow> S = S' \<and> \<sigma> = Var" 
  unfolding cond_constr_narrowing_subst_rtran_num_def by auto

lemma cond_narrowing_rtran_impl: assumes "cond_constr_narrowing_subst_rtran_num S S' \<sigma> n"
  shows "cond_constr_narrowing_subst_rtran S S' \<sigma>" 
  unfolding cond_constr_narrowing_subst_rtran_num_def cond_constr_narrowing_subst_rtran_def 
  using assms cond_constr_narrowing_subst_rtran_num_def by metis

lemma constructor_subst_apply:
  assumes csubst:"constructor_subst \<alpha>"
    and cterm:"constructor_term t"
  shows "constructor_term (t \<cdot> \<alpha>)" using assms unfolding constructor_subst_def constructor_term_def
proof(induct t)
  case (Var v)
  then show ?case unfolding constructor_term_def csubst constructor_subst_def by auto
next
  case (Fun f ss)
  then show ?case
  proof -{ 
    fix s
    assume asm:"s \<in> set ss" 
    with Fun(3) have "constructor_term s" unfolding constructor_term_def by auto
    hence cs:"constructor_term (s \<cdot> \<alpha>)" using Fun asm csubst
      by (simp add: constructor_term_def)
    hence "constructor_term (Fun f ss \<cdot> \<alpha>)" unfolding constructor_term_def
      by (smt (verit, ccfv_threshold) Fun.prems(1) Fun.prems(2) 
          UN_E UN_simps(10) Un_iff funas_term_subst subset_eq)
  } then show ?thesis using Fun.prems(2) constructor_term_def by auto
  qed
qed

lemma constructor_subst_compose:
  assumes \<alpha>:"constructor_subst \<alpha>"
    and \<beta>:"constructor_subst \<beta>"
  shows "constructor_subst (\<alpha> \<circ>\<^sub>s \<beta>)" using assms unfolding constructor_subst_def
proof (safe, goal_cases)
  case (1 u)
  then show ?case
  proof -
    have *:"constructor_term (\<alpha> u)" using \<alpha> 1 by force
    have **:"constructor_term (\<beta> u)" using \<beta> 1 by force
    from constructor_subst_apply[OF \<beta> *]
    have "constructor_term ((\<alpha> u) \<cdot> \<beta>)" by simp
    then show "constructor_term ((\<alpha> \<circ>\<^sub>s \<beta>) u)" by (simp add: subst_compose)
  qed
qed

lemma constructor_subst_union:
  assumes \<alpha>:"constructor_subst \<alpha>"
    and \<beta>:"constructor_subst \<beta>"
  shows "constructor_subst (\<alpha> \<union>\<^sub>s \<beta>)" using assms unfolding constructor_subst_def
proof (safe, goal_cases)
  case (1 u)
  then show ?case
  proof -
    have *:"constructor_term (\<alpha> u)" using \<alpha> 1 by force
    have **:"constructor_term (\<beta> u)" using \<beta> 1 by force
    from constructor_subst_apply[OF \<beta> *]
    have "constructor_term ((\<alpha> u) \<cdot> \<beta>)" by simp
    then show "constructor_term ((\<alpha> \<union>\<^sub>s \<beta>) u)" using  * ** by force
  qed
qed

lemma defined_imp_not_constructor: assumes def:"defined (Ru R) (f, n)"
  and root:"root t = Some (f, n)"
shows "\<not> constructor_term t"
proof (rule notI)
  assume asm:"constructor_term t"
  hence *:"funas_term t \<subseteq> funas_ctrs R - {fn. defined (Ru R) fn}" unfolding constructor_term_def by auto
  from root have **:"(f, n) \<in> {fn. defined (Ru R) fn}" by (simp add: def)
  have "(f, n) \<in> funas_term t" using root 
    by (metis UnI1 funas_term.simps(2) insertCI option.distinct(1) option.inject root.elims)
  then show False using * ** by blast
qed

lemma not_constructor_term_clhs: assumes rl:"rl \<in> R"
  shows "\<not> constructor_term (clhs rl)"   
proof(rule notI)
  assume asm:"constructor_term (clhs rl)"
  from wf[unfolded sdtrs_def wf_ctrs_def] have "(\<forall>((l, r), cs) \<in> R. is_Fun l)" by auto
  hence "\<exists>f n. root (clhs rl) = Some (f, n)" using rl 
    by (auto split:prod.splits) (metis is_VarI root.elims surjective_pairing)
  then obtain f n where root_rl:"root (clhs rl) = Some (f, n)" by auto
  hence "defined (Ru R) (f, n)" 
    by (metis defined_R_imp_Ru prod.collapse rl)
  then show False unfolding constructor_term_def defined_def using asm root_rl 
    by (simp add: defined_def defined_imp_not_constructor)
qed

lemma constructor_subst_var_perm: assumes con\<sigma>:"constructor_subst \<sigma>"
  and x\<sigma>:"\<And>x. (Var x) \<cdot> \<sigma> = (\<omega> \<bullet> (Var x)) \<cdot> \<sigma>'"
shows "constructor_subst \<sigma>'" 
proof -
  from con\<sigma> have "\<And>x. constructor_term ((\<omega> \<bullet> (Var x)) \<cdot> \<sigma>')" 
    unfolding constructor_subst_def constructor_term_def using x\<sigma> by auto
  hence "\<And>x. constructor_term ((Var x) \<cdot> \<sigma>')" 
    by (metis permute_term.simps(1) term_pt.permute_minus_cancel(1))
  then show "constructor_subst \<sigma>'" unfolding constructor_subst_def constructor_term_def by auto
qed

lemma cond_narrowing_set_imp_rtran:assumes "(S, T, \<sigma>) \<in> cond_narrowing_set"
  shows "cond_constr_narrowing_subst_rtran_num S T \<sigma> 1"
proof -
  have *:"(S, T) \<in> cond_constr_narrowing_rel" using assms 
    using cond_constr_narrowing_rel_def by fastforce
  then obtain f where f0:"f 0 = S" and f1:"f 1 = T" and rel_chain:"(f 0,  f (Suc 0)) \<in> cond_constr_narrowing_rel" 
    by (metis One_nat_def relpow_0_I relpow_Suc_I relpow_fun_conv)
  let ?\<tau> = "\<lambda>i. (if i = 0 then \<sigma> else Var)"
  show ?thesis  unfolding cond_constr_narrowing_subst_rtran_num_def
  proof(intro conjI, goal_cases)
    case 1
    then show ?case by (simp add: *)
  next
    case 2
    then show ?case by (rule exI[of _ f], rule exI[of _ ?\<tau>], insert assms f0 f1, auto)
  qed
qed

lemma constructor_based_conditional_lifting_lemma:
  fixes S::"('f, 'v)rule list" and T::"('f, 'v)rule list"
  assumes "constructor_subst \<theta>"
    and "T = subst_list \<theta> S"
    and cr:"(T,  T') \<in> (cond_reduction_set)\<^sup>*"
  shows "\<exists>\<sigma> \<theta>' S'. cond_constr_narrowing_subst_rtran S S' \<sigma> \<and> subst_list \<theta>' S' = T' \<and> constructor_subst \<theta>'"
proof -
  from cr
  obtain f n where f0:"f 0 = T" and fn:"f n = T'" and rel_chain:"\<forall>i < n. (f i,  f (Suc i)) \<in> cond_reduction_set" 
    by (metis rtrancl_imp_seq)
  then have "\<exists>\<sigma> \<theta>' S'. cond_constr_narrowing_subst_rtran_num S S' \<sigma> n \<and> subst_list \<theta>' S' = T' \<and> constructor_subst \<theta>'" using assms
  proof(induct n arbitrary: T')
    case 0
    show ?case
    proof(rule exI[of _ Var], rule exI[of _ \<theta>], rule exI[of _ S], safe, goal_cases)
      case 1
      then show ?case by (simp add:cond_constr_narrowing_subst_rtran_num_def, auto) 
    qed (insert assms 0 f0, auto)
  next
    case (Suc n)
    then obtain Tn where fnTn:"f n = Tn" by simp
    with Suc obtain \<sigma> \<theta>' S' where cond:"cond_constr_narrowing_subst_rtran_num S S' \<sigma> n" and
      S'Tn:"Tn = subst_list \<theta>' S'" and con\<theta>':"constructor_subst \<theta>'" 
      by (metis (no_types, lifting) less_SucI rtrancl_fun_conv)
    from n0_cond_constr_narrowing_subst_rtran_num have n0:"n = 0 \<Longrightarrow> S' = S \<and> \<sigma> = Var" 
      using cond by blast 
    from \<open>\<forall>i<Suc n. (f i, f (Suc i)) \<in> cond_reduction_set\<close> rel_chain
    have "(f n, f (Suc n)) \<in> cond_reduction_set" by simp
    hence "(f n, f (Suc n)) \<in> {(S, T) | S T. (S, T) \<in> cond_reduction_step} \<or> 
          (f n, f (Suc n)) \<in> {(S, T) | S T. (S, T) \<in> cond_matching_step}"  
      (is "?cond1 \<or> ?cond2") by (simp add: cond_reduction_set_def)
    then show ?case
    proof 
      assume ?cond2   
      then obtain s\<^sub>1 t\<^sub>1 xs \<sigma>' where fn:"f n = (s\<^sub>1, t\<^sub>1) # xs" and fsucn:"f (Suc n) = subst_list \<sigma>' xs" and cons1:"constructor_term s\<^sub>1" 
        and s1t1:"(s\<^sub>1  = t\<^sub>1 \<cdot> \<sigma>')" and wf_con\<sigma>':"wf_constructor_subst \<sigma>'" by auto
      from S'Tn fn fnTn obtain u v vs where S':"S' = (u, v) # vs" and sub:"subst_list \<theta>' ((u, v) # vs)  = (s\<^sub>1, t\<^sub>1) # xs"  
        unfolding subst_list_def by auto
      hence us1:"u \<cdot> \<theta>' = s\<^sub>1" and vt1:"v \<cdot> \<theta>' = t\<^sub>1" and sub_vsxs:"xs = subst_list  \<theta>' vs"
        by (auto simp add: subst_list_def, insert S' sub S'Tn fn fnTn) 
      from cons1 us1 con\<theta>' have consu:"constructor_term u"
        by (auto simp add: constructor_term_def funas_term_subst)
      from wf_con\<sigma>' have idemp:"\<sigma>' \<circ>\<^sub>s \<sigma>' = \<sigma>'"
        by (simp add: Term_More.subst_idemp_iff wf_constructor_subst_def)
      hence con\<sigma>':"constructor_subst \<sigma>'"
        using constructor_subst_def wf_con\<sigma>' wf_constructor_subst_def by auto
      from s1t1 us1 vt1 idemp have "(u \<cdot> \<theta>') \<cdot> \<sigma>' = (v \<cdot> \<theta>') \<cdot> \<sigma>'" by (metis subst_subst_compose)
      hence uv:"u \<cdot> (\<theta>' \<circ>\<^sub>s \<sigma>') = v \<cdot> (\<theta>' \<circ>\<^sub>s \<sigma>')" by auto
      then obtain \<delta> where mgu_uv:"mgu u v = Some \<delta>" 
        using ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast
      from mgu_sound[OF mgu_uv] uv have \<delta>:"(\<theta>'\<circ>\<^sub>s \<sigma>') =  \<delta> \<circ>\<^sub>s (\<theta>'\<circ>\<^sub>s \<sigma>')"
        by (metis is_imgu_def subst_monoid_mult.mult_assoc the_mgu the_mgu_is_imgu)
      then obtain \<gamma> where subst_eq:"(\<theta>'\<circ>\<^sub>s \<sigma>') = (\<delta> \<circ>\<^sub>s \<gamma>)" and gamma:"\<gamma> =  \<theta>'\<circ>\<^sub>s \<sigma>'" by auto
      let ?S = "subst_list \<delta> vs"
      have ss:"(S', ?S, \<delta>) \<in> {(S, T, \<sigma>) | S T s\<^sub>1 t\<^sub>1 xs \<sigma>. (S = (s\<^sub>1, t\<^sub>1) # xs \<and> T = subst_list \<sigma> xs \<and> constructor_term s\<^sub>1 \<and> mgu s\<^sub>1 t\<^sub>1 = Some \<sigma>)}" 
        using consu mgu_uv S' unfolding subst_list_def by blast
      hence *:"(S', ?S, \<delta>) \<in> cond_narrowing_set" using cond_narrowing_set_def by auto
      show ?thesis
      proof(rule exI[of _ "\<sigma> \<circ>\<^sub>s \<delta>"], rule exI[of _ \<gamma>], rule exI[of _ ?S], intro conjI)
        from * cond show "cond_constr_narrowing_subst_rtran_num S ?S (\<sigma> \<circ>\<^sub>s \<delta>) (Suc n)"
          unfolding cond_constr_narrowing_subst_rtran_num_def
        proof(intro conjI, goal_cases)
          case 1
          then show ?case unfolding cond_constr_narrowing_rel_def by auto
        next
          case 2
          note IH = this
          then obtain g \<tau> where g0:"g 0 = S" and gn:"g n = S'" and gchain:"(\<forall>i<n. (g i, g (Suc i), \<tau> i) \<in> cond_narrowing_set) \<and> 
              (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))" by auto
          let ?g = "\<lambda>i. if i = Suc n then ?S else g i"
          let ?\<tau> = "\<lambda>i. if i = n then \<delta> else \<tau> i"
          have **:"(?g n, ?g (n + 1), \<delta>) \<in> cond_narrowing_set"
            using ss  mgu_uv consu S' using "*" gn by fastforce
          show ?case
          proof(intro exI[of _ ?g] rule exI[of _ ?\<tau>], intro conjI, goal_cases)
            case 1
            then show ?case using g0 by auto
          next
            case 2
            then show ?case using ss S' mgu_uv consu unfolding cond_narrowing_set_def by auto
          next
            case 3
            then show ?case using ** by (simp add: gchain)
          next
            case 4
            from IH have \<sigma>:"(if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))" using gchain by force
            have *:"compose (map (\<lambda>i. if i = n then \<delta> else \<tau> i) [0..<n]) = compose (map (\<lambda>i. \<tau> i) [0..<n])" (is "compose ?lhs = compose ?rhs")
            proof -
              have "length ?lhs = length ?rhs" by simp
              from map_nth_eq_conv[OF this] map_equality_iff nat_neq_iff nth_upt
              show ?thesis by (smt (verit) add_0 diff_zero length_upt)             
            qed
            then show ?case by (cases "n = 0", insert \<sigma> *, auto)
          qed
        qed
        show "subst_list \<gamma> ?S = T'"
        proof -
          have "subst_list \<gamma> ?S  = subst_list \<gamma> (subst_list \<delta> vs)" by simp
          also have *:"... = subst_list (\<delta> \<circ>\<^sub>s \<gamma>) vs"
            by (simp add: subst_list_subst_compose)
          also have "... = subst_list (\<theta>'\<circ>\<^sub>s \<sigma>') vs" using subst_eq by force
          also have **:"... = subst_list \<sigma>' (subst_list \<theta>' vs)"
            by (simp add: subst_list_subst_compose)
          also have "... = subst_list \<sigma>' xs" using sub_vsxs by simp
          finally show ?thesis 
            using Suc.prems(2) fsucn * ** local.subst_eq sub_vsxs by auto
        qed
        from constructor_subst_compose[OF con\<theta>' con\<sigma>']
        show "constructor_subst \<gamma>" using gamma by auto
      qed
    next
      assume "?cond1"
      then obtain s\<^sub>1 t\<^sub>1 xs \<sigma>' rl p  where fn:"f n = (s\<^sub>1, t\<^sub>1) # xs" and fsucn:"f (Suc n) = subst_list \<sigma>' (snd rl) @ (replace_at s\<^sub>1 p ((crhs rl) \<cdot> \<sigma>'), t\<^sub>1) # xs"
        and rl:"rl \<in> R" and red_pos:"p \<in> fun_poss s\<^sub>1" 
        and s1p:"s\<^sub>1 |_ p = (clhs rl) \<cdot> \<sigma>'" and wf_con\<sigma>':"constructor_subst \<sigma>'" by auto
      have con\<theta>':"constructor_subst \<theta>'" by fact
      from wf_con\<sigma>' have con\<sigma>':"constructor_subst \<sigma>'" unfolding constructor_subst_def
        using constructor_subst_def by auto
      from S'Tn fn fnTn obtain u v vs where S':"S' = (u, v) # vs" and sub:"subst_list \<theta>' ((u, v) # vs) = (s\<^sub>1, t\<^sub>1) # xs"
        unfolding subst_list_def by auto
      hence us1:"u \<cdot> \<theta>' = s\<^sub>1" and vt1:"v \<cdot> \<theta>' = t\<^sub>1" and sub_vsxs:"xs = subst_list \<theta>' vs"
        by (auto simp add: subst_list_def, insert S' sub S'Tn fn fnTn)
      have "\<exists>\<omega>'. vars_seq S' \<inter> vars_crule (\<omega>' \<bullet> rl) = {}" 
        by (metis (no_types, opaque_lifting) crule_fs.rename_avoiding 
            finite_Un finite_vars_crule list.set_map prod.sel(2) supp_vars_crule_eq 
            vars_crule_def vars_defs(1) vars_seq_def)
      then obtain \<omega>' where varempty':"vars_seq S' \<inter> vars_crule (\<omega>' \<bullet> rl) = {}" by auto
      hence "\<exists>\<omega>r. \<omega>r \<bullet> \<omega>'\<bullet> rl \<in> R" using rl
        by (metis (no_types, opaque_lifting) crule_pt.permute_minus_cancel(2) crule_pt.permute_plus)
      then obtain \<omega>r where \<omega>r:"\<omega>r \<bullet> (\<omega>'\<bullet> rl) \<in> R" by auto
      have uS':"vars_term u \<subseteq> vars_seq S'" unfolding vars_seq_def 
        using S' vars_defs(2) by fastforce
      from red_pos have pfs1:"p \<in> fun_poss s\<^sub>1" by blast
      have ps1:"p \<in> poss s\<^sub>1" using fun_poss_imp_poss pfs1 by blast
      from not_constructor_term_clhs[OF \<omega>r]
      have "\<not> constructor_term (\<omega>r \<bullet> (\<omega>'\<bullet> (clhs rl)))" using \<omega>r unfolding constructor_term_def
        by (simp add: crule_pt.fst_eqvt rule_pt.fst_eqvt)
      hence "\<not> constructor_term (\<omega>'\<bullet> (clhs rl))" using constructor_term_def by auto
      hence "\<not> constructor_term (clhs rl)" using constructor_term_def by auto
      hence nc:"\<not> constructor_term ((clhs rl) \<cdot> \<sigma>')" 
        by (simp add: constructor_term_def funas_term_subst)
      have p:"p \<in> poss u" 
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence pnu:"p \<notin> poss u" by simp
        hence pnfu:"p \<notin> fun_poss u" using fun_poss_imp_poss by blast
        have sub_eq:"(u \<cdot> \<theta>') |_ p = (clhs rl) \<cdot> \<sigma>'" using us1 s1p by auto
        have "p \<in> fun_poss (u \<cdot> \<theta>')" using pfs1 us1 by auto
        from poss_subst_apply_term[of p u \<theta>']
        obtain q r x where qpr:"p = q @ r" and qu:"q \<in> poss u" and uqx:"u |_ q = Var x" and r:"r \<in> poss (\<theta>' x)"
          using pnfu ps1 us1 by blast
        hence *:"(u \<cdot> \<theta>') |_ p = (Var x) \<cdot> \<theta>' |_ r" by force
        have "constructor_term ((Var x) \<cdot> \<theta>')" using con\<theta>'
          by (simp add: constructor_subst_def constructor_term_def)
        hence "constructor_term ((Var x) \<cdot> \<theta>' |_ r)" 
        proof(auto simp add: constructor_subst_def constructor_term_def, insert r, goal_cases)
          case (1 f n)
          then show ?case 
            by (metis * constructor_term_def ctxt_supt_id eval_term.simps(1)
                funas_term_ctxt_apply le_sup_iff nc s1p us1)
        next
          case (2 f n)
          then show ?case 
            by (metis DiffD2 Int_Diff Un_iff ctxt_supt_id funas_term_ctxt_apply inf.orderE mem_Collect_eq)
        qed
        then show False using nc * using s1p us1 by auto
      qed
      hence pfun:"p \<in> fun_poss u" using ps1 us1 red_pos 
        by (metis con\<theta>' constructor_subst_def nc poss_is_Fun_fun_poss 
            poss_subst_choice ps1 s1p subt_at.simps(1) var_pos_maximal)
      hence vuS':"vars_term (u |_ p) \<subseteq> vars_seq S'" 
      proof -
        from vars_term_subt_at[OF p]
        have "vars_term (u |_ p) \<subseteq> vars_term u" by auto
        then show ?thesis using uS' by auto
      qed
      with varempty' have varcond:"vars_term (u |_ p) \<inter> vars_crule (\<omega>' \<bullet> rl) = {}" by blast
      have "\<exists>\<sigma>r. \<forall>x. \<sigma>r (\<omega>' \<bullet> x) = \<sigma>' x" using atom_pt.permute_minus_cancel(2) by (metis o_apply)
      then obtain \<sigma>r where \<sigma>rdef:"\<forall>x. \<sigma>r (\<omega>' \<bullet> x) = \<sigma>' x" by auto
      hence "\<forall>xs. subst_list \<sigma>r (\<omega>' \<bullet> xs) = subst_list \<sigma>' xs" unfolding subst_list_def
      proof(auto, goal_cases)
        case (1 xs s t)
        hence "(\<omega>' \<bullet> s) \<cdot> \<sigma>r = s \<cdot> \<sigma>'" 
          by (metis permute_term.simps(1) permute_term_subst_apply_term 
              subst_compose_def subst_monoid_mult.mult.left_neutral term_subst_eq_conv) 
        then show ?case 
          by (metis fst_conv rule_pt.fst_eqvt)
      next
        case (2 xs s t)
        hence "(\<omega>' \<bullet> t) \<cdot> \<sigma>r = t \<cdot> \<sigma>'" 
         by (metis permute_term.simps(1) permute_term_subst_apply_term 
              subst_compose_def subst_monoid_mult.mult.left_neutral term_subst_eq_conv) 
        then show ?case 
          by (metis snd_conv rule_pt.snd_eqvt)
      qed
      hence \<sigma>r1:"subst_list \<sigma>' [(fst rl)] = subst_list \<sigma>r [(fst (\<omega>' \<bullet> rl))]" and \<sigma>r2:"subst_list \<sigma>' (snd rl)  = subst_list \<sigma>r (snd (\<omega>' \<bullet> rl))" 
        by (metis (no_types, lifting) crule_pt.fst_eqvt list.simps(8) list.simps(9) rules_pt.permute_list_def) 
         (metis \<open>\<forall>xs. subst_list \<sigma>r (\<omega>' \<bullet> xs) = subst_list \<sigma>' xs\<close> crule_pt.snd_eqvt)
      hence pc:"clhs rl \<cdot> \<sigma>' = clhs (\<omega>' \<bullet> rl) \<cdot> \<sigma>r" by (simp add: subst_list_def)
      let ?\<sigma>r = "\<lambda>x. restrict_subst_domain (vars_crule (\<omega>' \<bullet> rl)) \<sigma>r x"
      let ?\<sigma>dom = "vars_term (clhs (\<omega>' \<bullet> rl)) \<union> vars_term (crhs (\<omega>' \<bullet> rl)) \<union> vars_trs (set (snd (\<omega>' \<bullet> rl)))"
      let ?\<sigma>X = "\<lambda>x. restrict_subst_domain (?\<sigma>dom) \<sigma>r x"
      have sub_\<sigma>r:"subst_domain ?\<sigma>r \<subseteq> (vars_crule (\<omega>' \<bullet> rl))" using subst_domain_restrict_subst_domain by fastforce
      let ?\<sigma> = "\<lambda>x. if x \<in> subst_domain ?\<sigma>r then (Var x) \<cdot> ?\<sigma>r else (Var x) \<cdot> \<sigma>r"
      let ?\<theta>' = "\<lambda>x. restrict_subst_domain (vars_seq S') \<theta>' x"
      let ?\<theta> = "\<lambda>x. if x \<in> subst_domain ?\<theta>' then (Var x) \<cdot> ?\<theta>' else (Var x) \<cdot> \<theta>'"
      have sub_\<theta>:"subst_domain ?\<theta>' \<subseteq> (vars_seq S')"
        using subst_domain_restrict_subst_domain by fastforce
      have inter_empty:"subst_domain ?\<sigma>X \<inter> subst_domain ?\<theta>' = {}" using varempty' 
        by (metis (no_types, opaque_lifting) Int_assoc Int_commute Int_empty_right 
            subst_domain_restrict_subst_domain vars_crule_def vars_rule_def)
      from  us1 s1p have *:"(u \<cdot> \<theta>' |_ p) = clhs (\<omega>' \<bullet> rl) \<cdot> \<sigma>r" 
        by (simp add: pc subst_apply_term_restrict_subst_domain) 
      have varcond':"vars_term (u |_ p) \<inter> vars_term (clhs (\<omega>' \<bullet> rl)) = {}" 
      proof -
        have "vars_term (clhs (\<omega>' \<bullet> rl)) \<subseteq> vars_crule (\<omega>' \<bullet> rl)"
          by (metis (mono_tags, opaque_lifting) dual_order.refl le_sup_iff vars_crule_def vars_defs(2))
        then show ?thesis using varcond by auto
      qed
      with con\<theta>' * have **:"(u |_ p) \<cdot> \<theta>' = clhs (\<omega>' \<bullet> rl) \<cdot> \<sigma>r" by (simp add: p)
      have sub_eq:"(u |_ p) \<cdot> ?\<theta>' = clhs (\<omega>' \<bullet> rl) \<cdot> ?\<sigma>X" using ** 
        by (simp add: Un_assoc subst_apply_term_restrict_subst_domain vuS' coincidence_lemma')
      from subst_union_sound[OF sub_eq]
      have subst_eq_\<theta>\<sigma>:"(u |_ p) \<cdot> (?\<theta>'\<union>\<^sub>s ?\<sigma>X)  = (clhs (\<omega>' \<bullet> rl)) \<cdot> (?\<theta>'\<union>\<^sub>s ?\<sigma>X)" using sub_\<sigma>r sub_\<theta> inter_empty
        by (smt (verit) Un_upper1 disjoint_iff notin_subst_domain_imp_Var sub_eq subsetD subst_union.simps 
            term_subst_eq_conv varempty' vars_crule_def vars_defs(2) vuS')
      then obtain \<delta> where mgu_uv:"mgu (u |_ p) (clhs (\<omega>' \<bullet> rl)) = Some \<delta>" using mgu_ex 
        by (meson ex_mgu_if_subst_apply_term_eq_subst_apply_term)
      from mgu_sound[OF mgu_uv] have \<delta>:"(?\<theta>'\<union>\<^sub>s ?\<sigma>X) =  \<delta> \<circ>\<^sub>s (?\<theta>'\<union>\<^sub>s ?\<sigma>X)" using subst_eq_\<theta>\<sigma> 
        by (smt (verit, ccfv_SIG) is_imgu_def subst_monoid_mult.mult_assoc the_mgu the_mgu_is_imgu)
      from fsucn have T':"T' = subst_list \<sigma>' (snd rl) @ (replace_at s\<^sub>1 p ((crhs rl) \<cdot> \<sigma>'), t\<^sub>1) # xs" 
        using Suc by blast
      let ?S = "subst_list \<delta> (snd (\<omega>' \<bullet> rl) @ (replace_at u p (crhs (\<omega>' \<bullet> rl)), v) # vs)"
      have vtrs:"vars_trs (set (snd (\<omega>' \<bullet> rl))) \<subseteq> vars_crule ((\<omega>' \<bullet> rl))" 
        by (simp add: vars_crule_def)
      have crl:"(crhs (\<omega>' \<bullet> rl)) \<cdot> \<sigma>r = ((crhs rl) \<cdot> \<sigma>')" 
        by (smt (verit) \<sigma>r1 list.inject list.simps(9) prod.inject subst_list_def)
      from subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
      have subinter:"subst_domain ?\<sigma>X = subst_domain \<sigma>r \<inter> ?\<sigma>dom" by auto
      have vtrs_dom:"vars_trs (set (snd (\<omega>' \<bullet> rl))) \<subseteq> ?\<sigma>dom" by blast
      have "subst_list ?\<sigma>X (snd (\<omega>' \<bullet> rl)) = subst_list \<sigma>r (snd (\<omega>' \<bullet> rl))" 
        using vtrs_dom subst_list_rest_domain by blast
      hence subpeq:"subst_list ?\<sigma>X (snd (\<omega>' \<bullet> rl)) = subst_list \<sigma>' (snd rl)" using \<sigma>r2 by auto
      have vars_inter_empty:"subst_domain ?\<theta>' \<inter> vars_trs (set (snd (\<omega>' \<bullet> rl))) = {}" 
        using vtrs varempty' using sub_\<theta> by auto
      from subst_union_reduction[of ?\<theta>' ?\<sigma>X]
      have "subst_list (?\<theta>' \<union>\<^sub>s ?\<sigma>X) (snd (\<omega>' \<bullet> rl)) = subst_list ?\<sigma>X (snd (\<omega>' \<bullet> rl))"
        using inter_empty vars_inter_empty by blast
      hence subeq:"subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) (snd (\<omega>' \<bullet> rl)) = subst_list \<sigma>' (snd rl)" using \<sigma>r2 inter_empty subpeq
        by auto
      hence vS:"vars_term v \<subseteq> vars_seq S'" using S' 
        using vars_defs(2) vars_seq_def by fastforce
      have vvs:"vars_trs (set vs) \<subseteq> vars_seq S'" using S'
        by (simp add: vars_rule_def vars_trs_def vars_seq_def)
      have sv:"subst_domain ?\<sigma>X \<inter> vars_term v = {}" 
         by (smt (verit, del_insts) disjoint_iff sub_\<sigma>r subsetD vS varempty' vars_crule_def vars_rule_def)
      have svsxs:"subst_list ?\<theta>' vs = xs" using  sub_vsxs 
        by (simp add: Int_commute \<open>vars_trs (set vs) \<subseteq> local.vars_seq S'\<close> subst_list_rest_domain)
      have sve:"subst_domain ?\<sigma>X \<inter> vars_trs (set vs) = {}" 
        by (smt (verit, del_insts) Int_Un_distrib Int_commute Int_left_commute Un_absorb2 
            Un_empty \<open>vars_trs (set vs) \<subseteq> local.vars_seq S'\<close> inf_bot_left subst_domain_restrict_subst_domain varempty' 
            vars_crule_def vars_rule_def)
      from subst_union_reduction [OF inter_empty sve] 
      have "subst_list (?\<sigma>X \<union>\<^sub>s ?\<theta>') vs = subst_list ?\<theta>' vs" by force
      hence suvsxs:"subst_list (?\<theta>' \<union>\<^sub>s ?\<sigma>X) vs = xs" using svsxs by (metis inter_empty sub_comm)
      have subun:"subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) [((replace_at u p (crhs (\<omega>' \<bullet> rl)), v))] = [(replace_at s\<^sub>1 p ((crhs rl) \<cdot> \<sigma>'), t\<^sub>1)]"
      proof -
        have "subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) [((replace_at u p (crhs (\<omega>' \<bullet> rl)), v))] = 
          [((replace_at (u \<cdot> (?\<theta>'\<union>\<^sub>s ?\<sigma>X)) p (crhs (\<omega>' \<bullet> rl) \<cdot> (?\<theta>'\<union>\<^sub>s ?\<sigma>X)), v \<cdot> (?\<theta>'\<union>\<^sub>s ?\<sigma>X)))]" 
          unfolding subst_list_def by (auto simp add: ctxt_of_pos_term_subst p)
        also have "... = [(replace_at s\<^sub>1 p (crhs (\<omega>' \<bullet> rl) \<cdot> (?\<theta>'\<union>\<^sub>s ?\<sigma>X)), v \<cdot> (?\<theta>'\<union>\<^sub>s ?\<sigma>X))]" using us1
          subst_union_reduction[of ?\<theta>' ?\<sigma>X]
          by (smt (z3) disjoint_iff mem_Collect_eq restrict_subst_domain_def 
              subsetD subst_domain_def subst_union.simps term_subst_eq_conv uS' varempty' vars_crule_def vars_defs(2))
        also have "... = [(replace_at s\<^sub>1 p ((crhs rl) \<cdot> \<sigma>'), v \<cdot> (?\<theta>'\<union>\<^sub>s ?\<sigma>X))]" using * 
          by (smt (z3) Un_upper1 crl disjoint_iff le_sup_iff mem_Collect_eq restrict_subst_domain_def 
              subsetD subst_domain_def subst_union.simps term_subst_eq_conv varempty' vars_crule_def vars_defs(2))
        also have "... = [(replace_at s\<^sub>1 p ((crhs rl) \<cdot> \<sigma>'), v \<cdot> ?\<theta>')]" 
          using  subst_union_term_reduction[of ?\<sigma>X ?\<theta>'] inter_empty sv 
          by (auto, smt (z3) disjoint_iff mem_Collect_eq restrict_subst_domain_def subst_domain_def term_subst_eq_conv)
        finally show ?thesis using vt1 vS subst_apply_term_restrict_subst_domain by auto
      qed
      have sub_st:"subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) ?S = T'" using T' 
      proof -
        have "subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) (snd (\<omega>' \<bullet> rl) @ (replace_at u p (crhs (\<omega>' \<bullet> rl)), v) # vs) = 
                  subst_list \<sigma>' (snd rl) @ (replace_at s\<^sub>1 p ((crhs rl) \<cdot> \<sigma>'), t\<^sub>1) # xs" 
        proof -
          have "subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) (snd (\<omega>' \<bullet> rl) @ (replace_at u p (crhs (\<omega>' \<bullet> rl)), v) # vs) = 
                subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) (snd (\<omega>' \<bullet> rl)) @ subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) ((replace_at u p (crhs (\<omega>' \<bullet> rl)), v) # vs)" 
            using subst_list_append by blast
          also have "... = subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) (snd (\<omega>' \<bullet> rl)) @ subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) [((replace_at u p (crhs (\<omega>' \<bullet> rl)), v))] @ subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) vs"
            by (metis append_Cons append_self_conv2 subst_list_append)
          also have "... = subst_list \<sigma>' (snd rl) @ subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) [((replace_at u p (crhs (\<omega>' \<bullet> rl)), v))] @ subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) vs"
            using subeq by (simp add: vars_crule_def vars_defs(2))
          also have "... = subst_list \<sigma>' (snd rl) @ subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) [((replace_at u p (crhs (\<omega>' \<bullet> rl)), v))] @ xs" 
            using suvsxs by auto 
          finally show ?thesis using subun by simp
        qed
        then show ?thesis using T' 
          by (metis (no_types, lifting) \<delta> subst_list_subst_compose vars_crule_def vars_defs(2))
      qed
      have "(S', ?S, \<delta>) \<in>  {(S, T, \<sigma>) | S T s\<^sub>1 t\<^sub>1 xs \<sigma> rl p \<omega>. (S = (s\<^sub>1, t\<^sub>1) # xs \<and>
        T = subst_list \<sigma> ((snd rl) @ (replace_at s\<^sub>1 p (crhs rl), t\<^sub>1) # xs) \<and>
        \<omega> \<bullet> rl \<in> R \<and> (vars_seq S \<inter> vars_crule rl = {}) \<and> p \<in> fun_poss s\<^sub>1 \<and> mgu (s\<^sub>1 |_ p) (clhs rl) = Some \<sigma>)}"
        unfolding subst_list_def using S' mgu_uv rl varempty' \<omega>r pfun by blast
      hence nar:"(S', ?S, \<delta>) \<in> cond_narrowing_set"
        using cond_narrowing_set_def cond_narrowing_stepI by force 
      from cond obtain g \<tau> where g0:"g 0 = S" and gn:"g n = S'" and gchain:"(\<forall>i<n. (g i, g (Suc i), \<tau> i) \<in> cond_narrowing_set) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))" 
        using cond_constr_narrowing_subst_rtran_num_def by blast
      let ?g = "\<lambda>i. if i = Suc n then ?S else g i"
      let ?\<tau> = "\<lambda>i. if i = n then \<delta> else \<tau> i"
      have g0_eq:"?g 0 = S" by (simp add: g0)
      have gsucn_eq:"?g (Suc n) = ?S" by auto
      have gn_nar:"(?g n, ?g (n + 1), \<delta>) \<in> cond_narrowing_set" using nar using gn by auto
      have "\<sigma> = compose (map ?\<tau> [0..< n])" 
        by (smt (verit) add_0 compose_simps(1) diff_zero gchain length_upt list.simps(8) 
            map_equality_iff nat_neq_iff nth_upt upt_0)
      hence \<sigma>\<delta>comp:"\<sigma> \<circ>\<^sub>s \<delta> = compose (map ?\<tau> [0..<Suc n])" by force
      show ?thesis
      proof(rule exI[of _ "\<sigma> \<circ>\<^sub>s \<delta>"], rule exI[of _ "(?\<theta>'\<union>\<^sub>s ?\<sigma>X)"], rule exI[of _ ?S], intro conjI)
        have *:"(\<exists>f \<tau>. f 0 = S \<and> f (Suc n) = ?S \<and> (\<forall>i<Suc n. (f i, f (Suc i), \<tau> i) \<in> cond_narrowing_set) \<and>
           (if Suc n = 0 then \<sigma> \<circ>\<^sub>s \<delta> = Var else \<sigma> \<circ>\<^sub>s \<delta> = compose (map \<tau> [0..<Suc n])))"
          by (rule exI[of _ ?g], rule exI[of _ ?\<tau>], simp add: gchain g0_eq gsucn_eq \<sigma>\<delta>comp g0, insert gn_nar, auto) 
        have **:"(S, ?S) \<in> cond_constr_narrowing_rel ^^ Suc n" using cond * nar 
          using cond_constr_narrowing_rel_def cond_constr_narrowing_subst_rtran_num_def by auto
        then show "cond_constr_narrowing_subst_rtran_num S ?S (\<sigma> \<circ>\<^sub>s \<delta>) (Suc n)" using * **
          using cond_constr_narrowing_subst_rtran_num_def by auto
        show "subst_list (?\<theta>'\<union>\<^sub>s ?\<sigma>X) ?S = T'" using sub_st by auto
        have con\<theta>'':"constructor_subst ?\<theta>'" using con\<theta>'
          by (simp add: constructor_subst_def constructor_term_def restrict_subst_domain_def,
              metis eval_term.simps(1) funas_term_subst in_subst_restrict le_sup_iff notin_subst_restrict)
        have "constructor_subst \<sigma>r" 
          by (auto simp add: constructor_subst_def, insert con\<sigma>') 
           (metis \<sigma>rdef atom_pt.permute_minus_cancel(1) constructor_subst_def)
        hence con\<sigma>r:"constructor_subst ?\<sigma>r" 
          by (simp add: constructor_subst_def constructor_term_def restrict_subst_domain_def)
           (metis eval_term.simps(1) funas_term_subst in_subst_restrict le_sup_iff notin_subst_restrict)
        from constructor_subst_union[OF con\<theta>'' con\<sigma>r]
        show "constructor_subst (?\<theta>'\<union>\<^sub>s ?\<sigma>X)" 
          by (simp add: vars_crule_def vars_defs(2))
      qed
    qed
  qed
  then show ?thesis using cond_narrowing_rtran_impl by blast
qed


(* Here, the empty list is a goal clause, where all narrowing/unification and reduction/matching steps have been successfully applied *)
lemma infeasibility_using_conditional_narrowing: assumes "S \<noteq> [] \<and> \<not> (\<exists>\<sigma>. cond_constr_narrowing_subst_rtran S [] \<sigma>)"
  shows "\<not> (\<exists>\<theta>. constructor_subst \<theta> \<and> (subst_list \<theta> S, []) \<in> (cond_reduction_set)\<^sup>+)"
proof(rule ccontr)
  assume "\<not>?thesis"
  hence "\<exists>\<theta>. constructor_subst \<theta> \<and> (subst_list \<theta> S, []) \<in> cond_reduction_set\<^sup>+" by auto
  then obtain \<theta> where con\<theta>:"constructor_subst \<theta>" and relsteps:"(subst_list \<theta> S, []) \<in> cond_reduction_set\<^sup>+" by auto
  define T where T:"T = subst_list \<theta> S"
  have reltran:"(T, []) \<in> cond_reduction_set\<^sup>*" using relsteps T by simp
  from constructor_based_conditional_lifting_lemma [OF con\<theta> T reltran]
  have "\<exists>\<sigma>. cond_constr_narrowing_subst_rtran S [] \<sigma>" 
    by (metis length_0_conv length_subst_list)
  then show False using assms by force
qed


end
end