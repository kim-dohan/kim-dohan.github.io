(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Formalization of narrowing and lifting lemma\<close>

theory Narrowing
  imports
    First_Order_Rewriting.Trs
    TRS.More_Abstract_Rewriting
    First_Order_Terms.Term_More
    TRS.Renaming_Interpretations
begin

fun subst_union::"('f,'v) subst \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) subst" (infixl "\<union>\<^sub>s" 67)
  where [intro]:"\<sigma> \<union>\<^sub>s \<theta> = (\<lambda>x. if x \<in> subst_domain \<sigma> then \<sigma> x else \<theta> x)"

lemma mgu_ex:
  assumes uv:"u = v \<cdot> \<theta>"
    and empty:"subst_domain \<theta> \<inter> range_vars \<theta> = {}"
  shows "\<exists>\<delta>. mgu u v = Some \<delta>"
proof -
  from subst_idemp_iff empty have idem:"\<theta> \<circ>\<^sub>s \<theta> = \<theta>" by auto
  with uv have "u \<cdot> \<theta> = v \<cdot> \<theta>" 
    by (simp add: subst_subst)
  with the_mgu_is_imgu[unfolded is_imgu_def]
  have "unifiers {(u, v)} \<noteq> {}" by blast
  then show ?thesis 
    by (simp add: ex_mgu_if_unifiers_not_empty)
qed

lemma restrict_subst_compose:
  assumes asm:"(B - subst_domain \<sigma>) \<union> range_vars \<sigma> \<subseteq> A"
    and \<theta>\<theta>':"\<forall>x. restrict_subst_domain A \<theta> x = restrict_subst_domain A \<theta>' x"
  shows "\<forall>x. restrict_subst_domain B (\<sigma> \<circ>\<^sub>s \<theta>) x =  restrict_subst_domain B (\<sigma> \<circ>\<^sub>s \<theta>') x" 
proof -
  let ?\<theta>1 = "\<lambda>x. restrict_subst_domain (range_vars \<sigma>) \<theta> x"
  let ?\<theta>2 = "\<lambda>x. restrict_subst_domain (B \<inter> subst_domain \<sigma>) (\<sigma> \<circ>\<^sub>s ?\<theta>1) x"
  let ?\<theta>3 = "\<lambda>x. restrict_subst_domain (B - subst_domain \<sigma>) \<theta> x"
  let ?\<theta>1' = "\<lambda>x. restrict_subst_domain (range_vars \<sigma>) \<theta>' x"
  let ?\<theta>2' = "\<lambda>x. restrict_subst_domain (B \<inter> subst_domain \<sigma>) (\<sigma> \<circ>\<^sub>s ?\<theta>1') x"
  let ?\<theta>3' = "\<lambda>x. restrict_subst_domain (B - subst_domain \<sigma>) \<theta>' x"
  let ?\<theta>l = "?\<theta>2 \<union>\<^sub>s ?\<theta>3"
  let ?\<theta>r = "?\<theta>2' \<union>\<^sub>s ?\<theta>3'"
  let ?\<sigma>\<theta>B = "\<lambda>x. restrict_subst_domain B (\<sigma> \<circ>\<^sub>s \<theta>) x"
  let ?\<sigma>\<theta>'B = "\<lambda>x. restrict_subst_domain B (\<sigma> \<circ>\<^sub>s \<theta>') x"
  from asm have "range_vars \<sigma> \<subseteq> A" by auto
  hence *:"\<forall>x. (Var x) \<cdot> ?\<theta>1  = (Var x) \<cdot> ?\<theta>1'" using \<theta>\<theta>' 
    by (metis eval_term.simps(1) in_mono restrict_subst_domain_def)
  hence **:"\<forall>x. (Var x) \<cdot> ?\<theta>2  = (Var x) \<cdot> ?\<theta>2'" using assms by simp
  from asm have "(B - subst_domain \<sigma>) \<subseteq> A" by auto
  hence ***:"\<forall>x. (Var x) \<cdot> ?\<theta>3 = (Var x) \<cdot> ?\<theta>3'" using \<theta>\<theta>' *
    by (metis eval_term.simps(1) restrict_subst_domain_def subsetD)
  have "?\<theta>l = ?\<theta>r" using * ** *** by simp
  moreover have "\<forall>x. (Var x) \<cdot> ?\<sigma>\<theta>B = (Var x) \<cdot> ?\<theta>l"
  proof(auto, goal_cases)
    case (1 x)
    hence "(\<sigma> \<circ>\<^sub>s \<theta>) x = (\<sigma> \<circ>\<^sub>s restrict_subst_domain (range_vars \<sigma>) \<theta>) x"
      by (metis (no_types, opaque_lifting) Diff_eq_empty_iff Term.term.simps(17) 
          Un_Diff_Int eval_term.simps(1) inf.order_iff insert_Diff1 le_sup_iff 
          subsetI subst_apply_term_restrict_subst_domain subst_compose vars_term_subst_apply_term_subset)
    then show ?case using assms 1 by (simp add: restrict_subst_domain_def)
  next
    case (2 x)
    then show ?case 
      by (metis Diff_iff eval_term.simps(1) notin_subst_domain_imp_Var restrict_subst_domain_def subst_compose)
  next
    case (3 x)
    then show ?case by (simp add: restrict_subst_domain_def)
  next
    case (4 x)
    from notin_subst_domain_imp_Var[OF this]
    have *:"(\<sigma> \<circ>\<^sub>s restrict_subst_domain (range_vars \<sigma>) \<theta>) x = Var x" by simp
    from subst_domain_restrict_subst_domain
    have "subst_domain (restrict_subst_domain (range_vars \<sigma>) \<theta>) = (range_vars \<sigma>) \<inter> subst_domain \<theta>" by simp
    then show ?case using * 4
    proof(cases "x \<in> B")
      case True
      then show ?thesis 
        by (smt (verit, ccfv_threshold) "*" Diff_iff mem_Collect_eq restrict_subst_domain_def 
            subst_apply_eq_Var subst_compose_def subst_domain_def subst_monoid_mult.mult.left_neutral)
    next
      case False
      then show ?thesis by (simp add: restrict_subst_domain_def)
    qed
  qed
  moreover have "\<forall>x. (Var x) \<cdot> ?\<theta>r = (Var x) \<cdot> ?\<sigma>\<theta>'B"
  proof(auto, goal_cases)
    case (1 x)
    hence "(\<sigma> \<circ>\<^sub>s \<theta>') x = (\<sigma> \<circ>\<^sub>s restrict_subst_domain (range_vars \<sigma>) \<theta>') x"
      by (metis (no_types, opaque_lifting) Diff_eq_empty_iff Term.term.simps(17) 
          Un_Diff_Int eval_term.simps(1) inf.order_iff insert_Diff1 le_sup_iff 
          subsetI subst_apply_term_restrict_subst_domain subst_compose vars_term_subst_apply_term_subset)
    then show ?case using assms 1 by (simp add: restrict_subst_domain_def)
  next
    case (2 x)
    then show ?case 
      by (metis Diff_iff eval_term.simps(1) notin_subst_domain_imp_Var restrict_subst_domain_def subst_compose)
  next
    case (3 x)
    then show ?case by (simp add: restrict_subst_domain_def)
  next
    case (4 x)
    from notin_subst_domain_imp_Var[OF this]
    have *:"(\<sigma> \<circ>\<^sub>s restrict_subst_domain (range_vars \<sigma>) \<theta>') x = Var x" by simp
    from subst_domain_restrict_subst_domain
    have "subst_domain (restrict_subst_domain (range_vars \<sigma>) \<theta>') = (range_vars \<sigma>) \<inter> subst_domain \<theta>'" by simp
    then show ?case using * 4
    proof(cases "x \<in> B")
      case True
      then show ?thesis 
        by (smt (verit, ccfv_threshold) "*" Diff_iff mem_Collect_eq restrict_subst_domain_def 
            subst_apply_eq_Var subst_compose_def subst_domain_def subst_monoid_mult.mult.left_neutral)
    next
      case False
      then show ?thesis by (simp add: restrict_subst_domain_def)
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma restrict_subst[simp]: "restrict_subst_domain V \<sigma> =  \<sigma> |s V" unfolding restrict_subst_domain_def by auto

(* MH94: Completeness Results for Basic Narrowing by Aart Middeldorp and Erik Hamoen *)

(* MH94. Proposition 3.6 *)

lemma r_subst_compose:
  assumes asm:"(B - subst_domain \<sigma>) \<union> range_vars \<sigma> \<subseteq> A"
    and \<theta>\<theta>':"\<theta> |s A = \<theta>'|s A"
  shows "(\<sigma> \<circ>\<^sub>s \<theta>) |s B = (\<sigma> \<circ>\<^sub>s \<theta>') |s B" using restrict_subst_compose
  by (metis (no_types, opaque_lifting) \<theta>\<theta>' asm in_subst_restrict restrict_subst subst_ext)

lemma subst_union_sound:assumes st:"s \<cdot> \<alpha> = t \<cdot> \<beta>"
  and s\<alpha>:"subst_domain \<alpha> \<subseteq> vars_term s "
  and t\<beta>:"subst_domain \<beta> \<subseteq> vars_term t"
  and disj:"vars_term s \<inter> vars_term t = {}"
shows "s \<cdot> (\<alpha> \<union>\<^sub>s \<beta>) = t \<cdot> (\<alpha> \<union>\<^sub>s \<beta>)" 
proof -
  from term_subst_eq_conv[of s \<alpha> "\<alpha> \<union>\<^sub>s \<beta>"]
  have *:"s \<cdot> \<alpha> = s \<cdot> (\<alpha> \<union>\<^sub>s \<beta>)" using s\<alpha> unfolding subst_union.simps
    by (metis disj disjoint_iff notin_subst_domain_imp_Var subsetD t\<beta>)
  from term_subst_eq_conv[of t \<beta> "\<alpha> \<union>\<^sub>s \<beta>"]
  have "t \<cdot> \<beta> = t \<cdot> (\<alpha> \<union>\<^sub>s \<beta>)" using t\<beta> disj s\<alpha> by auto
  then show ?thesis using * st by auto
qed

lemma sub_comm[simp]: assumes "subst_domain \<sigma> \<inter> subst_domain \<theta> = {}"
  shows "\<sigma> \<union>\<^sub>s \<theta> = \<theta> \<union>\<^sub>s \<sigma>" using assms by auto 
    (metis disjoint_insert(2) insert_absorb notin_subst_domain_imp_Var)

lemma subst_list_rest_domain: assumes asm:"\<sigma> = (\<lambda>x. restrict_subst_domain V \<theta> x)"
  and vts:"vars_trs (set xs) \<subseteq> V"
shows "subst_list \<sigma> xs = subst_list \<theta> xs"  using assms unfolding subst_list_def vars_trs_def 
  by (simp add: restrict_subst_domain_def subset_eq term_subst_eq_conv vars_rule_def)

definition subst_term_list :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) term list" where 
  "subst_term_list \<sigma> xs = map (\<lambda>p.  p \<cdot> \<sigma>) xs"

definition subst_term_set :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set \<Rightarrow> ('f, 'v) term set" where
  "subst_term_set \<sigma> S = (\<Union>t\<in>S. {t \<cdot> \<sigma>})"

definition subst_term_multiset :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset" where
  "subst_term_multiset \<sigma> M = {# (t \<cdot> \<sigma>). t \<in># M #}"

definition subst_equation :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f, 'v) equation" where 
  "subst_equation \<sigma> eq = ((fst eq) \<cdot> \<sigma>, (snd eq) \<cdot> \<sigma>)"

lemma subst_term_multiset_empty [simp]:"subst_term_multiset \<sigma> {#} = {#}" unfolding subst_term_multiset_def by auto

definition vars_term_list::"('f, 'v) term list \<Rightarrow> 'v set" where
  "vars_term_list S = \<Union> (set (map (vars_term) S))"

definition vars_term_set::"('f, 'v) term set \<Rightarrow> 'v set" where
  "vars_term_set S = (\<Union>t\<in>S. vars_term t)"

lemma subst_term_set_compose: "subst_term_set \<sigma> (subst_term_set \<theta> X) = subst_term_set (\<theta> \<circ>\<^sub>s \<sigma>) X"
  unfolding subst_term_set_def by auto

lemma subst_term_multiset_compose: "subst_term_multiset \<sigma> (subst_term_multiset \<theta> X) = subst_term_multiset (\<theta> \<circ>\<^sub>s \<sigma>) X"
  unfolding subst_term_multiset_def
  by (metis (no_types, lifting) comp_apply multiset.map_comp multiset.map_cong0 subst_subst)

lemma subst_term_list_rest_domain: assumes asm:"\<sigma> = (\<lambda>x. restrict_subst_domain V \<theta> x)"
  and vts:"vars_term_list xs \<subseteq> V"
shows "subst_term_list \<sigma> xs = subst_term_list \<theta> xs"  using assms unfolding subst_term_list_def vars_term_list_def 
  by (simp add: restrict_subst_domain_def subset_eq term_subst_eq_conv vars_rule_def)

lemma subst_term_set_rest_domain: assumes asm:"\<sigma> = (\<lambda>x. restrict_subst_domain V \<theta> x)"
  and vts:"vars_term_set S \<subseteq> V"
shows "subst_term_set \<sigma> S = subst_term_set \<theta> S"  using assms unfolding subst_term_set_def vars_term_set_def
  by (smt (verit, ccfv_SIG) Sup.SUP_cong UN_subset_iff restrict_subst_domain_def subset_eq term_subst_eq_conv)

lemma subst_term_multiset_rest_domain: assumes asm:"\<sigma> = (\<lambda>x. restrict_subst_domain V \<theta> x)"
  and vts:"vars_term_set (set_mset S) \<subseteq> V"
shows "subst_term_multiset \<sigma> S = subst_term_multiset \<theta> S"  using assms unfolding subst_term_multiset_def vars_term_set_def
  by (meson SUP_le_iff multiset.map_cong0 subst_apply_term_restrict_subst_domain)

lemma subst_union_term_reduction: assumes "subst_domain \<theta> \<inter> subst_domain \<sigma> = {}"
  and "subst_domain \<theta> \<inter> vars_term t = {}"
shows "t \<cdot> (\<theta> \<union>\<^sub>s \<sigma>) = t \<cdot> \<sigma>" using assms  term_subst_eq_conv by fastforce

lemma subst_union_reduction: assumes "subst_domain \<theta> \<inter> subst_domain \<sigma> = {}"
  and "subst_domain \<theta> \<inter> vars_trs(set xs) = {}"
shows "subst_list (\<theta> \<union>\<^sub>s \<sigma>) xs = subst_list \<sigma> xs" using assms subst_union_term_reduction  
  unfolding vars_trs_def subst_list_def by auto 
    (smt (verit, del_insts) UN_iff UnCI disjoint_iff prod.sel(1) term_subst_eq_conv vars_defs(2),
      smt (verit, best) UN_iff UnCI disjoint_iff snd_conv term_subst_eq_conv vars_defs(2))

lemma subst_union_term_list_reduction: assumes "subst_domain \<theta> \<inter> subst_domain \<sigma> = {}"
  and "subst_domain \<theta> \<inter> vars_term_list xs = {}"
shows "subst_term_list (\<theta> \<union>\<^sub>s \<sigma>) xs = subst_term_list \<sigma> xs" using assms subst_union_term_reduction  
  unfolding subst_term_list_def vars_term_list_def by fastforce

lemma subst_union_term_set_reduction: assumes "subst_domain \<theta> \<inter> subst_domain \<sigma> = {}"
  and "subst_domain \<theta> \<inter> vars_term_set S = {}"
shows "subst_term_set (\<theta> \<union>\<^sub>s \<sigma>) S = subst_term_set \<sigma> S" using assms subst_union_term_reduction  
  unfolding subst_term_set_def vars_term_set_def by fastforce

lemma subst_union_term_multiset_reduction: assumes "subst_domain \<theta> \<inter> subst_domain \<sigma> = {}"
  and "subst_domain \<theta> \<inter> vars_term_set (set_mset S) = {}"
shows "subst_term_multiset (\<theta> \<union>\<^sub>s \<sigma>) S = subst_term_multiset \<sigma> S" using assms subst_union_term_reduction  
  unfolding subst_term_multiset_def vars_term_set_def
  by (metis (mono_tags, lifting) Int_UN_distrib SUP_bot_conv(1) multiset.map_cong0)

lemma inv_var_subst:assumes "x \<in> vars_term t"
  and "x \<notin> subst_domain \<delta>"
  and "x \<notin> range_vars \<delta>"
shows "x \<in> vars_term (t \<cdot> \<delta>)" using assms 
proof(induct t)
  case (Var x)
  then show ?case using assms 
    by (metis eval_term.simps(1) notin_subst_domain_imp_Var 
        term.distinct(1) term.set_cases(2))
next
  case (Fun f ss)
  then show ?case by auto
qed

lemma replace_var_stable: assumes "vars_term s \<subseteq> vars_term t"
  shows "vars_term (replace_at u p s) \<subseteq> vars_term (replace_at u p t)" using assms 
  by (metis Un_upper1 ctxt_supteq le_sup_iff sup.absorb_iff2 supteq_imp_vars_term_subset vars_term_ctxt_apply)

definition subst_rule :: "('f, 'v) subst \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('f, 'v) rule"
  where "subst_rule \<sigma> lr = ((fst lr) \<cdot> \<sigma>, (snd lr) \<cdot> \<sigma>)"

lemma mgu_finite_range_vars:
  "mgu s t = Some \<sigma> \<Longrightarrow> finite (range_vars \<sigma>)"
  by (metis finite_Un finite_subset finite_vars_term mgu_range_vars)

definition normal_subst :: "('f, 'v::infinite) trs \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "normal_subst R \<sigma> \<longleftrightarrow> (\<forall>x \<in> subst_domain \<sigma>. \<sigma> x \<in> NF (rstep R))"

definition normalizable_subst ::"('f, 'v::infinite) trs \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "normalizable_subst R \<sigma> \<longleftrightarrow> (\<forall>x \<in> subst_domain \<sigma>. \<exists>y. (\<sigma> x, y) \<in> (rstep R)\<^sup>* \<and> y \<in> NF (rstep R))"

lemma Var_NF_rstep:
  assumes "\<forall> (l, r) \<in> R. is_Fun l"
  shows "Var x \<in> NF (rstep R)"
proof
  fix s
  show "(Var x, s) \<notin> rstep R"
  proof
    assume "(Var x, s) \<in> rstep R"
    then show "False" using assms supteq_var_imp_eq by fastforce
  qed
qed

lemma empty_subst_normalized:
  assumes "\<forall>(l, r) \<in> R. is_Fun l"
  shows "normal_subst R Var" 
  by (simp add:Var_NF_rstep[OF assms] normal_subst_def)

definition "strongly_irreducible_term R t \<longleftrightarrow> (\<forall>\<sigma>. normal_subst R \<sigma> \<longrightarrow> t \<cdot> \<sigma> \<in> NF (rstep R))"

lemma strongly_irreducible_I [Pure.intro?]:
  assumes "\<And>\<sigma>. normal_subst R \<sigma> \<Longrightarrow> t \<cdot> \<sigma> \<in> NF (rstep R)"
  shows "strongly_irreducible_term R t"
  using assms by (auto simp add: strongly_irreducible_term_def)

lemma Var_strongly_irreducible_cstep:
  "\<forall> (l, r) \<in> R. is_Fun l \<Longrightarrow> strongly_irreducible_term R (Var x)"
  by (rule strongly_irreducible_I, simp add: normal_subst_def)
    (metis Var_NF_rstep notin_subst_domain_imp_Var)

locale narrowing =
  fixes R :: "('f, 'v:: infinite) trs"
  assumes wf: "wf_trs R" 
begin

inductive_set narrowing_step  ("\<leadsto>" 50) where
    "(t = (replace_at s p (snd rl)) \<cdot> \<delta> \<and> \<omega> \<bullet> rl \<in> R \<and> (vars_term s \<inter> vars_rule rl = {}) \<and> 
      p \<in> fun_poss s \<and> mgu (s |_ p) (fst rl) = Some \<delta>) \<Longrightarrow> (s, t, \<delta>) \<in> narrowing_step"

definition narrowing_rel::"(('f, 'v::infinite) term) rel" where 
  "narrowing_rel = {(s, t) | s t \<sigma>. (s, t, \<sigma>) \<in> narrowing_step}"

lemmas narrowing_stepI = narrowing_step.intros [intro]
lemmas narrowing_stepE = narrowing_step.cases [elim]

definition narrowing_derivation where
  "narrowing_derivation s s' \<sigma> \<longleftrightarrow> (\<exists>n. (\<exists>f \<tau>. f 0 = s \<and> f n = s' \<and> 
  (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

definition narrowing_derivation_num where
  "narrowing_derivation_num s s' \<sigma> n \<longleftrightarrow> (\<exists>f \<tau>. f 0 = s \<and> f n = s' \<and> 
  (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n])))"

lemma n0_narrowing_derivation_num:"narrowing_derivation_num s s' \<sigma> 0 \<Longrightarrow> s = s' \<and> \<sigma> = Var"
  unfolding narrowing_derivation_num_def by auto

lemma narrowing_deriv_implication: assumes "narrowing_derivation_num s s' \<sigma> n"
  shows "narrowing_derivation s s' \<sigma>" 
  unfolding narrowing_derivation_num_def narrowing_derivation_def 
  using assms narrowing_derivation_num_def by metis

lemma normal_subst_union:
  assumes \<alpha>:"normal_subst R \<alpha>"
    and \<beta>:"normal_subst R \<beta>"
  shows "normal_subst R (\<alpha> \<union>\<^sub>s \<beta>)" using assms unfolding normal_subst_def 
  by (metis NF_I NF_Var local.wf notin_subst_domain_imp_Var subst_union.simps)

lemma narrowing_set_imp_rtran: assumes "(s, t, \<sigma>) \<in> narrowing_step"
  shows "narrowing_derivation_num s t \<sigma> 1"
proof -
  from assms obtain f where f0:"f 0 = s" and f1:"f 1 = t" and rel_chain:"(f 0,  f (Suc 0), \<sigma>) \<in> narrowing_step" 
    by auto (metis nth_Cons_0 nth_Cons_Suc)
  let ?\<tau> = "\<lambda>i. (if i = 0 then \<sigma> else Var)"
  show ?thesis  unfolding narrowing_derivation_num_def 
    by (rule exI[of _ f], rule exI[of _ ?\<tau>], insert assms f0 f1, auto)
qed

lemma normal_subst__perm: assumes norm:"normal_subst R \<sigma>"
  and equiv:"\<forall>x. \<sigma> x = \<sigma>r (\<omega> \<bullet> x)"
shows "normal_subst R \<sigma>r" 
proof -
  from norm have "\<forall>x. \<sigma> (-\<omega> \<bullet> x) \<in> NF (rstep R)"
    by (simp add: normal_subst_def)
      (metis NF_I local.wf no_Var_rstep notin_subst_domain_imp_Var)
  moreover have "\<forall>x. \<sigma> (\<omega> \<bullet> -\<omega> \<bullet> x) \<in> NF (rstep R)" 
    by (simp add: norm normal_subst_def) 
      (metis atom_pt.permute_minus_cancel(2) calculation)
  moreover have "\<forall>x. \<sigma> (-\<omega> \<bullet> x) = \<sigma>r (\<omega> \<bullet> -\<omega> \<bullet> x)" using equiv by simp
  moreover have "\<forall>x. \<sigma>r (\<omega> \<bullet> -\<omega> \<bullet> x) = \<sigma>r x" by simp
  ultimately show ?thesis 
    by (simp add: normal_subst_def)
qed

lemma funas_term_perm: fixes S::"'f sig"
  assumes "funas_term t \<subseteq> S"
  shows "funas_term (\<omega> \<bullet> t) \<subseteq> S" 
  by (simp add: assms)

lemma funas_rule_perm: fixes S::"'f sig"
  assumes "funas_rule rl \<subseteq> S"
  shows "funas_rule (\<omega> \<bullet> rl) \<subseteq> S"
proof -
  have "funas_term (fst rl) \<subseteq> S" using assms funas_rule_def by blast
  hence *:"funas_term (fst (\<omega> \<bullet> rl)) \<subseteq> S" 
    by (metis funas_term_permute rule_pt.fst_eqvt)
  have "funas_term (snd rl) \<subseteq> S" using assms funas_rule_def by blast
  hence **:"funas_term (snd (\<omega> \<bullet> rl)) \<subseteq> S" 
    by (metis funas_term_permute rule_pt.snd_eqvt)
  then show ?thesis using * **
    by (simp add: funas_rule_def)
qed

lemma funas_trs_perm: fixes S::"'f sig"
  assumes "funas_trs T \<subseteq> S"
  shows "funas_trs (\<omega> \<bullet> T) \<subseteq> S" 
proof -
  have "(\<Union>r \<in> T. funas_rule r) \<subseteq> S" using assms by (simp add: funas_trs_def)
  hence "(\<Union>r \<in> T. funas_rule (\<omega> \<bullet> r )) \<subseteq> S" using funas_rule_perm
    by (metis (no_types, lifting) SUP_le_iff)
  then show ?thesis unfolding funas_trs_def 
    by (metis (no_types, lifting) SUP_le_iff rule_pt.permute_minus_cancel(1) trs_pt.inv_mem_simps(1))
qed

lemma sop_perm_equiv:" (\<omega> \<bullet> rl) \<cdot> ((sop (- \<omega>) \<circ>\<^sub>s sop \<omega>')::('f, 'v) subst) = (\<omega>' \<bullet> rl)" 
  by (simp add: rule_pt.fst_eqvt)

lemma subst_equation_perm: "subst_equation ((sop (- \<omega>) \<circ>\<^sub>s sop \<omega>')::('f, 'v) subst) (\<omega> \<bullet> rl) =
  (\<omega>' \<bullet> rl)" using sop_perm_equiv unfolding subst_equation_def
  by (simp add: rule_pt.fst_eqvt rule_pt.snd_eqvt)

lemma root_perm_inv: "root t = root (\<omega> \<bullet> t)" by (induct t, auto)

lemma root_symbol_in_funas: assumes "root t = Some (f, n)"
  shows "(f, n) \<in> funas_term t" using assms by (induct t, auto) 

lemma fun_root_not_None:"is_Fun t \<Longrightarrow> root t \<noteq> None" by (induct t, auto)

lemma root_subst_inv: fixes \<theta>::"('f, 'v)subst"
  assumes "p \<in> fun_poss u"
  shows "root(u |_ p \<cdot> \<theta>) = root(u |_ p)" using assms
  by (induct "u |_ p", insert fun_poss_fun_conv, fastforce+)

lemma subterm_funas:assumes "root (u |_ p) = Some (f, n)"
  and pfun:"p \<in> fun_poss u"
shows "(f, n) \<in> funas_term u" 
proof -  
  { fix ss
    assume "u |_ p = Fun f ss" and "n = length ss"
    then have *:"(f, n) \<in> funas_term (u |_ p)" by auto
    hence "(f, n) \<in> funas_term u"
    proof (cases "p = []")
      case True
      then show ?thesis using * by auto
    next
      case False
      then show ?thesis using assms
      proof -
        from False have "u \<rhd> (u |_ p)" using pfun by (metis fun_poss_imp_poss subt_at_id_imp_eps 
              subt_at_imp_supteq subterm.dual_order.strict_iff_order)
        then show ?thesis using assms supt_imp_funas_term_subset using * by blast
      qed
    qed  
  } then show ?thesis by (metis assms(1) fst_conv prod.sel(2) root_Some)
qed

lemma subst_app_subterm: fixes \<theta>::"('f, 'v)subst"
  assumes "x \<in> vars_term t"
  shows "\<theta> x \<unlhd> t \<cdot> \<theta>" using assms
proof(induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  then show ?case by (meson subst_image_subterm supt_imp_supteq)
qed

lemma NF_rstep_subterm:
  assumes "t \<in> NF (rstep R)" and "t \<unrhd> s"
  shows "s \<in> NF (rstep R)"
proof (rule ccontr)  
  assume "\<not> ?thesis"
  then obtain u where "(s, u) \<in> rstep R" by auto
  from \<open>t \<unrhd> s\<close> obtain C where "t = C\<langle>s\<rangle>" by auto
  with \<open>(s, u) \<in> rstep R\<close> have "(t, C\<langle>u\<rangle>) \<in> rstep R" by auto
  then have "t \<notin> NF (rstep R)" by auto
  with assms show False by simp
qed

(* Proposition 3.7 in MH94*)
lemma restricted_normalized: fixes A::"('v::infinite) set" and B::"('v::infinite) set" and \<sigma> \<theta> \<theta>'::"('f, 'v)subst"
  assumes "normal_subst R (\<theta> |s A)"
    and "(\<sigma> \<circ>\<^sub>s \<theta>') |s A  = \<theta> |s A"
    and B:"B \<subseteq> (A - subst_domain \<sigma>) \<union> range_vars (\<sigma> |s A)"
  shows "normal_subst R (\<theta>' |s B)" using assms
proof -
  { fix x
    assume "x \<in> B"
    with B have "x \<in> (A - subst_domain \<sigma>) \<or> x \<in> range_vars (\<sigma> |s A)" by auto
    hence "(\<theta>' x) \<in> NF (rstep R)" 
    proof 
      assume asm:"x \<in> (A - subst_domain \<sigma>)"
      hence "\<theta>' x = (\<sigma> \<circ>\<^sub>s \<theta>') x" 
        by (metis DiffD2 eval_term.simps(1) notin_subst_domain_imp_Var subst_compose_def)
      also have "... = \<theta> x" 
        by (metis Diff_iff asm assms(2) in_subst_restrict)
      then show "(\<theta>' x) \<in> NF (rstep R)" using assms by (metis DiffD1 NF_I NF_Var asm calculation 
            in_subst_restrict local.wf normal_subst_def notin_subst_domain_imp_Var)
    next
      assume "x \<in> range_vars (\<sigma> |s A)"
      hence "\<exists>y \<in> A. x \<in> vars_term (\<sigma> y)" unfolding range_vars_def subst_domain_def by auto
          (metis IntE in_subst_restrict restrict_subst subst_domain_restrict_subst_domain)
      then obtain y where y:"y \<in> A" and x:"x \<in> vars_term (\<sigma> y)" by auto
      hence *:"(\<sigma> \<circ>\<^sub>s \<theta>') y = \<theta> y" by (metis assms(2) in_subst_restrict)
      from subst_app_subterm have "\<theta>' x \<unlhd> (\<sigma> y) \<cdot> \<theta>'" using x by auto
      moreover have "\<theta> y \<in> NF (rstep R)" 
        by (metis NF_I assms(1) in_subst_restrict local.wf no_Var_rstep normal_subst_def 
            notin_subst_domain_imp_Var y)
      ultimately show "(\<theta>' x) \<in> NF (rstep R)"
        by (metis NF_rstep_subterm * subst_compose_def)
    qed
  } then show ?thesis unfolding subst_restrict_def normal_subst_def 
    by (meson NF_I local.wf no_Var_rstep)
qed

lemma vars_term_range: fixes \<delta>::"('f, 'v)subst"
  assumes "x \<in> range_vars \<delta>"
    and "x \<in> vars_term t"
    and "subst_domain \<delta> \<inter> range_vars \<delta> = {}"
  shows "x \<in> vars_term (t \<cdot> \<delta>)" using assms 
proof(induct t)
  case (Var x)
  then show ?case unfolding range_vars_def subst_domain_def by auto
      (metis Var.prems(1) assms(3) disjoint_iff notin_subst_domain_imp_Var term.set_intros(3)) 
next
  case (Fun f ss)
  then show ?case unfolding range_vars_def subst_domain_def by auto
qed 

lemma subst_restricted_range_vars: fixes \<delta>::"('f, 'v)subst" 
  assumes "x \<in> vars_term (t \<cdot> \<delta>)" 
    and disj:"subst_domain \<delta> \<inter> range_vars \<delta> = {}"
    and "x \<notin> vars_term t"
    and "x \<in> range_vars \<delta>"
  shows "x \<in> range_vars (\<delta> |s vars_term t)" using assms
proof(induct t)
  case (Var x)
  have "vars_term (Var x \<cdot> \<delta>) = range_vars (\<delta> |s vars_term (Var x))" 
  proof(cases "x \<in> subst_domain \<delta>")
    case True
    then show ?thesis unfolding range_vars_def subst_domain_def by auto 
        (metis IntI True in_subst_restrict insertI1 restrict_subst subst_domain_restrict_subst_domain,
          metis IntE in_subst_restrict restrict_subst singletonD subst_domain_restrict_subst_domain)
  next
    case False
    then show ?thesis unfolding range_vars_def subst_domain_def using False Var.prems(1) Var.prems(3) by simp
  qed 
  then show ?case using Var.prems(1) by force 
next
  case (Fun f ss)
  then show ?case unfolding range_vars_def subst_domain_def subst_restrict_def by auto 
      (smt (verit, del_insts) IntE IntI mem_Collect_eq subst_domain_def)
qed

(* Lemma 3.4 in MH94. The first version is the lifting lemma for ordinary terms. *)
lemma lifting_lemma:
  fixes V::"('v::infinite) set" and s::"('f, 'v)term" and t::"('f, 'v)term"
  assumes "normal_subst R \<theta>"
    and "t = s \<cdot> \<theta>"
    and "vars_term s \<union> subst_domain \<theta> \<subseteq> V"
    and rs:"(t,  t') \<in> (rstep R)\<^sup>*"
    and fv:"finite V"
  shows "\<exists>\<sigma> \<theta>' s'. narrowing_derivation s s' \<sigma> \<and> t' = s' \<cdot> \<theta>' \<and>
      normal_subst R \<theta>' \<and> (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V "
proof -
  from rs
  obtain f n where f0:"f 0 = t" and fn:"f n = t'" and rel_chain:"\<forall>i < n. (f i,  f (Suc i)) \<in> rstep R" 
    by (metis rtrancl_imp_seq)
  then have "\<exists>\<sigma> \<theta>' s'. narrowing_derivation_num s s' \<sigma> n \<and> t' = s' \<cdot> \<theta>' \<and> 
    normal_subst R \<theta>' \<and> (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V" using assms
  proof(induct n arbitrary: s t t' \<theta> f V rule: wf_induct[OF wf_measure [of "\<lambda> n. n"]])
    case (1 n)
    note IH1 = 1(1)[rule_format]
    then show ?case
    proof(cases "n = 0")
      case True
      show ?thesis
        by (rule exI[of _ Var], rule exI[of _ \<theta>], rule exI[of _ "s"], insert 1 True)
          (simp add: narrowing_derivation_num_def subst_rule_def relpow_fun_conv, force) 
    next
      case False
      hence f0f1:"(f 0, f 1) \<in> rstep R" using 1 by auto
      then show ?thesis
      proof -
        from f0f1 obtain C \<sigma> l r  where f0:"f 0 = C\<langle>l \<cdot> \<sigma>\<rangle>" and f1:"f 1 = C\<langle>r \<cdot> \<sigma>\<rangle>"
          and rl:"(l, r) \<in> R" by auto
        have norm\<theta>:"normal_subst R \<theta>" by fact
        have s\<theta>t:"s \<cdot> \<theta> = t" using f0 1 by auto
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
        have p:"?p \<in> poss s" 
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence pns:"?p \<notin> poss s" by simp
          hence pnfs:"?p \<notin> fun_poss s" using fun_poss_imp_poss by blast
          have sub_eq:"(s \<cdot> \<theta>) |_ ?p = l \<cdot> \<sigma>" using 1(2) f0p s\<theta>t by auto
          have ps\<theta>:"?p \<in> fun_poss (s \<cdot> \<theta>)" using 1(2) 1(7) pf0 using s\<theta>t by auto
          from poss_subst_apply_term[of ?p s \<theta>]
          obtain q r x where qpr:"?p = q @ r" and qs:"q \<in> poss s" and sqx:"s |_ q = Var x" and r:"r \<in> poss (\<theta> x)"
            using fun_poss_imp_poss pnfs ps\<theta> by blast
          hence *:"(s \<cdot> \<theta>) |_ ?p = (Var x) \<cdot> \<theta> |_ r" by force
          have "((Var x) \<cdot> \<theta>) \<in> NF (rstep R)" using norm\<theta> by (simp add: normal_subst_def)
              (metis NF_I NF_Var local.wf notin_subst_domain_imp_Var)
          hence "((Var x) \<cdot> \<theta> |_ r) \<in> NF (rstep R)" unfolding normal_subst_def using r
            by (metis NF_rstep_subterm eval_term.simps(1) subt_at_imp_supteq)
          then show False by (metis * NF_instance lhs_notin_NF_rstep rl sub_eq)
        qed
        hence pfun':"?p \<in> fun_poss (s \<cdot> \<theta>)" using p pp0 pf0 s\<theta>t f0p f0 \<open> f 0 = t\<close> \<open>is_Fun l\<close> norm\<theta>[unfolded normal_subst_def]
          by auto 
        have sub:"is_Fun s" by (metis 1(2) NF_E eval_term.simps(1) f0f1 is_Fun_Fun_conv is_VarE local.wf norm\<theta> 
              normal_subst_def notin_subst_domain_imp_Var rstep_imp_Fun s\<theta>t)
        hence pfun:"?p \<in> fun_poss s" using pfun' p  p norm\<theta>[unfolded normal_subst_def]
          by (smt (verit, ccfv_SIG) "1.prems"(1) NF_instance eval_term.simps(1) f0p fun_poss_fun_conv 
              is_Fun_Fun_conv is_Var_def lhs_notin_NF_rstep notin_subst_domain_imp_Var poss_is_Fun_fun_poss rl s\<theta>t subt_at_subst)
        hence vuS':"vars_term (s |_ ?p) \<subseteq> vars_term s"
        proof -
          from vars_term_subt_at[OF p]
          have "vars_term (s |_ ?p) \<subseteq> vars_term s" by auto
          then show ?thesis by auto
        qed
        with varempty' have varcond:"vars_term (s |_ ?p) \<inter> vars_rule (\<omega> \<bullet> (l, r)) = {}" using 1(7) by auto
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
        have sub_\<theta>:"subst_domain ?\<theta> \<subseteq> V" using 1(7) by auto
        have inter_empty:"subst_domain ?\<sigma>r \<inter> subst_domain ?\<theta> = {}" using varempty' sub_\<sigma>r sub_\<theta> by auto
        from  s\<theta>t f0p have *:"(s \<cdot> \<theta> |_ ?p) = fst (\<omega> \<bullet> (l, r)) \<cdot> \<sigma>r" using subeq
          by (simp add: 1(2) subst_rule_def)
        have varcond':"vars_term (s |_ ?p) \<inter> vars_term (\<omega> \<bullet> l) = {}" 
        proof -
          have "vars_term (\<omega> \<bullet> l) \<subseteq> vars_rule (\<omega> \<bullet> (l, r))" 
            by (metis fst_conv rule_pt.fst_eqvt sup_ge1 vars_rule_def)
          then show ?thesis using varcond by auto
        qed
        with norm\<theta> * have **:"(s |_ ?p) \<cdot> \<theta> = fst (\<omega> \<bullet> (l, r)) \<cdot> \<sigma>r" by (simp add: p)
        have sub_eq:"(s |_ ?p) \<cdot> ?\<theta> = (\<omega> \<bullet> l) \<cdot> ?\<sigma>r" using **
          by (metis 1(7) coincidence_lemma' fst_conv le_sup_iff rule_pt.permute_prod.simps subst_domain_neutral sup_ge1 vars_rule_def)
        from subst_union_sound[OF sub_eq]
        have subst_eq_\<theta>\<sigma>:"(s |_ ?p) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)  = (\<omega> \<bullet> l) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using inter_empty sub_\<sigma>r sub_\<theta> inter_empty 
          by (smt (verit, best) disjoint_iff fst_conv local.wf rl sub_comm sub_eq subsetD subst_union.elims 
              term_subst_eq_conv varcond' varempty' vars_rule_eqvt vars_rule_lhs vars_term_eqvt)
        then obtain \<delta> where mgu_uv:"mgu (s |_ ?p) (\<omega> \<bullet> l) = Some \<delta>" using mgu_ex 
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
        let ?s1 = "(replace_at s ?p (\<omega> \<bullet> r))\<cdot> \<delta>"
        have nar:"(s, ?s1, \<delta>) \<in> narrowing_step" unfolding subst_rule_def narrowing_step_def using  \<omega>r mgu_uv rl varempty' pfun by auto 
            (smt (verit, ccfv_threshold) 1(7) Int_assoc fst_conv inf.orderE inf_bot_right le_sup_iff narrowing_step.simps 
              narrowing_stepp_narrowing_step_eq rule_pt.fst_eqvt rule_pt.snd_eqvt snd_conv subst_apply_term_ctxt_apply_distrib)
        from narrowing_set_imp_rtran[OF nar]
        have condn1:"narrowing_derivation_num s ?s1 \<delta> 1" by auto
        let ?V = "(V - subst_domain \<delta>) \<union> range_vars \<delta>"
        let ?\<theta>1 = "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s ?V"
        have sub\<theta>1:"subst_domain ?\<theta>1 \<subseteq> ?V" unfolding subst_restrict_def 
          by (smt (verit, del_insts) mem_Collect_eq subset_eq subst_domain_def)
        have reseq:"?\<theta>1 |s ?V = (?\<theta> \<union>\<^sub>s ?\<sigma>r)|s ?V" 
          by (simp add: restrict_subst_domain_def)
        have reseq\<delta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1) |s V = (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r))|s V" 
          using r_subst_compose reseq by blast
        have reseq\<theta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1) |s V = \<theta> |s V " using \<delta> by auto (smt (verit, best) \<delta> disjoint_iff notin_subst_domain_imp_Var 
              reseq\<delta> restrict_subst restrict_subst_domain_def subst_domain_neutral subst_ext subst_union.elims varempty')
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
            have subst_x:"x \<in> vars_term (s |_ ?p) \<union> vars_term (\<omega> \<bullet> l)" using mgu_uv 
                asm mgu_range_vars by auto
            then show "x \<in> ?B"
            proof
              assume "x \<in> vars_term (s |_ ?p)"
              hence "x \<in> V - subst_domain \<delta>" using 1(7) xn\<delta> vuS' by auto
              then show ?thesis by auto
            next
              assume asm2:"x \<in> vars_term (\<omega> \<bullet> l)"
              hence xnu:"x \<notin> vars_term (s |_ ?p)" using varcond' by blast
              from vars_term_range[OF asm asm2 subst_range_disj\<delta>]
              have xv\<delta>:"x \<in> vars_term ((\<omega> \<bullet> l) \<cdot> \<delta>)" by auto
              have *:"x \<in> vars_term (s |_ ?p \<cdot> \<delta>)" using mgu_uv xv\<delta>
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu) 
              hence "vars_term ((\<omega> \<bullet> l) \<cdot> \<delta>) = vars_term (s |_ ?p \<cdot> \<delta>)" using mgu_uv 
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu)
              from subst_restricted_range_vars[OF * subst_range_disj\<delta> xnu asm]
              have "x \<in> range_vars (\<delta> |s vars_term (s |_ ?p))" by auto
              moreover have upV:"vars_term (s |_ ?p) \<subseteq> V" using 1(7) vuS' by auto
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
        have vars_s1:"vars_term ?s1 \<subseteq> ?V" 
        proof -
          have *:"vars_term (\<omega> \<bullet> r) \<subseteq> vars_term (\<omega> \<bullet> l)" using wf[unfolded wf_trs_def] 
            by (metis fst_eqD local.wf rl rule_pt.fst_eqvt rule_pt.snd_eqvt snd_eqD sup.orderI vars_rule_def 
                vars_rule_eqvt vars_rule_lhs vars_term_eqvt)
          from var_cond_stable[OF this]
          have "vars_term ((\<omega> \<bullet> r) \<cdot> \<delta> ) \<subseteq> vars_term ((\<omega> \<bullet> l) \<cdot> \<delta>)" by fastforce
          from replace_var_stable[OF this]
          have "vars_term ?s1 \<subseteq> vars_term (replace_at s ?p ((\<omega> \<bullet> l))\<cdot> \<delta>)" 
            by (meson * replace_var_stable var_cond_stable)
          moreover have "vars_term ((replace_at s ?p (\<omega> \<bullet> l))\<cdot> \<delta>) = vars_term (s \<cdot> \<delta>)"
            by (metis ctxt_supt_id mgu_uv p subst_apply_term_ctxt_apply_distrib subst_apply_term_eq_subst_apply_term_if_mgu)
          moreover have "vars_term (s \<cdot> \<delta>) \<subseteq> ?V" 
            by (smt (verit) 1(7) Un_Diff Un_iff subsetI subset_Un_eq vars_term_subst_apply_term_subset)
          ultimately show ?thesis by auto
        qed
        have rel_chain':"\<And>i. i < n - 1 \<Longrightarrow> (f (i + 1), f (Suc i + 1)) \<in> rstep R" using rel_chain 
          by (simp add: 1(4))
        let ?f = "\<lambda>i. f (i + 1)"
        have relstar:"(f 1, f n) \<in> (rstep R)\<^sup>*" using False 1(4) less_Suc_eq 
          by (induct n, blast, metis (no_types, lifting) One_nat_def rtrancl.simps)
        have "\<exists>\<delta>' \<theta>' s'. narrowing_derivation_num ?s1 s' \<delta>' (n - 1) \<and>  f n = s' \<cdot> \<theta>' \<and> normal_subst R \<theta>' \<and>
         (\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V"
        proof (rule IH1[of "n - 1"  ?f "f 1" "f n" ?\<theta>1 ?s1], goal_cases)
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
          have "f 1 = ?s1 \<cdot> ?\<theta>1"
          proof -
            have "f 1 = replace_at (s \<cdot> \<theta>) ?p ((\<omega> \<bullet> r) \<cdot> \<sigma>r)" using crl f1 s\<theta>t 
              by (metis 1(2) ctxt_of_pos_term_hole_pos f0) 
            also have "...  = replace_at (s \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)) ?p ((\<omega> \<bullet> r) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r))" 
              by (metis 1(7) \<theta>sv coincidence_lemma' crl sndeq sup.boundedE)
            also have "... = replace_at s ?p (\<omega> \<bullet> r) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" by (simp add: ctxt_of_pos_term_subst p)
            also have "... = replace_at s ?p (\<omega> \<bullet> r) \<cdot> (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r))" using \<delta> by auto
            also have "... = ?s1 \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)" by simp
            also have *:"f 1 = ?s1 \<cdot> ?\<theta>1" using vars_s1 using calculation subst_apply_term_restrict_subst_domain by fastforce
            finally show ?thesis using * by fastforce
          qed
          then show ?case by auto
        next
          case 7
          then show ?case using vars_s1 sub\<theta>1 by auto
        next
          case 8
          then show ?case using relstar by blast
        next
          case 9
          then show ?case by (metis 1(9) finite_Diff2 infinite_Un mgu_finite_range_vars mgu_finite_subst_domain mgu_uv)
        qed
        then obtain \<delta>' \<theta>' s' where condn2:"narrowing_derivation_num ?s1 s' \<delta>' (n - 1)" and sub\<theta>':"s'\<cdot> \<theta>' = f n"
          and norm\<theta>':"normal_subst R \<theta>'" and sub_rel:"(\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V" by auto
        from n0_narrowing_derivation_num have n1:"n = 1 \<Longrightarrow> s' = ?s1 \<and> \<delta>' = Var" 
          using False using condn2 by (metis diff_self_eq_0)
        from condn2 obtain g \<tau> where g0:"g 0 = ?s1" and gnm1:"g (n - 1) = s'"
          and gcond_chain:"\<forall>i < n - 1. ((g i), (g (Suc i)), (\<tau> i)) \<in> narrowing_step" and comp\<delta>':"if n = 1 then \<delta>' = Var 
          else \<delta>' = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (n - 1)])" using False n1 unfolding narrowing_derivation_num_def by auto
        let ?g = "\<lambda>i. if i = 0 then s else g (i - 1)"
        let ?\<tau> = "\<lambda>i. if i = 0 then \<delta> else \<tau> (i - 1)"
        have "\<delta>' = compose (map ?\<tau> [1..< n])" 
          by (smt (verit) One_nat_def comp\<delta>' add_diff_cancel_left' add_diff_inverse_nat compose_simps(1) diff_zero length_upt 
              less_Suc_eq_0_disj list.simps(8) map_equality_iff nth_upt plus_1_eq_Suc upt_eq_Nil_conv)      
        hence \<delta>\<delta>'comp:"\<delta> \<circ>\<^sub>s \<delta>' = compose (map ?\<tau> [0..< n])" using False upt_conv_Cons by fastforce
        have condn:"narrowing_derivation_num s s' (\<delta> \<circ>\<^sub>s \<delta>') n" 
        proof -
          have "(\<exists>f. f 0 = s \<and> f n = s' \<and> (\<exists>\<tau>. (\<forall>i<n. (f i, f (Suc i), \<tau> i) \<in> narrowing_step) \<and>
            \<delta> \<circ>\<^sub>s \<delta>' = compose (map \<tau> [0..<n])))" 
            by (rule exI[of _ ?g], insert \<delta>\<delta>'comp False One_nat_def gnm1) (smt (verit, ccfv_SIG) Suc_pred gcond_chain 
                bot_nat_0.not_eq_extremum diff_Suc_1 g0 less_nat_zero_code nar not_less_eq)
          then show ?thesis 
            by (simp add: narrowing_derivation_num_def False local.wf)
        qed
        show ?thesis
        proof(rule exI[of _ "\<delta> \<circ>\<^sub>s \<delta>'"], intro exI[of _ \<theta>'] exI[of _ s'] conjI, goal_cases)
          case 1
          then show ?case using condn by auto
        next
          case 2
          then show ?case using 1(3) sub\<theta>' by auto
        next
          case 3
          then show ?case using norm\<theta>' by auto
        next
          case 4
          then show ?case using norm\<theta>' 
            by (metis order_refl r_subst_compose reseq\<theta> sub_rel subst_monoid_mult.mult_assoc)
        qed
      qed
    qed
  qed
  then show ?thesis using narrowing_deriv_implication by blast
qed

end
end
