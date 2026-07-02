(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2024)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Formalization of conditional narrowing, lifting lemma, etc.\<close>

theory Conditional_Narrowing
  imports
    Narrowing
    Equational_Narrowing
    CTRS.Conditional_Rewriting
    CTRS.Quasi_Decreasingness
    TRS.More_Abstract_Rewriting
    First_Order_Terms.Term_More
begin

(* An equation s \<approx> t is converted into the equation-term \<doteq>(s, t). 
  Also, the rewrite rule "\<doteq>(x, x) \<longrightarrow> \<top>" is added to the rewrite system. *)

definition type1 :: "('f, 'v) ctrs \<Rightarrow> bool"
  where
    "type1 R \<longleftrightarrow> (\<forall> \<rho> \<in> R. vars_term (crhs \<rho>) \<union> vars_trs (set (snd \<rho>)) \<subseteq> (vars_term (clhs \<rho>)))"

definition wf_1ctrs :: "('f, 'v) ctrs \<Rightarrow> bool"
  where
    "wf_1ctrs R \<longleftrightarrow> (\<forall>((l, r), cs) \<in> R. is_Fun l) \<and> type1 R "

locale conditional_narrowing = additional_narrowing_symbols DOTEQ TOP 
  for DOTEQ :: 'f ("\<doteq>")
    and TOP :: "'f" ("\<top>") +
  fixes R' :: "('f, 'v:: infinite) ctrs"
    and R :: "('f, 'v:: infinite) ctrs"
    and F :: "'f sig"
    and D :: "'f sig"
  assumes wf: "wf_1ctrs R"
    (* Add the (conditional) rewrite rule  x \<doteq> x \<longrightarrow> \<top> *)
    and R':"R = R' \<union> {((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []), [])}"
    and R_sig: "funas_ctrs R' \<subseteq> F"
    and D:"D = {(\<doteq>, 2),(\<top>, 0)}" 
    (* The special symbols (\<doteq>, 2) and (\<top>, 0) should be distinct from the original signature *)
    and D_fresh:"D \<inter> F = {}"
    (* Any substitution does not introduce the special symbols \<doteq> and \<top> *)
    and wf_eq_subst:"\<forall>(\<theta>::('f, 'v:: infinite)subst) t::('f, 'v:: infinite)term. wf_equational_term t \<longrightarrow> wf_equational_term (t \<cdot> \<theta>)"
    and wf_F_subst:"\<forall>t (\<theta>::('f, 'v)subst). funas_term t \<subseteq> F \<longrightarrow> funas_term (t \<cdot> \<theta>) \<subseteq> F"
    (* Any substitution has a finite substitution domain because only finite terms are considered.*)
    and finite_subst_domain:"\<forall>(\<theta>::('f, 'v)subst). finite (subst_domain \<theta>)"
    (* The additional rule {((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []), [])} should not be applied to
        terms with symbols in the original signature. *)
    and funas_term_restrict: "funas_term s \<subseteq> F \<Longrightarrow> (s, t) \<in> cstep R \<Longrightarrow> (s, t) \<in> cstep R'"
begin

definition subst_condition_list :: "('f, 'v) subst \<Rightarrow> ('f, 'v) condition list \<Rightarrow> ('f, 'v) condition list" where 
  "subst_condition_list \<sigma> xs = map (\<lambda>p.  subst_equation \<sigma> p) xs"

fun convert_cond_into_term_multiset:: "('f, 'v) rule list \<Rightarrow> ('f, 'v) term multiset"
  where 
    "convert_cond_into_term_multiset [] = {#}"
  | "convert_cond_into_term_multiset xs = {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset xs #}"

definition vars_seq::"('f, 'v) rule list \<Rightarrow> 'v set" where
  "vars_seq S = \<Union> (set (map (vars_rule) S))"

(* Definition 6.7 in MH94 *)
inductive_set cond_reduction_step::"(('f, 'v) term multiset) rel" ("\<Zinj>" 50)
  where 
    "(s \<in># S \<and> T = ((S - {#s#}) + {#replace_at s p ((crhs rl) \<cdot> \<sigma>)#} + (subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl)))) \<and> 
    rl \<in> R \<and>  p \<in> fun_poss s \<and> (s |_ p = (clhs rl) \<cdot> \<sigma>) \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set (snd rl). (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*)) \<Longrightarrow> (S, T) \<in> cond_reduction_step"

inductive_set cond_reduction_cstep::"(('f, 'v) term multiset) rel" 
  where 
    "s \<in># S \<and> T = ((S - {#s#}) + {#t#}) \<and> (s, t) \<in> cstep R \<Longrightarrow> (S, T) \<in> cond_reduction_cstep"

lemmas cond_reduction_stepI = cond_reduction_step.intros [intro]
lemmas cond_reduction_stepE = cond_reduction_step.cases [elim]

(* Definition 6.3 in MH94 *)
inductive_set cond_narrowing_step::"(('f, 'v) term multiset \<times> ('f, 'v) term multiset \<times> ('f, 'v) subst) set"  ("\<leadsto>\<^sub>c" 50)
  where
    "(s \<in># S \<and> T = subst_term_multiset \<delta> ((S - {#s#}) + {#replace_at s p (crhs rl)#} + convert_cond_into_term_multiset (snd rl)) \<and>  
         \<omega> \<bullet> rl \<in> R \<and> (vars_term_set (set_mset S) \<inter> vars_crule rl = {}) \<and> p \<in> fun_poss s \<and> mgu (s |_ p) (clhs rl) = Some \<delta>)
      \<Longrightarrow> (S, T, \<delta>) \<in> cond_narrowing_step"

lemmas cond_narrowing_stepI = cond_narrowing_step.intros [intro]
lemmas cond_narrowing_stepE = cond_narrowing_step.cases [elim]

definition cond_narrowing_step'::"(('f, 'v) term multiset) rel" where 
  "cond_narrowing_step' = {(S, T) | S T \<sigma>. (S, T, \<sigma>) \<in> cond_narrowing_step}"

definition cond_narrowing_derivation :: "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "cond_narrowing_derivation S S' \<sigma> \<longleftrightarrow> (\<exists>n. (S,  S') \<in> (cond_narrowing_step')^^n \<and> (\<exists>f \<tau>. f 0 = S \<and> f n = S' \<and> 
  (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> cond_narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

definition cond_narrowing_derivation_num :: "('f, 'v) term multiset \<Rightarrow> ('f, 'v) term multiset \<Rightarrow> ('f, 'v) subst \<Rightarrow> nat \<Rightarrow> bool" where
  "cond_narrowing_derivation_num S S' \<sigma> n \<longleftrightarrow> ((S,  S') \<in> (cond_narrowing_step')^^n \<and> (\<exists>f \<tau>. f 0 = S \<and> f n = S' \<and> 
  (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> cond_narrowing_step) \<and> (if n = 0 then \<sigma> = Var else \<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< n]))))"

lemma n0_cond_narrowing_derivation_num:"cond_narrowing_derivation_num S S' \<sigma> 0 \<Longrightarrow> S = S' \<and> \<sigma> = Var" 
  unfolding cond_narrowing_derivation_num_def by auto

lemma cond_narrowing_deriv_implication: assumes "cond_narrowing_derivation_num S S' \<sigma> n"
  shows "cond_narrowing_derivation S S' \<sigma>" 
  unfolding cond_narrowing_derivation_num_def cond_narrowing_derivation_def 
  using assms cond_narrowing_derivation_num_def by metis

lemma normalized_subst_union:
  assumes \<alpha>:"normalized R \<alpha>"
    and \<beta>:"normalized R \<beta>"
  shows "normalized R (\<alpha> \<union>\<^sub>s \<beta>)" using assms unfolding normalized_def by simp

lemma cond_narrowing_set_imp_rtran: assumes "(S, T, \<sigma>) \<in> cond_narrowing_step"
  shows "cond_narrowing_derivation_num S T \<sigma> 1"
proof -
  have *:"(S, T) \<in> cond_narrowing_step'" using assms 
    using cond_narrowing_step'_def by auto
  then obtain f where f0:"f 0 = S" and f1:"f 1 = T" and rel_chain:"(f 0,  f (Suc 0)) \<in> cond_narrowing_step'" 
    by (metis One_nat_def relpow_0_I relpow_Suc_I relpow_fun_conv)
  let ?\<tau> = "\<lambda>i. (if i = 0 then \<sigma> else Var)"
  show ?thesis  unfolding cond_narrowing_derivation_num_def
  proof(intro conjI, goal_cases)
    case 1
    then show ?case by (simp add: *)
  next
    case 2
    then show ?case by (rule exI[of _ f], rule exI[of _ ?\<tau>], insert assms f0 f1, auto)
  qed
qed

lemma normalized_perm: assumes norm:"normalized R \<sigma>"
  and equiv:"\<forall>x. \<sigma> x = \<sigma>r (\<omega> \<bullet> x)"
shows "normalized R \<sigma>r" 
proof -
  from norm have "\<forall>x. \<sigma> (-\<omega> \<bullet> x) \<in> NF (cstep R)"
    by (simp add: normalized_def)
  moreover have "\<forall>x. \<sigma> (\<omega> \<bullet> -\<omega> \<bullet> x) \<in> NF (cstep R)" 
    by (meson norm normalized_def)
  moreover have "\<forall>x. \<sigma> (-\<omega> \<bullet> x) = \<sigma>r (\<omega> \<bullet> -\<omega> \<bullet> x)" using equiv by simp
  moreover have "\<forall>x. \<sigma>r (\<omega> \<bullet> -\<omega> \<bullet> x) = \<sigma>r x" by simp
  ultimately show ?thesis 
    by (simp add: normalized_def)
qed

lemma vars_seq_term_set_equiv: "vars_trs (set xs) = vars_term_set (set_mset (convert_cond_into_term_multiset xs))" 
proof(induct xs)
  case Nil
  then show ?case unfolding vars_trs_def vars_term_set_def by simp
next
  case (Cons x xs)
  then obtain u v where pair:"x = (u, v)" by fastforce
  have "convert_cond_into_term_multiset [(u, v)] = {#Fun (\<doteq>) [u, v]#}" by simp
  moreover have "vars_term (Fun (\<doteq>) [u, v]) = vars_term u \<union> vars_term v" by auto
  moreover have "vars_term_set (set_mset (convert_cond_into_term_multiset [(u, v)])) = vars_term u \<union> vars_term v" 
    by (simp add: vars_term_set_def)
  moreover have "vars_trs (set [(u, v)]) = vars_term_set (set_mset (convert_cond_into_term_multiset [(u, v)]))" 
    unfolding vars_trs_def vars_term_set_def 
    using pair by (simp add: vars_rule_def)
  ultimately show ?case 
  proof (auto split:prod.splits, goal_cases)
    case (1 x1 x2 x)
    then show ?case using pair unfolding vars_trs_def vars_term_set_def vars_rule_def  
      by (auto split:prod.splits) 
  next
    case (2 x1 x2 x)
    then show ?case using pair unfolding vars_trs_def vars_term_set_def vars_rule_def  
      by (auto split:prod.splits, fastforce, auto)
  qed 
qed

lemma subst_term_multiset_perm_conv_main: fixes xs::"('f, 'v)rule list"
  shows "{#t \<cdot> sop \<omega>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset xs#}#} = 
    {#Fun \<doteq> [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #}"
proof -
  have "{#t \<cdot> sop \<omega>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset xs#}#} = 
          {# (Fun \<doteq> [u, v]) \<cdot> sop \<omega>. (u, v) \<in># mset xs #}"
  proof(auto split:prod.splits, induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case by (auto split:prod.splits)
  qed
  also have "... = {#Fun \<doteq> [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #}"
  proof(auto split:prod.splits, induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case by (auto split:prod.splits simp add: rule_pt.permute_prod.simps ) 
  qed
  finally show ?thesis by auto
qed

lemma subst_term_multiset_perm_conv_pre: fixes xs::"('f, 'v)rule list"
  shows "{# (t \<cdot> \<theta>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (xs) #}#} = 
  {# (t \<cdot> (sop \<omega> \<circ>\<^sub>s \<theta>)). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> xs) #} #}"
proof -
  let ?M = "{# Fun (\<doteq>) [u, v]. (u, v) \<in># mset xs #}"
  let ?Q = "{# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> xs) #}"
  have "?Q = subst_term_multiset (sop (- \<omega>)) ?M"
  proof -
    have "{#Fun \<doteq> [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> xs) #} = {#t \<cdot> sop (- \<omega>). t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset xs#}#}" 
      using subst_term_multiset_perm_conv_main by metis 
    then show ?thesis 
      by (simp add: subst_term_multiset_def)
  qed
  then show ?thesis
    by (smt (verit) comp_apply multiset.map_comp multiset.map_cong0 subst_subst_compose 
        subst_term_multiset_def term_apply_subst_Var_Rep_perm term_pt.permute_minus_cancel(1))
qed

lemma subst_term_multiset_perm_conv: fixes xs::"('f, 'v)rule list"
  assumes "\<theta> = sop \<omega> \<circ>\<^sub>s \<sigma>"
  shows "subst_term_multiset \<sigma> {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #} = subst_term_multiset \<theta> {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset xs #}"
proof -
  have \<sigma>:"\<sigma> = sop (- \<omega>) \<circ>\<^sub>s \<theta>" using assms  
    by (metis permute_subst_subst_compose subst_compose_o_assoc subst_monoid_mult.mult.left_neutral subst_pt.permute_minus_cancel(2))
  have "subst_term_multiset \<sigma> {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #} = {# (t \<cdot> \<sigma>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #} #}"
    unfolding subst_term_multiset_def by auto
  also have "... = {# (t \<cdot> sop (- \<omega>) \<circ>\<^sub>s \<theta>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (\<omega> \<bullet> xs) #} #}" using \<sigma> by force
  also have "... = {# (t \<cdot> sop \<omega> \<circ>\<^sub>s sop (- \<omega>) \<circ>\<^sub>s \<theta>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> \<omega> \<bullet> xs) #} #}" 
    using \<sigma> subst_term_multiset_perm_conv_pre 
    by (metis subst_compose_assoc)
  also have "... = {# (t \<cdot>  \<theta>). t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (- \<omega> \<bullet> \<omega> \<bullet> xs) #} #}" by auto
  finally show ?thesis by (simp add: subst_term_multiset_def)
qed

lemma subst_subtract_term_multiset: assumes "subst_domain \<sigma> \<subseteq> vars_term_set (set_mset S)"
  and "u \<in># S"
shows "subst_term_multiset \<sigma> (S - {#u#}) = subst_term_multiset \<sigma> S - subst_term_multiset \<sigma> {#u#}" 
proof -
  have "subst_term_multiset \<sigma> (S - {#u#}) \<subseteq># subst_term_multiset \<sigma> S - subst_term_multiset \<sigma> {#u#}"
    unfolding subst_term_multiset_def using assms 
    by (simp add: image_mset_Diff)
  moreover have "subst_term_multiset \<sigma> S - subst_term_multiset \<sigma> {#u#} \<subseteq># subst_term_multiset \<sigma> (S - {#u#})"
    unfolding subst_term_set_def using assms
    by (simp add: image_mset_Diff subst_term_multiset_def)
  ultimately show ?thesis by simp
qed

lemma subst_term_multiset_union: "subst_term_multiset \<sigma> (M + N) = subst_term_multiset \<sigma> M + subst_term_multiset \<sigma> N" 
  unfolding subst_term_multiset_def by simp

lemma var_set_conv_inv:"vars_term_set (set_mset (convert_cond_into_term_multiset xs )) = vars_trs (set xs)" 
  using vars_defs(1) vars_seq_def vars_seq_term_set_equiv by fastforce

lemma cond_nar_vars_finite: assumes "cond_narrowing_derivation_num S S' \<sigma> n"
  and "finite (vars_term_set (set_mset S))"
shows "finite (vars_term_set (set_mset S'))" using assms
proof( induct n arbitrary: S' \<sigma>)
  case 0
  then show ?case 
    using n0_cond_narrowing_derivation_num by auto
next
  case (Suc n)
  from Suc have "cond_narrowing_derivation_num S S' \<sigma> (Suc n)" by auto
  hence SS':"(S,  S') \<in> (cond_narrowing_step')^^(Suc n)" and relchain':"(\<exists>f \<tau>. f 0 = S \<and> f (Suc n) = S' \<and> 
    (\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> cond_narrowing_step) \<and> (\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (Suc n)])))"
    unfolding cond_narrowing_derivation_num_def by auto
  from relchain' obtain f \<tau> where f0:"f 0 = S" and fsucn:"f (Suc n) = S'" and 
    relchain:"\<forall>i < (Suc n). ((f i), (f (Suc i)), (\<tau> i)) \<in> cond_narrowing_step" 
    and \<sigma>:"(\<sigma> = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (Suc n)]))" by auto
  let ?\<tau> = "compose (map (\<lambda>i. (\<tau> i)) [0 ..< n])"
  let ?\<sigma> = "if n = 0 then Var else ?\<tau>"
  let ?f = "\<lambda>i. (if i \<le> n then f i else undefined)"
  from relchain obtain U where U:"f n = U" by simp
  from relchain have nchain:"\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> cond_narrowing_step" by simp
  hence f0fn:"(f 0, f n) \<in> (cond_narrowing_step')^^n" unfolding cond_narrowing_step'_def 
    by (smt (verit, del_insts) mem_Collect_eq relpow_fun_conv)
  have "(S,  U) \<in> (cond_narrowing_step')^^n" using f0 U f0fn by auto
  moreover have "(\<exists>f \<tau>. f 0 = S \<and> f n = U \<and> (\<forall>i < n. ((f i), (f (Suc i)), (\<tau> i)) \<in> cond_narrowing_step))"
    by (rule exI[of _ "?f"] rule exI[of _ "?\<sigma>"], insert U f0 nchain, auto)
  moreover have "cond_narrowing_derivation_num S U ?\<sigma> n" unfolding cond_narrowing_derivation_num_def
    using U calculation f0 nchain by auto 
  ultimately have finiteU:"finite (vars_term_set (set_mset U))" using Suc by auto
  have "\<exists>\<delta>. (U, S', \<delta>) \<in> cond_narrowing_step" using relchain fsucn U by auto
  then obtain \<delta> where "(U, S', \<delta>) \<in> cond_narrowing_step" by auto
  then obtain s rl \<omega> p where "s \<in># U" and S'eq:"S' = subst_term_multiset \<delta> ((U - {#s#}) + {#replace_at s p (crhs rl)#} + convert_cond_into_term_multiset (snd rl))"
    and "\<omega> \<bullet> rl \<in> R" and "(vars_term_set (set_mset U) \<inter> vars_crule rl = {})" and "p \<in> fun_poss s" and  mgu:"mgu (s |_ p) (clhs rl) = Some \<delta>" by auto
  from S'eq have *:"S' = subst_term_multiset \<delta> (U - {#s#}) + subst_term_multiset \<delta> {#replace_at s p (crhs rl)#} + 
    subst_term_multiset \<delta> (convert_cond_into_term_multiset (snd rl))" (is "S' = ?A + ?B + ?C")
    by (metis subst_term_multiset_union)
  have "vars_term_set (set_mset S') = vars_term_set (set_mset ?A) \<union> vars_term_set (set_mset ?B) \<union> vars_term_set (set_mset ?C)"
    unfolding vars_term_set_def using "*" by auto
  moreover have "finite (vars_term_set (set_mset ?A))" 
    unfolding vars_term_set_def using finiteU mgu_finite_range_vars[OF mgu] finite_vars_term by blast
  moreover have "finite (vars_term_set (set_mset ?B))" unfolding vars_term_set_def by simp
  moreover have "finite (vars_term_set (set_mset ?C))" unfolding vars_term_set_def by simp
  ultimately show ?case using * by auto
qed

lemma wf_eq_mset_subst_inv: fixes \<theta>:: "('f, 'v) subst"
  assumes "wf_equational_term_mset M"
  shows "wf_equational_term_mset (subst_term_multiset \<theta> M)" 
proof -
  let ?M = "subst_term_multiset \<theta> M"
  from assms have "(\<forall>t \<in># M. wf_equational_term t)" unfolding wf_equational_term_mset_def by simp
  moreover have "?M = {# (t \<cdot> \<theta>). t \<in># M #}" unfolding subst_term_multiset_def by auto
  moreover have "\<forall>s \<in># M. wf_equational_term s" by (simp add: calculation)
  then show ?thesis unfolding subst_term_multiset_def wf_equational_term_mset_def 
    using wf_eq_subst by auto
qed

lemma funas_crule_included_ctrs: assumes "rl \<in> R'"
  shows "funas_crule rl \<subseteq> funas_ctrs R'" unfolding funas_rule_def funas_ctrs_def 
  by (simp add: Union_upper assms)

lemma convert_cond_into_rule_list_sound: fixes rl::"('f, 'v) rule list"
  assumes "funas_trs (set rl) \<subseteq> F"
  shows "wf_equational_term_mset (convert_cond_into_term_multiset rl)" 
proof(cases "rl = []")
  case True
  then show ?thesis 
    by (simp add: wf_equational_term_def wf_equational_term_mset_def)
next
  case False
  have "funas_trs (set rl) \<subseteq> F" 
    unfolding funas_trs_def using assms funas_trs_def by blast
  moreover have *:"(\<doteq>, 2) \<notin> funas_trs (set rl) \<and> (\<top>, 0) \<notin> funas_trs (set rl)"
    using D D_fresh calculation by auto
  let ?C = "convert_cond_into_term_multiset rl"
  have "\<forall>t \<in># ?C. \<exists>(u::('f, 'v)term) v::('f, 'v)term. t = Fun (\<doteq>) [u, v] \<and> (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v \<and>
     (\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v"
  proof
    fix t
    assume "t \<in># ?C"
    hence "t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset rl #}" 
      using False by (smt (verit, ccfv_threshold) convert_cond_into_term_multiset.simps(2) list.exhaust)
    then obtain u v where t:"t = Fun (\<doteq>) [u, v]" and uv:"(u, v) \<in># mset rl" by auto
    have "(\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v" using * uv lhs_wf rhs_wf by fastforce
    moreover have "(\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v" using * uv lhs_wf rhs_wf by fastforce
    ultimately show "\<exists> u v. t = Fun (\<doteq>) [u, v] \<and> (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v \<and>
       (\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v" using t by auto
  qed  
  then show ?thesis by (simp add: wf_equational_term_def wf_equational_term_mset_def) 
qed

lemma convert_cond_into_term_multiset_sound: fixes rl::"('f, 'v) crule"
  assumes "rl \<in> R"
  shows "wf_equational_term_mset (convert_cond_into_term_multiset (snd rl))"
proof(cases "snd rl = []")
  case True
  then show ?thesis 
    by (simp add: wf_equational_term_def wf_equational_term_mset_def)
next
  case False
  have rl:"rl \<in> R'" using R' assms using False by fastforce
  moreover have "funas_ctrs R' \<subseteq> F" using R_sig by simp
  moreover have "funas_crule rl \<subseteq> funas_ctrs R'" 
    by (simp add: funas_crule_included_ctrs[OF rl])
  moreover have "funas_crule rl \<subseteq> F" using R_sig calculation(3) by auto
  moreover have "funas_trs (set (snd rl)) \<subseteq> F" 
    unfolding funas_trs_def funas_crule_def 
    by (metis Un_subset_iff calculation(4) funas_crule_def funas_trs_def)
  ultimately show ?thesis using convert_cond_into_rule_list_sound by auto
qed

lemma perm_empty_cond:assumes "(\<omega> \<bullet> rl) \<in> R"
  shows "snd rl = [] \<longleftrightarrow> (\<omega> \<bullet> (snd rl)) = []" by auto

lemma wf_equational_term_mset_add: assumes "wf_equational_term_mset A" and "wf_equational_term_mset B"
  shows "wf_equational_term_mset (A + B)" using assms
  using wf_equational_term_mset_def by (metis union_iff)

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

lemma funas_crule_perm: fixes S::"'f sig"
  assumes "funas_crule rl \<subseteq> S"
  shows "funas_crule (\<omega> \<bullet> rl) \<subseteq> S"
proof -
  have "funas_rule (fst rl) \<subseteq> S" using assms unfolding funas_crule_def by auto
  hence *:"funas_rule (fst (\<omega> \<bullet> rl)) \<subseteq> S" using funas_rule_perm by (metis crule_pt.fst_eqvt)
  have "funas_trs (set (snd rl)) \<subseteq> S" using assms unfolding funas_crule_def by auto
  hence **:"funas_trs (set (snd (\<omega> \<bullet> rl))) \<subseteq> S" using funas_trs_perm
    by (metis crule_pt.snd_eqvt permute_conds_set)    
  then show ?thesis using * ** by (simp add: funas_crule_def)
qed

lemma sop_perm_equiv:" (\<omega> \<bullet> rl) \<cdot> ((sop (- \<omega>) \<circ>\<^sub>s sop \<omega>')::('f, 'v) subst) = (\<omega>' \<bullet> rl)" 
  by (simp add: rule_pt.fst_eqvt)

lemma subst_equation_perm: "subst_equation ((sop (- \<omega>) \<circ>\<^sub>s sop \<omega>')::('f, 'v) subst) (\<omega> \<bullet> rl) =
  (\<omega>' \<bullet> rl)" using sop_perm_equiv unfolding subst_equation_def
  by (simp add: rule_pt.fst_eqvt rule_pt.snd_eqvt)

lemma root_perm_inv: "root t = root (\<omega> \<bullet> t)" by (induct t, auto)

lemma root_symbol_in_funas: assumes "root t = Some (f, n)"
  shows "(f, n) \<in> funas_term t" using assms by (induct t, auto) 

lemma root_special_notin_F: assumes "root t = Some (\<doteq>, 2) \<or> root t = Some (\<top>, 0)"
  shows "\<not> funas_term t \<subseteq> F" using root_symbol_in_funas D assms D_fresh 
  by (auto simp add: root_symbol_in_funas subset_iff, fastforce+) 

lemma fun_root_not_None:"is_Fun t \<Longrightarrow> root t \<noteq> None" by (induct t, auto)

lemma root_not_special_symbols: assumes "rl \<in> R'"
  and "funas_crule rl \<subseteq> F"
  and rnone:"root (clhs rl) \<noteq> None"
shows "root (clhs rl) \<noteq> Some (\<doteq>, 2) \<and> root (clhs rl) \<noteq> Some (\<top>, 0)" 
  using assms root_special_notin_F unfolding funas_crule_def D D_fresh R_sig 
    funas_rule_def funas_trs_def by auto

lemma root_subst_inv: fixes \<theta>::"('f, 'v)subst"
  assumes "p \<in> fun_poss u"
  shows "root(u |_ p \<cdot> \<theta>) = root(u |_ p)" using assms
  by (induct "u |_ p", insert fun_poss_fun_conv, fastforce+)

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
      by (metis UnCI UnE wf_s[unfolded wf_equational_term_def] asm ctxt_supt_id funas_term_ctxt_apply insert_disjoint(1) list.inject s snF sup.orderE term.inject(2))
    then show ?thesis using assms s nv unfolding wf_s[unfolded wf_equational_term_def] 
      using calculation wf_equational_term_def by (simp add: wf_equational_term_def)
  next
    assume asm:?B
    hence "replace_at s p t = Fun \<doteq> [u , (replace_at v r t)]" using s by auto
    moreover have "(\<doteq>, 2) \<notin> funas_term (replace_at v r t)" using D D_fresh qpos ft nv  
      by (smt (verit) UnCI UnE asm ctxt_supt_id funas_term_ctxt_apply insert_disjoint(1) subset_iff)
    moreover have "(\<top>, 0) \<notin> funas_term (replace_at v r t)" using D D_fresh qpos ft nv 
      by (metis UnCI UnE wf_s[unfolded wf_equational_term_def] asm ctxt_supt_id funas_term_ctxt_apply 
          insert_disjoint(1) list.inject s snF sup.orderE term.inject(2))
    then show ?thesis using assms s nu unfolding wf_s[unfolded wf_equational_term_def] 
      using calculation wf_equational_term_def by (metis nth_Cons_0 term.sel(4))
  qed
qed

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

lemma restricted_normalized: fixes A::"('v::infinite) set" and B::"('v::infinite) set" and \<sigma> \<theta> \<theta>'::"('f, 'v)subst"
  assumes "normalized R (\<theta> |s A)"
    and "(\<sigma> \<circ>\<^sub>s \<theta>') |s A  = \<theta> |s A"
    and B:"B \<subseteq> (A - subst_domain \<sigma>) \<union> range_vars (\<sigma> |s A)"
  shows "normalized R (\<theta>' |s B)" using assms
proof -
  { fix x
    assume "x \<in> B"
    with B have "x \<in> (A - subst_domain \<sigma>) \<or> x \<in> range_vars (\<sigma> |s A)" by auto
    hence "(\<theta>' x) \<in> NF (cstep R)" 
    proof 
      assume asm:"x \<in> (A - subst_domain \<sigma>)"
      hence "\<theta>' x = (\<sigma> \<circ>\<^sub>s \<theta>') x" 
        by (metis DiffD2 eval_term.simps(1) notin_subst_domain_imp_Var subst_compose_def)
      also have "... = \<theta> x" 
        by (metis Diff_iff asm assms(2) in_subst_restrict)
      then show "(\<theta>' x) \<in> NF (cstep R)"
        by (metis Diff_iff asm assms(1) calculation in_subst_restrict normalized_def)
    next
      assume "x \<in> range_vars (\<sigma> |s A)"
      hence "\<exists>y \<in> A. x \<in> vars_term (\<sigma> y)" unfolding range_vars_def subst_domain_def by auto
          (metis IntE in_subst_restrict restrict_subst subst_domain_restrict_subst_domain)
      then obtain y where y:"y \<in> A" and x:"x \<in> vars_term (\<sigma> y)" by auto
      hence *:"(\<sigma> \<circ>\<^sub>s \<theta>') y = \<theta> y" by (metis assms(2) in_subst_restrict)
      from subst_app_subterm have "\<theta>' x \<unlhd> (\<sigma> y) \<cdot> \<theta>'" using x by auto
      moreover have "\<theta> y \<in> NF (cstep R)" 
        by (metis assms(1) in_subst_restrict normalized_def y)
      ultimately show "(\<theta>' x) \<in> NF (cstep R)"
        by (metis NF_cstep_subterm * subst_compose_def)
    qed
  } then show ?thesis unfolding subst_restrict_def normalized_def by auto
      (metis NF_iff_no_step assms(1) cstep_subst eval_term.simps(1) normalized_def) 
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

lemma vars_cond_perm:"vars_trs (trs) \<subseteq> vars_term t \<Longrightarrow> vars_trs (\<omega> \<bullet> trs) \<subseteq> vars_term (\<omega> \<bullet> t)"
  unfolding vars_trs_def vars_rule_def by auto (smt (verit, ccfv_threshold) SUP_le_iff atom_set_pt.subset_eqvt 
      fst_conv le_supE rule_pt.fst_eqvt subsetD term_pt.permute_minus_cancel(1) trs_pt.eq_eqvt trs_pt.inv_mem_simps(1) 
      vars_term_eqvt, smt (verit, ccfv_threshold) SUP_le_iff atom_set_pt.subset_eqvt le_supE rule_pt.snd_eqvt 
      snd_conv subsetD term_pt.permute_minus_cancel(1) trs_pt.eq_eqvt trs_pt.inv_mem_simps(1) vars_term_eqvt)

(* Lemma 6.11 in MH94 *)
lemma conditional_lifting_lemma:
  fixes V::"('v::infinite) set" and S::"('f, 'v)term multiset" and T::"('f, 'v)term multiset"
  assumes "normalized R \<theta>"
    and "wf_equational_term_mset S"
    and "T = subst_term_multiset \<theta> S"
    and "vars_term_set (set_mset S) \<union> subst_domain \<theta> \<subseteq> V"
    and cr:"(T,  T') \<in> (cond_reduction_step)\<^sup>*"
    and fv:"finite V"
  shows "\<exists>\<sigma> \<theta>' S'. cond_narrowing_derivation S S' \<sigma> \<and> T' = subst_term_multiset \<theta>' S' \<and> wf_equational_term_mset S' \<and>
      normalized R \<theta>' \<and> (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V" 
proof -
  from cr obtain f n where f0:"f 0 = T" and fn:"f n = T'" and rel_chain:"\<forall>i < n. (f i,  f (Suc i)) \<in> cond_reduction_step" 
    by (metis rtrancl_imp_seq)
  then have "\<exists>\<sigma> \<theta>' S'. cond_narrowing_derivation_num S S' \<sigma> n \<and> subst_term_multiset \<theta>' S' = T' \<and> normalized R \<theta>' \<and> wf_equational_term_mset S' \<and>
    (\<sigma> \<circ>\<^sub>s \<theta>') |s V = \<theta> |s V \<and> finite V" using assms
  proof(induct n arbitrary: S T T' \<theta> f V rule: wf_induct[OF wf_measure [of "\<lambda> n. n"]])
    case (1 n)
    note IH1 = 1(1)[rule_format]
    then show ?case
    proof(cases "n = 0")
      case True
      show ?thesis by (rule exI[of _ Var], rule exI[of _ \<theta>], rule exI[of _ S], 
            simp add:cond_narrowing_derivation_num_def, insert True 1, auto)
    next
      case False
      hence f0f1:"(f 0, f 1) \<in> cond_reduction_step" using 1 by auto
      then show ?thesis
      proof -
        from f0f1 obtain T T1 s \<sigma> rl p  where f0:"f 0 = T" and f1:"f 1 = T1" and s:"s \<in># T" and 
          T':"T1 = ((T - {#s#}) + {#replace_at s p ((crhs rl) \<cdot> \<sigma>)#} + 
          (subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl))))" and rl:"rl \<in> R" and 
          red_pos:"p \<in> fun_poss s" and s1p:"s |_ p = (clhs rl) \<cdot> \<sigma>" and 
          condsat: "(\<forall> (s\<^sub>i, t\<^sub>i) \<in> set (snd rl). (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*)" by auto
        have norm\<theta>:"normalized R \<theta>" by fact
        hence Ts:"T = subst_term_multiset \<theta> S" using f0 1 by auto
        have "\<exists>\<omega>. V \<inter> vars_crule (\<omega> \<bullet> rl) = {}" using 1(10) 
          by (metis crule_fs.rename_avoiding supp_vars_crule_eq)
        then obtain \<omega> where varempty':"V \<inter> vars_crule (\<omega> \<bullet> rl) = {}" by auto
        hence "\<exists>\<omega>r. \<omega>r \<bullet> \<omega> \<bullet> rl \<in> R" using rl
          by (metis (no_types, opaque_lifting) crule_pt.permute_minus_cancel(2) crule_pt.permute_plus)
        then obtain \<omega>r where \<omega>r:"\<omega>r \<bullet> (\<omega> \<bullet> rl) \<in> R" by auto
        from red_pos have pfs1:"p \<in> fun_poss s" by blast
        have ps1:"p \<in> poss s" using fun_poss_imp_poss pfs1 by blast
        hence nt:"((clhs rl) \<cdot> \<sigma>) \<notin> NF (cstep R)"
        proof - 
          have *:"is_Fun (clhs rl)" using wf[unfolded wf_1ctrs_def] using rl by fastforce 
          let ?C = "Hole::('f, 'v)ctxt"
          from condsat rl * have "(clhs rl \<cdot> \<sigma>, crhs rl \<cdot> \<sigma>) \<in> cstep R" by (auto split:prod.splits)
              (rule cstepI[of "clhs rl" "crhs rl" "snd rl" R \<sigma> "clhs rl \<cdot> \<sigma>" ?C ], fastforce+)
          then show ?thesis by auto
        qed
        obtain u where uS':"u \<in># S" and us1:"u \<cdot> \<theta> = s" using Ts s unfolding subst_term_multiset_def by auto
        have sub_eq:"(u \<cdot> \<theta>) |_ p = (clhs rl) \<cdot> \<sigma>" using us1 s1p by auto
        have "p \<in> fun_poss (u \<cdot> \<theta>)" using pfs1 us1 by auto
        have p:"p \<in> poss u" 
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence pnu:"p \<notin> poss u" by simp
          hence pnfu:"p \<notin> fun_poss u" using fun_poss_imp_poss by blast
          from poss_subst_apply_term[of p u \<theta>]
          obtain q r x where qpr:"p = q @ r" and qu:"q \<in> poss u" and uqx:"u |_ q = Var x" and r:"r \<in> poss (\<theta> x)"
            using pnfu ps1 us1 by blast
          hence *:"(u \<cdot> \<theta>) |_ p = (Var x) \<cdot> \<theta> |_ r" by force
          have "((Var x) \<cdot> \<theta>) \<in> NF (cstep R)" using norm\<theta> 
            by (simp add: normalized_def)
          hence "((Var x) \<cdot> \<theta> |_ r) \<in> NF (cstep R)"  
            by (auto simp add: normalized_def, insert r, goal_cases) 
              (meson NF_cstep_subterm subt_at_imp_supteq')
          then show False using nt * using s1p us1 by auto
        qed
        hence pfun:"p \<in> fun_poss u"  using ps1 us1 red_pos 
          by (metis norm\<theta> normalized_def nt poss_is_Fun_fun_poss poss_subst_choice sub_eq subt_at.simps(1) var_pos_maximal)
        hence vuS':"vars_term (u |_ p) \<subseteq> vars_term_set (set_mset S)" 
        proof -
          have "vars_term (u |_ p) \<subseteq> vars_term u" using p 
            by (simp add: vars_term_subt_at)
          then show ?thesis using uS' vars_term_set_def by fastforce
        qed
        with varempty' have varcond:"vars_term (u |_ p) \<inter> vars_crule (\<omega> \<bullet> rl) = {}" using 1(8) by auto
        from vuS' have vuV:"vars_term (u |_ p) \<subseteq> V" using 1(8) by auto
        have "\<exists>\<sigma>r. \<forall>t. \<sigma>r (\<omega> \<bullet> t) = \<sigma> t" using atom_pt.permute_minus_cancel(2) by (metis o_apply)
        then obtain \<sigma>r where \<sigma>rdef:"\<forall>t. \<sigma>r (\<omega> \<bullet> t) = \<sigma> t" by auto
        hence "\<sigma>r = (\<lambda>x. \<sigma> (- \<omega> \<bullet> x))" by (metis atom_pt.permute_minus_cancel(1))
        hence \<sigma>r:"\<sigma>r = (\<lambda>x. (sop (- \<omega>) \<circ>\<^sub>s \<sigma>) x)" 
          by (metis comp_apply permute_atom_def subst_compose_o_assoc subst_monoid_mult.mult.left_neutral)
        hence "\<forall>S. subst_term_set \<sigma> S = subst_term_set \<sigma>r (\<omega> \<bullet> S)" unfolding subst_term_set_def 
        proof(auto, goal_cases)
          case (1 S t)
          then show ?case 
            by (metis term_pt.permute_flip term_set_pt.mem_permute_iff)
        next
          case (2 S xa)
          then show ?case by force
        qed
        hence pc:"clhs rl \<cdot> \<sigma> = clhs (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          by (simp add: \<sigma>r crule_pt.fst_eqvt rule_pt.fst_eqvt)
        have pc':"crhs rl \<cdot> \<sigma> = crhs (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          by (simp add: \<sigma>r crule_pt.snd_eqvt rule_pt.snd_eqvt crule_pt.fst_eqvt)
        let ?\<sigma>r = "\<sigma>r |s vars_crule (\<omega> \<bullet> rl)"
        let ?\<sigma>dom = "vars_crule (\<omega> \<bullet> rl)"
        have sub_\<sigma>r:"subst_domain ?\<sigma>r \<subseteq> (vars_crule (\<omega> \<bullet> rl))" 
          using subst_domain_restrict_subst_domain by fastforce 
        let ?\<theta> = "\<theta> |s V"
        have sub_\<theta>:"subst_domain ?\<theta> \<subseteq> V" using subst_domain_restrict_subst_domain by fastforce
        have inter_empty:"subst_domain ?\<sigma>r \<inter> subst_domain ?\<theta> = {}" using varempty' 1(8) sub_\<sigma>r by auto
        have vtrs:"vars_trs (set (snd (\<omega> \<bullet> rl))) \<subseteq> vars_crule ((\<omega> \<bullet> rl))" 
          by (simp add: vars_crule_def)
        have crl:"(crhs (\<omega> \<bullet> rl)) \<cdot> \<sigma>r = ((crhs rl) \<cdot> \<sigma>)" 
          by (simp add: \<sigma>r crule_pt.fst_eqvt rule_pt.snd_eqvt)
        note subst_rest_domain1 = subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
        have subinter:"subst_domain ?\<sigma>r = subst_domain \<sigma>r \<inter> ?\<sigma>dom" using subst_rest_domain1 by auto
        have vtrs_dom:"vars_trs (set (snd (\<omega> \<bullet> rl))) \<subseteq> ?\<sigma>dom" using vtrs by blast
        have vars_cond_crule:"vars_term_set (set_mset (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))) \<subseteq> vars_crule (\<omega> \<bullet> rl)" 
          unfolding vars_term_set_def vars_crule_def set_mset_def using var_set_conv_inv 
          by (metis set_mset_def sup_ge2 vars_term_set_def)
        moreover have sub_\<sigma>r_equiv:"subst_term_multiset ?\<sigma>r (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))) = 
          subst_term_multiset \<sigma>r (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))" 
          by (simp add: calculation subst_term_multiset_rest_domain)
        have "subst_domain ?\<theta> \<inter> vars_seq (snd (\<omega> \<bullet> rl)) = {}" 
          unfolding vars_seq_def using vtrs varempty' using vars_trs_def using sub_\<theta> by fastforce
        hence vars_inter_empty:"subst_domain ?\<theta> \<inter> vars_term_set(set_mset(convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))) = {}" 
          using var_set_conv_inv vars_defs(1) vars_seq_def by fastforce
        from us1 s1p have *:"(u \<cdot> \<theta> |_ p) = clhs (\<omega> \<bullet> rl) \<cdot> \<sigma>r"
          by (simp add: pc subst_apply_term_restrict_subst_domain) 
        have varcond':"vars_term (u |_ p) \<inter> vars_term (clhs (\<omega> \<bullet> rl)) = {}" 
        proof -
          have "vars_term (clhs (\<omega> \<bullet> rl)) \<subseteq> vars_crule (\<omega> \<bullet> rl)"
            by (metis (mono_tags, opaque_lifting) dual_order.refl le_sup_iff vars_crule_def vars_defs(2))
          then show ?thesis using varcond by auto
        qed
        with norm\<theta> * have u_p:"(u |_ p) \<cdot> \<theta> = clhs (\<omega> \<bullet> rl) \<cdot> \<sigma>r" 
          using p by simp
        have sub_eq:"(u |_ p) \<cdot> ?\<theta> = clhs (\<omega> \<bullet> rl) \<cdot> ?\<sigma>r" using u_p 
          by (metis (no_types, lifting) 1(8) Un_upper1 coincidence_lemma' le_supE subst_domain_neutral vars_crule_def vars_defs(2))
        from subst_union_sound[OF sub_eq]
        have subst_eq_\<theta>\<sigma>:"(u |_ p) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)  = (clhs (\<omega> \<bullet> rl)) \<cdot> (?\<theta>\<union>\<^sub>s ?\<sigma>r)" using sub_\<sigma>r sub_\<theta> inter_empty
          by (smt (verit) 1(8) Un_upper1 inf.absorb_iff2 inf.idem inf.orderE inf_bot_right inf_left_commute 
              inf_sup_aci(2) le_supE sub_comm sub_eq subst_union_term_reduction varcond varempty' vars_crule_def vars_defs(2))
        then obtain \<delta> where mgu_uv:"mgu (u |_ p) (clhs (\<omega> \<bullet> rl)) = Some \<delta>" using mgu_ex 
          by (meson ex_mgu_if_subst_apply_term_eq_subst_apply_term)
        hence up\<omega>rl:"(u |_ p) \<cdot> \<delta> =  clhs (\<omega> \<bullet> rl) \<cdot> \<delta>" using subst_apply_term_eq_subst_apply_term_if_mgu by blast
        from mgu_sound[OF mgu_uv] have \<delta>:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) =  \<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)" using subst_eq_\<theta>\<sigma> 
          by (smt (verit, ccfv_SIG) is_imgu_def subst_monoid_mult.mult_assoc the_mgu the_mgu_is_imgu)
        have subst_domain\<delta>:"subst_domain \<delta> \<subseteq> vars_term (u |_ p) \<union> vars_term (clhs (\<omega> \<bullet> rl))" 
          using mgu_subst_domain mgu_uv by blast
        have subst_range_disj\<delta>:"subst_domain \<delta> \<inter> range_vars \<delta> = {}" using mgu_uv mgu_subst_domain_range_vars_disjoint by blast
        let ?S = "subst_term_multiset \<delta> ((S - {#u#}) + {#replace_at u p (crhs (\<omega> \<bullet> rl))#} + convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))"
        have nar:"(S, ?S, \<delta>) \<in>  cond_narrowing_step" 
          by (smt (verit, ccfv_threshold) 1(8) \<omega>r cond_narrowing_stepI inf.orderE inf_bot_right inf_commute 
              inf_left_commute le_supE mgu_uv pfun uS' varempty')
        from cond_narrowing_set_imp_rtran[OF nar]
        have condn1:"cond_narrowing_derivation_num S ?S \<delta> 1" by auto
        let ?V = "(V - subst_domain \<delta>) \<union> range_vars \<delta>"
        let ?\<theta>1 = "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s ?V"
        have sub\<theta>1:"subst_domain ?\<theta>1 \<subseteq> ?V" 
          by (metis inf_le1 restrict_subst subst_domain_restrict_subst_domain)
        have reseq:"?\<theta>1 |s ?V = (?\<theta> \<union>\<^sub>s ?\<sigma>r) |s  ?V" 
          by (simp add: restrict_subst_domain_def)
        have reseq\<delta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1) |s V  = (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) |s V " 
          using reseq r_subst_compose by blast
        have reseq\<theta>:"(\<delta> \<circ>\<^sub>s ?\<theta>1)|s V = \<theta> |s V" using  \<delta> 1(8) by auto (smt (verit) \<delta> disjoint_iff notin_subst_domain_imp_Var 
              reseq\<delta> sub_\<sigma>r subset_iff subst_domain_neutral subst_ext subst_union.elims varempty')
        have "normalized R (?\<theta>1 |s ?V)"
        proof -
          let ?\<delta> = "\<delta> |s V"
          let ?B = "(V - subst_domain \<delta>) \<union> range_vars ?\<delta>"
          have normV:"normalized R (\<theta> |s V)" using norm\<theta> 1(8) by auto
          have BV:"?B \<subseteq> V - subst_domain \<delta> \<union> range_vars (\<delta> |s V)" by auto
          from restricted_normalized[OF normV reseq\<theta> BV]
          have normB:"normalized R (?\<theta>1 |s ?B)" by auto 
          have ranB:"range_vars \<delta> \<subseteq> ?B"
          proof
            fix x
            assume asm:"x \<in> range_vars \<delta>"
            hence xn\<delta>:"x \<notin> subst_domain \<delta>" using \<delta>
              by (meson disjoint_iff mgu_subst_domain_range_vars_disjoint mgu_uv)
            have subst_x:"x \<in> vars_term (u |_ p) \<union> vars_term (clhs (\<omega> \<bullet> rl))" using mgu_uv 
                asm mgu_range_vars by auto
            then show "x \<in> ?B"
            proof
              assume "x \<in> vars_term (u |_ p)"
              hence "x \<in> V - subst_domain \<delta>" using 1(8) xn\<delta> vuS' by auto
              then show ?thesis by auto
            next
              assume asm2:"x \<in> vars_term (clhs (\<omega> \<bullet> rl))"
              hence xnu:"x \<notin> vars_term (u |_ p)" using varcond' by blast
              from vars_term_range[OF asm asm2 subst_range_disj\<delta>]
              have xv\<delta>:"x \<in> vars_term (clhs (\<omega> \<bullet> rl) \<cdot> \<delta>)" by auto
              have *:"x \<in> vars_term (u |_ p \<cdot> \<delta>)" using mgu_uv xv\<delta>
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu) 
              hence "vars_term (clhs (\<omega> \<bullet> rl) \<cdot> \<delta>) = vars_term (u |_ p \<cdot> \<delta>)" using mgu_uv 
                by (simp add: subst_apply_term_eq_subst_apply_term_if_mgu)
              from subst_restricted_range_vars[OF * subst_range_disj\<delta> xnu asm]
              have "x \<in> range_vars (\<delta> |s vars_term (u |_ p))" by auto
              moreover have upV:"vars_term (u |_ p) \<subseteq> V" using 1(8) vuS' by auto
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
        hence norm\<theta>1:"normalized R ?\<theta>1" using sub\<theta>1 reseq by fastforce
        have rel_chain':"\<And>i. i < n - 1 \<Longrightarrow> (f (i + 1), f (Suc i + 1)) \<in> cond_reduction_step" using rel_chain 
          by (simp add: 1(4))
        let ?f = "\<lambda>i. f (i + 1)"
        have relstar:"(f 1, f n) \<in> (cond_reduction_step)\<^sup>*" using False 1(4) less_Suc_eq 
          by (induct n, blast, metis (no_types, lifting) One_nat_def rtrancl.simps)
        have vars\<theta>:"vars_term_set (set_mset S) \<union> subst_domain \<theta> \<subseteq> V" by fact
        have scomp:"?S = subst_term_multiset \<delta> (S - {#u#}) + subst_term_multiset \<delta> {#replace_at u p (crhs (\<omega> \<bullet> rl))#}
            + subst_term_multiset \<delta> (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))" (is "?S = ?fst + ?snd + ?lst")
          unfolding subst_term_multiset_def by auto
        have "subst_term_multiset \<delta> {#replace_at u p (crhs (\<omega> \<bullet> rl))#} \<subseteq># ?S"
          by (simp add: subst_term_multiset_def)
        hence vars_subS:"vars_term_set (set_mset (subst_term_multiset \<delta> {#replace_at u p (crhs (\<omega> \<bullet> rl))#})) \<subseteq> ?V"  
        proof -
          have "vars_term (crhs rl) \<subseteq> vars_term (clhs rl)" using wf[unfolded wf_1ctrs_def[unfolded type1_def]] rl by auto
          hence *:"vars_term (crhs (\<omega> \<bullet> rl)) \<subseteq> vars_term (clhs (\<omega> \<bullet> rl))" using rl by auto
              (metis UnCI crule_pt.fst_eqvt rule_pt.fst_eqvt sup.absorb_iff1 vars_defs(2) vars_rule_eqvt vars_term_eqvt)
          from var_cond_stable[OF this]
          have "vars_term (crhs (\<omega> \<bullet> rl) \<cdot> \<delta> ) \<subseteq> vars_term (crhs (\<omega> \<bullet> rl) \<cdot> \<delta>)" by fastforce
          from replace_var_stable[OF this] 
          have "vars_term(replace_at u p (crhs (\<omega> \<bullet> rl)) \<cdot> \<delta>) \<subseteq> vars_term (replace_at u p (clhs (\<omega> \<bullet> rl)) \<cdot> \<delta>)" 
            by (meson "*" replace_var_stable var_cond_stable)
          moreover have "vars_term (replace_at u p (clhs (\<omega> \<bullet> rl)) \<cdot> \<delta>) = vars_term (u \<cdot> \<delta>)" using up\<omega>rl
            by (metis ctxt_supt_id p subst_apply_term_ctxt_apply_distrib)
          moreover have "vars_term (u \<cdot> \<delta>) \<subseteq> ?V" using uS' 1(8)  vars_term_set_def vars_term_subst_apply_term_subset
            by auto (fastforce, meson Diff_iff UnE subsetD vars_term_subst_apply_term_subset)
          ultimately show ?thesis unfolding vars_term_set_def subst_term_multiset_def by auto
        qed    
        have "subst_term_multiset \<delta> (S - {#u#}) \<subseteq># ?S" by (simp add: subst_term_multiset_def)
        hence vars_subSu:"vars_term_set (set_mset (subst_term_multiset \<delta> (S - {#u#}))) \<subseteq> ?V" 
        proof -
          have "vars_term_set (set_mset S) \<subseteq> V" using vars\<theta> by auto
          hence "vars_term_set (set_mset (subst_term_multiset \<delta> S)) \<subseteq> ?V" unfolding vars_term_set_def
              subst_term_multiset_def set_mset_def using vars_term_subst_apply_term_subset by fastforce+
          then show ?thesis by (smt (verit, del_insts) SUP_le_iff add_mset_add_single insert_DiffM 
                subst_term_multiset_union uS' union_iff vars_term_set_def)
        qed
        have "subst_term_multiset \<delta> (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))) \<subseteq># ?S" 
          by (simp add: subst_term_multiset_def)
        hence vars_sndrl:"vars_term_set (set_mset (subst_term_multiset \<delta> (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))))) \<subseteq> ?V" 
        proof - 
          have "vars_trs (set (snd (rl))) \<subseteq> vars_term (clhs (rl))" using wf[unfolded wf_1ctrs_def[unfolded type1_def]] rl
            unfolding vars_trs_def vars_rule_def by auto
          hence *:"vars_trs (set (snd (\<omega> \<bullet> rl))) \<subseteq> vars_term (clhs (\<omega> \<bullet> rl))" using vars_cond_perm 
            by (metis crule_pt.fst_eqvt crule_pt.snd_eqvt permute_conds_set rule_pt.fst_eqvt)
          have "vars_term (clhs (\<omega> \<bullet> rl) \<cdot> \<delta>) \<subseteq> ?V" by auto (metis (mono_tags, opaque_lifting) DiffE UnE subset_iff up\<omega>rl 
                vars_term_subst_apply_term_subset vuV, meson Diff_iff UnE subsetD vars_term_subst_apply_term_subset)
          then show ?thesis unfolding vars_term_set_def set_mset_def subst_term_multiset_def by auto (smt (verit, ccfv_SIG) 
                Diff_iff UN_I UnE * inv_var_subst subsetD vars_seq_term_set_equiv vars_term_set_def vars_term_subst_apply_term_subset,
                meson Diff_iff UnE subsetD vars_term_subst_apply_term_subset)
        qed
        have varSV:"vars_term_set (set_mset ?S) \<subseteq> ?V"
        proof -
          have *:"vars_term_set (set_mset ?S) = vars_term_set (set_mset ?fst) \<union> vars_term_set (set_mset ?snd) \<union> vars_term_set (set_mset ?lst)"
            using scomp unfolding vars_term_set_def by auto
          then show ?thesis using vars_subS vars_subSu vars_sndrl by auto
        qed
        have wfeq_S:"wf_equational_term_mset ?S"
        proof -
          have wf_eq_S:"wf_equational_term_mset S" by fact
          have *:"?S = subst_term_multiset \<delta> (S - {#u#}) + subst_term_multiset \<delta> {#replace_at u p (crhs (\<omega> \<bullet> rl))#} + 
              subst_term_multiset \<delta> (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))"
            (is "?S = ?A + ?B + ?C") by (metis subst_term_multiset_union)
          have "wf_equational_term_mset ?A"
          proof -
            have "wf_equational_term_mset (S - {#u#})"
              by (meson in_diffD wf_eq_S wf_equational_term_mset_def)
            then show ?thesis unfolding wf_equational_term_mset_def using wf_eq_subst
              by (metis wf_eq_mset_subst_inv wf_equational_term_mset_def)
          qed
          moreover  
          {
            note funas_defs = funas_crule_def funas_rule_def funas_trs_def
            let ?crule = "\<lambda>x. ((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []), [])"
            have cr:"\<forall>x. funas_crule (?crule x) = {(\<doteq>, 2), (\<top>, 0)}" using D 
              unfolding funas_defs by (auto simp add: numeral_2_eq_2)
            have cd:"\<forall>x. funas_crule (?crule x) \<subseteq> D" using D 
              unfolding funas_defs by (auto simp add: numeral_2_eq_2)
            have wf_u:"wf_equational_term u" using uS' wf_eq_S wf_equational_term_mset_def by auto
            have \<omega>rl:"rl \<in> R' \<or> (\<exists>x. rl = ?crule x)" using R' rl by auto
            moreover have \<omega>rl_un:"funas_crule (rl) \<subseteq> F  \<or> (\<exists>x. rl = ?crule x)" 
              using R_sig using calculation funas_crule_included_ctrs by blast
            ultimately have "funas_crule ( rl) \<subseteq> F \<or> funas_crule (rl) = {(\<doteq>, 2), (\<top>, 0)}"
              using cr by metis
            then consider (ordinary) "funas_crule (rl) \<subseteq> F" | (special) "funas_crule ( rl) = {(\<doteq>, 2), (\<top>, 0)}" 
              using \<omega>rl by auto
            hence "wf_equational_term (replace_at u p (crhs (\<omega> \<bullet> rl)))"
            proof(cases)
              case ordinary
              hence rlR':"rl \<in> R'" using R' D R_sig D_fresh 
                by (metis Int_absorb2 \<omega>rl cr insert_not_empty)
              from ordinary have *:"funas_crule (\<omega> \<bullet> rl) \<subseteq> F" using funas_crule_perm by blast
              have **:"root (clhs (\<omega> \<bullet> rl)) = root (clhs (rl))" using root_perm_inv
                by (metis crule_pt.fst_eqvt rule_pt.fst_eqvt)
              have ***:"is_Fun (clhs rl)"  using ** wf[unfolded wf_1ctrs_def]
                using rl by fastforce
              from fun_root_not_None[OF ***] have nroot:"root (clhs rl) \<noteq> None" by auto
              from root_not_special_symbols[OF rlR' ordinary nroot]
              have "root(clhs rl) \<noteq> Some (\<doteq>, 2) \<and> root(clhs rl) \<noteq>  Some (\<top>, 0)" by simp
              hence rn:"root(clhs (\<omega> \<bullet> rl)) \<noteq> Some (\<doteq>, 2) \<and> root(clhs (\<omega> \<bullet> rl)) \<noteq> Some (\<top>, 0)" 
                by (simp add: "**")
              have "root (u |_ p) = root (clhs (\<omega> \<bullet> rl) \<cdot> \<sigma>r)" using u_p 
                by (metis pfun root_subst_inv)
              also have "... = root(clhs (\<omega> \<bullet> rl))" 
                using wf[unfolded wf_1ctrs_def] root_subst_inv 
                by (auto split:prod.splits, insert ** *** pc, auto)
              finally have root_eq:"root (u |_ p) = root(clhs (\<omega> \<bullet> rl))" by auto
              with u_p pfun have "root (u |_ p) \<noteq> Some (\<doteq>, 2) \<and> root (u |_ p) \<noteq> Some (\<top>, 0)"
                using rn by auto
              hence np:"p \<noteq> []" using wf_u[unfolded wf_equational_term_def] by force
              hence uf:"u \<noteq> Fun (\<top>) []" using pfun by auto
              from wf_u[unfolded wf_equational_term_def]
              obtain v w where u:"u = Fun \<doteq> [v, w] \<and> (\<doteq>, 2) \<notin> funas_term v \<and> (\<doteq>, 2) \<notin> funas_term w"
                using uf by auto
              have "funas_term (crhs (\<omega> \<bullet> rl)) \<subseteq> F" using * unfolding funas_defs by blast
              then show ?thesis by (simp add: np wf_equational_term_safe_replace wf_u uf pfun)
            next
              case special
              have "funas_crule (\<omega> \<bullet> rl) = {(\<doteq>, 2), (\<top>, 0)}"
              proof(rule ccontr)
                assume asm:"\<not> ?thesis"
                have "funas_crule rl = D" using special
                  by (simp add: D)
                hence "funas_crule (\<omega> \<bullet> rl) = D" using funas_crule_perm 
                  by (metis (full_types) crule_pt.permute_minus_cancel(2) 
                      order_refl subset_antisym)
                then show False using asm D by simp
              qed
              hence "\<exists>x. fst (\<omega> \<bullet> rl) = fst (?crule x)"
              proof -
                from special have "\<exists>y. fst rl = fst (?crule y)" using \<omega>rl
                  using D D_fresh \<omega>rl_un by auto
                then obtain y where "fst rl = fst (?crule y)" by auto
                hence "subst_equation ((sop \<omega>)::('f, 'v) subst) (fst (rl))
                = subst_equation ((sop \<omega>)::('f, 'v) subst) (fst (?crule y))"
                  by auto
                hence "fst (\<omega> \<bullet> rl) = subst_equation ((sop \<omega>)::('f, 'v) subst) (fst (?crule y))"
                  using subst_equation_perm 
                  by (simp add: crule_pt.fst_eqvt rule_pt.fst_eqvt rule_pt.snd_eqvt subst_equation_def)
                moreover have "\<exists>x. subst_equation ((sop \<omega>)::('f, 'v) subst) (fst (?crule y)) =
                fst (?crule x)" unfolding subst_equation_def by auto
                ultimately show ?thesis by simp
              qed
              then obtain x where \<omega>'rl:"fst (\<omega> \<bullet> rl) = fst (?crule x)" by auto
              have rclhs:"root (clhs (\<omega> \<bullet> rl)) = Some (\<doteq>, 2)" using \<omega>'rl by auto
              have crhs_\<omega>'rl:"crhs (\<omega> \<bullet> rl) = Fun (\<top>) []" using \<omega>'rl by auto
              have "is_Fun (clhs (rl))"  using wf[unfolded wf_1ctrs_def]
                using rl by fastforce
              hence isFun\<omega>':"is_Fun (clhs (\<omega> \<bullet> rl))" by (simp add: \<omega>'rl)
              from fun_root_not_None[OF isFun\<omega>'] have nroot:"root (clhs (\<omega> \<bullet> rl)) \<noteq> None" by auto
              have rclhs\<sigma>r:"root(clhs (\<omega> \<bullet> rl) \<cdot> \<sigma>r) = Some (\<doteq>, 2)" using \<omega>'rl by auto
              have "root (u |_ p) = root (clhs (\<omega> \<bullet> rl) \<cdot> \<sigma>r)" using u_p 
                by (metis pfun root_subst_inv)
              also have "... = root(clhs (\<omega> \<bullet> rl))" 
                using wf[unfolded wf_1ctrs_def] root_subst_inv 
                by (auto split:prod.splits, insert rclhs rclhs\<sigma>r, auto)
              finally have root_eq:"root (u |_ p) = root(clhs (\<omega> \<bullet> rl))" by auto
              with u_p pfun have root_u:"root (u |_ p) = Some (\<doteq>, 2)" using rclhs by auto
              have un:"u \<noteq> Fun (\<top>) []"
              proof(rule ccontr)
                assume "\<not> ?thesis"
                hence "u = Fun (\<top>) []" by auto
                hence "funas_term u = {(\<top>, 0)}" by auto
                then show False using root_u subterm_funas pfun by fastforce
              qed
              from wf_u[unfolded wf_equational_term_def] 
              obtain v w where u:"u = Fun (\<doteq>) [v, w]" and nv:"(\<doteq>, 2) \<notin> funas_term v" and 
                nw:"(\<doteq>, 2) \<notin> funas_term w" using un by auto
              have p:"p = []"
              proof (rule ccontr)
                assume "\<not> ?thesis"
                hence "v \<unrhd> (u |_ p) \<or> w \<unrhd> (u |_ p)" using pfun u by auto
                    (metis diff_Suc_1 fun_poss_imp_poss less_Suc0 less_Suc_eq nth_Cons' subt_at_imp_supteq)
                then show False using root_u nv nw 
                  by (meson root_symbol_in_funas subset_eq supteq_imp_funas_term_subset)
              qed
              hence "replace_at u p (crhs (\<omega> \<bullet> rl)) = crhs (\<omega> \<bullet> rl)" by auto
              then show ?thesis using crhs_\<omega>'rl wf_u[unfolded wf_equational_term_def] 
                by (simp add: wf_equational_term_def)
            qed
            hence "wf_equational_term_mset ?B" unfolding wf_equational_term_mset_def subst_term_multiset_def 
              using wf_eq_subst by fastforce
          }   
          moreover have "wf_equational_term_mset ?C"
          proof(cases "snd (\<omega> \<bullet> rl) = []")
            case True
            then show ?thesis by (metis \<omega>r convert_cond_into_term_multiset_sound crule_pt.snd_eqvt 
                  perm_empty_cond wf_eq_mset_subst_inv)
          next
            case False
            then show ?thesis 
            proof -
              have "\<forall>x. rl \<noteq> ((Fun \<doteq> [Var x, Var x], Fun \<top> []), [])" using False 
                by (metis crule_pt.permute_flip crule_pt.snd_eqvt perm_empty_cond rl snd_eqD)
              hence rl:"rl \<in> R'" using R' rl by auto
              hence "funas_ctrs R' \<subseteq> F" using R_sig by simp
              have "funas_crule rl \<subseteq> F" 
                using R_sig funas_crule_included_ctrs rl by blast
              hence "funas_crule (\<omega> \<bullet> rl) \<subseteq> F" using funas_crule_perm by blast
              hence "funas_trs (set (snd (\<omega> \<bullet> rl))) \<subseteq> F" 
                unfolding funas_trs_def funas_crule_def by blast
              hence *:"(\<doteq>, 2) \<notin> funas_trs (set (snd (\<omega> \<bullet> rl))) \<and> (\<top>, 0) \<notin> funas_trs (set (snd (\<omega> \<bullet> rl)))"
                using D D_fresh  unfolding funas_trs_def by blast
              let ?C = "convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))" 
              have "\<forall>t \<in># ?C. \<exists>(u::('f, 'v)term) v::('f, 'v)term. t = Fun (\<doteq>) [u, v] \<and> (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v
                \<and> (\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v"
              proof
                fix t
                assume "t \<in># ?C"
                hence "t \<in># {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (snd (\<omega> \<bullet> rl)) #}" 
                  using False convert_cond_into_term_multiset.elims by (metis (mono_tags, lifting))
                then obtain u v where t:"t = Fun (\<doteq>) [u, v]" and uv:"(u, v) \<in># mset (snd (\<omega> \<bullet> rl))" by auto
                have "(\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v" using * lhs_wf rhs_wf uv by fastforce
                moreover have "(\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v" using * lhs_wf rhs_wf uv by fastforce
                ultimately show "\<exists> u v. t = Fun (\<doteq>) [u, v] \<and> (\<doteq>, 2) \<notin> funas_term u \<and> (\<doteq>, 2) \<notin> funas_term v \<and>
                  (\<top>, 0) \<notin> funas_term u \<and> (\<top>, 0) \<notin> funas_term v" using t by auto
              qed    
              then show ?thesis unfolding wf_equational_term_mset_def subst_term_multiset_def 
                using wf_eq_subst by (simp add: wf_equational_term_def)
            qed
          qed
          ultimately show ?thesis using "*" wf_equational_term_mset_add by auto
        qed
        from subst_domain_restrict_subst_domain[of ?\<sigma>dom \<sigma>r]
        have subinter:"subst_domain ?\<sigma>r = subst_domain \<sigma>r \<inter> ?\<sigma>dom" by auto
        have inempty:"subst_domain ?\<sigma>r \<inter> V = {}" using varempty' subinter by auto
        hence \<theta>sv:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s V = \<theta> |s V"
          using \<delta> reseq\<delta> reseq\<theta> by auto
        have \<theta>varr:"(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s (vars_term (\<omega> \<bullet> crhs rl)) = ?\<sigma>r |s (vars_term (\<omega> \<bullet> crhs rl))" 
        proof -
          { fix v :: 'v
            have "vars_rule (\<omega> \<bullet> (clhs rl, crhs rl)) - V = vars_rule (\<omega> \<bullet> (clhs rl, crhs rl))" using varempty' unfolding funas_defs 
              by (auto simp add: crule_pt.fst_eqvt disjoint_iff vars_crule_def)
            then have "V \<inter> vars_term (\<omega> \<bullet> crhs rl) = {}"  
              by (metis (no_types, lifting) Diff_disjoint disjoint_iff prod.collapse rule_pt.snd_eqvt subsetD sup_ge2 vars_rule_def)
            then have "(?\<theta> \<union>\<^sub>s ?\<sigma>r) |s (vars_term (\<omega> \<bullet> crhs rl)) = ?\<sigma>r |s (vars_term (\<omega> \<bullet> crhs rl))"
              by (smt (verit, best) Int_iff disjoint_iff inf.absorb_iff2 sub_\<theta> subst_ext subst_union.simps)
          } then show ?thesis by fastforce
        qed
        have subeq:"subst_rule \<sigma>r (\<omega> \<bullet> (clhs rl, crhs rl)) = subst_rule \<sigma> (clhs rl, crhs rl)" unfolding subst_rule_def subst_list_def  
          using pc' pc crule_pt.fst_eqvt pc' by (metis prod.collapse)
        have sub_eq1:"subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) = f 0 - {#s#}"
        proof -  
          have "vars_term_set (set_mset (subst_term_multiset \<delta> (S - {#u#}))) \<subseteq> ?V" using vars_subSu by auto
          hence subm_eq:"subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) = subst_term_multiset (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) (S - {#u#})" using reseq\<delta> 
            by (metis (no_types, opaque_lifting) restrict_subst subst_term_multiset_compose subst_term_multiset_rest_domain)
          hence "... = subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (S - {#u#})" using \<delta> by auto
          have *:"subst_domain ?\<theta> \<subseteq> V" by fact
          have **:"subst_domain ?\<sigma>r \<inter> vars_term_set (set_mset (S - {#u#})) = {}" unfolding vars_term_set_def set_mset_def           
            by (smt (verit, ccfv_threshold) "1.prems"(7) SUP_le_iff count_greater_zero_iff disjoint_iff 
                in_diffD inempty le_supE mem_Collect_eq subsetD vars_term_set_def)
          from subst_union_term_multiset_reduction[of ?\<theta> ?\<sigma>r S]
          have ***:"subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) S = f 0" 
            by (metis Ts \<theta>sv f0 le_supE restrict_subst subst_term_multiset_rest_domain vars\<theta>)
          from subst_union_term_multiset_reduction[OF inter_empty **]
          have "subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (S - {#u#}) = subst_term_multiset ?\<theta> (S - {#u#})" by (metis inter_empty sub_comm)
          also have "... = subst_term_multiset ?\<theta> S - subst_term_multiset ?\<theta> {#u#}" 
            by (simp add: image_mset_Diff subst_term_multiset_def uS')
          also have "... = subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) S - subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) {#u#}"
            by (metis calculation image_mset_Diff mset_subset_eq_single subst_term_multiset_def uS')
          also have "... = f 0 - subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) {#u#}" using *** by auto
          also have "... = f 0 - {#s#}" unfolding subst_term_multiset_def
            by (metis (no_types, lifting) 1(8) SUP_le_iff \<theta>sv coincidence_lemma' 
                image_mset_add_mset image_mset_empty le_supE uS' us1 vars_term_set_def)
          finally show ?thesis using \<delta> subm_eq by auto
        qed
        have sub_eq2:"{#replace_at s p ((crhs rl) \<cdot> \<sigma>)#} = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) {#replace_at u p (crhs (\<omega> \<bullet> rl))#}" 
        proof -
          have "(crhs rl) \<cdot> \<sigma> = crhs (\<omega> \<bullet> rl) \<cdot> \<sigma>r" using subeq by (simp add: pc')
          have "{#replace_at s p ((crhs rl) \<cdot> \<sigma>)#} = {#replace_at s p ((crhs (\<omega> \<bullet> rl)) \<cdot> \<sigma>r)#}" using \<sigma>rdef pc  pc' by auto 
          also have "... = {#replace_at (u \<cdot> \<theta>) p ((crhs (\<omega> \<bullet> rl)) \<cdot> \<sigma>r)#}" using us1 by auto
          also have "... = {#replace_at (u \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)) p ((crhs (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r))#}" using \<theta>sv \<theta>varr vuV 
            by (smt (verit, best) Int_absorb1 UN_I Un_upper1 crule_pt.fst_eqvt in_subst_restrict 
                le_supE rule_pt.snd_eqvt subsetD term_subst_eq_conv uS' vars\<theta> vars_crule_def vars_defs(2) vars_term_set_def)
          also have "... = {#replace_at u p (crhs (\<omega> \<bullet> rl)) \<cdot> (?\<theta> \<union>\<^sub>s ?\<sigma>r)#}" by (simp add: ctxt_of_pos_term_subst p)
          also have "... = {#replace_at u p (crhs (\<omega> \<bullet> rl)) \<cdot> (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r))#}" using \<delta> by auto
          also have "... = {#replace_at u p (crhs (\<omega> \<bullet> rl)) \<cdot> (\<delta> \<circ>\<^sub>s ?\<theta>1)#}" using vars_subS unfolding vars_term_set_def subst_term_multiset_def 
            using coincidence_lemma' by fastforce
          finally show ?thesis unfolding subst_term_multiset_def by auto
        qed
        have sub_eq3:"subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))
          = (subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl)))"
        proof -
          have "vars_term_set (set_mset (subst_term_multiset \<delta> (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))))) \<subseteq> ?V" 
            using vars_sndrl by auto
          hence subm_eq:"subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))) = 
            subst_term_multiset (\<delta> \<circ>\<^sub>s (?\<theta> \<union>\<^sub>s ?\<sigma>r)) (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))" using reseq\<delta> 
            by (metis (no_types, opaque_lifting) restrict_subst subst_term_multiset_compose subst_term_multiset_rest_domain)
          hence "... = subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))" using \<delta> by auto
          then show ?thesis
          proof(cases "snd (\<omega> \<bullet> rl) = []")
            case True
            from subst_union_term_multiset_reduction[of ?\<theta> ?\<sigma>r]
            have "subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))) = 
              subst_term_multiset ?\<sigma>r (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))"
              using inter_empty vars_inter_empty by blast
            also have "subst_term_multiset ?\<sigma>r (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))) = 
              subst_term_multiset \<sigma>r (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))" 
              using sub_\<sigma>r_equiv by auto
            also have "... = subst_term_multiset \<sigma>r {#}" using True by simp
            also have "... = subst_term_multiset \<sigma> {#}" 
              using \<sigma>rdef unfolding subst_term_multiset_def by simp
            also have "... =  subst_term_multiset \<sigma> (convert_cond_into_term_multiset [])"
              using True unfolding subst_term_multiset_def by simp
            also have "... = subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl))" 
              using perm_empty_cond by (metis True \<omega>r crule_pt.permute_plus crule_pt.snd_eqvt)
            finally show ?thesis using True by auto
          next
            case False
            from subst_union_term_multiset_reduction[of ?\<theta> ?\<sigma>r]
            have "subst_term_multiset (?\<theta> \<union>\<^sub>s ?\<sigma>r) (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))) = 
              subst_term_multiset ?\<sigma>r (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))"
              using inter_empty vars_inter_empty by blast
            also have "subst_term_multiset ?\<sigma>r (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl))) = 
              subst_term_multiset \<sigma>r (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))" 
              using sub_\<sigma>r_equiv by auto
            also have "... = subst_term_multiset \<sigma>r {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (snd (\<omega> \<bullet> rl)) #}"
              using False by (metis (no_types, lifting) convert_cond_into_term_multiset.elims)
            also have *:"... = subst_term_multiset \<sigma> {# Fun (\<doteq>) [u, v]. (u, v) \<in># mset (snd (- \<omega> \<bullet> \<omega> \<bullet> rl)) #}"
              unfolding subst_term_multiset_def using \<sigma>r subst_term_multiset_perm_conv
              by (metis crule_pt.snd_eqvt subst_term_multiset_def)
            also have "... =  subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl))"
              using False by (smt (verit) * convert_cond_into_term_multiset.elims 
                  crule_pt.permute_minus_cancel(2) image_mset_is_empty_iff mset_zero_iff subst_term_multiset_def)
            ultimately show ?thesis using \<delta> subm_eq by auto
          qed
        qed
        have f1S:"subst_term_multiset ?\<theta>1 ?S = f 1"
        proof -
          have "subst_term_multiset ?\<theta>1 ?S = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) ((S - {#u#}) + {#replace_at u p (crhs (\<omega> \<bullet> rl))#} + convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))"
            using subst_term_multiset_compose by blast
          also have "... = subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (S - {#u#}) + subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) {#replace_at u p (crhs (\<omega> \<bullet> rl))#}
            + subst_term_multiset (\<delta> \<circ>\<^sub>s ?\<theta>1) (convert_cond_into_term_multiset (snd (\<omega> \<bullet> rl)))" (is "_ = ?A + ?B + ?C")
            unfolding subst_term_multiset_def using subst_term_multiset_union by auto
          also have "... = (T - {#s#}) + ?B + ?C" using sub_eq1 f0 by auto
          also have "... = (T - {#s#}) + {#replace_at s p ((crhs rl) \<cdot> \<sigma>)#} + ?C" using sub_eq2 by auto
          also have "... = T1" using sub_eq3 using T' by auto
          ultimately show ?thesis using f1 by auto
        qed
        have "\<exists>\<delta>' \<theta>' S'. cond_narrowing_derivation_num ?S S' \<delta>' (n - 1) \<and> subst_term_multiset \<theta>' S' = f n \<and> normalized R \<theta>' \<and> wf_equational_term_mset S' \<and>
         (\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V \<and> finite ?V"
        proof (rule IH1[of "n - 1"  ?f "f 1" "f n" ?\<theta>1 ?S ?V], goal_cases)
          case 1
          then show ?case using False by force
        next
          case 2
          then show ?case by force
        next
          case 3
          then show ?case using False by auto
        next
          case (4 i)
          then show ?case using rel_chain' by auto
        next
          case 5
          then show ?case using norm\<theta>1 by blast
        next
          case 6
          have "wf_equational_term_mset ?S" using wfeq_S by blast
          then show ?case by auto
        next
          case 7
          have "f 1 = subst_term_multiset ?\<theta>1 ?S" using f1S by auto
          then show ?case by blast
        next
          case 8
          then show ?case using varSV sub\<theta>1 by blast
        next
          case 9
          then show ?case using relstar by auto

        next
          case 10
          then show ?case by (meson 1(10) finite_Diff finite_UnI mgu_finite_range_vars mgu_uv)
        qed 
        then obtain \<delta>' \<theta>' S' where condn2:"cond_narrowing_derivation_num ?S S' \<delta>' (n - 1)" and sub\<theta>':"subst_term_multiset \<theta>' S' = f n"
          and norm\<theta>':"normalized R \<theta>'" and wfS':"wf_equational_term_mset S'" and sub_rel:"(\<delta>' \<circ>\<^sub>s \<theta>') |s ?V = ?\<theta>1 |s ?V" and fnV:"finite ?V" by auto
        from n0_cond_narrowing_derivation_num have n1:"n = 1 \<Longrightarrow> S' = ?S \<and> \<delta>' = Var" 
          using False using condn2 by (metis diff_self_eq_0)
        from condn2 obtain g \<tau> where "(?S,  S') \<in> (cond_narrowing_step')^^(n - 1)" and g0:"g 0 = ?S" and gnm1:"g (n - 1) = S'"
          and gcond_chain:"\<forall>i < n - 1. ((g i), (g (Suc i)), (\<tau> i)) \<in> cond_narrowing_step" and comp\<delta>':"if n = 1 then \<delta>' = Var else \<delta>' = compose (map (\<lambda>i. (\<tau> i)) [0 ..< (n - 1)])"
          using False n1 unfolding cond_narrowing_derivation_num_def by auto
        let ?g = "\<lambda>i. if i = 0 then S else g (i - 1)"
        let ?\<tau> = "\<lambda>i. if i = 0 then \<delta> else \<tau> (i - 1)"
        have "\<delta>' = compose (map ?\<tau> [1..< n])" 
          by (smt (verit) One_nat_def comp\<delta>' add_diff_cancel_left' add_diff_inverse_nat 
              compose_simps(1) diff_zero length_upt less_Suc_eq_0_disj list.simps(8) 
              map_equality_iff nth_upt plus_1_eq_Suc upt_eq_Nil_conv)      
        hence \<delta>\<delta>'comp:"\<delta> \<circ>\<^sub>s \<delta>' = compose (map ?\<tau> [0..< n])" using False upt_conv_Cons by fastforce
        have condn:"cond_narrowing_derivation_num S S' (\<delta> \<circ>\<^sub>s \<delta>') n" 
        proof -
          have "(S, S') \<in> cond_narrowing_step' ^^ n" using condn1 condn2 n1 False 
            by (metis (no_types, lifting) One_nat_def Suc_pred bot_nat_0.not_eq_extremum 
                cond_narrowing_derivation_num_def relpow_1 relpow_Suc_I2)
          moreover have "(\<exists>f. f 0 = S \<and> f n = S' \<and> (\<exists>\<tau>. (\<forall>i<n. (f i, f (Suc i), \<tau> i) \<in> cond_narrowing_step) \<and>
            \<delta> \<circ>\<^sub>s \<delta>' = compose (map \<tau> [0..<n])))" 
            by (rule exI[of _ ?g], insert \<delta>\<delta>'comp False One_nat_def gnm1) (smt (verit, ccfv_SIG) Suc_pred gcond_chain 
                bot_nat_0.not_eq_extremum diff_Suc_1 g0 less_nat_zero_code nar not_less_eq)
          ultimately show ?thesis 
            by (simp add: cond_narrowing_derivation_num_def False local.wf)
        qed
        show ?thesis
        proof(rule exI[of _ "\<delta> \<circ>\<^sub>s \<delta>'"], rule exI[of _ \<theta>'], rule exI[of _ S'], intro conjI, goal_cases)
          case 1
          then show ?case using condn by auto
        next
          case 2
          then show ?case using 1(3) sub\<theta>' by blast
        next
          case 3
          then show ?case using norm\<theta>' by auto
        next
          case 4
          then show ?case using wfS' by blast
        next
          case 5
          then show ?case 
            by (metis Un_upper1 r_subst_compose reseq\<theta> sub_rel subst_monoid_mult.mult_assoc sup.orderE)
        next
          case 6
          then show ?case using 1(10) by fastforce
        qed
      qed
    qed
  qed
  then show ?thesis using cond_narrowing_deriv_implication by blast
qed

lemma addFunT:assumes "(\<forall>s\<in>#S. s = Fun \<top> [])"
  and "(\<forall>t\<in>#T. t = Fun \<top> [])"
shows "\<forall>u \<in># S + T. u = Fun \<top> []" using assms 
  by (meson union_iff)

lemma cond_red_add:assumes st:"(S, T) \<in> (cond_reduction_step)\<^sup>*"
  shows "(S + U, T + U) \<in> (cond_reduction_step)\<^sup>*" using assms
proof (induct rule:rtrancl.induct)
  case (rtrancl_refl a)
  then show ?case by auto
next
  case (rtrancl_into_rtrancl a b c)
  from \<open>(b, c) \<in> cond_reduction_step\<close>
  obtain s rl \<sigma> p where s:"s \<in># b" and c:"c = ((b - {#s#}) + {#replace_at s p ((crhs rl) \<cdot> \<sigma>)#} + 
    (subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl))))" and rl:"rl \<in> R" and p:"p \<in> fun_poss s" and 
    sp:"(s |_ p = (clhs rl) \<cdot> \<sigma>)"  and condsat:"(\<forall> (s\<^sub>i, t\<^sub>i) \<in> set (snd rl). (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*)" by auto
  hence "(b + U, c + U) \<in> cond_reduction_step"
    by (intro cond_reduction_step.intros, auto split:prod.splits, simp add: union_assoc union_commute)
  then show ?case using rtrancl_into_rtrancl by auto
qed

lemma cond_red_combine_goal: assumes UT:"(U, T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])"
  and VT':"(V, T') \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T'. t = Fun (\<top>) [])"
shows "\<exists>P. (U + V, P) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># P. t = Fun (\<top>) [])" using assms
proof -
  have "(U + V, T + V) \<in> (cond_reduction_step)\<^sup>*" using cond_red_add UT by auto
  moreover have "(T + V, T + T') \<in> (cond_reduction_step)\<^sup>*" using cond_red_add VT' by (metis add.commute)
  moreover have "(U + V, T + T') \<in> (cond_reduction_step)\<^sup>*" using calculation(1) calculation(2) by auto
  ultimately show ?thesis by (meson UT VT' union_iff)
qed

lemma cond_red_refl: "({#Fun \<doteq> [u::('f, 'v) term, u]#}, {#Fun (\<top>) []#}) \<in> (cond_reduction_step)" 
proof -
  have "\<exists>x. ((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []), []) \<in> R" using R' by auto
  then obtain x::'v where rl:"((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []), []) \<in> R" by auto
  have "is_Fun (Fun \<doteq> [u, u])" by auto
  let ?p = "[]::pos"
  let ?s = "Fun \<doteq> [u, u]"
  let ?\<sigma> = "Var (x := u)" 
  let ?rl = "((Fun (\<doteq>) [Var x, Var x], Fun (\<top>) []), [])"
  have *:"crhs ?rl \<cdot> ?\<sigma> = Fun (\<top>) []" by auto
  show ?thesis
  proof(intro cond_reduction_step.intros conjI)
    show "?s \<in># {#Fun \<doteq> [u, u]#}" by auto
    show "{#Fun \<top> []#} = {#Fun \<doteq> [u, u]#} - {#?s#} + {#(ctxt_of_pos_term ?p ?s)\<langle>crhs ?rl \<cdot> ?\<sigma>\<rangle>#} +
      subst_term_multiset ?\<sigma> (convert_cond_into_term_multiset (conds ?rl))" 
      using empty_not_add_mset unfolding subst_term_multiset_def by auto
    show "?rl \<in> R" using rl by auto
    show "?p \<in> fun_poss ?s" by simp
    show "?s |_ ?p = clhs ?rl \<cdot> ?\<sigma>" using * by auto
    show "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set (conds ?rl). (s\<^sub>i \<cdot> ?\<sigma>, t\<^sub>i \<cdot> ?\<sigma>) \<in> (cstep R)\<^sup>*" by simp
  qed
qed

lemma subst_convert_mset_equiv: assumes "xs \<noteq> []"
  and "funas_trs (set xs) \<subseteq> F"
shows "subst_term_multiset \<sigma> (convert_cond_into_term_multiset xs) =
  {#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset xs#}" using assms
  unfolding subst_term_multiset_def by (induct xs, auto)
    (smt (verit, best) Un_subset_iff convert_cond_into_term_multiset.elims funas_trs_union image_mset_is_empty_iff insert_def mset.simps(1))

lemma trans_reachable_cond_red_step:assumes "(P, Q) \<in> (cond_reduction_step)"
  and "(Q, T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])"
shows "(P, T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])" using assms by auto

lemma cond_red_combine_fun: assumes "({#Fun \<doteq> [s\<^sub>1 \<cdot> \<sigma>, t\<^sub>1 \<cdot> \<sigma>]#}, T (s\<^sub>1, t\<^sub>1)) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T (s\<^sub>1, t\<^sub>1). t = Fun \<top> [])" 
  and "({#Fun \<doteq> [s\<^sub>2 \<cdot> \<sigma>, t\<^sub>2 \<cdot> \<sigma>]#}, T (s\<^sub>2, t\<^sub>2)) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T (s\<^sub>2, t\<^sub>2). t = Fun \<top> [])" 
shows "({#Fun \<doteq> [s\<^sub>1 \<cdot> \<sigma>, t\<^sub>1 \<cdot> \<sigma>], Fun \<doteq> [s\<^sub>2 \<cdot> \<sigma>, t\<^sub>2 \<cdot> \<sigma>] #},
    T (s\<^sub>1, t\<^sub>1) + T (s\<^sub>2, t\<^sub>2)) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in># T (s\<^sub>1, t\<^sub>1) + T (s\<^sub>2, t\<^sub>2). t = Fun \<top> [])" using cond_red_combine_goal 
  by (smt (verit, ccfv_SIG) addFunT add_mset_add_single assms(1) assms(2) cond_red_add converse_rtrancl_into_rtrancl rtrancl_idemp union_commute)

lemma cond_red_combine_fun_mset: assumes "\<forall>(s\<^sub>i, t\<^sub>i)\<in># mset xs. ({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]#}, T (s\<^sub>i, t\<^sub>i)) \<in> (cond_reduction_step)\<^sup>*" 
  shows "({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset xs #},
    \<Sum>(u, v)\<in># mset xs. T (u, v)) \<in> (cond_reduction_step)\<^sup>*" using assms 
proof (induct xs)
  case (Cons pair xs)
  then show ?case using cond_red_combine_fun cond_red_add union_commute
    by auto (smt (verit) add_mset_add_single converse_rtrancl_into_rtrancl 
        rtrancl_idemp union_commute)
qed auto 

lemma normRR':"normalized R \<sigma> \<Longrightarrow> normalized R' \<sigma>" using R' unfolding normalized_def 
  by (metis (no_types, opaque_lifting) NF_anti_mono Un_subset_iff cstep_subset insert_absorb insert_subset subsetI)

lemma cstep_single_cond_reduction_step_eq: assumes uv:"(u::('f, 'v)term, v::('f, 'v)term) \<in> (cstep R')\<^sup>*"
  shows "(\<exists>T. ({#Fun \<doteq> [u, v]#}, T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))"
proof -
  from csteps_imp_csteps_n[OF uv] obtain n where st':"(u, v) \<in> (cstep_n R' n)\<^sup>*" by auto
  then show ?thesis 
  proof(induct n arbitrary: u v)
    case 0
    hence uv_eq:"u = v" by simp
    hence "({#Fun \<doteq> [v, v]#}, {#Fun (\<top>) []#}) \<in> (cond_reduction_step)\<^sup>*" unfolding cond_reduction_step.simps 
      using R' cond_red_refl by auto
    then show ?case using uv_eq by auto
  next
    case (Suc n)
    from Suc(2) show ?case
    proof(induct rule: converse_rtrancl_induct)
      case base
      then show ?case using Suc cond_red_refl by blast
    next
      case (step P Q)
      from step(3) obtain T' where T:"({#Fun \<doteq> [Q, v]#}, T') \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T'. t = Fun \<top> [])" by auto
      from step(1) obtain C rl \<sigma> where rl:"rl \<in> R'" and cond':"(\<forall> (s\<^sub>i, t\<^sub>i) \<in> set (snd rl). (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R' n)\<^sup>* )"
        and P:"P = C\<langle>(clhs rl) \<cdot> \<sigma>\<rangle>" and Q:"Q = C\<langle>(crhs rl) \<cdot> \<sigma>\<rangle>" 
        by (smt (verit, del_insts) case_prodD case_prodI2 cstep_n_SucE fst_conv snd_conv)
      have funas_rl:"funas_trs (set (snd rl)) \<subseteq> F" using rl unfolding funas_trs_def funas_rule_def 
        by (auto, metis (no_types, opaque_lifting) R_sig UnCI funas_crule_def funas_crule_included_ctrs lhs_wf  subset_iff)
          (metis (mono_tags, opaque_lifting) R_sig UnCI funas_crule_def funas_crule_included_ctrs rhs_wf subset_iff)
      let ?F = "\<lambda> q T. ({#Fun \<doteq> [(fst q)\<cdot> \<sigma>, (snd q)\<cdot> \<sigma>]#}, T) \<in> (\<Zinj>)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])"
      let ?S = "set (conds rl)"
      from cond' have "\<forall>pair\<in>?S. \<exists>T. ?F pair T" 
        using Suc by auto
      from bchoice[OF this]
      obtain T where cond_IH':"\<forall>pair\<in>?S. ?F pair (T pair)" by auto
      have "is_Fun (clhs rl)" using wf[unfolded wf_1ctrs_def] rl R' by fastforce
      hence hf:"hole_pos C \<in> fun_poss P" using P 
        by (metis hole_pos_poss is_VarE is_VarI poss_is_Fun_fun_poss subst_apply_eq_Var subt_at_hole_pos)
      let ?p = "0 # hole_pos C"
      let ?S = "{# Fun \<doteq> [P, v] #}"
      let ?s = "Fun \<doteq> [P, v]"
      let ?rl = rl
      let ?\<sigma> = \<sigma>
      let ?T = "(?S - {#?s#}) + {#replace_at ?s  ?p ((crhs ?rl) \<cdot> ?\<sigma>)#} + (subst_term_multiset ?\<sigma> (convert_cond_into_term_multiset (snd ?rl)))"
      have "?s |_ ?p = (clhs ?rl) \<cdot> ?\<sigma>" using P by auto
      have cond:"\<forall> (s\<^sub>i, t\<^sub>i) \<in> set (snd ?rl). (s\<^sub>i \<cdot> ?\<sigma>, t\<^sub>i \<cdot> ?\<sigma>) \<in> (cstep R')\<^sup>*" 
        using csteps_n_subset_csteps R' using cond' by blast
      have "rl \<in> R" using R' conditional_narrowing_axioms rl by fastforce
      have "?p \<in> fun_poss ?s" using hf by auto
      from cond' have cond:"\<forall> (s\<^sub>i, t\<^sub>i) \<in> set (snd ?rl). (s\<^sub>i \<cdot> ?\<sigma>, t\<^sub>i \<cdot> ?\<sigma>) \<in> (cstep R')\<^sup>*" 
        using csteps_n_subset_csteps R' by blast
      hence *:"\<forall> (s\<^sub>i, t\<^sub>i) \<in> set (snd ?rl). (s\<^sub>i \<cdot> ?\<sigma>, t\<^sub>i \<cdot> ?\<sigma>) \<in> (cstep R)\<^sup>*" 
      proof (auto)
        fix a :: "('f, 'v) Term.term" and b :: "('f, 'v) Term.term"
        assume a1: "\<forall>x\<in>set (conds rl). case x of (s\<^sub>i, t\<^sub>i) \<Rightarrow> (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep R')\<^sup>*"
        assume a2: "(a, b) \<in> set (conds rl)"
        obtain g :: "('f, 'v) Term.term \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> bool" where
          f3: "\<forall>x1 x2. g x2 x1 = ((x2 \<cdot> \<sigma>, x1 \<cdot> \<sigma>) \<in> (cstep R')\<^sup>*)" by fastforce
        then have "g a b" using a2 a1 by blast
        then show "(a \<cdot> \<sigma>, b \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
          using f3 by (metis (no_types) R' Un_insert_right cstep_subset rtrancl_mono subsetD subset_insertI sup_bot.right_neutral)
      qed
      have st_step:"(?S, ?T) \<in> cond_reduction_step" 
      proof - 
        have "?s \<in># {#Fun \<doteq> [P, v]#}" by simp
        moreover have "?rl \<in> R" using conditional_narrowing.R' conditional_narrowing_axioms rl by fastforce
        moreover have "?p \<in> fun_poss ?s" using hf by auto
        moreover have "?s |_ ?p = clhs ?rl \<cdot> ?\<sigma>" using \<open>Fun \<doteq> [P, v] |_ (0 # hole_pos C) = clhs rl \<cdot> \<sigma>\<close> by force
        moreover have "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set (snd ?rl). (s\<^sub>i \<cdot> ?\<sigma>, t\<^sub>i \<cdot> ?\<sigma>) \<in> (cstep R)\<^sup>*" using * by auto
        ultimately show ?thesis by blast
      qed
      from cond_IH' have cond_IH:"\<forall>(s\<^sub>i, t\<^sub>i)\<in> set (conds rl). ({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]#}, T (s\<^sub>i, t\<^sub>i) ) \<in> (\<Zinj>)\<^sup>* \<and> (\<forall>t\<in># T (s\<^sub>i, t\<^sub>i). t = Fun \<top> [])" by auto
      have "replace_at (Fun \<doteq> [P, v])  ?p ((crhs rl) \<cdot> \<sigma>) = (Fun \<doteq> [Q, v])" using Q by (auto simp add: P)
      hence "?T = {#Fun \<doteq> [Q, v]#} + (subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl)))" 
        by fastforce
      hence *:"({#Fun \<doteq> [P, v]#}, {#Fun \<doteq> [Q, v]#} + (subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl)))) \<in> cond_reduction_step" 
        using st_step by simp
      then show ?case
      proof(cases "snd rl = []")
        case True
        then show ?thesis using * T 
          by (metis converse_rtrancl_into_rtrancl convert_cond_into_term_multiset.simps(1) 
              empty_neutral(2) subst_term_multiset_empty)
      next
        case False
        hence sub_eq:"subst_term_multiset \<sigma> (convert_cond_into_term_multiset (snd rl)) =
                {#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset (snd rl)#}" 
          by (simp add: subst_convert_mset_equiv[OF False funas_rl] )
        hence **:"({#Fun \<doteq> [P, v]#}, {#Fun \<doteq> [Q, v]#} + {#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset (snd rl)#}) \<in> cond_reduction_step"
          unfolding cond_reduction_step_def  subst_term_multiset_def using * sub_eq cond_reduction_stepp_cond_reduction_step_eq by fastforce 
        let ?W = "\<Sum>(u, v)\<in># mset (snd rl). T (u, v)"
        have IH:"(\<forall>(s\<^sub>i, t\<^sub>i) \<in># mset (snd rl). ({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]#}, T (s\<^sub>i, t\<^sub>i)) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T (s\<^sub>i, t\<^sub>i). t = Fun \<top> []))" 
          using cond_IH by auto
        have "(\<exists>W. ({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset (snd rl)#}, W) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#W. t = Fun \<top> []))"
        proof (rule exI[of _ ?W], auto split:prod.splits, goal_cases)
          case 1
          have "\<forall>(s\<^sub>i, t\<^sub>i) \<in># mset (snd rl). ({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]#}, T (s\<^sub>i, t\<^sub>i)) \<in> (cond_reduction_step)\<^sup>*" using IH by auto
          from cond_red_combine_fun_mset[OF this]
          show ?case by simp
        next
          case (2 a b t)
          then show ?case using cond_IH' by auto 
        qed 
        then obtain W where W:"({#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset (snd rl)#}, W) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#W. t = Fun \<top> [])" by auto
        from cond_red_combine_goal[OF T W]
        have "\<exists>F. ({#Fun \<doteq> [Q, v]#} + {#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset (conds rl)#}, F)
            \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#F. t = Fun \<top> [])" by auto
        then obtain F where F:"({#Fun \<doteq> [Q, v]#} + {#Fun \<doteq> [s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>]. (s\<^sub>i, t\<^sub>i) \<in># mset (conds rl)#}, F)
            \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#F. t = Fun \<top> [])" by auto
        from trans_reachable_cond_red_step[OF ** F]
        show ?thesis by (meson r_into_rtrancl)
      qed
    qed
  qed
qed

lemma funas_preserve_cstep: assumes fun_u:"funas_term u \<subseteq> F"
  and uv:"(u, v) \<in> (cstep R')\<^sup>*"
shows "funas_term v \<subseteq> F" using uv 
proof (induct, insert fun_u)
  case base
  then show ?case by (simp add: assms(1))
next
  case (step y z)
  from \<open>(y, z) \<in> cstep R'\<close> obtain n where "(y, z) \<in> cstep_n R' n" 
    by (meson cstep_iff)
  hence "(y, z) \<in> {(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) | C l r \<sigma> cs.
      ((l, r), cs) \<in> R' \<and> (\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R' (n - 1))\<^sup>*)}"
    by (metis cstep_n_Suc Suc_diff_1 cstep_n.simps(1) empty_iff not_gr_zero)
  then show ?case using R_sig R' step.hyps(3) unfolding funas_ctrs_def funas_trs_def
      funas_crule_def funas_rule_def by (auto, force split:prod.splits) 
      (metis (no_types, lifting) SUP_le_iff Un_subset_iff fst_conv 
        insert_Diff insert_subset snd_conv wf_F_subst)  
qed

lemma funas_cstep_R':assumes funas_u:"funas_term u \<subseteq> F"
  and funas_v:"funas_term v \<subseteq> F"
  and uv:"(u, v) \<in> (cstep R)\<^sup>*" 
shows "(u, v) \<in> (cstep R')\<^sup>*" using uv
proof (induct, insert funas_u funas_v)
  case base
  then show ?case by simp
next
  case (step y z)
  note funas_defs = funas_ctrs_def funas_crule_def funas_rule_def funas_trs_def
  from \<open>(u, y) \<in> (cstep R')\<^sup>*\<close> have funas_y:"funas_term y \<subseteq> F"
    by (simp add:funas_preserve_cstep[OF funas_u \<open>(u, y) \<in> (cstep R')\<^sup>*\<close>])
  from funas_term_restrict[OF funas_y \<open>(y, z) \<in> cstep R\<close>]
  have "(y, z) \<in> cstep R'" by auto
  hence yz:"(y, z) \<in> (cstep R')\<^sup>*" by auto
  hence "funas_term z \<subseteq> F" 
    by (simp add:funas_preserve_cstep[OF funas_y yz])
  then show ?case using funas_u using step yz by auto 
qed

lemma cstep_cond_reduction_step_eq: fixes C::"('f, 'v) condition list"
  assumes funas_A:"funas_trs (set C) \<subseteq> F"
    and "\<forall>u v. (u, v) \<in> set C \<longrightarrow> ((u, v) \<in> (cstep R)\<^sup>* \<and> v \<in> NF(cstep R))"
    and qro: "quasi_decreasing_order R S"
    and nfp:"CR (cstep R)"
  shows "(\<exists>T. ({#Fun \<doteq> [u, v]. (u, v) \<in># mset C#}, T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))" using assms
proof(induct C)
  case Nil
  then show ?case by auto
next
  case (Cons pair C)
  hence ftA:"funas_trs (set C) \<subseteq> F" unfolding funas_trs_def funas_rule_def by auto
  from Cons have *:"\<forall>u v. (u, v) \<in> set C \<longrightarrow> ((u, v) \<in> (cstep R)\<^sup>* \<and> v \<in> NF(cstep R))" by auto
  obtain u v where pair:"pair = (u, v)" by (meson surj_pair)
  have funas_u:"funas_term u \<subseteq> F" by (metis Cons.prems(1) lhs_wf list.set_intros(1) pair)
  have funas_v:"funas_term v \<subseteq> F" by (metis Cons.prems(1) list.set_intros(1) pair rhs_wf)
  have uvR:"(u, v) \<in> (cstep R)\<^sup>*" using Cons by (simp add: pair)
  hence uv:"(u, v) \<in> (cstep R')\<^sup>*" 
    by (simp add:funas_cstep_R'[OF funas_u funas_v uvR])
  obtain T where **:"({#Fun \<doteq> [u, v]. (u, v) \<in># mset C#}, T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" 
    using Cons * ftA by auto
  have "v \<in> NF(cstep R)" using Cons pair by auto
  hence v:"v \<in> NF(cstep R')" by (meson normRR' normalized_def)
  hence uvv:"(u, v) \<in> (cstep R')\<^sup>* \<and> v \<in> NF(cstep R')" using uv v by auto
  from cstep_single_cond_reduction_step_eq
  obtain T' where ***:"({#Fun \<doteq> [u, v]#}, T') \<in> (\<Zinj>)\<^sup>* \<and> (\<forall>t\<in>#T'. t = Fun \<top> [])" using qro uv v by blast
  have cond_step_ctxt1:"({#Fun \<doteq> [u, v]#} + {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset C#},   
    T'+ {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset C#}) \<in> (\<Zinj>)\<^sup>*" 
    using *** cond_red_add by blast
  have cond_step_ctxt2:"(T'+ {#Fun \<doteq> [u1, v1]. (u1, v1) \<in># mset C#}, T' + T) \<in> (\<Zinj>)\<^sup>*" using cond_red_add ** add.commute by metis
  show ?case by (auto split:prod.splits, rule exI[of _ "T' + T"], insert ** *** pair addFunT[of T' T] 
        cond_step_ctxt1 cond_step_ctxt2, fastforce)
qed                                                                                        

lemma subst_Fun_mset_equiv: fixes \<tau>::"('f, 'v)subst"
  shows "{#t \<cdot> \<tau>. t \<in># {#Fun \<doteq> [u, v]. (u, v) \<in># mset S#}#} = {#Fun \<doteq> [u \<cdot> \<tau>, v \<cdot> \<tau>]. (u, v) \<in># mset S#}"
proof(induct S)
  case Nil
  then show ?case by auto
next
  case (Cons p S)
  then show ?case by (auto split:prod.splits)
qed

lemma cstep_cond_red_equiv:
  assumes funas_A:"funas_trs (set C) \<subseteq> F"
    and cstep_A:"\<exists>\<tau>. (\<forall>u v. ((u, v) \<in> set C) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (cstep R)\<^sup>* ))"
    and qro: "quasi_decreasing_order R S"
    and cr: "CR (cstep R)"
    and sti:"\<forall> (u, v) \<in> set C. strongly_irreducible R v"
  shows "\<exists>\<theta> T. normalized R \<theta> \<and> (subst_term_multiset \<theta> (convert_cond_into_term_multiset C), T) \<in> (cond_reduction_step)\<^sup>*
          \<and> (\<forall> t \<in># T. t = Fun (\<top>) [])" using assms
proof(induct C)
  case Nil
  hence nVar:"normalized R Var" using wf[unfolded wf_1ctrs_def] 
    by (simp add: Conditional_Rewriting.empty_subst_normalized) 
  show ?case unfolding subst_term_multiset_def
    by (rule exI[of _ Var], rule exI[of _ "convert_cond_into_term_multiset []"], insert nVar, auto)
next
  case (Cons pair U)
  obtain u v where pair:"pair = (u, v)" using surjective_pairing by blast
  from funas_A have funU:"funas_trs (set U) \<subseteq> F" unfolding funas_trs_def funas_rule_def 
    using Cons by (meson lhs_wf rhs_wf subsetD subset_insertI, simp add: funas_rule_def funas_trs_def) 
  have cstepU':"\<exists>\<tau>. (\<forall>s t. ((s, t) \<in> set ((u, v) # U)) \<longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)" 
    using assms Cons pair by auto
  then obtain \<tau> where \<tau>:"\<forall>s t. ((s, t) \<in> set ((u, v) # U)) \<longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"  by auto
  then obtain \<tau>' where \<tau>':"\<tau>' = (\<lambda>x. some_NF (cstep R) (\<tau> x))" using quasi_decreasing_obtains_normalized_subst [OF qro] by auto
  hence norm\<tau>':"normalized R \<tau>'" using \<tau>' qro quasi_decreasing_obtains_normalized_subst by blast
  have cstep\<tau>':"\<forall>s t. ((s, t) \<in> set ((u, v) # U)) \<longrightarrow> (s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" 
  proof(intro impI allI)
    fix s t
    assume asm:"(s, t) \<in> set ((u, v) # U)"
    hence srt:"strongly_irreducible R t" using Cons(6) pair by auto
    hence *:"(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*" using \<tau> asm by auto
    have "(s \<cdot> \<tau>, s \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" using \<tau>'  by (metis qro quasi_decreasing_obtains_normalized_subst substs_csteps)
    moreover have "(t \<cdot> \<tau>, t \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" using \<tau>'  by (metis qro quasi_decreasing_obtains_normalized_subst substs_csteps)
    moreover have "t \<cdot> \<tau>' \<in> NF (cstep R)" using srt[unfolded strongly_irreducible_def] norm\<tau>' by auto
    moreover have "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (cstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
      by (meson * calculation(1) calculation(2) meetI meet_imp_conversion rtrancl_trans subset_iff)
    ultimately show "(s \<cdot> \<tau>', t \<cdot> \<tau>') \<in> (cstep R)\<^sup>*" using cr[unfolded CR_on_def] 
      by (meson CR_NF_conv cr normalizability_E)
  qed
  have ft\<tau>':"funas_trs (set (subst_condition_list \<tau>' ((u, v) # U))) \<subseteq> F" 
    unfolding subst_condition_list_def[unfolded subst_equation_def] funas_trs_def funas_rule_def
    using wf_F_subst Cons(2) pair lhs_wf rhs_wf funas_A funU by (auto, smt (verit, ccfv_SIG) insertCI lhs_wf subsetD, 
        smt (verit, best) insertCI rhs_wf subsetD, blast, smt (verit) rhs_wf subsetD)
  have sruv:"\<forall>(s, t) \<in> set ((u, v) # U). strongly_irreducible R t" using Cons(6) pair by auto
  show ?case
  proof(rule exI[of _ \<tau>'], auto split:prod.splits, goal_cases)
    case (1 x1 x2)
    then show ?case 
      using norm\<tau>' by auto
  next
    case (2 x1 x2)
    have pair:"x1 = u \<and> x2 = v" using 2 pair by force
    have *:"\<forall>s t. (s, t) \<in> set (subst_condition_list \<tau>' ((u, v) # U)) \<longrightarrow> (s, t) \<in> (cstep R)\<^sup>*" 
      using cstep\<tau>' unfolding subst_condition_list_def[unfolded subst_equation_def] by auto 
    have nfcond:"\<forall>(s, t) \<in> set (subst_condition_list \<tau>' ((u, v) # U)). t \<in> NF (cstep R)" using cstep\<tau>' norm\<tau>' \<tau> sruv
      unfolding subst_condition_list_def[unfolded subst_equation_def] strongly_irreducible_def by auto
    from cstep_cond_reduction_step_eq[of "subst_condition_list \<tau>' ((u, v) # U)"]
    obtain T where **:"(({#Fun \<doteq> [u, v]. (u, v) \<in># mset (subst_condition_list \<tau>' ((u, v) # U)) #}, T) \<in> 
      (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))" using * ft\<tau>' nfcond qro cr by force
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
    show ?case  unfolding subst_term_multiset_def subst_condition_list_def using ** pair 
      by (simp add:subst_condition_list_def subst_equation_def, insert equiv, auto) 
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

lemma infeasibility_using_conditional_narrowing: assumes wf_S:"wf_equational_term_mset S"
  and "\<not> (\<exists>\<sigma> S'. cond_narrowing_derivation S S' \<sigma> \<and> (\<forall> s \<in># S'. s = Fun (\<top>) []))"
shows "\<not> (\<exists>\<theta> T. normalized R \<theta> \<and> (subst_term_multiset \<theta> S, T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []))"
proof(rule ccontr)
  assume asm:"\<not>?thesis"
  hence "\<exists>\<theta> T. normalized R \<theta> \<and> (subst_term_multiset \<theta> S, T) \<in> cond_reduction_step\<^sup>* \<and> (\<forall> t \<in>#  T. t = Fun (\<top>) [])" by auto
  then obtain \<theta> T  where norm\<theta>:"normalized R \<theta>" and relsteps:"(subst_term_multiset \<theta> S, T) \<in> cond_reduction_step\<^sup>*" 
    and condsat:"\<forall> t \<in># T. t = Fun (\<top>) []"  by auto
  let ?V = "vars_term_set (set_mset S) \<union> subst_domain \<theta>"
  have "finite (vars_term_set (set_mset S))" unfolding vars_term_set_def by simp
  moreover have "finite (subst_domain \<theta>)" using finite_subst_domain by simp
  ultimately have fV:"finite ?V" by simp
  have "wf_equational_term_mset T" unfolding wf_equational_term_mset_def[unfolded wf_equational_term_def] 
    using condsat by auto
  define U where U:"U = subst_term_multiset \<theta> S" 
  have wf_U:"wf_equational_term_mset U" using wf_eq_mset_subst_inv by (simp add: U wf_S)
  have reltran:"(U, T) \<in> cond_reduction_step\<^sup>*" using relsteps by (simp add: U)
  from conditional_lifting_lemma [OF norm\<theta> wf_S U, of ?V T ]
  have "\<exists>\<sigma> \<theta>' S'. cond_narrowing_derivation S S' \<sigma> \<and> subst_term_multiset \<theta>' S' = T \<and> normalized R \<theta>' \<and> wf_equational_term_mset S'" using asm fV reltran by blast
  then obtain \<theta>' S' where cond:"\<exists>\<sigma>. cond_narrowing_derivation S S' \<sigma>" and sub:"subst_term_multiset \<theta>' S' = T" and "normalized R \<theta>'"
    and T:"\<forall> t \<in># T. t = Fun (\<top>) []" and wfS':"wf_equational_term_mset S'" using condsat by blast
  from T have *:"\<forall>t \<in># T. wf_equational_term t" unfolding wf_equational_term_def by auto
  from sub[unfolded subst_term_multiset_def]
  have *:"{#t \<cdot> \<theta>'. t \<in># S'#} = T" by auto
  have "(\<forall>u v \<theta>. Fun \<doteq> [u, v] \<cdot> \<theta> \<noteq> Fun (\<top>) [])" using wf_eq_subst by simp
  from wfS'[unfolded wf_equational_term_mset_def[unfolded wf_equational_term_def]]
  have "\<forall>t\<in>#S'. t = Fun \<top> []" using * using wf_eq_subst using condsat by fastforce
  then show False using assms cond by auto
qed

definition "cond_narrowing_based_infeasible C \<longleftrightarrow> (\<not> (\<exists>\<sigma> S'. cond_narrowing_derivation (convert_cond_into_term_multiset C) S' \<sigma> \<and> 
    (\<forall> s \<in># S'. s = Fun (\<top>) [])))"

definition "cond_narrowing_reaches_success C \<longleftrightarrow> (\<exists>\<sigma> S'. cond_narrowing_derivation (convert_cond_into_term_multiset C) S' \<sigma> \<and> 
    (\<forall> s \<in># S'. s = Fun (\<top>) []))"

definition "infeasibility C \<longleftrightarrow> (\<not> (\<exists>\<tau>. (\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)))"

definition "reachability C \<longleftrightarrow>  (\<exists>\<tau>. (\<forall>u v. (u, v) \<in> set C \<longrightarrow> (u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (cstep R)\<^sup>*))"

theorem cond_narrowing_based_infeasibility: assumes qro: "quasi_decreasing_order R S"
  and cr: "CR (cstep R)"
  and funas_C:"funas_trs (set C) \<subseteq> F"
  and sti:"\<forall> (u, v) \<in> set C. strongly_irreducible R v"
shows "\<not> cond_narrowing_reaches_success C \<Longrightarrow> infeasibility C" 
proof -
  note funas_defs = funas_crule_def funas_trs_def funas_rule_def
  assume "\<not> cond_narrowing_reaches_success C"
  hence ncs:"(\<not> (\<exists>\<sigma> S'. cond_narrowing_derivation (convert_cond_into_term_multiset C) S' \<sigma> \<and> 
    (\<forall> s \<in># S'. s = Fun (\<top>) [])))" unfolding cond_narrowing_reaches_success_def by simp
  from convert_cond_into_rule_list_sound[OF funas_C]
  have wfC:"wf_equational_term_mset (convert_cond_into_term_multiset C)" by auto
  from infeasibility_using_conditional_narrowing[OF wfC ncs]
  have *:"\<not> (\<exists>\<theta> T V. normalized R \<theta> \<and> (subst_term_multiset \<theta> (convert_cond_into_term_multiset C), T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []) \<and>
      vars_term_set (set_mset (convert_cond_into_term_multiset C)) \<union> subst_domain \<theta> \<subseteq> V \<and> finite V)" by auto
  show ?thesis
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "\<not> funas_trs (set C) \<subseteq> F \<or> (\<exists>\<tau>. (\<forall>u v. ((u, v) \<in> set C) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)))"
      unfolding infeasibility_def by auto
    with funas_C have **:"(\<exists>\<tau>. (\<forall>u v. ((u, v) \<in> set C) \<longrightarrow> ((u \<cdot> \<tau>, v \<cdot> \<tau>) \<in> (cstep R)\<^sup>*)))" by auto
    from cstep_cond_red_equiv[OF funas_C ** qro cr sti]
    have "\<exists>\<theta> T. normalized R \<theta> \<and> (subst_term_multiset \<theta> (convert_cond_into_term_multiset C), T) \<in> (\<Zinj>)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" by auto
    then obtain \<theta> T where ***:"normalized R \<theta> \<and> (subst_term_multiset \<theta> (convert_cond_into_term_multiset C), T) \<in> (\<Zinj>)\<^sup>* \<and> (\<forall>t\<in>#T. t = Fun \<top> [])" by auto
    let ?V = "vars_term_set (set_mset (convert_cond_into_term_multiset C)) \<union> subst_domain \<theta>"
    from *** have "normalized R \<theta>" by auto
    have "finite (subst_domain \<theta>)" using finite_subst_domain by simp
    hence fV:"finite ?V" by (metis List.finite_set finite_UnI set_vars_trs_list vars_seq_term_set_equiv)
    have "(\<exists>\<theta> T V. normalized R \<theta> \<and> (subst_term_multiset \<theta> (convert_cond_into_term_multiset C), T) \<in> (cond_reduction_step)\<^sup>* \<and> (\<forall> t \<in># T. t = Fun (\<top>) []) \<and>
      vars_term_set (set_mset (convert_cond_into_term_multiset C)) \<union> subst_domain \<theta> \<subseteq> V \<and> finite V)"
      by (rule exI[of _ \<theta>], rule exI[of _ T], rule exI[of _ ?V], insert fV * ***, auto)
    then show False using * by auto
  qed
qed

end

end