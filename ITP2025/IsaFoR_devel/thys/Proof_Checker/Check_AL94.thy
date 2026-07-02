(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_AL94
  imports
    CTRS.AL94
    CTRS.Conditional_Rewriting_Impl
    Check_Infeasibility
    Show.Shows_Literal
begin

hide_const (open) Ramsey.choice
hide_const (open) CP.overlap
hide_fact (open) CP.overlap_def

no_notation Matrix.scalar_prod  (infix "\<bullet>" 70)
no_notation Inner_Product.real_inner_class.inner (infix "\<bullet>" 70)

lemma mgu_vd_string_not_unifiable:
  fixes s t :: "('f, string) term"
  assumes *: "mgu_vd_string s t = None"
  shows "\<forall>\<pi>. vars_term (\<pi> \<bullet> t) \<inter> vars_term s = {} \<longrightarrow> \<not> unifiable {(s, \<pi> \<bullet> t)}"
proof -
  let ?f = "map_vars_term x_var"
  let ?g = "map_vars_term y_var"

  have disj: "vars_term (?f s) \<inter> vars_term (?g t) = {}"
    by (auto simp: term.set_map)
  have "inj x_var" and "inj y_var" by auto
  then have "bij_betw x_var (vars_term s) (x_var ` vars_term s)"
    and "bij_betw y_var (vars_term t) (y_var ` vars_term t)"
    by (auto intro: inj_on_imp_bij_betw)
  with bij_betw_extend [of x_var "vars_term s" "x_var ` vars_term s" UNIV]
    and bij_betw_extend [of y_var "vars_term t" "y_var ` vars_term t" UNIV]
    obtain f and g where "bij f" and "bij g" and "finite {x. f x \<noteq> x}" and "finite {x. g x \<noteq> x}"
      and "\<forall>x \<in> vars_term s. f x = x_var x"
      and "\<forall>x \<in> vars_term t. g x = y_var x"
      by auto
  moreover then have "s \<cdot> (Var \<circ> f) = ?f s" and "t \<cdot> (Var \<circ> g) = ?g t"
    using term_subst_eq [of s "Var \<circ> f" "Var \<circ> x_var"]
      and term_subst_eq [of t "Var \<circ> g" "Var \<circ> y_var"]
      by (induct s) (auto simp: map_vars_term_eq)
  moreover define \<pi>\<^sub>1 \<pi>\<^sub>2 where "\<pi>\<^sub>1 \<equiv> Abs_perm f" and "\<pi>\<^sub>2 \<equiv> Abs_perm g"
  ultimately have "vars_term (\<pi>\<^sub>1 \<bullet> s) \<inter> vars_term (\<pi>\<^sub>2 \<bullet> t) = {}"
    using disj
    using term_apply_subst_Var_Abs_perm [symmetric, of f s]
    using term_apply_subst_Var_Abs_perm [symmetric, of g t]
    by (auto simp: perms_def)
  then have "-\<pi>\<^sub>1 \<bullet> (vars_term (\<pi>\<^sub>1 \<bullet> s) \<inter> vars_term (\<pi>\<^sub>2 \<bullet> t)) = {}" by auto
  moreover define \<pi> where "\<pi> \<equiv> -\<pi>\<^sub>1 + \<pi>\<^sub>2"
  ultimately have **: "vars_term s \<inter> vars_term (\<pi> \<bullet> t) = {}" by (auto simp: eqvt)

  from mgu_vd_string_complete [of s \<mu> t "sop \<pi> \<circ>\<^sub>s \<mu>" for \<mu>] and *
    have ***: "\<not> unifiable {(s, \<pi> \<bullet> t)}" by (auto simp: unifiable_def unifiers_def)

  text \<open>now use @{thm disj_vars_not_unifiable}\<close>
  show ?thesis
    using disj_vars_not_unifiable [of \<pi> t s] and ** and *** by (auto)
qed

definition abs_irr :: "('f, string) crules \<Rightarrow> ('f, string) term \<Rightarrow> bool"
where
  "abs_irr rs v \<longleftrightarrow> (\<forall>\<rho> \<in> set rs. \<forall>p \<in> fun_poss v. mgu_vd_string (v |_ p) (clhs \<rho>) = None)"

lemma abs_irr_absolutely_irreducible:
  assumes "abs_irr R' t"
  shows "absolutely_irreducible (set R') t"
proof -
  from assms [unfolded abs_irr_def] mgu_vd_string_not_unifiable
    show ?thesis unfolding absolutely_irreducible_def by blast
qed

definition abs_det :: "('f, string) crules \<Rightarrow> bool"
where
  "abs_det rs \<longleftrightarrow> (\<forall>\<rho> \<in> set rs. \<forall>(u, v) \<in> set (conds \<rho>). abs_irr rs v)"

lemma abs_det_absolutely_deterministic:
  assumes "abs_det R'"
  shows "absolutely_deterministic (set R')"
proof -
  from assms [unfolded abs_det_def] abs_irr_absolutely_irreducible
    show ?thesis unfolding absolutely_deterministic_def by blast
qed

definition check_airr :: "('f :: showl, string) crules \<Rightarrow> ('f, string) term \<Rightarrow> showsl check"
where
  "check_airr R t = do {
    check_allm
      (\<lambda>cr.
       check_allm
         (\<lambda>p.
           check (mgu_vd_string (t |_ p) (clhs cr) = None)
             (showsl_lit (STR ''the term '') \<circ> showsl t \<circ> showsl_lit (STR '' is unifiable with the left-hand side of rule '') 
             \<circ> showsl_crule cr \<circ> showsl_lit (STR '' at position '') \<circ> showsl_pos p)
         ) (fun_poss_list t)
      ) R
  } <+? (\<lambda>e. showsl_lit (STR ''the term '') \<circ> showsl t \<circ> showsl_lit (STR '' is not absolutely irreducible'') \<circ> e)"

definition check_adtrs :: "('f :: showl, string) crules \<Rightarrow> showsl check"
where
  "check_adtrs R = do {
    check_allm
     (\<lambda>cr.
      check_allm
       (\<lambda>i.
        let v = snd (snd cr ! i) in check_airr R v
       ) [0..<length (snd cr)]
     ) R
  } <+? (\<lambda>e. showsl_lit (STR ''the CTRS is not absolutely deterministic\<newline>'') \<circ> e)"

lemma check_airr':
  "isOK (check_airr R t) = abs_irr R t"
by (auto simp: check_airr_def abs_irr_def)

lemma check_adtrs':
  "isOK (check_adtrs R) = abs_det R"
by (auto simp: check_airr' check_adtrs_def abs_det_def case_prod_unfold atLeast0LessThan)
   (metis in_set_idx lessThan_iff snd_conv)

lemma check_airr:
  assumes "isOK (check_airr R t)"
  shows "absolutely_irreducible (set R) t"
using abs_irr_absolutely_irreducible [OF check_airr' [THEN iffD1, OF assms]] .

lemma check_adtrs:
  assumes "isOK (check_adtrs R)"
  shows "absolutely_deterministic (set R)"
using abs_det_absolutely_deterministic [OF check_adtrs' [THEN iffD1, OF assms]] .

definition
  "qdstep R s t = (\<exists>l r cs \<sigma> i. ((l, r), cs) \<in> R \<and> i < length cs \<and> s = l \<cdot> \<sigma> \<and>
    t = fst (cs ! i) \<cdot> \<sigma> \<and> (\<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*))"

lemma qdstepE:
  assumes "qdstep R s t"
  obtains l r cs \<sigma> i where "((l, r), cs) \<in> R" and "i < length cs" and "s = l \<cdot> \<sigma>"
    and "t = fst (cs ! i) \<cdot> \<sigma>" and "\<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
using assms unfolding qdstep_def by blast

lemma qdstepI:
  assumes "((l, r), cs) \<in> R" and "i < length cs" and "s = l \<cdot> \<sigma>"
    and "t = fst (cs ! i) \<cdot> \<sigma>" and "\<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  shows "qdstep R s t"
using assms unfolding qdstep_def by blast

lemma qdstep_eqvt:
  "\<pi> \<bullet> {(s, t). qdstep R s t} = {(s, t). qdstep (\<pi> \<bullet> R) s t}" (is "_ = ?S (\<pi> \<bullet> R)")
proof (intro equalityI subrelI)
  fix s t assume "(s, t) \<in> \<pi> \<bullet> ?S R"
  then have "(-\<pi> \<bullet> s, -\<pi> \<bullet> t) \<in> ?S R"
    by (metis rule_pt.permute_prod.simps trs_pt.inv_mem_simps(1))
  then show "(s, t) \<in> ?S (\<pi> \<bullet> R)"
    apply (auto elim!: qdstepE)
    apply (rule_tac l = "\<pi> \<bullet> l" and r = "\<pi> \<bullet> r" and cs = "\<pi> \<bullet> cs" and \<sigma> = "sop (-\<pi>) \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop \<pi>" and i = i in qdstepI)
    apply (auto simp: eqvt [symmetric])
    apply (metis (no_types, lifting) crule_pt.permute_prod.simps ctrs_pt.inv_mem_simps(1) rule_pt.permute_prod.simps rules_pt.permute_list_def rules_pt.permute_minus_cancel(2) term_pt.permute_minus_cancel(2))
    apply (metis term_pt.permute_minus_cancel(1))
    apply (metis term_pt.permute_minus_cancel(1))
    unfolding rule_pt.permute_prod.simps term_apply_subst_Var_Rep_perm [symmetric]
    by (meson cstep_subst rtrancl_map)
next
  fix s t assume "(s, t) \<in> ?S (\<pi> \<bullet> R)"
  then have "(-\<pi> \<bullet> s, -\<pi> \<bullet> t) \<in> ?S R"
    apply (auto elim!: qdstepE)
    apply (rule_tac l = "-\<pi> \<bullet> l" and r = "-\<pi> \<bullet> r" and cs = "-\<pi> \<bullet> cs" and \<sigma> = "sop \<pi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop (-\<pi>)" in qdstepI)
    apply (auto simp: eqvt)
    apply (metis crule_pt.permute_prod.simps ctrs_pt.inv_mem_simps(1) rule_pt.permute_prod.simps rules_pt.permute_list_def)
    apply (auto simp: eqvt [symmetric])
    by (simp add: cstep_permute csteps_eqvt)
  then show "(s, t) \<in> \<pi> \<bullet> ?S R"
    using inv_rule_mem_trs_simps(2) by blast
qed

lemma qdstep_permute: "qdstep (\<pi> \<bullet> R) = qdstep R"
apply (intro ext)
apply (auto elim!: qdstepE)
apply (rule_tac l = "-\<pi> \<bullet> l" and r = "-\<pi> \<bullet> r" and cs = "-\<pi> \<bullet> cs" and \<sigma> = "sop \<pi> \<circ>\<^sub>s \<sigma>" in qdstepI)
apply (auto simp: eqvt [symmetric])
apply (metis crule_pt.permute_prod.simps ctrs_pt.inv_mem_simps(1) rules_pt.permute_list_def)
apply (rule_tac l = "\<pi> \<bullet> l" and r = "\<pi> \<bullet> r" and cs = "\<pi> \<bullet> cs" and \<sigma> = "sop (-\<pi>) \<circ>\<^sub>s \<sigma>" in qdstepI)
apply (auto simp: eqvt [symmetric])
by (metis crule_pt.permute_prod.simps ctrs_pt.mem_permute_iff rules_pt.permute_list_def)

lemma quasi_decreasing':
  assumes "quasi_decreasing R"
  shows "quasi_decreasing_order R ((cstep R \<union> {\<rhd>} \<union> {(s, t). qdstep R s t})\<^sup>+)"
    (is "quasi_decreasing_order _ ?S")
proof -
  from assms obtain S where qd: "quasi_decreasing_order R S" by (auto simp: quasi_decreasing_def)
  then have [dest]: "\<And>x y. (x, y) \<in> cstep R \<Longrightarrow> (x, y) \<in> S" and trans: "trans S" and SN: "SN S"
    and [dest]: "\<And>x y. x \<rhd> y \<Longrightarrow> (x, y) \<in> S"
    by (auto simp: quasi_decreasing_order_def)
  have [dest]: "qdstep R x y \<Longrightarrow> (x, y) \<in> S" for x y using qd
    by (auto simp: quasi_decreasing_order_def elim!: qdstepE)
  { fix s t
    assume "(s, t) \<in> ?S"
    then have "(s, t) \<in> S" by (induct) (auto dest: transD [OF trans])
  }
  then have "SN ?S" by (intro SN_subset [OF SN, of ?S]) auto
  moreover have "trans ?S" and "cstep R \<subseteq> ?S" and "{\<rhd>} \<subseteq> ?S" by auto
  moreover have "\<forall> l r cs \<sigma>. ((l, r), cs) \<in> R \<longrightarrow>
    (\<forall> i. i < length cs \<longrightarrow> (\<forall>j < i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>* ) \<longrightarrow>
      (l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> ?S)" by (auto dest: qdstepI)
  ultimately show ?thesis by (auto simp: quasi_decreasing_order_def)
qed

lemma subst_closed_qdstep [intro]:
  "subst.closed {(s, t). qdstep R s t}"
proof
  fix s t \<tau> presume "qdstep R s t"
  then obtain l r cs \<sigma> i where "((l, r), cs) \<in> R" and "i < length cs" and "s = l \<cdot> \<sigma>"
    and "t = fst (cs ! i) \<cdot> \<sigma>" and "\<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
    by (blast elim: qdstepE)
  then have "qdstep R (s \<cdot> \<tau>) (t \<cdot> \<tau>)"
    using subst.closed_rtrancl [OF subst_closed_cstep, of R]
    by (intro qdstepI [of l r cs R i _ "\<sigma> \<circ>\<^sub>s \<tau>"]) auto
  then show "(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> {(s, t). qdstep R s t}" by blast
qed blast

lemma subst_closed_cstep_Un_supt_Un_qdstep:
  "subst.closed ((cstep R \<union> {\<rhd>} \<union> {(s, t). qdstep R s t})\<^sup>+)"
by force

abbreviation perm_Inr :: "('v::infinite) perm \<Rightarrow> ('f + 'v, 'v) term \<Rightarrow> ('f + 'v, 'v) term"
where
  "perm_Inr \<pi> \<equiv> map_funs_term (case_sum Inl (Inr \<circ> ((\<bullet>) \<pi>)))"

lemma skol_perm:
  fixes C :: "'v::infinite set"
  shows "skol (\<pi> \<bullet> C) (\<pi> \<bullet> t) = perm_Inr \<pi> (\<pi> \<bullet> (skol C t))"
  by (induct t) (auto simp: eqvt [symmetric])

lemma perm_skol:
  fixes C :: "'v::infinite set"
  shows "\<pi> \<bullet> skol C t = perm_Inr (- \<pi>) (skol (\<pi> \<bullet> C) (\<pi> \<bullet> t))"
  by (induct C t rule: skol.induct) (auto simp: eqvt [symmetric])

lemma inj_perm_Inr':
  "inj (case_sum Inl (Inr \<circ> (permute_atom \<pi>)))"
apply (auto simp: inj_on_def split: sum.splits)
by (metis Rep_perm_simps(1) Rep_perm_simps(2) id_apply left_minus o_apply permute_atom_def)

lemma map_funs_crule_comp:
  "map_funs_crule f (map_funs_crule g r) = map_funs_crule (f \<circ> g) r"
  "(map_funs_crule f \<circ>\<circ> map_funs_crule) g = map_funs_crule (f \<circ> g)"
  by (auto simp: map_funs_term_comp map_funs_crule_def)

lemma cstep_iff_map_cstep:
  assumes "inj h"
  shows "(s, t) \<in> cstep R \<longleftrightarrow> (map_funs_term h s, map_funs_term h t) \<in> cstep (map_funs_ctrs h R)"
proof
  assume "(s, t) \<in> cstep R"
  then show "(map_funs_term h s, map_funs_term h t) \<in> cstep (map_funs_ctrs h R)"
    by (rule cstep_imp_map_cstep)
next
  let ?h = "the_inv h"
  have id: "(the_inv h) \<circ> h = id" using assms
    by (simp add: fun_comp_eq_conv the_inv_into_f_f)
  assume "(map_funs_term h s, map_funs_term h t) \<in> cstep (map_funs_ctrs h R)"
  then have "(map_funs_term ?h (map_funs_term h s), map_funs_term ?h (map_funs_term h t)) \<in>
    cstep (map_funs_ctrs ?h (map_funs_ctrs h R))" by (rule cstep_imp_map_cstep)
  also have "(map_funs_term ?h (map_funs_term h s), map_funs_term ?h (map_funs_term h t)) = (s,t)" 
    using map_funs_crule_comp[of ?h h, unfolded id] map_funs_term_comp[of ?h h, unfolded id] by auto
  also have "map_funs_ctrs ?h (map_funs_ctrs h R) = R" 
    unfolding map_funs_ctrs.simps image_comp map_funs_crule_comp[of ?h h, unfolded id]
    by auto
  finally show "(s, t) \<in> cstep R" by auto
qed

lemma map_funs_crule_case_sum_Inl [simp]:
  "map_funs_crule (case_sum Inl f) ` map_funs_crule Inl ` A = map_funs_crule Inl ` A"
  using image_comp map_funs_crule_comp case_sum_o_inj
  by (metis (no_types, opaque_lifting))

lemma vars_trs_eqvt [eqvt]:
  fixes p :: "'v::infinite perm"
  shows "p \<bullet> vars_trs R = vars_trs (p \<bullet> R)"
apply (auto simp: vars_defs eqvt)
apply (metis fst_conv rule_pt.permute_minus_cancel(1) trs_pt.inv_mem_simps(1))
by (metis rule_pt.permute_minus_cancel(1) snd_conv trs_pt.inv_mem_simps(1))

lemma image_map_funs_rule_trs2ctrs [simp]:
  "map_funs_crule f ` trs2ctrs R = trs2ctrs (map_funs_rule f ` R)"
by (force simp: trs2ctrs_def map_funs_crule_def)

(*TODO: move*)
lemma ground_perm_id:
  "ground t \<Longrightarrow> \<pi> \<bullet> t = t"
by (metis empty_iff ground_vars_term_empty term_pt.permute_plus term_pt.permute_swap_cancel2 vars_term_perm_eq)

lemma ground_skol_vars_trs:
  "(s, t) \<in> C \<Longrightarrow> ground (skol (vars_trs C) s) \<and> ground (skol (vars_trs C)t)"
by (auto intro!: ground_skol_mono [OF ground_skol_vars_term] simp: vars_defs)

lemma map_funs_rule_perm_Inr' [simp]:
  fixes p :: "'v::infinite perm"
  shows "map_funs_rule (case_sum Inl ((Inr \<circ>\<circ> (\<bullet>)) p)) ` skol_trs C = skol_trs (p \<bullet> C)"
apply (auto simp: eqvt [symmetric] skol_trs_def)
defer
subgoal premises prems for x y
  proof -
    obtain x' y' where "(x', y') \<in> C"
      and [simp]: "x = p \<bullet> x'" "y = p \<bullet> y'" using prems
      by (metis inv_rule_mem_trs_simps(1) term_pt.permute_minus_cancel(1))
    then show ?thesis
     apply (auto simp: skol_perm ground_perm_id)
     apply (force dest: ground_skol_vars_trs simp: ground_perm_id)
     done
  qed
subgoal premises prems for x y
  proof -
    from prems have "(p \<bullet> x, p \<bullet> y) \<in> p \<bullet> C" by auto
    moreover have "skol (p \<bullet> vars_trs C) (p \<bullet> x) = perm_Inr p (skol (vars_trs C) x)"
      and "skol (p \<bullet> vars_trs C) (p \<bullet> y) = perm_Inr p (skol (vars_trs C) y)"
      using prems by (force dest: ground_skol_vars_trs simp: ground_perm_id skol_perm)+
    ultimately show ?thesis by force
  qed
done


lemma cstep_map_perm_Inr_iff:
  "(s, t) \<in> cstep (map_funs_crule Inl ` R \<union> trs2ctrs (skol_trs C)) \<longleftrightarrow>
   (perm_Inr p s, perm_Inr p t) \<in> cstep (map_funs_crule Inl ` R \<union> trs2ctrs (skol_trs (p \<bullet> C)))"
  unfolding cstep_iff_map_cstep [OF inj_perm_Inr', of s t _ p]
  by (simp add: image_Un del: map_funs_rule.simps)

lemma map_funs_term_perm: "map_funs_term f (p \<bullet> t) = p \<bullet> map_funs_term f t"
by (induct t) auto

lemma ctxt_step_perm:
  "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ctxt_step R (\<pi> \<bullet> C) \<longleftrightarrow> (s, t) \<in> ctxt_step R C"
  apply (auto elim!: ctxt_step.cases intro!: ctxt_step.intros)
  unfolding cstep_map_perm_Inr_iff [of "skol (vars_trs C) s" "skol (vars_trs C) t" R C \<pi>]
  unfolding vars_trs_eqvt [symmetric]
  unfolding skol_perm
   apply (auto simp: map_funs_term_perm eqvt [symmetric])
   apply (metis (no_types, lifting) cstep_iff cstep_n_subst inv_rule_mem_trs_simps(1) term_apply_subst_Var_Rep_perm term_pt.permute_minus_cancel(1) trs_pt.inv_mem_simps(2))
  by (metis cstep_iff cstep_n_subst rule_pt.permute_prod.simps term_apply_subst_Var_Rep_perm)

lemma ctxt_steps_perm:
  "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> (ctxt_step R (\<pi> \<bullet> C))\<^sup>* \<longleftrightarrow> (s, t) \<in> (ctxt_step R C)\<^sup>*" (is "_ \<in> ?P\<^sup>* \<longleftrightarrow> _ \<in> ?C\<^sup>*")
proof -
  have "(\<pi> \<bullet> s, \<pi> \<bullet> t) \<in> ?P ^^ n \<longleftrightarrow> (s, t) \<in> ?C ^^ n" for n
  proof (induct n arbitrary: t)
    case (Suc n) then show ?case
      by auto
      (metis (no_types, lifting) ctxt_step_perm relcomp.simps term_pt.permute_minus_cancel(2))+
  qed simp
  then show ?thesis by (simp add: rtrancl_power)
qed

lemma permute_term_eq_Var_conv [simp]:
  fixes \<pi> :: "'v::infinite perm"
  shows "\<pi> \<bullet> t = Var (\<pi> \<bullet> x) \<longleftrightarrow> t = Var x"
  by (cases t) auto

lemma Var_inv_comp [simp]:
  "inj f \<Longrightarrow> (Var \<circ> f) \<circ>\<^sub>s (Var \<circ> the_inv f) = Var"
  by (auto simp: subst_compose_def the_inv_f_f)

lemma strongly_irreducible_perm:
  assumes "strongly_irreducible R (\<pi> \<bullet> t)"
  shows "strongly_irreducible R t"
using assms
by (auto simp: strongly_irreducible_def normalized_def)
   (metis (no_types) comp_eq_dest_lhs permute_term_subst_apply_term term_pt.permute_minus_cancel(2))

lemma unifiable_perm:
  assumes "unifiable {(\<pi> \<bullet> t\<^sub>1, \<pi> \<bullet> t\<^sub>2)}"
  shows "unifiable {(t\<^sub>1, t\<^sub>2)}"
using assms by (auto simp: unifiable_def unifiers_def permute_term_subst_apply_term)

locale al94_ops =
  fixes xvar yvar :: "'v::{showl, infinite} \<Rightarrow> 'v"
    and check_context_joinable :: "('f::showl, 'v) crules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
    and check_infeasible :: "('f, 'v) crules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
    and check_unfeasible :: "('f, 'v) crules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
begin

definition
  check_overlap :: "('f, 'v) crules \<Rightarrow> ('f, 'v) crule \<Rightarrow> ('f, 'v) crule \<Rightarrow> pos \<Rightarrow> showsl check"
where
  "check_overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p =
    (case mgu_var_disjoint_generic xvar yvar (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) of
      None \<Rightarrow> succeed
    | Some (\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Rightarrow>
      let cs = subst_list \<sigma>\<^sub>1 (snd \<rho>\<^sub>1) @ subst_list \<sigma>\<^sub>2 (snd \<rho>\<^sub>2) in
      let s = crhs \<rho>\<^sub>1 \<cdot> \<sigma>\<^sub>1 in
      let t = replace_at (clhs \<rho>\<^sub>1 \<cdot> \<sigma>\<^sub>1) p (crhs \<rho>\<^sub>2 \<cdot> \<sigma>\<^sub>2) in
      choice [
        do { check (p = []) id; check_crule_variants \<rho>\<^sub>1 \<rho>\<^sub>2 } <+? (\<lambda>e. showsl_lit (STR ''the overlap is critical\<newline>'') \<circ> e),
        check_context_joinable R s t cs <+? (\<lambda>e. showsl_lit (STR ''could not be shown to be context-joinable\<newline>'') \<circ> e),
        check_infeasible R cs <+? (\<lambda>e. showsl_lit (STR ''could not be shown to be infeasible\<newline>'') \<circ> e),
        check_unfeasible R (clhs \<rho>\<^sub>1) \<sigma>\<^sub>1 cs <+? (\<lambda>e. showsl_lit (STR ''could not be shown to be unfeasible\<newline>'') \<circ> e)
      ]
      <+? showsl_sep id showsl_nl)
    <+? (\<lambda>e. showsl_coverlap \<rho>\<^sub>1 \<rho>\<^sub>2 p \<circ> showsl_lit (STR '':\<newline>\<newline>'') \<circ> e)"

definition
  "check_CCPs R =
    check_allm (\<lambda>\<rho>\<^sub>1. let l\<^sub>1 = clhs \<rho>\<^sub>1 in check_allm (\<lambda>\<rho>\<^sub>2. check_allm (\<lambda>p.
      check_overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p) (fun_poss_list l\<^sub>1)) R) R"

end

lemmas [code] =
  al94_ops.check_overlap_def al94_ops.check_CCPs_def

locale al94_spec = al94_ops +
  assumes context_joinable: "isOK (check_context_joinable R s t cs) \<Longrightarrow>
    \<exists>t\<^sub>0. (s, t\<^sub>0) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and> (t, t\<^sub>0) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
    and infeasible: "isOK (check_infeasible R cs) \<Longrightarrow> \<not> (\<exists>\<sigma>. conds_sat (set R) cs \<sigma>)"
    and unfeasible: "isOK (check_unfeasible R l \<mu> cs) \<Longrightarrow> quasi_decreasing (set R) \<Longrightarrow>
      \<exists>t\<^sub>0 t\<^sub>1 t\<^sub>2.
        (\<forall>\<sigma>. (\<forall>(u, v)\<in>set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow>
          (l \<cdot> \<mu> \<cdot> \<sigma>, t\<^sub>0 \<cdot> \<sigma>) \<in> (cstep (set R) \<union> {\<rhd>} \<union> {(s, t). qdstep (set R) s t})\<^sup>+) \<and>
        (t\<^sub>0, t\<^sub>1) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and>
        (t\<^sub>0, t\<^sub>2) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and>
        \<not> unifiable {(t\<^sub>1, t\<^sub>2)} \<and>
        strongly_irreducible (set R) t\<^sub>1 \<and>
        strongly_irreducible (set R) t\<^sub>2"
    and ren: "inj xvar" "inj yvar" "range xvar \<inter> range yvar = {}"
begin

definition "S R = (cstep (set R) \<union> {\<rhd>} \<union> {(s, t). qdstep (set R) s t})\<^sup>+"

lemma isOK_check_CCPs:
  assumes "isOK (check_CCPs R)" and qd: "quasi_decreasing (set R)"
    and "overlap (set R) r r' p"
  shows "unfeasible (set R) (S R) r r' p \<or> context_joinable (set R) r r' p \<or> infeasible (set R) r r' p \<or> (p = [] \<and> (\<exists>\<pi>. \<pi> \<bullet> r = r'))"
proof -
  from \<open>overlap (set R) r r' p\<close> obtain \<pi>\<^sub>1 and \<pi>\<^sub>2 and \<mu>
    where rules': "\<pi>\<^sub>1 \<bullet> r \<in> set R" "\<pi>\<^sub>2 \<bullet> r' \<in> set R"
    and disj: "vars_crule r \<inter> vars_crule r' = {}"
    and p': "p \<in> fun_poss (clhs r)"
    and mgu': "mgu (clhs r |_ p) (clhs r') = Some \<mu>"
    by (auto simp: overlap_def)
  have the_mgu: "the (mgu (clhs r |_ p) (clhs r')) = \<mu>" using mgu' by auto
  define \<rho>\<^sub>1 \<rho>\<^sub>2 where "\<rho>\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> r" and "\<rho>\<^sub>2 \<equiv> \<pi>\<^sub>2 \<bullet> r'"
  have p: "p \<in> fun_poss (clhs \<rho>\<^sub>1)"
    and "\<rho>\<^sub>1 \<in> set R" and "\<rho>\<^sub>2 \<in> set R"
    using p' and rules' apply (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def eqvt)
    by (metis crule_pt.fst_eqvt fun_poss_perm_simp rule_pt.fst_eqvt)
  with assms have *: "isOK (check_overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p)" by (auto simp: check_CCPs_def)

  have "(clhs r |_ p) \<cdot> \<mu> = clhs r' \<cdot> \<mu>" using mgu' [THEN mgu_sound] by (auto simp: is_imgu_def)
  then have "(clhs r |_ p) \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1) \<circ> Rep_perm \<pi>\<^sub>1) =
    clhs r' \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2) \<circ> Rep_perm \<pi>\<^sub>2)"
    by (simp add: o_assoc [symmetric] Rep_perm_add [symmetric] Rep_perm_0)
  then have "clhs \<rho>\<^sub>1 |_ p \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1)) = clhs \<rho>\<^sub>2 \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2))"
    using p [THEN fun_poss_imp_poss]
    by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def permute_term_subst_apply_term [symmetric] eqvt)
  from mgu_var_disjoint_generic_complete [OF ren this] obtain \<mu>\<^sub>1 \<mu>\<^sub>2 \<delta>
    where mgu: "mgu_var_disjoint_generic xvar yvar (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some (\<mu>\<^sub>1, \<mu>\<^sub>2)"
    and **: "\<mu> \<circ> Rep_perm (- \<pi>\<^sub>1) = \<mu>\<^sub>1 \<circ>\<^sub>s \<delta>" "\<mu> \<circ> Rep_perm (- \<pi>\<^sub>2) = \<mu>\<^sub>2 \<circ>\<^sub>s \<delta>" by blast

  have "vars_term (clhs r |_ p) \<subseteq> vars_crule r" and "vars_term (clhs r') \<subseteq> vars_crule r'"
    using p' [THEN fun_poss_imp_poss, THEN vars_term_subt_at] by (auto simp: vars_crule_def vars_defs)
  from mgu_imp_mgu_var_disjoint [OF mgu' ren disj this finite_vars_crule finite_vars_crule, of \<pi>\<^sub>1 \<pi>\<^sub>2]
    obtain \<mu>' and \<pi>
    where left: "\<forall>x\<in>vars_crule r. \<mu> x = (sop \<pi>\<^sub>1 \<circ>\<^sub>s (\<mu>' \<circ> xvar) \<circ>\<^sub>s sop (- \<pi>)) x"
    and right: "\<forall>x\<in>vars_crule r'. \<mu> x = (sop \<pi>\<^sub>2 \<circ>\<^sub>s (\<mu>' \<circ> yvar) \<circ>\<^sub>s sop (- \<pi>)) x"
    and "mgu (\<pi>\<^sub>1 \<bullet> (clhs r |_ p) \<cdot> (Var \<circ> xvar)) (\<pi>\<^sub>2 \<bullet> clhs r' \<cdot> (Var \<circ> yvar)) = Some \<mu>'"
    by blast
  then have "mgu_var_disjoint_generic xvar yvar (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some (\<mu>' \<circ> xvar, \<mu>' \<circ> yvar)"
    and \<mu>\<^sub>1: "\<mu>\<^sub>1 = \<mu>' \<circ> xvar" and \<mu>\<^sub>2: "\<mu>\<^sub>2 = \<mu>' \<circ> yvar"
    using p' [THEN fun_poss_imp_poss] and mgu
    by (auto simp: map_vars_term_eq mgu_var_disjoint_generic_def \<rho>\<^sub>1_def \<rho>\<^sub>2_def eqvt)

  let ?s = "crhs \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1"
  let ?t = "replace_at (clhs \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1) p (crhs \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2)"
  let ?t' = "replace_at (clhs r \<cdot> \<mu>) p (crhs r' \<cdot> \<mu>)"
  let ?cs = "subst_list \<mu>\<^sub>1 (snd \<rho>\<^sub>1) @ subst_list \<mu>\<^sub>2 (snd \<rho>\<^sub>2)"
  let ?cs' = "subst_list \<mu> (conds r @ conds r')"
  have t': "?t \<cdot> \<delta> = replace_at (clhs r \<cdot> \<mu>) p (crhs r' \<cdot> \<mu>)"
    using p [THEN fun_poss_imp_poss] and left and right
    apply (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def ctxt_of_pos_term_subst [symmetric])
    unfolding subst_subst ** [symmetric]
    by (auto simp: eqvt [symmetric] permute_term_subst_apply_term [symmetric])

  have 1: "clhs \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1 = \<pi> \<bullet> (clhs r \<cdot> \<mu>)"
    apply (auto simp: \<mu>\<^sub>1 \<rho>\<^sub>1_def eqvt [symmetric])
    unfolding term_apply_subst_Var_Rep_perm [symmetric]
    unfolding subst_subst_compose [symmetric]
    unfolding term_subst_eq_conv
    using left
    by (auto simp: vars_crule_def vars_defs subst_compose)
  have 2: "crhs \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2 = \<pi> \<bullet> (crhs r' \<cdot> \<mu>)"
    apply (auto simp: \<mu>\<^sub>2 \<rho>\<^sub>2_def eqvt [symmetric])
    unfolding term_apply_subst_Var_Rep_perm [symmetric]
    unfolding subst_subst_compose [symmetric]
    unfolding term_subst_eq_conv
    using right
    by (auto simp: vars_crule_def vars_defs subst_compose)
  have t'': "?t = \<pi> \<bullet> ?t'"
    using p' [THEN fun_poss_imp_poss]
    unfolding 1 2 by (auto simp: eqvt)

  have length: "length ?cs = length ?cs'"
    by (auto simp: subst_list_def \<rho>\<^sub>1_def \<rho>\<^sub>2_def eqvt [symmetric])

  have 3: "?cs = \<pi> \<bullet> ?cs'"
  proof -
    { fix i assume "i < length ?cs"
      then have "fst (?cs ! i) = \<pi> \<bullet> (fst ((conds r @ conds r') ! i) \<cdot> \<mu>)
        \<and> snd (?cs ! i) = \<pi> \<bullet> (snd ((conds r @ conds r') ! i) \<cdot> \<mu>)"
      apply (cases "i < length (conds r)")
      apply (auto simp: subst_list_def nth_append \<rho>\<^sub>1_def \<rho>\<^sub>2_def \<mu>\<^sub>1 \<mu>\<^sub>2 eqvt [symmetric])
      unfolding term_apply_subst_Var_Rep_perm [symmetric]
      unfolding subst_subst_compose [symmetric]
      unfolding term_subst_eq_conv
      using left and right
      apply (auto simp: subst_compose dest!: vars_conds_vars_crule_subset)
      done
      then have "?cs ! i = \<pi> \<bullet> (fst ((conds r @ conds r') ! i) \<cdot> \<mu>, snd ((conds r @ conds r') ! i) \<cdot> \<mu>)"
        by (metis prod.collapse rule_pt.permute_prod.simps)
    }
    then show ?thesis using length by (intro nth_equalityI) auto
  qed
  have 3: "set ?cs = \<pi> \<bullet> set ?cs'" unfolding 3 permute_conds_set ..

  consider (cjoin) "isOK (check_context_joinable R ?s ?t ?cs)"
    | (inf) "isOK (check_infeasible R ?cs)"
    | (unf) "isOK (check_unfeasible R (clhs \<rho>\<^sub>1) \<mu>\<^sub>1 ?cs)"
    | (nc) "isOK (do { check (p = []) id; check_crule_variants \<rho>\<^sub>1 \<rho>\<^sub>2 })"
    using * and mgu by (force simp: check_overlap_def)
  then show ?thesis
  proof (cases)
    case nc
    then obtain \<pi> where "p = []" and "\<pi> \<bullet> \<pi>\<^sub>1 \<bullet> r = \<pi>\<^sub>2 \<bullet> r'" by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def)
    moreover then have "((-\<pi>\<^sub>2) + \<pi> + \<pi>\<^sub>1) \<bullet> r = r'" by simp
    ultimately show ?thesis by blast
  next
    case cjoin
    have "context_joinable (set R) r r' p"
    proof (unfold context_joinable_def Let_def the_mgu)
      from context_joinable [OF cjoin] obtain t
        where *: "(?s, t) \<in> (ctxt_step (set R) (set ?cs))\<^sup>* \<and> (?t, t) \<in> (ctxt_step (set R) (set ?cs))\<^sup>*" by blast
      have 1: "?s = \<pi> \<bullet> (crhs r \<cdot> \<mu>)"
        apply (auto simp: \<mu>\<^sub>1 \<rho>\<^sub>1_def eqvt [symmetric])
        unfolding term_apply_subst_Var_Rep_perm [symmetric]
        unfolding subst_subst_compose [symmetric]
        unfolding term_subst_eq_conv
        using left
        by (auto simp: vars_crule_def vars_defs subst_compose)
      have 4: "\<pi> \<bullet> -\<pi> \<bullet> t = t" by simp
      have "(\<pi> \<bullet> (crhs r \<cdot> \<mu>), \<pi> \<bullet> -\<pi> \<bullet> t) \<in> (ctxt_step (set R) (\<pi> \<bullet> set ?cs'))\<^sup>*"
        and "(\<pi> \<bullet> ?t', \<pi> \<bullet> -\<pi> \<bullet> t) \<in> (ctxt_step (set R) (\<pi> \<bullet> set ?cs'))\<^sup>*"
        using * unfolding 1 3 4 t'' by blast+
      from this [unfolded ctxt_steps_perm]
        show "\<exists>t\<^sub>0.(crhs r \<cdot> \<mu>, t\<^sub>0) \<in> (ctxt_step (set R) (set ?cs'))\<^sup>* \<and>
         ((ctxt_of_pos_term p (clhs r))\<langle>crhs r'\<rangle> \<cdot> \<mu>, t\<^sub>0) \<in> (ctxt_step (set R) (set ?cs'))\<^sup>*"
          using p' [THEN fun_poss_imp_poss] 
          by (metis ctxt_of_pos_term_subst subst_apply_term_ctxt_apply_distrib)
    qed
    then show ?thesis by blast
  next
    case inf
    have "infeasible (set R) r r' p"
    proof (unfold infeasible_def Let_def the_mgu, intro notI, elim exE)
      fix \<sigma>
      assume "\<forall>(u, v)\<in> set (subst_list \<mu> (conds r @ conds r')). (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*"
      then have "conds_sat (set R) (subst_list \<mu> (conds r @ conds r')) \<sigma>" by (auto simp: conds_sat_iff)
      then have "conds_sat (set R) (subst_list (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1)) (conds \<rho>\<^sub>1) @
        subst_list (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2)) (conds \<rho>\<^sub>2)) \<sigma>"
        by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def subst_list_append subst_list_Rep_perm eqvt [symmetric])
      then have "\<exists>\<sigma>. conds_sat (set R) (subst_list \<mu>\<^sub>1 (conds \<rho>\<^sub>1) @ subst_list \<mu>\<^sub>2 (conds \<rho>\<^sub>2)) \<sigma>"
       by (auto simp: ** subst_list_subst_compose conds_sat_subst_list)
      with infeasible [OF inf] show False by blast
    qed
    then show ?thesis by blast
  next
    case unf
    have "unfeasible (set R) (S R) r r' p"
    proof (unfold unfeasible_def Let_def the_mgu)
      from unfeasible [OF unf qd, folded S_def] obtain s t u
        where cs: "(\<forall>\<sigma>. (\<forall>(u, v)\<in>set ?cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow> (clhs \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1 \<cdot> \<sigma>, s \<cdot> \<sigma>) \<in> S R)"
        and st: "(s, t) \<in> (ctxt_step (set R) (set ?cs))\<^sup>*"
        and su: "(s, u) \<in> (ctxt_step (set R) (set ?cs))\<^sup>*"
        and nunif: "\<not> unifiable {(t, u)}"
        and sit: "strongly_irreducible (set R) t"
        and siu: "strongly_irreducible (set R) u" by blast
      from sit have sit: "strongly_irreducible (set R) (\<pi> \<bullet> -\<pi> \<bullet> t)" by auto
      from siu have siu: "strongly_irreducible (set R) (\<pi> \<bullet> -\<pi> \<bullet> u)" by auto

      { fix \<sigma>
        assume "\<forall>(u, v) \<in> set ?cs'. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*"
        with cs [THEN spec, of "sop (-\<pi>) \<circ>\<^sub>s \<sigma>", unfolded 3]
          have "(clhs \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1 \<cdot> (sop (-\<pi>) \<circ>\<^sub>s \<sigma>), s \<cdot> (sop (-\<pi>) \<circ>\<^sub>s \<sigma>)) \<in> S R" by auto
        then have "(clhs r \<cdot> \<mu> \<cdot> \<sigma>, -\<pi> \<bullet> s \<cdot> \<sigma>) \<in> S R" unfolding 1 by simp
      }
      then have "\<forall>\<sigma>. (\<forall>(u, v) \<in> set ?cs'. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow>
        (clhs r \<cdot> \<mu> \<cdot> \<sigma>, -\<pi> \<bullet> s \<cdot> \<sigma>) \<in> S R" by auto
      moreover have "(-\<pi> \<bullet> s, -\<pi> \<bullet> t) \<in> (ctxt_step (set R) (set ?cs'))\<^sup>*"
        using st [unfolded 3] ctxt_steps_perm [of \<pi> "-\<pi> \<bullet> s" "-\<pi> \<bullet> t" "set R" "set ?cs'"]
        by (simp add: trs_pt.permute_set_eq_image)
      moreover have "(-\<pi> \<bullet> s, -\<pi> \<bullet> u) \<in> (ctxt_step (set R) (set ?cs'))\<^sup>*"
        using su [unfolded 3] ctxt_steps_perm [of \<pi> "-\<pi> \<bullet> s" "-\<pi> \<bullet> u" "set R" "set ?cs'"]
        by (simp add: trs_pt.permute_set_eq_image)
      moreover from nunif have "\<not> unifiable {(-\<pi> \<bullet> t, -\<pi> \<bullet> u)}"
        by (auto simp: unifiable_def unifiers_def permute_term_subst_apply_term)
      moreover have "strongly_irreducible (set R) (-\<pi> \<bullet> t)" using strongly_irreducible_perm [OF sit] .
      moreover have "strongly_irreducible (set R) (-\<pi> \<bullet> u)" using strongly_irreducible_perm [OF siu] .
      ultimately show "\<exists>t\<^sub>0 t\<^sub>1 t\<^sub>2.
       (\<forall>\<sigma>. (\<forall>(u, v)\<in>set ?cs'. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow> (clhs r \<cdot> \<mu> \<cdot> \<sigma>, t\<^sub>0 \<cdot> \<sigma>) \<in> S R) \<and>
       (t\<^sub>0, t\<^sub>1) \<in> (ctxt_step (set R) (set ?cs'))\<^sup>* \<and>
       (t\<^sub>0, t\<^sub>2) \<in> (ctxt_step (set R) (set ?cs'))\<^sup>* \<and>
       \<not> unifiable {(t\<^sub>1, t\<^sub>2)} \<and>
       strongly_irreducible (set R) t\<^sub>1 \<and>
       strongly_irreducible (set R) t\<^sub>2" by blast
    qed
    then show ?thesis by blast
  qed
qed

end

(* TODO: move *)
fun map_funs_crules :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) crules \<Rightarrow> ('g, 'v) crules"
where
  "map_funs_crules f R = map (map_funs_crule f) R"

definition skol_rules :: "('f, 'v) rules \<Rightarrow> ('f + 'v, 'v) rules"
where
  "skol_rules cs = (let V = vars_trs (set cs) in map (\<lambda>(l, r). (skol V l, skol V r)) cs)"

definition skol_crule :: "('f, 'v) ctrs \<Rightarrow> 'v set \<Rightarrow> ('f, 'v) crule \<Rightarrow> ('f + 'v, 'v) crule"
where
  "skol_crule R V r =
    (if r \<in> R then map_funs_crule Inl r
    else ((skol V (clhs r), skol V (crhs r)), map (\<lambda>(s, t). (skol V s, skol V t)) (conds r)))"

definition rules2crules :: "('f, 'v) rules \<Rightarrow> ('f, 'v) crules"
where
  "rules2crules rs = map (\<lambda>r. (r, [])) rs"

fun skol_cstep_proof :: "('f, 'v) ctrs \<Rightarrow> 'v set \<Rightarrow> ('f, 'v) cstep_proof \<Rightarrow> ('f + 'v, 'v) cstep_proof" where
  "skol_cstep_proof R V (Cstep_step \<rho> p \<sigma> s t pss) =
    Cstep_step (skol_crule R V \<rho>) p (skol V \<circ> \<sigma>)
    (skol V s) (skol V t) (map (map (skol_cstep_proof R V)) pss)"

lemma cstep_src_skol_cstep_proof_skol_term:
  "cstep_src (skol_cstep_proof R V p) = skol V (cstep_src p)"
by (induct p) auto

lemma cstep_trg_skol_cstep_proof_skol_term:
  "cstep_trg (skol_cstep_proof R V p) = skol V (cstep_trg p)"
by (induct p) auto

lemma skol_trs_set_skol_rules:
  "skol_trs (set cs) = set (skol_rules cs)"
by (auto simp: skol_rules_def skol_trs_def Let_def)

lemma trs2ctrs_set_rules2crules:
  "trs2ctrs (set A) = set (rules2crules A)"
  by (auto simp: rules2crules_def trs2ctrs_def)

lemma check_csteps_imp_ctxt_step:
  fixes R :: "('f :: showl, 'v :: {infinite, showl}) crule list"
  assumes cstep: "isOK (check_csteps R' (skol V s) (skol V t) ps)"
    and ps: "ps = map (skol_cstep_proof (set R) V) qs"
    and V: "V = vars_trs (set cs)"
    and R': "R' = map_funs_crules Inl R @ rules2crules (skol_rules cs)"
  shows "(s, t) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
proof -
  from check_csteps' [OF cstep]
    have ite: "if ps = [] then skol V s = skol V t
      else skol V s = cstep_src (ps ! 0) \<and> skol V t = cstep_trg (last ps)"
    and *: "\<forall>i < length ps. (cstep_src (ps ! i), cstep_trg (ps ! i)) \<in> cstep (set R') \<and>
      (i < length ps - 1 \<longrightarrow> cstep_trg (ps ! i) = cstep_src (ps ! Suc i))" by (auto)
  from ite consider
    (em) "ps = []" and "skol V s = skol V t"
  | (ne) "ps \<noteq> []" and "skol V s = cstep_src (ps ! 0)" and "skol V t = cstep_trg (last ps)"
    by (auto split: if_splits)
  then show ?thesis
  proof (cases)
    case (ne)
    { fix i
      assume i: "i < length ps"
      have 1: "(skol V (cstep_src (qs ! i)), skol V (cstep_trg (qs ! i))) \<in> cstep (set R')" using *
        by (metis cstep_src_skol_cstep_proof_skol_term cstep_trg_skol_cstep_proof_skol_term i length_map nth_map ps)
      { assume "i < length ps - 1"
        then have "skol V (cstep_trg (qs ! i)) = skol V (cstep_src (qs ! Suc i))"
          by (metis "*" Nat.add_0_right One_nat_def add_Suc_right cstep_src_skol_cstep_proof_skol_term cstep_trg_skol_cstep_proof_skol_term i length_map less_diff_conv nth_map ps)
      }
      then have 2: "i < length ps - 1 \<longrightarrow> skol V (cstep_trg (qs ! i)) = skol V (cstep_src (qs ! Suc i))" by auto
      have "set (map_funs_crules Inl R) = map_funs_ctrs Inl (set R)" by simp
      moreover have "set (rules2crules (skol_rules cs)) = trs2ctrs (skol_trs (set cs))"
        by (simp add: skol_trs_set_skol_rules trs2ctrs_set_rules2crules)
      ultimately have "set R' = map_funs_ctrs Inl (set R) \<union> trs2ctrs (skol_trs (set cs))"
        using R' by force
      from 1 [unfolded this]
        have "(cstep_src (qs ! i), cstep_trg (qs ! i)) \<in> ctxt_step (set R) (set cs)"
        by (simp add: V ctxt_step.intros)
      with 2 have "((cstep_src (qs ! i), cstep_trg (qs ! i)) \<in> ctxt_step (set R) (set cs)) \<and>
        (i < length ps - 1 \<longrightarrow> skol V (cstep_trg (qs ! i)) = skol V (cstep_src (qs ! Suc i)))" by auto
    } note *** = this
    have "i < length qs \<Longrightarrow> (cstep_src (hd qs), cstep_trg (qs ! i)) \<in> (ctxt_step (set R) (set cs))\<^sup>*" for i
    proof (induct i)
      case 0
      then show ?case using *** [of 0] ne by (simp add: hd_conv_nth r_into_rtrancl)
    next
      case (Suc i)
      then show ?case using *** [of i] *** [of "Suc i"] unfolding V ps
        by (smt (verit, ccfv_SIG) Suc_lessD Suc_less_eq ctxt_step.cases ctxt_step.intros length_map remove_nth_len remove_nth_length rtrancl.simps)
    qed
    then have "(cstep_src (hd qs), cstep_trg (last qs)) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
      using ne by (metis List.last_in_set in_set_conv_nth list.simps(8) ps)
    then show ?thesis
      by (metis cstep_src_skol_cstep_proof_skol_term cstep_trg_skol_cstep_proof_skol_term
          hd_conv_nth last_map list.map_sel(1) map_is_Nil_conv ne(1) ne(2) ne(3) ps skol_inj)
  qed (fast)
qed

datatype ('f, 'v) context_joinable_proof =
  Contextual_Join (cj_term : "('f, 'v) term") "('f, 'v) cstep_proof list" "('f ,'v) cstep_proof list"

fun check_context_joinable' :: "('f::showl, 'v::showl) context_joinable_proof \<Rightarrow>
  ('f, 'v) crules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "check_context_joinable' (Contextual_Join u ps qs) R s t cs = do {
    let C = skol_rules cs;
    let V = vars_trs (set cs);
    let s' = skol V s;
    let t' = skol V t;
    let u' = skol V u;
    let ps' = map (skol_cstep_proof (set R) V) ps;
    let qs' = map (skol_cstep_proof (set R) V) qs;
    let R' = (map_funs_crules Inl R) @ rules2crules C;
    check_csteps R' s' u' ps';
    check_csteps R' t' u' qs'
  } <+? (\<lambda>e. showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' are not context-joinable\<newline>'') \<circ> e)"

lemma check_context_joinable':
  fixes R :: "('f :: showl, 'v :: {infinite, showl}) crule list"
  assumes "isOK (check_context_joinable' cj R s t cs)"
  shows "(s, cj_term cj) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and> (t, cj_term cj) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
proof -
  obtain u and ps and qs where cj: "cj = Contextual_Join u ps qs"
    using context_joinable_proof.exhaust by blast
  with assms obtain C V s' t' u' ps' qs' R'
    where C: "C = skol_rules cs"
    and V: "V = vars_trs (set cs)"
    and s': "s' = skol V s"
    and t': "t' = skol V t"
    and u': "u' = skol V u"
    and ps': "ps' = map (skol_cstep_proof (set R) V) ps"
    and qs': "qs' = map (skol_cstep_proof (set R) V) qs"
    and R': "R' = (map_funs_crules Inl R) @ rules2crules C"
    and su: "isOK (check_csteps R' s' u' ps')"
    and tu: "isOK (check_csteps R' t' u' qs')" by auto

  have "(s, u) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
    using check_csteps_imp_ctxt_step [OF su [unfolded s' u'] ps' V R' [unfolded C]] .
  moreover have "(t, u) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
    using check_csteps_imp_ctxt_step [OF tu [unfolded t' u'] qs' V R' [unfolded C]] .
  ultimately show ?thesis by (auto simp: cj)
qed

datatype ('f, 'v) unfeasible_proof =
  UnfeasibleOverlap "('f, 'v) term" "('f, 'v) term" "('f, 'v) term"
    "('f, 'v) cstep_proof list" "('f, 'v) cstep_proof list"
    (rule1: "('f, 'v) crule")
    (rule2: "('f, 'v) crule")

fun check_unfeasible' :: "('f::showl, string) unfeasible_proof \<Rightarrow>
  ('f, string) crules \<Rightarrow> ('f, string) term \<Rightarrow> ('f, string) subst \<Rightarrow>
  ('f, string) rules \<Rightarrow> showsl check"
where
  "check_unfeasible' (UnfeasibleOverlap t u v ps qs \<rho>\<^sub>1 \<rho>\<^sub>2) R l \<mu> cs = do {
    let C = skol_rules cs;
    let V = vars_trs (set cs);
    let t' = skol V t;
    let u' = skol V u;
    let v' = skol V v;
    let ps' = map (skol_cstep_proof (set R) V) ps;
    let qs' = map (skol_cstep_proof (set R) V) qs;
    let R' = (map_funs_crules Inl R) @ rules2crules C;
    check (l = clhs \<rho>\<^sub>1) id;
    check (\<forall>((l, r), cs) \<in> set R. is_Fun l) (showsl_lit (STR ''variable left-hand side''));
    check_variant_in_ctrs R \<rho>\<^sub>1;
    check_variant_in_ctrs R \<rho>\<^sub>2;
    check (l \<cdot> \<mu> \<unrhd> clhs \<rho>\<^sub>2 \<cdot> \<mu>) id;
    check (t \<in> fst ` set cs) id;
    check (cs = subst_list \<mu> (conds \<rho>\<^sub>1 @ conds \<rho>\<^sub>2)) id;
    check_csteps R' t' u' ps';
    check_csteps R' t' v' qs';
    check_airr R u;
    check_airr R v;
    check (mgu u v = None)
      (showsl u \<circ> showsl_lit (STR '' and '') \<circ> showsl v \<circ> showsl_lit (STR '' are unifiable''))
  } <+? (\<lambda>e. showsl_lit (STR ''conditions '') \<circ> showsl_conditions cs \<circ> showsl_lit (STR '' are not unfeasible\<newline>'') \<circ> e)"

lemma quasi_decreasing_orderD:
  assumes "quasi_decreasing_order R S"
    and "r \<in> R"
    and "i < length (conds r)"
    and "\<forall>j<i. (fst (conds r ! j) \<cdot> \<sigma>, snd (conds r ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  shows "(clhs r \<cdot> \<sigma>, fst (conds r ! i) \<cdot> \<sigma>) \<in> S"
using assms by (cases r rule: crule_cases) (auto simp: quasi_decreasing_order_def)

lemma check_unfeasible':
  fixes R :: "('f :: showl, string) crules"
  assumes "isOK (check_unfeasible' uo R l \<mu> cs)"
    and "quasi_decreasing (set R)"
  shows "\<exists>t\<^sub>0 t\<^sub>1 t\<^sub>2.
        (\<forall>\<sigma>. (\<forall>(u, v) \<in> set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow>
          (l \<cdot> \<mu> \<cdot> \<sigma>, t\<^sub>0 \<cdot> \<sigma>) \<in> (cstep (set R) \<union> {\<rhd>} \<union> {(s, t). qdstep (set R) s t})\<^sup>+) \<and>
        (t\<^sub>0, t\<^sub>1) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and>
        (t\<^sub>0, t\<^sub>2) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and>
        \<not> unifiable {(t\<^sub>1, t\<^sub>2)} \<and>
        strongly_irreducible (set R) t\<^sub>1 \<and>
        strongly_irreducible (set R) t\<^sub>2"
proof -
  obtain t u v ps qs \<rho>\<^sub>1 \<rho>\<^sub>2 where "uo = UnfeasibleOverlap t u v ps qs \<rho>\<^sub>1 \<rho>\<^sub>2"
    using unfeasible_proof.exhaust by blast
  with assms obtain C V t' u' v' ps' qs' R'
    where C: "C = skol_rules cs"
    and V: "V = vars_trs (set cs)"
    and t': "t' = skol V t"
    and u': "u' = skol V u"
    and v': "v' = skol V v"
    and ps': "ps' = map (skol_cstep_proof (set R) V) ps"
    and qs': "qs' = map (skol_cstep_proof (set R) V) qs"
    and R': "R' = (map_funs_crules Inl R) @ rules2crules C"
    and "isOK (check_variant_in_ctrs R \<rho>\<^sub>1)"
    and "isOK (check_variant_in_ctrs R \<rho>\<^sub>2)"
    and l: "l = clhs \<rho>\<^sub>1"
    and subt: "l \<cdot> \<mu> \<unrhd> (clhs \<rho>\<^sub>2) \<cdot> \<mu>"
    and t: "t \<in> fst ` set cs"
    and cs: "cs = subst_list \<mu> (conds \<rho>\<^sub>1 @ conds \<rho>\<^sub>2)"
    and tu: "isOK (check_csteps R' t' u' ps')"
    and tv: "isOK (check_csteps R' t' v' qs')"
    and aiu: "absolutely_irreducible (set R) u"
    and aiv: "absolutely_irreducible (set R) v"
    and no_mgu: "mgu u v = None"
    and vc: "\<forall>((l, r), cs) \<in> set R. is_Fun l"
      by (fastforce simp: check_airr)

  then obtain \<pi>\<^sub>1 and \<pi>\<^sub>2
    where rule: "\<pi>\<^sub>1 \<bullet> \<rho>\<^sub>1 \<in> set R" and rule': "\<pi>\<^sub>2 \<bullet> \<rho>\<^sub>2 \<in> set R"
    by (auto elim!: check_variant_in_ctrs)

  let ?cs\<^sub>1 = "(conds \<rho>\<^sub>1)"
  let ?cs\<^sub>2 = "(conds \<rho>\<^sub>2)"
  let ?cs' = "subst_list \<mu> ?cs\<^sub>1"
  let ?cs'' = "subst_list \<mu> ?cs\<^sub>2"
  let ?S = "(cstep (set R) \<union> {\<rhd>} \<union> {(s, t). qdstep (set R) s t})\<^sup>+"
  let ?l' = "clhs \<rho>\<^sub>2"

  have qd: "quasi_decreasing_order (set R) ?S" using quasi_decreasing' [OF assms(2)] .

  have "subst_list \<mu> (?cs\<^sub>1 @ ?cs\<^sub>2) = ?cs' @ ?cs''" using subst_list_append by auto
  from t [unfolded cs this] consider "t \<in> fst ` set ?cs'" | "t \<in> fst ` set ?cs''" by auto
  then have "\<forall>\<sigma>. (\<forall>(u, v) \<in> set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow> (l \<cdot> \<mu> \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?S"
  proof (cases)
    case (1)
    then obtain k where k: "k < length ?cs'" and "t = fst (?cs' ! k)"
      by (metis (no_types, lifting) imageE in_set_idx)
    then have tk: "t = fst (?cs\<^sub>1 ! k) \<cdot> \<mu>" using nth_subst_list by simp
    { fix \<sigma>
      assume "\<forall>(u, v) \<in> set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*"
      then have "\<forall>(u, v) \<in> set ?cs'. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*" unfolding cs
        by (simp add: subst_list_append)
      then have *: "\<forall>i < length ?cs'. (fst (?cs' ! i) \<cdot> \<sigma>, snd (?cs' ! i) \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*"
        by (metis (no_types, lifting) case_prod_beta nth_mem)
      let ?\<sigma> = "sop (-\<pi>\<^sub>1) \<circ>\<^sub>s \<mu> \<circ>\<^sub>s \<sigma>"
      have k: "k < length (conds (\<pi>\<^sub>1 \<bullet> \<rho>\<^sub>1))" using k by (cases \<rho>\<^sub>1 rule: crule_cases) (auto simp: eqvt)
      have "\<forall>j < k. (fst (conds (\<pi>\<^sub>1 \<bullet> \<rho>\<^sub>1) ! j) \<cdot> ?\<sigma>, snd (conds (\<pi>\<^sub>1 \<bullet> \<rho>\<^sub>1) ! j) \<cdot> ?\<sigma>) \<in> (cstep (set R))\<^sup>*"
        using * using k by (cases \<rho>\<^sub>1 rule: crule_cases) (fastforce simp: eqvt)
      then have "(clhs (\<pi>\<^sub>1 \<bullet> \<rho>\<^sub>1) \<cdot> ?\<sigma>, fst (conds (\<pi>\<^sub>1 \<bullet> \<rho>\<^sub>1) ! k) \<cdot> ?\<sigma>) \<in> ?S"
        using quasi_decreasing_orderD [OF qd rule k, of ?\<sigma>] by blast
      then have "(l \<cdot> \<mu> \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?S" using k by (auto simp: eqvt [symmetric] l tk)
    }
    then show ?thesis by auto
  next
    case (2)
    then obtain k where k: "k < length ?cs''" and "t = fst (?cs'' ! k)"
      by (metis (no_types, lifting) imageE in_set_idx)
    then have tk: "t = fst (?cs\<^sub>2 ! k) \<cdot> \<mu>" using nth_subst_list by simp
    { fix \<sigma>
      assume "\<forall>(u, v) \<in> set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*"
      then have "\<forall>(u, v) \<in> set ?cs''. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*" unfolding cs
        by (simp add: subst_list_append)
      then have *: "\<forall>i < length ?cs''. (fst (?cs'' ! i) \<cdot> \<sigma>, snd (?cs'' ! i) \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*"
        by (metis (no_types, lifting) case_prod_beta nth_mem)

      let ?\<sigma> = "sop (-\<pi>\<^sub>2) \<circ>\<^sub>s \<mu> \<circ>\<^sub>s \<sigma>"
      have k: "k < length (conds (\<pi>\<^sub>2 \<bullet> \<rho>\<^sub>2))" using k by (cases \<rho>\<^sub>2 rule: crule_cases) (auto simp: eqvt)
      have "\<forall>j < k. (fst (conds (\<pi>\<^sub>2 \<bullet> \<rho>\<^sub>2) ! j) \<cdot> ?\<sigma>, snd (conds (\<pi>\<^sub>2 \<bullet> \<rho>\<^sub>2) ! j) \<cdot> ?\<sigma>) \<in> (cstep (set R))\<^sup>*"
        using * using k by (cases \<rho>\<^sub>2 rule: crule_cases) (fastforce simp: eqvt)
      then have "(clhs (\<pi>\<^sub>2 \<bullet> \<rho>\<^sub>2) \<cdot> ?\<sigma>, fst (conds (\<pi>\<^sub>2 \<bullet> \<rho>\<^sub>2) ! k) \<cdot> ?\<sigma>) \<in> ?S"
        using quasi_decreasing_orderD [OF qd rule' k, of ?\<sigma>] by blast
      then have "(clhs \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?S" using k by (auto simp: eqvt [symmetric] tk)
      moreover have "(l \<cdot> \<mu> \<cdot> \<sigma>, clhs \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma>) \<in> (?S)\<^sup>="
        using subt [THEN supteq_subst, of \<sigma>] by (auto simp: supteq_supt_conv)
      ultimately have "(l \<cdot> \<mu> \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?S" by auto
    }
    then show ?thesis by auto
  qed
  moreover have "(t, u) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
    using check_csteps_imp_ctxt_step [OF tu [unfolded t' u'] ps' V R' [unfolded C]] .
  moreover have "(t, v) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
    using check_csteps_imp_ctxt_step [OF tv [unfolded t' v'] qs' V R' [unfolded C]] .
  moreover have "strongly_irreducible (set R) u"
    using absolutely_irreducible_strongly_irreducible [OF aiu vc] .
  moreover have "strongly_irreducible (set R) v"
    using absolutely_irreducible_strongly_irreducible [OF aiv vc] .
  moreover have "\<not> unifiable {(u, v)}" using no_mgu [THEN mgu_complete]
    by (auto simp: unifiable_def)
  ultimately show ?thesis by auto
qed

lemma conds_sat_perm_shift:
  "conds_sat R (\<pi> \<bullet> cs) \<sigma> = conds_sat R cs (\<sigma> \<circ> Rep_perm \<pi>)"
by (auto simp: conds_sat_iff permute_term_subst_apply_term eqvt split: prod.splits)

definition
  check_infeasible
where
  "check_infeasible a i I J css R cs = check_exm (\<lambda>(cs', p). do {
    check (length cs' = length cs) (showsl_lit (STR ''lengths differ''));
    check (match_rules cs cs' \<noteq> None \<and> match_rules cs' cs \<noteq> None) id;
    check_infeasible' a i I J R cs' p
  }) css (showsl_sep id showsl_nl)"

lemma check_infeasible:
  assumes I: "tp_spec I" and J: "dpp_spec J" and "isOK (check_infeasible a i I J css R cs)"
  shows "\<not> (\<exists>\<sigma>. conds_sat (set R) cs \<sigma>)" (is "?P cs")
proof -
  obtain \<pi> :: "string perm" and cs' and p where "(cs', p) \<in> set css"
    and cs': "cs' = \<pi> \<bullet> cs" and ok: "isOK (check_infeasible' a i I J R cs' p)"
    using assms(3) and match_rules_imp_variants [of _ cs]
    by (fastforce simp: check_infeasible_def)
  moreover then have "?P cs'" by (auto dest: check_infeasible'[OF I J] simp: conds_sat_conds_n_sat)
  ultimately show ?thesis by (metis conds_sat_perm_shift rules_pt.permute_minus_cancel(2))
qed

(*TODO: move*)
definition
  "check_coverlap r r' p =
    (case mgu (clhs r |_ p) (clhs r') of
      None \<Rightarrow> error (showsl_lit (STR ''the conditional rules '') \<circ> showsl_crule r \<circ> showsl_lit (STR '' and '') \<circ> showsl_crule r' \<circ>
        showsl_lit (STR '' do not overlap at position '') \<circ> showsl_pos p)
    | Some \<mu> \<Rightarrow> return ((crhs r \<cdot> \<mu>, replace_at (clhs r \<cdot> \<mu>) p (crhs r' \<cdot> \<mu>)), subst_list \<mu> (conds r @ conds r'))
    )"

fun check_context_joinable ::
  "(('f::{compare_order,showl}, 'v::{showl,infinite}) term \<times> ('f, 'v) term \<times> ('f ,'v) rules \<times> ('f, 'v) context_joinable_proof) list \<Rightarrow>
    ('f, 'v) crules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "check_context_joinable cj R s t cs = check_exm (\<lambda>(s', t', cs', p). do {
    check (match_rules ((s, t) # cs) ((s', t') # cs') \<noteq> None) id;
    check (match_rules ((s', t') # cs') ((s, t) # cs) \<noteq> None) id;
    check_context_joinable' p R s' t' cs'
    }) cj (showsl_sep id showsl_nl)"

lemma check_context_joinable:
  assumes "isOK (check_context_joinable cj R s t cs)"
  shows "\<exists>t\<^sub>0. (s, t\<^sub>0) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and> (t, t\<^sub>0) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
proof -
  obtain p and s' and t' and cs'
    where "(s', t', cs', p) \<in> set cj"
    and "match_rules ((s, t) # cs) ((s', t') # cs') \<noteq> None"
    and "match_rules ((s', t') # cs') ((s, t) # cs) \<noteq> None"
    and "isOK (check_context_joinable' p R s' t' cs')"
    using assms by (auto split: option.splits simp: check_coverlap_def)
  then obtain \<pi> :: "'b perm" and u' where "\<pi> \<bullet> ((s, t) # cs) = ((s', t') # cs')"
    and "(s', u') \<in> (ctxt_step (set R) (set cs'))\<^sup>*"
    and "(t', u') \<in> (ctxt_step (set R) (set cs'))\<^sup>*"
    by (auto dest: match_rules_imp_variants dest!: check_context_joinable')
  then have "(-\<pi> \<bullet> s', -\<pi> \<bullet> u') \<in> (ctxt_step (set R) (-\<pi> \<bullet> set cs'))\<^sup>*"
    and "(-\<pi> \<bullet> t', -\<pi> \<bullet> u') \<in> (ctxt_step (set R) (-\<pi> \<bullet> set cs'))\<^sup>*"
    and "-\<pi> \<bullet> s' = s" and "-\<pi> \<bullet> t' = t" and "-\<pi> \<bullet> cs' = cs"
    unfolding ctxt_steps_perm by (auto simp: eqvt)
  then show ?thesis unfolding permute_conds_set by blast
qed

definition
  check_unfeasible ::
  "(('f::{compare_order,showl}, string) subst \<times> ('f, string) unfeasible_proof) list \<Rightarrow>
    ('f, string) crules \<Rightarrow> ('f, string) term \<Rightarrow> ('f, string) subst \<Rightarrow> ('f, string) rules \<Rightarrow> showsl check"
where
  "check_unfeasible css R l \<mu> cs = check_exm (\<lambda>(\<mu>', uo). do {
    let cs\<^sub>1 = conds (rule1 uo);
    let cs\<^sub>2 = conds (rule2 uo);
    let cs' = subst_list \<mu>' (cs\<^sub>1 @ cs\<^sub>2);
    let l' = clhs (rule1 uo);
    check (length cs' = length cs) (showsl_lit (STR ''lengths differ''));
    check (match_rules ((l \<cdot> \<mu>, l \<cdot> \<mu>) # cs) ((l' \<cdot> \<mu>', l' \<cdot> \<mu>') # cs') \<noteq> None \<and>
      match_rules ((l' \<cdot> \<mu>', l' \<cdot> \<mu>') # cs') ((l \<cdot> \<mu>, l \<cdot> \<mu>) # cs) \<noteq> None) id;
    check_unfeasible' uo R l' \<mu>' cs'
  }) css (showsl_sep id showsl_nl)"

lemma check_unfeasible:
  assumes "isOK (check_unfeasible css R l \<mu> cs)"
  shows " quasi_decreasing (set R) \<Longrightarrow>
      \<exists>t\<^sub>0 t\<^sub>1 t\<^sub>2.
        (\<forall>\<sigma>. (\<forall>(u, v)\<in>set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow>
          (l \<cdot> \<mu> \<cdot> \<sigma>, t\<^sub>0 \<cdot> \<sigma>) \<in> (cstep (set R) \<union> {\<rhd>} \<union> {(s, t). qdstep (set R) s t})\<^sup>+) \<and>
        (t\<^sub>0, t\<^sub>1) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and>
        (t\<^sub>0, t\<^sub>2) \<in> (ctxt_step (set R) (set cs))\<^sup>* \<and>
        \<not> unifiable {(t\<^sub>1, t\<^sub>2)} \<and>
        strongly_irreducible (set R) t\<^sub>1 \<and>
        strongly_irreducible (set R) t\<^sub>2" (is "_ \<Longrightarrow> ?P l \<mu> cs")
proof -
  obtain \<pi> :: "string perm" and \<mu>' uo \<rho>\<^sub>1 \<rho>\<^sub>2 l' cs'
    where "(\<mu>', uo) \<in> set css"
    and "\<rho>\<^sub>1 = rule1 uo"
    and "\<rho>\<^sub>2 = rule2 uo"
    and l': "l' = clhs \<rho>\<^sub>1"
    and "cs' = subst_list \<mu>' (conds \<rho>\<^sub>1 @ conds \<rho>\<^sub>2)"
    and pi: " \<pi> \<bullet> ((l \<cdot> \<mu>, l \<cdot> \<mu>) # cs) = (l' \<cdot> \<mu>', l' \<cdot> \<mu>') # cs'"
    and ok: "isOK (check_unfeasible' uo R l' \<mu>' cs')"
    using assms and match_rules_imp_variants [of _ "(l \<cdot> \<mu>, l \<cdot> \<mu>) # cs"]
      by (fastforce simp: check_unfeasible_def)

    let ?S = "(cstep (set R) \<union> {\<rhd>} \<union> {(s, t). qdstep (set R) s t})\<^sup>+"
    have pi: "cs' = \<pi> \<bullet> cs" "l' \<cdot> \<mu>' = \<pi> \<bullet> (l \<cdot> \<mu>)" using pi by (auto simp: eqvt)
    { assume "quasi_decreasing (set R)"
      then have "?P l' \<mu>' cs'" using check_unfeasible' [OF ok] by auto
      then obtain t\<^sub>0 t\<^sub>1 t\<^sub>2 where *: "\<forall>\<sigma>. (\<forall>(u, v)\<in>set cs'. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow>
        (l' \<cdot> \<mu>' \<cdot> \<sigma>, \<pi> \<bullet> -\<pi> \<bullet> t\<^sub>0 \<cdot> \<sigma>) \<in> ?S"
        and 1: "(t\<^sub>0, t\<^sub>1) \<in> (ctxt_step (set R) (set cs'))\<^sup>*"
        and 2: "(t\<^sub>0, t\<^sub>2) \<in> (ctxt_step (set R) (set cs'))\<^sup>*"
        and nu: "\<not> unifiable {(t\<^sub>1, t\<^sub>2)}"
        and si1: "strongly_irreducible (set R) t\<^sub>1"
        and si2: "strongly_irreducible (set R) t\<^sub>2"
        by (auto simp: eqvt)

      have "\<forall>\<sigma>. (\<forall>(u, v)\<in>set cs. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*) \<longrightarrow> (l \<cdot> \<mu> \<cdot> \<sigma>, -\<pi> \<bullet> t\<^sub>0 \<cdot> \<sigma>) \<in> ?S"
        using * [unfolded pi] conds_sat_rel_perm [of \<pi> cs "set R" "l \<cdot> \<mu>" "-\<pi> \<bullet> t\<^sub>0" ?S] by fast
      moreover have "(-\<pi> \<bullet> t\<^sub>0, -\<pi> \<bullet> t\<^sub>1) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
        using ctxt_steps_perm [of \<pi> "-\<pi> \<bullet> t\<^sub>0" "-\<pi> \<bullet> t\<^sub>1" "set R" "set cs"] 1 [unfolded pi] by (auto simp: eqvt)
      moreover have "(-\<pi> \<bullet> t\<^sub>0, -\<pi> \<bullet> t\<^sub>2) \<in> (ctxt_step (set R) (set cs))\<^sup>*"
        using ctxt_steps_perm [of \<pi> "-\<pi> \<bullet> t\<^sub>0" "-\<pi> \<bullet> t\<^sub>2" "set R" "set cs"] 2 [unfolded pi] by (auto simp: eqvt)
      moreover have "\<not> unifiable {(-\<pi> \<bullet> t\<^sub>1, -\<pi> \<bullet> t\<^sub>2)}"
        using nu by (auto simp: unifiable_def unifiers_def permute_term_subst_apply_term)
      moreover have "strongly_irreducible (set R) (-\<pi> \<bullet> t\<^sub>1)"
        using si1 strongly_irreducible_perm [of "set R" \<pi> "-\<pi> \<bullet> t\<^sub>1"] by auto
      moreover have "strongly_irreducible (set R) (-\<pi> \<bullet> t\<^sub>2)"
        using si2 strongly_irreducible_perm [of "set R" \<pi> "-\<pi> \<bullet> t\<^sub>2"] by auto
      ultimately have "?P l \<mu> cs" by blast
    }
    then show "quasi_decreasing (set R) \<Longrightarrow> ?P l \<mu> cs" by blast
qed

lemma check_CCPs [dest]:
  assumes I: "tp_spec I" and J: "dpp_spec J" and
    "isOK (al94_ops.check_CCPs x_var y_var (check_context_joinable cj) (check_infeasible a i I J css) (check_unfeasible uo) R)" and
    "quasi_decreasing (set R)"
  shows "all_overlaps_nice (set R) (al94_spec.S R)"
proof -
  interpret al94_spec x_var y_var
    "check_context_joinable cj"
    "check_infeasible a i I J css"
    "check_unfeasible uo"
    for a i cj css uo
    apply (unfold_locales)
       apply (rule check_context_joinable; assumption)
      apply (rule check_infeasible[OF I J]; assumption)
     apply (rule check_unfeasible; assumption)
    apply force+
    done
  show ?thesis using assms isOK_check_CCPs
    unfolding all_overlaps_nice_def by fast
qed

definition check_al94
where
  "check_al94 a i I J cj css uo R = do {
    check_wf_ctrs R;
    check_adtrs R;
    al94_ops.check_CCPs x_var y_var (check_context_joinable cj) (check_infeasible a i I J css) (check_unfeasible uo) R
  } <+? (\<lambda>e. showsl_lit (STR ''Avenhaus & Loria-Saenz 1994 does not apply\<newline>'') \<circ> e)"

lemma check_al94:
  assumes I: "tp_spec I" and J: "dpp_spec J" and
    "isOK (check_al94 a i I J cj css uo R)" and "quasi_decreasing (set R)"
  shows "CR (cstep (set R))"
  using assms
  apply (intro quasi_decreasing_order_adtrs_all_CPs_unfeasible_or_context_joinable_or_infeasible_CR [of "set R" "al94_spec.S R"])
proof -
  interpret al94_spec x_var y_var
    "check_context_joinable cj"
    "check_infeasible a i I J css"
    "check_unfeasible uo"
    for a i cj css uo
    apply (unfold_locales)
       apply (rule check_context_joinable; assumption)
      apply (rule check_infeasible[OF I J]; assumption)
     apply (rule check_unfeasible; assumption)
    apply force+
  done
  show "quasi_decreasing_order (set R) (al94_spec.S R)"
    unfolding S_def
    apply (rule quasi_decreasing', insert assms(4), assumption)
    done
qed (auto simp: check_al94_def check_adtrs)

fun orig_term :: "('f \<Rightarrow> 'v option) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "orig_term m (Var x) = Var x"
| "orig_term m (Fun f []) = (case (m f) of None \<Rightarrow> Fun f [] | Some y \<Rightarrow> Var y)"
| "orig_term m (Fun f ts) = Fun f (map (orig_term m) ts)"

definition orig_crule :: "('f \<Rightarrow> 'v option) \<Rightarrow> ('f, 'v) crule \<Rightarrow> ('f, 'v) crule"
where
  "orig_crule m r =
    ((orig_term m (clhs r), orig_term m (crhs r)), map (\<lambda>(s, t). (orig_term m s, orig_term m t)) (conds r))"

fun orig_cstep :: "('f \<Rightarrow> 'v option) \<Rightarrow> ('f, 'v) cstep_proof \<Rightarrow> ('f, 'v) cstep_proof"
where
  "orig_cstep m (Cstep_step \<rho> p \<sigma> s t css) =
    Cstep_step (orig_crule m \<rho>) p (orig_term m \<circ> \<sigma>) (orig_term m s) (orig_term m t)
      (map (map (orig_cstep m)) css)"

end
