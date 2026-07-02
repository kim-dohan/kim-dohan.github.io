(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Renaming of Terms, Substitutions, TRSs, ...\<close>

theory Renaming_Interpretations
  imports
    Renaming
    First_Order_Rewriting.Trs
    First_Order_Rewriting.Unification_More
    First_Order_Rewriting.Unifiers_More
begin

lemma variants_imp_bij_betw_vars:
  assumes "s \<cdot> \<sigma> = t" and "t \<cdot> \<tau> = s"
  shows "bij_betw (the_Var \<circ> \<sigma>) (vars_term s) (vars_term t)"
proof -
  have id: "(the_Var \<circ> \<sigma>) ` vars_term s = vars_term t"
    using variants_imp_image_vars_term_eq [OF assms] by simp
  then have "card (vars_term t) \<le> card (vars_term s)"
    by (metis card_image_le finite_vars_term)
  moreover have "(the_Var \<circ> \<tau>) ` vars_term t = vars_term s"
    using variants_imp_image_vars_term_eq [OF assms(2, 1)] by simp
  ultimately have "card (vars_term t) = card (vars_term s)"
    by (metis card_image_le eq_iff finite_vars_term)
  then have "card ((the_Var \<circ> \<sigma>) ` vars_term s) = card (vars_term s)"
    using id by auto
  from finite_card_eq_imp_bij_betw [OF _ this] id
    show ?thesis by auto
qed

text \<open>When two terms are substitution instances of each other, then
there is a variable renaming (with finite domain) between them.\<close>
lemma variants_imp_renaming:
  fixes s t :: "('f, 'v) term"
  assumes "s \<cdot> \<sigma> = t" and "t \<cdot> \<tau> = s"
  shows "\<exists>f. bij f \<and> finite {x. f x \<noteq> x} \<and> s \<cdot> (Var \<circ> f) = t"
proof -
  from variants_imp_bij_betw_vars [OF assms, THEN bij_betw_extend, of UNIV]
    obtain g where *: "\<forall>x\<in>vars_term s. g x = (the_Var \<circ> \<sigma>) x"
    and "finite {x. g x \<noteq> x}"
    and "bij g" by auto
  moreover have 1: "\<forall>x\<in>vars_term s. (Var \<circ> g) x = \<sigma> x"
  proof
    fix x
    assume "x \<in> vars_term s"
    with * have "g x = (the_Var \<circ> \<sigma>) x" by simp
    with variants_imp_is_Var [OF assms] and \<open>x \<in> vars_term s\<close>
      show "(Var \<circ> g) x = \<sigma> x" by simp
  qed
  moreover have "s \<cdot> (Var \<circ> g) = t"
    using 1 \<open>s \<cdot> \<sigma> = t\<close> by (auto simp: term_subst_eq_conv)
  ultimately show ?thesis by blast
qed

text \<open>Turning a permutation into a substitution.\<close>
abbreviation "sop \<pi> \<equiv> Var \<circ> Rep_perm \<pi>"

fun permute_term :: "'v perm \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "permute_term p (Var x) = Var (permute_atom p x)" |
  "permute_term p (Fun f ts) = Fun f (map (permute_term p) ts)"

interpretation term_pt: permutation_type permute_term
  apply unfold_locales
  subgoal for x by (induct x, auto simp: map_idI)
  subgoal for p q x by (induct x, auto simp: map_idI)
  done


adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_term and
  FRESH \<rightleftharpoons> term_pt.fresh term_pt.fresh_set

interpretation terms_pt: list_pt permute_term ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> terms_pt.permute_list and
  FRESH \<rightleftharpoons> terms_pt.fresh

lemma supp_Var:
  fixes x :: "'v :: infinite"
  shows "term_pt.supp (Var x) = {x}"
  using infinite_UNIV
  by (auto simp: term_pt.supp_def swap_atom)

lemma permute_Fun:
  fixes p :: "('v :: infinite) perm"
  shows "p \<bullet> (Fun f ss) = Fun f (p \<bullet> ss)"
  by (induct ss) (simp)+

lemma supp_Fun':
  "term_pt.supp (Fun f ss) = permutation_type.supp (\<bullet>) ss"
  by (simp only: term_pt.supp_def terms_pt.supp_def permute_Fun) auto

lemma supp_Fun:
  "term_pt.supp (Fun f ss) = (\<Union>s\<in>set ss. term_pt.supp s)"
  by (simp add: supp_Fun')

lemma supp_vars_term_eq:
  fixes t :: "('f, 'v :: infinite) term"
  shows "term_pt.supp t = vars_term t"
by (induct t) (simp add: supp_Var supp_Fun)+

interpretation subst_conjugate_pt: fun_pt permute_atom permute_term ..

abbreviation "conjugate_subst \<equiv> subst_conjugate_pt.permute_fun"

lemma term_apply_subst_eqvt [eqvt]:
  "p \<bullet> (t \<cdot> \<sigma>) = (p \<bullet> t) \<cdot> (conjugate_subst p \<sigma>)"
  by (induct t) (simp add: subst_conjugate_pt.permute_fun_def)+

definition permute_subst :: "('v :: infinite) perm \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
where
  "permute_subst \<pi> \<sigma> x = \<pi> \<bullet> \<sigma> x"

interpretation subst_pt: permutation_type permute_subst
  by standard (simp add: permute_subst_def [abs_def])+

adhoc_overloading
  PERMUTE \<rightleftharpoons> "permute_subst" and
  FRESH \<rightleftharpoons> subst_pt.fresh

fun permute_ctxt :: "'v perm \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) ctxt"
where
  "permute_ctxt p \<box> = \<box>" |
  "permute_ctxt p (More f ss1 C ss2) =
    More f (map (permute_term p) ss1) (permute_ctxt p C) (map (permute_term p) ss2)"

interpretation ctxt_pt: permutation_type permute_ctxt
  apply unfold_locales
  subgoal for x by (induct x, auto simp: map_idI)
  subgoal for p q x by (induct x, auto simp: map_idI)
  done

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_ctxt and
  FRESH \<rightleftharpoons> ctxt_pt.fresh

lemma supp_Hole:
  "ctxt_pt.supp \<box> = {}"
  by (simp add: ctxt_pt.supp_def)

lemma permute_More:
  fixes p :: "('v :: infinite) perm"
  shows "p \<bullet> (More f ss1 C ss2) = More f (p \<bullet> ss1) (p \<bullet> C) (p \<bullet> ss2)"
  by (simp)

lemma supp_More':
  "ctxt_pt.supp (More f ss1 C ss2) =
    permutation_type.supp (\<bullet>) ss1 \<union> ctxt_pt.supp C \<union>  permutation_type.supp (\<bullet>) ss2"
  by (simp only: ctxt_pt.supp_def terms_pt.supp_def) auto

lemma supp_More:
  "ctxt_pt.supp (More f ss1 C ss2) =
    (\<Union>s\<in>set ss1. term_pt.supp s) \<union> ctxt_pt.supp C \<union> (\<Union>s\<in>set ss2. term_pt.supp s)"
  by (simp add: supp_More')

lemma supp_vars_ctxt_eq:
  fixes C :: "('f, 'v :: infinite) ctxt"
  shows "ctxt_pt.supp C = vars_ctxt C"
  by (induct C) (auto simp: supp_Hole supp_More supp_vars_term_eq)

lemma term_apply_ctxt_eqvt [eqvt]:
  fixes p :: "('v :: infinite) perm"
  shows "p \<bullet> (C\<langle>t\<rangle>) = (p \<bullet> C)\<langle>p \<bullet> t\<rangle>"
  by (induct C) simp+

interpretation rule_pt: prod_pt permute_term permute_term ..
interpretation rules_pt: list_pt rule_pt.permute_prod ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> rule_pt.permute_prod rules_pt.permute_list and
  FRESH \<rightleftharpoons> rule_pt.fresh rule_pt.fresh_set rules_pt.fresh rules_pt.fresh_set

lemma supp_vars_rule_eq:
  fixes r :: "('f, 'v :: infinite) rule"
  shows "rule_pt.supp r = vars_term (fst r) \<union> vars_term (snd r)"
  by (cases r) (simp add: supp_vars_term_eq)

interpretation trs_pt: rel_pt permute_term ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> trs_pt.permute_set and
  FRESH \<rightleftharpoons> trs_pt.fresh

interpretation term_set_pt: set_pt permute_term ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> term_set_pt.permute_set and
  FRESH \<rightleftharpoons> term_set_pt.fresh

lemma rule_mem_trs_iff [iff]:
  fixes p :: "('v :: infinite) perm" and R :: "('f, 'v) term rel"
  shows "(p \<bullet> s, p \<bullet> t) \<in> p \<bullet> R \<longleftrightarrow> (s, t) \<in> R"
unfolding rule_pt.permute_prod.simps [symmetric] trs_pt.mem_permute_iff ..

lemma inv_rule_mem_trs_simps [simp]:
  fixes p :: "('v :: infinite) perm" and R :: "('f, 'v) term rel"
  shows "(-p \<bullet> s, -p \<bullet> t) \<in> R \<longleftrightarrow> (s, t) \<in> p \<bullet> R"
    and "(s, t) \<in> -p \<bullet> R \<longleftrightarrow> (p \<bullet> s, p \<bullet> t) \<in> R"
  unfolding rule_pt.permute_prod.simps [symmetric]
  by (metis trs_pt.inv_mem_simps(1))
     (metis trs_pt.inv_mem_simps(2))

lemma symcl_trs_eqvt [eqvt]: "\<pi> \<bullet> R\<^sup>\<leftrightarrow> = (\<pi> \<bullet> R)\<^sup>\<leftrightarrow>"
  by (auto simp: eqvt)
   (meson converse_iff inv_rule_mem_trs_simps(1))+

lemma term_apply_subst_Var_Rep_perm [simp]:
  "t \<cdot> sop p = p \<bullet> t"
  by (induct t) (simp add: permute_atom_def)+

lemma rstep_permute_subset:
  "rstep (p \<bullet> R) \<subseteq> rstep R"
proof (rule subrelI)
  fix s t
  assume "(s, t) \<in> rstep (p \<bullet> R)"
  then show "(s, t) \<in> rstep R"
  proof (rule rstepE)
    fix l r C \<sigma>
    presume "(l, r) \<in> p \<bullet> R" and [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    then have "(-p \<bullet> l, -p \<bullet> r) \<in> R" by simp
    then have "((-p \<bullet> l) \<cdot> sop p, (-p \<bullet> r) \<cdot> sop p) \<in> rstep R" by blast
    then show "(s, t) \<in> rstep R" by auto
  qed auto
qed

text \<open>The rewrite relation is invariant under variable renamings of the given TRS.\<close>
lemma rstep_permute [simp]:
  "rstep (p \<bullet> R) = rstep R"
proof
  show "rstep (p \<bullet> R) \<subseteq> rstep R" by (rule rstep_permute_subset)
next
  have "rstep R = rstep (-p \<bullet> p \<bullet> R)" by simp
  also have "\<dots> \<subseteq> rstep (p \<bullet> R)" by (rule rstep_permute_subset)
  finally show "rstep R \<subseteq> rstep (p \<bullet> R)" .
qed

lemma permute_rstep_subset:
  "p \<bullet> rstep R \<subseteq> rstep R"
proof (rule subrelI)
  fix s t
  assume "(s, t) \<in> p \<bullet> rstep R"
  then have "(-p \<bullet> s, -p \<bullet> t) \<in> rstep R" by simp
  then show "(s, t) \<in> rstep R"
  proof (induct x\<equiv>"-p \<bullet> s" y\<equiv>"-p \<bullet> t")
    case (IH C \<sigma> l r)
    then have "(p \<bullet> l, p \<bullet> r) \<in> p \<bullet> R"
      and [simp]: "s = p \<bullet> C\<langle>l \<cdot> \<sigma>\<rangle>" "t = p \<bullet> C\<langle>r \<cdot> \<sigma>\<rangle>" by simp+
    then have "((p \<bullet> C)\<langle>(p \<bullet> l) \<cdot> (conjugate_subst p \<sigma>)\<rangle>,
                (p \<bullet> C)\<langle>(p \<bullet> r) \<cdot> (conjugate_subst p \<sigma>)\<rangle>) \<in> rstep (p \<bullet> R)" by blast
    then show "(s, t) \<in> rstep R" by (simp add: eqvt)
  qed
qed

lemma permute_rstep [simp]:
  "p \<bullet> rstep R = rstep R"
proof
  show "p \<bullet> rstep R \<subseteq> rstep R" by (rule permute_rstep_subset)
next
  have "rstep R = p \<bullet> -p \<bullet> rstep R" by simp
  also have "\<dots> \<subseteq> p \<bullet> rstep R"
    using permute_rstep_subset [of "-p" R] by auto
  finally show "rstep R \<subseteq> p \<bullet> rstep R" .
qed

lemma rstep_eqvt [eqvt]:
  "p \<bullet> rstep R = rstep (p \<bullet> R)"
  by simp

lemma rstep_imp_perm_rstep:
  "(s, t) \<in> rstep R \<Longrightarrow> (p \<bullet> s, p \<bullet> t) \<in> rstep R"
  by (subst (asm) rule_mem_trs_iff [symmetric]) (simp add: eqvt)

lemma perm_rstep_imp_rstep:
  "(p \<bullet> s, p \<bullet> t) \<in> rstep R \<Longrightarrow> (s, t) \<in> rstep R"
  by (subst (asm) rule_mem_trs_iff [symmetric, of _ _ _ "-p"]) (simp add: eqvt)

lemma rstep_permute_iff [iff]:
  "(p \<bullet> s, p \<bullet> t) \<in> rstep R \<longleftrightarrow> (s, t) \<in> rstep R"
  by (metis perm_rstep_imp_rstep rstep_imp_perm_rstep)

lemma term_apply_subst_Var_Abs_perm:
  "f \<in> perms \<Longrightarrow> t \<cdot> (Var \<circ> f) = Abs_perm f \<bullet> t"
  by (metis Abs_perm_inverse term_apply_subst_Var_Rep_perm)

lemma finite_term_supp: "finite (term_pt.supp t)"
  unfolding supp_vars_term_eq
  by (induct t) simp+

lemma finite_rule_supp: "finite (rule_pt.supp (l, r))"
  by (simp add: finite_term_supp)

interpretation term_fs: finitely_supported permute_term
  by standard (rule finite_term_supp)

interpretation rule_fs: finitely_supported rule_pt.permute_prod
  by standard (auto simp: finite_rule_supp finite_term_supp)

lemma vars_rule_disjoint:
  fixes l r u v :: "('f, 'v :: infinite) term"
  shows "\<exists>p. vars_rule (p \<bullet> (l, r)) \<inter> vars_rule (u, v) = {}"
proof -
  from rule_fs.supp_fresh_set obtain p
    where "rule_pt.supp (p \<bullet> (l, r)) \<sharp> (u, v)" by blast
  from rule_pt.fresh_set_disjoint [OF this]
    show ?thesis
    by (auto simp: supp_vars_rule_eq vars_rule_def)
qed

lemma vars_term_eqvt [eqvt]:
  "\<pi> \<bullet> vars_term t = vars_term (\<pi> \<bullet> t)"
  by (simp add: supp_vars_term_eq [symmetric] eqvt)

lemma permute_term_subst_apply_term:
  "(\<pi> \<bullet> t) \<cdot> \<sigma> = t \<cdot> (\<sigma> \<circ> Rep_perm \<pi>)"
  by (induct t) (simp_all add: permute_atom_def)

lemma permute_subst_subst_compose:
  "\<pi> \<bullet> \<sigma> = \<sigma> \<circ>\<^sub>s sop \<pi>"
  by (rule ext) (simp add: subst_compose_def permute_subst_def)

lemma vars_rule_eqvt [eqvt]:
  "\<pi> \<bullet> vars_rule r = vars_rule (\<pi> \<bullet> r)"
  by (simp add: vars_rule_def) (metis rule_fs.supp_eqvt supp_vars_rule_eq)

lemma fun_poss_perm_simp [simp]:
  "fun_poss (\<pi> \<bullet> t) = fun_poss t"
  by (induct t) auto

lemma poss_perm_simp [simp]:
  "poss (\<pi> \<bullet> t) = poss t"
  by (induct t) auto

definition permute_pos :: "'a perm \<Rightarrow> pos \<Rightarrow> pos"
where
  "permute_pos \<pi> (p :: pos) = p"

interpretation pos_pure: pure permute_pos
  by standard (simp_all add: permute_pos_def)

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_pos

interpretation pos_set_pt: set_pt permute_pos ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> pos_set_pt.permute_set

interpretation pos_set_pure: pure pos_set_pt.permute_set
  by standard (simp add: permute_pos_def pos_set_pt.permute_set_def)

lemma fun_poss_eqvt [eqvt]:
  "\<pi> \<bullet> fun_poss t = fun_poss (\<pi> \<bullet> t)"
  by simp

lemma poss_eqvt [eqvt]:
  "\<pi> \<bullet> poss t = poss (\<pi> \<bullet> t)"
  by simp

lemma subt_at_eqvt [eqvt]:
  "p \<in> poss t \<Longrightarrow> \<pi> \<bullet> (t |_ p) = (\<pi> \<bullet> t) |_ p"
  by (induct t p rule: subt_at.induct)
     (auto simp del: subt_at_Cons_distr)

lemma subst_variants_id:
  assumes variants: "\<sigma> \<circ>\<^sub>s \<sigma>' = \<tau>" "\<tau> \<circ>\<^sub>s \<tau>' = \<sigma>"
    and x: "x \<in> \<Union>(vars_term ` \<sigma> ` V)" (is "x \<in> ?D")
  shows "(the_Var \<circ> \<tau>') ((the_Var \<circ> \<sigma>') x) = x" (is "?\<tau>' (?\<sigma>' x) = x")
proof -
  note * [simp] = subst_variants_imp_eq [OF variants]
  { fix y
    assume **: "x \<in> vars_term (\<sigma> y)"
    then have var: "is_Var (\<sigma>' x)"
      using variants_imp_is_Var [OF *] by simp
    have "\<And>\<mu>. \<mu> x = Var x \<or> \<sigma> y \<cdot> \<mu> \<noteq> \<sigma> y"
      using ** by (metis subst_apply_term_empty term_subst_eq_rev)
    then have "\<And>\<mu> \<nu>. (\<nu> x) \<cdot> \<mu> = Var x \<or> \<sigma> y \<cdot> \<nu> \<cdot> \<mu> \<noteq> \<sigma> y"
      by (metis eval_term.simps(1) subst_subst)
    then have "?\<tau>' (?\<sigma>' x) = x"
      using var and * by (metis term.collapse(1) eval_term.simps(1) term.sel(1) o_def) }
  then show ?thesis using x by auto
qed

lemma subst_variants_image_subset:
  assumes variants: "\<sigma> \<circ>\<^sub>s \<sigma>' = \<tau>" "\<tau> \<circ>\<^sub>s \<tau>' = \<sigma>"
  shows "(the_Var \<circ> \<sigma>') ` \<Union>(vars_term ` \<sigma> ` V) \<subseteq> \<Union>(vars_term ` \<tau> ` V)"
  (is "?\<sigma>' ` ?S \<subseteq> ?T")
proof
  note * = subst_variants_imp_eq [OF variants]
  have subst_fun_range_subset: "?S \<subseteq> subst_fun_range \<sigma>" by (auto simp: subst_fun_range_def)
  note is_Var = subst_variants_imp_is_Var [OF variants]

  fix x\<^sub>0
  assume "x\<^sub>0 \<in> ?\<sigma>' ` ?S"
  then obtain x where **: "?\<sigma>' x = x\<^sub>0" and "x \<in> ?S" by blast
  then obtain x' where "x \<in> vars_term (\<sigma> x')" and "x' \<in> V" by (auto)
  then have "\<sigma> x' \<unrhd> Var x" by (metis supteq_Var)
  then have "\<sigma> x' \<cdot> \<sigma>' \<unrhd> \<sigma>' x" by auto
  then have "\<tau> x' \<unrhd> \<sigma>' x" by (simp add: *)
  moreover
  from is_Var and subst_fun_range_subset and \<open>x \<in> ?S\<close> have "is_Var (\<sigma>' x)" by auto
  ultimately have "?\<sigma>' x \<in> vars_term (\<tau> x')"
    by (metis term.collapse(1) comp_def subteq_Var_imp_in_vars_term)
  then have "?\<sigma>' x \<in> ?T" using \<open>x' \<in> V\<close> by (auto simp:)
  then show "x\<^sub>0 \<in> ?T" unfolding ** .
qed

lemma subst_variants_imp_image_eq:
  assumes "\<sigma> \<circ>\<^sub>s \<sigma>' = \<tau>" and "\<tau> \<circ>\<^sub>s \<tau>' = \<sigma>"
  shows "(the_Var \<circ> \<sigma>') ` \<Union>(vars_term ` \<sigma> ` V) = \<Union>(vars_term ` \<tau> ` V)"
  (is "?\<sigma>' ` ?S = ?T")
proof
  show "?\<sigma>' ` ?S \<subseteq> ?T"
    using subst_variants_image_subset [OF assms, of V] by (simp)
next
  let ?\<tau>' = "the_Var \<circ> \<tau>'"
  have "?\<sigma>' ` ?\<tau>' ` ?T \<subseteq> ?\<sigma>' ` ?S"
    using subst_variants_image_subset [OF assms(2, 1), of V] by (metis image_mono)
  moreover have "?\<sigma>' ` ?\<tau>' ` ?T = ?T"
    using subst_variants_id [OF assms(2, 1), of _ V]
    by (auto simp: o_def) (metis, metis (full_types) UN_I image_eqI)
  ultimately show "?T \<subseteq> ?\<sigma>' ` ?S" by simp
qed

text \<open>If two variables are substitution instances of each other, then they only differ
by a variable renaming.\<close>
lemma subst_variants_imp_perm:
  fixes \<sigma> \<tau> :: "('f, 'v :: infinite) subst"
  assumes variants: "\<sigma> \<circ>\<^sub>s \<sigma>' = \<tau>" "\<tau> \<circ>\<^sub>s \<tau>' = \<sigma>"
    and finite: "finite (subst_domain \<sigma>)" "finite (subst_domain \<tau>)"
  shows "\<exists>\<pi>. \<pi> \<bullet> \<sigma> = \<tau>"
proof -
  define D where "D = subst_domain \<sigma> \<union> subst_domain \<tau>"
  define D\<^sub>\<sigma> where "D\<^sub>\<sigma> = \<Union>(vars_term ` \<sigma> ` D)"
  define D\<^sub>\<tau> where "D\<^sub>\<tau> = \<Union>(vars_term ` \<tau> ` D)"
  let ?\<sigma>' = "the_Var \<circ> \<sigma>'"
  let ?\<tau>' = "the_Var \<circ> \<tau>'"

  note * = subst_variants_imp_eq [OF variants]
  note is_Var = subst_variants_imp_is_Var [OF variants]

  have finite: "finite D\<^sub>\<sigma>" using finite by (auto simp: D\<^sub>\<sigma>_def D_def)
  have subst_fun_range_subset: "D\<^sub>\<sigma> \<subseteq> subst_fun_range \<sigma>" by (auto simp: D\<^sub>\<sigma>_def subst_fun_range_def)
  have id: "\<And>x. x \<notin> D \<Longrightarrow> \<sigma>' x = Var x" "\<And>x. x \<notin> D \<Longrightarrow> \<tau>' x = Var x"
           "\<And>x. x \<notin> D \<Longrightarrow> \<sigma> x = Var x" "\<And>x. x \<notin> D \<Longrightarrow> \<tau> x = Var x"
    using * by (auto simp: D_def subst_domain_def) (metis eval_term.simps(1))+

  have "?\<sigma>' ` D\<^sub>\<sigma> = D\<^sub>\<tau>"
    using subst_variants_imp_image_eq [OF variants] by (simp add: D\<^sub>\<sigma>_def D\<^sub>\<tau>_def)
  moreover have "inj_on ?\<sigma>' D\<^sub>\<sigma>"
    by (rule inj_on_inverseI [of _ "?\<tau>'"]) (insert subst_variants_id [OF variants], simp add: D\<^sub>\<sigma>_def)
  ultimately have "bij_betw ?\<sigma>' D\<^sub>\<sigma> D\<^sub>\<tau>" by (auto simp: bij_betw_def)
  from bij_betw_extend [OF this, of UNIV] and finite obtain g
    where "finite {x. g x \<noteq> x}" and g_id: "(\<forall>x\<in>UNIV - (D\<^sub>\<sigma> \<union> D\<^sub>\<tau>). g x = x)"
      and g_eq: "\<forall>x\<in>D\<^sub>\<sigma>. g x = (the_Var \<circ> \<sigma>') x" and "bij g" by blast
  then have perm: "g \<in> perms" by (auto simp: perms_def)
  have "Abs_perm g \<bullet> \<sigma> = \<tau>"
  proof (rule ext)
    fix x
    have "Abs_perm g \<bullet> \<sigma> x = \<tau> x"
    proof (cases "x \<in> D")
      assume "x \<in> D"
      then have "vars_term (\<sigma> x) \<subseteq> D\<^sub>\<sigma>" by (auto simp: D\<^sub>\<sigma>_def)
      with g_eq and term_subst_eq [of "\<sigma> x" "Var \<circ> g" "\<sigma>'"]
        have "\<sigma> x \<cdot> (Var \<circ> g) = \<sigma> x \<cdot> \<sigma>'"
        by auto (metis subst_fun_range_subset(1) term.collapse(1) is_Var(1) set_rev_mp)
      with perm and * show ?thesis by (simp add: term_apply_subst_Var_Abs_perm)
    next
      have "D\<^sub>\<tau> - D \<subseteq> D\<^sub>\<sigma> - D"
      proof -
        have id: "?\<tau>' ` (D\<^sub>\<tau> - D) = D\<^sub>\<tau> - D"
          using id by auto 
        have "?\<tau>' ` (D\<^sub>\<tau> - D) \<subseteq> ?\<tau>' ` D\<^sub>\<tau>" by blast
        also have "... \<subseteq> D\<^sub>\<sigma>"
          using subst_variants_image_subset [OF variants(2, 1), of D] by (simp add: D\<^sub>\<tau>_def D\<^sub>\<sigma>_def)
        finally show ?thesis unfolding id by auto
      qed
      then have **: "D\<^sub>\<tau> - D\<^sub>\<sigma> \<subseteq> D" by blast
      assume "x \<notin> D"
      moreover then have "Abs_perm g \<bullet> x = x"
        using g_eq and id and g_id and perm and **
        by (cases "x \<in> D\<^sub>\<sigma>") (auto simp: permute_atom_def Abs_perm_inverse)
      ultimately show ?thesis by (simp add: id)
    qed
    then show "(Abs_perm g \<bullet> \<sigma>) x = \<tau> x" by (simp add: permute_subst_def)
  qed
  then show ?thesis ..
qed

lemma is_mgu_imp_perm:
  fixes E :: "('f, 'v :: infinite) equations"
  assumes mgu: "is_mgu \<sigma> E" "is_mgu \<tau> E"
    and finite: "finite (subst_domain \<sigma>)" "finite (subst_domain \<tau>)"
  shows "\<exists>\<pi>. \<pi> \<bullet> \<sigma> = \<tau>"
proof -
  obtain \<sigma>' \<tau>' :: "('f, 'v) subst"
    where "\<sigma> \<circ>\<^sub>s \<sigma>' = \<tau>" and "\<tau> \<circ>\<^sub>s \<tau>' = \<sigma>"
    using mgu by (auto simp: is_mgu_def unifiers_def) metis
  from subst_variants_imp_perm [OF this finite]
    show ?thesis .
qed

lemma unifiers_perm_simp [simp]:
  "\<pi> \<bullet> \<sigma> \<in> unifiers E \<longleftrightarrow> \<sigma> \<in> unifiers E"
  by (auto simp: unifiers_def permute_subst_subst_compose)

lemma inv_Rep_perm_simp [simp]:
  fixes x :: "'v :: infinite"
  shows "-\<pi> \<bullet> Rep_perm \<pi> x = x"
  by (simp add: permute_atom_def Rep_perm_uminus)
     (metis Rep_perm_uminus atom_pt.permute_minus_cancel(2) permute_atom_def)

lemma permute_subst_conjugate_subst [simp]:
  "(\<pi> \<bullet> \<sigma>) \<circ>\<^sub>s conjugate_subst \<pi> \<tau> = \<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s (Var \<circ> Rep_perm \<pi>))"
  apply (rule ext)
  apply (simp add: subst_conjugate_pt.permute_fun_def)
  apply (simp add: permute_subst_subst_compose ac_simps)
  apply (simp add: subst_compose_def)
done

text \<open>Every renaming of an mgu is again an mgu.\<close>
lemma is_mgu_perm:
  fixes E :: "('f, 'v :: infinite) equations"
  assumes "is_mgu \<sigma> E"
  shows "is_mgu (\<pi> \<bullet> \<sigma>) E"
proof (unfold is_mgu_def, intro conjI ballI)
  show "\<pi> \<bullet> \<sigma> \<in> unifiers E" using assms by (simp add: is_mgu_def)
next
  fix \<tau> :: "('f, 'v) subst"
  assume "\<tau> \<in> unifiers E"
  then obtain \<gamma> :: "('f, 'v) subst"
    where "\<tau> = \<sigma> \<circ>\<^sub>s \<gamma>" using assms by (auto simp: is_mgu_def)
  then have "\<tau> \<circ>\<^sub>s sop \<pi> = (\<pi> \<bullet> \<sigma>) \<circ>\<^sub>s conjugate_subst \<pi> \<gamma>"
    by (simp add: ac_simps)
  then have "\<tau> \<circ>\<^sub>s sop \<pi> \<circ>\<^sub>s sop (-\<pi>) =
    (\<pi> \<bullet> \<sigma>) \<circ>\<^sub>s conjugate_subst \<pi> \<gamma> \<circ>\<^sub>s sop (-\<pi>)" by simp
  then have "\<tau> = (\<pi> \<bullet> \<sigma>) \<circ>\<^sub>s conjugate_subst \<pi> \<gamma> \<circ>\<^sub>s sop (-\<pi>)"
    by (simp add: subst_compose_def)
  then have "\<tau> = (\<pi> \<bullet> \<sigma>) \<circ>\<^sub>s (conjugate_subst \<pi> \<gamma> \<circ>\<^sub>s sop (-\<pi>))"
    unfolding subst_compose_assoc .
  then show "\<exists>\<gamma>::('f, 'v) subst. \<tau> = (\<pi> \<bullet> \<sigma>) \<circ>\<^sub>s \<gamma>" by blast
qed

lemma Rep_perm_image:
  "Rep_perm \<pi> ` A = \<pi> \<bullet> A"
  by (metis atom_set_pt.permute_set_eq_image image_cong permute_atom_def)

(*Can this be proved abstractly, i.e.,
"finite (supp a) ==> ALL x : supp a. p \<bullet> x = p' \<bullet> x ==> p \<bullet> a = p' \<bullet> a"?*)
lemma vars_term_perm_eq:
  assumes "\<forall>x\<in>vars_term t. \<pi> \<bullet> x = \<pi>' \<bullet> x"
  shows "\<pi> \<bullet> t = \<pi>' \<bullet> t"
  using assms by (induct t) simp_all

lemma vars_rule_perm_eq:
  assumes "\<forall>x\<in>vars_rule r. \<pi> \<bullet> x = \<pi>' \<bullet> x"
  shows "\<pi> \<bullet> r = \<pi>' \<bullet> r"
  using assms by (cases r) (auto simp: vars_rule_def vars_term_perm_eq eqvt)

lemma rule_variants_imp_perm:
  assumes disj: "vars_rule (\<pi>\<^sub>1 \<bullet> r) \<inter> vars_rule (\<pi>\<^sub>2 \<bullet> r') = {}" (is "?V \<inter> ?V' = {}")
                "vars_rule (\<pi>\<^sub>3 \<bullet> r) \<inter> vars_rule (\<pi>\<^sub>4 \<bullet> r') = {}" (is "?W \<inter> ?W' = {}")
  shows "\<exists>\<pi>. \<pi> \<bullet> \<pi>\<^sub>3 \<bullet> r = \<pi>\<^sub>1 \<bullet> r \<and> \<pi> \<bullet> \<pi>\<^sub>4 \<bullet> r' = \<pi>\<^sub>2 \<bullet> r'"
proof -
  let ?f = "Rep_perm (\<pi>\<^sub>1 + -\<pi>\<^sub>3)"
  let ?g = "Rep_perm (\<pi>\<^sub>2 + -\<pi>\<^sub>4)"
  have "bij ?f" by (metis bij_Rep_perm)
  then have bij: "bij_betw ?f ?W (?f ` ?W)" by (auto elim: bij_betw_subset)
  have "bij ?g" by (metis bij_Rep_perm)
  then have bij': "bij_betw ?g ?W' (?g ` ?W')" by (auto elim: bij_betw_subset)
  define f where "f \<equiv> \<lambda>x. if x \<in> vars_rule (\<pi>\<^sub>3 \<bullet> r) then ?f x else x"
  define g where "g \<equiv> \<lambda>x. if x \<in> vars_rule (\<pi>\<^sub>4 \<bullet> r') then ?g x else x"
  define h where "h \<equiv> \<lambda>x. if x \<in> vars_rule (\<pi>\<^sub>3 \<bullet> r) then f x else if x \<in> vars_rule (\<pi>\<^sub>4 \<bullet> r') then g x else x"
  have bij: "bij_betw f ?W (f ` ?W)" using bij by (auto simp: f_def bij_betw_def inj_on_def)
  have bij': "bij_betw g ?W' (g ` ?W')" using bij' by (auto simp: g_def bij_betw_def inj_on_def)
  have *: "f ` ?W' = ?W'" "g ` ?W = ?W" using disj(2) by (auto simp: f_def g_def)
  have **: "h ` ?W' = g ` ?W'" "h ` ?W = f ` ?W" using disj(2) by (auto simp: h_def)
  have ***: "f ` ?W = ?V" "g ` ?W' = ?V'" using disj by (auto simp: f_def g_def eqvt Rep_perm_image)
  have "bij_betw h ?W ?V"
    using bij by (auto simp: *** bij_betw_def h_def inj_on_def)
  moreover have "bij_betw h ?W' ?V'"
    using bij' and disj
    apply (simp add: * ** *** bij_betw_def h_def inj_on_def)
    apply (intro conjI set_eqI iffI)
    subgoal by auto
    subgoal by auto (metis "***"(2) imageI)
    subgoal by auto (metis "***"(2) Compl_eq Diff_eq Diff_triv Int_commute)
    done
  moreover have "h ` ?W \<inter> h ` ?W' = {}"
    unfolding ** *** using disj(1) .
  ultimately have "bij_betw h (?W \<union> ?W') (?V \<union> ?V')"
    using  bij_betw_combine [of h ?W ?V ?W' ?V']
    unfolding ** *** by blast
  from conjI [THEN bij_betw_extend [OF this, of UNIV, simplified], OF finite_vars_rule finite_vars_rule]
    obtain b
    where "finite {x. b x \<noteq> x}"
    and neq: "\<forall>x\<in>UNIV - ((?W \<union> ?W') \<union> (?V \<union> ?V')). b x = x"
    and eq: "\<forall>x\<in>?W \<union> ?W'. b x = h x"
    and "bij b"
    by auto
  then have perm: "b \<in> perms" by (auto simp: perms_def)
  have "Abs_perm b \<bullet> \<pi>\<^sub>3 \<bullet> r = \<pi>\<^sub>1 \<bullet> r"
  proof -
    have "Abs_perm b \<bullet> \<pi>\<^sub>3 \<bullet> r = Abs_perm ?f \<bullet> \<pi>\<^sub>3 \<bullet> r"
    apply (rule vars_rule_perm_eq)
    apply (insert eq perm)
    apply (simp add: h_def f_def g_def Abs_perm_inverse Rep_perm permute_atom_def split: if_splits)
    done
    also have "\<dots> = \<pi>\<^sub>1 \<bullet> r" by (simp add: Rep_perm_inverse)
    finally show ?thesis .
  qed
  moreover have "Abs_perm b \<bullet> \<pi>\<^sub>4 \<bullet> r' = \<pi>\<^sub>2 \<bullet> r'"
  proof -
    have "Abs_perm b \<bullet> \<pi>\<^sub>4 \<bullet> r' = Abs_perm ?g \<bullet> \<pi>\<^sub>4 \<bullet> r'"
    apply (rule vars_rule_perm_eq)
    apply (insert eq perm disj)
    apply (auto simp add: h_def f_def g_def Abs_perm_inverse Rep_perm permute_atom_def split: if_splits)
    done
    also have "\<dots> = \<pi>\<^sub>2 \<bullet> r'" by (simp add: Rep_perm_inverse)
    finally show ?thesis .
  qed
  ultimately show ?thesis by blast
qed

lemma poss_perm_prod_simps [simp]:
  "poss (fst (\<pi> \<bullet> r)) = poss (fst r)"
  "poss (snd (\<pi> \<bullet> r)) = poss (snd r)"  
  by (cases r, auto simp: eqvt)+

lemma ctxt_of_pos_term_eqvt [eqvt]:
  assumes "p \<in> poss t"
  shows "\<pi> \<bullet> (ctxt_of_pos_term p t) = ctxt_of_pos_term p (\<pi> \<bullet> t)"
  using assms by (induct t arbitrary: p) (auto simp: take_map drop_map)

lemma finite_subst_domain_sop:
  "finite (subst_domain (sop \<pi>))"
  by (auto simp: subst_domain_def finite_Rep_perm)

lemma fun_poss_perm_iff [simp]:
  "p \<in> fun_poss (\<pi> \<bullet> t) \<longleftrightarrow> p \<in> fun_poss t"
  by (induct t) auto

lemma perm_rstep_conv [simp]:
  "\<pi> \<bullet> p \<in> rstep R \<longleftrightarrow> p \<in> rstep R"
  by (metis rstep_eqvt rstep_permute trs_pt.mem_permute_iff)

lemma perm_rstep_perm:
  assumes "(\<pi> \<bullet> s, t) \<in> rstep R"
  shows "\<exists>u. t = \<pi> \<bullet> u"
  using assms by (metis term_pt.permute_minus_cancel(1))

lemma perm_rsteps_perm:
  assumes "(\<pi> \<bullet> s, t) \<in> (rstep R)\<^sup>*"
  shows "\<exists>u. t = \<pi> \<bullet> u"
  using assms by (metis term_pt.permute_minus_cancel(1))

lemma perm_rsteps_conv [simp]:
  "\<pi> \<bullet> p \<in> (rstep R)\<^sup>* \<longleftrightarrow> p \<in> (rstep R)\<^sup>*"
  by (metis perm_rstep_conv rstep_rtrancl_idemp)

lemma perm_join_conv [simp]:
  "\<pi> \<bullet> p \<in> (rstep R)\<^sup>\<down> \<longleftrightarrow> p \<in> (rstep R)\<^sup>\<down>" (is "?L = ?R")
proof
  assume "?L"
  then obtain u
    where "(fst (\<pi> \<bullet> p), u) \<in> (rstep R)\<^sup>*" and "(snd (\<pi> \<bullet> p), u) \<in> (rstep R)\<^sup>*"
    by (metis joinE surjective_pairing)
  moreover then obtain v
    where [simp]: "u = \<pi> \<bullet> v" by (auto dest: perm_rsteps_perm simp: eqvt [symmetric])
  ultimately have "(fst p, v) \<in> (rstep R)\<^sup>*" and "(snd p, v) \<in> (rstep R)\<^sup>*"
    by (simp_all add: eqvt [symmetric])
  then show "?R" by (metis joinI surjective_pairing)
next
  assume "?R"
  then obtain u
    where "(fst p, u) \<in> (rstep R)\<^sup>*" and "(snd p, u) \<in> (rstep R)\<^sup>*"
    by (metis joinE surjective_pairing)
  then have "\<pi> \<bullet> (fst p, u) \<in> (rstep R)\<^sup>*" and "\<pi> \<bullet> (snd p, u) \<in> (rstep R)\<^sup>*" by auto
  then show "?L" by (metis joinI rule_pt.permute_prod_eqvt surjective_pairing)
qed

lemma permuted_rule_in_variants:
  assumes "(p \<bullet> s, p \<bullet> t) \<in> R"
  shows "(s, t) \<in> rule_pt.variants `` R"
  using assms
  by (auto simp: rule_pt.variants_def)
     (metis rule_pt.permute_minus_cancel(2) rule_pt.permute_prod.simps)

lemma in_fun_poss_eqvt:
  assumes "p \<in> fun_poss t"
  shows "p \<in> fun_poss (\<pi> \<bullet> t)"
  using assms by (induct t arbitrary: p) auto

text \<open>Lists have an infinite universe.\<close>
instance list :: (type) infinite by standard (rule infinite_UNIV_listI)

text \<open>Two terms are variants iff they are substitution instances of each other.\<close>
lemma term_variants_iff:
  fixes s t :: "('f, 'v :: infinite) term"
  shows "(\<exists>\<pi>. \<pi> \<bullet> s = t) \<longleftrightarrow> (\<exists>(\<sigma> :: ('f, 'v) subst) (\<tau> :: ('f, 'v) subst). s \<cdot> \<sigma> = t \<and> t \<cdot> \<tau> = s)"
  (is "?L = ?R")
proof
  assume "?L"
  then obtain \<pi> where *: "\<pi> \<bullet> s = t" ..
  have "s \<cdot> (Var \<circ> Rep_perm \<pi>) = t" by (simp add: *)
  moreover have "t \<cdot> (Var \<circ> Rep_perm (-\<pi>)) = s" by (simp add: * [symmetric])
  ultimately show "?R" by blast
next
  assume "?R"
  then obtain \<sigma> \<tau> :: "('f, 'v) subst"
    where variants: "s \<cdot> \<sigma> = t" "t \<cdot> \<tau> = s" by blast
  from variants_imp_bij_betw_vars [OF variants]
    have "bij_betw (the_Var \<circ> \<sigma>) (vars_term s) (vars_term t)" .
  from bij_betw_extend [OF this, of UNIV] obtain g :: "'v \<Rightarrow> 'v"
    where "finite {x. g x \<noteq> x}" and *: "\<forall>x\<in>vars_term s. g x = (the_Var \<circ> \<sigma>) x" and "bij g" by auto
  then have "g \<in> perms" by (simp add: perms_def)
  then have **: "s \<cdot> (Var \<circ> g) = Abs_perm g \<bullet> s" by (rule term_apply_subst_Var_Abs_perm)
  from * have "\<forall>x\<in>vars_term s. (Var \<circ> g) x = \<sigma> x"
    using variants_imp_is_Var [OF variants] by simp
  from term_subst_eq_conv [THEN iffD2, OF this]
    show "?L" unfolding variants and ** ..
qed

lemma rstep_pos_permute [simp]:
  "rstep_pos (\<pi> \<bullet> R) p = rstep_pos R p"
proof
  show "rstep_pos (\<pi> \<bullet> R) p \<subseteq> rstep_pos R p"
  proof (rule subrelI)
    fix s t
    assume "(s, t) \<in> rstep_pos (\<pi> \<bullet> R) p"
    then show "(s, t) \<in> rstep_pos R p"
    proof (cases)
      fix l r \<sigma>
      assume "(l, r) \<in> \<pi> \<bullet> R"
        and [simp]: "s |_ p = l \<cdot> \<sigma>" "t = (ctxt_of_pos_term p s)\<langle>r \<cdot> \<sigma>\<rangle>"
        and p: "p \<in> poss s"
      then have "(-\<pi> \<bullet> l, -\<pi> \<bullet> r) \<in> -\<pi> \<bullet> \<pi> \<bullet> R" by simp
      then have "(-\<pi> \<bullet> l, -\<pi> \<bullet> r) \<in> R" by simp
      from rstep_pos.intros [OF this p, of "sop \<pi> \<circ>\<^sub>s \<sigma>"]
        show "(s, t) \<in> rstep_pos R p" by simp
    qed
  qed
next
  show "rstep_pos R p \<subseteq> rstep_pos (\<pi> \<bullet> R) p"
  proof (rule subrelI)
    fix s t
    assume "(s, t) \<in> rstep_pos R p"
    then show "(s, t) \<in> rstep_pos (\<pi> \<bullet> R) p"
    proof (cases)
      fix l r \<sigma>
      assume "(l, r) \<in> R" and [simp]: "s |_ p = l \<cdot> \<sigma>" "t = (ctxt_of_pos_term p s)\<langle>r \<cdot> \<sigma>\<rangle>"
        and p: "p \<in> poss s"
      then have "(\<pi> \<bullet> l, \<pi> \<bullet> r) \<in> \<pi> \<bullet> R" by simp
      from rstep_pos.intros [OF this p, of "sop (-\<pi>) \<circ>\<^sub>s \<sigma>"]
        show "(s, t) \<in> rstep_pos (\<pi> \<bullet> R) p" by simp
    qed
  qed
qed

lemma rstep_pos_subset_permute_rstep_pos:
  "rstep_pos R p \<subseteq> \<pi> \<bullet> rstep_pos R p"
proof (rule subrelI)
  fix s t
  assume "(s, t) \<in> rstep_pos R p"
  then have "(s, t) \<in> rstep_pos (\<pi> \<bullet> R) p" by auto
  then show "(s, t) \<in> \<pi> \<bullet> rstep_pos R p"
  proof (cases)
    case (rule l r \<sigma>)
    then have p: "p \<in> poss (-\<pi> \<bullet> s)"
      and *: "- \<pi> \<bullet> s |_ p = -\<pi> \<bullet> l \<cdot> sop \<pi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s sop (-\<pi>)" by (auto simp: eqvt [symmetric])
    have "(l, r) \<in> \<pi> \<bullet> R" by fact
    then have "(\<pi> \<bullet> (-\<pi>) \<bullet> l, \<pi> \<bullet> (-\<pi>) \<bullet> r) \<in> \<pi> \<bullet> R" by simp+
    then have "(-\<pi> \<bullet> l, -\<pi> \<bullet> r) \<in> R" by simp
    from rstep_pos.intros [OF this p *] and p
      show ?thesis unfolding rule by (auto simp: eqvt [symmetric])
  qed
qed

lemma rstep_pos_eqvt [eqvt]:
  "\<pi> \<bullet> rstep_pos R p = rstep_pos (\<pi> \<bullet> R) p"
proof
  show "rstep_pos (\<pi> \<bullet> R) p \<subseteq> \<pi> \<bullet> rstep_pos R p"
    using rstep_pos_subset_permute_rstep_pos by simp
next
  from rstep_pos_subset_permute_rstep_pos [of R p "-\<pi>"]
    have "\<pi> \<bullet> rstep_pos R p \<subseteq> \<pi> \<bullet> -\<pi> \<bullet> rstep_pos R p" by (metis trs_pt.permute_set_subset)
  then show "\<pi> \<bullet> rstep_pos R p \<subseteq> rstep_pos (\<pi> \<bullet> R) p" by simp
qed

lemma perm_rstep_pos_conv [simp]:
  "\<pi> \<bullet> r \<in> rstep_pos R p \<longleftrightarrow> r \<in> rstep_pos R p"
  by (metis rstep_pos_eqvt rstep_pos_permute trs_pt.mem_permute_iff)

lemma is_partition_map_vars_term_permute [simp]:
  "is_partition (map (vars_term \<circ> (\<bullet>) \<pi>) xs) \<longleftrightarrow> is_partition (map vars_term xs)"
by (auto simp add: is_partition_def eqvt [symmetric])

lemma linear_term_permute [simp]:
  "linear_term (\<pi> \<bullet> t) \<longleftrightarrow> linear_term t"
by (induction t) (auto)

lemma ground_permute [simp]:
  "ground (\<pi> \<bullet> t) \<longleftrightarrow> ground t"
by (induction t) (auto)

lemma funas_term_permute [simp]:
  "funas_term (\<pi> \<bullet> t) = funas_term t"
by (induction t) (auto)

lemma in_NF_rstep_permute [simp]:
  "\<pi> \<bullet> t \<in> NF (rstep R) \<longleftrightarrow> t \<in> NF (rstep R)"
by (metis NF_instance term_variants_iff)

lemma Id_trs_eqvt [simp]: "\<pi> \<bullet> (Id :: ('f, 'v :: infinite) trs) = Id"
by (auto simp: inv_rule_mem_trs_simps [where p = \<pi>, symmetric])

lemma supteq_eqvt [simp]:
  fixes \<pi> :: "('v :: infinite) perm"
  shows "\<pi> \<bullet> {\<unrhd>} = {\<unrhd>}"
proof (intro equalityI subrelI)
  fix s t :: "('f, 'v) term" assume "(s, t) \<in> \<pi> \<bullet> {\<unrhd>}"
  then have "-\<pi> \<bullet> s \<unrhd> -\<pi> \<bullet> t" by auto
  then have "(-\<pi> \<bullet> s) \<cdot> sop \<pi> \<unrhd> (-\<pi> \<bullet> t) \<cdot> sop \<pi>" by blast
  then show "s \<unrhd> t" by simp
next
  fix s t :: "('f, 'v) term" assume "s \<unrhd> t"
  from supteq_subst [OF this, of "sop (-\<pi>)"] show "(s, t) \<in> \<pi> \<bullet> {\<unrhd>}" by simp
qed

lemma supt_eqvt [simp]:
  "\<pi> \<bullet> {\<rhd>} = {\<rhd>}"
  by (simp add: supt_supteq_set_conv eqvt)

lemma mgu_imp_mgu_var_disjoint:
  fixes v\<^sub>x v\<^sub>y :: "'v::infinite \<Rightarrow> 'v" and s t :: "('f, 'v) term"
  assumes \<mu>: "mgu s t = Some \<mu>"
    and ren: "inj v\<^sub>x" "inj v\<^sub>y" "range v\<^sub>x \<inter> range v\<^sub>y = {}"
    and disj: "V \<inter> W = {}"
    and vars_term: "vars_term s \<subseteq> V" "vars_term t \<subseteq> W"
    and finite: "finite V" "finite W"
  shows "\<exists>\<mu>'.
    (\<exists>\<pi>.
      (\<forall>x \<in> V. \<mu> x = (sop \<pi>\<^sub>1 \<circ>\<^sub>s (\<mu>' \<circ> v\<^sub>x) \<circ>\<^sub>s sop (-\<pi>)) x) \<and>
      (\<forall>x \<in> W. \<mu> x = (sop \<pi>\<^sub>2 \<circ>\<^sub>s (\<mu>' \<circ> v\<^sub>y) \<circ>\<^sub>s sop (-\<pi>)) x)) \<and>
    mgu ((\<pi>\<^sub>1 \<bullet> s) \<cdot> (Var \<circ> v\<^sub>x)) ((\<pi>\<^sub>2 \<bullet> t) \<cdot> (Var \<circ> v\<^sub>y)) = Some \<mu>'" (is "\<exists>\<mu>'. _ \<and> mgu ?sv ?tv = _")
proof -
  define h where "h x = (if x \<in> V then v\<^sub>x (Rep_perm \<pi>\<^sub>1 x) else v\<^sub>y (Rep_perm \<pi>\<^sub>2 x))" for x
  have "inj_on h (V \<union> W)"
    using disj and ren(3)
    apply (unfold inj_on_def)
    by (auto simp: h_def dest!: injD [OF \<open>inj v\<^sub>x\<close>] injD [OF \<open>inj v\<^sub>y\<close>] split: if_splits)
      (metis inv_Rep_perm_simp)+
  from inj_on_imp_bij_betw [OF this] have "bij_betw h (V \<union> W) (h ` (V \<union> W))" .
  from bij_betw_extend [OF this subset_UNIV subset_UNIV]
    obtain f where "f \<in> perms" and f: "\<forall>x \<in> V \<union> W. f x = h x"
    using finite by (auto simp: perms_def)
  define \<pi> and \<mu>' where "\<pi> = Abs_perm f" and "\<mu>' = sop (-\<pi>) \<circ>\<^sub>s \<mu>"
  have "finite (subst_domain \<mu>)"
    using mgu_subst_domain [OF \<mu>] and finite and vars_term by (auto intro: finite_subset)
  moreover have "{x. Rep_perm (- \<pi>) x \<noteq> x} = {x. Rep_perm \<pi> x \<noteq> x}"
    using \<open>f \<in> perms\<close>
    by (auto simp: \<pi>_def perms_def)
     (metis inv_Rep_perm_simp permute_atom_def)+
  moreover then have "finite (subst_domain (Var \<circ> Rep_perm (- \<pi>)))"
    using \<open>f \<in> perms\<close> by (auto simp: subst_domain_def \<pi>_def Abs_perm_inverse perms_def)
  ultimately have finite: "finite (subst_domain \<mu>')"
    by (auto simp: \<mu>'_def subst_domain_subst_compose)

  let ?s = "\<pi>\<^sub>1 \<bullet> s" and ?t = "\<pi>\<^sub>2 \<bullet> t"

  have "?sv = s \<cdot> sop \<pi>\<^sub>1 \<circ>\<^sub>s (Var \<circ> v\<^sub>x)" by simp
  also have "\<dots> = s \<cdot> sop \<pi>"
    using f and \<open>f \<in> perms\<close> and vars_term and disj unfolding term_subst_eq_conv
    by (auto simp: \<pi>_def h_def Abs_perm_inverse subst_compose)
  finally have sv: "?sv = \<pi> \<bullet> s" by simp

  have "?tv = t \<cdot> sop \<pi>\<^sub>2 \<circ>\<^sub>s (Var \<circ> v\<^sub>y)" by simp
  also have "\<dots> = t \<cdot> sop \<pi>"
    using f and \<open>f \<in> perms\<close> and vars_term and disj unfolding term_subst_eq_conv
    by (auto simp: \<pi>_def h_def Abs_perm_inverse subst_compose split: if_splits)
      (metis Un_iff disjoint_iff_not_equal set_rev_mp)
  finally have tv: "?tv = \<pi> \<bullet> t" by simp

  have eq: "s \<cdot> \<mu> = t \<cdot> \<mu>" using mgu_sound [OF \<open>mgu s t = Some \<mu>\<close>] by (auto simp: is_imgu_def)
  then have eq': "?sv \<cdot> \<mu>' = ?tv \<cdot> \<mu>'" by (simp add: sv tv \<mu>'_def)

  then obtain \<mu>'' where \<mu>'': "mgu ?sv ?tv = Some \<mu>''" using mgu_complete by (auto simp: unifiers_def)
  from mgu_sound [OF this] have eq'': "?sv \<cdot> \<mu>'' = ?tv \<cdot> \<mu>''"
    and mgu'': "is_mgu \<mu>'' {(?sv, ?tv)}" by (auto simp: is_mgu_def is_imgu_def)

  { fix \<tau> :: "('f, 'v) subst" assume *: "?sv \<cdot> \<tau> = ?tv \<cdot> \<tau>"
    then have "s \<cdot> sop \<pi> \<circ>\<^sub>s \<tau> = t \<cdot> sop \<pi> \<circ>\<^sub>s \<tau>" by (simp add: sv tv)
    with mgu_sound [OF \<mu>, THEN is_imgu_imp_is_mgu] obtain \<delta> where "sop \<pi> \<circ>\<^sub>s \<tau> = \<mu> \<circ>\<^sub>s \<delta>"
      unfolding is_mgu_def unifiers_def by force
    then have "sop (-\<pi>) \<circ>\<^sub>s sop \<pi> \<circ>\<^sub>s \<tau> = sop (-\<pi>) \<circ>\<^sub>s \<mu> \<circ>\<^sub>s \<delta>" by (auto simp: subst_compose_assoc)
    then have "\<tau> = \<mu>' \<circ>\<^sub>s \<delta>"
      by (auto simp: \<mu>'_def subst_compose_def)
      (metis atom_pt.permute_minus_cancel(1) permute_atom_def)
    then have "\<exists>\<gamma>. \<tau> = \<mu>' \<circ>\<^sub>s \<gamma>" by blast }
  then have "is_mgu \<mu>' {(?sv, ?tv)}" using eq' by (auto simp: is_mgu_def unifiers_def)
  with eq'' obtain \<gamma> where "\<mu>'' = \<mu>' \<circ>\<^sub>s \<gamma>" by (auto simp: is_mgu_def unifiers_def)
  moreover obtain \<delta> where "\<mu>' = \<mu>'' \<circ>\<^sub>s \<delta>" using eq' and mgu'' by (auto simp: is_mgu_def unifiers_def)
  ultimately obtain \<pi>' where *: "\<mu>'' = \<pi>' \<bullet> \<mu>'"
    using subst_variants_imp_perm [OF _ _ finite mgu_finite_subst_domain [OF \<mu>''], of \<gamma> \<delta>] by metis
  have "\<forall>x \<in> V. \<mu> x = (sop \<pi>\<^sub>1 \<circ>\<^sub>s (\<mu>'' \<circ> v\<^sub>x) \<circ>\<^sub>s sop (-\<pi>')) x"
    using f
    by (auto simp: * \<mu>'_def subst_compose_def permute_subst_def \<pi>_def h_def split: if_splits)
     (metis Abs_perm_inverse Rep_perm_uminus Un_iff \<open>f \<in> perms\<close> bij_Rep_perm bij_is_inj inv_f_eq)
  moreover have "\<forall>x \<in> W. \<mu> x = (sop \<pi>\<^sub>2 \<circ>\<^sub>s (\<mu>'' \<circ> v\<^sub>y) \<circ>\<^sub>s sop (-\<pi>')) x"
    using f and disj
    by (auto simp: * \<mu>'_def subst_compose_def permute_subst_def \<pi>_def h_def split: if_splits)
     (metis Abs_perm_inverse Rep_perm_uminus Un_iff \<open>f \<in> perms\<close> bij_Rep_perm bij_is_inj disjoint_iff_not_equal inv_f_eq)
  ultimately show ?thesis using \<mu>'' by blast
qed

end
