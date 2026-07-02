(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015-2017)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Level_Confluence
  imports
    Check_Infeasibility
    CTRS.Level_Confluence
    Show.Shows_Literal
begin

hide_const (open) Ramsey.choice
no_notation Matrix.scalar_prod  (infix "\<bullet>" 70)
no_notation Inner_Product.real_inner_class.inner (infix "\<bullet>" 70)

text \<open>
  Operations required to support a check function for almost-orthogonality (modulo infeasibility)
\<close>
locale almost_orthogonal_ops =
  fixes xvar yvar :: "'v::{showl, infinite} \<Rightarrow> 'v"
    and check_infeasible ::
      "('f::showl, 'v) crules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
begin

definition
  check_overlap :: "('f, 'v) crules \<Rightarrow> ('f, 'v) crule \<Rightarrow> ('f, 'v) crule \<Rightarrow> pos \<Rightarrow> showsl check"
where
  "check_overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p =
    (case mgu_var_disjoint_generic xvar yvar (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) of
      None \<Rightarrow> succeed
    | Some (\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Rightarrow>
      choice [
        check (p = [] \<and> crhs \<rho>\<^sub>1 \<cdot> \<sigma>\<^sub>1 = crhs \<rho>\<^sub>2 \<cdot> \<sigma>\<^sub>2) (showsl_lit (STR ''is not a trivial root-overlap'')),
        check (p = [] \<and> match_crule \<rho>\<^sub>1 \<rho>\<^sub>2 \<noteq> None \<and> match_crule \<rho>\<^sub>2 \<rho>\<^sub>1 \<noteq> None)
          (showsl_lit (STR ''is not a root-overlap of variants of the same rule'')),
        check_infeasible R (subst_list \<sigma>\<^sub>1 (snd \<rho>\<^sub>1)) (subst_list \<sigma>\<^sub>2 (snd \<rho>\<^sub>2))
          <+? (\<lambda>e. showsl_lit (STR ''could not be shown to be infeasible\<newline>'') \<circ> e)]
      <+? showsl_sep id showsl_nl)
    <+? (\<lambda>e. showsl_lit (STR ''the '') \<circ> showsl_coverlap \<rho>\<^sub>1 \<rho>\<^sub>2 p \<circ> showsl_nl \<circ> e)"

definition
  "check_ao R = do {
    check_left_linear_trs (map fst R);
    check_allm (\<lambda>\<rho>\<^sub>1. let l\<^sub>1 = clhs \<rho>\<^sub>1 in check_allm (\<lambda>\<rho>\<^sub>2. check_allm (\<lambda>p.
      check_overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p) (fun_poss_list l\<^sub>1)) R) R
  }"

end

lemmas [code] =
  almost_orthogonal_ops.check_overlap_def almost_orthogonal_ops.check_ao_def

locale almost_orthogonal_spec = almost_orthogonal_ops +
  assumes infeasible: "isOK (check_infeasible R cs\<^sub>1 cs\<^sub>2) \<Longrightarrow>
    (\<forall>m n. comm ((cstep_n (set R) m)\<^sup>*) ((cstep_n (set R) n)\<^sup>*) \<longrightarrow>
    \<not> (\<exists>\<sigma>. conds_n_sat (set R) m cs\<^sub>1 \<sigma> \<and> conds_n_sat (set R) n cs\<^sub>2 \<sigma>))"
    and ren: "inj xvar" "inj yvar" "range xvar \<inter> range yvar = {}"
begin

lemma isOK_check_ao [simp]:
  assumes "isOK (check_ao R)"
  shows "almost_orthogonal (set R)"
proof (unfold almost_orthogonal_def, intro conjI allI impI)
  show "left_linear_trs (Ru (set R))"
    using assms by (simp add: check_ao_def Ru_def)
next
  fix \<rho>\<^sub>1' \<rho>\<^sub>2' p
  assume "overlap (set R) \<rho>\<^sub>1' \<rho>\<^sub>2' p"
  then obtain \<pi>\<^sub>1 and \<pi>\<^sub>2 and \<mu>
    where rules': "\<pi>\<^sub>1 \<bullet> \<rho>\<^sub>1' \<in> set R" "\<pi>\<^sub>2 \<bullet> \<rho>\<^sub>2' \<in> set R"
    and "vars_crule \<rho>\<^sub>1' \<inter> vars_crule \<rho>\<^sub>2' = {}"
    and p': "p \<in> fun_poss (clhs \<rho>\<^sub>1')"
    and mgu': "mgu (clhs \<rho>\<^sub>1' |_ p) (clhs \<rho>\<^sub>2') = Some \<mu>"
    by (auto simp: overlap_def)
  define \<rho>\<^sub>1 \<rho>\<^sub>2 where "\<rho>\<^sub>1 \<equiv> \<pi>\<^sub>1 \<bullet> \<rho>\<^sub>1'" and "\<rho>\<^sub>2 \<equiv> \<pi>\<^sub>2 \<bullet> \<rho>\<^sub>2'"
  have p: "p \<in> fun_poss (clhs \<rho>\<^sub>1)"
    and "\<rho>\<^sub>1 \<in> set R" and "\<rho>\<^sub>2 \<in> set R"
    using p' and rules' apply (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def eqvt)
    by (metis crule_pt.fst_eqvt fun_poss_perm_simp rule_pt.fst_eqvt)
  with assms have *: "isOK (check_overlap R \<rho>\<^sub>1 \<rho>\<^sub>2 p)" by (auto simp: check_ao_def)

  let ?thesis = "let \<mu> = the (mgu (clhs \<rho>\<^sub>1' |_ p) (clhs \<rho>\<^sub>2')) in
     p = [] \<and> crhs \<rho>\<^sub>1' \<cdot> \<mu> = crhs \<rho>\<^sub>2' \<cdot> \<mu> \<or>
     p = [] \<and> (\<exists>p. p \<bullet> \<rho>\<^sub>1' = \<rho>\<^sub>2') \<or>
     (\<forall>m n. comm ((cstep_n (set R) m)\<^sup>*) ((cstep_n (set R) n)\<^sup>*) \<longrightarrow>
       \<not> (\<exists>\<sigma>. conds_n_sat (set R) m (subst_list \<mu> (snd \<rho>\<^sub>1')) \<sigma> \<and>
              conds_n_sat (set R) n (subst_list \<mu> (snd \<rho>\<^sub>2')) \<sigma>))"

  have "(clhs \<rho>\<^sub>1' |_ p) \<cdot> \<mu> = clhs \<rho>\<^sub>2' \<cdot> \<mu>" using mgu' [THEN mgu_sound] by (auto simp: is_imgu_def)
  then have "(clhs \<rho>\<^sub>1' |_ p) \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1) \<circ> Rep_perm \<pi>\<^sub>1) =
    clhs \<rho>\<^sub>2' \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2) \<circ> Rep_perm \<pi>\<^sub>2)"
    by (simp add: o_assoc [symmetric] Rep_perm_add [symmetric] Rep_perm_0)
  then have "clhs \<rho>\<^sub>1 |_ p \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1)) = clhs \<rho>\<^sub>2 \<cdot> (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2))"
    using p [THEN fun_poss_imp_poss]
    by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def permute_term_subst_apply_term [symmetric] eqvt)
  from mgu_var_disjoint_generic_complete [OF ren this] obtain \<mu>\<^sub>1 \<mu>\<^sub>2 \<delta>
    where "mgu_var_disjoint_generic xvar yvar (clhs \<rho>\<^sub>1 |_ p) (clhs \<rho>\<^sub>2) = Some (\<mu>\<^sub>1, \<mu>\<^sub>2)"
    and **: "\<mu> \<circ> Rep_perm (- \<pi>\<^sub>1) = \<mu>\<^sub>1 \<circ>\<^sub>s \<delta>" "\<mu> \<circ> Rep_perm (- \<pi>\<^sub>2) = \<mu>\<^sub>2 \<circ>\<^sub>s \<delta>" by blast
  with * have "p = [] \<and> crhs \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1 = crhs \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2 \<or>
    p = [] \<and> match_crule \<rho>\<^sub>1 \<rho>\<^sub>2 \<noteq> None \<and> match_crule \<rho>\<^sub>2 \<rho>\<^sub>1 \<noteq> None \<or>
    isOK (check_infeasible R (subst_list \<mu>\<^sub>1 (snd \<rho>\<^sub>1)) (subst_list \<mu>\<^sub>2 (snd \<rho>\<^sub>2)))"
    by (auto simp: check_overlap_def)
  moreover
  { assume [simp]: "p = []" and "crhs \<rho>\<^sub>1 \<cdot> \<mu>\<^sub>1 = crhs \<rho>\<^sub>2 \<cdot> \<mu>\<^sub>2"
    then have "crhs \<rho>\<^sub>1 \<cdot> (\<mu>\<^sub>1 \<circ>\<^sub>s \<delta>) = crhs \<rho>\<^sub>2 \<cdot> (\<mu>\<^sub>2 \<circ>\<^sub>s \<delta>)" by simp
    then have "crhs \<rho>\<^sub>1' \<cdot> \<mu> = crhs \<rho>\<^sub>2' \<cdot> \<mu>"
      unfolding ** [symmetric]
      by (simp add: \<rho>\<^sub>1_def \<rho>\<^sub>2_def permute_term_subst_apply_term [symmetric] eqvt)
    with mgu' have ?thesis by (auto) }
  moreover
  { assume "p = []" and "match_crule \<rho>\<^sub>1 \<rho>\<^sub>2 \<noteq> None" and "match_crule \<rho>\<^sub>2 \<rho>\<^sub>1 \<noteq> None"
    with match_crule_imp_variants [of \<rho>\<^sub>2 \<rho>\<^sub>1] obtain \<pi> where "\<pi> \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2" by blast
    then have "(-\<pi>\<^sub>2 + \<pi> + \<pi>\<^sub>1) \<bullet> \<rho>\<^sub>1' = \<rho>\<^sub>2'" by (simp add: \<rho>\<^sub>1_def \<rho>\<^sub>2_def)
    with \<open>p = []\<close> have ?thesis unfolding Let_def by blast }
  moreover
  { assume *: "isOK (check_infeasible R (subst_list \<mu>\<^sub>1 (snd \<rho>\<^sub>1)) (subst_list \<mu>\<^sub>2 (snd \<rho>\<^sub>2)))"
    { fix m n assume comm: "comm ((cstep_n (set R) m)\<^sup>*) ((cstep_n (set R) n)\<^sup>*)"
      have "\<not> (\<exists>\<sigma>. conds_n_sat (set R) m (subst_list \<mu> (snd \<rho>\<^sub>1')) \<sigma> \<and>
        conds_n_sat (set R) n (subst_list \<mu> (snd \<rho>\<^sub>2')) \<sigma>)"
      proof (intro notI, elim exE conjE)
        fix \<sigma>
        assume "conds_n_sat (set R) m (subst_list \<mu> (snd \<rho>\<^sub>1')) \<sigma>"
          and "conds_n_sat (set R) n (subst_list \<mu> (snd \<rho>\<^sub>2')) \<sigma>"
        then have "conds_n_sat (set R) m (subst_list (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>1)) (snd \<rho>\<^sub>1)) \<sigma>"
          and "conds_n_sat (set R) n (subst_list (\<mu> \<circ> Rep_perm (-\<pi>\<^sub>2)) (snd \<rho>\<^sub>2)) \<sigma>"
          by (auto simp: \<rho>\<^sub>1_def \<rho>\<^sub>2_def subst_list_subst_compose subst_list_Rep_perm map_idI eqvt [symmetric])
        then have "\<exists>\<sigma>. conds_n_sat (set R) m (subst_list \<mu>\<^sub>1 (snd \<rho>\<^sub>1)) \<sigma> \<and>
          conds_n_sat (set R) n (subst_list \<mu>\<^sub>2 (snd \<rho>\<^sub>2)) \<sigma>"
          by (auto simp add: ** subst_list_subst_compose conds_n_sat_subst_list)
        with infeasible [OF *, THEN spec, THEN spec, THEN mp, OF comm] show False by blast
      qed }
    then have ?thesis using mgu' by auto }
  ultimately show ?thesis by blast
qed

end

global_interpretation wo_infeasibility: almost_orthogonal_spec x_var y_var
  "\<lambda>R cs\<^sub>1 cs\<^sub>2. error (showsl_lit (STR ''infeasibility check not supported''))"
  defines
    check_almost_orthogonal = wo_infeasibility.check_ao
by (unfold_locales; auto simp: inj_on_def)

definition check_level_confluence :: "('f::{compare_order,showl}, string) crules \<Rightarrow> showsl check"
where
  "check_level_confluence R = do {
    check_varcond_no_Var_lhs (map fst R);
    check_type3 R;
    check_extended_properly_oriented R;
    check_right_stable R;
    check_almost_orthogonal R
  }"

lemma check_level_confluence [simp]:
  assumes "isOK (check_level_confluence R)"
  shows "level_confluent (set R)"
using assms by (force intro: level_confluence simp: check_level_confluence_def)

(* NOTE: this mod_infeasibility without dash is not used, so could be removed safely *)
(*
global_interpretation mod_infeasibility: almost_orthogonal_spec x_var y_var
  "check_infeasible a i I J css" for a i I J css
  defines
    check_almost_orthogonal_modulo_infeasibility = mod_infeasibility.check_ao
by (unfold_locales; force dest: infeasible_sufficient check_infeasible simp: inj_on_def)

definition
  check_level_confluence_modulo_infeasibility
where
  "check_level_confluence_modulo_infeasibility a i I J css R = do {
    check_varcond_no_Var_lhs (map fst R);
    check_type3 R;
    check_extended_properly_oriented R;
    check_right_stable R;
    check_almost_orthogonal_modulo_infeasibility a i I J css R
  }"

lemma check_level_confluence_modulo_infeasibility [simp]:
  assumes "isOK (check_level_confluence_modulo_infeasibility a i I J css R)"
  shows "level_confluent (set R)"
using assms
by (intro level_confluence)
   (auto simp: check_level_confluence_modulo_infeasibility_def)
*)

datatype ('f, 'v, 'rp, 'l) ao_infeasibility_proof =
  AO_Infeasibility_Proof "('f, 'v, 'rp, 'l) infeasibility_proof"
| AO_Lhss_Equal "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term" "('f, 'v, 'rp, 'l) nonjoinability_proof"

fun check_ao_infeasible'
where
  "check_ao_infeasible' a i I J R cs\<^sub>1 cs\<^sub>2 (AO_Infeasibility_Proof p) = check_infeasible' a i I J R (cs\<^sub>1 @ cs\<^sub>2) p"
| "check_ao_infeasible' a i I J R cs\<^sub>1 cs\<^sub>2 (AO_Lhss_Equal s t u p) = do {
    check ((s, t) \<in> set cs\<^sub>1)
      (showsl_eq (s, t) \<circ> showsl_lit (STR '' is not an equation in '') \<circ> showsl_conditions cs\<^sub>1);
    check ((s, u) \<in> set cs\<^sub>2)
      (showsl_eq (s, u) \<circ> showsl_lit (STR '' is not an equation in '') \<circ> showsl_conditions cs\<^sub>2);
    check_nonjoinable a i I J (map fst R) t u p
  }"

lemma check_ao_infeasible':
  assumes I: "tp_spec I" and J: "dpp_spec J" and  "isOK (check_ao_infeasible' a i I J R cs\<^sub>1 cs\<^sub>2 p)"
  shows "(\<forall>m n. comm ((cstep_n (set R) m)\<^sup>*) ((cstep_n (set R) n)\<^sup>*) \<longrightarrow>
    \<not> (\<exists>\<sigma>. conds_n_sat (set R) m cs\<^sub>1 \<sigma> \<and> conds_n_sat (set R) n cs\<^sub>2 \<sigma>))"
proof (intro allI impI)
  let ?R = "set R"
  fix m n assume comm: "comm ((cstep_n ?R m)\<^sup>*) ((cstep_n ?R n)\<^sup>*)"
  show "\<not> (\<exists>\<sigma>. conds_n_sat ?R m cs\<^sub>1 \<sigma> \<and> conds_n_sat ?R n cs\<^sub>2 \<sigma>)"
  proof (cases p)
    case (AO_Infeasibility_Proof q)
    then show ?thesis
      using assms and comm by (auto dest: check_infeasible' [OF I J, THEN infeasible_sufficient])
  next
    case (AO_Lhss_Equal s t u q)
    with assms have *: "(s, t) \<in> set cs\<^sub>1" "(s, u) \<in> set cs\<^sub>2"
      and "isOK (check_nonjoinable a i I J (map fst R) t u q)" by auto
    then have **: "\<not> (\<exists>\<sigma>. (t \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (rstep (Ru ?R))\<^sup>\<down>)"
      by (auto simp: Ru_def dest: check_nonjoinable[OF I J])
    { fix \<sigma> assume "conds_n_sat ?R m cs\<^sub>1 \<sigma>" and "conds_n_sat ?R n cs\<^sub>2 \<sigma>"
      with * and comm obtain v where "(t \<cdot> \<sigma>, v) \<in> (cstep_n ?R n)\<^sup>*"
        and "(u \<cdot> \<sigma>, v) \<in> (cstep_n ?R m)\<^sup>*" by (blast dest: conds_n_satD elim: commE)
      with ** have False
        using rtrancl_mono [OF cstep_imp_Ru_step] by (blast dest: csteps_n_imp_csteps) }
    then show ?thesis by auto
  qed
qed

definition
  check_ao_infeasible
where
  "check_ao_infeasible a i I J css R cs\<^sub>1' cs\<^sub>2' = check_exm (\<lambda>(cs\<^sub>1, cs\<^sub>2, p). do {
    let cs' = cs\<^sub>1' @ cs\<^sub>2';
    let cs = cs\<^sub>1 @ cs\<^sub>2;
    check (length cs\<^sub>1 = length cs\<^sub>1' \<and> length cs\<^sub>2 = length cs\<^sub>2') (showsl_lit (STR ''lengths differ''));
    check (match_rules cs cs' \<noteq> None \<and> match_rules cs' cs \<noteq> None) id;
    check_ao_infeasible' a i I J R cs\<^sub>1 cs\<^sub>2 p
  }) css (showsl_sep id showsl_nl)"

lemma check_ao_infeasible:
  fixes R :: "(_, string) crules"
  assumes I: "tp_spec I" and J: "dpp_spec J" and "isOK (check_ao_infeasible a i I J css R cs\<^sub>1 cs\<^sub>2)"
  shows "(\<forall>m n. comm ((cstep_n (set R) m)\<^sup>*) ((cstep_n (set R) n)\<^sup>*) \<longrightarrow>
    \<not> (\<exists>\<sigma>. conds_n_sat (set R) m cs\<^sub>1 \<sigma> \<and> conds_n_sat (set R) n cs\<^sub>2 \<sigma>))"
    (is "?P cs\<^sub>1 cs\<^sub>2")
proof -
  let ?cs = "cs\<^sub>1 @ cs\<^sub>2"
  obtain \<pi> :: "string perm" and cs\<^sub>1' and cs\<^sub>2' and p where "(cs\<^sub>1', cs\<^sub>2', p) \<in> set css"
    and cs': "cs\<^sub>1' = \<pi> \<bullet> cs\<^sub>1" "cs\<^sub>2' = \<pi> \<bullet> cs\<^sub>2" and ok: "isOK (check_ao_infeasible' a i I J R cs\<^sub>1' cs\<^sub>2' p)"
    using assms and match_rules_imp_variants [of _ ?cs]
    by (auto simp: check_ao_infeasible_def Ru_def)
       (metis (no_types, opaque_lifting) List.append_eq_append_conv length_map)
  moreover then have "?P cs\<^sub>1' cs\<^sub>2'" by (auto dest: check_ao_infeasible'[OF I J])
  ultimately show ?thesis by (metis conds_n_sat_perm_shift rules_pt.permute_minus_cancel(2))
qed

definition
  check_level_confluence_modulo_infeasibility'
where
  "check_level_confluence_modulo_infeasibility' a i I J css R = do {
    check_varcond_no_Var_lhs (map fst R);
    check_type3 R;
    check_extended_properly_oriented R;
    check_right_stable R;
    almost_orthogonal_ops.check_ao x_var y_var (check_ao_infeasible a i I J css) R
  }"

lemma check_level_confluence_modulo_infeasibility' [simp]:
  assumes I: "tp_spec I" and J: "dpp_spec J" and  "isOK (check_level_confluence_modulo_infeasibility' a i I J css R)"
  shows "level_confluent (set R)"
proof -
  interpret mod_infeasibility': almost_orthogonal_spec x_var y_var
    "check_ao_infeasible a i I J css" for a i css
  by (unfold_locales; force dest: check_ao_infeasible[OF I J] simp: inj_on_def)
  show ?thesis using assms
    by (intro level_confluence) (auto simp: check_level_confluence_modulo_infeasibility'_def)
qed

end
