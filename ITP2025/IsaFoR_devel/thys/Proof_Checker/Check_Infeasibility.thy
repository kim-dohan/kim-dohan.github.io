(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016, 2018)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Checking Infeasibility of Conditional Critical Pairs\<close>

theory Check_Infeasibility
  imports
    CTRS.Ifrit_Impl
    CTRS.Left_Inline_Conditions_Impl
    Check_Nonreachability
    CTRS.Conditional_Critical_Pairs
    CTRS.Conditional_Rewriting_Impl
    CTRS.Unraveling_Impl
begin

datatype ('f, 'v) inf_transformation =
  Ifrit_Rules_Inf
    "('f, 'v) crule list"
| Left_Inline_Conditions_Inf "('f, 'v) crules"
    "(('f, 'v) crule \<times> ('f, 'v) rules) list"
| Right_Inline_Conditions_Inf "('f, 'v) crules"
    "(('f, 'v) crule \<times> ('f, 'v) rules) list"

primrec check_inf_transform
  where
    "check_inf_transform R (Ifrit_Rules_Inf R') =
      (do {
       check (check_Ifrit_rules_iff R R') (showsl_lit (STR ''Given rules are not sound wrt Ifrit.''));
       return R'
      })"
  | "check_inf_transform R (Left_Inline_Conditions_Inf R' rcs) =
      (do {
       check_left_inline_conds R R' rcs;
       return R'
      })"
  | "check_inf_transform R (Right_Inline_Conditions_Inf R' rcs) =
      (do {
       check_inline_conds R R' rcs;
       return R'
      })"

hide_const AC_Rewriting_Base.cstep

lemma check_inf_transform:
  fixes R :: "('f::{compare_order, showl}, 'v::{compare_order, showl}) crule list"
  assumes "check_inf_transform R t = Inr S"
  shows "(cstep (set R))\<^sup>* \<subseteq> (cstep (set S))\<^sup>*"
  using assms
proof (induction t arbitrary: R S)
  case (Ifrit_Rules_Inf R')
  then have "cstep (set R) \<subseteq> cstep (set S)"
    using check_Ifrit_rules_iff by auto
  then show ?case
    by (simp add: rtrancl_mono)
next
  case (Left_Inline_Conditions_Inf R' rcs)
  moreover have "S = R'"
    using Left_Inline_Conditions_Inf by simp
  ultimately show ?case
    using check_left_inline_conds[of R R' rcs] by auto
next
  case (Right_Inline_Conditions_Inf R' rcs)
  then show ?case by auto
qed

datatype ('f, 'v, 'rp, 'l) infeasibility_proof =
  Infeasible_Compound_Conditions "('f, 'l) lab" "('f, 'v, 'rp, 'l) nonreachability_proof"
| Infeasible_Equation "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term" "('f, 'v, 'rp, 'l) nonreachability_proof"
| Infeasible_Subset "(('f, 'l) lab, 'v) rules" "('f, 'v, 'rp, 'l) infeasibility_proof"
| Infeasible_Rhss_Equal "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term"
  "('f, 'v, 'rp, 'l) nonjoinability_proof"
| Infeasible_Trans "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term" "('f, 'v, 'rp, 'l) nonreachability_proof"
| Infeasible_Transform "(('f, 'l) lab, 'v) inf_transformation" "('f, 'v, 'rp, 'l) infeasibility_proof"
| Infeasible_Split_If "(('f, 'l) lab, 'v) split_if" "('f, 'v, 'rp, 'l) nonreachability_proof"
| Infeasible_Goal_Lifting "('f, 'l) lab" "('f, 'l) lab" "('f, 'v, 'rp, 'l) infeasibility_proof"

abbreviation "err_not_cond e \<equiv>
  showsl_lit (STR ''equation '') \<circ> showsl_eq e \<circ> showsl_lit (STR '' is not in list of conditions\<newline>'')"

(*TODO: move*)
definition "trancl_of_list xs =
  concat (map (\<lambda>x. map (\<lambda>y. (x, y)) (trancl_list_impl xs [x])) (map fst xs))"

lemma set_trancl_of_list [simp]:
  "set (trancl_of_list R) = (set R)\<^sup>+"
proof (intro equalityI subrelI)
  fix x y assume "(x, y) \<in> (set R)\<^sup>+"
  then show "(x, y) \<in> set (trancl_of_list R)"
    by (induct) (auto dest: trancl_into_trancl simp: trancl_list_impl trancl_of_list_def, force)
qed (auto simp: trancl_list_impl trancl_of_list_def)

lemma conds_n_sat_trancl_of_list:
  assumes "conds_n_sat R n cs \<sigma>"
  shows "conds_n_sat R n (trancl_of_list cs) \<sigma>"
  using assms by (fastforce simp: conds_n_sat_iff elim: trancl.induct)

fun check_infeasible'
where
  "check_infeasible' a i I J R cs (Infeasible_Compound_Conditions f p) =
    check_nonreachable a i I J (map fst R) (Fun f (map fst cs)) (Fun f (map snd cs)) p"
| "check_infeasible' a i I J R cs (Infeasible_Equation s t p) = do {
    check ((s, t) \<in> set cs) (err_not_cond (s, t));
    check_nonreachable a i I J (map fst R) s t p
  }"
| "check_infeasible' a i I J R cs (Infeasible_Subset cs' p) = do {
    check_subseteq cs' cs <+? err_not_cond;
    check_infeasible' a i I J R cs' p
  }"
| "check_infeasible' a i I J R cs (Infeasible_Rhss_Equal s t u p) = do {
    check ((s, u) \<in> set cs) (err_not_cond (s, u));
    check ((t, u) \<in> set cs) (err_not_cond (t, u));
    check_nonjoinable a i I J (map fst R) s t p
  }"
| "check_infeasible' a i I J R cs (Infeasible_Trans s t u p) = do {
    check ((s, t) \<in> set cs) (err_not_cond (s, t));
    check ((t, u) \<in> set cs) (err_not_cond (t, u));
    check_nonreachable a i I J (map fst R) s u p
  }"
| "check_infeasible' a i I J R cs (Infeasible_Transform t p) = do {
    R' \<leftarrow> check_inf_transform R t;
    check_infeasible' a i I J R' cs p
  }"
| "check_infeasible' a i I J R cs (Infeasible_Split_If s p) =
   (case s of (T, F, U) \<Rightarrow> do {
      check (ground T) (showsl_lit (STR ''the term '') \<circ> showsl T \<circ> showsl_lit (STR '' is not ground''));
      check (ground F) (showsl_lit (STR ''the term '') \<circ> showsl F \<circ> showsl_lit (STR '' is not ground''));
      check ((T, F) \<in> set cs)  (showsl_lit (STR ''the equation '') \<circ> showsl_eq (T, F) \<circ> showsl_lit (STR '' is not contained in the infeasibility query''));
      check_nonreachable a i I J (split_if s R cs) T F p })"
| "check_infeasible' a i I J R cs (Infeasible_Goal_Lifting T F p) = do {
    check_infeasible' a i I J (((Fun T [], Fun F []), cs) # R) [(Fun T [], Fun F [])] p
  }"

definition
  check_infeasible ::
    "bool \<Rightarrow> showsl \<Rightarrow>
     ('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
     ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
     ((('f, label_type) lab, string) rules \<times> ('f, string, 'rp, nat list) infeasibility_proof) list \<Rightarrow>
     (('f, label_type) lab, string) crules \<Rightarrow> (('f, label_type) lab, string) rules \<Rightarrow>
     (('f, label_type) lab, string) rules \<Rightarrow> showsl check"
where
  "check_infeasible a i I J css R cs\<^sub>1 cs\<^sub>2 = check_exm (\<lambda>(cs, p). do {
    let cs' = cs\<^sub>1 @ cs\<^sub>2;
    check (match_rules cs cs' \<noteq> None \<and> match_rules cs' cs \<noteq> None) id;
    check_infeasible' a i I J R (trancl_of_list cs) p
  }) css (showsl_sep id showsl_nl)"

no_notation Matrix.scalar_prod  (infix "\<bullet>" 70)
no_notation Inner_Product.real_inner_class.inner (infix "\<bullet>" 70)

lemma perm_term_of_crule_eq_conv:
  "\<pi> \<bullet> term_of_crule \<rho>\<^sub>1 = term_of_crule \<rho>\<^sub>2 \<longleftrightarrow> \<pi> \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2"
by (cases \<rho>\<^sub>1 rule: crule_cases; cases \<rho>\<^sub>2 rule: crule_cases; auto simp: eqvt rules_enc_aux)

lemma match_crule_imp_variants:
  fixes \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v :: infinite) crule"
  assumes "match_crule \<rho>\<^sub>2 \<rho>\<^sub>1 = Some \<sigma>\<^sub>1" and "match_crule \<rho>\<^sub>1 \<rho>\<^sub>2 = Some \<sigma>\<^sub>2"
  shows "\<exists>\<pi>. \<pi> \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2"
proof -
  have "term_of_crule \<rho>\<^sub>2 \<cdot> \<sigma>\<^sub>2 = term_of_crule \<rho>\<^sub>1"
    and "term_of_crule \<rho>\<^sub>1 \<cdot> \<sigma>\<^sub>1 = term_of_crule \<rho>\<^sub>2"
    using assms by (auto simp: match_crule_alt_def dest: match_sound)
  then obtain \<pi> where "\<pi> \<bullet> \<rho>\<^sub>2 = \<rho>\<^sub>1"
    using term_variants_iff [of "term_of_crule \<rho>\<^sub>2" "term_of_crule \<rho>\<^sub>1"]
    unfolding perm_term_of_crule_eq_conv by auto
  then have "-\<pi> \<bullet> \<rho>\<^sub>1 = \<rho>\<^sub>2" by auto
  then show ?thesis ..
qed

lemma check_infeasible':
  assumes I: "tp_spec I" and J: "dpp_spec J" and "isOK (check_infeasible' a i I J R cs p)"
  shows "\<not> (\<exists>\<sigma> n. conds_n_sat (set R) n cs \<sigma>)"
using assms
proof (induct p arbitrary: cs R)
  case ok: (Infeasible_Compound_Conditions f p)
  let ?s = "Fun f (map fst cs)"
  let ?t = "Fun f (map snd cs)"
  have "\<not> (\<exists>\<sigma>. (?s \<cdot> \<sigma>, ?t \<cdot> \<sigma>) \<in> (rstep (Ru (set R)))\<^sup>*)"
    using ok by (auto simp: Ru_def dest: check_nonreachable[OF I J])
  moreover
  { fix \<sigma> and n assume "conds_n_sat (set R) n cs \<sigma>"
    then have "\<forall>(s, t) \<in> set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (Ru (set R)))\<^sup>*"
      using rtrancl_mono [OF cstep_imp_Ru_step, of "set R"]
      by (auto simp: conds_n_sat_iff split: prod.splits dest!: csteps_n_imp_csteps)
    then have "(?s \<cdot> \<sigma>, ?t \<cdot> \<sigma>) \<in> (rstep (Ru (set R)))\<^sup>*"
      by (unfold Term.eval_term.simps, intro args_steps_imp_steps)
         (auto intro: args_steps_imp_steps) }
   ultimately show ?case by auto
next
  case (Infeasible_Equation s t p)
  then have "(s, t) \<in> set cs" and "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (Ru (set R)))\<^sup>*)"
    by (auto simp: Ru_def dest: check_nonreachable[OF I J])
  then show ?case
    using csteps_n_imp_csteps [of _ _ "set R"]
      and cstep_imp_Ru_step [THEN rtrancl_mono, of "set R"] by (auto simp: conds_n_sat_iff) blast
next
  case *: (Infeasible_Subset cs' p)
  then have "isOK (check_subseteq cs' cs)  \<and> isOK (check_infeasible' a i I J R cs' p)" by auto
  then have "set cs' \<subseteq> set cs \<and> (\<nexists>\<sigma> n. conds_n_sat (set R) n cs' \<sigma>)"
    using * I J by force
  then show ?case apply (auto simp: conds_n_sat_iff) by blast
next
  case (Infeasible_Rhss_Equal s t u p)
  then have "(s, u) \<in> set cs" and "(t, u) \<in> set cs"
    and "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep (Ru (set R)))\<^sup>\<down>)" by (auto simp: Ru_def dest: check_nonjoinable[OF I J])
  then show ?case
    using csteps_n_imp_csteps [of _ _ "set R"] and cstep_imp_Ru_step [THEN rtrancl_mono, of "set R"]
    by (blast dest: conds_n_satD)
next
  case (Infeasible_Trans s t u p)
  then have "(s, t) \<in> set cs" and "(t, u) \<in> set cs"
    and "\<not> (\<exists>\<sigma>. (s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (rstep (Ru (set R)))\<^sup>*)"
    by (auto simp: Ru_def dest: check_nonreachable[OF I J])
  then show ?case
    using csteps_n_imp_csteps [of _ _ "set R"]
      and cstep_imp_Ru_step [THEN rtrancl_mono, of "set R"]
    by (auto simp: conds_n_sat_iff subset_iff)
      (metis (no_types, lifting) Pair_inject case_prodE rtrancl_trans)
next
  case (Infeasible_Transform t p)
  then obtain S where S: "check_inf_transform R t = Inr S"
    by auto
  then have subs: "(cstep (set R))\<^sup>* \<subseteq> (cstep (set S))\<^sup>*"
    using check_inf_transform[of R t S] by blast
  have ok: "isOK (check_infeasible' a i I J S cs p)"
    using Infeasible_Transform S by auto
  then have "\<nexists>\<sigma> n. (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n (set S) n)\<^sup>*)"
    using Infeasible_Transform conds_n_sat_iff by fast
  have "\<nexists>\<sigma> n. (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n (set R) n)\<^sup>*)"
  proof (rule ccontr)
    assume "\<not> (\<nexists>\<sigma> n. \<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n (set R) n)\<^sup>*)"
    then obtain n \<sigma> where cstep_R: "(\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n (set R) n)\<^sup>*)"
      by blast
    then have "(\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep (set R))\<^sup>*)"
      using csteps_n_imp_csteps by blast
    then have csteps_S: "(\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep (set S))\<^sup>*)"
      using subs by blast
    then show "False"
      by (meson Infeasible_Transform.hyps[OF I J] csteps_S ok conds_sat_conds_n_sat conds_sat_iff)
  qed
  then show ?case
    using conds_n_sat_iff by blast
next
  case (Infeasible_Split_If s p)
  then obtain T F U where s: "s = (T, F, U)" and
    ok: "isOK (check_nonreachable a i I J (split_if s R cs) T F p)" and
    groundT: "ground T" and groundF: "ground F" and cs: "(T, F) \<in> set cs" by auto
  have "(T, F) \<notin> (rstep (set (split_if (T, F, U) R cs)))\<^sup>*"
    using check_nonreachable[OF I J ok, simplified ground_subst_apply[OF groundT] ground_subst_apply[OF groundF]] s by blast
  then show ?case using split_if_correct[OF cs groundT groundF] conds_sat_conds_n_sat conds_sat_iff by meson
next
  case (Infeasible_Goal_Lifting T F p)
  let ?T = "Fun T []"
  let ?F = "Fun F []"
  let ?TF = "(?T, ?F)"
  from Infeasible_Goal_Lifting have ok: "isOK (check_infeasible' a i I J ((?TF, cs) # R) [?TF] p)" by auto
  have "\<not> (\<exists>\<sigma> n. conds_n_sat (set ((?TF, cs) # R)) n [?TF] \<sigma>)"
    using Infeasible_Goal_Lifting.hyps[OF I J ok] by auto
  then have "?TF \<notin> (cstep (set ((?TF, cs) # R)))" unfolding conds_n_sat_iff cstep_def by auto
  then have "\<not> conds_sat (set R) cs \<sigma>" for \<sigma>  using goal_lifting[of T F "set R" cs] by simp
  then show ?case unfolding conds_sat_conds_n_sat by presburger
qed

lemma check_infeasible:
  assumes I: "tp_spec I" and J: "dpp_spec J" and "isOK (check_infeasible a i I J css R cs\<^sub>1 cs\<^sub>2)"
  shows "\<not> (\<exists>\<sigma> n. conds_n_sat (set R) n (cs\<^sub>1 @ cs\<^sub>2) \<sigma>)"
proof -
  let ?cs' = "cs\<^sub>1 @ cs\<^sub>2"
  obtain cs and p
    where
      "(cs, p) \<in> set css" and ok: "isOK (check_infeasible' a i I J R (trancl_of_list cs) p)"
      and cs: "isOK (check (match_rules cs ?cs' \<noteq> None \<and> match_rules ?cs' cs \<noteq> None) id)"
    using assms and match_rules_imp_variants [of _ ?cs']
    apply (auto simp: check_infeasible_def Ru_def)
    done
  then have "\<not> (\<exists>\<sigma> n. conds_n_sat (set R) n cs \<sigma>)"
    using conds_n_sat_trancl_of_list [of "set R" _ cs] by  (blast dest: check_infeasible'[OF I J])
  moreover
  obtain \<pi> :: "string perm" where cs: "cs = \<pi> \<bullet> ?cs'"
    using cs match_rules_imp_variants [of _ ?cs'] by fastforce
  ultimately show ?thesis by (metis cs conds_n_sat_perm_shift rules_pt.permute_minus_cancel(2))
qed

lemma infeasible_rule:
  assumes "\<not> (\<exists>\<sigma>. conds_sat R (conds \<rho>) \<sigma>)"
  shows "(cstep R) = (cstep (R - {\<rho>}))" (is "_ = (cstep ?R)")
proof -
  have "(cstep_n R n) = (cstep_n ?R n)" for n
  proof (induct n)
    case (Suc n)
    show ?case
    proof
      show "(cstep_n R (Suc n)) \<subseteq> (cstep_n ?R (Suc n))"
      proof
        fix s t
        assume "(s, t) \<in> cstep_n R (Suc n)"
        then obtain C l r \<sigma> cs
          where rule: "((l, r), cs) \<in> R"
          and *: "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
          and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
          and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
          by (fast elim: cstep_nE)
        then consider (\<rho>) "((l, r), cs) = \<rho>" | (not_\<rho>) "((l, r), cs) \<in> ?R" by fast
        then show "(s, t) \<in> cstep_n ?R (Suc n)"
        proof (cases)
          case (\<rho>)
          then have "conds_n_sat R n (conds \<rho>) \<sigma>" unfolding conds_n_sat_iff using * by fastforce
          then have "conds_sat R (conds \<rho>) \<sigma>" using * conds_sat_conds_n_sat by blast
          then show ?thesis using assms by auto
        next
          case (not_\<rho>)
          then show ?thesis
            using * by (intro cstep_n_SucI [of l r cs _ \<sigma> _ _ C]) (auto simp: Suc s t)
        qed
      qed
    qed (auto intro: cstep_n_subset [THEN subsetD])
  qed (simp)
  then show ?thesis by (auto simp: cstep_iff)
qed

lemma infeasible_rules:
  assumes "finite S"
    and "\<forall>\<rho> \<in> S. \<not> (\<exists>\<sigma>. conds_sat R (conds \<rho>) \<sigma>)"
  shows "(cstep R) = (cstep (R - S))" (is "_ = (cstep ?R)")
  using assms
proof (induct)
  case (insert \<rho> S)
  then have *: "\<nexists>\<sigma>. conds_sat (R - S) (conds \<rho>) \<sigma>"
    using conds_sat_mono [of "R - S" R "conds \<rho>"] by fast
  from insert have [simp]: "cstep R = cstep (R - S)" by auto
  from infeasible_rule [OF *] and insert.hyps
  show ?case
    by (subst Diff_insert) simp
qed (simp)

definition check_infeasible_rules
  where
    "check_infeasible_rules a i I J R = check_allm (\<lambda>(r, ps).
      check_infeasible' a i I J R (conds r) ps
      <+? (\<lambda>e. showsl_lit (STR ''rule '') \<circ> showsl_crule r \<circ> showsl_lit (STR '' is not infeasible\<newline>'') \<circ> e))"

lemma check_infeasible_rules:
  assumes I: "tp_spec I" and J: "dpp_spec J"  and "isOK (check_infeasible_rules a i I J R rps)"
  shows "cstep (set R) = cstep (set R - fst ` set rps)"
proof -
  have "\<forall>r \<in> fst ` set rps. \<not> (\<exists>\<sigma>. conds_sat (set R) (conds r) \<sigma>)"
    using assms and check_infeasible'[OF I J]
    by (fastforce simp: check_infeasible_rules_def conds_sat_conds_n_sat)
  from infeasible_rules [OF _ this] show ?thesis by simp
qed

lemma check_infeasible_rules_imp_infeasible_rules_wrt:
  assumes  I: "tp_spec I" and J: "dpp_spec J" and "isOK (check_infeasible_rules a i I J R rps)"
  shows "infeasible_rules_wrt (set R) (fst ` set rps)"
  using assms and check_infeasible'[OF I J]
  by (force simp: check_infeasible_rules_def infeasible_rules_wrt_def infeasible_at_def)

lemma check_infeasible_rules':
  assumes  I: "tp_spec I" and J: "dpp_spec J" and "isOK (check_infeasible_rules a i I J (list_diff R (map fst rps)) rps)"
  shows "cstep (set R) = cstep (set R - fst ` set rps)"
  using check_infeasible_rules_imp_infeasible_rules_wrt [OF assms]
    and infeasible_rules_wrt_minimize [of "set R" "fst ` set rps"]
  by (intro infeasible_rules_wrt_cstep_conv) simp


datatype ('f,'v) feasibility_proof =
  Feasible_Witness "('f,'v)substL" "('f, 'v) cstep_proof list list"

fun check_feasibility_proof where
  "check_feasibility_proof r cs (Feasible_Witness sigma prf) = check_feasibility r cs (subst_of sigma) prf
     <+? (\<lambda> e. showsl_lit (STR ''problem in proving feasibility of conditions\<newline>'') o 
        showsl_lines (STR '''') cs o showsl_nl o 
        showsl_lit (STR ''via substitution '') o 
        showsl sigma o showsl_nl o e)" 

lemma check_feasibility_proof: assumes "isOK(check_feasibility_proof r cs prf)" 
  shows "\<exists> \<sigma>. conds_sat (set r) cs \<sigma>" 
  using assms
proof (induct "prf" arbitrary: r cs)
  case (Feasible_Witness sigma p)
  hence "isOK(check_feasibility r cs (subst_of sigma) p)" by auto
  from check_feasibility[OF this]
  show ?case by blast
qed

end
