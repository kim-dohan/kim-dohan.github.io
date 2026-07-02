(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015-2017)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Conditional_CRP
  imports
    Check_CRP
    Check_Quasi_Reductive
    Check_AL94
    Check_Level_Confluence
    CTRS.Non_Confluence2
    CTRS.Inline_Conditions_Impl
begin

(*TODO: move*)
lemma cstep_rstep_conv:
  assumes "\<forall>\<rho> \<in> R. conds \<rho> = []"
  shows "cstep R = rstep (fst ` R)"
proof -
  { fix C \<sigma> l r cs assume rule: "((l, r), cs) \<in> R"
    from assms [THEN bspec, OF rule]
    have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> cstep R" by (intro cstepI [OF rule]) simp_all }
  with assms show ?thesis by (auto elim!: cstepE)
qed

datatype (dead 'f, dead 'l, dead 'v, dead 'rp) ccr_transformation =
  Inline_Conditions_CCRT
    "(('f, 'l) lab, 'v) crules"
    "((('f, 'l) lab, 'v) crule \<times> (('f, 'l) lab, 'v) rules) list"
| Infeasible_Rule_Removal_CCRT
    "((('f, 'l) lab, 'v) crule \<times> ('f, 'v, 'rp, 'l) infeasibility_proof) list"

primrec check_ccr_trans
  where
    "check_ccr_trans a i I J R (Inline_Conditions_CCRT R' rcs) =
      debug i (STR ''Inline Conditions'') (do {
       check_inline_conds R R' rcs;
       return R'
      })"
  | "check_ccr_trans a i I J R (Infeasible_Rule_Removal_CCRT rps) =
      debug i (STR ''Infeasible Rule Removal'') (do {
        check_infeasible_rules a i I J (list_diff R (map fst rps)) rps;
        return (list_diff R (map fst rps))
      })"

lemma check_ccr_trans_Inr:
  assumes I: "tp_spec I" and J: "dpp_spec J" and "check_ccr_trans a i I J R p = Inr R'"
  shows "CR (cstep (set R)) \<longleftrightarrow> CR (cstep (set R'))"
  using assms
proof (induct p arbitrary: R')
  case (Inline_Conditions_CCRT R' rcs)
  note check = this [simplified]
  have *: "(cstep (set R'))\<^sup>* = (cstep (set R))\<^sup>*"
    using check by auto
  then show ?case by (simp add: rtrancl_eq_CR [OF *])
next
  case (Infeasible_Rule_Removal_CCRT rps)
  then have "cstep (set R) = cstep (set R - fst ` set rps)"
    and "R' = list_diff R (map fst rps)"
    by (auto simp: check_infeasible_rules')
  then show ?case by simp
qed

datatype ('f, 'l, 'v, 'rp) conditional_cr_proof =
  Unconditional_CR "('f, 'l, 'v) cr_proof"
| Unravel_CR
    "((('f, 'l) lab, 'v) crule \<times> (('f, 'l) lab, 'v) rules) list"
    "('f, 'l, 'v) cr_proof"
| Transformation_CR
    "('f, 'l, 'v, 'rp) ccr_transformation"
    "('f, 'l, 'v, 'rp) conditional_cr_proof"
| Almost_Orthogonal_CR
(* NOTE: not used, see also mod_infeasibility in Check_Level_Confluence *)
(*
| Almost_Orthogonal_Modulo_Infeasibility_CR
    "((('f, 'l) lab, 'v) rules \<times> ('f, 'v, 'rp, 'l) infeasibility_proof) list"
*)
| Almost_Orthogonal_Modulo_Infeasibility_CR'
    "((('f, 'l) lab, 'v) rules \<times> (('f, 'l) lab, 'v) rules \<times> ('f, 'v, 'rp, 'l) ao_infeasibility_proof) list"
| AL94_CR
    "('f, 'l, 'v) quasi_reductive_proof"
    "((('f, 'l) lab, 'v) term \<times> (('f, 'l) lab, 'v) term \<times> (('f, 'l) lab, 'v) rules \<times> (('f, 'l) lab, 'v) context_joinable_proof) list"
    "((('f, 'l) lab, 'v) rules \<times>  ('f, 'v, 'rp, 'l) infeasibility_proof) list"
    "((('f, 'l) lab, 'v) subst \<times> (('f, 'l) lab, 'v) unfeasible_proof) list"

primrec
  check_conditional_cr_proof
    where
      "check_conditional_cr_proof a i I J ctrs (Unconditional_CR prf) =
        debug i (STR ''Unconditional'') (do {
          check_all (\<lambda>\<rho>. conds \<rho> = []) ctrs
            <+? (\<lambda>\<rho>. showsl_lit (STR ''rule with non-empty conditions'') \<circ> showsl_nl \<circ> showsl_crule \<rho>);
          check_cr_proof a i I J (map fst ctrs) prf
        })"
    | "check_conditional_cr_proof a i I J ctrs (Unravel_CR u_info prf) =
        debug i (STR ''Unravel'') (do {
          r \<leftarrow> check_sp_unraveling u_info ctrs
            <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error in unraveling'') \<circ> showsl_nl \<circ> s);
          check_cr_proof a (add_index i 1) I J r prf
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below confluence proof'') \<circ> showsl_nl \<circ> s)
        })"
    | "check_conditional_cr_proof a i I J ctrs (Transformation_CR t prf) =
        debug i (STR ''CR Reflecting Transformation'') (do {
          ctrs' \<leftarrow> check_ccr_trans a i I J ctrs t;
          check_conditional_cr_proof a i I J ctrs' prf
        })"
    | "check_conditional_cr_proof a i I J ctrs Almost_Orthogonal_CR =
        debug i (STR ''Almost-Orthogonal'') (check_level_confluence ctrs)"
(*
    | "check_conditional_cr_proof a i I J ctrs (Almost_Orthogonal_Modulo_Infeasibility_CR cps) =
        debug i (STR ''Almost-Orthogonal modulo Infeasibility'') (
          check_level_confluence_modulo_infeasibility a i I J cps ctrs)"
*)
    | "check_conditional_cr_proof a i I J ctrs (Almost_Orthogonal_Modulo_Infeasibility_CR' cps) =
        debug i (STR ''Almost-Orthogonal modulo Infeasibility + meet-to-join'') (
          check_level_confluence_modulo_infeasibility' a i I J cps ctrs)"
    | "check_conditional_cr_proof a i I J ctrs (AL94_CR qrp cj icp ucp) =
        debug i (STR ''AL94'') (do {
          check_quasi_reductive_proof a i I J ctrs qrp;
          check_al94 a i I J cj icp ucp ctrs
        })"

primrec
  conditional_cr_assms
  where
    "conditional_cr_assms a (Unconditional_CR p) = cr_assms a p"
  | "conditional_cr_assms a (Unravel_CR _ p) = cr_assms a p"
  | "conditional_cr_assms a (Transformation_CR _ p) = conditional_cr_assms a p"
  | "conditional_cr_assms a Almost_Orthogonal_CR = []"
(*
  | "conditional_cr_assms a (Almost_Orthogonal_Modulo_Infeasibility_CR _) = []"
*)
  | "conditional_cr_assms a (Almost_Orthogonal_Modulo_Infeasibility_CR' _) = []"
  | "conditional_cr_assms a (AL94_CR qrp _ _ _) = quasi_reductive_assms a qrp"

lemma check_conditional_cr_proof_with_assms_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (conditional_cr_assms a prf). holds p"
    and ok: "isOK (check_conditional_cr_proof a i I J ctrs prf)"
  shows "CR (cstep (set ctrs))"
  using fin ok
proof -
  interpret tp_spec I by fact
  from ok fin show ?thesis
  proof (induct "prf" arbitrary: i ctrs)
    case check: (Unconditional_CR prof)
    then have "CR (rstep (set (map fst ctrs)))"
      by (intro check_cr_proof_with_assms_sound [OF I J]) auto
    moreover
    have "cstep (set ctrs) = rstep (set (map fst ctrs))"
    proof -
      have "\<forall>r \<in> set ctrs. conds r = []" using check by auto
      from cstep_rstep_conv [OF this] show ?thesis by simp
    qed
    ultimately show ?case by simp
  next
    case (Unravel_CR u_info prof)
    note check = Unravel_CR(1)[simplified]
    from check obtain R where R: "check_sp_unraveling u_info ctrs = return R" by auto
    from check[unfolded R]
    have ok: "isOK (check_cr_proof a (add_index i 1) I J R prof)" by simp
    from Unravel_CR(2) have a: "\<forall>a\<in>set (cr_assms a prof). holds a" by auto
    from check_cr_proof_with_assms_sound[OF I J a ok] have CR: "CR (rstep (set R))" by simp
    show ?case
      by (rule check_sp_unraveling_CR[OF R infinite_lab CR])
  next
    case IH: (Transformation_CR t prof)
    then obtain ctrs' where "check_ccr_trans a i I J ctrs t = Inr ctrs'" by auto
    with IH show ?case by (simp add: check_ccr_trans_Inr[OF I J])
  next
    case Almost_Orthogonal_CR
    then show ?case by (intro level_confluent_imp_CR; simp)
(*
  next
    case (Almost_Orthogonal_Modulo_Infeasibility_CR cps)
    then show ?case by (intro level_confluent_imp_CR; simp)
*)
  next
    case (Almost_Orthogonal_Modulo_Infeasibility_CR' cps)
    then show ?case
      apply (intro level_confluent_imp_CR)
      using assms by force
  next
    case (AL94_CR qrp cj icp ucp)
    then show ?case
      by (auto dest: check_al94[OF I J] quasi_reductive_quasi_decreasing check_quasi_reductive_proof_with_assms_sound [OF I J])
  qed
qed

lemma conditional_cr_assms_False [simp]:
  "conditional_cr_assms False prf = []"
  by (induct "prf") simp_all

lemma check_conditional_cr_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_conditional_cr_proof False i I J ctrs prf)"
  shows "CR (cstep (set ctrs))"
  by (rule check_conditional_cr_proof_with_assms_sound[OF I J _ ok], simp)

definition Ru_impl :: "('f, 'v) crules \<Rightarrow> ('f, 'v) rules"
  where "Ru_impl R = map fst R"

lemma Ru_Ru_impl:
  "Ru (set R) = set (Ru_impl R)"
  by (auto simp: Ru_def Ru_impl_def)

definition check_conditional_non_cr ::
  "(('f :: {showl, compare_order}) lt, string) crules \<Rightarrow>
  ('f lt, string) term \<Rightarrow> ('f lt, string) term \<Rightarrow> ('f lt, string) term \<Rightarrow>
  ('f lt,string) cstep_proof list \<Rightarrow>
  ('f lt,string) cstep_proof list \<Rightarrow>
  ('f lt, string, 'q :: {showl, compare_order},_) non_join_info \<Rightarrow> showsl check"
where
  "check_conditional_non_cr R s t u ps qs reason \<equiv> do {
    check_csteps R s t ps;
    check_csteps R s u qs;
    check_non_join (Ru_impl R) (Ru_impl R) t u reason
  }"

lemma check_conditional_non_cr:
  assumes ok: "isOK (check_conditional_non_cr R s t u ps qs prf)"
  shows "\<not> CR (cstep (set R))"
proof
  let ?R = "cstep (set R)"
  assume CR: "CR ?R"
  note ok = ok [unfolded check_conditional_non_cr_def Let_def, simplified]
  have s1: "(s, t) \<in> ?R\<^sup>*" and s2: "(s, u) \<in> ?R\<^sup>*" using ok check_csteps by auto
  from ok have "isOK (check_non_join (Ru_impl R) (Ru_impl R) t u prf)" by auto
  from check_non_join [OF this] have "(t, u) \<notin> (rstep (set (Ru_impl R)))\<^sup>\<down>"
    unfolding Abstract_Rewriting.join_def by (meson relcompEpair rtrancl_converseD)
  with CR s1 s2 show False by (metis Ru_Ru_impl csteps_peak_non_rstep_Ru_join_non_CR)
qed

datatype (dead 'f, dead 'l, dead 'v, 'q, 'rp) conditional_ncr_proof =
  Unconditional_CNCR "('f, 'l, 'v, 'q) ncr_proof"
| Transformation_CNCR
    "('f, 'l, 'v, 'rp) ccr_transformation"
    "('f, 'l, 'v, 'q, 'rp) conditional_ncr_proof"
| Non_Join_CNCR
    "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term" "(('f, 'l) lab, 'v) term"
    "(('f, 'l) lab, 'v) cstep_proof list"
    "(('f, 'l) lab, 'v) cstep_proof list"
    "(('f, 'l) lab, 'v, 'q, ('f,'l)lab redtriple_impl) non_join_info"

primrec check_conditional_ncr_proof
  where
    "check_conditional_ncr_proof a i I J R (Unconditional_CNCR prf) =
      debug i (STR ''Unconditional'') (do {
        check_all (\<lambda>\<rho>. conds \<rho> = []) R
          <+? (\<lambda>\<rho>. showsl_lit (STR ''rule with non-empty conditions'') \<circ> showsl_nl \<circ> showsl_crule \<rho>);
        check_ncr_proof a i I J (map fst R) prf
      })"
  | "check_conditional_ncr_proof a i I J R (Transformation_CNCR t prf) =
      debug i (STR ''CR Preserving Transformation'') (do {
        R' \<leftarrow> check_ccr_trans a i I J R t;
        check_conditional_ncr_proof a i I J R' prf
      })"
  | "check_conditional_ncr_proof a i I J R (Non_Join_CNCR s t u ps qs prf) =
      debug i (STR ''Conditional Non-Joinability'') (do {
        check_conditional_non_cr R s t u ps qs prf
          <+? (\<lambda>s. i \<circ> showsl_lit (STR ''error when disproving CR of '') \<circ> showsl_ctrs R \<circ> showsl_nl \<circ> s)
      })"

primrec conditional_ncr_assms
  where
    "conditional_ncr_assms a (Unconditional_CNCR p) = ncr_assms a p"
  | "conditional_ncr_assms a (Transformation_CNCR _ p) = conditional_ncr_assms a p"
  | "conditional_ncr_assms a (Non_Join_CNCR _ _ _ _ _ _)  = []"

lemma check_conditional_ncr_proof_with_assms_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p \<in> set (conditional_ncr_assms a prf). holds p"
    and ok: "isOK (check_conditional_ncr_proof a i I J R prf)"
  shows "\<not> CR (cstep (set R))"
proof -
  interpret tp_spec I by fact
  from ok fin show ?thesis
  proof (induct "prf" arbitrary: i R)
    case check: (Unconditional_CNCR prof)
    then have "\<not> CR (rstep (set (map fst R)))"
      by (intro check_ncr_proof_with_assms_sound [OF I J]) auto
    moreover
    have "cstep (set R) = rstep (set (map fst R))"
    proof -
      have "\<forall>r \<in> set R. conds r = []" using check by auto
      from cstep_rstep_conv [OF this] show ?thesis by simp
    qed
    ultimately show ?case by simp
  next
    case IH: (Transformation_CNCR t prof)
    then obtain R' where "check_ccr_trans a i I J R t = Inr R'" by auto
    with IH show ?case by (simp add: check_ccr_trans_Inr[OF I J])
  next
    case (Non_Join_CNCR s t u ps qs prof)
    then have ok: "isOK (check_conditional_non_cr R s t u ps qs prof)" by simp
    from check_conditional_non_cr [OF ok] show ?case .
  qed
qed

lemma conditional_ncr_assms_False [simp]: "conditional_ncr_assms False prf = []"
  by (induct "prf") simp_all

lemma check_conditional_ncr_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
  and ok: "isOK (check_conditional_ncr_proof False i I J R prf)"
  shows "\<not> CR (cstep (set R))"
  by (rule check_conditional_ncr_proof_with_assms_sound[OF I J _ ok], simp)

end
