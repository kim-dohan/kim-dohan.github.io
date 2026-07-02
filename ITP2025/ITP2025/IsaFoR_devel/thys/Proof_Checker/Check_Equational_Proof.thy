(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Equational_Proof
  imports
    Check_Completion_Proof
    CR.Ordered_Completion_Impl
begin

hide_const (open) Congruence.eq 
hide_const (open) Order_Relation.Refl  

subsection \<open>Proving equations from an equational system\<close>

datatype ('f, 'l, 'v) equational_proof =
  Equational_Proof_Tree "(('f, 'l) lab, 'v) eq_proof"
| Completion_and_Normalization "(('f, 'l) lab, 'v) rules" "('f, 'l, 'v) completion_proof"
| Conversion "(('f,'l)lab,'v)term list"
| Conversion_With_History "(('f,'l)lab,'v)subsumption_proof"

datatype ('f, 'l, 'v) equational_disproof =
  Completion_and_Normalization_Different "(('f, 'l) lab, 'v) rules" "('f, 'l, 'v) completion_proof"
| Approx_and_Completion_and_Normalization_Different "(('f, 'l) lab, 'v) rules" "('f, 'l, 'v) approx_completion_proof"
| Ordered_Completion_and_Normalization_Different
    "(('f, 'l) lab, 'v) rules"
    "(('f, 'l) lab, string) equation list"
    "('f, 'l) lab reduction_order_input"
    "(('f, 'l) lab, 'v) ordered_completion_proof"
| Approx_and_Ordered_Completion_and_Normalization_Different
    "(('f, 'l) lab, 'v) rules" \<comment> \<open>rules of ground complete system\<close>
    "(('f, 'l) lab, 'v) rules" \<comment> \<open>equations of ground complete system\<close>
    "('f, 'l) lab reduction_order_input" \<comment> \<open>reduction order\<close>

fun proves_impl :: "('f, 'v) rules \<Rightarrow> ('f, 'v) eq_proof \<Rightarrow> ('f, 'v) rule option"
where
  "proves_impl eqs (Refl s) = Some (s, s)"
| "proves_impl eqs (Sym p) = do {
    (s, t) \<leftarrow> proves_impl eqs p;
    Some (t, s)
  }"
| "proves_impl eqs (Trans p1 p2) = do {
    (s, t)  \<leftarrow> proves_impl eqs p1;
    (t', u) \<leftarrow> proves_impl eqs p2;
    guard (t = t');
    Some (s, u)
  }"
| "proves_impl eqs (Assm (l, r) \<sigma>) = do {
    guard ((l, r) \<in> set eqs);
    Some (l \<cdot> \<sigma>, r \<cdot> \<sigma>)
  }"
| "proves_impl eqs (Cong f ps) = do {
    sts \<leftarrow> Option_Monad.mapM (proves_impl eqs) ps;
    Some (Fun f (map fst sts), Fun f (map snd sts))
  }"

fun check_proves :: "('f:: showl, 'v:: showl) rules \<Rightarrow> ('f, 'v) eq_proof \<Rightarrow> showsl + ('f, 'v) rule" where
  "check_proves E (Refl s) = Inr (s, s)"
| "check_proves E (Sym p) = do {
    (s, t) \<leftarrow> check_proves E p;
    Inr (t, s)
  }"
| "check_proves E (Trans p1 p2) = do {
    (s, t) \<leftarrow> check_proves E p1;
    (t', u) \<leftarrow> check_proves E p2;
    if (t = t')
      then Inr (s, u)
      else error (showsl_lit (STR ''the error occurs in the following part \<newline>'')
        \<circ> showsl_eq_proof (Trans p1 p2) \<circ> showsl_lit (STR ''\<newline>\<newline>'')
        \<circ> showsl t \<circ> showsl_lit (STR '' is not equal to '') \<circ> showsl t')
  }"
| "check_proves E (Assm (l, r) \<sigma>) = (
    if (l, r) \<in> set E
      then Inr (l \<cdot> \<sigma>, r \<cdot> \<sigma>)
      else error (showsl_lit (STR ''the error occurs in the following part \<newline>'')
        \<circ> showsl_eq_proof (Assm (l, r) \<sigma>) \<circ> showsl_lit (STR ''\<newline>\<newline>'') \<circ> showsl_eq (l, r)
        \<circ> showsl_lit (STR '' is not in the '') \<circ> showsl_eqs E))"
| "check_proves E (Cong f ps) = do {
    sts \<leftarrow> Error_Monad.mapM (check_proves E) ps;
    Inr (Fun f (map fst sts), Fun f (map snd sts))
  }"

lemma proves_impl_sound[simp]:
  "proves_impl eqs p = proves (set eqs) p"
  by (induct p) (simp_all cong: Option_Monad.mapM_cong)

lemma mapM_sum_option:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> f x = Inr y \<Longrightarrow> g x = Some y"
    and "Error_Monad.mapM f xs = Inr ys"
  shows "Option_Monad.mapM g xs = Some ys"
using assms
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  from Cons(3) obtain z zs where "f x = Inr z"
    and "Error_Monad.mapM f xs = Inr zs" and "ys = z # zs"
    by (cases "f x", simp) (cases "Error_Monad.mapM f xs", force+)
  with Cons(1,2) have "Option_Monad.mapM g xs = Some zs" by simp
  moreover from Cons(2) and \<open>f x = Inr z\<close> have "g x = Some z" by simp
  ultimately show ?case unfolding \<open>ys = z#zs\<close> by simp
qed

lemma check_proves_sound[simp]:
  "check_proves E p = Inr eq \<Longrightarrow> proves_impl E p = Some eq"
proof (induct p arbitrary: eq rule: eq_proof_induct)
  case (Assm l r) then show ?case by (cases "(l, r) \<in> set E") simp_all
next
  case (Refl s) then show ?case by simp
next
  case (Sym p) then show ?case by (cases "check_proves E p") auto
next
  case (Trans p1 p2)
  from Trans(3) obtain s t u v 
    where p1: "check_proves E p1 = Inr (s, t)" and p2: "check_proves E p2 = Inr (u, v)" and eq: "t = u"
    by (cases "check_proves E p1", simp, cases "check_proves E p2", force+)
  with Trans(1, 2)
    have p1': "proves_impl E p1 = Some (s, t)" and p2': "proves_impl E p2 = Some (u, v)" by auto
  from Trans(3) have eq': "eq = (s, v)" by (simp add: p1 p2 eq)
  show ?case using p1' p2' by (simp add: eq' eq)
next
  case (Cong f ps)
  from this
    obtain sts where "Error_Monad.mapM (check_proves E) ps = Inr sts"
      and eq: "eq = (Fun f (map fst sts), Fun f (map snd sts))" by (cases "Error_Monad.mapM (check_proves E) ps") auto
  with mapM_sum_option[OF _ this(1)] and Cong(1)
    have 1: "Option_Monad.mapM (proves_impl E) ps = Some sts" by simp
  show ?case unfolding proves_impl.simps unfolding 1 eq by simp
qed
  
definition check_eq_proof :: "('f:: showl, 'v:: showl) rules \<Rightarrow> ('f, 'v) eq_proof \<Rightarrow> ('f, 'v) rule \<Rightarrow> showsl check" where
  "check_eq_proof E p eq \<equiv> do {
    eq' \<leftarrow> check_proves E p;
    if eq = eq'
      then Inr ()
      else error (showsl_lit (STR ''the proof does not fit the goal''))
  } <+? (\<lambda>s. showsl_lit (STR ''there is an error in the equational logic proof\<newline>'')
    \<circ> showsl_eq_proof p \<circ> showsl_lit (STR ''\<newline>\<newline>for proving the equation\<newline>\<newline>'') 
    \<circ> showsl_eq eq \<circ> showsl_lit (STR ''\<newline>\<newline>using the '') \<circ> showsl_eqs E
    \<circ> showsl_nl \<circ> s)"

lemma check_eq_proof_sound[simp]:
  assumes "isOK (check_eq_proof E p eq)"
  shows "eq \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
  using assms and check_proves_sound[of E p eq]
  unfolding check_eq_proof_def eq_theory_def eq_theory_is_esteps[symmetric]
  by (cases "check_proves E p") auto
  
fun
  check_equational_proof ::
    "bool \<Rightarrow> showsl \<Rightarrow>
    ('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
    ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
    (('f, label_type) lab, string) equation list \<Rightarrow>
    (('f, label_type) lab, string) equation \<Rightarrow>
    ('f, label_type, string) equational_proof \<Rightarrow>
    showsl check"
where
  "check_equational_proof a i I J E eq (Equational_Proof_Tree p) = debug i (STR ''Equational_Proof_Tree'')
    (check_eq_proof E p eq)"
| "check_equational_proof a i I J E eq (Conversion eseq) = debug i (STR ''Conversion'')
       (check_conversion_sequence E (fst eq) (snd eq) eseq)"
| "check_equational_proof a i I J E eq (Conversion_With_History convs) = debug i (STR ''Conversion with History'')
       (check_single_subsumption eq E convs)"
| "check_equational_proof a i I J E eq (Completion_and_Normalization R p) = debug i (STR ''Completion_and_Normalization'') (do {
    check_completion_proof a i I J E R p;
    let s = fst eq;
    let t = snd eq;
    (case (compute_rstep_NF R s, compute_rstep_NF R t) of
      (Some s', Some t') \<Rightarrow> (
        if s' = t'
          then Inr ()
          else error (showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' have different normal forms'')))
    | _ \<Rightarrow> error (showsl_lit (STR ''error when computing normal forms of '') \<circ> showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t)
    )})"

fun equational_assms :: "bool \<Rightarrow> ('f, 'l, 'v) equational_proof \<Rightarrow> (('f, 'l, 'v) assm) list" where
  "equational_assms a (Equational_Proof_Tree _) = []"
| "equational_assms a (Conversion _) = []"
| "equational_assms a (Conversion_With_History _) = []"
| "equational_assms a (Completion_and_Normalization _ p) = completion_assms a p"

lemma compute_rstep_NF_SN:
  assumes "SN (rstep (set R))"
  shows "compute_rstep_NF R s \<noteq> None"
proof -
  have "\<And>u v. first_rewrite R u = Some v \<Longrightarrow> (u, v) \<in> rstep (set R)"
    unfolding first_rewrite_def by (auto simp: rewrite_sound split: list.splits)
  from compute_NF_SN[OF assms, of "first_rewrite R", OF this]
    show ?thesis unfolding compute_rstep_NF_def by blast
qed

lemma rsteps_mono:
  assumes "R \<subseteq> R'"
  shows "(rstep R)^* \<subseteq> (rstep R')^*"
  by (rule rtrancl_mono[OF rstep_mono[OF assms]])

lemma check_equational_proof_with_assms_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (equational_assms a prf). holds p"
    and ok: "isOK (check_equational_proof a i I J E eq prf)"
  shows "eq \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
proof (cases "prf")
  case (Equational_Proof_Tree p) with ok show ?thesis by (force split: option.splits)
next
  case (Conversion_With_History cnv)
  with ok have ok: "isOK(check_single_subsumption eq E cnv)" by simp
  from check_single_subsumption[OF ok] have "eq \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*" by simp
  then show ?thesis .
next
  case (Conversion eseq)
  with ok have ok: "isOK(check_conversion_sequence E (fst eq) (snd eq) eseq)" by simp
  from check_conversion_sequence[OF ok] have "eq \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*" by simp
  then show ?thesis .
next
  case (Completion_and_Normalization R p)
  note 1 = this
  let ?s = "fst eq"
  let ?t = "snd eq"
  from ok[unfolded 1]
  have "isOK (check_completion_proof a i I J E R p)" by simp
  from check_completion_proof_with_assms_sound[OF I J fin[unfolded 1, simplified] this]
  have equiv: "equivalent (set E) (set R)" and cr: "CR (rstep (set R))" and sn: "SN (rstep (set R))"
    unfolding completed_rewrite_system_def by simp+
  from ok[unfolded 1, simplified, THEN conjunct2] obtain s' t'
    where s': "compute_rstep_NF R ?s = Some s'"
      and t': "compute_rstep_NF R ?t = Some t'"
    using compute_rstep_NF_SN[OF sn] by force
  with compute_rstep_NF_sound and compute_rstep_NF_complete
  have 2: "(?s, s') \<in> (rstep (set R))^*" and 3: "(?t, t') \<in> (rstep (set R))^*" by auto
  from ok have eq: "s' = t'" by (simp add: 1 s' t')
  from 2 have "(?s, s') \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*" 
    using rsteps_mono[of "set R" "(set R)^<->"] by auto
  moreover have "(s', ?t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  proof (rule sym_esteps_pair)
    from 3 show "(?t, s') \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*" 
      using rsteps_mono[of "set R" "(set R)^<->"] by (auto simp: eq)
  qed
  ultimately have "(?s, ?t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def by (rule rtrancl_trans)
  then show ?thesis unfolding equiv[unfolded equivalent_def] by simp
qed

lemma check_equational_proof_with_assms_entails:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (equational_assms a prf). holds p"
    and ok: "isOK (check_equational_proof a i I J E eq prf)"
  shows "entails ty (set E) eq" 
proof -
  from check_equational_proof_with_assms_sound[OF I J fin ok]
  have "eq \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*" by auto
  thus ?thesis using esteps_imp_entails[of _ _ "set E" ty]
    by (cases eq, auto)
qed


lemma equational_assms_False[simp]: "equational_assms False prf = []"
  by (cases "prf") (simp_all)

fun
  check_equational_disproof ::
    "bool \<Rightarrow> showsl \<Rightarrow>
    ('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
    ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
    (('f, label_type) lab, string) equation list \<Rightarrow>
    (('f, label_type) lab, string) equation \<Rightarrow>
    ('f, label_type, string) equational_disproof \<Rightarrow>
    showsl check"
where
  "check_equational_disproof a i I J E eq (Completion_and_Normalization_Different R p) =
   debug i (STR ''Completion_and_Normalization'') (do {
    check_completion_proof a i I J E R p;
    let s = fst eq;
    let t = snd eq;
    (case (compute_rstep_NF R s, compute_rstep_NF R t) of
      (Some s', Some t') \<Rightarrow> (
        if s' \<noteq> t'
          then Inr ()
          else error (showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' have same normal form '') \<circ> showsl s'))
    | _ \<Rightarrow> error (showsl_lit (STR ''error when computing normal forms of '') \<circ> showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t)
    )})"
 | "check_equational_disproof a i I J E eq (Approx_and_Completion_and_Normalization_Different R p) =
    debug i (STR ''Approx_and_Completion_and_Normalization'') (do {
    check_approx_completion_proof a i I J E R p;
    let s = fst eq;
    let t = snd eq;
    (case (compute_rstep_NF R s, compute_rstep_NF R t) of
      (Some s', Some t') \<Rightarrow> (
        if s' \<noteq> t'
          then Inr ()
          else error (showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' have same normal form '') \<circ> showsl s'))
    | _ \<Rightarrow> error (showsl_lit (STR ''error when computing normal forms of '') \<circ> showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t)
    )})"
 | "check_equational_disproof a i I J E\<^sub>0 eq (Ordered_Completion_and_Normalization_Different R E ro p) =
    debug i (STR ''Ordered_Completion_and_Normalization'') (
      check_equational_disproof_oc i eq E\<^sub>0 E R ro p)"
 | "check_equational_disproof a i I J E\<^sub>0 eq (Approx_and_Ordered_Completion_and_Normalization_Different R E ro) =
    debug i (STR ''Approx_and_Ordered_Completion_and_Normalization'') (
      check_equational_disproof_by_ground_complete_system i eq E\<^sub>0 E R ro)"

fun equational_dis_assms :: "bool \<Rightarrow> ('f, 'l, 'v) equational_disproof \<Rightarrow> (('f, 'l, 'v) assm) list" where
  "equational_dis_assms a (Completion_and_Normalization_Different _ p) = completion_assms a p"
 | "equational_dis_assms a (Approx_and_Completion_and_Normalization_Different _ p) = approx_completion_assms a p"
 | "equational_dis_assms a _ = []"

lemma check_equational_disproof_with_assms_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (equational_dis_assms a prf). holds p"
    and ok: "isOK (check_equational_disproof a i I J E eq prf)"
  shows "eq \<notin> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
proof (cases "prf")
  case (Completion_and_Normalization_Different R p)
  note 1 = this
  note ok = ok[unfolded 1, simplified, unfolded Let_def]
  obtain s t where [simp]:"eq = (s,t)" by (cases eq, auto)
  from ok
    have "isOK (check_completion_proof a i I J E R p)" by simp
  from check_completion_proof_with_assms_sound[OF I J fin[unfolded 1, simplified] this]
  have equiv: "equivalent (set E) (set R)" and cr: "CR (rstep (set R))" and sn: "SN (rstep (set R))"
    unfolding completed_rewrite_system_def by simp+
  from ok obtain s' t'
    where s': "compute_rstep_NF R s = Some s'"
    and t': "compute_rstep_NF R t = Some t'"
    using compute_rstep_NF_SN[OF sn] by force
  with compute_rstep_NF_sound and compute_rstep_NF_complete
    have 2: "(s, s') \<in> (rstep (set R))^*" "s' \<in> NF_trs (set R)" and 3: "(t, t') \<in> (rstep (set R))^*" "t' \<in> NF_trs (set R)" by auto
  from ok have neq: "s' \<noteq> t'" by (simp add: 1 s' t')
  {
    assume "(s,t) \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
    from this[unfolded equiv[unfolded equivalent_def]] have eq: "(s,t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*" by simp
    have "semi_complete (rstep (set R))" 
      by (rule, rule SN_imp_WN[OF sn], rule cr)
    note eq = eq[unfolded semi_complete_imp_conversionIff_same_NF[OF this], rule_format, of s' t']
    from eq 2 3 have "s' = t'" by auto
    with neq have False ..
  }
  then show ?thesis by auto
next
  case (Approx_and_Completion_and_Normalization_Different R p)
  note 1 = this
  note ok = ok[unfolded 1, simplified, unfolded Let_def]
  obtain s t where [simp]:"eq = (s,t)" by (cases eq, auto)
  from ok
    have "isOK (check_approx_completion_proof a i I J E R p)" by simp
  from check_approx_completion_proof_with_assms_sound[OF I J fin[unfolded 1, simplified] this]
  have subsumption: "subsumes (set R) (set E)" and cr: "CR (rstep (set R))" and sn: "SN (rstep (set R))"
    unfolding approx_completed_rewrite_system_def by simp+
  from ok obtain s' t'
    where s': "compute_rstep_NF R s = Some s'"
    and t': "compute_rstep_NF R t = Some t'"
    using compute_rstep_NF_SN[OF sn] by force
  with compute_rstep_NF_sound and compute_rstep_NF_complete
    have 2: "(s, s') \<in> (rstep (set R))^*" "s' \<in> NF_trs (set R)" and 3: "(t, t') \<in> (rstep (set R))^*" "t' \<in> NF_trs (set R)" by auto
  from ok have neq: "s' \<noteq> t'" by (simp add: 1 s' t')
  {
    assume "(s,t) \<in> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
    with subsumption[unfolded subsumption_def] have eq: "(s,t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
      by (meson basic_trans_rules(31) subsumes_def)
    have "semi_complete (rstep (set R))" 
      by (rule, rule SN_imp_WN[OF sn], rule cr)
    note eq = eq[unfolded semi_complete_imp_conversionIff_same_NF[OF this], rule_format, of s' t']
    from eq 2 3 have "s' = t'" by auto
    with neq have False ..
  }
  then show ?thesis by auto
next
  case (Ordered_Completion_and_Normalization_Different R' E' ro ocp)
  note 1 = this
  from ok have "isOK (check_equational_disproof_oc i eq E E' R' ro ocp)"
    unfolding 1 by force
  from Ordered_Completion_Impl.check_equational_disproof[OF this] show ?thesis by auto
next
  case (Approx_and_Ordered_Completion_and_Normalization_Different R' E' ro)
  note 1 = this
  from ok have "isOK (check_equational_disproof_by_ground_complete_system i eq E E' R' ro)"
    unfolding 1 by auto
  from Ordered_Completion_Impl.check_equational_disproof_by_ground_complete_system [OF this]
  show ?thesis .
qed

lemma equational_dis_assms_False[simp]: "equational_dis_assms False prf = []"
  by (cases "prf") (simp_all)

lemma check_equational_disproof_sound: 
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_equational_disproof False i I J E eq prf)"
  shows "eq \<notin> (rstep (set E))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule check_equational_disproof_with_assms_sound[OF I J _ ok]) simp

end
