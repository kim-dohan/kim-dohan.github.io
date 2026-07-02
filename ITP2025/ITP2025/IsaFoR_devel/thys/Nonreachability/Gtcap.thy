(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
Author:  Akihisa Yamada <akihisa.yamada@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>A generalized tcap-like decomposition of nonreachability problems\<close>

theory Gtcap
  imports
    TRS.Tcap
    TRS.Signature_Extension
begin

subsection \<open>Counting the number of root-steps in a rewrite sequence\<close>

inductive rrsteps_n for R
where
  nrrsteps: "(s, t) \<in> (nrrstep R)\<^sup>* \<Longrightarrow> rrsteps_n R 0 s t"
| rrstep: "(s, t) \<in> rrstep R \<Longrightarrow> rrsteps_n R (Suc 0) s t"
| trans: "rrsteps_n R m s t \<Longrightarrow> rrsteps_n R n t u \<Longrightarrow> rrsteps_n R (m + n) s u"

lemma rrsteps_n_refl [intro, simp]:
  "rrsteps_n R 0 t t" by (auto intro: rrsteps_n.intros)

lemma rsteps_imp_rrsteps_n:
  assumes "(s, t) \<in> (rstep R)\<^sup>*"
  shows "\<exists>n. rrsteps_n R n s t"
using assms
proof (induct)
  case (step t u)
  then show ?case
    by (auto elim: rstep_cases dest: rrsteps_n.trans [OF _ rrstep] rrsteps_n.trans [OF _ nrrsteps])
qed auto

locale reachability_decomposition =
  fixes R and S
  assumes S_substs: "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> S \<Longrightarrow> (s, t) \<in> S"
    and not_S_imp_nrrsteps: "(s, t) \<notin> S \<Longrightarrow> (s, t) \<in> (rstep R)\<^sup>* \<Longrightarrow> (s, t) \<in> (nrrstep R)\<^sup>*"
begin

abbreviation S_op (infix "\<sqsupset>" 50)
  where
    "x \<sqsupset> y \<equiv> (x, y) \<in> S"

fun reach_decomp :: "_"
and reach_decomps :: "_"
where
  "reach_decomp (Fun f ss) (Fun g ts) =
    (if f = g \<and> length ss = length ts \<and> \<not> Fun f ss \<sqsupset> Fun g ts then reach_decomps ss ts
    else [(Fun f ss, Fun g ts)])"
| "reach_decomp s t = [(s, t)]"
| "reach_decomps [] ts = []"
| "reach_decomps ss [] = []"
| "reach_decomps (s#ss) (t#ts) = reach_decomp s t @ reach_decomps ss ts"

fun reach_decomp' :: "_"
where
  "reach_decomp' (Fun f ss, Fun g ts) =
    (if f = g \<and> length ss = length ts \<and> \<not> Fun f ss \<sqsupset> Fun g ts then concat (map reach_decomp' (zip ss ts))
    else [(Fun f ss, Fun g ts)])"
| "reach_decomp' (s, t) = [(s, t)]"

lemma reach_decomp_reach_decomp'_conv:
  shows "reach_decomp s t = reach_decomp' (s, t)"
    and "length ss = length ts \<Longrightarrow> reach_decomps ss ts = concat (map reach_decomp' (zip ss ts))"
  by (induct s t and ss ts rule: reach_decomp_reach_decomps.induct) auto

lemma reach_decomp_supteq:
  assumes "(u, v) \<in> set (reach_decomp s t)"
  shows "s \<unrhd> u \<and> t \<unrhd> v"
  using assms [unfolded reach_decomp_reach_decomp'_conv]
  apply (induct "(s, t)" arbitrary: s t u v rule: reach_decomp'.induct)
    apply (auto split: if_splits)
   apply (meson Fun_supteq in_set_zipE)+
  done

lemma
  shows reach_decomp_subst:
    "reach_decomp (s \<cdot> \<sigma>) (t \<cdot> \<tau>) =
      concat (map (case_prod reach_decomp) (map (\<lambda>(s, t). (s \<cdot> \<sigma>, t \<cdot> \<tau>)) (reach_decomp s t)))"
    and reach_decomps_subst:
    "reach_decomps (map (\<lambda>t. t \<cdot> \<sigma>) ss) (map (\<lambda>t. t \<cdot> \<tau>) ts) =
      concat (map (case_prod reach_decomp) (map (\<lambda>(s, t). (s \<cdot> \<sigma>, t \<cdot> \<tau>)) (reach_decomps ss ts)))"
apply (induct s t and ss ts rule: reach_decomp_reach_decomps.induct)
apply auto
using S_substs [of "Fun f ss" \<sigma> "Fun g ts" \<tau> for f g ss ts, simplified]
apply blast
done

lemma
  shows rsteps_imp_reach_decomp_rsteps:
    "(s, t) \<in> (rstep R)\<^sup>* \<Longrightarrow> \<forall>(u, v) \<in> set (reach_decomp s t). (u, v) \<in> (rstep R)\<^sup>*"
    and rsteps_imp_reach_decomps_rsteps:
    "length ss = length ts \<Longrightarrow> \<forall>i<length ts. (ss ! i, ts ! i) \<in> (rstep R)\<^sup>* \<Longrightarrow>
      \<forall>(u, v) \<in> set (reach_decomps ss ts). (u, v) \<in> (rstep R)\<^sup>*"
apply (induct s t and ss ts rule: reach_decomp_reach_decomps.induct)
apply simp
apply (auto simp: all_set_conv_all_nth)[1]
apply (drule not_S_imp_nrrsteps, assumption)
apply (metis nrrsteps_imp_arg_rsteps term.sel(4))
apply simp
apply simp
apply simp
apply simp
apply (simp add: all_set_conv_all_nth del: set_append)
apply auto
apply (case_tac "i < length (reach_decomp s t)")
apply (auto simp: nth_append)
by (metis (no_types, opaque_lifting) Suc_less_eq2 add_diff_inverse_nat nat_add_left_cancel_less nth_Cons_Suc)

lemma
  shows reach_decomp_rsteps_imp_rsteps:
    "\<forall>(u, v) \<in> set (reach_decomp s t). (u, v) \<in> (rstep R)\<^sup>* \<Longrightarrow> (s, t) \<in> (rstep R)\<^sup>*"
    and reach_decomps_rsteps_imp_rsteps:
    "length ss = length ts \<Longrightarrow> \<forall>(u, v) \<in> set (reach_decomps ss ts). (u, v) \<in> (rstep R)\<^sup>* \<Longrightarrow>
      \<forall>i<length ts. (ss ! i, ts ! i) \<in> (rstep R)\<^sup>*"
apply (induct s t and ss ts rule: reach_decomp_reach_decomps.induct)
apply (auto simp: args_rsteps_imp_rsteps split: if_splits)
apply (case_tac i; simp)
done

lemma reach_decomp_sound:
  assumes "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  shows "\<forall>(u, v) \<in> set (reach_decomp s t). (u \<cdot> \<sigma>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
proof -
  from rsteps_imp_reach_decomp_rsteps [OF assms, unfolded reach_decomp_subst]
    have "\<forall>(u, v) \<in> set (reach_decomp s t). \<forall>(u', v') \<in> set (reach_decomp (u \<cdot> \<sigma>) (v \<cdot> \<tau>)). (u', v') \<in> (rstep R)\<^sup>*"
    by auto
  with reach_decomp_rsteps_imp_rsteps show ?thesis by blast
qed

lemma nonreach:
  assumes "(f, length ss) \<noteq> (g, length ts)"
    and "\<not> Fun f ss \<sqsupset> Fun g ts" (is "\<not> ?s \<sqsupset> ?t")
    and "(Fun f ss \<cdot> \<sigma>, Fun g ts \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  shows False
proof -
  have "\<not> ?s \<cdot> \<sigma> \<sqsupset> ?t \<cdot> \<tau>" using \<open>\<not> ?s \<sqsupset> ?t\<close> using S_substs by blast
  from not_S_imp_nrrsteps [OF this assms(3)]
  have "(?s \<cdot> \<sigma>, ?t \<cdot> \<tau>) \<in> (nrrstep R)\<^sup>*" .
  from nrrsteps_imp_eq_root_arg_rsteps [OF this] and assms
  show False by simp
qed

end

lemma reachability_decomposition_Int:
  assumes "reachability_decomposition R A"
    and "reachability_decomposition R B"
  shows "reachability_decomposition R (A \<inter> B)"
proof -
  interpret A: reachability_decomposition R A by fact
  interpret B: reachability_decomposition R B by fact
  show ?thesis
    by (standard) (auto dest: "A.not_S_imp_nrrsteps" "B.not_S_imp_nrrsteps" A.S_substs B.S_substs)
qed

lemma rrsteps_n_0:
  assumes "rrsteps_n R 0 s t"
  shows "root s = root t \<and> (s, t) \<in> (nrrstep R)\<^sup>*"
using assms by (induct "0::nat" s t) (auto dest: nrrsteps_imp_eq_root_arg_rsteps)


subsection \<open>Tcap\<close>

lemma rrsteps_n_match_tcap:
  assumes "rrsteps_n R (Suc n) s t"
  shows "\<exists>(l, r) \<in> R. Ground_Context.match (tcap R s) l"
proof -
  have "\<exists>u v. (s, u) \<in> (nrrstep R)\<^sup>* \<and> (u, v) \<in> rrstep R"
    using assms
    apply (induct "Suc n" s t arbitrary: n)
    apply auto
    apply (case_tac m; case_tac n)
    apply (auto dest!: rrsteps_n_0)
    by (metis rtrancl_trans)
  then obtain u v where "(s, u) \<in> (nrrstep R)\<^sup>*" and rrstep: "(u, v) \<in> rrstep R" by blast
  with tcap_sound [of _ Var, simplified, OF nrrsteps_imp_rsteps]
    have "u \<in> equiv_class (tcap R s)" by auto
  moreover obtain l r \<sigma> where "(l, r) \<in> R" and "l \<cdot> \<sigma> = u" using rrstep by (auto elim: rrstepE)
  ultimately show ?thesis by (auto simp: Ground_Context.match_def)
qed

lemma tcap_substs:
  "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> {(s, t). \<exists>(l, r)\<in>R. Ground_Context.match (tcap R s) l} \<Longrightarrow>
    (s, t) \<in> {(s, t). \<exists>(l, r)\<in>R. Ground_Context.match (tcap R s) l}"
  apply (auto simp:)[1]
  apply (rule_tac x = "(a, b)" in bexI)
   apply (auto simp add: Ground_Context.match_def)[1]
   apply (metis subsetCE tcap_instance_subset)
  apply (auto)
  done

lemma rd_tcap:
  "reachability_decomposition R {(s, t). \<exists>(l, r) \<in> R. Ground_Context.match (tcap R s) l}"
  apply (standard)
    apply (rule tcap_substs, assumption)
apply (auto dest!: rsteps_imp_rrsteps_n)
apply (case_tac n)
apply (auto dest: rrsteps_n_0 rrsteps_n_match_tcap)
done


subsection \<open>Root symbols\<close>

definition GT1 :: "_"
where
  "GT1 R = {(x, y). \<exists>(l, r)\<in>R. root l = x \<and> root r = y}"

definition "GT R \<equiv>
  {(s, t). is_Var s \<or> is_Var t \<or>
    (root s, root t) \<in> (GT1 R)\<^sup>+ \<or> (root s, None) \<in> (GT1 R)\<^sup>+
    \<or> (None, root t) \<in> (GT1 R)\<^sup>+ \<or> (None, None) \<in> (GT1 R)\<^sup>+}"

lemma GT1_substs:
  "(root (s \<cdot> \<sigma>), root (t \<cdot> \<tau>)) \<in> GT1 R \<Longrightarrow> is_Var s \<or> is_Var t \<or> (root s, root t) \<in> GT1 R"
by (cases s; cases t) (auto simp: GT1_def)

lemma Ex_term_with_root:
  "\<exists>t::('f, 'v) term. x = root t"
proof (cases x)
  let ?x = "Var (SOME x. True) :: ('f, 'v) term"
  case None
  then show ?thesis by (intro exI [of _ ?x]) auto
next
  case (Some fn)
  moreover then obtain f and ts :: "('f, 'v) term list" where "f = fst fn" and "length ts = snd fn"
    using Ex_list_of_length by blast
  ultimately show ?thesis by (intro exI [of _ "Fun f ts"]) auto
qed

lemma is_Fun_root_subst:
  "is_Fun t \<Longrightarrow> root (t \<cdot> \<sigma>) = root t"
by (cases t) auto

lemma GT_substs:
  fixes \<sigma> \<tau> :: "('f, 'v) subst"
  assumes "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> GT R"
  shows "(s, t) \<in> GT R"
proof -
  consider "is_Var (s \<cdot> \<sigma>)" | "is_Var (t \<cdot> \<tau>)"
    | "(root (s \<cdot> \<sigma>), root (t \<cdot> \<tau>)) \<in> (GT1 R)\<^sup>+"
    | "(root (s \<cdot> \<sigma>), None) \<in> (GT1 R)\<^sup>+"
    | "(None, root (t \<cdot> \<tau>)) \<in> (GT1 R)\<^sup>+"
    | "(None, None) \<in> (GT1 R)\<^sup>+"
    using assms by (auto simp: GT_def)
  then show ?thesis
  proof (cases)
    case 3
    then show ?thesis
    proof (induct "root (s \<cdot> \<sigma>)" "root (t \<cdot> \<tau>)" arbitrary: t \<tau> rule: trancl.induct)
      case IH: (trancl_into_trancl x)
      moreover obtain u :: "('f, 'v) term" where [simp]: "x = root u"
        using Ex_term_with_root [of x] by blast
      moreover have "x = root (u \<cdot> Var)" by simp
      ultimately have "(s, u) \<in> GT R" by blast
      moreover have "(root u, root (t \<cdot> \<tau>)) \<in> GT1 R" using IH by auto
      ultimately show ?case by (auto simp: GT_def is_Fun_root_subst dest: trancl_into_trancl)
    qed (auto simp: GT_def dest: GT1_substs)
  qed (auto simp: GT_def)
qed

lemma rrstep_GT1:
  assumes "(s, t) \<in> rrstep R"
  shows "(root s, root t) \<in> GT1 R \<or> (root s, None) \<in> GT1 R \<or> (None, root t) \<in> GT1 R \<or> (None, None) \<in> GT1 R"
using assms
proof (rule rrstepE)
  fix \<sigma> l r assume "(l, r) \<in> R" and "s = l \<cdot> \<sigma>" and "t = r \<cdot> \<sigma>"
  then show ?thesis by (cases l; cases r) (force simp: GT1_def)+
qed

lemma rrsteps_n_Suc_trancl_GT1:
  assumes "rrsteps_n R (Suc n) s t"
  shows "(root s, root t) \<in> (GT1 R)\<^sup>+ \<or> (root s, None) \<in> (GT1 R)\<^sup>+
    \<or> (None, root t) \<in> (GT1 R)\<^sup>+ \<or> (None, None) \<in> (GT1 R)\<^sup>+"
  using assms
  apply (induct "Suc n" s t arbitrary: n)
  subgoal by (force dest: rrstep_GT1)
  subgoal for m s t n
    apply (case_tac m; case_tac n)
       apply force
      apply (metis rrsteps_n_0)
     apply (metis rrsteps_n_0)
    by (metis trancl_trans)
  done

lemma rrsteps_n_Suc_GT:
  assumes "rrsteps_n R (Suc n) s t"
  shows "(s, t) \<in> GT R"
using assms by (auto dest: rrsteps_n_Suc_trancl_GT1 simp: GT_def)

lemma not_GT_rsteps_imp_nrrsteps:
  assumes "(s, t) \<notin> GT R" and "(s, t) \<in> (rstep R)\<^sup>*"
  shows "(s, t) \<in> (nrrstep R)\<^sup>*"
proof -
  obtain n where "rrsteps_n R n s t" using assms by (auto dest: rsteps_imp_rrsteps_n)
  then show ?thesis
    using assms by (cases n) (auto dest: rrsteps_n_0 rrsteps_n_Suc_GT nrrsteps_imp_arg_rsteps)
qed

abbreviation "GE R \<equiv> {(s, t). root s = root t} \<union> GT R"

lemma rsteps_GE:
  assumes "(s, t) \<in> (rstep R)\<^sup>*"
  shows "(s, t) \<in> GE R"
using assms
by (auto dest: not_GT_rsteps_imp_nrrsteps nrrsteps_imp_eq_root_arg_rsteps)

lemma rd_root: "reachability_decomposition R (GT R)"
  by (standard) (blast intro: GT_substs not_GT_rsteps_imp_nrrsteps)+


context
  fixes R :: "('f, 'v) trs"
  assumes var: "\<forall>(l, r)\<in>R. is_Fun l"
begin

lemma Var_NF:
  "Var x \<in> NF (rstep R)"
  using var by (metis (no_types, lifting) NF_Var_is_Fun NF_terms_lhss case_prod_unfold imageE)

lemma None_GT1_leftD:
  "(None, y) \<in> GT1 R \<Longrightarrow> False"
  using var by (force simp: GT1_def)

lemma None_trancl_GT1_leftD:
  assumes "(None, t) \<in> (GT1 R)\<^sup>+"
  shows False
  using assms by (induct) (auto dest: None_GT1_leftD)

lemma varcond_GT_iff:
  "(s, t) \<in> GT R \<longleftrightarrow> is_Var s \<or> is_Var t \<or> (root s, root t) \<in> (GT1 R)\<^sup>+ \<or> (root s, None) \<in> (GT1 R)\<^sup>+"
  by (auto simp: GT_def dest: None_trancl_GT1_leftD)

end

context reachability_decomposition
begin

lemma nonlinear_var_nonreach:
  fixes s t :: "('a, 'b) term"
  defines "rs \<equiv> reach_decomp s t"
  assumes F: "funas_trs R \<subseteq> F"
    and var: "\<forall>(l, r)\<in>R. is_Fun l"
    and ne: "R \<noteq> {}"
    and Fs: "\<forall>f \<in> F. (Some f, None) \<notin> (GT1 R)\<^sup>+ \<and> (
      \<exists>u. funas_term u \<subseteq> F \<and> (Var x, u) \<in> set rs \<and> is_Fun u \<and> (Some f, root u) \<notin> (GT1 R)\<^sup>*)"
    and *: "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  shows False
proof -
  have F_ne: "F \<noteq> {}" using ne and F and var by (force simp: funas_defs)
  interpret cleaning_const F "\<lambda>_. Var x" "Var x" by standard simp_all
  let ?\<sigma> = "clean_term \<circ> \<sigma>" and ?\<tau> = "clean_term \<circ> \<tau>"
  show ?thesis
  proof (cases "?\<sigma> x")
    case (Var y)
    with Fs and F_ne obtain f and u where fu: "f \<in> F" "(Some f, None) \<notin> (GT1 R)\<^sup>+"
      "(Var x, u) \<in> set rs" "is_Fun u" "(Some f, root u) \<notin> (GT1 R)\<^sup>*"
      and u: "funas_term u \<subseteq> F" by blast
    from fu and reach_decomp_sound [OF *] have "(\<sigma> x, u \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" by (auto simp: rs_def)
    from rsteps_imp_clean_rsteps [OF F(1) this]
    have "(?\<sigma> x, u \<cdot> ?\<tau>) \<in> (rstep R)\<^sup>*" using u by auto
    then have "u \<cdot> ?\<tau> = Var y"
      using var [THEN Var_NF, of y] unfolding Var by (metis NF_not_suc)
    then have "is_Var u" by (cases u; simp)+
    with Fs show ?thesis using F_ne and fu by auto
  next
    case (Fun f ts)
    then have "(f, length ts) \<in> F" (is "?f \<in> F")
      by auto (metis clean_term.simps(2) clean_term_idemp term.distinct(1))
    with Fs obtain u where fu: "(Some ?f, None) \<notin> (GT1 R)\<^sup>+"
      "(Var x, u) \<in> set rs" "is_Fun u" "(Some ?f, root u) \<notin> (GT1 R)\<^sup>*"
      and u: "funas_term u \<subseteq> F" by auto
    from fu and reach_decomp_sound [OF *] have "(\<sigma> x, u \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" by (auto simp: rs_def)
    from rsteps_imp_clean_rsteps [OF F(1) this]
    have "(?\<sigma> x, u \<cdot> ?\<tau>) \<in> (rstep R)\<^sup>*" using u by auto
    then have "(?\<sigma> x, u \<cdot> ?\<tau>) \<in> GE R" by (blast dest: rsteps_GE)
    then have "(?\<sigma> x, u) \<in> GE R" by (auto simp: GT_def)
    with fu show ?thesis
      unfolding Fun by (auto simp: varcond_GT_iff [OF var] trancl_into_rtrancl)
  qed
qed

end

end
