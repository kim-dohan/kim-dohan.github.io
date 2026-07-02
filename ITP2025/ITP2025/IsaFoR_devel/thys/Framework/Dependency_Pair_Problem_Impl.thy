(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Dependency_Pair_Problem_Impl
imports
  Dependency_Pair_Problem_Spec
  TRS.Q_Restricted_Rewriting_Impl
  TRS.Rule_Map
begin


section \<open>A multi-map based implementation\<close>

type_synonym ('f ,'v) dpp_impl =
  "bool \<times> \<comment> \<open> nfs \<close>
   bool \<times> \<comment> \<open> minimal \<close>
   ('f, 'v) rules \<times> \<comment> \<open>P\<close>
   ('f, 'v) rules \<times> \<comment> \<open>Pw\<close>
   ('f, 'v) term list \<times> \<comment> \<open>Q\<close>
   bool \<times> \<comment> \<open>are the NFs of Q a subset of the NFs of the rules?\<close>
   bool \<times> \<comment> \<open>are the rules in R and Rw collapsing\<close>
   ('f, 'v) rules \<times> \<comment> \<open>rules of R, having variables as lhss\<close>
   ('f, 'v) rules \<times> \<comment> \<open>rules of Rw, having variables as lhss\<close>
   ('f, 'v, bool) rm \<times> \<comment> \<open>the remaining rules in R and Rw\<close>
   ('f, 'v, bool) rm \<times> \<comment> \<open>the reversed rules of R and Rw\<close>
   bool \<comment> \<open> wwf_qtrs Q (R \<union> Rw) \<close>
   \<times> (('f,'v)term \<Rightarrow> bool) \<comment> \<open> is_NF Q \<close>"

fun dpp_impl :: "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f, 'v) dpp" where
  "dpp_impl (nfs, mi, p, pw, q, _, _, vr, vrw, m, _) = (nfs, mi,
    set p, set pw, set q,
    set vr \<union> set (rules_with id m),
    set vrw \<union> set (rules_with Not m))"

fun P_impl :: "('f, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules" where "P_impl (_, _, p, _) = p"
fun Pw_impl :: "('f, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules" where "Pw_impl (_, _, _, pw, _) = pw"
fun Nfs_impl :: "('f, 'v) dpp_impl \<Rightarrow> bool" where "Nfs_impl (nfs, _) = nfs"
fun M_impl :: "('f, 'v) dpp_impl \<Rightarrow> bool" where "M_impl (_, mi, _) = mi"
fun pairs_impl :: "('f, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules" where
  "pairs_impl (_, _, p, pw, _) = p @ pw"
fun Q_impl :: "('f, 'v) dpp_impl \<Rightarrow> ('f, 'v) term list" where "Q_impl (_, _, _, _, q, _) = q"
fun R_impl :: "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules" where
  "R_impl (_, _, _, _, _, _, _, vr, _, m, _) = vr @ rules_with id m"
fun Rw_impl :: "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules" where
  "Rw_impl (_, _, _, _, _, _, _, _, vrw, m, _) = vrw @ rules_with Not m"
fun rules_impl :: "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules" where
  "rules_impl (_, _, _, _, _, _, _, vr, vrw, m, _) = vr @ vrw @ rules m"
fun Q_empty_impl :: "('f, 'v) dpp_impl \<Rightarrow> bool" where
  "Q_empty_impl (_, _, _, _, q, _) = (q = [])"
fun is_QNF_impl :: "('f, 'v) dpp_impl \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "is_QNF_impl (_, _, _, _, _, _, _, _, _, _, _, _, isnf) = isnf"
fun NFQ_subset_NF_rules_impl :: "('f, 'v) dpp_impl \<Rightarrow> bool" where
  "NFQ_subset_NF_rules_impl (_, _, _, _, _, b, _) = b"
fun Wwf_rules_impl :: "('f, 'v) dpp_impl \<Rightarrow> bool" where
  "Wwf_rules_impl (_, _, _, _, _, _, _, _, _, _, _,wwf, _) = wwf"
fun rules_no_left_var_impl :: "('f, 'v) dpp_impl \<Rightarrow> bool" where
  "rules_no_left_var_impl (_, _, _, _, _, _, _, [], [], _) = True"
| "rules_no_left_var_impl _ = False"
fun rules_non_collapsing_impl :: "('f, 'v) dpp_impl \<Rightarrow> bool" where
  "rules_non_collapsing_impl (_, _, _, _, _, _, nc, _) = nc"

fun rules_map_impl :: "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules"
where
  "rules_map_impl (_, _, _, _, _, _, _, _, _, m, _) fn =
    (case rm.lookup fn m of
      None \<Rightarrow> []
    | Some rs \<Rightarrow> map snd rs)"

fun reverse_rules_map_impl :: "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules"
where
  "reverse_rules_map_impl (_, _, _, _, _, _, _, _, _, _, m,_) fn =
    (case rm.lookup fn m of
      None \<Rightarrow> []
    | Some rs \<Rightarrow> map snd rs)"

fun
  delete_P_Pw_impl :: "('f, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp_impl"
where
  "delete_P_Pw_impl (nfs, mi, p, pw, rest) pd pwd =
    (nfs, mi, list_diff p pd, list_diff pw pwd, rest)"

(*fun does not terminate*)
definition
  delete_R_Rw_impl ::
    "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp_impl"
where
  "delete_R_Rw_impl d r rw = (case d of
    (nfs, mi, p, pw, q, nfq, nc, vR, vRw, m, rm,wwf,isnf) \<Rightarrow>
    let
      (vr, r')   = partition (is_Var \<circ> fst) r;
      (vrw, rw') = partition (is_Var \<circ> fst) rw;
      vr'        = list_diff vR vr;
      vrw'       = list_diff vRw vrw;
      m'         = delete_rules True r' (delete_rules False rw' m);
      rm'        = delete_rules True (reverse_rules r) (delete_rules False (reverse_rules rw) rm);
      rs         = vr' @ vrw' @ rules m'
    in
    (nfs, mi, p, pw, q,
     nfq \<or> is_NF_trs_subset isnf rs,
     nc \<or> (\<forall>r \<in> set rs. is_Fun (snd r)),
     vr', vrw', m', rm', wwf \<or> wwf_qtrs_impl isnf rs, isnf))"

definition
  intersect_rules_impl :: "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp_impl"
where
  "intersect_rules_impl d ri = (case d of
    (nfs, mi, p, pw, q, nfq, nc, vR, vRw, m, rm, wwf, isnf) \<Rightarrow>
    let
      (vri, ri') = partition (is_Var \<circ> fst) ri;
      vr'        = list_inter vR vri;
      vrw'       = list_inter vRw vri;
      m'         = intersect_rules ri' m;
      rm'        = intersect_rules (reverse_rules ri) rm;
      rs         = vr' @ vrw' @ rules m'
    in
    (nfs, mi, p, pw, q,
     nfq \<or> is_NF_trs_subset isnf rs,
     nc \<or> (\<forall>r \<in> set rs. is_Fun (snd r)),
     vr', vrw', m', rm', wwf \<or> wwf_qtrs_impl isnf rs, isnf))"

fun
  intersect_pairs_impl :: "('f, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp_impl"
where
  "intersect_pairs_impl (nfs,mi,p, pw, rest) ps = (nfs,mi,list_inter p ps, list_inter pw ps, rest)"

fun
  replace_pair_impl :: "('f, 'v) dpp_impl \<Rightarrow> ('f,'v)rule \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp_impl"
where
  "replace_pair_impl (nfs, mi, p, pw, rest) pair ps =
    (nfs, mi, replace_impl pair ps p, replace_impl pair ps pw, rest)"

definition
  split_pairs_impl ::
    "('f, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
where
  "split_pairs_impl d ps = partition (\<lambda>lr. lr \<in> set ps) (pairs_impl d)"

definition
  split_rules_impl ::
    "('f::compare_order, 'v) dpp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
where
  "split_rules_impl d rs = partition (\<lambda>lr. lr \<in> set rs) (rules_impl d)"

definition
  mk_impl ::
    "bool \<Rightarrow> bool \<Rightarrow> ('f::compare_order, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) term list \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp_impl"
where
  "mk_impl nfs mi p pw q r rw = (
    let
      (vr, r') = partition (is_Var \<circ> fst) r;
      (vrw, rw') = partition (is_Var \<circ> fst) rw;
      rs = r @ rw;
      isnf = is_NF_terms q
    in
    (nfs, mi, p, pw, q,
      is_NF_trs_subset isnf rs,
      (\<forall>r \<in> set rs. is_Fun (snd r)),
      vr,
      vrw,
      insert_rules True r' (insert_rules False rw' (rm.empty ())),
      insert_rules True (reverse_rules r) (insert_rules False (reverse_rules rw) (rm.empty ())),
      wwf_qtrs_impl isnf rs, isnf
      ))"

fun is_dpp :: "('f::compare_order, 'v) dpp_impl \<Rightarrow> bool" where
  "is_dpp (nfs, mi, p, pw, q, qsub, nc, vr, vrw, m, rm, wwf,isnf) \<longleftrightarrow> (
    let r  = vr  @ rules_with id  m in
    let rw = vrw @ rules_with Not m in
    let rs = vr  @ vrw @ rules m in
    (qsub \<longleftrightarrow> NF_terms (set q) \<subseteq> NF_trs (set rs))
    \<and> (nc \<longleftrightarrow> (\<forall>r \<in> set rs. is_Fun (snd r)))
    \<and> set (filter (is_Fun \<circ> snd) r)  = (set (rules_with id rm))\<inverse>
    \<and> set (filter (is_Fun \<circ> snd) rw) = (set (rules_with Not rm))\<inverse>
    \<and> (\<forall>r \<in> set (vr @ vrw). is_Var (fst r))
    \<and> rm_inj m \<and> rm_inj rm
    \<and> (wwf \<longleftrightarrow> wwf_qtrs (set q) (set rs)))
    \<and> (isnf = (\<lambda> t. t \<in> NF_terms (set q)))"

lemma is_dpp_imp_is_Var:
  assumes "is_dpp (nfs, mi, p, pw, q, qsub, nc, vr, vrw, m, rm, wwf,isnf)"
  shows "r \<in> set vr \<Longrightarrow> is_Var (fst r)"
    and "r \<in> set vrw \<Longrightarrow> is_Var (fst r)"
  using assms by simp_all

lemma is_dpp_imp_rule_with_id:
  assumes "is_dpp (nfs, mi, p, pw, q, qsub, nc, vr, vrw, m, rm, wwf,isnf)"
  shows "set (rules_with id rm) = (set (filter (is_Fun \<circ> snd) (vr @ rules_with id m)))\<inverse>"
proof -
  have "set (filter (is_Fun \<circ> snd) (vr @ rules_with id m)) = (set (rules_with id rm))\<inverse>"
    using assms unfolding is_dpp.simps Let_def by blast
  then show ?thesis by simp
qed

lemma is_dpp_imp_rule_with_Not:
  assumes "is_dpp (nfs, mi, p, pw, q, qsub, nc, vr, vrw, m, rm, wwf, isnf)"
  shows "set (rules_with Not rm) = (set (filter (is_Fun \<circ> snd) (vrw @ rules_with Not m)))\<inverse>"
proof -
  have "set (filter (is_Fun \<circ> snd) (vrw @ rules_with Not m)) = (set (rules_with Not rm))\<inverse>"
    using assms unfolding is_dpp.simps Let_def by blast
  then show ?thesis by simp
qed

lemma dpp_impl_sound':
  "dpp_impl d =
    (Nfs_impl d, M_impl d, set (P_impl d), set (Pw_impl d), set (Q_impl d), set (R_impl d), set (Rw_impl d))"
  by (cases d) auto

lemma pairs_impl_sound:
  "set (pairs_impl d) = set (P_impl d) \<union> set (Pw_impl d)"
  by (cases d) simp_all

lemma rules_impl_sound:
  "set (rules_impl d) = set (R_impl d) \<union> set (Rw_impl d)"
  by (cases d) (auto simp: values_rules_with_conv)

lemma rules_no_left_var_impl_sound:
  assumes "is_dpp d"
  shows "rules_no_left_var_impl d \<longleftrightarrow> (\<forall>r \<in> set (rules_impl d). is_Fun (fst r))"
  using assms by (induct rule: rules_no_left_var_impl.induct) (auto)

lemma prod_cases11[case_names fields, cases type]:
  obtains a b c d e f g h i j k where "y = (a, b, c, d, e, f, g, h, i, j, k)"
  by (cases y, case_tac g) blast

lemma prod_induct11[case_names fields, induct type]:
  "(\<And>a b c d e f g h i j k. P (a, b, c, d, e, f, g, h, i, j, k)) \<Longrightarrow> P x"
  by (cases x) blast

lemma prod_cases12[case_names fields, cases type]:
  obtains a b c d e f g h i j k l where "y = (a, b, c, d, e, f, g, h, i, j, k, l)"
  by (cases y, case_tac k) blast

lemma prod_induct12[case_names fields, induct type]:
  "(\<And>a b c d e f g h i j k l. P (a, b, c, d, e, f, g, h, i, j, k, l)) \<Longrightarrow> P x"
  by (cases x) blast

lemma prod_cases13[case_names fields, cases type]:
  obtains a b c d e f g h i j k l m where "y = (a, b, c, d, e, f, g, h, i, j, k, l, m)"
  by (cases y, case_tac l) blast

lemma prod_induct13[case_names fields, induct type]:
  "(\<And>a b c d e f g h i j k l m. P (a, b, c, d, e, f, g, h, i, j, k, l, m)) \<Longrightarrow> P x"
  by (cases x) blast

lemma rules_non_collapsing_impl_sound:
  assumes "is_dpp d"
  shows "rules_non_collapsing_impl d \<longleftrightarrow> (\<forall>r \<in> set (rules_impl d). is_Fun (snd r))"
  using assms by (cases d) simp
  
lemma Q_empty_impl_sound:
  "Q_empty_impl d \<longleftrightarrow> set (Q_impl d) = {}"
  by (cases d) simp

lemma is_QNF_impl_sound:
  assumes "is_dpp d"
  shows "is_QNF_impl d = (\<lambda>t. t \<in> NF_terms (set (Q_impl d)))"
  using assms by (cases d) simp

lemma NFQ_subset_NF_rules_impl_sound:
  assumes "is_dpp d"
  shows "NFQ_subset_NF_rules_impl d
    \<longleftrightarrow> NF_terms (set (Q_impl d)) \<subseteq> NF_trs (set (R_impl d) \<union> set (Rw_impl d))"
  using assms by (cases d) (simp add: values_rules_with_conv Un_ac)

lemma Wwf_rules_impl_sound:
  assumes "is_dpp d"
  shows "Wwf_rules_impl d
    \<longleftrightarrow> wwf_qtrs (set (Q_impl d)) (set (R_impl d) \<union> set (Rw_impl d))"
  using assms by (cases d) (simp add: values_rules_with_conv Un_ac)

lemma mk_impl_sound:
  "dpp_impl (mk_impl nfs mi p pw q r rw) = (nfs, mi, set p, set pw, set q, set r, set rw)"
  by (auto simp: mk_impl_def Let_def)

lemma is_Var_aux:
  fixes R::"('f, 'v) trs"
  assumes "\<forall>r\<in>R. is_Var (fst r)" and "S \<subseteq> R" and "(Fun f ts, r) \<in> S"
  shows "False"
proof -
  from assms have "(Fun f ts, r) \<in> R" by blast
  with assms have "is_Var (Fun f ts)" by auto
  then show False by simp
qed

lemma rules_delete_rules_rules_with_conv:
  fixes m and r and rw
  defines [simp]: "m' \<equiv> delete_rules True r (delete_rules False rw m)"
  assumes rm_inj: "rm_inj m"
  shows "set (rules m') =
    (set (rules_with id m) - set r) \<union> (set (rules_with Not m) - set rw)"
proof -
  have rm_inj': "rm_inj (delete_rules False rw m)"
    using rm_inj_delete_rules[OF rm_inj] by blast

  have vals: "set (values m') = set (values m) - Pair False ` set rw - Pair True ` set r"
    unfolding m'_def
    unfolding values_delete_rules[OF rm_inj']
    unfolding values_delete_rules[OF rm_inj] ..
  then have "snd ` set (values m') =
    snd ` (set (values m) - Pair False ` set rw - Pair True ` set r)" by simp
  then have 1: "set (Rule_Map.rules m') =
    snd ` (set (values m) - Pair False ` set rw - Pair True ` set r)" by simp
  then show ?thesis
    unfolding 1 rules_with_def by force
qed

lemma rules_intersect_rules_rules_with_conv:
  fixes m and r and rw
  defines [simp]: "m' \<equiv> intersect_rules r m"
  assumes rm_inj: "rm_inj m"
  shows "set (rules m') =
    (set (rules_with id m) \<inter> set r) \<union> (set (rules_with Not m) \<inter> set r)"
proof -
  have vals: "set (values m') = set (values m) \<inter> (Pair True ` set r \<union> Pair False ` set r)"
    unfolding m'_def
    unfolding values_intersect_rules[OF rm_inj] ..
  then have "snd ` set (values m') =
    snd ` (set (values m) \<inter> (Pair True ` set r \<union> Pair False ` set r))" (is "_ = ?r") by simp
  then have 1: "set (Rule_Map.rules m') = ?r" by simp
  show ?thesis unfolding 1 rules_with_def by force
qed

lemma rules_map_impl_sound:
  assumes "is_dpp d"
  shows "set (rules_map_impl d (f, n)) =
    {r |r. r \<in> set (rules_impl d) \<and> root (fst r) = Some (f, n)}"
    (is "?A = ?B")
proof (cases d)
  case (fields nfs mi p pw q qsub nc vr vrw m rm wwf)
  show ?thesis
  proof
    show "?A \<subseteq> ?B"
    proof
      fix l r assume 1: "(l, r) \<in> set (rules_map_impl d (f, n))"
      show "(l, r) \<in> ?B"
      proof (cases "rm.lookup (f, n) m")
        case None with 1 show ?thesis by (simp add: fields)
      next
        case (Some rs)
        with 1 have 2: "(l, r) \<in> snd `set rs" by (simp add: fields)
        from assms and Some have "\<forall>r\<in>set rs. key r = Some (f, n)"
          by (simp add: fields rm_inj_def mmap_inj_def rm.correct)
        moreover from 2 obtain a where "(a, l, r) \<in> set rs" by auto
        ultimately have "key (a, l, r) = Some (f, n)" by simp
        then have root: "root l = Some (f, n)"
          by (cases l, simp_all)
        from Some_in_values[OF Some] have "set rs \<subseteq> set (values m)" .
        then have "(l, r) \<in> snd ` set (values m)" using 2 by auto
        then have "(l, r) \<in> set (rules_impl d)"
          by (auto simp: fields values_rules_with_conv)
        with root show ?thesis by simp
      qed
    qed
  next
    show "?B \<subseteq> ?A"
    proof
      fix l r assume "(l, r) \<in> ?B"
      then have "(l, r) \<in> set (rules_impl d)"
        and "root l = Some (f, n)" by auto
      then have "(l, r) \<in> set (R_impl d) \<union> set (Rw_impl d)" by (simp add: rules_impl_sound)
      then have 1: "(l, r) \<in> set (rules_impl d)"
        by (auto simp: fields values_rules_with_conv)
      from \<open>root l = Some (f, n)\<close> obtain ts where l: "l = Fun f ts" by (cases l) auto
      have "(l, r) \<in> set (rules m)"
        using 1 and is_dpp_imp_is_Var [OF assms [unfolded fields], of "(l, r)"]
          by (auto simp add: l fields)
      then obtain a where "(a, l, r) \<in> set (values m)" by auto
      from this[unfolded values_ran[unfolded ran_def]]
        obtain k vs where lookup: "rm.lookup k m = Some vs"
        and "(a, l, r) \<in> set vs" by (auto simp: rm.correct)
      then have 2: "(l, r) \<in> set (rules_map_impl d k)" unfolding fields by force
      have k: "k = (f, n)"
      proof -
        from \<open>root l = Some (f, n)\<close> have "length ts = n" by (simp add: l)
        from lookup have alpha: "rm.\<alpha> m k = Some vs" by (auto simp: rm.correct)
        from assms[unfolded fields, simplified, THEN conjunct2, THEN conjunct2,
          unfolded rm_inj_def mmap_inj_def]          
          and alpha and \<open>(a, l, r) \<in> set vs\<close> have "key (a, l, r) = Some k" 
          by blast
        then show ?thesis by (simp add: \<open>length ts = n\<close> l)
      qed
      from 2 show "(l, r) \<in> ?A" unfolding k .
    qed
  qed
qed

lemma intersect_pairs_impl_sound:
  "dpp_impl (intersect_pairs_impl d ps) =
    (Nfs_impl d, M_impl d, set (P_impl d) \<inter> set ps, set (Pw_impl d) \<inter> set ps, set (Q_impl d),
     set (R_impl d), set (Rw_impl d))"
  by (cases d) simp

lemma replace_pair_impl_sound:
  "dpp_impl (replace_pair_impl d pair ps) =
    (Nfs_impl d, M_impl d, replace pair (set ps) (set (P_impl d)), replace pair (set ps) (set (Pw_impl d)), set (Q_impl d),
     set (R_impl d), set (Rw_impl d))"
  by (cases d) simp

lemma is_Var_aux':
  fixes R::"('f, 'v) trs"
  assumes "\<forall>r\<in>R. is_Var (snd r)" and "S \<subseteq> R" and "(l, Fun f ts) \<in> S"
  shows "False"
proof -
  from assms have "(l, Fun f ts) \<in> R" by blast
  with assms have "is_Var (Fun f ts)" by auto
  then show False by simp
qed

lemma reverse_rules_map_impl_sound:
  assumes "is_dpp d"
  shows "set (reverse_rules_map_impl d (f, n)) =
    {(snd r, fst r) | r. r \<in> set (rules_impl d) \<and> root (snd r) = Some (f, n)}"
    (is "?A = ?B")
proof (cases d)
  case (fields nfs mi p pw q qsub nc vr vrw m rm wwf)
  show ?thesis
  proof
    show "?A \<subseteq> ?B"
    proof
      fix r l assume 1: "(r, l) \<in> set (reverse_rules_map_impl d (f, n))"
      show "(r, l) \<in> ?B"
      proof (cases "rm.lookup (f, n) rm")
        case None with 1 show ?thesis by (simp add: fields)
      next
        case (Some rs)
        with 1 have 2: "(r, l) \<in> snd `set rs" by (simp add: fields)
        from assms and Some have "\<forall>r\<in>set rs. key r = Some (f, n)"
          by (simp add: fields rm_inj_def mmap_inj_def rm.correct)
        moreover from 2 obtain a where "(a, r, l) \<in> set rs" by auto
        ultimately have "key (a, r, l) = Some (f, n)" by simp
        then have root: "root r = Some (f, n)"
          by (cases r, simp_all)
        from Some_in_values[OF Some] have "set rs \<subseteq> set (values rm)" .
        then have "(r, l) \<in> snd ` set (values rm)" using 2 by auto
        with assms[unfolded fields, simplified,
          THEN conjunct2, THEN conjunct2]
          have "(l, r) \<in> set (rules_impl d)"
          by (auto simp: fields values_rules_with_conv)
        with root show ?thesis by simp
      qed
    qed
  next
    show "?B \<subseteq> ?A"
    proof
      fix r l assume "(r, l) \<in> ?B"
      then have "(l, r) \<in> set (rules_impl d)"
        and "root r = Some (f, n)" by auto
      then have "(l, r) \<in> set (R_impl d) \<union> set (Rw_impl d)" by (simp add: rules_impl_sound)
      then have 1: "(l, r) \<in> set (rules_impl d)"
        by (auto simp: fields values_rules_with_conv)
      from \<open>root r = Some (f, n)\<close> obtain ts where r: "r = Fun f ts" by (cases r) auto
      
      have "(r, l) \<in> set (rules rm)"
        using 1 and is_dpp_imp_is_Var [OF assms [unfolded fields], of "(r, l)"]
        and is_dpp_imp_rule_with_id [OF assms [unfolded fields]]
        and is_dpp_imp_rule_with_Not [OF assms [unfolded fields]]
        by (simp add: fields values_rules_with_conv r) blast
      then obtain a where "(a, r, l) \<in> set (values rm)" by auto
      from this[unfolded values_ran[unfolded ran_def]]
        obtain k vs where lookup: "rm.lookup k rm = Some vs"
        and "(a, r, l) \<in> set vs" by (auto simp: rm.correct)
      then have 2: "(r, l) \<in> set (reverse_rules_map_impl d k)" unfolding fields by force
      have k: "k = (f, n)"
      proof -
        from \<open>root r = Some (f, n)\<close> have "length ts = n" by (simp add: r)
        from lookup have alpha: "rm.\<alpha> rm k = Some vs" by (simp add: rm.correct)
        from assms have "rm_inj rm" using assms by (simp add: fields)
        from this[unfolded rm_inj_def mmap_inj_def]
          and alpha and \<open>(a, r, l) \<in> set vs\<close>
          have "key (a, r, l) = Some k" by blast
        then show ?thesis by (simp add: \<open>length ts = n\<close> r)
      qed
      from 2 show "(r, l) \<in> ?A" unfolding k .
    qed
  qed
qed

lemma delete_P_Pw_impl_sound:
  "dpp_impl (delete_P_Pw_impl d p pw) =
    (Nfs_impl d, M_impl d, set (P_impl d) - set p, set (Pw_impl d) - set pw, set (Q_impl d),
     set (R_impl d), set (Rw_impl d))"
  by (cases d) simp

lemma intersect_rules_impl_sound:
  assumes "is_dpp d"
  shows "dpp_impl (intersect_rules_impl d r) =
    (Nfs_impl d, M_impl d, set (P_impl d), set (Pw_impl d), set (Q_impl d),
     set (R_impl d) \<inter> set r, set (Rw_impl d) \<inter> set r)"
proof (cases d)
  case (fields nfs mi p pw q qsub nc vr vrw m rm wwf)
  from assms have inj: "rm_inj m" by (simp add: fields)
  from assms have vars: "\<forall>r \<in> set vr \<union> set vrw. is_Var (fst r)" by (simp add: fields)
  from assms have vars2: "\<forall>(l,r) \<in> snd ` set (values m). is_Fun l" by (force simp: fields)
  from vars vars2 show ?thesis
    unfolding intersect_rules_impl_def fields Let_def rules_with_def o_def split dpp_impl.simps
    by (simp add: rules_with_id_intersect_rules[OF inj] rules_with_Not_intersect_rules[OF inj], 
        unfold values_rules_with_conv, auto) 
qed

lemma delete_R_Rw_impl_sound:
  assumes "is_dpp d"
  shows "dpp_impl (delete_R_Rw_impl d r rw) =
    (Nfs_impl d, M_impl d, set (P_impl d), set (Pw_impl d), set (Q_impl d),
     set (R_impl d) - set r, set (Rw_impl d) - set rw)"
proof (cases d)
  case (fields nfs mi p pw q qsub nc vr vrw m rm wwf)
  from assms have inj: "rm_inj m" by (simp add: fields)
  from rm_inj_delete_rules[OF this]
    have inj': "rm_inj (delete_rules False [x\<leftarrow>rw . is_Fun (fst x)] m)" .
  from assms have vars: "\<forall>r \<in> set vr \<union> set vrw. is_Var (fst r)" by (simp add: fields)
  show ?thesis
    using inj and vars
    by (simp add: delete_R_Rw_impl_def
                  fields dpp_impl_sound' Let_def rules_with_def o_def
                  values_delete_rules[OF inj']
                  values_delete_rules[OF inj])
        auto
qed

lemma split_pairs_impl_sound:
  assumes "split_pairs_impl d ps = (p, p')"
  shows "set p = set (pairs_impl d) \<inter> set ps \<and> set p' = set (pairs_impl d) - set ps"
  using assms
  unfolding split_pairs_impl_def by auto

lemma split_rules_impl_sound:
  assumes "split_rules_impl d rs = (r, r')"
  shows "set r = set (rules_impl d) \<inter> set rs \<and>
    set r' = set (rules_impl d) - set rs"
proof (cases d)
  case (fields nfs mi p pw q qsub nc vr vrw m rm wwf)
  from assms have r: "r =
    [lr\<leftarrow>vr . lr \<in> set rs] @ [lr\<leftarrow>vrw . lr \<in> set rs] @ [lr\<leftarrow>rules m . lr \<in> set rs]"
    and r': "r' =
    [x\<leftarrow>vr . x \<notin> set rs] @ [x\<leftarrow>vrw . x \<notin> set rs] @ [x\<leftarrow>rules m . x \<notin> set rs]"
    by (simp_all add: split_rules_impl_def o_def fields)
  show ?thesis
    by (auto simp: fields r r' o_def values_rules_with_conv)
qed

lemmas dpp_impl_sound =
  dpp_impl_sound'
  pairs_impl_sound
  rules_impl_sound
  Q_empty_impl_sound
  rules_no_left_var_impl_sound
  rules_non_collapsing_impl_sound
  is_QNF_impl_sound
  NFQ_subset_NF_rules_impl_sound
  intersect_pairs_impl_sound
  replace_pair_impl_sound
  intersect_rules_impl_sound
  rules_map_impl_sound
  reverse_rules_map_impl_sound
  delete_P_Pw_impl_sound
  delete_R_Rw_impl_sound
  split_pairs_impl_sound
  split_rules_impl_sound
  mk_impl_sound

section \<open>Invariant free implementation\<close>

context
  notes [[typedef_overloaded]]
begin
typedef ('f, 'v) dpp = "{d :: ('f::compare_order, 'v) dpp_impl. is_dpp d}"
  morphisms impl_of DPP
proof -
  have "mk_impl False False [] [] [] [] [] \<in> ?dpp"
    by (simp add: mk_impl_def Let_def insert_rules_def reverse_rules_def del: Id_on_empty)
  then show ?thesis ..
qed
end

definition dpp :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) QDP_Framework.dpp" where
  "dpp d = dpp_impl (impl_of d)"

definition P :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules" where
  "P d = P_impl (impl_of d)"

definition Pw :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules" where
  "Pw d = Pw_impl (impl_of d)"

definition pairs :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules" where
  "pairs d = pairs_impl (impl_of d)"

definition Q :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) term list" where
  "Q d = Q_impl (impl_of d)"

definition R :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules" where
  "R d = R_impl (impl_of d)"

definition Rw :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules" where
  "Rw d = Rw_impl (impl_of d)"

definition Nfs :: "('f::compare_order, 'v) dpp \<Rightarrow> bool" where
  "Nfs d = Nfs_impl (impl_of d)"

definition M :: "('f::compare_order, 'v) dpp \<Rightarrow> bool" where
  "M d = M_impl (impl_of d)"

definition rules :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules" where
  "rules d = rules_impl (impl_of d)"

definition Q_empty :: "('f::compare_order, 'v) dpp \<Rightarrow> bool" where
  "Q_empty d = Q_empty_impl (impl_of d)"

definition rules_no_left_var :: "('f::compare_order, 'v) dpp \<Rightarrow> bool" where
  "rules_no_left_var d = rules_no_left_var_impl (impl_of d)"

definition rules_non_collapsing :: "('f::compare_order, 'v) dpp \<Rightarrow> bool" where
  "rules_non_collapsing d = rules_non_collapsing_impl (impl_of d)"

definition is_QNF :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "is_QNF d = is_QNF_impl (impl_of d)"

definition NFQ_subset_NF_rules :: "('f::compare_order, 'v) dpp \<Rightarrow> bool" where
  "NFQ_subset_NF_rules d = NFQ_subset_NF_rules_impl (impl_of d)"

definition Wwf_rules :: "('f::compare_order, 'v) dpp \<Rightarrow> bool" where
  "Wwf_rules d = Wwf_rules_impl (impl_of d)"

definition intersect_pairs :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp" where
  "intersect_pairs d ps = DPP (intersect_pairs_impl (impl_of d) ps)"

definition replace_pair :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f,'v)rule \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp" where
  "replace_pair d pair ps = DPP (replace_pair_impl (impl_of d) pair ps)"

definition intersect_rules :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp" where
  "intersect_rules d rs = DPP (intersect_rules_impl (impl_of d) rs)"

definition rules_map :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules" where
  "rules_map d = rules_map_impl (impl_of d)"

definition reverse_rules_map :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules" where
  "reverse_rules_map d = reverse_rules_map_impl (impl_of d)"

definition
  delete_P_Pw :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp"
where
  "delete_P_Pw d p pw = DPP (delete_P_Pw_impl (impl_of d) p pw)"

definition
  delete_R_Rw :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp"
where
  "delete_R_Rw d r rw = DPP (delete_R_Rw_impl (impl_of d) r rw)"

definition
  split_pairs :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
where
  "split_pairs d = split_pairs_impl (impl_of d)"

definition
  split_rules :: "('f::compare_order, 'v) dpp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
where
  "split_rules d = split_rules_impl (impl_of d)"

definition
  mk :: "bool \<Rightarrow> bool \<Rightarrow> ('f::compare_order, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) term list
    \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) dpp"
where
  "mk nfs mi p pw q r rw = DPP (mk_impl nfs mi p pw q r rw)"

lemma is_dpp_impl_of[simp, intro]: "is_dpp (impl_of d)"
  using impl_of[of d] by simp

lemma DPP_impl_of[simp, code abstype]: "DPP (impl_of d) = d"
  by (rule impl_of_inverse)

lemma impl_of_DPP[simp]: "is_dpp d \<Longrightarrow> impl_of (DPP d) = d" by (simp add: DPP_inverse)


lemma is_dpp_mk_impl [simp, intro]:
  "is_dpp (mk_impl nfs mi p pw q r rw)"
proof -
  let ?vr = "filter (is_Var \<circ> fst) r"
  let ?vrw = "filter (is_Var \<circ> fst) rw"
  let ?r = "filter (Not \<circ> is_Var \<circ> fst) r"
  let ?rw = "filter (Not \<circ> is_Var \<circ> fst) rw"
  let ?m = "insert_rules True ?r (insert_rules False ?rw (rm.empty ()))"
  let ?rs = "r @ rw"
  let ?rs' = "?vr @ ?vrw @ Rule_Map.rules ?m"
  let ?rm = "insert_rules True (reverse_rules r) (insert_rules False (reverse_rules rw) (rm.empty ()))"
  let ?isnf = "is_NF_terms q"

  have eq: "set ?rs' = set ?rs"
    by (auto simp add: insert_rules_def image_Un image_snd_Pair)
  have "?isnf = (\<lambda> t. t \<in> NF_terms (set q))" by simp
  moreover 
  have "is_NF_trs_subset ?isnf ?rs \<longleftrightarrow> NF_terms (set q) \<subseteq> NF_trs (set ?rs')"
    unfolding eq by simp
  moreover
  have "(\<forall>r \<in> set ?rs. is_Fun (snd r)) \<longleftrightarrow> (\<forall>r \<in> set ?rs'. is_Fun (snd r))"
    unfolding eq by (rule refl)
  moreover
  have "wwf_qtrs_impl (is_NF_terms q) ?rs \<longleftrightarrow> wwf_qtrs (set q) (set ?rs')" unfolding eq by simp
  moreover
  have "set (filter (is_Fun \<circ> snd) (?vr @ rules_with id ?m)) = (set (rules_with id ?rm))\<inverse>" by auto
  moreover
  have "set (filter (is_Fun \<circ> snd) (?vrw @ rules_with Not ?m)) =
    (set (rules_with Not ?rm))\<inverse>" by auto
  moreover
  have "\<forall>r \<in> set (?vr @ ?vrw). is_Var (fst r)" by auto
  moreover
  have "rm_inj ?m" by simp
  moreover
  have "rm_inj ?rm"
    using rm_inj_insert_rules[OF rm_inj_insert_rules[OF rm_inj_rm_empty]] by best
  ultimately
  show ?thesis  
    by (simp only: mk_impl_def Let_def case_prod_partition is_dpp.simps o_assoc) 
qed

lemma impl_of_mk [code abstract]:
  "impl_of (mk nfs mi p pw q r rw) = mk_impl nfs mi p pw q r rw"
  by (simp add: mk_def)

lemma is_dpp_delete_P_Pw_impl [simp]:
  "is_dpp d \<Longrightarrow> is_dpp (delete_P_Pw_impl d p pw)"
  by (cases d) simp

lemma inj_on_snd_Pair: "inj_on snd (Pair x ` A)" by (simp add: inj_on_def)

lemma filter_union: "set [x\<leftarrow>xs. p x] \<union> set [x\<leftarrow>xs. \<not> p x] = set xs" by auto

lemma values_bool_cases:
  assumes "(b, l, r) \<in> set (values m)"
  shows "(l, r) \<in> set (rules_with id m) \<or> (l, r) \<in> set (rules_with Not m)"
  using assms unfolding rules_with_def by auto

lemma image_Pair_diff: "(Pair b ` A - Pair b ` B) = Pair b ` (A - B)"
  by auto

lemma is_dpp_delete_R_Rw_impl [simp]:
  assumes "is_dpp d"
  shows "is_dpp (delete_R_Rw_impl d r rw)"
proof (cases d)
  case (fields nfs mi p pw q qsub nc vr vrw m rm wwf isnf)

  let ?vr = "list_diff vr (filter (is_Var \<circ> fst) r)"
  let ?vrw = "list_diff vrw (filter (is_Var \<circ> fst) rw)"
  let ?r = "filter (Not \<circ> is_Var \<circ> fst) r"
  let ?rw = "filter (Not \<circ> is_Var \<circ> fst) rw"
  let ?m = "delete_rules True ?r (delete_rules False ?rw m)"
  let ?rs = "?vr @ ?vrw @ Rule_Map.rules ?m"
  let ?rs' = "vr @ vrw @ Rule_Map.rules m"
  let ?rm = "delete_rules True (reverse_rules r) (delete_rules False (reverse_rules rw) rm)"

  from assms have vars: "\<forall>r \<in> set (vr @ vrw). is_Var (fst r)" by (simp add: fields)
  from assms
    have qsub: "qsub \<longleftrightarrow> NF_terms (set q) \<subseteq> NF_trs (set (vr @ vrw @ Rule_Map.rules m))"
    by (simp add: fields)
  from assms
    have wwf: "wwf \<longleftrightarrow> wwf_qtrs (set q) (set (vr @ vrw @ Rule_Map.rules m))"
    by (simp add: fields)
  from assms
    have isnf: "isnf = (\<lambda> t. t \<in> NF_terms (set q))"
    by (simp add: fields)

  from assms have rm_inj: "rm_inj m" by (simp add: fields)
  then have rm_inj': "rm_inj (delete_rules False ?rw m)" by (rule rm_inj_delete_rules)

  from assms have rm_inj2: "rm_inj rm" by (simp add: fields)
  have rm_inj2': "rm_inj (delete_rules False (reverse_rules rw) rm)"
    using rm_inj_delete_rules[OF rm_inj2] by blast

  have "set (values ?m) \<subseteq> set (values m)" by (auto simp: values_delete_rules rm_inj rm_inj')
  then have subset: "set ?rs \<subseteq> set ?rs'" by auto

  from assms [unfolded fields is_dpp.simps Let_def]
    have maps_r: "set (filter (Not \<circ> is_Var \<circ> snd) (vr @ rules_with id m)) = (set (rules_with id rm))\<inverse>"
    and maps_rw: "set (filter (Not \<circ> is_Var \<circ> snd) (vrw @ rules_with Not m)) =
    (set (rules_with Not rm))\<inverse>"
    by simp_all

  have "set (values ?rm) \<subseteq> set (values rm)"
    unfolding values_delete_rules[OF rm_inj_delete_rules[OF rm_inj2]]
    unfolding values_delete_rules[OF rm_inj2]
    by blast
  then have subset_rm: "set (Rule_Map.rules ?rm) \<subseteq> set (Rule_Map.rules rm)" by auto

  have "qsub \<or> is_NF_trs_subset isnf ?rs
    \<longleftrightarrow> NF_terms (set q) \<subseteq> NF_trs (set ?rs)"
  proof (cases qsub)
    case False
    then show ?thesis unfolding isnf by simp
  next
    case True
    with qsub have "NF_terms (set q) \<subseteq> NF_trs (set (vr @ vrw @ Rule_Map.rules m))" by auto
    also have "... \<subseteq> NF_trs (set ?rs)"
      by (rule NF_trs_mono[OF subset])
    finally show ?thesis using True by simp
  qed
  moreover
  have "wwf \<or> wwf_qtrs_impl isnf ?rs \<longleftrightarrow> wwf_qtrs (set q) (set ?rs)"
  proof (cases wwf)
    case False
    then show ?thesis unfolding isnf by simp
  next
    case True
    with wwf have "wwf_qtrs (set q) (set (vr @ vrw @ Rule_Map.rules m))" by auto
    then have "wwf_qtrs (set q) (set ?rs)" using subset unfolding wwf_qtrs_def by blast
    then show ?thesis using True by simp
  qed
  moreover
  have "isnf = (\<lambda> t. t \<in> NF_terms (set q))" unfolding isnf ..
  moreover
  have "nc \<or> (\<forall>r \<in> set ?rs. is_Fun (snd r)) \<longleftrightarrow> (\<forall>r \<in> set ?rs. is_Fun (snd r))"
  proof -
    from assms have nc: "nc = (\<forall>r \<in> set ?rs'. is_Fun (snd r))" by (simp add: fields)
    from subset show ?thesis unfolding nc by blast
  qed
  moreover
  have "set (filter (is_Fun \<circ> snd) (?vr @ rules_with id ?m)) = (set (rules_with id ?rm))\<inverse>"
  proof -
    have "set (filter (is_Fun \<circ> snd) (?vr @ rules_with id ?m))
      = set (filter (Not \<circ> is_Var \<circ> snd) (vr @ rules_with id m)) - set r"
      unfolding set_filter set_append
      unfolding rules_with_id_delete_rules_True[OF rm_inj']
      unfolding rules_with_id_delete_rules_False[OF \<open>rm_inj m\<close>]
      using vars by (auto intro: in_rules_with_id_is_Var_False[OF \<open>rm_inj m\<close>])
    moreover
    have "(set (rules_with id ?rm))\<inverse> =  (set (rules_with id rm))\<inverse> - set r"
      unfolding rules_with_id_delete_rules_True[OF rm_inj2']
      unfolding rules_with_id_delete_rules_False[OF \<open>rm_inj rm\<close>]
      by auto
    ultimately
    show ?thesis unfolding maps_r by blast
  qed
  moreover
  have "set (filter (is_Fun \<circ> snd) (?vrw @ rules_with Not ?m)) = (set (rules_with Not ?rm))\<inverse>"
  proof -
    have "set (filter (is_Fun \<circ> snd) (?vrw @ rules_with Not ?m))
      = set (filter (Not \<circ> is_Var \<circ> snd) (vrw @ rules_with Not m)) - set rw"
      unfolding set_filter set_append
      unfolding rules_with_Not_delete_rules_True[OF rm_inj']
      unfolding rules_with_Not_delete_rules_False[OF \<open>rm_inj m\<close>]
      using vars by (auto intro: in_rules_with_Not_is_Var_False[OF \<open>rm_inj m\<close>])
    moreover
    have "(set (rules_with Not ?rm))\<inverse>
      =  (set (rules_with Not rm))\<inverse> - set rw"
      unfolding rules_with_Not_delete_rules_True[OF rm_inj2']
      unfolding rules_with_Not_delete_rules_False[OF \<open>rm_inj rm\<close>]
      by auto
    ultimately
    show ?thesis unfolding maps_rw by blast
  qed
  moreover have "\<forall>r \<in> set (?vr @ ?vrw). is_Var (fst r)" using vars by auto
  moreover have "rm_inj ?m" using rm_inj by simp
  moreover have "rm_inj ?rm"
    using rm_inj_delete_rules[OF rm_inj_delete_rules[OF rm_inj2]] by blast
  ultimately
  show ?thesis
    by (simp only:
      fields delete_R_Rw_impl_def case_prod_partition Let_def is_dpp.simps o_assoc split)
qed

lemma is_dpp_intersect_rules_r_impl[simp]:
  assumes "is_dpp d"
  shows "is_dpp (intersect_rules_impl d r)"
proof (cases d)
  case (fields nfs mi p pw q qsub nc vr vrw m rm wwf isnf)

  let ?vr = "list_inter vr (filter (is_Var \<circ> fst) r)"
  let ?vrw = "list_inter vrw (filter (is_Var \<circ> fst) r)"
  let ?r = "filter (Not \<circ> is_Var \<circ> fst) r"
  let ?m = "Rule_Map.intersect_rules ?r m"
  let ?rs = "?vr @ ?vrw @ Rule_Map.rules ?m"
  let ?rs' = "vr @ vrw @ Rule_Map.rules m"
  let ?rm = "Rule_Map.intersect_rules (reverse_rules r) rm"

  from assms have vars: "\<forall>r \<in> set (vr @ vrw). is_Var (fst r)" by (simp add: fields)
  from assms
    have qsub: "qsub \<longleftrightarrow> NF_terms (set q) \<subseteq> NF_trs (set (vr @ vrw @ Rule_Map.rules m))"
    by (simp add: fields)

  from assms
    have wwf: "wwf \<longleftrightarrow> wwf_qtrs (set q) (set (vr @ vrw @ Rule_Map.rules m))"
    by (simp add: fields)
  from assms
    have isnf: "isnf = (\<lambda> t. t \<in> NF_terms (set q))"
    by (simp add: fields)

  from assms have rm_inj: "rm_inj m" by (simp add: fields)

  from assms have rm_inj2: "rm_inj rm" by (simp add: fields)

  have "set (values ?m) \<subseteq> set (values m)" by (auto simp: values_intersect_rules rm_inj)
  then have subset: "set ?rs \<subseteq> set ?rs'" by auto

  from assms [unfolded fields is_dpp.simps Let_def]
    have maps_r: "set (filter (is_Fun \<circ> snd) (vr @ rules_with id m)) =
    (set (rules_with id rm))\<inverse>"
    and maps_rw: "set (filter (is_Fun \<circ> snd) (vrw @ rules_with Not m)) =
     (set (rules_with Not rm))\<inverse>"
    by blast+

  have "set (values ?rm) \<subseteq> set (values rm)"
    unfolding values_intersect_rules[OF rm_inj2] by blast
  then have subset_rm: "set (Rule_Map.rules ?rm) \<subseteq> set (Rule_Map.rules rm)" by auto

  have "qsub \<or> is_NF_trs_subset isnf ?rs \<longleftrightarrow> NF_terms (set q) \<subseteq> NF_trs (set ?rs)"
  proof (cases qsub)
    case False
    then show ?thesis unfolding isnf by simp
  next
    case True
    with qsub have "NF_terms (set q) \<subseteq> NF_trs (set (vr @ vrw @ Rule_Map.rules m))" by auto
    also have "... \<subseteq> NF_trs (set ?rs)"
      by (rule NF_trs_mono[OF subset])
    finally show ?thesis using True by simp
  qed
  moreover
  have "wwf \<or> wwf_qtrs_impl isnf ?rs \<longleftrightarrow> wwf_qtrs (set q) (set ?rs)"
  proof (cases wwf)
    case False
    then show ?thesis unfolding isnf by simp
  next
    case True
    with wwf have "wwf_qtrs (set q) (set (vr @ vrw @ Rule_Map.rules m))" by auto
    then have "wwf_qtrs (set q) (set ?rs)" using subset unfolding wwf_qtrs_def by blast
    then show ?thesis using True by simp
  qed
  moreover
  have "nc \<or> (\<forall>r \<in> set ?rs. is_Fun (snd r)) \<longleftrightarrow> (\<forall>r \<in> set ?rs. is_Fun (snd r))"
  proof -
    from assms have nc: "nc = (\<forall>r \<in> set ?rs'. is_Fun (snd r))" by (simp add: fields)
    from subset show ?thesis unfolding nc by blast
  qed
  moreover
  have "set (filter (is_Fun \<circ> snd) (?vr @ rules_with id ?m)) = (set (rules_with id ?rm))\<inverse>"
  proof -
    have "set (filter (is_Fun \<circ> snd) (?vr @ rules_with id ?m))
      = set (filter (is_Fun \<circ> snd) (vr @ rules_with id m)) \<inter> set r"
      unfolding set_filter set_append
      unfolding rules_with_id_intersect_rules[OF \<open>rm_inj m\<close>]
      using vars by (auto intro: in_rules_with_id_is_Var_False[OF \<open>rm_inj m\<close>])
    moreover
    have "(set (rules_with id ?rm))\<inverse> =  (set (rules_with id rm))\<inverse> \<inter> set r"
      unfolding rules_with_id_intersect_rules[OF \<open>rm_inj rm\<close>]
      by auto
    ultimately
    show ?thesis unfolding maps_r by blast
  qed
  moreover
  have "set (filter (is_Fun \<circ> snd) (?vrw @ rules_with Not ?m)) = (set (rules_with Not ?rm))\<inverse>"
  proof -
    have "set (filter (is_Fun \<circ> snd) (?vrw @ rules_with Not ?m))
      = set (filter (is_Fun \<circ> snd) (vrw @ rules_with Not m)) \<inter> set r"
      unfolding set_filter set_append
      unfolding rules_with_Not_intersect_rules[OF \<open>rm_inj m\<close>]
      using vars by (auto intro: in_rules_with_Not_is_Var_False[OF \<open>rm_inj m\<close>])
    moreover
    have "(set (rules_with Not ?rm))\<inverse> = (set (rules_with Not rm))\<inverse> \<inter> set r"
      unfolding rules_with_Not_intersect_rules[OF \<open>rm_inj rm\<close>]
      by auto
    ultimately
    show ?thesis unfolding maps_rw by blast
  qed
  moreover have "\<forall>r \<in> set (?vr @ ?vrw). is_Var (fst r)" using vars by auto
  moreover have "rm_inj ?m" using rm_inj by simp
  moreover have "rm_inj ?rm"
    using rm_inj_intersect_rules[OF rm_inj2] by blast
  ultimately
  show ?thesis using isnf
  by (simp only:
    fields intersect_rules_impl_def Let_def case_prod_partition o_assoc split is_dpp.simps)
qed

lemma impl_of_delete_P_Pw[code abstract]:
  "impl_of (delete_P_Pw d p pw) = delete_P_Pw_impl (impl_of d) p pw"
  unfolding delete_P_Pw_def by simp

lemma impl_of_delete_R_Rw[code abstract]:
  "impl_of (delete_R_Rw d r rw) = delete_R_Rw_impl (impl_of d) r rw"
  unfolding delete_R_Rw_def by simp

lemma dpp_sound': "dpp d = (Nfs d, M d, set (P d), set (Pw d), set (Q d), set (R d), set (Rw d))"
  by (simp add: dpp_def P_def Pw_def Q_def R_def Rw_def Nfs_def M_def dpp_impl_sound)

lemma pairs_sound: "set (pairs d) = set (P d) \<union> set (Pw d)"
  by (simp add: pairs_def P_def Pw_def dpp_impl_sound)

lemma rules_sound: "set (rules d) = set (R d) \<union> set (Rw d)"
  by (simp add: rules_def R_def Rw_def dpp_impl_sound)

lemma Q_empty_sound: "Q_empty d \<longleftrightarrow> Q d = []"
  by (simp add: Q_empty_def Q_def dpp_impl_sound)

lemma rules_no_left_var_sound:
  "rules_no_left_var d \<longleftrightarrow> (\<forall>(l, r) \<in> set (rules d). is_Fun l)"
  by (simp add: rules_no_left_var_def rules_def dpp_impl_sound prod.case_eq_if)

lemma rules_non_collapsing_sound:
  "rules_non_collapsing d \<longleftrightarrow> (\<forall>(l, r) \<in> set (rules d). is_Fun r)"
  by (simp add: rules_non_collapsing_def rules_def dpp_impl_sound prod.case_eq_if)

lemma is_QNF_sound:
  "is_QNF d = (\<lambda>t. t \<in> NF_terms (set (Q d)))"
  by (simp add: is_QNF_def Q_def dpp_impl_sound)

lemma NFQ_subset_NF_rules_sound:
  "NFQ_subset_NF_rules d \<longleftrightarrow> NF_terms (set (Q d)) \<subseteq> NF_trs (set (R d) \<union> set (Rw d))"
  using NFQ_subset_NF_rules_impl_sound[OF is_dpp_impl_of, of d]
  unfolding Q_def R_def Rw_def NFQ_subset_NF_rules_def .

lemma Wwf_rules_sound:
  "Wwf_rules d \<longleftrightarrow> wwf_qtrs (set (Q d)) (set (R d) \<union> set (Rw d))"
  using Wwf_rules_impl_sound[OF is_dpp_impl_of, of d]
  unfolding Q_def R_def Rw_def Wwf_rules_def .

lemma is_dpp_intersect_pairs_impl[simp]:
  assumes "is_dpp d"
  shows "is_dpp (intersect_pairs_impl d ps)"
  using assms by (cases d) simp_all

lemma is_dpp_replace_pair_impl[simp]:
  assumes "is_dpp d"
  shows "is_dpp (replace_pair_impl d pair ps)"
  using assms by (cases d) simp_all

lemma is_dpp_intersect_rules_impl[simp]:
  assumes "is_dpp d"
  shows "is_dpp (intersect_rules_impl d rs)"
  using assms by (cases d) simp_all

lemma impl_of_intersect_pairs[code abstract]:
  "impl_of (intersect_pairs d ps) = intersect_pairs_impl (impl_of d) ps"
  unfolding intersect_pairs_def by simp

lemma impl_of_replace_pair[code abstract]:
  "impl_of (replace_pair d pair ps) = replace_pair_impl (impl_of d) pair ps"
  unfolding replace_pair_def by simp

lemma impl_of_intersect_rules[code abstract]:
  "impl_of (intersect_rules d rs) = intersect_rules_impl (impl_of d) rs"
  unfolding intersect_rules_def by simp

lemma intersect_pairs_sound:
  "dpp (intersect_pairs d ps) =
    (Nfs d, M d, set (P d) \<inter> set ps, set (Pw d) \<inter> set ps, set (Q d), set (R d), set (Rw d))"
  by (simp add: intersect_pairs_def P_def Pw_def Q_def R_def Rw_def Nfs_def M_def
                dpp_def intersect_pairs_impl_sound)

lemma replace_pair_sound:
  "dpp (replace_pair d pair ps) =
    (Nfs d, M d, replace pair (set ps) (set (P d)), replace pair (set ps) (set (Pw d)), set (Q d), set (R d), set (Rw d))"
  by (simp add: replace_pair_def P_def Pw_def Q_def R_def Rw_def Nfs_def M_def
                dpp_def replace_pair_impl_sound)

lemma intersect_rules_sound:
  "dpp (intersect_rules d rs) =
    (Nfs d, M d, set (P d), set (Pw d), set (Q d), set (R d) \<inter> set rs, set (Rw d) \<inter> set rs)"
  by (simp add: intersect_rules_def P_def Pw_def Q_def R_def Rw_def Nfs_def M_def
                dpp_def intersect_rules_impl_sound)

lemma rules_map_sound:
  "set (rules_map d (f, n)) =
    {r \<in> set (rules d). root (fst r) = Some (f, n)}"
  using rules_map_impl_sound[OF is_dpp_impl_of, of d f n]
  unfolding rules_map_def rules_def by simp

lemma reverse_rules_map_sound:
  "set (reverse_rules_map d (f, n)) =
    {(snd r, fst r) | r. r \<in> set (rules d) \<and> root (snd r) = Some (f, n)}"
  using reverse_rules_map_impl_sound[OF is_dpp_impl_of, of d f n]
  unfolding reverse_rules_map_def rules_def .

lemma delete_P_Pw_sound:
  "dpp (delete_P_Pw d p pw) =
    (Nfs d, M d, set (P d) - set p, set (Pw d) - set pw, set (Q d), set (R d), set (Rw d))"
  using delete_P_Pw_impl_sound[of "impl_of d" p pw]
  unfolding dpp_def delete_P_Pw_def P_def Pw_def Q_def R_def Rw_def M_def Nfs_def
  by simp

lemma delete_R_Rw_sound:
  "dpp (delete_R_Rw d r rw) =
    (Nfs d, M d, set (P d), set (Pw d), set (Q d), set (R d) - set r, set (Rw d) - set rw)"
  using delete_R_Rw_impl_sound[OF is_dpp_impl_of, of d r rw]
  unfolding dpp_def delete_R_Rw_def P_def Pw_def Q_def R_def Rw_def Nfs_def M_def
  using is_dpp_delete_R_Rw_impl[OF is_dpp_impl_of] by simp

lemma split_pairs_sound:
  assumes "split_pairs d ps = (p, p')"
  shows "set p = set (pairs d) \<inter> set ps \<and> set p' = set (pairs d) - set ps"
  using split_pairs_impl_sound[OF assms[unfolded split_pairs_def]]
  unfolding pairs_def .

lemma split_rules_sound:
  assumes "split_rules d rs = (r, r')"
  shows "set r = set (rules d) \<inter> set rs \<and> set r' = set (rules d) - set rs"
  using split_rules_impl_sound[OF assms[unfolded split_rules_def]]
  unfolding rules_def .

lemma mk_sound:
  "dpp (mk nfs mi p pw q r rw) = (nfs, mi, set p, set pw, set q, set r, set rw)"
  by (simp add: dpp_def mk_def mk_impl_sound)

lemmas dpp_sound =
  dpp_sound'
  pairs_sound
  rules_sound
  Q_empty_sound
  rules_no_left_var_sound
  rules_non_collapsing_sound
  is_QNF_sound
  NFQ_subset_NF_rules_sound
  Wwf_rules_sound
  intersect_pairs_sound
  replace_pair_sound
  intersect_rules_sound
  rules_map_sound
  reverse_rules_map_sound
  delete_P_Pw_sound
  delete_R_Rw_sound
  split_pairs_sound
  split_rules_sound
  mk_sound

definition
  dpp_rbt_impl :: "(('f::compare_order, 'v) dpp, 'f, 'v) dpp_ops"
where
  "dpp_rbt_impl \<equiv> \<lparr>
    dpp_ops.dpp = dpp,
    dpp_ops.P = P,
    dpp_ops.Pw = Pw,
    dpp_ops.pairs = pairs,
    dpp_ops.Q = Q,
    dpp_ops.R = R,
    dpp_ops.Rw = Rw,
    dpp_ops.rules = rules,
    dpp_ops.Q_empty = Q_empty,
    dpp_ops.rules_no_left_var = rules_no_left_var,
    dpp_ops.rules_non_collapsing = rules_non_collapsing,
    dpp_ops.is_QNF = is_QNF,
    dpp_ops.NFQ_subset_NF_rules = NFQ_subset_NF_rules,
    dpp_ops.rules_map = rules_map,
    dpp_ops.reverse_rules_map = reverse_rules_map,
    dpp_ops.intersect_pairs = intersect_pairs,
    dpp_ops.replace_pair = replace_pair,
    dpp_ops.intersect_rules = intersect_rules,
    dpp_ops.delete_P_Pw = delete_P_Pw,
    dpp_ops.delete_R_Rw = delete_R_Rw,
    dpp_ops.split_pairs = split_pairs,
    dpp_ops.split_rules = split_rules,
    dpp_ops.mk = mk,
    dpp_ops.minimal = M,
    dpp_ops.nfs = Nfs,
    dpp_ops.wwf_rules = Wwf_rules\<rparr>"

lemma dpp_rbt_impl: "dpp_spec dpp_rbt_impl"
  by (unfold_locales, simp_all only: dpp_rbt_impl_def dpp_ops.simps,
     (blast intro!: dpp_sound)+, simp_all add: Wwf_rules_sound rules_sound)

hide_const (open) P Pw Q R Rw M Nfs

end
