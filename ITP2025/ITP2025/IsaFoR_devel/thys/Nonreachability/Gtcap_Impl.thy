(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016, 2017)
License: LGPL (see file COPYING.LESSER)
*)

theory Gtcap_Impl
  imports
    TRS.Tcap_Impl
    Gtcap
    "Transitive-Closure.Transitive_Closure_List_Impl"
    First_Order_Rewriting.Term_Impl
begin

definition "gt1 = map (\<lambda>r. case r of (s, t) \<Rightarrow> (root s, root t))"

lemma gt1_iff_GT1 [simp]:
  "set (gt1 rs) = GT1 (set rs)"
by (auto simp: GT1_def gt1_def)

definition "mk_gt_fun rs =
  (let in_trancl = memo_list_trancl (gt1 rs) in
  (\<lambda>f g. g \<in> set (in_trancl f)))"

lemma mk_gt_fun_iff [simp]:
  "mk_gt_fun rs f g \<longleftrightarrow> (f, g) \<in> (GT1 (set rs))\<^sup>+"
by (auto simp: mk_gt_fun_def memo_list_trancl)

lemma GT_set_iff:
  "(s, t) \<in> GT (set rs) \<longleftrightarrow>
  is_Var s \<or> is_Var t \<or> mk_gt_fun rs (root s) (root t) \<or> mk_gt_fun rs (root s) None
  \<or> mk_gt_fun rs None (root t) \<or> mk_gt_fun rs None None"
by (auto simp: GT_def)

definition gt_term
where
  "gt_term nlv ne gt_fun rm s t \<longleftrightarrow> ne \<and>
    (let root1 = root s; root2 = root t in
    (is_Var s \<or> is_Var t \<or> gt_fun None None \<or> gt_fun root1 root2 \<or> gt_fun root1 None \<or> gt_fun None root2) \<and>
    (if nlv then
      (case root1 of
        Some fn \<Rightarrow> \<exists>r\<in>set (rm fn). Ground_Context.match (tcapRM nlv rm s) (fst r)
      | None \<Rightarrow> True)
    else True))"

lemma root_None_gc_match:
  "root s = None \<Longrightarrow> Ground_Context.match (tcap R s) t"
by (cases s) (auto simp: Ground_Context.match_def)

lemma ne_pair_list:
  "xs \<noteq> [] \<Longrightarrow> \<exists>x y. (x, y) \<in> set xs"
by (cases xs) auto

lemma varcond_root:
  "\<forall>lr \<in> R. is_Fun (fst lr) \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> \<exists>f n. root x = Some (f, n)"
by (cases x) auto

lemma var_lhs_gc_match:
  "(l, r) \<in> R \<Longrightarrow> is_Var l \<Longrightarrow> Ground_Context.match (tcap R s) l"
apply (cases l) apply (auto simp: Ground_Context.match_def)
by (meson tcap_instance_equiv_class)

lemma gt_term_iff:
  assumes nlv: "nlv \<longleftrightarrow> (\<forall>lr \<in> set rs. is_Fun (fst lr))"
    and rm: "\<And>fn. set (rm fn) = {(l, r). (l, r) \<in> set rs \<and> root l = Some fn}"
  shows "gt_term nlv (rs \<noteq> []) (mk_gt_fun rs) rm s t \<longleftrightarrow>
    (s, t) \<in> GT (set rs) \<inter>
    {(s, t :: ('f, 'v) term). \<exists>(l, r) \<in> set rs. Ground_Context.match (tcap (set rs) s) l}"
proof (cases nlv)
  case True
  then have *: "\<forall>lr \<in> set rs. is_Fun (fst lr)" using nlv by auto
  show ?thesis
    using True and varcond_root [OF *]
    apply (simp add: gt_term_def Let_def tcapRM [OF assms, simplified True] GT_set_iff rm split: option.splits)
    apply (cases s; cases t; simp)
       apply (force simp: Ground_Context.match_def dest: ne_pair_list)
      apply (force simp: Ground_Context.match_def dest: ne_pair_list)
     apply (auto simp: Let_def Ground_Context.match_def)
    using nlv apply fastforce
            apply (metis fst_conv)
    using nlv apply fastforce
    using nlv apply fastforce
    using nlv apply fastforce
    using nlv apply fastforce
       apply (metis fst_conv)
      apply (metis fst_conv)
     apply (metis fst_conv)
    apply (metis fst_conv)
    done
next
  case False
  with nlv obtain l and r where "(l, r) \<in> set rs" and "is_Var l" by auto
  then have "Ground_Context.match (tcap (set rs) s) l"
    using var_lhs_gc_match by auto
  then show ?thesis
    using False and \<open>(l, r) \<in> set rs\<close>
    by (auto simp: gt_term_def Let_def GT_def)
qed

fun rd_impl
where
  "rd_impl gt (Fun f ss, Fun g ts) =
    (if f = g \<and> length ss = length ts \<and> \<not> gt (Fun f ss) (Fun g ts) then concat (map (rd_impl gt) (zip ss ts))
    else [(Fun f ss, Fun g ts)])"
| "rd_impl _ (s, t) = [(s, t)]"

interpretation rd_gtcap:
  reachability_decomposition R "GT R \<inter> {(s, t). \<exists>(l, r)\<in>R. Ground_Context.match (tcap R s) l}" for R
  by (intro reachability_decomposition_Int rd_root rd_tcap)

lemma rd_impl_gtcap_conv:
  fixes R :: "('f, 'v) trs"
  assumes gt: "\<And>s t. gt s t \<longleftrightarrow>
    (s, t) \<in> GT R \<inter> {(s, t :: ('f, 'v) term). \<exists>(l, r) \<in> R. Ground_Context.match (tcap R s) l}"
    (is "\<And>s t. gt s t \<longleftrightarrow> (s, t) \<in> ?S")
  shows "rd_impl gt (s, t) = rd_gtcap.reach_decomp R s t"
    unfolding rd_gtcap.reach_decomp_reach_decomp'_conv
    apply (induct ("(s, t)") rule: rd_gtcap.reach_decomp'.induct [where R = R])
      apply (case_tac "(Fun f ss, Fun g ts) \<in> ?S")
       apply (auto simp only: rd_gtcap.reach_decomp'.simps rd_impl.simps gt [symmetric])
       apply (auto intro!: arg_cong [of _ _ concat])
    done

lemma rd_impl:
  fixes R :: "('f, 'v) trs"
  assumes gt: "\<And>s t. gt s t \<longleftrightarrow>
    (s, t) \<in> GT R \<inter> {(s, t :: ('f, 'v) term). \<exists>(l, r) \<in> R. Ground_Context.match (tcap R s) l}"
    (is "\<And>s t. gt s t \<longleftrightarrow> (s, t) \<in> ?S")
    and "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  shows "\<forall>(u, v) \<in> set (rd_impl gt (s, t)). (u \<cdot> \<sigma>, v \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  using assms
  unfolding rd_impl_gtcap_conv [OF gt]
  by (auto dest: rd_gtcap.reach_decomp_sound)

definition nonreach :: "_"
  where
    "nonreach gt s t =
      (case (s, t) of
        (Fun f ss, Fun g ts) \<Rightarrow> (f, length ss) \<noteq> (g, length ts) \<and> \<not> gt s t
      | _ \<Rightarrow> False)"

lemma nonreach:
  fixes R :: "('f, 'v) trs"
  assumes gt: "\<And>s t. gt s t \<longleftrightarrow>
    (s, t) \<in> GT R \<inter> {(s, t :: ('f, 'v) term). \<exists>(l, r) \<in> R. Ground_Context.match (tcap R s) l}"
    (is "\<And>s t. gt s t \<longleftrightarrow> (s, t) \<in> ?S")
  assumes nr: "nonreach gt s t"
    and *: "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" (is "(?s, ?t) \<in> _")
  shows False
proof -
  obtain f ss and g ts where [simp]: "s = Fun f ss" "t = Fun g ts"
    and ne: "(f, length ss) \<noteq> (g, length ts)" and "\<not> gt s t"
    using nr by (auto simp: nonreach_def split: term.splits)
  have "(?s, ?t) \<in> GE R" using rsteps_GE [OF *] .
  then have "(?s, ?t) \<in> GT R" using ne by auto
  then have GT: "(s, t) \<in> GT R" by (rule GT_substs)

  obtain n where "rrsteps_n R (Suc n) ?s ?t"
    using rsteps_imp_rrsteps_n [OF *] and rrsteps_n_0 [of R ?s ?t] and ne
    by auto (metis old.nat.exhaust)+
  from rrsteps_n_match_tcap [OF this] and \<open>\<not> gt s t\<close> [unfolded gt]
  show False
    using GT and tcap_substs [of s \<sigma> t \<tau> R]
    by (auto simp del: tcap.simps simp: gt)
qed

declare length_dropWhile_le [termination_simp]
fun group_key :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  where
    "group_key f [] = []"
  | "group_key f (x#xs) = (x # takeWhile (\<lambda>y. f x = f y) xs) # group_key f (dropWhile (\<lambda>y. f x = f y) xs)"
declare length_dropWhile_le [termination_simp del]

lemma concat_group_key [simp]:
  "concat (group_key f xs) = xs"
  by (induct f xs rule: group_key.induct) (auto dest: set_takeWhileD set_dropWhileD)

lemma mem_group_key:
  assumes "ys \<in> set (group_key f xs)"
  shows "set ys \<subseteq> set xs \<and> length ys > 0 \<and> (\<forall>i<length ys. f (ys ! i) = f (ys ! 0))"
  using assms
  apply (induct f xs arbitrary: ys rule: group_key.induct)
   apply (auto simp: less_Suc_eq_0_disj dest: set_takeWhileD set_dropWhileD)
  by (metis (full_types) nth_mem set_takeWhileD)

definition "nonlinear_var_nonreach F gt_fun xs =
  (let xs1 = filter (is_Var \<circ> fst) xs in
  let xs2 = sort_key fst xs1 in
  let xs3 = group_key fst xs2 in
  (\<exists>xts \<in> set xs3. length xts > 1 \<and>
    (\<forall>f\<in>set F. \<not> gt_fun (Some f) None \<and> (\<exists>(u, v)\<in>set xts. is_Fun v \<and> funas_term v \<subseteq> set F \<and>
    root v \<noteq> Some f \<and> \<not> gt_fun (Some f) (root v)))))"

lemma nonlinear_var_nonreach_impl:
  assumes F: "funas_trs (set R) \<subseteq> set F"
    and var: "\<forall>(l, r)\<in>set R. is_Fun l"
    and ne: "set R \<noteq> {}"
    and nr: "nonlinear_var_nonreach F (mk_gt_fun R) (rd_gtcap.reach_decomp (set R) s t)"
      (is "nonlinear_var_nonreach _ _ ?rs")
    and *: "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep (set R))\<^sup>*"
  shows False
proof -
  have eq: "(f, g) \<notin> (GT1 (set R))\<^sup>* \<longleftrightarrow> g \<noteq> f \<and> (f, g) \<notin> (GT1 (set R))\<^sup>+" for f g
    by (auto simp: trancl_into_rtrancl rtrancl_eq_or_trancl)
  from nr obtain xts where 1: "\<forall>i<length xts. fst (xts ! i) = fst (xts ! 0)"
    and 2: "set xts \<subseteq> {x \<in> set ?rs. is_Var (fst x)}"
    "length xts > 1"
    "\<forall>f\<in>set F. (Some f, None) \<notin> (GT1 (set R))\<^sup>+ \<and> (
      \<exists>(u, v) \<in> set xts. is_Fun v \<and> funas_term v \<subseteq> set F \<and> (Some f, root v) \<notin> (GT1 (set R))\<^sup>*)"
    by (auto simp: nonlinear_var_nonreach_def eq in_set_idx dest: mem_group_key)
  from 1 have "\<forall>(u, v) \<in> set xts. u = fst (xts ! 0)"
    by (auto) (metis fst_conv in_set_conv_nth)
  then have "\<forall>f\<in>set F. \<exists>u. (fst (xts ! 0), u) \<in> set ?rs \<and> is_Fun u \<and> funas_term u \<subseteq> set F \<and> (Some f, root u) \<notin> (GT1 (set R))\<^sup>*"
    using 2
    apply (auto)
    apply (erule_tac x = "(a, b)" and A = "set F" in ballE)
     apply auto
    done
  with 2 and rd_gtcap.nonlinear_var_nonreach [OF F var ne _ *, of "the_Var (fst (xts ! 0))"]
  show ?thesis by (simp add: subset_eq) blast
qed

definition "nonreachable_gtcapRM fs nlv ne gt_fun rm s t =
  (let gt = gt_term nlv ne gt_fun rm in
  let rs = rd_impl gt (s, t) in
  (\<exists>(u, v) \<in> set rs. nonreach gt u v) \<or>
  (nlv \<and> ne \<and> nonlinear_var_nonreach fs gt_fun rs))"

lemma nonreach_gtcap:
  fixes R :: "('f::compare_order, 'v::compare_order) rules" and s t :: "('f, 'v) term"
  assumes nlv: "nlv \<longleftrightarrow> (\<forall>lr\<in>set R. is_Fun (fst lr))" (is "_ = ?nlv")
    and rm: "\<And>fn. set (rm fn) = {(l, r) \<in> set R. root l = Some fn}"
  assumes nr: "nonreachable_gtcapRM (funas_trs_list R) nlv (R \<noteq> []) (mk_gt_fun R) rm s t"
    and *: "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep (set R))\<^sup>*"
  shows False
proof -
  let ?F = "funas_trs_list R"
  let ?gt = "gt_term nlv (R \<noteq> []) (mk_gt_fun R) rm"
  let ?rd = "rd_impl ?gt (s, t)"
  from rd_impl [OF gt_term_iff, OF nlv rm *]
  have "\<forall>(u, v) \<in> set ?rd. (u \<cdot> \<sigma>, v \<cdot> \<tau>) \<in> (rstep (set R))\<^sup>*" by (simp add: nlv)
  then consider u and v where "(u, v) \<in> set ?rd" and "nonreach ?gt u v"
    | "nlv" and "R \<noteq> []" and "nonlinear_var_nonreach ?F (mk_gt_fun R) ?rd"
    using nr by (auto simp: nonreachable_gtcapRM_def Let_def)
  then show False
  proof (cases)
    case 1
    moreover
    have "(u \<cdot> \<sigma>, v \<cdot> \<tau>) \<in> (rstep (set R))\<^sup>*"
      using rd_impl [OF gt_term_iff, OF nlv rm *] and \<open>(u, v) \<in> set ?rd\<close> by (auto simp: nlv)
    ultimately
    show False
      using nonreach [OF gt_term_iff, OF nlv rm 1(2), of \<sigma> \<tau>] by simp
  next
    case 2
    then show False
      using rd_impl_gtcap_conv [OF gt_term_iff, OF nlv rm]
      by (intro nonlinear_var_nonreach_impl [OF _ _ _ _ *]) (auto simp: nlv)
  qed
qed

end
