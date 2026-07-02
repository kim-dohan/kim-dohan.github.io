theory AC_Weight
  imports AC_Aux
begin


fun term_size_ctxt
  where
    "term_size_ctxt Hole = 0" |
    "term_size_ctxt (More f ss C ts) =
      1 +
      sum_list (map term_size ss) +
      term_size_ctxt C +
      sum_list (map term_size ts)"

lemma term_size_ctxt [simp]:
  "term_size (C\<langle>t\<rangle>) = term_size_ctxt C + term_size t"
  by (induct C) auto

lemma term_size_at_least1:
  shows "term_size x \<ge> 1"
  by (cases x) auto

lemma term_size_ineq_sum_mset:
  fixes t :: "('f, 'v) term"
  shows "sum_mset (image_mset (term_size \<circ> \<sigma>) (vars_term_ms t)) \<ge>
           size (vars_term_ms t)"
proof (induct t)
  case (Var x)
  then show ?case using term_size_at_least1 by auto
next
  case (Fun x1a x2)
  then show ?case by (metis comp_apply size_eq_sum_mset sum_mset_mono term_size_at_least1) 
qed

lemma term_size_subst:
  shows "term_size (t \<cdot> \<sigma>) = term_size t +
           sum_mset (image_mset (\<lambda> x. term_size (\<sigma> x) - 1) (vars_term_ms t))"
proof (induct t)
  case (Var x)
  then show ?case using Nat.le_imp_diff_is_add term_size_at_least1 by fastforce 
next
  case (Fun f fs)
  then show ?case by (induct fs) auto
qed

lemma term_size_dec_sum_args_single:
  shows "sum_list (map term_size ss) < term_size (Fun f ss)"
  by simp

lemma term_size_dec_sum_args:
  shows "max (sum_list (map term_size ss)) (sum_list (map term_size ts)) < max (term_size (Fun f ss)) (term_size (Fun g ts))"
  by simp

lemma term_size_dec_arg_single:
  assumes "i < length ss"
  shows "term_size (ss ! i) < term_size (Fun f ss)"
  by (smt assms(1) elem_le_sum_list le_imp_less_Suc length_map max.strict_coboundedI1 max.strict_coboundedI2 max_def nth_map term_size.simps(2))


lemma assoc_term_size_eq:
  assumes "(l, r) \<in> A_rules AC"
  shows "term_size l = term_size r"
  using assms
  by (auto simp: A_rules_def)

lemma com_term_size_eq:
  assumes "(l, r) \<in> C_rules AC"
  shows "term_size l = term_size r"
  using assms
  by (auto simp: C_rules_def)

lemma ac_term_size_eq:
  assumes "(l, r) \<in> AC_rules AC AC"
  shows "term_size l = term_size r"
  using assms assoc_term_size_eq com_term_size_eq
  by (auto simp: AC_rules_def)

lemma ac_step_term_size_eq:
  assumes "(s, t) \<in> acstep AC AC"
  shows "term_size s = term_size t"
  using assms
proof (cases)
  case (rstep C \<sigma> l r)
  then have "term_size l = term_size r" using ac_term_size_eq by auto
  moreover have "vars_term_ms l = vars_term_ms r" using ac_rule_share_vars rstep(1) by blast
  ultimately have s:"term_size (l \<cdot> \<sigma>) = term_size (r \<cdot> \<sigma>)" by (simp add: term_size_subst) 
  then show ?thesis using rstep term_size_ctxt[of C] by auto
qed

lemma ac_converse_terms_size_eq:
  assumes "(s, t) \<in> (acstep AC AC)\<inverse>"
  shows "term_size s = term_size t"
  using assms
proof 
  have "(t, s) \<in> acstep AC AC" using assms converseD[of s t] by auto
  then show ?thesis using assms ac_step_term_size_eq[of t s] by auto
qed

lemma ac_symcl_terms_size_eq:
  assumes "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>"
  shows "term_size s = term_size t"
  using assms ac_converse_terms_size_eq ac_step_term_size_eq by auto

lemma ac_terms_size_eq:
  assumes "(s,t) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
  shows "term_size s = term_size t"
  using assms
  unfolding conversion_def by induction (auto simp:ac_symcl_terms_size_eq)


(*
  TODO remove the term_size lemmas from the local weigth function
*)

lemma acstep_no_ac_root_impl_acstep_lex_ext:
  assumes "(s,t) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)"
    and "s = Fun f ss"
    and "t = Fun f ts"
    and "length ss = length ts"
    and "f \<notin> AC \<or> length ss \<noteq> 2"
  shows "snd (lex_ext  (\<lambda> x y. ((x,y) \<in> ord, (x ,y) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*))) (length ss) ss ts)"
proof (rule ccontr)
  assume a:"\<not> snd (lex_ext (\<lambda>x y. ((x, y) \<in> ord, (x, y) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)) (length ss) ss ts)"
  then have exw:"\<exists> i < length ss. \<not> snd ((\<lambda> x y. ((x,y) \<in> ord, (x ,y) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*))) (ss ! i) (ts ! i))" using assms a by (simp add: lex_ext_iff)
  show "False" using assms(5)
  proof
    assume not_ac_sym:"f \<notin> AC"
    then show "False" using assms ac_no_ac_root_on_args_list not_ac_sym exw by (metis acconv_iff nth_map snd_conv)
  next
    assume arrity_not_two:"length ss \<noteq> 2"
    have "\<exists> i. i < length ss \<and> (ss ! i, ts ! i) \<notin> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)" using exw by auto
    moreover have "\<forall> i < length ss. (ss ! i, ts ! i) \<in> ((acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*)" using arrity_not_two ac_arity_not_two_impl_ac_terms_on_args_list assms(1-3)
      by (simp add: ac_arity_not_two_impl_ac_terms_on_args_list) 
    ultimately show "False" by auto
  qed
qed

locale weight_fun =
  fixes w :: "'f \<times> nat \<Rightarrow> nat"
    and w0 :: nat 
begin

fun weight :: "('f, 'v) term \<Rightarrow> nat"
  where
    "weight (Var x) = w0" |
    "weight (Fun f ts) = w(f, length ts) + sum_list (map weight ts)"

lemma list_take:
  assumes "xs ! k = i"
    and   "k < length xs"
  shows "EX ys zs . ys @ [i] @ zs = xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  then show ?case
    by (metis List.append_assoc append_take_drop_id take_Suc_conv_app_nth)
qed

lemma weight_subterm:
  "s \<unrhd> t \<Longrightarrow> weight t \<le> weight s"
proof (induct s)
  case (Var x)
  then show ?case using supteq_Var_id[of x t] by blast
next
  case (Fun x1a x2)
  then show ?case
  proof -
    consider (a) "t = (Fun x1a x2)" |
      (b) "EX i. i \<in> set x2 \<and> i \<unrhd> t"
      by (metis Fun.prems Fun_supteq)
    then show ?thesis
    proof cases
      case a
      then show ?thesis by simp
    next
      case b
      then obtain i
        where w:"i \<in> set x2 \<and> i \<unrhd> t" by auto
      then have "EX k. x2 ! k = i \<and> k < length x2" by (smt mem_Collect_eq set_conv_nth)
      then obtain k
        where nth:"x2 ! k = i \<and> k < length x2" by blast
      moreover have "EX xs ys . xs @ [i] @ ys = x2" using conjE[OF nth, of "\<exists>xs ys. xs @ [i] @ ys = x2"]  list_take[of x2 k i] by simp
      moreover have "weight t \<le> weight i" by (simp add: Fun.hyps w)
      ultimately show ?thesis using Fun by auto
    qed
  qed
qed


lemma subterm_weight:
  "s \<rhd> t \<Longrightarrow> weight t \<le> weight s"
  by (simp add: subterm.dual_order.strict_implies_order weight_subterm)

fun weight_ctxt :: "('f, 'v) ctxt \<Rightarrow> nat"
  where
    "weight_ctxt Hole = 0" |
    "weight_ctxt (More f ss C ts) =
      w(f, length ss + length ts + 1) +
      sum_list (map weight ss) +
      weight_ctxt C +
      sum_list (map weight ts)"

lemma weight_ctxt [simp]:
  "weight (C\<langle>t\<rangle>) = weight_ctxt C + weight t"
  by (induct C) auto

lemma weight_simp_over_list[simp]:
  "weight (Fun f (pref @ [x] @ suf)) = w (f, length (pref @ [x] @ suf)) + weight x + sum_list (map weight pref) + sum_list (map weight suf)"
  by (induct "(pref @ [x] @ suf)") auto

end

locale admissible_weight_fun =
  weight_fun w w0 +
  prec pr_strict 
  for w  :: "'f \<times> nat \<Rightarrow> nat"
    and w0 :: "nat"
    and pr_strict :: "('f \<times> nat) \<Rightarrow> ('f \<times> nat) \<Rightarrow> bool" +
  assumes w0: "w (f, 0) \<ge> w0" "w0 > 0"
    and adm: "w (f, 1) = 0 \<and> (f, 1) \<noteq> g \<Longrightarrow> pr_strict (f, 1) g"
    and pr_SN: "SN {(fn, gm). pr_strict fn gm}"
    and pr_irr: "\<not> pr_strict g g"
    and pr_trans[trans]: "pr_strict s t \<and> pr_strict t u \<Longrightarrow> pr_strict s u"
begin

lemma pr_str:
  assumes "pr_strict f g"
  shows "\<not> pr_strict g f"
proof
  assume "pr_strict g f"
  thus "False" using assms pr_irr pr_trans by blast
qed

lemma unique_unary_function_weight0:
  assumes "w (f,1) = 0"
  shows "\<And> g. w(g,1) = 0 \<Longrightarrow> f = g"
  using assms adm pr_irr pr_trans by (metis (no_types, opaque_lifting) fst_conv) 

lemma weight_w0: "weight t \<ge> w0"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun x1a x2)
  then show ?case
  proof (cases x2)
    case Nil
    then show ?thesis using w0(1) by auto
  next
    case (Cons a list)
    then have "weight a \<ge> w0" by (simp add: Fun.hyps)
    then show ?thesis using Cons by simp
  qed
qed

lemma weight_subst:
  shows "weight (t \<cdot> \<sigma>) = weight t + sum_mset (image_mset (\<lambda> x. weight (\<sigma> x) - w0) (vars_term_ms t))"
proof (induct t)
  case (Var x)
  then show ?case by (simp add: weight_w0)
next
  case (Fun f fs)
  then show ?case by (induct fs) auto
qed

lemma weight_lower_bound_list:
  shows "w0 * length ts \<le> sum_list (map weight ts)"
proof (induct ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  then have "w0 \<le> weight a" using weight_w0 by auto  
  then show ?case using Cons weight_w0 by auto
qed

lemma weight_lower_bound_n_arry_fun:
  shows "weight (Fun f ts) \<ge> length ts * w0"
  by (simp add: mult.commute trans_le_add2 weight_lower_bound_list)


lemma assoc_share_weight:
  assumes "(l, r) \<in> A_rules AC"
  shows "weight l = weight r"
  using assms
  by (auto simp: A_rules_def)

lemma com_share_weight:
  assumes "(l, r) \<in> C_rules AC"
  shows "weight l = weight r"
  using assms
  by (auto simp: C_rules_def)

lemma ac_share_weight:
  assumes "(l, r) \<in> AC_rules AC AC"
  shows "weight l = weight r"
  using assms assoc_share_weight com_share_weight
  by (auto simp: AC_rules_def)

lemma ac_step_terms_weight_eq:
  assumes "(s, t) \<in> acstep AC AC"
  shows "weight s = weight t"
  using assms
proof (cases)
  case (rstep C \<sigma> l r)
  then show ?thesis
    by (metis ac_rule_share_vars ac_share_weight weight_ctxt weight_subst) 
qed

lemma ac_converse_terms_weight_eq:
  assumes "(s, t) \<in> (acstep AC AC)\<inverse>"
  shows "weight s = weight t"
  using assms
proof 
  have "(t, s) \<in> acstep AC AC" using assms converseD[of s t] by auto
  then show ?thesis using assms ac_step_terms_weight_eq[of t s] by (auto)
qed

lemma ac_symcl_terms_weight_eq:
  assumes "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>"
  shows "weight s = weight t"
  using assms ac_converse_terms_weight_eq ac_step_terms_weight_eq by auto

lemma ac_terms_weight_eq:
  assumes "(s, t) \<in> (acstep AC AC)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "weight s = weight t"
  using assms
  unfolding conversion_def by induction (auto simp:ac_symcl_terms_weight_eq)


lemma weight_stable_lt:
  assumes ws: "weight t < weight s"
    and vs: "vars_term_ms t \<subseteq># vars_term_ms s"
  shows "weight (t \<cdot> \<sigma>) < weight (s \<cdot> \<sigma>)"
proof -
  from vs[unfolded mset_subset_eq_exists_conv] obtain u where vt: "vars_term_ms s = vars_term_ms t + u" by auto
  then show ?thesis unfolding weight_subst vt using assms(1) by (simp add: add_mono_thms_linordered_field(3))
qed

lemma weight_stable_le:
  assumes ws: "weight t \<le> weight s"
    and vs: "vars_term_ms t \<subseteq># vars_term_ms s"
  shows "weight (t \<cdot> \<sigma>) \<le> weight (s \<cdot> \<sigma>)"
proof -
  from vs[unfolded mset_subset_eq_exists_conv] obtain u where vt: "vars_term_ms s = vars_term_ms t + u" by auto
  then show ?thesis unfolding weight_subst vt using assms(1) by (simp add: add_mono_thms_linordered_field(3))
qed

end

end
