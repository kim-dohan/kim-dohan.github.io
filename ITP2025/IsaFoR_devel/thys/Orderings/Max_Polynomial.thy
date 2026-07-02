(*
Author:  Akihisa Yamada (2016-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Max_Polynomial
  imports Ordered_Algebra
    Integer_Arithmetic
    Polynomial_Interpolation.Ring_Hom
    "HOL-Algebra.Ring"
    Max_Polynomial_Aux
begin

section \<open>Max-Polynomial Interpretations\<close>

text \<open>We implement max-polynomial interpretations as an instance of @{locale encoded_algebra}.
  As a target algebra, we introduce a $G$-algebra where $G = \{+,\times,\max\}$.\<close>

locale max_poly_locale
begin

datatype sig = ConstF nat | SumF | ProdF | MaxF

primrec I where
  "I (ConstF n) = (\<lambda>x. n)"
| "I SumF = sum_list"
| "I ProdF = prod_list"
| "I MaxF = max_list"

abbreviation const where "const n \<equiv> Fun (ConstF n) []"

sublocale wf_weak_mono_algebra less_eq less I
proof
  fix f ls rs and a b :: nat
  assume ba: "b \<le> a"
  then show "I f (ls @ b # rs) \<le> I f (ls @ a # rs)"
  proof(cases f)
    case [simp]: MaxF
    note ba
    also have "a \<le> max_list (ls @ a # rs)" by auto
    finally show ?thesis by auto
  qed auto
qed

sublocale algebra_constant I const by (unfold_locales, auto)

fun simplify where
  "simplify (Var x) = Var x"
| "simplify (Fun (ConstF n) ss) = const n"
| "simplify (Fun SumF ss) = (
    let ss' = filter (\<lambda>s. s \<noteq> const 0) (map simplify ss) in
    case ss' of [] \<Rightarrow> const 0 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun SumF ss'
  )"
| "simplify (Fun ProdF ss) = (
    let ss' = filter (\<lambda>s. s \<noteq> const 1) (map simplify ss) in
    if const 0 \<in> set ss' then const 0
    else case ss' of [] \<Rightarrow> const 1 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun ProdF ss'
  )"
| "simplify (Fun MaxF ss) = (
    let ss' = filter (\<lambda>s. s \<noteq> const 0) (map simplify ss) in
    case ss' of [] \<Rightarrow> const 0 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun MaxF ss'
  )"

lemma list_caseE:
  assumes "case xs of [] \<Rightarrow> a | x # ys \<Rightarrow> b x ys"
    and "xs = [] \<Longrightarrow> a \<Longrightarrow> thesis"
    and "\<And>x ys. xs = x#ys \<Longrightarrow> b x ys \<Longrightarrow> thesis"
  shows thesis
  using assms
  by (cases xs, auto)

lemma vars_term_simplify: "vars_term (simplify s) \<subseteq> vars_term s"
proof (rule subsetI, induct s rule: simplify.induct)
  case (1 v)
  then show ?case by simp
next
  case (2 n ss)
  then show ?case by simp
next
  case IH: (3 ss)
  from IH.prems have "x \<in> \<Union>(vars_term ` set (filter (\<lambda>s. s \<noteq> const 0) (map simplify ss)))"
    by (auto simp: Let_def list.case_distrib simp del: set_filter elim!: list_caseE)
  also have "\<dots> \<subseteq> vars_term (Fun SumF ss)" using IH.hyps by auto
  finally show ?case.
next
  case IH: (4 ss)
  let ?ss = "filter (\<lambda>s. s \<noteq> const 1) (map simplify ss)"
  from IH.prems have "x \<in> \<Union>(vars_term ` set ?ss)"
    by (cases "const 0 \<in> set ?ss", auto simp: Let_def list.case_distrib simp del: set_filter elim!: list_caseE)
  also have "\<dots> \<subseteq> vars_term (Fun ProdF ss)" using IH.hyps by auto
  finally show ?case.
next
  case IH: (5 ss)
  from IH.prems have "x \<in> \<Union>(vars_term ` set (filter (\<lambda>s. s \<noteq> const 0) (map simplify ss)))"
    by (auto simp: Let_def list.case_distrib simp del: set_filter elim!: list_caseE)
  also have "\<dots> \<subseteq> vars_term (Fun MaxF ss)" using IH.hyps by auto
  finally show ?case.
qed



lemma eval_SumF_filter_0:
  "\<lbrakk>Fun SumF (filter (\<lambda>s. s \<noteq> const 0) ss)\<rbrakk> = \<lbrakk>Fun SumF ss\<rbrakk>"
  by (auto intro!: ext sum_list_map_filter)

lemma eval_MaxF_filter_0:
  "\<lbrakk>Fun MaxF (filter (\<lambda>s. s \<noteq> const 0) ss)\<rbrakk> = \<lbrakk>Fun MaxF ss\<rbrakk>"
  by (auto intro!: ext max_list_map_filter)

lemma eval_ProdF_filter_1:
  "\<lbrakk>Fun ProdF (filter (\<lambda>s. s \<noteq> const (Suc 0)) ss)\<rbrakk> = \<lbrakk>Fun ProdF ss\<rbrakk>"
  by (auto intro!: ext prod_list_map_filter)

lemma eval_ProdF_with_0:
  "\<exists>s \<in> set ss. s = const 0 \<Longrightarrow> \<lbrakk>Fun ProdF ss\<rbrakk> = \<lbrakk>const 0\<rbrakk>"
  by (intro ext, induct ss, auto)

lemma simplify_lemma:
  "\<lbrakk>case ss of [] \<Rightarrow> const 0 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun SumF ss\<rbrakk> = \<lbrakk>Fun SumF ss\<rbrakk>"
  "\<lbrakk>case ss of [] \<Rightarrow> const 1 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun ProdF ss\<rbrakk> = \<lbrakk>Fun ProdF ss\<rbrakk>"
  "\<lbrakk>case ss of [] \<Rightarrow> const 0 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun MaxF ss\<rbrakk> = \<lbrakk>Fun MaxF ss\<rbrakk>"
  by (atomize(full), cases ss rule: list_3_cases, auto simp: bot_nat_def)

lemma simplify [simp]: "\<lbrakk>simplify s\<rbrakk> = \<lbrakk>s\<rbrakk>"
proof (intro ext, induct s rule: simplify.induct)
  case (1 x \<alpha>)
  then show ?case by simp
next
  case (2 n ss \<alpha>)
  then show ?case by (auto simp: simplify_lemma)
next
  case (3 ss \<alpha>)
  then show ?case by (auto simp: Let_def simplify_lemma eval_SumF_filter_0 cong: map_cong)
next
  case (4 ss \<alpha>)
  then show ?case
    by (force simp: Let_def simplify_lemma eval_ProdF_filter_1[simplified] prod_list_zero_iff image_def cong: map_cong)
next
  case (5 ss \<alpha>)
  then show ?case by (auto simp: Let_def simplify_lemma eval_MaxF_filter_0 o_def intro:max_list_cong)
qed

end


derive compare max_poly_locale.sig
global_interpretation max_poly: max_poly_locale .

instantiation max_poly.sig :: showl
begin

primrec showsl_sig :: "max_poly.sig \<Rightarrow> showsl"
  where
    "showsl_sig (max_poly.ConstF n) = showsl n"
  | "showsl_sig (max_poly.MaxF) = showsl_lit (STR ''max'')"
  | "showsl_sig (max_poly.ProdF) = showsl_lit (STR ''prod'')"
  | "showsl_sig (max_poly.SumF) = showsl_lit (STR ''sum'')"

definition "showsl_list (xs :: max_poly.sig list) = default_showsl_list showsl xs"

instance ..

end


subsection \<open>Translation to Integer Arithmetic\<close>

context max_poly_locale
begin

primrec to_IA :: "(sig,'v) term \<Rightarrow> 'v IA.exp list" where
  "to_IA (Var x) = [IA.var x]"
| "to_IA (Fun f ss) = (case f of ConstF n \<Rightarrow> [IA.const n]
    | MaxF \<Rightarrow> if ss = [] then [IA.const 0] else concat (map to_IA ss)
    | SumF \<Rightarrow>
      if ss = [] then [Fun (IA.SumF 0) []]
      else map (Fun (IA.SumF (length ss))) (product_lists (map to_IA ss))
    | ProdF \<Rightarrow>
      if ss = [] then [Fun (IA.ProdF 0) []]
      else map (Fun (IA.ProdF (length ss))) (product_lists (map to_IA ss))
  )"

lemma to_IA_induct[case_names Var ConstF SumF ProdF MaxF SumF0 ProdF0 MaxF0]:
  assumes "\<And>x. P (Var x)"
    and "\<And>n ss. P (Fun (ConstF n) ss)"
    and "\<And>ss. ss \<noteq> [] \<Longrightarrow> (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (Fun SumF ss)"
    and "\<And>ss. ss \<noteq> [] \<Longrightarrow> (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (Fun ProdF ss)"
    and "\<And>ss. ss \<noteq> [] \<Longrightarrow> (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (Fun MaxF ss)"
    and "P (Fun SumF [])"
    and "P (Fun ProdF [])"
    and "P (Fun MaxF [])"
  shows "P s"
  by (insert assms, induction_schema, metis term.exhaust sig.exhaust, lexicographic_order)


lemma to_IA_has_type:
  "s' \<in> set (to_IA s) \<Longrightarrow> IA.has_type s' IA.IntT"
  apply (induct s arbitrary:s' rule: to_IA_induct, auto simp:in_set_product_lists_length product_lists_set)
  apply (metis length_map list_all2_nthD2 nth_map nth_mem)
  apply (metis length_map list_all2_nthD2 nth_map nth_mem)
  done

lemma to_IA_eq_NilE[elim!]: "to_IA s = [] \<Longrightarrow> thesis" by (induct s rule: to_IA_induct, auto)

definition "to_IA_assignment \<alpha> \<equiv> \<lambda>(x,t). case t of IA.IntT \<Rightarrow> IA.Int (int (\<alpha> x)) | _ \<Rightarrow> IA.Bool False"

lemma to_IA_assignment: "IA.assignment (to_IA_assignment \<alpha>)"
  by (intro IA.assignmentI, auto simp: to_IA_assignment_def split: IA.ty.split)

definition "eval_via_IA s \<alpha> \<equiv> map (\<lambda>t. IA.eval t (to_IA_assignment \<alpha>)) (to_IA s)"

lemma eval_via_IA_eq_NilE[elim!]: "eval_via_IA s \<alpha> = [] \<Longrightarrow> thesis"
  by (auto simp: eval_via_IA_def)

lemma eval_via_IA_range: "set (eval_via_IA s \<alpha>) \<subseteq> range IA.Int"
proof-
  have "set (eval_via_IA s \<alpha>) \<subseteq> set (map (\<lambda>t. IA.eval t (to_IA_assignment \<alpha>)) (to_IA s) @ [IA.Int 0])"
    by (unfold eval_via_IA_def, auto)
  also have "\<dots> \<subseteq> range IA.Int"
    using to_IA_assignment[of \<alpha>]
    by (auto dest!: to_IA_has_type IA.eval_types)
  finally show ?thesis.
qed

lemma max_list1_eval_via_IA_range:
  "max_list1 (eval_via_IA s \<alpha>) \<in> range IA.Int"
proof-
  note max_list1_mem
  also note eval_via_IA_range
  finally show ?thesis by force
qed

end

context max_poly_locale
begin

lemma eval_via_IA_ge_0: "v \<in> set (eval_via_IA s \<alpha>) \<Longrightarrow> IA.to_int v \<ge> 0"
proof (unfold eval_via_IA_def, induct s arbitrary:v rule: to_IA_induct)
  case (Var x)
  then show ?case by (auto simp: to_IA_assignment_def)
next
  case (SumF ss)
  from this(1,3)
  show ?case
    apply (auto simp: o_def image_def in_set_product_lists_length intro!:sum_list_ge_0_nth)
    apply(drule(1) in_set_product_lists_nth[of _ "map to_IA ss", simplified])
    using SumF(2)[OF nth_mem] apply auto
    done
next
  case (ProdF ss)
  from this(1,3)
  show ?case
    apply (auto simp: o_def image_def in_set_product_lists_length intro!:prod_list_nonneg_nth)
    apply(drule  in_set_product_lists_nth[of _ "map to_IA ss", simplified])
    using ProdF(2)[OF nth_mem] apply auto
    done
qed auto

lemma eval_via_IA:
  fixes f \<alpha>
  defines "f \<equiv> \<lambda>s. eval_via_IA s \<alpha>"
  shows "int (\<lbrakk>s\<rbrakk> \<alpha>) = IA.to_int (max_list1 (f s))"
proof (induct s rule: to_IA_induct)
  case (Var x)
  show ?case by (simp add: eval_via_IA_def to_IA_assignment_def IA_Int_hom.hom_max[symmetric] f_def)
next
  case (ConstF n ss)
  show ?case by (simp add: eval_via_IA_def IA_Int_hom.hom_max[symmetric] f_def)
next
  case (SumF ss)
  note ss = this(1) and 1 = map_ext[OF this(2)[unfolded atomize_imp]]
  have "int (\<lbrakk>Fun SumF ss\<rbrakk> \<alpha>) = (\<Sum>s\<leftarrow>ss. IA.to_int (max_list1 (f s)))"
    by (auto simp: image_def int_hom.hom_sum_list o_def 1)
  also have "\<dots> = (\<Sum>s\<leftarrow>ss. (max_list1 (map IA.to_int (f s))))"
    apply (rule arg_cong[of _ _sum_list])
    apply (rule map_cong[OF refl])
    apply (rule hom_max_list1)
    by (auto simp: o_def f_def dest!: subsetD[OF eval_via_IA_range])
  also have "\<dots> = sum_list (map max_list1 (map (map IA.to_int) (map f ss)))"
    by (auto simp: o_def)
  also have "\<dots> = max_list1 (map sum_list (product_lists (map (map IA.to_int) (map f ss))))"
    by (intro sum_list_max_list1, auto simp:o_def f_def)
  also have "\<dots> = max_list1 (map sum_list (product_lists (map (map (IA.to_int \<circ> (\<lambda>t. IA.eval t (to_IA_assignment \<alpha>)))) (map to_IA ss))))"
    by (auto simp: o_def f_def eval_via_IA_def)
  also have "\<dots> = max_list1 (map IA.to_int (f (Fun SumF ss)))"
    by (subst product_lists_map_map, auto simp: o_def f_def eval_via_IA_def ss)
  also have "\<dots> = IA.to_int (max_list1 (f (Fun SumF ss)))"
    by (rule hom_max_list1[symmetric], auto simp: f_def dest!: subsetD[OF eval_via_IA_range])
  finally show ?case.
next
  case (ProdF ss)
  note ss = this(1) and 1 = map_ext[OF this(2)[unfolded atomize_imp]]
  have "int (\<lbrakk>Fun ProdF ss\<rbrakk> \<alpha>) = (\<Prod>s\<leftarrow>ss. IA.to_int (max_list1 (f s)))"
    by (auto simp: image_def int_hom.hom_prod_list o_def 1)
  also have "\<dots> = (\<Prod>s\<leftarrow>ss. (max_list1 (map IA.to_int (f s))))"
    apply (rule arg_cong[of _ _prod_list])
    apply (rule map_cong[OF refl])
    apply (rule hom_max_list1)
    by (auto simp: o_def f_def dest!: subsetD[OF eval_via_IA_range])
  also have "\<dots> = prod_list (map max_list1 (map (map IA.to_int) (map f ss)))"
    by (auto simp: o_def)
  also have "\<dots> = max_list1 (map prod_list (product_lists (map (map IA.to_int) (map f ss))))"
    by (intro prod_list_max_list1, auto simp:o_def f_def intro:eval_via_IA_ge_0)
  also have "\<dots> = max_list1 (map prod_list (product_lists (map (map (IA.to_int \<circ> (\<lambda>t. IA.eval t (to_IA_assignment \<alpha>)))) (map to_IA ss))))"
    by (auto simp: o_def f_def eval_via_IA_def)
  also have "\<dots> = max_list1 (map IA.to_int (f (Fun ProdF ss)))"
    by (subst product_lists_map_map, auto simp: o_def f_def eval_via_IA_def ss)
  also have "\<dots> = IA.to_int (max_list1 (f (Fun ProdF ss)))"
    by (rule hom_max_list1[symmetric], auto simp: f_def dest!: subsetD[OF eval_via_IA_range])
  finally show ?case.
next
  case (MaxF ss)
  note ss = this(1) and 1 = map_ext[OF this(2)[unfolded atomize_imp]]
  have "\<lbrakk>Fun MaxF ss\<rbrakk>\<alpha> = max_list1 (map (\<lambda>s. \<lbrakk>s\<rbrakk>\<alpha>) ss)"
    using ss by (auto simp: max_list_as_max_list1)
  also have "int \<dots> = max_list1 (map (\<lambda>x. IA.to_int (max_list1 (f x))) ss)"
    using ss by (auto simp: o_def int_hom.hom_max_list1 1)
  also have "\<dots> = max_list1 (map (\<lambda>s. max_list1 (map IA.to_int (f s))) ss)"
    apply (rule arg_cong[of _ _ max_list1])
    apply (rule map_cong[OF refl])
    apply (rule hom_max_list1)
    by (auto simp: o_def f_def dest!: subsetD[OF eval_via_IA_range])
  also have "\<dots> = max_list1 (map max_list1 (map (map IA.to_int) (map f ss)))"
    by (auto simp: o_def)
  also have "\<dots> = max_list1 (concat (map (map IA.to_int \<circ> f) ss))"
    apply (subst max_list1_concat[symmetric])
    using ss by (auto simp: f_def eval_via_IA_def)
  also have "\<dots> = max_list1 (concat (map (map (IA.to_int \<circ> (\<lambda>t. IA.eval t (to_IA_assignment \<alpha>)))) (map to_IA ss)))"
    by (auto simp: o_def f_def eval_via_IA_def)
  also have "\<dots> = max_list1 (map IA.to_int (f (Fun MaxF ss)))"
    apply (unfold map_concat[symmetric])
    by (auto simp: o_def f_def eval_via_IA_def ss)
  also have "\<dots> = IA.to_int (max_list1 (f (Fun MaxF ss)))"
    by (rule hom_max_list1[symmetric], auto simp: f_def dest!: subsetD[OF eval_via_IA_range])
  finally show ?case.
qed (auto simp: f_def eval_via_IA_def bot_nat_def)

definition le_via_IA where "le_via_IA s t \<equiv>
  (\<And>\<^sub>f x \<leftarrow> vars_term_list s @ vars_term_list t. IA.const 0 \<le>\<^sub>I\<^sub>A IA.var x) \<longrightarrow>\<^sub>f
  (\<And>\<^sub>f s' \<leftarrow> to_IA s. \<Or>\<^sub>f t' \<leftarrow> to_IA t. s' \<le>\<^sub>I\<^sub>A t')"

lemma formula_le_via_IA [intro!]: "IA.formula (le_via_IA s t)"
  by (auto simp: le_via_IA_def less_Suc_eq dest: to_IA_has_type)

lemma le_via_IA:
  assumes "\<Turnstile>\<^sub>I\<^sub>A le_via_IA s t" shows "s \<le>\<^sub>\<A> t"
proof
  fix \<alpha> :: "'a \<Rightarrow> nat"
  let ?\<alpha> = "to_IA_assignment \<alpha>"
  let ?vs = "vars_term_list s @ vars_term_list t"
  have "\<And>x. IA.satisfies ?\<alpha> (formula.Atom (Fun IA.LeF [Fun (IA.ConstF 0) [], Var (x, IA.IntT)]))"
    by (simp add:to_IA_assignment_def)
  hence a:"IA.satisfies ?\<alpha> (\<And>\<^sub>f x \<leftarrow> ?vs. IA.const 0 \<le>\<^sub>I\<^sub>A IA.var x)" by auto
  note sat = IA.validD[OF assms to_IA_assignment, of \<alpha>, unfolded le_via_IA_def IA.satisfies_or]
  note sat = sat[unfolded IA.satisfies_not]
  with a have "\<forall>s' \<in> set (to_IA s). \<exists>t' \<in> set (to_IA t).
    IA.eval s' (to_IA_assignment \<alpha>) \<le> IA.eval t' (to_IA_assignment \<alpha>)"
    by (auto simp: le_via_IA_def IA.to_int_iff[OF to_IA_assignment to_IA_has_type to_IA_has_type] elim!: ballE)
  then have "max_list1 (eval_via_IA s \<alpha>) \<le> max_list1 (eval_via_IA t \<alpha>)"
    by (unfold max_list1_as_Max eval_via_IA_def, subst Max_le_Max, auto)
  then have "int (\<lbrakk>s\<rbrakk> \<alpha>) \<le> int (\<lbrakk>t\<rbrakk> \<alpha>)"
    unfolding eval_via_IA
    by (metis IA_Int_hom.hom_le_hom IA.val.sel(1) imageE max_list1_eval_via_IA_range)
  then show "\<lbrakk>s\<rbrakk> \<alpha> \<le> \<lbrakk>t\<rbrakk> \<alpha>" by auto
qed

definition less_via_IA where "less_via_IA s t \<equiv>
  (\<And>\<^sub>f x \<leftarrow> vars_term_list s @ vars_term_list t. IA.const 0 \<le>\<^sub>I\<^sub>A IA.var x) \<longrightarrow>\<^sub>f
  (\<And>\<^sub>f s' \<leftarrow> to_IA s. \<Or>\<^sub>f t' \<leftarrow> to_IA t. s' <\<^sub>I\<^sub>A t')"

lemma formula_less_via_IA [intro!]: "IA.formula (less_via_IA s t)" 
    by (auto simp: less_via_IA_def less_Suc_eq dest: to_IA_has_type)

lemma less_via_IA:
  assumes "\<Turnstile>\<^sub>I\<^sub>A less_via_IA s t" shows "s <\<^sub>\<A> t"
proof
  fix \<alpha> :: "'a \<Rightarrow> nat"
  let ?\<alpha> = "to_IA_assignment \<alpha>"
  let ?vs = "vars_term_list s @ vars_term_list t"
  have "\<And>x. IA.satisfies ?\<alpha> (IA.const 0 \<le>\<^sub>I\<^sub>A IA.var x)"
    by (simp add:to_IA_assignment_def)
  hence a:"IA.satisfies ?\<alpha> (\<And>\<^sub>f x \<leftarrow> ?vs. IA.const 0 \<le>\<^sub>I\<^sub>A IA.var x)" by auto
  note sat = IA.validD[OF assms to_IA_assignment, of \<alpha>, unfolded less_via_IA_def IA.satisfies_or]
  note sat = sat[unfolded IA.satisfies_not]
  with a have "(\<forall>s' \<in> set (to_IA s). \<exists>t' \<in> set (to_IA t). IA.eval s' ?\<alpha> < IA.eval t' ?\<alpha>)"
  using IA.to_int_iff[OF to_IA_assignment to_IA_has_type to_IA_has_type] 
    by (auto simp: less_via_IA_def IA.to_int_iff[OF to_IA_assignment to_IA_has_type to_IA_has_type] elim!: ballE)
  then have "max_list1 (eval_via_IA s \<alpha>) < max_list1 (eval_via_IA t \<alpha>)"
    by (unfold max_list1_as_Max eval_via_IA_def, subst Max_less_Max, auto)
  then have "int (\<lbrakk>s\<rbrakk> \<alpha>) < int (\<lbrakk>t\<rbrakk> \<alpha>)"
    unfolding eval_via_IA
    by (metis IA.less_IA_value_simps(3) IA.val.collapse(1) IA.val.discI(1) imageE max_list1_eval_via_IA_range)
  thus "\<lbrakk>s\<rbrakk> \<alpha> < \<lbrakk>t\<rbrakk> \<alpha>" by auto
qed

end


subsection \<open>Max-Polynomial Interpretations\<close>

text \<open>Now we encode arbitrary $F$-terms into the @{type max_poly.sig}-terms.\<close>

locale max_poly_encoding = encoded_ordered_algebra
  where less_eq = "(\<le>)" and less = "(<)" and I = max_poly.I
begin

sublocale encoded_wf_weak_mono_algebra where less_eq = "(\<le>)" and less = "(<)" and I = max_poly.I
  by (unfold_locales, fact max_poly.append_Cons_le_append_Cons)

lemmas redpair = redpair.redpair_axioms

lemma less_term_via_IA:
  assumes "\<Turnstile>\<^sub>I\<^sub>A max_poly.less_via_IA (encode s) (encode t)" shows "s <\<^sub>\<A> t"
  using max_poly.less_via_IA[OF assms] by (auto intro!: less_termI)

lemma less_eq_term_via_IA:
  assumes "\<Turnstile>\<^sub>I\<^sub>A max_poly.le_via_IA (encode s) (encode t)" shows "s \<le>\<^sub>\<A> t"
  using max_poly.le_via_IA[OF assms] by (auto intro!: less_eq_termI)

lemma simple_arg_pos_via_IA: (* TODO: one can syntactically check simple_arg_pos. *)
  assumes "\<Turnstile>\<^sub>I\<^sub>A max_poly.le_via_IA (Var i) (E f n)"
  shows "simple_arg_pos (rel_of (\<ge>\<^sub>\<A>)) (f,n) i"
proof (intro simple_arg_posI, unfold mem_Collect_eq prod.case, intro less_eq_termI)
  fix ts :: "('a,'b) term list" and \<alpha>
  assume n: "length ts = n" and i_n: "i < n"
  note max_poly.le_via_IA[OF assms]
  then
  have "\<alpha> i \<le> max_poly.eval (E f n) \<alpha>" for \<alpha> by auto
  note this[of "\<lambda>i. \<lbrakk>ts!i\<rbrakk>\<alpha>"]
  also have "target.eval (E f n) (\<lambda>i. \<lbrakk>ts ! i\<rbrakk> \<alpha>) = \<lbrakk>Fun f ts\<rbrakk> \<alpha>"
    using n encoder.var_domain by auto
  finally show "\<lbrakk>ts ! i\<rbrakk> \<alpha> \<le> \<lbrakk>Fun f ts\<rbrakk> \<alpha>".
qed

lemma ss_fun_arg_via_IA: (* TODO: one can syntactically check simple_arg_pos. *)
  assumes "\<Turnstile>\<^sub>I\<^sub>A max_poly.less_via_IA (Var i) (E f n)"
  shows "simple_arg_pos (rel_of (>\<^sub>\<A>)) (f,n) i"
proof (intro simple_arg_posI, unfold mem_Collect_eq prod.case, intro less_termI)
  fix ts :: "('a,'b) term list" and \<alpha>
  assume n: "length ts = n" and i_n: "i < n"
  note max_poly.less_via_IA[OF assms]
  then
  have "\<alpha> i < max_poly.eval (E f n) \<alpha>" for \<alpha> by auto
  note this[of "\<lambda>i. \<lbrakk>ts!i\<rbrakk>\<alpha>"]
  also have "target.eval (E f n) (\<lambda>i. \<lbrakk>ts ! i\<rbrakk> \<alpha>) = \<lbrakk>Fun f ts\<rbrakk> \<alpha>"
    using n encoder.var_domain by auto
  finally show "\<lbrakk>ts ! i\<rbrakk> \<alpha> < \<lbrakk>Fun f ts\<rbrakk> \<alpha>".
qed

end

end
