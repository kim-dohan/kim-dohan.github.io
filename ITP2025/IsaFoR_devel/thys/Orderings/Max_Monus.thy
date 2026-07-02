(*
Author:  Akihisa Yamada (2016-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Max_Monus
  imports Ordered_Algebra
    Integer_Arithmetic
    Polynomial_Interpolation.Ring_Hom
    "HOL-Algebra.Ring"
    Max_Polynomial_Aux
begin

section \<open>max-monus interpretation, a variant of max-polynomial\<close>

text \<open>NOTE: it is impossible to unify max_monus with max_poly, due to the presence of product operation\<close>

text \<open>We implement max-monus interpretations as an instance of @{locale encoded_algebra}.
  As a target algebra, we introduce a $G$-algebra where $G = \{+,\times,\max\}$.\<close>

locale max_monus_locale
begin

datatype sig = ConstF nat | SumF | MaxF | MaxExtF nat "(int \<times> nat) list"

text \<open>Product f(x_1, ..., x_n) = x_1 * ... * x_n must not be included because flattening of max is unsound:
max {0, x - 1} * max {0, x - 1} is flattened to max{0 * 0, 0 * (x-1), (x-1) * 0, (x-1)*(x-1)} = max{0,(x-1)^2}.
However, when x = 0
max {0, x - 1} * max {0, x - 1} = 0 \<noteq> 1 = max {0, (x-1)^2}.
\<close>

primrec I where
  "I (ConstF n) = (\<lambda>x. n)"
| "I SumF = sum_list"
| "I MaxF = max_list"
| "I (MaxExtF c0 cds) = (max_ext_list c0 cds)"

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
  next
    case (MaxExtF c0 cds)
    then show ?thesis
      using max_ext_list_weakly_mono[of b a c0 cds ls rs] ba by fastforce
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
| "simplify (Fun MaxF ss) = (
    let ss' = filter (\<lambda>s. s \<noteq> const 0) (map simplify ss) in
    case ss' of [] \<Rightarrow> const 0 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun MaxF ss'
  )"
(* TODO: remove c + d * e if c < m and d = 0 where m is the maximum of cs *)
| "simplify (Fun (MaxExtF c0 cds) ss) = (case (map simplify ss) of [] \<Rightarrow> const c0 | ss' \<Rightarrow> Fun (MaxExtF c0 cds) ss')"

lemma list_caseE:
  assumes "case xs of [] \<Rightarrow> a | x # ys \<Rightarrow> b x ys"
    and "xs = [] \<Longrightarrow> a \<Longrightarrow> thesis"
    and "\<And>x ys. xs = x#ys \<Longrightarrow> b x ys \<Longrightarrow> thesis"
  shows thesis
  using assms
  by (cases xs, auto)

lemma vars_term_simplify: "vars_term (simplify s) \<subseteq> vars_term s"
proof (rule subsetI, induct s rule: simplify.induct)
  case IH: (3 ss)
  from IH.prems have "x \<in> \<Union>(vars_term ` set (filter (\<lambda>s. s \<noteq> const 0) (map simplify ss)))"
    by (auto simp: Let_def list.case_distrib simp del: set_filter elim!: list_caseE)
  also have "\<dots> \<subseteq> vars_term (Fun SumF ss)" using IH.hyps by auto
  finally show ?case.
next
  case IH: (4 ss)
  from IH.prems have "x \<in> \<Union>(vars_term ` set (filter (\<lambda>s. s \<noteq> const 0) (map simplify ss)))"
    by (auto simp: Let_def list.case_distrib simp del: set_filter elim!: list_caseE)
  also have "\<dots> \<subseteq> vars_term (Fun MaxF ss)" using IH.hyps by auto
  finally show ?case.
next
  case IH: (5 c0 cds ss)
  from IH.prems have "x \<in> \<Union>(vars_term ` set (map simplify ss))"
    by (auto simp: Let_def list.case_distrib simp del: set_filter elim!: list_caseE)
  also have "\<dots> \<subseteq> vars_term (Fun (MaxExtF c0 cds) ss)" using IH.hyps by auto
  finally show ?case .
qed auto

lemma eval_SumF_filter_0:
  "\<lbrakk>Fun SumF (filter (\<lambda>s. s \<noteq> const 0) ss)\<rbrakk> = \<lbrakk>Fun SumF ss\<rbrakk>"
  by (auto intro!: ext sum_list_map_filter)

lemma eval_MaxF_filter_0:
  "\<lbrakk>Fun MaxF (filter (\<lambda>s. s \<noteq> const 0) ss)\<rbrakk> = \<lbrakk>Fun MaxF ss\<rbrakk>"
  by (auto intro!: ext max_list_map_filter)

lemma simplify_lemma:
  "\<lbrakk>case ss of [] \<Rightarrow> const 0 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun SumF ss\<rbrakk> = \<lbrakk>Fun SumF ss\<rbrakk>"
  "\<lbrakk>case ss of [] \<Rightarrow> const 0 | [s] \<Rightarrow> s | _ \<Rightarrow> Fun MaxF ss\<rbrakk> = \<lbrakk>Fun MaxF ss\<rbrakk>"
  "\<lbrakk>case ss of [] \<Rightarrow> const c0 | ss' \<Rightarrow> Fun (MaxExtF c0 cds) ss'\<rbrakk> = \<lbrakk>Fun (MaxExtF c0 cds) ss\<rbrakk>"
  by (atomize(full), cases ss rule: list_3_cases, auto simp: bot_nat_def)

lemma simplify [simp]: "\<lbrakk>simplify s\<rbrakk> = \<lbrakk>s\<rbrakk>"
proof (intro ext, induct s rule: simplify.induct)
next
  case (3 ss \<alpha>)
  then show ?case by (auto simp: Let_def simplify_lemma eval_SumF_filter_0 cong: map_cong)
next
  case (4 ss \<alpha>)
  then show ?case by (auto simp: Let_def simplify_lemma eval_MaxF_filter_0 o_def intro:max_list_cong)
next
  case (5 c0 cds ss \<alpha>)
  then have *: "map (\<lambda>x. int (\<lbrakk>local.simplify x\<rbrakk> \<alpha>)) ss = map (\<lambda>x. int (\<lbrakk>x\<rbrakk> \<alpha>)) ss" by auto
  show ?case by (simp add: simplify_lemma o_def *)
qed (auto simp: simplify_lemma)

end


derive compare max_monus_locale.sig
global_interpretation max_monus: max_monus_locale .

instantiation max_monus.sig :: showl
begin

primrec showsl_sig :: "max_monus.sig \<Rightarrow> showsl"
  where
    "showsl_sig (max_monus.ConstF n) = showsl n"
  | "showsl_sig (max_monus.MaxF) = showsl_lit (STR ''max'')"
  | "showsl_sig (max_monus.SumF) = showsl_lit (STR ''sum'')"
  | "showsl_sig (max_monus.MaxExtF c0 cds) = showsl_lit (STR ''maxext'')" (* TODO: print more *)

definition "showsl_list (xs :: max_monus.sig list) = default_showsl_list showsl xs"

instance ..

end


subsection \<open>Translation to Integer Arithmetic\<close>

context max_monus_locale
begin

definition madd_IA where
  "madd_IA c d e = Fun (IA.SumF 2) [IA.const c, Fun (IA.ProdF 2) [IA.const d, e]]"

thm less_2_cases[unfolded numeral_2_eq_2]

lemma madd_IA_has_type: assumes "IA.has_type e IA.IntT"
  shows "IA.has_type (madd_IA c d e) IA.IntT"
  using assms 
  by (auto simp: madd_IA_def dest!: less_2_cases[unfolded numeral_2_eq_2])

fun madd_IA_list :: "(int \<times> nat) list \<Rightarrow> 'v IA.exp list \<Rightarrow> 'v IA.exp list" where
  "madd_IA_list _ [] = []" |
  "madd_IA_list [] (e # es) = madd_IA 0 1 e # (madd_IA_list [] es)" | (* default: 1 * x + 0 *)
  "madd_IA_list ((c, d) # cds) (e # es) = madd_IA c d e # (madd_IA_list cds es)"

lemma madd_IA_list_has_type:
  "(\<forall> e \<in> set es. IA.has_type e IA.IntT) \<longrightarrow> e \<in> set (madd_IA_list cds es) \<longrightarrow> IA.has_type e IA.IntT"
  by (induction cds es rule: madd_IA_list.induct, auto intro: madd_IA_has_type)

primrec to_IA :: "(sig,'v) term \<Rightarrow> 'v IA.exp list" where
  "to_IA (Var x) = [IA.var x]"
| "to_IA (Fun f ss) = (case f of ConstF n \<Rightarrow> [IA.const n]
    | MaxF \<Rightarrow> if ss = [] then [IA.const 0] else concat (map to_IA ss)
    | MaxExtF c0 cds \<Rightarrow> if ss = [] then [IA.const c0] else (IA.const c0) # concat (map (madd_IA_list cds) (product_lists (map to_IA ss)))
    | SumF \<Rightarrow>
      if ss = [] then [Fun (IA.SumF 0) []]
      else map (Fun (IA.SumF (length ss))) (product_lists (map to_IA ss))
  )"

lemma to_IA_induct[case_names Var ConstF SumF MaxF MaxExtF SumF0 MaxF0 MaxExtF0]:
  assumes "\<And>x. P (Var x)"
    and "\<And>n ss. P (Fun (ConstF n) ss)"
    and "\<And>ss. ss \<noteq> [] \<Longrightarrow> (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (Fun SumF ss)"
    and "\<And>ss. ss \<noteq> [] \<Longrightarrow> (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (Fun MaxF ss)"
    and "\<And>ss c0 cds. ss \<noteq> [] \<Longrightarrow> (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (Fun (MaxExtF c0 cds) ss)"
    and "P (Fun SumF [])"
    and "P (Fun MaxF [])"
    and "\<And> c0 cds. P (Fun (MaxExtF c0 cds) [])"
  shows "P s"
  by (insert assms, induction_schema, metis term.exhaust sig.exhaust, lexicographic_order)


lemma to_IA_has_type:
  "s' \<in> set (to_IA s) \<Longrightarrow> IA.has_type s' IA.IntT"
  apply (induct s arbitrary:s' rule: to_IA_induct, auto simp:in_set_product_lists_length product_lists_set)
  apply (metis length_map list_all2_nthD2 nth_map nth_mem)
  using madd_IA_list_has_type length_map list_all2_nthD2 nth_map nth_mem
  apply (smt (verit, del_insts) in_set_conv_nth list_all2_conv_all_nth)
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

lemma madd_IA_madd_0_1:
  "IA.to_int (IA.eval (max_monus.madd_IA 0 1 e) \<alpha>) = IA.to_int (IA.eval e \<alpha>)"
  unfolding madd_IA_def by simp

lemma madd_IA_madd:
  "IA.to_int (IA.eval (max_monus.madd_IA c d e) \<alpha>) = madd c d (IA.to_int (IA.eval e \<alpha>))"
  unfolding madd_IA_def by auto

lemma madd_IA_list_madd_list:
  "map (\<lambda> e. IA.to_int (IA.eval e \<alpha>)) (madd_IA_list cds es) = madd_list cds (map (\<lambda> e. IA.to_int (IA.eval e \<alpha>)) es)"
  by (induction cds es rule: madd_IA_list.induct, auto simp: madd_IA_madd_0_1 madd_IA_madd)

lemma madd_IA_list_madd_list_ext: "(map (IA.to_int \<circ> (\<lambda>t. IA.eval t \<alpha>)) \<circ>\<circ> madd_IA_list) cds = 
  (madd_list cds) \<circ> map (\<lambda> e. IA.to_int (IA.eval e \<alpha>))"
  using madd_IA_list_madd_list fun_eq_iff by fastforce

end

context max_monus_locale
begin

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
  also have "\<dots> = max_list1 (map sum_list (map (map (IA.to_int \<circ> (\<lambda>t. IA.eval t (to_IA_assignment \<alpha>)))) (product_lists (map to_IA ss))))"
    by (subst product_lists_map_map, rule refl) 
  also have "\<dots> = max_list1 (map IA.to_int (f (Fun SumF ss)))"
    by (auto simp: o_def f_def eval_via_IA_def ss)
  also have "\<dots> = IA.to_int (max_list1 (f (Fun SumF ss)))"
    by (rule hom_max_list1[symmetric], auto simp: f_def dest!: subsetD[OF eval_via_IA_range])
  finally show ?case.
next
  case (MaxF ss)
  note ss = this(1) and 1 = map_ext[OF this(2)[unfolded atomize_imp]]
  have non_empty: "[] \<notin> set (map (map IA.to_int) (map f ss))"
    unfolding f_def by auto
  have "\<lbrakk>Fun MaxF ss\<rbrakk>\<alpha> = max_list1 (map (\<lambda>s. \<lbrakk>s\<rbrakk>\<alpha>) ss)"
    using ss by (auto simp: max_list_as_max_list1)
  also have "int \<dots> = max_list1 (map (\<lambda>s. int (\<lbrakk>s\<rbrakk>\<alpha>)) ss)"
    by (auto simp: ss o_def int_hom.hom_max_list1)
  also have "\<dots> = max_list1 (map (\<lambda>x. IA.to_int (max_list1 (f x))) ss)"
    using ss by (auto simp: 1)
  also have "\<dots> = max_list1 (map (\<lambda>s. max_list1 (map IA.to_int (f s))) ss)"
    apply (rule arg_cong[of _ _ max_list1])
    apply (rule map_cong[OF refl])
    apply (rule hom_max_list1)
    by (auto simp: o_def f_def dest!: subsetD[OF eval_via_IA_range])
  also have "\<dots> = max_list1 (map max_list1 (map (map IA.to_int) (map f ss)))"
    by (auto simp: o_def)
  also have "\<dots> = max_list1 (concat (map (map IA.to_int) (map f ss)))"
    by (subst max_list1_concat[symmetric, OF non_empty], rule refl)
  also have "\<dots> = max_list1 (concat (map (map IA.to_int \<circ> f) ss))"
    by auto
  also have "\<dots> = max_list1 (concat (map (map (IA.to_int \<circ> (\<lambda>t. IA.eval t (to_IA_assignment \<alpha>)))) (map to_IA ss)))"
    by (auto simp: o_def f_def eval_via_IA_def)
  also have "\<dots> = max_list1 (map (IA.to_int \<circ> (\<lambda>t. IA.eval t (to_IA_assignment \<alpha>))) (concat (map to_IA ss)))"
    by (subst map_concat[symmetric], rule refl)
  also have "\<dots> = max_list1 (map IA.to_int (f (Fun MaxF ss)))"
    by (auto simp: o_def f_def eval_via_IA_def ss)
  also have "\<dots> = IA.to_int (max_list1 (f (Fun MaxF ss)))"
    by (rule hom_max_list1[symmetric], auto simp: f_def dest!: subsetD[OF eval_via_IA_range])
  finally show ?case.
next
  case (MaxExtF ss c0 cds)
  note ss = this(1) and 1 = map_ext[OF this(2)[unfolded atomize_imp]]
  have map_f_ss: "[] \<notin> set (map (map IA.to_int) (map f ss))" using ss unfolding f_def by auto
  let ?eval = "\<lambda>t. IA.eval t (to_IA_assignment \<alpha>)"
  let ?eval_int = "IA.to_int \<circ> ?eval"
  have *: "max_list1 (concat (map (madd_list cds) (map (map IA.to_int) (product_lists (map f ss)))))
     = max_list1 (map ?eval_int (concat (map (madd_IA_list cds) (product_lists (map to_IA ss)))))"
  proof -
    have m: "concat (map ((madd_list cds \<circ>\<circ> map) IA.to_int) (product_lists (map (\<lambda>s. map ?eval (to_IA s)) ss)))
      =  (concat (map ((madd_list cds \<circ>\<circ> map) ?eval_int) (product_lists (map to_IA ss))))"
    proof -
      have a: "map (\<lambda>s. map ?eval (to_IA s)) ss
        = map (map ?eval) (map to_IA ss)"
        by simp
      have b: "product_lists (map (map ?eval) (map to_IA ss)) =
        map (map ?eval) (product_lists (map to_IA ss))"
        using product_lists_map_map[of ?eval "map to_IA ss"] by simp
      have "concat (map ((madd_list cds \<circ>\<circ> map) IA.to_int) (product_lists (map (\<lambda>s. map ?eval (to_IA s)) ss))) =
        concat (map ((madd_list cds \<circ>\<circ> map) IA.to_int) (product_lists (map (map ?eval) (map to_IA ss))))"
        by (subst a[symmetric], rule refl)
      also have "\<dots> = 
         concat (map ((madd_list cds \<circ>\<circ> map) IA.to_int) (map (map ?eval) (product_lists (map to_IA ss))))"
        by (subst product_lists_map_map[of ?eval "map to_IA ss"], rule refl)
      also have "\<dots> =
        concat (map ((madd_list cds \<circ>\<circ> map) IA.to_int \<circ> (map ?eval)) (product_lists (map to_IA ss)))"
        by (subst map_map, rule refl)
      also have "\<dots> =
        concat (map ((madd_list cds \<circ>\<circ> map) (IA.to_int \<circ> ?eval)) (product_lists (map to_IA ss)))"
        by (metis comp_apply list.map_comp)
      also have "IA.to_int \<circ> ?eval = (\<lambda>e. IA.to_int (IA.eval e (to_IA_assignment \<alpha>)))" by fastforce
      ultimately show ?thesis by argo
    qed
    show ?thesis
      apply (simp add: product_lists_map_map map_concat f_def madd_IA_list_madd_list_ext)
      unfolding eval_via_IA_def using m by (smt (verit, ccfv_SIG) fun_comp_eq_conv)
  qed
  have "\<lbrakk>Fun (MaxExtF c0 cds) ss\<rbrakk>\<alpha> = max_ext_list c0 cds (map (\<lambda>s. (\<lbrakk>s\<rbrakk> \<alpha>)) ss)" by simp
  also have "int \<dots> = max_ext_list' c0 cds (map (\<lambda>s. int (\<lbrakk>s\<rbrakk> \<alpha>)) ss)"
    by (simp add: max_ext_list'_nat o_def)
  also have "... = max_ext_list' c0 cds (map (\<lambda>x. IA.to_int (max_list1 (f x))) ss)"
    by (simp add: 1)
  also have "\<dots> = max_ext_list' c0 cds  (map (\<lambda>s. max_list1 (map IA.to_int (f s))) ss)"
    apply (rule arg_cong[of _ _ "max_ext_list' c0 cds"])
    apply (rule map_cong[OF refl])
    apply (rule hom_max_list1)
    by (auto simp: o_def f_def dest!: subsetD[OF eval_via_IA_range])
  also have "\<dots> =  max_ext_list' c0 cds (map max_list1 (map (map IA.to_int) (map f ss)))"
    by (auto simp: o_def)
  also have "\<dots> = max_list1 (int c0 # concat (map (madd_list cds) (product_lists (map (map IA.to_int) (map f ss)))))"
    by (rule max_ext_list'_max_list1[OF map_f_ss, of c0 cds])
  also have "\<dots> = max_list1 (int c0 # concat (map (madd_list cds) (map (map IA.to_int) (product_lists (map f ss)))))"
    using product_lists_map_map by metis
  also have "\<dots> = ord_class.max (int c0) (max_list1 (concat (map (madd_list cds) (map (map IA.to_int) (product_lists (map f ss))))))"
  proof -
    have "\<not> (\<forall>xs\<in>set (product_lists (map f ss)). madd_list cds (map IA.to_int xs) = [])"
    proof -
      have a: "[] \<notin> set (map f ss)" unfolding f_def using eval_via_IA_eq_NilE
        by (metis ex_map_conv)
      then obtain xs where b: "xs \<in> set (product_lists (map f ss))" using ss map_f_ss by fastforce
      moreover 
      have "xs \<noteq> []"
      proof -
        have "map f ss \<noteq> []" unfolding f_def using ss eval_via_IA_eq_NilE by blast
        with a b show ?thesis
          by (metis List.last_in_set in_set_conv_nth in_set_product_lists_length in_set_simps(3))
      qed
      ultimately have "\<exists> xs\<in>set (product_lists (map f ss)). madd_list cds (map IA.to_int xs) \<noteq> []"
        by (metis list.exhaust list.map_disc_iff madd_list_non_empty')
      then show ?thesis by auto
    qed
    then show ?thesis by auto 
  qed
  also have "\<dots> = ord_class.max (int c0) (max_list1 (map ?eval_int (concat (map (madd_IA_list cds) (product_lists (map to_IA ss))))))"
    using * by argo
  also have "\<dots> = max_list1 (map IA.to_int (f (Fun (MaxExtF c0 cds) ss)))"
  proof -
    have "(\<forall>xs\<in>set (product_lists (map to_IA ss)). madd_IA_list cds xs \<noteq> [])"
    proof (intro ballI)
      fix xs
      assume a: "xs \<in> set (product_lists (map to_IA ss))"
      have "[] \<notin> set (map to_IA ss)" using ss
        by (metis ex_map_conv to_IA_eq_NilE)
      then have "xs \<noteq> []" using ss a
        by (metis List.last_in_set in_set_conv_nth in_set_product_lists_length in_set_simps(3) list.map_disc_iff)
      then show "madd_IA_list cds xs \<noteq> []"
        using max_monus_locale.madd_IA_list.elims by blast
    qed
    moreover
    have " [] \<notin> to_IA ` set ss"
      using ss by (metis image_iff to_IA_eq_NilE)
    ultimately show ?thesis by (simp add: o_def f_def eval_via_IA_def ss)
  qed
  also have "... = IA.to_int (max_list1 (f (Fun (MaxExtF c0 cds) ss)))"
    by (rule hom_max_list1[symmetric], auto simp: f_def dest!: subsetD[OF eval_via_IA_range])
  finally show ?case .
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


subsection \<open>Max-Monus Interpretations\<close>

text \<open>Now we encode arbitrary $F$-terms into the @{type max_monus.sig}-terms.\<close>

locale max_monus_encoding = encoded_ordered_algebra
  where less_eq = "(\<le>)" and less = "(<)" and I = max_monus.I
begin

sublocale encoded_wf_weak_mono_algebra where less_eq = "(\<le>)" and less = "(<)" and I = max_monus.I
  by (unfold_locales, fact max_monus.append_Cons_le_append_Cons)

lemmas redpair = redpair.redpair_axioms

lemma less_term_via_IA:
  assumes "\<Turnstile>\<^sub>I\<^sub>A max_monus.less_via_IA (encode s) (encode t)" shows "s <\<^sub>\<A> t"
  using max_monus.less_via_IA[OF assms] by (auto intro!: less_termI)

lemma less_eq_term_via_IA:
  assumes "\<Turnstile>\<^sub>I\<^sub>A max_monus.le_via_IA (encode s) (encode t)" shows "s \<le>\<^sub>\<A> t"
  using max_monus.le_via_IA[OF assms] by (auto intro!: less_eq_termI)

lemma simple_arg_pos_via_IA: (* TODO: one can syntactically check simple_arg_pos. *)
  assumes "\<Turnstile>\<^sub>I\<^sub>A max_monus.le_via_IA (Var i) (E f n)"
  shows "simple_arg_pos (rel_of (\<ge>\<^sub>\<A>)) (f,n) i"
proof (intro simple_arg_posI, unfold mem_Collect_eq prod.case, intro less_eq_termI)
  fix ts :: "('a,'b) term list" and \<alpha>
  assume n: "length ts = n" and i_n: "i < n"
  note max_monus.le_via_IA[OF assms]
  then
  have "\<alpha> i \<le> max_monus.eval (E f n) \<alpha>" for \<alpha> by auto
  note this[of "\<lambda>i. \<lbrakk>ts!i\<rbrakk>\<alpha>"]
  also have "target.eval (E f n) (\<lambda>i. \<lbrakk>ts ! i\<rbrakk> \<alpha>) = \<lbrakk>Fun f ts\<rbrakk> \<alpha>"
    using n encoder.var_domain by auto
  finally show "\<lbrakk>ts ! i\<rbrakk> \<alpha> \<le> \<lbrakk>Fun f ts\<rbrakk> \<alpha>".
qed

lemma ss_fun_arg_via_IA: (* TODO: one can syntactically check simple_arg_pos. *)
  assumes "\<Turnstile>\<^sub>I\<^sub>A max_monus.less_via_IA (Var i) (E f n)"
  shows "simple_arg_pos (rel_of (>\<^sub>\<A>)) (f,n) i"
proof (intro simple_arg_posI, unfold mem_Collect_eq prod.case, intro less_termI)
  fix ts :: "('a,'b) term list" and \<alpha>
  assume n: "length ts = n" and i_n: "i < n"
  note max_monus.less_via_IA[OF assms]
  then
  have "\<alpha> i < max_monus.eval (E f n) \<alpha>" for \<alpha> by auto
  note this[of "\<lambda>i. \<lbrakk>ts!i\<rbrakk>\<alpha>"]
  also have "target.eval (E f n) (\<lambda>i. \<lbrakk>ts ! i\<rbrakk> \<alpha>) = \<lbrakk>Fun f ts\<rbrakk> \<alpha>"
    using n encoder.var_domain by auto
  finally show "\<lbrakk>ts ! i\<rbrakk> \<alpha> < \<lbrakk>Fun f ts\<rbrakk> \<alpha>".
qed

end

end
