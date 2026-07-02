(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Checking Polynomial Growth of Matrices\<close>

text \<open>We combine the developed algorithms into a single check-function which
  decides polynomial growth of a matrix w.r.t. to a given degree.\<close>
 
theory Jordan_Normal_Form_Complexity_Approximation
imports                                    
  Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness
  Jordan_Normal_Form.Jordan_Normal_Form_Existence
  Jordan_Normal_Form.Complexity_Carrier
  Jordan_Normal_Form.Ring_Hom_Matrix
  Jordan_Normal_Form.Show_Matrix
  Jordan_Normal_Form.Shows_Literal_Matrix
  Perron_Frobenius.Check_Matrix_Growth
  Show.Show_Poly
  Show.Show_Real
  Certification_Monads.Check_Monad
begin

text \<open>We first try a cheap test whether we have the simple case: an upper-triangular matrix. 
  If the counting-ones criterion succeeds, then we are done. 
  Otherwise, we use the full version of the Perron-Frobenius theorem combined with 
  Jordan-block computation of specific roots of unity.\<close>

definition count_ones_check :: "real list \<Rightarrow> nat \<Rightarrow> bool" where
  "count_ones_check diag d \<equiv> ((\<forall> a \<in> set diag. let aa = abs a in aa \<le> 1 \<and> (aa = 1 \<longrightarrow> length (filter ((=) a) diag) \<le> d)))"

definition complexity_via_perron_frobenius :: "nat \<Rightarrow> real poly \<Rightarrow> real mat \<Rightarrow> bool" where
  "complexity_via_perron_frobenius d cp A = (nonneg_mat A \<and> check_matrix_complexity A cp (d - 1))"

lemma complexity_via_perron_frobenius: assumes A: "A \<in> carrier_mat n n"
  and res: "complexity_via_perron_frobenius d (char_poly A) A"
shows "\<exists>c1 c2. \<forall>k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (d - 1))"
proof -
  from res[unfolded complexity_via_perron_frobenius_def]
  have "nonneg_mat A" "check_matrix_complexity A (char_poly A) (d - 1)" by auto
  from check_matrix_complexity[OF A this] obtain c1 c2 where bnd: "\<And> k a. 
    a \<in> elements_mat (A ^\<^sub>m k) \<Longrightarrow> \<bar>a\<bar> \<le> c1 + c2 * real k ^ (d - 1)" by auto
  then show ?thesis unfolding norm_bound_elements_mat by auto
qed

definition combined_growth_check_real_mat :: "nat \<Rightarrow> real mat \<Rightarrow> showsl check" where
  "combined_growth_check_real_mat d A \<equiv>
    (if upper_triangular A \<and> count_ones_check (diag_mat A) d then succeed 
    else if complexity_via_perron_frobenius d (char_poly A) A then succeed else
      error (if nonneg_mat A then showsl_lit (STR ''matrix does not have intended growth rate'') 
        else showsl_lit (STR ''only non-negative matrices supported'')))
    <+? (\<lambda> s. showsl_lit (STR ''could not deduce that '') o showsl A o 
     showsl (STR '' in O(n^'') o showsl (d-1) o showsl_lit (STR '')\<newline>'') o s)" 

lemma combined_growth_check_real_mat: assumes A: "A \<in> carrier_mat n n"
  and res: "isOK(combined_growth_check_real_mat d A)"
shows "\<exists>c1 c2. \<forall>k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (d - 1))" 
proof -
  from res consider (ut) "upper_triangular A" "count_ones_check (diag_mat A) d"
    | (pf) "complexity_via_perron_frobenius d (char_poly A) A"
    unfolding combined_growth_check_real_mat_def Let_def
    by (auto split: if_splits)
  then show ?thesis
  proof (cases)
    case pf
    from complexity_via_perron_frobenius[OF A pf] show ?thesis .
  next
    case ut
    show ?thesis
      by (rule counting_ones_complexity[OF A], insert ut[unfolded count_ones_check_def Let_def], auto)
  qed
qed

definition mat_estimate_complexity_jb :: "nat \<Rightarrow> 'a :: large_real_ordered_semiring_1 mat \<Rightarrow> showsl check" where
  "mat_estimate_complexity_jb d A \<equiv> let B = mat\<^sub>\<real> A in do {
     check (dim_row A = dim_col A) (showsl_lit (STR ''expected square matrix but got \<newline>'') o showsl B);
     combined_growth_check_real_mat d B
   }"

lemma mat_estimate_complexity_jb_norm_bound: assumes *: "isOK(mat_estimate_complexity_jb d A)"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (mat\<^sub>\<real> A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (d - 1))"
proof -
  note * = *[unfolded mat_estimate_complexity_jb_def Let_def]
  from * obtain n where A: "A \<in> carrier_mat n n" unfolding carrier_mat_def by auto 
  from * have *: "isOK(combined_growth_check_real_mat d (mat\<^sub>\<real> A))" by auto
  let ?B = "mat\<^sub>\<real> A"
  from A have "?B \<in> carrier_mat n n" by auto
  from combined_growth_check_real_mat[OF this *] show ?thesis .
qed

context
  fixes A B C :: "'a :: large_real_ordered_semiring_1 mat" and n d e :: nat
  assumes *: "isOK(mat_estimate_complexity_jb e A)"
  and A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n" and C: "C \<in> carrier_mat n n"
  and d: "d = e - 1"
begin

lemma mat_estimate_complexity_jb_norm_bound_prod: 
  "\<exists> c. \<forall> k. k > 0 \<longrightarrow> norm_bound (mat\<^sub>\<real> B * (mat\<^sub>\<real> A ^\<^sub>m k * mat\<^sub>\<real> C)) (c * of_nat k ^ d)"
proof -
  let ?R = "mat\<^sub>\<real>"
  let ?A = "?R A"
  let ?B = "?R B"
  let ?C = "?R C"
  from mat_estimate_complexity_jb_norm_bound[OF *, folded d]
  obtain c1 c2 where bnd: "\<And> k. norm_bound (?A ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)" by auto
  define c where "c = (max c1 0) + (max c2 0)"
  from norm_bound_max[of ?B] obtain nb where nb: "norm_bound ?B nb" by auto
  from norm_bound_max[of ?C] obtain nc where nc: "norm_bound ?C nc" by auto
  let ?n = "of_nat n :: real"
  define b where "b = nb * nc * ?n * ?n * c"
  {
    fix k
    assume "k > (0 :: nat)"
    let ?k = "of_nat k :: real"
    have id: "nb * (c * real k ^ d * nc * real n) * real n = nb * nc * real n * real n * c * real k ^ d" 
      by simp
    from bnd[of k] have "norm_bound (?A ^\<^sub>m k) (c1 + c2 * ?k ^ d)" .
    have "c1 \<le> (max c1 0) * 1 ^ d" by auto
    also have "\<dots> \<le> (max c1 0) * ?k ^ d"
      by (rule mult_left_mono, insert \<open>k > 0\<close>, auto)
    also have "\<dots> + c2 * ?k ^ d \<le> c * ?k ^ d"
      unfolding c_def by (auto simp: field_simps intro: mult_right_mono)
    finally have "c1 + c2 * of_nat k ^ d \<le> c * of_nat k ^ d" by auto
    with bnd[of k] have "norm_bound (?A ^\<^sub>m k) (c * of_nat k ^ d)"
      unfolding norm_bound_def by force
    from norm_bound_mult[OF pow_carrier_mat _ this nc]
    have "norm_bound (?A ^\<^sub>m k * ?C) (c * ?k ^ d * nc * ?n)" using A C by auto
    from norm_bound_mult[OF _ mult_carrier_mat[OF pow_carrier_mat] nb this, of n n n]
    have "norm_bound (?B * (?A ^\<^sub>m k * ?C)) (b * ?k ^ d)" unfolding b_def using A B C
      by (simp only: ac_simps, simp add: id)
  } note bnd = this
  then show ?thesis by auto
qed

text \<open>This is the main result for real valued matrices.\<close>

lemma mat_estimate_complexity_jb_norm_sum_mat_prod: 
  "\<exists> c. \<forall> k. k > 0 \<longrightarrow> norm (sum_mat (mat\<^sub>\<real> B * (mat\<^sub>\<real> A ^\<^sub>m k * mat\<^sub>\<real> C))) \<le> (c * of_nat k ^ d)"
proof -
  let ?R = "mat\<^sub>\<real>"
  let ?A = "?R A"
  let ?B = "?R B"
  let ?C = "?R C"
  from mat_estimate_complexity_jb_norm_bound_prod obtain c
  where bnd: "\<And> k. k > 0 \<Longrightarrow> norm_bound (?B * (?A ^\<^sub>m k * ?C)) (c * of_nat k ^ d)" by auto
  let ?n = "of_nat n :: real"
  define b where "b = ?n * ?n * c" 
  {
    fix k
    let ?nn = "{0 ..< n}"
    let ?g = "\<lambda> i. c * of_nat k ^ d"
    assume "k > (0 :: nat)"    
    from bnd[OF this] have bnd: "norm_bound (?B * (?A ^\<^sub>m k * ?C)) (c * of_nat k ^ d)" .
    have "norm (sum_mat (?B * (?A ^\<^sub>m k * ?C))) \<le> sum ?g (?nn \<times> ?nn)"
      unfolding sum_mat_def
      by (rule order_trans[OF sum_norm_le[of _ _ ?g]],
      insert bnd A B C, auto simp: norm_bound_def)
    also have "\<dots> = b * of_nat k ^ d" unfolding b_def sum_constant by simp
    finally have "norm (sum_mat (?B * (?A ^\<^sub>m k * ?C))) \<le> b * of_nat k ^ d" by auto
  }
  then show ?thesis by auto
qed

text \<open>And via conversion, it also holds for matrices over the intended semiring.\<close>

lemma mat_estimate_complexity_jb_sum_mat_prod: 
  "\<exists> c. \<forall> k. k > 0 \<longrightarrow> sum_mat (B * (A ^\<^sub>m k * C)) \<le> (c * of_nat k ^ d)"
proof -  
  from mat_estimate_complexity_jb_norm_sum_mat_prod obtain c where 
    bnd: "\<And> k. k > 0 \<Longrightarrow> norm (sum_mat (mat\<^sub>\<real> B * (mat\<^sub>\<real> A ^\<^sub>m k * mat\<^sub>\<real> C))) \<le> (c * of_nat k ^ d)"
    by auto
  note mat_real_conv = 
    real_embedding.hom_sum_mat 
    real_embedding.mat_hom_pow [of _ n]
    real_embedding.mat_hom_mult[of _ n n]
  {
    fix k
    assume "k > (0 :: nat)"
    let ?sum = "sum_mat (B * (A ^\<^sub>m k * C))"
    have Ak: "A ^\<^sub>m k \<in> carrier_mat n n" using A by simp
    have AkC: "A ^\<^sub>m k * C \<in> carrier_mat n n" using Ak C by simp
    let ?ck = "c * of_nat k ^ d"
    let ?cck = "of_int \<lceil>c\<rceil> * of_nat k ^ d :: real"
    from bnd[OF \<open>k > 0\<close>] have "sum_mat (mat\<^sub>\<real> B * (mat\<^sub>\<real> A ^\<^sub>m k * mat\<^sub>\<real> C)) \<le> ?ck" by auto
    also have "sum_mat (mat\<^sub>\<real> B * (mat\<^sub>\<real> A ^\<^sub>m k * mat\<^sub>\<real> C)) = 
      real_of ?sum" 
      using Ak AkC A B C by (simp add: mat_real_conv)
    finally have "real_of ?sum \<le> ?ck" .
    from real_le[OF this] have le: "?sum \<le> of_int \<lceil>?ck\<rceil>" by auto
    have "?ck \<le> ?cck"
      by (rule mult_right_mono, auto)
    then have "\<lceil>?ck\<rceil> \<le> \<lceil>?cck\<rceil>" by linarith
    then have "of_int \<lceil>?ck\<rceil> \<le> ((of_int \<lceil>?cck\<rceil>) :: 'a)" 
      unfolding of_int_le_iff .
    with le have le: "?sum \<le> of_int \<lceil>?cck\<rceil>" by linarith
    also have "\<dots> = of_int \<lceil>c\<rceil> * of_nat k ^ d"
      by (metis (no_types, opaque_lifting) ceiling_of_int of_int_mult of_int_of_nat_eq of_nat_power)
    finally have "?sum \<le> of_int \<lceil>c\<rceil> * of_nat k ^ d" .
  }
  then show ?thesis by auto
qed
end

end
