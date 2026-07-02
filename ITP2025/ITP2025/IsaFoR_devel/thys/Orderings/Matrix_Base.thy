theory Matrix_Base
  imports
    Jordan_Normal_Form.Matrix_Comparison
    "Abstract-Rewriting.SN_Order_Carrier"
begin


lemma list_split_length_exI_trivial:
  assumes "length xs = length (a\<^sub>1@a\<^sub>2)"
  shows "\<exists> xs\<^sub>1 xs\<^sub>2. xs = xs\<^sub>1@xs\<^sub>2 \<and> length xs\<^sub>1 = length a\<^sub>1 \<and> length xs\<^sub>2 = length a\<^sub>2"
  by (rule exI[of _ "take (length a\<^sub>1) xs"], rule exI[of _ "drop (length a\<^sub>1) xs"],
    insert assms, auto)

lemma list_cons_length_exI_trivial:
  assumes "length xs = length (c#cs)"
  shows "\<exists>x xss. xs = x#xss \<and> length xss = length cs"
  using assms length_Suc_conv by auto


text \<open>Considering only matrices of integers and of dimension $n\times n$.\<close>



locale squared_int_mat =
  fixes n :: nat
begin

abbreviation Mat_gt :: "int mat \<Rightarrow> int mat \<Rightarrow> bool" (infix ">\<^sub>m" 50) where
   "Mat_gt \<equiv> mat_gt (>) n" 

definition interp_add_monoid_mat where
"interp_add_monoid_mat = monoid_mat TYPE(int) n n"

definition interp_mul_monoid_mat :: "int mat monoid" where
"interp_mul_monoid_mat = \<lparr>carrier = carrier_mat n n, mult=(*), one=1\<^sub>m n\<rparr>"

definition interp_ring_mat where
"interp_ring_mat = ring_mat TYPE(int) n"


lemma add_monoid_mat_is_submonoid: "submonoid (carrier_mat n n) interp_add_monoid_mat"
  unfolding interp_add_monoid_mat_def monoid_mat_def
  using add_carrier_mat zero_carrier_mat by (simp add: submonoid_def)

lemma mul_monoid_mat_is_submonoid: "submonoid (carrier_mat n n) interp_mul_monoid_mat"
  unfolding interp_mul_monoid_mat_def
  using mult_carrier_mat one_carrier_mat by (simp add: submonoid_def)



interpretation inter_mat_monoid: monoid interp_mul_monoid_mat
  unfolding interp_mul_monoid_mat_def monoid_mat_def  
proof (unfold_locales, goal_cases)
  case (1 x y)
  then show ?case using mult_carrier_mat by simp
next
  case (2 x y z)
  then show ?case using assoc_mult_mat by simp
next
  case 3
  then show ?case using one_carrier_mat by simp
next
  case (4 x)
  then show ?case using left_mult_one_mat by simp
next
  case (5 x)
  then show ?case using right_mult_one_mat by simp
qed



text \<open>Zero matrix properties\<close>

lemma zero_minus: "(0\<^sub>m n n :: int mat) = -0\<^sub>m n n"
proof (standard, goal_cases)
  case (1 i j)
  then show ?case using index_zero_mat(1) by simp
qed auto


text \<open>Alternative definitions to matrix non-equality\<close>

lemma mat_neq_alt:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "A \<noteq> B = (\<exists>i j. i < n \<and> j < n \<and> A $$ (i,j) \<noteq> B $$ (i,j))"
  using assms by auto



text \<open>Alternative definitions to matrix multiplication and addition\<close>

lemma mat_mult_compo_alt:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
          "i < n" "j < n"
        shows "(A * B) $$ (i,j) = (\<Sum>k \<in> {0..< n}. A $$ (i,k) * B $$ (k,j))"
proof -
  have "(A * B) = mat (dim_row A) (dim_col B)
              (\<lambda>(i, j). \<Sum>ia = 0..<dim_vec (col B j). row A i $ ia * col B j $ ia)"
    unfolding scalar_prod_def times_mat_def
    by auto
  also have "\<dots> = mat n n
              (\<lambda>(i, j). \<Sum>ia = 0..< n. row A i $ ia * col B j $ ia)"
    using assms(1,2)
    by auto
  finally
  have "(A * B) $$ (i, j) = (\<Sum>ia = 0..< n. row A i $ ia * col B j $ ia)"
    using index_mat assms(3,4)
    by auto
  also have "\<dots> = (\<Sum>ia = 0..< n. A $$ (i, ia) * B $$ (ia, j))"
    using index_row(1) index_col(1) assms carrier_matD
    by auto
  finally
  show ?thesis.
qed

lemma mat_add_compo_alt:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
          "i < n" "j < n"
        shows "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
  using plus_mat_def index_mat assms carrier_matD by auto


lemma mat_minus_compo_alt:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
          "i < n" "j < n"
        shows "(A - B) $$ (i,j) = A $$ (i,j) - B $$ (i,j)"
  using minus_mat_def index_mat assms carrier_matD by auto



text \<open>Matrix equality equivalences\<close>


lemma mat_add_eq_minus: 
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A + B = C \<equiv> A = C - B"
proof -
  have carr: "A + B \<in> carrier_mat n n" "C - B \<in> carrier_mat n n"
    using assms by auto
  {
    assume as: "A + B = C"
    have "A = C - B"
    proof
      show "dim_row A = dim_row (C - B)" "dim_col A = dim_col (C - B)"
        using carr(2) assms(1) by auto
      {
        fix i j
        assume ij_p: "i < n" "j < n"
        then have "A $$ (i,j) + B $$ (i,j) = C $$ (i,j)"
          using as mat_add_compo_alt assms by auto
        then have "A $$ (i,j) = C $$ (i,j) - B $$ (i,j)"
          by auto
        then have "A $$ (i,j) = (C - B) $$ (i,j)"
          using mat_minus_compo_alt assms(2,3) ij_p by auto
      }
      then show "\<And>i j. i < dim_row (C - B) \<Longrightarrow> j < dim_col (C - B) \<Longrightarrow> A $$ (i, j) = (C - B) $$ (i, j)"
        using carr(2)[unfolded carrier_mat_def] by auto
    qed
  }
  moreover
  {
    assume as: "A = C - B"
    have "A + B = C"
    proof
      show "dim_row (A + B) = dim_row C""dim_col (A + B) = dim_col C"
        using carr(1) assms(3) by auto
      {
        fix i j
        assume ij_p: "i < n" "j < n"
        then have "A $$ (i,j) = C $$ (i,j) - B $$ (i,j)"
          using as mat_minus_compo_alt assms(2,3) by auto
        then have "A $$ (i,j) + B $$ (i,j) = C $$ (i,j)"
          by auto
        then have "(A + B) $$ (i,j) = C $$ (i,j)"
          using mat_add_compo_alt assms(1,2) ij_p by auto
      }
      then show "\<And>i j. i < dim_row C \<Longrightarrow> j < dim_col C \<Longrightarrow> (A + B) $$ (i, j) = C $$ (i, j)"
        using assms(3)[unfolded carrier_mat_def] by auto
    qed
  }
  ultimately show "A + B = C \<equiv> A = C - B" by linarith
qed



text \<open>Matrix comparison equivalences\<close>

lemma mat_cmp_minus_eq:
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A \<ge>\<^sub>m B + C = (A - C \<ge>\<^sub>m B)"
proof -
  have "(A \<ge>\<^sub>m B + C) = (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i,j) \<ge> B $$ (i,j) + C $$ (i,j))"
    using assms mat_ge_def carrier_matD mat_add_compo_alt by auto
  moreover
  have "(A - C \<ge>\<^sub>m B) = (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i,j) - C $$ (i,j) \<ge> B $$ (i,j))"
    using assms mat_ge_def carrier_matD mat_minus_compo_alt by auto
  ultimately show ?thesis using le_diff_eq[symmetric, of "B $$ _"] by auto
qed

lemma mat_minus_cmp_eq:
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A + B \<ge>\<^sub>m C = (A \<ge>\<^sub>m C - B)"
proof -
  have "(A + B \<ge>\<^sub>m C) = (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i,j) + B $$ (i,j) \<ge> C $$ (i,j))"
    using assms mat_ge_def carrier_matD mat_add_compo_alt by auto
  moreover
  have "(A \<ge>\<^sub>m C - B) = (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i,j) \<ge> C $$ (i,j) - B $$ (i,j))"
    using assms mat_ge_def carrier_matD mat_minus_compo_alt by auto
  ultimately show ?thesis using diff_le_eq[symmetric, of "C $$ _"] by auto
qed

lemma mat_comparison_zero_eq:
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "A \<ge>\<^sub>m B = (A - B \<ge>\<^sub>m 0\<^sub>m n n)"
  using assms mat_cmp_minus_eq[of A "0\<^sub>m n n"] left_add_zero_mat by auto



lemma mat_cmp_minus:
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A >\<^sub>m B + C = (A - C >\<^sub>m B)"
proof -
  {
    assume as: "A >\<^sub>m B + C"
    then obtain i j where ij_p: "A $$ (i,j) > B $$ (i,j) + C $$ (i,j)" "i < n" "j < n"
      using mat_gt_def mat_add_compo_alt assms(2,3) by auto
    from as have "A \<ge>\<^sub>m B + C" by auto
    then have "A - C \<ge>\<^sub>m B"
      using mat_cmp_minus_eq assms by auto
    moreover
    from ij_p have "A $$ (i,j) - C $$ (i,j) > B $$ (i,j)" by auto
    ultimately have "A - C >\<^sub>m B" using mat_gt_def ij_p assms(3) by auto
  }
  moreover
  {
    assume as: "A - C >\<^sub>m B"
    then obtain i j where ij_p: "A $$ (i,j) - C $$ (i,j) > B $$ (i,j)" "i < n" "j < n"
      using mat_gt_def mat_minus_compo_alt assms(2,3) by auto
    from as have "A - C \<ge>\<^sub>m B" by auto
    then have "A \<ge>\<^sub>m B + C"
      using mat_cmp_minus_eq assms by auto
    moreover
    from ij_p have "A $$ (i,j) > B $$ (i,j) + C $$ (i,j)" by auto
    ultimately have "A >\<^sub>m B + C" using mat_gt_def ij_p assms(3) by auto
  }
  ultimately show ?thesis by auto
qed

lemma mat_minus_cmp:
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A + B >\<^sub>m C = (A >\<^sub>m C - B)"
proof -
  {
    assume as: "A + B >\<^sub>m C"
    then obtain i j where ij_p: "A $$ (i,j) + B $$ (i,j) > C $$ (i,j)" "i < n" "j < n"
      using mat_gt_def mat_add_compo_alt assms(2,3) by auto
    from as have "A + B \<ge>\<^sub>m C" by auto
    then have "A \<ge>\<^sub>m C - B"
      using mat_minus_cmp_eq assms by auto
    moreover
    from ij_p have "A $$ (i,j) > C $$ (i,j) - B $$ (i,j)" by auto
    ultimately have "A >\<^sub>m C - B" using mat_gt_def ij_p assms(2) by auto
  }
  moreover
  {
    assume as: "A >\<^sub>m C - B"
    then obtain i j where ij_p: "A $$ (i,j) > C $$ (i,j) - B $$ (i,j)" "i < n" "j < n"
      using mat_gt_def mat_minus_compo_alt assms(2,3) by auto
    from as have "A \<ge>\<^sub>m C - B" by auto
    then have "A + B \<ge>\<^sub>m C"
      using mat_minus_cmp_eq assms by auto
    moreover
    from ij_p have "A $$ (i,j) + B $$ (i,j) > C $$ (i,j)" by auto
    ultimately have "A + B >\<^sub>m C" using mat_gt_def ij_p assms(2) by auto
  }
  ultimately show ?thesis by auto
qed

lemma mat_comparison_zero: 
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "A >\<^sub>m B = (A - B >\<^sub>m 0\<^sub>m n n)"
  using assms mat_cmp_minus[of A "0\<^sub>m n n"] left_add_zero_mat by auto




lemma mat_comparison_eq_imp_nonneg_diff:
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "A \<ge>\<^sub>m B"
  shows "\<exists>C. C \<ge>\<^sub>m 0\<^sub>m n n \<and> A = B + C"
proof
  have "A - B \<ge>\<^sub>m 0\<^sub>m n n" using mat_comparison_zero_eq[OF assms(1,2)] assms(3) by auto
  moreover
  have "B + (A - B) = A"
    using uminus_l_inv_mat[OF assms(2)] add_uminus_minus_mat[symmetric, OF assms(1,2)]
          assms(1,2) by auto
  ultimately show "A - B \<ge>\<^sub>m 0\<^sub>m n n \<and> A = B + (A - B)" by auto
qed

lemma mat_comparison_imp_nonnull_diff:
  assumes "(A :: int mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "A >\<^sub>m B"
  shows "\<exists>C. C >\<^sub>m 0\<^sub>m n n \<and> A = B + C"
proof
  have "A - B >\<^sub>m 0\<^sub>m n n" using mat_comparison_zero[OF assms(1,2)] assms(3) by auto
  moreover
  have "B + (A - B) = A"
    using uminus_l_inv_mat[OF assms(2)] add_uminus_minus_mat[symmetric, OF assms(1,2)]
          assms(1,2) by auto
  ultimately show "A - B >\<^sub>m 0\<^sub>m n n \<and> A = B + (A - B)" by auto
qed


text \<open>Matrix multiplication associativity properties for more complex expressions\<close>

lemma mat_mult_assoc_4:
  assumes "A \<in> carrier_mat n n"
          "B \<in> carrier_mat n n"
          "C \<in> carrier_mat n n"
          "D \<in> carrier_mat n n"
  shows "(A * B) * (C * D) = A * (B * C) * D"
proof -
  have "(A * B) * (C * D) = A * (B * (C * D))"
    using assms mult_carrier_mat assoc_mult_mat[of A n n B n "C * D" n] by auto
  also have "\<dots> = A * ((B * C) * D)"
    using assms mult_carrier_mat assoc_mult_mat by auto
  also have "\<dots> = (A * (B * C)) * D"
    using assms mult_carrier_mat assoc_mult_mat[of A n n "B * C" n] by auto
  finally show ?thesis.
qed

lemma mat_mult_assoc_5:
  assumes "A \<in> carrier_mat n n"
          "B \<in> carrier_mat n n"
          "C \<in> carrier_mat n n"
          "D \<in> carrier_mat n n"
          "E \<in> carrier_mat n n"
  shows "(A * B) * E * (C * D) = A * (B * E * C) * D"
proof -
  have "(A * B) * E * (C * D) = (A * B) * (E * (C * D))"
    using assms mult_carrier_mat assoc_mult_mat[of "A * B" n n E n "C * D" n] by auto
  also have "\<dots> = (A * B) * ((E * C) * D)"
    using assms mult_carrier_mat assoc_mult_mat by auto
  also have "\<dots> = A * (B * ((E * C) * D))"
    using assms mult_carrier_mat assoc_mult_mat[of A n n B n "((E * C) * D)" n] by auto
  also have "\<dots> = A * ((B * (E * C)) * D)"
    using assms mult_carrier_mat assoc_mult_mat[of B n n "E * C" n] by auto
  also have "\<dots> = A * ((B * E * C) * D)"
    using assms mult_carrier_mat assoc_mult_mat by auto
  also have "\<dots> = A * (B * E * C) * D"
    using assms mult_carrier_mat assoc_mult_mat[of A n n "B * E * C" n] by auto
  finally show ?thesis.
qed



text \<open>Transitivity of comparisons made simpler\<close>


lemma mat_gt_trans_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A >\<^sub>m B" "B >\<^sub>m C"
        shows "A >\<^sub>m C"
  using assms order_pair.mat_gt_trans[of "(>)" 1 n n] int_SN.order_pair_axioms
  by auto

lemma mat_ge_gt_trans_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A \<ge>\<^sub>m B" "B >\<^sub>m C"
        shows "A >\<^sub>m C"
  using assms order_pair.mat_ge_gt_trans[of "(>)" 1 n n] int_SN.order_pair_axioms
  by auto

lemma mat_gt_ge_trans_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A >\<^sub>m B" "B \<ge>\<^sub>m C"
        shows "A >\<^sub>m C"
  using assms order_pair.mat_gt_ge_trans[of "(>)" 1 n n] int_SN.order_pair_axioms
  by auto



text \<open>Monotonicity of comparisons made simpler\<close>

lemma mat_gt_add_left_mono_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A >\<^sub>m B"
        shows "A + C >\<^sub>m B + C"
  using assms one_mono_ordered_semiring_1.mat_plus_gt_left_mono[of 1 "(>)" n n]
        int_SN.one_mono_ordered_semiring_1_axioms
  by auto

lemma mat_gt_add_right_mono_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A >\<^sub>m B"
        shows "C + A >\<^sub>m C + B"
  using assms mat_gt_add_left_mono_simpler by (simp add: comm_add_mat)


text \<open>SN of matrix strict comparison\<close>


definition mat_gt_set :: "(int mat * int mat) set" where
"mat_gt_set = {(a,b). a \<in> carrier_mat n n \<and> b \<in> carrier_mat n n \<and>
                      a \<ge>\<^sub>m 0\<^sub>m n n \<and> b \<ge>\<^sub>m 0\<^sub>m n n \<and> a >\<^sub>m b}"

lemma SN_mat_gt: "SN mat_gt_set"
  unfolding mat_gt_set_def
  using SN_one_mono_ordered_semiring_1.mat_gt_SN[of _ "(>)" n n]
        int_SN.SN_one_mono_ordered_semiring_1_axioms
  by fastforce


subsection \<open>Notations for elements in $A^* $ where $A$ is some set of matrices.
 Note that the usual relation closures cannot be used here to faithfully
 represent the multiplications going on.\<close>


fun prod_list_mat :: "int mat list \<Rightarrow> int mat" where
  "prod_list_mat [] = 1\<^sub>m n"
| "prod_list_mat (x#xs) = x * prod_list_mat xs"





lemma prod_list_mat_closed:
  assumes "submonoid A interp_mul_monoid_mat" "set a\<^sub>1 \<subseteq> A"
shows "prod_list_mat a\<^sub>1 \<in> A"
  using assms(2)
proof (induction a\<^sub>1)
  case Nil
  then show ?case using assms(1)[unfolded submonoid_def interp_mul_monoid_mat_def] by auto
next
  case (Cons a a\<^sub>1)
  then show ?case
  proof -
    from Cons.prems have "set a\<^sub>1 \<subseteq> A" by auto
    then have "prod_list_mat a\<^sub>1 \<in> A" using Cons.IH by auto
    moreover
    have "prod_list_mat (a # a\<^sub>1) = a * prod_list_mat a\<^sub>1" by auto
    moreover
    have "a \<in> A" using Cons.prems by auto
    ultimately show "prod_list_mat (a # a\<^sub>1) \<in> A"
      using assms(1)[unfolded submonoid_def interp_mul_monoid_mat_def] by auto
  qed
qed


lemma prod_list_mat_singleton[simp]:
  assumes "x \<in> carrier_mat n n"
  shows "prod_list_mat[x] = x"
proof -
  have "prod_list_mat[x] = x * prod_list_mat []" by auto
  also have "\<dots> = x * 1\<^sub>m n" by auto
  also have "\<dots> = x" using assms by auto
  finally show ?thesis.
qed

lemma prod_list_mat_mult:
  assumes "set a\<^sub>1 \<subseteq> carrier_mat n n" "set a\<^sub>2 \<subseteq> carrier_mat n n"
  shows "prod_list_mat (a\<^sub>1@a\<^sub>2) = prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2"
  using assms(1)
proof (induction a\<^sub>1)
  case Nil
  then show ?case
    using prod_list_mat.simps(1) left_mult_one_mat prod_list_mat_closed[of "carrier_mat n n" a\<^sub>2]
          assms(2) subset_trans mul_monoid_mat_is_submonoid
    by auto
next
  case (Cons a a\<^sub>1)
  then show ?case
  proof -
    have "set a\<^sub>1 \<subseteq> carrier_mat n n" using Cons.prems by auto
    then have ih: "prod_list_mat (a\<^sub>1 @ a\<^sub>2) = prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2"
      using Cons.IH by auto
    have "prod_list_mat (a#a\<^sub>1@a\<^sub>2) = a * prod_list_mat (a\<^sub>1@a\<^sub>2)" by auto
    also have "\<dots> = a * (prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2)"
      using ih by auto
    moreover
    have "prod_list_mat (a#a\<^sub>1) * prod_list_mat a\<^sub>2 = a * (prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2)"
    proof -
      have carr:"a \<in> carrier_mat n n"
                "prod_list_mat a\<^sub>1 \<in> carrier_mat n n"
                "prod_list_mat a\<^sub>2 \<in> carrier_mat n n"
        using Cons.prems prod_list_mat_closed mul_monoid_mat_is_submonoid assms(2)
        by auto
      have "prod_list_mat (a#a\<^sub>1) * prod_list_mat a\<^sub>2 = (a * prod_list_mat a\<^sub>1) * prod_list_mat a\<^sub>2"
        by auto
      also have "\<dots> = a * (prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2)"
        using carr
        by (rule assoc_mult_mat)
      then show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
qed



lemma prod_list_mat_mult_map:
  assumes "set (map f a\<^sub>1) \<subseteq> carrier_mat n n" "set (map f a\<^sub>2) \<subseteq> carrier_mat n n"
  shows "prod_list_mat (map f (a\<^sub>1@a\<^sub>2)) = (prod_list_mat (map f a\<^sub>1)) * (prod_list_mat (map f a\<^sub>2))"
  using assms map_append prod_list_mat_mult
  by auto



lemma prod_list_mat_assoc_left:
  assumes "set a \<subseteq> carrier_mat n n" and xy_carr: "x \<in> carrier_mat n n" "y \<in> carrier_mat n n"
  shows "prod_list_mat a * x + prod_list_mat a * y = prod_list_mat a * (x + y)"
  by (rule mult_add_distrib_mat[OF prod_list_mat_closed[OF mul_monoid_mat_is_submonoid assms(1)] assms(2,3), symmetric])

lemma prod_list_mat_assoc_right:
  assumes "set a \<subseteq> carrier_mat n n" and xy_carr: "x \<in> carrier_mat n n" "y \<in> carrier_mat n n"
  shows "x * prod_list_mat a + y * prod_list_mat a = (x + y) * prod_list_mat a"
  by (rule add_mult_distrib_mat[OF assms(2,3) prod_list_mat_closed[OF mul_monoid_mat_is_submonoid assms(1)], symmetric])


subsection \<open>Same idea as above but with addition\<close>

fun add_list_mat :: "int mat list \<Rightarrow> int mat" where
"add_list_mat [] = 0\<^sub>m n n"
| "add_list_mat (x#xs) = x + add_list_mat xs"


lemma add_list_mat_closed:
  assumes "submonoid A interp_add_monoid_mat" "set a\<^sub>1 \<subseteq> A"
  shows "add_list_mat a\<^sub>1 \<in> A"
  using assms(2)
proof (induction a\<^sub>1)
  case Nil
  then show ?case
    using assms(1)[unfolded submonoid_def interp_add_monoid_mat_def monoid_mat_def] by auto
next
  case (Cons a a\<^sub>1)
  then show ?case
  proof -
    from Cons.prems have "set a\<^sub>1 \<subseteq> A" by auto
    then have "add_list_mat a\<^sub>1 \<in> A" using Cons.IH by auto
    moreover
    have "add_list_mat (a # a\<^sub>1) = a + add_list_mat a\<^sub>1" by auto
    moreover
    have "a \<in> A" using Cons.prems by auto
    ultimately show "add_list_mat (a # a\<^sub>1) \<in> A"
      using assms(1)[unfolded submonoid_def interp_add_monoid_mat_def monoid_mat_def] by auto
  qed
qed

lemma add_list_mat_singleton[simp]:
  assumes "x \<in> carrier_mat n n"
  shows "add_list_mat[x] = x"
proof -
  have "add_list_mat[x] = x + add_list_mat []" by auto
  also have "\<dots> = x + 0\<^sub>m n n" by auto
  also have "\<dots> = x" using assms by auto
  finally show ?thesis.
qed


lemma add_list_mat_add:
  assumes "set a\<^sub>1 \<subseteq> carrier_mat n n" "set a\<^sub>2 \<subseteq> carrier_mat n n"
  shows "add_list_mat (a\<^sub>1@a\<^sub>2) = add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2"
  using assms(1)
proof (induction a\<^sub>1)
  case Nil
  then show ?case
    using add_list_mat.simps(1) left_add_zero_mat add_list_mat_closed[of "carrier_mat n n" a\<^sub>2]
          assms(2) subset_trans add_monoid_mat_is_submonoid
    by auto
next
  case (Cons a a\<^sub>1)
  then show ?case
  proof -
    have "set a\<^sub>1 \<subseteq> carrier_mat n n" using Cons.prems by auto
    then have ih: "add_list_mat (a\<^sub>1 @ a\<^sub>2) = add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2"
      using Cons.IH by auto
    have "add_list_mat (a#a\<^sub>1@a\<^sub>2) = a + add_list_mat (a\<^sub>1@a\<^sub>2)" by auto
    also have "\<dots> = a + (add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2)"
      using ih by auto
    moreover
    have "add_list_mat (a#a\<^sub>1) + add_list_mat a\<^sub>2 = a + (add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2)"
    proof -
      have carr:"a \<in> carrier_mat n n"
                "add_list_mat a\<^sub>1 \<in> carrier_mat n n"
                "add_list_mat a\<^sub>2 \<in> carrier_mat n n"
        using Cons.prems add_list_mat_closed add_monoid_mat_is_submonoid assms(2)
        by auto
      have "add_list_mat (a#a\<^sub>1) + add_list_mat a\<^sub>2 = (a + add_list_mat a\<^sub>1) + add_list_mat a\<^sub>2"
        by auto
      also have "\<dots> = a + (add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2)"
        using carr
        by (rule assoc_add_mat)
      then show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
qed


lemma add_list_mat_add_map:
  assumes "set (map f a\<^sub>1) \<subseteq> carrier_mat n n" "set (map f a\<^sub>2) \<subseteq> carrier_mat n n"
  shows "add_list_mat (map f (a\<^sub>1@a\<^sub>2)) = (add_list_mat (map f a\<^sub>1)) + (add_list_mat (map f a\<^sub>2))"
  using assms map_append add_list_mat_add
  by auto


lemma add_list_mat_distrib:
  assumes "set a\<^sub>1 \<subseteq> carrier_mat n n" "a \<in> carrier_mat n n"
  shows "a * add_list_mat a\<^sub>1 = add_list_mat (map (\<lambda>x. a * x) a\<^sub>1)"
  using assms(1)
proof (induction a\<^sub>1)
  case Nil
  then show ?case using list.map(1) add_list_mat.simps(1) right_mult_zero_mat assms(2) by auto
next
  case (Cons x xs)
  then show ?case
  proof -
    have carr: "x \<in> carrier_mat n n" "set xs \<subseteq> carrier_mat n n"
      using Cons.prems by auto
    then have "a * add_list_mat (x # xs) = a * (x + add_list_mat xs)"
      using add_list_mat_add add_list_mat_singleton
      by auto
    also have "\<dots> = a * x + a * add_list_mat xs"
      using mult_add_distrib_mat carr assms(2)
            add_list_mat_closed[of "carrier_mat n n" xs]
            add_monoid_mat_is_submonoid
      by auto
    moreover
    have "add_list_mat (map ((*) a) (x # xs)) = add_list_mat (map ((*) a) [x]) +
                                                add_list_mat (map ((*) a) xs)"
      using add_list_mat_add_map[of _ "[x]" xs] carr assms(2) mult_carrier_mat
      by auto
    moreover
    have "add_list_mat (map ((*) a) [x]) + add_list_mat (map ((*) a) xs) =
           a * x + add_list_mat (map ((*) a) xs)"
      using add_list_mat_singleton carr(1) assms(2) mult_carrier_mat
      by auto
    moreover
    have "a * x + add_list_mat (map ((*) a) xs) = a * x + a * add_list_mat xs"
      using Cons.IH Cons.prems by auto
    ultimately show ?thesis by auto
  qed
qed


subsection \<open>Positive and strictly positive cones\<close>

text \<open>Defining the positive cone $N$ for a ring of matrices\<close>

definition N :: "int mat set" where
  "N = {A. A \<in> carrier_mat n n \<and> A \<ge>\<^sub>m 0\<^sub>m n n}"

lemma N_in_carr[simp]: "N \<subseteq> carrier_mat n n"
  using N_def by auto

lemma N_el_in_carr:
  assumes "x \<in> N"
  shows "x \<in> carrier_mat n n"
  using assms N_in_carr in_mono[of N "carrier_mat n n"] by auto

text \<open>Alternative definitions\<close>

lemma N_greater_eq_zero: 
  assumes "A \<in> carrier_mat n n"
  shows "A \<in> N = (A \<ge>\<^sub>m 0\<^sub>m n n)"
  using assms N_def by auto

lemma N_compo_greater_eq_zero:
  assumes "A \<in> N" "i < n" "j < n"
  shows "A $$ (i, j) \<ge> 0"
  using assms N_el_in_carr[of A] N_greater_eq_zero[of A] mat_ge_def by auto


lemma N_compo_greater_eq_zero2: "A \<in> N =
 (A \<in> carrier_mat n n \<and> (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i, j) \<ge> 0))"
  unfolding N_def
  using mat_ge_def index_zero_mat(1)
  by auto

lemma zero_in_N[simp]: "0\<^sub>m n n \<in> N"
  using N_greater_eq_zero by auto

lemma one_in_N[simp]: "1\<^sub>m n \<in> N"
  using N_greater_eq_zero by auto





text \<open>Positive cone is closed under multiplication and addition\<close>

lemma N_mult_closed:
  assumes "A \<in> N" "B \<in> N"
  shows "A * B \<in> N"
proof -
  have "B \<ge>\<^sub>m 0\<^sub>m n n" using assms(2) N_greater_eq_zero N_el_in_carr by auto
  then have "A * B \<ge>\<^sub>m 0\<^sub>m n n * B"
    using assms N_greater_eq_zero[of A] N_el_in_carr
          mat_mult_left_mono[of B n A "0\<^sub>m n n"]
          zero_carrier_mat[of n n]
    by auto
  then show ?thesis
    using left_mult_zero_mat[of B n n n]
          N_greater_eq_zero[of "A * B"]
          assms N_el_in_carr mult_carrier_mat[of A n n B n]
    by auto
qed


lemma N_add_closed:
  assumes "A \<in> N" "B \<in> N"
  shows "A + B \<in> N"
proof -
  have ABcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
    using assms N_el_in_carr by auto
  then have "A + B \<in> carrier_mat n n"
    using add_carrier_mat by auto
  moreover
  {
    fix i j
    assume ij_p: "i < n" "j < n"
    then have "A $$ (i,j) \<ge> 0" "B $$ (i,j) \<ge> 0"
      using assms N_compo_greater_eq_zero2 by auto
    moreover
    from ij_p have "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
      using mat_add_compo_alt ABcarr by auto
    ultimately have "(A + B) $$ (i,j) \<ge> 0"
      using add_nonneg_nonneg by auto
  }
  ultimately show ?thesis using N_compo_greater_eq_zero2[symmetric, of "A + B"] by auto
qed
    

lemma prod_list_mat_in_N:
  assumes "set a \<subseteq> N"
  shows "prod_list_mat a \<in> N"
  using assms
proof (induction a)
  case Nil
  then show ?case using prod_list_mat.simps(1) N_greater_eq_zero by auto
next
  case (Cons a\<^sub>1 a\<^sub>2)
  then show ?case
  proof -
    have "prod_list_mat (a\<^sub>1 # a\<^sub>2) = a\<^sub>1 * prod_list_mat a\<^sub>2" by auto
    moreover
    have "a\<^sub>1 \<in> N" using Cons.prems by auto
    moreover
    have "prod_list_mat a\<^sub>2 \<in> N" using Cons.prems by (simp add: Cons.IH)
    ultimately show ?thesis using N_mult_closed by auto
  qed
qed



lemma N_is_submonoid_mul: "submonoid N interp_mul_monoid_mat"
proof (unfold_locales, unfold interp_mul_monoid_mat_def, goal_cases)
  case 1
  then show ?case using N_in_carr by simp
next
  case (2 x y)
  then show ?case using N_mult_closed by simp
next
  case 3
  then show ?case using one_in_N by simp
qed

lemma N_is_submonoid_add: "submonoid N interp_add_monoid_mat"
  using N_add_closed zero_in_N
  by (unfold_locales, unfold interp_add_monoid_mat_def monoid_mat_def, auto)



text \<open>Defining the strictly positive cone $P$ for a ring of matrices\<close>

definition P :: "int mat set" where
  "P = {A. A \<in> carrier_mat n n \<and> A >\<^sub>m 0\<^sub>m n n}"

lemma P_in_carr[simp]: "P \<subseteq> carrier_mat n n"
  using P_def by auto

lemma P_el_in_carr:
  assumes "x \<in> P"
  shows "x \<in> carrier_mat n n"
  using assms P_in_carr in_mono[of P "carrier_mat n n"] by auto





text \<open>Alternative definitions\<close>

lemma P_greater_zero:
  assumes "A \<in> carrier_mat n n"
  shows "A \<in> P = (A >\<^sub>m 0\<^sub>m n n)"
  using assms P_def by auto

lemma P_N_one_elem_nonnull:
  assumes "A \<in> N"
  shows "A \<in> P = (\<exists>i j. i < n \<and> j < n \<and> A $$ (i,j) > 0)"
  unfolding P_def mat_gt_def
  using assms[unfolded N_def] index_zero_mat(1)[of _ n _ n]
  by fastforce
  

lemma P_in_N: "P \<subseteq> N"
  by (simp only: P_def N_def) auto


lemma zero_not_in_P: "0\<^sub>m n n \<notin> P"
  using P_def by auto



lemma P_add_closed:
  assumes "A \<in> P" "B \<in> N"
  shows "A + B \<in> P"
proof -
  have ABcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
    using assms P_el_in_carr N_el_in_carr by auto
  then have add_carr: "A + B \<in> carrier_mat n n"
    using add_carrier_mat by auto
  moreover
  have "A + B >\<^sub>m 0\<^sub>m n n"
  proof -
    have "A + B \<ge>\<^sub>m 0\<^sub>m n n"
      using assms N_add_closed set_mp[OF P_in_N] N_greater_eq_zero[OF add_carr]
      by auto
    moreover
    {
      obtain i j where ij_p: "i < n" "j < n" "A $$ (i,j) > 0"
        using assms[unfolded P_def] by auto
      moreover have "B $$ (i,j) \<ge> 0"
        using calculation assms(2) N_compo_greater_eq_zero by auto
      ultimately
      have "A $$ (i,j) + B $$ (i,j) > 0" by auto
      then have "(A + B) $$ (i,j) > 0"
        using index_add_mat(1) ij_p ABcarr by auto
      then have "\<exists>i j. i < n \<and> j < n \<and> (A + B) $$ (i,j) > 0" using ij_p by auto
    }
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis using P_greater_zero by auto
qed

subsection \<open>Core of a set\<close>
context
begin

text \<open>$core(A)$ is defined such that $A^*core(A)A^* \subseteq P$.
 Typically, we want the interpretation of the alphabet to be in $A$ and
 the interpretation of the rules of an SRS to be in $core(A)$.\<close>

definition core :: "int mat set \<Rightarrow> int mat set" where
 "core A = {d. d \<in> carrier_mat n n \<and>
   (\<forall>a\<^sub>1 a\<^sub>2. set a\<^sub>1 \<subseteq> A \<and> set a\<^sub>2 \<subseteq> A \<longrightarrow>
    ( prod_list_mat a\<^sub>1 * d * prod_list_mat a\<^sub>2 ) \<in> P
    )
  }"


lemma core_def_alt: "x \<in> core A =
 (x \<in> carrier_mat n n \<and>
 (\<forall>a\<^sub>1 a\<^sub>2. set a\<^sub>1 \<subseteq> A \<longrightarrow> set a\<^sub>2 \<subseteq> A \<longrightarrow> prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> P))"
  unfolding core_def by auto


lemma core_in_carr[simp]: "core A \<subseteq> carrier_mat n n"
  using core_def by auto

lemma core_el_in_carr:
  assumes "x \<in> core A"
  shows "x \<in> carrier_mat n n"
  using core_in_carr in_mono[of "core A" "carrier_mat n n" x] assms by auto


lemma core_element_in_P:
  assumes Acarr: "A \<subseteq> carrier_mat n n" and
    xA: "x \<in> core A" and lA: "l \<in> A" and rA: "r \<in> A"
  shows "l * x * r \<in> P"
proof -
  from xA[unfolded core_def, simplified] have x: "x \<in> carrier_mat n n"
  and inP: "set a\<^sub>1 \<subseteq> A \<Longrightarrow> set a\<^sub>2 \<subseteq> A \<Longrightarrow> prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> P" for a\<^sub>1 a\<^sub>2
    by auto
  moreover
  from inP[of "[l]" "[r]"] lA rA 
  have "prod_list_mat [l] * x * prod_list_mat [r] \<in> P" by auto
  moreover
  from lA Acarr have "l \<in> carrier_mat n n" by auto
  moreover
  from rA Acarr have "r \<in> carrier_mat n n" by auto
  ultimately show "l * x * r \<in> P" using prod_list_mat_singleton by auto
qed

lemma core_element_gt:
  assumes "A \<subseteq> carrier_mat n n" "x \<in> core A" "l \<in> A" "r \<in> A"
  shows "l * x * r >\<^sub>m 0\<^sub>m n n"
  using core_element_in_P P_greater_zero assms P_el_in_carr
  by meson

lemma core_extended:
  assumes "A \<subseteq> carrier_mat n n" "set a\<^sub>1 \<subseteq> A" "set a\<^sub>2 \<subseteq> A" "x \<in> core A"
  shows "prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> core A"
proof -

  have "x \<in> carrier_mat n n" using assms(4) core_el_in_carr by auto


  have "\<And>u v. set u \<subseteq> A \<Longrightarrow> set v \<subseteq> A \<Longrightarrow>
         prod_list_mat u * (prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2) * prod_list_mat v \<in> P"
  proof -
    fix u v
    assume suv_p: "set u \<subseteq> A" "set v \<subseteq> A"
    then obtain a3 a4  where
                           a_p:   "a3 = u@a\<^sub>1" "a4 = a\<^sub>2@v"
                      and  sa_p:  "set a3 \<subseteq> A" "set a4 \<subseteq> A"
      using assms(2) assms(3) by auto
    
    have st1: "prod_list_mat a3 * x * prod_list_mat a4 \<in> P" using sa_p core_def assms(4) by auto
    then have "prod_list_mat a3 * x * prod_list_mat a4 =
              (prod_list_mat u * prod_list_mat a\<^sub>1) * x * (prod_list_mat a\<^sub>2 * prod_list_mat v)"
      using prod_list_mat_mult assms(1) a_p suv_p sa_p  by auto
    also have "\<dots> = prod_list_mat u * (prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2) * prod_list_mat v"
      using mat_mult_assoc_5[of "prod_list_mat u" "prod_list_mat a\<^sub>1"]
            \<open>x \<in> carrier_mat n n\<close> prod_list_mat_closed mul_monoid_mat_is_submonoid
            suv_p assms(1,2,3)
      by auto
    finally
    show "prod_list_mat u * (prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2) * prod_list_mat v \<in> P"
      using st1
      by auto
  qed
  then show ?thesis using assms by (simp add: P_el_in_carr core_def)
qed


lemma core_in_P: "core A \<subseteq> P"
proof
  fix x
  assume "x \<in> core A"
  then obtain a\<^sub>1 a\<^sub>2 where "set a\<^sub>1 \<subseteq> A" "set a\<^sub>2 \<subseteq> A" and a_empty: "a\<^sub>1 = []" "a\<^sub>2 = []"
                    and in_p: "prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> P"
    using core_def_alt[of x A] core_el_in_carr[of x A]
    by (metis empty_iff empty_set subset_iff)

  then show "x \<in> P"
    using \<open>x \<in> core A\<close> core_el_in_carr[of x A] prod_list_mat.simps(1)
          left_mult_one_mat[of x n n] right_mult_one_mat[of x n n]
    by auto
qed


lemma core_gt:
  assumes "x \<in> carrier_mat n n" "y \<in> carrier_mat n n" "x - y \<in> core A"
  shows "x >\<^sub>m y"
  using mat_comparison_zero[OF assms(1,2)]
        P_greater_zero[OF set_mp[OF subset_trans[OF core_in_P P_in_carr] assms(3)]]
        set_mp[OF core_in_P assms(3)]
  by auto



lemma core_plus_mono:
  assumes "A \<subseteq> carrier_mat n n" "x \<in> core A" "y \<in> core A"
  shows "x + y \<in> core A"
proof -
  have carrs: "x \<in> carrier_mat n n" "y \<in> carrier_mat n n"
    using assms core_el_in_carr by auto
  {
    fix a\<^sub>1 a\<^sub>2
    assume as: "set a\<^sub>1 \<subseteq> A" "set a\<^sub>2 \<subseteq> A"
    then have xy_p: "prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> P" (is "?left \<in> _")
                    "prod_list_mat a\<^sub>1 * y * prod_list_mat a\<^sub>2 \<in> P" (is "?right \<in> _")
      using assms[unfolded core_def] by auto
    have carrs2: "set a\<^sub>1 \<subseteq> carrier_mat n n" "set a\<^sub>2 \<subseteq> carrier_mat n n"
                 "prod_list_mat a\<^sub>1 \<in> carrier_mat n n" "prod_list_mat a\<^sub>2 \<in> carrier_mat n n"
      using as assms(1) prod_list_mat_closed[OF mul_monoid_mat_is_submonoid] by auto

    have "?left + ?right = (prod_list_mat a\<^sub>1 * x + prod_list_mat a\<^sub>1 * y) * prod_list_mat a\<^sub>2"
      using prod_list_mat_assoc_right[OF carrs2(2)] mult_carrier_mat[OF carrs2(3)] carrs
      by auto
    also have "\<dots> = prod_list_mat a\<^sub>1 * (x + y) * prod_list_mat a\<^sub>2"
      using prod_list_mat_assoc_left[OF carrs2(1)] carrs by auto
    finally have "?left + ?right = prod_list_mat a\<^sub>1 * (x + y) * prod_list_mat a\<^sub>2".
    moreover
    have "?left + ?right \<in> P" using P_add_closed[OF xy_p(1) set_mp[OF P_in_N xy_p(2)]].
    ultimately
    have "prod_list_mat a\<^sub>1 * (x + y) * prod_list_mat a\<^sub>2 \<in> P"
      using carrs by auto
  }
  then show ?thesis unfolding core_def using add_carrier_mat carrs(2) by blast
qed


lemma core_plus_N_mono:
  assumes "A \<subseteq> N" "x \<in> core A" "y \<in> N"
  shows "x + y \<in> core A"
proof -
  have carrs: "x \<in> carrier_mat n n" "y \<in> carrier_mat n n"
    using assms core_el_in_carr N_el_in_carr by auto
  {
    fix a1 a2
    assume a_p: "set a1 \<subseteq> A" "set a2 \<subseteq> A"
    then have a_p2: "set a1 \<subseteq> N" "set a1 \<subseteq> carrier_mat n n"
                    "set a2 \<subseteq> N" "set a2 \<subseteq> carrier_mat n n"
      using assms N_in_carr set_mp by blast+

    from a_p have x_p: "prod_list_mat a1 * x * prod_list_mat a2 \<in> P"
      using assms[unfolded core_def] by auto

    have carrs2: "prod_list_mat a1 \<in> carrier_mat n n" "prod_list_mat a2 \<in> carrier_mat n n"
      using prod_list_mat_closed[OF mul_monoid_mat_is_submonoid] a_p2
      by auto

    have "prod_list_mat a1 * (x + y) * prod_list_mat a2 =
           (prod_list_mat a1 * x + prod_list_mat a1 * y) * prod_list_mat a2"
      using prod_list_mat_assoc_left[OF a_p2(2) carrs] by auto
    then have "prod_list_mat a1 * (x + y) * prod_list_mat a2 =
      prod_list_mat a1 * x * prod_list_mat a2 + prod_list_mat a1 * y * prod_list_mat a2"
      using prod_list_mat_assoc_right[OF a_p2(4) mult_carrier_mat[OF carrs2(1)] mult_carrier_mat[OF carrs2(1)]]
            carrs
      by auto
    moreover
    have "prod_list_mat a1 * x * prod_list_mat a2 + prod_list_mat a1 * y * prod_list_mat a2 \<in> P"
    proof -

      have "prod_list_mat a1 * y * prod_list_mat a2 \<in> N"
        using prod_list_mat_closed[OF N_is_submonoid_mul] a_p2(1,3) assms(3) N_mult_closed
        by auto
      then show ?thesis using x_p P_add_closed by auto
    qed
    ultimately
    have "prod_list_mat a1 * (x + y) * prod_list_mat a2 \<in> P" by auto
  }
  then show ?thesis unfolding core_def using add_carrier_mat carrs(2) by blast
qed



end (*Core of a set*)

section \<open>Matrix sets of interest\<close>
context
begin

definition E\<^sub>I :: "nat set \<Rightarrow> int mat set" where
  "E\<^sub>I I = {d \<in> N. \<forall>i \<in> I. d $$ (i,i) > 0}"

definition P\<^sub>I :: "nat set \<Rightarrow> int mat set" where
  "P\<^sub>I I = {d \<in> N. \<exists>i \<in> I. \<exists>j \<in> I. d $$ (i,j) > 0}"

definition M\<^sub>I :: "nat set \<Rightarrow> int mat set" where
  "M\<^sub>I I = {d \<in> N. \<forall>i \<in> I. \<exists>j \<in> I. d $$ (i,j) > 0}"



context
  fixes I
  assumes I0: "I \<subseteq> {0..< n}" 
  and I_non_empty: "I \<noteq> {}" 
begin





lemma one_in_E\<^sub>I[simp]: "1\<^sub>m n \<in> E\<^sub>I I"
proof -
  {
    fix i
    assume i_p: "i \<in> I"
    then have "i < n" using I0 by auto
    then have "(1\<^sub>m n) $$ (i,i) > (0 :: int)" using index_one_mat(1) by auto
  }
  then show ?thesis unfolding E\<^sub>I_def using one_in_N by auto
qed

lemma E\<^sub>I_in_N[simp]: "E\<^sub>I I \<subseteq> N"
  using E\<^sub>I_def by auto


lemma E\<^sub>I_in_carr[simp]: "E\<^sub>I I \<subseteq> carrier_mat n n"
  using subset_trans[of "E\<^sub>I I" N "carrier_mat n n"] E\<^sub>I_in_N N_in_carr by auto


lemma E\<^sub>I_el_in_carr:
  assumes "x \<in> E\<^sub>I I"
  shows "x \<in> carrier_mat n n"
  using assms E\<^sub>I_in_carr in_mono[of "E\<^sub>I I" "carrier_mat n n"] by auto




lemma E\<^sub>I_el_in_N:
  assumes "x \<in> E\<^sub>I I"
  shows "x \<in> N"
  using assms E\<^sub>I_in_N in_mono[of "E\<^sub>I I" N] by auto


lemma E\<^sub>I_greater_zero:
  assumes "x \<in> E\<^sub>I I"
  shows "x >\<^sub>m 0\<^sub>m n n"
proof -
  from I_non_empty obtain i where "i \<in> I" by auto
  with assms[unfolded E\<^sub>I_def] have "x $$ (i, i) > 0" by auto
  moreover
  from \<open>i \<in> I\<close> I0 have "i < n" by auto
  moreover
  from assms E\<^sub>I_el_in_carr[of x] E\<^sub>I_el_in_N[of x] N_greater_eq_zero[of x]
    have "x \<ge>\<^sub>m 0\<^sub>m n n" by auto 
  ultimately show ?thesis using mat_gt_def by auto
qed


lemma E\<^sub>I_in_P: "E\<^sub>I I \<subseteq> P"
  using E\<^sub>I_greater_zero E\<^sub>I_el_in_carr P_greater_zero by auto


lemma E\<^sub>I_mult_id_left:
  assumes "A \<in> E\<^sub>I I"
  shows "1\<^sub>m n * A \<in> E\<^sub>I I"
proof -
  have "1\<^sub>m n * A = A"
    using left_mult_one_mat E\<^sub>I_el_in_carr assms
    by auto
  then show ?thesis using assms by auto
qed

lemma E\<^sub>I_mult_id_right:
  assumes "A \<in> E\<^sub>I I"
  shows "A * 1\<^sub>m n \<in> E\<^sub>I I"
proof -
  have "A * 1\<^sub>m n = A"
    using right_mult_one_mat E\<^sub>I_el_in_carr assms
    by auto
  then show ?thesis using assms by auto
qed

lemma E\<^sub>I_closed_mult:
  assumes "A \<in> E\<^sub>I I" "B \<in> E\<^sub>I I"
  shows "A * B \<in> E\<^sub>I I"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> (A * B) $$ (i, i) > 0"
  proof -
    fix i
    assume as1: "i \<in> I"
    have "i < n" using I0 as1 by auto
    moreover
    have triv1: "A $$ (i, i) > 0" using assms(1) as1 by (simp add: E\<^sub>I_def)
    have triv2: "B $$ (i, i) > 0" using assms(2) as1 by (simp add: E\<^sub>I_def)
    have A_carr: "A \<in> carrier_mat n n" using E\<^sub>I_el_in_carr[of A] assms(1) by auto
    have B_carr: "B \<in> carrier_mat n n" using E\<^sub>I_el_in_carr[of B] assms(2) by auto
    have st1: "(A * B) $$ (i,i) = (\<Sum> k \<in> {0..< n}. A $$ (i,k) * B $$ (k,i))"
      using A_carr B_carr \<open>i < n\<close> mat_mult_compo_alt
      by blast
    have "A $$ (i,i) * B $$ (i,i) > 0"
      using triv1 triv2 E\<^sub>I_el_in_carr[of A] E\<^sub>I_el_in_carr[of B]
      by auto
    moreover
    have "\<And>k. k \<in> {0..< n} \<Longrightarrow> A $$ (i,k) * B $$ (k,i) \<ge> 0"
      using \<open>i < n\<close> assms E\<^sub>I_el_in_N[of A] E\<^sub>I_el_in_N[of B]
            A_carr B_carr
            N_compo_greater_eq_zero[of A i] N_compo_greater_eq_zero[of B _ i]
            mult_nonneg_nonneg[of "A $$ (i, _)" "B $$ (_, i)"]
      by auto
    ultimately show "(A * B) $$ (i, i) > 0" unfolding st1
      by (intro sum_pos2[of "{0..< n}" i], auto)
  qed
  
  moreover
  have "A * B \<in> carrier_mat n n"
    using assms E\<^sub>I_el_in_carr[of A] E\<^sub>I_el_in_carr[of B] mult_carrier_mat[of A n n B n]
    by auto
  moreover
  from mat_mult_right_mono[of A n B "0\<^sub>m n n"] right_mult_zero_mat[of A n n n]
      E\<^sub>I_el_in_carr[of A] E\<^sub>I_el_in_carr[of B] E\<^sub>I_el_in_N[of A] E\<^sub>I_el_in_N[of B]
      N_greater_eq_zero[of A] N_greater_eq_zero[of B] assms
    have "A * B \<ge>\<^sub>m 0\<^sub>m n n" by auto
  ultimately show ?thesis using N_greater_eq_zero[of "A * B"] I0 E\<^sub>I_def by auto
qed



lemma E\<^sub>I_closed_add:
  assumes "A \<in> E\<^sub>I I" "B \<in> N"
  shows "A + B \<in> E\<^sub>I I"
proof -
  have Mcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" using assms E\<^sub>I_el_in_carr N_el_in_carr by auto
  {
    fix i
    assume i_p: "i \<in> I"
    then have "i < n" using I0 by auto
    then have "A $$ (i,i) > 0" "B $$ (i,i) \<ge> 0"
      using assms E\<^sub>I_def N_compo_greater_eq_zero i_p by auto
    moreover
    have "(A + B) $$ (i,i) = A $$ (i,i) + B $$ (i,i)"
      using mat_add_compo_alt Mcarr \<open>i < n\<close> by auto
    ultimately have "(A + B) $$ (i,i) > 0"
      using add_pos_pos[of "A $$ (i,i)" "B $$ (i,i)"] by auto
  }
  moreover
  have "A + B \<in> carrier_mat n n" using add_carrier_mat Mcarr by auto
  moreover
  have "A + B \<in> N"
    using E\<^sub>I_el_in_N N_add_closed assms by auto
  ultimately show ?thesis unfolding E\<^sub>I_def by auto
qed



lemma submonoid_E\<^sub>I: "submonoid (E\<^sub>I I) interp_mul_monoid_mat"
proof (unfold_locales, unfold interp_mul_monoid_mat_def, goal_cases)
  case 1
  then show ?case using E\<^sub>I_in_carr by simp
next
  case (2 x y)
  then show ?case using E\<^sub>I_closed_mult by simp
next
  case 3
  then show ?case using one_in_E\<^sub>I by simp
qed







lemma one_in_P\<^sub>I[simp]: "1\<^sub>m n \<in> P\<^sub>I I"
proof -
  obtain i where i_p: "i \<in> I" using I_non_empty by auto
  then have "i < n" using I0 by auto
  then have "(1\<^sub>m n) $$ (i,i) > (0 :: int)" by auto
  then have "\<exists>i \<in> I. (1\<^sub>m n) $$ (i,i) > (0 :: int)"
    using i_p exI[of "\<lambda>i. i \<in> I \<and> 1\<^sub>m n $$ (i,i) > (0 :: int)" i]
    by auto
  then show ?thesis unfolding P\<^sub>I_def using one_in_N by auto
qed

lemma P\<^sub>I_in_N[simp]: "P\<^sub>I I \<subseteq> N"
  using P\<^sub>I_def by auto

lemma P\<^sub>I_el_in_N:
  assumes "x \<in> P\<^sub>I I"
  shows "x \<in> N"
  using assms P\<^sub>I_in_N in_mono[of "P\<^sub>I I" N] by auto

lemma P\<^sub>I_in_carr[simp]: "P\<^sub>I I \<subseteq> carrier_mat n n"
  using subset_trans[of "P\<^sub>I I" N "carrier_mat n n"] P\<^sub>I_in_N N_in_carr by auto

lemma P\<^sub>I_el_in_carr:
  assumes "x \<in> P\<^sub>I I"
  shows "x \<in> carrier_mat n n"
  using assms P\<^sub>I_in_carr in_mono[of "P\<^sub>I I" "carrier_mat n n"] by auto


lemma P\<^sub>I_greater_zero:
  assumes "x \<in> P\<^sub>I I"
  shows "x >\<^sub>m 0\<^sub>m n n"
proof -
  from assms[unfolded P\<^sub>I_def] I_non_empty obtain i j where "i \<in> I" "j \<in> I" "x $$ (i, j) > 0"
    by auto
  moreover
  from \<open>i \<in> I\<close> I0 have "i < n" by auto
  moreover
  from \<open>j \<in> I\<close> I0 have "j < n" by auto
  moreover
  from assms P\<^sub>I_el_in_N P\<^sub>I_el_in_carr N_greater_eq_zero have "x \<ge>\<^sub>m 0\<^sub>m n n" by auto
  ultimately show ?thesis using I0 mat_gt_def by auto
qed


lemma P\<^sub>I_greater_zero_compo:
 "x \<in> P\<^sub>I I = (x \<in> carrier_mat n n \<and> x \<ge>\<^sub>m 0\<^sub>m n n \<and> (\<exists>i j. i \<in> I \<and> j \<in> I \<and> x $$ (i,j) > 0))"
  unfolding P\<^sub>I_def
  using N_greater_eq_zero[of x] P\<^sub>I_el_in_carr[of x, unfolded P\<^sub>I_def]
  by auto



lemma P\<^sub>I_in_P: "P\<^sub>I I \<subseteq> P"
  using P\<^sub>I_greater_zero P\<^sub>I_el_in_carr P_greater_zero by auto



lemma P\<^sub>I_closed_add:
  assumes "A \<in> P\<^sub>I I" "B \<in> N"
  shows "A + B \<in> P\<^sub>I I"
proof -
  have Mcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" using assms P\<^sub>I_el_in_carr N_el_in_carr by auto
  {
    then obtain i j where ij_p: "i \<in> I" "j \<in> I" "A $$ (i,j) > 0"
      using assms[unfolded P\<^sub>I_def] by auto
    then have "i < n" "j < n" using ij_p I0 by auto
    then have "B $$ (i,j) \<ge> 0"
      using assms(2) N_compo_greater_eq_zero by auto
    moreover
    have "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
      using mat_add_compo_alt Mcarr \<open>i < n\<close> \<open>j < n\<close> by auto
    ultimately have "(A + B) $$ (i,j) > 0"
      using add_pos_nonneg[of "A $$ (i,j)" "B $$ (i,j)"] ij_p
      by auto
    then have "\<exists>i \<in> I. \<exists>j \<in> I. (A + B) $$ (i,j) > 0" using ij_p by auto
  }
  moreover
  have "A + B \<in> carrier_mat n n" using add_carrier_mat Mcarr by auto
  moreover
  have "A + B \<in> N"
    using P\<^sub>I_el_in_N N_add_closed assms by auto
  ultimately show ?thesis unfolding P\<^sub>I_def by auto
qed



lemma P\<^sub>I_mult_id_left:
  assumes "M \<in> P\<^sub>I I"
  shows "1\<^sub>m n * M \<in> P\<^sub>I I"
proof -
  have "1\<^sub>m n * M = M" using left_mult_one_mat assms P\<^sub>I_el_in_carr
    by auto
  then show ?thesis using assms by auto
qed

lemma P\<^sub>I_mult_id_right:
  assumes "M \<in> P\<^sub>I I"
  shows "M * 1\<^sub>m n \<in> P\<^sub>I I"
proof -
  have "M * 1\<^sub>m n = M" using right_mult_one_mat assms P\<^sub>I_el_in_carr
    by auto
  then show ?thesis using assms by auto
qed


lemma P\<^sub>I_closed_E\<^sub>I_mul_left:
  assumes "A \<in> E\<^sub>I I" "B \<in> P\<^sub>I I"
  shows "A * B \<in> P\<^sub>I I"
proof -
  from I0 assms(2) obtain i j where i_prop:  "i \<in> I"
                                      and j_prop:  "j \<in> I"
                                      and B_prop: "B $$ (i,j) > 0"
  proof (simp add: P\<^sub>I_def) qed auto

  from assms(1) E\<^sub>I_el_in_carr have triv1: "A \<in> carrier_mat n n" by auto
  from assms(2) P\<^sub>I_el_in_carr have triv2: "B \<in> carrier_mat n n" by auto
  from I0 i_prop have triv3: "i < n" by auto
  from I0 j_prop have triv4: "j < n" by auto

  have res1: "(A * B) $$ (i,j) > 0"
  proof -
    define f where "f k = A $$ (i, k) * B $$ (k, j)" for k
    from I0 assms(1) i_prop have A_prop: "A $$ (i,i) > 0" proof (simp add: E\<^sub>I_def) qed
    have id: "(A * B) $$ (i,j) = (\<Sum> k \<in> {0..< n}. A $$ (i,k) * B $$ (k,j))"
      using triv1 triv2 triv3 triv4 mat_mult_compo_alt by blast
    from A_prop B_prop have st1:"A $$ (i,i) * B $$ (i,j) > 0" by auto
    moreover
    from assms E\<^sub>I_el_in_N[of A] P\<^sub>I_el_in_N[of B]
        triv3 triv4 N_compo_greater_eq_zero[of A i] N_compo_greater_eq_zero[of B _ j]
        mult_nonneg_nonneg[of "A $$ (i, _)" "B $$ (_, j)"]
    have "\<forall>k \<in> {0..< n}. A $$ (i,k) * B $$ (k,j) \<ge> 0" by auto
    moreover
    from st1 triv3 have "\<exists>k \<in> {0..< n}. A $$ (i,k) * B $$ (k,j) > 0" by auto
    ultimately show ?thesis unfolding id f_def[symmetric] using triv3
      by (intro sum_pos2[of "{0..< n}" i], auto)
  qed
  
  from assms(1) assms(2) mat_mult_right_mono[of A n B "0\<^sub>m n n"]
        triv1 triv2 zero_carrier_mat[of n n]
      E\<^sub>I_el_in_N[of A] N_greater_eq_zero[of A] P\<^sub>I_el_in_N[of B] N_greater_eq_zero[of B]
      right_mult_zero_mat[of A n n n]
    have res2: "A * B \<ge>\<^sub>m 0\<^sub>m n n" by (simp add: less_eq_mat_def mat_ge_def)
  from triv1 triv2 mult_carrier_mat[of A n n B n] res2 N_greater_eq_zero[of "A * B"]
    have "A * B \<in> N" by auto
  then show ?thesis unfolding P\<^sub>I_def using res1 i_prop j_prop by auto
qed

lemma P\<^sub>I_closed_E\<^sub>I_mul_right:
  assumes "A \<in> E\<^sub>I I" "B \<in> P\<^sub>I I"
  shows "B * A \<in> P\<^sub>I I"
proof -
  from I0 assms(2) obtain i j where i_prop:  "i \<in> I"
                                      and j_prop:  "j \<in> I"
                                      and B_prop: "B $$ (i,j) > 0"
    by (simp add: P\<^sub>I_def) auto
  from assms(1) E\<^sub>I_el_in_carr have triv1: "A \<in> carrier_mat n n" by auto
  from assms(2) P\<^sub>I_el_in_carr have triv2: "B \<in> carrier_mat n n" by auto
  from I0 i_prop have triv3: "i < n" by auto
  from I0 j_prop have triv4: "j < n" by auto

  have res1: "(B * A) $$ (i,j) > 0"
  proof -
    define f where "f k = B $$ (i, k) * A $$ (k, j)" for k
    from assms(1) j_prop have A_prop: "A $$ (j,j) > 0" by (simp add: E\<^sub>I_def)
    have id: "(B * A) $$ (i,j) = (\<Sum> k \<in> {0..< n}. B $$ (i,k) * A $$ (k,j))"
      using triv1 triv2 triv3 triv4 mat_mult_compo_alt by blast
    from A_prop B_prop have st1:"B $$ (i,j) * A $$ (j,j) > 0" by auto
    moreover
    from assms(1) assms(2) E\<^sub>I_el_in_N[of A] P\<^sub>I_el_in_N[of B]
        triv3 triv4 N_compo_greater_eq_zero[of B i] N_compo_greater_eq_zero[of A _ j]
        mult_nonneg_nonneg[of "B $$ (i, _)" "A $$ (_, j)"]
    have "\<forall>k \<in> {0..< n}. B $$ (i,k) * A $$ (k,j) \<ge> 0" by auto
    moreover
    from st1 triv4 have "\<exists>k \<in> {0..< n}. B $$ (i,k) * A $$ (k,j) > 0" by auto
    ultimately show ?thesis unfolding id f_def[symmetric] using triv4
      by (intro sum_pos2[of "{0..< n}" j], auto)
  qed

  from assms(1) assms(2) mat_mult_right_mono[of B n A "0\<^sub>m n n"]
      triv1 triv2 zero_carrier_mat[of n n]
      E\<^sub>I_el_in_N[of A] N_greater_eq_zero[of A] P\<^sub>I_el_in_N[of B] N_greater_eq_zero[of B]
      right_mult_zero_mat[of B n n n]
    have res2: "B * A \<ge>\<^sub>m 0\<^sub>m n n" by (simp add: less_eq_mat_def mat_ge_def)
  from triv1 triv2 mult_carrier_mat[of B n n A n] res2 N_greater_eq_zero[of "B * A"]
    have "B * A \<in> N" by auto
  then show ?thesis unfolding P\<^sub>I_def using res1 i_prop j_prop by auto
qed


lemma P\<^sub>I_closed_E\<^sub>I_prod_left:
  assumes "M \<in> P\<^sub>I I" "set a\<^sub>1 \<subseteq> E\<^sub>I I"
  shows "prod_list_mat a\<^sub>1 * M \<in> P\<^sub>I I"
  using assms(2)
proof (cases "a\<^sub>1")
  case Nil
  then show ?thesis
  proof -
    assume as1: "a\<^sub>1 = []"
    then have "prod_list_mat a\<^sub>1 = 1\<^sub>m n" by auto
    then have "prod_list_mat a\<^sub>1 * M = M" using P\<^sub>I_el_in_carr[of M] assms(1) by auto
    then show ?thesis using assms by auto
  qed
next
  case (Cons x xs)
  from Cons have "a\<^sub>1 \<noteq> []" by auto
  then show ?thesis
    using assms prod_list_mat_closed[of "E\<^sub>I I" a\<^sub>1]
      submonoid_E\<^sub>I
      P\<^sub>I_closed_E\<^sub>I_mul_left[of "prod_list_mat a\<^sub>1" M]
    by auto
qed

lemma P\<^sub>I_closed_E\<^sub>I_prod_right:
  assumes "M \<in> P\<^sub>I I" "set a\<^sub>1 \<subseteq> E\<^sub>I I"
  shows "M * prod_list_mat a\<^sub>1 \<in> P\<^sub>I I"
  using assms(2)
proof (cases "a\<^sub>1")
  case Nil
  then have "prod_list_mat a\<^sub>1 = 1\<^sub>m n" by auto
  then have "M * prod_list_mat a\<^sub>1 = M" using P\<^sub>I_el_in_carr[of M] assms(1) by auto
  then show ?thesis using assms by auto
next
  case (Cons x xs)
  then have "a\<^sub>1 \<noteq> []" by auto
  then show ?thesis
    using assms prod_list_mat_closed[of "E\<^sub>I I" a\<^sub>1]
      submonoid_E\<^sub>I P\<^sub>I_closed_E\<^sub>I_mul_right[of "prod_list_mat a\<^sub>1" M]
    by auto
qed



lemma one_in_M\<^sub>I[simp]: "1\<^sub>m n \<in> M\<^sub>I I"
proof -
  {
    fix i
    assume i_p: "i \<in> I"
    then have "i < n" using I0 by auto
    then have "1\<^sub>m n $$ (i,i) > (0 :: int)" by auto
    then have "\<exists>j \<in> I. 1\<^sub>m n $$ (i,j) > (0:: int)"
      using i_p exI[of "\<lambda>j. j \<in> I \<and> 1\<^sub>m n $$ (i,j) > (0 :: int)" i]
      by auto
  }
  then show ?thesis unfolding M\<^sub>I_def using one_in_N by auto
qed


lemma M\<^sub>I_in_N: "M\<^sub>I I \<subseteq> N"
  using M\<^sub>I_def by auto

lemma M\<^sub>I_el_in_N:
  assumes "x \<in> M\<^sub>I I"
  shows "x \<in> N"
  using assms M\<^sub>I_in_N in_mono by auto

lemma M\<^sub>I_in_carr: "M\<^sub>I I \<subseteq> carrier_mat n n"
  using subset_trans[of "M\<^sub>I I" N] M\<^sub>I_in_N N_in_carr by auto

lemma M\<^sub>I_el_in_carr:
  assumes "x \<in> M\<^sub>I I"
  shows "x \<in> carrier_mat n n"
  using assms M\<^sub>I_in_carr in_mono by auto


lemma M\<^sub>I_greater_zero:
  assumes "x \<in> M\<^sub>I I"
  shows "x >\<^sub>m 0\<^sub>m n n"
proof -
  from assms[unfolded M\<^sub>I_def] I_non_empty obtain i j where "i \<in> I" "j \<in> I" "x $$ (i, j) > 0"
    by fastforce
  moreover
  from \<open>i \<in> I\<close> I0 have "i < n" by auto
  moreover
  from \<open>j \<in> I\<close> I0 have "j < n" by auto
  moreover
  from assms M\<^sub>I_el_in_carr M\<^sub>I_el_in_N N_greater_eq_zero have "x \<ge>\<^sub>m 0\<^sub>m n n" by auto
  ultimately show ?thesis by auto
qed


lemma M\<^sub>I_in_P: "M\<^sub>I I \<subseteq> P"
  using M\<^sub>I_greater_zero M\<^sub>I_el_in_carr P_greater_zero by auto




lemma M\<^sub>I_closed_mult:
  assumes "A \<in> M\<^sub>I I" "B \<in> M\<^sub>I I"
  shows "A * B \<in> M\<^sub>I I"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> \<exists>j \<in> I. (A * B) $$ (i,j) > 0"
  proof -
    fix i
    assume "i \<in> I"
    from \<open>i \<in> I\<close> obtain j1 where j1_p: "A $$ (i, j1) > 0" "j1 \<in> I"
      using assms(1)[unfolded M\<^sub>I_def]
      by auto
    from \<open>j1 \<in> I\<close> obtain j2 where j2_p: "B $$ (j1, j2) > 0" "j2 \<in> I"
      using assms(2)[unfolded M\<^sub>I_def]
      by auto
    have "i < n" using \<open>i \<in> I\<close> I0 by auto
    have "j1 < n" using \<open>j1 \<in> I\<close> I0 by auto
    have "j2 < n" using \<open>j2 \<in> I\<close> I0 by auto
    have id: "(A * B) $$ (i, j2) = (\<Sum> k \<in> {0..< n}. A $$ (i,k) * B $$ (k,j2))"
      using M\<^sub>I_el_in_carr \<open>i < n\<close> \<open>j2 < n\<close>  assms mat_mult_compo_alt by blast
    have "A $$ (i, j1) * B $$ (j1, j2) > 0"
      using j1_p j2_p M\<^sub>I_el_in_carr assms
      by auto
    moreover
    have "\<And>k. k < n \<Longrightarrow> A $$ (i,k) * B $$ (k,j2) \<ge> 0"
      using assms M\<^sub>I_el_in_N M\<^sub>I_el_in_carr \<open>i < n\<close> \<open>j2 < n\<close>
            N_compo_greater_eq_zero[of A i] N_compo_greater_eq_zero[of B _ j2]
            mult_nonneg_nonneg[of "A $$ (i,_)" "B $$ (_,j2)"]
      by auto
    ultimately have "(A * B) $$ (i, j2) > 0"
      unfolding id using \<open>j1 < n\<close>
      by (intro sum_pos2[of "{0..< n}" j1], auto)
    then show "\<exists>j \<in> I. (A * B) $$ (i, j) > 0"
      using \<open>j2 \<in> I\<close>
      by blast
  qed
  moreover
  have "A * B \<in> N"
    using N_mult_closed assms M\<^sub>I_el_in_N
    by auto
  ultimately
  show ?thesis unfolding M\<^sub>I_def by auto
qed



lemma M\<^sub>I_closed_add:
  assumes "A \<in> M\<^sub>I I" "B \<in> N"
  shows "A + B \<in> M\<^sub>I I"
proof -
  have Mcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" using assms M\<^sub>I_el_in_carr N_el_in_carr by auto
  {
    fix i
    assume i_p: "i \<in> I"
    then obtain j where j_p: "j \<in> I" "A $$ (i,j) > 0"
      using assms[unfolded M\<^sub>I_def] by auto
    then have "i < n" "j < n" using i_p I0 by auto
    then have "B $$ (i,j) \<ge> 0"
      using assms(2) M\<^sub>I_el_in_N N_compo_greater_eq_zero2 by auto
    moreover
    have "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
      using mat_add_compo_alt Mcarr \<open>i < n\<close> \<open>j < n\<close> by auto
    ultimately have "(A + B) $$ (i,j) > 0"
      using add_pos_nonneg[of "A $$ (i,j)" "B $$ (i,j)"] j_p(2)
      by auto
    then have "\<exists>j \<in> I. (A + B) $$ (i,j) > 0" using j_p(1) by auto
  }
  moreover
  have "A + B \<in> carrier_mat n n" using add_carrier_mat Mcarr by auto
  moreover
  have "A + B \<in> N"
    using M\<^sub>I_el_in_N N_add_closed assms by auto
  ultimately show ?thesis unfolding M\<^sub>I_def by auto
qed


lemma submonoid_M\<^sub>I: "submonoid (M\<^sub>I I) interp_mul_monoid_mat"
proof (unfold_locales, unfold interp_mul_monoid_mat_def, goal_cases)
  case 1
  then show ?case using M\<^sub>I_in_carr by simp
next
  case (2 x y)
  then show ?case using M\<^sub>I_closed_mult by simp
next
  case 3
  then show ?case using one_in_M\<^sub>I by simp
qed



subsection \<open>Main properties of the sets\<close>

theorem core_E\<^sub>I_in_P\<^sub>I: "P\<^sub>I I \<subseteq> core (E\<^sub>I I)"
proof
  fix A
  assume asm1: "A \<in> P\<^sub>I I"
  show "A \<in> core (E\<^sub>I I)"
  proof -
    have "E\<^sub>I I \<subseteq> carrier_mat n n" using E\<^sub>I_in_carr by auto
    have res: "\<And>a\<^sub>1 a\<^sub>2. set a\<^sub>1 \<subseteq> E\<^sub>I I \<Longrightarrow> set a\<^sub>2 \<subseteq> E\<^sub>I I \<Longrightarrow>
                   (prod_list_mat a\<^sub>1 * A * prod_list_mat a\<^sub>2) \<in> P\<^sub>I I"
      by (simp add: P\<^sub>I_closed_E\<^sub>I_prod_left P\<^sub>I_closed_E\<^sub>I_prod_right asm1)
    from asm1 P\<^sub>I_el_in_carr[of A] have triv: "A \<in> carrier_mat n n" by auto
    from triv res core_def P\<^sub>I_in_P in_mono[of "P\<^sub>I I" P] show ?thesis
      by simp
  qed
qed

theorem core_M\<^sub>I_in_M\<^sub>I: "M\<^sub>I I \<subseteq> core (M\<^sub>I I)"
proof
  fix A
  assume asm1: "A \<in> M\<^sub>I I"
  show "A \<in> core (M\<^sub>I I)"
  proof -
    {
      fix a\<^sub>1 a\<^sub>2
      assume a_p: "set a\<^sub>1 \<subseteq> M\<^sub>I I" "set a\<^sub>2 \<subseteq> M\<^sub>I I"
      have "(prod_list_mat a\<^sub>1 * A * prod_list_mat a\<^sub>2) \<in> M\<^sub>I I"
      proof -
        {
          fix K
          assume "K \<in> M\<^sub>I I"
          then have "K * prod_list_mat a\<^sub>2 \<in> M\<^sub>I I"
          proof (cases "a\<^sub>2 = []")
            case True
            from True have "prod_list_mat a\<^sub>2 = 1\<^sub>m n"
              using prod_list_mat.simps(1)
              by auto
            then have "K * prod_list_mat a\<^sub>2 = K"
              using right_mult_one_mat[of K] \<open>K \<in> M\<^sub>I I\<close> M\<^sub>I_el_in_carr[of K]
              by auto
            then show "K * prod_list_mat a\<^sub>2 \<in> M\<^sub>I I"
              using \<open>K \<in> M\<^sub>I I\<close>
              by auto
          next
            case False
            have "prod_list_mat a\<^sub>2 \<in> M\<^sub>I I"
              using prod_list_mat_closed[of "M\<^sub>I I" a\<^sub>2] submonoid_M\<^sub>I
                M\<^sub>I_in_carr a_p(2) \<open>a\<^sub>2 \<noteq> []\<close> M\<^sub>I_closed_mult
              by auto
            then show "K * prod_list_mat a\<^sub>2 \<in> M\<^sub>I I"
              using \<open>K \<in> M\<^sub>I I\<close> M\<^sub>I_closed_mult
              by auto
          qed
        } note res1 = this
        show ?thesis proof (cases "a\<^sub>1 = []")
          case True
          hence "prod_list_mat a\<^sub>1 = 1\<^sub>m n"
            using prod_list_mat.simps(1)
            by auto
          then have "prod_list_mat a\<^sub>1 * A = A"
            using left_mult_one_mat[of A] asm1 M\<^sub>I_el_in_carr[of A]
            by auto
          then show "(prod_list_mat a\<^sub>1 * A * prod_list_mat a\<^sub>2) \<in> M\<^sub>I I"
            using asm1 res1
            by auto
        next
          case False
          have "prod_list_mat a\<^sub>1 \<in> M\<^sub>I I"
            using prod_list_mat_closed[of "M\<^sub>I I" a\<^sub>1] submonoid_M\<^sub>I
              False a_p(1) M\<^sub>I_in_carr M\<^sub>I_closed_mult
            by auto
          then have "prod_list_mat a\<^sub>1 * A \<in> M\<^sub>I I"
            using asm1 M\<^sub>I_closed_mult
            by auto
          then show "(prod_list_mat a\<^sub>1 * A * prod_list_mat a\<^sub>2) \<in> M\<^sub>I I"
            using res1 by auto
        qed
      qed
    }
    then show ?thesis unfolding core_def
      using asm1 M\<^sub>I_el_in_carr M\<^sub>I_in_P in_mono
      by auto
  qed
qed


end (*index set I non empty*)
end (*matrix sets*)
end (*matrices of size n*)


end