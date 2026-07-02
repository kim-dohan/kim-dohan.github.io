theory Matrix_TRS_Impl
  imports 
    Matrix_TRS
    Certification_Monads.Check_Monad
    Certification_Monads.Error_Monad
    Show.Shows_Literal
    Jordan_Normal_Form.Matrix_Impl
begin

abbreviation "I \<equiv> LPI" 
abbreviation "Ip \<equiv> LPIp" 

abbreviation list_of_mat_to_list_of_list :: "'a mat list \<Rightarrow> 'a list list list"
  where
"list_of_mat_to_list_of_list \<equiv> map mat_to_list"



subsection \<open>Basic checks related to Matrix_Base\<close>
\<comment> \<open>checks on: carrier_mat n n, positive cone, strictly positive cone,
    E_I, M_I, P_I, set of indices I\<close>


definition check_carrier :: "nat \<Rightarrow> int mat \<Rightarrow> showsl check" where
"check_carrier n M = do {
  check (dim_row M = n) (showsl_lit (STR ''Expected '') o showsl n o
         showsl_lit (STR '' rows in matrix, got '') o showsl (dim_row M));
  check (dim_col M = n) (showsl_lit (STR ''Expected '') o showsl n o
         showsl_lit (STR '' columns in matrix, got '') o showsl (dim_col M))
}"
lemma check_carrier[simp]: assumes "isOK (check_carrier n M)"
  shows "M \<in> carrier_mat n n"
  using assms[unfolded check_carrier_def, simplified] by auto
  

definition check_N :: "nat \<Rightarrow> int mat \<Rightarrow> showsl check" where
"check_N n M = (do {
    check_carrier n M;
    check (\<forall>i < n. \<forall>j < n. M $$ (i,j) \<ge> 0)
         (showsl_lit (STR ''Expected all matrix element to be greater than or equal to zero: '')
          o showsl (mat_to_list M))
})"
lemma check_N[simp]: assumes "isOK (check_N n M)"
  shows "M \<in> squared_int_mat.N n"
  using assms[unfolded check_N_def, simplified] squared_int_mat.N_compo_greater_eq_zero2 by auto

lemma check_N_carr[simp]: assumes "isOK (check_N n M)"
  shows "isOK (check_carrier n M)"
  using assms[unfolded check_N_def, simplified] by auto


definition check_P :: "nat \<Rightarrow> int mat \<Rightarrow> showsl check" where
"check_P n M = (do {
    check_N n M;
    check (\<exists>i < n. \<exists>j < n. M $$ (i,j) > 0)
          (showsl_lit (STR ''Expected at least one non-null element: '')
          o showsl (mat_to_list M))
})"
lemma check_P[simp]: assumes "isOK (check_P n M)"
  shows "M \<in> squared_int_mat.P n"
  using assms[unfolded check_P_def, simplified] squared_int_mat.P_N_one_elem_nonnull by auto

lemma check_P_N[simp]: assumes "isOK (check_P n M)"
  shows "isOK (check_N n M)"
  using assms[unfolded check_P_def, simplified] by auto


definition check_indices :: "nat \<Rightarrow> nat list \<Rightarrow> showsl check" where
"check_indices n ids = (do {
    check (set ids \<noteq> {}) (showsl_lit (STR ''Set of indices should not be empty''));
    check (set ids \<subseteq> {0..< n}) (showsl_lit (STR ''I should be a subset of {0..n-1}''))
})"
lemma check_indices[simp]: assumes "isOK (check_indices n ids)"
  shows "set ids \<noteq> {} \<and> set ids \<subseteq> {0..< n}"
  using assms[unfolded check_indices_def, simplified] by auto


definition check_E\<^sub>I :: "nat \<Rightarrow> nat list \<Rightarrow> int mat \<Rightarrow> showsl check" where
"check_E\<^sub>I n ids M = (do {
    check_indices n ids;
    check_N n M;
    check (\<forall>i \<in> set ids. M $$ (i,i) > 0)
         (showsl_lit (STR ''[E_I set] Expected all diagonal elements to be non-null: '')
          o showsl (mat_to_list M))
})"
lemma check_E\<^sub>I[simp]: assumes "isOK (check_E\<^sub>I n ids M)"
  shows "M \<in> squared_int_mat.E\<^sub>I n (set ids)"
  using assms[unfolded check_E\<^sub>I_def, simplified] squared_int_mat.E\<^sub>I_def by auto

lemma check_E\<^sub>I_indices[simp]: assumes "isOK (check_E\<^sub>I n ids M)"
  shows "isOK (check_indices n ids)"
  using assms[unfolded check_E\<^sub>I_def, simplified] by auto

lemma check_E\<^sub>I_N[simp]: assumes "isOK (check_E\<^sub>I n ids M)"
  shows "isOK (check_N n M)"
  using assms[unfolded check_E\<^sub>I_def, simplified] by auto
 



definition check_P\<^sub>I :: "nat \<Rightarrow> nat list \<Rightarrow> int mat \<Rightarrow> showsl check" where
"check_P\<^sub>I n ids M = (do {
    check_indices n ids;
    check_N n M;
    check (\<exists>i \<in> set ids. \<exists>j \<in> set ids. M $$ (i,j) > 0)
         (showsl_lit (STR ''[P_I set] Expected at least 1 non-null element, got 0''))
})"
lemma check_P\<^sub>I[simp]: assumes "isOK (check_P\<^sub>I n ids M)"
  shows "M \<in> squared_int_mat.P\<^sub>I n (set ids)"
  using assms[unfolded check_P\<^sub>I_def, simplified] squared_int_mat.P\<^sub>I_def by auto

lemma check_P\<^sub>I_indices[simp]: assumes "isOK (check_P\<^sub>I n ids M)"
  shows "isOK (check_indices n ids)"
  using assms[unfolded check_P\<^sub>I_def, simplified] by auto

lemma check_P\<^sub>I_N[simp]: assumes "isOK (check_P\<^sub>I n ids M)"
  shows "isOK (check_N n M)"
  using assms[unfolded check_P\<^sub>I_def, simplified] by auto


definition check_M\<^sub>I :: "nat \<Rightarrow> nat list \<Rightarrow> int mat \<Rightarrow> showsl check" where
"check_M\<^sub>I n ids M = (do {
    check_indices n ids;
    check_N n M;
    check (\<forall>i \<in> set ids. \<exists>j \<in> set ids. M $$ (i,j) > 0)
         (showsl_lit (STR ''[M_I set] Expected at least 1 non-null element per row: '')
          o showsl (mat_to_list M))
})"
lemma check_M\<^sub>I[simp]: assumes "isOK (check_M\<^sub>I n ids M)"
  shows "M \<in> squared_int_mat.M\<^sub>I n (set ids)"
  using assms[unfolded check_M\<^sub>I_def, simplified] squared_int_mat.M\<^sub>I_def by auto

lemma check_M\<^sub>I_indices[simp]: assumes "isOK (check_M\<^sub>I n ids M)"
  shows "isOK (check_indices n ids)"
  using assms[unfolded check_M\<^sub>I_def, simplified] by auto

lemma check_M\<^sub>I_N[simp]: assumes "isOK (check_M\<^sub>I n ids M)"
  shows "isOK (check_N n M)"
  using assms[unfolded check_M\<^sub>I_def, simplified] by auto




subsection \<open>Terms-related checks, related to Matrix_TRS and Linear_Poly_Interpretation\<close>
\<comment> \<open>checks on: Variable interpretations being in the strict carrier (see strictly_ordered_semiring),
    having the right number of function interpretation coefficients and them begin in the strict carrier\<close>


type_synonym 'v variables = "'v list" \<comment> \<open>the list of variables occurring in a TRS\<close>
type_synonym 'v assignment = "('v, int mat) p_ass"
  \<comment> \<open>the list of variables occurring in a TRS and their corresponding interpretation\<close>
type_synonym 'f fun_coeffs = "(('f \<times> nat) \<times> (int mat list \<times> int mat)) list"
  \<comment> \<open>the list of function symbols occurring in a TRS and their corresponding interpretation coefficients\<close>

find_consts "'a list \<Rightarrow> showsl check"

definition check_assignment_E\<^sub>I ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'v variables \<Rightarrow> 'v assignment \<Rightarrow> showsl check"
  where
"check_assignment_E\<^sub>I n ids vs \<alpha> = (do {
    check_indices n ids; \<comment> \<open>This line is required in case vs is empty, and check_EI is never triggered\<close>
    check_allm (\<lambda>a. check_E\<^sub>I n ids (\<alpha> a)) vs <+? (\<lambda>str. showsl_lit (STR ''Expected all variable assignment matrices to be in E_I.\<newline>'') o str)
})"
lemma check_assignment_E\<^sub>I_triv[simp]: assumes "isOK (check_assignment_E\<^sub>I n ids vs \<alpha>)"
  shows "\<And>x. x \<in> set vs \<Longrightarrow> \<alpha> x \<in> squared_int_mat.E\<^sub>I n (set ids)"
  using assms[unfolded check_assignment_E\<^sub>I_def, simplified] by auto

lemma check_assignment_E\<^sub>I[simp]: assumes "isOK (check_assignment_E\<^sub>I n ids vs \<alpha>)"
  shows "range (\<lambda>v. if v \<in> set vs then \<alpha> v else 1\<^sub>m n) \<subseteq> squared_int_mat.E\<^sub>I n (set ids)"
proof -
  from assms[unfolded check_assignment_E\<^sub>I_def, simplified]
  have "set ids \<noteq> {}" "set ids \<subseteq> {0..< n}" "\<forall>a \<in> set vs. \<alpha> a \<in> squared_int_mat.E\<^sub>I n (set ids)"
    using check_indices by auto
  moreover
  have "1\<^sub>m n \<in> squared_int_mat.E\<^sub>I n (set ids)"
    using squared_int_mat.one_in_E\<^sub>I[of "set ids" n, OF calculation(2,1)].
  ultimately
  show ?thesis by auto
qed 

lemma check_assignment_E\<^sub>I_indices[simp]: assumes "isOK (check_assignment_E\<^sub>I n ids vs \<alpha>)"
  shows "isOK (check_indices n ids)"
  using assms[unfolded check_assignment_E\<^sub>I_def, simplified] by auto
  


definition check_assignment_M\<^sub>I ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'v variables \<Rightarrow> 'v assignment \<Rightarrow> showsl check"
  where
"check_assignment_M\<^sub>I n ids vs \<alpha> = (do {
    check_indices n ids; \<comment> \<open>This line is required in case vs is empty, and check_MI is never triggered\<close>
    check_allm (\<lambda>a. check_M\<^sub>I n ids (\<alpha> a)) vs <+? (\<lambda>str. showsl_lit (STR ''Expected all variable assignment matrices to be in M_I.\<newline>'') o str)
})"
lemma check_assignment_M\<^sub>I_triv[simp]: assumes "isOK (check_assignment_M\<^sub>I n ids vs \<alpha>)"
  shows "\<And>x. x \<in> set vs \<Longrightarrow> \<alpha> x \<in> squared_int_mat.M\<^sub>I n (set ids)"
  using assms[unfolded check_assignment_M\<^sub>I_def, simplified] by auto

lemma check_assignment_M\<^sub>I[simp]: assumes "isOK (check_assignment_M\<^sub>I n ids vs \<alpha>)"
  shows "range (\<lambda>v. if v \<in> set vs then \<alpha> v else 1\<^sub>m n) \<subseteq> squared_int_mat.M\<^sub>I n (set ids)"
proof -
  from assms[unfolded check_assignment_M\<^sub>I_def, simplified]
  have "set ids \<noteq> {}" "set ids \<subseteq> {0..< n}" "\<forall>a \<in> set vs. \<alpha> a \<in> squared_int_mat.M\<^sub>I n (set ids)"
    using check_indices by auto
  moreover
  have "1\<^sub>m n \<in> squared_int_mat.M\<^sub>I n (set ids)"
    using squared_int_mat.one_in_M\<^sub>I[of "set ids" n, OF calculation(2,1)].
  ultimately
  show ?thesis by auto
qed

lemma check_assignment_M\<^sub>I_indices[simp]: assumes "isOK (check_assignment_M\<^sub>I n ids vs \<alpha>)"
  shows "isOK (check_indices n ids)"
  using assms[unfolded check_assignment_M\<^sub>I_def, simplified] by auto



definition check_coeffs_length :: "'f :: showl fun_coeffs \<Rightarrow> showsl check"
  where
"check_coeffs_length fc = check_allm (\<lambda>fx. case fx of ((f,n), (cs,c)) \<Rightarrow>
 check (length cs = n) (showsl_lit (STR ''Expected as many multiplicative coefficients as the arity of '') o showsl f o
       showsl_lit (STR ''. Got '') o showsl (length cs) o showsl_lit (STR '' instead of '') o showsl n)) fc
<+? (\<lambda>str. showsl_lit (STR ''The number of interpretation coefficients (multiplicative, i.e. not the constant coefficient)
 should always match the arity of the corresponding function symbol.\<newline>'') o str)"
lemma check_coeffs_length[simp]: assumes "isOK (check_coeffs_length fc)"
  shows "((f,n),(cs,c)) \<in> set fc \<Longrightarrow> length cs = n"
  using assms[unfolded check_coeffs_length_def, simplified] by auto


definition check_coefficients_N ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> showsl check"
  where
"check_coefficients_N n ids fc = (do {
    check_indices n ids; \<comment> \<open>This line is required in case fc is empty, and check_N is never triggered\<close>
    check_allm (\<lambda>fx. case fx of ((f,m),(cs,c)) \<Rightarrow>
       check_allm (check_N n) (c#cs) <+? (\<lambda>str. showsl_lit (STR ''Expected all interpretation coefficients of symbol '')
 o showsl f o showsl_lit (STR '' to be in N\<newline>'') o str)
    ) fc <+? (\<lambda>str. showsl_lit (STR ''Expected all interpretation coefficients of all function symbols used to be in N.\<newline>'') o str)
})"
lemma check_coefficients_N[simp]: assumes "isOK (check_coefficients_N n ids fc)"
  shows "((f,m),(cs,c)) \<in> set fc \<Longrightarrow> set (c#cs) \<subseteq> squared_int_mat.N n"
  using assms[unfolded check_coefficients_N_def, simplified] by auto

lemma check_coefficients_N_indices[simp]: assumes "isOK (check_coefficients_N n ids fc)"
  shows "isOK (check_indices n ids)"
  using assms[unfolded check_coefficients_N_def, simplified] by auto 


definition check_coefficients_E\<^sub>I ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> showsl check"
  where
"check_coefficients_E\<^sub>I n ids fc = (do {
    check_coefficients_N n ids fc;
    check_allm (\<lambda>fx. case fx of ((f,m),(cs,c)) \<Rightarrow> (do{
        check_allm (check_E\<^sub>I n ids) cs <+? (\<lambda>str. showsl_lit(STR ''Expected all interpretation multiplicative coefficients of symbol '')
 o showsl f o showsl_lit(STR '' to be in E_I.\<newline>'') o str);
        check (\<exists>ci \<in> set(c#cs). isOK (check_E\<^sub>I n ids ci)) (
          (showsl_lit(STR ''Expected the constant coefficient '') o showsl (mat_to_list c) o
 showsl_lit(STR '' of symbol '') o showsl f o
 showsl_lit(STR '' to be in E_I whenever there are no multiplicative coefficient (i.e. symbol of arity 0).''))
        )
      })
    ) fc <+? (\<lambda>str. showsl_lit(STR ''Expected all interpretation multiplicative coeffs to be in E_I
 and the constant coeff to be in E_I whenever there are none multiplicative coeffs, for all function symbols.\<newline>'') o str)
})"
lemma check_coefficients_E\<^sub>I[simp]: assumes "isOK (check_coefficients_E\<^sub>I n ids fc)"
  shows "((f,m),(cs,c)) \<in> set fc \<Longrightarrow> set cs \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<and>
 set (c#cs) \<inter> squared_int_mat.E\<^sub>I n (set ids) \<noteq> {}"
proof -
  assume as: "((f,m),(cs,c)) \<in> set fc"

  then have "\<forall>ci \<in> set cs. ci \<in> squared_int_mat.E\<^sub>I n (set ids)"
            "\<exists>ci \<in> set (c#cs). ci \<in> squared_int_mat.E\<^sub>I n (set ids)"
    using assms[unfolded check_coefficients_E\<^sub>I_def, simplified] check_E\<^sub>I
    by auto
  then show ?thesis by auto
qed
  
  
lemma check_coefficients_E\<^sub>I_N[simp]: assumes "isOK (check_coefficients_E\<^sub>I n ids fc)"
  shows "isOK (check_coefficients_N n ids fc)"
  using assms[unfolded check_coefficients_E\<^sub>I_def, simplified] by auto



definition check_coefficients_M\<^sub>I ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> showsl check"
  where
"check_coefficients_M\<^sub>I n ids fc = (do {
    check_coefficients_N n ids fc;
    check_allm (\<lambda>fx. case fx of ((f,m),(cs,c)) \<Rightarrow> (do{
        check_allm (check_M\<^sub>I n ids) cs <+? (\<lambda>str. showsl_lit(STR ''Expected all interpretation multiplicative coefficients of symbol '')
 o showsl f o showsl_lit(STR '' to be in M_I.\<newline>'') o str);
        check (\<exists>ci \<in> set(c#cs). isOK (check_M\<^sub>I n ids ci)) (
          (showsl_lit(STR ''Expected the constant coefficient '') o showsl (mat_to_list c) o
 showsl_lit(STR '' of symbol '') o showsl f o
 showsl_lit(STR '' to be in M_I whenever there are no multiplicative coefficient (i.e. symbol of arity 0).''))
        )
      })
    ) fc <+? (\<lambda>str. showsl_lit(STR ''Expected all interpretation multiplicative coeffs to be in M_I
 and the constant coeff to be in M_I whenever there are none multiplicative coeffs, for all function symbols.\<newline>'') o str)
})"
lemma check_coefficients_M\<^sub>I[simp]: assumes "isOK (check_coefficients_M\<^sub>I n ids fc)"
  shows "((f,m), (cs,c)) \<in> set fc \<Longrightarrow> set cs \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<and>
set (c#cs) \<inter> squared_int_mat.M\<^sub>I n (set ids) \<noteq> {}"
proof -
  assume as: "((f,m),(cs,c)) \<in> set fc"
  then have "\<forall>ci \<in> set cs. ci \<in> squared_int_mat.M\<^sub>I n (set ids)"
            "\<exists>ci \<in> set (c#cs). ci \<in> squared_int_mat.M\<^sub>I n (set ids)"
    using assms[unfolded check_coefficients_M\<^sub>I_def, simplified]
    by auto
  then show ?thesis by auto
qed

lemma check_coefficients_M\<^sub>I_N[simp]: assumes "isOK (check_coefficients_M\<^sub>I n ids fc)"
  shows "isOK (check_coefficients_N n ids fc)"
  using assms[unfolded check_coefficients_M\<^sub>I_def, simplified] by auto



subsection \<open>Fake coefficient-generator functions built from the list of function symbols and their interpretation.\<close>
text \<open>pI' is the instantiation of the pI in Linear_Poly_Interpretation.
    Outside the provided function symbols, identity matrices are given in place of useful interpretation,
    c.f. @{const default_mat_inter}.
    The identity matrix is in $E_I$, $M_I$ and also $P_I$, making it a suitable choice.\<close>
text \<open>Perform checks that are required by @{const lin_poly_inter} and @{const mono_lin_poly_inter}.\<close>

definition pI' ::
 "nat \<Rightarrow> 'f fun_coeffs \<Rightarrow> ('f \<times> nat \<Rightarrow> int mat list \<times> int mat)"
  where
    "pI' n fc \<equiv> (\<lambda>(f,n1). case map_of fc (f,n1) of Some val \<Rightarrow> val | None \<Rightarrow> default_mat_inter n n1)"

lemma check_pI'_length[simp]: assumes "isOK (check_coeffs_length fc)"
  shows "let (cs, _) = pI' n fc f in length cs = snd f"
proof -
  obtain f' n1 where f: "f = (f',n1)" by force
  show ?thesis proof (cases "map_of fc f")
    case None
    thus ?thesis unfolding f pI'_def Let_def split by (auto simp: default_mat_inter_def)
  next
    case (Some val)
    then obtain cs c where Some: "map_of fc f = Some (cs,c)" by (cases val, auto)
    hence pI': "pI' n fc f = (cs,c)" unfolding f pI'_def Let_def by auto
    from map_of_SomeD[OF Some, unfolded f]
    have "((f', n1), cs, c) \<in> set fc" by auto
    from check_coeffs_length[OF assms this] pI' show ?thesis using f by auto
  qed
qed

lemma check_pI'_N[simp]: assumes "isOK (check_coefficients_N n ids fc)"
  shows "let (cs, c) = pI' n fc f in set (c#cs) \<subseteq> squared_int_mat.N n"
proof -
  obtain f' n1 where f: "f = (f',n1)" by force
  show ?thesis proof (cases "map_of fc f")
    case None
    thus ?thesis unfolding f pI'_def Let_def split default_mat_inter_def 
      using squared_int_mat.one_in_N by auto
  next
    case (Some val)
    then obtain cs c where Some: "map_of fc f = Some (cs,c)" by (cases val, auto)
    hence pI': "pI' n fc f = (cs,c)" unfolding f pI'_def Let_def by auto
    from map_of_SomeD[OF Some, unfolded f]
    have "((f', n1), cs, c) \<in> set fc" by auto
    then show ?thesis using f check_coefficients_N[OF assms] pI' by auto
  qed
qed

lemma check_pI'_E\<^sub>I[simp]: assumes "isOK (check_coefficients_E\<^sub>I n ids fc)"
  shows "let (cs,c) = pI' n fc f in set cs \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<and>
set (c#cs) \<inter> squared_int_mat.E\<^sub>I n (set ids) \<noteq> {}"
proof -
  obtain f' n1 where f: "f = (f',n1)" by force
  show ?thesis proof (cases "map_of fc f")
    case None
    thus ?thesis unfolding f pI'_def Let_def split default_mat_inter_def
      using squared_int_mat.one_in_E\<^sub>I
            check_indices[OF check_coefficients_N_indices[OF check_coefficients_E\<^sub>I_N[OF assms]]]
      by auto
  next
    case (Some val)
    then obtain cs c where Some: "map_of fc f = Some (cs,c)" by (cases val, auto)
    hence pI': "pI' n fc f = (cs,c)" unfolding f pI'_def Let_def by auto
    from map_of_SomeD[OF Some, unfolded f]
    have "((f', n1), cs, c) \<in> set fc" by auto
    then show ?thesis using f check_coefficients_E\<^sub>I[OF assms] pI' by auto
  qed
qed


lemma check_pI'_M\<^sub>I[simp]: assumes "isOK (check_coefficients_M\<^sub>I n ids fc)"
  shows "let (cs,c) = pI' n fc f in set cs \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<and>
set (c#cs) \<inter> squared_int_mat.M\<^sub>I n (set ids) \<noteq> {}"
proof -
  obtain f' n1 where f: "f = (f',n1)" by force
  show ?thesis proof (cases "map_of fc f")
    case None
    thus ?thesis unfolding f pI'_def Let_def split default_mat_inter_def
      using squared_int_mat.one_in_M\<^sub>I
            check_indices[OF check_coefficients_N_indices[OF check_coefficients_M\<^sub>I_N[OF assms]]]
      by auto
  next
    case (Some val)
    then obtain cs c where Some: "map_of fc f = Some (cs,c)" by (cases val, auto)
    hence pI': "pI' n fc f = (cs,c)" unfolding f pI'_def Let_def by auto
    from map_of_SomeD[OF Some, unfolded f]
    have "((f', n1), cs, c) \<in> set fc" by auto
    then show ?thesis using f check_coefficients_M\<^sub>I[OF assms] pI' by auto
  qed
qed



definition check_coeffs_E\<^sub>I_final where
"check_coeffs_E\<^sub>I_final n ids fc = (do {
    check_coeffs_length fc;
    check_coefficients_N n ids fc;
    check_coefficients_E\<^sub>I n ids fc
})"

lemma check_coeffs_E\<^sub>I_final_triv[simp]: assumes "isOK (check_coeffs_E\<^sub>I_final n ids fc)"
  shows "isOK (check_coeffs_length fc)" "isOK ( check_coefficients_N n ids fc)"
 "isOK (check_coefficients_E\<^sub>I n ids fc)"
  using assms[unfolded check_coeffs_E\<^sub>I_final_def] by auto

lemma check_coeffs_E\<^sub>I_final[simp]: assumes "isOK (check_coeffs_E\<^sub>I_final n ids fc)"
  shows "pI' n fc (f, n1) = (cs, c) \<Longrightarrow>
    set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set cs \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<and>
    set (c#cs) \<inter> squared_int_mat.E\<^sub>I n (set ids) \<noteq> {}"
proof -
  assume as: "pI' n fc (f, n1) = (cs, c)"
  have "set (c # cs) \<subseteq> squared_int_mat.N n"
    using as check_pI'_N[OF check_coeffs_E\<^sub>I_final_triv(2)[OF assms], of "(f,n1)"]
    by auto
  moreover
  have "length cs = n1"
    using as check_pI'_length[OF check_coeffs_E\<^sub>I_final_triv(1)[OF assms], of n "(f, n1)"]
    by auto
  moreover
  have "set cs \<subseteq> squared_int_mat.E\<^sub>I n (set ids)" "set (c#cs) \<inter> squared_int_mat.E\<^sub>I n (set ids) \<noteq> {}"
    using as check_pI'_E\<^sub>I[OF check_coeffs_E\<^sub>I_final_triv(3)[OF assms], of "(f,n1)"]
    by auto
  ultimately
  show ?thesis by auto
qed
  


subsection \<open>Final checks on the function symbols' interpretation coefficients\<close>
\<comment> \<open>Using both the section on coefficients being in the strict carrier and the section on
    pI'.\<close>

definition check_coeffs_M\<^sub>I_final where
"check_coeffs_M\<^sub>I_final n ids fc = (do {
    check_coeffs_length fc;
    check_coefficients_N n ids fc;
    check_coefficients_M\<^sub>I n ids fc
})"
lemma check_coeffs_M\<^sub>I_final_triv[simp]: assumes "isOK (check_coeffs_M\<^sub>I_final n ids fc)"
  shows "isOK (check_coeffs_length fc)" "isOK (check_coefficients_N n ids fc)"
 "isOK (check_coefficients_M\<^sub>I n ids fc)"
  using assms[unfolded check_coeffs_M\<^sub>I_final_def] by auto

lemma check_coeffs_M\<^sub>I_final[simp]: assumes "isOK (check_coeffs_M\<^sub>I_final n ids fc)"
  shows "pI' n fc (f, n1) = (cs, c) \<Longrightarrow>
 set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set cs \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<and>
set (c#cs) \<inter> squared_int_mat.M\<^sub>I n (set ids) \<noteq> {}"
proof -
  assume as: "pI' n fc (f, n1) = (cs, c)"
  have "set (c # cs) \<subseteq> squared_int_mat.N n"
    using as check_pI'_N[OF check_coeffs_M\<^sub>I_final_triv(2)[OF assms], of "(f,n1)"]
    by auto
  moreover
  have "length cs = n1"
    using as check_pI'_length[OF check_coeffs_M\<^sub>I_final_triv(1)[OF assms], of n "(f, n1)"]
    by auto
  moreover
  have "set cs \<subseteq> squared_int_mat.M\<^sub>I n (set ids)" "set (c#cs) \<inter> squared_int_mat.M\<^sub>I n (set ids) \<noteq> {}"
    using as check_pI'_M\<^sub>I[OF check_coeffs_M\<^sub>I_final_triv(3)[OF assms], of "(f,n1)"]
    by auto
  ultimately
  show ?thesis by auto
qed



subsection \<open>Useless cruft section\<close>
\<comment> \<open>Proving that every single polynomial evaluation function being used by the implementation
    is the same regardless of mat_interpretation_parameter.Matsemiring being used instead of
    mat_interpretation_parameter.R_mat_semiring.\<close>

definition RringEI where "RringEI n ids = mat_interpretation_parameter.R_mat_semiring n
 (squared_int_mat.E\<^sub>I n (set ids)) (squared_int_mat.core n (squared_int_mat.E\<^sub>I n (set ids)))"
definition RringMI where "RringMI n ids = mat_interpretation_parameter.R_mat_semiring n
 (squared_int_mat.M\<^sub>I n (set ids)) (squared_int_mat.core n (squared_int_mat.M\<^sub>I n (set ids)))"
definition Rring where "Rring n = mat_interpretation_parameter.Matsemiring n"


definition RringSet where "RringSet n ids S U =
 mat_interpretation_parameter.R_mat_semiring n (S n ids) (U n ids)"

lemma vpoly_eq: "vpoly (RringSet n ids S U) a = vpoly (Rring n) a"
  unfolding vpoly_def RringSet_def Rring_def
            mat_interpretation_parameter.R_mat_semiring_def
            mat_interpretation_parameter.Matsemiring_def
  by auto
lemma add_var_eq: "add_var (RringSet n ids S U) x a xs = add_var (Rring n) x a xs"
proof (induction xs)
  case Nil
  then show ?case unfolding add_var.simps by (rule refl)
next
  case (Cons xa xs)
  then show ?case
  proof (cases xa)
    case (Pair t u)
    then show ?thesis
    proof -
      let ?R1 = "RringSet n ids S U"
      let ?R2 = "Rring n"
      have "add_var ?R1 x a (xa # xs) =
 (if x = t then (let s = a \<oplus>\<^bsub>?R1\<^esub> u in if s = \<zero>\<^bsub>?R1\<^esub> then xs else (x, s) # xs)
    else ((t, u) # add_var ?R1 x a xs))"
        using Pair by auto
      also have "\<dots> =
 (if x = t then (let s = a \<oplus>\<^bsub>?R2\<^esub> u in if s = \<zero>\<^bsub>?R2\<^esub> then xs else (x, s) # xs)
    else ((t, u) # add_var ?R2 x a xs))"
      proof -
        have "\<zero>\<^bsub>?R1\<^esub> = \<zero>\<^bsub>?R2\<^esub>"
          unfolding RringSet_def Rring_def
                    mat_interpretation_parameter.R_mat_semiring_def
                    mat_interpretation_parameter.Matsemiring_def
          by auto
        moreover
        have "a \<oplus>\<^bsub>?R1\<^esub> u = a \<oplus>\<^bsub>?R2\<^esub> u"
          unfolding RringSet_def Rring_def
                    mat_interpretation_parameter.R_mat_semiring_def
                    mat_interpretation_parameter.Matsemiring_def
          by auto
        ultimately
        show ?thesis using Cons.IH by auto
      qed
      also have "\<dots> = add_var ?R2 x a (xa # xs)"
        using Pair by auto
      finally show ?thesis.
    qed
  qed
qed

lemma sum_pvars_eq: "sum_pvars (RringSet n ids S U) vas vbs = sum_pvars (Rring n) vas vbs"
proof (induction vas arbitrary: vbs)
  case Nil
  then show ?case unfolding sum_pvars.simps by (rule refl)
next
  case (Cons a vas)
  then show ?case
  proof (cases a)
    case (Pair x y)
    then show ?thesis
    proof -
      let ?R1 = "RringSet n ids S U"
      let ?R2 = "Rring n"
      have "sum_pvars ?R1 (a # vas) vbs = (if y = \<zero>\<^bsub>?R1\<^esub> then sum_pvars ?R1 vas vbs
    else sum_pvars ?R1 vas (add_var ?R1 x y vbs))"
        using Pair by auto
      also have "\<dots> = (if y = \<zero>\<^bsub>?R2\<^esub> then sum_pvars ?R2 vas vbs
    else sum_pvars ?R2 vas (add_var ?R2 x y vbs))"
      proof -
        have "\<zero>\<^bsub>?R1\<^esub> = \<zero>\<^bsub>?R2\<^esub>"
          unfolding RringSet_def Rring_def
                    mat_interpretation_parameter.R_mat_semiring_def
                    mat_interpretation_parameter.Matsemiring_def
          by auto
        moreover
        have "add_var ?R1 x y vbs = add_var ?R2 x y vbs"
          using add_var_eq[of n ids S U x y vbs]
          by auto
        ultimately
        show ?thesis using Cons.IH by auto
      qed
      also have "\<dots> = sum_pvars ?R2 (a # vas) vbs"
        using Pair by auto
      finally show ?thesis.
    qed
  qed
qed

lemma sum_lpoly_eq: "sum_lpoly (RringSet n ids S U) p q = sum_lpoly (Rring n) p q"
proof -
  obtain a b where p: "p = LPoly a b"
    using l_poly.exhaust by auto
  obtain c d where q: "q = LPoly c d"
    using l_poly.exhaust by auto

  let ?R1 = "RringSet n ids S U"
  let ?R2 = "Rring n"
  have "sum_lpoly ?R1 p q = LPoly (a \<oplus>\<^bsub>?R1\<^esub> c) (sum_pvars ?R1 b d)"
    using p q by auto
  also have "\<dots> = LPoly (a \<oplus>\<^bsub>?R1\<^esub> c) (sum_pvars ?R2 b d)"
    using sum_pvars_eq by auto
  also have "\<dots> = LPoly (a \<oplus>\<^bsub>?R2\<^esub> c) (sum_pvars ?R2 b d)"
    unfolding RringSet_def Rring_def
              mat_interpretation_parameter.R_mat_semiring_def
              mat_interpretation_parameter.Matsemiring_def
    by auto
  also have "\<dots> = sum_lpoly ?R2 p q"
    using p q by auto
  finally show ?thesis.
qed

lemma list_sum_poly_eq: "list_sum_poly (RringSet n ids S U) xs = list_sum_poly (Rring n) xs"
proof (induction xs)
  case Nil
  then show ?case unfolding list_sum_poly.simps RringSet_def Rring_def
      mat_interpretation_parameter.R_mat_semiring_def
      mat_interpretation_parameter.Matsemiring_def
    by auto
next
  case (Cons a xs)
  then show ?case unfolding list_sum_poly.simps using sum_lpoly_eq by auto
qed

lemma mul_pvars_eq: "mul_pvars (RringSet n ids S U) a xs = mul_pvars (Rring n) a xs"
proof (induction xs)
  case Nil
  then show ?case unfolding mul_pvars.simps by (rule refl)
next
  case (Cons x xs)
  then show ?case
  proof (cases x)
    case (Pair x1 x2)
    then show ?thesis
    proof -
      let ?R1 = "RringSet n ids S U"
      let ?R2 = "Rring n"
      have "mul_pvars ?R1 a (x # xs) = (let p = a \<otimes>\<^bsub>?R1\<^esub> x2;
         res = mul_pvars ?R1 a xs in
    if p = \<zero>\<^bsub>?R1\<^esub> then res else (x1, p) # res)"
        using Pair by auto
      also have "\<dots> = (let p = a \<otimes>\<^bsub>?R2\<^esub> x2;
         res = mul_pvars ?R2 a xs in
    if p = \<zero>\<^bsub>?R2\<^esub> then res else (x1, p) # res)"
      proof -
        have "\<zero>\<^bsub>?R1\<^esub> = \<zero>\<^bsub>?R2\<^esub>"
          unfolding RringSet_def Rring_def
                    mat_interpretation_parameter.R_mat_semiring_def
                    mat_interpretation_parameter.Matsemiring_def
          by auto
        moreover
        have "a \<otimes>\<^bsub>?R1\<^esub> x2 = a \<otimes>\<^bsub>?R2\<^esub> x2"
          unfolding RringSet_def Rring_def
                    mat_interpretation_parameter.R_mat_semiring_def
                    mat_interpretation_parameter.Matsemiring_def
          by auto
        ultimately
        show ?thesis using Cons.IH by auto
      qed
      also have "\<dots> = mul_pvars ?R2 a (x # xs)"
        using Pair by auto
      finally show ?thesis.
    qed
  qed
qed

lemma mul_lpoly_eq: "mul_lpoly (RringSet n ids S U) a p = mul_lpoly (Rring n) a p"
proof (cases p)
  case (LPoly b c)
  then show ?thesis
  proof -
    let ?R1 = "RringSet n ids S U"
    let ?R2 = "Rring n"
    have "mul_lpoly ?R1 a p = LPoly (a \<otimes>\<^bsub>?R1\<^esub> b) (mul_pvars ?R1 a c)"
      using LPoly by auto
    also have "\<dots> = LPoly (a \<otimes>\<^bsub>?R1\<^esub> b) (mul_pvars ?R2 a c)"
      using mul_pvars_eq
      by auto
    also have "\<dots> = LPoly (a \<otimes>\<^bsub>?R2\<^esub> b) (mul_pvars ?R2 a c)"
      unfolding RringSet_def Rring_def
                mat_interpretation_parameter.R_mat_semiring_def
                mat_interpretation_parameter.Matsemiring_def
      by auto
    also have "\<dots> = mul_lpoly ?R2 a p"
      using LPoly by auto
    finally show ?thesis.
  qed
qed

lemma evalp_eq: "evalp (RringSet n ids S U) p t = evalp (Rring n) p t"
proof (induction t)
  case (Var x)
  then show ?case unfolding Term.eval_term.simps by (rule vpoly_eq)
next
  case (Fun f xs)
  then show ?case
  proof -
    let ?R1 = "RringSet n ids S U"
    let ?R2 = "Rring n"
    have "evalp ?R1 p (Fun f xs) = Ip ?R1 p f [evalp ?R1 p s. s \<leftarrow> xs]"
      by auto
    also have "\<dots> = Ip ?R1 p f [evalp ?R2 p s. s \<leftarrow> xs]"
    proof -
      have "[evalp ?R1 p s. s \<leftarrow> xs] = [evalp ?R2 p s. s \<leftarrow> xs]"
        using Fun.IH by auto
      then show ?thesis by argo
    qed
    also have "\<dots> = Ip ?R2 p f [evalp ?R2 p s. s \<leftarrow> xs]"
    proof (cases "p (f, length [evalp ?R2 p s. s \<leftarrow> xs])")
      case (Pair cs c)
      then show ?thesis
      proof -
        define as where "as = [evalp ?R2 p s. s \<leftarrow> xs]"
        have "Ip ?R1 p f as =
          list_sum_poly ?R1 (c_lpoly c # map (\<lambda> ca. mul_lpoly ?R1 (fst ca) (snd ca))
             (zip cs as))"
          unfolding Ip_def as_def
          using Pair
          by auto
        also have "\<dots> = list_sum_poly ?R1 (c_lpoly c # map (\<lambda> ca. mul_lpoly ?R2 (fst ca) (snd ca))
             (zip cs as))"
          using mul_lpoly_eq
          by metis
        also have "\<dots> = list_sum_poly ?R2 (c_lpoly c # map (\<lambda> ca. mul_lpoly ?R2 (fst ca) (snd ca))
             (zip cs as))"
          using list_sum_poly_eq[of n ids S U]
          by blast
        also have "\<dots> = Ip ?R2 p f as"
          unfolding Ip_def as_def
          using Pair
          by auto
        finally show ?thesis unfolding as_def.
      qed
    qed
    also have "\<dots> = evalp ?R2 p (Fun f xs)"
      by auto
    finally show ?thesis.
  qed
qed

lemma sub_var_eq: "sub_var (RringSet n ids S U) a b c = sub_var (Rring n) a b c"
proof (induction a)
  case Nil
  then show ?case unfolding sub_var.simps RringSet_def Rring_def
          mat_interpretation_parameter.R_mat_semiring_def
          mat_interpretation_parameter.Matsemiring_def
    by auto
next
  case (Cons a as)
  then show ?case
  proof (cases a)
    case (Pair a1 a2)
    then show ?thesis
    proof -
      let ?R1 = "RringSet n ids S U"
      let ?R2 = "Rring n"
      have "sub_var ?R1 (a # as) b c = (
 if b = a1 then (let s = a2 \<ominus>\<ominus>\<^bsub>?R1\<^esub> c in if s = \<zero>\<^bsub>?R1\<^esub> then as else (b, s) # as)
    else ((a1, a2) # sub_var ?R1 as b c))"
        using Pair by auto
      also have "\<dots> = (
 if b = a1 then (let s = a2 \<ominus>\<ominus>\<^bsub>?R2\<^esub> c in if s = \<zero>\<^bsub>?R2\<^esub> then as else (b, s) # as)
    else ((a1, a2) # sub_var ?R2 as b c))"
      proof -
        have "a2 \<ominus>\<ominus>\<^bsub>?R1\<^esub> c = a2 \<ominus>\<ominus>\<^bsub>?R2\<^esub> c"
          unfolding expl_a_minus_def RringSet_def Rring_def
                    mat_interpretation_parameter.R_mat_semiring_def
                    mat_interpretation_parameter.Matsemiring_def
          by auto
        moreover
        have "\<zero>\<^bsub>?R1\<^esub> = \<zero>\<^bsub>?R2\<^esub>"
          unfolding Rring_def RringSet_def mat_interpretation_parameter.R_mat_semiring_def
                    mat_interpretation_parameter.Matsemiring_def
          by auto
        ultimately 
        show ?thesis using Cons.IH by auto
      qed
      also have "\<dots> = sub_var ?R2 (a # as) b c"
        using Pair by auto
      finally show ?thesis.
    qed
  qed
qed

lemma sub_pvars_eq: "sub_pvars (RringSet n ids S U) a b = sub_pvars (Rring n) a b"
proof (induction b arbitrary: a)
  case Nil
  then show ?case unfolding sub_pvars.simps by (rule refl)
next
  case (Cons x b)
  then show ?case
  proof (cases x)
    case (Pair x1 x2)
    then show ?thesis
    proof -
      let ?R1 = "RringSet n ids S U"
      let ?R2 = "Rring n"

      have "sub_pvars ?R1 a (x # b) = sub_pvars ?R1 a ((x1, x2) # b)"
        using Pair by auto
      also have "\<dots> = (if x2 = \<zero>\<^bsub>?R1\<^esub> then sub_pvars ?R1 a b
    else sub_pvars ?R1 (sub_var ?R1 a x1 x2) b)"
        by auto
      also have "\<dots> = (if x2 = \<zero>\<^bsub>?R2\<^esub> then sub_pvars ?R2 a b
    else sub_pvars ?R2 (sub_var ?R2 a x1 x2) b)"
      proof -
        have "sub_var ?R1 a x1 x2 = sub_var ?R2 a x1 x2"
          using sub_var_eq[of n ids S U a] by auto
        moreover
        have "sub_pvars ?R1 a b = sub_pvars ?R2 a b"
          using Cons.IH by auto
        moreover
        have "\<zero>\<^bsub>?R1\<^esub> = \<zero>\<^bsub>?R2\<^esub>"
          unfolding RringSet_def Rring_def
                    mat_interpretation_parameter.R_mat_semiring_def
                    mat_interpretation_parameter.Matsemiring_def
          by auto
        ultimately
        show ?thesis using Cons.IH by auto
      qed
      also have "\<dots> = sub_pvars ?R2 a (x # b)"
        using Pair by auto
      finally show ?thesis.
    qed
  qed
qed


lemma sub_lpoly_eq: "sub_lpoly (RringSet n ids S U) p q = sub_lpoly (Rring n) p q"
proof -
  obtain a b where p: "p = LPoly a b"
    using l_poly.exhaust by auto
  obtain c d where q: "q = LPoly c d"
    using l_poly.exhaust by auto

  let ?R1 = "RringSet n ids S U"
  let ?R2 = "Rring n"

  have "sub_lpoly ?R1 p q = LPoly (a \<ominus>\<ominus>\<^bsub>?R1\<^esub> c) (sub_pvars ?R1 b d)"
    using p q by auto
  also have "\<dots> = LPoly (a \<ominus>\<ominus>\<^bsub>?R1\<^esub> c) (sub_pvars ?R2 b d)"
    using sub_pvars_eq by auto
  also have "\<dots> = LPoly (a \<ominus>\<ominus>\<^bsub>?R2\<^esub> c) (sub_pvars ?R2 b d)"
    unfolding RringSet_def Rring_def mat_interpretation_parameter.R_mat_semiring_def
              mat_interpretation_parameter.Matsemiring_def
              expl_a_minus_def explicit_minus_semiring.simps
    by auto
  also have "\<dots> = sub_lpoly ?R2 p q"
    using p q by auto
  finally show ?thesis.
qed
  
lemma evp1 [simp]: "evalp_rule (RringEI n ids) p l r  =
 evalp_rule (Rring n) p l r"
proof -
  have "evalp (RringEI n ids) p l = evalp (Rring n) p l"
    using evalp_eq[of n ids _ _ p l] unfolding RringSet_def RringEI_def
    by meson
  moreover
  have "evalp (RringEI n ids) p r = evalp (Rring n) p r"
    using evalp_eq[of n ids _ _ p r] unfolding RringSet_def RringEI_def
    by meson
  ultimately
  have "sub_lpoly (RringEI n ids) (evalp (RringEI n ids) p l) (evalp (RringEI n ids) p r) =
sub_lpoly (RringEI n ids) (evalp (Rring n) p l) (evalp (Rring n) p r)"
    by auto
  also have "\<dots> = sub_lpoly (Rring n) (evalp (Rring n) p l) (evalp (Rring n) p r)"
    using sub_lpoly_eq unfolding RringSet_def RringEI_def
    by meson
  finally show ?thesis unfolding evalp_rule_def by auto
qed

lemma evp2[simp]: "evalp_rule (RringMI n ids) p l r =
evalp_rule (Rring n) p l r"
proof -
  have "evalp (RringMI n ids) p l = evalp (Rring n) p l"
    using evalp_eq[of n ids _ _ p l] unfolding RringSet_def RringMI_def
    by meson
  moreover
  have "evalp (RringMI n ids) p r = evalp (Rring n) p r"
    using evalp_eq[of n ids _ _ p r] unfolding RringSet_def RringMI_def
    by meson
  ultimately
  have "sub_lpoly (RringMI n ids) (evalp (RringMI n ids) p l) (evalp (RringMI n ids) p r) =
sub_lpoly (RringMI n ids) (evalp (Rring n) p l) (evalp (Rring n) p r)"
    by auto
  also have "\<dots> = sub_lpoly (Rring n) (evalp (Rring n) p l) (evalp (Rring n) p r)"
    using sub_lpoly_eq unfolding RringSet_def RringMI_def
    by meson
  finally show ?thesis unfolding evalp_rule_def by auto
qed



subsection \<open>Checks on TRS rules\<close>
\<comment> \<open>After working on variable interpretations and function symbol interpretations,
    now working on TRS rules being in the monotonic carrier (see carrierMono in Linear_Poly_Interpretation).\<close>
\<comment> \<open>Checks on:
    All interpretations of rule of a TRS being in the positive cone (>= 0),
    All interpretations of rule of a TRS we want to prove terminating being in the monotonic carrier.\<close>
\<comment> \<open>To be in the monotonic carrier, it suffices that all coefficients of the polynomial interpretation
    be in the positive cone and that at least 1 coefficient be in the monotonic carrier.\<close>


definition check_lpoly_coef_N where
"check_lpoly_coef_N n lp =
    check_allm (check_N n ) (coeffs_of_lpoly_better lp) <+? (\<lambda>str.
      showsl_lit (STR ''Expected all lpoly coefficient to be greater or equal to 0 mat.\<newline>'') o str)"
lemma check_lpoly_coef_N[simp]: assumes "isOK (check_lpoly_coef_N n lp)"
  shows "set (coeffs_of_lpoly_better lp) \<subseteq> squared_int_mat.N n"
  using assms[unfolded check_lpoly_coef_N_def, simplified] by auto


definition check_poly_coef_one_P\<^sub>I where
"check_poly_coef_one_P\<^sub>I n ids lp =
    check (\<exists>c \<in> set (coeffs_of_lpoly_better lp). isOK (check_P\<^sub>I n ids c))
      (showsl_lit (STR ''Expected at least 1 lpoly coefficient to be in P_I, got none.'')
      o showsl (list_of_mat_to_list_of_list (coeffs_of_lpoly_better lp)))"
lemma check_poly_coef_one_P\<^sub>I[simp]: assumes "isOK (check_poly_coef_one_P\<^sub>I n ids lp)"
  shows "set (coeffs_of_lpoly_better lp) \<inter> squared_int_mat.P\<^sub>I n (set ids) \<noteq> {}"
  using assms[unfolded check_poly_coef_one_P\<^sub>I_def, simplified] by auto


definition check_poly_coef_one_M\<^sub>I where
"check_poly_coef_one_M\<^sub>I n ids lp =
    check (\<exists>c \<in> set (coeffs_of_lpoly_better lp). isOK (check_M\<^sub>I n ids c))
      (showsl_lit (STR ''Expected at least 1 lpoly coefficient to be in M_I, got none.'')
      o showsl (list_of_mat_to_list_of_list (coeffs_of_lpoly_better lp)))"
lemma check_poly_coef_one_M\<^sub>I[simp]: assumes "isOK (check_poly_coef_one_M\<^sub>I n ids lp)"
  shows "set (coeffs_of_lpoly_better lp) \<inter> squared_int_mat.M\<^sub>I n (set ids) \<noteq> {}"
  using assms[unfolded check_poly_coef_one_M\<^sub>I_def, simplified] by auto






definition check_rules_N_E\<^sub>I :: "nat \<Rightarrow> nat list \<Rightarrow> 'f ::showl fun_coeffs \<Rightarrow> ('f, 'v :: showl) rules \<Rightarrow> showsl check" where
"check_rules_N_E\<^sub>I n ids fc R =
    check_allm (\<lambda>(l,r). (check_lpoly_coef_N n (
              evalp_rule (Rring n) (pI' n fc) l r
            )
      ) <+? (\<lambda>str. showsl_lit(STR ''Expected rule interpretation of lhs '') o showsl l o showsl_lit(STR '' and of rhs '')
 o showsl r o showsl_lit (STR '' to be in N.\<newline>'') o str)
    ) R <+? (\<lambda>str.
    (showsl_lit (STR ''Expected all interpretation of rules (i.e. I l - I r for all rule l -> r)
 to be greater or equal to 0 mat.\<newline>'')) o str)"
lemma check_rules_N_E\<^sub>I[simp]: assumes "isOK (check_rules_N_E\<^sub>I n ids fc R)"
  shows "(l,r) \<in> set R \<Longrightarrow> set (coeffs_of_lpoly_better (
  evalp_rule (Rring n) (pI' n fc) l r 
)) \<subseteq> squared_int_mat.N n"
  using assms[unfolded check_rules_N_E\<^sub>I_def, simplified] check_lpoly_coef_N[of n]
  by blast

definition check_rules_N_M\<^sub>I :: "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> ('f, 'v :: showl) rules \<Rightarrow> showsl check" where
"check_rules_N_M\<^sub>I n ids fc R =
    check_allm (\<lambda>(l,r). (check_lpoly_coef_N n (
              evalp_rule (Rring n) (pI' n fc) l r
            )
      ) <+? (\<lambda>str. showsl_lit(STR ''Expected rule interpretation of lhs '') o showsl l o showsl_lit(STR '' and of rhs '')
 o showsl r o showsl_lit (STR '' to be in N. Thus, expected all poly coeffs to be in N:\<newline>'')
 o showsl (evalp_rule (Rring n) (pI' n fc) l r) o str)
    ) R <+? (\<lambda>str.
    (showsl_lit (STR ''Expected all interpretation of rules (i.e. ids l - ids r for all rule l -> r)
 to be greater or equal to 0 mat.\<newline>'')) o str)"
lemma check_rules_N_M\<^sub>I[simp]: assumes "isOK (check_rules_N_M\<^sub>I n ids fc R)"
  shows "(l,r) \<in> set R \<Longrightarrow> set (coeffs_of_lpoly_better (
  evalp_rule (Rring n) (pI' n fc) l r 
)) \<subseteq> squared_int_mat.N n"
  using assms[unfolded check_rules_N_M\<^sub>I_def, simplified] check_lpoly_coef_N[of n]
  by blast



definition check_rules_one_P\<^sub>I ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> ('f, 'v :: showl) rules \<Rightarrow> showsl check" where
"check_rules_one_P\<^sub>I n ids fc R =
    check_allm (\<lambda>(l,r). (check_poly_coef_one_P\<^sub>I n ids (
              evalp_rule (Rring n) (pI' n fc) l r
            )
      ) <+? (\<lambda>str. showsl_lit(STR ''Expected rule interpretation of lhs '') o showsl l o showsl_lit(STR '' and of rhs '')
 o showsl r o showsl_lit (STR '' to be in P_I. Thus, expected at least 1 poly coeffs to be in P_I:\<newline>'')
 o showsl (evalp_rule (Rring n) (pI' n fc) l r) o str)
    ) R <+? (\<lambda>str.
    (showsl_lit (STR ''Expected all interpretation of rules (i.e. ids l - ids r for all rule l -> r)
 to have at least one lpoly coef in P_I.\<newline>'')) o str)"
lemma check_rules_one_P\<^sub>I[simp]: assumes "isOK (check_rules_one_P\<^sub>I n ids fc R)"
  shows "(l,r) \<in> set R \<Longrightarrow> set (coeffs_of_lpoly_better (

  evalp_rule (Rring n) (pI' n fc) l r 

)) \<inter> squared_int_mat.P\<^sub>I n (set ids) \<noteq> {}"
  using assms[unfolded check_rules_one_P\<^sub>I_def] by auto

definition check_rules_one_M\<^sub>I ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> ('f, 'v :: showl) rules \<Rightarrow> showsl check"
 where
"check_rules_one_M\<^sub>I n ids fc R =
    check_allm (\<lambda>(l,r). (check_poly_coef_one_M\<^sub>I n ids (
              evalp_rule (Rring n) (pI' n fc) l r
            )
      ) <+? (\<lambda>str. showsl_lit(STR ''Expected rule interpretation of lhs '') o showsl l o showsl_lit(STR '' and of rhs '')
 o showsl r o showsl_lit (STR '' to be in M_I. Thus, expected at least 1 poly coeffs to be in M_I:\<newline>'')
 o showsl (evalp_rule (Rring n) (pI' n fc) l r) o str)
    ) R <+? (\<lambda>str.
    (showsl_lit (STR ''Expected all interpretation of rules (i.e. ids l - ids r for all rule l -> r)
 to have at least one lpoly coef in M_I.\<newline>'')) o str)"
lemma check_rules_one_M\<^sub>I[simp]: assumes "isOK (check_rules_one_M\<^sub>I n ids fc R)"
  shows "(l,r) \<in> set R \<Longrightarrow> set (coeffs_of_lpoly_better (

  evalp_rule (Rring n) (pI' n fc) l r 

)) \<inter> squared_int_mat.M\<^sub>I n (set ids) \<noteq> {}"
  using assms[unfolded check_rules_one_M\<^sub>I_def, simplified] by auto







subsection \<open>(relative) termination checks for domain = E_I\<close>
\<comment> \<open>Checks that the rule of a TRS are in the monotonic carrier
   (that is the core of the strict carrier, see Matrix_Base).
    It mechanically implies termination.\<close>
\<comment> \<open>For termination relative to a TRS S, it suffices that the interpretations of the rule of S
    be in the positive cone, in addition to the above requirements.\<close>


definition check_core_E\<^sub>I :: "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> ('f, 'v :: showl) rules \<Rightarrow> showsl check" where
"check_core_E\<^sub>I n ids fc R = (do {
    check (n > 0) (showsl_lit (STR ''Expected matrices of size > 0''));
    check_coeffs_E\<^sub>I_final n ids fc;
    check_rules_N_E\<^sub>I n ids fc R;
    check_rules_one_P\<^sub>I n ids fc R
})"

lemma check_core_E\<^sub>I_n0[simp]: assumes "isOK (check_core_E\<^sub>I n ids fc R)"
  shows "n > 0"
  using assms[unfolded check_core_E\<^sub>I_def] by auto

lemma check_core_E\<^sub>I_triv[simp]: assumes "isOK (check_core_E\<^sub>I n ids fc R)"
  shows "isOK (check_coeffs_E\<^sub>I_final n ids fc)"
        "isOK (check_rules_N_E\<^sub>I n ids fc R)"
        "isOK (check_rules_one_P\<^sub>I n ids fc R)"
  using assms[unfolded check_core_E\<^sub>I_def] by auto


lemma check_core_E\<^sub>I:
  assumes "isOK (check_core_E\<^sub>I n ids fc R)"
  shows "range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<Longrightarrow>
 (squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha>) ` (set R) \<subseteq>
 squared_int_mat.core n (squared_int_mat.E\<^sub>I n (set ids))"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_E\<^sub>I_final_triv(2)[OF check_core_E\<^sub>I_triv(1)[OF assms]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto


  
  note th = squared_int_mat.one_coeff_in_mono_imp_forall_assig_trs[OF _ t2 E\<^sub>I_wf_carrierS[OF t1]]
  show "range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<Longrightarrow>
 (squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha>) ` (set R) \<subseteq>
 squared_int_mat.core n (squared_int_mat.E\<^sub>I n (set ids))"
    using th check_coeffs_E\<^sub>I_final[OF check_core_E\<^sub>I_triv(1)[OF assms]]
          check_rules_N_E\<^sub>I[OF check_core_E\<^sub>I_triv(2)[OF assms]]
          check_rules_one_P\<^sub>I[OF check_core_E\<^sub>I_triv(3)[OF assms]]
          evp1 
  by (smt (verit, ccfv_threshold) RringEI_def \<open>set ids \<noteq> {} \<and> set ids \<subseteq> {0..<n}\<close> disjoint_mono
      squared_int_mat.core_E\<^sub>I_in_P\<^sub>I subset_code(1))
qed


lemma check_core_E\<^sub>I_terminate:
  assumes "isOK (check_core_E\<^sub>I n ids fc R)"
  shows "SN (rstep (set R))"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_E\<^sub>I_final_triv(2)[OF check_core_E\<^sub>I_triv(1)[OF assms]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto

  note th = squared_int_mat.one_coeff_in_mono_imp_forall_assig_trs[OF _ t2 E\<^sub>I_wf_carrierS[OF t1]]

  have "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<longrightarrow>
         squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha> ` (set R)
         \<subseteq> squared_int_mat.core n (squared_int_mat.E\<^sub>I n (set ids)) \<Longrightarrow>
    SN (rstep (set R))"
    using th check_core_E\<^sub>I_triv[OF assms] check_coeffs_E\<^sub>I_final check_rules_N_E\<^sub>I check_rules_one_P\<^sub>I
    unfolding RringEI_def
    by (smt (verit) t1 domain_E\<^sub>I_term t2)

  then show ?thesis
    using check_core_E\<^sub>I[OF assms]
    by auto
qed





definition check_N_for_relative_E\<^sub>I ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> ('f, 'v :: showl) rules \<Rightarrow> showsl check"
 where
"check_N_for_relative_E\<^sub>I n ids fc R = (do {
    check (n > 0) (showsl_lit (STR ''Expected matrices of size > 0''));
    check_coeffs_E\<^sub>I_final n ids fc;
    check_rules_N_E\<^sub>I n ids fc R
})"

lemma check_N_for_relative_E\<^sub>I_n0[simp]: assumes "isOK (check_N_for_relative_E\<^sub>I n ids fc R)"
  shows "n > 0"
  using assms[unfolded check_N_for_relative_E\<^sub>I_def] by auto

lemma check_N_for_relative_E\<^sub>I_triv[simp]: assumes "isOK (check_N_for_relative_E\<^sub>I n ids fc R)"
  shows "isOK (check_coeffs_E\<^sub>I_final n ids fc)"
        "isOK (check_rules_N_E\<^sub>I n ids fc R)"
  using assms[unfolded check_N_for_relative_E\<^sub>I_def] by auto


lemma check_N_for_relative_E\<^sub>I:
  assumes "isOK (check_N_for_relative_E\<^sub>I n ids fc S)"
  shows "range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<Longrightarrow>
 (squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha>) ` (set S) \<subseteq>
 squared_int_mat.N n"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_E\<^sub>I_final_triv(2)[OF check_N_for_relative_E\<^sub>I_triv(1)[OF assms]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto


  note th = squared_int_mat.all_coeff_in_N_imp_forall_assig_trs[OF _ t2 E\<^sub>I_wf_carrierS[OF t1]]
  moreover
  have "(\<And>l r. (l, r) \<in> set S \<Longrightarrow> set (coeffs_of_lpoly_better
   (evalp_rule (RringEI n ids) (pI' n fc) l r))
          \<subseteq> squared_int_mat.N n)"
    using check_rules_N_E\<^sub>I[OF check_N_for_relative_E\<^sub>I_triv(2)[OF assms]]
    by auto
  ultimately
  show "range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<Longrightarrow>
 (squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha>) ` (set S) \<subseteq>
 squared_int_mat.N n"
    using check_coeffs_E\<^sub>I_final[OF check_N_for_relative_E\<^sub>I_triv(1)[OF assms]]
    unfolding RringEI_def
    by (smt (verit, del_insts) t2)
qed



lemma check_E\<^sub>I_terminates_relative:
  assumes "isOK (check_core_E\<^sub>I n ids fc R)" "isOK (check_N_for_relative_E\<^sub>I n ids fc S)"
  shows "SN (rstep ((set S)\<^sup>* O (set R) O (set S)\<^sup>*))"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_E\<^sub>I_final_triv(2)[OF check_core_E\<^sub>I_triv(1)[OF assms(1)]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto

  note th = squared_int_mat.A_interpretation_terminates_relative[OF _ t2 E\<^sub>I_wf_carrierS[OF t1]]
  have "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha> ` (set R)
       \<subseteq> squared_int_mat.core n (squared_int_mat.E\<^sub>I n (set ids)) \<Longrightarrow>
  \<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha> ` (set S) \<subseteq> squared_int_mat.N n \<Longrightarrow>
  SN (rstep ((set S)\<^sup>* O (set R) O (set S)\<^sup>*))"
    using th check_core_E\<^sub>I_triv[OF assms(1)] check_coeffs_E\<^sub>I_final check_rules_N_E\<^sub>I 
    by (smt (verit, del_insts))
  then show ?thesis
    using check_core_E\<^sub>I[OF assms(1)] check_N_for_relative_E\<^sub>I[OF assms(2)]
    by auto
qed




subsection \<open>(relative) termination checks for domain = M_I\<close>
\<comment> \<open>Same comments than for domain = E_I\<close>


definition check_core_M\<^sub>I :: "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> ('f, 'v :: showl) rules \<Rightarrow> showsl check" where
"check_core_M\<^sub>I n ids fc R = (do {
    check (n > 0) (showsl_lit (STR ''Expected matrices of size > 0''));
    check_coeffs_M\<^sub>I_final n ids fc;
    check_rules_N_M\<^sub>I n ids fc R;
    check_rules_one_M\<^sub>I n ids fc R
})"

lemma check_core_M\<^sub>I_n0[simp]: assumes "isOK (check_core_M\<^sub>I n ids fc R)"
  shows "n > 0"
  using assms[unfolded check_core_M\<^sub>I_def] by auto

lemma check_core_M\<^sub>I_triv[simp]: assumes "isOK (check_core_M\<^sub>I n ids fc R)"
  shows "isOK (check_coeffs_M\<^sub>I_final n ids fc)"
        "isOK (check_rules_N_M\<^sub>I n ids fc R)"
        "isOK (check_rules_one_M\<^sub>I n ids fc R)"
  using assms[unfolded check_core_M\<^sub>I_def] by auto

lemma check_core_M\<^sub>I:
  assumes "isOK (check_core_M\<^sub>I n ids fc R)"
  shows "range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<Longrightarrow>
 (squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n (set ids)) (pI' n fc) \<alpha>) ` (set R) \<subseteq>
 squared_int_mat.core n (squared_int_mat.M\<^sub>I n (set ids))"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_M\<^sub>I_final_triv(2)[OF check_core_M\<^sub>I_triv(1)[OF assms]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto



  note th = squared_int_mat.one_coeff_in_mono_imp_forall_assig_trs[OF _ t2 M\<^sub>I_wf_carrierS[OF t1]]
  show "range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<Longrightarrow>
 (squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n (set ids)) (pI' n fc) \<alpha>) ` (set R) \<subseteq>
 squared_int_mat.core n (squared_int_mat.M\<^sub>I n (set ids))"
    using th
             check_coeffs_M\<^sub>I_final[OF check_core_M\<^sub>I_triv(1)[OF assms]]
             check_rules_N_M\<^sub>I[OF check_core_M\<^sub>I_triv(2)[OF assms]]
             check_rules_one_M\<^sub>I[OF check_core_M\<^sub>I_triv(3)[OF assms]]
             evp2
  by (smt (verit, best) Int_absorb2 Int_ac(4) Int_empty_right RringMI_def \<open>set ids \<noteq> {} \<and> set ids \<subseteq> {0..<n}\<close>
      squared_int_mat.core_M\<^sub>I_in_M\<^sub>I)
qed



lemma check_core_M\<^sub>I_terminate:
  assumes "isOK (check_core_M\<^sub>I n ids fc R)"
  shows "SN (rstep (set R))"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_M\<^sub>I_final_triv(2)[OF check_core_M\<^sub>I_triv(1)[OF assms]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto

  note th = squared_int_mat.one_coeff_in_mono_imp_forall_assig_trs[OF _ t2 M\<^sub>I_wf_carrierS[OF t1]]

  have "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<longrightarrow>
         squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n (set ids)) (pI' n fc) \<alpha> ` (set R)
         \<subseteq> squared_int_mat.core n (squared_int_mat.M\<^sub>I n (set ids)) \<Longrightarrow>
    SN (rstep (set R))"
    using th check_core_M\<^sub>I_triv[OF assms] check_coeffs_M\<^sub>I_final check_rules_N_M\<^sub>I check_rules_one_M\<^sub>I
    unfolding RringMI_def

    by (smt (verit, del_insts) domain_M\<^sub>I_term order_refl t1(1,2) t2)

  then show ?thesis
    using check_core_M\<^sub>I[OF assms]
    by auto
qed





definition check_N_for_relative_M\<^sub>I ::
 "nat \<Rightarrow> nat list \<Rightarrow> 'f :: showl fun_coeffs \<Rightarrow> ('f, 'v :: showl) rules \<Rightarrow> showsl check"
 where
"check_N_for_relative_M\<^sub>I n ids fc R = (do {
    check (n > 0) (showsl_lit (STR ''Expected matrices of size > 0''));
    check_coeffs_M\<^sub>I_final n ids fc;
    check_rules_N_M\<^sub>I n ids fc R
})"
lemma check_N_for_relative_M\<^sub>I_n0[simp]: assumes "isOK (check_N_for_relative_M\<^sub>I n ids fc R)"
  shows "n > 0"
  using assms[unfolded check_N_for_relative_M\<^sub>I_def] by auto
lemma check_N_for_relative_M\<^sub>I_triv[simp]: assumes "isOK (check_N_for_relative_M\<^sub>I n ids fc R)"
  shows "isOK (check_coeffs_M\<^sub>I_final n ids fc)"
        "isOK (check_rules_N_M\<^sub>I n ids fc R)"
  using assms[unfolded check_N_for_relative_M\<^sub>I_def] by auto


lemma check_N_for_relative_M\<^sub>I:
  assumes "isOK (check_N_for_relative_M\<^sub>I n ids fc S)"
  shows "range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<Longrightarrow>
 (squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n (set ids)) (pI' n fc) \<alpha>) ` (set S) \<subseteq>
 squared_int_mat.N n"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_M\<^sub>I_final_triv(2)[OF check_N_for_relative_M\<^sub>I_triv(1)[OF assms]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto


  note th = squared_int_mat.all_coeff_in_N_imp_forall_assig_trs[OF _ t2 M\<^sub>I_wf_carrierS[OF t1]]
  moreover
  have "(\<And>l r. (l, r) \<in> set S \<Longrightarrow> set (coeffs_of_lpoly_better
   (evalp_rule (RringMI n ids) (pI' n fc) l r))
          \<subseteq> squared_int_mat.N n)"
    using check_rules_N_M\<^sub>I[OF check_N_for_relative_M\<^sub>I_triv(2)[OF assms]]
    by auto
  ultimately
  show "range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<Longrightarrow>
 (squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n (set ids)) (pI' n fc) \<alpha>) ` (set S) \<subseteq>
 squared_int_mat.N n"
    using check_coeffs_M\<^sub>I_final[OF check_N_for_relative_M\<^sub>I_triv(1)[OF assms]]
    unfolding RringMI_def
    by (smt (verit, ccfv_SIG)t2)
qed



lemma check_M\<^sub>I_to_redtriple_order:
  assumes "isOK (check_core_M\<^sub>I n ids fc R)" "isOK (check_N_for_relative_M\<^sub>I n ids fc S)"
  shows "\<exists> s ns. mono_redtriple_order s ns ns \<and> set R \<subseteq> s \<and> set S \<subseteq> ns \<and> ce_compatible s"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_M\<^sub>I_final_triv(2)[OF check_core_M\<^sub>I_triv(1)[OF assms(1)]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto

  have def: "(\<And>c m. (c, m) \<notin> set (map fst fc) \<Longrightarrow> pI' n fc (c, m) = default_mat_inter n m)" 
    unfolding pI'_def split 
    by (auto split: option.splits dest: map_of_SomeD) 

  note th = squared_int_mat.A_interpretation_to_redtriple_orientation[OF _ t2 M\<^sub>I_wf_carrierS[OF t1],
      of "pI' n fc" _ _ "map fst fc", OF _ _ _ _ def]
  have "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n (set ids)) (pI' n fc) \<alpha> ` (set R)
       \<subseteq> squared_int_mat.core n (squared_int_mat.M\<^sub>I n (set ids)) \<Longrightarrow>
  \<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n (set ids) \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n (set ids)) (pI' n fc) \<alpha> ` (set S) \<subseteq> squared_int_mat.N n \<Longrightarrow>
  ?thesis"
    using th check_core_M\<^sub>I_triv[OF assms(1)] check_coeffs_M\<^sub>I_final check_rules_N_M\<^sub>I
    by (smt (verit, del_insts))
  then show ?thesis
    using check_core_M\<^sub>I[OF assms(1)] check_N_for_relative_M\<^sub>I[OF assms(2)]
    by auto
qed



lemma check_E\<^sub>I_to_redtriple_order:
  assumes "isOK (check_core_E\<^sub>I n ids fc R)" "isOK (check_N_for_relative_E\<^sub>I n ids fc S)"
  shows "\<exists> s ns. mono_redtriple_order s ns ns \<and> set R \<subseteq> s \<and> set S \<subseteq> ns \<and> ce_compatible s"
proof -
  from check_indices[OF check_coefficients_N_indices[OF 
      check_coeffs_E\<^sub>I_final_triv(2)[OF check_core_E\<^sub>I_triv(1)[OF assms(1)]]]]
  have t1: "set ids \<subseteq> {0..< n}" "set ids \<noteq> {}"
    by auto
  then have t2: "n > 0" by auto

  have def: "(\<And>c m. (c, m) \<notin> set (map fst fc) \<Longrightarrow> pI' n fc (c, m) = default_mat_inter n m)" 
    unfolding pI'_def split 
    by (auto split: option.splits dest: map_of_SomeD) 

  note th = squared_int_mat.A_interpretation_to_redtriple_orientation[OF _ t2 E\<^sub>I_wf_carrierS[OF t1],
      of "pI' n fc" _ _ "map fst fc", OF _ _ _ _ def]

  have "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha> ` (set R)
       \<subseteq> squared_int_mat.core n (squared_int_mat.E\<^sub>I n (set ids)) \<Longrightarrow>
  \<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n (set ids) \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n (set ids)) (pI' n fc) \<alpha> ` (set S) \<subseteq> squared_int_mat.N n \<Longrightarrow>
  ?thesis"
    using th check_core_E\<^sub>I_triv[OF assms(1)] check_coeffs_E\<^sub>I_final check_rules_N_E\<^sub>I
    by (smt (verit, del_insts))
  then show ?thesis
    using check_core_E\<^sub>I[OF assms(1)] check_N_for_relative_E\<^sub>I[OF assms(2)]
    by auto
qed


subsection \<open>Connection to Relation_Implementation\<close>

datatype core_matrix_mode = E_I | M_I

datatype 'f core_matrix_inter = Core_Matrix_Inter core_matrix_mode nat "nat list" "'f fun_coeffs"

lemmas mat_interpretation_code = 
  mat_interpretation_parameter.Matsemiring_def

declare mat_interpretation_code[code]

definition "check_M_I_weak n ids fc = (\<lambda> (l,r). let diff = evalp_rule (Rring n) (pI' n fc) l r
              in check_lpoly_coef_N n diff 
            <+? (\<lambda> e. showsl_lit (STR ''problem in M_I-weak decrease of '') o showsl_rule (l,r) o showsl_nl o 
                 showsl_lit (STR ''with interpretation [left] - [right] = '') o showsl diff o showsl_nl o e))"
definition "check_M_I_strict n ids fc = (\<lambda> (l,r). let diff = evalp_rule (Rring n) (pI' n fc) l r in 
             do {check_poly_coef_one_M\<^sub>I n ids diff; check_lpoly_coef_N n diff}
            <+? (\<lambda> e. showsl_lit (STR ''problem in M_I-strict decrease of '') o showsl_rule (l,r) o showsl_nl o 
                 showsl_lit (STR ''with interpretation [left] - [right] = '') o showsl diff o showsl_nl o e))"

definition "check_E_I_weak n ids fc = (\<lambda> (l,r). let diff = evalp_rule (Rring n) (pI' n fc) l r in
              check_lpoly_coef_N n diff 
            <+? (\<lambda> e. showsl_lit (STR ''problem in E_I-weak decrease of '') o showsl_rule (l,r) o showsl_nl o
                 showsl_lit (STR ''with interpretation [left] - [right] = '') o showsl diff o showsl_nl o e))"
definition "check_E_I_strict n ids fc = (\<lambda> (l,r). let diff = evalp_rule (Rring n) (pI' n fc) l r in 
             do {check_poly_coef_one_P\<^sub>I n ids diff; check_lpoly_coef_N n diff}
            <+? (\<lambda> e. showsl_lit (STR ''problem in E_I-strict decrease of '') o showsl_rule (l,r) o showsl_nl o
                 showsl_lit (STR ''with interpretation [left] - [right] = '') o showsl diff o showsl_nl o e))"

 

definition show_core_matrix_inter :: "'f :: showl core_matrix_inter \<Rightarrow> showsl" where
  "show_core_matrix_inter cmi = (case cmi of Core_Matrix_Inter mode d idx intr \<Rightarrow> 
     showsl_lit (STR ''core matrix interpretation (mode = '')
   o showsl_lit (case mode of E_I \<Rightarrow> STR ''E_I'' | M_I \<Rightarrow> STR ''M_I'')
   o showsl_lit (STR '') with dimension '') o showsl d o showsl_lit (STR '' and strict indices I = '')
   o showsl (map Suc idx) o showsl_lit (STR '' where\<newline>'')
   o showsl_sep (\<lambda> ((f,n),(cs,c)). 
          showsl_lit (STR ''['')
        o showsl (Fun f (map (\<lambda> i. Var (''x'' @ show i)) [1..<Suc n])) 
        o showsl_lit (STR ''] = '')
        o showsl (LPoly c (zip (map (\<lambda> i. ''x'' @ show i) [1..<Suc n]) cs))
     ) (showsl_lit (STR ''\<newline>'')) intr
   o showsl_lit (STR ''\<newline>and\<newline>[f(x1,..,xn)] = x1 + ... + xn + 1 for all other symbols f\<newline>\<newline>''))"  

fun create_core_matrix_rel_impl :: "('f :: {showl,compare_order})core_matrix_inter \<Rightarrow> ('f,'v :: showl)rel_impl"
  where "create_core_matrix_rel_impl (Core_Matrix_Inter mode n ids fc) = (
     let ns = (case mode of E_I \<Rightarrow> check_E_I_weak n ids fc | 
              M_I \<Rightarrow> check_M_I_weak n ids fc);
         s = (case mode of E_I \<Rightarrow> check_E_I_strict n ids fc | 
              M_I \<Rightarrow> check_M_I_strict n ids fc)
          in
    \<lparr>rel_impl.valid = do {check (n > 0) (showsl (STR ''dimension must be > 0''));
       (case mode of 
             E_I \<Rightarrow> check_coeffs_E\<^sub>I_final n ids fc | 
             M_I \<Rightarrow> check_coeffs_M\<^sub>I_final n ids fc)},
     standard = succeed,
     desc = show_core_matrix_inter (Core_Matrix_Inter mode n ids fc),
     s = s,
     ns = ns, 
     nst = ns,
     af = full_af,
     top_af = full_af,
     SN = succeed,
     subst_s = succeed,
     ce_compat = succeed,
     co_rewr = succeed,
     top_mono = succeed,
     top_refl = succeed,
     mono_af = (\<lambda> f. UNIV),
     mono = (\<lambda> _. succeed),
     not_wst = None, 
     not_sst = None, 
     cpx = no_complexity_check \<rparr>)"

lemma create_core_matrix_rel_impl: "rel_impl (create_core_matrix_rel_impl mI)"
proof -
  obtain mode n ids fc where mI: "mI = Core_Matrix_Inter mode n ids fc" by (cases mI, auto)
  show ?thesis 
  proof (cases mode)
    case E_I  
    show ?thesis
    unfolding rel_impl_def create_core_matrix_rel_impl.simps mI Let_def rel_impl.simps E_I core_matrix_mode.simps split
    proof (intro allI impI, goal_cases)
      case (1 U)
      from 1 have n: "n > 0" and pI_EI: "isOK(check_coeffs_E\<^sub>I_final n ids fc)" by auto
      let ?S = "check_E_I_strict n ids fc" 
      let ?W = "check_E_I_weak n ids fc" 
      define R where "R = (filter (\<lambda> lr. isOK(?S lr)) U)"
      define S where "S = (filter (\<lambda> lr. isOK(?W lr)) U)"
      have main: "\<exists>s ns. mono_redtriple_order s ns ns \<and> set R \<subseteq> s \<and> set S \<subseteq> ns \<and> ce_compatible s" 
      proof (rule check_E\<^sub>I_to_redtriple_order)
        have "isOK (check_rules_N_E\<^sub>I n ids fc R)" 
          unfolding check_rules_N_E\<^sub>I_def R_def
          by (auto simp: check_E_I_strict_def check_E_I_weak_def)
        moreover have "isOK (check_rules_one_P\<^sub>I n ids fc R)" 
          unfolding check_rules_one_P\<^sub>I_def R_def 
          by (auto simp: check_E_I_strict_def)
        ultimately show "isOK (check_core_E\<^sub>I n ids fc R)" using pI_EI n
          unfolding check_core_E\<^sub>I_def by auto
        show "isOK (check_N_for_relative_E\<^sub>I n ids fc S)" unfolding check_N_for_relative_E\<^sub>I_def
          using pI_EI n by (auto simp: check_rules_N_E\<^sub>I_def S_def check_E_I_weak_def)
      qed
      then obtain s ns where mro: "mono_redtriple_order s ns ns" and sub: "set R \<subseteq> s" "set S \<subseteq> ns" 
        and ce: "ce_compatible s" 
        by auto
      interpret mono_redtriple_order s ns ns by fact
      from S_imp_NS ce have ce2: "ce_compatible ns" unfolding ce_compatible_def by blast
      show ?case
      proof (rule exI[of _ s], rule exI[of _ ns], rule exI[of _ ns], intro conjI impI allI
          refl_NST ctxt_S ctxt_NS subst_NS subst_S full_af not_subterm_rel_info.simps ce ce2
          compat_S_NS compat_NS_S trans_S trans_NS S_imp_NS SN ctxt_closed_imp_af_monotone top_mono_same)
        find_theorems s ns
        show "irrefl s" using SN by (meson SN_on_irrefl irrefl_on_def)
        show "ns \<inter> s\<inverse> = {}" by (simp add: \<open>irrefl s\<close> co_rewrite_irrefl compat_NS_S)
        show "lr \<in> set U \<Longrightarrow> isOK (check_E_I_strict n ids fc lr) \<Longrightarrow> lr \<in> s" for lr
          using sub(1) unfolding R_def by auto
        show "lr \<in> set U \<Longrightarrow> isOK (check_E_I_weak n ids fc lr) \<Longrightarrow> lr \<in> ns" for lr
          using sub(2) unfolding S_def by auto
        show "lr \<in> set U \<Longrightarrow> isOK (check_E_I_weak n ids fc lr) \<Longrightarrow> lr \<in> ns" for lr by fact
      qed (auto simp: isOK_no_complexity)
    qed
  next
    case M_I
    show ?thesis 
      unfolding rel_impl_def create_core_matrix_rel_impl.simps mI Let_def rel_impl.simps M_I core_matrix_mode.simps split
    proof (intro allI impI, goal_cases)
      case (1 U)
      from 1 have n: "n > 0" and pI_MI: "isOK(check_coeffs_M\<^sub>I_final n ids fc)" by auto
      let ?S = "check_M_I_strict n ids fc" 
      let ?W = "check_M_I_weak n ids fc" 
      define R where "R = (filter (\<lambda> lr. isOK(?S lr)) U)"
      define S where "S = (filter (\<lambda> lr. isOK(?W lr)) U)"
      have main: "\<exists>s ns. mono_redtriple_order s ns ns \<and> set R \<subseteq> s \<and> set S \<subseteq> ns \<and> ce_compatible s" 
      proof (rule check_M\<^sub>I_to_redtriple_order)
        have "isOK (check_rules_N_M\<^sub>I n ids fc R)" 
          unfolding check_rules_N_M\<^sub>I_def R_def
          by (auto simp: check_M_I_strict_def check_M_I_weak_def)
        moreover have "isOK (check_rules_one_M\<^sub>I n ids fc R)" 
          unfolding check_rules_one_M\<^sub>I_def R_def 
          by (auto simp: check_M_I_strict_def)
        ultimately show "isOK (check_core_M\<^sub>I n ids fc R)" using pI_MI n
          unfolding check_core_M\<^sub>I_def by auto
        show "isOK (check_N_for_relative_M\<^sub>I n ids fc S)" unfolding check_N_for_relative_M\<^sub>I_def
          using pI_MI n by (auto simp: check_rules_N_M\<^sub>I_def S_def check_M_I_weak_def)
      qed
      then obtain s ns where mro: "mono_redtriple_order s ns ns" and sub: "set R \<subseteq> s" "set S \<subseteq> ns"
        and ce: "ce_compatible s" 
        by auto
      interpret mono_redtriple_order s ns ns by fact
      from S_imp_NS ce have ce2: "ce_compatible ns" unfolding ce_compatible_def by blast
      show ?case
      proof (rule exI[of _ s], rule exI[of _ ns], rule exI[of _ ns], intro conjI impI allI
          refl_NST ctxt_S ctxt_NS subst_NS subst_S full_af not_subterm_rel_info.simps ce ce2
          compat_S_NS compat_NS_S trans_S trans_NS S_imp_NS SN ctxt_closed_imp_af_monotone top_mono_same)
        show "irrefl s" using SN by (meson SN_on_irrefl irrefl_on_def)
        show "ns \<inter> s\<inverse> = {}" by (simp add: \<open>irrefl s\<close> co_rewrite_irrefl compat_NS_S)
        show "lr \<in> set U \<Longrightarrow> isOK (check_M_I_strict n ids fc lr) \<Longrightarrow> lr \<in> s" for lr
          using sub(1) unfolding R_def by auto
        show "lr \<in> set U \<Longrightarrow> isOK (check_M_I_weak n ids fc lr) \<Longrightarrow> lr \<in> ns" for lr
          using sub(2) unfolding S_def by auto
        show "lr \<in> set U \<Longrightarrow> isOK (check_M_I_weak n ids fc lr) \<Longrightarrow> lr \<in> ns" for lr by fact
      qed (auto simp: isOK_no_complexity)
    qed
  qed
qed

hide_const Ip I

end