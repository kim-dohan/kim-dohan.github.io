theory Matrix_TRS
  imports
    Matrix_Base
    "First_Order_Rewriting.Trs"
    "Ord.Linear_Poly_Interpretation"
    "Ord.Matrix_Poly"
begin

hide_const (open) Poly_Order.eval_term
hide_const (open) Finite_Cartesian_Product.mat
no_notation Mpat_Antiquot.mpaq_App (infixl \<open>$$\<close> 900)
hide_const (open) Mpat_Antiquot.mpaq_App


abbreviation "I \<equiv> LPI"

definition default_mat_inter :: "nat \<Rightarrow> nat \<Rightarrow> int mat list \<times> int mat" where
  "default_mat_inter n n1 =  (replicate n1 (1\<^sub>m n), 1\<^sub>m n)" 

locale mat_interpretation_parameter = squared_int_mat +
  fixes A :: "int mat set"
  and   M :: "int mat set"
  and   pI :: "'f \<times> nat \<Rightarrow> int mat list \<times> int mat" 
begin



definition wf_carrierS where
"wf_carrierS = (
  A \<subseteq> P \<and>
  (\<forall> a b. a \<in> A \<longrightarrow> b \<in> N \<longrightarrow> a + b \<in> A) \<and>
  (\<forall> a b. a \<in> A \<longrightarrow> b \<in> A \<longrightarrow> a * b \<in> A)
)"

definition wf_carrierMono where
"wf_carrierMono = (
  M \<subseteq> N \<and>
  (\<forall> a b. a \<in> carrier_mat n n \<longrightarrow> b \<in> carrier_mat n n \<longrightarrow> a - b \<in> M \<longrightarrow> a >\<^sub>m b) \<and>
  (\<forall> a b. a \<in> M \<longrightarrow> b \<in> A \<longrightarrow> b * a \<in> M) \<and>
  (\<forall> a b. a \<in> M \<longrightarrow> b \<in> A \<longrightarrow> a * b \<in> M) \<and>
  (\<forall> a b. a \<in> M \<longrightarrow> b \<in> N \<longrightarrow> a + b \<in> M)
)"



definition Matsemiring :: "int mat explicit_minus_semiring" where 
  "Matsemiring = \<lparr>
  carrier = carrier_mat n n,
  mult = (*),
  one = 1\<^sub>m n,
  zero = 0\<^sub>m n n,
  add = (+),
  ordered_semiring.geq = (\<ge>\<^sub>m),
  ordered_semiring.gt = (>\<^sub>m),
  ordered_semiring.max = (\<lambda>a. \<lambda> b. if a > b then a else b),
  minus = (\<lambda>x. -x)
  \<rparr>"

definition R_mat_semiring :: "int mat strictly_ordered_semiring" where 
  "R_mat_semiring = \<lparr>
  carrier = carrier_mat n n,
  mult = (*),
  one = 1\<^sub>m n,
  zero = 0\<^sub>m n n,
  add = (+),
  ordered_semiring.geq = (\<ge>\<^sub>m),
  ordered_semiring.gt = (>\<^sub>m),
  ordered_semiring.max = (\<lambda>a. \<lambda> b. if a > b then a else b),
  minus = (\<lambda>x. -x),
  carrierR = N,
  carrierS = A,
  carrierMono = M
  \<rparr>"



lemma mat_minus_is_ring_minus:
  assumes "x \<in> carrier R_mat_semiring"
  shows "-x = \<ominus>\<^bsub>R_mat_semiring\<^esub>x"
proof -
  have x: "x \<in> carrier_mat n n" "-x \<in> carrier_mat n n"
    using assms
    by (simp add: R_mat_semiring_def)+
  define P where "P = (\<lambda>y. y \<in> carrier_mat n n \<and> x + y = 0\<^sub>m n n \<and> y + x = 0\<^sub>m n n)"
  have "P (-x)"
    unfolding P_def
    using x by auto
  moreover
  {
    fix y
    assume as: "P y"
    then have as1: "y \<in> carrier_mat n n" "x + y = 0\<^sub>m n n"
      unfolding P_def by auto
    have "y = -x" 
      apply (rule eq_matI)
      subgoal for i j using x as1(1) arg_cong[OF as1(2), of "\<lambda> m. m $$ (i,j)"] by auto
      by (insert as1 x, auto)
  }
  ultimately show ?thesis
    unfolding a_inv_def m_inv_def monoid.simps R_mat_semiring_def partial_object.simps ring.simps
              P_def
    using the_equality[symmetric, of "\<lambda>y. y \<in> carrier_mat n n \<and> x + y = 0\<^sub>m n n \<and> y + x = 0\<^sub>m n n" "-x"]
    by auto
qed

lemma mat_sub_is_ring_sub:
  assumes "x \<in> carrier R_mat_semiring" "y \<in> carrier R_mat_semiring"
  shows "x - y = x \<ominus>\<^bsub>R_mat_semiring\<^esub> y"
  unfolding a_minus_def
  using assms mat_minus_is_ring_minus
        add_uminus_minus_mat[OF assms[unfolded R_mat_semiring_def partial_object.simps]]
  by (simp add: R_mat_semiring_def)
  



lemma R_mat_semiring_is_strictly_ordered_ring:
  assumes "wf_carrierS" "wf_carrierMono"
  shows "strictly_ordered_ring R_mat_semiring"
proof ((unfold_locales; unfold R_mat_semiring_def strictly_ordered_semiring.simps
          ordered_semiring.simps monoid.simps partial_object.simps ring.simps), goal_cases)
  case 7
  then show ?case unfolding Units_def monoid.simps partial_object.simps
  proof
    fix x :: "int mat"
    assume carr: "x \<in> carrier_mat n n"
    then have "x + (-x) = 0\<^sub>m n n" "-x + x = 0\<^sub>m n n" "-x \<in> carrier_mat n n" by auto
    then have "\<exists>y\<in>carrier_mat n n. x + y = 0\<^sub>m n n \<and> y + x = 0\<^sub>m n n"
      by auto
    then show "x \<in> {y \<in> carrier_mat n n. \<exists>x\<in>carrier_mat n n. x + y = 0\<^sub>m n n \<and> y + x = 0\<^sub>m n n}"
      using carr by auto
  qed
next
  case (13 x y z)
  then show ?case using add_mult_distrib_mat[of x]  by auto
next
  case (14 x y z)
  then show ?case using mult_add_distrib_mat[of z] by auto
next
  case (15 x y z)
  then show ?case using mat_ge_gt_trans_simpler by auto
next
  case (16 x y z)
  then show ?case using mat_gt_ge_trans_simpler[of x y] by auto
next
  case 17
  then show ?case using N_in_carr by auto
next
  case 18
  then show ?case using assms(1)[unfolded wf_carrierS_def] P_in_N by auto
next
  case 19
  then show ?case
    using assms[unfolded wf_carrierS_def wf_carrierMono_def]
          subset_trans[of M A N] by auto
next
  case (22 x y)
  then show ?case using N_add_closed by auto
next
  case (23 x y)
  then show ?case using N_mult_closed by auto
next
  case (24 x y)
  then show ?case using assms(1)[unfolded wf_carrierS_def] by auto
next
  case (25 x y)
  then show ?case using assms(1)[unfolded wf_carrierS_def] by auto
next
  case (26 x y)
  then show ?case using assms(2)[unfolded wf_carrierMono_def N_def] by auto
next
  case (27 x y)
  then show ?case using assms(2)[unfolded wf_carrierMono_def] by auto
next
  case (28 y z x)
  then show ?case using mat_plus_right_mono[of y z] by auto
next
  case (29 y z x)
  then show ?case using mat_gt_add_right_mono_simpler by auto
next
  case (30 y z x)
  then show ?case using mat_mult_right_mono N_el_in_carr[of x] N_greater_eq_zero by auto
next
  case (31 y z x)
  then show ?case using mat_mult_left_mono N_el_in_carr[of x] N_greater_eq_zero by auto
next
  case *: (32 x y)
  then show ?case using assms[unfolded wf_carrierS_def wf_carrierMono_def] by auto
next
  case *: (33 x y)
  then show ?case using assms[unfolded wf_carrierS_def wf_carrierMono_def] by auto
next
  case (34 x y)
  then show ?case
    using mat_sub_is_ring_sub[of x y, symmetric, unfolded R_mat_semiring_def]
          assms(2)[unfolded wf_carrierMono_def]
    by auto
next
  case (36 x y z)
  then show ?case
    using mat_ge_trans[of x y z n n] assms(1)[unfolded wf_carrierS_def]
          N_in_carr subset_trans[of A N "carrier_mat n n"]
          in_mono[of A "carrier_mat n n"]
    by auto
next
  case (37 x y z)
  then show ?case
    using mat_gt_trans_simpler[of x y z] assms(1)[unfolded wf_carrierS_def]
          N_in_carr subset_trans[of A N "carrier_mat n n"]
          in_mono[of A "carrier_mat n n"]
    by auto
next
  case 39
  then show ?case
  proof -
    define S\<^sub>1 where "S\<^sub>1 = {(a,b). a \<in> carrier_mat n n \<and> b \<in> carrier_mat n n \<and>
                      a \<ge>\<^sub>m 0\<^sub>m n n \<and> b \<ge>\<^sub>m 0\<^sub>m n n \<and> a >\<^sub>m b}"
    define S\<^sub>2 where "S\<^sub>2 = {(x, y). mat_gt (\<lambda>x y. y < x) n x y} \<restriction> N"
    {
      have "S\<^sub>1 = {(a,b). a \<in> N \<and> b \<in> N \<and> a >\<^sub>m b}"
        unfolding N_def S\<^sub>1_def by auto
      then have "S\<^sub>1 = S\<^sub>2"
        unfolding S\<^sub>2_def restrict_def by auto
    }
    then
    have "SN S\<^sub>2" unfolding S\<^sub>1_def using SN_mat_gt[unfolded mat_gt_set_def] by auto
    then show ?thesis unfolding S\<^sub>2_def SN_defs by auto
  qed
next
  case (40 x)
  then show ?case
    unfolding explicit_minus_semiring.simps
    using mat_minus_is_ring_minus[unfolded R_mat_semiring_def partial_object.simps]
    by auto
qed auto

end

context squared_int_mat
begin

context
  fixes A
  fixes pI :: "'f \<times> nat \<Rightarrow> int mat list \<times> int mat" 
  assumes pI: "\<And> f n cs c. pI (f,n) = (cs,c) 
    \<Longrightarrow> set (c # cs) \<subseteq> N \<and> length cs = n \<and> set (c#cs) \<inter> A \<noteq> {}"
  assumes n0: "n > 0"
begin


interpretation int_mat_param: mat_interpretation_parameter n A "core A" pI.


context
  assumes A_p: "int_mat_param.wf_carrierS"
begin

lemma A_in_N: "A \<subseteq> N"
  using A_p(1)[unfolded int_mat_param.wf_carrierS_def] P_in_N by auto

lemma A_in_carr: "A \<subseteq> carrier_mat n n"
  using subset_trans[OF A_in_N N_in_carr].

lemma wf_carrierMonoA: "int_mat_param.wf_carrierMono"
  unfolding int_mat_param.wf_carrierMono_def    
proof (intro conjI, goal_cases)
  case 1
  then show ?case using core_in_P P_in_N by auto
next
  case 2
  then show ?case using core_gt by auto
next
  case 3
  then show ?case
  proof -
    {
      fix a b
      assume as: "a \<in> core A" "b \<in> A"
      then have carr: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n"
        using core_in_carr A_in_carr by blast+
      have "b * a \<in> core A"
        using core_extended[OF A_in_carr, of "[b]" "[]" a, simplified]
              right_mult_one_mat[OF carr(2)] 
              right_mult_one_mat[OF mult_carrier_mat[OF carr(2,1)]] as
        by auto
    }
    then show ?thesis by auto
  qed
next
  case 4
  then show ?case
  proof -
    {
      fix a b
      assume as: "a \<in> core A" "b \<in> A"
      then have carr: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n"
        using core_in_carr A_in_carr by blast+
      have "a * b \<in> core A"
        using core_extended[OF A_in_carr, of "[]" "[b]" a, simplified]
              right_mult_one_mat[OF carr(2)] 
              left_mult_one_mat[OF carr(1)] as
        by auto
    }
    then show ?thesis by auto
  qed
next
  case 5
  then show ?case using core_plus_N_mono A_p[unfolded int_mat_param.wf_carrierS_def] P_in_N
    by auto
qed



 


abbreviation current_semiring where "current_semiring \<equiv> int_mat_param.R_mat_semiring"


interpretation int: lin_poly_inter current_semiring pI
  unfolding lin_poly_inter_def lin_poly_inter_axioms_def
  using int_mat_param.R_mat_semiring_is_strictly_ordered_ring[OF A_p wf_carrierMonoA] pI
  by (simp add: int_mat_param.R_mat_semiring_def)
  


text \<open>restriction on pI for strict termination\<close>
context
  assumes pI_strict: "\<And> f n cs c. pI (f,n) = (cs,c) \<Longrightarrow> set cs \<subseteq> A"
begin


interpretation mono_int: mono_lin_poly_inter current_semiring pI
  unfolding mono_lin_poly_inter_def mono_lin_poly_inter_axioms_def
  using int.lin_poly_inter_axioms pI_strict by (simp add: int_mat_param.R_mat_semiring_def)


fun eval_rule :: "('v, int mat) p_ass \<Rightarrow> ('f, 'v) term \<times> ('f, 'v) term \<Rightarrow> int mat" where
"eval_rule \<alpha> (l,r) = I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha>"

lemma eval_rule_id:
  assumes "wf_ass current_semiring \<alpha>"
  shows "eval_rule \<alpha> (s,s) = 0\<^sub>m n n"
  unfolding eval_rule.simps using minus_r_inv_mat int.eval_carrier[OF assms[unfolded wf_ass_def]]
  by (simp add: int_mat_param.R_mat_semiring_def )




lemma one_coeff_in_mono_imp:
  assumes
    "range \<alpha> \<subseteq> A"
    "set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)) \<subseteq> N"
    "\<exists>c \<in> set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)). c \<in> core A"
  shows "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> core A"
proof -
  have wf_\<alpha>: "wf_ass current_semiring \<alpha>"
    unfolding partial_object.simps int_mat_param.R_mat_semiring_def  wf_ass_def
    using subset_trans[OF subset_trans[OF 
              assms(1)
              int.carrierS_sub_carrierR[unfolded int_mat_param.R_mat_semiring_def strictly_ordered_semiring.simps]
              ]]
          assms(1)
    by auto
  then have carr: "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> \<in> carrier current_semiring" "I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> carrier current_semiring"
    using int.eval_A assms(2)
    by (simp add: int.lin_poly_inter_axioms lin_poly_inter.eval_term_I_Ip)+

  
  have "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> = int.eval_lpoly \<alpha> (evalp_rule current_semiring pI l r)"
  proof -
    have "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> = I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> \<ominus>\<^bsub>current_semiring\<^esub> I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha>"
      using int_mat_param.mat_sub_is_ring_sub[OF carr].
    also have "\<dots> = int.eval_lpoly \<alpha> (evalp_rule current_semiring pI l r)"
      using int.eval_rule_I_Ip[OF wf_\<alpha>].
    finally show ?thesis.
  qed
  moreover
  have "int.eval_lpoly \<alpha> (evalp_rule current_semiring pI l r) \<in> core A"
    using int.eval_lpoly_sound_carrierMono assms
    by (simp add: int_mat_param.R_mat_semiring_def )
  ultimately show ?thesis by auto
qed



lemma one_coeff_in_mono_imp_forall_assig:
  assumes
    "set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)) \<subseteq> N"
    "set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)) \<inter> core A \<noteq> {}"
  shows "\<And>\<alpha> :: ('v, int mat) p_ass. range \<alpha> \<subseteq> A \<Longrightarrow> eval_rule \<alpha> (l,r) \<in> core A"
proof -
  fix \<alpha> :: "('v, int mat) p_ass"
  assume as: "range \<alpha> \<subseteq> A"
  have r: "\<exists>c \<in> set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)). c \<in> core A"
    using assms by auto
  show "eval_rule \<alpha> (l,r) \<in> core A"
    unfolding eval_rule.simps using one_coeff_in_mono_imp[OF as assms(1) r].
qed


lemma one_coeff_in_mono_imp_forall_assig_trs:
  assumes
    "\<And>l r. (l,r) \<in> R \<Longrightarrow> set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)) \<subseteq> N \<and> 
        set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)) \<inter> core A \<noteq> {}"
  shows "\<And>\<alpha> :: ('v, int mat) p_ass. range \<alpha> \<subseteq> A \<Longrightarrow> (eval_rule \<alpha>) ` R \<subseteq> core A"
proof -
  fix \<alpha> :: "('v, int mat) p_ass"
  assume as: "range \<alpha> \<subseteq> A"
  {
    fix l r
    assume as1: "(l,r) \<in> R"
    have "eval_rule \<alpha> (l,r) \<in> core A"
      using one_coeff_in_mono_imp_forall_assig assms[OF as1] as
      by auto
  }
  then show "eval_rule \<alpha> ` R \<subseteq> core A"
    by force
qed

(*l=c(s, t, xxxx), r=s/t*)
(*C(la) = *)

lemma prod_list_mat_closed2:
  assumes "set(x#xs) \<subseteq> A"
  shows "prod_list_mat (x#xs) \<in> A"
proof -
  have carr: "set (x#xs) \<subseteq> carrier_mat n n"
    using A_p[unfolded int_mat_param.wf_carrierS_def] P_in_carr assms
    by blast
  show ?thesis
    using assms carr
  proof (induction xs arbitrary: x)
    case Nil
    then show ?case unfolding prod_list_mat.simps  by auto
  next
    case (Cons a xs)
    then show ?case
    proof -
      have "a * prod_list_mat xs \<in> A"
        using Cons
        by auto
      moreover
      have "x \<in> A" using Cons by auto
      ultimately
      show ?thesis unfolding prod_list_mat.simps using A_p[unfolded  int_mat_param.wf_carrierS_def]
        by auto
    qed
  qed
qed

lemma default_mat_inter_ce_trs: 
  assumes pI: "pI (c,Suc (Suc m)) = default_mat_inter n (Suc (Suc m))" 
  shows "ce_trs (c,m) \<subseteq> int.S_A" unfolding int.S_A_def
proof (clarify)
  fix l r :: "('f,'a)term" and \<alpha> :: "'a \<Rightarrow> int mat" 
  assume lr: "(l,r) \<in> ce_trs (c,m)" and as: "range \<alpha> \<subseteq> carrierS current_semiring" 
  from lr[unfolded ce_trs.simps] obtain t s
    where l: "l = Fun c (t # s # replicate m (Var undefined))" 
     and r: "r = t \<or> r = s" by auto
  define u where "u = (if r = t then s else t)" 
  from r have choice: "r = t \<and> u = s \<or> r = s \<and> u = t" unfolding u_def by auto
  {
    fix t  
    from as have "int.eval t \<alpha> \<in> carrier current_semiring" 
      using int.carrierS_sub_carrier int.eval_carrierS mat_interpretation_parameter.R_mat_semiring_def
      by auto
    hence t: "int.eval t \<alpha> \<in> carrier_mat n n" 
      by (simp add: mat_interpretation_parameter.R_mat_semiring_def)  
    hence "1\<^sub>m n \<otimes>\<^bsub>current_semiring\<^esub> int.eval t \<alpha> = int.eval t \<alpha>" 
      by (simp add: int_mat_param.R_mat_semiring_def) 
    note t this
  } note eval = this
  define \<alpha>u where "\<alpha>u = \<alpha> undefined" 
  have "\<alpha>u \<in> carrierS current_semiring" using as unfolding \<alpha>u_def by auto
  hence "\<alpha>u \<in> A" by (simp add: int_mat_param.R_mat_semiring_def)
  hence \<alpha>u: "\<alpha>u \<in> carrier_mat n n" 
    using A_in_carr by auto
  hence 1: "1\<^sub>m n \<otimes>\<^bsub>current_semiring\<^esub> \<alpha>u = \<alpha>u"
    by (simp add: int_mat_param.R_mat_semiring_def)
  define other where "other = list_sum current_semiring (replicate m \<alpha>u)"
  define more where "more = int.eval u \<alpha> + 1\<^sub>m n + other" 
  have other: "other = smult_mat (int m) \<alpha>u" 
    unfolding other_def using \<alpha>u 
    by (simp add: int_mat_param.R_mat_semiring_def, induct m, auto simp: add_smult_distrib_right_mat) 
  have "int.eval l \<alpha> = 1\<^sub>m n \<oplus>\<^bsub>current_semiring\<^esub> (int.eval t \<alpha> \<oplus>\<^bsub>current_semiring\<^esub> (int.eval s \<alpha> \<oplus>\<^bsub>current_semiring\<^esub> other))" 
    unfolding l other_def by (subst 1[symmetric]) (simp add: I_def pI default_mat_inter_def eval \<alpha>u_def)
  also have "\<dots> = 1\<^sub>m n + (int.eval t \<alpha> + (int.eval s \<alpha> + other))" 
    by (simp add: int_mat_param.R_mat_semiring_def) 
  also have "\<dots> = (int.eval t \<alpha> + int.eval s \<alpha>) + 1\<^sub>m n + other" 
    unfolding other using \<alpha>u eval(1)[of s] eval(1)[of t] by auto
  also have "int.eval t \<alpha> + int.eval s \<alpha> = int.eval r \<alpha> + int.eval u \<alpha>" 
    using choice eval(1)[of s] eval(1)[of t] by auto
  also have "\<dots> + 1\<^sub>m n + other = int.eval r \<alpha> + more" 
    unfolding more_def other using \<alpha>u eval(1)[of r] eval(1)[of u] by auto
  finally have evall: "int.eval l \<alpha> = int.eval r \<alpha> + more" .
  have more: "more \<in> carrier_mat n n" unfolding more_def other using eval(1)[of u] \<alpha>u by auto
  have "int.eval r \<alpha> + more \<ominus>\<^bsub>current_semiring\<^esub> int.eval r \<alpha> = (int.eval r \<alpha> + more) - int.eval r \<alpha>" 
    by (metis (no_types, lifting) eval(1) evall int_mat_param.R_mat_semiring_def
        int_mat_param.mat_sub_is_ring_sub partial_object.select_convs(1))
  also have "\<dots> = more" using eval(1)[of r] more by auto
  finally have sub[simp]: "int.eval l \<alpha> \<ominus>\<^bsub>current_semiring\<^esub> int.eval r \<alpha> = more" using evall by auto
  have r[simp]: "int.eval r \<alpha> \<in> carrierS current_semiring" using int.eval_carrierS[of \<alpha> r] as 
    by (simp add: int_mat_param.R_mat_semiring_def)
  have l[simp]: "int.eval l \<alpha> \<in> carrierS current_semiring" using int.eval_carrierS[of \<alpha> l] as 
    by (simp add: int_mat_param.R_mat_semiring_def)

  have moreS: "more \<in> carrierS current_semiring"
  proof -
    have "int.eval u \<alpha> \<in> carrierS current_semiring" using int.eval_A as
      by (simp add: int_mat_param.R_mat_semiring_def)
    moreover
    have "1\<^sub>m n \<in> N" by auto
    ultimately
    have "int.eval u \<alpha> + 1\<^sub>m n \<in> carrierS current_semiring" using A_p[unfolded int_mat_param.wf_carrierS_def]
      by (simp add: int_mat_param.R_mat_semiring_def)
    moreover
    have "other \<in> N"
    proof -
      have r1: "set(replicate m \<alpha>u) \<subseteq> carrierS current_semiring"
        using \<open>\<alpha>u \<in> A\<close> int_mat_param.R_mat_semiring_def by auto
      then have "set(replicate m \<alpha>u) \<subseteq> carrierR current_semiring"
        using A_p[unfolded int_mat_param.wf_carrierS_def]
              strictly_ordered_ring.carrierS_sub_carrierR[OF 
                  int_mat_param.R_mat_semiring_is_strictly_ordered_ring[OF A_p wf_carrierMonoA]]
        by auto
      then have "other \<in> carrierR current_semiring"
        unfolding other_def
        using strictly_ordered_ring.list_sum_carrierR[OF
        int_mat_param.R_mat_semiring_is_strictly_ordered_ring[OF A_p wf_carrierMonoA]]
        by auto
      then show ?thesis by (simp add: int_mat_param.R_mat_semiring_def)
    qed
    ultimately
    show ?thesis unfolding more_def using A_p[unfolded int_mat_param.wf_carrierS_def]
      by (simp add: int_mat_param.R_mat_semiring_def)
  qed
  have moreMono: "more \<in> carrierMono current_semiring"
  proof -
    {
      fix a1 a2
      assume as: "set a1 \<subseteq> A" "set a2 \<subseteq> A"
      have moreP: "more \<in> P"
        using moreS A_p[unfolded int_mat_param.wf_carrierS_def]
              mat_interpretation_parameter.R_mat_semiring_def by auto
      then have "prod_list_mat a1 * more * prod_list_mat a2 \<in> P"
      proof (cases a1)
        case Nil
        then show ?thesis
        proof (cases a2)
          case *:Nil
          have "prod_list_mat a1 = 1\<^sub>m n" "prod_list_mat a2 = 1\<^sub>m n"
            using Nil * by auto
          then show ?thesis using more moreP by auto
        next
          case (Cons a list)
          have "prod_list_mat a1 = 1\<^sub>m n"
            using Nil by auto
          moreover
          from Cons have "prod_list_mat a2 \<in> A"
            using prod_list_mat_closed2 as(2)
            by auto
          ultimately
          show ?thesis using more moreS A_p[unfolded int_mat_param.wf_carrierS_def]
              int_mat_param.R_mat_semiring_def by auto
        qed
      next
        case (Cons a list)
        then show ?thesis
        proof (cases a2)
          case Nil
          then show ?thesis
          proof -
            have "prod_list_mat a2 = 1\<^sub>m n"
              using Nil by auto
            moreover
            from Cons have "prod_list_mat a1 \<in> A"
              using prod_list_mat_closed2 as(1)
              by auto
            ultimately
            show ?thesis using more moreS A_p[unfolded int_mat_param.wf_carrierS_def]
                int_mat_param.R_mat_semiring_def by auto
          qed
        next
          case *:(Cons a list)
          then show ?thesis
          proof -
            have "prod_list_mat a1 \<in> A" "prod_list_mat a2 \<in> A"
              using prod_list_mat_closed2 as Cons *
              by auto
            then show ?thesis using more moreS A_p[unfolded int_mat_param.wf_carrierS_def]
                int_mat_param.R_mat_semiring_def by auto
          qed
        qed
      qed
    }
    then show ?thesis unfolding strictly_ordered_semiring.simps int_mat_param.R_mat_semiring_def core_def
      using more
      by (simp add: mat_interpretation_parameter.R_mat_semiring_def)
  qed
  show "(int.eval l \<alpha>, int.eval r \<alpha>) \<in> int.S" unfolding int.S_def using moreMono by auto
qed

lemma default_mat_inter_ce_compatible:
  assumes pI: "\<And> c m. (c,m) \<notin> set F \<Longrightarrow> pI (c,m) = default_mat_inter n m" 
  shows "ce_compatible int.S_A" 
proof -
  define k where "k = max_list (map snd F)" 
  show ?thesis unfolding ce_compatible_def
  proof (rule exI[of _ k], intro allI impI, rule default_mat_inter_ce_trs[OF pI], rule notI)
    fix m c  
    assume "k \<le> m" "(c, Suc (Suc m)) \<in> set F" 
    hence "Suc (Suc m) \<in> set (map snd F)" by auto
    from max_list[OF this, folded k_def] 
    have "Suc (Suc m) \<le> k" by auto
    with \<open>k \<le> m\<close> show False by auto
  qed
qed


lemma rstep_carrierMono:
  assumes
    "\<And>(\<alpha> :: 'a \<Rightarrow> int mat). range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow>
       I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> carrierMono current_semiring"
  shows "\<And>(\<alpha> :: 'a \<Rightarrow> int mat). range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow>
         I current_semiring pI\<lbrakk>C\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>C\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> \<in> carrierMono current_semiring"
proof -
  fix \<alpha> :: "'a \<Rightarrow> int mat"
  assume as: "range \<alpha> \<subseteq> carrierS current_semiring"
  have \<alpha>2_as: "range (\<lambda>x. I current_semiring pI\<lbrakk>\<sigma> x\<rbrakk>\<alpha>) \<subseteq> carrierS current_semiring"
    using int.eval_carrierS[OF as] by auto

  have id1: "I current_semiring pI\<lbrakk>l \<cdot> \<sigma>\<rbrakk>\<alpha> = I current_semiring pI\<lbrakk>l\<rbrakk>(\<lambda>x. I current_semiring pI\<lbrakk>\<sigma> x\<rbrakk>\<alpha>)"
            "I current_semiring pI\<lbrakk>r \<cdot> \<sigma>\<rbrakk>\<alpha> = I current_semiring pI\<lbrakk>r\<rbrakk>(\<lambda>x. I current_semiring pI\<lbrakk>\<sigma> x\<rbrakk>\<alpha>)"
    using wf_algebra.eval_subst[OF int.wf_algebra_axioms, of _ \<sigma> \<alpha>] by auto

  show "I current_semiring pI\<lbrakk>C\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>C\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> \<in> carrierMono current_semiring"
  proof (induction C)
    case Hole
    then show ?case using id1 assms[OF \<alpha>2_as] by auto
  next
    case (More x1 x2 C x4)
    then show ?case
    proof -
      have more_id: "I current_semiring pI\<lbrakk>(More x1 x2 C x4)\<langle>t \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> =
            I current_semiring pI x1 ([I current_semiring pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]@I current_semiring pI\<lbrakk>C\<langle>t \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>#[I current_semiring pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x4])" for t
        by auto
      moreover
      have carrs:
           "set ([I current_semiring pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]@[I current_semiring pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x4]) \<subseteq> carrierS current_semiring"
           "I current_semiring pI\<lbrakk>C\<langle>t \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> \<in> carrierS current_semiring" for t
        using wf_algebra.eval_A[OF int.wf_algebra_axioms as] by auto
      moreover
      have "(I current_semiring pI\<lbrakk>C\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>, I current_semiring pI\<lbrakk>C\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>) \<in> int.S" (is "(?l, ?r) \<in> _")
      proof -
        have "?l - ?r = ?l \<ominus>\<^bsub>current_semiring\<^esub> ?r"
          using int_mat_param.mat_sub_is_ring_sub set_mp[OF int.carrierS_sub_carrier carrs(2)]
          by auto
        then have "?l \<ominus>\<^bsub>current_semiring\<^esub> ?r \<in> carrierMono current_semiring"
          using More.IH by auto
        then show ?thesis unfolding int.S_def restrict_def using carrs(2) by auto
      qed
      ultimately have "(I current_semiring pI\<lbrakk>(More x1 x2 C x4)\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>, I current_semiring pI\<lbrakk>(More x1 x2 C x4)\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>) \<in> int.S" (is "(?l, ?r) \<in> _")
        using mono_int.sm by auto
      then show ?thesis
      proof -
        have c:"I current_semiring pI\<lbrakk>(More x1 x2 C x4)\<langle>t \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> \<in> carrier current_semiring" for t
          using more_id carrs set_mp[OF int.carrierS_sub_carrier]
          by (meson as int.lin_poly_inter_axioms lin_poly_inter.eval_carrierS)
        have "?l \<ominus>\<^bsub>current_semiring\<^esub> ?r = ?l - ?r"
          using int_mat_param.mat_sub_is_ring_sub[OF c c] by auto
        then have "?l - ?r \<in> carrierMono current_semiring"
          using \<open>(?l, ?r) \<in> int.S\<close> unfolding int.S_def by auto
        then show ?thesis.
      qed
    qed
  qed
qed


lemma rstep_carrierMono2:
  assumes
    "\<And>\<alpha>. range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow> (eval_rule \<alpha>) ` R \<subseteq> carrierMono current_semiring"
  shows "\<And>\<alpha>. range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow> (eval_rule \<alpha>) ` rstep R \<subseteq> carrierMono current_semiring"
proof 
  fix \<alpha> x
  assume as: "range \<alpha> \<subseteq> carrierS current_semiring" "x \<in> (eval_rule \<alpha>) ` rstep R"
  {
    fix l r
    assume as1: "(l,r) \<in> rstep R"
    then obtain l' r' C \<sigma> where as2: "l = C\<langle>l' \<cdot> \<sigma>\<rangle>" "r = C\<langle>r' \<cdot> \<sigma>\<rangle>" "(l', r') \<in> R"
      by auto
    from assms as2(3) have "\<And>\<alpha>. range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow>
             eval_rule \<alpha> (l', r') \<in> carrierMono current_semiring"
      by blast
    then have "eval_rule \<alpha> (l, r) \<in> carrierMono current_semiring"
      using rstep_carrierMono[OF _ as(1)] as2(1,2) as(1) by auto
  }
  then show "x \<in> carrierMono current_semiring" using as by auto
qed




lemma rule_in_core_is_in_intS:
  assumes "range \<alpha> \<subseteq> A" "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> core A"
  shows "(I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha>, I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha>) \<in> int.S"
proof -
  have carrS: "I current_semiring pI\<lbrakk>t\<rbrakk>\<alpha> \<in> carrierS current_semiring" for t
    using int.eval_carrierS assms(1) by (simp add: int_mat_param.R_mat_semiring_def)
  then have carr: "I current_semiring pI\<lbrakk>t\<rbrakk>\<alpha> \<in> carrier current_semiring" for t
    using int.carrierS_sub_carrier by auto

  have "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> carrierMono current_semiring"
    using assms by (simp add: int_mat_param.R_mat_semiring_def)
  then have "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> \<ominus>\<^bsub>current_semiring\<^esub> I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> carrierMono current_semiring"
    using int_mat_param.mat_sub_is_ring_sub[OF carr carr, of l r] by auto
  then show ?thesis unfolding int.S_def restrict_def using carrS by auto
qed


lemma eval_rule_in_intSA:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> core A"
  shows "(l,r) \<in> int.S_A"
  unfolding int.S_A_def  using assms rule_in_core_is_in_intS
      int_mat_param.R_mat_semiring_def by auto


lemma rstep_core_imp_intSA:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> (eval_rule \<alpha>) ` rstep R \<subseteq> core A"
  shows "rstep R \<subseteq> int.S_A"
proof
  fix l r
  assume as: "(l,r) \<in> rstep R"
  then have "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> eval_rule \<alpha> (l,r) \<in> core A"
    using assms by blast
  then have "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> core A"
    by auto
  then show "(l,r) \<in> int.S_A"
    using eval_rule_in_intSA by auto
qed

lemma core_imp_rstep_intSA:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> (eval_rule \<alpha>) ` R \<subseteq> core A"
  shows "rstep R \<subseteq> int.S_A"
  by (rule rstep_core_imp_intSA[OF
    rstep_carrierMono2[unfolded int_mat_param.R_mat_semiring_def strictly_ordered_semiring.simps, OF assms, simplified],
    simplified
    ])




lemma all_coeff_in_N_imp:
  assumes
    "range \<alpha> \<subseteq> A"
    "set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)) \<subseteq> N"
  shows "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> N"
proof -
  have \<alpha>_carrR: "range \<alpha> \<subseteq> carrierR current_semiring"
    using assms(1) int.carrierS_sub_carrierR
    by (simp add: int_mat_param.R_mat_semiring_def)

  then have wf_\<alpha>: "wf_ass current_semiring \<alpha>"
    unfolding wf_ass_def using int.carrierR_sub_carrier by auto

  have "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> = int.eval_lpoly \<alpha> (evalp_rule current_semiring pI l r)"
  proof -
    have carr: "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> \<in> carrier current_semiring" "I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> carrier current_semiring"
      using int.eval_A assms(2) wf_\<alpha>
      by (simp add: int.lin_poly_inter_axioms lin_poly_inter.eval_term_I_Ip)+

    have "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> = I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> \<ominus>\<^bsub>current_semiring\<^esub> I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha>"
      using int_mat_param.mat_sub_is_ring_sub[OF carr].
    also have "\<dots> = int.eval_lpoly \<alpha> (evalp_rule current_semiring pI l r)"
      using int.eval_rule_I_Ip[OF wf_\<alpha>].
    finally show ?thesis.
  qed
  then show ?thesis using int.eval_lpoly_sound_carrierR[OF \<alpha>_carrR] assms(2)
    by (simp add: int_mat_param.R_mat_semiring_def)
qed


lemma all_coeffs_in_N_imp_forall_assig:
  assumes "set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)) \<subseteq> N"
  shows "\<And>\<alpha> :: ('v, int mat) p_ass. range \<alpha> \<subseteq> A \<Longrightarrow> eval_rule \<alpha> (l,r) \<in> N"
proof -
  fix \<alpha> :: "('v, int mat) p_ass"
  assume as: "range \<alpha> \<subseteq> A"
  show "eval_rule \<alpha> (l,r) \<in> N"
    unfolding eval_rule.simps using all_coeff_in_N_imp[OF as assms(1)].
qed



lemma all_coeff_in_N_imp_forall_assig_trs:
  assumes
    "\<And>l r. (l,r) \<in> R \<Longrightarrow> set (coeffs_of_lpoly_better (evalp_rule current_semiring pI l r)) \<subseteq> N"
  shows "\<And>\<alpha> :: ('v, int mat) p_ass. range \<alpha> \<subseteq> A \<Longrightarrow> (eval_rule \<alpha>) ` R \<subseteq> N"
proof -
  fix \<alpha> :: "('v, int mat) p_ass"
  assume as: "range \<alpha> \<subseteq> A"
  {
    fix l r
    assume as1: "(l,r) \<in> R"
    have "eval_rule \<alpha> (l,r) \<in> N"
      using all_coeffs_in_N_imp_forall_assig assms[OF as1] as
      by auto
  }
  then show "eval_rule \<alpha> ` R \<subseteq> N"
    by auto
qed


lemma rstep_carrierR:
  assumes
    "\<And>(\<alpha> :: 'a \<Rightarrow> int mat). range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow>
       I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> carrierR current_semiring"
  shows "\<And>(\<alpha> :: 'a \<Rightarrow> int mat). range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow>
         I current_semiring pI\<lbrakk>C\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>C\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> \<in> carrierR current_semiring"
proof -
  fix \<alpha> :: "'a \<Rightarrow> int mat"
  assume as: "range \<alpha> \<subseteq> carrierS current_semiring"
  have \<alpha>2_as: "range (\<lambda>x. I current_semiring pI\<lbrakk>\<sigma> x\<rbrakk>\<alpha>) \<subseteq> carrierS current_semiring"
    using int.eval_carrierS[OF as] by auto

  have id1: "I current_semiring pI\<lbrakk>l \<cdot> \<sigma>\<rbrakk>\<alpha> = I current_semiring pI\<lbrakk>l\<rbrakk>(\<lambda>x. I current_semiring pI\<lbrakk>\<sigma> x\<rbrakk>\<alpha>)"
            "I current_semiring pI\<lbrakk>r \<cdot> \<sigma>\<rbrakk>\<alpha> = I current_semiring pI\<lbrakk>r\<rbrakk>(\<lambda>x. I current_semiring pI\<lbrakk>\<sigma> x\<rbrakk>\<alpha>)"
    using wf_algebra.eval_subst[OF int.wf_algebra_axioms, of _ \<sigma> \<alpha>] by auto

  show "I current_semiring pI\<lbrakk>C\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>C\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> \<in> carrierR current_semiring"
  proof (induction C)
    case Hole
    then show ?case using id1 assms[OF \<alpha>2_as] by auto
  next
    case (More x1 x2 C x4)
    then show ?case
    proof -
      have more_id: "I current_semiring pI\<lbrakk>(More x1 x2 C x4)\<langle>t \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> =
            I current_semiring pI x1 ([I current_semiring pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]@I current_semiring pI\<lbrakk>C\<langle>t \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>#[I current_semiring pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x4])" for t
        by auto
      moreover
      have carrs:
           "set ([I current_semiring pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]@[I current_semiring pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x4]) \<subseteq> carrierS current_semiring"
           "I current_semiring pI\<lbrakk>C\<langle>t \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> \<in> carrierS current_semiring" for t
        using wf_algebra.eval_A[OF int.wf_algebra_axioms as] by auto
      moreover
      have "(I current_semiring pI\<lbrakk>C\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>, I current_semiring pI\<lbrakk>C\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>) \<in> int.NS" (is "(?l, ?r) \<in> _")
      proof -
        have carrs2: "?l \<in> carrier current_semiring" "?r \<in> carrier current_semiring"
          using carrs(2) int.carrierS_sub_carrier
          by auto
        have "?l - ?r = ?l \<ominus>\<^bsub>current_semiring\<^esub> ?r"
          using int_mat_param.mat_sub_is_ring_sub set_mp[OF int.carrierS_sub_carrier carrs(2)]
          by auto
        then have "?l \<ominus>\<^bsub>current_semiring\<^esub> ?r \<in> carrierR current_semiring"
          using More.IH by auto
        then have "?l - ?r \<in> carrierR current_semiring"
          using int_mat_param.mat_sub_is_ring_sub carrs2
          by auto
        then have "?l - ?r \<in> N" by (simp add: int_mat_param.R_mat_semiring_def)
        then have "?l \<succeq>\<^bsub>current_semiring\<^esub> ?r"
          using int_mat_param.R_mat_semiring_def 
                carrs2 mat_comparison_zero_eq N_def
          by force
        then show ?thesis unfolding int.NS_def restrict_def using carrs(2) by auto
      qed
      ultimately have "(I current_semiring pI\<lbrakk>(More x1 x2 C x4)\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>, I current_semiring pI\<lbrakk>(More x1 x2 C x4)\<langle>r \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha>) \<in> int.NS" (is "(?l, ?r) \<in> _")
        using int.wm by auto
      then show ?thesis
      proof -
        have c:"I current_semiring pI\<lbrakk>(More x1 x2 C x4)\<langle>t \<cdot> \<sigma>\<rangle>\<rbrakk>\<alpha> \<in> carrier current_semiring" for t
          using more_id carrs set_mp[OF int.carrierS_sub_carrier]
          by (meson as int.lin_poly_inter_axioms lin_poly_inter.eval_carrierS)
        from \<open>(?l, ?r) \<in> int.NS\<close> have "?l \<succeq>\<^bsub>current_semiring\<^esub> ?r"
          unfolding int.NS_def by auto
        then have "?l \<ge>\<^sub>m ?r"
          by (simp add: int_mat_param.R_mat_semiring_def )
        moreover
        have "?l \<in> carrier_mat n n" "?r \<in> carrier_mat n n"
          using c by (simp add: int_mat_param.R_mat_semiring_def )+
        ultimately have "?l - ?r \<in> N"
          unfolding N_def using minus_carrier_mat c mat_comparison_zero_eq
          by auto
        then show ?thesis by (simp add: int_mat_param.R_mat_semiring_def)
      qed
    qed
  qed
qed


lemma rstep_carrierR2:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow> (eval_rule \<alpha>) ` S \<subseteq> carrierR current_semiring"
  shows "\<And>\<alpha>. range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow> (eval_rule \<alpha>) ` rstep S \<subseteq> carrierR current_semiring"
proof 
  fix \<alpha> x
  assume as: "range \<alpha> \<subseteq> carrierS current_semiring" "x \<in> (eval_rule \<alpha>) ` rstep S"
  {
    fix l r
    assume as1: "(l,r) \<in> rstep S"
    then obtain l' r' C \<sigma> where as2: "l = C\<langle>l' \<cdot> \<sigma>\<rangle>" "r = C\<langle>r' \<cdot> \<sigma>\<rangle>" "(l', r') \<in> S"
      by auto
    from assms as2(3) have "\<And>\<alpha>. range \<alpha> \<subseteq> carrierS current_semiring \<Longrightarrow>
             eval_rule \<alpha> (l', r') \<in> carrierR current_semiring"
      by blast
    then have "eval_rule \<alpha> (l, r) \<in> carrierR current_semiring"
      using rstep_carrierR[OF _ as(1)] as2(1,2) as(1) by auto
  }
  then show "x \<in> carrierR current_semiring" using as by auto
qed


lemma rule_in_N_is_in_intNS:
  assumes "range \<alpha> \<subseteq> A" "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> N"
  shows "(I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha>, I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha>) \<in> int.NS"
proof -
  have carrS: "I current_semiring pI\<lbrakk>t\<rbrakk>\<alpha> \<in> carrierS current_semiring" for t
    using int.eval_carrierS assms(1) by (simp add: int_mat_param.R_mat_semiring_def)
  then have "I current_semiring pI\<lbrakk>t\<rbrakk>\<alpha> \<in> carrier current_semiring" for t
    using int.carrierS_sub_carrier by auto
 
  then have "I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha>  \<succeq>\<^bsub>current_semiring\<^esub> I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha>"
    using int_mat_param.R_mat_semiring_def 
          assms(2) mat_comparison_zero_eq squared_int_mat.N_def
    by force
  then show ?thesis unfolding int.NS_def restrict_def using carrS int_mat_param.R_mat_semiring_def by auto
qed


lemma eval_rule_in_intNSA:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> N"
  shows "(l,r) \<in> int.NS_A"
  unfolding int.NS_A_def using assms rule_in_N_is_in_intNS int_mat_param.R_mat_semiring_def
  by auto

lemma rstep_N_imp_intNSA:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> (eval_rule \<alpha>) ` rstep S \<subseteq> N"
  shows "rstep S \<subseteq> int.NS_A"
proof
  fix l r
  assume as: "(l,r) \<in> rstep S"
  then have "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> eval_rule \<alpha> (l,r) \<in> N"
    using assms by blast
  then have "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> I current_semiring pI\<lbrakk>l\<rbrakk>\<alpha> - I current_semiring pI\<lbrakk>r\<rbrakk>\<alpha> \<in> N"
    by auto
  then show "(l,r) \<in> int.NS_A"
    using eval_rule_in_intNSA by auto
qed


lemma N_imp_rstep_intNSA:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> (eval_rule \<alpha>) ` S \<subseteq> N"
  shows "rstep S \<subseteq> int.NS_A"
  by (rule rstep_N_imp_intNSA[OF
    rstep_carrierR2[unfolded int_mat_param.R_mat_semiring_def strictly_ordered_semiring.simps, OF assms, simplified],
    simplified
    ])

lemma eval_rule_in_N_imp_cloture:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> (eval_rule \<alpha>) ` S \<subseteq> N"
  shows "\<And>\<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> (eval_rule \<alpha>) ` S\<^sup>* \<subseteq> N"
proof
  fix \<alpha> x
  assume as: "range \<alpha> \<subseteq> A" "x \<in> (eval_rule \<alpha>) ` S\<^sup>*"
  then obtain l r where x: "x = eval_rule \<alpha> (l,r)" "(l,r) \<in> S\<^sup>*"
    by auto
  then obtain m where "(l,r) \<in> S ^^ m"
    by blast
  then obtain f where f_p:
                        "f 0 = l \<and> f m = r"
                        "\<And>k. k < m \<Longrightarrow> (f k, f (Suc k)) \<in> S"
    using relpow_fun_conv[of l r m S]
    by auto
  have wf_ass: "wf_ass current_semiring \<alpha>"
    unfolding wf_ass_def
    using A_p[unfolded int_mat_param.wf_carrierS_def]
          subset_trans[OF subset_trans[OF as(1), of N] N_in_carr] subset_trans[OF _ P_in_N]
    by (simp add: int_mat_param.R_mat_semiring_def)

  {
    fix k
    assume k_p: "k \<le> m"
    have "I current_semiring pI\<lbrakk>f 0\<rbrakk>\<alpha> \<ge>\<^sub>m I current_semiring pI\<lbrakk>f k\<rbrakk>\<alpha>"
      using k_p
    proof (induction k)
      case 0
      then show ?case using mat_ge_refl by auto
    next
      case (Suc k)
      then show ?case
      proof -
        from Suc.prems have k_p: "k \<le> m" "k < m" by auto
        have "eval_rule \<alpha> (f k, f (Suc k)) \<in> N"
          using f_p(2)[OF k_p(2)] assms[OF as(1)]
          by auto
        then have res: "I current_semiring pI\<lbrakk>f k\<rbrakk>\<alpha> \<ge>\<^sub>m I current_semiring pI\<lbrakk>f (Suc k)\<rbrakk>\<alpha>"
          unfolding eval_rule.simps
          using N_greater_eq_zero[OF minus_carrier_mat]
                mat_comparison_zero_eq
                int.eval_carrier[OF wf_ass[unfolded wf_ass_def]]
          by (simp add: int_mat_param.R_mat_semiring_def )
        show "I current_semiring pI\<lbrakk>f 0\<rbrakk>\<alpha> \<ge>\<^sub>m I current_semiring pI\<lbrakk>f (Suc k)\<rbrakk>\<alpha>"
          using mat_ge_trans[OF Suc.IH[OF k_p(1)] res, of n n]
                int.eval_carrier[OF wf_ass[unfolded wf_ass_def], of "f _"]
          by (simp add: int_mat_param.R_mat_semiring_def )
      qed
    qed
    then have "eval_rule \<alpha> (f 0, f k) \<in> N"
      using mat_comparison_zero_eq N_greater_eq_zero[symmetric, OF minus_carrier_mat]
            int.eval_carrier[OF wf_ass[unfolded wf_ass_def]]
      by (simp add: int_mat_param.R_mat_semiring_def )
  }
  then have "eval_rule \<alpha> (l,r) \<in> N"
    using f_p by auto
  then show "x \<in> N" using x by auto
qed





context
    fixes R :: "('f, 'v) trs"
    and   S :: "('f, 'v) trs"
begin


abbreviation A_interpretation where
"A_interpretation \<equiv> (\<forall>\<alpha>. range \<alpha> \<subseteq> A \<longrightarrow> (eval_rule \<alpha>) ` R \<subseteq> core A)"

abbreviation relative_criterion where
"relative_criterion \<equiv> (\<forall>\<alpha>. range \<alpha> \<subseteq> A \<longrightarrow> (eval_rule \<alpha>) ` S \<subseteq> N)"



lemma A_interpretation_terminates:
  assumes "A_interpretation"
  shows "SN (rstep R)"
  using assms core_imp_rstep_intSA[of R]
        SN_subset[OF wf_algebra.SN_S_A[OF int.wf_algebra_axioms]]
  by auto


lemma A_interpretation_terminates_relative:
  assumes "A_interpretation" "relative_criterion"
  shows "SN (rstep (S\<^sup>* O R O S\<^sup>*))"
proof -
  have "rstep (S\<^sup>* O R O S\<^sup>*) \<subseteq> int.S_A" (is "?lh \<subseteq> _")
  proof -
    have "?lh \<subseteq> rstep (S\<^sup>*) O rstep R O rstep (S\<^sup>*)"
      using rstep_distrib[of "S\<^sup>*" "R O S\<^sup>*"] O_mono1[OF rstep_distrib[of R "S\<^sup>*"], of "rstep (S\<^sup>*)"]
            subset_trans
      by auto
    also
    have "rstep (S\<^sup>*) \<subseteq> int.NS_A"
      using assms(2) eval_rule_in_N_imp_cloture[of S] N_imp_rstep_intNSA[of "S\<^sup>*"]
      by auto
    also
    have "rstep R \<subseteq> int.S_A"
      using assms(1) core_imp_rstep_intSA[of R]
      by auto
    finally
    have "?lh \<subseteq> int.NS_A O int.S_A O int.NS_A"
      using relcomp_mono by auto
    also have "\<dots> \<subseteq> int.S_A O int.NS_A"
      using int.NS_A_O_S_A relcomp_mono by auto
    also have "\<dots> \<subseteq> int.S_A"
      using int.S_A_O_NS_A.
    finally
    show ?thesis.
  qed
  then show ?thesis
    using SN_subset[OF wf_algebra.SN_S_A[OF int.wf_algebra_axioms]]
    by auto
qed

lemma A_interpretation_to_redtriple_orientation:
  assumes "A_interpretation" "relative_criterion" 
    "\<And> c m. (c,m) \<notin> set F \<Longrightarrow> pI (c,m) = default_mat_inter n m"
  shows "\<exists> s ns. mono_redtriple_order s ns ns \<and> R \<subseteq> s \<and> S \<subseteq> ns \<and> ce_compatible s" 
proof (intro exI conjI)
  show "R \<subseteq> int.S_A"
    using assms(1) core_imp_rstep_intSA[of R] by auto
  have "S \<subseteq> rstep S" by auto
  also have "\<dots> \<subseteq> rstep (S\<^sup>*)" by auto
  also have "\<dots> \<subseteq> int.NS_A" 
    using assms(2) eval_rule_in_N_imp_cloture[of S] N_imp_rstep_intNSA[of "S\<^sup>*"]
    by auto
  finally show "S \<subseteq> int.NS_A" .
  show "mono_redtriple_order int.S_A int.NS_A int.NS_A" by (rule mono_int.mono_redtriple_order)
  from default_mat_inter_ce_compatible[OF assms(3)] show "ce_compatible int.S_A" .
qed

end
end
end
end
end


lemma E\<^sub>I_wf_carrierS:
  assumes "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
  shows "mat_interpretation_parameter.wf_carrierS n (squared_int_mat.E\<^sub>I n ids)"
  unfolding mat_interpretation_parameter.wf_carrierS_def
  using squared_int_mat.E\<^sub>I_in_P[OF assms]
        squared_int_mat.E\<^sub>I_closed_add[OF assms]
        squared_int_mat.E\<^sub>I_closed_mult[OF assms]
  by auto

lemma M\<^sub>I_wf_carrierS:
  assumes "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
  shows "mat_interpretation_parameter.wf_carrierS n (squared_int_mat.M\<^sub>I n ids)"
  unfolding mat_interpretation_parameter.wf_carrierS_def
  using squared_int_mat.M\<^sub>I_in_P[OF assms]
        squared_int_mat.M\<^sub>I_closed_add[OF assms]
        squared_int_mat.M\<^sub>I_closed_mult[OF assms]
  by auto

definition wf_I :: "nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_I ids n \<equiv> ids \<subseteq> {0..< n} \<and> ids \<noteq> {}"

lemma wf_I[simp]:
  assumes "wf_I ids n"
  shows "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
  using assms[unfolded wf_I_def] by auto

lemma wf_I_n:
  assumes "wf_I ids n"
  shows "n > 0"
  using wf_I[OF assms] by auto


definition theor_pI where
  "theor_pI n pI A = (\<forall>f n1 cs c. pI (f, n1) = (cs, c) \<longrightarrow>
     set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set (c # cs) \<inter> A \<noteq> {} \<and> set cs \<subseteq> A)"

lemma theor_pI:
  assumes "theor_pI n pI A"
  shows "\<And>f n1 cs c. pI (f, n1) = (cs, c) \<Longrightarrow> set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set (c # cs) \<inter> A \<noteq> {}"
  "\<And>f n1 cs c. pI (f, n1) = (cs, c) \<Longrightarrow> set cs \<subseteq> A"
  using assms[unfolded theor_pI_def] by auto

definition concrete_pI :: "nat \<Rightarrow> ('f \<times> nat \<Rightarrow> int mat list \<times> int mat) \<Rightarrow> ('f \<times> nat) list \<Rightarrow> int mat set \<Rightarrow> bool" where
  "concrete_pI n pI fs A = (\<forall>f n1 cs c. (f,n1) \<in> set fs \<longrightarrow> pI (f, n1) = (cs, c) \<longrightarrow>
      set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set (c # cs) \<inter> A \<noteq> {} \<and> set cs \<subseteq> A)"

lemma concrete_pI:
  assumes "concrete_pI n pI fs A"
  shows "\<And>f n1 cs c. (f,n1) \<in> set fs \<Longrightarrow> pI (f, n1) = (cs, c) \<Longrightarrow> set (c # cs) \<subseteq> squared_int_mat.N n \<and>
 length cs = n1 \<and> set (c # cs) \<inter> A \<noteq> {}"
  "\<And>f n1 cs c. (f,n1) \<in> set fs \<Longrightarrow> pI (f, n1) = (cs, c) \<Longrightarrow> set cs \<subseteq> A"
  using assms[unfolded concrete_pI_def] by auto

lemma P\<^sub>I_wf_carrierMono:
  assumes "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
  shows "mat_interpretation_parameter.wf_carrierMono n (squared_int_mat.E\<^sub>I n ids) (squared_int_mat.P\<^sub>I n ids)"
  unfolding mat_interpretation_parameter.wf_carrierMono_def
proof (intro conjI, goal_cases)
  case 1
  then show ?case
    using squared_int_mat.P\<^sub>I_in_N[OF assms].
next
  case 2
  then show ?case using squared_int_mat.P\<^sub>I_greater_zero[OF assms]
      squared_int_mat.mat_comparison_zero by auto
next
  case 3
  then show ?case using squared_int_mat.P\<^sub>I_closed_E\<^sub>I_mul_left[OF assms] by auto
next
  case 4
  then show ?case using squared_int_mat.P\<^sub>I_closed_E\<^sub>I_mul_right[OF assms] by auto
next
  case 5
  then show ?case using squared_int_mat.P\<^sub>I_closed_add[OF assms] by auto
qed


lemma M\<^sub>I_wf_carrierMono:
  assumes "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
  shows "mat_interpretation_parameter.wf_carrierMono n (squared_int_mat.M\<^sub>I n ids) (squared_int_mat.M\<^sub>I n ids)"
  unfolding mat_interpretation_parameter.wf_carrierMono_def
proof (intro conjI, goal_cases)
  case 1
  then show ?case
    using squared_int_mat.M\<^sub>I_in_N[OF assms].
next
  case 2
  then show ?case using squared_int_mat.M\<^sub>I_greater_zero[OF assms]
      squared_int_mat.mat_comparison_zero by auto
next
  case 3
  then show ?case using squared_int_mat.M\<^sub>I_closed_mult[OF assms] by auto
next
  case 4
  then show ?case using squared_int_mat.M\<^sub>I_closed_mult[OF assms] by auto
next
  case 5
  then show ?case using squared_int_mat.M\<^sub>I_closed_add[OF assms] by auto
qed


lemma strictly_ordered_semiring_E\<^sub>I:
  assumes "ids \<subseteq> {0..< n}" "ids \<noteq>{}"
  shows "strictly_ordered_ring (mat_interpretation_parameter.R_mat_semiring n (squared_int_mat.E\<^sub>I n ids) (squared_int_mat.P\<^sub>I n ids))"
  using mat_interpretation_parameter.R_mat_semiring_is_strictly_ordered_ring P\<^sub>I_wf_carrierMono assms E\<^sub>I_wf_carrierS
  by auto


lemma strictly_ordered_semiring_M\<^sub>I:
  assumes "ids \<subseteq> {0..< n}" "ids \<noteq>{}"
  shows "strictly_ordered_ring (mat_interpretation_parameter.R_mat_semiring n (squared_int_mat.M\<^sub>I n ids) (squared_int_mat.M\<^sub>I n ids))"
  using mat_interpretation_parameter.R_mat_semiring_is_strictly_ordered_ring M\<^sub>I_wf_carrierMono assms M\<^sub>I_wf_carrierS
  by auto


lemmas domain_E\<^sub>I_term = squared_int_mat.A_interpretation_terminates[OF _ _ E\<^sub>I_wf_carrierS]
lemmas domain_M\<^sub>I_term = squared_int_mat.A_interpretation_terminates[OF _ _ M\<^sub>I_wf_carrierS]
lemmas domain_E\<^sub>I_rela_term = squared_int_mat.A_interpretation_terminates_relative[OF _ _ E\<^sub>I_wf_carrierS]
lemmas domain_M\<^sub>I_rela_term = squared_int_mat.A_interpretation_terminates_relative[OF _ _ M\<^sub>I_wf_carrierS]


lemma E\<^sub>I_interpretation_terminates:
  assumes as0: "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
        "(\<And>f n1 cs c.
      pI (f, n1) = (cs, c) \<Longrightarrow>
      set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set (c#cs) \<inter> squared_int_mat.E\<^sub>I n ids \<noteq> {})"
  "0 < n"
   "(\<And>f n1 cs c. pI (f, n1) = (cs, c) \<Longrightarrow> set cs \<subseteq> squared_int_mat.E\<^sub>I n ids)" and
     as:  "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n ids \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n ids) pI \<alpha> ` R
       \<subseteq> squared_int_mat.P\<^sub>I n ids"
shows "SN (rstep R)"
proof -
  from as have as: " \<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n ids \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n ids) pI \<alpha> ` R
       \<subseteq> squared_int_mat.core n (squared_int_mat.E\<^sub>I n ids)"
    using subset_trans[OF _ squared_int_mat.core_E\<^sub>I_in_P\<^sub>I[OF assms(1,2)]]
    by auto

  show ?thesis using domain_E\<^sub>I_term as0 as by auto
qed

lemma M\<^sub>I_interpretation_terminates:
  assumes as0: "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
        "(\<And>f n1 cs c.
      pI (f, n1) = (cs, c) \<Longrightarrow>
      set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set (c#cs) \<inter> squared_int_mat.M\<^sub>I n ids \<noteq> {})"
  "0 < n"
   "(\<And>f n1 cs c. pI (f, n1) = (cs, c) \<Longrightarrow> set cs \<subseteq> squared_int_mat.M\<^sub>I n ids)" and
     as:  "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n ids \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n ids) pI \<alpha> ` R
       \<subseteq> squared_int_mat.M\<^sub>I n ids"
shows "SN (rstep R)"
proof -
  from as have as: " \<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n ids \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n ids) pI \<alpha> ` R
       \<subseteq> squared_int_mat.core n (squared_int_mat.M\<^sub>I n ids)"
    using subset_trans[OF _ squared_int_mat.core_M\<^sub>I_in_M\<^sub>I[OF assms(1,2)]]
    by auto

  show ?thesis using domain_M\<^sub>I_term as0 as by auto
qed



lemma E\<^sub>I_interpretation_terminates_relative:
  assumes as0: "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
        "(\<And>f n1 cs c.
      pI (f, n1) = (cs, c) \<Longrightarrow>
      set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set (c#cs) \<inter> squared_int_mat.E\<^sub>I n ids \<noteq> {})"
  "0 < n"
   "(\<And>f n1 cs c. pI (f, n1) = (cs, c) \<Longrightarrow> set cs \<subseteq> squared_int_mat.E\<^sub>I n ids)" and
     as:  "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n ids \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n ids) pI \<alpha> ` R
       \<subseteq> squared_int_mat.P\<^sub>I n ids" and
     as1: "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n ids \<longrightarrow>
         squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n ids) pI \<alpha> ` S \<subseteq> squared_int_mat.N n"
shows "SN (rstep (S\<^sup>* O R O S\<^sup>*))"
proof -
  from as have as: " \<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.E\<^sub>I n ids \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.E\<^sub>I n ids) pI \<alpha> ` R
       \<subseteq> squared_int_mat.core n (squared_int_mat.E\<^sub>I n ids)"
    using subset_trans[OF _ squared_int_mat.core_E\<^sub>I_in_P\<^sub>I[OF assms(1,2)]]
    by auto

  show ?thesis using domain_E\<^sub>I_rela_term as0 as as1 by blast
qed

lemma M\<^sub>I_interpretation_terminates_relative:
  assumes as0: "ids \<subseteq> {0..< n}" "ids \<noteq> {}"
        "(\<And>f n1 cs c.
      pI (f, n1) = (cs, c) \<Longrightarrow>
      set (c # cs) \<subseteq> squared_int_mat.N n \<and> length cs = n1 \<and> set (c#cs) \<inter> squared_int_mat.M\<^sub>I n ids \<noteq> {})"
  "0 < n"
   "(\<And>f n1 cs c. pI (f, n1) = (cs, c) \<Longrightarrow> set cs \<subseteq> squared_int_mat.M\<^sub>I n ids)" and
     as:  "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n ids \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n ids) pI \<alpha> ` R
       \<subseteq> squared_int_mat.M\<^sub>I n ids" and
     as1: "\<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n ids \<longrightarrow>
         squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n ids) pI \<alpha> ` S \<subseteq> squared_int_mat.N n"
shows "SN (rstep (S\<^sup>* O R O S\<^sup>*))"
proof -
  from as have as: " \<forall>\<alpha>. range \<alpha> \<subseteq> squared_int_mat.M\<^sub>I n ids \<longrightarrow>
       squared_int_mat.eval_rule n (squared_int_mat.M\<^sub>I n ids) pI \<alpha> ` R
       \<subseteq> squared_int_mat.core n (squared_int_mat.M\<^sub>I n ids)"
    using subset_trans[OF _ squared_int_mat.core_M\<^sub>I_in_M\<^sub>I[OF assms(1,2)]]
    by auto

  show ?thesis using domain_M\<^sub>I_rela_term as0 as as1 by blast
qed

hide_const (open) I

end