(*
  Author:  René Thiemann and Ulysse Le Huitouze
*)

(* Plain linear polynomial interpretations without max, but supporting
   a different carrier for strict elements than the full carrier of the 
   semiring.
   
   Useful for matrix-interpretations in their SRS-version *)

theory Linear_Poly_Interpretation
  imports 
    Monotone_Algebra
    Linear_Polynomial
    "HOL-Algebra.Ring"
begin

hide_const (open) FuncSet.restrict
hide_fact (open) FuncSet.restrict_def

definition coeffs_of_pvars_better :: "('v, 'a) p_vars \<Rightarrow> 'a list" where
"coeffs_of_pvars_better = map snd"

fun coeffs_of_lpoly_better :: "('v, 'a) l_poly \<Rightarrow> 'a list" where
"coeffs_of_lpoly_better (LPoly a\<^sub>0 a\<^sub>is) = a\<^sub>0#coeffs_of_pvars_better a\<^sub>is"

lemma coeffs_pvars_sub_lpoly[simp]:
 "set (coeffs_of_pvars_better as) \<subseteq> set (coeffs_of_lpoly_better (LPoly a as))"
  unfolding coeffs_of_lpoly_better.simps by auto

lemma wf_pvars_split:
  assumes "wf_pvars R v\<^sub>1" "wf_pvars R v\<^sub>2"
  shows "wf_pvars R (v\<^sub>1@v\<^sub>2)"
  using assms by (simp add: wf_pvars_def)



lemma set_zip_bothD: "(a,b) \<in> set (zip as bs) \<Longrightarrow> a \<in> set as \<and> b \<in> set bs" for as bs
  by (meson in_set_zipE)



record 'a explicit_minus_semiring = "'a ordered_semiring" +
  minus :: "'a \<Rightarrow> 'a" (\<open>(\<open>open_block notation=\<open>prefix \<ominus>\<ominus>\<close>\<close>\<ominus>\<ominus>\<index> _)\<close> [81] 80)

record 'a strictly_ordered_semiring = "'a explicit_minus_semiring" +
  carrierR :: "'a set"    \<comment> \<open>Relaxed carrier. Interpretation of RS used for relative ter. should be in it.\<close>
  carrierS :: "'a set"    \<comment> \<open>Strict carrier. Interpretation of SN RS should be in it.\<close>
  carrierMono :: "'a set" \<comment> \<open>Monotonicity carrier. Interpretation of rules should be in it,
                              to become impervious to context outside which is in the strict carrier.\<close>
  

definition
  expl_a_minus :: "[('a, 'm) explicit_minus_semiring_scheme, 'a, 'a] => 'a"
        (\<open>(\<open>notation=\<open>infix \<ominus>\<ominus>\<close>\<close>_ \<ominus>\<ominus>\<index> _)\<close> [65,66] 65)
  where "x \<ominus>\<ominus>\<^bsub>R\<^esub> y = x \<oplus>\<^bsub>R\<^esub> (\<ominus>\<ominus>\<^bsub>R\<^esub> y)"



lemma list_sum_closed_submonoid:
  assumes "submonoid A (add_monoid R)" "set as \<subseteq> A"
  shows "list_sum R as \<in> A"
  using assms(2)
proof (induction as)
  case Nil
  then show ?case using assms[unfolded submonoid_def] by auto
next
  case (Cons a as)
  then show ?case
  proof -
    have "list_sum R as = list_prod (add_monoid R) as" by auto
    moreover
    have "set as \<subseteq> A" using Cons.prems by auto
    ultimately have "list_prod (add_monoid R) as \<in> A" using Cons.IH by auto
    moreover
    have "a \<in> A" using Cons.prems by auto
    ultimately have res1: "a \<otimes>\<^bsub>add_monoid R\<^esub> (list_prod (add_monoid R) as) \<in> A"
      using assms(1)[unfolded submonoid_def] by auto
    have "list_sum R (a # as) = list_prod (add_monoid R) (a # as)" by auto
    also have "\<dots> = a \<otimes>\<^bsub>add_monoid R\<^esub> (list_prod (add_monoid R) as)" by auto
    finally show "list_sum R (a # as) \<in> A" using res1 by auto
  qed
qed

context
  fixes R :: "('a, 'b) explicit_minus_semiring_scheme" (structure)
begin

definition vpoly :: "'v \<Rightarrow> ('v,'a) l_poly" where
  "vpoly x = LPoly \<zero> [(x,\<one>)]"

fun list_sum_poly :: "('v,'a) l_poly list \<Rightarrow> ('v,'a) l_poly" where
  "list_sum_poly [] = zero_lpoly R" 
| "list_sum_poly (p # ps) = sum_lpoly R p (list_sum_poly ps)" 

fun sub_var :: "('v, 'a) p_vars \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> ('v, 'a) p_vars" where 
  "sub_var [] x b = [(x, \<ominus>\<ominus>b)]"
| "sub_var ((y, a) # vas) x b =
    (if x = y then (let s = a \<ominus>\<ominus> b in if s = \<zero> then vas else (x, s) # vas)
    else ((y, a) # sub_var vas x b))"

fun sub_pvars :: "('v, 'a) p_vars \<Rightarrow> ('v, 'a) p_vars \<Rightarrow> ('v, 'a) p_vars" where
  "sub_pvars vas [] = vas"
| "sub_pvars vas ((x, b) # vbs) =
    (if b = \<zero> then sub_pvars vas vbs
    else sub_pvars (sub_var vas x b) vbs)"

fun sub_lpoly :: "('v, 'a) l_poly \<Rightarrow> ('v, 'a) l_poly \<Rightarrow> ('v, 'a) l_poly" where 
  "sub_lpoly (LPoly a vas) (LPoly b vbs) = LPoly (a \<ominus>\<ominus> b) (sub_pvars vas vbs)"




context
  fixes pI :: "'f \<times> nat \<Rightarrow> 'a list \<times> 'a"
begin

definition I where "I f as = (case pI (f,length as) of (cs, c) \<Rightarrow>
   list_sum R (c # map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs as)))"

definition Ip where "Ip f as = (case pI (f,length as) of (cs, c)
  \<Rightarrow> list_sum_poly (c_lpoly c # map (\<lambda> ca. mul_lpoly R (fst ca) (snd ca)) (zip cs as)))" 


abbreviation evalp where "evalp t \<equiv> Ip\<lbrakk>t\<rbrakk>vpoly" 

definition evalp_rule :: "('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> ('v, 'a) l_poly" where
"evalp_rule l r \<equiv> sub_lpoly (evalp l) (evalp r)"


end
end

locale strictly_ordered_ring = ring R for R :: "'a strictly_ordered_semiring" (structure) +
  assumes compat: "\<lbrakk>x \<succeq> (y :: 'a); y \<succ> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<succ> z"
  and compat2: "\<lbrakk>x \<succ> (y :: 'a); y \<succeq> z; x \<in> carrier R ; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<succ> z"
  and carrierR_sub_carrier: "carrierR R \<subseteq> carrier R"
  and carrierS_sub_carrierR: "carrierS R \<subseteq> carrierR R"
  and carrierMono_sub_carrierR: "carrierMono R \<subseteq> carrierR R"
  and zero_carrierR: "zero R \<in> carrierR R"
  and one_carrierR: "one R \<in> carrierR R"
  and plus_carrierR: "\<lbrakk>x \<in> carrierR R; y \<in> carrierR R\<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrierR R"
  and mult_carrierR: "\<lbrakk>x \<in> carrierR R; y \<in> carrierR R\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrierR R"
  and plus_carrierS: "\<lbrakk>x \<in> carrierS R; y \<in> carrierR R\<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrierS R"
  and mult_carrierS: "\<lbrakk>x \<in> carrierS R; y \<in> carrierS R\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrierS R"
  and plus_carrierMono: "\<lbrakk>x \<in> carrierMono R; y \<in> carrier R; y \<succeq> \<zero>\<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrierMono R"
  and plus_carrierMono2: "\<lbrakk>x \<in> carrierMono R; y \<in> carrierR R\<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrierMono R"
  and plus_right_mono: "\<lbrakk>y \<succeq> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<oplus> y \<succeq> x \<oplus> z"
  and plus_right_smono: "\<lbrakk>y \<succ> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<oplus> y \<succ> x \<oplus> z"
  and times_right_mono: "\<lbrakk>y \<succeq> z; x \<in> carrierR R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<otimes> y \<succeq> x \<otimes> z"
  and times_left_mono: "\<lbrakk>y \<succeq> z; x \<in> carrierR R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> y \<otimes> x \<succeq> z \<otimes> x"
  and carrierMono_times_right_closed: "\<lbrakk>y \<in> carrierMono R; x \<in> carrierS R\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrierMono R"
  and carrierMono_times_left_closed: "\<lbrakk>y \<in> carrierMono R; x \<in> carrierS R\<rbrakk> \<Longrightarrow> y \<otimes> x \<in> carrierMono R"
  and carrierMono_gt: "\<lbrakk>x \<in> carrier R; y \<in> carrier R; x \<ominus> y \<in> carrierMono R\<rbrakk> \<Longrightarrow> x \<succ> y"
  and geq_refl: "x \<in> carrier R \<Longrightarrow> x \<succeq> x" 
  and geq_trans[trans]: "\<lbrakk>x \<succeq> y; y \<succeq> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<succeq> z"
  and gt_trans[trans]: "\<lbrakk>x \<succ> y; y \<succ> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<succ> z"
  and gt_imp_ge: "\<lbrakk>x \<succ> y; x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow> x \<succeq> y" 
  and gt_SN: "SN_on (restrict {(x,y). x \<succ> y} (carrierR R)) (carrierR R)"
  and minus_wf[simp]: "\<lbrakk>x \<in> carrier R\<rbrakk> \<Longrightarrow> \<ominus>\<ominus>x = \<ominus>x"
begin



lemma minus_is_minus2[simp]:
 "\<lbrakk>x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow> x \<ominus> y = x \<ominus>\<ominus> y"
  using minus_wf expl_a_minus_def minus_eq
  by metis


lemma minus_in_carr[simp]:
"\<lbrakk>x \<in> carrier R\<rbrakk> \<Longrightarrow> \<ominus>\<ominus>x \<in> carrier R"
  using minus_wf by auto

lemma minus_in_carr2[simp]:
"\<lbrakk>x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow> x \<ominus>\<ominus> y \<in> carrier R"
  unfolding expl_a_minus_def
  using minus_wf by algebra


lemma list_sum_append: "set xs \<subseteq> carrier R \<Longrightarrow> set ys \<subseteq> carrier R \<Longrightarrow> list_sum R (xs @ ys) = list_sum R xs \<oplus> list_sum R ys" 
proof (induct xs)
  case (Cons x xs)
  hence IH: "list_sum R (xs @ ys) = list_sum R xs \<oplus> list_sum R ys" by auto
  show ?case unfolding list_prod.simps list.simps append_Cons IH monoid.simps
    by (rule a_assoc[symmetric], insert Cons, auto)
qed auto


lemma eval_vpoly[simp]: "\<alpha> x \<in> carrier R \<Longrightarrow> eval_lpoly  \<alpha> (vpoly R x) = \<alpha> x" 
  unfolding vpoly_def by auto

lemma wf_vpoly[intro,simp]: "wf_lpoly R (vpoly R x)" 
  by (auto simp: vpoly_def wf_pvars_def) 



lemma wf_list_sum_poly[intro, simp]: "Ball (set ps) (wf_lpoly R) \<Longrightarrow> wf_lpoly R (list_sum_poly R ps)" 
  by (induct ps, auto intro: wf_sum_lpoly simp: wf_pvars_def)

lemma eval_lpoly_sum: "wf_lpoly R p \<Longrightarrow> wf_lpoly R q \<Longrightarrow> range \<alpha> \<subseteq> carrier R \<Longrightarrow> 
  eval_lpoly \<alpha> (sum_lpoly R p q) = eval_lpoly \<alpha> p \<oplus> eval_lpoly \<alpha> q"
  by (meson sum_poly_sound wf_ass_def)

lemma eval_lpoly_mul: "a \<in> carrier R \<Longrightarrow> wf_lpoly R p \<Longrightarrow> range \<alpha> \<subseteq> carrier R \<Longrightarrow> 
  eval_lpoly \<alpha> (mul_lpoly R a p) = a \<otimes> eval_lpoly \<alpha> p"
  by (meson mul_poly_sound wf_ass_def)

lemma eval_lpoly_list_sum: "Ball (set ps) (wf_lpoly R) \<Longrightarrow> range \<alpha> \<subseteq> carrier R 
  \<Longrightarrow> eval_lpoly \<alpha> (list_sum_poly R ps) = list_sum R (map (eval_lpoly \<alpha>) ps)" 
proof (induct ps)
  case (Cons p ps)
  show ?case unfolding list_sum_poly.simps list_prod.simps list.simps monoid.simps
    by (subst eval_lpoly_sum, insert Cons, auto)
qed auto





lemma (in strictly_ordered_ring) plus_left_mono:
 "\<lbrakk>x \<succeq> y; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<oplus> z \<succeq> y \<oplus> z"
  using plus_right_mono[of x y z] by algebra

lemma (in strictly_ordered_ring) sub_zero[intro,simp]:
 "\<lbrakk>x \<in> carrier R\<rbrakk> \<Longrightarrow> x \<ominus> \<zero> = x"
  using minus_zero minus_eq by auto


lemma (in strictly_ordered_ring) carrierS_sub_carrier:
 "carrierS R \<subseteq> carrier R"
  using carrierS_sub_carrierR carrierR_sub_carrier subset_trans by auto

lemma (in strictly_ordered_ring) carrierMono_sub_carrier:
 "carrierMono R \<subseteq> carrier R"
  using carrierMono_sub_carrierR carrierR_sub_carrier subset_trans by auto




lemma (in strictly_ordered_ring) ge_imp_minus_ge_zero:
 "\<lbrakk>x \<in> carrier R; y \<in> carrier R; x \<succeq> y\<rbrakk> \<Longrightarrow> x \<ominus> y \<succeq> \<zero>"
proof -
  assume as: "x \<in> carrier R" "y \<in> carrier R" "x \<succeq> y"
  then have "x \<oplus> \<ominus>y \<succeq> y \<oplus> \<ominus>y"
    using  plus_right_mono a_inv_closed a_comm by auto
  also have "y \<oplus> \<ominus>y = \<zero>"
    using as(2)
    by (rule r_neg)
  finally show ?thesis using minus_eq by auto 
qed

lemma (in strictly_ordered_ring) gt_imp_minus_gt_zero:
 "\<lbrakk>x \<in> carrier R; y \<in> carrier R; x \<succ> y\<rbrakk> \<Longrightarrow> x \<ominus> y \<succ> \<zero>"
proof -
  assume as: "x \<in> carrier R" "y \<in> carrier R" "x \<succ> y"
  then have "x \<oplus> \<ominus>y \<succ> y \<oplus> \<ominus>y"
    using  plus_right_smono a_inv_closed a_comm by auto
  also have "y \<oplus> \<ominus>y = \<zero>"
    using as(2)
    by (rule r_neg)
  finally show ?thesis using minus_eq by auto
qed



lemma (in strictly_ordered_ring) carrierMono_right_mono:
 "\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R; x \<ominus> y \<in> carrierMono R; y \<succeq> z\<rbrakk> \<Longrightarrow> x \<ominus> z \<in> carrierMono R"
proof -
  assume as: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" "x \<ominus> y \<in> carrierMono R" "y \<succeq> z"
  then have "y \<ominus> z \<succeq> \<zero>" "y \<ominus> z \<in> carrier R" using ge_imp_minus_ge_zero by blast+
  then have "x \<ominus> y \<oplus> (y \<ominus> z) \<in> carrierMono R"
    using as(4) plus_carrierMono by auto
  then show "x \<ominus> z \<in> carrierMono R"
    using as(1,2,3) by algebra
qed

lemma (in strictly_ordered_ring) carrierMono_left_mono:
 "\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R; x \<succeq> y; y \<ominus> z \<in> carrierMono R\<rbrakk> \<Longrightarrow> x \<ominus> z \<in> carrierMono R"
proof -
  assume as: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" "x \<succeq> y" "y \<ominus> z \<in> carrierMono R"
  then have "x \<ominus> y \<succeq> \<zero>" "x \<ominus> y \<in> carrier R" using ge_imp_minus_ge_zero by blast+
  then have "y \<ominus> z \<oplus> (x \<ominus> y) \<in> carrierMono R"
    using as(5) plus_carrierMono by auto
  then show "x \<ominus> z \<in> carrierMono R"
    using as(1,2,3) by algebra
qed

lemma (in strictly_ordered_ring) carrierMono_trans:
 "\<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R; x \<ominus> y \<in> carrierMono R; y \<ominus> z \<in> carrierMono R\<rbrakk> \<Longrightarrow>
    x \<ominus> z \<in> carrierMono R"
proof -
  assume as: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" "x \<ominus> y \<in> carrierMono R" "y \<ominus> z \<in> carrierMono R"
  then have "y \<succeq> z" using gt_imp_ge carrierMono_gt by auto
  then show ?thesis using carrierMono_right_mono as by blast
qed



lemma carrierR_is_semiring: "semiring \<lparr>
  carrier = carrierR R,
  monoid.mult = mult R,
  one = one R,
  zero = zero R,
  add = add R
\<rparr>"
proof ((unfold_locales, auto), goal_cases)
  case (1 x y)
  then show ?case using plus_carrierR by auto
next
  case (2 x y z)
  then show ?case using a_assoc carrierR_sub_carrier by auto
next
  case 3
  then show ?case using zero_carrierR by auto
next
  case (4 x)
  then show ?case using l_zero carrierR_sub_carrier by auto
next
  case (5 x)
  then show ?case using r_zero carrierR_sub_carrier by auto
next
  case (6 x y)
  then show ?case using a_comm carrierR_sub_carrier by auto
next
  case (7 x y)
  then show ?case using mult_carrierR by auto
next
  case (8 x y z)
  then show ?case using m_assoc carrierR_sub_carrier by auto
next
  case 9
  then show ?case using one_carrierR by auto
next
  case (10 x)
  then show ?case using l_one carrierR_sub_carrier by auto
next
  case (11 x)
  then show ?case using r_one carrierR_sub_carrier by auto
next
  case (12 x y z)
  then show ?case using l_distr carrierR_sub_carrier by auto
next
  case (13 x y z)
  then show ?case using r_distr carrierR_sub_carrier by auto
next
  case (14 x)
  then show ?case using l_null carrierR_sub_carrier by auto
next
  case (15 x)
  then show ?case using r_null carrierR_sub_carrier by auto
qed

lemma (in strictly_ordered_ring) carrierR_submonoid: "submonoid (carrierR R) (add_monoid R)"
  unfolding submonoid_def
proof (intro conjI)
  show "carrierR R \<subseteq> carrier (add_monoid R)"
    using carrierR_sub_carrier by auto
  show "\<forall>x y. x \<in> carrierR R \<longrightarrow> y \<in> carrierR R \<longrightarrow> x \<otimes>\<^bsub>add_monoid R\<^esub> y \<in> carrierR R"
    using plus_carrierR by auto
  show "\<one>\<^bsub>add_monoid R\<^esub> \<in> carrierR R"
    using zero_carrierR by auto
qed
  


lemma list_sum_carrierR:
  assumes "set as \<subseteq> carrierR R"
  shows "list_sum R as \<in> carrierR R"
  using assms carrierR_submonoid list_sum_closed_submonoid by blast


lemma list_sum_carrierS[intro]: assumes "set as \<subseteq> carrierR R"
  and "set as \<inter> carrierS R \<noteq> {}" 
shows "list_sum R as \<in> carrierS R"
proof -
  from assms obtain x where "x \<in> set as" and x: "x \<in> carrierS R" by auto
  from split_list[OF this(1)] obtain b a where as: "as = b @ x # a" by auto
  from assms as have carrR: "{list_sum R b, list_sum R a, x} \<subseteq> carrierR R"
    using list_sum_closed_submonoid carrierR_submonoid by auto
  then have carr: "{list_sum R b, list_sum R a, x} \<subseteq> carrier R"
    using carrierR_sub_carrier
          subset_trans[of "{list_sum R b, list_sum R a, x}" "carrierR R" "carrier R"]
    by auto
  have "list_sum R as = list_sum R b \<oplus> (x \<oplus> list_sum R a)" unfolding as 
    by (subst list_sum_append, insert assms as carrierR_sub_carrier, auto)
  also have "\<dots> = x \<oplus> (list_sum R b \<oplus> list_sum R a)" using carr
    by (simp add: a_lcomm)
  also have "\<dots> \<in> carrierS R"
    by (rule plus_carrierS[OF x], insert carrR plus_carrierR, auto)
  finally show ?thesis .
qed




lemma eval_pvars_split:
  assumes "wf_ass R \<alpha>" "wf_pvars R v\<^sub>1" "wf_pvars R v\<^sub>2"
  shows "eval_pvars \<alpha> (v\<^sub>1@v\<^sub>2) = eval_pvars \<alpha> v\<^sub>1 \<oplus> eval_pvars \<alpha> v\<^sub>2"
  using assms(2)
proof (induction v\<^sub>1)
  case Nil
  then show ?case by (simp add: assms(1,3))
next
  case (Cons v v\<^sub>1)
  then show ?case
  proof (cases v)
    case (Pair x xa)
    then show ?thesis
    proof -

      have prems: "wf_pvars R v\<^sub>1" using Cons.prems by (simp add: wf_pvars_def)
      then have IH: "eval_pvars \<alpha> (v\<^sub>1 @ v\<^sub>2) = eval_pvars \<alpha> v\<^sub>1 \<oplus> eval_pvars \<alpha> v\<^sub>2" using Cons.IH by auto

      have carr: "xa \<in> carrier R" "\<alpha> x \<in> carrier R"
                 "eval_pvars \<alpha> v\<^sub>1 \<in> carrier R" "eval_pvars \<alpha> v\<^sub>2 \<in> carrier R"
      proof -
        show "xa \<in> carrier R" using Cons.prems Pair by (simp add: wf_pvars_def)
        show "\<alpha> x \<in> carrier R" by (rule range_subsetD[OF assms(1)[unfolded wf_ass_def]])
        show "eval_pvars \<alpha> v\<^sub>1 \<in> carrier R" by (rule wf_eval_pvars[OF assms(1) prems])
        show "eval_pvars \<alpha> v\<^sub>2 \<in> carrier R" by (rule wf_eval_pvars[OF assms(1,3)])
      qed

      have r: "eval_pvars \<alpha> ((v # v\<^sub>1) @ v\<^sub>2) = xa \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (v\<^sub>1@v\<^sub>2)"
        using Pair by auto

      have "eval_pvars \<alpha> (v # v\<^sub>1) \<oplus> eval_pvars \<alpha> v\<^sub>2 = (xa \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> v\<^sub>1) \<oplus> eval_pvars \<alpha> v\<^sub>2"
        using Pair by auto
      also have "\<dots> = xa \<otimes> \<alpha> x \<oplus> (eval_pvars \<alpha> v\<^sub>1 \<oplus> eval_pvars \<alpha> v\<^sub>2)"
        using carr by algebra
      also have "\<dots> = xa \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (v\<^sub>1@v\<^sub>2)"
        using IH by auto
      finally show ?thesis using r by auto
    qed
  qed
qed






lemma wf_sub_var[simp]:
  assumes "wf_pvars R vs" "a \<in> carrier R"
  shows "wf_pvars R (sub_var R vs x a)"
  using assms(1)
proof (induction vs)
  case Nil
  then show ?case
    using wf_pvars_def[of R "[(x,\<ominus>a)]"] sub_var.simps(1)[of R x a]
          a_inv_closed[OF assms(2)] minus_wf[OF assms(2)] by auto
next
  case (Cons v vs)

  have wf_vs: "wf_pvars R vs" using Cons.prems by (simp add: wf_pvars_def)
  then have IH: "wf_pvars R (sub_var R vs x a)" using Cons.IH by auto
  

  then show ?case
  proof (cases v)
    case (Pair y b)

    then have b_carr: "b \<in> carrier R" using Cons.prems by (simp add: wf_pvars_def)

    then show ?thesis
    proof (cases "x = y")
      case True
      then show ?thesis
      proof (cases "b \<ominus>\<ominus> a = \<zero>")
        case *: True
        then show ?thesis
        proof -
          from * True have "sub_var R (v # vs) x a = vs"
            using sub_var.simps(2)[of R y b vs x a, simplified] Pair by auto
          then show ?thesis using wf_vs by auto
        qed
      next
        case *: False
        then show ?thesis
        proof -
          from * True have "sub_var R (v # vs) x a = (x, b \<ominus>\<ominus> a)#vs"
            using sub_var.simps(2)[of R y b vs x a, simplified] Pair by auto
          moreover
          have "b \<ominus>\<ominus> a \<in> carrier R" using b_carr assms(2) by (rule minus_in_carr2)
          ultimately show ?thesis using wf_vs by (simp add: wf_pvars_def)
        qed
      qed
    next
      case False
      then show ?thesis
      proof -
        from False have "sub_var R (v # vs) x a = v#sub_var R vs x a"
          using sub_var.simps(2)[of R y b vs x a, simplified] Pair by auto
        then show ?thesis using Pair b_carr IH by (simp add: wf_pvars_def)
      qed
    qed
  qed
qed








lemma wf_sub_pvars[simp]:
  assumes "wf_pvars R vas" "wf_pvars R vbs"
  shows "wf_pvars R (sub_pvars R vas vbs)"
  using assms
proof (induction vbs arbitrary: vas)
  case Nil
  then show ?case using assms(1) by simp
next
  case (Cons v vbs)

  then have wf_vbs: "wf_pvars R vbs" by (simp add: wf_pvars_def)

  then show ?case
  proof (cases v)
    case (Pair x b)

    then have b_carr: "b \<in> carrier R" using Cons.prems(2) Pair by (simp add: wf_pvars_def)

    then show ?thesis
    proof (cases "b = \<zero>")
      case True
      then show ?thesis
      proof -
        from Pair True have "sub_pvars R vas (v # vbs) = sub_pvars R vas vbs"
          using sub_pvars.simps(2) by auto
        then show ?thesis using Cons.IH[OF Cons.prems(1) wf_vbs] by auto
      qed
    next
      case False
      then show ?thesis
      proof -
        have r1: "wf_pvars R (sub_var R vas x b)" using b_carr Cons.prems(1) by auto
        from Pair False have "sub_pvars R vas (v # vbs) = sub_pvars R (sub_var R vas x b) vbs"
          using sub_pvars.simps(2) by auto
        then show ?thesis using Cons.IH[OF r1 wf_vbs] by auto
      qed
    qed
  qed
qed




lemma sub_var_sound:
  assumes "wf_ass R \<alpha>" "wf_pvars R vas" "b \<in> carrier R"
  shows "eval_pvars \<alpha> (sub_var R vas x b) = \<ominus>b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas"
  using assms(2)
proof (induction vas)
  case Nil
  then show ?case using minus_wf[OF assms(3)] by auto
next
  case (Cons v vas)
  then show ?case
  proof (cases v)
    case (Pair y a)

    have wf_vas: "wf_pvars R vas" using Cons.prems by (simp add: wf_pvars_def)
    have a_carr: "a \<in> carrier R" using assms(2) wf_pvars_def Pair Cons.prems
      by (metis insert_subset list.simps(15,9) snd_conv)
    have vas_carr: "eval_pvars \<alpha> vas \<in> carrier R" by (rule wf_eval_pvars[OF assms(1) wf_vas])
    have wf_sub_vas: "eval_pvars \<alpha> (sub_var R vas x b) \<in> carrier R"
      by (rule wf_eval_pvars[OF assms(1) wf_sub_var[OF wf_vas assms(3)]])

    have x_carr: "\<alpha> x \<in> carrier R"
      using assms(1)[unfolded wf_ass_def] by auto

    then show ?thesis
    proof (cases "x = y")
      case True
      then show ?thesis
      proof (cases "a \<ominus>\<ominus> b = \<zero>")
        case *: True
        then show ?thesis
        proof -
          from * True have r1: "eval_pvars \<alpha> (sub_var R (v # vas) x b) = eval_pvars \<alpha> vas"
            using sub_var.simps(2) Pair by auto
          have "\<ominus> b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (v # vas) =
                \<ominus> b \<otimes> \<alpha> x \<oplus> (a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas)"
            using Pair True by auto
          also have "\<dots> = (\<ominus> b \<oplus> a) \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas"
            using a_carr assms(3) vas_carr x_carr
            by algebra
          also have "\<dots> = eval_pvars \<alpha> vas"
            using a_carr assms(1,3)[unfolded wf_ass_def] vas_carr *
            using a_comm a_inv_closed minus_eq range_subsetD minus_wf[OF assms(3)] expl_a_minus_def
            by (metis l_zero local.semiring_axioms semiring.l_null)
          finally show ?thesis using r1 by auto
        qed
      next
        case *: False
        then show ?thesis
        proof -
          from * True have "eval_pvars \<alpha> (sub_var R (v # vas) x b) = eval_pvars \<alpha> ((x, a \<ominus> b)#vas)" (is "?e1 = _")
            using sub_var.simps(2) Pair minus_is_minus2[OF a_carr assms(3)] by auto
          also have "\<dots> = (a \<ominus> b) \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas" (is "_ = ?e2")
            by auto
          finally have e12: "?e1 = ?e2" .
        

          have "\<ominus> b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (v # vas) =
                \<ominus> b \<otimes> \<alpha> x \<oplus> (a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas)"
            using True eval_pvars.simps(2) Pair by auto
          also have "\<dots> = (\<ominus> b \<otimes> \<alpha> x \<oplus> a \<otimes> \<alpha> x) \<oplus> eval_pvars \<alpha> vas"
            using a_carr assms(1,3)[unfolded wf_ass_def] vas_carr
          by (metis a_assoc a_inv_closed m_closed range_subsetD)
          also have "\<dots> = (a \<ominus> b) \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas"
            using a_carr assms(1,3)[unfolded wf_ass_def] vas_carr
          by (metis a_comm a_inv_closed l_distr minus_eq range_subsetD)
          finally show ?thesis using e12 by auto
        qed
      qed
    next
      case False
      then show ?thesis
      proof -
        have IH: "eval_pvars \<alpha> (sub_var R vas x b) = \<ominus> b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas"
          using Cons.IH wf_vas by auto

        have "eval_pvars \<alpha> (sub_var R (v # vas) x b) = eval_pvars \<alpha> (v#sub_var R vas x b)"
          using False by (simp add: Pair)
        also have "\<dots> = a \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> (sub_var R vas x b)"
          by (simp add: Pair)
        also have "\<dots> = a \<otimes> \<alpha> y \<oplus> (\<ominus>b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas)"
          using IH by auto
        also have "\<dots> = (\<ominus>b \<otimes> \<alpha> x) \<oplus> (a \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> vas)"
          using a_carr assms(3) assms(1)[unfolded wf_ass_def] vas_carr
        by (meson a_inv_closed a_lcomm m_closed range_subsetD)
        also have "\<dots> = (\<ominus>b \<otimes> \<alpha> x) \<oplus> eval_pvars \<alpha> (v#vas)"
          using Pair eval_pvars.simps(2) by auto
        finally show ?thesis.
      qed
    qed
  qed
qed
  


lemma sub_pvars_sub_var_sound:
  assumes "wf_ass R \<alpha>" "b \<in> carrier R" "wf_pvars R vas" "wf_pvars R vbs"
  shows " eval_pvars \<alpha> (sub_pvars R (sub_var R vas x b) vbs) = \<ominus>b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (sub_pvars R vas vbs)"
  using assms(2,3,4)
proof (induction vbs arbitrary: vas x b)
  case (Nil a b f)
  then show ?case by (simp add: assms(1) sub_var_sound)
next
  case (Cons v vs vas x b)

  then have wf_vs: "wf_pvars R vs" by (simp add: wf_pvars_def)

  then show ?case
  proof (cases v)
    case (Pair y a)
    then show ?thesis
    proof (cases "a = \<zero>")
      case True
      then show ?thesis
      proof -
        have r1: "eval_pvars \<alpha> (sub_pvars R vas (v # vs)) = eval_pvars \<alpha> (sub_pvars R vas vs)"
          using True Pair sub_pvars.simps(2) by auto
        have "eval_pvars \<alpha> (sub_pvars R (sub_var R vas x b) (v # vs)) =
              eval_pvars \<alpha> (sub_pvars R (sub_var R vas x b) vs)"
          using True Pair sub_pvars.simps(2) by auto
        also have "\<dots> = \<ominus> b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (sub_pvars R vas vs)"
          using Cons.IH Cons.prems wf_vs by auto
        finally show ?thesis using r1 by auto
      qed
    next
      case False
      then show ?thesis
      proof -
        have a_carr: "a \<in> carrier R"
          using Cons.prems Pair by (simp add: wf_pvars_def)
        have wf_sub_vas: "wf_pvars R (sub_var R vas x b)"
          using wf_sub_var[OF Cons.prems(2) Cons.prems(1)].
        have r1: "eval_pvars \<alpha> (sub_pvars R vas (v # vs)) = eval_pvars \<alpha> (sub_pvars R (sub_var R vas y a) vs)"
          using False Pair sub_pvars.simps(2) by auto

        have "eval_pvars \<alpha> (sub_pvars R (sub_var R vas x b) (v # vs)) =
              eval_pvars \<alpha> (sub_pvars R (sub_var R (sub_var R vas x b) y a) vs)"
          using False Pair sub_pvars.simps(2) by auto
        also have "\<dots> = \<ominus>a \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> (sub_pvars R (sub_var R vas x b) vs)"
          using Cons.IH[OF a_carr wf_sub_vas wf_vs].
        also have "\<dots> = \<ominus>a \<otimes> \<alpha> y \<oplus> (\<ominus>b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (sub_pvars R vas vs))"
          using Cons.IH[OF Cons.prems(1) Cons.prems(2) wf_vs] by auto
        also have "\<dots> = \<ominus>b \<otimes> \<alpha> x \<oplus> (\<ominus>a \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> (sub_pvars R vas vs))"
        proof -
          have "wf_pvars R (sub_pvars R vas vs)"
            using wf_sub_pvars[OF Cons.prems(2) wf_vs].
          then have "eval_pvars \<alpha> (sub_pvars R vas vs) \<in> carrier R"
            using wf_eval_pvars[OF assms(1)] by auto
          then show ?thesis using Cons.prems(1) a_carr assms(1)[unfolded wf_ass_def]
          by (meson a_inv_closed a_lcomm m_closed range_subsetD)
        qed
        also have "\<dots> = \<ominus>b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (sub_pvars R (sub_var R vas y a) vs)"
          using Cons.IH[OF a_carr Cons.prems(2) wf_vs] by auto
        finally show ?thesis using r1 by auto
      qed
    qed
  qed
qed



lemma sub_pvars_sound:
  assumes "wf_ass R \<alpha>" "wf_pvars R vas" "wf_pvars R vbs"
  shows "eval_pvars \<alpha> (sub_pvars R vas vbs) = eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> vbs"
  using assms(3)
proof (induction vbs)
  case Nil
  then show ?case using assms
  using sub_zero by auto
next
  case (Cons vb vbs)


  then have wf_vbs: "wf_pvars R vbs" by (simp add: wf_pvars_def)

  then show ?case
  proof (cases vb)
    case tu: (Pair x b)
    then show ?thesis
    proof -


      from Cons.prems have r1: "wf_pvars R vbs" unfolding wf_pvars_def by auto
      then have IH: "eval_pvars \<alpha> (sub_pvars R vas vbs) = eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> vbs"
        using Cons.IH by auto

      from Cons.prems[unfolded wf_pvars_def] tu
      have carr: "b \<in> carrier R" "eval_pvars \<alpha> vbs \<in> carrier R" "\<alpha> x \<in> carrier R"
        using wf_eval_pvars[OF assms(1) r1] assms(1)[unfolded wf_ass_def]
        by auto
   
      show "eval_pvars \<alpha> (sub_pvars R vas (vb # vbs)) = eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> (vb # vbs)"
      proof (cases "b = \<zero>")
        case *: True
        then show ?thesis
        proof -
          from * have "eval_pvars \<alpha> (sub_pvars R vas (vb # vbs)) = eval_pvars \<alpha> (sub_pvars R vas vbs)"
            using sub_pvars.simps(2) tu by auto
          moreover
          from * have "eval_pvars \<alpha> (vb # vbs) = eval_pvars \<alpha> vbs"
          proof -
            have "eval_pvars \<alpha> ((x,b)#vbs) = \<zero> \<oplus> eval_pvars \<alpha> vbs"
              using carr eval_pvars.simps(2) l_null * by auto
            also have "\<dots> = eval_pvars \<alpha> vbs"
              using carr l_zero by auto
            finally show ?thesis using tu by auto
          qed
          ultimately show ?thesis using IH by auto
        qed
      next
        case *: False
        then show ?thesis
        proof -
          have times_carr: "b \<otimes> \<alpha> x \<in> carrier R" using carr by auto
          have vas_carr: "eval_pvars \<alpha> vas \<in> carrier R"
            using wf_eval_pvars[OF assms(1) assms(2)].


          have "eval_pvars \<alpha> (sub_pvars R vas (vb # vbs)) = \<ominus>(b \<otimes> \<alpha> x) \<oplus> eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> vbs"
          proof -
            have "eval_pvars \<alpha> (sub_pvars R vas (vb # vbs)) = eval_pvars \<alpha> (sub_pvars R (sub_var R vas x b) vbs)"
              using * tu by auto
            also have "\<dots> = \<ominus>b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> (sub_pvars R vas vbs)"
              using sub_pvars_sub_var_sound[OF assms(1) carr(1) assms(2) wf_vbs].
            also have "\<dots> = \<ominus>(b \<otimes> \<alpha> x) \<oplus> eval_pvars \<alpha> (sub_pvars R vas vbs)"
            proof -
              have "eval_pvars \<alpha> (sub_pvars R vas vbs) \<in> carrier R"
                using wf_eval_pvars[OF assms(1) wf_sub_pvars[OF assms(2) wf_vbs]].
              then show ?thesis using carr(1,3) l_minus by presburger
            qed
            finally show ?thesis using IH times_carr carr(2) vas_carr by algebra
          qed
          moreover
          have "eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> (vb # vbs) = \<ominus>(b \<otimes> \<alpha> x) \<oplus> eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> vbs"
          proof -
            have "eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> (vb # vbs) = eval_pvars \<alpha> vas \<ominus> (b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vbs)"
              using tu by auto
            also have "\<dots> = eval_pvars \<alpha> vas \<oplus> \<ominus> (b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vbs)"
              using minus_eq by auto
            also have "\<dots> = eval_pvars \<alpha> vas \<oplus> (\<ominus>(b \<otimes> \<alpha> x) \<oplus> \<ominus>eval_pvars \<alpha> vbs)"
              using minus_add[OF times_carr carr(2)] by auto
            also have "\<dots> = \<ominus>(b \<otimes> \<alpha> x) \<oplus> eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> vbs"
              using carr(2) times_carr vas_carr by algebra
            finally show ?thesis.
          qed
          ultimately show ?thesis by auto
        qed
      qed
    qed
  qed
qed






lemma sub_poly_sound:
  assumes wf_ass: "wf_ass R \<alpha>"
    and wf_p: "wf_lpoly R p" 
    and wf_q: "wf_lpoly R q" 
  shows "eval_lpoly \<alpha> (sub_lpoly R p q) = eval_lpoly \<alpha> p \<ominus> eval_lpoly \<alpha> q"
proof (cases p)
  case pl: (LPoly a vas)
  show ?thesis
  proof (cases q)
    case ql: (LPoly b vbs)
    then show ?thesis
    proof -

      have wfs: "a \<in> carrier R" "b \<in> carrier R" "wf_pvars R vas" "wf_pvars R vbs"
                "eval_pvars \<alpha> vas \<in> carrier R" "eval_pvars \<alpha> vbs \<in> carrier R"
        using wf_p wf_q pl ql wf_eval_pvars[OF wf_ass] by auto

      have "sub_lpoly R p q = LPoly (a \<ominus>\<ominus> b) (sub_pvars R vas vbs)"
        using pl ql by auto
      moreover
      have "eval_pvars \<alpha> (sub_pvars R vas vbs) = eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> vbs"
        using sub_pvars_sound[OF wf_ass wfs(3,4)].
      ultimately
      have "eval_lpoly \<alpha> (sub_lpoly R p q) = (a \<ominus>\<ominus> b) \<oplus> (eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> vbs)"
        by auto
      also have "\<dots> = (a \<ominus> b) \<oplus> (eval_pvars \<alpha> vas \<ominus> eval_pvars \<alpha> vbs)"
        using wfs(1,2) by auto
      also have "\<dots> = (a \<oplus> eval_pvars \<alpha> vas) \<ominus> (b \<oplus> eval_pvars \<alpha> vbs)"
        using wfs by algebra
      also have "\<dots> = eval_lpoly \<alpha> p \<ominus> eval_lpoly \<alpha> q"
        using pl ql by auto
      finally show ?thesis.
    qed
  qed
qed



end



locale lin_poly_inter = strictly_ordered_ring +
  fixes pI :: "'f \<times> nat \<Rightarrow> 'a list \<times> 'a" 
  assumes pI: "\<And> f n cs c. pI (f,n) = (cs,c) 
    \<Longrightarrow> set (c # cs) \<subseteq> carrierR R \<and> length cs = n \<and> set (c#cs) \<inter> carrierS R \<noteq> {}" 
begin




lemma wf_lpoly_of_term[simp,intro]: "wf_lpoly R (evalp R pI t)" 
proof (induct t)
  case (Fun f ts)
  obtain cs c where pif: "pI (f,length ts) = (cs, c)" by force
  from pI[OF this]
  have pi: "c \<in> carrier R" "set cs \<subseteq> carrier R" "length cs = length ts"
    using carrierR_sub_carrier by auto
  from Fun show ?case unfolding Ip_def[of R pI f] eval_term.simps length_map pif split using pi
  proof (intro wf_list_sum_poly ballI, clarsimp, goal_cases)
    case (1 p)
    from this(1) \<open>length cs = length ts\<close> consider (c) "p = c_lpoly c" 
      | (arg) c t where "(c,t) \<in> set (zip cs ts)" "p = mul_lpoly R c (Ip R pI\<lbrakk>t\<rbrakk>vpoly R)" 
      by (force simp: set_conv_nth)
    thus ?case
    proof cases
      case c
      with 1(2-) show ?thesis by (auto simp: wf_pvars_def)
    next
      case (arg c t)
      from arg(1) 1 have wf_arg: "wf_lpoly R (Ip R pI\<lbrakk>t\<rbrakk>vpoly R)" by (metis in_set_zipE)
      from arg(1) \<open>set cs \<subseteq> carrier R\<close> have wf_c: "c \<in> carrier R" 
        by (meson in_set_zipE subsetD)
      show ?thesis unfolding arg(2) using wf_c wf_arg by (rule wf_mul_lpoly)
    qed
  qed
qed auto
      

lemma eval_term_I_Ip: assumes "wf_ass R \<alpha>" 
  shows "I R pI\<lbrakk>t\<rbrakk>\<alpha> = eval_lpoly  \<alpha> (evalp R pI t)" 
proof (induct t)
  case (Var x)
  from assms[unfolded wf_ass_def] have "\<alpha> x \<in> carrier R" by auto
  thus ?case by auto
next
  case (Fun f ts)

  have \<alpha>_carr: "range \<alpha> \<subseteq> carrier R" using assms by (simp add: wf_ass_def)

  obtain cs c where pif: "pI (f,length ts) = (cs, c)" by force
  from pI[OF this]
  have pi: "c \<in> carrier R" "set cs \<subseteq> carrier R" "length cs = length ts"
    using carrierR_sub_carrier by auto
  show ?case unfolding eval_term.simps I_def[of R pI f] Ip_def[of R pI f] length_map pif split
  proof (subst eval_lpoly_list_sum[OF _ \<alpha>_carr], goal_cases)
    case 1
    show ?case using pi 
      by (auto simp: wf_pvars_def intro!: wf_mul_lpoly dest: set_zip_leftD)
        (auto dest!: set_zip_rightD)
  next
    case 2
    have "map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs (map (\<lambda>s. I R pI\<lbrakk>s\<rbrakk>\<alpha>) ts)) =
      map (\<lambda>x. eval_lpoly \<alpha> (mul_lpoly R (fst x) (snd x)))
        (zip cs (map (evalp R pI)  ts))" (is "?ls = ?rs") 
    proof (intro nth_equalityI, unfold length_map, force, goal_cases)
      case (1 i)
      with pi have i: "i < length ts" "i < length cs" by auto
      have ls: "?ls ! i = cs ! i \<otimes> I R pI\<lbrakk>ts ! i\<rbrakk>\<alpha>" using i by auto
      have rs: "?rs ! i = eval_lpoly \<alpha> (mul_lpoly R (cs ! i) (evalp R pI (ts ! i)))" using i by auto
      from i have ti: "ts ! i \<in> set ts" by auto
      show "?ls ! i = ?rs ! i" unfolding ls rs Fun[OF ti]
        by (rule eval_lpoly_mul[symmetric, OF _ wf_lpoly_of_term \<alpha>_carr], insert i pi, auto)
    qed
    thus ?case by (simp add: pi o_def)
  qed
qed
        




lemma eval_rule_I_Ip: assumes "wf_ass R \<alpha>" 
  shows "I R pI\<lbrakk>l\<rbrakk>\<alpha> \<ominus> I R pI\<lbrakk>r\<rbrakk>\<alpha> = eval_lpoly \<alpha> (evalp_rule R pI l r)"
proof -
  have "I R pI\<lbrakk>l\<rbrakk>\<alpha> = eval_lpoly \<alpha> (evalp R pI l)" "I R pI\<lbrakk>r\<rbrakk>\<alpha> = eval_lpoly \<alpha> (evalp R pI r)"
    using eval_term_I_Ip assms by auto
  then have "I R pI\<lbrakk>l\<rbrakk>\<alpha> \<ominus> I R pI\<lbrakk>r\<rbrakk>\<alpha> = eval_lpoly \<alpha> (evalp R pI l) \<ominus> eval_lpoly \<alpha> (evalp R pI r)"
    by auto
  also have "\<dots> = eval_lpoly \<alpha> (sub_lpoly R (evalp R pI l) (evalp R pI r))"
    using sub_poly_sound[OF assms(1)] by auto
  finally show ?thesis unfolding evalp_rule_def by auto
qed





lemma eval_pvars_sound_carrierR:
  assumes "range \<alpha> \<subseteq> carrierR R" "set (coeffs_of_pvars_better ps) \<subseteq> carrierR R"
  shows "eval_pvars \<alpha> ps \<in> carrierR R"
  using assms(2)
proof (induction ps)
  case Nil
  then show ?case using zero_carrierR by auto
next
  case (Cons p ps)
  then show ?case
  proof (cases p)
    case (Pair x xp)
    then show ?thesis
    proof -
      from Cons.prems have "set (coeffs_of_pvars_better ps) \<subseteq> carrierR R"
        unfolding coeffs_of_pvars_better_def by auto
      then have IH: "eval_pvars \<alpha> ps \<in> carrierR R" using Cons.IH by auto

      have carrR: "xp \<in> carrierR R" "\<alpha> x \<in> carrierR R"
        using assms(1) Cons.prems[unfolded coeffs_of_lpoly_better.simps coeffs_of_pvars_better_def]
              Pair
        by auto

      have carr: "xp \<in> carrier R" "\<alpha> x \<in> carrier R" "eval_pvars \<alpha> ps \<in> carrier R"
      proof -
        show "xp \<in> carrier R" using carrR carrierR_sub_carrier by auto
        show "\<alpha> x \<in> carrier R" using carrR carrierR_sub_carrier by auto
        from assms(1) have wf_ass: "wf_ass R \<alpha>" using carrierR_sub_carrier by (simp add: wf_ass_def)
        have wf_p\<^sub>is: "wf_pvars R ps"
          using Cons.prems[unfolded coeffs_of_pvars_better_def]
                carrierR_sub_carrier wf_pvars_def
          by fastforce
        show "eval_pvars \<alpha> ps \<in> carrier R " using wf_eval_pvars[OF wf_ass wf_p\<^sub>is].
      qed

      have "eval_pvars \<alpha> (p # ps) = xp \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> ps"
        using Pair by auto
      then show ?thesis using plus_carrierR[OF _ IH] mult_carrierR[OF carrR] by auto
    qed
  qed
qed


lemma eval_lpoly_sound_carrierR:
  assumes "range \<alpha> \<subseteq> carrierR R" "set (coeffs_of_lpoly_better lp) \<subseteq> carrierR R"
  shows "eval_lpoly \<alpha> lp \<in> carrierR R"
  unfolding eval_lpoly.simps
proof (cases lp)
  case (LPoly p\<^sub>0 p\<^sub>is)
  then show ?thesis
  proof -
    have r: "p\<^sub>0 \<in> carrierR R" "set (coeffs_of_pvars_better p\<^sub>is) \<subseteq> carrierR R"
      using assms(2) LPoly by auto
    moreover
    have "eval_pvars \<alpha> p\<^sub>is \<in> carrierR R" using eval_pvars_sound_carrierR[OF assms(1) r(2)].
    ultimately show "eval_lpoly \<alpha> lp \<in> carrierR R" using plus_carrierR LPoly by auto
  qed
qed



lemma eval_pvars_sound_carrierMono:
  assumes "range \<alpha> \<subseteq> carrierS R" "set (coeffs_of_pvars_better ps) \<subseteq> carrierR R"
          "\<exists>p \<in> set ps. snd p \<in> carrierMono R"
        shows "eval_pvars \<alpha> ps \<in> carrierMono R"
proof -
  from assms(3) obtain p bef aft where p: "ps = bef @ p # aft" "snd p \<in> carrierMono R"
    by (meson split_list)
  from assms(2) p(1) have ba: "set (coeffs_of_pvars_better bef) \<subseteq> carrierR R"
                              "set (coeffs_of_pvars_better aft) \<subseteq> carrierR R"
    unfolding coeffs_of_pvars_better_def by auto

  have wf: "wf_ass R \<alpha>" "wf_pvars R bef" "wf_pvars R [p]" "wf_pvars R aft"
    unfolding wf_ass_def wf_pvars_def
    using assms(1) ba[unfolded coeffs_of_pvars_better_def] carrierR_sub_carrier
          carrierS_sub_carrier p(2) carrierMono_sub_carrier
    by auto
  then show ?thesis
  proof (cases p)
    case (Pair x xp)
    then show ?thesis
    proof -
      have carr: "xp \<in> carrier R" "\<alpha> x \<in> carrier R" "\<alpha> x \<in> carrierS R"
        using assms(1) carrierS_sub_carrier p(2) carrierMono_sub_carrier Pair by auto

      from ba have r1: "eval_pvars \<alpha> bef \<in> carrierR R" "eval_pvars \<alpha> aft \<in> carrierR R"
        using eval_pvars_sound_carrierR subset_trans[OF assms(1) carrierS_sub_carrierR] by auto
      then have c2: "eval_pvars \<alpha> bef \<in> carrier R"
        using carrierR_sub_carrier by auto
      have r2: "eval_pvars \<alpha> [p] \<in> carrierMono R"
        using carr carrierMono_times_left_closed p(2) eval_pvars.simps r_zero m_closed
        by (simp add: Pair)

      from r1 r2 have r3: "eval_pvars \<alpha> [p] \<oplus> eval_pvars \<alpha> aft \<in> carrierMono R"
        using plus_carrierMono2 by auto
      then have r4: "eval_pvars \<alpha> bef \<oplus> (eval_pvars \<alpha> [p] \<oplus> eval_pvars \<alpha> aft) \<in> carrierMono R"
      proof -
        have "eval_pvars \<alpha> bef \<oplus> (eval_pvars \<alpha> [p] \<oplus> eval_pvars \<alpha> aft) =
              eval_pvars \<alpha> [p] \<oplus> eval_pvars \<alpha> aft \<oplus> eval_pvars \<alpha> bef"
          using a_comm[OF c2] in_mono[OF carrierMono_sub_carrier] r3 by auto
        moreover
        have "eval_pvars \<alpha> [p] \<oplus> eval_pvars \<alpha> aft \<oplus> eval_pvars \<alpha> bef \<in> carrierMono R"
          using r3 plus_carrierMono2 r1 by auto
        ultimately show ?thesis by auto
      qed
        
      

      have "eval_pvars \<alpha> ps = eval_pvars \<alpha> bef \<oplus> eval_pvars \<alpha> (p#aft)"
        using wf wf_pvars_split[OF wf(3,4)] eval_pvars_split p(1) by auto
      also have "\<dots> = eval_pvars \<alpha> bef \<oplus> (eval_pvars \<alpha> [p] \<oplus> eval_pvars \<alpha> aft)"
        using wf eval_pvars_split by fastforce
      finally show ?thesis using r4 by auto
    qed
  qed
qed


lemma eval_lpoly_sound_carrierMono:
  assumes "range \<alpha> \<subseteq> carrierS R" "set (coeffs_of_lpoly_better lp) \<subseteq> carrierR R"
          "\<exists> p \<in> set (coeffs_of_lpoly_better lp). p \<in> carrierMono R"
        shows "eval_lpoly \<alpha> lp \<in> carrierMono R"
proof (cases lp)
  case (LPoly p\<^sub>0 p\<^sub>is)
  then show ?thesis
  proof -
    have triv: "p\<^sub>0 \<in> carrierR R" "set (coeffs_of_pvars_better p\<^sub>is) \<subseteq> carrierR R"
               "range \<alpha> \<subseteq> carrierR R" "wf_ass R \<alpha>"
      unfolding wf_ass_def
      using LPoly assms carrierS_sub_carrierR carrierR_sub_carrier by auto
    have "\<exists> p \<in> {p\<^sub>0} \<union> set (map snd p\<^sub>is). p \<in> carrierMono R"
      using assms(3) LPoly by (simp add: coeffs_of_pvars_better_def)
    then have as: "p\<^sub>0 \<in> carrierMono R \<or> (\<exists>p \<in> set (map snd p\<^sub>is). p \<in> carrierMono R)"
      by auto
    show ?thesis
    proof (cases "p\<^sub>0 \<in> carrierMono R")
      case True
      then show ?thesis using LPoly plus_carrierMono2[OF _ eval_pvars_sound_carrierR[OF triv(3,2)]]
        by auto
    next
      case False
      then show ?thesis
      proof -
        from False as have "(\<exists> p \<in> set p\<^sub>is. snd p \<in> carrierMono R)" by auto
        then have r1: "eval_pvars \<alpha> p\<^sub>is \<in> carrierMono R"
          using eval_pvars_sound_carrierMono[OF assms(1) triv(2)] by auto
        then have r2: "eval_pvars \<alpha> p\<^sub>is \<in> carrier R"
          using carrierMono_sub_carrier by auto
        from assms(2)[unfolded coeffs_of_lpoly_better.simps] LPoly have r3: "p\<^sub>0 \<in> carrierR R" by auto
        then have r4: "p\<^sub>0 \<in> carrier R"
          using carrierR_sub_carrier by auto
        have "eval_lpoly \<alpha> (LPoly p\<^sub>0 p\<^sub>is) = p\<^sub>0 \<oplus> eval_pvars \<alpha> p\<^sub>is"
          unfolding eval_lpoly.simps by (rule refl)
        also have "\<dots> = eval_pvars \<alpha> p\<^sub>is \<oplus> p\<^sub>0"
          by (rule a_comm[OF r4 r2])
        finally show ?thesis using plus_carrierMono2[OF r1 r3] LPoly by auto
      qed
    qed
  qed
qed



lemma eval_carrierS[simp]:
  assumes "range \<alpha> \<subseteq> carrierS R"
  shows "I R pI\<lbrakk>t\<rbrakk>\<alpha> \<in> carrierS R"
proof (induction t)
  case (Var x)
  then show ?case using assms by auto
next
  case (Fun x1a x2)
  then show ?case
  proof (cases "pI (x1a, length x2)")
    case (Pair cs c)
    then show ?thesis
    proof-
      have as: "length cs = length [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]"
        using pI[OF Pair] by auto
      have IH: "set [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2] \<subseteq> carrierS R" using Fun.IH by auto
      then have "set [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2] \<subseteq> carrierR R" using carrierS_sub_carrierR by auto
      moreover
      have "set (c#cs) \<subseteq> carrierR R" using Pair pI by auto
      ultimately
      have "set (c#map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) \<subseteq> carrierR R"
        using mult_carrierR[of "fst _" "snd _"] zip_fst[of _ cs] zip_snd[of _ _ "[I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]"]
        by (smt (verit, del_insts) imageE insert_subset list.set_map list.simps(15) subset_iff)
      moreover
      have "set (c#map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) \<inter> carrierS R \<noteq> {}"
      proof -
        from pI have r1: "set (c#cs) \<inter> carrierS R \<noteq> {}" using Pair by auto
        show ?thesis
        proof (cases "c \<in> carrierS R")
          case True
          then show ?thesis by auto
        next
          case False
          then show ?thesis
          proof -
            obtain c\<^sub>1 where c\<^sub>1_p: "c\<^sub>1 \<in> set cs" "c\<^sub>1 \<in> carrierS R"
              using False r1 by auto
            then obtain i where i_p: "cs ! i = c\<^sub>1" "i < length cs"
              by (meson in_set_conv_nth)
            then have "[I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2] ! i \<in> carrierS R"
              using IH as by force
            then have "fst ((zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]) ! i) \<otimes> snd ((zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]) ! i) \<in> carrierS R"
              using mult_carrierS i_p as c\<^sub>1_p(2) by auto
            then have "(map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) ! i \<in> carrierS R"
              using i_p as by auto
            then have "set (map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) \<inter> carrierS R \<noteq> {}"
              using i_p as
              by (metis (no_types, lifting) disjoint_iff length_map map_fst_zip nth_mem)
            then show ?thesis using i_p as by auto
          qed
        qed
      qed
      ultimately have "list_sum R (c # map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) \<in> carrierS R"
        by (rule list_sum_carrierS)
      then show ?thesis unfolding I_def using Pair by auto
    qed
  qed
qed


lemma eval_carrierR[simp]:
  assumes "range \<alpha> \<subseteq> carrierR R"
  shows "I R pI\<lbrakk>t\<rbrakk>\<alpha> \<in> carrierR R"
proof (induction t)
  case (Var x)
  then show ?case using assms by auto
next
  case (Fun x1a x2)
  then show ?case
  proof (cases "pI (x1a, length x2)")
    case (Pair cs c)
    then show ?thesis
    proof-
      have "set (c#cs) \<subseteq> carrierR R" using Pair pI by auto
      moreover
      have "set [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2] \<subseteq> carrierR R" using Fun.IH by auto
      ultimately
      have "set (c#map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) \<subseteq> carrierR R"
        using mult_carrierR[of "fst _" "snd _"] zip_fst[of _ cs] zip_snd[of _ _ "[I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]"]
        by (smt (verit, del_insts) imageE insert_subset list.set_map list.simps(15) subset_iff)
      then have "list_sum R (c # map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) \<in> carrierR R"
        by (rule list_sum_carrierR)
      then show ?thesis unfolding I_def using Pair by auto
    qed
  qed
qed



lemma eval_carrier[simp]:
  assumes "range \<alpha> \<subseteq> carrier R"
  shows "I R pI\<lbrakk>t\<rbrakk>\<alpha> \<in> carrier R"
proof (induction t)
  case (Var x)
  then show ?case using assms by auto
next
  case (Fun x1a x2)
  then show ?case
  proof (cases "pI (x1a, length x2)")
    case (Pair cs c)
    then show ?thesis
    proof-
      have "set (c#cs) \<subseteq> carrier R" using Pair pI subset_trans[OF _ carrierR_sub_carrier, of "set (c#cs)"]
        by auto
      moreover
      have "set [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2] \<subseteq> carrier R" using Fun.IH by auto
      ultimately
      have "set (c#map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) \<subseteq> carrier R"
        using m_closed[of "fst _" "snd _"] zip_fst[of _ cs] zip_snd[of _ _ "[I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2]"]
        by (smt (verit, ccfv_threshold) imageE insert_subset list.set_map list.simps(15) subset_iff)
      then have "list_sum R (c # map (\<lambda> ca. fst ca \<otimes> snd ca) (zip cs [I R pI\<lbrakk>s\<rbrakk>\<alpha>. s \<leftarrow> x2])) \<in> carrier R"
        by (rule wf_list_sum)
      then show ?thesis unfolding I_def using Pair by auto
    qed
  qed
qed





 
definition S where "S = restrict {(x,y) . x \<ominus> y \<in> carrierMono R} (carrierS R)"


definition NS where "NS = restrict {(x,y) . x \<succeq> y} (carrierS R)" 

sublocale wf_algebra NS S "carrierS R" "I R pI"
proof
  show "refl_on (carrierS R) NS" unfolding NS_def refl_on_def restrict_def using carrierS_sub_carrier
    by (auto intro!: geq_refl)
  show "NS O S \<subseteq> S" unfolding NS_def S_def restrict_def using carrierMono_left_mono carrierS_sub_carrier
    by blast    
  show "S O NS \<subseteq> S" unfolding NS_def S_def restrict_def using carrierMono_right_mono carrierS_sub_carrier
    by blast
  show "S \<subseteq> NS" unfolding S_def NS_def restrict_def using gt_imp_ge[OF carrierMono_gt] carrierMono_sub_carrierR
  carrierS_sub_carrier by blast
  show "trans_on (carrierS R) NS" unfolding trans_on_def NS_def restrict_def 
    using geq_trans carrierS_sub_carrier by blast
  show "trans_on (carrierS R) S" unfolding trans_on_def S_def restrict_def 
    using carrierMono_trans carrierS_sub_carrier by blast
  show "SN_on S (carrierS R)"
  proof -
    have "restrict {(x,y) . x \<ominus> y \<in> carrierMono R} (carrierS R) \<subseteq> restrict {(x, y). x \<succ> y} (carrierS R)"
      (is "?l \<subseteq> _")
      unfolding restrict_def using carrierS_sub_carrier carrierMono_gt
      by ((simp add: subset_iff), blast)
    also have "\<dots> \<subseteq> restrict {(x, y). x \<succ> y} (carrierR R)" (is "_ \<subseteq> ?r")
      unfolding restrict_def using carrierS_sub_carrierR by auto
    finally have res: "?l \<subseteq> ?r" by auto
    show ?thesis unfolding S_def using SN_on_mono[OF gt_SN res] SN_on_subset2[OF carrierS_sub_carrierR]
      by auto
  qed
  {
    fix as f
    assume as: "set as \<subseteq> carrierS R"
    obtain c cs where pIf: "pI (f, length as) = (cs,c)" by force
    note pi = pI[OF pIf]
    show "I R pI f as \<in> carrierS R" 
      unfolding I_def split pIf
    proof (intro list_sum_carrierS)
      show "set (c # map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs as)) \<subseteq> carrierR R" 
        using pi as
              set_mp[OF carrierS_sub_carrierR]
        by (auto intro!: mult_carrierR dest: set_zip_bothD)
      show "set (c # map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs as)) \<inter> carrierS R \<noteq> {}"
      proof (cases "c \<in> carrierS R")
        case True
        then show ?thesis by auto
      next
        case False
        then show ?thesis
        proof -
          obtain ci where ci_p: "ci \<in> set cs" "ci \<in> carrierS R"
            using pi False by auto
          then obtain i where "cs ! i = ci" "i < length cs"
            using in_set_conv_nth[of ci cs] by auto
          then have "i < length as"
            using pi by auto
          then obtain ai where "ai \<in> set as" "as ! i = ai"
            using nth_mem by auto
          then have ai_p: "ai \<in> carrierS R" using as by auto
          from \<open>cs ! i = ci\<close> \<open>as ! i = ai\<close> \<open>i < length cs\<close> \<open>i < length as\<close>
          have "(zip cs as) ! i = (ci, ai)" by auto
          moreover
          have "i < length (zip cs as)" using \<open>i < length cs\<close> \<open>i < length as\<close> by auto
          ultimately
          have "(map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs as)) ! i = (\<lambda>ca. fst ca \<otimes> snd ca) (ci, ai)"
            using nth_map by auto
          also have "\<dots> = ci \<otimes> ai" by auto
          also have "\<dots> \<in> carrierS R"
            using ci_p ai_p mult_carrierS by auto
          finally have "(map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs as)) ! i \<in> carrierS R"
            by auto
          moreover
          have "i < length (map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs as))"
            using \<open>i < length (zip cs as)\<close> by auto
          ultimately
          show ?thesis
            by (meson disjoint_iff list.set_intros(2) nth_mem)
        qed
      qed
    qed
  } note I_in_carr = this
  {
    fix a b bef aft f
    assume *: "a \<in> carrierS R" "b \<in> carrierS R" 
       "set (bef @ aft) \<subseteq> carrierS R" 
       "(a,b) \<in> NS" 
    let ?n = "Suc (length bef) + length aft" 
    
    obtain c cs where pif: "pI (f,?n) = (cs,c)" by force
    let ?i = "length bef" 
    from pI[OF pif]
    have len_cs: "length cs = ?n" and csR: "set cs \<subseteq> carrierR R" and c: "c \<in> carrierR R" by auto
    from c have c_carr: "c \<in> carrier R" using carrierR_sub_carrier by auto
    have len: "length (bef @ a # aft) = ?n" for a by auto
    define list where "list a = (bef @ undefined # aft)[?i := a]" for a 
    have len_list: "length (list a) = length cs" for a unfolding list_def len_cs by auto
    have i: "?i < length cs" unfolding len_cs by auto
    define cs1 where "cs1 = take ?i cs" 
    define csi where "csi = cs ! ?i" 
    define cs2 where "cs2 = drop (Suc ?i) cs" 
    define l1 where "l1 = map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs1 bef)" 
    define l2 where "l2 = map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs2 aft)" 
    have "set (zip cs1 bef) \<subseteq> carrierR R \<times> carrierR R" unfolding cs1_def using * csR 
        carrierS_sub_carrierR
      by (auto dest!: set_zip_bothD in_set_takeD)
    hence l1: "set l1 \<subseteq> carrierR R" unfolding l1_def using mult_carrierR by auto
    then have l1_carr: "set l1 \<subseteq> carrier R" using carrierR_sub_carrier by auto
    have "set (zip cs2 aft) \<subseteq> carrierR R \<times> carrierR R" unfolding cs2_def using * csR 
        carrierS_sub_carrierR
      by (auto dest!: set_zip_bothD in_set_dropD)
    hence l2: "set l2 \<subseteq> carrierR R" unfolding l2_def using mult_carrierR by auto
    then have l2_carr: "set l2 \<subseteq> carrier R" using carrierR_sub_carrier by auto
    define l where "l = list_sum R ((c # l1) @ l2)" 
    have l: "l \<in> carrierR R" unfolding l_def using c l1 l2
          list_sum_closed_submonoid[of "carrierR R" R "(c#l1) @ l2"] carrierR_submonoid by auto
    then have l_carr: "l \<in> carrier R" using carrierR_sub_carrier by auto
    have csi: "csi \<in> carrierR R" unfolding csi_def using i csR by auto
    then have csi_carr: "csi \<in> carrier R" using carrierR_sub_carrier by auto

    from i have cs: "cs = cs1 @ csi # cs2" unfolding cs1_def csi_def cs2_def by (rule id_take_nth_drop)
    have zip: "zip cs (bef @ a # aft) = zip cs1 bef @ (csi,a) # zip cs2 aft" for a 
      unfolding cs unfolding cs1_def cs2_def csi_def  using i by auto
    have id: "map (\<lambda>ca. fst ca \<otimes> snd ca) (zip cs (bef @ a # aft)) = 
      l1 @ csi \<otimes> a # l2" for a unfolding zip l1_def l2_def by simp
    {
      fix a
      assume a: "a \<in> carrier R" 
      have "I R pI f (bef @ a # aft) = list_sum R ((c # l1) @ csi \<otimes> a # l2)"
        unfolding I_def len pif split id by auto
      also have "\<dots> = csi \<otimes> a \<oplus> l" unfolding l_def
        apply (subst (1 2) list_sum_append)
        subgoal using c l1 carrierR_sub_carrier by auto
        subgoal using l2 carrierR_sub_carrier by auto
        subgoal using csi a l2 carrierR_sub_carrier by auto
        subgoal using a c_carr csi_carr wf_list_sum[OF l1_carr] wf_list_sum[OF l2_carr]
          by simp algebra
        done
      finally have "I R pI f (bef @ a # aft) = csi \<otimes> a \<oplus> l" .
    } note id = this
    from * have a: "a \<in> carrier R"
      and b: "b \<in> carrier R" 
      and ab: "a \<succeq> b" unfolding NS_def restrict_def
      using carrierS_sub_carrierR carrierR_sub_carrier by auto

    show "(I R pI f (bef @ a # aft), I R pI f (bef @ b # aft)) \<in> NS"
      unfolding NS_def restrict_def
    proof (standard, unfold split, intro conjI CollectI; (unfold split)?)
      show "I R pI f (bef @ a # aft) \<in> carrierS R" by (intro I_in_carr, insert *, auto)
      show "I R pI f (bef @ b # aft) \<in> carrierS R" by (intro I_in_carr, insert *, auto)
      show "I R pI f (bef @ a # aft) \<succeq> I R pI f (bef @ b # aft)" 
        unfolding id[OF a] id[OF b]
        by (rule plus_left_mono[OF times_right_mono], insert a b csi csi_carr ab l_carr, auto)
    qed
  }
qed


lemma S_A_O_NS_A: "S_A O NS_A \<subseteq> S_A"
  unfolding S_A_def NS_A_def
  using compat_S_NS by auto

lemma NS_A_O_S_A: "NS_A O S_A \<subseteq> S_A"
  unfolding S_A_def NS_A_def
  using compat_NS_S by auto

lemma S_A_O_S_A: "S_A O S_A \<subseteq> S_A"
proof
  fix x y :: "('f, 'v) term"
  assume "(x,y) \<in> S_A O S_A"
  then obtain x' where "(x, x') \<in> S_A" "(x', y) \<in> S_A"
    by auto
  then show "(x,y) \<in> S_A" using S_A_S_A by auto
qed

lemma NS_A_O_NS_A: "NS_A O NS_A \<subseteq> NS_A"
proof
  fix x y :: "('f, 'v) term"
  assume "(x,y) \<in> NS_A O NS_A"
  then obtain x' where "(x, x') \<in> NS_A" "(x', y) \<in> NS_A"
    by auto
  then show "(x, y) \<in> NS_A" using NS_A_NS_A by auto
qed




end

locale mono_lin_poly_inter = lin_poly_inter R pI for
  R and pI :: "'f \<times> nat \<Rightarrow> 'a list \<times> 'a" +
  assumes strict_pI: "\<And> f n cs c. pI (f,n) = (cs,c) 
    \<Longrightarrow> set (cs) \<subseteq> carrierS R" 
begin


sublocale mono_wf_algebra NS S "carrierS R" "I R pI"
proof 
  {
    fix a b bef aft f
    assume a_carr: "a \<in> carrierS R" and
           b_carr: "b \<in> carrierS R" and
       befaf_carr: "set (bef@aft) \<subseteq> carrierS R" and
               ab: "(a,b) \<in> S"

    let ?n = "length bef + length aft + 1"
    have n: "?n = length (bef@a#aft)" "?n = length (bef@b#aft)"
      by auto
    obtain c cs where csc_p: "pI (f, ?n) = (cs,c)" by fastforce
    let ?i = "length bef"

    have tds: "take ?i (bef@a#aft) = bef"       "take ?i (bef@b#aft) = bef"
              "drop ?i (bef@a#aft) = a#aft"     "drop ?i (bef@b#aft) = b#aft"
              "drop (?i + 1) (bef@a#aft) = aft" "drop (?i + 1) (bef@b#aft) = aft"
      by auto

    have wf_i: "?i < length cs"
      using csc_p pI by auto

    have carr1: "c \<in> carrier R" "set cs \<subseteq> carrier R"
      using csc_p pI carrierR_sub_carrier
      by fastforce+
    have carr2: "set (bef@a#aft) \<subseteq> carrier R" "set (bef@b#aft) \<subseteq> carrier R"
      using befaf_carr a_carr b_carr carrierS_sub_carrier
      by auto

    define csi where "csi = cs ! ?i"
    define csl where "csl = take ?i cs"
    define csr where "csr = drop (?i + 1) cs"
    have cs_id: "cs = csl@csi#csr"
      unfolding csl_def csi_def csr_def using wf_i by (simp add: id_take_nth_drop) 
    define ml where "ml = map (\<lambda>ac. fst ac \<otimes>\<^bsub>R\<^esub> snd ac) (zip csl bef)"
    define mr where "mr = map (\<lambda>ac. fst ac \<otimes>\<^bsub>R\<^esub> snd ac) (zip csr aft)"

    have csi_carr: "csi \<in> carrier R"
      using cs_id carr1 by auto

    have times_carr: "csi \<otimes>\<^bsub>R\<^esub> a \<in> carrier R" "csi \<otimes>\<^bsub>R\<^esub> b \<in> carrier R"
      using csi_carr a_carr b_carr carrierS_sub_carrier by auto

    have map_carr: "set ml \<subseteq> carrier R" (is ?g1) "set mr \<subseteq> carrier R" (is ?g2)
    proof -
      {
        fix f s
        assume as: "(f,s) \<in> set (zip csl bef)"
        then have "f \<in> carrier R"
          using cs_id carr1 set_zip_bothD by fastforce
        moreover
        from as have "s \<in> carrier R"
          using carr2(1) set_zip_bothD by fastforce
        ultimately have "f \<otimes>\<^bsub>R\<^esub> s \<in> carrier R" by auto
      }
      then show ?g1  unfolding ml_def by auto
      {
        fix f s
        assume as: "(f,s) \<in> set (zip csr aft)"
        then have "f \<in> carrier R"
          using cs_id carr1 set_zip_bothD by fastforce
        moreover
        from as have "s \<in> carrier R"
          using carr2(1) set_zip_bothD by fastforce
        ultimately have "f \<otimes>\<^bsub>R\<^esub> s \<in> carrier R" by auto
      }
      then show ?g2  unfolding mr_def by auto
    qed

    from times_carr map_carr have times_carr2:
      "set ((csi \<otimes>\<^bsub>R\<^esub> a)#mr) \<subseteq> carrier R" "set ((csi \<otimes>\<^bsub>R\<^esub> b)#mr) \<subseteq> carrier R"
      by auto

    have "map (\<lambda>ac. fst ac \<otimes>\<^bsub>R\<^esub> snd ac) (zip cs (bef@a#aft)) = ml@(csi \<otimes>\<^bsub>R\<^esub> a)#mr" (is ?g1)
         "map (\<lambda>ac. fst ac \<otimes>\<^bsub>R\<^esub> snd ac) (zip cs (bef@b#aft)) = ml@(csi \<otimes>\<^bsub>R\<^esub> b)#mr" (is ?g2)
    proof -
      let ?mul = "\<lambda>ac. fst ac \<otimes>\<^bsub>R\<^esub> snd ac"
      have drcs: "drop ?i cs = csi#csr"
        unfolding csi_def csr_def
        by (simp add: Cons_nth_drop_Suc wf_i)

      have "take ?i (zip cs (bef@a#aft)) = zip csl bef"
           "take ?i (zip cs (bef@b#aft)) = zip csl bef"
        unfolding csl_def
        using take_zip[of ?i cs "bef@_#aft"] tds(1)
        by auto
      moreover
      have "drop ?i (zip cs (bef@a#aft)) = zip (csi#csr) (a#aft)"
           "drop ?i (zip cs (bef@b#aft)) = zip (csi#csr) (b#aft)"
        using drop_zip[of ?i cs "bef@_#aft"] tds(3,4) drcs
        by auto
      then have "drop ?i (zip cs (bef@a#aft)) = (csi, a)#zip csr aft"
                "drop ?i (zip cs (bef@b#aft)) = (csi, b)#zip csr aft"
        by auto
      moreover
      have "map ?mul (zip cs (bef@a#aft)) =
            map ?mul ((take ?i (zip cs (bef@a#aft)))@
                                       (drop ?i (zip cs (bef@a#aft))))" (is "?lh1 = _")
           "map ?mul (zip cs (bef@b#aft)) =
            map ?mul ((take ?i (zip cs (bef@b#aft)))@
                                       (drop ?i (zip cs (bef@b#aft))))" (is "?lh2 = _")
        using append_take_drop_id take_map drop_map by auto
      ultimately
      have "?lh1 = map ?mul ((zip csl bef)@(csi, a)#zip csr aft)"
           "?lh2 = map ?mul ((zip csl bef)@(csi, b)#zip csr aft)"
        by auto
      then have "?lh1 = (map ?mul (zip csl bef))@?mul (csi, a)#map ?mul (zip csr aft)"
                "?lh2 = (map ?mul (zip csl bef))@?mul (csi, b)#map ?mul (zip csr aft)"
        by auto
      then show ?g1 ?g2 unfolding ml_def mr_def by auto
    qed
    then
    have "I R pI f (bef@a#aft) = c \<oplus>\<^bsub>R\<^esub> list_sum R (ml@(csi \<otimes>\<^bsub>R\<^esub> a)#mr)" (is "?lh1 = _")
         "I R pI f (bef@b#aft) = c \<oplus>\<^bsub>R\<^esub> list_sum R (ml@(csi \<otimes>\<^bsub>R\<^esub> b)#mr)" (is "?lh2 = _")
      unfolding I_def using csc_p n by auto
    then have res1: "?lh1 = c \<oplus>\<^bsub>R\<^esub> list_sum R ml \<oplus>\<^bsub>R\<^esub> csi \<otimes>\<^bsub>R\<^esub> a \<oplus>\<^bsub>R\<^esub> list_sum R mr"
                    "?lh2 = c \<oplus>\<^bsub>R\<^esub> list_sum R ml \<oplus>\<^bsub>R\<^esub> csi \<otimes>\<^bsub>R\<^esub> b \<oplus>\<^bsub>R\<^esub> list_sum R mr"
      using list_sum_append times_carr2 map_carr(1) wf_list_sum
      by (simp add: a_assoc carr1(1))+


    have carrs: "list_sum R ml \<in> carrier R" "list_sum R mr \<in> carrier R" "c \<in> carrier R" "csi \<in> carrier R"
                "a \<in> carrier R" "b \<in> carrier R"
      using wf_list_sum[OF map_carr(1)] wf_list_sum[OF map_carr(2)] carr1(1)
            csi_carr set_mp[OF carrierS_sub_carrier a_carr] set_mp[OF carrierS_sub_carrier b_carr].



    from ab have "a \<ominus>\<^bsub>R\<^esub> b \<in> carrierMono R"
      unfolding S_def restrict_def by auto
    moreover
    from csc_p cs_id strict_pI have "csi \<in> carrierS R" by fastforce
    ultimately
    have "csi \<otimes>\<^bsub>R\<^esub> (a \<ominus>\<^bsub>R\<^esub> b) \<in> carrierMono R"
      by (rule carrierMono_times_right_closed)
    moreover
    from res1 have "?lh1 \<ominus>\<^bsub>R\<^esub> ?lh2 = csi \<otimes>\<^bsub>R\<^esub> (a \<ominus>\<^bsub>R\<^esub> b)"
      using carrs by algebra
    moreover
    have "?lh1 \<in> carrierS R" "?lh2 \<in> carrierS R" using I_A befaf_carr a_carr b_carr carrierS_sub_carrierR
      by (simp add: subset_iff)+
    ultimately
    show "(I R pI f (bef @ a # aft), I R pI f (bef @ b # aft)) \<in> S" unfolding S_def restrict_def by simp
  }
qed




end

lemma rstep_distrib: "rstep (R O S) \<subseteq> rstep R O rstep S"
proof
  fix x y :: "('a, 'b) term"
  assume "(x, y) \<in> rstep (R O S)"
  then obtain C l r and \<sigma> :: "('a,'b)subst" where lr: "x = C\<langle>l \<cdot> \<sigma>\<rangle>" "y = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l,r) \<in> R O S"
    by blast
  then obtain t where "(l,t) \<in> R" "(t,r) \<in> S"
    by auto
  then have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>t \<cdot> \<sigma>\<rangle>) \<in> rstep R" "(C\<langle>t \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep S"
    by auto
  then have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep R O rstep S"
    by auto
  then show "(x, y) \<in> rstep R O rstep S" using lr by auto
qed

abbreviation "LPI \<equiv> I" 
abbreviation "LPIp \<equiv> Ip" 
hide_const (open) I Ip
lemmas LPI_def = I_def
lemmas LPIp_def = Ip_def

end