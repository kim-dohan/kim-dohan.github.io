(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Non_Inf_Order
imports
  First_Order_Rewriting.Trs
  Knuth_Bendix_Order.Order_Pair
  "Abstract-Rewriting.SN_Order_Carrier"
begin

text \<open>We define non infinitesmal orders and related notions
  as in the CADE07 "Bounded Increase" paper.\<close>

text \<open>for monotonicity, we do not use 0, 1, -1, and 2 as in CADE07, but a dedicated datatype\<close>

datatype dependance = Ignore | Increase | Decrease | Wild

type_synonym 'f dep = "('f \<times> nat) \<Rightarrow> nat \<Rightarrow> dependance"

fun rel_dep :: "'a rel \<Rightarrow> dependance \<Rightarrow> 'a rel" (infix "^^^" 52) where
  "_ ^^^ Ignore = {}"
| "r ^^^ Increase = r"
| "r ^^^ Decrease = (r ^-1)"
| "r ^^^ Wild = (r^<->)"

lemma rel_dep_mono: "r1 \<subseteq> r2 \<Longrightarrow> r1 ^^^ k \<subseteq> r2 ^^^ k"
  by (cases k, auto)

fun invert_dep :: "dependance \<Rightarrow> dependance" where
  "invert_dep Increase = Decrease"
| "invert_dep Decrease = Increase"  
| "invert_dep d = d"
  
lemma rel_dep_invert_mono: "r1^-1 \<subseteq> r2 \<Longrightarrow> r1 ^^^ invert_dep k \<subseteq> r2 ^^^ k"
  by (cases k, auto)

text \<open>for compatibility (monotonicity) we only consider F-terms, not all terms as in CADE07\<close>

definition dep_compat :: "'f sig \<Rightarrow> ('f, 'v) term rel \<Rightarrow> 'f dep \<Rightarrow> bool" where
  "dep_compat F r \<pi> \<longleftrightarrow> (\<forall> f bef s t aft. \<Union>(funas_term ` ({s,t} \<union> set bef \<union> set aft)) \<subseteq> F \<longrightarrow> 
  {(s,t)} ^^^ \<pi> (f,Suc (length bef + length aft)) (length bef) \<subseteq> r \<longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> r)"

lemma dep_compatE[elim]: assumes dep: "dep_compat F r \<pi>" shows "funas_args_term (Fun f (bef @ s # aft)) \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow> 
  {(s,t)} ^^^ \<pi> (f,Suc (length bef + length aft)) (length bef) \<subseteq> r
  \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> r"
  unfolding funas_args_term_def
  by (rule dep[unfolded dep_compat_def, rule_format, of s t bef aft f], force+)

lemma dep_compatI[intro]: assumes "\<And> f bef s t aft. 
  \<lbrakk>\<And> u. u \<in> {s,t} \<union> set bef \<union> set aft \<Longrightarrow> funas_term u \<subseteq> F\<rbrakk> \<Longrightarrow>
  {(s,t)} ^^^ \<pi> (f,Suc (length bef + length aft)) (length bef) \<subseteq> r
  \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> r"
  shows "dep_compat F r \<pi>" 
  unfolding dep_compat_def
  by (intro allI impI, rule assms, auto)

text \<open>F-stability (closure under F-substitutions) is the same as in CADE07\<close>  

definition F_subst_closed :: "'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "F_subst_closed F r \<longleftrightarrow>
    (\<forall> \<sigma> s t. \<Union>(funas_term ` range \<sigma>) \<subseteq> F \<longrightarrow> (s,t) \<in> r \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> r)"

lemma F_subst_closedI[intro]:
  assumes "\<And> \<sigma> s t. \<Union>(funas_term ` range \<sigma>) \<subseteq> F \<Longrightarrow> (s,t) \<in> r \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> r"
  shows "F_subst_closed F r" using assms unfolding F_subst_closed_def by blast

lemma F_subst_closedD[elim]: "F_subst_closed F r \<Longrightarrow> \<Union>(funas_term ` range \<sigma>) \<subseteq> F \<Longrightarrow> (s,t) \<in> r \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> r"
  unfolding F_subst_closed_def by auto

lemma F_subst_closed_UNIV:
  "F_subst_closed F r \<Longrightarrow> F = UNIV \<Longrightarrow> subst.closed r" unfolding F_subst_closed_def
  using subst.closedI[of r] by auto

text \<open>a locale to have all nice properties together\<close>

locale non_inf_order = Order_Pair.order_pair S NS for S NS :: "'a rel" +
  assumes non_inf: "non_inf S"
begin

lemma chain_split: fixes f :: "'b seq" and m :: "'b \<Rightarrow> 'a" 
  assumes fS: "fS \<subseteq> {i. (m (f i), m (f (Suc i))) \<in> S}"
  and fB: "fB \<subseteq> {i. (m (f i), a) \<in> NS \<union> S}" 
  and decr: "\<And> i. (m (f i), m (f (Suc i))) \<in> NS \<union> S" 
  shows "(\<forall>\<^sub>\<infinity> j. j \<notin> fS) \<or> (\<forall>\<^sub>\<infinity> j. j \<notin> fB)"
proof (cases "(\<exists>\<^sub>\<infinity> i. i \<in> fS) \<and> (\<exists>\<^sub>\<infinity> i. i \<in> fB)")
  case False
  then show ?thesis unfolding INFM_nat_le MOST_nat_le by blast
next
  case True
  define g where "g = (\<lambda> i. m (f i))"
  from decr have orient': "\<And> i. (g i, g (Suc i)) \<in> NS \<union> S" unfolding g_def by auto
  have Ps': "\<And> i. i \<in> fS \<Longrightarrow> (g i, g (Suc i)) \<in> S" using fS unfolding g_def by auto
  have Pb': "\<And> i. i \<in> fB \<Longrightarrow> (g i, a) \<in> NS \<union> S" using fB unfolding g_def by auto
  from decr have orient': "\<And> i. (g i, g (Suc i)) \<in> NS \<union> S" unfolding g_def by auto
  {
    fix i j :: nat
    assume "i \<le> j"
    then have "j = (j - i) + i" by arith
    then obtain k where j: "j = k + i" by blast
    have "(g i, g j) \<in> (NS \<union> S)^*" unfolding j
    proof (induct k)
      case (Suc k)
      with orient'[of "k + i"] have "(g i, g (Suc k + i)) \<in> (NS \<union> S)^* O (NS \<union> S)" by auto
      then show ?case by regexp
    qed simp
  } note NS = this

  let ?P = "\<lambda> i. (g i, g (Suc i)) \<in> S"
  (* since for non-inf. we require strict decrease and boundedness in every step, 
     we need to compress our sequences, i.e., we consider a subsequence where all 
     non-strict decreases are dropped *)
  from True have infm: "INFM i. ?P i" using fS unfolding g_def INFM_nat_le by blast
  interpret infinitely_many ?P
    by (unfold_locales, rule infm)
  let ?i = "\<lambda> i. index i"
  define v where "v = (\<lambda> i. g (?i i))"
  {
    fix i
    from index_p[of i] have S: "(v i, g (Suc (?i i))) \<in> S" unfolding v_def .
    from index_ordered[of i] have "Suc (?i i) \<le> ?i (Suc i)" by simp
    from compat_rtrancl[OF S NS[OF this]] have vv: "(v i, v (Suc i)) \<in> S" unfolding v_def .
    from True obtain j where ji: "j \<ge> ?i (Suc i)" and Pb: "j \<in> fB" unfolding INFM_nat_le by auto
    from fB Pb have *: "(g j, a) \<in> NS \<union> S" unfolding g_def by auto
    from compat_rtrancl[OF vv[unfolded v_def] NS[OF ji]] have "(v i, g j) \<in> S" unfolding v_def .
    with * compat_S_NS_point trans_S_point
    have "(v i, a) \<in> S" by blast
    then have "(v i, v (Suc i)) \<in> S" and "(v i, a) \<in> S" using vv by blast+
  } 
  (* using this compressed sequence, we have direct contradiction to non-inf. *)
  with non_infE[OF non_inf, of v a] have False by blast
  then show ?thesis ..
qed

end

definition "bound_on b s = {(x,y). (x,b) \<in> s \<and> (x,y) \<in> s}"
definition "bound_on_le b s ns = {(x,y). (x,b) \<in> ns \<and> (x,y) \<in> s}"

lemma (in non_inf_order) bound_on_SN_generic: "SN (bound_on_le bnd S (NS \<union> S))"
proof -
  have sn: "SN {(a, b). (b, bnd) \<in> S \<and> (a, b) \<in> S}" by (rule non_inf_imp_SN_bound[OF non_inf])
  show ?thesis proof(rule SN_onI) fix f
    assume "\<forall>i. (f i, f (Suc i)) \<in> bound_on_le bnd S (NS \<union> S)"
    then have all:"\<And>i. (f i, f (Suc i)) \<in> {(x,y). (y,bnd) \<in> NS \<union> S \<and> (x,y) \<in> S}"
      unfolding bound_on_le_def by auto
    then have s:"\<And> i. (f i, f (Suc i)) \<in> S"
      and b:"\<And> i. (f (Suc i),bnd) \<in> NS \<union> S" by auto
    from sn[unfolded SN_defs]
      obtain i where i:"(f i, f (Suc i)) \<notin> {(a, b). (b, bnd) \<in> S \<and> (a, b) \<in> S}" by auto
    then have "(f (Suc i), bnd) \<notin> S" using s by auto
    then have "(f (Suc i), f (Suc (Suc i))) \<notin> {(x,y). (y,bnd) \<in> NS \<union> S \<and> (x,y) \<in> S}"
      using compat_S_NS_point trans_S_point by blast
    then show False using all by auto
  qed
qed
  
lemma (in non_inf_order) bound_on_SN: "SN (bound_on bnd S)"
  by (rule SN_subset[OF bound_on_SN_generic], auto simp: bound_on_def bound_on_le_def)

lemma (in non_inf_order) bound_on_le_SN: "SN (bound_on_le bnd S NS)"
  by (rule SN_subset[OF bound_on_SN_generic], auto simp: bound_on_le_def)

lemma (in Order_Pair.compat_pair) compat_pair_bound_on:
  shows "Order_Pair.compat_pair (bound_on bnd S) NS"
  by (unfold_locales, auto simp: bound_on_def dest: compat_NS_S_point compat_S_NS_point)

lemma (in Order_Pair.pre_order_pair) pre_order_pair_bound_on:
  shows "Order_Pair.pre_order_pair (bound_on bnd S) NS"
  by (unfold_locales, auto simp: bound_on_def intro: transI refl_NS dest: transD trans_NS_point trans_S_point)

lemma (in Order_Pair.order_pair) order_pair_bound_on:
  shows "Order_Pair.order_pair (bound_on bnd S) NS"
  by (unfold Order_Pair.order_pair_def, auto intro: compat_pair_bound_on pre_order_pair_bound_on)

lemma (in non_inf_order) SN_order_pair_bound_on:
  shows "Order_Pair.SN_order_pair (bound_on bnd S) NS"
  by (unfold SN_order_pair_def SN_ars_def, intro conjI order_pair_bound_on bound_on_SN)


lemma(in Order_Pair.order_pair) order_pair_union: "Order_Pair.order_pair S (NS \<union> S)"
  by (unfold_locales, auto dest: compat_NS_S_point compat_S_NS_point trans_S_point trans_NS_point intro: trans_S refl_onI refl_NS_point transI)

lemma(in SN_order_pair) SN_order_pair_union: shows "SN_order_pair S (NS \<union> S)"
proof-
  interpret Order_Pair.order_pair S "NS \<union> S" by (rule order_pair_union)
  show ?thesis..
qed

lemma(in non_inf_order) non_inf_union: shows "non_inf_order S (NS \<union> S)"
proof-
  interpret Order_Pair.order_pair S "NS \<union> S" by (fact order_pair_union)
  show ?thesis by (unfold_locales, fact non_inf)
qed

lemma(in Order_Pair.order_pair) order_pair_inv_image: "Order_Pair.order_pair (inv_image S f) (inv_image NS f)"
  by (unfold_locales, auto intro!: refl_onI refl_NS_point transI dest: trans_S_point trans_NS_point compat_NS_S_point compat_S_NS_point)

lemma non_inf_inv_image: "non_inf S \<Longrightarrow> non_inf (inv_image S f)" by fastforce

lemma(in non_inf_order) non_inf_order_inv_image: "non_inf_order (inv_image S f) (inv_image NS f)"
proof-
  interpret Order_Pair.order_pair "inv_image S f" "inv_image NS f" by (fact order_pair_inv_image)
  from non_inf_inv_image[OF non_inf] show ?thesis by unfold_locales
qed

locale non_inf_order_trs = non_inf_order S NS
  for S :: "('f,'v)trs"
  and NS :: "('f,'v)trs" +
  fixes F :: "'f sig"
  and \<pi> :: "'f dep"
  assumes stable_NS: "F_subst_closed F NS"
  and stable_S: "F_subst_closed F S"
  and dep_compat_NS: "dep_compat F NS \<pi>"

end
