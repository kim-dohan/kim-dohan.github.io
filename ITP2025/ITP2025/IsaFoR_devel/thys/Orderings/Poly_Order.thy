(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Poly_Order
imports
  Term_Order_Impl
  First_Order_Rewriting.Term_Impl
  Non_Inf_Order_Impl
  Jordan_Normal_Form.Complexity_Carrier
  "Abstract-Rewriting.SN_Orders"
  Auxx.Map_Choice
  Polynomials.Show_Polynomials
  Show_Literal_Polynomial
  Show.Shows_Literal \<comment> \<open>For having strings in showsl class\<close>
begin

hide_const (open) NthRoot.root

type_synonym ('f, 'a) poly_inter = "'f \<times> nat \<Rightarrow> (nat, 'a) poly"

fun
  eval_term :: "('f, 'a::poly_carrier) poly_inter \<Rightarrow> ('f, 'v :: linorder) term \<Rightarrow> ('v, 'a) poly"
where
  "eval_term _ (Var x) = [(var_monom x,1)]"
| "eval_term I (Fun f ts) = (let
    ps = map (eval_term I) ts;
    n  = length ts
  in poly_subst (\<lambda>i. if i < n then ps ! i else zero_poly) (I (f,n)))"

locale cpx_poly_order_carrier = poly_order_carrier default gt power_mono discrete + complexity_one_mono_ordered_semiring_1 gt default bound
  for default :: "'a :: large_ordered_semiring_1" and gt (infix "\<succ>" 50) and power_mono discrete and bound :: "'a \<Rightarrow> nat"

locale pre_poly_order = poly_order_carrier +
  fixes I :: "('f, 'a) poly_inter"
    and F :: "'f sig"
  assumes  pos_I: "\<And>fn. fn \<in> F \<Longrightarrow> I fn \<ge>p zero_poly"
begin

lemma eval_term_pos:
  fixes t :: "('f, 'v :: linorder) term" assumes tF: "funas_term t \<subseteq> F" shows "eval_term I t \<ge>p zero_poly"
unfolding poly_ge_def zero_poly_def
proof (intro impI allI)
  fix \<alpha> :: "('v,'a)assign"
  assume pos: "pos_assign \<alpha>"
  from tF
  show "eval_poly \<alpha> (eval_term I t) \<ge> eval_poly \<alpha> []"
  proof (induct t)
    case (Var x) then show ?case by (simp add: pos[unfolded pos_assign_def])
  next
    case (Fun f ts)
    then have f: "(f,length ts) \<in> F" by auto
    {
      fix i
      have "eval_poly \<alpha> (if i < length ts then map (eval_term I) ts ! i else zero_poly) \<ge> 0"
      proof (cases "i < length ts")
        case False then show ?thesis unfolding zero_poly_def by (simp add: ge_refl)
      next
        case True
        then have "ts ! i \<in> set ts" by auto
        with Fun have "eval_poly \<alpha> (eval_term I (ts ! i)) \<ge> 0" by auto
        with True show ?thesis by simp
      qed
    }
    then show ?case 
      by (simp add: Let_def poly_subst, intro pos_assign_poly[OF _ pos_I[OF f]], unfold pos_assign_def, auto)
  qed
qed

definition inter_s :: "('f,'v :: linorder)trs"
  where "inter_s \<equiv> {(s,t). (eval_term I s >p eval_term I t)}"

definition inter_ns :: "('f,'v :: linorder)trs"
  where "inter_ns \<equiv> {(s,t). eval_term I s \<ge>p eval_term I t}"

lemma inter_stable: 
  shows "eval_poly \<alpha> (eval_term I (t \<cdot> \<sigma>)) = eval_poly (\<lambda> x. eval_poly \<alpha> (eval_term I (\<sigma> x))) (eval_term I t)"
proof -
  have "eval_poly \<alpha> (eval_term I (t \<cdot> \<sigma>)) = eval_poly (\<lambda> x. eval_poly \<alpha> (eval_term I (\<sigma> x))) (eval_term I t)" (is "_ = eval_poly ?ass _")
  proof (induct t)
    case (Var x)
    then show ?case by simp
  next
    case (Fun f ts)
    let ?ts = "map (\<lambda> s. s \<cdot> \<sigma>) ts"
    show ?case
    proof (simp add: Let_def poly_subst, rule fun_cong, rule arg_cong[where f = eval_poly], rule ext, unfold zero_poly_def)
      fix i
      show "eval_poly \<alpha> (if i < length ts then map (eval_term I \<circ> (\<lambda> t. t \<cdot> \<sigma>)) ts ! i else []) = 
            eval_poly ?ass (if i < length ts then map (eval_term I) ts ! i else [])"
      proof (cases "i < length ts")
        case False then show ?thesis by simp
      next
        case True
        then have "ts ! i \<in> set ts" by auto
        from Fun[OF this] True show ?thesis by simp
      qed
    qed
  qed
  then show ?thesis by simp
qed

lemma pos_assign_F_subst:
  fixes \<sigma> :: "('f, 'v :: linorder) subst"
  assumes F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" and alpha: "pos_assign \<alpha>"
  shows "pos_assign (\<lambda>x. eval_poly \<alpha> (eval_term I (\<sigma> x)))"
unfolding pos_assign_def
proof
  fix x
  from F have "funas_term (\<sigma> x) \<subseteq> F" by auto
  from pos_assign_poly[OF alpha eval_term_pos[OF this]]
  show "eval_poly \<alpha> (eval_term I (\<sigma> x)) \<ge> (0 :: 'a)" .
qed

lemma F_subst_closed_inter_s: "F_subst_closed F inter_s"
proof
  fix \<sigma> :: "('f,'v :: linorder)subst" and s t :: "('f,'v)term"
  assume F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" and st: "(s,t) \<in> inter_s"
  from st[unfolded inter_s_def] have "eval_term I s >p eval_term I t" by simp
  from this[unfolded poly_gt_def]
  have gt: "\<And> \<alpha>. pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (eval_term I s) \<succ> eval_poly \<alpha> (eval_term I t)" by blast
  have "eval_term I (s \<cdot> \<sigma>) >p eval_term I (t \<cdot> \<sigma>)" unfolding poly_gt_def inter_stable
    by (intro allI impI, rule gt, rule pos_assign_F_subst[OF F])
  then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> inter_s" unfolding inter_s_def by simp
qed

lemma F_subst_closed_inter_ns: "F_subst_closed F inter_ns"
proof
  fix \<sigma> :: "('f,'v :: linorder)subst" and s t :: "('f,'v)term"
  assume F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" and st: "(s,t) \<in> inter_ns"
  from st[unfolded inter_ns_def] have "eval_term I s \<ge>p eval_term I t" by simp
  from this[unfolded poly_ge_def]
  have gt: "\<And> \<alpha>. pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (eval_term I s) \<ge> eval_poly \<alpha> (eval_term I t)" by blast
  have "eval_term I (s \<cdot> \<sigma>) \<ge>p eval_term I (t \<cdot> \<sigma>)" unfolding poly_ge_def inter_stable
    by (intro allI impI, rule gt, rule pos_assign_F_subst[OF F])
  then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> inter_ns" unfolding inter_ns_def by simp
qed

lemma trans_inter_ns: "trans inter_ns"
  unfolding trans_def inter_ns_def using poly_ge_trans by auto

lemma refl_inter_ns: "refl inter_ns"
  unfolding refl_on_def inter_ns_def using poly_ge_refl by auto

lemma trans_inter_s: "trans inter_s"
    unfolding trans_def inter_s_def using poly_gt_trans by auto

lemma inter_ns_s_s: "inter_ns O inter_s \<subseteq> inter_s"
  by (rule subrelI, clarify, unfold inter_s_def inter_ns_def, simp add: poly_compat)

lemma inter_s_ns_s: "inter_s O inter_ns \<subseteq> inter_s"
  by (rule subrelI, clarify, unfold inter_s_def inter_ns_def, simp add: poly_compat2)
end

locale non_inf_poly_order_carrier = poly_order_carrier default gt power_mono discrete 
  for default :: "'a :: poly_carrier" and gt (infix "\<succ>" 50) 
    and power_mono :: bool and discrete :: bool +
  fixes sqrt :: "'a \<Rightarrow> 'a list"
  assumes non_inf: "non_inf {(a, b). a \<succ> b}"
    and anti_sym: "\<And> a b :: 'a. a \<ge> b \<Longrightarrow> b \<ge> a \<Longrightarrow> a = b"
    and cond_ge: "\<And> a b c d :: 'a. a + d \<ge> b + c \<Longrightarrow> c \<ge> d \<Longrightarrow> a \<ge> b"
    and cond_gt: "\<And> a b c d :: 'a. a + d \<ge> b + c \<Longrightarrow> gt c d \<Longrightarrow> gt a b"
    and sqr: "\<And> a :: 'a . a * a \<ge> 0"

locale poly_order = pre_poly_order default gt power_mono discrete I UNIV +
  cpx_poly_order_carrier default gt power_mono discrete bound
  for default :: "'a :: large_ordered_semiring_1" and gt (infix "\<succ>" 50) 
  and power_mono :: bool
  and discrete :: bool 
  and I :: "('f, 'a) poly_inter"
  and bound :: "'a \<Rightarrow> nat" +
  fixes \<pi> :: "'f af"
  assumes mono_I: "\<And>fn. poly_weak_mono_all (I fn)"
    and pi: "\<And>fn. poly_vars (I fn) \<subseteq> \<pi> fn"
begin
lemma eval_term_pos: fixes t :: "('f,'v :: linorder)term" shows "eval_term I t \<ge>p zero_poly"
  by (rule eval_term_pos, auto)
end

locale non_inf_poly_order = pre_poly_order default gt power_mono discrete I F + non_inf_poly_order_carrier default gt power_mono discrete sqrt
  for default :: "'a :: poly_carrier" and gt (infix "\<succ>" 50) 
  and power_mono :: bool
  and discrete :: bool
  and sqrt :: "'a \<Rightarrow> 'a list"
  and I :: "('f, 'a) poly_inter"
  and F :: "'f sig" + 
  fixes \<pi> :: "'f dep"
  assumes pi_ignore: "\<And>fn i. i < snd fn \<Longrightarrow> \<pi> fn i = Ignore \<Longrightarrow> i \<notin> poly_vars (I fn)"
    and pi_increase: "\<And>fn i. i < snd fn \<Longrightarrow> \<pi> fn i = Increase \<Longrightarrow> poly_weak_mono (I fn) i"
    and pi_decrease: "\<And>fn i. i < snd fn \<Longrightarrow> \<pi> fn i = Decrease \<Longrightarrow> poly_weak_anti_mono (I fn) i"

sublocale non_inf_poly_order \<subseteq> non_inf_order_trs inter_s inter_ns
proof
  show "F_subst_closed F inter_ns" by (rule F_subst_closed_inter_ns)
  show "F_subst_closed F inter_s" by (rule F_subst_closed_inter_s)
  show "inter_ns O inter_s \<subseteq> inter_s" by (rule inter_ns_s_s)
  show "inter_s O inter_ns \<subseteq> inter_s" by (rule inter_s_ns_s)
  show "refl inter_ns" by (rule refl_inter_ns)
  show "trans inter_ns" by (rule trans_inter_ns)
  show "trans inter_s" by (rule trans_inter_s)
next
  show "non_inf inter_s"
  proof (rule non_inf_image[OF non_inf])
    fix s t :: "('f,'v :: linorder)term"
    define \<alpha> where "\<alpha> = (\<lambda> v :: 'v. 0 :: 'a)"
    let ?f = "\<lambda> t :: ('f,'v)term. eval_poly \<alpha> (eval_term I t)"
    have pos: "pos_assign \<alpha>" unfolding pos_assign_def \<alpha>_def using ge_refl by simp
    assume st: "(s,t) \<in> inter_s"
    with st[unfolded inter_s_def poly_gt_def] pos
    show "(?f s, ?f t) \<in> {(a, b). a \<succ> b}" by simp
  qed
next
  show "dep_compat F inter_ns \<pi>" 
  proof
    fix f and s t and bef aft :: "('f,'v :: linorder)term list"
    assume ns: "{(s, t)} ^^^ \<pi> (f, Suc (length bef + length aft)) (length bef) \<subseteq> inter_ns"
      and TF: "\<And> u. u \<in> {s,t} \<union> set bef \<union> set aft \<Longrightarrow> funas_term u \<subseteq> F"
    let ?T = "{s,t} \<union> set bef \<union> set aft"
    let ?i = "length bef"
    let ?n = "Suc (?i + length aft)"
    let ?ss = "bef @ s # aft"
    let ?ts = "bef @ t # aft"
    let ?s = "Fun f ?ss"
    let ?t = "Fun f ?ts"
    let ?f = "(f,?n)"
    let ?pi = "\<pi> ?f ?i"
    have len: "\<And> t. length (bef @ t # aft) = ?n" by simp
    note ns = ns[unfolded inter_ns_def]
    note eval = eval_term.simps Let_def len
    have "eval_term I ?s \<ge>p eval_term I ?t" 
      unfolding poly_ge_def 
    proof (clarify)
      fix \<alpha> :: "('v,'a)assign"
      assume pos: "pos_assign \<alpha>"
      let ?e = "\<lambda> t. eval_poly \<alpha> (eval_term I t)"
      let ?ee = "\<lambda> t w. if w < ?n then map (eval_term I) (bef @ t # aft) ! w else zero_poly"
      from eval_term_pos[OF TF]
      have T0: "\<And> u. u \<in> ?T \<Longrightarrow> eval_term I u \<ge>p zero_poly" .
      let ?S = "insert zero_poly (eval_term I ` ?T0)"
      {
        fix p
        assume "p \<in> ?S"
        with T0 poly_ge_refl[of zero_poly] have "p \<ge>p zero_poly" by blast
      } note S0 = this
      show "?e ?s \<ge> ?e ?t"
      proof (cases ?pi)
        case Increase
        from ns[unfolded Increase] have ge: "eval_term I s \<ge>p eval_term I t" by auto
        from pi_increase[OF _ Increase] have "poly_weak_mono (I ?f) ?i" by simp
        from poly_weak_mono_E[OF this] pos
        have mono: "\<And> f g. \<lbrakk>\<And> j. (?i \<noteq> j \<longrightarrow> f j = g j) \<and> g j \<ge>p zero_poly\<rbrakk> \<Longrightarrow> f ?i \<ge>p g ?i \<Longrightarrow>
          eval_poly \<alpha> (poly_subst f (I ?f)) \<ge> eval_poly \<alpha> (poly_subst g (I ?f))" using poly_ge_def by blast
        show ?thesis unfolding eval 
        proof (rule mono, intro conjI impI)
          show "?ee s ?i \<ge>p ?ee t ?i" using ge by (simp add: nth_append)
        next
          fix j
          assume "?i \<noteq> j"
          then show "?ee s j = ?ee t j" by (simp add: nth_append)
        next
          fix j
          show "?ee t j \<ge>p zero_poly" 
            by (rule S0, cases "j < ?n", auto simp: nth_append, cases "j - ?i", auto)
        qed
      next
        case Decrease
        from ns[unfolded Decrease] have ge: "eval_term I t \<ge>p eval_term I s" by auto
        from pi_decrease[OF _ Decrease] have "poly_weak_anti_mono (I ?f) ?i" by simp
        from poly_weak_anti_mono_E[OF this] pos
        have mono: "\<And> f g. \<lbrakk>\<And> j. (?i \<noteq> j \<longrightarrow> f j = g j) \<and> g j \<ge>p zero_poly\<rbrakk> \<Longrightarrow> f ?i \<ge>p g ?i \<Longrightarrow>
          eval_poly \<alpha> (poly_subst g (I ?f)) \<ge> eval_poly \<alpha> (poly_subst f (I ?f))" unfolding poly_ge_def by blast
        show ?thesis unfolding eval 
        proof (rule mono, intro conjI impI)
          show "?ee t ?i \<ge>p ?ee s ?i" using ge by (simp add: nth_append)
        next
          fix j
          assume "?i \<noteq> j"
          then show "?ee t j = ?ee s j" by (simp add: nth_append)
        next
          fix j
          show "?ee s j \<ge>p zero_poly" 
            by (rule S0, cases "j < ?n", auto simp: nth_append, cases "j - ?i", auto)
        qed
      next
        case Ignore
        from pi_ignore[OF _ this] have nvar: "?i \<notin> poly_vars (I ?f)" by simp
        have "?e ?s = ?e ?t"
          unfolding eval
          by (rule arg_cong[where f = "eval_poly \<alpha>"], rule poly_var[OF nvar], auto simp: nth_append)
        then show ?thesis using ge_refl by simp
      next
        case Wild
        from ns[unfolded Wild poly_ge_def] pos have "?e s \<ge> ?e t" "?e t \<ge> ?e s" by auto
        from anti_sym[OF this]
        have id: "?e s = ?e t" .
        have "?e ?s = ?e ?t"
          unfolding eval poly_subst
        proof (rule eval_poly_vars)
          fix i
          show "eval_poly \<alpha> (if i < ?n then map (eval_term I) ?ss ! i else zero_poly) =
            eval_poly \<alpha> (if i < ?n then map (eval_term I) ?ts ! i else zero_poly)"
            using id
            by (auto simp: nth_append, cases "i - ?i", auto)
        qed
        then show ?thesis using ge_refl by simp
      qed
    qed
    then show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> inter_ns" unfolding inter_ns_def by simp
  qed
qed
  
sublocale poly_order \<subseteq> redtriple_order inter_s inter_ns inter_ns
proof
  show "subst.closed inter_s"
    by (rule F_subst_closed_UNIV[OF F_subst_closed_inter_s refl])
  show "subst.closed inter_ns"
    by (rule F_subst_closed_UNIV[OF F_subst_closed_inter_ns refl])
  show "inter_ns O inter_s \<subseteq> inter_s" by (rule inter_ns_s_s)
  show "inter_s O inter_ns \<subseteq> inter_s" by (rule inter_s_ns_s)
  show "refl inter_ns" by (rule refl_inter_ns)
  show "trans inter_ns" by (rule trans_inter_ns)
  show "trans inter_s" by (rule trans_inter_s)
  show "inter_s \<subseteq> inter_ns" 
    using poly_gt_imp_poly_ge unfolding inter_s_def inter_ns_def by blast
  show "SN inter_s"
  proof (standard, goal_cases)
    case (1 f)
    obtain g where g: "\<And> i. g i = eval_term I (f i)" by auto
    from 1[unfolded inter_s_def] eval_term_pos
    have "\<And> i. (g i, g (Suc i)) \<in> poly_GT" 
      by (simp only: g, auto)
    with poly_GT_SN show False unfolding SN_defs by blast
  qed
next
  show "ctxt.closed inter_ns"
  proof (rule one_imp_ctxt_closed)
    fix f bef and s t :: "('f,'v :: linorder)term" and aft 
    assume st: "(s,t) \<in> inter_ns"
    show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> inter_ns" (is "(Fun f ?s, Fun f ?t) \<in> _")
      unfolding inter_ns_def poly_ge_def
    proof (clarify)
      fix \<alpha> :: "('v,'a)assign"
      assume pos: "pos_assign \<alpha>"
      let ?n = "Suc (length bef + length aft)"
      let ?i = "length bef"
      from mono_I[of "(f,?n)"] have mono: "poly_weak_mono (I (f,?n)) ?i" by (rule poly_weak_mono_all)
      let ?exp = "\<lambda> w s.  (if w < ?n then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! w else zero_poly)"
      {
        fix w
        assume "?i \<noteq> w"
        then have "?exp w s = ?exp w t" by (simp add: nth_append)
      } note one = this
      {
        fix w
        have "\<exists> ts. (?exp w t = (if w < length ts then (map (eval_term I) ts) ! w else zero_poly))"
          by (rule exI[of _ ?t], simp only: map_append, simp)
        then obtain ts where id: "?exp w t = (if w < length ts then (map (eval_term I) ts) ! w else zero_poly)" by blast
        have "?exp w t \<ge>p zero_poly" 
          by (simp only: id, unfold poly_ge_def zero_poly_def, simp add: ge_refl, intro impI allI, force simp: eval_term_pos[unfolded poly_ge_def zero_poly_def, simplified])
      } note two = this 
      have "eval_poly \<alpha> (poly_subst (\<lambda>i. if i < ?n then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! i else zero_poly) (I (f,?n))) \<ge>
        eval_poly \<alpha> (poly_subst (\<lambda>i. if i < ?n then (map (eval_term I) bef @ eval_term I t # map (eval_term I) aft) ! i else zero_poly) (I (f,?n)))"
        by (rule poly_weak_mono_E[OF mono, unfolded poly_ge_def, rule_format, OF _ _ _ pos])
           ((auto simp: one two ge_refl two[unfolded poly_ge_def])[2], simp add: nth_append st[unfolded inter_ns_def poly_ge_def, simplified])
      then show "eval_poly \<alpha> (eval_term I (Fun f ?s)) \<ge> eval_poly \<alpha> (eval_term I (Fun f ?t))" by simp
    qed
  qed
qed

sublocale poly_order \<subseteq> af_redpair inter_s inter_ns \<pi>
proof
  show "af_compatible \<pi> inter_ns"
    unfolding af_compatible_def
  proof (intro allI, clarify, goal_cases)
    case (1 f bef s t aft) 
    let ?s = "bef @ s # aft"
    let ?t = "bef @ t # aft"
    let ?n = "Suc (length bef + length aft)"
    let ?i = "length bef"
    show "?i \<in> \<pi> (f, ?n)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with pi have pv: "?i \<notin> poly_vars (I (f,?n))" by auto
      let ?sub = "\<lambda>s i. if i < ?n then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! i else zero_poly"
      have id: "poly_subst (?sub s) (I (f,?n)) = poly_subst (?sub t) (I (f,?n))"
      proof (rule poly_var[OF pv])
        fix j
        assume "?i \<noteq> j"
        then show "(if j < ?n then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! j else zero_poly) = 
          (if j < ?n then (map (eval_term I) bef @ eval_term I t # map (eval_term I) aft) ! j else zero_poly)"
          by (cases "j \<ge> ?n", simp, cases "j < ?i", simp add: nth_append, cases "j \<ge> ?i", simp add: nth_append, cases "j - ?i", simp, simp add: nth_append)
      qed
      { 
        fix \<alpha>
        have "eval_poly \<alpha> (eval_term I (Fun f ?s)) = eval_poly \<alpha> (eval_term I (Fun f ?t))"  using id by simp
        then have "eval_poly \<alpha> (eval_term I (Fun f ?s)) \<ge> eval_poly \<alpha> (eval_term I (Fun f ?t))" using ge_refl by simp
      }
      then have "(Fun f ?s, Fun f ?t) \<in> inter_ns" unfolding inter_ns_def poly_ge_def by auto
      with 1 show False ..
    qed
  qed
qed

context poly_order
begin

lemma poly_strict_mono_imp_af_monotone: assumes "\<And> f n i. i < n \<Longrightarrow> i \<in> \<mu> (f,n) \<Longrightarrow> poly_strict_mono (I (f,n)) i"
  shows "af_monotone \<mu> inter_s"
proof (rule af_monotoneI)
  fix f and s t :: "('f,'v :: linorder)term" and bef aft :: "('f,'v)term list"
  let ?n = "Suc (length bef + length aft)"
  let ?i = "length bef"
  assume st: "(s,t) \<in> inter_s" and bef: "?i \<in> \<mu> (f, ?n)"
  from assms[OF _ bef] have mono: "poly_strict_mono (I (f, ?n)) ?i" by auto
  show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> inter_s" (is "(Fun f ?s, Fun f ?t) \<in> _")
    unfolding inter_s_def poly_gt_def
  proof (clarify)
    fix \<alpha> :: "('v,'a)assign"
    assume pos: "pos_assign \<alpha>"
    let ?exp = "\<lambda> w s.  (if w < Suc (length bef + length aft) then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! w else zero_poly)"
    {
      fix w
      assume "?i \<noteq> w"
      then have "?exp w s = ?exp w t" by (simp add: nth_append)
    } note one = this
    {
      fix w
      have "\<exists> ts. (?exp w t = (if w < length ts then (map (eval_term I) ts) ! w else zero_poly))"
        by (rule exI[of _ ?t], simp only: map_append, simp)
      then obtain ts where id: "?exp w t = (if w < length ts then (map (eval_term I) ts) ! w else zero_poly)" (is "_ = ?if") by blast
      have "?exp w t \<ge>p zero_poly" 
      proof (simp only: id, unfold poly_ge_def, intro impI allI)
        fix \<alpha> :: "('v,'a)assign"
        assume "pos_assign \<alpha>"
        then show "eval_poly \<alpha> ?if \<ge> eval_poly \<alpha> zero_poly"
          by (simp add: ge_refl zero_poly_def, force simp: eval_term_pos[unfolded poly_ge_def zero_poly_def, simplified])
      qed
    } note two = this 
    have "eval_poly \<alpha> (poly_subst (\<lambda> i. ?exp i s) (I (f,?n))) \<succ> eval_poly \<alpha> (poly_subst (\<lambda> i. ?exp i t) (I (f,?n)))"
    by (rule poly_strict_mono_E[OF mono, unfolded poly_gt_def, rule_format],
      insert pos one two st[unfolded inter_s_def poly_gt_def], auto simp: nth_append)
    then show "eval_poly \<alpha> (eval_term I (Fun f ?s)) \<succ> eval_poly \<alpha> (eval_term I (Fun f ?t))" by simp
  qed
qed  
end

locale mono_poly_order = poly_order +
  assumes strict_mono_I: "\<And>f n i. i < n \<Longrightarrow> poly_strict_mono (I (f,n)) i"
begin

lemma inter_s_mono: "ctxt.closed (inter_s :: ('b,'v :: linorder)trs)"
  by (rule af_monotone_full_af_imp_ctxt_closed[OF poly_strict_mono_imp_af_monotone],
  rule strict_mono_I)
end       

definition default_I :: "'a \<Rightarrow> nat \<Rightarrow> (nat,'a :: poly_carrier)poly"
where "default_I def n \<equiv> (1,def) # map (\<lambda> i. (var_monom i,1)) [0 ..< n]"

lemma default_I_check_poly_weak_mono: assumes "def \<ge> (0 :: 'a :: poly_carrier)" shows "check_poly_weak_mono_all (default_I def n)"
unfolding default_I_def check_poly_weak_mono_all_def
by (simp add: list_all_iff assms one_ge_zero)

lemma default_I_check_poly_strict_mono: assumes i: "i < n" shows "check_poly_strict_mono power_mono (default_I def n) i"
unfolding check_poly_strict_mono_def list_ex_iff default_I_def using i
  by (auto simp: ge_refl check_monom_strict_mono_def univariate_power_var_monom)


lemma default_I_pos: assumes "def \<ge> (0 :: 'a :: poly_carrier)" shows "default_I def n \<ge>p zero_poly"
using check_poly_weak_mono_all_pos[OF default_I_check_poly_weak_mono[OF assms]] .

lemma default_I_mono_all: assumes ge: "def \<ge> (0 :: 'a :: poly_carrier)" shows "poly_weak_mono_all (default_I def n)"
using check_poly_weak_mono_all[OF default_I_check_poly_weak_mono[OF assms]] .

lemma (in pre_poly_order) default_imp_s: 
  assumes st: "st = (Fun f ts, t)"
  and t: "t \<in> set ts"
  and d: "I (f,length ts) = default_I default (length ts)"
  and F: "\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F"
  shows "st \<in> inter_s" unfolding st inter_s_def
proof (clarify, unfold eval_term.simps Let_def d default_I_def)
  let ?et = "eval_term I"
  let ?\<sigma>' = "(\<lambda>i. if i < length ts then map ?et ts ! i else zero_poly)"
  let ?\<sigma> = "\<lambda> i. ?et (ts ! i)"
  let ?map = "map (\<lambda>i. (var_monom i, 1)) [0..<length ts]"
  let ?def = "(1, default) # ?map"
  have id: "poly_subst ?\<sigma>' ?def = poly_subst ?\<sigma> ?def"
    by (rule poly_vars, auto simp: poly_vars_def)
  show "poly_subst ?\<sigma>' ?def >p ?et t" unfolding id poly_gt_def
  proof (intro allI impI)
    fix \<alpha> :: "'b \<Rightarrow> 'a"
    let ?ep = "eval_poly \<alpha>"
    let ?ep' = "\<lambda>v. ?ep (?et (ts ! v))"
    let ?m = "sum_list (map (\<lambda> t. ?ep (?et t)) ts)"
    let ?d = "default + ?m"
    have "?m = eval_poly ?ep' ?map" 
    proof (induct ts rule: List.rev_induct)
      case (snoc x xs)
      show ?case
        by (simp add: snoc, rule arg_cong[where f = "\<lambda> t. t + ?ep (?et x)"],
          rule eval_poly_vars, auto simp: poly_vars_def nth_append)
    qed simp
    then have id: "eval_poly ?ep' ?def = ?d" by simp
    assume pos: "pos_assign \<alpha>"
    define f where "f = (\<lambda> t. ?ep (?et t))"
    from pos_assign_poly[OF pos eval_term_pos[OF F]] 
    have pos: "\<And> t. t \<in> set ts \<Longrightarrow> f t \<ge> 0" unfolding f_def .
    have id2: "?ep (?et t) = f t" unfolding f_def ..
    show "?ep (poly_subst ?\<sigma> ?def) \<succ> ?ep (?et t)"
      unfolding poly_subst id id2
      using t pos
      unfolding f_def[symmetric]
    proof (induct ts)
      case (Cons s ts)
      from Cons(3)[of s] have fs: "0 \<le> f s" by auto
      from Cons(3) have pos: "\<And> t. t \<in> set ts \<Longrightarrow> 0 \<le> f t" by auto
      show ?case
      proof (cases "s = t")
        case False
        with Cons(2) have "t \<in> set ts" by auto
        from Cons(1)[OF this pos] 
        have 1: "default + sum_list (map f ts) \<succ> f t" (is "?sum \<succ> _") by simp
        have 2: "?sum \<le> ?sum + f s" using 
          plus_left_mono[OF fs, of ?sum] by (auto simp: ac_simps)
        from compat[OF 2 1]
        show ?thesis by (simp add: ac_simps)
      next
        case True
        from plus_gt_left_mono[OF default_gt_zero, of "f t"] True
        have 1: "default + f s + 0 \<succ> f t" by simp
        have "default + f s + sum_list (map f ts) \<succ> f t"
        proof (rule compat[OF plus_right_mono 1], insert pos, induct ts)
          case Nil
          with ge_refl show ?case by simp
        next
          case (Cons t ts)
          from Cons(2)[of t] have t: "0 \<le> f t" by auto
          from Cons(1)[OF Cons(2)] have "0 \<le> sum_list (map f ts)" by auto
          from ge_trans[OF plus_right_mono[OF t] plus_left_mono[OF this]]
          show ?case by (simp add: ac_simps)
        qed
        then show ?thesis by (simp add: ac_simps)
      qed
    qed simp
  qed
qed

locale ce_poly_order = poly_order +
  assumes default: "\<exists> n. \<forall> f m. m \<ge> n \<longrightarrow> I (f,m) = default_I default m"
begin

lemma ce_compat: 
  shows "\<exists> n. \<forall> m \<ge> n. \<forall> c. ce_trs (c,m) \<subseteq> inter_ns \<inter> (inter_s :: ('b,_)trs)"
proof -
  from default obtain n where default: "\<And> f m. m \<ge> n \<Longrightarrow> I (f,m) = default_I default m" by auto
  show ?thesis
  proof(rule exI[of _ n], intro allI impI)
    fix m and c d :: 'b
    assume "n \<le> m"
    with default have default: "I (c,Suc (Suc m)) = default_I default (Suc (Suc m))" by auto
    show "ce_trs (c,m) \<subseteq> inter_ns \<inter> inter_s"
    proof (standard, goal_cases)
      case (1 s t)
      from this[unfolded ce_trs.simps] 
      obtain u v where s: "s = Fun c (u # v # replicate m (Var undefined))" 
        and t: "\<And> ts. t \<in> set (u # v # ts)" by auto
      have "(s,t) \<in> inter_s" unfolding s
        by (rule default_imp_s[OF refl t], insert default, auto)
      with S_imp_NS show "(s,t) \<in> inter_ns \<inter> inter_s" by blast
    qed
  qed
qed 
end

locale mono_ce_poly_order = ce_poly_order + mono_poly_order

sublocale ce_poly_order \<subseteq> ce_af_redtriple_order inter_s inter_ns inter_ns \<pi>
proof -
  let ?inter_s = "inter_s :: ('b,'v :: linorder)trs"
  have "\<exists> n. \<forall> m \<ge> n. \<forall> c. ce_trs (c,m) \<subseteq> inter_ns \<inter> ?inter_s"
    by (rule ce_compat)
  then have one: "ce_compatible inter_s" and
    ce: "ce_compatible inter_ns" unfolding ce_compatible_def by blast+
  show "ce_af_redtriple_order inter_s inter_ns inter_ns \<pi>"
    by (unfold_locales, rule ce)
qed

sublocale mono_ce_poly_order \<subseteq> mono_ce_af_redtriple_order inter_s inter_ns inter_ns \<pi>
proof -
  let ?inter_s = "inter_s :: ('b,'v :: linorder)trs"
  have "\<exists> n. \<forall> m \<ge> n. \<forall> c. ce_trs (c,m) \<subseteq> inter_ns \<inter> ?inter_s"
    by (rule ce_compat)
  then have ce: "ce_compatible ?inter_s" unfolding ce_compatible_def by blast+
  show "mono_ce_af_redtriple_order ?inter_s inter_ns inter_ns \<pi>"
    by (unfold_locales, rule inter_s_mono, rule ce)
qed

type_synonym ('f,'a)poly_inter_list = "(('f \<times> nat) \<times> (nat,'a)poly)list"

definition
  poly_inter_list_to_inter :: "'a :: poly_carrier \<Rightarrow> ('f :: compare_order, 'a) poly_inter_list \<Rightarrow> ('f, 'a) poly_inter"
where
  "poly_inter_list_to_inter def I \<equiv> fun_of_map_fun (ceta_map_of I) (\<lambda> fn. default_I def (snd fn))"

definition poly_inter_to_af :: "('f :: compare_order,'a) poly_inter_list \<Rightarrow> 'f af" where
  "poly_inter_to_af I \<equiv> fun_of_map_fun (ceta_map_of (map (\<lambda> (fn,e). (fn, poly_vars e)) I)) (\<lambda> fn. {0 ..< snd fn})"

definition poly_inter_to_mono_af :: "bool \<Rightarrow> bool \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('f :: compare_order,'a :: poly_carrier)poly_inter_list \<Rightarrow> 'f af" where
  "poly_inter_to_mono_af discrete power_mono gt I \<equiv> fun_of_map_fun (ceta_map_of (map (\<lambda> ((f,n),e). ((f,n),
    set (filter (\<lambda> i. check_poly_weak_mono_and_pos discrete e \<and> check_poly_strict_mono_smart discrete power_mono gt e i) [0 ..< n]))) I)) (\<lambda> fn. {0 ..< snd fn})"

definition check_poly_inter_list :: "bool \<Rightarrow> ('f,'a :: poly_carrier)poly_inter_list \<Rightarrow> (showsl + ('f \<times> (nat,'a)poly)) check"
where "check_poly_inter_list discrete I \<equiv> do {
   check (distinct (map fst I)) (Inl (showsl (STR ''some symbol has two interpretations'')));
   check_all (\<lambda> (_,p). check_poly_weak_mono_and_pos discrete p) I <+? (\<lambda> ((f,n),p). Inr (f,p))
 }"

definition check_non_inf_poly_inter_list :: "bool \<Rightarrow> ('f \<times> nat)list \<Rightarrow> ('f,'a :: poly_carrier)poly_inter_list \<Rightarrow> ('f \<times> (nat,'a)poly) check"
where "check_non_inf_poly_inter_list discrete F I \<equiv> do {
    check_all (\<lambda> (_,p). check_poly_weak_mono_and_pos discrete p) (filter (\<lambda> (fn,p). fn \<in> set F) I) <+? (\<lambda> ((f,n),p). (f,p))
  }"

definition create_dep :: "bool \<Rightarrow> 'a \<Rightarrow> ('f :: compare_order,'a :: poly_carrier)poly_inter_list \<Rightarrow> 'f dep" where
  "create_dep discrete def I \<equiv> let 
     fs = remdups (map fst I);
     II = poly_inter_list_to_inter def I;
     fsres = map (\<lambda> fn. let 
        p = II fn;
        vars = poly_vars_list p;
        is = [0 ..< snd fn];
        res = map (\<lambda> i. if i \<in> set vars then 
          (if check_poly_weak_mono_smart discrete p i then Increase
          else if check_poly_weak_anti_mono_smart discrete p i then Decrease
          else Wild)
          else Ignore) is
      in (fn,res)) fs;
     III = fun_of_map_fun' (ceta_map_of fsres) (\<lambda> _ i. Increase) (\<lambda> res i. res ! i)
  in III"  

context non_inf_poly_order_carrier
begin

lemma check_non_inf_poly_inter_list: fixes I :: "('f :: compare_order,'a :: poly_carrier)poly_inter_list"
  assumes check: "isOK(check_non_inf_poly_inter_list discrete F I)"
  shows "non_inf_poly_order default gt power_mono discrete (poly_inter_list_to_inter default I) (set F) (create_dep discrete default I)"
proof -
  let ?I = "poly_inter_list_to_inter default I"
  let ?pi = "create_dep discrete default I"
  {
    fix f :: 'f and n i :: nat
    assume i: "i < n"
    let ?pii = "?pi (f,n) i"
    let ?If = "?I (f,n)"
    let ?P1 = "?pii = Ignore \<longrightarrow> i \<notin> poly_vars ?If"
    let ?P2 = "?pii = Increase \<longrightarrow> poly_weak_mono ?If i"
    let ?P3 = "?pii = Decrease \<longrightarrow> poly_weak_anti_mono ?If i"
    define main where "main = (\<lambda> fn. let 
        p = ?I fn;
        vars = poly_vars_list p;
        is = [0 ..< snd fn];
        res = map (\<lambda> i. if i \<in> set vars then 
          (if check_poly_weak_mono_smart discrete p i then Increase
          else if check_poly_weak_anti_mono_smart discrete p i then Decrease
          else Wild)
          else Ignore) is
      in (fn,res))"
    define fsres where "fsres = (let fs = remdups (map fst I) in map main fs)"
    have fst_id: "fst ` set fsres = fst ` set I" unfolding fsres_def main_def Let_def by force
    have "?P1 \<and> ?P2 \<and> ?P3"
    proof (cases "map_of fsres (f,n)")
      case None
      then have "(f,n) \<notin> fst ` set fsres" unfolding map_of_eq_None_iff .
      then have "map_of I (f,n) = None" unfolding fst_id map_of_eq_None_iff .
      then have Idef: "?I (f,n) = default_I default n" unfolding poly_inter_list_to_inter_def by simp
      from None have inc: "?pii = Increase" unfolding create_dep_def fsres_def main_def Let_def by simp
      have ?P2
      proof
        show "poly_weak_mono (poly_inter_list_to_inter default I (f, n)) i"
          unfolding Idef
          by (rule poly_weak_mono_all[OF check_poly_weak_mono_all[OF default_I_check_poly_weak_mono[OF default_ge_zero]]])
      qed
      with inc show ?thesis by auto
    next
      case (Some deps)
      let ?i = "(\<lambda> i. if i \<in> set (poly_vars_list ?If) then 
          (if check_poly_weak_mono_smart discrete ?If i then Increase
          else if check_poly_weak_anti_mono_smart discrete ?If i then Decrease
          else Wild)
          else Ignore)"
      from Some have dep: "?pii = deps ! i" unfolding create_dep_def fsres_def main_def Let_def by simp
      from map_of_SomeD[OF Some] have "((f,n),deps) \<in> set fsres" .
      then have "main (f,n) = ((f,n),deps)" unfolding fsres_def main_def Let_def by auto
      from this[unfolded main_def Let_def] have deps: "deps = map ?i [0 ..< n]" by simp
      with i dep have dep: "?pii = ?i i" by simp
      show ?thesis
      proof (cases "i \<in> poly_vars ?If")
        case False
        with dep have dep: "?pii = Ignore" by simp
        from False have "i \<notin> poly_vars ?If" by auto
        with dep show ?thesis by auto
      next
        case True note pv = this
        show ?thesis
        proof (cases "check_poly_weak_mono_smart discrete ?If i")
          case True
          with pv dep have dep: "?pii = Increase" by simp
          from check_poly_weak_mono_smart[OF True] dep
          show ?thesis by auto
        next
          case False note wm = this
          show ?thesis
          proof (cases "check_poly_weak_anti_mono_smart discrete ?If i")
            case True
            with pv wm dep have dep: "?pii = Decrease" by simp
            from check_poly_weak_anti_mono_smart[OF True] dep
            show ?thesis by auto
          next
            case False
            with pv wm dep show ?thesis by auto
          qed
        qed
      qed
    qed
  } note dep_compat = this
  show ?thesis
  proof
    fix fn
    assume fn: "fn \<in> set F"
    show "?I fn \<ge>p zero_poly"
    proof (cases "map_of I fn")
      case None then show ?thesis 
        by (cases fn, simp only: poly_inter_list_to_inter_def, simp add: default_I_pos[OF default_ge_zero] default_I_mono_all[OF default_ge_zero])
    next 
      case (Some p)
      from map_of_SomeD[OF this] check[unfolded check_non_inf_poly_inter_list_def] fn
      have "check_poly_weak_mono_and_pos discrete p" by (cases fn, force)
      from check_poly_weak_mono_and_pos[OF this]
      show ?thesis unfolding poly_inter_list_to_inter_def using Some by auto
    qed 
  qed (insert dep_compat, force+)
qed
end 

lemma poly_vars_default_I[simp]: "poly_vars (default_I k n) = {0..< n}"
  unfolding default_I_def poly_vars_def by auto

lemma check_poly_inter_list_distinct: 
  "isOK(check_poly_inter_list discrete I) \<Longrightarrow> distinct (map fst I)"
  unfolding check_poly_inter_list_def by auto

context cpx_poly_order_carrier
begin

lemma check_poly_inter_list: assumes check: "isOK(check_poly_inter_list discrete I)"
  shows "poly_weak_mono_all (poly_inter_list_to_inter default I (f,n)) \<and> (poly_inter_list_to_inter default I (f,n) \<ge>p zero_poly)"
proof -
  note d = check_poly_inter_list_def
  let ?I = "poly_inter_list_to_inter default I"
  show ?thesis
  proof (cases "map_of I (f, n)")
    case None then show ?thesis 
      by (simp only: poly_inter_list_to_inter_def, simp add: default_I_pos[OF default_ge_zero] default_I_mono_all[OF default_ge_zero])
  next 
    case (Some p)
    with map_of_SomeD[OF this] check[unfolded d]
    show ?thesis unfolding poly_inter_list_to_inter_def using check_poly_weak_mono_and_pos  by force
  qed
qed

lemma ce_poly_order: 
  fixes I :: "('f :: compare_order,'a)poly_inter_list"
  assumes check: "isOK(check_poly_inter_list discrete I)"
  shows "ce_poly_order default gt power_mono discrete (poly_inter_list_to_inter default I) bound (poly_inter_to_af I)"
proof -
  let ?I = "poly_inter_list_to_inter default I :: ('f,'a)poly_inter"
  from check_poly_inter_list[OF check] have 
    main1: "\<And> fn. poly_weak_mono_all (?I fn)" and 
    main2: "\<And> fn. (?I fn) \<ge>p zero_poly" by auto
  note distinct = check_poly_inter_list_distinct[OF check]
  show ?thesis
  proof (unfold_locales, rule main2, rule main1)
    let ?m = "Suc (max_list (map (snd o fst) I))"
    show "\<exists> n. \<forall> f m. n \<le> m \<longrightarrow> ?I (f,m) = default_I default m"
    proof (rule exI[of _ ?m], intro allI impI)
      fix f m 
      assume m: "?m \<le> m"
      show "?I (f,m) = default_I default m" 
      proof (cases "map_of I (f, m)")
        case None then show ?thesis 
          by (simp add: poly_inter_list_to_inter_def)
      next
        case (Some p)
        from map_of_SomeD[OF this] have "((f,m),p) \<in> set I" .
        then have "m \<in> set (map (snd o fst) I)" by force
        from max_list[OF this] m show ?thesis by auto
      qed
    qed
  next
    fix fn 
    let ?map2 = "(map (\<lambda>(fn, e). (fn, poly_vars e)) I)"
    show "poly_vars (poly_inter_list_to_inter default I fn)
          \<subseteq> poly_inter_to_af I fn"
    proof (cases "map_of I fn")
      case None 
      then have "fn \<notin> fst ` set I" unfolding map_of_eq_None_iff .
      then have "fn \<notin> fst ` set ?map2" by auto
      then have None2: "map_of ?map2 fn = None" unfolding map_of_eq_None_iff .
      show ?thesis 
        by (simp add: poly_inter_list_to_inter_def poly_inter_to_af_def None None2)
    next
      case (Some p)
      from map_of_SomeD[OF this] have "(fn,p) \<in> set I" .
      then have mem: "(fn, poly_vars p) \<in> set ?map2" by auto
      from distinct have "distinct (map fst ?map2)" by (induct I, auto)
      from map_of_is_SomeI[OF this mem] have Some2: "map_of ?map2 fn = Some (poly_vars p)" by auto
      show ?thesis
        by (simp add: poly_inter_list_to_inter_def poly_inter_to_af_def Some Some2)
    qed
  qed
qed
end

definition check_ns :: "('f,'a :: {showl,poly_carrier})poly_inter \<Rightarrow> ('f :: showl ,'v :: {showl, linorder})rule \<Rightarrow> showsl check" where
  "check_ns I \<equiv> (\<lambda> (s,t). let p = eval_term I s; q = eval_term I t in check (check_poly_ge p q) 
    (showsl (STR ''could not ensure '') \<circ> showsl s \<circ> showsl (STR '' >= '') \<circ> showsl t 
    \<circ> showsl (STR '' since we\<newline>could not ensure '') \<circ> showsl_poly p \<circ> showsl (STR '' >= '') \<circ> showsl_poly q))"

definition check_s :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('f,'a :: {showl,poly_carrier})poly_inter \<Rightarrow> ('f :: showl ,'v :: {showl, linorder})rule \<Rightarrow> showsl check" where
  "check_s gt I \<equiv> (\<lambda> (s,t). let p = eval_term I s; q = eval_term I t in check (check_poly_gt gt p q) 
    (showsl (STR ''could not ensure '') \<circ> showsl s \<circ> showsl (STR '' > '') \<circ> showsl t 
    \<circ> showsl (STR '' since we\<newline>could not ensure '') \<circ> showsl_poly p \<circ> showsl (STR '' > '') \<circ> showsl_poly q))"

context 
  fixes I :: "('f :: showl,'a :: {showl,poly_carrier})poly_inter" and st :: "('f,'v ::{showl,linorder})rule"
begin
lemma check_ns: 
  assumes check: "isOK (check_ns I st)" and "pre_poly_order d gt power_mono discrete I F"
  shows "st \<in> pre_poly_order.inter_ns I"
proof -
  obtain s t where st: "st = (s,t)" by force
  interpret pre_poly_order d gt power_mono discrete I F by fact
  from check[unfolded check_ns_def Let_def st] have "check_poly_ge (eval_term I s) (eval_term I t)" by auto
  from check_poly_ge[OF this] show "st \<in> inter_ns" unfolding st inter_ns_def by simp
qed

lemma check_s: 
  assumes check: "isOK (check_s gt I st)" and "pre_poly_order d gt power_mono discrete I F"
  shows "st \<in> pre_poly_order.inter_s gt I"
proof -
  obtain s t where st: "st = (s,t)" by force
  interpret pre_poly_order d gt power_mono discrete I F by fact
  from check[unfolded check_s_def Let_def st] have "check_poly_gt gt (eval_term I s) (eval_term I t)" by auto
  from check_poly_gt[OF this] show "st \<in> inter_s" unfolding inter_s_def st by simp
qed
end

definition check_ge_v :: "'a :: poly_carrier \<Rightarrow> (nat,'a) poly \<Rightarrow> bool"
  where "check_ge_v v p \<equiv> case p of Nil \<Rightarrow> True | Cons (m,c) Nil \<Rightarrow> m = 1 \<and> v \<ge> c | _ \<Rightarrow> False"

fun strongly_linear :: "nat \<Rightarrow> (nat,'a) poly \<Rightarrow> ('a :: poly_carrier) \<Rightarrow> bool"
where 
  "strongly_linear 0 p v = check_ge_v v p"
| "strongly_linear (Suc x) p v = (let (a,p') = poly_split (var_monom x) p 
     in 1 \<ge> a \<and> strongly_linear x p' v)"

lemma poly_vars_empty: 
  assumes "check_ge_v v p"
  shows "poly_vars p = {}"
proof (cases p)
  case (Cons mc q)
  note cons = this
  then show ?thesis 
  proof (cases mc)
    case (Pair m c)
    from assms[unfolded cons Pair check_ge_v_def, simplified]
    have "q = []" "m = 1" "c \<le> v" by (auto split: list.splits)
    then show ?thesis unfolding cons Pair by (simp add: poly_vars_def)
  qed
qed (simp add: poly_vars_def)


locale strongly_linear_poly_order = poly_order + 
  fixes F :: "('b \<times> nat) set"
  and v :: 'a
  assumes strongly_linear: "\<And> f n. (f,n) \<in> F \<Longrightarrow> strongly_linear n (I (f,n)) v"
  and v: "v \<ge> 0"
begin

lemma check_ge_v: 
  assumes "check_ge_v v p"
  shows "[(1,v)] \<ge>p p"
proof (cases p)
  case Nil
  then show ?thesis using v unfolding poly_ge_def by simp
next
  case (Cons mc q)
  obtain m c where mc: "mc = (m,c)" by force
  from assms[unfolded Cons mc check_ge_v_def, simplified]
  have "q = []" "m = 1" "c \<le> v" by (auto split: list.splits)
  then show ?thesis unfolding Cons mc by (auto simp: poly_ge_def)
qed

lemma strongly_linear_poly_vars: 
  "strongly_linear x p v \<Longrightarrow> poly_vars p \<subseteq> { i. i < x}"
proof (induction x arbitrary: p)
  case 0
  then have "check_ge_v v p" by simp
  then have empty: "poly_vars p = {}" using poly_vars_empty by auto
  then show ?case by auto
next
  case (Suc x)
  note sl = Suc.prems[simplified, unfolded poly_split_def]
  show ?case 
  proof (cases "List.extract (\<lambda>(n, _). var_monom x = n) p")
    case None
    from None[unfolded extract_None_iff] sl[unfolded None, simplified] Suc.IH[of p] show ?thesis by auto
  next
    case (Some res)
    obtain bef y c aft where res: "res = (bef,(y,c),aft)" by (cases res, auto)
    note some = extract_SomeE[OF Some[unfolded res], simplified]
    from sl[unfolded Some res, simplified] Suc.IH[of "bef @ aft"] have ba: "poly_vars (bef @ aft) \<subseteq> {i. i < x}" by auto
    then have ba: "poly_vars (bef @ aft) \<subseteq> {i. i < Suc x}" by auto
    with some have "var_monom x = y" by force
    then have y: "poly_vars [(y,c)] = {x}" unfolding poly_vars_def by force
    then have y: "poly_vars [(y,c)] \<subseteq> {i. i < Suc x}" by force
    from some have p: "p = bef @ [(y, c)] @ aft" by simp
    show ?thesis using ba y unfolding p poly_vars_def by force
  qed
qed

lemma linear_bound: 
  assumes "funas_term (t :: ('b,'c :: linorder)term) \<subseteq> F"
  shows "of_nat (term_size t) * v \<ge> eval_poly (\<lambda> _. 0) (eval_term I t)"
  using assms
proof (induction t)
  case (Var x)
  have "of_nat 1 * v \<ge> 0" by (rule mult_ge_zero[OF of_nat_ge_zero v])
  then show ?case by simp
next
  case (Fun f ts)
  let ?e = "\<lambda> t. eval_poly (\<lambda> _. 0) (eval_term I t)"
  {
    fix t :: "('b, 'c) term"
    assume t: "t \<in> set ts"
    from Fun.prems(1) t have F: "funas_term t \<subseteq> F" by auto
    from Fun.IH[OF t F] have "of_nat (term_size t) * v \<ge> ?e t" .
  } note IH = this
  let ?f = "(f,length ts)"
  obtain p where If: "I ?f = p" by auto
  from Fun.prems have "?f \<in> F" by auto
  from strongly_linear[OF this] If have sl: "strongly_linear (length ts) p v" by simp
  have "of_nat (term_size (Fun f ts)) * v = (1 + of_nat (sum_list (map term_size ts))) * v"
    by (simp add: ac_simps)
  also have "\<dots> = of_nat (sum_list (map term_size ts)) * v + v" by (simp add: field_simps)
  also have "of_nat (sum_list (map term_size ts)) * v = sum_list (map (\<lambda> t. of_nat (term_size t) * v) ts)"
    by (induct ts, auto simp: field_simps)
  also have "sum_list (map (\<lambda> t. of_nat (term_size t) * v) ts) + v \<ge> sum_list (map ?e ts) + v"
  proof (rule plus_left_mono, rule sum_list_ge_mono, unfold length_map)
    fix i
    assume i: "i < length ts"
    then have mem: "ts ! i \<in> set ts" by simp
    have "map (\<lambda> t. of_nat (term_size t) * v) ts ! i = of_nat (term_size (ts ! i)) * v"
      using i by simp
    also have "\<dots> \<ge> ?e (ts ! i)" (is "_ \<ge> ?res") by (rule IH[OF mem]) 
    also have "?res = map ?e ts ! i" using i by simp
    finally show "map (\<lambda> t. of_nat (term_size t) * v) ts ! i \<ge> map ?e ts ! i" .
  qed simp
  finally have ge: "of_nat (term_size (Fun f ts)) * v \<ge> sum_list (map ?e ts) + v" .
  let ?e2 = "\<lambda> p ts. eval_poly (\<lambda> _ . 0 :: 'a) (poly_subst ( \<lambda> i. if i < length ts then map (eval_term I) ts ! i else zero_poly) p)"
  have id: "?e (Fun f ts) = ?e2 p ts" by (simp add: Let_def If (* poly_subst *))
  have "sum_list (map ?e ts) + v \<ge> ?e2 p ts" using sl
  proof (induction ts arbitrary: p rule: List.rev_induct)
    case Nil
    then have ge: "check_ge_v v p" by simp
    have pos: "pos_assign (\<lambda>v. eval_poly (\<lambda>_. 0 :: 'a) zero_poly)" unfolding pos_assign_def by (simp add: zero_poly_def ge_refl)
    from check_ge_v[OF ge] have "[(1, v)] \<ge>p p" by simp
    from this[unfolded poly_ge_def, rule_format, OF pos]
    show ?case by (simp add: poly_subst)
  next
    case (snoc t ts)
    obtain a p' where split: "poly_split (var_monom (length ts)) p = (a,p')" by force
    with snoc.prems[simplified] have a: "1 \<ge> a" and p': "strongly_linear (length ts) p' v" by auto
    from snoc.IH[OF p'] have IH: "sum_list (map ?e ts) + v \<ge> ?e2 p' ts" .
    let ?m = "(var_monom (length ts),a)"
    let ?p = "?m # p'"
    from poly_split[OF split] have p: "p =p ?p" .
    have "?e2 p (ts @ [t]) = ?e2 (?m # p') (ts @ [t])" unfolding poly_subst
      using p unfolding eq_poly_def by blast
    also have "... = ?e2 [?m] (ts @ [t]) + ?e2 p' (ts @ [t])"
      by (simp add: poly_subst.simps zero_poly_def) 
    also have "?e2 [?m] (ts @ [t]) = a * ?e t"
      by (simp add: poly_subst.simps nth_append zero_poly_def)
    also have "?e2 p' (ts @ [t]) = ?e2 p' ts"
    proof (rule arg_cong[where f = "eval_poly (\<lambda> _ . 0)"], rule poly_vars)
      fix x
      assume x: "x \<in> poly_vars p'"
      from snoc(2) split have "strongly_linear (length ts) p' v" by simp 
      from strongly_linear_poly_vars[OF this] x have "x < length ts" by auto
      then show "(if x < length (ts @ [t]) then map (eval_term I) (ts @ [t]) ! x else zero_poly) =
        (if x < length ts then map (eval_term I) ts ! x else zero_poly)"
        using nth_append[of "map (eval_term I) ts" "[eval_term I t]" x] by simp
    qed
    finally have id: "?e2 p (ts @ [t]) = a * ?e t + ?e2 p' ts" .
    have "sum_list (map ?e (ts @ [t])) + v = ?e t + (sum_list (map ?e ts) + v)"
      by (simp add: field_simps)
    also have "\<dots> \<ge> ?e t + ?e2 p' ts" (is "_ \<ge> ?res")
      by (rule plus_right_mono[OF IH])
    also have "?res \<ge> a * ?e t + ?e2 p' ts" (is "_ \<ge> ?res")
    proof (rule plus_left_mono)
      have 2: "pos_assign (\<lambda>_. 0 :: 'a)" unfolding pos_assign_def by (simp add: ge_refl)
      have 3: "eval_term I t \<ge>p zero_poly" using eval_term_pos[of t] .
      have 1: "?e t \<ge> (0 :: 'a)" using pos_assign_poly[OF 2 3] .
      show "?e t \<ge> a * ?e t" using times_left_mono[OF 1 a] by simp
    qed
    also have "?res = ?e2 p (ts @ [t])" unfolding id ..
    finally show "sum_list (map ?e (ts @ [t])) + v \<ge> ?e2 p (ts @ [t])" .
  qed
  with IH[of t] id ge ge_trans show ?case by simp
qed

lemma degree_bound:
  assumes FF: "set FF = F" 
  and t: "(t :: ('b,'c :: linorder)term) \<in> terms_of_nat (Runtime_Complexity FF D) n"
  and v1: "v \<ge> 1"
  and deg: "\<And> d. d \<in> set D \<Longrightarrow> deg \<ge> poly_degree (I d)"
  and c: "\<And> d. d \<in> set D \<Longrightarrow> c \<ge> poly_coeff_sum (I d)" 
  shows "(c * v ^ deg) * of_nat n ^ deg \<ge> eval_poly (\<lambda> _. 0) (eval_term I t)"
proof -
  from t FF have "is_Fun t" "the (root t) \<in> set D" "\<And> s. s \<in> set (args t) \<Longrightarrow> funas_term s \<subseteq> F"
    and size: "term_size t \<le> n" by (auto simp: funas_args_term_def)
  then obtain f ts where t: "t = Fun f ts" and f: "(f,length ts) \<in> set D" and ts: "\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F" by (cases t, auto)
  let ?f = "(f,length ts)"
  let ?zass = "(\<lambda> _. 0) :: ('c,'a)assign" 
  let ?e = "\<lambda> t :: ('b,'c)term. eval_poly ?zass (eval_term I t)"
  {
    fix t
    assume mem: "t \<in> set ts"
    then have "term_size t \<le> term_size (Fun f ts)" by (induct ts, auto)
    with size[unfolded t] have size: "term_size t \<le> n" by simp
    from linear_bound[OF ts[OF mem]] 
    have "of_nat (term_size t) * v \<ge> ?e t" .
    from ge_trans[OF times_left_mono[OF v of_nat_mono[OF size]] this]
    have "of_nat n * v \<ge> eval_poly ?zass (eval_term I t)" .
  } note args = this
  have nv0: "of_nat n * v \<ge> 0" by (rule mult_ge_zero[OF of_nat_ge_zero v])
  have zass: "pos_assign ?zass" unfolding pos_assign_def using ge_refl by simp
  let ?p = "\<lambda>i. if i < length ts then map (eval_term I) ts ! i else zero_poly"
  have "eval_poly ?zass (poly_subst (\<lambda>i. [(1,of_nat n * v)]) (I ?f)) \<ge> eval_poly ?zass (poly_subst ?p (I ?f))" 
    (is "_ \<ge> ?res")
    unfolding poly_subst
  proof (rule mono_I[of ?f, unfolded poly_weak_mono_all_def, rule_format])
    fix i
    have "eval_poly ?zass [(1, of_nat n * v)] = of_nat n * v" by simp 
    also have "\<dots> \<ge> eval_poly ?zass (?p i)"
    proof (cases "i < length ts")
      case False
      then have "eval_poly ?zass (?p i) = 0" unfolding zero_poly_def by simp
      then show ?thesis using nv0 by simp
    next
      case True
      then have id: "eval_poly ?zass (?p i) = ?e (ts ! i)" by simp
      show ?thesis unfolding id
        by (rule args, insert True, auto)
    qed
    finally show "eval_poly ?zass [(1, of_nat n * v)] \<ge> eval_poly ?zass (?p i)" .
  next
    show "pos_assign (\<lambda>v. eval_poly ?zass (?p v))" 
      unfolding pos_assign_def
    proof
      fix i
      show "eval_poly ?zass (?p i) \<ge> 0"
      proof (cases "i < length ts")
        case False
        then show ?thesis unfolding zero_poly_def using ge_refl by simp
      next
        case True
        then have "eval_poly ?zass (?p i) = ?e (ts ! i)" by simp
        also have "\<dots> \<ge> 0"
          by (rule pos_assign_poly[OF zass eval_term_pos])
        finally show "eval_poly ?zass (?p i) \<ge> 0" .
      qed
    qed
  qed
  also have "?res = ?e t" 
    unfolding t eval_term.simps Let_def ..
  finally have "eval_poly ?zass (poly_subst (\<lambda>i. [(1,of_nat n * v)]) (I ?f)) \<ge> ?e t" .
  from this[unfolded poly_subst] have ge1: "eval_poly (\<lambda>_. of_nat n * v) (I ?f) \<ge> ?e t" by simp
  from size[unfolded t] have n: "n \<ge> 1" by simp
  have nv1: "of_nat n * v \<ge> 1"
    by (rule mult_ge_one[OF of_nat_mono[OF n, unfolded of_nat_1] v1])
  from poly_degree_bound[OF nv1 c[OF f] deg[OF f]] have ge2: "c * (of_nat n * v) ^ deg \<ge> eval_poly (\<lambda>_. of_nat n * v) (I ?f)" .
  from ge_trans[OF ge2 ge1] have "c * (of_nat n * v) ^ deg \<ge> ?e t" .
  also have "(of_nat n * v) ^ deg = v ^ deg * of_nat n ^ deg" by (induct deg, auto simp: field_simps)
  finally 
  show "(c * v ^ deg) * of_nat n ^ deg \<ge> ?e t" by (simp add: field_simps)
qed
end

definition sl_complexity_sig_check :: "('f,'a :: poly_carrier)poly_inter \<Rightarrow> 'a \<Rightarrow> ('f \<times> nat)list \<Rightarrow> ('f \<times> nat) check" where 
  "sl_complexity_sig_check I v F \<equiv> do {
       check_allm (\<lambda> (f,n). check (strongly_linear n (I (f,n)) v) (f,n)) F
    }"

definition max_v :: "'a \<Rightarrow> ('f,'a :: {ord,zero})poly_inter \<Rightarrow> ('f \<times> nat)list \<Rightarrow> 'a" where
  "max_v v I fs \<equiv> max v (foldr (\<lambda> f m. max m (fst (poly_split 1 (I f)))) fs 0)"

lemma max_v_v: "max_v (v :: 'a :: ordered_semiring_1) I fs \<ge> v" unfolding max_v_def by (rule max_ge_x)

definition sl_complexity_check :: "'a \<Rightarrow> ('f :: showl,'a :: {poly_carrier,ord})poly_inter \<Rightarrow> ('f \<times> nat)list \<Rightarrow> showsl check" where
  "sl_complexity_check v I F \<equiv> do {
     let w = max_v v I F;
     sl_complexity_sig_check I w F 
       <+? (\<lambda> (f,n). showsl (STR ''symbol '') \<circ> showsl f \<circ> showsl (STR '' does not possess a strongly linear interpretation''))
   }"

fun nl_complexity_check (* :: "('f :: show,'a :: poly_carrier)poly_inter \<Rightarrow> *) where
  "nl_complexity_check I (Derivational_Complexity F) cc = (do { 
    sl_complexity_check 0 I F; 
    check (Comp_Poly 1 \<le> cc) (showsl (STR ''cannot deduce constant complexity for derivational complexity''))
  })"
| "nl_complexity_check I (Runtime_Complexity C D) (Comp_Poly deg) = (do { 
    sl_complexity_check 1 I C; 
    check_allm (\<lambda> f. check (poly_degree (I f) \<le> deg) 
      (showsl (STR ''degree of interpretation for '') o showsl f o showsl (STR '' exceeds bound ''))) D
  }
  )"

definition create_nlpoly_rel_impl :: "showsl check \<Rightarrow> 'a :: {showl,poly_carrier} \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('f,'a)poly_inter_list \<Rightarrow> ('f :: {compare_order,showl},'v :: {showl,linorder})rel_impl"
where "create_nlpoly_rel_impl cI def gt power_mono discrete I = (let 
   J = poly_inter_list_to_inter def I;
   x = poly_subst (\<lambda> n. poly_of (PVar (''x_'' @ show n))) \<comment> \<open>do not use String.literal at this point, as this will break code-gen\<close>
   in \<lparr>
    rel_impl.valid = do {cI ;  check_poly_inter_list discrete I <+? 
      case_sum id (\<lambda> (f,p). showsl (STR ''interpretation '') \<circ> showsl_poly (x p) \<circ> showsl (STR '' of '') \<circ> showsl f \<circ> showsl (STR '' invalid ''))},
    standard = succeed,
    desc = showsl (STR ''polynomial interpretation\<newline>'') \<circ> showsl_sep (\<lambda> ((f,n),p) . 
        showsl (STR ''Pol('') \<circ> showsl f \<circ> showsl (STR ''/'') \<circ> showsl n \<circ> showsl (STR '') = '') \<circ> showsl_poly (x p))
        showsl_nl I, 
    s = check_s gt J,
    ns = check_ns J, 
    nst = check_ns J,
    af = poly_inter_to_af I,
    top_af = poly_inter_to_af I,
    SN = succeed,
    subst_s = succeed,
    ce_compat = succeed,
    co_rewr = succeed,
    top_mono = succeed,
    top_refl = succeed,
    mono_af = poly_inter_to_mono_af discrete power_mono gt I,
    mono = (\<lambda> _. check_all (\<lambda> ((f,n),p). list_all (\<lambda> i. check_poly_strict_mono_smart discrete power_mono gt p i) [0 ..< n]) I 
      <+? (\<lambda> ((f,n),p). showsl (STR ''could not ensure monotonicty of '') \<circ> showsl_poly (x p) \<circ> 
       showsl (STR '' as interpretation of '') \<circ> showsl f)),
    not_wst = Some (map fst I),
    not_sst = Some (map fst I),
    cpx = nl_complexity_check J\<rparr>)"

lemma poly_order_carrier_with_create_nlpoly_rel_impl: 
  assumes cpx: "isOK cI \<Longrightarrow> cpx_poly_order_carrier def gt power_mono discrete bound"
  shows "rel_impl (create_nlpoly_rel_impl cI def gt power_mono discrete I :: ('f :: {compare_order,showl},'v :: {linorder, showl})rel_impl)" 
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 U)
  let ?rp = "create_nlpoly_rel_impl cI def gt power_mono discrete I :: ('f,'v)rel_impl"
  let ?af = "rel_impl.af ?rp :: 'f af"
  let ?af' = "rel_impl.mono_af ?rp"
  let ?cpx = "rel_impl.cpx ?rp"
  let ?cpx' = "\<lambda> cm cc. isOK(?cpx cm cc)"
  note [simp] = create_nlpoly_rel_impl_def Let_def
  have top_af: "rel_impl.top_af ?rp = ?af" by auto
  note valid = 1(1)
  from valid have valid: "isOK(check_poly_inter_list discrete I)" and cI: "isOK cI" by auto
  note distinct = check_poly_inter_list_distinct[OF valid]
  from cpx[OF cI] interpret cpx_poly_order_carrier def gt power_mono discrete bound .
  let ?J = "poly_inter_list_to_inter def I"
  from ce_poly_order[OF valid] interpret ce_poly_order def gt power_mono discrete ?J bound ?af by simp 
  let ?S = "inter_s :: ('f,'v)trs" 
  let ?NS = "inter_ns :: ('f,'v)trs" 
  have pre: "pre_poly_order def gt power_mono discrete ?J {}" by (unfold_locales, auto)
  have cpx: "?cpx = nl_complexity_check ?J" by simp
  have mrp: "ce_af_redtriple_order ?S ?NS ?NS ?af" ..
  show ?case unfolding top_af
  proof (rule exI[of _ ?S], intro exI[of _ ?NS] conjI impI allI
       trans_NS trans_S top_mono_same refl_NS SN S_imp_NS ctxt_NS compat_S_NS compat_NS_S subst_NS subst_S af_compat)
    show "isOK (rel_impl.s ?rp st) \<Longrightarrow> st \<in> inter_s" for st 
      by (intro check_s[OF _ pre], auto)
    show "isOK (rel_impl.ns ?rp st) \<Longrightarrow> st \<in> inter_ns" for st 
      by (intro check_ns[OF _ pre], auto)
    show "isOK (rel_impl.nst ?rp st) \<Longrightarrow> st \<in> inter_ns" for st 
      by (intro check_ns[OF _ pre], auto)
    show "irrefl ?S" using SN irrefl_on_def by fastforce
    from co_rewrite_irrefl[OF this compat_NS_S] show "?NS \<inter> ?S^-1 = {}" .
    show "ce_compatible ?S" "ce_compatible ?NS"
      using ce_compat unfolding ce_compatible_def by blast+
    show "af_monotone ?af' ?S"
    proof (rule poly_strict_mono_imp_af_monotone)
      fix f n i
      assume i_n: "i < n"
      and i: "i \<in> ?af' (f,n)"
      show "poly_strict_mono (?J (f,n)) i"
      proof (cases "map_of I (f,n)")
        case None
        then have J: "?J (f,n) = default_I def n" 
          unfolding poly_inter_list_to_inter_def by auto
        show ?thesis unfolding J
          by (rule check_poly_strict_mono, 
          rule default_I_check_poly_strict_mono[OF i_n],
          rule default_I_check_poly_weak_mono[OF default_ge_zero])
      next
        case (Some e)
        let ?f = "\<lambda> n p. {x. x < n \<and> check_poly_weak_mono_and_pos discrete p \<and> check_poly_strict_mono_smart discrete power_mono gt p x}"
        let ?map2 = "(map (\<lambda>((f, n), e). ((f, n), ?f n e)) I)"
        from Some have "((f,n),e) \<in> set I" by (rule map_of_SomeD)
        then have mem: "((f,n),?f n e) \<in> set ?map2" by force
        have "map fst I = map fst ?map2" by (induct I, auto)
        with distinct have distinct: "distinct (map fst ?map2)" by simp
        from Some have J: "?J (f,n) = e" unfolding poly_inter_list_to_inter_def by auto
        have "?af' (f,n) = poly_inter_to_mono_af discrete power_mono gt I (f, n)" 
          by simp
        also have "\<dots> = ?f n e" unfolding poly_inter_to_mono_af_def
          using map_of_is_SomeI[OF distinct mem] by simp
        finally have "?af' (f,n) = ?f n e" by simp
        from i[unfolded this] show ?thesis unfolding J
          by (intro check_poly_strict_mono_smart, auto)
      qed
    qed
    {
      fix sig
      assume "isOK(rel_impl.mono ?rp sig)" "funas_trs (set U) \<subseteq> set sig" 
      hence mono: "isOK(rel_impl.mono ?rp (funas_trs_list U))" 
        by auto
      interpret mono_poly_order def gt power_mono discrete ?J bound ?af
      proof
        fix f :: 'f and  n i :: nat
        assume i: "i < n" 
        show "poly_strict_mono (?J (f,n)) i"
        proof (cases "map_of I (f, n)")
          case None
          then have d: "?J (f,n) = default_I def n" unfolding poly_inter_list_to_inter_def by auto
          show ?thesis 
            by (simp only: d, rule check_poly_strict_mono, rule default_I_check_poly_strict_mono[OF i], rule default_I_check_poly_weak_mono[OF default_ge_zero])
        next
          case (Some p)
          then have p: "?J (f,n) = p" and fnp: "((f,n),p) \<in> set I" unfolding poly_inter_list_to_inter_def using map_of_SomeD[OF Some] by auto
          show ?thesis
          proof (simp only: p, 
              rule check_poly_strict_mono_smart[OF mono[simplified, unfolded check_poly_inter_list_def list_all_iff, THEN bspec[OF _ fnp], simplified, THEN bspec]])
            show "i \<in> {0..<n}" by (simp add: i)
          next 
            from valid[unfolded check_poly_inter_list_def] fnp
            show "check_poly_weak_mono_and_pos discrete p" by auto
          qed
        qed
      qed
      show "ctxt.closed ?S" by (rule inter_s_mono)
    }
    {
      fix f n i 
      assume "(f, n) \<notin> fst ` set I" 
      from this[folded map_of_eq_None_iff]
      have d: "?J (f,n) = default_I def n" unfolding poly_inter_list_to_inter_def by auto
      have "simple_arg_pos ?S (f, n) i \<and> simple_arg_pos ?NS (f, n) i" 
      proof (intro conjI simple_arg_posI)
        fix ts :: "('f,'v)term list"
        assume n: "length ts = n" and i: "i < n"
        then have mem: "ts ! i \<in> set ts" by auto
        show "(Fun f ts, ts ! i) \<in> ?S"
          by (rule default_imp_s[OF refl mem], insert n d, auto)
        with S_imp_NS
        show "(Fun f ts, ts ! i) \<in> ?NS" by blast
      qed 
    } 
    then show "not_subterm_rel_info ?NS (rel_impl.not_wst ?rp)" "not_subterm_rel_info ?S (rel_impl.not_sst ?rp)" 
      by auto    
    {
      fix cm cc
      assume "?cpx' cm cc"
      then have nlc: "isOK(nl_complexity_check ?J cm cc)" unfolding cpx .
      let ?v = "\<lambda> v F. max_v v ?J F"
      have vge: "\<And> v F. ?v v F \<ge> v" by (rule max_v_v)
      {
        fix F and v :: 'a
        assume v0: "v \<ge> 0"
        from ge_trans[OF vge v0] have v: "?v v F \<ge> 0" .
        assume "isOK(sl_complexity_check v ?J F)"
        note sl = this[unfolded sl_complexity_check_def Let_def sl_complexity_sig_check_def, simplified]
        have "strongly_linear_poly_order def gt power_mono discrete ?J bound ?af (set F) (?v v F)"
          by (unfold_locales, insert sl v, auto)
      } note slo = this
      define ev where "ev = (\<lambda> t :: ('f,'v)term. eval_poly (\<lambda>_. 0) (eval_term ?J t))"
      have pos: "pos_assign ((\<lambda> _. 0) :: ('v,'a)assign)" unfolding pos_assign_def using ge_refl by auto
      let ?S = "{(a,b). b \<ge> 0 \<and> gt a b}"
      show "deriv_bound_measure_class (pre_poly_order.inter_s gt ?J) cm cc" 
      proof (cases cm)
        case (Derivational_Complexity F)
        from nlc[unfolded this nl_complexity_check.simps]
        have sl: "isOK(sl_complexity_check 0 (poly_inter_list_to_inter def I) F)" 
          and "Comp_Poly 1 \<le> cc" by auto
        then have O_of: "O_of (Comp_Poly 1) \<subseteq> O_of cc" by auto
        let ?V = "?v 0 F"
        from slo[OF ge_refl sl] have
          "strongly_linear_poly_order def gt power_mono discrete ?J bound ?af (set F) ?V" .
        interpret strongly_linear_poly_order def gt power_mono discrete ?J bound ?af "set F" ?V by fact
        {
          fix n t
          assume "t \<in> terms_of_nat cm n"
          from this[unfolded Derivational_Complexity] have tF: "funas_term t \<subseteq> set F" and tn: "term_size t \<le> n" by auto
          from ge_trans[OF times_left_mono[OF v of_nat_mono[OF tn]] linear_bound[OF tF]]
          have "of_nat n * ?V \<ge> ev t" unfolding ev_def .
        } note linear = this
        let ?bnd = "\<lambda> n :: nat. (bound ?V * n ^ 1 + 0)"
        show ?thesis 
        proof (rule deriv_bound_measure_class_mono[OF subset_refl subset_refl O_of],
            unfold deriv_bound_measure_class_def, rule)
          fix t n
          assume "t \<in> terms_of_nat cm n"
          from linear[OF this] have nv_t: "of_nat n * ?V \<ge> ev t" .
          show "deriv_bound inter_s t (?bnd n)"
          proof (rule deriv_bound_image)
            fix s t :: "('f,'v)term"
            assume "(s,t) \<in> inter_s"
            then show "(ev s, ev t) \<in> ?S^+"
              unfolding inter_s_def poly_gt_def ev_def using pos eval_term_pos[of t] 
              unfolding poly_ge_def zero_poly_def by auto  
          next            
            show "deriv_bound ?S (ev t) (?bnd n)" 
            proof (rule deriv_bound_mono [OF  _ bound])
              have "bound (ev t) \<le> bound (of_nat n * ?V)" by (rule bound_mono[OF nv_t])
              also have "\<dots> \<le> n * bound ?V" by (rule bound_of_nat_times)
              also have "\<dots> = ?bnd n" by simp
              finally show "bound (ev t) \<le> ?bnd n" .
            qed
          qed          
        qed
      next
        case (Runtime_Complexity C D)
        obtain deg where cc: "cc = Comp_Poly deg" by (cases cc, auto)
        define c where "c = (foldr max (map (\<lambda> f. poly_coeff_sum (?J f)) D) 0)"
        define e where "e = c * max_v 1 (poly_inter_list_to_inter def I) C ^ deg"
        let ?V = "?v 1 C"
        from nlc[unfolded Runtime_Complexity nl_complexity_check.simps cc, simplified]
        have sl: "isOK(sl_complexity_check 1 ?J C)" 
          and deg: "\<And> f . f \<in> set D \<Longrightarrow> poly_degree (?J f) \<le> deg" by auto
        from slo[OF one_ge_zero sl] have 
          "strongly_linear_poly_order def gt power_mono discrete ?J  bound ?af (set C) ?V" .
        interpret strongly_linear_poly_order def gt power_mono discrete ?J bound ?af "set C" ?V by fact
        {
          fix d
          assume d: "d \<in> set D"
          then have "c \<ge> poly_coeff_sum (?J d)" unfolding c_def
          proof (induct D)
            case Nil then show ?case by simp
          next
            case (Cons e D)
            show ?case
            proof (cases "e = d")
              case False
              with Cons(2) have "d \<in> set D" by auto
              from ge_trans[OF max_ge_y Cons(1)[OF this]]
              show ?thesis by simp
            next
              case True
              then show ?thesis using max_ge_x by auto
            qed
          qed
        } note c = this
        {
          fix n t
          assume "t \<in> terms_of_nat cm n"
          from degree_bound[OF refl this[unfolded Runtime_Complexity] vge deg c]
          have "e * of_nat n ^ deg \<ge> ev t" unfolding ev_def e_def by simp
        } note endeg_t = this
        let ?bnd = "\<lambda> n :: nat. (bound e * n ^ deg + 0)"
        show ?thesis
          unfolding deriv_bound_measure_class_def cc 
        proof rule
          fix t n
          assume t: "t \<in> terms_of_nat cm n"
          show "deriv_bound inter_s t (?bnd n)"
          proof (rule deriv_bound_image)
            fix s t :: "('f,'v)term"
            assume "(s,t) \<in> inter_s"
            then show "(ev s, ev t) \<in> ?S^+"
              unfolding inter_s_def poly_gt_def ev_def using pos eval_term_pos[of t] 
              unfolding poly_ge_def zero_poly_def by auto  
          next            
            show "deriv_bound ?S (ev t) (?bnd n)" 
            proof (rule deriv_bound_mono [OF _ bound])
              have "bound (ev t) \<le> bound (e * of_nat n ^ deg)" by (rule bound_mono[OF endeg_t[OF t]])
              also have "\<dots> \<le> bound e * of_nat n ^ deg" by (rule bound_pow_of_nat)
              finally show "bound (ev t) \<le> ?bnd n" by simp
            qed
          qed          
        qed
      qed
    }
  qed 
qed
  
definition
  square_possibilities :: "('a \<Rightarrow> 'a list) \<Rightarrow> ('b :: linorder, 'a :: poly_carrier) poly \<Rightarrow> ('b,'a) poly list"
where
  "\<And> sqrt. square_possibilities sqrt p =
    (let
      roots = (map (\<lambda> x. map (Pair x) (sqrt (fst (poly_split (var_monom x * var_monom x) p)))) (poly_vars_list p));
      choices = if [] \<in> set roots then [] else concat_lists roots;
      polys = map (\<lambda> xas. poly_of (PSum (map (\<lambda>(x, a). PMult [PVar x, PNum a]) xas))) choices
    in polys)"

definition check_quadratic :: "('a \<Rightarrow> 'a list) \<Rightarrow> (nat, 'a :: poly_carrier)poly \<Rightarrow> showsl check"
where
  "\<And> sqrt. check_quadratic sqrt p = do {
    check (poly_degree p = 2) (showsl (STR ''not quadratic''));
    let polys = square_possibilities sqrt p;
    check (\<exists> q \<in> set polys. check_poly_eq (poly_mult q q) p)
     (showsl (STR ''could not find quadratic polynomial''))
  }"

lemma (in non_inf_poly_order_carrier) check_quadratic:
  assumes ok: "isOK (check_quadratic sqrt p)"
  shows "eval_poly \<alpha> p \<ge> 0"
proof -
  let ?e = "eval_poly \<alpha>"
  from ok[unfolded check_quadratic_def Let_def]
  obtain q where q: "check_poly_eq (poly_mult q q) p" by auto
  from check_poly_eq[OF q, unfolded eq_poly_def]
  have "?e p = ?e (poly_mult q q)" by auto
  also have "\<dots> = ?e q * ?e q" by simp
  also have "\<dots> \<ge> 0" by (rule sqr)
  finally show ?thesis .
qed

definition check_quadratic_ge_const :: "('a \<Rightarrow> 'a list) \<Rightarrow> ('f,'a :: poly_carrier)poly_inter \<Rightarrow> ('f,'v :: linorder)rule \<Rightarrow> showsl check" where
  "check_quadratic_ge_const sq I st \<equiv> do {
     let (s,t) = st;
     check (is_Fun s) (showsl (STR ''require non-variables as arguments''));
     let pt = eval_term I t;
     let (c,p0) = poly_split 1 pt;
     check (p0 = zero_poly) (showsl (STR ''rhs must evaluate to constant''));
     let ps = I (the (root s));
     let (d,psx) = poly_split 1 ps;
     check (d \<ge> c) (showsl (STR ''problem in comparing constants''));
     check_quadratic sq psx
     }"

lemma check_quadratic_ge_const: 
  fixes I :: "('f,'a :: poly_carrier)poly_inter" and sqrt  
  assumes ok: "isOK(check_quadratic_ge_const sqrt I st)"
  and "pre_poly_order d gt power_mono discrete I F"
  and "non_inf_poly_order_carrier d gt power_mono discrete"
  shows "st \<in> pre_poly_order.inter_ns I"
proof -
  interpret pre_poly_order d gt power_mono discrete I F by fact
  interpret non_inf_poly_order_carrier d gt power_mono discrete sqrt by fact
  obtain s t where st: "st = (s,t)" by force
  note ok = ok[unfolded check_quadratic_ge_const_def Let_def st, simplified]
  from ok obtain f ss where s: "s = Fun f ss" by (cases s, auto)
  let ?et = "eval_term I t"
  let ?es = "eval_term I s"
  let ?p = "I (f,length ss)"
  obtain c p0 where t: "poly_split 1 ?et = (c,p0)" by force
  with ok have "p0 = []" by (simp add: zero_poly_def)
  note t = t[unfolded this]
  obtain d px where p: "poly_split 1 ?p = (d,px)" by force
  show ?thesis unfolding st inter_ns_def
  proof (rule, unfold split, unfold poly_ge_def, intro allI impI)
    fix \<alpha> :: "'b \<Rightarrow> 'a"
    assume pos: "pos_assign \<alpha>"
    let ?ea = "eval_poly \<alpha>"
    have eat: "?ea ?et = c" using poly_split[OF t] unfolding eq_poly_def by auto
    have "\<exists> \<beta>. ?ea ?es = d + eval_poly \<beta> px" unfolding s eval_term.simps Let_def
      using poly_split[OF p] unfolding eq_poly_def poly_subst by auto
    then obtain \<beta> where eas: "?ea ?es = d + eval_poly \<beta> px" ..
    from ok t s p have dc: "d \<ge> c" and qu: "isOK(check_quadratic sqrt px)" by auto
    from plus_right_mono[OF check_quadratic[OF qu, of \<beta>]] have "?ea ?es \<ge> d" unfolding eas by simp
    from ge_trans[OF this dc]
    show "?ea ?es \<ge> ?ea ?et" unfolding eat .
  qed
qed

fun check_cc :: "('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('f,'a :: {showl,poly_carrier})poly_inter \<Rightarrow> ('f :: showl ,'v :: {showl,linorder})c_constraint \<Rightarrow> showsl check" where
  "check_cc sq gt I (Unconditional_C False st) = (if isOK(check_quadratic_ge_const sq I st) then succeed else check_ns I st)"
| "check_cc sq gt I (Unconditional_C True st) = check_s gt I st"
| "check_cc sq gt I (Conditional_C True (u,v) (s,t)) = (let
    ss = eval_term I s;
    tt = eval_term I t;
    uu = eval_term I u;
    vv = eval_term I v
  in (if check_poly_gt gt ss tt then succeed else
    check (check_poly_ge (poly_add ss vv) (poly_add tt uu)) 
      (showsl (STR ''could not ensure '') \<circ> showsl u \<circ> showsl (STR '' > '') \<circ> showsl v \<circ> showsl (STR '' ==> '') \<circ> 
       showsl s \<circ> showsl (STR '' > '') \<circ> showsl t)))"
| "check_cc sq gt I (Conditional_C False (u,v) (s,t)) = (if isOK(check_quadratic_ge_const sq I (s,t)) then succeed else (let
    ss = eval_term I s;
    tt = eval_term I t;
    uu = eval_term I u;
    vv = eval_term I v
  in (if check_poly_ge ss tt then succeed else
    check (check_poly_ge (poly_add ss vv) (poly_add tt uu)) 
      (showsl (STR ''could not ensure '') \<circ> showsl u \<circ> showsl (STR '' >= '') \<circ> showsl v \<circ> showsl (STR '' ==> '') \<circ> 
       showsl s \<circ> showsl (STR '' >= '') \<circ> showsl t))))"

lemma check_cc:
  fixes I :: "('f :: showl,'a :: {showl,poly_carrier})poly_inter" and cc :: "('f,'v :: {showl,linorder})c_constraint" and sqrt
  assumes check: "isOK (check_cc sqrt gt I cc)" and pre: "pre_poly_order d gt power_mono discrete I F"
    and non: "non_inf_poly_order_carrier d gt power_mono discrete"
  shows "cc_satisfied F (pre_poly_order.inter_s gt I) (pre_poly_order.inter_ns I) cc"
proof -
  interpret pre_poly_order d gt power_mono discrete I F by fact
  interpret non_inf_poly_order_carrier d gt power_mono discrete by fact
  let ?sat = "cc_satisfied F inter_s inter_ns"
  note stable_S = F_subst_closedD[OF F_subst_closed_inter_s]
  note stable_NS = F_subst_closedD[OF F_subst_closed_inter_ns]
  {
    fix s t :: "('f,'v)term"
    assume "isOK(check_s gt I (s,t))"
    from check_s[OF this pre] have s: "(s,t) \<in> inter_s" .
    from stable_S[OF _ this] have "?sat (Unconditional_C True (s,t))" by auto
  } note s = this
  {
    fix s t :: "('f,'v)term"
    assume "isOK(check_ns I (s,t))"
    from check_ns[OF this pre] have s: "(s,t) \<in> inter_ns" .
    from stable_NS[OF _ this] have "?sat (Unconditional_C False (s,t))" by auto
  } note ns = this
  {
    fix s t :: "('f,'v)term"
    assume "isOK(check_quadratic_ge_const sqrt I (s,t))"
    from check_quadratic_ge_const[OF this pre non]
    have s: "(s,t) \<in> inter_ns" .
    from stable_NS[OF _ this] have "?sat (Unconditional_C False (s,t))" by auto
  } note ns2 = this
  show "?sat cc"
  proof (cases cc)
    case (Unconditional_C stri st)
    note cc = this
    obtain s t where st: "st = (s,t)" by force
    show ?thesis
    proof (cases stri)
      case True
      from check cc True st have "isOK(check_s gt I (s,t))" by auto
      from s[OF this] show ?thesis unfolding cc st using True by auto
    next
      case False note nstri = this
      show ?thesis
      proof (cases "isOK(check_quadratic_ge_const sqrt I (s,t))")
        case True
        from ns2[OF this] show ?thesis unfolding cc st using nstri by auto
      next
        case False
        from check cc False nstri st have "isOK(check_ns I (s,t))" by auto
        from ns[OF this] show ?thesis unfolding cc st using nstri by auto
      qed
    qed
  next
    case (Conditional_C stri uv st)
    note cc = this
    obtain s t where st: "st = (s,t)" by force
    obtain u v where uv: "uv = (u,v)" by force
    let ?I = "eval_term I"
    let ?s = "?I s"
    let ?t = "?I t"
    let ?u = "?I u"
    let ?v = "?I v"
    note check = check[unfolded cc st uv]
    show ?thesis
    proof (cases stri)
      case True
      then have stri: "stri = True" by auto
      with check have "check_poly_gt gt ?s ?t \<or> check_poly_ge (poly_add ?s ?v) (poly_add ?t ?u)" 
        by (cases "check_poly_gt gt ?s ?t", auto simp: Let_def)
      then show ?thesis
      proof
        assume "check_poly_gt gt ?s ?t"
        then have "isOK(check_s gt I (s,t))" unfolding check_s_def by auto
        from s[OF this] show ?thesis unfolding cc st uv stri by auto
      next
        assume "check_poly_ge (poly_add ?s ?v) (poly_add ?t ?u)"
        from check_poly_ge[OF this] 
        have "poly_add (eval_term I s) (eval_term I v) \<ge>p poly_add (eval_term I t) (eval_term I u)" by auto
        then have ge: "\<And> \<alpha>. pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (eval_term I s) + eval_poly \<alpha> (eval_term I v) \<ge>
          (eval_poly \<alpha> (eval_term I t) + eval_poly \<alpha> (eval_term I u))" unfolding poly_ge_def by auto
        let ?inter_s = "inter_s :: ('f,'v)trs"
        show ?thesis unfolding cc uv st stri cc_satisfied.simps if_True
        proof (intro allI impI)
          fix \<sigma> 
          assume F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" and s: "(u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> ?inter_s"
          from s[unfolded inter_s_def] have s: "\<And> \<alpha>. pos_assign \<alpha> \<Longrightarrow> gt (eval_poly \<alpha> (?I (u \<cdot> \<sigma>))) (eval_poly \<alpha> (?I (v \<cdot> \<sigma>)))"
            unfolding poly_gt_def by auto
          have "?I (s \<cdot> \<sigma>) >p ?I (t \<cdot> \<sigma>)" unfolding poly_gt_def
          proof(intro allI impI)
            fix \<alpha> :: "('v,'a)assign"
            let ?\<sigma> = "(\<lambda>x. eval_poly \<alpha> (eval_term I (\<sigma> x)))"
            define J where "J = (\<lambda> t. eval_poly ?\<sigma> (?I t))"
            assume pos: "pos_assign \<alpha>"
            from pos_assign_F_subst[OF F pos] have poss: "pos_assign ?\<sigma>" .
            from s[OF pos, unfolded inter_stable] have gt: "gt (J u) (J v)" unfolding J_def .
            from ge[OF poss] have ge: "(J s + J v) \<ge> (J t + J u)" unfolding J_def .
            from ge gt have "gt (J s) (J t)" by (rule cond_gt)
            then show "gt (eval_poly \<alpha> (?I (s \<cdot> \<sigma>))) (eval_poly \<alpha> (?I (t \<cdot> \<sigma>)))"
              unfolding inter_stable J_def .
          qed
          then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> inter_s" unfolding inter_s_def by simp
        qed
      qed
    next
      case False
      then have stri: "stri = False" by auto
      show ?thesis
      proof (cases "isOK(check_quadratic_ge_const sqrt I (s,t))")
        case True
        from ns2[OF this] show ?thesis unfolding cc st stri uv by auto
      next
        case False
        with check stri have "check_poly_ge ?s ?t \<or> check_poly_ge (poly_add ?s ?v) (poly_add ?t ?u)" 
          by (cases "check_poly_ge ?s ?t", auto simp: Let_def)
        then show ?thesis
        proof
          assume "check_poly_ge ?s ?t"
          then have "isOK(check_ns I (s,t))" unfolding check_ns_def by auto
          from ns[OF this] show ?thesis unfolding cc st uv stri by auto
        next
          assume "check_poly_ge (poly_add ?s ?v) (poly_add ?t ?u)"
          from check_poly_ge[OF this] 
          have "poly_add (eval_term I s) (eval_term I v) \<ge>p poly_add (eval_term I t) (eval_term I u)" by auto
          then have ge: "\<And> \<alpha>. pos_assign \<alpha> \<Longrightarrow> (eval_poly \<alpha> (eval_term I s) + eval_poly \<alpha> (eval_term I v)) \<ge>
            (eval_poly \<alpha> (eval_term I t) + eval_poly \<alpha> (eval_term I u))" unfolding poly_ge_def by auto
          let ?inter_ns = "inter_ns :: ('f,'v)trs"
          show ?thesis unfolding cc uv st stri cc_satisfied.simps if_False
          proof (intro allI impI)
            fix \<sigma> 
            assume F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" and ns: "(u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> ?inter_ns"
            from ns[unfolded inter_ns_def] have ns: "\<And> \<alpha>. pos_assign \<alpha> \<Longrightarrow> (eval_poly \<alpha> (?I (u \<cdot> \<sigma>))) \<ge> (eval_poly \<alpha> (?I (v \<cdot> \<sigma>)))"
              unfolding poly_ge_def by auto
            have "?I (s \<cdot> \<sigma>) \<ge>p ?I (t \<cdot> \<sigma>)" unfolding poly_ge_def
            proof(intro allI impI)
              fix \<alpha> :: "('v,'a)assign"
              let ?\<sigma> = "(\<lambda>x. eval_poly \<alpha> (eval_term I (\<sigma> x)))"
              define J where "J = (\<lambda> t. eval_poly ?\<sigma> (?I t))"
              assume pos: "pos_assign \<alpha>"
              from pos_assign_F_subst[OF F pos] have poss: "pos_assign ?\<sigma>" .
              from ns[OF pos, unfolded inter_stable] have ge': "(J u) \<ge> (J v)" unfolding J_def .
              from ge[OF poss] have ge: "(J s + J v) \<ge> (J t + J u)" unfolding J_def .
              from ge ge' have "(J s) \<ge> (J t)" by (rule cond_ge)
              then show "(eval_poly \<alpha> (?I (s \<cdot> \<sigma>))) \<ge> (eval_poly \<alpha> (?I (t \<cdot> \<sigma>)))"
                unfolding inter_stable J_def .
            qed
            then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> inter_ns" unfolding inter_ns_def by simp
          qed
        qed
      qed
    qed
  qed
qed

definition create_nlpoly_non_inf_order :: 
  "showsl check \<Rightarrow> 'a :: {showl,poly_carrier} \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 
    ('a \<Rightarrow> 'a list) \<Rightarrow> ('f,'a)poly_inter_list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> 
    ('f :: {compare_order,showl},'v :: {showl,linorder})non_inf_order"
where "\<And> sqrt. create_nlpoly_non_inf_order cI def gt power_mono discrete sqrt I F \<equiv> (let 
   J = poly_inter_list_to_inter def I;
   x = poly_subst (\<lambda> n. poly_of (PVar (''x_'' @ (shows n []))))
   in \<lparr>
    non_inf_order.valid = do {cI; check_non_inf_poly_inter_list discrete F I 
       <+? (\<lambda> (f,p). showsl (STR ''interpretation '') \<circ> showsl_poly (x p) \<circ> showsl (STR '' of '') 
         \<circ> showsl f \<circ> showsl (STR '' invalid ''))},    
    ns = check_ns J, 
    cc = check_cc sqrt gt J,
    af = create_dep discrete def I,
    desc = showsl (STR ''polynomial interpretation\<newline>'') \<circ> showsl_sep (\<lambda> ((f,n),p) . 
        showsl (STR ''Pol('') \<circ> showsl f \<circ> showsl (STR ''/'') \<circ> showsl n \<circ> showsl (STR '') = '') \<circ> showsl_poly (x p)) 
        showsl_nl I
  \<rparr>)"

lemma non_inf_poly_order_carrier_to_generic_non_inf_order: 
  fixes default :: "'a :: {showl,poly_carrier}" and sqrt
  assumes non_inf: "isOK cI \<Longrightarrow> non_inf_poly_order_carrier default gt power_mono discrete"
  shows "generic_non_inf_order_impl (create_nlpoly_non_inf_order cI default gt power_mono discrete sqrt)"
proof 
  fix I :: "('f :: {compare_order,showl},'a)poly_inter_list" and ns_list :: "('f,'v :: {showl,linorder})rule list" and cc 
    and F
  let ?rp = "create_nlpoly_non_inf_order cI default gt power_mono discrete sqrt I F :: ('f,'v)non_inf_order"
  let ?af = "non_inf_order.af ?rp :: 'f dep"
  assume valid: "isOK (non_inf_order.valid ?rp)" 
  assume cc: "isOK (check_allm (non_inf_order.cc ?rp) cc)" 
  assume ns: "isOK (check_allm (non_inf_order.ns ?rp) ns_list)"
  from valid have valid: "isOK(check_non_inf_poly_inter_list discrete F I)" and cI: "isOK(cI)" unfolding create_nlpoly_non_inf_order_def by (auto simp: Let_def)
  from non_inf[OF cI] interpret non_inf_poly_order_carrier default gt power_mono discrete .
  let ?J = "poly_inter_list_to_inter default I :: ('f,'a)poly_inter"
  from check_non_inf_poly_inter_list[OF valid]
  interpret non_inf_poly_order default gt power_mono discrete sqrt ?J "set F" ?af unfolding create_nlpoly_non_inf_order_def by (simp add: Let_def) 
  have pre: "pre_poly_order default gt power_mono discrete ?J (set F)" ..
  have non_inf: "non_inf_poly_order_carrier default gt power_mono discrete" ..
  let ?all = "ns_list"
  show "\<exists> S NS. non_inf_order_trs S NS (set F) ?af \<and> set ns_list \<subseteq> NS \<and> Ball (set cc) (cc_satisfied (set F) S NS)"
  proof (intro exI allI conjI, unfold_locales)
    show "set ns_list \<subseteq> inter_ns" 
    proof
      fix s t
      assume "(s,t) \<in> set ns_list"
      with ns have "isOK(check_ns ?J (s,t))" unfolding create_nlpoly_non_inf_order_def
        by (auto simp: Let_def)
      from check_ns[OF this pre] show "(s,t) \<in> inter_ns" .
    qed
  next
    show "Ball (set cc) (cc_satisfied (set F) inter_s inter_ns)"
    proof
      fix c
      assume "c \<in> set cc"
      with cc have "isOK(check_cc sqrt gt ?J c)" unfolding create_nlpoly_non_inf_order_def
        by (auto simp: Let_def)
      from check_cc[OF this pre non_inf] show "cc_satisfied (set F) inter_s inter_ns c" .
    qed
  qed
qed

end
