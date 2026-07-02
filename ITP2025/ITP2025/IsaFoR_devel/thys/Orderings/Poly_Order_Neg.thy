theory Poly_Order_Neg
imports
  Poly_Order
begin

class poly_carrier' = poly_carrier + ring

locale order_pair_neg = 
  fixes gt :: "'a :: poly_carrier' \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50)
  and F :: "'f sig"
  assumes compat[trans]: "\<lbrakk>x \<ge> y; y \<succ> z\<rbrakk> \<Longrightarrow> x \<succ> z"
  and compat2[trans]: "\<lbrakk>x \<succ> y; y \<ge> z\<rbrakk> \<Longrightarrow> x \<succ> z"
  and gt_imp_ge: "x \<succ> y \<Longrightarrow> x \<ge> y"
  and plus_gt_left_mono: "x \<succ> y \<Longrightarrow> x + z \<succ> y + z"
  and irrefl: "x \<succ> x \<Longrightarrow> False"
  and F_Univ: "F = UNIV"
begin

abbreviation  less_n  (infix "\<prec>" 50)
  where "x \<prec> y \<equiv> y \<succ> x"

lemma gt_trans[trans]: "\<lbrakk>x \<succ> y; y \<succ> z\<rbrakk> \<Longrightarrow> x \<succ> z"
  by (rule compat[OF gt_imp_ge])

definition neg_assign :: "('v,'a::poly_carrier')assign \<Rightarrow> bool"
  where "neg_assign \<alpha> = (\<forall> x. \<alpha> x \<le> 0)"

definition poly_gt :: "('v :: linorder,'a:: poly_carrier')poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" (infix ">p" 51)
  where "p >p q = (\<forall> \<alpha>. pos_assign \<alpha> \<longrightarrow> eval_poly \<alpha> p \<succ> eval_poly \<alpha> q)"

definition poly_neg_gt :: "('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" (infix ">pn" 51)
  where "p >pn q = (\<forall> \<alpha>. neg_assign \<alpha> \<longrightarrow> eval_poly \<alpha> p \<succ> eval_poly \<alpha> q)"

definition poly_neg_ge :: "('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" (infix "\<ge>pn" 51)
  where "p \<ge>pn q = (\<forall> \<alpha>. neg_assign \<alpha> \<longrightarrow> eval_poly \<alpha> p \<ge> eval_poly \<alpha> q)"

definition poly_weak_neg_mono :: "('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> 'v \<Rightarrow> bool" where 
  "poly_weak_neg_mono p v \<equiv> \<forall> (\<alpha> :: ('v,'a)assign) \<beta>. (\<forall> x. v \<noteq> x \<longrightarrow> \<alpha> x = \<beta> x) \<longrightarrow> neg_assign \<alpha> \<longrightarrow> \<alpha> v \<ge> \<beta> v \<longrightarrow> eval_poly \<alpha> p \<ge> eval_poly \<beta> p"

definition poly_strict_neg_mono :: "('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> 'v \<Rightarrow> bool" where 
  "poly_strict_neg_mono p v \<equiv> \<forall> (\<alpha> :: ('v,'a)assign) \<beta>. (\<forall> x. v \<noteq> x \<longrightarrow> \<alpha> x = \<beta> x) \<longrightarrow> neg_assign \<alpha> \<longrightarrow> \<alpha> v \<succ> \<beta> v \<longrightarrow> eval_poly \<alpha> p \<succ> eval_poly \<beta> p"

definition poly_weak_neg_mono_all :: "('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> bool" where 
  "poly_weak_neg_mono_all p \<equiv> \<forall> (\<alpha> :: ('v,'a)assign) \<beta>. (\<forall> x. \<alpha> x \<ge> \<beta> x) 
    \<longrightarrow> neg_assign \<alpha> \<longrightarrow> eval_poly \<alpha> p \<ge> eval_poly \<beta> p"

lemma poly_weak_neg_mono_all: fixes p :: "('v :: linorder,'a :: poly_carrier')poly"
  assumes p: "poly_weak_neg_mono_all p"
  shows "poly_weak_neg_mono p v"
unfolding poly_weak_neg_mono_def
proof (intro allI impI)
  fix \<alpha> \<beta> :: "('v,'a)assign"
  assume all: "\<forall>x. v \<noteq> x \<longrightarrow> \<alpha> x = \<beta> x"
  assume neg: "neg_assign \<alpha>"
  assume v: "\<alpha> v \<ge> \<beta> v"
  show "eval_poly \<alpha> p \<ge> eval_poly \<beta> p" 
  proof (rule p[unfolded poly_weak_neg_mono_all_def, rule_format, OF _ neg])
    fix x 
    show "\<alpha> x \<ge> \<beta> x" using v all ge_refl[of "\<beta> x"] by auto
  qed
qed
end

definition poly_convert :: "('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> ('v,'a)poly" where
  "poly_convert p = poly_subst (\<lambda> v. [(var_monom v,-1)]) p" 

definition check_poly_neg_ge :: "('v:: linorder,'a::poly_carrier')poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" where 
  "check_poly_neg_ge p q = (let p' = poly_convert p;
  q' = poly_convert q in check_poly_ge p' q')"

definition check_poly_neg_gt :: "_ \<Rightarrow> ('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" where
  "check_poly_neg_gt gt p q = (let p' = poly_convert p;
  q' = poly_convert q in check_poly_gt gt p' q')"


locale poly_order_neg = order_pair_neg +
  fixes default' :: "'a :: poly_carrier'"
    and discrete' :: "bool"
    and I :: "('f, 'a) poly_inter" 
  assumes neg_I: "\<And>fn. fn \<in> F \<Longrightarrow> zero_poly \<ge>pn I fn"
    and mono_I: "\<And>fn. poly_weak_neg_mono_all (I fn)"
    and default': "\<exists> n. \<forall> f m. m \<ge> n \<longrightarrow> I (f,m) = zero_poly"
begin

definition inter_neg_s :: "('f,'v :: linorder)trs"
  where "inter_neg_s \<equiv> {(s,t). (eval_term I s >pn eval_term I t)}"

definition inter_neg_ns :: "('f,'v :: linorder)trs"
  where "inter_neg_ns \<equiv> {(s,t). eval_term I s \<ge>pn eval_term I t}"

lemma inter_neg_s_ns:"inter_neg_s \<subseteq> inter_neg_ns" 
  unfolding inter_neg_s_def inter_neg_ns_def poly_neg_ge_def poly_neg_gt_def
  using gt_imp_ge by auto

lemma poly_neg_ge_refl[simp]: "p \<ge>pn p"
  unfolding poly_neg_ge_def using ge_refl by auto

lemma refl_inter_neg_ns: "refl inter_neg_ns"
  unfolding refl_on_def inter_neg_ns_def by simp

lemma poly_neg_gt_imp_poly_neg_ge: "p >pn q \<Longrightarrow> p \<ge>pn q" unfolding poly_neg_ge_def poly_neg_gt_def using gt_imp_ge by blast

lemma poly_neg_ge_trans[trans]: "\<lbrakk>p1 \<ge>pn p2; p2 \<ge>pn p3\<rbrakk> \<Longrightarrow> p1 \<ge>pn p3"
  unfolding poly_neg_ge_def using ge_trans by blast

lemma poly_neg_gt_trans[trans]: "\<lbrakk>p1 >pn p2; p2 >pn p3\<rbrakk> \<Longrightarrow> p1 >pn p3"
  unfolding poly_neg_gt_def using gt_trans by blast

lemma trans_inter_neg_ns: "trans inter_neg_ns"
  unfolding trans_def inter_neg_ns_def using poly_neg_ge_trans by auto

lemma poly_neg_compat: "\<lbrakk>p1 \<ge>pn p2; p2 >pn p3\<rbrakk> \<Longrightarrow> p1 >pn p3"
unfolding poly_neg_ge_def poly_neg_gt_def using compat by blast

lemma poly_neg_compat2: "\<lbrakk>p1 >pn p2; p2 \<ge>pn p3\<rbrakk> \<Longrightarrow> p1 >pn p3"
unfolding poly_neg_ge_def poly_neg_gt_def using compat2 by blast

lemma neg_assign_poly: assumes neg: "neg_assign \<alpha>"
  and p: "zero_poly \<ge>pn p"
  shows "0 \<ge> eval_poly \<alpha> p"
proof -
  from p[unfolded poly_neg_ge_def zero_poly_def] neg 
  show ?thesis by simp
qed

lemma eval_term_neg: fixes t :: "('f, 'v :: linorder) term" 
  assumes tF: "funas_term t \<subseteq> F" 
  shows "zero_poly \<ge>pn eval_term I t"
unfolding poly_neg_ge_def zero_poly_def
proof (intro impI allI)
  fix \<alpha> :: "('v,'a)assign"
  assume neg: "neg_assign \<alpha>"
  from tF
  show "eval_poly \<alpha> (eval_term I t) \<le> eval_poly \<alpha> []"
  proof (induct t)
    case (Var x) then show ?case by (simp add: neg[unfolded neg_assign_def]) 
  next
    case (Fun f ts)
    then have f: "(f,length ts) \<in> F" by auto
    {
      fix i
      have "eval_poly \<alpha> (if i < length ts then map (eval_term I) ts ! i else zero_poly) \<le> 0"
      proof (cases "i < length ts")
        case False then show ?thesis unfolding zero_poly_def by (simp add: ge_refl)
      next
        case True
        then have "ts ! i \<in> set ts" by auto
        with Fun have "eval_poly \<alpha> (eval_term I (ts ! i)) \<le> 0" by auto
        with True show ?thesis by simp
      qed
    }
    then show ?case 
      by (simp add: Let_def poly_subst, intro neg_assign_poly[OF _ neg_I[OF f]], unfold neg_assign_def, auto)
  qed
qed

lemma neg_assign_F_subst:
  fixes \<sigma> :: "('f, 'v :: linorder) subst"
  assumes F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" 
  and alpha: "neg_assign \<alpha>"
   shows "neg_assign (\<lambda>x. eval_poly \<alpha> (eval_term I (\<sigma> x)))"
unfolding neg_assign_def
proof
  fix x
  from F have "funas_term (\<sigma> x) \<subseteq> F" by auto
  from neg_assign_poly[OF alpha eval_term_neg[OF this]]
  show "eval_poly \<alpha> (eval_term I (\<sigma> x)) \<le> (0 :: 'a)" using neg_I by blast
qed

lemma inter_stable_neg: 
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

lemma F_subst_closed_inter_neg_s: "F_subst_closed F inter_neg_s"
proof
  fix \<sigma> :: "('f,'v :: linorder)subst" and s t :: "('f,'v)term"
  assume F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" and st: "(s,t) \<in> inter_neg_s"
  from st[unfolded inter_neg_s_def] have "eval_term I s >pn eval_term I t" by simp
  from this[unfolded poly_neg_gt_def]
  have gt: "\<And> \<alpha>. neg_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (eval_term I s) \<succ> eval_poly \<alpha> (eval_term I t)" by auto
  have "eval_term I (s \<cdot> \<sigma>) >pn eval_term I (t \<cdot> \<sigma>)" unfolding poly_neg_gt_def inter_stable_neg using neg_I
    using F gt neg_assign_F_subst by blast
  then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> inter_neg_s" unfolding inter_neg_s_def by simp
qed

lemma F_subst_closed_inter_neg_ns: "F_subst_closed F inter_neg_ns"
proof
  fix \<sigma> :: "('f,'v :: linorder)subst" and s t :: "('f,'v)term"
  assume F: "\<Union>(funas_term ` range \<sigma>) \<subseteq> F" and st: "(s,t) \<in> inter_neg_ns"
  from st[unfolded inter_neg_ns_def] have "eval_term I s \<ge>pn eval_term I t" by simp
  from this[unfolded poly_neg_ge_def]
  have gt: "\<And> \<alpha>. neg_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (eval_term I s) \<ge> eval_poly \<alpha> (eval_term I t)" by auto
  have "eval_term I (s \<cdot> \<sigma>) \<ge>pn eval_term I (t \<cdot> \<sigma>)" unfolding poly_neg_ge_def inter_stable_neg
    by (intro allI impI, rule gt, rule neg_assign_F_subst[OF F])
  then show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> inter_neg_ns" unfolding inter_neg_ns_def by simp
qed

lemma F_subst_closed_UNIV:
  "F_subst_closed F r \<Longrightarrow> F = UNIV \<Longrightarrow> subst.closed r" unfolding F_subst_closed_def
  using subst.closedI[of r] by auto

lemma poly_weak_neg_mono_E: assumes p: "poly_weak_neg_mono p v"
  and fgw: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w"
  and f: "\<And> w. zero_poly \<ge>pn f w" 
  and fgv: "f v \<ge>pn g v"
  shows "poly_subst f p \<ge>pn poly_subst g p"
  unfolding poly_neg_ge_def poly_subst
proof (intro allI impI, rule p[unfolded poly_weak_neg_mono_def, rule_format])
  fix \<alpha> :: "('c::linorder,'a :: poly_carrier')assign" and x
  assume v: "v \<noteq> x"
  show "neg_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f x) = eval_poly \<alpha> (g x)" using fgw[OF v] unfolding poly_neg_ge_def by auto
next
  fix \<alpha> :: "('c::linorder,'a :: poly_carrier')assign"
  show "neg_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f v) \<ge> eval_poly \<alpha> (g v)" using fgv unfolding poly_neg_ge_def by auto
next
  fix \<alpha> :: "('c::linorder,'a :: poly_carrier')assign"
  assume alpha: "neg_assign \<alpha>"
  show "neg_assign (\<lambda>v. eval_poly \<alpha> (f v))" 
    unfolding neg_assign_def
  proof
    fix x
    show "eval_poly \<alpha> (f x) \<le> 0"
    using f[of x] unfolding poly_neg_ge_def zero_poly_def using alpha by simp
  qed
qed

lemma ctxt_closed_inter_neg_ns: assumes F:"F = UNIV"
  shows "ctxt.closed inter_neg_ns"
proof (rule one_imp_ctxt_closed)
  fix f bef and s t :: "('f,'v :: linorder)term" and aft 
  assume st: "(s,t) \<in> inter_neg_ns"
  show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> inter_neg_ns" (is "(Fun f ?s, Fun f ?t) \<in> _")
    unfolding inter_neg_ns_def poly_neg_ge_def
  proof (clarify)
    fix \<alpha> :: "('v,'a)assign"
    assume neg: "neg_assign \<alpha>"
    let ?n = "Suc (length bef + length aft)"
    let ?i = "length bef"
    from mono_I[of "(f,?n)"] have mono: "poly_weak_neg_mono (I (f,?n)) ?i" by (rule poly_weak_neg_mono_all)
    let ?exp = "\<lambda> w s. (if w < ?n then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! w else zero_poly)"
    {
      fix w
      assume "?i \<noteq> w"
      then have "?exp w s = ?exp w t" by (simp add: nth_append)
    } note one = this
    {
      fix w
      have "\<exists> ts. (?exp w s = (if w < length ts then (map (eval_term I) ts) ! w else zero_poly))"
        by (rule exI[of _ ?s], simp only: map_append, simp) 
      then obtain ts where id: "?exp w s = (if w < length ts then (map (eval_term I) ts) ! w else zero_poly)" by blast
      have "zero_poly \<ge>pn ?exp w s" unfolding poly_neg_ge_def zero_poly_def id
      proof(intro impI allI)
        fix \<alpha> :: "('v,'a)assign"
        assume asm:"neg_assign \<alpha>"
        then show "eval_poly \<alpha>
          (if w < ?n
           then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! w else [])
         \<le> eval_poly \<alpha> []"
        proof(cases "w < ?n")
          case True
          then show ?thesis using asm id neg_assign_poly one poly_neg_ge_refl F eval_term_neg neg_I by auto
        next
          case False
          then show ?thesis by (simp add: ge_refl)
        qed
      qed
    } note two = this 
    have "eval_poly \<alpha> (poly_subst (\<lambda>i. if i < ?n then (map (eval_term I) bef @ eval_term I s # map (eval_term I) aft) ! i else zero_poly) (I (f,?n))) \<ge>
        eval_poly \<alpha> (poly_subst (\<lambda>i. if i < ?n then (map (eval_term I) bef @ eval_term I t # map (eval_term I) aft) ! i else zero_poly) (I (f,?n)))"
      by (rule poly_weak_neg_mono_E[OF mono, unfolded poly_neg_ge_def, rule_format, OF _ _ _ neg])
        ((auto simp: one two ge_refl two[unfolded poly_neg_ge_def])[2], simp add: nth_append st[unfolded inter_neg_ns_def poly_neg_ge_def, simplified])
    then show "eval_poly \<alpha> (eval_term I (Fun f ?s)) \<ge> eval_poly \<alpha> (eval_term I (Fun f ?t))" by simp
  qed
qed

lemma irrefl_inter_neg_s: "\<not> s >pn s"
proof
  assume "s >pn s" 
  thus False unfolding poly_neg_gt_def
  proof (induct s)
    case Nil
    have ea:"eval_poly \<alpha> [] \<succ> eval_poly \<alpha> [] \<Longrightarrow> False" for \<alpha>:: "('b::linorder,'a :: poly_carrier')assign"
    proof -
      assume asm:"(eval_poly \<alpha> []) \<succ> (eval_poly \<alpha> [])"
      have "eval_poly \<alpha> [] = 0" by simp
      then show ?thesis using irrefl asm by auto
    qed
    from Nil show ?case unfolding neg_assign_def using  ge_refl irrefl by fast
  next
    case (Cons a s)
    have ne:"neg_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> s \<succ> eval_poly \<alpha> s \<Longrightarrow> False" for \<alpha>::"('b::linorder,'a :: poly_carrier')assign"
      using irrefl by auto
    hence ne_app:"neg_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (a # s)  \<succ> eval_poly \<alpha> (a # s) \<Longrightarrow> False" for \<alpha>:: "('b::linorder,'a :: poly_carrier')assign" 
      using irrefl by blast
    show ?case unfolding neg_assign_def eval_poly.simps using Cons ne ne_app by force
  qed
qed

lemma comp_ns_s_inv:"inter_neg_ns \<inter> inter_neg_s\<inverse> = {}" unfolding inter_neg_ns_def inter_neg_s_def 
proof (safe)
  fix a b::"('f,'v::linorder)term"
  assume asm1:"eval_term I a \<ge>pn eval_term I b"
  assume asm2:"eval_term I b >pn eval_term I a"
  from asm1 asm2 have "eval_term I a >pn eval_term I a" using poly_neg_compat by auto
  then show "(a, b) \<in> {}" using irrefl_inter_neg_s by auto
qed

theorem co_rewrite_pair_poly:
  assumes F:"F = UNIV"
  shows "co_rewrite_pair inter_neg_s inter_neg_ns"
proof
  show "ctxt.closed inter_neg_ns" using ctxt_closed_inter_neg_ns[OF F] by simp
  show "subst.closed inter_neg_s" by (rule F_subst_closed_UNIV[OF F_subst_closed_inter_neg_s F])
  show "subst.closed inter_neg_ns" by (rule F_subst_closed_UNIV[OF F_subst_closed_inter_neg_ns F])
  show "refl inter_neg_ns" using refl_inter_neg_ns by auto
  show "trans inter_neg_ns" using trans_inter_neg_ns by auto
  show "inter_neg_ns \<inter> inter_neg_s\<inverse> = {}" using comp_ns_s_inv by auto
qed

end

definition check_neg_s :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('f,'a :: {showl,poly_carrier'})poly_inter \<Rightarrow> ('f :: showl ,'v :: {showl, linorder})rule \<Rightarrow> showsl check" where
  "check_neg_s gt I \<equiv> (\<lambda> (s,t). let p = eval_term I s; q = eval_term I t in check (check_poly_neg_gt gt p q) 
    (showsl (STR ''could not ensure '') \<circ> showsl s \<circ> showsl (STR '' > '') \<circ> showsl t 
    \<circ> showsl (STR '' since we\<newline>could not ensure '') \<circ> showsl_poly p \<circ> showsl (STR '' > '') \<circ> showsl_poly q))"

definition default_I' :: "'a \<Rightarrow> nat \<Rightarrow> (nat,'a :: poly_carrier')poly"
  where "default_I' def n \<equiv> zero_poly"

definition
  poly_inter_list_to_inter_neg :: "'a :: poly_carrier' \<Rightarrow> ('f :: compare_order, 'a) poly_inter_list \<Rightarrow> ('f, 'a) poly_inter"
where                                                                                                               
  "poly_inter_list_to_inter_neg def I \<equiv> fun_of_map_fun (ceta_map_of I) (\<lambda> fn. default_I' def (snd fn))"

definition check_neg_ns :: "('f,'a :: {showl,preorder, poly_carrier'})poly_inter \<Rightarrow> ('f :: showl ,'v :: {showl, linorder})rule \<Rightarrow> showsl check" where
  "check_neg_ns I \<equiv> (\<lambda> (s,t). let p = eval_term I s; q = eval_term I t in check (check_poly_neg_ge p q) 
    (showsl (STR ''could not ensure '') \<circ> showsl s \<circ> showsl (STR '' >= '') \<circ> showsl t 
    \<circ> showsl (STR '' since we\<newline>could not ensure '') \<circ> showsl_poly p \<circ> showsl (STR '' >= '') \<circ> showsl_poly q))"

definition check_poly_weak_mono_easy :: "('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> bool"
  where "check_poly_weak_mono_easy p \<equiv> check_poly_weak_mono_all (monom_mult_poly (1,-1)(poly_convert p))"

definition check_poly_weak_mono_and_neg' :: "('v :: linorder,'a :: poly_carrier')poly \<Rightarrow> bool"
  where "check_poly_weak_mono_and_neg' p \<equiv> check_poly_neg_ge zero_poly p \<and> check_poly_weak_mono_easy p"

definition check_poly_inter_list_neg :: "('f :: showl,'a :: poly_carrier')poly_inter_list \<Rightarrow> showsl check"
where "check_poly_inter_list_neg I \<equiv> do {
   check (distinct (map fst I)) (showsl (STR ''some symbol has two interpretations''));
   check_all (\<lambda> (_,p). check_poly_weak_mono_and_neg' p) I <+? (\<lambda> ((f,n),p). showsl (STR ''could not ensure weak-mono-, or neg.-property of interpretation of symbol '') o showsl f)
 }"

context order_pair_neg
begin

lemma eval_equiv:"eval_poly \<alpha> (poly_convert p) = eval_poly (\<lambda> x. - \<alpha> x) p" 
  unfolding poly_convert_def poly_subst by simp

lemma poly_imp:"(poly_convert p) \<ge>p (poly_convert q) \<Longrightarrow>  p \<ge>pn q" 
proof -
  assume "(poly_convert p) \<ge>p (poly_convert q)"
  hence pos_\<alpha>:"(\<forall> \<alpha>. pos_assign \<alpha> \<longrightarrow> eval_poly \<alpha> (poly_convert p) \<ge> eval_poly \<alpha> (poly_convert q))" 
    using poly_ge_def by auto
  hence pos:"(\<forall> \<alpha>. (\<forall>x. \<alpha> x \<ge> 0) \<longrightarrow>  eval_poly (\<lambda> x. - \<alpha> x) p \<ge> eval_poly (\<lambda> x. - \<alpha> x) q)" 
    unfolding pos_assign_def using eval_equiv by metis
  hence "(\<forall> \<alpha>. (\<forall>x. \<alpha> x \<le> 0) \<longrightarrow>  eval_poly (\<lambda> x. - (- \<alpha> x)) p \<ge> eval_poly (\<lambda> x. -(- \<alpha> x)) q)" 
    by (metis add.inverse_inverse add_0 left_minus plus_left_mono)
  hence "\<forall> \<alpha>. neg_assign \<alpha> \<longrightarrow>  eval_poly (\<lambda> x. \<alpha> x) p \<ge> eval_poly (\<lambda> x. \<alpha> x) q"  
    unfolding neg_assign_def by simp
  then show "p \<ge>pn q" unfolding poly_neg_ge_def by auto 
qed

lemma check_poly_neg_ge: fixes p :: "('v :: linorder,'a :: poly_carrier')poly"
  shows "check_poly_neg_ge p q \<Longrightarrow> (p \<ge>pn q)"
proof -
  assume asm:"check_poly_neg_ge p q"
  define p' where "p' = poly_convert p"
  define q' where "q' = poly_convert q"
  hence "check_poly_ge p' q'" using asm p'_def by (auto simp: check_poly_neg_ge_def)
  hence "(p' \<ge>p q')" using check_poly_ge by auto
  then show "(p \<ge>pn q)" using poly_imp p'_def q'_def by auto
qed

lemma poly_imp_s:"(poly_convert p) >p (poly_convert q) \<Longrightarrow>  p >pn q" 
proof -
  assume "(poly_convert p) >p (poly_convert q)"
  hence pos_\<alpha>:"(\<forall> \<alpha>. pos_assign \<alpha> \<longrightarrow> eval_poly \<alpha> (poly_convert p) \<succ> eval_poly \<alpha> (poly_convert q))" 
    using poly_gt_def by auto
  hence pos:"(\<forall> \<alpha>. (\<forall>x. \<alpha> x \<ge> 0) \<longrightarrow>  eval_poly (\<lambda> x. - \<alpha> x) p \<succ> eval_poly (\<lambda> x. - \<alpha> x) q)" 
    unfolding pos_assign_def using eval_equiv by metis
  hence "(\<forall> \<alpha>. (\<forall>x. \<alpha> x \<le> 0) \<longrightarrow>  eval_poly (\<lambda> x. - (- \<alpha> x)) p \<succ> eval_poly (\<lambda> x. -(- \<alpha> x)) q)" 
    by (metis add.inverse_inverse add_0 left_minus plus_left_mono)
  hence "\<forall> \<alpha>. neg_assign \<alpha> \<longrightarrow>  eval_poly (\<lambda> x. \<alpha> x) p \<succ> eval_poly (\<lambda> x. \<alpha> x) q"  
    unfolding neg_assign_def by simp
  then show "p >pn q" unfolding poly_neg_gt_def by auto 
qed

lemma check_poly_gt: 
  fixes p :: "('v :: linorder,'a::poly_carrier')poly"
  assumes "check_poly_gt gt p q" shows "p >p q"
proof -
  obtain a1 p1 where p: "poly_split 1 p = (a1,p1)" by force
  obtain b1 q1 where q: "poly_split 1 q = (b1,q1)" by force
  from p q assms have gt: "a1 \<succ> b1" and ge: "p1 \<ge>p q1" unfolding check_poly_gt_def using check_poly_ge[of p1 q1]  by auto
  show ?thesis
  proof (unfold poly_gt_def, intro impI allI)
    fix \<alpha> :: "('v,'a)assign"
    assume "pos_assign \<alpha>"
    with ge have ge: "eval_poly \<alpha> p1 \<ge> eval_poly \<alpha> q1" unfolding poly_ge_def by simp
    from plus_gt_left_mono[OF gt] compat[OF plus_left_mono[OF ge]] have gt: "a1 + eval_poly \<alpha> p1 \<succ> b1 + eval_poly \<alpha> q1" by (force simp: field_simps)
    show "eval_poly \<alpha> p \<succ> eval_poly \<alpha> q"
      by (simp add: poly_split[OF p, unfolded eq_poly_def] poly_split[OF q, unfolded eq_poly_def] gt)
  qed
qed

lemma check_poly_neg_gt: fixes p :: "('v :: linorder,'a :: poly_carrier')poly"
  shows "check_poly_neg_gt gt p q \<Longrightarrow> (p >pn q)"
proof -
  assume asm:"check_poly_neg_gt gt p q"
  define p' where "p' = poly_convert p"
  define q' where "q' = poly_convert q"
  hence "check_poly_gt gt p' q'" using asm p'_def by (auto simp: check_poly_neg_gt_def)
  hence "p'>p q'" using check_poly_gt by auto
  then show "(p >pn q)" using poly_imp_s p'_def q'_def by auto
qed

lemma poly_mono_conv:
  fixes p :: "('v :: linorder,'a)poly"
  assumes check:"check_poly_weak_mono_and_neg' p"
  shows "poly_weak_neg_mono_all p \<and> (zero_poly \<ge>pn p)" 
proof 
  note check = check[unfolded check_poly_weak_mono_and_neg'_def, simplified]
  from check have "check_poly_neg_ge zero_poly p" by auto
  from check_poly_neg_ge[OF this] show "zero_poly \<ge>pn p" by auto
  from check have "check_poly_weak_mono_easy p" by auto
  from this[unfolded check_poly_weak_mono_easy_def] 
  have "check_poly_weak_mono_all (monom_mult_poly (1,-1)(poly_convert p))" .
  from check_poly_weak_mono_all[OF this] have mono: "poly_weak_mono_all (monom_mult_poly (1,-1)(poly_convert p))" .
  show "poly_weak_neg_mono_all p" unfolding poly_weak_neg_mono_all_def
  proof (intro impI allI, goal_cases)
    case (1 \<alpha> \<beta>)
    let ?na = "\<lambda> x. - \<alpha> x" 
    let ?nb = "\<lambda> x. - \<beta> x" 
    have le: "\<And>x. ?na x \<le> ?nb x"
    proof -
      from 1(1) plus_right_mono  have "\<And>x.(-\<alpha> x + -\<beta> x) + \<beta> x \<le> (-\<alpha> x + -\<beta> x) + \<alpha> x" 
        by blast
      with minus_add_cancel have "\<And>x. -\<alpha> x \<le> (-\<alpha> x + -\<beta> x) + \<alpha> x" by auto
      with add.commute have "\<And>x. -\<alpha> x \<le> (-\<beta> x + -\<alpha> x) + \<alpha> x" by auto
      with minus_add_cancel show "\<And>x. -\<alpha> x \<le> -\<beta> x" by auto
    qed
    have pos: "pos_assign ?na" unfolding neg_assign_def pos_assign_def
    proof -
      from 1(2)[unfolded neg_assign_def] have "\<forall>x. \<alpha> x \<le> 0" by auto
      with plus_right_mono have "\<forall>x. -\<alpha> x + \<alpha> x \<le> -\<alpha> x + 0" by blast
      with add_0 minus_add_cancel show "\<forall>x. 0 \<le> -\<alpha> x" by simp
    qed
    from mono[unfolded poly_weak_mono_all_def, rule_format, OF _ pos, OF le, unfolded eval_equiv, simplified]
    have "- eval_poly \<alpha> p \<le> - eval_poly \<beta> p" by (simp add: eval_equiv)
    with plus_right_mono[of "- eval_poly \<alpha> p" "- eval_poly \<beta> p" "(eval_poly \<beta> p + eval_poly \<alpha> p)"] 
    have "(eval_poly \<beta> p + eval_poly \<alpha> p) - eval_poly \<alpha> p \<le> (eval_poly \<beta> p + eval_poly \<alpha> p) - eval_poly \<beta> p" by auto
    with minus_add_cancel add.commute have "eval_poly \<beta> p \<le> eval_poly \<alpha> p" by auto
    thus ?case by simp
  qed
qed
    
lemma check_poly_inter_list_neg:
  assumes check: "isOK(check_poly_inter_list_neg I)"
  shows "poly_weak_neg_mono_all (poly_inter_list_to_inter_neg 0 I (f,n)) 
    \<and> (zero_poly \<ge>pn (poly_inter_list_to_inter_neg 0 I (f,n)))"  
proof -
  note d = check_poly_inter_list_neg_def
  let ?I = "poly_inter_list_to_inter (0 :: 'a :: poly_carrier') I"
  show ?thesis
  proof (cases "map_of I (f, n)")
    case None 
    then show ?thesis
      by (simp add: default_I'_def ge_refl poly_neg_ge_def poly_weak_neg_mono_all_def zero_poly_def  
          poly_inter_list_to_inter_neg_def)
  next
    case (Some p)
    hence p:"poly_inter_list_to_inter_neg 0 I (f, n) = p" 
      by (simp add: poly_inter_list_to_inter_neg_def)
    from map_of_SomeD[OF Some] check[unfolded d]
    show ?thesis unfolding poly_inter_list_to_inter_neg_def using poly_mono_conv by force
  qed
qed

end

context
  fixes I :: "('f :: showl,'a :: {showl,preorder,poly_carrier'})poly_inter" and st :: "('f:: showl, 'v ::{showl,linorder})rule"
begin

lemma check_neg_ns:
  assumes check: "isOK (check_neg_ns I st)" and "poly_order_neg gt F I"
  shows "st \<in> poly_order_neg.inter_neg_ns I"
proof -
  obtain s t where st: "st = (s,t)" by force
  interpret poly_order_neg gt F def dis I for def dis by fact
  from check[unfolded check_neg_ns_def Let_def st] have "check_poly_neg_ge (eval_term I s) (eval_term I t)" by auto
  from check_poly_neg_ge[OF this] show "st \<in> inter_neg_ns" unfolding st inter_neg_ns_def by simp
qed

lemma check_neg_s: 
  assumes check: "isOK (check_neg_s gt I st)" and "poly_order_neg gt F I"
  shows "st \<in> poly_order_neg.inter_neg_s gt I"
proof -
  obtain s t where st: "st = (s,t)" by force
  interpret poly_order_neg gt F def dis I for def dis by fact
  from check[unfolded check_neg_s_def Let_def st] have "check_poly_neg_gt gt (eval_term I s) (eval_term I t)" by auto
  from check_poly_neg_gt[OF this] show "st \<in> inter_neg_s" unfolding inter_neg_s_def st by simp
qed

end

definition create_negpoly_rel_impl :: "showsl check \<Rightarrow> 'a :: {showl,preorder,poly_carrier'} \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('f,'a)poly_inter_list 
  \<Rightarrow> ('f :: {compare_order,showl},'v :: {showl,linorder})rel_impl"
  where "create_negpoly_rel_impl cI def gt discrete I = (let 
   J = poly_inter_list_to_inter_neg def I;
   x = poly_subst (\<lambda> n. poly_of (PVar (''x_'' @ show n))) \<comment> \<open>do not use String.literal at this point, as this will break code-gen\<close>
   in \<lparr>
    rel_impl.valid = do {cI ;  check_poly_inter_list_neg I},
    standard = succeed,
    desc = showsl (STR ''polynomial interpretation\<newline>'') \<circ> showsl_sep (\<lambda> ((f,n),p) . 
        showsl (STR ''Pol('') \<circ> showsl f \<circ> showsl (STR ''/'') \<circ> showsl n \<circ> showsl (STR '') = '') \<circ> showsl_poly (x p))
        showsl_nl I, 
    s = check_neg_s gt J,
    ns = check_neg_ns J, 
    nst = (\<lambda> _. error (showsl_lit (STR ''top-order not supported by neg-polys''))),
    af = full_af,
    top_af = full_af,
    SN = error (showsl_lit (STR ''SN not supported by neg-polys'')),
    subst_s = succeed,
    ce_compat = error (showsl_lit (STR ''Ce not supported by neg-polys'')),
    co_rewr = succeed,
    top_mono = error (showsl_lit (STR ''top-mono not supported by neg-polys'')),
    top_refl = error (showsl_lit (STR ''top-refl not supported by neg-polys'')),
    mono_af = empty_af,
    mono = (\<lambda> _. error (showsl_lit (STR ''strict monotonicity not supported by neg-polys''))),
    not_wst = None,
    not_sst = None,
    cpx = no_complexity_check\<rparr>)"

lemma check_poly_inter_list_distinct_neg:
  "isOK(check_poly_inter_list_neg I) \<Longrightarrow> distinct (map fst I)"
  unfolding check_poly_inter_list_neg_def by auto

lemma poly_order_neg_carrier_with_create_nlpoly_rel_impl: 
  assumes cx: "isOK cI \<Longrightarrow> isOK (check_poly_inter_list_neg I) \<Longrightarrow> poly_order_neg gt F (poly_inter_list_to_inter_neg def I)"
    and F: "F = UNIV"
  shows "rel_impl (create_negpoly_rel_impl cI def gt dis I :: ('f :: {compare_order,showl},'v :: {linorder, showl})rel_impl)"
  unfolding rel_impl_def
proof (intro impI allI, goal_cases) 
  case (1 U)
  let ?rp = "create_negpoly_rel_impl cI def gt dis I :: ('f,'v)rel_impl"
  let ?af = "rel_impl.af ?rp:: 'f af"
  let ?af' = "rel_impl.mono_af ?rp"
  note [simp] = create_negpoly_rel_impl_def Let_def
  have top_af: "rel_impl.top_af ?rp = ?af" by auto
  note valid = 1(1)
  from valid have valid: "isOK(check_poly_inter_list_neg I)" and cI: "isOK cI" by auto
  
  note distinct = check_poly_inter_list_distinct_neg[OF valid]
  let ?J = "poly_inter_list_to_inter_neg def I" 
  note cx = cx[OF cI valid]
  interpret poly_order_neg gt F def dis ?J by fact
  let ?S = "inter_neg_s::('f,'v)trs"
  let ?NS = "inter_neg_ns::('f,'v)trs" 
  interpret co_rewrite_pair ?S ?NS using co_rewrite_pair_poly[OF F] by simp
  show ?case unfolding top_af 
  proof (rule exI[of _ ?S], intro exI[of _ ?NS] conjI impI allI
    trans_NS top_mono_same refl_NS ctxt_NS subst_NS subst_S)
    show "isOK (rel_impl.s ?rp st) \<Longrightarrow> st \<in> ?S" for st
      by (metis check_neg_s create_negpoly_rel_impl_def cx rel_impl.simps(4))
    show "isOK (rel_impl.ns (?rp) st) \<Longrightarrow> st \<in> ?NS"  for st 
      by (metis check_neg_ns create_negpoly_rel_impl_def cx rel_impl.simps(5))
    show "isOK (rel_impl.nst (?rp) st) \<Longrightarrow> st \<in> ?NS" for st by simp
    show "irrefl ?S" 
      by (simp add: inter_neg_s_def irreflI irrefl_inter_neg_s)
    show afc:"af_compatible (rel_impl.af (?rp)) ?NS" by (simp add: full_af)
    show "af_compatible (rel_impl.af (?rp)) ?NS" using afc by auto
    let ?af' = "rel_impl.mono_af ?rp"
    show "af_monotone (rel_impl.mono_af (?rp)) ?S" unfolding inter_neg_s_def af_monotone_def
      by (simp add: empty_af empty_af_def)
    show "not_subterm_rel_info inter_neg_ns (rel_impl.not_wst (?rp))" by simp
    show "not_subterm_rel_info inter_neg_s (rel_impl.not_sst (?rp))" by simp
    have ok:"isOK (rel_impl.standard (?rp))" by simp
    from poly_neg_gt_trans transp_trans
    show ti:"isOK (rel_impl.standard (?rp)) \<Longrightarrow> trans ?S" 
      using ok unfolding inter_neg_s_def transp_def by blast
    show "isOK (rel_impl.standard (?rp)) \<Longrightarrow> ?S \<subseteq> ?NS" using ok inter_neg_s_ns by auto
    show comp_s_ns:"isOK (rel_impl.standard (?rp)) \<Longrightarrow> ?S O ?NS \<subseteq> ?S" unfolding inter_neg_s_def inter_neg_ns_def 
      using poly_neg_compat2 by auto
    show comp_ns_s:"isOK (rel_impl.standard (?rp)) \<Longrightarrow> ?NS O ?S \<subseteq> ?S" unfolding inter_neg_s_def 
      using inter_neg_ns_def poly_neg_compat by fastforce
    show "isOK (rel_impl.top_mono (?rp)) \<or> isOK (rel_impl.standard (?rp)) \<Longrightarrow> trans ?S" using ti by simp
    show "isOK (rel_impl.top_mono (?rp)) \<or> isOK (rel_impl.standard (?rp)) \<Longrightarrow> ?NS O ?S \<subseteq> ?S" using comp_ns_s ok by auto
    show "isOK (rel_impl.top_mono (?rp)) \<or> isOK (rel_impl.standard (?rp)) \<Longrightarrow> ?S O ?NS \<subseteq> ?S" using comp_s_ns ok by auto
    have "\<And>sig. funas_trs (set U) \<subseteq> set sig \<Longrightarrow> isOK (rel_impl.mono (?rp) sig) \<Longrightarrow> False" by auto
    then show "\<And>sig. funas_trs (set U) \<subseteq> set sig \<Longrightarrow> isOK (rel_impl.mono (?rp) sig) \<Longrightarrow> ctxt.closed ?S" by auto
    show "isOK (rel_impl.SN (?rp)) \<Longrightarrow> SN inter_neg_s" by simp
    show "isOK (rel_impl.ce_compat (?rp)) \<Longrightarrow> ce_compatible ?NS" by simp
    show "\<And>sig. funas_trs (set U) \<subseteq> set sig \<Longrightarrow> isOK (rel_impl.ce_compat (?rp)) \<Longrightarrow>
      isOK (rel_impl.mono (?rp) sig) \<Longrightarrow> ce_compatible ?S" by simp
    show "isOK (rel_impl.co_rewr (?rp)) \<Longrightarrow> ?NS \<inter> ?S\<inverse> = {}" using comp_ns_s_inv by auto
    let ?cpx = "rel_impl.cpx ?rp"
    let ?cpx' = "\<lambda> cm cc. isOK(?cpx cm cc)"
    show "\<And>cm cc. isOK (rel_impl.cpx (?rp) cm cc) \<Longrightarrow> deriv_bound_measure_class ?S cm cc" 
    proof -
      fix cm cc
      assume "?cpx' cm cc"
      hence "isOK (no_complexity_check cm cc)" by simp
      then show "deriv_bound_measure_class ?S cm cc" 
        by (meson isOK_no_complexity)
    qed
  qed
qed

instance int :: poly_carrier' .. 

lemma poly_order_neg_lemmma:
  assumes nassign:"isOK(check_poly_inter_list_neg I)" 
  shows "poly_order_neg (>) UNIV (poly_inter_list_to_inter_neg (0 :: int) I)"
proof (unfold_locales, (force+)[6])
  interpret order_pair_neg "(>)::int\<Rightarrow>int\<Rightarrow>bool" UNIV 
    by (simp add: order_pair_neg_def)
  have asm:"(\<And>gt F I a b. poly_order_neg gt F I \<Longrightarrow> (a, b) \<in> F \<Longrightarrow> order_pair_neg.poly_neg_ge zero_poly (I (a, b)))"
    using poly_order_neg.neg_I by auto
  from check_poly_inter_list_neg
  have main:"\<And>f n. order_pair_neg.poly_weak_neg_mono_all (poly_inter_list_to_inter_neg (0 :: int) I (f,n)) \<and> ((zero_poly \<ge>pn poly_inter_list_to_inter_neg (0 :: int) I (f,n)))" 
    using nassign by blast 
  then show "\<And>fn. fn \<in> UNIV \<Longrightarrow> zero_poly \<ge>pn poly_inter_list_to_inter_neg 0 I fn" by auto
  show "\<And>fn. order_pair_neg.poly_weak_neg_mono_all (poly_inter_list_to_inter_neg 0 I fn)" using main by auto
  let ?m = "Suc (max_list (map (snd o fst) I))"
  show "\<exists>n. \<forall>f m. n \<le> m \<longrightarrow> poly_inter_list_to_inter_neg 0 I (f, m) = zero_poly" 
  proof (rule exI[of _ ?m], intro allI impI)
    fix f m
    assume m: "?m \<le> m"
    show "poly_inter_list_to_inter_neg 0 I (f, m) = zero_poly"
    proof (cases "map_of I (f, m)")
      case None
      hence "default_I' 0 (snd (f, m)) = zero_poly" 
        using default_I'_def by auto
      then show ?thesis using None
        by (simp add: poly_inter_list_to_inter_neg_def)
    next
      case (Some p)
      from map_of_SomeD[OF this] have "((f,m),p) \<in> set I" .
      then have "m \<in> set (map (snd o fst) I)" by force
      from max_list[OF this] m show ?thesis by auto
    qed
  qed
qed

end