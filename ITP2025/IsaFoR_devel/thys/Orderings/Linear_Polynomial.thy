(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Linear Polynomials\<close>

theory Linear_Polynomial
imports
  Show.Show
  Certification_Monads.Check_Monad
  "Abstract-Rewriting.Abstract_Rewriting"
  Linear_Poly_Complexity
  Show.Shows_Literal
begin

type_synonym ('v, 'a) p_ass = "'v \<Rightarrow> 'a"
type_synonym ('v, 'a) p_vars = "('v \<times> 'a) list"
datatype ('v,'a) l_poly = LPoly 'a "('v, 'a) p_vars"

instantiation l_poly :: (showl,showl) showl
begin
fun showsl_l_poly :: "('a, 'b) l_poly \<Rightarrow> showsl" where 
  "showsl_l_poly (LPoly c xcs) = showsl c o (if xcs = [] then id else showsl_lit (STR '' + '')
     o showsl_sep (\<lambda> (x,c). showsl c o showsl_lit (STR '' * '') o showsl x) (showsl_lit (STR '' + '')) xcs)" 
definition showsl_list_l_poly :: "('a, 'b) l_poly list \<Rightarrow> showsl" where
  "showsl_list_l_poly = default_showsl_list showsl"
instance ..
end


fun get_nc_lpoly :: "('v, 'a) l_poly \<Rightarrow> ('v, 'a) p_vars" 
where
  "get_nc_lpoly (LPoly _ nc) = nc"

fun
  lookup_rest :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('b \<times> ('a \<times> 'b) list) option"
where
  "lookup_rest x [] = None" |
  "lookup_rest x ((y, c) # ycs) =
    (if x = y then Some (c, ycs)
    else 
      (case lookup_rest x ycs of
        None \<Rightarrow> None
      | Some (d, yccs) \<Rightarrow> Some (d, (y, c) # yccs)))"

lemma lookup_rest_set:
  assumes "lookup_rest a ab = Some (b, ab')"
  shows "set ab = insert (a, b) (set ab')"
  using assms
proof (induct ab arbitrary: ab')
  case (Cons entry ab)
  obtain a' b' where entry: "entry = (a', b')" by force
  note Cons = Cons[unfolded entry lookup_rest.simps]
  show ?case
  proof (cases "a' = a")
    case True
    with Cons show ?thesis unfolding entry by auto
  next
    case False
    show ?thesis 
    proof (cases "lookup_rest a ab")
      case (Some res)
      obtain b'' ab'' where res: "res = (b'', ab'')" by force
      from Cons(2) False have Some: "lookup_rest a ab = Some (b, ab'')"
        and ab: "ab' = (a', b') # ab''" by (auto simp: Some res)
      from Cons(1)[OF Some]
        show ?thesis unfolding ab entry by auto
    qed (insert Cons(2) False, auto)
  qed
qed auto


context 
  fixes R :: "('a, 'b) partial_object_scheme" (structure)
begin

definition wf_ass :: "('v, 'a) p_ass \<Rightarrow> bool"
where
  "wf_ass \<alpha> \<longleftrightarrow> range \<alpha> \<subseteq> carrier R" 
  (* one might check whether using FuncSet: \<alpha> \<in> UNIV \<rightarrow> carrier R simplifies reasoning *)

definition wf_pvars :: "('v, 'a) p_vars \<Rightarrow> bool"
where 
  "wf_pvars vas \<longleftrightarrow> set (map snd vas) \<subseteq> carrier R"

fun wf_lpoly :: "('v, 'a) l_poly \<Rightarrow> bool" where 
  "wf_lpoly (LPoly a vas) \<longleftrightarrow> a \<in> carrier R \<and> wf_pvars vas"

end

context 
  fixes R :: "('a, 'b) monoid_scheme" (structure)
begin

fun list_prod :: "'a list \<Rightarrow> 'a" where 
  "list_prod [] = \<one>"
| "list_prod (x # xs) = x \<otimes> (list_prod xs)"

lemma wf_list_prod_gen:
  assumes "\<one> \<in> carrier G"
    and "\<And> x y. x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> x \<otimes> y \<in> carrier G"
  shows "set as \<subseteq> carrier G \<Longrightarrow> list_prod as \<in> carrier G"
  using assms by (induct as) auto

end

context 
  fixes R :: "('a, 'b) ring_scheme" (structure)
begin

definition coeffs_of_pvars :: "('v, 'a) p_vars \<Rightarrow> 'a list"
where
  "coeffs_of_pvars vas = \<zero> # map snd vas"
      
fun coeffs_of_lpoly :: "('v, 'a) l_poly \<Rightarrow> 'a list"
where
  "coeffs_of_lpoly (LPoly a vas) = a # coeffs_of_pvars vas"

fun add_var :: "'v \<Rightarrow> 'a \<Rightarrow> ('v, 'a) p_vars \<Rightarrow> ('v, 'a) p_vars" where 
  "add_var x a [] = [(x, a)]"
| "add_var x a ((y, b) # vas) =
    (if x = y then (let s = a \<oplus> b in if s = \<zero> then vas else (x, s) # vas)
    else ((y, b) # add_var x a vas))"

fun sum_pvars :: "('v, 'a) p_vars \<Rightarrow> ('v, 'a) p_vars \<Rightarrow> ('v, 'a) p_vars" where
  "sum_pvars [] vbs = vbs"
| "sum_pvars ((x, a) # vas) vbs =
    (if a = \<zero> then sum_pvars vas vbs
    else sum_pvars vas (add_var x a vbs))"

fun sum_lpoly :: "('v, 'a) l_poly \<Rightarrow> ('v, 'a) l_poly \<Rightarrow> ('v, 'a) l_poly" where 
  "sum_lpoly (LPoly a vas) (LPoly b vbs) = LPoly (a \<oplus> b) (sum_pvars vas vbs)"

fun mul_pvars :: "'a \<Rightarrow> ('v, 'a) p_vars \<Rightarrow> ('v, 'a) p_vars" where 
  "mul_pvars a [] = []"
| "mul_pvars a ((x, b) # vas) =
    (let p = a \<otimes> b;
         res = mul_pvars a vas in
    if p = \<zero> then res else (x, p) # res)"

fun mul_lpoly :: "'a \<Rightarrow> ('v, 'a) l_poly \<Rightarrow> ('v, 'a) l_poly" where
 "mul_lpoly a (LPoly b vas) = LPoly (a \<otimes> b) (mul_pvars a vas)"

abbreviation c_lpoly :: "'a \<Rightarrow> ('v, 'a) l_poly" where 
  "c_lpoly c \<equiv> LPoly c []"

abbreviation zero_lpoly :: "('v, 'a) l_poly" where 
  "zero_lpoly \<equiv> c_lpoly \<zero>"

abbreviation lpoly_monoid :: "('v, 'a) l_poly monoid" where
  "lpoly_monoid \<equiv> \<lparr> carrier = Collect (wf_lpoly R), mult = sum_lpoly, one = zero_lpoly \<rparr>"

abbreviation list_sum where
  "list_sum \<equiv> list_prod (add_monoid R)"

abbreviation list_sum_lpoly where
  "list_sum_lpoly \<equiv> list_prod lpoly_monoid"

end

definition (in semiring) zero_ass :: "('v, 'a) p_ass"
where
  "zero_ass = (\<lambda> x. \<zero>)"

context monoid
begin

lemma wf_list_prod[simp,intro!]: "set as \<subseteq> carrier G \<Longrightarrow> list_prod G as \<in> carrier G"
  by (rule wf_list_prod_gen, auto)

lemma list_prod_one[simp]: "list_prod G (map (\<lambda> _. \<one>) ts) = \<one>"
  by (induct ts, auto)

lemma list_prod_mono:
  assumes rel1: "rel \<one> \<one>" 
    and rel_mono: "\<And> x y z u. rel x y \<Longrightarrow> rel z u \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G
    \<Longrightarrow> u \<in> carrier G \<Longrightarrow> rel (x \<otimes> z) (y \<otimes> u)"
  shows "f \<in> set ts \<rightarrow> carrier G \<Longrightarrow> g \<in> set ts \<rightarrow> carrier G \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> rel (f t) (g t)) 
    \<Longrightarrow> rel (list_prod G (map f ts)) (list_prod G (map g ts))"
proof (induct ts)
  case (Cons t ts)
  show ?case 
    unfolding list_prod.simps list.simps by (rule rel_mono, insert Cons, auto)
qed (auto simp: rel1)

lemma pos_list_prod:
  assumes rel1: "rel \<one> \<one>" 
    and rel_mono: "\<And> x y z u. rel x y \<Longrightarrow> rel z u \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G
    \<Longrightarrow> u \<in> carrier G \<Longrightarrow> rel (x \<otimes> z) (y \<otimes> u)"
    and as: "set as \<subseteq> carrier G" "\<And> a. a \<in> set as \<Longrightarrow> rel a \<one>"
  shows "rel (list_prod G as) \<one>"
proof -
  have "?thesis = rel (list_prod G (map id as)) (list_prod G (map (\<lambda> _. \<one>) as))" by simp
  also have "\<dots>"
    by (rule list_prod_mono[of rel, OF rel1 rel_mono], insert as, auto)
  finally show ?thesis .
qed

end

context semiring
begin

lemmas wf_list_sum = add.wf_list_prod

fun eval_pvars :: "('v, 'a) p_ass \<Rightarrow> ('v, 'a) p_vars \<Rightarrow> 'a" where 
  "eval_pvars _ [] = \<zero>"
| "eval_pvars \<alpha> ((x, a) # vas) = (a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas)"

fun eval_lpoly :: "('v, 'a) p_ass \<Rightarrow> ('v, 'a) l_poly \<Rightarrow> 'a" where 
  "eval_lpoly \<alpha> (LPoly a vas) = a \<oplus> eval_pvars \<alpha> vas"

lemma wf_lpoly_coeff:
  assumes wf: "wf_lpoly R p" and mem: "a \<in> set (coeffs_of_lpoly R p)"
  shows "a \<in> carrier R"
proof -
  obtain b as where p: "p = LPoly b as" by (cases p, auto)
  note wf = wf[unfolded p, simplified]
  show ?thesis
  proof (cases "a = b")
    case True
    with wf show ?thesis by auto
  next
    case False
    with mem[unfolded p] have mem: "a \<in> set (coeffs_of_pvars R as)" by auto
    from wf have "wf_pvars R as" ..
    with mem show ?thesis
    proof (induct as)
      case Nil
      then show ?case unfolding coeffs_of_pvars_def by auto
    next
      case (Cons b bs)
      show ?case
      proof (cases "a = snd b")
        case True
        with Cons(3) show ?thesis unfolding wf_pvars_def  by auto
      next
        case False
        with Cons(2) have mem: "a \<in> set (coeffs_of_pvars R bs)" unfolding coeffs_of_pvars_def by auto
        from False Cons(3) have wf: "wf_pvars R bs" unfolding wf_pvars_def by auto
        from Cons(1)[OF mem wf] show ?thesis .
      qed
    qed
  qed
qed

lemma wf_mul_pvars[simp]: 
  assumes wf_pvars: "wf_pvars R vas"
    and wf_elem: "a \<in> carrier R"
  shows "wf_pvars R (mul_pvars R a vas)"
using wf_pvars  
unfolding wf_pvars_def
proof (induct vas)
  case (Cons yb vas)
  obtain y b where yb: "yb = (y,b)" by force
  show ?case using yb Cons wf_elem by (auto simp: Let_def)
qed simp

lemma wf_add_var[simp]: 
  assumes wf_pvars: "wf_pvars R vas"
    and [simp]: "a \<in> carrier R"
  shows "wf_pvars R (add_var R x a vas)"
using wf_pvars  
unfolding wf_pvars_def
proof (induct vas)
  case (Cons yb vas)
  obtain y b where yb: "yb = (y,b)" by force
  show ?case using yb Cons by (auto simp: Let_def)
qed auto

lemma wf_sum_pvars[simp]: 
  assumes wf_pvars_a: "wf_pvars R vas"
    and wf_pvars_b: "wf_pvars R vbs"
  shows "wf_pvars R (sum_pvars R vas vbs)"
using wf_pvars_a  wf_pvars_b
unfolding wf_pvars_def[where vas = vas]
proof (induct vas arbitrary: vbs)
  case (Cons xa vas)
  then show ?case by (cases xa, auto)
qed simp

lemma wf_eval_pvars[simp,intro]:
  assumes wf_ass: "wf_ass R \<alpha>"
    and wf_pvars: "wf_pvars R vas"
  shows "eval_pvars \<alpha> vas \<in> carrier R"
using wf_pvars
unfolding wf_pvars_def
proof (induct vas)
  case (Cons xa vas)
  show ?case
  proof (cases xa)
    case (Pair x a)
    from wf_ass have "\<alpha> x \<in> carrier R" unfolding wf_ass_def by auto
    with Pair Cons show ?thesis by auto
  qed
qed simp

lemma mul_pvars_sound[simp]: 
  assumes wf_pvars: "wf_pvars R vas"
    and wf_a: "a \<in> carrier R"
    and wf_ass: "wf_ass R \<alpha>"
  shows "eval_pvars \<alpha> (mul_pvars R a vas) = a \<otimes> (eval_pvars \<alpha> vas)"
using wf_pvars  
proof (induct vas)
  case Nil then show ?case by (simp add: wf_a)
next
  case (Cons xb vas)
  show ?case
  proof (cases xb)
    case (Pair x b)
    with Cons have wf_b: "b \<in> carrier R" unfolding wf_pvars_def by auto
    from Cons have wf_vas: "wf_pvars R vas" unfolding wf_pvars_def by auto
    from wf_ass have wf_x: "\<alpha> x \<in> carrier R" unfolding wf_ass_def by auto
    note wf_eval = wf_eval_pvars[OF wf_ass wf_vas] 
    show ?thesis 
    proof (cases "a \<otimes> b = \<zero>")
      case True
      with Pair Cons have "eval_pvars \<alpha> (mul_pvars R a (xb # vas)) = eval_pvars \<alpha> (mul_pvars R a vas)" by (simp add: Let_def)
      also have "\<dots> = a \<otimes> eval_pvars \<alpha> vas" using Cons wf_vas wf_a by auto
      also have "\<dots> = a \<otimes> (b \<otimes> \<alpha> x) \<oplus> \<dots>" unfolding m_assoc[OF wf_a wf_b wf_x,symmetric] True using wf_a wf_eval wf_x by algebra
      also have "\<dots> = a \<otimes> (b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas)" using wf_vas wf_a wf_b wf_x wf_eval by algebra
      finally show ?thesis using Pair by auto
    next
      case False
      with Cons Pair have "eval_pvars \<alpha> (mul_pvars R a (xb # vas)) = eval_pvars \<alpha> ((x,a\<otimes>b) # mul_pvars R a vas)" by (simp add: Let_def)
      also have "\<dots> = a \<otimes> (b \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas)" using Cons wf_vas wf_vas wf_a wf_b wf_x wf_ass wf_eval
        by (auto, algebra)
      finally show ?thesis using Pair by auto
    qed
  qed
qed

lemma add_var_sound[simp]: 
  assumes wf_pvars: "wf_pvars R vas"
    and wf_a: "a \<in> carrier R"
    and wf_ass: "wf_ass R \<alpha>"
  shows "eval_pvars \<alpha> (add_var R x a vas) = a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas"
using wf_pvars 
proof (induct vas)
  case (Cons yb vas)
  show ?case
  proof (cases yb)
    case (Pair y b)
    with Cons have wf_b: "b \<in> carrier R" unfolding wf_pvars_def by auto
    from Cons have wf_vas: "wf_pvars R vas" unfolding wf_pvars_def by auto
    from wf_ass have wf_x: "\<alpha> x \<in> carrier R" unfolding wf_ass_def by auto
    from wf_ass have wf_y: "\<alpha> y \<in> carrier R" unfolding wf_ass_def by auto
    note wf_eval = wf_eval_pvars[OF wf_ass wf_vas]
    show ?thesis 
    proof (cases "x = y")
      case True note oTrue = this
      show ?thesis 
      proof (cases "a \<oplus> b = \<zero>")
        case True
        with oTrue Pair have "eval_pvars \<alpha> (add_var R x a (yb # vas)) = eval_pvars \<alpha> (vas)" by (simp add: Let_def)
        also have "\<dots> = (a \<oplus> b) \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas" using True wf_x wf_ass wf_vas by auto
        also have "\<dots> = a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> ((y,b) # vas)" using wf_ass wf_x wf_vas wf_a wf_b wf_eval unfolding \<open>x = y\<close>
          by (auto, algebra)
        finally show ?thesis using Pair by auto
      next
        case False
        with oTrue Pair have "eval_pvars \<alpha> (add_var R x a (yb # vas)) = eval_pvars \<alpha> ((x,a\<oplus>b) # vas)" by (simp add: Let_def)
        also have "\<dots> = (a \<oplus> b) \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas" using True wf_x wf_ass wf_vas by auto
        also have "\<dots> = a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> ((y,b) # vas)" using wf_ass wf_x wf_vas wf_a wf_b wf_eval unfolding \<open>x = y\<close> 
          by (auto, algebra)
        finally show ?thesis using Pair by auto
      qed
    next
      case False
      term group
      with Pair  False have "eval_pvars \<alpha> (add_var R x a (yb # vas)) = eval_pvars \<alpha> ((y,b) # (add_var R x a vas))" by (simp add: Let_def)
      also have "\<dots> = b \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> (add_var R x a vas)" by auto
      also have "\<dots> = b \<otimes> \<alpha> y \<oplus> (a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas)" using Cons wf_vas by auto
      also have "\<dots> = a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> ((y,b) # vas)" using wf_ass wf_x wf_y wf_vas wf_a wf_b wf_eval
        by (auto, algebra)
      finally show ?thesis using Pair by auto
    qed
  qed
qed simp

lemma sum_pvars_sound[simp]:
  assumes wf_ass: "wf_ass R \<alpha>"
    and wf_pvars_a: "wf_pvars R vas"
    and wf_pvars_b: "wf_pvars R vbs" 
  shows "eval_pvars \<alpha> (sum_pvars R vas vbs) = eval_pvars \<alpha> vas \<oplus> eval_pvars \<alpha> vbs"
using wf_pvars_a wf_pvars_b
proof (induct vas arbitrary: vbs)
  case Nil then show ?case using wf_ass by auto
next
  case (Cons xa vas)
  obtain x a where xa: "xa = (x,a)" by force
  with Cons wf_ass have wf: "wf_pvars R vas" "a \<in> carrier R" "\<alpha> x \<in> carrier R" 
    unfolding wf_pvars_def wf_ass_def by auto
  have "eval_pvars \<alpha> vas \<in> carrier R" using wf_eval_pvars wf_ass wf by auto
  note wf = wf this
  show ?case
  proof (cases "a = \<zero>")
    case True
    then show ?thesis using xa Cons wf by auto
  next
    case False
    from wf Cons have "wf_pvars R (add_var R x a vbs)" by auto
    with False show ?thesis 
      using xa Cons wf wf_eval_pvars[OF wf_ass Cons(3)] wf_ass by (auto, algebra)
  qed
qed

lemma wf_sum_lpoly: 
  assumes wf_p: "wf_lpoly R p" 
    and wf_q: "wf_lpoly R q" 
  shows "wf_lpoly R (sum_lpoly R p q)"
using assms
by (cases p, cases q, auto)

lemma wf_mul_lpoly: 
  assumes wf_a: "a \<in> carrier R" 
    and wf_p: "wf_lpoly R p" 
  shows "wf_lpoly R (mul_lpoly R a p)"
using assms
by (cases p, auto)

lemma wf_eval_lpoly[simp, intro]: 
  assumes wf_ass: "wf_ass R \<alpha>"
    and wf_p: "wf_lpoly R p"
  shows "eval_lpoly \<alpha> p \<in> carrier R"
using assms by (cases p, auto)

lemma sum_poly_sound:
  assumes wf_ass: "wf_ass R \<alpha>"
    and wf_p: "wf_lpoly R p" 
    and wf_q: "wf_lpoly R q" 
  shows "eval_lpoly \<alpha> (sum_lpoly R p q) = eval_lpoly \<alpha> p \<oplus> eval_lpoly \<alpha> q"
proof (cases p)
  case (LPoly a vas) note oLPoly = this
  show ?thesis
  proof (cases q)
    case (LPoly b vbs)
    with oLPoly assms have "eval_pvars \<alpha> vas \<in> carrier R" "eval_pvars \<alpha> vbs \<in> carrier R" by auto
    with LPoly oLPoly assms wf_eval_pvars[OF wf_ass] show ?thesis 
      by (auto, algebra)
  qed
qed

lemma mul_poly_sound:
  assumes wf_ass: "wf_ass R \<alpha>"
    and wf_a: "a \<in> carrier R"
    and wf_p: "wf_lpoly R p" 
  shows "eval_lpoly \<alpha> (mul_lpoly R a p) = a \<otimes> eval_lpoly \<alpha> p"
proof (cases p)
  case (LPoly b vbs)
  with wf_p have wfb: "b \<in> carrier R" and wfbs: "wf_pvars R vbs" by auto
  from wf_ass wfbs wf_eval_pvars[OF wf_ass wfbs] wfb wf_a show ?thesis unfolding LPoly
    by (auto, algebra)
qed

lemma wf_zero_ass[simp]: "wf_ass R zero_ass"
unfolding wf_ass_def zero_ass_def by auto 

lemma lookup_rest_sound: 
  assumes lookup: "lookup_rest y vas = Some (a,vas')"
    and wf_ass: "wf_ass R \<alpha>"
    and wf_vas: "wf_pvars R vas"
  shows "eval_pvars \<alpha> vas = a \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> vas' \<and> wf_pvars R vas' \<and> a \<in> carrier R" 
using lookup wf_vas
proof (induct vas arbitrary: vas')
  case (Cons xb vas)
  show ?case 
  proof (cases xb)
    case (Pair x b)
    with Cons have wf_b: "b \<in> carrier R" and wf_vas: "wf_pvars R vas" and wf_x: "\<alpha> x \<in> carrier R" using wf_ass unfolding wf_ass_def wf_pvars_def by auto
    show ?thesis 
    proof (cases "x = y")
      case True
      with Pair Cons have "a = b \<and> vas' = vas" by auto
      with wf_b wf_vas Pair True show ?thesis by auto
    next
      case False
      show ?thesis
      proof (cases "lookup_rest y vas")
        case None
        with Pair False have "lookup_rest y ((x,b) # vas) = None" by auto
        with Cons Pair show ?thesis by simp
      next
        case (Some res)
        show ?thesis 
        proof (cases res)
          case (Pair c vbs)
          with Some False \<open>xb = (x,b)\<close> have "lookup_rest y (xb # vas) = Some (c,(x,b) # vbs)" by simp
          with Cons have ca: "c = a" and vas': "vas' = (x,b) # vbs" by auto
          from Some Pair Cons ca wf_vas have rec: "eval_pvars \<alpha> vas = a \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> vbs"  and wf_vbs: "wf_pvars R vbs" and wf_a: "a \<in> carrier R" by auto
          from wf_eval_pvars[OF wf_ass] wf_vbs have wf_evbs: "eval_pvars \<alpha> vbs \<in> carrier R" by auto
          from wf_ass have wf_y: "\<alpha> y \<in> carrier R" unfolding wf_ass_def by auto
          show ?thesis using \<open>xb = (x,b)\<close> wf_b vas' rec wf_evbs wf_vbs wf_a wf_y wf_ass wf_b wf_x
            by (auto simp: wf_pvars_def, algebra)
        qed
      qed
    qed
  qed
qed simp

lemma wf_list_sum_lpoly: "set as \<subseteq> carrier (lpoly_monoid R) \<Longrightarrow> 
  list_sum_lpoly R as \<in> carrier (lpoly_monoid R)"
  by (rule wf_list_prod_gen, insert wf_sum_lpoly, auto simp: wf_pvars_def)

end

context ordered_semiring
begin

definition pos_pvars :: "('v,'a)p_vars \<Rightarrow> bool" where 
  "pos_pvars vas \<longleftrightarrow> (\<forall> va \<in> set vas. snd va \<succeq> \<zero>)"

definition pos_coeffs :: "('v,'a)l_poly \<Rightarrow> bool" where
  "pos_coeffs p = pos_pvars (get_nc_lpoly p)"

lemmas poly_simps = geq_refl
declare poly_simps[simp]

lemma plus_right_mono:
  assumes ge: "y \<succeq> z" and carr: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" 
  shows "x \<oplus> y \<succeq> x \<oplus> z" 
proof -
  have "?thesis = (y \<oplus> x \<succeq> z \<oplus> x)" using carr by algebra
  also have "\<dots>" by (rule plus_left_mono[OF ge], insert carr, auto)
  finally show ?thesis .
qed

lemma plus_left_right_mono: "\<lbrakk>x \<succeq> y; z \<succeq> u; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R; u \<in> carrier R\<rbrakk> \<Longrightarrow> x \<oplus> z \<succeq> y \<oplus> u"
  by (rule geq_trans[OF plus_left_mono plus_right_mono], auto)

lemma pos_list_sum: "(\<And> a. a \<in> set as \<Longrightarrow> a \<in> carrier R \<and> (a :: 'a) \<succeq> \<zero>) \<Longrightarrow> list_sum R as \<succeq> \<zero>"
  by (rule add.pos_list_prod[of "(\<succeq>)", OF geq_refl plus_left_right_mono], auto)

lemma list_sum_mono: "(\<And> t. t \<in> set ts \<Longrightarrow> f t \<succeq> g t \<and> f t \<in> carrier R \<and> g t \<in> carrier R) \<Longrightarrow>
  list_sum R (map f ts) \<succeq> list_sum R (map g ts)"
  by (rule add.list_prod_mono[of "(\<succeq>)", OF geq_refl plus_left_right_mono], auto)

lemma sum_pos:
  assumes "a \<succeq> \<zero>" and "b \<succeq> \<zero>" and "a \<in> carrier R" and "b \<in> carrier R"
  shows "a \<oplus> b \<succeq> \<zero>"
proof -
  have "a \<oplus> b \<succeq> \<zero> \<oplus> \<zero>" by (rule plus_left_right_mono, auto simp: assms)
  then show ?thesis by auto
qed

lemma pos_mul_pvars:
  assumes pos_vas: "pos_pvars vas"
    and   wf_vas: "wf_pvars R vas"
    and   pos_a: "a \<succeq> \<zero>"
    and   wf_a: "a \<in> carrier R"
  shows "pos_pvars (mul_pvars R a vas)"
using pos_vas wf_vas unfolding pos_pvars_def
proof (induct vas)
  case (Cons xb vas)
  show ?case
  proof (cases xb)
    case (Pair x b)
    with Cons have wf_b: "b \<in> carrier R" and pos_b: "b \<succeq> \<zero>" unfolding wf_pvars_def by auto
    from Cons have "wf_pvars R vas" unfolding wf_pvars_def by auto
    with Cons have rec: "\<forall> va \<in> set (mul_pvars R a vas). snd va \<succeq> \<zero>" by auto
    show ?thesis 
    proof (cases "a \<otimes> b = \<zero>")
      case True
      with Cons Pair have "mul_pvars R a (xb # vas) = mul_pvars R a vas" by (simp add: Let_def)
      with rec show ?thesis by auto
    next
      case False
      have "a \<otimes> b \<succeq> \<zero> \<otimes> \<zero>" by (rule geq_trans[where y = "a \<otimes> \<zero>"], rule times_right_mono, auto simp: wf_a pos_a pos_b wf_b)
      then have pos_ab: "a \<otimes> b \<succeq> \<zero>" by simp            
      from False Pair Cons have "mul_pvars R a (xb # vas) = (x,a\<otimes>b) # mul_pvars R a vas" by (simp add: Let_def)
      with rec pos_ab show ?thesis by auto
    qed
  qed
qed simp

declare mul_pvars.simps[simp del]

lemma pos_add_var: 
  assumes wf_pvars: "wf_pvars R vas"
    and pos_pvars: "pos_pvars vas"
    and wf_a: "a \<in> carrier R"
    and pos_a: "a \<succeq> \<zero>"
  shows "pos_pvars (add_var R x a vas)"
using wf_pvars  pos_pvars unfolding pos_pvars_def
proof (induct vas)
  case Nil then show ?case by (simp add: pos_a)
next
  case (Cons yb vas)
  show ?case
  proof (cases yb)
    case (Pair y b)
    with Cons have wf_b: "b \<in> carrier R" and pos_b: "b \<succeq> \<zero>" unfolding wf_pvars_def by auto
    from Cons have "wf_pvars R vas" unfolding wf_pvars_def by auto
    with Cons have rec: "\<forall> va \<in> set (add_var R x a vas). snd va \<succeq> \<zero>" by auto
    show ?thesis 
    proof (cases "x = y")
      case True note oTrue = this
      show ?thesis 
      proof (cases "a \<oplus> b = \<zero>")
        case True
        with oTrue Pair have "add_var R x a (yb # vas) = vas" by (simp add: Let_def)
        with Cons show ?thesis by auto
      next
        case False
        with True Pair have id: "add_var R x a (yb # vas) = (x,a\<oplus>b) # vas" by (simp add: Let_def)
        have "a \<oplus> b \<succeq> \<zero> \<oplus> \<zero>" by (rule plus_left_right_mono, auto simp: pos_a pos_b wf_a wf_b)
        with Cons id show ?thesis by auto
      qed
    next
      case False
      with Pair have "add_var R x a (yb # vas) = (y,b) # (add_var R x a vas)" by (simp add: Let_def)
      with pos_b rec show ?thesis by auto 
    qed
  qed
qed

declare add_var.simps[simp del]

lemma pos_sum_pvars: 
  assumes pos_vas: "pos_pvars vas"
    and   wf_vas: "wf_pvars R vas"
    and   pos_vbs: "pos_pvars vbs"
    and   wf_vbs: "wf_pvars R vbs"
  shows "pos_pvars (sum_pvars R vas vbs)"
using assms 
proof (induct vas arbitrary: vbs)
  case (Cons xa vas)
  from Cons(2) Cons(3)
  have wf_vas: "wf_pvars R vas" and pos_vas: "pos_pvars vas" unfolding wf_pvars_def pos_pvars_def by auto
  show ?case
  proof (cases xa)
    case (Pair x a)
    with Cons(2) Cons(3) have wf_a: "a \<in> carrier R" and pos_a: "a \<succeq> \<zero>" unfolding wf_pvars_def pos_pvars_def by auto
    show ?thesis 
    proof (cases "a = \<zero>")
      case True
      then show ?thesis using Pair Cons(1)[OF pos_vas wf_vas Cons(4) Cons(5)] unfolding pos_pvars_def by auto
    next
      case False
      from wf_a Cons have wf_xvbs: "wf_pvars R (add_var R x a vbs)" by auto
      have "pos_pvars (add_var R x a vbs)" by (rule pos_add_var, auto simp: Cons wf_a pos_a)
      with Cons wf_xvbs wf_vas pos_vas have "pos_pvars (sum_pvars R vas (add_var R x a vbs))" by auto      
      with False show ?thesis using Pair by auto
    qed
  qed
qed simp

declare sum_pvars.simps[simp del]

lemma pos_sum_lpoly: 
  assumes wf_p: "wf_lpoly R p" 
    and wf_q: "wf_lpoly R q" 
    and pos_p: "pos_coeffs p"
    and pos_q: "pos_coeffs q"
  shows "pos_coeffs (sum_lpoly R p q)"
  using assms unfolding pos_coeffs_def
  by (cases p, cases q, simp add: pos_sum_pvars)

lemma pos_mul_lpoly: 
  assumes wf_a: "a \<in> carrier R"
    and pos_a: "a \<succeq> \<zero>"
    and wf_p: "wf_lpoly R p" 
    and pos_p: "pos_coeffs p"
  shows "pos_coeffs (mul_lpoly R a p)"
  using assms unfolding pos_coeffs_def
  by (cases p, simp add: pos_mul_pvars)

text \<open>let us head for comparing polynomials now\<close>

definition pos_ass :: "('v, 'a) p_ass \<Rightarrow> bool"
where
  "pos_ass \<alpha> \<longleftrightarrow> (\<forall> x. \<alpha> x \<succeq> \<zero>)"

lemma pos_zero_ass[simp]: "pos_ass zero_ass"
unfolding pos_ass_def zero_ass_def by auto 

definition poly_s :: "('v, 'a) l_poly rel"
where
  "poly_s = {(p, q). \<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<longrightarrow> eval_lpoly \<alpha> p \<succ> eval_lpoly \<alpha> q}"     

definition poly_ns :: "('v, 'a) l_poly rel"
where
  "poly_ns = {(p, q) . \<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<longrightarrow> eval_lpoly \<alpha> p \<succeq> eval_lpoly \<alpha> q}"     

end

context 
  fixes R :: "('a :: showl, 'b) ring_scheme" (structure)
begin

fun
  check_pvars :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('v, 'a) p_vars \<Rightarrow> ('v, 'a) p_vars \<Rightarrow> 'v check"
where
  "check_pvars rel vas [] = check_allm (\<lambda>va. check (rel (snd va) \<zero>) (fst va)) vas" |
  "check_pvars rel vas ((x, b) # vbs) = do {
    let (a', vas') = 
      (case lookup_rest x vas of
        None \<Rightarrow> (\<zero>, vas)
      | Some (a, vas'') \<Rightarrow> (a, vas''));
    check (rel a' b) x;
    check_pvars rel vas' vbs
  }"

fun
  showl_pvars :: "('v :: showl, 'a :: showl) p_vars \<Rightarrow> String.literal list"
where
  "showl_pvars  [] = []" |
  "showl_pvars  ((x, c) # vas) =
    (if c = \<one> then id else showsl c) (showl x) # showl_pvars vas"

fun
  showsl_lpoly :: "('v :: showl, 'a) l_poly \<Rightarrow> showsl"
where
  "showsl_lpoly (LPoly c cs) =
    (case showl_pvars  cs of 
      [] \<Rightarrow> showsl c
    | ss \<Rightarrow>
      (if c = \<zero> then id
      else (showsl c \<circ> showsl (STR '' + ''))) \<circ> showsl_list_gen showsl (STR '''') (STR '''') (STR '' + '') (STR '''') ss)"

end

context 
  fixes R :: "('a :: showl, 'b) ordered_semiring_scheme" (structure)

begin
fun
  check_lpoly_ns :: "('v :: showl, 'a) l_poly \<Rightarrow> ('v, 'a) l_poly \<Rightarrow> showsl check"
where
  "check_lpoly_ns (LPoly a vas) (LPoly b vbs) = do {
    check (a \<succeq> b) (showsl (STR ''problem when comparing constant parts''));
    check_pvars R (\<succeq>) vas vbs
      <+? (\<lambda>e. showsl (STR ''problem when comparing coefficients of variable '') \<circ> showsl e)
  } <+? (\<lambda>e. showsl (STR ''problem when comparing '') \<circ> showsl_lpoly R (LPoly a vas)
          \<circ> showsl (STR '' >= '') \<circ> showsl_lpoly R (LPoly b vbs) \<circ> showsl_nl \<circ> e)"

end

context 
  fixes R :: "('a :: showl, 'b) lpoly_order_semiring_scheme" (structure)
begin

fun
  check_lpoly_s :: "('v :: showl, 'a) l_poly \<Rightarrow> ('v, 'a) l_poly \<Rightarrow> showsl check"
where
  "check_lpoly_s (LPoly a vas) (LPoly b vbs) = do {
    check (a \<succ> b) (showsl (STR ''problem when comparing constant part''));
    check_pvars R (if psm then (\<succeq>) else (\<succ>)) vas vbs
      <+? (\<lambda>x. showsl (STR ''problem when comparing coefficients of variable '') \<circ> showsl x) 
  } <+? (\<lambda>s. showsl (STR ''problem when comparing '') \<circ> showsl_lpoly R (LPoly a vas)
          \<circ> showsl (STR '' > '') \<circ> showsl_lpoly R (LPoly b vbs) \<circ> showsl_nl \<circ> s)"

end

context lpoly_order
begin

lemma check_pvars_sound:
  assumes check: "isOK (check_pvars (R \<lparr> gt := gt, bound := bnd \<rparr>) (\<succeq>) vas vbs)"
    and wf_ass: "wf_ass R \<alpha>"
    and wf_vas: "wf_pvars R vas"
    and wf_vbs: "wf_pvars R vbs"
    and pos_ass: "pos_ass \<alpha>"
  shows "eval_pvars \<alpha> vas \<succeq> eval_pvars \<alpha> vbs"
using check wf_vas wf_vbs
proof (induct vbs arbitrary: vas)
  case Nil
  then have "\<forall> va \<in> set vas. (snd va \<succeq> \<zero>)" by auto
  with \<open>wf_pvars R vas\<close> have "eval_pvars \<alpha> vas \<succeq> \<zero>" 
  proof (induct vas)
    case (Cons xa vas)
    show ?case
    proof (cases xa)
      case (Pair x a)
      with Cons have wf_a: "a \<in> carrier R" and wf_vas: "wf_pvars R vas" and pos: "a \<succeq> \<zero>" unfolding wf_pvars_def by auto
      from wf_ass have wf_x: "\<alpha> x \<in> carrier R" unfolding wf_ass_def by auto
      have "a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas \<succeq> \<zero> \<oplus> eval_pvars \<alpha> vas" 
      proof (rule plus_left_mono)
        have posx: "\<alpha> x \<succeq> \<zero>" using pos_ass unfolding pos_ass_def by auto
        have ge1: "a \<otimes> \<alpha> x \<succeq> \<zero> \<otimes> \<alpha> x" by (rule times_left_mono, auto simp: pos posx wf_x wf_a)
        have ge2: "\<dots> \<succeq> \<zero> \<otimes> \<zero>" by (rule times_right_mono, auto simp: posx wf_x)
        have "a \<otimes> \<alpha> x \<succeq> \<zero> \<otimes> \<zero>" by (rule geq_trans[where y = "\<zero> \<otimes> \<alpha> x"], auto simp only: ge1 ge2, auto simp: wf_x wf_a)
        then show "a \<otimes> \<alpha> x \<succeq> \<zero>" by auto 
      qed (auto simp: wf_a wf_ass wf_x wf_vas)
      then have ge1: "a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas \<succeq> eval_pvars \<alpha> vas" using wf_vas wf_ass by auto 
      have ge2: "\<dots> \<succeq> \<zero>" using Pair Cons wf_vas by auto
      have "a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas \<succeq> \<zero>" 
        by (rule geq_trans[where y = "eval_pvars \<alpha> vas"], auto simp only: ge1 ge2,
          auto simp: wf_a wf_x wf_ass wf_vas)
      then show ?thesis using Pair by auto
    qed
  qed simp
  then show ?case by auto
next
  case (Cons yb vbs)
  let ?R = "R \<lparr> gt := gt, bound := bnd \<rparr>"
  show ?case
  proof (cases yb)
    case (Pair y b) note oPair = this
    with Cons have wf_b: "b \<in> carrier R" and wf_y: "\<alpha> y \<in> carrier R" and pos_y: "\<alpha> y \<succeq> \<zero>" and wf_vbs: "wf_pvars R vbs" 
      using wf_ass pos_ass unfolding wf_ass_def pos_ass_def wf_pvars_def by auto    
    show ?thesis 
    proof (cases "lookup_rest y vas")
      case None
      with Cons Pair wf_vbs have rec: "eval_pvars \<alpha> vas \<succeq> eval_pvars \<alpha> vbs" (is "?l \<succeq> ?r") and small_b: "\<zero> \<succeq> b" by auto
      have "\<zero> \<otimes> \<alpha> y \<succeq> b \<otimes> \<alpha> y" by (rule times_left_mono, auto simp: wf_b wf_y small_b pos_y)
      then have ge: "\<zero> \<succeq> b \<otimes> \<alpha> y" using wf_y by auto
      have "\<zero> \<oplus> ?l \<succeq> b \<otimes> \<alpha> y \<oplus> ?r" by (rule plus_left_right_mono, auto simp: rec wf_ass wf_vbs wf_b wf_y Cons ge)
      with Cons wf_ass Pair None show ?thesis by auto
    next
      case (Some avas)
      show ?thesis 
      proof (cases avas)
        case (Pair a vas')
        with Some Cons oPair have lookup: "lookup_rest y vas = Some (a,vas')" and check: "isOK(check_pvars ?R (\<succeq>) vas' vbs)" and ab: "a \<succeq> b" by auto
        have lookupRes: "eval_pvars \<alpha> vas = a \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> vas' \<and> wf_pvars R vas' \<and> a \<in> carrier R"
          by (rule lookup_rest_sound[OF lookup wf_ass \<open>wf_pvars R vas\<close>])
        with Cons check wf_vbs have rec: "eval_pvars \<alpha> vas' \<succeq> eval_pvars \<alpha> vbs" (is "?l \<succeq> ?r") by auto
        have "a \<otimes> \<alpha> y \<oplus> ?l \<succeq> b \<otimes> \<alpha> y \<oplus> ?r" 
          by (rule plus_left_right_mono, rule times_left_mono, auto simp: rec lookupRes wf_ass wf_vbs wf_y wf_b ab pos_y)
        with lookupRes Pair Some oPair show ?thesis by auto 
      qed
    qed
  qed
qed

lemma check_pvars_gt_sound:
  assumes check: "isOK(check_pvars (R \<lparr> gt := gt, bound := bnd \<rparr>) wgt vas vbs)"
    and wgt_imp_gt: "\<And> a b. (a,b) \<in> set (coeffs_of_pvars (R \<lparr> gt := gt, bound := bnd \<rparr>) vas) \<times> set (coeffs_of_pvars (R \<lparr> gt := gt, bound := bnd \<rparr>) vbs) 
    \<Longrightarrow> a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow>  wgt a b \<Longrightarrow> a \<succ> b"
    and wf_ass: "wf_ass R \<alpha>"
    and wf_vas: "wf_pvars R vas"
    and wf_vbs: "wf_pvars R vbs"
    and pos_ass: "pos_ass \<alpha>"
    and mode: "\<not> psm"
  shows "eval_pvars \<alpha> vas \<succ> eval_pvars \<alpha> vbs"
using check wgt_imp_gt wf_vas wf_vbs
proof (induct vbs arbitrary: vas)
  case Nil
  have "eval_pvars \<alpha> Nil = \<zero>" by auto
  then show ?case by (auto simp: zero_leastI mode wf_ass \<open>wf_pvars R vas\<close>)
next
  case (Cons yb vbs)
  let ?R = "R \<lparr> gt := gt, bound := bnd \<rparr>"
  show ?case
  proof (cases yb)
    case (Pair y b) note oPair = this
    with Cons have wf_b: "b \<in> carrier R" and wf_y: "\<alpha> y \<in> carrier R" and pos_y: "\<alpha> y \<succeq> \<zero>" and wf_vbs: "wf_pvars R vbs" 
      using wf_ass pos_ass unfolding wf_ass_def pos_ass_def wf_pvars_def by auto
    note coeff = coeffs_of_pvars_def
    have "set (coeffs_of_pvars ?R (yb # vbs)) = {b} \<union> set (coeffs_of_pvars ?R vbs)"
      unfolding Pair coeff by auto
    note coeffs = Cons(3)[unfolded this]
    show ?thesis 
    proof (cases "lookup_rest y vas")
      case None
      from coeffs have "\<And> a b. (a, b) \<in> set (coeffs_of_pvars ?R vas) \<times> set (coeffs_of_pvars ?R vbs) 
        \<Longrightarrow> a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> wgt a b \<Longrightarrow> a \<succ> b"
        by auto
      from Cons(1)[OF _ this] None Cons
        Pair wf_vbs have rec: "eval_pvars \<alpha> vas \<succ> eval_pvars \<alpha> vbs" and small_b: "wgt \<zero> b" by auto
      from coeffs[unfolded coeff] small_b wf_b have "\<zero> \<succ> b" by auto
      from this wf_b have "b = \<zero>" using zero_leastII mode by auto
      with rec Pair wf_b wf_vbs wf_y wf_ass show ?thesis by auto 
    next
      case (Some avas)
      show ?thesis 
      proof (cases avas)
        case (Pair a vas')
        with Some oPair Cons  have lookup: "lookup_rest y vas = Some (a,vas')" and check: "isOK(check_pvars ?R wgt vas' vbs)" and ab: "wgt a b" by auto
        from Cons(4)[unfolded wf_pvars_def] lookup_rest_set[OF lookup] have wf_a: "a \<in> carrier R" by auto
        from lookup_rest_set[OF lookup] coeffs[unfolded coeff] ab wf_a wf_b have ab: "a \<succ> b" by auto
        from lookup_rest_set[OF lookup] have "set (coeffs_of_pvars ?R vas') \<subseteq> set (coeffs_of_pvars ?R vas)" 
          unfolding coeff by auto 
        with coeffs have "\<And> a b. (a, b) \<in> set (coeffs_of_pvars ?R vas') \<times> set (coeffs_of_pvars ?R vbs) \<Longrightarrow> a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> wgt a b \<Longrightarrow> a \<succ> b" by auto
        note IH = Cons(1)[OF check this]
        have lookupRes: "eval_pvars \<alpha> vas = a \<otimes> \<alpha> y \<oplus> eval_pvars \<alpha> vas' \<and> wf_pvars R vas' \<and> a \<in> carrier R"
          by (rule lookup_rest_sound[OF lookup wf_ass \<open>wf_pvars R vas\<close>])        
        with IH check wf_vbs have gt: "eval_pvars \<alpha> vas' \<succ> eval_pvars \<alpha> vbs" (is "?l \<succ> ?r") by auto
        show ?thesis 
        proof (cases "\<alpha> y = \<zero>")
          case False
          have "a \<otimes> \<alpha> y \<oplus> ?l \<succ> b \<otimes> \<alpha> y \<oplus> ?r"
            by (rule plus_gt_both_mono, rule times_gt_left_mono[OF ab], auto simp: lookupRes wf_b wf_y wf_ass wf_vbs mode gt)
          with lookupRes Some Pair oPair Cons show ?thesis by auto
        next
          case True
          then have "a \<otimes> \<alpha> y \<oplus> ?l = ?l" and "b \<otimes> \<alpha> y \<oplus> ?r = ?r" by (auto simp: wf_y lookupRes wf_ass wf_b wf_vbs)
          with gt lookupRes True Some Pair oPair Cons show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma check_lpoly_ns_sound:
  assumes check: "isOK (check_lpoly_ns (R \<lparr> gt := gt, bound := bnd \<rparr>) p q)"
    and wf_p: "wf_lpoly R p"
    and wf_q: "wf_lpoly R q"
  shows "(p, q) \<in> poly_ns"
proof (cases p)
  case (LPoly a vas) note oLPoly = this
  let ?R = "R \<lparr> gt := gt, bound := bnd \<rparr>"
  show ?thesis
  proof (cases q)
    case (LPoly b vbs)
    with oLPoly assms have ab: "a \<succeq> b" and pvars: "isOK(check_pvars ?R (\<succeq>) vas vbs)" and
      wf_a: "a \<in> carrier R" and wf_b: "b \<in> carrier R" and wf_vas: "wf_pvars R vas" and wf_vbs: "wf_pvars R vbs" 
      by auto
    {
      fix \<alpha>
      have "wf_ass R \<alpha> \<and> pos_ass \<alpha> \<longrightarrow> (a \<oplus> (eval_pvars \<alpha> vas)) \<succeq> (b \<oplus> (eval_pvars \<alpha> vbs))" (is "?ass \<longrightarrow> ?goal")
      proof 
        assume ass: ?ass
        show ?goal
          by (rule plus_left_right_mono[OF _ check_pvars_sound[OF pvars]],
          insert wf_a wf_b ass wf_vas wf_vbs ab, auto)
      qed
    }
    then have "(LPoly a vas, LPoly b vbs) \<in> poly_ns" unfolding poly_ns_def
      by auto
    with LPoly oLPoly show ?thesis by auto
  qed
qed

lemma plus_gt_left_mono2:
  assumes xy: "(x :: 'a) \<succ> y" and zu: "(z :: 'a) \<succeq> u" 
    and carr: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" "u \<in> carrier R" 
    and psm: psm
  shows "(x :: 'a) \<oplus> z \<succ> y \<oplus> u"
proof -
  have "x \<oplus> z \<succ> y \<oplus> z" by (rule plus_gt_left_mono[OF xy psm], insert carr, auto)
  also have "\<dots> = z \<oplus> y" using carr by algebra
  finally have one: "x \<oplus> z \<succ> z \<oplus> y" .
  have "z \<oplus> y \<succeq> u \<oplus> y" by (rule plus_left_mono[OF zu], insert carr, auto)
  also have "\<dots> = y \<oplus> u" using carr by algebra
  finally have two: "z \<oplus> y \<succeq> y \<oplus> u" .
  show ?thesis
    by (rule compat2[OF one two], insert carr, auto)
qed

lemma check_lpoly_s_sound:
  assumes check: "isOK (check_lpoly_s (R \<lparr> gt := wgt, bound := bnd \<rparr>) p q)"
    and wf_p: "wf_lpoly R p"
    and wf_q: "wf_lpoly R q"
    and weak_gt: "\<And> a b. (a,b) \<in> set (coeffs_of_lpoly (R \<lparr> gt := wgt, bound := bnd \<rparr>) p) \<times> set (coeffs_of_lpoly (R \<lparr> gt := wgt, bound := bnd \<rparr>) q) 
    \<Longrightarrow> a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> wgt a b \<Longrightarrow> a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> a \<succ> b"
  shows "(p,q) \<in> poly_s"
proof (cases p)
  case (LPoly a vas) note oLPoly = this
  let ?R = "R \<lparr> gt := wgt, bound := bnd \<rparr>"
  let ?wgt = "if psm then (\<succeq>) else wgt"
  show ?thesis
  proof (cases q)
    case (LPoly b vbs)
    with oLPoly wf_p wf_q check weak_gt[of a b] have ab: "a \<succ> b" and ppvars: "isOK(check_pvars ?R ?wgt vas vbs)" and
      wf_a: "a \<in> carrier R" and wf_b: "b \<in> carrier R" and wf_vas: "wf_pvars R vas" and wf_vbs: "wf_pvars R vbs" by auto    
    {
      fix \<alpha>
      have "wf_ass R \<alpha> \<and> pos_ass \<alpha> \<longrightarrow> (a \<oplus> (eval_pvars \<alpha> vas)) \<succ> (b \<oplus> (eval_pvars \<alpha> vbs))" (is "?ass \<longrightarrow> ?goal")
      proof 
        assume ass: ?ass
        show ?goal 
        proof (cases psm)
          case True
          with ppvars have pvars: "isOK(check_pvars ?R (\<succeq>) vas vbs)" by auto
          show ?goal 
            by (rule plus_gt_left_mono2[OF _ check_pvars_sound[OF pvars]], insert 
              ass pvars wf_vas wf_vbs True wf_a wf_b ab, auto)
        next 
          case False
          with ppvars have pvars: "isOK(check_pvars ?R wgt vas vbs)" by auto
          have gt: "eval_pvars \<alpha> vas \<succ> eval_pvars \<alpha> vbs" 
            by (rule check_pvars_gt_sound[OF pvars weak_gt], insert False LPoly oLPoly ass wf_vas wf_vbs, auto)
          show ?thesis 
            by (rule plus_gt_both_mono[OF ab gt], auto simp: wf_a wf_b ass wf_vas wf_vbs False)
        qed
      qed
    }
    then have "(LPoly a vas, LPoly b vbs) \<in> poly_s" unfolding poly_s_def by auto
    with LPoly oLPoly show ?thesis by auto
  qed
qed

declare check_lpoly_ns.simps[simp del]
declare check_lpoly_s.simps[simp del]

end

context lpoly_order
begin

lemmas poly_order_simps =  one_geq_zero default_geq_zero arc_pos_plus arc_pos_mult arc_pos_max0 arc_pos_default

declare poly_simps [simp del]

end

end
