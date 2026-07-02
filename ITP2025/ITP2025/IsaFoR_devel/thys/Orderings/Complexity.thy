(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Complexity\<close>

theory Complexity
imports
  First_Order_Terms.Term_More
  Show.Show_Instances
  Jordan_Normal_Form.Derivation_Bound
  Show.Shows_Literal
  "Abstract-Rewriting.Relative_Rewriting" 
begin

subsection \<open>Derivation Height and Complexity Functions\<close>

locale traditional_complexity =
  fixes r :: "('a::size) rel"
begin

abbreviation "DH x \<equiv> {n. \<exists>y. (x, y) \<in> r ^^ n}"

end

locale fb_sn =
  fixes r :: "('a::size) rel"
  assumes fb: "\<And>x. finite {y. (x, y) \<in> r}" and sn: "SN r"
begin

interpretation traditional_complexity r .

lemma finite_DH:
  "finite (DH x)"
using sn
proof (induct)
  case (IH x)
  let ?Y = "\<Union>y \<in> {y. (x, y) \<in> r}. Suc ` DH y"
  have "DH x = {0} \<union> ?Y"
    by (auto simp: relpow_commute elim: relpow_E2 intro!: rev_image_eqI)
       (metis relcomp.relcompI relpow_commute)
  moreover have "finite ?Y"
    using fb and IH by simp
  ultimately show ?case by simp
qed

end

context traditional_complexity
begin

definition "dh x = Max (DH x)"

abbreviation "CP n T \<equiv> {dh x | x. x \<in> T \<and> size x \<le> n}"

definition "cp n T = Max (CP n T)"

abbreviation "of_size A n \<equiv> {x \<in> A. size x \<le> n}"

end

datatype complexity_class = Comp_Poly nat

fun complexity_of :: "complexity_class \<Rightarrow> (nat \<Rightarrow> nat) set"
where
  "complexity_of (Comp_Poly d) = { \<lambda> n. c * n ^ d + e | c e. True}"

lemma complexity_poly_mono_deg:
  assumes "d \<le> d'" 
    and "f \<in> complexity_of (Comp_Poly d)"
  shows "\<exists> g \<in> complexity_of (Comp_Poly d'). \<forall> n. f n \<le> g n"
proof -
  from assms obtain c e where f: "f = (\<lambda> n. c * n ^ d + e)" by auto
  let ?g = "\<lambda> n. c * n ^ d' + e"
  define g where "g \<equiv> \<lambda>n. ?g n + c"
  {
    fix n
    have "f n \<le> ?g n + c"
    proof (cases n)
      case 0
      then show ?thesis by (cases d) (simp_all add: f)
    next
      case (Suc m)
      have "f n \<le> ?g n" 
        using power_increasing [OF \<open>d \<le> d'\<close>, of n] by (auto simp: f Suc)
      then show ?thesis by auto
    next
     
    qed
  }
  then have "\<forall> n. f n \<le> g n" by (simp add: g_def)
  moreover have "g \<in> complexity_of (Comp_Poly d')"
    by (auto simp: g_def) (rule exI [of _ c], rule exI [of _ "e + c"], auto)
  ultimately show ?thesis by auto
qed

lemma complexity_poly_mono: 
  assumes "f \<in> complexity_of (Comp_Poly d)"
    and "n \<le> m"
  shows "f n \<le> f m"
  using power_mono [OF \<open>n \<le> m\<close>, of d] and assms by auto

definition O_of :: "complexity_class \<Rightarrow> (nat \<Rightarrow> nat) set"
where
  "O_of cl = {f. \<exists> g \<in> complexity_of cl. \<forall> n. f n \<le> g n}"

lemma O_of_polyI [intro]: 
  assumes ge: "\<And> n. f n \<le> c * n ^ d + e"
  shows "f \<in> O_of (Comp_Poly d)"
  using assms by (auto simp: O_of_def)

lemma O_of_poly_mono_deg:
  assumes "d \<le> d'" 
  shows "O_of (Comp_Poly d) \<subseteq> O_of (Comp_Poly d')"
proof 
  fix f
  assume "f \<in> O_of (Comp_Poly d)"
  then obtain g where "g \<in> complexity_of (Comp_Poly d)" and "\<And> n. f n \<le> g n" 
    by (auto simp: O_of_def)
  moreover with complexity_poly_mono_deg [OF \<open>d \<le> d'\<close>]
    obtain h where "h \<in> complexity_of (Comp_Poly d')" and "\<And> n. g n \<le> h n" by blast
  ultimately show "f \<in> O_of (Comp_Poly d')" unfolding O_of_def using le_trans by blast
qed

lemma O_of_poly_mono_deg_inv:
  assumes subset: "O_of (Comp_Poly d1) \<subseteq> O_of (Comp_Poly d2)" 
  shows "d1 \<le> d2"
proof (rule ccontr)
  assume "\<not> d1 \<le> d2"
  then have d: "d1 > d2" by simp
  let ?f = "\<lambda> n :: nat. n ^ d1"
  have "?f \<in> O_of (Comp_Poly d1)" 
    by (rule O_of_polyI [of _ 1 _ 0]) simp
  with subset have "?f \<in> O_of (Comp_Poly d2)" by auto
  then obtain g where g: "g \<in> complexity_of (Comp_Poly d2)" 
    and comp: "\<And> n. ?f n \<le> g n" by (auto simp: O_of_def)
  from g obtain c e where g: "g = (\<lambda>n. c * n ^ d2 + e)" by auto
  from d obtain d where d1: "d1 = Suc d" and d: "d \<ge> d2" by (cases d1) auto
  define n where "n = c + e + 1"
  have "n \<ge> 1" by (auto simp: n_def)
  then have nd1: "n ^ d2 \<ge> 1" by simp
  have "g n = c * n ^ d2 + e" by (simp add: g)
  also have "\<dots> < c * n ^ d2 + e + 1" by simp
  also have "e \<le> e * n ^ d2" using nd1 by simp
  also have "1 \<le> 1 * n ^ d2" using nd1 by simp
  finally have "g n < c * n ^ d2 + e * n ^ d2 + 1 * n ^ d2" by arith
  also have "\<dots> = n * n ^ d2" by (simp add: n_def field_simps)
  also have "\<dots> \<le> n * n^d" using power_increasing [OF d \<open>n \<ge> 1\<close>] by simp
  also have "\<dots> = ?f n" by (simp add: d1)
  also have "\<dots> \<le> g n" using comp [of n] .
  finally show False by auto
qed

lemma O_of_sum:
  assumes f1: "f1 \<in> O_of cc"
    and f2: "f2 \<in> O_of cc"
  shows "(\<lambda> n. f1 n + f2 n) \<in> O_of cc"
proof (cases cc)
  case (Comp_Poly d)
  from f1 obtain c1 e1 where b1: "\<And> n. f1 n \<le> c1 * n ^ d + e1" by (auto simp: Comp_Poly O_of_def)
  from f2 obtain c2 e2 where b2: "\<And> n. f2 n \<le> c2 * n ^ d + e2" by (auto simp: Comp_Poly O_of_def)
  show ?thesis
  proof (unfold Comp_Poly, rule O_of_polyI)
    fix n
    have "f1 n + f2 n \<le> c1 * n ^ d + e1 + c2 * n ^ d + e2"
      using b1 [of n] and b2 [of n] by auto
    also have "\<dots> = (c1 + c2) * n ^ d + (e1 + e2)" by (simp add: field_simps)
    finally show "f1 n + f2 n \<le> (c1 + c2) * n ^ d + (e1 + e2)" .
  qed
qed

fun degree :: "complexity_class \<Rightarrow> nat"
where
  "degree (Comp_Poly d) = d"

instantiation complexity_class :: ord
begin
fun less_eq_complexity_class where "less_eq_complexity_class (x :: complexity_class) (y :: complexity_class) = (degree x \<le> degree y)"
fun less_complexity_class where "less_complexity_class (x :: complexity_class) (y :: complexity_class) = (degree x < degree y)"
instance ..
end

instantiation complexity_class :: showl
begin
definition "showsl_complexity_class (c::complexity_class) =
  (if degree c = 0 then showsl_lit (STR ''O(1)'')
  else if degree c = 1 then showsl_lit (STR ''O(n)'')
  else showsl_lit (STR ''O(n^'') \<circ> showsl (degree c) \<circ> showsl_lit (STR '')''))"
definition "showsl_list (xs :: complexity_class list) = default_showsl_list showsl xs"
instance ..
end

lemma degree_subset [simp]:
  "(cc \<le> cc') = (O_of cc \<subseteq> O_of cc')"
proof -
  obtain d where cc: "cc = Comp_Poly d" by (cases cc) auto
  obtain d' where cc': "cc' = Comp_Poly d'" by (cases cc') auto
  show ?thesis
    using O_of_poly_mono_deg O_of_poly_mono_deg_inv by (auto simp: cc cc')
qed

declare less_eq_complexity_class.simps [simp del]

definition deriv_bound_rel :: "'a rel \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
where
  "deriv_bound_rel r as f \<longleftrightarrow> (\<forall> n a. a \<in> as n \<longrightarrow> deriv_bound r a (f n))"

context fb_sn
begin

interpretation traditional_complexity r .

text \<open>@{const cp} is a derivation bound, whenever it is defined.\<close>
lemma deriv_bound_rel_cp:
  assumes fin: "\<And>n. finite (CP n T)"
  shows "deriv_bound_rel r (of_size T) (\<lambda>n. cp n T)"
proof (unfold deriv_bound_rel_def, intro allI impI)
  fix x and n
  assume x: "x \<in> of_size T n"
  show "deriv_bound r x (cp n T)"
  proof
    fix y and m
    assume "cp n T < m" and "(x, y) \<in> r ^^ m"
    then have "dh x \<ge> m"
      using finite_DH [of x] by (auto simp: dh_def) (metis Max_ge mem_Collect_eq)
    then have "cp n T \<ge> m"
      using x and fin [of n]
      by (auto simp: cp_def) (metis (mono_tags, lifting) Max_ge mem_Collect_eq order_trans)
    with \<open>cp n T < m\<close> show False by arith
  qed
qed

text \<open>@{const cp} is a lower bound for any derivation bound, whenever it is defined.\<close>
lemma cp_lower:
  assumes "\<And>x. DH x \<noteq> {}"
    and "\<And>n. finite (CP n T)"
    and "\<And>n. CP n T \<noteq> {}"
    and db: "deriv_bound_rel r (of_size T) f"
  shows "f n \<ge> cp n T"
proof (rule ccontr)
  assume "\<not> cp n T \<le> f n"
  then have "cp n T > f n" by arith
  have *: "\<And>x. x \<in> of_size T n \<Longrightarrow> deriv_bound r x (f n)"
    using db by (auto simp: deriv_bound_rel_def)
  define m where "m = cp n T"
  have **: "\<And>k. k \<in> CP n T \<Longrightarrow> k \<le> m"
    using \<open>finite (CP n T)\<close> by (auto simp: m_def cp_def)
  have "m \<in> CP n T"
    using Max_in [OF \<open>finite (CP n T)\<close> \<open>CP n T \<noteq> {}\<close>] by (simp add: m_def cp_def)
  then obtain x where "x \<in> of_size T n" and "dh x = m" by blast
  then have "dh x > f n" by (simp add: m_def) (rule \<open>cp n T > f n\<close>)
  moreover then obtain y where "(x, y) \<in> r ^^ dh x"
    using Max_in [OF finite_DH \<open>DH x \<noteq> {}\<close>] by (auto simp: dh_def)
  ultimately show False using * [OF \<open>x \<in> of_size T n\<close>] by (auto elim: deriv_boundE)
qed

end

lemma deriv_bound_rel_empty [simp]:
  "deriv_bound_rel {} as f"
  by (simp add: deriv_bound_rel_def)

definition deriv_bound_rel_class :: "'a rel \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> complexity_class \<Rightarrow> bool"
where
  "deriv_bound_rel_class r as cpx \<longleftrightarrow> (\<exists> f. f \<in> O_of cpx \<and> deriv_bound_rel r as f)"

lemma deriv_bound_rel_class_polyI [intro]: 
  assumes "\<And> n a. a \<in> as n \<Longrightarrow> deriv_bound r a (c * n ^ d + e)"
  shows "deriv_bound_rel_class r as (Comp_Poly d)"
  using assms unfolding deriv_bound_rel_class_def
  by (intro exI [of _ "\<lambda> n. c * n ^ d + e"] conjI [OF O_of_polyI [OF le_refl]])
     (auto simp: deriv_bound_rel_def)

lemma deriv_bound_rel_class_empty [simp]:
  "deriv_bound_rel_class {} as cpx"
proof (cases cpx)
  case (Comp_Poly d)
  show ?thesis
    unfolding deriv_bound_rel_class_def Comp_Poly
    by (rule exI, rule conjI, rule O_of_polyI [OF le_refl], simp)
qed

lemma deriv_bound_relto_class_union:
  assumes s1: "deriv_bound_rel_class (relto s1 (w \<union> s2)) as cc"
    and s2: "deriv_bound_rel_class (relto s2 (w \<union> s1)) as cc"
  shows "deriv_bound_rel_class (relto (s1 \<union> s2)  w) as cc"
proof -
  let ?r1 = "relto s1 (w \<union> s2)"
  let ?r2 = "relto s2 (w \<union> s1)"
  let ?r  = "relto (s1 \<union> s2) w"
  from s1[unfolded deriv_bound_rel_class_def]
  obtain f1 where f1: "f1 \<in> O_of cc" and b1: "deriv_bound_rel ?r1 as f1" by auto
  from s2[unfolded deriv_bound_rel_class_def]
  obtain f2 where f2: "f2 \<in> O_of cc" and b2: "deriv_bound_rel ?r2 as f2" by auto
  obtain f where f: "f = (\<lambda> n. f1 n + f2 n)" by auto
  have fcc: "f \<in> O_of cc" using O_of_sum[OF f1 f2] unfolding f .
  show ?thesis unfolding deriv_bound_rel_class_def
  proof(intro exI conjI, rule fcc)
    show "deriv_bound_rel ?r as f"
      unfolding deriv_bound_rel_def
    proof (intro allI impI)
      fix n a
      assume a: "a \<in> as n"
      from b1[unfolded deriv_bound_rel_def] a
      have b1: "deriv_bound ?r1 a (f1 n)" by simp
      from b2[unfolded deriv_bound_rel_def] a
      have b2: "deriv_bound ?r2 a (f2 n)" by simp
      show "deriv_bound ?r a (f n)" 
        unfolding deriv_bound_def
      proof
        assume "\<exists> b. (a,b) \<in> ?r ^^ Suc (f n)"
        then obtain b where ab: "(a,b) \<in> ?r ^^ Suc (f n)" by blast
        from ab[unfolded relpow_fun_conv] obtain as where
          as0: "as 0 = a"
          and steps: "\<And> i. i < Suc (f n) \<Longrightarrow> (as  i, as (Suc i)) \<in> ?r" by auto
        {
          fix i
          assume "i < Suc (f n)"
          from steps[OF this]
          obtain b c where asb: "(as i, b) \<in> w^*"  and bc: "(b,c) \<in> s1 \<union> s2" and cas: "(c,as (Suc i)) \<in> w^*" by auto
          let ?p = "(as i, as (Suc i))"
          {
            fix s
            have "(as i, b) \<in> (w \<union> s)^*"
              by (rule set_mp[OF _ asb], regexp)
          } note asb = this
          {
            fix s
            have "(c, as (Suc i)) \<in> (w \<union> s)^*"
              by (rule set_mp[OF _ cas], regexp)
          } note cas = this
          from bc
          have "?p \<in> ?r1 \<and> ?p \<in> (w \<union> s1)^* \<or> ?p \<in> ?r2 \<and> ?p \<in> (w \<union> s2)^*"
          proof
            assume bc: "(b,c) \<in> s1"
            have s: "?p \<in> ?r1" using asb[of s2] bc cas[of s2] by auto
            have ns: "?p \<in> (w \<union> s1)^* O (w \<union> s1) O (w \<union> s1)^* " using asb[of s1] bc cas[of s1] by auto
            have "?p \<in> (w \<union> s1)^*" by (rule set_mp[OF _ ns], regexp)
            with s show ?thesis by blast
          next
            assume bc: "(b,c) \<in> s2"
            have s: "?p \<in> ?r2" using asb[of s1] bc cas[of s1] by auto
            have ns: "?p \<in> (w \<union> s2)^* O (w \<union> s2) O (w \<union> s2)^* " using asb[of s2] bc cas[of s2] by auto
            have "?p \<in> (w \<union> s2)^*" by (rule set_mp[OF _ ns], regexp)
            with s show ?thesis by blast
          qed
        } note steps = this
        {
          fix i
          assume i: "i \<le> Suc (f n)"
          let ?p = "\<lambda> i i1 i2 b1 b2. (a,b1) \<in> ?r1 ^^ i1 \<and> (b1,as i) \<in> (w \<union> s2)^* \<and> (a,b2) \<in> ?r2 ^^ i2 \<and> (b2,as i) \<in> (w \<union> s1)^* \<and> i1 + i2 = i"
          from i have "\<exists> i1 i2 b1 b2. ?p i i1 i2 b1 b2"
          proof (induct i)
            case 0
            show ?case
            proof (intro exI)
              show "?p 0 0 0 a a" unfolding as0 by simp
            qed
          next
            case (Suc i)
            from Suc(2) have "i \<le> Suc (f n)" by simp
            from Suc(1)[OF this] obtain i1 i2 b1 b2 where p: "?p i i1 i2 b1 b2" by blast
            then have ab1: "(a,b1) \<in> ?r1 ^^ i1"
              and b1ai: "(b1,as i) \<in> (w \<union> s2)^*"
              and ab2: "(a,b2) \<in> ?r2 ^^ i2"
              and b2ai: "(b2,as i) \<in> (w \<union> s1)^*" 
              and i: "i = i1 + i2" by auto
            let ?a = "(as i, as (Suc i))"
            from Suc(2) have "i < Suc (f n)" by simp
            from steps[OF this] show ?case
            proof
              assume "?a \<in> ?r1 \<and> ?a \<in> (w \<union> s1)^*"
              then have s: "?a \<in> ?r1" and ns: "?a \<in> (w \<union> s1)^*" by auto
              from b1ai s have s: "(b1, as (Suc i)) \<in> (w \<union> s2)^* O ?r1" by blast
              have "(b1, as (Suc i)) \<in> ?r1" 
                by (rule set_mp[OF _ s], regexp)
              from relpow_Suc_I[OF ab1 this]
              have s: "(a, as (Suc i)) \<in> ?r1 ^^ Suc i1" .
              from b2ai ns have ns: "(b2, as (Suc i)) \<in> (w \<union> s1)^*" by auto
              have "?p (Suc i) (Suc i1) i2 (as (Suc i)) b2" using s ns i ab2 by auto
              then show ?thesis by blast
            next
              assume one: "?a \<in> ?r2 \<and> ?a \<in> (w \<union> s2)^*"
              then have s: "?a \<in> ?r2" and ns: "?a \<in> (w \<union> s2)^*" by auto
              from b2ai s have s: "(b2, as (Suc i)) \<in> (w \<union> s1)^* O ?r2" by blast
              have "(b2, as (Suc i)) \<in> ?r2" 
                by (rule set_mp[OF _ s], regexp)
              from relpow_Suc_I[OF ab2 this]
              have s: "(a, as (Suc i)) \<in> ?r2 ^^ Suc i2" .
              from b1ai ns have ns: "(b1, as (Suc i)) \<in> (w \<union> s2)^*" by auto
              have "?p (Suc i) i1 (Suc i2) b1 (as (Suc i))" using s ns i ab1 by auto
              then show ?thesis by blast
            qed
          qed
          then have "\<exists> i1 i2 b1 b2. (a,b1) \<in> ?r1 ^^ i1 \<and> (a,b2) \<in> ?r2 ^^ i2 \<and> i1 + i2 = i" by blast
        }
        from this[OF le_refl]
        obtain i1 i2 b1 b2 where steps1: "(a,b1) \<in> ?r1 ^^ i1" and steps2: "(a,b2) \<in> ?r2 ^^ i2" and i: "i1 + i2 = Suc (f n)" by blast
        from deriv_bound_steps[OF steps1 b1] deriv_bound_steps[OF steps2 b2] have "i1 + i2 \<le> f1 n + f2 n" by simp
        with i[unfolded f] show False by simp
      qed
    qed
  qed
qed            

datatype ('f, 'v) complexity_measure = 
  Derivational_Complexity "('f \<times> nat) list" | (* signature *)
  Runtime_Complexity "('f \<times> nat) list" "('f \<times> nat) list" (* constructors, defined *) 

fun term_size :: "('f,'v)term \<Rightarrow> nat" where
  "term_size (Var x) = Suc 0"
| "term_size (Fun f ts) = Suc (sum_list (map term_size ts))"

lemma term_size_map_funs_term [simp]:
  "term_size (map_funs_term fg t) = term_size t"
proof (induct t)
  case (Fun f ts)
  then show ?case by (induct ts) auto
qed simp

lemma term_size_subst: "term_size t \<le> term_size (t \<cdot> \<sigma>)"
proof (induct t)
  case (Var x)
  then show ?case by (cases "\<sigma> x") auto
next
  case (Fun f ss)
  then show ?case 
    by (induct ss, force+)
qed

lemma term_size_const_subst[simp]: "term_size (t \<cdot> (\<lambda> _ . Fun f [])) = term_size t"
proof (induct t)
  case (Fun f ts)
  then show ?case by (induct ts, auto)
qed simp

lemma supt_term_size:
  "s \<rhd> t \<Longrightarrow> term_size s > term_size t"
proof (induct rule: supt.induct)
  case (arg s ss)
  then show ?case by (induct ss, auto)
next
  case (subt s ss t f)
  then show ?case by (induct ss, auto)
qed



fun terms_of_nat :: "('f, 'v) complexity_measure \<Rightarrow> nat \<Rightarrow> ('f, 'v) terms"
where
  "terms_of_nat (Derivational_Complexity F) n = {t. funas_term t \<subseteq> set F \<and> term_size t \<le> n}" |
  "terms_of_nat (Runtime_Complexity C D) n =
    {t. is_Fun t \<and> the (root t) \<in> set D \<and> funas_args_term t \<subseteq> set C \<and> term_size t \<le> n}"

fun terms_of :: "('f, 'v) complexity_measure \<Rightarrow> ('f, 'v) terms"
where
  "terms_of (Derivational_Complexity F) = {t. funas_term t \<subseteq> set F}" |
  "terms_of (Runtime_Complexity C D) =
    {t. is_Fun t \<and> the (root t) \<in> set D \<and> funas_args_term t \<subseteq> set C}"

lemma terms_of:
  "terms_of cm = \<Union>(range (terms_of_nat cm))"
  by (cases cm) auto

definition
  deriv_bound_measure_class ::
    "('f, 'v) term rel \<Rightarrow> ('f, 'v) complexity_measure \<Rightarrow> complexity_class \<Rightarrow> bool"
where
  "deriv_bound_measure_class r cm cpx = deriv_bound_rel_class r (terms_of_nat cm) cpx"

lemma deriv_bound_measure_class_empty [simp]:
  "deriv_bound_measure_class {} cm cc"
  unfolding deriv_bound_measure_class_def by simp

lemma deriv_bound_measure_class_SN_on:
  assumes bound: "deriv_bound_measure_class r cm p"
  shows "SN_on r (terms_of cm)"
proof -
  {
    fix t
    assume "t \<in> terms_of cm"
    then obtain n where t: "t \<in> terms_of_nat cm n" unfolding terms_of by auto
    with bound[unfolded deriv_bound_measure_class_def deriv_bound_rel_class_def 
      deriv_bound_rel_def] obtain n where "deriv_bound r t n" by blast
    then have "SN_on r {t}"
      by (rule deriv_bound_SN_on)
  }
  then show ?thesis unfolding SN_on_def by blast
qed

lemma deriv_bound_relto_measure_class_union:
  assumes s1: "deriv_bound_measure_class (relto s1 (w \<union> s2)) as cc"
    and s2: "deriv_bound_measure_class (relto s2 (w \<union> s1)) as cc"
  shows "deriv_bound_measure_class (relto (s1 \<union> s2) w) as cc"
  using s1 s2
  unfolding deriv_bound_measure_class_def
  by (rule deriv_bound_relto_class_union)

lemma deriv_bound_rel_mono:
  assumes r: "r \<subseteq> r'\<^sup>+" and as: "\<And> n. as n \<subseteq> as' n"
    and f: "\<And> n. f' n \<le> f n"
    and d: "deriv_bound_rel r' as' f'"
  shows "deriv_bound_rel r as f" unfolding deriv_bound_rel_def
proof (intro allI impI)
  fix n a 
  assume "a \<in> as n"
  with as have "a \<in> as' n" by auto
  from d [unfolded deriv_bound_rel_def, rule_format, OF this]
    have "deriv_bound r' a (f' n)" .
  from deriv_bound_mono [OF f this]
    have "deriv_bound r' a (f n)" .
  from deriv_bound_subset[OF r this]
    show "deriv_bound r a (f n)" .
qed

lemma deriv_bound_rel_class_mono:
  assumes r: "r \<subseteq> r'\<^sup>+" and as: "\<And> n. as n \<subseteq> as' n"
    and cc: "O_of cc' \<subseteq> O_of cc"
    and d: "deriv_bound_rel_class r' as' cc'"
  shows "deriv_bound_rel_class r as cc" unfolding deriv_bound_rel_class_def
proof -
  from d obtain f where f: "f \<in> O_of cc'"
    and d: "deriv_bound_rel r' as' f" by (auto simp: deriv_bound_rel_class_def)
  from f and cc have "f \<in> O_of cc" by auto
  with deriv_bound_rel_mono [OF r as le_refl d]
    show "\<exists> f. f \<in> O_of cc \<and> deriv_bound_rel r as f" by auto
qed

lemma deriv_bound_measure_class_trancl_mono:
  assumes r: "r \<subseteq> r'\<^sup>+" and cm: "\<And> n. terms_of_nat cm n \<subseteq> terms_of_nat cm' n"
    and cc: "O_of cc' \<subseteq> O_of cc"
    and d: "deriv_bound_measure_class r' cm' cc'"
  shows "deriv_bound_measure_class r cm cc" unfolding deriv_bound_measure_class_def
  by (rule deriv_bound_rel_class_mono [OF r cm cc], rule d [unfolded deriv_bound_measure_class_def])

lemma deriv_bound_measure_class_mono:
  assumes r: "r \<subseteq> r'" and cm: "\<And> n. terms_of_nat cm n \<subseteq> terms_of_nat cm' n"
    and cc: "O_of cc' \<subseteq> O_of cc"
    and d: "deriv_bound_measure_class r' cm' cc'"
  shows "deriv_bound_measure_class r cm cc" 
  by (rule deriv_bound_measure_class_trancl_mono [OF _ cm cc d], insert r, auto)

lemma runtime_subset_derivational:
  assumes F: "set C \<union> set D \<subseteq> set F" 
  shows "terms_of_nat (Runtime_Complexity C D) n \<subseteq> terms_of_nat (Derivational_Complexity F) n"
proof 
  fix t
  assume t: "t \<in> terms_of_nat (Runtime_Complexity C D) n"
  from t have n: "term_size t \<le> n" by simp
  from t obtain f ts where f: "t = Fun f ts" by (cases t, auto)
  from t f have D: "(f, length ts) \<in> set D" and C: "\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> set C"
    by (auto simp: funas_args_term_def)
  from D C F have "funas_term t \<subseteq> set F" unfolding f by auto
  with t show "t \<in> terms_of_nat (Derivational_Complexity F) n" by simp
qed  

fun get_signature_of_cm
where
  "get_signature_of_cm (Derivational_Complexity F) = F" |
  "get_signature_of_cm (Runtime_Complexity C D) = C @ D"

lemma get_signature_of_cm:
  "terms_of_nat cm n \<subseteq> terms_of_nat (Derivational_Complexity (get_signature_of_cm cm)) n"
  using runtime_subset_derivational [of _ _ _ n]
  by (cases cm) (force simp: funas_args_term_def)+

end

