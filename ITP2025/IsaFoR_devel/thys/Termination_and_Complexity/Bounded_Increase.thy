(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Bounded_Increase
imports
  Generalized_Usable_Rules 
begin

text \<open>in this theory, we introduce the induction calculus from
  the CADE07 "Bounded Increase" paper, and prove its soundness.
  We generalize the result, since we only demand minimality or unique normal forms.\<close>

text \<open>free variables of a constraint, as set and as list\<close>
fun vars_cc :: "('f, 'v) cond_constraint \<Rightarrow> 'v set" where
  "vars_cc (CC_cond ct (s, t)) = vars_term s \<union> vars_term t"
| "vars_cc (CC_rewr s t) = vars_term s \<union> vars_term t"
| "vars_cc (CC_impl cs c) = \<Union>(vars_cc ` set cs) \<union> vars_cc c"
| "vars_cc (CC_all x c) = vars_cc c - {x}"

fun vars_cc_list :: "('f, 'v) cond_constraint \<Rightarrow> 'v list" where
  "vars_cc_list (CC_cond ct (s, t)) = vars_term_list s @ vars_term_list t"
| "vars_cc_list (CC_rewr s t) = vars_term_list s @ vars_term_list t"
| "vars_cc_list (CC_impl c1 c2) = concat (map vars_cc_list c1) @ vars_cc_list c2"
| "vars_cc_list (CC_all x c) = [ y . y <- vars_cc_list c, y \<noteq> x]"

lemma vars_cc_list [simp]:
  "set (vars_cc_list c) = vars_cc c"
  by (induct c) auto

text \<open>constructor for adding multiple quantors\<close>
fun cc_bound :: "'v list \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint" where
  "cc_bound [] c = c"
| "cc_bound (x # xs) c = CC_all x (cc_bound xs c)"

locale fresh =
  fixes fresh :: "'v list \<Rightarrow> 'v"
begin

text \<open>apply a substitution 
  (where the list besides the substitution contains information on which variables have to be avoided)\<close>
fun cc_subst_apply :: "('f,'v)cond_constraint \<Rightarrow> (('f,'v)subst \<times> 'v list) \<Rightarrow> ('f,'v)cond_constraint" (infix "\<cdot>\<^sub>cc" 70) where 
  "CC_cond ct (s,t) \<cdot>\<^sub>cc (\<sigma>,_) = CC_cond ct (s \<cdot> \<sigma>,t \<cdot> \<sigma>)"
| "CC_rewr s t \<cdot>\<^sub>cc (\<sigma>,_) = CC_rewr (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
| "CC_impl c1 c2 \<cdot>\<^sub>cc \<sigma> = CC_impl (map (\<lambda> c. c \<cdot>\<^sub>cc \<sigma>) c1) (c2 \<cdot>\<^sub>cc \<sigma>)"
| "CC_all x c \<cdot>\<^sub>cc (\<sigma>,vs) = (let y = fresh (vs @ vars_cc_list (CC_all x c)) in 
     CC_all y (c \<cdot>\<^sub>cc (\<sigma>(x := Var y), y # vs)))"

text \<open>uniquely rename all bound variables by applying empty substitution\<close>
definition normalize_alpha :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint" where
  "normalize_alpha c \<equiv> c \<cdot>\<^sub>cc (Var,[])"

text \<open>construct induction hypothesis for induction rule\<close>
definition cc_ih_prems :: "'f \<Rightarrow> ('f,'v)term \<Rightarrow> 'v list 
  \<Rightarrow> ('f,'v)cond_constraint list \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> (('f,'v)term \<times> 'v list) list \<Rightarrow> ('f,'v)cond_constraint list" where 
  "cc_ih_prems f q xs \<phi> \<psi> rs_ys_list \<equiv> 
      map (\<lambda> (r,ys). let 
            rs = args r;
            \<mu> = mk_subst Var (zip xs rs);
            vs' = range_vars_impl (zip xs rs);
            mu = \<lambda> c. c \<cdot>\<^sub>cc (\<mu>,vs');
            \<phi>' = CC_impl (CC_rewr r (q \<cdot> \<mu>) # map mu \<phi>) (mu \<psi>)
           in cc_bound ys \<phi>') rs_ys_list"

text \<open>construct constraint for each rule when applying induction rule, the user can choose a list
  of subterms (with corresponding free variables) for which IHs should be generated.\<close>
definition cc_rule_constraint :: "'f \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> 'v list 
  \<Rightarrow> ('f,'v)cond_constraint list \<Rightarrow> ('f,'v)cond_constraint \<Rightarrow> (('f,'v)term \<times> 'v list) list \<Rightarrow> ('f,'v)cond_constraint" where 
  "cc_rule_constraint f ls r q xs \<phi> \<psi> rs_ys_list \<equiv> 
     let 
       \<sigma> = mk_subst Var (zip xs ls);
       vs = range_vars_impl (zip xs ls);
       rew = CC_rewr r (q \<cdot> \<sigma>);
       phi_sig = map (\<lambda>c. c \<cdot>\<^sub>cc (\<sigma>,vs)) \<phi>;
       psi_sig = \<psi> \<cdot>\<^sub>cc (\<sigma>,vs);
       ihs = cc_ih_prems f q xs \<phi> \<psi> rs_ys_list
     in CC_impl (rew # phi_sig @ ihs) psi_sig"

end

declare fresh.cc_subst_apply.simps[code]
declare fresh.normalize_alpha_def[code]
declare fresh.cc_rule_constraint_def[code]
declare fresh.cc_ih_prems_def[code]

locale fixed_trs_dep_order_fresh = fixed_trs_dep_order \<pi> R Q F S NS nfs m const + fresh fresh
  for \<pi> :: "('f :: countable) dep"
  and R :: "('f,'v :: countable)trs"
  and Q :: "('f,'v)terms"
  and F :: "'f sig"
  and S :: "('f,'v)trs"
  and NS :: "('f,'v)trs"
  and nfs :: bool
  and m :: bool
  and fresh :: "'v list \<Rightarrow> 'v"
  and const :: 'f
  + fixes UR :: "('f,'v)term \<Rightarrow> ('f,'v)trs"
  assumes fresh: "fresh vs \<notin> set vs"
  and UR: "\<And> t u \<sigma>. \<sigma> ` vars_term t \<subseteq> NF_terms Q \<Longrightarrow> (t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)^* \<Longrightarrow> (t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q (UR t))^*"
  and UR_sub: "\<And> t. UR t \<subseteq> R"
begin

text \<open>only the free variables matter, when checking the model condition\<close>
lemma cc_models_vars:
  assumes "\<And> x. x \<in> vars_cc c \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "\<sigma> \<Turnstile> c = \<tau> \<Turnstile> c"
  using assms
proof (induct c arbitrary: \<sigma> \<tau>)
  case (cond ct s t)
  have "(Fun f [s,t,Fun const []]) \<cdot> \<sigma> = (Fun f [s,t,Fun const []] \<cdot> \<tau>)"
    by (rule term_subst_eq, insert cond, auto)
  then show ?case by auto
next
  case (rewr s t)
  have "(Fun f [s,t]) \<cdot> \<sigma> = (Fun f [s,t] \<cdot> \<tau>)"
    by (rule term_subst_eq, insert rewr, auto)
  then show ?case by auto
next
  case (impl c1 c2 \<sigma> \<tau>)
  from this(1)[of _ \<sigma> \<tau>] this(2)[of \<sigma> \<tau>] this(3)
  show ?case by auto
next
  case (all x c \<sigma> \<tau>)
  {
    fix t
    have "\<sigma>(x := t) \<Turnstile> c = \<tau>(x := t) \<Turnstile> c"
      by (rule all(1), insert all(2), auto)
  }
  then show ?case by auto
qed

text \<open>the substitution lemma for conditional constraints\<close>
lemma cc_models_subst: assumes vs: "range_vars \<sigma>1 \<subseteq> set vs"
  shows "(\<sigma>2 \<Turnstile> c \<cdot>\<^sub>cc (\<sigma>1,vs)) = (\<sigma>1 \<circ>\<^sub>s \<sigma>2 \<Turnstile> c)"
  using vs
proof (induct c arbitrary: \<sigma>1 \<sigma>2 vs)
  (* all cases besides universal quantification are trivial *)
  case (all x c \<sigma>1 \<sigma>2 vs)
  let ?Var = "Var :: 'v \<Rightarrow> ('f,'v)term"
  obtain y where y: "fresh (vs @ vars_cc_list (CC_all x c)) = y" by auto
  with fresh[of "vs @ vars_cc_list (CC_all x c)"] have fresh: "y \<notin> set vs \<union> vars_cc (CC_all x c)" by auto
  with all(2) have y1: "y \<notin> range_vars \<sigma>1" by auto
  let ?vs = "y # vs"
  have "range_vars (\<sigma>1(x := ?Var y)) \<subseteq> set ?vs"
  proof 
    fix z
    assume "z \<in> range_vars (\<sigma>1(x := ?Var y))"
    then obtain u where u: "u \<in> subst_domain (\<sigma>1(x := ?Var y))" and z: "z \<in> vars_term ((\<sigma>1(x := ?Var y)) u)"
      unfolding range_vars_def by force
    show "z \<in> set ?vs"
    proof (cases "u = x")
      case True
      with z show ?thesis by auto
    next
      case False
      with u have "u \<in> subst_domain \<sigma>1" unfolding subst_domain_def by auto
      with z False have "z \<in> range_vars \<sigma>1" unfolding range_vars_def by auto
      with all(2) show ?thesis by auto
    qed
  qed
  note IH = all(1)[OF this]
  show ?case unfolding cc_subst_apply.simps y Let_def 
  proof -
    show "(\<sigma>2 \<Turnstile> CC_all y (c \<cdot>\<^sub>cc (\<sigma>1(x := Var y), ?vs))) = 
       \<sigma>1 \<circ>\<^sub>s \<sigma>2 \<Turnstile> CC_all x c" (is "?l = ?r") 
    proof -
      define P where "P = (\<lambda> t. funas_term t \<subseteq> F \<and> t \<in> NF_trs R)"
      have l: "?l = (\<forall> t. P t \<longrightarrow> \<sigma>2( y := t) \<Turnstile> (c \<cdot>\<^sub>cc (\<sigma>1(x := Var y), ?vs)))" unfolding P_def by auto
      have r: "?r = (\<forall> t. P t \<longrightarrow> (\<sigma>1 \<circ>\<^sub>s \<sigma>2) (x := t) \<Turnstile> c)" unfolding P_def by auto
      {
        fix t
        assume "P t"
        let ?l = "(\<sigma>1(x := Var y) \<circ>\<^sub>s \<sigma>2(y := t))"
        let ?r = "((\<sigma>1 \<circ>\<^sub>s \<sigma>2)(x := t))"
        have "((\<sigma>2( y := t) \<Turnstile> (c \<cdot>\<^sub>cc (\<sigma>1(x := Var y), ?vs)))
           =  ((\<sigma>1 \<circ>\<^sub>s \<sigma>2) (x := t) \<Turnstile> c)) = (?l \<Turnstile> c = ?r \<Turnstile> c)"
          unfolding IH by simp
        also have "(?l \<Turnstile> c = ?r \<Turnstile> c) = True"
        proof -
          {
            fix z
            assume z: "z \<in> vars_cc c"
            have "?l z = ?r z"
            proof (cases "z = x")
              case True
              then show ?thesis by (simp add: subst_compose_def)
            next
              case False
              with z fresh have neq: "y \<noteq> z" by auto
              have "(?l z = ?r z) = (\<sigma>1 z \<cdot> \<sigma>2(y := t) =  \<sigma>1 z \<cdot> \<sigma>2)" unfolding subst_compose_def using False by simp
              moreover have "..."
              proof (cases "z \<in> subst_domain \<sigma>1")
                case True
                then have "vars_term (\<sigma>1 z) \<subseteq> range_vars \<sigma>1" unfolding range_vars_def by auto
                with y1 have y: "y \<notin> vars_term (\<sigma>1 z)" by auto
                show ?thesis
                  by (rule term_subst_eq, insert y, auto)
              next
                case False
                then have z1: "\<sigma>1 z = Var z" unfolding subst_domain_def by auto
                show ?thesis unfolding z1 using neq by simp
              qed
              ultimately show ?thesis by simp
            qed
          } note main = this
          then have "(?l \<Turnstile> c = ?r \<Turnstile> c)" by (rule cc_models_vars)
          then show ?thesis by simp
        qed
        finally have "(\<sigma>2( y := t) \<Turnstile> (c \<cdot>\<^sub>cc (\<sigma>1(x := Var y), ?vs)))
           =  ((\<sigma>1 \<circ>\<^sub>s \<sigma>2) (x := t) \<Turnstile> c)" by simp
      } then show ?thesis unfolding l r by auto
    qed
  qed
qed auto

lemma normalize_alpha: "\<sigma> \<Turnstile> normalize_alpha c = \<sigma> \<Turnstile> c"
proof -
  have id: "\<sigma> \<Turnstile> c = Var \<circ>\<^sub>s \<sigma> \<Turnstile> c" by simp
  show ?thesis unfolding normalize_alpha_def id 
    by (rule cc_models_subst, unfold range_vars_def, auto)
qed

lemma alpha_equivalence: assumes eq: "normalize_alpha c = normalize_alpha d"
  shows "c =cc d"
proof (rule cc_equivI)
  fix \<sigma>
  have "\<sigma> \<Turnstile> c = \<sigma> \<Turnstile> normalize_alpha c" unfolding normalize_alpha ..
  also have "... = \<sigma> \<Turnstile> normalize_alpha d" unfolding eq ..
  also have "... = \<sigma> \<Turnstile> d" unfolding normalize_alpha ..
  finally show "\<sigma> \<Turnstile> c = \<sigma> \<Turnstile> d" .
qed

lemma cc_models_boundE: assumes ys: "\<And> x. x \<notin> set ys \<Longrightarrow> \<sigma> x = \<delta> x"
  and models: "\<sigma> \<Turnstile> cc_bound ys c"
  and F: "normal_F_subst \<delta>"
  shows "\<delta> \<Turnstile> c"
  using ys models
proof (induct ys arbitrary: \<sigma>)
  case Nil
  then show ?case by simp
next
  case (Cons y ys \<sigma>)
  let ?y = "\<delta> y"
  from F[unfolded normal_F_subst_def] have "funas_term ?y \<subseteq> F" and "?y \<in> NF_trs R" by auto
  with Cons(3) have model: "\<sigma>(y := ?y) \<Turnstile> cc_bound ys c" by auto
  show ?case
    by (rule Cons(1)[OF _ model], insert Cons(2), auto)
qed

lemma cc_models_boundI: 
  assumes ys: "\<And> \<sigma>. \<lbrakk>\<And>x. x \<notin> set ys \<Longrightarrow> \<sigma> x = \<delta> x\<rbrakk> \<Longrightarrow> \<lbrakk>\<And>x. x \<in> set ys \<Longrightarrow> funas_term (\<sigma> x) \<subseteq> F \<and> \<sigma> x \<in> NF_trs R\<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile> c"
  shows "\<delta> \<Turnstile> cc_bound ys c"
  using ys
proof (induct ys arbitrary: \<delta>)
  case Nil
  then show ?case by simp
next
  case (Cons y ys \<delta>)
  show ?case unfolding cc_bound.simps cc_models.simps
  proof (intro allI impI)
    fix t
    assume tF: "funas_term t \<subseteq> F" and t: "t \<in> NF_trs R"
    show "\<delta>(y := t) \<Turnstile> cc_bound ys c"
    proof (rule Cons(1))
      fix \<sigma>
      assume eq: "\<And>x. x \<notin> set ys \<Longrightarrow> \<sigma> x = (\<delta>(y := t)) x"
      assume fun_NF: "\<And>x. x \<in> set ys \<Longrightarrow> funas_term (\<sigma> x) \<subseteq> F \<and> \<sigma> x \<in> NF_trs R"
      show "\<sigma> \<Turnstile> c"
      proof (rule Cons(2))
        fix x
        assume "x \<notin> set (y # ys)" with eq[of x] show "\<sigma> x = \<delta> x" by auto
      next
        fix x
        assume "x \<in> set (y # ys)"
        then show "funas_term (\<sigma> x) \<subseteq> F \<and> \<sigma> x \<in> NF_trs R" using eq[of x] fun_NF[of x] tF t
          by (cases "x \<in> set ys", auto)
      qed
    qed
  qed
qed
end

text \<open>in the paper, constraints always occur in the form .. \<and> .. \<and> .. \<longrightarrow> ..,
  therefore we provide means to transform every formula in this form\<close>

fun concl_of :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint" where
  "concl_of (CC_impl c1 c2) = c2"
| "concl_of c = c"

fun prems_of :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint list" where
  "prems_of (CC_impl c1 c2) = c1"
| "prems_of c = []"

definition normalize_cc :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint" where
  "normalize_cc c \<equiv> CC_impl (prems_of c) (concl_of c)"

lemma vars_cc_normalize[simp]: "vars_cc (normalize_cc c) = vars_cc c"
  by (cases c, auto simp: normalize_cc_def)

context fixed_trs_dep_order
begin

lemma normalize_cc: "(\<sigma> \<Turnstile> c) = (\<sigma> \<Turnstile> normalize_cc c)"  unfolding normalize_cc_def
proof (cases c)
  case (CC_impl c1 c2)
  show "\<sigma> \<Turnstile> c = \<sigma> \<Turnstile> CC_impl ((prems_of c)) (concl_of c)" unfolding CC_impl by auto
qed auto

lemma normalize_cc_valid: "cc_valid (normalize_cc c) \<Longrightarrow> cc_valid c" 
  unfolding cc_valid_def normalize_cc[symmetric] by auto

lemma normalize_cc_equivI: "normalize_cc c = normalize_cc d \<Longrightarrow> c =cc d"
  by (rule cc_equivI, unfold normalize_cc[of _ c] normalize_cc[of _ d], auto)

lemma normalize_validI: "normalize_cc c = CC_impl \<phi> \<psi> \<Longrightarrow> 
  \<lbrakk>\<And> \<sigma>. normal_F_subst \<sigma> \<Longrightarrow> \<lbrakk> \<And> c'. c' \<in> set \<phi> \<Longrightarrow> \<sigma> \<Turnstile> c' \<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile> \<psi>\<rbrakk> \<Longrightarrow> cc_valid c" 
  using normalize_cc[of _ c] unfolding cc_valid_def by auto

lemma normalize_validE: "normalize_cc c = CC_impl \<phi> \<psi> \<Longrightarrow> cc_valid c \<Longrightarrow> normal_F_subst \<sigma> \<Longrightarrow>
  \<lbrakk> \<And> c'. c' \<in> set \<phi> \<Longrightarrow> \<sigma> \<Turnstile> c'\<rbrakk> \<Longrightarrow> \<sigma> \<Turnstile> \<psi>"
  using normalize_cc[of _ c] unfolding cc_valid_def by auto
end

context fixed_trs_dep_order_fresh
begin

text \<open>Here, all rules of the induction calculus are formulated. We return a list of constraint instead of one
  constraint, and therefore do not require the primitives "conjunction" and "TRUE" for conditional constraints.\<close>
inductive cc_simplify :: "('f,'v)cond_constraint \<Rightarrow> ('f,'v)cond_constraint list \<Rightarrow> bool" (infix "\<turnstile>" 51) where
(* IV *)  delete_conditions: "normalize_cc c = CC_impl \<phi> \<psi> \<Longrightarrow> normalize_cc c' = CC_impl \<phi>' \<psi> \<Longrightarrow> set \<phi>' \<subseteq> set \<phi> \<Longrightarrow> c \<turnstile> [c']"
| (* I *) constructor_different: "normalize_cc c = CC_impl \<phi> \<psi> \<Longrightarrow> (f,length ss) \<noteq> (g,length ts) \<Longrightarrow> \<not> (defined R (f,length ss)) 
  \<Longrightarrow> CC_rewr (Fun f ss) (Fun g ts) \<in> set \<phi> \<Longrightarrow> c \<turnstile> []"
| (* II *) constructor_same: "normalize_cc c = CC_impl \<phi> \<psi> 
  \<Longrightarrow> c' \<longrightarrow>cc CC_impl (\<phi> @ map (\<lambda> (s,t). CC_rewr s t) (zip ss ts)) \<psi> 
  \<Longrightarrow> length ss = length ts \<Longrightarrow> \<not> (defined R (f,length ss)) 
  \<Longrightarrow> CC_rewr (Fun f ss) (Fun f ts) \<in> set \<phi>  
  \<Longrightarrow> c \<turnstile> [c']" 
| (* III *) variable_left: "normalize_cc c = CC_impl \<phi> \<psi> 
  \<Longrightarrow> c' \<longrightarrow>cc c \<cdot>\<^sub>cc \<tau>
  \<Longrightarrow> \<tau> = (Var(x := q),vars_term_list q) \<Longrightarrow> CC_rewr (Var x) q \<in> set \<phi>
  \<Longrightarrow> c \<turnstile> [c']"
| (* III *) variable_right: "normalize_cc c = CC_impl \<phi> \<psi>  
  \<Longrightarrow> c' \<longrightarrow>cc c \<cdot>\<^sub>cc \<tau>
  \<Longrightarrow> \<tau> = (Var(x := q),vars_term_list q) \<Longrightarrow> CC_rewr q (Var x) \<in> set \<phi>
  \<Longrightarrow> \<lbrakk> \<And> fn. fn \<in> funas_term q \<Longrightarrow> \<not> defined R fn\<rbrakk> 
  \<Longrightarrow> c \<turnstile> [c']"
| (* VI *) simplify_condition: "normalize_cc c = CC_impl \<phi> \<psi>
  \<Longrightarrow> cc_bound ys cc \<in> set \<phi>
  \<Longrightarrow> normalize_cc cc = CC_impl \<phi>' \<psi>'
  \<Longrightarrow> subst_domain \<sigma> \<subseteq> set ys 
  \<Longrightarrow> range_vars \<sigma> \<subseteq> set vs 
  \<Longrightarrow> \<lbrakk>\<And> fn. fn \<in> \<Union>(funas_term ` subst_range \<sigma>) \<Longrightarrow> fn \<in> F \<and> \<not> (defined R fn)\<rbrakk> 
  \<Longrightarrow> \<lbrakk>\<And> c. c \<in> set \<phi>' \<Longrightarrow> \<exists> d \<in> set \<phi>. d \<longrightarrow>cc c \<cdot>\<^sub>cc (\<sigma>,vs)\<rbrakk> 
  \<Longrightarrow> c' \<longrightarrow>cc CC_impl (\<psi>' \<cdot>\<^sub>cc (\<sigma>,vs) # \<phi>) \<psi>
  \<Longrightarrow> c \<turnstile> [c']"
| (* VII *) fun_arg_into_var: "normalize_cc c = CC_impl \<phi> \<psi> 
  \<Longrightarrow> c' \<longrightarrow>cc CC_impl (CC_rewr p (Var x) # CC_rewr (Fun f (bef @ Var x # aft)) q # \<phi>) \<psi>
  \<Longrightarrow> x \<notin> vars_cc c 
  \<Longrightarrow> CC_rewr (Fun f (bef @ p # aft)) q \<in> set \<phi> 
  \<Longrightarrow> funas_term p \<subseteq> F
  \<Longrightarrow> c \<turnstile> [c']"
| (* V *) induction: "normalize_cc c = CC_impl \<phi>' \<psi>  
  \<Longrightarrow> mgu (Fun f (map Var xs)) q = None
  \<Longrightarrow> CC_rewr (Fun f (map Var xs)) q \<in> set \<phi>'
  \<Longrightarrow> set \<phi> \<subseteq> set \<phi>'
  \<Longrightarrow> \<lbrakk> \<And> ls r. length xs = length ls \<Longrightarrow> (Fun f ls,r) \<in> R \<Longrightarrow> \<exists> d ls' r' r_ys_list. 
    (Fun f ls,r) =\<^sub>v (Fun f ls',r') \<and> vars_rule (Fun f ls',r') \<inter> vars_cc (CC_impl (CC_rewr (Fun f (map Var xs)) q # \<phi>) \<psi>) = {} \<and> d \<in> set cs \<and> d \<longrightarrow>cc cc_rule_constraint f ls' r' q xs \<phi> \<psi> r_ys_list
    \<and> (\<forall>(r, ys) \<in> set r_ys_list. root r = Some (f,length xs) \<and> r' \<unrhd> r \<and> vars_term r' \<inter> set ys = {} \<and> (\<forall> fn \<in> funas_args_term r. \<not> defined R fn))\<rbrakk> 
  \<Longrightarrow> distinct xs
  \<Longrightarrow> m \<or> CR (rstep (UR (Fun f (map Var xs)))) \<comment> \<open>we directly require CR instead of UNF, since we only have means to prove the former\<close>
  \<Longrightarrow> c \<turnstile> cs"
end

text \<open>before proving soundness, we need to express the distance to normal form,
  which is the induction relation, if minimality is not present\<close>

definition distance :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> nat" where
  "distance r s a \<equiv> LEAST n. \<exists> b \<in> s. (a,b) \<in> r ^^ n"

lemma distance_path: assumes b: "b \<in> s" and path: "(a,b) \<in> r^*"
  shows "\<exists> b \<in> s. (a,b) \<in> r ^^ distance r s a"
proof -
  let ?p = "\<lambda> n. \<exists> b \<in> s. (a,b) \<in> r ^^ n"
  from rtrancl_imp_relpow[OF path] b have "\<exists> n. ?p n" by blast
  from LeastI_ex[of ?p, OF this]
  show ?thesis unfolding distance_def .
qed

lemma distance_least: assumes "b \<in> s" and "(a,b) \<in> r^^n"
  shows "distance r s a \<le> n"
unfolding distance_def
  by (rule Least_le, insert assms, auto)

lemma distance_Suc_relpow: assumes b: "b \<in> s" and path: "(a,b) \<in> r ^^ distance r s a" and a: "a \<noteq> b"
  shows "\<exists> c. (a,c) \<in> r \<and> (c,b) \<in> r ^^ distance r s c \<and> distance r s a = Suc (distance r s c)"
proof -
  from a path obtain n where d: "distance r s a = Suc n" by (cases "distance r s a", auto)
  from relpow_Suc_D2[OF path[unfolded d]] obtain c where ac: "(a,c) \<in> r" and cb: "(c,b) \<in> r ^^ n" by auto
  from distance_least[OF b cb] have n: "distance r s c \<le> n" .
  {
    assume n: "distance r s c < n"
    from distance_path[OF b relpow_imp_rtrancl[OF cb]] obtain b' where b': "b' \<in> s" and cb': "(c,b') \<in> r ^^ distance r s c" ..
    from distance_least[OF b' relpow_Suc_I2[OF ac cb'], unfolded d] n have False by arith
  }
  with n have n: "n = distance r s c" by arith
  show ?thesis
    by (intro exI conjI, rule ac, insert cb d n, auto)
qed

lemma distance_Suc_rtrancl: assumes b: "b \<in> s" and path: "(a,b) \<in> r^*" and a: "a \<notin> s"
  shows "\<exists> c b. (a,c) \<in> r \<and> (c,b) \<in> r^* \<and> distance r s a = Suc (distance r s c)"
proof -
  from distance_path[OF b path] obtain b' where b': "b' \<in> s" "(a,b') \<in> r ^^ distance r s a" by blast
  from a b' have "a \<noteq> b'" by auto
  from distance_Suc_relpow[OF b' this] obtain c where ac: "(a, c) \<in> r" 
    and cb: "(c, b') \<in> r ^^ distance r s c" and d: "distance r s a = Suc (distance r s c)" by blast
  from ac relpow_imp_rtrancl[OF cb] d show ?thesis by blast
qed

text \<open>the following lemma is essentially proven by using the fact that any normalizing
  reduction can be reordered to a reduction, where one first reduces some subterm c to normal form. 
  Most of the tedious reasoning is hidden in @{thm normalize_subterm_qrsteps_count}.\<close>
lemma distance_subterm: fixes Q R nfs
  defines dist: "dist \<equiv> distance (qrstep nfs Q R) (NF_terms Q)"
  assumes b: "b \<in> NF_terms Q" and ab: "(a,b) \<in> (qrstep nfs Q R)^*"
  and ac: "a \<unrhd> c"
  shows "dist a \<ge> dist c"
proof -
  from distance_path[OF b ab] obtain b where
    b: "b \<in> NF_terms Q" and ab: "(a, b) \<in> qrstep nfs Q R ^^ dist a" unfolding dist by auto
  from supteq_imp_subt_at[OF ac] obtain p where p: "p \<in> poss a" and c: "c = a |_ p" by auto
  from normalize_subterm_qrsteps_count[OF p ab b]
    obtain n1 n2 u where cu: "(c, u) \<in> qrstep nfs Q R ^^ n1" and u: "u \<in> NF_terms Q" and da: "dist a = n1 + n2"
    unfolding c by blast
  from distance_least[OF u cu] have "dist c \<le> n1" unfolding dist by auto
  also have "\<dots> \<le> dist a" unfolding da by simp
  finally show ?thesis .
qed

definition UNF_r_q where 
  "UNF_r_q r q \<equiv> \<forall> a b c. (a,b) \<in> r^* \<longrightarrow> (a,c) \<in> r^* \<longrightarrow> b \<in> q \<longrightarrow> c \<in> q \<longrightarrow> b = c"

text \<open>confluence is a sufficient condition for unique normal forms. In the following lemma,
  usually R' are the usable rules of R.\<close>
lemma CR_imp_UNF_inn: assumes inn: "NF_terms Q \<subseteq> NF_trs R" and sub: "R' \<subseteq> R" and cr: "CR (rstep R')" 
  shows "UNF_r_q (qrstep nfs Q R') (NF_terms Q)"
proof -
  let ?QR = "qrstep nfs Q R"
  let ?QR' = "qrstep nfs Q R'"
  let ?Q = "NF_terms Q"
  let ?R' = "rstep R'"
  show ?thesis 
  unfolding UNF_r_q_def
  proof (intro allI impI)
    fix a b c
    assume ab: "(a,b) \<in> ?QR'^*" and ac: "(a,c) \<in> ?QR'^*" and b: "b \<in> ?Q" and c: "c \<in> ?Q"
    from inn NF_anti_mono[OF rstep_mono[OF sub]] have inn: "?Q \<subseteq> NF ?R'" by auto
    have sub: "?QR'^* \<subseteq> ?R'^*" by (rule rtrancl_mono, auto)
    from sub ab ac have ab: "(a,b) \<in> ?R'^*" and ac: "(a,c) \<in> ?R'^*" by auto
    from inn b c have b: "b \<in> NF ?R'" and c: "c \<in> NF ?R'" by auto
    from CR_imp_UNF[OF cr] ab ac b c show "b = c" by auto
  qed
qed    
  
text \<open>if there unique normal forms, then one can reach any normal form via a path, where the length
  of this path is exactly the distance\<close>
lemma distance_NF_UNF: assumes NF: "s \<subseteq> q" and UNF: "UNF_r_q r q" and b: "b \<in> s" and path: "(a,b) \<in> r^*"
  shows "(a,b) \<in> r^^distance r s a"
proof -
  from distance_path[OF b path] obtain b' where b': "b' \<in> s" and ab': "(a,b') \<in> r ^^ distance r s a" ..
  from b b' NF have "b \<in> q" "b' \<in> q" by auto
  with path relpow_imp_rtrancl[OF ab'] UNF[unfolded UNF_r_q_def] have "b' = b" by auto
  with ab' show ?thesis by auto
qed  


context fixed_trs_dep_order_fresh
begin

text \<open>the main soundness lemma for the induction calculus\<close>
lemma cc_simplify: "c \<turnstile> c' \<Longrightarrow> Ball (set c') cc_valid \<Longrightarrow> cc_valid c"
proof -
  from wwf_var_cond[OF wwf] have Rfun: "\<forall>(l, r)\<in>R. is_Fun l" .
  note a_ndef = ndef_applicable_rules[of R _ Q]
  {
    fix \<delta> :: "('f,'v)subst"
    fix vs :: "'v list"
    fix x :: 'v
    fix q :: "('f,'v)term"
    fix \<phi> :: "('f,'v)cond_constraint"
    assume vs: "vars_term q \<subseteq> set vs"
    assume id: "\<delta> x = q \<cdot> \<delta>"
    have "(\<delta> \<Turnstile> \<phi> \<cdot>\<^sub>cc (Var(x := q),vs)) = (Var(x := q) \<circ>\<^sub>s \<delta> \<Turnstile> \<phi>)"
    proof (rule cc_models_subst)
      show "range_vars (Var(x := q)) \<subseteq> set vs" unfolding range_vars_def subst_range.simps subst_domain_def using vs
        by auto
    qed
    also have "(Var(x := q) \<circ>\<^sub>s \<delta>) = \<delta>"
    proof
      fix y
      show "(Var(x := q) \<circ>\<^sub>s \<delta>) y = \<delta> y"
        by (unfold subst_compose_def, cases "y = x", insert id, auto)
    qed
    finally have "(\<delta> \<Turnstile> \<phi> \<cdot>\<^sub>cc (Var(x := q),vs)) = (\<delta> \<Turnstile> \<phi>)" .
  } note subst = this (* subst is useful result for both variable_left and variable_right *)
  show "c \<turnstile> c' \<Longrightarrow> Ball (set c') cc_valid \<Longrightarrow> cc_valid c"
  proof (induct rule: cc_simplify.induct)
    case (delete_conditions c \<phi> \<psi> c' \<chi>)
    then have c': "cc_valid c'" by auto
    show ?case
      by (rule normalize_validI[OF delete_conditions(1)],
        insert normalize_validE[OF delete_conditions(2) c'] delete_conditions(3), auto)
  next
    case (constructor_different c \<phi> \<psi> f ss g ts)
    show ?case
    proof (rule normalize_validI[OF constructor_different(1)])
      fix \<sigma>
      assume phi: "\<And> c'. c' \<in> set \<phi> \<Longrightarrow> \<sigma> \<Turnstile> c'"
      have "(Fun f ss \<cdot> \<sigma>, Fun g ts \<cdot> \<sigma>) \<notin> (qrstep nfs Q R)^*"
      proof
        let ?\<sigma> = "map (\<lambda> t. t \<cdot> \<sigma>)"
        from constructor_different(3) have ndef: "\<not> defined R (the (root (Fun f (?\<sigma> ss))))" by simp
        assume "(Fun f ss \<cdot> \<sigma>, Fun g ts \<cdot> \<sigma>) \<in> (qrstep nfs Q R)^*"
        then have "(Fun f (?\<sigma> ss), Fun g (?\<sigma> ts)) \<in> (qrstep nfs Q R)^*" by simp
        from nrqrsteps_preserve_root[OF qrsteps_imp_nrqrsteps[OF Rfun a_ndef[OF ndef] this]]
        show False using constructor_different(2) by simp
      qed
      with phi[OF constructor_different(4)]
      show "\<sigma> \<Turnstile> \<psi>" by auto
    qed
  next
    case (constructor_same c \<phi> \<psi> c' ss ts f)
    then have c': "cc_valid c'" by auto
    note valid = cc_validE[OF cc_impliesE[OF constructor_same(2) c']]
    show ?case
    proof (rule normalize_validI[OF constructor_same(1)])
      fix \<sigma>
      assume nfs: "normal_F_subst \<sigma>"
      note valid = valid[OF nfs]
      assume phi: "\<And>c'. c' \<in> set \<phi> \<Longrightarrow> \<sigma> \<Turnstile> c'"
      from phi[OF constructor_same(5)] have
        mrewr: "\<sigma> \<Turnstile> CC_rewr (Fun f ss) (Fun f ts)" by auto
      from constructor_same have len: "length ss = length ts" by simp
      have "Ball (set (map (\<lambda>(s, t). CC_rewr s t) (zip ss ts))) (cc_models \<sigma>) = 
        (\<forall> i. i < length ss \<longrightarrow> \<sigma> \<Turnstile> CC_rewr (ss ! i) (ts ! i))" using len
        by (auto simp: set_zip)
      also have "..."
      proof (intro allI impI)
        fix i
        assume i: "i < length ss"
        let ?\<sigma> = "map (\<lambda> t. t \<cdot> \<sigma>)"
        from a_ndef[OF constructor_same(4)] have ndef: "\<not> defined (applicable_rules Q R) (the (root (Fun f (?\<sigma> ss))))" by simp
        from mrewr have steps: "(Fun f (?\<sigma> ss), Fun f (?\<sigma> ts)) \<in> (qrstep nfs Q R)^*" by simp
        from mrewr have nf: "Fun f (?\<sigma> ts) \<in> NF_terms Q" by simp
        from nrqrsteps_imp_arg_qrsteps[OF qrsteps_imp_nrqrsteps[OF Rfun ndef steps], of i] i len
        have steps: "(ss ! i \<cdot> \<sigma>, ts ! i \<cdot> \<sigma>) \<in> (qrstep nfs Q R)^*" by auto
        have nf: "ts ! i \<cdot> \<sigma> \<in> NF_terms Q" by (rule NF_subterm[OF nf], insert i len, auto)
        {
          assume m
          with mrewr have SN: "SN_on (qrstep nfs Q R) {Fun f (?\<sigma> ss)}" unfolding m_SN_def cc_models.simps by simp
          have SN: "SN_on (qrstep nfs Q R) {ss ! i \<cdot> \<sigma>}"
            by (rule SN_imp_SN_arg_gen[OF ctxt_closed_qrstep SN], insert i, auto)
        }
        then have SN: "m_SN (ss ! i \<cdot> \<sigma>)" unfolding m_SN_def by simp
        show "\<sigma> \<Turnstile> CC_rewr (ss ! i) (ts ! i)" using steps nf SN by auto
      qed
      finally show "\<sigma> \<Turnstile> \<psi>" using valid phi by auto
    qed
  next
    case (variable_left c \<phi> \<psi> c' \<tau> x q)
    then have c': "cc_valid c'" by auto
    note valid = cc_validE[OF cc_impliesE[OF variable_left(2) c']]
    show ?case
    proof (rule normalize_validI[OF variable_left(1)])
      fix \<sigma>
      assume sigma: "normal_F_subst \<sigma>"
      assume phi: "\<And>c'. c' \<in> set \<phi> \<Longrightarrow> \<sigma> \<Turnstile> c'"
      from phi[OF variable_left(4)] have 
        steps: "(\<sigma> x, q \<cdot> \<sigma>) \<in> (qrstep nfs Q R)^*" by auto
      from steps rtrancl_mono[OF qrstep_mono[of R R Q "{}" nfs]] have steps: "(\<sigma> x, q \<cdot> \<sigma>) \<in> (rstep R)^*" by auto
      from sigma[unfolded normal_F_subst_def] NFQ have sigmax: "\<sigma> x \<in> NF_trs R" by force
      from steps sigmax have id: "\<sigma> x = q \<cdot> \<sigma>" unfolding NF_def by (induct, auto)
      have subset: "vars_term q \<subseteq> set (vars_term_list q)" by auto
      note subst = subst[OF subset id, unfolded variable_left(3)[symmetric]]
      from valid[OF sigma, unfolded subst normalize_cc[of _ c] variable_left(1)] phi
      show "\<sigma> \<Turnstile> \<psi>" by auto
    qed
  next
    case (variable_right c \<phi> \<psi>  c' \<tau> x q)
    then have c': "cc_valid c'" by auto
    note valid = cc_validE[OF cc_impliesE[OF variable_right(2) c']]
    show ?case
    proof (rule normalize_validI[OF variable_right(1)])
      fix \<sigma>
      assume sigma: "normal_F_subst \<sigma>"
      assume phi: "\<And>c'. c' \<in> set \<phi> \<Longrightarrow> \<sigma> \<Turnstile> c'"
      from phi[OF variable_right(4)] have 
        steps: "(q \<cdot> \<sigma>, \<sigma> x) \<in> (qrstep nfs Q R)^*" by auto
      have "q \<cdot> \<sigma> \<in> NF (qrstep nfs Q R)"
      proof (rule NF_subst_qrstep[OF a_ndef[OF variable_right(5)] _ Rfun])
        fix x
        from sigma[unfolded normal_F_subst_def] have NF: "\<sigma> x \<in> NF_trs R" by auto
        then show "\<sigma> x \<in> NF (qrstep nfs Q R)" using NF_anti_mono[OF qrstep_mono[of R R Q "{}" nfs]] by auto
      qed
      with steps
      have id: "\<sigma> x = q \<cdot> \<sigma>" unfolding NF_def by (induct, auto)
      have subset: "vars_term q \<subseteq> set (vars_term_list q)" by auto
      note subst = subst[OF subset id, unfolded variable_right(3)[symmetric]]
      from valid[OF sigma, unfolded subst normalize_cc[of _ c] variable_right(1)] phi
      show "\<sigma> \<Turnstile> \<psi>" by auto
    qed
  next
    case (simplify_condition c \<phi> \<psi> ys cc \<phi>' \<psi>' \<sigma> vs c')
    then have c': "cc_valid c'" by auto
    show ?case
    proof (rule normalize_validI[OF simplify_condition(1)])
      fix \<delta>
      assume delta: "normal_F_subst \<delta>"
      assume "\<And>c'. c' \<in> set \<phi> \<Longrightarrow> \<delta> \<Turnstile> c'"
      with simplify_condition(2)
      have delta_bound: "\<delta> \<Turnstile> cc_bound ys cc" and delta_phi: "Ball (set \<phi>) (cc_models \<delta>)" by auto
      note delta_nf = delta[unfolded normal_F_subst_def]
      let ?\<delta>' = "\<sigma> \<circ>\<^sub>s \<delta>"
      {
        fix x
        assume "x \<notin> subst_domain \<sigma>"
        then have "\<sigma> x = Var x" unfolding subst_domain_def by auto
        then have "?\<delta>' x = \<delta> x" unfolding subst_compose_def by simp
      } note delta_id = this
      with simplify_condition(4) have delta_idd: "\<And> x. x \<notin> set ys \<Longrightarrow> \<delta> x = ?\<delta>' x" by force
      {
        fix t
        assume "t \<in> range ?\<delta>'"
        then obtain x where x: "?\<delta>' x = t" by auto
        have "funas_term t \<subseteq> F \<and> t \<in> NF_trs R"
        proof (cases "x \<in> subst_domain \<sigma>")
          case False
          from x delta_id[OF this] have "t \<in> range \<delta>" by auto
          with delta_nf show ?thesis by auto
        next
          case True
          with simplify_condition(4) have x_ys: "x \<in> set ys" by auto
          from x have t: "t = \<sigma> x \<cdot> \<delta>" unfolding subst_compose_def by auto
          from True have range: "\<sigma> x \<in> subst_range \<sigma>" by simp 
          from range simplify_condition(6) have F: "funas_term (\<sigma> x) \<subseteq> F" by force
          from range simplify_condition(6) have ndef: "\<And> fn. fn \<in> funas_term (\<sigma> x) \<Longrightarrow> \<not> defined R fn" by force
          show ?thesis unfolding t
          proof
            show "funas_term (\<sigma> x \<cdot> \<delta>) \<subseteq> F" using F delta_nf unfolding funas_term_subst by auto
          next
            have "\<sigma> x \<cdot> \<delta> \<in> NF (qrstep nfs {} R)"
            proof (rule NF_subst_qrstep[OF _ _ Rfun])
              fix fn
              assume "fn \<in> funas_term (\<sigma> x)"
              from ndef[OF this] show "\<not> defined (applicable_rules {} R) fn" unfolding applicable_rules_def applicable_rule_def by auto
            next
              fix y
              assume "y \<in> vars_term (\<sigma> x)"
              show "\<delta> y \<in> NF (qrstep nfs {} R)" using delta_nf by auto
            qed
            then show "\<sigma> x \<cdot> \<delta> \<in> NF_trs R" by auto
          qed
        qed
      }
      then have nF: "normal_F_subst ?\<delta>'" unfolding normal_F_subst_def by auto
      from cc_models_boundE[OF delta_idd delta_bound nF]
      have "?\<delta>' \<Turnstile> cc" .
      from this[unfolded normalize_cc[of _ cc] simplify_condition(3)]
      have "?\<delta>' \<Turnstile> CC_impl \<phi>' \<psi>'" .
      from this[unfolded cc_models_subst[OF simplify_condition(5), symmetric]]
      have delta_imp: "\<delta> \<Turnstile> CC_impl \<phi>' \<psi>' \<cdot>\<^sub>cc (\<sigma>,vs)" .
      {
        fix c
        assume "c \<in> set \<phi>'"
        from simplify_condition(7)[OF this] obtain d where d: "d \<in> set \<phi>"
          and imp: "d \<longrightarrow>cc c \<cdot>\<^sub>cc (\<sigma>,vs)" by auto
        from d delta_phi have "\<delta> \<Turnstile> d" by auto
        from cc_implies_substE[OF imp this]
        have "\<delta> \<Turnstile> c \<cdot>\<^sub>cc (\<sigma>,vs)" .
      }
      with delta_imp have "\<delta> \<Turnstile> \<psi>' \<cdot>\<^sub>cc (\<sigma>,vs)" by auto
      with delta_phi
      have "Ball (set (\<psi>' \<cdot>\<^sub>cc (\<sigma>,vs) # \<phi>)) (cc_models \<delta>)" by auto
      with cc_validE[OF cc_impliesE[OF simplify_condition(8) c'] delta]
      show "\<delta> \<Turnstile> \<psi>" by auto
    qed
  next
    case (fun_arg_into_var c \<phi> \<psi> c' p x f bef aft q)
    then have c': "cc_valid c'" by auto
    note valid = cc_validE[OF cc_impliesE[OF fun_arg_into_var(2) c']]
    note c = fun_arg_into_var(1)
    from fun_arg_into_var(1,3) have "x \<notin> vars_cc (CC_impl \<phi> \<psi>)" using vars_cc_normalize[of c] by auto
    note x_fresh = this[simplified]
    from fun_arg_into_var(4) x_fresh have "x \<notin> vars_cc (CC_rewr (Fun f (bef @ p # aft)) q)" by auto
    note x_fresh' = this[simplified]
    let ?t = "\<lambda> x. Fun f (bef @ x # aft)"
    show ?case
    proof (rule normalize_validI[OF c])
      fix \<sigma>
      assume sigma: "normal_F_subst \<sigma>"
      assume phi: "\<And>c'. c' \<in> set \<phi> \<Longrightarrow> \<sigma> \<Turnstile> c'"
      from phi[OF fun_arg_into_var(4)]
      have rewr: "\<sigma> \<Turnstile> CC_rewr (?t p) q" .
      let ?tsig = "\<lambda> x. Fun f (map (\<lambda> t. t \<cdot> \<sigma>) bef @ x # map (\<lambda> t. t \<cdot> \<sigma>) aft)"
      from rewr have SN: "m_SN (?tsig (p \<cdot> \<sigma>))" by simp
      from rewr have steps: "(?tsig (p \<cdot> \<sigma>), q \<cdot> \<sigma>) \<in> (qrstep nfs Q R)^*" by simp
      from rewr have NF: "q \<cdot> \<sigma> \<in> NFQ" by simp
      from normalize_subterm_qrsteps[OF _ steps NF, of "[length bef]"]
      obtain u where steps1: "(p \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)^*" and u: "u \<in> NFQ"
        and steps2: "(?tsig u, q \<cdot> \<sigma>) \<in> (qrstep nfs Q R)^*" by (auto simp: nth_append)        
      let ?\<delta> = "\<sigma>(x := u)"
      have p: "p \<cdot> ?\<delta> = p \<cdot> \<sigma>" by (rule term_subst_eq, insert x_fresh', auto)
      have q: "q \<cdot> ?\<delta> = q \<cdot> \<sigma>" by (rule term_subst_eq, insert x_fresh', auto)
      let ?m = "map (\<lambda>t. t \<cdot> \<sigma>)"
      let ?mu = "map (\<lambda>t. t \<cdot> \<sigma>(x := u))"
      have "(?t (Var x) \<cdot> \<sigma>(x := u) = ?tsig u) = (?mu (bef @ aft) = ?m (bef @ aft))" by simp
      moreover have "..."
        by (rule map_cong[OF refl term_subst_eq], insert x_fresh', auto)
      ultimately have tu: "?t (Var x) \<cdot> \<sigma>(x := u) = ?tsig u" by simp
      {
        assume m
        with SN[unfolded m_SN_def] have SN: "SN_on (qrstep nfs Q R) {?tsig (p \<cdot> \<sigma>)}" by blast
        from SN_imp_SN_arg_gen[OF ctxt_closed_qrstep SN, of "p \<cdot> \<sigma>"] have SNp: "SN_on (qrstep nfs Q R) {p \<cdot> \<sigma>}" by auto
        from steps_preserve_SN_on[OF ctxt.closedD[OF ctxt.closed_rtrancl[OF ctxt_closed_qrstep] steps1], of "More f (?m bef) Hole (?m aft)"]
        SN have SNu: "SN_on (qrstep nfs Q R) {?tsig u}" by auto
        note SNp SNu
      }
      then have SNp: "m_SN (p \<cdot> \<sigma>)" and SNu: "m_SN (?tsig u)" unfolding m_SN_def by auto
      {
        fix c
        assume "c \<in> set \<phi> \<union> {\<psi>}"
        with x_fresh have x: "x \<notin> vars_cc c" by auto
        have "\<sigma> \<Turnstile> c = ?\<delta> \<Turnstile> c"
          by (rule cc_models_vars, insert x, auto)
      } note id = this
      have rewr1: "?\<delta> \<Turnstile> CC_rewr p (Var x)" unfolding cc_models.simps p using u SNp steps1 by auto
      have rewr2: "?\<delta> \<Turnstile> CC_rewr (?t (Var x)) q" unfolding cc_models.simps tu q using steps2 NF SNu by auto
      have phi: "Ball (set \<phi>) (cc_models ?\<delta>)" using phi id by auto
      from NFQ u have NF: "u \<in> NF_trs R" by auto
      note sigma = sigma[unfolded normal_F_subst_def]
      have uF: "funas_term u \<subseteq> F"
        by (rule qrsteps_funas_term[OF wwf RF _ steps1], unfold funas_term_subst, insert sigma fun_arg_into_var(5), auto)
      {
        fix y
        have F: "funas_term (?\<delta> y) \<subseteq> F" using sigma uF by auto
        have NF: "?\<delta> y \<in> NF_trs R" using NF sigma by auto
        note F NF
      }
      then have delta: "normal_F_subst ?\<delta>" unfolding normal_F_subst_def by fastforce
      from id
      have "\<sigma> \<Turnstile> \<psi> = ?\<delta> \<Turnstile> \<psi>" by auto
      also have "..." using valid[OF delta] rewr1 rewr2 phi by auto
      finally show "\<sigma> \<Turnstile> \<psi>" .
    qed
  next
    case (induction cc \<phi>' \<psi> f xs q \<phi> cs)
    note cc = induction(1)
    note \<phi> = induction(4)
    note distinct = induction(6)
    let ?xs = "map Var xs :: ('f,'v)term list"
    let ?\<phi> = "CC_impl (CC_rewr (Fun f ?xs) q # \<phi>) \<psi>"
    let ?P = "\<lambda> \<delta>. normal_F_subst \<delta> \<longrightarrow> \<delta> \<Turnstile> ?\<phi>"
    let ?UR = "UR (Fun f ?xs)"
    from qrstep_mono[OF UR_sub subset_refl] have UR_R: "qrstep nfs Q ?UR \<subseteq> qrstep nfs Q R" .
    then have step_UR: "\<And> p. p \<in> qrstep nfs Q ?UR \<Longrightarrow> p \<in> qrstep nfs Q R" by auto
    from rtrancl_mono[OF UR_R] have steps_UR: "\<And> p. p \<in> (qrstep nfs Q ?UR)^* \<Longrightarrow> p \<in> (qrstep nfs Q R)^*" by auto
    {
      fix \<delta>
      assume delta: "normal_F_subst \<delta>"
      define dist where "dist = distance (qrstep nfs Q ?UR) (NF_terms Q)"
      define SNrel1 where "SNrel1 = inv_image (restrict_SN (qrstep nfs Q R O {\<unrhd>}) (qrstep nfs Q R)) (\<lambda> \<delta>. (Fun f ?xs) \<cdot> \<delta>)"
      define SNrel2 where "SNrel2 = inv_image {(x,y). x > (y :: nat)} (\<lambda> \<delta>. dist (Fun f ?xs \<cdot> \<delta>))"
      (* use SNrel1 if minimality is provided, otherwise use SNrel2 (then we have CR / UIN) *)
      define SNrel where "SNrel = (if m then SNrel1 else SNrel2)"
      (* proof that this relation is strongly normalizing *)
      have SN_rel: "SN SNrel"
      proof (cases m)
        case True
        have "SN SNrel1" unfolding SNrel1_def
        proof (rule SN_inv_image[OF SN_subset[OF SN_restrict_SN_idemp]])
          let ?R = "({\<rhd>} \<union> qrstep nfs Q R)^+"
          note d = restrict_SN_def
          show "restrict_SN (qrstep nfs Q R O {\<unrhd>}) (qrstep nfs Q R) \<subseteq> restrict_SN ?R ?R" (is "?l \<subseteq> ?r")
          proof
            fix s t
            assume "(s,t) \<in> ?l"
            from this[unfolded d] have step: "(s,t) \<in> qrstep nfs Q R O {\<unrhd>}" and SN: "SN_on (qrstep nfs Q R) {s}" by auto
            from step have "(s,t) \<in> qrstep nfs Q R \<union> qrstep nfs Q R O {\<rhd>}" by auto
            then have step: "(s,t) \<in> ?R" by regexp
            with SN_on_trancl[OF SN_on_qrstep_imp_SN_on_supt_union_qrstep[OF SN]] show "(s,t) \<in> ?r" unfolding d by auto
          qed
        qed
        then show ?thesis unfolding SNrel_def using True by simp
      next
        case False
        have id: "{(x, y). y < x} = {(x, y). y > (x :: nat)}^-1" by auto
        have "SN SNrel2" unfolding SNrel2_def id
          by (rule SN_inv_image, rule wf_imp_SN, insert wf_less, simp)
        then show ?thesis unfolding SNrel_def using False by simp
      qed
      (* next prove main property by induction via SNrel *)
      have "\<delta> \<Turnstile> ?\<phi>"
      proof (induct \<delta> rule: SN_induct[where P = ?P, rule_format, OF SN_rel])
        show "normal_F_subst \<delta>" by fact
      next
        fix \<delta>
        assume delta: "normal_F_subst \<delta>"
        assume IH: "\<And> \<tau>. (\<delta>, \<tau>) \<in> SNrel \<Longrightarrow> normal_F_subst \<tau> \<Longrightarrow> \<tau> \<Turnstile> ?\<phi>"
        show "\<delta> \<Turnstile> ?\<phi>" unfolding cc_models.simps(2)
        proof
          assume conj: "Ball (set (CC_rewr (Fun f ?xs) q # \<phi>)) (cc_models \<delta>)"
          then have rewr: "\<delta> \<Turnstile> CC_rewr (Fun f ?xs) q" and phi: "Ball (set \<phi>) (cc_models \<delta>)" by auto
          from rewr have steps: "(Fun f ?xs \<cdot> \<delta>, q \<cdot> \<delta>) \<in> (qrstep nfs Q R)^*" and nf_q: "q \<cdot> \<delta> \<in> NFQ" 
            and SN: "m_SN (Fun f ?xs \<cdot> \<delta>)" by auto
          (* if there is a first reduction step, it must be a reduction at the root *)
          {
            fix u R'
            assume u: "(Fun f ?xs \<cdot> \<delta>, u) \<in> qrstep nfs Q R'" and sub: "R' \<subseteq> R"
            have "(Fun f ?xs \<cdot> \<delta>, u) \<notin> nrqrstep nfs Q R'"
            proof
              assume "(Fun f ?xs \<cdot> \<delta>, u) \<in> nrqrstep nfs Q R'"
              from nrqrstep_imp_arg_qrstep[OF this] obtain i where 
                "(\<delta> (xs ! i), args u ! i) \<in> qrstep nfs Q R'" by auto
              with qrstep_mono[OF sub, of Q "{}" nfs] have "(\<delta> (xs ! i), args u ! i) \<in> rstep R" by auto
              moreover from delta[unfolded normal_F_subst_def] have "\<delta> (xs ! i) \<in> NF_trs R" by auto
              ultimately show False by auto
            qed            
            with u[unfolded qrstep_iff_rqrstep_or_nrqrstep] 
            have "(Fun f ?xs \<cdot> \<delta>, u) \<in> rqrstep nfs Q R'" by auto
          } note rqrstep = this
          (* there must be at least one step to reach normal form *)
          have neq: "Fun f ?xs \<cdot> \<delta> \<noteq> q \<cdot> \<delta>"
          proof
            assume "Fun f ?xs \<cdot> \<delta> = q \<cdot> \<delta>"
            then have "\<delta> \<in> unifiers {(Fun f ?xs, q)}" unfolding unifiers_def by auto
            with mgu_complete[OF induction(2)] show False by auto
          qed
          (* all steps are performed using usable rules *)
          {
            from rtranclD[OF steps, unfolded trancl_unfold_left] neq
            obtain u where step: "(Fun f ?xs \<cdot> \<delta>, u) \<in> qrstep nfs Q R" by auto
            from rqrstep[OF step subset_refl] have "(Fun f ?xs \<cdot> \<delta>, u) \<in> rqrstep nfs Q R" .
            from rqrstepE[OF this] have NFQ: "\<And> u. u \<lhd> Fun f ?xs \<cdot> \<delta> \<Longrightarrow> u \<in> NFQ" by metis
            {
              fix x
              assume "x \<in> vars_term (Fun f ?xs)"
              then have "Var x \<lhd> Fun f ?xs" by auto
              from NFQ[OF supt_subst[OF this]] have "\<delta> x \<in> NFQ" by auto
            }
            then have "\<delta> ` vars_term (Fun f ?xs) \<subseteq> NFQ" by auto
            from UR[OF this steps] have "(Fun f ?xs \<cdot> \<delta>, q \<cdot> \<delta>) \<in> (qrstep nfs Q ?UR)^*" .
          } note steps = this
          (* obtain first rewrite step and remaining steps (with smaller distance) *)
          have "\<exists> u d. (Fun f ?xs \<cdot> \<delta>, u) \<in> qrstep nfs Q ?UR \<and> (u,q \<cdot> \<delta>) \<in> (qrstep nfs Q ?UR)^^d \<and> (m \<or> dist (Fun f ?xs \<cdot> \<delta>) = Suc d)"
          proof (cases m)
            case True
            from rtranclD[OF steps, unfolded trancl_unfold_left] neq
            obtain u where step: "(Fun f ?xs \<cdot> \<delta>, u) \<in> qrstep nfs Q ?UR" and steps: "(u,q \<cdot> \<delta>) \<in> (qrstep nfs Q ?UR)^*" by auto
            from step True rtrancl_imp_relpow[OF steps] show ?thesis by auto
          next
            case False
            from False induction(7) have CR: "CR (rstep ?UR)" by auto
            from CR_imp_UNF_inn[OF NFQ UR_sub CR] have "UNF_r_q (qrstep nfs Q ?UR) NFQ" .
            from distance_NF_UNF[OF subset_refl this nf_q steps]
            have "(Fun f ?xs \<cdot> \<delta>, q \<cdot> \<delta>) \<in> qrstep nfs Q ?UR ^^ distance (qrstep nfs Q ?UR) NFQ (Fun f ?xs \<cdot> \<delta>)" .
            from distance_Suc_relpow[OF nf_q this neq]
            show ?thesis unfolding dist_def by auto
          qed
          then obtain u d where step: "(Fun f ?xs \<cdot> \<delta>, u) \<in> qrstep nfs Q ?UR"
            and steps_d: "(u,q \<cdot> \<delta>) \<in> (qrstep nfs Q ?UR)^^d" and dist: "m \<or> dist (Fun f ?xs \<cdot> \<delta>) = Suc d" by auto
          from relpow_imp_rtrancl[OF steps_d] have steps: "(u,q \<cdot> \<delta>) \<in> (qrstep nfs Q ?UR)^*" .
          from SN step_preserves_SN_on[OF step_UR[OF step]] have SN_u: "m_SN u" unfolding m_SN_def by auto
          from rqrstep[OF step UR_sub]
          (* first step is reduction at root *)
          have "(Fun f ?xs \<cdot> \<delta>, u) \<in> rqrstep nfs Q ?UR" .
          (* with rule l \<rightarrow> r and substitution \<sigma>'' *)
          from rqrstepE[OF this] obtain l r \<sigma>'' where 
            nf: "\<forall>u\<lhd>l \<cdot> \<sigma>''. u \<in> NFQ" and lr_U: "(l, r) \<in> ?UR" and fl: "Fun f ?xs \<cdot> \<delta> = l \<cdot> \<sigma>''" and u: "u = r \<cdot> \<sigma>''" and nfs: "NF_subst nfs (l, r) \<sigma>'' Q" .
          from rqrstepI[OF nf _ fl u nfs] have rstep: "(Fun f ?xs \<cdot> \<delta>, u) \<in> rqrstep nfs Q {(l,r)}" by auto
          from lr_U UR_sub have lr: "(l,r) \<in> R" by auto
          from only_applicable_rules[OF nf] lr wwf UR_sub have vars: "vars_term r \<subseteq> vars_term l" unfolding wwf_qtrs_def by auto
          from Rfun lr fl obtain ls where l: "l = Fun f ls" by (cases l, auto)
          from fl l have id: "map \<delta> xs = map (\<lambda> t. t \<cdot> \<sigma>'') ls" by (simp add: comp_def)
          from arg_cong[OF id, of length] have len: "length ls = length xs" by auto
          (* next, use preconditions of induction rule *)
          from induction(5)[OF len[symmetric] lr[unfolded l]] obtain c ls' r' rs_ys_list
            where eq: "(Fun f ls, r) =\<^sub>v (Fun f ls', r')" and vars_cc: "vars_rule (Fun f ls', r') \<inter> vars_cc ?\<phi> = {}"
            and c: "c \<longrightarrow>cc cc_rule_constraint f ls' r' q xs \<phi> \<psi> rs_ys_list" and c_cs: "c \<in> set cs" 
            and pre: "(\<forall>(r, ys)\<in>set rs_ys_list. root r = Some (f,length xs) \<and> r' \<unrhd> r \<and> vars_term r' \<inter> set ys = {} \<and> (\<forall>fn\<in>funas_args_term r. \<not> defined R fn))" by auto
          from rqrstep_rename_vars[of "{(Fun f ls,r)}" "{(Fun f ls',r')}" nfs Q] rstep[unfolded l] eq
          have "(Fun f ?xs \<cdot> \<delta>, u) \<in> rqrstep nfs Q {(Fun f ls',r')}" by auto
          from rqrstepE[OF this] obtain \<sigma>'' where 
            nf: "\<forall>u\<lhd>Fun f ls' \<cdot> \<sigma>''. u \<in> NFQ" and fl: "Fun f ?xs \<cdot> \<delta> = Fun f ls' \<cdot> \<sigma>''" and u: "u = r' \<cdot> \<sigma>''" and nfs: "NF_subst nfs (Fun f ls', r') \<sigma>'' Q" by auto
          from fl l have id: "map \<delta> xs = map (\<lambda> t. t \<cdot> \<sigma>'') ls'" by (simp add: comp_def)
          from arg_cong[OF id, of length] have len: "length ls' = length xs" by auto
          from eq_rule_mod_vars_var_cond[OF eq vars[unfolded l]] have vars: "vars_term r' \<subseteq> vars_term (Fun f ls')"  .
          (* next, define required substitutions *)
          define \<sigma> where "\<sigma> = mk_subst Var (zip xs ls')"
          have "ls' = map id ls'" by simp
          also have "... = map \<sigma> xs"
          proof (rule nth_map_conv[OF len], intro allI impI)
            fix i
            assume i: "i < length ls'"
            have "ls' ! i = \<sigma> (xs ! i)" unfolding \<sigma>_def using mk_subst_distinct[OF distinct i[unfolded len] i]
              by simp
            then show "id (ls' ! i) = \<sigma> (xs ! i)" by simp
          qed
          finally have ls: "ls' = map \<sigma> xs" .
          from id[unfolded ls] have "map \<delta> xs = map (\<lambda> x. \<sigma> x \<cdot> \<sigma>'') xs" by auto
          then have delta_sigma: "\<And> x. x \<in> set xs \<Longrightarrow> \<delta> x = \<sigma> x \<cdot> \<sigma>''" by auto
          define \<sigma>' where "\<sigma>' = (\<lambda> x. if x \<in> vars_term (Fun f ls') then \<sigma>'' x else \<delta> x)"
          (* on variables in f(ls'), \<sigma>' = \<sigma>'' *)
          {
            fix t :: "('f,'v)term"
            assume sub: "vars_term t \<subseteq> vars_term (Fun f ls')"            
            have "t \<cdot> \<sigma>'' = t \<cdot> \<sigma>'" unfolding \<sigma>'_def
              by (rule term_subst_eq, insert sub, auto)
          } note conv1 = this
          (* on variables not in f(ls'), \<sigma>\<sigma>' = \<delta> *)
          have delta_sigma': "\<And> x.  x \<notin> vars_term (Fun f ls') \<Longrightarrow> \<delta> x = (\<sigma> \<circ>\<^sub>s \<sigma>') x"
          proof -
            fix x
            assume x: "x \<notin> vars_term (Fun f ls')"
            have "\<sigma> x \<cdot> \<sigma>' = \<delta> x"
            proof (cases "x \<in> set xs")
              case True
              then obtain i where x: "x = xs ! i" and i: "i < length xs" unfolding set_conv_nth by auto
              have "\<sigma> x = ls' ! i" using arg_cong[OF ls, of "\<lambda> xs. xs ! i"] x i by auto
              with i len have mem: "\<sigma> x \<in> set ls'" by auto
              show ?thesis unfolding delta_sigma[OF True]
                by (rule conv1[symmetric], insert mem, auto)
            next
              case False
              from mk_subst_not_mem[OF this]
              have "\<sigma> x = Var x" unfolding \<sigma>_def . 
              then have "\<sigma> x \<cdot> \<sigma>' = \<sigma>' x" by simp
              also have "... = \<delta> x" unfolding \<sigma>'_def using x by simp
              finally show ?thesis by simp
            qed
            then show "\<delta> x = (\<sigma> \<circ>\<^sub>s \<sigma>') x" unfolding subst_compose_def by auto
          qed
          define \<delta>' where "\<delta>' = (\<lambda> x. if x \<in> vars_term (Fun f ls') then (\<sigma> \<circ>\<^sub>s \<sigma>') x else \<delta> x)"
          have delta': "\<delta>' = \<sigma> \<circ>\<^sub>s \<sigma>'" unfolding \<delta>'_def using delta_sigma' by auto
          {
            fix c :: "('f,'v)cond_constraint"
            assume "vars_cc c \<subseteq> vars_cc ?\<phi>"
            with vars_cc have disj: "vars_cc c \<inter> vars_term (Fun f ls') = {}" unfolding vars_rule_def by auto
            have "\<delta> \<Turnstile> c = \<delta>' \<Turnstile> c"
              by (rule cc_models_vars, insert disj \<delta>'_def, auto)
          } note delta_switch = this
          from delta_switch phi have phi: "Ball (set \<phi>) (cc_models \<delta>')" unfolding \<phi> by auto
          {
            fix x
            have "funas_term (\<sigma>' x) \<subseteq> F \<and> \<sigma>' x \<in> NF_trs R"
            proof (cases "x \<in> vars_term (Fun f ls')")
              case True
              then have sigma': "\<sigma>' x = \<sigma>'' x" unfolding \<sigma>'_def by simp
              from True obtain l where l: "l \<in> set ls'" and x: "x \<in> vars_term l" by auto
              from l[unfolded set_conv_nth] obtain i where i: "i < length ls'" and l: "l = ls' ! i" by auto
              from arg_cong[OF id, of "\<lambda> ls. ls ! i"] i len l have "l \<cdot> \<sigma>'' = \<delta> (xs ! i)" by auto
              with delta[unfolded normal_F_subst_def] have F: "funas_term (l \<cdot> \<sigma>'') \<subseteq> F" and NF: "l \<cdot> \<sigma>'' \<in> NF_trs R" by auto
              with l x have F: "funas_term (\<sigma>' x) \<subseteq> F" unfolding sigma' funas_term_subst by auto
              from x have "l \<unrhd> Var x" by auto
              then have "l \<cdot> \<sigma>'' \<unrhd> Var x \<cdot> \<sigma>''" by auto
              from NF_subterm[OF NF this] F
              show ?thesis unfolding sigma' by auto
            next
              case False
              then have "\<sigma>' x = \<delta> x" unfolding \<sigma>'_def by simp
              then show ?thesis using delta unfolding normal_F_subst_def by auto
            qed
          }
          then have sigmaF: "normal_F_subst \<sigma>'" unfolding normal_F_subst_def by auto
          have q: "q \<cdot> \<delta> = q \<cdot> \<delta>'"
            by (rule term_subst_eq, unfold \<delta>'_def, insert vars_cc, auto simp: vars_rule_def cc \<phi>)
          have u: "u = r' \<cdot> \<sigma>'" unfolding u
          proof (rule term_subst_eq)
            fix x
            assume "x \<in> vars_term r'"
            with vars have "x \<in> vars_term (Fun f ls')" by auto
            then show "\<sigma>'' x = \<sigma>' x" unfolding \<sigma>'_def by auto
          qed
          have sigma'_rewr: "\<sigma>' \<Turnstile> CC_rewr r' (q \<cdot> \<sigma>)" 
            unfolding cc_models.simps using steps_UR[OF steps] nf_q SN_u unfolding q delta' u by auto
          from cc_validE[OF _ sigmaF] c_cs induction(8) have sigma'_c: "\<sigma>' \<Turnstile> c" by auto        
          define vs where "vs = range_vars_impl (zip xs ls')"
          have "range_vars \<sigma> \<subseteq> set vs" unfolding vs_def \<sigma>_def by simp
          note cc_sigma = cc_models_subst[OF this]
          note c = c[unfolded cc_rule_constraint_def Let_def \<sigma>_def[symmetric] vs_def[symmetric]]
          (* it remains to show that all generated induction hypothesis are valid (by using our induction on SNrel) *)
          have "Ball (set (cc_ih_prems f q xs \<phi> \<psi> rs_ys_list)) (cc_models \<sigma>')" unfolding cc_models.simps
          proof
            fix c
            assume "c \<in> set (cc_ih_prems f q xs \<phi> \<psi> rs_ys_list)"
            note c = this[unfolded cc_ih_prems_def Let_def]
            from c obtain rr ys where c: "c =  cc_bound ys
                            (CC_impl (CC_rewr rr (q \<cdot> mk_subst Var (zip xs (args rr))) #
                                               map (\<lambda>c. c \<cdot>\<^sub>cc (mk_subst Var (zip xs (args rr)), range_vars_impl (zip xs (args rr)))) \<phi>)
                              (\<psi> \<cdot>\<^sub>cc (mk_subst Var (zip xs (args rr)), range_vars_impl (zip xs (args rr)))))" and mem: "(rr,ys) \<in> set rs_ys_list" by force
            from mem pre obtain rs where rr: "rr = Fun f rs" "args rr = rs" by (cases rr, auto)
            note c = c[unfolded rr]
            from mem pre rr have
              lenrs: "length rs = length xs" and subt: "r' \<unrhd> Fun f rs" and rvars: "vars_term r' \<inter> set ys = {}" 
                and ndef: "\<forall> fn \<in> funas_args_term (Fun f rs). \<not> defined R fn" by auto
            from supteq_imp_vars_term_subset[OF subt] rvars have rs_vars: "vars_term (Fun f rs) \<inter> set ys = {}" by auto
            define vs' where "vs' = range_vars_impl (zip xs rs)"
            define \<mu> where "\<mu> = mk_subst Var (zip xs rs)"
            from c vs'_def \<mu>_def
            have c: "c = cc_bound ys (CC_impl (CC_rewr (Fun f rs) (q \<cdot> \<mu>) # map (\<lambda>c. c \<cdot>\<^sub>cc (\<mu>, vs')) \<phi>) (\<psi> \<cdot>\<^sub>cc (\<mu>, vs')))" by simp
            have "rs = map id rs" by simp
            also have "... = map \<mu> xs"
            proof (rule nth_map_conv[OF lenrs], intro allI impI)
              fix i
              assume i: "i < length rs"
              have "rs ! i = \<mu> (xs ! i)" unfolding \<mu>_def using mk_subst_distinct[OF distinct i[unfolded lenrs] i]
                by simp
              then show "id (rs ! i) = \<mu> (xs ! i)" by simp
            qed
            finally have "rs = map \<mu> xs" .
            then have rsmu: "Fun f rs = Fun f ?xs \<cdot> \<mu>" by simp
            have rs_mu: "cc_bound ys (CC_impl (CC_rewr (Fun f rs) (q \<cdot> \<mu>) # map (\<lambda>c. c \<cdot>\<^sub>cc (\<mu>, vs')) \<phi>) (\<psi> \<cdot>\<^sub>cc (\<mu>, vs')))
              = cc_bound ys ((CC_impl (CC_rewr (Fun f ?xs) q # \<phi>) \<psi>) \<cdot>\<^sub>cc (\<mu>,vs'))" unfolding rsmu by simp
            have "\<sigma>' \<Turnstile> cc_bound ys (CC_impl (CC_rewr (Fun f rs) (q \<cdot> \<mu>) # map (\<lambda>c. c \<cdot>\<^sub>cc (\<mu>, vs')) \<phi>) (\<psi> \<cdot>\<^sub>cc (\<mu>, vs')))" unfolding rs_mu
            proof (rule cc_models_boundI)
              fix \<tau>
              assume tau_sigma: "\<And>x. x \<notin> set ys \<Longrightarrow> \<tau> x = \<sigma>' x"
                and tau: "\<And>x. x \<in> set ys \<Longrightarrow> funas_term (\<tau> x) \<subseteq> F \<and> \<tau> x \<in> NF_trs R"
              {
                fix x
                have "funas_term (\<tau> x) \<subseteq> F \<and> \<tau> x \<in> NF_trs R"
                using tau_sigma[of x] tau[of x] sigmaF[unfolded normal_F_subst_def]
                  by (cases "x \<in> set ys", force+)
              } note tauF = this
              then have tau_F: "normal_F_subst \<tau>" unfolding normal_F_subst_def by auto
              have vs': "range_vars \<mu> \<subseteq> set vs'" unfolding vs'_def \<mu>_def by auto
              show "\<tau> \<Turnstile> (CC_impl (CC_rewr (Fun f ?xs) q # \<phi>) \<psi>) \<cdot>\<^sub>cc (\<mu>, vs')" 
                unfolding cc_models_subst[OF vs']
              proof (rule IH) (* this follows by induction *)
                {
                  fix x
                  let ?x = "\<mu> x \<cdot> \<tau>"
                  have "funas_term ?x \<subseteq> F \<and> ?x \<in> NF_trs R"
                  proof (cases "x \<in> set xs")
                    case False
                    from mk_subst_not_mem[OF this]
                    have "\<mu> x = Var x" unfolding \<mu>_def .
                    with tauF[of x] show ?thesis by simp
                  next
                    case True
                    then obtain i where i: "i < length xs" and x: "x = xs ! i" unfolding set_conv_nth by auto
                    from mk_subst_distinct[OF distinct i i[unfolded lenrs[symmetric]]]
                    have "\<mu> x = rs ! i" unfolding \<mu>_def x .
                    with i lenrs have mu: "\<mu> x \<in> set rs" by auto
                    from eq_rule_mod_varsE[OF eq] obtain \<gamma> where r: "r = r' \<cdot> \<gamma>" by auto
                    have "funas_term (\<mu> x) \<subseteq> funas_term (Fun f rs)" using mu by auto
                    also have "\<dots> \<subseteq> funas_term r'" using subt by fastforce
                    also have "\<dots> \<subseteq> funas_term r" unfolding r funas_term_subst by auto
                    also have "\<dots> \<subseteq> F"
                      using lr RF unfolding funas_trs_def funas_rule_def [abs_def] by force
                    finally have F: "funas_term ?x \<subseteq> F" using tauF unfolding funas_term_subst by auto
                    have "(?x \<in> NF_trs R) = (?x \<in> NF (qrstep nfs {} R))" by simp
                    also have "\<dots>"
                      by (rule NF_subst_qrstep[OF _ _ Rfun], insert tauF ndef mu, 
                        auto simp: applicable_rules_def applicable_rule_def funas_args_term_def)
                    finally show ?thesis using F by auto
                  qed
                }
                then show "normal_F_subst (\<mu> \<circ>\<^sub>s \<tau>)" unfolding subst_compose_def normal_F_subst_def by auto
                have "(Fun f ?xs \<cdot> \<delta>, u) \<in> qrstep nfs Q R" using step_UR[OF step] .
                also have "u = r' \<cdot> \<sigma>'" unfolding u ..
                finally have step: "(Fun f ?xs \<cdot> \<delta>, Fun f rs \<cdot> \<sigma>') \<in> qrstep nfs Q R O {\<unrhd>}" using supteq_subst[OF subt] by auto
                have "Fun f rs \<cdot> \<sigma>' = Fun f rs \<cdot> \<tau>"
                  by (rule term_subst_eq[OF tau_sigma[symmetric]], insert rs_vars, auto)
                also have "Fun f rs \<cdot> \<tau> = Fun f ?xs \<cdot> \<mu> \<cdot> \<tau>" unfolding rsmu by simp
                finally have id: "Fun f rs \<cdot> \<sigma>' = Fun f ?xs \<cdot> \<mu> \<circ>\<^sub>s \<tau>" by simp
                from step id have stepi: "(Fun f ?xs \<cdot> \<delta>, Fun f ?xs \<cdot> \<mu> \<circ>\<^sub>s \<tau>) \<in> qrstep nfs Q R O {\<unrhd>}" by simp
                (* to show that \<delta> is larger than \<mu>\<tau>, we distinguish between both cases (minimality / CR) *)
                show "(\<delta>, \<mu> \<circ>\<^sub>s \<tau>) \<in> SNrel"
                proof (cases m)
                  case True
                  with SN have "SN_on (qrstep nfs Q R) {Fun f ?xs \<cdot> \<delta>}" unfolding m_SN_def by auto
                  then have "(\<delta>, \<mu> \<circ>\<^sub>s \<tau>) \<in> SNrel1" using stepi unfolding SNrel1_def inv_image_def restrict_SN_def by force
                  then show ?thesis using True unfolding SNrel_def by auto
                next
                  case False
                  with dist have dist: "dist (Fun f ?xs \<cdot> \<delta>) = Suc d" and SNrel: "SNrel = SNrel2" unfolding SNrel_def by auto
                  from steps_d[unfolded u] have steps_d: "(r' \<cdot> \<sigma>', q \<cdot> \<delta>) \<in> qrstep nfs Q ?UR ^^ d" .
                  have "dist (Fun f ?xs \<cdot> \<mu> \<circ>\<^sub>s \<tau>) = dist (Fun f rs \<cdot> \<sigma>')" unfolding id by simp
                  also have "\<dots> \<le> dist (r' \<cdot> \<sigma>')" unfolding dist_def
                    by (rule distance_subterm[OF nf_q steps[unfolded u] supteq_subst[OF subt]]) 
                  also have "\<dots> \<le> d" unfolding dist_def
                    by (rule distance_least[OF nf_q steps_d])
                  also have "\<dots> < dist (Fun f ?xs \<cdot> \<delta>)" unfolding dist by simp
                  finally have dist: "dist (Fun f ?xs \<cdot> \<mu> \<circ>\<^sub>s \<tau>) < dist (Fun f ?xs \<cdot> \<delta>)" .
                  show ?thesis unfolding SNrel SNrel2_def inv_image_def 
                    by (rule, unfold split, rule, unfold split, rule dist)
                qed
              qed
            qed
            then show "\<sigma>' \<Turnstile> c" unfolding c .
          qed
          with sigma'_rewr cc_implies_substE[OF c sigma'_c]
          have sigma'_impl: "\<sigma>' \<Turnstile> (CC_impl \<phi> \<psi>) \<cdot>\<^sub>cc (\<sigma>,vs)" by auto
          from sigma'_impl[unfolded cc_sigma] 
          have "\<delta>' \<Turnstile> CC_impl \<phi> \<psi>" unfolding delta' by auto
          with phi have "\<delta>' \<Turnstile> \<psi>" by auto
          with delta_switch[of \<psi>] show "\<delta> \<Turnstile> \<psi>" by simp
        qed
      qed
      then have "\<delta> \<Turnstile> CC_impl \<phi>' \<psi>" using induction(3-4) by auto
    }
    then show ?case unfolding cc_valid_def normalize_cc[of _ cc] cc by auto
  qed
qed
end

end
