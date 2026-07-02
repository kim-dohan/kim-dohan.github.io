(*
Author:  Akihisa Yamada (2018)
License: LGPL (see file COPYING.LESSER)
*)
theory F_Algebra
  imports First_Order_Terms.Term_More
begin

section \<open>F-Algebras\<close>

locale algebra = fixes I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
begin

fun eval :: "('f,'v) term \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "eval (Var x) \<alpha> = \<alpha> x"
      | "eval (Fun f ss) \<alpha> = I f (map (\<lambda>s. eval s \<alpha>) ss)"

notation eval ("\<lbrakk>(_)\<rbrakk>")

lemma eval_same_vars[intro]: "(\<And>x. x \<in> vars_term t \<Longrightarrow> \<alpha> x = \<beta> x) \<Longrightarrow> \<lbrakk>t\<rbrakk> \<alpha> = \<lbrakk>t\<rbrakk> \<beta>"
  by(induct t, auto intro!:map_cong[OF refl] cong[of "I _"])

lemma subset_range_eval: "range \<alpha> \<subseteq> range (\<lambda>s. \<lbrakk>s\<rbrakk>\<alpha>)" (is "?l \<subseteq> ?r")
proof
  fix a assume "a \<in> ?l"
  then obtain v where "\<alpha> v = a" by auto
  then show "a \<in> ?r" by (auto intro!: range_eqI[of _ _ "Var v"])
qed

definition constant_at where "constant_at f n i \<equiv>
  \<forall>as b. i < n \<longrightarrow> length as = n \<longrightarrow> I f (as[i:=b]) = I f as"

lemma constant_atI:
  assumes "\<And>as b. i < n \<Longrightarrow> length as = n \<Longrightarrow> I f (as[i:=b]) = I f as"
  shows "constant_at f n i" using assms by (auto simp: constant_at_def)

lemma constant_atD:
  "constant_at f n i \<Longrightarrow> length as = n \<Longrightarrow> I f (as[i:=b]) = I f as"
  by (auto simp: constant_at_def)

definition "constant_term_on s x \<equiv> \<forall>\<alpha> a. \<lbrakk>s\<rbrakk>(\<alpha>(x:=a)) = \<lbrakk>s\<rbrakk>\<alpha>"

lemma constant_term_onI: assumes "\<And>\<alpha> a. \<lbrakk>s\<rbrakk>(\<alpha>(x:=a)) = \<lbrakk>s\<rbrakk>\<alpha>" shows "constant_term_on s x"
  using assms by (auto simp: constant_term_on_def)

lemma constant_term_onD:
  assumes "constant_term_on s x" shows "\<lbrakk>s\<rbrakk>(\<alpha>(x:=a)) = \<lbrakk>s\<rbrakk>\<alpha>"
  using assms by (auto simp: constant_term_on_def)

lemma constant_term_onE:
  assumes "constant_term_on s x" and "(\<And>\<alpha> a. \<lbrakk>s\<rbrakk>(\<alpha>(x:=a)) = \<lbrakk>s\<rbrakk>\<alpha>) \<Longrightarrow> thesis"
  shows thesis using assms by (auto simp: constant_term_on_def)

lemma constant_term_on_extra_var: "x \<notin> vars_term s \<Longrightarrow> constant_term_on s x"
  by (auto intro!: constant_term_onI)

lemma constant_term_on_eq:
  assumes "\<lbrakk>s\<rbrakk> = \<lbrakk>t\<rbrakk>" and "constant_term_on s x" shows "constant_term_on t x"
  using assms by (simp add: constant_term_on_def)

definition "constant_term s \<equiv> \<forall>x. constant_term_on s x"

lemma constant_termI: assumes "\<And>x. constant_term_on s x" shows "constant_term s"
  using assms by (auto simp: constant_term_def)

lemma ground_imp_constant: "ground s \<Longrightarrow> constant_term s"
  by (auto intro!: constant_termI constant_term_on_extra_var simp: ground_vars_term_empty)

end

declare algebra.eval.simps[code,simp]

lemma eval_map_term:
  "algebra.eval I (map_term ff fv t) \<alpha> = algebra.eval (I \<circ> ff) t (\<alpha> \<circ> fv)"
  by (induct t, auto intro: cong[of "I _"])

text \<open>In the term algebra, evaluation is substitution.\<close>

interpretation term_algebra: algebra Fun
  rewrites term_algebra_eval: "term_algebra.eval = (\<cdot>)"
proof (intro ext)
  show "algebra.eval Fun s \<sigma> = s\<cdot>\<sigma>" for s \<sigma> by (induct s, unfold algebra.eval.simps, auto)
qed

subsection \<open>Homomorphism\<close>

locale algebra_hom = source: algebra I + target: algebra I'
  for hom :: "'a \<Rightarrow> 'b" and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" and I' :: "'f \<Rightarrow> 'b list \<Rightarrow> 'b" +
  assumes hom: "\<And>f as. hom (I f as) = I' f (map hom as)"
begin

lemma hom_eval: "hom (source.eval s \<alpha>) = target.eval s (\<lambda>x. hom (\<alpha> x))"
  by (induct s, auto simp: hom intro: arg_cong[OF list.map_cong0])

end

context algebra begin

text \<open>Evaluation is a homomophism from the term algebra.\<close>

sublocale eval_hom: algebra_hom "(\<lambda>s. \<lbrakk>s\<rbrakk>\<alpha>)" Fun I
  rewrites "algebra.eval Fun = (\<cdot>)"
  by (unfold_locales, auto simp: term_algebra_eval)

lemmas subst_eval = eval_hom.hom_eval

end

(* a.k.a. subst_subst *)
thm term_algebra.subst_eval[folded subst_compose_def]

locale algebra_epim = algebra_hom +
  assumes surj: "surj hom"

text \<open>An algebra where every element has a representation:\<close>
locale algebra_constant = algebra I
  for I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
  and const :: "'a \<Rightarrow> ('f,'v) term" +
  assumes vars_term_const[simp]: "\<And>d. vars_term (const d) = {}"
      and eval_const[simp]: "\<And>d \<alpha>. \<lbrakk>const d\<rbrakk> \<alpha> = d"

text \<open>
 Here we ``encode'' an $F$-algebra into a $G$-algebra, where $G$ is supposed to be established
 small signature like the semiring signature.
 Each function symbol $f \in F$ of arity $n$ is encoded as a term in $T(G,{0..<n})$.
\<close>

subsubsection \<open>Syntactic Encodings\<close>

locale pre_encoding =
  fixes E :: "'f \<Rightarrow> nat \<Rightarrow> ('g, nat) term"
begin

text \<open>These "pre" locales are needed only for (unconditional) cord equations.\<close>

abbreviation(input) I where "I f ss \<equiv> E f (length ss) \<cdot> (nth ss)"

sublocale algebra I.

end

locale pre_encoded_algebra = target: algebra I + encoder: pre_encoding E
  for I :: "'g \<Rightarrow> 'a list \<Rightarrow> 'a"
  and E :: "'f \<Rightarrow> nat \<Rightarrow> ('g, nat) term"
begin

abbreviation encode :: "('f,'v) term \<Rightarrow> ('g,'v) term" where "encode s \<equiv> encoder.eval s Var"

abbreviation IE :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" where "IE f vs \<equiv> target.eval (E f (length vs)) (nth vs)"

sublocale algebra IE.

lemma constant_at_via_encoding:
  assumes "target.constant_term_on (E f n) i"
  shows "constant_at f n i"
proof (intro constant_atI)
  fix as :: "'a list" and b
  assume 1: "i < n" and 2: "length as = n"
  then have [simp]: "(!) (as [i := b]) = (\<lambda>j. if i = j then b else as ! j)" by auto
  from target.constant_term_onD[OF assms, of "\<lambda>j. as ! j" b, symmetric]
  show "target.eval (E f (length (as[i := b]))) ((!) (as[i := b])) =
    target.eval (E f (length as)) ((!) as)" by (auto simp: fun_upd_def 2)
qed

definition "constant_positions f n \<equiv> [i \<leftarrow> [0..<n]. i \<notin> vars_term (E f n)]"

lemma constant_positions: "i \<in> set (constant_positions f n) \<Longrightarrow> constant_at f n i"
  apply (rule constant_at_via_encoding)
  apply (rule target.constant_term_on_extra_var)
  by (auto simp: constant_positions_def)

end

subsubsection \<open>Well-Formed Encodings\<close>

locale encoding = pre_encoding +
  assumes var_domain: "i \<in> vars_term (E f n) \<Longrightarrow> i < n"

locale encoded_algebra = pre_encoded_algebra + encoder: encoding
begin

sublocale algebra_hom "\<lambda>t. target.eval t \<alpha>" "encoder.I" IE
  apply unfold_locales
  by (auto simp: target.eval_hom.hom_eval encoder.var_domain)

lemma eval_via_encoding [simp]: "target.eval (encode s) = \<lbrakk>s\<rbrakk>"
  by (intro ext, induct s, auto simp: target.eval_hom.hom_eval encoder.var_domain)

end


end
