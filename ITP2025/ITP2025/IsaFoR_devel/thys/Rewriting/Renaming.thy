(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014-2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Permutations\<close>

theory Renaming
imports
  "HOL-Library.Infinite_Set"
  Fresh_Identifiers.Fresh (* for type class infinite *)
  First_Order_Rewriting.FOR_Preliminaries
begin

text \<open>This theory is mainly ported from HOL-Nominal2, but using locales instead
of type classes. The intention is to leave the type of atoms arbitrary (such
that it can later be used with polymorphic first-order terms.\<close>

text \<open>The set of all permutations of a given type.\<close>
definition perms :: "('a \<Rightarrow> 'a) set"
where
  "perms = {f. bij f \<and> finite {x. f x \<noteq> x}}"

typedef 'a perm = "perms :: ('a \<Rightarrow> 'a) set"
  by standard (auto simp: perms_def)

lemma permsI [Pure.intro]:
  assumes "bij f" and "MOST x. f x = x"
  shows "f \<in> perms"
  using assms by (auto simp: perms_def) (metis MOST_iff_finiteNeg)

lemma perms_imp_bij:
  "f \<in> perms \<Longrightarrow> bij f"
  by (simp add: perms_def)

lemma perms_imp_finite_domain:
  "f \<in> perms \<Longrightarrow> finite {x. f x \<noteq> x}"
  by (simp add: perms_def)

lemma perms_imp_MOST_eq:
  "f \<in> perms \<Longrightarrow> MOST x. f x = x"
  by (simp add: perms_def) (metis MOST_iff_finiteNeg)

lemma id_perms [simp]:
  "id \<in> perms"
  "(\<lambda>x. x) \<in> perms"
  by (auto simp: perms_def bij_def)

lemma perms_comp [simp]:
  assumes "f \<in> perms" and "g \<in> perms"
  shows "(f \<circ> g) \<in> perms"
  using assms
  by (force intro: permsI bij_comp elim: perms_imp_bij MOST_rev_mp [OF perms_imp_MOST_eq])

lemma perms_inv:
  assumes "f \<in> perms"
  shows "inv f \<in> perms"
  using assms
  by (force intro: permsI bij_imp_bij_inv MOST_mono [OF perms_imp_MOST_eq]
            dest: perms_imp_bij
            simp: bij_def inv_f_eq)

lemma bij_Rep_perm:
  "bij (Rep_perm p)"
  using Rep_perm [of p] by (simp add: perms_def)

lemma finite_Rep_perm:
  "finite {x. Rep_perm p x \<noteq> x}"
  using Rep_perm [of p] by (simp add: perms_def)

lemma Rep_perm_ext:
  "Rep_perm p1 = Rep_perm p2 \<Longrightarrow> p1 = p2"
  by (simp add: fun_eq_iff Rep_perm_inject [symmetric])

instance perm :: (type) size ..

instantiation perm :: (type) group_add
begin

definition "0 = Abs_perm id"
definition "- p = Abs_perm (inv (Rep_perm p))"
definition "p + q = Abs_perm (Rep_perm p \<circ> Rep_perm q)"
definition "(p1::'a perm) - p2 = p1 + - p2"

lemma Rep_perm_0: "Rep_perm 0 = id"
  unfolding zero_perm_def by (simp add: Abs_perm_inverse)

lemma Rep_perm_add:
  "Rep_perm (p1 + p2) = Rep_perm p1 \<circ> Rep_perm p2"
  unfolding plus_perm_def by (simp add: Abs_perm_inverse Rep_perm)

lemma Rep_perm_uminus:
  "Rep_perm (- p) = inv (Rep_perm p)"
  unfolding uminus_perm_def by (simp add: Abs_perm_inverse perms_inv Rep_perm)

instance
  by standard
     (simp_all add: Rep_perm_inject [symmetric] minus_perm_def Rep_perm_add Rep_perm_uminus
                    Rep_perm_0 o_assoc inv_o_cancel [OF bij_is_inj [OF bij_Rep_perm]])

end

definition swap :: "'a \<Rightarrow> 'a \<Rightarrow> 'a perm" ("'(_ \<rightleftharpoons> _')")
where
  "(x \<rightleftharpoons> y) = Abs_perm (\<lambda>z. if z = x then y else if z = y then x else z)"

lemma Rep_perm_swap:
  "Rep_perm (x \<rightleftharpoons> y) = (\<lambda>z. if z = x then y else if z = y then x else z)"
  by (auto intro!: Abs_perm_inverse permsI simp: bij_def MOST_eq_imp inj_on_def MOST_conj_distrib swap_def)

lemmas Rep_perm_simps =
  Rep_perm_0
  Rep_perm_add
  Rep_perm_uminus
  Rep_perm_swap

lemma swap_cancel:
  "(x \<rightleftharpoons> y) + (x \<rightleftharpoons> y) = 0"
  "(x \<rightleftharpoons> y) + (y \<rightleftharpoons> x) = 0"
  apply (atomize(full))
  apply (intro conjI; rule Rep_perm_ext)
  by (auto simp: Rep_perm_simps fun_eq_iff)


lemma swap_self [simp]:
  "(x \<rightleftharpoons> x) = 0"
  by (rule Rep_perm_ext, simp add: Rep_perm_simps fun_eq_iff)

lemma minus_swap [simp]:
  "- (a \<rightleftharpoons> b) = (a \<rightleftharpoons> b)"
  by (rule minus_unique [OF swap_cancel(1)])

lemma swap_commute:
  "(a \<rightleftharpoons> b) = (b \<rightleftharpoons> a)"
  by (rule Rep_perm_ext)
     (simp add: Rep_perm_swap fun_eq_iff)

lemma swap_triple:
  assumes "a \<noteq> b" and "c \<noteq> b"
  shows "(a \<rightleftharpoons> c) + (b \<rightleftharpoons> c) + (a \<rightleftharpoons> c) = (a \<rightleftharpoons> b)"
  apply (rule Rep_perm_ext)
  using assms by (auto simp add: Rep_perm_simps fun_eq_iff)


section \<open>Permutation Types\<close>

ML \<open>
structure Equivariance = Named_Thms (
  val name = @{binding "eqvt"}
  val description = "equivariance rules"
)
\<close>

setup Equivariance.setup

text \<open>Infix syntax for @{text PERMUTE} has higher precedence than
addition, but lower than unary minus.\<close>

consts PERMUTE :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b" (infixr "\<bullet>" 75)

locale permutation_type =
  fixes permute :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes permute_zero [simp]: "permute 0 x = x"
    and permute_plus [simp]: "permute (p + q) x = permute p (permute q x)"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute

text \<open>Equivariance.\<close>

definition eqvt :: "'b \<Rightarrow> bool"
where
  "eqvt x \<longleftrightarrow> (\<forall>p. p \<bullet> x = x)"

definition unpermute :: "'a perm \<Rightarrow> 'b \<Rightarrow> 'b"
where
  "unpermute p = permute (- p)"

definition variants :: "('b \<times> 'b) set"
where
  "variants = {(x, y). \<exists>\<pi>. \<pi> \<bullet> x = y}"

lemma permute_diff [simp]:
  shows "(p - q) \<bullet> x = p \<bullet> - q \<bullet> x"
  unfolding diff_conv_add_uminus permute_plus by simp

lemma permute_minus_cancel [simp]:
  shows "p \<bullet> - p \<bullet> x = x"
    and "- p \<bullet> p \<bullet> x = x"
  unfolding permute_plus [symmetric] by simp_all

lemma permute_swap_cancel [simp]:
  shows "(a \<rightleftharpoons> b) \<bullet> (a \<rightleftharpoons> b) \<bullet> x = x"
  unfolding permute_plus [symmetric]
  by (simp add: swap_cancel)

lemma permute_swap_cancel2 [simp]:
  shows "(a \<rightleftharpoons> b) \<bullet> (b \<rightleftharpoons> a) \<bullet> x = x"
  unfolding permute_plus [symmetric]
  by (simp add: swap_commute)

lemma inj_permute [simp]: 
  shows "inj ((\<bullet>) p)"
  by (rule inj_on_inverseI) (rule permute_minus_cancel)

lemma surj_permute [simp]: 
  shows "surj ((\<bullet>) p)"
  by (rule surjI) (rule permute_minus_cancel)

lemma bij_permute [simp]: 
  shows "bij ((\<bullet>) p)"
  by (rule bijI [OF inj_permute surj_permute])

lemma inv_permute: 
  shows "inv ((\<bullet>) p) = (\<bullet>) (- p)"
  by (rule inv_equality) (simp_all)

lemma permute_minus: 
  shows "(\<bullet>) (- p) = inv ((\<bullet>) p)"
  by (simp add: inv_permute)

lemma permute_eq_iff [simp]: 
  shows "p \<bullet> x = p \<bullet> y \<longleftrightarrow> x = y"
  by (rule inj_permute [THEN inj_eq])

lemma variants_refl:
  "(x, x) \<in> variants"
proof -
  have "0 \<bullet> x = x" by simp
  then have "\<exists>\<pi>. \<pi> \<bullet> x = x" ..
  then show ?thesis by (auto simp: variants_def)
qed

lemma variants_sym:
  assumes "(x, y) \<in> variants"
  shows "(y, x) \<in> variants"
proof -
  from assms obtain \<pi> where "y = \<pi> \<bullet> x" by (auto simp: variants_def)
  then have "-\<pi> \<bullet> y = x" by simp
  then show ?thesis by (auto simp: variants_def)
qed

lemma variants_trans:
  assumes "(x, y) \<in> variants" and "(y, z) \<in> variants"
  shows "(x, z) \<in> variants"
proof -
  from assms obtain \<pi>\<^sub>1 and \<pi>\<^sub>2
    where "y = \<pi>\<^sub>1 \<bullet> x" and "z = \<pi>\<^sub>2 \<bullet> y" by (auto simp: variants_def)
  then have "(\<pi>\<^sub>2 + \<pi>\<^sub>1) \<bullet> x = z" by simp
  then have "\<exists>\<pi>. \<pi> \<bullet> x = z" ..
  then show ?thesis by (auto simp: variants_def)
qed

lemma variants_equiv_on_TRS:
  "equiv R (variants \<inter> R \<times> R)"
  by (rule equivI)
     (auto simp: refl_on_def sym_def trans_def variants_refl dest: variants_sym variants_trans)

lemma variants_TRS:
  "equiv UNIV variants"
  by (rule equivI)
     (auto simp: refl_on_def sym_def trans_def variants_refl dest: variants_sym variants_trans)

lemma permute_flip: "x = \<pi> \<bullet> y \<Longrightarrow> y = -\<pi> \<bullet> x" by auto

end

definition permute_atom :: "'a perm \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "permute_atom p a = (Rep_perm p) a"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_atom

interpretation atom_pt: permutation_type permute_atom
  by standard (simp add: permute_atom_def Rep_perm_simps)+

lemma swap_atom:
  "(a \<rightleftharpoons> b) \<bullet> c = (if c = a then b else if c = b then a else c)"
  by (simp add: permute_atom_def Rep_perm_swap)

lemma swap_atom_simps [simp]:
  "(a \<rightleftharpoons> b) \<bullet> a = b"
  "(a \<rightleftharpoons> b) \<bullet> b = a"
  "c \<noteq> a \<Longrightarrow> c \<noteq> b \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> c = c"
  by (simp_all add: swap_atom)

lemma perm_eq_iff:
  shows "p = q \<longleftrightarrow> (\<forall>a. p \<bullet> a = q \<bullet> a)"
  unfolding permute_atom_def
  by (metis Rep_perm_ext ext)

definition permute_perm :: "'a perm \<Rightarrow> 'a perm \<Rightarrow> 'a perm"
where
  "permute_perm p q = p + q + - p"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_perm

interpretation perm_pt: permutation_type permute_perm
  by standard
    (simp_all add: permute_perm_def minus_add, simp only: diff_conv_add_uminus add.assoc)

lemma permute_self: 
  shows "p \<bullet> p = p"
  by (simp add: permute_perm_def add.assoc)

lemma pemute_minus_self:
  shows "(-p) \<bullet> p = p"
  by (simp add: add.assoc permute_perm_def)

lemma (in permutation_type) permute_eqvt:
  fixes x :: "'b"
  shows "p \<bullet> (q \<bullet> x) = (p \<bullet> q) \<bullet> (p \<bullet> x)"
  by (simp add: permute_perm_def)

lemma zero_perm_eqvt [eqvt]:
  shows "p \<bullet> (0 :: ('a :: infinite) perm) = 0"
  by (simp add: permute_perm_def)

lemma add_perm_eqvt [eqvt]:
  fixes p p1 p2 :: "('a :: infinite) perm"
  shows "p \<bullet> (p1 + p2) = p \<bullet> p1 + p \<bullet> p2"
  by (simp add: permute_perm_def perm_eq_iff)

locale fun_pt =
  dom: permutation_type perm1 + ran: permutation_type perm2
  for perm1 :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
  and perm2 :: "'a perm \<Rightarrow> 'c \<Rightarrow> 'c"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> perm1 perm2

definition permute_fun :: "'a perm \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c)"
where
  "permute_fun p f = (\<lambda>x. p \<bullet> (f (-p \<bullet> x)))"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_fun

end

sublocale fun_pt \<subseteq> permutation_type permute_fun
  by standard (auto simp: permute_fun_def, metis dom.permute_plus minus_add)

(*FIXME: needed?*)
locale fun_comp_pt =
  a: fun_pt pa pb +
  b: fun_pt pb pc +
  c: fun_pt pa pc
  for pa :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
  and pb :: "'a perm \<Rightarrow> 'c \<Rightarrow> 'c"
  and pc :: "'a perm \<Rightarrow> 'd \<Rightarrow> 'd"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> pa pb pc a.permute_fun b.permute_fun c.permute_fun

lemma comp_eqvt':
  fixes g :: "'b \<Rightarrow> 'c" and f :: "'c \<Rightarrow> 'd"
  shows "p \<bullet> (\<lambda>x. f (g x)) = (\<lambda>x. (p \<bullet> f) ((p \<bullet> g) x))"
  by (simp add: a.permute_fun_def b.permute_fun_def c.permute_fun_def)

lemma comp_eqvt [eqvt]:
  fixes g :: "'b \<Rightarrow> 'c" and f :: "'c \<Rightarrow> 'd"
  shows "p \<bullet> (f \<circ> g) = (p \<bullet> f) \<circ> (p \<bullet> g)"
  by (simp add: comp_def comp_eqvt')

end

context fun_pt
begin

lemma apply_eqvt:
  fixes f :: "'b \<Rightarrow> 'c" and x :: "'b"
  shows "p \<bullet> (f x) = (p \<bullet> f) (p \<bullet> x)"
  by (simp add: permute_fun_def)

lemma lambda_eqvt:
  fixes p :: "('a::infinite) perm" and f :: "'b \<Rightarrow> 'c"
  shows "p \<bullet> f = (\<lambda>x. p \<bullet> (f (dom.unpermute p x)))"
  by (simp add: permute_fun_def dom.unpermute_def)

lemma unpermute_self:
  "p \<bullet> unpermute p x = x"
  by (simp add: unpermute_def)

lemma permute_fun_comp:
  fixes p :: "'a perm"
  shows "p \<bullet> f  = ((\<bullet>) p) o f o ((\<bullet>) (-p))"
  by (simp add: comp_def permute_fun_def)

end

definition permute_bool :: "'a perm \<Rightarrow> bool \<Rightarrow> bool" where
  "permute_bool p b = b"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_bool

interpretation bool_pt: permutation_type permute_bool
  by standard (simp add: permute_bool_def)+

lemma permute_boolE:
  fixes p :: "('a :: infinite) perm"
  shows "p \<bullet> P \<Longrightarrow> P"
  by (simp add: permute_bool_def)

lemma permute_boolI:
  fixes p :: "('a :: infinite) perm"
  shows "P \<Longrightarrow> p \<bullet> P"
  by (simp add: permute_bool_def)

lemma Not_eqvt [eqvt]:
  "p \<bullet> (\<not> A) \<longleftrightarrow> \<not> (p \<bullet> A)"
  by (simp add: permute_bool_def)

lemma conj_eqvt [eqvt]:
  "p \<bullet> (A \<and> B) \<longleftrightarrow> (p \<bullet> A) \<and> (p \<bullet> B)"
  by (simp add: permute_bool_def)

lemma imp_eqvt [eqvt]:
  "p \<bullet> (A \<longrightarrow> B) \<longleftrightarrow> (p \<bullet> A) \<longrightarrow> (p \<bullet> B)"
  by (simp add: permute_bool_def)

lemmas
  True_eqvt [eqvt] = permute_bool_def [of _ True] and
  False_eqvt [eqvt] = permute_bool_def [of _ False]

lemma disj_eqvt [eqvt]:
  "p \<bullet> (A \<or> B) \<longleftrightarrow> (p \<bullet> A) \<or> (p \<bullet> B)"
  by (simp add: permute_bool_def)

locale pred_pt =
  arg: permutation_type perm
  for perm :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
begin

definition
  permute_pred :: "('a::infinite) perm \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)"
where
  "permute_pred p P = (\<lambda>x. P (perm (-p) x))"

end

sublocale pred_pt \<subseteq> fun_pt perm permute_bool
  rewrites "permute_fun = permute_pred"
proof -
  show *: "fun_pt perm permute_bool" ..
  show "fun_pt.permute_fun perm permute_bool = permute_pred"
    unfolding fun_pt.permute_fun_def [OF *, abs_def] permute_bool_def permute_pred_def [abs_def]
    ..
qed

definition permute_atom_pred :: "('a :: infinite) perm \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "permute_atom_pred p P = (\<lambda>x. P (-p \<bullet> x))"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_atom_pred

interpretation atom_pred_pt: pred_pt permute_atom
  rewrites "pred_pt.permute_pred permute_atom = permute_atom_pred"
proof -
  show *: "pred_pt permute_atom" ..
  show "pred_pt.permute_pred permute_atom = permute_atom_pred"
    by (simp add: permute_atom_pred_def [abs_def] pred_pt.permute_pred_def [OF *, abs_def])
qed

context permutation_type
begin

interpretation pred: pred_pt permute ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> pred.permute_pred

lemma eq_eqvt [eqvt]:
  fixes x :: "'b"
  shows "p \<bullet> (x = y) \<longleftrightarrow> (p \<bullet> x) = (p \<bullet> y)"
  unfolding permute_eq_iff permute_bool_def ..

lemma all_eqvt [eqvt]:
  fixes P :: "'b \<Rightarrow> bool"
  shows "p \<bullet> (\<forall>x. P x) = (\<forall>x. (p \<bullet> P) x)"
  unfolding pred.permute_pred_def permute_bool_def
  by (metis permute_plus permute_zero right_minus)

lemma all_eqvt':
  fixes P :: "'c \<Rightarrow> bool"
  shows "p \<bullet> (\<forall>x. P x) = (\<forall>x. p \<bullet> (P x))"
  by (simp add: permute_bool_def)

lemma ball_eqvt':
  fixes P :: "'c \<Rightarrow> bool"
  shows "p \<bullet> (\<forall>x\<in>A. P x) = (\<forall>x\<in>A. p \<bullet> (P x))"
by (simp add: permute_bool_def)

lemma ex_eqvt [eqvt]:
  fixes P :: "'b \<Rightarrow> bool"
  shows "p \<bullet> (\<exists>x. P x) = (\<exists>x. (p \<bullet> P) x)"
  unfolding Ex_def pred.permute_pred_def permute_bool_def
    by (simp) (metis permute_minus_cancel(2))

lemma ex1_eqvt [eqvt]:
  fixes P :: "'b \<Rightarrow> bool"
  shows "p \<bullet> (\<exists>!x. P x) = (\<exists>!x. (p \<bullet> P) x)"
  unfolding Ex1_def pred_pt.permute_pred_def
  by (simp add: eqvt pred.permute_pred_def)
     (metis permute_minus_cancel(2))

lemma if_eqvt [eqvt]:
  fixes x :: "'b"
  shows "p \<bullet> (if b then x else y) = (if p \<bullet> b then p \<bullet> x else p \<bullet> y)"
  by (simp add: pred_pt.permute_pred_def permute_bool_def)

lemma all_eqvt2:
  fixes P :: "'b \<Rightarrow> bool"
  shows "p \<bullet> (\<forall>x. P x) = (\<forall>x. p \<bullet> P (- p \<bullet> x))"
  by (simp add: eqvt pred.permute_pred_def)
     (metis permute_bool_def)

lemma ex_eqvt2:
  fixes P :: "'b \<Rightarrow> bool"
  shows "p \<bullet> (\<exists>x. P x) = (\<exists>x. p \<bullet> P (- p \<bullet> x))"
  by (simp add: eqvt pred.permute_pred_def)
     (metis permute_bool_def)

lemma ex1_eqvt2:
  fixes P :: "'b \<Rightarrow> bool"
  shows "p \<bullet> (\<exists>!x. P x) = (\<exists>!x. p \<bullet> P (- p \<bullet> x))"
  by (simp add: eqvt pred.permute_pred_def)
     (metis permute_bool_def)

end

locale set_pt =
  elt: permutation_type perm for perm :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> perm

definition permute_set :: "'a perm \<Rightarrow> 'b set \<Rightarrow> 'b set"
where
 "permute_set p A = {p \<bullet> x | x. x \<in> A}"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_set

lemma permute_set_subset:
  fixes \<pi> :: "('a :: infinite) perm"
    and A :: "'b set"
  assumes "A \<subseteq> B"
  shows "\<pi> \<bullet> A \<subseteq> \<pi> \<bullet> B"
  using assms by (auto simp: permute_set_def)

lemma subset_imp_ex_perm:
  fixes A :: "'b set"
  assumes "A \<subseteq> B"
  shows "\<forall>x \<in> A. \<exists>p. \<exists>y \<in> B. p \<bullet> x = y"
  using assms by (auto) (metis elt.permute_zero set_rev_mp)

end

sublocale set_pt \<subseteq> permutation_type permute_set
  by standard (auto simp: permute_set_def)

context set_pt
begin

lemma permute_set_eq:
  "p \<bullet> X = {x. - p \<bullet> x \<in> X}"
  by (auto simp: permute_set_def) (metis elt.permute_minus_cancel(1))

lemma permute_set_eq_image:
  "p \<bullet> X = (\<bullet>) p ` X"
  by (auto simp: permute_set_def)

lemma permute_set_eq_vimage:
  "p \<bullet> X = (\<bullet>) (- p) -` X"
  by (simp add: permute_set_eq vimage_def)

lemma permute_finite [simp]:
  "finite (p \<bullet> X) = finite X"
  unfolding permute_set_eq_vimage
  using bij_permute by (metis elt.bij_permute finite_vimage_iff)

lemma mem_permute_iff:
  fixes p :: "'a perm"
  shows "(p \<bullet> x) \<in> (p \<bullet> X) \<longleftrightarrow> x \<in> X"
  by (auto simp: permute_set_def)

lemma inv_mem_simps [simp]:
  fixes p :: "'a perm"
  shows "(-p \<bullet> x) \<in> X \<longleftrightarrow> x \<in> (p \<bullet> X)"
    and "x \<in> (-p \<bullet> X) \<longleftrightarrow> (p \<bullet> x) \<in> X"
  by (metis permute_minus_cancel(2) mem_permute_iff)+

lemma empty_eqvt [simp]:
  "p \<bullet> {} = {}"
  by (simp add: permute_set_def)

lemma permute_set_emptyD [dest]:
  "p \<bullet> A = {} \<Longrightarrow> A = {}"
by (simp add: permute_set_def)

lemma insert_eqvt [eqvt]:
  "p \<bullet> (insert x A) = insert (p \<bullet> x) (p \<bullet> A)"
  unfolding permute_set_eq_image image_insert ..

lemma mem_eqvt [eqvt]:
  shows "p \<bullet> (x \<in> A) \<longleftrightarrow> (p \<bullet> x) \<in> (p \<bullet> A)"
  unfolding permute_bool_def permute_set_def
  by (simp add: eqvt)

interpretation elt_pred_pt: pred_pt perm ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> elt_pred_pt.permute_pred

lemma Collect_eqvt [eqvt]:
  "p \<bullet> {x. P x} = {x. (p \<bullet> P) x}"
  by (simp add: permute_set_eq elt_pred_pt.permute_pred_def)

lemma inter_eqvt [eqvt]:
  "p \<bullet> (A \<inter> B) = (p \<bullet> A) \<inter> (p \<bullet> B)"
  unfolding Int_def permute_set_eq by simp

lemma Bex_eqvt [eqvt]:
  "p \<bullet> (\<exists>x \<in> S. P x) = (\<exists>x \<in> (p \<bullet> S). (p \<bullet> P) x)"
  by (simp add: Bex_def pred_pt.permute_pred_def eqvt elt_pred_pt.permute_pred_def permute_set_def)

lemma Ball_eqvt [eqvt]:
  "p \<bullet> (\<forall>x \<in> S. P x) = (\<forall>x \<in> (p \<bullet> S). (p \<bullet> P) x)"
  by (simp add: Ball_def eqvt permute_set_def elt_pred_pt.permute_pred_def)

lemma UNIV_eqvt [eqvt]:
  "p \<bullet> UNIV = UNIV"
  unfolding UNIV_def by (auto simp add: permute_set_def) (metis elt.permute_minus_cancel(1))

lemma union_eqvt [eqvt]:
  "p \<bullet> (A \<union> B) = (p \<bullet> A) \<union> (p \<bullet> B)"
  by (auto simp: Un_def permute_set_def)

lemma Union_eqvt [eqvt]:
  "p \<bullet> \<Union>A = \<Union>((\<bullet>) p ` A)"
  by (auto simp: permute_set_def)

lemma UNION_eqvt [eqvt]:
  "p \<bullet> (\<Union> (f ` A)) = \<Union> ((\<lambda>x. p \<bullet> f x) ` A)"
by (auto simp: permute_set_def)

lemma Diff_eqvt [eqvt]:
  fixes A B :: "'b set"
  shows "p \<bullet> (A - B) = (p \<bullet> A) - (p \<bullet> B)"
  by (auto simp: set_diff_eq permute_set_def)

lemma Compl_eqvt [eqvt]:
  fixes A :: "'b set"
  shows "p \<bullet> (- A) = - (p \<bullet> A)"
  by (auto simp: permute_set_def Compl_eq_Diff_UNIV)
     (metis elt.permute_minus_cancel(1))

lemma subset_eqvt [eqvt]:
  "p \<bullet> (S \<subseteq> T) \<longleftrightarrow> (p \<bullet> S) \<subseteq> (p \<bullet> T)"
  by (simp add: subset_eq eqvt elt_pred_pt.permute_pred_def)

lemma psubset_eqvt [eqvt]:
  "p \<bullet> (S \<subset> T) \<longleftrightarrow> (p \<bullet> S) \<subset> (p \<bullet> T)"
  by (simp add: psubset_eq eqvt)

end

definition permute_atom_set :: "('a :: infinite) perm \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "permute_atom_set p A = {p \<bullet> x | x. x \<in> A}"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_atom_set

interpretation atom_set_pt: set_pt permute_atom
  rewrites "set_pt.permute_set permute_atom = permute_atom_set"
    and "pred_pt.permute_pred permute_atom = permute_atom_pred"
proof -
  show *: "set_pt permute_atom" ..
  show "set_pt.permute_set permute_atom = permute_atom_set"
    by (simp add: permute_atom_set_def [abs_def] set_pt.permute_set_def [OF *, abs_def])
  have **: "pred_pt permute_atom" ..
  show "pred_pt.permute_pred permute_atom = permute_atom_pred"
    by (simp add: permute_atom_pred_def [abs_def] pred_pt.permute_pred_def [OF **, abs_def])
qed

lemma swap_set_not_in:
  assumes "a \<notin> S" "b \<notin> S"
  shows "(a \<rightleftharpoons> b) \<bullet> S = S"
  using assms by (auto simp: permute_atom_set_def swap_atom)

lemma swap_set_in:
  assumes "a \<in> S" "b \<notin> S"
  shows "(a \<rightleftharpoons> b) \<bullet> S \<noteq> S"
  using assms by (force simp: permute_atom_set_def swap_atom)

lemma swap_set_in_eq:
  assumes "a \<in> S" "b \<notin> S"
  shows "(a \<rightleftharpoons> b) \<bullet> S = (S - {a}) \<union> {b}"
  using assms by (auto simp: permute_atom_set_def swap_atom)

lemma swap_set_both_in:
  assumes "a \<in> S" "b \<in> S"
  shows "(a \<rightleftharpoons> b) \<bullet> S = S"
  using assms by (auto simp add: permute_atom_set_def swap_atom) metis

definition permute_unit :: "'a perm \<Rightarrow> unit \<Rightarrow> unit"
where
  "permute_unit p (u :: unit) = u"

interpretation unit_pt: permutation_type permute_unit
  by standard (simp add: permute_unit_def)+

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_unit

locale prod_pt =
  fst: permutation_type perm1 + snd: permutation_type perm2
  for perm1 :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
  and perm2 :: "'a perm \<Rightarrow> 'c \<Rightarrow> 'c"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> perm1 perm2

fun permute_prod :: "'a perm \<Rightarrow> ('b \<times> 'c) \<Rightarrow> ('b \<times> 'c)"
where
  permute_prod_eqvt [eqvt]: "permute_prod p (x, y) = (p \<bullet> x, p \<bullet> y)"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_prod

declare permute_prod.simps [simp del]

end

sublocale prod_pt \<subseteq> permutation_type permute_prod
  by standard (auto simp: eqvt)

locale sum_pt =
  l: permutation_type perm1 + r: permutation_type perm2
  for perm1 :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
  and perm2 :: "'a perm \<Rightarrow> 'c \<Rightarrow> 'c"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> perm1 perm2

fun permute_sum :: "'a perm \<Rightarrow> ('b + 'c) \<Rightarrow> ('b + 'c)"
where
  "permute_sum p (Inl x) = Inl (p \<bullet> x)" |
  "permute_sum p (Inr y) = Inr (p \<bullet> y)"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_sum

end

sublocale sum_pt \<subseteq> permutation_type permute_sum
  apply unfold_locales
  subgoal for x by (cases x, auto)
  subgoal for p q x by (cases x, auto)
  done
  
locale list_pt =
  elt: permutation_type perm for perm :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> perm

definition permute_list :: "'a perm \<Rightarrow> 'b list \<Rightarrow> 'b list"
where
  [simp]: "permute_list p = map (\<lambda>x. p \<bullet> x)"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_list

lemma nth_eqvt:
  "i < length xs \<Longrightarrow> \<pi> \<bullet> (xs ! i) = (\<pi> \<bullet> xs) ! i"
  by simp

end

sublocale list_pt \<subseteq> permutation_type permute_list
  apply unfold_locales
  subgoal for x by (cases x, auto)
  subgoal for p q x by (cases x, auto)
  done

locale option_pt =
  elt: permutation_type perm for perm :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> perm

fun permute_option :: "'a perm \<Rightarrow> 'b option \<Rightarrow> 'b option"
where
  "permute_option p None = None" |
  "permute_option p (Some x) = Some (p \<bullet> x)"

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_option

end

sublocale option_pt \<subseteq> permutation_type permute_option
  apply unfold_locales
  subgoal for x by (cases x, auto)
  subgoal for p q x by (cases x, auto)
  done

locale rel_pt =
  step: prod_pt perm perm for perm :: "('a :: infinite perm) \<Rightarrow> 'b \<Rightarrow> 'b"
begin

adhoc_overloading
  PERMUTE \<rightleftharpoons> perm step.permute_prod

interpretation set_pt step.permute_prod ..

adhoc_overloading
  PERMUTE \<rightleftharpoons> permute_set

end

sublocale rel_pt \<subseteq> set_pt step.permute_prod ..

context rel_pt
begin

lemma relcomp_eqvt:
  fixes R S :: "'b rel"
  assumes "\<And>p. p \<bullet> R = R" and "\<And>p. p \<bullet> S = S"
  shows "p \<bullet> (R O S) = R O S"
proof -
  interpret step_pred: pred_pt step.permute_prod ..
  { fix a b x y z assume "-p \<bullet> (a, b) = (x, z)" and "(a, y) \<in> R" and "(y, b) \<in> S"
    moreover then have "-p \<bullet> (a, y) \<in> R"  and "-p \<bullet> (y, b) \<in> S"
      by (simp_all, auto simp: eqvt assms)
    ultimately have "(x, -p \<bullet> y) \<in> R" and "(-p \<bullet> y, z) \<in> S" by (auto simp: eqvt)
    then have "\<exists>y. (x, y) \<in> R \<and> (y, z) \<in> S" by blast }
  moreover
  { fix a b x y z assume "- p \<bullet> (a, b) = (x, z)" and "(x, y) \<in> R" and "(y, z) \<in> S"
    moreover then have "p \<bullet> (x, y) \<in> R" and "p \<bullet> (y, z) \<in> S"
      by (auto simp: inv_mem_simps [symmetric] assms)
    ultimately have "(a, p \<bullet> y) \<in> R" and "(p \<bullet> y, b) \<in> S" by (auto simp: eqvt)
    then have "\<exists>y. (a, y) \<in> R \<and> (y, b) \<in> S" by blast }
  moreover have "R O S = {(x, z). \<exists>y. (x, y) \<in> R \<and> (y, z) \<in> S}" by auto
  ultimately have "p \<bullet> (R O S) = {(x, z). \<exists>y. p \<bullet> ((x, y) \<in> R) \<and> p \<bullet> ((y, z) \<in> S)}"
    using [[show_variants]]
    by (auto simp: eqvt step_pred.permute_pred_def mem_permute_iff simp del: step.permute_prod_eqvt)
  then show ?thesis by (auto simp: permute_bool_def)
qed

end


section \<open>Pure Types\<close>

locale pure =
  permutation_type permute for permute :: "('a :: infinite) perm \<Rightarrow> 'b \<Rightarrow> 'b" +
  assumes permute_pure [simp]: "(p :: 'a perm) \<bullet> (x :: 'b) = x"

interpretation unit_pure: pure permute_unit
  by standard (simp add: permute_unit_def)

interpretation bool_pure: pure permute_bool
  by standard (simp add: permute_bool_def)

lemma (in fun_pt) eqvt_fun_iff:
  "eqvt f \<longleftrightarrow> (\<forall>(p :: 'a perm) x. p \<bullet> (f x) = f (p \<bullet> x))"
  by (auto simp add: eqvt_def permute_fun_def)
     (metis dom.unpermute_def apply_eqvt lambda_eqvt)

lemma bool_pt_eqvt [simp]:
  "bool_pt.eqvt TYPE('a :: infinite) x"
  by (simp add: bool_pt.eqvt_def permute_bool_def)

lemma swap_eqvt [eqvt]:
  fixes p :: "('a :: infinite) perm"
  shows "p \<bullet> (a \<rightleftharpoons> b) = (p \<bullet> a \<rightleftharpoons> p \<bullet> b)"
  by (auto simp add: permute_perm_def swap_atom perm_eq_iff)

consts
  FRESH :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sharp>" 55)

context permutation_type
begin

text \<open>The support of @{term x} (aka, the set of free variables, provided we have infinitely many
atoms at our disposal).\<close>
definition supp :: "'b \<Rightarrow> 'a set"
where
  "supp x = {a. infinite {b. (a \<rightleftharpoons> b) \<bullet> x \<noteq> x}}"

definition fresh :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  "fresh a x \<longleftrightarrow> a \<notin> supp x"

adhoc_overloading
  FRESH \<rightleftharpoons> fresh

definition fresh_set :: "'a set \<Rightarrow> 'b \<Rightarrow> bool"
where
  "fresh_set A x \<longleftrightarrow> (\<forall>a \<in> A. a \<sharp> x)"

adhoc_overloading
  FRESH \<rightleftharpoons> fresh_set

definition supports :: "'a set \<Rightarrow> 'b \<Rightarrow> bool"
where  
  "supports S x \<longleftrightarrow> (\<forall>a b. (a \<notin> S \<and> b \<notin> S \<longrightarrow> (a \<rightleftharpoons> b) \<bullet> x = x))"

lemma fresh_set_disjoint:
  assumes "A \<sharp> x"
  shows "A \<inter> supp x = {}"
  using assms unfolding fresh_set_def fresh_def
  by (metis disjoint_iff_not_equal)

lemma supp_is_subset:
  fixes S :: "'a set"
    and x :: "'b"
  assumes a1: "supports S x"
    and a2: "finite S"
  shows "supp x \<subseteq> S"
proof (rule ccontr)
  assume "\<not> (supp x \<subseteq> S)"
  then obtain a where b1: "a \<in> supp x" and b2: "a \<notin> S" by auto
  from a1 b2 have "\<forall>b. b \<notin> S \<longrightarrow> (a \<rightleftharpoons> b) \<bullet> x = x" unfolding supports_def by auto
  then have "{b. (a \<rightleftharpoons> b) \<bullet> x \<noteq> x} \<subseteq> S" by auto
  with a2 have "finite {b. (a \<rightleftharpoons> b) \<bullet> x \<noteq> x}" by (simp add: finite_subset)
  then have "a \<notin> (supp x)" unfolding supp_def by simp
  with b1 show False by simp
qed

lemma supp_conv_fresh: 
  "supp x = {a. \<not> a \<sharp> x}"
  by (simp add: fresh_def)

lemma swap_rel_trans:
  fixes a b c :: "'a" and x :: "'b"
  assumes "(a \<rightleftharpoons> c) \<bullet> x = x" and "(b \<rightleftharpoons> c) \<bullet> x = x"
  shows "(a \<rightleftharpoons> b) \<bullet> x = x"
proof (cases)
  assume "a = b \<or> c = b"
  with assms show "(a \<rightleftharpoons> b) \<bullet> x = x" by auto
next
  assume *: "\<not> (a = b \<or> c = b)"
  have "((a \<rightleftharpoons> c) + (b \<rightleftharpoons> c) + (a \<rightleftharpoons> c)) \<bullet> x = x"
    using assms by simp
  also have "(a \<rightleftharpoons> c) + (b \<rightleftharpoons> c) + (a \<rightleftharpoons> c) = (a \<rightleftharpoons> b)"
    using assms * by (simp add: swap_triple)
  finally show "(a \<rightleftharpoons> b) \<bullet> x = x" .
qed

lemma obtain_atom:
  fixes X :: "'a set"
  assumes X: "finite X"
  obtains a where "a \<notin> X"
proof -
  from X have "MOST a. a \<notin> X"
    unfolding MOST_iff_cofinite by simp
  then have "INFM a. a \<notin> X" using infinite_UNIV and X by (metis Collect_mem_eq INFM_iff_infinite finite_Collect_not)
  then obtain a where "a \<notin> X"
    by (auto elim: INFM_E)
  then show ?thesis ..
qed

lemma swap_fresh_fresh:
  assumes a: "a \<sharp> x" and b: "b \<sharp> x"
  shows "(a \<rightleftharpoons> b) \<bullet> x = x"
proof -
  have "finite {c. (a \<rightleftharpoons> c) \<bullet> x \<noteq> x}" "finite {c. (b \<rightleftharpoons> c) \<bullet> x \<noteq> x}" 
    using a b unfolding fresh_def supp_def by simp_all
  then have "finite ({c. (a \<rightleftharpoons> c) \<bullet> x \<noteq> x} \<union> {c. (b \<rightleftharpoons> c) \<bullet> x \<noteq> x})" by simp
  then obtain c 
    where "(a \<rightleftharpoons> c) \<bullet> x = x" "(b \<rightleftharpoons> c) \<bullet> x = x"
    by (rule obtain_atom) (auto)
  then show "(a \<rightleftharpoons> b) \<bullet> x = x" by (rule swap_rel_trans)
qed

text \<open>The notion of support does not make sense for a finite set of atoms.\<close>
lemma supp_empty:
  assumes "finite (UNIV :: 'a set)"
  shows "supp x = {}"
  using assms by (auto simp: supp_def) (metis rev_finite_subset top_greatest)

lemma fresh_ex:
  assumes "finite (supp x)"
  shows "\<exists>a::'a. a \<sharp> x"
  using ex_new_if_finite [OF infinite_UNIV assms] by (simp add: fresh_def)

lemma fresh_set_supp_conv:
  shows "supp x \<sharp> y \<Longrightarrow> supp y \<sharp> x"
  by (auto simp add: fresh_set_def fresh_def)

lemma supp_supports:
  fixes x :: "'b"
  shows "supports (supp x) x"
unfolding supports_def
proof (intro strip)
  fix a b
  assume "a \<notin> (supp x) \<and> b \<notin> (supp x)"
  then have "a \<sharp> x" and "b \<sharp> x" by (simp_all add: fresh_def)
  then show "(a \<rightleftharpoons> b) \<bullet> x = x" by (simp add: swap_fresh_fresh)
qed

lemma supp_is_least_supports:
  fixes S :: "'a set"
    and x :: "'b"
  assumes  a1: "supports S x"
    and a2: "finite S"
    and a3: "\<And>S'. finite S' \<Longrightarrow> supports S' x \<Longrightarrow> S \<subseteq> S'"
  shows "(supp x) = S"
proof (rule equalityI)
  show "(supp x) \<subseteq> S" using a1 a2 by (rule supp_is_subset)
  with a2 have fin: "finite (supp x)" by (rule rev_finite_subset)
  have "supports (supp x) x" by (rule supp_supports)
  with fin a3 show "S \<subseteq> supp x" by blast
qed

lemma subsetCI: 
  "(\<And>x. x \<in> A \<Longrightarrow> x \<notin> B \<Longrightarrow> False) \<Longrightarrow> A \<subseteq> B" by auto

lemma finite_supp_unique:
  assumes a1: "supports S x"
  assumes a2: "finite S"
  assumes a3: "\<And>a b. \<lbrakk>a \<in> S; b \<notin> S\<rbrakk> \<Longrightarrow> (a \<rightleftharpoons> b) \<bullet> x \<noteq> x"
  shows "supp x = S"
  using a1 a2
proof (rule supp_is_least_supports)
  fix S'
  assume "finite S'" and "supports S' x"
  show "S \<subseteq> S'"
  proof (rule subsetCI)
    fix a
    assume "a \<in> S" and "a \<notin> S'"
    have "finite (S \<union> S')"
      using \<open>finite S\<close> \<open>finite S'\<close> by simp
    then obtain b where "b \<notin> S \<union> S'" by (rule obtain_atom)
    then have "b \<notin> S" and "b \<notin> S'" by simp_all
    then have "(a \<rightleftharpoons> b) \<bullet> x = x"
      using \<open>a \<notin> S'\<close> \<open>supports S' x\<close> by (simp add: supports_def)
    moreover have "(a \<rightleftharpoons> b) \<bullet> x \<noteq> x"
      using \<open>a \<in> S\<close> \<open>b \<notin> S\<close> by (rule a3)
    ultimately show "False" by simp
  qed
qed

end

lemma perm_swap_eq:
  "(a \<rightleftharpoons> b) \<bullet> p = p \<longleftrightarrow> (p \<bullet> (a \<rightleftharpoons> b)) = (a \<rightleftharpoons> b)"
  unfolding permute_perm_def by (metis add_diff_cancel minus_perm_def)

lemma supports_perm: 
  "perm_pt.supports {a. p \<bullet> a \<noteq> a} p"
  by (simp add: perm_pt.supports_def perm_swap_eq eqvt)

lemma finite_perm_lemma:
  fixes p :: "('a::infinite) perm"
  shows "finite {a :: 'a. p \<bullet> a \<noteq> a}"
  using finite_Rep_perm [of p]
  unfolding permute_atom_def .

lemma supp_perm:
  "perm_pt.supp p = {a. p \<bullet> a \<noteq> a}"
  apply (intro perm_pt.finite_supp_unique supports_perm finite_perm_lemma)
  apply (simp add: perm_swap_eq)
  apply (auto simp: perm_eq_iff swap_atom eqvt)
done

lemma supp_swap:
  "perm_pt.supp (a \<rightleftharpoons> b) = (if a = b then {} else {a, b})"
  by (auto simp add: supp_perm swap_atom)

lemma supp_zero_perm: 
  "perm_pt.supp 0 = {}"
  by (simp add: supp_perm)

lemma finite_supp_perm:
  "finite (perm_pt.supp p)"
  by (metis finite_perm_lemma supp_perm)

lemma plus_perm_eq:
  assumes "perm_pt.supp p \<inter> perm_pt.supp q = {}"
  shows "p + q = q + p"
unfolding perm_eq_iff
proof
  fix a :: "'a"
  show "(p + q) \<bullet> a = (q + p) \<bullet> a"
  proof -
    { assume "a \<notin> perm_pt.supp p" "a \<notin> perm_pt.supp q"
      then have "(p + q) \<bullet> a = (q + p) \<bullet> a" 
        by (simp add: supp_perm)
    }
    moreover
    { assume a: "a \<in> perm_pt.supp p" "a \<notin> perm_pt.supp q"
      then have "p \<bullet> a \<in> perm_pt.supp p" by (simp add: supp_perm)
      then have "p \<bullet> a \<notin> perm_pt.supp q" using assms by auto
      with a have "(p + q) \<bullet> a = (q + p) \<bullet> a" 
        by (simp add: supp_perm)
    }
    moreover
    { assume a: "a \<notin> perm_pt.supp p" "a \<in> perm_pt.supp q"
      then have "q \<bullet> a \<in> perm_pt.supp q" by (simp add: supp_perm)
      then have "q \<bullet> a \<notin> perm_pt.supp p" using assms by auto 
      with a have "(p + q) \<bullet> a = (q + p) \<bullet> a" 
        by (simp add: supp_perm)
    }
    ultimately show "(p + q) \<bullet> a = (q + p) \<bullet> a" 
      using assms by blast
  qed
qed

lemma supp_plus_perm:
  "perm_pt.supp (p + q) \<subseteq> perm_pt.supp p \<union> perm_pt.supp q"
  by (auto simp add: supp_perm)

lemma supp_plus_perm_eq:
  assumes "perm_pt.supp p \<inter> perm_pt.supp q = {}"
  shows "perm_pt.supp (p + q) = perm_pt.supp p \<union> perm_pt.supp q"
proof -
  { fix a
    assume "a \<in> perm_pt.supp p"
    then have "a \<notin> perm_pt.supp q" using assms by auto
    then have "a \<in> perm_pt.supp (p + q)" using \<open>a \<in> perm_pt.supp p\<close> 
      by (simp add: supp_perm)
  }
  moreover
  { fix a
    assume "a \<in> perm_pt.supp q"
    then have "a \<notin> perm_pt.supp p" using assms by auto
    then have "a \<in> perm_pt.supp (q + p)" using \<open>a \<in> perm_pt.supp q\<close> 
      by (simp add: supp_perm)
    then have "a \<in> perm_pt.supp (p + q)" using assms plus_perm_eq
      by metis
  }
  ultimately have "perm_pt.supp p \<union> perm_pt.supp q \<subseteq> perm_pt.supp (p + q)"
    by blast
  then show "perm_pt.supp (p + q) = perm_pt.supp p \<union> perm_pt.supp q"
    using supp_plus_perm
    by blast
qed

lemma atom_set_avoiding_aux:
  fixes As Xs :: "('a::infinite) set"
  assumes b: "Xs \<subseteq> As"
    and c: "finite As"
  shows "\<exists>(p::('a::infinite) perm). (p \<bullet> Xs) \<inter> As = {} \<and> perm_pt.supp p = (Xs \<union> (p \<bullet> Xs))"
proof -
  from b c have "finite Xs" by (rule finite_subset)
  then show ?thesis using b
  proof (induct rule: finite_subset_induct)
    case empty
    have "0 \<bullet> {} \<inter> As = {}" by (simp)
    moreover
    have "perm_pt.supp 0 = {} \<union> 0 \<bullet> {}" by (simp add: supp_zero_perm)
    ultimately show ?case by blast
  next
    case (insert x Xs)
    then obtain p where
      p1: "(p \<bullet> Xs) \<inter> As = {}" and 
      p2: "perm_pt.supp p = (Xs \<union> (p \<bullet> Xs))" by blast
    from \<open>x \<in> As\<close> p1 have "x \<notin> p \<bullet> Xs" by fast
    with \<open>x \<notin> Xs\<close> p2 have "x \<notin> perm_pt.supp p" by fast
    then have px: "p \<bullet> x = x" unfolding supp_perm by simp
    have "finite (As \<union> p \<bullet> Xs \<union> perm_pt.supp p)"
      using \<open>finite As\<close> \<open>finite Xs\<close>
      by (simp add: set_pt.permute_set_eq_image finite_supp_perm)
    then obtain y where "y \<notin> (As \<union> p \<bullet> Xs \<union> perm_pt.supp p)"
      by (rule atom_set_pt.obtain_atom)
    then have y: "y \<notin> As" "y \<notin> p \<bullet> Xs" "y \<notin> perm_pt.supp p"
      by simp_all
    then have py: "p \<bullet> y = y" "x \<noteq> y" using \<open>x \<in> As\<close>
      by (auto simp add: supp_perm)
    let ?q = "(x \<rightleftharpoons> y) + p"
    have q: "?q \<bullet> insert x Xs = insert y (p \<bullet> Xs)"
      unfolding atom_set_pt.insert_eqvt
      using \<open>p \<bullet> x = x\<close>
      using \<open>x \<notin> p \<bullet> Xs\<close> \<open>y \<notin> p \<bullet> Xs\<close>
      by (simp add: swap_atom swap_set_not_in)
    have "?q \<bullet> insert x Xs \<inter> As = {}"
      using \<open>y \<notin> As\<close> \<open>p \<bullet> Xs \<inter> As = {}\<close>
      unfolding q by simp
    moreover
    have "perm_pt.supp (x \<rightleftharpoons> y) \<inter> perm_pt.supp p = {}" using px py
      unfolding supp_swap by (simp add: supp_perm)
    then have "perm_pt.supp ?q = (perm_pt.supp (x \<rightleftharpoons> y) \<union> perm_pt.supp p)" 
      by (simp add: supp_plus_perm_eq)
    then have "perm_pt.supp ?q = insert x Xs \<union> ?q \<bullet> insert x Xs"
      using p2 \<open>x \<noteq> y\<close> unfolding q supp_swap
      by auto
    ultimately show ?case by blast
  qed
qed

lemma (in permutation_type) finite_atom_set_avoiding:
  fixes Xs :: "('a::infinite) set"
  assumes "finite (supp c)"
    and "finite Xs"
  obtains p :: "('a::infinite) perm"
    where "(p \<bullet> Xs) \<sharp> c" and "perm_pt.supp p = (Xs \<union> (p \<bullet> Xs))"
  using assms and atom_set_avoiding_aux [of Xs "Xs \<union> supp c"]
  unfolding fresh_set_def fresh_def by blast

lemma (in permutation_type) finite_atom_set_avoidingD:
  assumes "finite (supp c)"
    and "finite xs"
  shows "\<exists>p. (p \<bullet> xs) \<sharp> c"
  using assms by (elim finite_atom_set_avoiding) auto

lemma (in permutation_type) permute_minus_comp_id [simp]:
  fixes \<pi> :: "('a::infinite) perm"
  shows "((\<bullet>) (- \<pi>)) \<circ> ((\<bullet>) \<pi>) = (id :: 'b \<Rightarrow> 'b)"
by auto

(*finitely supported*)
locale finitely_supported = permutation_type +
  assumes finite_supp: "finite (supp x)"
begin

lemma atom_set_avoiding:
  fixes Xs :: "('a::infinite) set"
  assumes "finite Xs"
  obtains p :: "('a::infinite) perm"
    where "(p \<bullet> Xs) \<sharp> c" and "perm_pt.supp p = (Xs \<union> (p \<bullet> Xs))"
  using assms and atom_set_avoiding_aux [of Xs "Xs \<union> supp c"]
    and finite_atom_set_avoiding [OF finite_supp] by blast

lemma atom_set_avoidingD:
  assumes "finite xs"
  shows "\<exists>p. (p \<bullet> xs) \<sharp> c"
  using assms and finite_atom_set_avoidingD [OF finite_supp] by blast

lemma supp_eqvt [eqvt]:
  shows "p \<bullet> (supp x) = supp (p \<bullet> x)"
proof -
  interpret ap: pred_pt permute_atom ..
  interpret asp: pred_pt permute_atom_set ..
  interpret bf: fun_pt permute_bool permute_bool ..
  have *: "fun_pt.permute_fun (\<bullet>) (\<bullet>) p Not = Not"
    by (simp add: bf.permute_fun_def permute_bool_def)
  show ?thesis
    unfolding supp_def
    unfolding atom_set_pt.Collect_eqvt
    unfolding atom_pred_pt.lambda_eqvt
    unfolding asp.apply_eqvt [of _ infinite]
    by (simp add: bf.apply_eqvt * eqvt asp.permute_pred_def permute_eqvt [of p]
                  atom_pt.unpermute_def atom_pred_pt.lambda_eqvt
             del: permute_eq_iff bool_pure.permute_pure)
qed

lemma rename_avoiding:
  assumes "finite Xs"
  obtains p t' where "t' = p \<bullet> t" "Xs \<inter> supp t' = {}"
proof -
  obtain p where 1: "- p \<bullet> Xs \<inter> supp t = {}"
    by (metis assms minus_minus atom_set_avoidingD fresh_set_disjoint)
  obtain t' where "t' = p \<bullet> t" by simp
  moreover then have "Xs \<inter> supp t' = {}"
    by (metis 1 atom_set_pt.empty_eqvt atom_set_pt.inter_eqvt atom_set_pt.permute_minus_cancel(1) supp_eqvt)
  ultimately show ?thesis ..
qed

text \<open>We can always rename finitely supported entities apart.\<close>
lemma supp_fresh_set:
  "\<exists>p. supp (p \<bullet> x) \<sharp> y"
  using atom_set_avoidingD [OF finite_supp]
  by (simp add: eqvt)

lemma fresh_eqvt [eqvt]:
  fixes a :: "'a"
  shows "p \<bullet> (a \<sharp> x) = (p \<bullet> a) \<sharp> (p \<bullet> x)"
  by (simp add: fresh_def eqvt del: bool_pure.permute_pure)

lemma fresh_permute_iff:
  fixes a :: "'a"
  shows "(p \<bullet> a) \<sharp> (p \<bullet> x) \<longleftrightarrow> a \<sharp> x"
  by (simp only: fresh_eqvt [symmetric] permute_bool_def)

lemma fresh_permute_left:
  fixes a :: "'a"
  shows "a \<sharp> p \<bullet> x \<longleftrightarrow> (- p \<bullet> a) \<sharp> x"
proof
  assume "a \<sharp> p \<bullet> x"
  then have "- p \<bullet> a \<sharp> - p \<bullet> p \<bullet> x" by (simp only: fresh_permute_iff)
  then show "- p \<bullet> a \<sharp> x" by simp
next
  assume "- p \<bullet> a \<sharp> x"
  then have "p \<bullet> - p \<bullet> a \<sharp> p \<bullet> x" by (simp only: fresh_permute_iff)
  then show "a \<sharp> p \<bullet> x" by simp
qed

end

context list_pt
begin

adhoc_overloading
  FRESH \<rightleftharpoons> fresh elt.fresh

lemma supp_Nil [simp]: 
  "supp [] = {}"
  by (simp add: supp_def)

lemma supp_Cons [simp]: 
  "supp (x # xs) = elt.supp x \<union> supp xs"
  by (simp add: elt.supp_def supp_def Collect_imp_eq Collect_neg_eq)

lemma fresh_Nil [simp]: 
  "a \<sharp> []"
  by (simp add: fresh_def)

lemma fresh_Cons [iff]:
  "a \<sharp> (x # xs) \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> xs"
  by (simp add: elt.fresh_def fresh_def)

lemma supp_Union [simp]:
  "supp xs = (\<Union>x\<in>set xs. elt.supp x)"
  by (induct xs) (simp del: permute_list_def)+

end

context prod_pt
begin

lemma supp_Un [simp]:
  "supp (x, y) = fst.supp x \<union> snd.supp y"
  by (auto simp: supp_def fst.supp_def snd.supp_def eqvt)

lemma fst_eqvt [eqvt]:
  "\<pi> \<bullet> (fst p) = fst (\<pi> \<bullet> p)"
  by (cases p) (simp add: eqvt)

lemma snd_eqvt [eqvt]:
  "\<pi> \<bullet> (snd p) = snd (\<pi> \<bullet> p)"
  by (cases p) (simp add: eqvt)

end

end
