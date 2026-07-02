(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at>
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL (see file COPYING.LESSER)
*)

chapter \<open>AC-Equivalence\<close>

theory AC_Equivalence
  imports
    AC_Rewriting_Base
    "HOL-Library.Multiset"
begin

(*TODO: move*)
lemma map_nth_conv: "map f ss = map g ts \<Longrightarrow> \<forall>i < length ss. f (ss ! i) = g (ts ! i)"
proof (intro allI impI)
  fix i show "map f ss = map g ts \<Longrightarrow> i < length ss \<Longrightarrow> f(ss!i) = g(ts!i)"
  proof (induct ss arbitrary: i ts)
    case Nil then show ?case by (induct ts) auto
  next
    case (Cons s ss) then show ?case
      by (induct ts, simp, (cases i, auto))
  qed
qed

section \<open>Implicit E-Algebras\<close>

text \<open>
  We call an F-algebra (where \<open>F\<close> is given implicitly by \<^typ>\<open>'f\<close>) that satisfies all
  equations in a set \<^term_type>\<open>E :: (('f, 'v) term \<times> ('f, 'v) term) set\<close> an E-algebra.

  Let \<open>A\<close> be an E-algebra whose carrier is the type \<^typ>\<open>'a\<close>. Then, there is a unique
  homomorphism \<^term_type>\<open>h :: ('f, 'v) term \<Rightarrow> 'a\<close>.

  Moreover, the image \<^term>\<open>h ` (UNIV :: ('f, 'v) term set)\<close> is the carrier of a
  subalgebra \<open>A'\<close> of \<open>A\<close> and \<open>h\<close> is a surjective homomorphism from \<^typ>\<open>('f, 'v) term\<close>
  to the carrier of \<open>A'\<close>.

  Since \<open>h\<close> is a homomorphism it satisfies

  \<open>
    1: h(f(t\<^sub>1,...,t\<^sub>n)) = f\<^sup>A(h(t\<^sub>1),...,h(t\<^sub>n))
  \<close>

  Now the goal is to use the above equation as specification for the operations \<open>f\<^sup>A\<^sup>'\<close>.
  To this end, we require that \<open>h\<close> is a congruence, assuring that \<open>f\<^sup>A\<^sup>'\<close> is well-defined on \<open>A'\<close>:

  \<open>
    2: h(t\<^sub>1) = h(u\<^sub>1) \<and> ... \<and> h(t\<^sub>n) = h(u\<^sub>n) \<Longrightarrow> h(f(t\<^sub>1,...,t\<^sub>n)) = h(f(u\<^sub>1,...,u\<^sub>n))
  \<close>

  If \<open>h\<close> satisfies (2) then the F-algebra \<open>A'\<close> can be reconstructed using (1) as the
  defining property of operations. If moreover, \<open>h\<close> satisfies

  \<open>
    3: h(l \<cdot> \<sigma>) = h(r \<cdot> \<sigma>)
  \<close>

  for all equations \<open>(l, r) \<in> E\<close> and substitutions \<open>\<sigma>\<close>, then \<open>A'\<close> is an E-algebra.

  In light of this observation, we call an \<open>h\<close> satisfying (2) and (3) an
  "implicit E-algebra" and \<open>A'\<close> its induced E-algebra.
\<close>


section \<open>Associativity\<close>

subsection \<open>Abstract A-normal forms\<close>

locale abstract_anf =
  fixes nf :: "('f, 'v) term \<Rightarrow> 'a" \<comment> \<open>implicit A-algebra\<close>
    and A :: "'f set" \<comment> \<open>set of associative function symbols\<close>
  assumes nf_assoc [simp]: "f \<in> A \<Longrightarrow> nf (Bin f (Bin f s t) u) = nf (Bin f s (Bin f t u))"
    and nf_FunI [intro]: "map nf ss = map nf ts \<Longrightarrow> nf (Fun f ss) = nf (Fun f ts)"
begin

lemma nf_BinI:
  assumes "nf s = nf s'" and "nf t = nf t'"
  shows "nf (Bin f s t) = nf (Bin f s' t')"
  using assms by (auto)

lemma nf_eq_ctxt:
  assumes "nf s = nf t"
  shows "nf (C\<langle>s\<rangle>) = nf (C\<langle>t\<rangle>)"
  using assms by (induct C) auto

end

text \<open>
  \<^term>\<open>A_class A\<close> is an implicit A-algebra.
\<close>
interpretation A_class_abstract_anf: abstract_anf where nf = "A_class A"
  by (unfold_locales) (auto simp: map_eq_conv' args_aconv_imp_aconv)


subsection \<open>Algebraic version of A-normal forms (executable)\<close>

text \<open>Smart constructor for associative function symbols.\<close>
fun aBin :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
  where
    "aBin f (Bin g s t) u = (if f = g then Bin f s (aBin f t u) else Bin f (Bin g s t) u)"
  | "aBin f s t = Bin f s t"

context
  fixes A :: "'f set"
begin

function anf :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
  where
    "anf (Var x) = Var x"
  | "anf (Bin f s t) = (if f \<in> A then aBin f (anf s) (anf t) else Bin f (anf s) (anf t))"
  | "\<And>f ts. \<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> anf (Fun f ts) = Fun f (map anf ts)"
  by (auto, atomize_elim, insert Bin_cases, auto)
termination by (lexicographic_order)

function is_anf :: "('f, 'v) term \<Rightarrow> bool"
  where
    "is_anf (Var x) \<longleftrightarrow> True"
  | "is_anf (Bin f s t) \<longleftrightarrow> is_anf s \<and> is_anf t \<and> (f \<in> A \<longrightarrow> (\<forall>u v. s \<noteq> Bin f u v))"
  | "\<And>f ts. \<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> is_anf (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. is_anf t)"
  by (auto, atomize_elim, insert Bin_cases, auto)
termination by (lexicographic_order)

lemma anf_code [code]:
  "anf (Var x) = Var x"
  "anf (Bin f s t) = (if f \<in> A then aBin f (anf s) (anf t) else Bin f (anf s) (anf t))"
  "anf (Fun f []) = Fun f []"
  "anf (Fun f [t]) = Fun f [anf t]"
  "anf (Fun f (s # t # u # us)) = Fun f (anf s # anf t # anf u # map anf us)"
  by simp_all

end

lemma aBin_assoc [simp]:
  "aBin f (aBin f s t) u = aBin f s (aBin f t u)"
  by (induct f s t rule: aBin.induct) simp_all

lemma is_anf_aBin [intro]:
  "is_anf A s \<Longrightarrow> is_anf A t \<Longrightarrow> is_anf A (aBin f s t)"
  by (induct f s t rule: aBin.induct) auto

lemma is_anf_anf [intro]: "is_anf A (anf A t)"
proof (induct t rule: anf.induct [of _ A])
  case (3 f ts)
  then show ?case using Bin_cases[of "Fun f (map (anf A) ts)"] by auto
qed auto

text \<open>
  \<^term>\<open>anf A\<close> is an implicit A-algebra.
\<close>
interpretation anf_abstract_anf: abstract_anf where nf = "anf A"
proof (unfold_locales)
  fix f and ss ts :: "('a, 'b) term  list"
  assume "map (anf A) ss = map (anf A) ts"
  then show "anf A (Fun f ss) = anf A (Fun f ts)"
    using Bin_cases[of "Fun f ss"] Bin_cases[of "Fun f ts"] by force
qed auto


subsection \<open>Relate abstract A-normal forms to \<^const>\<open>anf\<close> and \<^const>\<open>A_class\<close>\<close>

context abstract_anf
begin

text \<open>A-rewriting preserves abstract normal forms.\<close>

lemma astep_imp_nf_eq:
  "(s, t) \<in> astep A \<Longrightarrow> nf s = nf t"
  by (force intro: nf_eq_ctxt simp: A_rules_def)

lemma aconv_imp_nf_eq:
  "(s, t) \<in> (astep A)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> nf s = nf t"
  unfolding conversion_def
  by (induct rule: rtrancl_induct) (auto simp: astep_imp_nf_eq)

lemma nf_aBin [simp]:
  "f \<in> A \<Longrightarrow> nf (aBin f s t) = nf (Bin f s t)"
  by (induct f s t rule: aBin.induct) force+


text \<open>The normalization function \<^const>\<open>anf\<close> preserves abstract normal forms.\<close>
(* anf A t = anf A s ==> nf t = nf s   +   anf A (anf A t) = anf A t *)
lemma nf_anf: "nf (anf A t) = nf t"
  by (induct t rule: anf.induct [of _ A]) force+

end


subsection \<open>The main result for associativity\<close>

lemma aconv_iff [code_unfold]:
  "(s, t) \<in> (astep A)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> anf A s = anf A t"
proof
  assume "anf A s = anf A t"
  then have "A_class A (anf A s) = A_class A (anf A t)" by simp
  then show "(s, t) \<in> (astep A)\<^sup>\<leftrightarrow>\<^sup>*"
    by (simp add: A_class_abstract_anf.nf_anf)
qed (simp add: anf_abstract_anf.aconv_imp_nf_eq)


section \<open>Associativity and Commutativity\<close>

subsection \<open>Abstract AC-normal forms\<close>

text \<open>All function symbols are either both associative and commutative, or neither.\<close>
locale abstract_acnf =
  abstract_anf +
  assumes nf_commute [simp]: "f \<in> A \<Longrightarrow> nf (Bin f s t) = nf (Bin f t s)"
begin

lemma nf_left_commute [simp]:
  "f \<in> A \<Longrightarrow> nf (Bin f s (Bin f t u)) = nf (Bin f t (Bin f s u))"
  by (auto simp only: nf_assoc [symmetric] nf_BinI [OF nf_commute [of f s]])

end

text \<open>
  \<^term>\<open>AC_class A A\<close> is an implicit AC-algebra.
\<close>
interpretation AC_class_abstract_acnf: abstract_acnf where nf = "AC_class A A"
  by (unfold_locales) (auto simp: map_eq_conv' args_acconv_imp_acconv)


subsection \<open>Algebraic version of AC-normal forms (executable)\<close>

datatype ('f, 'v) acterm =
  AVar 'v
| AFun 'f "('f, 'v) acterm list"
| AAC 'f "('f, 'v) acterm multiset"

abbreviation (input) "ABin f s t \<equiv> AFun f [s, t]"

fun actop :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term multiset"
  where
    "actop f (Bin g s t) = (if f = g then actop f s + actop f t else {# Bin g s t #})"
  | "actop f t = {# t #}"

lemma actop_non_Bin [simp]:
  "\<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> actop h (Fun f ts) = {# Fun f ts #}"
  by (induct f "Fun f ts" rule: actop.induct) auto

lemma Melem_actop_size [termination_simp]:
  "s \<in># actop f t \<Longrightarrow> size s < Suc (size t + q)"
  "s \<in># actop f t \<Longrightarrow> size s < Suc (q + size t)"
  by (induct f t rule: actop.induct) (auto split: if_splits)

context
  fixes A :: "'f set"
begin

function acnf :: "('f, 'v) term \<Rightarrow> ('f, 'v) acterm"
  where
    "acnf (Var x) = AVar x"
  | "acnf (Bin f s t) =
      (if f \<in> A then AAC f (image_mset acnf (actop f (Bin f s t)))
      else ABin f (acnf s) (acnf t))"
  | "\<And>f ts. \<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> acnf (Fun f ts) = AFun f (map acnf ts)"
  by (auto, atomize_elim, insert Bin_cases, auto)
termination by (lexicographic_order)

function acnf_schema :: "('f, 'v) term \<Rightarrow> ('f, 'v) acterm"
  where
    "acnf_schema (Var v) = AVar v"
  | "acnf_schema (Bin f s t) =
      (if f \<in> A then AAC f (image_mset acnf_schema (actop f (Fun f [s, t])) + {# acnf_schema t #})
      else ABin f (acnf_schema s) (acnf_schema t))"
  | "\<And>f ts. \<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> acnf_schema (Fun f ts) = AFun f (map acnf_schema ts)"
  by (auto, atomize_elim, insert Bin_cases, auto)
termination by (lexicographic_order)

lemma acnf_code [code]:
  "acnf (Var x) = AVar x"
  "acnf (Bin f s t) =
    (if f \<in> A then AAC f (image_mset acnf (actop f (Bin f s t)))
    else ABin f (acnf s) (acnf t))"
  "acnf (Fun f []) = AFun f []"
  "acnf (Fun f [t]) = AFun f [acnf t]"
  "acnf (Fun f (s # t # u # us)) = AFun f (acnf s # acnf t # acnf u # map acnf us)"
  by simp_all

end

lemma image_mset_acnf_actop:
  assumes "f \<in> A" and "acnf A s = acnf A t"
  shows "image_mset (acnf A) (actop f s) = image_mset (acnf A) (actop f t)"
  using assms by (cases s rule: acnf.cases; cases t rule: acnf.cases) (auto split: if_splits)

text \<open>
  \<^term>\<open>acnf A\<close> is an implicit A-algebra.
\<close>
interpretation acnf_abstract_acnf: abstract_acnf where nf = "acnf A"
proof (unfold_locales)
  fix f and ss ts :: "('a, 'b) term list"
  assume "map (acnf A) ss = map (acnf A) ts"
  then show "acnf A (Fun f ss) = acnf A (Fun f ts)"
    using Bin_cases[of "Fun f ss"] Bin_cases[of "Fun f ts"]
    by auto (auto intro: arg_cong2[of _ _ _ _ "(+)"] image_mset_acnf_actop)
qed (auto simp: ac_simps)


subsection \<open>Relate abstract AC-normal forms to @{const acnf} and @{const AC_class}\<close>

lemma actop_singleton [simp]:
  "(\<And>u v. s \<noteq> Bin g u v) \<Longrightarrow> actop g s = {# s #}"
  by (cases "(g, s)" rule: actop.cases) auto

lemma non_empty_plus_non_empty_not_single:
  assumes "a \<noteq> {#}" "b \<noteq> {#}" shows "a + b \<noteq> {# x #}"
  using assms by (simp add: union_is_single)

lemma image_actop_nonempty:
  "image_mset h (actop f t) \<noteq> {#}"
  by (induct f t rule: actop.induct) auto

lemmas image_actop_plus_image_actop_not_single =
  non_empty_plus_non_empty_not_single [OF image_actop_nonempty image_actop_nonempty]
  non_empty_plus_non_empty_not_single [OF image_actop_nonempty image_actop_nonempty, symmetric]

fun del_actop :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
  where
    "del_actop s' (Bin f s t) =
      (if s = s' then t else if t = s' then s else Bin f s (del_actop s' t))"

lemma trivial_Bin_facts [simp]:
  "s \<noteq> Bin f s t" "s \<noteq> Bin f t s" "Bin f s t \<noteq> s" "Bin f t s \<noteq> s" "\<not> Bin f u v \<in># actop f s"
proof (induct s)
  fix g ts
  assume "(\<And>t. t \<in> set ts \<Longrightarrow> \<not> Fun f [u, v] \<in># actop f t)"
  then show "\<not> Bin f u v \<in># actop f (Fun g ts)"
    using Bin_cases[of "Fun g ts"] by (auto split: if_splits)
qed (auto, (metis list.set_intros)+)

lemma is_anf_actops:
  assumes "is_anf A t" and "s \<in># actop f t"
  shows "is_anf A s" and "\<forall>u v. Bin f u v \<noteq> s"
  using assms by (induct t rule: is_anf.induct) (auto split: if_splits)

context abstract_acnf
begin

text \<open>AC-rewriting preserves abstract normal forms.\<close>

lemma acstep_imp_nf_eq:
  "(s, t) \<in> acstep A A \<Longrightarrow> nf s = nf t"
  by (force intro: nf_eq_ctxt simp: AC_rules_def A_rules_def C_rules_def)

(* AC_class s = AC_class t ==> nf s = nf t *)
lemma acconv_imp_nf_eq:
  "(s, t) \<in> (acstep A A)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> nf s = nf t"
  unfolding conversion_def
  by (induct rule: rtrancl_induct) (auto simp: acstep_imp_nf_eq)

text \<open>Terms with the same @{const acnf} have the same abstract normal form. This is the hard part.\<close>

lemma acnf_eq_intro:
  assumes "f \<in> A" and "image_mset (acnf A) (actop f s) = image_mset (acnf A) (actop f t)"
  shows "acnf A s = acnf A t"
  using assms
  by (cases s rule: acnf.cases; cases t rule: acnf.cases)
    (auto split: if_splits simp: image_actop_plus_image_actop_not_single)

lemma shuffle_actop:
  assumes "f \<in> A" and "is_anf A (Bin f s t)" and "s' \<in># actop f (Bin f s t)"
  shows "nf (Bin f s t) = nf (Bin f s' (del_actop s' (Bin f s t))) \<and>
    is_anf A (Bin f s' (del_actop s' (Bin f s t)))"
using assms
proof (induct t arbitrary: s rule: bterm_induct)
  case (Bin g t u s)
  show ?case using Bin(3-5) nf_commute Bin(2)[of t]
    by (auto split: if_splits simp del: nf_commute)
       (subst (2) nf_left_commute, simp, metis nf_BinI)+
qed (auto split: if_splits)

lemma acnf_eq_imp_nf_eq':
  "is_anf A s \<Longrightarrow> is_anf A u \<Longrightarrow> acnf A s = acnf A u \<Longrightarrow> nf s = nf u"
proof (induct s arbitrary: u rule: acnf_schema.induct [of _ A, case_names Var Bin Fun])
  case (Var v u) then show ?case by (cases u rule: is_anf.cases) (auto split: if_splits)
next
  case (Fun f ts u)
  then obtain g us where [simp]: "u = Fun g us" by (cases u) (auto split: if_splits)
  have "length ts = length us"
    using Fun by (cases "\<forall>u v. us \<noteq> [u, v]") (auto dest: map_eq_imp_length_eq split: if_splits)
  then show ?case using Fun
    by (cases "\<forall>u v. us \<noteq> [u, v]")
       (auto intro!: nth_equalityI nf_BinI dest!: map_nth_conv split: if_splits)
next
  case (Bin f s t u)
  obtain v w where u[simp]: "u = Bin f v w" using Bin(5-7) by (cases u rule: is_anf.cases) (auto split: if_splits)
  show ?case
  proof (cases "f \<in> A")
    case False then show ?thesis using Bin(3-7)
      by (cases u rule: is_anf.cases)
         (auto simp only: acnf.simps is_anf.simps split: if_splits intro: nf_BinI, force+)
  next
    case [simp]: True
    have s: "actop f s = {# s #}" "s \<in># actop f (Bin f s t)"
      using Bin(5) by (auto split: if_splits)
    obtain s' where s': "s' \<in># actop f u" "acnf A s = acnf A s'"
      using s(2) arg_cong[OF image_mset_acnf_actop[OF True Bin(7)], of "set_mset"]
      by auto blast+
    then have 0: "nf (Bin f s t) = nf (Bin f s' t)" and *: "\<And>u v. s' \<noteq> Bin f u v"
      using is_anf_actops[of A u s' f] Bin(1)[of s s'] Bin(5,6) by auto
    define t' where "t' = del_actop s' u"
    have 1: "nf (Bin f s' t') = nf u" and t': "acnf A (Bin f s' t') = acnf A u" "is_anf A (Bin f s' t')"
      using Bin(6) s' shuffle_actop[of f v w s'] acnf_abstract_acnf.shuffle_actop[of f A v w s']
      by (auto simp: t'_def)
    have "acnf A t = acnf A t'" using Bin(7) s'(2) *
      by (auto intro: acnf_eq_intro[of f] simp: s(1) t'(1)[symmetric] simp del: u)
    then have 2: "nf (Bin f s' t) = nf (Bin f s' t')"
      using Bin(5) t'(2) by (fastforce intro: Bin(2) nf_BinI split: if_splits)
    show ?thesis by (simp add: 0 1 2)
  qed
qed

(* acnf A s = acnf A t ==> nf s = nf t *)
lemma acnf_eq_imp_nf_eq: "acnf A s = acnf A t \<Longrightarrow> nf s = nf t"
  using acnf_eq_imp_nf_eq' [of "anf A s" "anf A t"]
  by (auto simp: nf_anf acnf_abstract_acnf.nf_anf)

end


subsection \<open>The main result for associativity and commutativity\<close>

(* AC_class s = AC_classt <--> acnf A s = acnf A t *)
lemma acconv_iff [code_unfold]:
  "(s, t) \<in> (acstep A A)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> acnf A s = acnf A t"
  by (auto dest: AC_class_abstract_acnf.acnf_eq_imp_nf_eq intro: acnf_abstract_acnf.acconv_imp_nf_eq)


section \<open>A \<or> C - Symbols\<close>

locale abstract_cnf =
  fixes nf :: "('f, 'v) term \<Rightarrow> 'a" \<comment> \<open>implicit C-algebra\<close>
    and F\<^sub>C :: "'f set" \<comment> \<open>commutative function symbols\<close>
  assumes nf_commute [simp]: "f \<in> F\<^sub>C \<Longrightarrow> nf (Bin f s t) = nf (Bin f t s)"
    and nf_FunI [intro]: "map nf ss = map nf ts \<Longrightarrow> nf (Fun f ss) = nf (Fun f ts)"
begin

lemma nf_BinI:
  "nf s = nf s' \<Longrightarrow> nf t = nf t' \<Longrightarrow> nf (Bin f s t) = nf (Bin f s' t')"
  by (auto)

lemma nf_eq_ctxt:
  "nf s = nf t \<Longrightarrow> nf (C\<langle>s\<rangle>) = nf (C\<langle>t\<rangle>)"
  by (induct C) auto

end

text \<open>
  \<^term>\<open>C_class F\<^sub>C\<close> is an implicit C-algebra.
\<close>
interpretation C_class_abstract_cnf: abstract_cnf where nf = "C_class F\<^sub>C"
  by (unfold_locales) (auto simp: map_eq_conv' args_cconv_imp_cconv)

context
  fixes F\<^sub>C :: "'f set"
begin

function cnf :: "('f, 'v) term \<Rightarrow> ('f, 'v) acterm"
  where
    "cnf (Var x) = AVar x"
  | "cnf (Bin f s t) = (if f \<in> F\<^sub>C then AAC f {#cnf s, cnf t#} else ABin f (cnf s) (cnf t))"
  | "\<And>f ts. \<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> cnf (Fun f ts) = AFun f (map cnf ts)"
  by (auto, atomize_elim, insert Bin_cases, auto)
termination by (lexicographic_order)

lemma cnf_code [code]:
  "cnf (Var x) = AVar x"
  "cnf (Bin f s t) =
    (let s' = cnf s; t' = cnf t in if f \<in> F\<^sub>C then AAC f {#s', t'#} else ABin f s' t')"
  "cnf (Fun f []) = AFun f []"
  "cnf (Fun f [t]) = AFun f [cnf t]"
  "cnf (Fun f (s # t # u # us)) = AFun f (cnf s # cnf t # cnf u # map cnf us)"
  by (simp_all add: Let_def)

end

text \<open>
  \<^term>\<open>cnf F\<^sub>C\<close> is an implicit C-algebra.
\<close>
interpretation cnf_abstract_cnf: abstract_cnf where nf = "cnf F\<^sub>C"
proof (unfold_locales)
  fix f and ss ts :: "('a, 'b) term  list"
  assume "map (cnf F\<^sub>C) ss = map (cnf F\<^sub>C) ts"
  then show "cnf F\<^sub>C (Fun f ss) = cnf F\<^sub>C (Fun f ts)"
    using Bin_cases [of "Fun f ss"] Bin_cases [of "Fun f ts"] by auto
qed auto

context abstract_cnf
begin

lemma cstep_imp_nf_eq:
  "(s, t) \<in> cstep F\<^sub>C \<Longrightarrow> nf s = nf t"
  by (force intro: nf_eq_ctxt simp: C_rules_def)

lemma cconv_imp_nf_eq:
  "(s, t) \<in> (cstep F\<^sub>C)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> nf s = nf t"
  unfolding conversion_def
  by (induct rule: rtrancl_induct) (auto simp: cstep_imp_nf_eq)

end

\<comment> \<open>\<open>nf\<close> is an implicit A\<or>C-algebra\<close>
locale abstract_aocnf =
  anf: abstract_anf nf F\<^sub>A +
  cnf: abstract_cnf nf F\<^sub>C
  for nf :: "('f, 'v) term \<Rightarrow> 'a" and F\<^sub>A F\<^sub>C
begin

abbreviation (input) "AC \<equiv> F\<^sub>A \<inter> F\<^sub>C"

lemma nf_left_commute [simp]:
  "f \<in> AC \<Longrightarrow> nf (Bin f s (Bin f t u)) = nf (Bin f t (Bin f s u))"
  by (auto simp only: anf.nf_assoc [symmetric] anf.nf_BinI [OF cnf.nf_commute [of f s]])

end

text \<open>
  \<^term>\<open>AC_class F\<^sub>A F\<^sub>C\<close> is an implicit A\<or>C-algebra.
\<close>
interpretation AC_class_abstract_aocnf: abstract_aocnf where nf = "AC_class F\<^sub>A F\<^sub>C"
  by (unfold_locales) (auto simp: map_eq_conv' args_acconv_imp_acconv)

text \<open>Smart constructor for associative function symbols.\<close>
fun aABin :: "'f \<Rightarrow> ('f, 'v) acterm \<Rightarrow> ('f, 'v) acterm \<Rightarrow> ('f, 'v) acterm"
  where
    "aABin f (ABin g s t) u = (if f = g then ABin f s (aABin f t u) else ABin f (ABin g s t) u)"
  | "aABin f s t = ABin f s t"

lemma aABin_simps [simp]:
  "\<forall>u v. s \<noteq> AFun f [u, v] \<Longrightarrow> aABin f s t = ABin f s t"
  by (induct f s t rule: aABin.induct) auto

lemma aABin_assoc [simp]:
  "aABin f (aABin f s t) u = aABin f s (aABin f t u)"
  by (induct f s t rule: aABin.induct) simp_all

lemma aABin_neq_AAC [simp]:
  "aABin f s t \<noteq> AAC g T"
  "AAC g T \<noteq> aABin f s t"
  "aABin f s t \<noteq> AVar x"
  "AVar x \<noteq> aABin f s t"
  "\<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> aABin f s t \<noteq> AFun h ts"
  "\<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> AFun h ts \<noteq> aABin f s t"
  by (induct f s t rule: aABin.induct) auto

context
  fixes F\<^sub>A F\<^sub>C :: "'f set"
begin

function aocnf :: "('f, 'v) term \<Rightarrow> ('f, 'v) acterm"
  where
    "aocnf (Var x) = AVar x"
  | "aocnf (Bin f s t) =
      (if f \<in> F\<^sub>A \<inter> F\<^sub>C then AAC f (image_mset aocnf (actop f (Bin f s t)))
      else if f \<in> F\<^sub>A then aABin f (aocnf s) (aocnf t)
      else if f \<in> F\<^sub>C then AAC f {#aocnf s, aocnf t#}
      else ABin f (aocnf s) (aocnf t))"
  | "\<And>f ts. \<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> aocnf (Fun f ts) = AFun f (map aocnf ts)"
  by (auto, atomize_elim, insert Bin_cases, auto)
termination by (lexicographic_order)

function aocnf_schema :: "('f, 'v) term \<Rightarrow> ('f, 'v) acterm"
  where
    "aocnf_schema (Var v) = AVar v"
  | "aocnf_schema (Bin f s t) =
      (if f \<in> F\<^sub>A \<inter> F\<^sub>C then
        AAC f (image_mset aocnf_schema (actop f (Fun f [s, t])) + {# aocnf_schema t #})
      else ABin f (aocnf_schema s) (aocnf_schema t))"
  | "\<And>f ts. \<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> aocnf_schema (Fun f ts) = AFun f (map aocnf_schema ts)"
  by (auto, atomize_elim, insert Bin_cases, auto)
termination by (lexicographic_order)

lemma aocnf_code [code]:
  "aocnf (Var x) = AVar x"
  "aocnf (Bin f s t) = (let A = f \<in> F\<^sub>A; C = f \<in> F\<^sub>C in
    (if A \<and> C then AAC f (image_mset aocnf (actop f (Bin f s t)))
    else if A then aABin f (aocnf s) (aocnf t)
    else if C then AAC f {#aocnf s, aocnf t#}
    else ABin f (aocnf s) (aocnf t)))"
  "aocnf (Fun f []) = AFun f []"
  "aocnf (Fun f [t]) = AFun f [aocnf t]"
  "aocnf (Fun f (s # t # u # us)) = AFun f (aocnf s # aocnf t # aocnf u # map aocnf us)"
  by simp_all

end

lemma image_mset_aocnf_actop:
  assumes "f \<in> A \<inter> C" and "aocnf A C s = aocnf A C t"
  shows "image_mset (aocnf A C) (actop f s) = image_mset (aocnf A C) (actop f t)"
  using assms
  by (cases s rule: aocnf.cases; cases t rule: aocnf.cases)
    (auto simp: split: if_splits elim: aABin.cases)

text \<open>
  \<^term>\<open>aocnf F\<^sub>A F\<^sub>C\<close> is an implicit A\<or>C-algebra.
\<close>
interpretation aocnf_abstract_aocnf: abstract_aocnf where nf = "aocnf F\<^sub>A F\<^sub>C"
proof (unfold_locales)
  fix f and ss ts :: "('a, 'b) term list"
  assume "map (aocnf F\<^sub>A F\<^sub>C) ss = map (aocnf F\<^sub>A F\<^sub>C) ts"
  then show "aocnf F\<^sub>A F\<^sub>C (Fun f ss) = aocnf F\<^sub>A F\<^sub>C (Fun f ts)"
    using Bin_cases[of "Fun f ss"] Bin_cases[of "Fun f ts"]
    by auto (auto intro: arg_cong2 [of _ _ _ _ "(+)"] image_mset_aocnf_actop)
qed (auto simp: ac_simps)

context abstract_aocnf
begin

text \<open>A \<or> C - rewriting preserves abstract normal forms.\<close>

lemma acstep_imp_nf_eq:
  "(s, t) \<in> acstep F\<^sub>A F\<^sub>C \<Longrightarrow> nf s = nf t"
  by (force intro: anf.nf_eq_ctxt simp: AC_rules_def A_rules_def C_rules_def)

(* AC_class s = AC_class t ==> nf s = nf t *)
lemma acconv_imp_nf_eq:
  "(s, t) \<in> (acstep F\<^sub>A F\<^sub>C)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> nf s = nf t"
  unfolding conversion_def
  by (induct rule: rtrancl_induct) (auto simp: acstep_imp_nf_eq)

text \<open>Terms with the same @{const aocnf} have the same abstract normal form. This is the hard part.\<close>

lemma aocnf_eq_intro:
  assumes "f \<in> AC" and "image_mset (aocnf F\<^sub>A F\<^sub>C) (actop f s) = image_mset (aocnf F\<^sub>A F\<^sub>C) (actop f t)"
  shows "aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C t"
  using assms
  by (cases s rule: aocnf.cases; cases t rule: aocnf.cases)
    (auto split: if_splits simp: image_actop_plus_image_actop_not_single)

lemma shuffle_actop:
  assumes "f \<in> AC" and "is_anf F\<^sub>A (Bin f s t)"
    and "s' \<in># actop f (Bin f s t)"
  shows "nf (Bin f s t) = nf (Bin f s' (del_actop s' (Bin f s t))) \<and>
    is_anf F\<^sub>A (Bin f s' (del_actop s' (Bin f s t)))"
using assms
proof (induct t arbitrary: s rule: bterm_induct)
  case (Bin g t u s)
  show ?case
    using Bin(3-5) cnf.nf_commute [of f] Bin(2)[of t]
    by (auto split: if_splits simp del: cnf.nf_commute)
       (subst (2) nf_left_commute, simp, metis cnf.nf_BinI)+
qed (auto split: if_splits)

lemma map_not_bin: "\<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> \<forall>u v. map f ts \<noteq> [u, v]" by auto

lemma aocnf_not_ABin: "\<forall>u v. t \<noteq> Bin f u v \<Longrightarrow> \<forall>u v. aocnf F\<^sub>A F\<^sub>C t \<noteq> ABin f u v"
  apply (induct t rule: aocnf_schema.induct [of _ F\<^sub>A F\<^sub>C])
    apply auto
  apply (metis (no_types, lifting) aABin.simps(1) aABin_simps acterm.inject(2))+
  done

lemma aABin_roots: "aABin f s t = aABin g u v \<Longrightarrow> g = f"
  apply (induct f s t arbitrary: u v rule: aABin.induct)
       apply (auto split: if_splits)
        apply (metis aABin.simps(1) aABin_simps acterm.inject(2))+
  done

lemma aABin_AFun_roots:
  "aABin f s t = AFun g us \<Longrightarrow> g = f \<and> length us = 2"
  "AFun g us = aABin f s t \<Longrightarrow> g = f \<and> length us = 2"
  by (induct f s t arbitrary: us rule: aABin.induct) (auto split: if_splits)

lemma aocnf_roots:
  "aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C t \<Longrightarrow> root s = root t"
proof (induct s arbitrary: t rule: aocnf_schema.induct [of _ F\<^sub>A F\<^sub>C])
  case (1 x)
  then show ?case using Bin_cases [of t] by (auto split: if_splits)
next
  case (2 f u v)
  then show ?case using Bin_cases [of t]
    by (auto split: if_splits dest!: aABin_roots aABin_AFun_roots)
next
  case (3 f ts)
  then show ?case
    using Bin_cases [of t] by (auto split: if_splits simp: map_not_bin dest: map_eq_imp_length_eq)
qed

lemma aocnf_Fun_roots:
  "aocnf F\<^sub>A F\<^sub>C (Fun f ss) = aocnf F\<^sub>A F\<^sub>C (Fun g ts) \<Longrightarrow> g = f"
  using aocnf_roots [of "Fun f ss" "Fun g ts"] by simp

lemma is_anf_Bin_aocnf_simp:
  "f \<in> F\<^sub>A \<Longrightarrow> f \<notin> F\<^sub>C \<Longrightarrow> is_anf F\<^sub>A (Bin f s t) \<Longrightarrow>
    aocnf F\<^sub>A F\<^sub>C (Bin f s t) = ABin f (aocnf F\<^sub>A F\<^sub>C s) (aocnf F\<^sub>A F\<^sub>C t)"
  by (simp add: aocnf_not_ABin)

lemma aocnf_eq_imp_nf_eq':
  assumes "is_anf F\<^sub>A s"
    and "is_anf F\<^sub>A u"
    and "aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C u"
  shows "nf s = nf u"
using assms
proof (induct s arbitrary: u rule: aocnf_schema.induct [of _ F\<^sub>A F\<^sub>C, case_names Var Bin Fun])
  case (Var v u) then show ?case by (cases u rule: is_anf.cases) (auto split: if_splits)
next
  case (Fun f ts u)
  then obtain g us where [simp]: "u = Fun g us" by (cases u) (auto split: if_splits)
  have *: "\<forall>u v. map (aocnf F\<^sub>A F\<^sub>C) ts \<noteq> [u, v]" using Fun by auto
  then have "length ts = length us"
    using Fun by (cases "\<forall>u v. us \<noteq> [u, v]") (auto dest: map_eq_imp_length_eq split: if_splits)
  then show ?case using Fun and *
    by (cases "\<forall>u v. us \<noteq> [u, v]")
       (auto intro!: nth_equalityI cnf.nf_BinI dest!: map_nth_conv split: if_splits)
next
  case (Bin f s t u)
  obtain v w where u [simp]: "u = Bin f v w"
    using Bin(5-7) by (cases u rule: is_anf.cases) (auto split: if_splits simp: aocnf_not_ABin)
  show ?case
  proof (cases "f \<in> AC")
    case False
    moreover
    { assume "f \<notin> F\<^sub>A" and "f \<notin> F\<^sub>C"
      then have ?thesis using Bin(3-7) by (auto intro: cnf.nf_BinI) }
    moreover
    { assume f: "f \<notin> F\<^sub>A" "f \<in> F\<^sub>C"
      then have "aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C v \<and> aocnf F\<^sub>A F\<^sub>C t = aocnf F\<^sub>A F\<^sub>C w \<or>
        aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C w \<and> aocnf F\<^sub>A F\<^sub>C t = aocnf F\<^sub>A F\<^sub>C v"
        using Bin(7) by (auto simp: single_is_union add_eq_conv_diff)
      moreover
      { assume "aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C v" and "aocnf F\<^sub>A F\<^sub>C t = aocnf F\<^sub>A F\<^sub>C w"
        then have ?thesis using Bin(3-6) and f by (auto intro: cnf.nf_BinI) }
      moreover
      { assume "aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C w" and "aocnf F\<^sub>A F\<^sub>C t = aocnf F\<^sub>A F\<^sub>C v"
        then have ?thesis
        using Bin(3-6) and f
        by (subst cnf.nf_commute) (auto simp only: u is_anf.simps intro: cnf.nf_BinI) }
      ultimately have ?thesis by blast }
    moreover
    { assume "f \<in> F\<^sub>A" and "f \<notin> F\<^sub>C"
      then have ?thesis
        using Bin(3-7)
        by (simp_all only: u) (unfold is_anf_Bin_aocnf_simp [of f], auto intro: cnf.nf_BinI) }
    ultimately show ?thesis using False by blast
  next
    case True
    then have s: "actop f s = {# s #}" "s \<in># actop f (Bin f s t)"
      using Bin(5) by (auto split: if_splits)
    obtain s' where s': "s' \<in># actop f u" "aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C s'"
      using s(2) arg_cong[OF image_mset_aocnf_actop[OF True Bin(7)], of "set_mset"]
      by auto blast+
    then have 0: "nf (Bin f s t) = nf (Bin f s' t)" and *: "\<And>u v. s' \<noteq> Bin f u v"
      using Bin(1) [of s s'] and Bin(5,6) and True
      by (auto split: if_splits intro: cnf.nf_BinI is_anf_actops)
    define t' where "t' = del_actop s' u"
    have 1: "nf (Bin f s' t') = nf u"
      and t': "aocnf F\<^sub>A F\<^sub>C (Bin f s' t') = aocnf F\<^sub>A F\<^sub>C u" "is_anf F\<^sub>A (Bin f s' t')"
      using Bin(5,6) s' shuffle_actop[of f v w s'] and True
      and aocnf_abstract_aocnf.shuffle_actop[of f F\<^sub>A F\<^sub>C v w s']
      by (auto simp: t'_def)
    have "aocnf F\<^sub>A F\<^sub>C t = aocnf F\<^sub>A F\<^sub>C t'" using Bin(7) s'(2) * and True
      by (auto intro: aocnf_eq_intro [of f] simp: s(1) t'(1) [symmetric] simp del: u split: if_splits)
    then have 2: "nf (Bin f s' t) = nf (Bin f s' t')"
      using True and Bin(2, 5,6) and shuffle_actop [OF True, of v w s'] and s'
      by (intro cnf.nf_BinI) (auto simp: t'_def)
    show ?thesis by (simp add: 0 1 2)
  qed
qed

lemma aocnf_eq_imp_nf_eq:
  "aocnf F\<^sub>A F\<^sub>C s = aocnf F\<^sub>A F\<^sub>C t \<Longrightarrow> nf s = nf t"
using aocnf_eq_imp_nf_eq' [of "anf F\<^sub>A s" "anf F\<^sub>A t"]
by (auto simp: anf.nf_anf aocnf_abstract_aocnf.anf.nf_anf)

end

lemma aocconv_iff [code_unfold]:
  "(s, t) \<in> (acstep A C)\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> aocnf A C s = aocnf A C t"
  by (auto dest: AC_class_abstract_aocnf.aocnf_eq_imp_nf_eq intro: aocnf_abstract_aocnf.acconv_imp_nf_eq)

end
