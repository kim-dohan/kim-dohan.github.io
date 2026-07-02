(*
Author:  Akihisa Yamada (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Quasi_Order
  imports
    Reduction_Pair
    HOL.Complete_Lattices
begin

unbundle lattice_syntax

(*FIXME: move*)
section\<open>Convenient Relation-to-Set Conversion\<close>

abbreviation rel_of where "rel_of f \<equiv> Collect (case_prod f)"

lemma mem_rel_ofI: "r1 x y \<Longrightarrow> (x,y) \<in> rel_of r1" by simp
lemma rel_of:
  shows rel_of_OO: "\<And>r1 r2. rel_of (r1 OO r2) = rel_of r1 O rel_of r2"
    and rel_of_sup: "\<And>r1 r2. rel_of (r1 \<squnion> r2) = rel_of r1 \<union> rel_of r2"
    and rel_of_inf: "\<And>r1 r2. rel_of (r1 \<sqinter> r2) = rel_of r1 \<inter> rel_of r2"
    and rel_of_tranclp: "\<And>r. rel_of (r\<^sup>+\<^sup>+) = (rel_of r)\<^sup>+"
    and rel_of_rtranclp: "\<And>r. rel_of (r\<^sup>*\<^sup>*) = (rel_of r)\<^sup>*"
    and rel_of_conversep: "\<And>r. rel_of r\<inverse>\<inverse> = (rel_of r)\<inverse>"
    and le_by_rel_of: "\<And>r1 r2. r1 \<le> r2 \<longleftrightarrow> rel_of r1 \<subseteq> rel_of r2"
    and eq_by_rel_of: "\<And>r1 r2. r1 = r2 \<longleftrightarrow> rel_of r1 = rel_of r2"
    and wfP_by_rel_of: "\<And>r. wfP r \<longleftrightarrow> wf (rel_of r)"
  by (auto 0 4 simp add: trancl_def rtrancl_def wfp_def)

(* Maybe automation is useful *)
lemmas OO_mono1 = O_mono1[of "rel_of _" "rel_of _" "rel_of _", folded rel_of]
lemmas OO_mono2 = O_mono2[of "rel_of _" "rel_of _" "rel_of _", folded rel_of]
lemmas OO_assoc = O_assoc[of "rel_of _" "rel_of _" "rel_of _", folded rel_of]

lemma tranclp_mono: "r \<le> s \<Longrightarrow> r\<^sup>+\<^sup>+ \<le> s\<^sup>+\<^sup>+"
  by (simp add: rel_of subrelI trancl_mono)

lemma wf_O_comm: "wf (R O S) \<longleftrightarrow> wf (S O R)"
  using SN_O_comm
  by (metis SN_iff_wf converse_converse converse_relcomp)

lemma wf_relto_relcomp: "wf (relto R S) \<longleftrightarrow> wf (R O S\<^sup>*)"
  using SN_on_relto_relcomp[of "S\<inverse>" "R\<inverse>" UNIV]
  by (simp add: rtrancl_converse converse_relcomp[symmetric] SN_iff_wf O_assoc)

context
  fixes S R
  assumes pull: "S O R \<subseteq> R\<^sup>* O S"
begin

qualified lemma push: "R\<inverse> O S\<inverse> \<subseteq> S\<inverse> O (R\<inverse>)\<^sup>*"
  by (metis pull converse_mono converse_relcomp rtrancl_converse)

lemma O_rtrancl_pull: "S O R\<^sup>* \<subseteq> R\<^sup>* O S"
  using rtrancl_O_push[OF push]
  by (metis converse_mono converse_relcomp rtrancl_converse)

lemma rtrancl_U_pull: "(S \<union> R)\<^sup>* = R\<^sup>* O S\<^sup>*"
  using rtrancl_U_push[OF push]
  by (metis converse_Un converse_converse converse_relcomp rtrancl_converse sup_commute)

lemma wf_relto_pull: "wf (R\<^sup>* O S O R\<^sup>*) \<longleftrightarrow> wf S"
  apply (rule iffI)
  apply (rule wf_subset, force, force)
  unfolding wf_relto_relcomp
  using SN_on_O_push[OF push, of UNIV]
  by (subst wf_O_comm, auto simp: O_rtrancl_pull wf_relcomp_compatible)

end

lemma wf_trancl_iff[simp]: "wf (R\<^sup>+) \<longleftrightarrow> wf R"
  by (intro iffI[OF wf_subset[of "R\<^sup>+"] wf_trancl], auto)

context
  fixes R S :: "('a \<times> 'a) set"
  assumes absorb: "R O S \<subseteq> R"
begin

lemma O_rtrancl_absorb_right: "R O S\<^sup>* = R"
proof-
  { fix x y z
    have "(y,z) \<in> S\<^sup>* \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> (x,z) \<in> R"
      by (induct rule: rtrancl_induct, insert absorb, auto)
  }
  then show ?thesis by auto
qed

lemma rtrancl_U_absorb_right: "(S \<union> R)\<^sup>* = S\<^sup>* O R\<^sup>*"
  apply (subst Un_commute)
  apply (rule rtrancl_U_pull)
  using absorb by auto

lemma wf_relto_absorb_right: "wf (relto R S) \<longleftrightarrow> wf R"
  apply (rule wf_relto_pull) using absorb by auto

end

section \<open>Quasi-Orderings\<close>

context ord begin

text \<open>Extending @{class ord} with some more notations.\<close>

definition equiv (infix "\<sim>" 50) where [simp]: "x \<sim> y \<equiv> x \<le> y \<and> y \<le> x"

lemma equiv_sym[sym]: "x \<sim> y \<Longrightarrow> y \<sim> x" by auto

definition equiv_class ("[_]\<^sub>\<sim>") where "[x]\<^sub>\<sim> \<equiv> { y. x \<sim> y }"

lemma mem_equiv_class[simp]: "y \<in> [x]\<^sub>\<sim> \<longleftrightarrow> x \<sim> y" by (auto simp: equiv_class_def)

definition "Upper_Bounds X \<equiv> {b. \<forall>x \<in> X. b \<ge> x}"

lemma mem_Upper_Bounds: "b \<in> Upper_Bounds X \<longleftrightarrow> (\<forall>x \<in> X. b \<ge> x)"
  by (auto simp: Upper_Bounds_def)

lemma Upper_BoundsI[intro]: "(\<And>x. x \<in> X \<Longrightarrow> b \<ge> x) \<Longrightarrow> b \<in> Upper_Bounds X"
  by (auto simp: Upper_Bounds_def)

lemma Upper_BoundsE[elim]: "b \<in> Upper_Bounds X \<Longrightarrow> ((\<And>x. x \<in> X \<Longrightarrow> b \<ge> x) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: Upper_Bounds_def)

lemma Upper_Bounds_empty[simp]: "Upper_Bounds {} = UNIV" by auto
lemma Upper_Bounds_insert: "Upper_Bounds (insert x X) = {b. b \<ge> x} \<inter> Upper_Bounds X" by auto
lemma Upper_Bounds_singleton[simp]: "Upper_Bounds {x} = {b. b \<ge> x}" by auto

lemma Upper_Bounds_cmono: assumes "X \<subseteq> Y" shows "Upper_Bounds X \<supseteq> Upper_Bounds Y"
  using assms by (auto simp: Upper_Bounds_def)

definition "Leasts X \<equiv> { b \<in> X. \<forall>c \<in> X. b \<le> c }"

lemma LeastsI[intro]: "b \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> b \<le> x) \<Longrightarrow> b \<in> Leasts X"
  and LeastsD: "x \<in> Leasts X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y"
  and LeastsE[elim]: "b \<in> Leasts X \<Longrightarrow> (b \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> b \<le> x) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: Leasts_def)

lemma Least_Upper_Bounds_mono:
  assumes XY: "X \<subseteq> Y" and bX: "bX \<in> Leasts (Upper_Bounds X)" and bY: "bY \<in> Leasts (Upper_Bounds Y)"
  shows "bX \<le> bY"
proof-
  have "bY \<in> Upper_Bounds X" using XY bY by force
  with bX show ?thesis by auto
qed

lemma Leasts_equiv: "x \<in> Leasts X \<Longrightarrow> y \<in> Leasts X \<Longrightarrow> x \<sim> y" by auto

end

text \<open>This is a trick to make a class available also as a locale\<close>

locale ord_syntax = ord less_eq less for less_eq less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation less_eq (infix "\<sqsubseteq>" 50)
notation less (infix "\<sqsubset>" 50)
abbreviation(input) greater_eq_syntax (infix "\<sqsupseteq>" 50) where "greater_eq_syntax \<equiv> ord.greater_eq less_eq"
abbreviation(input) greater_syntax (infix "\<sqsupset>" 50) where "greater_syntax \<equiv> ord.greater less"

abbreviation equiv_syntax (infix "\<simeq>" 50) where "equiv_syntax \<equiv> ord.equiv less_eq"

abbreviation equiv_class_syntax ("[_]\<^sub>\<simeq>") where "equiv_class_syntax \<equiv> ord.equiv_class less_eq"

end

class quasi_order = ord +
  assumes order_refl[iff]: "x \<le> x"
      and order_trans[trans]: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      and le_less_trans[trans]: "x \<le> y \<Longrightarrow> y < z \<Longrightarrow> x < z"
      and less_le_trans[trans]: "x < y \<Longrightarrow> y \<le> z \<Longrightarrow> x < z"
      and less_imp_le: "x < y \<Longrightarrow> x \<le> y"
begin

lemma eq_imp_le: "x = y \<Longrightarrow> x \<le> y" by auto

lemma less_trans[trans]: "x < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  using le_less_trans[OF less_imp_le].

text \<open>
 Class @{class quasi_order} is incomparable with HOL class @{class preorder}, as the latter
 fixes $<$ as the "strict part" (which is not nice, e.g., for comparing polynomials)
 while we already assume compatibility (@{thm le_less_trans}).
\<close>

lemma equiv_trans[trans]:
  "x \<sim> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<sim> z"
  "x \<sim> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  "x \<le> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<le> z"
  "x \<sim> y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  "x < y \<Longrightarrow> y \<sim> z \<Longrightarrow> x < z"
  by (auto dest: order_trans le_less_trans less_le_trans)

lemma chainp_le_mono:
  assumes ch: "chainp (\<le>) seq" and ij: "i \<le> j" shows "seq i \<le> seq j"
  by (insert ij, induct rule: inc_induct, insert ch, auto dest: order_trans)

lemma chainp_less_mono: assumes ch: "chainp (<) seq" and ij: "i < j" shows "seq i < seq j"
  by (insert ij, induct rule:strict_inc_induct, insert ch, auto dest: less_trans)


lemma Leasts_singleton[simp]: "Leasts {a} = {a}"
  by auto

lemma Least_Upper_Bounds_singleton: "Leasts ({b. b \<ge> x}) = [x]\<^sub>\<sim>"
  by (auto intro!: LeastsI dest: order_trans)

lemma Least_Upper_Bounds_equiv_class:
  assumes bX: "b \<in> Leasts (Upper_Bounds X)" shows "Leasts (Upper_Bounds X) = [b]\<^sub>\<sim>"
proof(intro equalityI subsetI, unfold mem_equiv_class)
  from bX have bX: "b \<in> Upper_Bounds X" and leastb: "\<And>x. x \<in> Upper_Bounds X \<Longrightarrow> b \<le> x" by auto
  { fix c assume "c \<in> Leasts (Upper_Bounds X)"
    then have cUpper_Bounds: "c \<in> Upper_Bounds X" and leastc: "\<And>b. b \<in> Upper_Bounds X \<Longrightarrow> c \<le> b" by auto
    from leastb[OF cUpper_Bounds] leastc[OF bX] show "b \<sim> c" by auto
  }
  { fix c assume bc: "b \<sim> c"
    show "c \<in> Leasts (Upper_Bounds X)"
    proof(intro LeastsI Upper_BoundsI)
      fix x assume "x \<in> X"
      with bX have "x \<le> b" by auto
      with bc show "x \<le> c" by (auto dest: order_trans)
    next
      fix x assume "x \<in> Upper_Bounds X"
      from leastb[OF this] bc show "c \<le> x" by (auto dest: order_trans)
    qed
  }
qed

sublocale order_pair "rel_of (>)" "rel_of (\<ge>)"
  apply (unfold_locales, fold transp_trans)
  using le_less_trans less_le_trans
  by (auto intro: refl_onI transpI[OF less_trans] transpI[OF order_trans])

end

subsection \<open>Weakly ordered domain: where antisymmetry holds\<close>
class weak_order = quasi_order + assumes antisym[dest]: "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
begin

lemma equiv_is_eq[simp]: "(\<sim>) = (=)" by (intro ext, auto)

lemma equiv_class_singleton[simp]: "[a]\<^sub>\<sim> = {a}" by auto

lemma Least_Upper_Bound_singleton[simp]: "Leasts (Upper_Bounds {a}) = {a}" by auto

end

declare equiv_def[simp del]

subclass(in order) weak_order by(unfold_locales, auto)


subsection \<open>Well-founded quasi-ordered domain\<close>

class wf_order = quasi_order +
  assumes less_induct[case_names less]: "\<And>P a. (\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
begin

lemma wf: "wf (rel_of (<))" unfolding wf_def by(auto intro:less_induct)

sublocale SN_order_pair "rel_of (>)" "rel_of (\<ge>)"
  by (unfold_locales, auto simp: SN_iff_wf converse_def conversep.simps intro: wf)

lemma chainp_ends_nonstrict:
  assumes 0: "chainp (\<ge>) seq" shows "\<exists>n. \<forall>i \<ge> n. \<not> seq (Suc i) < seq i"
proof (rule ccontr, insert 0, induct "seq 0" arbitrary: seq rule: less_induct)
  case (less seq)
  from less.prems
  obtain n where 1: "seq n > seq (Suc n)" by auto
  define seq' where "\<And>i. seq' i = seq (Suc n + i)"
  show False
  proof (rule less.hyps)
    from less.prems show "chainp (\<ge>) seq'" by (auto simp: seq'_def)
    note 1
    also have "seq 0 \<ge> seq n" using less.prems by (induct n, auto dest: order_trans)
    finally show "seq 0 > seq' 0" by (auto simp: seq'_def)
    show "\<nexists>n. \<forall>i\<ge>n. \<not> seq' (Suc i) < seq' i"
    proof (unfold not_ex, intro allI notI)
      fix m
      assume 2: "\<forall>i\<ge>m. \<not> seq' (Suc i) < seq' i"
      from less.prems(1)[simplified, rule_format, of "m+n+1"]
      obtain i where "i \<ge> m + n + 1" and "seq (Suc i) < seq i" by auto
      then have "i - n - 1 \<ge> m" and "seq' (Suc (i-n-1)) < seq' (i-n-1)" by (auto simp: seq'_def)
      with 2 show False by auto
    qed
  qed
qed

end


text \<open>@{class wellorder} is a @{class wf_order}.\<close>

context wellorder begin

subclass wf_order by (unfold_locales; (fact less_induct | simp))

lemma chainp_ends_eq:
  assumes 1: "chainp (\<ge>) seq" shows "\<exists>n. \<forall>i\<ge>n. seq i = seq n"
proof-
  from chainp_ends_nonstrict[OF 1] 1
  obtain n where 2: "\<And>i. i \<ge> n \<Longrightarrow> seq (Suc i) = seq i" by (auto simp: not_less)
  show ?thesis
  proof (intro exI allI impI)
    show "n \<le> i \<Longrightarrow> seq i = seq n" for i by (induct rule:dec_induct, auto simp: 2)
  qed
qed

end

text \<open>@{type nat} is a @{class wf_order}.\<close>
instance nat :: wf_order ..

text \<open>The next one turns a well-founded relation into a well-founded order pair.\<close>
locale wf_order_seed =
  fixes w s :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes wf: "wfP s"
    and weak_compatp: "s OO w \<le> s\<^sup>+\<^sup>+"
begin

definition less (infix "\<sqsubset>" 50) where "less \<equiv> (w\<^sup>*\<^sup>* OO s)\<^sup>+\<^sup>+"

definition less_eq (infix "\<sqsubseteq>" 50) where "less_eq \<equiv> (w \<squnion> s)\<^sup>*\<^sup>*"

lemma absorb: "s\<^sup>+\<^sup>+ OO w \<le> s\<^sup>+\<^sup>+"
proof-
  have "s\<^sup>+\<^sup>+ x y \<Longrightarrow> w y z \<Longrightarrow> s\<^sup>+\<^sup>+ x z" for x y z
    by (induct rule: tranclp_induct, insert weak_compatp, auto)
  then show ?thesis by auto
qed

sublocale wf_order where less_eq = less_eq and less = less
proof (unfold_locales)
  have [trans]: "\<And>x y z. less x y \<Longrightarrow> less y z \<Longrightarrow> less x z" by (auto simp: less_def)
  have "less \<le> less_eq" by (unfold less_def less_eq_def rel_of, regexp)
  then show "\<And>x y. x \<sqsubset> y \<Longrightarrow> x \<sqsubseteq> y" by auto
  show [trans]: "\<And>x y z. x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z" by (auto simp: less_eq_def)
  have 1: "less_eq OO less \<le> less" by (unfold rel_of less_eq_def less_def, regexp)
  then show "\<And>x y z. x \<sqsubseteq> y \<Longrightarrow> y \<sqsubset> z \<Longrightarrow> x \<sqsubset> z" by auto
  have "less OO w \<le> (w\<^sup>*\<^sup>* OO s)\<^sup>*\<^sup>* OO w\<^sup>*\<^sup>* OO s\<^sup>+\<^sup>+"
    apply (unfold less_def)
    apply (subst trancl_unfold_right[of "rel_of _", unfolded rel_of[symmetric]])
    using OO_mono1[OF weak_compatp, of "(w\<^sup>*\<^sup>* OO s)\<^sup>*\<^sup>* OO w\<^sup>*\<^sup>*"]
    by (simp add: OO_assoc)
  also have "... \<le> less" by (unfold less_def rel_of, regexp)
  finally have "less OO w \<le> less".
  moreover have "less OO s \<le> less" by (unfold less_def rel_of, regexp)
  ultimately have "less OO (w \<squnion> s) \<le> less" by auto
  then have 2: "less OO less_eq = less"
    by (simp add: less_eq_def rel_of O_rtrancl_absorb_right)
  from eq_imp_le[OF this] show "\<And>x y z. x \<sqsubset> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubset> z" by force
  have less: "less = (w\<^sup>*\<^sup>* OO s\<^sup>+\<^sup>+ OO w\<^sup>*\<^sup>*)\<^sup>+\<^sup>+"
    apply (subst 2[symmetric])
    apply (unfold less_eq_def less_def rel_of)
    apply regexp
    done
  have "wf (rel_of less)"
    apply (unfold less rel_of wf_trancl_iff)
    apply (subst wf_relto_absorb_right) using absorb wf
    by (auto simp: rel_of)
  then show "\<And>P a. (\<And>x. (\<And>y. y \<sqsubset> x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
    by (auto simp: wf_def)
qed (auto simp: less_eq_def)

end

class quasi_order_sup = quasi_order + sup +
  assumes sup_ge1 [intro!]: "x \<le> x \<squnion> y"
      and sup_ge2 [intro!]: "y \<le> x \<squnion> y"
begin

lemma sup_trans1: assumes "x \<le> y" shows "x \<le> y \<squnion> z"
proof-
  note assms also note sup_ge1 finally show ?thesis by auto
qed

lemma sup_trans2: assumes "x \<le> z" shows "x \<le> y \<squnion> z"
proof-
  note assms also note sup_ge2 finally show ?thesis by auto
qed

lemma finite_set_has_Upper_Bounds: "finite X \<Longrightarrow> \<exists>b. b \<in> Upper_Bounds X"
  by (unfold Upper_Bounds_def, induct X rule:finite_induct, auto dest: sup_trans1)

lemma finite_set_is_bounded:
  assumes "finite X" and "x \<in> X" shows "x \<le> (SOME b. b \<in> Upper_Bounds X)"
  using finite_set_has_Upper_Bounds[OF assms(1), folded some_eq_ex] assms(2) by auto

end

class quasi_semilattice_sup = quasi_order_sup +
  assumes sup_least: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
begin

lemma finite_set_has_Least_Upper_Bounds: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>b. b \<in> Leasts (Upper_Bounds X)"
proof(induct X rule:finite_induct)
  case empty then show ?case by auto
next
  case IH: (insert x X)
  show ?case
  proof(cases "X = {}")
    case True
    with Least_Upper_Bounds_singleton have "Leasts (Upper_Bounds (insert x X)) = [x]\<^sub>\<sim>" by auto
    then show ?thesis by auto
  next
    case False
    with IH have "Leasts (Upper_Bounds X) \<noteq> {}" by auto
    then obtain b where bX: "b \<in> Leasts (Upper_Bounds X)" by auto
    then have "sup x b \<in> Leasts (Upper_Bounds (insert x X))"
      by (auto intro: sup_trans2 sup_least intro!: LeastsI Upper_BoundsI simp: Upper_Bounds_insert)
    then show ?thesis by auto
  qed
qed

end

subclass (in semilattice_sup) quasi_semilattice_sup by (unfold_locales, auto)

class quasi_order_bot = quasi_order + bot +
  assumes bot_least: "\<bottom> \<le> a"

text \<open>A class where the @{const Sup} operator is defined, which is valid only if it is definable.\<close>

class quasi_order_Sup = quasi_order + Sup +
  assumes Sup_in_Least_Upper_Bounds: "Leasts (Upper_Bounds X) \<noteq> {} \<Longrightarrow> \<Squnion>X \<in> Leasts (Upper_Bounds X)"
begin

lemma Sup_upper: assumes LUB: "Leasts (Upper_Bounds X) \<noteq> {}" and xX: "x \<in> X" shows "x \<le> \<Squnion>X"
  using Sup_in_Least_Upper_Bounds[OF LUB] xX by auto

lemma Sup_least: assumes LUB: "Leasts (Upper_Bounds X) \<noteq> {}" shows "(\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> \<Squnion>X \<le> y"
  using Sup_in_Least_Upper_Bounds[OF LUB] by (auto simp: Upper_Bounds_def)

lemma Sup_equiv_Least_Upper_Bounds: assumes bX: "b \<in> Leasts (Upper_Bounds X)" shows "\<Squnion>X \<sim> b"
proof-
  have "Leasts (Upper_Bounds X) \<noteq> {}" using bX by auto
  from Sup_in_Least_Upper_Bounds[OF this] show ?thesis using bX by auto
qed

lemma Sup_singleton: "\<Squnion>{x} \<sim> x" by (rule Sup_equiv_Least_Upper_Bounds, auto)

lemma Sup_mono:
  assumes X: "Leasts (Upper_Bounds X) \<noteq> {}" and Y: "Leasts (Upper_Bounds Y) \<noteq> {}" and XY: "X \<subseteq> Y"
  shows "\<Squnion>X \<le> \<Squnion>Y"
  by (auto intro: Least_Upper_Bounds_mono[OF XY] Sup_in_Least_Upper_Bounds[OF X] Sup_in_Least_Upper_Bounds[OF Y])

end

text \<open>Upward complete quasi-semilattices -- where @{const Sup} is always defined.\<close>

class quasi_semilattice_Sup = quasi_order_Sup + sup + bot +
  assumes Least_Upper_Bounds: "Leasts (Upper_Bounds X) \<noteq> {}"
    and sup_Sup: "x \<squnion> y = \<Squnion>{x,y}"
    and bot_Sup: "\<bottom> = \<Squnion>{}"
begin

lemmas Sup_in_Least_Upper_Bounds = Sup_in_Least_Upper_Bounds[OF Least_Upper_Bounds]
lemmas Sup_upper = Sup_upper[OF Least_Upper_Bounds]
lemmas Sup_least = Sup_least[OF Least_Upper_Bounds]
lemmas Sup_mono = Sup_mono[OF Least_Upper_Bounds]

subclass quasi_semilattice_sup
  by (unfold_locales, auto intro: Sup_upper Sup_least simp: sup_Sup)

subclass quasi_order_bot
proof(unfold_locales)
  fix x
  have "\<bottom> \<le> \<Squnion>{x}" by (unfold bot_Sup, rule Sup_mono, auto)
  also have "\<dots> \<sim> x" by (rule Sup_singleton)
  finally show "\<bottom> \<le> x".
qed

end


subsection \<open>@{term inv_imagep}\<close>

locale quasi_order_inv_imagep = base: quasi_order
begin

sublocale quasi_order "inv_imagep less_eq f" "inv_imagep less f"
  by (unfold_locales, unfold in_inv_imagep;
   fact base.order_refl base.order_trans base.less_trans base.less_le_trans base.le_less_trans base.less_imp_le)

end

locale wf_order_inv_imagep = base: wf_order
begin

interpretation quasi_order_inv_imagep..

sublocale wf_order "inv_imagep less_eq f" "inv_imagep less f"
  apply (unfold_locales)
  apply (unfold in_inv_imagep)
  using wf_inv_image[OF base.wf, unfolded wf_def] by auto

end

end
