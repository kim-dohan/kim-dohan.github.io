(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
License: LGPL (see file COPYING.LESSER)
*)

chapter \<open>AC-Rewriting\<close>

theory AC_Rewriting
imports
  AC_Rewriting_Base
  First_Order_Rewriting.Multihole_Context
  TRS.Sharp_Syntax
  Auxx.Util
begin

(*TODO: term_size already exists in Complexity.thy*)
fun num_symbs :: "('f, 'v) term \<Rightarrow> nat"
where
  "num_symbs (Var x) = 1"
| "num_symbs (Fun f ts) = sum_list (map num_symbs ts) + 1"

fun num_symbs_ctxt
where
  "num_symbs_ctxt \<box> = 0"
| "num_symbs_ctxt (More f ss C ts) =
    num_symbs_ctxt C + sum_list (map num_symbs ss) + sum_list (map num_symbs ts) + 1"

lemma num_symbs_ctxt_apply_term [simp]:
  "num_symbs (C\<langle>t\<rangle>) = num_symbs_ctxt C + num_symbs t"
by (induct C) (simp_all)

fun num_funs :: "('f, 'v) term \<Rightarrow> nat"
where
  "num_funs (Var x) = 0"
| "num_funs (Fun f ts) = sum_list (map num_funs ts) + 1"

fun num_vars :: "('f, 'v) term \<Rightarrow> nat"
where
  "num_vars (Var x) = 1"
| "num_vars (Fun f ts) = sum_list (map num_vars ts)"

lemma num_symbs_conv:
  "num_symbs t = num_funs t + num_vars t"
by (induct t) (simp_all, metis (no_types, lifting) sum_list_addf map_eq_conv)

text \<open>A mutually-recursive characterization of \<open>vars_term_ms\<close> (sometimes easier for proof).\<close>
fun vars_term_mset and vars_term_list_mset
where
  "vars_term_mset (Var x) = {#x#}"
| "vars_term_mset (Fun f ts) = vars_term_list_mset ts"
| "vars_term_list_mset [] = {#}"
| "vars_term_list_mset (t#ts) = vars_term_mset t + vars_term_list_mset ts"

lemma vars_term_mset_conv:
  fixes t :: "('f, 'v) term" and ts :: "('f, 'v) term list"
  shows "vars_term_mset t = vars_term_ms t"
    and "vars_term_list_mset ts = \<Sum>\<^sub># (mset (map vars_term_ms ts))"
by (induct t and ts rule: vars_term_mset_vars_term_list_mset.induct) (auto simp: ac_simps)

lemma
  fixes t :: "('f, 'v) term" and ts :: "('f, 'v) term list"
  shows num_vars_conv: "num_vars t = size (vars_term_mset t)"
    and "sum_list (map num_vars ts) = size (vars_term_list_mset ts)"
by (induct t and ts rule: vars_term_mset_vars_term_list_mset.induct) simp_all

lemma num_symbs_subst_apply_term':
  fixes t :: "('f, 'v) term" and ts :: "('f, 'v) term list"
  shows "num_symbs (t \<cdot> \<sigma>) = num_funs t + sum_mset (image_mset (num_symbs \<circ> \<sigma>) (vars_term_mset t))"
    and "sum_list (map (num_symbs \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts) =
      sum_list (map num_funs ts) + sum_mset (image_mset (num_symbs \<circ> \<sigma>) (vars_term_list_mset ts))"
by (induct t and ts rule: vars_term_mset_vars_term_list_mset.induct)
   (auto, metis (mono_tags, lifting) comp_apply map_eq_conv)

lemma num_symbs_subst_apply_term:
  "num_symbs (t \<cdot> \<sigma>) =
    num_symbs t + sum_mset (image_mset (num_symbs \<circ> \<sigma>) (vars_term_ms t)) - size (vars_term_ms t)"
unfolding num_symbs_subst_apply_term'
by (simp add: num_symbs_conv num_vars_conv vars_term_mset_conv)

lemma num_symbs_simp1:
  "t \<in> set ts \<Longrightarrow> num_symbs t < Suc (sum_list (map num_symbs ts))"
by (induct ts) auto

lemma num_symbs_simp2:
  "s \<in> set ss \<Longrightarrow> s \<rhd> t \<Longrightarrow> num_symbs t < num_symbs s \<Longrightarrow>
    num_symbs t < Suc (sum_list (map num_symbs ss))"
by (induct ss) auto

lemmas num_symbs_simps =
  num_symbs_simp1 num_symbs_simp2

lemma supt_num_symbs:
  "s \<rhd> t \<Longrightarrow> num_symbs s > num_symbs t"
by (induct rule: supt.induct) (auto simp: num_symbs_simps)

(*actually also multisets of variables are preserved (name?)*)
locale size_preserving_trs =
  fixes R :: "('f, 'v) trs"
  assumes same_size: "\<forall>(l, r) \<in> R. num_symbs l = num_symbs r \<and> vars_term_ms l = vars_term_ms r"
begin

lemma rstep_num_symbs_eq:
  assumes "(s, t) \<in> rstep R"
  shows "num_symbs s = num_symbs t"
using assms and same_size by (induct) (auto simp: num_symbs_subst_apply_term)

lemma rstep_vars_terms_ms_eq:
  assumes "(s, t) \<in> rstep R"
  shows "vars_term_ms s = vars_term_ms t"
proof -
  from rstepE[OF assms] obtain C \<sigma> l r ls rs where lr: "(l, r) \<in> R" and
    id: "s = C\<langle>ls\<rangle>" "t = C\<langle>rs\<rangle>" and id2: "ls = l \<cdot> \<sigma>" "rs = r \<cdot> \<sigma>" by metis
  from same_size lr have "vars_term_ms l = vars_term_ms r" by auto
  then have vars: "vars_term_ms ls = vars_term_ms rs" unfolding id2 by auto
  show ?thesis unfolding id
    by (induct C, auto simp: vars)
qed

lemma rsteps_num_symbs_eq:
  assumes "(s, t) \<in> (rstep R)\<^sup>*"
  shows "num_symbs s = num_symbs t"
using assms by (induct) (auto dest: rstep_num_symbs_eq)

lemma suptrel_num_symbs:
  assumes "(s, t) \<in> suptrel R"
  shows "num_symbs s > num_symbs t"
using assms unfolding suptrel_def by (induct) (auto dest!: supt_num_symbs rsteps_num_symbs_eq)

lemma SN_suptrel:
  "SN (suptrel R)"
by (rule SN_subset [of "(measure num_symbs)\<inverse>"])
   (auto simp: SN_iff_wf suptrel_num_symbs)

end

fun vars_ctxt_ms :: "('f, 'v) ctxt \<Rightarrow> 'v multiset"
where
  "vars_ctxt_ms Hole = {#}" |
  "vars_ctxt_ms (More f ss C ts) =
    \<Sum>\<^sub># (mset (map vars_term_ms ss)) +
    vars_ctxt_ms C + \<Sum>\<^sub># (mset (map vars_term_ms ts))"

lemma vars_term_ms_ctxt_apply:
  "vars_term_ms (C\<langle>t\<rangle>) = vars_ctxt_ms C + vars_term_ms t"
by (induct C) (auto simp: multiset_eq_iff)

text \<open>A mutually-recursive characterization of \<open>funs_term_ms\<close> (sometimes easier for proof).\<close>
fun funs_term_mset and funs_term_list_mset
where
  "funs_term_mset (Var x) = {#}"
| "funs_term_mset (Fun f ts) = {#f#} + funs_term_list_mset ts"
| "funs_term_list_mset [] = {#}"
| "funs_term_list_mset (t#ts) = funs_term_mset t + funs_term_list_mset ts"

lemma funs_term_mset_conv:
  fixes t :: "('f, 'v) term" and ts :: "('f, 'v) term list"
  shows "funs_term_mset t = funs_term_ms t"
    and "funs_term_list_mset ts = \<Sum>\<^sub># (mset (map funs_term_ms ts))"
by (induct t and ts rule: funs_term_mset_funs_term_list_mset.induct) (auto simp: ac_simps)

lemma funs_term_mset_subst_apply:
  fixes t :: "('f, 'v) term" and ts :: "('f, 'v) term list"
  shows "funs_term_mset (t \<cdot> \<sigma>) =
    funs_term_mset t + \<Sum>\<^sub># (image_mset (funs_term_mset \<circ> \<sigma>) (vars_term_mset t))"
  and "funs_term_list_mset (map (\<lambda>t. t \<cdot> \<sigma>) ts) =
    funs_term_list_mset ts + \<Sum>\<^sub># (image_mset (funs_term_mset \<circ> \<sigma>) (vars_term_list_mset ts))"
by (induct t and ts rule: funs_term_mset_funs_term_list_mset.induct) (simp_all add: ac_simps)

lemma funs_term_ms_subst_apply [simp]:
  "funs_term_ms (t \<cdot> \<sigma>) =
    funs_term_ms t + \<Sum>\<^sub># (image_mset (funs_term_ms \<circ> \<sigma>) (vars_term_ms t))"
by (simp add: funs_term_mset_subst_apply funs_term_mset_conv [symmetric, abs_def] vars_term_mset_conv)

lemma num_symbs_is_size_funs_terms_ms_vars_term_ms: 
  "num_symbs t = size (funs_term_ms t) + size (vars_term_ms t)"
proof (induct t)
  case (Fun f ts)
  show ?case
    by (simp, insert Fun, induct ts, auto)
qed simp

locale symbol_preserving_trs =
  fixes R :: "('f, 'v) trs"
  assumes same_symbs: "\<forall>(l, r)\<in>R. funs_term_ms l = funs_term_ms r \<and> vars_term_ms l = vars_term_ms r"
begin

sublocale size_preserving_trs
  by (standard, insert same_symbs, auto simp: num_symbs_is_size_funs_terms_ms_vars_term_ms)

lemma rstep_symbs_mset_eq:
  assumes "(s, t) \<in> rstep R"
  shows "funs_term_mset s = funs_term_mset t \<and> vars_term_mset s = vars_term_mset t"
using assms and same_symbs
by (induct)
   (auto simp: vars_term_ms_ctxt_apply funs_term_mset_conv funs_term_ms_ctxt_apply
               vars_term_mset_conv)

lemma rsteps_symbs_mset_eq:
  assumes "(s, t) \<in> (rstep R)\<^sup>*"
  shows "funs_term_mset s = funs_term_mset t \<and> vars_term_mset s = vars_term_mset t"
using assms by (induct) (auto dest: rstep_symbs_mset_eq)

inductive terms_n for F V
where
  Var: "x \<in> V \<Longrightarrow> terms_n F V (Suc n) (Var x)"
| Fun: "f \<in> F \<Longrightarrow> length ts = length ss \<Longrightarrow> sum_list ss \<le> n \<Longrightarrow>
    \<forall>i<length ss. ss ! i \<le> n \<and> ss ! i > 0 \<Longrightarrow>
    \<forall>i<length ss. terms_n F V (ss ! i) (ts ! i) \<Longrightarrow>
    terms_n F V (Suc n) (Fun f ts)"

lemma terms_n_0 [simp]:
  "{t. terms_n F V 0 t} = {}"
proof -
  { fix t have "terms_n F V 0 t \<Longrightarrow> False" by (auto elim: terms_n.cases) }
  then show ?thesis by auto
qed

lemma terms_n_Suc:
  "{t. terms_n F V (Suc n) t} = {Var x | x. x \<in> V} \<union>
    {Fun f ts | f ts ss. f \<in> F \<and> sum_list ss \<le> n \<and> length ts = length ss \<and>
      (\<forall>i<length ss. ss ! i \<le> n \<and> ss ! i > 0) \<and> (\<forall>i<length ss. terms_n F V (ss ! i) (ts ! i))}"
by (auto elim!: terms_n.cases intro: terms_n.intros)

lemma terms_n_mono:
  assumes "m \<le> n" and "terms_n F V m t"
  shows "terms_n F V n t"
using assms(2, 1) by (induct; cases n) (auto intro!: terms_n.intros)

lemma sum_list_le_length:
  assumes "sum_list xs \<le> n" and "\<forall>i<length xs. xs ! i > 0"
  shows "length xs \<le> n"
using assms
proof (induct xs arbitrary: n)
  case (Cons x xs)
  then show ?case
    by (cases x; cases n) (auto simp: nth_Cons dest!: add_leD2 split: nat.splits, metis Suc_mono)
qed simp

lemma finite_terms_n:
  assumes "finite F" and "finite V"
  shows "finite {t. terms_n F V n t}"
using assms
proof (induct n rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case [simp]: (Suc n')
    let ?P = "\<lambda>ts ss. sum_list ss \<le> n' \<and> length ts = length ss \<and>
      (\<forall>i<length ss. ss ! i \<le> n' \<and> ss ! i > 0) \<and> (\<forall>i<length ss. terms_n F V (ss ! i) (ts ! i))"
    let ?T = "{ts | ts ss. ?P ts ss}"
    have "?T \<subseteq> {ts. set ts \<subseteq> {t. terms_n F V n' t} \<and> length ts \<le> n'}"
      using terms_n_mono [of _ n'] by (auto simp: in_set_conv_nth sum_list_le_length) blast
    moreover have "finite \<dots>" using less by (auto intro: finite_lists_length_le)
    ultimately have "finite ?T" by (auto intro: finite_subset)
    then have "finite (F \<times> ?T)"
      using \<open>finite F\<close> by (auto intro: finite_cartesian_product)
    moreover have "{Fun f ts | f ts ss. f \<in> F \<and> ?P ts ss} = (\<lambda>(f, ts). Fun f ts) ` (F \<times> ?T)" by (auto)
    ultimately have "finite {Fun f ts | f ts ss. f \<in> F \<and> ?P ts ss}" by simp
    then show ?thesis using less by (simp add: terms_n_Suc)
  qed simp
qed

lemma size_funs_term_list_mset [simp]:
  "size (funs_term_list_mset ts) = (\<Sum>t\<leftarrow>ts. size (funs_term_mset t))"
by (induct ts) simp_all

lemma size_vars_term_list_mset [simp]:
  "size (vars_term_list_mset ts) = (\<Sum>t\<leftarrow>ts. size (vars_term_mset t))"
by (induct ts) simp_all

lemma size_funs_term_mset_ground [simp]:
  assumes "vars_term_mset t = {#}"
  shows "size (funs_term_mset t) > 0"
using assms by (induct t) simp_all

lemma sum_list_le_imp_nth_le:
  assumes "sum_list xs \<le> (n::nat)" and "i < length xs"
  shows "xs ! i \<le> n"
using assms and elem_le_sum_list
by (induct xs arbitrary: n) (force simp: nth_Cons split: nat.splits)+

lemma set_mset_funs_term_list_mset [simp]:
  "set_mset (funs_term_list_mset ts) = \<Union> (set (map (set_mset \<circ> funs_term_mset) ts))"
by (induct ts) simp_all

lemma set_mset_vars_term_list_mset [simp]:
  "set_mset (vars_term_list_mset ts) = \<Union> (set (map (set_mset \<circ> vars_term_mset) ts))"
by (induct ts) simp_all

lemma size_symbs_mset_eq_terms_n:
  assumes "set_mset (funs_term_mset t) \<subseteq> F" and "set_mset (vars_term_mset t) \<subseteq> V"
    and "size (funs_term_mset t) + size (vars_term_mset t) \<le> n"
  shows "terms_n F V n t"
using assms
proof (induct t arbitrary: n)
  case (Var x)
  then show ?case by (cases n) (auto intro: terms_n.intros)
next
  case (Fun f ts)
  let ?ss = "map (\<lambda>t. size (funs_term_mset t) + size (vars_term_mset t)) ts"
  have "\<forall>i<length ts. terms_n F V (?ss ! i) (ts ! i)" using Fun by (auto simp: UN_subset_iff)
  then show ?case
    using Fun and sum_list_le_imp_nth_le [of ?ss]
    by (cases n) (auto simp: sum_list_addf intro!: terms_n.Var terms_n.Fun [of f F ts ?ss])
qed

lemma reachable_subset:
  "{t. (s, t) \<in> (rstep R)\<^sup>*} \<subseteq>
    {t. funs_term_mset s = funs_term_mset t \<and> vars_term_mset s = vars_term_mset t}"
by (auto simp: rsteps_symbs_mset_eq)

lemma finite_reachable:
  "finite {t. (s, t) \<in> (rstep R)\<^sup>*}" (is "finite ?A")
proof (rule finite_subset)
  let ?F = "set_mset (funs_term_mset s)"
  let ?V = "set_mset (vars_term_mset s)"
  let ?n = "size (funs_term_mset s) + size (vars_term_mset s)"
  have "{t. funs_term_mset s = funs_term_mset t \<and> vars_term_mset s = vars_term_mset t} \<subseteq>
    {t. terms_n ?F ?V ?n t}" by (auto intro: size_symbs_mset_eq_terms_n)
  then show "?A \<subseteq> {t. terms_n ?F ?V ?n t}" using reachable_subset by blast
  show "finite {t. terms_n ?F ?V ?n t}" by (intro finite_terms_n) simp_all
qed
end

text \<open>Extended rule for AC-symbols.\<close>
definition "ext_AC_rule f r t = (Bin f (fst r) t, Bin f (snd r) t)"

text \<open>Extended rules for A-symbols.\<close>
definition "ext_A_rules f r s t = {
  (Bin f s (fst r), Bin f s (snd r)),
  (Bin f (fst r) s, Bin f (snd r) s),
  (Bin f (Bin f s (fst r)) t, Bin f (Bin f s (snd r)) t)}"

definition "ext_AC_trs F R =
  {ext_AC_rule f r t | f r t. r \<in> R \<and> f \<in> F \<and> root (fst r) = Some (f, 2)}"

definition "ext_A_trs F R =
  \<Union>{ext_A_rules f r s t | f r s t. r \<in> R \<and> f \<in> F \<and> root (fst r) = Some (f, 2)}"

lemma ext_AC_trs_cases [consumes 1]:
  assumes "(s, t) \<in> ext_AC_trs F R"
  obtains (left) f l r u
    where "root l = Some (f, 2)" and "f \<in> F" and "(l, r) \<in> R"
    and "s = Bin f l u" and "t = Bin f r u"
using assms by (auto simp: ext_AC_trs_def ext_AC_rule_def)

lemma ext_A_trs_cases [consumes 1]:
  assumes "(s, t) \<in> ext_A_trs F R"
  obtains (ext_rules) f l r u v where "(l, r) \<in> R" and "f \<in> F"
    and "root l = Some (f, 2)" and "(s, t) \<in> ext_A_rules f (l, r) u v"
using assms by (auto simp: ext_A_trs_def)

lemma ext_A_rules_cases [consumes 1]:
  assumes "(s, t) \<in> ext_A_rules f (l, r) u v"
  obtains (left) "s = Bin f l u" and "t = Bin f r u"
  | (right) "s = Bin f u l" and "t = Bin f u r"
  | (middle) "s = Bin f (Bin f u l) v" and "t = Bin f (Bin f u r) v"
using assms by (auto simp: ext_A_rules_def)

lemma size_preserving_AC_trs: "size_preserving_trs (AC_trs A C)"
by (standard) (auto simp: AC_trs_def A_trs_def A_rules_def C_rules_def ac_simps)

lemma symbol_preserving_AC_trs: "symbol_preserving_trs (AC_trs A C)"
by (standard) (auto simp: AC_trs_def A_trs_def A_rules_def C_rules_def ac_simps)

locale aoc_rewriting =
  fixes F\<^sub>A F\<^sub>C :: "'f set"
begin

abbreviation "AOCEQ \<equiv> (acstep F\<^sub>A F\<^sub>C)\<^sup>\<leftrightarrow>\<^sup>*"

abbreviation aoceq :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<sim>\<^sub>A\<^sub>\<or>\<^sub>C" 50)
where
  "s \<sim>\<^sub>A\<^sub>\<or>\<^sub>C t \<equiv> (s, t) \<in> AOCEQ"

definition "relaoc R = relto (rstep R) AOCEQ"

lemma ctxt_closed_relac: "ctxt.closed (relaoc R)"
unfolding relaoc_def by (rule ctxt.closed_relto [OF ctxt_closed_rstep ctxt.closed_conversion], auto) 

lemma relaoc_empty [simp]: "F\<^sub>A = {} \<Longrightarrow> F\<^sub>C = {} \<Longrightarrow> relaoc R = rstep R"
unfolding relaoc_def by auto

definition "ext_trs R = ext_AC_trs (F\<^sub>A \<inter> F\<^sub>C) R \<union> ext_A_trs (F\<^sub>A - F\<^sub>C) R"

lemma ext_trs_cases [consumes 1]:
  assumes "(s, t) \<in> ext_trs R"
  obtains (AC) f where "root s = Some (f, 2)" and "f \<in> F\<^sub>A \<inter> F\<^sub>C" and "(s, t) \<in> ext_AC_trs (F\<^sub>A \<inter> F\<^sub>C) R"
    | (A_only) f where "root s = Some (f, 2)" and "f \<in> F\<^sub>A - F\<^sub>C" and "(s, t) \<in> ext_A_trs (F\<^sub>A - F\<^sub>C) R"
proof -
  consider "(s, t) \<in> ext_AC_trs (F\<^sub>A \<inter> F\<^sub>C) R" | "(s, t) \<in> ext_A_trs (F\<^sub>A - F\<^sub>C) R"
    using assms by (auto simp: ext_trs_def)
  then show ?thesis
  proof (cases)
    case 1
    then obtain f where root: "root s = Some (f, 2)" by (auto elim: ext_AC_trs_cases)
    then show ?thesis by (rule that(1)) (insert 1 root, auto elim!: ext_AC_trs_cases)
  next
    case 2
    then obtain f where root: "root s = Some (f, 2)" by (auto elim!: ext_A_trs_cases ext_A_rules_cases)
    then show ?thesis by (rule that(2)) (insert 2 root, auto elim!: ext_A_trs_cases ext_A_rules_cases)
  qed
qed

lemma rrstep_ext_A_trs_cases [consumes 2]:
  assumes "(s, t) \<in> rrstep (ext_A_trs F R)" and "root s = Some (f, 2)"
  obtains (left) u v w where "root u = Some (f, 2)" and "f \<in> F" and "(u, v) \<in> rrstep R"
    and "s = Bin f u w" and "t = Bin f v w"
  | (right) u v w where "root u = Some (f, 2)" and "f \<in> F" and "(u, v) \<in> rrstep R"
    and "s = Bin f w u" and "t = Bin f w v"
  | (middle) u v w x where "root u = Some (f, 2)" and "f \<in> F" and "(u, v) \<in> rrstep R"
    and "s = Bin f (Bin f w u) x" and "t = Bin f (Bin f w v) x"
using assms(1)
proof (cases rule: rrstepE)
  case [simp]: (1 l r \<sigma>)
  then have roots: "root l = Some (f, 2)" "root r = Some (f, 2)"
    using assms(2) by (auto simp: ext_A_trs_def ext_A_rules_def)
  show ?thesis using 1(1)
  proof (cases rule: ext_A_trs_cases)
    case (ext_rules g l' r' a b)
    then have [simp]: "g = f" using roots by (auto elim!: ext_A_rules_cases)
    show ?thesis using ext_rules(4)
    proof (cases rule: ext_A_rules_cases)
      case left
      then show ?thesis using ext_rules(1-3) by (intro that(1)) (auto, cases l', auto)
    next
      case right
      then show ?thesis using ext_rules(1-3) by (intro that(2)) (auto, cases l', auto)
    next
      case middle
      then show ?thesis using ext_rules(1-3) by (intro that(3)) (auto, cases l', auto)
    qed
  qed
qed

lemma rrstep_ext_trs_cases [consumes 2]:
  assumes "(s, t) \<in> rrstep (ext_trs R)" and "root s = Some (f, 2)"
  obtains (ext_AC_trs) "f \<in> F\<^sub>A \<inter> F\<^sub>C" and "(s, t) \<in> rrstep (ext_AC_trs (F\<^sub>A \<inter> F\<^sub>C) R)"
  | (ext_A_trs) "f \<in> F\<^sub>A - F\<^sub>C" and "(s, t) \<in> rrstep (ext_A_trs (F\<^sub>A - F\<^sub>C) R)"
using assms(1)
proof (cases rule: rrstepE)
  case [simp]: (1 l r \<sigma>)
  show ?thesis using 1(1)
  proof (cases rule: ext_trs_cases)
    case (AC f)
    show ?thesis by (rule that(1)) (insert AC 1 assms(2), cases l, auto)
  next
    case (A_only f)
    show ?thesis by (rule that(2)) (insert A_only 1 assms(2), cases l, auto)
  qed
qed

lemma rstep_ext_trs_imp_nrrstep:
  assumes "(s, t) \<in> rstep (ext_trs R)"
  shows "(s, t) \<in> nrrstep R"
using assms
  apply (rule rstepE)
  apply (auto simp: ext_AC_trs_def ext_AC_rule_def ext_trs_def)
  apply (rule_tac C = "C \<circ>\<^sub>c More f [] \<box> [ta \<cdot> \<sigma>]" and \<sigma> = \<sigma> in nrrstepI)
  apply assumption
  apply simp_all
  apply (case_tac C) apply auto
  apply (auto simp: ext_A_trs_def ext_A_rules_def)
  apply (rule_tac C = "C \<circ>\<^sub>c More f [sa \<cdot> \<sigma>] \<box> []" and \<sigma> = \<sigma> in nrrstepI)
  apply assumption
  apply simp_all
  apply (case_tac C) apply auto
  apply (rule_tac C = "C \<circ>\<^sub>c More f [] \<box> [sa \<cdot> \<sigma>]" and \<sigma> = \<sigma> in nrrstepI)
  apply assumption
  apply simp_all
  apply (case_tac C) apply auto
  apply (rule_tac C = "C \<circ>\<^sub>c More f [] (More f [sa \<cdot> \<sigma>] \<box> []) [ta \<cdot> \<sigma>]" and \<sigma> = \<sigma> in nrrstepI)
  apply assumption
  apply simp_all
  apply (case_tac C) apply auto
done

lemma finite_AOCEQ: "finite {t. s \<sim>\<^sub>A\<^sub>\<or>\<^sub>C t}"
using symbol_preserving_trs.finite_reachable [OF symbol_preserving_AC_trs, of s F\<^sub>A F\<^sub>C]
by (metis conversion_def symcl_acstep)

end

locale ac_rewriting =
  fixes F :: "'f set" \<comment> \<open>AC symbols\<close>
begin

abbreviation "ACEQ \<equiv> (acstep F F)\<^sup>\<leftrightarrow>\<^sup>*"

abbreviation aceq :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<sim>\<^sub>A\<^sub>C" 50)
where
  "s \<sim>\<^sub>A\<^sub>C t \<equiv> (s, t) \<in> ACEQ"

definition "relac R = relto (rstep R) ACEQ"

end

sublocale ac_rewriting \<subseteq> aoc_rewriting F F
  rewrites "relaoc R = relac R"
    and "ext_trs R = ext_AC_trs F R"
by (auto simp: aoc_rewriting.relaoc_def relac_def
               aoc_rewriting.ext_trs_def ext_AC_trs_def ext_A_trs_def)

context ac_rewriting
begin

inductive_set reacstep :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs" for R
where
  "\<And>l r C \<sigma>. (l, r) \<in> R \<Longrightarrow> s \<sim>\<^sub>A\<^sub>C l \<cdot> \<sigma> \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> reacstep R"

lemma reacstep_ctxt:
  "(s, t) \<in> reacstep R \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> reacstep R"
by (induct rule: reacstep.induct) (metis reacstep.intros ctxt_ctxt)

lemma reacstep_subset_ACEQ_rstep:
  fixes R :: "('f, 'v) trs"
  shows "reacstep R \<subseteq> ACEQ O rstep R"
proof (intro subrelI)
  fix s t :: "('f, 'v) term" assume "(s, t) \<in> reacstep R"
  then obtain l r C \<sigma> u where "(l, r) \<in> R"
    and "u \<sim>\<^sub>A\<^sub>C l \<cdot> \<sigma>" and "s = C\<langle>u\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by (rule reacstep.cases)
  moreover then have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep R" by blast
  ultimately show "(s, t) \<in> ACEQ O rstep R"
    using ctxt.closed_conversion [OF ctxt_closed_rstep, of "AC_rules F F", THEN ctxt.closedD]
    by (auto)
qed

definition "ext R = R \<union> ext_AC_trs F R"

lemma extE [consumes 1]:
  assumes "(s, t) \<in> ext R"
  obtains (rule) "(s, t) \<in> R"
  | (ext_AC_rule) f u v r w where "f \<in> F" and "(Bin f u v, r) \<in> R"
    and "s = Bin f (Bin f u v) w" and "t = Bin f r w"
using assms apply (auto simp: ext_def ext_AC_rule_def ext_AC_trs_def)
apply (case_tac a)
apply (simp_all)
by (metis (no_types, lifting) One_nat_def Suc_1 Suc_length_conv length_0_conv)

lemma rstep_ext [simp]:
  "rstep (ext R) = rstep R"
  by (auto dest: rstep_ext_trs_imp_nrrstep nrrstep_imp_rstep simp: ext_def rstep_simps)

lemma rstep_subset_reacstep_ext_ACEQ:
  "rstep R \<subseteq> reacstep (ext R) O ACEQ"
proof
  fix s t assume "(s, t) \<in> rstep R"
  then have "(s, t) \<in> reacstep (ext R)" by (auto simp: ext_def intro: reacstep.intros)
  then show "(s, t) \<in> reacstep (ext R) O ACEQ" by blast
qed

(*NOTE: this lemma does not hold for AOCEQ*)
lemma ACEQ_eq_acsteps:
  "ACEQ = (acstep F F)\<^sup>*"
proof (intro equalityI subrelI)
  fix s t :: "('f, 'v) term" assume "s \<sim>\<^sub>A\<^sub>C t"
  then show "(s, t) \<in> (acstep F F)\<^sup>*"
    unfolding conversion_def
  proof (induct)
    case (step t u)
    show ?case
      using \<open>(t, u) \<in> (acstep F F)\<^sup>\<leftrightarrow>\<close>
    proof
      assume "(t, u) \<in> (acstep F F)\<inverse>"
      then have "(u, t) \<in> astep F \<or> (u, t) \<in> cstep F" by (auto simp: AC_rules_def)
      then show ?thesis
      proof
        assume "(u, t) \<in> cstep F"
        then have "(t, u) \<in> cstep F" by (force simp: C_rules_def)
        then show ?thesis using step by (auto simp: AC_rules_def intro: rtrancl_trans)
      next
        assume "(u, t) \<in> astep F"
        then obtain C \<sigma> and f and a b c :: "('f, 'v) term"
          where f: "f \<in> F" and "A_rule f a b c \<in> A_rules F"
          and u: "u = C\<langle>Bin f (Bin f a b) c \<cdot> \<sigma>\<rangle>"
          and t: "t = C\<langle>Bin f a (Bin f b c) \<cdot> \<sigma>\<rangle>" by (auto simp: A_rules_def) 
        have "(Bin f a (Bin f b c), Bin f (Bin f c b) a) \<in> (acstep F F)\<^sup>*"
          using C_rule_cstep [OF f, of "More f [a] \<box> []" b c]
          and C_rule_cstep [OF f, of \<box> a "Bin f c b"]
          by (force dest: cstep_imp_acsteps [of _ _ F F])
        moreover have "(Bin f (Bin f c b) a, Bin f c (Bin f b a)) \<in> (acstep F F)\<^sup>*"
          using A_rule_astep [OF f, of \<box> c b a] by (simp add: astep_imp_acsteps)
        moreover have "(Bin f c (Bin f b a), Bin f (Bin f a b) c) \<in> (acstep F F)\<^sup>*"
          using C_rule_cstep [OF f, of "More f [c] \<box> []" b a]
          and C_rule_cstep [OF f, of \<box> c "Bin f a b"]
          by (force dest: cstep_imp_acsteps [of _ _ F F])
        ultimately have "(Bin f a (Bin f b c), Bin f (Bin f a b) c) \<in> (acstep F F)\<^sup>*" by (auto)
        then have "(t, u) \<in> (acstep F F)\<^sup>*"
          unfolding t u by (blast intro: rsteps_closed_subst rsteps_closed_ctxt)
        with step show ?thesis by auto
      qed
    qed (insert step, auto)
  qed simp
qed auto

lemma ACEQ_ctxt: "(s, t) \<in> ACEQ \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> ACEQ"
by (simp add: ACEQ_eq_acsteps rsteps_closed_ctxt)

lemma Bin_ACEQ:
  assumes "(Bin f s t, u) \<in> ACEQ"
  shows "\<exists>v w. u = Bin f v w"
using assms unfolding ACEQ_eq_acsteps
by (induct "Bin f s t" u arbitrary: s t) (auto dest: Bin_acstep)

lemma ACEQ_eq_converse_a_Un_c_steps:
  "ACEQ = ((astep F)\<inverse> \<union> cstep F)\<^sup>*"
by (metis ACEQ_eq_acsteps acstep_eq_astep_Un_cstep converse_Un
          converse_cstep conversion_converse rtrancl_converse)

lemma ACEQ_rstep_subset_reacstep_ext_ACEQ:
  fixes R :: "('f, 'v) trs"
  assumes vc: "\<forall>(l, r) \<in> R. is_Fun l" "\<forall>r \<in> R. \<exists>x. x \<notin> vars_rule r"
  shows "ACEQ O rstep R \<subseteq> reacstep (ext R) O ACEQ"
proof -
  let ?AC = "(astep F)\<inverse> \<union> cstep F"
  have *: "?AC = rstep ((A_rules F)\<inverse> \<union> C_rules F)" by (auto)
  { fix n
    have "?AC ^^ n O rstep R \<subseteq> reacstep (ext R) O ACEQ"
    proof (induct n)
      case 0
      then show ?case using rstep_subset_reacstep_ext_ACEQ by simp
    next
      case (Suc n)
      then have "?AC O ?AC ^^ n O rstep R \<subseteq> ?AC O reacstep (ext R) O ACEQ" by blast
      moreover have "?AC O reacstep (ext R) \<subseteq> reacstep (ext R) O ACEQ"
      proof -
        { fix s t u :: "('f, 'v) term"
          assume "(s, t) \<in> ?AC" and "(t, u) \<in> reacstep (ext R)"
          then obtain C C' \<sigma> \<sigma>' and l r l' r' t' :: "('f, 'v) term"
            where rule: "(l, r) \<in> (A_rules F)\<inverse> \<union> C_rules F" and rule': "(l', r') \<in> ext R"
            and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t1: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
            and ac: "t' \<sim>\<^sub>A\<^sub>C l' \<cdot> \<sigma>'" and t2: "t = C'\<langle>t'\<rangle>" and u: "u = C'\<langle>r' \<cdot> \<sigma>'\<rangle>"
            unfolding * by (force elim!: rstepE elim: reacstep.cases)
          have s_mctxt: "s = fill_holes (mctxt_of_ctxt C) [l \<cdot> \<sigma>]" by (simp add: s)
          have u_mctxt: "u = fill_holes (mctxt_of_ctxt C') [r' \<cdot> \<sigma>']" by (simp add: u)
          have reacstep: "(\<box>\<langle>t'\<rangle>, \<box>\<langle>r' \<cdot> \<sigma>'\<rangle>) \<in> reacstep (ext R)"
            using rule' and ac by (intro reacstep.intros) (auto)
          have ACEQ: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ACEQ"
            using rule unfolding acstep_eq_astep_Un_cstep by (force simp: conversion_def)
          have "(s, u) \<in> reacstep (ext R) O ACEQ"
            using t1 t2
          proof (cases rule: two_subterms_cases)
            case eq
            then have "l \<cdot> \<sigma> \<sim>\<^sub>A\<^sub>C l' \<cdot> \<sigma>'"
              using rule and ac
              unfolding ACEQ_eq_converse_a_Un_c_steps *
              by (metis converse_rtrancl_into_rtrancl rstep_rule rstep_subst)
            with \<open>C = C'\<close> have "(s, u) \<in> reacstep (ext R)"
              using rule' by (auto simp: s u reacstep.intros)
            then show ?thesis by blast
          next
            case [simp]: (nested1 D)
            have "D\<langle>l \<cdot> \<sigma>\<rangle> \<sim>\<^sub>A\<^sub>C D\<langle>r \<cdot> \<sigma>\<rangle>" using rule by (auto simp: A_rules_def C_rules_def)
            moreover have "D\<langle>r \<cdot> \<sigma>\<rangle> = t'" using t1 and t2 by simp
            ultimately have "D\<langle>l \<cdot> \<sigma>\<rangle> \<sim>\<^sub>A\<^sub>C l' \<cdot> \<sigma>'" using ac by (auto dest: rtrancl_trans)
            then have "(s, u) \<in> reacstep (ext R)"
              using rule' by (auto simp: s u intro: reacstep.intros)
            then show ?thesis by blast
          next
            case [simp]: (nested2 D)
            have reacstep: "\<And>C. (C\<langle>t'\<rangle>, C\<langle>r' \<cdot> \<sigma>'\<rangle>) \<in> reacstep (ext R)"
              using ac and rule' by (auto intro: reacstep.intros)
            show ?thesis using rule
            proof
              assume "(l, r) \<in> C_rules F"
              then obtain g x y where "g \<in> F" and [simp]: "l = Bin g x y" "r = Bin g y x"
                by (auto simp: C_rules_def)
              have "D\<langle>t'\<rangle> = Bin g (y \<cdot> \<sigma>) (x \<cdot> \<sigma>)" using t1 and t2 by (simp)
              with \<open>D \<noteq> \<box>\<close> show ?thesis
              proof (cases rule: ctxt_apply_term_Bin_cases)
                case [simp]: (left D')
                have "(D'\<langle>t'\<rangle>, D'\<langle>r' \<cdot> \<sigma>'\<rangle>) \<in> reacstep (ext R)"
                  using ac and rule' by (auto intro: reacstep.intros)
                have "(s, C\<langle>Fun g [x \<cdot> \<sigma>, D'\<langle>r' \<cdot> \<sigma>'\<rangle>]\<rangle>) \<in> reacstep (ext R)"
                  using reacstep_ctxt [where C = "C \<circ>\<^sub>c More g [x \<cdot> \<sigma>] \<box> []"]
                  and reacstep by (auto simp: s)
                moreover have "(C\<langle>Fun g [x \<cdot> \<sigma>, D'\<langle>r' \<cdot> \<sigma>'\<rangle>]\<rangle>, u) \<in> ACEQ"
                  using \<open>g \<in> F\<close> by (auto simp: u intro!: ACEQ_ctxt)
                ultimately show ?thesis by blast
              next
                case [simp]: (right D')
                have "(s, C\<langle>Fun g [D'\<langle>r' \<cdot> \<sigma>'\<rangle>, y \<cdot> \<sigma>]\<rangle>) \<in> reacstep (ext R)"
                  using reacstep_ctxt [where C = "C \<circ>\<^sub>c More g [] \<box> [y \<cdot> \<sigma>]"]
                  and reacstep by (auto simp: s)
                moreover have "(C\<langle>Fun g [D'\<langle>r' \<cdot> \<sigma>'\<rangle>, y \<cdot> \<sigma>]\<rangle>, u) \<in> ACEQ"
                  using \<open>g \<in> F\<close> by (auto simp: u intro!: ACEQ_ctxt)
                ultimately show ?thesis by blast
              qed
            next
              assume "(l, r) \<in> (A_rules F)\<inverse>"
              then obtain g x y z where "g \<in> F"
                and [simp]: "l = Bin g x (Bin g y z)" "r = Bin g (Bin g x y) z"
                by (auto simp: A_rules_def)
              have "D\<langle>t'\<rangle> = Bin g (Bin g (x \<cdot> \<sigma>) (y \<cdot> \<sigma>)) (z \<cdot> \<sigma>)" using t1 and t2 by simp
              with \<open>D \<noteq> \<box>\<close> show ?thesis
              proof (cases rule: ctxt_apply_term_Bin_cases)
                case [simp]: (right D')
                have "(s, C\<langle>Fun g [x \<cdot> \<sigma>, Bin g (y \<cdot> \<sigma>) (D'\<langle>r' \<cdot> \<sigma>'\<rangle>)]\<rangle>) \<in> reacstep (ext R)"
                  using reacstep_ctxt [where C = "C \<circ>\<^sub>c More g [x \<cdot> \<sigma>] (More g [y \<cdot> \<sigma>] \<box> []) []"]
                  and reacstep by (auto simp: s)
                moreover have "(C\<langle>Fun g [x \<cdot> \<sigma>, Bin g (y \<cdot> \<sigma>) (D'\<langle>r' \<cdot> \<sigma>'\<rangle>)]\<rangle>, u) \<in> ACEQ"
                  using \<open>g \<in> F\<close> by (auto simp: u intro!: ACEQ_ctxt)
                ultimately show ?thesis by blast
              next
                case (left D')
                note * = this
                show ?thesis
                proof (cases "D' = \<box>")
                  case False
                  then show ?thesis using left(2) [symmetric]
                  proof (cases rule: ctxt_apply_term_Bin_cases)
                    case [simp]: (left D'')
                    have "(s, C\<langle>Fun g [D''\<langle>r' \<cdot> \<sigma>'\<rangle>, Fun g [y \<cdot> \<sigma>, z \<cdot> \<sigma>]]\<rangle>) \<in> reacstep (ext R)"
                      using reacstep_ctxt [where C = "C \<circ>\<^sub>c More g [] \<box> [Fun g [y \<cdot> \<sigma>, z \<cdot> \<sigma>]]"]
                      and reacstep by (auto simp: s)
                    moreover have "(C\<langle>Fun g [D''\<langle>r' \<cdot> \<sigma>'\<rangle>, Fun g [y \<cdot> \<sigma>, z \<cdot> \<sigma>]]\<rangle>, u) \<in> ACEQ"
                      using \<open>g \<in> F\<close> by (auto simp: u * intro!: ACEQ_ctxt)
                    ultimately show ?thesis by blast
                  next
                    case [simp]: (right D'')
                    have "(D''\<langle>t'\<rangle>, D''\<langle>r' \<cdot> \<sigma>'\<rangle>) \<in> reacstep (ext R)"
                      using ac and rule' by (auto intro: reacstep.intros)
                    have "(s, C\<langle>Fun g [x \<cdot> \<sigma>, Fun g [D''\<langle>r' \<cdot> \<sigma>'\<rangle>, z \<cdot> \<sigma>]]\<rangle>) \<in> reacstep (ext R)"
                      using reacstep_ctxt [where C = "C \<circ>\<^sub>c More g [x \<cdot> \<sigma>] (More g [] \<box> [z \<cdot> \<sigma>]) []"]
                      and reacstep by (auto simp: s)
                    moreover have "(C\<langle>Fun g [x \<cdot> \<sigma>, Fun g [D''\<langle>r' \<cdot> \<sigma>'\<rangle>, z \<cdot> \<sigma>]]\<rangle>, u) \<in> ACEQ"
                      using \<open>g \<in> F\<close> by (auto simp: u * intro!: ACEQ_ctxt)
                    ultimately show ?thesis by blast
                  qed
                next
                  case [simp]: True
                  have t': "t' = Bin g (x \<cdot> \<sigma>) (y \<cdot> \<sigma>)" by (simp add: *)
                  show ?thesis using rule'
                  proof (cases rule: extE)
                    case [simp]: (ext_AC_rule h l\<^sub>1 l\<^sub>2 r'' v)
                    let ?l'' = "Bin g l\<^sub>1 l\<^sub>2"
                    have [simp]: "h = g" using ac by (auto dest: Bin_ACEQ simp: t')
                    have rule: "(?l'', r'') \<in> R" using ext_AC_rule by simp
                    from vc [THEN bspec, OF rule] obtain w
                      where w: "w \<notin> vars_rule (?l'', r'')" by auto
                    have *: "Bin g (x \<cdot> \<sigma>) (y \<cdot> \<sigma>) \<sim>\<^sub>A\<^sub>C Bin g ?l'' v \<cdot> \<sigma>'"
                      using ac by (simp add: t')
                    have **: "(Bin g ?l'' (Var w), Bin g r'' (Var w)) \<in> ext R"
                      using \<open>g \<in> F\<close> and rule by (auto simp: ext_def ext_AC_rule_def ext_AC_trs_def)
                    let ?\<sigma> = "\<lambda>x. if x = w then Bin g (v \<cdot> \<sigma>') (z \<cdot> \<sigma>) else \<sigma>' x"
                    have [simp]: "l\<^sub>1 \<cdot> ?\<sigma> = l\<^sub>1 \<cdot> \<sigma>'" "l\<^sub>2 \<cdot> ?\<sigma> = l\<^sub>2 \<cdot> \<sigma>'" "r'' \<cdot> ?\<sigma> = r'' \<cdot> \<sigma>'"
                      using w by (auto simp: term_subst_eq_conv vars_defs)
                    have "(Fun g [x \<cdot> \<sigma>, Fun g [y \<cdot> \<sigma>, z \<cdot> \<sigma>]], Fun g [Fun g [x \<cdot> \<sigma>, y \<cdot> \<sigma>], z \<cdot> \<sigma>]) \<in> ACEQ"
                      using \<open>g \<in> F\<close> by (auto)
                    moreover have "(Fun g [Fun g [x \<cdot> \<sigma>, y \<cdot> \<sigma>], z \<cdot> \<sigma>], Bin g (Bin g ?l'' v \<cdot> \<sigma>') (z \<cdot> \<sigma>)) \<in> ACEQ"
                      using ACEQ_ctxt [OF *, where C = "More g [] \<box> [z \<cdot> \<sigma>]"] by auto
                    moreover have "(Bin g (Bin g ?l'' v \<cdot> \<sigma>') (z \<cdot> \<sigma>), Bin g ?l'' (Var w) \<cdot> ?\<sigma>) \<in> ACEQ"
                      using \<open>g \<in> F\<close> by auto
                    ultimately have "(Fun g [x \<cdot> \<sigma>, Fun g [y \<cdot> \<sigma>, z \<cdot> \<sigma>]], Bin g ?l'' (Var w) \<cdot> ?\<sigma>) \<in> ACEQ"
                      using \<open>g \<in> F\<close> by (auto simp: conversion_def)
                    with reacstep.intros [OF **, of _ ?\<sigma> \<box>, simplified]
                      have "(Fun g [x \<cdot> \<sigma>, Fun g [y \<cdot> \<sigma>, z \<cdot> \<sigma>]], Bin g r'' (Var w) \<cdot> ?\<sigma>) \<in> reacstep (ext R)" by simp
                    moreover have "(C\<langle>Bin g r'' (Var w) \<cdot> ?\<sigma>\<rangle>, u) \<in> ACEQ"
                      using \<open>g \<in> F\<close> by (auto simp: u left intro!: ACEQ_ctxt [where C = C])
                    ultimately show "(s, u) \<in> reacstep (ext R) O ACEQ"
                      by (auto simp: s intro: reacstep_ctxt)
                  next
                    case rule
                    with vc [THEN bspec, OF rule] and ac
                      obtain v where v: "v \<notin> vars_rule (l', r')"
                      and ext_AC_rule: "ext_AC_rule g (l', r') (Var v) \<in> ext R"
                      using \<open>g \<in> F\<close> by (cases l') (force dest!: Bin_ACEQ simp: t' ext_def ext_AC_trs_def)+
                    let ?\<sigma> = "\<lambda>x. if x = v then z \<cdot> \<sigma> else \<sigma>' x"
                    have [simp]: "l' \<cdot> ?\<sigma> = l' \<cdot> \<sigma>'" "r' \<cdot> ?\<sigma> = r' \<cdot> \<sigma>'"
                      using v by (auto simp: term_subst_eq_conv vars_defs)
                    have "(Bin g t' (z \<cdot> \<sigma>), fst (ext_AC_rule g (l', r') (Var v)) \<cdot> ?\<sigma>) \<in> ACEQ"
                      using ACEQ_ctxt [where C = "More g [] \<box> [z \<cdot> \<sigma>]"]
                      and ac and \<open>g \<in> F\<close> by (auto simp: ext_AC_rule_def)
                    moreover have "(Bin g (x \<cdot> \<sigma>) (Bin g (y \<cdot> \<sigma>) (z \<cdot> \<sigma>)), Bin g (Bin g (x \<cdot> \<sigma>) (y \<cdot> \<sigma>)) (z \<cdot> \<sigma>)) \<in> ACEQ"
                      using \<open>g \<in> F\<close> by (auto simp: A_rules_def)
                    ultimately have "(Bin g (x \<cdot> \<sigma>) (Bin g (y \<cdot> \<sigma>) (z \<cdot> \<sigma>)), fst (ext_AC_rule g (l', r') (Var v)) \<cdot> ?\<sigma>) \<in> ACEQ"
                      by (auto simp: ext_AC_rule_def t' intro: rtrancl_trans)
                    then have "(s, u) \<in> reacstep (ext R)"
                      using reacstep.intros [OF ext_AC_rule [unfolded ext_AC_rule_def], of _ ?\<sigma> C]
                      by (auto simp: left s u ext_AC_rule_def)
                    then show ?thesis by blast
                  qed
                qed
              qed   
            qed
          next
            case [simp]: (parallel1 E)
            have "fill_holes E [l \<cdot> \<sigma>, t'] =\<^sub>f (mctxt_of_ctxt C, concat [[l \<cdot> \<sigma>],[]])"
              unfolding parallel1 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
            then have s': "s = fill_holes E [l \<cdot> \<sigma>, t']" using s_mctxt by (auto dest: eqfE)
            have "fill_holes E [r \<cdot> \<sigma>, r' \<cdot> \<sigma>'] =\<^sub>f (mctxt_of_ctxt C', concat [[], [r' \<cdot> \<sigma>']])"
              unfolding parallel1 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
            then have u': "u = fill_holes E [r \<cdot> \<sigma>, r' \<cdot> \<sigma>']" using u_mctxt by (auto dest: eqfE)

            from ctxt_imp_mctxt [OF _ reacstep, of E "[l \<cdot> \<sigma>]" "[]"] and reacstep_ctxt [of _ _ "ext R"]
              have "(s, fill_holes E [l \<cdot> \<sigma>, r' \<cdot> \<sigma>']) \<in> reacstep (ext R)" by (simp add: s')
            moreover
            from ctxt_imp_mctxt [OF _ ACEQ, of E "[]" "[r' \<cdot> \<sigma>']"] and ACEQ_ctxt
              have "(fill_holes E [l \<cdot> \<sigma>, r' \<cdot> \<sigma>'], u) \<in> ACEQ" by (auto simp: u')
            ultimately show ?thesis by blast
          next
            case [simp]: (parallel2 E)
            have "fill_holes E [t', l \<cdot> \<sigma>] =\<^sub>f (mctxt_of_ctxt C, concat [[], [l \<cdot> \<sigma>]])"
              unfolding parallel2 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
            then have s': "s = fill_holes E [t', l \<cdot> \<sigma>]" using s_mctxt by (auto dest: eqfE)
            have "fill_holes E [r' \<cdot> \<sigma>', r \<cdot> \<sigma>] =\<^sub>f (mctxt_of_ctxt C', concat [[r' \<cdot> \<sigma>'], []])"
              unfolding parallel2 by (intro fill_holes_mctxt_sound) (auto, case_tac i, auto)
            then have u': "u = fill_holes E [r' \<cdot> \<sigma>', r \<cdot> \<sigma>]" using u_mctxt by (auto dest: eqfE)

            from ctxt_imp_mctxt [OF _ reacstep, of E "[]" "[l \<cdot> \<sigma>]"] and reacstep_ctxt [of _ _ "ext R"]
              have "(s, fill_holes E [r' \<cdot> \<sigma>', l \<cdot> \<sigma>]) \<in> reacstep (ext R)" by (simp add: s')
            moreover
            from ctxt_imp_mctxt [OF _ ACEQ, of E "[r' \<cdot> \<sigma>']" "[]"] and ACEQ_ctxt
              have "(fill_holes E [r' \<cdot> \<sigma>', l \<cdot> \<sigma>], u) \<in> ACEQ" by (auto simp: u')
            ultimately show ?thesis by blast
          qed
        }
        then show ?thesis by auto
      qed
      ultimately have "?AC ^^ Suc n O rstep R \<subseteq> reacstep (ext R) O ACEQ O ACEQ"
        by (simp only: O_assoc [symmetric] relpow_Suc) blast
      then show ?case by simp
    qed
  }
  then show ?thesis unfolding ACEQ_eq_converse_a_Un_c_steps by blast
qed

lemma relac_reacstep_conv:
  assumes "\<forall>(l, r) \<in> R. is_Fun l" and "\<forall>r \<in> R. \<exists>x. x \<notin> vars_rule r"
  shows "relac R = reacstep (ext R) O ACEQ"
proof -
  have "relac R = ACEQ O rstep R O ACEQ" by (simp add: relac_def)
  also have "\<dots> \<subseteq> reacstep (ext R) O ACEQ O ACEQ"
    using ACEQ_rstep_subset_reacstep_ext_ACEQ [OF assms] by blast
  finally have "relac R \<subseteq> reacstep (ext R) O ACEQ" by simp
  moreover have "reacstep (ext R) O ACEQ \<subseteq> (ACEQ O rstep R) O ACEQ"
    using reacstep_subset_ACEQ_rstep [of "ext R"] by (intro relcomp_mono; simp)
  ultimately show ?thesis by (auto simp: O_assoc relac_def)
qed

end

locale root_preserving_trs =
  fixes R :: "('f, 'v) trs"
  assumes rt: "(l, r) \<in> R \<Longrightarrow> eroot l = eroot r"
begin

lemma root_preservation:
  assumes "(s, t) \<in> (rstep R)\<^sup>*"
  shows "eroot s = eroot t \<and> (root t \<in> Some ` roots_trs R \<or> 
  (\<forall> i. i < num_args t \<longrightarrow> (args s ! i, args t ! i) \<in> (rstep R)\<^sup>*))"
using assms
proof (induct rule: rtrancl_induct)
  case (step t u)
  from step(2) obtain C l r \<sigma> where t: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" and u: "u = C\<langle>r \<cdot> \<sigma>\<rangle>" and lr: "(l,r) \<in> R"
    by auto
  note rt = rt[OF lr]
  from rt t u have rtu: "eroot t = eroot u" by (cases C; cases l; cases r; auto)
  then have rtu': "root t = root u" by (cases t; cases u, auto)
  show ?case 
  proof (cases "root t \<in> Some ` roots_trs R")
    case True
    with rtu rtu' step(3) show ?thesis by auto
  next
    case False
    show ?thesis
    proof (cases "is_Fun l")
      case True
      have "root l \<in> Some ` roots_rule (l,r)" using rt True unfolding roots_rule_def
        by (cases l; cases r; auto)
      with False rt t lr have "C \<noteq> \<box>" unfolding roots_trs_def 
        by (cases C; cases l, auto)
      then obtain f bef D aft where C: "C = More f bef D aft" by (cases C, auto)
      {
        fix i
        assume i: "i < num_args u"
        then have i': "i < num_args t" using rtu by (cases t; cases u, auto)
        from False step(3) i' 
        have st: "(args s ! i, args t ! i) \<in> (rstep R)\<^sup>*" by auto
        also have "(args t ! i, args u ! i) \<in> (rstep R)\<^sup>*"
          unfolding t u C using lr 
          by (cases "i = length bef", auto simp: nth_append)
        finally have "(args s ! i, args u ! i) \<in> (rstep R)\<^sup>*" .
      }
      with step(3) rtu show ?thesis by auto
    next
      case False
      with rt have l: "l = r" by (cases l; cases r; auto)
      show ?thesis using step(3) unfolding t u l by auto
    qed
  qed
qed simp

lemma roots_trs_defined: "roots_trs R = {f. defined R f}"
proof -
  {
    fix l r
    have "(l,r) \<in> R \<Longrightarrow> roots_rule (l,r) = set_option (root (fst (l, r)))"
      unfolding roots_rule_def using rt[of l r] by (cases l; cases r; auto)
  }
  then show ?thesis
    unfolding roots_trs_def defined_def 
    by (auto split: option.splits)
qed

end

lemma root_preserving_AC_trs: "root_preserving_trs (AC_trs A C)"
by (standard) (auto simp: AC_trs_def A_trs_def A_rules_def C_rules_def)

lemma (in aoc_rewriting) AOCEQ_roots:
  assumes "s \<sim>\<^sub>A\<^sub>\<or>\<^sub>C t"
  shows "root s = root t"
proof -
  interpret root_preserving_trs "AC_trs F\<^sub>A F\<^sub>C" by (rule root_preserving_AC_trs)
  have "(s, t) \<in> (rstep (AC_trs F\<^sub>A F\<^sub>C))\<^sup>*"
    using assms by (metis conversion_def symcl_acstep)
  from root_preservation [OF this] show ?thesis by (cases s; cases t; auto)
qed

lemma root_preserving_AC_rules: "root_preserving_trs (AC_rules A C)"
by (standard) (auto simp: AC_rules_def A_trs_def A_rules_def C_rules_def)

lemma (in ac_rewriting) ACEQ_roots:
  assumes "s \<sim>\<^sub>A\<^sub>C t"
  shows "root s = root t"
using root_preserving_trs.root_preservation [OF root_preserving_AC_rules assms [unfolded ACEQ_eq_acsteps]]
by (cases s; cases t; auto)

lemma root_preserving_rstep_eq:
  assumes "root_preserving_trs R"
    and RS: "rstep R = rstep S"
  shows "root_preserving_trs S"
proof -
  interpret root_preserving_trs R by fact
  show ?thesis
  proof
    fix l r
    assume "(l,r) \<in> S"
    then have "(l,r) \<in> (rstep S)\<^sup>*" by auto
    then have "(l,r) \<in> (rstep R)\<^sup>*" unfolding RS by simp
    from root_preservation[OF this]
    show "eroot l = eroot r" by auto
  qed
qed

lemma SN_acsteps_supt: "SN ((acstep A C)\<^sup>\<leftrightarrow>\<^sup>* O {\<rhd>})"
proof -
  interpret size_preserving_trs "AC_trs A C" by (rule size_preserving_AC_trs)
  have sub: "(acstep A C)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> ((acstep A C)\<^sup>\<leftrightarrow>)\<^sup>*" by auto
  show ?thesis 
    by (rule SN_subset[OF SN_suptrel], unfold suptrel_def symcl_acstep[symmetric], insert sub, auto)
qed

text \<open>Flexible notion of AC-theory, which also admits rules like f(f(x,y),z) \<rightarrow> f(z,f(y,x)).
  This shape is required for usable rules.\<close>

locale AC_theory =
  fixes E :: "('f,'v)trs"
  assumes ac_ruleD: "(l, r) \<in> E \<Longrightarrow> funs_term_ms l = funs_term_ms r"
    "(l, r) \<in> E \<Longrightarrow> vars_term_ms l = vars_term_ms r"
    "(l, r) \<in> E \<Longrightarrow> \<exists> f. funas_term l = {(f,2)} \<and> funas_term r = {(f,2)}"
begin

lemma ruleD: 
  assumes lr: "(l, r) \<in> E"
  shows "funs_term_ms l = funs_term_ms r" "vars_term_ms l = vars_term_ms r"
  "\<exists> f l1 l2 r1 r2. 
    l = Fun f [l1,l2] \<and> 
    r = Fun f [r1,r2] \<and> 
    \<Union> (funas_term ` {l1,l2,r1,r2}) \<subseteq> {(f,2)}"
  (is "?f")
proof -
  from ac_ruleD[OF lr] show "funs_term_ms l = funs_term_ms r" "vars_term_ms l = vars_term_ms r"
    by auto
  from ac_ruleD[OF lr] obtain f where 
    l: "funas_term l = {(f,2)}" and r: "funas_term r = {(f,2)}" by force
  {
    fix t :: "('f,'v)term"
    assume *: "funas_term t = {(f,2)}"
    then obtain ts where t: "t = Fun f ts" by (cases t, auto)
    with * obtain t1 t2 where "ts = [t1,t2]" by (cases ts; cases "tl ts", auto)
    with t * have "\<exists> t1 t2. t = Fun f [t1,t2] \<and> funas_term t1 \<subseteq> {(f,2)} \<and> funas_term t2 \<subseteq> {(f,2)}"
      by auto
  }
  from this[OF l] this[OF r] show ?f
    by (intro exI[of _ f], auto)
qed

lemma no_left_var: "(Var x, r) \<notin> E"
using ruleD by force

sublocale symbol_preserving_trs E using ruleD 
by (force simp: symbol_preserving_trs_def)

sublocale root_preserving_trs E 
using ruleD by (force simp: root_preserving_trs_def)

lemma SN_supt_relto: "SN (relto {\<rhd>} (rstep E))"
  by (rule SN_subset[OF SN_suptrel], unfold suptrel_def, auto)

lemma SN_supt: "SN ((rstep E)\<^sup>* O {\<rhd>})"
  by (rule SN_subset[OF SN_supt_relto], auto)

lemma rstep_root: "(s, t) \<in> rstep E \<Longrightarrow> root s = root t"
using root_preservation[of s t] by (cases s; cases t; auto)

end

locale AC_C_theory = AC_theory E for E +
  fixes F\<^sub>O\<^sub>C (* F-only C *)
  assumes  only_C_D: "(l, r) \<in> E \<Longrightarrow> root l = Some (f,2) 
    \<Longrightarrow> f \<in> F\<^sub>O\<^sub>C \<Longrightarrow> \<exists> s t. (l,r) = (Fun f [s,t], Fun f [t,s])"


lemma AC_theory_empty[simp]: "AC_theory {}" 
  by (standard, auto)

lemma AC_C_theory_empty[simp]: "AC_C_theory {} F"
  by (standard, auto)

lemma size_preserving_trs_empty[simp]: "size_preserving_trs {}"
  by (standard, auto)
  

definition is_ext_trs :: "('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "is_ext_trs R A C R\<^sub>e\<^sub>x\<^sub>t \<longleftrightarrow> (\<forall> l r f. (l, r) \<in> R \<longrightarrow> f \<in> A \<longrightarrow> root l = Some (f, 2) \<longrightarrow>
    (\<exists> x. x \<notin> vars_rule (l, r) \<and> ext_AC_rule f (l, r) (Var x) \<in> R\<^sub>e\<^sub>x\<^sub>t) \<and> 
    (f \<notin> C \<longrightarrow> (\<exists> x y z. x \<notin> vars_rule (l,r) \<and> y \<notin> vars_rule (l,r) \<and> z \<notin> vars_rule (l,r) \<and> x \<noteq> y \<and> 
        (Bin f (Var z) l, Bin f (Var z) r) \<in> R\<^sub>e\<^sub>x\<^sub>t \<and>
        (Bin f (Bin f (Var x) l) (Var y), Bin f (Bin f (Var x) r) (Var y)) \<in> R\<^sub>e\<^sub>x\<^sub>t)))" 

lemma is_ext_trsD:
  "is_ext_trs R A C R\<^sub>e\<^sub>x\<^sub>t \<Longrightarrow> (l, r) \<in> R \<Longrightarrow> f \<in> A \<Longrightarrow> root l = Some (f, 2) \<Longrightarrow>
    \<exists> x. x \<notin> vars_rule (l, r) \<and> ext_AC_rule f (l, r) (Var x) \<in> R\<^sub>e\<^sub>x\<^sub>t"
unfolding is_ext_trs_def by auto

lemma is_ext_trsD2:
  "is_ext_trs R A C R\<^sub>e\<^sub>x\<^sub>t \<Longrightarrow> (l, r) \<in> R \<Longrightarrow> f \<in> A \<Longrightarrow> f \<notin> C \<Longrightarrow> root l = Some (f, 2) \<Longrightarrow>
    \<exists> x y z. x \<noteq> y \<and> x \<notin> vars_rule (l, r) \<and> y \<notin> vars_rule (l, r) \<and> z \<notin> vars_rule (l,r) \<and>
      (Bin f (Var z) l, Bin f (Var z) r) \<in> R\<^sub>e\<^sub>x\<^sub>t \<and> 
      (Bin f (Bin f (Var x) l) (Var y), Bin f (Bin f (Var x) r) (Var y)) \<in> R\<^sub>e\<^sub>x\<^sub>t"
unfolding is_ext_trs_def by blast

context aoc_rewriting
begin

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

lemma is_ext_trs_rrstep:
  assumes R_ext: "is_ext_trs R F\<^sub>A F\<^sub>C R\<^sub>e\<^sub>x\<^sub>t"
    and st: "(s, t) \<in> rrstep (ext_trs R)"
  shows "(\<sharp> s, \<sharp> t) \<in> rrstep (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)"
proof -
  obtain l r and \<sigma> where s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" and lr: "(l, r) \<in> ext_trs R"
    using rrstepE [OF st] . 
  show ?thesis
  proof (cases "(l, r) \<in> ext_AC_trs F\<^sub>A R")
    case True
    then obtain f l' r' u where l: "l = Fun f [l', u]"
      and r: "r = Fun f [r', u]" and lr': "(l', r') \<in> R"
      and f: "f \<in> F\<^sub>A" "root l' = Some (f, 2)" by (auto simp: ext_AC_trs_def ext_AC_rule_def)
    from is_ext_trsD [OF R_ext lr' f] obtain x :: 'a where x: "x \<notin> vars_rule (l', r')"
      and "(Fun f [l',Var x], Fun f [r', Var x]) \<in> R\<^sub>e\<^sub>x\<^sub>t" by (auto simp: ext_AC_rule_def)
    then have rule: "(Fun (\<sharp> f) [l', Var x], Fun (\<sharp> f) [r', Var x]) \<in> \<sharp> R\<^sub>e\<^sub>x\<^sub>t" by (force simp: dir_image_def)
    define \<tau> where "\<tau> = (\<lambda> y. if x = y then u \<cdot> \<sigma> else \<sigma> y)"
    then have [simp]: "\<tau> x = u \<cdot> \<sigma>" by simp
    show ?thesis unfolding s t l r
      by (rule rrstepI[OF rule, of _ \<tau>], auto intro!: term_subst_eq, insert x, auto simp: \<tau>_def vars_rule_def)
  next
    case False
    with lr have "(l,r) \<in> ext_A_trs (F\<^sub>A - F\<^sub>C) R" unfolding ext_trs_def ext_AC_trs_def by auto
    from this[unfolded ext_A_trs_def ext_A_rules_def, simplified] obtain f l' r' a b where 
      choice: "(l,r) \<in> {
          (Fun f [a, l'], Fun f [a, r']), 
          (Fun f [l', a], Fun f [r', a]),
          (Fun f [Fun f [a, l'], b], Fun f [Fun f [a, r'], b])}" 
      and lr': "(l',r') \<in> R" and f: "f \<in> F\<^sub>A" "f \<notin> F\<^sub>C" "root l' = Some (f,2)" by metis
    from is_ext_trsD2[OF R_ext lr' f] obtain x y z where xy: "x \<noteq> y" "x \<notin> vars_rule (l', r')" "y \<notin> vars_rule (l', r')"
      "z \<notin> vars_rule (l',r')" 
      and rules: "(Fun f [Var z, l'], Fun f [Var z, r']) \<in> R\<^sub>e\<^sub>x\<^sub>t" 
        "(Fun f [Fun f [Var x, l'], Var y], Fun f [Fun f [Var x, r'], Var y]) \<in> R\<^sub>e\<^sub>x\<^sub>t" by auto
    define \<tau> where "\<tau> = (\<lambda> z. if z = x then a \<cdot> \<sigma> else if z = y then b \<cdot> \<sigma> else \<sigma> z)"
    define \<tau>' where "\<tau>' = (\<lambda> u. if u = z then a \<cdot> \<sigma> else \<sigma> u)"
    have id: "l' \<cdot> \<tau> = l' \<cdot> \<sigma>" "r' \<cdot> \<tau> = r' \<cdot> \<sigma>" "\<tau> x = a \<cdot> \<sigma>" "\<tau> y = b \<cdot> \<sigma>"
       and id2: "l' \<cdot> \<tau>' = l' \<cdot> \<sigma>" "r' \<cdot> \<tau>' = r' \<cdot> \<sigma>" "\<tau>' z = a \<cdot> \<sigma>"
      unfolding \<tau>_def \<tau>'_def using xy
      by (auto intro!: term_subst_eq simp: vars_rule_def)
    note id[symmetric, simp]
    {
      assume "(l,r) = (Fun f [l', a], Fun f [r', a])"
      with f lr' have "(l,r) \<in> ext_AC_trs F\<^sub>A R" unfolding ext_AC_trs_def ext_AC_rule_def by auto
      with False have ?thesis by simp
    }
    moreover
    {
      assume id: "(l,r) = (Fun f [a, l'], Fun f [a, r'])"
      from rules(1) have rule: "(Fun (\<sharp> f) [Var z, l'], Fun (\<sharp> f) [Var z, r']) \<in> \<sharp> R\<^sub>e\<^sub>x\<^sub>t" by (force simp: dir_image_def)
      have ?thesis unfolding s t
        by (rule rrstepI[OF rule, of _ \<tau>'], insert id id2, auto)
    }
    moreover
    {
      assume id: "(l,r) = (Fun f [Fun f [a, l'], b], Fun f [Fun f [a, r'], b])"
      from rules(2) have rule:
        "(Fun (\<sharp> f) [Fun f [Var x, l'], Var y], Fun (\<sharp> f) [Fun f [Var x, r'], Var y]) \<in> \<sharp> R\<^sub>e\<^sub>x\<^sub>t" by (force simp: dir_image_def)
      have ?thesis unfolding s t 
        by (rule rrstepI[OF rule], insert id, auto)
    }
    ultimately show ?thesis using choice by blast
  qed
qed

end

end

lemma sym_esym_steps: "(s,t) \<in> (rstep (E\<^sup>\<leftrightarrow>))\<^sup>* \<Longrightarrow> (t,s) \<in> (rstep (E\<^sup>\<leftrightarrow>))\<^sup>*"
  unfolding rstep_simps(5) by (metis rtrancl_converseI symcl_converse)

definition symmetric_trs :: "('f,'v)trs \<Rightarrow> bool" where
  "symmetric_trs E \<equiv> E\<inverse> \<subseteq> (rstep E)\<^sup>*"

lemma symmetric_trs_sym_rstep:
  assumes sym: "symmetric_trs E"
  shows "(rstep (E\<^sup>\<leftrightarrow>))\<^sup>* = (rstep E)\<^sup>*"
proof 
  show "(rstep E)\<^sup>* \<subseteq> (rstep (E\<^sup>\<leftrightarrow>))\<^sup>*" unfolding rstep_union by regexp
  have "rstep (E\<^sup>\<leftrightarrow>) \<subseteq> (rstep E)\<^sup>*"
    by (rule rstep_subset, insert sym[unfolded symmetric_trs_def], auto)
  then show "(rstep (E\<^sup>\<leftrightarrow>))\<^sup>* \<subseteq> (rstep E)\<^sup>*" by (rule rtrancl_subset_rtrancl)
qed

lemma symmetric_trs_sym_step: assumes sym: "symmetric_trs E"
  and st: "(s,t) \<in> (rstep E)\<^sup>*" shows "(t,s) \<in> (rstep E)\<^sup>*"
  using st unfolding symmetric_trs_sym_rstep[OF sym, symmetric]
  by (rule sym_esym_steps)

end
