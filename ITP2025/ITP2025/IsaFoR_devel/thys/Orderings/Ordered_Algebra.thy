(*
Author:  Akihisa Yamada (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Ordered_Algebra
imports 
  Quasi_Order
  F_Algebra
  HOL.Lattices
begin

subsection \<open>Quasi-Ordered Algebras\<close>

text
\<open>A quasi-ordered algebra is an F-algebra whose domain is quasi-ordered.
   We cannot use @{class quasi_order} as a class since later we want to use
   arbitrary order on terms which cannot be globally fixed. Local instantiation
   would alleviate the problem.
\<close>

text \<open>Following is a syntactic locale where executable definitions should be made.\<close>
locale ord_algebra = ord less_eq less + algebra I
  for less_eq less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
begin

interpretation ord_syntax.

text\<open>Base orderings are extended over terms in the standard way.\<close>

definition less_term (infix "<\<^sub>\<A>" 50) where "s <\<^sub>\<A> t \<equiv> \<forall>\<alpha>. \<lbrakk>s\<rbrakk>\<alpha> \<sqsubset> \<lbrakk>t\<rbrakk>\<alpha>"
notation less_term (infix "<\<^sub>\<A>" 50)

definition less_eq_term (infix "\<le>\<^sub>\<A>" 50) where "s \<le>\<^sub>\<A> t \<equiv> \<forall>\<alpha>. \<lbrakk>s\<rbrakk>\<alpha> \<sqsubseteq> \<lbrakk>t\<rbrakk>\<alpha>"
notation less_eq_term (infix "\<le>\<^sub>\<A>" 50)

lemma less_termI[intro]: "(\<And>\<alpha> :: 'v \<Rightarrow> 'a. \<lbrakk>s\<rbrakk>\<alpha> \<sqsubset> \<lbrakk>t\<rbrakk>\<alpha>) \<Longrightarrow> s <\<^sub>\<A> t" by (auto simp: less_term_def)
lemma less_termE[elim]:
  assumes "s <\<^sub>\<A> t" and "(\<And>\<alpha> :: 'v \<Rightarrow> 'a. \<lbrakk>s\<rbrakk>\<alpha> \<sqsubset> \<lbrakk>t\<rbrakk>\<alpha>) \<Longrightarrow> thesis"
  shows "thesis" using assms by (auto simp: less_term_def)

lemma less_eq_termI[intro]: "(\<And>\<alpha> :: 'v \<Rightarrow> 'a. \<lbrakk>s\<rbrakk>\<alpha> \<sqsubseteq> \<lbrakk>t\<rbrakk>\<alpha>) \<Longrightarrow> s \<le>\<^sub>\<A> t" by (auto simp: less_eq_term_def)
lemma less_eq_termE[elim]:
  assumes "s \<le>\<^sub>\<A> t" and "(\<And>\<alpha> :: 'v \<Rightarrow> 'a. \<lbrakk>s\<rbrakk>\<alpha> \<sqsubseteq> \<lbrakk>t\<rbrakk>\<alpha>) \<Longrightarrow> thesis"
  shows "thesis" using assms by (auto simp: less_eq_term_def)

sublocale "term": ord "(\<le>\<^sub>\<A>)" "(<\<^sub>\<A>)".

notation(input) term.greater (infix ">\<^sub>\<A>" 50)
notation(input) term.greater_eq (infix "\<ge>\<^sub>\<A>" 50)

notation term.equiv (infix "\<simeq>\<^sub>\<A>" 50)
notation term.equiv_class ("[_]\<^sub>\<A>")

lemma equiv_termI[intro]: "(\<And>\<alpha> :: 'v \<Rightarrow> 'a. \<lbrakk>s\<rbrakk>\<alpha> \<simeq> \<lbrakk>t\<rbrakk>\<alpha>) \<Longrightarrow> s \<simeq>\<^sub>\<A> t" by auto
lemma equiv_termE[elim]:
  assumes "s \<simeq>\<^sub>\<A> t" and "(\<And>\<alpha> :: 'v \<Rightarrow> 'a. \<lbrakk>s\<rbrakk>\<alpha> \<simeq> \<lbrakk>t\<rbrakk>\<alpha>) \<Longrightarrow> thesis"
  shows "thesis" using assms by auto

lemma less_term_stable[intro]: fixes \<sigma> :: "'v \<Rightarrow> ('f,'w) term" shows "t <\<^sub>\<A> s \<Longrightarrow> t\<cdot>\<sigma> <\<^sub>\<A> s\<cdot>\<sigma>"
  by (intro less_termI, auto simp: subst_eval)

lemma less_eq_term_stable[intro]: fixes \<sigma> :: "'v \<Rightarrow> ('f,'w) term" shows "t \<le>\<^sub>\<A> s \<Longrightarrow> t\<cdot>\<sigma> \<le>\<^sub>\<A> s\<cdot>\<sigma>"
  by (intro less_eq_termI, auto simp: subst_eval)

end

locale ordered_algebra = ord_algebra + quasi_order
begin

sublocale "term": quasi_order "(\<le>\<^sub>\<A>)" "(<\<^sub>\<A>)"
  apply (unfold_locales, unfold less_term_def less_eq_term_def)
  apply (auto dest: order_trans less_trans le_less_trans less_le_trans less_imp_le)
  done

end

locale ordered_algebra_hom =
  algebra_hom hom I I' + ordered_algebra less_eq less I +
  target: ordered_algebra less_eq' less' I'
  for hom less_eq less I less_eq' less' I' +
  assumes le_hom: "less_eq a b \<Longrightarrow> less_eq' (hom a) (hom b)"
    and less_hom: "less a b \<Longrightarrow> less' (hom a) (hom b)"

locale ordered_algebra_epim = ordered_algebra_hom + algebra_epim

locale wf_algebra = ordered_algebra where I = I + wf_order
  for I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
begin

interpretation ord_syntax.

sublocale "term": wf_order "(\<le>\<^sub>\<A>) :: ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool" "(<\<^sub>\<A>)"
proof
  obtain v where "(v :: 'a) = v" by auto
  define \<alpha> where "\<alpha> \<equiv> \<lambda>x :: 'v. v"
  fix P s
  assume *: "\<And>s :: ('f,'v) term. (\<And>t. t <\<^sub>\<A> s \<Longrightarrow> P t) \<Longrightarrow> P s"
  then show "P s"
  proof(induct "\<lbrakk>s\<rbrakk>\<alpha>" arbitrary: s rule: less_induct)
    case less show ?case
    proof (rule less(2))
      fix t assume ts: "t <\<^sub>\<A> s"
      then have "\<lbrakk>t\<rbrakk>\<alpha> \<sqsubset> \<lbrakk>s\<rbrakk>\<alpha>" by auto
      from less(1)[OF this *] show "P t" by auto
    qed
  qed
qed

end

locale weak_mono = quasi_order +
  fixes f
  assumes append_Cons_le_append_Cons:
    "\<And>a b ls rs. less_eq a b \<Longrightarrow> less_eq (f (ls @ a # rs)) (f (ls @ b # rs))"
begin

interpretation ord_syntax.

lemma Cons_le_Cons[intro,simp]: "a \<sqsubseteq> b \<Longrightarrow> f (a#as) \<sqsubseteq> f (b#as)"
  using append_Cons_le_append_Cons[of _ _ "[]"] by auto

lemma weak_mono_Cons: "weak_mono less_eq less (\<lambda>as. f (a#as))"
  using append_Cons_le_append_Cons[of _ _ "a#_"] by (unfold_locales, auto)

lemma weak_mono_append_left: "weak_mono less_eq less (\<lambda>as. f (cs@as))"
  using append_Cons_le_append_Cons[of _ _ "cs@_"] by (unfold_locales, auto)

lemma weak_mono_append_right: "weak_mono less_eq less (\<lambda>as. f (as@cs))"
  using append_Cons_le_append_Cons by (unfold_locales, auto)

end

lemma (in quasi_order) weak_mono_iff_all_le:
  "weak_mono (\<le>) (<) f \<longleftrightarrow>
   (\<forall>as bs. length as = length bs \<longrightarrow> (\<forall>i < length as. as ! i \<le> bs ! i) \<longrightarrow> f as \<le> f bs)"
  (is "?l \<longleftrightarrow> ?r")
proof(intro iffI impI allI)
  fix as bs
  assume "?l" and "length as = length bs" and "\<forall>i < length as. as ! i \<le> bs ! i"
  then show "f as \<le> f bs"
  proof (induct as arbitrary: bs f)
    case (Cons a as bbs)
    then obtain b bs
      where bbs: "bbs = b#bs"
        and ab: "a \<le> b"
        and all: "\<forall>i < length as. as ! i \<le> bs ! i"
        and len: "length as = length bs"
      by (atomize(full), cases bbs, auto)
    interpret weak_mono "(\<le>)" "(<)" f using Cons(2).
    have "f (a # as) \<le> f (b # as)" using ab by auto
    also have "\<dots> \<le> f (b # bs)" using Cons(1) all len
      using weak_mono_Cons by blast
    finally show ?case unfolding bbs.
  qed simp
next
  assume r: ?r
  show ?l
  proof (unfold_locales, intro r[rule_format] allI impI)
    fix a b ls rs
    assume ab: "a \<le> b"
    fix i assume i: "i < length (ls @ a # rs)"
    show " (ls @ a # rs) ! i \<le> (ls @ b # rs) ! i"
      by(cases i "length ls" rule: linorder_cases, auto simp: ab nth_append)
  qed auto
qed

lemmas(in weak_mono) weak_mono_all_le = weak_mono_axioms[unfolded weak_mono_iff_all_le, rule_format]

locale str_mono = weak_mono +
  assumes append_Cons_less_append_Cons:
    "\<And>ls rs a b. less a b \<Longrightarrow> less (f (ls @ a # rs)) (f (ls @ b # rs))"
begin

interpretation ord_syntax.

lemma Cons_less_Cons[intro,simp]: "a \<sqsubset> b \<Longrightarrow> f (a#as) \<sqsubset> f (b#as)"
  using append_Cons_less_append_Cons[of _ _ "[]"] by auto

lemma str_mono_Cons: "str_mono less_eq less (\<lambda>as. f (a#as))"
  using append_Cons_le_append_Cons[of _ _ "a#_"] append_Cons_less_append_Cons[of _ _ "a#_"]
  by (unfold_locales, auto)

lemma str_mono_append_left: "str_mono less_eq less (\<lambda>as. f (cs@as))"
  using append_Cons_le_append_Cons[of _ _ "cs@_"] append_Cons_less_append_Cons[of _ _ "cs@_"]
  by (unfold_locales, auto)

lemma str_mono_append_right: "str_mono less_eq less (\<lambda>as. f (as@cs))"
  using append_Cons_le_append_Cons append_Cons_less_append_Cons by (unfold_locales, auto)

end

context weak_mono begin

interpretation ord_syntax.

lemma str_mono_iff_all_le_ex_less:
  "str_mono less_eq less f \<longleftrightarrow>
  (\<forall>as bs. length as = length bs \<longrightarrow>
    (\<forall>i < length as. as ! i \<sqsubseteq> bs ! i) \<longrightarrow>
    (\<exists>i < length as. as ! i \<sqsubset> bs ! i) \<longrightarrow> f as \<sqsubset> f bs)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI allI impI)
  fix as bs
  assume ?l and "length as = length bs" and "\<forall>i < length as. as ! i \<sqsubseteq> bs ! i"
  and "\<exists>i < length as. as ! i \<sqsubset> bs ! i"
  then show "f as \<sqsubset> f bs"
  proof (induct as arbitrary: bs f)
    case Nil then show ?case by auto
  next
    case (Cons a as bbs)
    from Cons.prems obtain b bs
      where bbs[simp]: "bbs = b#bs"
        and len: "length as = length bs"
      by (atomize(full), cases bbs, auto)
    from Cons.prems
    have ab: "a \<sqsubseteq> b"
      and all: "\<forall>i < length as. as ! i \<sqsubseteq> bs ! i"
      and some: "a \<sqsubset> b \<or> (\<exists>i < length as. as ! i \<sqsubset> bs ! i)" by (auto simp: ex_Suc_conv)
    interpret str_mono where f = f using Cons.prems(1) .
    from some show ?case
    proof (elim disjE)
      assume ab: "a \<sqsubset> b"
      interpret str_mono where f = "\<lambda>cs. f (a#cs)" by (rule str_mono_Cons)
      have "f (a#as) \<sqsubseteq> f (a#bs)" using all len by (simp add: weak_mono_all_le)
      also have "\<dots> \<sqsubset> f (b#bs)" using ab by auto
      finally show ?thesis by simp
    next
      assume "\<exists>i < length as. as ! i \<sqsubset> bs ! i"
      from Cons.hyps[OF _ len all this, of "\<lambda>cs. f (a#cs)"] str_mono_Cons
      have "f (a # as) \<sqsubset> f (a # bs)" by auto
      also have "\<dots> \<sqsubseteq> f (b # bs)" using ab by auto
      finally show ?thesis by simp
    qed
  qed
next
  assume r: ?r
  show ?l
    apply unfold_locales apply (intro r[rule_format])
    apply simp
    apply (metis append_Cons_nth_not_middle eq_imp_le less_imp_le nth_append_length)
    by (metis add_Suc_right length_Cons length_append less_add_Suc1 nth_append_length)
qed

end

lemmas(in str_mono) str_mono_all_le_ex_less =
  str_mono_axioms[unfolded str_mono_iff_all_le_ex_less, rule_format]

subsection \<open>Weakly monotone algebra\<close>

locale weak_mono_algebra = ordered_algebra +
  assumes weak_mono: "\<And>f. weak_mono less_eq less (I f)"
begin

interpretation ord_syntax.

sublocale weak_mono where f = "I f" by (fact weak_mono)

sublocale "term": weak_mono less_eq_term less_term "Fun f"
  by (unfold_locales, intro less_eq_termI, auto intro: append_Cons_le_append_Cons)

lemma ctxt_closed_NS: "ctxt.closed (rel_of (\<ge>\<^sub>\<A>))"
 by (rule one_imp_ctxt_closed, auto intro: term.append_Cons_le_append_Cons)

lemma subst_closed_S: "subst.closed (rel_of (>\<^sub>\<A>))" by auto

lemma subst_closed_NS: "subst.closed (rel_of (\<ge>\<^sub>\<A>))" by auto

lemma le_ctxt_closed[intro]: "s \<ge>\<^sub>\<A> t \<Longrightarrow> C\<langle>s\<rangle> \<ge>\<^sub>\<A> C\<langle>t\<rangle>"
  using ctxt.closedD[OF ctxt_closed_NS] by auto

lemma eval_le_eval: "\<forall>v \<in> vars_term s. \<alpha> v \<sqsubseteq> \<beta> v \<Longrightarrow> \<lbrakk>s\<rbrakk>\<alpha> \<sqsubseteq> \<lbrakk>s\<rbrakk>\<beta>"
proof (induct s)
  case (Var v) then show ?case by auto
next
  case IH: (Fun f ss)
  { fix i assume i: "i < length ss"
    then have "vars_term (ss!i) \<subseteq> vars_term (Fun f ss)" by fastforce
    with IH(2) have *: "v \<in> vars_term (ss!i) \<Longrightarrow> \<alpha> v \<sqsubseteq> \<beta> v" for v by blast
    with i have "\<lbrakk>ss ! i\<rbrakk>\<alpha> \<sqsubseteq> \<lbrakk>ss ! i\<rbrakk>\<beta>" by(intro IH(1), auto)
  }
  then show ?case by(auto intro: weak_mono_all_le)
qed

end

locale wf_weak_mono_algebra = weak_mono_algebra + wf_order
begin

sublocale wf_algebra..

sublocale redpair: redpair_order "rel_of (>\<^sub>\<A>)" "rel_of (\<ge>\<^sub>\<A>)"
  using SN ctxt_closed_NS subst_closed_S subst_closed_NS by unfold_locales

end


locale mono_algebra = weak_mono_algebra +
  assumes str_mono: "str_mono less_eq less (I f)"
begin

interpretation ord_syntax.

sublocale str_mono where f = "I f" by (fact str_mono)

sublocale "term": str_mono "(\<le>\<^sub>\<A>)" "(<\<^sub>\<A>)" "(Fun f)"
  by (unfold_locales, intro less_termI, auto intro: append_Cons_less_append_Cons)

lemma ctxt_closed_S: "ctxt.closed (rel_of (>\<^sub>\<A>))"
  by (rule one_imp_ctxt_closed, auto intro: term.append_Cons_less_append_Cons)

lemma less_ctxt_closed[intro]: "s >\<^sub>\<A> t \<Longrightarrow> C\<langle>s\<rangle> >\<^sub>\<A> C\<langle>t\<rangle>"
  using ctxt.closedD[OF ctxt_closed_S] by auto

lemma eval_less_eval:
  assumes "\<forall>v \<in> vars_term s. \<alpha> v \<sqsubseteq> \<beta> v"
    and "\<exists>v \<in> vars_term s. \<alpha> v \<sqsubset> \<beta> v"
  shows "\<lbrakk>s\<rbrakk>\<alpha> \<sqsubset> \<lbrakk>s\<rbrakk>\<beta>"
proof (insert assms, induct s)
  case (Var v)
  then show ?case by auto
next
  case (Fun f ss)
  from Fun.prems
  obtain i where i: "i < length ss" and "\<exists>v \<in> vars_term (ss!i). \<alpha> v \<sqsubset> \<beta> v"
    by (metis term.sel(4) var_imp_var_of_arg)
  with Fun have ex: "\<lbrakk>ss!i\<rbrakk>\<alpha> \<sqsubset> \<lbrakk>ss!i\<rbrakk>\<beta>" by auto
  have "\<forall>t \<in> set ss. \<lbrakk>t\<rbrakk>\<alpha> \<sqsubseteq> \<lbrakk>t\<rbrakk>\<beta>" using Fun by (auto intro: eval_le_eval)
  with i ex show ?case by (auto intro!: str_mono_all_le_ex_less)
qed

end

locale wf_mono_algebra = mono_algebra + wf_order
begin
  sublocale wf_weak_mono_algebra..
end

section \<open>Models\<close>

lemma subst_closed_rrstep: "subst.closed r \<Longrightarrow> rrstep r = r"
  apply (intro equalityI subrelI)
  apply (force elim: rrstepE)
  apply (force intro: rrstepI[of _ _ _ _ Var])
  done

subsection \<open>Non-Monotone Models\<close>

locale quasi_root_model = ordered_algebra where I = I
  for I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" +
  fixes R :: "('f,'v) trs"
  assumes R_imp_ge: "(l,r) \<in> R \<Longrightarrow> l \<ge>\<^sub>\<A> r"
begin

lemma rrstep_imp_ge: assumes st: "(s,t) \<in> rrstep R" shows "s \<ge>\<^sub>\<A> t"
proof-
  from st obtain \<sigma> l r where s: "s = l\<cdot>\<sigma>" and t: "t = r\<cdot>\<sigma>" and lr: "(l,r) \<in> R" by (auto simp:rrstep_def')
  show ?thesis by (auto simp: s t intro: R_imp_ge lr)
qed

lemma rrstep_subseteq_ge: "rrstep R \<subseteq> rel_of (\<ge>\<^sub>\<A>)"
  using rrstep_imp_ge by auto

lemma rrsteps_imp_ge: "(s,t) \<in> (rrstep R)\<^sup>* \<Longrightarrow> s \<ge>\<^sub>\<A> t"
  by (induct rule: rtrancl_induct, auto dest: rrstep_imp_ge term.order_trans)

lemma rrsteps_subseteq_ge: "(rrstep R)\<^sup>* \<subseteq> rel_of (\<ge>\<^sub>\<A>)"
  using rrsteps_imp_ge by auto

end

locale wf_quasi_root_model = quasi_root_model + wf_order
begin

sublocale wf_algebra..

lemma SN_rrstep_minus_greater:
  assumes "SN (rrstep R - rel_of (>\<^sub>\<A>))" shows "SN(rrstep R)"
proof
  fix f
  assume 1: "chain (rrstep R) f"
  then have "chainp (\<ge>\<^sub>\<A>) f" using rrstep_imp_ge by auto
  from term.chainp_ends_nonstrict[OF this]
  obtain n where "\<And>i. i \<ge> n \<Longrightarrow> \<not> f i >\<^sub>\<A> f (Suc i)" by auto
  with 1 have "\<And>i. i \<ge> n \<Longrightarrow> (f i, f (Suc i)) \<in> rrstep R - rel_of (>\<^sub>\<A>)" by auto
  then have "chain (rrstep R - rel_of (>\<^sub>\<A>)) (\<lambda>i. f (n+i))" by auto
  from chain_imp_not_SN_on[OF this] assms
  show False by fast
qed

end

locale strict_root_model = ordered_algebra where I = I
  for I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" +
  fixes R :: "('f,'v) trs"
  assumes R_imp_greater: "(l,r) \<in> R \<Longrightarrow> l >\<^sub>\<A> r"
begin

sublocale quasi_root_model using R_imp_greater by (unfold_locales, auto dest: term.less_imp_le)

lemma rrstep_imp_greater: assumes st: "(s,t) \<in> rrstep R" shows "s >\<^sub>\<A> t"
proof-
  from st obtain \<sigma> l r where s: "s = l\<cdot>\<sigma>" and t: "t = r\<cdot>\<sigma>" and lr: "(l,r) \<in> R" by (auto simp:rrstep_def')
  show ?thesis by (auto simp: s t intro: R_imp_greater lr)
qed

lemma rrstep_subseteq_greater: "rrstep R \<subseteq> rel_of (>\<^sub>\<A>)"
  using rrstep_imp_greater by auto

lemma rrsteps_imp_greater: "(s,t) \<in> (rrstep R)\<^sup>+ \<Longrightarrow> s >\<^sub>\<A> t"
  by (induct rule: trancl_induct, auto dest: rrstep_imp_greater term.less_trans)

lemma rrsteps_subseteq_greater: "(rrstep R)\<^sup>+ \<subseteq> rel_of (>\<^sub>\<A>)"
  using rrsteps_imp_greater by auto

end

locale wf_root_model = strict_root_model + wf_algebra
begin

sublocale wf_quasi_root_model..

lemma SN_rrstep: "SN (rrstep R)" by (rule SN_rrstep_minus_greater, auto intro: rrstep_imp_greater)

end

lemma rstep_imp_ctxt_rrstep: "(s,t) \<in> rstep R \<Longrightarrow> \<exists>(s',t') \<in> rrstep R. \<exists>C. s = C\<langle>s'\<rangle> \<and> t = C\<langle>t'\<rangle>"
  by force

subsection \<open>Monotone Models for Rewriting\<close>

locale quasi_model = quasi_root_model + weak_mono_algebra
begin

lemma rstep_imp_ge: assumes st: "(s,t) \<in> rstep R" shows "s \<ge>\<^sub>\<A> t"
  using rstep_imp_ctxt_rrstep[OF st] rrstep_imp_ge by auto

lemma rstep_subseteq_ge: "rstep R \<subseteq> rel_of (\<ge>\<^sub>\<A>)"
  using rstep_imp_ge by auto

lemma rsteps_imp_ge: "(s,t) \<in> (rstep R)\<^sup>* \<Longrightarrow> s \<ge>\<^sub>\<A> t"
  by (induct rule: rtrancl_induct, auto dest: rstep_imp_ge term.order_trans)

lemma rsteps_subseteq_ge: "(rstep R)\<^sup>* \<subseteq> rel_of (\<ge>\<^sub>\<A>)"
  using rsteps_imp_ge by auto

end


locale wf_quasi_model = quasi_model + wf_quasi_root_model
begin

lemma SN_minus_greater:
  assumes rR: "r \<subseteq> (rstep R)\<^sup>*"
  assumes SN: "SN (r - rel_of (>\<^sub>\<A>))"
  shows "SN r"
proof
  fix f
  assume 1: "chain r f"
  have "r \<subseteq> rel_of (\<ge>\<^sub>\<A>)" using rR rsteps_imp_ge by auto
  with 1 have "chainp (\<ge>\<^sub>\<A>) f" by auto
  from term.chainp_ends_nonstrict[OF this]
  obtain n where "\<And>i. i \<ge> n \<Longrightarrow> \<not> f i >\<^sub>\<A> f (Suc i)" by auto
  with 1 have "\<And>i. i \<ge> n \<Longrightarrow> (f i, f (Suc i)) \<in> r - rel_of (>\<^sub>\<A>)" by auto
  then have "chain (r - rel_of (>\<^sub>\<A>)) (\<lambda>i. f (n+i))" by auto
  from chain_imp_not_SN_on[OF this] SN_on_subset2[OF _ SN]
  show False by auto
qed

text \<open>Relative rule removal:\<close>
lemma SN_rstep_minus_greater:
  assumes "SN (rstep R - rel_of (>\<^sub>\<A>))" shows "SN (rstep R)"
  by (rule SN_minus_greater, insert assms, auto)

text \<open>Reduction pair processor:\<close>
lemma SN_relto_rrstep_rstep_minus_greater:
  assumes "SN (relto (rrstep R) (rstep R) - rel_of (>\<^sub>\<A>))" shows "SN (relto (rrstep R) (rstep R))"
    by (rule SN_minus_greater[OF _ assms], auto dest: rrstep_imp_rstep)

end

locale strict_model = strict_root_model + mono_algebra
begin

sublocale quasi_model using R_imp_greater term.less_imp_le by (unfold_locales, auto)

lemma rstep_imp_greater: assumes st: "(s,t) \<in> rstep R" shows "s >\<^sub>\<A> t"
  using rstep_imp_ctxt_rrstep[OF st] rrstep_imp_greater by auto

lemma rsteps_imp_greater: "(s,t) \<in> (rstep R)\<^sup>+ \<Longrightarrow> s >\<^sub>\<A> t"
  by (induct rule: trancl_induct, auto dest:rstep_imp_greater term.less_trans)

end

locale wf_model = strict_model + wf_order
begin

sublocale wf_quasi_model..
sublocale wf_mono_algebra..

text \<open>A well-founded model proves termination.\<close>
lemma SN_rstep: "SN (rstep R)"
  by (rule SN_rstep_minus_greater, auto intro: rstep_imp_greater)

end

subsection \<open>Rewrite Algebra\<close>

text \<open>A TRS induces a monotone algebra w.r.t. rewriting.\<close>

locale rewrite_algebra = fixes R :: "('f,'v) trs"
begin

abbreviation less_eq (infix "\<leftarrow>\<^sup>*" 50) where "t \<leftarrow>\<^sup>* s \<equiv> (s,t) \<in> (rstep R)\<^sup>*"
abbreviation less (infix "\<leftarrow>\<^sup>+" 50) where "t \<leftarrow>\<^sup>+ s \<equiv> (s,t) \<in> (rstep R)\<^sup>+"

sublocale ord less_eq less
  rewrites "rel_of less_eq = ((rstep R)\<^sup>*)\<inverse>"
    and "rel_of less = ((rstep R)\<^sup>+)\<inverse>"
    and "rel_of greater_eq = (rstep R)\<^sup>*"
    and "rel_of greater = (rstep R)\<^sup>+"
  by auto

notation less_eq (infix "\<leftarrow>\<^sup>*" 50)
notation less (infix "\<leftarrow>\<^sup>+" 50)
notation greater_eq (infix "\<rightarrow>\<^sup>*" 50)
notation greater (infix "\<rightarrow>\<^sup>+" 50)
notation equiv (infix "\<leftrightarrow>\<^sup>*" 50)

sublocale mono_algebra less_eq less Fun
  using ctxt_closed_rsteps[of R] ctxt.closed_trancl[OF ctxt_closed_rstep[of R]]
  by (unfold_locales, auto simp: dest: ctxt_closed_one)

lemma less_term_is_less[simp]: "less_term = less"
  using subst.closed_trancl[OF subst_closed_rstep[of R]]
  by (unfold less_term_def, auto intro!: ext elim: allE[of _ Var] simp: term_algebra_eval)

lemma le_term_is_le[simp]: "less_eq_term = less_eq"
  using subst.closed_rtrancl[OF subst_closed_rstep[of R]]
  by (unfold less_eq_term_def, auto intro!: ext elim: allE[of _ Var] simp: term_algebra_eval)

(* rsteps_subst_closed is derived *)
thm less_term_stable[where 'v='v and 'w='v, simplified]

sublocale strict_model less_eq less Fun by (unfold_locales, auto)

text \<open>
  To any model of @{term R}, there is a homomorphism from the term algebra.
\<close>
proposition strict_model_imp_hom:
  assumes model: "strict_model (less_eq' :: 'b \<Rightarrow> _) less' I' R"
  shows "\<exists>hom. ordered_algebra_hom hom (\<leftarrow>\<^sup>*) (\<leftarrow>\<^sup>+) Fun less_eq' less' I'"
proof-
  interpret target: strict_model less_eq' less' I' R using model.
  have "ordered_algebra_hom (\<lambda>s. target.eval s \<alpha>) (\<leftarrow>\<^sup>*) (\<leftarrow>\<^sup>+) Fun less_eq' less' I'" for \<alpha>
    by (unfold_locales, auto dest: target.rsteps_imp_ge target.rsteps_imp_greater)
  then show ?thesis by auto
qed

text \<open>
  Further, if there is enough variables, then the model is a homomorphic image of the term algebra.
\<close>
theorem strict_model_imp_epim:
  assumes surj: "surj (\<alpha> :: 'v \<Rightarrow> 'b)" (* there should be enough variables *)
      and model: "strict_model (less_eq' :: 'b \<Rightarrow> _) less' I' R"
  defines "hom \<equiv> \<lambda>s. algebra.eval I' s \<alpha>"
  shows "ordered_algebra_epim hom (\<leftarrow>\<^sup>*) (\<leftarrow>\<^sup>+) Fun less_eq' less' I'"
proof-
  interpret target: strict_model less_eq' less' I' R using model.
  from surj have "surj hom" using target.subset_range_eval[of \<alpha>] by (auto simp: hom_def)
  then show "ordered_algebra_epim hom (\<leftarrow>\<^sup>*) (\<leftarrow>\<^sup>+) Fun less_eq' less' I'"
    by (unfold_locales, auto dest: target.rsteps_imp_ge target.rsteps_imp_greater simp: hom_def)
qed

end

text \<open>The next theorem is due to Zantema (JSC 1994): a TRS is terminating if and only if
  there is a well-founded model for it.
  In paper we don't restrict the domain of interpretations but in Isabelle/HOL we have to.
\<close>
proposition ex_wf_model_iff_terminating:
  fixes R :: "('f,'v) trs"
  shows "(\<exists>less_eq less :: ('f,'v) term \<Rightarrow> _. \<exists> I. wf_model less_eq less I R) \<longleftrightarrow> SN (rstep R)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain less_eq less :: "('f,'v) term \<Rightarrow> _" and I where "wf_model less_eq less I R" by auto
  then interpret wf_model less_eq less I R by auto
  from SN_rstep show ?r.
next
  interpret rewrite_algebra R.
  assume ?r
  then have "SN ((rstep R)\<^sup>+)" by (rule SN_on_trancl)
  from SN_induct[OF this]
  have "wf_model less_eq less Fun R" by (unfold_locales, auto)
  then show ?l by auto
qed

text \<open>Ordering in the rewrite algebra of R is preserved in any strict model of R.\<close>

definition models_less
  where "models_less (ty :: 'a itself) R t s \<longleftrightarrow>
  (\<forall>less_eq less :: 'a \<Rightarrow> _. \<forall> I. strict_model less_eq less I R \<longrightarrow> ord_algebra.less_term less I t s)"

lemma(in strict_model) models_lessD:
  assumes "models_less (TYPE('a)) R t s" shows "t <\<^sub>\<A> s"
  using assms strict_model_axioms by (auto simp: models_less_def)

lemma models_less_imp_rsteps:
  assumes "models_less (TYPE(('f,'v) term)) (R::('f,'v) trs) t s"
  shows "(s,t) \<in> (rstep R)\<^sup>+"
proof-
  interpret rewrite_algebra R.
  from models_lessD[OF assms] show ?thesis by auto
qed

lemma rsteps_imp_models_less:
  assumes st: "(s,t) \<in> (rstep R)\<^sup>+"
  shows "models_less (TYPE('a)) R t s"
proof (unfold models_less_def, intro allI impI)
  interpret rewrite_algebra R.
  fix less_eq less and I :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a"
  assume "strict_model less_eq less I R"
  then interpret target: strict_model less_eq less I R.
  from target.rsteps_imp_greater[OF st]
  show "target.less_term t s" by auto
qed

subsection \<open>Models for Equational Theories\<close>

locale equimodel = weak_mono_algebra where I = I
  for I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" +
  fixes E :: "('f,'v) trs"
  assumes E_imp_equiv: "(l,r) \<in> E \<Longrightarrow> l \<simeq>\<^sub>\<A> r"
begin

sublocale quasi_model where R = "E\<^sup>\<leftrightarrow>"
  by (unfold_locales, insert E_imp_equiv, auto)

lemma conversion_imp_equiv: assumes "(s,t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" shows "s \<simeq>\<^sub>\<A> t"
proof-
  note * = rsteps_imp_ge[unfolded rstep_simps(5), folded conversion_def]
  from *[OF assms[unfolded conversion_inv[of s t]]] *[OF assms]
  show ?thesis by auto
qed

end

locale model = algebra I for I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" and E :: "('f,'v) trs" +
  assumes E_imp_eq: "(l,r) \<in> E \<Longrightarrow> \<lbrakk>l\<rbrakk> = \<lbrakk>r\<rbrakk>"
begin

interpretation ordered: ordered_algebra
  where less_eq = "(=)" and less = "\<lambda>x y. False"
  by (unfold_locales, auto)

sublocale ordered: equimodel
  where less_eq = "(=)" and less = "\<lambda>x y. False"
  by (unfold_locales, auto simp: E_imp_eq)

lemma conversion_imp_eq: assumes "(s,t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" shows "\<lbrakk>s\<rbrakk> = \<lbrakk>t\<rbrakk>"
  using ordered.conversion_imp_equiv[OF assms] by auto

end


subsection \<open>Encoding algebras\<close>


locale pre_encoded_ord_algebra =
  ord less_eq less + pre_encoded_algebra I E
  for less_eq less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and I :: "'g \<Rightarrow> 'a list \<Rightarrow> 'a"
  and E :: "'f \<Rightarrow> nat \<Rightarrow> ('g, nat) term"
begin

sublocale target: ord_algebra.

sublocale ord_algebra where I = IE.

end

locale encoded_ordered_algebra = quasi_order + pre_encoded_ord_algebra + encoded_algebra
begin

sublocale target: ordered_algebra..

sublocale ordered_algebra where I = IE..

end

locale encoded_wf_algebra = wf_order + encoded_ordered_algebra
begin

sublocale target: wf_algebra by (unfold_locales, fact less_induct)

sublocale wf_algebra where I = IE..

end


locale encoded_weak_mono_algebra = encoded_ordered_algebra +
  target: weak_mono_algebra
begin

sublocale weak_mono where f = "IE f"
  using encoder.var_domain
  by (auto simp: weak_mono_iff_all_le intro: target.eval_le_eval)

sublocale weak_mono_algebra where I = IE..

end

locale encoded_mono_algebra = encoded_ordered_algebra +
  target: mono_algebra +
  assumes mono_vars: "i < n \<Longrightarrow> i \<in> vars_term (E f n)"
begin

interpretation ord_syntax.

sublocale encoded_weak_mono_algebra ..

sublocale str_mono where f = "IE f"
  apply (unfold str_mono_iff_all_le_ex_less)
  using encoder.var_domain mono_vars
  by (auto intro!: target.eval_less_eval)

sublocale mono_algebra where I = IE..

end

locale encoded_wf_weak_mono_algebra =
  encoded_weak_mono_algebra + wf_order
begin

sublocale encoded_wf_algebra..

sublocale wf_weak_mono_algebra where I = IE..

end

locale encoded_wf_mono_algebra =
  encoded_mono_algebra + wf_order
begin

sublocale encoded_wf_weak_mono_algebra..

sublocale wf_mono_algebra where I = IE..

end

end
