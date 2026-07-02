(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL (see file COPYING.LESSER)
*)

chapter \<open>Preliminaries for AC-Rewriting\<close>

theory AC_Rewriting_Base
  imports First_Order_Rewriting.Trs
begin

(*TODO: move*)
lemma map_eq_conv':
  "map f xs = map g ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>i<length ys. f (xs ! i) = g (ys ! i))"
  by (auto dest: map_eq_imp_length_eq intro: nth_equalityI)
    (metis map_eq_imp_length_eq nth_map)

abbreviation (input) "Bin f s t \<equiv> Fun f [s, t]"

lemma Bin_cases:
  "(\<exists>x. s = Var x) \<or> (\<exists>f t u. s = Fun f [t, u]) \<or> (\<exists>f ts. (\<forall>u v. ts \<noteq> [u, v]) \<and> s = Fun f ts)"
  by (cases s; cases "args s"; cases "tl (args s)"; auto)

lemma Bin_cases_with_length:
  "(\<exists>x. s = Var x) \<or> (\<exists>f t u. s = Fun f [t, u]) \<or> (\<exists>f ts. length ts \<noteq> 2 \<and> (\<forall>u v. ts \<noteq> [u, v]) \<and> s = Fun f ts)"
  by (cases s; cases "args s"; cases "tl (args s)"; auto)

lemma Bin_ctxt_cases:
  "(C = \<box>) \<or>
  (\<exists>f t D. C = More f [t] D []) \<or>
  (\<exists>f t D. C = More f [] D [t]) \<or>
  (\<exists>f ss D ts. length ss + length ts \<noteq> 1 \<and> C = More f ss D ts)"
proof (cases C)
  case (More f ss D ts)
  then show ?thesis by (cases ss; cases ts) auto
qed simp

lemma ctxt_apply_term_Bin_cases [consumes 2]:
  assumes "C \<noteq> \<box>" and "C\<langle>s\<rangle> = Bin f t u"
  obtains (right) D where "C = More f [t] D []" and "u = D\<langle>s\<rangle>"
  | (left) D where "C = More f [] D [u]" and "t = D\<langle>s\<rangle>"
  using assms and Bin_ctxt_cases [of C] by (auto) (case_tac ss; case_tac ts; simp)

lemma bterm_induct [case_names Var Fun Bin]:
  fixes P :: "('f, 'v) term \<Rightarrow> bool" 
  assumes "\<And>x. P (Var x)"
    and "\<And>f ts. length ts \<noteq> 2 \<Longrightarrow> \<forall>u v. ts \<noteq> [u, v] \<Longrightarrow> (\<And>t. t \<in> set ts \<Longrightarrow> P t) \<Longrightarrow> P (Fun f ts)"
    and "\<And>f s t. P s \<Longrightarrow> P t \<Longrightarrow> P (Bin f s t)"
  shows "P t"
using assms
proof (induct t)
  case (Fun f ts)
  then show ?case using Bin_cases_with_length [of "Fun f ts"] by auto
qed auto

abbreviation "A_rule f s t u \<equiv> (Bin f (Bin f s t) u, Bin f s (Bin f t u))"
abbreviation "A_rule_inv f s t u \<equiv> (Bin f s (Bin f t u), Bin f (Bin f s t) u)"
definition "A_rules F = {A_rule f s t u | f s t u. f \<in> F}"
definition "A_trs F = A_rules F \<union> {A_rule_inv f s t u | f s t u. f \<in> F}"
abbreviation "astep F \<equiv> rstep (A_rules F)"

text \<open>The A-equivalence class of a term.\<close>
definition "A_class A s = {t. (s, t) \<in> (astep A)\<^sup>\<leftrightarrow>\<^sup>*}"

abbreviation "C_rule f s t \<equiv> (Bin f s t, Bin f t s)"
definition "C_rules F = {C_rule f s t | f s t. f \<in> F}"
abbreviation "cstep F \<equiv> rstep (C_rules F)"

text \<open>The C-equivalence class of a term.\<close>
definition "C_class C s = {t. (s, t) \<in> (cstep C)\<^sup>\<leftrightarrow>\<^sup>*}"

definition "AC_rules A C = A_rules A \<union> C_rules C"
definition "AC_trs A C = A_trs A \<union> C_rules C"
abbreviation acstep :: "'f set \<Rightarrow> 'f set \<Rightarrow> ('f, 'v) term rel"
  where
    "acstep A C \<equiv> rstep (AC_rules A C)"
abbreviation "acrstep A C \<equiv> rstep (AC_trs A C)"

lemma acstep_empty [simp]:  "acstep {} {} = {}"
  by (auto simp: AC_rules_def A_rules_def C_rules_def)

lemma symcl_AC_rules:
  "(AC_rules A C)\<^sup>\<leftrightarrow> = AC_trs A C"
  by (auto simp: AC_trs_def A_trs_def AC_rules_def A_rules_def C_rules_def)

lemma symcl_acstep:
  "(acstep A C)\<^sup>\<leftrightarrow> = acrstep A C"
  by (auto simp flip: symcl_AC_rules)

text \<open>The AC-equivalence class of a term.\<close>
definition "AC_class A C s = {t. (s, t) \<in> (acstep A C)\<^sup>\<leftrightarrow>\<^sup>*}"

lemma ctxt_closed_astep_symcl: "ctxt.closed ((astep F)\<^sup>\<leftrightarrow>)" by auto

lemma ctxt_closed_cstep_symcl: "ctxt.closed ((cstep C)\<^sup>\<leftrightarrow>)" by auto

lemma ctxt_closed_acstep_symcl: "ctxt.closed ((acstep A C)\<^sup>\<leftrightarrow>)" by auto

lemmas
  args_aconv_imp_aconv = args_steps_imp_steps [OF ctxt_closed_astep_symcl, folded conversion_def]
and
  args_cconv_imp_cconv = args_steps_imp_steps [OF ctxt_closed_cstep_symcl, folded conversion_def]
and
  args_acconv_imp_acconv = args_steps_imp_steps [OF ctxt_closed_acstep_symcl, folded conversion_def]

lemma A_rule_in_A_rules [intro]:
  "f \<in> F \<Longrightarrow> A_rule f s t u \<in> A_rules F"
  by (auto simp: A_rules_def)

lemma A_rule_in_AC_rules [intro]:
  "f \<in> A \<Longrightarrow> A_rule f s t u \<in> AC_rules A C"
  by (auto simp: AC_rules_def)

lemma C_rule_in_C_rules [intro]:
  "f \<in> F \<Longrightarrow> C_rule f s t \<in> C_rules F"
  by (auto simp: C_rules_def)

lemma C_rule_in_AC_rules [intro]:
  "f \<in> C \<Longrightarrow> C_rule f s t \<in> AC_rules A C"
  by (auto simp: AC_rules_def)

lemma Bin_acstep:
  assumes "(Bin f s t, u) \<in> acstep A C"
  shows "\<exists>v w. u = Bin f v w"
using assms
proof (cases)
  case (rstep C \<sigma> l r)
  then show ?thesis
  proof (cases "C = \<box>")
    case False
    with rstep and Bin_ctxt_cases [of C] show ?thesis
      by (auto) (metis Suc_inject add_Suc_right length_Cons length_append list.size(3))
  next
    case [simp]: True
    show ?thesis using rstep by (auto simp: AC_rules_def A_rules_def C_rules_def)
  qed
qed

lemma converse_C_rules [simp]:
  "(C_rules F)\<inverse> = C_rules F"
  by (auto simp: C_rules_def)

lemma converse_cstep [simp]:
  "(cstep F)\<inverse> = cstep F"
  by (force simp: C_rules_def)

lemma acstep_eq_astep_Un_cstep:
  "acstep A C = astep A \<union> cstep C"
  by (auto simp: AC_rules_def)

lemma A_rule_astep:
  "f \<in> F \<Longrightarrow> (C\<langle>Bin f (Bin f s t) u\<rangle>, C\<langle>Bin f s (Bin f t u)\<rangle>) \<in> astep F"
  by (intro rstep_ctxt rstep_rule) (auto simp: A_rules_def)

lemma C_rule_cstep:
  "f \<in> F \<Longrightarrow> (C\<langle>Bin f s t\<rangle>, C\<langle>Bin f t s\<rangle>) \<in> cstep F"
  by (intro rstep_ctxt rstep_rule) (auto simp: C_rules_def)

lemma astep_imp_acsteps:
  "(s, t) \<in> astep A \<Longrightarrow> (s, t) \<in> (acstep A C)\<^sup>*"
  by (auto simp: AC_rules_def)

lemma cstep_imp_acsteps:
  "(s, t) \<in> cstep C \<Longrightarrow> (s, t) \<in> (acstep A C)\<^sup>*"
  by (auto simp: AC_rules_def)

lemma acrstep_empty[simp]: "acrstep {} {} = {}"
  by (auto simp: AC_trs_def A_trs_def A_rules_def C_rules_def)

lemma A_class_eq_conv [simp]:
  "A_class A s = A_class A t \<longleftrightarrow> (s, t) \<in> (astep A)\<^sup>\<leftrightarrow>\<^sup>*"
  by (auto simp: A_class_def dest: transD [OF conversion_trans] iffD1 [OF conversion_inv])

lemma AC_class_eq_conv [simp]:
  "AC_class A C s = AC_class A C t \<longleftrightarrow> (s, t) \<in> (acstep A C)\<^sup>\<leftrightarrow>\<^sup>*"
  by (auto simp: AC_class_def dest: transD [OF conversion_trans] iffD1 [OF conversion_inv])

lemma C_class_eq_conv [simp]:
  "C_class C s = C_class C t \<longleftrightarrow> (s, t) \<in> (cstep C)\<^sup>\<leftrightarrow>\<^sup>*"
  by (auto simp: C_class_def dest: transD [OF conversion_trans] iffD1 [OF conversion_inv])

end
