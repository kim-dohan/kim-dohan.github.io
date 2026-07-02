(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory String_Reversal
  imports
    TRS.QDP_Framework
    TRS.Signature_Extension
begin

fun
  unary_term :: "('f, 'v) term \<Rightarrow> bool"
where
  "unary_term(Var x) = True" |
  "unary_term(Fun f [t]) = unary_term t" |
  "unary_term t = False"

lemma unary_term_single_arg: assumes "unary_term(Fun f ts)" shows "\<exists>s. ts = [s]"
proof -
  from assms obtain t where t: "t = Fun f ts" by simp
  moreover with assms have "unary_term t" by simp
  ultimately show ?thesis by (induct rule: unary_term.induct) auto
qed

lemma unary_term_induct[consumes 1,case_names Var Fun,induct type: "term"]:
  fixes P :: "('f,'v)term \<Rightarrow> bool"
  assumes "unary_term t"
    and "\<And>x. P(Var x)"
    and "\<And>f s. unary_term s \<Longrightarrow> P s \<Longrightarrow> P(Fun f [s])"
  shows "P t"
using assms(1) proof (induct t)
  case (Var x) show ?case by (simp add: assms)
next
  case (Fun f ss)
  with unary_term_single_arg obtain s where [simp]: "ss = [s]" by best
  from Fun have "unary_term s" by simp
  moreover with Fun have "P s" by simp
  ultimately show ?case using assms by simp
qed

fun unary_ctxt :: "('f,'v)ctxt \<Rightarrow> bool"
where "unary_ctxt \<box> = True"
    | "unary_ctxt(More _ [] C []) = unary_ctxt C"
    | "unary_ctxt _ = False"

lemma unary_ctxt_single_arg: assumes "unary_ctxt(More f ss1 D ss2)" shows "ss1 = [] \<and> ss2 = []"
proof -
  from assms obtain E where "E = More f ss1 D ss2" by simp
  moreover with assms have "unary_ctxt E" by simp
  ultimately show ?thesis by (induct rule: unary_ctxt.induct) auto
qed

lemma unary_ctxt_induct[consumes 1,case_names Hole More,induct type: "ctxt"]:
  fixes P :: "('f,'v)ctxt \<Rightarrow> bool"
  assumes "unary_ctxt C"
    and "P \<box>"
    and "\<And>f D. unary_ctxt D \<Longrightarrow> P D \<Longrightarrow> P(More f [] D [])"
  shows "P C"
using assms(1) proof (induct C)
  case Hole show ?case by (simp add: assms)
next
  case (More f ss1 D ss2)
  from unary_ctxt_single_arg[OF More(2)] have [simp]: "ss1 = []" and [simp]: "ss2 = []" by auto
  from More have "unary_ctxt D" by simp
  moreover with More have "P D" by simp
  ultimately show ?case using assms by simp
qed

fun rev_term :: "('f,'v)ctxt \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term"
where "rev_term C (Var x) = C\<langle>Var x\<rangle>"
    | "rev_term C (Fun f [t]) = rev_term (More f [] C []) t"

fun rev_ctxt :: "('f,'v)ctxt \<Rightarrow> ('f,'v)ctxt \<Rightarrow> ('f,'v)ctxt"
where "rev_ctxt C \<box> = C"
    | "rev_ctxt C (More f [] D []) = rev_ctxt (More f [] C []) D"
    | "rev_ctxt C D = D \<circ>\<^sub>c C" (* the last case is not relevant but it is helpful to be defined *)

fun get_var :: "('f,'v)term \<Rightarrow> 'v"
where "get_var(Var x) = x"
    | "get_var(Fun _ [t]) = get_var t"

definition subst :: "'v \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) subst" where
  "subst x C = (\<lambda>y. if x = y then C\<langle>Var x\<rangle> else Var y)"

lemma rev_term_subst[simp]:
  assumes "unary_term t"
    and "unary_ctxt C"
  shows "rev_term C t \<cdot> subst (get_var t) D = rev_term (C \<circ>\<^sub>c D) t"
using assms proof (induct t arbitrary: C rule: unary_term_induct)
  case (Var x) then show ?case by (induct C) (simp_all add: subst_def)
next
  case (Fun f s) then show ?case by simp
qed

lemma rev_term_ctxt_apply[simp]:
  fixes t :: "('f,'v)term"
  assumes "unary_ctxt D"
    and "unary_term t"
  shows "rev_term C (D\<langle>t\<rangle>) = rev_term \<box> t \<cdot> subst (get_var t) (rev_ctxt C D)"
using assms proof (induct D arbitrary: t C rule: unary_ctxt_induct)
  case Hole then show ?case
  proof (induct t rule: unary_term_induct)
    case (Var x) then show ?case by (simp add: subst_def)
  next
    case (Fun f s) then show ?case by simp
  qed
next
  case (More f D)
  have "rev_term C ((More f [] D [])\<langle>t\<rangle>) = rev_term C (Fun f [D\<langle>t\<rangle>])" by simp
  also have "... = rev_term (More f [] C []) (D\<langle>t\<rangle>)" by simp
  also have "... = rev_term \<box> t \<cdot> subst (get_var t) (rev_ctxt (More f [] C []) D)"
    by (simp add: More)
  also have "... = rev_term \<box> t \<cdot> subst (get_var t) (rev_ctxt C (More f [] D []))" by simp
  finally show ?case by simp
qed

lemma rev_ctxt_assoc:
  assumes "unary_ctxt D"
    and "unary_ctxt C"
  shows "rev_ctxt C D = rev_ctxt \<box> D \<circ>\<^sub>c C"
using assms proof (induct D arbitrary: C rule: unary_ctxt_induct)
  case Hole then show ?case 
  proof (induct C rule: unary_ctxt_induct)
    case Hole show ?case by simp
  next
    case (More f C') then show ?case by simp
  qed
next
  case (More f D')
  from More(3) have "unary_ctxt (More f [] C [])" (is "unary_ctxt ?C") by simp
  from More(2)[OF this] have IH: "rev_ctxt ?C D' = rev_ctxt \<box> D' \<circ>\<^sub>c ?C" by simp
  have "unary_ctxt (More f [] \<box> [])" by simp
  from More(2)[OF this]
    have IH': "rev_ctxt (More f [] \<box> []) D' = rev_ctxt \<box> D' \<circ>\<^sub>c More f [] \<box> []" by simp
  have "rev_ctxt C (More f [] D' []) = rev_ctxt ?C D'" by simp
  also have "... = rev_ctxt \<box> D' \<circ>\<^sub>c ?C" unfolding IH by simp
  also have "... = rev_ctxt \<box> D' \<circ>\<^sub>c More f [] \<box> [] \<circ>\<^sub>c C" by (simp add: ac_simps)
  also have "... = rev_ctxt (More f [] \<box> []) D' \<circ>\<^sub>c C" unfolding IH'[symmetric] by simp
  also have "... = rev_ctxt \<box> (More f [] D' []) \<circ>\<^sub>c C" by simp
  finally show ?case by simp
qed

lemma subst_rev_ctxt[simp]:
  assumes "unary_ctxt D" and "unary_ctxt C"
  shows "Var x \<cdot> subst x (rev_ctxt C D) = (rev_ctxt \<box> D)\<langle>C\<langle>Var x\<rangle>\<rangle>"
proof -
  have "rev_ctxt C D = rev_ctxt \<box> D \<circ>\<^sub>c C" by (rule rev_ctxt_assoc[OF assms])
  then have "(rev_ctxt C D)\<langle>Var x\<rangle> = (rev_ctxt \<box> D \<circ>\<^sub>c C)\<langle>Var x\<rangle>" by simp
  then show ?thesis by (auto simp: subst_def)
qed

fun term_to_ctxt :: "('f,'v)term \<Rightarrow> ('f,'v)ctxt" where
  "term_to_ctxt(Var _) = \<box>"
| "term_to_ctxt(Fun f [t]) = More f [] (term_to_ctxt t) []"

fun ctxt :: "'v \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) ctxt" where
  "ctxt x \<sigma> = term_to_ctxt (\<sigma> x)"

lemma unary_ctxt_usb_id[simp]:
  assumes "unary_ctxt C" shows "C \<cdot>\<^sub>c \<sigma> = C"
using assms by (induct C rule: unary_ctxt_induct) simp_all

fun rev_rule :: "('f,'v)rule \<Rightarrow> ('f,'v)rule"
where "rev_rule(l,r) = (rev_term \<box> l,rev_term \<box> r)"

definition rev_trs :: "('f,'v)trs \<Rightarrow> ('f,'v)trs"
where "rev_trs R \<equiv> rev_rule ` R"

definition unary_sig :: "('f\<times>nat)set \<Rightarrow> bool"
where "unary_sig F \<equiv> \<forall>(f,i)\<in>F. i = 1"

lemma unary_ctxt_appl_imp_unary_ctxt: 
  assumes "unary_term C\<langle>t\<rangle>"
  shows "unary_ctxt C"
using assms
proof (induct C, simp)
  case (More f l C r)
  then show ?case
    by (cases l, cases r, simp, simp, cases r, simp, cases "tl l", simp, simp, cases "tl l", simp, simp)
qed

lemma unary_ctxt_appl_imp_unary_term: 
  assumes "unary_term C\<langle>t\<rangle>"
  shows "unary_term t"
using assms
proof (induct C, simp)
  case (More f l C r)
  then show ?case
    by (cases l, cases r, simp, simp, cases r, simp, cases "tl l", simp, simp, cases "tl l", simp, simp)
qed

lemma unary_subst_appl_imp_unary_term :
  assumes "unary_term (t \<cdot> \<sigma>)"
  shows "unary_term t"
using assms 
proof (induct t, simp)
  case (Fun f ss)
  from Fun(2) obtain s where ss: "ss = [s]" by (cases ss, simp, cases "tl ss", simp, simp)
  with Fun(2) have "unary_term (s \<cdot> \<sigma>)" by auto
  with Fun ss show ?case by simp
qed

lemma unary_subst_appl_imp_unary_subst:
  assumes "unary_term (t \<cdot> \<sigma>)"
  shows "unary_term (\<sigma> (get_var t))"
using assms 
proof (induct t)
  case (Var t)
  then show ?case by auto
next
  case (Fun f ss)
  from Fun(2) obtain s where ss: "ss = [s]" by (cases ss, simp, cases "tl ss", simp, simp)
  with Fun(2) have "unary_term (s \<cdot> \<sigma>)" by auto
  with Fun ss show ?case by simp
qed

lemma unary_term_imp_unary_ctxt :
  assumes "unary_term t"
  shows "unary_ctxt (term_to_ctxt t)"
using assms
by (induct rule: unary_term_induct, auto)

lemma unary_rev_ctxt :
  "unary_ctxt (rev_ctxt C D) = (unary_ctxt C \<and> unary_ctxt D)"
proof (induct D arbitrary: C, simp)
  case (More f l D r C)
  then show ?case 
    by (cases l, cases r, simp+)
qed

lemma get_var_subst: 
  assumes string: "unary_term t"  
  shows "get_var (t \<cdot> \<sigma>) = get_var (\<sigma> (get_var t))"
proof -
  from assms
  have "get_var (t \<cdot> \<sigma>) = get_var (\<sigma> (get_var t))"
    by (induct rule: unary_term_induct, auto)
  then show ?thesis by simp
qed
  
lemma get_var_ctxt: assumes "unary_ctxt C"  
  shows "get_var (C\<langle>t\<rangle>) = get_var t"
using assms by (induct rule: unary_ctxt_induct, auto)

lemma get_var_rev_term: assumes "unary_term t"
  and "unary_ctxt C"
  shows "get_var (rev_term C t) = get_var t"
using assms
proof (induct arbitrary: C rule: unary_term_induct)
  case (Var x C)
  let ?x = "Var x"
  have "get_var (rev_term C (?x)) = get_var (C\<langle>?x\<rangle>)" by simp
  also have "\<dots> = get_var (?x)" by (simp add: get_var_ctxt[OF Var])
  finally show ?case .
next
  case (Fun f s C)
  then show ?case by auto
qed

lemma rev_term_subst_apply:
  assumes ut: "unary_term t"
  and uC: "unary_ctxt C"
  shows "rev_term C (t \<cdot> \<sigma>) = rev_term (rev_ctxt C (term_to_ctxt t)) (\<sigma> (get_var t))"
using assms
proof (induct arbitrary: C rule: unary_term_induct)
  case (Fun f s C)
  then show ?case by simp
next
  case (Var x C)
  then show ?case by simp
qed

lemma rev_term_to_rev_ctxt: 
  assumes ut: "unary_term t"
  and uC: "unary_ctxt C"
  shows "rev_term C t = ((rev_ctxt \<box> (term_to_ctxt t)) \<circ>\<^sub>c C)\<langle>Var (get_var t)\<rangle>"
using assms
proof (induct arbitrary: C rule: unary_term_induct)
  case (Var x C)
  then show ?case by auto
  case (Fun f s C)
  from Fun(1) have us: "unary_ctxt (term_to_ctxt s)" by (induct rule: unary_term_induct, auto)
  have uf: "unary_ctxt (More f [] \<box> [])" by simp
  from Fun show ?case by (simp add: rev_ctxt_assoc[OF us uf])
qed
    
lemma rev_ctxt_to_rev_term: 
  assumes "unary_term t"
  and "unary_ctxt C"
  shows "(rev_ctxt C (term_to_ctxt t))\<langle>Var (get_var (\<sigma> (get_var t)))\<rangle> =
    rev_term C t \<cdot> (\<lambda>x. Var (get_var (\<sigma> (get_var t))))"
using assms
proof (induct arbitrary: C rule: unary_term_induct)
  case (Fun f s C) then show ?case by auto
next
  case (Var x C) then show ?case by simp
qed

lemma rstep_imp_rev_rstep:
  assumes string_s: "unary_term s"
    and string_t: "unary_term t"
    and same_vars: "\<forall> (l,r) \<in> R. get_var l = get_var r"
    and step: "(s,t) \<in> rstep R"
  shows "(rev_term \<box> s,rev_term \<box> t) \<in> rstep(rev_trs R)" (is "_ \<in> rstep ?S")
proof -
  from rstep_imp_C_s_r[OF step] obtain C \<sigma> l r where rule: "(l,r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  then have rrule: "(rev_term \<box> l, rev_term \<box> r) \<in> ?S" unfolding rev_trs_def by force
  from string_s[simplified s] have uC: "unary_ctxt C" and uls: "unary_term (l \<cdot> \<sigma>)"
    using unary_ctxt_appl_imp_unary_term[of C "l \<cdot> \<sigma>"] unary_ctxt_appl_imp_unary_ctxt[of C "l \<cdot> \<sigma>"] by auto
  from uls have ul: "unary_term l" by (rule unary_subst_appl_imp_unary_term)
  from string_t[simplified t] have urs: "unary_term (r \<cdot> \<sigma>)"
    by (rule unary_ctxt_appl_imp_unary_term)
  then have ur: "unary_term r" by (rule unary_subst_appl_imp_unary_term)
  let ?sig = "subst (get_var (l \<cdot> \<sigma>)) (rev_ctxt \<box> C)"
  let ?xsig = "\<sigma> (get_var l)"
  let ?sig2 = "(\<lambda>x. Var (get_var ?xsig))"
  let ?revl = "rev_ctxt \<box> (term_to_ctxt l)"
  let ?revr = "rev_ctxt \<box> (term_to_ctxt r)"
  let ?C = "(rev_ctxt \<box> (term_to_ctxt ?xsig)) \<cdot>\<^sub>c ?sig"
  have url: "unary_ctxt ?revl" using ul by (simp add: unary_rev_ctxt, rule unary_term_imp_unary_ctxt)
  have urr: "unary_ctxt ?revr" using ur by (simp add: unary_rev_ctxt, rule unary_term_imp_unary_ctxt)
  have uxsig: "unary_term ?xsig" by (rule unary_subst_appl_imp_unary_subst[OF uls])
  have "rev_term \<box> s = rev_term \<box> C\<langle>l \<cdot> \<sigma>\<rangle>" by (simp add: s)
  also have "\<dots> = (rev_term \<box> (l \<cdot> \<sigma>)) \<cdot> ?sig" by (rule rev_term_ctxt_apply[OF uC uls])
  also have "\<dots> = (rev_term ?revl ?xsig) \<cdot> ?sig" using rev_term_subst_apply[OF ul, of \<box> \<sigma>] by simp
  also have "\<dots> = (rev_ctxt \<box> (term_to_ctxt ?xsig) \<circ>\<^sub>c ?revl)\<langle>Var (get_var ?xsig)\<rangle> \<cdot> ?sig" by (simp only: rev_term_to_rev_ctxt[OF uxsig url]) 
  also have "\<dots> = (rev_ctxt \<box> (term_to_ctxt ?xsig))\<langle>?revl \<langle>Var (get_var ?xsig)\<rangle>\<rangle> \<cdot> ?sig" by simp
  also have "\<dots> = (rev_ctxt \<box> (term_to_ctxt ?xsig))\<langle>rev_term \<box> l \<cdot> ?sig2\<rangle> \<cdot> ?sig" by (simp only: rev_ctxt_to_rev_term[OF ul, of \<box> \<sigma>, simplified])
  also have "\<dots> = ?C \<langle>rev_term \<box> l \<cdot> ?sig2 \<cdot> ?sig\<rangle>" by simp 
  finally have idl: "rev_term \<box> s = ?C \<langle>rev_term \<box> l \<cdot> (?sig2 \<circ>\<^sub>s ?sig)\<rangle>"
    by (simp only: subst_subst)
  have "rev_term \<box> t = rev_term \<box> C\<langle>r \<cdot> \<sigma>\<rangle>" by (simp add: t)
  also have "\<dots> = (rev_term \<box> (r \<cdot> \<sigma>)) \<cdot> ?sig" 
    by (simp only: rev_term_ctxt_apply[OF uC urs], simp add: get_var_subst[OF ul] get_var_subst[OF ur]
      bspec[OF same_vars rule, simplified])
  also have "\<dots> = (rev_term ?revr ?xsig) \<cdot> ?sig" using rev_term_subst_apply[OF ur, of \<box> \<sigma>] bspec[OF same_vars rule, simplified] by simp
  also have "\<dots> = (rev_ctxt \<box> (term_to_ctxt ?xsig) \<circ>\<^sub>c ?revr)\<langle>Var (get_var ?xsig)\<rangle> \<cdot> ?sig" by (simp only: rev_term_to_rev_ctxt[OF uxsig urr]) 
  also have "\<dots> = (rev_ctxt \<box> (term_to_ctxt ?xsig))\<langle>?revr \<langle>Var (get_var ?xsig)\<rangle>\<rangle> \<cdot> ?sig" by simp
  also have "\<dots> = (rev_ctxt \<box> (term_to_ctxt ?xsig))\<langle>rev_term \<box> r \<cdot> ?sig2\<rangle> \<cdot> ?sig" by (simp only: bspec[OF same_vars rule, simplified], simp only: rev_ctxt_to_rev_term[OF ur, of \<box> \<sigma>, simplified])
  also have "\<dots> = ?C \<langle>rev_term \<box> r \<cdot> ?sig2 \<cdot> ?sig\<rangle>" by simp
  finally have idr: "rev_term \<box> t = ?C \<langle>rev_term \<box> r \<cdot> (?sig2 \<circ>\<^sub>s ?sig)\<rangle>"
    by (simp only: subst_subst)
  show ?thesis using rrule unfolding idl idr by auto
qed

lemma unary_funas_conv: 
  assumes "unary_term l"
  and "(f,i) \<in> funas_term l"
  shows "i = 1"
using assms by (induct l, auto)

lemma funas_unary_conv:
  assumes "\<forall> (f,i) \<in> funas_term l. i = 1"
  shows "unary_term l"
using assms 
proof (induct l, simp)
  case (Fun f ss)
  then have "length ss = 1" by auto
  from this obtain s where ss: "ss = [s]" by (cases ss, simp, cases "tl ss", auto)
  with Fun have s: "unary_term s" by auto
  from s ss show ?case by auto 
qed
   
lemma vars_term_unary_is_get_var: assumes "unary_term t" shows "vars_term t = {get_var t}"
using assms by (induct rule: unary_term_induct, auto)

lemma unary_rev_term: fixes t :: "('f,'v)term" assumes "unary_term t" shows "unary_term (rev_term \<box> t)"
proof -
  {
    fix C :: "('f,'v)ctxt"
    assume "unary_ctxt C"
    with assms have "unary_term (rev_term C t)"
    proof (induct arbitrary: C rule: unary_term_induct)
      case (Fun f s C) then show ?case by auto
    next
      case (Var x C) then show ?case by (simp, induct rule: unary_ctxt_induct, auto)
    qed
  }
  then show ?thesis by auto
qed

lemma unary_sig_to_unary_term: assumes F: "unary_sig F"
  and t: "funas_term t \<subseteq> F"
  shows "unary_term t"
using t proof (induct t)
  case (Var x) then show ?case by simp
next
  case (Fun f ss)
  with F have "length ss = 1" unfolding unary_sig_def by auto
  from this obtain s where ss: "ss = [s]" by (cases ss, simp, cases "tl ss", auto)
  with Fun show ?case by auto
qed


lemma rev_term_rev_term_id: 
  assumes "unary_term t"
  shows "rev_term \<box> (rev_term \<box> t) = t" (is "rev_term ?box _ = _")
using assms 
proof (induct t rule: unary_term_induct, simp)
  case (Fun f t)
  have ub: "unary_ctxt ?box" by simp
  let ?C = "More f [] \<box> []" 
  let ?rev = "rev_term \<box>"
  have ur: "unary_term (?rev t)" by (rule unary_rev_term[OF Fun(1)])
  have var: "get_var (?rev t) = get_var t" using get_var_rev_term[OF Fun(1)] by simp
  have "?rev (?rev (Fun f [t])) = 
    ?rev (rev_term ?C t)" by simp
  also have "\<dots> = ?rev (rev_term ?C \<box>\<langle>t\<rangle>)" by simp
  also have "\<dots> = ?rev (?rev t \<cdot> subst (get_var t) ?C)" unfolding rev_term_ctxt_apply[OF ub Fun(1), of ?C] by simp
  also have "\<dots> = Fun f [(rev_ctxt \<box> (term_to_ctxt (?rev t)))\<langle>Var (get_var t)\<rangle>]" unfolding rev_term_subst_apply[OF ur ub] by (simp add: subst_def var)
  also have "\<dots> = Fun f [?rev (?rev t)]" using rev_term_to_rev_ctxt[symmetric, OF ur ub, simplified, simplified var] by simp
  also have "\<dots> = Fun f [t]" using Fun(2) by simp
  finally show ?case .
qed

lemma unary_sig_unary_term: assumes "unary_sig (funas_trs R)"
  and "(l,r) \<in> R"
  shows "unary_term l \<and> unary_term r"
proof -
  from assms have "unary_sig (funas_term l)" and "unary_sig (funas_term r)"
    unfolding unary_sig_def funas_trs_def funas_rule_def [abs_def] by auto
  with funas_unary_conv[of l] funas_unary_conv[of r] show ?thesis unfolding unary_sig_def by auto
qed

lemma string_reversal_one_way_SN_rel: 
  assumes unary: "unary_sig (funas_trs (R \<union> S))" and 
   SN: "SN_rel (rstep (rev_trs R)) (rstep (rev_trs S))" 
  shows "SN_rel (rstep R) (rstep S)"
proof (cases "R = {}")
  case True
  show ?thesis unfolding True by (auto simp: SN_rel_defs)
next
  case False
  let ?F = "funas_trs (R \<union> S)"
  from SN_rel_imp_wf_reltrs[OF SN] have wf: "wf_reltrs (rev_trs R) (rev_trs S)" by auto
  from wf[unfolded wf_reltrs.simps] have wfR: "wf_trs (rev_trs R)" 
    and varcond: "\<And> l r. (l,r) \<in> rev_trs S \<Longrightarrow> (vars_term r \<subseteq> vars_term l)" 
    using False unfolding rev_trs_def by auto
  {
    fix l r
    assume lr: "(l,r) \<in> R \<union> S"
    from unary lr have ul: "unary_term l" and ur: "unary_term r" using unary_sig_unary_term[OF unary lr] by auto
    from lr have rlv: "(rev_term \<box> l, rev_term \<box> r) \<in> rev_trs R \<union> rev_trs S"
      unfolding rev_trs_def by force
    from wfR varcond rlv have vars: "vars_term (rev_term \<box> r) \<subseteq> vars_term (rev_term \<box> l)" unfolding wf_trs_def by force
    from lr have "(l,r) \<in> S \<or> (rev_term \<box> l, rev_term \<box> r) \<in> rev_trs R" 
      unfolding rev_trs_def by force
    from vars have "vars_term r \<subseteq> vars_term l" 
      unfolding vars_term_unary_is_get_var[OF unary_rev_term[OF ul]] 
        get_var_rev_term[OF ul, of \<box>, simplified] 
        vars_term_unary_is_get_var[OF unary_rev_term[OF ur]] get_var_rev_term[OF ur, of \<box>, simplified]
        vars_term_unary_is_get_var[OF ul] vars_term_unary_is_get_var[OF ur] .
    note wf = this 
    from vars_term_unary_is_get_var[OF ul]
         vars_term_unary_is_get_var[OF ur]
         wf have "{get_var r} \<subseteq> {get_var l}" by auto
    then have "get_var l = get_var r" by auto
    note this wf
  }
  then have same_vars: "\<forall> (l,r) \<in> R \<union> S. get_var l = get_var r" and varcond: "\<And> l r. (l,r) \<in> S \<Longrightarrow> vars_term r \<subseteq> vars_term l" by blast+
  let ?R = "rev_trs R"
  let ?S = "rev_trs S"
  show ?thesis
  proof (rule sig_ext_relative_rewriting_var_cond[OF varcond])
    show "funas_trs R \<subseteq> ?F" by auto
  next
    show "funas_trs S \<subseteq> ?F" by auto
  next
    let ?r = "rev_term \<box>"
    {
      fix s t T
      assume step: "(s,t) \<in> sig_step ?F (rstep T)" and T: "T \<subseteq> R \<union> S"
      from sig_stepE[OF step] have step: "(s,t) \<in> rstep T"
        and s: "funas_term s \<subseteq> ?F" and t: "funas_term t \<subseteq> ?F" by auto
      have us: "unary_term s" by (rule unary_sig_to_unary_term[OF unary s])
      have ut: "unary_term t" by (rule unary_sig_to_unary_term[OF unary t])
      from rstep_imp_rev_rstep[OF us ut _ step] same_vars T
      have "(?r s, ?r t) \<in> rstep (rev_trs T)"  by auto
    } note main = this
    show "SN_rel (sig_step ?F (rstep R)) (sig_step ?F (rstep S))" 
    proof (rule SN_rel_map[OF SN, of _ ?r])
      fix s t
      assume "(s,t) \<in> sig_step ?F (rstep R)"
      from main[OF this] have "(?r s, ?r t) \<in> rstep ?R" by auto
      then show "(?r s, ?r t) \<in> (rstep ?R \<union> rstep ?S)^* O rstep ?R O (rstep ?R \<union> rstep ?S)^*" by auto
    next
      fix s t 
      assume "(s,t) \<in> sig_step ?F (rstep S)"
      from main[OF this] have "(?r s, ?r t) \<in> rstep ?S" by simp
      then show "(?r s, ?r t) \<in> (rstep ?R \<union> rstep ?S)^*" by auto
    qed
  qed
qed

lemma unary_rev_trs: assumes unary: "unary_sig (funas_trs R)"
  shows "unary_sig (funas_trs (rev_trs R))"
  unfolding unary_sig_def funas_trs_def  rev_trs_def  
proof (clarify, simp, clarify)      
  fix f n l r
  assume fn: "(f,n) \<in> funas_rule (rev_term \<box> l, rev_term \<box> r)" and lr: "(l,r) \<in> R"
  from unary_sig_unary_term[OF unary lr] have l: "unary_term l" and r: "unary_term r" by auto
  from unary_funas_conv[OF unary_rev_term[OF l]] unary_funas_conv[OF unary_rev_term[OF r]] fn
  show "n = Suc 0" unfolding funas_rule_def by auto
qed

lemma rev_trs_rev_trs_id: assumes unary: "unary_sig (funas_trs R)"
shows "rev_trs (rev_trs R) = R"
proof -
  {
    fix l r
    assume lr: "(l,r) \<in> R"
    with unary_sig_unary_term[OF unary] have ul: "unary_term l" and ur: "unary_term r" by auto
    from rev_term_rev_term_id[OF ul] rev_term_rev_term_id[OF ur]
    have "rev_term \<box> (rev_term \<box> l) = l" and "rev_term \<box> (rev_term \<box> r) = r" by auto
  }
  then show ?thesis unfolding rev_trs_def by force
qed

lemma string_reversal_SN_rel:
  assumes unary: "unary_sig (funas_trs (R \<union> S))" 
  shows "SN_rel (rstep (rev_trs R)) (rstep (rev_trs S)) = SN_rel (rstep R) (rstep S)"
proof (rule iffI, rule string_reversal_one_way_SN_rel[OF unary])
  assume SN: "SN_rel (rstep R) (rstep S)"
  have id: "rev_trs R \<union> rev_trs S = rev_trs (R \<union> S)" unfolding rev_trs_def by auto
  from unary have unaryRS: "unary_sig (funas_trs R)" "unary_sig (funas_trs S)"
    unfolding funas_trs_def unary_sig_def by auto    
  show "SN_rel (rstep (rev_trs R)) (rstep (rev_trs S))"
    by (rule string_reversal_one_way_SN_rel, unfold id,
      rule unary_rev_trs[OF unary], 
      unfold rev_trs_rev_trs_id[OF unaryRS(1)] rev_trs_rev_trs_id[OF unaryRS(2)], rule SN)
qed

lemma string_reversal: assumes unary: "unary_sig (funas_trs R)"
   shows "SN (rstep (rev_trs R)) = SN (rstep R)"
  using string_reversal_SN_rel[of R "{}"] unary unfolding rev_trs_def by auto

lemma string_reversal_qrstep: assumes unary: "unary_sig (funas_trs R)"
  and SN: "SN (rstep (rev_trs R))"
  shows "SN (qrstep nfs Q R)"
  by (rule SN_subset[OF SN[unfolded string_reversal[OF unary]]], auto)

lemma string_reversal_qrstep_SN_rel: assumes unary: "unary_sig (funas_trs (R \<union> S))"
  and SN: "SN_qrel (nfs',{},rev_trs R,rev_trs S)"
  shows "SN_qrel (nfs,Q,R,S)"
proof (rule SN_qrel_mono)
  show "SN_qrel (nfs,{},R,S)" using string_reversal_SN_rel[OF unary] SN
    by simp
qed auto

end

