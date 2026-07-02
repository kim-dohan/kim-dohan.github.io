(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Icap
imports
  TRS.Q_Restricted_Rewriting
  First_Order_Rewriting.Unification_More
  "HOL-Library.Countable"
  Auxx.Name
begin

section \<open>Preliminaries\<close>

text \<open>Combined set of left-hand sides and right-hand sides of a TRS.\<close>
definition
  terms :: "('f, 'v) trs \<Rightarrow> ('f, 'v) terms"
where
  "terms R = lhss R \<union> rhss R"

section \<open>A semantic version of cap\<close>

text \<open>The \emph{cap} of a term is the `upper' part which is definitely not
changed by rewriting. Parts which are potentially changed, are replaced by
fresh variables (represented by @{term "Var (Inl ())"} below).\<close>
type_synonym ('f, 'v) cap_fun =
  "('f, 'v) trs \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, unit + 'v) term"

fun cap :: "('f, 'v) cap_fun" where
  "cap R Q S (Var x) = (
    if \<exists>\<sigma> nfs. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q \<and> Var x \<cdot> \<sigma> \<notin> NF (qrstep nfs Q R)
      then Var (Inl ())
      else Var (Inr x))"
| "cap R Q S (Fun f ts) = (
    if \<exists>\<sigma> nfs u. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q \<and> (Fun f ts \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>* O rqrstep nfs Q R
      then Var (Inl ())
      else Fun f (map (cap R Q S) ts))"

(*The substitution is needed in the proof of Lemma 3.8*)
fun
  fresh_instances_subst ::
    "('f, unit + 'v) term \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) terms" ("\<lbrace>_\<rbrace>'__" [0, 999] 61)
where
  "\<lbrace>Var (Inl ())\<rbrace>_\<sigma> = UNIV" |
  "\<lbrace>Var (Inr x) \<rbrace>_\<sigma> = {Var x \<cdot> \<sigma>}" |
  "\<lbrace>Fun f ss    \<rbrace>_\<sigma> = {Fun f ts | ts.
    length ts = length ss \<and> (\<forall>i<length ss. ts ! i \<in> \<lbrace>ss ! i\<rbrace>_\<sigma>)}"

abbreviation
  fresh_instances :: "('f, unit + 'v) term \<Rightarrow> ('f, 'v) terms" ("\<lbrace>_\<rbrace>" [0] 61)
where
  "\<lbrace>t\<rbrace> \<equiv> \<lbrace>t\<rbrace>_Var"

lemma fresh_instances_subst_not_empty [simp]:
  "\<lbrace>t\<rbrace>_\<sigma> \<noteq> {}"
proof (induct t)
  case (Var x) then show ?case by (cases x) auto
next
  case (Fun f ts)
  then have "\<forall>t\<in>set ts. \<exists>s. s \<in> \<lbrace>t\<rbrace>_\<sigma>" by auto
  from bchoice [OF this] obtain s
    where in_class: "\<forall>t\<in>set ts. s t \<in> \<lbrace>t\<rbrace>_\<sigma>" by auto
  let ?ss = "map (\<lambda>i. (s (ts ! i))) [0 ..< length ts]"
  have len: "length ?ss = length ts" by simp
  from in_class have "\<forall>i<length ts. (s (ts ! i)) \<in> \<lbrace>ts ! i\<rbrace>_\<sigma>" by auto
  then have "\<forall>i<length ts. (?ss ! i) \<in> \<lbrace>ts ! i\<rbrace>_\<sigma>" by simp
  with len have "Fun f ?ss \<in> \<lbrace>Fun f ts\<rbrace>_\<sigma>" by auto
  then show ?case by best
qed

lemma fresh_instances_subst_subst:
  "\<lbrace>t\<rbrace>_\<tau> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> \<lbrace>t\<rbrace>_(\<tau> \<circ>\<^sub>s \<sigma>)"
proof (induct t arbitrary: \<sigma> \<tau>)
  case (Var x)
  show ?case
  proof (cases x)
    case (Inl n)
    have "\<lbrace>Var x\<rbrace>_\<tau> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> = UNIV \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>" by (simp add: Inl)
    moreover have "\<lbrace>Var x\<rbrace>_(\<tau> \<circ>\<^sub>s \<sigma>) = UNIV" by (simp add: Inl)
    moreover have "UNIV \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> UNIV" by auto
    ultimately show ?thesis by blast
  next
    case (Inr y) then show ?thesis by (simp add: subst_compose)
  qed
next
  case (Fun f ts)
  show ?case
  proof
    fix t assume in_Fun: "t \<in> \<lbrace>Fun f ts\<rbrace>_\<tau> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
    then obtain ss where len: "length ss = length ts" and "\<forall>i<length ts. (ss ! i) \<in> \<lbrace>ts ! i\<rbrace>_\<tau>"
      and t: "t = Fun f (map (\<lambda>t. t\<cdot>\<sigma>) ss)" by auto
    moreover from Fun have "\<forall>i<length ts. \<lbrace>ts ! i\<rbrace>_\<tau> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> \<lbrace>ts ! i\<rbrace>_(\<tau> \<circ>\<^sub>s \<sigma>)" by auto
    ultimately have "\<forall>i<length ts. (ss ! i) \<cdot> \<sigma> \<in> \<lbrace>ts ! i\<rbrace>_(\<tau> \<circ>\<^sub>s \<sigma>)" by auto
    with len show "t \<in> \<lbrace>Fun f ts\<rbrace>_(\<tau> \<circ>\<^sub>s \<sigma>)" unfolding t by auto
  qed
qed

lemma fresh_instances_subst: "\<lbrace>t\<rbrace> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> \<lbrace>t\<rbrace>_\<sigma>"
proof -
  have "\<lbrace>t\<rbrace>_Var \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> \<lbrace>t\<rbrace>_(Var \<circ>\<^sub>s \<sigma>)" by (rule fresh_instances_subst_subst)
  then show ?thesis by simp
qed

definition is_ecap :: "('f, 'v) cap_fun \<Rightarrow> bool" where
  "is_ecap ecap \<longleftrightarrow> (\<forall>R Q S t f ts x.
    \<lbrace>cap R Q S t\<rbrace> \<subseteq> \<lbrace>ecap R Q S t\<rbrace> \<and>
    ecap R Q S (Fun f ts) \<in> {Var (Inl ()), Fun f (map (ecap R Q S) ts)} \<and>
    ecap R Q S (Var x) \<in> {Var (Inl ()), Var (Inr x)})"

lemma is_ecapI [intro]:
  assumes "\<And>R Q S t f ts x. \<lbrace>cap R Q S t\<rbrace> \<subseteq> \<lbrace>ecap R Q S t\<rbrace>
    \<and> ecap R Q S (Fun f ts) \<in> {Var (Inl ()), Fun f (map (ecap R Q S) ts)}
    \<and> ecap R Q S (Var x) \<in> {Var (Inl ()), Var (Inr x)}"
  shows "is_ecap ecap"
using assms unfolding is_ecap_def by auto

lemma is_ecapE [elim]:
  assumes "is_ecap ecap"
    and "\<lbrakk>\<lbrace>cap R Q S t\<rbrace> \<subseteq> \<lbrace>ecap R Q S t\<rbrace>;
      ecap R Q S (Fun f ts) \<in> {Var (Inl ()), Fun f (map (ecap R Q S) ts)};
      ecap R Q S (Var x) \<in> {Var (Inl ()), Var (Inr x)}\<rbrakk> \<Longrightarrow> P"
  shows P
using assms unfolding is_ecap_def by simp

lemma is_ecap_cap [intro]:
  "is_ecap (cap :: ('f, 'v) cap_fun)"
proof
  fix R :: "('f, 'v) trs" and Q S t f ts x nfs
    show "\<lbrace>cap R Q S t\<rbrace> \<subseteq> \<lbrace>cap R Q S t\<rbrace>
      \<and> cap R Q S (Fun f ts) \<in> {Var (Inl ()), Fun f (map (cap R Q S) ts)}
      \<and> cap R Q S (Var x) \<in> {Var (Inl ()), Var (Inr x)}"
  by (induct t) simp_all
qed

lemma vars_term_ecap:
  assumes ecap: "is_ecap ecap"
  shows "vars_term (ecap R Q S t) \<subseteq> Inr ` vars_term t \<union> {Inl ()}"
proof -
  note ecap = ecap [unfolded is_ecap_def, rule_format, of R Q S, THEN conjunct2]
  show ?thesis 
  proof (induct t)
    case (Var x)
    from ecap [of f ts x] show ?case by auto
  next
    case (Fun f ts)
    with ecap [of f ts x] show ?case by fastforce
  qed
qed

lemma UNIV_term_not_singleton [intro]:
  "(UNIV :: ('f, 'v) terms) = {t} \<Longrightarrow> False"
  by (induct t) auto

lemma UNIV_fresh_instances_substE:
  assumes "UNIV = \<lbrace>t\<rbrace>_\<sigma>" and "t = Var (Inl ()) \<Longrightarrow> P" shows P
proof (cases t)
  case (Var x) show ?thesis using assms UNIV_term_not_singleton unfolding Var 
    by (cases x, auto)
next
  case (Fun f ts) show ?thesis using assms unfolding Fun by auto
qed

lemma Var_Inr_fresh_instancesE:
  assumes "\<lbrace>Var (Inr x)\<rbrace> \<subseteq> \<lbrace>t\<rbrace>" and "t = Var (Inl ()) \<Longrightarrow> P"
    and "t = Var (Inr x) \<Longrightarrow> P"
  shows P
proof (cases t)
  case (Var y) show ?thesis using assms unfolding Var by (cases y) auto
next
  case (Fun f ts) show ?thesis using assms unfolding Fun by auto
qed

lemma Fun_fresh_instancesE:
  assumes "Fun f ts \<in> \<lbrace>t\<rbrace>"
    and "t = Var (Inl ()) \<Longrightarrow> P"
    and "\<And>ss. \<lbrakk>t = Fun f ss;length ts = length ss; \<forall>i<length ss. ts ! i \<in> \<lbrace>ss ! i\<rbrace>\<rbrakk> \<Longrightarrow> P"
  shows P
proof (cases t)
  case (Var x) show ?thesis using assms unfolding Var by (cases x) auto
next
  case (Fun g ss) show ?thesis using assms unfolding Fun by auto
qed

lemma fresh_instances_Var_fresh: "t \<in> \<lbrace>Var (Inl ())\<rbrace>_\<sigma>" by simp

lemma fresh_instances_Var_old:
  assumes "t \<in> \<lbrace>Var (Inr x)\<rbrace>_\<sigma>" and "t = Var x \<cdot> \<sigma> \<Longrightarrow> P" shows P
using assms by simp

lemma equiv_class_Fun:
  assumes "t \<in> \<lbrace>Fun f ts\<rbrace>_\<sigma>"
    and "\<And>ss. \<lbrakk>t = Fun f ss; length ss = length ts; \<forall>i<length ts. ss ! i \<in> \<lbrace>ts ! i\<rbrace>_\<sigma>\<rbrakk> \<Longrightarrow> P"
  shows P
using assms by auto

lemma cap_Var_fresh:
  assumes "is_ecap ecap" and "cap R Q S (Var x) = Var (Inl ())"
  shows "ecap R Q S (Var x) = Var (Inl ())"
using assms(1) proof
  assume cap: "\<lbrace>cap R Q S (Var x)\<rbrace> \<subseteq> \<lbrace>ecap R Q S (Var x)\<rbrace>"
  show "ecap R Q S (Var x) = Var (Inl ())"
  proof (cases "cap R Q S (Var x) = Var (Inl ())")
    case True
    from cap [unfolded True] show ?thesis using UNIV_fresh_instances_substE [of _ Var] by auto
  next
    case False
    then have "cap R Q S (Var x) = Var (Inr x)" by (auto simp: split_ifs)
    with assms have False by auto
    then show ?thesis by simp
  qed
qed

lemma is_ecap_Var:
  assumes "is_ecap ecap" and "ecap R Q S (Var x) = Var (Inr x)"
  shows "cap R Q S (Var x) = Var (Inr x)"
proof -
  from assms have "ecap R Q S (Var x) \<noteq> Var (Inl ())" by auto
  with cap_Var_fresh [OF assms(1)]
    have "cap R Q S (Var x) \<noteq> Var (Inl ())" by blast
  then show ?thesis by (simp add: split_ifs)
qed

lemma cap_Var_old:
  assumes "is_ecap ecap" and "cap R Q S (Var x) = Var (Inr x)"
  shows "ecap R Q S (Var x) = Var (Inl ()) \<or> ecap R Q S (Var x) = Var (Inr x)"
using assms(1) proof
  assume cap: "\<lbrace>cap R Q S (Var x)\<rbrace> \<subseteq> \<lbrace>ecap R Q S (Var x)\<rbrace>"
  from Var_Inr_fresh_instancesE [OF this [unfolded assms]] show ?thesis by auto
qed

lemma cap_Var_cases:
  assumes "cap R Q S (Var x) = Var (Inr x) \<Longrightarrow> P"
    and "cap R Q S (Var x) = Var (Inl ()) \<Longrightarrow> P"
  shows P
using assms by (auto simp: split_ifs)

lemma ecap_Var_not_fresh:
  assumes "is_ecap ecap" and "ecap R Q S (Var x) \<noteq> Var (Inl ())"
  shows "ecap R Q S (Var x) = Var (Inr x)"
using assms(1) proof
  assume cap: "\<lbrace>cap R Q S (Var x)\<rbrace> \<subseteq> \<lbrace>ecap R Q S (Var x)\<rbrace>"
  show ?thesis
  proof (rule cap_Var_cases)
    assume "cap R Q S (Var x) = Var (Inr x)"
    from cap_Var_old [OF assms(1) this] and assms show ?thesis by simp
  next
    assume "cap R Q S (Var x) = Var (Inl ())"
    from cap_Var_fresh [OF assms(1) this] and assms show ?thesis by simp
  qed
qed

lemma cap_Fun_cases:
  assumes "cap R Q S (Fun f ts) = Var (Inl ()) \<Longrightarrow> P"
    and "cap R Q S (Fun f ts) = Fun f (map (cap R Q S) ts) \<Longrightarrow> P"
  shows P
using assms unfolding cap.simps split_ifs by blast

lemma cap_Fun_fresh:
  assumes "is_ecap ecap" and "cap R Q S (Fun f ts) = Var (Inl ())"
  shows "ecap R Q S (Fun f ts) = Var (Inl ())"
using assms(1)
proof
  assume "\<lbrace>cap R Q S (Fun f ts)\<rbrace> \<subseteq> \<lbrace>ecap R Q S (Fun f ts)\<rbrace>"
  from UNIV_fresh_instances_substE [of _ Var] and this [unfolded assms] show ?thesis by auto
qed

lemma ecap_Fun:
  assumes "is_ecap ecap"
  shows "ecap R Q S (Fun f ts) = Var (Inl ())
    \<or> ecap R Q S (Fun f ts) = Fun f (map (ecap R Q S) ts)"
using assms by auto


lemma ecap_poss_imp_start_poss:
  assumes ecap: "is_ecap ecap"
    and p: "p \<in> poss (ecap R Q S t)"
  shows "p \<in> poss t"
  using p 
proof (induct p arbitrary: t)
  case Nil then show ?case by auto
next
  case (Cons i p)
  from Cons obtain f ets where efts: "ecap R Q S t = Fun f ets" by (cases "ecap R Q S t", auto)
  note ecap' = ecap [unfolded is_ecap_def, rule_format, of R Q S]
  have "\<exists> ts. t = Fun f ts"
  proof (cases t)
    case (Var x)
    from ecap' [of _ _ _ x] efts show ?thesis unfolding Var by auto
  next
    case (Fun g ts)
    from ecap' [of _ g ts] efts show ?thesis unfolding Fun by auto
  qed
  then obtain ts where t: "t = Fun f ts" by auto
  note ecap' = ecap' [of "Fun f ts" f ts] 
  from ecap' efts have efts: "ecap R Q S t = Fun f (map (ecap R Q S) ts)" unfolding t by auto
  from Cons(2) [unfolded efts] have i: "i < length ts" and p: "p \<in> poss (ecap R Q S (ts ! i))" by auto
  from Cons(1) [OF p] i show ?case unfolding t by auto
qed  

lemma ecap_no_above_steps:
  assumes ecap: "is_ecap ecap"
    and steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>*"
    and NF: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
    and p: "p \<in> poss (ecap R Q S t)"
    and step: "(u, v) \<in> qrstep_r_p_s nfs Q R r p' \<tau>"
  shows "\<not> p' <\<^sub>p p"
  using p steps step
proof (induct p arbitrary: p' t u v)
  case Nil show ?case by simp
next
  case (Cons i p)
  note ecap' = ecap [unfolded is_ecap_def, rule_format, of R Q S]
  from ecap_poss_imp_start_poss [OF ecap, OF Cons(2)]
  obtain f ts where t: "t = Fun f ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)" by (cases t, auto)
  note ecap' = ecap' [of "Fun f ts" f ts]
  let ?e = "ecap R Q S"
  let ?c = "cap R Q S"
  let ?QR = "\<lambda> nfs. qrstep nfs Q R"
  from Cons(2) [unfolded t] ecap' have et: "?e (Fun f ts) = Fun f (map ?e ts)" by (cases "?e (Fun f ts)", auto)
  from Cons(2) [unfolded t et] have pet: "p \<in> poss (?e (ts ! i))" by auto
  from cap_Fun_fresh [OF ecap, of R Q S f ts] et have ct: "?c (Fun f ts) \<noteq> Var (Inl ())" by (cases "?c (Fun f ts)", auto)
  let ?Prop = "\<exists> \<sigma> nfs. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q \<and> (\<exists> u. (Fun f ts \<cdot> \<sigma>, u) \<in> (?QR nfs)\<^sup>* O rqrstep nfs Q R)"
  from ct [simplified] have "\<not> ?Prop" by (cases ?Prop, auto)
  with NF have no_root: "\<not> (\<exists> u nfs. (Fun f ts \<cdot> \<sigma>, u) \<in> (?QR nfs)\<^sup>* O rqrstep nfs Q R)" by auto 
  from Cons(3) [unfolded t] have steps: "(Fun f ts \<cdot> \<sigma>, u) \<in> (?QR nfs)\<^sup>*" by auto
  from Cons(4) have "(u, v) \<in> ?QR nfs" unfolding qrstep_qrstep_r_p_s_conv by blast
  with steps no_root have no_root_uv: "(u, v) \<notin> rqrstep nfs Q R" by auto
  {
    assume p': "p' = []"
    obtain ll rr where r: "r = (ll, rr)" by force
    note step = Cons(4) [unfolded qrstep_r_p_s_def p' r fst_conv snd_conv]
    have "(u, v) \<in> rqrstep nfs Q R" 
      by (rule rqrstepI [of ll \<tau> _ rr], insert step, auto)
    with no_root_uv have False by simp
  }
  then obtain j q where p': "p' = j # q" by (cases p', auto)
  show ?case
  proof (cases "j = i")
    case False
    then show ?thesis unfolding p' by auto
  next
    case True
    let ?QR = "qrstep nfs Q R"
    have  "(\<exists>us nfs. length us = length ts
    \<and> u = Fun f us \<and> (\<forall>i<length ts. ((ts ! i) \<cdot> \<sigma>, us ! i) \<in> ?QR\<^sup>*))"
      using qrsteps_rqrstep_cases [of f "map (\<lambda>t. t \<cdot> \<sigma>) ts" u nfs Q R, OF steps [simplified], unfolded length_map] no_root  using nth_map [of _ ts "\<lambda>t. t \<cdot> \<sigma>"] by auto
    then obtain us where len: "length us = length ts"
      and u: "u = Fun f us"
      and steps: "(ts ! i \<cdot> \<sigma>, us ! i) \<in> ?QR\<^sup>*" using i by auto
    from Cons(4) [unfolded p' True] have step: "(u, v) \<in> qrstep_r_p_s nfs Q R r ([i] @ q) \<tau>" by simp
    from qrstep_subt_at_gen [OF step [unfolded u]] i have "(us ! i, v |_ [i]) \<in> qrstep_r_p_s nfs Q R r q \<tau>" by auto 
    from Cons(1) [OF pet steps this] have "\<not> q <\<^sub>p p" .
    then show ?thesis unfolding p' True by auto
  qed
qed    

(* Lemma 3.8 of René's Thesis *)
lemma ecap_steps:
  assumes ecap: "is_ecap ecap"
    and step: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>*"
    and NF: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
  shows "u \<in> \<lbrace>ecap R Q S t\<rbrace>_\<sigma>"
using step proof (induct t arbitrary: u)
  case (Var x)
  show ?case
  proof (cases "Var x \<cdot> \<sigma> \<in> NF (qrstep nfs Q R)")
    case True
    show ?thesis
    proof (cases rule: cap_Var_cases)
      assume 1: "cap R Q S (Var x) = Var (Inl ())"
      (*this case is the reason for the subst in fresh_instances_subst.
      Otherwise we would have to prove "u : UNIV \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>", which does not
      hold.*)
      from cap_Var_fresh [OF ecap this] show ?thesis by auto
    next
      assume "cap R Q S (Var x) = Var (Inr x)"
      from cap_Var_old [OF ecap this]
        have "ecap R Q S (Var x) = Var (Inl ()) \<or> ecap R Q S (Var x) = Var (Inr x)" .
      then show ?thesis
      proof
        assume "ecap R Q S (Var x) = Var (Inl ())"
        then show ?thesis by auto
      next
        assume "ecap R Q S (Var x) = Var (Inr x)"
        moreover from Var and True have "u = Var x \<cdot> \<sigma>" by (induct rule: rtrancl.induct) auto
        ultimately show ?thesis by auto
      qed
    qed
  next
    case False
    with NF have "cap R Q S (Var x) = Var (Inl ())" by auto
    from cap_Var_fresh [OF ecap this] show ?thesis by auto
  qed
next
  case (Fun f ss)
  have "(\<exists>us. length us = length ss
    \<and> u = Fun f us \<and> (\<forall>i<length ss. ((ss ! i) \<cdot> \<sigma>, us ! i) \<in> (qrstep nfs Q R)\<^sup>*))
    \<or> (Fun f ss \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>* O (rqrstep nfs Q R) O (qrstep nfs Q R)\<^sup>*"
    using qrsteps_rqrstep_cases [of f "map (\<lambda>t. t \<cdot> \<sigma>) ss" u nfs Q R,
      OF Fun(2) [simplified], unfolded length_map]
      using nth_map [of _ ss "\<lambda>t. t \<cdot> \<sigma>"] by auto
  then show ?case
  proof
    assume "(Fun f ss \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>* O (rqrstep nfs Q R) O (qrstep nfs Q R)\<^sup>*"
    then obtain v where "(Fun f ss \<cdot> \<sigma>, v) \<in> (qrstep nfs Q R)\<^sup>* O (rqrstep nfs Q R)" by auto
    with NF
    have "cap R Q S (Fun f ss) = Var (Inl ())" by auto
    from cap_Fun_fresh [OF ecap this] show ?thesis by auto
  next
    assume "\<exists>us. length us = length ss
      \<and> u = Fun f us \<and> (\<forall>i<length ss. ((ss ! i) \<cdot> \<sigma>, us ! i) \<in> (qrstep nfs Q R)\<^sup>*)"
    then obtain us where len: "length us = length ss" and u: "u = Fun f us"
      and steps: "\<forall>i<length ss. ((ss ! i)\<cdot>\<sigma>, us ! i) \<in> (qrstep nfs Q R)\<^sup>*" by auto
    with Fun have args: "\<forall>i<length ss. us ! i \<in> \<lbrace>ecap R Q S (ss ! i)\<rbrace>_\<sigma>" by auto
    from ecap_Fun [OF ecap]
      have "ecap R Q S (Fun f ss) = Var (Inl ())
        \<or> ecap R Q S (Fun f ss) = Fun f (map (ecap R Q S) ss)" .
    then show ?thesis
    proof
      assume "ecap R Q S (Fun f ss) = Var (Inl ())" then show ?thesis by auto
    next
      assume ecap_map: "ecap R Q S (Fun f ss) = Fun f (map (ecap R Q S) ss)"
      from len and args have "Fun f us \<in> \<lbrace>ecap R Q S (Fun f ss)\<rbrace>_\<sigma>"
        unfolding ecap_map by auto
      then show ?thesis unfolding u .
    qed
  qed
qed

lemma poss_fresh_instances_subst: "p \<in> poss et \<Longrightarrow> u \<in> \<lbrace>et\<rbrace>_\<sigma> \<Longrightarrow> p \<in> poss u"
proof (induct p arbitrary: u et)
  case Nil then show ?case by auto
next
  case (Cons i p)
  from Cons(2) obtain e ts where et: "et = Fun e ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)" by (cases et, auto)
  from Cons(3) [unfolded et] obtain us where u: "u = Fun e us" by (cases u, auto)
  from Cons(1) [OF p] Cons(3) [unfolded et] i show ?case unfolding u by auto
qed

lemma ecap_poss_imp_result_poss:
  assumes ecap: "is_ecap ecap"
    and steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>*"
    and NF: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
    and p: "p \<in> poss (ecap R Q S t)"
  shows "p \<in> poss u"
  by (rule poss_fresh_instances_subst [OF p ecap_steps [OF ecap steps NF]])

lemma first_step_subterm_qrsteps_ecap:
  assumes ecap: "is_ecap ecap"
    and pet: "p \<in> poss (ecap R Q S t)"
    and steps: "(t \<cdot> \<sigma>, v) \<in> (qrstep nfs Q R)^^n"
    and NF_set: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
    and neq: "t \<cdot> \<sigma> |_ p \<noteq> v |_ p"
  shows "\<exists> u m. (t |_ p \<cdot> \<sigma>, u) \<in> qrstep nfs Q R \<and> (replace_at (t \<cdot> \<sigma>) p u, v) \<in> (qrstep nfs Q R)^^m \<and> n = Suc m"
proof -
  let ?QR = "qrstep nfs Q R"
  from ecap_poss_imp_start_poss [OF ecap, OF pet] have pt: "p \<in> poss t" .
  then have pt\<sigma>: "p \<in> poss (t \<cdot> \<sigma>)" by auto
  obtain t\<sigma> where t\<sigma>: "t \<cdot> \<sigma> = t\<sigma>" by auto
  from pt have tp: "t |_ p \<cdot> \<sigma> = t\<sigma> |_ p" unfolding t\<sigma> [symmetric] by auto
  note no_above = ecap_no_above_steps [OF ecap _ NF_set, OF _ pet, of _ nfs]
  from steps pt\<sigma> neq no_above
  show ?thesis unfolding tp t\<sigma>
  proof (induct n arbitrary: t\<sigma>)
    case 0
    then show ?case by simp
  next
    case (Suc n t)
    from relpow_Suc_D2 [OF Suc(2)] obtain s where
      step: "(t, s) \<in> ?QR" and steps: "(s, v) \<in> ?QR^^n" by auto
    from step [unfolded qrstep_qrstep_r_p_s_conv]
    obtain r q \<sigma> where stepp: "(t, s) \<in> qrstep_r_p_s nfs Q R r q \<sigma>" by auto
    from Suc(5) [OF _ stepp] have "\<not> q <\<^sub>p p" by simp
    with pos_cases [of p q] have "p \<le>\<^sub>p q \<or> p \<bottom> q" by simp
    then show ?case
    proof
      assume le: "p \<le>\<^sub>p q"
      then obtain q' where q: "q = p @ q'" unfolding less_eq_pos_def by auto
      from qrstep_subt_at_gen [OF stepp [unfolded q]]
      have step: "(t |_ p, s |_ p) \<in> ?QR" unfolding qrstep_qrstep_r_p_s_conv by blast
      from qrstep_r_p_s_imp_poss [OF stepp] q have ps: "p \<in> poss s" by auto
      have id: "replace_at t p (s |_ p) = s" 
        unfolding ctxt_of_pos_term_qrstep_below [OF stepp le] using ps
        by (rule ctxt_supt_id)
      show ?thesis
        by (intro exI conjI, rule step, unfold id, rule steps, simp)
    next
      assume par: "p \<bottom> q"
      from parallel_pos_sym [OF this] have par': "q \<bottom> p" by auto
      have pt: "p \<in> poss t" by fact
      from parallel_qrstep_subt_at [OF stepp par' pt]
      have id: "t |_ p = s |_ p" and ps: "p \<in> poss s" by auto
      {
        fix u
        assume "(s, u) \<in> ?QR\<^sup>*"
        with step have "(t, u) \<in> ?QR\<^sup>*" by auto
      } note st_conv = this
      from Suc(1) [OF steps ps Suc(4) [unfolded id] Suc(5) [OF st_conv]]
      have "\<exists> u m. (s |_ p, u) \<in> ?QR \<and> (replace_at s p u, v) \<in> ?QR ^^ m \<and> n = Suc m" by auto
      then obtain u m where onestep: "(s |_ p, u) \<in> ?QR"
        and steps: "(replace_at s p u, v) \<in> ?QR ^^ m"
        and n: "n = Suc m" by auto
      show ?thesis
      proof (intro exI conjI, unfold id, rule onestep)
        have "(replace_at t p u, replace_at s p u) \<in> qrstep nfs Q R"
          by (rule parallel_qrstep_r_p_s [OF par pt stepp])
        from this steps
        show "(replace_at t p u, v) \<in> ?QR ^^ n" unfolding n 
          by (rule relpow_Suc_I2)
      qed simp
    qed
  qed
qed

fun
  class_to_term_intern :: "(nat \<Rightarrow> 'v) \<Rightarrow> nat \<Rightarrow> ('f, unit + 'v) term \<Rightarrow> nat \<times> (('f, 'v) term)"
where
  "class_to_term_intern iv i (Fun f ts) = (
    let (k, ss) = foldr (\<lambda>t (j, ss).
      let (k, s) = class_to_term_intern iv j t
      in (k, s # ss)) ts (i, [])
    in (k, Fun f ss))"
| "class_to_term_intern iv i (Var (Inl _)) = (i + 1, Var (iv i))"
| "class_to_term_intern iv i (Var (Inr x)) = (i,     Var x)"

lemma class_to_term_intern_vars:
  fixes t :: "('f, unit + 'v) term"
  assumes "class_to_term_intern iv i t = (j, s)"
  shows "i \<le> j \<and> (vars_term s \<subseteq> {x . Inr x \<in> vars_term t} \<union> {iv k | k. i \<le> k \<and> k < j})"
using assms
proof (induct t arbitrary: i j s)
  case (Var x i j s)
  then show ?case by (cases x, auto)
next
  case (Fun f ts i j sss)
  from Fun(2) obtain ss where sss: "sss = Fun f ss"
    by (cases sss, auto split: prod.split_asm)
  note Fun = Fun [unfolded sss]
  let ?f = "(\<lambda> t (j, ss). let (k, s) = class_to_term_intern iv j t
              in (k, s # ss))"
  let ?P = "\<lambda> s t i j. (vars_term s \<subseteq> {x . Inr x \<in> vars_term t} \<union> {iv k | k. i \<le> k \<and> k < j})"
  let ?Q = "\<lambda> ss ts i j. i \<le> j \<and> (\<forall> k < length ss. ?P (ss ! k) (ts ! k) i j) \<and> length ss = length ts"
  from Fun(2) have id: "foldr ?f ts (i, []) = (j, ss)" by (auto split: prod.split_asm)
  with Fun(1) have "?Q ss ts i j"
  proof (induct ts arbitrary: i j ss)
    case (Cons t ts i j sss)
    obtain i' ss where ts: "foldr ?f ts (i, []) = (i', ss)" by (cases "foldr ?f ts (i, [])", auto)
    obtain j' s where t: "class_to_term_intern iv i' t = (j', s)" by (cases "class_to_term_intern iv i' t", auto)
    from ts t Cons(3) have sss: "sss = s # ss" and j: "j = j'" by auto
    from Cons(2) [OF _ t] have t: "?P s t i' j'" and ij: "i' \<le> j'" by auto
    have ts: "?Q ss ts i i'"
      by (rule Cons(1) [OF _ ts], insert Cons(2), auto)
    have len: "length sss = Suc (length ss)" unfolding sss by simp
    from t ts ij show ?case unfolding len unfolding sss j unfolding all_Suc_conv by force
  qed auto
  note main = this
  {
    fix x
    assume "x \<in> vars_term (Fun f ss)"
    then obtain k where k: "k < length ss" and x: "x \<in> vars_term (ss ! k)"
      by (auto simp: set_conv_nth)
    with main have x: "x \<in> {x. Inr x \<in> vars_term (ts ! k)} \<union> {iv k | k. i \<le> k \<and> k < j}"
      by auto
    from k have "vars_term (ts ! k) \<subseteq> vars_term (Fun f ts)" using main by (auto simp: set_conv_nth)
    with x have "x \<in> {x. Inr x \<in> vars_term (Fun f ts)} \<union> {iv k | k. i \<le> k \<and> k < j}"
      by blast
  } note tedious = this
  show ?case unfolding sss using main tedious by auto
qed

lemma class_to_term_intern:
  assumes inj: "inj iv"
    and ivt: "\<And> x. Inr x \<in> vars_term t \<Longrightarrow> x \<notin> range iv"
  shows "\<lbrace>t\<rbrace>_\<sigma> = {snd (class_to_term_intern iv i t) \<cdot> \<tau> | \<tau>. (\<forall> x. x \<in> range iv \<or> \<sigma> x = \<tau> x)}" (is "_ = ?\<tau>s t i")
  using ivt
proof (induct t arbitrary: i)
  case (Var x i)
  show ?case 
  proof (cases x)
    case (Inl y)
    {
      fix u
      have "u \<in> ?\<tau>s (Var (Inl y)) i" 
        by (rule, rule exI [of _ "\<lambda> x. if x = iv i then u else \<sigma> x"], auto)
    }
    then show ?thesis unfolding Inl by simp
  next
    case (Inr y)
    then show ?thesis using Var unfolding Inr by force
  qed
next
  case (Fun f ts i)
  let ?valid = "\<lambda> \<tau>. (\<forall> x. x \<in> range iv \<or> \<sigma> x = \<tau> x)"
  show ?case (is "?l (Fun f ts) = ?r i (Fun f ts)")
  proof -
    let ?f = "(\<lambda> t (i, ss). let (j, s) = class_to_term_intern iv i t
      in (j, s # ss))"
    let ?g = "(\<lambda> t (i, ss, is, js). let (j, s) = class_to_term_intern iv i t
      in (j, s # ss, i # is, j # js))"
    obtain j us ii jj where foldg: "foldr ?g ts (i, [], [], []) = (j, us, ii, jj)" by (cases "foldr ?g ts (i, [], [], [])", auto)
    let ?P = "\<lambda> ts us ii jj k j. class_to_term_intern iv (ii ! k) (ts ! k)  = (jj ! k, us ! k) \<and> jj ! k \<le> j \<and> (\<forall> k'. k < k' \<and> k' < length ts \<longrightarrow> jj ! k' \<le> ii ! k)"
    from foldg have fold_prop: "i \<le> j \<and> foldr ?f ts (i,[]) = (j, us) \<and> length us = length ts \<and> length ii = length ts \<and> length jj = length ts \<and> (\<forall> k < length ts. ?P ts us ii jj k j)"
    proof (induct ts arbitrary: j us ii jj)
      case Nil then show ?case by simp
    next
      case (Cons t ts k us' ii' jj')
      obtain i' us ii jj where foldg: "foldr ?g ts (i,[],[],[]) = (i', us, ii, jj)" by (cases "foldr ?g ts (i, [], [], [])", auto)
      obtain j' u where cjt: "class_to_term_intern iv i' t = (j', u)" by (cases "class_to_term_intern iv i' t", auto)
      from foldg cjt have fold: "foldr ?g (t # ts) (i,[],[],[]) = (j', u # us, i' # ii, j' # jj)" by auto
      from fold [unfolded Cons(2)] have k: "k = j'" and us: "us' = u # us" and ii: "ii' = i' # ii" and jj: "jj' = j' # jj" by auto
      from Cons(1) [OF foldg] have ii': "i \<le> i'" and 
        foldf: "foldr ?f ts (i,[]) = (i', us)" and 
        lus: "length us = length ts" and 
        lii: "length ii = length ts" and 
        ljj: "length jj = length ts" and 
        comp: "\<forall>k < length ts. ?P ts us ii jj k i'"
        by auto
      from class_to_term_intern_vars [OF cjt] have i'j': "i' \<le> j'" by simp
      from ii' i'j'  have ij': "i \<le> j'" by auto
      show ?case
      proof (intro conjI,
          simp add: k ij', 
          simp add: foldf [simplified] us k cjt,
          simp add: us lus,
          simp add: ii lii,
          simp add: jj ljj, 
          intro allI impI, unfold k)
        fix k
        assume k: "k < length (t # ts)"
        show "?P (t # ts) us' ii' jj' k j'"
        proof (cases k)
          case 0
          {
            fix k'
            assume "0 < k' \<and> k' < Suc (length ts)"
            then obtain k'' where k': "k' = Suc k''" and len: "k'' < length ts" by (cases k', auto)
            from comp [THEN spec, THEN mp [OF _ len]] have cik: "class_to_term_intern iv (ii ! k'') (ts ! k'') = (jj ! k'', us ! k'')" 
              and ji': "jj ! k'' \<le> i'" by auto
            then have "jj ! (k' - Suc 0) \<le> i'" unfolding k' by simp
          }
          then show ?thesis unfolding us ii jj 0  by (auto simp: cjt)
        next
          case (Suc k)
          with k have k: "k < length ts" by auto
          from comp [THEN spec, THEN mp [OF _ k]] have cik: "class_to_term_intern iv (ii ! k) (ts ! k) = (jj ! k, us ! k)" 
            and ji': "jj ! k \<le> i'" by auto
          from class_to_term_intern_vars [OF cik] have ij: "ii ! k \<le> jj ! k" by simp
          from ji' i'j' have jjk: "jj ! k \<le> j'" by simp
          show ?thesis unfolding us ii jj Suc
          proof (intro conjI,
              simp add: cik,
              simp add: jjk,
              intro allI impI)
            fix k'
            assume ass: "Suc k < k' \<and> k' < length (t # ts)"
            then obtain k'' where k': "k' = Suc k''" and kk: "k < k'' \<and> k'' < length ts" by (cases k', auto)
            from comp [THEN spec, THEN mp [OF _ k], THEN conjunct2, THEN conjunct2, THEN spec, THEN mp [OF _ kk]] 
            show "(j' # jj) ! k' \<le> (i' # ii) ! Suc k" unfolding k' by simp
          qed
        qed
      qed
    qed
    from fold_prop have ct: "\<And> k. k < length ts \<Longrightarrow> ?P ts us ii jj k j" by auto
    from fold_prop have id: "snd (class_to_term_intern iv i (Fun f ts)) = (Fun f us)"
      by (simp add: Let_def)          
    {
      fix i j
      assume i: "i < length ts"
      then have mem: "ts ! i \<in> set ts" by auto
      from Fun(2) have "\<And> x. Inr x \<in> vars_term (ts ! i) \<Longrightarrow> x \<notin> range iv" using mem by auto
      from Fun(1) [OF mem this] have "?l (ts ! i) = ?r j (ts ! i)" by auto
    } note IH = this
    {
      fix s
      assume "s \<in> ?l (Fun f ts)"      
      then obtain ss where len: "length ss = length ts" and ss: "\<And> i. i < length ts \<Longrightarrow> ss ! i \<in> \<lbrace>ts ! i\<rbrace>_\<sigma>" and s: "s = Fun f ss" by auto
      {
        fix i j
        assume i: "i < length ts"
        from IH [OF this, of j]
          ss [OF i] have "ss ! i  \<in> ?r j (ts ! i)" by auto
      } note ss = this
      from fold_prop len have len2: "length ss = length us" by auto
      {
        fix k
        assume k: "k < length ts"
        from ct [OF k] ss [OF k, of "ii ! k"]
        have "\<exists> \<tau>. ss ! k = us ! k \<cdot> \<tau> \<and> ?valid \<tau>"
          by auto
      } note arg = this
      from arg have "\<forall> i. \<exists> \<tau>. i < length ts \<longrightarrow> ss ! i = us ! i \<cdot> \<tau> \<and> ?valid \<tau>" by auto
      from choice [OF this] obtain \<tau>i where arg: "\<And> i. i < length ts \<Longrightarrow> ss ! i = us ! i \<cdot> \<tau>i i \<and> ?valid (\<tau>i i)" by auto
      let ?choice = "\<lambda> x. (THE i. i < length ts \<and> x \<in> vars_term (us ! i))"
      let ?\<tau> = "\<lambda> x. if x \<in> range iv then \<tau>i (?choice x) x else \<sigma> x"
      have "s \<in> ?r i (Fun f ts)" unfolding s id
      proof (simp, rule exI, rule conjI, rule sym, unfold map_nth_eq_conv [OF len2 [symmetric]], clarify)
        fix i
        assume "i < length ss"
        with len len2 have i: "i < length ts" by auto
        have "ss ! i = us ! i \<cdot> ?\<tau>" unfolding arg [OF i, THEN conjunct1]
        proof (rule term_subst_eq)
          fix x
          assume x: "x \<in> vars_term (us ! i)"
          from arg [OF i] have "x \<in> range iv \<or> \<tau>i i x = \<sigma> x" by auto
          then have "x \<in> range iv \<or> x \<notin> range iv \<and> \<tau>i i x = \<sigma> x" by auto
          then show "\<tau>i i x = ?\<tau> x"
          proof
            assume x': "x \<in> range iv"
            {
              fix j
              assume j: "j < length ts"
              from Fun(2) [of x] x' have "Inr x \<notin> vars_term (Fun f ts)" by auto
              with j have "Inr x \<notin> vars_term (ts ! j)" by (auto simp: set_conv_nth)
            } note Inr = this
            {
              fix k
              assume k: "k < length ts" and x: "x \<in> vars_term (us ! k)"
              from x class_to_term_intern_vars [OF ct [OF k, THEN conjunct1], THEN conjunct2] Inr [OF k]
              have "x \<in> {iv j | j. ii ! k \<le> j \<and> j < jj ! k}" by auto
              then have "\<exists> j. x = iv j \<and> ii ! k \<le> j \<and> j < jj ! k" by auto
            } note index = this
            have "?choice x = i"
            proof
              show "i < length ts \<and> x \<in> vars_term (us ! i)" using x i by simp
            next
              fix j
              assume both: "j < length ts \<and> x \<in> vars_term (us ! j)"              
              then have j: "j < length ts" and xj: "x \<in> vars_term (us ! j)" by auto
              from index [OF i x] obtain ki where xki: "x = iv ki \<and> ii ! i \<le> ki \<and> ki < jj ! i" by auto
              from index [OF j xj] obtain kj where xkj: "x = iv kj \<and> ii ! j \<le> kj \<and> kj < jj ! j" by auto
              from xki xkj have "iv ki = iv kj" by simp
              from arg_cong [OF this, of "the_inv iv"] the_inv_f_f [OF inj] have kij: "ki = kj" by simp
              from xki have iy: "ii ! i \<le> ki" and yi: "ki < jj ! i" by auto
              from xkj have jy: "ii ! j \<le> ki" and yj: "ki < jj ! j" unfolding kij by auto
              from iy yj have ij: "ii ! i < jj ! j" by auto
              from jy yi have ji: "ii ! j < jj ! i" by auto
              {
                fix i j
                assume i: "i < length ts" and j: "j < length ts" and gt: "ii ! i < jj ! j"
                have "j \<le> i"
                proof (rule ccontr)
                  assume "\<not> j \<le> i"
                  then have "i < j" by auto
                  with ct [OF i, THEN conjunct2, THEN conjunct2, THEN spec [of _ j]]
                    j have "jj ! j \<le> ii ! i" by auto
                  with gt show False by auto
                qed
              } note increasing = this
              from increasing [OF i j ij] increasing [OF j i ji]
              show "j = i" by auto
            qed
            with x' show ?thesis by simp
          qed simp
        qed
        then show "us ! i \<cdot> ?\<tau> = ss ! i" by simp
      qed auto
    }
    moreover
    {
      fix s
      assume "s \<in> ?r i (Fun f ts)"
      with fold_prop [THEN conjunct2, THEN conjunct1]      
      obtain \<tau> where valid: "?valid \<tau>" and s: "s = Fun f (map (\<lambda> t. t \<cdot> \<tau>) us)" (is "_ = Fun f (map ?sig us)") by auto
      from fold_prop have len: "length ts = length us" by auto
      let ?P = "\<lambda> i tsi. ?sig (us ! i) = tsi \<and> tsi \<in> \<lbrace>ts ! i\<rbrace>_\<sigma>"
      {
        fix i
        assume i: "i < length ts"
        then have mem: "ts ! i \<in> set ts" by auto
        with ct [OF i] have us: "us ! i = snd (class_to_term_intern iv (ii ! i) (ts ! i))" by auto
        from IH [OF i, of "ii ! i"]
        have "?sig (us ! i) \<in> \<lbrace>ts ! i\<rbrace>_\<sigma>" unfolding us using valid by auto
        then have "\<exists> tsi. ?P i tsi" by auto
      } 
      then have "\<forall> i. \<exists> tsi. i < length ts \<longrightarrow> ?P i tsi" by auto
      from choice [OF this] obtain ss where ss: "\<And> i. i < length ts \<Longrightarrow> ?P i (ss i)" by auto      
      let ?ss = "map ss [0 ..< length ts]"
      have "s \<in> ?l (Fun f ts)" unfolding s using ss by (simp add: len ss)
    }
    ultimately show ?case by blast
  qed
qed

definition class_to_term :: "char \<Rightarrow> ('f, unit + string) term \<Rightarrow> ('f, string)term" where
  "class_to_term c t = snd (class_to_term_intern (\<lambda> i. Cons c (show (i :: nat))) 0 t)"

lemma class_to_term:
  assumes range: "\<And> x. Inr x \<in> vars_term t \<Longrightarrow> x \<notin> range (Cons c)"
  shows "\<lbrace>t\<rbrace>_\<sigma> = {class_to_term c t \<cdot> \<tau>| \<tau>. (\<forall> x. x \<in> range (\<lambda> i. Cons c (show (i :: nat))) \<or> \<sigma> x = \<tau> x)}" 
  unfolding class_to_term_def 
proof (rule class_to_term_intern)
  show "inj (\<lambda> i. c # show (i :: nat))" using inj_show_nat unfolding inj_on_def by auto
qed (insert range, auto)

lemma vars_term_class_to_term: "vars_term (class_to_term c t) \<subseteq> range (Cons c) \<union> {x. Inr x \<in> vars_term t}" 
proof -
  obtain s j where id: "class_to_term_intern (\<lambda> i. Cons c (show (i :: nat))) 0 t = (j, s)"
    by force
  from class_to_term_intern_vars [OF id] show ?thesis unfolding class_to_term_def id
    by auto
qed

definition
  mgu_class ::
    "('f, unit + string) term \<Rightarrow> ('f, string) term \<Rightarrow> (('f, string) subst) option"
where
  "mgu_class cs t = mgu (class_to_term (CHR ''z'') cs) (map_vars_term y_var t)"

lemma mgu_class_complete:
  fixes cs :: "('f, unit + string) term" and \<sigma> :: "('f, string) subst"
  assumes mem: "t \<cdot> \<tau> \<in> \<lbrace>cs\<rbrace>_\<sigma>"
  and range: "\<And> x. Inr x \<in> vars_term cs \<Longrightarrow> x \<in> range x_var"
  shows "\<exists> \<mu> \<delta>. mgu_class cs t = Some \<mu> \<and> (\<forall> x \<in> range x_var. \<sigma> x = \<mu> x \<cdot> \<delta>) 
  \<and> (\<forall> t. t \<cdot> \<tau> = map_vars_term y_var t \<cdot> \<mu> \<cdot> \<delta>)"
proof -
  let ?cs = "class_to_term (CHR ''z'') cs"
  let ?valid = "\<lambda> \<tau>. (\<forall> x. x \<in> range (\<lambda> i. z_var (show (i :: nat))) \<or> \<sigma> x = \<tau> x)"
  from mem have "t \<cdot> \<tau> \<in> {?cs \<cdot> \<tau>| \<tau>. ?valid \<tau>}"
    using class_to_term [of cs "CHR ''z''" \<sigma>] range by force
  then obtain \<tau>' where id: "?cs \<cdot> \<tau>' = t \<cdot> \<tau>" and \<tau>': "?valid \<tau>'" by force
  from range vars_term_class_to_term [of "CHR ''z''" cs] have subset: "vars_term ?cs \<subseteq> range x_var \<union> range z_var" by auto
  from mgu_var_disjoint_right_string [OF subset id]
  obtain \<mu> \<delta> where
  mgu: "mgu_class cs t = Some \<mu>"
    and idt: "\<And> t. t \<cdot> \<tau> = map_vars_term y_var t \<cdot> \<mu> \<cdot> \<delta>"
    and \<tau>'1: "\<And> x. x \<in> range x_var \<union> range z_var \<Longrightarrow> \<tau>' x = \<mu> x \<cdot> \<delta>"
    unfolding mgu_class_def by blast
  {
    fix x
    assume x: "x \<in> range x_var"
    with \<tau>' [rule_format, of x] have "\<sigma> x = \<tau>' x" by auto
    also have "... = \<mu> x \<cdot> \<delta>" by (rule \<tau>'1, insert x, auto)
    finally have "\<sigma> x = \<mu> x \<cdot> \<delta>" .
  } note \<sigma> = this
  show ?thesis
    by (intro exI conjI, rule mgu, rule ballI [OF \<sigma>], insert idt, auto)
qed

fun icap :: "('f, string) cap_fun" where
  "icap R Q S (Var x) =
    Var (if NF_terms Q \<subseteq> NF_trs R \<and> (\<exists>t \<in> S. x \<in> vars_term t) then Inr x else Inl ())"
| "icap R Q S (Fun f ts) = (
    let t' = Fun f (map (icap R Q S) ts) in
    if (\<exists> lr \<in>R. \<exists> \<mu>. mgu_class t' (fst lr) = Some \<mu> \<and> 
         (\<forall>u\<in>set (args (fst lr)). map_vars_term y_var u \<cdot> \<mu> \<in> NF_terms Q) \<and>
         (\<forall>u\<in>S. u \<cdot> \<mu> \<in> NF_terms Q))
      then Var (Inl ())
      else t')"

definition icap' :: "('f, string) cap_fun" where
  "icap' R Q S t =
    (if vars_term t \<union> \<Union>(vars_term ` S) \<subseteq> range x_var then icap R Q S t
    else Var (Inl ()))"

lemma vars_term_icap: "vars_term (icap R Q S t) \<subseteq> Inr ` vars_term t \<union> {Inl ()}"
  by (induct t, auto simp: Let_def)

lemma icap:
  "is_ecap (icap' :: ('f, string) cap_fun)"
proof (rule, intro conjI)
  fix R :: "('f, string) trs" and Q S f ts
  show "icap' R Q S (Fun f ts) \<in> {Var (Inl ()), Fun f (map (icap' R Q S) ts)}"
    by (auto simp: Let_def icap'_def)
next
  fix R :: "('f, string) trs" and Q S x 
  show "icap' R Q S (Var x) \<in> {Var (Inl ()), Var (Inr x)}" by (auto simp: icap'_def)
next
  fix R :: "('f, string) trs" and Q S :: "('f, string) terms" and t :: "('f, string) term"
  {
    fix \<tau> :: "('f, string) subst" and t :: "('f, string) term"
    assume Sx: "\<Union>(vars_term ` S) \<subseteq> range x_var"
      and t: "vars_term t \<subseteq> range x_var"
    from t have "\<lbrace>cap R Q S t\<rbrace>_\<tau> \<subseteq> \<lbrace>icap R Q S t\<rbrace>_\<tau>"
    proof (induct t arbitrary: \<tau>)
      case (Var x)
      show ?case 
      proof (cases "\<exists>\<sigma> nfs. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q \<and> Var x \<cdot> \<sigma> \<notin> NF (qrstep nfs Q R)")
        case True
        then obtain \<sigma> nfs where subset: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_trs (Id_on Q)" and notNF: "Var x \<cdot> \<sigma> \<notin> NF (qrstep nfs Q R)" by auto
        show ?thesis 
        proof (cases "NF_trs (Id_on Q) \<subseteq> NF_trs R \<and> (\<exists>t \<in> S. x \<in> vars_term t)")
          case True
          then obtain t where t: "t \<in> S" and x: "x \<in> vars_term t" and subset2: "NF_trs (Id_on Q) \<subseteq> NF_trs R" by auto
          from t subset subset2 have NF: "t \<cdot> \<sigma> \<in> NF_trs R" by blast
          from x have "Var x \<unlhd> t" by auto
          then have "Var x \<cdot> \<sigma> \<unlhd> t \<cdot> \<sigma>" by auto
          from NF_subterm [OF NF this] have "Var x \<cdot> \<sigma> \<in> NF_trs R" by simp
          with notNF have False unfolding NF_def using qrstep_subset_rstep [of nfs Q R] by force
          then show ?thesis by auto
        qed auto
      qed auto
    next
      case (Fun f ss)
      let ?Pm = "\<lambda> t. t \<in> NF_terms Q"
      let ?Pl = "\<lambda> r \<mu>. (\<forall> u \<in> set (args (fst r)). ?Pm (map_vars_term y_var u \<cdot> \<mu>))"
      let ?Pr = "\<lambda> \<mu>. (\<forall> u \<in> S. ?Pm  (u \<cdot> \<mu>))"
      let ?ss = "map (icap R Q S) ss"
      show ?case
      proof (cases "\<exists> r \<in> R. \<exists> \<mu>. mgu_class (Fun f ?ss) (fst r) = Some \<mu> \<and>  (?Pl r \<mu>) \<and> (?Pr \<mu>)") 
        case False 
        then have icap: "icap R Q S (Fun f ss) = Fun f ?ss" by (auto simp: Let_def)
        {
          fix \<tau> :: "('f, string)subst"
          from Fun(1) [of _ \<tau>, OF _ subset_trans [OF _ Fun(2)]]
          have "\<And> s. s \<in> set ss \<Longrightarrow> \<lbrace>cap R Q S s\<rbrace>_\<tau> \<subseteq> \<lbrace>icap R Q S s\<rbrace>_\<tau>" by auto
        } note ind_arg = this
        {
          fix \<tau> :: "('f, string)subst"
          from ind_arg [of _ \<tau>] have  "\<lbrace>Fun f (map (cap R Q S) ss)\<rbrace>_\<tau> \<subseteq> \<lbrace>Fun f ?ss\<rbrace>_\<tau>" 
            unfolding set_conv_nth by auto
        } note ind = this
        show ?thesis       
        proof (cases "\<exists> \<sigma> nfs. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_trs (Id_on Q) \<and> (\<exists> u. (Fun f ss \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>* O rqrstep nfs Q R)")
          case False
          then have cap: "cap R Q S (Fun f ss) = Fun f (map (cap R Q S) ss)" by auto
          show ?thesis unfolding cap icap by (rule ind)
        next
          case True
          then obtain \<sigma> nfs u where S: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_trs (Id_on Q)" and steps: "(Fun f ss \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>* O rqrstep nfs Q R" by auto
          from first_step_O [OF _ steps, unfolded qrstep_iff_rqrstep_or_nrqrstep, of "nrqrstep nfs Q R"]
          obtain u where "(Fun f ss \<cdot> \<sigma>, u) \<in> (nrqrstep nfs Q R)\<^sup>* O rqrstep nfs Q R" 
            by auto
          then obtain v where steps: "(Fun f (map (\<lambda> s. s \<cdot> \<sigma>) ss), v) \<in> (nrqrstep nfs Q R)\<^sup>*" and step: "(v, u) \<in> rqrstep nfs Q R" by auto
          from nrqrsteps_preserve_root [OF steps]
            obtain ts where v: "v = Fun f ts" and len: "length ts = length ss" by (cases v) auto
          {
            fix i
            assume i: "i < length ss"
            then have si: "ss ! i \<in> set ss" by auto
            from nrqrsteps_imp_arg_qrsteps [OF steps, unfolded v, of i]
            have "(ss ! i \<cdot> \<sigma>, ts ! i) \<in> (qrstep nfs Q R)\<^sup>*" using len i by auto
            from ecap_steps [OF is_ecap_cap this S] have "ts ! i \<in> \<lbrace>cap R Q S (ss ! i)\<rbrace>_\<sigma>" by auto
            with ind_arg [OF si, of \<sigma>]
            have "ts ! i \<in> \<lbrace>icap R Q S (ss ! i)\<rbrace>_\<sigma>" by auto
          } note icap_arg = this
          have in_icap: "v \<in> \<lbrace>Fun f ?ss\<rbrace>_\<sigma>" unfolding v 
            by (simp add: len icap_arg)
          from step [unfolded rqrstep_def] obtain l r \<tau> where v: "v = l \<cdot> \<tau>" and lr: "(l, r) \<in> R" 
            and NF: "\<And> u. u \<lhd> l \<cdot> \<tau> \<Longrightarrow> u \<in> NF_terms Q" by auto
          from False lr have nmgu: "\<not> (\<exists> \<mu>. mgu_class (Fun f ?ss) l = Some \<mu> \<and> (?Pl (l, r) \<mu>) \<and> (?Pr \<mu>))" by auto
          {
            fix x
            assume "Inr x \<in> vars_term (Fun f ?ss)"
            then obtain s where s: "s \<in> set ss" and x: "Inr x \<in> vars_term (icap R Q S s)" by auto
            from x vars_term_icap [of R Q S s] have "x \<in> vars_term s" by auto
            with s Fun(2) have "x \<in> range x_var" by auto
          } note range = this
          from mgu_class_complete [OF in_icap [unfolded v] range]
          obtain \<mu> \<delta> where mgu: "mgu_class (Fun f ?ss) l = Some \<mu>" and \<sigma>: "\<And> x. x \<in> range x_var \<Longrightarrow> \<sigma> x = \<mu> x \<cdot> \<delta>" and \<tau>: "\<And> t. t \<cdot> \<tau> = map_vars_term y_var t \<cdot> \<mu> \<cdot> \<delta>" by blast
          have Pr: "?Pr \<mu>"
          proof
            fix u
            assume u: "u \<in> S"
            with S have NF: "u \<cdot> \<sigma> \<in> NF_terms Q" by auto
            have "u \<cdot> \<sigma> = u \<cdot> (\<mu> \<circ>\<^sub>s \<delta>)"
            proof (rule term_subst_eq)
              fix x
              assume x: "x \<in> vars_term u"
              show "\<sigma> x = (\<mu> \<circ>\<^sub>s \<delta>) x" unfolding subst_compose_def
                by (rule \<sigma>, insert x Sx u, auto)
            qed
            with NF have "u \<cdot> \<mu> \<cdot> \<delta> \<in> NF_terms Q" by simp
            from NF_instance [OF this] show "u \<cdot> \<mu> \<in> NF_terms Q" .
          qed
          have Pl: "?Pl (l, r) \<mu>" unfolding fst_conv
          proof
            fix u
            assume u: "u \<in> set (args l)"
            from u obtain f ls where "l = Fun f ls" and "u \<in> set ls" by (cases l, auto)
            then have "u \<cdot> \<tau> \<lhd> l \<cdot> \<tau>" by auto
            from NF [OF this] have NF: "u \<cdot> \<tau> \<in> NF_terms Q" .
            show "map_vars_term y_var u \<cdot> \<mu> \<in> NF_terms Q"
              using NF [unfolded \<tau>]
              by (rule NF_instance)
          qed
          from nmgu mgu Pl Pr have False by auto
          then show ?thesis ..
        qed
      qed (auto simp: Let_def)
    qed
  }
  then show "\<lbrace>cap R Q S t\<rbrace> \<subseteq> \<lbrace>icap' R Q S t\<rbrace>" by (auto simp: icap'_def)
qed       

abbreviation "mv_xvar \<equiv> map_vars_term x_var"
abbreviation "mv_yvar \<equiv> map_vars_term y_var"
abbreviation "mv_subst \<equiv> \<lambda>\<sigma>. \<sigma> \<circ> tl"

lemma mv_xvar: "s \<cdot> \<sigma> = mv_xvar s \<cdot> mv_subst \<sigma>" 
  unfolding apply_subst_map_vars_term by (simp add: o_def)

lemma mv_yvar: "s \<cdot> \<sigma> = mv_yvar s \<cdot> mv_subst \<sigma>" 
  unfolding apply_subst_map_vars_term by (simp add: o_def)

lemma ecap_steps_mgu:
  fixes u s :: "('f, string) term" and \<sigma> \<tau> :: "('f, string) subst"
  assumes ecap: "is_ecap ecap"
    and SNF: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
    and steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "\<exists>\<mu>1 \<mu>2.
     mgu_class (ecap R Q (mv_xvar ` S) (mv_xvar t)) u = Some \<mu>1 \<and>
     (\<forall>s. s \<cdot> \<sigma> = mv_xvar s \<cdot> \<mu>1 \<cdot> \<mu>2 \<and> s \<cdot> \<tau> = mv_yvar s \<cdot> \<mu>1 \<cdot> \<mu>2)"
proof -
  let ?S = "mv_xvar ` S"
  let ?\<sigma> = "mv_subst \<sigma>"
  let ?t = "mv_xvar t"
  from SNF have "?S \<cdot>\<^sub>s\<^sub>e\<^sub>t ?\<sigma> \<subseteq> NF_terms Q" using mv_xvar [of _ \<sigma>] by auto
  from ecap_steps [OF ecap steps [unfolded mv_xvar [of _ \<sigma>]] this]
  have inst: "u \<cdot> \<tau> \<in> fresh_instances_subst (ecap R Q ?S ?t) ?\<sigma>" .
  {
    fix x
    assume x: "Inr x \<in> vars_term (ecap R Q ?S ?t)"
    from x vars_term_ecap [OF ecap, of R Q ?S ?t]
    have "x \<in> range x_var" unfolding term.set_map by auto
  }
  from mgu_class_complete [OF inst this]
  obtain \<mu> \<delta> where mgu: "mgu_class (ecap R Q ?S ?t) u = Some \<mu>"
    and \<sigma>: "\<And> x. x \<in> range x_var \<Longrightarrow> ?\<sigma> x = \<mu> x \<cdot> \<delta>"
    and \<tau>: "\<And> t. t \<cdot> \<tau> = mv_yvar t \<cdot> \<mu> \<cdot> \<delta>" by blast
  {
    fix s
    have "s \<cdot> \<sigma> = mv_xvar s \<cdot> (\<mu> \<circ>\<^sub>s \<delta>)"
      unfolding mv_xvar [of _ \<sigma>]
      by (rule term_subst_eq, unfold subst_compose_def, rule \<sigma>,
        unfold term.set_map, auto)
    also have "... = mv_xvar s \<cdot> \<mu> \<cdot> \<delta>" by simp
    finally have "s \<cdot> \<sigma> = mv_xvar s \<cdot> \<mu> \<cdot> \<delta>" .
  } note \<sigma> = this
  show ?thesis
    by (intro exI conjI, rule mgu, unfold \<sigma> \<tau>, auto)
qed

lemma ecap_steps_mgu_below_root:
  fixes u s :: "('f, string) term" and \<sigma> \<tau> :: "('f, string) subst"
  assumes ecap: "is_ecap ecap"
  and SNF: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
  and steps: "(Fun f ts \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (nrqrstep nfs Q R)^*"
  shows "\<exists>\<mu>1 \<mu>2.
     mgu_class (Fun f (map (\<lambda> t. ecap R Q (mv_xvar ` S) (mv_xvar t)) ts)) u = Some \<mu>1 \<and>
     (\<forall>s. s \<cdot> \<sigma> = mv_xvar s \<cdot> \<mu>1 \<cdot> \<mu>2 \<and> s \<cdot> \<tau> = mv_yvar s \<cdot> \<mu>1 \<cdot> \<mu>2)"
proof -
  let ?S = "mv_xvar ` S"
  let ?\<sigma> = "mv_subst \<sigma>"
  let ?et = "Fun f (map (\<lambda> t. ecap R Q ?S (mv_xvar t)) ts)"
  from SNF have S: "?S \<cdot>\<^sub>s\<^sub>e\<^sub>t ?\<sigma> \<subseteq> NF_terms Q" using mv_xvar [of _ \<sigma>] by auto
  from steps have steps: "(Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts), u \<cdot> \<tau>) \<in> (nrqrstep nfs Q R)^*" by auto
  from nrqrsteps_preserve_root_fun[OF steps] nrqrsteps_num_args[OF steps]
  obtain us where u: "u \<cdot> \<tau> = Fun f us" and len: "length ts = length us" using length_map by auto
  with nrqrsteps_imp_arg_qrsteps[OF steps]
  have isteps:"\<And>i. i < length ts \<Longrightarrow> (ts ! i \<cdot> \<sigma>, us ! i) \<in> (qrstep nfs Q R)^*" 
    using nth_map term.sel(4) by metis
  {
    fix i
    assume i: "i < length ts"
    from ecap_steps[OF ecap isteps[OF i, unfolded mv_xvar[of _ \<sigma>]] S]
    have "us ! i \<in> fresh_instances_subst (ecap R Q ?S (mv_xvar (ts ! i))) ?\<sigma>" .
  }
  then have inst: "u \<cdot> \<tau> \<in> fresh_instances_subst ?et ?\<sigma>" unfolding u using len by auto
  {
    fix x
    assume "Inr x \<in> vars_term ?et"
    then obtain t where "Inr x \<in> vars_term (ecap R Q ?S (mv_xvar t))" by auto
    with vars_term_ecap [OF ecap, of R Q ?S "mv_xvar t"]
    have "x \<in> range x_var" unfolding term.set_map by auto
  }
  from mgu_class_complete [OF inst this]
  obtain \<mu> \<delta> where mgu: "mgu_class ?et u = Some \<mu>"
    and \<sigma>: "\<And> x. x \<in> range x_var \<Longrightarrow> ?\<sigma> x = \<mu> x \<cdot> \<delta>"
    and \<tau>: "\<And> t. t \<cdot> \<tau> = mv_yvar t \<cdot> \<mu> \<cdot> \<delta>" by blast
  {
    fix s
    have "s \<cdot> \<sigma> = mv_xvar s \<cdot> (\<mu> \<circ>\<^sub>s \<delta>)"
      unfolding mv_xvar [of _ \<sigma>]
      by (rule term_subst_eq, unfold subst_compose_def, rule \<sigma>,
        unfold term.set_map, auto)
    also have "... = mv_xvar s \<cdot> \<mu> \<cdot> \<delta>" by simp
    finally have "s \<cdot> \<sigma> = mv_xvar s \<cdot> \<mu> \<cdot> \<delta>" .
  } note \<sigma> = this
  show ?thesis
    by (intro exI conjI, rule mgu, unfold \<sigma> \<tau>, auto)
qed

lemma icap': "icap' R Q (mv_xvar ` S) (mv_xvar t) = icap R Q (mv_xvar ` S) (mv_xvar t)"
  by (auto simp: term.set_map icap'_def)

definition icap_mv :: "('f, string) cap_fun" where
  "icap_mv R Q S t = icap R Q (mv_xvar ` S) (mv_xvar t)"

lemma icap_mv_mgu:
  assumes steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs Q R)\<^sup>*"
    and NF: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
  shows "\<exists> \<mu> \<delta>. mgu_class (icap_mv R Q S t) u = Some \<mu> \<and> 
     (\<forall> s. s \<cdot> \<sigma> = mv_xvar s \<cdot> \<mu> \<cdot> \<delta> \<and> s \<cdot> \<tau> = mv_yvar s \<cdot> \<mu> \<cdot> \<delta>)"
proof -
  from ecap_steps_mgu [OF icap NF steps]
  show ?thesis unfolding icap' icap_mv_def .
qed  

no_notation Icap.fresh_instances_subst ("\<lbrace>_\<rbrace>'__")
no_notation Icap.fresh_instances ("\<lbrace>_\<rbrace>")

end
