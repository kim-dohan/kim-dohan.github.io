(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Equational_Reasoning 
  imports
    First_Order_Rewriting.Trs
    First_Order_Terms.Option_Monad
begin

text \<open>
The following datatype represents proofs in equational logic
using the following rules:
\begin{itemize}
  \item reflexivity: $E \vdash t = t$
  \item symmetry: $E \vdash s = t$ implies $E \vdash t = s$
  \item transitivity: $E \vdash s = t$ and $E \vdash t = u$
    implies $E \vdash s = u$
  \item assumption: for every $(s, t) \in E$ and substitution
    $\sigma$, we have $E \vdash s\sigma = t\sigma$ (Note that this
    rules combines the instantiation and assumption rules that are
    for example found in \emph{Term Rewriting and All That}.)
  \item congruence: for every $n$-ary function symbol $f$ and
    $E \vdash s_1 = t_1$, \ldots, $E \vdash s_n = t_n$, we have
    $E \vdash f(s_1, \ldots, s_n) = f(t_1, \ldots, t_n)$
\end{itemize}
\<close>
datatype (dead 'f, 'v) eq_proof = 
  Refl "('f, 'v) term" 
| Sym "('f, 'v) eq_proof" 
| Trans "('f, 'v) eq_proof" "('f, 'v) eq_proof"
| Assm "('f, 'v) rule" "('f, 'v) subst"
| Cong 'f "('f, 'v) eq_proof list"


lemma
  fixes P :: "('f, 'v) eq_proof \<Rightarrow> bool"
  assumes "\<And>t. P (Refl t)" and "\<And>p. P p \<Longrightarrow> P (Sym p)"
  and "\<And>p1 p2. P p1 \<Longrightarrow> P p2 \<Longrightarrow> P (Trans p1 p2)"
  and "\<And>l r \<sigma>. P (Assm (l, r) \<sigma>)"
  and "\<And>f ps. (\<And>p. p \<in> set ps \<Longrightarrow> P p) \<Longrightarrow> P (Cong f ps)"
  shows eq_proof_induct[case_names Refl Sym Trans Assm Cong, induct type: eq_proof]:
    "P p" 
  by (induct p, insert assms, auto)

type_synonym ('f, 'v) equation = "('f, 'v) rule"

text \<open>
Given an equational system @{term E} and an equational logic proof @{term p},
@{term "proves E p"} obtains the equation which is proved, simultaneously checking
the correctness of @{term p}. If @{term p} is not correct the result is @{term None},
otherwise the result is the proved equation.
\<close>
fun
  proves :: "('f, 'v) trs \<Rightarrow> ('f, 'v) eq_proof \<Rightarrow> ('f, 'v) equation option"
where
  "proves E (Refl s) = Some (s, s)"
| "proves E (Sym p) = do {
    (s, t) \<leftarrow> proves E p;
    Some (t, s) }"
| "proves E (Trans p1 p2) = do {
    (s, t)  \<leftarrow> proves E p1;
    (t', u) \<leftarrow> proves E p2;
    guard (t = t');
    Some (s, u)
  }"
| "proves E (Assm (l, r) \<sigma>) = do {
    guard ((l, r) \<in> E);
    Some (l \<cdot> \<sigma>, r \<cdot> \<sigma>)
  }"
| "proves E (Cong f ps) = do {
    sts \<leftarrow> mapM (proves E) ps;
    Some (Fun f (map fst sts), Fun f (map snd sts))
  }"

text \<open>
The \emph{equational theory} of an equational system @{term E} is the set
of all provable equations.
\<close>
definition eq_theory :: "('f, 'v) trs \<Rightarrow> ('f, 'v) equation set" where
  "eq_theory E \<equiv> {e. \<exists>p. proves E p = Some e}"

lemma estep_sym_closure_conv: "(rstep E)\<^sup>\<leftrightarrow> = rstep (E\<^sup>\<leftrightarrow>)"
  by (simp add: rstep_simps)

lemma subst_closed_estep: "subst.closed ((rstep E)\<^sup>\<leftrightarrow>)"
  by blast

lemma ctxt_closed_estep [intro]: "ctxt.closed ((rstep E)\<^sup>\<leftrightarrow>)"
  unfolding rstep_union by blast

lemma sym_esteps_pair: "(s,t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> (t,s) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
  using conversion_sym[of "rstep E", unfolded sym_def] by blast

lemma all_ctxt_closed_esteps[intro]: "all_ctxt_closed F ((rstep E)\<^sup>\<leftrightarrow>\<^sup>*)"
  by (simp add: conversion_ctxt_closed conversion_trans trans_ctxt_sig_imp_all_ctxt_closed)

lemma ctxt_closed_eq_theory: "ctxt.closed (eq_theory E)"
proof (rule one_imp_ctxt_closed)
  fix f bef s t aft
  assume "(s,t) \<in> eq_theory E"
  from this[unfolded eq_theory_def] obtain p where p: "proves E p = Some (s,t)" by auto
  show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> eq_theory E" (is "?pair \<in> _")
    unfolding eq_theory_def
  proof(rule, rule exI)
    have id: "mapM (proves E) (map Refl bef @ p # map Refl aft) = (Some (map (\<lambda> b. (b,b)) bef @ (s,t) # map (\<lambda> a. (a,a)) aft))"
    proof (induct bef)
      case (Cons b bef)
      then show ?case by auto
    next
      case Nil
      have "mapM (proves E) (map Refl aft) = Some (map (\<lambda> a. (a,a)) aft)"
        by (induct aft, auto)
      then show ?case unfolding list.map append_Nil mapM.simps p by simp
    qed
    then show "proves E (Cong f (map (\<lambda> b. Refl b) bef @ p # map (\<lambda> a. Refl a) aft)) = Some ?pair" by (auto simp: o_def)
  qed
qed

text \<open>
For every sentence of the equational theory of @{term E},
the left-hand side can be transformed into the right-hand side by
applying equations from @{term E}.
\<close>
lemma eq_theory_is_esteps: "eq_theory E = (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" (is "?P = ?E")
proof -
  let ?p = "proves E"
  {
    fix s t
    assume "(s,t) \<in> eq_theory E"
    from this[unfolded eq_theory_def] obtain p where
      "proves E p = Some (s,t)" by auto
    then have "(s,t) \<in> ?E"
    proof (induct p arbitrary: s t)
      case (Sym p)
      from Sym(2) have p: "?p p = Some (t,s)" by (cases "?p p", auto)
      from Sym(1)[OF p] have ts: "(t,s) \<in> ?E" .
      from conversion_sym[of "rstep E"] ts
      show ?case unfolding sym_def by auto
    next
      case (Trans p1 p2)
      from Trans(3) obtain s1 t1 where p1: "?p p1 = Some (s1,t1)" by (cases "?p p1", auto)
      from Trans(3) obtain s2 t2 where p2: "?p p2 = Some (s2,t2)" using p1 by (cases "?p p2", auto)
      from Trans(3) have t1s2: "t1 = s2" using p1 p2 by (cases "t1 = s2", auto)
      from Trans(3) p1 p2 t1s2 have p1: "?p p1 = Some (s,t1)" and p2: "?p p2 = Some (t1,t)" by auto
      from Trans(1)[OF p1] Trans(2)[OF p2] show ?case by (metis conversion_def rtrancl_trans)
    next
      case (Assm l r \<sigma>)
      from Assm have mem: "(l,r) \<in> E" by (cases "(l,r) \<in> E", auto)
      from Assm mem have id: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" by auto
      have "(s,t) \<in> rstep E" unfolding id using mem by auto
      then show ?case by auto
    next
      case (Cong f ps)
      from Cong(2) obtain sts where sts: "mapM ?p ps = Some sts" by (cases "mapM ?p ps", auto)
      let ?ss = "map fst sts"
      let ?ts = "map snd sts"
      from Cong(2) sts
      have id: "s = Fun f ?ss" "t = Fun f ?ts" by auto
      note sts' = mapM_Some[OF sts]
      show ?case unfolding id
      proof (rule all_ctxt_closedD[of UNIV], unfold length_map)
        fix i
        assume i: "i < length sts"
        have psi: "ps ! i \<in> set ps" using sts sts' i by auto
        show "(?ss ! i, ?ts ! i) \<in> ?E" unfolding nth_map[OF i]
        proof (rule Cong(1)[OF psi])
          from sts' psi have "?p (ps ! i) \<noteq> None" by auto
          then show "?p (ps ! i) = Some (fst (sts ! i), snd (sts ! i))"
            using sts' i by (cases "?p (ps ! i)", auto)
        qed
      qed auto
    qed auto
  }
  then have "?P \<subseteq> ?E" by auto
  moreover
  {
    fix s t
    assume "(s,t) \<in> ?E"
    then have "(s,t) \<in> ?P" unfolding eq_theory_def conversion_def
    proof (induct)
      case base
      have "proves E (Refl s) = Some (s,s)" by simp
      then show ?case by blast
    next
      case (step t u)
      from step(3) obtain p where st: "?p p = Some (s,t)" by auto      
      obtain l r C \<sigma> where lr: "(l,r) \<in> E^<->" and t: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" and u: "u = C\<langle>r \<cdot> \<sigma>\<rangle>"
        by (rule rstepE [OF step(2) [unfolded estep_sym_closure_conv]]) auto
      from lr
      have "\<exists> p. ?p p = Some (l \<cdot> \<sigma>, r \<cdot> \<sigma>)"
      proof
        assume "(l,r) \<in> E"
        then have "?p (Assm (l,r) \<sigma>) = Some (l \<cdot> \<sigma>, r \<cdot> \<sigma>)" by simp
        then show ?thesis ..
      next
        assume "(l,r) \<in> E^-1"
        then have "(r,l) \<in> E" by simp
        then have "?p (Sym (Assm (r,l) \<sigma>)) = Some (l \<cdot> \<sigma>, r \<cdot> \<sigma>)" by simp
        then show ?thesis ..
      qed
      then have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ?P" unfolding eq_theory_def by auto
      from ctxt.closedD[OF ctxt_closed_eq_theory this, of C]
      obtain p2 where tu: "?p p2 = Some (t,u)" unfolding t u unfolding eq_theory_def by auto
      from st tu have "?p (Trans p p2) = Some (s,u)" by simp
      then show ?case by blast
    qed
  }
  then have "?E \<subseteq> ?P" by auto
  ultimately show ?thesis by auto
qed

type_synonym ('f, 'a) eq_inter = "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
type_synonym ('v, 'a) eq_assign = "'v \<Rightarrow> 'a"

definition eq_inter :: "'a set \<Rightarrow> ('f, 'a) eq_inter \<Rightarrow> bool" where
  "eq_inter U I \<equiv> \<forall>f as. set as \<subseteq> U \<longrightarrow> I f as \<in> U"

definition eq_assign :: "'a set \<Rightarrow> ('v, 'a) eq_assign \<Rightarrow> bool" where
  "eq_assign U \<alpha> \<equiv> range \<alpha> \<subseteq> U"

text \<open>
We evaluate terms w.r.t\ an interpretation @{term I} on function symbols
and an assignment @{term \<alpha>} on variables.
\<close>
fun
  eq_eval :: "('f, 'a) eq_inter \<Rightarrow> ('v, 'a) eq_assign \<Rightarrow> ('f, 'v) term \<Rightarrow> 'a"
where
  "eq_eval I \<alpha> (Var x) = \<alpha> x"
| "eq_eval I \<alpha> (Fun f ts) = I f (map (eq_eval I \<alpha>) ts)"

fun
  eq_model_eqn :: "'a set \<Rightarrow> ('f, 'a) eq_inter \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool"
where
  "eq_model_eqn U I (l, r) = (\<forall>\<alpha>. eq_assign U \<alpha> \<longrightarrow> eq_eval I \<alpha> l = eq_eval I \<alpha> r)"

text \<open>
The algebra given by the carrier @{term U} and where function symbols are interpreted
by @{term I} is a \emph{model} of an equational system @{term E} if all its equations
are satisfied for arbitrary assignments.
\<close>
definition models :: "'a set \<Rightarrow> ('f, 'a) eq_inter \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "models U I E \<equiv> (\<forall>e\<in>E. eq_model_eqn U I e)"

text \<open>
The equational system @{term E} \emph{entails} the equation @{term e}, if every
model of @{term E} is also a model of @{term e}.
\<close>
definition entails :: "'a itself \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "entails ty E e \<equiv> \<forall>U::'a set. \<forall>I. eq_inter U I \<longrightarrow> models U I E \<longrightarrow> eq_model_eqn U I e"

lemma eq_subst_lemma: "eq_eval I \<alpha> (t \<cdot> \<sigma>) = eq_eval I (\<lambda>x. eq_eval I \<alpha> (\<sigma> x)) t" 
proof (induct t)
  case (Var x) then show ?case by simp
next
  case (Fun f ts)
  have id: "map (\<lambda>x. eq_eval I \<alpha> (x \<cdot> \<sigma>)) ts =
    map (eq_eval I (\<lambda>x. eq_eval I \<alpha> (\<sigma> x))) ts"
    using Fun by (induct ts, auto)
  show ?case unfolding eq_eval.simps id[symmetric]
    by (simp add: o_def)
qed

lemma eq_inter_assign:
  assumes I: "eq_inter U I" and \<alpha>: "eq_assign U \<alpha>"
  shows "eq_eval I \<alpha> t \<in> U"
proof (induct t)
  case (Var x)
  show ?case using \<alpha>[unfolded eq_assign_def] by auto
next
  case (Fun f ts)
  then have "eq_eval I \<alpha> ` set ts \<subseteq> U"  by auto
  with I[unfolded eq_inter_def] show ?case by auto
qed

text \<open>
Every conversion is also 
a semantic consequence of @{term E}.
\<close>
lemma esteps_imp_entails: 
  fixes E :: "('f, 'v) trs" and ty :: "'a itself"
  assumes "(s, t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "entails ty E (s, t)"
proof -
  let ?p = "proves E"
  from assms[folded eq_theory_is_esteps, unfolded eq_theory_def]
    obtain p where eq: "?p p = Some (s,t)" by auto
  show ?thesis unfolding entails_def
  proof (intro impI allI)
    fix U :: "'a set" and I
    assume I: "models U I E" "eq_inter U I"
    let ?J = "eq_eval I"
    show "eq_model_eqn U I (s,t)"
      unfolding eq_model_eqn.simps
    proof (intro impI allI)
      fix \<alpha> :: "('v,'a)eq_assign"
      assume \<alpha>: "eq_assign U \<alpha>"
      from eq
      show "?J \<alpha> s = ?J \<alpha> t" (is "?I s = _")
      proof (induct p arbitrary: s t)
        case (Refl u s t)
        then show ?case by auto
      next
        case (Sym p)
        from Sym(2) have p: "?p p = Some (t,s)" by (cases "?p p", auto)
        from Sym(1)[OF p] show ?case by simp
      next
        case (Trans p1 p2)
        from Trans(3) obtain s1 t1 where p1: "?p p1 = Some (s1,t1)" by (cases "?p p1", auto)
        from Trans(3) obtain s2 t2 where p2: "?p p2 = Some (s2,t2)" using p1 by (cases "?p p2", auto)
        from Trans(3) have t1s2: "t1 = s2" using p1 p2 by (cases "t1 = s2", auto)
        from Trans(3) p1 p2 t1s2 have p1: "?p p1 = Some (s,t1)" and p2: "?p p2 = Some (t1,t)" by auto
        from Trans(1)[OF p1] Trans(2)[OF p2] show ?case by auto
      next
        case (Assm l r \<sigma>)
        from Assm have mem: "(l,r) \<in> E" by (cases "(l,r) \<in> E", auto)
        from Assm mem have id: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" by auto
        from I[unfolded models_def] mem have "eq_model_eqn U I (l,r)" by auto
        from this[unfolded eq_model_eqn.simps] have lr: "\<And> \<alpha>. eq_assign U \<alpha> \<Longrightarrow> ?J \<alpha> l = ?J \<alpha> r" by simp
        show ?case unfolding id eq_subst_lemma 
        proof (rule lr, unfold eq_assign_def, rule)
          fix a
          assume "a \<in> range (\<lambda> x. ?I (\<sigma> x))"
          then obtain t where a: "a = ?I t" by auto
          show "a \<in> U" unfolding a
            by (rule eq_inter_assign[OF I(2) \<alpha>])
        qed
      next
        case (Cong f ps)
        from Cong(2) obtain sts where sts: "mapM ?p ps = Some sts" by (cases "mapM ?p ps", auto)
        let ?ss = "map fst sts"
        let ?ts = "map snd sts"
        from Cong(2) sts
        have id: "s = Fun f ?ss" "t = Fun f ?ts" by auto
        note sts' = mapM_Some[OF sts]
        show ?case unfolding id eq_eval.simps
        proof (rule arg_cong[where f = "I f"], rule nth_map_conv, simp, 
            unfold length_map, intro allI impI)
          fix i
          assume i: "i < length sts"
          have psi: "ps ! i \<in> set ps" using sts sts' i by auto
          show "?I (?ss ! i) = ?I (?ts ! i)" unfolding nth_map[OF i]
          proof (rule Cong(1)[OF psi])
            from sts' psi have "?p (ps ! i) \<noteq> None" by auto
            then show "?p (ps ! i) = Some (fst (sts ! i), snd (sts ! i))"
              using sts' i by (cases "?p (ps ! i)", auto)
          qed
        qed
      qed
    qed
  qed
qed

text \<open>
Every equation that is semantic consequence of @{term E} is
yields a converion w.r.t. @{term E}.
\<close>
lemma entails_imp_esteps: 
  fixes E :: "('f, 'v) trs" and ty :: "('f,'v)terms itself"
  assumes entails: "entails ty E (s, t)"
  shows "(s, t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  let ?E = "(rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
  obtain cl where cl: "cl \<equiv> \<lambda> t. {s. (t,s) \<in> ?E}" by auto
  {
    fix s t 
    have "((s,t) \<in> ?E) = (cl s = cl t)"
    proof
      assume st: "(s,t) \<in> ?E"
      from st sym_esteps_pair[OF st]
      show "cl s = cl t" unfolding cl conversion_def by auto
    next
      assume "cl s = cl t"
      then show "(s,t) \<in> ?E"
        unfolding cl by auto
    qed
  } note esteps_iff_cl = this
  note cl_iff_esteps = esteps_iff_cl[symmetric]
  let ?U = "range cl"
  obtain cl' where cl': "cl' \<equiv> \<lambda> eqc. SOME (t :: ('f,'v)term). t \<in> eqc" by auto 
  obtain a_to_s where a_to_s: "a_to_s \<equiv> \<lambda> \<alpha> :: ('v,('f,'v)terms)eq_assign. \<lambda> x. cl' (\<alpha> x)" by auto   
  obtain I where I: "I \<equiv> \<lambda> f eqs. cl (Fun f (map cl' eqs))" by auto
  let ?I = "eq_eval I"
  have I_inter: "eq_inter ?U I"
    unfolding eq_inter_def cl I by auto
  note entails = entails[unfolded entails_def, rule_format, OF I_inter]
  {
    fix t
    let ?P = "\<lambda> s. (t,s) \<in> ?E"
    let ?s = "SOME s. ?P s"
    have id: "cl' (cl t) = ?s" unfolding cl' cl by auto
    have "cl (cl' (cl t)) = cl t" 
      unfolding id cl_iff_esteps
      by (rule sym_esteps_pair, rule someI[of ?P t], simp)
  } note cl_cl' = this
  {
    fix s and \<alpha> :: "('v,('f,'v)terms)eq_assign"
    assume \<alpha>: "eq_assign ?U \<alpha>"
    have "?I \<alpha> s = cl (s \<cdot> a_to_s \<alpha>)"
    proof (induct s)
      case (Var x)
      from \<alpha>[unfolded eq_assign_def] obtain t where \<alpha>x: "\<alpha> x = cl t" by auto
      show ?case unfolding a_to_s eq_eval.simps eval_term.simps
        unfolding \<alpha>x cl_cl' by simp
    next
      case (Fun f ss)
      from I have id: "I f = (\<lambda> eqs. cl (Fun f (map cl' eqs)))" by auto
      show ?case unfolding eq_eval.simps eval_term.simps id map_map o_def
        unfolding cl_iff_esteps
      proof (rule all_ctxt_closedD[of UNIV], unfold length_map)
        fix i
        assume i: "i < length ss"
        from Fun[unfolded set_conv_nth, of "ss ! i"] i have id: "?I \<alpha> (ss ! i) = 
          cl (ss ! i \<cdot> a_to_s \<alpha>)" by auto
        show "(map (\<lambda> x. cl' (?I \<alpha> x)) ss ! i, map (\<lambda> t. t \<cdot> a_to_s \<alpha>) ss ! i) \<in> ?E"
          unfolding nth_map[OF i]
          unfolding esteps_iff_cl 
          unfolding id cl_cl' ..
      qed auto
    qed
  } note eq_eval_id = this
  have model: "models ?U I E"
    unfolding models_def 
  proof(rule, clarify)
    fix s t
    assume st: "(s,t) \<in> E"
    show "eq_model_eqn ?U I (s,t)" unfolding eq_model_eqn.simps
    proof (intro allI impI)
      fix \<alpha> :: "('v,('f,'v)terms)eq_assign"
      assume \<alpha>: "eq_assign ?U \<alpha>"
      from st have "(s \<cdot> a_to_s \<alpha>, t \<cdot> a_to_s \<alpha>) \<in> rstep (E\<^sup>\<leftrightarrow>)"
        "(t \<cdot> a_to_s \<alpha>, s \<cdot> a_to_s \<alpha>) \<in> rstep (E\<^sup>\<leftrightarrow>)"
        by auto
      then show "eq_eval I \<alpha> s = eq_eval I \<alpha> t"
        unfolding eq_eval_id[OF \<alpha>]
        unfolding cl conversion_def estep_sym_closure_conv by auto
    qed
  qed
  note entails = entails[OF model, unfolded eq_model_eqn.simps, rule_format]
  obtain \<alpha> where \<alpha>: "\<alpha> \<equiv> \<lambda> x. cl (Var x)" by simp
  have \<alpha>_inter: "eq_assign ?U \<alpha>" unfolding eq_assign_def \<alpha> by auto
  note entails = entails[OF this]
  {
    fix s
    have "cl(s \<cdot> a_to_s \<alpha>) = cl s"
    proof (induct s)
      case (Var x)
      show ?case unfolding a_to_s \<alpha> 
        by (simp add: cl_cl')
    next
      case (Fun f ss)
      show ?case unfolding eval_term.simps
        unfolding cl_iff_esteps
      proof (rule all_ctxt_closedD[of UNIV], unfold length_map)
        fix i
        assume i: "i < length ss"
        have "map (\<lambda> t. t \<cdot> a_to_s \<alpha>) ss ! i = ss ! i \<cdot> a_to_s \<alpha>" using i by simp
        also have "(ss ! i \<cdot> a_to_s \<alpha>, ss ! i) \<in> ?E" using Fun[unfolded set_conv_nth cl_iff_esteps, of "ss ! i"] i by auto
        finally show "(map (\<lambda> t. t \<cdot> a_to_s \<alpha>) ss ! i, ss ! i) \<in> ?E" .
      qed auto
    qed
  } note a_to_s = this
  from entails have "?I \<alpha> s = ?I \<alpha> t" .
  from this[unfolded eq_eval_id[OF \<alpha>_inter] a_to_s]  
  show ?thesis unfolding esteps_iff_cl .
qed

text \<open>
Syntactic consequence (convertability) and
semantic consequence (entailment) coincide.
\<close>
lemma birkhoff:
  fixes E :: "('f, 'v) trs" and ty :: "('f, 'v) terms itself" 
  shows "entails ty E (s, t) \<longleftrightarrow> (s, t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
  using esteps_imp_entails[of s t E ty]
    and entails_imp_esteps[of ty E s t] by auto

text \<open>
Two equational systems are \emph{equivalent} if they prove
same equations, i.e., have the same conversions 
\<close>
definition equivalent :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "equivalent E E' \<equiv> (rstep E)\<^sup>\<leftrightarrow>\<^sup>* = (rstep E')\<^sup>\<leftrightarrow>\<^sup>*"

text \<open>
The equational system @{term E} \emph{subsumes} the equational system
@{term E'} when all equations that are provable using @{term E'} are
also provable using @{term E}.
\<close>
definition subsumes :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "subsumes E E' \<equiv> (rstep E')\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"

lemma equivalent_subsumes:
  "equivalent E E' \<longleftrightarrow> subsumes E E' \<and> subsumes E' E"
  unfolding subsumes_def equivalent_def by auto

lemma subsumes_via_rule_conversion:
  "subsumes E E' = (\<forall>(s, t)\<in>E'. (s, t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*)"
proof
  assume subs: "subsumes E E'"
  show "\<forall> (s,t) \<in> E'. (s,t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
  proof(clarify)
    fix s t
    assume "(s,t) \<in> E'"
    then have "(s,t) \<in> (rstep E')\<^sup>\<leftrightarrow>\<^sup>*" by auto
    with subs show "(s,t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" unfolding subsumes_def by auto
  qed
next
  assume "\<forall>(s, t)\<in>E'. (s,t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
  then have steps: "\<And>s t. (s, t) \<in> E' \<Longrightarrow> (s, t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" by auto
  show "subsumes E E'"
    unfolding subsumes_def
  proof
    fix s t 
    assume "(s,t) \<in> (rstep E')\<^sup>\<leftrightarrow>\<^sup>*"
    then show "(s,t) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def
    proof(induct)
      case base
      show ?case by auto
    next
      case (step t u)
      from step(2)[unfolded estep_sym_closure_conv] obtain l r C \<sigma> where t: "t = C\<langle>l\<cdot>\<sigma>\<rangle>"
        and u: "u = C\<langle>r \<cdot> \<sigma>\<rangle>" and lr: "(l,r) \<in> E' \<union> E'^-1" by auto
      from lr have steps: "(l,r) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*"
      proof
        assume "(l,r) \<in> E'"
        from steps[OF this] show ?thesis .
      next
        assume "(l,r) \<in> E'^-1" 
        then have "(r,l) \<in> E'" by simp
        from steps[OF this] have "(r,l) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" .
        with sym_rtrancl[OF sym_Un_converse, of "rstep E"]
        show ?thesis unfolding sym_def conversion_def by auto
      qed
      with subst.closed_rtrancl[OF subst_closed_estep[of E], unfolded subst.closed_def] 
      have steps: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" unfolding conversion_def by auto      
      have "(t,u) \<in> (rstep E)\<^sup>\<leftrightarrow>\<^sup>*" unfolding t u 
        by (rule ctxt.closedD[OF _ steps], blast)
      with step(3) show ?case unfolding conversion_def by simp
    qed
  qed
qed

text \<open>All
We say that the TRS @{term R} is a complete rewrite system for the
equational system @{term E} iff their respective equational
theories are the same and @{term R} is convergent, i.e., confluent
and terminating.
\<close>
definition
  completed_rewrite_system :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "completed_rewrite_system E R \<equiv> equivalent E R \<and> CR (rstep R) \<and> SN (rstep R)"

lemma completion_via_WCR_SN_simulation:
  assumes 1: "subsumes E R" 
    and 2: "subsumes R E"
    and 3: "WCR (rstep R)"
    and 4: "SN (rstep R)"
  shows "completed_rewrite_system E R"
  unfolding completed_rewrite_system_def equivalent_subsumes 
  using Newman[OF 4 3] 1 2 4 by auto

end
