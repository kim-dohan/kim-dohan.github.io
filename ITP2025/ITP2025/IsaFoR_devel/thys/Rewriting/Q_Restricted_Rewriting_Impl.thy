(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Q_Restricted_Rewriting_Impl
imports
  First_Order_Rewriting.Trs_Impl
  Q_Restricted_Rewriting
begin

definition prop_rstep_r_p_s where
  "prop_rstep_r_p_s nfs P R r p \<sigma> = {(s, t).
    (\<forall> u \<in> set (args (s |_ p)). P u) \<and>
    p \<in> poss s \<and> r \<in> R \<and> s |_ p = fst r \<cdot> \<sigma> \<and> t = replace_at s p (snd r \<cdot> \<sigma>) \<and>
    (nfs \<longrightarrow> Ball (\<sigma> ` vars_rule r) P)}"

definition
  check_prop_rstep_rule ::
    "bool \<Rightarrow> ((_, _) term \<Rightarrow> showsl check) \<Rightarrow>
     pos \<Rightarrow> (_,_) rule \<Rightarrow> (_,_) term \<Rightarrow> (_,_) term \<Rightarrow>
     showsl check"
where
  "check_prop_rstep_rule nfs P p rule s t \<equiv> do {
     check (p \<in> poss s) (showsl_pos p \<circ> showsl (STR '' is not a position of '') \<circ> showsl s \<circ> showsl_nl);
     check (p \<in> poss t) (showsl_pos p \<circ> showsl (STR '' is not a position of '') \<circ> showsl t \<circ> showsl_nl);
     let C = ctxt_of_pos_term p s;
     let D = ctxt_of_pos_term p t;
     let u = subt_at s p;
     let v = subt_at t p;
     (case match_list Var [(fst rule, u), (snd rule, v)] of
       Some \<tau> \<Rightarrow>
         check_allm P (args u @ (if nfs then map \<tau> (vars_rule_list rule) else []))
       >> check (C = D)
           (showsl (STR ''the term '') \<circ> showsl t
             \<circ> showsl (STR '' does not result from a proper application of rule\<newline>'')
             \<circ> showsl_rule rule \<circ> showsl (STR '' at position '') \<circ> showsl_pos p \<circ> showsl_nl)
     | None \<Rightarrow>
       error (showsl (STR ''the term '') \<circ> showsl t
             \<circ> showsl (STR '' does not result from a proper application of rule\<newline>'')
             \<circ> showsl_rule rule \<circ> showsl (STR '' at position '') \<circ> showsl_pos p \<circ> showsl_nl))
  }"

lemma check_prop_rstep_rule [simp]:
  "isOK (check_prop_rstep_rule nfs P p r s t) =
    (\<exists>\<sigma>. (s, t) \<in> prop_rstep_r_p_s nfs (\<lambda> t. isOK (P t)) {r} r p \<sigma>)" (is "?l = ?r")
proof 
  assume ok: ?l
  let ?C = "ctxt_of_pos_term p s"
  let ?D = "ctxt_of_pos_term p t"
  let ?mlist = "[(subt_at s p, fst r), (subt_at t p, snd r)]"
  note ok = ok[unfolded check_prop_rstep_rule_def Let_def, simplified]
  from ok have "p \<in> poss s" and "p \<in> poss t" by auto
  from ok obtain \<sigma> where some: "match_list Var [(fst r, s |_ p), (snd r, t |_ p)] = Some \<sigma>"
    by force
  let ?\<sigma> = "\<sigma>"
  note ok = ok[unfolded some option.simps, simplified]
  from match_list_sound [OF some] have "fst r \<cdot> ?\<sigma> = s |_ p" and "snd r \<cdot> ?\<sigma> = t |_ p" by auto
  then have "s |_ p = fst r \<cdot> ?\<sigma>" and "t = ?D\<langle>snd r \<cdot> ?\<sigma>\<rangle>"
    using ctxt_supt_id[OF \<open>p \<in> poss t\<close>]  by simp+
  moreover from ok
    have "?D = ?C" by simp
  moreover from ok 
    have "\<And> t. t \<in> set (args (s |_ p)) \<Longrightarrow> isOK (P t)" by simp
  moreover from ok 
    have "nfs \<Longrightarrow> Ball (?\<sigma> ` vars_rule r) (\<lambda> x. isOK( P x))" by auto
  ultimately have "(s, t) \<in> prop_rstep_r_p_s nfs (\<lambda> t. isOK (P t)) {r} r p ?\<sigma>"
    using \<open>p \<in> poss s\<close> unfolding prop_rstep_r_p_s_def some by force
  then show ?r by blast
next
  assume r: ?r  
  let ?P = "\<lambda> t. isOK (P t)"
  from r obtain \<sigma> where step: "(s, t) \<in> prop_rstep_r_p_s nfs ?P {r} r p \<sigma>" by auto
  let ?C = "ctxt_of_pos_term p s"
  let ?D = "ctxt_of_pos_term p t"
  from step have "p \<in> poss s" 
    and P: "\<forall>u \<in> set (args (s |_ p)). ?P u"
    and s: "s |_ p = fst r \<cdot> \<sigma>" and t: "t = ?C\<langle>snd r \<cdot> \<sigma>\<rangle>"
    and P2: "nfs \<Longrightarrow> Ball (\<sigma> ` vars_rule r) ?P"
    unfolding prop_rstep_r_p_s_def by auto
  from hole_pos_ctxt_of_pos_term[OF \<open>p \<in> poss s\<close>]
  have p: "p = hole_pos ?C" by simp
  obtain \<tau> where match: "match_list Var [(fst r, s |_ p), (snd r, t |_ p)] = Some \<tau>"
    and tau: "\<forall>x\<in>lvars [(fst r, s |_ p), (snd r, t |_ p)]. \<tau> x = \<sigma> x"
  proof -
    from subt_at_hole_pos[of "?C" "snd r \<cdot> \<sigma>", unfolded t[symmetric]]
      have 2: "t |_ p = snd r \<cdot> \<sigma>" unfolding p[symmetric] .
    assume *: "\<And>\<tau>. \<lbrakk>match_list Var [(fst r, s |_ p), (snd r, t |_ p)] = Some \<tau>;
      \<forall>x\<in>lvars [(fst r, s |_ p), (snd r, t |_ p)]. \<tau> x = \<sigma> x\<rbrakk> \<Longrightarrow> thesis"
    show ?thesis
    proof -
      from match_list_complete' [of "[(fst r, s |_ p), (snd r, t |_ p)]" \<sigma>, unfolded s 2]
        obtain \<sigma>' where "match_list Var [(fst r, s |_ p), (snd r, t |_ p)] = Some \<sigma>'"
        and "\<forall>x \<in> lvars [(fst r, s |_ p), (snd r, t |_ p)]. \<sigma> x = \<sigma>' x"
        unfolding s 2 by (metis (lifting, no_types) Pair_inject empty_iff empty_set set_ConsD)
      from * [OF this(1)] and this(2) show ?thesis by simp
    qed
  qed
  have "p \<in> set (poss_list s)" by (simp add: \<open>p \<in> poss s\<close>)
  moreover have "p \<in> set (poss_list t)"
    using p and hole_pos_poss[of "?C" "snd r \<cdot> \<sigma>"] by (simp add: t)
  moreover have "isOK(check_allm P (args (s |_ p)))" using P by auto
  moreover have "?C = ?D"
  proof -
    from hole_pos_id_ctxt[OF t[symmetric]]
    show ?thesis unfolding p[symmetric] ..
  qed
  ultimately show ?l using match tau P2 unfolding check_prop_rstep_rule_def Let_def by (auto simp: vars_rule_def)
qed


definition
  check_prop_rstep ::
    "bool \<Rightarrow> ((_,_) term \<Rightarrow> showsl check) \<Rightarrow>
     (_,_) rules \<Rightarrow>
     pos \<Rightarrow> (_,_) rule \<Rightarrow> (_,_) term \<Rightarrow> (_,_) term \<Rightarrow>
     showsl check"
where
  "check_prop_rstep nfs P R p rule s t \<equiv> do {
     check (\<exists> r \<in> set R. (rule =\<^sub>v r) \<and> isOK(check_prop_rstep_rule nfs P p r s t))
           (showsl (STR ''the step from '') \<circ> showsl s \<circ> showsl (STR '' to '') \<circ> showsl t \<circ> 
            showsl (STR '' via rule '') \<circ> showsl_rule rule \<circ> 
            showsl (STR '' at position '') \<circ> showsl_pos p \<circ> showsl (STR '' is problematic\<newline>''))
   }"

lemma check_prop_rstep_sound:
  assumes ok: "isOK (check_prop_rstep nfs P R p r s t)"
  shows "\<exists>\<sigma> r'. (s, t) \<in> prop_rstep_r_p_s nfs (\<lambda> t. isOK(P t)) (set R) r' p \<sigma> \<and> r =\<^sub>v r'"
proof -
  note ok = ok[unfolded check_prop_rstep_def, simplified]
  from ok obtain rule \<sigma> where rule: "rule \<in> set R" and instr: "r =\<^sub>v rule" 
   and step: "(s, t) \<in> prop_rstep_r_p_s nfs (\<lambda>t. isOK (P t)) {rule} rule p \<sigma>" by auto
  from instr have inst: "(fst r, snd r) =\<^sub>v (fst rule, snd rule)" by simp
  from step rule have step: "(s, t) \<in> prop_rstep_r_p_s nfs (\<lambda>t. isOK (P t)) (set R) rule p \<sigma>" 
    unfolding prop_rstep_r_p_s_def by auto
  from eq_rule_mod_varsE[OF inst] obtain \<delta> where fst: "fst r = fst rule \<cdot> \<delta>" and snd: "snd r = snd rule \<cdot> \<delta>" by auto
  show ?thesis
    by (intro exI conjI, rule step, rule instr)
qed


lemma check_prop_rstep_complete:
  assumes "\<exists>\<sigma>. (s, t) \<in> prop_rstep_r_p_s nfs (\<lambda> t. isOK (P t)) (set R) r p \<sigma>"
  shows "isOK (check_prop_rstep nfs P R p r s t)"
proof -
  let ?P = "\<lambda> t. isOK (P t)"
  from assms obtain \<sigma> where step: "(s, t) \<in> prop_rstep_r_p_s nfs ?P (set R) r p \<sigma>" by auto
  from step have step: "(s, t) \<in> prop_rstep_r_p_s nfs ?P {r} r p \<sigma>" and rule: "r \<in> set R" 
    unfolding prop_rstep_r_p_s_def by auto
  have "r =\<^sub>v r" by simp
  with rule step show ?thesis unfolding check_prop_rstep_def by force
qed

definition
  check_prop_rstep' ::
    "bool \<Rightarrow> ((_,_) term \<Rightarrow> showsl check) \<Rightarrow>
     (_,_) rules \<Rightarrow>
     pos \<Rightarrow> (_,_) rule \<Rightarrow> (_,_) term \<Rightarrow> (_,_) term \<Rightarrow>
     showsl check"
where
  "check_prop_rstep' nfs P R p rule s t \<equiv> do {
     check (rule \<in> set R)
       (showsl_rule rule \<circ> showsl (STR '' is not a rule of\<newline>'') \<circ> showsl_trs R \<circ> showsl_nl);
     check_prop_rstep_rule nfs P p rule s t
   }"

lemma check_prop_rstep'[simp]:
  "isOK (check_prop_rstep' nfs P R p r s t) = 
  (\<exists>\<sigma>. (s, t) \<in> prop_rstep_r_p_s nfs (\<lambda> t. isOK(P t)) (set R) r p \<sigma>)"
  unfolding check_prop_rstep'_def
  by (auto simp: prop_rstep_r_p_s_def)

lemma prop_rstep_qrstep: "prop_rstep_r_p_s nfs (\<lambda> t. t \<in> NF_terms Q) = qrstep_r_p_s nfs Q" (is "?l = ?r")
proof (intro ext)
  fix R r p \<sigma>
  show "?l R r p \<sigma> = ?r R r p \<sigma>"
  unfolding prop_rstep_r_p_s_def qrstep_r_p_s_def NF_terms_args_conv[symmetric]
  using subt_at_ctxt_of_pos_term[of p "fst r \<cdot> \<sigma>"]
  by (auto simp: NF_subst_def)
qed

lemma prop_rstep_rstep: "prop_rstep_r_p_s nfs (\<lambda> t. True) = rstep_r_p_s" (is "?l = ?r")
  by (intro ext, unfold prop_rstep_r_p_s_def rstep_r_p_s_def', simp)

lemma prop_rstep_qrstep_subst:
  fixes \<mu> :: "('f,'v)subst"
  assumes nvar: "is_Fun (fst r)"
  shows "(s,t) \<in> prop_rstep_r_p_s nfs (\<lambda> t. (\<forall> i. t \<cdot> \<mu> ^^ i \<in> NF_terms Q)) R r p \<sigma> = (\<forall> i. (s \<cdot> \<mu> ^^ i, t \<cdot> \<mu> ^^ i) \<in> qrstep_r_p_s nfs Q R r p (\<sigma> \<circ>\<^sub>s \<mu> ^^ i))" (is "?l = ?r")
proof -
  let ?NF = "\<lambda> t i. (\<forall> i. t \<cdot> \<mu> ^^ i \<in> NF_terms Q)"
  let ?c = "ctxt_of_pos_term p s"
  let ?QR = "qrstep_r_p_s nfs Q R r p"
  from nvar obtain f ls where l: "fst r = Fun f ls" by force
  show ?thesis
  proof
    assume ?l
    from this[unfolded prop_rstep_r_p_s_def Let_def, simplified]
    have p: "p \<in> poss s" and r: "r \<in> R" and s: "s |_ p = fst r \<cdot> \<sigma>" and t: "t = ?c\<langle>snd r \<cdot> \<sigma>\<rangle>" 
      and NF: "\<And> u i. u \<in> set (args (s |_ p)) \<Longrightarrow> u \<cdot> \<mu> ^^ i \<in> NF_terms Q" 
      and nfs: "\<And> x i. nfs \<Longrightarrow> x \<in> vars_rule r \<Longrightarrow> \<sigma> x \<cdot> \<mu> ^^ i \<in> NF_terms Q" by auto
    then obtain us where sp: "s |_ p = Fun f us" unfolding l by (cases "s |_ p", auto)
    from p have p': "\<And> i. p \<in> poss (s \<cdot> \<mu> ^^ i)" by (rule poss_imp_subst_poss) 
    show ?r 
    proof
      fix i
      let ?C = "ctxt_of_pos_term p (s \<cdot> \<mu> ^^ i)"
      show "(s \<cdot> \<mu> ^^ i, t \<cdot> \<mu> ^^ i) \<in> ?QR (\<sigma> \<circ>\<^sub>s \<mu> ^^ i)"
        unfolding prop_rstep_qrstep[symmetric] prop_rstep_r_p_s_def Let_def
      proof (rule, rule, intro conjI ballI impI)
        fix u
        assume "u \<in> set (args (s \<cdot> \<mu> ^^ i |_ p))"
        then obtain v where v: "v \<in> set (args (s |_ p))" and u: "u = v \<cdot> \<mu> ^^ i" unfolding subt_at_subst[OF p] sp
          by auto        
        show "u \<in> NF_terms Q" unfolding u using NF[OF v] .
      next
        show "p \<in> poss (s \<cdot> \<mu> ^^ i)" by (rule p')
      next
        show "r \<in> R" by (rule r)
      next
        have "fst r \<cdot> \<sigma> \<circ>\<^sub>s \<mu> ^^ i = s |_ p \<cdot> \<mu> ^^ i" using s[symmetric] by simp
        also have "... = s \<cdot> \<mu> ^^ i |_ p" unfolding subt_at_subst[OF p] ..
        finally show "s \<cdot> \<mu> ^^ i |_ p = fst r \<cdot> \<sigma> \<circ>\<^sub>s \<mu> ^^ i" by simp
      next          
        show "t \<cdot> \<mu> ^^ i = ?C\<langle>snd r \<cdot> \<sigma> \<circ>\<^sub>s \<mu> ^^ i\<rangle>"
          unfolding t subst_apply_term_ctxt_apply_distrib ctxt_of_pos_term_subst[OF p] ctxt_eq by simp
      next
        fix t
        assume nfs and t: "t \<in> (\<sigma> \<circ>\<^sub>s \<mu> ^^ i) ` vars_rule r"
        then obtain x where t: "t = (\<sigma> \<circ>\<^sub>s \<mu> ^^ i) x"  and x: "x \<in> vars_rule r" by auto
        from nfs[OF \<open>nfs\<close> x, of i]
        show "t \<in> NF_terms Q" unfolding t subst_compose_def .
      qed
    qed
  next
    assume ?r
    then have step: "\<And> i. (s \<cdot> \<mu> ^^ i, t \<cdot> \<mu> ^^ i) \<in> prop_rstep_r_p_s nfs (\<lambda> t. t \<in> NF_terms Q) R r p (\<sigma> \<circ>\<^sub>s \<mu> ^^ i)"
      unfolding prop_rstep_qrstep ..
    note step = step[unfolded prop_rstep_r_p_s_def Let_def]
    from step[of 0]
    have p: "p \<in> poss s" and r: "r \<in> R" and s: "s |_ p = fst r \<cdot> \<sigma>" and t: "t = ?c\<langle>snd r \<cdot> \<sigma>\<rangle>" by auto
    then have rs: "fst r \<cdot> \<sigma> = s |_ p" by simp
    then obtain us where sp: "s |_ p = Fun f us" unfolding l by (cases "s |_ p", auto)
    show ?l
      unfolding prop_rstep_r_p_s_def Let_def
    proof (rule, rule, intro conjI ballI impI allI)
      fix u i
      assume u: "u \<in> set (args (s |_ p))"
      from step[of i]
      have "\<And> v. v \<in> set (args (s \<cdot> \<mu> ^^ i |_ p)) \<Longrightarrow> v \<in> NF_terms Q" by auto
      with u  show "u \<cdot> \<mu> ^^ i \<in> NF_terms Q" unfolding subt_at_subst[OF p] sp by auto
    next
      fix t i
      assume "t \<in> \<sigma> ` vars_rule r" nfs
      then obtain x where t: "t = \<sigma> x" and x: "x \<in> vars_rule r" by auto
      then have "t \<cdot> \<mu> ^^ i \<in> (\<sigma> \<circ>\<^sub>s \<mu> ^^ i) ` vars_rule r" unfolding subst_compose_def by auto
      with step[of i] \<open>nfs\<close>
      show "t \<cdot> \<mu> ^^ i \<in> NF_terms Q" by auto
    qed (insert p r s t, auto)
  qed
qed

definition
  check_rstep' :: 
    "('f::showl, 'v::showl) rules \<Rightarrow> pos \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
      showsl check"
where
  "check_rstep' = check_prop_rstep' False (\<lambda> _. succeed)"

lemma check_rstep' [simp]:
  "isOK (check_rstep' R p r s t) = (\<exists> \<sigma>. (s, t) \<in> rstep_r_p_s (set R) r p \<sigma>)"
  unfolding check_rstep'_def by (simp add: prop_rstep_rstep)

definition
  check_qrstep ::
    "(('f::showl, 'v::showl) term \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('f, 'v) rules \<Rightarrow> pos \<Rightarrow> ('f, 'v) rule \<Rightarrow>
      ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
where
  "check_qrstep nf nfs =
    check_prop_rstep nfs (\<lambda> t. check (nf t) (showsl t \<circ> showsl (STR '' is not in Q-normal form'')))"

lemma check_qrstep_sound:
  assumes nf: "\<And>t. nf t \<longleftrightarrow> t \<in> NF_terms (set Q)"
    and  ok: "isOK (check_qrstep nf nfs R p r s t)"
  shows "\<exists> \<sigma> r. (s, t) \<in> qrstep_r_p_s nfs (set Q) (set R) r p \<sigma>"
  using check_prop_rstep_sound[OF ok[unfolded check_qrstep_def]]
  unfolding isOK_check prop_rstep_qrstep[symmetric] using nf by auto


lemma check_qrstep_complete:
  assumes nf: "\<And>t. nf t \<longleftrightarrow> t \<in> NF_terms (set Q)"
  and ok: "\<exists> \<sigma>. (s, t) \<in> qrstep_r_p_s nfs (set Q) (set R) r p \<sigma>"
  shows "isOK (check_qrstep nf nfs R p r s t)"
  unfolding check_qrstep_def nf 
  by (rule check_prop_rstep_complete, insert ok[unfolded prop_rstep_qrstep[symmetric]], auto)

lemma check_qrstep_qrstep:
  assumes nf: "\<And>t. nf t \<longleftrightarrow> t \<in> NF_terms (set Q)"
    and  ok: "isOK (check_qrstep nf nfs R p r s t)"
  shows "(s, t) \<in> qrstep nfs (set Q) (set R)"
  unfolding qrstep_qrstep_r_p_s_conv
  using check_qrstep_sound[OF nf ok] by auto

definition
  check_no_defined_root :: "((_ \<times> nat) \<Rightarrow> bool) \<Rightarrow> (_,_) term \<Rightarrow> showsl check"
where
  "check_no_defined_root isdef t =
    check (\<not> isdef (the (root t))) (
      showsl (STR ''the root of '') \<circ> showsl t \<circ> showsl (STR '' is defined''))"

lemma check_no_defined_root_sound[simp]:
  "isOK (check_no_defined_root isdef t) \<longleftrightarrow> \<not> isdef (the (root t))"
  by (cases t) (auto simp: check_no_defined_root_def)

definition
  "check_rqrstep nf nfs R rule s t \<equiv> check_qrstep nf nfs R [] rule s t"

lemma check_rqrstep_sound':
  assumes nf: "\<And>t. nf t \<longleftrightarrow> t \<in> NF_terms (set Q)"
    and ok: "isOK (check_rqrstep nf nfs R r s t)"
  shows "\<exists>\<sigma> r. (s, t) \<in> qrstep_r_p_s nfs (set Q) (set R) r [] \<sigma>"
  using check_qrstep_sound[OF assms[unfolded check_rqrstep_def]] .

lemma check_rqrstep_sound:
  assumes nf: "\<And>t. nf t \<longleftrightarrow> t \<in> NF_terms (set Q)"
    and ok: "isOK (check_rqrstep nf nfs R r s t)"
  shows "(s, t) \<in> rqrstep nfs (set Q) (set R)"
  using check_qrstep_sound[OF assms[unfolded check_rqrstep_def]]
  unfolding rqrstep_def qrstep_r_p_s_def by auto

type_synonym  ('f, 'v) prseq = "(pos \<times> ('f, 'v) rule \<times> bool \<times> ('f, 'v) term) list"
type_synonym  ('f, 'v) rseq = "(pos \<times> ('f, 'v) rule \<times> ('f, 'v) term) list"

fun
  check_qsteps ::
    "(('f::showl, 'v::showl) term \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow>
     ('f, 'v) prseq \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
where
  "check_qsteps nf nfs P R [] s u = check (s = u) (
    showsl (STR ''the last term of the rewrite sequence\<newline>'') \<circ> showsl s \<circ>
    showsl (STR ''\<newline>does not correspond to the goal term\<newline>'') \<circ> showsl u \<circ> showsl_nl)"
| "check_qsteps nf nfs P R ((_, r, True, t) # prts) s u = do {
    check_rqrstep nf nfs P r s t;
    check_qsteps nf nfs P R prts t u
  }"
| "check_qsteps nf nfs P R ((p, r, False, t) # prts) s u = do {
    check_qrstep nf nfs R p r s t;
    check_qsteps nf nfs P R prts t u
  }"

lemma check_qsteps_sound:
  assumes nf: "\<And>t. nf t \<longleftrightarrow> t \<in> NF_terms (set Q)"
    and ok: "isOK (check_qsteps nf nfs P R rseq s t)"
  shows "(s, t) \<in> (rqrstep nfs (set Q) (set P) \<union> qrstep nfs (set Q) (set R))^^(length rseq)"
proof -
  obtain PR where PR: "PR = rqrstep nfs (set Q) (set P) \<union> qrstep nfs (set Q) (set R)" by auto
  from ok show ?thesis unfolding PR[symmetric] 
  proof (induct rseq arbitrary: s)
    case Nil then show ?case by simp
  next
    case (Cons prt rseq)
    obtain p r or u where prt: "prt = (p, r, or, u)" by (cases prt, blast)
    from Cons[unfolded prt]
    have IH: "(u, t) \<in> PR ^^ (length rseq)" by (cases or, induct rseq) auto
    have "(s, u) \<in> PR"
    proof (cases or)
      case True
      with Cons[unfolded prt]
      have "isOK (check_rqrstep nf nfs P r s u)" by simp
      from check_rqrstep_sound[OF nf this]
        have "(s, u) \<in> rqrstep nfs (set Q) (set P)" .
      then show ?thesis unfolding PR ..
    next
      case False
      with Cons[unfolded prt]
      have "isOK (check_qrstep nf nfs R p r s u)" by simp
      from check_qrstep_qrstep[OF nf this]
        have "(s, u) \<in> qrstep nfs (set Q) (set R)" .
      then show ?thesis unfolding PR ..
    qed
    with IH show ?case unfolding prt o_def using relpow_Suc_I2[of s u PR] by simp
  qed
qed

definition
  "check_qrsteps nf nfs R prts s u \<equiv>
    check_qsteps nf nfs [] R (map (\<lambda>(p, r, t). (p, r, False, t)) prts) s u"

lemma check_qrsteps_sound:
  assumes nf: "\<And>t. nf t \<longleftrightarrow> t \<in> NF_terms (set Q)"
    and ok: "isOK (check_qrsteps nf nfs R rseq s t)"
  shows "(s, t) \<in> (qrstep nfs (set Q) (set R))^^(length rseq)"
proof -
  have empty: "rqrstep nfs (set Q) {} \<union> qrstep nfs (set Q) (set R) = qrstep nfs (set Q) (set R)"
    unfolding rqrstep_def qrstep_r_p_s_def by auto
  from check_qsteps_sound[OF assms[unfolded check_qrsteps_def]]
    show ?thesis by (auto simp: Let_def empty)
qed

definition "check_rsteps \<equiv> check_qrsteps (\<lambda> _. True) False"

lemma check_rsteps_sound:
  assumes ok: "isOK (check_rsteps R rseq s t)"
  shows "(s, t) \<in> (rstep (set R))^^(length rseq)"
  unfolding qrstep_rstep_conv[symmetric]
  using check_qrsteps_sound[OF _ ok[unfolded check_rsteps_def], of Nil]
  by auto

lemma check_rsteps_sound_star:
  assumes ok: "isOK (check_rsteps R rseq s t)"
  shows "(s, t) \<in> (rstep (set R))^*"
  using relpow_imp_rtrancl[OF check_rsteps_sound[OF ok]] .

definition rseq_last :: "('f,'v)term \<Rightarrow> ('f,'v) rseq \<Rightarrow> ('f,'v)term"
  where "rseq_last s steps \<equiv> last (s # map (\<lambda> (_,_,s). s) steps)"

definition "check_rsteps_last \<equiv> \<lambda> R s steps. check_rsteps R steps s (rseq_last s steps)"

lemma check_rsteps_last_sound_length:
  assumes ok: "isOK (check_rsteps_last R s rseq)"
  shows "(s, rseq_last s rseq) \<in> (rstep (set R))^^ (length rseq)"
  by (rule check_rsteps_sound[OF ok[unfolded check_rsteps_last_def]])

lemma check_rsteps_last_sound:
  assumes ok: "isOK (check_rsteps_last R s rseq)"
  shows "(s, rseq_last s rseq) \<in> (rstep (set R))^*"
  by (rule check_rsteps_sound_star[OF ok[unfolded check_rsteps_last_def]])

(* version of check_rsteps that does not permit using variants of rules  *)
fun check_rsteps' ::
  "('f :: showl, 'v :: showl) rules \<Rightarrow> ('f, 'v) rseq \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
where
  "check_rsteps' R [] s u = check (s = u) (
    showsl (STR ''the last term of the rewrite sequence\<newline>'') \<circ> showsl s \<circ> 
    showsl (STR ''\<newline>does not correspond to the goal term\<newline>'') \<circ> showsl u \<circ> showsl_nl)"
| "check_rsteps' R ((p, lr, t) # rs) s u = do {
     check_rstep' R p lr s t;
     check_rsteps' R rs t u
   }"


subsection \<open>Efficient Normal Form Checking\<close>

definition NF_subst_impl :: "(('f,'v)term \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('f,'v)rule \<Rightarrow> ('f,'v) subst \<Rightarrow> bool"
  where "NF_subst_impl nf nfs r \<sigma> \<equiv> if nfs then (\<forall> x \<in> set (vars_rule_list r). nf (\<sigma> x)) else True"

lemma NF_subst_impl[simp]: "NF_subst_impl (\<lambda> t. t \<in> NF_terms Q) nfs r \<sigma> = NF_subst nfs r \<sigma> Q"
  unfolding NF_subst_impl_def NF_subst_def by auto

(* checking NF-term sets (Q) modulo variable names *)
definition NF_vars_subset :: "('f,'v)terms \<Rightarrow> ('f,'v)terms \<Rightarrow> bool"
  where "NF_vars_subset Q Q' \<equiv> \<forall> q \<in> Q. \<exists> q' \<in> Q'. matches q q'"

lemma NF_vars_subsetI[intro]: assumes "\<And> q. q \<in> Q \<Longrightarrow> \<exists> q' \<in> Q'. matches q q'"
  shows "NF_vars_subset Q Q'" using assms unfolding NF_vars_subset_def by auto

lemma NF_vars_subset[simp]: assumes "NF_vars_subset Q Q'"
  shows "NF_terms Q' \<subseteq> NF_terms Q"
proof
  fix t
  assume Q: "t \<in> NF_terms Q'"
  show "t \<in> NF_terms Q"
  proof
    fix C l \<sigma>
    assume t: "t = C \<langle> l \<cdot> \<sigma> \<rangle>" and l: "l \<in> Q"
    from assms[unfolded NF_vars_subset_def matches_iff] l obtain l' \<mu> where l: "l' \<in> Q'"
      and mu: "l = l' \<cdot> \<mu>" by auto
    have t: "t = C \<langle> l' \<cdot> (\<mu> \<circ>\<^sub>s \<sigma>) \<rangle>" unfolding t mu by simp
    then obtain \<delta> where "t = C \<langle> l' \<cdot> \<delta> \<rangle>" by blast
    with l Q show False by auto
  qed
qed

definition check_NF_vars_subset :: "('f,'v)term list \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term check"
  where "check_NF_vars_subset Q Q' \<equiv> check_allm (\<lambda> q. check (\<exists> q' \<in> set Q'. matches q q') q) Q"

lemma check_NF_vars_subset[simp]: "isOK(check_NF_vars_subset Q Q') = NF_vars_subset (set Q) (set Q')"
  unfolding check_NF_vars_subset_def NF_vars_subset_def by auto

definition check_NF_terms_subset :: "(('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term check"
  where "check_NF_terms_subset is_Q_nf \<equiv> (\<lambda> Q'. check_all (\<lambda> q. \<not> is_Q_nf q) Q')"

lemma check_NF_terms_subset[simp]: "isOK(check_NF_terms_subset (\<lambda> t. t \<in> NF_trs R) Q') = (NF_trs R \<subseteq> NF_terms (set Q'))" 
  unfolding check_NF_terms_subset_def 
  using NF_terms_subset_criterion[of "set Q'" "lhss R", unfolded NF_terms_lhss[of R]] by auto

definition check_NF_trs_subset :: "('f :: compare_order,'v)rules \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term check"
  where "check_NF_trs_subset R \<equiv> check_NF_terms_subset (is_NF_trs R)"

lemma check_NF_trs_subset[simp]: "isOK(check_NF_trs_subset R Q) = (NF_trs (set R) \<subseteq> NF_terms (set Q))"
  unfolding check_NF_trs_subset_def is_NF_trs by simp

definition is_NF_subset :: "(('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)term list \<Rightarrow> bool"
  where "is_NF_subset is_Q_nf Q' \<equiv> \<forall> q \<in> set Q'.  \<not> is_Q_nf q"

lemma is_NF_subset[simp]: "is_NF_subset (\<lambda> t. t \<in> NF_terms Q) Q' = (NF_terms Q \<subseteq> NF_terms (set Q'))" 
  unfolding NF_terms_subset_criterion[symmetric] is_NF_subset_def by auto

definition is_NF_trs_subset :: "(('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)rules \<Rightarrow> bool"
  where "is_NF_trs_subset is_Q_nf R \<equiv> is_NF_subset is_Q_nf (map fst R)"

lemma is_NF_trs_subset[simp]: "is_NF_trs_subset (\<lambda> t. t \<in> NF_terms Q) R = (NF_terms Q \<subseteq> NF_trs (set R))" 
  unfolding is_NF_trs_subset_def is_NF_subset using NF_terms_lhss[of "set R"] by auto

definition check_NF_terms_eq :: "('f :: compare_order,'v)term list \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term check"
  where "check_NF_terms_eq Q Q' \<equiv> do {
      check_NF_terms_subset (is_NF_terms Q) Q';
      check_NF_terms_subset (is_NF_terms Q') Q
    }"

lemma check_NF_terms_eq[simp]: "isOK(check_NF_terms_eq Q Q') = (NF_terms (set Q) = NF_terms (set Q'))" unfolding check_NF_terms_eq_def  by auto


definition applicable_rule_impl :: "(('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)rule \<Rightarrow> bool"
 where "applicable_rule_impl isNF \<equiv> \<lambda> (l,r). Ball (set (args l)) isNF"

lemma applicable_rule_impl[simp]: assumes isNF: "\<And> s. isNF s = (s \<in> NF_terms Q)"
  shows "applicable_rule_impl isNF lr = applicable_rule Q lr"
  unfolding applicable_rule_def NF_terms_args_conv[symmetric]
  unfolding applicable_rule_impl_def isNF[symmetric] by (cases lr, auto)

definition check_non_applicable_rules :: "(('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)rule list \<Rightarrow> ('f,'v)rule check"
 where "check_non_applicable_rules isNF r \<equiv> check_all (\<lambda> lr. \<not> applicable_rule_impl isNF lr) r"

lemma check_non_applicable_rules: assumes isNF: "\<And> s. isNF s = (s \<in> NF_terms Q)"
  and ok: "isOK(check_non_applicable_rules isNF r)"
  shows "qrstep nfs Q (R - set r) = qrstep nfs Q R" (is "?r = ?l")
proof
  show "?r \<subseteq> ?l" by (rule qrstep_mono, auto)
  have "?l = qrstep nfs Q (applicable_rules Q R)" unfolding qrstep_applicable_rules ..
  also have "... \<subseteq> ?r" 
  proof (rule qrstep_mono[OF _ subset_refl])
    show "applicable_rules Q R \<subseteq> R - set r" (is "?l \<subseteq> ?r")
    proof
      fix l r
      assume "(l,r) \<in> ?l"
      from this[unfolded applicable_rules_def] have lr: "(l,r) \<in> R"
        and app: "applicable_rule Q (l,r)" by auto
      from lr app ok[unfolded check_non_applicable_rules_def, unfolded applicable_rule_impl[OF isNF]]
      show "(l,r) \<in> ?r" by auto
    qed
  qed
  finally show "?l \<subseteq> ?r" .
qed

definition
  "check_wwf_qtrs nf R \<equiv> (
    check_allm (\<lambda>r. if applicable_rule_impl nf r
      then (do {
        check (is_Fun (fst r)) (showsl (STR ''variable left-hand side in''));
        check_subseteq (vars_term_list (snd r)) (vars_term_list (fst r))
          <+? (\<lambda>x. showsl (STR ''free variable '') \<circ> showsl x
            \<circ> showsl (STR '' in right-hand side of''))
      } <+? (\<lambda>s. s \<circ> showsl (STR '' rule '') \<circ> showsl_rule r \<circ> showsl_nl)) else succeed) R
      <+? (\<lambda>e. showsl (STR ''the Q-TRS is not weakly well-formed\<newline>'') \<circ> e))"

lemma check_wwf_qtrs_sound[simp]:
  shows "isOK (check_wwf_qtrs (\<lambda> t. t \<in> NF_terms Q) R) = wwf_qtrs Q (set R)"
  unfolding check_wwf_qtrs_def wwf_qtrs_def applicable_rule_impl[OF refl]
    split_def by auto

definition
  wwf_qtrs_impl :: "(('f, 'v) term \<Rightarrow> bool) \<Rightarrow> ('f, 'v) rules \<Rightarrow> bool"
where
  "wwf_qtrs_impl nf R \<longleftrightarrow> (\<forall> r \<in> set R. wf_rule r \<or> \<not> applicable_rule_impl nf r)"

lemma wwf_qtrs_impl[simp]:
  "wwf_qtrs_impl (\<lambda> t. t \<in> NF_terms Q) R = wwf_qtrs Q (set R)"
  unfolding wwf_qtrs_impl_def 
  unfolding wwf_qtrs_wwf_rules 
  unfolding applicable_rule_impl[OF refl]
  unfolding wwf_rule_def wf_rule_def by force

context
  fixes nfs :: bool
  and nfq :: "(('f,'v)term \<Rightarrow> bool)" 
  and R :: "('f,'v)rules" 
begin
fun qrewrite :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list"
where
  "qrewrite s = remdups [ r \<cdot> \<sigma> . Ball (set (args s)) nfq, (l,r) \<leftarrow> R, \<sigma> \<leftarrow> option_to_list (match s l), case l of Var x \<Rightarrow> nfs \<longrightarrow> nfq (\<sigma> x) | _ \<Rightarrow> True]
     @ (case s of Var _ \<Rightarrow> [] | Fun f ss \<Rightarrow> [ Fun f (ss [i := ti]) . i \<leftarrow> [0 ..< length ss], ti \<leftarrow> qrewrite (ss ! i)])"

declare qrewrite.simps[simp del]

lemma qrewrite: assumes varcond: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l" 
  and nfq: "\<And> t. nfq t = (t \<in> NF_terms Q)"
  shows "set (qrewrite s) = { t. (s,t) \<in> qrstep nfs Q (set R)}" 
proof -
  define vartest where "vartest l \<sigma> = (case l of Var x \<Rightarrow> nfs \<longrightarrow> nfq (\<sigma> x) | _ \<Rightarrow> True)" 
    for l :: "('f,'v)term" and \<sigma> :: "('f,'v)subst" 
  {
    fix t
    assume "(s,t) \<in> qrstep nfs Q (set R)" 
    hence "t \<in> set (qrewrite s)" 
    proof (standard, goal_cases)
      case (1 C \<sigma> l r)
      from supt_imp_args[OF 1(1)] 
      have args: "Ball (set (args (l \<cdot> \<sigma>))) nfq = True" using nfq by auto
      from 1(2) have lr: "(l,r) \<in> set R" .
      show ?case unfolding 1(3-4)
      proof (induct C)
        case Hole
        from match_complete'[of l \<sigma>, OF refl]
        obtain \<tau> where match: "match (l \<cdot> \<sigma>) l = Some \<tau>" 
          and vars: "(\<forall>x\<in>vars_term l. \<sigma> x = \<tau> x)" by auto        
        from varcond[OF lr] vars have same: "(\<forall>x\<in>vars_term r. \<sigma> x = \<tau> x)" by auto
        hence r: "r \<cdot> \<sigma> = r \<cdot> \<tau>" by (meson term_subst_eq)
        from match_sound[OF match] have l: "l \<cdot> \<sigma> = l \<cdot> \<tau>" by auto
        {
          fix x
          assume "l = Var x" nfs
          with 1(5) have "nfq (\<tau> x)" using vars unfolding NF_subst_def by (auto simp: vars_rule_def nfq)
        } 
        hence vtest: "vartest l \<tau>" by (cases l, auto simp: vartest_def)
        show ?case unfolding intp_actxt.simps
          apply (subst qrewrite.simps)
          apply (unfold args if_True set_append set_concat vartest_def[symmetric])
          apply (rule UnI1)
          using match l r lr vtest by auto
      next
        case (More f bef C aft)
        show ?case unfolding intp_actxt.simps
          apply (subst qrewrite.simps)
          apply (unfold args term.simps set_append set_concat set_map image_comp o_def set_upt)
          apply (rule UnI2)
          apply (rule UN_I[of "length bef"])
          using More by auto
      qed
    qed
  }
  moreover
  {
    fix t
    assume "t \<in> set (qrewrite s)" 
    hence "(s,t) \<in> qrstep nfs Q (set R)" 
    proof (induct s arbitrary: t rule: qrewrite.induct)
      case (1 s t)
      show ?case
      proof (cases "(\<exists>ss f. s = Fun f ss \<and> (\<exists>i\<in>{0..<length ss}. t \<in> (\<lambda>ti. Fun f (ss[i := ti])) ` set (qrewrite (ss ! i))))")
        case False
        with 1(2)[unfolded qrewrite.simps[of s] vartest_def[symmetric]] obtain l r \<sigma> where 
          args: "(\<forall>x\<in>set (args s). nfq x)" and lr: "(l,r) \<in>set R" 
          and match: "match s l = Some \<sigma>" and t: "t = r \<cdot> \<sigma>" 
          and vtest: "vartest l \<sigma>" by auto
        from match_sound[OF match] have s: "s = l \<cdot> \<sigma>" by auto
        from args[unfolded nfq] have args2: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" unfolding s by (simp add: NF_rstep_supt_args_conv)
        have "NF_subst nfs (l, r) \<sigma> Q" 
        proof (cases l)
          case (Fun f ll)
          thus ?thesis using args varcond[OF lr] s by (intro NF_subst_from_NF_args, auto simp: wf_rule_def nfq)
        next
          case (Var x)
          thus ?thesis using vtest[unfolded vartest_def] varcond[OF lr] by (auto simp: NF_subst_def vars_rule_def nfq)
        qed
        from rqrstepI[OF args2 lr s t this] 
        show ?thesis by blast
      next
        case True
        then obtain f ss i ti where s: "s = Fun f ss" and i: "i < length ss" and ti: "ti \<in> set (qrewrite (ss ! i))" 
          and t: "t = Fun f (ss [i := ti])" by auto
        from 1(1)[OF s _ ti] i have IH: "(ss ! i, ti) \<in> qrstep nfs Q (set R)" by auto
        have "((More f (take i ss) \<box> (drop (Suc i) ss))\<langle>ss ! i\<rangle>, (More f (take i ss) \<box> (drop (Suc i) ss))\<langle>ti\<rangle>) = (s,t)" 
          unfolding s t using i
          by (simp add: id_take_nth_drop[symmetric] upd_conv_take_nth_drop)  
        from qrstep.ctxt[OF IH, of "More f (take i ss) Hole (drop (Suc i) ss)", unfolded this] 
        show ?thesis .
      qed
    qed
  }
  ultimately show ?thesis by blast
qed
end

end
