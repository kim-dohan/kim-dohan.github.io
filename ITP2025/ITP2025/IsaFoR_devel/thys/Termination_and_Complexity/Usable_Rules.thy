(*
Author:  Alexander Krauss <krauss@in.tum.de> (2009)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Rules
imports
  TRS.Tcap
  First_Order_Rewriting.Trs_Impl
  Ord.Reduction_Pair
  AC_TRS.AC_Rewriting
begin

definition qrewrite :: "bool \<Rightarrow> ('f,'v)terms \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term list"
  where "qrewrite nfs Q R t \<equiv> filter (\<lambda> s. (t,s) \<in> qrstep nfs Q (set R)) (rewrite R t)" 

lemma qrewrite_sound: assumes "t \<in> set (qrewrite nfs Q R s)"
  shows "(s,t) \<in> qrstep nfs Q (set R)" using assms unfolding qrewrite_def by auto

lemma qrewrite_complete:
  assumes SN: "SN_on (qrstep nfs Q (set R)) {s}"
  and qstep: "(s,t) \<in> qrstep nfs Q (set R)"
  and nfs: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q (set R)"
  shows "t \<in> set (qrewrite nfs Q R s)" 
  using qstep
proof 
  fix C \<sigma> l r
  assume Q: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms Q" and lr: "(l,r) \<in> set R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  from wwf_qtrs_imp_nfs_False_switch[OF nfs, of nfs] have switch:
    "qrstep nfs Q (set R) = qrstep False Q (set R)" .
  note SN = SN[unfolded switch]
  note qstep = qstep[unfolded switch]
  from only_applicable_rules[OF Q] SN_on_imp_wwf_rule[OF SN s lr Q, unfolded wwf_rule_def] 
  have vars: "vars_term r \<subseteq> vars_term l" by auto
  from lr s t have "(s,t) \<in> rstep (set [(l,r)])" by auto
  with vars have "t \<in> set (rewrite [(l,r)] s)" 
    by (subst rewrite, auto)
  hence step: "t \<in> set (rewrite R s)" using lr rewrite_mono[of "[(l,r)]" R s] by auto
  then show ?thesis using qstep unfolding qrewrite_def switch by auto
qed

definition qrelac where "qrelac Q R E \<equiv> relto (qrstep False Q R) (rstep E)"

lemma qrstep_subset_qrelac: "qrstep False Q R \<subseteq> qrelac Q R E" unfolding qrelac_def by auto

lemma qrelac_empty_is_qrstep: "qrelac Q R {} = qrstep False Q R"
  unfolding qrelac_def by auto

lemma ctxt_closed_qrelac: "ctxt.closed (qrelac Q R E)"
  unfolding qrelac_def
  by (rule ctxt.closed_relto[OF ctxt_closed_qrstep ctxt_closed_rstep]) 
  

locale itrans = 
  fixes Q :: "('f,'v)terms"
  and R :: "('f,'v)trs"
  and RE :: "('f,'v)trs"
  and E :: "('f,'v)trs"
  and ur :: "('f,'v)trs"
  and us :: "('f \<times> nat)set"
  and cn :: "('f \<times> nat)"
  assumes AC_E: "AC_theory E" (* required for tcap, otherwise root- and symbol-preserving suffices *)
  and sym_E: "symmetric_trs E"
  and fin: "finite R"
begin

sublocale AC_theory E by (rule AC_E)

lemmas sym_step = symmetric_trs_sym_step[OF sym_E]
lemmas sym_rstep_E = symmetric_trs_sym_rstep[OF sym_E] symmetric_trs_sym_rstep[OF sym_E, symmetric]

lemma fin_branch_E: "finite ((rstep E)^* `` {t})"
  using finite_reachable[of t] 
  unfolding Image_def by auto  

definition ac_equiv_list :: "('f,'v)term \<Rightarrow> ('f,'v)term list" where
  "ac_equiv_list t = (SOME ss. set ss = (rstep E)^* `` {t})"

lemma ac_equiv_list[simp]: "set (ac_equiv_list t) = (rstep E)^* `` {t}"
  using finite_list[OF fin_branch_E[of t]] unfolding ac_equiv_list_def by (rule someI_ex)

lemma fin_branch: assumes SN: "SN_on (qrelac Q R E) {t}"
  shows "finite (qrelac Q R E `` {t})"
proof -
  let ?E = "(rstep E)^*"
  from finite_list[OF fin] obtain RR where R: "R = set RR" by auto
  from finite_list[OF fin_branch_E[of t]] obtain ts where ts: "set ts = (rstep E)^* `` {t}" by auto
  {
    fix ti
    assume "ti \<in> set ts"
    then have step: "(t,ti) \<in> ?E" unfolding ts by auto
    have SN: "SN_on (qrelac Q R E) {ti}" unfolding qrelac_def
      by (rule steps_preserve_SN_on_relto[OF _ SN[unfolded qrelac_def]], insert step, regexp)
    have SN: "SN_on (qrstep False Q R) {ti}"
      by (rule SN_on_mono[OF SN], auto simp: qrelac_def)
    have "qrstep False Q R `` {ti} = set (qrewrite False Q RR ti)"
      using qrewrite_sound[of _ False Q RR ti] qrewrite_complete[OF SN[unfolded R]]
      unfolding R[symmetric] by auto
  }
  then have "set [u . ti \<leftarrow> ts, u \<leftarrow> qrewrite False Q RR ti] \<supseteq> (?E O qrstep False Q R) `` {t}"
    using ts by auto
  from finite_subset[OF this] have "finite ((?E O qrstep False Q R) `` {t})" by auto
  from finite_list[OF this] obtain xs where xs: "set xs = (?E O qrstep False Q R) `` {t}" by auto
  have id: "qrelac Q R E `` {t} = set [y . x \<leftarrow> xs, y \<leftarrow> ac_equiv_list x]"
    using xs by (auto simp: qrelac_def)
  show ?thesis unfolding id by blast
qed

lemma ACEQ_identities: assumes st: "(s,t) \<in> (rstep E)^*"
  shows "(rstep E)^* `` {s} = (rstep E)^* `` {t}" "ac_equiv_list s = ac_equiv_list t"
proof -
  show "(rstep E)^* `` {s} = (rstep E)^* `` {t}" using sym_step[OF st] st 
    unfolding rstep_simps(5) Image_def sym_rstep_E(2) using rtrancl_trans[of _ _ "(rstep E)\<^sup>\<leftrightarrow>"] by blast
  then show "ac_equiv_list s = ac_equiv_list t" unfolding ac_equiv_list_def by auto
qed

lemma ACEQ_qrelac: assumes st: "(s,t) \<in> (rstep E)^*"
  shows "qrelac Q R E `` {s} = qrelac Q R E `` {t}"
proof -
  let ?A = "(rstep E)^*"
  {
    fix z s t 
    assume st: "(s,t) \<in> ?A" and z: "z \<in> qrelac Q R E `` {t}"
    from z[unfolded qrelac_def] obtain x where tx: "(t,x) \<in> ?A^*"
      and xz: "(x,z) \<in> qrstep False Q R O ?A^*" by blast
    from st tx have "(s,x) \<in> ?A^*" by (rule converse_rtrancl_into_rtrancl)
    with xz have "z \<in> qrelac Q R E `` {s}" unfolding qrelac_def by auto
  } note main = this
  from sym_step[OF st] have "(t,s) \<in> ?A" .
  from main[OF st] main[OF this] show ?thesis by auto
qed

fun i_trans_check :: "('f,'v)term \<Rightarrow> bool" where 
  "i_trans_check (Fun f ts) = 
    ((f,length ts) \<in> us \<and> \<not> (\<exists> (l,r) \<in> RE - ur. match_tcap_below l RE (Fun f ts)))"

definition qr_successors :: "('f,'v)term \<Rightarrow> ('f,'v)term list" where
  "qr_successors t = (SOME list. set list = qrelac Q R E `` {t})"

lemma qr_successors[simp]: assumes "SN_on (qrelac Q R E) {t}"
  shows "set (qr_successors t) = qrelac Q R E `` {t}"
proof -
  from fin_branch[OF assms] have "\<exists> xs. set xs = qrelac Q R E `` {t}" by (rule finite_list)
  then show ?thesis unfolding qr_successors_def
    by (rule someI_ex)
qed

definition "ac_subterms_list f ts = [(g,ss) . s \<leftarrow> ac_equiv_list (Fun f ts), (g,ss) \<leftarrow> case s of Fun g ss \<Rightarrow> [(g,ss)] | _ \<Rightarrow> []]"

lemma ac_subterms_list: "set (ac_subterms_list f ts) = { (g,ss). (Fun f ts, Fun g ss) \<in> (rstep E)^*}"
  unfolding ac_subterms_list_def by auto

lemma ac_subterms_list_id: "(f, ts) \<in> set (ac_subterms_list f ts)"
  unfolding ac_subterms_list by auto

declare i_trans_check.simps[simp del]

function i_trans :: "('f,'v)term \<Rightarrow> ('f,'v)term"
where "i_trans (Var x) = (Var x)" 
   |  "i_trans (Fun f ts) = (if SN_on (qrelac Q R E) {Fun f ts} then (
         if i_trans_check (Fun f ts) then Fun f (map i_trans ts) 
           else (comb cn) (map (\<lambda> (g,ss). Fun g (map i_trans ss)) (ac_subterms_list f ts) 
            @ map i_trans (qr_successors (Fun f ts)))
  )  else Fun f ts)"
by (pat_completeness, auto)


termination i_trans
proof -
  interpret E_compatible "qrelac Q R E" "(rstep E)^*" 
    by (standard, auto simp: qrelac_def) 
  have "SN (restrict_SN_supt_E)" 
    by (rule ctxt_closed_imp_SN_restrict_SN_E_supt[OF ctxt_closed_qrelac SN_supt_relto])
  then have wf: "wf (restrict_SN_supt_E\<inverse>)" (is "wf ?R")  by (simp add: SN_iff_wf)
  show ?thesis
    by (standard, rule wf, auto simp: ac_subterms_list intro!: restrict_SN_supt_E_I[OF ctxt_closed_qrelac])
qed


abbreviation
  i_trans_subst ::
    "('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
where
  "i_trans_subst \<sigma> \<equiv> (\<lambda>x. i_trans (\<sigma> x))"
end

fun ur_closed_term_af :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f \<times> nat)set \<Rightarrow> 'f af \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
where "ur_closed_term_af _ _ _ _ (Var x) = True"
   |  "ur_closed_term_af R ur us \<pi> (Fun f ts) = ((f,length ts) \<in> us 
     \<and> (\<forall> i < length ts. i \<in> \<pi> (f, (length ts)) \<longrightarrow> ur_closed_term_af R ur us \<pi> (ts ! i)) \<and> 
  (\<forall> (l,r) \<in> R. match_tcap_below l R (Fun f ts) \<longrightarrow> (l,r) \<in> ur) 
)"

abbreviation ur_closed_af :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f \<times> nat)set \<Rightarrow> 'f af \<Rightarrow> bool"
where "ur_closed_af R ur us \<pi> \<equiv> 
   (\<forall> (l,r) \<in> ur. ur_closed_term_af R ur us \<pi> r)"

abbreviation ur_P_closed_af :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f \<times> nat)set \<Rightarrow> 'f af \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" 
  where "ur_P_closed_af R ur us \<pi> P  \<equiv> \<forall> st \<in> P. ur_closed_term_af R ur us \<pi> (snd st)"  

notation Ground_Context.equiv_class ("[_]")

lemma (in itrans) i_transII:
  assumes sn: "SN_on (qrelac Q R E) {t \<cdot> \<sigma>}" 
  shows "(i_trans (t \<cdot> \<sigma>), t \<cdot> i_trans_subst \<sigma>) \<in> (rstep (ce_trs cn))^*
  \<and> (funas_term t \<subseteq> us \<or> (i_trans (t \<cdot> \<sigma>), t \<cdot> i_trans_subst \<sigma>) \<in> (rstep (ce_trs cn))^+) " 
  (is "(i_trans _,_) \<in> ?rel \<and> (_ \<or> _ \<in> ?Rel)  ")
using sn
proof (induct t)
  case (Var x) then show ?case by auto
next
  case (Fun f ts)
  from \<open>SN_on (qrelac Q R E) {Fun f ts \<cdot> \<sigma>}\<close> 
  have sns: "\<And> s. s \<in> set ts \<Longrightarrow> SN_on (qrelac Q R E) {s \<cdot> \<sigma>}"
    by (simp add: SN_imp_SN_arg_gen[OF ctxt_closed_qrelac])
  let ?us = "map (\<lambda>(g, ss). Fun g (map i_trans ss)) (ac_subterms_list f (map (\<lambda>t. t \<cdot> \<sigma>) ts))"
  let ?ts = "map (\<lambda> t. i_trans (t \<cdot> \<sigma>)) ts"
  let ?ss = "map (\<lambda> t. t \<cdot> i_trans_subst \<sigma>) ts"
  have len: "length ?ts = length ?ss" and other: "\<forall> i. i< length ?ts \<longrightarrow> (?ts ! i, ?ss ! i) \<in> ?rel" using sns Fun  by auto
  have "(Fun f ?ts, Fun f ?ss) \<in> ?rel"
    by (rule all_ctxt_closedD[of UNIV], insert len other, auto)
  then have nearlyDone: "(Fun f ?ts, Fun f ts \<cdot> i_trans_subst \<sigma>) \<in> ?rel" (is "(_,?ti) \<in> _") by auto
  show ?case
  proof (cases "i_trans_check (Fun f ts \<cdot> \<sigma>)")
    case False
    with Fun have id: "i_trans (Fun f ts \<cdot> \<sigma>) = 
       (comb cn) (?us @ map i_trans (qr_successors (Fun f ts \<cdot> \<sigma>)))" (is "?it = (comb cn) ?list") 
      by (simp add: o_def) 
    have "Fun f ?ts \<in> set ?us" using ac_subterms_list_id[of f "map (\<lambda>t. t \<cdot> \<sigma>) ts"]
      by force
    then have "Fun f ?ts \<in> set ?list" by auto
    then have steps: "((comb cn) ?list, Fun f ?ts) \<in> (rstep (ce_trs cn))^+" (is "_ \<in> ?r^+") by (rule ce_trs_sound) 
    from nearlyDone steps have steps: "(i_trans (Fun f ts \<cdot> \<sigma>), ?ti) \<in> ?r^+" unfolding id by auto
    show ?thesis using steps by auto
  next
    case True
    with Fun nearlyDone have part1: "(i_trans (Fun f ts \<cdot> \<sigma>), Fun f ts \<cdot> i_trans_subst \<sigma>) \<in> ?rel"
      by (simp add: o_def) 
    let ?fus = "funas_term (Fun f ts) \<subseteq> us"
    show ?thesis 
    proof (intro conjI, rule part1, unfold disj_commute[of ?fus], rule disjCI)
      assume not: "\<not> ?fus"
      with Fun True have id: "i_trans (Fun f ts \<cdot> \<sigma>) = Fun f ?ts" by simp 
      from True have fus: "(f,length ts) \<in> us" by (simp add: i_trans_check.simps)
      with not have "\<exists> t. t \<in> set ts \<and> \<not> funas_term t \<subseteq> us" by auto
      then obtain t where t: "t \<in> set ts" and tus: "\<not> funas_term t \<subseteq> us" by blast
      from t obtain i where i: "i < length ?ts" and ti: "t = ts ! i" by (simp only: set_conv_nth, auto)
      from Fun(1)[OF t _] sns t ti tus have "(i_trans (ts ! i \<cdot> \<sigma>), ts ! i \<cdot> i_trans_subst \<sigma>) \<in> ?Rel" by auto   
      with i have ind: "(?ts ! i, ?ss ! i) \<in> ?Rel" by auto
      have "(Fun f ?ts, Fun f ?ss) \<in> ?Rel" 
        by (rule rtrancl_trancl_into_trancl[OF len other i ind ctxt_closed_rstep])
      with id show "(i_trans (Fun f ts \<cdot> \<sigma>), Fun f ts \<cdot> i_trans_subst \<sigma>) \<in> ?Rel" by auto
    qed
  qed
qed

lemma (in itrans) i_transIV_R: assumes 
  sn: "SN_on (qrelac Q R E) {Fun f ts}" and
  step: "(Fun f ts,s) \<in> qrelac Q R E" and
  ur: "\<not> i_trans_check (Fun f ts)" 
  shows "(i_trans (Fun f ts), i_trans s) \<in> (rstep (ce_trs cn))^+" (is "_ \<in> ?rel")
proof -
  let ?I = "i_trans"
  from ur sn obtain xs where id: "?I (Fun f ts) = (comb cn) 
    (xs @ map ?I (qr_successors (Fun f ts)))" (is "_ = (comb cn) ?list") 
    by auto
  then have "?I s \<in> set ?list" using qr_successors[OF sn] using step by simp
  then have "(comb cn ?list, ?I s) \<in> ?rel" by (rule ce_trs_sound)
  with id show ?thesis by simp
qed

lemma tcap_ac_rule_GCHole: assumes lr: "(Fun f [l1,l2],r) \<in> R"
  shows "funas_term t \<subseteq> {(f,2)} \<Longrightarrow> tcap R t = GCHole"
  by (induct t rule: bterm_induct, auto simp: Let_def intro!: bexI[OF _ lr] 
    simp: less_Suc_eq Ground_Context.match_def)

lemma (in itrans) i_transIV_AC: assumes 
  sn: "SN_on (qrelac Q R E) {Fun f ts}" and
  ac: "(Fun f ts,s) \<in> (rstep E)^*" and
  ur: "\<not> i_trans_check (Fun f ts)" and
  ur_closed: "ur_closed_af RE ur us \<pi>" and
  RE: "RE = R \<union> E"
  shows "i_trans (Fun f ts) = i_trans s" 
proof -
  from ac have step: "\<And> A. (Fun f ts, s) \<in> (A \<union> (rstep E))^*" by regexp
  have sn': "SN_on (qrelac Q R E) {s}" using sn
    unfolding qrelac_def
    by (rule steps_preserve_SN_on_relto[OF step])
  let ?I = "i_trans"
  note root = root_preservation[OF ac]
  from root obtain ss where s: "s = Fun f ss" by (cases s, auto)
  note root = root[unfolded s]
  from root have len: "length ts = length ss" by simp
  note ac = ac[unfolded s]
  let ?f = "(f,length ss)"
  from ur[unfolded i_trans_check.simps, simplified]
  have ur': "\<not> i_trans_check (Fun f ss)"
  proof (cases "?f \<in> us")
    case False
    then show ?thesis unfolding i_trans_check.simps by auto
  next
    case True
    with ur[unfolded i_trans_check.simps] len obtain l r where
      lr: "(l,r) \<in> RE - ur" and match: "match_tcap_below l RE (Fun f ts)" by auto
    from sym_step[OF ac] have steps: "(Fun f ss, Fun f ts) \<in> (rstep E)\<^sup>*" .
    from qrsteps_rqrstep_cases_nrqrstep[of f ss "Fun f ts" False "{}", unfolded qrstep_rstep_conv, OF steps]
    have cases: "(\<forall>i<length ss. (ss ! i, ts ! i) \<in> (rstep E)\<^sup>*) \<or> 
      (Fun f ss, Fun f ts) \<in> (nrrstep E)\<^sup>* O rrstep E O (rstep E)\<^sup>*" (is "?A \<or> ?B") by auto    
    show ?thesis
    proof (cases ?A)
      case False
      with cases have ?B by auto
      then obtain u v where su: "(Fun f ss, u) \<in> (nrrstep E)^*" and uv: "(u,v) \<in> rrstep E" by auto
      from rrstepE[OF uv] obtain l' r' \<sigma> where lr': "(l',r') \<in> E" and u: "u = l' \<cdot> \<sigma>" .
      note nrr_steps = nrrsteps_imp_eq_root_arg_rsteps[OF su, unfolded u] 
      from nrr_steps have rt: "root (l' \<cdot> \<sigma>) = Some (f,length ss)" by auto
      with ruleD(3)[OF lr'] obtain l1 l2 r1 r2 where
        cases: "l' = Fun f [l1,l2]" "r' = Fun f [r1,r2]" and 
        args: "\<Union>(funas_term ` {l1, l2, r1, r2}) \<subseteq> {(f, 2)}"
        by auto
      then have l': "is_Fun l'" by auto
      from su have "(Fun f ss, u) \<in> (nrrstep RE)^*" unfolding RE nrrstep_union by regexp
      from match_tcap_below[OF this[unfolded u] l'] 
      have match': "match_tcap_below l' RE (Fun f ss)" .
      from cases rt have lenss: "length ss = 2" by auto
      from lenss obtain s1 s2 where ss: "ss = [s1, s2]" by (cases ss; cases "tl ss", auto)
      from nrr_steps[unfolded ss] 
      have nrr_steps: "(s1, l' \<cdot> \<sigma> |_ [0]) \<in> (rstep E)^*" "(s2, l' \<cdot> \<sigma> |_ [1]) \<in> (rstep E)^*" by auto
      from cases obtain ll1 ll2 rr1 rr2 where l': "l' = Fun f [ll1,ll2]" and r': "r' = Fun f [rr1,rr2]" by auto
      have lr'': "(l',r') \<in> RE" using lr' unfolding RE by auto
      from tcap_ac_rule_GCHole[OF lr''[unfolded cases]] args
      have tcapr: "tcap RE rr1 = GCHole" "tcap RE rr2 = GCHole" using cases[unfolded r'] by auto
      show ?thesis 
      proof (cases "(l',r') \<in> ur")
        case False
        then show ?thesis using lr' match' RE unfolding i_trans_check.simps by auto
      next
        case True
        with ur_closed have ur: "ur_closed_term_af RE ur us \<pi> r'" by blast
        have match: "match_tcap_below l RE r'"
        proof (cases l)
          case (Var z)
          show ?thesis unfolding Var r'
            by (auto simp: Ground_Context.match_def less_Suc_eq tcap_refl intro!: exI[of _ "\<lambda> _. Fun f [rr1,rr2]"])
        next
          case (Fun g ls)
          from match[unfolded Fun] len have "g = f" "length ls = length ss" 
            by (auto simp: Ground_Context.match_def)
          with ss obtain l1 l2 where l: "l = Fun f [l1,l2]" unfolding Fun 
            by (cases ls; cases "tl ls"; auto)
          show ?thesis unfolding l r'
            by (auto simp: Ground_Context.match_def less_Suc_eq tcapr)
        qed
        with ur lr cases have False by auto
        then show ?thesis ..
      qed
    next
      case True
      {
        fix i
        assume "i < length ss"
        then have "(ss ! i, ts ! i) \<in> (rstep E)\<^sup>*" using True by simp
        then have "(ss ! i, ts ! i) \<in> (rstep RE)\<^sup>*" unfolding RE rstep_union by regexp
        from tcap_rewrites[OF this] have "[tcap RE (ts ! i)] \<subseteq> [tcap RE (ss ! i)]" .
      }
      with len have "[tcap_below RE f ts] \<subseteq> [tcap_below RE f ss]" by auto
      with match have "match_tcap_below l RE (Fun f ss)" unfolding match_tcap_below.simps Ground_Context.match_def
        by auto
      with lr
      show ?thesis unfolding i_trans_check.simps by auto
    qed
  qed
  let ?xs = "map (\<lambda>(g, ss). Fun g (map i_trans ss)) (ac_subterms_list f ts)"
  let ?xs' = "map (\<lambda>(g, ss). Fun g (map i_trans ss)) (ac_subterms_list f ss)"
  let ?ys = "map ?I (qr_successors (Fun f ts))"
  let ?ys' = "map ?I (qr_successors (Fun f ss))"
  from ur sn have id: "?I (Fun f ts) = (comb cn) (?xs @ ?ys)" by auto
  also have "ac_subterms_list f ts = ac_subterms_list f ss"
  proof -
    have "ac_equiv_list (Fun f ts) = ac_equiv_list (Fun f ss)" 
      using ACEQ_identities[OF ac] by simp
    then show ?thesis unfolding ac_subterms_list_def by simp
  qed
  also have "qr_successors (Fun f ts) = qr_successors (Fun f ss)"
    unfolding qr_successors_def ACEQ_qrelac[OF ac] by simp
  also have "(comb cn) (?xs' @ ?ys') = ?I (Fun f ss)"
    using ur' sn' s by auto
  finally show ?thesis using id s by simp
qed


context ce_redpair
begin

definition c :: "'a" where "c \<equiv> undefined"
definition n :: nat where "n \<equiv> SOME n. \<forall> m. m \<ge> n \<longrightarrow> (\<forall> c.  ce_trs (c,m) \<subseteq> NS)"

lemma NS_ce_compat_n: "m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> NS"
proof -
  assume m: "n \<le> m"
  from mp[OF spec[OF someI_ex[OF NS_ce_compat[unfolded ce_compatible_def]]] 
      m[unfolded n_def]] show "ce_trs (c,m) \<subseteq> NS" by blast
qed

lemma ce_orient: "m \<ge> n \<Longrightarrow> (rstep (ce_trs (c,m)))^* \<subseteq> NS^*"
  by (rule rtrancl_mono, rule rstep_subset, rule ctxt_NS, rule subst_NS, rule NS_ce_compat_n, simp)

abbreviation mono where "mono m \<equiv> ctxt.closed S \<and> ce_trs (c,m) \<subseteq> S"
abbreviation "monoNS \<equiv> (NS \<union> S)^*"
abbreviation "monoS \<equiv> monoNS O S O monoNS"

abbreviation Snwf where "Snwf us \<equiv> S \<union> {lr | lr. \<not> funas_term (fst lr) \<subseteq> us}"

lemma mono_ce: assumes m: "mono m"   
  shows "rstep (ce_trs (c,m)) \<subseteq> S"
  by (rule rstep_subset, insert m, auto simp: subst_S)

definition mode_cond where "mode_cond mmode m \<equiv> mmode \<longrightarrow> mono m"
definition mode_left where "mode_left mmode \<equiv> if mmode then NS \<union> S else NS"
definition mode_NS where "mode_NS mmode \<equiv> if mmode then monoNS else NS^*"

lemma mode_cond_left: "mode_cond mmode m \<Longrightarrow> ctxt.closed (mode_left mmode) \<and> subst.closed (mode_left mmode)"
  by (cases mmode,
    auto simp: mode_cond_def mode_left_def subst_S subst_NS ctxt_NS intro: mono_NSS)

lemma mode_left_NS: "mode_left mode \<subseteq> mode_NS mode"
  unfolding mode_left_def mode_NS_def
  by (cases mode, auto)

lemma mode_NS_mode[simp]: "NS^* O mode_NS mode = mode_NS mode"
proof (cases mode)
  case False then show ?thesis unfolding mode_left_def mode_NS_def by auto
next
  case True 
  then have id: "mode = True" by simp
  show ?thesis unfolding mode_left_def mode_NS_def id
    by (simp, regexp)
qed

lemma mode_mode_NS[simp]: "mode_NS mode O NS^* = mode_NS mode"
proof (cases mode)
  case False then show ?thesis unfolding mode_left_def mode_NS_def by auto
next
  case True 
  then have id: "mode = True" by simp
  show ?thesis unfolding mode_left_def mode_NS_def id
    by (simp, regexp)
qed
end
 
context ce_af_redpair
begin

context
  fixes R E RE :: "('f,'v)trs"
  assumes fin_R: "finite R" and RE: "RE = R \<union> E"
  and sym_E: "symmetric_trs E"
  and AC_E: "AC_theory E"
begin
lemma itrans: "itrans R E" using AC_E sym_E fin_R unfolding itrans_def by auto

lemma i_transI:
  assumes ur: "ur_closed_term_af RE ur us \<pi> t"
    and sn: "SN_on (qrelac Q R E) {t \<cdot> \<sigma>}"
  shows "(t \<cdot> (itrans.i_trans_subst Q R RE E ur us com \<sigma>), itrans.i_trans Q R RE E ur us com (t \<cdot> \<sigma>)) \<in> NS^*"
proof -
  interpret itrans Q R RE E ur us com by (rule itrans) 
  from assms show ?thesis 
  proof (induct t)
    case (Fun f ts)  
    then have sClosed: "\<And> i. i < length ts \<and> i \<in> \<pi> (f, (length ts)) \<Longrightarrow> ur_closed_term_af RE ur us \<pi> (ts ! i)" by auto
    from \<open>SN_on (qrelac Q R E) {Fun f ts \<cdot> \<sigma>}\<close> have sns: "\<And> s. s \<in> set ts \<Longrightarrow> SN_on (qrelac Q R E) {s \<cdot> \<sigma>}"
      by (simp add: SN_imp_SN_arg_gen[OF ctxt_closed_qrelac])
    have "i_trans (Fun f ts \<cdot> \<sigma>)
         = i_trans (Fun f (map (\<lambda> t. t \<cdot> \<sigma>) ts))" (is "?l = _") by auto
    also have "\<dots> = Fun f (map i_trans (map (\<lambda> t. t \<cdot> \<sigma>) ts))"
    proof -
      from Fun(2)
      have inst: "\<forall> (l,r) \<in> RE. match_tcap_below l RE (Fun f ts) \<longrightarrow> (l,r) \<in> ur" 
        and us: "(f, length ts) \<in> us" by auto
      have "i_trans_check (Fun f ts \<cdot> \<sigma>)" (is ?check)
      proof (rule ccontr)
        assume "\<not> ?check"
        from this us obtain l r \<delta> where nUsable: "(l,r) \<in> RE - ur" 
          and elem: "l \<cdot> \<delta> \<in> [GCFun f (map (\<lambda> t. tcap RE (t \<cdot> \<sigma>)) ts)]" (is "_ \<in> ?hs")
          by (auto simp:i_trans_check.simps Ground_Context.match_def)
        have "\<And> t. [tcap RE (t \<cdot> \<sigma>)] \<subseteq> [tcap RE t]" by (rule tcap_instance_subset)
        then have "?hs \<subseteq> [GCFun f (map (tcap RE) ts)]" (is "_ \<subseteq> [?h]") by auto
        with elem have "l \<cdot> \<delta> \<in> [?h]" by auto
        then have "Ground_Context.match ?h l" unfolding Ground_Context.match_def by auto
        with inst nUsable show False by auto
      qed
      with Fun show ?thesis by auto
    qed
    finally have eq1: "?l = Fun f (map (\<lambda> t. i_trans (t \<cdot> \<sigma>)) ts)" (is "_ = ?r") by simp
    let ?tis = "\<lambda> t. t \<cdot> i_trans_subst \<sigma>"
    let ?its = "\<lambda> t. i_trans (t \<cdot> \<sigma>)"
    have "(Fun f (map ?tis ts), Fun f (map ?its ts)) \<in> NS^*" 
    proof -
      {
        fix i
        assume ilen: "i < length ts" and ipi: "i \<in> \<pi> (f, (length ts))"
        with sns have "ts ! i \<in> set ts" and "SN_on (qrelac Q R E) {ts ! i \<cdot> \<sigma>}" by auto
        with Fun sClosed ilen ipi have "(?tis (ts ! i), ?its (ts ! i)) \<in> NS^*" by auto
      } note ind = this
      from ctxt_NS have cc: "ctxt.closed (NS^*)" by blast
      show ?thesis 
      proof (rule af_steps_imp_orient, rule trans_rtrancl, rule refl_rtrancl, rule cc, force)
        show "\<forall>i<length (map ?tis ts). i \<in> \<pi> (f, (length ts)) \<longrightarrow> (map ?tis ts ! i, map ?its ts ! i) \<in> NS^*"
          using ind by auto
        show "\<forall>bef s t aft. length (map ?tis ts) = Suc (length bef + length aft) \<longrightarrow> length bef \<in> \<pi> (f, (length ts)) \<or> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS\<^sup>*"
          using af_compat unfolding af_compatible_def by force
      qed
    qed
    also have "Fun f (map ?tis ts) = Fun f ts \<cdot> i_trans_subst \<sigma>" by auto
    finally show ?case using eq1 by auto
  qed simp
qed
      
lemma SN_ac_preservation: assumes st: "(s,t) \<in> qrstep False Q R \<union> rstep E"
  and SN: "SN_on (qrelac Q R E) {s}"
  shows "SN_on (qrelac Q R E) {t}"
  by (rule step_preserves_SN_on_relto[OF _ SN[unfolded qrelac_def], of t, folded qrelac_def],
  insert st, auto)

lemma SN_ac_preservation_steps: assumes SN: "SN_on (qrelac Q R E) {t}" 
  shows "(t,s) \<in> (qrstep False Q R \<union> rstep E)^* \<Longrightarrow> SN_on (qrelac Q R E) {s}"
proof (induct rule: rtrancl_induct)
  case (step s r)
  from SN_ac_preservation[OF step(2-3)]
  show ?case by auto
qed (rule SN)

lemma i_transIII: assumes 
  mode: "mode_cond mode m" and
  m: "m \<ge> n" and
  sn: "SN_on (qrelac Q R E) {Fun f ts}" and
  choice: "lr \<in> R \<and> Q' = Q \<or> lr \<in> E \<and> Q' = {}" and
  step: "(Fun f ts,s) \<in> rqrstep False Q' {lr}" and
  ur: "itrans.i_trans_check RE ur us (Fun f ts)" and
  ur_closed: "ur_closed_af RE ur us \<pi>" and
  orient: "ur \<subseteq> mode_left mode"
  shows "((itrans.i_trans Q R RE E ur us (c,m) (Fun f ts), itrans.i_trans Q R RE E ur us (c,m) s) \<in> mode_NS mode) \<and> 
    (mode \<and> lr \<in> Snwf us \<longrightarrow>  (itrans.i_trans Q R RE E ur us (c,m) (Fun f ts), itrans.i_trans Q R RE E ur us (c,m) s) \<in> monoS) \<and> lr \<in> ur"
proof -
  from step choice have rule: "lr \<in> RE" unfolding RE by auto
  let ?cn = "(c,m)"
  let ?QR = "qrelac Q R E"
  interpret itrans Q R RE E ur us ?cn by (rule itrans)
  let ?I = "i_trans"
  obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
  note rule = rule[unfolded lr]
  from step[unfolded lr rqrstep_def] obtain \<sigma> where left: "l \<cdot> \<sigma> = Fun f ts" and right: "r \<cdot> \<sigma> = s" by auto
  let ?Is = "i_trans_subst \<sigma>"
  {
    assume "is_Var l"
    with no_left_var[of _ r] lr step choice obtain x where "(Var x, r) \<in> R" unfolding RE by (cases l, auto)
    then have "\<not> (SN_on (qrstep False Q R) {Fun f ts})" 
      by (rule left_Var_imp_not_SN_qrstep, auto)
    with SN_on_mono[OF _ qrstep_subset_qrelac, of Q R E "{Fun f ts}"]
    have False using sn by auto
  }
  then obtain g ss where l: "l = Fun g ss" by (cases l, auto)
  from ur have nmatch: "\<forall> (l,r) \<in> RE - ur. \<not> match_tcap_below l RE (Fun f ts)" by (simp only: i_trans_check.simps, blast)
  from l left have fg: "f = g" and tsss: "ts = map (\<lambda> s. s \<cdot> \<sigma>) ss" (is "_ = ?ts") and nvar: "\<not> (is_Var l)" by auto
  have "match_tcap_below (Fun f ss) RE (Fun f ss \<cdot> \<sigma>)"
    by (rule match_tcap_below, auto)
  with l fg tsss rule nmatch have urule: "(l, r) \<in> ur" by auto
  with left and right 
    have urStep: "(Fun f ts, s) \<in> rstep ur" by (auto) (metis rstep_rule rstep_subst)
  from urule ur_closed have fr: "ur_closed_term_af RE ur us \<pi> r" by auto
  from left sn have snl: "SN_on ?QR {l \<cdot> \<sigma>}" by auto
  from i_transII[OF snl] left have oneB: "funas_term (fst lr) \<subseteq> us \<or> (?I (Fun f ts), l \<cdot> ?Is) \<in> (rstep (ce_trs ?cn))^+" unfolding lr by auto
  from i_transII[OF snl] ce_orient[OF m] have "(?I (l \<cdot> \<sigma>), l \<cdot> ?Is) \<in> NS^*" by blast
  with left have one: "(?I (Fun f ts), l \<cdot> ?Is) \<in> NS^*" by auto
  from choice step have "(Fun f ts, s) \<in> rqrstep False Q R \<union> rqrstep False {} E" unfolding rqrstep_def
    by (cases, blast+)
  then have "(Fun f ts, s) \<in> qrstep False Q R \<union> qrstep False {} E" unfolding qrstep_iff_rqrstep_or_nrqrstep  by auto
  then have "(Fun f ts, s) \<in> qrstep False Q R \<union> rstep E" by auto
  from SN_ac_preservation[OF this sn] have sns: "SN_on ?QR {r \<cdot> \<sigma>}" unfolding right .
  have "(r \<cdot> ?Is , ?I (r \<cdot> \<sigma>)) \<in> NS^*"  by (rule i_transI[OF fr sns])
  with right have stepRight: "(r \<cdot> ?Is, ?I s) \<in> NS^*" by auto
  from urule have urstep: "(l \<cdot> ?Is, r \<cdot> ?Is) \<in> rstep ur" by auto
  with rstep_subset[OF _ _ orient] mode_cond_left[OF mode] have lstep: "(l \<cdot> ?Is, r \<cdot> ?Is) \<in> mode_left mode" by auto
  with mode_left_NS have rstep: "(l \<cdot> ?Is, r \<cdot> ?Is) \<in> mode_NS mode" by auto
  with stepRight have two: "(l \<cdot> ?Is, ?I s) \<in> mode_NS mode O NS^*" by blast
  from one two have "(?I (Fun f ts), ?I s) \<in> NS^* O mode_NS mode O NS^*" by blast
  then have part1: "(?I (Fun f ts), ?I s) \<in> mode_NS mode" by simp
  show ?thesis
  proof (intro conjI impI, rule part1, unfold lr, erule conjE)
    show "(l,r) \<in> ur" by (rule urule)
  next
    assume mono: mode and S: "(l,r) \<in> Snwf us"
    from S have "(l,r) \<in> S \<or> \<not> funas_term l \<subseteq> us" by auto
    then have "(?I (Fun f ts), r \<cdot> ?Is) \<in> monoS"
    proof
      assume "(l,r) \<in> S"
      with subst_S have "(l \<cdot> ?Is, r \<cdot> ?Is) \<in> S" unfolding subst.closed_def by auto
      moreover have "(?I (Fun f ts), l \<cdot> ?Is) \<in> monoNS" using one rtrancl_mono by blast
      ultimately show ?thesis by auto
    next
      assume "\<not> funas_term l \<subseteq> us"
      with oneB have steps: "(?I (Fun f ts), l \<cdot> ?Is) \<in> (rstep (ce_trs ?cn))^+" unfolding lr by auto
      from mode[unfolded mode_cond_def] \<open>mode\<close> 
        trancl_mono[OF steps mono_ce]
      have "(?I (Fun f ts), l \<cdot> ?Is) \<in> S^+" by auto
      moreover have "(l \<cdot> ?Is, r \<cdot> ?Is) \<in> subst.closure (NS \<union> S)" using S urule orient \<open>mode\<close> unfolding mode_left_def by auto
      then have "(l \<cdot> ?Is, r \<cdot> ?Is) \<in> NS \<union> S" using subst_NS subst_S unfolding subst.closure_Un subst.closed_def by force
      ultimately have "(?I (Fun f ts), r \<cdot> ?Is) \<in> S^+ O (NS \<union> S)" by auto
      moreover have "S^+ O (NS \<union> S) \<subseteq> monoS" by regexp
      ultimately show ?thesis by blast
    qed
    with stepRight have "(?I (Fun f ts), ?I s) \<in> monoS O NS^*" by blast
    moreover have "monoS O NS^* \<subseteq> monoS" by regexp
    ultimately show "(?I (Fun f ts), ?I s) \<in> monoS" by blast
  qed
qed

lemma mode_NS: "NS^* \<subseteq> mode_NS mode"
  unfolding mode_NS_def
  by (cases mode, insert rtrancl_mono[of NS], auto)

lemma mode_NS_ctxt: "mode_cond mode m \<Longrightarrow> ctxt.closed (mode_NS mode)"
proof (cases mode)
  case False then show ?thesis unfolding mode_NS_def using ctxt_NS by auto 
next
  case True
  assume "mode_cond mode m"
  then have "ctxt.closed S" unfolding mode_cond_def using True by auto
  from mono_NSS[OF this] show ?thesis unfolding mode_NS_def using True by auto 
qed

lemma mode_S_ctxt: "mode \<Longrightarrow> mode_cond mode m \<Longrightarrow> ctxt.closed monoS"
proof -
  assume m: mode and c: "mode_cond mode m"
  from mode_NS_ctxt[OF c] have NS: "ctxt.closed monoNS" unfolding mode_NS_def
    using m by auto
  from c m have S: "ctxt.closed S" unfolding mode_cond_def by auto
  from S NS show ?thesis by blast
qed

lemma mode_ce: "mode \<Longrightarrow> mode_cond mode m \<Longrightarrow> (rstep (ce_trs (c,m)))^+ \<subseteq> monoS"
proof -
  assume mode and mode: "mode_cond mode m"
  with mode have "mono m" unfolding mode_cond_def by auto
  from trancl_mono[OF _ mono_ce[OF this]] have "(rstep (ce_trs (c,m)))^+ \<subseteq> S^+" by auto
  moreover have "S^+ \<subseteq> monoS" by regexp
  ultimately show ?thesis by auto
qed

lemma i_transV: 
  assumes 
  mode: "mode_cond mode m" and
  m: "m \<ge> n" and
  choice: "lr \<in> R \<and> Q' = Q \<or> lr \<in> E \<and> Q' = {}" and
  sn: "SN_on (qrelac Q R E) {t}" and
  step: "(t,s) \<in> qrstep False Q' {lr}" and
  ur_closed: "ur_closed_af RE ur us \<pi>" and
  orient: "ur \<subseteq> mode_left mode" 
  shows "(itrans.i_trans Q R RE E ur us (c,m) t, itrans.i_trans Q R RE E ur us (c,m) s) \<in> mode_NS mode \<and> 
  (mode \<and> lr \<in> R \<and> Q' = Q \<and> (lr \<notin> ur \<or> lr \<in> Snwf us) 
  \<longrightarrow> (itrans.i_trans Q R RE E ur us (c,m) t, itrans.i_trans Q R RE E ur us (c,m) s) \<in> monoS)"
proof -
  let ?L = "mode_left mode"
  let ?R = "mode_NS mode"
  let ?cn = "(c,m)"
  let ?QR = "qrelac Q R E"
  interpret itrans Q R RE E ur us ?cn by (rule itrans)
  let ?I = "i_trans"
  let ?cond = "mode \<and> lr \<in> R \<and> Q' = Q \<and> (lr \<notin> ur \<or> lr \<in> Snwf us)"
  let ?goal = "\<lambda> t s. 
    (?I t, ?I s) \<in> ?R \<and> 
  (?cond \<longrightarrow> (?I t, ?I s) \<in> monoS)"
  from step choice have rule: "lr \<in> RE" unfolding RE by auto
  from step sn show "?goal t s"
  proof induct 
    case (IH C \<sigma> l r)
    with choice rule have lr: "lr = (l,r)" and IH2: "(l,r) \<in> RE" 
      and choice: "(l,r) \<in> R \<and> Q' = Q \<or> (l,r) \<in> E \<and> Q' = {}" by auto
    have sub: "\<And> x. x \<in> qrstep False Q' {(l,r)} \<Longrightarrow> x \<in> qrstep False Q R \<union> rstep E" using choice 
      by (cases, auto)
    from IH(4)
    show ?case
    proof (induct C)
      case Hole
      let ?ls = "\<box>\<langle>l \<cdot> \<sigma>\<rangle>" 
      let ?rs = "\<box>\<langle>r \<cdot> \<sigma>\<rangle>" 
      {
        assume "is_Var ?ls"
        then obtain x where "?ls = Var x" by (cases ?ls, auto)
        then obtain x where l: "l = Var x" by (cases l, auto)
        with choice no_left_var lr have "(l,r) \<in> R" by auto
        from left_Var_imp_not_SN_qrstep[OF this[unfolded l], of False] IH(4)
          SN_on_mono[OF _ qrstep_subset_qrelac, of Q R E]
        have False by auto
      }
      then have "\<not> (is_Var ?ls)" ..
      from this obtain f ls where ls: "?ls = Fun f ls" by (cases ?ls, auto)
      from IH(3) Hole ls have snls: "SN_on ?QR {Fun f ls}" by auto
      from rqrstepI[OF IH(1-2) _ _ IH(3)] ls have rstep: "(Fun f ls, ?rs) \<in> rqrstep False Q' {(l,r)}"
        unfolding lr by auto
      then have step: "(Fun f ls, ?rs) \<in> qrstep False Q' {(l,r)}" unfolding qrstep_iff_rqrstep_or_nrqrstep by blast
      show "?goal ?ls ?rs"
      proof (cases "i_trans_check (Fun f ls)")
        case True
        from i_transIII[OF mode m snls choice rstep True ur_closed orient]
        show ?thesis using IH2 unfolding ls lr by blast
      next
        case False note check = this
        from choice
        show ?thesis
        proof (cases "(l,r) \<in> R \<and> Q' = Q")
          case True
          with qrstep_mono[of "{(l,r)}" R Q _ False, OF _ subset_refl] step
          have "(Fun f ls, ?rs) \<in> qrstep False Q R" by auto
          from snls set_mp[OF qrstep_subset_qrelac this] check
          have steps: "(?I ?ls, ?I ?rs) \<in> (rstep (ce_trs ?cn))^+" unfolding ls by (rule i_transIV_R)
          from steps ce_orient[OF m] have "(?I ?ls, ?I ?rs) \<in> NS^*" by auto
          then have piece0:"(?I ?ls, ?I ?rs) \<in> mode_NS mode" using mode_NS by blast
          show ?thesis 
            by (intro conjI[OF piece0] impI, elim conjE, insert steps mode_ce[OF _ mode], auto)
        next
          case False
          with choice have "(l,r) \<in> E \<and> Q' = {}" by auto
          with step have "(Fun f ls, ?rs) \<in> rstep E" by auto
          then have "(Fun f ls, ?rs) \<in> (rstep E)\<^sup>*" by regexp
          from i_transIV_AC[OF snls this check ur_closed RE] ls have "(?I ?ls, ?I ?rs) \<in> NS^*" by auto
          then have piece0:"(?I ?ls, ?I ?rs) \<in> mode_NS mode" using mode_NS by blast
          with False IH show ?thesis using ls by auto
        qed
      qed
    next
      case (More f bef D aft)
      obtain t s where t: "t = l \<cdot> \<sigma>" and s: "s = r \<cdot> \<sigma>" by auto
      from More
      have snbta: "SN_on ?QR {Fun f (bef @ D\<langle>t\<rangle> # aft)}" (is "SN_on _ {Fun f ?bta}") 
        unfolding t by auto
      let ?Dt = "D\<langle>t\<rangle>"
      let ?Ds = "D\<langle>s\<rangle>"
      let ?bsa = "bef @ ?Ds # aft"
      let ?C = "More f bef D aft"
      have step: "(Fun f ?bta, Fun f ?bsa) \<in> qrstep False Q' {(l,r)}" 
        unfolding s t
        by (rule qrstepI[OF IH(1) _ _ _ IH(3), of _ _ ?C], auto)
      show ?case 
      proof (cases "i_trans_check (Fun f ?bta)")
        case False note check = this
        let ?l = "Fun f ?bta"
        let ?r = "Fun f ?bsa"
        show ?thesis
        proof (cases "(l,r) \<in> R \<and> Q' = Q")
          case True
          with qrstep_mono[of "{(l,r)}" R Q _ False, OF _ subset_refl] step
          have "(?l, ?r) \<in> qrstep False Q R" by auto
          from snbta set_mp[OF qrstep_subset_qrelac this] check
          have steps: "(?I ?l, ?I ?r) \<in> (rstep (ce_trs ?cn))^+" 
            by (rule i_transIV_R)
          from steps ce_orient[OF m] have "(?I ?l, ?I ?r) \<in> NS^*" by auto
          then have piece0: "(?I ?l, ?I ?r) \<in> mode_NS mode" using mode_NS by blast
          show ?thesis unfolding s[symmetric] t[symmetric]
            by (rule conjI, insert piece0, simp, intro impI, elim conjE, insert steps mode_ce[OF _ mode], auto)
        next
          case False
          with choice have "(l,r) \<in> E \<and> Q' = {}" by auto
          with step have "(?l,?r) \<in> rstep E" by auto
          then have "(?l, ?r) \<in> (rstep E)\<^sup>*" by regexp
          from i_transIV_AC[OF snbta this check ur_closed RE] have "(?I ?l, ?I ?r) \<in> NS^*" by auto
          then have piece0:"(?I ?l, ?I ?r) \<in> mode_NS mode" using mode_NS by blast
          with False IH show ?thesis unfolding s[symmetric] t[symmetric] by auto
        qed
      next
        case True
        then have fus: "(f, Suc (length bef + length aft)) \<in> us" by (simp add: i_trans_check.simps)
        have "?Dt \<in> set ?bta" by auto 
        with snbta have "SN_on ?QR {?Dt}" by (rule SN_imp_SN_arg_gen[OF ctxt_closed_qrelac])
        with More have "?goal ?Dt ?Ds" unfolding s t by auto
        then have always: "(?I ?Dt, ?I ?Ds) \<in> ?R" and choice: "?cond \<longrightarrow> (?I ?Dt, ?I ?Ds) \<in> monoS" by auto
        from ctxt_closed_one[OF mode_NS_ctxt[OF mode] always]
        have piece0: "(Fun f (map ?I bef @ ?I ?Dt # map ?I aft), 
          Fun f (map ?I bef @ ?I ?Ds # map ?I aft)) \<in> ?R" (is "(?Il, ?Ir) \<in> _") .         
        from choice have choice: "?cond \<longrightarrow> (?Il, ?Ir) \<in> monoS" using ctxt_closed_one[OF mode_S_ctxt[OF _ mode]] by blast
        from True snbta have left: "?I (Fun f ?bta) = ?Il" by auto
        have snbsa: "SN_on ?QR {Fun f ?bsa}" by (rule SN_ac_preservation[OF sub[OF step] snbta])
        from IH2 ctxt.closure.intros[where a = D] have "(?Dt,?Ds) \<in> rstep RE"
          unfolding rstep_eq_closure s t RE by auto
        then have subset: "[tcap RE ?Ds] \<subseteq> [tcap RE ?Dt]" by (rule tcap_rewrite)		
        have "i_trans_check (Fun f ?bsa)"
        proof (simp add: i_trans_check.simps fus, rule ballI) 
          fix lr'
          assume lr': "lr' \<in> RE - ur"
          show "\<not> (\<lambda>(l, r). Ground_Context.match (GCFun f (map (tcap RE) bef @ tcap RE ?Ds # map (tcap RE) aft)) l) lr'"
          proof (cases lr')
          case (Pair l r)
            from lr' Pair have "(l,r) \<in> RE" by auto
            from Pair lr' have nMatch: 
              "\<not> Ground_Context.match (GCFun f (map (tcap RE) bef @ tcap RE ?Dt # map (tcap RE) aft)) l" (is "\<not> Ground_Context.match ?cbta l") 
              using True by (auto simp: i_trans_check.simps)
            {
              assume "Ground_Context.match (GCFun f (map (tcap RE) bef @ tcap RE ?Ds # map (tcap RE) aft)) l" 
              from this subset have "Ground_Context.match ?cbta l" by (rule match_below)
              with nMatch have False ..
            }
            with lr' Pair show ?thesis by auto 
          qed
        qed
        with snbsa  have "?I (Fun f ?bsa) = ?Ir" by auto	
        with left piece0 choice show ?thesis unfolding s t by (simp)
      qed
    qed
  qed
qed


lemma i_transVI: assumes 
  mode: "mode_cond mode m" and
  m: "m \<ge> n" and
  sn: "SN_on (qrelac Q R E) {t}" and
  step: "(t,s) \<in> (qrstep False Q R \<union> rstep E)^*" and
  ur_closed: "ur_closed_af RE ur us \<pi>" and
  orient: "ur \<subseteq> mode_left mode"
  shows "(itrans.i_trans Q R RE E ur us (c,m) t, itrans.i_trans Q R RE E ur us (c,m) s) \<in> mode_NS mode"
 (is "?goal t s")
using step 
proof (induct rule: rtrancl_induct)
  case base
  show ?case by (cases mode, unfold mode_NS_def, auto)
next
  case (step s u)
  let ?cn = "(c,m)"
  let ?QR = "qrelac Q R E"
  interpret itrans Q R RE E ur us ?cn by (rule itrans)
  let ?I = "i_trans"
  from step(1-2) have "(t,s) \<in> (qrstep False Q R \<union> rstep E)^*" by auto
  from SN_ac_preservation_steps[OF sn this] have sn': "SN_on (qrelac Q R E) {s}" .
  from step(2) have isteps2: "(?I s, ?I u) \<in> mode_NS mode"
  proof 
    assume "(s, u) \<in> qrstep False Q R"
    from this[unfolded qrstep_rule_conv[where R = R]] obtain lr where lr: "lr \<in> R" 
      and sustep: "(s,u) \<in> qrstep False Q {lr}" by auto
    from i_transV[OF mode m _ sn' sustep ur_closed orient] lr show ?thesis by auto
  next
    assume "(s,u) \<in> rstep E"
    from this obtain lr where lr: "lr \<in> E"
      and sustep: "(s,u) \<in> qrstep False {} {lr}" by blast
    from i_transV[OF mode m _ sn' sustep ur_closed orient] lr show ?thesis by auto
  qed
  with step(3) have "(?I t, ?I u) \<in> mode_NS mode O mode_NS mode" by auto
  then show ?case unfolding mode_NS_def by (cases mode, auto)
qed

lemma i_transVI_S: assumes 
  mode: "mode_cond mode m" and
  modeT: "mode" and
  m: "m \<ge> n" and
  sn: "SN_on (qrelac Q R E) {t}" and
  step: "(t,s) \<in> (qrstep False Q R \<union> rstep E)^* O qrstep False Q R' O (qrstep False Q R \<union> rstep E)^*" and
  ur_closed: "ur_closed_af RE ur us \<pi>" and
  orient: "ur \<subseteq> mode_left mode" and
  R': "R' \<inter> ur \<subseteq> Snwf us" and
  RR': "R' \<subseteq> R"
  shows "(itrans.i_trans Q R RE E ur us (c,m) t, itrans.i_trans Q R RE E ur us (c,m) s) \<in> monoS"
proof -
  let ?R = "qrstep False Q R \<union> rstep E"
  let ?R' = "qrstep False Q R'"
  let ?QR = "qrelac Q R E"
  from step obtain u v where tu: "(t,u) \<in> ?R^*" and uv: "(u,v) \<in> ?R'" and vs: "(v,s) \<in> ?R^*" by auto
  note itVI = i_transVI[OF mode m _ _ ur_closed orient]
  let ?cn = "(c,m)"
  let ?I = "itrans.i_trans Q R RE E ur us ?cn"
  note to_QR = set_mp[OF qrstep_subset_qrelac]
  note to_QRs = set_mp[OF rtrancl_mono[OF qrstep_subset_qrelac]]
  from itVI[OF sn tu] have one: "(?I t,?I u) \<in> mode_NS mode" .
  from SN_ac_preservation_steps[OF sn tu] have sn: "SN_on ?QR {u}" .
  from uv[unfolded qrstep_rule_conv[where R = "R'"]] obtain lr where lr: "lr \<in> R'"
    and uv: "(u,v) \<in> qrstep False Q {lr}" by auto
  with RR' R' have lr': "lr \<in> R" and uv': "(u,v) \<in> qrstep False Q R" and lr: "lr \<notin> ur \<or> lr \<in> Snwf us" 
    unfolding qrstep_rule_conv[where R = R] by auto
  from i_transV[OF mode m _ sn uv ur_closed orient] modeT lr lr'
  have two: "(?I u,?I v) \<in> monoS" by auto
  from step_preserves_SN_on[OF to_QR[OF uv'] sn] have sn: "SN_on ?QR {v}" .
  from itVI[OF sn vs] have three: "(?I v, ?I s) \<in> mode_NS mode" .
  from one two three have steps: "(?I t, ?I s) \<in> mode_NS mode O monoS O mode_NS mode" (is "_ \<in> ?Rel") by blast
  from modeT have m: "mode_NS mode = monoNS" unfolding mode_NS_def by auto
  have "?Rel \<subseteq> monoS" unfolding m by regexp
  with steps show "(?I t, ?I s) \<in> monoS" by blast
qed

lemma i_trans_strict_step: assumes 
  mode: "mode_cond mode m" and
  modeT: "mode" and
  m: "m \<ge> n" and
  sn: "SN_on (qrelac Q R E) {t \<cdot> \<sigma>}" and
  step: "(t \<cdot> \<sigma> ,s \<cdot> \<delta>) \<in> (qrstep False Q R \<union> rstep E)^* O qrstep False Q R' O (qrstep False Q R \<union> rstep E)^*" and
  ur_closed: "ur_closed_af RE ur us \<pi>" and
  ur_P_closed: "ur_P_closed_af RE ur us \<pi> P" and
  st: "(s',t) \<in> P" and
  orient: "ur \<subseteq> mode_left mode" and
  R': "R' \<inter> ur \<subseteq> Snwf us" and
  RR': "R' \<subseteq> R"  
  shows "(t \<cdot> itrans.i_trans_subst Q R RE E ur us (c,m) \<sigma>, s \<cdot> itrans.i_trans_subst Q R RE E ur us (c,m) \<delta>) \<in> monoS"
proof -
  let ?cn = "(c,m)"
  let ?QR = "qrelac Q R E"
  interpret itrans Q R RE E ur us ?cn by (rule itrans)
  let ?I = "i_trans"
  let ?\<sigma> = "i_trans_subst \<sigma>"
  let ?\<delta> = "i_trans_subst \<delta>"
  from st ur_P_closed have urt: "ur_closed_term_af RE ur us \<pi> t" by auto
  from i_transI[OF urt sn] have ns0: "(t \<cdot> ?\<sigma>, ?I (t \<cdot> \<sigma>)) \<in> NS^*" . 
  note step
  also have "(qrstep False Q R \<union> rstep E)^* O qrstep False Q R' O (qrstep False Q R \<union> rstep E)^* \<subseteq> (qrstep False Q R \<union> rstep E)^* O qrstep False Q R O (qrstep False Q R \<union> rstep E)^*"
    by (rule relto_mono[OF qrstep_mono[OF RR']], auto)
  also have "\<dots> \<subseteq> (qrstep False Q R \<union> rstep E)^*" by regexp
  finally have "(t \<cdot> \<sigma>, s \<cdot> \<delta>) \<in> (qrstep False Q R \<union> rstep E)^*" .
  from SN_ac_preservation_steps[OF sn this] have SNs: "SN_on (qrelac Q R E) {s \<cdot> \<delta>}" .
  from i_transII[OF SNs] ce_orient[OF m] have ns2: "(?I (s \<cdot> \<delta>), s \<cdot> ?\<delta>) \<in> NS^*" by auto
  from i_transVI_S[OF mode modeT m sn step ur_closed orient R' RR'] 
  have s: "(?I (t \<cdot> \<sigma>), ?I (s \<cdot> \<delta>)) \<in> monoNS O S O monoNS" .
  from ns0 this ns2 have "(t \<cdot> ?\<sigma>, s \<cdot> ?\<delta>) \<in> NS^* O monoNS O S O monoNS O NS^*" by auto
  then show "(t \<cdot> ?\<sigma>, s \<cdot> ?\<delta>) \<in> monoS" by regexp
qed
end
end

no_notation Ground_Context.equiv_class ("[_]")

lemma itrans_ac_empty: 
  "R = R \<union> {}" 
  "symmetric_trs {}"
  "AC_theory {}"
  by (auto simp: root_preserving_trs_def symbol_preserving_trs_def symmetric_trs_def AC_theory_def)

lemma (in ce_af_redpair) i_trans_sound_dp: 
  assumes
  fin_R: "finite R"
  and nfs: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R" (* required from previous lemmas *)
  and mode: "mode_cond mode m"
  and m: "m \<ge> n"
  and P: "(s,t) \<in> P"
  and steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs Q R)^*"
  and SN: "SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}"
  and ur_closed: "ur_closed_af R ur us \<pi>"
  and ur_P_closed: "ur_P_closed_af R ur us \<pi> P"
  and orient: "ur \<subseteq> mode_left mode"
  shows  "(t \<cdot> itrans.i_trans_subst Q R R {} ur us (c,m) \<sigma>, 
    u \<cdot> itrans.i_trans_subst Q R R {} ur us (c,m) \<tau>) \<in> mode_NS mode"
proof -
  let ?cn = "(c,m)"
  interpret itrans Q R R "{}" ur us ?cn by (rule itrans[OF fin_R itrans_ac_empty])
  let ?s = "s \<cdot> \<sigma>"
  let ?t = "t \<cdot> \<sigma>"
  let ?u = "u \<cdot> \<tau>"
  let ?I = "i_trans"
  let ?Is = "i_trans_subst"
  let ?ssig = "s \<cdot> ?Is \<sigma>"
  let ?tsig = "t \<cdot> ?Is \<sigma>"
  let ?utau = "u \<cdot> ?Is \<tau>"
  let ?QR = "qrelac Q R {}"
  have switch': "qrstep False Q R = ?QR" unfolding qrelac_empty_is_qrstep ..
  have switch: "qrstep nfs Q R = qrstep False Q R"
    by (rule wwf_qtrs_imp_nfs_False_switch[OF nfs])
  note steps = steps[unfolded switch]
  note SN = SN[unfolded switch]
  note SN' = SN[unfolded switch']
  from i_transVI[OF fin_R itrans_ac_empty mode m SN' _ ur_closed orient] steps
  have one: "(?I ?t, ?I ?u) \<in> mode_NS mode" by simp
  from P ur_P_closed have "ur_closed_term_af R ur us \<pi> t" by auto
  from i_transI[OF fin_R itrans_ac_empty this SN'] have two: "(?tsig, ?I ?t) \<in> NS^*" by simp
  from steps SN have sns: "SN_on (qrstep False Q R) {?u}" by (rule steps_preserve_SN_on[of _ _ "qrstep False Q R"])
  note sns' = sns[unfolded switch']
  from i_transII[OF sns', THEN conjunct1] ce_orient[OF m]
  have three: "(?I ?u, ?utau ) \<in> NS^*" by auto    
  from one two three have "(?tsig,?utau) \<in> NS^* O mode_NS mode O NS^*" by blast
  then show ?thesis by simp
qed

lemma (in mono_ce_af_redtriple) mono_redpair_ur_sound:
  assumes fin: "finite (R \<union> Rw)" 
  and rules: "ur \<subseteq> NS \<union> S"
  and nonStrict: "P \<union> Pw \<subseteq> NS \<union> S"
  and strictP: "Ps - {lr | lr. \<not> funas_term (fst lr) \<subseteq> us} \<subseteq> S"
  and strictR: "(Rs \<inter> ur) - {lr | lr. \<not> funas_term (fst lr) \<subseteq> us} \<subseteq> S"
  and ur_closed: "ur_closed_af (R \<union> Rw) ur us \<pi>"
  and ur_P_closed: "ur_P_closed_af (R \<union> Rw) ur us \<pi> (P \<union> Pw)"
  and m: m
  and nfs: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q (R \<union> Rw)"
  and minChain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows  "\<exists> j. min_ichain (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs) (shift s j) (shift t j) (shift \<sigma> j)"
proof (rule min_ichain_split[OF minChain], rule)
  {
    fix RR
    assume RR: "RR \<subseteq> R \<union> Rw"
    from RR nfs have "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q RR" unfolding wwf_qtrs_def by blast
    from wwf_qtrs_imp_nfs_False_switch[OF this] have "qrstep nfs Q RR = qrstep False Q RR" .
  } note switch_gen = this
  from switch_gen[OF subset_refl] have switch: "qrstep nfs Q (R \<union> Rw) = qrstep False Q (R \<union> Rw)" .
  assume chain: "min_ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw), R \<union> Rw - Rs) s t \<sigma>"
  then have chain: "min_ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw), R \<union> Rw - Rs) s t \<sigma>" by auto    
  have id: "Ps \<inter> (P \<union> Pw) \<union> (P \<union> Pw - Ps) = P \<union> Pw" by auto
  have idR: "Rs \<inter> (R \<union> Rw) \<union> (R \<union> Rw - Rs) = R \<union> Rw" by auto
  have idS: "S \<union> NS = NS \<union> S" by auto
  from ce_compatibleE[OF S_ce_compat] obtain n' where 
    S_compat: "\<And> m. m \<ge> n' \<Longrightarrow> ce_trs (c,m) \<subseteq> S" by metis
  obtain k where k: "k = max n n'" by auto
  then have n: "n \<le> k"  by simp
  obtain mode where mode: "mode" by blast
  from S_compat k mode have cond: "mode_cond mode k" unfolding mode_cond_def using ctxt_S by auto
  interpret itrans Q "R \<union> Rw" "R \<union> Rw" "{}" ur us "(c, k)" by (rule itrans[OF _ itrans_ac_empty], insert fin, auto)
  obtain \<tau> where \<tau>: "\<tau> = (\<lambda> i. i_trans_subst (\<sigma> i))" by auto
  from mode rules have orient: "ur \<subseteq> mode_left mode" unfolding mode_left_def by auto
  note chain = chain[unfolded min_ichain.simps ichain.simps minimal_cond_def id idR]
  {
    fix i    
    from chain \<open>m\<close> switch
    have P: "(s i, t i) \<in> P \<union> Pw" and R: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep False Q (R \<union> Rw))^*" and 
    SN: "SN_on (qrstep False Q (R \<union> Rw)) {t i \<cdot> \<sigma> i}" by auto
    from i_trans_sound_dp[OF fin nfs cond n P R SN ur_closed ur_P_closed orient]
    have "(t i \<cdot> \<tau> i, s (Suc i) \<cdot> \<tau> (Suc i)) \<in> (NS \<union> S)^*" unfolding \<tau> mode_NS_def using mode by auto
    then have "(t i \<cdot> \<tau> i, s (Suc i) \<cdot> \<tau> (Suc i)) \<in> (rstep (NS \<union> S))^*" 
      using rtrancl_mono[OF subset_rstep[of "NS \<union> S"]] by auto 
  } note steps = this
  have chain: "ichain (nfs,m,S,NS,{},S,NS) s t \<tau>"
    unfolding ichain.simps qrstep_rstep_conv idS
  proof (intro conjI allI)
    fix i
    from chain nonStrict show "(s i, t i) \<in> NS \<union> S" by auto 
  next
    let ?Q = "qrstep False Q (R \<union> Rw)"
    let ?QQ = "relto (qrstep False Q (Rs \<inter> (R \<union> Rw))) (?Q \<union> rstep {})"
    let ?R = "rstep (NS \<union> S)"
    let ?RR = "?R^* O rstep S O ?R^*"
    let ?QR = "qrelac Q (R \<union> Rw) {}"
    have switch': "qrstep False Q (R \<union> Rw) = ?QR" unfolding qrelac_empty_is_qrstep ..
    show "(INFM i. (s i, t i) \<in> S) \<or> 
      (INFM i. (t i \<cdot> \<tau> i, s (Suc i) \<cdot> \<tau> (Suc i)) \<in> ?RR)" unfolding INFM_disj_distrib[symmetric] 
      unfolding INFM_nat
    proof (intro allI)
      fix m
      from chain 
      have "(INFM i. (s i, t i) \<in> Ps \<inter> (P \<union> Pw)) \<or>
        (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QQ)" by (auto simp: switch_gen)
      from this[unfolded INFM_disj_distrib[symmetric], unfolded INFM_nat]
      obtain l where l: "Suc m < l" and alt:"(s l, t l) \<in> Ps \<inter> (P \<union> Pw) \<or> 
        (t l \<cdot> \<sigma> l, s (Suc l) \<cdot> \<sigma> (Suc l)) \<in> ?QQ" by blast
      then have l': "m < l" by auto
      let ?I = "i_trans"
      from chain m switch have SN: "\<And> l. SN_on (qrelac Q (R \<union> Rw) {}) {t l \<cdot> \<sigma> l}" by (simp add: qrelac_def)
      from alt show "\<exists> l > m. (s l, t l) \<in> S \<or> (t l \<cdot> \<tau> l, s (Suc l) \<cdot> \<tau> (Suc l)) \<in> ?RR"
      proof
        assume Ssteps: "(t l \<cdot> \<sigma> l, s (Suc l) \<cdot> \<sigma> (Suc l)) \<in> ?QQ"
        let ?tt = "t l \<cdot> \<tau> l"
        let ?st = "s (Suc l) \<cdot> \<tau> (Suc l)"              
        from chain have P: "(s l, t l) \<in> P \<union> Pw" by auto
        let ?Rs = "Rs \<inter> (R \<union> Rw)"
        have "(?tt,?st) \<in> monoS" unfolding \<tau>
          by (rule i_trans_strict_step[OF fin itrans_ac_empty cond mode n 
          SN Ssteps ur_closed ur_P_closed P orient], insert strictR, auto)
        with rtrancl_mono[OF subset_rstep[of "NS \<union> S"]] subset_rstep[of S] have "(?tt, ?st) \<in> ?RR" by auto
        with l' show ?thesis by auto
      next
        assume P: "(s l, t l) \<in> Ps \<inter> (P \<union> Pw)"
        with strictP have "(s l, t l) \<in> S \<or> \<not> funas_term (s l) \<subseteq> us" by force
        then show ?thesis
        proof
          assume nwf: "\<not> funas_term (s l) \<subseteq> us"
          from l obtain ll where ll: "l = Suc ll" by (cases l, auto)
          let ?ts = "t ll \<cdot> \<sigma> ll"
          let ?tt = "t ll \<cdot> \<tau> ll"
          let ?ss = "s (Suc ll) \<cdot> \<sigma> (Suc ll)"      
          let ?st = "s (Suc ll) \<cdot> \<tau> (Suc ll)"              
          from chain have P: "(s ll, t ll) \<in> P \<union> Pw" by auto
          from P ur_P_closed have urt: "ur_closed_term_af (R \<union> Rw) ur us \<pi> (t ll)" by force
          from chain have steps: "(?ts, ?ss) \<in> ?Q^*" by (auto simp: switch)
          from steps SN[of ll, folded switch'] 
          have SNs: "SN_on (qrstep False Q (R \<union> Rw)) {?ss}" by (rule steps_preserve_SN_on)
          from i_transI[OF fin itrans_ac_empty urt SN[unfolded switch']] 
          have ns0: "(?tt, ?I ?ts) \<in> NS^*" unfolding \<tau> by simp
          from i_transVI[OF fin itrans_ac_empty cond n SN[unfolded switch'] _ ur_closed orient] 
          have ns1: "(?I ?ts, ?I ?ss) \<in> monoNS"
            using mode steps unfolding mode_NS_def by auto
          from i_transII[OF SNs[unfolded switch'], THEN conjunct2] nwf[unfolded ll]
          have "(?I ?ss, ?st) \<in> (rstep (ce_trs (c,k)))^+" unfolding \<tau> by auto
          from trancl_mono[OF this mono_ce[OF cond[unfolded mode_cond_def, THEN mp[OF _ mode]]]]
          have strict: "(?I ?ss, ?st) \<in> S^+" .
          from ns0 ns1 strict have "(?tt,?st) \<in> NS^* O monoNS O S^+" by auto
          then have "(?tt,?st) \<in> monoNS O S O monoNS" by regexp
          with rtrancl_mono[OF subset_rstep[of "NS \<union> S"]] subset_rstep[of S] 
          have strict: "(?tt, ?st) \<in> ?RR" by auto
          from l ll have "m < ll" by auto
          with strict show ?thesis by blast
        qed (insert l', auto)
      qed
    qed
  qed (auto simp: steps)
  have idS: "S \<inter> (NS \<union> S) = S" by auto
  from ichain_mono[OF chain subset_refl _ subset_refl subset_refl, of "NS \<union> S - S" "NS \<union> S - S"] 
    mono_redpair_sound_ichain[OF subset_refl subset_refl, of nfs m "{}" s t \<tau>]
  show False unfolding idS by blast
qed

end
