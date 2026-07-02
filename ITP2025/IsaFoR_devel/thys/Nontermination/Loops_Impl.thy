(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Loops_Impl
imports 
  Framework.Dependency_Pair_Problem_Spec
  Framework.Termination_Problem_Spec
  Innermost_Loops_Impl
  Nontermination
begin

definition
  check_loop ::
    "('f :: showl,'v :: showl) term list \<Rightarrow> bool \<Rightarrow>
     ('f, 'v) term \<Rightarrow>
     ('f, 'v) rseq \<Rightarrow> ('f, 'v) substL \<Rightarrow> ('f, 'v) ctxt \<Rightarrow>
     ('f, 'v) rules \<Rightarrow>
     showsl check"
where
  "check_loop Q nfs s rseq \<sigma> C R \<equiv> do {
    check (rseq \<noteq> []) (showsl_lit (STR ''rewrite sequence must be non-empty''));
    if Q = []
      then check_qrsteps (\<lambda> _. True) nfs R rseq s (C\<langle>s \<cdot> mk_subst Var \<sigma>\<rangle>)
      else do {
        check_qrsteps_subst (check_NF_iteration \<sigma> Q) nfs R rseq s (C\<langle>s \<cdot> mk_subst Var \<sigma>\<rangle>)
      }
   }"

lemma check_loop_sound:
  assumes ok: "isOK (check_loop Q nfs s rseq \<sigma> C R)"
  shows "\<not> SN (qrstep nfs (set Q) (set R))"
proof (cases "Q = []")
  case True
  obtain sig where sig: "sig = mk_subst Var \<sigma>" by auto
  with ok and True
    have check: "isOK (check_qrsteps (\<lambda> _. True) nfs R rseq s (C\<langle>s \<cdot> sig\<rangle>))" and nonempty: "rseq \<noteq> []"
    by (auto simp: Let_def check_loop_def)
  from nonempty obtain n where rseq: "length rseq = Suc n" by (cases rseq, auto)
  with check_qrsteps_sound[OF _ check, of "[]"]
    have "(s,C\<langle>s \<cdot> sig\<rangle>) \<in> (rstep (set R)) ^^ (Suc n)" by auto
  then have step: "(s,C\<langle>s \<cdot> sig\<rangle>) \<in> (rstep (set R))^+" using pow_Suc_subset_trancl by auto
  from loop_imp_not_SN_on_rstep[OF step] show ?thesis
    unfolding SN_on_def True by auto
next
  case False
  let ?\<sigma> = "mk_subst Var \<sigma>"
  from False ok 
  have check: "isOK (check_qrsteps_subst (check_NF_iteration \<sigma> Q) nfs R rseq s (C\<langle>s \<cdot> ?\<sigma>\<rangle>))" and nonempty: "rseq \<noteq> []"
    by (auto simp: Let_def check_loop_def)
  from nonempty obtain n where rseq: "length rseq = Suc n" by (cases rseq) simp_all
  from check_qrsteps_subst_sound[OF refl check]
  have "\<And> i. (s \<cdot> ?\<sigma> ^^ i, (C \<cdot>\<^sub>c ?\<sigma> ^^ i)\<langle>s \<cdot> ?\<sigma> \<cdot> ?\<sigma> ^^ i\<rangle>) \<in> qrstep nfs (set Q) (set R) ^^ Suc n" unfolding rseq by auto
  then have step: "\<And> i. \<exists> C. (s \<cdot> ?\<sigma> ^^ i, C\<langle>s \<cdot> ?\<sigma> \<cdot> ?\<sigma> ^^ i\<rangle>) \<in> (qrstep nfs (set Q) (set R))^+" using pow_Suc_subset_trancl by blast
  from loop_imp_not_SN_on_qrstep[OF step]
  show ?thesis unfolding SN_on_def by auto
qed

datatype ('f,'v)trs_loop_prf = TRS_loop_prf "('f,'v)term" "('f,'v)rseq" "('f,'v)substL" "('f,'v)ctxt"

primrec check_trs_loop ::
    "('tp, 'f:: showl, 'v :: showl) tp_ops \<Rightarrow> 'tp \<Rightarrow> ('f, 'v)trs_loop_prf \<Rightarrow> showsl check" where
  "check_trs_loop I tp (TRS_loop_prf s rseq \<sigma> C) = 
     check_loop (tp_ops.Q I tp) (tp_ops.nfs I tp) s rseq \<sigma> C (tp_ops.rules I tp)"

lemma check_trs_loop_sound:
  assumes ok: "isOK (check_trs_loop I tp prf)"
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
proof -
  obtain s rseq \<sigma> C where id: "prf = TRS_loop_prf s rseq \<sigma> C" by (cases "prf")
  from check_loop_sound[OF ok[unfolded id check_trs_loop.simps]] show ?thesis .
qed

datatype ('f,'v)dp_loop_prf = DP_loop_prf "('f,'v)term" "('f,'v)prseq" "('f,'v)substL" "('f,'v)ctxt"

primrec
  check_dp_loop ::
    "('dpp, 'f:: showl, 'v :: showl) dpp_ops \<Rightarrow> 'dpp \<Rightarrow> ('f,'v)dp_loop_prf \<Rightarrow>
     showsl check"
where
  "check_dp_loop I dpp (DP_loop_prf s prseq \<sigma> C) = (let 
    P    = dpp_ops.pairs I dpp;
    R    = dpp_ops.rules I dpp;
    nfs  = dpp_ops.nfs I dpp;
    Q    = dpp_ops.Q I dpp in 
  (if C = \<box> then do {
    check (prseq \<noteq> []) (showsl_lit (STR ''rewrite sequence must be non-empty''));
    if Q = [] then check_qsteps (\<lambda> _. True) nfs P R prseq s (s \<cdot> mk_subst Var \<sigma>)
        else check_qsteps_subst (check_NF_iteration \<sigma> Q) nfs P R prseq s (s \<cdot> mk_subst Var \<sigma>)
  } else do {
    check_loop Q nfs s (map (\<lambda>(x, y, _, z). (x, y, z)) prseq) \<sigma> C R
  }))"
  
lemma check_dp_loop:
  assumes I: "dpp_spec I"
  and ok: "isOK (check_dp_loop I dpp prf)"
  shows "infinite_dpp (dpp_ops.nfs I dpp, set (dpp_ops.pairs I dpp), set (dpp_ops.Q I dpp), set (dpp_ops.rules I dpp))"
proof -
  obtain s prseq \<sigma> C where id: "prf = DP_loop_prf s prseq \<sigma> C" by (cases "prf", auto)
  note ok = ok[unfolded id check_dp_loop.simps Let_def]
  obtain sig where sig: "sig = mk_subst Var \<sigma>" by auto
  interpret dpp_spec I by fact
  let ?Q = "Q dpp"
  let ?R = "rules dpp"
  let ?P = "pairs dpp"
  let ?sQ = "set ?Q"
  let ?sR = "set ?R"
  let ?sP = "set ?P"
  let ?nfs = "NFS dpp"
  show ?thesis
  proof (cases C)
    case Hole    
    with ok  obtain n where prseq: "length prseq = Suc n" 
      by (cases prseq, auto)
    obtain PR where PR: "PR = rqrstep ?nfs ?sQ ?sP \<union> qrstep ?nfs ?sQ ?sR" by auto
    show ?thesis
    proof (cases "?Q = []")
      case True
      with sig ok Hole
      have check: "isOK (check_qsteps (\<lambda> _. True) ?nfs ?P ?R prseq s (s \<cdot> sig))"
        by (auto simp: check_dp_loop_def)
      from check_qsteps_sound[OF _ check, of ?Q] prseq PR
      have "(s, s \<cdot> sig) \<in> PR ^^ (Suc n)" using True by simp
      then have step: "(s, s \<cdot> sig) \<in> PR^+" using pow_Suc_subset_trancl by auto
      from step[simplified PR True]
      have "(s, s \<cdot> sig) \<in> (rrstep ?sP \<union> rstep ?sR)^+"
        unfolding rqrstep_def qrstep_rstep_conv rrstep_def' by simp
      from loop_imp_infinite_empty_Q[OF this]
      show ?thesis by (simp add: True)
    next
      case False
      with sig ok Hole
      have check: "isOK (check_qsteps_subst (check_NF_iteration \<sigma> ?Q) ?nfs ?P ?R prseq s (s \<cdot> sig))"
        by auto
      from check_qsteps_subst_sound[OF refl check]
      have "\<And> i. (s \<cdot> sig ^^ i, s \<cdot> sig \<cdot> sig ^^ i) \<in> PR ^^ Suc n"
        unfolding sig prseq PR .
      then have step: "\<And> i. (s \<cdot> sig ^^ i, s \<cdot> sig \<cdot> sig ^^ i) \<in> PR^+" using pow_Suc_subset_trancl by blast
      from loop_imp_infinite[OF this[unfolded PR]]
      show ?thesis .
    qed      
  next
    case (More f bef D aft)
    with sig ok
    have check: "isOK (check_loop ?Q ?nfs s (map (\<lambda> (x,y,_,z). (x,y,z)) prseq) \<sigma> C ?R)"
      by simp
    from check_loop_sound[OF this] and SN_subset
    have "\<not> SN (rqrstep ?nfs ?sQ ?sP \<union> qrstep ?nfs ?sQ ?sR)"
      unfolding SN_on_def by blast
    then show ?thesis unfolding infinite_dpp_not_SN_conv .
  qed
qed

fun
  check_rel_seq ::
    "('f:: showl, 'v:: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow>
     ('f, 'v) prseq \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<Rightarrow>
     showsl check"
where
  "check_rel_seq R S [] s u True = check (s = u) (
     showsl_lit (STR ''the last term of the rewrite sequence\<newline>'') \<circ> showsl s \<circ> 
     showsl_lit (STR ''\<newline>does not correspond to the goal term\<newline>'') \<circ> showsl u \<circ> showsl_nl
   )"
| "check_rel_seq R S [] s u False = error (showsl_lit (STR ''did not find strict step in rewrite sequence''))"
| "check_rel_seq R S ((p, r, True, t) # prts) s u b = do {
     check_qrstep (\<lambda> _ . True) False R p r s t;
     check_rel_seq R S prts t u True
   }"
| "check_rel_seq R S ((p, r, False, t) # prts) s u b = do {
     check_qrstep (\<lambda> _ . True) False S p r s t;
     check_rel_seq R S prts t u b
   }"

lemma check_rel_seq_rtrancl:
  assumes "isOK (check_rel_seq R S rseq s t b)"
  shows "(s, t) \<in> (rstep (set R \<union> set S))^*" (is "_ \<in> ?R^*")
using assms
proof (induct rseq arbitrary: s b)
  case Nil
  then show ?case by (cases b) simp_all
next
  case (Cons prt rseq)
  obtain p r or u where prt: "prt = (p, r, or, u)" by (cases prt) blast
  from Cons[unfolded prt]
  have IH: "(u, t) \<in> ?R^*"
    by (cases or, induct rseq) (auto)
  have "(s,u) \<in> ?R"
  proof (cases or)
    case True
    with Cons[unfolded prt]
    have "isOK (check_qrstep (\<lambda> _ . True) False R p r s u)" by simp
    from check_qrstep_qrstep[OF _ this, of "[]"]
    have "(s,u) \<in> rstep (set R)" by auto
    then show ?thesis by auto
  next
    case False
    with Cons[unfolded prt]
    have "isOK (check_qrstep  (\<lambda> _ . True) False S p r s u)" by simp
    from check_qrstep_qrstep[OF _ this, of "[]"]
    have "(s,u) \<in> rstep (set S)" by simp
    then show ?thesis by auto
  qed
  with IH show ?case by auto
qed

lemma check_rel_seq_trancl:
  assumes "isOK (check_rel_seq R S rseq s t False)"
  shows "(s, t) \<in> (rstep (set R \<union> set S))^* O rstep (set R) O (rstep (set R \<union> set S))^*"
proof -
  let ?RS = "(rstep (set R \<union> set S))^*"
  let ?R  = "?RS O rstep (set R) O ?RS"
  from assms show "(s,t) \<in> ?R"
  proof (induct rseq arbitrary: s)
    case (Cons prt rseq)
    obtain p r or u where prt: "prt = (p, r, or, u)" by (cases prt) blast   
    show ?case 
    proof (cases or)
      case False
      with Cons[unfolded prt]
      have IH: "(u, t) \<in> ?R"  and check: "isOK (check_qrstep  (\<lambda> _ . True) False S p r s u)" by auto
      have subset: "rstep (set R \<union> set S) O ?RS \<subseteq> ?RS" by auto
      from check_qrstep_qrstep[OF _ check, of "[]"] have "(s, u) \<in> rstep (set R \<union> set S)" by auto
      with IH have "(s, t) \<in> (rstep (set R \<union> set S) O ?RS) O rstep (set R) O ?RS"
        by (auto simp: O_assoc)
      then show ?thesis using subset by blast
    next
      case True
      with Cons[unfolded prt]
        have check1: "isOK (check_qrstep (\<lambda> _ . True) False R p r s u)"
        and check2: "isOK (check_rel_seq R S rseq u t True)"
        by auto
      from check_qrstep_qrstep[OF _ check1, of "[]"]  check_rel_seq_rtrancl[OF check2]
        show ?thesis by auto
    qed
  qed simp
qed

definition
  check_rel_loop ::
    "('f:: showl, 'v:: showl) term \<Rightarrow>
     ('f, 'v) prseq \<Rightarrow> ('f, 'v) substL \<Rightarrow> ('f, 'v) ctxt \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "check_rel_loop s rseq \<sigma> C R S \<equiv> check_rel_seq R S rseq s (C\<langle>s \<cdot> mk_subst Var \<sigma>\<rangle>) False"

lemma check_rel_loop:
  assumes "isOK (check_rel_loop s rseq \<sigma> C R S)"
  shows "\<not> (SN_qrel (False,{}, (set R), (set S)))"
  by (rule loop_imp_not_SN_qrel_empty_Q[OF
    check_rel_seq_trancl[OF assms[unfolded check_rel_loop_def]]])

datatype ('f,'v)rel_trs_loop_prf = Rel_trs_loop_prf "('f, 'v)term" "('f, 'v) prseq" "('f, 'v) substL" "('f, 'v)ctxt"

fun check_rel_trs_loop ::
    "('tp, 'f:: showl, 'v :: showl) tp_ops \<Rightarrow> 'tp \<Rightarrow> 
     ('f,'v)rel_trs_loop_prf \<Rightarrow> showsl check" where
  "check_rel_trs_loop I tp (Rel_trs_loop_prf s rseq \<sigma> C) = (do {
        check (tp_ops.Q_empty I tp) (showsl_lit (STR ''Q is not empty''));
        check_rel_loop s rseq \<sigma> C (tp_ops.R I tp) (tp_ops.Rw I tp)
      })"

lemma check_rel_trs_loop:
  assumes I: "tp_spec I"
  and ok: "isOK (check_rel_trs_loop I tp prf)"
  shows "\<not> (SN_qrel (tp_ops.nfs I tp,set (tp_ops.Q I tp), set (tp_ops.R I tp), set (tp_ops.Rw I tp)))"
proof -
  obtain s rseq \<sigma> C where id: "prf = Rel_trs_loop_prf s rseq \<sigma> C" by (cases "prf")
  interpret tp_spec I by fact
  note ok = ok[unfolded id check_rel_trs_loop.simps]
  from ok have Q: "set (Q tp) = {}" and ok: "isOK(check_rel_loop s rseq \<sigma> C (R tp) (Rw tp))" by auto
  show ?thesis unfolding Q using check_rel_loop[OF ok] by auto
qed

end

