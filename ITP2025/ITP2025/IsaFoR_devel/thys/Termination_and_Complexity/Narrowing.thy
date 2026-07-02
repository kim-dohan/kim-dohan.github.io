(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Narrowing
imports
  Dependency_Graph
  Rewriting
begin

definition
  qnarrows_r_p_s :: "bool \<Rightarrow> ('f,string)terms \<Rightarrow> ('f, string) trs \<Rightarrow> ('f, string) rule \<Rightarrow> pos \<Rightarrow> ('f,string)subst \<Rightarrow> ('f, string)trs"
where
 "qnarrows_r_p_s nfs Q R r p \<mu> \<equiv> {(s,t). \<exists> \<mu>2. p \<in> poss s \<and> is_Fun (s |_ p) \<and> r \<in> R \<and> mgu_vd_string (s |_ p) (fst r) = Some (\<mu>, \<mu>2) 
     \<and> set (args (fst r \<cdot> \<mu>2)) \<subseteq> NF_terms Q \<and> NF_subst nfs r \<mu>2 Q \<and> t = replace_at (s \<cdot> \<mu>) p (snd r \<cdot> \<mu>2)}"

lemma qnarrows_r_p_s_imp_qrstep: assumes narr: "(s,t) \<in> qnarrows_r_p_s nfs Q R r p \<mu>"
  shows "\<exists> \<delta>. (s \<cdot> \<mu>, t) \<in> qrstep_r_p_s nfs Q R r p \<delta>"
proof -
  from narr[unfolded qnarrows_r_p_s_def] obtain \<mu>2 where p: "p \<in> poss s"
    and r: "r \<in> R"
    and mgu: "mgu_vd_string (s |_ p) (fst r) = Some (\<mu>, \<mu>2)"
    and t: "t = replace_at (s \<cdot> \<mu>) p (snd r \<cdot> \<mu>2)" 
    and NF: "set (args (fst r \<cdot> \<mu>2)) \<subseteq> NF_terms Q" 
    and nfs: "NF_subst nfs r \<mu>2 Q" by auto  
  from p have p\<mu>: "p \<in> poss (s \<cdot> \<mu>)" by auto
  from mgu_vd_string_sound[OF mgu] have id: "s |_ p \<cdot> \<mu> = fst r \<cdot> \<mu>2" by simp
  show ?thesis
    by (rule exI[of _ \<mu>2], unfold qrstep_r_p_s_def t NF_terms_args_conv[symmetric], insert NF r p p\<mu> id nfs, auto)
qed


lemma qrstep_instance_imp_qnarrows: assumes step: "(s \<cdot> \<sigma>,t) \<in> qrstep_r_p_s nfs Q R r p \<tau>"
  and not\<sigma>: "p \<in> poss s" "is_Fun (s |_ p)"
  shows "\<exists> \<mu> \<delta> u. (s,u) \<in> qnarrows_r_p_s nfs Q R r p \<mu> \<and> s \<cdot> \<sigma> = s \<cdot> \<mu> \<cdot> \<delta> \<and> t = u \<cdot> \<delta> \<and> \<sigma> = \<mu> \<circ>\<^sub>s \<delta>"
proof -
  from step[unfolded qrstep_r_p_s_def NF_terms_args_conv[symmetric]] have r: "r \<in> R" and id: "s \<cdot> \<sigma> |_ p = fst r \<cdot> \<tau>" 
    and t: "t = replace_at (s \<cdot> \<sigma>) p (snd r \<cdot> \<tau>)" and NF: "set (args (fst r \<cdot> \<tau>)) \<subseteq> NF_terms Q" 
    and nfs: "NF_subst nfs r \<tau> Q" by auto
  from not\<sigma>(1) id have "s |_ p \<cdot> \<sigma> = fst r \<cdot> \<tau>" by auto
  from mgu_vd_string_complete[OF this] obtain \<mu>1 \<mu>2 \<delta> where 
    mgu: "mgu_vd_string (s |_ p) (fst r)
     = Some (\<mu>1, \<mu>2)" and \<sigma>: "\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" and \<tau>: "\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" and id: "s |_ p \<cdot> \<mu>1 = fst r \<cdot> \<mu>2" by auto
  {
    fix t
    assume t: "t \<in> set (args (fst r \<cdot> \<mu>2))"
    then obtain f ts where r2: "fst r \<cdot> \<mu>2 = Fun f ts" by (cases "fst r \<cdot> \<mu>2", auto)
    with t have "t \<cdot> \<delta> \<in> set (args (fst r \<cdot> \<tau>))" unfolding \<tau> by auto
    with NF  have "t \<cdot> \<delta> \<in> NF_terms Q" by auto
    from NF_instance[OF this] have "t \<in> NF_terms Q" .
  } note NF = this
  have nfs: "NF_subst nfs r \<mu>2 Q" using nfs[unfolded \<tau>] NF_instance[of _ \<delta>] 
    unfolding NF_subst_def subst_compose_def by auto
  have narr: "(s,replace_at (s \<cdot> \<mu>1) p (snd r \<cdot> \<mu>2)) \<in> qnarrows_r_p_s nfs Q R r p \<mu>1"
    unfolding qnarrows_r_p_s_def using nfs not\<sigma> r mgu NF by auto
  show ?thesis
  proof (intro exI conjI, rule narr)
    show "s \<cdot> \<sigma> = s \<cdot> \<mu>1 \<cdot> \<delta>" unfolding \<sigma> by simp
  next
    show "t = replace_at (s \<cdot> \<mu>1) p (snd r \<cdot> \<mu>2) \<cdot> \<delta>"
      unfolding t \<sigma> \<tau> using not\<sigma>(1) 
      by (simp add: ctxt_of_pos_term_subst)
  qed (rule \<sigma>)
qed

lemma qrstep_imp_qnarrows: assumes step: "(s,t) \<in> qrstep_r_p_s nfs Q R r p \<tau>"
  and wf_trs: "\<And> l r. (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "\<exists> \<mu> \<delta> u. (s,u) \<in> qnarrows_r_p_s nfs Q R r p \<mu> \<and> s = s \<cdot> \<mu> \<cdot> \<delta> \<and> t = u \<cdot> \<delta> \<and> \<mu> \<circ>\<^sub>s \<delta> = Var"
proof -
  from step[unfolded qrstep_r_p_s_def] have p: "p \<in> poss s" and r: "r \<in> R" and id: "s |_ p = fst r \<cdot> \<tau>" 
    by auto
  obtain l1 r1 where lr1: "r = (l1,r1)" by force
  from wf_trs[OF r[unfolded lr1]] have is_Fun: "is_Fun (s |_ p)" unfolding id lr1 by (cases l1, auto)
  from step have step: "(s \<cdot> Var, t) \<in> qrstep_r_p_s nfs Q R r p \<tau>" by simp
  from qrstep_instance_imp_qnarrows[OF step p is_Fun] obtain \<mu> \<delta> u where 
    narr: "(s,u) \<in> qnarrows_r_p_s nfs Q R r p \<mu>" and s: "s = s \<cdot> \<mu> \<cdot> \<delta>" and t: "t = u \<cdot> \<delta>" 
    and var: "\<mu> \<circ>\<^sub>s \<delta> = Var" by auto
  show ?thesis
    by (intro exI conjI, rule narr, insert s t var, auto)
qed  

lemma ichain_narrowing_replacement: fixes s t \<sigma> pair sts Q Rs Rw nfs
  defines R: "R \<equiv> Rs \<union> Rw"
  defines Pr: "Pr \<equiv> \<lambda> i. (\<exists> s' t' \<tau>. (s',t') \<in> sts \<and> (s i \<cdot> \<sigma> i,  s' \<cdot> \<tau>) \<in> (qrstep nfs Q R)^* \<and> 
         s' \<cdot> \<tau> \<in> NF_terms Q \<and> NF_subst nfs (s',t') \<tau> Q \<and> (t i \<cdot> \<sigma> i, t' \<cdot> \<tau>) \<in> (qrstep nfs Q R)^* \<and> 
         (t' \<cdot> \<tau>, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q R)^*)"
  assumes chain: "min_ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>"
  and strict: "pair \<in> P \<or> Rs = {}"
  and main: "\<And> i. (s i,t i) = pair \<Longrightarrow> Pr i"
  shows "\<exists> s' t' \<sigma>'. min_ichain (nfs,m,replace pair sts P, replace pair sts Pw, Q, Rs, Rw) s' t' \<sigma>'" 
proof -
  let ?P = "replace pair sts P"
  let ?Pw = "replace pair sts Pw"
  let ?R = "(qrstep nfs Q R)^*"
  let ?R1 = "qrstep nfs Q R"
  let ?Rs = "qrstep nfs Q Rs"
  let ?Q = "NF_terms Q"
  obtain Pr' where Pr': "Pr' \<equiv> \<lambda> i (s',t',\<sigma>'). (s',t') \<in> sts \<and> (s i \<cdot> \<sigma> i, s' \<cdot> \<sigma>') \<in> ?R \<and> s' \<cdot> \<sigma>' \<in> ?Q \<and> 
  NF_subst nfs (s',t') \<sigma>' Q \<and>
  (t i \<cdot> \<sigma> i, t' \<cdot> \<sigma>') \<in> ?R \<and> (t' \<cdot> \<sigma>', s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R" by auto
  obtain st\<sigma> where st\<sigma>: "st\<sigma> \<equiv> \<lambda> i. if (s i, t i) = pair then (SOME st\<sigma>. Pr' i st\<sigma>) else (s i, t i, \<sigma> i)"
    by auto
  obtain s' where s': "s' \<equiv> \<lambda> i. fst (st\<sigma> i)" by auto
  obtain t' where t': "t' \<equiv> \<lambda> i. fst (snd (st\<sigma> i))" by auto
  obtain \<sigma>' where \<sigma>': "\<sigma>' \<equiv> \<lambda> i. snd (snd (st\<sigma> i))" by auto
  note st\<sigma>' = s' t' \<sigma>'
  note chain = chain[unfolded min_ichain.simps ichain.simps R[symmetric] minimal_cond_def]
  from chain have inP: "\<And> i. (s i, t i) \<in> P \<union> Pw" by auto
  from chain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> ?Q" by auto
  from chain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
  from chain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R" by auto
  from chain have SN: "\<And> i. m \<Longrightarrow> SN_on ?R1 {t i \<cdot> \<sigma> i}" by auto
  {
    fix i
    assume pair: "(s i, t i) = pair"
    from main[OF this]
    have "\<exists> s t \<sigma>. Pr' i (s,t,\<sigma>)" unfolding Pr' split Pr .
    then have "\<exists> st\<sigma>. Pr' i st\<sigma>" by blast
    from someI_ex[OF this] have "Pr' i (st\<sigma> i)" unfolding st\<sigma> pair by auto
    then have "Pr' i (s' i, t' i, \<sigma>' i)" unfolding st\<sigma>' by simp
  } note main = this[unfolded Pr' split]
  {
    fix i
    assume npair: "(s i, t i) \<noteq> pair"
    then have "(s' i, t' i, \<sigma>' i) = (s i, t i, \<sigma> i)" unfolding st\<sigma> st\<sigma>' by simp
  } note other = this
  {
    fix i
    have "(s i \<cdot> \<sigma> i, s' i \<cdot> \<sigma>' i) \<in> ?R"
      using main[of i] other[of i]
      by (cases "(s i, t i) = pair", auto)
  } note ss' = this
  have "min_ichain (nfs,m,?P,?Pw,Q,Rs,Rw) s' t' \<sigma>'"
    unfolding min_ichain.simps ichain.simps minimal_cond_def R[symmetric]
  proof (intro conjI allI impI)
    fix i
    assume m
    note SN = SN[of i, OF this] 
    show "SN_on ?R1 {t' i \<cdot> \<sigma>' i}"      
    proof (cases "(s i, t i) = pair")
      case False
      from other[OF this] SN show ?thesis by simp 
    next
      case True
      from main[OF this] have "(t i \<cdot> \<sigma> i, t' i \<cdot> \<sigma>' i) \<in> ?R" by auto
      from steps_preserve_SN_on[OF this SN] show ?thesis .
    qed
  next
    fix i
    from inP have inP: "(s i, t i) \<in> P \<union> Pw" .
    show "(s' i, t' i) \<in> ?P \<union> ?Pw"
    proof (cases "(s i, t i) = pair")
      case False
      from other[OF this] inP False show ?thesis unfolding replace_def by auto
    next
      case True
      with inP have pair: "pair \<in> P \<union> Pw" by auto
      from main[OF True] have "(s' i, t' i) \<in> sts" by auto
      with inP pair show ?thesis unfolding replace_def by auto
    qed
  next
    fix i    
    show "s' i \<cdot> \<sigma>' i \<in> ?Q" 
    proof (cases "(s i, t i) = pair")
      case False
      from other[OF this] NF  show ?thesis  by simp
    next
      case True
      from main[OF True] show ?thesis by simp
    qed
  next
    fix i
    show "NF_subst nfs (s' i, t' i) (\<sigma>' i) Q" 
    proof (cases "(s i, t i) = pair")
      case False
      from other[OF this] nfs[of i] show ?thesis by simp
    next
      case True
      from main[OF True] show ?thesis by simp
    qed
  next
    fix i
    show "(t' i \<cdot> \<sigma>' i, s' (Suc i) \<cdot> \<sigma>' (Suc i)) \<in> ?R"
    proof (rule rtrancl_trans[OF _ ss'])
      show "(t' i \<cdot> \<sigma>' i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R"
        using steps[of i] main[of i] other[of i]
        by (cases "(s i, t i) = pair", auto)
    qed
  next
    from chain have disj: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R O ?Rs O ?R)" by simp
    show "(INFM i. (s' i, t' i) \<in> ?P) \<or> (INFM i. (t' i \<cdot> \<sigma>' i, s' (Suc i) \<cdot> \<sigma>' (Suc i)) \<in> ?R O ?Rs O ?R)"
      unfolding INFM_disj_distrib[symmetric] 
      unfolding INFM_nat_le
    proof
      fix i
      from disj[unfolded INFM_nat_le] obtain j where j: "j \<ge> i" and 
        disj: "(s j, t j) \<in> P \<or> (t j \<cdot> \<sigma> j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> ?R O ?Rs O ?R" (is "?one \<or> ?two") by blast
      show "\<exists> j \<ge> i. (s' j, t' j) \<in> ?P \<or> (t' j \<cdot> \<sigma>' j, s' (Suc j) \<cdot> \<sigma>' (Suc j)) \<in> ?R O ?Rs O ?R"
      proof (intro exI conjI, rule j)
        show "(s' j, t' j) \<in> ?P \<or> (t' j \<cdot> \<sigma>' j, s' (Suc j) \<cdot> \<sigma>' (Suc j)) \<in> ?R O ?Rs O ?R" 
          (is "?one' \<or> ?two' \<in> ?rel")
        proof (cases "(s j, t j) = pair")
          case False          
          from other[OF this] disj have "(s' j, t' j) \<in> ?P \<or> (t' j \<cdot> \<sigma>' j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> ?rel" 
            using False unfolding replace_def by auto
          then show ?thesis 
          proof 
            assume ?one' then show ?thesis by auto
          next
            assume "(t' j \<cdot> \<sigma>' j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> ?rel"
            with ss'[of "Suc j"] have steps: "?two' \<in> ?rel O ?R" by blast
            have steps: "?two' \<in> ?rel"
              by (rule set_mp[OF _ steps], regexp)
            then show ?thesis by auto
          qed
        next
          case True
          from main[OF this] have mem: "(s' j,t' j) \<in> sts" by auto
          then show ?thesis using strict disj True by (auto simp: replace_def)
        qed
      qed
    qed
  qed    
  then show ?thesis by blast
qed
  
lemma reorder_steps_for_narrowing:
  assumes no_NF: "t |_ p \<notin> NF_terms Q"
  and steps: "(t, u) \<in> qrstep nfs Q R ^^ n"
  and NF: "u \<in> NF_terms Q"
  and pt: "p \<in> poss t"
  and inn: "NF_terms Q \<subseteq> NF_trs R"
  shows "\<exists>up m. (t |_ p, up) \<in> qrstep nfs Q R \<and> (replace_at t p up, u) \<in> qrstep nfs Q R ^^ m \<and> n = Suc m"
proof - 
  let ?QR = "qrstep nfs Q R"
  from normalize_subterm_qrsteps_count[OF pt steps NF]
  obtain n1 n2 v where steps: "(t |_ p, v) \<in> ?QR ^^ n1" and NF: "v \<in> NF_terms Q" 
    and steps2: "(replace_at t p v, u) \<in> ?QR ^^ n2" and n: "n = n1 + n2" by blast
  from NF no_NF steps obtain k where n1: "n1 = Suc k" by (cases n1, auto)
  from n1 n have n: "n = Suc (k + n2)" by auto
  from steps[unfolded n1] obtain w where step: "(t |_ p, w) \<in> ?QR" and steps: "(w,v) \<in> ?QR ^^ k"
    by (rule relpow_Suc_E2)
  have steps: "(replace_at t p w, replace_at t p v) \<in> ?QR ^^ k"
    using ctxt.closed_relpow [THEN ctxt.closedD [OF _ steps]] by auto
  from steps steps2
  have steps: "(replace_at t p w, u) \<in> ?QR ^^ (k + n2)"
    unfolding relpow_add by auto
  show ?thesis
    by (intro exI conjI, rule step, rule steps, rule n)
qed
    
lemma narrowing_technique: fixes R :: "('f,string)trs"
  assumes steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs Q R)^*"
  and lin_or_inn: "linear_term t \<and> Q = {} \<or> NF_terms Q \<subseteq> NF_trs R"
  and NF: "{s \<cdot> \<sigma>, u \<cdot> \<tau>} \<subseteq> NF_terms Q"
  and nfs: "NF_subst nfs (s,t) \<sigma> Q"
  and var_cond: "vars_term (t |_ p) \<subseteq> vars_term s"
  and precond: "t |_ p \<in> NF_terms Q \<Longrightarrow> p \<in> poss u \<and> (\<forall> \<mu>1 \<mu>2.
  mgu_vd_string (t |_ p) (u |_ p) = Some (\<mu>1,\<mu>2) \<longrightarrow>
  \<not> ({s \<cdot> \<mu>1, u \<cdot> \<mu>2} \<subseteq> NF_terms Q))"
  and narr: "\<And> r t' q \<mu>. (t |_ p,t') \<in> qnarrows_r_p_s nfs Q R r q \<mu> \<Longrightarrow> s \<cdot> \<mu> \<in> NF_terms Q \<Longrightarrow> 
     \<exists> st' \<in> sts. instance_rule (s \<cdot> \<mu>, replace_at (t \<cdot> \<mu>) p t') st' \<and> (\<not> nfs \<or> Q = {} \<or> wf_rule st')"
  and pt: "p \<in> poss t"
  and pet: "p \<in> poss (ecap R Q {mv_xvar s} (mv_xvar t)) \<or> (t |_ p \<notin> NF_terms Q)" 
  and ecap: "is_ecap ecap"
  shows "\<exists> s' t' \<delta>. (s',t') \<in> sts \<and> (s \<cdot> \<sigma>,s' \<cdot> \<delta>) \<in> (qrstep nfs Q R)^* \<and> s' \<cdot> \<delta> \<in> NF_terms Q \<and> NF_subst nfs (s',t') \<delta> Q \<and> (t \<cdot> \<sigma>, t' \<cdot> \<delta>) \<in> (qrstep nfs Q R)^* \<and> 
  (t' \<cdot> \<delta>, u \<cdot> \<tau>) \<in> (qrstep nfs Q R)^*"
proof -
  let ?QR = "qrstep nfs Q R"
  let ?R = "rstep R"
  let ?\<sigma>prop = "\<lambda> n \<sigma>'. (\<forall> x. (\<sigma> x, \<sigma>' x) \<in> ?QR^*) \<and> s \<cdot> \<sigma>' \<in> NF_terms Q \<and> (t \<cdot> \<sigma>', u \<cdot> \<tau>) \<in> ?QR^^n"
  let ?\<sigma>propex = "\<lambda> n. \<exists> \<sigma>'. ?\<sigma>prop n \<sigma>'"
  obtain n where n: "n = (LEAST n. ?\<sigma>propex n)" by auto
  {
    from rtrancl_imp_relpow[OF steps] obtain m where "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> ?QR^^m"
      by auto
    then have "?\<sigma>prop m \<sigma>" using steps NF by auto
    then have "?\<sigma>propex m" by blast
    from LeastI[of ?\<sigma>propex, OF this] have "?\<sigma>propex n" unfolding n .
  }
  then obtain \<sigma>' where "?\<sigma>prop n \<sigma>'" by auto
  then have \<sigma>steps: "\<And> x. (\<sigma> x, \<sigma>' x) \<in> ?QR^*" and NFs: "s \<cdot> \<sigma>' \<in> NF_terms Q" and stepsn: "(t \<cdot> \<sigma>', u \<cdot> \<tau>) \<in> ?QR^^n" by auto
  have \<sigma>steps_term: "\<And> t. (t \<cdot> \<sigma>, t \<cdot> \<sigma>') \<in> ?QR^*"
    by (rule subst_qrsteps_imp_qrsteps[OF \<sigma>steps])
  from NF NFs have NF: "{s \<cdot> \<sigma>', s \<cdot> \<sigma>, u \<cdot> \<tau>} \<subseteq> NF_terms Q" by auto
  from relpow_imp_rtrancl[OF stepsn] have steps: "(t \<cdot> \<sigma>', u \<cdot> \<tau>) \<in> ?QR^*" .
  from pt have pt\<sigma>: "p \<in> poss (t \<cdot> \<sigma>')" by simp
  let ?\<sigma> = "mv_subst \<sigma>'"
  note mv_xvar = mv_xvar[of _ \<sigma>']
  from NF have NF_set: "{s} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>' \<subseteq> NF_terms Q" by auto
  then have NF_set': "mv_xvar ` {s} \<cdot>\<^sub>s\<^sub>e\<^sub>t ?\<sigma> \<subseteq> NF_terms Q" using mv_xvar by auto
  from NF have NFu: "u \<cdot> \<tau> \<in> NF_terms Q" by auto
  note steps' = steps[unfolded mv_xvar]
  let ?t = "t |_ p"
  from pt have tp: "t \<cdot> \<sigma>' |_ p = ?t \<cdot> \<sigma>'" by auto
  from pet have "\<exists> up m. (?t \<cdot> \<sigma>' , up) \<in> ?QR \<and> (replace_at (t \<cdot> \<sigma>') p up, u \<cdot> \<tau>) \<in> ?QR^^m \<and> n = Suc m"
  proof
    assume pet: "p \<in> poss (ecap R Q {mv_xvar s} (mv_xvar t))"
    from pet have pet': "p \<in> poss (ecap R Q (mv_xvar ` {s}) (mv_xvar t))" by auto
    from ecap_poss_imp_result_poss[OF ecap steps' NF_set', OF pet']
    have pu\<tau>: "p \<in> poss (u \<cdot> \<tau>)" .
    then have "u \<cdot> \<tau> \<unrhd> u \<cdot> \<tau> |_ p" by (rule subt_at_imp_supteq)
    from NF_subterm[OF NFu this] NF have NFu\<tau>: "u \<cdot> \<tau> |_ p \<in> NF_terms Q" by auto
    have neq: "?t \<cdot> \<sigma>' \<noteq> u \<cdot> \<tau> |_ p" 
    proof
      assume id: "?t \<cdot> \<sigma>' = u \<cdot> \<tau> |_ p"  
      from NFu\<tau> id have "?t \<cdot> \<sigma>' \<in> NF_terms Q" by auto
      from NF_instance[OF this] have NFt: "?t \<in> NF_terms Q" .
      note precond = precond[OF NFt]
      from precond have pu: "p \<in> poss u" by auto
      with id have id': "?t \<cdot> \<sigma>' = u |_ p \<cdot> \<tau>" by simp
      from mgu_vd_string_complete[OF id'] obtain \<mu>1 \<mu>2 \<delta> where 
        mgu: "mgu_vd_string ?t (u |_ p) = Some (\<mu>1,\<mu>2)" and \<sigma>': "\<sigma>' = \<mu>1 \<circ>\<^sub>s \<delta>"
        and \<tau>: "\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" by auto
      from precond[unfolded mgu] have nNF: "\<not> {s \<cdot> \<mu>1, u \<cdot> \<mu>2} \<subseteq> NF_terms Q" by auto
      from NF[unfolded \<sigma>' \<tau>] have NF1: "s \<cdot> \<mu>1 \<cdot> \<delta> \<in> NF_terms Q" and NF2: "u \<cdot> \<mu>2 \<cdot> \<delta> \<in> NF_terms Q" by auto
      from NF_instance[OF NF1] NF_instance[OF NF2] nNF show False by simp
    qed 
    with tp have neg: "t \<cdot> \<sigma>' |_ p \<noteq> u \<cdot> \<tau> |_ p" by simp
    from NFs[unfolded mv_xvar] have NFs: "{mv_xvar s} \<cdot>\<^sub>s\<^sub>e\<^sub>t ?\<sigma> \<subseteq> NF_terms Q" by auto
    from first_step_subterm_qrsteps_ecap[OF ecap, OF pet stepsn[unfolded mv_xvar] NFs, unfolded map_vars_term_subt_at[OF pt, symmetric] mv_xvar[symmetric], OF neg] 
    show ?thesis .
  next
    assume no_NF: "?t \<notin> NF_terms Q"
    from no_NF lin_or_inn have inn: "NF_terms Q \<subseteq> NF_trs R" by auto
    from NF_instance[of ?t \<sigma>'] no_NF have "?t \<cdot> \<sigma>' \<notin> NF_terms Q" by auto
    with tp have no_NF: "t \<cdot> \<sigma>' |_ p \<notin> NF_terms Q" by simp
    from pt have pts: "p \<in> poss (t \<cdot> \<sigma>')" by auto
    from no_NF stepsn NFu pts inn
    show ?thesis unfolding tp[symmetric]
      by (rule reorder_steps_for_narrowing)
  qed
  then 
  obtain up m where step: "(?t \<cdot> \<sigma>' , up) \<in> ?QR" 
    and steps: "(replace_at (t \<cdot> \<sigma>') p up, u \<cdot> \<tau>) \<in> ?QR^^m"
    and m: "n = Suc m" by blast
  from pt have tp: "t \<cdot> \<sigma>' |_ p = ?t \<cdot> \<sigma>'" by auto
  from step[unfolded qrstep_qrstep_r_p_s_conv] obtain r p' \<sigma>'' where step: "(?t \<cdot> \<sigma>', up) \<in> qrstep_r_p_s nfs Q R r p' \<sigma>''"
    by auto
  have "t \<cdot> \<sigma>' = replace_at (t \<cdot> \<sigma>') p (t \<cdot> \<sigma>' |_ p)" using  ctxt_supt_id[OF pt\<sigma>] by simp
  also have "... = replace_at (t \<cdot> \<sigma>') p (?t \<cdot> \<sigma>')" using pt by simp
  finally have t\<sigma>: "t \<cdot> \<sigma>' = replace_at (t \<cdot> \<sigma>') p (?t \<cdot> \<sigma>')" .
  note step' = step[unfolded qrstep_r_p_s_def]
  from step' have p': "p' \<in> poss (?t \<cdot> \<sigma>')" by auto
  {
    assume "\<not> (p' \<in> poss ?t \<and> is_Fun (?t |_ p'))"
    from pos_into_subst[OF refl p' this]
    obtain q q' x where pq': "p' = q @ q'" and qt: "q \<in> poss ?t" and x: "?t |_ q = Var x" by auto
    from qrstep_subt_at_gen[OF step[unfolded pq']] have "(Var x \<cdot> \<sigma>', up |_ q) \<in> qrstep_r_p_s nfs Q R r q' \<sigma>''"
      unfolding x[symmetric] using qt by auto
    then have qrstep: "(\<sigma>' x, up |_ q) \<in> ?QR" unfolding qrstep_qrstep_r_p_s_conv eval_term.simps by blast
    from lin_or_inn 
    have False
    proof 
      assume inn: "NF_terms Q \<subseteq> NF_trs R"
      from qrstep have step: "(\<sigma>' x, up |_q) \<in> ?R" by auto
      from qt have "?t \<unrhd> ?t |_ q" by (rule subt_at_imp_supteq)
      with x have "?t \<unrhd> Var x" by auto
      then have "x \<in> vars_term ?t" by (rule subteq_Var_imp_in_vars_term)
      with var_cond have "x \<in> vars_term s" by auto
      then have "Var x \<unlhd> s" by auto
      then have "Var x \<cdot> \<sigma>' \<unlhd> s \<cdot> \<sigma>'" by (rule supteq_subst)
      from NF_subterm[OF _ this] NF 
      have "\<sigma>' x \<in> NF_terms Q" by simp
      with inn have no_step: "\<sigma>' x \<in> NF_trs R" by auto
      from step no_step show False by auto
    next
      assume "linear_term t \<and> Q = {}"
      then have lin: "linear_term t" and Q: "NF_terms Q = UNIV" by auto
      obtain \<delta> where delta: "\<delta> \<equiv> \<lambda> y. if y = x then up |_ q else \<sigma>' y" by auto
      have id': "replace_at (t \<cdot> \<sigma>') (p @ q) (up |_ q) = t \<cdot> \<delta>"
      proof (rule linear_term_replace_in_subst[OF lin])
        show "p @ q \<in> poss t" using pt qt by simp
      next
        show "t |_ (p @ q) = Var x" unfolding x[symmetric] using pt by simp
      qed (insert delta, auto)
      have id: "replace_at (t \<cdot> \<sigma>') p up = t \<cdot> \<delta>" unfolding id'[symmetric]
        unfolding ctxt_of_pos_term_append[OF pt\<sigma>]
          ctxt_ctxt_compose
      proof (unfold ctxt_eq)
        from qrstep_r_p_s_imp_poss[OF step] have p'u: "p' \<in> poss up" by auto
        note step' = step'[unfolded pq']
        from qt have qt\<sigma>: "q \<in> poss (?t \<cdot> \<sigma>')" by simp
        from step' have "up = replace_at (?t \<cdot> \<sigma>') (q @ q') (snd r \<cdot> \<sigma>'')"
          by simp
        also have "... = replace_at (t \<cdot> \<sigma>' |_ p) q (up |_ q)" unfolding tp
          ctxt_of_pos_term_append[OF qt\<sigma>]
          ctxt_ctxt_compose
          ctxt_eq
        proof -
          have "up |_ q = ( (ctxt_of_pos_term (q @ q') (t |_ p \<cdot> \<sigma>'))\<langle>snd r \<cdot> \<sigma>''\<rangle>) |_ q" using step' by simp
          from this[unfolded ctxt_of_pos_term_append[OF qt\<sigma>]]
          have "up |_ q = (replace_at (?t \<cdot> \<sigma>') q (replace_at (?t \<cdot> \<sigma>' |_ q) q' (snd r \<cdot> \<sigma>''))) |_ q" by simp
          also have "... = replace_at (?t \<cdot> \<sigma>' |_ q) q' (snd r \<cdot> \<sigma>'')"
            by (rule replace_at_subt_at[OF qt\<sigma>])
          finally show "replace_at (?t \<cdot> \<sigma>' |_ q) q' (snd r \<cdot> \<sigma>'') = up |_ q"
            by simp
        qed
        finally 
        show "up = replace_at (t \<cdot> \<sigma>' |_ p) q (up |_ q)" .
      qed
      {
        fix y
        have "(\<sigma> y, \<delta> y) \<in> ?QR^*"
          by (rule rtrancl_trans[OF \<sigma>steps], unfold delta, insert qrstep, auto)
      } note \<sigma>steps = this
      have "?\<sigma>prop m \<delta>"
        by (intro allI conjI, rule \<sigma>steps, unfold Q, insert steps[unfolded id], auto)
      then have mprop: "?\<sigma>propex m" by blast
      from m have "m < n" by auto
      from not_less_Least[OF this[unfolded n]] mprop
      show False ..
    qed        
  } 
  then have p': "p' \<in> poss ?t" and is_fun: "is_Fun (?t |_ p')" by auto
  from qrstep_instance_imp_qnarrows[OF step p' is_fun]
  obtain \<mu> \<delta> w where narrow: "(?t,w) \<in> qnarrows_r_p_s nfs Q R r p' \<mu>" and t: "?t \<cdot> \<sigma>' = ?t \<cdot> \<mu> \<cdot> \<delta>"
    and up: "up = w \<cdot> \<delta>" and \<sigma>: "\<sigma>' = \<mu> \<circ>\<^sub>s \<delta>" by auto
  let ?t' = "replace_at (t \<cdot> \<mu>) p w"
  from NF[unfolded \<sigma>] have "s \<cdot> \<mu> \<cdot> \<delta> \<in> NF_terms Q" by auto
  from narr[OF narrow NF_instance[OF this]] obtain s' t' where mem: "(s',t') \<in> sts" and inst: "instance_rule (s \<cdot> \<mu>, ?t') (s',t')"
    and choice: "\<not> nfs \<or> Q = {} \<or> wf_rule (s',t')"
    by auto
  from inst[unfolded instance_rule_def] obtain \<gamma> where id: "s \<cdot> \<mu> = s' \<cdot> \<gamma>" "?t' = t' \<cdot> \<gamma>" by auto
  have s\<sigma>: "s \<cdot> \<sigma>' = s' \<cdot> \<gamma> \<circ>\<^sub>s \<delta>" unfolding subst_subst_compose \<sigma> id by simp
  show ?thesis
  proof (intro exI conjI, rule mem)
    show "(s \<cdot> \<sigma>, s' \<cdot> (\<gamma> \<circ>\<^sub>s \<delta>)) \<in> ?QR^*"
      by (rule rtrancl_trans[OF \<sigma>steps_term], unfold s\<sigma>, simp)
  next
    have NF: "s' \<cdot> \<gamma> \<circ>\<^sub>s \<delta> \<in> NF_terms Q"  unfolding s\<sigma>[symmetric] using NF_set by auto
    show "s' \<cdot> \<gamma> \<circ>\<^sub>s \<delta> \<in> NF_terms Q" by fact
    show "NF_subst nfs (s',t') (\<gamma> \<circ>\<^sub>s \<delta>) Q"
    proof (cases "\<not> nfs \<or> Q = {}")
      case True
      then show ?thesis by auto
    next
      case False
      with choice have "wf_rule (s',t')" by auto
      from this[unfolded wf_rule_def] have vars: "vars_term t' \<subseteq> vars_term s'" by auto 
      show ?thesis
      proof
        fix x
        assume nfs and "x \<in> vars_term s' \<or> x \<in> vars_term t'"
        with vars have "x \<in> vars_term s'" by auto
        then have "s' \<unrhd> Var x" by auto
        from NF_subterm[OF NF supteq_subst[OF this]]
        show "(\<gamma> \<circ>\<^sub>s \<delta>) x \<in> NF_terms Q" unfolding subst_compose_def by simp
      qed
    qed
  next
    from step[unfolded up] have step: "(?t \<cdot> \<sigma>', w \<cdot> \<delta>) \<in> ?QR" unfolding qrstep_qrstep_r_p_s_conv by blast
    from pt have pt\<mu>: "p \<in> poss (t \<cdot> \<mu>)" by auto
    have "t \<cdot> \<sigma>' = replace_at (t \<cdot> \<sigma>') p (?t \<cdot> \<sigma>')" by (rule t\<sigma>)
    also have "(..., replace_at (t \<cdot> \<sigma>') p (w \<cdot> \<delta>)) \<in> ?QR" (is "(_,?t'') \<in> _")
      using step by auto
    also have "?t'' = t' \<cdot> \<gamma> \<cdot> \<delta>" unfolding id[symmetric] \<sigma> using pt
      by (simp add: ctxt_of_pos_term_subst)
    finally show "(t \<cdot> \<sigma>, t' \<cdot> \<gamma> \<circ>\<^sub>s \<delta>) \<in> ?QR^*" using \<sigma>steps_term[of t] by auto
  next
    have "(t' \<cdot> \<gamma> \<cdot> \<delta>, u \<cdot> \<tau>) \<in> ?QR^*" 
      using relpow_imp_rtrancl[OF steps] pt unfolding id[symmetric] \<sigma> up
      by (simp add: ctxt_of_pos_term_subst)
    then show "(t' \<cdot> (\<gamma> \<circ>\<^sub>s \<delta>), u \<cdot> \<tau>) \<in> ?QR^*"
      by simp
  qed
qed

lemma narrowing_proc: fixes R Rw P Pw :: "('f,string)trs"
  assumes fin: "finite_dpp (nfs,m,replace (s,t) sts P, replace (s,t) sts Pw, Q, R, Rw)"
  and lin_or_inn: "linear_term t \<and> Q = {} \<or> NF_terms Q \<subseteq> NF_trs (R \<union> Rw)"
  and varcond: "vars_term (t |_ p) \<subseteq> vars_term s"
  and precond: "\<And> u v. t |_ p \<in> NF_terms Q \<Longrightarrow> ((s,t),(u,v)) \<in> DG nfs m (P \<union> Pw) Q (R \<union> Rw) \<Longrightarrow> p \<in> poss u \<and> (\<forall> \<mu>1 \<mu>2. 
  mgu_vd_string (t |_ p) (u |_ p) = Some (\<mu>1,\<mu>2) \<longrightarrow>
  \<not> {s \<cdot> \<mu>1, u \<cdot> \<mu>2} \<subseteq> NF_terms Q)"
  and strict: "(s,t) \<in> P \<or> R = {}"
  and narr: "\<And> r q t' \<mu>. (t |_ p,t') \<in> qnarrows_r_p_s nfs Q (R \<union> Rw) r q \<mu> \<Longrightarrow> s \<cdot> \<mu> \<in> NF_terms Q \<Longrightarrow> \<exists> st' \<in> sts. 
    instance_rule (s \<cdot> \<mu>, replace_at (t \<cdot> \<mu>) p t') st' \<and> (\<not> nfs \<or> Q = {} \<or> wf_rule st')"
  and pt: "p \<in> poss t"
  and pet: "p \<in> poss (ecap (R \<union> Rw) Q {mv_xvar s} (mv_xvar t)) \<or> t |_ p \<notin> NF_terms Q" 
  and ecap: "is_ecap ecap"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
  unfolding finite_dpp_def
proof (intro notI, elim exE)
  fix s' t' \<sigma>'
  assume mc: "min_ichain (nfs,m,P, Pw, Q, R, Rw) s' t' \<sigma>'"
  let ?P = "replace (s,t) sts P"
  let ?Pw = "replace (s,t) sts Pw"
  let ?QR = "qrstep nfs Q (R \<union> Rw)"
  have "\<exists> s' t' \<sigma>'. min_ichain (nfs,m,?P, ?Pw, Q, R, Rw) s' t' \<sigma>'"
  proof (rule ichain_narrowing_replacement[OF mc strict])
    fix i
    assume "(s' i, t' i) = (s,t)"    
    then have id: "s = s' i" "t = t' i" by auto
    note mc = mc[unfolded min_ichain.simps ichain.simps minimal_cond_def, simplified]
    from mc have NF: "{s' i \<cdot> \<sigma>' i, s' (Suc i) \<cdot> \<sigma>' (Suc i)} \<subseteq> NF_terms Q" by auto
    from mc have nfs: "NF_subst nfs (s' i, t' i)  (\<sigma>' i) Q" "NF_subst nfs (s' (Suc i), t' (Suc i))  (\<sigma>' (Suc i)) Q"  by auto
    from mc have steps: "(t' i \<cdot> \<sigma>' i, s' (Suc i) \<cdot> \<sigma>' (Suc i)) \<in> ?QR^*" by auto    
    from mc have mem: "(s' (Suc i), t' (Suc i)) \<in> P \<union> Pw" "(s' i, t' i) \<in> P \<union> Pw" by auto
    from mc have SN: "m \<Longrightarrow> SN_on ?QR {t' i \<cdot> \<sigma>' i}" by simp
    from varcond have vc: "vars_term (t' i |_ p) \<subseteq> vars_term (s' i)" unfolding id .
    let ?Pr = "\<lambda> s t \<tau>. (s,t) \<in> sts \<and> (s' i \<cdot> \<sigma>' i, s \<cdot> \<tau>) \<in> ?QR^* \<and> s \<cdot> \<tau> \<in> NF_terms Q \<and> NF_subst nfs (s,t) \<tau> Q \<and> (t' i \<cdot> \<sigma>' i, t \<cdot> \<tau>) \<in> ?QR^* \<and> (t \<cdot> \<tau>, s' (Suc i) \<cdot> \<sigma>' (Suc i)) \<in> ?QR^*"
    have "((s,t),(s' (Suc i), t' (Suc i))) \<in> DG nfs m (P \<union> Pw) Q (R \<union> Rw)"
      unfolding DG_def id using mem steps nfs NF SN by auto
    note precond = precond[OF _ this]
    have "\<exists> s t \<tau>. ?Pr s t \<tau>" 
      by (rule narrowing_technique[OF steps lin_or_inn[unfolded id] NF nfs(1) vc precond[unfolded id] narr[unfolded id] pt[unfolded id] pet[unfolded id] ecap])
    then obtain s t \<tau> where "?Pr s t \<tau>" by blast
    then have "?Pr s t \<tau>" by auto
    then show "\<exists> s t \<tau>. ?Pr s t \<tau> " by blast
  qed
  with fin show False unfolding finite_dpp_def ..
qed

lemma narrowing_complete_proc: fixes R Rw P Pw :: "('f,string)trs"
  assumes infin: "infinite_dpp (nfs,replace (s,t) sts P, Q, R)"
  and full_or_inn: "Q = {} \<or> NF_terms Q \<subseteq> NF_trs R"
  and ecap: "is_ecap ecap"
  and wf: "\<And> l r. Q \<noteq> {} \<Longrightarrow> nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  and t_inn: "Q \<noteq> {} \<Longrightarrow> is_Fun t \<and> \<not> defined R (the (root t))"
  and s_inn: "Q \<noteq> {} \<Longrightarrow> is_Fun s"
  and narr: "\<And> s' t'. (s',t') \<in> sts \<Longrightarrow> \<exists> lr p \<mu> \<sigma>. 
    s' = s \<cdot> \<mu> \<and>
    (t \<cdot> \<mu>,t') \<in> rstep_r_p_s R lr p \<sigma> \<and>
    (Q \<noteq> {} \<longrightarrow> (\<exists> U. R_Q_U_ecap.rewrite_common_preconditions R U Q ecap s' (args s') (args (t \<cdot> \<mu> |_ p)) (t \<cdot> \<mu>) t' lr p nfs False
      \<and> (\<forall> v. t \<cdot> \<mu> |_ p \<rhd> v \<longrightarrow> nfc R Q (set (args (s \<cdot> \<mu>))) v nfs)))"
  and wf_st: "Q \<noteq> {} \<Longrightarrow> nfs \<Longrightarrow> wf_rule (s,t)"
  shows "infinite_dpp (nfs,P,Q,R)"
proof -
  let ?QR = "qrstep nfs Q R"
  let ?P = "replace (s,t) sts P"
  let ?ndpp = "(nfs,?P,Q,R)"
  let ?dpp = "(nfs,P,Q,R)"
  show ?thesis
  proof (cases "SN ?QR")
    case True
    note SN = this
    with infin obtain ss ts \<sigma> where chain: "i_chain ?ndpp ss ts \<sigma>" by auto
    note chain = chain[simplified]
    from chain have NF: "\<And> i. set (args (ss i \<cdot> \<sigma> i)) \<subseteq> NF_terms Q" 
      using NF_terms_args_conv[of _ Q] by blast
    {
      fix i
      assume nmem: "(ss i, ts i) \<notin> P"
      from chain have steps: "(ts i \<cdot> \<sigma> i, ss (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^*" by auto
      from chain have "(ss i, ts i) \<in> ?P" by simp
      with nmem have st: "(s,t) \<in> P" and sts: "(ss i, ts i) \<in> sts" unfolding replace_def 
        by ((cases "(s,t) \<in> P", auto)+)
      from narr[OF sts] obtain lr p \<mu> \<tau> U where 
        s: "ss i = s \<cdot> \<mu>" and step: "(t \<cdot> \<mu>, ts i) \<in> rstep_r_p_s R lr p \<tau>" and 
        inn: "Q \<noteq> {} \<Longrightarrow> R_Q_U_ecap.rewrite_common_preconditions R U Q ecap (ss i) (args (ss i)) (args (t \<cdot> \<mu> |_ p)) (t \<cdot> \<mu>) (ts i) lr p nfs False"
        and nfc: "\<And> v. Q \<noteq> {} \<Longrightarrow> t \<cdot> \<mu> |_ p \<rhd> v \<Longrightarrow> nfc R Q (set (args (s \<cdot> \<mu>))) v nfs"
        by blast
      define \<delta> where "\<delta> = \<mu> \<circ>\<^sub>s \<sigma> i"
      from s have id: "ss i \<cdot> \<sigma> i = s \<cdot> \<delta>" unfolding \<delta>_def by simp
      obtain l r where lr: "lr = (l,r)" by force
      have steps: "(t \<cdot> \<delta>, ss (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^*"
      proof (cases "Q = {}")
        case True
        from step have "(t \<cdot> \<mu>, ts i) \<in> rstep R" unfolding rstep_iff_rstep_r_p_s lr by blast
        then have "(t \<cdot> \<delta>, ts i \<cdot> \<sigma> i) \<in> rstep R" unfolding \<delta>_def by auto
        with True have step: "(t \<cdot> \<delta>, ts i \<cdot> \<sigma> i) \<in> ?QR" by auto
        from step steps show ?thesis by auto
      next
        case False
        note inn = inn[OF False, unfolded lr]
        note nfc = nfc[OF False, folded s]
        from full_or_inn False have "NF_terms Q \<subseteq> NF_trs R" by auto
        then interpret R_Q_U_ecap R U Q ecap using ecap by (unfold_locales, auto)
        from t_inn[OF False] have ndef: "\<not> defined R (the (root (t \<cdot> \<mu>)))" by (cases t, auto)
        from s_inn[OF False] have sf: "is_Fun (ss i)" unfolding s by auto
        show ?thesis using rewriting_complete[OF inn step[unfolded lr] steps NF NF sf nfc SN wf[OF False] ndef] unfolding \<delta>_def by auto
      qed
      from id steps st have "\<exists> \<delta>. (t \<cdot> \<delta>, ss (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^* \<and> ss i \<cdot> \<sigma> i = s \<cdot> \<delta> \<and> (s,t) \<in> P" by blast
    } note main = this
    have "\<forall> i. \<exists> \<delta>. (ss i, ts i) \<notin> P \<longrightarrow> (t \<cdot> \<delta>, ss (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^* \<and> ss i \<cdot> \<sigma> i = s \<cdot> \<delta> \<and> (s,t) \<in> P" 
      using main by blast
    from choice[OF this] obtain \<delta> where 
      delta: "\<And> i. (ss i, ts i) \<notin> P \<Longrightarrow> (t \<cdot> \<delta> i, ss (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^* \<and> ss i \<cdot> \<sigma> i = s \<cdot> \<delta> i \<and> (s,t) \<in> P" 
      by blast
    define ss' where "ss' = (\<lambda> i. if (ss i, ts i) \<in> P then ss i else s)"
    define ts' where "ts' = (\<lambda> i. if (ss i, ts i) \<in> P then ts i else t)"
    define \<sigma>' where "\<sigma>' = (\<lambda> i. if (ss i, ts i) \<in> P then \<sigma> i else \<delta> i)"
    note id = ss'_def ts'_def \<sigma>'_def
    {
      fix i
      have "ss' i \<cdot> \<sigma>' i = ss i \<cdot> \<sigma> i"
        by (cases "(ss i, ts i) \<in> P", insert delta[of i], auto simp: id)
    } note lhs = this
    have "i_chain ?dpp ss' ts' \<sigma>'" unfolding i_chain.simps lhs NF_terms_args_conv[symmetric]
    proof (intro conjI allI impI)
      fix i
      from chain have "(ss i, ts i) \<in> ?P" by auto
      then show "(ss' i, ts' i) \<in> P" unfolding id replace_def by (cases "(s,t) \<in> P", auto)
      from chain have steps: "(ts i \<cdot> \<sigma> i, ss (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^*" by auto
      then show "(ts' i \<cdot> \<sigma>' i, ss (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^*"
        by (cases "(ss i, ts i) \<in> P", insert delta[of i], auto simp: id)
      show "\<forall>u\<in>set (args (ss i \<cdot> \<sigma> i)). u \<in> NF_terms Q" using NF by auto
      show "NF_subst nfs (ss' i, ts' i) (\<sigma>' i) Q" 
      proof (cases "(ss i,ts i) \<in> P")
        case True
        from chain show ?thesis unfolding id using True by auto
      next
        case False
        with id have id: "ss' i = s" "ts' i = t" "\<sigma>' i = \<delta> i" by auto
        note NF = NF[of i, folded lhs]
        show ?thesis
          by (rule NF_subst_from_NF_args[OF _ NF], unfold id, rule wf_st)
      qed
    qed 
    then show ?thesis unfolding infinite_dpp.simps by blast
  qed auto
qed
  
end

