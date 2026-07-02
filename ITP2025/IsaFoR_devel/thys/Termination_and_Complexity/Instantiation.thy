(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Instantiation
  imports
    TRS.QDP_Framework
    Innermost_Usable_Rules
    Dependency_Graph
begin

lemma ichain_instantiation: fixes s t \<sigma> f Q nfs
  defines Pr: "Pr \<equiv> \<lambda> P' i s' t' \<sigma>'. s i \<cdot> \<sigma> i = s' \<cdot> \<sigma>' \<and> t i \<cdot> \<sigma> i = t' \<cdot> \<sigma>' \<and> 
    instance_rule (s',t') (s i, t i) \<and> (s',t') \<in> f P'"
  assumes ichain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and main: "\<And> i P'. i \<ge> n \<Longrightarrow> (s i, t i) \<in> P' \<Longrightarrow> \<exists> s' t' \<sigma>'. Pr P' i s' t' \<sigma>'"
  shows "\<exists> s' t' \<sigma>'. min_ichain (nfs,m,f P, f Pw, Q, R, Rw) s' t' \<sigma>'"
proof -
  let ?QR = "(qrstep nfs Q (R \<union> Rw))^*"
  note ichain = ichain[unfolded min_ichain.simps ichain.simps minimal_cond_def]
  let ?s = "fst"
  let ?t = "fst o snd"
  let ?\<sigma> = "snd o snd"
  let ?Q = "\<lambda> P i st\<sigma>. Pr P i (?s st\<sigma>) (?t st\<sigma>) (?\<sigma> st\<sigma>)"
  let ?st\<sigma> = "\<lambda> i. if (s i, t i) \<in> P 
    then (SOME st\<sigma>. ?Q P i st\<sigma>)
    else (SOME st\<sigma>. ?Q Pw i st\<sigma>)"
  obtain st\<sigma> where st\<sigma>: "st\<sigma> = (\<lambda> i. ?st\<sigma> (i + n))" by auto
  let ?fP = "f P"
  let ?fPw = "f Pw"
  obtain sr where sr: "sr = ?s o st\<sigma>" by auto
  obtain tr where tr: "tr = ?t o st\<sigma>" by auto
  obtain \<sigma>r where \<sigma>r: "\<sigma>r = ?\<sigma> o st\<sigma>" by auto
  {
    fix i
    assume mem: "(s (i + n), t (i + n)) \<in> P"
    from main[OF _ mem] 
    obtain s' t' \<sigma>' where P: "Pr P (i + n) s' t' \<sigma>'" by auto
    let ?st\<sigma>' = "(s',t',\<sigma>')" 
    from P have Q: "?Q P (i + n) ?st\<sigma>'" by simp
    from someI[of "?Q P (i + n)" ?st\<sigma>', OF Q]
    have "?Q P (i + n) (st\<sigma> i)" unfolding st\<sigma> using mem by simp
  } note P = this
  {
    fix i
    assume nomem: "(s (i + n), t (i + n)) \<notin> P"
    with ichain have mem: "(s (i + n), t (i + n)) \<in> Pw" by auto
    from main[OF _ mem] 
    obtain s' t' \<sigma>' where P: "Pr Pw (i + n) s' t' \<sigma>'" by auto
    let ?st\<sigma>' = "(s',t',\<sigma>')" 
    from P have Q: "?Q Pw (i + n) ?st\<sigma>'" by simp
    from someI[of "?Q Pw (i + n)" ?st\<sigma>', OF Q]
    have "?Q Pw (i + n) (st\<sigma> i)" unfolding st\<sigma> using nomem by simp
  } note Pw = this
  {
    fix i
    have ids: "sr i \<cdot> \<sigma>r i = s (i + n) \<cdot> \<sigma> (i + n)"
      using P[of i] Pw[of i] unfolding sr tr \<sigma>r Pr by (cases "(s (i + n), t (i + n)) \<in> P", auto)
    have idt: "tr i \<cdot> \<sigma>r i = t (i + n) \<cdot> \<sigma> (i + n)"
      using P[of i] Pw[of i] unfolding sr tr \<sigma>r Pr by (cases "(s (i + n), t (i + n)) \<in> P", auto)
    have mem: "(sr i, tr i) \<in> ?fP \<union> ?fPw"
      using P[of i] Pw[of i] unfolding sr tr \<sigma>r Pr by (cases "(s (i + n), t (i + n)) \<in> P", auto)
    have strict: "(s (i + n), t (i + n)) \<in> P \<Longrightarrow> (sr i, tr i) \<in> ?fP"
      using P[of i] unfolding sr tr Pr by auto
    from ichain have nfs: "NF_subst nfs (s (i + n), t (i + n)) (\<sigma> (i + n)) Q" by auto
    from P[of i] Pw[of i] have "instance_rule (sr i, tr i) (s (i+n), t (i + n))" unfolding sr tr Pr by auto
    from this[unfolded instance_rule_def] obtain \<gamma> where id: "sr i = s (i + n) \<cdot> \<gamma>" "tr i = t (i + n) \<cdot> \<gamma>" by auto
    from ids id have ids': "s (i+n) \<cdot> (\<gamma> \<circ>\<^sub>s \<sigma>r i) = s (i+n) \<cdot> \<sigma> (i+ n)" by auto
    from idt id have idt': "t (i+n) \<cdot> (\<gamma> \<circ>\<^sub>s \<sigma>r i) = t (i+n) \<cdot> \<sigma> (i+ n)" by auto
    from term_subst_eq_rev[OF ids'] term_subst_eq_rev[OF idt']
    have id_subst: "\<And> y. y \<in> vars_rule (s (i+n), t(i+ n)) \<Longrightarrow> (\<gamma> \<circ>\<^sub>s \<sigma>r i) y = \<sigma> (i + n) y" 
      unfolding vars_rule_def by auto
    have nfs: "NF_subst nfs (sr i, tr i) (\<sigma>r i) Q" 
    proof
      fix x 
      assume nfs and x: "x \<in> vars_term (sr i) \<or> x \<in> vars_term (tr i)"
      from x obtain y where y: "y \<in> vars_rule (s (i + n),t (i + n))" and x: "x \<in> vars_term (\<gamma> y)"
        unfolding id vars_rule_def vars_term_subst by auto      
      from nfs[unfolded NF_subst_def] \<open>nfs\<close> y have "\<sigma> (i + n) y \<in> NF_terms Q" by auto
      from this[unfolded id_subst[OF y, symmetric] subst_compose_def] have NF: "\<gamma> y \<cdot> \<sigma>r i \<in> NF_terms Q" .
      from x have "\<gamma> y \<unrhd> Var x" by auto
      from NF_subterm[OF NF supteq_subst[OF this, of "\<sigma>r i"]]
      show "\<sigma>r i x \<in> NF_terms Q" by simp
    qed      
    note ids idt mem strict nfs
  } note main = this
  have "min_ichain (nfs,m,?fP,?fPw,Q,R,Rw) sr tr \<sigma>r"
    unfolding min_ichain.simps ichain.simps minimal_cond_def 
    unfolding INFM_disj_distrib[symmetric]
  proof (intro conjI)
    let ?S = "?QR O qrstep nfs Q R O ?QR"
    let ?orig = "\<lambda> i. (s i, t i) \<in> P \<or> (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?S"
    let ?new = "\<lambda> i. (sr i, tr i) \<in> ?fP \<or> (tr i \<cdot> \<sigma>r i, sr (Suc i) \<cdot> \<sigma>r (Suc i)) \<in> ?S"
    from ichain 
    have inf: "(INFM i. ?orig i)" unfolding INFM_disj_distrib by simp
    show "(INFM i. ?new i)"
      unfolding INFM_nat_le
    proof
      fix m
      from inf[unfolded INFM_nat_le, rule_format, of "m + n"] obtain n' where n': "n' \<ge> m + n"
        and orig: "?orig n'" by blast
      from n' have "\<exists> k. n' = k + n \<and> k \<ge> m" by arith
      then obtain k where n': "n' = k + n" and k: "k \<ge> m" by blast
      from main[of k] main[of "Suc k"] orig[unfolded n'] have "?new k"
        by auto
      with k show "\<exists> k \<ge> m. ?new k" by blast
    qed
  qed (insert main ichain, auto)
  then show ?thesis by blast
qed


lemma instantiation_proc: fixes R Rw P Pw :: "('f,string)trs"
  assumes ecap: "is_ecap ecap"
  and fin: "finite_dpp (nfs,m,replace (s,t) sts P, replace (s,t) sts Pw, Q, R, Rw)"
  and main: "\<And> u v \<mu>. 
  (u,v) \<in> P \<union> Pw \<Longrightarrow> ((u,v),(s,t)) \<in> DG nfs m (P \<union> Pw) Q (R \<union> Rw) \<Longrightarrow>
  mgu_class (ecap (R \<union> Rw) Q (mv_xvar ` {u}) (mv_xvar v)) s = Some \<mu> \<Longrightarrow> 
  mv_yvar s \<cdot> \<mu> \<in> NF_terms Q \<Longrightarrow>
  mv_xvar u \<cdot> \<mu> \<in> NF_terms Q \<Longrightarrow>
  \<exists> (s',t') \<in> sts. instance_rule (s',t') (s,t) \<and> instance_rule (mv_yvar s \<cdot> \<mu>, mv_yvar t \<cdot> \<mu>) (s',t')"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
  unfolding finite_dpp_def
proof (clarify)
  fix si ti \<sigma>i
  assume min_ichain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) si ti \<sigma>i"
  let ?P = "\<lambda> P' i s' t' \<sigma>'. si i \<cdot> \<sigma>i i = s' \<cdot> \<sigma>' \<and> ti i \<cdot> \<sigma>i i = t' \<cdot> \<sigma>' \<and> 
    instance_rule (s',t') (si i, ti i) \<and>
    (s',t') \<in> replace (s,t) sts P'"
  let ?QR = "(qrstep nfs Q (R \<union> Rw))^*"
  note ichain = min_ichain[unfolded min_ichain.simps ichain.simps minimal_cond_def]
  from ichain have P: "\<And> i. (si i, ti i) \<in> P \<union> Pw" by auto
  from ichain have NF: "\<And> i. si i \<cdot> \<sigma>i i \<in> NF_terms Q" by auto  
  from ichain have nfs: "\<And> i. NF_subst nfs (si i, ti i) (\<sigma>i i) Q" by auto  
  from ichain have min: "\<And> i. m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {ti i \<cdot> \<sigma>i i}" by auto
  from ichain have steps: "\<And> i. (ti i \<cdot> \<sigma>i i, si (Suc i) \<cdot> \<sigma>i (Suc i)) \<in> ?QR" by auto
  {
    fix P' and i :: nat
    assume i: "i \<ge> Suc 0" and pair: "(si i, ti i) \<in> P'"
    have "\<exists> s' t' \<sigma>'. ?P P' i s' t' \<sigma>'"
    proof (cases "(si i, ti i) = (s,t)")
      case False
      from instance_rule_refl[of "(si i, ti i)"] False pair
      show ?thesis unfolding replace_def instance_rule_def by auto
    next
      case True
      then have True: "si i = s" "ti i = t" by auto
      from i obtain j where i: "i = Suc j" by (cases i, auto)
      note inst = ecap_steps_mgu[OF ecap]
      note main = main[OF P[of j]]
      note DG = DG_I[OF P[of j] P[of "Suc j"] steps[of j] NF NF nfs nfs min]
      from DG have "((si j, ti j), (s, t)) \<in> DG nfs m (P \<union> Pw) Q (R \<union> Rw)" unfolding i True[symmetric] .
      note main = main[OF this]
      from NF[of j] have "{si j} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>i j \<subseteq> NF_terms Q" by simp
      note inst = inst[OF this]
      from steps[of j] have "(ti j \<cdot> \<sigma>i j, si i \<cdot> \<sigma>i i) \<in> ?QR" unfolding i by simp
      with True have "(ti j \<cdot> \<sigma>i j, s \<cdot> \<sigma>i i) \<in> ?QR" by auto
      note inst = inst[OF this]
      from inst obtain \<mu> \<delta> where 
        mgu: "mgu_class (ecap (R \<union> Rw) Q (mv_xvar ` {si j}) (mv_xvar (ti j))) s = Some \<mu>"
        and \<sigma>j: "\<And> s. s \<cdot> \<sigma>i j = mv_xvar s \<cdot> \<mu> \<cdot> \<delta>"
        and \<sigma>i: "\<And> s. s \<cdot> \<sigma>i i = mv_yvar s \<cdot> \<mu> \<cdot> \<delta>" by blast
      note main = main[OF mgu]
      from nfs[of i] have nfs: "NF_subst nfs (si i, ti i) (\<sigma>i i) Q" .
      from NF[of i] have "si i \<cdot> \<sigma>i i \<in> NF_terms Q" .
      then have NF2: "s \<cdot> \<sigma>i i \<in> NF_terms Q" unfolding True .
      from NF_instance[OF NF2[unfolded \<sigma>i]] have "mv_yvar s \<cdot> \<mu> \<in> NF_terms Q" .      
      note main = main[OF this]
      from NF_instance[OF NF[of j, unfolded \<sigma>j]] have "mv_xvar (si j) \<cdot> \<mu> \<in> NF_terms Q" .
      note main = main[OF this]      
      from main obtain s' t' where st': "(s',t') \<in> sts" and inst: "instance_rule (mv_yvar s \<cdot> \<mu>, mv_yvar t \<cdot> \<mu>) (s',t')" 
        and inst2: "instance_rule (s', t') (s, t)" by auto
      from pair True st' have mem: "(s',t') \<in> replace (s,t) sts P'" unfolding replace_def by auto
      from inst[unfolded instance_rule_def] obtain \<tau> where id: 
        "mv_yvar s \<cdot> \<mu> = s' \<cdot> \<tau>" "mv_yvar t \<cdot> \<mu> = t' \<cdot> \<tau>" by auto
      show ?thesis unfolding True \<sigma>i id
      proof (intro exI conjI impI)
        show "s' \<cdot> \<tau> \<cdot> \<delta> = s' \<cdot> (\<tau> \<circ>\<^sub>s \<delta>)" by simp
        show "(s',t') \<in> replace (s,t) sts P'" by fact
      qed (insert inst2, auto)
    qed
  } note main = this
  let ?RP = "replace (s,t) sts P"
  let ?RPw = "replace (s,t) sts Pw"
  from ichain_instantiation[OF min_ichain main, of "Suc 0" "\<lambda> x. x"]
  have "\<exists> s' t' \<sigma>'. min_ichain (nfs,m,?RP, ?RPw, Q, R, Rw) s' t' \<sigma>'" by blast
  with fin show False unfolding finite_dpp_def by blast
qed

lemma forward_instantiation_proc: fixes R Rw P Pw :: "('f,string)trs" and ecap Q U
  defines urc: "urc \<equiv> is_ur_closed_term_mv' (R \<union> Rw) U Q ecap full_af"
  assumes ecap: "is_ecap ecap"
  and U_None: "U_opt = None \<Longrightarrow> U = R \<union> Rw"
  and U_Some: "U_opt = Some U \<Longrightarrow> (\<not> nfs \<longrightarrow> vars_term t \<subseteq> vars_term s) \<and> (\<not> nfs \<longrightarrow> m) \<and> NF_terms Q \<subseteq> NF_trs (R \<union> Rw) \<and> urc {s} t \<and> (\<forall> (l,r) \<in> U. urc (set (args l)) r)"
  and U_opt: "U_opt = None \<or> U_opt = Some U"
  and fin: "finite_dpp (nfs,m,replace (s,t) sts P, replace (s,t) sts Pw, Q, R, Rw)"
  and main: "\<And> u v \<mu>. 
  (u,v) \<in> P \<union> Pw \<Longrightarrow> ((s,t),(u,v)) \<in> DG nfs m (P \<union> Pw) Q (R \<union> Rw) \<Longrightarrow>
  mgu_class (ecap (U^-1) {} {} (mv_xvar u)) t = Some \<mu> \<Longrightarrow> 
  mv_yvar s \<cdot> \<mu> \<in> NF_terms Q \<Longrightarrow>
  mv_xvar u \<cdot> \<mu> \<in> NF_terms Q \<Longrightarrow>
  \<exists> (s',t') \<in> sts. instance_rule (s',t') (s,t) \<and> instance_rule (mv_yvar s \<cdot> \<mu>, mv_yvar t \<cdot> \<mu>) (s',t')"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
  unfolding finite_dpp_def
proof (clarify)
  fix si ti \<sigma>i
  assume min_ichain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) si ti \<sigma>i"
  let ?P = "\<lambda> P' i s' t' \<sigma>'. si i \<cdot> \<sigma>i i = s' \<cdot> \<sigma>' \<and> ti i \<cdot> \<sigma>i i = t' \<cdot> \<sigma>' \<and> 
    instance_rule (s',t') (si i, ti i) \<and>
    (s',t') \<in> replace (s,t) sts P'"
  let ?QR = "(qrstep nfs Q (R \<union> Rw))^*"
  note ichain = min_ichain[unfolded min_ichain.simps ichain.simps minimal_cond_def]
  from ichain have P: "\<And> i. (si i, ti i) \<in> P \<union> Pw" by auto
  from ichain have NF: "\<And> i. si i \<cdot> \<sigma>i i \<in> NF_terms Q" by auto  
  from ichain have nfs: "\<And> i. NF_subst nfs (si i, ti i) (\<sigma>i i) Q" by auto  
  from ichain have min: "\<And> i. m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {ti i \<cdot> \<sigma>i i}" by auto
  from ichain have steps: "\<And> i. (ti i \<cdot> \<sigma>i i, si (Suc i) \<cdot> \<sigma>i (Suc i)) \<in> ?QR" by auto
  let ?QU = "(qrstep nfs Q U)^*"
  let ?U = "(rstep U)^*"
  let ?U' = "(rstep (U^-1))^*"
  {
    fix P' and i :: nat
    assume pair: "(si i, ti i) \<in> P'"
    have "\<exists> s' t' \<sigma>'. ?P P' i s' t' \<sigma>'"
    proof (cases "(si i, ti i) = (s,t)")
      case False
      from instance_rule_refl[of "(si i, ti i)"] False pair 
      show ?thesis unfolding replace_def instance_rule_def by auto
    next
      case True
      then have True: "si i = s" "ti i = t" by auto
      note DG = DG_I[OF P[of i] P[of "Suc i"] steps NF NF nfs nfs min]
      from DG have DG: "((s, t),(si (Suc i), ti (Suc i))) \<in> DG nfs m (P \<union> Pw) Q (R \<union> Rw)" unfolding True .
      note inst = ecap_steps_mgu[OF ecap]
      note inst = inst[where Q = "{}" and S = "{}", unfolded qrstep_rstep_conv]
      have id: "?U^-1 = ?U'" unfolding rtrancl_converse[symmetric] rstep_converse ..
      from steps[of i] have "(ti i \<cdot> \<sigma>i i, si (Suc i) \<cdot> \<sigma>i (Suc i)) \<in> ?QR" .
      then have steps: "(t \<cdot> \<sigma>i i, si (Suc i) \<cdot> \<sigma>i (Suc i)) \<in> ?QR" (is "?ts \<in> _") unfolding True .
      from NF[of i, unfolded True] have NF: "s \<cdot> \<sigma>i i \<in> NF_terms Q" .
      from nfs[of i, unfolded True] have nfs: "NF_subst nfs (s,t) (\<sigma>i i) Q" .
      from U_opt
      have "?ts \<in> ?QU"
      proof
        assume "U_opt = None"
        from U_None[OF this] steps show ?thesis by auto
      next
        assume "U_opt = Some U"
        from U_Some[OF this] have inn: "NF_terms Q \<subseteq> NF_trs (R \<union> Rw)"
          and urct: "urc {s} t"
          and urcU: "\<And> l r. (l,r) \<in> U \<Longrightarrow> urc (set (args l)) r" 
          and nfs_m: "\<not> nfs \<Longrightarrow> m"
          and var_cond: "\<not> nfs \<Longrightarrow> vars_term t \<subseteq> vars_term s" by auto
        interpret R_Q_U_ecap "R \<union> Rw" U Q ecap
          by (unfold_locales, rule ecap, rule inn)
        from NF have NF: "{s} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>i i \<subseteq> NFQ" by auto
        from ichain have "m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {ti i \<cdot> \<sigma>i i}" by auto
        from this[unfolded True] have SN: "m \<Longrightarrow> wwf_qtrs Q (R \<union> Rw) \<or> SN_on (qrstep nfs Q (R \<union> Rw)) {t \<cdot> \<sigma>i i}" ..
        note urc = is_ur_closed_term[OF steps _ NF urcU[unfolded urc] subset_refl SN urct[unfolded urc]]
        {
          fix u
          assume "u \<in> \<sigma>i i ` vars_term t"
          then obtain x where x: "x \<in> vars_term t" and u: "u = \<sigma>i i x" by auto
          have "u \<in> NFQ"
          proof (cases nfs)
            case False
            from var_cond[OF False] x have x: "x \<in> vars_term s" by auto
            then have "s \<unrhd> Var x" by auto
            then have "s \<cdot> \<sigma>i i \<unrhd> Var x \<cdot> \<sigma>i i" by auto
            then have "s \<cdot> \<sigma>i i \<unrhd> \<sigma>i i x" by simp
            from NF_subterm[OF _ this] NF 
            show "u \<in> NFQ" unfolding u by auto
          next
            case True
            from nfs[unfolded NF_subst_def] True x
            show ?thesis unfolding u vars_rule_def by force
          qed
        }
        then have "\<sigma>i i ` vars_term t \<subseteq> NFQ" by auto
        from urc[OF this] nfs_m have "?ts \<in> (qrstep nfs Q ((R \<union> Rw) \<inter> U))^*" by blast
        then show ?thesis using rtrancl_mono[OF qrstep_mono[OF _ subset_refl]] by blast
      qed
      then have "?ts \<in> ?U"
        using rtrancl_mono[OF qrstep_mono[OF subset_refl, of Q "{}" nfs U]]
        by auto
      then have "(si (Suc i) \<cdot> \<sigma>i (Suc i), t \<cdot> \<sigma>i i) \<in> ?U'" unfolding id[symmetric] by simp
      note inst = inst[OF _ this]
      from inst obtain \<mu> \<delta> where 
        mgu: "mgu_class (ecap (U^-1) {} {} (mv_xvar (si (Suc i)))) t = Some \<mu>"
        and \<sigma>si: "\<And> s. s \<cdot> \<sigma>i (Suc i) = mv_xvar s \<cdot> \<mu> \<cdot> \<delta>"
        and \<sigma>i: "\<And> s. s \<cdot> \<sigma>i i = mv_yvar s \<cdot> \<mu> \<cdot> \<delta>" by auto
      from ichain have "(si (Suc i), ti (Suc i)) \<in> P \<union> Pw" by auto
      note main = main[OF this DG mgu]
      from NF_instance[OF NF[unfolded \<sigma>i]] have "mv_yvar s \<cdot> \<mu> \<in> NF_terms Q" .
      note main = main[OF this]
      from ichain have NF2: "si (Suc i) \<cdot> \<sigma>i (Suc i) \<in> NF_terms Q" by simp
      from NF_instance[OF NF2[unfolded \<sigma>si]] have "mv_xvar (si (Suc i)) \<cdot> \<mu> \<in> NF_terms Q" . 
      note main = main[OF this]
      from main obtain s' t' where st': "(s',t') \<in> sts" and inst: "instance_rule (mv_yvar s \<cdot> \<mu>, mv_yvar t \<cdot> \<mu>) (s',t') " 
        and inst2: "instance_rule (s',t') (s,t)" by auto
      from pair True st' have mem: "(s',t') \<in> replace (s,t) sts P'" unfolding replace_def by auto
      from inst[unfolded instance_rule_def] obtain \<tau> where id: 
        "mv_yvar s \<cdot> \<mu> = s' \<cdot> \<tau>" "mv_yvar t \<cdot> \<mu> = t' \<cdot> \<tau>" by auto        
      show ?thesis unfolding True \<sigma>i id
      proof (intro exI conjI)
        show "s' \<cdot> \<tau> \<cdot> \<delta> = s' \<cdot> (\<tau> \<circ>\<^sub>s \<delta>)" by simp
      qed (insert inst2 mem, auto)
    qed
  } note main = this
  let ?RP = "replace (s,t) sts P"
  let ?RPw = "replace (s,t) sts Pw"
  from ichain_instantiation[OF min_ichain main, of "0" "\<lambda> x. x"]
  have "\<exists> s' t' \<sigma>'. min_ichain (nfs,m,?RP, ?RPw, Q, R, Rw) s' t' \<sigma>'" by blast
  with fin show False unfolding finite_dpp_def by blast
qed

end
