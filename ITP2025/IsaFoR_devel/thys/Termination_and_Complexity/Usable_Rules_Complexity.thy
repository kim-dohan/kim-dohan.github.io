(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Rules_Complexity
imports
  TRS.Q_Relative_Rewriting
  Ord.Complexity
  Innermost_Usable_Rules
  Usable_Replacement_Map
begin

context 
  fixes US :: "'f sig"
  and U :: "('f,'v)trs"
  and R :: "('f,'v)trs"
  and Q :: "('f,'v)terms"
  and nfs :: bool
begin
definition usable_symbols_rule_closed :: "('f,'v)rule \<Rightarrow> bool" where
  "usable_symbols_rule_closed lr \<equiv> case lr of (l,r) \<Rightarrow>
    funas_term l \<subseteq> US \<longrightarrow> funas_term r \<subseteq> US"

definition usable_symbols_closed :: "bool" where
  "usable_symbols_closed \<equiv> \<forall> lr \<in> U. usable_symbols_rule_closed lr"

definition U_usable :: bool where
  "U_usable \<equiv> \<forall> lr \<in> R. funas_term (fst lr) \<subseteq> US \<longrightarrow> lr \<in> U"

context
  assumes U_usable usable_symbols_closed 
  and wf: "\<And> l r. (l,r) \<in> U \<Longrightarrow> vars_term r \<subseteq> vars_term l"
begin

lemma only_usable_step: assumes sUS: "funas_term s \<subseteq> US"
  and R': "R' \<subseteq> R"
  and step: "(s,t) \<in> qrstep nfs Q R'"
  shows "(s,t) \<in> qrstep nfs Q (R' \<inter> U) \<and> funas_term t \<subseteq> US"
proof -
  from qrstepE[OF step]
  obtain C \<sigma> l r where nf: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and
      lr: "(l, r) \<in> R'" and 
      s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and 
      t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and 
      nfs: "NF_subst nfs (l, r) \<sigma> Q" .
  note sUS = sUS[unfolded s]
  from sUS have l: "funas_term l \<subseteq> US" by (auto simp: funas_term_subst)
  with \<open>U_usable\<close>[unfolded U_usable_def] lr R' have lrU: "(l,r) \<in> U" by auto
  with nf lr s t nfs have step: "(s,t) \<in> qrstep nfs Q (R' \<inter> U)" by auto
  from wf[OF lrU] have vars: "vars_term r \<subseteq> vars_term l" .
  from \<open>usable_symbols_closed\<close>[unfolded usable_symbols_closed_def] lrU
  have "usable_symbols_rule_closed (l,r)" by auto  
  from this[unfolded usable_symbols_rule_closed_def] l have "funas_term r \<subseteq> US" by auto
  with vars sUS have "funas_term t \<subseteq> US" unfolding t
    by (force simp: funas_term_subst)
  with step show ?thesis by blast
qed

lemma usable_rules_complexity: assumes S: "S \<subseteq> R" and W: "W \<subseteq> R" 
  and sig: "set (get_signature_of_cm cm) \<subseteq> US"
  and bound: "deriv_bound_measure_class 
    (relto (qrstep nfs Q (S \<inter> U)) (qrstep nfs Q (W \<inter> U)))
    cm cc" (is "deriv_bound_measure_class ?U cm cc")
  shows "deriv_bound_measure_class 
    (relto (qrstep nfs Q S) (qrstep nfs Q W))
    cm cc" (is "deriv_bound_measure_class ?P cm cc")
proof -
  note d = deriv_bound_measure_class_def deriv_bound_rel_class_def deriv_bound_rel_def
  from bound[unfolded d] obtain f where 
    f: "f \<in> O_of cc" and
    bound: "\<And> n t. t \<in> terms_of_nat cm n \<Longrightarrow> deriv_bound ?U t (f n)" 
    by auto
  show ?thesis unfolding d
  proof (intro exI[of _ f] conjI[OF f] allI impI)
    fix n t
    assume t: "t \<in> terms_of_nat cm n"
    with get_signature_of_cm[of cm n] sig have tUS: "funas_term t \<subseteq> US" by auto
    note d = deriv_bound_def
    from bound[OF t] have bound: "deriv_bound ?U t (f n)" .
    show "deriv_bound ?P t (f n)" unfolding d
    proof
      assume "\<exists> s. (t,s) \<in> ?P^^(Suc (f n))"
      then obtain s where steps: "(t,s) \<in> ?P^^(Suc (f n))" by auto
      let ?p = "\<lambda> t. funas_term t \<subseteq> US"
      let ?s = "Collect ?p"
      let ?R = "qrstep nfs Q R"
      let ?S = "qrstep nfs Q S"
      let ?W = "qrstep nfs Q W"
      from tUS have tUS: "t \<in> ?s" by auto
      have "(t,s) \<in> ?U^^(Suc (f n))"
      proof (rule abstract_closure_twice.AA_steps_imp_BB_steps[of _ _ ?R ?s ?p, OF _ tUS steps],
        unfold_locales)
        show "?S \<subseteq> ?R^*" using qrstep_mono[OF S subset_refl, of nfs Q] by auto
        show "?W \<subseteq> ?R^*" using qrstep_mono[OF W subset_refl, of nfs Q] by auto
        show "\<And> a b. funas_term a \<subseteq> US \<Longrightarrow> (a, b) \<in> ?S \<Longrightarrow> (a, b) \<in> qrstep nfs Q (S \<inter> U)"
          using only_usable_step[OF _ S] by blast
        show "\<And> a b. funas_term a \<subseteq> US \<Longrightarrow> (a, b) \<in> ?W \<Longrightarrow> (a, b) \<in> qrstep nfs Q (W \<inter> U)"
          using only_usable_step[OF _ W] by blast
        fix s t 
        assume s: "s \<in> ?s" and st: "(s,t) \<in> ?R^*" 
        from st show "?p t"
        proof (induct)
          case (step t u)
          from only_usable_step[OF step(3) _ step(2)] show ?case by auto
        qed (insert s, auto)
      qed
      with bound[unfolded d] show False by auto
    qed
  qed
qed
end
end

context R_Q_U_ecap
begin

context
  fixes S W :: "('f,string)trs"
  and C D :: "('f \<times> nat)list"
  and cm :: "('f,string)complexity_measure"
  assumes 
      R: "S \<union> W \<subseteq> R"
  and wf: "wf_trs R"
  and rt: "cm = Runtime_Complexity C D"
  and C: "\<And> c. c \<in> set C \<Longrightarrow> \<not> defined R c"
  and init: "\<And> l r. (l,r) \<in> R \<Longrightarrow> the (root l) \<in> set D \<Longrightarrow> 
    \<Union> (funas_term ` set (args l)) \<subseteq> set C \<Longrightarrow> (l,r) \<in> U"
begin

(* store info for usable rules for complexity *)
definition "urc_info t n nfs ts sel m s l r \<sigma> lr p \<tau> \<equiv> relto_fun (qrstep nfs Q S) (qrstep nfs Q W) (Suc n) ts sel m (t, s)
    \<and> ts 0 = l \<cdot> \<sigma> \<and> ts (Suc 0) = r \<cdot> \<sigma> \<and> (l,r) \<in> U \<and> lr 0 = (l,r)
    \<and> set (args l) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ \<and> \<sigma> ` vars_term r \<subseteq> NFQ 
    \<and> (\<forall> i < m. (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i))
    \<and> (\<forall> i < m. vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i)) \<and> is_Fun (fst (lr i)))
    \<and> (\<forall> i < m. (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i})
    \<and> (\<forall> i < m. lr i \<in> (if sel i then S else W))"

lemma get_step_urc_info: assumes t: "t \<in> terms_of_nat cm n'"
  and steps: "\<exists> s. (t,s) \<in> ((relto (qrstep nfs Q S) (qrstep nfs Q W)))^^(Suc n)"
  shows "\<exists> ts sel m s l r \<sigma> lr p \<tau>. urc_info t n nfs ts sel m s l r \<sigma> lr p \<tau>"
proof -
  let ?P = "relto (qrstep nfs Q S) (qrstep nfs Q W)"
  from t[unfolded rt] obtain g ss where 
      tg: "t = Fun g ss" and g: "(g,length ss) \<in> set D" and 
      ss: "\<And> ti. ti \<in> set ss \<Longrightarrow> funas_term ti \<subseteq> set C" by (force simp: funas_args_term_def)
  from steps obtain s where steps: "(t,s) \<in> ?P^^(Suc n)" by auto
  from reltos_into_relto_fun[OF this] obtain ts sel m where 
    rtf: "relto_fun (qrstep nfs Q S) (qrstep nfs Q W) (Suc n) ts sel m (t, s)" by blast      
  note steps = relto_funD[OF rtf]
  let ?R = "\<lambda> i. if sel i then S else W"
  let ?RU = "\<lambda> i. if sel i then S \<inter> U else W \<inter> U"
  {
    fix i
    assume "i < m"
    from steps(3-4)[OF this, unfolded qrstep_rule_conv[where R = S] qrstep_rule_conv[where R = W]]
    have "\<exists> lr \<in> ?R i. (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr}" by auto
  }
  then have "\<forall> i. \<exists> lr. i < m \<longrightarrow> lr \<in> ?R i \<and> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr}" by blast
  from choice[OF this] obtain lr where lr: "\<And> i. i < m \<Longrightarrow> lr i \<in> ?R i" 
    and step: "\<And> i. i < m \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}" by blast+
  from lr R have lrR: "\<And> i. i < m \<Longrightarrow> lr i \<in> R" by (force split: if_splits)
  {
    fix i
    assume i: "i < m"
    from step[OF i, unfolded qrstep_qrstep_r_p_s_conv] obtain lr' p \<tau>
    where "(ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q {lr i} lr' p \<tau>" by auto
    with lrR[OF i]
    have "(ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) p \<tau>" unfolding qrstep_r_p_s_def by auto
    then have "\<exists> p \<tau>. (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) p \<tau>" by blast
  }
  then have "\<forall> i. \<exists> p \<tau>. i < m \<longrightarrow> (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) p \<tau>" by blast
  from choice[OF this] obtain p where "\<forall> i. \<exists> \<tau>. i < m \<longrightarrow> (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) \<tau>" by blast
  from choice[OF this] obtain \<tau> where 
    step': "\<And> i. i < m \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i)" by blast
  obtain l r where lr0: "lr 0 = (l,r)" by force
  from steps have 0: "0 < m" by auto      
  from lrR[OF 0] lr0 have lrR0: "(l,r) \<in> R" by auto
  from step[OF 0] steps(1) lr0 have "(t, ts 1) \<in> qrstep nfs Q {(l,r)}" by simp
  then obtain C' \<sigma> where tl: "t = C'\<langle>l \<cdot> \<sigma>\<rangle>" and tr: "ts 1 = C'\<langle>r \<cdot> \<sigma>\<rangle>" 
    and Q: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" by auto
  from wf_trs_imp_lhs_Fun[OF wf lrR0] obtain f ls where l: "l = Fun f ls"
    by auto
  have C': "C' = \<box>"
  proof (cases C')
    case (More h bef D' aft)
    from tl[unfolded this tg] have "D'\<langle>l \<cdot> \<sigma>\<rangle> \<in> set ss" by auto
    from ss[OF this] have lC: "funas_term (l \<cdot> \<sigma>) \<subseteq> set C" by auto
    from l lrR0 lr0 have "(Fun f ls, r) \<in> R" by auto 
    then have df: "defined R (f,length ls)" unfolding defined_def by auto
    from lC l have "(f,length ls) \<in> set C" by (auto simp: funas_term_subst)
    from C[OF this] df show ?thesis by simp
  qed simp
  with tl tr steps have tl: "ts 0 = l \<cdot> \<sigma>" and tr: "ts (Suc 0) = r \<cdot> \<sigma>" by auto
  let ?ts = "\<lambda> i. ts (Suc i)"
  let ?lr = "\<lambda> i. lr (Suc i)"
  let ?p = "\<lambda> i. p (Suc i)"
  let ?\<tau> = "\<lambda> i. \<tau> (Suc i)"
  from steps obtain m' where m: "m = Suc m'" by (cases m, auto)
  then have i: "\<And> i. i < m' \<Longrightarrow> Suc i < m" by auto
  from Q[folded NF_terms_args_conv] have lQ: "set (args l) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" unfolding l by auto
  {
    fix x
    assume "x \<in> vars_term r"
    with wf lrR0 have "x \<in> vars_term l" by (auto simp: wf_trs_def)
    then have "l \<rhd> Var x" unfolding l by force
    from supt_subst[OF this, of \<sigma>] Q have "\<sigma> x \<in> NFQ" by auto
  }
  then have rQ: "\<sigma> ` vars_term r \<subseteq> NFQ" by auto
  {
    fix i
    assume "i < m" 
    from wf lrR[OF this] 
    have "vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i))" "is_Fun (fst (lr i))"
      unfolding wf_trs_def by (cases "lr i", force)+
  } note wf = this
  from tl l steps(1) tg have lg: "l \<cdot> \<sigma> = Fun g ss" by simp
  from lg l g have lD: "the (root l) \<in> set D" by auto
  from lg l ss have argsC: "\<Union>(funas_term ` set (args l)) \<subseteq> set C" by (force simp: funas_term_subst)
  have lrU0: "(l,r) \<in> U"
    by (rule init[OF lrR0 lD argsC]) 
  show ?thesis unfolding urc_info_def
    by (intro exI conjI allI impI, rule rtf, rule tl, rule tr, rule lrU0, rule lr0, 
      rule lQ, rule rQ, rule step', insert step lr wf, auto)
qed  

lemma usable_rules_innermost_complexity_urm: assumes 
      U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv \<mu> (set (args l)) r"
  and URM: "usable_replacement_map \<mu> (terms_of cm) nfs R Q R"
  and bound: "deriv_bound_measure_class 
    (relto (qrstep nfs Q (S \<inter> U)) (qrstep nfs Q (W \<inter> U)))
    cm cc" (is "deriv_bound_measure_class ?U cm cc")
  shows "deriv_bound_measure_class 
    (relto (qrstep nfs Q S) (qrstep nfs Q W))
    cm cc" (is "deriv_bound_measure_class ?P cm cc")
proof -
  note d = deriv_bound_measure_class_def deriv_bound_rel_class_def deriv_bound_rel_def
  from bound[unfolded d] obtain f where 
    f: "f \<in> O_of cc" and
    bound: "\<And> n t. t \<in> terms_of_nat cm n \<Longrightarrow> deriv_bound ?U t (f n)" 
    by auto
  show ?thesis unfolding d
  proof (intro exI[of _ f] conjI[OF f] allI impI)
    fix n t
    assume t: "t \<in> terms_of_nat cm n"
    from bound[OF t] have bound: "deriv_bound ?U t (f n)" .
    note d = deriv_bound_def
    show "deriv_bound ?P t (f n)" unfolding d
    proof
      assume "\<exists> s. (t,s) \<in> ?P^^(Suc (f n))"
      from get_step_urc_info[OF t this] obtain ts sel m s l r \<sigma> lr p \<tau> where
        info: "urc_info t (f n) nfs ts sel m s l r \<sigma> lr p \<tau>" by auto
      from info[unfolded urc_info_def] have
        rtf: "relto_fun (qrstep nfs Q S) (qrstep nfs Q W) (Suc (f n)) ts sel m (t, s)" 
        and tl: "ts 0 = l \<cdot> \<sigma>" and tr: "ts (Suc 0) = r \<cdot> \<sigma>" and lrU0: "(l,r) \<in> U" 
        and lr0: "lr 0 = (l,r)" 
        and lQ: "set (args l) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" and rQ: "\<sigma> ` vars_term r \<subseteq> NFQ"
        and step': "\<And> i. i < m \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i)" 
        and wf: "\<And> i. i < m \<Longrightarrow> vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i)) \<and> is_Fun (fst (lr i))" 
        and step: "\<And> i. i < m \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}"
        and lr: "\<And> i. i < m \<Longrightarrow> lr i \<in> (if sel i then S else W)" by auto
      note steps = relto_funD[OF rtf]
      let ?R = "\<lambda> i. if sel i then S else W"
      let ?RU = "\<lambda> i. if sel i then S \<inter> U else W \<inter> U"
      let ?ts = "\<lambda> i. ts (Suc i)"
      let ?lr = "\<lambda> i. lr (Suc i)"
      let ?p = "\<lambda> i. p (Suc i)"
      let ?\<tau> = "\<lambda> i. \<tau> (Suc i)"
      from steps obtain m' where m: "m = Suc m'" by (cases m, auto)
      then have i: "\<And> i. i < m' \<Longrightarrow> Suc i < m" by auto
      {
        fix i
        assume im': "i < m'"
        with m have im: "Suc i \<le> m" "Suc i < m" by auto
        let ?ti = "ts (Suc i)"  
        let ?pi = "p (Suc i)"
        have "lr (Suc i) \<in> U"
        proof (rule is_ur_closed_term_main_af[of m' ?ts nfs ?lr ?p ?\<tau>, OF step'[OF i] wf[OF i] rQ tr lQ U U[OF lrU0] _ im'])
          have "(t, ?ti) \<in> (qrstep nfs Q R)\<^sup>*"
            by (rule relto_fun_intermediate[OF qrstep_mono qrstep_mono rtf im(1)], insert R, auto)
          with t have "?ti \<in> (qrstep nfs Q R)\<^sup>* `` terms_of cm" by (auto simp: terms_of)
          with URM[unfolded usable_replacement_map_def] 
          have af: "?ti \<in> af_nf_compatible_terms \<mu> (qrstep nfs Q R)" by auto
          define C where "C = ctxt_of_pos_term ?pi ?ti"
          from qrstep_r_p_s_conv[OF step'[OF im(2)]] have hp: "?pi = hole_pos C"
            and ti: "?ti = C\<langle>fst (lr (Suc i)) \<cdot> \<tau> (Suc i)\<rangle>" unfolding C_def by auto
          from step'[OF im(2)] have step: "(fst (lr (Suc i)) \<cdot> \<tau> (Suc i), snd (lr (Suc i)) \<cdot> \<tau> (Suc i))
            \<in> qrstep nfs Q R" unfolding qrstep_r_p_s_def by auto
          with af[unfolded af_nf_compatible_terms_def] 
          show "af_regarded_pos \<mu> ?ti ?pi" unfolding ti hp by auto
        qed auto
      } note lrU = this
      have "relto_fun (qrstep nfs Q (S \<inter> U)) (qrstep nfs Q (W \<inter> U)) (Suc (f n)) ts sel m (t, s)"
      proof (rule relto_fun[OF steps(1-2) _ steps(5-6)])
        fix i
        assume i: "i < m"
        then have "lr i \<in> U" using lrU[of "i - 1"] lrU0 lr0 m by (cases i, auto)
        with step'[OF i] lr[OF i] have "lr i \<in> ?RU i" by auto
        with step[OF i] have "(ts i, ts (Suc i)) \<in> qrstep nfs Q (?RU i)" 
          unfolding qrstep_rule_conv[where R = "?RU i"] by auto
        then show "(sel i \<longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q (S \<inter> U)) \<and>
         (\<not> sel i \<longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q (W \<inter> U))"
         by (cases "sel i", auto)
      qed
      from relto_fun_into_reltos[OF this]
      have "(t,s) \<in> ?U^^(Suc (f n))" .
      with bound[unfolded d] show False by blast
    qed
  qed
qed

lemma usable_rules_innermost_complexity: assumes 
      U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r"
  and bound: "deriv_bound_measure_class 
    (relto (qrstep nfs Q (S \<inter> U)) (qrstep nfs Q (W \<inter> U)))
    cm cc" 
  shows "deriv_bound_measure_class 
    (relto (qrstep nfs Q S) (qrstep nfs Q W))
    cm cc" 
  by (rule usable_rules_innermost_complexity_urm[OF U _ bound], auto)

text \<open>in the following proof we do not make use of the fact that NS_ord
   is monotone in all arguments, which is enforced by the rp-precondition on
   @{term cpx_ce_af_redtriple_order}}\<close>
lemma usable_rules_innermost_complexity_urm_redpair: assumes 
      compatR: "S \<inter> U \<subseteq> S_ord" "W \<inter> U \<subseteq> NS_ord"
  and af: "af_monotone \<mu>\<^sub>S S_ord" "af_monotone \<mu>\<^sub>w NS_ord"
  and bound: "deriv_bound_measure_class S_ord cm cc"
  and URMS: "usable_replacement_map \<mu>\<^sub>S (terms_of cm) nfs R Q S"
  and URMW: "usable_replacement_map \<mu>\<^sub>w (terms_of cm) nfs R Q W"
  and U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv \<mu>\<^sub>S (set (args l)) r"
  and U\<pi>: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv (af_inter \<pi> \<mu>\<^sub>w) (set (args l)) r"
  and rp: "compat_redpair_order S_ord NS_ord"
  and af_compat: "af_compatible \<pi> NS_ord" 
  shows "deriv_bound_measure_class 
    (relto (qrstep nfs Q S) (qrstep nfs Q W))
    cm cc" (is "deriv_bound_measure_class ?P cm cc")
proof -
  interpret compat_redpair_order S_ord NS_ord by fact
  note d = deriv_bound_measure_class_def deriv_bound_rel_class_def deriv_bound_rel_def
  from bound[unfolded d] obtain f where 
    f: "f \<in> O_of cc" and
    bound: "\<And> n t. t \<in> terms_of_nat cm n \<Longrightarrow> deriv_bound S_ord t (f n)" 
    by auto
  show ?thesis unfolding d
  proof (intro exI[of _ f] conjI[OF f] allI impI)
    fix n t
    assume t: "t \<in> terms_of_nat cm n"
    from bound[OF t] have bound: "deriv_bound S_ord t (f n)" .
    note d = deriv_bound_def
    show "deriv_bound ?P t (f n)" unfolding d
    proof
      assume "\<exists> s. (t,s) \<in> ?P^^(Suc (f n))"
      from get_step_urc_info[OF t this] obtain ts sel m s l r \<sigma> lr p \<tau> where
        info: "urc_info t (f n) nfs ts sel m s l r \<sigma> lr p \<tau>" by auto
      from info[unfolded urc_info_def] have
        rtf: "relto_fun (qrstep nfs Q S) (qrstep nfs Q W) (Suc (f n)) ts sel m (t, s)" 
        and tl: "ts 0 = l \<cdot> \<sigma>" and tr: "ts (Suc 0) = r \<cdot> \<sigma>" and lrU0: "(l,r) \<in> U" 
        and lr0: "lr 0 = (l,r)" 
        and lQ: "set (args l) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" and rQ: "\<sigma> ` vars_term r \<subseteq> NFQ"
        and step': "\<And> i. i < m \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i)" 
        and wf: "\<And> i. i < m \<Longrightarrow> vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i)) \<and> is_Fun (fst (lr i))" 
        and step: "\<And> i. i < m \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}"
        and lr: "\<And> i. i < m \<Longrightarrow> lr i \<in> (if sel i then S else W)" by auto
      note steps = relto_funD[OF rtf]
      let ?R = "\<lambda> i. if sel i then S else W"
      let ?RU = "\<lambda> i. if sel i then S \<inter> U else W \<inter> U"
      let ?ts = "\<lambda> i. ts (Suc i)"
      let ?lr = "\<lambda> i. lr (Suc i)"
      let ?p = "\<lambda> i. p (Suc i)"
      let ?\<tau> = "\<lambda> i. \<tau> (Suc i)"
      from steps obtain m' where m: "m = Suc m'" by (cases m, auto)
      then have i: "\<And> i. i < m' \<Longrightarrow> Suc i < m" by auto
      {
        assume "sel 0"
        with lr[of 0] m have "lr 0 \<in> S" by auto
        with lr0 lrU0 have "(l,r) \<in> S \<inter> U" by auto
        with compatR have "(l,r) \<in> S_ord" by auto
        from subst.closedD[OF subst_S this, of \<sigma>] tl tr have "(ts 0, ts (Suc 0)) \<in> S_ord" by auto
      } note S_ord_0 = this
      {
        assume "\<not> sel 0"
        with lr[of 0] m have "lr 0 \<in> W" by auto
        with lr0 lrU0 have "(l,r) \<in> W \<inter> U" by auto
        with compatR have "(l,r) \<in> NS_ord" by auto
        from subst.closedD[OF subst_NS this, of \<sigma>] tl tr have "(ts 0, ts (Suc 0)) \<in> NS_ord" by auto
      } note NS_ord_0 = this
      {
        fix i
        assume im': "i < m'"
        with m have im: "Suc i \<le> m" "Suc i < m" by auto
        let ?ti = "ts (Suc i)"  
        let ?pi = "p (Suc i)"
        let ?C = "ctxt_of_pos_term (?p i) (?ts i)"
        define C where "C = ?C" 
        from qrstep_r_p_s_conv[OF step'[OF im(2)]] 
          have tsSi: "?ts (Suc i) = C\<langle>snd (?lr i) \<cdot> ?\<tau> i\<rangle>" and pi: "?p i \<in> poss (?ts i)"
          and hp: "?pi = hole_pos C"
          and tsi: "?ts i = C \<langle>fst (?lr i) \<cdot> ?\<tau> i\<rangle>" unfolding C_def by auto
        have "(t, ?ti) \<in> (qrstep nfs Q R)\<^sup>*"
          by (rule relto_fun_intermediate[OF qrstep_mono qrstep_mono rtf im(1)], insert R, auto)
        with t have ti1: "?ti \<in> (qrstep nfs Q R)\<^sup>* `` terms_of cm" by (auto simp: terms_of)
        have piC: "?pi = hole_pos C" unfolding C_def using pi by auto
        {
          assume "sel (Suc i)"
          with lr[OF im(2)] have lrS: "lr (Suc i) \<in> S" by auto
          {
            from ti1 URMS[unfolded usable_replacement_map_def] 
            have af: "?ti \<in> af_nf_compatible_terms \<mu>\<^sub>S (qrstep nfs Q S)" by auto
            from step'[OF im(2)] lrS have step: "(fst (lr (Suc i)) \<cdot> \<tau> (Suc i), snd (lr (Suc i)) \<cdot> \<tau> (Suc i))
              \<in> qrstep nfs Q S" unfolding qrstep_r_p_s_def by auto
            with af[unfolded af_nf_compatible_terms_def] 
            have "af_regarded_pos \<mu>\<^sub>S ?ti ?pi" unfolding tsi hp by auto
          } note r\<mu> = this
          have "?lr i \<in> U"
            by (rule is_ur_closed_term_main_af[of m' ?ts nfs ?lr ?p ?\<tau>, OF step'[OF i] wf[OF i] rQ tr lQ U U[OF lrU0] r\<mu> im'], auto)
          with lrS have "?lr i \<in> S \<inter> U" by auto
          with compatR have S: "?lr i \<in> S_ord" by auto
          with subst.closedD[OF subst_S] have "(fst (?lr i) \<cdot> ?\<tau> i, snd (?lr i) \<cdot> ?\<tau> i) \<in> S_ord" by auto
          from af_monotone_af_regarded_posD[OF af(1) r\<mu>[unfolded tsi piC] this]
          have "(?ts i, ?ts (Suc i)) \<in> S_ord" unfolding tsi tsSi .
        }
        moreover
        {
          assume "\<not> sel (Suc i)"
          with lr[OF im(2)] have lrW: "lr (Suc i) \<in> W" by auto
          have "(?ts i, ?ts (Suc i)) \<in> NS_ord"
          proof (cases "af_regarded_pos \<pi> ?ti ?pi")
            case False
            from af_compatible_af_regarded_ctxt[OF af_compat ctxt_NS False[unfolded tsi piC]]
            show ?thesis unfolding tsi tsSi .
          next
            case True
            {
              from ti1 URMW[unfolded usable_replacement_map_def] 
              have af: "?ti \<in> af_nf_compatible_terms \<mu>\<^sub>w (qrstep nfs Q W)" by auto
              from step'[OF im(2)] lrW have step: "(fst (lr (Suc i)) \<cdot> \<tau> (Suc i), snd (lr (Suc i)) \<cdot> \<tau> (Suc i))
                \<in> qrstep nfs Q W" unfolding qrstep_r_p_s_def by auto
              with af[unfolded af_nf_compatible_terms_def] 
              have "af_regarded_pos \<mu>\<^sub>w ?ti ?pi" unfolding tsi hp by auto
            } note r\<mu> = this
            with True have afi: "af_regarded_pos (af_inter \<pi> \<mu>\<^sub>w) ?ti ?pi"
              unfolding af_regarded_pos_af_inter by blast
            have "?lr i \<in> U" 
              by (rule is_ur_closed_term_main_af[of m' ?ts nfs ?lr ?p ?\<tau>, 
                  OF step'[OF i] wf[OF i] rQ tr lQ U\<pi> U\<pi>[OF lrU0] afi im'], auto)
            with lrW have "?lr i \<in> W \<inter> U" by auto
            with compatR have NS: "?lr i \<in> NS_ord" by auto
            with subst.closedD[OF subst_NS] have "(fst (?lr i) \<cdot> ?\<tau> i, snd (?lr i) \<cdot> ?\<tau> i) \<in> NS_ord" by auto
            from af_monotone_af_regarded_posD[OF af(2) r\<mu>[unfolded tsi piC] this]
            show "(?ts i, ?ts (Suc i)) \<in> NS_ord" unfolding tsi tsSi .
          qed
        }
        ultimately 
        have "sel (Suc i) \<Longrightarrow> (?ts i, ?ts (Suc i)) \<in> S_ord"
             "\<not> sel (Suc i) \<Longrightarrow> (?ts i, ?ts (Suc i)) \<in> NS_ord" by blast+
      } note later = this
      {
        fix i
        assume i: "i < m"
        have "(sel i \<longrightarrow> (ts i, ts (Suc i)) \<in> S_ord) \<and> (\<not> sel i \<longrightarrow> (ts i, ts (Suc i)) \<in> NS_ord)"
        proof (cases i)
          case 0
          with S_ord_0 NS_ord_0 show ?thesis by auto
        next
          case (Suc j)
          with later[of j] i[unfolded m] show ?thesis by auto
        qed
        then have "sel i \<Longrightarrow> (ts i, ts (Suc i)) \<in> S_ord" "\<not> sel i \<Longrightarrow> (ts i, ts (Suc i)) \<in> NS_ord" by auto
      } note main = this      
      have ord_comb: "NS_ord^* O S_ord O NS_ord^* = S_ord" 
        using S_O_rtrancl_NS(1) rtrancl_NS rtrancl_NS_O_S(1) by auto
      have "relto_fun S_ord NS_ord (Suc (f n)) ts sel m (t, s)"
        by (rule relto_fun[OF steps(1-2) _ steps(5-6)], insert main, auto)
      from relto_fun_into_reltos[OF this, unfolded ord_comb]
      have "(t,s) \<in> S_ord^^(Suc (f n))" .
      with bound[unfolded d] show False by blast
    qed
  qed
qed

end
end
end
