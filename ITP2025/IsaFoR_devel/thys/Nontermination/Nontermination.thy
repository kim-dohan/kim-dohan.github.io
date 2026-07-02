(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2012)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Nontermination
imports
  First_Order_Rewriting.Trs_Impl
  TRS.Q_Relative_Rewriting
begin

(* for nontermination analysis we use a simpler notion of DP-problems than for termination,
   which does not feature weak components *)
type_synonym ('f, 'v) dpp = "bool \<times> ('f, 'v) trs \<times> ('f, 'v) terms \<times> ('f, 'v) trs"

fun
  i_chain ::
    "('f, 'v) dpp \<Rightarrow>
     (nat \<Rightarrow> ('f, 'v) term) \<Rightarrow>
     (nat \<Rightarrow> ('f, 'v) term) \<Rightarrow>
     (nat \<Rightarrow> ('f, 'v) subst) \<Rightarrow> bool"
where
  "i_chain (nfs, P, Q, R) s t \<sigma> = (
    (\<forall>i. (s i, t i) \<in> P) \<and> 
    (\<forall>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q R)^*) \<and>
    (\<forall>i. \<forall>u\<lhd>s i \<cdot> \<sigma> i. u \<in> NF_terms Q) \<and> 
    (\<forall>i. NF_subst nfs (s i, t i) (\<sigma> i) Q))"

lemma loop_imp_not_SN_on_qrstep:
  assumes loop: "\<And> i. \<exists> C. (t \<cdot> \<mu> ^^ i, C\<langle>t \<cdot> \<mu> \<cdot> \<mu> ^^ i\<rangle>) \<in> (qrstep nfs Q R)^+"
  shows "\<not> SN_on (qrstep nfs Q R) {t}"
proof
  let ?R = "({\<rhd>} \<union> qrstep nfs Q R)^+"
  assume "SN_on (qrstep nfs Q R) {t}"
  from SN_on_trancl[OF SN_on_qrstep_imp_SN_on_supt_union_qrstep[OF this]]
  have sn: "SN_on ?R {t}" .  
  let ?t = "\<lambda>i. t \<cdot> \<mu> ^^ i"
  have "?t 0 = t" by simp
  moreover have "\<forall>i. (?t i, ?t (Suc i)) \<in> ?R"
  proof
    fix i 
    from loop[of i] obtain C where "(?t i, C\<langle>?t (Suc i)\<rangle>) \<in> (qrstep nfs Q R)^+"
      by auto
    moreover have "(C\<langle>?t (Suc i)\<rangle>, ?t (Suc i)) \<in> ({\<rhd>})^="       
      by (cases "C = \<box>", auto)
    ultimately have step: "(?t i, ?t (Suc i)) \<in> (qrstep nfs Q R)^+ O ({\<rhd>})^=" by auto 
    show "(?t i, ?t (Suc i)) \<in> ?R"
      by (rule set_mp[OF _ step], regexp)
  qed
  ultimately show False using sn unfolding SN_defs by best
qed


lemma loop_imp_not_SN_on_rstep:
  assumes steps: "(s, C\<langle>s \<cdot> \<sigma>\<rangle>) \<in> (rstep R)^+"
  shows "\<not> SN_on (rstep R) {s}"
proof
  let ?R = "{\<rhd>} \<union> rstep R"
  assume "SN_on (rstep R) {s}"
  from SN_on_rstep_imp_SN_on_supt_union_rstep[OF this]
  have SN: "SN_on ?R {s}" .
  from subst.closed_Un[OF subst_closed_supt subst_closed_rstep]
  have subst: "subst.closed ?R" .
  have steps: "(s, C\<langle>s \<cdot> \<sigma>\<rangle>) \<in> ?R^+" using trancl_mono[OF steps] by auto
  have "(s, s \<cdot> \<sigma>) \<in> ?R^+"
  proof (cases C)
    case Hole
    with steps  show ?thesis by simp
  next
    case (More f bef D aft)
    with ctxt_supt[of C _ "s \<cdot> \<sigma>"] have "C\<langle>s \<cdot> \<sigma>\<rangle> \<rhd> s \<cdot> \<sigma>" by simp 
    then have "(C\<langle>s \<cdot> \<sigma>\<rangle>, s \<cdot> \<sigma>) \<in> ?R" unfolding supt_def by auto
    with steps show ?thesis by (rule trancl_into_trancl)
  qed
  from stable_loop_imp_not_SN[OF subst this] SN 
  show False ..
qed

fun infinite_dpp :: "('f, 'v) dpp \<Rightarrow> bool" where
  "infinite_dpp (nfs, P, Q, R) = ((\<not> SN (qrstep nfs Q R)) \<or> (\<exists>s t \<sigma>. i_chain (nfs, P, Q, R) s t \<sigma>))"

lemma infinite_dpp_not_SN_conv:
  "infinite_dpp (nfs, P, Q, R) = (\<not> SN (rqrstep nfs Q P \<union> qrstep nfs Q R))"
proof (cases "SN (qrstep nfs Q R)")
  case False
  with SN_subset[of "rqrstep nfs Q P \<union> qrstep nfs Q R" "qrstep nfs Q R"]
  show ?thesis by auto
next
  case True
  note snR = this
  let ?R = "qrstep nfs Q R"
  let ?P = "rqrstep nfs Q P"
  let ?RP = "?P \<union> ?R"
  show ?thesis
  proof
    assume "infinite_dpp (nfs,P, Q, R)"
    with snR obtain s t \<sigma> where i_chain: "i_chain (nfs,P, Q, R) s t \<sigma>" by auto
    {
      fix i
      let ?i = "Suc i"
      from i_chain
        have "(s ?i, t ?i) \<in> P"
        and "\<forall>u\<lhd>s ?i \<cdot> \<sigma> ?i. u \<in> NF_terms Q" 
        and "NF_subst nfs (s ?i, t ?i) (\<sigma> ?i) Q" by simp+
      then have step: "(s ?i \<cdot> \<sigma> ?i, t ?i \<cdot> \<sigma> ?i) \<in> ?RP"
        unfolding rqrstep_def qrstep_r_p_s_def by auto
      from i_chain have ts: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R^*" by simp
      with rtrancl_mono[of ?R ?RP]
        have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?RP^*" by auto
      from step steps have "(t i \<cdot> \<sigma> i, t (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?RP^+"
        by (simp only: trancl_unfold_right, auto)
    }
    then have "\<not> SN (?RP^+)" unfolding SN_defs by force
    with SN_imp_SN_trancl show "\<not> SN ?RP" by auto
  next
    assume "\<not> SN ?RP"
    then obtain f where steps: "\<And>i. (f i, f (Suc i)) \<in> ?RP" by (simp, unfold SN_defs, auto)
    show "infinite_dpp (nfs,P, Q, R)"
    proof (cases "\<exists>i. \<forall>j\<ge>i. (f j, f (Suc j)) \<in> ?R")
      case True
      then obtain i where rsteps: "\<And>j. j \<ge> i \<Longrightarrow> (f j, f (Suc j)) \<in> ?R" by auto
      obtain g where g: "\<And>j. g j = f (j + i)" by auto
      from rsteps have "\<And>j. (g j, g (Suc j)) \<in> ?R" using g by auto
      then have "\<not> SN ?R" unfolding SN_defs by blast
      with snR show ?thesis by simp
    next
      case False
      then have "\<forall>i. \<exists>j\<ge>i. (f j, f (Suc j)) \<notin> ?R" by simp
      with steps have Psteps: "INFM j. (f j, f (Suc j)) \<in> ?P" unfolding INFM_nat_le by force
      obtain p where p: "\<And>j. p j = ((f j, f (Suc j)) \<in> ?P)" by auto
      { 
        fix i
        assume "\<not> p i"
        then have "(f i, f (Suc i)) \<notin> ?P" unfolding p by auto
        with steps have "(f i, f (Suc i)) \<in> ?R" by auto
      }
      note p_false = this
      {
        fix i
        assume "p i"
        then have "(f i, f (Suc i)) \<in> ?P" unfolding p by auto
        then have "\<exists>s t \<sigma> . (\<forall>u\<lhd>s \<cdot> \<sigma>. u \<in> NF_terms Q) \<and> NF_subst nfs (s,t) \<sigma> Q \<and>
          (s, t) \<in> P \<and> f i = s \<cdot> \<sigma> \<and> f (Suc i) = t \<cdot> \<sigma>"
          unfolding rqrstep_def qrstep_r_p_s_def by blast
      }
      note p_true = this
      from Psteps have inf_p: "INFM j. p j" unfolding p by auto
      then have ih: "infinitely_many p" by (unfold_locales, simp)
      obtain p_index where "p_index = infinitely_many.index p" by simp
      with infinitely_many.index_p[OF ih]
      and infinitely_many.index_ordered[OF ih]
      and infinitely_many.index_not_p_between[OF ih] 
        have p_index: "\<And>i. p (p_index i) \<and> p_index i < p_index (Suc i) \<and>
          (\<forall>j. p_index i < j \<and> j < p_index (Suc i) \<longrightarrow> \<not> p j)"
        by auto
      let ?prop = "\<lambda>s t \<sigma> i. (\<forall>u\<lhd>s \<cdot> \<sigma>. u \<in> NF_terms Q) \<and> NF_subst nfs (s,t) \<sigma> Q \<and>
        (s, t) \<in> P \<and> s \<cdot> \<sigma> = f (p_index i) \<and> t \<cdot> \<sigma> = f (Suc (p_index i)) \<and>
        (f (Suc (p_index i)), f (p_index (Suc i))) \<in> ?R^*"
      {
        fix i
        let ?pi = "p_index i"
        let ?psi = "p_index (Suc i)"
        from p_index p_true[of ?pi] obtain s t \<sigma>
          where nf: "\<forall>u\<lhd>s \<cdot> \<sigma>. u \<in> NF_terms Q"
          and nfs: "NF_subst nfs (s,t) \<sigma> Q" 
          and st: "(s, t) \<in> P" and s: "f ?pi = s \<cdot> \<sigma>" and t: "f (Suc ?pi) = t \<cdot> \<sigma>" by auto
        from p_index have isi: "?pi < ?psi" by auto
        obtain pi psi where pi: "pi = ?pi" and psi: "psi = ?psi" by auto
        with p_index[of i] p_false
          have inter: "\<And>j. pi < j \<and> j < psi \<Longrightarrow> (f j, f (Suc j)) \<in> ?R" by auto
        from pi isi psi have pisi: "pi < psi" by simp
        {
          fix n
          assume "Suc n \<le> psi - pi"
          then have "(f (Suc pi), f (Suc (n + pi))) \<in> ?R^*"
          proof (induct n, simp)
            case (Suc n)
            then have steps: "(f (Suc pi), f (Suc (n+pi))) \<in> ?R^*" by simp
            have "(f (Suc (n+pi)), f (Suc (Suc n + pi))) \<in> ?R"
              using inter[of "Suc n + pi"] Suc(2) by auto
            with steps show ?case by simp
          qed
        }
        from this[of "psi - pi - 1"] pisi have 
          "(f (Suc pi), f psi) \<in> ?R^*" by simp
        with pi psi have rsteps: "(f (Suc ?pi), f ?psi) \<in> ?R^*" by simp
        from nf nfs rsteps st s t have "\<exists>s t \<sigma>. ?prop s t \<sigma> i" by auto
      }
      then have "\<forall> i. \<exists> s t \<sigma>. ?prop s t \<sigma> i" by simp
      from choice[OF this] obtain s where "\<forall>i. \<exists>t \<sigma>. ?prop (s i) t \<sigma> i" by blast
      from choice[OF this] obtain t where "\<forall>i. \<exists>\<sigma>. ?prop (s i) (t i) \<sigma> i" by blast
      from choice[OF this] obtain \<sigma> where "\<And>i. ?prop (s i) (t i) (\<sigma> i) i" by blast
      then have "i_chain (nfs,P, Q, R) s t \<sigma>" by simp
      then show ?thesis by (simp del: i_chain.simps, blast)
    qed
  qed
qed

lemma infinite_dpp_imp_not_SN:
  assumes P_are_DPs: "\<And> s t. (s,t) \<in> P \<Longrightarrow> is_Fun t \<and> \<not> defined R (the (root t)) \<and>
    (\<exists> l r. (l,r) \<in> R \<and> l = sharp_term unshp s \<and> r \<unrhd> sharp_term unshp t)" 
    and infinite: "infinite_dpp (nfs,P, Q, R)"
    and nfs: "\<not> nfs"
  shows "\<not> SN (qrstep nfs Q R)"
proof
  assume sn: "SN (qrstep nfs Q R)"
  let ?ut = "sharp_term unshp"
  let ?rel = "supt \<union> qrstep nfs Q R"
  from infinite[unfolded infinite_dpp.simps] sn
    obtain s t \<sigma> where ichain: "i_chain (nfs,P, Q, R) s t \<sigma>" by auto
  let ?t = "\<lambda>i. (?ut (t i) \<cdot> \<sigma> i)"
  have main: "\<And>i. (?t i, ?t (Suc i)) \<in> ?rel^+"
  proof -
    fix i    
    let ?sig = "\<sigma>"
    let ?i = "Suc i"
    from ichain have st: "(s i, t i) \<in> P" by auto
    from ichain have st': "(s ?i, t ?i) \<in> P" by auto
    from P_are_DPs[OF st]
      obtain g ts where ti: "t i = Fun g ts"
      and ndef: "\<not> defined R (g, length ts)"
      by (cases "t i") (force+)
    from P_are_DPs[OF st']
      obtain l rr where lr: "(l,rr) \<in> R" and si': "l = ?ut (s ?i)"
      and rr: "rr \<unrhd> ?ut (t ?i)" by auto
    from left_Var_imp_not_SN_qrstep[of _ rr R nfs Q, OF _ nfs] sn lr
      obtain ff ss where l: "l = Fun ff ss" by (cases l, auto simp: SN_def)
    from si' l obtain f where si': "s ?i = Fun f ss"
      and f: "ff = unshp f" by (cases "s ?i", auto)
    from si' f l have l: "l = Fun (unshp f) ss" by simp
    have steps: "(?ut (t i \<cdot> \<sigma> i), ?ut (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> (qrstep nfs Q R)^*"
    proof -
      from ichain have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q R)^*" by simp
      have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (nrqrstep nfs Q R)^*"
      proof (rule qrsteps_imp_nrqrsteps[OF _ _ steps])
        show "\<not> defined (applicable_rules Q R) (the (root (t i \<cdot> \<sigma> i)))"
          unfolding ti using ndef_applicable_rules[OF ndef, of Q] by auto
      next
        {
          fix l rr
          assume "(l,rr) \<in> R" and var: "is_Var l"
          with SN_imp_wwf_qtrs[OF sn nfs, unfolded wwf_qtrs_def]
          have "\<not> applicable_rule Q (l,rr)" by auto
          with left_Var_applicable[of Q _ rr] var have False
            by (cases l, auto)
        }
        then show "\<forall> (l,rr) \<in> R. is_Fun l" by auto
      qed
      show ?thesis
        by (rule set_mp[OF rtrancl_mono nrqrsteps_imp_sharp_qrsteps[OF steps]], auto)
    qed
    from rtrancl_mono[of "qrstep nfs Q R" "supt \<union> qrstep nfs Q R"]
      have "(qrstep nfs Q R)^* \<subseteq> ?rel^*" by auto
    from set_mp[OF this steps]
      have steps: "(?ut (t i) \<cdot> ?sig i, ?ut (s ?i) \<cdot> ?sig ?i) \<in> ?rel^*"
      unfolding si' ti by auto
    from ichain have "\<forall> u \<lhd> s ?i \<cdot> ?sig ?i. u \<in> NF_terms Q" by auto
    then have NF: "\<forall>u\<lhd> l \<cdot> \<sigma> (Suc i). u \<in> NF_terms Q" unfolding l si'
      unfolding NF_terms_args_conv[symmetric] by auto  
    from ichain have "NF_subst nfs (s ?i,t ?i) (\<sigma> ?i) Q" by auto
    with nfs have nfs: "NF_subst nfs (?ut (s ?i), rr) (?sig ?i) Q" by simp
    have "(?ut (s ?i) \<cdot> ?sig ?i, rr \<cdot> ?sig ?i) \<in> ?rel"
      using qrstepI[OF NF lr refl refl, of nfs \<box>] nfs unfolding si' l by auto
    moreover from supteq_subst[OF rr, of "?sig ?i"]
      have "(rr \<cdot> ?sig ?i, ?ut (t ?i) \<cdot> ?sig ?i) \<in> ?rel^=" 
      by (auto simp: supteq_def)
    ultimately have "(?ut (s ?i) \<cdot> ?sig ?i, ?ut (t ?i) \<cdot> ?sig ?i) \<in> ?rel O ?rel^=" by auto
    with steps
    have "(?ut (t i) \<cdot> ?sig i, ?ut (t (Suc i)) \<cdot> ?sig (Suc i)) \<in> ?rel^* O ?rel O ?rel^="
      (is "?pair \<in> _") by blast
    then have "?pair \<in> ?rel^+ O ?rel^=" by (simp only:  O_assoc[symmetric] trancl_unfold_right)
    then show "?pair \<in> ?rel^+" by (simp only: trancl_o_refl_is_trancl)
  qed
  then have "\<not> SN_on (?rel^+) {?t 0}" unfolding SN_on_def by auto
  then have "\<not> SN_on ?rel {?t 0}" using SN_on_trancl[of ?rel] by auto
  then have "\<not> SN_on (qrstep nfs Q R) {?t 0}"
    using SN_on_qrstep_imp_SN_on_supt_union_qrstep[of nfs Q R] by auto
  with sn show False unfolding SN_on_def by auto
qed


lemma infinite_dpp_mono: assumes P: "P \<subseteq> P'" and R: "R \<subseteq> R'" and Q: "NF_terms Q \<subseteq> NF_terms Q'"
  and nfs: "Q \<noteq> {} \<Longrightarrow> nfs' \<Longrightarrow> nfs"
  and inf: "infinite_dpp (nfs,P,Q,R)"
  shows "infinite_dpp (nfs',P',Q',R')"
proof (rule ccontr)
  note conv = infinite_dpp_not_SN_conv not_not
  assume "\<not> ?thesis"
  from this[unfolded conv] have SN: "SN (rqrstep nfs' Q' P' \<union> qrstep nfs' Q' R')" .
  have P: "rqrstep nfs Q P \<subseteq> rqrstep nfs' Q' P'"
    by (rule rqrstep_all_mono[OF P Q nfs])
  have R: "qrstep nfs Q R \<subseteq> qrstep nfs' Q' R'"
    by (rule qrstep_all_mono[OF R Q nfs])
  have "SN (rqrstep nfs Q P \<union> qrstep nfs Q R)"
    by (rule SN_subset[OF SN], insert P R, auto)
  with inf[unfolded conv] show False by simp
qed    

lemma infinite_dpp_rename_vars: assumes infin: "infinite_dpp (nfs,P,Q,R)"
  and P: "\<And> st. st \<in> P \<Longrightarrow> \<exists> st'. st' \<in> P' \<and> st =\<^sub>v st'"
  shows "infinite_dpp (nfs,P',Q,R)"
proof -
  have P: "rqrstep nfs Q P \<subseteq> rqrstep nfs Q P'" by (rule rqrstep_rename_vars[OF P])
  with infin show ?thesis unfolding infinite_dpp_not_SN_conv SN_defs by blast
qed

lemma loop_imp_infinite_empty_Q:
  assumes "(s, s \<cdot> \<sigma>) \<in> (rrstep P \<union> rstep R)^+"
  shows "infinite_dpp (nfs,P, {}, R)"
proof -
  obtain PR where PR: "PR = rrstep P \<union> rstep R" by auto
  from subst.closed_Un[OF subst_closed_rrstep subst_closed_rstep] PR
    have subst: "subst.closed PR" by simp
  from PR assms have steps: "(s,s \<cdot> \<sigma>) \<in> PR^+" by simp
  from stable_loop_imp_not_SN[OF subst steps] have "\<not> SN PR" unfolding SN_on_def by auto
  then show ?thesis unfolding infinite_dpp_not_SN_conv PR by simp
qed


lemma loop_imp_infinite:
  assumes steps: "\<And> i. (s \<cdot> \<sigma>^^i, s \<cdot> \<sigma> \<cdot> \<sigma>^^i) \<in> (rqrstep nfs Q P \<union> qrstep nfs Q R)^+"
  shows "infinite_dpp (nfs,P, Q, R)"
proof -
  obtain PR where PR: "PR = rqrstep nfs Q P \<union> qrstep nfs Q R" by auto
  let ?s = "\<lambda> i. s \<cdot> \<sigma>^^i"
  show ?thesis unfolding  infinite_dpp_not_SN_conv PR[symmetric]
  proof
    assume "SN PR"
    then have "SN_on PR {?s 0}" unfolding SN_on_def by auto
    from SN_on_trancl[OF this] have "SN_on (PR^+) {?s 0}" .
    moreover
    {
      fix i
      have "(?s i, ?s (Suc i)) \<in> PR^+" using steps[of i] unfolding PR by simp
    }
    ultimately show False unfolding SN_defs by best
  qed
qed

lemma loop_imp_not_SN_qrel_empty_Q:
  assumes steps: "(s, C\<langle>s \<cdot> \<sigma>\<rangle>) \<in> (rstep (R \<union> S))^* O rstep R O (rstep (R \<union> S))^*"
  shows "\<not> SN_qrel (nfs,{}, R, S)"
proof
  let ?RS = "rstep (R \<union> S)"
  let ?SRS = "?RS^* O rstep R O ?RS^*"
  let ?R = "rel_rstep (R,S) \<union> {\<rhd>}"
  have subset: "?SRS \<subseteq> (rel_rstep (R, S))^+" unfolding relto_trancl_conv rstep_union
    by (simp, regexp)
  with steps have steps: "(s,C\<langle>s \<cdot> \<sigma>\<rangle>) \<in> (rel_rstep (R,S))^+" by auto
  assume "SN_qrel (nfs,{},R,S)"
  then have SN: "SN (rel_rstep (R,S))" unfolding SN_rel_defs SN_qrel_def by simp
  from SN_imp_SN_union_supt[OF SN]  ctxt_closed_rel_qrstep[of "(nfs,{},R,S)"]
  have SN: "SN_on ?R {s}" unfolding SN_on_def by auto
  from subst.closed_Un[OF subst_closed_rel_rstep subst_closed_supt]
  have subst: "subst.closed ?R" .
  have steps: "(s, C\<langle>s \<cdot> \<sigma>\<rangle>) \<in> ?R^+" using trancl_mono[OF steps] by auto
  have "(s, s \<cdot> \<sigma>) \<in> ?R^+"
  proof (cases C)
    case Hole
    with steps  show ?thesis by simp
  next
    case (More f bef D aft)
    with ctxt_supt[of C _ "s \<cdot> \<sigma>"] have "C\<langle>s \<cdot> \<sigma>\<rangle> \<rhd> s \<cdot> \<sigma>" by simp 
    then have "(C\<langle>s \<cdot> \<sigma>\<rangle>, s \<cdot> \<sigma>) \<in> ?R" unfolding supt_def by auto
    with steps show ?thesis by (rule trancl_into_trancl)
  qed
  from stable_loop_imp_not_SN[OF subst this] SN 
  show False ..
qed

lemma loop_imp_not_SN_qrel:
  assumes loop: "\<And> i. \<exists> C. (t \<cdot> \<mu> ^^ i, C\<langle>t \<cdot> \<mu> \<cdot> \<mu> ^^ i\<rangle>) \<in> (qrstep nfs Q (R \<union> S))^* O qrstep nfs Q R O (qrstep nfs Q (R \<union> S))^*"
  shows "\<not> SN_qrel (nfs,Q, R, S)"
proof
  let ?R = "qrstep nfs Q R"
  let ?S = "qrstep nfs Q S"
  let ?B = "?S^* O ?R O ?S^*"
  let ?B' = "(?R \<union> ?S)^* O ?R O (?R \<union> ?S)^*"
  obtain B where B: "B = (?B' O {\<unrhd>})" by auto
  let ?t = "\<lambda> i. t \<cdot> \<mu> ^^ i"
  assume "SN_qrel (nfs,Q,R,S)"
  from this[unfolded SN_qrel_def split SN_rel_defs]
  have sn: "SN_on ?B {?t 0}" unfolding SN_on_def by auto
  have sn: "SN_on ({\<rhd>} \<union> ?B) {?t 0}"
    by (rule SN_on_r_imp_SN_on_supt_union_r[OF _ sn], blast)
  have sn: "SN_on B {?t 0}" unfolding B supteq_supt_set_conv
    by (rule SN_on_subset1[OF SN_on_trancl[OF sn]], regexp)
  moreover {
    fix i
    from loop[of i] obtain C where "(?t i, C\<langle>?t (Suc i)\<rangle>) \<in> ?B'" 
      unfolding qrstep_union by auto
    moreover have "(C\<langle>?t (Suc i)\<rangle>, ?t (Suc i)) \<in> {\<unrhd>}" by auto
    ultimately have "(?t i, ?t (Suc i)) \<in> B" unfolding B by auto
  }
  ultimately show False unfolding SN_defs by best
qed

lemma instantiation_ichain : 
  assumes ichain: "\<exists>s' t' \<sigma>'. i_chain (nfs,P', Q, R) s' t' \<sigma>'"
  and inst: "\<forall> (s',t') \<in> P'. \<exists> (s,t) \<in> P. \<exists> \<delta>. s \<cdot> \<delta> = s' \<and> t \<cdot> \<delta> = t'"
  and nfs: "\<not> nfs \<or> Q = {}"
  shows "\<exists>s t \<sigma>. i_chain (nfs,P, Q, R) s t \<sigma>"
proof -
  from ichain obtain s' t' \<sigma>' where ic:
    "(\<forall>i. (s' i, t' i) \<in> P') \<and>
    (\<forall>i. (t' i \<cdot> \<sigma>' i, s' (Suc i) \<cdot> \<sigma>' (Suc i)) \<in> (qrstep nfs Q R)\<^sup>*) \<and>
    (\<forall>i u. s' i \<cdot> \<sigma>' i \<rhd> u \<longrightarrow> u \<in> NF_terms Q)" by auto
  then have mem:"\<And>i. (s' i, t' i) \<in> P'" by auto
  {
    fix i
    from mem[of i] inst have "\<exists> (s,t) \<in> P. \<exists> \<delta>. (s' i) = s \<cdot> \<delta> \<and> (t' i) = t \<cdot> \<delta>"
      by blast
  }
  then have "\<forall> i. \<exists> s t \<delta>. (s,t) \<in> P \<and> (s' i) = s \<cdot> \<delta> \<and> (t' i) = t \<cdot> \<delta>" by blast
  from choice[OF this] obtain s where 
    "\<forall> i. \<exists> t \<delta>. (s i,t) \<in> P \<and> (s' i) = (s i) \<cdot> \<delta> \<and> (t' i) = t \<cdot> \<delta>" ..
  from choice[OF this] obtain t where 
    "\<forall> i. \<exists> \<delta>. (s i,t i) \<in> P \<and> (s' i) = (s i) \<cdot> \<delta> \<and> (t' i) = (t i) \<cdot> \<delta>" ..
  from choice[OF this] obtain \<delta> where sim:
    "\<forall> i. (s i,t i) \<in> P \<and> (s' i) = (s i) \<cdot> (\<delta> i) \<and> (t' i) = (t i) \<cdot> (\<delta> i)" ..       
  let ?\<gamma> = "\<lambda> i. (\<delta> i) \<circ>\<^sub>s (\<sigma>' i)"
  from sim ic have "i_chain (nfs,P,Q,R) s t ?\<gamma>" using nfs by auto
  then show ?thesis by blast
qed

   
lemma instantiation_inf :
  assumes inf: "infinite_dpp (nfs,P', Q, R)"
  and inst: "\<forall> (s',t') \<in> P'. \<exists> (s,t) \<in> P. \<exists> \<delta>. s \<cdot> \<delta> = s' \<and> t \<cdot> \<delta> = t'"
  and nfs: "\<not> nfs \<or> Q = {}"
  shows "infinite_dpp (nfs,P,Q,R)"
proof -
  from inf have 
    "((\<not> SN (qrstep nfs Q R)) \<or> (\<exists>s' t' \<sigma>. i_chain (nfs,P', Q, R) s' t' \<sigma>))" 
    by (simp only: infinite_dpp.simps)
  then show ?thesis proof (rule disjE)
    assume "(\<not> SN (qrstep nfs Q R))"
    then show "infinite_dpp (nfs,P,Q,R)" by auto
  next
    assume "\<exists>s' t' \<sigma>. i_chain (nfs,P', Q, R) s' t' \<sigma>"
    with inst instantiation_ichain[of nfs P' Q R P] nfs have "\<exists>s t \<sigma>. i_chain (nfs,P, Q, R) s t \<sigma>" 
      by blast
    then show ?thesis by (auto simp only: infinite_dpp.simps) 
  qed
qed   

end

