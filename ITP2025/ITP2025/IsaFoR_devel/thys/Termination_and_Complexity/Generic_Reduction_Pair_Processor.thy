(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Generic_Reduction_Pair_Processor
imports
  Generic_Usable_Rules
  TRS.QDP_Framework
begin


lemma generic_redtriple_proc: 
  assumes checker: "usable_rules_checker checker"
  and U: "set U \<subseteq> NS"
  and oP: "P \<subseteq> NST \<union> S"
  and redtriple: "af_redtriple S NS NST \<pi>"
  and ce: "ce \<Longrightarrow> ce_compatible NS" 
  and check: "checker nfs m ce (wwf_qtrs Q (set R)) \<pi> Q R U_opt P = Some U"
  shows "\<not> min_ichain (nfs,m,S \<inter> P, P - S, Q, {}, set R) s t \<sigma>"
proof   
  assume chain: "min_ichain (nfs,m,S \<inter> P, P - S, Q, {}, set R) s t \<sigma>"
  let ?Q = "NF_terms Q"
  let ?R = "qrstep nfs Q (set R)"
  interpret af_redtriple S NS NST \<pi> by fact
  have redpair: "af_redpair S NS \<pi>" ..
  note checker = checker[unfolded usable_rules_checker_def, rule_format, OF check redpair U ce]
  from checker obtain f where f: "\<And> s t u \<sigma> \<tau>. (s,t) \<in> P \<Longrightarrow> s \<cdot> \<sigma> \<in> ?Q \<Longrightarrow> NF_subst nfs (s,t) \<sigma> Q \<Longrightarrow> 
    (t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> ?R^* \<Longrightarrow> (m \<Longrightarrow> SN_on ?R {t \<cdot> \<sigma>}) \<Longrightarrow> (t \<cdot> f \<sigma>, u \<cdot> f \<tau>) \<in> NS^*" by blast
  note chain = chain[unfolded min_ichain.simps ichain.simps minimal_cond_def]
  from chain have P: "\<And> i. (s i, t i) \<in> P" by auto
  from chain have Q: "\<And> i. s i \<cdot> \<sigma> i \<in> ?Q" by auto
  from chain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
  from chain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R^*" by auto
  from chain have SNt: "\<And> i. m \<Longrightarrow> SN_on ?R {t i \<cdot> \<sigma> i}" by auto
  let ?s = "\<lambda> i. s i \<cdot> f (\<sigma> i)"
  let ?t = "\<lambda> i. t i \<cdot> f (\<sigma> i)"
  let ?next = "\<lambda> i. (s (Suc i), t (Suc i))"
  from f[OF P Q nfs steps SNt] have stepsNS: "\<And> i. (?t i, ?s (Suc i)) \<in> NS^*" by simp
  from oP P have allP: "\<And> i. (s i, t i) \<in> NST \<union> S" by (auto simp: ichain.simps)
  from chain have inf: "INFM i. (s i, t i) \<in> S \<inter> P" by simp
  have piece1: "\<forall> i. (?t i, ?t (Suc i)) \<in> S \<or> (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* \<and> (?next i) \<notin> S"
  proof
    fix i
    show "(?t i, ?t (Suc i)) \<in> S \<or> (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* \<and> (?next i) \<notin> S" 
    proof (cases "?next i \<in> S")
      case True
      then have "(?s (Suc i), ?t (Suc i)) \<in> S" using subst_S by (auto simp: subst.closed_def)
      with stepsNS NS.trCompat show ?thesis by auto 
    next
      case False
      with stepsNS allP[of "Suc i"]
      have one: "?next i \<in> NST" and two: "?next i \<notin> S" by auto
      from one have "(?s (Suc i), ?t (Suc i)) \<in> NST" using subst_NST by (auto simp: subst.closed_def)
      with stepsNS[of i] have steps: "(?t i, ?t (Suc i)) \<in> NS^* O NST" by auto
      have "(?t i, ?t (Suc i)) \<in> (NS \<union> NST)^*"
        by (rule set_mp[OF _ steps], regexp)
      with two show ?thesis by simp
    qed
  qed  
  then have infSeq: "\<forall> i. (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* \<union> S" by auto
  from SN have "SN_on S {?t 0}" by best
  from infSeq both.trCompat this have "\<exists> j. \<forall> i \<ge> j. (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* - S" by (rule non_strict_ending)  
  from this obtain j where one: "\<forall> i \<ge> j. (?t i, ?t (Suc i)) \<in> (NS \<union> NST)^* - S" ..
  with piece1 have ns: "\<forall> i \<ge> j. ?next i \<notin> S" by blast
  from inf[unfolded INFM_nat] obtain n where n: "n > j" and s: "(s n, t n) \<in> S" by auto
  from n obtain m where n: "n = Suc m" and m: "m \<ge> j" by (cases n, auto)
  from ns[THEN spec[of _ m]] s show False unfolding n using m by auto
qed


lemma generic_root_redtriple_proc: 
  assumes checker: "usable_rules_checker (checker :: ('f,'v)usable_rules_checker)"
  and U: "set U \<subseteq> NS"
  and oP: "P \<subseteq> NST \<union> S"
  and Pcond: "\<And> s t. (s,t) \<in> P \<Longrightarrow> is_Fun s \<and> is_Fun t"
  and redtriple: "af_root_redtriple_order S NS NST \<pi> \<pi>'"
  and ce: "ce \<Longrightarrow> ce_compatible NS" 
  and check: "checker nfs m ce (wwf_qtrs Q (set R)) \<pi> Q R U_opt 
    {(s,ts ! i) | s f ts i. (s,Fun f ts) \<in> P \<and> i < length ts \<and> i \<in> \<pi>' (f,length ts)} = Some U"
   (is "checker nfs m ce _ \<pi> Q R U_opt ?P = Some U")
  shows "\<not> nr_min_ichain (nfs,m,S \<inter> P, P - S, Q, set R) s t \<sigma>"
proof 
  assume chain: "nr_min_ichain (nfs,m,S \<inter> P, P - S, Q, set R) s t \<sigma>"
  let ?Q = "NF_terms Q"
  let ?R = "qrstep nfs Q (set R)"
  let ?N = "nrqrstep nfs Q (set R)"
  interpret af_root_redtriple_order S NS NST \<pi> \<pi>' by fact
  have redpair: "af_redpair S NS \<pi>" ..
  note checker = checker[unfolded usable_rules_checker_def, rule_format, OF check redpair U ce]
  from checker obtain f where f: "\<And> s t u \<sigma> \<tau>. (s,t) \<in> ?P \<Longrightarrow> s \<cdot> \<sigma> \<in> ?Q \<Longrightarrow> NF_subst nfs (s,t) \<sigma> Q \<Longrightarrow> 
    (t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> ?R^* \<Longrightarrow> (m \<Longrightarrow> SN_on ?R {t \<cdot> \<sigma>}) \<Longrightarrow> (t \<cdot> f \<sigma>, u \<cdot> f \<tau>) \<in> NS^*" by blast
  note chain = chain[unfolded nr_min_ichain.simps nr_ichain.simps minimal_cond_def]
  from chain have P: "\<And> i. (s i, t i) \<in> P" by auto
  from chain have Q: "\<And> i. s i \<cdot> \<sigma> i \<in> ?Q" by auto
  from chain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
  from chain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?N^*" by auto
  from chain have SNt: "\<And> i. m \<Longrightarrow> SN_on ?R {t i \<cdot> \<sigma> i}" by auto
  let ?s = "\<lambda> i. s i \<cdot> f (\<sigma> i)"
  let ?t = "\<lambda> i. t i \<cdot> f (\<sigma> i)"
  let ?next = "\<lambda> i. (s (Suc i), t (Suc i))"
  {
    fix i
    note P = P[of i] P[of "Suc i"]
    from Pcond[OF P(1)] obtain g ts where ti: "t i = Fun g ts" by force
    from Pcond[OF P(2)] obtain h ss where si: "s (Suc i) = Fun h ss" by force
    let ?ts = "map (\<lambda> t. t \<cdot> \<sigma> i) ts"
    let ?ss = "map (\<lambda> t. t \<cdot> \<sigma> (Suc i)) ss"
    let ?fts = "map (\<lambda> t. t \<cdot> f (\<sigma> i)) ts" 
    let ?fss = "map (\<lambda> t. t \<cdot> f (\<sigma> (Suc i))) ss" 
    have id: "t i \<cdot> \<sigma> i = Fun g ?ts" "s (Suc i) \<cdot> \<sigma> (Suc i) = Fun h ?ss" unfolding si ti by auto
    from nrqrsteps_preserve_root[OF steps[of i], unfolded id] have hg:  "h = g" "length ts = length ss" by auto
    note arg_steps = nrqrsteps_imp_arg_qrsteps[OF steps[of i], unfolded id term.sel]
    {
      fix j
      assume j: "j < length ts" and "j \<in> \<pi>' (g,length ts)"
      with P have s: "(s i, ts ! j) \<in> ?P" unfolding ti by auto
      note f = f[OF this Q[of i]]
      from ti j have "ts ! j \<in> set (args (t i))" by auto
      then have "vars_term (ts ! j) \<subseteq> vars_term (t i)" unfolding ti by auto
      with nfs[of i] have "NF_subst nfs (s i, ts ! j) (\<sigma> i) Q" unfolding NF_subst_def vars_rule_def by auto
      note f = f[OF this]
      from arg_steps[of j] j hg have "(ts ! j \<cdot> \<sigma> i, ss ! j \<cdot> \<sigma> (Suc i)) \<in> ?R^*" by auto
      note f = f[OF this]
      {
        assume m
        have "SN_on ?R {ts ! j \<cdot> \<sigma> i}"
          by (rule SN_imp_SN_arg_gen[OF ctxt_closed_qrstep SNt[of i, unfolded id, OF \<open>m\<close>]], insert j, auto)
      }
      note f = f[OF this]
      from f have "(?fts ! j, ?fss ! j) \<in> NS^*" using j hg by auto
    } note NS = this
    let ?rel = "\<lambda> i. if i \<in> \<pi>' (g,length ts) then NS^* else UNIV"
    note cong = args_steps_imp_steps_gen[of ?rel]
    note af = af_compat'[unfolded af_compatible_def, rule_format, of _ g]
    have "(t i \<cdot> f (\<sigma> i), s (Suc i) \<cdot> f (\<sigma> (Suc i))) \<in> NST^*" unfolding ti si hg eval_term.simps
    proof (rule cong, unfold length_map hg(2)[symmetric])
      fix s t and bef aft :: "('f,'v)term list"
      assume st: "(s,t) \<in> ?rel (length bef)" and len: "length ts = Suc (length bef + length aft)"
      show "(Fun g (bef @ s # aft), Fun g (bef @ t # aft)) \<in> NST^*"
      proof (cases "length bef \<in> \<pi>' (g,length ts)")
        case False
        with af[of bef aft s t, unfolded len[symmetric]] show ?thesis by auto
      next
        case True
        with st have st: "(s,t) \<in> NS^*" by simp
        show ?thesis
          by (rule compat_NSs_root[OF st])
      qed
    qed (insert NS, auto)
  } 
  then have stepsNS: "\<And> i. (?t i, ?s (Suc i)) \<in> NST^*" .
  from oP P have allP: "\<And> i. (s i, t i) \<in> NST \<union> S" by (auto simp: ichain.simps)
  from chain have inf: "INFM i. (s i, t i) \<in> S \<inter> P" by simp
  have piece1: "\<forall> i. (?t i, ?t (Suc i)) \<in> S \<or> (?t i, ?t (Suc i)) \<in> NST^* \<and> (?next i) \<notin> S"
  proof
    fix i
    show "(?t i, ?t (Suc i)) \<in> S \<or> (?t i, ?t (Suc i)) \<in> NST^* \<and> (?next i) \<notin> S" 
    proof (cases "?next i \<in> S")
      case True
      then have "(?s (Suc i), ?t (Suc i)) \<in> S" using subst_S by (auto simp: subst.closed_def)
      with stepsNS compat_NSTs show ?thesis by auto 
    next
      case False
      with stepsNS allP[of "Suc i"]
      have one: "?next i \<in> NST" and two: "?next i \<notin> S" by auto
      from one have "(?s (Suc i), ?t (Suc i)) \<in> NST" using subst_NST by (auto simp: subst.closed_def)
      with stepsNS[of i] have steps: "(?t i, ?t (Suc i)) \<in> NST^*" by auto
      with two show ?thesis by simp
    qed
  qed  
  then have infSeq: "\<forall> i. (?t i, ?t (Suc i)) \<in> NST^* \<union> S" by auto
  from compat_NSTs have compat: "NST^* O S \<subseteq> S" by auto
  from SN have "SN_on S {?t 0}" by best
  from non_strict_ending[OF infSeq compat, OF this] 
  obtain j where one: "\<forall> i \<ge> j. (?t i, ?t (Suc i)) \<in> NST^* - S" ..
  with piece1 have ns: "\<forall> i \<ge> j. ?next i \<notin> S" by blast
  from inf[unfolded INFM_nat] obtain n where n: "n > j" and s: "(s n, t n) \<in> S" by auto
  from n obtain m where n: "n = Suc m" and m: "m \<ge> j" by (cases n, auto)
  from ns[THEN spec[of _ m]] s show False unfolding n using m by auto
qed

lemma root_redtriple_sound:
  assumes checker: "usable_rules_checker checker"
  and check: "checker nfs m ce (wwf_qtrs Q (set R)) \<pi> Q R U_opt 
    {(s,ts ! i) | s f ts i. (s,Fun f ts) \<in> P \<and> i < length ts \<and> i \<in> \<pi>' (f,length ts)} = Some U"
  and U: "set U \<subseteq> NS"
  and oP: "P \<subseteq> NST \<union> S"
  and Pcond: "\<And> s t. (s,t) \<in> P \<Longrightarrow> is_Fun s \<and> is_Fun t"
  and Rcond: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> is_Fun l"
  and ndef: "\<forall> (s,t) \<in> P. \<not> defined (set R) (the (root t))"
  and redtriple: "af_root_redtriple_order S NS NST \<pi> \<pi>'"
  and ce: "ce \<Longrightarrow> ce_compatible NS" 
  shows "\<not> min_ichain (nfs,m,S \<inter> P, P - S, Q, {}, (set R)) s t \<sigma>"
proof 
  assume ichain: "min_ichain (nfs,m,S \<inter> P, P - S, Q, {}, (set R)) s t \<sigma>"
  have "nr_min_ichain (nfs,m,S \<inter> P, P - S, Q, (set R)) s t \<sigma>"
    by (rule min_ichain_imp_nr_min_ichain[OF ichain], insert ndef Pcond Rcond, auto)
  with generic_root_redtriple_proc[OF checker U oP Pcond redtriple ce, OF _ _ check]
  show False ..
qed


end

