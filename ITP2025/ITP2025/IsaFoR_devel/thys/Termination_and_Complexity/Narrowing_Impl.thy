(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Narrowing_Impl
imports
  Innermost_Usable_Rules_Impl
  Dependency_Graph_Impl
  Narrowing
  Rewriting_Impl
begin      

definition qnarrows_impl :: "(('f,string)term \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)term \<Rightarrow> (('f,string)term \<times> ('f,string)subst) list"
  where "qnarrows_impl isnf nfs R t \<equiv> concat (map (\<lambda> p. let tp = t |_ p in
  if is_Fun tp then [(replace_at (t \<cdot> \<mu>1) p (r \<cdot> \<mu>2), \<mu>1). (l,r) \<leftarrow> R,
    (\<mu>1,\<mu>2) \<leftarrow> option_to_list (mgu_vd_string tp l),
    NF_subst_impl isnf nfs (l,r) \<mu>2, (\<forall> la \<in> set (args (l \<cdot> \<mu>2)). isnf la)] else []) (poss_list t))"

lemma qnarrows_impl[simp]:
  "set (qnarrows_impl (\<lambda> t. t \<in> NF_terms Q) nfs R t) = {(t',\<mu>). \<exists> r p. (t,t') \<in> qnarrows_r_p_s nfs Q (set R) r p \<mu>}" (is "?l = ?r")
proof -
  note d = qnarrows_impl_def[unfolded Let_def]  qnarrows_r_p_s_def
  note sc = set_concat set_map split
  {
    fix t' \<mu>
    assume "(t',\<mu>) \<in> ?r"
    from this[unfolded d] obtain lr p \<mu>2 where
      p: "p \<in> poss t" and
      tp: "is_Fun (t |_ p)" and
      R: "lr \<in> set R" and
      mgu: "mgu_vd_string (t |_ p) (fst lr) = Some (\<mu>,\<mu>2)" and
      NF: "set (args (fst lr \<cdot> \<mu>2)) \<subseteq> NF_terms Q" and
      nfs: "NF_subst nfs lr \<mu>2 Q" and
      t': "t' = replace_at (t \<cdot> \<mu>) p (snd lr \<cdot> \<mu>2)" by blast
    from tp have tp: "\<And> r q. (if is_Fun (t |_ p) then r else q) = r" by simp
    obtain l r where lr: "lr = (l,r)" by force
    have "(t',\<mu>) \<in> ?l"
      unfolding d sc
      by (rule, unfold poss_list_sound, rule imageI[OF p], unfold tp sc,
      rule, rule imageI[OF R[unfolded lr]], unfold sc, rule, rule imageI[of "(\<mu>,\<mu>2)"],
      insert mgu NF nfs t' lr, auto)
  }
  then have "?r \<subseteq> ?l" by blast
  moreover
  {
    fix t' \<mu>
    assume "(t',\<mu>) \<in> ?l"
    from this[unfolded d sc]
    obtain p l r \<mu>2 where
      p: "p \<in> poss t" and tp: "is_Fun (t |_ p)" and
      lr: "(l,r) \<in> set R" and
      mgu: "mgu_vd_string (t |_ p) l = Some (\<mu>,\<mu>2)" and
      NF: "\<forall> t \<in> set (args (l \<cdot> \<mu>2)). t \<in> NF_terms Q" and
      nfs: "NF_subst nfs (l,r) \<mu>2 Q" and
      t': "t' = replace_at (t \<cdot> \<mu>) p (r \<cdot> \<mu>2)" by auto
    have "(t',\<mu>) \<in> ?r"
      unfolding d
      by (rule, unfold sc, rule exI[of _ "(l,r)"], rule exI[of _ p], rule, unfold sc, rule exI[of _ \<mu>2],
      insert p tp lr mgu NF nfs t', auto)
  } then have "?l \<subseteq> ?r" by blast
  ultimately show ?thesis by blast
qed

definition
  narrowing_proc ::
    "('dpp, 'f :: {showl, compare_order}, string) dpp_ops \<Rightarrow>
     ('f,string)rule \<Rightarrow> pos \<Rightarrow> ('f,string)rules \<Rightarrow> 'dpp proc"
where
  "narrowing_proc I st p sts dpp \<equiv>
    check_return (do {
     let (s,t) = st;
     let q = dpp_ops.Q I dpp;
     check (dpp_ops.NFQ_subset_NF_rules I dpp \<or> q = [] \<and> linear_term t) (showsl_lit (STR ''innermost or full rewriting required (and linearity of t in full rewriting case)''));
     let ic = icap_impl_dpp_mv I dpp;
     let isnf = dpp_ops.is_QNF I dpp;
     let pairs = dpp_ops.pairs I dpp;
     check (p \<in> set (poss_list t)) (showsl_lit (STR ''position not contained in '') \<circ> showsl t);
     let tp = t |_ p;
     let nftp = isnf tp;
     check (p \<in> set (poss_list (ic [s] t)) \<or> \<not> nftp) (showsl_lit (STR ''neither is position contained in capped term of t, nor is t|_p not in Q-normal form''));
     let nfs = dpp_ops.nfs I dpp;
     let narrows = qnarrows_impl isnf nfs (dpp_ops.rules I dpp) tp;
     let sts' = filter (\<lambda> (smu,_). isnf smu) (map (\<lambda> (t',\<mu>). (s \<cdot> \<mu>, replace_at (t \<cdot> \<mu>) p t')) narrows);
     check_allm (\<lambda> new. check (\<exists> st' \<in> set sts. instance_rule new st' \<and> (\<not> nfs \<or> q = [] \<or> wf_rule st'))
                (showsl_lit (STR ''could not find narrowed pair '') \<circ> showsl_rule new)) sts';
     let iedg = is_iedg_edge_dpp I dpp (s,t);
     check_subseteq (vars_term_list tp) (vars_term_list s) <+? (\<lambda> x. showsl_lit (STR ''variable '') o showsl x o showsl_lit (STR '' only occurs on rhs of pair''));
     check (st \<in> set (dpp_ops.P I dpp) \<or> dpp_ops.R I dpp = []) (showsl_lit (STR ''strict DP or no strict rules required''));
     (if nftp then check_allm (\<lambda> (u,v).
         do {
             check (p \<in> set (poss_list u)) (showsl_lit (STR ''position not contained in lhs of pair '') \<circ> showsl_rule (u,v));
             case mgu_vd_string tp (u |_ p) of None \<Rightarrow> succeed | Some (\<mu>1,\<mu>2) \<Rightarrow> check (\<not> isnf (s \<cdot> \<mu>1) \<or> \<not> isnf (u \<cdot> \<mu>2)) (showsl_lit (STR ''t |_ p and u |_ p unify and satisfy variable condition for pair (u,v) = '')
                \<circ> showsl_rule (u,v))
         }) (filter (\<lambda> (u,v). iedg u) pairs)
       else succeed)
   })
   (dpp_ops.replace_pair I dpp st sts)"

lemma narrowing_proc: assumes I: "dpp_spec I"
 shows "dpp_spec.sound_proc_impl I (narrowing_proc I (st :: ('f :: {showl, compare_order},string)rule)
  p sts)"
proof -
  from assms interpret dpp_spec I .
  show ?thesis
  proof
    fix d d'
    assume ok: "narrowing_proc I st p sts d = Inr d'" and fin: "finite_dpp (dpp d')"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?Q = "set (Q d)"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?Rb = "?R \<union> ?Rw"
    let ?Rb' = "set (rules d)"
    let ?Pb = "?P \<union> ?Pw"
    let ?Pb' = "set (pairs d)"
    let ?nfs = "NFS d"
    let ?m = "M d"
    obtain s t where st: "st = (s,t)" by force
    note ok = ok[unfolded narrowing_proc_def st icap_impl_dpp_icap_mv[OF I] Let_def dpp_spec_sound, simplified]
    from ok have d': "d' = replace_pair d (s,t) sts" by auto
    have d': "dpp d' = (?nfs,?m,replace (s,t) (set sts) ?P, replace (s,t) (set sts) ?Pw, ?Q, ?R, ?Rw)"
      unfolding d' unfolding replace_pair_sound by simp
    note fin = fin[unfolded this]
    note ok_narrow = ok[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
    note ok_precond = ok[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
    from ok have pt: "p \<in> poss t" by auto
    show "finite_dpp (dpp d)" unfolding dpp_spec_sound
    proof (rule narrowing_proc[OF fin _ _ _ _ _ pt _ icap])
      from ok show "(s,t) \<in> ?P \<or> ?R = {}" by auto
      from ok show "linear_term t \<and> ?Q = {} \<or> NF_terms ?Q \<subseteq> NF_trs ?Rb" by auto
      from ok show "vars_term (t |_ p) \<subseteq> vars_term s" by auto
      from ok have "p \<in> poss (icap_mv ?Rb ?Q {s} t) \<or> t |_ p \<notin> NF_terms ?Q" by simp
      then show "p \<in> poss (icap' ?Rb ?Q {mv_xvar s} (mv_xvar t)) \<or> t |_ p \<notin> NF_terms ?Q" unfolding icap_mv_def using icap'[of ?Rb ?Q "{s}" t] by auto
    next
      fix u v
      assume tp: "t |_ p \<in> NF_terms ?Q" and edge: "((s,t),(u,v)) \<in> DG ?nfs ?m ?Pb ?Q ?Rb"
      from edge[unfolded DG_def] obtain \<sigma> \<tau> where steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep ?nfs ?Q ?Rb)^*"
        and NFs: "s \<cdot> \<sigma> \<in> NF_terms ?Q" and NFu: "u \<cdot> \<tau> \<in> NF_terms ?Q"
        and nfs: "NF_subst ?nfs (s,t) \<sigma> ?Q" "NF_subst ?nfs (u,v) \<tau> ?Q"
        and SN: "?m \<Longrightarrow> SN_on (qrstep ?nfs ?Q ?Rb) {t \<cdot> \<sigma>}"
        and mem: "(u,v) \<in> ?Pb" by auto
      have edge: "is_iedg_edge_dpp I d (s,t) u"
        by (rule is_iedg_edge_dpp_sound[OF I NFs NFu nfs], insert SN steps, auto)
      then have edge: "is_iedg_edge_dpp I d (s,t) u = True" by simp
      from tp have tp: "t |_ p \<in> NF_terms ?Q = True" by simp
      note ok = ok_precond[unfolded tp, simplified, rule_format, of u v, unfolded edge]
      from ok mem have pu: "p \<in> poss u" by simp
      show "p \<in> poss u \<and> (\<forall> \<mu>1 \<mu>2. mgu_vd_string (t |_ p) (u |_ p) = Some (\<mu>1,\<mu>2) \<longrightarrow> \<not> {s \<cdot> \<mu>1, u \<cdot> \<mu>2} \<subseteq> NF_terms ?Q)"
      proof (rule conjI[OF pu], intro allI impI)
        fix \<mu>1 \<mu>2
        assume mgu: "mgu_vd_string (t |_ p) (u |_ p) = Some (\<mu>1, \<mu>2)"
        from ok[unfolded mgu] mem show "\<not> {s \<cdot> \<mu>1, u \<cdot> \<mu>2} \<subseteq> NF_terms ?Q" by auto
      qed
    next
      fix rule q t' \<mu>
      assume narr: "(t |_ p, t') \<in> qnarrows_r_p_s ?nfs ?Q ?Rb rule q \<mu>" and smu: "s \<cdot> \<mu> \<in> NF_terms ?Q"
      obtain l r where rule: "rule = (l,r)" by force
      from narr[unfolded rule] have narr: "(t |_ p, t') \<in> qnarrows_r_p_s (NFS d) ?Q ?Rb (l, r) q \<mu>" .
      from ok_narrow[rule_format, of "s \<cdot> \<mu>" "replace_at (t \<cdot> \<mu>) p t'"] narr smu
      show "\<exists> st' \<in> set sts. instance_rule (s \<cdot> \<mu>, replace_at (t \<cdot> \<mu>) p t') st' \<and>
         (\<not> ?nfs \<or> ?Q = {} \<or> wf_rule st')" by force
    qed
  qed
qed

definition
  rstep_enum_impl ::
    "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow>
    (('f, 'v) rule \<times> ('f, 'v) subst \<times> pos) list"
where
  "rstep_enum_impl R t t' p = concat (map (\<lambda> p.
    let tp = t |_ p in
    [((l, r), \<mu>, p). p \<in> set (poss_list t'),
      ctxt_of_pos_term p t = ctxt_of_pos_term p t', tp' \<leftarrow> [t' |_ p], (l, r) \<leftarrow> R,
      \<mu> \<leftarrow> option_to_list (Matching.match_list Var [(l, tp),(r, tp')])]) (filter (\<lambda>q. p \<le> q) (poss_list t)))"

lemma rstep_enum_impl:
  assumes mem: "(lr, \<mu>, q) \<in> set (rstep_enum_impl R t t' p)"
  shows "(t, t') \<in> rstep_r_p_s (set R) lr q \<mu> \<and> p \<le> q"
proof -
  obtain l r where lr: "lr = (l,r)" by force
  note mem = mem[unfolded rstep_enum_impl_def Let_def lr, simplified]
  let ?C = "ctxt_of_pos_term q"
  from mem have C: "?C t = ?C t'" by auto
  from mem
    have match: "Matching.match_list Var [(l, t |_ q), (r, t' |_ q)] = Some \<mu>" by auto
  from Matching.match_list_sound [OF match]
    have id: "l \<cdot> \<mu> = t |_ q" "r \<cdot> \<mu> = t' |_ q" by auto
  show ?thesis
    by (rule conjI, unfold rstep_r_p_s_def Let_def lr fst_conv snd_conv id, rule, unfold split, intro conjI,
      insert mem, auto intro!: ctxt_supt_id)
qed

definition narrow_enum_impl :: "('f,'v)rules \<Rightarrow> ('f,'v)rule \<Rightarrow> ('f,'v)rule \<Rightarrow> pos \<Rightarrow>
  (('f,'v) subst \<times> ('f,'v)rule \<times> pos \<times> ('f,'v)subst)list" where
  "narrow_enum_impl R st st' p \<equiv>
     let (s,t) = st;
         (s',t') = st' in
       [(\<mu>, lr, q, \<tau>).
         \<mu> \<leftarrow> option_to_list (Matching.match s' s),
         (lr, \<tau>, q) \<leftarrow> rstep_enum_impl R (t \<cdot> \<mu>) t' p]"

lemma narrow_enum_impl:
  assumes mem: "(\<mu>, lr, q, \<tau>) \<in> set (narrow_enum_impl R (s,t) (s',t') p)"
  shows "s \<cdot> \<mu> = s' \<and> (t \<cdot> \<mu>, t') \<in> rstep_r_p_s (set R) lr q \<tau> \<and> p \<le> q"
  by (rule conjI [OF _ rstep_enum_impl])
     (insert mem [unfolded narrow_enum_impl_def Let_def split], auto dest: Matching.match_sound)

definition check_narrow :: "bool \<Rightarrow> ('dpp, 'f :: {showl, compare_order}, string) dpp_ops \<Rightarrow> 'dpp \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)term list \<Rightarrow> bool \<Rightarrow> ('f,string)rule \<Rightarrow> ('f,string)rule
  \<Rightarrow> ('f,string) subst \<times> ('f,string)rule \<times> pos \<times> ('f,string)subst \<Rightarrow> showsl check"
  where "check_narrow inn I dpp R Q nfs st st' quad \<equiv> case (st,st',quad) of ((s,t),(s',t'),(\<mu>, lr, p, \<sigma>)) \<Rightarrow>
    do {
      check_nfc inn R Q (dpp_ops.is_QNF I dpp) (args s') nfs (t \<cdot> \<mu> |_ p);
      check_rewrite_common_preconditions I None (s',t \<cdot> \<mu>) (args s') (args (t \<cdot> \<mu> |_ p)) t' lr p False dpp}"

datatype ('f,'v)narrowing_complete_proc_prf =
  Narrowing_complete_proc_prf "('f,'v)rule" pos "('f,'v)rules"

fun narrowing_complete_proc ::
    "('dpp, 'f :: {showl, compare_order}, string) dpp_ops \<Rightarrow>
     ('f,string)narrowing_complete_proc_prf \<Rightarrow> 'dpp proc"
where
  "narrowing_complete_proc I (Narrowing_complete_proc_prf st p sts) dpp =
    check_return ((do {
     let (s,t) = st;
     let q = dpp_ops.Q I dpp;
     let nfs = dpp_ops.nfs I dpp;
     let rules = dpp_ops.rules I dpp;
     let check_ndef = check_no_defined_root (dpp_spec.is_defined I dpp);
     let inn = isOK(check_NF_trs_subset rules q);
     let cnarrow = check_narrow inn I dpp rules q nfs st;
     check (q = [] \<or> dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''full or innermost rewriting required''));
     (if (q = []) then succeed else do {
       check_no_var s;
       check_no_var t;
       check_ndef t;
       (if nfs then do {
          check_allm (\<lambda> (l,r). check_no_var l) rules;
          check (wf_rule (s,t)) (showsl_rule (s,t) \<circ> showsl_lit (STR '' is not well formed''))
        } else succeed)
     });
     check_allm (\<lambda> st'. let quads = narrow_enum_impl rules st st' p in
                 check_exm (\<lambda>quad. try (check (q = []) (showsl_lit (STR ''q not empty''))) catch (\<lambda>e. cnarrow st' quad))
                   quads (\<lambda>es. showsl_rule st' \<circ> showsl_lit (case quads of
                   Nil \<Rightarrow> STR '' does not seem to be narrowed pair''
                 | Cons _ _ \<Rightarrow> STR '' violates side conditions for completeness'') 
                \<circ> showsl_list_gen id (STR '''')  (STR '''')  (STR '''')  (STR '''') es)) sts
   }) <+? (\<lambda> s. showsl_lit (STR ''error when narrowing\<newline>'')
              \<circ> showsl_rule st \<circ>
             showsl_lit (STR ''\<newline> to the pairs\<newline>'') \<circ> showsl_trs sts \<circ> showsl_nl \<circ> s))
   (dpp_ops.replace_pair I dpp st sts)"

lemma narrowing_complete_proc: assumes I: "dpp_spec I"
  and ok: "narrowing_complete_proc I prf d = return d'"
  and infin: "infinite_dpp (dpp_ops.nfs I d', set (dpp_ops.pairs I d'), set (dpp_ops.Q I d'), set (dpp_ops.rules I d'))"
    (is "infinite_dpp ?dpp'")
  shows "infinite_dpp (dpp_ops.nfs I d, set (dpp_ops.pairs I d), set (dpp_ops.Q I d), set (dpp_ops.rules I d))"
    (is "infinite_dpp ?dpp")
proof -
  obtain st p sts where id: "prf = Narrowing_complete_proc_prf st p sts" by (cases "prf")
  interpret dpp_spec I by fact
  let ?R = "set (rules d)"
  let ?nfs = "NFS d"
  let ?Q = "set (Q d)"
  let ?P = "set (pairs d)"
  obtain s t where st: "st = (s,t)" by force
  note ok = ok[unfolded id narrowing_complete_proc.simps st Let_def, simplified]
  from ok have d': "d' = replace_pair d (s,t) sts" by auto
  note id = replace_pair_sound[unfolded dpp_sound, of d "(s,t)" sts]
  have id1: "?dpp' = (?nfs, replace (s,t) (set sts) ?P, ?Q, ?R)" unfolding d' using id
    by (auto simp: replace_def)
  from ok have full_or_inn: "?Q = {} \<or> NF_terms ?Q \<subseteq> NF_trs ?R" by auto
  {
    assume "?Q \<noteq> {}"
    then have "(Q d = []) = False" by simp
    from ok[unfolded this]
    have "\<And> l r. ?nfs \<Longrightarrow> (l,r) \<in> ?R \<Longrightarrow> is_Fun l" "is_Fun t \<and> \<not> defined ?R (the (root t))" "is_Fun s" "?nfs \<Longrightarrow> wf_rule (s,t)" by auto
  } note inn = this
  show "infinite_dpp ?dpp"
  proof (rule narrowing_complete_proc[OF infin[unfolded id1] full_or_inn icap inn(1-3) _ inn(4)])
    fix s' t'
    assume mem: "(s',t') \<in> set sts"
    let ?inn = "NF_trs ?R \<subseteq> NF_terms ?Q"
    let ?cn = "check_narrow ?inn I d (rules d) (Q d) ?nfs (s,t)"
    from mem ok have "\<exists> quad \<in> set (narrow_enum_impl (rules d) (s,t) (s',t') p). Q d = [] \<or> isOK(?cn (s',t') quad)"
      by (auto simp add: isOK_check_catch)
    then obtain quad where narrow: "quad \<in> set (narrow_enum_impl (rules d) (s,t) (s',t') p)"
      and cn: "Q d = [] \<or> isOK(?cn (s',t') quad)" by auto
    obtain \<mu> lr q \<sigma> where quad: "quad = (\<mu>, lr, q, \<sigma>)" by (cases quad, blast)
    from narrow_enum_impl[OF narrow[unfolded quad]]
    have one: "s' = s \<cdot> \<mu>" "(t \<cdot> \<mu>, t') \<in> rstep_r_p_s ?R lr q \<sigma>" by auto
    show "\<exists>lr q \<mu> \<sigma>.
               s' = s \<cdot> \<mu> \<and>
               (t \<cdot> \<mu>, t') \<in> rstep_r_p_s ?R lr q \<sigma> \<and>
               (?Q \<noteq> {} \<longrightarrow> (\<exists> U.
                R_Q_U_ecap.rewrite_common_preconditions ?R U ?Q icap' s' (args s') (args (t \<cdot> \<mu> |_ q)) (t \<cdot> \<mu>) t' lr q ?nfs False \<and>
                (\<forall>v\<lhd>t \<cdot> \<mu> |_ q. nfc ?R ?Q (set (args (s \<cdot> \<mu>))) v ?nfs)))"
    proof (intro exI, intro conjI, rule one(1), rule one(2), intro impI)
      assume Q: "?Q \<noteq> {}"
      with full_or_inn have i: "NF_terms ?Q \<subseteq> NF_trs ?R" by auto
      note cn = cn[unfolded check_narrow_def quad split]
      from cn Q have nfc: "isOK (check_nfc ?inn (rules d) (Q d) (\<lambda> t. t \<in> NF_terms (set (Q d))) (args s') ?nfs (t \<cdot> \<mu> |_ q))" by simp
      from cn Q have
        rewr: "isOK (check_rewrite_common_preconditions I None (s', t \<cdot> \<mu>) (args s') (args (t \<cdot> \<mu> |_ q)) t' lr q False d)" by simp
      note common =  check_rewrite_common_preconditions[OF I rewr i]
      from common(2) obtain U where
        rewr: "R_Q_U_ecap.rewrite_common_preconditions ?R U ?Q icap' s' (args s') (args (t \<cdot> \<mu> |_ q)) (t \<cdot> \<mu>) t' lr q ?nfs False"
        by auto
      interpret R_Q_U_ecap ?R U ?Q icap' by (rule common(1))
      from rewr[unfolded rewrite_common_preconditions_def] have "vars_term (t \<cdot> \<mu> |_ q) \<subseteq> vars_term s'" by auto
      moreover have "is_Fun s'" using one(1) ok Q by fastforce
      ultimately have vars: "vars_term (t \<cdot> \<mu> |_ q) \<subseteq> (\<Union>u\<in>set (args s'). vars_term u)" by fastforce
      from check_nfc[OF common(1) nfc vars] have nfc: "(\<forall>v\<lhd>t \<cdot> \<mu> |_ q. nfc ?R ?Q (set (args (s \<cdot> \<mu>))) v ?nfs)" using one(1) by auto
      show "\<exists> U. R_Q_U_ecap.rewrite_common_preconditions ?R U ?Q icap' s' (args s') (args (t \<cdot> \<mu> |_ q)) (t \<cdot> \<mu>) t' lr q ?nfs False \<and>
        (\<forall>v\<lhd>t \<cdot> \<mu> |_ q. nfc ?R ?Q (set (args (s \<cdot> \<mu>))) v ?nfs)"
        using rewr nfc by blast
    qed
  qed
qed

end
