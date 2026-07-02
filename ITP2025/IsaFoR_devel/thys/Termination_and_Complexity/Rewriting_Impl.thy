(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Rewriting_Impl
imports 
  Innermost_Usable_Rules_Impl
  Rewriting
  CR.Critical_Pairs_Impl
  "Transitive-Closure-II.RTrancl"
begin

definition check_rewrite_common_preconditions where
  "check_rewrite_common_preconditions I U_opt st ss ts t' lr p sound dpp \<equiv> do {
     let R = dpp_ops.rules I dpp;
     let s = fst st;
     let t = snd st;
     let tp = t |_ p;
     let U = (case U_opt of Some U \<Rightarrow> U | None => List.maps (\<lambda> t. inn_usable_rules_pair I dpp (s,t)) ts);
     check_subseteq U R <+? (\<lambda> lr. showsl_rule lr \<circ> showsl_lit (STR '' is not a rule of the rewrite system ''));
     let urc = is_ur_closed_impl_dpp_mv I dpp U;
     let check_urc = (\<lambda> S t. check (urc S t) (showsl_lit (STR ''term '') \<circ> showsl t \<circ> showsl_lit (STR '' is not closed under usable rules'')));
     let nfs = dpp_ops.nfs I dpp;
     check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''lhss must not be variables''))) U;
     check (wf_rule lr) (showsl_rule lr \<circ> showsl_lit (STR '' is not a well formed rule''));
     (if nfs \<and> sound then succeed else (check_subseteq (vars_term_list tp) (vars_term_list s) <+? (\<lambda> x. showsl_lit (STR ''variable condition in pair violated''))));
     check_allm (\<lambda> t. check_urc ss t) ts;
     check_allm (\<lambda>(l,r). check_urc (args l) r) U;
     check_critical_pairs_innermost string_rename U <+? (\<lambda> s. showsl_lit (STR ''problem in showing UNF of usable rules\<newline>'') \<circ> s);
     check_allm (\<lambda>(b,s,t). check (s = t) (showsl_lit (STR ''non-trivial critical pair between rule to rewrite and usable rules''))) (critical_pairs_impl string_rename [lr] U)
   }"

lemma check_rewrite_common_preconditions: assumes I: "dpp_spec I"
  and ok: "isOK(check_rewrite_common_preconditions I U_opt (s,t) ss ts t' lr p sound dpp)"
  and inn: "NF_terms (set (dpp_ops.Q I dpp)) \<subseteq> NF_trs (set (dpp_ops.rules I dpp))"
  shows "R_Q_U_ecap (set (dpp_ops.rules I dpp)) (set (dpp_ops.Q I dpp)) icap'"
    "(\<exists> U. R_Q_U_ecap.rewrite_common_preconditions (set (dpp_ops.rules I dpp)) U (set (dpp_ops.Q I dpp)) icap' 
    s ss ts t t' lr p (dpp_ops.nfs I dpp) sound)"
proof -
  interpret dpp_spec I by fact
  let ?R = "set (dpp_ops.rules I dpp)"
  let ?Q = "set (dpp_ops.Q I dpp)"
  let ?U' = "case U_opt of None \<Rightarrow> List.maps (\<lambda> t. inn_usable_rules_pair I dpp (s,t)) ts | Some U \<Rightarrow> U"
  define U where "U = ?U'" 
  let ?U = "set U"
  let ?nfs = "dpp_ops.nfs I dpp"
  note ok = ok[unfolded check_rewrite_common_preconditions_def Let_def is_ur_closed_impl_dpp_mv[OF I] fst_conv snd_conv,
    folded U_def, simplified] 
  show "R_Q_U_ecap ?R ?Q icap'" 
    by (unfold_locales, rule icap, rule inn)
  interpret R_Q_U_ecap ?R ?U ?Q icap' by fact
  from ok have subset: "?U \<subseteq> ?R" by auto
  show "\<exists> U. R_Q_U_ecap.rewrite_common_preconditions ?R U ?Q icap' s ss ts t t' lr p ?nfs sound"
  proof (rule exI[of _ ?U], unfold rewrite_common_preconditions_def, intro conjI allI impI)
    from ok have ok': "isOK(check_critical_pairs_innermost string_rename U)" by simp
    from NF_Q_R NF_anti_mono[OF rstep_mono[OF subset]] have NFQU: "NFQ \<subseteq> NF_trs (set U)" by auto
    {
      fix l r
      assume "(l,r) \<in> ?U"
      with ok have "is_Fun l" by force
    }
    from check_critical_pairs_innermost[OF ok' NFQU this]
    have "CR (qrstep ?nfs ?Q ?U)" .
    from CR_imp_UNF[OF this] show "UNF (qrstep ?nfs ?Q ?U)" .
  qed (insert ok, auto)
qed
      

(* TODO: one might automatically put st' into strict pairs,
   if st is not strict and there are strict rules *)
definition
  rewriting_proc ::
    "('dpp, 'f :: {showl, compare_order}, string) dpp_ops \<Rightarrow> 
     ('f,string)rules option \<Rightarrow> ('f,string)rule \<Rightarrow> ('f,string)rule \<Rightarrow> ('f,string)rule \<Rightarrow> ('f,string)rule \<Rightarrow> pos \<Rightarrow> 'dpp proc"
where
  "rewriting_proc I U st st' st'' lr p dpp \<equiv> 
    check_return (do {
     let s = fst st;
     let t' = snd st';
     check_rstep' (dpp_ops.rules I dpp) p lr (snd st) t';
     check (dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''innermost rewriting required''));
     check_rewrite_common_preconditions I U st [s] [(snd st) |_ p] t' lr p True dpp;
     check (st' =\<^sub>v st'') (showsl_lit (STR ''the rule '') \<circ> showsl_rule st' \<circ> showsl_lit (STR '' is not a renamed variant of '') \<circ> showsl_rule st'');
     check (s = fst st') (showsl_lit (STR ''left-hand sides of old and new pair differ''));
     check (st \<in> set (dpp_ops.P I dpp) \<or> dpp_ops.R I dpp = []) (showsl_lit (STR ''strict DP or no strict rules required''));
     check (dpp_ops.nfs I dpp \<or> dpp_ops.wwf_rules I dpp) (showsl_lit (STR ''well-formed rules or normal subst. required''))
   })
   (dpp_ops.replace_pair I dpp st [st''])"    

lemma variable_renamed_variant: assumes eqv: "st1 =\<^sub>v st2" and st: "st \<in> replace st0 ({st1}) P"
  shows "\<exists> st'. st' \<in> replace st0 ({st2}) P \<and> st =\<^sub>v st'"
proof -
  note rep_def = Util.replace_def
  have str: "st =\<^sub>v st" by simp
  show ?thesis
  proof (cases "st0 \<in> P")
    case False
    with st str show ?thesis unfolding rep_def 
      by (intro exI[of _ st], auto)
  next
    case True 
    with st[unfolded rep_def]
    have "st \<in> P - {st0} \<union> {st1}" by simp
    then show ?thesis
    proof
      assume "st \<in> P - {st0}" 
      with True str show ?thesis unfolding rep_def
        by (intro exI[of _ st], auto)
    next
      assume "st \<in> {st1}"
      with True eqv show ?thesis unfolding rep_def
        by (intro exI[of _ "st2"], auto)
    qed
  qed
qed
 
lemma rewriting_proc: assumes I: "dpp_spec I"
 shows "dpp_spec.sound_proc_impl I (rewriting_proc I (U_opt :: ('f :: {showl, compare_order},string)rules option)
  st st' st'' lr p)"
proof -
  from assms interpret dpp_spec I .
  show ?thesis
  proof
    fix d d''    
    assume ok: "rewriting_proc I U_opt st st' st'' lr p d = Inr d''" and fin: "finite_dpp (dpp d'')"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?Q = "set (Q d)"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?Rb = "?R \<union> ?Rw"
    let ?Rb' = "set (rules d)"
    let ?nfs = "NFS d"
    let ?m = "M d"
    obtain s t where st: "st = (s,t)" by force
    obtain l r where lr: "lr = (l,r)" by force
    obtain s' t' where st': "st' = (s',t')" by force
    obtain s'' t'' where st'': "st'' = (s'',t'')" by force
    note ok = ok[unfolded rewriting_proc_def st lr st' st'' Let_def dpp_spec_sound, simplified]
    from ok have inn: "NF_terms ?Q \<subseteq> NF_trs ?Rb'" by auto
    from ok obtain \<sigma> where rewrite: "(t, t') \<in> rstep_r_p_s ?Rb' (l, r) p \<sigma>" by auto
    from ok have common: "isOK (check_rewrite_common_preconditions I U_opt (s, t) [s] [t |_ p] t' (l, r) p True d)" by auto
    note common = check_rewrite_common_preconditions[OF I this inn]
    obtain d' where d': "d' = replace_pair d (s,t) [(s,t')]" by auto
    from ok have d'': "d'' = replace_pair d (s,t) [(s'',t'')]" by auto
    from ok have eqv: "(s,t') =\<^sub>v (s'',t'')" by simp
    note variant = variable_renamed_variant[OF this, of _ "(s,t)"]
    from fin have fin: "finite_dpp (dpp d')" unfolding d' d'' replace_pair_sound
      by (rule finite_dpp_rename_vars, insert variant[of _ ?P] variant[of _ ?Pw], auto)
    have d': "dpp d' = (?nfs,?m,replace (s,t) {(s,t')} ?P, replace (s,t) {(s,t')} ?Pw, ?Q, ?R, ?Rw)" 
      unfolding d' unfolding replace_pair_sound by simp
    note fin = fin[unfolded this]
    from common(2) obtain U where
      comm: "R_Q_U_ecap.rewrite_common_preconditions ?Rb' U (set (Q d)) icap' s [s] [t |_ p] t t' (l, r) p (NFS d) True"
      by blast
    interpret R_Q_U_ecap ?Rb' U ?Q icap' by (rule common(1))
    show "finite_dpp (dpp d)" unfolding dpp_spec_sound
      by (rule rewriting_proc[OF fin comm rewrite], insert ok, auto)
  qed
qed

(* implementation of the estimated q normal form condition *)
fun enfc_cand
where
  "enfc_cand isQnf R Q (_, Var _) = []"
| "enfc_cand isQnf R Q (S, Fun f ts) =
     map (Pair S) ts @ [(args l, r). (l,r) <- R,
      (case mgu_class (Fun f (map (icap_impl' isQnf R S) ts)) l of
         None \<Rightarrow> False
       | Some \<mu> \<Rightarrow> ((\<forall>u \<in> set (args l). isQnf (mv_yvar u \<cdot> \<mu>)) \<and> (\<forall>u \<in> set S. isQnf (mv_xvar u \<cdot> \<mu>))))]"

fun enfc_q
where
  "enfc_q isQnf isRnf R Q S (Var x) = True"
| "enfc_q isQnf isRnf R Q S (Fun f ts) =
     (\<forall>q \<in> set Q. case mgu_class (Fun f (map (icap_impl' isQnf R S) ts)) q of
        None \<Rightarrow> True
      | Some \<mu> \<Rightarrow> \<not> ((\<forall>u \<in> set S. isQnf (mv_xvar u \<cdot> \<mu>)) \<and> (isRnf (mv_yvar q \<cdot> \<mu>))))"

definition enfc_impl
where
  "enfc_impl isQnf isRnf R Q S t =
    (\<forall> (S',u) \<in> set (mk_rtrancl_list (=) (enfc_cand isQnf R Q) [(S,t)]). enfc_q isQnf isRnf R Q S' u)"

lemma enfc_impl_sound :
  fixes Q :: "('f :: compare_order, string) term list" and S R
  defines isQnf : "isQnf \<equiv> (\<lambda> t. t \<in> NF_terms (set Q))"
  defines isRnf : "isRnf \<equiv> (\<lambda> t. t \<in> NF_trs (set R))"
  assumes "R_Q_U_ecap (set R) (set Q) icap'"
  and SS:"set S = SS"
  and "vars_term t \<subseteq> (\<Union>s\<in>SS. vars_term s)"
  and "wf_trs (set R)"
  shows
  "enfc_impl isQnf isRnf R Q S t \<Longrightarrow> nfc (set R) (set Q) SS t nfs"
proof -
  assume *: "enfc_impl isQnf isRnf R Q S t"
  let ?cand = "enfc_cand isQnf R Q"
  interpret R_Q_U_ecap "(set R)" U "(set Q)" icap' by (rule assms)
  {
    fix s S
    have "{b. ((S, s), b) \<in> {(a, b). b \<in> set (enfc_cand isQnf R Q a)}^*} \<subseteq>
      ({(S', ti). S' = S \<and> s \<unrhd> ti} \<union> {(args l, u) | l r u. (l,r) \<in> set R \<and> r \<unrhd> u})"  (is "?A \<subseteq> ?B")
    proof
      fix S' u
      assume "(S', u) \<in> ?A"
      then have "((S, s), S', u) \<in> {(a, b). b \<in> set (enfc_cand isQnf R Q a)}^*" by simp
      then show "(S', u) \<in> ?B"
      proof (induct)
        case base
        show ?case by auto
      next
        case (step Tt Uu)
        obtain T t where Tt: "Tt = (T, t)" by force
        obtain U u where Uu: "Uu = (U, u)" by force
        from step(2)[unfolded Tt Uu]
        have mem: "(U, u) \<in> set (enfc_cand isQnf R Q (T, t))" by auto
        from mem obtain f ts where t: "t = Fun f ts" by (cases t, auto)
        from mem[unfolded t]
        have "(T = U \<and> u \<in> set ts) \<or> (\<exists> l r. (l, r) \<in> set R \<and> U = (args l) \<and> u = r)" (is "?ts \<or> ?lr")  by auto
        then show ?case
        proof
          assume ?lr
          then obtain l r where "(l, r) \<in> set R \<and> U = args l \<and> u = r" by auto
          then show ?thesis unfolding Uu by auto
        next
          assume ts: ?ts
          from step(3)[unfolded Tt]
          have "(S = T \<and> s \<unrhd> t) \<or> (\<exists> l r. (l, r) \<in> set R \<and> T = (args l) \<and> r \<unrhd> t)" (is "(?subt \<or> ?rule)") by auto
          then show ?thesis
          proof
            assume subt: ?subt
            with ts have "s \<unrhd> u" unfolding t using arg_subteq subterm.dual_order.trans by blast
            with ts subt show ?thesis unfolding Uu by auto
          next
            assume ?rule
            then obtain l r where lr:"(l, r) \<in> set R \<and> T = args l \<and> r \<unrhd> t" by auto
            with ts have "r \<unrhd> u" unfolding t using arg_subteq subterm.dual_order.trans by blast
            with lr ts show ?thesis unfolding Uu t by auto
          qed
        qed
      qed
    qed
    also have "... = set (map (Pair S) (supteq_list s) @ [(args l, u) . (l,r) <- R, u <- supteq_list r])" (is "_ = ?B") by auto
    finally have "?A \<subseteq> ?B" .
    from finite_subset[OF this finite_set] have "finite ?A" .
  } note finite = this
  interpret relation_subsumption_list ?cand "(=)" by (unfold_locales, insert finite, auto)
  let ?nf = "is_NF_terms Q"
  show "nfc (set R) (set Q) SS t nfs"
  proof (rule enfcf_sound)
    show "\<not> R_Q_U_ecap.enfcf (set R) (set Q) icap' SS t"
    proof
      assume enfcf: "R_Q_U_ecap.enfcf (set R) (set Q) icap' SS t"
      from enfcf SS have "enfc_impl isQnf isRnf R Q S t = False"
      proof (induct arbitrary: S)
        case (arg i ts S' f)
        have "(S, ts ! i) \<in> set (enfc_cand isQnf R Q (S, Fun f ts))" using arg(1) by auto
        then have rec: "(S, ts ! i) \<in> {(a, b). b \<in> set (enfc_cand isQnf R Q a)}^* `` set [(S, Fun f ts)]" by fastforce
        from arg have "enfc_impl isQnf isRnf R Q S (ts ! i) = False" by auto
        then obtain T t where
          "(T, t) \<in> set (mk_rtrancl_list (=) (enfc_cand isQnf R Q) [(S, ts ! i)])"
          and Tt:"enfc_q isQnf isRnf R Q T t = False"
          unfolding enfc_impl_def by auto
        then have "(T, t) \<in> {(a, b). b \<in> set (enfc_cand isQnf R Q a)}^*`` set [(S, ts ! i)]"
          using mk_rtrancl_list[unfolded mk_rtrancl_no_subsumption[OF refl], of "[(S, ts ! i)]"]  by simp
        with rec have "(T, t) \<in> {(a, b). b \<in> set (enfc_cand isQnf R Q a)}^*`` set [(S, Fun f ts)]" by simp
        then have  "(T, t) \<in> set (mk_rtrancl_list (=) (enfc_cand isQnf R Q) [(S, Fun f ts)])"
          using mk_rtrancl_list[unfolded mk_rtrancl_no_subsumption[OF refl], of "[(S,Fun f ts)]"] by auto
        with Tt show ?case unfolding enfc_impl_def by auto
      next
        case (rule l r f S' ts)
        then have IH: "enfc_impl isQnf isRnf R Q (args l) r = False" by auto
        from rule obtain \<mu> where \<mu>: "mgu_class (Fun f (map (icap' (set R) (set Q) (mv_xvar ` S') \<circ> mv_xvar) ts)) l = Some \<mu> \<and>
          mv_xvar ` S' \<union> mv_yvar ` set (args l) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu> \<subseteq> NF_terms (set Q)" by auto
        from icap_impl'_sound rule(2) icap' icap_mv_def isQnf have
          icap:"\<And> t. icap' (set R) (set Q) (mv_xvar ` S') (mv_xvar t)= icap_impl' isQnf R S t" by metis
        then have "map (icap' (set R) (set Q) (mv_xvar ` S') \<circ> mv_xvar) ts = map (icap_impl' isQnf R S) ts" by auto
        with \<mu> have "mgu_class (Fun f (map (icap_impl' isQnf R S) ts)) l = Some \<mu>" by auto
        moreover have "\<forall>u \<in> set (args l). isQnf (mv_yvar u \<cdot> \<mu>)"
        proof
          fix u
          assume "u \<in> set (args l)"
          with \<mu> have "mv_yvar u \<cdot> \<mu> \<in> NF_terms (set Q)" by auto
          then show "isQnf (mv_yvar u \<cdot> \<mu>)" unfolding isQnf by auto
        qed
        moreover have "\<forall>u \<in> set S. isQnf (mv_xvar u \<cdot> \<mu>)"
        proof
          fix u
          assume "u \<in> set S"
          with rule(2) have "u \<in> S'" by auto
          with \<mu> have "mv_xvar u \<cdot> \<mu> \<in> NF_terms (set Q)" by auto
          then show "isQnf (mv_xvar u \<cdot> \<mu>)" unfolding isQnf by auto
        qed
        ultimately have "(case mgu_class (Fun f (map (icap_impl' isQnf R S) ts)) l of None \<Rightarrow> False
          | Some \<mu> \<Rightarrow> ((\<forall>u \<in> set (args l). isQnf (mv_yvar u \<cdot> \<mu>)) \<and> (\<forall>u \<in> set S. isQnf (mv_xvar u \<cdot> \<mu>))))" by auto
        with rule have "(args l, r) \<in> set (enfc_cand isQnf R Q (S, Fun f ts))" by force
        then have rec: "(args l, r) \<in> {(a, b). b \<in> set (enfc_cand isQnf R Q a)}^* `` set [(S, Fun f ts)]" by fastforce
        from IH obtain T t where
          "(T, t) \<in> set (mk_rtrancl_list (=) (enfc_cand isQnf R Q) [(args l, r)])" and Tt:"enfc_q isQnf isRnf R Q T t = False"
          unfolding enfc_impl_def  by auto
        then have "(T, t) \<in> {(a, b). b \<in> set (enfc_cand isQnf R Q a)}^*`` set [(args l, r)]"
          using mk_rtrancl_list[unfolded mk_rtrancl_no_subsumption[OF refl], of "[(args l, r)]"]  by auto
        with rec have "(T, t) \<in> {(a, b). b \<in> set (enfc_cand isQnf R Q a)}^* `` set [(S, Fun f ts)]" by auto
         then have  "(T, t) \<in> set (mk_rtrancl_list (=) (enfc_cand isQnf R Q) [(S, Fun f ts)])"
          using mk_rtrancl_list[unfolded mk_rtrancl_no_subsumption[OF refl], of "[(S,Fun f ts)]"] by auto
        with Tt show ?case unfolding enfc_impl_def by auto
      next
        case (q q f S' ts)
        then obtain \<mu> where \<mu>:"mgu_class (Fun f (map (icap' (set R) (set Q) (mv_xvar ` S') \<circ> mv_xvar) ts)) q = Some \<mu> \<and>
          mv_xvar ` S' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu> \<subseteq> NF_terms (set Q) \<and> mv_yvar q \<cdot> \<mu> \<in> NF_trs (set R)" by auto
        from icap_impl'_sound q(2) icap' icap_mv_def isQnf have
          icap:"\<And> t. icap' (set R) (set Q) (mv_xvar ` S') (mv_xvar t)= icap_impl' isQnf R S t" by metis
        then have icapts:"map (icap' (set R) (set Q) (mv_xvar ` S') \<circ> mv_xvar) ts = map (icap_impl' isQnf R S) ts" by auto
        {
          fix u
          assume "u \<in> set S"
          with q(2) have "u \<in> S'" by auto
          with \<mu> have "mv_xvar u \<cdot> \<mu> \<in> NF_terms (set Q)" by auto
          then have "isQnf (mv_xvar u \<cdot> \<mu>)" unfolding isQnf by auto
        }
        then have Sqnf:"\<forall>u \<in> set S. isQnf (mv_xvar u \<cdot> \<mu>)" by fast
        moreover from \<mu> have "isRnf (mv_yvar q \<cdot> \<mu>)" unfolding isRnf by auto
        ultimately have "(case mgu_class (Fun f (map (icap_impl' isQnf R S) ts)) q of None \<Rightarrow> True
          | Some \<mu> \<Rightarrow> \<not> ((\<forall>u \<in> set S. isQnf (mv_xvar u \<cdot> \<mu>)) \<and> (isRnf (mv_yvar q \<cdot> \<mu>)))) = False" using \<mu> icapts by auto
        then have "enfc_q isQnf isRnf R Q S (Fun f ts) = False" using q by auto
        moreover have "(S, Fun f ts) \<in> set (mk_rtrancl_list (=) (enfc_cand isQnf R Q) [(S, Fun f ts)])"
          using mk_rtrancl_list[unfolded mk_rtrancl_no_subsumption[OF refl], of "[(S,Fun f ts)]"]  by auto
        ultimately show ?case unfolding enfc_impl_def by blast
      qed
      then show False using * by auto
    qed
  qed (auto simp add: assms)
qed

definition check_nfc :: "bool \<Rightarrow> ('f :: {showl, compare_order}, string) rules \<Rightarrow> 
  ('f, string)term list \<Rightarrow> (('f, string)term \<Rightarrow> bool) \<Rightarrow> ('f,string)term list \<Rightarrow> bool \<Rightarrow> ('f,string)term \<Rightarrow> showsl check" where 
  "check_nfc inn R Q isQnf ss nfs t \<equiv>
     do {
      check_wf_trs R;
      (if inn then succeed else
        check_allm (\<lambda>t. check (enfc_impl isQnf 
        (is_NF_trs R) R Q ss t)
        (showsl_lit (STR '' nfc not satisfied for '') \<circ> showsl t)) (supteq_list t))}"
  
lemma check_nfc:
  assumes cap: "R_Q_U_ecap (set R) (set Q) icap'"
  and ok: "isOK(check_nfc (NF_trs (set R) \<subseteq> NF_terms (set Q)) R Q (\<lambda>t. t \<in> NF_terms (set Q)) ss nfs t)"
  and var_cond: "vars_term t \<subseteq> (\<Union>s\<in>set ss. vars_term s)"
  and sub: "t \<rhd> u"
  shows "nfc (set R) (set Q) (set ss) u nfs"
proof -
  interpret R_Q_U_ecap "(set R)" U "(set Q)" icap' by (rule assms)
  note ok = ok[unfolded check_nfc_def]
  from ok have wf: "wf_trs (set R)" by auto
  show ?thesis
  proof (cases "NF_trs (set R) \<subseteq> NF_terms (set Q)")
    case True
    {
      fix l r
      assume "(l, r) \<in> set R"
      with wf have "is_Fun l" unfolding wf_trs_def by blast
    }
    then have *:"\<And> l r. nfs \<Longrightarrow> (l,r) \<in> set R \<Longrightarrow> is_Fun l" by simp
    show ?thesis by (rule innermost_imp_nfc[OF _ *], insert True NF_Q_R, auto)
  next
    case False
    with ok have "\<forall> u \<lhd> t. (enfc_impl (\<lambda> t. t \<in> NF_terms (set Q)) (\<lambda> t. t \<in> NF_trs (set R)) R Q ss u)" by auto
    with sub have impl: "(enfc_impl  (\<lambda> t. t \<in> NF_terms (set Q)) (\<lambda> t. t \<in> NF_trs (set R)) R Q ss u)" by auto
    from sub have "t \<unrhd> u" by auto
    with supteq_imp_vars_term_subset have "vars_term u \<subseteq> vars_term t" by blast
    with var_cond have " vars_term u \<subseteq> (\<Union>s\<in>set ss. vars_term s)" by auto
    with enfc_impl_sound[OF cap _ _ wf impl, of "set ss"] show "nfc (set R) (set Q) (set ss) u nfs" by blast
  qed
qed

datatype ('f,'v)rewriting_complete_proc_prf = Rewriting_complete_proc_prf "('f,'v)rules option" "('f,'v)rule" "('f,'v)rule" "('f,'v)rule" "('f,'v)rule" pos

fun rewriting_complete_proc ::
  "('dpp, 'f :: {showl, compare_order}, string) dpp_ops \<Rightarrow> ('f,string)rewriting_complete_proc_prf \<Rightarrow> 'dpp proc" where
  "rewriting_complete_proc I (Rewriting_complete_proc_prf U_opt st st' st'' lr p) dpp = 
    check_return ((do {
     let s = fst st;
     let t = snd st;
     let t' = snd st';
     let R = dpp_ops.rules I dpp;
     check_rstep' R p lr t t';
     check (dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''innermost rewriting required''));     
     check_rewrite_common_preconditions I U_opt st (args s) (args (t |_ p)) t' lr p False dpp;
     check (is_Fun s) (showsl_lit (STR ''lhs of pair must not be variable''));
     check (st' =\<^sub>v st'') (showsl_lit (STR ''the rule '') \<circ> showsl_rule st' \<circ> showsl_lit (STR '' is not a renamed variant of '') \<circ> showsl_rule st'');
     check (s = fst st') (showsl_lit (STR ''left-hand sides of old and new pair differ''));
     let Q = dpp_ops.Q I dpp;
     let inn = isOK(check_NF_trs_subset R Q);
     check_nfc inn R Q (dpp_ops.is_QNF I dpp) (args s) (dpp_ops.nfs I dpp) (t |_ p);
     check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''lhss must not be variables''))) R;
     (if is_Fun t then check (\<not> dpp_spec.is_defined I dpp (the (root t))) (showsl_lit (STR ''root of '') \<circ> showsl t \<circ> showsl_lit (STR '' must not be defined''))
       else succeed)
   }) <+? (\<lambda> s. showsl_lit (STR ''error when rewriting the pair\<newline>'')
              \<circ> showsl_rule st \<circ>
             showsl_lit (STR ''\<newline> to the pair\<newline>'') \<circ> showsl_rule st'' \<circ> showsl_nl \<circ> s))
   (dpp_ops.replace_pair I dpp st [st''])"  
 
lemma rewriting_complete_proc: assumes I: "dpp_spec I"
  and ok: "rewriting_complete_proc I prf d = return d''"
  and infin: "infinite_dpp (dpp_ops.nfs I d'', set (dpp_ops.pairs I d''), set (dpp_ops.Q I d''), set (dpp_ops.rules I d''))" 
    (is "infinite_dpp ?dpp''")
  shows "infinite_dpp (dpp_ops.nfs I d, set (dpp_ops.pairs I d), set (dpp_ops.Q I d), set (dpp_ops.rules I d))"
    (is "infinite_dpp ?dpp")
proof -
  obtain U_opt st st' st'' lr p where id: "prf = Rewriting_complete_proc_prf U_opt st st' st'' lr p" 
    by (cases "prf") 
  interpret dpp_spec I by fact
  let ?R = "set (rules d)"
  let ?nfs = "NFS d"
  let ?Q = "set (Q d)"
  let ?P = "set (pairs d)"
  obtain s t where st: "st = (s,t)" by force
  obtain l r where lr: "lr = (l,r)" by force
  obtain s' t' where st': "st' = (s',t')" by force
  obtain s'' t'' where st'': "st'' = (s'',t'')" by force
  note ok = ok[unfolded id rewriting_complete_proc.simps st lr st' st'' Let_def, simplified]
  obtain d' where d': "d' = replace_pair d (s,t) [(s,t')]" by auto  
  let ?dpp' = "(dpp_ops.nfs I d', set (dpp_ops.pairs I d'), set (dpp_ops.Q I d'), set (dpp_ops.rules I d'))"
  from ok have d'': "d'' = replace_pair d (s,t) [(s'',t'')]" by auto
  from ok have inn: "NF_terms ?Q \<subseteq> NF_trs ?R" by auto
  from ok obtain \<sigma> where rewrite: "(t, t') \<in> rstep_r_p_s ?R (l, r) p \<sigma>" by auto
  from ok have "isOK (check_rewrite_common_preconditions I U_opt (s, t) (args s) (args (t |_ p)) t' (l, r) p False d)" by auto
  note common = check_rewrite_common_preconditions[OF I this inn]
  note id = replace_pair_sound[unfolded dpp_sound]
  note id1 = id[of d "(s,t)" "[(s,t')]"]
  have id1: "?dpp' = (?nfs, replace (s,t) {(s,t')} ?P, ?Q, ?R)" unfolding d' using id1 
    by (auto simp: replace_def)
  from ok have "(s,t') =\<^sub>v (s'',t'')" by simp
  then have eqv: "(s'',t'') =\<^sub>v (s,t')" unfolding eq_rule_mod_vars_def by simp
  note variant = variable_renamed_variant[OF this]
  note id2 = id[of d "(s,t)" "[(s'',t'')]"]
  have id2: "?dpp'' = (?nfs, replace (s,t) {(s'',t'')} ?P, ?Q, ?R)" unfolding d'' using id2
    by (auto simp: replace_def)
  from infin have infin: "infinite_dpp ?dpp'" unfolding id1 id2
    by (rule infinite_dpp_rename_vars, insert variant, auto)
  from common(2) obtain U where
    comm: "R_Q_U_ecap.rewrite_common_preconditions ?R U (set (Q d)) icap' s (args s) (args (t |_ p)) t t' (l, r) p (NFS d) False"
    by blast
  interpret R_Q_U_ecap ?R U ?Q icap' by (rule common(1))
  from comm[unfolded rewrite_common_preconditions_def] have "vars_term (t |_ p) \<subseteq> vars_term s" by auto
  with ok have vars: "vars_term (t |_ p) \<subseteq> (\<Union>u\<in>set (args s). vars_term u)" by fastforce
  have nfc: "\<And> u. t |_ p \<rhd> u \<Longrightarrow> nfc ?R ?Q (set (args s)) u ?nfs"
    by (rule check_nfc[OF common(1) _ vars], insert ok, auto)
  show "infinite_dpp ?dpp"
    by (rule rewriting_proc_complete[OF infin[unfolded id1] comm rewrite _ nfc], insert ok, auto)
qed

end
