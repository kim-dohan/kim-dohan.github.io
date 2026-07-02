(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Generic_Usable_Rules_Impl
  imports
    Generic_Usable_Rules
    Innermost_Usable_Rules_Impl
    Usable_Rules_Impl
begin

(* if usable rules are not given, then just return R,
   otherwise, try whether innermost usable rules are allowed,
   finally try termination usable rules *)
definition smart_usable_rules_checker :: "('f,string)usable_rules_checker"
  where "smart_usable_rules_checker nfs m c wwf \<pi> Q R U_opt sts \<equiv> case U_opt of None \<Rightarrow> Some R
           | Some U \<Rightarrow> if NF_terms Q \<subseteq> NF_trs (set R) \<and> (nfs \<or> (\<forall> (s,t) \<in> sts. vars_term t \<subseteq> vars_term s)) \<and> (nfs \<or> m \<or> wwf) then 
                        (let urc = is_ur_closed_term_mv' (set R) (set U) Q icap' \<pi> 
                         in if (\<forall> (s,t) \<in> sts. urc {s} t) \<and> (\<forall> (l,r) \<in> set U. urc (set (args l)) r) then Some U else None) else 
                        (let us = UNIV in if m \<and> c \<and> (nfs \<longrightarrow> Q \<noteq> {} \<longrightarrow> wwf) \<and> ur_closed_af (set R) (set U) us \<pi> \<and> ur_P_closed_af (set R) (set U) us \<pi> sts then Some U else None)"

lemma smart_usable_rules_checker: "usable_rules_checker (smart_usable_rules_checker :: ('f,string)usable_rules_checker)"
  unfolding usable_rules_checker_def
proof (intro allI impI)
  fix Q R \<pi> U_opt sts U and S NS :: "('f,string)trs" and nfs m c
  assume check: "smart_usable_rules_checker nfs m c (wwf_qtrs Q (set R)) \<pi> Q R U_opt sts = Some U"
    and pair: "af_redpair S NS \<pi>"
    and orient: "set U \<subseteq> NS"
    and ce: "c \<longrightarrow> ce_compatible NS" 
  note check = check[unfolded smart_usable_rules_checker_def]
  interpret af_redpair S NS \<pi> by fact
  let ?Q = "NF_terms Q"
  let ?R = "qrstep nfs Q (set R)"
  let ?wwf = "wwf_qtrs Q (set R)"
  show "\<exists> f. \<forall> s t u \<sigma> \<tau>. (s,t) \<in> sts \<longrightarrow> s \<cdot> \<sigma> \<in> ?Q \<longrightarrow> NF_subst nfs (s,t) \<sigma> Q \<longrightarrow> (t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> ?R^* 
       \<longrightarrow> (m \<longrightarrow> SN_on ?R {t \<cdot> \<sigma>}) \<longrightarrow> (t \<cdot> f \<sigma>, u \<cdot> f \<tau>) \<in> NS^*"
  proof (cases U_opt)
    case None
    with check have U: "U = R" by simp
    show ?thesis
    proof (rule exI[of _ "\<lambda> x. x"], intro allI impI)
      fix t u and \<sigma> \<tau> :: "('f,string)subst"
      assume steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> ?R^*" 
      show "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> NS^*"
      proof (rule set_mp[OF rtrancl_mono[OF subset_trans] steps])
        show "?R \<subseteq> rstep (set R)" by auto
      next
        show "rstep (set R) \<subseteq> NS"
          by (rule rstep_subset[OF ctxt_NS subst_NS orient[unfolded U]])
      qed
    qed
  next
    case (Some U')
    note check = check[unfolded Some option.simps Let_def]
    let ?inntest = "?Q \<subseteq> NF_trs (set R) \<and> (nfs \<or> (\<forall> (s,t) \<in> sts. vars_term t \<subseteq> vars_term s)) \<and> (nfs \<or> m \<or> ?wwf)"
    show ?thesis 
    proof (cases ?inntest)
      case True
      then have "?inntest = True" by simp
      note check = check[unfolded this if_True]
      let ?urc = "is_ur_closed_term_mv' (set R) (set U') Q icap' \<pi>"
      let ?urctest = "(\<forall> (s,t) \<in> sts. ?urc {s} t) \<and> (\<forall> (l,r) \<in> set U'. ?urc (set (args l)) r)"
      have ?urctest 
      proof (cases ?urctest)
        case False
        then have "?urctest = False" by simp
        from check[unfolded this] show ?thesis by simp
      qed
      with check have U: "U = U'" by simp
      show ?thesis
      proof (rule exI[of _ "\<lambda> x. x"], intro allI impI)
        fix s t u and \<sigma> \<tau> :: "('f,string)subst"
        assume st: "(s,t) \<in> sts" and NF: "s \<cdot> \<sigma> \<in> ?Q"
        and nfsigma: "NF_subst nfs (s,t) \<sigma> Q"
        and steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> ?R^*"
        and SN: "m \<longrightarrow> SN_on ?R {t \<cdot> \<sigma>}"
        from \<open>?inntest\<close> st have vars: "\<not> nfs \<Longrightarrow> vars_term t \<subseteq> vars_term s" by auto
        interpret R_Q_U_ecap "set R" "set U'" Q icap'
          by (unfold_locales, rule icap, insert \<open>?inntest\<close> U, auto)
        show "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> NS^*"
        proof (rule is_ur_closed_term_af[OF steps _ _ _ _])
          assume "\<not> nfs"
          with SN True show "wwf_qtrs Q (set R) \<or> SN_on ?R {t \<cdot> \<sigma>}" by auto
        next
          show "af_redpair S NS \<pi>" ..
        next
          show "{s} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> ?Q" using NF by auto
        next
          {
            fix x
            assume x: "x \<in> vars_term t"
            have "\<sigma> x \<in> ?Q"
            proof (cases nfs)
              case False
              with vars x have "x \<in> vars_term s" by auto
              then have "Var x \<unlhd> s" by auto
              then have "Var x \<cdot> \<sigma> \<unlhd> s \<cdot> \<sigma>" by (rule supteq_subst)
              from NF_subterm[OF NF this]
              show ?thesis by simp
            next
              case True
              with x nfsigma show ?thesis unfolding NF_subst_def vars_rule_def by auto
            qed
          }           
          then show "\<sigma> ` vars_term t \<subseteq> NF_terms Q" by auto            
        next
          show "set U' \<subseteq> NS" using orient U by auto
        qed (insert \<open>?urctest\<close> U st, auto)
      qed
    next
      case False
      then have "?inntest = False" by simp
      note check = check[unfolded this if_False]
      let ?u1 = "ur_closed_af (set R) (set U') UNIV \<pi>"
      let ?u2 = "ur_P_closed_af (set R) (set U') UNIV \<pi> sts"
      let ?urctest = "m \<and> c \<and> (nfs \<longrightarrow> Q \<noteq> {} \<longrightarrow> ?wwf) \<and> ?u1 \<and> ?u2"
      from check have ?urctest by (cases ?urctest, auto)
      with check have U: "U = U'" and u1: ?u1 and u2: ?u2 and c by auto
      with ce have ce: "ce_compatible NS" by auto
      interpret ce_af_redpair S NS \<pi> 
        by (unfold_locales, rule ce)
      from ce_compatibleE[OF NS_ce_compat] obtain k where 
        ce: "\<And> m. m \<ge> k \<Longrightarrow> ce_trs (local.c,m) \<subseteq> NS" by metis
      then have ce: "ce_trs (local.c,k + n) \<subseteq> NS" by auto
      interpret itrans Q "set R" "set R" "{}" "set U'" UNIV "(local.c,k+n)" by (rule itrans, insert itrans_ac_empty, auto)
      let ?I = "i_trans_subst"
      from orient U have orient: "set U' \<subseteq> mode_left False" unfolding mode_left_def by auto
      show ?thesis
      proof (rule exI[of _ ?I], intro allI impI)
        fix s t u :: "('f,string)term" and \<sigma> \<tau>
        assume st: "(s,t) \<in> sts" and NF: "s \<cdot> \<sigma> \<in> ?Q"
        and steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> ?R^*"
        and SNt: "m \<longrightarrow> SN_on ?R {t \<cdot> \<sigma>}"
        from wwf_qtrs_imp_nfs_False_switch[of nfs Q "set R"] \<open>?urctest\<close>
        have switch: "?R = qrstep False Q (set R)" (is "_ = ?R'") by auto
        from switch SNt \<open>?urctest\<close> have SNt: "SN_on ?R' {t \<cdot> \<sigma>}" by simp
        note steps = steps[unfolded switch]
        have le: "n \<le> k + n" by simp
        show "(t \<cdot> ?I \<sigma>, u \<cdot> ?I \<tau>) \<in> NS^*"
          using i_trans_sound_dp[OF finite_set _ _ le st steps SNt u1 _ orient]
            u2 by (auto simp: mode_cond_def mode_NS_def) 
      qed
    qed
  qed
qed

type_synonym ('d,'f)usable_rules_checker_impl = "('d,'f,string)dpp_ops \<Rightarrow> 'd \<Rightarrow> bool \<Rightarrow> 'f af \<Rightarrow> ('f,string)rules option \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)rules result"

definition smart_usable_rules_checker_impl :: "('d,'f :: {showl, compare_order})usable_rules_checker_impl"
  where "smart_usable_rules_checker_impl I d ce \<pi> U_opt sts \<equiv> 
    let nfs = dpp_ops.nfs I d;
        m = dpp_ops.minimal I d;
        wwf = dpp_ops.wwf_rules I d;
        qempty = dpp_ops.Q_empty I d
      in case U_opt of None \<Rightarrow> return (dpp_ops.rules I d)
           | Some U \<Rightarrow> if 
                  dpp_ops.NFQ_subset_NF_rules I d 
                \<and> (nfs \<or> isOK(check_varcond_subset sts))
                \<and> (nfs \<or> m \<or> wwf)
             then do {
                 let urc = is_ur_closed_af_impl_dpp_mv I d \<pi> U;
                 let check_urc = (\<lambda> S t. check (urc S t) (showsl_lit (STR ''term '') \<circ> showsl t \<circ> showsl_lit (STR '' is not closed under usable rules'')));                 
                 check_allm (\<lambda>(s, t). check_urc [s] t) sts;
                 check_allm (\<lambda>(l,r). check_urc (args l) r) U;
                 return U
              }
             else do {
               check (m \<and> ce \<and> (nfs \<longrightarrow> qempty \<or> wwf)) (showsl_lit (STR ''minimality and ce-compatibility and well formedness required''));
               check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''variables as lhss not allowed''))) (dpp_ops.rules I d);               
               let rm = dpp_ops.rules_map I d;     
               check_ur_P_closed_rm_af rm U \<pi> sts;
               return U
             }"

lemma smart_usable_rules_checker_impl: assumes I: "dpp_spec I"
  and check: "smart_usable_rules_checker_impl I d ce \<pi> U_opt sts = return U"
  shows "smart_usable_rules_checker (dpp_ops.nfs I d) (dpp_ops.minimal I d) ce (wwf_qtrs (set (dpp_ops.Q I d)) (set (dpp_ops.rules I d))) \<pi> (set (dpp_ops.Q I d)) (dpp_ops.rules I d) U_opt (set sts) = Some U" (is "?l = Some U")
proof -
  interpret dpp_spec I by fact
  let ?nfs = "NFS d"
  let ?m = "M d"
  let ?R = "set (R d) \<union> set (Rw d)"
  have id: "set (rules d) = ?R" by auto
  let ?wwf = "wwf_qtrs (set (Q d)) ?R"
  note check = check[unfolded smart_usable_rules_checker_impl_def Let_def]
  note d = smart_usable_rules_checker_def[of ?nfs ?m ce ?wwf \<pi> _ _ U_opt "set sts"]
  show ?thesis
  proof (cases U_opt)
    case None
    with check have U: "U = dpp_ops.rules I d" by simp
    then show ?thesis using d unfolding None U by simp
  next
    case (Some U')
    note d = d[unfolded Some option.simps]
    let ?Q = "set (Q d)"
    note d = d[of ?Q "rules d", unfolded id]
    note check = check[unfolded Some option.simps dpp_spec_sound check_varcond_subset set_vars_term_list] 
    let ?inntest = "NF_terms ?Q \<subseteq> NF_trs ?R \<and> (?nfs \<or> (\<forall> (s,t) \<in> set sts. vars_term t \<subseteq> vars_term s)) \<and> (?nfs \<or> ?m \<or> ?wwf)"
    show ?thesis
    proof (cases ?inntest)
      case True
      then have inn: "?inntest = True" by simp
      note d = d[unfolded dpp_spec_sound, unfolded inn if_True Let_def]
      note check = check[unfolded inn if_True Let_def, simplified, unfolded is_ur_closed_af_impl_dpp_mv[OF I], simplified dpp_spec_sound]
      then show ?thesis unfolding Some using d by auto
    next
      case False
      then have ninn: "?inntest = False" by simp
      note d = d[unfolded dpp_spec_sound, unfolded ninn if_False Let_def]
      note check' = check[unfolded ninn if_False Let_def, simplified] 
      from check' have check: "isOK(check_ur_P_closed_rm_af (rules_map d) U' \<pi> sts)" and U: "U' = U" by auto
      have id': "?R = set (rules d)" by simp
      have "ur_closed_af ?R (set U') UNIV \<pi> \<and> 
        ur_P_closed_af ?R (set U') UNIV \<pi> (set sts)" (is "?ur1 \<and> ?ur2")
        unfolding id'
        by (rule check_ur_P_closed_rm_af_sound[OF _ _ check], insert check', auto)
      then show ?thesis unfolding Some id unfolding d unfolding U using check' by auto 
    qed
  qed
qed

end

