(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Innermost_Usable_Rules
imports
  Icap
  TRS.QDP_Framework
  Ord.Reduction_Pair
  Usable_Rules
begin

definition rule_match :: "('f,string)trs \<Rightarrow> ('f,string)terms \<Rightarrow> ('f,string)cap_fun \<Rightarrow> ('f,string)terms \<Rightarrow> 
  'f \<Rightarrow> ('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> bool" where
  "rule_match R Q ecap S f ts l \<equiv> \<exists> \<mu>. mgu_class (Fun f (map (ecap R Q S) ts)) l = Some \<mu>
    \<and> (S \<union> mv_yvar ` (set (args l))) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu> \<subseteq> NF_terms Q"

lemma rule_match_cong: assumes "\<And> t. t \<in> set ts \<Longrightarrow> ecap R Q S t = ecap' R Q S t"
  shows "rule_match R Q ecap S f ts = rule_match R Q ecap' S f ts"
proof -
  from assms have id: "map (ecap R Q S) ts = map (ecap' R Q S) ts"
    by (induct ts, auto)
  show ?thesis 
    by (intro ext, unfold rule_match_def id, auto) 
qed

lemma rule_match_icap': "rule_match R Q icap' (mv_xvar ` S) f (map mv_xvar ts) = rule_match R Q icap  (mv_xvar ` S) f (map mv_xvar ts)"
  by (rule rule_match_cong, insert icap'[of R Q S], auto)

lemma rule_matchI: assumes ecap: "is_ecap ecap" 
  and S: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
  and NF_l: "\<forall> s \<lhd> l \<cdot> \<delta>. s \<in> NF_terms Q"
  and steps: "(Fun f ts \<cdot> \<sigma>, l \<cdot> \<delta>) \<in> (nrqrstep nfs Q R)^*"
  shows "rule_match R Q ecap (mv_xvar ` S) f (map mv_xvar ts) l"
proof -
  let ?n = "length ts"
  from nrqrsteps_preserve_root[OF steps] have "root (l \<cdot> \<delta>) = Some (f,?n)" by auto
  then obtain ls where l: "l \<cdot> \<delta> = Fun f ls" and ls: "length ls = ?n" by (cases "l \<cdot> \<delta>", auto)
  let ?S = "mv_xvar ` S"
  let ?\<sigma> = "mv_subst \<sigma>"
  let ?ts = "map mv_xvar ts"
  have inst: "l \<cdot> \<delta> \<in> fresh_instances_subst (Fun f (map (ecap R Q ?S) ?ts)) ?\<sigma>" unfolding l
    unfolding fresh_instances_subst.simps eval_term.simps
  proof (rule, unfold length_map, intro exI conjI, rule refl, force simp: ls, intro allI impI)
    fix i
    assume i: "i < ?n"
    then have il: "i < length ls" unfolding ls .
    show "ls ! i \<in> fresh_instances_subst (map (ecap R Q ?S) ?ts ! i) ?\<sigma>"
      unfolding nth_map[OF i] nth_map[OF il] map_map o_def[of "ecap R Q ?S"]
    proof (rule ecap_steps[OF ecap])
      show "(mv_xvar (ts ! i) \<cdot> ?\<sigma>, ls ! i) \<in> (qrstep nfs Q R)^*" unfolding mv_xvar[symmetric]
        using nrqrsteps_imp_arg_qrsteps[OF steps, of i] i il unfolding l by simp
    next
      show "?S \<cdot>\<^sub>s\<^sub>e\<^sub>t ?\<sigma> \<subseteq> NF_terms Q" using S mv_xvar[of _ \<sigma>] by auto
    qed
  qed
  {
    fix x
    assume x: "Inr x \<in> vars_term (Fun f (map (ecap R Q ?S) ?ts))"
    then obtain s where s: "s \<in> set ts" and x: "Inr x \<in> vars_term (ecap R Q ?S (mv_xvar s))" by auto
    from x vars_term_ecap[OF ecap, of R Q "?S" "mv_xvar s"]
    have "x \<in> range x_var" unfolding term.set_map by auto
  }
  from mgu_class_complete[OF inst this] obtain \<mu> \<delta>'
    where mgu: "mgu_class (Fun f (map (ecap R Q ?S) ?ts)) l = Some \<mu>" 
    and delta1: "\<And> x. x \<in> range x_var \<Longrightarrow> mv_subst \<sigma> x = \<mu> x \<cdot> \<delta>'"
    and delta2: "\<And> t. t \<cdot> \<delta> = mv_yvar t \<cdot> \<mu> \<cdot> \<delta>'" by blast
  show ?thesis unfolding rule_match_def 
  proof (intro exI conjI, rule mgu, rule)
    fix t
    assume "t \<in> (?S \<union> mv_yvar ` set (args l)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>" 
    then have "t \<in> ?S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu> \<or> t \<in> mv_yvar ` set (args l) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>" (is "_ \<or> _ \<in> ?T") by auto
    then show "t \<in> NF_terms Q" 
    proof 
      assume "t \<in> ?S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>"
      then obtain s where s: "s \<in> S" and t: "t = mv_xvar s \<cdot> \<mu>" by auto
      from s S have NF: "s \<cdot> \<sigma> \<in> NF_terms Q" by auto
      also have "s \<cdot> \<sigma> = mv_xvar s \<cdot> (\<mu> \<circ>\<^sub>s \<delta>')"
        unfolding mv_xvar[of _ \<sigma>]
        by (rule term_subst_eq, unfold subst_compose_def, rule delta1,
          unfold term.set_map, auto)
      also have "... = mv_xvar s \<cdot> \<mu> \<cdot> \<delta>'" by simp                    
      finally show "t \<in> NF_terms Q" unfolding t
        by (rule NF_instance)
    next
      assume t: "t \<in> ?T"
      have "\<forall> u \<in> set (args l). u \<cdot> \<delta> \<in> NF_terms Q" using NF_l[unfolded NF_terms_args_conv[symmetric]] by (cases l, auto)
      from this[unfolded delta2]
      have NFl: "?T \<subseteq> NF_terms Q" using NF_instance[of _ \<delta>' "Id_on Q"] by auto
      then show "t \<in> NF_terms Q" using t by auto
    qed
  qed
qed    

fun is_ur_closed_term' :: "('f,string)trs \<Rightarrow> ('f,string)trs \<Rightarrow> ('f,string)terms \<Rightarrow> ('f,string)cap_fun \<Rightarrow> 'f af \<Rightarrow> ('f,string)terms \<Rightarrow> ('f,string)term \<Rightarrow> bool"
  where "is_ur_closed_term' R U Q ecap \<pi> S (Var x) = True"
     |  "is_ur_closed_term' R U Q ecap \<pi> S (Fun f ts) = (
              (\<forall> i < length ts. i \<in> \<pi> (f,length ts) \<longrightarrow> is_ur_closed_term' R U Q ecap \<pi> S (ts ! i)) \<and>                
              (\<forall> (l,r) \<in> R. (l,r) \<in> U \<or> \<not> rule_match R Q ecap S f ts l))"

abbreviation is_ur_closed_term_mv' :: "('f,string)trs \<Rightarrow> ('f,string)trs \<Rightarrow> ('f,string)terms \<Rightarrow> ('f,string)cap_fun \<Rightarrow> 'f af \<Rightarrow> ('f,string)terms \<Rightarrow> ('f,string)term \<Rightarrow> bool"
  where "is_ur_closed_term_mv' R U Q ecap \<pi> S t \<equiv> is_ur_closed_term' R U Q ecap \<pi> (mv_xvar ` S) (mv_xvar t)"

lemma is_ur_closed_mv_subt: "t \<unrhd> s \<Longrightarrow> is_ur_closed_term_mv' R U Q ecap full_af S t 
  \<Longrightarrow> is_ur_closed_term_mv' R U Q ecap full_af S s"
proof (induct rule: supteq.induct)
  case (refl t)
  then show ?case .
next
  case (subt u ss t f)
  from subt(1)[unfolded set_conv_nth] obtain i where i: "i < length ss" and u: "u = ss ! i" by auto
  from i subt(4)  have "is_ur_closed_term_mv' R U Q ecap full_af S u" unfolding u 
    by (simp, unfold full_af_def, auto)
  from subt(3)[OF this]
  show ?case .
qed


lemma is_ur_closed_term_mv_icap': "is_ur_closed_term_mv' R U Q icap' \<pi> S t = is_ur_closed_term_mv' R U Q icap \<pi> S t" (is "?l t = ?r t")
proof (induct t)
  case (Var x) show ?case by simp
next
  case (Fun f ts)  
  then have rec: "\<And> t. t \<in> set ts \<Longrightarrow>  ?l t = ?r t" by auto
  then have rec: "\<And> P. (\<forall> i < length ts. P i \<longrightarrow> ?l (ts ! i)) = 
    (\<forall> i < length ts. P i \<longrightarrow> ?r (ts ! i))"
    unfolding set_conv_nth by auto
  let ?m = "mv_xvar"
  let ?S = "?m ` S"
  show "?l (Fun f ts) = ?r (Fun f ts)"    
    unfolding term.simps is_ur_closed_term'.simps rule_match_icap'
    using rec[of "\<lambda> i. i \<in> \<pi> (f, length ts)"]
    by auto
qed

locale R_Q_U_ecap = 
  fixes R U :: "('f,string)trs"
  and Q :: "('f,string)terms"
  and ecap :: "('f,string)cap_fun" 
  assumes ecap: "is_ecap ecap"
    and NF_Q_R: "NF_terms Q \<subseteq> NF_trs R"
begin

abbreviation NFQ :: "('f,string)terms" where "NFQ \<equiv> NF_terms Q"
abbreviation e_cap where "e_cap \<equiv> ecap R Q"
abbreviation is_ur_closed_term where "is_ur_closed_term \<equiv> is_ur_closed_term' R U Q ecap"
abbreviation is_ur_closed_term_mv where "is_ur_closed_term_mv \<equiv> is_ur_closed_term_mv' R U Q ecap"

lemma is_ur_closed_term_main_af: assumes steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i)"
  and varcond: "\<And> i. Suc i < n \<Longrightarrow> \<not> nfs \<Longrightarrow> vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i)) \<and> is_Fun (fst (lr i))"
  and \<sigma>: "\<sigma> ` vars_term t \<subseteq> NFQ"
  and t0: "ts 0 = t \<cdot> \<sigma>"
  and S: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ"
  and U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv \<pi> (set (args l)) r"
  and closed: "is_ur_closed_term_mv \<pi> S t"
  and reg_pos: "af_regarded_pos \<pi> (ts i) (p i)"
  and i: "i < n"
  shows "lr i \<in> U"
proof -
  let ?vc = "\<lambda> (lr :: nat \<Rightarrow> ('f,string)rule) i. \<not> nfs \<longrightarrow> vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i)) \<and> is_Fun (fst (lr i))"
  obtain vc where vc: "vc = ?vc" by auto
  let ?m = "[\<lambda> (nt :: nat \<times> ('f,string)term). fst nt, \<lambda> nt. size (snd nt)]"
  let ?P = "\<lambda> (n,t). (\<forall> \<sigma> u S ts lr p \<tau>. (\<forall> i. Suc i < n \<longrightarrow> vc lr i) \<longrightarrow> ts 0 = t \<cdot> \<sigma> \<longrightarrow> ts n = u \<longrightarrow> S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ \<longrightarrow> 
     (\<sigma> ` vars_term t \<subseteq> NFQ) \<longrightarrow> is_ur_closed_term_mv \<pi> S t \<longrightarrow> 
     (\<forall> i < n. (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i)) \<longrightarrow> 
     (\<forall> i < n. af_regarded_pos \<pi> (ts i) (p i) \<longrightarrow> lr i \<in> U))"
  {
    fix n t
    have "?P (n,t)"
    proof (induct rule: wf_induct[OF wf_measures[of ?m], of ?P])
      case (1 nt)
      obtain n t where nt: "nt = (n,t)" by force
      note 1 = 1[unfolded nt, rule_format]
      show ?case
        unfolding nt split
      proof (intro allI, intro impI)
        fix \<sigma> u S ts lr p \<tau>
        assume vc_lr: "\<forall> i. Suc i < n \<longrightarrow> vc lr i"
          and t\<sigma>: "ts 0 = t \<cdot> \<sigma>" 
          and tsn: "ts n = u" 
          and S: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" 
          and \<sigma>: "\<sigma> ` vars_term t \<subseteq> NFQ" 
          and ur: "is_ur_closed_term_mv \<pi> S t"
          and steps: "\<forall> i < n. (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i)"
        let ?S = "mv_xvar ` S"
        let ?t = "mv_xvar t"
        show "\<forall> i < n. af_regarded_pos \<pi> (ts i) (p i) \<longrightarrow> lr i \<in> U"
        proof (cases n)
          case 0 then show ?thesis by auto
        next
          case (Suc m)
          {
            fix i
            assume i: "i < m" and af: "af_regarded_pos \<pi> (ts i) (p i)"
            with vc_lr Suc have vc: "\<And> i. i < m \<Longrightarrow> vc lr i" by auto
            have m: "((m,t),(n,t)) \<in> measures ?m" unfolding Suc by auto
            have "lr i \<in> U"
              by (rule 1[OF m, unfolded split, rule_format, of lr ts \<sigma> _ _ p \<tau>],
                rule vc, simp, rule t\<sigma>, rule refl, insert S \<sigma> ur i steps Suc af, auto)
          } note IH = this
          have main: "af_regarded_pos \<pi> (ts m) (p m) \<longrightarrow> lr m \<in> U"
          proof
            assume af: "af_regarded_pos \<pi> (ts m) (p m)"
            show "lr m \<in> U"
            proof (cases "\<forall> i < m. p i \<noteq> []")
              case False
              then obtain i where i: "i < m" and p: "p i = []" by auto
              with steps[THEN spec[of _ i]] have "(ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) [] (\<tau> i)" unfolding Suc by auto
              then obtain l r where l\<tau>: "l \<cdot> \<tau> i = ts i" and r\<tau>: "r \<cdot> \<tau> i = ts (Suc i)"  and lr': "(l,r) \<in> R" and lr: "(l,r) = lr i" and NF: "\<forall> u \<lhd> l \<cdot> \<tau> i. u \<in> NFQ" 
                and nfs: "NF_subst nfs (l,r) (\<tau> i) Q" unfolding qrstep_r_p_s_def by auto
               from IH[OF i] U lr
              have ur: "is_ur_closed_term_mv \<pi> (set (args l)) r" unfolding p by auto
              let ?ts = "\<lambda> j. ts (Suc i + j)"
              let ?lr = "\<lambda> j. lr (Suc i + j)"
              let ?p = "\<lambda> j. p (Suc i + j)"
              let ?\<tau> = "\<lambda> j. \<tau> (Suc i + j)"
              from i Suc have i': "Suc i < n" by simp
              from vc_lr[rule_format, OF i', unfolded vc]
              have vcond: "\<not> nfs \<Longrightarrow> vars_term r \<subseteq> vars_term l \<and> is_Fun l" unfolding lr[symmetric] by auto
              have "is_Fun l" 
              proof (cases l)
                case (Fun f ls)
                then show ?thesis by auto
              next
                case (Var x)
                with vcond have nfs by (cases nfs, auto)
                from nfs[unfolded NF_subst_def, rule_format, OF \<open>nfs\<close>] have "l \<cdot> \<tau> i \<in> NFQ"
                  unfolding Var vars_rule_def by auto
                with NF_Q_R have "l \<cdot> \<tau> i \<in> NF_trs R" by auto
                with rstepI[OF  \<open>(l,r) \<in> R\<close> refl refl, of Hole "\<tau> i"] have False by auto
                then show ?thesis ..
              qed
              then obtain f ls where l: "l = Fun f ls" by (cases l, auto)
              {
                fix x
                assume x: "x \<in> vars_term r"
                have "\<tau> i x \<in> NFQ"
                proof (cases nfs)
                  case False
                  with vcond x have "x \<in> vars_term l" by auto
                  then have "Var x \<lhd> l" unfolding l by auto
                  then have "Var x \<cdot> \<tau> i \<lhd> l \<cdot> \<tau> i" by (rule supt_subst)
                  with NF show "\<tau> i x \<in> NFQ" by auto
                next
                  case True
                  from nfs[unfolded NF_subst_def, rule_format, OF True] x
                  show ?thesis unfolding vars_rule_def by auto
                qed
              }
              then have \<tau>: "\<tau> i ` vars_term r \<subseteq> NFQ" by auto
              from NF[unfolded NF_terms_args_conv[symmetric]] have NF: "set (args l) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<tau> i \<subseteq> NFQ" by (cases l, auto)
              let ?m' = "m - Suc i"
              have IH: "((n - Suc i, r), (n,t)) \<in> measures ?m" unfolding Suc by auto
              have "lr (Suc i + ?m') \<in> U"
                by (rule 1[OF IH, unfolded split Suc, rule_format, OF _ _ refl NF \<tau> ur, of ?lr ?ts ?p ?\<tau>],
                insert steps[unfolded Suc] vc_lr i Suc af, auto simp: r\<tau> vc)
              with i show ?thesis by auto
            next
              case True note nrr = this
              {
                assume "is_Var t"
                then obtain x where t: "t = Var x" by (cases t, auto)
                with \<sigma> have "\<sigma> x \<in> NFQ" by auto
                with NF_Q_R have "\<sigma> x \<in> NF_trs R" by auto
                then have "\<sigma> x \<in> NF (qrstep nfs Q R)" using qrstep_subset_rstep[of nfs Q R] 
                  unfolding NF_def by blast
                then have NF: "t \<cdot> \<sigma> \<in> NF (qrstep nfs Q R)" unfolding t by simp
                from steps[THEN spec[of _ 0]] have "(t \<cdot> \<sigma>, ts (Suc 0)) \<in> qrstep nfs Q R" unfolding Suc t\<sigma>
                  unfolding qrstep_qrstep_r_p_s_conv by blast
                with NF have False by auto
              }
              then obtain f ss where t: "t = Fun f ss" by (cases t, auto)
              with t\<sigma> have ts0: "ts 0 = Fun f (map (\<lambda>s. s \<cdot> \<sigma>) ss)" by auto
              let ?n = "length ss" 
              let ?LR = "{(l,r) | l r. \<not> nfs \<longrightarrow> vars_term r \<subseteq> vars_term l \<and> is_Fun l}"
              let ?Q = "\<lambda> ts' is' i. ts i = Fun f ts' \<and> length ts' = ?n \<and> length is' = ?n \<and> (\<forall> j \<in> set is'. j \<le> i) \<and> 
                    (\<forall> j < ?n. (ss ! j \<cdot> \<sigma>, ts' ! j) \<in> (qrstep nfs Q (R \<inter> ?LR))^^(is' ! j))"
              {
                fix i
                assume i: "i \<le> m"
                from i have "\<exists> ts' is'. ?Q ts' is' i"
                proof (induct i)
                  case 0
                  show ?case unfolding ts0
                    by (rule exI, rule exI[of _ "replicate ?n 0"], intro conjI, rule refl, auto)
                next
                  case (Suc i)
                  then have "i \<le> m" by auto
                  from Suc(1)[OF this] obtain ts' is' where Q: "?Q ts' is' i" by blast
                  from Suc have i: "i < m" by auto
                  with steps[THEN spec[of _ i]] have step: "(ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i)"
                    unfolding \<open>n = Suc m\<close> by auto
                  then have R: "lr i \<in> R" and step: "(ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q {lr i} (lr i) (p i) (\<tau> i)" unfolding qrstep_r_p_s_def by auto
                  from True[rule_format, OF i] have "p i \<noteq> []" by auto
                  with step have step: "(ts i, ts (Suc i)) \<in> nrqrstep nfs Q ({lr i})" by (rule qrstep_r_p_s_imp_nrqrstep)
                  from vc_lr i \<open>n = Suc m\<close> have "vc lr i" by auto
                  with vc have vcond: "lr i \<in> ?LR" by auto
                  have "(ts i, ts (Suc i)) \<in> nrqrstep nfs Q (R \<inter> ?LR)"
                    by (rule set_mp[OF nrqrstep_mono step], insert R vcond, auto)
                  with Q have step: "(Fun f ts', ts (Suc i)) \<in> nrqrstep nfs Q (R \<inter> ?LR)" by auto
                  then obtain l r D \<tau> where step: "(l,r) \<in> (R \<inter> ?LR)" "Fun f ts' = D\<langle>l\<cdot>\<tau>\<rangle>" 
                    "ts (Suc i) = D\<langle>r \<cdot> \<tau>\<rangle>" "D \<noteq> \<box>" "\<forall> u \<lhd> l\<cdot>\<tau>. u \<in> NFQ" "NF_subst nfs (l,r) \<tau> Q"
                    unfolding nrqrstep_def by blast
                  from step obtain bef C aft where "D = More f bef C aft" by (cases D, auto)
                  note step = step[unfolded this]
                  from step have ts': "ts' = bef @ C\<langle>l\<cdot>\<tau>\<rangle> # aft" by simp
                  let ?j = "length bef"
                  let ?ts' = "bef @ C\<langle>r\<cdot>\<tau>\<rangle> # aft"
                  let ?is' = "is'[?j := Suc(is' ! ?j)]"
                  show ?case
                  proof (rule exI[of _ ?ts'], rule exI[of _ ?is'], intro conjI)
                    show "ts (Suc i) = Fun f ?ts'" unfolding step by simp
                    show "length ?ts' = ?n" using Q step by auto
                    show "length ?is' = ?n" using Q step by auto
                    show "\<forall> j \<in> set ?is'. j \<le> Suc i" 
                    proof
                      fix j
                      assume j': "j \<in> set ?is'"
                      have j: "?j < length is'" using Q step by auto
                      have "j \<in> insert (Suc (is' ! ?j)) (set is')" 
                        by (rule set_mp[OF set_update_subset_insert j'])
                      then have "j = Suc (is' ! ?j) \<or> j \<in> set is'" by auto
                      then show "j \<le> Suc i"
                      proof
                        assume j': "j = Suc (is' ! ?j)"
                        from j have "is' ! ?j \<in> set is'" by auto
                        with Q have "is' ! ?j \<le> i" by auto
                        then show ?thesis using j' by auto
                      next
                        assume j: "j \<in> set is'"
                        with Q show ?thesis by auto
                      qed
                    qed
                    show "\<forall> j < ?n. (ss ! j \<cdot> \<sigma>, ?ts' ! j) \<in> qrstep nfs Q (R \<inter> ?LR) ^^ (?is' ! j)"
                    proof (intro allI impI)
                      fix j
                      assume j: "j < ?n"
                      with Q have steps: "(ss ! j \<cdot> \<sigma>, ts' ! j) \<in> qrstep nfs Q (R \<inter> ?LR) ^^ (is' ! j)" by simp
                      show "(ss ! j \<cdot> \<sigma>, ?ts' ! j) \<in> qrstep nfs Q (R \<inter> ?LR) ^^ (?is' ! j)"
                      proof (cases "?j = j")
                        case False
                        with steps show ?thesis unfolding ts' nth_append nth_list_update_neq[OF False]
                          by auto
                      next
                        case True
                        then have j: "j = length bef" "length bef < length is'" using j step Q by auto
                        from step have onestep: "(ts' ! j, ?ts' ! j) \<in> qrstep nfs Q (R \<inter> ?LR)" unfolding j ts' by auto
                        from j have is': "?is' ! j = Suc (is' ! j)" by auto
                        show ?thesis unfolding is' using steps onestep by auto
                      qed
                    qed
                  qed
                qed
              } note details = this
              then have "\<forall> i. \<exists> ts' is'. i \<le> m \<longrightarrow> ?Q ts' is' i" by auto
              from choice[OF this] obtain ts' where "\<forall> i. \<exists> is'. i \<le> m \<longrightarrow> ?Q (ts' i) is' i" by auto
              from choice[OF this] obtain is' where Q: "\<And> i. i \<le> m \<Longrightarrow> ?Q (ts' i) (is' i) i" by auto
              show ?thesis 
              proof (cases "p m = []")
                case True
                with steps \<open>n = Suc m\<close> have "(ts m, ts (Suc m)) \<in> qrstep_r_p_s nfs Q R (lr m) [] (\<tau> m)" by auto
                then obtain l r where lr: "(l,r) \<in> {lr m}" and l\<tau>: "ts m = l \<cdot> \<tau> m" and r\<tau>: "ts (Suc m) = r \<cdot> \<tau> m" 
                  and lr': "(l,r) \<in> R" and NF: "\<forall> s \<lhd> l \<cdot> \<tau> m. s \<in> NFQ" unfolding qrstep_r_p_s_def by (cases "lr m", auto)
                let ?ss = "map mv_xvar ss"
                let ?\<sigma> = "mv_subst \<sigma>"
                from ur[unfolded t] lr' 
                have choice: "(l,r) \<in> U \<or> (\<not> rule_match R Q ecap (mv_xvar ` S) f (map mv_xvar ss) l)" (is "_ \<or> \<not> ?check") by auto
                have ?check
                proof (rule rule_matchI[OF ecap S NF])
                  define RR where "RR = R \<inter> {(l, r) |l r. \<not> nfs \<longrightarrow> vars_term r \<subseteq> vars_term l \<and> is_Fun l}"
                  have RR: "RR \<subseteq> R" unfolding RR_def by auto
                  from Q[of m] l\<tau> have id: "l \<cdot> \<tau> m = Fun f (ts' m)" and len: "length (ts' m) = length ss" by auto
                  {
                    fix i
                    assume "i < length ss"
                    with Q[of m] have "(ss ! i \<cdot> \<sigma>, ts' m ! i) \<in> qrstep nfs Q RR ^^ is' m ! i" 
                      unfolding RR_def by auto
                    from relpow_imp_rtrancl[OF this] rtrancl_mono[OF qrstep_mono[OF RR subset_refl]]
                    have "(ss ! i \<cdot> \<sigma>, ts' m ! i) \<in> (qrstep nfs Q R)^*" by auto
                  } note steps = this
                  show "(Fun f ss \<cdot> \<sigma>, l \<cdot> \<tau> m) \<in> (nrqrstep nfs Q R)\<^sup>*" 
                    using steps len
                    unfolding id 
                    unfolding eval_term.simps
                    by (intro args_steps_imp_nrqrsteps, auto)
                qed
                with choice have "(l,r) \<in> U" by simp                
                then show ?thesis using lr by auto
              next
                assume p: "p m \<noteq> []"
                from p obtain I P where p: "p m = (I # P)" by (cases "p m", auto)
                from steps[THEN spec[of _ m]] have stepP: "(ts m, ts (Suc m)) \<in> qrstep_r_p_s nfs Q R (lr m) (p m) (\<tau> m)" unfolding Suc by auto
                from stepP[unfolded qrstep_r_p_s_def]
                obtain l r D where step: "(l,r) \<in> {lr m}" "p m \<in> poss (ts m)" "ts m |_ p m = l\<cdot> \<tau> m" "ts (Suc m) = D\<langle>r \<cdot> \<tau> m\<rangle>" "\<forall> u \<lhd> l\<cdot>\<tau> m. u \<in> NFQ" "(l,r) \<in> R" and D: "D = ctxt_of_pos_term (p m) (ts m)" by (cases "lr m", auto)
                from ctxt_supt_id[OF step(2)] have tsmD: "ts m = D\<langle>l \<cdot> \<tau> m\<rangle>" unfolding step D by simp
                from Q[of m]  have tsm: "ts m = Fun f (ts' m)" by auto
                from D[unfolded tsm p] have D: "D = More f (take I (ts' m)) (ctxt_of_pos_term P (ts' m ! I)) (drop (Suc I) (ts' m))" by simp
                then obtain bef aft C where bef: "bef = take I (ts' m)" and D: "D = More f bef C aft" and C: "C = ctxt_of_pos_term P (ts' m ! I)" by auto
                from bef step[unfolded p tsm] Q[of m] have lbef: "length bef = I" "I < ?n" by auto
                note tsmD = tsmD[unfolded D]
                from tsm[unfolded tsmD] have ts'm: "ts' m = bef @ C\<langle>l \<cdot> \<tau> m\<rangle> # aft" by simp
                from Q[of m] lbef(2) obtain j where steps: "(ss ! I \<cdot> \<sigma>, ts' m ! I) \<in> qrstep nfs Q (R \<inter> ?LR) ^^ j" and j: "j \<le> m" by auto
                from af[unfolded tsm p]
                have af: "I < length (ts' m)" "I \<in> \<pi> (f,length (ts' m))" "af_regarded_pos \<pi> (ts' m ! I) P" by auto
                from steps[unfolded relpow_fun_conv] obtain ss' where first: "ss' 0 = ss ! I \<cdot> \<sigma>" and last: "ss' j = ts' m ! I"
                  and steps: "\<forall> i < j. (ss' i, ss' (Suc i)) \<in> qrstep nfs Q (R \<inter> ?LR)" by auto
                {
                  fix i
                  assume i: "i < j"
                  from steps[THEN spec, THEN mp[OF _ this], unfolded qrstep_qrstep_r_p_s_conv]
                  have "\<exists> lr p \<tau>. (ss' i, ss' (Suc i)) \<in> qrstep_r_p_s nfs Q (R \<inter> ?LR) lr p \<tau>" by auto
                }
                then have "\<forall> i. \<exists> lr p \<tau>. i < j \<longrightarrow> (ss' i, ss' (Suc i)) \<in> qrstep_r_p_s nfs Q (R \<inter> ?LR) lr p \<tau>" by auto
                from choice[OF this] obtain lr' where "\<forall> i. \<exists> p \<tau>. i < j \<longrightarrow> (ss' i, ss' (Suc i)) \<in> qrstep_r_p_s nfs Q (R \<inter> ?LR) (lr' i) p \<tau>" by auto
                from choice[OF this] obtain p' where "\<forall> i. \<exists> \<tau>. i < j \<longrightarrow> (ss' i, ss' (Suc i)) \<in> qrstep_r_p_s nfs Q (R \<inter> ?LR) (lr' i) (p' i) \<tau>" by auto
                from choice[OF this] obtain \<tau>' where "\<And> i. i < j \<Longrightarrow> (ss' i, ss' (Suc i)) \<in> qrstep_r_p_s nfs Q (R \<inter> ?LR) (lr' i) (p' i) (\<tau>' i)" by auto
                then have steps: "\<And> i. i < j \<Longrightarrow> (ss' i, ss' (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr' i) (p' i) (\<tau>' i)" 
                  and lr'': "\<And> i. i < j \<Longrightarrow> lr' i \<in> ?LR" 
                  unfolding qrstep_r_p_s_def by auto
                let ?ss = "\<lambda> i. if i \<le> j then ss' i else C\<langle>r\<cdot>\<tau> m\<rangle>"
                let ?lr = "\<lambda> i. if i < j then lr' i else lr m"
                let ?p  = "\<lambda> i. if i < j then p' i else P"
                let ?\<tau>  = "\<lambda> i. if i < j then \<tau>' i else \<tau> m"
                have vc_lr: "\<And> i. i < j \<Longrightarrow> vc ?lr i" using lr'' vc_lr Suc unfolding vc by (cases nfs, force+)
                from stepP[unfolded p] have "(ts m, ts (Suc m)) \<in> qrstep_r_p_s nfs Q R (lr m) ([I] @ P) (\<tau> m)" by auto
                from qrstep_subt_at_gen[OF this] have step: "(ts' m ! I, C\<langle>r \<cdot> \<tau> m\<rangle>) \<in> qrstep_r_p_s nfs Q R (lr m) P (\<tau> m)"
                  unfolding tsm step D using lbef by auto
                from ts'm have tsm: "ts' m = bef @ C\<langle>l\<cdot>\<tau> m\<rangle> # aft" .
                from step last
                have step: "(?ss j, ?ss (Suc j)) \<in> qrstep_r_p_s nfs Q R (lr m) P (\<tau> m)" unfolding tsm by auto
                from j Suc have jn: "Suc j \<le> n" by auto
                from lbef t have ssi: "ss ! I \<in> set ss" by auto
                then have size: "size (ss ! I) < size t" unfolding t by (auto simp: size_simps)
                from \<sigma>[unfolded t] ssi have \<sigma>: "\<sigma> ` vars_term (ss ! I) \<subseteq> NFQ" by auto
                have meas: "((Suc j,ss ! I), (n,t)) \<in> measures ?m" using jn size by auto
                from ur[unfolded t] lbef(2) af Q[of m] have ur: "is_ur_closed_term_mv \<pi> S (ss ! I)" by simp                 
                have "?lr j \<in> U"
                proof (rule 1[OF meas, unfolded split, rule_format, OF vc_lr _ refl S \<sigma> ur, of ?ss ?p ?\<tau>])
                  fix i
                  assume i: "i < Suc j"
                  show "(?ss i, ?ss (Suc i)) \<in> qrstep_r_p_s nfs Q R (?lr i) (?p i) (?\<tau> i)"
                  proof (cases "i < j")
                    case False
                    with i have i: "i = j" by auto
                    show ?thesis unfolding i using step by auto
                  next
                    case True
                    from steps[OF this] True show ?thesis by auto
                  qed
                qed (insert af last first, auto)
                then show ?thesis by simp
              qed
            qed
          qed          
          show ?thesis unfolding Suc 
          proof (intro allI impI)
            fix i
            assume "i < Suc m" and af: "af_regarded_pos \<pi> (ts i) (p i)"
            then have "i < m \<or> i = m" by auto
            with IH main af show "lr i \<in> U" by auto
          qed
        qed
      qed
    qed
  }
  then have main: "?P (n,t)" .
  show ?thesis
    by (rule main[unfolded split vc, rule_format, of _ ts, OF _ t0 refl S \<sigma> closed steps i, OF _ _ reg_pos],
      insert varcond, auto)
qed

lemma is_ur_closed_term_main: assumes steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}"
   and varcond: "\<And> i. Suc i < n \<Longrightarrow> \<not> nfs \<Longrightarrow> vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i)) \<and> is_Fun (fst (lr i))"
   and \<sigma>: "\<sigma> ` vars_term t \<subseteq> NFQ"
   and lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> R"
   and t0: "ts 0 = t \<cdot> \<sigma>"
   and S: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ"
   and U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r"
   and closed: "is_ur_closed_term_mv full_af S t"
   and i: "i < n"
  shows "lr i \<in> U"
proof -
  let ?ts = "\<lambda> i. (ts i, ts (Suc i))"
  {
    fix i
    assume "i < n"
    from steps[rule_format, OF this] lr[OF this]
    have "?ts i \<in> qrstep nfs Q (R \<inter> {lr i})" by auto
    from this[unfolded qrstep_qrstep_r_p_s_conv] obtain lr' p \<sigma> where "?ts i \<in> qrstep_r_p_s nfs Q (R \<inter> {lr i}) lr' p \<sigma>" by auto
    then have "\<exists> p \<sigma>. ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) p \<sigma>" unfolding qrstep_r_p_s_def by auto
  }
  then have "\<forall> i. \<exists> p \<sigma>. i < n \<longrightarrow> ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) p \<sigma>" by simp
  from choice[OF this] obtain p where "\<forall> i. \<exists> \<sigma>. i < n \<longrightarrow> ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) (p i) \<sigma>" by auto
  from choice[OF this] obtain \<sigma> where steps: "\<And> i. i < n \<Longrightarrow> ?ts i \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<sigma> i)" by auto
  show ?thesis 
  proof (rule is_ur_closed_term_main_af[of n ts nfs lr p \<sigma>, OF steps varcond \<sigma> t0 S U closed _ i])
    show "af_regarded_pos full_af (ts i) (p i)" unfolding af_regarded_full
      using qrstep_r_p_s_imp_poss[OF steps[OF i]] ..
  qed
qed

lemma is_ur_closed_term_last: assumes steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R')^*"
  and \<sigma>: "\<sigma> ` vars_term t \<subseteq> NFQ"
  and S: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ"
  and U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r"
  and R': "R' \<subseteq> R"
  and varcond_or_SN: "\<not> nfs \<Longrightarrow> wwf_qtrs Q R' \<or> SN_on (qrstep nfs Q R') {t \<cdot> \<sigma>}"
  and closed: "is_ur_closed_term_mv full_af S t"
  and step: "(u,v) \<in> qrstep_r_p_s nfs Q R' lr' p \<tau>"
  shows "lr' \<in> U"
proof -
  from steps[unfolded qrsteps_rules_conv] obtain n ts lr where first: "ts 0 = t \<cdot> \<sigma>" and last: "ts n = u" and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}" and lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> R'" by blast+
  let ?lr = "\<lambda> i. if i < n then lr i else lr'"
  let ?ts = "\<lambda> i. if i \<le> n then ts i else v"
  from step have lr': "?lr n \<in> R'" unfolding qrstep_r_p_s_def by auto
  from step have "(?ts n, ?ts (Suc n)) \<in> qrstep_r_p_s nfs Q R' lr' p \<tau>" unfolding last by simp
  also have "qrstep_r_p_s nfs Q R' lr' p \<tau> \<subseteq> qrstep_r_p_s nfs Q {?lr n} lr' p \<tau>" unfolding qrstep_r_p_s_def by auto
  finally have step: "(?ts n, ?ts (Suc n)) \<in> qrstep nfs Q {?lr n}" unfolding qrstep_qrstep_r_p_s_conv by blast
  have "?lr n \<in> U"
  proof (rule is_ur_closed_term_main[of "Suc n" ?ts nfs ?lr \<sigma> t, OF _ _ \<sigma> _ _ S U closed]) 
    fix i
    assume i: "i < Suc n"
    from i show "(?ts i, ?ts (Suc i)) \<in> qrstep nfs Q {?lr i}" using steps step by (cases "i = n", auto)
    from i show "?lr i \<in> R" using R' lr lr' by (cases "i = n", auto)
  next
    fix i'
    assume "Suc i' < Suc n" and nfs: "\<not> nfs"
    then have i': "i' < n" by auto
    then have id: "?lr i' = lr i'" by auto
    from nfs varcond_or_SN have "wwf_qtrs Q R' \<or> SN_on (qrstep nfs Q R') {t \<cdot> \<sigma>}" by simp
    then show "vars_term (snd (?lr i')) \<subseteq> vars_term (fst (?lr i')) \<and> is_Fun (fst (?lr i'))" 
    proof
      assume SN: "SN_on (qrstep nfs Q R') {t \<cdot> \<sigma>}"
      have i'steps: "(t \<cdot> \<sigma>, ts i') \<in> (qrstep nfs Q R')^*"
        unfolding qrsteps_rules_conv
      proof (intro exI conjI, rule first, rule refl)
        show "\<forall> i < i'. (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> R'"
        proof (intro allI impI)
          fix i
          assume "i < i'" with i' have "i < n" by simp
          from steps[OF this] lr[OF this]
          show "(ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> R'" by simp
        qed
      qed        
      have SN: "SN_on (qrstep nfs Q R') {ts i'}"
        by (rule steps_preserve_SN_on[OF i'steps SN])
      from steps[OF i'] lr[OF i'] have "(ts i', ts (Suc i')) \<in> qrstep nfs Q (R' \<inter> {lr i'})" by auto 
      from this[unfolded qrstep_qrstep_r_p_s_conv] obtain lr' p \<sigma> where "(ts i', ts (Suc i')) \<in> qrstep_r_p_s nfs Q (R' \<inter> {lr i'}) lr' p \<sigma>" by blast
      then have step: "(ts i', ts (Suc i')) \<in> qrstep_r_p_s nfs Q R' (lr i') p \<sigma>" unfolding qrstep_r_p_s_def by auto
      from SN_on_qrstep_r_p_s_imp_wf_rule[OF SN step nfs]
      show ?thesis unfolding id by auto
    next
      assume wwf: "wwf_qtrs Q R'"
      obtain ll rr where llrr: "lr i' = (ll,rr)" by force
      with steps[OF i'] have step: "(ts i', ts (Suc i')) \<in> qrstep nfs Q (applicable_rules Q {(ll,rr)})" 
        unfolding qrstep_applicable_rules by simp
      from llrr lr[OF i'] have mem: "(ll,rr) \<in> R'" by auto
      from wwf have wf: "wf_trs (applicable_rules Q R')" unfolding wwf_qtrs_wf_trs .
      from step mem have "(ll,rr) \<in> applicable_rules Q R'" 
        unfolding applicable_rules_def by auto
      with wf
      show ?thesis unfolding id unfolding llrr wf_trs_def by force
    qed
  qed (insert first, auto)
  then show ?thesis by simp
qed


lemma is_ur_closed_term: assumes steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R')^*"
  and \<sigma>: "\<sigma> ` vars_term t \<subseteq> NFQ"
  and S: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ"
  and U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r"
  and R': "R' \<subseteq> R"
  and varcond_or_SN: "\<not> nfs \<Longrightarrow> wwf_qtrs Q R' \<or> SN_on (qrstep nfs Q R') {t \<cdot> \<sigma>}"
  and closed: "is_ur_closed_term_mv full_af S t"
  shows "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q (R' \<inter> U))^*"
  using steps
proof (induct)
  case (step u v)
  from step(2)[unfolded qrstep_qrstep_r_p_s_conv] obtain lr p \<tau> where last: "(u,v) \<in> qrstep_r_p_s nfs Q R' lr p \<tau>" by auto
  from is_ur_closed_term_last[OF step(1) \<sigma> S U R' varcond_or_SN closed last] have "lr \<in> U" .
  with last have "(u,v) \<in> qrstep_r_p_s nfs Q (R' \<inter> U) lr p \<tau>" unfolding qrstep_r_p_s_def by auto
  then have "(u,v) \<in> qrstep nfs Q (R' \<inter> U)" unfolding qrstep_qrstep_r_p_s_conv by blast
  with step(3) show ?case by auto
qed auto
    
lemma is_ur_closed_term_af: assumes steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)^*"
  and \<sigma>: "\<sigma> ` vars_term t \<subseteq> NFQ"
  and S: "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ"
  and U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv \<pi> (set (args l)) r"
  and SNt: "\<not> nfs \<Longrightarrow> wwf_qtrs Q R \<or> SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}"
  and closed: "is_ur_closed_term_mv \<pi> S t"
  and af_redpair: "af_redpair St NS \<pi>"
  and UNS: "U \<subseteq> NS"
  shows "(t \<cdot> \<sigma>, u) \<in> NS^*"
proof -
  let ?NS = "NS^*"
  interpret af_redpair St NS \<pi> by fact
  from qrsteps_imp_qrsteps_r_p_s[OF steps] obtain n ts lr p \<tau> where first: "ts 0 = t \<cdot> \<sigma>" and last: "ts n = u" and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep_r_p_s nfs Q R (lr i) (p i) (\<tau> i)" by blast
  {
    fix i
    assume i: "i < n" and af: "af_regarded_pos \<pi> (ts i) (p i)"
    have "lr i \<in> U"
    proof (rule is_ur_closed_term_main_af[of n ts nfs lr p \<tau>, OF steps _ \<sigma> first S U closed af i])
      fix i
      assume "Suc i < n" and nfs: "\<not> nfs"
      then have i: "i < n" by simp
      have isteps: "(t \<cdot> \<sigma>, ts i) \<in> (qrstep nfs Q R)^*"
        by (rule qrsteps_r_p_s_imp_qrsteps[of ts _ i, OF first refl steps], insert i, auto)
      from SNt[OF nfs]
      have SN: "wwf_qtrs Q R \<or> SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}" .
      then show "vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i)) \<and> is_Fun (fst (lr i))"
      proof 
        assume SNt: "SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}"
        have SN: "SN_on (qrstep nfs Q R) {ts i}" 
          by (rule steps_preserve_SN_on[OF isteps SNt])
        from SN_on_qrstep_r_p_s_imp_wf_rule[OF SN steps[OF i] nfs]
        show "vars_term (snd (lr i)) \<subseteq> vars_term (fst (lr i)) \<and> is_Fun (fst (lr i))" .
      next
        assume wwf: "wwf_qtrs Q R"
        obtain ll rr where llrr: "lr i = (ll,rr)" by force
        from steps[OF i] have step: "(ts i, ts (Suc i)) \<in> qrstep nfs Q {(ll,rr)}" 
          and mem: "(ll,rr) \<in> R" unfolding llrr
          unfolding qrstep_qrstep_r_p_s_conv qrstep_r_p_s_def by auto
        then have step: "(ts i, ts (Suc i)) \<in> qrstep nfs Q (applicable_rules Q {(ll,rr)})" 
          unfolding qrstep_applicable_rules by auto
        from wwf have wf: "wf_trs (applicable_rules Q R)" unfolding wwf_qtrs_wf_trs .
        from step mem have "(ll,rr) \<in> applicable_rules Q R" 
          unfolding applicable_rules_def by auto
        with wf
        show ?thesis unfolding llrr wf_trs_def by force
      qed
    qed
  } note one = this
  {
    fix i
    assume i: "i < n"
    from steps[OF i, unfolded qrstep_r_p_s_def] 
    have pi: "p i \<in> poss (ts i)" 
      and s: "ts i |_ p i = fst (lr i) \<cdot> \<tau> i" 
      and t: "ts (Suc i) = replace_at (ts i) (p i) (snd (lr i) \<cdot> \<tau> i)" by auto
    from ctxt_supt_id[OF pi, unfolded s] have s: "ts i = replace_at (ts i) (p i) (fst (lr i) \<cdot> \<tau> i)" by auto
    from hole_pos_ctxt_of_pos_term[OF pi] have hp: "hole_pos (ctxt_of_pos_term (p i) (ts i)) = p i" .
    from s t hp obtain C where s: "ts i = C\<langle>fst (lr i) \<cdot> \<tau> i\<rangle>" 
      and t: "ts (Suc i) = C\<langle>snd (lr i) \<cdot> \<tau> i\<rangle>"
      and p: "hole_pos C = p i" by auto
    have "(ts i, ts (Suc i)) \<in> NS"
    proof (cases "af_regarded_pos \<pi> (ts i) (p i)")
      case True
      from one[OF i this] have lr: "lr i \<in> U" by simp
      have "(ts i, ts (Suc i)) \<in> rstep U" unfolding s t 
      proof (rule rstepI)
        show "(fst (lr i), snd (lr i)) \<in> U" using lr by simp
      qed auto
      with rstep_subset[OF ctxt_NS subst_NS UNS] show ?thesis by auto
    next
      case False
      show ?thesis unfolding s t 
        by (rule af_compatible_af_regarded_ctxt[OF af_compat ctxt_NS False[unfolded s p[symmetric]]])
    qed
  } note main = this
  show ?thesis
    unfolding rtrancl_fun_conv 
    by (rule exI[of _ ts], rule exI[of _ n], unfold first last, insert main, auto)
qed

fun usable_rules_precond :: "('f,string)dpp \<Rightarrow> bool" where
  "usable_rules_precond (nfs,m,P,Pw,_,Rs,Rw) = (
    (\<forall> l r.  (l,r) \<in> P \<union> Pw \<longrightarrow> is_ur_closed_term_mv full_af {l} r)
  \<and> (\<forall> l r. \<not> nfs \<longrightarrow> (l,r) \<in> P \<union> Pw \<longrightarrow> vars_term r \<subseteq> vars_term l)
  \<and> (\<not> nfs \<longrightarrow> \<not> m \<longrightarrow> wwf_qtrs Q (Rs \<union> Rw))
  \<and> (\<forall> l r. (l,r) \<in> U \<longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r)
  \<and> (Rs \<union> Rw \<subseteq> R)
  )"

lemma usable_rules_precondE[elim]: assumes "usable_rules_precond (nfs,m,P,Pw,Q',Rs,Rw)"
  shows "\<And> l r. (l,r) \<in> P \<union> Pw \<Longrightarrow> is_ur_closed_term_mv full_af {l} r"
  and "\<And> l r. \<not> nfs \<Longrightarrow> (l,r) \<in> P \<union> Pw \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and "\<not> nfs \<Longrightarrow> \<not> m \<Longrightarrow> wwf_qtrs Q (Rs \<union> Rw)"
  and "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r"
  and "Rs \<union> Rw \<subseteq> R"
  using assms[unfolded usable_rules_precond.simps] by blast+

lemma usable_rules_precond_mono: assumes "usable_rules_precond (nfs,m,P,Pw,Q',Rs,Rw)"
  and "P' \<union> Pw' \<subseteq> P \<union> Pw" "Rs' \<union> Rw' \<subseteq> Rs \<union> Rw"
  shows "usable_rules_precond (nfs,m,P',Pw',Q'',Rs',Rw')"
  using assms 
  unfolding usable_rules_precond.simps wwf_qtrs_def by blast+

declare usable_rules_precond.simps[simp del]

lemma usable_rules_min_ichain: assumes 
  precond: "usable_rules_precond (nfs,m,P,Pw,Q,Rs,Rw)"
  and chain: "min_ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>"
  shows "min_ichain (nfs,m,P,Pw,Q,Rs \<inter> U,Rw \<inter> U) s t \<sigma>"
proof -
  note precond = usable_rules_precondE[OF precond]
  note P = precond(1)
  note vars = precond(2)
  note varsR = precond(3)
  note U = precond(4)
  note R = precond(5)
  from chain have min: "m \<Longrightarrow> minimal_cond nfs Q (Rs \<union> Rw) s t \<sigma>" unfolding min_ichain.simps by auto     
  show "min_ichain (nfs,m,P,Pw,Q,Rs \<inter> U,Rw \<inter> U) s t \<sigma>"
    unfolding min_ichain.simps
  proof (intro conjI impI)
    assume m
    show "minimal_cond nfs Q (Rs \<inter> U \<union> Rw \<inter> U) s t \<sigma>" 
      by (rule minimal_cond_mono[OF _ min[OF \<open>m\<close>]],auto)
  next
    from chain have chain: "ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>" unfolding min_ichain.simps by simp
    note chain = chain[unfolded ichain.simps]
    from chain have inP: "\<And> i. (s i, t i) \<in> P \<union> Pw" by auto
    from chain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NFQ" by auto
    from chain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
    {
      fix i x
      assume x: "x \<in> vars_term (t i)"
      have "\<sigma> i x \<in> NFQ"
      proof (cases nfs)
        case True
        from nfs[of i, unfolded NF_subst_def, rule_format, OF True] x
        show ?thesis unfolding vars_rule_def by auto
      next
        case False
        from vars[OF False inP, of i] x
        have "x \<in> vars_term (s i)" by auto
        then have "Var x \<unlhd> s i" by auto
        then have "Var x \<cdot> \<sigma> i \<unlhd> s i \<cdot> \<sigma> i" by (rule supteq_subst)
        from NF_subterm[OF NF this]
        show "\<sigma> i x \<in> NFQ" by simp
      qed
    } 
    then have NFt: "\<And> i. \<sigma> i ` vars_term (t i) \<subseteq> NFQ" by auto
    from NF have NFs: "\<And> i. {s i} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> i \<subseteq> NFQ" by auto
    note ur = P[OF inP]    
    let ?B = "qrstep nfs Q (Rs \<union> Rw)"
    let ?B' = "qrstep nfs Q (Rs \<inter> U \<union> Rw \<inter> U)"
    let ?R = "qrstep nfs Q Rs"
    let ?R' = "qrstep nfs Q (Rs \<inter> U)"
    {
      fix i n ts lr j
      assume first: "ts 0 = t i \<cdot> \<sigma> i" and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}"
      and lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> Rs \<union> Rw"
      and j: "j < n"
      have "lr j \<in> U"
      proof (rule is_ur_closed_term_main[of n ts nfs lr, OF steps _ NFt set_mp[OF R lr] first NFs U ur j])
        fix i'
        assume "Suc i' < n" and nfs: "\<not> nfs"
        then have i': "i' < n" by auto
        show "vars_term (snd (lr i')) \<subseteq> vars_term (fst (lr i')) \<and> is_Fun (fst (lr i'))"
        proof (cases m)
          case False
          obtain ll rr where llrr: "lr i' = (ll,rr)" by force
          with steps[OF i'] have step: "(ts i', ts (Suc i')) \<in> qrstep nfs Q (applicable_rules Q {(ll,rr)})" 
            unfolding qrstep_applicable_rules by simp
          from llrr lr[OF i'] have mem: "(ll,rr) \<in> Rs \<union> Rw" by auto
          from varsR[OF nfs False] have "wwf_qtrs Q (Rs \<union> Rw)" .
          then have wf: "wf_trs (applicable_rules Q (Rs \<union> Rw))" unfolding wwf_qtrs_wf_trs .
          from step mem have "(ll,rr) \<in> applicable_rules Q (Rs \<union> Rw)" 
            unfolding applicable_rules_def by auto
          with wf
          show ?thesis unfolding llrr wf_trs_def by force
        next
          case True          
          have i'steps: "(t i \<cdot> \<sigma> i, ts i') \<in> (qrstep nfs Q (Rs \<union> Rw))^*" 
            unfolding qrsteps_rules_conv
          proof (intro exI conjI, rule first, rule refl)
            show "\<forall> i < i'. (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> Rs \<union> Rw"
            proof (intro allI impI)
              fix i
              assume "i < i'" with i' have "i < n" by simp
              from steps[OF this] lr[OF this]
              show "(ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i} \<and> lr i \<in> Rs \<union> Rw" by simp
            qed
          qed
          have SN: "SN_on (qrstep nfs Q (Rs \<union> Rw)) {ts i'}"
            by (rule steps_preserve_SN_on[OF i'steps], insert min True, unfold minimal_cond_def, auto)
          from steps[OF i'] obtain l r C \<tau> where l\<tau>: "ts i' = C\<langle>l \<cdot> \<tau>\<rangle>" and r\<tau>: "C\<langle>r \<cdot> \<tau>\<rangle> = ts (Suc i')"  and lr': "(l,r) = lr i'" and NF: "\<forall> u \<lhd> l \<cdot> \<tau>. u \<in> NFQ" by auto
          from lr' lr[OF i'] have mem: "(l,r) \<in> Rs \<union> Rw" by auto
          from only_applicable_rules[OF NF, of r] SN_on_imp_wwf_rule[OF SN l\<tau> mem NF nfs]
          have vars: "vars_term r \<subseteq> vars_term l" "is_Fun l" 
            unfolding wwf_rule_def by auto
          with lr'[symmetric]
          show "vars_term (snd (lr i')) \<subseteq> vars_term (fst (lr i')) \<and> is_Fun (fst (lr i'))" by auto
        qed
      qed
    } note ur = this
    show "ichain (nfs,m,P,Pw,Q,Rs \<inter> U,Rw \<inter> U) s t \<sigma>"
      unfolding ichain.simps
    proof (intro conjI allI, rule inP)
      fix i
      from chain have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?B^*" by simp
      from steps[unfolded qrsteps_rules_conv]
      obtain n ts lr
        where first: "ts 0 = t i \<cdot> \<sigma> i" and last: "ts n = s (Suc i) \<cdot> \<sigma> (Suc i)"
        and steps: "\<And> i. i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}"
        and lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> Rs \<union> Rw" by blast
      from ur[of ts i n lr, OF first steps lr] lr have lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> Rs \<inter> U \<union> Rw \<inter> U"
        by auto
      show "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?B'^*"
        unfolding qrsteps_rules_conv
        by (rule exI[of _ n], rule exI[of _ ts], rule exI[of _ lr], intro conjI, rule first, rule last, insert steps lr, auto)
    next
      fix i
      show "s i \<cdot> \<sigma> i \<in> NFQ" by (rule NF)
    next
      from chain have "(INFM i. (s i, t i) \<in> P) \<or>
        (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
        ?B^* O ?R O ?B^*)" (is "?l \<or> ?r") by simp
      then show "(INFM i. (s i, t i) \<in> P) \<or>
        (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
        ?B'^* O ?R' O ?B'^*)" (is "?l' \<or> ?r'")
      proof
        assume ?l then show ?thesis by auto
      next
        assume ?r
        have ?r' unfolding INFM_nat_le
        proof
          fix i
          from \<open>?r\<close>[unfolded INFM_nat_le, THEN spec[of _ i]] obtain j where j: "j \<ge> i"
            and steps: "(t j \<cdot> \<sigma> j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> ?B^* O ?R O ?B^*" (is "(?t j,?s j) \<in> _") by blast
          from qrsteps_rules_conv'[OF steps]
          obtain n ts lr k
            where first: "ts 0 = t j \<cdot> \<sigma> j" and last: "ts n = s (Suc j) \<cdot> \<sigma> (Suc j)"
            and steps: "\<And> i . i < n \<Longrightarrow> (ts i, ts (Suc i)) \<in> qrstep nfs Q {lr i}"
            and lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> Rs \<union> Rw"
            and k: "k < n" and k': "lr k \<in> Rs" by blast
          from ur[of ts j n lr, OF first steps lr] have lr': "\<And> i. i < n \<Longrightarrow> lr i \<in> U" by auto
          with lr have lr: "\<And> i. i < n \<Longrightarrow> lr i \<in> Rs \<inter> U \<union> Rw \<inter> U" by auto
          from k' lr'[OF k] have k': "lr k \<in> Rs \<inter> U" by auto
          show "\<exists> j \<ge> i. (?t j, ?s j) \<in> ?B'^* O ?R' O ?B'^*"
            by (intro exI conjI, rule j, rule qrsteps_rules_conv''[of ts _ n _ nfs _ lr, OF first last steps lr k k'])
        qed
        then show ?thesis ..
      qed      
    qed (rule nfs)
  qed
qed

lemma usable_rules_proc: assumes fin: "finite_dpp (nfs,m,P,Pw,Q,Rs \<inter> U,Rw \<inter> U)"
  and precond: "usable_rules_precond (nfs,m,P,Pw,Q,Rs,Rw)"
  shows "finite_dpp (nfs,m,P, Pw, Q, Rs, Rw)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain s t \<sigma> where "min_ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>" unfolding finite_dpp_def by auto
  from usable_rules_min_ichain[OF precond this]
  have "min_ichain (nfs, m, P, Pw, Q, Rs \<inter> U, Rw \<inter> U) s t \<sigma>" .
  with fin show False unfolding finite_dpp_def by auto
qed
end
  
locale ce_unusable_symbols = mono_ce_af_redtriple_order S NS NST \<pi>
  for S NS NST :: "('f,'v)trs" and \<pi> :: "'f af" +  
  fixes us :: "'f sig"
  and Rb :: "('f,'v)trs"
  and cn :: "'f \<times> nat"
  and m :: nat
  assumes cn: "cn = (c,m)"
  and ce: "ce_trs cn \<subseteq> S"
  and m: "m \<ge> n"
  and ctxt: "ctxt.closed S"
  and Rb: "Rb \<subseteq> NS \<union> S"
  and Rb_us: "\<And> l r. (l,r) \<in> Rb \<Longrightarrow> funas_term r \<subseteq> us"
begin

definition "SS \<equiv> S \<union> { lr. \<not> funas_term (fst lr) \<subseteq> us}"

fun itrans :: "('f,'v)term \<Rightarrow> ('f,'v)term" where 
  "itrans (Var x) = (Var x)" 
| "itrans (Fun f ts) = 
   (if (f,length ts) \<in> us then Fun f (map itrans ts) 
             else (comb cn) [Fun f (map itrans ts)])"

abbreviation
  itrans_subst ::
    "('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
where
  "itrans_subst \<sigma> \<equiv> (\<lambda>x. itrans (\<sigma> x))"


lemma itransI: "funas_term t \<subseteq> us \<Longrightarrow> t \<cdot> itrans_subst \<sigma> = itrans (t \<cdot> \<sigma>)"
  by (induct t, auto)

lemma itransII_main:
  "(itrans (t \<cdot> \<sigma>), t \<cdot> itrans_subst \<sigma>) \<in> (rstep (ce_trs cn))^*
  \<and> (funas_term t \<subseteq> us \<or> (itrans (t \<cdot> \<sigma>), t \<cdot> itrans_subst \<sigma>) \<in> (rstep (ce_trs cn))^+) " 
  (is "(itrans _,_) \<in> ?rel \<and> (_ \<or> _ \<in> ?Rel)  ")
proof (induct t)
  case (Var x) then show ?case by auto
next
  case (Fun f ts)
  let ?ts = "map (\<lambda> t. itrans (t \<cdot> \<sigma>)) ts"
  let ?ss = "map (\<lambda> t. t \<cdot> itrans_subst \<sigma>) ts"
  have len: "length ?ts = length ?ss" and other: "\<forall> i. i< length ?ts \<longrightarrow> (?ts ! i, ?ss ! i) \<in> ?rel" using Fun by auto
  have "(Fun f ?ts, Fun f ?ss) \<in> ?rel"
    by (rule all_ctxt_closedD[of UNIV], insert len other, auto)
  then have nearlyDone: "(Fun f ?ts, Fun f ts \<cdot> itrans_subst \<sigma>) \<in> ?rel" (is "(_,?ti) \<in> _") by auto
  show ?case
  proof (cases "(f,length ts) \<in> us")
    case False
    with Fun have id: "itrans (Fun f ts \<cdot> \<sigma>) = 
       (comb cn) [Fun f ?ts]" (is "?it = (comb cn) ?list") 
      by (simp add: o_def) 
    have "Fun f ?ts \<in> set ?list" by simp
    then have steps: "((comb cn) ?list, Fun f ?ts) \<in> (rstep (ce_trs cn))^+" (is "_ \<in> ?r^+") by (rule ce_trs_sound) 
    from nearlyDone steps have steps: "(itrans (Fun f ts \<cdot> \<sigma>), ?ti) \<in> ?r^+" unfolding id by auto
    show ?thesis using steps by auto
  next
    case True
    with Fun nearlyDone have part1: "(itrans (Fun f ts \<cdot> \<sigma>), Fun f ts \<cdot> itrans_subst \<sigma>) \<in> ?rel"
      by (simp add: o_def) 
    let ?fus = "funas_term (Fun f ts) \<subseteq> us"
    show ?thesis 
    proof (intro conjI, rule part1, unfold disj_commute[of ?fus], rule disjCI)
      assume not: "\<not> ?fus"
      with Fun True have id: "itrans (Fun f ts \<cdot> \<sigma>) = Fun f ?ts" by simp 
      from True not have "\<exists> t. t \<in> set ts \<and> \<not> funas_term t \<subseteq> us" by auto
      then obtain t where t: "t \<in> set ts" and tus: "\<not> funas_term t \<subseteq> us" by blast
      from t obtain i where i: "i < length ?ts" and ti: "t = ts ! i" by (simp only: set_conv_nth, auto)
      from Fun(1)[OF t] t ti tus have "(itrans (ts ! i \<cdot> \<sigma>), ts ! i \<cdot> itrans_subst \<sigma>) \<in> ?Rel" by auto   
      with i have ind: "(?ts ! i, ?ss ! i) \<in> ?Rel" by auto
      have "(Fun f ?ts, Fun f ?ss) \<in> ?Rel" 
        by (rule rtrancl_trancl_into_trancl[OF len other i ind ctxt_closed_rstep])
      with id show "(itrans (Fun f ts \<cdot> \<sigma>), Fun f ts \<cdot> itrans_subst \<sigma>) \<in> ?Rel" by auto
    qed
  qed
qed

lemma itransII: "(itrans (t \<cdot> \<sigma>), t \<cdot> itrans_subst \<sigma>) \<in> NS"
  "\<not> funas_term t \<subseteq> us \<Longrightarrow> (itrans (t \<cdot> \<sigma>), t \<cdot> itrans_subst \<sigma>) \<in> S"
proof -
  from itransII_main[of t \<sigma>] have "(itrans (t \<cdot> \<sigma>), t \<cdot> itrans_subst \<sigma>) \<in> (rstep (ce_trs cn))^*" by auto
  also have "(rstep (ce_trs cn))^* \<subseteq> NS^*"
    using ce_orient[OF m, folded cn] .
  also have "\<dots> = NS" by (rule rtrancl_NS)
  finally show "(itrans (t \<cdot> \<sigma>), t \<cdot> itrans_subst \<sigma>) \<in> NS" .
  assume "\<not> funas_term t \<subseteq> us"
  with itransII_main[of t \<sigma>] have "(itrans (t \<cdot> \<sigma>), t \<cdot> itrans_subst \<sigma>) \<in> (rstep (ce_trs cn))^+" by auto
  also have "(rstep (ce_trs cn))^+ \<subseteq> S^+" by (metis ce cn ctxt mono_ce trancl_mono_set)
  also have "\<dots> = S" 
    by (metis trancl_id trans_S)
  finally show "(itrans (t \<cdot> \<sigma>), t \<cdot> itrans_subst \<sigma>) \<in> S" .
qed

lemma itrans_step: fixes t u l r :: "('f,'v)term"
  assumes step: "(t, u) \<in> qrstep nfs Q (Rb \<inter> {(l,r)})"
  shows "(itrans t, itrans u) \<in> (NS \<union> S) \<inter>
    (if (l,r) \<in> SS then S else UNIV)"
proof -
  define strict where "strict = (if (l, r) \<in> SS then S else UNIV)"
  from step obtain C \<tau> where t: "t = C \<langle> l \<cdot> \<tau> \<rangle>" and u: "u = C \<langle> r \<cdot> \<tau> \<rangle>" 
    and lr: "(l,r) \<in> Rb" 
    and NF: "(\<forall>u\<lhd> l \<cdot> \<tau>. u \<in> NF_terms Q)" by auto
  let ?I = "itrans" let ?Is = "itrans_subst"
  show ?thesis unfolding u t strict_def[symmetric]
  proof (induct C)
    case (Hole)
    show ?case unfolding intp_actxt.simps
    proof -
      from itransI[OF Rb_us[OF lr]] have r: "?I (r \<cdot> \<tau>) = r \<cdot> ?Is \<tau>" ..
      from itransII(1)[of l \<tau>] have lNS: "(?I (l \<cdot> \<tau>), l \<cdot> ?Is \<tau>) \<in> NS" by auto
      from Rb lr have "(l,r) \<in> NS \<union> S" by auto
      from subst.closedD[OF subst_NSS this]
      have l_to_r: "(l \<cdot> ?Is \<tau>, r \<cdot> ?Is \<tau>) \<in> NS \<union> S" .
      from lNS r l_to_r have "(?I (l \<cdot> \<tau>), ?I (r \<cdot> \<tau>)) \<in> NS O (NS \<union> S)" by fastforce
      also have "NS O (NS \<union> S) \<subseteq> NS \<union> S" using compat_NS_S trans_NS_point by blast 
      finally have one: "(?I (l \<cdot> \<tau>), ?I (r \<cdot> \<tau>)) \<in> NS \<union> S" .
      show "(?I (l \<cdot> \<tau>), ?I (r \<cdot> \<tau>)) \<in> (NS \<union> S) \<inter> strict"
      proof (cases "(l,r) \<in> SS")
        case False
        with one show ?thesis unfolding strict_def by auto
      next
        case True
        then have "(?I (l \<cdot> \<tau>), ?I (r \<cdot> \<tau>)) \<in> S" unfolding SS_def
        proof
          assume "(l,r) \<in> S"
          from subst.closedD[OF subst_S this] have l_to_r: "(l \<cdot> ?Is \<tau>, r \<cdot> ?Is \<tau>) \<in> S" .
          from lNS r l_to_r compat_NS_S show ?thesis by fastforce
        next
          assume "(l, r) \<in> {lr. \<not> funas_term (fst lr) \<subseteq> us}"
          then have "\<not> funas_term l \<subseteq> us" by auto
          from itransII(2)[OF this] have "(?I (l \<cdot> \<tau>), l \<cdot> ?Is \<tau>) \<in> S" .
          with r l_to_r have "(?I (l \<cdot> \<tau>), ?I (r \<cdot> \<tau>)) \<in> S O (NS \<union> S)" by fastforce
          with compat_S_NS trans_S_point show ?thesis by auto
        qed
        then show ?thesis unfolding strict_def by auto
      qed
    qed
  next
    case (More f bef C aft)
    let ?C = "More f bef C aft"
    from More have rel: "(?I C\<langle>l \<cdot> \<tau>\<rangle>, ?I C\<langle>r \<cdot> \<tau>\<rangle>) \<in> (NS \<union> S) \<inter> strict" by auto
    let ?D = "More f (map ?I bef) Hole (map ?I aft)"
    let ?n = "Suc (length bef + length aft)"
    have "\<exists> D. \<forall> t. ?I (Fun f (bef @ t # aft)) = D \<langle>?I t\<rangle>"
    proof (cases "(f,?n) \<in> us")
      case True
      show ?thesis
        by (rule exI[of _ ?D], insert True, auto)
    next
      case False
      show ?thesis
        by (rule exI[of _ "More c [] ?D (comb (c, m) [] # replicate m (Var undefined))"], 
          insert False, simp, simp add: cn comb.simps)
    qed
    then obtain D where id2: "\<And> t. ?I (Fun f (bef @ t # aft)) = D \<langle>?I t\<rangle>" by auto
    show ?case unfolding intp_actxt.simps id2
    proof (rule ctxt.closedD[OF _ rel])
      show "ctxt.closed ((NS \<union> S) \<inter> strict)" using ctxt ctxt_NS unfolding strict_def 
      by (metis (lifting, mono_tags) inf_absorb2 inf_top_right mono_NSS sup.cobounded2)
    qed
  qed
qed


lemma itrans_steps: fixes t u :: "('f,'v)term"
  assumes steps: "(t, u) \<in> (qrstep nfs Q Rb)^*"
  shows "(itrans t, itrans u) \<in> NS \<union> S"
  using steps 
proof (induct)
  case base
  show ?case using refl_NS unfolding refl_on_def by auto
next
  case (step ts v)
  from step(3) have tts: "(itrans t, itrans ts) \<in> (NS \<union> S)"  .
  from step(2) obtain lr where rel: "(ts,v) \<in> qrstep nfs Q (Rb \<inter> {lr})" 
    unfolding qrstep_qrstep_r_p_s_conv 
    unfolding qrstep_r_p_s_def by blast
  obtain l r where lr: "lr = (l,r)" by force
  from itrans_step[OF rel[unfolded lr]] have  
    rel: "(itrans ts, itrans v) \<in> (NS \<union> S)" by auto  
  from tts rel have "(itrans t, itrans v) \<in> NS \<union> S"
    using compat_NS_S compat_S_NS trans_NS_point trans_S_point by blast
  with split show ?case by auto
qed
end

context R_Q_U_ecap
begin

lemma usable_rules_min_ichain_ce: assumes 
  precond: "usable_rules_precond (nfs,m,P,Pw,Q,Rs,Rw)"
  and redp: "mono_ce_af_redtriple_order S NS NST \<pi>"
  and or: "P \<union> Pw \<union> U \<subseteq> NS \<union> S"
  and min_chain: "min_ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>"
  and SS: "SS \<inter> (P \<union> Pw) \<subseteq> S \<union> {lr . \<not> funas_term (fst lr) \<subseteq> us}"
  and SR: "SR \<inter> U \<subseteq> S \<union> {lr . \<not> funas_term (fst lr) \<subseteq> us}"
  and us: "us = \<Union> (funas_term ` (snd ` (P \<union> Pw \<union> U)))"
  shows "\<exists> i. min_ichain (nfs,m,P - SS,Pw - SS,Q,Rs - SR, Rw - SR) (shift s i) (shift t i) (shift \<sigma> i)"
proof -  
  from usable_rules_precondE[OF precond] have R: "Rs \<union> Rw \<subseteq> R" and 
    vars: "\<And> l r. \<not> nfs \<Longrightarrow> (l,r) \<in> P \<union> Pw \<Longrightarrow> vars_term r \<subseteq> vars_term l" by blast+
  from min_chain have ichain: "ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>" unfolding min_ichain.simps by simp
  note ichain = ichain[unfolded ichain.simps]
  from ichain have inP: "\<And> i. (s i, t i) \<in> P \<union> Pw" by auto
  {
    from ichain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NFQ" by auto
    from ichain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
    {
      fix i x
      assume x: "x \<in> vars_term (t i)"
      have "\<sigma> i x \<in> NFQ"
      proof (cases nfs)
        case True
        from nfs[of i, unfolded NF_subst_def, rule_format, OF True] x
        show ?thesis unfolding vars_rule_def by auto
      next
        case False
        from vars[OF False inP, of i] x
        have "x \<in> vars_term (s i)" by auto
        then have "Var x \<unlhd> s i" by auto
        then have "Var x \<cdot> \<sigma> i \<unlhd> s i \<cdot> \<sigma> i" by (rule supteq_subst)
        from NF_subterm[OF NF this]
        show "\<sigma> i x \<in> NFQ" by simp
      qed
    } 
    then have "\<And> i. \<sigma> i ` vars_term (t i) \<subseteq> NFQ" by auto
  } note NFt = this
  interpret mono_ce_af_redtriple_order S NS NST \<pi> by fact
  from usable_rules_min_ichain[OF precond min_chain]
  have chain: "min_ichain (nfs, m, P, Pw, Q, Rs \<inter> U, Rw \<inter> U) s t \<sigma>" .
  show ?thesis
  proof (rule min_ichain_split[OF min_chain], rule)
    assume mchain: "min_ichain (nfs, m, SS \<inter> (P \<union> Pw), P \<union> Pw - SS, Q, SR \<inter> (Rs \<union> Rw), Rs \<union> Rw - SR) s t \<sigma>"
    have "min_ichain (nfs, m, SS \<inter> (P \<union> Pw), P \<union> Pw - SS, Q, SR \<inter> (Rs \<union> Rw) \<inter> U, (Rs \<union> Rw - SR) \<inter> U) s t \<sigma>"
      by (rule usable_rules_min_ichain[OF usable_rules_precond_mono[OF precond] mchain], auto)
    then have chain: "ichain (nfs, m, SS \<inter> (P \<union> Pw), P \<union> Pw - SS, Q, SR \<inter> (Rs \<union> Rw) \<inter> U, (Rs \<union> Rw - SR) \<inter> U) s t \<sigma>" by auto
    let ?Rs = "(SR \<union> S) \<inter> U \<inter> (Rs \<union> Rw)"
    let ?Rw = "NS \<inter> U \<inter> (Rs \<union> Rw)"
    let ?QRs = "qrstep nfs Q ?Rs"
    let ?QRw = "qrstep nfs Q (?Rs \<union> ?Rw)"
    let ?QRW = "qrstep nfs Q (U \<inter> (Rs \<union> Rw))"
    have QRW: "?QRw \<subseteq> ?QRW" by (rule qrstep_mono, auto)    
    have "ichain (nfs, m, (SS \<inter> NS) \<union> S, NS, Q, ?Rs, ?Rw) s t \<sigma>"
      by (rule ichain_mono[OF chain], insert or SS SR, auto)
    note chain = this[unfolded ichain.simps, simplified]
    from chain have P: "\<And> i. (s i, t i) \<in> NS \<union> S" by auto
    {
      fix i
      from chain have "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QRw^*" by auto
      also have "?QRw^* \<subseteq> ?QRW^*"
        by (rule rtrancl_mono[OF QRW])
      finally have "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QRW^*" .
    } note steps = this
    from chain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NFQ" by auto
    from ce_compatibleE[OF S_ce_compat] obtain k where 
      ce: "\<And> m. m \<ge> k \<Longrightarrow> ce_trs (c,m) \<subseteq> S" by metis
    define m where "m = max k n"
    have ce: "ce_trs (c,m) \<subseteq> S" unfolding m_def by (rule ce, auto)
    have mn: "m \<ge> n" unfolding m_def by auto
    have ori: "U \<inter> (Rs \<union> Rw) \<subseteq> NS \<union> S" using or by auto
    have NFQ: "NFQ \<subseteq> NF_trs (U \<inter> (Rs \<union> Rw))"
      by (rule subset_trans[OF NF_Q_R NF_anti_mono[OF rstep_mono]], insert R, auto)
    interpret ce_unusable_symbols S NS NST \<pi> us "U \<inter> (Rs \<union> Rw)" "(c,m)" m unfolding us
      by (unfold_locales, rule refl, rule ce, rule mn, rule ctxt_S, rule ori, auto)
    let ?I = "itrans"
    let ?I\<sigma> = "\<lambda> i x. ?I (\<sigma> i x)"
    let ?s = "\<lambda> i. ?I (s i \<cdot> \<sigma> i)"
    {
      fix i
      have "funas_term (t i) \<subseteq> us" unfolding us using inP[of i] by auto
      from itransI[OF this]
      have It: "?I (t i \<cdot> \<sigma> i) = t i \<cdot> ?I\<sigma> i" by simp
      from itrans_steps[OF steps] 
      have "(?I (t i \<cdot> \<sigma> i), ?I (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> NS \<union> S" by auto
      with It have ts: "(t i \<cdot> ?I\<sigma> i, ?I (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> NS \<union> S" by auto
      from itransII(1) have Iss: "(?I (s i \<cdot> \<sigma> i), s i \<cdot> ?I\<sigma> i) \<in> NS" .
      from inP[of i] or have st: "(s i, t i) \<in> NS \<union> S" by auto
      have st: "(s i \<cdot> ?I\<sigma> i, t i \<cdot> ?I\<sigma> i) \<in> NS \<union> S"
        by (rule subst.closedD[OF subst_NSS st])
      from st ts Iss have "(?s i, ?s (Suc i)) \<in> NS O (NS \<union> S) O (NS \<union> S)" by auto
      with S_O_S have NS: "(?s i, ?s (Suc i)) \<in> NS \<union> S" by (auto simp: order_simps)
      note Iss st ts It NS
    }
    note non_strict = this
    then have ns: "\<forall> i. (?s i, ?s (Suc i)) \<in> NS \<union> S" by auto
    from SN have "SN_on S {?s 0}" unfolding SN_def ..
    from non_strict_ending[OF ns compat_NS_S this] obtain j where ns: "\<And> i. i \<ge> j \<Longrightarrow> (?s i, ?s (Suc i)) \<notin> S" by auto
    from chain have "(INFM i. (s i, t i) \<in> (SS \<inter> NS) \<union> S) \<or> 
      (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QRw^* O ?QRs O ?QRw^*)" by auto
    from this[folded INFM_disj_distrib, unfolded INFM_nat_le, rule_format, of j]
      obtain i where i: "i \<ge> j" and disj: "(s i, t i) \<in> (SS \<inter> NS) \<union> S \<or> (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QRw^* O ?QRs O ?QRw^*" by blast
      define si si' ti ssi where
        "si = ?s i" and "si' = s i \<cdot> ?I\<sigma> i" and "ti \<equiv> t i \<cdot> ?I\<sigma> i" and "ssi = ?s (Suc i)"
    note d = si_def si'_def ti_def ssi_def
    note ns = ns[OF i, folded d]
    note non_strict = non_strict(1-4)[of i, folded d]
    from non_strict ns compat_S_NS compat_NS_S trans_S_point 
    have noS: "(si, si') \<notin> S" "(si', ti) \<notin> S" "(ti,ssi) \<notin> S" by blast+
    {
      assume "(s i, t i) \<in> SS \<union> S"
      with SS inP[of i] have "(s i, t i) \<in> S \<or> \<not> funas_term (s i) \<subseteq> us" by force
      then have False
      proof
        assume "(s i, t i) \<in> S"
        from subst.closedD[OF subst_S this, of "?I\<sigma> i", folded d] noS show False by auto
      next
        assume "\<not> funas_term (s i) \<subseteq> us"
        from itransII(2)[OF this, of "\<sigma> i", folded d] noS show False by auto
      qed
    }
    with disj have "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QRw^* O ?QRs O ?QRw^*" by auto
    also have "?QRw^* O ?QRs O ?QRw^* \<subseteq> ?QRW^* O ?QRs O ?QRW^*" using rtrancl_mono[OF QRW] by blast
    finally have strict: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QRW^* O ?QRs O ?QRW^*" .
    then obtain a b where 1: "(t i \<cdot> \<sigma> i, a) \<in> ?QRW^*" 
      and 2: "(a,b) \<in> ?QRs" 
      and 3: "(b, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QRW^*" by blast+
    from itrans_steps[OF 1, unfolded non_strict(4)] 
    have 1: "(ti, ?I a) \<in> NS \<union> S" .
    from 2 obtain lr where rel: "(a,b) \<in> qrstep nfs Q (U \<inter> (Rs \<union> Rw) \<inter> {lr})"
      and lr: "lr \<in> (SR \<union> S) \<inter> U"
      unfolding qrstep_qrstep_r_p_s_conv 
      unfolding qrstep_r_p_s_def by blast
    obtain l r where l_r: "lr = (l,r)" by force
    from lr l_r have SS: "(l,r) \<in> ce_unusable_symbols.SS S us" unfolding SS_def using SR by blast
    from itrans_step[OF rel[unfolded l_r]] SS
    have 2: "(?I a, ?I b) \<in> S" by auto
    from itrans_steps[OF 3, folded d]
    have 3: "(?I b, ssi) \<in> NS \<union> S" .
    from 1 2 3 have "(ti, ssi) \<in> (NS \<union> S) O S O (NS \<union> S)" by fast
    then have "(ti, ssi) \<in> S" using compat_NS_S compat_S_NS trans_S_point by blast
    with noS show False by auto
  qed
qed

lemma usable_rules_finite_dpp_ce: assumes 
  precond: "usable_rules_precond (nfs,m,P,Pw,Q,Rs,Rw)"
  and redp: "mono_ce_af_redtriple S NS NST \<pi>"
  and or: "P \<union> Pw \<union> U \<subseteq> NS \<union> S"
  and SS: "SS \<inter> (P \<union> Pw) \<subseteq> S \<union> {lr . \<not> funas_term (fst lr) \<subseteq> us}"
  and SR: "SR \<inter> U \<subseteq> S \<union> {lr . \<not> funas_term (fst lr) \<subseteq> us}"
  and us: "us = \<Union> (funas_term ` (snd ` (P \<union> Pw \<union> U)))"
  and fin: "finite_dpp (nfs,m,P - SS,Pw - SS,Q,Rs - SR,Rw - SR)"
  shows "finite_dpp (nfs,m,P,Pw,Q,Rs,Rw)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  from this[unfolded finite_dpp_def] obtain s t \<sigma>
    where chain: "min_ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>" by blast
  interpret mono_ce_af_redtriple S NS NST \<pi> by fact
  from mono_ce_af_redtriple_order have redp: "mono_ce_af_redtriple_order (S^+) (NS^*) (NST^*) \<pi>" .
  have "\<exists>i. min_ichain (nfs, m, P - SS, Pw - SS, Q, Rs - SR, Rw - SR) (shift s i) (shift t i) (shift \<sigma> i)"
    by (rule usable_rules_min_ichain_ce[OF precond redp subset_trans[OF or] chain subset_trans[OF SS] subset_trans[OF SR] us], auto)
  with fin show False unfolding finite_dpp_def by blast
qed
end

definition "usable_rules_approx Q R nfs U \<equiv> \<forall> \<sigma> ss t u v lr p \<tau>. 
  \<sigma> ` vars_term t \<subseteq> NF_terms Q 
  \<longrightarrow> set ss \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q
  \<longrightarrow> (t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)^* 
  \<longrightarrow> (u,v) \<in> qrstep_r_p_s nfs Q R lr p \<tau> 
  \<longrightarrow> lr \<in> U ss t"

lemma usable_rules_approxD: assumes U: "usable_rules_approx Q R nfs U"
  shows "\<sigma> ` vars_term t \<subseteq> NF_terms Q 
    \<Longrightarrow> set ss \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q
    \<Longrightarrow> (t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)^* 
    \<Longrightarrow> (u,v) \<in> qrstep_r_p_s nfs Q R lr' p \<tau> 
    \<Longrightarrow> lr' \<in> U ss t" 
  using U unfolding usable_rules_approx_def by metis

end
