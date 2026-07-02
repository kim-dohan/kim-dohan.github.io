(*
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory
  Critical_Pair_Closing_Systems
imports
  Parallel_Closed
begin

context fixes ren :: "'v :: infinite renaming2" 
begin
definition
  "critical_pair_closing' C R = ((\<forall> (b, p, q) \<in> critical_pairs ren R R. (p, q) \<in> (rstep C)\<^sup>\<down>) \<and>
    C \<subseteq> { (l \<cdot> \<sigma>, r \<cdot> \<sigma>) | \<sigma> l r. (l, r) \<in> R \<and> (\<forall> x. \<sigma> x \<noteq> Var x \<longrightarrow> (\<sigma> x) \<in> NF R \<and> ground (\<sigma> x))})"

definition
  "critical_pair_closing C R = ((\<forall> (b, p, q) \<in> critical_pairs ren R R. (p, q) \<in> (rstep C)\<^sup>\<down>) \<and> C \<subseteq> R)"

lemma cpcs_sn_cr:
  assumes "critical_pair_closing S R"
     and "SN (rstep S)"
  shows "CR (rstep S)"
proof -
  from assms have "\<forall> (b, p, q) \<in> critical_pairs ren S S. (p, q) \<in> (rstep S)\<^sup>\<down>"
    using critical_pairs_mono unfolding critical_pair_closing_def by blast
  with critical_pair_lemma have "WCR (rstep S)" by auto
  with Newman assms show ?thesis by auto
qed

lemma cpcs_sn:
  assumes "critical_pair_closing S R"
    and "SN (rstep S)"
    and left_lin: "left_linear_trs R"
    and closed:"\<And>p q. (False, q, p) \<in> critical_pairs ren R R \<Longrightarrow> \<exists>v. (q, v) \<in> par_rstep S \<and> (p, v) \<in> (rstep S)\<^sup>*"
  shows "CR (rstep R)"
proof -
  have SR: "S \<subseteq> R" using assms(1)[unfolded critical_pair_closing_def] by auto
  with left_lin have left_lin :"left_linear_trs R" "left_linear_trs S" unfolding left_linear_trs_def by auto
  have overlay_closed: "\<And>p q. (True, p, q) \<in> critical_pairs ren R R \<Longrightarrow> \<exists>w. (p, w) \<in> (rstep S)\<^sup>* \<and> (q, w) \<in> (rstep S)\<^sup>*"
    using assms(1)[unfolded critical_pair_closing_def, THEN conjunct1] by auto
  let ?pR = "par_rstep R"
  let ?pS = "par_rstep S"
  { fix s t u
    assume "(s, t) \<in> ?pR" and "(s, u) \<in> ?pR"
    with par_rstep_par_rstep_mctxt_conv obtain C infos and D infos'
      where "(s, t) \<in> par_rstep_mctxt R C infos" and "(s, u) \<in> par_rstep_mctxt R D infos'"
      by metis
    then have "\<exists>v w c. (t, v) \<in> (rstep S)\<^sup>* \<and> (v, c) \<in> ?pR \<and> (u, w) \<in> (rstep S)\<^sup>* \<and> (w, c) \<in> ?pR"
    proof (induct "overlap' (C, par_lefts infos) (D, par_lefts infos')" arbitrary: C D infos infos' s t u rule: wf_induct_rule[OF wf_mult[OF SN_imp_wf[OF SN_supt]]])
      case (1 C D infos infos' s t u)
      then show ?case
      proof (induct s arbitrary: C D infos infos' t u)
        case (Var x)
        from par_rstep_mctxt_Var_diamond[OF Var(2) Var(3)] left_lin show ?case by blast
      next
        case (Fun f ss')
        let ?ss = "par_lefts infos" 
        let ?ts = "par_rights infos" 
        let ?vs = "par_lefts infos'" 
        let ?us = "par_rights infos'" 
        from Fun have s: "Fun f ss' =\<^sub>f (C, ?ss)" and t: "t =\<^sub>f (C , ?ts)"
          and s2: "Fun f ss' =\<^sub>f (D, ?vs)" and u:"u =\<^sub>f (D, ?us)"
          and par_conds1: "par_conds R infos" 
          and par_conds2: "par_conds R infos'" 
          unfolding par_rstep_mctxt_def by auto
        from par_conds_imp_rrstep[OF par_conds1]
        have steps1: "\<forall>i<length ?ss. (?ss ! i, ?ts ! i) \<in> rrstep R" by auto
        from par_conds_imp_rrstep[OF par_conds2]
        have steps2: "\<forall>i<length ?vs. (?vs ! i, ?us ! i) \<in> rrstep R" by auto
        show ?case
        proof (cases C)
          case MHole
          then have ss:"?ss = [Fun f ss']" using s by (auto elim: eqf_MHoleE)
          moreover have "?ts = [t]" using t MHole by (auto elim: eqf_MHoleE)
          ultimately have "(Fun f ss', t) \<in> rrstep R" using steps1 by auto
          then obtain l r \<sigma> where lr: "(l, r) \<in> R" and l:"Fun f ss' = l \<cdot> \<sigma>" and r:" t = r \<cdot> \<sigma> "
            using rrstep_imp_rule_subst by fastforce
          from lr left_lin have linl:"linear_term l" by (auto simp: left_linear_trs_def)
          show ?thesis
          proof (cases D)
            case (MFun g Ds)
            then have [simp]: "g = f" using s2 by (auto dest: eqfE)
            obtain vss where lDs:"length ss' = length Ds" and lvss:"length vss = length Ds"
              and vss:"?vs = concat vss" and vs'iD:"\<And> i. i < length Ds \<Longrightarrow> ss' ! i =\<^sub>f (Ds ! i, vss ! i)"
              using MFun s2 by (auto elim: eqf_MFunE)
            from u MFun obtain us' where [simp]: "u = Fun f us'" by (auto elim: eqf_MFunE)
            obtain uss where lDs2:"length us' = length Ds" and luss:"length uss = length Ds"
              and uss:"?us = concat uss" and us'iD:"\<And> i. i < length Ds \<Longrightarrow> us' ! i =\<^sub>f (Ds ! i, uss ! i)"
              using MFun u by (auto elim: eqf_MFunE)
            { fix i
              assume i:"i < length vss"
              then have "ss' ! i =\<^sub>f (Ds ! i, vss ! i)" using lvss vs'iD by auto
              moreover have "us' ! i =\<^sub>f (Ds ! i, uss ! i)" using luss us'iD i lvss by auto
              ultimately have "length (vss ! i) = length (uss ! i)"  by (auto dest!: eqfE)
            } note lvssuss = this
            from par_rstep_mctxt_linear_subst[OF linl Fun(4)[unfolded l]]
            obtain \<tau> where \<tau>:"u = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR) \<or>
            (\<exists>E s' l' r' j D'. l = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
              \<and> hole_pos E \<in> hole_poss D \<and> j < length infos'
              \<and> (E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs) \<and> u =\<^sub>f (D', remove_nth j ?us))"
              by blast
            then show ?thesis
            proof
              assume "u = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR)"
              with step_in_subst_imp_par_diamond r lr show ?thesis using par_rstep_rsteps by fastforce
            next
              assume "\<exists>E s' l' r' j D'. l = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
                \<and> hole_pos E \<in> hole_poss D \<and> j < length infos'
                \<and> (E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs) \<and> u =\<^sub>f (D', remove_nth j ?us)"
              then obtain E l'' l' r' j D' where E:"l = E\<langle>l''\<rangle>" and l'':"is_Fun l''" and lr':"(l', r') \<in> R"
                and unifiable:"l'' \<cdot> \<sigma> = l' \<cdot> \<tau>" and hpos:"hole_pos E \<in> hole_poss D" and j:"j < length infos'"
                and E\<sigma>r:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs)"
                and uD:"u =\<^sub>f (D', remove_nth j ?us)"
                by auto
              obtain \<mu>1 \<mu>2 \<delta> where mgu:"mgu_vd ren l'' l' = Some (\<mu>1, \<mu>2)"
                and \<sigma>:"\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" and \<tau>:"\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" and \<mu>:"l'' \<cdot> \<mu>1 = l' \<cdot> \<mu>2"
                using mgu_vd_complete[OF unifiable, of ren] by auto
              have inner:"hole_pos E \<noteq> []" using hpos MFun by auto
              have "(False, (E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, r \<cdot> \<mu>1) \<in> critical_pairs ren R R"
                using lr lr' E l'' mgu inner by (force intro: critical_pairsI)
              from closed[rule_format,OF this] obtain v
                where v:"((E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, v) \<in> par_rstep S" "(r \<cdot> \<mu>1, v) \<in> (rstep S)\<^sup>*" by auto
              then have closed1:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep S" unfolding \<sigma> \<tau>
                using subst_closed_par_rstep by fastforce
              from v have closed2: "(r \<cdot> \<sigma>, v \<cdot> \<delta>) \<in> (rstep S)\<^sup>*" unfolding \<sigma> \<tau> using rsteps_closed_subst by auto
              from par_rstep_mctxtE[OF closed1] obtain F infos3 where EF:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (F, par_lefts infos3)" 
                and "v \<cdot> \<delta> =\<^sub>f (F, par_rights infos3)"
                and "par_conds S infos3" by auto
              then have Er: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt S F infos3"
                unfolding par_rstep_mctxt_def by auto
              then have ErR: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt R F infos3"
                using SR unfolding par_rstep_mctxt_def by (auto simp: par_cond_def)
              let ?cs = "par_lefts infos3" 
              let ?ol' = "overlap' (F, ?cs) (D', remove_nth j ?vs)"
              have "(?ol', mset (remove_nth j ?vs)) \<in> (mult {\<lhd>})\<^sup>="
                using overlap'_bounded[OF E\<sigma>r EF] overlap'_symmetric[OF EF E\<sigma>r] by auto
              moreover have "(mset (remove_nth j ?vs), mset ?vs) \<in> mult {\<lhd>}"
                using remove_nth_mult[of j] j by (metis length_map)
              moreover have "overlap' (C, ?ss) (D, ?vs) = mset ?vs" using MFun MHole ss by auto
              ultimately have ol:"(?ol', overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}"
                unfolding mult_def by simp

              have "set (remove_nth j infos') \<subseteq> set infos'" unfolding remove_nth_def
                by (simp add: set_drop_subset set_take_subset)
              hence "par_conds R (remove_nth j infos')" using par_conds2 by auto 
              from E\<sigma>r uD this have Eu:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, u) \<in> par_rstep_mctxt R D' (remove_nth j infos')"
                unfolding par_rstep_mctxt_def using j by (auto simp: remove_map)
              from Fun(2)[OF ol[unfolded remove_map[OF j]] ErR Eu] closed2 show ?thesis using r rtrancl_trans by metis
            qed
          next
            case MHole
            then have "?vs = [Fun f ss']" using s2 by (auto elim: eqf_MHoleE)
            moreover have "?us = [u]" using u MHole by (auto elim: eqf_MHoleE)
            ultimately have "(Fun f ss', u) \<in> rrstep R" using steps2 by auto
            then obtain l' r' \<sigma>' where lr': "(l', r') \<in> R" and l':"Fun f ss' = l' \<cdot> \<sigma>'"
              and r':" u = r' \<cdot> \<sigma>'"
              using rrstep_imp_rule_subst by fastforce
            with l have eq:"l' \<cdot> \<sigma>' = l \<cdot> \<sigma>" by auto
            from lr' left_lin have "linear_term l'" by (auto simp: left_linear_trs_def)
            from par_rstep_mctxt_linear_subst[OF this Fun(3)[unfolded l']]
            obtain \<tau> where \<tau>:"t = l' \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l'. (\<sigma>' x, \<tau> x) \<in> par_rstep R) \<or>
              (\<exists>E s'. l' = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> hole_pos E \<in> hole_poss C)"
              by blast
            then show ?thesis
            proof
              assume "t = l' \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l'. (\<sigma>' x, \<tau> x) \<in> par_rstep R)"
              with step_in_subst_imp_par_diamond r' lr' show ?thesis using par_rstep_rsteps by fastforce
            next
              assume "\<exists>E s'. l' = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> hole_pos E \<in> hole_poss C"
              then obtain E s' where "l' = E\<langle>s'\<rangle>" and "is_Fun s'" and "hole_pos E \<in> hole_poss C" by blast
              with \<open>C = MHole\<close> have isFun:"is_Fun l'" by (cases E) auto
              from mgu_vd_complete[OF eq, of ren] obtain \<mu>1 \<mu>2 \<delta>
                where unif:"mgu_vd ren l' l = Some (\<mu>1, \<mu>2)"
                  and \<sigma>:"\<sigma>' = \<mu>1 \<circ>\<^sub>s \<delta>" and \<sigma>':"\<sigma> = \<mu>2 \<circ>\<^sub>s \<delta>"
                by auto
              from critical_pairsI[OF lr' lr _ _ unif] isFun
              have "(True, r \<cdot> \<mu>2, r' \<cdot> \<mu>1) \<in> critical_pairs ren R R" by force
              with overlay_closed obtain w
                where "(r \<cdot> \<mu>2, w) \<in> (rstep S)\<^sup>*" and "(r' \<cdot> \<mu>1, w) \<in> (rstep S)\<^sup>*" by auto
              with \<sigma> \<sigma>' have "(r \<cdot> \<sigma>, w \<cdot> \<delta>) \<in> (rstep S)\<^sup>*" "(r' \<cdot> \<sigma>', w \<cdot> \<delta>) \<in> (rstep S)\<^sup>*"
                by (auto simp: rsteps_closed_subst)
              with r r' show ?thesis using par_rsteps_rsteps by auto
            qed
          qed (insert s2, auto dest: eqfE)
        next
          case (MFun g Cs)
          note C = this
          then have [simp]: "g = f" using s by (auto dest: eqfE)
          define Infos where "Infos = partition_holes infos Cs" 
          from eqfE[OF s, unfolded C, simplified]  
          have len_infos: "sum_list (map num_holes Cs) = length infos" 
            and ss'_id: "ss' = map (\<lambda>i. fill_holes (Cs ! i) (par_lefts (Infos ! i))) [0..<length Cs]" 
            and len_Infos: "length Infos = length Cs" 
            and infos: "infos = concat Infos" 
            and len_Csi: "\<And> i. i < length Cs \<Longrightarrow> num_holes (Cs ! i) = length (Infos ! i)" 
            by (auto simp: Infos_def)
          define sss where "sss = map par_lefts Infos" 
          have lCs:"length ss' = length Cs" and lsss:"length sss = length Cs"
            and sss:"?ss = concat sss" and ss'iC:"\<And> i. i < length Cs \<Longrightarrow> ss' ! i =\<^sub>f (Cs ! i, sss ! i)"
            unfolding ss'_id sss_def using len_infos len_Infos infos by (auto simp: map_concat len_Csi)
          from s have "Fun f ss' = fill_holes C ?ss" "num_holes C = length ?ss" by (auto dest: eqfE)
          define tss where "tss = map par_rights Infos" 
          from t C obtain ts' where [simp]: "t = Fun f ts'" by (auto elim: eqf_MFunE)
          from eqfE[OF t[unfolded C this], simplified]
          have ts'_id: "ts' = map (\<lambda>i. fill_holes (Cs ! i) (par_rights (Infos ! i))) [0..<length Cs]" 
            by (auto simp: Infos_def)
          have lCs2:"length ts' = length Cs" and ltss:"length tss = length Cs"
            and tss:"?ts = concat tss" and ts'iC:"\<And> i. i < length Cs \<Longrightarrow> ts' ! i =\<^sub>f (Cs ! i, tss ! i)"
            unfolding ts'_id tss_def using len_infos len_Infos infos by (auto simp: map_concat len_Csi)
          show ?thesis
          proof (cases D)
            case MHole
            then have vs:"?vs = [Fun f ss']" using s2 by (auto elim: eqf_MHoleE)
            moreover have "?us = [u]" using u MHole by (auto elim: eqf_MHoleE)
            ultimately have "(Fun f ss', u) \<in> rrstep R" using steps2 by auto
            then obtain l r \<sigma> where lr: "(l, r) \<in> R" and l:"Fun f ss' = l \<cdot> \<sigma>" and r: "u = r \<cdot> \<sigma>"
              using rrstep_imp_rule_subst by fastforce
            from lr left_lin have "linear_term l" by (auto simp: left_linear_trs_def)
            from par_rstep_mctxt_linear_subst[OF this Fun(3)[unfolded l]]
            obtain \<tau> where \<tau>:"t = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR) \<or>
              (\<exists>D s' l' r' j C'. l = D\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
                \<and> hole_pos D \<in> hole_poss C \<and> j < length infos
                \<and> (D \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss) \<and> t =\<^sub>f (C', remove_nth j ?ts))"
              by blast
            then show ?thesis
            proof
              assume *:"t = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR)"
              with step_in_subst_imp_par_diamond r lr show ?thesis using par_rstep_rsteps by fastforce
            next
              assume "\<exists>D s' l' r' j C'. l = D\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
                \<and> hole_pos D \<in> hole_poss C \<and> j < length infos
                \<and> (D \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss) \<and> t =\<^sub>f (C', remove_nth j ?ts)"
              then obtain E l'' l' r' j C' where E:"l = E\<langle>l''\<rangle>" and l'':"is_Fun l''" and lr':"(l', r') \<in> R"
                and unifiable:"l'' \<cdot> \<sigma> = l' \<cdot> \<tau>" and hpos:"hole_pos E \<in> hole_poss C" and j:"j < length infos"
                and E\<sigma>r:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss)" and tCtsj:"t =\<^sub>f (C', remove_nth j ?ts)"
                by auto
              obtain \<mu>1 \<mu>2 \<delta> where mgu:"mgu_vd ren l'' l' = Some (\<mu>1, \<mu>2)"
                and \<sigma>:"\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" and \<tau>:"\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" and \<mu>:"l'' \<cdot> \<mu>1 = l' \<cdot> \<mu>2"
                using mgu_vd_complete[OF unifiable, of ren] by auto
              have inner:"hole_pos E \<noteq> []" using hpos C by auto
              have "(False, (E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, r \<cdot> \<mu>1) \<in> critical_pairs ren R R"
                using lr lr' E l'' mgu inner by (force intro: critical_pairsI)
              from closed[rule_format,OF this] obtain v
                where v: "((E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, v) \<in> par_rstep S" "(r \<cdot> \<mu>1, v) \<in> (rstep S)\<^sup>*" by auto
              then have closed1: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep S" unfolding \<sigma> \<tau>
                using subst_closed_par_rstep by fastforce
              from v have closed2: "(r \<cdot> \<sigma>, v \<cdot> \<delta>) \<in> (rstep S)\<^sup>*" unfolding \<sigma> \<tau> using rsteps_closed_subst by auto

              from par_rstep_mctxtE[OF closed1] obtain F infos3 where EF:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (F, par_lefts infos3)" and 
                "v \<cdot> \<delta> =\<^sub>f (F, par_rights infos3)"
                and "par_conds S infos3" by auto
              then have Ev:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt S F infos3"
                unfolding par_rstep_mctxt_def by auto

              then have EvR: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt R F infos3"
                using SR unfolding par_rstep_mctxt_def par_cond_def by fastforce
              let ?cs = "par_lefts infos3" 
              let ?ol' = "overlap' (C', remove_nth j ?ss) (F, ?cs)"
              have "(?ol', mset (remove_nth j ?ss)) \<in> (mult {\<lhd>})\<^sup>=" using overlap'_bounded[OF E\<sigma>r EF] by auto
              moreover have "(mset (remove_nth j ?ss), mset ?ss) \<in> mult {\<lhd>}" using remove_nth_mult j
                by (metis length_map)
              moreover have "overlap' (C, ?ss) (D, ?vs) = mset ?ss" using C MHole vs by auto
              ultimately have ol:"(?ol', overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}" unfolding mult_def by simp
              have "set (remove_nth j infos) \<subseteq> set infos" unfolding remove_nth_def
                by (simp add: set_drop_subset set_take_subset)
              hence "par_conds R (remove_nth j infos)" using par_conds1 by auto 

              from E\<sigma>r tCtsj this
              have Et:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, t) \<in> par_rstep_mctxt R C' (remove_nth j infos)"
                unfolding par_rstep_mctxt_def using j by (auto simp: remove_map)
              from Fun(2)[OF ol[unfolded remove_map[OF j]] Et EvR] show ?thesis by (metis closed2 r rtrancl_trans)
            qed
          next
            case (MFun h Ds) note D = this
            then have [simp]: "h = f" using s2 by (auto dest: eqfE)
            define Infos' where "Infos' = partition_holes infos' Ds" 
            from eqfE[OF s2, unfolded D, simplified]  
            have len_infos': "sum_list (map num_holes Ds) = length infos'" 
              and ss'_id': "ss' = map (\<lambda>i. fill_holes (Ds ! i) (par_lefts (Infos' ! i))) [0..<length Ds]" 
              and len_Infos': "length Infos' = length Ds" 
              and infos': "infos' = concat Infos'" 
              and len_Dsi: "\<And> i. i < length Ds \<Longrightarrow> num_holes (Ds ! i) = length (Infos' ! i)" 
              by (auto simp: Infos'_def)
            define vss where "vss = map par_lefts Infos'" 
            have lDs:"length ss' = length Ds" and lvss:"length vss = length Ds"
              and vss:"?vs = concat vss" and vs'iD:"\<And> i. i < length Ds \<Longrightarrow> ss' ! i =\<^sub>f (Ds ! i, vss ! i)"
              unfolding ss'_id' vss_def using len_infos' len_Infos' infos' by (auto simp: map_concat len_Dsi)
            from s2 have "Fun f ss' = fill_holes D ?vs" "num_holes D = length ?vs" by (auto dest: eqfE)
            define uss where "uss = map par_rights Infos'" 
            from u D obtain us' where [simp]: "u = Fun f us'" by (auto elim: eqf_MFunE)
            from eqfE[OF u[unfolded D this], simplified]
            have us'_id: "us' = map (\<lambda>i. fill_holes (Ds ! i) (par_rights (Infos' ! i))) [0..<length Ds]" 
              by (auto simp: Infos'_def)
            have lDs2:"length us' = length Ds" and luss:"length uss = length Ds"
              and uss:"?us = concat uss" and us'iD:"\<And> i. i < length Ds \<Longrightarrow> us' ! i =\<^sub>f (Ds ! i, uss ! i)"
              unfolding us'_id uss_def using len_infos' len_Infos' infos' by (auto simp: map_concat len_Dsi)

            { fix i
              assume i:"i < length ss'"
              then have s: "ss' ! i \<in> set ss'" using nth_mem by blast
              from i ts'iC lCs lCs2 have ts'i:"ts' ! i =\<^sub>f (Cs ! i, tss ! i)" by auto
              from i us'iD lDs lDs2 have us'i:"us' ! i =\<^sub>f (Ds ! i, uss ! i)" by auto
              have "sss ! i = partition_holes ?ss Cs ! i"
                by (metis eqfE(2) lsss partition_holes_concat_id ss'iC sss)
              moreover have " vss ! i = partition_holes ?vs Ds ! i"
                by (metis eqfE(2) lvss partition_holes_concat_id vs'iD vss)
              ultimately have "overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i) \<in>#
              mset (map (\<lambda>i. overlap' (Cs ! i, partition_holes ?ss Cs ! i) (Ds ! i, partition_holes ?vs Ds ! i)) [0..<length Cs])"
                unfolding sss vss using i lCs by fastforce
              then have ol:"overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i) \<subseteq># overlap' (C, ?ss) (D, ?vs)"
                unfolding C MFun by (simp add: in_mset_subset_Union)
              { fix C' D' s' t' u' infos2 infos2'
                assume 1:"(overlap' (C', par_lefts infos2) (D', par_lefts infos2'), overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i)) \<in> mult {\<lhd>}"
                  and 2: "(s', t') \<in> par_rstep_mctxt R C' infos2" "(s', u') \<in> par_rstep_mctxt R D' infos2'"
                have "trans {\<lhd>}" unfolding trans_def using supt_trans by auto
                with mult_subset_mult ol 1 have "(overlap' (C', par_lefts infos2) (D', par_lefts infos2'), overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}" by blast
                from Fun(2)[OF this 2] have "\<exists>v w c. (t', v) \<in> (rstep S)\<^sup>* \<and> (v, c) \<in> ?pR \<and> (u', w) \<in> (rstep S)\<^sup>* \<and> (w, c) \<in> ?pR" .
              } note m = this

              from i have iI: "i < length Infos" using len_Infos lCs by auto
              have "Ball (set Infos) (par_conds R)" using par_conds1 unfolding infos by auto
              with iI have parR1: "par_conds R (Infos ! i)" by auto
              have id: "par_lefts (Infos ! i) = map par_lefts Infos ! i \<and> par_rights (Infos ! i) = map par_rights Infos ! i"
                using iI by auto 
              with ss'iC i lCs ts'i parR1
              have ssts:"(ss' ! i, ts' ! i) \<in> par_rstep_mctxt R (Cs ! i) (Infos ! i)"
                by (intro par_rstep_mctxtI, auto simp: tss_def sss_def)

              from i have iI': "i < length Infos'" using len_Infos' lDs by auto
              have "Ball (set Infos') (par_conds R)" using par_conds2 unfolding infos' by auto
              with iI' have parR2: "par_conds R (Infos' ! i)" by auto
              have id': "par_lefts (Infos' ! i) = map par_lefts Infos' ! i \<and> par_rights (Infos' ! i) = map par_rights Infos' ! i"
                using iI' by auto 
              with vs'iD i lDs us'i parR2
              have ssus:"(ss' ! i, us' ! i) \<in> par_rstep_mctxt R (Ds ! i) (Infos' ! i)"
                by (intro par_rstep_mctxtI, auto simp: uss_def vss_def) 

              have "\<exists>v w c. (ts' ! i, v) \<in> (rstep S)\<^sup>* \<and> (v, c) \<in> ?pR \<and>
                (us' ! i, w) \<in> (rstep S)\<^sup>* \<and> (w, c) \<in> ?pR" 
                by (rule Fun(1)[OF s _ ssts ssus], rule m, insert id id', auto simp: vss_def sss_def)
            }
            then obtain v w c
              where vwc: "\<And>i. i < length ts' \<Longrightarrow> (ts' ! i, v i) \<in> (rstep S)\<^sup>* \<and> (v i, c i) \<in> ?pR \<and>
                (us' ! i, w i) \<in> (rstep S)\<^sup>* \<and> (w i, c i) \<in> ?pR"
              using lCs lCs2 by metis
            let ?vs' = "map v [0..<length ts']"
            let ?ws' = "map w [0..<length us']"
            let ?cs' = "map c [0..<length ts']"
            from vwc have *:"\<And>i. i < length ts' \<Longrightarrow> (ts' ! i, v i) \<in> (rstep S)\<^sup>*" by auto
            have "length ts' = length ?vs'" by auto
            from * args_rsteps_imp_rsteps[OF this] have v:"(Fun f ts', Fun f ?vs') \<in> (rstep S)\<^sup>*" by auto
            from vwc have *:"\<And>i. i < length us' \<Longrightarrow> (us' ! i, w i) \<in> (rstep S)\<^sup>*"
              using par_rsteps_rsteps lCs lCs2 lDs lDs2  by auto
            have "length us' = length ?ws'" by auto
            from * args_rsteps_imp_rsteps[OF this] have w:"(Fun f us', Fun f ?ws') \<in> (rstep S)\<^sup>*"
              by auto
            from vwc have c1:"(Fun f ?vs', Fun f ?cs') \<in> ?pR" by auto
            have "length ?ws' = length ?cs'" using lCs lCs2 lDs lDs2  by auto
            with vwc have c2:"(Fun f ?ws', Fun f ?cs') \<in> ?pR" by auto
            from v w c1 c2 show ?thesis by auto
          qed (insert s2, auto dest: eqfE)
        qed  (insert s, auto dest: eqfE)
      qed
    qed
  } note b = this
  { fix s t u
    assume "(s, t) \<in> rstep S"
      and "(s, u) \<in> par_rstep R"
    then have "(s, t) \<in> ?pS" and "(s, u) \<in> ?pR" using rstep_par_rstep by auto
    with par_rstep_par_rstep_mctxt_conv obtain C infos and D infos'
      where "(s, t) \<in> par_rstep_mctxt S C infos" and "(s, u) \<in> par_rstep_mctxt R D infos'"
      by metis
    then have "\<exists>v w. (t, v) \<in> (rstep S)\<^sup>* \<and> (v, w) \<in> par_rstep R \<and> (u, w) \<in> (rstep S)\<^sup>*"
    proof (induct "overlap' (C, par_lefts infos) (D, par_lefts infos')" arbitrary: C D infos infos' s t u rule: wf_induct_rule[OF wf_mult[OF SN_imp_wf[OF SN_supt]]])
      case (1 C D infos infos' s t u)
      then show ?case
      proof (induct s arbitrary: C D infos infos' t u)
        case (Var x)
        from par_rstep_mctxt_Var_diamond[OF Var(2) Var(3)] left_lin par_rstep_rsteps show ?case by blast
      next
        case (Fun f ss')
        let ?ss = "par_lefts infos" 
        let ?ts = "par_rights infos" 
        let ?vs = "par_lefts infos'" 
        let ?us = "par_rights infos'" 
        from Fun have s: "Fun f ss' =\<^sub>f (C, ?ss)" and t: "t =\<^sub>f (C , ?ts)"
          and s2: "Fun f ss' =\<^sub>f (D, ?vs)" and u:"u =\<^sub>f (D, ?us)"
          and par_conds1: "par_conds S infos" 
          and par_conds2: "par_conds R infos'" 
          unfolding par_rstep_mctxt_def by auto
        from par_conds_imp_rrstep[OF par_conds1]
        have steps1: "\<forall>i<length ?ss. (?ss ! i, ?ts ! i) \<in> rrstep S" by auto
        from par_conds_imp_rrstep[OF par_conds2]
        have steps2: "\<forall>i<length ?vs. (?vs ! i, ?us ! i) \<in> rrstep R" by auto
        show ?case
        proof (cases C)
          case MHole
          then have ss:"?ss = [Fun f ss']" using s by (auto elim: eqf_MHoleE)
          moreover have "?ts = [t]" using t MHole by (auto elim: eqf_MHoleE)
          ultimately have "(Fun f ss', t) \<in> rrstep S" using steps1 by auto
          then obtain l r \<sigma> where lr: "(l, r) \<in> S" and l:"Fun f ss' = l \<cdot> \<sigma>" and r:" t = r \<cdot> \<sigma> "
            using rrstep_imp_rule_subst by fastforce
          from lr left_lin have linl:"linear_term l" by (auto simp: left_linear_trs_def)
          show ?thesis
          proof (cases D)
            case (MFun g Ds) note D = this
            then have [simp]: "g = f" using s2 by (auto dest: eqfE)
            define Infos' where "Infos' = partition_holes infos' Ds" 
            from eqfE[OF s2, unfolded D, simplified]  
            have len_infos': "sum_list (map num_holes Ds) = length infos'" 
              and ss'_id': "ss' = map (\<lambda>i. fill_holes (Ds ! i) (par_lefts (Infos' ! i))) [0..<length Ds]" 
              and len_Infos': "length Infos' = length Ds" 
              and infos': "infos' = concat Infos'" 
              and len_Dsi: "\<And> i. i < length Ds \<Longrightarrow> num_holes (Ds ! i) = length (Infos' ! i)" 
              by (auto simp: Infos'_def)
            define vss where "vss = map par_lefts Infos'" 
            have lDs:"length ss' = length Ds" and lvss:"length vss = length Ds"
              and vss:"?vs = concat vss" and vs'iD:"\<And> i. i < length Ds \<Longrightarrow> ss' ! i =\<^sub>f (Ds ! i, vss ! i)"
              unfolding ss'_id' vss_def using len_infos' len_Infos' infos' by (auto simp: map_concat len_Dsi)
            from s2 have "Fun f ss' = fill_holes D ?vs" "num_holes D = length ?vs" by (auto dest: eqfE)
            define uss where "uss = map par_rights Infos'" 
            from u D obtain us' where [simp]: "u = Fun f us'" by (auto elim: eqf_MFunE)
            from eqfE[OF u[unfolded D this], simplified]
            have us'_id: "us' = map (\<lambda>i. fill_holes (Ds ! i) (par_rights (Infos' ! i))) [0..<length Ds]" 
              by (auto simp: Infos'_def)
            have lDs2:"length us' = length Ds" and luss:"length uss = length Ds"
              and uss:"?us = concat uss" and us'iD:"\<And> i. i < length Ds \<Longrightarrow> us' ! i =\<^sub>f (Ds ! i, uss ! i)"
              unfolding us'_id uss_def using len_infos' len_Infos' infos' by (auto simp: map_concat len_Dsi)

            from par_rstep_mctxt_linear_subst[OF linl Fun(4)[unfolded l]]
            obtain \<tau> where \<tau>:"u = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR) \<or>
              (\<exists>E s' l' r' j D'. l = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
                \<and> hole_pos E \<in> hole_poss D \<and> j < length infos'
                \<and> (E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs) \<and> u =\<^sub>f (D', remove_nth j ?us))"
              by blast
            then show ?thesis
            proof
              assume "u = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR)"
              with step_in_subst_imp_par_diamond r lr show ?thesis using par_rstep_rsteps by fastforce
            next
              assume "\<exists>E s' l' r' j D'. l = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
                \<and> hole_pos E \<in> hole_poss D \<and> j < length infos'
                \<and> (E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs) \<and> u =\<^sub>f (D', remove_nth j ?us)"
              then obtain E l'' l' r' j D' where E:"l = E\<langle>l''\<rangle>" and l'':"is_Fun l''" and lr':"(l', r') \<in> R"
                and unifiable:"l'' \<cdot> \<sigma> = l' \<cdot> \<tau>" and hpos:"hole_pos E \<in> hole_poss D" and j:"j < length infos'"
                and E\<sigma>r:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs)"
                and uD:"u =\<^sub>f (D', remove_nth j ?us)"
                by auto
              obtain \<mu>1 \<mu>2 \<delta> where mgu:"mgu_vd ren l'' l' = Some (\<mu>1, \<mu>2)"
                and \<sigma>:"\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" and \<tau>:"\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" and \<mu>:"l'' \<cdot> \<mu>1 = l' \<cdot> \<mu>2"
                using mgu_vd_complete[OF unifiable, of ren] by auto
              have inner:"hole_pos E \<noteq> []" using hpos MFun by auto
              have "(False, (E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, r \<cdot> \<mu>1) \<in> critical_pairs ren R R"
                using lr lr' E l'' mgu inner SR by (force intro: critical_pairsI)
              from closed[rule_format,OF this] obtain v
                where v:"((E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, v) \<in> par_rstep S" "(r \<cdot> \<mu>1, v) \<in> (rstep S)\<^sup>*" by auto
              then have closed1:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep S" unfolding \<sigma> \<tau>
                using subst_closed_par_rstep by fastforce
              from v have closed2: "(r \<cdot> \<sigma>, v \<cdot> \<delta>) \<in> (rstep S)\<^sup>*" unfolding \<sigma> \<tau> using rsteps_closed_subst by auto
              from par_rstep_mctxtE[OF closed1] obtain F infos3 where EF:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (F, par_lefts infos3)" 
                and "v \<cdot> \<delta> =\<^sub>f (F, par_rights infos3)"
                and "par_conds S infos3" by auto
              then have Er: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt S F infos3"
                unfolding par_rstep_mctxt_def by auto
              let ?cs = "par_lefts infos3" 
              let ?ol' = "overlap' (F, ?cs) (D', remove_nth j ?vs)"
              have "(?ol', mset (remove_nth j ?vs)) \<in> (mult {\<lhd>})\<^sup>="
                using overlap'_bounded[OF E\<sigma>r EF] overlap'_symmetric[OF EF E\<sigma>r] by auto
              moreover have "(mset (remove_nth j ?vs), mset ?vs) \<in> mult {\<lhd>}"
                using remove_nth_mult j by (metis length_map)
              moreover have "overlap' (C, ?ss) (D, ?vs) = mset ?vs" using MFun MHole ss by auto
              ultimately have ol:"(?ol', overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}"
                unfolding mult_def by simp

              have "set (remove_nth j infos') \<subseteq> set infos'" using j unfolding remove_nth_def
                by (simp add: set_drop_subset set_take_subset)
              hence "par_conds R (remove_nth j infos')" using par_conds2 by auto 
              from E\<sigma>r uD this have Eu:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, u) \<in> par_rstep_mctxt R D' (remove_nth j infos')"
                unfolding par_rstep_mctxt_def using j by (auto simp: remove_map)
              from Fun(2)[OF ol[unfolded remove_map[OF j]] Er Eu] closed2 
              show ?thesis using r rtrancl_trans by metis
            qed
          next
            case MHole
            then have "?vs = [Fun f ss']" using s2 by (auto elim: eqf_MHoleE)
            moreover have "?us = [u]" using u MHole by (auto elim: eqf_MHoleE)
            ultimately have "(Fun f ss', u) \<in> rrstep R" using steps2 by auto
            then obtain l' r' \<sigma>' where lr': "(l', r') \<in> R" and l':"Fun f ss' = l' \<cdot> \<sigma>'"
              and r':" u = r' \<cdot> \<sigma>'"
              using rrstep_imp_rule_subst by fastforce
            with l have eq:"l' \<cdot> \<sigma>' = l \<cdot> \<sigma>" by auto
            from lr' left_lin have "linear_term l'" by (auto simp: left_linear_trs_def)
            from par_rstep_mctxt_linear_subst[OF this Fun(3)[unfolded l']]
            obtain \<tau> where \<tau>:"t = l' \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l'. (\<sigma>' x, \<tau> x) \<in> par_rstep S) \<or>
              (\<exists>E s'. l' = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> hole_pos E \<in> hole_poss C)"
              by blast
            then show ?thesis
            proof
              assume "t = l' \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l'. (\<sigma>' x, \<tau> x) \<in> par_rstep S)"
              with step_in_subst_imp_par_diamond r' lr' show ?thesis using par_rstep_rsteps by fastforce
            next
              assume "\<exists>E s'. l' = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> hole_pos E \<in> hole_poss C"
              then obtain E s' where "l' = E\<langle>s'\<rangle>" and "is_Fun s'" and "hole_pos E \<in> hole_poss C" by blast
              with \<open>C = MHole\<close> have isFun:"is_Fun l'" by (cases E) auto
              from mgu_vd_complete[OF eq, of ren] obtain \<mu>1 \<mu>2 \<delta>
                where unif:"mgu_vd ren l' l = Some (\<mu>1, \<mu>2)"
                and \<sigma>:"\<sigma>' = \<mu>1 \<circ>\<^sub>s \<delta>" and \<sigma>':"\<sigma> = \<mu>2 \<circ>\<^sub>s \<delta>"
                by auto
              from critical_pairsI[OF lr' lr _ _ unif] isFun
              have "(True, r \<cdot> \<mu>2, r' \<cdot> \<mu>1) \<in> critical_pairs ren R R"
                using critical_pairs_mono[OF subset_refl[of R] SR, of ren] by force
              with overlay_closed obtain w
                where "(r \<cdot> \<mu>2, w) \<in> (rstep S)\<^sup>*" and "(r' \<cdot> \<mu>1, w) \<in> (rstep S)\<^sup>*" by auto
              with \<sigma> \<sigma>' have "(r \<cdot> \<sigma>, w \<cdot> \<delta>) \<in> (rstep S)\<^sup>*" "(r' \<cdot> \<sigma>', w \<cdot> \<delta>) \<in> (rstep S)\<^sup>*"
                by (auto simp: rsteps_closed_subst)
              with r r' show ?thesis using par_rsteps_rsteps by auto
            qed
          qed (insert s2, auto dest: eqfE)
        next
          case (MFun g Cs) note C = this
          then have [simp]: "g = f" using s by (auto dest: eqfE)
          define Infos where "Infos = partition_holes infos Cs" 
          from eqfE[OF s, unfolded C, simplified]  
          have len_infos: "sum_list (map num_holes Cs) = length infos" 
            and ss'_id: "ss' = map (\<lambda>i. fill_holes (Cs ! i) (par_lefts (Infos ! i))) [0..<length Cs]" 
            and len_Infos: "length Infos = length Cs" 
            and infos: "infos = concat Infos" 
            and len_Csi: "\<And> i. i < length Cs \<Longrightarrow> num_holes (Cs ! i) = length (Infos ! i)" 
            by (auto simp: Infos_def)
          define sss where "sss = map par_lefts Infos" 
          have lCs:"length ss' = length Cs" and lsss:"length sss = length Cs"
            and sss:"?ss = concat sss" and ss'iC:"\<And> i. i < length Cs \<Longrightarrow> ss' ! i =\<^sub>f (Cs ! i, sss ! i)"
            unfolding ss'_id sss_def using len_infos len_Infos infos by (auto simp: map_concat len_Csi)
          from s have "Fun f ss' = fill_holes C ?ss" "num_holes C = length ?ss" by (auto dest: eqfE)
          define tss where "tss = map par_rights Infos" 
          from t C obtain ts' where [simp]: "t = Fun f ts'" by (auto elim: eqf_MFunE)
          from eqfE[OF t[unfolded C this], simplified]
          have ts'_id: "ts' = map (\<lambda>i. fill_holes (Cs ! i) (par_rights (Infos ! i))) [0..<length Cs]" 
            by (auto simp: Infos_def)
          have lCs2:"length ts' = length Cs" and ltss:"length tss = length Cs"
            and tss:"?ts = concat tss" and ts'iC:"\<And> i. i < length Cs \<Longrightarrow> ts' ! i =\<^sub>f (Cs ! i, tss ! i)"
            unfolding ts'_id tss_def using len_infos len_Infos infos by (auto simp: map_concat len_Csi)
          show ?thesis
          proof (cases D)
            case MHole
            then have vs:"?vs = [Fun f ss']" using s2 by (auto elim: eqf_MHoleE)
            moreover have "?us = [u]" using u MHole by (auto elim: eqf_MHoleE)
            ultimately have "(Fun f ss', u) \<in> rrstep R" using steps2 by auto
            then obtain l r \<sigma> where lr: "(l, r) \<in> R" and l:"Fun f ss' = l \<cdot> \<sigma>" and r: "u = r \<cdot> \<sigma>"
              using rrstep_imp_rule_subst by fastforce
            from lr left_lin have "linear_term l" by (auto simp: left_linear_trs_def)
            from par_rstep_mctxt_linear_subst[OF this Fun(3)[unfolded l]]
            obtain \<tau> where \<tau>:"t = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pS) \<or>
              (\<exists>D s' l' r' j C'. l = D\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> S \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
                \<and> hole_pos D \<in> hole_poss C \<and> j < length infos
                \<and> (D \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss) \<and> t =\<^sub>f (C', remove_nth j ?ts))"
              by blast
            then show ?thesis
            proof
              assume *:"t = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pS)"
              with step_in_subst_imp_par_diamond r lr show ?thesis using par_rstep_rsteps by fastforce
            next
              assume "\<exists>D s' l' r' j C'. l = D\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> S \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
                \<and> hole_pos D \<in> hole_poss C \<and> j < length infos
                \<and> (D \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss) \<and> t =\<^sub>f (C', remove_nth j ?ts)"
              then obtain E l'' l' r' j C' where E:"l = E\<langle>l''\<rangle>" and l'':"is_Fun l''" and lr':"(l', r') \<in> S"
                and unifiable:"l'' \<cdot> \<sigma> = l' \<cdot> \<tau>" and hpos:"hole_pos E \<in> hole_poss C" and j:"j < length infos"
                and E\<sigma>r:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss)" and tCtsj:"t =\<^sub>f (C', remove_nth j ?ts)"
                by auto
              obtain \<mu>1 \<mu>2 \<delta> where mgu:"mgu_vd ren l'' l' = Some (\<mu>1, \<mu>2)"
                and \<sigma>:"\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" and \<tau>:"\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" and \<mu>:"l'' \<cdot> \<mu>1 = l' \<cdot> \<mu>2"
                using mgu_vd_complete[OF unifiable, of ren] by auto
              have inner:"hole_pos E \<noteq> []" using hpos C by auto
              have "(False, (E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, r \<cdot> \<mu>1) \<in> critical_pairs ren R R"
                using lr lr' E l'' mgu inner SR by (force intro: critical_pairsI)
              from closed[rule_format,OF this] obtain v
                where v: "((E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, v) \<in> par_rstep S" "(r \<cdot> \<mu>1, v) \<in> (rstep S)\<^sup>*" by auto
              then have closed1: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep S" unfolding \<sigma> \<tau>
                using subst_closed_par_rstep by fastforce
              from v have closed2: "(r \<cdot> \<sigma>, v \<cdot> \<delta>) \<in> (rstep S)\<^sup>*" unfolding \<sigma> \<tau> using rsteps_closed_subst by auto
              from par_rstep_mctxtE[OF closed1] 
              obtain F infos3 where EF:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (F, par_lefts infos3)" 
                and "v \<cdot> \<delta> =\<^sub>f (F, par_rights infos3)"
                and "par_conds S infos3" by auto
              then have Er: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt S F infos3"
                unfolding par_rstep_mctxt_def by auto              
              then have Ev:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt S F infos3"
                unfolding par_rstep_mctxt_def by auto
              then have EvR: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt R F infos3"
                using SR unfolding par_rstep_mctxt_def par_cond_def by fastforce

              let ?cs = "par_lefts infos3" 
              let ?ol' = "overlap' (C', remove_nth j ?ss) (F, ?cs)"
              have "(?ol', mset (remove_nth j ?ss)) \<in> (mult {\<lhd>})\<^sup>=" using overlap'_bounded[OF E\<sigma>r EF] by auto
              moreover have "(mset (remove_nth j ?ss), mset ?ss) \<in> mult {\<lhd>}" using remove_nth_mult j
                by (metis length_map)
              moreover have "overlap' (C, ?ss) (D, ?vs) = mset ?ss" using C MHole vs by auto
              ultimately have ol:"(?ol', overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}" unfolding mult_def by simp
              have "set (remove_nth j infos) \<subseteq> set infos" unfolding remove_nth_def
                by (simp add: set_drop_subset set_take_subset)
              hence "par_conds S (remove_nth j infos)" using par_conds1 by auto 

              from E\<sigma>r tCtsj this
              have Et:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, t) \<in> par_rstep_mctxt S C' (remove_nth j infos)"
                unfolding par_rstep_mctxt_def using j by (auto simp: remove_map)
              from Fun(2)[OF ol[unfolded remove_map[OF j]] Et EvR] 
              show ?thesis by (metis closed2 r rtrancl_trans)
            qed
          next
            case (MFun h Ds) note D = this
            then have [simp]: "h = f" using s2 by (auto dest: eqfE)

            define Infos' where "Infos' = partition_holes infos' Ds" 
            from eqfE[OF s2, unfolded D, simplified]  
            have len_infos': "sum_list (map num_holes Ds) = length infos'" 
              and ss'_id': "ss' = map (\<lambda>i. fill_holes (Ds ! i) (par_lefts (Infos' ! i))) [0..<length Ds]" 
              and len_Infos': "length Infos' = length Ds" 
              and infos': "infos' = concat Infos'" 
              and len_Dsi: "\<And> i. i < length Ds \<Longrightarrow> num_holes (Ds ! i) = length (Infos' ! i)" 
              by (auto simp: Infos'_def)
            define vss where "vss = map par_lefts Infos'" 
            have lDs:"length ss' = length Ds" and lvss:"length vss = length Ds"
              and vss:"?vs = concat vss" and vs'iD:"\<And> i. i < length Ds \<Longrightarrow> ss' ! i =\<^sub>f (Ds ! i, vss ! i)"
              unfolding ss'_id' vss_def using len_infos' len_Infos' infos' by (auto simp: map_concat len_Dsi)
            from s2 have "Fun f ss' = fill_holes D ?vs" "num_holes D = length ?vs" by (auto dest: eqfE)
            define uss where "uss = map par_rights Infos'" 
            from u D obtain us' where [simp]: "u = Fun f us'" by (auto elim: eqf_MFunE)
            from eqfE[OF u[unfolded D this], simplified]
            have us'_id: "us' = map (\<lambda>i. fill_holes (Ds ! i) (par_rights (Infos' ! i))) [0..<length Ds]" 
              by (auto simp: Infos'_def)
            have lDs2:"length us' = length Ds" and luss:"length uss = length Ds"
              and uss:"?us = concat uss" and us'iD:"\<And> i. i < length Ds \<Longrightarrow> us' ! i =\<^sub>f (Ds ! i, uss ! i)"
              unfolding us'_id uss_def using len_infos' len_Infos' infos' by (auto simp: map_concat len_Dsi)

            { fix i
              assume i:"i < length ss'"
              then have s: "ss' ! i \<in> set ss'" using nth_mem by blast
              from i ts'iC lCs lCs2 have ts'i:"ts' ! i =\<^sub>f (Cs ! i, tss ! i)" by auto
              from i us'iD lDs lDs2 have us'i:"us' ! i =\<^sub>f (Ds ! i, uss ! i)" by auto
              have "sss ! i = partition_holes ?ss Cs ! i"
                by (metis eqfE(2) lsss partition_holes_concat_id ss'iC sss)
              moreover have " vss ! i = partition_holes ?vs Ds ! i"
                by (metis eqfE(2) lvss partition_holes_concat_id vs'iD vss)
              ultimately have "overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i) \<in>#
              mset (map (\<lambda>i. overlap' (Cs ! i, partition_holes ?ss Cs ! i) (Ds ! i, partition_holes ?vs Ds ! i)) [0..<length Cs])"
                unfolding sss vss using i lCs by fastforce
              then have ol:"overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i) \<subseteq># overlap' (C, ?ss) (D, ?vs)"
                unfolding C MFun by (simp add: in_mset_subset_Union)
              { fix C' D' s' t' u' infos2 infos2'
                assume 1:"(overlap' (C', par_lefts infos2) (D', par_lefts infos2'), overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i)) \<in> mult {\<lhd>}"
                  and 2: "(s', t') \<in> par_rstep_mctxt S C' infos2" "(s', u') \<in> par_rstep_mctxt R D' infos2'"
                have "trans {\<lhd>}" unfolding trans_def using supt_trans by auto
                with mult_subset_mult ol 1 have "(overlap' (C', par_lefts infos2) (D', par_lefts infos2'), overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}" by blast
                from Fun(2)[OF this 2] have "\<exists>v w. (t', v) \<in> (rstep S)\<^sup>* \<and> (v, w) \<in> ?pR \<and> (u', w) \<in> (rstep S)\<^sup>*" .
              } note m = this

              from i have iI: "i < length Infos" using len_Infos lCs by auto
              have "Ball (set Infos) (par_conds S)" using par_conds1 unfolding infos by auto
              with iI have parR1: "par_conds S (Infos ! i)" by auto
              have id: "par_lefts (Infos ! i) = map par_lefts Infos ! i \<and> par_rights (Infos ! i) = map par_rights Infos ! i"
                using iI by auto 
              with ss'iC i lCs ts'i parR1
              have ssts:"(ss' ! i, ts' ! i) \<in> par_rstep_mctxt S (Cs ! i) (Infos ! i)"
                by (intro par_rstep_mctxtI, auto simp: tss_def sss_def)

              from i have iI': "i < length Infos'" using len_Infos' lDs by auto
              have "Ball (set Infos') (par_conds R)" using par_conds2 unfolding infos' by auto
              with iI' have parR2: "par_conds R (Infos' ! i)" by auto
              have id': "par_lefts (Infos' ! i) = map par_lefts Infos' ! i \<and> par_rights (Infos' ! i) = map par_rights Infos' ! i"
                using iI' by auto 
              with vs'iD i lDs us'i parR2
              have ssus:"(ss' ! i, us' ! i) \<in> par_rstep_mctxt R (Ds ! i) (Infos' ! i)"
                by (intro par_rstep_mctxtI, auto simp: uss_def vss_def) 

              have "\<exists>v w. (ts' ! i, v) \<in> (rstep S)\<^sup>* \<and> (v, w) \<in> ?pR \<and> (us' ! i, w) \<in> (rstep S)\<^sup>*" 
                by (rule Fun(1)[OF s _ ssts ssus], rule m, insert id id', auto simp: vss_def sss_def)
            }

            then obtain v w
            where vw: "\<And>i. i < length ts' \<Longrightarrow> (ts' ! i, v i) \<in> (rstep S)\<^sup>* \<and> (v i, w i) \<in> ?pR \<and>
                (us' ! i, w i) \<in> (rstep S)\<^sup>*"
              using lCs lCs2 by metis
            let ?vs' = "map v [0..<length ts']"
            let ?ws' = "map w [0..<length us']"
            from vw have *:"\<And>i. i < length ts' \<Longrightarrow> (ts' ! i, v i) \<in> (rstep S)\<^sup>*" by auto
            have "length ts' = length ?vs'" by auto
            from * args_rsteps_imp_rsteps[OF this] have v:"(Fun f ts', Fun f ?vs') \<in> (rstep S)\<^sup>*" by auto
            from vw have *:"\<And>i. i < length us' \<Longrightarrow> (us' ! i, w i) \<in> (rstep S)\<^sup>*"
              using par_rsteps_rsteps lCs lCs2 lDs lDs2  by auto
            have "length us' = length ?ws'" by auto
            from * args_rsteps_imp_rsteps[OF this] have w:"(Fun f us', Fun f ?ws') \<in> (rstep S)\<^sup>*"
              by auto
            from vw have "(Fun f ?vs', Fun f ?ws') \<in> ?pR" using lCs lCs2 lDs lDs2 by auto
            with v w show ?thesis by auto
          qed (insert s2, auto dest: eqfE)
        qed  (insert s, auto dest: eqfE)
      qed
    qed
  } note a = this
  from assms(2) have sn:"SN ((rstep S)\<^sup>+)" using SN_imp_SN_trancl by blast
  have "a*": "\<exists>v w. (t, v) \<in> (rstep S)\<^sup>* \<and> (v, w) \<in> par_rstep R \<and> (u, w) \<in> (rstep S)\<^sup>*"
    if st:"(s, t) \<in> (rstep S)\<^sup>*" and su:"(s, u) \<in> par_rstep R" for s t u
    using st su
  proof (induct s arbitrary: t u rule: SN_induct[OF sn])
    case (1 s) note IH = 1(1)
    from 1(2) show ?case
    proof (cases rule: converse_rtranclE)
      case (step s')
      from a step(1) 1(3) obtain v w
        where sv:"(s', v) \<in> (rstep S)\<^sup>*" and vw:"(v, w) \<in> par_rstep R" and uw:"(u, w) \<in> (rstep S)\<^sup>*"
        by blast
      from sv step(2) cpcs_sn_cr[OF assms(1,2)] obtain t'
        where tt:"(t, t') \<in> (rstep S)\<^sup>*" and vt:"(v, t') \<in> (rstep S)\<^sup>*" by auto
      from sv step(1) have "(s, v) \<in> (rstep S)\<^sup>+" by simp
      from IH[OF this vt vw] obtain v' w'
        where "(t', v') \<in> (rstep S)\<^sup>*" and "(v', w') \<in> par_rstep R" and "(w, w') \<in> (rstep S)\<^sup>*"
        by auto
      then have "(t, v') \<in> (rstep S)\<^sup>* \<and> (v', w') \<in> par_rstep R \<and> (u, w') \<in> (rstep S)\<^sup>*"
        using tt uw by auto
      then show ?thesis by blast
    qed (insert 1, blast)
  qed
  have "\<exists>v w x. (t', v) \<in> (rstep S)\<^sup>* \<and> (v, x) \<in> par_rstep R \<and> (u', w) \<in> (rstep S)\<^sup>* \<and> (w, x) \<in> par_rstep R"
    if st:"(s, t) \<in> (rstep S)\<^sup>*" and tt:"(t, t') \<in> par_rstep R"
    and su:"(s, u) \<in> (rstep S)\<^sup>*" and uu:"(u, u') \<in> par_rstep R" for s t t' u u'
    using st tt su uu
  proof (induct s arbitrary: t u t' u' rule: SN_induct[OF sn])
    case (1 s)
    then consider (empty) "s = t \<and> t = u" | (nonempty) "(s, t) \<in> (rstep S)\<^sup>+ \<or> (s, u) \<in> (rstep S)\<^sup>+" by (metis rtranclD)
    then show ?case
    proof (cases)
      case empty
      then show ?thesis using b 1 by auto
    next
      case nonempty
      from 1 cpcs_sn_cr[OF assms(1,2)] obtain v where
        tv:"(t , v) \<in> (rstep S)\<^sup>*" and uv:"(u, v) \<in> (rstep S)\<^sup>*" by blast
      with nonempty have sv:"(s, v) \<in> (rstep S)\<^sup>+" by auto
      from "a*"[OF tv 1(3)] obtain v\<^sub>1 w\<^sub>1 where
        vv\<^sub>1:"(v, v\<^sub>1) \<in> (rstep S)\<^sup>*" and v\<^sub>1w\<^sub>1: "(v\<^sub>1, w\<^sub>1) \<in> par_rstep R" and tw\<^sub>1:"(t', w\<^sub>1) \<in> (rstep S)\<^sup>*"
        by auto
      from "a*"[OF uv 1(5)] obtain v\<^sub>2 w\<^sub>2 where
        vv\<^sub>2:"(v, v\<^sub>2) \<in> (rstep S)\<^sup>*" and v\<^sub>2w\<^sub>2: "(v\<^sub>2, w\<^sub>2) \<in> par_rstep R" and uw\<^sub>2:"(u', w\<^sub>2) \<in> (rstep S)\<^sup>*"
        by auto
      from 1(1)[OF sv vv\<^sub>1 v\<^sub>1w\<^sub>1 vv\<^sub>2 v\<^sub>2w\<^sub>2] tw\<^sub>1 uw\<^sub>2 show ?thesis by (meson rtrancl_trans)
    qed
  qed
  then have "\<diamond> ((rstep S)\<^sup>* O par_rstep R)" by (intro diamond_I') blast
  moreover have "rstep R \<subseteq> (rstep S)\<^sup>* O par_rstep R" using rstep_par_rstep by fastforce
  moreover have "(rstep S)\<^sup>* O par_rstep R \<subseteq> (rstep R)\<^sup>*" using SR
    by (metis par_rstep_rsteps relcomp_mono rstep_mono rtrancl_idemp_self_comp rtrancl_mono)
  ultimately show ?thesis using diamond_imp_CR' by auto
qed

end
end
