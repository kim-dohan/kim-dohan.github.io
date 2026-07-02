(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2013, 2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Rewriting
imports
  Innermost_Usable_Rules
  TRS.QDP_Framework
  Not_SN.Nontermination
  First_Order_Rewriting.Critical_Pairs
  First_Order_Terms.Unification_String
begin

definition "nfc R Q S t nfs = (\<forall> \<sigma> u. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q \<longrightarrow> 
  u \<in> NF (qrstep nfs Q R) \<and> (t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>* \<longrightarrow> u \<in> NF_terms Q)"

lemma innermost_imp_nfc:
  assumes inner: "NF_terms Q = NF_trs R"
  and no_var_lhs:"\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "nfc R Q S t nfs"
proof (unfold nfc_def, intro allI impI, elim conjE) 
  fix \<sigma> u
  assume uNF:"u \<in> NF (qrstep nfs Q R)" 
  from inner have "NF_trs R \<subseteq> NF_terms Q" by auto
  from Q_subset_R_imp_same_NF[OF this no_var_lhs] have "NF_trs R = NF (qrstep nfs Q R)" by auto
  with inner uNF show "u \<in> NF_terms Q" by auto
qed

context R_Q_U_ecap
begin

inductive enfcf :: "('f, string) terms \<Rightarrow> ('f, string) term \<Rightarrow> bool"
where
  arg:  "i < length ts \<and> enfcf S (ts ! i) \<Longrightarrow> enfcf S (Fun f ts) "
| rule: "(l, r) \<in> R \<and> (\<exists>\<mu>. mgu_class (Fun f (map ((ecap R Q (mv_xvar ` S)) \<circ> mv_xvar) ts)) l = Some \<mu> \<and>
         ((mv_xvar ` S) \<union> (mv_yvar ` (set (args l))) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>) \<subseteq> NF_terms Q) \<and> enfcf (set (args l)) r \<Longrightarrow> enfcf S (Fun f ts)"
| q:    "q \<in> Q \<and> (\<exists>\<mu>. mgu_class (Fun f (map ((ecap R Q (mv_xvar ` S)) \<circ> mv_xvar) ts)) q = Some \<mu> \<and>
         ((mv_xvar ` S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>) \<subseteq> NF_terms Q \<and> (mv_yvar q) \<cdot> \<mu> \<in> NF_trs R) \<Longrightarrow> enfcf S (Fun f ts)"

lemma enfcf_sound:
  assumes vars: "vars_term t \<subseteq> (\<Union> s \<in> S. vars_term s)"
  and enfcf: "\<not> enfcf S t"
  and wf_trs : "wf_trs R"
  shows "nfc R Q S t nfs"
proof (rule ccontr)
  let ?QR = "qrstep nfs Q R"
  let ?RQR = "rqrstep nfs Q R"
  let ?NRQR = "nrqrstep nfs Q R"
  let ?R = "rstep R"
  assume "\<not> nfc R Q S t nfs"
  then obtain \<sigma> u where \<sigma>:"S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" and "(t \<cdot> \<sigma>, u) \<in> ?QR\<^sup>*" and  u:"u \<notin> NFQ" and unf: "u \<in> NF ?QR"
    unfolding nfc_def by auto
  then obtain n where "(t \<cdot> \<sigma>, u) \<in> ?QR^^n" by blast
  with \<sigma> u unf vars have "enfcf S t" proof (induct n arbitrary: t \<sigma> S u rule: nat_less_induct)
    fix n t \<sigma> u
    fix S :: "('f, string) terms"
    assume "\<forall>m<n. \<forall>s \<tau> S. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<tau> \<subseteq> NFQ \<longrightarrow> (\<forall>u. u \<notin> NFQ \<longrightarrow> u \<in> NF ?QR \<longrightarrow> vars_term s \<subseteq> (\<Union> s' \<in> S. vars_term s')
      \<longrightarrow> (s \<cdot> \<tau>, u) \<in> ?QR ^^ m \<longrightarrow> enfcf S s)"
      and "S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" and "u \<notin> NFQ" and "u \<in> NF ?QR"
      and "vars_term t \<subseteq> (\<Union> s \<in> S. vars_term s)" and "(t \<cdot> \<sigma>, u) \<in> ?QR ^^ n"
    then show "enfcf S t" proof (induction t arbitrary: n u)
      case (Var x)
      from Var(5) have "x \<in> (\<Union>a\<in>S. vars_term a)" by auto
      then obtain s where sS: "s \<in> S" and "x \<in> vars_term s" by auto
      then have xs:"s \<unrhd> Var x" by auto
      from sS Var(2) have "s \<cdot> \<sigma> \<in> NFQ" by auto
      with xs have xnfq:"Var x \<cdot> \<sigma> \<in> NFQ"
        by (metis (no_types) NF_subterm \<open>s \<cdot> \<sigma> \<in> NFQ\<close> eval_term.simps(1) supteq_subst)
      then have "Var x \<cdot> \<sigma> \<in> NF ?R" using NF_Q_R by auto
      then have "Var x \<cdot> \<sigma> \<in> NF ?QR" using qrstep_subset_rstep NF_anti_mono by blast
      moreover from  Var(6) rtrancl_power have "(Var x \<cdot> \<sigma>, u) \<in> ?QR\<^sup>*" by blast
      ultimately have "Var x \<cdot> \<sigma> = u" using NF_not_suc by auto
      with xnfq Var(3) show ?case by auto
    next
      case (Fun f ts)
      let ?ts\<sigma> = "map (\<lambda>t. t \<cdot> \<sigma>) ts"
      have t:"Fun f (map (\<lambda>t. e_cap (mv_xvar ` S) (mv_xvar t)) ts) = Fun f (map (e_cap (mv_xvar ` S) \<circ> mv_xvar) ts)" by auto
      have ml: "length ?ts\<sigma> = length ts" using length_map by auto
      with Fun(7) have "(Fun f ?ts\<sigma>, u) \<in> ?QR ^^ n" by simp
      from qrsteps_rqrstep_cases_n[OF this] have
        "(\<exists>us. length us = length ?ts\<sigma> \<and> u = Fun f us \<and> (\<forall>i<length ?ts\<sigma>. \<exists>m \<le>n. (?ts\<sigma> ! i, us ! i) \<in> ?QR^^m) \<and>
         (Fun f ?ts\<sigma>, u) \<in> ?NRQR ^^ n) \<or>
         (\<exists>m1 < n. \<exists>m2 < n. (Fun f ?ts\<sigma>, u) \<in> ?NRQR ^^ m1 O ?RQR O ?QR ^^ m2)" .
      then show ?case
      proof
        assume " \<exists>m1 < n. \<exists>m2 < n. (Fun f ?ts\<sigma>, u) \<in> ?NRQR ^^ m1 O ?RQR O ?QR ^^ m2"
        then obtain m1 m2 where "(Fun f ?ts\<sigma>, u) \<in> ?NRQR ^^ m1 O ?RQR O ?QR ^^ m2 \<and> m1 < n" and m2: "m2 < n" by blast
        then obtain v w where tv:"(Fun f ?ts\<sigma>, v) \<in> ?NRQR ^^ m1"
          and vw:"(v, w) \<in> ?RQR" and wu:"(w, u) \<in> ?QR ^^ m2" by auto
        then have nr:"(Fun f ?ts\<sigma>, v) \<in> ?NRQR\<^sup>*" using relpow_imp_rtrancl by auto
        from nrqrsteps_preserve_root_fun[OF nr] obtain vs where v: "v = Fun f vs" by blast
        with nrqrsteps_num_args[OF nr] have len: "length vs = length ?ts\<sigma>" by auto
        have isteps: "\<forall>i < length ?ts\<sigma>. (?ts\<sigma> ! i, vs ! i) \<in> ?QR\<^sup>*"
        proof (intro allI impI)
          fix i
          assume "i < length ?ts\<sigma>"
          moreover with len have "i < length vs" by auto
          with v have "args v ! i = vs ! i" by auto
          moreover have "args (Fun f ?ts\<sigma>) ! i= ?ts\<sigma> ! i" by auto
          ultimately show "(?ts\<sigma> ! i, vs ! i) \<in> ?QR\<^sup>*" using nrqrsteps_imp_arg_qrsteps[OF nr] by metis
        qed
        from vw obtain l r \<rho> where vl: "v = l \<cdot> \<rho>" and lr: "(l, r) \<in> R" and wr: "w = r \<cdot> \<rho>" and nfq: " (\<forall>z\<lhd>l \<cdot> \<rho>. z \<in> NFQ)"
          by blast
        let ?S' = "set (args l)"
        from nfq have "\<forall> z \<in> ?S'. z \<cdot> \<rho> \<in> NFQ"
          by (metis instance_no_supt_imp_no_supt supt_imp_args supt_list_sound)
        then have S':"?S' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<rho> \<subseteq> NFQ" by auto
        from spec[OF spec[OF wf_trs[unfolded wf_trs_def]], of l r] lr
        obtain g ls where l:"l = Fun f ls" and "vars_term r \<subseteq> vars_term l" using v vl by auto
        then have vars:"vars_term r \<subseteq> \<Union> (vars_term ` ?S')" by auto
        from spec[OF Fun(2), of m2] m2 have
          "\<forall>s \<tau> S. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<tau> \<subseteq> NFQ \<longrightarrow> u \<notin> NFQ \<longrightarrow> u \<in> NF (qrstep nfs Q R) \<longrightarrow>
          vars_term s \<subseteq> (\<Union>a\<in>S. vars_term a) \<longrightarrow> (s \<cdot> \<tau>, u) \<in> qrstep nfs Q R ^^ m2 \<longrightarrow> enfcf S s" by auto
        from spec[OF spec[OF spec[OF this]], of \<rho> ?S' r] S' Fun(4) Fun(5) wu wr vars have enfcr:"enfcf ?S' r" by simp
        from \<open>(Fun f ?ts\<sigma>, v) \<in> ?NRQR\<^sup>*\<close> vl have "(Fun f ts \<cdot> \<sigma>, l \<cdot> \<rho>) \<in> ?NRQR\<^sup>*" by auto
        from ecap_steps_mgu_below_root[OF ecap Fun(3) this] obtain \<mu>1 \<mu>2 where
          mgu: "mgu_class (Fun f (map (\<lambda>t. e_cap (mv_xvar ` S) (mv_xvar t)) ts)) l = Some \<mu>1" and
          \<sigma>\<mu>2: "\<forall>s. s \<cdot> \<sigma> = mv_xvar s \<cdot> \<mu>1 \<cdot> \<mu>2" and \<rho>\<mu>2:"\<forall>s. s \<cdot> \<rho> = mv_yvar s \<cdot> \<mu>1 \<cdot> \<mu>2" by blast
        {
          fix s
          assume "s \<in> ((mv_xvar ` S) \<union> (mv_yvar ` ?S')) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>1"
          then have "s \<in> (mv_xvar ` S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>1 \<or> s \<in> (mv_yvar ` ?S') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>1" by auto
          then have "s \<in> NFQ"
          proof
            assume "s \<in> (mv_xvar ` S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>1"
            then obtain s' where s':"s' \<in> S \<and> s = mv_xvar s' \<cdot> \<mu>1" by blast
            with Fun(3) have "s' \<cdot> \<sigma> \<in> NFQ" by auto
            with spec[OF \<sigma>\<mu>2, of s'] have "mv_xvar s' \<cdot> \<mu>1 \<cdot> \<mu>2 \<in> NFQ" by auto
            with s' show ?thesis using NF_instance by auto
          next
            assume "s \<in> (mv_yvar ` ?S') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>1"
            then obtain s' where s':"s' \<in> ?S' \<and> s = mv_yvar s' \<cdot> \<mu>1" by blast
            with S' have "s' \<cdot> \<rho> \<in> NFQ" by auto
            with spec[OF \<rho>\<mu>2, of s'] have "mv_yvar s' \<cdot> \<mu>1 \<cdot> \<mu>2 \<in> NFQ" by auto
            with s' show ?thesis using NF_instance by auto
          qed
        }
        then have SS':"(((mv_xvar ` S) \<union> (mv_yvar ` ?S')) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>1) \<subseteq> NFQ" by force
        from mgu lr enfcr SS' t show ?thesis using enfcf.rule by metis
      next
        assume "(\<exists>us. length us = length ?ts\<sigma> \<and> u = Fun f us \<and>
          (\<forall>i<length ?ts\<sigma>. \<exists>m \<le> n. (?ts\<sigma> ! i, us ! i) \<in> ?QR^^m) \<and> (Fun f ?ts\<sigma>, u) \<in> ?NRQR ^^ n)"
        then obtain us where
          len: "length us = length ?ts\<sigma>" and u:"u = Fun f us" and
          isteps:"\<forall>i<length ?ts\<sigma>. \<exists>m \<le> n. (?ts\<sigma> ! i, us ! i) \<in> ?QR^^m"
          and steps: "(Fun f ?ts\<sigma>, u) \<in> ?NRQR ^^ n" by auto
        show ?thesis proof (cases "\<forall>i < length us. us ! i \<in> NFQ")
          case False
          then obtain i where i: "i < length us" and uinfq:"us ! i \<notin> NFQ" by auto
          then have tsi:"ts ! i \<in> set ts" using len length_map by auto
          from isteps i len obtain m where m:"m \<le> n" and "(?ts\<sigma> ! i, us ! i) \<in> ?QR^^m" by auto
          then have isteps: "(ts ! i \<cdot> \<sigma>, us ! i) \<in> ?QR^^m"
            by (metis i len ml nth_map)
          have uinf: "us ! i \<in> NF ?QR"
          proof (rule ccontr)
            assume "us ! i \<notin> NF (qrstep nfs Q R)"
            then obtain c where c: "(us ! i, c) \<in> ?QR" using NF_I by metis
            from id_take_nth_drop[OF i] have us: "us = take i us @ us ! i # drop (Suc i) us" .
            with qrstep_imp_ctxt_nrqrstep[OF c, of f "take i us" "drop (Suc i) us"] have
              "(Fun f us, Fun f (take i us @ c # drop (Suc i) us)) \<in> nrqrstep nfs Q R" by auto
            with Fun(5) u show False by (metis NF_E Un_iff qrstep_iff_rqrstep_or_nrqrstep)
          qed
          from tsi Fun(6) have vars:"vars_term (ts ! i) \<subseteq> (\<Union>a\<in>S. vars_term a)" by auto
          from Fun(2) have "\<forall>k<m. \<forall>s \<tau> S. S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<tau> \<subseteq> NFQ \<longrightarrow>
            (\<forall>u. u \<notin> NFQ \<longrightarrow> u \<in> NF (qrstep nfs Q R) \<longrightarrow> vars_term s \<subseteq> (\<Union>a\<in>S. vars_term a) \<longrightarrow>
            (s \<cdot> \<tau>, u) \<in> qrstep nfs Q R ^^ k \<longrightarrow> enfcf S s)" using Orderings.order_less_le_trans[OF _ m] by metis
          from Fun(1)[OF tsi this Fun(3) uinfq uinf vars isteps] have "enfcf S (ts ! i)" .
          then show ?thesis using tsi enfcf.arg i len ml by auto
        next
          case True
          from not_NF_termsE[OF Fun(4)] obtain C q \<rho> where C:"u = C\<langle>q \<cdot> \<rho>\<rangle>" and q: "q \<in> Q" by metis
          from C have "u \<unrhd> q \<cdot> \<rho>" by auto
          moreover have "\<not> (u \<rhd> q \<cdot> \<rho>)"
          proof
            assume "u \<rhd> q \<cdot> \<rho>"
            with u obtain ui where ui:"ui \<in> set us" and "ui  \<unrhd> q \<cdot> \<rho>" by blast
            then have "ui \<notin> NFQ" using q by (metis NF_instance NF_subterm notin_NF_terms)
            with ui True show False by (metis in_set_conv_nth)
          qed
          ultimately have rho:"u = q \<cdot> \<rho>" by auto
          with steps have "(Fun f ts \<cdot> \<sigma>, q \<cdot> \<rho>) \<in> ?NRQR\<^sup>*" using relpow_imp_rtrancl by auto
          from ecap_steps_mgu_below_root[OF ecap Fun(3) this] obtain \<mu>1 \<mu>2 where
          mgu: "mgu_class (Fun f (map (\<lambda>t. e_cap (mv_xvar ` S) (mv_xvar t)) ts)) q = Some \<mu>1" and
          \<sigma>\<mu>2: "\<forall>s. s \<cdot> \<sigma> = mv_xvar s \<cdot> \<mu>1 \<cdot> \<mu>2" and \<rho>\<mu>2:"\<forall>s. s \<cdot> \<rho> = mv_yvar s \<cdot> \<mu>1 \<cdot> \<mu>2" by blast
          have S: "(mv_xvar ` S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>1 \<subseteq> NFQ"
          proof
            fix s
            assume "s \<in> (mv_xvar ` S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<mu>1"
            then obtain s' where s':"s' \<in> S \<and> s = mv_xvar s' \<cdot> \<mu>1" by blast
            with Fun(3) have "s' \<cdot> \<sigma> \<in> NFQ" by auto
            with spec[OF \<sigma>\<mu>2, of s'] have "mv_xvar s' \<cdot> \<mu>1 \<cdot> \<mu>2 \<in> NFQ" by auto
            with s' show "s \<in> NFQ" using NF_instance by auto
          qed
          have "u \<in> NF_trs R"
          proof (rule ccontr)
            assume "u \<notin> NF_trs R"
            then obtain c where c:"(u, c) \<in> ?R" using NF_I by metis
            from c obtain l r C \<sigma> where l:"u = C\<langle>l \<cdot> \<sigma>\<rangle>" and r:"c = C\<langle>r \<cdot> \<sigma>\<rangle>" and lr:"(l, r) \<in> R" by auto
            from True u have "\<forall>s \<in> set (args u). s \<in> NFQ" using in_set_conv_nth term.sel(4) by metis
            with NF_terms_args_conv have "\<forall>s \<lhd> u. s \<in> NFQ" by auto
            with l NF_terms_ctxt have "\<forall>s\<lhd>l \<cdot> \<sigma>. s \<in> NFQ" by simp
            with lr have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> qrstep False Q R" by auto
            then have uc:"(u, c) \<in> qrstep False Q R" using l r by auto
            from wf_trs have "wwf_qtrs Q R" by (auto simp add: wf_trs_imp_wwf_qtrs)
            then have "?QR = qrstep False Q R" by (auto simp add: wwf_qtrs_imp_nfs_switch)
            with uc Fun(5) show False by auto
          qed
          with rho \<rho>\<mu>2 have "(mv_yvar q) \<cdot> \<mu>1 \<cdot> \<mu>2 \<in> NF_trs R" by simp
          then have nf:"(mv_yvar q) \<cdot> \<mu>1 \<in> NF_trs R" using NF_instance by blast
          from nf S mgu q t show ?thesis using enfcf.q by metis
        qed
      qed
    qed
  qed
  with assms show False by auto
qed

definition rewrite_common_preconditions where 
  "rewrite_common_preconditions s ss ts t t' lr p nfs sound \<equiv>
    (\<not> sound \<or> \<not> nfs \<longrightarrow> vars_term (t |_ p) \<subseteq> vars_term s)
  \<and> wf_rule lr
  \<and> UNF (qrstep nfs Q U)
  \<and> U \<subseteq> R
  \<and> (\<forall> l r. (l,r) \<in> U \<longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r)
  \<and> (\<forall> b s t. (b,s,t) \<in> critical_pairs string_rename {lr} U \<longrightarrow> s = t)
  \<and> (\<forall>t \<in> set ts. is_ur_closed_term_mv full_af (set ss) t)"

lemma rewriting_sound: 
  assumes common: "rewrite_common_preconditions s [s] [t |_p ] t t' (l,r) p nfs True"
  and rewrite: "(t,t') \<in> rstep_r_p_s R (l,r) p \<mu>"
  and sNF: "s \<cdot> \<sigma> \<in> NFQ"
  and nfs: "NF_subst nfs (s,t) \<sigma> Q"
  and steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>*"
  and uNF: "u \<in> NFQ"
  and wwf_or_SN: "\<not> nfs \<Longrightarrow> wwf_qtrs Q R \<or> SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>}"
  shows "(t' \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>* \<and> (SN_on (qrstep nfs Q R) {t \<cdot> \<sigma>} \<longrightarrow> SN_on (qrstep nfs Q R) {t' \<cdot> \<sigma>})"
proof -
  let ?QR = "qrstep nfs Q R"
  let ?QU = "qrstep nfs Q U"
  let ?QUR = "qrstep nfs Q (R \<inter> U)"
  note common = common[unfolded rewrite_common_preconditions_def if_True wf_rule_def]
  from common have 
    usable: "is_ur_closed_term_mv full_af {s} (t |_ p)" and
    var_cond: "\<not> nfs \<Longrightarrow> vars_term (t |_ p) \<subseteq> vars_term s" and
    var_cond_2: "vars_term r \<subseteq> vars_term l" and
    unf: "UNF (qrstep nfs Q U)" and
    subset: "U \<subseteq> R" and
    U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r" and
    crit_pairs: "\<And> b s t. (b,s,t) \<in> critical_pairs string_rename {(l,r)} U \<Longrightarrow> s = t"
    by auto
  have "NFQ \<subseteq> NF_trs R" by (rule NF_Q_R)
  also have "... \<subseteq> NF_trs U" by (rule NF_trs_mono[OF subset])
  finally have NF_Q_U: "NFQ \<subseteq> NF_trs U" . 
  from rewrite[unfolded rstep_r_p_s_def'] 
  have p: "p \<in> poss t" and lr: "(l,r) \<in> R" and subt: "t |_ p = l \<cdot> \<mu>"
    and t': "t' = replace_at t p (r \<cdot> \<mu>)" by auto
  from p have pt\<sigma>: "p \<in> poss (t \<cdot> \<sigma>)" by auto
  from normalize_subterm_qrsteps[OF pt\<sigma> steps uNF] obtain w
    where steps1: "(t \<cdot> \<sigma> |_ p, w) \<in> ?QR\<^sup>*" and w: "w \<in> NFQ" and steps2: "(replace_at (t \<cdot> \<sigma>) p w, u) \<in> ?QR\<^sup>*" by auto
  from steps1 p have steps1: "(t |_ p \<cdot> \<sigma>, w) \<in> ?QR\<^sup>*" by auto
  from subt_at_imp_supteq[OF p] have ttp: "t \<unrhd> t |_ p" .
  {
    fix x
    assume x: "x \<in> vars_term (t |_ p)"
    from var_cond have "nfs \<or> vars_term (t |_ p) \<subseteq> vars_term s" by blast
    then have "\<sigma> x \<in> NFQ"
    proof
      assume "vars_term (t |_ p) \<subseteq> vars_term s"
      with x have "x \<in> vars_term s" by auto
      then have "Var x \<unlhd> s" by auto
      then have "Var x \<cdot> \<sigma> \<unlhd> s \<cdot> \<sigma>" by (rule supteq_subst)
      from NF_subterm[OF sNF this]
      show "\<sigma> x \<in> NFQ" by simp
    next
      assume nfs
      from x have "t |_ p \<unrhd> Var x" by auto
      from supteq_trans[OF ttp this]
      have "t \<unrhd> Var x" .
      from subteq_Var_imp_in_vars_term[OF this]
      have "x \<in> vars_term t" .
      with nfs[unfolded NF_subst_def vars_rule_def] \<open>nfs\<close> show ?thesis by auto
   qed
  } 
  then have \<sigma>tp: "\<sigma> ` vars_term (t |_ p) \<subseteq> NFQ" by auto
  from wwf_or_SN have wf: "\<not> nfs \<Longrightarrow> wwf_qtrs Q R \<or> SN_on ?QR {t |_ p \<cdot> \<sigma>}"
    using ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep, of nfs Q R "t \<cdot> \<sigma>", OF _ supteq_subst[OF ttp]] by auto
  let ?\<mu>\<sigma> = "\<mu> \<circ>\<^sub>s \<sigma>"
  have steps1: "(t |_ p \<cdot> \<sigma>, w) \<in> ?QUR\<^sup>*"
    by (rule is_ur_closed_term[OF steps1 \<sigma>tp _ U subset_refl wf usable], insert sNF, auto)
  with subt have steps1: "(l \<cdot> ?\<mu>\<sigma>, w) \<in> ?QUR\<^sup>*" by auto
  obtain \<tau> where \<tau>: "\<tau> \<equiv> \<lambda> x. some_NF (qrstep nfs Q U) (?\<mu>\<sigma> x)" by auto
  have steps1': "(l \<cdot> ?\<mu>\<sigma>, w) \<in> ?QU\<^sup>*"
    by (rule set_mp[OF _ steps1], rule rtrancl_mono, rule qrstep_mono, auto)
  from normalize_subst_qrsteps_inn[OF unf _ steps1' w NF_Q_U]
  have lx: "\<And> x. x \<in> vars_term l \<Longrightarrow> (?\<mu>\<sigma> x, \<tau> x) \<in> ?QU\<^sup>*"
    "\<And> x. x \<in> vars_term l \<Longrightarrow> \<tau> x \<in> NFQ"
    and steps: "(l \<cdot> \<tau>, w) \<in> ?QU\<^sup>*" unfolding \<tau> by blast+
  {
    fix x
    assume "x \<in> vars_term l"
    from lx(2)[OF this] NF_Q_R
    have "\<tau> x \<in> NF_trs R" by auto
  } note \<tau>NF = this
  from lr have "(l \<cdot> \<tau>, r \<cdot> \<tau>) \<in> rstep R" by auto
  then have "l \<cdot> \<tau> \<notin> NF_trs R" by auto
  with NF_Q_R have "l \<cdot> \<tau> \<notin> NFQ" by auto
  with w have lw: "l \<cdot> \<tau> \<noteq> w" by auto
  from rtrancl_imp_relpow[OF steps] obtain n where n: "(l \<cdot> \<tau>, w) \<in> ?QU ^^ n" by auto
  with lw obtain n where "(l \<cdot> \<tau>, w) \<in> ?QU ^^ (Suc n)" by (cases n, auto)
  from relpow_Suc_D2[OF this] obtain v where step: "(l \<cdot> \<tau>, v) \<in> ?QU" and steps: "(v, w) \<in> ?QU ^^ n" by auto
  from relpow_imp_rtrancl[OF steps] have steps: "(v,w) \<in> ?QU\<^sup>*" by auto
  {
    from step obtain l' r' p \<sigma> where step: "(l \<cdot> \<tau>,v) \<in> qrstep_r_p_s nfs Q U (l',r') p \<sigma>" unfolding qrstep_qrstep_r_p_s_conv by auto
    obtain D where D: "D = ctxt_of_pos_term p (l \<cdot> \<tau>)" by auto
    from step have p: "p \<in> poss (l \<cdot> \<tau>)" and
      NF': "\<forall> u \<lhd> l' \<cdot> \<sigma>. u \<in> NFQ"
      and lr': "(l',r') \<in> U"
      and l\<tau>p: "l \<cdot> \<tau> |_ p = l' \<cdot> \<sigma>"
      and v: "v = D\<langle>r' \<cdot> \<sigma>\<rangle>" unfolding qrstep_r_p_s_def D by auto
    from ctxt_supt_id[OF p] have "l \<cdot> \<tau> = D\<langle>l \<cdot> \<tau> |_ p\<rangle>" unfolding D ..
    with l\<tau>p have l\<tau>: "l \<cdot> \<tau> = D\<langle>l' \<cdot> \<sigma>\<rangle>" by simp
    have "v = r \<cdot> \<tau>"
    proof (cases "p \<in> poss l \<and> is_Fun (l |_ p)")
      case False      
      from pos_into_subst[OF l\<tau> p[unfolded l\<tau>] this]
      obtain q q' x where pq: "p = q @ q'" and q: "q \<in> poss l" and x: "l |_ q = Var x" by auto
      from q have q\<tau>: "q \<in> poss (l \<cdot> \<tau>)" by auto
      from l\<tau>p[unfolded pq subt_at_append[OF q\<tau>] subt_at_subst[OF q]]
      have id: "\<tau> x |_ q' = l' \<cdot> \<sigma>" unfolding x by auto
      from p[unfolded pq poss_append_poss subt_at_subst[OF q] x] have q': "q' \<in> poss (\<tau> x)" by auto
      from q' have "\<tau> x \<unrhd> \<tau> x |_ q'" by (rule subt_at_imp_supteq)
      with id have subt: "\<tau> x \<unrhd> l' \<cdot> \<sigma>" by auto
      from q have "l \<unrhd> l |_ q" by (rule subt_at_imp_supteq)
      from this[unfolded x] have "x \<in> vars_term l" by (rule subteq_Var_imp_in_vars_term)
      from \<tau>NF[OF this] have NF: "\<tau> x \<in> NF_trs R" .
      from lr' subset have "(l',r') \<in> R" by auto
      from lhs_notin_NF_rstep[OF this]
        NF_instance[OF NF_subterm[OF NF subt]] show ?thesis by auto
    next
      case True
      then have p: "p \<in> poss l" and isfun: "is_Fun (l |_ p)" by auto
      from l\<tau>p have id: "l |_ p \<cdot> \<tau> = l' \<cdot> \<sigma>" unfolding subt_at_subst[OF p] .
      from ctxt_supt_id[OF p] obtain E where E': "E = ctxt_of_pos_term p l" and E: "E\<langle>l |_ p\<rangle> = l" by auto
      have lr: "(l,r) \<in> {(l,r)}" by auto
      from mgu_vd_string_complete[OF id]
      obtain \<mu>1 \<mu>2 \<mu>3 where mgu: "mgu_vd string_rename (l |_ p) l' = Some (\<mu>1,\<mu>2)" 
        and \<tau>: "\<tau> = \<mu>1 \<circ>\<^sub>s \<mu>3" and \<sigma>: "\<sigma> = \<mu>2 \<circ>\<^sub>s \<mu>3" by (auto simp: mgu_vd_string_def)
      from crit_pairs[OF critical_pairsI[OF lr lr' E[symmetric] isfun mgu refl refl refl]]
      have id: "r \<cdot> \<mu>1 = (E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>" ..
      have id2: "D = E \<cdot>\<^sub>c \<mu>1 \<cdot>\<^sub>c \<mu>3" unfolding D E'
        unfolding ctxt_of_pos_term_subst[OF p]  \<tau> by simp
      show "v = r \<cdot> \<tau>" 
        unfolding v \<sigma> \<tau> subst_subst_compose id
        subst_apply_term_ctxt_apply_distrib id2 by simp
    qed
  } 
  then have vr\<tau>: "v = r \<cdot> \<tau>" .
  have lsteps: "(l \<cdot> ?\<mu>\<sigma>, l \<cdot> \<tau>) \<in> ?QU\<^sup>*"
    by (rule all_ctxt_closed_subst_step[OF _ lx(1)], auto)
  with step[unfolded vr\<tau>] have lsteps: "(l \<cdot> \<mu> \<cdot> \<sigma>, r \<cdot> \<tau>) \<in> ?QU\<^sup>*" by auto
  from var_cond_2 have var_cond: "\<And> x. x \<in> vars_term r \<Longrightarrow> x \<in> vars_term l" by auto
  have rsteps: "(r \<cdot> ?\<mu>\<sigma>, r \<cdot> \<tau>) \<in> ?QU\<^sup>*"
    by (rule all_ctxt_closed_subst_step[OF _ lx(1)[OF var_cond]], auto)
  from rtrancl_mono[OF qrstep_mono[OF subset subset_refl]] have subsetUR: "?QU\<^sup>* \<subseteq> ?QR\<^sup>*" by simp
  from rsteps steps[unfolded vr\<tau>] have "(r \<cdot> \<mu> \<cdot> \<sigma>, w) \<in> ?QU\<^sup>*" by auto
  with subsetUR have steps: "(r \<cdot> \<mu> \<cdot> \<sigma>, w) \<in> ?QR\<^sup>*" by auto
  have t'\<sigma>: "t' \<cdot> \<sigma> = replace_at (t \<cdot> \<sigma>) p (r \<cdot> \<mu> \<cdot> \<sigma>)" unfolding t' ctxt_of_pos_term_subst[OF p] by simp
  have first_part: "(t' \<cdot> \<sigma>, u) \<in> ?QR\<^sup>*" unfolding t'\<sigma> 
    by (rule rtrancl_trans[OF _ steps2], 
      rule ctxt.closedD[OF _ steps], blast)
  show ?thesis
  proof (rule conjI[OF first_part], intro impI)
    assume SN: "SN_on ?QR {t \<cdot> \<sigma>}"
    with ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep, of nfs Q R "t \<cdot> \<sigma>", OF _ supteq_subst[OF ttp]] have SN_l: "SN_on ?QR {l \<cdot> \<mu> \<cdot> \<sigma>}" unfolding subt by auto 
    {
      fix x
      assume x: "x \<in> vars_term r"
      have subt_lx: "l \<cdot> \<mu> \<unrhd> Var x \<cdot> \<mu>" 
        by (rule supteq_subst, insert var_cond[OF x], auto)
    } note subt_lx = this
    {
      fix x
      assume x: "x \<in> vars_term r"
      from ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep, of nfs Q R "l \<cdot> \<mu> \<cdot> \<sigma>", OF SN_l supteq_subst[OF subt_lx[OF x]]]
      have "SN_on ?QR {Var x \<cdot> \<mu> \<cdot> \<sigma>}" .
    } note SN_x = this
    {
      fix x u
      assume x: "x \<in> vars_term r" and steps: "(?\<mu>\<sigma> x, u) \<in> ?QR\<^sup>*"
      from steps have steps: "(Var x \<cdot> \<mu> \<cdot> \<sigma>, u) \<in> ?QR\<^sup>*" unfolding subst_compose_def by auto
      from \<sigma>tp[unfolded subt vars_term_subst] var_cond[OF x] have NF: "\<sigma> ` vars_term (Var x \<cdot> \<mu>) \<subseteq> NFQ" by auto
      have usable: "is_ur_closed_term_mv full_af {s} (Var x \<cdot> \<mu>)"
        by (rule is_ur_closed_mv_subt[OF subt_lx[OF x] usable[unfolded subt]]) 
      from SN_x[OF x] have wf: "wwf_qtrs Q R \<or> SN_on ?QR {Var x \<cdot> \<mu> \<cdot> \<sigma>}" ..
      from is_ur_closed_term[OF steps NF _ U subset_refl wf usable] sNF
      have "(Var x \<cdot> \<mu> \<cdot> \<sigma>, u) \<in> (qrstep nfs Q (R \<inter> U))\<^sup>*" by simp
      then have "(Var x \<cdot> ?\<mu>\<sigma>, u) \<in> ?QU\<^sup>*"
        using rtrancl_mono[OF qrstep_mono[of "(R \<inter> U)" U Q, OF _ subset_refl]] by (auto simp: subst_compose)
      then have "(?\<mu>\<sigma> x, u) \<in> ?QU\<^sup>*" unfolding subst_compose_def by auto
    } note x_R_U = this
    show "SN_on ?QR {t' \<cdot> \<sigma>}" unfolding t'\<sigma>
    proof (rule normalize_subterm_SN)
      show "SN_on ?QR {r \<cdot> \<mu> \<cdot> \<sigma>}" 
      proof (rule ccontr)
        assume "\<not> SN_on ?QR {r \<cdot> \<mu> \<cdot> \<sigma>}"
        then have nSN: "\<not> SN_on ?QR {r \<cdot> ?\<mu>\<sigma>}" by simp
        from SN_x have SN_x: "\<And> x. x \<in> vars_term r \<Longrightarrow> SN_on ?QR {?\<mu>\<sigma> x}" 
          unfolding subst_compose_def by auto
        from normalize_subst_qrsteps_inn_infinite[OF unf x_R_U nSN SN_x NF_Q_U]
        have nSN: "\<not> SN_on ?QR {r \<cdot> \<tau>}" unfolding \<tau> by blast+
        from steps_preserve_SN_on[OF _ SN_l] lsteps subsetUR have "SN_on ?QR {r \<cdot> \<tau>}" by auto
        with nSN show False by simp
      qed
    next
      fix v
      assume rv: "(r \<cdot> \<mu> \<cdot> \<sigma>, v) \<in> ?QR\<^sup>*" and v: "v \<in> NFQ"
      then have rv': "(r \<cdot> ?\<mu>\<sigma>,v) \<in> ?QR\<^sup>*" by auto
      have r\<tau>v: "(r \<cdot> \<tau>, v) \<in> ?QR\<^sup>*" unfolding \<tau>
        using normalize_subst_qrsteps_inn[OF unf x_R_U rv' v NF_Q_U] by auto
      with lsteps subsetUR have lsteps: "(l \<cdot> \<mu> \<cdot> \<sigma>, v) \<in> ?QR\<^sup>*" by auto
      have "t \<cdot> \<sigma> = replace_at (t \<cdot> \<sigma>) p (t \<cdot> \<sigma> |_p)"
        by (rule ctxt_supt_id[symmetric], rule pt\<sigma>)
      also have "... = replace_at (t \<cdot> \<sigma>) p (t |_p \<cdot> \<sigma>)"
        using p by auto
      also have "... = replace_at (t \<cdot> \<sigma>) p (l \<cdot> \<mu> \<cdot> \<sigma>)" unfolding subt ..
      also have "(..., replace_at (t \<cdot> \<sigma>) p v) \<in> ?QR\<^sup>*"
        by (rule ctxt.closedD[OF _ lsteps], blast)
      finally have "(t \<cdot> \<sigma>, replace_at (t \<cdot> \<sigma>) p v) \<in> ?QR\<^sup>*" .
      from steps_preserve_SN_on[OF this SN] show "SN_on ?QR {replace_at (t \<cdot> \<sigma>) p v}" .
    next
      show "SN_on ?QR (set (ctxt_to_term_list (ctxt_of_pos_term p (t \<cdot> \<sigma>))))"
        by (rule SN_ctxt_apply_imp_SN_ctxt_to_term_list_gen[OF ctxt_closed_qrstep, where t = "(t \<cdot> \<sigma>) |_ p"], unfold ctxt_supt_id[OF \<open>p \<in> poss (t \<cdot> \<sigma>)\<close>], rule SN)
    qed
  qed
qed

lemma rewriting_complete: 
  assumes common: "rewrite_common_preconditions s (args s) (args (t |_ p)) t t' (l,r) p nfs False"
  and rewrite: "(t,t') \<in> rstep_r_p_s R (l,r) p \<mu>"
  and steps: "(t' \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>*"
  and uNF: "set (args u) \<subseteq> NFQ"
  and sNF: "set (args (s \<cdot> \<sigma>)) \<subseteq> NFQ"
  and sFun: "is_Fun s"
  and nfc: "\<And> v. t |_ p \<rhd> v \<Longrightarrow> nfc R Q (set (args s)) v nfs"
  and SNqr: "SN (qrstep nfs Q R)"
  and wwf: "\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  and ndef: "is_Fun t \<Longrightarrow> \<not> defined R (the (root t))"
  shows "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>*"
proof -      
  let ?QR = "qrstep nfs Q R"
  let ?QU = "qrstep nfs Q U"
  let ?QUR = "qrstep nfs Q (R \<inter> U)"
  note common = common[unfolded rewrite_common_preconditions_def if_False]
  from common have
      subset: "U \<subseteq> R"
  and var_cond: "vars_term (t |_ p) \<subseteq> vars_term s"
  and wf_lr: "wf_rule (l,r)"
  and usable: "\<forall> t \<in> set (args (t |_ p)). is_ur_closed_term_mv full_af (set (args s)) t"
  and crit_pairs: "\<And> b s t. (b,s,t) \<in> critical_pairs string_rename {(l,r)} U \<Longrightarrow> s = t"
  and unf: "UNF (qrstep nfs Q U)"
  and U: "\<And> l r. (l,r) \<in> U \<Longrightarrow> is_ur_closed_term_mv full_af (set (args l)) r"
  by auto
  from wf_lr have var_cond_2: "vars_term r \<subseteq> vars_term l" and var_cond_3: "is_Fun l"
    unfolding wf_rule_def by auto
  have "NFQ \<subseteq> NF_trs R" by (rule NF_Q_R)
  also have "... \<subseteq> NF_trs U" by (rule NF_trs_mono[OF subset])
  finally have NF_Q_U: "NFQ \<subseteq> NF_trs U" . 
  {
    fix l r
    assume lr: "(l,r) \<in> R"
    have "is_Fun l"
    proof (cases nfs)
      case True
      from wwf[OF this lr] show ?thesis .
    next
      case False
      from SNqr have "SN_on ?QR {r}" unfolding SN_def ..
      with lr left_Var_imp_not_SN_qrstep[OF _ False, of _ r R Q r]
      show ?thesis by (cases l, auto)
    qed
  } note wwf = this
  from rewrite[unfolded rstep_r_p_s_def'] 
  have p: "p \<in> poss t" and lr: "(l,r) \<in> R" and subt: "t |_ p = l \<cdot> \<mu>"
    and t': "t' = replace_at t p (r \<cdot> \<mu>)" by auto
  then have t: "t = replace_at t p (l \<cdot> \<mu>)" using ctxt_supt_id by force
  from replace_at_subt_at[of p t "r \<cdot> \<mu>"] p  
  have "(ctxt_of_pos_term p t)\<langle>r \<cdot> \<mu>\<rangle> |_ p = r \<cdot> \<mu>" .
  with t' have subt': "t' |_ p = r \<cdot> \<mu>" by auto
  from p replace_at_below_poss t' order_refl have pt': "p \<in> poss t'" by auto
  then have pt'\<sigma>: "p \<in> poss (t' \<cdot> \<sigma>)" by auto
  {
    from wwf[OF lr] have lf: "is_Fun l" .
    with lr have "defined R (the (root l))" unfolding defined_def by (cases l, auto)
    with ndef have neq: "is_Fun t \<Longrightarrow> root l \<noteq> root t" by auto
    have pe: "p \<noteq> []"
    proof (cases p)
      case Nil
      with subt have id: "t = l \<cdot> \<mu>" by auto
      from neq[unfolded arg_cong[OF id, of root] id] have False using lf by (cases l, auto)
      then show ?thesis by auto
    qed auto
    then obtain j pp where pjpp: "p = j # pp" by (cases p, auto)
    with p obtain f ts where tts: "t = Fun f ts" and j: "j < length ts" by (cases t, auto)
    from t have id: "root (t' \<cdot> \<sigma>) = root t" "root t' = root t" "is_Fun t" unfolding t' tts pjpp using j by auto
    from qrsteps_imp_nrqrsteps[OF _ ndef_applicable_rules steps, unfolded id, OF _ ndef] wwf
    have steps: "(t' \<cdot> \<sigma>, u) \<in> (nrqrstep nfs Q R)\<^sup>*" unfolding tts by auto
    note steps id pe
  } note steps_id = this
  note steps = steps_id(1)
  from steps_id(2-4) obtain f ts ts' where tts: "t = Fun f ts" and tts': "t' = Fun f ts'" 
    by (cases t, auto, cases t', auto)
  from steps_id(2) tts tts' have lts: "length ts' = length ts" by auto
  from lts nrqrsteps_preserve_root[OF steps, unfolded tts'] obtain us where u: "u = Fun f us" 
    and lus: "length us = length ts" by (cases u, auto)
  have "(t \<cdot> \<sigma>, u) \<in> (nrqrstep nfs Q R)\<^sup>*" unfolding u tts eval_term.simps
  proof (rule args_steps_imp_nrqrsteps)
    fix i
    assume i: "i < length us"
    have idd: "t |_ p = Fun f ts |_ p" "t' |_ p = Fun f ts' |_ p" unfolding tts tts' by auto
    define u t t' where "u = us ! i" and "t = ts ! i" and "t' = ts' ! i"
    from i have id: "map (\<lambda>t. t \<cdot> \<sigma>) ts ! i = t \<cdot> \<sigma>" "us ! i = u" unfolding u_def t_def lus by auto    
    from nrqrsteps_imp_arg_qrsteps[OF steps, of i, unfolded tts' u]
    have steps: "(t' \<cdot> \<sigma>, u) \<in> ?QR\<^sup>*" using i unfolding u_def t'_def using lus lts by auto
    from uNF[unfolded u] have uNF: "u \<in> NFQ" unfolding u_def using i lus by auto
    from steps_id(5) obtain j pp where pjpp: "p = j # pp" by (cases p, auto)
    with p[unfolded tts] have jts: "j < length ts" by auto
    then have min: "min (length ts) j = j" by simp
    show "(map (\<lambda>t. t \<cdot> \<sigma>) ts ! i, us ! i) \<in> ?QR\<^sup>*" unfolding id
    proof (cases "i = j")
      case False
      then have "i < j \<or> j < i" by arith
      then have "t = t'" unfolding t'_def t_def
      proof 
        assume "i < j"
        then have "\<exists> k. j = Suc i + k" by presburger
        then obtain k where j: "j = Suc i + k" ..
        show "ts ! i = ts' ! i" using t t' jts unfolding tts' tts pjpp j
          by (auto simp: nth_append)
      next
        assume "j < i"
        then have "\<exists> k. i = Suc j + k" by presburger
        then obtain k where i: "i = Suc j + k" .. 
        then show "ts ! i = ts' ! i" using min t t' \<open>i < length us\<close> unfolding tts' tts pjpp i lus
          by (auto simp: nth_append)
      qed
      with steps show "(t \<cdot> \<sigma>, u) \<in> ?QR\<^sup>*" by simp
    next
      case True
      (* first rename subterms and new position to same names *)
      have "Fun f ts |_ p = t |_ pp" "Fun f ts' |_ p = t' |_ pp" unfolding t_def t'_def pjpp True by auto
      note idd = idd[unfolded this]
      from pt'\<sigma> have pt'\<sigma>: "pp \<in> poss (t' \<cdot> \<sigma>)" unfolding pjpp tts' t'_def True by auto
      from p have p: "pp \<in> poss t" unfolding pjpp tts t_def True by auto
      from pt' have pt': "pp \<in> poss t'" unfolding pjpp tts' t'_def True by auto
      note subt = subt[unfolded idd]
      note subt' = subt'[unfolded idd]
      note usable = usable[unfolded idd]
      note var_cond = var_cond[unfolded idd]
      note nfc = nfc[unfolded idd]
      from arg_cong[OF t', of "\<lambda> t. args t ! i"] have t': "t' = (ctxt_of_pos_term pp t)\<langle>r \<cdot> \<mu>\<rangle>" 
        unfolding t_def t'_def tts' tts pjpp True by (auto simp: nth_append min)
      from ctxt_supt_id[OF p] subt have t: "t = (ctxt_of_pos_term pp t)\<langle>l \<cdot> \<mu>\<rangle>" by auto
      (* now formalize paper proof where now u is a NF, and not only all subterms *)
      from normalize_subterm_qrsteps[OF pt'\<sigma> steps uNF] obtain w
        where steps1: "(t' \<cdot> \<sigma> |_ pp, w) \<in> ?QR\<^sup>*" 
        and w: "w \<in> NFQ" 
        and steps2: "(replace_at (t' \<cdot> \<sigma>) pp w, u) \<in> ?QR\<^sup>*" by auto
      from steps1 pt' have steps1: "(t' |_ pp \<cdot> \<sigma>, w) \<in> ?QR\<^sup>*" by simp
      let ?\<mu>\<sigma> = "\<mu> \<circ>\<^sub>s \<sigma>"
      obtain \<tau> where \<tau>: "\<tau> \<equiv> \<lambda> x. some_NF ?QU (?\<mu>\<sigma> x)" by auto
      from subt' steps1 have steps1: "(r \<cdot> ?\<mu>\<sigma>, w) \<in> ?QR\<^sup>*" by auto
      from sFun obtain f ss where s: "s = Fun f ss" by (cases s, auto)
      {
        fix y
        assume "y \<in> vars_term s"
        then obtain si where si: "si \<in> set (args s)" and y: "y \<in> vars_term si"
          unfolding s by auto
        from si sNF have si: "si \<cdot> \<sigma> \<in> NFQ" unfolding s by auto
        from y have "Var y \<unlhd> si" by auto
        then have "\<sigma> y \<unlhd> si \<cdot> \<sigma>" by auto
        from NF_subterm[OF si this] have "\<sigma> y \<in> NFQ" .
      } note s_var_NF = this
      {
        fix x u
        assume 1:"x \<in> vars_term r" and 2:"((\<mu> x) \<cdot> \<sigma>, u) \<in> ?QR\<^sup>*"
        with var_cond_2 have "x \<in> vars_term l" by auto
        with var_cond_3 obtain li where li: "li \<in> set (args l)" and "x \<in> vars_term li" by (cases l, auto)
        then have supt: "li \<cdot> \<mu> \<unrhd> \<mu> x " using supteq_subst vars_term_supteq(1) by force
        from li usable[unfolded subt] have "is_ur_closed_term_mv full_af (set (args s)) (li \<cdot> \<mu>)"
          using var_cond_3 by (cases l, auto)
        from is_ur_closed_mv_subt[OF supt this]
        have urc_mux:"is_ur_closed_term_mv full_af (set (args s)) (\<mu> x)" .
        from SNqr have wf: "\<not> nfs \<Longrightarrow> wwf_qtrs Q R \<or> SN_on ?QR {(\<mu> x) \<cdot> \<sigma>}"
          using SN_def[of ?QR] by auto
        {
          fix y
          assume y:"y \<in> vars_term (\<mu> x)"
          have "vars_term (\<mu> x) \<subseteq> vars_term (r \<cdot> \<mu>)" using var_cond_stable[of "Var x" r \<mu>] 1 by simp
          also have "... \<subseteq> vars_term (l \<cdot> \<mu>)" using var_cond_2 var_cond_stable by fast
          also have "... \<subseteq> vars_term s" using var_cond subt by auto
          finally have "vars_term (\<mu> x) \<subseteq> vars_term s" .
          with y have  "y \<in> vars_term s" by auto
          from s_var_NF[OF this]
          have "\<sigma> y \<in> NFQ" .
        } 
        then have smuxNFQ: "\<sigma> ` vars_term (\<mu> x) \<subseteq> NFQ" by auto
        have xQUR:"((\<mu> x) \<cdot> \<sigma>, u) \<in> ?QUR\<^sup>*" 
          by (rule is_ur_closed_term[OF 2 smuxNFQ _ U subset_refl wf urc_mux], insert sNF s, auto) 
        from subset have "R \<inter> U = U" by blast
        then have "?QUR = ?QU" by auto
        with xQUR have "((\<mu> x) \<cdot> \<sigma>, u) \<in> ?QU\<^sup>*" by force
      }
      with normalize_subst_qrsteps_inn[OF unf _ steps1 w NF_Q_U]
      have rx: "\<And> x. x \<in> vars_term r \<Longrightarrow> (?\<mu>\<sigma> x, \<tau> x) \<in> ?QU\<^sup>*"
        "\<And> x. x \<in> vars_term r \<Longrightarrow> \<tau> x \<in> NFQ" 
        and steps: "(r \<cdot> \<tau>, w) \<in> ?QR\<^sup>*"unfolding \<tau> subst_compose_def by blast+
      {
        fix x
        assume "x \<in> vars_term r"
        from rx(2)[OF this] NF_Q_R
        have "\<tau> x \<in> NF_trs R" by auto
        then have "\<tau> x \<in> NF ?QR" by blast
      } note \<tau>NF = this
      {
        fix x :: string
        from SNqr have "SN_on ?QR {?\<mu>\<sigma> x}" unfolding SN_def ..
        from SN_reaches_NF[OF this]
        have "\<exists> v. (?\<mu>\<sigma> x,v) \<in> ?QR\<^sup>* \<and> v \<in> NF ?QR" .
      }
      then have "\<forall> x. \<exists> v. (?\<mu>\<sigma> x, v) \<in> ?QR\<^sup>* \<and> v \<in> NF ?QR" by auto
      from choice[OF this] obtain \<nu> where \<nu>:"\<forall>x. (?\<mu>\<sigma> x, \<nu> x) \<in> ?QR\<^sup>* \<and> \<nu> x \<in> NF ?QR" 
        by auto 
      then obtain \<delta> where \<delta>:"\<delta> \<equiv> \<lambda> x. if x \<in> vars_term r then \<tau> x else \<nu> x"
        by auto
      then have \<tau>\<delta>:"\<And> z. z \<in> vars_term r \<Longrightarrow> \<delta> z = \<tau> z" unfolding \<delta> \<tau> by auto
      with steps have steps:"(r \<cdot> \<delta>, w) \<in> ?QR\<^sup>*" using term_subst_eq_conv[of r \<delta> \<tau>] by auto
      {
        fix x
        assume "x \<in> vars_term l"
        have "(?\<mu>\<sigma> x, \<delta> x) \<in> ?QR\<^sup>*" proof (cases "x \<in> vars_term r")
          case True
          show ?thesis using \<tau>\<delta>[OF True]  rx(1)[OF True]
            in_mono rtrancl_mono[OF qrstep_rules_mono[OF subset]] by force
        next
          case False
          then have "\<delta> x = \<nu> x" using \<delta> by auto
          with \<nu> show ?thesis by auto
        qed
      } note l\<delta> = this
      then have lsteps:"(l \<cdot> ?\<mu>\<sigma>,l \<cdot> \<delta>) \<in> ?QR\<^sup>*" using subst_qrsteps_imp_qrsteps by blast 
      {
        fix p'
        assume lp':"p' \<in> poss l"
        have "((l \<cdot> \<delta>) |_ p' \<in> NFQ) \<or> 
          (\<exists> p rl \<sigma>.(l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> qrstep_r_p_s nfs Q R rl p \<sigma> \<and> p' \<le>\<^sub>p p)"
          using lp' 
        proof (induction "l |_ p'" arbitrary: p')
          case (Var x)
          from subst_qrsteps_imp_qrsteps_at_pos[OF Var(2), of ?\<mu>\<sigma> \<delta>] 
          have lp'steps: "(l |_ p'\<cdot> ?\<mu>\<sigma>,l |_ p' \<cdot> \<delta>) \<in> ?QR\<^sup>*" using l\<delta>  by auto
          show ?case proof (cases "p' = []")
            case True
            then have "l |_ p' = l" by auto
            with Var have "l = Var x" by auto
            then show ?thesis using var_cond_3 by auto
          next
            case False
            from Var(2) False have strict:"l \<rhd> (l |_ p')" 
              using subt_at_id_imp_eps[OF Var(2)] subt_at_imp_supteq subterm.le_less by auto
            with subt have "(t |_ pp) \<rhd> (l |_ p') \<cdot> \<mu>" 
              using instance_no_supt_imp_no_supt by auto
            from nfc[OF this] have "nfc R Q (set (args s)) ((l |_ p') \<cdot> \<mu>) nfs" .
            then have "\<forall>\<sigma> u.  (set (args s)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ \<longrightarrow>
              u \<in> NF ?QR \<and> (l |_ p' \<cdot> \<mu> \<cdot> \<sigma>, u) \<in> ?QR\<^sup>* \<longrightarrow>
              u \<in> NFQ" unfolding nfc_def .
            from spec[OF spec[OF this, of \<sigma>], of "(l |_ p') \<cdot> \<delta>"] have
              nf:"(set (args s)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ \<longrightarrow>
              l |_ p' \<cdot> \<delta> \<in> NF (qrstep nfs Q R) \<and>
              (l |_ p' \<cdot> \<mu> \<cdot> \<sigma>, l |_ p' \<cdot> \<delta>) \<in> ?QR\<^sup>* \<longrightarrow>
              l |_ p' \<cdot> \<delta> \<in> NFQ" .
            moreover from sNF have "(set (args s)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" unfolding s by auto
            moreover from lp'steps have "(l |_ p' \<cdot> \<mu> \<cdot> \<sigma>, l |_ p' \<cdot> \<delta>) \<in> ?QR\<^sup>*" 
              using  subst_subst by auto
            moreover have "l |_ p' \<cdot> \<delta> \<in> NF ?QR" using Var \<delta> \<nu> \<tau>NF by auto
            ultimately have "l |_ p' \<cdot> \<delta> \<in> NFQ" by auto
            then show ?thesis using subt_at_subst[OF Var(2), of \<delta>] by auto
          qed
        next
          case (Fun f ls)
          from subst_qrsteps_imp_qrsteps_at_pos[OF Fun(3), of ?\<mu>\<sigma> \<delta>] 
          have lp'steps: "(l |_ p'\<cdot> ?\<mu>\<sigma>,l |_ p' \<cdot> \<delta>) \<in> ?QR\<^sup>*" using l\<delta>  by auto
          {
            fix i         
            assume i:"i < length ls"
            then have "l |_ (p' @ [i]) \<in> set ls" using Fun subt_at_append nth_mem by auto
            moreover with i Fun(3) Fun(2) have "(p' @ [i]) \<in> poss l" by simp
            ultimately have ih:"l \<cdot> \<delta> |_ (p' @ [i]) \<in> NFQ \<or>
              (\<exists>p rl \<sigma>. (l \<cdot> \<delta>, r \<cdot> \<delta>)
              \<in> qrstep_r_p_s nfs Q R rl p \<sigma> \<and> (p' @ [i]) \<le>\<^sub>p p)" 
              using Fun(1) by blast
            then have "l \<cdot> \<delta> |_ (p' @ [i]) \<in> NFQ  \<or>
              (\<exists>p rl \<sigma>. (l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> qrstep_r_p_s nfs Q R rl p \<sigma> \<and> p' \<le>\<^sub>p p)" 
            proof (rule disjE, clarsimp)
              assume a:"\<exists>p rl \<sigma>. (l \<cdot> \<delta>, r \<cdot>
              \<delta>) \<in> qrstep_r_p_s nfs Q R rl p \<sigma> \<and> p' @ [i] \<le>\<^sub>p p"
              have "p' \<le>\<^sub>p p' @ [i]" by auto          
              with a have "(\<exists>p rl \<sigma>. (l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> qrstep_r_p_s nfs Q R rl p \<sigma> \<and> p' \<le>\<^sub>p p)"
                using order_pos.order_trans by blast
              then show ?thesis by auto
            qed
          }
          then have "(\<exists>p rl \<sigma>. (l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> qrstep_r_p_s nfs Q R rl p \<sigma> \<and> p' \<le>\<^sub>p p) \<or>
            (\<forall> i < length ls. l \<cdot> \<delta> |_ (p' @ [i]) \<in> NFQ)" by auto
          then show "l \<cdot> \<delta> |_ p' \<in> NFQ \<or>
            (\<exists>p rl \<sigma>. (l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> qrstep_r_p_s nfs Q R rl p \<sigma> \<and> p' \<le>\<^sub>p p)" 
          proof (rule disjE, force)
            assume strat:"\<forall>i<length ls. l \<cdot> \<delta> |_ (p' @ [i]) \<in> NFQ"
            show ?thesis 
            proof (cases p')
              case Nil
              show ?thesis unfolding Nil
              proof (rule disjI2, intro exI conjI)
                {
                  fix u
                  assume "u \<in> set (args (l \<cdot> \<delta>))"
                  then have "u \<in> NFQ" using strat Fun(2)[symmetric]
                    unfolding Nil by (auto simp: set_conv_nth)
                } note args = this
                {
                  fix x
                  assume "x \<in> vars_rule (l,r)"
                  with var_cond_2 have "x \<in> vars_term l" unfolding vars_rule_def by auto
                  with var_cond_3 obtain li where x: "x \<in> vars_term li" and li: "li \<cdot> \<delta> \<in> set (args (l \<cdot> \<delta>))" by (cases l, auto)
                  from x have "li \<unrhd> Var x" by auto
                  from NF_subterm[OF args[OF li]  supteq_subst[OF this, of \<delta>]]
                  have "\<delta> x \<in> NFQ" by auto
                } note vars = this
                show "(l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> qrstep_r_p_s nfs Q R (l,r) [] \<delta>"
                  unfolding qrstep_r_p_s_def NF_rstep_supt_args_conv
                  using \<open>(l,r) \<in> R\<close> args vars
                  by (auto simp: NF_subst_def)
              qed auto
            next
              case (Cons i p'')
              show ?thesis
              proof (cases "\<exists> w rl \<sigma>. (l \<cdot> \<delta>, w) \<in> qrstep_r_p_s nfs Q R rl p' \<sigma>")
                case True
                then obtain w l' r' \<rho>
                  where True: "(l \<cdot> \<delta>, w) \<in> qrstep_r_p_s nfs Q R (l',r') p' \<rho>" by auto
                obtain D where D: "D = ctxt_of_pos_term p' (l \<cdot> \<delta>)" by auto
                with True have
                  p': "p' \<in> poss (l \<cdot> \<delta>)" and
                  NF': "\<forall> u \<lhd> l' \<cdot> \<rho>. u \<in> NFQ"
                  and lr': "(l',r') \<in> R"
                  and l\<delta>p: "l \<cdot> \<delta> |_ p' = l' \<cdot> \<rho>"
                  and w: "w = D\<langle>r' \<cdot> \<rho>\<rangle>"
                  and nsubs:"NF_subst nfs (l', r') \<rho> Q"
                  unfolding qrstep_r_p_s_def D by auto
                then have id:"l |_ p' \<cdot> \<delta> = l' \<cdot> \<rho>" using Fun(3) by simp
                from Fun have p: "p' \<in> poss l" and isfun: "is_Fun (l |_ p')" by auto
                from ctxt_supt_id[OF p] obtain E where E': "E = ctxt_of_pos_term p' l"
                  and E: "E\<langle>l |_ p'\<rangle> = l" by auto
                have lr: "(l,r) \<in> {(l,r)}" by auto
                from lp'steps subt p have *:"(t |_ pp |_ p' \<cdot> \<sigma>, l \<cdot> \<delta> |_ p') \<in> ?QR\<^sup>*" by simp
                from sNF have sNF:"set (args s) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" using s by auto
                from True qrstep_subt_at have p'step:"(l \<cdot> \<delta> |_ p', w |_ p') \<in> qrstep_r_p_s nfs Q R (l', r') [] \<rho>" by auto
                have lr': "(l',r') \<in> U"
                proof (rule is_ur_closed_term_last[of _ \<sigma>, OF * _ sNF U _ _ _ p'step])
                  have p'tp: "p' \<in> poss (t |_ pp)" using p subt by auto
                  from subt_at_nepos_neq p'tp Cons have **: "(t |_ pp) |_ p' \<noteq> (t |_ pp)" by blast
                  from subt_at_imp_supteq[OF p'tp] 
                  obtain ti where "ti \<in> set (args (t |_ pp))" and "ti \<unrhd> t |_ pp |_ p'"
                    by(rule supteq.cases, auto simp add: **)
                  with usable is_ur_closed_mv_subt show "is_ur_closed_term_mv full_af (set (args s)) (t |_pp |_ p')" by blast
                  {
                    fix x
                    assume "x \<in> vars_term (t |_ pp |_ p')"
                    with var_cond p'tp have "x \<in> vars_term s" using vars_ctxt_pos_term by blast
                    from s_var_NF[OF this] have "\<sigma> x \<in> NFQ" .
                  }
                  then show "\<sigma> ` vars_term (t |_ pp |_ p') \<subseteq> NFQ" by auto
                qed (insert SNqr, auto simp: SN_def)
                from mgu_vd_string_complete[OF id]
                obtain \<mu>1 \<mu>2 \<mu>3 where
                  mgu: "mgu_vd string_rename (l |_ p') l' = Some (\<mu>1,\<mu>2)"
                  and \<delta>: "\<delta> = \<mu>1 \<circ>\<^sub>s \<mu>3" and \<rho>: "\<rho> = \<mu>2 \<circ>\<^sub>s \<mu>3" by (auto simp: mgu_vd_string_def)
                from crit_pairs[OF critical_pairsI[OF lr lr'
                  E[symmetric] isfun mgu refl refl refl]]
                have id: "r \<cdot> \<mu>1 = (E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>" ..
                have id2: "D = E \<cdot>\<^sub>c \<mu>1 \<cdot>\<^sub>c \<mu>3" unfolding D E'
                  unfolding ctxt_of_pos_term_subst[OF p]  \<delta> by simp
                have "w = r \<cdot> \<delta>" unfolding w \<rho> \<delta> subst_subst_compose id
                  subst_apply_term_ctxt_apply_distrib id2 ..
                with True show ?thesis using order_refl[of p'] by auto
              next
                case False
                from strat NF_Q_R have lsnf:"\<forall>i<length ls. l \<cdot>
                \<delta> |_ (p' @ [i]) \<in> NF ?QR"
                  using NF_anti_mono[OF qrstep_subset_rstep] in_mono by force
                from Fun(3) have pshifte:"l \<cdot> \<delta> |_ p' = l |_ p' \<cdot> \<delta>" by auto
                have len_ls: "length ls = length (args (l \<cdot> \<delta> |_ p'))"
                  using pshifte Fun(2)[symmetric] by auto
                have lnf:"(l \<cdot> \<delta>) |_p' \<in> NF ?QR"
                proof (rule ccontr)
                  assume "\<not> ?thesis"
                  then obtain u where u:"((l \<cdot> \<delta>) |_p', u) \<in> ?QR" by blast
                  from this[unfolded qrstep_iff_rqrstep_or_nrqrstep]
                  show False
                  proof
                    assume "((l \<cdot> \<delta>) |_p', u) \<in> rqrstep nfs Q R"
                    then obtain rl \<xi>  where "((l \<cdot> \<delta>) |_p', u) \<in> qrstep_r_p_s nfs Q R rl [] \<xi>"
                      unfolding qrstep_r_p_s_def by (rule rqrstepE, auto+)
                    then have "\<exists> z. (l \<cdot> \<delta>, z) \<in> qrstep_r_p_s nfs Q R rl p' \<xi>" unfolding qrstep_r_p_s_def using Fun(3) by auto
                    with False show ?thesis by blast
                  next
                    assume "((l \<cdot> \<delta>) |_p', u) \<in> nrqrstep nfs Q R"
                    from nrqrstep_imp_arg_qrstep[OF this] obtain i
                      where i1: "i<length (args (l \<cdot> \<delta> |_ p'))" and i2:"(args (l \<cdot> \<delta> |_ p') ! i, args u ! i) \<in> ?QR" by auto
                    from Fun(2) pshifte have ls\<delta>: "l \<cdot> \<delta> |_ p' = (Fun f ls) \<cdot> \<delta>" by auto
                    with Fun(3) have args:"args (l \<cdot> \<delta> |_ p') = map (\<lambda>t. t \<cdot> \<delta>) ls" by auto
                    from len_ls i1 have i1': "i<length ls" by simp
                    with lsnf have "l \<cdot> \<delta> |_ (p' @ [i]) \<in> NF ?QR" by blast
                    moreover have "args (l \<cdot> \<delta> |_ p') ! i = l
                    \<cdot> \<delta> |_ (p' @ [i])"
                      using subt_at_append[OF poss_imp_subst_poss[OF Fun(3)], of \<delta> "[i]"] ls\<delta> by simp
                    ultimately show ?thesis using i2 by auto
                  qed
                qed
                from Cons have notE: "p' \<noteq> []" by auto
                with Fun(3) have strict:"l \<rhd> (l |_ p')"
                  using subt_at_id_imp_eps[OF Fun(3)] subt_at_imp_supteq subterm.le_less 
                  by auto
                with subt have "t |_ pp \<rhd> l |_ p' \<cdot> \<mu>" 
                  using instance_no_supt_imp_no_supt by auto
                from nfc[OF this] have "nfc R Q (set (args s)) (l |_ p' \<cdot> \<mu>) nfs" by auto
                then have "\<forall>\<sigma> u. (set (args s)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ \<longrightarrow>
                  u \<in> NF ?QR \<and> (l |_ p' \<cdot> \<mu> \<cdot> \<sigma>, u) \<in> ?QR\<^sup>* \<longrightarrow>
                  u \<in> NFQ" unfolding nfc_def .
                from spec[OF spec[OF this, of \<sigma>], of "l |_ p' \<cdot> \<delta>"] have
                  nf:"(set (args s)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ \<longrightarrow>
                  l |_ p' \<cdot> \<delta> \<in> NF (qrstep nfs Q R) \<and>
                  (l |_ p' \<cdot> \<mu> \<cdot> \<sigma>, l |_ p' \<cdot> \<delta>) \<in> ?QR\<^sup>* \<longrightarrow>
                  l |_ p' \<cdot> \<delta> \<in> NFQ" .
                moreover from sNF have "(set (args s)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NFQ" unfolding s by auto
                moreover from lp'steps have "(l |_ p' \<cdot> \<mu> \<cdot> \<sigma>, l |_ p' \<cdot> \<delta>) \<in> ?QR\<^sup>*" 
                  using subst_subst by auto
                moreover have "l |_ p' \<cdot> \<delta> \<in> NF ?QR" using lnf Fun(3) by auto
                ultimately have "l |_ p' \<cdot> \<delta> \<in> NFQ" by auto
                then show ?thesis using subt_at_subst[OF Fun(3), of \<delta>] by auto
              qed
            qed
          qed
        qed
      } note p'=this
      have eps:"[] \<in> poss l" by auto
      from lr have "(l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> rstep R" by auto
      then have "l \<cdot> \<delta> \<notin> NF_trs R" by auto
      with NF_Q_R have "l \<cdot> \<delta> \<notin> NFQ" by auto
      then have "\<exists>p v \<sigma>. (l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> qrstep_r_p_s nfs Q R v p \<sigma>" using p'[OF eps] by auto
      then have "(l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> ?QR\<^sup>*" 
        using qrstep_qrstep_r_p_s_conv r_into_rtrancl by fast
      with lsteps have lrsteps: "(l \<cdot> \<mu> \<cdot> \<sigma>,r \<cdot> \<delta>) \<in> ?QR\<^sup>*" 
        using rtrancl_trans subst_subst by auto
      let ?C = "(ctxt_of_pos_term pp (t \<cdot> \<sigma>))"
      let ?C' = "(ctxt_of_pos_term pp (t' \<cdot> \<sigma>))"
      from ctxt_of_pos_term_subst[OF p, of \<sigma>] have C\<sigma>:"?C = ctxt_of_pos_term pp t \<cdot>\<^sub>c \<sigma>" .
      have "ctxt_of_pos_term pp t = ctxt_of_pos_term pp t'" 
        using ctxt_of_pos_term_replace_at_below[OF p order_pos.order_refl] unfolding t' by auto 
      moreover have "ctxt_of_pos_term pp t' \<cdot>\<^sub>c \<sigma> = ctxt_of_pos_term pp (t' \<cdot> \<sigma>)" 
        using ctxt_of_pos_term_subst[OF pt', of \<sigma>] by simp
      ultimately have  ctxt_closure': "?C = ?C'" using  C\<sigma> by auto
      from t have "t \<cdot> \<sigma> = ?C\<langle>l \<cdot> \<mu> \<cdot> \<sigma>\<rangle>" 
        using C\<sigma> subst_apply_term_ctxt_apply_distrib[of "ctxt_of_pos_term pp t" "l \<cdot> \<mu>" \<sigma>] 
        by auto
      then have 1:"(t \<cdot> \<sigma>, ?C\<langle>r \<cdot> \<delta>\<rangle>) \<in> ?QR\<^sup>*" 
        using ctxt.closedD[OF _ lrsteps, of ?C] 
          ctxt.closed_rtrancl[OF ctxt_closed_qrstep] by auto
      from qrstep_rules_mono[OF subset] rtrancl_mono have "?QU\<^sup>* \<subseteq> ?QR\<^sup>*" by blast
      from qrsteps_ctxt_closed[OF steps] have "(?C\<langle>r \<cdot> \<delta>\<rangle>, ?C\<langle>w\<rangle>) \<in> ?QR\<^sup>*" by auto
      with 1 have 2:"(t \<cdot> \<sigma>, ?C\<langle>w\<rangle>) \<in> ?QR\<^sup>*" using rtrancl_trans by auto
      from ctxt_closure' steps2 have "(?C\<langle>w\<rangle>, u) \<in> ?QR\<^sup>*" by auto
      with 2 show "(t \<cdot> \<sigma>, u) \<in> ?QR\<^sup>*" by auto
    qed
  qed (simp add: lus)
  then show ?thesis unfolding qrstep_iff_rqrstep_or_nrqrstep by regexp
qed

lemma rewriting_proc_complete: assumes infin: "infinite_dpp (nfs,replace (s1,t1) {(s1,t1')} P,Q,R)" (is "infinite_dpp (_,?P,_,_)")
  and common: "rewrite_common_preconditions s1 (args s1) (args (t1 |_ p)) t1 t1' (l,r) p nfs False"
  and rewrite: "(t1,t1') \<in> rstep_r_p_s R (l,r) p \<mu>"
  and sFun: "is_Fun s1"
  and nfc: "\<And> v. t1 |_ p \<rhd> v \<Longrightarrow> nfc R Q (set (args s1)) v nfs"
  and wwf: "\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  and ndef: "is_Fun t1 \<Longrightarrow> \<not> defined R (the (root t1))"
  shows "infinite_dpp (nfs,P,Q,R)"
proof (cases "SN (qrstep nfs Q R)")
  case True note SN = this
  let ?QR = "qrstep nfs Q R"
  from SN infin obtain s t \<sigma> where ichain: "i_chain (nfs,?P,Q,R) s t \<sigma>" by auto
  have "\<exists> u. i_chain (nfs, P, Q, R) s u \<sigma>"
  proof (cases "\<exists> i. (s i, t i) \<notin> P")
    case False
    then have "\<And> i. (s i, t i) \<in> P" by auto
    with ichain have "i_chain (nfs, P, Q, R) s t \<sigma>" by auto
    then show ?thesis by blast
  next
    case True
    then obtain i where mem: "(s i, t i) \<notin> P" by blast
    from ichain have "(s i, t i) : ?P" by auto
    with mem have s1t1: "(s1,t1) \<in> P" unfolding replace_def 
      by (cases ?thesis, auto)
    then have P: "?P = P - {(s1,t1)} \<union> {(s1,t1')}" unfolding replace_def by auto
    define u where "u = (\<lambda> i. if (s i, t i) = (s1,t1') then t1 else t i)"
    {
      fix i
      from ichain have "(s i, t i) \<in> ?P" by auto
      then have "(s i, u i) \<in> P" unfolding u_def P by (cases "(s i, t i) = (s1,t1')", insert s1t1, auto)
    } note inP = this
    note conv = NF_rstep_supt_args_conv
    have "i_chain (nfs,P,Q,R) s u \<sigma>" unfolding i_chain.simps
    proof (intro allI conjI)
      fix i
      show "(u i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR\<^sup>*"
      proof (cases "(s i, t i) = (s1,t1')")
        case True
        from True ichain have steps: "(t1' \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR\<^sup>*" by auto
        from True ichain have "\<forall> u \<lhd> s1 \<cdot> \<sigma> i. u \<in> NFQ" by auto
        from this[unfolded conv] have NF: "set (args (s1 \<cdot> \<sigma> i)) \<subseteq> NFQ" by auto
        from inP[of "Suc i"] have s: "s (Suc i) \<in> fst ` P" by force
        from ichain have "\<forall> u \<lhd> s (Suc i) \<cdot> \<sigma> (Suc i). u \<in> NFQ" by auto
        from this[unfolded conv] have NFs: "set (args (s (Suc i) \<cdot> \<sigma> (Suc i))) \<subseteq> NFQ" by auto
        have steps: "(t1 \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR\<^sup>*"
          by (rule rewriting_complete[OF common rewrite steps NFs NF sFun nfc SN wwf ndef])
        with True show ?thesis unfolding u_def by simp
      qed (insert ichain u_def, auto)
      from ichain have nfs: "NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
      show "NF_subst nfs (s i, u i) (\<sigma> i) Q"
      proof (cases "(s i, t i) = (s1,t1')")
        case True
        show ?thesis
        proof
          fix x
          assume nfs and x: "x \<in> vars_term (s i) \<or> x \<in> vars_term (u i)"
          from x have "x \<in> vars_rule (s i, t i)"
          proof
            assume "x \<in> vars_term (u i)"
            with True have x: "x \<in> vars_term t1" unfolding u_def by auto
            define C where "C = ctxt_of_pos_term p t1"
            note common = common[unfolded rewrite_common_preconditions_def]
            from rewrite have id: "t1 = C \<langle>l \<cdot> \<mu>\<rangle>" "t1' = C \<langle>r \<cdot> \<mu>\<rangle>" and p: "p \<in> poss t1" unfolding rstep_r_p_s_def Let_def C_def by auto
            with x have "x \<in> vars_ctxt C \<or> x \<in> vars_term (l \<cdot> \<mu>)" by (simp add: vars_term_ctxt_apply)
            then have "x \<in> vars_term s1 \<or> x \<in> vars_term t1'"
            proof
              assume "x \<in> vars_ctxt C"
              then show ?thesis unfolding id by (simp add: vars_term_ctxt_apply)
            next
              assume "x \<in> vars_term (l \<cdot> \<mu>)"
              also have "l \<cdot> \<mu> = t1 |_ p" using p ctxt_eq ctxt_supt_id id(1) C_def by force
              finally show ?thesis using common by auto
            qed
            then show ?thesis unfolding True vars_rule_def by auto 
          qed (simp add: vars_rule_def)
          with \<open>nfs\<close> nfs
          show "\<sigma> i x \<in> NFQ" unfolding NF_subst_def by blast
        qed
      qed (insert nfs u_def, auto)        
    qed (insert ichain inP, auto)
    then show ?thesis by blast
  qed
  then show ?thesis unfolding infinite_dpp.simps by blast
qed simp

lemma rewriting_proc: assumes fin: "finite_dpp (nfs,m,replace (s1,t1) {(s1,t1')} P,replace (s1,t1) {(s1,t1')} Pw,Q,Rs,Rw)" (is "finite_dpp (_,_,?P,?Pw,_,_,_)")
  assumes common: "rewrite_common_preconditions s1 [s1] [t1 |_ p] t1 t1' (l,r) p nfs True"
  and rewrite: "(t1,t1') \<in> rstep_r_p_s R (l,r) p \<mu>"
  and wf: "\<not> nfs \<Longrightarrow> \<not> m \<Longrightarrow> wwf_qtrs Q R"
  and strict: "(s1,t1) \<in> P \<or> Rs = {}"
  and R: "Rs \<union> Rw = R"
  shows "finite_dpp (nfs,m,P, Pw, Q, Rs, Rw)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain s t \<sigma> where chain: "min_ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>" 
    unfolding finite_dpp_def by auto
  from chain have min: "m \<Longrightarrow> minimal_cond nfs Q R s t \<sigma>" unfolding min_ichain.simps R by auto     
  let ?t = "\<lambda> i. if (s i,t i) = (s1,t1) then t1' else t i"
  let ?R = "qrstep nfs Q R"
  let ?Rb = "qrstep nfs Q (Rs \<union> Rw)"
  let ?Rs = "qrstep nfs Q Rs"
  from chain have chain: "ichain (nfs,m,P,Pw,Q,Rs,Rw) s t \<sigma>" unfolding min_ichain.simps by simp
  note chain = chain[unfolded ichain.simps]
  from chain have inP: "\<And> i. (s i, t i) \<in> P \<union> Pw" by auto
  from chain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NFQ" by auto
  from chain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
  from chain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R\<^sup>*" unfolding R by auto
  from min have SN: "\<And> i. m \<Longrightarrow> SN_on ?R {t i \<cdot> \<sigma> i}" unfolding minimal_cond_def by auto
  note rewr = rewriting_sound[OF common rewrite] 
  have "min_ichain (nfs,m,?P,?Pw,Q,Rs,Rw) s ?t \<sigma>"
    unfolding min_ichain.simps
  proof (intro conjI impI)
    assume m
    show "minimal_cond nfs Q (Rs \<union> Rw) s ?t \<sigma>" unfolding R minimal_cond_def 
    proof
      fix i
      show "SN_on ?R {?t i \<cdot> \<sigma> i}"
      proof (cases "(s i, t i) = (s1,t1)")
        case False
        with SN[of i, OF \<open>m\<close>] show ?thesis by auto
      next
        case True
        then have id: "?t i = t1'" "s i = s1" "t i = t1" by auto
        with SN[of i, OF \<open>m\<close>] have SN: "SN_on ?R {t1 \<cdot> \<sigma> i}" by auto
        note rewr = rewr[OF NF[of i, unfolded id] nfs[of i, unfolded id] steps[of i, unfolded id], THEN conjunct2, rule_format, OF NF]
        have "SN_on ?R {t1' \<cdot> \<sigma> i}" 
          by (rule rewr, insert SN, auto)
        then show ?thesis unfolding id by simp
      qed
    qed
  next
    show "ichain (nfs,m,?P,?Pw,Q,Rs,Rw) s ?t \<sigma>"
      unfolding ichain.simps
    proof (intro conjI allI)
      fix i
      show "(s i, ?t i) \<in> ?P \<union> ?Pw" using inP[of i]
        by (cases "(s i, t i) = (s1,t1)", auto simp: replace_def)
    next        
      fix i
      show "s i \<cdot> \<sigma> i \<in> NFQ" by (rule NF)
    next
      fix i
      have "(?t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R\<^sup>*"
      proof (cases "(s i, t i) = (s1,t1)")
        case False
        with steps[of i] show ?thesis by auto
      next
        case True
        then have id: "?t i = t1'" "s i = s1" "t i = t1" by auto
        note rewr = rewr[OF NF[of i, unfolded id] nfs[of i, unfolded id] steps[of i, unfolded id], THEN conjunct1, rule_format, OF NF]
        have "(t1' \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?R\<^sup>*"
          by (rule rewr, insert SN[of i, unfolded id] wf, auto)
        then show ?thesis unfolding id by simp
      qed
      then show "(?t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?Rb\<^sup>*" unfolding R .
    next
      from chain have disj: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?Rb\<^sup>* O ?Rs O ?Rb\<^sup>*)" by simp
      show "(INFM i. (s i, ?t i) \<in> ?P) \<or> (INFM i. (?t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?Rb\<^sup>* O ?Rs O ?Rb\<^sup>*)" unfolding
        INFM_disj_distrib[symmetric] unfolding INFM_nat_le
      proof
        fix i
        from disj[unfolded INFM_nat_le] obtain j where j: "j \<ge> i" and 
          disj: "(s j, t j) \<in> P \<or> (t j \<cdot> \<sigma> j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> ?Rb\<^sup>* O ?Rs O ?Rb\<^sup>*" by blast
        show "\<exists> j \<ge> i. (s j, ?t j) \<in> ?P \<or> (?t j \<cdot> \<sigma> j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> ?Rb\<^sup>* O ?Rs O ?Rb\<^sup>*"
        proof (intro exI conjI, rule j)
          show "(s j, ?t j) \<in> ?P \<or> (?t j \<cdot> \<sigma> j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> ?Rb\<^sup>* O ?Rs O ?Rb\<^sup>*"
            by (cases "(s j, t j) = (s1,t1)", insert strict disj, auto simp: replace_def)
        qed
      qed
    next
      fix i
      show "NF_subst nfs (s i, ?t i) (\<sigma> i) Q"
      proof (cases "(s i, t i) = (s1,t1)")
        case False
        with nfs[of i] show ?thesis by auto
      next 
        case True
        then have id: "?t i = t1'" "s i = s1" "t i = t1" by auto
        then have nfs: "NF_subst nfs (s1,t1) (\<sigma> i) Q" using nfs[of i] by simp
        note common = common[unfolded rewrite_common_preconditions_def wf_rule_def]
        from rewrite[unfolded rstep_r_p_s_def Let_def]
        obtain C where t1: "C \<langle> l \<cdot> \<mu> \<rangle> = t1" "C \<langle> r \<cdot> \<mu> \<rangle> = t1'"
          unfolding fst_conv snd_conv by blast
        have "vars_term t1' \<subseteq> vars_term t1" using common
          unfolding t1[symmetric] 
          unfolding vars_term_ctxt_apply vars_term_subst by auto
        then have "vars_rule (s1,t1') \<subseteq> vars_rule (s1, t1)" unfolding vars_rule_def by auto
        with nfs have nfs: "NF_subst nfs (s1,t1') (\<sigma> i) Q" unfolding NF_subst_def by auto
        then show ?thesis unfolding id by simp
     qed
    qed 
  qed    
  with fin show False unfolding finite_dpp_def by auto
qed

end

end

