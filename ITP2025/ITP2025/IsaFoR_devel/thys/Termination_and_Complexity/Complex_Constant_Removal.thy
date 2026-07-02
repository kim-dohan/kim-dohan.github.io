(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Complex_Constant_Removal
imports
  TRS.QDP_Framework
begin

text \<open>the following technique allows to replace a ground expression
  like a large constant c or some value "ack(5,5)" by a fresh variable x.
  this variable must then be added as new (last) argument to all pairs.
  this technique is sometimes applied as a preprocessing technique for bounded increase
  where loops like (while i < 1000 do i++) are transformed into (while i < x do i++).
\<close>
text \<open>the technique can be improved by only demanding CR of usable rules of c,
   where @{thm normalize_subst_qrsteps_inn_partial} should be useful.
   so far, in example proofs this was never necessary, so it remains as future work\<close>
lemma complex_constant_removal: fixes P :: "('f,'v)trs" 
  assumes fin: "finite_dpp (nfs,m,P',Pw',Q,{},R)" (is "finite_dpp ?P'")
  and CR: "c \<in> NF_trs R \<or> CR (qrstep nfs Q R)"
  and inn: "NF_terms Q \<subseteq> NF_trs R"
  and ground: "ground c"
  and PPW: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> is_Fun s \<and> is_Fun t \<and> \<not> defined R (the (root t))"
  and x: "\<And> s t. (s,t) \<in> P \<union> Pw \<Longrightarrow> x \<notin> vars_rule (s,t)"
  and rel: "\<And> P P' f ss g ts. rel P P' \<Longrightarrow> (Fun f ss, Fun g ts) \<in> P \<Longrightarrow>
    \<exists> ts'. (Fun (ren (f,length ss)) (ss @ [Var x]), Fun (ren (g,length ts)) (ts' @ [Var x])) \<in> P'
      \<and> ts = map (\<lambda> t. t \<cdot> subst x c) ts'"
  and ren: "\<And> f ss t. (Fun f ss,t) \<in> P \<union> Pw \<Longrightarrow> Some (ren (f,length ss), Suc (length ss)) \<notin> root ` Q"
  and ren2: "\<And> f ss t. (Fun f ss,t) \<in> P \<union> Pw \<Longrightarrow> \<not> defined R (ren (f,length ss), Suc (length ss))"
  and R: "\<forall> (l,r) \<in> R. is_Fun l"
  and P: "rel P P'"
  and Pw: "rel Pw Pw'"
  shows "finite_dpp (nfs,m,P,Pw,Q,{},R)" (is "finite_dpp ?P")
proof -
  let ?xc = "subst x c"
  let ?QR = "qrstep nfs Q R"
  let ?Q = "NF_terms Q"
  let ?NFR = "NF_trs R"
  let ?prop = "\<lambda> u. (c,u) \<in> ?QR^* \<and> u \<in> ?Q"
  have "?NFR = NF (qrstep nfs {} R)" by simp
  also have "\<dots> \<subseteq> NF ?QR"
    by (rule NF_anti_mono, auto)
  finally have NFR_imp_NF: "?NFR \<subseteq> NF ?QR" .
  with inn have Q_imp_NF: "?Q \<subseteq> NF ?QR" by auto
  {
    fix s t \<sigma>    
    assume "min_ichain ?P s t \<sigma>"
    note chain = this[unfolded min_ichain.simps ichain.simps, simplified]
    from chain have PP: "\<And> i. (s i, t i) \<in> P \<union> Pw" by auto
    from chain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR^*" by auto
    from chain have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> ?Q" by auto
    from chain have m: "\<And> i. m \<Longrightarrow> SN_on ?QR {t i \<cdot> \<sigma> i}" unfolding minimal_cond_def by auto
    (* in principle we want to instantiate x by some normal form of c (which is unique due to CR).
       however, we do not know, whether c is normalizing (perhaps the chain only uses pairs where 
       c does not occur), but still need a normal form for filling the fresh variable in the additional
       argument of every pair. therefore, nf is defined via the following case distinction *)
    define nf where "nf = (if (\<exists> u. ?prop u) then (SOME u. ?prop u) else (SOME u. u \<in> ?Q))"
    have nf: "nf \<in> ?Q"
    proof (cases "\<exists> u. ?prop u")
      case True
      from someI_ex[of ?prop, OF True] show ?thesis unfolding nf_def by auto
    next
      case False
      from someI[of "\<lambda> u. u \<in> ?Q", OF NF] False show ?thesis unfolding nf_def by auto
    qed
    (* now we can define the new substitution *)
    define \<sigma>' where "\<sigma>' = (\<lambda> i. (\<sigma> i)(x := nf))"
    (* and the substitutions which corresponds to the unmodified chain *)
    define \<sigma>'' where "\<sigma>'' = (\<lambda> i. (\<sigma> i)(x := c))"
    (* next we extract all the pairs in more explicit form *)
    {
      fix i
      from PPW[OF PP[of i]] obtain f ss where si: "s i = Fun f ss" by (cases "s i", auto)
      from PPW[OF PP[of i]] obtain g ts where ti: "t i = Fun g ts" by (cases "t i", auto)
      have "\<exists> f g ss ts. s i = Fun f ss \<and> t i = Fun g ts" using si ti by auto
    }
    from choice[OF allI[OF this]] obtain f where "\<forall> i. \<exists> g ss ts. s i = Fun (f i) ss \<and> t i = Fun g ts" ..
    from choice[OF this] obtain g where "\<forall> i. \<exists> ss ts. s i = Fun (f i) ss \<and> t i = Fun (g i) ts" ..
    from choice[OF this] obtain ss where "\<forall> i. \<exists> ts. s i = Fun (f i) (ss i) \<and> t i = Fun (g i) ts" ..
    from choice[OF this] obtain ts where si_ti: "\<And> i. s i = Fun (f i) (ss i)" "\<And> i. t i = Fun (g i) (ts i)" by auto
    {
      fix i
      from PPW[OF PP[of i], unfolded si_ti] have ndef: "\<not> defined R (g i, length (ts i))" by simp
      from nondef_root_imp_arg_qrsteps[OF steps[of i, unfolded si_ti, simplified] R] ndef
      have "g i = f (Suc i)" "length (ts i) = length (ss (Suc i))" "\<not> defined R (f (Suc i), length (ss (Suc i)))" by auto
    } note gi = this    
    note si_ti = si_ti[unfolded gi]
    let ?g = "\<lambda> i. f (Suc i)"
    let ?lss = "\<lambda> i. length (ss i)"
    let ?lts = "\<lambda> i. length (ss (Suc i))"
    (* make sure that strict pairs P are translated into strict pairs P' ... *)
    define Pb where "Pb = (\<lambda> i. if (s i, t i) \<in> P then P else Pw)"
    define Pb' where "Pb' = (\<lambda> i. if (s i, t i) \<in> P then P' else Pw')"
    (* ... in the following way to obtain the new pairs *)
    {
      fix i
      have mem: "(s i, t i) \<in> Pb i" using PP[of i] unfolding Pb_def by auto
      have Pb: "rel (Pb i) (Pb' i)" using P Pw unfolding Pb_def Pb'_def by (cases "(s i, t i) \<in> P", auto)
      note mem = mem[unfolded si_ti]
      from rel[OF Pb mem, unfolded gi] have "\<exists> ts'. (Fun (ren (f i , ?lss i)) (ss i @ [Var x]), Fun (ren (?g i, ?lts i)) (ts' @ [Var x])) \<in> Pb' i
        \<and> ts i = map (\<lambda>t. t \<cdot> ?xc) ts'" by auto
    }
    from choice[OF allI[OF this]] obtain ts' where "\<forall> i. (Fun (ren (f i , ?lss i)) (ss i @ [Var x]), Fun (ren (?g i, ?lts i)) (ts' i @ [Var x])) \<in> Pb' i
        \<and> ts i = map (\<lambda>t. t \<cdot> ?xc) (ts' i)" ..
    then have ts: "\<And> i. ts i = map (\<lambda>t. t \<cdot> ?xc) (ts' i)" 
      and Pb': "\<And> i. (Fun (ren (f i , ?lss i)) (ss i @ [Var x]), Fun (ren (?g i, ?lts i)) (ts' i @ [Var x])) \<in> Pb' i" by blast+
    let ?s = "\<lambda> i. Fun (ren (f i, ?lss i)) (ss i @ [Var x])"
    let ?t = "\<lambda> i. Fun (ren (?g i, ?lts i)) (ts' i @ [Var x])"
    define s' t' where "s' = ?s" and "t' = ?t" 
    (* we have all ingredients to define our new chain, so it remains to prove that it really is a chain *)
    have "min_ichain ?P' s' t' \<sigma>'"
    proof -    
      {
        fix t :: "('f,'v)term" and i
        assume x: "x \<notin> vars_term t"
        have "t \<cdot> \<sigma>' i = t \<cdot> \<sigma> i"
          by (rule term_subst_eq, insert x, unfold \<sigma>'_def, auto)
      } note \<sigma>' = this
      have [simp]: "\<And> i. \<sigma>' i x = nf" unfolding \<sigma>'_def by auto
      have [simp]: "\<And> \<sigma>. c \<cdot> \<sigma> = c" by (rule ground_subst_apply[OF ground])
      {
        fix i
        let ?ss = "map (\<lambda> s. s \<cdot> \<sigma> i) (ss i)"
        {
          fix s
          assume "s \<in> set (ss i)"
          with x[OF PP[of i, unfolded si_ti]] have x: "x \<notin> vars_term s" unfolding vars_rule_def by auto
          from \<sigma>'[OF this] have "s \<cdot> \<sigma>' i = s \<cdot> \<sigma> i" .
        } 
        then have "s' i \<cdot> \<sigma>' i = Fun (ren (f i,?lss i)) (?ss @ [nf])" unfolding s'_def by simp
      } note sis = this (* represent s' i \<cdot> \<sigma>' i more conveniently *)
      {
        fix i
        let ?ts = "map (\<lambda> t. t \<cdot> \<sigma>'' i) (ts' i)"
        have "map (\<lambda>t. t \<cdot> ?xc \<cdot> \<sigma> i) (ts' i) = ?ts"
        proof (rule nth_map_conv[OF refl], intro allI impI)
          fix j
          have "ts' i ! j \<cdot> ?xc \<cdot> \<sigma> i = ts' i ! j \<cdot> (?xc \<circ>\<^sub>s \<sigma> i)" by auto
          also have "\<dots> = ts' i ! j \<cdot> \<sigma>'' i"
            by (rule term_subst_eq, unfold subst_compose_def \<sigma>''_def subst_def, auto)
          finally show "ts' i ! j \<cdot> ?xc \<cdot> \<sigma> i = ts' i ! j \<cdot> \<sigma>'' i" .
        qed
        then have "t i \<cdot> \<sigma> i = Fun (?g i) ?ts" "t' i \<cdot> \<sigma>' i = Fun (ren (?g i,?lts i)) (map (\<lambda> t. t \<cdot> \<sigma>' i) (ts' i) @ [nf])"
          unfolding si_ti ts t'_def by auto        
      } note tis = this (* represent t i \<cdot> \<sigma> i and t' i \<cdot> \<sigma>' i more conveniently *)
      {
        (* show all properties I, II, ... of a chain for each i *)
        fix i
        let ?si = "?s i"
        let ?ti = "?t i"
        let ?ss = "map (\<lambda> s. s \<cdot> \<sigma> i) (ss i)"
        let ?ts = "map (\<lambda> s. s \<cdot> \<sigma>' i) (ts' i)"
        let ?sss = "map (\<lambda> s. s \<cdot> \<sigma> (Suc i)) (ss (Suc i))"
        note memP = PP[of i, unfolded si_ti]
        have mem: "(?si, ?ti) \<in> Pb' i" by (rule Pb')
        then have I: "(s' i, t' i) \<in> P' \<union> Pw'" "(s' i, t' i) \<in> Pb' i" unfolding s'_def t'_def Pb'_def
          by (cases "(s i, t i) \<in> P", auto)
        have II: "s' i \<cdot> \<sigma>' i \<in> ?Q" unfolding sis
        proof (rule NF_args_imp_NF[OF _ nf])
          show "Some (ren (f i, ?lss i), length (?ss @ [nf])) \<notin> root ` Q"
            using ren[OF memP]  by auto
        next
          fix s
          assume "s \<in> set (?ss @ [nf])"
          then have "s \<in> set ?ss \<or> s = nf" by auto
          then show "s \<in> NF_terms Q"
          proof
            assume "s = nf" with nf show ?thesis by auto
          next
            assume "s \<in> set ?ss"
            then have "Fun (f i) (ss i) \<cdot> \<sigma> i \<rhd> s" by auto
            with NF_imp_subt_NF[OF NF[of i, unfolded si_ti]] show ?thesis by blast
          qed
        qed  
        {
          (* for strong normalization and evaluation between pairs, first consider
             some arbitrary argument of (ts i) *)
          fix j
          assume j: "j < length (ts' i)"
          have "(ts' i ! j \<cdot> \<sigma>'' i, ts' i ! j \<cdot> \<sigma>' i) \<in> ?QR^* \<and> (c \<in> ?NFR \<longrightarrow> ts' i ! j \<cdot> \<sigma>'' i = ts' i ! j \<cdot> \<sigma>' i)"
          proof (cases "x \<in> vars_term (ts' i ! j)")
            case False
            have "ts' i ! j \<cdot> \<sigma>'' i = ts' i ! j \<cdot> \<sigma>' i"
              by (rule term_subst_eq, insert False, auto simp: \<sigma>'_def \<sigma>''_def subst_def)
            then show ?thesis by auto
          next
            case True
            from j have arg: "t i \<cdot> \<sigma> i \<unrhd> ts' i ! j \<cdot> \<sigma>'' i" 
              unfolding tis by auto
            from True have "ts' i ! j \<unrhd> Var x" by auto
            from supteq_subst[OF this, of "\<sigma>'' i"] have "ts' i ! j \<cdot> \<sigma>'' i \<unrhd> c"
              by (simp add: \<sigma>''_def subst_def)
            from supteq_trans[OF arg this] have "t i \<cdot> \<sigma> i \<unrhd> c" .
            from supteq_imp_subt_at[OF this] 
              obtain p where c: "t i \<cdot> \<sigma> i |_ p = c" and p: "p \<in> poss (t i \<cdot> \<sigma> i)" by auto
            from normalize_subterm_qrsteps[OF p steps[of i] NF, unfolded c] obtain u
              where cu: "(c,u) \<in> ?QR^*" and u: "u \<in> ?Q" by auto
            then have propu: "\<exists> u. ?prop u" by auto
            then have "nf = (SOME u. ?prop u)" unfolding nf_def by auto
            from someI_ex[of ?prop, OF propu, folded this] have cnf: "(c,nf) \<in> ?QR^*" ..            
            show ?thesis
            proof (intro conjI impI, rule all_ctxt_closed_subst_step)
              fix y
              show "(\<sigma>'' i y, \<sigma>' i y) \<in> ?QR^*"
                by (cases "y = x", insert cnf, auto simp: subst_def \<sigma>'_def \<sigma>''_def)
            next
              assume "c \<in> ?NFR"
              with NFR_imp_NF have "c \<in> NF ?QR" by auto
              with cnf have nf: "nf = c" by (induct, auto)
              show "ts' i ! j \<cdot> \<sigma>'' i = ts' i ! j \<cdot> \<sigma>' i" unfolding \<sigma>'_def \<sigma>''_def nf ..
            qed auto
          qed
          then have ts_ts': "(ts' i ! j \<cdot> \<sigma>'' i, ts' i ! j \<cdot> \<sigma>' i) \<in> ?QR^*" and 
            ts_ts'': "c \<in> ?NFR \<Longrightarrow> ts' i ! j \<cdot> \<sigma>' i = ts' i ! j \<cdot> \<sigma>'' i" by auto
          from nondef_root_imp_arg_qrsteps[OF steps[of i, unfolded si_ti, simplified] R]
            j ts gi[of i] 
          have "(ts i ! j \<cdot> \<sigma> i, ?sss ! j) \<in> ?QR^*" by auto
          with tis[of i, unfolded si_ti] j ts 
          have arg_steps: "(ts' i ! j \<cdot> \<sigma>'' i, ?sss ! j) \<in> ?QR^*" by auto
          have steps: "(ts' i ! j \<cdot> \<sigma>' i, ?sss ! j) \<in> ?QR^*"
          proof (cases "c \<in> ?NFR")
            case True
            from ts_ts''[OF this] show ?thesis using arg_steps by simp
          next
            case False
            with CR have CR: "CR ?QR" by simp
            from CR_divergence_imp_join[OF CR ts_ts' arg_steps] obtain u where
              join: "(ts' i ! j \<cdot> \<sigma>' i, u) \<in> ?QR^*" and u: "(?sss ! j, u) \<in> ?QR^*" by auto
            have "?sss ! j \<in> ?Q"
              by (rule NF_subterm[OF NF[of "Suc i", unfolded si_ti]], insert j ts gi, auto)
            then have "?sss ! j \<in> NF ?QR" using Q_imp_NF by auto
            with u have u: "u = ?sss ! j" by (induct, auto)
            from join u show "(ts' i ! j \<cdot> \<sigma>' i, ?sss ! j) \<in> ?QR^*" by simp
          qed
          {
            assume m
            have "SN_on ?QR {ts i ! j \<cdot> \<sigma> i}"
              by (rule SN_imp_SN_arg_gen[OF ctxt_closed_qrstep m[OF \<open>m\<close>, of i, unfolded si_ti, simplified]],
                insert j ts, auto)
            with tis[of i] j ts si_ti have "SN_on ?QR {ts' i ! j \<cdot> \<sigma>'' i}" by auto
            from steps_preserve_SN_on[OF ts_ts' this] have "SN_on ?QR {ts' i ! j \<cdot> \<sigma>' i}" .
          }
          note steps this
        }
        note steps_SN = this   
        (* using steps_SN allows to easily derive III and IV *)
        from arg_cong[OF ts, of length] gi have ts': "length (ts' i) = length (ss (Suc i))" by simp
        have III: "(t' i \<cdot> \<sigma>' i, s' (Suc i) \<cdot> \<sigma>' (Suc i)) \<in> ?QR^*"
          unfolding sis tis
        proof (rule all_ctxt_closedD[of UNIV])
          fix j
          assume "j < length (?ts @ [nf])"
          then have j: "j < Suc (length (ts' i))" by auto
          show "((?ts @ [nf]) ! j, (?sss @ [nf]) ! j) \<in> ?QR^*"
          proof (cases "j < length (ts' i)")
            case True
            from steps_SN(1)[OF True] show ?thesis using ts' True by (auto simp: nth_append)
          next
            case False
            with j have j: "j = length (ts' i)" by auto
            then show ?thesis using ts' by (auto simp: nth_append)
          qed
        qed (auto simp: ts')
        have IV: "m \<Longrightarrow> SN_on ?QR {t' i \<cdot> \<sigma>' i}"
        proof -
          assume m
          show "SN_on (qrstep nfs Q R) {t' i \<cdot> \<sigma>' i}"
            unfolding tis
          proof (rule SN_args_imp_SN[OF _ R ndef_applicable_rules])
            from ren2[OF PP[of "Suc i", unfolded si_ti]]
            show "\<not> defined R (ren (f (Suc i), ?lts i), length (?ts @ [nf]))"
              using ts' by auto
          next
            fix t
            assume "t \<in> set (?ts @ [nf])"
            then have "t \<in> set ?ts \<or> t = nf" by auto
            then show "SN_on ?QR {t}"
            proof
              assume "t = nf"
              with nf Q_imp_NF show ?thesis by blast
            next
              assume "t \<in> set ?ts"
              from this[unfolded set_conv_nth] obtain j where 
                j: "j < length (ts' i)" and t: "t = ts' i ! j \<cdot> \<sigma>' i" by auto
              from steps_SN(2)[OF j \<open>m\<close>] show ?thesis unfolding t .
            qed
          qed
        qed
        have V: "NF_subst nfs (s' i, t' i) (\<sigma>' i) Q"
        proof
          fix y
          assume nfs and y: "y \<in> vars_term (s' i) \<or> y \<in> vars_term (t' i)"
          have "vars_term (s' i) \<union> vars_term (t' i) = vars_term (s i) \<union> (vars_term (Fun h (ts' i)) \<union> {x})"
            unfolding s'_def t'_def si_ti by auto
          also have "\<dots> \<subseteq> vars_term (s i) \<union> vars_term (Fun h (ts' i) \<cdot> ?xc) \<union> {x}"
            unfolding vars_term_subst subst_def fun_upd_def by auto
          also have "\<dots> = vars_rule (s i, t i) \<union> {x}" unfolding si_ti ts vars_rule_def by auto
          finally have "y = x \<or> y \<noteq> x \<and> y \<in> vars_rule (s i, t i)" using y by blast
          then show "\<sigma>' i y \<in> ?Q"
          proof
            assume "y = x"
            with nf show ?thesis by simp
          next
            assume y: "y \<noteq> x \<and> y \<in> vars_rule (s i, t i)"
            from chain have "NF_subst nfs (s i, t i) (\<sigma> i) Q" by simp
            from this[unfolded NF_subst_def, rule_format, OF \<open>nfs\<close>] y have "\<sigma> i y \<in> ?Q" by auto
            with y show ?thesis unfolding \<sigma>'_def by auto
          qed
        qed
        note I II III IV V
      }
      note main = this
      have "INFM i. (s' i, t' i) \<in> P'"
        unfolding INFM_nat_le
      proof
        fix i
        from chain[unfolded INFM_nat_le] obtain j where j: "j \<ge> i" and mem: "(s j, t j) \<in> P" by blast
        from main(2)[of j] mem have "(s' j, t' j) \<in> P'" unfolding Pb'_def by auto
        with j show "\<exists> j \<ge> i. (s' j, t' j) \<in> P'" by auto
      qed
      then show "min_ichain ?P' s' t' \<sigma>'"
        unfolding min_ichain.simps ichain.simps using main by (auto simp: minimal_cond_def)
    qed
    with fin have False unfolding finite_dpp_def by auto
  }
  then show ?thesis unfolding finite_dpp_def by blast
qed

end
