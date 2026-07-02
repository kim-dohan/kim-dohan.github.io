(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Q_Reduction
  imports TRS.Signature_Extension
begin

(* the following lemma is similar to prove as clean_qrstep_reverse *)
lemma qrstep_reduced_Q: fixes R :: "('f,'v)trs"
  assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and Q': "Q' = {q. q \<in> Q \<and> (root q = None \<or> the (root q) \<in> F)}"
  and F: "funas_trs R \<subseteq> F"
  and wf: "wf_trs R" (* essentially, we need vars(r) \<subseteq> vars(l) *)
  (* this is also essential: consider R = {a \<rightarrow> x}, Q = {a,b}, F = Q' = {a}, and step "a \<rightarrow> b" *)
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and step: "(s, t) \<in> qrstep nfs Q' R"
  shows "(s,t) \<in> qrstep nfs Q R \<and> set (aliens F t) \<subseteq> NF_terms Q"
proof -
  let ?QR = "qrstep False Q R"
  let ?Q = "NF_terms Q"
  let ?Q' = "NF_terms Q'"
  from step obtain C l r \<sigma> where lr: "(l,r) \<in> R" and NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> ?Q'" 
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" 
    and nfs: "NF_subst nfs (l,r) \<sigma> Q'" by auto
  from lr F have l: "funas_term l \<subseteq> F" and r: "funas_term r \<subseteq> F"
    unfolding funas_trs_def funas_rule_def [abs_def]
    by force+
  from wf[unfolded wf_trs_def] lr have vars: "vars_term r \<subseteq> vars_term l" by auto
  note switch = wwf_qtrs_imp_nfs_False_switch[OF wf_trs_imp_wwf_qtrs[OF wf], of nfs]
  note NF_conv = NF_terms_args_conv
  show ?thesis using aliens unfolding s t switch
  proof (induct C)
    case (More f bef C aft)
    let ?i = "length bef"
    let ?n = "Suc (?i + length aft)"
    let ?C = "More f bef C aft"
    {
      assume "(f,?n) \<notin> F"
      with More(2) have "?C\<langle>l\<cdot>\<sigma>\<rangle> \<in> ?Q" by auto
      with inn have "?C\<langle>l\<cdot>\<sigma>\<rangle> \<in> NF_trs R" by auto
      with rstepI[OF lr refl refl, of ?C \<sigma>] have False by auto
    }
    then have f: "(f,?n) \<in> F" by auto
    from More(2) f have aliens: "set (aliens F (C\<langle>l\<cdot>\<sigma>\<rangle>)) \<subseteq> ?Q" by auto
    from More(1)[OF aliens] have step: "(C\<langle>l\<cdot>\<sigma>\<rangle>,C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> ?QR" and aliens: "set (aliens F C\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> ?Q" by auto
    from More(2) f aliens have aliens: "set (aliens F (?C\<langle>r \<cdot> \<sigma>\<rangle>)) \<subseteq> ?Q" by auto
    with qrstep.ctxt[OF step, of "More f bef \<box> aft"] show ?case by auto
  next
    case Hole
    from Hole have aliens: "set (aliens F (l \<cdot> \<sigma>)) \<subseteq> ?Q" by simp
    with vars have alienst: "set (aliens F (r \<cdot> \<sigma>)) \<subseteq> ?Q"
      unfolding aliens_subst[OF l] aliens_subst[OF r] by auto
    note NF_conv = NF_terms_args_conv[symmetric]
    have "(\<box>\<langle>l \<cdot> \<sigma>\<rangle>, \<box>\<langle>r \<cdot> \<sigma>\<rangle>) \<in> ?QR"
    proof (rule qrstepI[OF _ lr refl refl], unfold NF_conv, intro ballI)
      fix u
      assume u: "u \<in> set (args (l \<cdot> \<sigma>))"
      from u obtain f ls where l\<sigma>: "l \<cdot> \<sigma> = Fun f ls" and mem: "u \<in> set ls" by (cases "l \<cdot> \<sigma>", auto)
      let ?n = "length ls"
      {
        assume "(f,?n) \<notin> F"
        with aliens l\<sigma> have "l \<cdot> \<sigma> \<in> ?Q" by auto
        with inn have "l \<cdot> \<sigma> \<in> NF_trs R" by auto
        with rstepI[OF lr refl refl, of \<box> \<sigma>] have False by auto
      }
      then have f: "(f,?n) \<in> F" by auto
      from aliens f mem l\<sigma> have aliensu: "set (aliens F u) \<subseteq> ?Q" by auto
      from NF[unfolded NF_conv] u have NF: "u \<in> ?Q'" by auto
      show "u \<in> ?Q" 
      proof (rule, rule ccontr, unfold not_not)
        fix v
        assume "(u,v) \<in> rstep (Id_on Q)"
        then obtain C \<tau> q q' where qq: "(q,q') \<in> Id_on Q" and u: "u = C\<langle>q\<cdot>\<tau>\<rangle>" and "v = C\<langle>q' \<cdot> \<tau>\<rangle>" by blast
        then have q: "q \<in> Q" by auto
        {
          fix C \<sigma>
          have "C\<langle>q \<cdot> \<sigma>\<rangle> \<notin> ?Q" using rstepI[OF qq refl refl, of C \<sigma>] by auto
        } note nmem = this
        {
          assume q: "q \<in> Q'"
          then have "(q,q) \<in> Id_on Q'" by auto
          from NF rstepI[OF this refl refl, of C \<tau>] u have False by auto
        }
        then have "q \<notin> Q'" by auto
        from this[unfolded Q'] q obtain f qs where q_fun: "q = Fun f qs" and f: "(f,length qs) \<notin> F" by (cases q, auto)
        from Q' have "Id_on Q' \<subseteq> Id_on Q" by auto
        from NF_anti_mono[OF rstep_mono[OF this]] have QQ': "?Q \<subseteq> ?Q'" by auto
        from aliensu NF show False unfolding u
        proof (induct C)
          case Hole
          from Hole(1) show ?case using nmem[of \<box> \<tau>] unfolding q_fun using f by auto
        next
          case (More g bef C aft)
          let ?n = "Suc (length bef + length aft)"
          from nmem[of "More g bef C aft" \<tau>] have g: "(g,?n) \<in> F" using More(2) by (auto split: if_splits)
          from More(2) g have aliens: "set (aliens F (C\<langle>q\<cdot>\<tau>\<rangle>)) \<subseteq> ?Q" by auto
          have NF: "C\<langle>q\<cdot>\<tau>\<rangle> \<in> ?Q'"
            by (rule NF_subterm[OF More(3)], auto)
          from More(1)[OF aliens NF] show ?case .
        qed
      qed
    qed simp
    with alienst show ?case by simp
  qed
qed

lemma qrstep_reduced_Q_SN_on: fixes R :: "('f,'v)trs"
  assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and Q': "Q' = {q. q \<in> Q \<and> (root q = None \<or> the (root q) \<in> F)}"
  and F: "funas_trs R \<subseteq> F"
  and wf: "wf_trs R" 
  and aliens: "set (aliens F s) \<subseteq> NF_terms Q"
  and SN: "SN_on (qrstep nfs Q R) {s}"
  shows "SN_on (qrstep nfs Q' R) {s}"
proof -
  let ?R = "qrstep nfs Q R"
  let ?R' = "qrstep nfs Q' R"
  let ?Q = "NF_terms Q"
  note transform = qrstep_reduced_Q[OF inn Q' F wf]
  {
    fix f
    assume f0: "f 0 = s" and steps: "\<And> i. (f i, f (Suc i)) \<in> ?R'"
    {
      fix i
      have "set (aliens F (f i)) \<subseteq> ?Q"
      proof (induct i)
        case 0
        with aliens f0 show ?case by simp
      next
        case (Suc i)
        from transform[OF Suc steps] show ?case by auto
      qed
      from transform[OF this steps] have "(f i, f (Suc i)) \<in> ?R" ..
    }
    with f0 have "\<not> SN_on ?R {s}" by force
    with SN have False by simp
  }
  then show ?thesis by force
qed

lemma min_ichain_reduced_Q: fixes R :: "('f,'v)trs"
  assumes inn: "NF_terms Q \<subseteq> NF_trs (R \<union> Rw)"
  and Q': "Q' = {q. q \<in> Q \<and> root q \<in> Some ` F}"
  and F: "funas_trs (R \<union> Rw) \<subseteq> F"
  and FP: "funas_trs (P \<union> Pw ) \<subseteq> F"
  and wf: "wf_trs (R \<union> Rw)"
  and vars: "\<And> s t. \<not> nfs \<Longrightarrow> (s,t) \<in> P \<union> Pw \<Longrightarrow> vars_term t \<subseteq> vars_term s"
  and ichain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows "min_ichain (nfs,m,P,Pw,Q',R,Rw) s t \<sigma>"
proof -
  from ichain 
  have ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>" and SN: "\<And> i. m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {t i \<cdot> \<sigma> i}"
    by (auto simp: minimal_cond_def)
  from ichain[unfolded ichain.simps] have NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NF_terms Q" 
    and P: "\<And> i. (s i, t i) \<in> P \<union> Pw" 
    and nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
  have ichain: "ichain (nfs,m,P,Pw,Q',R,Rw) s t \<sigma>"
    by (rule ichain_mono[OF ichain _ _ NF_trs_mono], insert Q', auto)
  show ?thesis unfolding min_ichain.simps minimal_cond_def
  proof (rule conjI[OF ichain], intro impI allI)
    fix i
    assume m
    note SN = SN[OF this]
    show "SN_on (qrstep nfs Q' (R \<union> Rw)) {t i \<cdot> \<sigma> i}"
    proof (rule qrstep_reduced_Q_SN_on[OF inn _ F wf _ SN])
      from FP P[of i] have F: "funas_term (s i) \<subseteq> F" "funas_term (t i) \<subseteq> F"
        unfolding funas_trs_def funas_rule_def [abs_def] by force+
      from NF_subterm[OF NF[of i] aliens_imp_supteq]
      have nf: "set (aliens F (s i \<cdot> \<sigma> i)) \<subseteq> NF_terms Q" by auto           
      show "set (aliens F (t i \<cdot> \<sigma> i)) \<subseteq> NF_terms Q"
      proof (cases nfs)
        case False
        from nf vars[OF False P[of i]] show ?thesis
        unfolding aliens_subst[OF F(1)] aliens_subst[OF F(2)] by auto
      next
        case True
        {
          fix a
          assume "a \<in> set (aliens F (t i \<cdot> \<sigma> i))"
          from this[unfolded aliens_subst[OF F(2)]] obtain x where
            x: "x \<in> vars_term (t i)" and a: "a \<in> set (aliens F (\<sigma> i x))" by auto
          from True nfs[of i] x have "\<sigma> i x \<in> NF_terms Q" unfolding NF_subst_def vars_rule_def by auto
          from NF_subterm[OF this aliens_imp_supteq[OF a]] have "a \<in> NF_terms Q" .
        }
        then show ?thesis by auto
      qed
    next
      let ?Q = "{q \<in> Q. root q = None \<or> the (root q) \<in> F}"
      let ?Q' = "{q \<in> Q. root q \<in> Some ` F}"
      have "Q' = ?Q'" unfolding Q' by simp
      also have "... = ?Q"
      proof -
        {
          fix q
          assume "q \<in> ?Q"
          then have q: "q \<in> Q" and disj: "root q = None \<or> the (root q) \<in> F" by auto
          {
            assume "root q = None"
            then obtain x where x: "q = Var x" by (cases q, auto)
            with q have "(Var x, Var x) \<in> Id_on Q" by auto
            from rstepI[OF this refl refl, of \<box> "\<lambda> _. s 0 \<cdot> \<sigma> 0"] NF[of 0]
            have False by auto
          }
          with disj have "root q \<in> Some ` F" by (cases q, auto)
          with q have "q \<in> ?Q'" by auto
        }
        then show ?thesis by auto
      qed
      finally show "Q' = ?Q" .
    qed
  qed
qed

lemma ichain_reduced_Q: fixes R :: "('f,'v)trs"
  assumes Q': "NF_terms Q \<subseteq> NF_terms Q'"
  and ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows "ichain (nfs,m,P,Pw,Q',R,Rw) s t \<sigma>"
  by (rule ichain_mono[OF ichain _ _ Q'], auto)

end
