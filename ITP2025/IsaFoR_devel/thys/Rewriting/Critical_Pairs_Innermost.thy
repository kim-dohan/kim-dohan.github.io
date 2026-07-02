(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2016-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Critical_Pairs_Innermost 
  imports 
    First_Order_Rewriting.Critical_Pairs
    Q_Restricted_Rewriting
begin

context
  fixes ren :: "'v :: infinite renaming2"  (* fix some renaming scheme *)
begin

(* note that the lhss condition is necessary:
   consider R = {x \<rightarrow> f(a), x \<rightarrow> g(a)} and Q = {x}
   then there are no critical pairs and NF Q \<subseteq> NF R
   however, f(a) \<leftarrow> x \<rightarrow> g(a) and f(a) and g(a) are not joinable *)
lemma critical_pairs_innermost_weak_diamond:
  fixes R :: "('f, 'v) trs"
  assumes cp: "\<And> l r. (True, l, r) \<in> critical_pairs ren R R \<Longrightarrow> l = r"
    and NF_Q_R: "NF_terms Q \<subseteq> NF_trs R"
    and lhss: "\<And> l r. (l, r) \<in> R \<Longrightarrow> is_Fun l"
  shows "w\<diamond> (qrstep nfs Q R)"
unfolding weak_diamond_def
proof
  fix t1 t2 :: "('f, 'v) term"
  let ?R = "qrstep nfs Q R"
  assume "(t1, t2) \<in> ?R^-1 O ?R - Id"
  then obtain s where st1: "(s, t1) \<in> ?R" and st2: "(s, t2) \<in> ?R" and t12: "t1 \<noteq> t2" by auto
  let ?Q = "NF_terms Q"
  from st1 obtain C1 l1 r1 \<sigma>1 where lr1: "(l1, r1) \<in> R" and s1: "s = C1\<langle>l1 \<cdot> \<sigma>1\<rangle>" and t1: "t1 = C1\<langle>r1 \<cdot> \<sigma>1\<rangle>"
    and NF1: "\<forall> u \<lhd> l1 \<cdot> \<sigma>1. u \<in> ?Q" and nfs1: "NF_subst nfs (l1, r1) \<sigma>1 Q" by auto
  from st2 obtain C2 l2 r2 \<sigma>2 where lr2: "(l2, r2) \<in> R" and s2: "s = C2\<langle>l2 \<cdot> \<sigma>2\<rangle>" and t2: "t2 = C2\<langle>r2 \<cdot> \<sigma>2\<rangle>"
    and NF2: "\<forall> u \<lhd> l2 \<cdot> \<sigma>2. u \<in> ?Q" and nfs2: "NF_subst nfs (l2, r2) \<sigma>2 Q" by auto
  from s1 s2 have id: "C1\<langle>l1 \<cdot> \<sigma>1\<rangle> = C2\<langle>l2 \<cdot> \<sigma>2\<rangle>" by simp
  let ?p = "\<lambda> (C1, C2). C1\<langle>l1 \<cdot> \<sigma>1\<rangle> = C2\<langle>l2 \<cdot> \<sigma>2\<rangle> \<longrightarrow> (\<exists> s'. (C1\<langle>r1 \<cdot> \<sigma>1\<rangle>, s') \<in> ?R \<and> (C2\<langle>r2 \<cdot> \<sigma>2\<rangle>, s') \<in> ?R \<or> C1\<langle>r1 \<cdot> \<sigma>1\<rangle> = C2\<langle>r2 \<cdot> \<sigma>2\<rangle>)"
  {
    fix C12
    let ?m = "\<lambda> (C1, C2). size C1 + size C2"
    have "?p C12"
    proof (induct rule: wf_induct [OF wf_measure [of ?m], of ?p])
      case (1 C12)
      obtain C1 C2 where C12: "C12 = (C1, C2)" by force
      show "?p C12" unfolding C12 split
      proof (intro impI)
        assume id: "C1\<langle>l1 \<cdot> \<sigma>1\<rangle> = C2\<langle>l2 \<cdot> \<sigma>2\<rangle>"
        show "\<exists> s'. ( (C1\<langle>r1 \<cdot> \<sigma>1\<rangle>, s') \<in> ?R \<and> (C2\<langle>r2 \<cdot> \<sigma>2\<rangle>, s') \<in> ?R \<or> C1\<langle>r1 \<cdot> \<sigma>1\<rangle> = C2\<langle>r2 \<cdot> \<sigma>2\<rangle>)"
        proof (cases C1)
          case Hole note C1 = this
          with id have id: "l1 \<cdot> \<sigma>1 = C2\<langle>l2 \<cdot> \<sigma>2\<rangle>" by simp
          have C2: "C2 = \<box>"
          proof (rule ccontr)
            assume "C2 \<noteq> \<box>"
            with id have "l2 \<cdot> \<sigma>2 \<lhd> l1 \<cdot> \<sigma>1" by auto
            with NF1 NF_Q_R have "l2 \<cdot> \<sigma>2 \<in> NF_trs R" by auto
            with lr2 show False by auto
          qed
          with id have ident: "l1 \<cdot> \<sigma>1 = l2 \<cdot> \<sigma>2"  by simp
          from lhss [OF lr1] have nvar: "is_Fun l1" .
          from mgu_vd_complete [OF ident]
          obtain \<mu>1 \<mu>2 \<rho> where mgu: "mgu_vd ren l1 l2 = Some (\<mu>1, \<mu>2)" and
            \<mu>1: "\<sigma>1 = \<mu>1 \<circ>\<^sub>s \<rho>"
            and \<mu>2: "\<sigma>2 = \<mu>2 \<circ>\<^sub>s \<rho>"
            by blast
          have in_cp: "(True, r2 \<cdot> \<mu>2, r1 \<cdot> \<mu>1) \<in> critical_pairs ren R R"
            by (rule critical_pairsI [OF lr1 lr2 _ nvar mgu, of \<box>], auto)
          from C2 have C2r\<sigma>: "C2\<langle>r2 \<cdot> \<sigma>2\<rangle> = r2 \<cdot> \<sigma>2" by simp
          from C1 have C1r\<sigma>: "C1\<langle>r1 \<cdot> \<sigma>1\<rangle> = r1 \<cdot> \<sigma>1" by simp
          from cp [OF in_cp, unfolded instance_rule_def] have id: "r1 \<cdot> \<mu>1 = r2 \<cdot> \<mu>2" ..
          from C1r\<sigma> have "C1\<langle>r1 \<cdot> \<sigma>1\<rangle> = r2 \<cdot> \<sigma>2" unfolding \<mu>1 using id \<mu>2 by simp
          also have "... = C2\<langle>r2 \<cdot> \<sigma>2\<rangle>" unfolding C2r\<sigma> ..
          finally show ?thesis by simp
        next
          case (More f1 bef1 D1 aft1) note C1 = this
          show ?thesis
          proof (cases C2)
            case Hole
            with id have "l2 \<cdot> \<sigma>2 = C1\<langle>l1 \<cdot> \<sigma>1\<rangle>" by auto
            with C1 have "l1 \<cdot> \<sigma>1 \<lhd> l2 \<cdot> \<sigma>2" by auto
            with NF2 NF_Q_R have "l1 \<cdot> \<sigma>1 \<in> NF_trs R" by auto
            with lr1 have False by auto
            then show ?thesis ..
          next
            case (More f2 bef2 D2 aft2) note C2 = this
            let ?n1 = "length bef1"
            let ?n2 = "length bef2"
            note id = id [unfolded C1 C2]
            from id have f: "f1 = f2" by simp
            show ?thesis
            proof (cases "?n1 = ?n2")
              case True
              with id have idb: "bef1 = bef2" and ida: "aft1 = aft2"
                and idD: "D1\<langle>l1 \<cdot> \<sigma>1\<rangle> = D2\<langle>l2 \<cdot> \<sigma>2\<rangle>" by auto
              have "((D1, D2), C12) \<in> measure ?m" unfolding C12 C1 C2
                by auto
              from 1 [rule_format, OF this, unfolded split, rule_format,
                OF idD] obtain s'
                where disj: "(D1\<langle>r1 \<cdot> \<sigma>1\<rangle>, s') \<in> ?R \<and> (D2\<langle>r2 \<cdot> \<sigma>2\<rangle>, s') \<in> ?R \<or> D1\<langle>r1 \<cdot> \<sigma>1\<rangle> = D2\<langle>r2 \<cdot> \<sigma>2\<rangle>" (is "?seq1 \<and> ?seq2 \<or> ?id") by auto
              let ?C = "More f2 bef2 \<box> aft2"
              have id1: "C1 = ?C \<circ>\<^sub>c D1" unfolding C1 f ida idb by simp
              have id2: "C2 = ?C \<circ>\<^sub>c D2" unfolding C2 by simp
              from disj show ?thesis
              proof
                assume "?seq1 \<and> ?seq2"
                then have seq1: "?seq1" and seq2: "?seq2" by auto
                from qrstep.ctxt [OF seq1, of ?C]
                have seq1: "(C1\<langle>r1 \<cdot> \<sigma>1\<rangle>, ?C\<langle>s'\<rangle>) \<in> ?R" using id1 by auto
                from qrstep.ctxt [OF seq2, of ?C]
                have seq2: "(C2\<langle>r2 \<cdot> \<sigma>2\<rangle>, ?C\<langle>s'\<rangle>) \<in> ?R" using id2 by auto
                from seq1 seq2 show ?thesis by auto
              next
                assume ?id
                then show ?thesis unfolding id1 id2 by simp
              qed
            next
              case False
              let ?p1 = "?n1 # hole_pos D1"
              let ?p2 = "?n2 # hole_pos D2"
              have l2: "C1\<langle>l1 \<cdot> \<sigma>1\<rangle> |_ ?p2 = l2 \<cdot> \<sigma>2" unfolding C1 id by simp
              have p12: "?p1  \<bottom> ?p2" using False by simp
              have p1: "?p1 \<in> poss (C1\<langle>l1 \<cdot> \<sigma>1\<rangle>)" unfolding C1 by simp
              have p2: "?p2 \<in> poss (C1\<langle>l1 \<cdot> \<sigma>1\<rangle>)" unfolding C1 unfolding id by simp
              let ?one = "replace_at (C1\<langle>l1 \<cdot> \<sigma>1\<rangle>) ?p1 (r1 \<cdot> \<sigma>1)"
              have one: "C1\<langle>r1 \<cdot> \<sigma>1\<rangle> = ?one" unfolding C1 by simp
              from parallel_qrstep [OF p12 p1 p2 l2 NF2 lr2 nfs2]
              have "(?one, replace_at ?one ?p2 (r2 \<cdot> \<sigma>2)) \<in> qrstep nfs Q R" .
              then have one: "(C1\<langle>r1 \<cdot> \<sigma>1\<rangle>, replace_at ?one ?p2 (r2 \<cdot> \<sigma>2)) \<in> qrstep nfs Q R" unfolding one by simp
              have l1: "C2\<langle>l2 \<cdot> \<sigma>2\<rangle> |_ ?p1 = l1 \<cdot> \<sigma>1" unfolding C2 id [symmetric] by simp
              have p21: "?p2  \<bottom> ?p1" using False by simp
              have p1': "?p1 \<in> poss (C2\<langle>l2 \<cdot> \<sigma>2\<rangle>)" unfolding C2 id [symmetric] by simp
              have p2': "?p2 \<in> poss (C2\<langle>l2 \<cdot> \<sigma>2\<rangle>)" unfolding C2 by simp
              let ?two = "replace_at (C2\<langle>l2 \<cdot> \<sigma>2\<rangle>) ?p2 (r2 \<cdot> \<sigma>2)"
              have two: "C2\<langle>r2 \<cdot> \<sigma>2\<rangle> = ?two" unfolding C2 by simp
              from parallel_qrstep [OF p21 p2' p1' l1 NF1 lr1 nfs1]
              have "(?two, replace_at ?two ?p1 (r1 \<cdot> \<sigma>1)) \<in> qrstep nfs Q R" .
              then have two: "(C2\<langle>r2 \<cdot> \<sigma>2\<rangle>, replace_at ?two ?p1 (r1 \<cdot> \<sigma>1)) \<in> qrstep nfs Q R" unfolding two by simp
              have "replace_at ?one ?p2 (r2 \<cdot> \<sigma>2) = replace_at (replace_at (C1\<langle>l1 \<cdot> \<sigma>1\<rangle>) ?p2 (r2 \<cdot> \<sigma>2)) ?p1 (r1 \<cdot> \<sigma>1)"
                by (rule parallel_replace_at [OF p12 p1 p2])
              also have "... = replace_at ?two ?p1 (r1 \<cdot> \<sigma>1)" unfolding C1 C2 id ..
              finally have one_two: "replace_at ?one ?p2 (r2 \<cdot> \<sigma>2) = replace_at ?two ?p1 (r1 \<cdot> \<sigma>1)" .
              show ?thesis
                by (intro exI disjI1 conjI, rule one, unfold one_two, rule two)
            qed
          qed
        qed
      qed
    qed
  }
  from this [of "(C1, C2)", unfolded split, rule_format, OF id]
  show "(t1, t2) \<in> ?R O ?R^-1" using t12 unfolding t1 t2 by auto
qed

lemma critical_pairs_innermost:
  assumes "\<And> l r. (True, l, r) \<in> critical_pairs ren R R \<Longrightarrow> l = r"
    and "NF_terms Q \<subseteq> NF_trs R"
    and "\<And> l r. (l, r) \<in> R \<Longrightarrow> is_Fun l"
  shows "CR (qrstep nfs Q R)"
  by (rule weak_diamond_imp_CR [OF critical_pairs_innermost_weak_diamond [OF assms]])

end
end