(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  Martin Avanzini <martin.avanzini@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Complexity_Framework
  imports
    Ord.Complexity
    TRS.Q_Relative_Rewriting
    First_Order_Rewriting.Multihole_Context
begin

context 
  fixes Cp FS F :: "'f sig" (* compound, F-sharp, F *)
begin

inductive_set Fsharp_terms :: "('f, 'v) term set"
where
  Fsharp_term:
    "(f, length ts) \<in> FS \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F) \<Longrightarrow> Fun f ts \<in> Fsharp_terms"

lemma Fsharp_terms_imp_is_Fun [dest, simp]:
  assumes "t \<in> Fsharp_terms"
  shows "is_Fun t"
  using assms by (cases) simp

inductive is_DP_complexity :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) complexity_measure \<Rightarrow> bool"
where
  is_DP_complexity: "wf_trs RS \<Longrightarrow> wf_trs R \<Longrightarrow> 
  funas_trs R \<subseteq> F \<Longrightarrow>
  lhss RS \<subseteq> Fsharp_terms \<Longrightarrow>
  (\<And> l r. (l, r) \<in> RS \<Longrightarrow> \<exists> C ts. r =\<^sub>f (C, ts) \<and> funas_mctxt C \<subseteq> Cp \<and> set ts \<subseteq> Fsharp_terms) \<Longrightarrow>
  FS \<inter> Cp = {} \<Longrightarrow> FS \<inter> F = {} \<Longrightarrow> Cp \<inter> F = {} \<Longrightarrow>
  (case cm of Runtime_Complexity C D \<Rightarrow> set C \<subseteq> F \<and> set D \<subseteq> FS \<union> Cp | _ \<Rightarrow> False) \<Longrightarrow>
  is_DP_complexity RS R cm"
(* perhaps one should demand "set D \<subseteq> FS" which is the requirement in Martin's thesis, but
   so far we can prove everything with "set D \<subseteq> FS \<union> Cp" *)

inductive_set Tsharp_terms :: "('f, 'v) term set"
where
  base: "funas_term t \<subseteq> F \<Longrightarrow> t \<in> Tsharp_terms"  |
  sharp: "t \<in> Fsharp_terms \<Longrightarrow> t \<in> Tsharp_terms" |
  compound: "(f, length ts) \<in> Cp \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> t \<in> Tsharp_terms) \<Longrightarrow> Fun f ts \<in> Tsharp_terms"

context 
  fixes RS R :: "('f, 'v) trs" and cm :: "('f, 'v) complexity_measure"
  assumes is_DP': "is_DP_complexity RS R cm"
begin

lemmas DP = is_DP' [unfolded is_DP_complexity.simps, simplified]

lemma terms_of_Tsharp_terms: "terms_of cm \<subseteq> Tsharp_terms"
proof -
  from DP obtain C D where cm: "cm = Runtime_Complexity C D" by (cases cm, auto)
  with DP have C: "set C \<subseteq> F" and D: "set D \<subseteq> FS \<union> Cp" by auto
  {
    fix t
    assume "t \<in> terms_of cm"
    from this[unfolded cm] C D
    obtain f ts where t: "t = Fun f ts" and f: "(f, length ts) \<in> FS \<union> Cp" and 
      args: "\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F"
      by (force simp: funas_args_term_def simp del: Un_iff)
    let ?f = "(f,length ts)"
    from f have "t \<in> Tsharp_terms"
    proof
      assume f: "?f \<in> FS"
      show ?thesis unfolding t 
        by (rule sharp, rule Fsharp_term[OF f args])
    next
      assume f: "?f \<in> Cp"
      show ?thesis unfolding t
        by (rule compound[OF f base[OF args]])
    qed
  }
  then show ?thesis by auto
qed 
  

lemma qrstep_Tsharp_terms: 
  assumes step: "(s,t) \<in> qrstep nfs Q (RS \<union> R)"
  and sT: "s \<in> Tsharp_terms"
  shows "t \<in> Tsharp_terms"
proof -
  note DP = DP[unfolded is_DP_complexity.simps, simplified]
  from DP have wf: "wf_trs (RS \<union> R)" by (auto simp: wf_trs_def)
  note funas_term_subst[simp]
  from step have "(s,t) \<in> rstep (RS \<union> R)" by auto
  from sT this show ?thesis
  proof (induct s arbitrary: t)
    case (base s t) note IH = this
    from IH(2) obtain C l r \<sigma> where lr: "(l,r) \<in> RS \<union> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
    from IH(1)[unfolded s] have lF: "funas_term l \<subseteq> F" by auto
    from wf_trs_imp_lhs_Fun[OF wf lr] obtain f ls where l: "l = Fun f ls" by auto
    with lF DP have f: "(f,length ls) \<notin> FS" by auto
    from lr have "(l,r) \<in> R"
    proof
      assume "(l,r) \<in> RS"
      with DP have "l \<in> Fsharp_terms" by auto
      from this l f show ?thesis by (cases, auto)
    qed
    with s t have "(s,t) \<in> rstep R" by auto
    from rstep_preserves_funas_terms[OF _ IH(1) this] DP have "funas_term t \<subseteq> F" by auto
    then show ?case ..
  next
    case (compound f ss) note IH = this
    from IH(4) obtain C l r \<sigma> where lr: "(l,r) \<in> RS \<union> R" and s: "Fun f ss = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
    from wf_trs_imp_lhs_Fun[OF wf lr] obtain g ls where l: "l = Fun g ls" by auto
    let ?g = "(g,length ls)"
    from lr DP have "funas_term l \<subseteq> F \<or> l \<in> Fsharp_terms" by (cases, (force simp: funas_trs_def funas_rule_def)+)
    then have "?g \<in> F \<or> ?g \<in> FS" 
    proof 
      assume "l \<in> Fsharp_terms"
      then show ?thesis unfolding l by (cases, auto)
    qed (simp add: l)
    with DP have g: "?g \<notin> Cp" by auto
    with s l IH(1) obtain bef D aft where C: "C = More f bef D aft" by (cases C, auto)
    with lr have step: "(D\<langle>l \<cdot> \<sigma>\<rangle>, D\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep (RS \<union> R)" by auto
    from s[unfolded C] have ss: "ss = bef @ D \<langle>l \<cdot> \<sigma>\<rangle> # aft" by auto
    then have "D\<langle>l \<cdot> \<sigma>\<rangle> \<in> set ss" by auto
    from IH(3)[OF this step] have rec: "D\<langle>r \<cdot> \<sigma>\<rangle> \<in> Tsharp_terms" by auto
    show ?case unfolding t C intp_actxt.simps
      by (rule Tsharp_terms.compound, insert IH(1-2) rec, auto simp: ss)
  next
    case (sharp s t) note IH = this
    from IH(2) obtain C l r \<sigma> where lr: "(l,r) \<in> RS \<union> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
    from IH(1)[unfolded s] have lF: "C\<langle>l \<cdot> \<sigma>\<rangle> \<in> Fsharp_terms" by auto
    from wf_trs_imp_lhs_Fun[OF wf lr] obtain f ls where l: "l = Fun f ls" by auto
    let ?f = "(f,length ls)"
    show ?case
    proof (cases C)
      case (More g bef D aft) note C = this
      let ?g = "(g,Suc (length bef + length aft))"
      from lF[unfolded C] have DF: "funas_term (D \<langle>l \<cdot> \<sigma>\<rangle>) \<subseteq> F" and g: "?g \<in> FS" 
        and b_a: "\<And> t. t \<in> set bef \<union> set aft \<Longrightarrow> funas_term t \<subseteq> F" by (cases, force)+
      with l DP have f: "(f,length ls) \<notin> FS" by auto
      from lr have lr: "(l,r) \<in> R"
      proof
        assume "(l,r) \<in> RS"
        with DP have "l \<in> Fsharp_terms" by auto
        from this l f show ?thesis by (cases, auto)
      qed
      from rstep_preserves_funas_terms[OF _ DF rstepI[OF lr refl refl]] DP
      have DF: "funas_term (D\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> F" by auto
      have "t \<in> Fsharp_terms" unfolding t C intp_actxt.simps
        by (rule Fsharp_term, insert g DF b_a, force+)
      then show ?thesis ..
    next
      case Hole note C = this
      from C lF have lF: "l \<cdot> \<sigma> \<in> Fsharp_terms" by simp
      from this[unfolded l] DP have f: "?f \<notin> F" by (cases, auto)
      from lr have lr: "(l,r) \<in> RS"
      proof
        assume "(l,r) \<in> R"
        with l DP have "?f \<in> F" unfolding funas_trs_def funas_rule_def[abs_def] by force
        with f show ?thesis by auto
      qed
      with DP obtain D ts where r: "r =\<^sub>f (D, ts)" and D: "funas_mctxt D \<subseteq> Cp" and 
          ts: "set ts \<subseteq> Fsharp_terms" by blast
      from lF[unfolded l] have "Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ls) \<in> Fsharp_terms" by simp
      then have li: "\<And> li. li \<in> set ls \<Longrightarrow> funas_term (li \<cdot> \<sigma>) \<subseteq> F" by (cases, force+)
      {
        fix x
        assume "x \<in> vars_term r"
        with lr wf[unfolded wf_trs_def]
        have "x \<in> vars_term l" by auto
        with l obtain li where "li \<in> set ls" and "x \<in> vars_term li" by auto
        with li[of li] have "funas_term (\<sigma> x) \<subseteq> F" by auto
      } note \<sigma> = this
      define \<tau> where "\<tau> = (\<lambda> x. if x \<in> vars_term r then \<sigma> x else Var x)"
      have r\<tau>: "r \<cdot> \<sigma> = r \<cdot> \<tau>"
        by (rule term_subst_eq, auto simp: \<tau>_def)
      have \<tau>: "\<And> x. funas_term (\<tau> x) \<subseteq> F" using \<sigma>
        by (auto simp: \<tau>_def)
      define tss where "tss = map (\<lambda>ti. ti \<cdot> \<tau>) ts"
      define r' where "r' = r \<cdot> \<sigma>"
      from subst_apply_mctxt_sound[OF r, of \<tau>] have rsig: "r \<cdot> \<sigma> =\<^sub>f (D \<cdot>mc \<tau>, tss)" unfolding r\<tau> tss_def .
      {
        fix t'
        assume "t' \<in> set tss"
        then obtain t where tts: "t \<in> set ts" and t': "t' = t \<cdot> \<tau>" unfolding tss_def by auto
        with ts have "t \<in> Fsharp_terms" by auto
        then obtain f us where t: "t = Fun f us" and f: "(f,length us) \<in> FS" 
          and us: "\<And> u. u \<in> set us \<Longrightarrow> funas_term u \<subseteq> F" by (cases, auto)
        {
          fix u
          assume u: "u \<in> set us"
          from us[OF u] have uF: "funas_term u \<subseteq> F" by auto
          with \<tau> have "funas_term (u \<cdot> \<tau>) \<subseteq> F" by auto
        } note us = this
        with f have "t' \<in> Fsharp_terms" unfolding t' t eval_term.simps
          by (intro Fsharp_term, force+)
      } 
      then have "set tss \<subseteq> Fsharp_terms" by auto
      with D rsig have "r \<cdot> \<sigma> \<in> Tsharp_terms" unfolding r'_def[symmetric]
      proof (induct D arbitrary: r' tss)
        case (MHole r tss)
        note eq = eqfE[OF MHole(2)]
        from eq obtain t where tss: "tss = [t]" by (cases tss, auto)
        with eq have "r = t" by auto
        with MHole(3) tss show ?case by (auto intro: Tsharp_terms.sharp)
      next
        case (MVar x r tss)
        note eq = eqfE[OF MVar(2)]
        from eq have "r = \<tau> x" by simp
        with \<tau>[of x] show ?case by (auto intro: Tsharp_terms.base)
      next
        case (MFun f Ds r tss)
        let ?n = "length Ds"
        from MFun(3) have "r =\<^sub>f (MFun f (map (\<lambda> D. D \<cdot>mc \<tau>) Ds), tss)" by auto
        from eqf_MFunE[OF this]
        obtain rs sss where 
        r: "r = Fun f rs"
        and len: "length rs = ?n"
          "length sss = ?n"
        and rec: "\<And>i. i < ?n \<Longrightarrow> rs ! i =\<^sub>f (Ds ! i \<cdot>mc \<tau>, sss ! i)"
        and tss: "tss = concat sss" by auto
        {
          fix i
          assume i: "i < ?n"
          then have mem: "Ds ! i \<in> set Ds" by auto
          with MFun(2) have Cp: "funas_mctxt (Ds ! i) \<subseteq> Cp" by auto
          from i len have "sss ! i \<in> set sss" by auto
          with tss have "set (sss ! i) \<subseteq> set tss" by auto
          with MFun(4) have "set (sss ! i) \<subseteq> Fsharp_terms" by auto
          from MFun(1)[OF mem Cp rec[OF i] this] have "rs ! i \<in> Tsharp_terms" .
        } 
        with len have IH: "set rs \<subseteq> Tsharp_terms" unfolding set_conv_nth by auto
        from MFun(2) len have "(f,length rs) \<in> Cp" by auto
        from Tsharp_terms.compound[OF this] IH have "Fun f rs \<in> Tsharp_terms" by auto
        with r show ?case by simp
      qed
      then show ?thesis unfolding t C by simp
    qed
  qed
qed

lemma avanzini_14_20: 
  "(qrstep nfs Q (RS \<union> R))^* `` Tsharp_terms \<subseteq> Tsharp_terms"
  "(qrstep nfs Q (RS \<union> R))^* `` terms_of cm \<subseteq> Tsharp_terms"
proof -
  let ?R = "qrstep nfs Q (RS \<union> R)" let ?T = "Tsharp_terms"
  {
    fix t
    assume "t \<in> ?R^* `` ?T"
    then obtain s where s: "s \<in> ?T" and st: "(s,t) \<in> ?R^*" by auto
    from st have "t \<in> ?T"
    proof (induct)
      case base
      show ?case by (rule s)
    next
      case (step t v)
      from qrstep_Tsharp_terms[OF step(2-3)] show ?case .
    qed
  }
  then show one: "?R^* `` ?T \<subseteq> ?T" by auto
  from one terms_of_Tsharp_terms show "?R^* `` terms_of cm \<subseteq> ?T" by blast
qed

end
end
end
