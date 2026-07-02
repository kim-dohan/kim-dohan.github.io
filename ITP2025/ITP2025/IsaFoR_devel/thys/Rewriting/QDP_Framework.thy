(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory QDP_Framework
imports
  Q_Relative_Rewriting
begin

type_synonym ('f, 'v) dpp =
  "bool \<times> bool \<times> ('f, 'v) trs \<times> ('f, 'v) trs \<times> ('f, 'v) terms \<times> ('f, 'v) trs \<times> ('f, 'v) trs"

fun
  ichain :: "('f, 'v) dpp \<Rightarrow> ('f, 'v) term seq \<Rightarrow> ('f, 'v) term seq \<Rightarrow> ('f, 'v) subst seq \<Rightarrow> bool"
where
  "ichain (nfs, m, P, Pw, Q, R, Rw) s t \<sigma> \<longleftrightarrow>
    (\<forall>i. (s i, t i) \<in> P \<union> Pw) \<and> 
    ((INFM i. (s i, t i) \<in> P) \<or>
      (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
        (qrstep nfs Q (R \<union> Rw))\<^sup>* O qrstep nfs Q R O (qrstep nfs Q (R \<union> Rw))\<^sup>*)) \<and> 
    (\<forall>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q (R \<union> Rw))\<^sup>*) \<and>
    (\<forall>i. s i \<cdot> \<sigma> i \<in> NF_terms Q) \<and>
    (\<forall>i. NF_subst nfs (s i, t i) (\<sigma> i) Q)"

lemma ichain_alternative: 
  "ichain (nfs, m, P, Pw, Q, R, Rw) s t \<sigma> = (\<exists> f n.
    (\<forall>i. (s i,t i) \<in> P \<union> Pw) \<and> 
    (\<forall>i. (f i 0 = t i \<cdot> \<sigma> i) \<and> (f i (n i) = s (Suc i) \<cdot> \<sigma> (Suc i)) \<and>
          (\<forall> j < n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q (R \<union> Rw))) \<and>
    (\<forall>i. s i \<cdot> \<sigma> i \<in> NF_terms Q) \<and>
    (\<forall>i. NF_subst nfs (s i, t i) (\<sigma> i) Q)
    \<and> ((INFM i. (s i, t i) \<in> P) \<or> (INFM i. \<exists> j < n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q R)))" (is "?l = ?r")
proof -
  let ?QR = "qrstep nfs Q (R \<union> Rw)"
  let ?QRS = "?QR\<^sup>* O qrstep nfs Q R O ?QR\<^sup>*"
  show ?thesis
  proof
    assume ?r
    then obtain f n
      where P: "(\<forall>i. (s i,t i) \<in> P \<union> Pw)" and
      steps: "\<And> i. (f i 0 = t i \<cdot> \<sigma> i) \<and> (f i (n i) = s (Suc i) \<cdot> \<sigma> (Suc i)) \<and>
      (\<forall> j < n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q (R \<union> Rw))"
      and nf: "(\<forall>i. s i \<cdot> \<sigma> i \<in> NF_terms Q)"
      and nfs: "(\<forall>i. NF_subst nfs (s i, t i) (\<sigma> i) Q)"
      and inf: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. (\<exists> j < n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q R))" (is "?one \<or> ?two") by auto
    {
      fix i j j'
      assume j: "j \<le> j'" and j': "j' \<le> n i"
      have "(f i j, f i j') \<in> ?QR\<^sup>*"
        unfolding rtrancl_fun_conv
      proof (rule exI[of _ "\<lambda> n. f i (j + n)"], rule exI[of _ "j' - j"], insert j,
          simp, intro allI impI)
        fix m
        assume "m < j' - j"
        then have "j + m < j'" by auto
        with j' have jm: "j + m < n i" by auto
        with steps[of i]
        show "(f i (j + m), f i (Suc (j+m))) \<in> ?QR" by auto
      qed
    } note Rsteps = this
    {
      fix i
      from steps[of i] Rsteps[of 0 "n i" i]
      have "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR\<^sup>*" by auto
    } note steps' = this
    from inf have inf: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      ?QRS)" (is "?one' \<or> ?two'")
    proof
      assume ?one then show ?thesis by auto
    next
      assume ?two 
      have ?two'
        unfolding INFM_nat
      proof (intro allI)
        fix m
        from \<open>?two\<close>[unfolded INFM_nat] obtain k j where k: "k > m" and j: "j < n k" and step: "(f k j, f k (Suc j)) \<in> qrstep nfs Q R" by blast
        from Rsteps[of 0 j k] j have bef: "(f k 0, f k j) \<in> ?QR\<^sup>*" by auto
        from Rsteps[of "Suc j" "n k" k] j have aft: "(f k (Suc j), f k (n k)) \<in> ?QR\<^sup>*" by auto
        from bef step aft have "(f k 0, f k (n k)) \<in> ?QRS" by auto
        with steps[of k] have main: "(t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> ?QRS" by auto
        show "\<exists> k > m. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> ?QRS"
          by (intro exI conjI, rule k, rule main)
      qed
      then show ?thesis ..
    qed
    from P nf nfs steps' inf show ?l by simp
  next
    assume ?l
    let ?pair = "\<lambda> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i))"
    let ?strict = "\<lambda> i. ?pair i \<in> ?QRS"
    from \<open>?l\<close> have P: "\<forall> i. (s i, t i) \<in> P \<union> Pw"
      and inf: "(\<exists>\<^sub>\<infinity>i. (s i, t i) \<in> P) \<or>
   (\<exists>\<^sub>\<infinity>i. ?strict i)" (is "?one \<or> ?two")
     and steps: "\<And> i. ?pair i \<in> ?QR\<^sup>*"
     and nf: "\<forall> i. s i \<cdot> \<sigma> i \<in> NF_terms Q" 
     and nfs: "(\<forall>i. NF_subst nfs (s i, t i) (\<sigma> i) Q)" by auto
    {
      fix i      
      note steps[of i, unfolded rtrancl_fun_conv]
    } note fns = this
    {
      fix i
      assume "?strict i"
      then obtain u v where bef: "(t i \<cdot> \<sigma> i, u) \<in> ?QR\<^sup>*"
        and step: "(u,v) \<in> qrstep nfs Q R"
        and aft: "(v,s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QR\<^sup>*" by auto
      from bef[unfolded rtrancl_fun_conv] obtain fb nb
        where b: "fb 0 = t i \<cdot> \<sigma> i \<and> fb nb = u \<and> (\<forall> i < nb. (fb i, fb (Suc i)) \<in> ?QR)" by auto
      from aft[unfolded rtrancl_fun_conv] obtain fa na
        where a: "fa 0 = v \<and> fa na = s (Suc i) \<cdot> \<sigma> (Suc i) \<and> (\<forall> i < na. (fa i, fa (Suc i)) \<in> ?QR)" by auto
      let ?f = "\<lambda> n. if n \<le> nb then fb n else fa (n - Suc nb)"
      let ?n = "Suc (nb + na)"
      {
        fix i
        assume i: "i < ?n"
        have "(?f i, ?f (Suc i)) \<in> ?QR"
        proof (cases "i < nb")
          case True
          with b show ?thesis by auto
        next
          case False note oFalse = this
          show ?thesis
          proof (cases "i = nb")
            case True
            with a b qrstep_mono[of R "R \<union> Rw" Q Q] step show ?thesis by auto
          next
            case False
            with oFalse have "i > nb" by auto
            then have "i = i - Suc nb + Suc nb" by auto
            then obtain ii where ii: "i = ii + Suc nb" ..
            with i have i: "ii < na" by auto
            from i a show ?thesis unfolding ii by simp
          qed
        qed
      } note steps = this
      from a b step have step: "(?f nb, ?f (Suc nb)) \<in> qrstep nfs Q R" by auto
      have step: "\<exists> n < ?n. (?f n, ?f (Suc n)) \<in> qrstep nfs Q R" 
        by (rule exI[of _ nb], rule conjI[OF _ step], simp)
      have "\<exists> f n. f 0 = (t i \<cdot> \<sigma> i) \<and> f n = (s (Suc i) \<cdot> \<sigma> (Suc i)) \<and> (\<forall> m < n. (f m, f (Suc m)) \<in> ?QR) \<and> (\<exists> k < n. (f k, f (Suc k)) \<in> qrstep nfs Q R)"
        by (rule exI[of _ ?f], rule exI[of _ ?n], simp add: step steps a b)
    } note gns = this
    let ?Pf = "\<lambda> f n i.  
             f 0 = (t i \<cdot> \<sigma> i) \<and> f n = (s (Suc i) \<cdot> \<sigma> (Suc i)) \<and> (\<forall> m < n. (f m, f (Suc m)) \<in> ?QR)"
    let ?Pg = "\<lambda> f n i.  ?strict i \<longrightarrow> 
             ?Pf f n i \<and> (\<exists> k < n. (f k, f (Suc k)) \<in> qrstep nfs Q R)"
    from choice[OF allI[OF fns]] obtain f where "\<forall> i. \<exists> n. ?Pf (f i) n i" ..
    from choice[OF this] obtain nf where f: "\<And> i. ?Pf (f i) (nf i) i" by auto
    from gns have "\<forall> i. \<exists> f n. ?Pg f n i" by auto
    from choice[OF this] obtain g where "\<forall> i. \<exists> n. ?Pg (g i) n i" by auto
    from choice[OF this] obtain ng where g: "\<And> i. ?Pg (g i) (ng i) i" by auto
    let ?f = "\<lambda> i. if ?strict i then g i else f i"
    let ?n = "\<lambda> i. if ?strict i then ng i else nf i"
    show ?r
    proof (rule exI[of _ ?f], rule exI[of _ ?n], rule conjI[OF P], rule conjI[OF _ conjI[OF nf conjI[OF nfs]]])
      show "\<forall> i. ?Pf (?f i) (?n i) i" 
      proof 
        fix i
        show "?Pf (?f i) (?n i) i"
          using f g by (cases "?strict i", auto)
      qed
    next
      from inf
      show "?one \<or> (INFM i. \<exists> j < ?n i. (?f i j, ?f i (Suc j)) \<in> qrstep nfs Q R)" (is "_ \<or> ?two'")
      proof
        assume ?one then show ?thesis ..
      next
        assume ?two
        have ?two'
          unfolding INFM_nat
        proof (intro allI)
          fix m
          from \<open>?two\<close>[unfolded INFM_nat] obtain n where n: "n > m" and s: "?strict n" by blast
          from g[of n] s have j: "\<exists> j < ?n n. (?f n j, ?f n (Suc j)) \<in> qrstep nfs Q R" by auto
          show "\<exists> i > m. \<exists> j < ?n i. (?f i j, ?f i (Suc j)) \<in> qrstep nfs Q R"
            by (rule exI, intro conjI, rule n, rule j)
        qed
        then show ?thesis ..
      qed
    qed              
  qed
qed

definition "minimal_cond nfs Q R s t \<sigma> \<longleftrightarrow> (\<forall>i. SN_on (qrstep nfs Q R) {t i \<cdot> \<sigma> i})"

text \<open>
  A \emph{minimal infinite chain} is an infinite chain where additionally all @{term \<sigma>}-instances
  of terms in the sequence~@{term t} are terminating w.r.t.~@{term R}.
\<close>
fun min_ichain ::
 "('f, 'v) dpp \<Rightarrow> ('f, 'v) term seq \<Rightarrow> ('f, 'v) term seq \<Rightarrow> ('f, 'v) subst seq \<Rightarrow> bool"
where
  "min_ichain (nfs, m, P, Pw, Q, R, Rw) s t \<sigma> \<longleftrightarrow>
    ichain (nfs, m, P, Pw, Q, R, Rw) s t \<sigma> \<and> (m \<longrightarrow> minimal_cond nfs Q (R \<union> Rw) s t \<sigma>)"

definition
  funas_ichain ::
    "(nat \<Rightarrow> ('f, 'v) term) \<Rightarrow> (nat \<Rightarrow> ('f, 'v) term) \<Rightarrow> (nat \<Rightarrow> ('f, 'v) subst) \<Rightarrow> 'f sig"
where
  "funas_ichain s t \<sigma> = \<Union>{\<Union>(funas_term ` range (\<sigma> i)) | i. True}"

lemma funas_ichain_shift: "funas_ichain (shift s i) (shift t i) (shift \<sigma> i) \<subseteq> funas_ichain s t \<sigma>" unfolding funas_ichain_def by auto

fun min_ichain_sig ::
 "('f,'v)dpp \<Rightarrow> 'f sig \<Rightarrow> (nat \<Rightarrow> ('f,'v)term) \<Rightarrow> (nat \<Rightarrow> ('f,'v)term) \<Rightarrow> (nat \<Rightarrow> ('f,'v)subst) \<Rightarrow> bool"
where "min_ichain_sig dpp F s t \<sigma> = (min_ichain dpp s t \<sigma> \<and> funas_ichain s t \<sigma> \<subseteq> F)"

lemma ichain_imp_map_ichain:
  assumes chain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows "ichain (nfs,m,map_funs_trs fg P, map_funs_trs fg Pw,{},map_funs_trs fg R,map_funs_trs fg Rw) (\<lambda> i. map_funs_term fg (s i)) (\<lambda> i. map_funs_term fg (t i)) (\<lambda> i. map_funs_subst fg (\<sigma> i))"
  (is "ichain (_,_,?lP, ?lPw,{},?lR,?lRw) ?ls ?lt ?lsig")
proof -
  have mem: "\<forall> i. (?ls i, ?lt i) \<in> ?lP \<union> ?lPw"
  proof
    fix i
    from chain have "(s i, t i) \<in> P \<union> Pw" by auto
    then show "(?ls i, ?lt i) \<in> ?lP \<union> ?lPw" by (force simp: map_funs_trs.simps)
  qed
  let ?QRW = "qrstep nfs Q (R \<union> Rw)"
  let ?QR = "qrstep nfs Q R"
  from chain have inf: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?QRW\<^sup>* O ?QR O ?QRW\<^sup>*) " (is "?P \<or> ?R") by auto
  let ?ilP = "INFM i. (?ls i, ?lt i) \<in> ?lP" 
  {
    assume ?P
    then have ?ilP unfolding INFM_nat
      by (force simp: map_funs_trs.simps)    
  } note inf1 = this
  let ?RR = "(rstep (?lR \<union> ?lRw))\<^sup>* O rstep ?lR O (rstep (?lR \<union> ?lRw))\<^sup>*"
  let ?ilR = "INFM i. (?lt i \<cdot> ?lsig i, ?ls (Suc i) \<cdot> ?lsig (Suc i)) \<in> ?RR"
  {
    assume ?R
    have ?ilR 
      unfolding INFM_nat
    proof
      fix m
      from \<open>?R\<close>[unfolded INFM_nat]
      obtain n where n: "n > m" and steps: "(t n \<cdot> \<sigma> n, s (Suc n) \<cdot> \<sigma> (Suc n)) \<in> ?QRW\<^sup>* O ?QR O ?QRW\<^sup>*" by blast
      from steps obtain u v where steps: "(t n \<cdot> \<sigma> n, u) \<in> ?QRW\<^sup>*" "(u,v) \<in> ?QR" "(v,s (Suc n) \<cdot> \<sigma> (Suc n)) \<in> ?QRW\<^sup>*" by auto
      from qrsteps_imp_map_rsteps[OF steps(1), of fg] 
        qrstep_imp_map_rstep[OF steps(2), of fg] 
        qrsteps_imp_map_rsteps[OF steps(3), of fg] 
      have "(map_funs_term fg (t n \<cdot> \<sigma> n), map_funs_term fg (s (Suc n) \<cdot> \<sigma> (Suc n))) \<in> ?RR"
        unfolding map_funs_trs_union by auto
      then show "\<exists> n > m. (?lt n \<cdot> ?lsig n, ?ls (Suc n) \<cdot> ?lsig (Suc n)) \<in> ?RR"
        using n by auto
    qed      
  } note inf2 = this
  from inf inf1 inf2 have inf: "?ilP \<or> ?ilR" by blast
  have steps: "\<forall> i. (?lt i \<cdot> ?lsig i, ?ls (Suc i) \<cdot> ?lsig (Suc i)) \<in> (rstep (?lR \<union> ?lRw))\<^sup>*"
  proof
    fix i
    from chain have "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q (R \<union> Rw))\<^sup>*" by auto
    from qrsteps_imp_map_rsteps[OF this]
    have steps: "(map_funs_term fg (t i \<cdot> \<sigma> i), map_funs_term fg (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> (rstep (map_funs_trs fg (R \<union> Rw)))\<^sup>*" .
    have "map_funs_trs fg (R \<union> Rw) = ?lR \<union> ?lRw" unfolding map_funs_trs_union ..
    from steps[unfolded this] show"(?lt i \<cdot> ?lsig i, ?ls (Suc i) \<cdot> ?lsig (Suc i)) \<in> (rstep (?lR \<union> ?lRw))\<^sup>*" by auto
  qed
  from mem steps inf show ?thesis by simp
qed


lemma min_ichain_imp_ichain:
  assumes "min_ichain DPP s t \<sigma>" shows "ichain DPP s t \<sigma>"
using assms by (cases DPP) simp_all


definition ci_subset :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "ci_subset R S \<longleftrightarrow> (\<forall> l r. (l,r) \<in> R \<longrightarrow> (\<exists> l' r' C. (l',r') \<in> S \<and> l = C\<langle>l'\<rangle> \<and> r = C\<langle>r'\<rangle>))"

notation (xsymbols)
  ci_subset ("(_/ \<subseteq>ci _)" [50,51] 50)

lemma ci_subsetI:
  assumes "R \<subseteq> S"
  shows "ci_subset R S"
unfolding ci_subset_def
proof (intro allI impI)
  fix l r
  assume "(l,r) \<in> R"
  with assms have S: "(l,r) \<in> S" by auto
  show "\<exists> l' r' C. (l',r') \<in> S \<and> l = C\<langle>l'\<rangle> \<and> r = C\<langle>r'\<rangle>"
    by (rule exI[of _ l], rule exI[of _ r], rule exI[of _ \<box>], simp add: S)
qed

lemma ci_subset_refl: "R \<subseteq>ci R"
proof (unfold ci_subset_def, intro allI impI)
  fix l r
  assume rule: "(l,r) \<in> R"
  show "\<exists> l' r' C.  (l', r') \<in> R \<and> l = C\<langle>l'\<rangle> \<and> r = C\<langle>r'\<rangle>"
    by (rule exI[of _ l], rule exI[of _ r], rule exI[of _ \<box>], auto simp: rule)
qed

(* generalization of one direction of thm rstep_subset_characterization,
   the other direction does not hold in general, perhaps restrict to
   applicable rules *)
(* for nfs it does not hold in general, but perhaps allow a bit *)
lemma ctxt_qrstep_subset:
  assumes "\<And> l r. (l,r) \<in> R \<Longrightarrow> (\<exists> l' r' C \<sigma> . (l',r') \<in> S \<and> l = C\<langle>l' \<cdot> \<sigma>\<rangle> \<and> r = C\<langle>r' \<cdot> \<sigma>\<rangle>)" 
  and nnfs: "\<not> nfs"
  shows "qrstep nfs Q R \<subseteq> qrstep nfs Q S" 
proof (rule subsetI, simp add: split_paired_all)
  fix s t
  assume "(s,t) \<in> qrstep nfs Q R"
  then obtain C \<sigma> l r where nf: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms Q" and lr: "(l,r) \<in> R" and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" 
  and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  from lr assms  obtain l' r' C' \<sigma>' where Srule: "(l',r') \<in> S" and l: "l = C'\<langle>l' \<cdot> \<sigma>'\<rangle>" and r: "r = C'\<langle>r' \<cdot> \<sigma>'\<rangle>"
    by (force simp: Let_def)+
  let ?D = "C \<circ>\<^sub>c (C' \<cdot>\<^sub>c \<sigma>)"
  let ?sig = "\<sigma>' \<circ>\<^sub>s \<sigma>"
  have s2: "s = ?D\<langle>l' \<cdot> ?sig\<rangle>" by (simp add: s l)
  have t2: "t = ?D\<langle>r' \<cdot> ?sig\<rangle>" by (simp add: t r)
  show "(s,t) \<in> qrstep nfs Q S"
  proof(rule qrstepI[OF _ Srule s2 t2], intro allI impI)
    fix u
    assume gt: "l' \<cdot> \<sigma>' \<circ>\<^sub>s \<sigma> \<rhd> u"
    have "l \<cdot> \<sigma> \<unrhd> l' \<cdot> \<sigma>' \<circ>\<^sub>s \<sigma>" unfolding l by auto
    from supteq_supt_trans[OF this gt] nf
    show "u \<in> NF_terms Q" by auto
  qed (insert nnfs, simp)      
qed
  
lemma qrstep_ci_mono: assumes "R \<subseteq>ci S" and nfs: "\<not> nfs"
  shows "qrstep nfs Q R \<subseteq> qrstep nfs Q S"
proof(rule ctxt_qrstep_subset[OF _ nfs])
  fix l r
  assume "(l,r) \<in> R"
  with assms obtain l' r' C where cond: "(l',r') \<in> S \<and> l = C\<langle>l'\<rangle> \<and> r = C\<langle>r'\<rangle>" unfolding ci_subset_def by blast
  show "\<exists> l' r' C \<sigma>. (l',r') \<in> S \<and> l = C\<langle>l' \<cdot> \<sigma>\<rangle> \<and> r = C\<langle>r' \<cdot> \<sigma>\<rangle>"
    by (rule exI[of _ l'], rule exI[of _ r'], rule exI[of _ C], rule exI[of _ Var], simp add: cond)
qed

lemma minimal_cond_mono: 
  assumes subset: "R \<subseteq> R'" and cond: "minimal_cond nfs Q R' s t \<sigma>" 
  shows "minimal_cond nfs Q R s t \<sigma>"
unfolding minimal_cond_def
proof 
  fix i
  from cond have SN: "SN_on (qrstep nfs Q R') {t i \<cdot> \<sigma> i}"
    unfolding minimal_cond_def by auto
  have "qrstep nfs Q R \<subseteq> qrstep nfs Q R'" by (rule qrstep_rules_mono[OF subset])
  with SN show "SN_on (qrstep nfs Q R) {t i \<cdot> \<sigma> i}" by (rule SN_on_subset1)
qed

lemma minimal_cond_ci_mono: 
  assumes subset: "R \<subseteq>ci R'" and cond: "minimal_cond nfs Q R' s t \<sigma>" 
  and nfs: "\<not> nfs"
  shows "minimal_cond nfs Q R s t \<sigma>"
unfolding minimal_cond_def
proof 
  fix i
  from cond have SN: "SN_on (qrstep nfs Q R') {t i \<cdot> \<sigma> i}"
    unfolding minimal_cond_def by auto
  have "qrstep nfs Q R \<subseteq> qrstep nfs Q R'" by (rule qrstep_ci_mono[OF subset nfs])
  with SN show "SN_on (qrstep nfs Q R) {t i \<cdot> \<sigma> i}" by (rule SN_on_subset1)
qed


lemma min_ichainI[intro]: 
  assumes sub: "R \<union> Rw \<subseteq> R' \<union> Rw'" and m: "m \<Longrightarrow> minimal_cond nfs Q (R' \<union> Rw') s t \<sigma>" and i: "ichain (nfs,m,P,Pw,Q,R,Rw) (shift s i) (shift t i) (shift \<sigma> i)" 
  shows "min_ichain (nfs,m,P,Pw,Q,R,Rw) (shift s i) (shift t i) (shift \<sigma> i)"
proof (cases m)
  case False
  with assms show ?thesis by simp
next
  case True
  from minimal_cond_mono[OF sub m[OF True]]
  have "minimal_cond nfs Q (R \<union> Rw) (shift s i) (shift t i) (shift \<sigma> i)" 
    unfolding minimal_cond_def by auto
  with i show ?thesis by auto
qed

lemma min_ichain_ciI: 
  assumes sub: "R \<union> Rw \<subseteq>ci R' \<union> Rw'" and nfs: "\<not> nfs" and m: "m \<Longrightarrow> minimal_cond nfs Q (R' \<union> Rw') s t \<sigma>" and i: "ichain (nfs,m,P,Pw,Q,R,Rw) (shift s i) (shift t i) (shift \<sigma> i)" 
  shows "min_ichain (nfs,m,P,Pw,Q,R,Rw) (shift s i) (shift t i) (shift \<sigma> i)"
proof (cases m)
  case False
  with assms show ?thesis by simp
next
  case True
  from minimal_cond_ci_mono[OF sub m[OF True] nfs]
  have "minimal_cond nfs Q (R \<union> Rw) (shift s i) (shift t i) (shift \<sigma> i)" 
    unfolding minimal_cond_def by auto
  with i show ?thesis by auto
qed

lemma ichain_split_gen: assumes chain: "ichain (nfs,m,P,Pw,Q,R,Rw \<union> E) s t \<sigma>"
  and nchain: "\<not> ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs \<union> E) s t \<sigma>"
  shows "\<exists> i. ichain (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs \<union> E) (shift s i) (shift t i) (shift \<sigma> i)"
proof -
  have Pw: "P \<union> Pw = (Ps \<inter> (P \<union> Pw)) \<union> (P \<union> Pw - Ps)" by auto
  have Rw: "R \<union> (Rw \<union> E) = (Rs \<inter> (R \<union> Rw)) \<union> (R \<union> Rw - Rs \<union> E)" by auto
  let ?Rw = "qrstep nfs Q (R \<union> (Rw \<union> E))"
  let ?R = "qrstep nfs Q R"
  from chain[unfolded ichain_alternative]
  obtain f n where P: "\<And> i. (s i, t i) \<in> P \<union> Pw"
    and steps: "\<And> i. f i 0 = t i \<cdot> \<sigma> i \<and> f i (n i) = s (Suc i) \<cdot> \<sigma> (Suc i) \<and> (\<forall> j < n i. (f i j, f i (Suc j)) \<in> ?Rw)"
    and nf: "\<And> i. s i \<cdot> \<sigma> i \<in> NF_terms Q"
    and nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q"
    and inf: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. \<exists> j < n i. (f i j, f i (Suc j)) \<in> ?R)" by auto
  show ?thesis
  proof (cases "(INFM i. (s i, t i) \<in> Ps \<inter> (P \<union> Pw)) \<or> (INFM i. \<exists> j < n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q (Rs \<inter> (R \<union> Rw)))")
    case True
    have "ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs \<union> E) s t \<sigma>"
      unfolding ichain_alternative
      by (rule exI[of _ f], rule exI[of _ n], insert True P steps nf nfs, simp add: Rw[symmetric])
    with nchain
    show ?thesis ..
  next
    case False
    from False[unfolded de_Morgan_disj not_INFM MOST_conj_distrib[symmetric], unfolded MOST_nat]
    obtain i where Pn: "\<And> j. i < j \<Longrightarrow> (s j, t j) \<notin> Ps \<inter> (P \<union> Pw)"
      and Rn: "\<And> j k. i < j \<Longrightarrow> k < n j \<Longrightarrow> (f j k, f j (Suc k)) \<notin> qrstep nfs Q (Rs \<inter> (R \<union> Rw))"
      by auto
    from P Pn have P: "\<And> j. i < j \<Longrightarrow> (s j, t j) \<in> P \<union> Pw - Ps" by auto
    {
      fix j
      assume j: "i < j"
      {
        fix k
        assume k: "k < n j"
        from steps[of j] k  have step: "(f j k, f j (Suc k)) \<in> ?Rw" by auto
        from Rn[OF j k] have nstep: "(f j k, f j (Suc k)) \<notin> qrstep nfs Q (Rs \<inter> (R \<union> Rw))" by auto
        from step nstep have "(f j k, f j (Suc k)) \<in> qrstep nfs Q (R \<union> Rw - Rs \<union> E)"
          unfolding qrstep_rule_conv[where R = "R \<union> (Rw \<union> E)"]
          unfolding qrstep_rule_conv[where R = "R \<union> Rw - Rs \<union> E"]
          unfolding qrstep_rule_conv[where R = "Rs \<inter> (R \<union> Rw)"] by blast
      }
    } note R = this
    from inf have inf: "(INFM j. (shift s (Suc i) j, shift t (Suc i) j) \<in> P - Ps) \<or> 
      (INFM j. \<exists> k < n (j + Suc i). (f (j + Suc i) k, f (j + Suc i) (Suc k)) \<in> qrstep nfs Q (R - Rs))" (is "?l \<or> ?r")
    proof
      assume iP: "INFM i. (s i, t i) \<in> P"
      have ?l unfolding INFM_nat
      proof
        fix m
        from iP[unfolded INFM_nat]
        obtain n where n: "m + Suc i < n" and "(s n, t n) \<in> P" by auto
        with P[of n] have P: "(s n, t n) \<in> P - Ps" by auto
        show "\<exists> n > m. (shift s (Suc i) n, shift t (Suc i) n) \<in> P - Ps" 
          by (rule exI[of _ "n - Suc i"], insert n P, auto)
      qed
      then show ?thesis ..
    next
      assume iR: "INFM j. \<exists> k < n j. (f j k, f j (Suc k)) \<in> ?R"
      have ?r unfolding INFM_nat
      proof
        fix m
        from iR[unfolded INFM_nat]
        obtain mm k where mm: "m + Suc i < mm" and k: "k < n mm" and step: "(f mm k, f mm (Suc k)) \<in> ?R" by blast      
        from Rn[OF _ k] mm have step2: "(f mm k, f mm (Suc k)) \<notin> qrstep nfs Q (Rs \<inter> (R \<union> Rw))" by auto
        from step step2 have R: "(f mm k, f mm (Suc k)) \<in> qrstep nfs Q (R - Rs)" 
          unfolding qrstep_rule_conv[of _ _ nfs _ R]
          unfolding qrstep_rule_conv[of _ _ nfs _ "Rs \<inter> (R \<union> Rw)"]
          unfolding qrstep_rule_conv[of _ _ nfs _ "R - Rs"]
          by auto
        show "\<exists> mm > m. \<exists> k < n (mm + Suc i). (f (mm + Suc i) k, f (mm + Suc i) (Suc k)) \<in> qrstep nfs Q (R - Rs)"
          by (rule exI[of _ "mm - Suc i"], insert mm k R, auto)
      qed
      then show ?thesis ..
    qed
    let ?g = "\<lambda> j. f (j + Suc i)"
    let ?n = "\<lambda> j. n (j + Suc i)"
    have id: "R - Rs \<union> (Rw - Rs \<union> E) = R \<union> Rw - Rs \<union> E" by auto
    show ?thesis
      by (rule exI[of _ "Suc i"], unfold ichain_alternative, rule exI[of _ ?g], rule exI[of _ ?n], intro conjI, 
        insert P, simp, 
        unfold id, insert R steps, simp, 
        insert nf, simp,
        insert nfs, simp,        
        insert inf, simp)
  qed
qed

lemma ichain_split: assumes chain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and nchain: "\<not> ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs) s t \<sigma>"
  shows "\<exists> i. ichain (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs) (shift s i) (shift t i) (shift \<sigma> i)"
  using ichain_split_gen[of nfs m P Pw Q R Rw "{}" s t \<sigma> Ps Rs] assms by auto


lemma ichain_split_P: assumes chain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and nchain: "\<not> ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, {},  R \<union> Rw) s t \<sigma>"
  shows "\<exists> i. ichain (nfs,m,P - Ps, Pw - Ps, Q, R, Rw) (shift s i) (shift t i) (shift \<sigma> i)"
  using ichain_split[OF chain, of Ps "{}"] nchain by auto

lemma ichain_mono_plain: assumes ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and P: "P \<subseteq> P'"
  and Pw: "P \<union> Pw \<subseteq> P' \<union> Pw'"
  and Q: "NF_terms Q \<subseteq> NF_terms Q'"
  and R: "qrstep nfs Q R \<subseteq> qrstep nfs Q' R'"
  and Rw: "qrstep nfs Q (R \<union> Rw) \<subseteq> qrstep nfs Q' (R' \<union> Rw')"
  shows "ichain (nfs,m,P',Pw',Q',R',Rw') s t \<sigma>"
proof -
  from ichain obtain f n
    where main: " (\<forall>i. (s i, t i) \<in> P \<union> Pw) \<and>
        (\<forall>i. f i 0 = t i \<cdot> \<sigma> i \<and>
             f i (n i) = s (Suc i) \<cdot> \<sigma> (Suc i) \<and>
             (\<forall>j<n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q (R \<union> Rw))) \<and>
        (\<forall>i. s i \<cdot> \<sigma> i \<in> NF_terms Q)"
    and nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q"
    and inf: "((INFM i. (s i, t i) \<in> P) \<or> (INFM i. \<exists>j<n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q R))"
    unfolding ichain_alternative by blast
  {
    fix i
    from nfs[of i] have nfs: "NF_subst nfs (s i, t i) (\<sigma> i) Q'"
      using Q unfolding NF_subst_def by auto
  } note nfs = this
  from inf have inf: "((INFM i. (s i, t i) \<in> P') \<or> (INFM i. \<exists>j<n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q' R'))" unfolding INFM_nat using P R by blast
  show ?thesis unfolding ichain_alternative
    by (rule exI[of _ f], rule exI[of _ n], 
      insert main R Rw Q P Pw inf nfs, auto)
qed

lemma ichain_mono: assumes ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and P: "P \<subseteq> P'"
  and Pw: "P \<union> Pw \<subseteq> P' \<union> Pw'"
  and Q: "NF_terms Q \<subseteq> NF_terms Q'"
  and R: "R \<subseteq> R'"
  and Rw: "R \<union> Rw \<subseteq> R' \<union> Rw'"
  shows "ichain (nfs,m,P',Pw',Q',R',Rw') s t \<sigma>"
  by (rule ichain_mono_plain[OF ichain P Pw Q qrstep_mono[OF R Q] qrstep_mono[OF Rw Q]])

lemma SN_rel_ichain:
  assumes SN: "SN_rel (qrstep nfs Q (P \<union> R)) (qrstep nfs Q (Pw \<union> Rw))" (is "SN_rel ?PR ?PRw")
  shows "\<not> ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
proof
  assume chain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  let ?NS = "?PR \<union> ?PRw"
  obtain NS where NS: "?NS = NS" by auto
  let ?S = "?NS\<^sup>* O ?PR O ?NS\<^sup>*"
  from SN_imp_SN_trancl[OF SN[unfolded SN_rel_on_def], unfolded relto_trancl_conv]
    have SN: "SN ?S" .
  let ?s = "\<lambda> i. s i \<cdot> \<sigma> i"
  let ?t = "\<lambda> i. t i \<cdot> \<sigma> i"
  let ?st = "\<lambda> i. (?s i,?t i)"
  let ?ss = "\<lambda> i. ?s (Suc i)"
  from chain have "\<And> i. ?s i \<in> NF_terms Q" by auto
  from NF_imp_subt_NF[OF this] have NF: "\<And> i. \<forall> u \<lhd> ?s i. u \<in> NF_terms Q" .
  from chain have nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" by auto
  {
    fix i
    assume P: "(s i,t i) \<in> P"
    then have st: "(s i, t i) \<in> P \<union> R" by auto
    have "?st i \<in> ?PR" unfolding qrstep_rule_conv[where R = "P \<union> R"]      
      by (rule bexI[OF _ st], rule qrstepI[of "s i" "\<sigma> i" _ "t i" _ _ Hole], insert NF[of i] nfs[of i], auto)
  } note P = this
  {
    fix i
    from chain have st: "(s i, t i) \<in> (P \<union> R) \<union> (Pw \<union> Rw)" by auto
    have "?st i \<in> ?NS" unfolding qrstep_union[symmetric] qrstep_rule_conv[where R = "P \<union> R \<union> (Pw \<union> Rw)"]      
      by (rule bexI[OF _ st], rule qrstepI[of "s i" "\<sigma> i" _ "t i" _ _ Hole], insert NF[of i] nfs[of i], auto)
  } note Pw = this
  note subset =  rtrancl_mono[OF qrstep_mono[of "R \<union> Rw" "P \<union> R \<union> (Pw \<union> Rw)" Q Q]]
  {
    fix i
    from chain have "(?t i, ?ss i) \<in> (qrstep nfs Q (R \<union> Rw))\<^sup>*" by auto
    then have "(?t i, ?ss i) \<in> ?NS\<^sup>*" unfolding qrstep_union[symmetric] using subset by auto
    with Pw[of i] have "(?t i, ?ss i) \<in> ?NS\<^sup>*" and "(?s i, ?ss i) \<in> ?NS\<^sup>*" unfolding NS by auto
  } note steps = this
  then have asteps: "\<forall> i. (?s i, ?ss i) \<in> ?NS\<^sup>* \<union> ?S" by auto
  from SN have SN: "SN_on ?S {?s 0}" unfolding SN_on_def by auto
  have compat: "?NS\<^sup>* O ?S \<subseteq> ?S" unfolding qrstep_union by regexp
  from non_strict_ending[OF asteps, OF compat SN]
  obtain i where i: "\<And> j. i \<le> j \<Longrightarrow> (?s j, ?ss j) \<notin> ?S" by auto
  let ?QNS = "qrstep nfs Q (R \<union> Rw)"
  let ?QS = "?QNS\<^sup>* O qrstep nfs Q R O ?QNS\<^sup>*"
  from chain have inf: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. (?t i, ?ss i) \<in> ?QS)" by auto
  from this[unfolded INFM_disj_distrib[symmetric],unfolded INFM_nat, THEN spec[of _ i]]
  obtain j where j: "j > i" and S: "(s j, t j) \<in> P \<or> (?t j, ?ss j) \<in> ?QS" by auto
  from j have j: "j \<ge> i" by auto
  from S show False
  proof
    assume "(s j, t j) \<in> P"
    from P[OF this] steps[of j] have S: "(?s j, ?ss j) \<in> qrstep nfs Q (P \<union> R) O ?NS\<^sup>*" by auto
    have "qrstep nfs Q (P \<union> R) O ?NS\<^sup>* \<subseteq> ?S" unfolding NS by regexp
    with S have "(?s j, ?ss j) \<in> ?S" by auto
    with i[OF j] show False unfolding NS ..
  next
    assume "(?t j, ?ss j) \<in> ?QS"
    then obtain u v where tu: "(?t j, u) \<in> ?QNS\<^sup>*" and uv: "(u,v) \<in> qrstep nfs Q R" and vs: "(v,?ss j) \<in> ?QNS\<^sup>*" by auto
    from Pw[of j] have one: "(?s j, ?t j) \<in> ?NS" by auto
    from tu vs subset have two: "(?t j, u) \<in> ?NS\<^sup>*" and four: "(v, ?ss j) \<in> ?NS\<^sup>*" unfolding qrstep_union by auto
    from qrstep_mono[of R "P \<union> R" Q Q] uv have three: "(u,v) \<in> qrstep nfs Q (P \<union> R)" by auto
    from one two three four have step: "(?s j, ?ss j) \<in> ?NS O ?NS\<^sup>* O qrstep nfs Q (P \<union> R) O ?NS\<^sup>*" (is "_ \<in> ?rel") unfolding NS by auto
    have "?rel \<subseteq> ?S" unfolding NS by regexp
    from set_mp[OF this step] i[OF j]
    show False by simp
  qed
qed

  
declare ichain.simps[simp del]

lemma min_ichain_split: assumes chain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and nchain: "\<not> min_ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs) s t \<sigma>"
  shows "\<exists> i. min_ichain (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs) (shift s i) (shift t i) (shift \<sigma> i)"
proof -
  have Rw: "R \<union> Rw = (Rs \<inter> (R \<union> Rw)) \<union> (R \<union> Rw - Rs)" by auto
  have nchain: "\<not> ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs) s t \<sigma>"
  proof
    assume ichain: "ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs) s t \<sigma>"
    then have "min_ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs) s t \<sigma>"
      using chain
      by (simp add: Rw[symmetric])
    with nchain show False ..
  qed
  from chain have ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>" by auto
  from ichain_split[OF ichain nchain] obtain i
    where ichain: "ichain (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs) (shift s i) (shift t i) (shift \<sigma> i)" ..
  have "min_ichain (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs) (shift s i) (shift t i) (shift \<sigma> i)" 
    by (rule min_ichainI[OF _ _ ichain, of R Rw], insert chain, auto)
  then show ?thesis ..
qed

lemma min_ichain_split_sig: assumes chain: "min_ichain_sig (nfs,m,P,Pw,Q,R,Rw) F s t \<sigma>"
  and nchain: "\<not> min_ichain_sig (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs) F s t \<sigma>"
  shows "\<exists> i. min_ichain_sig (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs) F (shift s i) (shift t i) (shift \<sigma> i)"
proof -
  from chain have chain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>" and sig: "funas_ichain s t \<sigma> \<subseteq> F" by auto
  from nchain sig have "\<not> min_ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs) s t \<sigma>" by auto
  from min_ichain_split[OF chain this] funas_ichain_shift[of s _ t \<sigma>] sig show ?thesis by auto
qed

lemma min_ichain_split_P: assumes chain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and nchain: "\<not> min_ichain (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, {},  R \<union> Rw) s t \<sigma>"
  shows "\<exists> i. min_ichain (nfs,m,P - Ps, Pw - Ps, Q, R, Rw) (shift s i) (shift t i) (shift \<sigma> i)"
  using min_ichain_split[OF chain, of Ps "{}"] nchain by auto

lemma min_ichain_mono_plain: assumes chain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and P: "P \<subseteq> P'"
  and Pw: "P \<union> Pw \<subseteq> P' \<union> Pw'"
  and Q: "NF_terms Q \<subseteq> NF_terms Q'"
  and R: "qrstep nfs Q R \<subseteq> qrstep nfs Q' R'"
  and Rw: "qrstep nfs Q (R \<union> Rw) = qrstep nfs Q' (R' \<union> Rw')"
  shows "min_ichain (nfs,m,P',Pw',Q',R',Rw') s t \<sigma>"
proof -
  from chain have ichain: "ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
    by simp
  have "ichain (nfs,m,P',Pw',Q',R',Rw') s t \<sigma>" 
    by (rule ichain_mono_plain[OF ichain P Pw Q R], insert Rw, auto)
  with chain Rw show ?thesis by (auto simp: minimal_cond_def)
qed

lemma min_ichain_mono: assumes chain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and P: "P \<subseteq> P'"
  and Pw: "P \<union> Pw \<subseteq> P' \<union> Pw'"
  and Q: "NF_terms Q = NF_terms Q'"
  and R: "R \<subseteq> R'"
  and Rw: "R \<union> Rw = R' \<union> Rw'"
  shows "min_ichain (nfs,m,P',Pw',Q',R',Rw') s t \<sigma>"
proof -
  from Q have Q': "NF_terms Q \<subseteq> NF_terms Q'" and Q'': "NF_terms Q' \<subseteq> NF_terms Q" by auto
  show ?thesis 
   by (rule min_ichain_mono_plain[OF chain P Pw Q' qrstep_mono[OF R Q']], unfold Rw, 
      insert qrstep_mono[OF subset_refl Q', of _ "R' \<union> Rw'"] qrstep_mono[OF subset_refl Q'', of nfs "R' \<union> Rw'"], auto)
qed

lemma Infm_double_shift: "(INFM i. P (shift f n i) (shift g n i)) = 
  (INFM i. P (f i) (g i))" using Infm_shift[of "\<lambda> (fi,gi). P fi gi" "\<lambda> i. (f i, g i)" n]
  unfolding split shift.simps .

lemma Infm_triple_shift: "(INFM i. P (shift f n (Suc i)) (shift h n (Suc i)) (shift g n i) (shift h n i)) = 
  (INFM i. P (f (Suc i)) (h (Suc i)) (g i) (h i))" 
  using Infm_shift[of "\<lambda> (fsi,hsi,gi,hi). P fsi hsi gi hi" "\<lambda> i. (f (Suc i), h (Suc i), g i, h i)" n]
  unfolding split shift.simps by simp

lemma ichain_shift_merge: assumes ic: "ichain (nfs,m,Pb,{},Q,R,Rw) (shift s i) (shift t i) (shift \<sigma> i)"
  and mc: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows "min_ichain (nfs,m,P \<inter> Pb, Pw \<inter> Pb, Q,R,Rw) (shift s i) (shift t i) (shift \<sigma> i)"
  using assms unfolding min_ichain.simps ichain.simps
  unfolding Infm_double_shift[of "\<lambda> s t. (s,t) \<in> P" s i t for P, symmetric]
  unfolding Infm_triple_shift[of "\<lambda> s \<sigma> t \<tau>. (t \<cdot> \<tau>, s \<cdot> \<sigma>) \<in> P" s i \<sigma> t for P, symmetric]
  by (auto simp: minimal_cond_def)
  

definition finite_dpp :: "('f,'v)dpp \<Rightarrow> bool" where "finite_dpp DPP = (\<not>(\<exists>s t \<sigma>. min_ichain DPP s t \<sigma>))"

lemma finite_dpp_split: 
  assumes fin1: "finite_dpp (nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, Q, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs)" (is "finite_dpp ?D1")
  and fin2: "finite_dpp (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs)" (is "finite_dpp ?D2")
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)" (is "finite_dpp ?D")
  unfolding finite_dpp_def 
proof
  assume "\<exists> s t \<sigma>. min_ichain ?D s t \<sigma>"
  then obtain s t \<sigma> where min: "min_ichain ?D s t \<sigma>" by blast
  from fin1[unfolded finite_dpp_def] have "\<not> min_ichain ?D1 s t \<sigma>" by blast
  from min_ichain_split[OF min this]
  show False using fin2[unfolded finite_dpp_def] by blast
qed

lemma finite_dpp_mono_plain: assumes finite: "finite_dpp (nfs,m,P',Pw',Q,R',Rw')"
  and P: "rqrstep nfs Q P \<subseteq> rqrstep nfs Q P'"
  and Pw: "rqrstep nfs Q (P \<union> Pw) \<subseteq> rqrstep nfs Q (P' \<union> Pw')"
  and R: "qrstep nfs Q R \<subseteq> qrstep nfs Q R'"
  and Rw: "qrstep nfs Q (R \<union> Rw) = qrstep nfs Q (R' \<union> Rw')"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
  unfolding finite_dpp_def
proof (clarify)
  fix s t \<sigma>
  assume mi: "min_ichain (nfs,m,P, Pw, Q, R, Rw) s t \<sigma>"
  then have "ichain (nfs,m,P, Pw, Q, R, Rw) s t \<sigma>"
    by simp
  then obtain f n
    where main: " (\<forall>i. (s i, t i) \<in> P \<union> Pw) \<and>
        (\<forall>i. f i 0 = t i \<cdot> \<sigma> i \<and>
             f i (n i) = s (Suc i) \<cdot> \<sigma> (Suc i) \<and>
             (\<forall>j<n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q (R \<union> Rw)))"
        and NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NF_terms Q"
        and nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q"
    and inf: "((INFM i. (s i, t i) \<in> P) \<or> (INFM i. \<exists>j<n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q R))"
    unfolding ichain_alternative by blast
  let ?prop = "\<lambda> i s' t' \<sigma>'. (s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i) = (s' \<cdot> \<sigma>', t' \<cdot> \<sigma>') \<and>  NF_subst nfs (s',t') \<sigma>' Q \<and> (s', t') \<in> P' \<union> Pw' \<and> ((s i, t i) \<in> P \<longrightarrow> (s', t') \<in> P')"
  {
    fix i
    from main have "(s i,t i) \<in> P \<union> Pw" by auto
    from rqrstepI[OF NF_imp_subt_NF[OF NF] this refl refl nfs]
    have "(s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i) \<in> rqrstep nfs Q (P \<union> Pw)" by auto
    with Pw have "(s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i) \<in> rqrstep nfs Q (P' \<union> Pw')" by auto
    note one = this[unfolded rqrstep_def]
    {
      assume "(s i, t i) \<in> P"
      from rqrstepI[OF NF_imp_subt_NF[OF NF] this refl refl nfs]
      have "(s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i) \<in> rqrstep nfs Q P" by auto
      with P have "(s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i) \<in> rqrstep nfs Q P'" by auto
      note one = this[unfolded rqrstep_def]
    }
    with one have "\<exists> s' t' \<sigma>'. ?prop i s' t' \<sigma>'" by blast
  } 
  from choice[OF allI[OF this]] obtain s' where "\<forall> i. (\<exists> t' \<sigma>'. ?prop i (s' i) t' \<sigma>')" ..
  from choice[OF this] obtain t' where "\<forall> i. (\<exists> \<sigma>'. ?prop i (s' i) (t' i) \<sigma>')" ..
  from choice[OF this] obtain \<sigma>' where switch: "\<And> i. ?prop i (s' i) (t' i) (\<sigma>' i)" by blast
  from switch have si: "\<And> i. s i \<cdot> \<sigma> i = s' i \<cdot> \<sigma>' i" by auto
  from switch have ti: "\<And> i. t i \<cdot> \<sigma> i = t' i \<cdot> \<sigma>' i" by auto
  from switch have Pw: "\<forall> i. (s' i, t' i) \<in> P' \<union> Pw'" by auto
  from switch have P: "\<And> i. (s i, t i) \<in> P \<Longrightarrow> (s' i, t' i) \<in> P'" by auto
  from switch have nfs: "\<And> i. NF_subst nfs (s' i, t' i) (\<sigma>' i) Q" by blast
  note main = main[unfolded si ti Rw]
  note NF = NF[unfolded si ti]
  from inf P R have inf: "(INFM i. (s' i, t' i) \<in> P') \<or> (INFM i. \<exists> j < n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q R')" unfolding INFM_nat by blast
  have ic: "ichain (nfs,m,P',Pw',Q,R',Rw') s' t' \<sigma>'"
    unfolding ichain_alternative
    by (rule exI[of _ f], rule exI[of _ n], insert Pw main NF nfs inf, auto)
  with mi have "min_ichain (nfs,m,P',Pw',Q,R',Rw') s' t' \<sigma>'"
    by (simp add: minimal_cond_def ti Rw)
  with finite show False unfolding finite_dpp_def by auto
qed

lemma finite_dpp_mono:
  assumes finite: "finite_dpp (nfs, m, P', Pw', Q, R', Rw')"
    and P: "P \<subseteq> P'"
    and Pw: "P \<union> Pw \<subseteq> P' \<union> Pw'"
    and Q: "NF_terms Q = NF_terms Q'"
    and R: "R \<subseteq> R'"
    and Rw: "R \<union> Rw = R' \<union> Rw'"
  shows "finite_dpp (nfs, m, P, Pw, Q', R, Rw)"
using min_ichain_mono[OF _ P Pw Q[symmetric] R Rw] finite
unfolding finite_dpp_def by blast

lemma SN_rel_ext_imp_finite_dpp:
  assumes "SN_rel_ext 
  (rqrstep nfs Q P \<inter> {(s,t) . s \<in> NF_terms Q}) 
  (rqrstep nfs Q Pw \<inter> {(s,t) . s \<in> NF_terms Q}) 
  (qrstep nfs Q R) 
  (qrstep nfs Q Rw) 
  (\<lambda>x. m \<longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {x})" (is "SN_rel_ext ?P ?Pw ?R ?Rw ?M")
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)" (is "finite_dpp ?dpp")
  unfolding finite_dpp_def
proof (clarify)
  fix s t \<sigma>
  assume chain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  then have "ichain ?dpp s t \<sigma>" by auto
  from this[unfolded ichain_alternative]
  obtain f n where PPw: "\<And> i. (s i, t i) \<in> P \<union> Pw"
    and t: "\<And> i. f i 0 = t i \<cdot> \<sigma> i" 
    and s: "\<And> i. f i (n i) = s (Suc i) \<cdot> \<sigma> (Suc i)"
    and RRw: "\<And> i. (\<forall> j < n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q (R \<union> Rw))"
    and NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NF_terms Q"
    and nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q"
    and inf: "(INFM i. (s i, t i ) \<in> P) \<or> (INFM i. \<exists> j < n i. (f i j, f i (Suc j)) \<in> qrstep nfs Q R)" (is "?one \<or> ?two") by blast
  note NF_arg = NF_imp_subt_NF[OF NF]
  from chain have min: "\<And> i. m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {t i \<cdot> \<sigma> i}" by (auto simp: minimal_cond_def)
  let ?m = m
  obtain m where m: "\<And> i. m i = Suc (n i)" by auto
  let ?c = "inf_concat_simple m"
  let ?g = "\<lambda> k. case ?c k of (i,j) \<Rightarrow> f i j"
  let ?t = "\<lambda> i j. if (j = n i) then (if (s (Suc i), t (Suc i)) \<in> P then top_s else top_ns) else (if (f i j, f i (Suc j)) \<in> qrstep nfs Q R then normal_s else normal_ns)"
  let ?ty = "\<lambda> k. case ?c k of (i,j) \<Rightarrow> ?t i j"
  {
    fix k i j
    assume ck: "?c k = (i,j)"
    then have "j < m i" 
    proof (cases k)
      case 0 
      with ck show ?thesis unfolding m by auto
    next
      case (Suc k')
      obtain i' j' where ck': "?c k' = (i',j')" by (cases "?c k'", auto)        
      from ck[unfolded Suc] ck' show ?thesis
        by (cases "Suc j' < m i'", auto simp: m)
    qed
  } note ck_mi = this 
  let ?rel = "SN_rel_ext_step ?P ?Pw ?R ?Rw"
  note rqrstep = rqrstepI[OF NF_arg _ refl refl nfs]
  have "\<not> SN_rel_ext ?P ?Pw ?R ?Rw ?M"
    unfolding 
      SN_rel_ext_def
      simp_thms
  proof (rule exI[of _ ?g], rule exI[of _ ?ty], intro conjI allI)
    fix k
    obtain i j where ck: "?c k = (i,j)" by (cases "?c k", auto)
    show "(?g k, ?g (Suc k)) \<in> ?rel (?ty k)"
    proof (cases "Suc j < m i")
      case False
      from ck_mi[OF ck] False have j: "j = n i" unfolding m by auto
      from False ck have csk: "?c (Suc k) = (Suc i, 0)" by auto
      show ?thesis unfolding ck csk split t j s
        by (cases "(s (Suc i), t (Suc i)) \<in> P", insert PPw[of "Suc i"] rqrstep, auto simp: NF)
    next
      case True
      then have j: "(j = n i) = False" and jn: "j < n i" unfolding m by auto
      from True ck have csk: "?c (Suc k) = (i, Suc j)" by auto
      show ?thesis unfolding ck csk split j using RRw[THEN spec, THEN mp[OF _ jn]]
        by (auto simp: qrstep_union)
    qed
  next
    fix k
    obtain i j where ck: "?c k = (i,j)" by (cases "?c k", auto)
    from ck_mi[OF ck] have j: "j \<le> n i" unfolding m by simp
    show "?M (?g k)" unfolding ck split
      using j 
    proof (induct j)
      case 0
      show ?case unfolding t using min[of i] by simp
    next
      case (Suc j)
      then have j: "j < n i" and SN: "?m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {f i j}" by auto
      from step_preserves_SN_on[OF RRw[THEN spec, THEN mp[OF _ j]] SN]
      show ?case by auto
    qed
  next
    show "INFM k. ?ty k \<in> {top_s,top_ns}"
      unfolding INFM_nat_le
    proof (intro allI)
      fix k :: nat
      obtain i j where ck: "?c k = (i,j)" by (cases "?c k", auto)
      let ?a = "m i - Suc j"
      let ?j = "j + ?a"
      from ck_mi[OF ck] have j: "j < m i" by auto
      then have "?j < m i" by auto
      from inf_concat_simple_add[OF ck, OF this] have "?c (k + ?a) = (i,?j)" .
      also have "... = (i,n i)" using j unfolding m by auto
      finally have c: "?c (k + ?a) = (i, n i)" by auto
      show "\<exists> k' \<ge> k. ?ty k' \<in> {top_s,top_ns}"
        by (rule exI[of _ "k + ?a"], unfold c, auto)
    qed
  next
    show "INFM k. ?ty k \<in> {top_s,normal_s}"
      unfolding INFM_nat_le
    proof (intro allI)
      fix k
      obtain i j where ck: "?c k = (i,j)" by (cases "?c k", auto)      
      from inf
      show "\<exists> k' \<ge> k. ?ty k' \<in> {top_s,normal_s}"
      proof
        assume ?one
        then obtain i' where i': "i' > Suc i" and P: "(s i', t i') \<in> P"
          unfolding INFM_nat by auto
        then obtain i' where i': "i' > i" and P: "(s (Suc i'), t (Suc i')) \<in> P" by (cases i', auto)
        have "n i' < m i'" unfolding m by auto
        from inf_concat_simple_surj[where f = m, OF this]
        obtain k' where ck': "?c k' = (i',n i')" by auto
        {
          assume "k' \<le> k"
          from inf_concat_simple_mono[OF this, of m] i' have False unfolding ck ck' by simp
        }
        then have k': "k' \<ge> k" by presburger
        show ?thesis
          by (rule exI[of _ k'], unfold ck', auto simp: P k')
      next
        assume ?two
        then obtain i' j' where i': "i' > Suc i" and j': "j' < n i'" and R: "(f i' j', f i' (Suc j')) \<in> qrstep nfs Q R"
          unfolding INFM_nat by blast
        from j' have jm: "j' < m i'" and jn: "(j' = n i') = False" unfolding m by auto
        from inf_concat_simple_surj[where f = m, OF jm]
        obtain k' where ck': "?c k' = (i',j')" by auto
        {
          assume "k' \<le> k"
          from inf_concat_simple_mono[OF this, of m] i' have False unfolding ck ck' by simp
        }
        then have k': "k' \<ge> k" by presburger
        show ?thesis
          by (rule exI[of _ k'], unfold ck' jn split, auto simp: R k')
      qed
    qed
  qed
  with assms
  show False by simp
qed


lemma finite_dpp_imp_SN_rel_ext:
  assumes "finite_dpp (nfs,m,P,Pw,Q,R,Rw)" (is "finite_dpp ?dpp")
  shows "SN_rel_ext 
  (rqrstep nfs Q P \<inter> {(s,t) . s \<in> NF_terms Q}) 
  (rqrstep nfs Q Pw \<inter> {(s,t) . s \<in> NF_terms Q}) 
  (qrstep nfs Q R) 
  (qrstep nfs Q Rw) 
  (\<lambda>x. m \<longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {x})" (is "SN_rel_ext ?P ?Pw ?R ?Rw ?M")
proof (rule ccontr)
  let ?rel = "SN_rel_ext_step ?P ?Pw ?R ?Rw"
  assume "\<not> ?thesis"
  from this[unfolded SN_rel_ext_def] obtain f ty where
    steps: "\<And> i. (f i, f (Suc i)) \<in> ?rel (ty i)"
   and min: "\<And> i. ?M (f i)"
   and inf1: "INFM i. ty i \<in> {top_s,top_ns}"
   and inf2: "INFM i. ty i \<in> {top_s,normal_s}" by blast
  obtain p where p: "\<And> i. p i = (ty i \<in> {top_s,top_ns})" by auto
  interpret infinitely_many p
    by (unfold_locales, insert inf1, unfold INFM_nat_le p)
  let ?ind = "infinitely_many.index p"
  let ?g = "\<lambda> i. f (?ind i)"
  let ?h = "\<lambda> i. f (Suc (?ind i))"
  let ?prop = "\<lambda> s t \<sigma> i. (s,t) \<in> P \<union> Pw \<and> ?g i = s \<cdot> \<sigma> \<and> ?h i = t \<cdot> \<sigma> \<and> s \<cdot> \<sigma> \<in> NF_terms Q \<and> NF_subst nfs (s,t) \<sigma> Q \<and> (ty (?ind i) = top_s \<longrightarrow> (s,t) \<in> P)" 
  {
    fix i
    have "ty (?ind i) \<in> {top_s,top_ns}"
      using index_p[of i] unfolding p .
    then have one: "(?g i, ?h i) \<in> ?P \<union> ?Pw" and two: "ty (?ind i) = top_s \<Longrightarrow> (?g i, ?h i) \<in> ?P" using steps[of "?ind i"]
      by auto      
    have "\<exists> s t \<sigma>. ?prop s t \<sigma> i"
    proof (cases "ty (?ind i) = top_s")
      case True
      from two[OF True] have "(?g i, ?h i) \<in> rqrstep nfs Q P" by simp
      from rqrstepE[OF this] two[OF True]
      obtain s t \<sigma> where "(s,t) \<in> P" "?g i = s \<cdot> \<sigma>" "?h i = t \<cdot> \<sigma>"  "s \<cdot> \<sigma> \<in> NF_terms Q"
      and "NF_subst nfs (s,t) \<sigma> Q" by auto
      then show ?thesis by blast
    next
      case False
      from one have "(?g i, ?h i) \<in> rqrstep nfs Q (P \<union> Pw)" 
        unfolding rqrstep_def
       by auto
      from rqrstepE[OF this] one 
      obtain s t \<sigma> where "(s,t) \<in> P \<union> Pw" "?g i = s \<cdot> \<sigma>" "?h i = t \<cdot> \<sigma>" "s \<cdot> \<sigma> \<in> NF_terms Q" 
      "NF_subst nfs (s,t) \<sigma> Q" by force
      then show ?thesis using False by blast
    qed
  }
  from choice[OF allI[OF this]] obtain s where "\<forall> i. \<exists> t \<sigma>. ?prop (s i) t \<sigma> i" ..
  from choice[OF this] obtain t where "\<forall> i. \<exists> \<sigma>. ?prop (s i) (t i) \<sigma> i" ..
  from choice[OF this] obtain \<sigma> where st\<sigma>: "\<And> i. ?prop (s i) (t i) (\<sigma> i) i" by auto
  from st\<sigma> have PPw: "\<And> i. (s i, t i) \<in> P \<union> Pw" by auto
  from st\<sigma> have NF: "\<And> i. (s i \<cdot> \<sigma> i) \<in> NF_terms Q" by auto
  from st\<sigma> have s: "\<And> i. s i \<cdot> \<sigma> i = ?g i" by auto
  from st\<sigma> have t: "\<And> i. t i \<cdot> \<sigma> i = ?h i" by auto
  from st\<sigma> have P: "\<And> i. ty (?ind i) = top_s \<Longrightarrow> (s i, t i) \<in> P" by auto
  {
    fix i
    from st\<sigma>[of i] have "?M (t i \<cdot> \<sigma> i)" using min[of "Suc (?ind i)"] by auto
  } note min = this
  let ?f = "\<lambda> i j. f (Suc (?ind i) + j)"
  let ?n = "\<lambda> i. ?ind (Suc i) - Suc (?ind i)"
  let ?RRw = "qrstep nfs Q (R \<union> Rw)"
  have "ichain ?dpp s t \<sigma>" 
    unfolding ichain_alternative
  proof (rule exI[of _ ?f], rule exI[of _ ?n], intro conjI allI impI, rule PPw)
    fix i
    show "?f i 0 = t i \<cdot> \<sigma> i" unfolding t by simp
  next
    fix i
    show "?f i (?n i) = s (Suc i) \<cdot> \<sigma> (Suc i)" unfolding s
      using index_ordered[of i] by auto
  next
    fix i
    show "s i \<cdot> \<sigma> i \<in> NF_terms Q" by (rule NF)
  next
    fix i j
    let ?k = "Suc (?ind i) + j"
    assume "j < ?n i"
    with index_not_p_between[of i ?k]
    have "\<not> p ?k" by auto
    then have "ty ?k \<in> {normal_s,normal_ns}"
       unfolding p apply (cases "ty ?k", auto)
       using SN_rel_ext_type.exhaust apply blast
       using SN_rel_ext_type.exhaust apply blast
       using SN_rel_ext_type.exhaust apply blast
       using SN_rel_ext_type.exhaust by blast
    with steps[of ?k] show "(?f i j, ?f i (Suc j)) \<in> ?RRw" unfolding qrstep_union
      by auto
  next
    let ?L = "\<lambda> i. (s i, t i) \<in> P"
    let ?R = "\<lambda> i. \<exists> j < ?n i. (?f i j, ?f i (Suc j)) \<in> ?R"
    show "(INFM i. ?L i) \<or> (INFM i. ?R i)" 
      unfolding INFM_disj_distrib[symmetric] 
      unfolding INFM_nat_le
    proof (intro allI)
      fix i
      from inf2[unfolded INFM_nat_le]
      obtain k where k: "k \<ge> ?ind i" and ty: "ty k \<in> {top_s,normal_s}" by auto
      from index_surj[OF k]
      obtain j j' where kj: "k = ?ind j + j'" and j': "?ind j + j' < ?ind (Suc j)" by auto
      note ty = ty[unfolded kj]
      from k[unfolded kj] j' have lt: "?ind i < ?ind (Suc j)" by auto
      {
        assume "j < i"
        then have "Suc j \<le> i" by auto
        from index_ordered_le[OF this] lt have False by auto
      }
      then have j: "i \<le> j" by presburger
      show "\<exists> j \<ge> i. ?L j \<or> ?R j"
      proof (intro exI conjI, rule j)
        show "?L j \<or> ?R j"
        proof (cases j')
          case 0
          from index_p[of j, unfolded p]
            ty[unfolded 0] have "ty (?ind j) = top_s" using index_p p by force
          from P[OF this] show ?thesis by auto
        next
          case (Suc j'')
          from index_not_p_between[of j "?ind j + j'", OF _ j']
          have "ty (?ind j + j') \<notin> {top_s,top_ns}" unfolding p Suc by auto
          with ty have ty: "ty (?ind j + j') = normal_s" by auto
          have j'': "j'' < ?ind (Suc j) - Suc (?ind j)" using j' unfolding Suc by auto
          have "?R j"
            by (rule exI[of _ j''], rule conjI[OF j''],
              insert steps[of "?ind j + j'", unfolded ty], unfold Suc, auto)
          then show ?thesis by auto
        qed
      qed
    qed
  next
    fix i
    show "NF_subst nfs (s i, t i) (\<sigma> i) Q"
     using st\<sigma>[of i] by simp
  qed
  then have "min_ichain ?dpp s t \<sigma>"
    unfolding min_ichain.simps minimal_cond_def using min by auto
  with assms show False
    unfolding finite_dpp_def by auto
qed


(* map each (P,Pw,..) chain to an (P',Pw',...)-chain via function f, where invariant I is established *)
lemma finite_dpp_map:
  fixes P Pw R Rw P' Pw' R' Rw' :: "('f,'v)trs" and Q Q' :: "('f,'v)terms" and nfs nfs' m m'
  defines QR: "QR \<equiv> qrstep nfs Q R"
  defines QRw: "QRw \<equiv> qrstep nfs Q Rw"
  defines QP: "QP \<equiv> rqrstep nfs Q P \<inter> {(s,t). s \<in> NF_terms Q}"
  defines QPw: "QPw \<equiv> rqrstep nfs Q Pw \<inter> {(s,t). s \<in> NF_terms Q}"
  defines QR': "QR' \<equiv> qrstep nfs' Q' R'"
  defines QRw': "QRw' \<equiv> qrstep nfs' Q' Rw'"
  defines QP': "QP' \<equiv> rqrstep nfs' Q' P' \<inter> {(s,t). s \<in> NF_terms Q'}"
  defines QPw': "QPw' \<equiv> rqrstep nfs' Q' Pw' \<inter> {(s,t). s \<in> NF_terms Q'}"
  defines M: "M \<equiv> \<lambda>x. m \<longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {x}"
  defines M': "M' \<equiv> \<lambda>x. m' \<longrightarrow> SN_on (qrstep nfs' Q' (R' \<union> Rw')) {x}"
  defines Ms': "Ms' \<equiv> {(s,t). M' t}"
  defines A: "A \<equiv> (QP' \<union> QPw' \<union> QR' \<union> QRw') \<inter> Ms'"
  assumes SN: "finite_dpp (nfs',m',P',Pw',Q',R',Rw')"
  and P: "\<And> s t. M s \<Longrightarrow> M t \<Longrightarrow> (s,t) \<in> QP \<Longrightarrow> (f s, f t) \<in> (A\<^sup>* O (QP' \<inter> Ms') O A\<^sup>*) \<and> I t"
  and Pw: "\<And> s t. M s \<Longrightarrow> M t \<Longrightarrow> (s,t) \<in> QPw \<Longrightarrow> (f s, f t) \<in> (A\<^sup>* O ((QP' \<union> QPw') \<inter> Ms') O A\<^sup>*) \<and> I t"
  and R: "\<And> s t. I s \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> (s,t) \<in> QR \<Longrightarrow> (f s, f t) \<in> (A\<^sup>* O ((QP' \<union> QR') \<inter> Ms') O A\<^sup>*) \<and> I t"
  and Rw: "\<And> s t. I s \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> (s,t) \<in> QRw \<Longrightarrow> (f s, f t) \<in> A\<^sup>* \<and> I t"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
proof -
  from finite_dpp_imp_SN_rel_ext[OF SN]
  have SN: "SN_rel_ext QP' QPw' QR' QRw' M'"
    unfolding QP' QPw' QR' QRw' M' .
  have SN: "SN_rel_ext QP QPw QR QRw M"
    by (rule SN_rel_ext_map[OF  SN, unfolded Ms'[symmetric] A[symmetric], OF P Pw R Rw], auto)
  show ?thesis
    by (rule SN_rel_ext_imp_finite_dpp[OF SN[unfolded QP QPw QR QRw M]])
qed


(* map each (P,Pw,..) chain to an (P',Pw',...)-chain via function f, where invariant I is established *)
lemma finite_dpp_map_min:
  fixes P Pw R Rw P' Pw' R' Rw' :: "('f,'v)trs" and Q Q' :: "('f,'v)terms" and m m' nfs nfs'
  defines QR: "QR \<equiv> qrstep nfs Q R"
  defines QRw: "QRw \<equiv> qrstep nfs Q Rw"
  defines QP: "QP \<equiv> rqrstep nfs Q P \<inter> {(s,t). s \<in> NF_terms Q}"
  defines QPw: "QPw \<equiv> rqrstep nfs Q Pw \<inter> {(s,t). s \<in> NF_terms Q}"
  defines QR': "QR' \<equiv> qrstep nfs' Q' R'"
  defines QRw': "QRw' \<equiv> qrstep nfs' Q' Rw'"
  defines QP': "QP' \<equiv> rqrstep nfs' Q' P' \<inter> {(s,t). s \<in> NF_terms Q'}"
  defines QPw': "QPw' \<equiv> rqrstep nfs' Q' Pw' \<inter> {(s,t). s \<in> NF_terms Q'}"
  defines M: "M \<equiv> \<lambda>x. m \<longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {x}"
  defines M': "M' \<equiv> \<lambda>x. m' \<longrightarrow> SN_on (qrstep nfs' Q' (R' \<union> Rw')) {x}"
  defines Ms': "Ms' \<equiv> {(s,t). M' t}"
  defines A: "A \<equiv> QP' \<inter> Ms' \<union> QPw' \<inter> Ms' \<union> QR' \<union> QRw'"
  assumes SN: "finite_dpp (nfs',m',P',Pw',Q',R',Rw')"
  and MM': "\<And> t. M t \<Longrightarrow> M' (f t)"
  and P: "\<And> s t. M s \<Longrightarrow> M t \<Longrightarrow> M' (f s) \<Longrightarrow> M' (f t) \<Longrightarrow> (s,t) \<in> QP \<Longrightarrow> (f s, f t) \<in> (A\<^sup>* O (QP' \<inter> Ms') O A\<^sup>*) \<and> I t"
  and Pw: "\<And> s t. M s \<Longrightarrow> M t \<Longrightarrow> M' (f s) \<Longrightarrow> M' (f t) \<Longrightarrow> (s,t) \<in> QPw \<Longrightarrow> (f s, f t) \<in> (A\<^sup>* O (QP' \<inter> Ms' \<union> QPw' \<inter> Ms') O A\<^sup>*) \<and> I t"
  and R: "\<And> s t. I s \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> M' (f s) \<Longrightarrow> M' (f t) \<Longrightarrow> (s,t) \<in> QR \<Longrightarrow> (f s, f t) \<in> (A\<^sup>* O (QP' \<inter> Ms' \<union> QR') O A\<^sup>*) \<and> I t"
  and Rw: "\<And> s t. I s \<Longrightarrow> M s \<Longrightarrow> M t \<Longrightarrow> M' (f s) \<Longrightarrow> M' (f t) \<Longrightarrow> (s,t) \<in> QRw \<Longrightarrow> (f s, f t) \<in> A\<^sup>* \<and> I t"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
proof -
  from finite_dpp_imp_SN_rel_ext[OF SN]
  have SN: "SN_rel_ext QP' QPw' QR' QRw' M'"
    unfolding QP' QPw' QR' QRw' M' .
  {
    fix s t 
    assume a: "M' s" and b: "(s,t) \<in> QR' \<union> QRw'"
    from b a have "M' t" unfolding M' QR' QRw' qrstep_union
      by (intro impI step_preserves_SN_on[of s t], auto)
  } note min = this  
  have SN: "SN_rel_ext QP QPw QR QRw M"
    by (rule SN_rel_ext_map_min[OF SN, unfolded Ms'[symmetric] A[symmetric], OF MM' min P Pw R Rw], auto)
  show ?thesis
    by (rule SN_rel_ext_imp_finite_dpp[OF SN[unfolded QP QPw QR QRw M]])
qed

  
theorem finite_dpp_iff_SN_rel:
  "finite_dpp (nfs,m,P,{},{},{},R) = SN_rel 
  ((subst.closure P \<inter> {(s,t) | s t. m \<longrightarrow> SN_on (rstep R) {t}})) (rstep R)" (is "_ = SN_rel ?R ?S")
proof
  assume SN: "SN_rel ?R ?S"
  show "finite_dpp (nfs,m,P,{},{},{},R)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain s t \<sigma> where chain: "min_ichain (nfs,m,P,{},{},{},R) s t \<sigma>" unfolding finite_dpp_def by auto
    obtain f where f: "\<And> i. f i = s i \<cdot> \<sigma> i" by auto
    from chain have "\<And> i. (s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i) \<in> ?R" and "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?S\<^sup>*"  
      by (auto simp: minimal_cond_def ichain.simps)
    then have "\<And> i. (f i,f (Suc i)) \<in> ?S\<^sup>* O ?R O ?S\<^sup>*" unfolding f by auto
    with SN[unfolded SN_rel_on_def]
    show False unfolding SN_defs by blast
  qed
next
  assume finite: "finite_dpp (nfs,m,P,{},{},{},R)"
  show "SN_rel ?R ?S"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain t where steps: "\<And> i. (t i, t (Suc i)) \<in> ?S\<^sup>* O ?R O ?S\<^sup>*"
      unfolding SN_rel_defs SN_defs by auto
    let ?prop = "\<lambda> s u i.  (t i, s) \<in> ?S\<^sup>* \<and> (s,u) \<in> ?R \<and> (u, t (Suc i)) \<in> ?S\<^sup>*"
    have "\<forall> i. \<exists> s u. ?prop s u i"
    proof
      fix i
      from steps[of i] show "\<exists> s u. ?prop s u i" by auto
    qed
    from choice[OF this] obtain s where "\<forall> i. \<exists> u. ?prop (s i) u i" ..
    from choice[OF this] obtain u where p: "\<And> i. ?prop (s i) (u i) i" by auto
    let ?prop2 = "\<lambda> l r \<sigma> i. (l, r) \<in> P \<and> (m \<longrightarrow> SN_on (rstep R) {r \<cdot> \<sigma>}) \<and> r \<cdot> \<sigma> = u i \<and> l \<cdot> \<sigma> = s i"
    have "\<forall> i. \<exists> l r \<sigma>. ?prop2 l r \<sigma> i"
    proof
      fix i
      from p[of i] have "(s i, u i) \<in> subst.closure P" by auto
      then obtain l r \<sigma> where  "s i = l \<cdot> \<sigma> \<and> u i = r \<cdot> \<sigma> \<and> (l,r) \<in> P" by (auto elim: subst.closure.cases)
      with p[of i] have "?prop2 l r \<sigma> i" by auto
      then show "\<exists> l r \<sigma>. ?prop2 l r \<sigma> i" by blast
    qed
    from choice[OF this] obtain l where "\<forall> i. \<exists> r \<sigma> . ?prop2 (l i) r \<sigma> i" ..
    from choice[OF this] obtain r where "\<forall> i. \<exists> \<sigma> . ?prop2 (l i) (r i) \<sigma> i" ..
    from choice[OF this] obtain \<sigma> where p2: "\<And> i. ?prop2 (l i) (r i) (\<sigma> i) i" by auto
    {
      fix i
      from p2[of i] p[of i] p[of "Suc i"] p2[of "Suc i"]
      have "(r i \<cdot> \<sigma> i, l (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?S\<^sup>* " by auto
    }
    with p2 have "min_ichain (nfs,m,P,{},{},{},R) l r \<sigma>" 
      by (auto simp: minimal_cond_def p2 ichain.simps)
    with finite show False unfolding finite_dpp_def by blast
  qed
qed

lemma min_ichain_imp_var_cond: assumes "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  and "lr \<in> R \<union> Rw"
  and m: m
  and nfs: "\<not> nfs"
  shows "is_Fun (fst lr)"
proof(rule ccontr)
  assume n: "\<not> ?thesis"
  let ?R = "R \<union> Rw"
  obtain l r where lr: "lr = (l,r)" by force
  with assms(2) n have  "(l,r) \<in> ?R"
    and "is_Var (fst (l,r))" by auto
  then obtain x where lr: "(Var x,r) \<in> ?R" by (cases l, auto)
  from assms(1) m have "SN_on (qrstep nfs Q (R \<union> Rw)) {t 0 \<cdot> \<sigma> 0}" 
    by (auto simp: minimal_cond_def)
  with left_Var_imp_not_SN_qrstep[OF lr nfs]
  show False ..
qed

lemma finite_under_var_cond:
  assumes var: "(\<And> lr. lr \<in> R \<union> Rw \<Longrightarrow> is_Fun (fst lr)) \<Longrightarrow> finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
  and m: m and nfs: "\<not> nfs"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
proof(rule ccontr)
  assume n: "\<not> ?thesis"
  from n[unfolded finite_dpp_def] obtain s t \<sigma> where 
    chain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>" by auto 
  have ?thesis
    by (rule var, rule min_ichain_imp_var_cond[OF chain _ m nfs])
  with n show False ..
qed

fun
  nr_ichain ::
    "bool \<times> bool \<times> ('f, 'v)trs \<times> ('f,'v)trs \<times> ('f,'v)terms \<times> ('f,'v)trs \<Rightarrow> (nat \<Rightarrow> ('f, 'v) term) \<Rightarrow> (nat \<Rightarrow> ('f, 'v) term) \<Rightarrow>
     (nat \<Rightarrow> ('f, 'v) subst) \<Rightarrow> bool"
where
  "nr_ichain (nfs,m,P, Pw, Q, R) s t \<sigma> = (
    (\<forall>i. (s i \<cdot> \<sigma> i) \<in> NF_terms Q) \<and>
    (\<forall>i. (s i,t i) \<in> P \<union> Pw) \<and> 
    (\<forall>i. NF_subst nfs (s i, t i) (\<sigma> i) Q) \<and>
    (INFM i. (s i,t i) \<in> P) \<and>
    (\<forall>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (nrqrstep nfs Q R)\<^sup>*))"

lemma ichain_imp_nr_ichain: 
  assumes ichain: "ichain (nfs,m,P,Pw,Q,{},R) s t \<sigma>"
  and nvar: "\<forall> (l,r) \<in> R. is_Fun l"
  and nvarP: "\<forall> (s,t) \<in> P \<union> Pw. is_Fun t"
  and ndef: "\<forall> (s,t) \<in> P \<union> Pw. \<not> defined R (the (root t))"
  shows "nr_ichain (nfs,m,P,Pw,Q,R) s t \<sigma>"
proof -
  from ichain[unfolded ichain.simps] have 
    zero: "\<And> i. (s i \<cdot> \<sigma> i) \<in> NF_terms Q" "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q"
    and one: "\<forall>i. (s i,t i) \<in> P \<union> Pw"
    and two: "(INFM i. (s i, t i) \<in> P)"
    and three: "(\<forall>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q R)\<^sup>*)"
    by auto
  {
    fix i
    from three have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q R)\<^sup>*" by auto
    from one nvarP have t: "is_Fun (t i)" by auto
    then have nvart: "is_Fun (t i \<cdot> \<sigma> i)" by auto
    from one ndef have "\<not> defined R (the (root (t i)))" by auto
    with t have "\<not> defined R (the (root (t i \<cdot> \<sigma> i)))" by auto
    from qrsteps_imp_nrqrsteps[OF nvar ndef_applicable_rules[OF this] steps]
    have "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (nrqrstep nfs Q R)\<^sup>*" .
  }
  with zero one two show ?thesis by auto
qed

lemma nr_ichain_mono: assumes ichain: "nr_ichain (nfs,m,P,Pw,Q,R) s t \<sigma>"
  and P: "P \<subseteq> P'"
  and Pw: "P \<union> Pw \<subseteq> P' \<union> Pw'"
  and R: "R \<subseteq> R'"
  shows "nr_ichain (nfs,m,P',Pw',Q,R') s t \<sigma>"
proof -
  from ichain have
    zero: "\<And> i. (s i \<cdot> \<sigma> i) \<in> NF_terms Q" "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q"
    and one: "\<forall>i. (s i,t i) \<in> P \<union> Pw"
    and two: "(INFM i. (s i, t i) \<in> P)"
    and three: "(\<forall>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (nrqrstep nfs Q R)\<^sup>*)"
    by auto
  show ?thesis unfolding nr_ichain.simps 
  proof (intro conjI)
    show "\<forall>i. (s i,t i) \<in> P' \<union> Pw'" using one Pw by auto
  next
    show "(INFM i. (s i, t i) \<in> P')" using two P unfolding INFM_nat_le by auto
  next
    show "(\<forall>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (nrqrstep nfs Q R')\<^sup>*)"
      using rtrancl_mono[OF nrqrstep_mono[OF subset_refl R]] three by auto
  qed (insert zero, auto)
qed

fun
  nr_min_ichain ::
    "bool \<times> bool \<times> ('f, 'v)trs \<times> ('f,'v)trs \<times> ('f,'v)terms \<times> ('f,'v)trs \<Rightarrow> (nat \<Rightarrow> ('f, 'v) term) \<Rightarrow> (nat \<Rightarrow> ('f, 'v) term) \<Rightarrow>
     (nat \<Rightarrow> ('f, 'v) subst) \<Rightarrow> bool"
where
  "nr_min_ichain (nfs,m,P, Pw, Q, R) s t \<sigma> = (nr_ichain (nfs,m,P, Pw, Q, R) s t \<sigma> \<and> (m \<longrightarrow> minimal_cond nfs Q R s t \<sigma>))"

lemma min_ichain_imp_nr_min_ichain: 
  assumes ichain: "min_ichain (nfs,m,P,Pw,Q,{},R) s t \<sigma>"
  and nvarP: "\<forall> (s,t) \<in> P \<union> Pw. is_Fun t"
  and nvarR: "\<forall> (s,t) \<in> R. is_Fun s"
  and ndef: "\<forall> (s,t) \<in> P \<union> Pw. \<not> defined R (the (root t))"
  shows "nr_min_ichain (nfs,m,P,Pw,Q,R) s t \<sigma>"
proof -
  from ichain have "ichain (nfs,m,P,Pw,Q,{},R) s t \<sigma>" by simp   
  from ichain_imp_nr_ichain[OF this nvarR nvarP ndef] 
  have nr: "nr_ichain (nfs,m,P,Pw,Q,R) s t \<sigma>" by auto
  from nr ichain show ?thesis by simp 
qed

lemma nr_min_ichain_mono: assumes ichain: "nr_min_ichain (nfs,m,P,Pw,Q,R) s t \<sigma>"
  and P: "P \<subseteq> P'"
  and Pw: "P \<union> Pw \<subseteq> P' \<union> Pw'"
  shows "nr_min_ichain (nfs,m,P',Pw',Q,R) s t \<sigma>"
proof -
  from ichain have nr: "nr_ichain (nfs,m,P,Pw,Q,R) s t \<sigma>" and min: "m \<Longrightarrow> minimal_cond nfs Q R s t \<sigma>" by auto
  from nr_ichain_mono[OF nr P Pw subset_refl] have ichain': "nr_ichain (nfs,m,P', Pw', Q, R) s t \<sigma>" by auto
  with min show ?thesis by auto 
qed

lemma finite_dpp_rename_vars: assumes fin: "finite_dpp (nfs,m,P',Pw',Q,R,Rw)"
  and P: "\<And> st. st \<in> P \<Longrightarrow> \<exists> st'. st' \<in> P' \<and> st =\<^sub>v st'"
  and Pw: "\<And> st. st \<in> Pw \<Longrightarrow> \<exists> st'. st' \<in> Pw' \<and> st =\<^sub>v st'"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
proof -
  have P: "rqrstep nfs Q P \<subseteq> rqrstep nfs Q P'" by (rule rqrstep_rename_vars[OF P])
  have Pw: "rqrstep nfs Q Pw \<subseteq> rqrstep nfs Q Pw'" by (rule rqrstep_rename_vars[OF Pw])
  have "SN_rel_ext (rqrstep nfs Q P \<inter> {(s, t). s \<in> NF_terms Q}) (rqrstep nfs Q Pw \<inter> {(s, t). s \<in> NF_terms Q})
   (qrstep nfs Q R) (qrstep nfs Q Rw) (\<lambda>x. m \<longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {x})"
    by (rule SN_rel_ext_mono[OF _ _ _ _ finite_dpp_imp_SN_rel_ext[OF fin]], insert P Pw, auto)
  from SN_rel_ext_imp_finite_dpp[OF this] show ?thesis .
qed   


subsection \<open>Soundness and Chain-Identifyingness of Termination Techniques and DP Processors\<close>


definition
  subset_proc :: "(('f, 'v) dpp \<Rightarrow> ('f, 'v) dpp \<Rightarrow> bool) \<Rightarrow> bool"
where
  "subset_proc proc \<longleftrightarrow> (\<forall> nfs m P Pw Q R Rw nfs' m' P' Pw' Q' R' Rw'. proc (nfs,m,P,Pw,Q,R,Rw) (nfs',m',P',Pw',Q',R',Rw') \<longrightarrow>
     (R' \<union> Rw' \<subseteq> R \<union> Rw \<and> Q' = Q \<and> nfs' = nfs \<and> (m' \<longrightarrow> m) \<and> (\<forall>s t \<sigma>. min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma> \<longrightarrow>
       (\<exists>i. ichain (nfs,m',P',Pw',Q',R',Rw') (shift s i) (shift t i) (shift \<sigma> i)))))"

definition
  sound_proc :: "(('f, 'v) dpp \<Rightarrow> ('f, 'v) dpp \<Rightarrow> bool) \<Rightarrow> bool"
where
  "sound_proc proc \<longleftrightarrow> (\<forall>nfs m P Pw Q R Rw nfs' m' P' Pw' Q' R' Rw'.
    proc (nfs, m, P, Pw, Q, R, Rw) (nfs', m', P', Pw', Q', R', Rw') \<and> finite_dpp (nfs',m',P', Pw', Q', R', Rw') \<longrightarrow>
    finite_dpp (nfs,m,P, Pw, Q, R, Rw))"

lemma subset_proc_to_sound_proc: 
  assumes subset_proc: "subset_proc proc"
  shows "sound_proc proc"
unfolding sound_proc_def
proof (intro allI impI, erule conjE)
  fix DPP DPP'
  assume cond: "proc DPP DPP'" and finite: "finite_dpp DPP'"
  obtain nfs m P Pw Q R Rw where dpp: "DPP = (nfs,m,P,Pw,Q,R,Rw)" by (cases DPP, blast)
  obtain nfs' m' P' Pw' Q' R' Rw' where dpp': "DPP' = (nfs',m',P',Pw',Q',R',Rw')" by (cases DPP', blast)
  show "finite_dpp DPP"
  proof (rule ccontr)
    assume "\<not> finite_dpp DPP"
    from this[unfolded dpp] obtain s t \<sigma> where min: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>" unfolding finite_dpp_def by auto
    from subset_proc[unfolded subset_proc_def, rule_format, OF cond[unfolded dpp dpp']] min
    obtain i where subset: "R' \<union> Rw' \<subseteq> R \<union> Rw" and id: "Q' = Q"  "nfs' = nfs" and 
    m': "m' \<Longrightarrow> m" and
      ichain: "ichain (nfs,m',P',Pw',Q',R',Rw') (shift s i) (shift t i) (shift \<sigma> i)" by force
    have "min_ichain (nfs,m',P',Pw',Q',R',Rw') (shift s i) (shift t i) (shift \<sigma> i)" 
      by (rule min_ichainI[OF subset _ ichain], insert min id m', auto)
    then have "\<not> finite_dpp DPP'" unfolding finite_dpp_def dpp' id by blast
    with finite show False by auto
  qed
qed

lemma sound_proc: assumes "finite_dpp DPP'"
  and "proc DPP DPP'"
  and "sound_proc proc"
  shows "finite_dpp DPP"
  using assms unfolding sound_proc_def by (cases DPP, cases DPP') blast

lemma subset_proc:
  assumes fin: "finite_dpp DPP'"
    and proc: "proc DPP DPP'"
    and subset: "subset_proc proc"
  shows "finite_dpp DPP"
  by (rule sound_proc[OF fin proc subset_proc_to_sound_proc[OF subset]])

end
