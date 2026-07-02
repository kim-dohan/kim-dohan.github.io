(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Q_Reduction_Nonterm
imports 
  Nontermination
  Auxx.Util
begin

locale cleaning_Q =
  fixes F :: "'f sig"
  and G :: "'f sig"
  and c :: "'f \<times> nat \<Rightarrow> 'f"
  and Q :: "('f,'v)terms"
  assumes c_F: "\<And> f n. (f,n) \<in> F \<Longrightarrow> c (f,n) = f"
  and FG: "\<And> q. q \<in> Q \<Longrightarrow> funas_term q \<subseteq> F \<union> G"
  and cG: "range (\<lambda> (f,n). (c (f,n),n)) \<inter> G = {}"
  and c_inj: "inj (\<lambda> (f,n). (c (f,n),n))"
begin

abbreviation cc where "cc \<equiv> (\<lambda> (f,n). (c (f,n),n))"

definition Q' where "Q' \<equiv> {q. q \<in> Q \<and> funas_term q \<subseteq> F}"

fun
  clean_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "clean_term (Var x) = Var x" |
  "clean_term (Fun f ts) = Fun (c (f, length ts)) (map clean_term ts)"

lemma funas_term_clean_term: "funas_term (clean_term t) \<subseteq> range cc"
  by (induct t) auto

fun
  clean_subst :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
where
  "clean_subst \<sigma> = (clean_term \<circ> \<sigma>)"

fun
  clean_ctxt :: "('f, 'v)ctxt \<Rightarrow> ('f, 'v)ctxt"
where
  "clean_ctxt \<box> = \<box>" |
  "clean_ctxt (More f bef C aft) = More (c (f,Suc (length bef + length aft)))
      (map clean_term bef) (clean_ctxt C) (map clean_term aft)"

lemma clean_subst_apply_term[simp]:
  assumes "funas_term t \<subseteq> F"
  shows "clean_term (t \<cdot> \<sigma>) = t \<cdot> (clean_subst \<sigma>)"
using assms
proof (induct t rule: term.induct)
  case (Fun f ss)
  from Fun(2)
    have "\<forall>t\<in>set ss. funas_term t \<subseteq> F" by auto
  with Fun have IH: "\<And>t. t \<in> set ss \<Longrightarrow> clean_term (t \<cdot> \<sigma>) = t \<cdot> (clean_subst \<sigma>)" by best
  with Fun show ?case using c_F[of f "length ss"] by auto
qed simp

lemma clean_ctxt_apply_term[simp]:
  shows "clean_term (C\<langle>t\<rangle>) = (clean_ctxt C)\<langle>clean_term t\<rangle>"
  by (induct C, auto)

definition c' where "c' \<equiv> fst o the_inv (\<lambda> (f,n). (c (f,n),n))"

lemma c'[simp]: "c' (c (f,n),n) = f" unfolding c'_def o_def
  using the_inv_f_f[OF c_inj, of "(f,n)"] by simp

fun
  clean_term' :: "('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "clean_term' (Var x) = Var x" |
  "clean_term' (Fun f ts) = Fun (c' (f, length ts)) (map clean_term' ts)"

fun
  clean_subst' :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
where
  "clean_subst' \<sigma> = (clean_term' \<circ> \<sigma>)"

fun
  clean_ctxt' :: "('f, 'v)ctxt \<Rightarrow> ('f, 'v)ctxt"
where
  "clean_ctxt' \<box> = \<box>" |
  "clean_ctxt' (More f bef C aft) = More (c' (f,Suc (length bef + length aft)))
      (map clean_term' bef) (clean_ctxt' C) (map clean_term' aft)"

lemma clean_term'[simp]: "clean_term' (clean_term t) = t"
  by (induct t, auto intro: map_idI)

lemma clean_subst_apply_term'[simp]:
  shows "clean_term' (t \<cdot> \<sigma>) = clean_term' t \<cdot> clean_subst' \<sigma>"
  by (induct t, auto)

lemma clean_ctxt_apply_term'[simp]:
  shows "clean_term' (C\<langle>t\<rangle>) = (clean_ctxt' C)\<langle>clean_term' t\<rangle>"
  by (induct C, auto)

lemma clean_term_NF: assumes t: "t \<in> NF_terms Q'"
  shows "clean_term t \<in> NF_terms Q"
proof -
  let ?Q = "NF_terms Q"
  let ?Q' = "NF_terms Q'"
  let ?c = clean_term
  let ?c' = clean_term'
  show "?c t \<in> NF_terms Q"
  proof (rule NF_termsI)
    fix C q \<sigma>
    assume ct: "?c t = C \<langle>q \<cdot> \<sigma>\<rangle>" and q: "q \<in> Q"
    from ct have "?c' (?c t) = ?c' (C\<langle>q \<cdot> \<sigma>\<rangle>)" by simp
    then have tq: "t = (clean_ctxt' C)\<langle>?c' q \<cdot> clean_subst' \<sigma>\<rangle>" by simp
    then have nNF: "t \<notin> NF_terms {?c' q}" by auto
    show False
    proof (cases "funas_term q \<subseteq> F")
      case True       
      with q have q: "q \<in> Q'" unfolding Q'_def by auto
      from clean_subst_apply_term[OF True, of Var] have "?c q = q" by (simp add: o_def)
      then have "?c' (?c q) = ?c' q" by simp
      then have "?c' q = q" by simp
      with nNF have nNF: "t \<notin> NF_terms {q}" by simp
      with NF_trs_mono[of "{(q,q)}" "Id_on Q'"] q t show False by force
    next
      case False
      then obtain f n where fq: "(f,n) \<in> funas_term q" and fF: "(f,n) \<notin> F" by auto
      from FG[OF q] fq fF have fG: "(f,n) \<in> G" by auto
      from ct have "funas_term (?c t) = funas_term (C\<langle>q \<cdot> \<sigma>\<rangle>)" by auto
      with fq have "(f,n) \<in> funas_term (?c t)" by (simp add: funas_term_subst)
      with funas_term_clean_term have "(f,n) \<in> range cc" by auto
      with fG cG show False by auto
     qed
  qed
qed

lemma clean_term_supt_NF: assumes NF: "\<forall> u \<lhd> l\<sigma>. u \<in> NF_terms Q'"
  shows "\<forall> u \<lhd> clean_term l\<sigma>. u \<in> NF_terms Q"
proof -
  let ?Q = "NF_terms Q"
  let ?Q' = "NF_terms Q'"
  let ?c = clean_term
  let ?c' = clean_term'
  note NF_conv = NF_terms_args_conv[symmetric]
  show ?thesis unfolding NF_conv
  proof (intro ballI)
    fix u
    assume u: "u \<in> set (args (?c l\<sigma>))"    
    then obtain t where u: "u = ?c t" and t: "t \<in> set (args (l\<sigma>))"
      by (cases "l\<sigma>", auto)
    from NF[unfolded NF_conv, rule_format, OF t] have t: "t \<in> ?Q'" .
    from clean_term_NF[OF this]
    show "u \<in> NF_terms Q" unfolding u .
  qed
qed

lemma clean_NF_subst: assumes "NF_subst nfs (l,r) \<sigma> Q'"
  shows "NF_subst nfs (l,r) (clean_subst \<sigma>) Q"
proof
  fix x
  let ?Q' = "NF_terms Q'"
  assume nfs and x: "x \<in> vars_term l \<or> x \<in> vars_term r"
  with assms[unfolded NF_subst_def vars_rule_def] have "\<sigma> x \<in> ?Q'" by auto
  from clean_term_NF[OF this]
  show "clean_subst \<sigma> x \<in> NF_terms Q" by simp
qed


lemma clean_qrstep: assumes F: "funas_trs R \<subseteq> F"
  and step: "(s,t) \<in> qrstep nfs Q' R"
  shows "(clean_term s, clean_term t) \<in> qrstep nfs Q R"
proof -
  let ?QR = "qrstep nfs Q R"
  let ?Q = "NF_terms Q"
  let ?QR' = "qrstep nfs Q' R"
  let ?Q' = "NF_terms Q'"
  from step obtain C l r \<sigma> where lr: "(l,r) \<in> R" and NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> ?Q'" 
    and nfs: "NF_subst nfs (l,r) \<sigma> Q'"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  from lr F have l: "funas_term l \<subseteq> F" and r: "funas_term r \<subseteq> F"
    unfolding funas_trs_def funas_rule_def [abs_def]
    by force+
  let ?\<sigma> = "clean_subst \<sigma>"
  let ?c = clean_term
  let ?c' = clean_term'
  note clr = clean_subst_apply_term[OF l] clean_subst_apply_term[OF r]
  note NF =  clean_term_supt_NF[OF NF]
  note nfs = clean_NF_subst[OF nfs]
  show ?thesis unfolding s t clean_ctxt_apply_term clr
    by (rule qrstepI[OF _ lr refl refl], insert NF nfs clr, auto)
qed


lemma clean_qrsteps: 
  assumes F: "funas_trs R \<subseteq> F"
  and step: "(s,t) \<in> (qrstep nfs Q' R)^*"
  shows "(clean_term s, clean_term t) \<in> (qrstep nfs Q R)^*"
  using step
proof (induct)
  case base then show ?case by auto
next
  case (step t u)
  from step(3) clean_qrstep[OF F step(2)] show ?case by auto
qed

lemma clean_ichain: assumes FR: "funas_trs R \<subseteq> F"
  and FP: "funas_trs P \<subseteq> F"
  and ichain: "i_chain (nfs,P,Q',R) s t \<sigma>"
  shows "i_chain (nfs,P,Q,R) s t (\<lambda> i. clean_subst (\<sigma> i))"
proof -
  let ?\<sigma> = "\<lambda> i. clean_subst (\<sigma> i)"
  let ?c = clean_term
  from ichain[simplified]
  have P: "\<And> i. (s i, t i) \<in> P"
    and steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q' R)^*"
    and NF: "\<And> i. \<forall> u \<lhd> s i \<cdot> \<sigma> i. u \<in> NF_terms Q'" 
    and nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q'" by auto
  {
    fix i
    from P[of i] FP have F: "funas_term (s i) \<subseteq> F" "funas_term (t i) \<subseteq> F"
      unfolding funas_trs_def funas_rule_def [abs_def] by force+
    note clean_subst_apply_term[OF F(1)] clean_subst_apply_term[OF F(2)]
  } note subst = this
  {
    fix i
    from clean_qrsteps[OF FR steps[of i]]
    have "(t i \<cdot> ?\<sigma> i, s (Suc i) \<cdot> ?\<sigma> (Suc i)) \<in> (qrstep nfs Q R)^*" unfolding subst .
  } note steps = this
  {
    fix i
    from clean_term_supt_NF[OF NF[of i]]
    have "\<And> u. u \<lhd> s i \<cdot> ?\<sigma> i \<Longrightarrow> u \<in> NF_terms Q" unfolding subst by auto
  } note NF = this
  show ?thesis using steps P NF clean_NF_subst[OF nfs] by simp
qed

lemma q_reduction_SN: 
  assumes FR: "funas_trs R \<subseteq> F"
  and nSN: "\<not> SN (qrstep nfs Q' R)"
  shows "\<not> SN (qrstep nfs Q R)"
proof -
  from nSN obtain f where steps: "\<And> i. (f i, f (Suc i)) \<in> (qrstep nfs Q' R)" unfolding SN_defs by blast
  from clean_qrstep[OF FR steps] show ?thesis by force
qed
  

lemma infinite_dpp_q_reduction: assumes FR: "funas_trs R \<subseteq> F"
  and FP: "funas_trs P \<subseteq> F"
  and inf: "infinite_dpp (nfs,P,Q',R)"
  shows "infinite_dpp (nfs,P,Q,R)"
proof (cases "SN (qrstep nfs Q' R)")
  case True
  with inf obtain s t \<sigma> where "i_chain (nfs,P,Q',R) s t \<sigma>" by auto
  from clean_ichain[OF FR FP this] show ?thesis unfolding infinite_dpp.simps by blast
next
  case False
  from q_reduction_SN[OF FR False] show ?thesis by auto
qed
end


lemma finite_infinite_cleaning_Q: fixes Q :: "('f,'v)terms"
  assumes finF: "finite F" 
  and finite: "finite Q"
  and infinite: "infinite (UNIV :: 'f set)"
  shows "\<exists> c G. cleaning_Q F G c Q"
proof -
  let ?G = "\<Union>(funas_term ` Q) - F"
  obtain G where G: "G = ?G" by auto
  have finQ: "finite (funas_trs (Id_on Q))" 
    by (rule finite_funas_trs, insert finite, unfold Id_on_def, auto)
  have "finite (\<Union>(funas_term ` Q))"
    by (rule finite_subset[OF _ finQ], auto simp: funas_trs_def Id_on_def funas_rule_def)
  then have finG: "finite G" unfolding G by auto
  from finF finG have fin: "finite (fst ` (F \<union> G))" by auto
  let ?f = "\<lambda> x. (x :: 'f)"
  have inj: "inj ?f" unfolding inj_on_def by auto
  from infinite_inj_on_finite_remove_finite[OF infinite inj fin]
  obtain g where inj: "inj (g :: 'f \<Rightarrow> 'f)" and ran: "range g \<inter> (fst ` (F \<union> G)) = {}" by auto
  let ?c = "\<lambda> f n. if (f,n) \<in> F then f else g f"
  obtain c where c: "c = (\<lambda> (f,n). ?c f n)" by auto
  let ?cc = "\<lambda> (f,n). (c (f,n),n)"
  have "cleaning_Q F G c Q"
  proof
    fix q
    assume "q \<in> Q" then show "funas_term q \<subseteq> F \<union> G" unfolding G by auto
  next
    fix f n 
    assume "(f,n) \<in> F"
    then show "c (f,n) = f" unfolding c by simp
  next
    {
      fix f n
      assume "(f,n) \<in> range ?cc \<inter> G"
      then have fc: "(f,n) \<in> range ?cc" and fG: "(f,n) \<in> G" by force+
      from fG ran have fg: "f \<notin> range g" by force
      from fc[unfolded c] fg have fF: "(f,n) \<in> F" by force
      with G fG have False by auto
    }
    then show "range ?cc \<inter> G = {}" by force
  next
    show "inj ?cc" unfolding c split inj_on_def
    proof (intro ballI impI)
      fix fn1 fn2
      assume id: "(case fn1 of (f,n) \<Rightarrow> (?c f n,n)) = (case fn2 of (f,n) \<Rightarrow> (?c f n,n))"
      obtain f1 f2 n1 n where fn: "fn1 = (f1,n1)" "fn2 = (f2,n)" by force+
      from id fn have n1: "n1 = n" by simp
      note fn = fn[unfolded n1]
      from id fn have id: "?c f1 n = ?c f2 n" by simp
      have "f1 = f2"
      proof (cases "(f1,n) \<in> F")
        case True
        with id ran have "(f2,n) \<in> F" by force
        with id True show ?thesis by simp
      next
        case False
        with id ran have "(f2,n) \<notin> F" by force
        with id False have "g f1 = g f2" by simp
        with inj show ?thesis unfolding inj_on_def by auto
      qed
      then show "fn1 = fn2" unfolding fn by simp
    qed
  qed
  then show ?thesis by blast
qed

lemma infinite_dpp_q_reduction: fixes Q and P R :: "('f,'v)trs"
  defines F: "F \<equiv> funas_trs P \<union> funas_trs R" 
  assumes inf: "infinite_dpp (nfs,P,{q. q \<in> Q \<and> funas_term q \<subseteq> F},R)"
  and finite: "finite P" "finite R" "finite Q"
  and infinite: "infinite (UNIV :: 'f set)"
  shows "infinite_dpp (nfs,P,Q,R)"
proof -
  have finF: "finite F" using finite_funas_trs[OF finite(1)] finite_funas_trs[OF finite(2)] 
    unfolding F by auto
  from finite_infinite_cleaning_Q[OF finF finite(3) infinite]
  obtain c G where cleaning: "cleaning_Q F G c Q" by blast
  interpret cleaning_Q F G c Q by (rule cleaning)
  from inf have inf: "infinite_dpp (nfs,P,Q',R)" unfolding Q'_def .
  from F have FR: "funas_trs R \<subseteq> F"
  and FP: "funas_trs P \<subseteq> F" by auto
  from infinite_dpp_q_reduction[OF FR FP inf]
  show ?thesis .
qed

end

