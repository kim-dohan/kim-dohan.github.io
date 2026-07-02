(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Monadic_Rewriting
  imports TRS.Signature_Extension
begin

text \<open>A formalization of the most important result of 
  "Adding Constants to String Rewriting", namely that the
  termination behaviour is unchanged\<close>

locale pre_max_unary =
  fixes 
      NU :: "'f set" (* new unary symbols *)
  and d d' :: "'f \<Rightarrow> 'f" (* transformation from constants to unary symbols (d) and inverse (d') *)
begin
fun str :: "'v \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term" where
  "str _ (Var x) = Var x"
| "str x (Fun f [t]) = Fun f [str x t]"
| "str x (Fun f _) = Fun (d f) [Var x]"

fun "term" :: "('f,'v)term \<Rightarrow> ('f,'v)term" where
  "term (Var x) = Var x"
| "term (Fun f [t]) = (if f \<in> NU then Fun (d' f) [] else Fun f [term t])"
| "term (Fun f ts) = Fun f [Fun f ts,Fun f ts]"

fun drop :: "('f,'v)term \<Rightarrow> ('f,'v)subst" where
  "drop (Var x) = Var"
| "drop (Fun f [t]) = (if f \<in> NU then (\<lambda> _. t) else drop t)"
| "drop t = Var"
end

declare pre_max_unary.term.simps[code]
declare pre_max_unary.drop.simps[code]
declare pre_max_unary.str.simps[code]

locale max_unary = pre_max_unary NU d d' for NU :: "'f set" and d d' :: "'f \<Rightarrow> 'f" +
  (* MU is original signature of TRS, containing constants and unary symbols *)
  (* NU is set of new unary symbols that have been generated from constants *)
  (* renamings are required since e.g., (f,0) and (f,1) may be present in MU, where
     then (f,0) has to be renamed into some fresh (g,1) where g is in NU, these are managed by d and d' *)
  fixes MU :: "'f sig" 
  assumes MU: "\<And> f n. (f,n) \<in> MU \<Longrightarrow> n \<le> 1"
  and NU: "\<And> f. f \<in> NU \<Longrightarrow> (f,1) \<notin> MU"
  and d'd: "\<And> f. (f,0) \<in> MU \<Longrightarrow> d f \<in> NU \<and> d' (d f) = f"
  and dd': "\<And> f. f \<in> NU \<Longrightarrow> (d' f,0) \<in> MU \<and> d (d' f) = f" 
begin

definition "U \<equiv> { (f,1 :: nat) | f. (f,1) \<in> MU \<or> f \<in> NU}"
definition "NU1 \<equiv> { (f,1 :: nat) | f. f \<in> NU}"

lemma MU_NU1: "MU \<inter> NU1 = {}" unfolding NU1_def using NU by auto

lemma MU_induct[consumes 1,case_names Var Fun Const,induct type: "term"]:
  fixes P :: "('f,'v)term \<Rightarrow> bool"
  assumes "funas_term t \<subseteq> MU"
    and "\<And>x. P(Var x)"
    and "\<And>f t. funas_term t \<subseteq> MU \<Longrightarrow> (f,1) \<in> MU \<Longrightarrow> f \<notin> NU \<Longrightarrow> P t \<Longrightarrow> P(Fun f [t])"
    and "\<And>f. (f,0) \<in> MU \<Longrightarrow> P(Fun f [])"
  shows "P t"
using assms(1)
proof (induct t)
  case (Var x)
  show ?case by (rule assms(2))
next
  case (Fun f ts)
  with MU[of f "length ts"] have len: "length ts \<le> 1" by auto
  show ?case
  proof (cases ts)
    case Nil
    with assms(4)[of f] Fun show ?thesis by auto
  next
    case (Cons t tts)
    with len have ts: "ts = [t]" by auto
    with assms(3)[of t f] Fun NU[of f] show ?thesis by auto
  qed
qed
 
lemma U_induct[consumes 1,case_names Var Fun Const,induct type: "term"]:
  fixes P :: "('f,'v)term \<Rightarrow> bool"
  assumes "funas_term u \<subseteq> U"
    and "\<And>x. P(Var x)"
    and "\<And>f u. funas_term u \<subseteq> U \<Longrightarrow> (f,1) \<in> MU \<Longrightarrow> f \<notin> NU \<Longrightarrow> P u \<Longrightarrow> P(Fun f [u])"
    and "\<And>f u. funas_term u \<subseteq> U \<Longrightarrow> f \<in> NU \<Longrightarrow> (f,1) \<notin> MU \<Longrightarrow> P u \<Longrightarrow> P(Fun f [u])"
  shows "P u"
using assms(1)
proof (induct u)
  case (Var x)
  show ?case by (rule assms(2))
next
  case (Fun f us)
  then have "(f,length us) \<in> U" by auto
  from this[unfolded U_def] have len: "length us = 1" and f: "f \<in> NU \<or> (f,1) \<in> MU" by auto
  from len obtain u where us: "us = [u]" by (cases us, auto)
  from Fun(2) us have u: "funas_term u \<subseteq> U" by auto
  from Fun(1)[OF _ u] us have p: "P u" by auto
  note props = assms(3-4)[OF u _ _ this, folded us]
  from f show ?case
  proof
    assume f: "f \<in> NU"
    from props(2)[OF f NU[OF f]] show ?thesis .
  next
    assume f: "(f,1) \<in> MU"
    with NU[of f] have "f \<notin> NU" by auto
    from props(1)[OF f this] show ?thesis .
  qed
qed


lemma lemma_3_1: "funas_term t \<subseteq> MU \<Longrightarrow> term (str X t) = t"
  by (induct t, auto simp: d'd)

lemma lemma_3_2: "funas_term u \<subseteq> U \<Longrightarrow> str X (term u) \<cdot> drop u = u"
  by (induct u, auto simp: dd')

lemma lemma_3_3: "funas_term t \<subseteq> MU \<Longrightarrow> vars_term t \<noteq> {} \<Longrightarrow> str X (t \<cdot> \<sigma>) = str Y t \<cdot> (\<lambda> x. str X (\<sigma> x))"
  by (induct t, auto)

lemma lemma_3_4: "funas_term u \<subseteq> U \<Longrightarrow> term (u \<cdot> \<sigma>) = term u \<cdot> (\<lambda> x. term (\<sigma> x))"
  by (induct u, auto)

lemma lemma_3_5: "funas_term u \<subseteq> U \<Longrightarrow> funas_term u \<inter> NU1 \<noteq> {} \<Longrightarrow> term (u \<cdot> \<sigma>) = term u"
  by (induct u, insert MU_NU1, auto simp: U_def)

lemma lemma_3_6: "funas_term u \<subseteq> U \<Longrightarrow> vars_term (term u) \<noteq> {} \<Longrightarrow> drop u = Var"
  by (induct u, auto)

lemma funas_term_str: "funas_term t \<subseteq> MU \<Longrightarrow> funas_term (str X t) \<subseteq> U"
  by (induct t, auto simp: d'd U_def)

lemma funas_term_str_const: "funas_term t \<subseteq> MU \<Longrightarrow> vars_term t = {} \<Longrightarrow> funas_term (str X t) \<inter> NU1 \<noteq> {}"
  by (induct t, auto simp: NU1_def d'd)

lemma funas_term_term: "funas_term u \<subseteq> U \<Longrightarrow> funas_term (term u) \<subseteq> MU"
  by (induct u, auto simp: dd')

lemma vars_term_str: "vars_term t \<subseteq> {X} \<Longrightarrow> vars_term (str X t) = {X}"
proof (induct t)
  case (Fun f ts)
  then show ?case by (cases ts, simp, cases "tl ts", auto)
qed auto

context 
  fixes R S :: "('f,'v)trs"
  assumes R: "funas_trs R \<subseteq> MU"
  and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and S: "\<And> l r. (l,r) \<in> R \<Longrightarrow> \<exists> Y. vars_term l \<subseteq> {Y} \<and> (str Y l, str Y r) \<in> S"
begin

lemma simulation_R_rrstep: assumes uU: "funas_term u \<subseteq> U"
  and step: "(term u,t) \<in> rrstep R"
  shows "\<exists> v. funas_term v \<subseteq> U \<and> (u,v) \<in> rrstep S \<and> t = term v"
proof -  
  obtain s where u: "s = term u" by auto
  from step[unfolded u[symmetric] rrstep_def'] obtain l r \<sigma> where s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" and lr: "(l,r) \<in> R" by auto
  note funas_term_subst[simp]
  from R lr have rMU: "funas_term r \<subseteq> MU" by (force simp: funas_trs_def funas_rule_def)
  from funas_term_str[OF rMU] have rU: "\<And> Y. funas_term (str Y r) \<subseteq> U" .
  from funas_term_str_const[OF rMU] have rNU1: "\<And> Y. vars_term r = {} \<Longrightarrow> funas_term (str Y r) \<inter> NU1 \<noteq> {}" .
  note wf = wf[OF lr]
  from S[OF lr] obtain Y where Y: "vars_term l \<subseteq> {Y}" and slr: "(str Y l, str Y r) \<in> S" by auto
  from vars_term_str[OF Y] vars_term_str[of r Y] wf Y have wf2: "vars_term (str Y r) = vars_term (str Y l)" by auto
  from funas_term_term[OF uU, folded u] have "funas_term s \<subseteq> MU" .
  with wf rMU
  have rsMU: "funas_term (r \<cdot> \<sigma>) \<subseteq> MU" and lMU: "funas_term l \<subseteq> MU" unfolding s t by force+
  have id: "l \<cdot> \<sigma> = term u" unfolding u[symmetric] s ..
  from lemma_3_2[OF uU, folded id] have u: "str Y (l \<cdot> \<sigma>) \<cdot> drop u = u" .
  show ?thesis 
  proof (cases "ground l")
    case True
    from ground_subst_apply[OF this] 
    have l: "l \<cdot> \<sigma> = l" .
    from True wf have gr: "ground r" and vars: "vars_term l = {}" "vars_term r = {}" 
      unfolding ground_vars_term_empty by auto
    from ground_subst_apply[OF gr] have r: "r \<cdot> \<sigma> = r" .
    have "u = str Y (l \<cdot> \<sigma>) \<cdot> drop u" using u by simp
    also have "l \<cdot> \<sigma> = l" by fact
    finally have u: "str Y l \<cdot> drop u = u" by simp
    define v where "v = str Y r \<cdot> drop u"
    have step: "(u,v) \<in> rrstep S" unfolding v_def
      by (rule rrstepI[OF slr, of _ "drop u"], insert u, auto)
    have "term v = term (str Y r \<cdot> drop u)" unfolding v_def ..
    also have "\<dots> = term (str Y r)" 
      by (rule lemma_3_5[OF rU rNU1[OF vars(2)]])
    also have "\<dots> = r"
      by (rule lemma_3_1[OF rMU])
    finally have vr: "term v = r" .
    have vU: "funas_term v \<subseteq> U" using uU  
      unfolding v_def funas_term_subst arg_cong[of _ _ funas_term, OF u[symmetric]] wf2
      using rU by auto
    show ?thesis unfolding t
      by (intro exI[of _ v], insert vr step r vU, simp)
  next
    case False
    from this[unfolded ground_vars_term_empty] have vl: "vars_term l \<noteq> {}" by auto
    define v where "v = str Y r \<cdot> (\<lambda>x. str Y (\<sigma> x)) \<cdot> drop u"
    let ?sig = "(\<lambda>x. str Y (\<sigma> x)) \<circ>\<^sub>s drop u"
    have "u = str Y (l \<cdot> \<sigma>) \<cdot> drop u" using u by simp
    also have "\<dots> = str Y l \<cdot> (\<lambda>x. str Y (\<sigma> x)) \<cdot> drop u"
      unfolding lemma_3_3[OF lMU vl, of Y _ Y] ..
    finally have uid: "u = str Y l \<cdot> (\<lambda>x. str Y (\<sigma> x)) \<cdot> drop u" .
    then have step: "(u,v) \<in> rrstep S"
      by (intro rrstepI[OF slr, of _ ?sig], unfold v_def, auto)
    have rsU: "funas_term (str Y (r \<cdot> \<sigma>)) \<subseteq> U"
      by (rule funas_term_str[OF rsMU])
    have vr: "term v = r \<cdot> \<sigma>"
    proof (cases "vars_term r = {}")
      case True
      from True wf have gr: "ground r" and vars: "vars_term r = {}" 
        unfolding ground_vars_term_empty by auto
      from ground_subst_apply[OF gr] have r: "r \<cdot> \<sigma> = r" .
      have "term v = term (str Y r)" unfolding v_def using lemma_3_5[OF rU rNU1[OF vars], of Y ?sig]
        by auto
      also have "\<dots> = r" by (rule lemma_3_1[OF rMU])
      also have "\<dots> = r \<cdot> \<sigma>" by (simp add: r)
      finally show ?thesis .
    next
      case False
      have v: "term v = term (str Y (r \<cdot> \<sigma>) \<cdot> drop u)" unfolding v_def
        unfolding lemma_3_3[OF rMU False, of Y _ Y] ..
      also have "term (str Y (r \<cdot> \<sigma>) \<cdot> drop u) = term (str Y (r \<cdot> \<sigma>))"
      proof (cases "vars_term (r \<cdot> \<sigma>) = {}")
        case True
        show ?thesis
          by (rule lemma_3_5[OF funas_term_str funas_term_str_const[OF _ True]], insert rsMU, auto)
      next
        case False
        with wf have "vars_term (l \<cdot> \<sigma>) \<noteq> {}" by (auto simp: vars_term_subst)
        then have "vars_term (term u) \<noteq> {}" using id by simp
        from lemma_3_6[OF uU this] have u: "drop u = Var" .
        then show ?thesis by simp
      qed
      also have "\<dots> = r \<cdot> \<sigma>"
        by (rule lemma_3_1[OF rsMU])
      finally show ?thesis .
    qed
    have "funas_term v \<subseteq> funas_term u \<union> U" unfolding arg_cong[OF uid, of funas_term] v_def
      using wf2 rU
      by (auto simp: vars_term_subst)
    also have "\<dots> \<subseteq> U" using uU by auto
    finally 
    show ?thesis unfolding t
      by (intro exI[of _ v], insert vr step, simp)
  qed
qed

lemma simulation_R_rstep: assumes uU: "funas_term u \<subseteq> U"
  and step: "(term u, t) \<in> rstep R"
  shows "\<exists> v. funas_term v \<subseteq> U \<and> (u,v) \<in> rstep S \<and> t = term v"
proof -
  obtain s where u: "s = term u" by auto
  from step[folded u] obtain D l r \<sigma> where s: "s = D \<langle> l \<cdot> \<sigma> \<rangle>" and t: "t = D \<langle> r \<cdot> \<sigma> \<rangle>" and lr: "(l,r) \<in> R" by auto
  from funas_term_term[OF uU, folded u, unfolded s] have DMU: "funas_ctxt D \<subseteq> MU" by auto
  show ?thesis using DMU u uU unfolding s t
  proof (induct D arbitrary: u)
    case (More f bef C aft)
    from MU[of f "Suc (length bef + length aft)"] More(2) have *: "aft = []" "bef = []" and fMU: "(f,1) \<in> MU" by auto
    note More = More[unfolded *]
    from NU[of f] fMU have fNU: "f \<notin> NU" by auto
    from More(3) obtain g us where u: "u = Fun g us" and id: "Fun f [C \<langle> l \<cdot> \<sigma> \<rangle>] = term (Fun g us)" by (cases u, auto)
    from id obtain u' where us: "us = [u']" by (cases us, simp, cases "tl us", auto)
    from id[unfolded us] have g: "g = f" and u': "C \<langle> l \<cdot> \<sigma> \<rangle> = term u'"
      by (auto split: if_splits)
    from More(1)[OF _ u'] More(2) More(4)[unfolded u us] obtain v' where v': "funas_term v' \<subseteq> U" 
    and step: "(u', v') \<in> rstep S" and id: "C\<langle>r \<cdot> \<sigma>\<rangle> = term v'" by auto
    let ?v = "Fun f [v']"
    show ?case
      by (intro exI[of _ ?v], unfold u g us, insert fMU v' id rstep_ctxt[OF step, of "More f [] Hole []"] fNU *, 
        auto simp: U_def)
  next
    case Hole
    with rrstepI[OF lr _ refl, of "term u" \<sigma>] have "(term u, r \<cdot> \<sigma>) \<in> rrstep R" by auto
    from simulation_R_rrstep[OF Hole(3) this] show ?case unfolding rstep_iff_rrstep_or_nrrstep by auto
  qed
qed

lemma simulation_R_rsteps: assumes uU: "funas_term u \<subseteq> U"
  and step: "(term u, t) \<in> (rstep R)^*"
  shows "\<exists> v. funas_term v \<subseteq> U \<and> (u,v) \<in> (rstep S)^* \<and> t = term v"
  using step
proof (induct)
  case base
  with uU show ?case by blast
next
  case (step v t)
  from step(3) obtain w where wU: "funas_term w \<subseteq> U" and uw: "(u, w) \<in> (rstep S)\<^sup>*" and vw: "v = term w" by auto
  from simulation_R_rstep[OF wU step(2)[unfolded vw]] obtain s where 
    "funas_term s \<subseteq> U \<and> (w, s) \<in> rstep S \<and> t = term s" by auto
  with uw show ?case by auto
qed

lemma simulation_R_chain: assumes uU: "funas_term u \<subseteq> U"
  and step: "chain (rstep R) f"
  and start: "term u = f 0"
  shows "\<not> SN_on (rstep S) {u}"
proof -
  let ?P = "\<lambda> u. funas_term u \<subseteq> U \<and> (\<exists> i. f i = term u)"
  show ?thesis
  proof (rule conditional_steps_imp_not_SN_on[of ?P])
    show "?P u" using uU and start by auto
  next
    fix u
    assume "?P u"
    then obtain i where u: "funas_term u \<subseteq> U" and fi: "f i = term u" by auto
    from step[THEN spec, of i] fi have step: "(term u, f (Suc i)) \<in> rstep R" by auto
    from simulation_R_rstep[OF u step]
    show "\<exists> v. (u,v) \<in> rstep S \<and> ?P v" by blast
  qed
qed

lemma SN_S_imp_SN_R: assumes SN: "SN (rstep S)"
  shows "SN (rstep R)"
proof (rule SN_sig_rstep_imp_SN_rstep[OF subset_refl], standard)
  fix f
  let ?R = "sig_step (funas_trs R) (rstep R)"
  assume chain: "chain ?R f"
  then have sig_steps: "\<And> i. (f i, f (Suc i)) \<in> ?R" by auto
  then have chain: "chain (rstep R) f" by auto
  from sig_steps[of 0] have "funas_term (f 0) \<subseteq> funas_trs R" by auto
  with R have MU: "funas_term (f 0) \<subseteq> MU" by auto
  let ?u = "str undefined (f 0)"
  from lemma_3_1[OF MU] have u1: "term ?u = f 0" .
  from funas_term_str[OF MU] have u2: "funas_term ?u \<subseteq> U" .
  from simulation_R_chain[OF u2 chain u1] SN
  show False unfolding SN_def by blast
qed
end

context 
  fixes R S Rw Sw :: "('f,'v)trs"
  assumes R: "funas_trs R \<subseteq> MU"
  and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and S: "\<And> l r. (l,r) \<in> R \<Longrightarrow> \<exists> Y. vars_term l \<subseteq> {Y} \<and> (str Y l, str Y r) \<in> S"
  and Rw: "funas_trs Rw \<subseteq> MU"
  and wfw: "\<And> l r. (l,r) \<in> Rw \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and Sw: "\<And> l r. (l,r) \<in> Rw \<Longrightarrow> \<exists> Y. vars_term l \<subseteq> {Y} \<and> (str Y l, str Y r) \<in> Sw"
begin

lemma simulation_R_Rw_rel_rstep: assumes uU: "funas_term u \<subseteq> U"
  and step: "(term u, t) \<in> relto (rstep R) (rstep Rw)"
  shows "\<exists> v. funas_term v \<subseteq> U \<and> (u,v) \<in> relto (rstep S) (rstep Sw) \<and> t = term v"
proof -
  from step obtain u1 u2 where u1: "(term u,u1) \<in> (rstep Rw)^*" and u12: "(u1,u2) \<in> rstep R" and u2t: "(u2,t) \<in> (rstep Rw)^*" by blast
  from simulation_R_rsteps[OF Rw wfw Sw uU u1] obtain v1 where 
    v1: "funas_term v1 \<subseteq> U" and uv1: "(u, v1) \<in> (rstep Sw)\<^sup>*" and u1: "u1 = term v1" by auto
  from simulation_R_rstep[OF R wf S v1 u12[unfolded u1]] obtain v2 where 
    v2: "funas_term v2 \<subseteq> U" and v12: "(v1, v2) \<in> rstep S" and u2: "u2 = term v2" by auto
  from simulation_R_rsteps[OF Rw wfw Sw v2 u2t[unfolded u2]] obtain v3 where 
    v3: "funas_term v3 \<subseteq> U" and v23: "(v2, v3) \<in> (rstep Sw)\<^sup>*" and t: "t = term v3" by auto
  from uv1 v12 v23 have "(u,v3) \<in> relto (rstep S) (rstep Sw)" by auto
  with t v3 show ?thesis by auto
qed


lemma SN_rel_S_Sw_imp_SN_rel_R_Rw: assumes SN: "SN_rel (rstep S) (rstep Sw)"
  shows "SN_rel (rstep R) (rstep Rw)"
proof (rule sig_ext_relative_rewriting_var_cond[OF wfw R Rw], simp, rule ccontr)
  let ?R = "relto (sig_step MU (rstep R)) (sig_step MU (rstep Rw))"
  let ?S = "relto (rstep S) (rstep Sw)"
  assume "\<not> SN_rel (sig_step MU (rstep R)) (sig_step MU (rstep Rw))"
  then obtain f where "chain ?R f" unfolding SN_rel_on_def SN_defs by blast
  note sig_steps = this[THEN spec]
  {
    fix i
    from sig_steps[of i] obtain v where "(f i, v) \<in> (sig_step MU (rstep Rw))^* O sig_step MU (rstep R)" by auto
    then have "(f i, v) \<in> (sig_step MU (rstep (R \<union> Rw))) O ((sig_step MU (rstep (Rw \<union> R)))^*)"
      unfolding sig_step_union rstep_union by regexp
    then obtain v where "(f i, v) \<in> sig_step MU (rstep (R \<union> Rw))" by blast
    then have "funas_term (f i) \<subseteq> MU" unfolding sig_step_def by auto
  } note MU = this
  let ?u = "str undefined (f 0)"
  from lemma_3_1[OF MU] have u1: "term ?u = f 0" .
  from funas_term_str[OF MU] have u2: "funas_term ?u \<subseteq> U" .
  let ?P = "\<lambda> u. funas_term u \<subseteq> U \<and> (\<exists> i. f i = term u)"
  have Pu: "?P ?u" using u1 u2 by auto
  have "\<not> SN_on ?S {?u}"
  proof (rule conditional_steps_imp_not_SN_on[of ?P ?u, OF Pu])
    fix t
    assume "?P t"
    then obtain i where U: "funas_term t \<subseteq> U" and i: "f i = term t" by blast
    have "(f i, f (Suc i)) \<in> relto (rstep R) (rstep Rw)"
      by (rule set_mp[OF relto_mono sig_steps[of i]], auto)
    from simulation_R_Rw_rel_rstep[OF U this[unfolded i]]
    show "\<exists> u. (t,u) \<in> ?S \<and> ?P u" by blast
  qed
  with SN show False unfolding SN_rel_on_def SN_defs by blast
qed
end
end

locale max_unary_reverse = max_unary NU d d' MU for NU :: "'f set" and d d' :: "'f \<Rightarrow> 'f" and MU :: "'f sig" +
  fixes R S :: "('f,'v)trs"
  assumes R: "funas_trs R \<subseteq> MU"
  and wf: "\<And> sl sr. (sl,sr) \<in> S \<Longrightarrow> vars_term sr \<subseteq> vars_term sl" 
  and S: "\<And> sl sr. (sl,sr) \<in> S \<Longrightarrow> \<exists> Y l r. (l,r) \<in> R \<and> (sl,sr) = (str Y l, str Y r)"
begin 

lemma simulation_S_rrstep: assumes uU: "funas_term u \<subseteq> U"
  and step: "(u,v) \<in> rrstep S"
  shows "(term u, term v) \<in> rrstep R"
proof -  
  from step[unfolded rrstep_def'] obtain sl sr \<sigma> where u: "u = sl \<cdot> \<sigma>" and v: "v = sr \<cdot> \<sigma>" and slr: "(sl,sr) \<in> S" by auto
  from S[OF slr] obtain Y l r where lr: "(l,r) \<in> R" and id: "sl = str Y l" "sr = str Y r" by auto
  from lr R have lrMU: "funas_term l \<subseteq> MU" "funas_term r \<subseteq> MU" by (force simp: funas_trs_def funas_rule_def)+
  let ?sigma = "\<lambda>x. term (\<sigma> x)"
  have u: "term u = l \<cdot> ?sigma" unfolding u id lemma_3_4[OF funas_term_str[OF lrMU(1)], unfolded lemma_3_1[OF lrMU(1)]] ..
  have v: "term v = r \<cdot> ?sigma" unfolding v id lemma_3_4[OF funas_term_str[OF lrMU(2)], unfolded lemma_3_1[OF lrMU(2)]] ..
  show ?thesis unfolding u v
    by (rule rrstepI[OF lr], auto)
qed

lemma simulation_S_rstep: assumes uU: "funas_term u \<subseteq> U"
  and step: "(u,v) \<in> rstep S"
  shows "(term u, term v) \<in> (rstep R)^="
proof -
  from step obtain D sl sr \<sigma> where id: "u = D \<langle> sl \<cdot> \<sigma> \<rangle>" "v = D \<langle> sr \<cdot> \<sigma> \<rangle>" and slr: "(sl,sr) \<in> S" by auto
  define l where "l = sl \<cdot> \<sigma>" 
  define r where "r = sr \<cdot> \<sigma>"
  from uU[unfolded id] have D: "funas_ctxt D \<subseteq> U" and lU: "funas_term (sl \<cdot> \<sigma>) \<subseteq> U" by auto
  from simulation_S_rrstep[OF lU rrstepI[OF slr refl refl, of \<sigma>]]
  have lr: "(term l, term r) \<in> rrstep R" unfolding l_def r_def .
  show ?thesis using D unfolding id l_def[symmetric] r_def[symmetric]
  proof (induct D)
    case Hole
    from lr show ?case unfolding rstep_iff_rrstep_or_nrrstep intp_actxt.simps by regexp
  next
    case (More f bef D aft)
    from More(2)[unfolded U_def] have ba: "bef = []" "aft = []" by auto
    from More have IH: "(term D\<langle>l\<rangle>, term D\<langle>r\<rangle>) \<in> (rstep R)\<^sup>=" by auto
    show ?case
    proof (cases "f \<in> NU")
      case True
      then show ?thesis unfolding ba by simp
    next
      case False
      with rstep_ctxt[of "term D\<langle>l\<rangle>" "term D\<langle>r\<rangle>" R "More f [] Hole []"] IH
      show ?thesis unfolding ba by auto
    qed
  qed
qed

lemma S_U: "funas_trs S \<subseteq> U"
proof -
  {
    fix f
    assume "f \<in> funas_trs S"
    then obtain sl sr where f: "f \<in> funas_rule (sl,sr)" and slr: "(sl,sr) \<in> S" unfolding funas_trs_def by auto
    from S[OF slr] obtain Y l r where lr: "(l,r) \<in> R" and sl: "sl = str Y l" and sr: "sr = str Y r" by auto
    from R lr have l: "funas_term l \<subseteq> MU" and r: "funas_term r \<subseteq> MU" by (force simp: funas_trs_def funas_rule_def)+
    from funas_term_str[OF l, of Y] funas_term_str[OF r, of Y] f sl sr
    have "f \<in> U" by (auto simp: funas_rule_def)
  }
  then show ?thesis by blast
qed

lemma simulation_S_rsteps: assumes uU: "funas_term u \<subseteq> U"
  and steps: "(u,v) \<in> (rstep S)^*"
  shows "(term u, term v) \<in> (rstep R)^*"
  using steps
proof (induct rule: rtrancl_induct)
  case (step v w)
  from rsteps_preserve_funas_terms_var_cond[OF S_U uU step(1) wf]
  have "funas_term v \<subseteq> U" .
  from step(3) simulation_S_rstep[OF this step(2)]
  show ?case by auto
qed simp

lemma SN_R_imp_SN_S: assumes SN: "SN (rstep R)"
  shows "SN (rstep S)"
proof (rule ccontr)
  assume nSN: "\<not> SN (rstep S)"
  {
    fix l r
    assume lr: "(l,r) \<in> S"
    assume "\<not> is_Fun l"
    then obtain x where "l = Var x" by auto
    from S[OF lr[unfolded this]]
    obtain Y l r where lr: "(l,r) \<in> R" and x: "Var x = str Y l" by auto
    have "l = Var x"
    proof (cases l)
      case (Var y)
      with x show ?thesis by simp
    next
      case (Fun f ts)
      from x[unfolded this] show ?thesis
        by (cases ts, simp, cases "tl ts", auto)
    qed
    from lr[unfolded this] have "\<not> SN (rstep R)"
      by (rule lhs_var_imp_rstep_not_SN)
    with SN have False by simp
  }
  with wf have wfS: "wf_trs S" unfolding wf_trs_def by force
  define c where "c = ((\<lambda> x. (Var undefined)) :: ('f,'v)term \<Rightarrow> ('f,'v)term)"
  define const where "const = (Var undefined :: ('f,'v)term)"
  interpret cleaning_const U c const 
    by (unfold_locales, auto simp: c_def const_def)
  from not_SN_imp_ichain_rstep[OF wfS nSN, of False False id]
  obtain s t \<sigma> where chain: "ichain (False, False, DP id S, {}, {}, {}, S) s t \<sigma>" by blast
  let ?sig  = "\<lambda> i. (clean_subst (\<sigma> i))"
  have "funas_trs (DP id S) \<subseteq> funas_trs S"
    using funas_DP_on_subset[of id _ S] by auto
  with S_U have DS_U: "funas_trs (DP id S) \<subseteq> U" by auto
  have "funas_dpp (False, False, DP id S, {}, {}, {}, S) \<subseteq> U" using DS_U S_U by auto
  from ichain_imp_clean_ichain[OF this chain]
  have "ichain (False, False, DP id S, {}, {}, {}, S) s t ?sig" .
  note ichain = this[unfolded ichain.simps, simplified]
  from ichain have st: "\<And> i. (s i, t i) \<in> DP id S"
    and tsi: "\<And> i. (t i \<cdot> ?sig i, s (Suc i) \<cdot> ?sig (Suc i)) \<in> (rstep S)^*" by auto
  let ?DPR = "DP_simple id UNIV R"
  interpret DP: max_unary_reverse NU d d' MU ?DPR "DP id S"
  proof
    from funas_DP_simple_subset[of id UNIV R] R show "funas_trs ?DPR \<subseteq> MU" by auto
  next
    fix sl st
    assume sst: "(sl, st) \<in> DP id S" 
    with wf_trs_imp_wf_DP_on [OF wfS, of id]
    show "vars_term st \<subseteq> vars_term sl" unfolding wf_trs_def by auto
    from sst[unfolded DP_on_def sharp_term_id] obtain 
      sr h us where st: "st = Fun h us" and slr: "(sl, sr) \<in> S" and sr: "sr \<unrhd> Fun h us" 
      by blast
    let ?f = "(h, length us)"
    from S[OF slr] obtain Y l r where lr: "(l,r) \<in> R" and id: "sl = str Y l" "sr = str Y r" by auto   
    from R lr have rlMU: "funas_term r \<subseteq> MU" "funas_term l \<subseteq> MU" by (force simp: funas_trs_def funas_rule_def)+
    from sr obtain C where sr: "sr = C \<langle> st \<rangle>" unfolding st by auto
    from rlMU(1) this[unfolded id] have "\<exists> D t. st = str Y t \<and> r = D \<langle> t \<rangle>" 
    proof (induct C arbitrary: r)
      case Hole
      show ?case
        by (intro exI[of _ Hole] exI[of _ r], insert Hole, auto)
    next
      case (More f bef C aft r)
      from More(2-3) obtain g rs where r: "r = Fun g rs" by (induct r, auto)
      from More(2) r MU[of g "length rs"] have "length rs \<le> 1" by auto
      show ?case
      proof (cases rs)
        case Nil
        with r have r: "r = Fun g []" by auto
        with More(3) have ba: "bef = []" "aft = []" by (cases bef, auto, cases aft, auto)
        from More(3)[unfolded r ba] have *: "C\<langle>st\<rangle> = Var Y" by auto
        then have "st = Var Y" by (cases C, auto)
        with st show ?thesis by auto
      next
        case (Cons r' rrs)
        with \<open>length rs \<le> 1\<close> r have r: "r = Fun g [r']" by auto
        from More(3)[unfolded r] have ba: "g = f" "bef = []" "aft = []" by (auto, cases bef, auto, cases aft, auto)
        from More(3)[unfolded r ba] have id: "str Y r' = C\<langle>st\<rangle>" by simp
        from More(2) r have "funas_term r' \<subseteq> MU" by auto
        from More(1)[OF this id] obtain D t where *: "st = str Y t \<and> r' = D\<langle>t\<rangle>" by auto
        show ?thesis
          by (rule exI[of _ "More f [] D []"], rule exI[of _ t], insert * r ba, auto)
      qed
    qed
    then obtain D t where idt: "st = str Y t" and "r = D \<langle> t \<rangle>" by auto
    with rlMU have rt: "r \<unrhd> t" and tMU: "funas_term t \<subseteq> MU" by auto
    from tMU idt obtain h' ts' where t: "t = Fun h' ts'" unfolding st by (induct, auto)
    have lt: "(l,t) \<in> ?DPR" unfolding DP_simple_def sharp_term_id
    proof (rule, unfold split, intro exI conjI)
      show "(l,r) \<in> R" by fact
      show "t = Fun h' ts'" by fact
      show "r \<unrhd> Fun h' ts'" using rt t by simp
    qed auto
    show "\<exists>Y l r. (l, r) \<in> ?DPR \<and> (sl, st) = (str Y l, str Y r)" unfolding id idt
      by (intro exI, rule conjI[OF lt refl])
  qed
  define ss where "ss = (\<lambda> i. term (s i \<cdot> ?sig i))"
  define ts where "ts = (\<lambda> i. term (t i \<cdot> ?sig i))"
  let ?P = "\<lambda> l r \<tau> i. ss i = l \<cdot> \<tau> \<and> ts i = r \<cdot> \<tau> \<and> (l,r) \<in> ?DPR"
  {
    fix i
    from DS_U st[of i] have sU: "funas_term (s i) \<subseteq> U" and tU: "funas_term (t i) \<subseteq> U"
      by (force simp: funas_trs_def funas_rule_def)+
    from sU have sU: "funas_term (s i \<cdot> ?sig i) \<subseteq> U" by (metis clean_subst_apply_term funas_term_clean_term)
    from tU have tU: "funas_term (t i \<cdot> ?sig i) \<subseteq> U" by (metis clean_subst_apply_term funas_term_clean_term)
    from simulation_S_rsteps[OF tU tsi] have tsi: "(ts i, ss (Suc i)) \<in> (rstep R)^*" unfolding ss_def ts_def .
    from DP.simulation_S_rrstep[OF sU rrstepI[OF st refl refl]] have st: "(ss i, ts i) \<in> rrstep ?DPR" unfolding ss_def ts_def .
    from this[unfolded rrstep_def'] have "\<exists> l r \<tau>. ?P l r \<tau> i" by force    
    note this tsi
  } note main = this
  then have "\<forall> i. \<exists> l r \<tau>. ?P l r \<tau> i" by blast
  from choice[OF this] obtain l where "\<forall> i. \<exists> r \<tau>. ?P (l i) r \<tau> i" by blast
  from choice[OF this] obtain r where "\<forall> i. \<exists> \<tau>. ?P (l i) (r i) \<tau> i" by blast
  from choice[OF this] obtain \<tau> where st: "\<And> i. ?P (l i) (r i) (\<tau> i) i" by blast
  have chain: "ichain (False, False, ?DPR, {}, {}, {}, R) l r \<tau>"
    using st main(2) by (auto simp: ichain.simps)
  from SN have "SN (qrstep False {} R)" by simp
  from SN_imp_finite_dpp_simple[OF this, of id UNIV id]
  have "finite_dpp (False, False, ?DPR, {}, {}, {}, R)" by simp
  with chain show False unfolding finite_dpp_def by simp
qed    
end

text \<open>Termination is preserved in both directions:\<close>
thm 
  max_unary_reverse.SN_R_imp_SN_S[unfolded max_unary_reverse_def max_unary_reverse_axioms_def]
  max_unary.SN_S_imp_SN_R

text \<open>For relative termination only one direction holds.\<close>
text \<open>The counterexample is R = f(x) -> a and S = b -> f(b).\<close>
thm
  max_unary.SN_rel_S_Sw_imp_SN_rel_R_Rw

end
