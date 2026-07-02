(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  Guillaume Allais (2011)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory RPO_More
  imports
  Weighted_Path_Order.RPO
  Efficient_Weighted_Path_Order.RPO_Unbounded
  Term_Order_Impl
  Knuth_Bendix_Order.Lexicographic_Extension
  Reduction_Order_Impl
  First_Order_Rewriting.Term_Impl
  Reduction_Pair
  Polynomial_Factorization.Missing_Multiset
  Show.Shows_Literal \<comment> \<open>For having strings in showsl class\<close>
  "HOL-Cardinals.Wellorder_Extension"  
begin

(* The strict order implies the non strict one *)
lemma rpo_stri_imp_nstri[rule_format]: "fst (rpo pr prl c n s t) \<longrightarrow>
  snd (rpo pr prl c n s t)"
proof (induct rule: rpo.induct[of _ pr prl c n])
  case (4 f ss g ts)
  obtain s ns where  prc: "pr (f,length ss) (g,length ts) = (s,ns)" by force
  show ?case
    by (cases "length ss = length ts \<or> length ts \<le> n", auto simp: Let_def lex_ext_stri_imp_nstri
      mul_ext_stri_imp_nstri prc)
qed (auto simp: Let_def)

context rpo_with_assms
begin
(* Reflexivity of the non strict order *)

lemma rpo_nstri_refl: 
  shows "snd (rpo_pr s s)"
  unfolding rpo_eq_wpo by (rule wpo_ns_refl)

(* Compatibility of the subterm relation with the order relation:
    a strict subterm is stricly smaller *)
lemma supt_imp_rpo_stri: assumes "s \<rhd> t" 
  shows "fst (rpo_pr s t)"
  using supt_subset_RPO_S assms by auto

(* Compatibility of the subterm relation with the order relation:
    a subterm is smaller *)
lemma supteq_imp_rpo_nstri: assumes supteq: "s \<unrhd> t" shows "snd (rpo_pr s t)" 
  using supteq_subset_RPO_NS assms by auto

(* Monotonicity of the non-strict order with respect
    to (fun x \<rightarrow> Fun f (bef @ x # aft)) *)
lemma rpo_nstri_mono: assumes rel: "snd (rpo_pr s t)"
  shows "snd (rpo_pr (Fun f (bef @ s # aft)) (Fun f (bef @ t # aft)))"
  using RPO_NS_ctxt assms by blast

(* Monotonicity of the strict order with respect
    to (fun x \<rightarrow> Fun f (bef @ x # aft)) *)
lemma rpo_stri_mono: 
  assumes rel: "fst (rpo_pr s t)"
  shows "fst (rpo_pr (Fun f (bef @ s # aft)) (Fun f (bef @ t # aft)))"
  using RPO_S_ctxt assms by blast

(* Stability of the orders *)
lemma rpo_stable: fixes \<sigma> :: "('f,'v)subst"
  shows "(fst (rpo_pr s t) \<longrightarrow> fst (rpo_pr (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))) \<and> (snd (rpo_pr s t) \<longrightarrow> snd (rpo_pr (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)))"
  using RPO_S_subst RPO_NS_subst by blast

(* Least element *)

lemma rpo_least_1: assumes "prl (f,0)" 
  shows "snd (rpo_pr t (Fun f []))" 
  unfolding rpo_eq_wpo using wpo_least_1[of f Nil t] assms by auto 

(* Transitivity / compatibility of the orders *)
lemma rpo_compat[rule_format]: 
  fixes s t u :: "('f,'v)term"
  shows "
  (snd (rpo_pr s t) \<and> fst (rpo_pr t u) \<longrightarrow> fst (rpo_pr s u)) \<and>
  (fst (rpo_pr s t) \<and> snd (rpo_pr t u) \<longrightarrow> fst (rpo_pr s u)) \<and>
  (snd (rpo_pr s t) \<and> snd (rpo_pr t u) \<longrightarrow> snd (rpo_pr s u))"
  by (metis (full_types) rpo_eq_wpo wpo_compat)

(* Transitivity of the strict order *)

lemma rpo_trans:
  assumes one: "fst (rpo_pr s t)"
  and two: "fst (rpo_pr t u)"
  shows "fst (rpo_pr s u)"
using assms rpo_compat rpo_stri_imp_nstri[OF one] by blast

(* large_symbol implies orientation *)
lemma rpo_large_sym:
  assumes prec: "\<And> g. g \<in> funas_term t \<Longrightarrow> prc (f,length ss) g = (True,True)"
  and vars: "vars_term t \<subseteq> vars_term (Fun f ss)"
  shows "rpo_pr (Fun f ss) t = (True,True)"
  using assms
proof (induct t)
  case (Var x)
  then have "x \<in> vars_term (Fun f ss)" by simp
  from supteq_Var[OF this] 
  have"Fun f ss \<rhd> Var x" unfolding subterm.le_less by simp
  from supt_imp_rpo_stri[OF this] have "fst (rpo_pr (Fun f ss) (Var x))" .
  with rpo_stri_imp_nstri[OF this] show ?case by (cases "rpo_pr (Fun f ss) (Var x)", auto)
next
  case (Fun g ts)
  from Fun(2) have prec: "prc (f,length ss) (g,length ts) = (True,True)" by simp
  { 
    fix t
    assume t: "t \<in> set ts"
    from t Fun(3) have v: "vars_term t \<subseteq> vars_term (Fun f ss)" by auto
    from t Fun(2) have p: "\<And> g . g \<in> funas_term t \<Longrightarrow> prc (f,length ss) g = (True,True)"
      by auto
    from Fun(1)[OF t p v] have "rpo_pr (Fun f ss) t = (True,True)" .
  }
  then show ?case
    by (simp add: prec)
qed

context
  fixes F :: "('f \<times> nat) set"
  assumes pr_gtotal: "\<And>f g. f \<in> F \<Longrightarrow> g \<in> F \<Longrightarrow> f = g \<or> fst (prc f g) \<or> fst (prc g f)"
    and lpo: "\<And> f. f \<in> F \<Longrightarrow> c f = Lex" 
begin

lemma lpo_ground_total:
  assumes "funas_term s \<subseteq> F" and "ground s" and "funas_term t \<subseteq> F" and "ground t"
  shows "s = t \<or> fst (rpo_pr s t) \<or> fst (rpo_pr t s)"
  using assms
proof (induct "size s + size t" arbitrary: s t rule: nat_less_induct)
  case (1 s t)
  note IH = 1(1)[rule_format, OF _ refl]
  note gs = 1(2-3)
  note gt = 1(4-5)
  from 1 obtain f ss where s: "s = Fun f ss" by (cases s, auto)
  from 1 obtain g ts where t: "t = Fun g ts" by (cases t, auto)
  let ?f = "(f,length ss)" 
  let ?g = "(g,length ts)"
  let ?s = "Fun f ss"
  let ?t = "Fun g ts" 
  let ?S = "\<lambda> s t. fst (rpo_pr s t)" 
  let ?NS = "\<lambda> s t. snd (rpo_pr s t)" 
  {
    assume contra: "\<not> ?case"
    {
      fix si
      assume si: "si \<in> set ss" 
      from si gs have gsi: "funas_term si \<subseteq> F" "ground si" unfolding s by auto
      from si have "size si + size t < size s + size t" unfolding s by (auto simp: size_simps)
      from IH[OF this gsi gt] have "(si = t \<or> ?S si t) \<or> ?S t si" by simp
      then have "?S t si" 
      proof
        assume "si = t \<or> ?S si t"
        then have "?NS si t" using rpo_nstri_refl rpo_stri_imp_nstri by blast
        moreover have "?S s si" using supt_imp_rpo_stri[of s si] unfolding s using si by auto
        ultimately have "?S s t" using rpo_compat by auto
        with contra show "?S t si" by simp
      qed simp
    }
    then have tsi: "(\<forall> si \<in> set ss. ?S ?t si) = True" unfolding t by auto
    {
      fix ti
      assume ti: "ti \<in> set ts" 
      from ti gt have gti: "funas_term ti \<subseteq> F" "ground ti" unfolding t by auto
      from ti have "size s + size ti < size s + size t" unfolding t by (auto simp: size_simps)
      from IH[OF this gs gti] have "(ti = s \<or> ?S ti s) \<or> ?S s ti" by auto
      then have "?S s ti" 
      proof
        assume "ti = s \<or> ?S ti s"
        then have "?NS ti s" using rpo_nstri_refl rpo_stri_imp_nstri by blast
        moreover have "?S t ti" using supt_imp_rpo_stri[of t ti] unfolding t using ti by auto
        ultimately have "?S t s" using rpo_compat by auto
        with contra show "?S s ti" by simp
      qed simp
    }
    then have sti: "(\<forall> ti \<in> set ts. ?S ?s ti) = True" unfolding s by auto
    from gs gt have f: "?f \<in> F" and g: "?g \<in> F" unfolding s t by auto
    note lpo = lpo[OF f] lpo[OF g]
    note contra = contra[unfolded s t rpo.simps tsi sti fst_conv lpo, simplified]
    from pr_gtotal[OF f g] contra prc_stri_imp_nstri[of ?f ?g] prc_stri_imp_nstri[of ?g ?f] 
    have fg: "?f = ?g" 
      by (cases "prc ?f ?g", cases "prc ?g ?f", auto split: prod.splits if_splits)
    then have fg': "f = g" "length ss = length ts" by auto
    note contra = contra[unfolded fg' prc_refl Let_def split]
    {
      fix si ti
      assume "(si, ti) \<in> set (zip ss ts)" 
      from in_set_zipE[OF this]
      have si: "si \<in> set ss" and ti: "ti \<in> set ts" by auto
      then have "size si + size ti < size si + size t" unfolding s t by (auto simp: size_simps)
      also have "\<dots> < size s + size t" unfolding s t using si by (auto simp: size_simps)
      finally have size: "size si + size ti < size s + size t" by simp
      from ti gt have gti: "funas_term ti \<subseteq> F" "ground ti" unfolding t by auto
      from si gs have gsi: "funas_term si \<subseteq> F" "ground si" unfolding s by auto
      from IH[OF size gsi gti]
      have "si = ti \<or> ?S si ti \<or> ?S ti si" .
    }         
    then have IH: "(\<forall>(s, t)\<in>set (zip ss ts). s = t \<or> ?S s t \<or> ?S t s)" by auto
    from contra have "\<not> fst (lex_ext rpo_pr n ss ts)"
       "\<not> fst (lex_ext rpo_pr n ts ss)" by (auto split: if_splits)
    with lex_ext_total[of ss ts rpo_pr, OF IH rpo_nstri_refl fg'(2)] 
    have "ss = ts" by auto
    with fg contra have False by auto
  } 
  then show ?case by blast
qed 
end


(* Definition: corresponding relations *)
definition RPO_S_pr where "RPO_S_pr = {(s,t) . fst (rpo_pr s t)}"
definition RPO_NS_pr where "RPO_NS_pr = {(s,t). snd (rpo_pr s t)}"

lemma RPO_NS_subt: assumes st: "s \<unrhd> t"
  shows "(s,t) \<in> RPO_NS_pr"  
  using supteq_imp_rpo_nstri[OF st]
  unfolding RPO_NS_pr_def by blast


(* introduction rules w.r.t. inference rules *)
lemma RPO_subt: "s \<in> set ss \<Longrightarrow> (s,t) \<in> RPO_NS_pr \<Longrightarrow> (Fun f ss,t) \<in> RPO_S_pr"
  unfolding RPO_S_pr_def RPO_NS_pr_def by (cases t, auto simp: Let_def)

lemma RPO_prec: "\<lbrakk>\<And> t. t \<in> set ts \<Longrightarrow> (Fun f ss, t) \<in> RPO_S_pr\<rbrakk> \<Longrightarrow> 
  fst (prc (f,length ss) (g,length ts)) \<Longrightarrow> (Fun f ss, Fun g ts) \<in> RPO_S_pr"
  unfolding RPO_S_pr_def 
  using prc_stri_imp_nstri[of "(f,length ss)" "(g,length ts)"]
  by (cases "prc (f,length ss) (g,length ts)", auto)

lemma RPO_refl: "(s,s) \<in> RPO_NS_pr"
  unfolding RPO_NS_pr_def 
  by (simp add: rpo_nstri_refl)

lemma RPO_stri: "(s,t) \<in> RPO_S_pr \<Longrightarrow> (s,t) \<in> RPO_NS_pr" 
  unfolding RPO_S_pr_def RPO_NS_pr_def 
  using rpo_stri_imp_nstri by auto

lemma RPO_least_1: "prl (g,0) \<Longrightarrow> (t, Fun g []) \<in> RPO_NS_pr" 
  unfolding RPO_NS_pr_def using rpo_least_1 by blast

lemma RPO_S_mul: assumes ms: "(mset ss, mset ts) \<in> s_mul_ext RPO_NS_pr RPO_S_pr"
  and prc: "snd (prc (f,length ss) (g,length ts))"
  and fmul: "c (f,length ss) = Mul"
  and gmul: "c (g,length ts) = Mul"
  shows "(Fun f ss, Fun g ts) \<in> RPO_S_pr"
  unfolding RPO_S_pr_def
proof (rule, unfold split)
  let ?n = "length ss"
  let ?m = "length ts"
  let ?f = "(f,?n)"
  let ?g = "(g,?m)"
  from prc obtain b where prc: "prc ?f ?g = (b,True)" by (cases "prc ?f ?g", auto)
  from ms have ms': "fst (mul_ext rpo_pr ss ts)"
    unfolding mul_ext_def Let_def RPO_NS_pr_def RPO_S_pr_def by simp
  from ms
  obtain as bs A' B' where 
    id: "mset ss = mset as + A'"
    "mset ts = mset bs + B'"
    and len: "length as = length bs"
    and as: "\<And> i. i < length bs \<Longrightarrow> (as ! i, bs ! i) \<in> RPO_NS_pr"
    and A': "\<And> b. b \<in># B' \<Longrightarrow> \<exists> a. a \<in># A' \<and> (a,b) \<in> RPO_S_pr"
    by (auto simp: s_mul_ext_def mult2_alt_s_def elim: multpw_listE)
  {
    fix t
    assume "t \<in> set ts"
    then have "t \<in># mset ts" unfolding in_multiset_in_set .
    then have "t \<in># mset bs \<or> t \<in># B'" unfolding id by simp
    then have "\<exists> s. s \<in># mset as + A' \<and> (s,t) \<in> RPO_NS_pr"
    proof
      assume "t \<in># B'"
      from A'[OF this] obtain s where A': "s \<in># A'" and S: "(s,t) \<in> RPO_S_pr"
        by blast
      from RPO_stri[OF S] A' show ?thesis by auto
    next
      assume "t \<in># mset bs"
      then have "t \<in> set bs" unfolding in_multiset_in_set .
      from this[unfolded set_conv_nth] obtain i where t: "t = bs ! i"
        and i: "i < length bs" by auto
      from as[OF i] have NS: "(as ! i, t) \<in> RPO_NS_pr" unfolding t .
      from i len have "as ! i \<in># mset as" 
        unfolding in_multiset_in_set set_conv_nth by auto
      with NS show ?thesis by auto
    qed
    then obtain s where s: "s \<in> set ss" and NS: "(s,t) \<in> RPO_NS_pr"
      unfolding in_multiset_in_set id[symmetric] by blast
    from RPO_subt[OF this] have "(Fun f ss, t) \<in> RPO_S_pr" .
  }
  then show "fst (rpo_pr (Fun f ss) (Fun g ts))"
    unfolding RPO_S_pr_def
    by (auto simp: fmul gmul prc ms')
qed

lemma RPO_NS_mul: assumes ms: "(mset ss, mset ts) \<in> ns_mul_ext RPO_NS_pr RPO_S_pr"
  and prc: "snd (prc (f,length ss) (g,length ts))"
  and fmul: "c (f,length ss) = Mul"
  and gmul: "c (g,length ts) = Mul"
  shows "(Fun f ss, Fun g ts) \<in> RPO_NS_pr"
  unfolding RPO_NS_pr_def
proof (rule, unfold split)
  let ?n = "length ss"
  let ?m = "length ts"
  let ?f = "(f,?n)"
  let ?g = "(g,?m)"
  from prc obtain b where prc: "prc ?f ?g = (b,True)" by (cases "prc ?f ?g", auto)
  from ms have ms': "snd (mul_ext rpo_pr ss ts)"
    unfolding mul_ext_def Let_def RPO_NS_pr_def RPO_S_pr_def by simp
  from ms
  obtain as bs A' B' where 
    id: "mset ss = mset as + A'"
    "mset ts = mset bs + B'"
    and len: "length as = length bs"
    and as: "\<And> i. i < length bs \<Longrightarrow> (as ! i, bs ! i) \<in> RPO_NS_pr"
    and A': "\<And> b. b \<in># B' \<Longrightarrow> \<exists> a. a \<in># A' \<and> (a,b) \<in> RPO_S_pr"
    by (auto simp: ns_mul_ext_def mult2_alt_ns_def elim: multpw_listE)
  {
    fix t
    assume "t \<in> set ts"
    then have "t \<in># mset ts" unfolding in_multiset_in_set .
    then have "t \<in># mset bs \<or> t \<in># B'" unfolding id by simp
    then have "\<exists> s. s \<in># mset as + A' \<and> (s,t) \<in> RPO_NS_pr"
    proof
      assume "t \<in># B'"
      from A'[OF this] obtain s where A': "s \<in># A'" and S: "(s,t) \<in> RPO_S_pr"
        by blast
      from RPO_stri[OF S] A' show ?thesis by auto
    next
      assume "t \<in># mset bs"
      then have "t \<in> set bs" unfolding in_multiset_in_set .
      from this[unfolded set_conv_nth] obtain i where t: "t = bs ! i"
        and i: "i < length bs" by auto
      from as[OF i] have NS: "(as ! i, t) \<in> RPO_NS_pr" unfolding t .
      from i len have "as ! i \<in># mset as" 
        unfolding in_multiset_in_set set_conv_nth by auto
      with NS show ?thesis by auto
    qed
    then obtain s where s: "s \<in> set ss" and NS: "(s,t) \<in> RPO_NS_pr"
      unfolding in_multiset_in_set id[symmetric] by blast
    from RPO_subt[OF this] have "(Fun f ss, t) \<in> RPO_S_pr" .
  }
  then show "snd (rpo_pr (Fun f ss) (Fun g ts))"
    unfolding RPO_S_pr_def
    by (auto simp: fmul gmul prc ms')
qed

lemma RPO_lex: 
  defines lexext: "lexext \<equiv> lex_ext (\<lambda> a b. ((a,b) \<in> RPO_S_pr,(a,b) \<in> RPO_NS_pr)) n"
  assumes lex: "fst (lexext ss ts)"
  and prc: "snd (prc (f,length ss) (g,length ts))"
  and ts: "\<And> t. t \<in> set ts \<Longrightarrow> (Fun f ss,t) \<in> RPO_S_pr"
  and fmul: "c (f,length ss) = Lex"
  and gmul: "c (g,length ts) = Lex"
  shows "(Fun f ss, Fun g ts) \<in> RPO_S_pr"
  unfolding RPO_S_pr_def
proof (rule, unfold split)
  let ?n = "length ss"
  let ?m = "length ts"
  let ?f = "(f,?n)"
  let ?g = "(g,?m)"
  from prc obtain b where prc: "prc ?f ?g = (b,True)" by (cases "prc ?f ?g", auto)
  note lex = lex[unfolded lexext RPO_NS_pr_def RPO_S_pr_def] 
  with ts[unfolded RPO_S_pr_def]
  show "fst (rpo_pr (Fun f ss) (Fun g ts))"
    unfolding RPO_S_pr_def
    by (auto simp: fmul gmul prc)
qed

lemma RPO_NS_lex: 
  defines lexext: "lexext \<equiv> lex_ext (\<lambda> a b. ((a,b) \<in> RPO_S_pr,(a,b) \<in> RPO_NS_pr)) n"
  assumes lex: "snd (lexext ss ts)"
  and prc: "snd (prc (f,length ss) (g,length ts))"
  and ts: "\<And> t. t \<in> set ts \<Longrightarrow> (Fun f ss,t) \<in> RPO_S_pr"
  and fmul: "c (f,length ss) = Lex"
  and gmul: "c (g,length ts) = Lex"
  shows "(Fun f ss, Fun g ts) \<in> RPO_NS_pr"
  unfolding RPO_NS_pr_def
proof (rule, unfold split)
  let ?n = "length ss"
  let ?m = "length ts"
  let ?f = "(f,?n)"
  let ?g = "(g,?m)"
  from prc obtain b where prc: "prc ?f ?g = (b,True)" by (cases "prc ?f ?g", auto)
  note lex = lex[unfolded lexext RPO_NS_pr_def RPO_S_pr_def] 
  with ts[unfolded RPO_S_pr_def]
  show "snd (rpo_pr (Fun f ss) (Fun g ts))"
    unfolding RPO_S_pr_def
    by (auto simp: fmul gmul prc)
qed


(* desired properties of RPO *)
lemma RPO_NS_refl: "refl (RPO_NS_pr)"
unfolding refl_on_def RPO_NS_pr_def
 by (simp add: rpo_nstri_refl)

lemma RPO_NS_trans: "trans RPO_NS_pr"
unfolding trans_def RPO_NS_pr_def 
using rpo_compat by blast

lemma RPO_S_trans: "trans RPO_S_pr"
unfolding trans_def RPO_S_pr_def 
using rpo_trans by blast

lemma RPO_compat: "RPO_NS_pr O RPO_S_pr \<subseteq> RPO_S_pr"
  using rpo_compat
  by (unfold RPO_S_pr_def RPO_NS_pr_def, auto)

lemma RPO_S_pr_ctxt_closed: "ctxt.closed RPO_S_pr"
  by (rule one_imp_ctxt_closed, unfold RPO_S_pr_def, insert rpo_stri_mono, blast)


(* Strong Normalisation *)

lemma RPO_S_SN: "SN RPO_S_pr"
  unfolding rpo_eq_wpo RPO_S_pr_def by (rule WPO_S_SN)
end

(* rpo as reduction pairs *)

sublocale rpo_with_assms \<subseteq> rpo_redpair: mono_ce_af_redtriple "RPO_S_pr" "RPO_NS_pr" "RPO_NS_pr" full_af
proof (unfold_locales)
  show "SN RPO_S_pr" by (rule rule RPO_S_SN)
  show "subst.closed RPO_NS_pr" unfolding RPO_NS_pr_def
    by (standard, rule RPO_NS_subst)
  show "subst.closed RPO_S_pr" unfolding RPO_S_pr_def
    by (standard, rule RPO_S_subst)
  show "ctxt.closed RPO_NS_pr"
    by (rule one_imp_ctxt_closed, unfold RPO_NS_pr_def, insert rpo_nstri_mono, blast)
  show "ce_compatible RPO_NS_pr"
    unfolding ce_compatible_def
  proof (intro exI allI impI)
    fix m c
    show "ce_trs (c,m) \<subseteq> RPO_NS_pr"
      unfolding RPO_NS_pr_def 
      by (simp add: ce_trs.simps, auto simp: size_simps rpo_stri_imp_nstri[OF supt_imp_rpo_stri])
  qed
  show "ce_compatible RPO_S_pr"
    unfolding ce_compatible_def
  proof (intro exI allI impI)
    fix m c
    show "ce_trs (c,m) \<subseteq> RPO_S_pr"
      unfolding RPO_S_pr_def 
      by (simp add: ce_trs.simps, auto simp: size_simps supt_imp_rpo_stri)
  qed
  show "RPO_S_pr O RPO_NS_pr \<subseteq> RPO_S_pr"
    unfolding RPO_S_pr_def RPO_NS_pr_def using rpo_compat by auto
  show "RPO_S_pr \<subseteq> RPO_NS_pr" using rpo_stri_imp_nstri 
    unfolding RPO_S_pr_def RPO_NS_pr_def by blast
  show "ctxt.closed RPO_S_pr" by (rule RPO_S_pr_ctxt_closed)
qed (rule RPO_compat, rule full_af)

sublocale rpo_with_assms \<subseteq> rpo_redpair: redtriple_order "RPO_S_pr" "RPO_NS_pr" "RPO_NS_pr" 
  by (unfold_locales, insert RPO_NS_refl RPO_NS_trans RPO_S_trans, auto)

context rpo_with_assms
begin

lemma rpo_manna_ness: assumes "\<And> l r. (l,r) \<in> R \<Longrightarrow> fst (rpo_pr l r)"
  shows "SN (rstep R)"
  by (rule rpo_redpair.manna_ness, insert assms, unfold RPO_S_pr_def, auto)

sublocale reduction_order "\<lambda> s t. fst (rpo_pr s t)" 
proof
  let ?SS = "\<lambda> s t. fst (rpo_pr s t)" 
  fix s t u :: "('f,'a)term" and \<sigma> :: "('f,'a) subst" and C
  show "?SS s t \<Longrightarrow> ?SS t u \<Longrightarrow> ?SS s u" by (rule rpo_trans)
  show "?SS s t \<Longrightarrow> ?SS (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)" using rpo_stable by auto
  show "?SS s t \<Longrightarrow> ?SS  C\<langle>s\<rangle> C\<langle>t\<rangle>" 
    using ctxt.closedD[OF RPO_S_pr_ctxt_closed, unfolded RPO_S_pr_def] by auto
  show "SN {(x, y). ?SS x y}" using RPO_S_SN unfolding RPO_S_pr_def .
qed
end

definition
  rpo_strict 
where
  "rpo_strict pr \<tau> n \<equiv> \<lambda>(s, t). check (fst (rpo (prc_nat pr) (prl_nat pr) \<tau> n s t)) 
    (showsl (STR ''could not orient '') \<circ> showsl s \<circ> showsl (STR '' >RPO '') \<circ> showsl t \<circ> showsl_nl)"

definition
  rpo_nstrict
where
  "rpo_nstrict pr \<tau> n \<equiv> \<lambda> (s,t). check (snd (rpo (prc_nat pr) (prl_nat pr) \<tau> n s t)) 
    (showsl (STR ''could not orient '') \<circ> showsl s \<circ> showsl (STR '' >=RPO '') \<circ> showsl t \<circ> showsl_nl)"

interpretation rpo_pr_prc: rpo_with_assms "prc_nat pr" "prl_nat pr" c n
  for "pr" :: "'f \<times> nat \<Rightarrow> nat" and c :: "'f \<times> nat \<Rightarrow> order_tag" and n :: nat ..

abbreviation RPO_S where "RPO_S pr \<tau> n \<equiv> rpo_with_assms.RPO_S_pr (prc_nat pr) (prl_nat pr) \<tau> n"
abbreviation RPO_NS where "RPO_NS pr \<tau> n \<equiv> rpo_with_assms.RPO_NS_pr (prc_nat pr) (prl_nat pr) \<tau> n"

lemma rpo_unbounded_stri_imp_nstri[rule_format]: "fst (rpo_unbounded pr c s t) \<longrightarrow>
  snd (rpo_unbounded pr c s t)"
proof (induct rule: rpo_unbounded.induct[of "\<lambda> pr c s t. fst (rpo_unbounded pr c s t) \<longrightarrow> snd (rpo_unbounded pr c s t)"])
  case (4 "pr" c f ss g ts)
  obtain prc prl where prec: "pr = (prc,prl)"  by (cases "pr", auto)
  obtain  s ns where  prc: "prc (f,length ss) (g,length ts) = (s,ns)" by force
  show ?case
    by (auto simp: Let_def lex_ext_unbounded_stri_imp_nstri
      mul_ext_stri_imp_nstri prec prc)
qed (auto simp: Let_def)

definition
  rpo_strict_unbounded
where
  "rpo_strict_unbounded pr c \<equiv> \<lambda>(s, t). check (fst (rpo_unbounded pr c s t)) 
    (showsl (STR ''could not orient '') \<circ> showsl s \<circ> showsl (STR '' >RPO '') \<circ> showsl t \<circ> showsl_nl)"

definition
  rpo_nstrict_unbounded
where
  "rpo_nstrict_unbounded pr c \<equiv> \<lambda>(s, t). check (snd (rpo_unbounded pr c s t)) 
    (showsl (STR ''could not orient '') \<circ> showsl s \<circ> showsl (STR '' >=RPO '') \<circ> showsl t \<circ> showsl_nl)"

type_synonym 'f status_prec_repr = "(('f \<times> nat) \<times> (nat \<times> order_tag))list"

fun showsl_rpo_repr :: "('f :: showl) status_prec_repr \<Rightarrow> showsl"
where
  "showsl_rpo_repr prs =
    showsl (STR ''RPO with the following precedence\<newline>'') \<circ> foldr (\<lambda>((f, n), (pr, s)).
      showsl (STR ''precedence('') \<circ> showsl f \<circ> showsl (STR ''['') \<circ> showsl n \<circ> showsl (STR '']) = '') 
       \<circ> showsl pr \<circ> showsl_nl) prs \<circ>
  showsl (STR ''\<newline>precedence(_) = 0\<newline>and the following status\<newline>'') \<circ>
  foldr (\<lambda>((f, n), (pr, s)).
    showsl (STR ''status('') \<circ> showsl f \<circ> showsl (STR ''['') \<circ> showsl n \<circ> showsl (STR '']) = '') \<circ>
    showsl (case s of Mul \<Rightarrow> STR ''mul'' | Lex \<Rightarrow> STR ''lex'') \<circ> showsl_nl) prs \<circ>
  showsl (STR ''\<newline>status(_) = lex\<newline>'')"

definition create_RPO_rel_impl :: "(('f :: showl) status_prec_repr \<Rightarrow> ('g \<times> nat \<Rightarrow> nat) \<times> ('g \<times> nat \<Rightarrow> order_tag)) 
  \<Rightarrow> 'f status_prec_repr \<Rightarrow> ('g :: showl,'v :: showl)rel_impl"
where "create_RPO_rel_impl prec_repr_to_pr pr = (let (p,\<tau>) = prec_repr_to_pr pr;
   ns = rpo_nstrict_unbounded (pr_nat p) \<tau> in
  \<lparr> rel_impl.valid = succeed, 
    standard = succeed,
    desc = showsl_rpo_repr pr, 
    s = rpo_strict_unbounded (pr_nat p) \<tau>, 
    ns = ns, nst = ns, 
    af = full_af, 
    top_af = full_af,
    SN = succeed,
    subst_s = succeed,
    ce_compat = succeed,
    co_rewr = succeed,
    top_mono = succeed,
    top_refl = succeed,
    mono_af = full_af,
    mono = (\<lambda> _. succeed), 
    not_wst = Some [],
    not_sst = Some [],
    cpx = no_complexity_check\<rparr>)"

lemma create_RPO_rel_impl: "rel_impl (create_RPO_rel_impl prec_repr_to_pr pr\<tau> :: ('g :: showl,'v :: showl)rel_impl)" 
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 U)
  note [simp] = create_RPO_rel_impl_def Let_def
  let ?rp = "create_RPO_rel_impl prec_repr_to_pr pr\<tau> :: ('g,'v)rel_impl"
  let ?af = "rel_impl.af ?rp :: ('g af)"
  let ?af' = "rel_impl.mono_af ?rp :: ('g af)"
  let ?cpx = "rel_impl.cpx ?rp"
  let ?cpx' = "\<lambda> cm cc. isOK(?cpx cm cc)"
  let ?pr = "prec_repr_to_pr pr\<tau>"
  obtain "pr" \<tau> where id: "?pr = (pr,\<tau>)" by (cases ?pr, auto)
  note valid = 1(1)
  obtain n where n: "n = max_list (map snd (funas_trs_list U))" by auto
  {
    fix s t
    assume st: "(s,t) \<in> set U"
    have "\<forall> f i. (f,i) \<in> funas_term s \<union> funas_term t \<longrightarrow> i \<le> n"
    proof (intro allI impI)
      fix f i
      assume fi: "(f,i) \<in> funas_term s \<union> funas_term t"
      hence "i \<in> set (map snd (funas_trs_list U))" using st by (force simp: funas_trs_def funas_rule_def)
      from max_list[OF this] show "i \<le> n" unfolding n .
    qed
    then have "rpo_unbounded (pr_nat pr) \<tau> s t = rpo (prc_nat pr) (prl_nat pr) \<tau> n s t"
     by (rule rpo_to_rpo_unbounded[symmetric])
  } note main = this
  have mono: "mono_ce_af_redtriple_order (RPO_S pr \<tau> n) (RPO_NS pr \<tau> n) (RPO_NS pr \<tau> n) full_af" ..
  let ?S = "RPO_S pr \<tau> n :: ('g, 'v) term rel"
  let ?NS = "RPO_NS pr \<tau> n :: ('g, 'v) term rel"
  have ctxt: "ctxt.closed ?S"
    by (rule rpo_pr_prc.rpo_redpair.ctxt_S)
  have ce_af: "cpx_ce_af_redtriple_order ?S ?NS ?NS full_af full_af no_complexity" 
    by (unfold_locales, rule ctxt_closed_imp_af_monotone[OF ctxt])
  interpret cpx_ce_af_redtriple_order ?S ?NS ?NS full_af full_af no_complexity by fact
  show ?case
  proof (rule exI[of _ ?S], intro exI[of _ ?NS] conjI impI allI
      rpo_pr_prc.rpo_redpair.S_imp_NS
      rpo_pr_prc.rpo_redpair.ctxt_NS
      rpo_pr_prc.rpo_redpair.subst_S
      rpo_pr_prc.rpo_redpair.subst_NS
      rpo_pr_prc.rpo_redpair.SN
      rpo_pr_prc.rpo_redpair.compat_S_NS
      rpo_pr_prc.rpo_redpair.compat_NS_S
      rpo_pr_prc.rpo_redpair.NS_ce_compat
      rpo_pr_prc.rpo_redpair.S_ce_compat
      rpo_pr_prc.rpo_redpair.trans_NS
      rpo_pr_prc.rpo_redpair.trans_S
      rpo_pr_prc.rpo_redpair.refl_NS
      top_mono_same
      )

    {
      fix st
      assume inU: "st \<in> set U" 
      obtain s t where st: "st = (s,t)" by force
      note main = main[of s t, folded st, OF inU]
      note defs = create_RPO_rel_impl_def Let_def id split rel_impl.simps isOK_check
      show "isOK (rel_impl.s ?rp st) \<Longrightarrow> st \<in> ?S" 
        unfolding st unfolding defs rpo_strict_unbounded_def main rpo_pr_prc.RPO_S_pr_def by simp
      show "isOK (rel_impl.ns ?rp st) \<Longrightarrow> st \<in> ?NS" 
        unfolding st unfolding defs rpo_nstrict_unbounded_def main rpo_pr_prc.RPO_NS_pr_def by simp
      show "isOK (rel_impl.nst ?rp st) \<Longrightarrow> st \<in> ?NS" 
        unfolding st unfolding defs rpo_nstrict_unbounded_def main rpo_pr_prc.RPO_NS_pr_def by simp
    }
    show "ctxt.closed ?S" by fact
    from rpo_pr_prc.rpo_redpair.SN show "irrefl ?S" using irrefl_on_def by fastforce
    from co_rewrite_irrefl[OF this rpo_pr_prc.rpo_redpair.compat_NS_S] show "?NS \<inter> ?S^-1 = {}" .    
    show "af_compatible ?af ?NS" by (simp add: id full_af)
    show "af_monotone ?af' ?S" using ctxt_closed_imp_af_monotone[OF \<open>ctxt.closed ?S\<close>] by (simp add: id)
    have suptS: "supt \<subseteq> ?S" 
      by (simp add: rpo_pr_prc.RPO_S_pr_def rpo_pr_prc.supt_subset_RPO_S)
    hence suptNS: "supt \<subseteq> ?NS" using rpo_pr_prc.rpo_redpair.S_imp_NS[of pr] by auto
    show "not_subterm_rel_info ?NS (rel_impl.not_wst ?rp)" "not_subterm_rel_info ?S (rel_impl.not_sst ?rp)" 
      by (intro simple_impl_not_subterm_rel_info suptS suptNS)+
  qed (auto simp: id isOK_no_complexity full_af)
qed 

definition check_LPO_valid :: "('f :: showl \<times> nat \<Rightarrow> nat) \<Rightarrow> ('f \<times> nat) list \<Rightarrow> nat \<times> 'f \<times> _ \<times> showsl check" where
  "check_LPO_valid prec fs = (let 
   F = set fs;
   pr = (\<lambda> f g. if g \<in> F then if f \<in> F then (prec f > prec g, prec f > prec g \<or> f = g) else (True, True) else (False, f = g));
   n = max_list (map snd fs);
   fs_pr = map (\<lambda> f. (f, prec f)) fs;
   cs = map fst (filter (\<lambda> (fn,p). snd fn = 0 \<and> p = 0) fs_pr); \<comment> \<open>constants with precedence 0\<close>
   c = fst (if cs = [] then (if fs = [] then Code.abort (STR ''empty function symbol list in LPO'') (\<lambda> x. hd fs)
     else hd fs) else hd cs);
   prl = (\<lambda> f. f = (c,(0 :: nat)));
   valid = do {
       check (cs \<noteq> []) (showsl (STR ''did not find minimal constant, i.e., one with precedence 0''));
       check (distinct (map snd fs_pr)) (showsl (STR ''precedence is not distinct''))
    }
  in (n, c, (pr, prl), valid))" 

definition create_LPO_redorder :: "('f :: showl \<times> nat \<Rightarrow> nat) \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, string) redord"
  where "create_LPO_redorder prec fs = (let 
   (n, c, pr, valid) = check_LPO_valid prec fs;
   F = set fs;
   S = rpo (fst pr) (snd pr) (\<lambda> _. Lex) n
  in \<lparr> redord.valid = valid,
    redord.less = (\<lambda> s t. fst (S s t)),
    redord.min_const = c \<rparr>)" 

(* one might want to change prl as well *)
lemma rpo_prec_mono: assumes prc: "\<And> f g. fst (prc1 f g) \<Longrightarrow> fst (prc2 f g)"
    "\<And> f g. snd (prc1 f g) \<Longrightarrow> snd (prc2 f g)" 
shows "fst (rpo prc1 prl c n s t) \<Longrightarrow> fst (rpo prc2 prl c n s t)"  
  "snd (rpo prc1 prl c n s t) \<Longrightarrow> snd (rpo prc2 prl c n s t)"
proof (atomize(full), induct "size s + size t" arbitrary: s t rule: less_induct)
  case (less s t)
  let ?S1 = "\<lambda> s t. fst (rpo prc1 prl c n s t)" 
  let ?NS1 = "\<lambda> s t. snd (rpo prc1 prl c n s t)"
  let ?S2 = "\<lambda> s t. fst (rpo prc2 prl c n s t)" 
  let ?NS2 = "\<lambda> s t. snd (rpo prc2 prl c n s t)"
  show ?case 
  proof (cases s)
    case (Var x)
    then show ?thesis by (cases t, auto)
  next
    case s: (Fun f ss)
    then have "\<And> si. si \<in> set ss \<Longrightarrow> size si + size t < size s + size t" by (auto simp: size_simps)
    note IH_si_t = less[OF this]
    show ?thesis
    proof (cases t)
      case (Var y)
      then show ?thesis unfolding s using IH_si_t by (auto simp: Let_def)
    next
      case t: (Fun g ts)
      then have size: "\<And> ti. ti \<in> set ts \<Longrightarrow> size s + size ti < size s + size t" by (auto simp: size_simps)
      note IH_s_ti = less[OF this]
      {
        assume contra: "\<not> ?thesis" 
        with rpo_stri_imp_nstri
        have NS1: "?NS1 s t" and S2: "\<not> ?S2 s t" by blast+
        let ?f = "(f,length ss)" let ?g = "(g,length ts)"
        obtain prs1 prns1 where prc1: "prc1 ?f ?g = (prs1, prns1)" by force
        obtain prs2 prns2 where prc2: "prc2 ?f ?g = (prs2, prns2)" by force
        from S2[unfolded s t] IH_si_t have *: "(\<exists>si\<in>set ss. ?NS1 si (Fun g ts)) = False" 
          by (auto split: if_splits simp: t)
        note NS1 = NS1[unfolded s t rpo.simps this if_False fst_conv prc1 Let_def split]
        from NS1 IH_s_ti t s have prns1: prns1 and s_ti: "(\<forall>t\<in>set ts. ?S2 (Fun f ss) t) = True" 
          by (auto split: if_splits)
        from prc[of ?f ?g] prns1 prc1 prc2 have prns2: "prns2 = True" and prs1: "prs1 \<Longrightarrow> prs2" by auto
        note S2 = S2[unfolded s t rpo.simps s_ti prc2 Let_def fst_conv split s_ti prns2]
        from S2 prs1 have prs1: "prs1 = False" by (auto split: if_splits)
        note NS1 = NS1[unfolded prs1 if_False]
        {
          fix si ti
          assume mem: "si \<in> set ss" "ti \<in> set ts" 
          then have "size si < size s" unfolding s
            by (auto simp: size_simps)
          with size[OF mem(2)] have "size si + size ti < size s + size t" by auto
        }
        note IH = less[OF this]
        from lex_ext_unbounded_mono[of ss ts "rpo prc1 prl c n" "rpo prc2 prl c n"] 
          IH[unfolded set_conv_nth] 
        have lex: "(snd (lex_ext (rpo prc1 prl c n) n ss ts) \<longrightarrow> snd (lex_ext (rpo prc2 prl c n) n ss ts)) \<and>
          (fst (lex_ext (rpo prc1 prl c n) n ss ts) \<longrightarrow> fst (lex_ext (rpo prc2 prl c n) n ss ts))"
          unfolding lex_ext_def by (auto simp: Let_def)
        with NS1 S2 contra * s_ti prns2 s t prc1 prc2 prs1 
        have mul: "snd (mul_ext (rpo prc1 prl c n) ss ts) \<and> \<not> snd (mul_ext (rpo prc2 prl c n) ss ts) \<or>
          fst (mul_ext (rpo prc1 prl c n) ss ts) \<and> \<not> fst (mul_ext (rpo prc2 prl c n) ss ts)" 
          by (auto split: if_splits simp: Let_def)
        note d = mul_ext_def Let_def snd_conv fst_conv
        {
          assume ns: "snd (mul_ext (rpo prc1 prl c n) ss ts)" 
          have "snd (mul_ext (rpo prc2 prl c n) ss ts)" unfolding d
            by (rule ns_mul_ext_local_mono[OF _ _ ns[unfolded d]], insert IH, auto)
        } note ns = this
        {
          assume s: "fst (mul_ext (rpo prc1 prl c n) ss ts)" 
          have "fst (mul_ext (rpo prc2 prl c n) ss ts)" unfolding d
            by (rule s_mul_ext_local_mono[OF _ _ s[unfolded d]], insert IH, auto)
        } note s = this
        from mul ns s have False by auto
      }
      then show ?thesis by blast
    qed
  qed
qed

lemma create_LPO_redorder: "reduction_order_impl create_LPO_redorder"
proof (unfold_locales, intro conjI)
  fix prec and fs :: "('a \<times> nat)list"  
  let ?O = "create_LPO_redorder prec fs" 
  let ?S = "redord.less ?O" 
  let ?c = "redord.min_const ?O" 
  assume valid: "isOK (redord.valid ?O)" 
  obtain n c prc prl valid where *: "check_LPO_valid prec fs = (n, c, (prc,prl), valid)" 
    by (cases "check_LPO_valid prec fs", auto) 
  note lpo = create_LPO_redorder_def[of prec fs, unfolded * Let_def split]
  let ?SS = "\<lambda>s t :: ('a,string)term. fst (rpo prc prl (\<lambda>_. Lex) n s t)" 
  have less: "?S = ?SS" 
    unfolding lpo by auto
  from valid have valid: "valid = return ()" unfolding lpo by auto
  have c: "?c = c" unfolding lpo by simp
  note * = *[unfolded check_LPO_valid_def prc_nat_def Let_def prl_nat_def valid, simplified]
  let ?F = "set fs" 
  from * have prc: "prc = (\<lambda>f g. if g \<in> set fs then if f \<in> set fs then (prec g < prec f, prec g < prec f \<or> f = g) else (True, True)
          else (False, f = g))" 
    and prl: "prl = (\<lambda>f. f = (c,0))" by auto
  let ?fs_pr = "map (\<lambda>f. (f, prec f)) fs" 
  let ?prs = "\<lambda> f g. fst (prc f g)" 
  let ?prw = "\<lambda> f g. snd (prc f g)" 
  let ?cs = "[(fn, p)\<leftarrow> ?fs_pr . snd fn = 0 \<and> p = 0]" 
  define cs where "cs = ?cs" 
  from * have cc: "c = fst (hd (map fst cs))" by (auto split: if_splits simp: cs_def)
  from * have cs: "cs \<noteq> []" unfolding cs_def by auto
  then obtain rest ac pc where cs: "cs = ((c,ac),pc) # rest" unfolding cc by (cases cs, auto)
  from arg_cong[OF this, of set, unfolded cs_def] 
  have "((c, ac), pc) \<in> {x \<in> (\<lambda>f. (f, prec f)) ` set fs. case x of (fn, p) \<Rightarrow> snd fn = 0 \<and> p = 0}" 
    by auto
  then have p_c: "prec (c,0) = 0" and cF: "(c,0) \<in> ?F" by auto
  then show "(?c,0) \<in> ?F" unfolding c by auto
  from * valid
  have dist: "distinct (map snd ?fs_pr)" unfolding check_def by (auto split: if_splits)
  from this[unfolded distinct_map] have inj: "inj_on snd (set (map (\<lambda>f. (f, prec f)) fs))" ..
  {
    fix f g 
    assume "f \<in> ?F" "g \<in> ?F" "f \<noteq> g" 
    with inj_onD[OF inj, of "(f, prec f)" "(g, prec g)"] have "prec f \<noteq> prec g" by force
    then have "prec f > prec g \<or> prec g > prec f" by linarith
  }
  then have total: "\<And> f g. f \<in> ?F \<Longrightarrow> g \<in> ?F \<Longrightarrow> f = g \<or> prec f > prec g \<or> prec f < prec g" by auto
  then have total_prec_F: "\<And> f g. f \<in> ?F \<Longrightarrow> g \<in> ?F \<Longrightarrow> f = g \<or> ?prs f g \<or> ?prs g f" 
    unfolding prc by auto
  interpret rpo: rpo_with_assms prc prl "\<lambda> _. Lex" n
  proof
    show "SN {(f, g). fst (prc f g)}" unfolding SN_iff_wf
      by (rule wf_subset[OF wf_measures[of "[(\<lambda> f. if f \<in> ?F then 0 else 1), prec]"]],
        auto simp: prc)
    show "prl g \<Longrightarrow> snd (prc f g) = True" for f g using cF total[OF cF, of f] by (auto simp: prc prl p_c)
  qed (insert cF p_c, auto simp: prc prl split: if_splits)
  show "reduction_order (redord.less ?O)" unfolding less ..

  from rpo.lpo_ground_total[OF _ refl, of ?F, OF total_prec_F]
  show "\<forall>s t. fground ?F s \<and> fground ?F t \<longrightarrow> s = t \<or> ?S s t \<or> ?S t s" 
    unfolding less fground_def by auto
  (* now we have to prove that an extension of the precedence is possible such
     that the result is a ground-total order on all terms *)
  have id: "{(f, g). fst (prc f g)}\<inverse> = {(f, g). fst (prc g f)}" by auto
  from SN_imp_wf[OF rpo.prc_SN, unfolded id] have wf:"wf {(gm,fn). ?prs fn gm}" . 
  from wf total_well_order_extension obtain Pt where Pt:"{(gm,fn). ?prs fn gm} \<subseteq> Pt" and
    wo:"Well_order Pt" and univ:"Field Pt = (UNIV :: ('a \<times> nat) set)" by metis
  let ?psx = "\<lambda> (fn :: 'a \<times> nat) gm. (gm,fn) \<in> Pt - Id"
  let ?pwx = "\<lambda> fn gm. (gm,fn) \<in> Pt"
  from wo[unfolded well_order_on_def] have lin:"Linear_order Pt" and wf: "wf (Pt - Id)" by auto
  from Linear_order_in_diff_Id[OF lin] univ have ptotal:"\<And>fn gm. fn = gm \<or> ?psx fn gm \<or> ?psx gm fn" by blast
  from lin[unfolded linear_order_on_def partial_order_on_def preorder_on_def refl_on_def] univ
  have refl_Pt:"\<And>x. (x,x) \<in> Pt" and trans_Pt: "trans Pt" by blast+
  {
    fix f g 
    assume "(g,f) \<in> Pt" "(f,g) \<in> Pt" "f \<noteq> g" 
    then have "(g,g) \<in> (Pt - Id) O (Pt - Id)" by auto
    with wf have False by (meson wf_comp_self wf_not_refl)
  } note two_step = this
  interpret rpox: rpo_with_assms "\<lambda> f g. (?psx f g, ?pwx f g)" prl "\<lambda> _. Lex" n
  proof (unfold_locales, unfold fst_conv snd_conv)
    fix f g h :: "'a \<times> nat" 
    { fix s1 ns1 h s2 ns2 s ns
      assume "(?psx f g, ?pwx f g) = (s1, ns1)" 
         "(?psx g h, ?pwx g h) = (s2, ns2)" 
         "(?psx f h, ?pwx f h) = (s, ns)" 
      then have id: "s1 = ?psx f g" "ns1 = ?pwx f g" 
          "s2 = ?psx g h" "ns2 = ?pwx g h" 
          "s = ?psx f h" "ns = ?pwx f h" 
        by auto
      from two_step[of f g]
      show "(ns1 \<and> ns2 \<longrightarrow> ns) \<and> (ns1 \<and> s2 \<longrightarrow> s) \<and> (s1 \<and> ns2 \<longrightarrow> s)"
        using trans_Pt[unfolded trans_def, rule_format, of h g f] unfolding id
        by auto
    }
    have id: "{(f, g). (g, f) \<in> Pt - Id}\<inverse> = Pt - Id" by auto
    show "SN {(f, g). ?psx f g}" using wf unfolding SN_iff_wf id .
    {
      assume "prl g"
      with rpo.prl[OF this, of f] have "fst (prc f g) \<or> f = g" by (auto simp: prc)
      with Pt refl_Pt[of g]
      show "((g, f) \<in> Pt) = True" by auto
    }
    assume f: "prl f" and gf: "(g,f) \<in> Pt" 
    from f have fc: "f = (c,0)" unfolding prl by auto    
    show "prl g"
    proof (rule ccontr)
      assume "\<not> prl g" 
      then have gc: "g \<noteq> (c,0)" unfolding prl by auto
      then have "?prs g (c,0)" using total_prec_F[of g, OF _ cF] p_c cF unfolding prc by auto
      with Pt fc have "(f, g) \<in> Pt" by auto
      from two_step[OF this gf] gc fc
      show False by auto
    qed
  qed (auto simp: refl_Pt)
  let ?SX = "\<lambda>s t :: ('a,string)term. fst (rpox.rpo_pr s t)" 
  let ?WX = "\<lambda>s t :: ('a,string)term. snd (rpox.rpo_pr s t)" 
  have gt: "ground s \<Longrightarrow> ground t \<Longrightarrow> s = t \<or> ?SX s t \<or> ?SX t s" 
      for s t 
    by (rule rpox.lpo_ground_total[of UNIV], insert ptotal, auto)
  have fU[simp]:"\<And>t. fground UNIV t = ground t" unfolding fground_def by auto
  have gto: "gtotal_reduction_order ?SX" 
    by (unfold_locales, unfold fU, rule gt, auto)
  show "\<exists>gt. gtotal_reduction_order gt \<and> (\<forall>s t. ?S s t \<longrightarrow> gt s t) \<and> 
     (\<forall>t. ground t \<longrightarrow> gt\<^sup>=\<^sup>= t (Fun ?c []))" unfolding less c
  proof (intro exI conjI allI impI, rule gto)
    fix s t 
    {
      assume S: "?SS s t"
      show "?SX s t" 
      proof (rule rpo_prec_mono(1)[OF _ _ S], unfold fst_conv snd_conv)
        fix f g
        show "?prw f g \<Longrightarrow> (g,f) \<in> Pt" using Pt by (auto simp: prc refl_Pt split: if_splits)
        assume "?prs f g" then show "(g,f) \<in> Pt - Id" using Pt rpo.prc_refl[of g] 
          by (auto simp: prc refl_Pt split: if_splits)
      qed
    }
    assume t: "ground (t :: ('a,string)term)" 
    let ?ct = "Fun c [] :: ('a,string)term" 
    have "ground ?ct" by auto
    from gt[OF t this] have "?SX\<^sup>=\<^sup>= t ?ct \<or> ?SX ?ct t" by auto
    then show "?SX\<^sup>=\<^sup>= t ?ct"
    proof
      assume S: "?SX ?ct t" 
      from rpox.rpo_least_1[of _ t] have "?WX t ?ct" unfolding prl by auto
      with rpox.rpo_compat S have "?SX t t" by blast
      with rpox.irrefl 
      show "?SX\<^sup>=\<^sup>= t ?ct" by blast
    qed
  qed
qed

end