(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Term_Order_Impl
imports 
  Term_Order
  Certification_Monads.Check_Monad
  Show.Shows_Literal
begin
 
record ('f, 'v) rel_impl =
  valid :: "showsl check"
  standard :: "showsl check" 
  desc :: showsl
  s :: "('f, 'v) rule \<Rightarrow> showsl check"
  ns :: "('f, 'v) rule \<Rightarrow> showsl check"
  nst :: "('f, 'v) rule \<Rightarrow> showsl check"
  af :: "'f af"
  top_af :: "'f af"
  SN :: "showsl check" 
  subst_s :: "showsl check" 
  ce_compat :: "showsl check" 
  co_rewr :: "showsl check" 
  top_mono :: "showsl check" 
  top_refl :: "showsl check" 
  mono_af :: "'f af"
  mono :: "('f \<times> nat) list \<Rightarrow> showsl check"
  not_wst :: "('f \<times> nat) list option"
  not_sst :: "('f \<times> nat) list option"
  cpx :: "('f, 'v) complexity_measure \<Rightarrow> complexity_class \<Rightarrow> showsl check"

hide_const (open) valid standard desc s ns nst af top_af SN subst_s 
  ce_compat co_rewr top_mono mono_af mono not_wst not_sst cpx 

definition rel_impl_s :: "('f,'v)rel_impl \<Rightarrow> _ \<Rightarrow> _" where
  "rel_impl_s ri = check_allm (rel_impl.s ri)" 

definition rel_impl_ns :: "('f,'v)rel_impl \<Rightarrow> _ \<Rightarrow> _" where
  "rel_impl_ns ri = check_allm (rel_impl.ns ri)" 

definition rel_impl_nst :: "('f,'v)rel_impl \<Rightarrow> _ \<Rightarrow> _" where
  "rel_impl_nst ri = check_allm (rel_impl.nst ri)" 

lemmas rel_impl_list = rel_impl_s_def rel_impl_ns_def rel_impl_nst_def

fun not_subterm_rel_info :: "('f,'v)trs \<Rightarrow> ('f \<times> nat)list option \<Rightarrow> bool" where
  "not_subterm_rel_info rel None = True"
| "not_subterm_rel_info rel (Some ws) =  (\<forall> f i. f \<notin> set ws \<longrightarrow> simple_arg_pos rel f i)"

lemma simple_impl_not_subterm_rel_info: assumes "supt \<subseteq> rel"
  shows "not_subterm_rel_info rel anything" 
proof (cases anything)
  case (Some ws)
  show ?thesis unfolding Some not_subterm_rel_info.simps
  proof (intro allI impI)
    fix fn i
    show "simple_arg_pos rel fn i" 
    proof (cases fn)
      case fn: (Pair f n)
      show ?thesis unfolding fn
      proof (intro simple_arg_posI)
        fix ts
        show  "length ts = n \<Longrightarrow> i < n \<Longrightarrow> (Fun f ts, ts ! i) \<in> rel" 
          by (intro set_mp[OF assms], simp)
      qed
    qed
  qed
qed auto


abbreviation rel_impl_prop :: "('f,'v)rel_impl \<Rightarrow> ('f,'v)rule list \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "rel_impl_prop impl U S NS NST \<equiv>
       (\<forall> st. st \<in> set U \<longrightarrow> (
            (isOK(rel_impl.s impl st) \<longrightarrow> st \<in> S) \<and> 
            (isOK(rel_impl.ns impl st) \<longrightarrow> st \<in> NS) \<and> 
            (isOK(rel_impl.nst impl st) \<longrightarrow> st \<in> NST)))
  
       \<comment> \<open>unconditional properties\<close>
       \<and> irrefl S 
       \<and> ctxt.closed NS 
       \<and> subst.closed NS       
       \<and> trans NS 
       \<and> refl NS 
       \<and> af_compatible (rel_impl.af impl) NS
       \<and> af_compatible (rel_impl.top_af impl) NST
       \<and> af_monotone (rel_impl.mono_af impl) S
       \<and> not_subterm_rel_info NS (rel_impl.not_wst impl) 
       \<and> not_subterm_rel_info S (rel_impl.not_sst impl)
       \<comment> \<open>properties that can be tested via flags\<close>
       \<and> (isOK(rel_impl.standard impl) \<longrightarrow> trans S \<and> S \<subseteq> NS \<and> S O NS \<subseteq> S \<and> NS O S \<subseteq> S)
       \<and> (isOK(rel_impl.top_mono impl) \<or> isOK(rel_impl.standard impl) \<longrightarrow> trans S \<and> subst.closed NST \<and> trans NST \<and> NST O S \<subseteq> S \<and> S O NST \<subseteq> S)
       \<and> (\<forall> sig. funas_trs (set U) \<subseteq> set sig \<longrightarrow> isOK(rel_impl.mono impl sig) \<longrightarrow> ctxt.closed S)
       \<and> (isOK(rel_impl.top_mono impl) \<longrightarrow> top_mono NS NST)
       \<and> (isOK(rel_impl.top_refl impl) \<longrightarrow> refl NST)
       \<and> (isOK(rel_impl.SN impl) \<longrightarrow> SN S)
       \<and> (isOK(rel_impl.subst_s impl) \<longrightarrow> subst.closed S)
       \<and> (isOK(rel_impl.ce_compat impl) \<longrightarrow> ce_compatible NS)
       \<and> (\<forall> sig. funas_trs (set U) \<subseteq> set sig \<longrightarrow> isOK(rel_impl.ce_compat impl) \<longrightarrow> isOK(rel_impl.mono impl sig) \<longrightarrow> ce_compatible S)
       \<and> (isOK(rel_impl.co_rewr impl) \<longrightarrow> NS \<inter> S\<inverse> = {})
       \<and> (\<forall> cm cc. isOK(rel_impl.cpx impl cm cc) \<longrightarrow> deriv_bound_measure_class S cm cc)" 


definition rel_impl :: "('f,'v)rel_impl \<Rightarrow> bool" where
  "rel_impl impl = (isOK(rel_impl.valid impl) \<longrightarrow> (\<forall> U. \<exists> S NS NST. 
      rel_impl_prop impl U S NS NST))"

definition rel_impl_mono_redpair :: "('f,'v)rel_impl \<Rightarrow> ('f,'v)rule list \<Rightarrow> ('f,'v)rule list \<Rightarrow> showsl check" where
  "rel_impl_mono_redpair ri s ns = do {
      rel_impl.valid ri;
      rel_impl.standard ri;
      rel_impl.SN ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring strong normalization of relation''));
      rel_impl.subst_s ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring stability of strict relation''));
      rel_impl.mono ri (funas_trs_list (s @ ns)) <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring monotonicity of strict relation''))      
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a monotone reduction pair\<newline>'') \<circ> s)" 

lemma rel_impl_mono_redpair: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_mono_redpair ri s ns)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)" 
shows "\<exists> S NS NST. mono_redtriple_order S NS NST \<and> set s \<subseteq> S \<and> set ns \<subseteq> NS
   \<and> (isOK(rel_impl.cpx ri cm cc) \<longrightarrow> deriv_bound_measure_class S cm cc)" 
proof -
  from checks[unfolded rel_impl_mono_redpair_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and std: "isOK(rel_impl.standard ri)" 
    and sn: "isOK (rel_impl.SN ri)" 
    and mono: "isOK (rel_impl.mono ri (funas_trs_list (s @ ns)))" 
    and subst: "isOK (rel_impl.subst_s ri)" 
    by auto
  let ?U = "s @ ns" 
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient subst mono sn std
  have *: "set s \<subseteq> S" "set ns \<subseteq> NS" 
     "S \<subseteq> NS" 
     "ctxt.closed NS" "ctxt.closed S" 
     "subst.closed NS" "subst.closed S"
     "S O NS \<subseteq> S" "NS O S \<subseteq> S"
     "trans NS" 
     "refl NS" 
     "SN S"      
     "isOK (rel_impl.cpx ri cm cc) \<longrightarrow> deriv_bound_measure_class S cm cc" 
    by (auto simp: rel_impl_list)
  from \<open>S O NS \<subseteq> S\<close> \<open>S \<subseteq> NS\<close> have trans_S: "trans S" unfolding trans_def by auto
  show ?thesis
  proof (rule exI[of _ S], rule exI[of _ NS], rule exI[of _ Id], intro conjI *)
    show "mono_redtriple_order S NS Id" 
      by (unfold_locales; (intro trans_S *)?) (auto simp: trans_def refl_on_def)
  qed
qed

definition rel_impl_mono_ce_redpair :: "('f,'v)rel_impl \<Rightarrow> ('f,'v)rule list \<Rightarrow> ('f,'v)rule list \<Rightarrow> showsl check" where
  "rel_impl_mono_ce_redpair ri s ns = do {
      rel_impl.valid ri;
      rel_impl.standard ri;
      rel_impl.SN ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring strong normalization of relation''));
      rel_impl.subst_s ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring stability of strict relation''));
      rel_impl.ce_compat ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring ce-compatibility''));
      rel_impl.mono ri (funas_trs_list (s @ ns)) <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring monotonicity of strict relation''))      
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a ce-compatible monotone reduction pair\<newline>'') \<circ> s)" 

lemma rel_impl_mono_ce_redpair: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_mono_ce_redpair ri s ns)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)" 
shows "\<exists> S NS NST. mono_ce_af_redtriple_order S NS NST full_af \<and> set s \<subseteq> S \<and> set ns \<subseteq> NS" 
proof -
  let ?U = "s @ ns" 
  from checks[unfolded rel_impl_mono_ce_redpair_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and std: "isOK(rel_impl.standard ri)" 
    and sn: "isOK (rel_impl.SN ri)" 
    and mono: "isOK (rel_impl.mono ri (funas_trs_list ?U))" 
    and subst: "isOK (rel_impl.subst_s ri)" 
    and ce: "isOK(rel_impl.ce_compat ri)" 
    by auto
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient subst mono sn ce std
  have *: "set s \<subseteq> S" "set ns \<subseteq> NS" 
     "S \<subseteq> NS" 
     "ctxt.closed NS" "ctxt.closed S" 
     "subst.closed NS" "subst.closed S"
     "S O NS \<subseteq> S" "NS O S \<subseteq> S"
     "trans NS" 
     "refl NS" 
     "SN S"      
     "ce_compatible NS" "ce_compatible S" 
    by (auto simp: rel_impl_list)
  from \<open>S O NS \<subseteq> S\<close> \<open>S \<subseteq> NS\<close> have trans_S: "trans S" unfolding trans_def by auto
  show ?thesis
  proof (rule exI[of _ S], rule exI[of _ NS], rule exI[of _ Id], intro conjI *)
    show "mono_ce_af_redtriple_order S NS Id full_af" 
      by (unfold_locales; (intro trans_S full_af *)?) (auto simp: trans_def refl_on_def)
  qed
qed


definition rel_impl_redpair :: "('f,'v)rel_impl \<Rightarrow> showsl check" where
  "rel_impl_redpair ri = do {
      rel_impl.valid ri;
      rel_impl.standard ri;
      rel_impl.SN ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring strong normalization of relation''));
      rel_impl.subst_s ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring stability of strict relation''))
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a reduction pair\<newline>'') \<circ> s)" 


lemma rel_impl_redpair: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_redpair ri)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)"  
shows "\<exists> S NS. compat_redpair_order S NS \<and> set s \<subseteq> S \<and> set ns \<subseteq> NS 
   \<and> af_monotone (rel_impl.mono_af ri) S \<and> af_compatible (rel_impl.af ri) NS
   \<and> (isOK(rel_impl.cpx ri cm cc) \<longrightarrow> deriv_bound_measure_class S cm cc)
   \<and> (isOK(rel_impl.ce_compat ri) \<longrightarrow> ce_compatible NS)" 
proof -
  from checks[unfolded rel_impl_redpair_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and std: "isOK(rel_impl.standard ri)" 
    and sn: "isOK (rel_impl.SN ri)" 
    and subst: "isOK (rel_impl.subst_s ri)" 
    by auto
  let ?U = "s @ ns" 
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient subst sn std
  have *: "set s \<subseteq> S" "set ns \<subseteq> NS" 
     "S \<subseteq> NS" 
     "ctxt.closed NS" 
     "trans NS" 
     "refl NS" 
     "af_monotone (rel_impl.mono_af ri) S" 
     "af_compatible (rel_impl.af ri) NS" 
     "subst.closed NS" "subst.closed S"
     "S O NS \<subseteq> S" "NS O S \<subseteq> S"
     "SN S" 
     "isOK (rel_impl.cpx ri cm cc) \<longrightarrow> deriv_bound_measure_class S cm cc" 
     "isOK (rel_impl.ce_compat ri) \<longrightarrow> ce_compatible NS" 
    by (auto simp: rel_impl_list)
  from \<open>S O NS \<subseteq> S\<close> \<open>S \<subseteq> NS\<close> have trans_S: "trans S" unfolding trans_def by auto
  show ?thesis
  proof (rule exI[of _ S], rule exI[of _ NS], intro conjI *)
    show "compat_redpair_order S NS" 
      by (unfold_locales; (intro * trans_S)?) 
  qed
qed

definition rel_impl_redtriple :: "('f,'v)rel_impl \<Rightarrow> showsl check" where
  "rel_impl_redtriple ri = do {
      rel_impl.valid ri;
      rel_impl.standard ri;
      rel_impl.top_refl ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring reflexivity of top-non-strict relation''));
      rel_impl.SN ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring strong normalization of relation''));
      rel_impl.subst_s ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring stability of strict relation''))
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a reduction triple\<newline>'') \<circ> s)" 

lemma rel_impl_redtriple: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_redtriple ri)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)" "isOK(rel_impl_nst ri nst)" 
shows "\<exists> S NS NST. af_redtriple_order S NS NST (rel_impl.af ri)
   \<and> set s \<subseteq> S \<and> set ns \<subseteq> NS \<and> set nst \<subseteq> NST   
   \<and> (isOK(rel_impl.ce_compat ri) \<longrightarrow> ce_compatible NS)" 
proof -
  from checks[unfolded rel_impl_redtriple_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and std: "isOK(rel_impl.standard ri)" 
    and sn: "isOK (rel_impl.SN ri)" 
    and subst: "isOK (rel_impl.subst_s ri)" 
    and refl: "isOK(rel_impl.top_refl ri)" 
    by auto
  let ?U = "s @ ns @ nst" 
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient subst sn std refl
  have *: "set s \<subseteq> S" "set ns \<subseteq> NS" "set nst \<subseteq> NST" 
     "S \<subseteq> NS" 
     "ctxt.closed NS" 
     "trans NS" "trans NST" 
     "refl NS" "refl NST" 
     "af_monotone (rel_impl.mono_af ri) S" 
     "af_compatible (rel_impl.af ri) NS" 
     "subst.closed NS" "subst.closed S" "subst.closed NST" 
     "S O NS \<subseteq> S" "NS O S \<subseteq> S" "NST O S \<subseteq> S" 
     "SN S" 
     "isOK (rel_impl.ce_compat ri) \<longrightarrow> ce_compatible NS" 
    by (simp_all add: rel_impl_list) (metis subrelI)+
  from \<open>S O NS \<subseteq> S\<close> \<open>S \<subseteq> NS\<close> have trans_S: "trans S" unfolding trans_def by auto
  show ?thesis
  proof (rule exI[of _ S], rule exI[of _ NS], rule exI[of _ NST], intro conjI *)
    show "af_redtriple_order S NS NST (rel_impl.af ri)" 
      by (unfold_locales; (intro * trans_S)?) 
  qed
qed

definition rel_impl_root_redtriple :: "('f,'v)rel_impl \<Rightarrow> showsl check" where
  "rel_impl_root_redtriple ri = do {
      rel_impl.valid ri;
      rel_impl.SN ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring strong normalization of relation''));
      rel_impl.subst_s ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring stability of strict relation''));
      rel_impl.top_mono ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in monotonicity from non-root to root''))
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a root-reduction triple\<newline>'') \<circ> s)" 

lemma rel_impl_root_redtriple: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_root_redtriple ri)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)" "isOK(rel_impl_nst ri nst)" 
shows "\<exists> S NS NST. af_root_redtriple_order S NS NST (rel_impl.af ri) (rel_impl.top_af ri)
   \<and> set s \<subseteq> S \<and> set ns \<subseteq> NS \<and> set nst \<subseteq> NST   
   \<and> (isOK(rel_impl.ce_compat ri) \<longrightarrow> ce_compatible NS)" 
proof -
  from checks[unfolded rel_impl_root_redtriple_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and sn: "isOK (rel_impl.SN ri)" 
    and subst: "isOK (rel_impl.subst_s ri)" 
    and tm: "isOK (rel_impl.top_mono ri)" 
    by auto
  let ?U = "s @ ns @ nst" 
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient subst sn tm
  have *: "set s \<subseteq> S" "set ns \<subseteq> NS" "set nst \<subseteq> NST" 
     "ctxt.closed NS" 
     "trans S" "trans NS" "trans NST" 
     "refl NS"  
     "af_monotone (rel_impl.mono_af ri) S" 
     "af_compatible (rel_impl.af ri) NS"
     "af_compatible (rel_impl.top_af ri) NST"
     "subst.closed NS" "subst.closed S" "subst.closed NST" 
     "NST O S \<subseteq> S" 
     "SN S" 
     "isOK (rel_impl.ce_compat ri) \<longrightarrow> ce_compatible NS" 
     "top_mono NS NST" 
    by (simp_all add: rel_impl_list) (metis subrelI)+
  show ?thesis
  proof (rule exI[of _ S], rule exI[of _ NS], rule exI[of _ NST], intro conjI *)
    show "af_root_redtriple_order S NS NST (rel_impl.af ri) (rel_impl.top_af ri)" 
      by (unfold_locales; (intro *)?) 
  qed
qed

definition rel_impl_discr_pair :: "('f,'v)rel_impl \<Rightarrow> showsl check" where
  "rel_impl_discr_pair ri = do {
      rel_impl.valid ri;
      rel_impl.standard ri
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a discrimination pair\<newline>'') \<circ> s)" 


lemma rel_impl_discr_pair: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_discr_pair ri)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)"  
shows "\<exists> S NS. discrimination_pair S NS \<and> set s \<subseteq> S \<and> set ns \<subseteq> NS" 
proof -
  let ?U = "s @ ns" 
  from checks[unfolded rel_impl_discr_pair_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and std: "isOK(rel_impl.standard ri)" 
    by auto
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient std
  have *: "set s \<subseteq> S" "set ns \<subseteq> NS" 
     "S \<subseteq> NS" 
     "ctxt.closed NS" 
     "trans NS" 
     "refl NS" 
     "irrefl S" 
     "subst.closed NS" 
     "S O NS \<subseteq> S" "NS O S \<subseteq> S"
    by (simp_all add: rel_impl_list) (metis subrelI)+
  from \<open>S O NS \<subseteq> S\<close> \<open>S \<subseteq> NS\<close> have trans_S: "trans S" unfolding trans_def by auto
  show ?thesis
  proof (rule exI[of _ S], rule exI[of _ NS], intro conjI *)
    show "discrimination_pair S NS" 
      by (unfold_locales; (intro * trans_S)?) (insert \<open>irrefl S\<close>, auto simp: irrefl_def)
  qed
qed

definition rel_impl_co_rewrite_pair :: "('f,'v)rel_impl \<Rightarrow> showsl check" where
  "rel_impl_co_rewrite_pair ri = do {
      rel_impl.valid ri;
      rel_impl.co_rewr ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring disjointness property''));
      rel_impl.subst_s ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring stability of strict relation''))
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a co-rewrite pair\<newline>'') \<circ> s)" 

lemma rel_impl_co_rewrite_pair: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_co_rewrite_pair ri)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)"  
shows "\<exists> S NS. co_rewrite_pair S NS \<and> set s \<subseteq> S \<and> set ns \<subseteq> NS" 
proof -
  let ?U = "s @ ns" 
  from checks[unfolded rel_impl_co_rewrite_pair_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and subst: "isOK (rel_impl.subst_s ri)" 
    and co: "isOK (rel_impl.co_rewr ri)"  
    by auto
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient subst co have *: "set s \<subseteq> S" "set ns \<subseteq> NS" 
    "ctxt.closed NS" 
    "trans NS" 
    "refl NS" 
    "subst.closed NS" "subst.closed S" 
    "NS \<inter> S\<inverse> = {}" 
    by (simp_all add: rel_impl_list) (metis subrelI)+
  show ?thesis
  proof (rule exI[of _ S], rule exI[of _ NS], intro conjI *)
    show "co_rewrite_pair S NS" 
      by (unfold_locales; (intro *)?)
  qed
qed

definition rel_impl_co_discrimination_pair :: "('f,'v)rel_impl \<Rightarrow> showsl check" where
  "rel_impl_co_discrimination_pair ri = do {
      rel_impl.valid ri;
      rel_impl.co_rewr ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring disjointness property''))
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a co-discrimination pair\<newline>'') \<circ> s)" 

lemma rel_impl_co_discrimination_pair: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_co_discrimination_pair ri)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_ns ri ns)"  
shows "\<exists> S NS. co_discrimination_pair S NS \<and> set s \<subseteq> S \<and> set ns \<subseteq> NS" 
proof -
  let ?U = "s @ ns" 
  from checks[unfolded rel_impl_co_discrimination_pair_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and co: "isOK (rel_impl.co_rewr ri)"  
    by auto
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S NS NST
    where "rel_impl_prop ri ?U S NS NST" by presburger
  with orient subst co have *: "set s \<subseteq> S" "set ns \<subseteq> NS" 
    "ctxt.closed NS" 
    "trans NS" 
    "refl NS" 
    "subst.closed NS"  
    "NS \<inter> S\<inverse> = {}" 
    by (simp_all add: rel_impl_list) (metis subrelI)+
  show ?thesis
  proof (rule exI[of _ S], rule exI[of _ NS], intro conjI *)
    show "co_discrimination_pair S NS" 
      by (unfold_locales; (intro *)?)
  qed
qed

definition rel_impl_quasi_reduction_triple :: "('f,'v)rel_impl \<Rightarrow> showsl check" where
  "rel_impl_quasi_reduction_triple ri = do {
      rel_impl.valid ri;
      rel_impl.subst_s ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring stability of strict relation''));
      rel_impl.SN ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring strong normalization of strict relation''));
      rel_impl.top_mono ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring top-monotonicity of non-strict relations''));
      rel_impl.top_refl ri <+? (\<lambda> e. e o showsl_lit (STR ''\<newline>problem in ensuring top-reflexivity''))
    } <+? (\<lambda>s. showsl_lit (STR ''problem with being a quasi-reduction triple\<newline>'') \<circ> s)" 

lemma rel_impl_quasi_reduction_triple: assumes ri: "rel_impl ri" 
  and checks: "isOK(rel_impl_quasi_reduction_triple ri)"
  and orient: "isOK(rel_impl_s ri s)" "isOK(rel_impl_nst ri ns)" "isOK(rel_impl_ns ri h)"  
shows "\<exists> S NS H. 
    trans H \<and> refl H \<and> subst.closed H \<and> ctxt.closed H \<and> \<comment> \<open>H is a rewrite preorder\<close>
    trans NS \<and> refl NS \<and> subst.closed NS \<and> \<comment> \<open>NS is a stable quasi-order\<close>
    trans S \<and> irrefl S \<and> subst.closed S \<and> SN S \<and> \<comment> \<open>S is a stable well-founded order\<close>
    NS O S \<subseteq> S \<and> S O NS \<subseteq> S \<and> \<comment> \<open>S and NS forms an order-pair\<close>
    top_mono H NS \<and> \<comment> \<open>top-mono/harmony property\<close>
    set s \<subseteq> S \<and> set ns \<subseteq> NS \<and> set h \<subseteq> H" 
proof -
  let ?U = "s @ ns @ h" 
  from checks[unfolded rel_impl_quasi_reduction_triple_def, simplified]
  have valid: "isOK (rel_impl.valid ri)" 
    and subst: "isOK (rel_impl.subst_s ri)" 
    and tm: "isOK (rel_impl.top_mono ri)"
    and tr: "isOK (rel_impl.top_refl ri)"
    and sn: "isOK(rel_impl.SN ri)" 
    by auto
  from ri[unfolded rel_impl_def, rule_format, OF valid, of ?U] obtain S H NS
    where "rel_impl_prop ri ?U S H NS" by presburger
  with orient subst tm tr sn have *: "set s \<subseteq> S" "set ns \<subseteq> NS" "set h \<subseteq> H" 
    "trans H" "refl H" "subst.closed H" "ctxt.closed H"
    "trans NS" "refl NS" "subst.closed NS"
    "trans S" "irrefl S" "subst.closed S" "SN S"
    "NS O S \<subseteq> S" "S O NS \<subseteq> S"
    "top_mono H NS"
      by (simp_all add: rel_impl_list) (metis subrelI)+
  show ?thesis
    by (rule exI[of _ S], rule exI[of _ NS], rule exI[of _ H], intro conjI *)
qed

lemma co_rewrite_irrefl: assumes "irrefl S" and "NS O S \<subseteq> S" 
  shows "NS \<inter> S\<inverse> = {}" 
proof (rule ccontr)
  assume "\<not> ?thesis" 
  then obtain a b where "(a,b) \<in> NS" and "(b,a) \<in> S" by auto
  hence "(a,a) \<in> S" using assms(2) by auto
  with assms(1) show False unfolding irrefl_def by auto
qed

definition no_complexity where
  "no_complexity \<equiv> (\<lambda> _ _. False)"

definition no_complexity_check where
  "no_complexity_check \<equiv> (\<lambda> _ _. error (showsl (STR ''complexity analysis unsupported'')) :: showsl check)"

lemma isOK_no_complexity: "isOK(no_complexity_check cm cc) = False" 
  by (auto simp: no_complexity_check_def)

lemma no_complexity_check[simp]: "(\<lambda> cm cc. isOK(no_complexity_check cm cc)) = no_complexity"
  unfolding no_complexity_check_def no_complexity_def by auto

interpretation cpx_term_rel S no_complexity 
  by (unfold_locales) (auto simp: no_complexity_def)

definition faulty_rel_impl :: "'f itself \<Rightarrow> 'v itself \<Rightarrow> showsl \<Rightarrow> showsl \<Rightarrow> ('f, 'v)rel_impl"
  where
    "faulty_rel_impl _ _ err desc = \<lparr>
      rel_impl.valid = error err,
      standard = succeed,
      desc = desc,
      s = (\<lambda> _. succeed),
      ns = (\<lambda> _. succeed),
      nst = (\<lambda> _. succeed),
      af = full_af,
      top_af = full_af,
      SN = succeed,
      subst_s = succeed,
      ce_compat = succeed,
      co_rewr = succeed,
      top_mono = succeed,
      top_refl = succeed,
      mono_af = empty_af,
      mono = (\<lambda> _ . succeed),
      not_wst = None,
      not_sst = None,
      cpx = no_complexity_check
    \<rparr>"

lemma faulty_rel_impl[simp]: "\<not> isOK (rel_impl.valid (faulty_rel_impl a b c d))"
  unfolding faulty_rel_impl_def by simp

typedef ('f,'v,'rp) rel_impl_type = "{ ri :: 'rp \<Rightarrow> ('f,'v)rel_impl.
  \<forall> params. rel_impl (ri params) }" 
  by (intro exI[of _ "\<lambda> _. faulty_rel_impl TYPE('f) TYPE('v) undefined undefined"], 
      auto simp: faulty_rel_impl_def rel_impl_def)

setup_lifting type_definition_rel_impl_type

lift_definition rel_impl_of :: "('f,'v,'rp) rel_impl_type \<Rightarrow> 'rp \<Rightarrow> ('f,'v)rel_impl" is id .

lemma rel_impl_of: "rel_impl (rel_impl_of ri params)" 
  by (transfer, auto)

(* Precedences for natural numbers *)
definition prc_nat :: "('f \<times> nat \<Rightarrow> nat) \<Rightarrow> ('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool)"
  where "prc_nat pr \<equiv> \<lambda> f g. let pf = pr f; pg = pr g in (pg < pf, pg \<le> pf)"

definition prl_nat :: "('f \<times> nat \<Rightarrow> nat) \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
  where "prl_nat pr \<equiv> \<lambda> f. pr f = 0"

abbreviation pr_nat where "pr_nat pr \<equiv> (prc_nat pr, prl_nat pr)"

(* Precedences via natural numbers *)

lemma SN_pr_nat: "SN {(f,g). (pr :: 'f \<times> nat \<Rightarrow> nat) g < pr f}"
  by (rule HOL.subst[of _ _ SN, OF _ SN_inv_image[OF SN_nat_gt, of "pr"]],
  auto simp: inv_image_def)

interpretation precedence_nat: precedence "prc_nat pr" "prl_nat pr" 
  for "pr" :: "'f \<times> nat \<Rightarrow> nat" 
  by (unfold_locales, unfold prc_nat_def prl_nat_def Let_def, insert SN_pr_nat[of "pr"], auto)

\<comment> \<open>show function symbol together with arity\<close>
fun showsl_funa :: "('f::showl \<times> nat) \<Rightarrow> showsl"
  where
    "showsl_funa (f, n) = showsl f \<circ> showsl_lit (STR ''/'') \<circ> showsl n"

end

