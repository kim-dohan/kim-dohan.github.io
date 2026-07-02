(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Implementation of the Weak Dependency Pair Processor\<close>

theory WDP_Transformation_Impl
imports
  WDP_Transformation
  Framework.QDP_Framework_Impl
  TRS.Multihole_Context_Impl
begin

datatype ('f, 'v) wdp_trans_info = WDP_Trans_Info
  "'f sig" \<comment> \<open>compound symbols\<close>
  "(('f, 'v) rule \<times> ('f, 'v) rule) list" \<comment> \<open>strict rules and corresponding WDPs\<close>
  "(('f, 'v) rule \<times> ('f, 'v) rule) list" \<comment> \<open>weak rules and corresponding WDPs\<close>
  "('f, 'v) term list" \<comment> \<open>new Q-component\<close>

fun is_compound_context
where
  "is_compound_context CComp C \<longleftrightarrow> ground_mctxt C \<and> funas_mctxt C \<subseteq> CComp"

context
  fixes shp :: "'f \<Rightarrow> 'f:: showl"
begin

interpretation sharp_syntax .

definition
  check_rule_wdp ::
    "'f sig \<Rightarrow> ('f :: showl, 'v :: showl) rule \<times> ('f, 'v) rule \<Rightarrow> showsl check"
where
  "check_rule_wdp CComp = (\<lambda>((l, r), (p, q)). do {
    let l' = \<sharp> l;
    check (l' = p) (showsl_lit (STR ''wrong lhs, expected '') \<circ> showsl l' \<circ> showsl_lit (STR '' but got '') \<circ> showsl p);
    let us = uncap_till_funas (- CComp) r;
    let (C, us') = split_term_funas (- CComp) q;
    check (\<sharp> us = us')
      (showsl_lit (STR ''lists of maximal subterms with defined root differ''));
    check (is_compound_context CComp C)
      (showsl C \<circ> showsl_lit (STR '' is not a proper compound context of '') \<circ> showsl q)
  } <+? (\<lambda>e. showsl_lit (STR ''could not ensure that '') \<circ> showsl_rule (p, q) \<circ>
             showsl_lit (STR '' is a valid weak dependency pair for '') \<circ> showsl_rule (l, r) \<circ> showsl_nl \<circ> e))"

lemma check_rule_wdp:
  assumes "isOK (check_rule_wdp C (r, p))"
  shows "pre_wdps.is_WDP_of (\<sharp> :: 'f \<Rightarrow> 'f) C p r"
proof -
  interpret pre_wdps shp C .
  from assms obtain l u p' q
    where [simp]: "r = (l, u)" "p = (p', q)"
    and [simp]: "p' = \<sharp> l" and *: "dmax q = \<sharp>(dmax u)"
    and "ground_mctxt (ccap q)" (is "ground_mctxt ?C")
    and "funas_mctxt (ccap q) \<subseteq> C"
    by (cases r p rule: prod.exhaust [case_product prod.exhaust]) (auto simp: check_rule_wdp_def)
  then show ?thesis
    by (auto simp: is_WDP_of_def intro!: exI [of _ "?C"]) (metis * split_term_eqf)
qed

definition
  check_wdp_trans ::
    "('tp, 'f :: showl, 'v :: showl) tp_ops \<Rightarrow> ('f, 'v) wdp_trans_info \<Rightarrow>
    ('f, 'v) complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp \<Rightarrow>
    (('f, 'v) complexity_measure \<times> 'tp) result"
where
  "check_wdp_trans I info cm cc cp =
    (case info of 
      WDP_Trans_Info Comp s_wdps w_wdps Q' \<Rightarrow>
      (case cm of 
        Runtime_Complexity C' D' \<Rightarrow> (do {
        let S' = tp_ops.R I cp;
        let W' = tp_ops.Rw I cp;
        let S = map fst s_wdps;
        let W = map fst w_wdps;
        let R = S @ W;
        let fs = funas_trs_list R;
        let ds = defined_list R;
        check_allm (\<lambda>r. check (\<exists>r' \<in> set S. r =\<^sub>v r')
          (showsl_lit (STR ''could not find weak dependency pair for strict rule '') \<circ> showsl r)) S';
        check_allm (\<lambda>r. check (\<exists>r' \<in> set W. r =\<^sub>v r')
          (showsl_lit (STR ''could not find weak dependency pair for weak rule '') \<circ> showsl r)) W';
        let WDP_S = map snd s_wdps;
        let WDP_W = map snd w_wdps;
        let shpf = (\<lambda>(f, n). (\<sharp> f, n));
        let F = fs @ C' @ D';
        let f_sharps = map shpf F;
        let Fs = \<sharp> (set F);
        let CComp = (set fs - set (defined_list R) - set D') \<union> Comp;
        check_allm (\<lambda>q. check (is_Fun q \<and> the (root q) \<notin> set F)
          (showsl_lit (STR ''new Q-term '') \<circ> showsl q \<circ> showsl_lit (STR '' not allowed''))) Q';
        check_wf_trs R;
        check_allm (\<lambda>f. check (f \<notin> CComp) (showsl f \<circ> showsl_lit (STR '' clashes with sharp symbols''))) f_sharps;
        check_allm (\<lambda>f. check (f \<notin> CComp) (showsl f \<circ> showsl_lit (STR '' clashes with defined symbols of RC''))) D';
        check_allm (\<lambda>f. check (f \<notin> CComp) (showsl f \<circ> showsl_lit (STR '' clashes with defined symbols''))) ds;
        check_allm (check_rule_wdp CComp) s_wdps;
        check_allm (check_rule_wdp CComp) w_wdps;
        return (Runtime_Complexity C' (map shpf D'),
          tp_ops.mk I (tp_ops.nfs I cp) (tp_ops.Q I cp @ Q') (WDP_S @ S) (WDP_W @ W))
      })
    | Derivational_Complexity _ \<Rightarrow>  
      error (showsl_lit (STR ''only runtime complexity supported for weak dependency pairs''))))
      <+? (\<lambda>e. showsl_lit (STR ''error when switching to weak dependency pairs'') \<circ> showsl_nl \<circ> e)"

lemma wdp_trans:
  assumes "tp_spec I"
  and res: "check_wdp_trans I info cm cc tp = return (cm', tp')"
  and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm' cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  obtain Comp and s_wdps and w_wdps and Q'
    where info: "info = WDP_Trans_Info Comp s_wdps w_wdps Q'" by (cases info) auto
  note res = res [unfolded check_wdp_trans_def info]
  interpret tp_spec I by fact
  from res obtain C' D' where cm: "cm = Runtime_Complexity C' D'" by (cases cm) (simp, blast)
  let ?S' = "set (R tp)"
  let ?W' = "set (Rw tp)"
  let ?S = "fst ` set s_wdps"
  let ?W = "fst ` set w_wdps"
  let ?R = "?S \<union> ?W"
  let ?nfs = "NFS tp"
  let ?D = "Collect (defined ?R)"
  let ?shp = "\<lambda>(f, n). (shp f, n)"
  let ?Ds = "?shp ` ?D \<union> ?D"
  let ?D'' = "map ?shp D'"
  let ?Q = "set (Q tp)"
  let ?Q' = "?Q \<union> set Q'"
  let ?WDP_S = "snd ` set s_wdps"
  let ?WDP_W = "snd ` set w_wdps"
  let ?F = "funas_trs ?R \<union> set C' \<union> set D'"
  let ?Fs = "?shp ` ?F"
  let ?C = "funas_trs ?R - ?D - set D'"
  let ?Cs = "?C \<union> Comp"
  let ?NF = "NF_terms ((fst \<circ> fst) ` set s_wdps \<union> (fst \<circ> fst) ` set w_wdps)"
  note res = res[unfolded cm Let_def, simplified]
  have wf: "wf_trs ?R" and
    D': "set D' \<inter> ?Cs = {}" and
    C_fresh: "(?D \<union> ?Fs) \<inter> ?Cs = {}" and
    tp': "tp' = mk ?nfs (Q tp @ Q') (map snd s_wdps @ map fst s_wdps) (map snd w_wdps @ map fst w_wdps)" and
    cm': "cm' = Runtime_Complexity C' ?D''" and
    S: "(\<forall>x\<in> ?S'. \<exists> lr \<in> ?S. x =\<^sub>v lr)" and 
    W: "(\<forall>x\<in> ?W'. \<exists> lr \<in> ?W. x =\<^sub>v lr)" and 
    check_S: "(\<forall>x\<in>set s_wdps. isOK (check_rule_wdp ?Cs x))" and
    check_W: "(\<forall>x\<in>set w_wdps. isOK (check_rule_wdp ?Cs x))"
    using res by (auto simp: cm Let_def) (*TODO: speed up*)
  interpret wdps ?Cs shp ?F ?R ?Q ?Q'
    by (unfold_locales) (force, rule C_fresh, rule wf, insert res, force)
  interpret sharp_syntax .
  have cpx: "deriv_bound_measure_class
    (relto (qrstep ?nfs ?Q' (?WDP_S \<union> ?S)) (qrstep ?nfs ?Q' (?WDP_W \<union> ?W)))
    (Runtime_Complexity C' ?D'') cc" using cpx by (simp add: cm' tp')
  have subset: "?S \<subseteq> ?R" "?W \<subseteq> ?R" by auto
  have "set C' \<union> set D' \<subseteq> ?F" "set ?D'' = \<sharp>(set D')" by force+
  note wdps = WDPs_sound [of ?S ?WDP_S ?W ?WDP_W ?nfs C' ?D'' cc D', OF _ _ subset cpx D' this]
  show ?thesis
    unfolding qreltrs_sound split cm
  proof (rule deriv_bound_measure_class_mono [OF relto_mono subset_refl subset_refl wdps])
    show "qrstep ?nfs ?Q ?S' \<subseteq> qrstep ?nfs ?Q ?S"
      by (rule qrstep_rename_vars, insert S, force)
  next
    show "qrstep ?nfs ?Q ?W' \<subseteq> qrstep ?nfs ?Q ?W"
      by (rule qrstep_rename_vars, insert W, force)
  next
    { fix r
      assume "r \<in> ?S"
      with S obtain p where *: "(r, p) \<in> set s_wdps" by auto
      then have "p \<in> ?WDP_S" by force
      with check_rule_wdp [OF check_S [rule_format, OF *]]
        have "\<exists>p \<in> ?WDP_S. is_WDP_of p r" by blast }
    then show "\<forall>r \<in> ?S. \<exists>p \<in> ?WDP_S. is_WDP_of p r" by auto
  next
    { fix r
      assume "r \<in> ?W"
      with W obtain p where *: "(r, p) \<in> set w_wdps" by auto
      then have "p \<in> ?WDP_W" by force
      with check_rule_wdp [OF check_W [rule_format, OF *]]
        have "\<exists>p \<in> ?WDP_W. is_WDP_of p r" by blast }
    then show "\<forall>r \<in> ?W. \<exists>p \<in> ?WDP_W. is_WDP_of p r" by auto
  qed
qed

end

end
