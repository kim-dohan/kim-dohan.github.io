(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_AC_Termination
imports 
  Check_Termination_Common
begin

subsection \<open>Proving finiteness in the AC-DP Framework\<close>

fun mk_tp where
  "mk_tp I (r, a, c) = ac_tp_ops.mk I r a c"

fun mk_dpp where
  "mk_dpp I (p, pw, r, rw, e) = ac_dpp_ops.mk I p pw r rw e"  

datatype (dead 'f, dead 'v) ac_dp_termination_proof =
  AC_P_is_Empty
| AC_Subterm_Proc "'f status_impl"
    "('f,'v) rules" (* removed pairs *)
    "('f, 'v) ac_dp_termination_proof" 
| AC_Redpair_UR_Proc "'f redtriple_impl"
    "('f,'v) rules" (* removed pairs *) 
    "('f,'v) rules" (* usable rules *)
    "('f, 'v) ac_dp_termination_proof" 
| AC_Mono_Redpair_UR_Proc "'f redtriple_impl"
    "('f,'v) rules" (* removed pairs *) 
    "('f,'v) rules" (* removed rules *) 
    "('f,'v) rules" (* usable rules *)
    "('f, 'v) ac_dp_termination_proof" 
| AC_Dep_Graph_Proc "(('f, 'v) ac_dp_termination_proof option \<times> ('f, 'v) rules) list"

datatype (dead 'f, dead 'l, dead 'v) ac_termination_proof = 
  AC_DP_Trans 
    "(('f, 'l) lab, 'v) ac_dependency_pairs_proof" 
    "(('f, 'l) lab, 'v) ac_dp_termination_proof" 
    "(('f, 'l) lab, 'v) ac_dp_termination_proof"
| AC_DP_Trans_Single
    "(('f, 'l) lab, 'v) ac_dependency_pairs_proof" 
    "(('f, 'l) lab, 'v) ac_dp_termination_proof"
| AC_Rule_Removal "('f,'l)lab redtriple_impl"
    "(('f,'l) lab,'v) rules" (* removed rules *) 
    "('f, 'l, 'v) ac_termination_proof" 
| AC_R_is_Empty


definition
  showsl_ac_dpp :: "('dpp, 'f :: showl, 'v :: showl) ac_dpp_ops \<Rightarrow> 'dpp \<Rightarrow> showsl"
where
  "showsl_ac_dpp I d = (let
    p  = ac_dpp_ops.P  I d;
    pw = ac_dpp_ops.Pw I d;
    r  = ac_dpp_ops.R  I d;
    rw = ac_dpp_ops.Rw I d;
    e  = ac_dpp_ops.E  I d
  in     
    (if p = [] then id else showsl_trs' showsl showsl (STR ''pairs:'') (STR '' -> '') p) o
    (if pw = [] then id else showsl_trs' showsl showsl (STR ''weak pairs:'') (STR '' ->= '') pw) o
    (if r  = [] then id else showsl_trs' showsl showsl (STR ''strict rules:'') (STR '' ->! '') r) o
    (if rw = [] then id else showsl_trs' showsl showsl (STR ''rules:'') (STR '' -> '') rw) o
    (if e = [] then id else showsl_trs' showsl showsl (STR ''equations:'') (STR '' -> '') e)
    )"

definition
  showsl_ac_tp :: "('tp, 'f :: showl, 'v :: showl) ac_tp_ops \<Rightarrow> 'tp \<Rightarrow> showsl"
where
  "showsl_ac_tp I t = (let
    r   = ac_tp_ops.R I t;
    a   = ac_tp_ops.A I t;
    c   = ac_tp_ops.C I t
  in
    showsl_trs' showsl showsl (STR ''rules:'') (STR '' -> '') r o
    (if a = [] then id else showsl_lit (STR ''A-symbols: '') o showsl a o showsl_nl) o
    (if c = [] then id else showsl_lit (STR ''C-symbols: '') o showsl c o showsl_nl))"

context 
  fixes I :: "('dpp, 'f :: {showl, compare_order}, string) ac_dpp_ops"
begin

function
  check_ac_dp_termination_proof ::
    "showsl \<Rightarrow> 'dpp \<Rightarrow>
    ('f, string) ac_dp_termination_proof \<Rightarrow>
    showsl check"
where
  "check_ac_dp_termination_proof i dpp AC_P_is_Empty = debug i (STR ''P is empty'') (
     ac_dpp_trivial_check I dpp 
       <+? (\<lambda> s. i o showsl_lit (STR ''problem in applying trivial check on\<newline>'') o showsl_ac_dpp I dpp o s)
   )"
| "check_ac_dp_termination_proof i dpp (AC_Redpair_UR_Proc redp del_p ur prf) = debug i (STR ''AC_Redpair_UR_Proc'') (do {
     dpp' \<leftarrow> ac_ur_redpair_proc I (get_rel_impl redp) del_p ur dpp
       <+? (\<lambda>s. i o showsl_lit (STR '': error when applying AC-reduction pair processor to DP problem\<newline>'') o
             showsl_ac_dpp I dpp o showsl_lit (STR ''\<newline>and trying to remove pairs\<newline>'') o showsl_rules del_p o showsl_nl o s);
     check_ac_dp_termination_proof (add_index i 1) dpp' prf
         <+? (\<lambda>s. i o showsl_lit (STR '': error below AC-reduction pair processor\<newline>'') o s)
   })" 
| "check_ac_dp_termination_proof i dpp (AC_Subterm_Proc pi del_p prf) = debug i (STR ''AC_Subterm_Proc'') (do {
     dpp' \<leftarrow> ac_subterm_proc I pi del_p dpp
       <+? (\<lambda>s. i o showsl_lit (STR '': error when applying AC-subterm criterion processor to DP problem\<newline>'') o
             showsl_ac_dpp I dpp o showsl_lit (STR ''\<newline>and trying to remove pairs\<newline>'') o showsl_rules del_p o showsl_nl o s);
     check_ac_dp_termination_proof (add_index i 1) dpp' prf
         <+? (\<lambda>s. i o showsl_lit (STR '': error below AC-reduction pair processor\<newline>'') o s)
   })" 
| "check_ac_dp_termination_proof i dpp (AC_Mono_Redpair_UR_Proc redp del_p del_r ur prf) = debug i (STR ''AC_Mono_Redpair_UR_Proc'') (do {
     dpp' \<leftarrow> ac_mono_ur_redpair_proc I (get_rel_impl redp) del_p del_r ur dpp
       <+? (\<lambda>s. i o showsl_lit (STR '': error when applying monotone AC-reduction pair processor to DP problem\<newline>'') o
             showsl_ac_dpp I dpp o showsl_lit (STR ''\<newline>and trying to remove pairs\<newline>'') o showsl_rules del_p o 
             showsl_lit (STR ''\<newline>and rules\<newline>'') o showsl_rules del_r o showsl_nl o s);
     check_ac_dp_termination_proof (add_index i 1) dpp' prf
         <+? (\<lambda>s. i o showsl_lit (STR '': error below monotone AC-reduction pair processor\<newline>'') o s)
   })" 
| "check_ac_dp_termination_proof i dpp (AC_Dep_Graph_Proc edpts) =
     debug i (STR ''Dep_Graph_Proc'') (do {
        pdpps \<leftarrow> ac_dep_graph_proc I dpp edpts
         <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error while trying to perform Sctxt_closure-decomposition  on\<newline>'') \<circ>
           showsl_ac_dpp I dpp \<circ> showsl_nl \<circ> s);
        check_allm_index (\<lambda> (prof,dpp') j. check_ac_dp_termination_proof (add_index i (Suc j)) dpp' prof) pdpps
          <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below the dependency graph processor\<newline>'') \<circ> s)
  })"
  by pat_completeness auto

termination
proof -
  let ?M = "(\<lambda> (i, dpp, prof) \<Rightarrow> size prof)"
  show ?thesis
  proof (standard, rule wf_measure[of ?M]; unfold update_error_return)
    fix i dpp
      and edpts :: "(('f, string) ac_dp_termination_proof option
        \<times> ('f, string) rules) list" 
      and pdpps pdpp i' prof dpp' j
    assume proc: "ac_dep_graph_proc I dpp edpts = Inr pdpps"
      and mem: "pdpp \<in> set pdpps" and pdpp: "(prof, dpp') = pdpp"
    show "((add_index i (Suc j), dpp', prof), 
      (i, dpp, AC_Dep_Graph_Proc edpts)) \<in> measure ?M" 
    proof -
      from proc mem [unfolded pdpp [symmetric]]
      have "Some prof \<in> set (map fst edpts)" unfolding ac_dep_graph_proc_def by force
      then obtain P where "(Some prof, P) \<in> set edpts" by auto
      then show ?thesis
        by (induct edpts, auto)
    qed 
  qed auto
qed



lemma check_ac_dp_termination_proof: assumes I: "ac_dpp_spec I"
  and ok: "isOK(check_ac_dp_termination_proof i dpp prf)"
  shows "finite_rel_dpp (ac_dpp_ops.ac_dpp I dpp)"
proof -
  interpret ac_dpp_spec I by fact
  from ok show ?thesis
  proof (induct "prf" arbitrary: i dpp)
    case (AC_P_is_Empty) note IH = this
    from IH have "isOK(ac_dpp_trivial_check I dpp)" by auto
    from ac_dpp_trivial_check[OF this] show ?case .
  next
    case (AC_Subterm_Proc pi del_p prof) note IH = this
    from IH obtain dpp' where proc: "ac_subterm_proc I pi del_p dpp = return dpp'" 
      and IH: "finite_rel_dpp (ac_dpp dpp')" by auto
    from sound_proc_impl[OF ac_subterm_proc proc IH]
    show ?case .
  next
    case (AC_Redpair_UR_Proc redp del_p ur prof) note IH = this
    from IH obtain dpp' where proc: "ac_ur_redpair_proc I (get_rel_impl redp) del_p ur dpp = return dpp'" 
      and IH: "finite_rel_dpp (ac_dpp dpp')" by auto
    from sound_proc_impl[OF ac_ur_redpair_proc[OF get_rel_impl] proc IH]
    show ?case .
  next
    case (AC_Mono_Redpair_UR_Proc redp del_p del_r ur prof) note IH = this
    from IH obtain dpp' where proc: "ac_mono_ur_redpair_proc I (get_rel_impl redp) del_p del_r ur dpp = return dpp'" 
      and IH: "finite_rel_dpp (ac_dpp dpp')" by auto
    from sound_proc_impl[OF ac_mono_ur_redpair_proc[OF get_rel_impl] proc IH]
    show ?case .
  next
    case (AC_Dep_Graph_Proc edpts i dpp)
    note IH = this    
    from IH(2) obtain pdpps where proc: "ac_dep_graph_proc I dpp edpts = return pdpps" 
      and rec: "\<And>j. j < length pdpps \<Longrightarrow>
        isOK ((\<lambda>(prof, dpp') j.
          check_ac_dp_termination_proof (add_index i (Suc j)) dpp' prof) (pdpps ! j) j)"
    by auto
    show ?case
    proof (rule ac_dep_graph_proc[OF I proc])
      fix p dpp'
      assume mem: "(p, dpp') \<in> set pdpps"
      from this[unfolded set_conv_nth]
        obtain j where j: "j < length pdpps" and pair: "pdpps ! j = (p, dpp')" by auto
      from rec[OF j] have rec: "isOK (check_ac_dp_termination_proof (add_index i (Suc j)) dpp' p)"
        unfolding pair by simp
      from proc[unfolded ac_dep_graph_proc_def, simplified]
      have pdpps: "pdpps =
        map (\<lambda>aP. (the (fst aP), ac_dpp_ops.intersect_pairs I dpp (snd aP)))
            [aP\<leftarrow>edpts . \<exists>y. fst aP = Some y]" by simp
      from mem[unfolded this set_map] obtain edp r where edp: "(Some edp, r) \<in> set edpts" 
        and p: "p \<in> set_option (Some edp)" by auto
      show "finite_rel_dpp (ac_dpp_ops.ac_dpp I dpp')" 
        by (rule IH(1)[OF edp _ p rec], simp add: Basic_BNFs.fsts.simps)
    qed
  qed
qed
end

context
  fixes I :: "('dpp, ('f ::{showl, compare_order}, 'l :: {showl, compare_order}) lab, string) ac_dpp_ops"
  fixes J :: "('tp, ('f, 'l) lab, string) ac_tp_ops"
begin
fun check_ac_termination_proof :: "showsl \<Rightarrow> 'tp \<Rightarrow> ('f, 'l, string) ac_termination_proof \<Rightarrow> showsl check" where
  "check_ac_termination_proof i tp (AC_DP_Trans info prf1 prf2) = debug i (STR ''AC Dependency Pairs'') (do {
     (dp1, dp2) \<leftarrow> ac_dependency_pairs_proc J I Sharp ''x'' ''y'' ''z'' info tp
        <+? (\<lambda> s. i o showsl_lit (STR '': error when applying AC-dependency pair processor to\<newline>'') o
             showsl_ac_tp J tp o s);
     check_ac_dp_termination_proof I (add_index i 1) dp1 prf1
        <+? (\<lambda>s. i o showsl_lit (STR '': error below AC-dependency pair processor\<newline>'') o s);
     check_ac_dp_termination_proof I (add_index i 2) dp2 prf2
        <+? (\<lambda>s. i o showsl_lit (STR '': error below AC-dependency pair processor\<newline>'') o s)
   })"
| "check_ac_termination_proof i tp (AC_DP_Trans_Single info prf1) = debug i (STR ''AC Dependency Pairs'') (do {
     dp1 \<leftarrow> ac_dependency_pairs_proc_simple J I Sharp ''x'' ''y'' ''z'' info tp
        <+? (\<lambda> s. i o showsl_lit (STR '': error when applying AC-dependency pair processor to\<newline>'') o
             showsl_ac_tp J tp o s);
     check_ac_dp_termination_proof I (add_index i 1) dp1 prf1
        <+? (\<lambda>s. i o showsl_lit (STR '': error below AC-dependency pair processor\<newline>'') o s)
   })"
| "check_ac_termination_proof i tp (AC_Rule_Removal redp del_r prf) = debug i (STR ''AC_Mono_Redpair_UR_Proc'') (do {
     tp' \<leftarrow> ac_rule_removal J (get_rel_impl redp) del_r tp
       <+? (\<lambda>s. i o showsl_lit (STR '': error when applying AC rule removal to AC termination problem\<newline>'') o
             showsl_ac_tp J tp o showsl_lit (STR ''\<newline>trying to remove rules\<newline>'') o showsl_rules del_r o 
             showsl_nl o s);
     check_ac_termination_proof (add_index i 1) tp' prf
         <+? (\<lambda>s. i o showsl_lit (STR '': error below AC rule removal\<newline>'') o s)
   })" 
| "check_ac_termination_proof i tp AC_R_is_Empty = debug i (STR ''AC_R_is_Empty'') (
      check (ac_tp_ops.R J tp = []) (showsl_lit (STR ''The TRS is not empty''))
        <+? (\<lambda>s. i o showsl_lit (STR '': error when applying the R-is-Empty check on the AC termination problem\<newline>'') o
             showsl_ac_tp J tp o showsl_nl o s))"

lemma check_ac_termination_proof:
  assumes I: "ac_dpp_spec I" and J: "ac_tp_spec J"
  and ok: "isOK(check_ac_termination_proof i tp prf)"
  shows "SN (relation_ac_tp (ac_tp_ops.ac_tp J tp))"
proof -
  interpret ac_tp_spec J by fact
  from ok show ?thesis
  proof (induct "prf" arbitrary: i tp)
    case (AC_DP_Trans info prf1 prf2) note IH = this
    from IH obtain dp1 dp2 where res: "ac_dependency_pairs_proc J I Sharp ''x'' ''y'' ''z'' info tp = return (dp1,dp2)"
      and IH: "finite_rel_dpp (ac_dpp_ops.ac_dpp I dp1)" "finite_rel_dpp (ac_dpp_ops.ac_dpp I dp2)" 
      by (auto simp: check_ac_dp_termination_proof[OF I])
    show ?case 
      by (rule ac_dependency_pairs_proc[OF J I _ _ _ _ res IH], auto simp: inj_on_def)
  next
    case (AC_DP_Trans_Single info prf1) note IH = this
    from IH obtain dp1 where res: "ac_dependency_pairs_proc_simple J I Sharp ''x'' ''y'' ''z'' info tp = return dp1"
      and IH: "finite_rel_dpp (ac_dpp_ops.ac_dpp I dp1)"  
      by (auto simp: check_ac_dp_termination_proof[OF I])
    show ?case 
      by (rule ac_dependency_pairs_proc_simple[OF J I _ _ _ _ res IH], auto simp: inj_on_def)
  next
    case (AC_Rule_Removal rp rs prf1) note IH = this
    from IH(2) obtain tp1 where res: "ac_rule_removal J (get_rel_impl rp) rs tp = return tp1" 
      by auto
    from ac_rule_removal[OF get_rel_impl res IH(1)] IH(2) res
    show ?case by auto
  next 
    case AC_R_is_Empty
    then show ?case by (auto simp: aoc_rewriting.relaoc_def)
  qed
qed
end

end
