(*
Author:  Rene Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory AC_Dependency_Pairs_Impl
imports 
  AC_Dependency_Pairs
  Framework.AC_Dependency_Pair_Problem_Spec
  Framework.AC_Termination_Problem_Spec
  AC_TRS.AC_Rewriting_Impl
  DP_Transformation_Impl (* for DP_list *)
begin

datatype ('f,'v)ac_dependency_pairs_proof = AC_dependency_pairs_proof 
  "('f,'v)rules" (* E *)
  "('f,'v)rules" (* DP(R) *)
  "('f,'v)rules" (* DP(E) *)
  "('f,'v)rules" (* R_ext *)

context
  fixes I :: "('tp, 'f :: showl, 'v :: showl)ac_tp_ops"
  and J :: "('dpp, 'f,'v)ac_dpp_ops"
  and shp :: "'f \<Rightarrow> 'f"
  and x y z :: 'v
begin

interpretation sharp_syntax .

fun ac_dependency_pairs_checks :: "('f,'v)ac_dependency_pairs_proof \<Rightarrow> 'tp \<Rightarrow> showsl check" where
  "ac_dependency_pairs_checks (AC_dependency_pairs_proof E DPR DPE Rext) tp = do {
      let A = ac_tp_ops.A I tp;
      let C = ac_tp_ops.C I tp;
      let R = ac_tp_ops.R I tp;
      let OC = list_diff C A;
      let D = defined_list R;
      let DD = set D;
      let D' = defined_list (R @ E);
      check_allm (\<lambda> (f,n). check ((\<sharp> f,n) \<notin> set D') (showsl_lit (STR ''sharping '') \<circ> showsl f \<circ> showsl_lit (STR '' yields the defined symbol '') \<circ> showsl (\<sharp> f))) D';
      check_wf_trs (R @ E) 
        <+? (\<lambda> s. showsl_lit (STR ''TRS or equations are not well-formed'') o s);
      check_symmetric_AC_theory E
        <+? (\<lambda> s. showsl_lit (STR ''equations do not form a symmetric AC-theory\<newline>'') o s);
      check_only_C_theory (set OC) E
        <+? (\<lambda> s. showsl_lit (STR ''equations do not form AC_C-theory\<newline>'') o s);
      check_subseteq (funs_trs_list E) (A @ C)
        <+? (\<lambda> s. showsl_lit (STR ''equations contain symbol '') o showsl s o showsl_lit (STR '' which is not AC-symbol''));
      check_AC_same_as_E x y z A C E
        <+? (\<lambda> s. showsl_lit (STR ''could not ensure that equations correspond to AC equivalence\<newline>'') o s);
      check_subseteq (DP_list shp R D) DPR 
        <+? (\<lambda> lr. showsl_lit (STR ''could not find DP for R: '') o showsl_rule lr);
      check_subseteq (DP_list shp E D) DPE
        <+? (\<lambda> lr. showsl_lit (STR ''could not find DP for E: '') o showsl_rule lr);
      check_ext_trs R A C Rext
        <+? (\<lambda> s. showsl_lit (STR ''could not ensure validity of extended TRS R_ext\<newline>'') o s)
    } <+? (\<lambda> s. showsl_lit (STR ''problem in applying AC-dependency pairs\<newline>'') o s)"

fun ac_dependency_pairs_proc :: "('f,'v)ac_dependency_pairs_proof \<Rightarrow> 'tp \<Rightarrow> ('dpp \<times> 'dpp) result" where
  "ac_dependency_pairs_proc (AC_dependency_pairs_proof E DPR DPE Rext) tp = do {
      ac_dependency_pairs_checks (AC_dependency_pairs_proof E DPR DPE Rext) tp;
      let R = ac_tp_ops.R I tp;
      return (ac_dpp_ops.mk J DPR DPE [] R E, ac_dpp_ops.mk J (map (\<lambda> (l,r). (\<sharp> l, \<sharp> r)) Rext) DPE [] R E)
    }"

fun ac_dependency_pairs_proc_simple :: "('f,'v)ac_dependency_pairs_proof \<Rightarrow> 'tp \<Rightarrow> 'dpp result" where
  "ac_dependency_pairs_proc_simple (AC_dependency_pairs_proof E DPR DPE Rext) tp = do {
      ac_dependency_pairs_checks (AC_dependency_pairs_proof E DPR DPE Rext) tp;
      let R = ac_tp_ops.R I tp;
      return (ac_dpp_ops.mk J (DPR @ map (\<lambda> (l,r). (\<sharp> l, \<sharp> r)) Rext) DPE [] R E)
    }"

context 
  assumes 
  I: "ac_tp_spec I" and
  J: "ac_dpp_spec J" and
  shp: "inj shp" and
  xyz: "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
begin

lemma ac_dependency_pairs_proc: assumes 
  res: "ac_dependency_pairs_proc prf tp = return (dp1, dp2)" and
  fin1: "finite_rel_dpp (ac_dpp_ops.ac_dpp J dp1)" and
  fin2: "finite_rel_dpp (ac_dpp_ops.ac_dpp J dp2)"
  shows "SN (relation_ac_tp (ac_tp_ops.ac_tp I tp))"
proof -
  obtain E DPR DPE Rext where pr: "prf = AC_dependency_pairs_proof E DPR DPE Rext" by (cases "prf", auto)
  interpret ac_tp_spec I by fact
  let ?A = "set (A tp)"
  let ?C = "set (C tp)"
  let ?AC = "?A \<union> ?C"
  let ?OC = "?C - ?A"
  let ?R = "set (R tp)"
  let ?E = "set E"
  let ?RE = "?R \<union> ?E"
  interpret aoc_rewriting ?A ?C .
  interpret J: ac_dpp_spec J by fact
  let ?D = "DP_on \<sharp> {f. defined ?R f}"
  let ?D' = "DP_on \<sharp> {f. defined ?RE f}"
  let ?shpRext = "map (\<lambda> (l,r). (\<sharp> l, \<sharp> r)) Rext"
  from res[unfolded pr ac_dependency_pairs_proc.simps Let_def, simplified] xyz
  have wf: "wf_trs ?RE" and
    shpD: "\<And>f n. defined ?RE (f, n) \<Longrightarrow> \<not> defined ?RE (\<sharp> f, n)" and
    AC: "AC_theory ?E" and
    sym: "symmetric_trs ?E" and
    AC_C: "AC_C_theory ?E ?OC" and
    funsE: "funs_trs ?E \<subseteq> ?AC" and
    AOC_E: "AOCEQ = (rstep ?E)^*" and
    DPR: "?D ?R \<subseteq> set DPR" and
    DPE: "?D ?E \<subseteq> set DPE" and
    dp1: "dp1 = J.mk DPR DPE [] (R tp) E" and
    dp2: "dp2 = J.mk ?shpRext DPE [] (R tp) E" and
    Rext: "is_ext_trs ?R ?A ?C (set Rext)"
    by auto  
  interpret relative_dp shp ?R ?E
    by (standard, insert shp[unfolded inj_on_def], auto simp: wf shpD)
  from fin1[unfolded dp1 J.mk_sound] have "finite_rel_dpp (set DPR, set DPE, {}, ?R, ?E)" by simp
  from finite_rel_dpp_pairs_mono[OF this DPR] DPE
  have fin1: "finite_rel_dpp (?D ?R, ?D ?E, {}, ?R, ?E)" by auto
  have "set ?shpRext = dir_image (set Rext) \<sharp>" unfolding dir_image_def by auto
  from fin2[unfolded dp2 J.mk_sound this] 
  have "finite_rel_dpp (dir_image (set Rext) \<sharp>, set DPE, {}, ?R, ?E)" by simp
  from finite_rel_dpp_pairs_mono[OF this subset_refl, of "?D ?E"] DPE
  have fin2: "finite_rel_dpp (dir_image (set Rext) \<sharp>, ?D ?E, {}, ?R, ?E)" by auto
  show ?thesis unfolding ac_tp_sound relation_ac_tp.simps relaoc_def AOC_E rtrancl_idemp
    by (rule SN_relstep_via_finite_rel_dpps_defined_R[OF Rext AOC_E[symmetric] AC_C funsE fin1 fin2])  
qed

declare ac_dependency_pairs_checks.simps[simp del]

lemma ac_dependency_pairs_proc_simple: assumes 
  res: "ac_dependency_pairs_proc_simple prf tp = return dp" and
  fin: "finite_rel_dpp (ac_dpp_ops.ac_dpp J dp)" 
  shows "SN (relation_ac_tp (ac_tp_ops.ac_tp I tp))"
proof -
  obtain E DPR DPE Rext where pr: "prf = AC_dependency_pairs_proof E DPR DPE Rext" by (cases "prf", auto)
  interpret ac_dpp_spec J by fact
  let ?Rext = "map (\<lambda>(l, r). (\<sharp> l, \<sharp> r)) Rext"
  let ?R = "ac_tp_ops.R I tp"
  from res pr have dp: "dp = mk (DPR @ ?Rext) DPE [] ?R E" 
    and ac_dp: "ac_dependency_pairs_proc prf tp = return (mk DPR DPE [] ?R E, mk ?Rext DPE [] ?R E)"
    by (auto simp: Let_def)
  note fin = fin[unfolded dp mk_sound]
  show ?thesis
    by (rule ac_dependency_pairs_proc[OF ac_dp, unfolded mk_sound, 
      OF finite_rel_dpp_pairs_mono[OF fin] finite_rel_dpp_pairs_mono[OF fin]], auto)
qed
end

end
end
