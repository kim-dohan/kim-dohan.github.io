(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory QDP_Framework_Impl
imports
  Dependency_Pair_Problem_Spec
  Termination_Problem_Spec
begin

type_synonym 'r result = "showsl + 'r"
type_synonym 'a proc = "'a \<Rightarrow> 'a result"

definition (in tp_spec) sound_tt_impl :: "'a proc \<Rightarrow> bool" where
  "sound_tt_impl tt \<equiv> \<forall>tp tp'. tt tp = return tp' \<longrightarrow>
    SN_qrel (qreltrs tp') \<longrightarrow> SN_qrel (qreltrs tp)"

lemma (in tp_spec) sound_tt_implI[intro]:
  assumes "\<And>tp tp'. tt tp = return tp' \<Longrightarrow> SN_qrel (qreltrs tp') \<Longrightarrow> SN_qrel (qreltrs tp)"
  shows "sound_tt_impl tt"
  using assms unfolding sound_tt_impl_def by auto

lemma (in tp_spec) sound_tt_impl:
  assumes "sound_tt_impl tt"
  and "tt tp = return tp'"
  and "SN_qrel (qreltrs tp')"
  shows "SN_qrel (qreltrs tp)"
  using assms unfolding sound_tt_impl_def by auto

lemma (in dpp_spec) finite_under_var_cond_impl:
  assumes m: "M d"
  and nnfs: "\<not> NFS d"
  and var: "(\<And>lr. lr \<in> set (rules d) \<Longrightarrow> is_Fun (fst lr)) \<Longrightarrow> finite_dpp (dpp d)"
  shows "finite_dpp (dpp d)"
  using var unfolding rules_sound dpp_sound
  by (rule finite_under_var_cond[OF _ m nnfs])

definition (in dpp_spec) sound_proc_impl :: "'a proc \<Rightarrow> bool" where
  "sound_proc_impl proc \<equiv> \<forall>d d'. proc d = return d' \<longrightarrow>
    finite_dpp (dpp d') \<longrightarrow> finite_dpp (dpp d)"

lemma (in dpp_spec) sound_proc_implI[intro]:
  assumes "\<And>d d'. proc d = return d' \<Longrightarrow> finite_dpp (dpp d') \<Longrightarrow> finite_dpp (dpp d)"
  shows "sound_proc_impl proc"
  using assms unfolding sound_proc_impl_def by auto

lemma (in dpp_spec) sound_proc_impl:
  assumes "sound_proc_impl proc"
    and "proc d = return d'"
    and "finite_dpp (dpp d')"
  shows "finite_dpp (dpp d)"
  using assms unfolding sound_proc_impl_def by auto

lemma (in dpp_spec) rules_map_defined_conv:
  "(\<lambda>fn. rules_map d fn \<noteq> []) = defined (set (R d) \<union> set (Rw d))"
  by (rule ext) simp

definition internal_error where "internal_error \<equiv> (
  showsl_lit (STR ''internal error\<newline>'') o
  showsl_lit (STR ''please contact one of the CeTA members\<newline>'') o
  showsl_lit (STR ''http://cl-informatik.uibk.ac.at/software/ceta\<newline>'') o 
  showsl_lit (STR ''ceta@informatik.uibk.ac.at\<newline>''))"

definition showsl_terms where
  "showsl_terms name ts = showsl_lit name o showsl_nl o 
     showsl_list_gen showsl (STR '''') (STR '''') (STR ''\<newline>'') (STR '''') ts" 

definition
  showsl_dpp :: "('dpp, 'f :: showl, 'v :: showl) dpp_ops \<Rightarrow> 'dpp \<Rightarrow> showsl"
where
  "showsl_dpp I d = (let
    m = dpp_ops.minimal I d;
    nfs = dpp_ops.nfs I d;
    p  = dpp_ops.P  I d;
    pw = dpp_ops.Pw I d;
    r  = dpp_ops.R  I d;
    rw = dpp_ops.Rw I d;
    q  = dpp_ops.Q  I d
  in     
    showsl_trs' showsl showsl (STR ''pairs:'') (STR '' -> '') p \<circ>
    (if pw = [] then id else showsl_trs' showsl showsl (STR ''weak pairs:'') (STR '' ->= '') pw) \<circ>
    (if r  = [] then id else showsl_trs' showsl showsl (STR ''strict rules:'') (STR '' ->! '') r) \<circ>
    showsl_trs' showsl showsl (STR ''rules:'') (STR '' -> '') rw \<circ>
    (if q  = [] then id else showsl_terms (STR ''Q-component:'') q) \<circ>
    (if m then showsl_lit (STR ''\<newline>(minimal)'') else id) \<circ> 
    (if nfs \<and> q \<noteq> [] then showsl_lit (STR ''\<newline>(normal form substitutions)'') else id))"

definition
  showsl_tp :: "('tp, 'f :: showl, 'v :: showl) tp_ops \<Rightarrow> 'tp \<Rightarrow> showsl"
where
  "showsl_tp I t = (let
    nfs = tp_ops.nfs I t;
    r   = tp_ops.R  I t;
    rw  = tp_ops.Rw I t;
    q   = tp_ops.Q  I t
  in
    showsl_trs' showsl showsl (STR ''rules:'') (STR '' -> '') r \<circ>
    (if rw  = [] then id else showsl_trs' showsl showsl (STR ''relative rules:'') (STR '' ->= '') rw) \<circ>
    (if q  = [] then id else showsl_terms (STR ''Q-component:'') q) \<circ>
    (if nfs then showsl_lit (STR ''substitutions are assumed to be in normal form\<newline>'') else id))"

end
