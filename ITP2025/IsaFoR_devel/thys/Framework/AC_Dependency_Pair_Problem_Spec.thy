(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Operations on AC Dependency-Pair problems (AC-DPPs)\<close>

theory AC_Dependency_Pair_Problem_Spec
imports
  First_Order_Rewriting.Trs_Impl
  AC_TRS.AC_Rewriting
  Relative_DP_Framework
  QDP_Framework_Impl (* to have 'a proc type *)
begin

subsection \<open>Record-Based Interface\<close>

record ('p, 'f, 'v) ac_dpp_ops =
  ac_dpp :: "'p \<Rightarrow> ('f,'v) rel_dpp"
  P :: "'p \<Rightarrow> ('f, 'v) rules"
  Pw :: "'p \<Rightarrow> ('f, 'v) rules"
  pairs :: "'p \<Rightarrow> ('f, 'v) rules"
  R :: "'p \<Rightarrow> ('f, 'v) rules"
  Rw :: "'p \<Rightarrow> ('f, 'v) rules"
  rules :: "'p \<Rightarrow> ('f, 'v) rules"
  E :: "'p \<Rightarrow> ('f, 'v)rules"
  mk :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"
  eq_rules_map :: "'p \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules"
  reverse_eq_rules_map :: "'p \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules"
  delete_pairs_rules :: "'p \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 'p"
  eq_rules_no_left_var :: "'p \<Rightarrow> bool"
  eq_rules_non_collapsing :: "'p \<Rightarrow> bool"
  intersect_pairs :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"


hide_const (open)
  ac_dpp P Pw pairs R Rw rules E eq_rules_map mk delete_pairs_rules eq_rules_map reverse_eq_rules_map 
  eq_rules_no_left_var eq_rules_non_collapsing intersect_pairs

locale ac_dpp_defs =
  fixes I :: "('p, 'f::showl, 'v::showl) ac_dpp_ops"
begin
  abbreviation ac_dpp where "ac_dpp \<equiv> ac_dpp_ops.ac_dpp I"
  abbreviation P where "P \<equiv> ac_dpp_ops.P I"
  abbreviation Pw where "Pw \<equiv> ac_dpp_ops.Pw I"
  abbreviation pairs where "pairs \<equiv> ac_dpp_ops.pairs I"
  abbreviation R where "R \<equiv> ac_dpp_ops.R I"
  abbreviation Rw where "Rw \<equiv> ac_dpp_ops.Rw I"
  abbreviation E where "E \<equiv> ac_dpp_ops.E I"
  abbreviation rules where "rules \<equiv> ac_dpp_ops.rules I"
  abbreviation eq_rules_map where "eq_rules_map \<equiv> ac_dpp_ops.eq_rules_map I"
  abbreviation reverse_eq_rules_map where "reverse_eq_rules_map \<equiv> ac_dpp_ops.reverse_eq_rules_map I"
  abbreviation delete_pairs_rules where "delete_pairs_rules \<equiv> ac_dpp_ops.delete_pairs_rules I"
  abbreviation intersect_pairs where "intersect_pairs \<equiv> ac_dpp_ops.intersect_pairs I"
  abbreviation mk where "mk \<equiv> ac_dpp_ops.mk I"
  abbreviation eq_rules_no_left_var where "eq_rules_no_left_var \<equiv> ac_dpp_ops.eq_rules_no_left_var I"
  abbreviation eq_rules_non_collapsing where "eq_rules_non_collapsing \<equiv> ac_dpp_ops.eq_rules_non_collapsing I"
end

locale ac_dpp_spec = ac_dpp_defs I for I +
  assumes ac_dpp_sound: "ac_dpp d = (set (P d), set (Pw d), set (R d), set (Rw d), set (E d))"
    and pairs_sound: "set (pairs d) = set (P d) \<union> set (Pw d)"
    and rules_sound: "set (rules d) = set (R d) \<union> set (Rw d)"
    and eq_rules_map_sound: "set (eq_rules_map d (f, n)) =
      {r\<in>set (R d @ Rw d @ E d). root (fst r) = Some (f, n)}"
    and eq_rules_non_collapsing_sound:
      "eq_rules_non_collapsing d \<longleftrightarrow> (\<forall>(l, r)\<in>set (R d @ Rw d @ E d). is_Fun r)"
    and eq_rules_no_left_var_sound: "eq_rules_no_left_var d \<longleftrightarrow> (\<forall>(l, r)\<in>set (R d @ Rw d @ E d). is_Fun l)"
    and reverse_eq_rules_map_sound: "set (reverse_eq_rules_map d (f, n)) =
      {(snd r, fst r) | r. r \<in> set (R d @ Rw d @ E d) \<and> root (snd r) = Some (f, n)}"
    and delete_pairs_rules_sound: "ac_dpp (delete_pairs_rules d dp dr) = 
      (set (P d) - set dp, set (Pw d) - set dp, set (R d) - set dr, set (Rw d) - set dr, set (E d))"
    and intersect_pairs_sound:
      "ac_dpp (intersect_pairs d ps) =
        (set (P d) \<inter> set ps, set (Pw d) \<inter> set ps, set (R d), set (Rw d), set (E d))"
    and mk_sound: "ac_dpp (mk p pw r rw e) = (set p, set pw, set r, set rw, set e)"
begin

lemmas ac_dpp_spec_sound[simp] =
  ac_dpp_sound
  pairs_sound 
  rules_sound
  mk_sound
  delete_pairs_rules_sound
  eq_rules_map_sound
  reverse_eq_rules_map_sound
  eq_rules_no_left_var_sound
  eq_rules_non_collapsing_sound
  intersect_pairs_sound

definition sound_proc_impl :: "'a proc \<Rightarrow> bool" where
  "sound_proc_impl proc \<equiv> \<forall>d d'. proc d = return d' \<longrightarrow>
    finite_rel_dpp (ac_dpp d') \<longrightarrow> finite_rel_dpp (ac_dpp d)"

lemma sound_proc_implI[intro]:
  assumes "\<And>d d'. proc d = return d' \<Longrightarrow> finite_rel_dpp (ac_dpp d') \<Longrightarrow> finite_rel_dpp (ac_dpp d)"
  shows "sound_proc_impl proc"
  using assms unfolding sound_proc_impl_def by auto

lemma sound_proc_impl:
  assumes "sound_proc_impl proc"
    and "proc d = return d'"
    and "finite_rel_dpp (ac_dpp d')"
  shows "finite_rel_dpp (ac_dpp d)"
  using assms unfolding sound_proc_impl_def by auto
end

definition ac_dpp_trivial_check :: "('dpp, 'f, 'v) ac_dpp_ops \<Rightarrow> 'dpp \<Rightarrow> showsl check" where
  "ac_dpp_trivial_check I dpp \<equiv> do {
     check (ac_dpp_ops.P I dpp = []) (showsl_lit (STR ''there are strict pairs''));
     check (ac_dpp_ops.Pw I dpp = [] \<or> ac_dpp_ops.R I dpp = []) (showsl_lit (STR ''there are weak pairs and strict rules''))
   }"

lemma (in ac_dpp_spec) ac_dpp_trivial_check: 
  assumes "isOK(ac_dpp_trivial_check I dpp)"
  shows "finite_rel_dpp (ac_dpp dpp)"
proof
  fix s t \<sigma>
  assume "min_relchain (ac_dpp dpp) s t \<sigma>"
  from this[unfolded ac_dpp_sound min_relchain.simps] assms[unfolded ac_dpp_trivial_check_def]
  show False by auto
qed


end
