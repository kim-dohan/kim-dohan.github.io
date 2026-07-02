(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012, 2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Operations on termination problems (TPs)\<close>

theory Termination_Problem_Spec
imports
  TRS.QDP_Framework
  First_Order_Rewriting.Trs_Impl
begin

section \<open>Record-Based Interface\<close>

record ('p, 'f, 'v) tp_ops =
  qreltrs :: "'p \<Rightarrow> ('f, 'v) qreltrs"
  Q :: "'p \<Rightarrow> ('f, 'v) term list"
  R :: "'p \<Rightarrow> ('f, 'v) rules"
  Rw :: "'p \<Rightarrow> ('f, 'v) rules"
  rules :: "'p \<Rightarrow> ('f, 'v) rules"
  Q_empty :: "'p \<Rightarrow> bool"
  is_QNF :: "'p \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  NFQ_subset_NF_rules :: "'p \<Rightarrow> bool"
  rules_map :: "'p \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules"
  delete_R_Rw :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"
  split_rules :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
  mk :: "bool \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"
  nfs :: "'p \<Rightarrow> bool"

hide_const (open)
  qreltrs Q R Rw rules Q_empty is_QNF
  NFQ_subset_NF_rules rules_map delete_R_Rw split_rules mk nfs

locale tp_defs =
  fixes I :: "('p, 'f::showl, 'v::showl) tp_ops"
begin
  abbreviation qreltrs where "qreltrs \<equiv> tp_ops.qreltrs I"
  abbreviation Q where "Q \<equiv> tp_ops.Q I"
  abbreviation R where "R \<equiv> tp_ops.R I"
  abbreviation Rw where "Rw \<equiv> tp_ops.Rw I"
  abbreviation rules where "rules \<equiv> tp_ops.rules I"
  abbreviation Q_empty where "Q_empty \<equiv> tp_ops.Q_empty I"
  abbreviation is_QNF where "is_QNF \<equiv> tp_ops.is_QNF I"
  abbreviation NFQ_subset_NF_rules where "NFQ_subset_NF_rules \<equiv> tp_ops.NFQ_subset_NF_rules I"
  abbreviation rules_map where "rules_map \<equiv> tp_ops.rules_map I"
  abbreviation delete_R_Rw where "delete_R_Rw \<equiv> tp_ops.delete_R_Rw I"
  abbreviation split_rules where "split_rules \<equiv> tp_ops.split_rules I"
  abbreviation mk where "mk \<equiv> tp_ops.mk I"
  abbreviation NFS where "NFS \<equiv> tp_ops.nfs I"
end

locale tp_spec = tp_defs I for I +
  assumes qreltrs_sound: "qreltrs tp = (NFS tp, set (Q tp), set (R tp), set (Rw tp))"
    and rules_sound: "set (rules tp) = set (R tp) \<union> set (Rw tp)"
    and Q_empty_sound: "Q_empty tp \<longleftrightarrow> set (Q tp) = {}"
    and is_QNF_sound: "is_QNF tp = (\<lambda>t. t \<in> NF_terms (set (Q tp)))"
    and NFQ_subset_NF_rules_sound:
      "NFQ_subset_NF_rules tp \<longleftrightarrow>
      NF_terms (set (Q tp)) \<subseteq> NF_trs (set (R tp) \<union> set (Rw tp))"
    and rules_map_sound:
      "set (rules_map tp (f, n)) =
      {r | r. r \<in> set (rules tp) \<and> root (fst r) = Some (f, n)}"
    and delete_R_Rw_sound:
      "qreltrs (delete_R_Rw tp rs rws) =
      (NFS tp, set (Q tp), set (R tp) - set rs, set (Rw tp) - set rws)"
    and split_rules_sound: "split_rules tp s = (rs, rns) \<Longrightarrow>
      set rs = (set (rules tp)) \<inter> set s \<and>
      set rns = (set (rules tp)) - set s"
    and mk_sound: "qreltrs (mk nfs q r rw) = (nfs, set q, set r, set rw)"
begin
  abbreviation delete_rules where "delete_rules tp r \<equiv> tp_ops.delete_R_Rw I tp r r"

lemmas tp_spec_sound[simp] =
  qreltrs_sound
  rules_sound
  Q_empty_sound
  is_QNF_sound
  NFQ_subset_NF_rules_sound
  rules_map_sound
  delete_R_Rw_sound
  split_rules_sound
  mk_sound

lemma Q_delete_R_Rw:
  "set (Q (delete_R_Rw tp r rw)) = set (Q tp)"
  using delete_R_Rw_sound[of tp r rw]
  unfolding tp_spec_sound by auto

lemma R_delete_R_Rw:
  "set (R (delete_R_Rw tp r rw)) = set (R tp) - set r"
  using delete_R_Rw_sound[of tp r rw]
  unfolding tp_spec_sound by auto

lemma Rw_delete_R_Rw:
  "set (Rw (delete_R_Rw tp r rw)) = set (Rw tp) - set rw"
  using delete_R_Rw_sound[of tp r rw]
  unfolding tp_spec_sound by auto

lemma nfs_delete_R_Rw:
  "NFS (delete_R_Rw tp r rw) = NFS tp"
  using delete_R_Rw_sound[of tp r rw]
  unfolding tp_spec_sound by auto

lemma rules_delete_rules:
  "set (rules (delete_rules tp r)) = set (rules tp) - set r"
  using delete_R_Rw_sound[of tp r r]
  unfolding tp_spec_sound by auto

lemmas delete_simps[simp] =
  Q_delete_R_Rw R_delete_R_Rw Rw_delete_R_Rw nfs_delete_R_Rw
  rules_delete_rules

lemma Q_mk:
  "set (Q (mk n q r rw)) = set q"
  using mk_sound[of n q r rw]
  unfolding tp_spec_sound by auto

lemma R_mk:
  "set (R (mk n q r rw)) = set r"
  using mk_sound[of n q r rw]
  unfolding tp_spec_sound by auto

lemma Rw_mk:
  "set (Rw (mk n q r rw)) = set rw"
  using mk_sound[of n q r rw]
  unfolding tp_spec_sound by auto

lemma rules_mk:
  "set (rules (mk n q r rw)) = set r \<union> set rw"
  using mk_sound[of n q r rw]
  unfolding tp_spec_sound by auto

lemma NFS_mk:
  "NFS (mk n q r rw) = n"
  using mk_sound[of n q r rw]
  unfolding tp_spec_sound by auto

lemmas mk_simps[simp] = Q_mk R_mk Rw_mk rules_mk NFS_mk

end

end
