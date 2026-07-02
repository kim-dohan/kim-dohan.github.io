(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Operations on dependency pair problems (DPPs)\<close>

theory Dependency_Pair_Problem_Spec
imports
  TRS.QDP_Framework
  First_Order_Rewriting.Trs_Impl
  Auxx.Util
begin

section \<open>Record-Based Interface\<close>

record ('p, 'f, 'v) dpp_ops =
  dpp :: "'p \<Rightarrow> ('f, 'v) dpp"
  P :: "'p \<Rightarrow> ('f, 'v) rules"
  Pw :: "'p \<Rightarrow> ('f, 'v) rules"
  pairs :: "'p \<Rightarrow> ('f, 'v) rules"
  Q :: "'p \<Rightarrow> ('f, 'v) term list"
  R :: "'p \<Rightarrow> ('f, 'v) rules"
  Rw :: "'p \<Rightarrow> ('f, 'v) rules"
  rules :: "'p \<Rightarrow> ('f, 'v) rules"
  Q_empty :: "'p \<Rightarrow> bool"
  rules_no_left_var :: "'p \<Rightarrow> bool"
  rules_non_collapsing :: "'p \<Rightarrow> bool"
  is_QNF :: "'p \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  NFQ_subset_NF_rules :: "'p \<Rightarrow> bool"
  rules_map :: "'p \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules"
  reverse_rules_map :: "'p \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules"
  intersect_pairs :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"
  replace_pair :: "'p \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('f,'v) rules \<Rightarrow> 'p"
  intersect_rules :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"
  delete_P_Pw :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"
  delete_R_Rw :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"
  split_pairs :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
  split_rules :: "'p \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
  mk :: "bool \<Rightarrow> bool \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow>
    ('f, 'v) term list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'p"
  minimal :: "'p \<Rightarrow> bool"
  nfs :: "'p \<Rightarrow> bool"
  wwf_rules :: "'p \<Rightarrow> bool"

hide_const (open)
  dpp P Pw pairs Q R Rw rules Q_empty rules_no_left_var rules_non_collapsing
  is_QNF NFQ_subset_NF_rules rules_map reverse_rules_map intersect_pairs
  intersect_rules replace_pair delete_P_Pw delete_R_Rw
  split_pairs split_rules mk minimal nfs wwf_rules

locale dpp_defs =
  fixes I :: "('p, 'f::showl, 'v::showl) dpp_ops"
begin
  abbreviation dpp where "dpp \<equiv> dpp_ops.dpp I"
  abbreviation P where "P \<equiv> dpp_ops.P I"
  abbreviation Pw where "Pw \<equiv> dpp_ops.Pw I"
  abbreviation pairs where "pairs \<equiv> dpp_ops.pairs I"
  abbreviation Q where "Q \<equiv> dpp_ops.Q I"
  abbreviation R where "R \<equiv> dpp_ops.R I"
  abbreviation Rw where "Rw \<equiv> dpp_ops.Rw I"
  abbreviation rules where "rules \<equiv> dpp_ops.rules I"
  abbreviation Q_empty where "Q_empty \<equiv> dpp_ops.Q_empty I"
  abbreviation rules_no_left_var where "rules_no_left_var \<equiv> dpp_ops.rules_no_left_var I"
  abbreviation rules_non_collapsing where
    "rules_non_collapsing \<equiv> dpp_ops.rules_non_collapsing I"
  abbreviation is_QNF where "is_QNF \<equiv> dpp_ops.is_QNF I"
  abbreviation NFQ_subset_NF_rules where "NFQ_subset_NF_rules \<equiv> dpp_ops.NFQ_subset_NF_rules I"
  abbreviation intersect_pairs where "intersect_pairs \<equiv> dpp_ops.intersect_pairs I"
  abbreviation replace_pair where "replace_pair \<equiv> dpp_ops.replace_pair I"
  abbreviation intersect_rules where "intersect_rules \<equiv> dpp_ops.intersect_rules I"
  abbreviation rules_map where "rules_map \<equiv> dpp_ops.rules_map I"
  abbreviation reverse_rules_map where "reverse_rules_map \<equiv> dpp_ops.reverse_rules_map I"
  abbreviation delete_P_Pw where "delete_P_Pw \<equiv> dpp_ops.delete_P_Pw I"
  abbreviation delete_R_Rw where "delete_R_Rw \<equiv> dpp_ops.delete_R_Rw I"
  abbreviation split_pairs where "split_pairs \<equiv> dpp_ops.split_pairs I"
  abbreviation split_rules where "split_rules \<equiv> dpp_ops.split_rules I"
  abbreviation mk where "mk \<equiv> dpp_ops.mk I"
  abbreviation M where "M \<equiv> dpp_ops.minimal I"
  abbreviation NFS where "NFS \<equiv> dpp_ops.nfs I"
  abbreviation wwf_rules where "wwf_rules \<equiv> dpp_ops.wwf_rules I"
end

locale dpp_spec = dpp_defs I for I +
  assumes dpp_sound: "dpp d = (NFS d,M d,set (P d), set (Pw d), set (Q d), set (R d), set (Rw d))"
    and pairs_sound: "set (pairs d) = set (P d) \<union> set (Pw d)"
    and rules_sound: "set (rules d) = set (R d) \<union> set (Rw d)"
    and Q_empty_sound: "Q_empty d \<longleftrightarrow> Q d = []"
    and rules_no_left_var_sound: "rules_no_left_var d \<longleftrightarrow> (\<forall>(l, r)\<in>set (rules d). is_Fun l)"
    and rules_non_collapsing_sound:
      "rules_non_collapsing d \<longleftrightarrow> (\<forall>(l, r)\<in>set (rules d). is_Fun r)"
    and is_QNF_sound: "is_QNF d = (\<lambda>t. t \<in> NF_terms (set (Q d)))"
    and NFQ_subset_NF_rules_sound:
      "NFQ_subset_NF_rules d \<longleftrightarrow> NF_terms (set (Q d)) \<subseteq> NF_trs (set (R d) \<union> set (Rw d))"
    and intersect_pairs_sound:
      "dpp (intersect_pairs d ps) =
        (NFS d,M d,set (P d) \<inter> set ps, set (Pw d) \<inter> set ps, set (Q d), set (R d), set (Rw d))"
    and replace_pair_sound:
      "dpp (replace_pair d pair ps) =
        (NFS d,M d,replace pair (set ps) (set (P d)), replace pair (set ps) (set (Pw d)), set (Q d), set (R d), set (Rw d))"
    and intersect_rules_sound:
      "dpp (intersect_rules d rs) =
        (NFS d,M d,set (P d), set (Pw d), set (Q d), set (R d) \<inter> set rs, set (Rw d) \<inter> set rs)"
    and rules_map_sound: "set (rules_map d (f, n)) =
      {r\<in>set (rules d). root (fst r) = Some (f, n)}"
    and reverse_rules_map_sound: "set (reverse_rules_map d (f, n)) =
      {(snd r, fst r) | r. r \<in> set (rules d) \<and> root (snd r) = Some (f, n)}"
    and delete_P_Pw_sound:
      "dpp (delete_P_Pw d p pw) =
        (NFS d,M d,set (P d) - set p, set (Pw d) - set pw, set (Q d), set (R d), set (Rw d))"
    and delete_R_Rw_sound:
      "dpp (delete_R_Rw d r rw) =
        (NFS d,M d,set (P d), set (Pw d), set (Q d), set (R d) - set r, set (Rw d) - set rw)"
    and split_pairs_sound:
      "split_pairs d ps = (p, pw) \<Longrightarrow>
        set p = set (pairs d) \<inter> set ps \<and> set pw = set (pairs d) - set ps"
    and split_rules_sound:
      "split_rules d rs = (r, rw) \<Longrightarrow>
        set r = set (rules d) \<inter> set rs \<and> set rw = set (rules d) - set rs"
    and mk_sound: "dpp (mk nfs m p pw q r rw) = (nfs, m, set p, set pw, set q, set r, set rw)"
    and wwf_rules_sound: "wwf_rules d = wwf_qtrs (set (Q d)) (set (rules d))"
begin

abbreviation delete_pairs where "delete_pairs d ps \<equiv> dpp_ops.delete_P_Pw I d ps ps"
abbreviation delete_rules where "delete_rules d rs \<equiv> dpp_ops.delete_R_Rw I d rs rs"
abbreviation is_defined where "is_defined d fn \<equiv> dpp_ops.rules_map I d fn \<noteq> []"
abbreviation delete_pairs_rules where
  "delete_pairs_rules d ps rs \<equiv> delete_rules (delete_pairs d ps) rs"

lemma set_not_empty: "xs \<noteq> [] \<longleftrightarrow> set xs \<noteq> {}" by simp

lemma is_defined_sound:
  "is_defined d fn \<longleftrightarrow> defined (set (rules d)) fn"
  unfolding set_not_empty defined_def rules_map_sound[of d "fst fn" "snd fn", simplified]
  by auto

lemmas dpp_spec_sound[simp] =
  dpp_sound
  pairs_sound
  rules_sound
  Q_empty_sound
  rules_no_left_var_sound
  is_defined_sound
  rules_non_collapsing_sound
  is_QNF_sound
  NFQ_subset_NF_rules_sound
  intersect_pairs_sound
  replace_pair_sound
  intersect_rules_sound
  rules_map_sound
  reverse_rules_map_sound
  delete_P_Pw_sound
  delete_R_Rw_sound
  split_pairs_sound
  split_rules_sound
  mk_sound
  wwf_rules_sound

lemma P_delete_pairs_rules:
  "set (P (delete_pairs_rules d ps rs)) = set (P d) - set ps"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma Pw_delete_pairs_rules:
  "set (Pw (delete_pairs_rules d ps rs)) = set (Pw d) - set ps"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma pairs_delete_pairs_rules:
  "set (pairs (delete_pairs_rules d ps rs)) = set (pairs d) - set ps"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma R_delete_pairs_rules:
  "set (R (delete_pairs_rules d ps rs)) = set (R d) - set rs"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma Rw_delete_pairs_rules:
  "set (Rw (delete_pairs_rules d ps rs)) = set (Rw d) - set rs"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma rules_delete_pairs_rules:
  "set (rules (delete_pairs_rules d ps rs)) = set (rules d) - set rs"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma Q_delete_pairs_rules:
  "set (Q (delete_pairs_rules d ps rs)) = set (Q d)"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma nfs_delete_pairs_rules:
  "NFS (delete_pairs_rules d ps rs) = NFS d"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma minimal_delete_pairs_rules:
  "M (delete_pairs_rules d ps rs) = M d"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemma dpp_delete_pairs_rules:
  "dpp (delete_pairs_rules d ps rs) =
    (NFS d, M d, set (P d) - set ps, set (Pw d) - set ps, set (Q d),
     set (R d) - set rs, set (Rw d) - set rs)"
  using delete_P_Pw_sound[of d ps ps]
    and delete_R_Rw_sound[of "delete_pairs d ps" rs rs]
  by auto

lemmas delete_simps[simp] =
  P_delete_pairs_rules
  Pw_delete_pairs_rules
  pairs_delete_pairs_rules
  R_delete_pairs_rules
  Rw_delete_pairs_rules
  rules_delete_pairs_rules
  Q_delete_pairs_rules
  minimal_delete_pairs_rules
  nfs_delete_pairs_rules
  dpp_delete_pairs_rules

lemma P_mk:
  "set (P (mk n m p pw q r rw)) = set p"
  using mk_sound[of n m p pw q r rw] by simp

lemma Pw_mk:
  "set (Pw (mk n m p pw q r rw)) = set pw"
  using mk_sound[of n m p pw q r rw] by simp

lemma Q_mk:
  "set (Q (mk n m p pw q r rw)) = set q"
  using mk_sound[of n m p pw q r rw] by simp

lemma R_mk:
  "set (R (mk n m p pw q r rw)) = set r"
  using mk_sound[of n m p pw q r rw] by simp

lemma Rw_mk:
  "set (Rw (mk n m p pw q r rw)) = set rw"
  using mk_sound[of n m p pw q r rw] by simp

lemma NFS_mk:
  "NFS (mk n m p pw q r rw) = n"
  using mk_sound[of n m p pw q r rw] by simp

lemma M_mk:
  "M (mk n m p pw q r rw) = m"
  using mk_sound[of n m p pw q r rw] by simp

lemmas mk_simps[simp] = P_mk Pw_mk Q_mk R_mk Rw_mk NFS_mk M_mk

end

end
