(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Termination_Problem_Impl
imports
  Termination_Problem_Spec
  TRS.Rule_Map
  TRS.Q_Restricted_Rewriting_Impl
  Auxx.Map_Choice
begin

type_synonym ('f ,'v) tp_impl =
  "bool \<times> 
   ('f, 'v) term list \<times>
   bool \<times> \<comment> \<open>are the NFs of Q a subset of the NFs of the rules?\<close>
   ('f, 'v) rules \<times> \<comment> \<open>rules of R, having variables as lhss\<close>
   ('f, 'v) rules \<times> \<comment> \<open>rules of Rw, having variables as lhss\<close>
   ('f, 'v, bool) rm \<times>
   (('f,'v)term \<Rightarrow> bool) \<comment> \<open> is Q-NF \<close>"

fun qreltrs_impl :: "('f::compare_order, 'v) tp_impl \<Rightarrow> ('f, 'v) qreltrs" where
  "qreltrs_impl (nfs,q, _, vR, vRw, m, isnf) = (nfs,
    set q,
    set vR \<union> set (rules_with id m),
    set vRw \<union> set (rules_with Not m))"

fun Q_impl :: "('f, 'v) tp_impl \<Rightarrow> ('f, 'v) term list" where "Q_impl (_,q, _) = q"

fun R_impl :: "('f::compare_order, 'v) tp_impl \<Rightarrow> ('f, 'v) rules" where
  "R_impl (_,_, _, vR, _, m,_) = vR @ rules_with id m"

fun Rw_impl :: "('f::compare_order, 'v) tp_impl \<Rightarrow> ('f, 'v) rules" where
  "Rw_impl (_,_, _, _, vRw, m, _) = vRw @ rules_with Not m"

fun Nfs_impl :: "('f::compare_order, 'v) tp_impl \<Rightarrow> bool" where
  "Nfs_impl (nfs,_) = nfs"

fun rules_impl :: "('f::compare_order, 'v) tp_impl \<Rightarrow> ('f, 'v) rules" where
  "rules_impl (_,_, _, vR, vRw, m,_) = vR @ vRw @ Rule_Map.rules m"

fun Q_empty_impl :: "('f, 'v) tp_impl \<Rightarrow> bool" where
  "Q_empty_impl (_,q, _) = (q = [])"

fun is_QNF_impl :: "('f, 'v) tp_impl \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "is_QNF_impl (_,_, _,_,_,_,isnf) = isnf"

fun NFQ_subset_NF_rules_impl :: "('f, 'v) tp_impl \<Rightarrow> bool" where
  "NFQ_subset_NF_rules_impl (_,_, b, _) = b"

fun rules_map_impl :: "('f::compare_order, 'v) tp_impl \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules" where
  "rules_map_impl (_,_, _, _, _, m, _) fn =
    (case rm.lookup fn m of
      None \<Rightarrow> []
    | Some rs \<Rightarrow> map snd rs)"

fun
  delete_R_Rw_impl ::
    "('f::compare_order, 'v) tp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) tp_impl"
where
  "delete_R_Rw_impl (nfs,q, _, vR, vRw, m, isnf) r rw = (
    let
      (vr, r)   = partition (is_Var \<circ> fst) r;
      (vrw, rw) = partition (is_Var \<circ> fst) rw;
      vr'       = list_diff vR vr;
      vrw'      = list_diff vRw vrw;
      m'        = delete_rules True r (delete_rules False rw m)
    in
    (nfs,q, is_NF_trs_subset isnf (vr' @ vrw' @ Rule_Map.rules m'), vr', vrw', m', isnf))"

definition
  split_rules_impl ::
    "('f::compare_order, 'v :: compare_order) tp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
where
  "split_rules_impl tp rs \<equiv> let m = ceta_set_of rs in partition m (rules_impl tp)"

definition
  mk_impl ::
    "bool \<Rightarrow> ('f::compare_order, 'v) term list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) tp_impl"
where
  "mk_impl nfs q r rw \<equiv> (
    let
      (vr, r') = partition (is_Var \<circ> fst) r;
      (vrw, rw') = partition (is_Var \<circ> fst) rw;
      isnf = is_NF_terms q
    in
    (nfs,q,
      is_NF_trs_subset isnf (r @ rw),
      vr,
      vrw,
      insert_rules True r' (insert_rules False rw' (rm.empty ())), 
      isnf))"

fun is_tp :: "('f::compare_order, 'v) tp_impl \<Rightarrow> bool" where
  "is_tp (nfs,q, qsub, vr, vrw, m, isnf) = (
    (NF_terms (set q) \<subseteq> NF_trs (set (vr @ vrw @ Rule_Map.rules m)) \<longleftrightarrow> qsub) \<and>
    (\<forall>r\<in>set (vr @ vrw). is_Var (fst r)) \<and>
    rm_inj m \<and>
    (isnf = (\<lambda> t. t \<in> NF_terms (set q))))"

lemma qreltrs_impl_sound:
  "qreltrs_impl tp = (Nfs_impl tp, set (Q_impl tp), set (R_impl tp), set (Rw_impl tp))"
  by (cases tp) simp_all

lemma values_rules_with_conv:
  "snd ` set (values m) = set (rules_with id m) \<union> set (rules_with Not m)"
  by (auto simp: rules_with_def o_def)

lemma rules_impl_sound:
  "set (rules_impl tp) = set (R_impl tp) \<union> set (Rw_impl tp)"
  by (cases tp) (auto simp: values_rules_with_conv)

lemma Q_empty_impl_sound:
  "Q_empty_impl tp \<longleftrightarrow> set (Q_impl tp) = {}"
  by (cases tp) simp

lemma is_QNF_impl_sound:
  "is_tp tp \<Longrightarrow> is_QNF_impl tp = (\<lambda>t. t \<in> NF_terms (set (Q_impl tp)))"
  by (cases tp) simp

lemma NFQ_subset_NF_rules_impl_sound:
  assumes "is_tp tp"
  shows "NFQ_subset_NF_rules_impl tp
    \<longleftrightarrow> NF_terms (set (Q_impl tp)) \<subseteq> NF_trs (set (R_impl tp) \<union> set (Rw_impl tp))"
  using assms by (cases tp) (simp add: values_rules_with_conv Un_ac)

lemma mk_impl_sound:
  "qreltrs_impl (mk_impl nfs q r rw) = (nfs,set q, set r, set rw)"
  by (auto simp: mk_impl_def Let_def)

lemma is_Var_aux:
  fixes R::"('f, 'v) trs"
  assumes "\<forall>r\<in>R. is_Var (fst r)" and "S \<subseteq> R" and "(Fun f ts, r) \<in> S"
  shows "False"
proof -
  from assms have "(Fun f ts, r) \<in> R" by blast
  with assms have "is_Var (Fun f ts)" by auto
  then show False by simp
qed

lemma rules_map_impl_sound:
  assumes "is_tp tp"
  shows "set (rules_map_impl tp (f, n)) =
    {r |r. r \<in> set (rules_impl tp) \<and> root (fst r) = Some (f, n)}"
    (is "?A = ?B")
proof (cases tp)
  case (fields nfs q qsub vr vrw m isnf)
  show ?thesis
  proof
    show "?A \<subseteq> ?B"
    proof
      fix l r assume 1: "(l, r) \<in> set (rules_map_impl tp (f, n))"
      show "(l, r) \<in> ?B"
      proof (cases "rm.lookup (f, n) m")
        case None with 1 show ?thesis by (simp add: fields)
      next
        case (Some rs)
        with 1 have 2: "(l, r) \<in> snd `set rs" by (simp add: fields)
        from assms and Some have "\<forall>r\<in>set rs. key r = Some (f, n)"
          by (simp add: fields rm_inj_def mmap_inj_def rm.correct)
        moreover from 2 obtain a where "(a, l, r) \<in> set rs" by auto
        ultimately have "key (a, l, r) = Some (f, n)" by simp
        then have root: "root l = Some (f, n)"
          by (cases l, simp_all)
        from Some_in_values[OF Some] have "set rs \<subseteq> set (values m)" .
        then have "(l, r) \<in> snd ` set (values m)" using 2 by auto
        then have "(l, r) \<in> set (rules_impl tp)"
          by (auto simp: fields values_rules_with_conv)
        with root show ?thesis by simp
      qed
    qed
  next
    show "?B \<subseteq> ?A"
    proof
      fix l r assume "(l, r) \<in> ?B"
      then have "(l, r) \<in> set (rules_impl tp)"
        and "root l = Some (f, n)" by auto
      then have "(l, r) \<in> set (R_impl tp) \<union> set (Rw_impl tp)" by (simp add: rules_impl_sound)
      then have 1: "(l, r) \<in> set (rules_impl tp)" by (auto simp: fields values_rules_with_conv)
      from \<open>root l = Some (f, n)\<close> obtain ts where l: "l = Fun f ts" by (cases l) auto
      from 1 and assms[unfolded fields, simplified, THEN conjunct2, THEN conjunct1]
        have "(l, r) \<in> set (Rule_Map.rules m)"
        unfolding fields l
        using is_Var_aux[of "set vr \<union> set vrw" "set vr" f ts r]
        using is_Var_aux[of "set vr \<union> set vrw" "set vrw" f ts r]
        by (auto simp add: values_rules_with_conv)
      then obtain a where "(a, l, r) \<in> set (values m)" by auto
      from this[unfolded values_ran[unfolded ran_def]] 
        obtain k vs where lookup: "rm.lookup k m = Some vs"
        and "(a, l, r) \<in> set vs" by (auto simp: rm.correct)
      then have 2: "(l, r) \<in> set (rules_map_impl tp k)" unfolding fields by force
      have k: "k = (f, n)"
      proof -
        from \<open>root l = Some (f, n)\<close> have "length ts = n" by (simp add: l)
        from assms[unfolded fields, simplified, THEN conjunct2, THEN conjunct2, THEN conjunct1,
          unfolded rm_inj_def mmap_inj_def, rule_format, OF _ \<open>(a, l, r) \<in> set vs\<close>]
          and lookup have "key (a, l, r) = Some k" by (auto simp: rm.correct)
        then show ?thesis by (simp add: \<open>length ts = n\<close> l)
      qed
      from 2 show "(l, r) \<in> ?A" unfolding k .
    qed
  qed
qed

lemma delete_R_Rw_impl_sound:
  assumes "is_tp tp"
  shows "qreltrs_impl (delete_R_Rw_impl tp rs rws) =
    (Nfs_impl tp, set (Q_impl tp), set (R_impl tp) - set rs, set (Rw_impl tp) - set rws)"
proof (cases tp)
  case (fields nfs q qsub vr vrw m isnf)
  from assms have inj: "rm_inj m" by (simp add: fields)
  from rm_inj_delete_rules[OF this]
    have inj': "rm_inj (delete_rules False [x\<leftarrow>rws . is_Fun (fst x)] m)" .
  from assms have vars: "\<forall>r\<in>set vr \<union> set vrw. is_Var (fst r)" by (simp add: fields)
  show ?thesis
    using inj and vars
    by (simp add: fields qreltrs_impl_sound Let_def rules_with_def o_def
                  values_delete_rules[OF inj']
                  values_delete_rules[OF inj]) auto
qed

lemma split_rules_impl_sound:
  assumes "split_rules_impl tp s = (rs, rns)"
  shows "set rs = set (rules_impl tp) \<inter> set s \<and>
    set rns = set (rules_impl tp) - set s"
proof (cases tp)
  case (fields nfs q qsub vr vrw m isnf)
  from assms have rs: "rs =
    [lr\<leftarrow>vr . lr \<in> set s] @ [lr\<leftarrow>vrw . lr \<in> set s] @ [lr\<leftarrow>Rule_Map.rules m . lr \<in> set s]"
    and rns: "rns =
    [x\<leftarrow>vr . x \<notin> set s] @ [x\<leftarrow>vrw . x \<notin> set s] @ [x\<leftarrow>Rule_Map.rules m . x \<notin> set s]"
    by (simp_all add: split_rules_impl_def o_def fields Let_def)
  show ?thesis
    by (auto simp: fields rs rns o_def values_rules_with_conv)
qed

lemmas tp_impl_sound =
  qreltrs_impl_sound
  rules_impl_sound
  Q_empty_impl_sound
  is_QNF_impl_sound
  NFQ_subset_NF_rules_impl_sound
  rules_map_impl_sound
  delete_R_Rw_impl_sound
  split_rules_impl_sound
  mk_impl_sound


section \<open>Invariant free implementation\<close>

context
  notes [[typedef_overloaded]]
begin
typedef ('f, 'v) tp = "{tp :: ('f::compare_order, 'v :: compare_order) tp_impl. is_tp tp}"
  morphisms impl_of TP
proof -
  have "mk_impl False [] [] [] \<in> ?tp"
    by (simp add: mk_impl_def Let_def insert_rules_def del: Id_on_empty)
  then show ?thesis ..
qed
end

definition qreltrs :: "('f::compare_order, 'v :: compare_order) tp \<Rightarrow> ('f, 'v) qreltrs" where
  "qreltrs tp \<equiv> qreltrs_impl (impl_of tp)"

definition Q :: "('f::compare_order, 'v :: compare_order) tp \<Rightarrow> ('f, 'v) term list" where
  "Q tp \<equiv> Q_impl (impl_of tp)"

definition R :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> ('f, 'v) rules" where
  "R tp \<equiv> R_impl (impl_of tp)"

definition Rw :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> ('f, 'v) rules" where
  "Rw tp \<equiv> Rw_impl (impl_of tp)"

definition Nfs :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> bool" where
  "Nfs tp \<equiv> Nfs_impl (impl_of tp)"

definition rules :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> ('f, 'v) rules" where
  "rules tp \<equiv> rules_impl (impl_of tp)"

definition Q_empty :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> bool" where
  "Q_empty tp \<equiv> Q_empty_impl (impl_of tp)"

definition is_QNF :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "is_QNF tp \<equiv> is_QNF_impl (impl_of tp)"

definition NFQ_subset_NF_rules :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> bool" where
  "NFQ_subset_NF_rules tp \<equiv> NFQ_subset_NF_rules_impl (impl_of tp)"

definition rules_map :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules" where
  "rules_map tp \<equiv> rules_map_impl (impl_of tp)"

definition
  delete_R_Rw :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) tp"
where
  "delete_R_Rw tp r rw = TP (delete_R_Rw_impl (impl_of tp) r rw)"

definition
  split_rules :: "('f::compare_order, 'v::compare_order) tp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
where
  "split_rules tp \<equiv> split_rules_impl (impl_of tp)"

definition
  mk :: "bool \<Rightarrow> ('f::compare_order, 'v::compare_order) term list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) tp"
where
  "mk nfs q r rw \<equiv> TP (mk_impl nfs q r rw)"

lemma is_tp_impl_of[simp, intro]: "is_tp (impl_of tp)"
  using impl_of[of tp] by simp

lemma TP_impl_of[simp, code abstype]: "TP (impl_of tp) = tp"
  by (rule impl_of_inverse)

lemma impl_of_TP[simp]: "is_tp tp \<Longrightarrow> impl_of (TP tp) = tp" by (simp add: TP_inverse)

lemma image_snd_Pair_Un[simp]:
  "snd ` ({x \<in> Pair a ` A. P x} \<union> {x \<in> Pair b ` B. P x}) =
    {x \<in> A. P (a, x)} \<union> {x \<in> B. P (b, x)}" by force


lemma is_tp_mk_impl[simp, intro]: "is_tp (mk_impl nfs q r rw)"
proof -
  let ?vr = "filter (is_Var \<circ> fst) r"
  let ?vrw = "filter (is_Var \<circ> fst) rw"
  let ?r = "filter (Not \<circ> (is_Var \<circ> fst)) r"
  let ?rw = "filter (Not \<circ> (is_Var \<circ> fst)) rw"
  let ?m = "insert_rules True ?r (insert_rules False ?rw (rm.empty ()))"
  let ?isnf = "is_NF_terms q"

  have "NF_terms (set q) \<subseteq> NF_trs (set (?vr @ ?vrw @ Rule_Map.rules ?m))
    \<longleftrightarrow> is_NF_trs_subset ?isnf (r @ rw)"
  proof -
    have 1: "set (?vr @ ?vrw @ Rule_Map.rules ?m) = set (r @ rw)"
      by (simp add: insert_rules_def) force
    show ?thesis unfolding 1 by simp
  qed
  moreover have "\<forall>r\<in>set (?vr @ ?vrw). is_Var (fst r)" by auto
  moreover have "rm_inj ?m" by simp
  ultimately show ?thesis using is_NF_terms[of q]
    by (simp only: mk_impl_def Let_def case_prod_partition is_tp.simps)
qed

lemma impl_of_mk[code abstract]: "impl_of (mk nfs q r rw) = mk_impl nfs q r rw"
  by (simp add: mk_def)

lemma is_tp_delete_R_Rw_impl[simp]:
  assumes "is_tp tp"
  shows "is_tp (delete_R_Rw_impl tp r rw)"
proof (cases tp)
  case (fields nfs q qsub vr vrw m isnf )
  from assms have vars: "\<forall>r\<in>set (vr @ vrw). is_Var (fst r)" by (simp add: fields)
  from assms have isnf: "isnf = (\<lambda> t. t \<in> NF_terms (set q))"
    by (simp add: fields)
  from assms
    have qsub: "qsub \<longleftrightarrow> NF_terms (set q) \<subseteq> NF_trs (set (vr @ vrw @ Rule_Map.rules m))"
    by (simp add: fields)
  from assms have rm_inj: "rm_inj m" by (simp add: fields)
  let ?vr = "list_diff vr (filter (is_Var \<circ> fst) r)"
  let ?vrw = "list_diff vrw (filter (is_Var \<circ> fst) rw)"
  let ?r = "filter (Not \<circ> (is_Var \<circ> fst)) r"
  let ?rw = "filter (Not \<circ> (is_Var \<circ> fst)) rw"
  let ?m = "delete_rules True ?r (delete_rules False ?rw m)"
  have "NF_terms (set q) \<subseteq> NF_trs (set (?vr @ ?vrw @ Rule_Map.rules ?m))
    \<longleftrightarrow> is_NF_trs_subset isnf (?vr @ ?vrw @ Rule_Map.rules ?m)"
    unfolding isnf by simp
  moreover have "\<forall>r\<in>set (?vr @ ?vrw). is_Var (fst r)" using vars by auto
  moreover have "rm_inj ?m" using rm_inj by simp
  ultimately show ?thesis using isnf
    by (simp only: fields delete_R_Rw_impl.simps case_prod_partition Let_def is_tp.simps)       
qed

lemma impl_of_delete_R_Rw[code abstract]:
  "impl_of (delete_R_Rw tp r rw) = delete_R_Rw_impl (impl_of tp) r rw"
  unfolding delete_R_Rw_def by simp

lemma qreltrs_sound: "qreltrs tp = (Nfs tp, set (Q tp), set (R tp), set (Rw tp))"
  by (simp add: qreltrs_def Q_def R_def Rw_def Nfs_def tp_impl_sound)

lemma rules_sound: "set (rules tp) = set (R tp) \<union> set (Rw tp)"
  by (simp add: rules_def R_def Rw_def tp_impl_sound)

lemma Q_empty_sound: "Q_empty tp \<longleftrightarrow> set (Q tp) = {}"
  by (simp add: Q_empty_def Q_def tp_impl_sound)

lemma is_QNF_sound: "is_QNF tp = (\<lambda>t. t \<in> NF_terms (set (Q tp)))"
  by (simp add: is_QNF_def Q_def tp_impl_sound)

lemma NFQ_subset_NF_rules_sound:
  "NFQ_subset_NF_rules tp \<longleftrightarrow> NF_terms (set (Q tp)) \<subseteq> NF_trs (set (R tp) \<union> set (Rw tp))"
  using NFQ_subset_NF_rules_impl_sound[OF is_tp_impl_of, of tp]
  unfolding Q_def R_def Rw_def NFQ_subset_NF_rules_def .

lemma rules_map_sound:
  "set (rules_map tp (f, n)) =
    {r |r. r \<in> set (rules tp) \<and> root (fst r) = Some (f, n)}"
  using rules_map_impl_sound[OF is_tp_impl_of, of tp f n]
  unfolding rules_map_def rules_def .

lemma delete_R_Rw_sound:
  "qreltrs (delete_R_Rw tp r rw) = (Nfs tp, set (Q tp), set (R tp) - set r, set (Rw tp) - set rw)"
  using delete_R_Rw_impl_sound[OF is_tp_impl_of, of tp r rw]
  unfolding qreltrs_def delete_R_Rw_def Q_def R_def Rw_def Nfs_def
  using is_tp_delete_R_Rw_impl[OF is_tp_impl_of] by simp

lemma split_rules_sound:
  assumes "split_rules tp s = (r, rw)"
  shows "set r = set (rules tp) \<inter> set s \<and> set rw = set (rules tp) - set s"
  using split_rules_impl_sound[OF assms[unfolded split_rules_def]]
  unfolding rules_def .

lemma mk_sound:
  "qreltrs (mk nfs q r rw) = (nfs,set q, set r, set rw)"
  by (simp add: mk_impl_sound qreltrs_def mk_def)

lemmas tp_sound =
  qreltrs_sound
  rules_sound
  Q_empty_sound
  is_QNF_sound
  NFQ_subset_NF_rules_sound
  rules_map_sound
  delete_R_Rw_sound
  split_rules_sound
  mk_sound

definition
  tp_rbt_impl :: "(('f::compare_order, 'v::compare_order) tp, 'f, 'v) tp_ops"
where
  "tp_rbt_impl \<equiv> \<lparr>
    tp_ops.qreltrs = qreltrs,
    tp_ops.Q = Q,
    tp_ops.R = R,
    tp_ops.Rw = Rw,
    tp_ops.rules = rules,
    tp_ops.Q_empty = Q_empty,
    tp_ops.is_QNF = is_QNF,
    tp_ops.NFQ_subset_NF_rules = NFQ_subset_NF_rules,
    tp_ops.rules_map = rules_map,
    tp_ops.delete_R_Rw = delete_R_Rw,
    tp_ops.split_rules = split_rules,
    tp_ops.mk = mk,
    tp_ops.nfs = Nfs\<rparr>"

lemma tp_rbt_impl: "tp_spec tp_rbt_impl"
  using tp_sound
  by (unfold_locales, simp_all only: tp_rbt_impl_def tp_ops.simps)

hide_const (open) Q R Rw Nfs

end
