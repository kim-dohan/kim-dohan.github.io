(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Flat_Context_Closure
  imports
    Auxx.Name
    TRS.QDP_Framework
    TRS.Signature_Extension
begin

definition
  root_altering :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs" ("'(_')a" 1000)
where
  "(R)a \<equiv> {(l, r) | l r. (l, r) \<in> R \<and> root l \<noteq> root r}"

text \<open>The following function creates a flat context with root @{text f}
and a hole at position @{text i}. All variables are taken from the list
@{text xs}.\<close>
definition
  flat_ctxt_i :: "('f, 'v) term list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> ('f, 'v) ctxt"
where
  "flat_ctxt_i xs f i \<equiv> More f (take i xs) \<box> (drop (Suc i) xs)"

definition
  fresh_vars :: "nat \<Rightarrow> string set \<Rightarrow> string list"
where
  "fresh_vars n tabus \<equiv> fresh_strings ''x'' 0 tabus n"

lemma fresh_vars_fresh:
  assumes "finite V"
  shows "set (fresh_vars n V) \<inter> V = {}"
  using assms fresh_name_gen_for_strings[of "''x''" 0]
  unfolding fresh_vars_def fresh_name_gen_def by auto

lemma fresh_vars_length:
  assumes "finite V" shows "length (fresh_vars n V) = n"
  using assms fresh_name_gen_for_strings[of "''x''" 0]
  unfolding fresh_name_gen_def fresh_vars_def by simp

lemma Var_inj: "inj_on Var (set vs)" unfolding inj_on_def by auto

lemma fresh_vars_distinct:
  assumes "finite V"
  shows "distinct (fresh_vars n V)"
  using assms Var_inj[of "fresh_strings ''x'' 0 V n"]
  fresh_name_gen_for_strings[of "''x''" 0]
  distinct_map[of Var "fresh_strings ''x'' 0 V n"]
  unfolding fresh_name_gen_def fresh_vars_def by auto

definition
  flat_ctxts :: "string set \<Rightarrow> ('f \<times> nat) set \<Rightarrow> ('f, string) ctxt set"
where
  "flat_ctxts tabus fs \<equiv> (\<Union>(f, n)\<in>fs.
    {flat_ctxt_i (map Var (fresh_vars n tabus)) f i | i. i \<in> {0..<n}})"

definition
  flat_ctxt_closure :: "('f \<times> nat) set \<Rightarrow> ('f, string) trs \<Rightarrow> ('f, string) trs" ("FC")
where
  "FC F R \<equiv> (\<Union>(l, r)\<in>(R)a. {(C\<langle>l\<rangle>, C\<langle>r\<rangle>) | C. C \<in> flat_ctxts (vars_trs R) F}) \<union> (R - (R)a)"

lemma flat_ctxts_empty[simp]: "flat_ctxts xs {} = {}" unfolding flat_ctxts_def by simp

lemma root_altering_list[simp]:
  "set (fst (partition (\<lambda>(l, r). root l \<noteq> root r) trs)) = (set trs)a"
  unfolding partition_filter_conv root_altering_def by auto

lemma root_altering_list_aux[simp]:
  "set (snd (partition (\<lambda>(l, r). root l \<noteq> root r) trs)) = set trs - (set trs)a"
  unfolding partition_filter_conv root_altering_def by auto

lemma fccE[elim]:
  fixes R::"('f, string) trs"
  assumes "(s, t) \<in> FC F R"
    and ra: "(s, t) \<in> R - (R)a \<Longrightarrow> P"
    and rp: "\<exists>(l, r)\<in>(R)a. \<exists>C\<in>flat_ctxts (vars_trs R) F. s = C\<langle>l\<rangle> \<and> t = C\<langle>r\<rangle> \<Longrightarrow> P"
  shows "P"
  using assms unfolding flat_ctxts_def flat_ctxt_closure_def by force

lemma fccI_altering[intro]:
  fixes R::"('f, string) trs"
  assumes "C \<in> flat_ctxts (vars_trs R) F"
    and "(l, r) \<in> (R)a"
  shows "(C\<langle>l\<rangle>, C\<langle>r\<rangle>) \<in> FC F R"
  using assms unfolding flat_ctxt_closure_def by auto

lemma fccI_preserving[intro]:
  fixes R::"('f, string) trs"
  assumes "(l, r) \<in> R - (R)a"
  shows "(l, r) \<in> FC F R"
  using assms unfolding flat_ctxt_closure_def by simp

lemma partial_fcc_preserves_SN:
  assumes SN: "SN (qrstep nfs Q R)"
    and wwf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R"
    and refl: "\<forall>(l, r)\<in>R'. \<exists>(u, v)\<in>R. \<exists>C. l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
  shows "SN (qrstep nfs Q R')"
using SN
proof (rule contrapos_pp)
  let ?r = "qrstep nfs Q R"
  let ?c = "qrstep nfs Q R'"
  from wwf_qtrs_imp_nfs_False_switch[OF wwf] have switch: "qrstep nfs Q R = qrstep False Q R" .
  assume "\<not> SN ?c"
  then obtain t where chain: "chain ?c t" unfolding SN_defs by auto
  have "chain ?r t"
  proof
    fix i
    from chain have "(t i, t (Suc i)) \<in> ?c" by simp
    then obtain C \<sigma> l r where R': "(l, r) \<in> R'" and NF: "\<forall>s\<lhd>l \<cdot> \<sigma>. s \<in> NF_terms Q"
      and s: "t i = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t (Suc i) = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
    from R' refl have "\<exists>(u, v) \<in> R. \<exists>C. l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>" by auto
    then obtain u v C' where R: "(u, v) \<in> R" and l: "l = C'\<langle>u\<rangle>" and r: "r = C'\<langle>v\<rangle>" by auto
    from ctxt_supteq[OF l] have "l \<unrhd> u" .
    then have "l \<cdot> \<sigma> \<unrhd> u \<cdot> \<sigma>" by auto
    then have NF': "\<forall>s\<lhd>u \<cdot> \<sigma>. s \<in> NF_terms Q"
      unfolding supteq_supt_conv using NF by (auto intro: supt_trans)
    from qrstep.subst[OF NF' R] have "(u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> qrstep nfs Q R" unfolding switch by auto
    from qrstep.ctxt[OF this] show "(t i, t (Suc i)) \<in> ?r"
      unfolding s t l r by auto
  qed
  then show "\<not> SN ?r" unfolding SN_defs by auto
qed

lemma fcc_imp_refl:
  "\<forall>(l, r) \<in> FC F R. (\<exists>(u, v)\<in>R. \<exists>C. l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>)"
proof -
  {
    fix l r assume "(l, r) \<in> FC F R"
    then have "\<exists>(u,v)\<in>R. \<exists>C. l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
    proof
      assume "(l, r) \<in> R - (R)a"
      then have "(l, r) \<in> R" by simp
      moreover have "l = \<box>\<langle>l\<rangle>" by simp
      moreover have "r = \<box>\<langle>r\<rangle>" by simp
      ultimately show ?thesis by best
    next
      assume "\<exists>(x, y)\<in>(R)a. \<exists>C\<in>flat_ctxts (vars_trs R) F. l = C\<langle>x\<rangle> \<and> r = C\<langle>y\<rangle>"
      moreover have "(R)a \<subseteq> R" unfolding root_altering_def by auto
      ultimately show ?thesis by auto
    qed
  }
  then show ?thesis by auto
qed

lemma fcc_imp_pres:
  fixes R::"('f, string) trs"
    and F::"('f \<times> nat) set"
  defines "fcs \<equiv> flat_ctxts (vars_trs R) F"
  shows "\<forall>(l, r)\<in>R. (l, r) \<in> FC F R \<or> (\<forall>C\<in>fcs. (C\<langle>l\<rangle>, C\<langle>r\<rangle>) \<in> FC F R)"
proof (intro ballI2)
  fix l r assume "(l, r) \<in> R"
  then have "(l, r) \<in> (R)a \<or> (l, r) \<in> R - (R)a" by auto
  then show "(l, r) \<in> FC F R \<or> (\<forall>C\<in>fcs. (C\<langle>l\<rangle>, C\<langle>r\<rangle>) \<in> FC F R)"
  proof
    assume Ra: "(l, r) \<in> (R)a"
    then show ?thesis unfolding fcs_def using fccI_altering[of _ R F l r] by auto
  next
    assume "(l, r) \<in> R - (R)a" then show ?thesis using fccI_preserving by best
  qed
qed

lemma fcc_preserves_SN:
  assumes "SN (qrstep nfs Q R)" and "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R" shows "SN (qrstep nfs Q (FC F R))"
  using partial_fcc_preserves_SN[OF assms, of "FC F R"] fcc_imp_refl[of F R] by simp

lemma fresh_vars_subst:
  assumes "finite V" and "x \<in> set (fresh_vars n V)" shows "Var x\<cdot>(\<sigma> |s V) = Var x"
  using fresh_vars_fresh[OF \<open>finite V\<close>] assms by (auto simp: subst_restrict_def)

lemma flat_ctxt_subst_apply[simp]:
  assumes "finite V" and "C \<in> flat_ctxts V F"
  shows "C\<langle>t\<rangle>\<cdot>(\<sigma> |s V) = C\<langle>t\<cdot>(\<sigma> |s V)\<rangle>"
proof -
  from assms obtain f n i
    where i:"i<n" and fn: "(f,n)\<in>F" and C: "C = flat_ctxt_i (map Var (fresh_vars n V)) f i" (is "_ = flat_ctxt_i ?V f i")
    unfolding flat_ctxts_def by auto
  have fresh: "map (\<lambda>t. t\<cdot>(\<sigma> |s V)) ?V = ?V"
    using map_idI[of "?V" "\<lambda>t. t\<cdot>(\<sigma> |s V)"] fresh_vars_subst[OF \<open>finite V\<close>] by auto
  from C have C: "C = More f (take i ?V) \<box> (drop (Suc i) ?V)"
    unfolding flat_ctxt_i_def by simp
  show ?thesis unfolding C
    unfolding intp_actxt.simps eval_term.simps unfolding map_append
    unfolding take_map[symmetric]
    unfolding list.simps
    unfolding drop_map[symmetric]
    unfolding fresh by simp
qed

lemma flat_ctxt_has_fresh_vars:
  assumes finite: "finite V"
    and FC: "C \<in> flat_ctxts V F"
  shows "vars_ctxt C \<inter> V = {}"
proof -
  from FC obtain f n i where "(f,n) \<in> F"
    and "i < n" and "C = flat_ctxt_i (map Var (fresh_vars n V)) f i"
    (is "_ = flat_ctxt_i ?V _ _")
    unfolding flat_ctxts_def by auto
  then have C: "C = More f (take i ?V) \<box> (drop (Suc i) ?V)" unfolding flat_ctxt_i_def by simp
  have vC: "vars_ctxt C = \<Union>(set (map vars_term (take i ?V @ drop (Suc i) ?V)))" by (simp add: C)
  have"vars_ctxt C \<subseteq> \<Union>(set (map vars_term ?V))"
    using fresh_vars_length[OF finite,of n] and \<open>i < n\<close> unfolding vC
    using set_take_subset[of i ?V] set_drop_subset[of "Suc i" ?V] by auto
  then have "{Var x | x. x \<in> vars_ctxt C} \<subseteq> set ?V" unfolding fresh_vars_def by auto
  with fresh_vars_fresh[OF finite,of n] show ?thesis by auto
qed

lemma wwf_FC:
  assumes "wwf_qtrs Q R"
  shows "wwf_qtrs Q (FC F R)"
unfolding wwf_qtrs_def
proof (intro ballI2 impI)
  fix l r assume 1: "(l, r) \<in> FC F R" and applicable: "applicable_rule Q (l, r)"
  from 1 show "is_Fun l \<and> vars_term r \<subseteq> vars_term l"
  proof
    assume "(l, r) \<in> R - (R)a" with assms show ?thesis by (auto simp: applicable wwf_qtrs_def)
  next
    assume "\<exists>(l', r')\<in>(R)a. \<exists>C\<in>flat_ctxts (vars_trs R) F. l = C\<langle>l'\<rangle> \<and> r = C\<langle>r'\<rangle>"
    then obtain l' r' C where "(l',r') \<in> (R)a"
      and C: "C \<in> flat_ctxts (vars_trs R) F" and l: "l = C\<langle>l'\<rangle>" and r: "r = C\<langle>r'\<rangle>" by best
    then have R: "(l', r') \<in> R" unfolding root_altering_def by auto
    from C obtain f n i where "(f,n) \<in> F" and "i < n"
      and "C = flat_ctxt_i (map Var (fresh_vars n (vars_trs R))) f i"
      (is "C = flat_ctxt_i ?V f i") unfolding flat_ctxts_def by auto
    then have C: "C = More f (take i ?V) \<box> (drop (Suc i) ?V)" unfolding flat_ctxt_i_def by simp
    then have "l = Fun f (take i ?V@l'#drop (Suc i) ?V)" unfolding l by simp
    then have "is_Fun l" by auto
    moreover have "vars_term r \<subseteq> vars_term l"
    proof -
      from applicable have "applicable_rule Q (l', r')" unfolding l r applicable_rule_def
        using NF_terms_ctxt[of C l' Q] by simp
      with R and assms have "vars_term r' \<subseteq> vars_term l'" by (auto simp: wwf_qtrs_def)
      with l r show ?thesis unfolding C by auto
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma wf_FC:
  assumes "wf_trs R"
  shows "wf_trs (FC F R)"
  using assms wwf_FC[of "{}", unfolded wwf_qtrs_empty] by blast

lemma fc_flat:
  assumes C: "C \<in> flat_ctxts V F"
    and finite: "finite V"
  shows "vars_ctxt C \<inter> V = {} \<and> (\<exists>f ss1 ss2. C = More f ss1 \<box> ss2
    \<and> (f, Suc (length (ss1 @ ss2))) \<in> F
    \<and> (\<forall>t\<in>set (ss1 @ ss2). is_Var t)
    \<and> distinct (ss1 @ ss2))"
proof -
  from C obtain g i m where "i < m" and "(g,m) \<in> F"
    and C': "C = More g (take i (map Var (fresh_vars m V))) \<box> (drop (Suc i) (map Var (fresh_vars m V)))" (is "C = More g ?ss1 \<box> ?ss2")
    unfolding flat_ctxts_def flat_ctxt_i_def by auto
  from flat_ctxt_has_fresh_vars[OF finite C] have fresh: "vars_ctxt C \<inter> V = {}" .
  from fresh_vars_length[OF finite] have len: "length(fresh_vars m V) = m" by simp
  from fresh_vars_distinct[OF finite] have dist: "distinct(fresh_vars m V)" by simp
  from length_take[of i "fresh_vars m V"] \<open>i < m\<close> have take: "length(?ss1) = i" unfolding len by simp
  from length_drop[of "Suc i" "fresh_vars m V"] have drop: "length(?ss2) = length(fresh_vars m V) - Suc i" by simp
  from take drop have m: "Suc(length(?ss1@?ss2)) = m" unfolding len using \<open>i < m\<close> by simp
  have F:"(g,Suc(length(?ss1@?ss2))) \<in> F" using \<open>(g,m) \<in> F\<close> unfolding m .
  have "\<forall>t\<in>set ?ss1. is_Var t" unfolding take_map by auto
  moreover have "\<forall>t\<in>set ?ss2. is_Var t" unfolding drop_map by auto
  ultimately have is_Var: "\<forall>t\<in>set (?ss1@?ss2). is_Var t" by auto
  have dist: "distinct(?ss1@?ss2)" using distinct_take_drop[OF dist,unfolded len,OF \<open>i < m\<close>]
    unfolding take_map drop_map map_append[symmetric] by (rule distinct_map_Var)
  with fresh C' F is_Var dist show ?thesis by auto
qed

fun is_flat_ctxt :: "'v set \<Rightarrow> ('f \<times> nat) set \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> bool" where
  "is_flat_ctxt V F (More f ss1 \<box> ss2) = (
          (f, Suc (length (ss1 @ ss2))) \<in> F
        \<and> (\<forall>s\<in>set (ss1 @ ss2). is_Var s)
        \<and> distinct (ss1 @ ss2)
        \<and> vars_ctxt (More f ss1 \<box> ss2) \<inter> V = {}
      )"
| "is_flat_ctxt V F _ = False"

lemma is_flat_ctxt_union: "is_flat_ctxt (V \<union> W) F C = (is_flat_ctxt V F C \<and> is_flat_ctxt W F C)"
proof (cases C)
  case Hole
  show ?thesis unfolding Hole by simp
next
  case (More f bef D aft)
  show ?thesis unfolding More by (cases D, auto)
qed

lemma is_flat_ctxt_cases[consumes 1,case_names True]:
  assumes "is_flat_ctxt V F C"
    and "\<And>f ss1 ss2. C = More f ss1 \<box> ss2 \<Longrightarrow> P"
  shows "P"
using assms(1) proof (cases rule: is_flat_ctxt.cases[of "(V,F,C)"])
  case (1 V' F' f ss1 ss2)
  then have "C = More f ss1 \<box> ss2" by simp
  with assms(2) show ?thesis by auto
next
  case ("2_1" V' F') with assms(1) show ?thesis by simp
next
  case ("2_2" V' F' f ss1 g ts1 D ts2 ss2) with assms(1) show ?thesis by simp
qed

lemma is_flat_ctxt_imp_flat_ctxt:
  assumes "is_flat_ctxt V F C"
  shows "vars_ctxt C \<inter> V = {} \<and> (\<exists>f ss1 ss2. C = More f ss1 \<box> ss2
          \<and> (f, Suc (length(ss1 @ ss2))) \<in> F
          \<and> (\<forall>s\<in>set (ss1 @ ss2). is_Var s)
          \<and> distinct (ss1 @ ss2))"
  using assms by (cases rule: is_flat_ctxt_cases, auto)

lemma subst_extend_flat_ctxt':
  assumes dist: "distinct(vs1@vs2)"
    and len1: "length vs1 = length ss1"
    and len2: "length vs2 = length ss2"
  shows "More f (map Var vs1) \<box> (map Var vs2) \<cdot>\<^sub>c subst_extend \<sigma> (zip (vs1@vs2) (ss1@ss2)) = More f ss1 \<box> ss2"
proof -
  let ?V = "map Var (vs1@vs2)"
  let ?vs1 = "vs1" and ?vs2 = "vs2"
  let ?ss1 = "map Var vs1" and ?ss2 = "map Var vs2"
  let ?\<sigma> = "subst_extend \<sigma> (zip (?vs1@?vs2) (ss1@ss2))"
  from len1 and len2 have len: "length(?vs1@?vs2) = length(ss1@ss2)" by simp
  from subst_extend_absorb[OF dist len,of "\<sigma>"] have map: "map (\<lambda>t. t\<cdot>?\<sigma>) (?ss1@?ss2) = ss1@ss2" unfolding map_append .
  from len1 and map have "map (\<lambda>t. t\<cdot>?\<sigma>) ?ss1 = ss1" by auto
  moreover from len2 and map have "map (\<lambda>t. t\<cdot>?\<sigma>) ?ss2 = ss2" by auto
  ultimately show ?thesis by simp
qed


lemma partial_fcc_sig_step:
  assumes flat_ctxts: "\<forall>C\<in>fcs. is_flat_ctxt (vars_trs R) F C"
    and complete: "\<forall>(f, n)\<in>F. \<forall>i<n. \<exists>ss1 ss2. (More f ss1 \<box> ss2) \<in> fcs \<and> length ss1 = i \<and>
                   length ss2 = n - i - 1"
    and subset: "funas_trs R \<subseteq> F"
    and C: "C \<in> fcs"
    and pres: "\<forall>(l, r)\<in>R. (Bex R' (instance_rule (l, r))) \<or> (\<forall>C\<in>fcs. Bex R' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
    and step: "(s,t) \<in> sig_step F (rstep R)"
  shows "(C\<langle>s\<rangle>,C\<langle>t\<rangle>) \<in> rstep R'"
proof -
  let ?r = "sig_step F (rstep R)"
  let ?c = "rstep R'"
  from sig_stepE[OF step] subset
  have rstep: "(s,t) \<in> rstep R" and wfs: "funas_term s \<subseteq> F"
      and wft: "funas_term t \<subseteq> F" by auto
  from rstep_imp_C_s_r[OF rstep] obtain D \<sigma> l r where R: "(l,r) \<in> R"
    and s: "s = D\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = D\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  have vl: "vars_term l \<subseteq> vars_trs R"
    using R unfolding vars_trs_def vars_rule_def [abs_def] by auto
  have vr: "vars_term r \<subseteq> vars_trs R"
    using R unfolding vars_trs_def vars_rule_def [abs_def] by auto
  from flat_ctxts[THEN bspec[where x=C],OF C] have distinct: "vars_ctxt C \<inter> vars_trs R = {}"
    using is_flat_ctxt_imp_flat_ctxt by best
  from R pres have "(Bex R' (instance_rule (l,r))) \<or> (\<forall>C\<in>fcs. Bex R' (instance_rule (C\<langle>l\<rangle>,C\<langle>r\<rangle>)))" by auto
  then show "(C\<langle>s\<rangle>,C\<langle>t\<rangle>) \<in> ?c"
  proof
    assume bex: "Bex R' (instance_rule (l,r))"
    have "(D\<langle>l\<cdot>\<sigma>\<rangle>,D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep {(l,r)}" by auto
    then have "(D\<langle>l\<cdot>\<sigma>\<rangle>,D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> ?c"
      by (rule instance_rule_rstep[OF _ bex])
    from rstep_ctxt[OF this] show ?thesis unfolding s t by simp
  next
    assume closed: "\<forall>C\<in>fcs. Bex R' (instance_rule (C\<langle>l\<rangle>,C\<langle>r\<rangle>))"
    show ?thesis
    proof (cases D rule: ctxt_exhaust_rev)
      case Hole
      let ?\<sigma> = "\<sigma> |s (vars_trs R)"
      from C and closed have inst: "Bex R' (instance_rule (C\<langle>l\<rangle>,C\<langle>r\<rangle>))" by auto
      have "(C\<langle>l\<rangle>\<cdot>?\<sigma>,C\<langle>r\<rangle>\<cdot>?\<sigma>) \<in> ?c"
        by (rule instance_rule_rstep[OF _ inst], blast) 
      then have mem: "((C \<cdot>\<^sub>c ?\<sigma>)\<langle>l\<cdot>?\<sigma>\<rangle>, (C \<cdot>\<^sub>c ?\<sigma>)\<langle>r\<cdot>?\<sigma>\<rangle>) \<in> ?c" by simp
      have "l \<cdot> ?\<sigma> = l \<cdot> \<sigma>" and "r \<cdot> ?\<sigma> = r \<cdot> \<sigma>"
        unfolding term_subst_eq_conv using vl vr unfolding subst_restrict_def
        by auto
      with mem have "((C \<cdot>\<^sub>c ?\<sigma>)\<langle>l\<cdot>\<sigma>\<rangle>, (C \<cdot>\<^sub>c ?\<sigma>)\<langle>r\<cdot>\<sigma>\<rangle>) \<in> ?c" by auto
      then show ?thesis unfolding subst_apply_ctxt_id[OF distinct] unfolding s t Hole by simp
    next
      case (More E f ss1 ss2)
      from wfs[unfolded s]
      have D: "funas_ctxt D \<subseteq> F" and "funas_term (l\<cdot>\<sigma>) \<subseteq> F" by auto
      from D[unfolded More]
      have "funas_ctxt E \<subseteq> F" and "funas_ctxt (More f ss1 \<box> ss2) \<subseteq> F" by auto
      then have F: "(f,Suc(length(ss1@ss2))) \<in> F" (is "(f,?n) \<in> _")
        by auto
      have len: "length ss1 < ?n" (is "?i < _") by simp
      from complete[THEN bspec[where x="(f,?n)"],OF F] len
      obtain  ts1 ts2 where C': "More f ts1 \<box> ts2 \<in> fcs" (is "?C' \<in> fcs")
        and "length ts1 = ?i" and "length ts2 = ?n - ?i - 1" by best
      note inst = instance_rule_rstep[OF _ closed[THEN bspec[OF _ C']]]
      have len_ss1: "length ss1 = length ts1" using \<open>length ts1 = ?i\<close> by simp
      have len_ss2: "length ss2 = length ts2" using \<open>length ts2 = ?n - ?i - 1\<close> by simp
      have len_ss1ss2: "length(ss1@ss2) = length(ts1@ts2)" using len_ss1 len_ss2 by simp
      let ?V = "map the_Var (ts1@ts2)"
      let ?\<sigma> = "subst_extend \<sigma> (zip ?V (ss1@ss2))"
      from is_flat_ctxt_imp_flat_ctxt[OF flat_ctxts[THEN bspec,OF C']]
      have is_Var: "\<forall>t\<in>set (ts1 @ ts2). is_Var t"
        and fresh: "vars_ctxt ?C' \<inter> vars_trs R = {}" by auto
      have vars_C': "vars_ctxt ?C' = set ?V" using terms_to_vars[OF is_Var] by simp
      from fresh have fresh: "vars_trs R \<inter> set ?V = {}" unfolding vars_C' by auto
      from is_flat_ctxt_imp_flat_ctxt[OF flat_ctxts[THEN bspec,OF C']]
      have "\<forall>t\<in>set (ts1 @ ts2). is_Var t" and "distinct(ts1@ts2)" by auto
      then have "distinct ?V" by (rule distinct_the_vars)
      then have dist: "distinct(map the_Var ts1 @ map the_Var ts2)" by simp
      have len1: "length(map the_Var ts1) = length ss1" unfolding len_ss1 by simp
      have len2: "length(map the_Var ts2) = length ss2" unfolding len_ss2 by simp
      from is_Var have "\<forall>t\<in>set ts1. is_Var t" by simp
      then have id1: "map Var (map the_Var ts1) = ts1" by (rule Var_the_Var_id)
      from is_Var have "\<forall>t\<in>set ts2. is_Var t" by simp
      then have id2: "map Var (map the_Var ts2) = ts2" by (rule Var_the_Var_id)
      have Cl: "(?C'\<langle>l\<rangle>)\<cdot>?\<sigma> = (More f ss1 \<box> ss2)\<langle>l\<cdot>\<sigma>\<rangle>"
        unfolding subst_apply_term_ctxt_apply_distrib subst_extend_id[OF fresh vl,of \<sigma>]
        unfolding map_append subst_extend_flat_ctxt'[OF dist len1 len2,unfolded id1 id2] by simp
      have Cr: "(?C'\<langle>r\<rangle>)\<cdot>?\<sigma> = (More f ss1 \<box> ss2)\<langle>r\<cdot>\<sigma>\<rangle>"
        unfolding subst_apply_term_ctxt_apply_distrib subst_extend_id[OF fresh vr,of \<sigma>]
        unfolding map_append subst_extend_flat_ctxt'[OF dist len1 len2,unfolded id1 id2] by simp
      let ?C'' = "More f ss1 \<box> ss2"
      have "(?C''\<langle>l\<cdot>\<sigma>\<rangle>,?C''\<langle>r\<cdot>\<sigma>\<rangle>) \<in> ?c"
        by (rule inst, unfold Cl[symmetric] Cr[symmetric], blast)
      from ctxt.closure.intros[OF this,of E] have "(E\<langle>?C''\<langle>l\<cdot>\<sigma>\<rangle>\<rangle>,E\<langle>?C''\<langle>r\<cdot>\<sigma>\<rangle>\<rangle>) \<in> ?c" by simp
      from ctxt.closure.intros[OF this,of C] have "(C\<langle>E\<langle>?C''\<langle>l\<cdot>\<sigma>\<rangle>\<rangle>\<rangle>,C\<langle>E\<langle>?C''\<langle>r\<cdot>\<sigma>\<rangle>\<rangle>\<rangle>) \<in> ?c" by simp
      then show ?thesis unfolding s t More by simp
    qed
  qed
qed

lemma partial_fcc_reflects_SN_rel: fixes R S R' S' :: "('f,'v)trs"
  assumes flat_ctxts: "\<forall>C\<in>fcs. is_flat_ctxt (vars_trs (R \<union> S)) F C"
    and complete: "\<forall>(f, n)\<in>F. \<forall>i<n. \<exists>ss1 ss2. (More f ss1 \<box> ss2) \<in> fcs \<and> length ss1 = i \<and>
    length ss2 = n - i - 1"
    and F: "funas_trs (R \<union> S) \<subseteq> F"
    and ne: "fcs \<noteq> {}"
    and presR: "\<forall>(l, r)\<in>R. (Bex R' (instance_rule (l, r))) \<or> (\<forall>C\<in>fcs. Bex R' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
    and presS: "\<forall>(l, r)\<in>S. (Bex (R' \<union> S') (instance_rule (l, r))) \<or> (\<forall>C\<in>fcs. Bex (R' \<union> S') (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
    and SN: "SN_rel (rstep R') (rstep S')"
  shows "SN_rel (rstep R) (rstep S)"
proof -
  from ne obtain C where C: "C \<in> fcs" by auto
  let ?r = "sig_step F (rstep R)"
  let ?s = "sig_step F (rstep S)"
  let ?r' = "rstep R'"
  let ?s' = "rstep S'"
  let ?c = "\<lambda> t. C\<langle>t\<rangle>"
  note fcc = partial_fcc_sig_step[OF _ complete _ C]
  from F have FR: "funas_trs R \<subseteq> F" and FS: "funas_trs S \<subseteq> F" by auto
  have relSN: "SN_rel (?r) (?s)"
  proof (rule SN_rel_map[OF SN, of _ ?c])
    fix s t
    assume step: "(s,t) \<in> ?r"
    from flat_ctxts have flat_ctxt: "\<forall> C \<in> fcs. is_flat_ctxt (vars_trs R) F C"
      unfolding vars_trs_union is_flat_ctxt_union by auto
    from F have F: "funas_trs R \<subseteq> F" by auto
    have "(?c s, ?c t) \<in> ?r'"
      by (rule fcc[OF flat_ctxt F presR step])
    then show "(?c s, ?c t) \<in> (?r' \<union> ?s')^* O ?r' O (?r' \<union> ?s')^*" by auto
  next
    fix s t
    assume "(s,t) \<in> ?s"
    then have step: "(s,t) \<in> sig_step F (rstep (R \<union> S))" unfolding rstep_union sig_step_def  by auto
    have "(?c s, ?c t) \<in> rstep (R' \<union> S')"
      by (rule fcc[OF flat_ctxts F _ step], insert presR presS, force)
    then show "(?c s, ?c t) \<in> (?r' \<union> ?s')^*" unfolding rstep_union by auto
  qed
  show ?thesis
  proof (cases "R = {}")
    case True
    then show ?thesis by (simp add: SN_rel_defs)
  next
    case False
    with presR C have ne: "R' \<noteq> {}" by auto
    with SN_rel_imp_wf_reltrs[OF SN] have
      varcond: "\<And> l r. (l,r) \<in> R' \<union> S' \<Longrightarrow> vars_term r \<subseteq> vars_term l" by (force simp: wf_trs_def)
    show ?thesis
    proof (rule sig_ext_relative_rewriting_var_cond[OF _ FR FS relSN])
      fix l r
      assume lr: "(l,r) \<in> S"
      from presS[rule_format, OF lr, unfolded split]
      show "vars_term r \<subseteq> vars_term l"
      proof
        assume "Bex (R' \<union> S') (instance_rule (l, r))"
        then obtain l' r' \<sigma> where mem: "(l',r') \<in> R' \<union> S'" and lr: "l = l' \<cdot> \<sigma>" "r = r' \<cdot> \<sigma>"
          by (force simp: instance_rule_def)
        from varcond[OF mem] show ?thesis unfolding lr by (auto simp: vars_term_subst)
      next
        assume "\<forall>C\<in>fcs. Bex (R' \<union> S') (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>))"
        with C obtain l' r' where mem: "(l',r') \<in> R' \<union> S'" 
          and inst: "instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>) (l',r')" by force
        from inst[unfolded instance_rule_def] obtain \<sigma> where id: "C\<langle>l\<rangle> = l' \<cdot> \<sigma>" "C\<langle>r\<rangle> = r' \<cdot> \<sigma>" by auto
        from varcond[OF mem] have vars: "vars_term r' \<subseteq> vars_term l'" .
        from flat_ctxts[rule_format,OF C] have distinct: "vars_ctxt C \<inter> vars_trs (R \<union> S) = {}"
          using is_flat_ctxt_imp_flat_ctxt by best
        show ?thesis
        proof
          fix x
          assume x: "x \<in> vars_term r"
          then have "x \<in> vars_term C\<langle>r\<rangle>" unfolding vars_term_ctxt_apply by auto
          with vars id have "x \<in> vars_term C\<langle>l\<rangle>" by (auto simp: vars_term_subst)
          then have xx: "x \<in> vars_ctxt C \<union> vars_term l" unfolding vars_term_ctxt_apply .
          from x lr have "x \<in> vars_trs (R \<union> S)"
            unfolding vars_trs_def vars_rule_def [abs_def] by force
          with distinct xx show "x \<in> vars_term l" by auto
        qed
      qed
    qed
  qed
qed

lemma flat_ctxt_is_flat:
  assumes fin: "finite V" and fc: "C \<in> flat_ctxts V F"
  shows "is_flat_ctxt V F C"
  using fc_flat[OF fc fin] by auto

lemma fcc_reflects_SN_rel:
  assumes finite: "finite (R \<union> S)"
    and subset: "funas_trs (R \<union> S) \<subseteq> G"
    and ne: "flat_ctxts (vars_trs (R \<union> S)) G \<noteq> {}" (is "?fcs \<noteq> {}")
    and SN: "SN_rel (rstep(FC G R)) (rstep (FC G S))"
  shows "SN_rel (rstep R) (rstep S)"
proof -
  from finite have fin: "finite(vars_trs (R \<union> S))"
    unfolding vars_trs_def vars_rule_def [abs_def] by auto
  have fcs: "\<forall>C\<in>?fcs. is_flat_ctxt (vars_trs (R \<union> S)) G C" using flat_ctxt_is_flat[OF fin] by best
  have complete: "\<forall>(f,n)\<in>G.\<forall>i<n.\<exists>ss1 ss2. More f ss1 \<box> ss2 \<in> ?fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1"
  proof (intro ballI2 allI impI)
    fix f n i
    let ?V = "map Var (fresh_vars n (vars_trs (R \<union> S)))"
    assume "(f,n) \<in> G" and "i < n"
    then have "flat_ctxt_i ?V f i \<in> ?fcs" unfolding flat_ctxts_def by auto
    then have "More f (take i ?V) \<box> (drop (Suc i) ?V) \<in> ?fcs" (is "More f ?ss1 \<box> ?ss2 \<in> _") unfolding flat_ctxt_i_def by auto
    moreover have "length ?ss1 = i" using fresh_vars_length[OF fin,of n] \<open>i < n\<close> by simp
    moreover have "length ?ss2 = n - i - 1" using fresh_vars_length[OF fin,of n] \<open>i < n\<close> by simp
    ultimately show "\<exists>ss1 ss2. More f ss1 \<box> ss2 \<in> ?fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1" by best
  qed
  from partial_fcc_reflects_SN_rel[OF fcs complete subset ne _  _ SN]
    fcc_imp_pres show ?thesis oops

(*
lemma SN_iff_fcc_SN:
  assumes "finite R" and "funas_trs R \<subseteq> G" and "flat_ctxts (vars_trs R) G \<noteq> {}"
  shows "SN (rstep R) = SN (rstep (FC G R))"
  using fcc_reflects_SN[OF assms] fcc_preserves_SN[of "{}", unfolded qrstep_rstep_conv]
  by blast
*)

lemma fcc_ne_imp_funs_ne:
  assumes ne: "flat_ctxts V (funas_trs R) \<noteq> {}"
  shows "funs_trs R \<noteq> {}"
proof -
  from ne have "funas_trs R \<noteq> {}" unfolding flat_ctxts_def by auto
  then obtain l r where R: "(l,r) \<in> R" and "funas_term l \<union> funas_term r \<noteq> {}"
    unfolding funas_rule_def [abs_def] funas_trs_def by force
  then have "funas_term l \<noteq> {} \<or> funas_term r \<noteq> {}" by simp
  then show "funs_trs R \<noteq> {}"
  proof
    assume "funas_term l \<noteq> {}"
    then obtain f ss where "l = Fun f ss" by (induct l) auto
    then have "f \<in> funs_term l" by simp
    with R show ?thesis unfolding funs_trs_def funs_rule_def [abs_def] by force
  next
    assume "funas_term r \<noteq> {}"
    then obtain f ss where "r = Fun f ss" by (induct r) auto
    then have "f \<in> funs_term r" by simp
    with R show ?thesis unfolding funs_trs_def funs_rule_def [abs_def] by force
  qed
qed

fun hole_at where
  "hole_at n i f (More g ss1 \<box> ss2) = (g = f \<and> length ss1 = i \<and> length ss2 = n - i - 1)"
| "hole_at n i f _ = False"

fun has_unary_root :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "has_unary_root f (Fun g [t]) = (f = g)"
| "has_unary_root f t = False"

fun strip_unary_root :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "strip_unary_root f (Fun g [t]) = (if f = g then t else Fun g [t])"
| "strip_unary_root f t = t"

fun block_term :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "block_term f (Var x) = Var x"
| "block_term f (Fun g ts) = Fun g (map (\<lambda>t. Fun f [t]) ts)"

definition block_rule :: "'f \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('f, 'v) rule" where
  "block_rule f r = (block_term f (fst r), block_term f (snd r))"

fun unblock_term :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "unblock_term f (Fun g ts) = (if \<forall>t\<in>set ts. has_unary_root f t
     then Fun g (map (strip_unary_root f) ts)
     else Fun g ts)"
| "unblock_term f t = t"

lemma [simp]: "strip_unary_root f \<circ> (\<lambda>t. Fun f [t]) = id"
  by (rule ext) (simp add: o_def)

lemma unblock_block_term_ident[simp]: "unblock_term f (block_term f t) = t"
  by (cases t) (simp_all)

definition unblock_rule :: "'f \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('f, 'v) rule" where
  "unblock_rule f r \<equiv> (unblock_term f (fst r), unblock_term f (snd r))"

lemma subst_apply_term_block_term_distrib[simp]:
  assumes "is_Fun t"
  shows "block_term f t \<cdot> \<sigma> = block_term f (t \<cdot> \<sigma>)"
using assms by (cases t) simp_all

lemma blocked_rstep_imp_rstep:
  assumes refl: "\<forall>(l, r)\<in>R'. \<exists>(u, v)\<in>R. \<exists>C\<in>set (\<box> # fcs). l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
    and rstep: "(s, t) \<in> rstep R'"
  shows "(s, t) \<in> rstep R"
proof -
  from rstep obtain C l r \<sigma> where "(l, r) \<in> R'"
    and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  from refl and \<open>(l, r) \<in> R'\<close>
    have "(l, r) \<in> R \<or> (\<exists>(u, v)\<in>R. \<exists>C\<in>set fcs. l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>)" by auto
  then show ?thesis
  proof
    assume "(l, r) \<in> R" then show "(s, t) \<in> rstep R" unfolding s t by auto
  next
    assume "\<exists>(u, v)\<in>R. \<exists>C\<in>set fcs. l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
    then obtain u v D where "(u, v) \<in> R" and "D \<in> set fcs" and l: "l = D\<langle>u\<rangle>" and r: "r = D\<langle>v\<rangle>" by auto
    let ?C = "C \<circ>\<^sub>c (D \<cdot>\<^sub>c \<sigma>)"
    have s': "s = ?C\<langle>u\<cdot>\<sigma>\<rangle>" unfolding s l by simp
    have t': "t = ?C\<langle>v\<cdot>\<sigma>\<rangle>" unfolding t r by simp
    from \<open>(u, v) \<in> R\<close> show "(s, t) \<in> rstep R" unfolding s' t' by best
  qed
qed

lemma unary_flat_ctxts:
  assumes "(f, Suc 0) \<in> F"
  shows "More f [] \<box> [] \<in> flat_ctxts V F"
proof -
  let ?xs = "map Var (fresh_vars (Suc 0) V)"
  have "flat_ctxt_i ?xs f 0 = More f [] \<box> []"
    unfolding flat_ctxt_i_def fresh_vars_def fresh_strings_def by simp
  with assms show ?thesis unfolding flat_ctxts_def by force
qed

lemma flat_ctxts_funas:
  fixes n::nat and V::"string set"
  defines "xs \<equiv> map Var (fresh_vars n V)"
  assumes "(f, n) \<in> F"
  shows "\<forall>i<n. More f (take i xs) \<box> (drop (Suc i) xs) \<in> flat_ctxts V F"
proof (intro allI impI)
  fix i assume "i < n"
  then have "flat_ctxt_i xs f i = More f (take i xs) \<box> (drop (Suc i) xs)"
    unfolding flat_ctxt_i_def xs_def by simp
  with \<open>i < n\<close>
    have "More f (take i xs) \<box> (drop (Suc i) xs) \<in> {flat_ctxt_i xs f i | i. i \<in> {0..<n}}"
    unfolding xs_def by force
  with assms show "More f (take i xs) \<box> (drop (Suc i) xs) \<in> flat_ctxts V F"
    unfolding flat_ctxts_def xs_def by force
qed  

lemma rstep_imp_blocked_rstep_union:
  assumes "wf_trs (R \<union> Rw)"
    and flat_ctxts: "\<forall>C\<in>fcs. is_flat_ctxt (vars_trs (R \<union> Rw)) F C"
    and complete: "\<forall>(f, n)\<in>F. \<forall>i<n. \<exists>ss1 ss2.
      (More f ss1 \<box> ss2) \<in> fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1"
    and "funas_args_term s \<subseteq> funas_trs (R \<union> Rw) \<union> funas_args_trs P"
    and "funas_trs (R \<union> Rw) \<union> funas_args_trs P \<subseteq> F"
    and "(f, Suc 0) \<in> F"
    and "\<not> defined (R \<union> Rw) (the(root s))"
    and "(s, t) \<in> rstep R"
    and pres: "\<forall>(l, r)\<in>R. (Bex R' (instance_rule (l, r))) \<or> (\<forall>E\<in>fcs. Bex R' (instance_rule (E\<langle>l\<rangle>, E\<langle>r\<rangle>)))"
  shows "\<not> defined (R \<union> Rw) (the(root t)) \<and> funas_args_term t \<subseteq> funas_trs (R \<union> Rw) \<union> funas_args_trs P
    \<and> (block_term f s, block_term f t) \<in> rstep R'" (is "_ \<and> _ \<and> (?s, ?t) \<in> rstep R'")
proof -
  let ?R = "R \<union> Rw"
  from \<open>(s, t) \<in> rstep R\<close> obtain C l r \<sigma> where "(l, r) \<in>  R"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  from \<open>wf_trs ?R\<close> and \<open>(l, r) \<in> R\<close> obtain g ls
    where l: "l = Fun g ls" by (cases l) (auto simp: wf_trs_def)
  show ?thesis
  proof (cases C)
    case Hole
    have "the(root s) = (g, length ls)" by (simp add: s l Hole)
    with \<open>(l, r) \<in> R\<close> l Hole s have "defined ?R (the(root s))" by (auto simp: defined_def l)
    with assms show ?thesis by simp
  next
    case (More h ss1 D ss2)
    note C = this
    let ?block_list = "map (\<lambda>t. Fun f [t])"
    let ?ss1 = "?block_list ss1"
    let ?ss2 = "?block_list ss2"
    let ?D = "More h ?ss1 (More f [] D []) ?ss2"
    have s': "?s = ?D\<langle>l\<cdot>\<sigma>\<rangle>" by (simp add: s More)
    have t': "?t = ?D\<langle>r\<cdot>\<sigma>\<rangle>" by (simp add: t More)
    have "the (root s) = (h, num_args s)" unfolding s More by simp
    moreover have "the(root t) = (h, num_args t)" unfolding t More by simp
    moreover have "num_args s = num_args t" unfolding s t More by simp
    ultimately have no_def: "\<not> defined ?R (the (root t))" using assms by simp
    have funas_args: "funas_args_term t \<subseteq> funas_trs ?R \<union> funas_args_trs P"
    proof -
      have "funas_args_term t = \<Union>(set (map funas_term (ss1 @ (D\<langle>r \<cdot> \<sigma>\<rangle>) # ss2 )))"
        unfolding t More funas_args_term_def by simp
      moreover have "funas_term (D\<langle>r \<cdot> \<sigma>\<rangle>) \<subseteq> funas_trs ?R \<union> funas_args_trs P"
      proof -
        from \<open>funas_args_term s \<subseteq> funas_trs ?R \<union> funas_args_trs P\<close>
          have fs: "funas_term (D\<langle>l \<cdot> \<sigma>\<rangle>) \<subseteq> funas_trs ?R \<union> funas_args_trs P"
          unfolding s C funas_args_term_def by simp
        from fs
          have "(\<Union>x\<in>vars_term l. funas_term (Var x \<cdot> \<sigma>)) \<subseteq> funas_trs ?R \<union> funas_args_trs P"
          unfolding funas_term_subst funas_term_ctxt_apply by simp
        moreover from \<open>(l, r) \<in> R\<close> and \<open>wf_trs ?R\<close>
          have "vars_term r \<subseteq> vars_term l" unfolding wf_trs_def by simp
        ultimately
          have "(\<Union>x\<in>vars_term r. funas_term (Var x \<cdot> \<sigma>)) \<subseteq> funas_trs ?R \<union> funas_args_trs P"
          by auto
        moreover from \<open>(l, r) \<in> R\<close> have "funas_term r \<subseteq> funas_trs ?R"
          unfolding funas_defs [abs_def] by auto
        ultimately have "funas_term (r \<cdot> \<sigma>) \<subseteq> funas_trs ?R \<union> funas_args_trs P"
          unfolding funas_term_subst by auto
        moreover from fs have "funas_ctxt D \<subseteq> funas_trs ?R \<union> funas_args_trs P"
          unfolding s More funas_term_ctxt_apply by simp
        ultimately show ?thesis unfolding funas_term_ctxt_apply by simp
      qed
      ultimately show ?thesis using \<open>funas_args_term s \<subseteq> funas_trs ?R \<union> funas_args_trs P\<close>
        unfolding s C funas_args_term_def by simp
    qed
    from bspec[OF pres \<open>(l, r) \<in> R\<close>, unfolded split_def fst_conv snd_conv] show ?thesis
    proof
      assume inst: "Bex R' (instance_rule (l, r))"
      have "(block_term f s, block_term f t) \<in> rstep {(l,r)}"
        unfolding s' t' by best
      from instance_rule_rstep[OF this inst]
      show ?thesis using no_def funas_args by auto
    next
      assume flat_ctxt: "\<forall>E\<in>fcs. Bex R' (instance_rule (E\<langle>l\<rangle>, E\<langle>r\<rangle>))"
      show ?thesis
      proof (cases D rule: ctxt_exhaust_rev)
        case Hole
        let ?E = "More f [] \<box> []"
        let ?F = "More h ?ss1 \<box> ?ss2"
        from \<open>(f, Suc 0) \<in> F\<close> and complete
          have "More f [] \<box> [] \<in> fcs" by auto
        with flat_ctxt
        have inst: "Bex R' (instance_rule (?E\<langle>l\<rangle>, ?E\<langle>r\<rangle>))" by best
        have "((?E\<langle>l\<rangle>)\<cdot>\<sigma>, (?E\<langle>r\<rangle>)\<cdot>\<sigma>) \<in> rstep R'"
          by (rule instance_rule_rstep[OF _ inst], blast)
        then have "(?E\<langle>l\<cdot>\<sigma>\<rangle>, ?E\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R'" by simp
        from rstep_ctxt[OF this]
          have "(?F\<langle>?E\<langle>l\<cdot>\<sigma>\<rangle>\<rangle>, ?F\<langle>?E\<langle>r\<cdot>\<sigma>\<rangle>\<rangle>) \<in> rstep R'" .
        then have "(?s, ?t) \<in> rstep R'" unfolding s' t' Hole by simp
        with no_def and funas_args show ?thesis by simp
      next
        case (More D' f' ss1' ss2')
        let ?n = "Suc (length (ss1' @ ss2'))"
        let ?i = "length ss1'"
        from \<open>(l, r) \<in> R\<close>
          have vl: "vars_term l \<subseteq> vars_trs R"
          and vr: "vars_term r \<subseteq> vars_trs R"
          unfolding vars_defs [abs_def] by auto
        from vl have l_subst_R: "l \<cdot> (\<sigma> |s vars_trs R) = l \<cdot> \<sigma>"
          unfolding term_subst_eq_conv subst_restrict_def by auto
        from vr have r_subst_R: "r \<cdot> (\<sigma> |s vars_trs R) = r \<cdot> \<sigma>"
          unfolding term_subst_eq_conv subst_restrict_def by auto
        from \<open>funas_args_term s \<subseteq> funas_trs ?R \<union> funas_args_trs P\<close>
          and \<open>funas_trs ?R \<union> funas_args_trs P \<subseteq> F\<close>
          have "funas_args_term s \<subseteq> F" by blast
        then have in_F: "(f', ?n) \<in> F"
          unfolding funas_args_term_def s C More by simp
        have "?i < ?n" by simp
        with in_F and complete obtain ss1 ss2 where "More f' ss1 \<box> ss2 \<in> fcs" (is "?G \<in> _")
          and "length ss1 = ?i" and "length ss2 = ?n - ?i - 1" by best
        with flat_ctxt have in_R': "Bex R' (instance_rule (?G\<langle>l\<rangle>, ?G\<langle>r\<rangle>))" by best
        from flat_ctxts and \<open>?G \<in> fcs\<close> have "is_flat_ctxt (vars_trs ?R) F ?G" by best
        from is_flat_ctxt_imp_flat_ctxt[OF this]
          have dist_vars: "vars_ctxt ?G \<inter> vars_trs ?R = {}"
          and "(f', Suc (length (ss1 @ ss2))) \<in> F"
          and all_vars: "\<forall>s\<in>set (ss1 @ ss2). is_Var s"
          and "distinct (ss1 @ ss2)" by auto
        let ?ss1' = "map the_Var ss1"
        let ?ss2' = "map the_Var ss2"
        from all_vars have "\<forall>s\<in>set ss1. is_Var s" by simp
        from all_vars have "\<forall>s\<in>set ss2. is_Var s" by simp
        from dist_vars have "\<Union>(set (map vars_term ss1)) \<inter> vars_trs ?R = {}" by auto
        with \<open>\<forall>s\<in>set ss1. is_Var s\<close> have "set ?ss1' \<inter> vars_trs ?R = {}" by (induct ss1) auto
        moreover from dist_vars have "\<Union>(set (map vars_term ss2)) \<inter> vars_trs ?R = {}" by auto
        with \<open>\<forall>s\<in>set ss2. is_Var s\<close> have "set ?ss2' \<inter> vars_trs ?R = {}" by (induct ss2) auto
        ultimately have fresh: "vars_trs ?R \<inter> set(?ss1' @ ?ss2') = {}" by auto
        then have fresh: "vars_trs R \<inter> set(?ss1' @ ?ss2') = {}" unfolding vars_trs_def by auto
        from Var_the_Var_id[OF all_vars]
          have "map Var (map the_Var (ss1 @ ss2)) = ss1 @ ss2" .
        from distinct_the_vars[OF all_vars \<open>distinct (ss1 @ ss2)\<close>]
          have "distinct (map the_Var (ss1 @ ss2))" .
        then have dist: "distinct (?ss1' @ ?ss2')" by simp
        have len1: "length ?ss1' = length ss1'" using \<open>length ss1 = ?i\<close> by simp
        have len2: "length ?ss2' = length ss2'" using \<open>length ss2 = ?n - ?i - 1\<close> by simp
        let ?\<sigma> = "subst_extend \<sigma> (zip (?ss1' @ ?ss2') (ss1' @ ss2'))"
        let ?E' = "More f' ss1' \<box> ss2'"
        have G_l_substex: "?E'\<langle>l \<cdot> \<sigma>\<rangle> = (?G\<langle>l\<rangle>) \<cdot> ?\<sigma>"
          unfolding subst_apply_term_ctxt_apply_distrib
          unfolding subst_extend_id[OF fresh vl]
          using subst_extend_flat_ctxt'[OF dist len1 len2]
          unfolding Var_the_Var_id[OF \<open>\<forall>s\<in>set ss1. is_Var s\<close>]
          unfolding Var_the_Var_id[OF \<open>\<forall>s\<in>set ss2. is_Var s\<close>] by simp
       have G_r_substex: "?E'\<langle>r \<cdot> \<sigma>\<rangle> = (?G\<langle>r\<rangle>) \<cdot> ?\<sigma>"
          unfolding subst_apply_term_ctxt_apply_distrib
          unfolding subst_extend_id[OF fresh vr]
          using subst_extend_flat_ctxt'[OF dist len1 len2]
          unfolding Var_the_Var_id[OF \<open>\<forall>s\<in>set ss1. is_Var s\<close>]
          unfolding Var_the_Var_id[OF \<open>\<forall>s\<in>set ss2. is_Var s\<close>] by simp
       have "(?E'\<langle>l \<cdot> \<sigma>\<rangle>, ?E'\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep R'"
         unfolding G_l_substex G_r_substex
         by (rule instance_rule_rstep[OF _ in_R'], blast)
        from rstep_ctxt[OF this, of D']
          have "(D\<langle>l \<cdot> \<sigma>\<rangle>, D\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep R'"
          unfolding More by simp
        from rstep_ctxt[OF this, of "More h ?ss1 (More f [] \<box> []) ?ss2"]
          have "(?s, ?t) \<in> rstep R'" unfolding s t C by simp
        with no_def and funas_args show ?thesis by simp
      qed
    qed
  qed
qed

lemma rstep_imp_blocked_rstep:
  assumes "wf_trs R"
    and flat_ctxts: "\<forall>C\<in>fcs. is_flat_ctxt (vars_trs R) F C"
    and complete: "\<forall>(f, n)\<in>F. \<forall>i<n. \<exists>ss1 ss2.
      (More f ss1 \<box> ss2) \<in> fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1"
    and "funas_args_term s \<subseteq> funas_trs R \<union> funas_args_trs P"
    and "funas_trs R \<union> funas_args_trs P \<subseteq> F"
    and "(f, Suc 0) \<in> F"
    and "\<not> defined R (the(root s))"
    and "(s, t) \<in> rstep R"
    and pres: "\<forall>(l, r)\<in>R. (Bex R' (instance_rule (l, r))) \<or> (\<forall>E\<in>fcs. Bex R' (instance_rule (E\<langle>l\<rangle>, E\<langle>r\<rangle>)))"
  shows "\<not> defined R (the(root t)) \<and> funas_args_term t \<subseteq> funas_trs R \<union> funas_args_trs P
    \<and> (block_term f s, block_term f t) \<in> rstep R'"
  using assms rstep_imp_blocked_rstep_union[of R "{}" fcs F s P f t R']
  by auto

lemma rseq_imp_blocked_rseq:
  assumes "wf_trs R"
    and flat_ctxts: "\<forall>C\<in>fcs. is_flat_ctxt (vars_trs R) F C"
    and complete: "\<forall>(f, n)\<in>F. \<forall>i<n. \<exists>ss1 ss2.
      (More f ss1 \<box> ss2) \<in> fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1"
    and "funas_args_term s \<subseteq> funas_trs R \<union> funas_args_trs P"
    and "funas_trs R \<union> funas_args_trs P \<subseteq> F"
    and "(f, Suc 0) \<in> F"
    and "\<not> defined R (the (root s))"
    and "(s, t) \<in> (rstep R)^*"
    and pres: "\<forall>(l, r)\<in>R. (Bex R' (instance_rule (l, r))) \<or> (\<forall>E\<in>fcs. Bex R' (instance_rule (E\<langle>l\<rangle>, E\<langle>r\<rangle>)))"
  shows "\<not> defined R (the (root t)) \<and> funas_args_term t \<subseteq> funas_trs R \<union> funas_args_trs P
    \<and> (block_term f s, block_term f t) \<in> (rstep R')^*"
using \<open>(s, t) \<in> (rstep R)^*\<close>
  and \<open>funas_args_term s \<subseteq> funas_trs R \<union> funas_args_trs P\<close>
  and \<open>\<not> defined R (the (root s))\<close>
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step y z)
  with rstep_imp_blocked_rstep[OF \<open>wf_trs R\<close> flat_ctxts complete
    _ \<open>funas_trs R \<union> funas_args_trs P \<subseteq> F\<close> \<open>(f, Suc 0) \<in> F\<close> _ _ pres, of y z]
    have "\<not> defined R (the (root z)) \<and> funas_args_term z \<subseteq> funas_trs R \<union> funas_args_trs P
      \<and> (block_term f y, block_term f z) \<in> rstep R'
      \<and> (block_term f s, block_term f y) \<in> (rstep R')^*" by simp
  then show ?case by auto
qed

lemma funas_args_term_Fun:
  "funas_args_term (Fun f ts \<cdot> \<sigma>) = (\<Union>t\<in>set ts. funas_term (t \<cdot> \<sigma>))"
unfolding funas_args_term_def by auto

lemma funas_args_term_subst_apply:
  assumes "is_Fun t"
  shows "funas_args_term (t \<cdot> \<sigma>) = (\<Union>t\<in>set (args t). funas_term (t \<cdot> \<sigma>))"
proof -
  from assms obtain f ts where t: "t = Fun f ts" by (cases t) auto
  show ?thesis using funas_args_term_Fun unfolding t by simp
qed

lemma block_subst_Fun:
  "block_term f (Fun g us \<cdot> \<sigma>) = (block_term f (Fun g us)) \<cdot> \<sigma>"
  by simp

lemma num_args_block_term[simp]:
  "num_args (block_term f t) = num_args t"
  by (induct t) simp_all


lemma blocked_rstep_imp_rstep':
  assumes "wf_trs R"
    and "\<not> defined R (f, 1)"
    and "\<not> defined R (the (root s))"
    and "(block_term f s, block_term f t) \<in> rstep R" (is "(?s, ?t) \<in> _")
  shows "\<not> defined R (the (root t)) \<and> (s, t) \<in> rstep R"
proof -
  from NF_Var[OF \<open>wf_trs R\<close>] and assms obtain g ss where s: "s = Fun g ss" by (induct s) auto
  then have s': "?s = Fun g (map (\<lambda>t. Fun f [t]) ss)" by simp
  from assms have "\<not> defined R (g, length ss)" unfolding s by simp
  from \<open>wf_trs R\<close> and \<open>(?s, ?t) \<in> rstep R\<close>[unfolded s'] show ?thesis
  proof (cases rule: rstep_cases_Fun')
    case (root ls r \<sigma>)
    from arg_cong[where f = length, OF this(2)]
    have id: "length ss = length ls" by auto
    from \<open>\<not> defined R (g, length ss)\<close> show ?thesis unfolding defined_def id using root by force
  next
    case (nonroot i u)
    from \<open>i < length (map (\<lambda>t. Fun f [t]) ss)\<close> have "i < length ss" by simp
    from id_take_nth_drop[OF this] have ss: "take i ss @ (ss!i) # drop (Suc i) ss = ss" ..
    let ?C = "More g (take i ss) \<box> (drop (Suc i) ss)"
    from nonroot have "(Fun f [ss!i], u) \<in> rstep R" by simp
    with \<open>wf_trs R\<close> have "\<exists>v. u = Fun f [v] \<and> (ss!i, v) \<in> rstep R"
    proof (cases rule: rstep_cases_Fun')
      case (root ls' r' \<sigma>')
      with \<open>\<not> defined R (f, 1)\<close> have False unfolding defined_def by force
      then show ?thesis ..
    next
      case (nonroot j v)
      then show ?thesis by auto
    qed
    then obtain v where u: "u = Fun f [v]" and rstep: "(ss!i, v) \<in> rstep R" by auto
    from rstep_ctxt[OF rstep] have "(?C\<langle>ss!i\<rangle>, ?C\<langle>v\<rangle>) \<in> rstep R" .
    moreover have "s = ?C\<langle>ss!i\<rangle>" by (simp add: s ss)
    moreover have u: "unblock_term f ?t = ?C\<langle>v\<rangle>"
    proof -
      let ?ss = "take i ss @ v # drop (Suc i) ss"
      let ?ss' = "map (\<lambda>t. Fun f [t]) ?ss"
      have map_simp_aux: "Fun f [v] # map (\<lambda>t. Fun f [t]) (drop (Suc i) ss) = map (\<lambda>t. Fun f [t]) (v # drop (Suc i) ss)" by simp
      have "\<forall>s\<in>set ?ss'. has_unary_root f s" by auto
      then have "unblock_term f (Fun g ?ss') = Fun g ?ss" by simp
      then show ?thesis unfolding nonroot
        unfolding take_map u drop_map
        unfolding list.map[symmetric]
      unfolding nonroot u
      unfolding take_map drop_map
      unfolding map_simp_aux
      unfolding map_append by simp
    qed
    moreover have "\<not> defined R (the (root t))"
    proof -
      have id: "num_args t = length ss" using u unfolding unblock_block_term_ident using \<open>i < length ss\<close> by auto
      have "the (root (unblock_term f ?t)) = (g, num_args ?t)" unfolding nonroot by simp
      with \<open>\<not> defined R (g, length ss)\<close>
        show ?thesis unfolding unblock_block_term_ident by (simp add: id)
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma rstep_imp_blocked_rstep':
  assumes "wf_trs R"
    and "\<not> defined R (f, 1)"
    and "\<not> defined R (the (root s))"
    and "(block_term f s, t) \<in> rstep R"
  shows "\<exists>u. \<not> defined R (the (root u)) \<and> t = block_term f u"
proof -
  let ?s = "block_term f s"
  from assms and NF_Var[OF \<open>wf_trs R\<close>] have "is_Fun s" by auto
  then obtain g ss where s: "s = Fun g ss" by (induct s) auto
  let ?ss = "map (\<lambda>t. Fun f [t]) ss"
  have s': "?s = Fun g ?ss" by (simp add: s)
  from assms have "\<not> defined R (g, length ?ss)" unfolding s by simp
  from rstep_preserves_undefined_root[OF \<open>wf_trs R\<close> this \<open>(?s, t) \<in> rstep R\<close>[unfolded s']]
    obtain ts where "length ts = length ?ss" and t: "t = Fun g ts" by auto
  then have "\<not> defined R (the (root t))" unfolding t using \<open>\<not> defined R (g, length ?ss)\<close> by simp
  from \<open>wf_trs R\<close> and \<open>(?s, t) \<in> rstep R\<close>[unfolded s'] show ?thesis
  proof (cases rule: rstep_cases_Fun')
    case (root ls r \<sigma>)
    from arg_cong[where f = length,OF root(2)] have "length ss = length ls" by auto
    with assms and root have "\<not> defined R (g, length ls)" unfolding root s by auto
    with \<open>(Fun g ls, r) \<in> R\<close> show ?thesis unfolding defined_def by force
  next
    case (nonroot i u)
    then have i: "i < length ss" by auto
    then have "length (take i ?ss @ u # drop (Suc i) ?ss) = length ss" by auto
    with assms have "\<not> defined R (the (root t))" using nonroot by (simp add: s)
    from nonroot have "(Fun f [ss!i], u) \<in> rstep R" by simp
    from rstep_preserves_undefined_root[OF \<open>wf_trs R\<close> _ this] \<open>\<not> defined R (f, 1)\<close>
      obtain ts where "length ts = length [ss!i]" and "u = Fun f ts" by auto
    then obtain v where u: "u = Fun f [v]" by (induct ts) simp_all
    let ?u = "Fun g (take i ss @ v # drop (Suc i) ss)"
    have ss1: "map (\<lambda>t. Fun f [t]) (take i ss) = take i ?ss" unfolding take_map ..
    have ss2: "map (\<lambda>t. Fun f [t]) (drop (Suc i) ss) = drop (Suc i) ?ss" unfolding drop_map ..
    have "map (\<lambda>t. Fun f [t]) (take i ss @ v # drop (Suc i) ss) = take i ?ss @ (Fun f [v]) # drop (Suc i) ?ss" unfolding map_append by (simp add: ss1 ss2)
    then have "t = block_term f ?u" unfolding nonroot u by simp
    moreover have "\<not> defined R (the (root ?u))" using \<open>\<not> defined R (the (root t))\<close>
      unfolding nonroot by simp
    ultimately show ?thesis by best
  qed
qed

lemma SN_on_imp_blocked_SN_on:
  assumes "wf_trs R"
    and "\<not> defined R (f, 1)"
    and "\<not> SN_on (rstep R') {block_term f t}"
    and "\<not> defined R (the (root t))"
    and refl: "\<forall>(l, r)\<in>R'. \<exists>(u, v)\<in>R. \<exists>C\<in>set (\<box> # fcs). l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
  shows "\<not> SN_on (rstep R) {t}"
proof -
  from assms(3) obtain S where "S 0 = block_term f t"
    and chain: "chain (rstep R') S" by auto
  from chain and blocked_rstep_imp_rstep[OF refl]
    have R_chain: "chain (rstep R) S" by auto
  have "\<forall>i. \<exists>u. \<not> defined R (the (root u)) \<and> S i = block_term f u"
  proof
    fix i show "\<exists>u. \<not> defined R (the (root u)) \<and> S i = block_term f u"
    proof (induct i)
      case 0
      from \<open>S 0 = block_term f t\<close> and assms show ?case by auto
    next
      case (Suc i)
      then obtain u where "\<not> defined R (the (root u))" and Si: "S i = block_term f u" by auto
      from R_chain have "(S i, S (Suc i)) \<in> rstep R" by simp
      then have "(block_term f u, S (Suc i)) \<in> rstep R" unfolding Si by simp
      from rstep_imp_blocked_rstep'[OF \<open>wf_trs R\<close> \<open>\<not> defined R (f, 1)\<close>
        \<open>\<not> defined R (the (root u))\<close> this]
        show ?case .
    qed
  qed
  from choice[OF this] obtain T
    where "\<forall>i. \<not> defined R (the (root (T i))) \<and> S i = block_term f (T i)"
    (is "\<forall>i. _ \<and> S i = ?T i") by auto
  with R_chain have blocked_chain: "chain (rstep R) ?T" by auto
  let ?T' = "\<lambda>i. unblock_term f (S i)"
  have "?T' 0 = t" unfolding \<open>S 0 = block_term f t\<close> by simp
  moreover have "\<forall>i. (?T' i, ?T' (Suc i)) \<in> rstep R"
  proof
    fix i show "(?T' i, ?T' (Suc i)) \<in> rstep R"
    proof -
      from \<open>\<forall>i. \<not> defined R (the (root (T i))) \<and> S i = ?T i\<close>
        have "\<not> defined R (the (root (T i)))"
        and si: "S i = block_term f (T i)"
        and ssi: "S (Suc i) = block_term f (T (Suc i))" by auto
      from blocked_chain have "(?T i, ?T (Suc i)) \<in> rstep R" ..
      from blocked_rstep_imp_rstep'[OF \<open>wf_trs R\<close> \<open>\<not> defined R (f, 1)\<close> \<open>\<not> defined R (the (root (T i)))\<close> this]
      show ?thesis unfolding si ssi by simp
    qed
  qed
  ultimately show ?thesis unfolding SN_defs by auto
qed

lemma block_map_funs_term [simp]:
  "(map_funs_term h (block_term f (Fun g ts))) = block_term (h f) (map_funs_term h (Fun g ts))"
  by (simp)

lemma block_map_funs_term_pow [simp]:
  fixes h :: "'a \<Rightarrow> 'a"
  shows "((map_funs_term h)^^n) (block_term f (Fun g ts)) = block_term ((h ^^ n) f) (((map_funs_term h)^^n) (Fun g ts))"
proof (induct n arbitrary: g ts f)
  case (Suc n g ts f)
  have "(map_funs_term h ^^ Suc n) (block_term f (Fun g ts)) = (map_funs_term h ^^ n) (map_funs_term h (block_term f (Fun g ts)))"
    by (simp add: funpow_swap1)
  also have "\<dots> = (map_funs_term h ^^ n) (block_term (h f) (Fun (h g) (map (map_funs_term h) ts)))" by (simp only: block_map_funs_term, simp)
  also have "\<dots> = block_term ((h ^^ n) (h f)) ((map_funs_term h ^^ n) (Fun (h g) (map (map_funs_term h) ts)))" unfolding Suc by simp
  also have "\<dots> = block_term ((h ^^ (Suc n)) f) ((map_funs_term h ^^ (Suc n)) (Fun g ts))" by (simp add: funpow_swap1)
  finally
  show ?case .
qed simp


abbreviation block_trs where "block_trs f R \<equiv> block_rule f ` R"

lemma superset_of_blocked:
  assumes "\<forall>rule\<in>R. block_rule f rule \<in> R'"
  shows "block_trs f R \<subseteq> R'"
proof (rule subrelI)
  fix s t assume "(s, t) \<in> block_trs f R"
  then obtain r where st: "block_rule f r = (s, t)" and "r \<in> R" by auto
  with assms have "block_rule f r \<in> R'" by blast
  then show "(s, t) \<in> R'" unfolding st .
qed

definition fcc_tt_cond :: "('f, 'v) ctxt set \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "fcc_tt_cond fcs R R' S S' = (
    let F  = funas_trs (R \<union> S) in
    let vs = vars_trs (R \<union> S) in
    fcs \<noteq> {} \<and>
    (\<forall>C\<in>fcs. is_flat_ctxt vs F C) \<and>
    (\<forall>(g, n)\<in>F. \<forall>i<n. \<exists>ss1 ss2.
      More g ss1 \<box> ss2 \<in> fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1) \<and>
    (\<forall>(l, r)\<in>R. (Bex R' (instance_rule (l, r))) \<or> (\<forall>E\<in>fcs. Bex R' (instance_rule (E\<langle>l\<rangle>, E\<langle>r\<rangle>)))) \<and>
    (\<forall>(l, r)\<in>S. (Bex (R' \<union> S') (instance_rule (l, r))) \<or> (\<forall>E\<in>fcs. Bex (R' \<union> S') (instance_rule (E\<langle>l\<rangle>, E\<langle>r\<rangle>)))))"

fun
  fcc_tt :: "('f, 'v) ctxt set \<Rightarrow> ('f, 'v) qreltrs \<Rightarrow> ('f, 'v) qreltrs \<Rightarrow> bool"
where
  "fcc_tt fcs (nfs,Q, R, S) (nfs',Q', R', S') = (
    fcc_tt_cond fcs R R' S S' \<and>
    Q' = {})"

theorem fcc_tt_sound:
  assumes tt: "fcc_tt fcs (nfs,Q, R, S) (nfs',Q', R', S')"
    and sn: "SN_qrel (nfs',Q', R', S')"
  shows "SN_qrel (nfs,Q, R, S)"
proof -
  note cond = tt[unfolded fcc_tt.simps fcc_tt_cond_def Let_def]
  from sn have "SN_rel (rstep R') (rstep S')" using cond by simp
  from partial_fcc_reflects_SN_rel[OF _ _ _ _ _ _ this] and cond
  have relSN: "SN_rel (rstep R) (rstep S)" by auto
  show ?thesis unfolding SN_qrel_def split
    by (rule SN_rel_mono[OF _ _ relSN], auto)
qed

definition
  fcc_cond ::
    "'f \<Rightarrow> ('f, 'v) ctxt list \<Rightarrow>
    ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    bool"
where
  "fcc_cond f fcs P Pw R Rw P' Pw' R' Rw' \<equiv>
    let F = funas_trs (R \<union> Rw) \<union> funas_args_trs (P \<union> Pw);
        Cf  = More f [] \<box> [] in
    wf_trs (R \<union> Rw) \<and> \<not> defined (R \<union> Rw) (f, 1) \<and>
    (\<forall>C\<in>set (Cf#fcs). is_flat_ctxt (vars_trs (R \<union> Rw)) ({(f, 1)} \<union> F) C) \<and>
    (\<forall>(g, n)\<in>F. \<forall>i<n. \<exists>ss1 ss2.
      More g ss1 \<box> ss2 \<in> set (Cf # fcs) \<and> length ss1 = i \<and> length ss2 = n - i - 1) \<and>
    (\<forall>(l, r)\<in>R. (Bex R' (instance_rule (l, r))) \<or> (\<forall>C\<in>set (Cf#fcs). (Bex R' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>))))) \<and>
    (\<forall>(l, r)\<in>Rw. (Bex (R' \<union> Rw') (instance_rule (l, r))) \<or> (\<forall>C\<in>set (Cf#fcs). Bex (R' \<union> Rw') (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))) \<and>
    (\<forall>(l', r')\<in>R' \<union> Rw'. \<exists>(l, r)\<in>R \<union> Rw. \<exists>C\<in>set (\<box> # Cf # fcs). l' = C\<langle>l\<rangle> \<and> r' = C\<langle>r\<rangle>) \<and>
    block_rule f ` P \<subseteq> P' \<and>
    block_rule f ` Pw \<subseteq> Pw' \<and>
    (\<forall>(s, t)\<in>P \<union> Pw. is_Fun s \<and> is_Fun t) \<and>
    (\<forall>(s, t)\<in>P \<union> Pw. \<not> defined (R \<union> Rw) (the (root t)))"

fun
  fcc_proc ::
    "'f \<Rightarrow> ('f, 'v) ctxt list \<Rightarrow> ('f, 'v) dpp \<Rightarrow> ('f, 'v) dpp \<Rightarrow> bool"
where
  "fcc_proc f fcs (nfs,m,P, Pw, Q, R, Rw) (nfs',m',P', Pw', Q', R', Rw') = (
    fcc_cond f fcs P Pw R Rw P' Pw' R' Rw')"

theorem fcc_proc_chain: fixes P Pw R Rw :: "('f,'v)trs"
  defines F: "F \<equiv> funas_trs (R \<union> Rw) \<union> funas_args_trs (P \<union> Pw)"
  assumes proc: "fcc_proc f fcs (nfs,m,P, Pw, {}, R, Rw) (nfs,m,P', Pw', {}, R', Rw')"
    and michain: "min_ichain_sig (nfs,m,P,Pw,{},R,Rw) F s t \<sigma>"
   shows "\<exists> s t. min_ichain (nfs,m,P',Pw',{},R',Rw') s t \<sigma>"
proof -
  note cond = proc[unfolded fcc_proc.simps fcc_cond_def Let_def]
  let ?P  = "P \<union> Pw"
  let ?P' = "P' \<union> Pw'"
  let ?R = "R \<union> Rw"
  let ?R' = "R' \<union> Rw'"
  let ?Cf = "More f [] \<box> []"
  let ?F' = "funas_trs ?R \<union> funas_args_trs ?P"
  let ?F  = "{(f, 1)} \<union> ?F'"
  from michain proc have mchain: "min_ichain (nfs,m,P,Pw,{},R,Rw) s t \<sigma>" and F: "funas_ichain s t \<sigma> \<subseteq> ?F'" unfolding F by auto
  from cond have flat_ctxts: "\<forall>C\<in>set (?Cf # fcs). is_flat_ctxt (vars_trs ?R) ?F C" by auto
  from cond have complete: "\<forall>(g, n)\<in>?F. \<forall>i<n. \<exists>ss1 ss2.
    More g ss1 \<box> ss2 \<in> set (?Cf # fcs) \<and> length ss1 = i \<and> length ss2 = n - i - 1" by simp
  from cond have wfR: "wf_trs ?R" by simp
  from cond have pres: "\<forall>(l, r)\<in>R. (Bex R' (instance_rule (l, r)))
    \<or> (\<forall>C\<in>set (?Cf # fcs). (Bex R' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>))))"
    "\<forall>(l, r)\<in>Rw. (Bex ?R' (instance_rule (l, r)))
    \<or> (\<forall>C\<in>set (?Cf # fcs). Bex ?R' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))" by auto
  from pres have pres': "\<forall>(l, r)\<in> ?R. (Bex ?R' (instance_rule (l, r)))
    \<or> (\<forall>C\<in>set (?Cf # fcs). Bex ?R' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))" by blast
  from cond
  have refl: "\<forall>(l', r')\<in> ?R'. \<exists>(l, r)\<in> ?R. \<exists>C\<in>set (\<box> # ?Cf # fcs). l' = C\<langle>l\<rangle> \<and> r' = C\<langle>r\<rangle>"
    by simp
  from mchain have P_steps: "\<forall>i. (s i, t i) \<in> ?P" by (auto simp add: ichain.simps)
  then have "\<forall>i. is_Fun (s i) \<and> is_Fun (t i)" using cond by best
  then have si_Fun: "\<forall>i. is_Fun (s i)" and ti_Fun: "\<forall>i. is_Fun (t i)" by auto
  have funas_args: "funas_trs ?R \<union> funas_args_trs ?P \<subseteq> ?F" by blast
  from cond have nd: "\<not> defined ?R (f, 1)" by simp
  have inP: "\<And> s t. (s, t) \<in> ?P \<Longrightarrow> is_Fun s \<and> is_Fun t \<and> \<not> defined ?R (the (root t))"
    using cond by blast
  let ?s = "\<lambda>i. block_term f (s i)"
  let ?t = "\<lambda>i. block_term f (t i)"
  let ?RR = "(rstep ?R)^* O rstep R O (rstep ?R)^*"
  let ?RR' = "(rstep ?R')^* O rstep R' O (rstep ?R')^*"
  {
    fix t u :: "('f,'v)term"
    let ?Rc = "(if rstep ?R = rstep R then rstep R' else rstep ?R')"
    have Rc: "?Rc \<subseteq> rstep ?R'" unfolding rstep_union by auto
    then have Rc: "?Rc^* \<subseteq> (rstep ?R')^*" by (rule rtrancl_mono)
    assume t: "\<not> defined ?R (the (root t)) \<and> funas_args_term t \<subseteq> ?F'"
    have " ((t, u) \<in> (rstep ?R)\<^sup>* \<longrightarrow>
      (block_term f t, block_term f u)
      \<in> ?Rc^*) \<and>
     ((t, u) \<in> ?RR \<longrightarrow>
      (block_term f t, block_term f u)
      \<in> ?Rc^* O
        rstep R' O
        ?Rc^*)"
    proof (rule steps_map[where Q = "\<lambda> S. S = rstep R \<or> S = rstep ?R" and P = "\<lambda> t. \<not> defined ?R (the (root t)) \<and> funas_args_term t \<subseteq> ?F'" and f = "block_term f" and g = "\<lambda> S. if S = rstep R then rstep R' else rstep ?R'", of _ "rstep ?R" "rstep R", unfolded HOL.simp_thms if_True, OF _ t])
      fix t u S
      assume t: "\<not> defined ?R (the (root t)) \<and> funas_args_term t \<subseteq> ?F'"
      and S: "S = rstep R \<or> S = rstep ?R"
      and step: "(t,u) \<in> S"
      from step S have step': "(t, u) \<in> rstep ?R" unfolding rstep_union by auto
      from t have ndef: "\<not> defined ?R (the (root t))"
        and funas: "funas_args_term t \<subseteq> ?F'" by auto
      from rstep_imp_blocked_rstep[OF wfR flat_ctxts complete funas _ _ ndef step' pres', of f]
      have one: "\<not> defined ?R (the (root u)) \<and> funas_args_term u \<subseteq> ?F'" and
        step': "(block_term f t, block_term f u) \<in> rstep ?R'" by auto
      let ?S = "(if S = rstep R then rstep R' else rstep ?R')"
      show "(\<not> defined ?R (the (root u)) \<and> funas_args_term u \<subseteq> ?F') \<and>
        (block_term f t, block_term f u) \<in> ?S"
      proof (rule conjI[OF one])
        show "(block_term f t, block_term f u) \<in> ?S"
        proof (cases "?S = rstep ?R'")
          case True
          show ?thesis unfolding True using step' .
        next
          case False
          then have "?S = rstep R' \<and> S = rstep R"
            by (cases "S = rstep R", auto)
          then have S: "?S = rstep R'" "S = rstep R" by auto
          with step have step: "(t,u) \<in> rstep R" by auto
          from rstep_imp_blocked_rstep_union[OF wfR flat_ctxts complete funas _ _ ndef step pres(1), of f]
          show ?thesis unfolding S(1) by auto
        qed
      qed
    qed auto
    with Rc have " ((t, u) \<in> (rstep ?R)\<^sup>* \<longrightarrow>
      (block_term f t, block_term f u)
      \<in> (rstep ?R')^*) \<and>
     ((t, u) \<in> ?RR \<longrightarrow>
      (block_term f t, block_term f u)
      \<in> ?RR')" by auto
  } note main = this
  {
    fix i
    let ?\<sigma> = "\<sigma> i"
    let ?t = "t i \<cdot> ?\<sigma>"
    let ?\<sigma>' = "\<sigma> (Suc i)"
    let ?s = "s (Suc i) \<cdot> ?\<sigma>'"
    let ?bt = "block_term f (t i) \<cdot> \<sigma> i"
    let ?bs = "block_term f (s (Suc i)) \<cdot> \<sigma> (Suc i)"
    from P_steps have t_in_P: "(s i, t i) \<in> ?P" by simp
    from P_steps have s_in_P: "(s (Suc i), t (Suc i)) \<in> ?P" by simp
    from mchain have R_seq: "(?t, ?s) \<in> (rstep ?R)^*" by (simp add: ichain.simps)
    from ti_Fun have "is_Fun (t i)" by simp
    then obtain gs ts where ti: "t i = Fun gs ts" by best
    from si_Fun have "is_Fun (s (Suc i))" by simp
    then obtain hs us where si: "s (Suc i) = Fun hs us" by best
    from inP[OF t_in_P]
    have "\<not> defined ?R (the (root (t i)))" by (auto)
    then have not_def_t: "\<not> defined ?R (the (root ?t))" unfolding ti by simp
    have t_funas_args: "funas_args_term ?t \<subseteq> funas_trs ?R \<union> funas_args_trs ?P"
    proof -
      from t_in_P
      have funas_ti: "funas_args_term (t i) \<subseteq> ?F'"
        unfolding funas_args_trs_def funas_args_rule_def [abs_def] by auto
      moreover have "funas_args_term ?t = (\<Union>t\<in>set ts. funas_term (t \<cdot> ?\<sigma>))"
        unfolding funas_args_term_subst_apply[OF \<open>is_Fun (t i)\<close>]
        unfolding ti by auto
      moreover
      have "\<forall>t\<in>set ts. funas_term (t \<cdot> ?\<sigma>) \<subseteq> ?F'"
      proof
        fix u assume "u \<in> set ts"
        from funas_ti[unfolded ti funas_args_term_def]
        have "\<Union>(set (map funas_term ts))
          \<subseteq> ?F'" by simp
        with \<open>u \<in> set ts\<close> have "funas_term u
          \<subseteq> ?F'" by auto
        then have "funas_term (u \<cdot> ?\<sigma>) \<subseteq> ?F' \<union> funas_ichain s t \<sigma>"
          unfolding funas_term_subst funas_ichain_def by auto
        then show "funas_term (u \<cdot> ?\<sigma>)
          \<subseteq> ?F'" using F by auto
      qed
      ultimately show ?thesis by auto
    qed
    from not_def_t t_funas_args have precond: "\<not> defined ?R (the (root ?t)) \<and> funas_args_term ?t \<subseteq> ?F'" by auto
    note main = main[OF this, of ?s]
    from ti have bti: "block_term f ?t = ?bt" by simp
    from si have bsi: "block_term f ?s = ?bs" by simp
    note main = main[unfolded bti bsi]
    from main[THEN conjunct1, rule_format, OF R_seq]
    have steps: "(?bt, ?bs) \<in> (rstep ?R')^*" by simp
    {
      assume "(?t,?s) \<in> ?RR"
      then have "(?bt,?bs) \<in> ?RR'"
        using main[THEN conjunct2] by auto
    }
    note steps this
  } note main = this
  note steps = main(1)
  note strict_steps = main(2)
  have "\<forall>i. (?s i, ?t i) \<in> ?P'"
  proof
    fix i
    from mchain have "(s i, t i) \<in> ?P" by (simp add: ichain.simps)
    then have "block_rule f (s i, t i) \<in> block_rule f ` ?P" by simp
    then have "(?s i, ?t i) \<in> block_rule f ` ?P" unfolding block_rule_def by simp
    moreover from cond
    have "block_rule f ` ?P \<subseteq> ?P'"
      using superset_of_blocked by auto
    ultimately show "(?s i, ?t i) \<in> ?P'" by blast
  qed
  moreover {
    assume m
    have "\<forall>i. SN_on (rstep ?R') {?t i \<cdot> \<sigma> i}"
    proof
      fix i
      from ti_Fun obtain k vs where ti: "t i = Fun k vs" by best
      have "the (root (t i)) = (k, length vs)" unfolding ti by simp
      then have k: "(k, length vs) = the (root (t i \<cdot> \<sigma> i))" unfolding ti by simp
      from P_steps have inP': "(s i, t i) \<in> ?P" by simp
      let ?tsi = "(t i \<cdot> \<sigma> i)"
      let ?bti = "block_term f ?tsi"
      from cond and \<open>(s i, t i) \<in> ?P\<close>
      have "\<not> defined ?R (the (root (t i)))" by auto
      then have not_def_t: "\<not> defined ?R (the (root ?tsi))"
        unfolding ti by auto
      from block_subst_Fun[of f k vs "\<sigma> i"]
      have block_ti: "?t i \<cdot> \<sigma> i = ?bti" unfolding ti by auto
      from refl have ci: "?R' \<subseteq>ci ?R" unfolding ci_subset_def by blast
      have subset: "rstep ?R' \<subseteq> rstep ?R"
        using qrstep_ci_mono[OF ci, of False "{}", unfolded qrstep_rstep_conv] by auto
      show "SN_on (rstep ?R') {?t i \<cdot> \<sigma> i}"
      proof (rule SN_on_subset1[OF _ subset], rule ccontr)
        assume "\<not> SN_on (rstep ?R) {?t i \<cdot> \<sigma> i}"
        then have not_SN: "\<not> SN_on (rstep ?R) {?bti}" unfolding block_ti .
        let ?tmp = "Fun f [t 0]"
        from nd have a: "is_Fun ?tmp"
          and b: "\<not> defined ?R (the (root ?tmp))" by auto
        have nSN: "\<not> SN_on (rstep ?R) {?tsi}"
          using SN_on_imp_blocked_SN_on[OF \<open>wf_trs ?R\<close> nd not_SN not_def_t, of "[]"] by auto
        with mchain \<open>m\<close>
        show False by (simp add: minimal_cond_def)
      qed
    qed
  }
  moreover have "\<forall>i. (?t i \<cdot> \<sigma> i, ?s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (rstep ?R')^*"
    (is "\<forall>i. ?Prop i")
    using steps by simp
  moreover have "(INFM i. (?s i, ?t i) \<in> P') \<or> (INFM i. (?t i \<cdot> \<sigma> i, ?s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?RR')"
  proof -
    let ?orig = "\<lambda> i. (s i, t i) \<in> P \<or> (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?RR"
    let ?new = "\<lambda> i. (?s i, ?t i) \<in> P' \<or> (?t i \<cdot> \<sigma> i, ?s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?RR'"
    from mchain[unfolded min_ichain.simps ichain.simps]
    have inf: "(INFM i. ?orig i)" unfolding INFM_disj_distrib by simp
    show ?thesis unfolding INFM_disj_distrib[symmetric]
      unfolding INFM_nat_le
    proof
      fix i :: nat
      from inf[unfolded INFM_nat_le, rule_format, of i]
      obtain j where j: "j \<ge> i" and orig: "?orig j" by auto
      show "\<exists> j \<ge> i. ?new j"
      proof (rule exI, rule conjI[OF j])
        from \<open>?orig j\<close> show "?new j"
        proof
          assume "(s j, t j) \<in> P"
          then have "block_rule f (s j, t j) \<in> block_rule f ` P" by simp
          then have "(?s j, ?t j) \<in> block_rule f ` P" unfolding block_rule_def by simp
          moreover from cond
          have "block_rule f ` P \<subseteq> P'"
            using superset_of_blocked by auto
          ultimately have "(?s j, ?t j) \<in> P'" by blast
          then show "?new j" ..
        next
          assume "(t j \<cdot> \<sigma> j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> ?RR"
          from strict_steps[OF this] show "?new j" ..
        qed
      qed
    qed
  qed
  ultimately have "min_ichain (nfs,m,P', Pw', {}, R', Rw') ?s ?t \<sigma>"
    unfolding min_ichain.simps ichain.simps minimal_cond_def
    by simp
  then show ?thesis by blast
qed

theorem fcc_proc_sound: fixes P :: "('f,'v)trs"
  assumes proc: "fcc_proc f fcs (nfs,m,P, Pw, {}, {}, R) (nfs,m,P', Pw', {}, {}, R')"
    and left: "left_linear_trs R"
    and finite: "finite_dpp (nfs,m,P', Pw', {}, {}, R')"
  shows "finite_dpp (nfs,m,P, Pw, {}, {}, R)"
proof (rule ccontr)
  let ?D = "(nfs,m,P,Pw,{},{},R) :: ('f,'v)dpp"
  let ?F = "(funas_args_trs (P \<union> Pw) \<union> funas_trs R)"
  let ?F' = "(funas_trs ({} \<union> R) \<union> funas_args_trs (P \<union> Pw))"
  assume "\<not> ?thesis"
  then obtain s t \<sigma> where chain: "min_ichain ?D s t \<sigma>" unfolding finite_dpp_def by auto
  from proc[unfolded fcc_proc.simps fcc_cond_def Let_def] have "wf_trs R" by auto
  then have nvar: " \<forall>(l, r)\<in> R. is_Fun l" unfolding wf_trs_def by auto
  have "\<exists> \<sigma>. min_ichain_sig ?D ?F s t \<sigma>"
    by (rule left_linear_min_ichain_imp_min_ichain_sig[OF left subset_refl _ chain nvar], insert proc[unfolded fcc_proc.simps fcc_cond_def Let_def], auto)
  then obtain \<sigma> where chain: "min_ichain_sig ?D ?F' s t \<sigma>" by auto
  from finite fcc_proc_chain[OF proc chain] show False unfolding finite_dpp_def by auto
qed

theorem fcc_split_proc_sound: fixes P :: "('f,'v)trs"
  assumes proc: "fcc_proc f fcs (nfs,m,Ps \<inter> (P \<union> Pw), (P \<union> Pw) - Ps, {}, Rw \<inter> Rs, Rw - Rs) (nfs,m,P', Pw', {}, R', Rw')"
    and left: "left_linear_trs Rw"
    and finite1: "finite_dpp (nfs,m,P', Pw', {}, R', Rw')"
    and finite2: "finite_dpp (nfs,m,P - Ps, Pw - Ps,{},{},Rw - Rs)"
  shows "finite_dpp (nfs,m,P, Pw, {}, {}, Rw)"
proof (rule ccontr)
  let ?D = "(nfs,m,P,Pw,{},{},Rw) :: ('f,'v)dpp"
  let ?D' = "(nfs,m,Ps \<inter> (P \<union> Pw), P \<union> Pw - Ps, {}, Rs \<inter> ({} \<union> Rw), {} \<union> Rw - Rs)"
  assume "\<not> ?thesis"
  then obtain s t \<sigma> where chain: "min_ichain ?D s t \<sigma>" unfolding finite_dpp_def by auto
  let ?F = "(funas_args_trs (P \<union> Pw) \<union> funas_trs Rw)"
  let ?F' = "(funas_trs ({} \<union> Rw) \<union> funas_args_trs (P \<union> Pw))"
  from  proc[unfolded fcc_proc.simps fcc_cond_def Let_def]
  have Pcond: " (\<forall>(s, t)\<in>Ps \<inter> (P \<union> Pw) \<union> (P \<union> Pw - Ps). is_Fun s \<and> is_Fun t) \<and>
   (\<forall>(s, t)\<in>Ps \<inter> (P \<union> Pw) \<union> (P \<union> Pw - Ps).
       \<not> defined (Rw \<inter> Rs \<union> (Rw - Rs)) (the (root t)))"
       and wf: "wf_trs (Rw \<inter> Rs \<union> (Rw - Rs))" by auto
  have id: "Ps \<inter> (P \<union> Pw) \<union> (P \<union> Pw - Ps) = P \<union> Pw" "(Rw \<inter> Rs) \<union> (Rw - Rs) = Rw" by blast+
  from Pcond[unfolded this]
  have Pcond: "\<And>s t. (s, t) \<in> P \<union> Pw \<Longrightarrow>
          is_Fun s \<and> is_Fun t \<and> \<not> defined Rw (the (root t))" by auto
  have "\<exists> \<sigma>. min_ichain_sig ?D ?F s t \<sigma>"
  by (rule left_linear_min_ichain_imp_min_ichain_sig[OF left subset_refl Pcond chain],
    insert wf[unfolded wf_trs_def], force+)
  then obtain \<sigma> where chain: "min_ichain_sig ?D ?F' s t \<sigma>" by auto
  have no_chain: "\<not> min_ichain_sig ?D' ?F' s t \<sigma>"
  proof
    assume chain: "min_ichain_sig ?D' ?F' s t \<sigma>"
    have "\<exists> s t. min_ichain (nfs,m,P',Pw',{},R',Rw') s t \<sigma>"
      by (rule fcc_proc_chain[OF proc, unfolded id, of s t \<sigma>],
        insert chain, simp add: Int_commute[of Rs])
    with finite1 show False unfolding finite_dpp_def by blast
  qed
  from min_ichain_split_sig[OF chain no_chain] obtain i where
    "min_ichain (nfs,m,P - Ps, Pw - Ps, {}, {}, Rw - Rs) (shift s i) (shift t i) (shift \<sigma> i)" by auto
  with finite2 show False unfolding finite_dpp_def by blast
qed

end

