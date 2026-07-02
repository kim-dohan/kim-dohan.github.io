(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory DP_Transformation_Impl
imports
  TRS.DP_Transformation
  Framework.QDP_Framework_Impl
  TRS.Q_Restricted_Rewriting_Impl
begin

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

definition DP_list :: "('f, 'v) rules \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules"
where
  "DP_list R d_list =
    concat (map (\<lambda>lr.
      let l = fst lr; s = \<sharp> l in
      map (\<lambda>u. (s, \<sharp> u)) (filter
        (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> (the (root u)) \<in> set d_list) (supteq_list (snd lr)))) R)"

lemma DP_list [simp]:
  shows "set (DP_list R F) = DP_on \<sharp> (set F) (set R)" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix s t assume "(s, t) \<in> ?L" 
    then obtain l r u where "(l, r) \<in> set R" and "r \<unrhd> u" and "\<not> l \<rhd> u"
      and "s = \<sharp> l" and "t = \<sharp> u"
      and "is_Fun u" and "the (root u) \<in> set F"
        unfolding DP_list_def Let_def by auto
    then show "(s, t) \<in> DP_on \<sharp> (set F) (set R)" unfolding DP_on_def by (cases u) auto      
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix s t assume "(s, t) \<in> ?R"
    then obtain lr u where "lr \<in> set R" and "snd lr \<unrhd> u" and "\<not> fst lr \<rhd> u"
      and "s = \<sharp> (fst lr)" and "t = \<sharp> u"
      and "is_Fun u" and "the (root u) \<in> set F" unfolding DP_on_def by auto
    then show "(s, t) \<in> ?L" unfolding DP_list_def Let_def by auto
  qed
qed

end

context
  fixes shp :: "'f \<Rightarrow> 'f::{showl, linorder}"
begin

interpretation sharp_syntax .

(* COMMENT: we silently handle relative rules as strict rules in this step.
  Advantage: other choices like putting Decreasing rules in relative part can also silently be done, and no explict step: Rw_into_R *) 
definition
  dependency_pairs_tt ::
    "('tp, 'f, 'v::{showl,linorder}) tp_ops \<Rightarrow>
    ('dpp, 'f, 'v) dpp_ops \<Rightarrow> 'tp \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'dpp result"
where
  "dependency_pairs_tt I J tp nfs m P \<equiv> 
  let R = tp_ops.rules I tp;
      Q = tp_ops.Q I tp;
      iQ = tp_ops.is_QNF I tp;
      U = filter (applicable_rule_impl iQ) R
  in
  check_return (do {
     (if isOK(check_wf_trs U) then succeed else 
     check (nfs \<and> tp_ops.nfs I tp \<and> tp_ops.NFQ_subset_NF_rules I tp \<and> (\<forall> l \<in> set (map fst R). is_Fun l)) 
       (showsl_lit (STR ''neither is the TRS well-formed, nor is the restriction to innermost with normal form substitutions present'')));
     check_allm (\<lambda> q. check_no_var q) Q;
     let Qr = map (\<lambda> q. case q of Fun f ss \<Rightarrow> (f,length ss)) Q;
     let D = defined_list U;
     check_allm (\<lambda> (f,n). check ((\<sharp> f,n) \<notin> set D) 
       (showsl_lit (STR ''sharping '') \<circ> showsl f \<circ> showsl_lit (STR '' yields the defined symbol '') \<circ> showsl (\<sharp> f))) D;
     check_allm (\<lambda> (f,n). check ((\<sharp> f,n) \<notin> set Qr) 
       (showsl_lit (STR ''sharping '') \<circ> showsl f \<circ> showsl_lit (STR '' yields the symbol '') \<circ> showsl (\<sharp> f) \<circ> showsl_lit (STR '' which is a root of Q''))) D;
     let P' = set P;
     check_all (\<lambda> dp. dp \<in> P' \<or> (\<exists> dp' \<in> set P. dp =\<^sub>v dp')) (DP_list \<sharp> U D)
       <+? (\<lambda>dp. showsl_lit (STR ''the DP '') \<circ> showsl_rule dp
         \<circ> showsl_lit (STR '' does not appear in the DP problem\<newline>''))
   } <+? (\<lambda>s. showsl_lit (STR ''the DP-transformation is not applied correctly.\<newline>'') \<circ> s))
   (dpp_ops.mk J nfs m P [] Q [] R)"

lemma dependency_pairs_tt:
  assumes I: "tp_spec I"
  and J: "dpp_spec J"
  and tt: "dependency_pairs_tt I J tp nfs m P = return d"
  and fin: "finite_dpp (dpp_ops.dpp J d)"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  interpret spec: dpp_spec J by fact
  let ?R = "set (R tp)"
  let ?Rw = "set (Rw tp)"
  let ?Q = "set (Q tp)"
  let ?Qr = "map (\<lambda>q. case q of Fun f ss \<Rightarrow> (f, length ss)) (Q tp)"
  let ?nfs = "NFS tp"
  let ?B = "set (R tp) \<union> set (Rw tp)"
  let ?u = "{x. (x \<in> set (R tp) \<or> x \<in> set (Rw tp)) \<and> applicable_rule ?Q x}"
  let ?U = "applicable_rules ?Q ?B"
  have u: "?u = ?U" by (auto simp: applicable_rules_def)
  note tt = tt[unfolded dependency_pairs_tt_def Let_def, simplified]
  note ttu = tt[unfolded u]
  from tt have idpp: "d = dpp_ops.mk J nfs m P [] (Q tp) [] (rules tp)" by auto
  from ttu have P: "\<And> dp. dp \<in> DP \<sharp> ?U \<Longrightarrow> dp \<in> set P \<or> (\<exists> dp' \<in> set P. dp =\<^sub>v dp')" by (auto simp: u)
  have wf: "wf_qtrs nfs ?Q ?B \<and> qrstep nfs ?Q ?B = qrstep ?nfs ?Q ?B"
  proof (cases "wf_trs ?U")
    case True
    have "wwf_qtrs ?Q ?B" using True unfolding wwf_qtrs_def u[symmetric] wf_trs_def by auto
    with wwf_qtrs_imp_nfs_switch[OF this, of nfs ?nfs]
    show ?thesis using ttu unfolding wf_qtrs_def by auto
  next
    case False
    with ttu
    have "nfs \<and> ?nfs \<and> NF_terms (set (Q tp)) \<subseteq> NF_trs (set (rules tp)) \<and> (\<forall>t\<in>lhss (set (rules tp)). is_Fun t)" by auto
    then show ?thesis unfolding wf_qtrs_def wwf_inn_qtrs_def using ttu by auto
  qed
  then have wf: "wf_qtrs nfs ?Q ?B" and switch: "qrstep nfs ?Q ?B = qrstep ?nfs ?Q ?B" by blast+
  have SN: "SN (qrstep nfs ?Q ?B)"
  proof (rule ccontr)
    assume nSN: "\<not> ?thesis"
    have easy: "\<And> p. \<lbrakk> \<And> f n. p f n\<rbrakk> \<Longrightarrow> True = (\<forall> f n. p f n)" by blast
    have "\<exists> s t \<sigma>. min_ichain (initial_dpp \<sharp> nfs True ?Q ?B) s t \<sigma>"
    proof (rule not_SN_imp_min_ichain[OF wf nSN _ easy])
      fix f n
      show "defined (applicable_rules ?Q ?B) (f, n) \<longrightarrow> 
      \<not> defined (applicable_rules ?Q ?B) (\<sharp> f, n)" using ttu by auto
    next
      fix f n and ss :: "('f, 'b) term list"
      assume d: "defined (applicable_rules ?Q ?B) (f,n)" "length ss = n"
      with ttu have not: "(\<sharp> f,n) \<notin> set ?Qr" by auto
      from d have n: "n = length ss" by auto
      show "Fun (\<sharp> f) ss \<notin> ?Q" using not unfolding n by force
    qed
    then obtain s t \<sigma> where mic: "min_ichain (initial_dpp \<sharp> nfs True ?Q ?B) s t \<sigma>" by blast
    then have mic: "min_ichain (initial_dpp \<sharp> nfs m ?Q ?B) s t \<sigma>" by (simp add: minimal_cond_def ichain.simps)
    let ?P = "DP \<sharp> ?U"
    let ?init = "(nfs, m, ?P, {}, ?Q, {}, ?B)"
    from mic have inf: "\<not> finite_dpp ?init" unfolding finite_dpp_def initial_dpp.simps by blast
    have "finite_dpp
      (nfs, m, ?P, {}, ?Q, set [], set (rules tp))"
    proof (rule finite_dpp_rename_vars[OF fin[unfolded idpp dpp_spec.mk_sound[OF J]]])
      fix dp
      assume "dp \<in> ?P"
      from P[OF this] show "\<exists>dp'. dp' \<in> set P \<and> dp =\<^sub>v dp'" using eq_rule_mod_vars_refl[of dp]
        by blast
    qed auto
    with inf show False by auto
  qed
  with switch have "SN (qrstep ?nfs ?Q ?B)" by simp
  then have SN: "SN_qrel (?nfs, ?Q, ?B, {})" by simp
  show ?thesis unfolding qreltrs_sound
    by (rule SN_qrel_mono[OF subset_refl _ _ SN]) simp_all
qed

end

end
