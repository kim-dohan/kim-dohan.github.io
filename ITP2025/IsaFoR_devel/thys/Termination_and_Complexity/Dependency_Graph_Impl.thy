(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Dependency_Graph_Impl
  imports
    Auxx.Graph
    Auxx.Multi_Map
    TRS.Tcap_Impl
    Icap_Impl
    TRS.QDP_Framework
    Dependency_Graph
    Innermost_Usable_Rules_Impl
    Nonreach.Gtcap_Impl
    Tcap_Dpp_Impl
begin

(* from AFP/Automatic_Refinement/Lib/Words *)
hide_fact suffix_def
hide_const suffix

definition
  is_iedg_edge_dpp ::
    "('d,'f :: {showl, compare_order},string)dpp_ops \<Rightarrow> 'd \<Rightarrow> ('f,string)rule \<Rightarrow> ('f,string)term \<Rightarrow> bool"
where
  "is_iedg_edge_dpp I d \<equiv> let qnf = dpp_ops.is_QNF I d;
                              ic = icap_impl_dpp_mv I d;
                              R = dpp_ops.rules I d;
                              urules = inn_usable_rules_pair I d in
      (\<lambda> (s,t). let cst = ic [s] t;
                    urls = reverse_rules (urules (s,t));
                    ic'  = icap_impl' (is_NF_terms []) urls
         in (\<lambda> u.
            (case mgu_class cst u of None \<Rightarrow> False | Some \<mu>
                \<Rightarrow> qnf (mv_xvar s \<cdot> \<mu>) \<and> qnf (mv_yvar u \<cdot> \<mu>))
           \<and> (let cu = ic' [] u in 
               case mgu_class cu t of None \<Rightarrow> False | Some \<mu>
                \<Rightarrow> qnf (mv_yvar s \<cdot> \<mu>) 
             )))"

lemma is_iedg_edge_dpp_sound:
  fixes I::"('d, 'f::{showl, compare_order}, string) dpp_ops" and d::"'d"
  defines q: "q \<equiv> dpp_ops.Q I d"
      and r: "r \<equiv> dpp_ops.rules I d"
      and nfs: "nfs \<equiv> dpp_ops.nfs I d"
      and m: "m \<equiv> dpp_ops.minimal I d"
  assumes I: "dpp_spec I"
  and sNF: "s \<cdot> \<sigma> \<in> NF_terms (set q)"
  and uNF: "u \<cdot> \<tau> \<in> NF_terms (set q)"
  and nfs1: "NF_subst nfs (s,t) \<sigma> (set q)"
  and nfs2: "NF_subst nfs (u,v) \<tau> (set q)"
  and tSN: "m \<Longrightarrow> SN_on (qrstep nfs (set q) (set r)) {t \<cdot> \<sigma>}" 
  and steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs (set q) (set r))^*"
  shows "is_iedg_edge_dpp I d (s,t) u"
proof -
  note Id_on_empty[simp del]
  interpret dpp_spec I by fact
  let ?U = "inn_usable_rules_pair I d (s,t)"
  let ?nfs = "NFS d"
  let ?m = "M d"
  obtain U where U: "U = reverse_rules ?U" by auto
  from sNF uNF nfs1 nfs2 steps tSN have "((s,t),(u,v)) \<in> DG ?nfs ?m UNIV (set (dpp_ops.Q I d)) (set (dpp_ops.rules I d))" unfolding 
    DG_def r q nfs m by auto  
  with IEDG[of ?nfs ?m] have edge: "((s,t),(u,v)) \<in> IEDG UNIV (set (dpp_ops.Q I d)) (set (dpp_ops.rules I d))" by auto
  from inn_usable_rules_pair[OF I refl steps[unfolded q r nfs] sNF[unfolded q nfs] NF_subst_right[OF _ nfs1[unfolded q nfs]] 
    tSN[unfolded q r nfs m]]
  have "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs (set q) (set ?U))^*" unfolding q nfs .
  then have "(u \<cdot> \<tau>, t \<cdot> \<sigma>) \<in> (rstep (set U))^*"
    unfolding U reverse_rules 
    unfolding rstep_converse
    unfolding rtrancl_converse
    using rtrancl_mono[OF qrstep_subset_rstep] by auto
  then have steps: "(u \<cdot> \<tau>, t \<cdot> \<sigma>) \<in> (qrstep nfs {} (set U))^*" by simp
  from icap_mv_mgu[OF steps, of "{}"] obtain \<mu> \<delta> where mgu: 
    "mgu_class (icap_mv (set U) {} {} u) t = Some \<mu>"
    and \<sigma>: "\<And> s. s \<cdot> \<sigma> = mv_yvar s \<cdot> \<mu> \<cdot> \<delta>" by auto
  note sNF = NF_instance[OF sNF[unfolded \<sigma>]]
  have edge2: "case mgu_class (icap_impl' (is_NF_terms []) U [] u)
           t of
     None \<Rightarrow> False
     | Some \<mu> \<Rightarrow>
         is_QNF d (mv_yvar s \<cdot> \<mu>)"
    unfolding icap_impl'_sound using mgu sNF uNF q by simp
  show ?thesis using edge edge2
    unfolding is_iedg_edge_dpp_def Let_def IEDG_def split U
    unfolding icap_impl_dpp_icap_mv[OF I, of d] by auto
qed

lemma is_iedg_edge_dpp_DG_sound:
  fixes I::"('d, 'f::{showl, compare_order}, string) dpp_ops" and d::"'d"
  defines q: "q \<equiv> dpp_ops.Q I d"
      and r: "r \<equiv> dpp_ops.rules I d"
      and nfs: "nfs \<equiv> dpp_ops.nfs I d"
      and m: "m \<equiv> dpp_ops.minimal I d"
  assumes I: "dpp_spec I"
  and edge: "((s,t),(u,v)) \<in> DG nfs m p (set q) (set r)"
  shows "is_iedg_edge_dpp I d (s,t) u"
proof -
  from edge[unfolded DG_def] obtain \<sigma> \<tau> where
   steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs (set q) (set r))^*"
   and NF: "s \<cdot> \<sigma> \<in> NF_terms (set q)" 
          "u \<cdot> \<tau> \<in> NF_terms (set q)"
   and nf: "NF_subst nfs (s, t) \<sigma> (set q)" "NF_subst nfs (u, v) \<tau> (set q)" 
   and min: "m \<Longrightarrow> SN_on (qrstep nfs (set q) (set r)) {t \<cdot> \<sigma>}"
    by blast
  show ?thesis
    by (rule is_iedg_edge_dpp_sound[OF I, of _ \<sigma> _ _ \<tau> _ v], insert NF nf min steps nfs q r m, auto) 
qed

fun graph_approx_rt_sym_main where 
  "graph_approx_rt_sym_main m (GCFun f ts) = Multi_Map.lookup m None @ Multi_Map.lookup m (Some (f,length ts))"
| "graph_approx_rt_sym_main m GCHole = Multi_Map.values m"

fun graph_approx_rt_sym where
  "graph_approx_rt_sym m ( _, (_, ct, _)) = graph_approx_rt_sym_main m ct"

declare graph_approx_rt_sym.simps[simp del]

definition
  check_dep_graph_proc ::
    "('dpp, 'f::{showl, compare_order}, string) dpp_ops \<Rightarrow> 'dpp
    \<Rightarrow> ('a option \<times> ('f, string) rules) list \<Rightarrow> showsl check"
where
  "check_dep_graph_proc I dpp dps = do {
    let c      = tcapRM_dpp I dpp;
    let rc     = reverse_tcapRM_dpp I dpp;
    let iedg   = is_iedg_edge_dpp I dpp;
    let P      = dpp_ops.pairs I dpp;
    let R = dpp_ops.rules I dpp;
    let F = funas_trs_list R;
    let gt_fun = mk_gt_fun R;
    let rm = dpp_ops.rules_map I dpp;
    let nlv = dpp_ops.rules_no_left_var I dpp;
    check_subseteq P (concat (map snd dps))
      <+? (\<lambda>dp. showsl_lit (STR ''Dependency Pair '') \<circ> showsl_rule dp \<circ> showsl_lit (STR '' is missing in decomposition\<newline>''));
    check_graph_decomp
      (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_rt_sym
      Multi_Map.insert
      (\<lambda>(((s, t), (_, ct, ict)), ((u, _), (cu, _, _))).
        Ground_Context.match ct u
        \<and> Ground_Context.match cu t
        \<and> ict u
        \<and> \<not> (nonreachable_gtcapRM F nlv (R \<noteq> []) gt_fun rm t u)
      )
      (map (\<lambda>(real, Cs). (real \<noteq> None, (map (\<lambda>(s, t). ((s, t), (rc s, c t, iedg (s,t)))) Cs))) dps)
        <+? (\<lambda>s. showsl_lit (STR ''our estimation (EDG*** + IEDG***) could not show that you have a valid decomposition '')
        \<circ> showsl_lit (STR ''due to the following reason\<newline>'') \<circ> s)
  }"

lemma check_dep_graph_proc_sound:
  assumes I: "dpp_spec I"
    and check: "isOK (check_dep_graph_proc I d edps)" 
    and chain: "min_ichain (dpp_ops.dpp I d) s t \<sigma> "
  shows "\<exists>edp\<in>set edps. fst edp \<noteq> None
    \<and> (\<exists>i. min_ichain (dpp_ops.nfs I d, dpp_ops.minimal I d, set (snd edp), {}, set (dpp_ops.Q I d),
    set (dpp_ops.R I d), set (dpp_ops.Rw I d) :: ('f :: {compare_order,showl},string)trs) (shift s i) (shift t i) (shift \<sigma> i))"
proof -
  let ?c  = "tcapRM_dpp I d"
  let ?rc = "reverse_tcapRM_dpp I d"
  let ?Pb = "set (dpp_ops.pairs I d)"
  let ?Rb = "set (dpp_ops.rules I d)"
  let ?Q  = "set (dpp_ops.Q I d)"
  let ?R  = "set (dpp_ops.R I d)"
  let ?Rw = "set (dpp_ops.Rw I d)"
  let ?RR = "dpp_ops.rules I d" 
  let ?iedg   = "is_iedg_edge_dpp I d"
  let ?nfs = "dpp_ops.nfs I d"
  let ?m = "dpp_ops.minimal I d"
  let ?F = "funas_trs_list ?RR"
  let ?gt_fun = "mk_gt_fun ?RR"
  let ?rm = "dpp_ops.rules_map I d"
  let ?nlv = "dpp_ops.rules_no_left_var I d"
  let ?gtcap = "\<lambda> t u. \<not> (nonreachable_gtcapRM ?F ?nlv (?RR \<noteq> []) ?gt_fun ?rm t u)" 
  from check
    have subset: "set (dpp_ops.pairs I d) \<subseteq> set (concat (map snd edps))" (is "_ \<subseteq> ?dps")
    and scc: "isOK (check_graph_decomp (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_rt_sym
      Multi_Map.insert
    (\<lambda>(((s, t), (_, ct, ict)),((u, _), (cu, _, _))).
      Ground_Context.match ct u \<and> Ground_Context.match cu t
      \<and> ict u
      \<and> ?gtcap t u
    )
    (map (\<lambda>(real, Cs).
      (real \<noteq> None, (map (\<lambda>(s,t).
        ((s, t), (reverse_tcapRM_dpp I d s, tcapRM_dpp I d t,
                  ?iedg (s,t)))) Cs))) edps))"
    (is "isOK (check_graph_decomp ?sshow ?empty ?cands ?ins ?echeck (map ?conv edps))")
    unfolding check_dep_graph_proc_def
    by (auto simp: Let_def)
  let ?quads = "map ?conv edps"
  note sound = dpp_spec.dpp_spec_sound[OF I]
    dpp_spec.tcapRM_dpp[OF I] dpp_spec.reverse_tcapRM_dpp[OF I]
  from chain have inP: "\<And>i. (s i, t i) \<in> ?Pb"
    and betw: "\<And>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep ?nfs ?Q ?Rb)^*"
    and NFs: "\<And>i. s i \<cdot> \<sigma> i \<in> NF_terms ?Q" 
    and nfs: "\<And> i. NF_subst ?nfs (s i, t i) (\<sigma> i) ?Q"
    and SN: "\<And>i. ?m \<Longrightarrow> SN_on (qrstep ?nfs ?Q ?Rb) {t i \<cdot> \<sigma> i}"
    by (auto simp: ichain.simps sound minimal_cond_def)
  let ?p = "\<lambda>i. ((s i, t i), (?rc (s i), ?c (t i), ?iedg (s i,t i)))"
  let ?ps = "\<lambda>i. (s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i)"
  fix whatever
  {
    fix n
    from qrsteps_into_rsteps[OF betw[of n]]
      have steps: "(t n \<cdot> \<sigma> n, s (Suc n) \<cdot> \<sigma> (Suc n)) \<in> (rstep ?Rb)^* " by auto
    have "Ground_Context.match (tcap ?Rb (t n)) (s (Suc n))
      \<and> Ground_Context.match (tcap (?Rb^-1) (s (Suc n))) (t n)"
      using match_tcap_sound[OF steps] match_tcap_inv_sound[OF steps] by auto
    moreover
      from is_iedg_edge_dpp_sound[OF I NFs[of n] NFs nfs nfs SN betw]
      have "?iedg (s n, t n) (s (Suc n))" .
    moreover
    have "?gtcap (t n) (s (Suc n))" 
    proof
      assume *: "nonreachable_gtcapRM ?F ?nlv (?RR \<noteq> []) ?gt_fun ?rm (t n) (s (Suc n))" 
      show False 
      proof (rule nonreach_gtcap[OF _ _ * steps])
        show "dpp_ops.rules_no_left_var I d = (\<forall>lr\<in>set (dpp_ops.rules I d). is_Fun (fst lr))" 
          unfolding sound by force
        fix fn
        show "set (dpp_ops.rules_map I d fn) = {(l, r). (l, r) \<in> set (dpp_ops.rules I d) \<and> root l = Some fn}" 
          by (cases fn, auto simp: sound)
      qed
    qed
    ultimately have "Ground_Context.match (tcap ?Rb (t n)) (s (Suc n))
      \<and> Ground_Context.match (tcap (?Rb^-1) (s (Suc n))) (t n)
      \<and> ?iedg (s n, t n) (s (Suc n))
      \<and> ?gtcap (t n) (s (Suc n))" by simp
  }
  note 1 = this
  have one: "\<And>n. ?echeck (?p n, ?p (Suc n))"
  proof -
    fix n
    from 1[of n]
    show "?echeck (?p n, ?p (Suc n))" unfolding sound by simp
  qed
  from inP subset have two: "path_nodes ?p \<subseteq> set (concat (map snd ?quads))"
    unfolding path_nodes_def
    by (auto split: prod.splits) fastforce
  {
    fix st aa ct ba s t x m
    assume kf: "Multi_Map.key_fun m = root \<circ> fst \<circ> fst" 
      and mem: "((s, t), x) \<in> set (Multi_Map.values m)"
      and match: "Ground_Context.match ct s"
    have "((s, t), x) \<in> set (graph_approx_rt_sym m (st, aa, ct, ba))"
    proof (cases ct)
      case GCHole
      with mem show ?thesis unfolding graph_approx_rt_sym.simps by auto
    next
      case (GCFun f ts)
      with match have "root s = None \<or> root s = Some (f,length ts)"
        unfolding Ground_Context.match_def by (cases s, auto)
      with mem show ?thesis unfolding graph_approx_rt_sym.simps GCFun
        by (simp add: kf)
    qed
  } note approx = this
  have "\<exists> q D. ?p =\<dots> q \<and> D \<in> set (map snd (filter fst ?quads)) \<and> path_nodes q \<subseteq> set D"
    by (rule check_graph_decomp_sound[of "\<lambda> m. set (Multi_Map.values m)", 
    OF values_empty values_insert, of "\<lambda> m. Multi_Map.key_fun m = (root o fst o fst)",
    OF key_fun_empty _ _ scc one two], force, insert approx, force)
  then
  obtain q D where 
    suffix: "?p =\<dots> q" and 
    mem: "D \<in> set (map snd (filter fst ?quads))" and 
    ending: "path_nodes q \<subseteq> set D" by blast
  from mem obtain C S
    where C: "(S, C) \<in> set edps \<and> D = snd (?conv (S, C)) \<and> S \<noteq> None" by force
  from suffix obtain n where pq: "\<And>m. (?p (m + n) = q m)" unfolding Graph.suffix_def by blast
  {
    fix i
    have "(shift s n i, shift t n i) \<in> set C"
      using inP ending C pq[of i] unfolding path_nodes_def by force
  }
  note CP = this
  from chain CP
    have ichain: "min_ichain (?nfs,?m,set C, {}, ?Q, ?R, ?Rw) (shift s n) (shift t n) (shift \<sigma> n)"
    unfolding sound ichain.simps min_ichain.simps
    by (intro conjI allI, auto simp: minimal_cond_def)
  from ichain C
    have "\<exists>edp \<in> set edps. fst edp \<noteq> None
    \<and> min_ichain (?nfs,?m,set (snd edp), {}, ?Q, ?R, ?Rw) (shift s n) (shift t n) (shift \<sigma> n)"
    by force
  then show ?thesis by blast
qed

fun graph_approx_edg_rt_sym where
  "graph_approx_edg_rt_sym m ( _, (_, ct)) = graph_approx_rt_sym_main m ct"

declare graph_approx_edg_rt_sym.simps[simp del]

definition
  check_ac_dep_graph_proc ::
    "('dpp, 'f::{showl, compare_order}, string) ac_dpp_ops \<Rightarrow> 'dpp
    \<Rightarrow> ('a option \<times> ('f, string) rules) list \<Rightarrow> showsl check"
where
  "check_ac_dep_graph_proc I dpp dps = do {
    let c      = tcapRM_ac_dpp I dpp;
    let rc     = reverse_tcapRM_ac_dpp I dpp;
    let P      = ac_dpp_ops.pairs I dpp;
    check_subseteq P (concat (map snd dps))
      <+? (\<lambda>dp. showsl_lit (STR ''Dependency Pair '') \<circ> showsl_rule dp \<circ> showsl_lit (STR '' is missing in decomposition'')
        \<circ> showsl_nl);
    check_graph_decomp
      (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_edg_rt_sym
      Multi_Map.insert
      (\<lambda>(((s, t), (_, ct)), ((u, _), (cu, _))).
        Ground_Context.match ct u
        \<and> Ground_Context.match cu t
      )
      (map (\<lambda>(real, Cs). (real \<noteq> None, (map (\<lambda>(s, t). ((s, t), (rc s, c t))) Cs))) dps)
        <+? (\<lambda>s. showsl_lit (STR ''our estimation (EDG***) could not show that you have a valid decomposition '')
        \<circ> showsl_lit (STR ''due to the following reason'') \<circ> showsl_nl \<circ> s)
  }"

lemma check_ac_dep_graph_proc_sound:
  assumes I: "ac_dpp_spec I"
    and check: "isOK (check_ac_dep_graph_proc I d edps)" 
    and chain: "min_relchain (ac_dpp_ops.ac_dpp I d) s t \<sigma> "
  shows "\<exists>edp\<in>set edps. fst edp \<noteq> None
    \<and> (\<exists>i. min_relchain (set (snd edp), {},  set (ac_dpp_ops.R I d), 
    set (ac_dpp_ops.Rw I d) :: ('f :: {compare_order,showl},string)trs,
    set (ac_dpp_ops.E I d)) (shift s i) (shift t i) (shift \<sigma> i))"
proof -
  let ?c  = "tcapRM_ac_dpp I d"
  let ?rc = "reverse_tcapRM_ac_dpp I d"
  let ?Pb = "set (ac_dpp_ops.pairs I d)"
  let ?Rb = "set (ac_dpp_ops.R I d @ ac_dpp_ops.Rw I d @ ac_dpp_ops.E I d)"
  let ?R  = "set (ac_dpp_ops.R I d)"
  let ?Rw = "set (ac_dpp_ops.Rw I d)"
  let ?E  = "set (ac_dpp_ops.E I d)"
  from check
    have subset: "set (ac_dpp_ops.pairs I d) \<subseteq> set (concat (map snd edps))" (is "_ \<subseteq> ?dps")
    and scc: "isOK (check_graph_decomp (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_edg_rt_sym
      Multi_Map.insert
    (\<lambda>(((s, t), (_, ct)),((u, _), (cu, _))).
      Ground_Context.match ct u \<and> Ground_Context.match cu t
    )
    (map (\<lambda>(real, Cs).
      (real \<noteq> None, (map (\<lambda>(s,t).
        ((s, t), (reverse_tcapRM_ac_dpp I d s, tcapRM_ac_dpp I d t))) Cs))) edps))"
    (is "isOK (check_graph_decomp ?sshow ?empty ?cands ?ins ?echeck (map ?conv edps))")
    unfolding check_ac_dep_graph_proc_def
    by (auto simp: Let_def)
  let ?quads = "map ?conv edps"
  note sound = ac_dpp_spec.ac_dpp_spec_sound[OF I]
    ac_dpp_spec.tcapRM_ac_dpp[OF I] ac_dpp_spec.reverse_tcapRM_ac_dpp[OF I]
  from chain have inP: "\<And>i. (s i, t i) \<in> ?Pb"
    and betw: "\<And>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (rstep ?Rb)^*"
    by (auto simp: min_relchain.simps sound ac_simps)
  let ?p = "\<lambda>i. ((s i, t i), (?rc (s i), ?c (t i)))"
  let ?ps = "\<lambda>i. (s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i)"
  fix whatever
  {
    fix n
    from betw[of n]
      have steps: "(t n \<cdot> \<sigma> n, s (Suc n) \<cdot> \<sigma> (Suc n)) \<in> (rstep ?Rb)^* " by auto
    have "Ground_Context.match (tcap ?Rb (t n)) (s (Suc n))
      \<and> Ground_Context.match (tcap (?Rb^-1) (s (Suc n))) (t n)"
      using match_tcap_sound[OF steps] match_tcap_inv_sound[OF steps] by auto
    then have "Ground_Context.match (tcap ?Rb (t n)) (s (Suc n))
      \<and> Ground_Context.match (tcap (?Rb^-1) (s (Suc n))) (t n)"  by simp
  }
  note 1 = this
  have one: "\<And>n. ?echeck (?p n, ?p (Suc n))"
  proof -
    fix n
    from 1[of n]
    show "?echeck (?p n, ?p (Suc n))" unfolding sound by simp
  qed
  from inP subset have two: "path_nodes ?p \<subseteq> set (concat (map snd ?quads))"
    unfolding path_nodes_def
    by (auto split: prod.splits) fastforce
  {
    fix st aa ct s t x m
    assume kf: "Multi_Map.key_fun m = root \<circ> fst \<circ> fst" 
      and mem: "((s, t), x) \<in> set (Multi_Map.values m)"
      and match: "Ground_Context.match ct s"
    have "((s, t), x) \<in> set (graph_approx_edg_rt_sym m (st, aa, ct))"
    proof (cases ct)
      case GCHole
      with mem show ?thesis unfolding graph_approx_edg_rt_sym.simps by auto
    next
      case (GCFun f ts)
      with match have "root s = None \<or> root s = Some (f,length ts)"
        unfolding Ground_Context.match_def by (cases s, auto)
      with mem show ?thesis unfolding graph_approx_edg_rt_sym.simps GCFun
        by (simp add: kf)
    qed
  } note approx = this
  have "\<exists> q D. ?p =\<dots> q \<and> D \<in> set (map snd (filter fst ?quads)) \<and> path_nodes q \<subseteq> set D"
    by (rule check_graph_decomp_sound[of "\<lambda> m. set (Multi_Map.values m)", 
    OF values_empty values_insert, of "\<lambda> m. Multi_Map.key_fun m = (root o fst o fst)",
    OF key_fun_empty _ _ scc one two], force, insert approx, force)
  then
  obtain q D where 
    suffix: "?p =\<dots> q" and 
    mem: "D \<in> set (map snd (filter fst ?quads))" and 
    ending: "path_nodes q \<subseteq> set D" by blast
  from mem obtain C S
    where C: "(S, C) \<in> set edps \<and> D = snd (?conv (S, C)) \<and> S \<noteq> None" by force
  from suffix obtain n where pq: "\<And>m. (?p (m + n) = q m)" unfolding Graph.suffix_def by blast
  {
    fix i
    have "(shift s n i, shift t n i) \<in> set C"
      using inP ending C pq[of i] unfolding path_nodes_def by force
  }
  note CP = this
  from chain CP
    have ichain: "min_relchain (set C, {}, ?R, ?Rw, ?E) (shift s n) (shift t n) (shift \<sigma> n)"
    unfolding sound min_relchain.simps by auto
  from ichain C
    have "\<exists>edp \<in> set edps. fst edp \<noteq> None
    \<and> min_relchain (set (snd edp), {}, ?R, ?Rw, ?E) (shift s n) (shift t n) (shift \<sigma> n)"
    by force
  then show ?thesis by blast
qed

definition
  dep_graph_proc ::
    "('dpp, 'f::{showl, compare_order}, string) dpp_ops \<Rightarrow> 'dpp
    \<Rightarrow> ('a option \<times> ('f, string) rules) list \<Rightarrow> ('a \<times> 'dpp) list result"
where
  "dep_graph_proc I d dps \<equiv> check_return
    (check_dep_graph_proc I d dps)
    (map (\<lambda>aP. (the (fst aP), dpp_ops.intersect_pairs I d (snd aP)))
         (filter (\<lambda> aP. fst aP \<noteq> None) dps))"

lemma dep_graph_proc :
  assumes I: "dpp_spec I"
    and proc: "dep_graph_proc I d dps = return dpps"
    and rec: "\<And>a d'. (a, d') \<in> set dpps \<Longrightarrow> finite_dpp (dpp_ops.dpp I d')"
  shows "finite_dpp (dpp_ops.dpp I d)"
  unfolding finite_dpp_def
proof
  let ?P = "set (dpp_ops.P I d)"
  let ?Pw = "set (dpp_ops.Pw I d)"
  let ?Q = "set (dpp_ops.Q I d)"
  let ?R = "set (dpp_ops.R I d)"
  let ?Rw = "set (dpp_ops.Rw I d)"
  let ?nfs = "dpp_ops.nfs I d"
  let ?m = "dpp_ops.minimal I d"
  let ?Dpp = "(?nfs,?m,?P, ?Pw, ?Q, ?R, ?Rw)"
  let ?DPP = "dpp_ops.dpp I d"
  note sound = dpp_spec.dpp_spec_sound[OF I]
  assume "\<exists>s t \<sigma>. min_ichain ?DPP s t \<sigma>"
  from this obtain s t \<sigma> where michain: "min_ichain ?DPP s t \<sigma>" by auto
  then have mc: "min_ichain ?Dpp s t \<sigma>" unfolding sound by auto
  from proc[unfolded dep_graph_proc_def]
    have check: "isOK (check_dep_graph_proc I d dps)"
    and dpps: "dpps = map (\<lambda>aP. (the (fst aP), dpp_ops.intersect_pairs I d (snd aP)))
                          (filter (\<lambda>aP. fst aP \<noteq> None) dps)"
    by auto
  from check_dep_graph_proc_sound[OF I check michain]
  obtain edp i where nearly: "edp \<in> set dps" "fst edp \<noteq> None"
    and ic: "min_ichain (?nfs,?m,set (snd edp), {}, ?Q, ?R, ?Rw) (shift s i) (shift t i) (shift \<sigma> i)"
    by auto
  then have ic: "ichain (?nfs,?m,set (snd edp), {}, ?Q, ?R, ?Rw) (shift s i) (shift t i) (shift \<sigma> i)" by simp
  from nearly have "(the (fst edp), dpp_ops.intersect_pairs I d (snd edp)) \<in> set dpps"
    unfolding dpps by auto
  from rec[OF this]
    have contra: "finite_dpp (?nfs,?m,?P \<inter> set (snd edp), ?Pw \<inter> set (snd (edp)), ?Q, ?R, ?Rw)" 
    using  dpp_spec.intersect_pairs_sound[OF I, of d "snd edp"]
    unfolding sound by auto
  from ichain_shift_merge[OF ic mc]
    have "min_ichain (?nfs,?m,?P \<inter> set (snd edp), ?Pw \<inter> set (snd (edp)), ?Q, ?R, ?Rw)
                     (shift s i) (shift t i) (shift \<sigma> i)" .
  with contra show False unfolding finite_dpp_def by blast
qed

definition
  ac_dep_graph_proc ::
    "('dpp, 'f::{showl, compare_order}, string) ac_dpp_ops \<Rightarrow> 'dpp
    \<Rightarrow> ('a option \<times> ('f, string) rules) list \<Rightarrow> ('a \<times> 'dpp) list result"
where
  "ac_dep_graph_proc I d dps \<equiv> check_return
    (check_ac_dep_graph_proc I d dps)
    (map (\<lambda>aP. (the (fst aP), ac_dpp_ops.intersect_pairs I d (snd aP)))
         (filter (\<lambda> aP. fst aP \<noteq> None) dps))"

lemma ac_dep_graph_proc :
  assumes I: "ac_dpp_spec I"
    and proc: "ac_dep_graph_proc I d dps = return dpps"
    and rec: "\<And>a d'. (a, d') \<in> set dpps \<Longrightarrow> finite_rel_dpp (ac_dpp_ops.ac_dpp I d')"
  shows "finite_rel_dpp (ac_dpp_ops.ac_dpp I d)"
proof
  fix s t \<sigma>
  let ?P = "set (ac_dpp_ops.P I d)"
  let ?Pw = "set (ac_dpp_ops.Pw I d)"
  let ?R = "set (ac_dpp_ops.R I d)"
  let ?Rw = "set (ac_dpp_ops.Rw I d)"
  let ?E = "set (ac_dpp_ops.E I d)"
  let ?Dpp = "(?P, ?Pw, ?R, ?Rw, ?E)"
  let ?DPP = "ac_dpp_ops.ac_dpp I d"
  note sound = ac_dpp_spec.ac_dpp_spec_sound[OF I]
  assume michain: "min_relchain ?DPP s t \<sigma>"
  then have mc: "min_relchain ?Dpp s t \<sigma>" unfolding sound .
  from proc[unfolded ac_dep_graph_proc_def]
    have check: "isOK (check_ac_dep_graph_proc I d dps)"
    and dpps: "dpps = map (\<lambda>aP. (the (fst aP), ac_dpp_ops.intersect_pairs I d (snd aP)))
                          (filter (\<lambda>aP. fst aP \<noteq> None) dps)"
    by auto
  from check_ac_dep_graph_proc_sound[OF I check michain]
  obtain edp i where nearly: "edp \<in> set dps" "fst edp \<noteq> None"
    and ic: "min_relchain (set (snd edp), {}, ?R, ?Rw, ?E) (shift s i) (shift t i) (shift \<sigma> i)"
    by auto
  from nearly have "(the (fst edp), ac_dpp_ops.intersect_pairs I d (snd edp)) \<in> set dpps"
    unfolding dpps by auto
  from rec[OF this]
    have contra: "finite_rel_dpp (?P \<inter> set (snd edp), ?Pw \<inter> set (snd (edp)), ?R, ?Rw, ?E)" 
    using ac_dpp_spec.intersect_pairs_sound[OF I, of d "snd edp"]
    unfolding sound by auto
  from ic mc
  have "min_relchain (?P \<inter> set (snd edp), ?Pw \<inter> set (snd (edp)), ?R, ?Rw, ?E)
                     (shift s i) (shift t i) (shift \<sigma> i)" 
    unfolding min_relchain.simps 
    unfolding Infm_double_shift[of "\<lambda> s t. (s,t) \<in> P" s i t for P, symmetric]
    unfolding Infm_triple_shift[of "\<lambda> s \<sigma> t \<tau>. (t \<cdot> \<tau>, s \<cdot> \<sigma>) \<in> P" s i \<sigma> t for P, symmetric]
    by auto
  with contra show False unfolding finite_rel_dpp_def by blast
qed
end
