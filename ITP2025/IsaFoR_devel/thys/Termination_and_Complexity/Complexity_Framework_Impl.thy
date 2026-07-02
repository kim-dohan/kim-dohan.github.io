(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Complexity_Framework_Impl
imports 
  Complexity_Framework
  Framework.QDP_Framework_Impl
  First_Order_Rewriting.Trs_Impl
begin

fun is_Fsharp_term :: "'f sig \<Rightarrow> 'f sig \<Rightarrow> ('f,'v)term \<Rightarrow> bool" where
  "is_Fsharp_term _ _ (Var _) = False"
| "is_Fsharp_term FS F (Fun f ts) = ( (f,length ts) \<in> FS \<and> set (concat (map funas_term_list ts)) \<subseteq> F)"

lemma is_Fsharp_term[simp]: "is_Fsharp_term FS F t = (t \<in> Fsharp_terms FS F)"
  by (cases t, auto simp: Fsharp_terms.simps)

definition split_DP :: "'f sig \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('f, 'v) mctxt \<times> ('f, 'v) term list"
where
  "split_DP FS = (\<lambda>r. split_term (\<lambda>t. is_Fun t \<and> the (root t) \<in> FS) (snd r))"

primrec
  check_DP_complexity ::
    "('f :: showl, 'v :: showl) rules \<Rightarrow> ('f, 'v) complexity_measure \<Rightarrow>
    showsl + ('f, 'v) rules \<times> ('f, 'v) rules \<times> ('f \<times> nat) list \<times> ('f \<times> nat) list \<times> ('f \<times> nat) list"
where
  "check_DP_complexity P (Derivational_Complexity _) = error (showsl_lit (STR ''require runtime complexity''))" |
  "check_DP_complexity P (Runtime_Complexity C FS) = do {
    let FS' = set FS;
    let (RS, R) = partition (\<lambda> lr. the (root (fst lr)) \<in> FS') P;
    let Cs_ts = map (split_DP FS') RS;
    let Cp = remdups (concat (map (funas_mctxt_list o fst) Cs_ts));
    let Cp' = set Cp;
    let F = remdups (C @ funas_trs_list R @
      concat [funas_term_list s. (fs, _) \<leftarrow> RS, s \<leftarrow> args fs] @
      concat [funas_term_list s. (_, ts) \<leftarrow> Cs_ts, t \<leftarrow> ts, s \<leftarrow> args t]);
    let F' = set F;
    check (F' \<inter> FS' = {} \<and> F' \<inter> Cp' = {} \<and> FS' \<inter> Cp' = {}) (showsl_lit (STR ''symbols are not disjoint''));
    check (\<forall> lr \<in> set RS. is_Fsharp_term FS' F' (fst lr)) (showsl_lit (STR ''lhss of RS are not sharp terms''));
    return (RS, R, Cp, FS, F)
  }"

lemma check_DP_complexity:
  assumes check: "check_DP_complexity P cm = return (RS, R, Cp, FS, F)"
    and wf: "wf_trs (set P)"
  shows "set P = set RS \<union> set R \<and> is_DP_complexity (set Cp) (set FS) (set F) (set RS) (set R) cm"
proof -
  from check obtain C FS' where cm: "cm = Runtime_Complexity C FS'" by (cases cm, auto)
  let ?FS = "set FS'"
  note check = check[unfolded cm check_DP_complexity.simps]
  obtain RS' R' where part: "partition (\<lambda>lr. the (root (fst lr)) \<in> ?FS) P = (RS',R')" by force
  let ?Cs_ts = "map (split_DP ?FS) RS'"
  define F' where "F' = remdups (C @ funas_trs_list R' @
    concat [funas_term_list s. (fs, _) \<leftarrow> RS', s \<leftarrow> args fs] @
    concat [funas_term_list s. (_, ts) \<leftarrow> ?Cs_ts, t \<leftarrow> ts, s \<leftarrow> args t])"
  define Cp' where "Cp' = remdups (concat (map (funas_mctxt_list \<circ> fst) ?Cs_ts))"
  let ?RS = "set RS'"
  let ?R = "set R'"
  let ?Cp = "set Cp'"
  let ?F = "set F'"
  let ?FST = "Fsharp_terms ?FS ?F"
  note check = check[unfolded Let_def part split F'_def[symmetric] Cp'_def[symmetric], simplified]
  from check have id: "RS = RS'" "R = R'" "FS = FS'" "Cp = Cp'" "F = F'" by auto
  from part have p: "set P = ?RS \<union> ?R" by auto
  with wf have wf: "wf_trs ?RS" "wf_trs ?R" unfolding wf_trs_def by auto
  from F'_def have RF: "funas_trs ?R \<subseteq> ?F" by auto
  from check have disj: "?FS \<inter> ?Cp = {}" "?FS \<inter> ?F = {}" "?Cp \<inter> ?F = {}" by auto
  from check have lhss: "lhss ?RS \<subseteq> ?FST" by auto
  show ?thesis unfolding id
  proof (rule conjI[OF p], rule is_DP_complexity[OF wf RF lhss _ disj])
    fix l r
    assume lr: "(l, r) \<in> ?RS"
    let ?test = "(\<lambda>t. is_Fun t \<and> the (root t) \<in> ?FS)"
    obtain C ts where split_lr: "split_DP ?FS (l, r) = (C, ts)" by force
    note split = this [unfolded split_DP_def, simplified]
    from split split_term_eqf [of r ?test] have eq: "r =\<^sub>f (C, ts)" by simp
    from uncap_till [of ?test r]
      have ts: "\<And>t. t \<in> set ts \<Longrightarrow> is_Fun t \<and> the (root t) \<in> ?FS" using split by auto
    have "?Cp = (\<Union>lr\<in>set RS'. funas_mctxt (fst (split_DP (set FS') lr)))" unfolding Cp'_def by simp
    with lr split_lr have C: "funas_mctxt C \<subseteq> ?Cp" by auto
    show "\<exists>C ts. r =\<^sub>f (C, ts) \<and> funas_mctxt C \<subseteq> ?Cp \<and> set ts \<subseteq> ?FST"
    proof (intro exI conjI, rule eq, rule C, rule)
      fix t
      assume t: "t \<in> set ts"
      from ts [OF t] obtain f ss where tf: "t = Fun f ss" and f: "(f, length ss) \<in> ?FS" by auto
      show "t \<in> ?FST" unfolding tf
      proof (rule Fsharp_term[OF f])
        fix s 
        assume "s \<in> set ss"
        with tf have "s \<in> set (args t)" by auto
        with lr split_lr t
        show "funas_term s \<subseteq> ?F" unfolding F'_def by force
      qed
    qed
  qed (simp add: cm F'_def)
qed

definition split_proc_complexity ::
    "('tp, 'f:: showl, 'v:: showl) tp_ops \<Rightarrow> ('f,'v)rules \<Rightarrow>
    'tp \<Rightarrow> ('tp \<times> 'tp)result"
 where "split_proc_complexity I S1 cp \<equiv> do {
    let S = tp_ops.R I cp;
    let W = tp_ops.Rw I cp;
    let nfs = tp_ops.nfs I cp;
    let Q = tp_ops.Q I cp;
    check_subseteq S1 S <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is not a strict rule'')); 
    let S2 = list_diff S S1;
    return (tp_ops.mk I nfs Q S1 (S2 @ W), tp_ops.mk I nfs Q S2 (S1 @ W))
  }
    <+? (\<lambda> e. showsl_lit (STR ''error when splitting complexity problem\<newline>'') \<circ> e)"

lemma split_proc_complexity: assumes "tp_spec I"
  and res: "split_proc_complexity I S1 tp = return (tp1,tp2)"
  and cpx1: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp1)) cm cc"
  and cpx2: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp2)) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  interpret tp_spec I by fact
  obtain nfs q s w where tp: "qreltrs tp = (nfs,q,s,w)" by cases auto  
  then have id [simp]: "NFS tp = nfs" "set (Q tp) = q" "set (R tp) = s" "set (Rw tp) = w" by auto
  define S2 where "S2 = list_diff (R tp) S1" 
  note res = res[unfolded split_proc_complexity_def Let_def, simplified, folded S2_def]
  from res have s: "s = set S1 \<union> set S2" using S2_def by auto
  from res have tp1: "qreltrs tp1 = (nfs,q,set S1, w \<union> set S2)" by auto
  from res have tp2: "qreltrs tp2 = (nfs,q,set S2, w \<union> set S1)" by auto
  show ?thesis using cpx1 cpx2 unfolding tp tp1 tp2 split s qrstep_union
    by (rule deriv_bound_relto_measure_class_union)
qed
end

