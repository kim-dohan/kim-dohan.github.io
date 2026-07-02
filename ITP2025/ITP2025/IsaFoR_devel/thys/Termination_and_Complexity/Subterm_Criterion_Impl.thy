(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Subterm_Criterion_Impl
imports
  Subterm_Criterion
  Framework.QDP_Framework_Impl
  Auxx.Map_Choice
  TRS.Q_Restricted_Rewriting_Impl
begin

definition
  check_strict_rstep ::
    "('f:: showl, 'v:: showl) rules \<Rightarrow>
     (('f, 'v) rule \<Rightarrow> ('f, 'v) rseq option) \<Rightarrow>
     'f proj \<Rightarrow> ('f, 'v) rule \<Rightarrow> showsl check"
where
  "check_strict_rstep R rseqm p r = (
     let s = proj_term p (fst r); t = proj_term p (snd r) in
     case rseqm r of
       None \<Rightarrow> check_supt s t
     | Some rseq \<Rightarrow> (if length rseq = 0
       then check_supt s t
       else (        
           check_rsteps_last R s rseq
         >> check_supteq (rseq_last s rseq) t)))"

definition
  check_strict_one_rstep ::
    "('f:: showl, 'v:: showl) rules \<Rightarrow>
     (('f, 'v) rule \<Rightarrow> ('f, 'v) rseq option) \<Rightarrow>
     'f proj \<Rightarrow> ('f, 'v) rule \<Rightarrow> showsl check"
where
  "check_strict_one_rstep R rseqm p r = (
    let s = proj_term p (fst r); t = proj_term p (snd r) in
    case rseqm r of
      None \<Rightarrow> check_supt s t
    | Some [(pos, rule, u)] \<Rightarrow> (
        check_qrstep (\<lambda> _. True) False R pos rule s u
      >> check_supteq u t)
    | Some _ \<Rightarrow> error (showsl_lit (STR ''more than a single rewrite step is not allowed'')))"

lemma check_strict_rstep_sound:
  assumes "isOK (check_strict_rstep R rseqm p r)"
  shows "(proj_term p (fst r), proj_term p (snd r)) \<in> ({\<rhd>} \<union> rstep (set R))^+"
    (is "(?s, ?t) \<in> ({\<rhd>} \<union> rstep (set R))^+")
proof (cases "rseqm r")
  case None
  from assms[unfolded check_strict_rstep_def None]
    have "isOK (check_supt ?s ?t)" by simp
  then have "(?s, ?t) \<in> {\<rhd>}" by simp
  then show ?thesis by auto
next
  case (Some rseq)
  show ?thesis
  proof (cases "length rseq = 0")
    case True
    with assms[unfolded check_strict_rstep_def Some]
      have "isOK (check_supt ?s ?t)" by simp
    then have "(?s, ?t) \<in> {\<rhd>}" by simp
    then show ?thesis by auto
  next
    let ?u = "rseq_last ?s rseq"
    case False
    with assms[unfolded check_strict_rstep_def Some]
      have "isOK (check_rsteps_last R ?s rseq >> check_supteq ?u ?t)" unfolding Let_def by simp
    then have "(?s, ?u) \<in> (rstep (set R))^^(length rseq)" and "(?u, ?t) \<in> {\<unrhd>}" 
      using check_rsteps_last_sound_length[of R ?s rseq] by auto
    with False obtain n where "(?s, ?u) \<in> (rstep (set R))^^(Suc n)" by (induct rseq) simp_all
    then have "(?s, ?u) \<in> (rstep (set R))^+" using trancl_power[of _ "rstep (set R)"] by blast
    from \<open>(?u, ?t) \<in> {\<unrhd>}\<close> show ?thesis unfolding supteq_supt_conv
    proof
      assume "?u = ?t"
      from \<open>(?s, ?u) \<in> (rstep (set R))^+\<close>
        show ?thesis unfolding \<open>?u = ?t\<close> using trancl_union_right[of "rstep (set R)" "{\<rhd>}"] by blast
    next
      assume "(?u, ?t) \<in> {\<rhd>}"
      then have "(?u, ?t) \<in> ({\<rhd>} \<union> rstep (set R))^+" by auto
      moreover from \<open>(?s, ?u) \<in> (rstep (set R))^+\<close>
        have "(?s, ?u) \<in> ({\<rhd>} \<union> rstep (set R))^+" using trancl_union_right by blast
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma check_strict_one_rstep_sound:
  assumes ok: "isOK (check_strict_one_rstep R rseqm p r)"
  shows "(proj_term p (fst r), proj_term p (snd r)) \<in> ({\<rhd>} \<union> rstep (set R) O {\<unrhd>})"
    (is "(?s, ?t) \<in> ({\<rhd>} \<union> ?S)")
proof (cases "rseqm r")
  case None
  from ok[unfolded check_strict_one_rstep_def None]
    show ?thesis by auto
next
  case (Some prus)
  show ?thesis
  proof (cases prus)
    case Nil
    from ok[unfolded check_strict_one_rstep_def Some Nil]
      show ?thesis by simp
  next
    case (Cons pru prus')
    note Cons' = this
    show ?thesis
    proof (cases prus')
      case (Cons pru' prus'')
      from ok[unfolded check_strict_one_rstep_def Some Cons' Cons]
        show ?thesis by simp
    next
      case Nil
      with Cons obtain p r u where pru: "pru = (p, r, u)" by (cases pru) auto
      with Nil and Cons have prus: "prus = [(p, r, u)]" by simp
      from ok[unfolded check_strict_one_rstep_def Some Cons Nil, simplified]
        have okstep: "isOK (check_qrstep (\<lambda> _. True) False R p r ?s u)"
        and supteq: "isOK (check_supteq u ?t)" unfolding pru by auto
      from check_qrstep_qrstep[OF _ okstep, of Nil]
        and supteq[unfolded isOK_check_supteq]
        show ?thesis by auto
    qed
  qed
qed

definition
  check_weak :: "'f proj \<Rightarrow> ('f:: showl, 'v:: showl) rule \<Rightarrow> showsl check"
where
  "check_weak p r \<equiv> check (proj_term p (fst r) = proj_term p (snd r))
     (showsl_lit (STR ''the projected lhs is not equal to the projected rhs\<newline>''))
   <+? (\<lambda>s. showsl_lit (STR ''Could not orient rule '') \<circ> showsl_rule r \<circ> showsl_lit (STR '', since\<newline>'') \<circ>
          showsl (proj_term p (fst r)) \<circ> showsl_lit (STR '' != '') \<circ> showsl (proj_term p (snd r)) \<circ>
          showsl_nl \<circ> s)"

lemma check_weak_sound[simp]:
  assumes "isOK (check_weak p r)"
  shows "proj_term p (fst r) = proj_term p (snd r)"
  using assms unfolding check_weak_def by auto

datatype ('f) projL = Projection "(('f \<times> nat) \<times> nat) list"

fun
  create_proj :: "('f :: compare_order) projL \<Rightarrow> 'f proj"
where
  "create_proj (Projection p) = (let I = ceta_map_of p in (\<lambda> f. case I f of None \<Rightarrow> 0 | Some n \<Rightarrow> n))"

fun
  create_rseq_map :: "(('f :: compare_order, 'v :: compare_order) rule \<times> ('f, 'v) rseq) list \<Rightarrow> (('f, 'v) rule \<Rightarrow> ('f, 'v) rseq option)"
where
  "create_rseq_map rseqs = ceta_map_of rseqs"

definition
  subterm_criterion_proc ::
    "('dpp, 'f::{compare_order,showl}, 'v::{compare_order,showl}) dpp_ops \<Rightarrow>
    'f projL \<Rightarrow> (('f, 'v) rule \<times> ('f, 'v) rseq)list \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> 'dpp proc"
where
  "subterm_criterion_proc I pL rseqmL Prm dpp = check_return (do {
    let p       = create_proj pL;
    let rseqm   = create_rseq_map rseqmL;
    let P       = dpp_ops.pairs I dpp;
    let nfs     = dpp_ops.nfs I dpp;
    let R       = dpp_ops.rules I dpp;
    let P'      = snd (dpp_ops.split_pairs I dpp Prm);
    let wfR     = wf_rules_impl R;
    check_allm (\<lambda>(l, r). do {
      check_no_var l;
      check_no_var r;
      check_no_defined_root (dpp_spec.is_defined I dpp) r
    }) P;
    check (dpp_ops.minimal I dpp \<or> dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''minimality or innermost required''));
    check_allm (\<lambda>(l, r). check_no_var l) R;
    (if dpp_ops.Q_empty I dpp
      then check_allm (check_strict_rstep R rseqm p) Prm
      else check_allm (check_strict_one_rstep wfR rseqm p) Prm);
    check_allm (check_weak p) P'
  }) (dpp_spec.delete_pairs I dpp Prm)"

lemma subterm_criterion_proc: assumes "dpp_spec I"
  shows "dpp_spec.sound_proc_impl I (subterm_criterion_proc I p rseqm ps)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof
    fix d d'
    assume ok: "subterm_criterion_proc I p rseqm ps d = return d'"
      and fin: "finite_dpp (dpp_ops.dpp I d')"
    let ?S  = "set ps"
    let ?P  = "set (dpp_ops.P I d)"
    let ?Pw = "set (dpp_ops.Pw I d)"
    let ?P' = "?P \<union> ?Pw"
    let ?Q  = "set (dpp_ops.Q I d)"
    let ?R  = "set (dpp_ops.R I d)"
    let ?Rw = "set (dpp_ops.Rw I d)"
    let ?nfs = "dpp_ops.nfs I d"
    let ?m  = "dpp_ops.minimal I d"
    let ?R' = "?R \<union> ?Rw"
    let ?wfR = "wf_rules (?R')"
    let ?\<pi>  = "proj_term (create_proj p)"
    let ?rseqm = "create_rseq_map rseqm"
    show "finite_dpp (dpp_ops.dpp I d)"
    proof (cases "dpp_ops.split_pairs I d ps")
      case (Pair D P')
      from split_pairs_sound[OF Pair]
        have D: "set D = (?P \<union> ?Pw) \<inter> ?S"
        and P': "set P' = (?P \<union> ?Pw) - ?S" by auto
      let ?D = "set D"
      note ok = ok[unfolded subterm_criterion_proc_def, simplified, simplified Pair, unfolded Let_def, simplified]
      from ok
        have cond: "\<forall>(l, r)\<in>?P'.
          is_Fun l \<and> is_Fun r \<and> \<not> defined ?R' (the (root r))" by simp
      from ok have nvar: "\<forall>(l, r)\<in>?R'. is_Fun l" by simp
      from ok
        have weak: "\<forall>(l, r)\<in>set P'. ?\<pi> l = ?\<pi> r"
        by (simp_all add: split_def Let_def Pair)
      from ok
        have strict: "?Q = {} \<and> (\<forall>(l, r)\<in>?S. (?\<pi> l, ?\<pi> r) \<in> ({\<rhd>} \<union> rstep ?R')^+) \<or>
                                (\<forall>(l, r)\<in>?S. (?\<pi> l, ?\<pi> r) \<in> {\<rhd>} \<union> rstep ?wfR O {\<unrhd>})"
        using check_strict_rstep_sound[of "dpp_ops.rules I d" ?rseqm "create_proj p"]
        using check_strict_one_rstep_sound[of "wf_rules_impl (dpp_ops.rules I d)" ?rseqm "create_proj p"] 
        by (cases "?Q = {}", simp_all add: split_def Pair D P')
      from ok have m: "?m \<or> NF_terms ?Q \<subseteq> NF_trs ?R'" by simp
      from ok have d': "d' = dpp_spec.delete_pairs I d ps" by simp
      have proc: "Subterm_Criterion.subterm_criterion_proc (create_proj p) ?S
        (?nfs,?m,?P, ?Pw, ?Q, ?R, ?Rw) (?nfs,?m,?P - ?S, ?Pw - ?S, ?Q, ?R, ?Rw)"
        by (simp add: subterm_criterion_cond_def cond P' weak, insert strict m nvar, auto) 
      note fin = fin[unfolded d' delete_P_Pw_sound]
      show ?thesis unfolding dpp_spec_sound d'
        by (rule subset_proc[OF fin proc subset_subterm_criterion_proc])
    qed
  qed
qed

end

