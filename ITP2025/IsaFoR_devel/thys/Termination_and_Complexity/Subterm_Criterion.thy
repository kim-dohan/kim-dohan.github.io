(*
Author:  Alexander Krauss <krauss@in.tum.de> (2009)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Subterm_Criterion
imports 
  TRS.QDP_Framework
begin

subsection \<open>Projections\<close>

text \<open>
A projection @{text "proj_term p t"} maps a term with root symbol @{term "f"}
to its @{term "p f"}-th argument or does not change the term at all (if
@{term "p f"} is not an argument position of @{term "f"}. Variables are not changed.
\<close>
type_synonym 'f proj = "('f \<times> nat) \<Rightarrow> nat"

fun proj_term :: "'f proj \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "proj_term p (Var x) = Var x"
| "proj_term p (Fun f ts) = (let n = length ts; i = p (f,n) in if i < n
     then ts ! i
     else Fun f ts)"

lemma proj_term_subst_distr[simp]:
  "proj_term \<pi> (Fun f ss) \<cdot> \<sigma> = proj_term \<pi> (Fun f ss \<cdot> \<sigma>)"
  by (auto simp: Let_def)

lemma supteq_proj_term: "t \<unrhd> proj_term p t"
  by (cases t) (auto simp: Let_def)

lemma proj_term_subst_apply_term_distrib[simp]:
  assumes "is_Fun t"
  shows "proj_term p t \<cdot> \<sigma> = proj_term p (t \<cdot> \<sigma>)"
  using assms by (cases t) (simp_all add: Let_def)

lemma qrstep_proj_term:
  fixes p :: "'f proj"
  defines pi_def[simp]: "\<pi> t \<equiv> proj_term p t"
  assumes "\<not> defined R (the (root s))"
    and nvar: "\<forall> (l,r) \<in> R. is_Fun l"
    and "(s, t) \<in> qrstep nfs Q R"
  shows "(\<pi> s, \<pi> t) \<in> (qrstep nfs Q R)^="
proof -
  from nvar_qrstep_Fun[OF nvar \<open>(s, t) \<in> qrstep nfs Q R\<close>]
    obtain f ss where s: "s = Fun f ss" by best
  from \<open>(s, t) \<in> qrstep nfs Q R\<close> have "(Fun f ss, t) \<in> qrstep nfs Q R" by (simp add: s)
  from this[unfolded qrstep_iff_rqrstep_or_nrqrstep] show ?thesis
  proof
    assume "(Fun f ss, t) \<in> rqrstep nfs Q R"
    then obtain l r \<sigma> where "(l, r) \<in> R" and Fun: "Fun f ss = l \<cdot> \<sigma>" ..
    with nvar 
      obtain ls where l: "l = Fun f ls" by force
    from \<open>(l, r) \<in> R\<close> have "defined R (f, num_args s)" by (auto simp: defined_def s Fun l)
    with assms show ?thesis by (auto simp: s)
  next
    assume step: "(Fun f ss, t) \<in> nrqrstep nfs Q R"
    from nrqrstep_preserves_root[OF step] obtain ts where t: "t = Fun f ts"
      by (cases t, auto)
    from nrqrstep_imp_arg_qrsteps[OF step] and nrqrstep_num_args[OF step]
      have args: "\<forall>i. (ss ! i, args t ! i) \<in> (qrstep nfs Q R)^="
      and num_args: "num_args (Fun f ss) = num_args t" unfolding t  by auto
    with t have len: "length ts = length ss" by simp
    let ?i = "p (f,length ss)"
    show ?thesis
    proof (cases "?i < length ss")
      case True
      from args have "(ss ! ?i, args t ! ?i) \<in> (qrstep nfs Q R)^=" by simp
      then show ?thesis using len unfolding s t pi_def num_args[symmetric]
        unfolding proj_term.simps Let_def unfolding len unfolding if_P[OF True] by simp          
    next
      case False
      from \<open>(s, t) \<in> qrstep nfs Q R\<close>
        show ?thesis unfolding s t pi_def proj_term.simps Let_def len if_not_P[OF False]
        by simp
    qed
  qed
qed

lemma qrsteps_proj_term:
  assumes steps: "(s, t) \<in> (qrstep nfs Q R)^*" and ndef: "\<not> defined R (the (root s))"
    and nvar: "\<forall> (l,r) \<in> R. is_Fun l"
  shows "(proj_term p s, proj_term p t) \<in> (qrstep nfs Q R)^*"
using steps ndef
proof (induct)
  case base show ?case by simp
next
  case (step u v)
  then have seq: "(proj_term p s, proj_term p u) \<in> (qrstep nfs Q R)^*" by simp
  note steps = qrsteps_imp_nrqrsteps[OF nvar ndef_applicable_rules[OF ndef] step(1)]
  from ndef[unfolded nrqrsteps_preserve_root[OF steps] nrqrsteps_num_args[OF steps]]
  have ndef: "\<not> defined R (the (root u))" .
  from qrstep_proj_term[OF ndef nvar]
    and \<open>(u, v) \<in> qrstep nfs Q R\<close>
    have "(proj_term p u, proj_term p v) \<in> qrstep nfs Q R \<union> Id" by simp
  with \<open>(proj_term p s, proj_term p u) \<in> (qrstep nfs Q R)^*\<close>
    show "(proj_term p s, proj_term p v) \<in> (qrstep nfs Q R)^*" by auto
qed

text \<open>
Lhss and rhss of @{text "P"} are nonvariable terms with roots that are
not defined in @{text "R"}. The projections of the removed pairs need
to be in the relation @{term "({\<rhd>} \<union> rstep R)^+"}. The projections of
all other pairs need to be equal. This extended version of the subterm
criterion (where now also identity projections and rewrite steps are
possible) is due to the A3PAT team (TODO: add reference). However,
extending our existing proof, was straight-forward, since internally we
already used exactly this relation, but just did not realize that we could
lift it to the main result.

Extension: For @{text Q}-restricted rewriting, at most a single rewrite-step
is allowed between the projections of the removed pairs. 
Moreover, for innermost rewriting, no minimality is required.

Comment: if Q \<noteq> {} and NF Q \<subseteq> NF R (usual innermost or more restrictive case) then the restriction
  do single rewrite steps is not a real restriction: in fact, not a single rewrite-step can be performed,
  because if \<pi>(s) \<unrhd> \<cdot> -Q\<rightarrow>_R t, then s is not in NF R and thus not in NF Q. Hence, then this DP can immediately
  dropped by other criteria like the dependency graph.

if however Q \<noteq> {} and \<not> NF Q \<subseteq> NF R, then the condition is required for soundness:
Consider P = {F(f(x)) \<rightarrow> F(g(x))}, R = {f(x) \<rightarrow> h(i(x)), h(i(x)) \<rightarrow> g(x), g(x) \<rightarrow> f(x)} and Q = {i(a)}.
We get an infinite minimal chain F(f(a)) -P\<rightarrow> F(g(a)) -R\<rightarrow> F(f(a)) -P\<rightarrow> ...
However, the criterion which allows more than one step would allow do delete the pair as
F(f(x)) -R\<rightarrow> F(h(i(x))) -R\<rightarrow> F(g(x))
\<close>
definition
  subterm_criterion_cond ::
    "'f proj \<Rightarrow> bool \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "subterm_criterion_cond p nfs P Q R D \<equiv>
     (\<forall>(l, r)\<in>P. is_Fun l \<and> is_Fun r \<and> \<not> defined R (the (root r))) \<and>
     (\<forall>(l, r)\<in>P - D. proj_term p l = proj_term p r) \<and>
     (\<forall>(l, r)\<in>R. is_Fun l) \<and>
     ((Q = {} \<and> (\<forall>(l, r)\<in>D. (proj_term p l, proj_term p r) \<in> ({\<rhd>} \<union> rstep R)^+)) \<or>
                (\<forall>(l, r)\<in>D. (proj_term p l, proj_term p r) \<in> ({\<rhd>} \<union> rstep (wf_rules R) O {\<unrhd>})))"

fun
  subterm_criterion_proc ::
    "'f proj \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) dpp \<Rightarrow> ('f, 'v) dpp \<Rightarrow> bool"
where
  "subterm_criterion_proc p D (nfs,m,P, Pw, Q, R, Rw) (nfs',m',P', Pw', Q', R', Rw') = (
    subterm_criterion_cond p nfs (P \<union> Pw) Q (R \<union> Rw) D \<and>
    Q' = Q \<and> R' = R \<and> Rw' = Rw \<and> P' = P - D \<and> Pw' = Pw - D \<and> nfs' = nfs \<and> (m' \<longrightarrow> m) \<and> (m \<or> NF_terms Q \<subseteq> NF_trs (R \<union> Rw)))"

fun shift_by :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "shift_by f 0 = 0"
| "shift_by f (Suc i) = Suc (f (shift_by f i))"

theorem subset_subterm_criterion_proc:
  "subset_proc (subterm_criterion_proc p D)"
unfolding subset_proc_def
proof (intro impI allI)
  fix P Pw Q R Rw P' Pw' Q' R' Rw' nfs nfs' m m'
  assume proc: "subterm_criterion_proc p D (nfs, m, P, Pw, Q, R, Rw) (nfs', m', P', Pw', Q', R', Rw')"
  let ?\<pi> = "proj_term p"
  let ?R = "R \<union> Rw"
  let ?R' = "R' \<union> Rw'"
  let ?wfR = "wf_rules ?R"
  let ?P = "P \<union> Pw"
  let ?P' = "P' \<union> Pw'"
  let ?S = "({\<rhd>} \<union> qrstep nfs Q ?R)"
  let ?S' = "({\<rhd>} \<union> rstep (wf_rules ?R) O {\<unrhd>})"
  have wwf: "wwf_qtrs Q ?wfR" by (rule wwf_qtrs_wf_rules)
  have "qrstep False Q ?wfR \<subseteq> qrstep nfs Q ?wfR" using wwf_qtrs_imp_nfs_switch[OF wwf] by blast
  also have "\<dots> \<subseteq> qrstep nfs Q ?R" by (rule qrstep_mono, auto simp: wf_rules_def)
  finally have wf_to_R: "\<And> st. st \<in> qrstep False Q ?wfR \<Longrightarrow> st \<in> qrstep nfs Q ?R" by blast
  from proc have eqs: "Q' = Q" "R' = R " "Rw' = Rw" "P' = P - D" "Pw' = Pw - D" "nfs' = nfs"
    and "?R' \<subseteq> ?R" 
    and m_or_inn: "m \<or> NF_terms Q \<subseteq> NF_trs ?R" 
    and "m' \<Longrightarrow> m"
    unfolding subterm_criterion_proc.simps by auto
  from proc[unfolded subterm_criterion_proc.simps subterm_criterion_cond_def, THEN conjunct1]
    have cond: "\<forall>(l, r)\<in>?P. is_Fun l \<and> is_Fun r \<and> \<not> defined ?R (the (root r))"
    and nvar: "\<forall>(l, r)\<in>?R. is_Fun l"
    and weak: "\<forall>(l, r)\<in>?P - D. ?\<pi> l = ?\<pi> r"
    and strict: "(Q = {} \<and> (\<forall>(l, r)\<in>D. (?\<pi> l, ?\<pi> r) \<in> ?S^+))
      \<or> (\<forall>(l, r)\<in>D. (?\<pi> l, ?\<pi> r) \<in> ?S')"
    by auto
  show "?R' \<subseteq> ?R \<and> Q' = Q \<and> nfs' = nfs \<and> (m' \<longrightarrow> m) \<and> (\<forall>s t \<sigma>.
    min_ichain (nfs, m, P, Pw, Q, R, Rw) s t \<sigma> \<longrightarrow>
    (\<exists>i. ichain (nfs, m', P', Pw', Q', R', Rw') (shift s i) (shift t i) (shift \<sigma> i)))"
  proof (intro conjI allI impI)
    show "?R' \<subseteq> ?R" by fact
    show "Q' = Q" unfolding eqs ..
    show "nfs' = nfs" unfolding eqs ..
    assume m' then show m by fact 
  next
    fix s t \<sigma> assume mchain: "min_ichain (nfs,m,P, Pw, Q, R, Rw) s t \<sigma>"
    have "\<exists>i. min_ichain (nfs,m,P - D, Pw - D, Q, R, Rw) (shift s i) (shift t i) (shift \<sigma> i)"
    proof (intro min_ichain_split_P[OF mchain] notI)
      assume mchain': "min_ichain (nfs,m,D \<inter> ?P, ?P - D, Q, {}, ?R) s t \<sigma>"
      then have "\<forall>i. \<exists>j\<ge>i. (s j, t j) \<in> D" by (auto simp: ichain.simps INFM_nat_le)
      from choice[OF this] obtain f :: "nat \<Rightarrow> nat"
        where mono: "\<forall>i. f i \<ge> i"
        and D_seq: "\<forall>i. (s (f i), t (f i)) \<in> D" by auto
      from cond and mchain
        have s_no_vars: "\<And> i. is_Fun (s i)"
        and  t_no_vars: "\<And> i. is_Fun (t i)"
        and  t_undef: "\<And> i. \<not> defined ?R (the (root (t i)))"
        by (auto simp: ichain.simps)
      have ts_undef: "\<And> i. \<not> defined ?R (the (root (t i \<cdot> \<sigma> i)))"
      proof -
        fix i
        from t_no_vars[of i] and t_undef[of i]
          show "\<not> defined ?R (the (root (t i \<cdot> \<sigma> i)))" by auto
      qed
      let ?s = "\<lambda>i. ?\<pi> (s i \<cdot> \<sigma> i)"
      let ?t = "\<lambda>i. ?\<pi> (t i \<cdot> \<sigma> i)"
      {
        fix i
        from mchain' have "(s i, t i) \<in> D \<inter> ?P \<union> (?P - D)" by (auto simp: ichain.simps)
        then have "(s i, t i) \<in> D \<union> ?P'" unfolding eqs by blast
        then have "(?s i, ?t i) \<in> ?S^*"
        proof
          assume in_D: "(s i, t i) \<in> D"
          from strict
          show ?thesis
          proof (elim disjE conjE)
            assume Q: "Q = {}" and "(\<forall>(l, r)\<in>D. (?\<pi> l, ?\<pi> r) \<in> ({\<rhd>} \<union> qrstep nfs Q ?R)^+)"
            with in_D have 1: "(?\<pi> (s i), ?\<pi> (t i)) \<in> ?S^+" by auto
            from supt_rstep_trancl_stable[OF 1[unfolded Q qrstep_rstep_conv], of "\<sigma> i"]
              have "(?s i, ?t i) \<in> ?S^+"
              using s_no_vars[of i] and t_no_vars[of i]
              by (simp add: Q)
            then show ?thesis by simp
          next
            assume "\<forall>(l, r)\<in>D. (?\<pi> l, ?\<pi> r) \<in> {\<rhd>} \<union> rstep ?wfR O {\<unrhd>}"
            with in_D have "(?\<pi> (s i), ?\<pi> (t i)) \<in> {\<rhd>} \<union> rstep ?wfR O {\<unrhd>}" by blast
            then show ?thesis
            proof
              assume "?\<pi> (s i) \<rhd> ?\<pi> (t i)"
              from supt_subst[OF this] have "?\<pi> (s i) \<cdot> \<sigma> i \<rhd> ?\<pi> (t i) \<cdot> \<sigma> i" .
              then show ?thesis
                using s_no_vars[of i]
                and t_no_vars[of i]
                using proj_term_subst_apply_term_distrib by auto
            next
              assume step_rhd: "(?\<pi> (s i), ?\<pi> (t i)) \<in> rstep ?wfR O {\<unrhd>}"
              from mchain have "s i \<cdot> \<sigma> i \<in> NF_terms Q" and nfsub: "NF_subst nfs (s i, t i) (\<sigma> i) Q" by (auto simp: ichain.simps)
              moreover have "s i \<cdot> \<sigma> i \<unrhd> ?\<pi> (s i) \<cdot> \<sigma> i"
                using supteq_proj_term[of "s i \<cdot> \<sigma> i"]
                unfolding proj_term_subst_apply_term_distrib[OF s_no_vars]
                .
              ultimately have NF_si: "?\<pi> (s i) \<cdot> \<sigma> i \<in> NF_terms Q" using NF_subterm by blast
              from NF_imp_subt_NF[OF this] have NF_terms: "\<forall>u\<lhd>?\<pi> (s i) \<cdot> \<sigma> i. u \<in> NF_terms Q" .
              from step_rhd obtain u where step: "(?\<pi> (s i), u) \<in> rstep ?wfR" and "u \<unrhd> ?\<pi> (t i)"
                by auto
              then obtain C l r \<tau> where si: "?\<pi> (s i) = C \<langle> l \<cdot> \<tau> \<rangle>" and u: "u = C \<langle> r \<cdot> \<tau> \<rangle>"
                and wlr: "(l,r) \<in> ?wfR" by auto
              from wlr have vrl: "vars_term r \<subseteq> vars_term l" unfolding wf_rules_def wf_rule_def by auto
              from si have "?\<pi> (s i) \<unrhd> l \<cdot> \<tau>" by auto
              then have subtl: "?\<pi> (s i) \<cdot> \<sigma> i \<unrhd> l \<cdot> \<tau> \<cdot> \<sigma> i" by auto
              from NF_subterm[OF NF_si this] have NFli: "l \<cdot> \<tau> \<cdot> \<sigma> i \<in> NF_terms Q" .
              have "(?\<pi> (s i) \<cdot> \<sigma> i, u \<cdot> \<sigma> i) \<in> qrstep nfs Q ?R"
                unfolding si u subst_apply_term_ctxt_apply_distrib
              proof (rule wf_to_R, rule qrstep.ctxt[OF qrstepI[OF _ wlr, of _ _ _ Hole]], unfold intp_actxt.simps, intro allI impI)
                show "l \<cdot> \<tau> \<cdot> \<sigma> i = l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma> i)" by simp
                show "r \<cdot> \<tau> \<cdot> \<sigma> i = r \<cdot> (\<tau> \<circ>\<^sub>s \<sigma> i)" by simp
              next
                fix t
                assume "l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma> i) \<rhd> t"
                with NF_imp_subt_NF[OF NFli] show "t \<in> NF_terms Q" by auto
              qed simp
              moreover from \<open>u \<unrhd> ?\<pi> (t i)\<close> have "u \<cdot> \<sigma> i \<unrhd> ?\<pi> (t i) \<cdot> \<sigma> i" by auto
              ultimately have "(?\<pi> (s i) \<cdot> \<sigma> i, ?\<pi> (t i) \<cdot> \<sigma> i) \<in> qrstep nfs Q ?R O {\<unrhd>}"
                by auto
              then show ?thesis
                unfolding proj_term_subst_apply_term_distrib[OF s_no_vars]
                unfolding proj_term_subst_apply_term_distrib[OF t_no_vars]
                unfolding supteq_supt_set_conv by (rule set_rev_mp) regexp
            qed
          qed
        next
          assume "(s i, t i) \<in> ?P'"
          with weak have "?\<pi> (s i) = ?\<pi> (t i)"
            unfolding eqs by auto
          then have "?\<pi> (s i) \<cdot> \<sigma> i = ?\<pi> (t i) \<cdot> \<sigma> i" by simp
          then have "?s i = ?t i"
            using s_no_vars[of i] and t_no_vars[of i] by simp
          then show ?thesis by simp
        qed
      } note si_ti = this
      have chain: "chain (?S^*) ?s"
      proof
        fix i
        have "(?t i, ?s (Suc i)) \<in> ?S^*"
        proof -
          from mchain
            have "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q ?R)^*"
            by (simp add: ichain.simps)
          from qrsteps_proj_term[OF this ts_undef nvar]
            show ?thesis using rtrancl_Un_subset[of "{\<rhd>}" "qrstep nfs Q ?R"] 
              by auto
        qed
        with si_ti[of i] show "(?s i, ?s (Suc i)) \<in> ?S^*" by simp
      qed
      from chain_imp_rtrancl[OF this] and mono
        have between: "\<forall>i. (?s i, ?s (f i)) \<in> ?S^*" by simp
      
      let ?s' = "\<lambda>i. ?\<pi> (s (shift_by f (Suc i)) \<cdot> \<sigma> (shift_by f (Suc i)))"
      have "\<forall>i. (?s i, ?s (Suc (f i))) \<in> ?S^+"
      proof
        fix i
        from strict have "(?\<pi> (s (f i) \<cdot> \<sigma> (f i)), ?\<pi> (t (f i) \<cdot> \<sigma> (f i))) \<in> ?S^+"
        proof (elim disjE conjE)
          assume Q: "Q = {}" and strict: "\<forall>(l, r)\<in>D. (?\<pi> l, ?\<pi> r) \<in> ?S^+"
          with D_seq have "(?\<pi> (s (f i)), ?\<pi> (t (f i))) \<in> ?S^+" by blast
          from supt_rstep_trancl_stable[OF this[unfolded Q qrstep_rstep_conv]]
            show ?thesis
            using s_no_vars[of "f i"] t_no_vars[of "f i"] by (simp add: Q)
        next
          assume "\<forall>(l, r)\<in>D. (?\<pi> l, ?\<pi> r) \<in> ?S'"
          with D_seq have "(?\<pi> (s (f i)), ?\<pi> (t (f i))) \<in> ?S'" by auto
          then show ?thesis
          proof
            assume "?\<pi> (s (f i)) \<rhd> ?\<pi> (t (f i))"
            from supt_subst[OF this, of "\<sigma> (f i)"]
              show ?thesis 
              using s_no_vars[of "f i"]
              and t_no_vars[of "f i"]
              using proj_term_subst_apply_term_distrib by auto
          next
            from mchain have "s (f i) \<cdot> \<sigma> (f i) \<in> NF_terms Q" by (auto simp: ichain.simps)
            moreover have "s (f i) \<cdot> \<sigma> (f i) \<unrhd> ?\<pi> (s (f i)) \<cdot> \<sigma> (f i)"
              using supteq_proj_term[of "s (f i) \<cdot> \<sigma> (f i)"]
              unfolding proj_term_subst_apply_term_distrib[OF s_no_vars]
              .
            ultimately have NF_si: "?\<pi> (s (f i)) \<cdot> \<sigma> (f i) \<in> NF_terms Q" using NF_subterm by blast
            from NF_imp_subt_NF[OF this] have NF_terms: "\<forall>u\<lhd>?\<pi> (s (f i)) \<cdot> \<sigma> (f i). u \<in> NF_terms Q" .
            assume "(?\<pi> (s (f i)), ?\<pi> (t (f i))) \<in> rstep ?wfR O {\<unrhd>}"
            then obtain u where step: "(?\<pi> (s (f i)), u) \<in> rstep ?wfR" and "u \<unrhd> ?\<pi> (t (f i))"
              by auto
            then obtain C l r \<tau> where si: "?\<pi> (s (f i)) = C \<langle> l \<cdot> \<tau> \<rangle>" and u: "u = C \<langle> r \<cdot> \<tau> \<rangle>"
              and wlr: "(l,r) \<in> ?wfR" by auto
            from si have "?\<pi> (s (f i)) \<unrhd> l \<cdot> \<tau>" by auto
            then have subtl: "?\<pi> (s (f i)) \<cdot> \<sigma> (f i) \<unrhd> l \<cdot> \<tau> \<cdot> \<sigma> (f i)" by auto
            from NF_subterm[OF NF_si this] have NFli: "l \<cdot> \<tau> \<cdot> \<sigma> (f i) \<in> NF_terms Q" .
            have "(?\<pi> (s (f i)) \<cdot> \<sigma> (f i), u \<cdot> \<sigma> (f i)) \<in> qrstep nfs Q ?R" unfolding si u
            proof (rule wf_to_R, rule qrstepI[OF _ wlr], intro allI impI)
              show "C \<langle> l \<cdot> \<tau> \<rangle> \<cdot> \<sigma> (f i) = (C \<cdot>\<^sub>c \<sigma> (f i)) \<langle> l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma> (f i)) \<rangle>" by simp
              show "C \<langle> r \<cdot> \<tau> \<rangle> \<cdot> \<sigma> (f i) = (C \<cdot>\<^sub>c \<sigma> (f i)) \<langle> r \<cdot> (\<tau> \<circ>\<^sub>s \<sigma> (f i)) \<rangle>" by simp
            next
              fix t
              assume "l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma> (f i)) \<rhd> t"
              with NF_imp_subt_NF[OF NFli] show "t \<in> NF_terms Q" by auto
            qed simp
            moreover from \<open>u \<unrhd> ?\<pi> (t (f i))\<close> have "u \<cdot> \<sigma> (f i) \<unrhd> ?\<pi> (t (f i)) \<cdot> \<sigma> (f i)" by auto
            ultimately have step: "(?\<pi> (s (f i)) \<cdot> \<sigma> (f i), ?\<pi> (t (f i)) \<cdot> \<sigma> (f i)) \<in> qrstep nfs Q ?R O {\<unrhd>}"
              by auto            
            show ?thesis 
              by (rule set_mp[OF _ step[unfolded 
                proj_term_subst_apply_term_distrib[OF s_no_vars]
                proj_term_subst_apply_term_distrib[OF t_no_vars]]],
                unfold supteq_supt_set_conv, regexp)
          qed
        qed
        with between[THEN spec, of i] have "(?s i, ?\<pi> (t (f i) \<cdot> \<sigma> (f i))) \<in> ?S^+" by simp
        moreover have "(?\<pi> (t (f i) \<cdot> \<sigma> (f i)), ?\<pi> (s (Suc (f i)) \<cdot> \<sigma> (Suc (f i)))) \<in> ?S^*"
        proof -
          from mchain
            have "(t (f i) \<cdot> \<sigma> (f i), s (Suc (f i)) \<cdot> \<sigma> (Suc (f i))) \<in> (qrstep nfs Q ?R)^*" by (simp add: ichain.simps)
          from qrsteps_proj_term[OF this ts_undef nvar, of p]
            show ?thesis
            using rtrancl_Un_subset[of "{\<rhd>}" "qrstep nfs Q ?R"] by auto
        qed
        ultimately show "(?s i, ?s (Suc (f i))) \<in> ?S^+" by simp
      qed
      then have "\<forall>i. (?s' i, ?s' (Suc i)) \<in> ?S^+" by simp
      with HOL.refl[of "?s' 0"]
        have "\<exists>S. S 0 = ?s' 0 \<and> (\<forall>i. (S i, S (Suc i)) \<in> ?S^+)" by best
      then have "\<not> SN_on (?S^+) {?s' 0}" unfolding SN_defs by simp
      moreover have "SN_on (?S^+) {?s' 0}"
      proof -
        have "(?t 0, ?s' 0) \<in> (?S^+)^*"
        proof -
          from mchain have "(t 0 \<cdot> \<sigma> 0, s (Suc 0) \<cdot> \<sigma> (Suc 0)) \<in> (qrstep nfs Q ?R)^*" by (simp add: ichain.simps)
          from qrsteps_proj_term[OF this ts_undef nvar, of p]
            have "(?t 0, ?s (Suc 0)) \<in> ?S^*"
            using rtrancl_Un_subset[of "{\<rhd>}" "qrstep nfs Q ?R"] by auto
          moreover have "(?s (Suc 0), ?s' 0) \<in> ?S^*"
          proof -
            have "shift_by f (Suc 0) \<ge> Suc 0" by simp
            from chain_imp_rtrancl[OF chain this] show ?thesis by simp
          qed
          ultimately show ?thesis by simp
        qed
        moreover have "SN_on (?S^+) {?t 0}"
        proof -
          from m_or_inn have "SN_on (qrstep nfs Q ?R) {?t 0}"
          proof
            assume m
            with mchain m_or_inn have "SN_on (qrstep nfs Q ?R) {t 0 \<cdot> \<sigma> 0}" by (simp add: minimal_cond_def)
            moreover have "(t 0 \<cdot> \<sigma> 0, ?t 0) \<in> {\<unrhd>}" by (simp add: supteq_proj_term)
            ultimately show "SN_on (qrstep nfs Q ?R) {?t 0}"
              using subterm_preserves_SN_gen[OF ctxt_closed_qrstep, of nfs Q "?R" "t 0 \<cdot> \<sigma> 0" "?t 0"]
              unfolding supt_supteq_conv by force
          next
            assume "NF_terms Q \<subseteq> NF_trs ?R"
            with mchain have NF: "s 0 \<cdot> \<sigma> 0 \<in> NF_trs ?R" by (auto simp: ichain.simps)
            from supteq_proj_term
            have "s 0 \<cdot> \<sigma> 0 \<unrhd> ?s 0" . 
            from NF_subterm[OF NF this] have NF: "?s 0 \<in> NF_trs ?R" .
            moreover have "?s 0 \<unrhd> ?t 0" using si_ti[of 0] 
            proof (induct)
              case (step y z)
              from NF_subterm[OF NF step(3)] have NF: "y \<in> NF_trs ?R" .
              have "y \<in> NF (qrstep nfs Q ?R)"
                by (rule set_mp[OF NF_anti_mono NF], auto)
              with step(2) have "y \<rhd> z" by auto
              with step(3) show ?case 
                by (metis subterm.dual_order.strict_implies_order subterm.order.strict_trans2)
            qed auto
            ultimately have NF: "?t 0 \<in> NF_trs ?R" by (rule NF_subterm)
            have "?t 0 \<in> NF (qrstep nfs Q ?R)"
              by (rule set_mp[OF NF_anti_mono NF], auto)
            from NF_imp_SN_on[OF this]            
            show "SN_on (qrstep nfs Q ?R) {?t 0}" . 
          qed
          from SN_on_trancl[OF SN_on_qrstep_imp_SN_on_supt_union_qrstep[OF this]]
            show ?thesis .
        qed
        ultimately show ?thesis by (rule steps_preserve_SN_on)
      qed
      ultimately show False ..
    qed
    then show "\<exists>i. ichain (nfs,m',P',Pw',Q',R',Rw') (shift s i) (shift t i) (shift \<sigma> i)"
      by (auto simp: eqs ichain.simps)
  qed
qed

lemmas subterm_criterion_proc_sound =
  subset_proc_to_sound_proc[OF subset_subterm_criterion_proc]

end

