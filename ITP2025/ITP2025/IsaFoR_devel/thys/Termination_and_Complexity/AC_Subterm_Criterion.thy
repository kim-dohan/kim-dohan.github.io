(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>AC Subterm Criterion\<close>

theory AC_Subterm_Criterion
imports
  Framework.Relative_DP_Framework
  AC_TRS.AC_Rewriting
  Ord.Subterm_Multiset
  Auxx.Multiset2
begin

lemma suptmulexeq_singleton_Var:
  assumes "{#Var x#} \<unrhd>\<^sub># T"
  obtains "T = {#Var x#}" | "T = {#}"
proof -
  obtain X Y Z where x: "{#Var x#} = X + Z" and T: "T = Y + Z"
    and *: "\<forall>y\<in>set_mset Y. \<exists>x\<in>set_mset X. x \<rhd> y" using assms by (auto elim: ns_mul_ext_IdE)
  show ?thesis
  proof (cases "Z")
    case empty
    with x and T and * have "\<forall>y\<in>set_mset T. Var x \<rhd> y" by auto
    then have "T = {#}" by (cases T) auto
    then show ?thesis ..
  next
    case (add z Z')
    then have "Z = {#Var x#}" and "X = {#}" and [simp]: "z = Var x"
      using x and T by (auto split: if_splits)
    with * have "T = {#Var x#}" by (auto simp: T multiset_eq_iff)
    then show ?thesis ..
  qed
qed


subsection \<open>Projections\<close>

abbreviation "proj_mset f T \<equiv> \<Sum>\<^sub># (image_mset f T)"

abbreviation subst_mset (infixl "\<cdot>\<^sub>m" 67)
where
  "M \<cdot>\<^sub>m \<sigma> \<equiv> image_mset (\<lambda>t. t \<cdot> \<sigma>) M"

lemma proj_mset_cong:
  assumes "\<And>x. x \<in># M \<Longrightarrow> f x = g x"
  shows "proj_mset f M = proj_mset g M"
using image_mset_cong [of M f g, OF assms] by auto

context
  fixes proj :: "'f status"
    and F :: "'f sig"
begin

fun proj_term
where
  "proj_term (Var x) = {#Var x#}"
| "proj_term (Fun f ts) =
    (if (f, length ts) \<in> F then \<Sum>\<^sub># (mset (map (\<lambda>i. proj_term (ts ! i)) (status proj (f, length ts))))
    else {#Fun f ts#})"

abbreviation suptproj_pred (infix "\<rhd>\<^sup>\<pi>" 55)
where
  "s \<rhd>\<^sup>\<pi> t \<equiv> proj_term s \<rhd>\<^sub># proj_term t"

abbreviation suptprojeq_pred (infix "\<unrhd>\<^sup>\<pi>" 55)
where
  "s \<unrhd>\<^sup>\<pi> t \<equiv> proj_term s \<unrhd>\<^sub># proj_term t"

lemma proj_term_supteq:
  assumes "u \<in># proj_term t"
  shows "t \<unrhd> u"
using assms
apply (induct t)
apply (auto split: if_splits simp: in_multiset_in_set Fun_supteq dest: set_status_nth)
by (meson status_aux)

lemma proj_term_supt:
  assumes u: "u \<in># proj_term t"
  and neq: "proj_term t \<noteq> {# t #}"
  shows "t \<rhd> u"
proof -
  from neq obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from neq have "proj_term t = \<Sum>\<^sub>#(mset (map (\<lambda>i. proj_term (ts ! i)) (status proj (f, length ts))))"
    unfolding t by auto
  from u[unfolded this] obtain i where "u \<in># proj_term (ts ! i)" and "i \<in> set (status proj (f,length ts))"
    by (auto simp: in_multiset_in_set dest: set_status_nth)
  from set_status_nth[OF refl this(2)] this(1) obtain ti where ti: "ti \<in> set ts" and "u \<in># proj_term ti" by auto
  from proj_term_supteq[OF this(2)] ti show ?thesis unfolding t by auto
qed

lemma proj_term_subst:
  "proj_mset proj_term (proj_term t \<cdot>\<^sub>m \<sigma>) = proj_term (t \<cdot> \<sigma>)"
proof (induct t)
  case (Fun f ts)
  then have "\<And>i. i \<in># mset (status proj (f, length ts)) \<Longrightarrow>
    proj_mset (proj_term \<circ> (\<lambda>t. t \<cdot> \<sigma>)) (proj_term (ts ! i)) = proj_term (map (\<lambda>t. t \<cdot> \<sigma>) ts ! i)"
    by (auto simp: in_multiset_in_set multiset.map_comp set_status_nth)
  then show ?case by (auto simp: mset_map multiset.map_comp intro: proj_mset_cong)
qed simp

lemma proj_term_idemp:
  "proj_mset proj_term (proj_term t) = proj_term t"
using proj_term_subst [of Var t] by simp

lemma proj_term_root:
  assumes "u \<in># proj_term t"
  obtains (Var) "root u = None"
  | (not_F) f and n where "root u = Some (f, n)" and "(f, n) \<notin> F"
using assms
by (induct t arbitrary: u) (force split: if_splits simp: in_multiset_in_set status_aux)+

lemma suptmulexeq_subst:
  assumes "s \<unrhd>\<^sup>\<pi> t"
  shows "s \<cdot> \<sigma> \<unrhd>\<^sup>\<pi> t \<cdot> \<sigma>"
proof -
  obtain S T U where proj_s: "proj_term s = S + U" and "proj_term t = T + U"
    and *: "\<forall>t' \<in> set_mset T. \<exists>s' \<in> set_mset S. s' \<rhd> t'"
    using assms by (auto elim: ns_mul_ext_IdE)
  then have s: "proj_term (s \<cdot> \<sigma>) = proj_mset proj_term (S \<cdot>\<^sub>m \<sigma>) + proj_mset proj_term (U \<cdot>\<^sub>m \<sigma>)"
    and t: "proj_term (t \<cdot> \<sigma>) = proj_mset proj_term (T \<cdot>\<^sub>m \<sigma>) + proj_mset proj_term (U \<cdot>\<^sub>m \<sigma>)"
    by (auto simp: proj_term_subst [symmetric])
  { fix t' v assume "t' \<in># T" and v: "v \<in># proj_term (t' \<cdot> \<sigma>)"
    with * obtain s' where "s' \<in> set_mset S" and "s' \<rhd> t'" by force
    then have "s' \<cdot> \<sigma> \<rhd> t' \<cdot> \<sigma>" by (auto dest: supt_subst)
    moreover have "t' \<cdot> \<sigma> \<unrhd> v" by (rule proj_term_supteq [OF v])
    ultimately have "s' \<cdot> \<sigma> \<rhd> v" by (auto dest: supt_supteq_trans)
    moreover have "s' \<cdot> \<sigma> \<in> set_mset (proj_term (s' \<cdot> \<sigma>))"
    proof -
      have *: "s' \<in># proj_term s" using \<open>s' \<in> set_mset S\<close> by (auto simp: proj_s)
      show ?thesis
      apply (cases s', auto, insert \<open>s' \<rhd> t'\<close>, blast)
      using * by (cases rule: proj_term_root) auto
    qed
    ultimately have "\<exists>w \<in> set_mset S. \<exists>x \<in> set_mset (proj_term (w \<cdot> \<sigma>)). x \<rhd> v"
      using \<open>s' \<in> set_mset S\<close> by blast }
  then show ?thesis by (intro ns_mul_ext_IdI [OF s t]) auto
qed

lemma proj_mset_empty:
  "proj_mset f M = {#} \<Longrightarrow> (\<forall>x. x \<in># M \<longrightarrow> f x = {#})"
by (induct M) simp_all

lemma status_ne_imp_proj_term_ne:
  assumes "\<forall>f \<in> F. status proj f \<noteq> []"
  shows "proj_term t \<noteq> {#}"
proof (induct t)
  case (Fun f ts)
  then have "(f, length ts) \<in> F \<Longrightarrow> ?case"
    using assms [THEN bspec, of "(f, length ts)"]
    by (force simp: mset_map in_multiset_in_set dest: status_ne proj_mset_empty)
  then show ?case by simp
qed simp

lemma proj_mset_nth_map:
  "proj_mset (\<lambda>i. proj_term (map g ss ! i))
     (mset (status proj (f, length ss))) =
    proj_mset (\<lambda>i. proj_term (g (ss ! i)))
     (mset (status proj (f, length ss)))"
by (intro proj_mset_cong) (auto simp: in_multiset_in_set set_status_nth)

lemma proj_term_ns_mul_ext: "{# t #} \<unrhd>\<^sub># proj_term t"
proof (cases "proj_term t = {# t #}")
  case False
  from proj_term_supt[OF _ this]
  show ?thesis using ns_mul_extI[OF refl refl, of "{#}" "{#}" _ _ "{#t#}"] by auto
qed auto

context
  fixes R :: "('f,'v)trs"
  assumes wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> is_Fun l"
  and rulesF: "\<And> l r. (l,r) \<in> R \<Longrightarrow> root l \<in> Some ` F \<Longrightarrow> l \<unrhd>\<^sup>\<pi> r"
begin
lemma rstep_proj_term: assumes st: "(s,t) \<in> rstep R"
  shows "(proj_term s, proj_term t) \<in> (ns_mul_ext ((rstep R)^*) {\<rhd>})^*"
proof -
  let ?ns = "ns_mul_ext ((rstep R)^*) {\<rhd>}"
  let ?sub = "{\<unrhd>\<^sub>#}"
  let ?p = proj_term
  have sub: "?sub \<subseteq> ?ns" 
    by (rule ns_mul_ext_mono, auto)
  from st obtain C l r \<sigma> where s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and lr: "(l,r) \<in> R" by auto
  note lrF = rulesF[OF lr]
  show ?thesis unfolding s t
  proof (induct C)
    case Hole
    show ?case 
    proof (cases "root l \<in> Some ` F")
      case True
      from suptmulexeq_subst[OF rulesF[OF lr True], of \<sigma>] sub
      show ?thesis by auto
    next
      case False
      from wf[OF lr] obtain f ls where l: "l = Fun f ls" by (cases l, auto)
      from lr have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep R" by auto
      then have "({# l \<cdot> \<sigma> #}, {# r \<cdot> \<sigma> #}) \<in> ?ns" by (intro ns_mul_ext_singleton, auto)
      with False have "(?p (l \<cdot> \<sigma>), {# r \<cdot> \<sigma> #}) \<in> ?ns" unfolding l by auto
      moreover have "{# r \<cdot> \<sigma> #} \<unrhd>\<^sub># ?p (r \<cdot> \<sigma>)"
        by (rule proj_term_ns_mul_ext)
      then have "({# r \<cdot> \<sigma> #}, ?p (r \<cdot> \<sigma>)) \<in> ?ns" using sub by auto
      ultimately show ?thesis by auto
    qed
  next
    case (More f bef C aft)
    let ?n = "Suc (length bef + length aft)"
    let ?f = "(f,?n)"
    let ?C = "More f bef C aft"
    show ?case
    proof (cases "?f \<in> F")
      case False
      have "(?C \<langle>l \<cdot> \<sigma>\<rangle>, ?C \<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep R" by (intro rstepI[OF lr refl refl])
      with set_mp[OF sub ns_mul_ext_singleton] 
      show ?thesis using False by auto
    next
      case True
      define idx where "idx = status proj (f, Suc (length bef + length aft))"
      let ?i = "length bef"
      let ?g = "\<lambda> lr i. ?p ((bef @ C\<langle>lr \<cdot> \<sigma>\<rangle> # aft) ! i)"
      let ?gen = "\<lambda> lr idx. \<Sum>\<^sub>#(mset (map (?g lr) idx))"
      let ?l = "?gen l" let ?r = "?gen r"
      have id: "?thesis = ((?l idx, ?r idx) \<in> ?ns^*)"
        by (simp add: True idx_def[symmetric])
      show ?thesis unfolding id
      proof (induct idx)
        case (Cons i idx)
        have l: "?l (i # idx) = ?g l i + ?l idx" by (simp add: ac_simps)
        have r: "?r (i # idx) = ?g r i + ?r idx" by (simp add: ac_simps)
        have refl: "refl Id" unfolding refl_on_def by auto
        show ?case unfolding l r
          by (rule ns_ns_mul_ext_union_compat_rtrancl[OF _ _ Cons], insert More,
          cases "i = ?i"; cases "i - ?i", auto simp: nth_append intro: refl_rtrancl)
      qed simp
    qed
  qed
qed

lemma rsteps_proj_term: "(s,t) \<in> (rstep R)^* 
  \<Longrightarrow> (proj_term s, proj_term t) \<in> (ns_mul_ext ((rstep R)^*) {\<rhd>})^*"
  by (induct rule: rtrancl_induct, auto dest: rstep_proj_term)
end  

context
  assumes ne: "\<forall>f\<in>F. status proj f \<noteq> []"
begin

lemma suptmulex_subst:
  assumes "s \<rhd>\<^sup>\<pi> t"
  shows "s \<cdot> \<sigma> \<rhd>\<^sup>\<pi> t \<cdot> \<sigma>"
proof -
  obtain S T U where S_ne: "S \<noteq> {#}"
    and proj_s: "proj_term s = S + U" and "proj_term t = T + U"
    and *: "\<forall>t' \<in> set_mset T. \<exists>s' \<in> set_mset S. s' \<rhd> t'"
    using assms by (auto elim: s_mul_ext_IdE)
  then have s: "proj_term (s \<cdot> \<sigma>) = proj_mset proj_term (S \<cdot>\<^sub>m \<sigma>) + proj_mset proj_term (U \<cdot>\<^sub>m \<sigma>)"
    and t: "proj_term (t \<cdot> \<sigma>) = proj_mset proj_term (T \<cdot>\<^sub>m \<sigma>) + proj_mset proj_term (U \<cdot>\<^sub>m \<sigma>)"
    by (auto simp: proj_term_subst [symmetric])
  have ne': "proj_mset proj_term (S \<cdot>\<^sub>m \<sigma>) \<noteq> {#}"
    using S_ne
    by (auto dest!: proj_mset_empty simp: status_ne_imp_proj_term_ne [OF ne])
  { fix t' v assume "t' \<in># T" and v: "v \<in># proj_term (t' \<cdot> \<sigma>)"
    with * obtain s' where "s' \<in> set_mset S" and "s' \<rhd> t'" by force
    then have "s' \<cdot> \<sigma> \<rhd> t' \<cdot> \<sigma>" by (auto dest: supt_subst)
    moreover have "t' \<cdot> \<sigma> \<unrhd> v" by (rule proj_term_supteq [OF v])
    ultimately have "s' \<cdot> \<sigma> \<rhd> v" by (auto dest: supt_supteq_trans)
    moreover have "s' \<cdot> \<sigma> \<in> set_mset (proj_term (s' \<cdot> \<sigma>))"
    proof -
      have *: "s' \<in># proj_term s" using \<open>s' \<in> set_mset S\<close> by (auto simp: proj_s)
      show ?thesis
      apply (cases s', auto, insert \<open>s' \<rhd> t'\<close>, blast)
      using * by (cases rule: proj_term_root) auto
    qed
    ultimately have "\<exists>w \<in> set_mset S. \<exists>x \<in> set_mset (proj_term (w \<cdot> \<sigma>)). x \<rhd> v"
      using \<open>s' \<in> set_mset S\<close> by blast }
  then show ?thesis by (intro s_mul_ext_IdI [OF ne' s t]) auto
qed

theorem ac_subterm_proc: fixes P :: "('f,'v)trs"
  assumes fin: "finite_rel_dpp (P', Q', R, Rw, E)"
  and PQ: "\<And> l r. (l,r) \<in> P \<union> Q \<Longrightarrow> l \<unrhd>\<^sup>\<pi> r"
  and RE: "\<And> l r. (l,r) \<in> R \<union> Rw \<union> E \<Longrightarrow> root l \<in> Some ` F \<Longrightarrow> l \<unrhd>\<^sup>\<pi> r"
  and P': "\<And> l r. (l,r) \<in> (P - P') \<union> (Q - Q') \<Longrightarrow> l \<rhd>\<^sup>\<pi> r"
  and E: "size_preserving_trs E" (* actually, size-non-increasing would suffice, but there is no definition for that *)
  and wf: "\<And> l r. (l,r) \<in> R \<union> Rw \<union> E \<Longrightarrow> is_Fun l"
  shows "finite_rel_dpp (P, Q, R, Rw, E)"
proof (rule finite_rel_dpp_split_top[OF finite_rel_dpp_pairs_mono[OF fin]])  
  let ?S = "{(l,r). l \<rhd>\<^sup>\<pi> r} :: ('f,'v)trs"
  define S where "S = ?S" 
  let ?S = "(relto {\<rhd>} (rstep (R \<union> Rw \<union> E)))^+"
  let ?RE = "(rstep (R \<union> Rw \<union> E))^*"
  define relS where "relS = s_mul_ext ?RE ?S"
  define relNS where "relNS = ns_mul_ext ?RE ?S"
  have subNS: "{\<unrhd>\<^sub>#} \<subseteq> relNS" unfolding relNS_def
    by (rule ns_mul_ext_mono, auto)
  have subS: "{\<rhd>\<^sub>#} \<subseteq> relS" unfolding relS_def
    by (rule s_mul_ext_mono, auto)
  show "P - S \<subseteq> P'" "Q - S \<subseteq> P' \<union> Q'" using P' unfolding S_def by auto
  show "finite_rel_dpp (S \<inter> (P \<union> Q), P \<union> Q - S, {}, R \<union> Rw, E)"
  proof
    fix s t \<sigma>
    assume "min_relchain (S \<inter> (P \<union> Q), P \<union> Q - S, {}, R \<union> Rw, E) s t \<sigma>"
    then have chain: "min_relchain (S \<inter> (P \<union> Q), P \<union> Q, {}, R \<union> Rw, E) s t \<sigma>" 
      unfolding min_relchain.simps by auto
    note chain = chain[unfolded min_relchain.simps, simplified]
    from chain have st: "\<And> i. (s i, t i) \<in> P \<union> Q" by auto
    let ?p = "proj_term"
    define ss where "ss = (\<lambda> i. ?p (s (Suc i) \<cdot> \<sigma> (Suc i)))"
    define ts where "ts = (\<lambda> i. ?p (t i \<cdot> \<sigma> i))"
    {
      fix i
      from chain have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (rstep (R \<union> Rw \<union> E))\<^sup>*" by auto
      have "(ts i, ss i) \<in> relNS^*" 
        unfolding ss_def ts_def relNS_def
        by (rule set_mp[OF rtrancl_mono[OF ns_mul_ext_mono] rsteps_proj_term[OF wf RE steps]], auto)
    } note ts = this
    have OP: "order_pair ?S ?RE"
    proof (unfold_locales, goal_cases)
      case 4 show ?case by regexp
    next 
      case 5 show ?case by regexp
    qed (auto intro: trans_rtrancl refl_rtrancl)
    interpret order_pair relS relNS unfolding relS_def relNS_def
      using order_pair.mul_ext_order_pair[OF OP] .
    {
      fix i
      from suptmulexeq_subst[OF PQ[OF st[of "Suc i"]]]
      have "ss i \<unrhd>\<^sub># ts (Suc i)" unfolding ss_def ts_def .
      then have "(ss i, ts (Suc i)) \<in> relNS" using subNS by auto
      with ts[of i] have "(ts i, ts (Suc i)) \<in> relNS^*" by auto
      then have "(ts i, ts (Suc i)) \<in> relNS" unfolding rtrancl_NS .
    } note NS = this
    {
      fix i
      assume "(s (Suc i), t (Suc i)) \<in> S \<inter> (P \<union> Q)"
      then have "s (Suc i) \<rhd>\<^sup>\<pi> t (Suc i)" unfolding S_def by auto
      from suptmulex_subst[OF this]
      have "ss i \<rhd>\<^sub># ts (Suc i)" unfolding ss_def ts_def .
      then have "(ss i, ts (Suc i)) \<in> relS" using subS by auto
      with ts[of i] have "(ts i, ts (Suc i)) \<in> relNS^* O relS" by auto
      then have "(ts i, ts (Suc i)) \<in> relS" by (simp add: order_simps)
    } note S = this
    have "SN_on relS {ts 0}" unfolding relS_def
    proof (rule SN_s_mul_ext_strong[OF OP], intro allI impI)
      fix ti
      assume "ti \<in># ts 0"
      from this[unfolded ts_def] have sub: "t 0 \<cdot> \<sigma> 0 \<unrhd> ti" by (rule proj_term_supteq)
      let ?relac = "relstep (R \<union> Rw) E"
      have ctxt: "ctxt.closed ?relac" by (rule ctxt.closed_relto, auto)
      from chain have "SN_on ?relac {t 0 \<cdot> \<sigma> 0}" by auto
      from ctxt_closed_SN_on_subt [OF ctxt this sub]
      have SN: "SN_on ?relac {ti}" .

      let ?T = "{t. SN_on ?relac {t}}"
      let ?rel = "?relac \<union> relto {\<rhd>} (rstep E)"
      let ?RE = "rstep (R \<union> Rw \<union> E)"
      let ?R = "rstep (R \<union> Rw)"
      let ?E = "rstep E"
      interpret E_compatible ?relac "(rstep E)\<^sup>*"
        by (standard, auto)
      interpret size_preserving_trs E by fact
      note SN_E = SN_suptrel[unfolded suptrel_def]  
      have "SN_on ?rel ?T"
        by (rule ctxt_closed_imp_SN_on_E_supt[OF ctxt SN_subset[OF SN_E]], regexp)
      with SN have "SN_on ?rel {ti}" unfolding SN_defs by blast
      then have "SN_on (?rel^+) {ti}" unfolding SN_on_trancl_SN_on_conv .
      then have "SN_on (relto ?R ({\<rhd>} \<union> ?E)) {ti}" by (rule SN_on_mono) regexp
      then have SN: "SN_rel_on ?R ({\<rhd>} \<union> ?E) {ti}" unfolding SN_rel_on_def .
      have "SN_on (relto {\<rhd>} ?RE) {ti}" 
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "\<not> SN_rel_on {\<rhd>} ?RE {ti}" unfolding SN_rel_on_def by auto
        from this[unfolded SN_rel_on_ideriv] obtain f where
          f: "ideriv {\<rhd>} ?RE f" and f0: "f 0 = ti" by auto
        from f have inf: "\<exists>\<^sub>\<infinity>i. f i \<rhd> f (Suc i)" unfolding ideriv_def by auto
        show False
        proof (cases "INFM i. (f i, f (Suc i)) \<in> ?R")
          case False
          then obtain j where j: "\<And> i. i \<ge> j \<Longrightarrow> (f i, f (Suc i)) \<notin> ?R" unfolding INFM_nat_le by blast
          define g where "g = shift f j"
          have inf: "\<exists>\<^sub>\<infinity>i. g i \<rhd> g (Suc i)" using inf unfolding g_def 
            using Infm_double_shift[of "\<lambda> x y. x \<rhd> y" f j "shift f 1"]
            by auto
          {
            fix i
            from f have "(f (i + j), f (Suc (i + j))) \<in> {\<rhd>} \<union> ?RE" unfolding ideriv_def by auto
            with j[of "i + j"] have "(g i, g (Suc i)) \<in> {\<rhd>} \<union> ?E" unfolding rstep_union g_def by auto
          }
          then have "ideriv {\<rhd>} ?E g" using inf by (auto simp: ideriv_def)
          then have nSN: "\<not> SN_rel {\<rhd>} ?E" unfolding SN_rel_ideriv by auto
          interpret size_preserving_trs E by fact
          from SN_suptrel[unfolded suptrel_def] nSN[unfolded SN_rel_on_def] 
          show False unfolding SN_trancl_SN_conv by blast
        next
          case True
          with f have "ideriv ?R ({\<rhd>} \<union> ?E) f" unfolding ideriv_def rstep_union by auto
          then have "\<not> SN_rel_on ?R ({\<rhd>} \<union> ?E) {ti}" using f0 unfolding SN_rel_on_ideriv by auto
          with SN show False by blast
        qed
      qed
      then show "SN_on ?S {ti}" unfolding SN_on_trancl_SN_on_conv .
    qed
    from non_strict_ending[of ts, OF _ compat_NS_S this] NS
    obtain j where j: "\<And> i. i \<ge> j \<Longrightarrow> (ts i, ts (Suc i)) \<notin> relS" by auto
    from chain[unfolded INFM_nat] obtain i where i: "i > j" and st: "(s i, t i) \<in> S \<inter> (P \<union> Q)" by blast
    define k where "k = i - 1"
    from i st have k: "k \<ge> j" and st: "(s (Suc k), t (Suc k)) \<in> S \<inter> (P \<union> Q)" unfolding k_def by auto
    from S[OF st] j[OF k] show False by auto
  qed
qed

corollary generalized_subterm_proc:
  fixes P :: "('f, 'v) trs"
  assumes fin: "finite_dpp (nfs, True, P', Pw', {},  R, Rw)"
  and P: "\<And> l r. (l,r) \<in> P \<union> Pw \<Longrightarrow> l \<unrhd>\<^sup>\<pi> r"
  and R: "\<And> l r. (l,r) \<in> R \<union> Rw \<Longrightarrow> root l \<in> Some ` F \<Longrightarrow> l \<unrhd>\<^sup>\<pi> r"
  and P': "\<And> l r. (l,r) \<in> (P - P') \<union> (Pw - Pw') \<Longrightarrow> l \<rhd>\<^sup>\<pi> r"
  and wf: "\<And> l r. (l,r) \<in> R \<union> Rw \<Longrightarrow> is_Fun l"
  shows "finite_dpp (nfs, True, P, Pw, {}, R, Rw)"
  unfolding finite_dpp_via_finite_rel_dpp
  by (rule ac_subterm_proc[OF fin[unfolded finite_dpp_via_finite_rel_dpp] P R P' _ wf], auto)  
end

end

end
