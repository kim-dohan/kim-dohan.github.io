(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
Author:  Rene Thiemann <rene.thiemann@uibk.ac.at> (2016)
Author:  Akihisa Yamada <akihisa.yamada@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

chapter \<open>AC-Dependency Pairs\<close>


theory AC_Dependency_Pairs
imports
  Framework.Relative_DP_Framework
  AC_TRS.AC_Rewriting
  AC_TRS.AC_Equivalence
  Ord.Subterm_Multiset
begin

lemma chain_reshuffling:
  fixes P Q R E :: "'a rel"
    and M :: "'a \<Rightarrow> bool"
  defines "M' \<equiv> {(s,t). M t} :: 'a rel"
  defines "S \<equiv> ((Q \<union> E) \<inter> M')\<^sup>* O ((P \<union> R) \<inter> M')"
  assumes f: "\<And> i. (f i, f (Suc i)) \<in> S"  
  shows "\<not> SN_rel_ext P Q R E M \<or> (\<exists> t. M t \<and> \<not> SN_on (relto (R \<inter> M') (E \<inter> M')) {t})"
proof -
  define QE where "QE = (Q \<union> E) \<inter> M'"
  define Q' where "Q' = relto (Q \<inter> M') QE"
  define PR where "PR = (P \<union> R) \<inter> M'"
  define P' where "P' = P \<inter> M'"
  define A where "A = (P \<union> Q \<union> R \<union> E) \<inter> M'"
  define g where "g = (\<lambda> i. f (Suc i))"
  have g: "\<And> i. (g i, g (Suc i)) \<in> S" unfolding g_def using f by auto
  from f[unfolded S_def] 
  have M: "\<And> i. M (g i)" unfolding M'_def g_def by auto
  from g have "\<forall> i. \<exists> hi. (g i, hi) \<in> QE\<^sup>* \<and> (hi, g (Suc i)) \<in> PR" unfolding S_def QE_def PR_def by blast
  from choice[OF this] obtain h where gh: "\<And> i. (g i, h i) \<in> QE\<^sup>*" and hg: "\<And> i. (h i, g (Suc i)) \<in> PR" by blast
  define j where "j = (\<lambda> i :: nat. i div 2)"
  define f where "f = (\<lambda> i. (if even i then g else h) (j i))"
  define t where "t = (\<lambda> i. (if even i then 
     if (f i, f (Suc i)) \<in> Q' then top_ns else normal_ns else
     if (f i, f (Suc i)) \<in> P' then top_s else normal_s))"
  have "QE \<subseteq> A" unfolding QE_def A_def by auto
  then have QE: "QE\<^sup>* \<subseteq> A\<^sup>*" by (rule rtrancl_mono)
  show ?thesis
  proof (cases "INFM i. t i \<in> {top_s,top_ns}")
    case True
    have "\<not> SN_rel_ext (A\<^sup>* O (P \<inter> M') O A\<^sup>*) (A\<^sup>* O ((P \<union> Q) \<inter> M') O A\<^sup>*) (A\<^sup>* O ((P \<union> R) \<inter> M') O A\<^sup>*) (A\<^sup>*) M"
      unfolding SN_rel_ext_def not_not
    proof (rule exI[of _ f], rule exI[of _ t], intro conjI allI)
      fix i
      have M: "M (g (j i))" by fact
      show "M (f i)"
      proof (cases "even i")
        case True
        then show ?thesis using M unfolding f_def by auto
      next
        case False
        then have id: "f i = h (j i)" unfolding f_def by auto
        from gh[of "j i"] M have "M (h (j i))" unfolding QE_def M'_def
          by (induct, auto)
        then show ?thesis using id by simp
      qed
      show "(f i, f (Suc i)) \<in> SN_rel_ext_step (A\<^sup>* O (P \<inter> M') O A\<^sup>*) (A\<^sup>* O ((P \<union> Q) \<inter> M') O A\<^sup>*)
          (A\<^sup>* O ((P \<union> R) \<inter> M') O A\<^sup>*) (A\<^sup>*) (t i)"
      proof (cases "even i")
        case True
        then have fi: "f i = g (j i)" and fsi: "f (Suc i) = h (j i)" and jsi: "j (Suc i) = j i"
          unfolding f_def j_def by auto
        show ?thesis
        proof (cases "(f i, f (Suc i)) \<in> Q'")
          case True
          then have t: "t i = top_ns" unfolding t_def using \<open>even i\<close> by auto
          with True QE fi fsi show ?thesis by (auto simp: Q'_def)
        next
          case False
          then have t: "t i = normal_ns" unfolding t_def using \<open>even i\<close> by auto
          with gh[of "j i"] QE fi fsi jsi show ?thesis by auto
        qed
      next
        case False
        then have fi: "f i = h (j i)" and fsi: "f (Suc i) = g (Suc (j i))" and jsi: "j (Suc i) = Suc (j i)"
          unfolding f_def j_def by auto
        show ?thesis
        proof (cases "(f i, f (Suc i)) \<in> P'")
          case True
          then have t: "t i = top_s" unfolding t_def using \<open>odd i\<close> by auto
          with True QE fi fsi show ?thesis by (auto simp: P'_def)
        next
          case False
          then have t: "t i = normal_s" unfolding t_def using \<open>odd i\<close> by auto
          with hg[of "j i"] QE fi fsi jsi show ?thesis by (auto simp: PR_def)
        qed
      qed
      show "\<exists>\<^sub>\<infinity>i. t i \<in> {top_s, normal_s}"
        unfolding INFM_nat_le 
      proof
        fix i
        show "\<exists> j \<ge> i. t j \<in> {top_s, normal_s}"
          by (rule exI[of _ "2 * i + 1"], auto simp: t_def)
      qed
    qed (rule True)      
    with SN_rel_ext_trans[of P Q R E M, folded M'_def, folded A_def]
    have "\<not> SN_rel_ext P Q R E M" by blast
    then show ?thesis ..
  next
    case False
    then obtain k where k: "\<And> i. i \<ge> k \<Longrightarrow> t i \<notin> {top_s, top_ns}" 
      unfolding INFM_nat_le by auto
    {
      fix i
      assume i: "i \<ge> k"
      then have "2 * i \<ge> k" by auto
      from k[OF this, unfolded t_def f_def j_def] 
      have nmem: "(g i, h i) \<notin> Q'" by auto
      have sub: "\<And> A B. (A \<union> B)\<^sup>* \<subseteq> B\<^sup>* \<union> relto A (A \<union> B)" by regexp
      from set_mp[OF sub gh[of i, unfolded QE_def Int_Un_distrib2]] nmem
      have gh: "(g i, h i) \<in> (E \<inter> M')\<^sup>*" unfolding QE_def Q'_def Int_Un_distrib2 by blast
      from i have "2 * i + 1 \<ge> k" by auto
      from k[OF this, unfolded t_def f_def j_def]
      have nmem: "(h i, g (Suc i)) \<notin> P'" by auto
      with hg[of i] have hg: "(h i, g (Suc i)) \<in> R \<inter> M'" unfolding PR_def P'_def by auto
      note gh hg
    } note gh = this
    define f where "f = (\<lambda> i. g (k + i))"
    have "(f i, f (Suc i)) \<in> relto (R \<inter> M') (E \<inter> M')" for i
      unfolding f_def using gh[of "k + i"] by auto
    then have "\<not> SN_on (relto (R \<inter> M') (E \<inter> M')) {f 0}" by (rule steps_imp_not_SN_on)
    with M[of k]
    show ?thesis unfolding f_def by auto
  qed
qed

lemma defined_symbol_finite_rel_dpp: 
  assumes fin: "finite_rel_dpp (P', Q', {}, R, E)"
  and P: "\<And> s t. (s,t) \<in> P - P' \<Longrightarrow> root s \<in> Some ` D \<and> root t \<in> Some ` C"
  and Q: "\<And> s t. (s,t) \<in> Q - Q' \<Longrightarrow> root s \<in> Some ` C \<and> root t \<in> Some ` C"
  and Q': "\<And> s t. (s,t) \<in> Q' \<Longrightarrow> root s \<in> Some ` D \<and> root t \<in> Some ` D"
  and P': "\<And> s t. (s,t) \<in> P' \<Longrightarrow> root s \<in> Some ` D \<and> root t \<in> Some ` D"
  and CD: "C \<inter> D = {}"
  and C: "\<And> f. f \<in> C \<Longrightarrow> \<not> defined (R \<union> E) f"
  and wf: "wf_trs (R \<union> E)"
  shows "finite_rel_dpp (P, Q, {}, R, E)"
proof
  fix s t \<sigma>
  assume chain: "min_relchain (P, Q, {}, R, E) s t \<sigma>"
  note * = chain[unfolded min_relchain.simps]
  note P = P[of "s i" "t i" for i]
  note Q = Q[of "s i" "t i" for i]
  note P' = P'[of "s i" "t i" for i]
  note Q' = Q'[of "s i" "t i" for i]
  note all = P Q P' Q'
  from * have st: "\<And> i. (s i, t i) \<in> P \<union> Q" by auto
  {
    fix j
    assume "root (t j) \<in> Some ` C"
    then have tj: "root (t j \<cdot> \<sigma> j) \<in> Some ` C" by (cases "t j", auto)
    from * have steps: "(t j \<cdot> \<sigma> j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> (rstep (R \<union> E))^*" by auto
    have "(t j \<cdot> \<sigma> j, s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> (nrrstep (R \<union> E))^*"
      by (rule rsteps_imp_nrrsteps[OF _ C _ steps], insert wf tj, (force simp: wf_trs_def)+)
    from nrrsteps_imp_eq_root_arg_rsteps[OF this] tj 
    have sj: "root (s (Suc j) \<cdot> \<sigma> (Suc j)) \<in> Some ` C"
      by auto
    with st[of "Suc j"] all[of "Suc j"] 
    have "root (s (Suc j)) \<in> Some ` C" by (cases "s (Suc j)", auto)
  } note tC_sC = this
  {
    fix j
    assume sj: "root (s j) \<in> Some ` C" 
    from st[of j] sj CD all[of j] have "root (t j) \<in> Some ` C" 
      by force
  } note sC_tC = this
  show False
  proof (cases "\<exists> i. root (s i) \<in> Some ` C")
    case True
    then obtain i where si: "root (s i) \<in> Some ` C" by auto
    {
      fix j
      assume "j \<ge> i"
      then have "root (s j) \<in> Some ` C"
      proof (induct j)
        case 0
        with si show ?case by simp
      next
        case (Suc j)
        show ?case
        proof (cases "j \<ge> i")
          case False
          with Suc(2) have "Suc j = i" by auto
          then show ?thesis using si by auto
        next
          case True
          from Suc(1)[OF this] have IH: "root (s j) \<in> Some ` C" .
          from tC_sC[OF sC_tC[OF this]] show ?thesis .
        qed
      qed
      then have "(s j, t j) \<notin> P" using all[of j] CD 
        by force
    } note noP = this
    with *[unfolded INFM_nat_le] show False by blast
  next
    case False
    then have C: "\<And> i. root (s i) \<notin> Some ` C" by auto
    let ?D = "(P - P') \<union> (Q - Q')"
    {
      fix i
      from C[of "Suc i"] have C: "root (s (Suc i)) \<notin> Some ` C" .
      with tC_sC[of i] have "root (t i) \<notin> Some ` C" by auto
      with all[of i] CD st[of i]
      have "(s i, t i) \<notin> ?D" by auto
    } note D = this
    have " \<exists>i. min_relchain (P - ?D, Q - ?D, {}, R, E) (shift s i) (shift t i) (shift \<sigma> i)"
      by (rule min_relchain_split_top[OF chain], insert D, auto simp: min_relchain.simps)
    then have "\<not> finite_rel_dpp (P - ?D, Q - ?D, {}, R, E)" unfolding finite_rel_dpp_def by blast
    moreover have "finite_rel_dpp (P - ?D, Q - ?D, {}, R, E)"
      by (rule finite_rel_dpp_pairs_mono[OF fin], auto)
    ultimately show False ..
  qed
qed


context size_preserving_trs
begin

interpretation subteq_redpair: SN_order_pair "suptrel R" "supteqrel R"
  by (standard, auto intro: SN_suptrel)

end

definition "strictly_finite P Q R E \<longleftrightarrow> \<not> (\<exists>s t \<sigma>. min_relchain (P, Q, R, {}, E) s t \<sigma>)"
definition "weakly_finite P Q R E \<longleftrightarrow> \<not> (\<exists>s t \<sigma>. min_relchain (P, Q, {}, R, E) s t \<sigma>)"

lemma strictly_finite_imp_SN_rel_ext:
  assumes "strictly_finite P Q R E"
  shows "SN_rel_ext (rrstep P) (rrstep Q) (rstep R) (rstep E) (\<lambda>t. SN_on (relstep R E) {t})"
  using assms no_chain_imp_SN_rel_ext[of P Q R "{}" E] unfolding strictly_finite_def by auto

lemma weakly_finite_imp_SN_rel_ext:
  assumes "weakly_finite P Q R E"
  shows "SN_rel_ext (rrstep P) (rrstep Q) {} (rstep (R \<union> E)) (\<lambda>t. SN_on (relstep R E) {t})"
  using assms no_chain_imp_SN_rel_ext[of P Q "{}" R E] unfolding weakly_finite_def rstep_union by auto

lemma strictly_finite_SN:
  assumes "strictly_finite P Q R E"
  defines "M' \<equiv> \<lambda>t. SN_on (relstep R E) {t}"
  defines "M \<equiv> {(s, t). M' t}"
  defines "S \<equiv> ((rrstep Q \<union> rstep E) \<inter> M)\<^sup>* O ((rrstep P \<union> rstep R) \<inter> M)"
  shows "SN S"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain f where "\<And>i. (f i, f (Suc i)) \<in> S" by (auto simp: SN_defs)
  from chain_reshuffling [of f, OF this [unfolded S_def M_def], folded M_def]
    consider (ichain) "\<not> SN_rel_ext (rrstep P) (rrstep Q) (rstep R) (rstep E) M'" |
      (min) "(\<exists>t. M' t \<and> \<not> SN_on (relto (rstep R \<inter> M) (rstep E \<inter> M)) {t})" by blast
  then show False
  proof (cases)
    case ichain
    with strictly_finite_imp_SN_rel_ext [OF assms(1)] show False by (auto simp: M'_def)
  next
    case min
    have "rstep R \<inter> M \<subseteq> rstep R" and "rstep E \<inter> M \<subseteq> rstep E" by auto
    from SN_on_mono [OF _ relto_mono [OF this]] and min show ?thesis by (auto simp: M'_def)
  qed
qed

context relative_dp
begin

theorem ACDP_transformation:
  assumes sp: "size_preserving_trs E" and F: "{f. defined (R \<union> E) f} \<subseteq> F"
    and fin: "strictly_finite (DP_on \<sharp> F R) (DP_on \<sharp> F E) R E"
  shows "SN (relstep R E)"
proof (rule ccontr)
  define M' where "M' = (\<lambda>t. SN_on (relstep R E) {t})"
  define M where "M = {(s::('f, 'v) term, t). M' t}"
  define E' where "E' = (rrstep (DP_on \<sharp> F E) \<union> rstep E)"
  define R' where "R' = (rrstep (DP_on \<sharp> F R) \<union> rstep R)"
  interpret sp: size_preserving_trs E using sp.
  note readable = M'_def M_def E'_def R'_def
  assume "\<not> SN (relstep R E)"
  then obtain s where "s \<in> Tinf (relstep R E)" by (auto simp: SN_def dest: not_SN_imp_subt_Tinf)
  then show False
  proof (induct "\<sharp> s" arbitrary: s rule: SN_induct [OF strictly_finite_SN [OF fin],folded readable])
    case (1 s)
    then have "s \<in> Tinf (relstep R E)" by auto
    from Tinf_starts_relchain [OF sp.SN_suptrel F this, unfolded starts_relchain_def]
      obtain v and n
      where "relchain_part (DP_on \<sharp> F R) (DP_on \<sharp> F E) s v n" by blast
    from this[unfolded relchain_part_def]
    have v: "\<And>i. v i \<in> Tinf (relstep R E)"
     and sv: "s = v 0"
     and E: "\<And>i. i < n \<Longrightarrow> (\<sharp> (v i), \<sharp> (v (Suc i))) \<in> E'"
     and R: "(\<sharp> (v n), \<sharp> (v (Suc n))) \<in> R'"
     unfolding E'_def R'_def by (auto simp: nrrstep_imp_rstep)
    from v have *: "\<And>i. M' (\<sharp> (v i))" unfolding M'_def using Tinf_sharp_imp_SN by auto
    from R * have "(\<sharp> (v n), \<sharp> (v (Suc n))) \<in> (R' \<inter> M)" unfolding M_def by auto
    moreover from E and * have "\<And>i. i < n \<Longrightarrow> (\<sharp> (v i), \<sharp> (v (Suc i))) \<in> E' \<inter> M" by (auto simp: M_def)
    then have "(\<sharp> s, \<sharp> (v n)) \<in> (E' \<inter> M)\<^sup>*" using sv by (induct n) (auto intro: rtrancl_into_rtrancl)
    ultimately have "(\<sharp> s, \<sharp> (v (Suc n))) \<in> (E' \<inter> M)\<^sup>* O (R' \<inter> M)" by auto
    from "1.hyps" [OF this] and v show False by force
  qed
qed

corollary SN_relstep_via_finite_rel_dpp:
  assumes "size_preserving_trs E" and F: "{f. defined (R \<union> E) f} \<subseteq> F"
    and fin: "finite_rel_dpp (DP_on \<sharp> F R, DP_on \<sharp> F E, R, {}, E)"
  shows "SN (relstep R E)"
  by (rule ACDP_transformation[OF assms(1-2)], insert fin,
  auto simp: strictly_finite_def finite_rel_dpp_def)
end

subsection \<open>AC-Extensions\<close>

inductive_set actopstep_sym for f and F :: "'f set" and R :: "('f, 'v) trs"
where
  root: "(s, t) \<in> rrstep R \<Longrightarrow> (s, t) \<in> actopstep_sym f F R"
| Binl: "root s = Some (f, 2) \<Longrightarrow> (s, t) \<in> actopstep_sym f F R \<Longrightarrow> f \<in> F \<Longrightarrow>
    (Bin f s u, Bin f t u) \<in> actopstep_sym f F R"
| Binr: "root s = Some (f, 2) \<Longrightarrow> (s, t) \<in> actopstep_sym f F R \<Longrightarrow> f \<in> F \<Longrightarrow>
    (Bin f u s, Bin f u t) \<in> actopstep_sym f F R"

definition "actopstep F R = {(s, t) | s t f. (s, t) \<in> actopstep_sym f F R}"

definition "acnontopstep F R = rstep R - actopstep F R"

lemma acnontopstep_eq_roots:
  assumes "(s, t) \<in> acnontopstep F R"
  shows "\<exists>f n. root s = Some (f, n) \<and> root t = Some (f, n)"
using assms
apply (auto simp: acnontopstep_def elim!: rstepE)
apply (case_tac C)
apply (auto simp: actopstep_def intro!: actopstep_sym.intros)
done

lemma actop_cases:
  assumes "(s, t) \<in> rstep R"
  obtains (top) "(s, t) \<in> actopstep F R"
    | (nontop) "(s, t) \<notin> actopstep F R" and "(s, t) \<in> acnontopstep F R"
using assms by (auto simp: acnontopstep_def)

context
  fixes R R\<^sub>e\<^sub>x\<^sub>t :: "('f, 'v) trs" and F\<^sub>A F\<^sub>C :: "'f set"
  assumes R_ext: "is_ext_trs R F\<^sub>A F\<^sub>C R\<^sub>e\<^sub>x\<^sub>t" and vc: "\<forall>(l, r)\<in>R. is_Fun l"
begin

interpretation aoc_rewriting F\<^sub>A F\<^sub>C .

private lemma vc_AC: "f \<in> F\<^sub>A \<Longrightarrow> (l, r) \<in> R \<Longrightarrow> root l = Some (f, 2) \<Longrightarrow> \<exists>x. x \<notin> vars_rule (l, r)"
using R_ext by (fastforce simp: is_ext_trs_def)

private lemma vc_A_only: "f \<in> F\<^sub>A - F\<^sub>C \<Longrightarrow> (l, r) \<in> R \<Longrightarrow> root l = Some (f, 2) \<Longrightarrow>
  \<exists>x y. x \<noteq> y \<and> x \<notin> vars_rule (l, r) \<and> y \<notin> vars_rule (l, r)"
using R_ext by (fastforce simp: is_ext_trs_def)

lemma AC_rrstep_imp_rrstep_ext_trs:
  assumes "root s = Some (f, 2)" and "f \<in> F\<^sub>A" and "(s, t) \<in> rrstep R"
  shows "(Bin f s u, Bin f t u) \<in> rrstep (ext_trs R)"
proof -
  obtain l and r and \<sigma> where lr: "(l, r) \<in> R" and [simp]: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>"
    using \<open>(s, t) \<in> rrstep R\<close> by (auto elim: rrstepE)
  with assms and vc and vc_AC [OF \<open>f \<in> F\<^sub>A\<close> lr] obtain x where "x \<notin> vars_rule (l, r)"
    and ext_rule: "(Bin f l (Var x), Bin f r (Var x)) \<in> ext_trs R" (is "(?l, ?r) \<in> _")
    apply (cases s; cases l)
    apply (auto simp: ext_trs_def ext_AC_trs_def ext_AC_rule_def ext_A_trs_def ext_A_rules_def)
    by (metis \<open>(l, r) \<in> R\<close> insert_subset order_refl root.simps(2))
  moreover define \<tau> where "\<tau> = (\<lambda>y. if y = x then u else \<sigma> y)"
  ultimately have "(?l \<cdot> \<tau>, ?r \<cdot> \<tau>) \<in> rrstep (ext_trs R)"
    and "Bin f s u = ?l \<cdot> \<tau>" and "Bin f t u = ?r \<cdot> \<tau>"
    using rrstepI [OF ext_rule, of "Bin f s u" \<tau> "Bin f t u"]
    by (auto simp: term_subst_eq_conv vars_rule_def) force
  then show ?thesis by simp
qed

lemma A_only_rrstep_imp_rrstep_ext_trs_right:
  assumes "root s = Some (f, 2)" and "f \<in> F\<^sub>A - F\<^sub>C" and "(s, t) \<in> rrstep R"
  shows "(Bin f u s, Bin f u t) \<in> rrstep (ext_trs R)"
proof -
  have "f \<in> F\<^sub>A" using assms by blast
  obtain l and r and \<sigma> where lr: "(l, r) \<in> R" and [simp]: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>"
    using \<open>(s, t) \<in> rrstep R\<close> by (auto elim: rrstepE)
  with assms and vc and vc_AC [OF \<open>f \<in> F\<^sub>A\<close> lr] obtain x where "x \<notin> vars_rule (l, r)"
    and ext_rule: "(Bin f (Var x) l, Bin f (Var x) r) \<in> ext_trs R" (is "(?l, ?r) \<in> _")
    apply (cases s; cases l)
    apply (auto simp: ext_trs_def ext_AC_trs_def ext_AC_rule_def ext_A_trs_def ext_A_rules_def)
    by (metis \<open>(l, r) \<in> R\<close> insert_subset order_refl root.simps(2))
  moreover define \<tau> where "\<tau> = (\<lambda>y. if y = x then u else \<sigma> y)"
  ultimately have "(?l \<cdot> \<tau>, ?r \<cdot> \<tau>) \<in> rrstep (ext_trs R)"
    and "Bin f u s = ?l \<cdot> \<tau>" and "Bin f u t = ?r \<cdot> \<tau>"
    using rrstepI [OF ext_rule, of "Bin f u s" \<tau> "Bin f u t"]
    apply (auto simp: term_subst_eq_conv vars_rule_def)
    by (metis (no_types, lifting) term_subst_eq)
  then show ?thesis by simp
qed

lemma A_only_rrstep_imp_rrstep_ext_trs_middle:
  assumes "root s = Some (f, 2)" and "f \<in> F\<^sub>A - F\<^sub>C" and "(s, t) \<in> rrstep R"
  shows "(Bin f (Bin f u s) v, Bin f (Bin f u t) v) \<in> rrstep (ext_trs R)"
proof -
  obtain l and r and \<sigma> where lr: "(l, r) \<in> R" and [simp]: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>"
    using \<open>(s, t) \<in> rrstep R\<close> by (auto elim: rrstepE)
  with assms and vc and vc_A_only [OF \<open>f \<in> F\<^sub>A - F\<^sub>C\<close> lr] obtain x and y
    where vars: "x \<noteq> y" "x \<notin> vars_rule (l, r)" "y \<notin> vars_rule (l, r)"
    and ext_rule: "(Bin f (Bin f (Var x) l) (Var y), Bin f (Bin f (Var x) r) (Var y)) \<in> ext_trs R" (is "(?l, ?r) \<in> _")
    apply (cases s; cases l)
    apply (auto simp: ext_trs_def ext_AC_trs_def ext_AC_rule_def ext_A_trs_def ext_A_rules_def)
    by (metis \<open>(l, r) \<in> R\<close> insert_subset order_refl root.simps(2))
  moreover define \<tau> where "\<tau> = (\<lambda>z. if z = x then u else if z = y then v else \<sigma> z)"
  ultimately have "(?l \<cdot> \<tau>, ?r \<cdot> \<tau>) \<in> rrstep (ext_trs R)"
    and "Bin f (Bin f u s) v = ?l \<cdot> \<tau>" and "Bin f (Bin f u t) v = ?r \<cdot> \<tau>"
    using rrstepI [OF ext_rule, of "Bin f (Bin f u s) v" \<tau> "Bin f (Bin f u t) v"]
    apply (auto simp: term_subst_eq_conv vars_rule_def)
    by (metis (no_types, lifting) term_subst_eq)
  then show ?thesis by simp
qed

lemma rrstep_ext_trs_imp_rrstep_ext_trs_AOCEQ_AC:
  assumes "root s = Some (f, 2)" and "f \<in> F\<^sub>A \<inter> F\<^sub>C" and "(s, t) \<in> rrstep (ext_trs R)"
  shows "(Bin f s u, Bin f t u) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ"
proof -
  obtain l and r and v and \<sigma> where rule: "(l, r) \<in> R"
    and "root l = Some (f, 2)"
    and "(Bin f l v, Bin f r v) \<in> ext_trs R"
    and [simp]: "s = Bin f l v \<cdot> \<sigma>" "t = Bin f r v \<cdot> \<sigma>"
    using assms
    by (auto elim!: rrstepE simp: ext_trs_def ext_AC_rule_def ext_AC_trs_def ext_A_trs_def ext_A_rules_def)
  moreover then obtain x where "x \<notin> vars_rule (l, r)"
    and ext_rule: "(Bin f l (Var x), Bin f r (Var x)) \<in> ext_trs R" (is "(?l, ?r) \<in> _")
    using vc and vc_AC [OF _ rule] and \<open>f \<in> F\<^sub>A \<inter> F\<^sub>C\<close>
    by (auto simp: ext_trs_def ext_AC_rule_def ext_AC_trs_def ext_A_trs_def ext_A_rules_def)
  moreover define \<tau> where "\<tau> = (\<lambda>y. if y = x then Bin f u (v \<cdot> \<sigma>) else \<sigma> y)"
  ultimately have "(?l \<cdot> \<tau>, ?r \<cdot> \<tau>) \<in> rrstep (ext_trs R)"
    and "?l \<cdot> \<tau> = Bin f (l \<cdot> \<sigma>) (Bin f u (v \<cdot> \<sigma>))"
    and "?r \<cdot> \<tau> = Bin f (r \<cdot> \<sigma>) (Bin f u (v \<cdot> \<sigma>))"
    using rrstepI [OF ext_rule refl refl, of \<tau>] by (auto simp: term_subst_eq_conv vars_rule_def)
  moreover then have "(Bin f s u, ?l \<cdot> \<tau>) \<in> AOCEQ" and "(?r \<cdot> \<tau>, Bin f t u) \<in> AOCEQ"
    using \<open>f \<in> F\<^sub>A \<inter> F\<^sub>C\<close> by (auto simp: aocconv_iff ac_simps)
  ultimately show ?thesis by blast
qed

lemma rrstep_ext_trs_imp_rrstep_ext_trs_AOCEQ_A_only_left:
  assumes "root s = Some (f, 2)" and "f \<in> F\<^sub>A - F\<^sub>C" and "(s, t) \<in> rrstep (ext_trs R)"
  shows "(Bin f s u, Bin f t u) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ"
using assms(3, 1, 2)
proof (cases rule: rrstep_ext_trs_cases)
  case ext_A_trs
  show ?thesis using ext_A_trs(2) and \<open>root s = Some (f, 2)\<close>
  proof (cases rule: rrstep_ext_A_trs_cases)
    case (left v w x)
    with AC_rrstep_imp_rrstep_ext_trs [of v f w]
      have "(Bin f v (Bin f x u), Bin f w (Bin f x u)) \<in> rrstep (ext_trs R)" by blast
    then show ?thesis by (rule relcomp3_I) (insert left, auto)
  next
    case [simp]: (right v w x)
    from A_only_rrstep_imp_rrstep_ext_trs_middle [OF this(1-3)]
      have "(Bin f (Bin f x v) u, Bin f (Bin f x w) u) \<in> rrstep (ext_trs R)" by blast
    then show ?thesis by auto
  next
    case (middle v w x y)
    from A_only_rrstep_imp_rrstep_ext_trs_middle [OF this(1-3)]
      have "(Bin f (Bin f x v) (Bin f y u), Bin f (Bin f x w) (Bin f y u)) \<in> rrstep (ext_trs R)" by blast
    then show ?thesis by (rule relcomp3_I) (insert middle, auto)
  qed
qed simp

lemma rrstep_ext_trs_imp_rrstep_ext_trs_AOCEQ_A_right:
  assumes "root s = Some (f, 2)" and "f \<in> F\<^sub>A - F\<^sub>C" and "(s, t) \<in> rrstep (ext_trs R)"
  shows "(Bin f u s, Bin f u t) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ"
using assms(3, 1, 2)
proof (cases rule: rrstep_ext_trs_cases)
  case ext_A_trs
  show ?thesis using ext_A_trs(2) and \<open>root s = Some (f, 2)\<close>
  proof (cases rule: rrstep_ext_A_trs_cases)
    case (left v w x)
    from A_only_rrstep_imp_rrstep_ext_trs_middle [OF this(1-3)]
      have "(Bin f (Bin f u v) x, Bin f (Bin f u w) x) \<in> rrstep (ext_trs R)" by blast
    then show ?thesis by (rule relcomp3_I) (insert left, auto)
  next
    case (right v w x)
    from A_only_rrstep_imp_rrstep_ext_trs_right [OF this(1-3)]
      have "(Bin f (Bin f u x) v, Bin f (Bin f u x) w) \<in> rrstep (ext_trs R)" by blast
    then show ?thesis by (rule relcomp3_I) (insert right, auto)
  next
    case (middle v w x y)
    from A_only_rrstep_imp_rrstep_ext_trs_middle [OF this(1-3)]
      have "(Bin f (Bin f (Bin f u x) v) y, Bin f (Bin f (Bin f u x) w) y) \<in> rrstep (ext_trs R)" by blast
    then show ?thesis by (rule relcomp3_I) (insert middle, auto simp: aocconv_iff)
  qed
qed simp

lemma actopstep_sym_rrstep_or_ext_trs:
  assumes "(s, t) \<in> actopstep_sym f F\<^sub>A R"
  shows "(s, t) \<in> rrstep R \<or> (s, t) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ"
using assms
proof (induct)
  case (root s t)
  then show ?case by simp
next
  case (Binl s t u)
  then consider "(s, t) \<in> rrstep R" | "(s, t) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ" by auto
  then show ?case
  proof (cases)
    case 1
    with Binl have "(Bin f s u, Bin f t u) \<in> rrstep (ext_trs R)"
      by (auto dest: AC_rrstep_imp_rrstep_ext_trs)
    then show ?thesis by auto
  next
    case 2
    then obtain v and w where aoceq: "(s, v) \<in> AOCEQ" "(w, t) \<in> AOCEQ"
      and "(v, w) \<in> rrstep (ext_trs R)" by auto
    moreover then have "root v = Some (f, 2)"
      using \<open>root s = Some (f, 2)\<close> by (auto dest: AOCEQ_roots)
    moreover have "f \<in> F\<^sub>A \<inter> F\<^sub>C \<or> f \<in> F\<^sub>A - F\<^sub>C" using Binl by blast
    ultimately have "(Bin f v u, Bin f w u) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ"
      by (blast dest: rrstep_ext_trs_imp_rrstep_ext_trs_AOCEQ_AC rrstep_ext_trs_imp_rrstep_ext_trs_AOCEQ_A_only_left)
    then show ?thesis
      by (rule disjI2 [OF relcomp3_transI [OF conversion_trans]])
      (insert aoceq, auto simp: args_acconv_imp_acconv nth_Cons')
  qed
next
  case (Binr s t u)
  then consider "(s, t) \<in> rrstep R" | "(s, t) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ" by auto
  then show ?case
  proof (cases)
    case 1
    consider (AC) "f \<in> F\<^sub>A \<inter> F\<^sub>C" | (A_only) "f \<in> F\<^sub>A - F\<^sub>C" using Binr by blast
    then show ?thesis
    proof (cases)
      case AC
      with 1 and Binr have "(Bin f s u, Bin f t u) \<in> rrstep (ext_trs R)"
        by (auto dest: AC_rrstep_imp_rrstep_ext_trs)
      moreover have "(Bin f u s, Bin f s u) \<in> AOCEQ" and "(Bin f t u, Bin f u t) \<in> AOCEQ"
        using AC by auto
      ultimately show ?thesis by blast
    next
      case A_only
      with 1 and Binr have "(Bin f u s, Bin f u t) \<in> rrstep (ext_trs R)"
        using A_only_rrstep_imp_rrstep_ext_trs_right by auto
      then show ?thesis by auto
    qed
  next
    case 2
    then obtain v and w where aoceq: "(s, v) \<in> AOCEQ" "(w, t) \<in> AOCEQ"
      and vw: "(v, w) \<in> rrstep (ext_trs R)" by auto
    then have root_v: "root v = Some (f, 2)"
      using \<open>root s = Some (f, 2)\<close> by (auto dest: AOCEQ_roots)
    consider (AC) "f \<in> F\<^sub>A \<inter> F\<^sub>C" | (A_only) "f \<in> F\<^sub>A - F\<^sub>C" using Binr by blast
    then show ?thesis
    proof (cases)
      case AC
      with root_v and vw have rrstep: "(Bin f v u, Bin f w u) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ"
        by (auto dest: rrstep_ext_trs_imp_rrstep_ext_trs_AOCEQ_AC)
      moreover have "(Bin f s u, Bin f v u) \<in> AOCEQ"
        and "(Bin f w u, Bin f t u) \<in> AOCEQ"
        using \<open>(s, v) \<in> AOCEQ\<close> and \<open>(w, t) \<in> AOCEQ\<close>
        by (auto simp: args_acconv_imp_acconv nth_Cons')
      ultimately show ?thesis
        by (intro disjI2 [OF relcomp3_transI [OF conversion_trans]])
           (insert AC, auto simp: aocconv_iff ac_simps)
    next
      case A_only
      have "(Bin f u v, Bin f u w) \<in> AOCEQ O rrstep (ext_trs R) O AOCEQ"
        using rrstep_ext_trs_imp_rrstep_ext_trs_AOCEQ_A_right [OF root_v A_only vw] .
      then show ?thesis
        by (rule disjI2 [OF relcomp3_transI [OF conversion_trans]])
           (insert aoceq, auto simp: args_acconv_imp_acconv nth_Cons')
    qed
  qed
qed

end

inductive_set top_ctxts for f
where
  Hole: "\<box> \<in> top_ctxts f"
| Binl: "C \<in> top_ctxts f \<Longrightarrow> More f [] C [t] \<in> top_ctxts f"
| Binr: "C \<in> top_ctxts f \<Longrightarrow> More f [t] C [] \<in> top_ctxts f"

lemma actopstep_sym_cases:
  assumes "(s, t) \<in> actopstep_sym f F R"
  shows "(s, t) \<in> rrstep R \<or>
    (\<exists>u v C. C \<in> top_ctxts f \<and> C \<noteq> \<box> \<and>
    s = C\<langle>u\<rangle> \<and> t = C\<langle>v\<rangle> \<and>
    root u = Some (f, 2) \<and> (u, v) \<in> rrstep R)" (is "_ \<or> (\<exists>u v C. ?P s t u v C)")
using assms
proof (induct)
  case (root s t)
  then show ?case by blast
next
  case (Binl s t u)
  then consider "(s, t) \<in> rrstep R" | v w C where "?P s t v w C" by blast
  then show ?case
  proof (cases)
    define C where "C = More f [] \<box> [u]"
    case 1
    moreover have "C \<noteq> \<box>" and "C \<in> top_ctxts f" by (auto simp: C_def intro: top_ctxts.intros)
    ultimately show ?thesis using Binl
      by (intro disjI2) (rule exI [of _ s], rule exI [of _ t], rule exI [of _ C], auto simp: C_def)
  next
    case (2 v w C)
    moreover define D where "D = More f [] C [u]"
    moreover have "D \<noteq> \<box>" and "D \<in> top_ctxts f"
      using 2 by (auto simp: D_def intro: top_ctxts.intros)
    ultimately show ?thesis
      by (intro disjI2) (rule exI [of _ v], rule exI [of _ w], rule exI [of _ D], simp)
  qed
next
  case (Binr s t u)
  then consider "(s, t) \<in> rrstep R" | v w C where "?P s t v w C" by blast
  then show ?case
  proof (cases)
    define C where "C = More f [u] \<box> []"
    case 1
    moreover have "C \<noteq> \<box>" and "C \<in> top_ctxts f" by (auto simp: C_def intro: top_ctxts.intros)
    ultimately show ?thesis using Binr
      by (intro disjI2) (rule exI [of _ s], rule exI [of _ t], rule exI [of _ C], auto simp: C_def)
  next
    case (2 v w C)
    moreover define D where "D = More f [u] C []"
    moreover have "D \<noteq> \<box>" and "D \<in> top_ctxts f"
      using 2 by (auto simp: D_def intro: top_ctxts.intros)
    ultimately show ?thesis
      by (intro disjI2) (rule exI [of _ v], rule exI [of _ w], rule exI [of _ D], simp)
  qed
qed

lemma top_ctxts_root:
  assumes "C \<in> top_ctxts f" and "C \<noteq> \<box>"
  shows "root (C\<langle>t\<rangle>) = Some (f, 2)"
using assms by (induct) simp_all

lemma top_ctxts_actopstep_symI:
  assumes "C \<in> top_ctxts f"
    and "C \<noteq> \<box>" and "s = C\<langle>u\<rangle>" and "t = C\<langle>v\<rangle>"
    and "f \<in> F"
    and "root u = Some (f, 2)"
    and "(u, v) \<in> rrstep R"
  shows "(s, t) \<in> actopstep_sym f F R"
using assms(1-4)
proof (induct arbitrary: s t)
  case (Binl C w)
  then show ?case
    using assms(5-) by (cases C) (auto dest: top_ctxts_root intro: actopstep_sym.intros)
next
  case (Binr C w)
  then show ?case
    using assms(5-) by (cases C) (auto dest: top_ctxts_root intro: actopstep_sym.intros)
qed simp

lemma actopstep_sym_iff:
  "(s, t) \<in> actopstep_sym f F R \<longleftrightarrow> (s, t) \<in> rrstep R \<or> f \<in> F \<and>
    (\<exists>C u v. C \<noteq> \<box> \<and> C \<in> top_ctxts f \<and> s = C\<langle>u\<rangle> \<and> t = C\<langle>v\<rangle> \<and>
    root u = Some (f, 2) \<and> (u, v) \<in> rrstep R)"
using actopstep_sym_cases [of s t f F R]
  by (auto intro: actopstep_sym.intros top_ctxts_actopstep_symI elim: actopstep_sym.cases)

lemma acnontopstepD:
  assumes "(s, t) \<in> acnontopstep F R"
  shows "\<exists>C u v. C \<noteq> \<box> \<and> s = C\<langle>u\<rangle> \<and> t = C\<langle>v\<rangle> \<and> (u, v) \<in> rrstep R \<and>
    (\<forall>f\<in>F. root u \<noteq> Some (f, 2) \<or> C \<notin> top_ctxts f)"
proof -
  obtain C and u and v where [simp]: "s = C\<langle>u\<rangle>" "t = C\<langle>v\<rangle>" and "(u, v) \<in> rrstep R"
    and *: "\<And>f. (s, t) \<notin> actopstep_sym f F R"
    using assms by (auto simp: acnontopstep_def actopstep_def elim!: rstepE)
  moreover then have "C \<noteq> \<box>" by (auto simp: actopstep_sym.root)
  moreover
  { fix f assume "f \<in> F" and "root u = Some (f, 2)" and "C \<in> top_ctxts f"
    then have False
      using * [of f] and \<open>C \<noteq> \<box>\<close> and \<open>(u, v)\<in> rrstep R\<close> by (auto simp: actopstep_sym_iff) }
  ultimately show ?thesis by blast
qed

lemma actop_not_empty [simp]: "actop f t \<noteq> {#}"
by (induct f t rule: actop.induct) simp_all

lemma actop_singleton_iff:
  "actop f u = {#u#} \<longleftrightarrow> root u \<noteq> Some (f, 2)"
by (cases "(f, u)" rule: actop.cases) (auto simp: non_empty_plus_non_empty_not_single)

lemma not_top_ctxts_actops:
  assumes "C \<notin> top_ctxts f" and "s = C\<langle>u\<rangle>" and "t = C\<langle>v\<rangle>"
  shows "actop f s = {#s#} \<and> actop f t = {#t#} \<or>
    (\<exists>D M. M \<noteq> {#} \<and> actop f s = {#D\<langle>u\<rangle>#} + M \<and> actop f (D\<langle>u\<rangle>) = {#D\<langle>u\<rangle>#} \<and>
      actop f t = {#D\<langle>v\<rangle>#} + M \<and> actop f (D\<langle>v\<rangle>) = {#D\<langle>v\<rangle>#} \<and>
      s \<rhd> D\<langle>u\<rangle> \<and> t \<rhd> D\<langle>v\<rangle>)"
using assms
proof (induct C arbitrary: s t)
  case Hole
  then show ?case by (auto intro: top_ctxts.intros)
next
  case (More g ss C ts)
  then consider s' where "ss = [s']" and "ts = []" | t' where "ss = []" and "ts = [t']" |
    "\<And>u v. s \<noteq> Bin g u v" and "\<And>u v. t \<noteq> Bin g u v"
    using Bin_cases [of s] and Bin_cases [of t]
    by (metis (no_types, lifting) actxt.distinct(1) actxt.inject ctxt_apply_term_Bin_cases)
  then show ?case
  proof (cases)
    case [simp]: 1
    show ?thesis
    proof (cases "C \<in> top_ctxts f")
      case True
      with More show ?thesis by (auto intro: top_ctxts.intros)
    next
      case False
      from More(1) [OF this refl refl]
        consider (A) "actop f C\<langle>u\<rangle> = {#C\<langle>u\<rangle>#}" and "actop f (C\<langle>v\<rangle>) = {#C\<langle>v\<rangle>#}"
        | (B) D M where "M \<noteq> {#}" and "actop f (C\<langle>u\<rangle>) = {#D\<langle>u\<rangle>#} + M" and "actop f (D\<langle>u\<rangle>) = {#D\<langle>u\<rangle>#}"
          and "actop f (C\<langle>v\<rangle>) = {#D\<langle>v\<rangle>#} + M" and "actop f (D\<langle>v\<rangle>) = {#D\<langle>v\<rangle>#}"
          and "C\<langle>u\<rangle> \<rhd> D\<langle>u\<rangle>" and "C\<langle>v\<rangle> \<rhd> D\<langle>v\<rangle>" by auto
      then show ?thesis
      proof (cases)
        case A then show ?thesis unfolding More actop_singleton_iff
          apply (auto simp: A)
          apply (rule exI [of _ C], rule exI [of _ "actop f s'"]) apply auto
          done
      next
        case B then show ?thesis unfolding More actop_singleton_iff
        apply (auto simp: B)
        apply (rule exI [of _ "D"], rule exI [of _ "actop f s' + M"])
        using B apply (auto simp: ac_simps)
        done
      qed
    qed
  next
    case [simp]: 2
    show ?thesis
    proof (cases "C \<in> top_ctxts f")
      case True
      with More show ?thesis by (auto intro: top_ctxts.intros)
    next
      case False
      from More(1) [OF this refl refl]
        consider (A) "actop f C\<langle>u\<rangle> = {#C\<langle>u\<rangle>#}" and "actop f (C\<langle>v\<rangle>) = {#C\<langle>v\<rangle>#}"
        | (B) D M where "M \<noteq> {#}" and "actop f (C\<langle>u\<rangle>) = {#D\<langle>u\<rangle>#} + M" and "actop f (D\<langle>u\<rangle>) = {#D\<langle>u\<rangle>#}"
          and "actop f (C\<langle>v\<rangle>) = {#D\<langle>v\<rangle>#} + M" and "actop f (D\<langle>v\<rangle>) = {#D\<langle>v\<rangle>#}"
          and "C\<langle>u\<rangle> \<rhd> D\<langle>u\<rangle>" and "C\<langle>v\<rangle> \<rhd> D\<langle>v\<rangle>" by auto
      then show ?thesis
      proof (cases)
        case A then show ?thesis unfolding More actop_singleton_iff
          apply (auto simp: A)
          apply (rule exI [of _ C], rule exI [of _ "actop f t'"]) apply auto
          done
      next
        case B then show ?thesis unfolding More actop_singleton_iff
        apply (auto simp: B)
        apply (rule exI [of _ "D"], rule exI [of _ "actop f t' + M"])
        using B apply (auto simp: ac_simps)
        done
      qed
    qed
  next
    case 3
    with More show ?thesis by auto
  qed
qed

fun actop_ctxt
where
  "actop_ctxt f Hole = {#}"
| "actop_ctxt f (More g ss C ts) =
    (if f = g \<and> length ss + length ts = 1 then
      \<Sum>\<^sub># (mset (map (actop f) (ss @ ts))) + actop_ctxt f C
    else {#})"

lemma top_ctxts_actop_apply_ctxt [simp]:
  assumes "C \<in> top_ctxts f"
  shows "actop f (C\<langle>t\<rangle>) = actop_ctxt f C + actop f t"
using assms by (induct C) (auto simp: ac_simps)

lemma not_AC_actop [simp]:
  assumes "root t \<noteq> Some (f, 2)"
  shows "actop f t = {#t#}"
using assms by (cases "(f, t)" rule: actop.cases) auto

fun nabla ("\<nabla>")
where
  "\<nabla> F (Fun f ts) = (if f \<in> F \<and> length ts = 2 then actop f (Fun f ts) else mset ts)"
| "\<nabla> F (Var x) = {#}"

lemma actop_subteq:
  assumes "s \<in># actop f t"
  shows "s \<unlhd> t"
using assms by (induct t rule: bterm_induct) (auto split: if_splits)

lemma actop_subt:
  assumes "t = Fun f ts" "s \<in># actop f t" "length ts = 2"
  shows "s \<lhd> t"
proof -
  from assms obtain t1 t2 where ts: "ts = [t1,t2]" by (cases ts; cases "tl ts"; auto)
  then have "s \<in># actop f t1 \<or> s \<in># actop f t2" using assms by auto
  with actop_subteq[of s f _] consider "t1 \<unrhd> s" | "t2 \<unrhd> s" by auto
  then show ?thesis unfolding assms(1) ts
    by (cases, auto intro: set_supteq_into_supt) 
qed

lemma nabla_subt:
  assumes "s \<in># \<nabla> F t"
  shows "s \<lhd> t"
proof (cases t)
  case Var then show ?thesis using assms by auto
next case (Fun f ts)
  show ?thesis
  proof (cases "f \<in> F \<and> length ts = 2")
    case True
      with actop_subt[OF Fun, of s] assms
      show ?thesis unfolding Fun by auto
  next case False
    with assms show ?thesis unfolding Fun by force
  qed
qed

lemma non_ac_term_acnontopstepE:
  assumes "(s, t) \<in> acnontopstep F R" and "\<forall>f\<in>F. root s \<noteq> Some (f, 2)"
  obtains u v M where "(u, v) \<in> rstep R" and "\<nabla> F s = {#u#} + M" and "\<nabla> F t = {#v#} + M"
    and "s \<rhd> u" and "t \<rhd> v"
proof -
  obtain f and n where roots: "root s = Some (f, n)" "root t = Some (f, n)"
    using assms by (auto dest: acnontopstep_eq_roots)
  then have "\<not> (f \<in> F \<and> n = 2)" using assms by auto
  then have [simp]: "\<nabla> F s = mset (args s) \<and> \<nabla> F t = mset (args t)"
      using roots by (cases s; cases t) auto
  have nrrstep: "(s, t) \<in> nrrstep R"
    using assms by (auto simp: acnontopstep_def actopstep_def elim!: rstep_cases intro: actopstep_sym.intros)
  moreover then obtain i where i: "i < length (args s)" and "(args s ! i, args t ! i) \<in> rstep R"
    and args_t: "(args s) [i := args t ! i] = args t" and "length (args t) = length (args s)"
    by (auto simp: nrrstep_iff_arg_rstep)
  moreover then have "s \<rhd> args s ! i" and "t \<rhd> args t ! i"
    using nrrstep by (auto dest!: nrrstep_equiv_root)
  moreover have "mset (take i (args s) @ args s ! i # drop (Suc i) (args s)) = mset (args s)"
    unfolding id_take_nth_drop [OF i, symmetric] ..
  moreover have "mset (take i (args s) @ args t ! i # drop (Suc i) (args s)) = mset (args t)"
  proof -
    have *: "i < length ((args s) [i := args t ! i])" using i by simp
    show ?thesis using id_take_nth_drop[OF *, symmetric] and i by (simp) (metis args_t)
  qed
  ultimately have "\<exists>u v M. (u, v) \<in> rstep R \<and> \<nabla> F s = {#u#} + M \<and> \<nabla> F t = {#v#} + M \<and> s \<rhd> u \<and> t \<rhd> v"
    using assms and roots
    apply (subst exI [of _ "args s ! i"], subst exI [of _ "args t ! i"])
    apply (rule exI [of _ "mset (take i (args s) @ drop (Suc i) (args s))"])
    apply (auto simp: actop_singleton_iff acnontopstep_def actopstep_def ac_simps)
    done
  then show ?thesis using that by blast
qed

lemma ac_term_acnontopstepE:
  assumes st: "(s, t) \<in> acnontopstep F R" and "root s = Some (f, 2)" and "f \<in> F"
  obtains
   (nonroot) u v M where "(u, v) \<in> rstep R" and "\<nabla> F s = {#u#} + M" and "actop f u = {#u#}"
    and "\<nabla> F t = {#v#} + M \<and> actop f v = {#v#} \<or> \<nabla> F t = actop f v + M"
    and "s \<rhd> u" and "t \<rhd> v"
proof -
  have roots: "root s = Some (f, 2)" "root t = Some (f, 2)"
    using assms by (auto dest: acnontopstep_eq_roots)
  then have [simp]: "f \<in> F" and *: "\<nabla> F s = actop f s" "\<nabla> F t = actop f t"
    using assms by (cases s; cases t; simp)+
  from acnontopstepD [OF assms(1)] obtain C and u and v
    where C: "C \<noteq> \<box>" and [simp]: "s = C\<langle>u\<rangle>" "t = C\<langle>v\<rangle>"
    and uv: "(u, v) \<in> rrstep R"
    and "root u \<noteq> Some (f, 2) \<or> C \<notin> top_ctxts f"
    using assms by blast
  then consider "C \<in> top_ctxts f" and "root u \<noteq> Some (f, 2)" | "C \<notin> top_ctxts f" by auto
  then have "(\<exists>u v M. (u, v) \<in> rstep R \<and>
     \<nabla> F s = {#u#} + M \<and> actop f u = {#u#} \<and>
    (\<nabla> F t = {#v#} + M \<and> actop f v = {#v#} \<or> \<nabla> F t = actop f v + M) \<and> s \<rhd> u \<and> t \<rhd> v)"
  proof (cases)
    case 2
    from not_top_ctxts_actops [OF this, of s u t v]
      consider (A) "actop f s = {#s#}" and "actop f t = {#t#}"
      | (B) D M where "M \<noteq> {#}" and "actop f s = {#D\<langle>u\<rangle>#} + M" and "actop f (D\<langle>u\<rangle>) = {#D\<langle>u\<rangle>#}"
      and "actop f t = {#D\<langle>v\<rangle>#} + M" and "actop f (D\<langle>v\<rangle>) = {#D\<langle>v\<rangle>#}"
      and "s \<rhd> D\<langle>u\<rangle>" and "t \<rhd> D\<langle>v\<rangle>" by auto
    then show ?thesis
    proof (cases)
      case A then show ?thesis
        using rrstep_imp_rstep [OF uv] and roots by (auto simp: actop_singleton_iff)
    next
      case B
      then show ?thesis
        using rrstep_imp_rstep [OF uv] unfolding *
        by (subst exI[of _ "D\<langle>u\<rangle>"], subst exI[of _ "D\<langle>v\<rangle>"], subst exI[of _ M]) auto
     qed
  next
    case 1
    show ?thesis
    proof (cases "root v = Some (f, 2)")
      case False
      with 1 have "actop f s = {#u#} + actop_ctxt f C" and "actop f u = {#u#}"
        and "actop f t = {#v#} + actop_ctxt f C" and "actop f v = {#v#}" by auto
      then show ?thesis
        using rrstep_imp_rstep [OF uv] C unfolding * by auto
    next
      case True
      then have [simp]: "\<nabla> F v = actop f v" by (cases "(f, v)" rule: actop.cases) auto
      have "actop f s = {#u#} + actop_ctxt f C" and "actop f u = {#u#}"
        and "actop f t = actop f v + actop_ctxt f C" using 1 by (auto simp: ac_simps)
      moreover have "\<forall>x\<in>set_mset (actop f v). x \<unlhd> v" by (auto simp: actop_subteq)
      ultimately show ?thesis
        using rrstep_imp_rstep[OF uv] C unfolding * by auto
    qed
  qed
  then show ?thesis using that by blast
qed

lemma acnontopstep_cases [consumes 1]:
  assumes "(s, t) \<in> acnontopstep F R"
  obtains (nonac) u v M where "\<forall>f\<in>F. root s \<noteq> Some (f, 2)"
    and "(u, v) \<in> rstep R" and "\<nabla> F s = {#u#} + M" and "\<nabla> F t = {#v#} + M" and "s \<rhd> u" and "t \<rhd> v"
  | (ac) u v M f where "root s = Some (f, 2)" and "f \<in> F" and "(u, v) \<in> rstep R"
    and "\<nabla> F s = {#u#} + M" and "actop f u = {#u#}"
    and "\<nabla> F t = {#v#} + M \<and> actop f v = {#v#} \<or> \<nabla> F t = actop f v + M" and "s \<rhd> u" and "t \<rhd> v"
using non_ac_term_acnontopstepE [OF assms, of thesis]
  and ac_term_acnontopstepE [OF assms, of _ thesis] by auto

lemma restrict_Un[simp]: "(R\<union>S)\<restriction>X = R\<restriction>X \<union> S\<restriction>X" by auto

lemma restrict_id[simp]: "R\<restriction>X\<restriction>X = R\<restriction>X" by auto

lemma restrict_mono: "R' \<subseteq> R \<Longrightarrow> R'\<restriction>X \<subseteq> R\<restriction>X" by auto

lemma restrict_relpow_Suc[simp]: "((R\<restriction>X)^^Suc n)\<restriction>X = (R\<restriction>X)^^Suc n" by (induct n, auto simp: relpow_Suc)

lemma restrict_trancl_id[simp]: "(R\<restriction>X)\<^sup>+\<restriction>X = (R\<restriction>X)\<^sup>+"
proof(intro equalityI subrelI,force)
  fix x y
  assume "(x,y) \<in> (R\<restriction>X)\<^sup>+"
  then obtain n where "n > 0" "(x,y) \<in> (R\<restriction>X)^^n" by (unfold trancl_power, auto)
  then obtain n' where "(x,y) \<in> (R\<restriction>X)^^Suc n'" by (cases n, auto)
  then have "(x,y) \<in> ((R\<restriction>X)^^Suc n')\<restriction>X" unfolding restrict_relpow_Suc.
  then show "(x,y) \<in> (R\<restriction>X)\<^sup>+\<restriction>X" by (rule subsetD[OF restrict_mono[OF pow_Suc_subset_trancl]])
qed

lemma restrict_O_id[simp]: "(R\<restriction>X O S\<restriction>X)\<restriction>X = R\<restriction>X O S\<restriction>X" by auto

lemma restrict_trancl_O_id[simp]: "((R\<restriction>X)\<^sup>+ O S\<restriction>X)\<restriction>X = (R\<restriction>X)\<^sup>+ O S\<restriction>X"
  by (subst restrict_trancl_id[symmetric], unfold restrict_O_id, simp)

lemma SN_rel_ext_trans:(* TODO: almost clone *)
  fixes P Pw R Rw :: "'a rel" and M :: "'a \<Rightarrow> bool"
  defines A: "A \<equiv> (P \<union> Pw \<union> R \<union> Rw) \<restriction> Collect M"
  assumes "SN_rel_ext P Pw R Rw M" 
  shows "SN_rel_ext (A^* O (P \<restriction> Collect M) O A^*) (A^* O ((P \<union> Pw) \<restriction> Collect M) O A^*) (A^* O ((P \<union> R) \<restriction> Collect M) O A^*) (A^*) M" (is "SN_rel_ext ?P ?Pw ?R ?Rw M")
proof (rule ccontr)
  let ?relt = "SN_rel_ext_step ?P ?Pw ?R ?Rw"
  let ?rel = "SN_rel_ext_step P Pw R Rw" 
  assume "\<not> ?thesis"
  from this[unfolded SN_rel_ext_def]
  obtain f ty
    where steps: "\<And> i. (f i, f (Suc i)) \<in> ?relt (ty i)" 
    and min: "\<And> i. M (f i)"
    and inf1: "INFM i. ty i \<in> {top_s, top_ns}"
    and inf2: "INFM i. ty i \<in> {top_s, normal_s}"
    by auto
  let ?Un = "\<lambda> tt. \<Union> (?rel ` tt)"
  let ?UnM = "\<lambda> tt. (\<Union> (?rel ` tt)) \<restriction> Collect M"
  let ?A = "?UnM {top_s,top_ns,normal_s,normal_ns}"
  let ?P' = "?UnM {top_s}"
  let ?Pw' = "?UnM {top_s,top_ns}"
  let ?R' = "?UnM {top_s,normal_s}"
  let ?Rw' = "?UnM {top_s,top_ns,normal_s,normal_ns}"
  have A: "A = ?A" unfolding A by auto
  have P: "(P \<restriction> Collect M) = ?P'" by auto
  have Pw: "(P \<union> Pw) \<restriction> Collect M = ?Pw'" by auto
  have R: "(P \<union> R) \<restriction> Collect M = ?R'" by auto
  have Rw: "A = ?Rw'" unfolding A ..
  {
    fix s t tt
    assume m: "M s" and st: "(s,t) \<in> ?UnM tt"
    then have "\<exists> typ \<in> tt. (s,t) \<in> ?rel typ \<and> M s \<and> M t" by auto
  } note one_step = this
  let ?seq = "\<lambda> s t g n ty. s = g 0 \<and> t = g n \<and> (\<forall> i < n. (g i, g (Suc i)) \<in> ?rel (ty i)) \<and> (\<forall> i \<le> n. M (g i))"
  {
    fix s t
    assume m: "M s" and st: "(s,t) \<in> A^*"
    from st[unfolded rtrancl_fun_conv]
    obtain g n where g0: "g 0 = s" and gn: "g n = t" and steps: "\<And> i. i < n \<Longrightarrow> (g i, g (Suc i)) \<in> ?A" unfolding A by auto
    {
      fix i
      assume "i \<le> n"
      have "M (g i)"
      proof (cases i)
        case 0
        show ?thesis unfolding 0 g0 by (rule m)
      next
        case (Suc j)
        with \<open>i \<le> n\<close> have "j < n" by auto
        from steps[OF this] show ?thesis unfolding Suc by auto
      qed
    } note min = this
    {
      fix i
      assume i: "i < n" then have i': "i \<le> n" by auto
      from i' one_step[OF min steps[OF i]]
      have "\<exists> ty. (g i, g (Suc i)) \<in> ?rel ty" by blast
    }
    then have "\<forall> i. (\<exists> ty. i < n \<longrightarrow> (g i, g (Suc i)) \<in> ?rel ty)" by auto
    from choice[OF this]
    obtain tt where steps: "\<And> i. i < n \<Longrightarrow> (g i, g (Suc i)) \<in> ?rel (tt i)" by auto
    from g0 gn steps min
    have "?seq s t g n tt" by auto
    then have "\<exists> g n tt. ?seq s t g n tt" by blast
  } note A_steps = this
  let ?seqtt = "\<lambda> s t tt g n ty. s = g 0 \<and> t = g n \<and> n > 0 \<and> (\<forall> i<n. (g i, g (Suc i)) \<in> ?rel (ty i)) \<and> (\<forall> i \<le> n. M (g i)) \<and> (\<exists> i < n. ty i \<in> tt)"
  {
    fix s t tt
    assume m: "M s" and st: "(s,t) \<in> A^* O ?UnM tt O A^*"
    then obtain u v where su: "(s,u) \<in> A^*" and uv: "(u,v) \<in> ?UnM tt" and vt: "(v,t) \<in> A^*"
      by auto
    from A_steps[OF m su] obtain g1 n1 ty1 where seq1: "?seq s u g1 n1 ty1" by auto
    from uv have "M v" by auto
    from A_steps[OF this vt] obtain g2 n2 ty2 where seq2: "?seq v t g2 n2 ty2" by auto
    from seq1 have "M u" by auto
    from one_step[OF this uv] obtain ty where ty: "ty \<in> tt" and uv: "(u,v) \<in> ?rel ty" by auto
    let ?g = "\<lambda> i. if i \<le> n1 then g1 i else g2 (i - (Suc n1))"
    let ?ty = "\<lambda> i. if i < n1 then ty1 i else if i = n1 then ty else ty2 (i - (Suc n1))"
    let ?n = "Suc (n1 + n2)"
    have ex: "\<exists> i < ?n. ?ty i \<in> tt"
      by (rule exI[of _ n1], simp add: ty)
    have steps: "\<forall> i < ?n. (?g i, ?g (Suc i)) \<in> ?rel (?ty i)"
    proof (intro allI impI)
      fix i
      assume "i < ?n"
      show "(?g i, ?g (Suc i)) \<in> ?rel (?ty i)"
      proof (cases "i \<le> n1")
        case True
        with seq1 seq2 uv show ?thesis by auto
      next
        case False
        then have "i = Suc n1 + (i - Suc n1)" by auto
        then obtain k where i: "i = Suc n1 + k" by auto
        with \<open>i < ?n\<close> have "k < n2" by auto
        then show ?thesis using seq2 unfolding i by auto
      qed
    qed
    from steps seq1 seq2 ex 
    have seq: "?seqtt s t tt ?g ?n ?ty" by auto
    have "\<exists> g n ty. ?seqtt s t tt g n ty" 
      by (intro exI, rule seq)
  } note A_tt_A = this
  let ?tycon = "\<lambda> ty1 ty2 tt ty' n. ty1 = ty2 \<longrightarrow> (\<exists>i < n. ty' i \<in> tt)"
  let ?seqt = "\<lambda> i ty g n ty'. f i = g 0 \<and> f (Suc i) = g n \<and> (\<forall> j < n. (g j, g (Suc j)) \<in> ?rel (ty' j)) \<and> (\<forall> j \<le> n. M (g j)) 
                \<and> (?tycon (ty i) top_s {top_s} ty' n)
                \<and> (?tycon (ty i) top_ns {top_s,top_ns} ty' n)
                \<and> (?tycon (ty i) normal_s {top_s,normal_s} ty' n)"
  {
    fix i
    have "\<exists> g n ty'. ?seqt i ty g n ty'"
    proof (cases "ty i")
      case top_s
      from steps[of i, unfolded top_s] 
      have "(f i, f (Suc i)) \<in> ?P" by auto
      from A_tt_A[OF min this[unfolded P]]
      show ?thesis unfolding top_s by auto
    next
      case top_ns
      from steps[of i, unfolded top_ns] 
      have "(f i, f (Suc i)) \<in> ?Pw" by auto
      from A_tt_A[OF min this[unfolded Pw]]
      show ?thesis unfolding top_ns by auto
    next
      case normal_s
      from steps[of i, unfolded normal_s] 
      have "(f i, f (Suc i)) \<in> ?R" by auto
      from A_tt_A[OF min this[unfolded R]]
      show ?thesis unfolding normal_s by auto
    next
      case normal_ns
      from steps[of i, unfolded normal_ns] 
      have "(f i, f (Suc i)) \<in> ?Rw" by auto
      from A_steps[OF min this]
      show ?thesis unfolding normal_ns by auto
    qed
  }
  then have "\<forall> i. \<exists> g n ty'. ?seqt i ty g n ty'" by auto
  from choice[OF this] obtain g where "\<forall> i. \<exists> n ty'. ?seqt i ty (g i) n ty'" by auto
  from choice[OF this] obtain n where "\<forall> i. \<exists> ty'. ?seqt i ty (g i) (n i) ty'" by auto
  from choice[OF this] obtain ty' where "\<forall> i. ?seqt i ty (g i) (n i) (ty' i)" by auto
  then have partial: "\<And> i. ?seqt i ty (g i) (n i) (ty' i)" ..
  (* it remains to concatenate all these finite sequences to an infinite one *)
  let ?ind = "inf_concat n"
  let ?g = "\<lambda> k. (\<lambda> (i,j). g i j) (?ind k)"
  let ?ty = "\<lambda> k. (\<lambda> (i,j). ty' i j) (?ind k)"
  have inf: "INFM i. 0 < n i"
    unfolding INFM_nat_le
  proof (intro allI)
    fix m
    from inf1[unfolded INFM_nat_le]
    obtain k where k: "k \<ge> m" and ty: "ty k \<in> {top_s, top_ns}" by auto
    show "\<exists> k \<ge> m. 0 < n k"
    proof (intro exI conjI, rule k)
      from partial[of k] ty show "0 < n k" by (cases "n k", auto)
    qed
  qed
  note bounds = inf_concat_bounds[OF inf]
  note inf_Suc = inf_concat_Suc[OF inf]
  note inf_mono = inf_concat_mono[OF inf]
  have "\<not> SN_rel_ext P Pw R Rw M"
    unfolding SN_rel_ext_def simp_thms
  proof (rule exI[of _ ?g], rule exI[of _ ?ty], intro conjI allI)
    fix k
    obtain i j where ik: "?ind k = (i,j)" by force
    from bounds[OF this] have j: "j < n i" by auto
    show "M (?g k)" unfolding ik using partial[of i] j by auto
  next
    fix k
    obtain i j where ik: "?ind k = (i,j)" by force
    from bounds[OF this] have j: "j < n i" by auto
    from partial[of i] j have step: "(g i j, g i (Suc j)) \<in> ?rel (ty' i j)" by auto
    obtain i' j' where isk: "?ind (Suc k) = (i',j')" by force
    have i'j': "g i' j' = g i (Suc j)"
    proof (rule inf_Suc[OF _ ik isk])
      fix i
      from partial[of i]
      have "g i (n i) = f (Suc i)" by simp
      also have "... = g (Suc i) 0" using partial[of "Suc i"] by simp
      finally show "g i (n i) = g (Suc i) 0" .
    qed
    show "(?g k, ?g (Suc k)) \<in> ?rel (?ty k)"
      unfolding ik isk split i'j'
      by (rule step)
  next
    show "INFM i. ?ty i \<in> {top_s, top_ns}"
      unfolding INFM_nat_le
    proof (intro allI)
      fix k
      obtain i j where ik: "?ind k = (i,j)" by force
      from inf1[unfolded INFM_nat] obtain i' where i': "i' > i" and ty: "ty i' \<in> {top_s, top_ns}" by auto
      from partial[of i'] ty obtain j' where j': "j' < n i'" and ty': "ty' i' j' \<in> {top_s, top_ns}" by auto
      from inf_concat_surj[of _ n, OF j'] obtain k' where ik': "?ind k' = (i',j')" ..
      from inf_mono[OF ik ik' i'] have k: "k \<le> k'" by simp
      show "\<exists> k' \<ge> k. ?ty k' \<in> {top_s, top_ns}"
        by (intro exI conjI, rule k, unfold ik' split, rule ty')
    qed
  next
    show "INFM i. ?ty i \<in> {top_s, normal_s}"
      unfolding INFM_nat_le
    proof (intro allI)
      fix k
      obtain i j where ik: "?ind k = (i,j)" by force
      from inf2[unfolded INFM_nat] obtain i' where i': "i' > i" and ty: "ty i' \<in> {top_s, normal_s}" by auto
      from partial[of i'] ty obtain j' where j': "j' < n i'" and ty': "ty' i' j' \<in> {top_s, normal_s}" by auto
      from inf_concat_surj[of _ n, OF j'] obtain k' where ik': "?ind k' = (i',j')" ..
      from inf_mono[OF ik ik' i'] have k: "k \<le> k'" by simp
      show "\<exists> k' \<ge> k. ?ty k' \<in> {top_s, normal_s}"
        by (intro exI conjI, rule k, unfold ik' split, rule ty')
    qed
  qed
  with assms show False by auto
qed

context relative_dp
begin

context
  fixes F\<^sub>A F\<^sub>C :: "'f set"
  assumes AC_C_E: "AC_C_theory E (F\<^sub>C - F\<^sub>A)"
  and EF: "funs_trs E \<subseteq> F\<^sub>A \<union> F\<^sub>C"
begin

private abbreviation "ST \<equiv> { s. \<forall> s' \<lhd> s. SN_on (relstep R E) {s'} }"

private abbreviation "po2s \<equiv> (relto (rstep R \<restriction> M \<union> {\<rhd>} \<restriction> M) (rstep E \<restriction> M))\<^sup>+"
private abbreviation "po2w \<equiv> (rstep R \<restriction> M \<union> {\<rhd>} \<restriction> M \<union> rstep E \<restriction> M)\<^sup>*"

interpretation AC_theory E using AC_C_E unfolding AC_C_theory_def ..

interpretation po2: SN_order_pair po2s po2w
proof
  let ?T = "{t. SN_on (relstep R E) {t}}"
  interpret E_compatible "relstep R E" "(rstep E)\<^sup>*"
    by (standard, auto)
  have "SN_on (relstep R E \<union> (relto {\<rhd>} (rstep E))) ?T"
    by (rule ctxt_closed_imp_SN_on_E_supt[OF _ SN_supt_relto], auto)
  then have "SN_on ((rstep E)\<^sup>* O (rstep R \<union> {\<rhd>})) ?T" by (rule SN_on_mono) regexp
  then have "SN_on ((rstep E \<restriction> M)\<^sup>* O ((rstep R \<union> {\<rhd>}) \<restriction> M)) ?T"
    apply (rule SN_on_mono) apply(rule relcomp_mono, rule rtrancl_mono, auto) done
  from SN_on_imp_SN_restrict[OF this, unfolded mem_Collect_eq, folded M_def]
  have "SN ((rstep E \<restriction> M)\<^sup>* O (rstep R \<restriction> M \<union> {\<rhd>} \<restriction> M))"
    apply(rule SN_on_mono)
    unfolding rtrancl_trancl_reflcl relcomp_distrib2 Id_O_R restrict_Un by simp
  then show "SN po2s"
    unfolding SN_on_trancl_SN_on_conv
    unfolding SN_on_relto_relcomp.
qed

context
  fixes Q :: "('f, 'v) trs"
begin
private definition "M' \<equiv> \<lambda>s. SN_on (relstep R E) {s}"
private abbreviation "po3w P \<equiv> (minstep (P \<union> Q) \<union> rstep (R \<union> E))\<^sup>*"
private abbreviation "po3s P \<equiv> (relto (minstep P) (minstep Q \<union> rstep (R \<union> E)))\<^sup>+"

lemma minstep_union: "minstep (P \<union> Q) = minstep P \<union> minstep Q"
  unfolding rrstep_union by auto

interpretation po3: order_pair "po3s P" "po3w P"
  unfolding minstep_union rstep_union
  by (standard, unfold trans_O_iff refl_O_iff, regexp+)

private lemma po3: assumes fin: "weakly_finite P Q R E"
  shows "SN_order_pair (po3s P) (po3w P)"
proof 
  let ?R = "relto (minstep P) (minstep Q \<union> rstep (R \<union> E))"
  show "SN (po3s P)" unfolding SN_trancl_SN_conv
  proof
    fix f
    assume f: "\<forall> i. (f i, f (Suc i)) \<in> ?R"
    define g where "g = (\<lambda> i. f (Suc i))"
    have g: "\<And> i. (g i, g (Suc i)) \<in> ?R" using f unfolding g_def by blast
    from weakly_finite_imp_SN_rel_ext[OF fin]
    have SN: "SN_rel_ext (rrstep P) (rrstep Q) {} (rstep (R \<union> E)) M'" unfolding M'_def by auto
    let ?P = "rrstep P" let ?Pw = "rrstep Q" let ?R = "{}" let ?Rw = "rstep (R \<union> E)"
    define A where "A = ?P \<union> ?Pw \<union> ?R \<union> ?Rw"
    let ?A = "A \<restriction> M"
    from SN_rel_ext_trans[OF SN, unfolded M'_def, folded A_def M_def, folded M'_def]
    have SN: "SN_rel_ext (relto (?P\<restriction>M) ?A) (relto ((?P \<union> ?Pw)\<restriction>M) ?A)
       (relto (?P\<restriction>M) ?A) (?A\<^sup>*) M'" (is ?SN) by auto
    {
      fix s t
      assume s: "M' s" and st: "(s,t) \<in> (?Pw\<restriction>M \<union> ?Rw)\<^sup>*"
      from st have "M' t \<and> (s,t) \<in> ?A\<^sup>*"
      proof (induct rule: rtrancl_induct)
        case (step t u)
        from step(2) have u: "M' u"
        proof
          assume "(t,u) \<in> rstep (R \<union> E)"
          then have "(t,u) \<in> (rstep R \<union> rstep E)\<^sup>*" by auto
          from steps_preserve_SN_on_relto[OF this] step(3)
          show ?thesis unfolding M'_def by auto
        qed (auto simp: M_def M'_def)
        from step(2,3) u have "(t,u) \<in> ?A" unfolding A_def M_def M'_def rstep_union by auto
        with u step(3) show ?case by (meson rtrancl.rtrancl_into_rtrancl)
      qed (insert s, auto)
    } note SN_steps = this
    {
      fix i
      from f obtain s where "M' s" and "(s,f (Suc i)) \<in> (?Pw \<restriction> M \<union> ?Rw)\<^sup>*"
        unfolding M_def M'_def by auto
      from SN_steps[OF this]
      have "M' (g i)" unfolding g_def by auto
    } note Mg = this
    {
      fix i
      from g[of i] obtain s t where gs: "(g i, s) \<in> (?Pw \<restriction> M \<union> ?Rw)\<^sup>*" and st: "(s,t) \<in> ?P \<restriction> M"
        and tg: "(t, g (Suc i)) \<in> (?Pw \<restriction> M \<union> ?Rw)\<^sup>*" by auto
      from Mg have g: "M' (g i)" .
      from st have t: "M' t" unfolding M_def M'_def by auto
      from SN_steps[OF g gs] st SN_steps[OF t tg]
      have "(g i, g (Suc i)) \<in> relto (?P \<restriction> M) ?A" by auto
    } note steps = this
    have "\<not> ?SN" unfolding SN_rel_ext_def not_not
      by (rule exI[of _ g], rule exI[of _ "\<lambda> _. top_s"], intro conjI allI, auto simp: Mg steps)
    with SN show False by simp
  qed
qed

lemma acnontopstep_mul_ext:
  assumes "s \<in> ST"
  shows "(s, t) \<in> acnontopstep F R \<Longrightarrow> (\<nabla> F s, \<nabla> F t) \<in> s_mul_ext po2w po2s" (is "_ \<Longrightarrow> _ \<in> ?S")
    and "(s, t) \<in> acnontopstep F E \<Longrightarrow> (\<nabla> F s, \<nabla> F t) \<in> ns_mul_ext po2w po2s" (is "_ \<Longrightarrow> _ \<in> ?NS")
proof -
  assume nontop: "(s, t) \<in> acnontopstep F R"
  then obtain f and n where roots: "root s = Some (f, n)" "root t = Some (f, n)"
    by (auto dest: acnontopstep_eq_roots)
  with nontop obtain u v N where rstep: "(u, v) \<in> rstep R" and s: "\<nabla> F s = N + {#u#}"
    and "\<nabla> F t = N + {#v#} \<or> \<nabla> F t = N + actop f v" and "s \<rhd> u"
    by (cases rule: acnontopstep_cases) (auto simp: ac_simps)
  then consider "\<nabla> F t = N + {#v#}" | "\<nabla> F t = N + actop f v" by blast
  note * = this
  have "SN_on (relstep R E) {v}"
    using assms and \<open>s \<rhd> u\<close> and rstep and step_preserves_SN_on_relto [of u v "rstep R" "rstep E"] by auto
  moreover from \<open>s \<rhd> u\<close> \<open>s \<in> ST\<close> have uM: "u \<in> M" by (auto simp: M_def)
  ultimately have vM: "v \<in> M" and strict: "(u, v) \<in> po2s"
    using rstep by (auto simp: M_def)
  have N: "(N, N) \<in> ?NS" by (rule ns_mul_ext_refl_local) (auto simp: locally_refl_def)
  show "(\<nabla> F s, \<nabla> F t) \<in> ?S" using *
  proof (cases)
    case t: 1
    show ?thesis
      using strict unfolding s and t by (intro ns_s_mul_ext_union_multiset_l [OF N]) auto
  next
    case t: 2
    { fix y assume "v \<rhd> y"
      moreover from  subterm_preserves_SN_rel[OF _ this] vM have "y \<in> M" by (auto simp: M_def)
      ultimately have "(v, y) \<in> relto (rstep R \<restriction> M \<union> {\<rhd>} \<restriction> M) (rstep E \<restriction> M)" using vM by auto
      moreover have "(u, v) \<in> relto (rstep R \<restriction> M \<union> {\<rhd>} \<restriction> M) (rstep E \<restriction> M)" using rstep uM vM by auto
      ultimately have "(u, y) \<in> po2s" by (simp add: r_r_into_trancl) }
    then have "\<forall>y. y \<in># actop f v \<longrightarrow> (\<exists>x. x \<in># {#u#} \<and> (x, y) \<in> po2s)"
      using strict by (auto dest!: actop_subteq simp: supteq_supt_conv r_into_trancl')
    then show ?thesis
      unfolding s and t by (intro ns_s_mul_ext_union_multiset_l [OF N]) auto
  qed
next
  assume nontop: "(s, t) \<in> acnontopstep F E"
  then obtain f and n where roots: "root s = Some (f, n)" "root t = Some (f, n)"
    using assms by (auto dest: acnontopstep_eq_roots)
  show "(\<nabla> F s, \<nabla> F t) \<in> ?NS" using nontop
  proof (cases rule: acnontopstep_cases)
    case (ac u v N f)
    then have s: "\<nabla> F s = N + {#u#}"
      and "\<nabla> F t = N + {#v#} \<and> actop f u = {#u#} \<or> \<nabla> F t = N + actop f v" by (auto simp: ac_simps)
    then consider "\<nabla> F t = N + {#v#}" | "\<nabla> F t = N + actop f v" by blast
    note * = this
    have v: "actop f v = {#v#}"
      using ac and rstep_root by (simp add: actop_singleton_iff)
    have N: "(N, N) \<in> ?NS" by (rule ns_mul_ext_refl_local) (auto simp: locally_refl_def)
    from \<open>s \<in> ST\<close> \<open>s \<rhd> u\<close> have uM: "u \<in> M" by (auto simp: M_def)
    have vM: "v \<in> M"
      using assms and ac and step_preserves_SN_on_relto [of u v "rstep R" "rstep E"] by (auto simp: M_def)
    from uM vM have weak: "(u, v) \<in> po2w" using ac by auto
    show "(\<nabla> F s, \<nabla> F t) \<in> ?NS" using *
    proof (cases)
      case t: 1
      show ?thesis
        using weak unfolding s and t by (intro ns_ns_mul_ext_union_compat [OF N]) simp
    next
      case t: 2
      show ?thesis
        using weak unfolding s and t and v by (intro ns_ns_mul_ext_union_compat [OF N]) simp
    qed
  next
    case (nonac u v N)
    then have s: "\<nabla> F s = N + {#u#}" and t: "\<nabla> F t = N + {#v#}" by (auto simp: ac_simps)

    have N: "(N, N) \<in> ?NS" by (rule ns_mul_ext_refl_local) (auto simp: locally_refl_def)
    have "SN_on (relstep R E) {v}"
      using assms and nonac and step_preserves_SN_on_relto [of u v "rstep R" "rstep E"] by auto
    then have weak: "(u, v) \<in> po2w" using \<open>s \<in> ST\<close> nonac by (auto simp: M_def)
    show "(\<nabla> F s, \<nabla> F t) \<in> ?NS"
      using weak unfolding s and t by (intro ns_ns_mul_ext_union_compat [OF N]) simp
  qed
qed

lemma sharp_rstep_imp_nrrstep:
  assumes "r \<subseteq> R \<union> E"
  assumes st: "(\<sharp> s, \<sharp> t) \<in> rstep r"
  and d: "defined (R \<union> E) (the (root s))"
  shows "(s, t) \<in> nrrstep r" 
proof -
  have wf: "wf_trs r" using wf assms(1) unfolding wf_trs_def by auto
  with st have s: "is_Fun (\<sharp> s)" by (simp add: is_Fun_Fun_conv rstep_imp_Fun)
  then obtain f ss where s: "s = Fun f ss" by (cases s, auto)
  let ?f = "(f,length ss)"
  have "(\<sharp> s, \<sharp> t) \<in> nrrstep r"
  proof (rule rstep_imp_nrrstep[OF _ _ _ st])
    show "\<forall>(l, r)\<in>r. is_Fun l" using wf unfolding wf_trs_def by auto
    from d have "defined (R \<union> E) ?f" unfolding s by auto
    from shp_not_defined[OF this] assms(1) show "\<not> defined r (the (root (\<sharp> s)))"
      unfolding s defined_def by auto
  qed (simp add: s)
  then show ?thesis unfolding nrrstep_iff_arg_rstep s by (cases t; insert inj_shp, auto)
qed

lemma actop_subst: "funas_term t \<subseteq> {(f,2)} \<Longrightarrow> actop f (t \<cdot> \<sigma>) = \<Sum>\<^sub># (image_mset (actop f o \<sigma>) (vars_term_ms t))" 
  by (induct t rule: bterm_induct, auto simp: ac_simps)

lemma nabla_subst: "funas_term t \<subseteq> {(f,2)} \<Longrightarrow> is_Fun t \<Longrightarrow> f \<in> F \<Longrightarrow> \<nabla> F (t \<cdot> \<sigma>) = \<Sum>\<^sub># (image_mset (actop f o \<sigma>) (vars_term_ms t))"
  using actop_subst[of t f \<sigma>] by (cases t, auto)

lemma flatten_vars_term_subst: 
  assumes "(l, r) \<in> E" "the (root l) \<in> F\<^sub>A \<times> UNIV"
  shows "\<exists> f \<in> F\<^sub>A. root l = Some (f,2) \<and> root r = Some (f,2) 
    \<and> \<nabla> F\<^sub>A (l \<cdot> \<sigma>) = \<Sum>\<^sub># (image_mset (actop f o \<sigma>) (vars_term_ms l))
    \<and> \<nabla> F\<^sub>A (r \<cdot> \<sigma>) = \<Sum>\<^sub># (image_mset (actop f o \<sigma>) (vars_term_ms r))"
proof -
  from ruleD[OF assms(1)] obtain f l1 l2 r1 r2 where l: "l = Fun f [l1,l2]"
    and r: "r = Fun f [r1,r2]" "\<Union> (funas_term ` {l1,l2,r1,r2}) \<subseteq> {(f,2)}" by auto
  then have lf: "funas_term l \<subseteq> {(f,2)}" "is_Fun l" and rf: "funas_term r \<subseteq> {(f,2)}" "is_Fun r" by auto
  from assms[unfolded l] have f: "f \<in> F\<^sub>A" unfolding funs_trs_def funs_rule_def[abs_def] by force
  from nabla_subst[OF lf f, of \<sigma>] nabla_subst[OF rf f, of \<sigma>] l r f show ?thesis by auto
qed

lemma flatten_vars_term_subst_actop:
  assumes "(l, r) \<in> E" and "root l = Some (f, n)"
  shows "actop f (l \<cdot> \<sigma>) = \<Sum>\<^sub># (image_mset (actop f o \<sigma>) (vars_term_ms l))
    \<and> actop f (r \<cdot> \<sigma>) = \<Sum>\<^sub># (image_mset (actop f o \<sigma>) (vars_term_ms r))"
proof -
  from ruleD[OF assms(1)] 
  have lf: "funas_term l \<subseteq> {(f,2)}" and rf: "funas_term r \<subseteq> {(f,2)}" using assms(2) by auto 
  from actop_subst[OF lf] actop_subst[OF rf] show ?thesis by blast+
qed

lemma nabla_rrstep_E:
  assumes "(s,t) \<in> rrstep E"
  shows "\<nabla> F\<^sub>A s = \<nabla> F\<^sub>A t"
proof -
  from rrstepE[OF assms] obtain l r \<sigma> where lr: "(l, r) \<in> E" and id: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" .
  show ?thesis 
  proof (cases "the (root l) \<in> F\<^sub>A \<times> UNIV")
    case True
    from flatten_vars_term_subst[OF lr True, of \<sigma>, folded id] ruleD(2)[OF lr] show ?thesis by auto
  next
    case False
    from ruleD[OF lr] obtain f l1 l2 r1 r2 where 
      id': "l = Fun f [l1,l2]" "r = Fun f [r1,r2]" by auto
    from lr id' have "f \<in> funs_trs E" unfolding funs_trs_def funs_rule_def[abs_def] by force
    with EF False id' have f: "f \<in> F\<^sub>C - F\<^sub>A" by auto
    from AC_C_theory.only_C_D[OF AC_C_E lr _ f] obtain u v where l: "l = Fun f [u,v]" 
      and r: "r = Fun f [v,u]" unfolding id' by auto
    then show ?thesis unfolding id l r using f by simp
  qed
qed

lemma actop_rrstepE:
  assumes "(s, t) \<in> rrstep E" and "root s = Some (f, n)"
  shows "actop f s = actop f t"
proof -
  from rrstepE [OF assms(1)] obtain l r \<sigma> where lr: "(l, r) \<in> E" and id: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" .
  with assms no_left_var[of _ r] lr
  have "root l = Some (f, n)" by (cases l) auto
  from flatten_vars_term_subst_actop [OF lr this, of \<sigma>, folded id]
    and ruleD(2) [OF lr] show ?thesis by auto
qed

lemma ne_top_ctxts_actop_ctxt_ne [simp]:
  assumes "C \<in> top_ctxts f" and "C \<noteq> \<box>"
  shows "actop_ctxt f C \<noteq> {#}"
using assms by (induct) auto

lemma ac_term_top_ctxtsI:
  assumes "funas_term t = {(f, 2)}" and "t = C\<langle>u\<rangle>"
  shows "C \<in> top_ctxts f"
using assms
proof (induct C arbitrary: t)
  case Hole
  show ?case by (auto intro: top_ctxts.intros)
next
  case (More g ss C ts)
  moreover then have "funas_term (C\<langle>u\<rangle>) \<subseteq> funas_term t" by auto
  with \<open>funas_term t = {(f, 2)}\<close> and More(1) [of "C\<langle>u\<rangle>"]
    have "C \<in> top_ctxts f" by (cases C) (auto intro: top_ctxts.intros)
  then show ?case
    using More.prems by (cases ss; cases ts; auto intro!: top_ctxts.intros)
qed

lemma subst_top_ctxts:
  assumes "C \<in> top_ctxts f"
  shows "C \<cdot>\<^sub>c \<sigma> \<in> top_ctxts f"
using assms by (induct C) (auto intro: top_ctxts.intros)

(*maybe the following works?*)
lemma rhs_subt_actop_subset:
  fixes s t :: "('f, 'v) term"
  assumes rule: "(l, r) \<in> E"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" and "r \<rhd> u" and rt: "root l = Some (f, n)"
    and f: "f \<in> F\<^sub>A"
  shows "actop f (u \<cdot> \<sigma>) \<subset># \<nabla> F\<^sub>A s"
proof -
  have rrstep: "(s, t) \<in> rrstep E" using assms by (auto)
  have nabla_s: "\<nabla> F\<^sub>A s = \<nabla> F\<^sub>A t" by (rule nabla_rrstep_E [OF rrstep])
  from rt f have "the (root l) \<in> F\<^sub>A \<times> UNIV" by auto
  from flatten_vars_term_subst[OF rule this, of \<sigma>] rt s t 
  have [simp]: "root t = root s"  
    and *: "root t = Some (f, 2)" "f \<in> F\<^sub>A" by (cases l; cases r; auto)+
  then have [simp]: "\<nabla> F\<^sub>A s = actop f t" by (cases t) (auto simp: nabla_s)
  from ruleD[OF rule] *
  have "funas_term r = {(f, 2)}" unfolding t by auto
  with \<open>r \<rhd> u\<close> obtain C where "C \<in> top_ctxts f" and "C \<noteq> \<box>" and "r = C\<langle>u\<rangle>"
    by (auto simp: ac_term_top_ctxtsI)
  then have "C \<cdot>\<^sub>c \<sigma> \<in> top_ctxts f" and "t = (C \<cdot>\<^sub>c \<sigma>)\<langle>u \<cdot> \<sigma>\<rangle>"
    using \<open>r \<rhd> u\<close> by (auto simp: t dest: subst_top_ctxts)
  moreover have "C \<cdot>\<^sub>c \<sigma> \<noteq> \<box>" using \<open>C \<noteq> \<box>\<close> by (cases C) auto
  ultimately show ?thesis
    by auto (metis add.left_neutral subset_mset.zero_less_iff_neq_zero ne_top_ctxts_actop_ctxt_ne subset_mset.add_less_cancel_right)
qed

lemma nabla_actop_suptmulexeq:
  fixes ts
  assumes "f \<in> F\<^sub>A"
  defines "s \<equiv> Fun f ts"
  shows "actop f s \<unrhd>\<^sub># \<nabla> F\<^sub>A s"
using assms and args_in_suptmulex [of f ts]
by (auto simp: locally_refl_def s_ns_mul_ext intro: ns_mul_ext_refl)

lemma nabla_of_subt_suptmulex:
  assumes "s \<rhd> t"
  shows "{#s#} \<rhd>\<^sub># \<nabla> F\<^sub>A t"
using assms by (intro all_s_s_mul_ext) (auto dest!: nabla_subt intro: supt_trans)

lemma actop_suptmulexeq:
  "{#t#} \<unrhd>\<^sub># actop f t"
using Bin_cases_with_length [of t]
apply (auto)
apply (intro s_ns_mul_ext all_s_s_mul_ext)
by (auto dest: actop_subteq intro: set_supteq_into_supt)

lemma nabla_not_actop_suptmulex:
  assumes "\<not> (f \<in> F\<^sub>A \<and> length ts = 2)"
  defines "s \<equiv> Fun f ts"
  assumes "s \<rhd> t"
  shows "\<nabla> F\<^sub>A s \<rhd>\<^sub># \<nabla> F\<^sub>A t"
proof -
  have "mset ts \<rhd>\<^sub># \<nabla> F\<^sub>A t"
    using \<open>s \<rhd> t\<close>
    by (intro all_s_s_mul_ext)
      (auto simp: s_def in_multiset_in_set supteq_supt_trans dest!: nabla_subt supt_Fun_imp_arg_supteq)
  then show ?thesis using assms by auto
qed

lemma not_top_ctxts_supt:
  assumes "C \<notin> top_ctxts f"
  shows "\<exists>u. u \<in># actop f (C\<langle>t\<rangle>) \<and> u \<rhd> t"
using assms
proof (induct C arbitrary: t)
  case Hole then show ?case by (auto simp: top_ctxts.intros)
next
  case (More g ss C ts)
  let ?C = "More g ss C ts"
  consider s' where "ss = [s']" and "ts = []" | t' where "ss = []" and "ts = [t']" |
    "\<And>u v. ?C\<langle>t\<rangle> \<noteq> Bin g u v"
    using More and Bin_cases [of "?C\<langle>t\<rangle>"]
    by (metis (no_types, lifting) actxt.distinct(1) actxt.inject ctxt_apply_term_Bin_cases)
  then show ?case
  proof (cases)
    case [simp]: 1
    show ?thesis
    proof (cases "C \<in> top_ctxts f")
      case True
      with More show ?thesis
        apply (auto intro: top_ctxts.intros)
        by (metis Cons_eq_append_conv actxt.distinct(1) intp_actxt.simps(2) ctxt_supt)
    next
      case False
      from More(1) [OF this] show ?thesis apply auto
        by (metis Cons_eq_append_conv actxt.distinct(1) intp_actxt.simps(2) ctxt_supt)
    qed
  next
    case [simp]: 2
    show ?thesis
    proof (cases "C \<in> top_ctxts f")
      case True
      with More show ?thesis
        apply (auto intro: top_ctxts.intros)
        by (metis Cons_eq_append_conv actxt.distinct(1) intp_actxt.simps(2) ctxt_supt)
    next
      case False
      from More(1) [OF this] show ?thesis apply auto
        by (metis Cons_eq_append_conv actxt.distinct(1) intp_actxt.simps(2) ctxt_supt)
    qed
  next
    case 3
    with More show ?thesis by auto
  qed
qed

lemma not_top_ctxts_actop_mul_ext_supt:
  assumes "C \<notin> top_ctxts f"
  shows "actop f (C\<langle>t\<rangle>) \<rhd>\<^sub># {#t#}"
using assms by (intro all_s_s_mul_ext) (auto dest: not_top_ctxts_supt)

lemma supt_impl_nabla_mul_supt:
  fixes s t :: "('f, 'v) term"
  assumes "s \<rhd> t"
  shows "\<nabla> F\<^sub>A s \<rhd>\<^sub># \<nabla> F\<^sub>A t"
proof (cases t)
  case (Var x)
  moreover have "\<nabla> F\<^sub>A s \<noteq> {#}" using assms by (cases s) auto
  ultimately show ?thesis using assms by (auto dest: s_mul_ext_bottom)
next
  case t: (Fun g ts)
  show ?thesis
  proof (cases s)
    case [simp]: (Fun f ss)
    show ?thesis
    proof (cases "f \<in> F\<^sub>A \<and> length ss = 2")
      case False
      from nabla_not_actop_suptmulex [OF this, of t] show ?thesis using assms by simp
    next
      case F: True
      obtain C where [simp]: "C \<noteq> \<box>" and s: "Fun f ss = C\<langle>t\<rangle>" using assms by auto
      show ?thesis
      proof (cases "C \<in> top_ctxts f")
        case True
        {
          assume "f \<in> F\<^sub>A" "length ss = 2"
          from True this have "actop f C\<langle>t\<rangle> \<rhd>\<^sub># \<nabla> F\<^sub>A t" 
          apply (auto simp: t)
          apply (cases "f = g")
          apply auto
          apply (rule s_mul_ext_self_extend_left)
          apply force
          apply (force simp: locally_refl_def)
          apply (subst add_mset_add_single)
          apply (rule s_mul_ext_ne_extend_left)
          apply force
          apply (rule actop_suptmulexeq)
          apply (subst add_mset_add_single)
          apply (rule s_mul_ext_extend_left)
          apply (simp add: args_in_suptmulex)
          apply (subst add_mset_add_single)
          apply (rule s_mul_ext_extend_left)
          apply (simp add: args_in_suptmulex)
          done
        } note main = this
        show ?thesis using F unfolding Fun by (auto, unfold s, insert main, auto)
    next
      case False
      then show ?thesis using F unfolding Fun apply auto
      unfolding s
      apply (auto simp: t)

      apply (rule s_ns_mul_ext_trans [of _ _ _ "{#Fun g ts#}"])
      apply (auto simp: trans_def compatible_l_def compatible_r_def refl_on_def dest: supt_trans)
      apply (rule all_s_s_mul_ext)
      apply (auto dest: not_top_ctxts_supt intro: actop_suptmulexeq)

      apply (rule s_mul_ext_trans [of _ _ _ "{#Fun g ts#}"])
      apply (auto simp: trans_def compatible_l_def compatible_r_def refl_on_def dest: supt_trans)

      apply (rule s_ns_mul_ext_trans [of _ _ _ "{#Fun g ts#}"])
      apply (auto simp: trans_def compatible_l_def compatible_r_def refl_on_def dest: supt_trans)
      apply (rule all_s_s_mul_ext)
      apply (auto dest: not_top_ctxts_supt intro: actop_suptmulexeq args_in_suptmulex)

      apply (rule s_mul_ext_trans [of _ _ _ "{#Fun g ts#}"])
      apply (auto simp: trans_def compatible_l_def compatible_r_def refl_on_def dest: supt_trans)

      apply (rule s_ns_mul_ext_trans [of _ _ _ "{#Fun g ts#}"])
      apply (auto simp: trans_def compatible_l_def compatible_r_def refl_on_def dest: supt_trans)
      apply (rule all_s_s_mul_ext)
      apply (auto dest: not_top_ctxts_supt intro: actop_suptmulexeq args_in_suptmulex)
      done
    qed
  qed
next
  case (Var x)
  with assms show ?thesis by auto
  qed
qed


lemma rrstep_E_imp_nabla_mul_supt:
  assumes "(s, t) \<in> rrstep E" and "t \<rhd> u"
  shows "\<nabla> F\<^sub>A s \<rhd>\<^sub># \<nabla> F\<^sub>A u"
  using nabla_rrstep_E[OF assms(1)] supt_impl_nabla_mul_supt[OF assms(2)]
  by auto

lemma actopstep_E_preserves_actop:
  assumes "(s, t) \<in> actopstep F E" and "root s = Some (f, n)"
  shows "actop f s = actop f t"
using assms apply (auto simp: actopstep_def dest!: actopstep_sym_cases)
using actop_rrstepE apply blast
by (auto dest!: actop_rrstepE simp: top_ctxts_root)

lemma nabla_actop_conv:
  assumes "C \<in> top_ctxts f" and "C \<noteq> \<box>" and "f \<in> F\<^sub>A"
  shows "\<nabla> F\<^sub>A (C\<langle>t\<rangle>) = actop f (C\<langle>t\<rangle>)"
using assms by (cases) auto

lemma actopstep_E_preserves_nabla:
  assumes "(s, t) \<in> actopstep F E" and "root s = Some (f, n)" and "f \<in> F\<^sub>A"
  shows "\<nabla> F\<^sub>A s = \<nabla> F\<^sub>A t"
using assms apply (auto simp: actopstep_def dest!: actopstep_sym_cases)
using nabla_rrstep_E apply blast
by (auto dest!: actop_rrstepE simp: nabla_actop_conv top_ctxts_root)

lemma Q_preserves_nabla:
  assumes "(\<sharp> s, \<sharp> t) \<in> rrstep (DP_on \<sharp> D E)"
  shows "\<nabla> F\<^sub>A s \<supseteq># \<nabla> F\<^sub>A t" (is ?goal1)
    and "(s,t) \<in> rstep E O {\<rhd>} \<Longrightarrow> \<nabla> F\<^sub>A s \<supset># \<nabla> F\<^sub>A t" (is "?prem2 \<Longrightarrow> ?goal2")
proof(atomize(full))
  have "wf_trs E" using wf by (auto simp: wf_trs_def)
  obtain l and r and f and us and \<sigma>
    where rule: "(l, r) \<in> E" and "\<sharp> s = \<sharp> l \<cdot> \<sigma>" and "\<sharp> t = \<sharp> (Fun f us) \<cdot> \<sigma>"
    and "r \<unrhd> Fun f us" (is "r \<unrhd> ?u") and lu: "\<not> l \<rhd> Fun f us" and "(f, length us) \<in> D"
    using assms by (auto simp: DP_on_def elim!: rrstepE)
  then have s: "s = l \<cdot> \<sigma>" and t: "t = ?u \<cdot> \<sigma>"
    using wf_trs_imp_lhs_Fun [OF \<open>wf_trs E\<close> rule]
    by (cases s; cases t; auto dest!: inj_shp)+
  show "?goal1 \<and> (?prem2 \<longrightarrow> ?goal2)" (is ?thesis)
  proof (cases "r = ?u")
    case True
    then have rrstep: "(s, t) \<in> rrstep E" using rule and s and t by (auto)
    then have "\<nabla> F\<^sub>A s = \<nabla> F\<^sub>A t" by (rule nabla_rrstep_E)
    moreover {
      assume "?prem2"
      then obtain u where "(s,u) \<in> rstep E" "(u,t) \<in> {\<rhd>}" by auto
      from rstep_num_symbs_eq[OF this(1)] supt_num_symbs[OF this(2)]
        rstep_num_symbs_eq[OF rrstep_imp_rstep[OF rrstep]]
      have False by auto
    }
    ultimately show ?thesis using rrstep by auto
  next
    case False 
    then have ru: "r \<rhd> ?u" using \<open>r \<unrhd> ?u\<close> by auto
    from ru ruleD [OF rule] and EF
    have root: "root l = Some (f, 2)" and len: "length us = 2"
      using supt_imp_funas_term_subset [OF \<open>r \<rhd> ?u\<close>] and rule
      by (auto simp: funs_defs)
    from root rule have fE: "f \<in> funs_trs E" by (cases l; force simp: funs_defs)
    with EF have f: "f \<in> F\<^sub>A \<union> F\<^sub>C" by auto
    show ?thesis
    proof (cases "f \<in> F\<^sub>A")
      case True
      with len root rhs_subt_actop_subset [OF \<open>(l, r) \<in> E\<close> s refl \<open>r \<rhd> ?u\<close> root True] True
      show ?thesis by (auto simp: t)
    next
      case False
      with f have "f \<in> F\<^sub>C - F\<^sub>A" by auto
      from AC_C_theory.only_C_D[OF AC_C_E rule root this] obtain v w where
         l: "l = Fun f [v,w]" and r: "r = Fun f [w,v]" by auto
      from supt_Fun_imp_arg_supteq[OF ru[unfolded r]] lu[unfolded l] have False 
        using set_supteq_into_supt[of _ "[v,w]" ?u f] by auto
      then show ?thesis ..
    qed
  qed
qed

private lemma QE_preserve_nabla:
  assumes "(\<sharp> s, \<sharp> t) \<in> rstep E \<union> rrstep (DP_on \<sharp> D E)"
  and s: "s \<in> ST"
  and d: "defined (R \<union> E) (the (root s))"
  shows "(\<nabla> F\<^sub>A s, \<nabla> F\<^sub>A t) \<in> ns_mul_ext po2w po2s"
  using assms(1)
proof
  assume "(\<sharp> s, \<sharp> t) \<in> rstep E"
  then have st: "(s,t) \<in> nrrstep E" using sharp_rstep_imp_nrrstep[OF _ _ d] by auto
  show ?thesis
  proof (cases "(s,t) \<in> actopstep F\<^sub>A E")
    case True
    with \<open>(s, t) \<in> nrrstep E\<close> have eq: "\<nabla> F\<^sub>A s = \<nabla> F\<^sub>A t"
      apply (auto simp: actopstep_def actopstep_sym_iff top_ctxts_root nabla_rrstep_E)
      using True actopstep_E_preserves_nabla top_ctxts_root by fastforce
    show ?thesis unfolding eq
      apply(rule ns_mul_ext_refl_local) unfolding locally_refl_def by auto
  next case False
    with nrrstep_imp_rstep[OF st]
    have "(s,t) \<in> acnontopstep F\<^sub>A E" unfolding acnontopstep_def by auto
    from acnontopstep_mul_ext(2)[OF s this] show ?thesis.
  qed
next
  assume "(\<sharp> s, \<sharp> t) \<in> rrstep (DP_on \<sharp> D E)"
  then have "\<nabla> F\<^sub>A s \<supseteq># \<nabla> F\<^sub>A t" using Q_preserves_nabla by blast
  from supseteq_imp_ns_mul_ext [OF refl_rtrancl this]
    show ?thesis .
qed

lemma not_SN_on_pred: "(s,t) \<in> r \<Longrightarrow> \<not> SN_on r {t} \<Longrightarrow> \<not> SN_on r {s}"
  by (meson step_preserves_SN_on)

lemma not_SN_on_rel_pred: "(s,t) \<in> r \<union> e \<Longrightarrow> \<not> SN_on (relto r e) {t} \<Longrightarrow> \<not> SN_on (relto r e) {s}"
  by (meson step_preserves_SN_on_relto)

lemma not_SN_on_rel_preds:
  assumes tr: "(s,t) \<in> (r \<union> e)\<^sup>*"
    and SN: "\<not> SN_on (relto r e) {t}"
  shows "\<not> SN_on (relto r e) {s}"
  using tr unfolding rtrancl_power
proof (elim exE)
  fix n assume "(s, t) \<in> (r \<union> e) ^^ n"
  with SN show ?thesis
  proof(induct n arbitrary: s)
    case 0 then show ?case using SN by auto
    next case (Suc n)
      obtain s' where ss': "(s,s') \<in> r \<union> e" and s't: "(s',t) \<in> (r \<union> e) ^^ n" using relpow_Suc_E2[OF Suc(3)].
      from not_SN_on_rel_pred[OF ss' Suc(1)[OF SN s't]] show ?case.
  qed
qed

lemma Tinf_imp_not_SN_on:
  "s \<in> Tinf r \<Longrightarrow> \<not> SN_on r {s}"
by (auto simp: Tinf_def)

lemma AC_is_size_preserving:
  assumes "rrstep E = rrstep (AC_trs F F)"
  shows "size_preserving_trs E"
proof -
  have "E \<subseteq> rstep E" by auto
  also have "\<dots> \<subseteq> acrstep F F"
  proof (rule rstep_subset[OF ctxt_closed_rstep subst_closed_rstep])
    have "E \<subseteq> rrstep E" by auto
    also have "\<dots> \<subseteq> acrstep F F" unfolding assms(1) by (simp add: rstep_iff_rrstep_or_nrrstep)
    finally show "E \<subseteq> acrstep F F" .
  qed
  finally have E: "E \<subseteq> acrstep F F" .
  interpret size_preserving_trs "AC_trs F F" by (rule size_preserving_AC_trs)
  show ?thesis
  proof (standard, clarify)
    fix l r
    assume "(l,r) \<in> E"
    with E have "(l,r) \<in> acrstep F F" by auto
    from rstep_num_symbs_eq[OF this] rstep_vars_terms_ms_eq[OF this]
    show "num_symbs l = num_symbs r \<and> vars_term_ms l = vars_term_ms r" by auto
  qed
qed

lemma Tinf_relstep_defined_root':
  assumes "wf_trs (R \<union> E)" and "t \<in> Tinf (relstep R E)"
  shows "\<exists>f. defined (R \<union> E) f \<and> root t = Some f"
using assms(1)
  and Tinf_imp_SN_nr_first_root_step_rel[of _ False "{}" _ "{}", unfolded qrstep_rstep_conv nrqrstep_nrrstep rqrstep_rrstep_conv, OF assms(2)]
  and nrrsteps_imp_eq_root_arg_rsteps [of t _ "R \<union> E"]
  and assms
by (auto simp: nrrstep_union wf_trs_def defined_def elim!: rrstepE) (case_tac l; auto)+

lemma rrstep_Tinfs_imp_rrstep_R_DP_on:
  assumes "(s, t) \<in> rrstep R" and "s \<in> Tinf (relstep R E)" and "t \<in> Tinf (relstep R E)"
  shows "(\<sharp> s, \<sharp> t) \<in> rrstep (DP_on \<sharp> {f. defined (R \<union> E) f} R)"
proof -
  from Tinf_relstep_defined_root' [OF wf assms(3)] obtain f and n
    where "root t = Some (f, n)" and *: "defined (R \<union> E) (f, n)" by force
  moreover obtain l and r and \<sigma> where rule: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    using assms by (auto elim: rrstepE)
  moreover have "is_Fun r"
  proof
    assume "is_Var r"
    then obtain x where "r = Var x" and "x \<in> vars_term l"
      using wf and rule by (cases r; force simp: wf_trs_def) 
    then have "l \<rhd> r" using wf and rule by (cases l) (auto simp: wf_trs_def)
    then show False using assms(2, 3) by (auto simp: s t Tinf_def dest: supt_subst)
  qed
  ultimately obtain us where r: "r = Fun f us" (is "_ = ?u") and [simp]: "length us = n" by auto
  then have "r \<unrhd> ?u" by simp
  then have "(\<sharp> l, \<sharp> ?u) \<in> DP_on \<sharp> {f. defined (R \<union> E) f} R"
    using * and rule apply (auto simp: DP_on_def)
    apply (rule exI [of _ l]) apply auto
    apply (rule exI [of _ r], rule exI [of _ f]) apply (auto simp: r [symmetric])
    using s and t and assms(2, 3) by (auto simp: Tinf_def dest: supt_subst)
  from rrstepI [OF this, of "\<sharp> s" \<sigma> "\<sharp> t"]
    show "(\<sharp> s, \<sharp> t) \<in> rrstep (DP_on \<sharp> {f. defined (R \<union> E) f} R)"
    using wf and rule by (cases l) (auto simp: s t r wf_trs_def)
qed

lemma rrstep_Tinfs_imp_rrstep_E_DP_on:
  assumes "(s, t) \<in> rrstep E" and "s \<in> Tinf (relstep R E)"
  shows "(\<sharp> s, \<sharp> t) \<in> rrstep (DP_on \<sharp> {f. defined (R \<union> E) f} E)"
proof -
  obtain l and r and \<sigma> where rule: "(l, r) \<in> E" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    using assms by (auto elim: rrstepE)
  from ruleD[OF rule] obtain f ls rs where l: "l = Fun f ls" and r: "r = Fun f rs" (is "_ = ?u")
    and [simp]: "length ls = length rs" by auto
  from rule l have *: "defined (R \<union> E) (f,length rs)" unfolding defined_def by auto  
  interpret AC_C_theory E "F\<^sub>C - F\<^sub>A" by (rule AC_C_E)
  from supt_num_symbs[of l r] same_size rule
  have supt: "\<not> l \<rhd> r" by auto
  have "(\<sharp> l, \<sharp> r) \<in> DP_on \<sharp> {f. defined (R \<union> E) f} E"
    using * and rule apply (auto simp: DP_on_def r)
    apply (rule exI [of _ l]) apply auto
    apply (rule exI [of _ r], rule exI [of _ f]) by (insert supt, auto simp: r)
  from rrstepI [OF this, of "\<sharp> s" \<sigma> "\<sharp> t"]
    show "(\<sharp> s, \<sharp> t) \<in> rrstep (DP_on \<sharp> {f. defined (R \<union> E) f} E)"
    using wf and rule by (auto simp: l r s t)
qed

interpretation aoc_rewriting F\<^sub>A F\<^sub>C .

theorem main_sound:
  defines "D \<equiv> {f. defined (R \<union> E) f}"
  defines "P \<equiv> DP_on \<sharp> D R"
  assumes R_ext: "is_ext_trs R F\<^sub>A F\<^sub>C R\<^sub>e\<^sub>x\<^sub>t"
    and E_is_AC: "(rstep E)\<^sup>* = AOCEQ"
    and Q: "Q = DP_on \<sharp> D E"
    and finP: "weakly_finite P Q R E"
    and finP': "weakly_finite (\<sharp> R\<^sub>e\<^sub>x\<^sub>t) Q R E"
  shows "SN (relstep R E)"
proof (rule ccontr)
  (*setting up orders*)
  from po3[OF finP] interpret po3P: SN_order_pair "po3s P" "po3w P".
  from po3[OF finP'] interpret po3P': SN_order_pair "po3s (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)" "po3w (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)".
  define po2ms where "po2ms = s_mul_ext po2w po2s"
  define po2mw where "po2mw = ns_mul_ext po2w po2s"
  interpret AC_C_theory E "F\<^sub>C - F\<^sub>A" by (rule AC_C_E)
  interpret po2m: SN_order_pair po2ms po2mw 
    unfolding po2ms_def po2mw_def using po2.mul_ext_SN_order_pair.
  define indos where "indos = lex_two (po3s P) (po3w P) (lex_two (po3s (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)) (po3w (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)) po2ms)"
  define indow where "indow = lex_two (po3s P) (po3w P) (lex_two (po3s (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)) (po3w (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)) po2mw)"
  interpret indo: SN_order_pair indos indow
    unfolding indos_def indow_def by (intro lex_two_SN_order_pair; unfold_locales)
  define msr where "msr = (\<lambda>s :: ('f,'v) term. (\<sharp> s, \<sharp> s, \<nabla> F\<^sub>A s ))"
  (*main part*)
  { fix s assume "s \<in> Tinf (relstep R E)"
    then have False
    proof (induct "msr s" arbitrary: s rule: SN_induct[OF indo.SN])
      case (1 s)
      from Tinf_starts_relchain [OF SN_suptrel subset_refl 1(2), unfolded starts_relchain_def]
        obtain w and m
        where "relchain_part P Q s w m" unfolding P_def Q D_def by blast
      from this[unfolded relchain_part_def]
      have w: "\<And>i. w i \<in> Tinf (relstep R E)"
       and sw0: "s = w 0"
       and QE: "\<And>i. i < m \<Longrightarrow> (\<sharp> (w i), \<sharp> (w (Suc i))) \<in> rstep E \<union> minstep Q"
       and PR: "(\<sharp> (w m), \<sharp> (w (Suc m))) \<in> rstep R \<union> minstep P"
       by (auto simp: nrrstep_imp_rstep)
      from Tinf_relstep_defined_root[OF wf w]
      have d: "\<And> i. defined (R \<union> E) (the (root (w i)))" .
      define u where "u = w (Suc m)"
      with PR w
      have tu: "(\<sharp> (w m), \<sharp> u) \<in> rstep R \<union> minstep P" and u: "u \<in> Tinf (relstep R E)" by auto
      have "\<And>P''. (\<sharp> s, \<sharp> (w m)) \<in> po3w P''"
      proof -
        fix P''
        have "(\<sharp> s, \<sharp> (w m)) \<in> (rstep E \<union> minstep Q)\<^sup>*"
          unfolding rtrancl_fun_conv
          apply (intro exI[of _ "\<lambda>i. \<sharp> (w i)"] exI[of _ m]) using QE sw0 by auto
        also have "... \<subseteq> po3w P''" unfolding rstep_union minstep_union by regexp
        ultimately show "(\<sharp> s, \<sharp> (w m)) \<in> ..." by auto
      qed
      moreover have "(\<nabla> F\<^sub>A s, \<nabla> F\<^sub>A (w m)) \<in> po2mw"
      proof -
        { fix i assume "i \<le> m" then have "(\<nabla> F\<^sub>A s, \<nabla> F\<^sub>A (w i)) \<in> po2mw"
          proof (induct i)
            case 0 show ?case unfolding sw0 using "po2m.refl_NS_point" by auto
            next case (Suc i)
              then have i: "i < m"
                and st: "(\<nabla> F\<^sub>A s, \<nabla> F\<^sub>A (w i)) \<in> po2mw" by auto
              have "(\<nabla> F\<^sub>A (w i), \<nabla> F\<^sub>A (w (Suc i))) \<in> po2mw"
                unfolding po2mw_def
                apply(rule QE_preserve_nabla[OF _ _ d])
                using Suc w[unfolded Tinf_def] QE[unfolded Q, of i] by auto
              from po2m.trans_NS_point[OF st this]
              show ?case.
          qed
        }
        then show ?thesis by auto
      qed
      ultimately have swm_indow: "(msr s, msr (w m)) \<in> indow" unfolding indow_def msr_def by auto
      show ?case
      proof(cases "(\<sharp> (w m), \<sharp> u) \<in> minstep P")
        case True
        then have "(\<sharp> (w m), \<sharp> u) \<in> po3s P" by auto
        then have "(msr (w m), msr u) \<in> indos" unfolding indos_def msr_def by auto
        with indo.compat_NS_S_point[OF swm_indow this] 1 u show ?thesis by auto
      next case False
        then have Rsh: "(\<sharp> (w m), \<sharp> u) \<in> rstep R" using tu by auto
        note R = sharp_rstep_imp_nrrstep[OF _ Rsh d]
        have wmu_po3w: "\<And>P''. (\<sharp> (w m), \<sharp> u) \<in> po3w P''"
          apply(rule subsetD[OF _ Rsh]) unfolding minstep_union rstep_union by regexp
        show ?thesis
        proof (cases "(w m, u) \<in> actopstep F\<^sub>A R")
          case False
            with R have "(w m, u) \<in> acnontopstep F\<^sub>A R"
              using nrrstep_imp_rstep unfolding acnontopstep_def by auto
            from acnontopstep_mul_ext(1)[OF _ this] w[unfolded Tinf_def]
            have "(\<nabla> F\<^sub>A (w m), \<nabla> F\<^sub>A u) \<in> po2ms" unfolding po2ms_def by auto
            with wmu_po3w
            have "(msr (w m), msr u) \<in> indos" unfolding indos_def msr_def by auto
            with indo.compat_NS_S_point[OF swm_indow this] 1 u show ?thesis by auto
          next
            case True
            then obtain f where topstep: "(w m, u) \<in> actopstep_sym f F\<^sub>A R" by (auto simp: actopstep_def)
            have "\<forall>(l, r)\<in>R. is_Fun l" using wf by (auto simp: wf_trs_def')
            from actopstep_sym_rrstep_or_ext_trs[OF R_ext this topstep, folded E_is_AC]
            show ?thesis
            proof
              assume "(w m, u) \<in> rrstep R"
              from rrstep_Tinfs_imp_rrstep_R_DP_on [OF this w]
                have "(\<sharp> (w m), \<sharp> u) \<in> minstep P"
                using u w by (auto dest: Tinf_sharp_imp_SN simp: P_def D_def M_def)
              with False show False by auto
            next
              assume "(w m, u) \<in> relto (rrstep (ext_trs R)) (rstep E)"
              then obtain t' v
                where wt': "(w m, t') \<in> (rstep E)\<^sup>*"
                  and t'v: "(t',v) \<in> rrstep (ext_trs R)"
                  and vu: "(v,u) \<in> (rstep E)\<^sup>*"
                by force
              from t'v have t'vR: "(t',v) \<in> nrrstep R" 
                by (auto dest: rrstep_imp_rstep rstep_ext_trs_imp_nrrstep)
              from nrrstep_imp_rstep[OF this] vu u
              have t': "\<not> SN_on (relstep R E) {t'}"
                unfolding Tinf_def by (subst not_SN_on_pred, auto)
              from wt' obtain t n
                where wt: "t 0 = w m"
                  and E: "\<And>i. i < n \<Longrightarrow> (t i, t (Suc i)) \<in> rstep E"
                  and tt': "t n = t'"
                unfolding rtrancl_fun_conv by auto
              have t_t': "\<And>i. i \<le> n \<Longrightarrow> (t i, t') \<in> (rstep E)\<^sup>*"
              proof -
                fix i assume i_n: "i \<le> n"
                then show "(t i, t') \<in> (rstep E)\<^sup>*"
                proof (induct "n - i" arbitrary: i)
                  case (Suc ni i)
                  with E[of "i"]
                  have "(t i, t (Suc i)) \<in> rstep E" and "(t (Suc i), t') \<in> (rstep E)\<^sup>*" by auto
                  then show ?case by auto
                qed (auto simp: tt')
              qed
              have t: "\<And>i. i \<le> n \<Longrightarrow> \<not> SN_on (relstep R E) {t i}"
              proof -
                fix i assume i: "i \<le> n"
                show "\<not> SN_on (relstep R E) {t i}"
                  by (rule not_SN_on_rel_preds[OF _ t'], rule set_mp[OF _ t_t'[OF i]], regexp)
              qed
              have "\<And>i. i \<le> n \<Longrightarrow> t i \<in> Tinf (relstep R E) \<and> (msr s, msr (t i)) \<in> indow"
              proof -
                fix i assume "i \<le> n"
                then show "t i \<in> Tinf (relstep R E) \<and> (msr s, msr (t i)) \<in> indow"
                proof (induct i)
                  case 0 then show ?case using wt w[of m] swm_indow by auto
                next case (Suc i)
                  then have i: "i < n"
                    and ti: "t i \<in> Tinf (relstep R E)"
                    and sti_indow: "(msr s, msr (t i)) \<in> indow" by auto
                  from E[OF i] consider (root) "(t i, t (Suc i)) \<in> rrstep E"
                    | (nroot) "(t i, t (Suc i)) \<in> nrrstep E" unfolding rstep_iff_rrstep_or_nrrstep by auto
                  then have QE: "(\<sharp> (t i), \<sharp> (t (Suc i))) \<in> rstep E \<union> rrstep Q"
                  proof (cases)
                    case nroot
                    from nrrstep_imp_sharp_rstep[OF this]
                    have "(\<sharp> (t i), \<sharp> (t (Suc i))) \<in> rstep E" by auto
                    then show ?thesis by auto
                  next
                    case root
                    from rrstep_Tinfs_imp_rrstep_E_DP_on[OF this ti]
                    have "(\<sharp> (t i), \<sharp> (t (Suc i))) \<in> rrstep Q" unfolding Q D_def .
                    then show ?thesis by auto
                  qed
                  have titSi_po2mw: "(\<nabla> F\<^sub>A (t i), \<nabla> F\<^sub>A (t (Suc i))) \<in> po2mw"
                    using ti unfolding po2mw_def Tinf_def
                    apply (intro QE_preserve_nabla[OF QE [unfolded Q] _ Tinf_relstep_defined_root [OF wf ti]])
                    by auto
                  have tSi: "t (Suc i) \<in> Tinf (relstep R E)"
                  proof (rule ccontr)
                    have nSN: "\<not> SN_on (relstep R E) {t (Suc i)}" using t Suc by auto
                    assume notTinf: "t (Suc i) \<notin> Tinf (relstep R E)"
                    with E[OF i, unfolded rstep_iff_rrstep_or_nrrstep] Tinf_nrrstep[OF ti _ nSN]
                    have "(t i, t (Suc i)) \<in> rrstep E" unfolding nrrstep_union by auto
                    from rrstep_imp_minstep(2)[OF _ wf ti nSN this]
                    obtain t''
                      where "t'' \<unlhd> t (Suc i)"
                        and t'': "t'' \<in> Tinf (relstep R E)"
                        and tit'': "(\<sharp> (t i), \<sharp> t'') \<in> minstep Q" unfolding Q D_def by auto
                    then have tSit'': "t (Suc i) \<rhd> t''" using notTinf by auto
                    have "(\<sharp> (t i), \<sharp> t'') \<in> po3w P" "(\<sharp> (t i), \<sharp> t'') \<in> po3w (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)"
                      using tit'' unfolding minstep_union by auto
                    moreover
                      from tit'' Q_preserves_nabla(2)[OF _ relcompI[OF E[OF i] tSit'']]
                      have "\<nabla> F\<^sub>A (t i) \<supset># \<nabla> F\<^sub>A t''" by (auto simp: Q)
                      then have "(\<nabla> F\<^sub>A (t i), \<nabla> F\<^sub>A t'') \<in> po2ms"
                        by (unfold po2ms_def, auto intro!: supset_imp_s_mul_ext refl_onI)
                    ultimately have "(msr (t i), msr t'') \<in> indos"
                      unfolding indos_def msr_def by auto
                    with sti_indow have "(msr s, msr t'') \<in> indos"
                      using indo.compat_NS_S by auto
                    from 1(1)[OF this t''] show False.
                  qed
                  with ti Tinf_sharp_imp_SN have "\<sharp> (t i) \<in> M" "\<sharp> (t (Suc i)) \<in> M" by (auto simp: M_def)
                  moreover then have "\<And>P''. (\<sharp> (t i), \<sharp> (t (Suc i))) \<in> po3w P''"
                      using QE by (auto simp: minstep_union rstep_union)
                  then have "(msr (t i), msr (t (Suc i))) \<in> indow"
                    unfolding indow_def msr_def using titSi_po2mw by auto
                  ultimately show ?case using indo.trans_NS_point[OF sti_indow] tSi
                    by (auto simp: M'_def)
                qed
              qed
              with tt'
              have t': "t' \<in> Tinf (relstep R E)" and st'_indow: "(msr s, msr t') \<in> indow" by auto
              have v: "v \<in> Tinf (relstep R E)"
                apply (rule Tinf_nrrstep[OF t']) using t'vR unfolding nrrstep_union apply simp
                apply (rule not_SN_on_rel_preds[OF _ Tinf_imp_not_SN_on[OF u]])
                apply (rule subsetD[OF _ vu]) by regexp
              with t' have "\<sharp>t' \<in> M" "\<sharp> v \<in> M" using Tinf_sharp_imp_SN by (auto simp: M_def)
              moreover from is_ext_trs_rrstep[OF R_ext t'v]
                have "(\<sharp> t', \<sharp> v) \<in> rrstep (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)" .
              ultimately have "(\<sharp> t', \<sharp> v) \<in> minstep (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)" unfolding M_def by auto
              then have "(\<sharp> t', \<sharp> v) \<in> po3s (\<sharp> R\<^sub>e\<^sub>x\<^sub>t)" unfolding minstep_union by auto
              moreover have "(\<sharp> t', \<sharp> v) \<in> po3w P"
                  unfolding rstep_union
                  using nrrstep_imp_sharp_nrrstep[OF t'vR] nrrstep_imp_rstep by fast
                then have "(\<sharp> t', \<sharp> v) \<in> po3w P" using t' unfolding M_def Tinf_def by auto
              ultimately have "(msr t', msr v) \<in> indos" unfolding indos_def msr_def by auto
              with st'_indow have "(msr s, msr v) \<in> indos" using "indo.compat_NS_S" by auto
              from 1(1)[OF this v] show False.
            qed
        qed
      qed
    qed
  } note main = this
  assume "\<not> ?thesis"
  then obtain s where "s \<in> Tinf (relstep R E)" using not_SN_imp_Tinf by auto
  from main[OF this]
  show False.
qed

end (* fixed Q *)

end (* AC_theory E *)

context
  fixes F\<^sub>A F\<^sub>C :: "'f set"
begin

interpretation aoc_rewriting F\<^sub>A F\<^sub>C .

corollary SN_relstep_via_finite_rel_dpps:
  defines "D \<equiv> {f. defined (R \<union> E) f}"
  assumes R_ext: "is_ext_trs R F\<^sub>A F\<^sub>C R\<^sub>e\<^sub>x\<^sub>t"
    and E_is_AC: "(rstep E)\<^sup>* = AOCEQ"
    and AC: "AC_C_theory E (F\<^sub>C - F\<^sub>A)"
    and EF\<^sub>A: "funs_trs E \<subseteq> F\<^sub>A \<union> F\<^sub>C"
    and finP: "finite_rel_dpp (DP_on \<sharp> D R, DP_on \<sharp> D E, {}, R, E)" 
    and finP': "finite_rel_dpp (\<sharp> R\<^sub>e\<^sub>x\<^sub>t, DP_on \<sharp> D E, {}, R, E)"
  shows "SN (relstep R E)"
  by (rule main_sound [OF AC EF\<^sub>A R_ext E_is_AC refl])
     (insert finP finP', auto simp: D_def finite_rel_dpp_def weakly_finite_def)

corollary SN_relstep_via_finite_rel_dpps_defined_R:
  defines "D \<equiv> {f. defined R f}"
  assumes R_ext: "is_ext_trs R F\<^sub>A F\<^sub>C R\<^sub>e\<^sub>x\<^sub>t"
    and E_is_AC: "(rstep E)\<^sup>* = AOCEQ"
    and AC: "AC_C_theory E (F\<^sub>C - F\<^sub>A)"
    and EF\<^sub>A: "funs_trs E \<subseteq> F\<^sub>A \<union> F\<^sub>C"
    and finP: "finite_rel_dpp (DP_on \<sharp> D R, DP_on \<sharp> D E, {}, R, E)" 
    and finP': "finite_rel_dpp (\<sharp> R\<^sub>e\<^sub>x\<^sub>t, DP_on \<sharp> D E, {}, R, E)"
  shows "SN (relstep R E)"
proof -
  define RR where "RR = ({(l,r). root l \<noteq> None \<and> root r \<noteq> None \<and> the (root l) \<in> D \<and> the (root r) \<in> D} :: ('f,'v)trs)" 
  let ?Rext = "R\<^sub>e\<^sub>x\<^sub>t \<inter> RR"
  have finP': "finite_rel_dpp (\<sharp> ?Rext, DP_on \<sharp> D E, {}, R, E)"
    by (rule finite_rel_dpp_pairs_mono[OF finP'], auto simp: dir_image_def)
  have R_ext: "is_ext_trs R F\<^sub>A F\<^sub>C ?Rext" unfolding is_ext_trs_def
  proof (intro allI impI conjI)
    fix l r f
    assume lr: "(l,r) \<in> R" "f \<in> F\<^sub>A" "root l = Some (f,2)"
    note R_ext = R_ext[unfolded is_ext_trs_def, rule_format, OF this]
    from lr(1,3) have f: "(f,2) \<in> D" "(f,Suc (Suc 0)) \<in> D" unfolding defined_def D_def by auto
    from R_ext obtain x where x: "x \<notin> vars_rule (l,r)" and lr: "ext_AC_rule f (l,r) (Var x) \<in> R\<^sub>e\<^sub>x\<^sub>t" by auto
    from lr f have "ext_AC_rule f (l,r) (Var x) \<in> ?Rext" unfolding RR_def ext_AC_rule_def by auto
    with x show "\<exists>x. x \<notin> vars_rule (l, r) \<and> ext_AC_rule f (l, r) (Var x) \<in> R\<^sub>e\<^sub>x\<^sub>t \<inter> RR" by blast
    assume "f \<notin> F\<^sub>C"
    with R_ext show "\<exists>x y z. x \<notin> vars_rule (l, r) \<and>
              y \<notin> vars_rule (l, r) \<and>
              z \<notin> vars_rule (l, r) \<and>
              x \<noteq> y \<and>
              (Fun f [Var z, l], Fun f [Var z, r]) \<in> R\<^sub>e\<^sub>x\<^sub>t \<inter> RR \<and>
              (Fun f [Fun f [Var x, l], Var y], Fun f [Fun f [Var x, r], Var y]) \<in> R\<^sub>e\<^sub>x\<^sub>t \<inter> RR"
      unfolding RR_def using f by auto
  qed
  let ?DRE = "{f. defined (R \<union> E) f}"
  define DD where "DD = {(shp f,n) | f n. defined R (f,n)}"
  define C where "C = {(shp f,n) | f n. defined (R \<union> E) (f,n)} - DD"
  have C: "\<And>f. f \<in> C \<Longrightarrow> \<not> defined (R \<union> E) f"
    unfolding C_def using shp_not_defined by auto
  have CD: "C \<inter> DD = {}" unfolding C_def by auto
  interpret AC_C_theory E "F\<^sub>C - F\<^sub>A" by fact
  {
    fix D E and s t :: "('f,'v)term"
    assume "(s,t) \<in> DP_on \<sharp> D E"
    then have "root t \<in> Some ` {(shp f,n) | f n. (f,n) \<in> D}"
      unfolding DP_on_def by force
  } note root_t = this
  {
    fix D and s t :: "('f,'v)term"
    assume st: "(s,t) \<in> DP_on \<sharp> D E"
    then obtain l r h where lr: "(l,r) \<in> E" and s: "s = \<sharp> l" and rh: "r \<unrhd> h" and t: "t = \<sharp> h"
      and h: "is_Fun h" unfolding DP_on_def by auto
    from ac_ruleD[OF lr] obtain f where l: "funas_term l = {(f,2)}" and r: "funas_term r = {(f,2)}" by auto
    then have rs: "root s = Some (shp f,2)" unfolding s by (cases l, auto)
    from supteq_imp_funas_term_subset[OF rh] r have "funas_term h \<subseteq> {(f,2)}" by simp
    with h have rt: "root t = Some (shp f,2)" unfolding t by (cases h, auto)
    from root_t[OF st, unfolded rt, folded rs] rs[folded rt] 
    have "root s \<in> Some ` {(\<sharp> f, n) |f n. (f, n) \<in> D}" "root t = root s" by auto
  } note root_s_E = this
  {
    fix s t
    assume "(s, t) \<in> DP_on \<sharp> D E" 
    from root_t[OF this] root_s_E[OF this]
    have "root s \<in> Some ` DD \<and> root t \<in> Some ` DD" unfolding DD_def D_def by auto
  } note DP_D_E = this
  {
    fix s t D
    assume st: "(s, t) \<in> DP_on \<sharp> D R"
    then obtain l r where lr: "(l,r) \<in> R" and s: "s = \<sharp> l" unfolding DP_on_def by auto
    from wf lr obtain f ls where l: "l = Fun f ls" unfolding wf_trs_def by (cases l, auto)
    from l lr have "defined R (f,length ls)" unfolding defined_def by auto
    then have "root s \<in> Some ` DD" unfolding DD_def s l by auto
  } note root_s_R = this
  note fin_step = defined_symbol_finite_rel_dpp[OF _ _ _ DP_D_E _ CD C wf]
  show ?thesis
  proof (rule SN_relstep_via_finite_rel_dpps[OF R_ext E_is_AC AC EF\<^sub>A
      fin_step[OF finP]
      fin_step[OF finP']])
    fix s t
    assume st: "(s, t) \<in> DP_on \<sharp> ?DRE R - DP_on \<sharp> D R"
    then obtain l r h where lr: "(l,r) \<in> R" and s: "s = \<sharp> l" and rh: "r \<unrhd> h" 
      and lh: "\<not> (l \<rhd> h)" and t: "t = \<sharp> h"
      and h: "is_Fun h" "root h \<in> Some ` ?DRE" unfolding DP_on_def by auto
    from st have st': "(s, t) \<in> DP_on \<sharp> ?DRE R" by auto
    note root_t = root_t[OF this]
    note root_s = root_s_R[OF st']
    {
      assume "root t \<in> Some ` DD"
      then have "root h \<in> Some ` D" unfolding t DD_def D_def using inj_shp h by (cases h, auto)
      with lr s rh lh h(1) t have "(s,t) \<in> DP_on \<sharp> D R" unfolding DP_on_def
        by (cases h, auto)
      with st have False by auto
    }
    with root_t have "root t \<in> Some ` C" unfolding C_def by auto
    with root_s show "root s \<in> Some ` DD \<and> root t \<in> Some ` C" by auto
  next
    fix s t
    assume "(s, t) \<in> DP_on \<sharp> D R"
    with root_t[OF this] root_s_R[OF this]
    show "root s \<in> Some ` DD \<and> root t \<in> Some ` DD" unfolding DD_def D_def by auto
  next
    fix s t
    assume st: "(s, t) \<in> DP_on \<sharp> ?DRE E - DP_on \<sharp> D E"
    then have "(s,t) \<in> DP_on \<sharp> ?DRE E" by auto
    from root_s_E[OF this] have s_t: "root s = root t" "root s \<in> Some ` {(\<sharp> f, n) |f n. (f, n) \<in> ?DRE}"
      by auto
    {
      assume "root s \<in> Some ` DD"
      with s_t have rt: "root t \<in> Some ` DD" by auto
      from st obtain l r h where lr: "(l,r) \<in> E" and s: "s = \<sharp> l" and rh: "r \<unrhd> h" 
        and lh: "\<not> (l \<rhd> h)" and t: "t = \<sharp> h"
        and h: "is_Fun h" "root h \<in> Some ` ?DRE" unfolding DP_on_def by auto
      from rt[unfolded t DD_def] have "root h \<in> Some ` D" unfolding D_def using inj_shp h by (cases h, auto)
      with lr s rh lh h(1) t have "(s,t) \<in> DP_on \<sharp> D E" unfolding DP_on_def
        by (cases h, auto)
      with st have False by auto
    }
    with s_t(2) have "root s \<in> Some ` C" unfolding C_def by auto
    with s_t(1) 
    show "root s \<in> Some ` C \<and> root t \<in> Some ` C" by auto
    then show "root s \<in> Some ` C \<and> root t \<in> Some ` C" .
  next
    fix s t
    assume st: "(s, t) \<in> dir_image ?Rext \<sharp>"
    then obtain l r where lr: "(l,r) \<in> RR" and s: "s = \<sharp> l" and t: "t = \<sharp> r" 
      unfolding dir_image_def by auto
    then show "root s \<in> Some ` DD \<and> root t \<in> Some ` DD" unfolding s t DD_def RR_def D_def
      by (cases l; cases r, auto)
  qed auto
qed
end

end (* relative dp *)

end (*t theory *)
