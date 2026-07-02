theory SPO
  imports
    Weighted_Path_Order.WPO
    Lexicographic_Extension_More
begin

text \<open>utilities for lex_ext\<close>

definition order_pair_eq where
  "order_pair_eq R = (\<lambda> s t. (R s t, s = t))"

lemma order_pair_eq_compat:
  assumes "R s t \<longrightarrow> R t u \<longrightarrow> R s u"
  shows
    "(snd (order_pair_eq R s t) \<and> fst (order_pair_eq R t u) \<longrightarrow> fst (order_pair_eq R s u)) \<and>
    (fst (order_pair_eq R s t) \<and> snd (order_pair_eq R t u) \<longrightarrow> fst (order_pair_eq R s u)) \<and>
    (snd (order_pair_eq R s t) \<and> snd (order_pair_eq R t u) \<longrightarrow> snd (order_pair_eq R s u)) \<and>
    (fst (order_pair_eq R s t) \<and> fst (order_pair_eq R t u) \<longrightarrow> fst (order_pair_eq R s u))"
  using assms
  unfolding order_pair_eq_def
  by (intro conjI impI; auto)

lemma lex_ext_trans':
  assumes "\<forall> s \<in> set ss . \<forall> t \<in> set ts. \<forall> u \<in> set us. 
    (snd (f s t) \<and> fst (f t u) \<longrightarrow> fst (f s u)) \<and>
    (fst (f s t) \<and> snd (f t u) \<longrightarrow> fst (f s u)) \<and>
    (snd (f s t) \<and> snd (f t u) \<longrightarrow> snd (f s u)) \<and>
    (fst (f s t) \<and> fst (f t u) \<longrightarrow> fst (f s u))"
  shows "(fst (lex_ext f m ss ts) \<and> fst (lex_ext f m ts us) \<longrightarrow> fst (lex_ext f m ss us))"
  using lex_ext_compat
  by (smt (verit, best) assms)

lemma lex_ext_trans:
  assumes
    "\<forall> s \<in> set ss . \<forall> t \<in> set ts. \<forall> u \<in> set us. R s t \<longrightarrow> R t u \<longrightarrow> R s u"
  shows "(fst (lex_ext (order_pair_eq R) m ss ts)  \<and> fst (lex_ext (order_pair_eq R) m ts us)) \<longrightarrow>
          fst (lex_ext (order_pair_eq R) m ss us)"
  using lex_ext_trans' order_pair_eq_compat
  by (smt (verit, ccfv_threshold) assms lex_ext_trans')

lemma lex_ext_incr: (* incrementality? *)
  assumes
    "\<forall> t \<in> set ts . \<forall> u \<in> set us. R t u \<longrightarrow> Q t u"
    "fst (lex_ext (order_pair_eq (\<lambda> t u. R t u)) n ts us)"
  shows 
    "fst (lex_ext (order_pair_eq (\<lambda> t u. Q t u)) n ts us)"
  using assms unfolding order_pair_eq_def lex_ext_iff by auto

text \<open>an upperbound of the arities\<close>
locale spo =
  fixes n :: nat 
    and S NS :: "('f, 'v) term rel"
begin

fun spo :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" 
  where
    "spo (Var _) _ = False" |
    "spo (Fun f ss) t = ((\<exists> si \<in> set ss. si = t \<or> spo si t) \<or>
      (case t of
        Var _ \<Rightarrow> False
      | Fun g ts \<Rightarrow> (\<forall> tj \<in> set ts. spo (Fun f ss) tj) \<and>
                     (((Fun f ss), t) \<in> S \<or>
                      (((Fun f ss), t) \<in> NS \<and> fst (lex_ext (\<lambda> s' t'. (spo s' t', s' = t')) n ss ts)))))"


declare spo.simps [simp del]

text \<open>The abbreviation of >_spo. Note that the paper uses \<sqsupset> for S in this formalization.\<close>
abbreviation spo_s (infix "\<sqsupset>" 50) where "s \<sqsupset> t \<equiv> spo s t"

abbreviation "SPO \<equiv> {(s,t). s \<sqsupset> t}"

lemma spo_fun: "s \<sqsupset> t \<Longrightarrow> \<exists> f ss . s = Fun f ss"
  using spo.elims(2) by fastforce

definition spo1a
  where
    "spo1a s t \<longleftrightarrow>  (\<exists> f ss si . s = Fun f ss \<and>  si \<in> set ss \<and> si = t)"

definition spo1b
  where
    "spo1b s t \<longleftrightarrow>  (\<exists> f ss si . s = Fun f ss \<and>  si \<in> set ss \<and> si \<sqsupset> t)"

definition spo2a
  where
    "spo2a s t \<longleftrightarrow> 
    (\<exists> f ss g ts. s = Fun f ss \<and> t = Fun g ts \<and>
                  (\<forall> tj \<in> set ts. spo s tj) \<and> (s, t) \<in> S)"

definition spo2b
  where
    "spo2b s t \<longleftrightarrow>
    (\<exists> f ss g ts. s = Fun f ss \<and> t = Fun g ts \<and>
                  (\<forall> tj \<in> set ts. spo s tj) \<and> (s, t) \<in> NS \<and>
                  fst (lex_ext (\<lambda> s' t'. (spo s' t', s' = t')) n ss ts))"

lemma spo_if: "s \<sqsupset> t \<Longrightarrow> spo1a s t \<or> spo1b s t \<or> spo2a s t \<or> spo2b s t"
proof -
  assume *: "s \<sqsupset> t"
  then obtain f ss where "s = Fun f ss" using spo_fun by blast
  note [simp] = this
  show ?thesis
  proof (cases t)
    case (Var)
    then have "\<exists> si \<in> set ss. si = t \<or> spo si t"
      using * by (simp add: spo.simps)
    then obtain si where "si \<in> set ss" "si = t \<or> spo si t" by blast
    then show ?thesis
    proof (elim disjE, goal_cases)
      case 1
      then have "spo1a s t" using spo1a_def by fastforce
      then show ?case by blast
    next
      case 2
      then have "spo1b s t" using spo1b_def by fastforce
      then show ?case by blast
    qed
  next
    case (Fun g ts)
    note [simp] = this
    show ?thesis
    proof (cases "\<exists> si \<in> set ss. si = t \<or> spo si t")
      case True
      then obtain si where "si \<in> set ss" "si = t \<or> spo si t" by blast
      then show ?thesis
      proof (elim disjE, goal_cases)
        case 1
        then have "spo1a s t" using spo1a_def by fastforce
        then show ?case by blast
      next
        case 2
        then have "spo1b s t" using spo1b_def by fastforce
        then show ?case by blast
      qed
    next
      case False
      then have args: "\<forall> tj \<in> set ts. spo (Fun f ss) tj"
        using * by (simp add: spo.simps)  
      have "(s, t) \<in> S \<or>
            ((s, t) \<in> NS \<and> fst (lex_ext (\<lambda> s' t'. (spo s' t', s' = t')) n ss ts))"
        using * False by (simp add: spo.simps)
      then show ?thesis
      proof (elim disjE, goal_cases)
        case 1
        then have "spo2a s t" using args spo2a_def by auto
        then show ?case by blast
      next
        case 2
        then have "spo2b s t" using args spo2b_def by force
        then show ?case by blast
      qed
    qed
  qed
qed

lemma spo_only_if:  "(spo1a s t \<or> spo1b s t \<or> spo2a s t \<or> spo2b s t) \<Longrightarrow> s \<sqsupset> t"
proof (elim disjE, goal_cases)
  case 1
  then obtain f ss si where "s = Fun f ss" "si \<in> set ss" "si = t"
    unfolding spo1a_def by blast
  then show ?case using spo.simps(2) by blast
next
  case 2
  then obtain f ss si where "s = Fun f ss" "si \<in> set ss" "spo si t"
    unfolding spo1b_def by blast
  then show ?case using spo.simps(2) by blast
next
  case 3
  then obtain f ss g ts
    where "s = Fun f ss" " t = Fun g ts"
          "\<forall> tj \<in> set ts. spo s tj"  "(s, t) \<in> S"
    unfolding spo2a_def by blast
  then show ?case by (simp add: spo.simps)
next
  case 4
  then obtain f ss g ts
    where "s = Fun f ss" " t = Fun g ts"
          "\<forall> tj \<in> set ts. spo s tj"  "(s, t) \<in> NS"
          "fst (lex_ext (\<lambda> s' t'. (spo s' t', s' = t')) n ss ts)"
    unfolding spo2b_def by blast
  then show ?case by (simp add: spo.simps)
qed

(* TODO: refactor proofs using this *)
lemma spo_iff:  "s \<sqsupset> t \<longleftrightarrow> (spo1a s t \<or> spo1b s t \<or> spo2a s t \<or> spo2b s t)"
  using spo_if spo_only_if by blast

lemma subterm_spo_arg_var:
  "x \<in> vars_term (Fun f ss) \<Longrightarrow> Fun f ss \<sqsupset> Var x"
proof (induct "Fun f ss" arbitrary: f ss
       rule: wf_induct[OF wf_measure[of "size"]])
  case 1
  obtain si where "si \<in> set ss" "x \<in> vars_term si"
    using "1.prems" by fastforce
  have "\<exists> si \<in> set ss. (si = Var x \<or> si \<sqsupset> Var x)"
  proof (cases si)
    case Var
    then have "si = Var x" using \<open>x \<in> vars_term si\<close> by force
    thus ?thesis using \<open>si \<in> set ss\<close> by auto
  next
    case Fun
    then have "si \<sqsupset> Var x" using 1
      by (metis One_nat_def \<open>si \<in> set ss\<close> \<open>x \<in> vars_term si\<close> add.commute in_measure plus_1_eq_Suc size_simp1 term.size(4))
    thus ?thesis using \<open>si \<in> set ss\<close> by blast
  qed
  thus "Fun f ss \<sqsupset> Var x" by (auto simp: spo.simps) 
qed

lemma subterm_spo_arg:
  assumes "si \<in> set ss"
  shows "Fun f ss \<sqsupset> si"
proof (cases si)
  case (Var _)
  then show ?thesis using subterm_spo_arg_var assms by fastforce
next
  case (Fun )
  have "\<exists> s \<in> set ss. (s = si \<or> s \<sqsupset> si)" using assms by blast
  then show ?thesis using Fun by (auto simp: spo.simps)
qed

end

declare spo.spo.simps[code]

lemma spo_on_subterms: "spo.spo n S NS s t \<longrightarrow>
   (\<forall> u \<unlhd> s. \<forall> v \<unlhd> t. (u, v) \<in> S \<longrightarrow> (u, v) \<in> S') \<longrightarrow>
   (\<forall> u \<unlhd> s. \<forall> v \<unlhd> t. (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS') \<longrightarrow>
  spo.spo n S' NS' s t"
proof (induct "(s, t)" arbitrary: s t rule: wf_induct[OF wf_measure[of "\<lambda> (s, t). size s + size t"]])
  case (1 s t)
  then have IH:
    "\<forall> s' t' . size s' + size t' < size s + size t \<longrightarrow>
     spo.spo n S NS s' t' \<longrightarrow>
     (\<forall> u \<unlhd> s'. \<forall> v \<unlhd> t'. (u, v) \<in> S \<longrightarrow> (u, v) \<in> S') \<longrightarrow>
     (\<forall> u \<unlhd> s'. \<forall> v \<unlhd> t'. (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS') \<longrightarrow>
     spo.spo n S' NS' s' t'"
    by auto
  show ?case
  proof (intro impI)
    assume spo_s_t: "spo.spo n S NS s t"
    assume SS': "\<forall> u \<unlhd> s. \<forall> v \<unlhd> t. (u, v) \<in> S \<longrightarrow> (u, v) \<in> S'"
    assume NSNS': "\<forall> u \<unlhd> s. \<forall> v \<unlhd> t. (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS'"
    from spo_s_t have "spo.spo1a s t \<or> spo.spo1b n S NS s t \<or> spo.spo2a n S NS s t \<or> spo.spo2b n S NS s t"
      unfolding spo.spo_iff by simp
    thus "spo.spo n S' NS' s t"
    proof (elim disjE, goal_cases)
      case 1
      thus ?case using spo.spo_iff by blast
    next
      case 2
      then obtain f si ss where *:  "s = Fun f ss" " si \<in> set ss" "spo.spo n S NS si t"
        unfolding spo.spo1b_def by blast
      moreover
      have "size si + size t < size s + size t" using *
        by (simp add: size_simp1)
      moreover
      have "(\<forall> u \<unlhd> si. \<forall> v \<unlhd> t. (u, v) \<in> S \<longrightarrow> (u, v) \<in> S')"
        using * SS' by auto
      moreover
      have "(\<forall> u \<unlhd> si. \<forall> v \<unlhd> t. (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS')"
        using * NSNS' by auto
      ultimately have "spo.spo n S' NS' si t" using IH by blast
      then have "spo.spo1b n S' NS' s t" using * spo.spo1b_def by blast
      thus ?case using spo.spo_iff by blast
    next
      case 3
      then obtain f ss g ts where *: "s = Fun f ss" "t = Fun g ts" "\<forall> tj \<in> set ts. spo.spo n S NS s tj" "(s, t) \<in> S"
        unfolding spo.spo2a_def by blast
      moreover
      have "\<forall> tj \<in> set ts. size s + size tj < size s + size t" using *
        by (simp add: size_simp1)
      moreover
      have "\<forall> tj \<in> set ts. (\<forall> u \<unlhd> s. \<forall> v \<unlhd> tj. (u, v) \<in> S \<longrightarrow> (u, v) \<in> S')"
        using * SS' by auto
      moreover
      have "\<forall> tj \<in> set ts. (\<forall> u \<unlhd> s. \<forall> v \<unlhd> tj. (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS')"
        using * NSNS' by auto
      ultimately have "\<forall> tj \<in> set ts. spo.spo n S' NS' s tj" using IH by blast
      moreover
      have "(s, t) \<in> S'" using * SS' by simp
      ultimately have "spo.spo2a n S' NS' s t" using * spo.spo2a_def by fast
      thus ?case using spo.spo_iff by blast
    next
      case 4
      then obtain f ss g ts where *: "s = Fun f ss" "t = Fun g ts" "\<forall> tj \<in> set ts. spo.spo n S NS s tj"
        "(s, t) \<in> NS" "fst (lex_ext (\<lambda> s' t'. (spo.spo n S NS s' t', s' = t')) n ss ts)"
        unfolding spo.spo2b_def by blast
      moreover
      have "\<forall> tj \<in> set ts. size s + size tj < size s + size t" using *
        by (simp add: size_simp1)
      moreover
      have "\<forall> tj \<in> set ts. (\<forall> u \<unlhd> s. \<forall> v \<unlhd> tj. (u, v) \<in> S \<longrightarrow> (u, v) \<in> S')"
        using * SS' by auto
      moreover
      have "\<forall> tj \<in> set ts. (\<forall> u \<unlhd> s. \<forall> v \<unlhd> tj. (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS')"
        using * NSNS' by auto
      ultimately have "\<forall> tj \<in> set ts. spo.spo n S' NS' s tj" using IH by blast
      moreover
      have "(s, t) \<in> NS'" using * NSNS' by simp
      moreover
      have "fst (lex_ext (\<lambda> s' t'. (spo.spo n S' NS' s' t', s' = t')) n ss ts)"
      proof (rule lex_ext_incr[unfolded order_pair_eq_def, of _ _ "spo.spo n S NS"])
        show "\<forall>si \<in>set ss. \<forall>tj\<in>set ts. spo.spo n S NS si tj \<longrightarrow> spo.spo n S' NS' si tj"
        proof (intro ballI impI)
          fix si tj
          assume **: "si \<in> set ss" "tj \<in> set ts" "spo.spo n S NS si tj"
          have "size si + size tj < size s + size t"
            using * ** size_simp1
            by (metis add.right_neutral add_Suc_right add_le_less_mono less_imp_le_nat term.size(4))
          moreover
          have "(\<forall> u \<unlhd> si. \<forall> v \<unlhd> tj. (u, v) \<in> S \<longrightarrow> (u, v) \<in> S')"
            using * ** SS' by auto
          moreover
          have "(\<forall> u \<unlhd> si. \<forall> v \<unlhd> tj. (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS')"
            using * ** NSNS' by auto
          ultimately show "spo.spo n S' NS' si tj" using IH ** by presburger
        qed
        show "fst (lex_ext (\<lambda>s' t'. (spo.spo n S NS s' t', s' = t')) n ss ts)"
          using * by blast
      qed
      ultimately have "spo.spo2b n S' NS' s t" using * spo.spo2b_def by fast
      thus ?case using spo.spo_iff by blast
    qed
  qed
qed

locale spo_with_basic_assms = spo + order_pair +
  constrains S :: "('f, 'v) term rel" and NS :: _ and n :: nat
  assumes subst_S: "(s,t) \<in> S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S"
    and subst_NS: "(s,t) \<in> NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS"
    and irrefl_S: "irrefl S"
    (* NOTE: S_imp_NS: "S \<subseteq> NS" is assumed in WPO *)
begin

lemma spo_trans: "s \<sqsupset> t \<Longrightarrow> t \<sqsupset> u \<Longrightarrow> s \<sqsupset> u"
proof (induct "(s, t, u)" arbitrary: s t u
       rule: wf_induct[OF wf_measure[of "\<lambda> (s, t, u) . size s + size t + size u"]])
  case (1 s t u)
  then have
    IH: "\<And> s' t' u'. size s' + size t' + size u' < size s + size t + size u \<longrightarrow>
                     s' \<sqsupset> t' \<longrightarrow> t' \<sqsupset> u' \<longrightarrow> s' \<sqsupset> u'"
    by auto
  obtain f ss where "s = Fun f ss" using 1 spo_fun by meson
  note [simp] = this
  obtain g ts where "t = Fun g ts" using 1 spo_fun by meson
  note [simp] = this
  show ?case
  proof (cases "\<exists> si \<in> set ss. (si = t \<or> si \<sqsupset> t)")
    case True
    then obtain si where "si \<in> set ss" "si = t \<or> si \<sqsupset> t" by auto
    then show ?thesis
    proof (elim disjE, goal_cases)
      case 1
      then have "si \<sqsupset> u" using "1.prems"(2) by auto
      then have "\<exists> si \<in> set ss. (si = u \<or> si \<sqsupset> u)" using "1"(1) by blast
      then show ?case by (auto simp: spo.simps)
    next
      case 2
      then have "size si + size t + size u < size s + size t + size u"
        using size_simp1 by auto
      then have "si \<sqsupset> u" using "1.prems"(2) "2"(2) IH by blast
      then have "\<exists> si \<in> set ss. (si = u \<or> si \<sqsupset> u)"
        using "2"(1) by blast
      then show ?case by (auto simp: spo.simps)
    qed
  next
    case False
    then have s_t_rest:
      "(\<forall> tj \<in> set ts. s \<sqsupset> tj) \<and>
          ((s, t) \<in> S \<or> ((s, t) \<in> NS \<and> fst (lex_ext (\<lambda> s' t'. (s' \<sqsupset> t', s' = t')) n ss ts)))"
      using \<open>s \<sqsupset> t\<close> by (auto simp: spo.simps)
    then have "(\<forall> tj \<in> set ts. s \<sqsupset> tj)" by auto
    have s_t_S_or_NS:
      "((s, t) \<in> S \<or> ((s, t) \<in> NS \<and> fst (lex_ext (\<lambda> s' t'. (s' \<sqsupset> t', s' = t')) n ss ts)))"
      using s_t_rest by auto
    then show ?thesis
    proof (cases "\<exists> tj \<in> set ts. (tj = u \<or> tj \<sqsupset> u)")
      case True
      then obtain tj where "tj \<in> set ts" "tj = u \<or> tj \<sqsupset> u" by auto
      then have "s \<sqsupset> tj" using \<open>tj \<in> set ts\<close> \<open>\<forall> tj \<in> set ts. s \<sqsupset> tj\<close> by auto
      from \<open>tj = u \<or> tj \<sqsupset> u\<close> show ?thesis
      proof (elim disjE, goal_cases)
        case 1
        then show ?case using 1 \<open>s \<sqsupset> tj\<close> by auto
      next
        case 2
        have "size s + size tj + size u < size s + size t + size u"
          by (simp add: \<open>tj \<in> set ts\<close> size_simp1)
        then show ?case using IH[of s tj u] 2 \<open>s \<sqsupset> tj\<close> by auto
      qed
    next
      case False
      then obtain h us where "u = Fun h us"
      proof (cases u)
        case (Var x1)
        then have "\<not> (t \<sqsupset> u)" using False by (auto simp: spo.simps)
        then show ?thesis
          using "1.prems"(2) by force
      next
        case (Fun h us)
        then show ?thesis by fact
      qed
      note [simp] = this
      have t_u_rest:
        "(\<forall> uk \<in> set us. t \<sqsupset> uk) \<and>
            ((t, u) \<in> S \<or> ((t, u) \<in> NS \<and> fst (lex_ext (\<lambda> t' u'. (t' \<sqsupset> u', t' = u')) n ts us)))"
        using \<open>t \<sqsupset> u\<close> False by (auto simp: spo.simps)
      then have "\<forall> uk \<in> set us. t \<sqsupset> uk" by auto
      have t_u_S_or_NS:
        "((t, u) \<in> S \<or> ((t, u) \<in> NS \<and> fst (lex_ext (\<lambda> s' t'. (s' \<sqsupset> t', s' = t')) n ts us)))"
        using t_u_rest by auto
      have "\<forall> uk \<in> set us. size s + size t + size uk < size s + size t + size u"
          by (simp add: size_simp1)
      then have "\<forall> uk \<in> set us. s \<sqsupset> uk" using \<open>s \<sqsupset> t\<close> \<open>\<forall> uk \<in> set us. t \<sqsupset> uk\<close> IH[of s t] by auto
      from s_t_S_or_NS t_u_S_or_NS show ?thesis
      proof (elim disjE, goal_cases)
        case 1
        then have "(s, u) \<in> S" by (rule trans_S_point)
        then show ?case using \<open>\<forall> uk \<in> set us. s \<sqsupset> uk\<close> by (auto simp: spo.simps)
      next
        case 2
        then have "(s, u) \<in> S" using compat_S_NS_point by blast
        then show ?case using \<open>\<forall> uk \<in> set us. s \<sqsupset> uk\<close> by (auto simp: spo.simps)
      next
        case 3
        then have "(s, u) \<in> S" using compat_NS_S_point by blast
        then show ?case using \<open>\<forall> uk \<in> set us. s \<sqsupset> uk\<close> by (auto simp: spo.simps)
      next
        case 4
        then have "(s, u) \<in> NS" using trans_NS_point by blast
        have "\<forall> s' \<in> set ss . \<forall> t' \<in> set ts. \<forall> u' \<in> set us.
                size s' + size t' + size u' < size s + size t + size u"
          by (metis \<open>s = Fun f ss\<close> \<open>t = Fun g ts\<close> \<open>u = Fun h us\<close> add_strict_mono supt.intros(1) supt_size)
        then have "\<forall> s' \<in> set ss . \<forall> t' \<in> set ts. \<forall> u' \<in> set us.
                s' \<sqsupset> t' \<longrightarrow> t' \<sqsupset> u' \<longrightarrow> s' \<sqsupset> u'" using IH by blast
        then have "fst (lex_ext (\<lambda>s' u'. (s' \<sqsupset> u', s' = u')) n ss us)"
          using lex_ext_trans 4 unfolding order_pair_eq_def
          by blast
        then show ?case using \<open>(s, u) \<in> NS\<close> \<open>\<forall> uk \<in> set us. s \<sqsupset> uk\<close> by (auto simp: spo.simps)
      qed
    qed
  qed
qed

lemma spo_irrefl': "s \<sqsupset> s \<Longrightarrow> False"
proof (induct s rule: wf_induct[OF wf_measure[of "\<lambda> s. size s"]])
  case (1 s)
  assume "s \<sqsupset> s"
  then have IH: "\<forall> s' t' . size s' < size s \<longrightarrow> \<not> (s' \<sqsupset> s')" using 1 by auto
  show False
  proof (cases rule: spo.spo.cases[of "(s, s)"])
    case (1)
    then have "\<not> (s \<sqsupset> s)" by (auto simp: spo.simps)
    thus ?thesis using \<open>s \<sqsupset> s\<close> by auto
  next
    case (2 f ss)
    then have "s = Fun f ss" by auto
    note [simp] = this
    show ?thesis
    proof (cases "(\<exists> si \<in> set ss. si = s \<or> spo si s)")
      case True
      then obtain si where "si \<in> set ss" "(si = s \<or> si \<sqsupset> s)" by auto
      then show ?thesis
      proof (elim disjE, goal_cases)
        case 1
        then have "si \<sqsupset> si" using \<open>s \<sqsupset> s\<close> by auto
        have "size si < size s" using "1"(1) "1"(2) by auto
        then have False using IH \<open>si \<sqsupset> si\<close> by auto
        then show ?case by blast
      next
        case 2
        then have "si \<sqsupset> s" by auto
        have "s \<sqsupset> si" using \<open>si \<in> set ss\<close> by (auto simp: spo.simps)
        then have "si \<sqsupset> si" using \<open>si \<sqsupset> s\<close> spo_trans[of si s si] by auto
        have "size si < size s"
          using "2"(1) \<open>s = Fun f ss\<close> supt_size by blast
        then have False using IH \<open>si \<sqsupset> si\<close> by auto
        then show ?case by blast
      qed
    next
      case False
      then have "\<not> (\<exists> si \<in> set ss. si = s \<or> si \<sqsupset> s)" by blast
      note [simp] = this
      then show ?thesis
      proof (cases "\<forall> si \<in> set ss. s \<sqsupset> si")
        case True
        have "(s, s) \<in> S \<or> ((s, s) \<in> NS \<and> fst (lex_ext (\<lambda> s s'. (s \<sqsupset> s', s = s')) n ss ss))"
            using \<open>s \<sqsupset> s\<close> True False spo.simps(2) by auto
        then show ?thesis
        proof (elim disjE, goal_cases)
          case 1
          then show ?case using irrefl_S by (simp add: irreflD)
        next
          case 2
          then have "fst (lex_ext (\<lambda> s s'. (s \<sqsupset> s', s = s')) n ss ss)" by auto
          then have "\<exists> si \<in> set ss. si \<sqsupset> si"
            by (smt (verit) fst_conv lex_ext_iff nth_mem order_less_irrefl)
          then obtain si where "si \<in> set ss" "si \<sqsupset> si" by auto
          then have "size si < size s"
            using \<open>s = Fun f ss\<close> supt_size by blast
          then have False using IH \<open>si \<sqsupset> si\<close> by auto
          then show ?case by blast
        qed
      next
        case False
        then have "\<not> (s \<sqsupset> s)" using \<open>\<not> (\<exists> si \<in> set ss. si = s \<or> spo si s)\<close>
          by (auto simp: spo.simps) 
        then show ?thesis using \<open>s \<sqsupset> s\<close> by auto
      qed
    qed
  qed
qed

lemma spo_irrefl: "\<not> s \<sqsupset> s"
  using spo_irrefl' by blast

lemma lex_ext_fst_map:
  assumes
    "fst (lex_ext (\<lambda> a b. (R a b, a = b)) n as bs)"
    "\<forall> a \<in> set as. \<forall> b \<in> set bs. (R a b \<longrightarrow> R (f a) (f b))"
  shows "fst (lex_ext (\<lambda> a b. (R a b, a = b)) n (map f as) (map f bs))"
  by (rule stri_lex_ext_map[OF _ _ assms(1)], insert assms, auto)

lemma spo_stable: "s \<sqsupset> t \<Longrightarrow> s \<cdot> \<delta> \<sqsupset> t \<cdot> \<delta>"
proof (induct "(s, t)" arbitrary: s t rule: wf_induct[OF wf_measure[of "\<lambda> (s, t). size s + size t"]])
  case (1 s t)
  then have IH: "\<forall> s' t' . size s' + size t' < size s + size t \<longrightarrow> s' \<sqsupset> t' \<longrightarrow> s' \<cdot> \<delta> \<sqsupset> t' \<cdot> \<delta>"
    by auto
  assume "s \<sqsupset> t"
  let ?subst = "(\<lambda> u. u \<cdot> \<delta>)"
  from 1 show "(s \<cdot> \<delta>) \<sqsupset> (t \<cdot> \<delta>)"
  proof (cases rule: spo.spo.cases[of "(s, t)"])
    case (1 _ _)
    then have "\<not> (s \<sqsupset> t)" by (auto simp: spo.simps)
    then show ?thesis using \<open>s \<sqsupset> t\<close> by blast  
  next
    case (2 f ss)
    then have "s = Fun f ss" by auto
    note [simp] = this
    show ?thesis
    proof (cases "(\<exists> si \<in> set ss. si = t \<or> spo si t)")
      case True
      then obtain si where "si \<in> set ss" "(si = t \<or> si \<sqsupset> t)" by auto
      then have si_subst_in_args: "si \<cdot> \<delta> \<in> set (map ?subst ss)" by simp
      from \<open>si = t \<or> spo si t\<close> show ?thesis
      proof (elim disjE, goal_cases)
        case 1
        then have "si \<cdot> \<delta> = t \<cdot> \<delta>" by auto
        thus ?case using 2 si_subst_in_args by (auto simp: spo.simps)
      next
        case 2
        then have "size si + size t < size s + size t"
          by (simp add: \<open>si \<in> set ss\<close> size_simp1)
        then have "si \<cdot> \<delta> \<sqsupset> t \<cdot> \<delta>" using IH 2 by auto
        then show ?case using si_subst_in_args by (auto simp: spo.simps)
      qed
    next
      case False
      then have "\<not> (\<exists> si \<in> set ss. si = t \<or> spo si t)" by blast
      note [simp] = this
      then show ?thesis
      proof (cases t)
        case (Var y)
        then have "t = Var y" by auto
        then have "\<not> (s \<sqsupset> t)" using 2 False by (auto simp: spo.simps)
        then show ?thesis using \<open>s \<sqsupset> t\<close> by blast
      next
        case (Fun g ts)
        then have "t = Fun g ts" by auto
        note [simp] = this
        have tj_size: "\<forall> tj \<in> set ts . size s + size tj < size s + size t"
          by (simp add: size_simp1)
        then show ?thesis
        proof (cases "\<forall> tj \<in> set ts. s \<sqsupset> tj")
          case True
          then have "\<forall> tj \<in> set ts. s \<cdot> \<delta> \<sqsupset> tj \<cdot> \<delta>" using IH tj_size by blast
          then have tj_subst: "\<forall> tj' \<in> set (map ?subst ts). s \<cdot> \<delta> \<sqsupset> tj'" by auto
          note [simp] = this
          have "(s, t) \<in> S \<or> ((s, t) \<in> NS \<and> fst (lex_ext (\<lambda> s' t'. (spo s' t', s' = t')) n ss ts))"
            using \<open>s \<sqsupset> t\<close> True False spo.simps(2) by auto
          then show ?thesis
          proof (elim disjE, goal_cases)
            case 1
            then have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> S" using subst_S by blast
            then show ?case using tj_subst by (auto simp: spo.simps)
          next
            case 2
            then have "(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> NS" using subst_NS by blast
            have "\<forall> s' \<in> set ss. \<forall> t' \<in> set ts. (size s' + size t' < size s + size t)"
              using size_simp1 tj_size by fastforce
            then have "\<forall> s' \<in> set ss. \<forall> t' \<in> set ts. (s' \<sqsupset> t' \<longrightarrow> s' \<cdot> \<delta> \<sqsupset> t' \<cdot> \<delta>)" using IH by auto
            then have "fst (lex_ext (\<lambda> s' t'. (s' \<sqsupset> t', s' = t')) n (map ?subst ss) (map ?subst ts))"
              using 2 lex_ext_fst_map by auto
            then show ?case using \<open>(s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> NS\<close> tj_subst by (auto simp: spo.simps)
          qed
        next
          case False
          then have "\<not> (s \<sqsupset> t)"
            using \<open>\<not> (\<exists>si\<in>set ss. si = t \<or> si \<sqsupset> t)\<close> by (auto simp: spo.simps)
          then show ?thesis using "1.prems" by auto
        qed
      qed
    qed
  qed
qed

text \<open>If S is well-founded, so is the SPO.\<close>

context
  assumes "SN S"
begin

lemma SPO_var_NF: "\<not> Var x \<sqsupset> u"
  by (simp add: spo.simps)

lemma SPO_SN_var: "SN_on SPO {Var x}"
  using SPO_var_NF
  by (metis CollectD case_prodD step_reflects_SN_on)

text \<open>set up a well-founded order for induction proof of SN SPO.\<close>

abbreviation SPO_SN
  where
    "SPO_SN \<equiv> SPO \<restriction> (SN_part SPO)"

lemma spo_SPO_SN:
  assumes "SN_on SPO {s}" "SN_on SPO {t}" "s \<sqsupset> t"
  shows "(s, t) \<in> SPO_SN"
  using assms
  by (simp add: SN_on_SN_part_conv mem_restrictI)

(* The restriction of a relation to its accessible/terminating part must be well-founded!
   But I don't know how to prove it... *)
lemma SN_SN_part:
  fixes R :: "'a rel"
  shows "SN (R \<restriction> (SN_part R))"
    by (metis SN_def SN_on_SN_part_conv SN_on_all_reducts_SN_on_conv SN_on_restrict empty_subsetI insert_subsetI mem_restrictD(1))

lemma SN_SPO_SN: "SN SPO_SN"
  using SN_SN_part .

abbreviation spo_lex_SN
  where
    "spo_lex_SN ss ts \<equiv> fst (lex_ext (order_pair_eq (\<lambda> s t. (s, t) \<in> SPO_SN)) n ss ts)"

lemma spo_lex_SN_if:
  assumes  "SN_on SPO (set ts)"  "SN_on SPO (set us)"
    "fst (lex_ext (order_pair_eq (\<lambda> s' t'. spo s' t')) n ts us)"
  shows "spo_lex_SN ts us"
proof -
  have "\<forall> t \<in> set ts . \<forall> u \<in> set us. (t \<sqsupset> u \<longrightarrow> (t, u) \<in> SPO_SN)"
    using spo_SPO_SN assms by (simp add: SN_on_SN_part_conv subset_iff)
  thus "fst (lex_ext (order_pair_eq (\<lambda> s t. (s, t) \<in> SPO_SN)) n ts us)"
    using assms lex_ext_incr by fast
qed

abbreviation SPO_LEX_SN
  where
    "SPO_LEX_SN \<equiv> { (ss, ts) . spo_lex_SN ss ts }"

lemma SN_SPO_LEX_SN: "SN SPO_LEX_SN"
  apply (rule lex_ext_SN_2)
    unfolding order_pair_eq_def apply simp
    using SN_SPO_SN apply simp
    done

abbreviation REFL where "REFL \<equiv> {(x,y). x = y}" 

text \<open>measure for the main lemma\<close>
definition BUCHHOLZ
  where
    "BUCHHOLZ \<equiv> lex_two S NS (lex_two SPO_LEX_SN REFL supt)"

lemma SN_BUCHHOLZ: "SN BUCHHOLZ"
  unfolding BUCHHOLZ_def
proof (rule lex_two)
  show "SN S" using \<open>SN S\<close> .
  show "NS O S \<subseteq> S" using compat_NS_S .
  show "SN (lex_two SPO_LEX_SN REFL {\<rhd>})"
  proof (rule lex_two)
    show "SN SPO_LEX_SN" using SN_SPO_LEX_SN .
    show "SN {\<rhd>}" using SN_supt .
    show "REFL O SPO_LEX_SN \<subseteq> SPO_LEX_SN" by blast
  qed
qed

abbreviation Buchholz_gg (infix "\<ggreater>" 50)
  where "x \<ggreater> y \<equiv> ((x, y) \<in> BUCHHOLZ)"

text \<open>uncurried version of main lemma (@{thm SN_induct} requires uncurrying?) \<close>
abbreviation SPO_SN_Buchholz_statement
  where
   " SPO_SN_Buchholz_statement t_ts_u \<equiv>
      (case t_ts_u of (t, ts, u) \<Rightarrow> (\<exists> f. t = Fun f ts) \<longrightarrow> t \<sqsupset> u \<longrightarrow> SN_on SPO (set ts) \<longrightarrow> SN_on SPO {u})"

lemma  SPO_SN_Buchholz': " SPO_SN_Buchholz_statement t_ts_u"
proof -
  have H: "\<forall> a. (\<forall> b. a \<ggreater> b \<longrightarrow>  SPO_SN_Buchholz_statement b) \<longrightarrow>  SPO_SN_Buchholz_statement a"
    apply simp
  proof (intro allI impI)
    fix t ts u
    assume IH: "\<forall> t' ts' u'. (t, ts, u) \<ggreater> (t', ts', u') \<longrightarrow>
          (\<exists>f. t' = Fun f ts') \<longrightarrow>
          t' \<sqsupset> u' \<longrightarrow>
          SN_on SPO (set ts') \<longrightarrow> SN_on SPO {u'}"
    assume "\<exists>f. t = Fun f ts"
    then obtain f where "t = Fun f ts" by blast
    note [simp] = this
    assume "t \<sqsupset> u"
    assume "SN_on SPO (set ts)"
    have "spo1a t u \<or> spo1b t u \<or> spo2a t u \<or> spo2b t u" using \<open>t \<sqsupset> u\<close> spo_iff by blast
    then show "SN_on SPO {u}"
    proof (elim disjE, goal_cases)
      case 1
      then obtain ti where "ti \<in> set ts" "ti = u"
        unfolding spo1a_def by force
      then show ?case using \<open>SN_on SPO (set ts)\<close> by fast
    next
      case 2
      then obtain ti where "ti \<in> set ts" "ti \<sqsupset> u"
        unfolding spo1b_def by force
      then have "SN_on SPO {ti}" using \<open>SN_on SPO (set ts)\<close> by fast
      then show ?case using \<open>ti \<sqsupset> u\<close> by (simp add: step_preserves_SN_on)
    next
      case 3
      then obtain g us where
        "u = Fun g us" "\<forall> uj \<in> set us. t \<sqsupset> uj" "(t, u) \<in> S"
        using spo2a_def by force
      note [simp] = \<open>u = Fun g us\<close>
      note [simp] = BUCHHOLZ_def
      have "\<forall> uj \<in> set us. SN_on SPO {uj}"
      proof (intro ballI)
        fix uj
        assume "uj \<in> set us"
        note [simp] = this
        then have "t \<sqsupset> uj" using \<open>\<forall> uj \<in> set us. t \<sqsupset> uj\<close> by blast
        moreover
        have "u \<rhd> uj" by simp
        then have "(t, ts, u) \<ggreater> (t, ts, uj)"
          by (simp add: refl_NS_point)
        ultimately show "SN_on SPO {uj}"
          using IH \<open>SN_on SPO (set ts)\<close> \<open>t = Fun f ts\<close> by blast
      qed
      then have "SN_on SPO (set us)" by fast
      show ?case
      proof (subst SN_on_all_reducts_SN_on_conv, intro allI impI)
        fix v
        assume "(u, v) \<in> SPO"
        then have "u \<sqsupset> v" by auto
        moreover
        have "(t, ts, u) \<ggreater> (u, us, v)" using \<open>(t, u) \<in> S\<close> by auto
        ultimately show "SN_on SPO {v}" using IH \<open>SN_on SPO (set us)\<close> by auto
      qed
    next
      case 4
      then obtain g us where
        *: "u = Fun g us" "\<forall> uj \<in> set us. t \<sqsupset> uj" "(t, u) \<in> NS"
        "fst (lex_ext (\<lambda> s' t'. (spo s' t', s' = t')) n ts us)"
        using spo2b_def by force
      note [simp] = \<open>u = Fun g us\<close>
      note [simp] = \<open>fst (lex_ext (\<lambda> s' t'. (spo s' t', s' = t')) n ts us)\<close>
      note [simp] = BUCHHOLZ_def
      have "\<forall> uj \<in> set us. SN_on SPO {uj}"
      proof (intro ballI)
        fix uj
        assume "uj \<in> set us"
        note [simp] = this
        then have "t \<sqsupset> uj" using \<open>\<forall> uj \<in> set us. t \<sqsupset> uj\<close> by blast
        moreover
        have "u \<rhd> uj" by simp
        then have "(t, ts, u) \<ggreater> (t, ts, uj)"
          by (simp add: refl_NS_point)
        ultimately show "SN_on SPO {uj}"
          using IH \<open>SN_on SPO (set ts)\<close> \<open>t = Fun f ts\<close> by blast
      qed
      then have "SN_on SPO (set us)" by fast
      then show ?case
      proof (subst SN_on_all_reducts_SN_on_conv, intro allI impI)
        fix v
        assume "(u, v) \<in> SPO"
        then have "u \<sqsupset> v" by auto
        moreover
        have "spo_lex_SN ts us"
          using spo_lex_SN_if * \<open>SN_on SPO (set us)\<close>  \<open>SN_on SPO (set ts)\<close>
          unfolding order_pair_eq_def by blast
        then have "(ts, us) \<in> SPO_LEX_SN" by simp
        then have "(t, ts, u) \<ggreater> (u, us, v)"
          using \<open>(t, u) \<in> NS\<close> by simp
        ultimately show "SN_on SPO {v}" using IH \<open>SN_on SPO (set us)\<close> by auto
      qed
    qed
  qed
  show ?thesis
    apply (rule SN_induct[OF SN_BUCHHOLZ])
    using H by blast
qed

text \<open>main lemma for SN SPO\<close>
lemma SPO_SN_Buchholz:
  assumes "t = Fun f ts" "t \<sqsupset> u" "SN_on SPO (set ts)"
  shows "SN_on SPO {u}"
proof -
  have "\<exists> f. t = Fun f ts"
    apply (rule exI[of _ f])
    using assms by blast
  have "SPO_SN_Buchholz_statement (t, ts, u)" using SPO_SN_Buchholz'
    by fast
  then have "(\<exists> f. t = Fun f ts) \<longrightarrow> t \<sqsupset> u \<longrightarrow> SN_on SPO (set ts) \<longrightarrow> SN_on SPO {u}" by simp
  thus ?thesis
    using \<open>\<exists> f. t = Fun f ts\<close> assms by blast
qed

lemma SPO_SN': "SN_on SPO {t}"
proof (induct t)
  case Var
  then show ?case using SPO_SN_var by auto
next
  case (Fun f ts)
  then have SN_args: "SN_on SPO (set ts)" by fast
  show "SN_on SPO {Fun f ts}"
  proof (subst SN_on_all_reducts_SN_on_conv, intro allI impI)
    fix u
    assume "(Fun f ts, u) \<in> SPO"
    then have "Fun f ts \<sqsupset> u" by auto
    thus "SN_on SPO {u}" using SPO_SN_Buchholz SN_args by auto
  qed
qed

lemma SPO_SN: "SN SPO"
  apply (rule SN_I)
  apply (rule SPO_SN')
  done

end

end

text \<open>H: a harmonious rewrite preorder\<close>
locale mspo = spo +
  fixes H :: "('a, 'b) term rel" (* the same type as S and NS *)
begin

definition mspo
  where
    "mspo s t \<longleftrightarrow> (((s, t) \<in> H) \<and> spo s t)"

abbreviation mspo_s (infix "\<succ>" 50) where "s \<succ> t \<equiv> mspo s t"

abbreviation "MSPO \<equiv> {(s,t). s \<succ> t}"

end

lemma mspo_on_subterms:
  assumes "mspo.mspo n S NS H s t" and
    "\<forall> u \<unlhd> s. \<forall> v \<unlhd> t. (u, v) \<in> S \<longrightarrow> (u, v) \<in> S'" and
    "\<forall> u \<unlhd> s. \<forall> v \<unlhd> t. (u, v) \<in> NS \<longrightarrow> (u, v) \<in> NS'" and
    "(s,t) \<in> H \<longrightarrow> (s, t) \<in> H'"
  shows "mspo.mspo n S' NS' H' s t"
proof -
  from assms spo_on_subterms mspo.mspo_def
  have "spo.spo n S' NS' s t" by blast
  with assms mspo.mspo_def show ?thesis by metis
qed

locale mspo_with_basic_assms = spo_with_basic_assms + mspo +
  assumes refl_H: "refl H"
    and trans_H: "trans H"
    and subst_H: "(s,t) \<in> H \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> H"
    and mono_H: "(s, t) \<in> H \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> H"
    and harmony_H_NS: "(s, t) \<in> H \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS" 
begin

lemma mspo_irrefl: "\<not> (s \<succ> s)"
  using spo_irrefl unfolding mspo_def by auto

lemma mspo_trans:
  "s \<succ> t \<longrightarrow> t \<succ> u \<longrightarrow> s \<succ> u"
  using spo_trans trans_H unfolding mspo_def
  by (meson transE)

lemma mspo_stable:
   "s \<succ> t \<longrightarrow> s \<cdot> \<delta> \<succ> t \<cdot> \<delta>"
  using spo_stable subst_H unfolding mspo_def by auto

lemma mspo_mono:
  assumes "s \<succ> t"
  shows "Fun f (bef @ s # aft) \<succ> Fun f (bef @ t # aft)"
  unfolding mspo_def
proof (intro conjI, goal_cases)
  case 1
  show ?case using assms mono_H mspo_def by auto
next
  case 2
  let ?ss = "bef @ s # aft"
  let ?ts = "bef @ t # aft"
  have "Fun f ?ss \<sqsupset> t"
    using spo_trans[of "Fun f ?ss" s t] subterm_spo_arg assms mspo_def by force
  have "\<forall> tj \<in> set (bef @ aft). Fun f ?ss \<sqsupset> tj"
    using subterm_spo_arg by auto
  then have "\<forall> tj \<in> set ?ts. Fun f ?ss \<sqsupset> tj" using \<open>Fun f ?ss \<sqsupset> t\<close> by auto
  moreover
  have "fst (lex_ext (\<lambda> s' t'. (s' \<sqsupset> t', s' = t')) n ?ss ?ts)"
    using assms exI[of _ "length bef"] unfolding lex_ext_iff
    by (auto simp: append_Cons_nth_not_middle mspo_def) 
  moreover
  have "(Fun f ?ss, Fun f ?ts) \<in> NS"
    using assms mspo_def harmony_H_NS by auto
  ultimately show ?case by (auto simp: spo.simps)
qed

lemma MSPO_SN: "SN S \<Longrightarrow> SN MSPO"
  using SPO_SN mspo_def by fastforce

end

end