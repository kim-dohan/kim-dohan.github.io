(*
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Reflection of confluence by currying\<close>

theory LS_Currying2
  imports 
    LS_Currying
begin

context pp_cr
begin

lemma missing_persists_Cu [simp]:
  assumes "is_Fun l"
  shows "missing_args (mctxt_of_term ((Cu l) \<cdot> \<sigma>)) n = missing_args (mctxt_of_term (l \<cdot> \<sigma>)) n"
using assms
proof (induction l arbitrary: n)
  case (Fun f ts)
  { fix x
    assume asm: "x \<in> set ts"
    have "missing_args (mctxt_of_term (x \<cdot> \<sigma>)) n' =
          missing_args (mctxt_of_term ((Cu x) \<cdot> \<sigma>)) n'" for n'
      using Fun(1)[OF asm, of n'] by (cases x) simp+
  } note inner = this
  then show ?case
  proof (cases "f = Ap")
    case isAp: True
    then show ?thesis using inner isAp by simp
  next
    case notAp: False
    then have "Suc (arity f) - length (map mctxt_of_term ts) - n =
           missing_args (mctxt_of_term (Cu (Fun f ts) \<cdot> \<sigma>)) n"
      using inner
    proof (induction "length ts" arbitrary: n ts)
      case (Suc n')
      then obtain ts' a where ts_def: "ts = ts' @ [a]"
        by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI)
      have "Suc (arity f) - Suc (length (map mctxt_of_term ts')) - n =
             missing_args (mctxt_of_term (Cu (Fun f ts') \<cdot> \<sigma>)) (Suc n)"
        using Suc(1)[OF _ Suc(3), of ts' "Suc n"] Suc(2,4)
        unfolding ts_def by simp
      then show ?case using Suc(2-) unfolding ts_def by simp
    qed simp
    then show ?thesis using notAp by force
  qed
qed simp

lemma check_persists_Cu [simp]:
  assumes "is_Fun l"
  shows "check_first_non_Ap n ((Cu l) \<cdot> \<sigma>) = check_first_non_Ap n (l \<cdot> \<sigma>)"
using missing_args_unfold missing_persists_Cu[OF assms] by metis

lemma \<F>_in_\<LL>\<^sub>1:
  assumes "funas_term t \<subseteq> \<F>\<^sub>U - { (Ap, 2) }"
  shows "\<LL>\<^sub>1 (mctxt_of_term t)"
using assms
proof (induction t)
  case (Fun f ts)
  moreover have "x \<in> set ts \<longrightarrow> \<LL>\<^sub>1 (mctxt_of_term x)" for x using Fun by auto
  ultimately show ?case using Fun(2) \<LL>\<^sub>1.simps[of "MFun f (map mctxt_of_term ts)"] by simp
qed auto

lemma Cu_\<F>_\<LL>\<^sub>1:
  assumes "funas_term t \<subseteq> \<F>\<^sub>U - { (Ap, 2) }"
  shows "\<LL>\<^sub>1 (mctxt_of_term (Cu t))"
proof -
  have "\<LL>\<^sub>1 (mctxt_of_term t)" using \<F>_in_\<LL>\<^sub>1[OF assms] .
  then show ?thesis using assms
  proof (induction t)
    case (Fun f ts) then show ?case
    proof (induction "length ts" arbitrary: ts)
      case (Suc n)
      then obtain ts' a where ts_def: "ts = ts' @ [a]"
        by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI)
      have arity_f: "length ts \<le> arity f"
        using Suc(5) unfolding \<F>\<^sub>U_def arity_def by fastforce
      have "f \<noteq> Ap" using Suc(5) fresh unfolding \<F>\<^sub>U_def by fastforce
      have f_ts': "(f, length ts') \<in> \<F>\<^sub>U - {(Ap, 2)}"
        using \<F>\<^sub>U_def \<F>_def Suc(5) fresh unfolding ts_def by force
      have "x \<in> set ts \<longrightarrow> \<LL>\<^sub>1 (mctxt_of_term x)" for x
        using Suc(4) \<LL>_def in_set_idx sub_layers by fastforce
      then have "x \<in> set ts' \<longrightarrow> \<LL>\<^sub>1 (mctxt_of_term x)" for x unfolding ts_def by simp
      then have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mctxt_of_term (Fun f ts'))"
        using Suc(4) f_ts' unfolding ts_def mctxt_of_term.simps by fastforce
      have funas: "funas_term (Fun f ts') \<subseteq> \<F>\<^sub>U - {(Ap, 2)}"
        using Suc(5) \<open>f \<noteq> Ap\<close> unfolding ts_def \<F>\<^sub>U_def by auto
      have arg1: "\<LL>\<^sub>1 (mctxt_of_term (Cu (Fun f ts')))"
        using Suc(1)[OF _ _ in_\<LL>\<^sub>1 funas] Suc(2,3) unfolding ts_def by force
      have "check_first_non_Ap 1 (Fun f ts')"
        using arity_f \<open>f \<noteq> Ap\<close> unfolding ts_def by simp
      then have "check_first_non_Ap 1 (Cu (Fun f ts'))"
        using check_persists_Cu[of "Fun f ts'" 1 Var] by simp
      moreover have arg2: "\<LL>\<^sub>1 (mctxt_of_term (Cu a))"
        using Suc(3)[of a] Suc(5) \<F>_in_\<LL>\<^sub>1[of a] unfolding ts_def by auto
      ultimately show ?case using \<open>f \<noteq> Ap\<close> arg1
        unfolding ts_def missing_args_unfold[symmetric] by auto
    qed simp
  qed simp
qed

lemma Cu\<^sub>R_NF_\<U>_\<R>_step:
  assumes "(Cu s, Cu t) \<in> rstep (Cu\<^sub>R \<R>)" "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
  shows "(s, t) \<in> rstep \<R>"
proof -
  obtain C l r \<sigma> where s_def: "Cu s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t_def: "Cu t = C\<langle>r \<cdot> \<sigma>\<rangle>" and
                      in_Cu\<^sub>R: "(l, r) \<in> Cu\<^sub>R \<R>"
    using assms(1) by fast
  then obtain l' r' where l_def: "l = Cu l'" and r_def: "r = Cu r'" and in_\<R>: "(l', r') \<in> \<R>"
    using Cu\<^sub>R_def by auto
  obtain f ts' where l'_def: "l' = Fun f ts'" using in_\<R> wfR unfolding wf_trs_def
    by fastforce
  then have "f \<noteq> Ap" "arity f = length ts'" using in_\<R> sigR fresh
    unfolding arity_def funas_trs_def funas_rule_def by fastforce+
  moreover obtain ts where l\<sigma>_def: "l' \<cdot> \<sigma> = Fun f ts" "length ts = length ts'"
    using l'_def by auto
  ultimately have "\<not> check_first_non_Ap 1 (l' \<cdot> \<sigma>)" by auto
  then have check_l\<sigma>: "\<not> check_first_non_Ap 1 (l \<cdot> \<sigma>)"
    using check_persists_Cu[of l' 1 \<sigma>] unfolding l_def by fastforce
  have Cu_s_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mctxt_of_term (Cu s))"
    using Cu_\<F>_\<LL>\<^sub>1[of s] assms(2) fresh unfolding \<F>_def \<F>\<^sub>U_def by auto
  { fix C' f' ss2
    assume "C = C' \<circ>\<^sub>c More f' [] \<box> ss2"
    then have in_\<LL>\<^sub>1: "\<LL>\<^sub>1 (mctxt_of_term (Fun f' ([] @ l \<cdot> \<sigma> # ss2)))"
      using Cu_s_\<LL>\<^sub>1 subm_at_layers[of "mctxt_of_term (Cu s)" "hole_pos C'"] unfolding s_def \<LL>_def
      by simp (metis hole_pos_poss list.simps(9) mctxt_of_term.simps(2)
         subm_at.simps(1) subm_at_mctxt_of_term subt_at_hole_pos)
    have "f' \<noteq> Ap" using \<LL>\<^sub>1.cases[OF in_\<LL>\<^sub>1] check_l\<sigma> fresh
      unfolding missing_args_unfold[symmetric] \<F>\<^sub>U_def by simp ((cases "f' = Ap"), fastforce)
  }
  then have no_Ap_above: "\<forall>C' f ss2. C = C' \<circ>\<^sub>c More f [] \<box> ss2 \<longrightarrow> f \<noteq> Ap"
    by blast
  obtain D where "NF_\<U> (Cu s) = D\<langle>NF_\<U> (l \<cdot> \<sigma>)\<rangle> \<and> NF_\<U> (Cu t) = D\<langle>NF_\<U> (r \<cdot> \<sigma>)\<rangle>"
    using NF_\<U>_persists[OF no_Ap_above]
    unfolding s_def t_def by blast
  moreover have "funas_term l' \<subseteq> \<F>" "funas_term r' \<subseteq> \<F>" using in_\<R> sigR \<F>_def
    unfolding funas_trs_def funas_rule_def by fastforce+
  ultimately have s_def: "s = D\<langle>l' \<cdot> (NF_\<U> \<circ> \<sigma>)\<rangle>" and NF_\<U>_t_def: "t = D\<langle>r' \<cdot> (NF_\<U> \<circ> \<sigma>)\<rangle>"
    using NF_\<U>_Cu_subst[of _ \<sigma>] NF_\<U>_Cu assms(2,3) unfolding l_def r_def by auto
  moreover have "(s, t) \<in> rstep \<R>" unfolding s_def NF_\<U>_t_def using in_\<R> by blast
  ultimately show ?thesis by blast
qed

inductive is_Cu' :: "('f, 'v) term \<Rightarrow> nat \<Rightarrow> bool" where
  var  [intro]: "is_Cu' (Var x) 0"
| funs [intro]: "sigF f = Some n \<Longrightarrow> is_Cu' (Fun f []) n"
| ap   [intro]: "is_Cu' t\<^sub>1 (Suc n) \<Longrightarrow> is_Cu' t\<^sub>2 0 \<Longrightarrow> is_Cu' (Fun Ap [t\<^sub>1, t\<^sub>2]) n"

abbreviation is_Cu where "is_Cu t \<equiv> is_Cu' t 0"

lemma is_Cu_intro:
  assumes "funas_term t \<subseteq> \<F>"
  shows "is_Cu (Cu t)"
using assms
proof (induction t)
  case (Fun f ts)
  then have props: "Some (length ts) = sigF f" "\<forall>t'\<in>set ts. funas_term t' \<subseteq> \<F>"
    using \<F>_def by auto
  then have "f \<noteq> Ap" using fresh by force
  { fix m
    assume "Some (length ts + m) = sigF f"
    moreover have "t' \<in> set ts \<longrightarrow> is_Cu (Cu t')" for t' using Fun by auto
    ultimately have "is_Cu' (Cu (Fun f ts)) m" using props(2)
    proof (induction "length ts" arbitrary: ts m)
      case (Suc n)
      then obtain ts' a where ts_def: "ts = ts' @ [a]"
        by (metis append_Nil2 append_eq_conv_conj id_take_nth_drop lessI)
      have "Cu (Fun f ts) = Fun Ap [Cu (Fun f ts'), Cu a]"
        using \<open>f \<noteq> Ap\<close> unfolding ts_def by simp
      have "is_Cu (Cu a)" using Suc(4) unfolding ts_def by auto
      moreover have "is_Cu' (Cu (Fun f ts')) (Suc m)"
        using Suc(1)[of ts' "Suc m"] Suc(2-) unfolding ts_def by auto
      ultimately show ?case using \<open>f \<noteq> Ap\<close> unfolding ts_def by auto
    qed auto
  }
  then show ?case using props(1) by fastforce
qed auto

lemma is_Cu_elim':
  assumes "is_Cu' t n"
  shows "(\<exists>f ts. Some (length ts + n) = sigF f \<and>
         (\<forall>t' \<in> set ts. funas_term t' \<subseteq> \<F>) \<and> t = Cu (Fun f ts))
          \<or> n = 0 \<and> (\<exists>x. t = Var x)"
using assms
proof (induction t n rule: is_Cu'.induct)
  case (funs f m)
  then have "Some (length [] + m) = sigF f \<and> (\<forall>t'\<in>set []. funas_term t' \<subseteq> \<F>) \<and>
         Fun f [] = Cu (Fun f [])" using arity_def by simp
  then show ?case by blast
next
  case (ap t\<^sub>1 n t\<^sub>2)
  then obtain f ts' where inner: "Some (length ts' + Suc n) = sigF f \<and>
       (\<forall>t' \<in> set ts'. funas_term t' \<subseteq> \<F>) \<and> t\<^sub>1 = Cu (Fun f ts')" by blast
  then have "f \<noteq> Ap" using fresh by force
  obtain g ss where t\<^sub>2'_props: "Some (length ss) = sigF g \<and>
       (\<forall>t'\<in>set ss. funas_term t' \<subseteq> \<F>) \<and> t\<^sub>2 = Cu (Fun g ss) \<or> (\<exists>x. t\<^sub>2 = Var x)"
    using ap(4) by auto
  then show ?case
  proof (elim disjE)
    assume t\<^sub>2_props: "Some (length ss) = sigF g \<and>
                     (\<forall>t'\<in>set ss. funas_term t' \<subseteq> \<F>) \<and> t\<^sub>2 = Cu (Fun g ss)"
    let ?ts = "ts' @ [Fun g ss]"
    have "Some (length ?ts + n) = sigF f \<and>
         (\<forall>t' \<in> set ?ts. funas_term t' \<subseteq> \<F>) \<and> Fun Ap [t\<^sub>1, t\<^sub>2] = Cu (Fun f ?ts)"
      using inner t\<^sub>2_props \<open>f \<noteq> Ap\<close> \<F>_def by auto
    then show ?thesis by blast
  next
    assume "\<exists>x. t\<^sub>2 = Var x"
    then obtain x where t\<^sub>2_def: "t\<^sub>2 = Var x" by blast
    let ?ts = "ts' @ [Var x]"
    have "Some (length ?ts + n) = sigF f \<and>
         (\<forall>t' \<in> set ?ts. funas_term t' \<subseteq> \<F>) \<and> Fun Ap [t\<^sub>1, t\<^sub>2] = Cu (Fun f ?ts)"
      using inner t\<^sub>2_def \<open>f \<noteq> Ap\<close> by auto
    then show ?thesis by blast
  qed
qed blast

lemma is_Cu_elim:
  assumes "is_Cu' t 0"
  shows "\<exists>t'. funas_term t' \<subseteq> \<F> \<and> t = Cu t'"
proof (cases t)
  case (Var x)
  then show ?thesis by (auto intro: exI[of _ "Var x"])
next
  case (Fun f ts)
  then obtain f' ts' where props: "Some (length ts' + 0) = sigF f' \<and>
        (\<forall>t'\<in>set ts'. funas_term t' \<subseteq> \<F>) \<and> t = Cu (Fun f' ts')"
    using is_Cu_elim'[OF assms] by blast
  then have "funas_term (Fun f' ts') \<subseteq> \<F> \<and> t = Cu (Fun f' ts')" unfolding \<F>_def by auto
  then show ?thesis by blast
qed

lemma Cu'_subst_Cu':
  assumes "is_Cu' t n" "\<forall>x. x \<in> vars_term t \<longrightarrow> is_Cu (Var x \<cdot> \<sigma>)"
  shows "is_Cu' (t \<cdot> \<sigma>) n"
using assms by (induction rule: is_Cu'.induct) auto

lemma Cu_subst_Cu:
  assumes "is_Cu t" "\<forall>x. x \<in> vars_term t \<longrightarrow> is_Cu (Var x \<cdot> \<sigma>)"
  shows "is_Cu (t \<cdot> \<sigma>)"
using assms Cu'_subst_Cu' by blast

lemma is_Cu'_unique:
  assumes "is_Cu' t n" "is_Cu' t m"
  shows "n = m"
using assms
by (induction t n arbitrary: m rule: is_Cu'.induct) (force elim: is_Cu'.cases)+

lemma replace_in_Cu:
  assumes "is_Cu' C\<langle>s'\<rangle> n" "is_Cu s'" "is_Cu t'"
  shows "is_Cu' C\<langle>t'\<rangle> n"
using assms
proof (induction C arbitrary: n)
  case Hole
  then have "n = 0" using is_Cu'_unique by force
  then show ?case using Hole by simp
next
  case (More f ss1 C' ss2)
  then have "f = Ap" by (auto elim: is_Cu'.cases)
  consider "\<exists>a. ss1 = [] \<and> ss2 = [a]" | "\<exists>a. ss2 = [] \<and> ss1 = [a]"
    using More(2) by (cases ss1; cases ss2) (auto elim: is_Cu'.cases)
  then show ?case
  proof cases
    case 1
    then show ?thesis using More by (auto elim: is_Cu'.cases)
  next
    case 2
    then obtain a where lists: "ss2 = [] \<and> ss1 = [a]" by blast
    then have "is_Cu' a (Suc n)" "is_Cu C'\<langle>t'\<rangle>" using More by (auto elim: is_Cu'.cases)
    then show ?thesis using lists \<open>f = Ap\<close> by auto
  qed
qed

(*suggested by Aart*)
lemma vars_term_subst_Cu:
  assumes "is_Cu' t n" "is_Cu' (t \<cdot> \<sigma>) n"
  shows "\<forall>x \<in> vars_term t. is_Cu (Var x \<cdot> \<sigma>)"
using assms by (induction rule: is_Cu'.induct) (auto elim: is_Cu'.cases)

lemma nothing_missing_lhs_Cu\<^sub>R:
  assumes "r \<in> Cu\<^sub>R \<R>"
  shows "missing_args (mctxt_of_term (fst r \<cdot> \<sigma>)) 0 = 1"
proof -
  obtain l' r' where lhs_rhs_def: "fst r = Cu l'" "snd r = Cu r'" "(l', r') \<in> \<R>"
    using assms(1) Cu\<^sub>R_def by auto
  moreover have "is_Fun l'"
    using \<open>(l', r') \<in> \<R>\<close> wfR unfolding wf_trs_def by blast
  ultimately have "missing_args (mctxt_of_term (l' \<cdot> \<sigma>)) 0 = 1"
    using nothing_missing_lhs_\<R> by force
  then have "missing_args (mctxt_of_term ((Cu l') \<cdot> \<sigma>)) 0 = 1"
    using missing_persists_Cu[of l' \<sigma>] unfolding missing_args_unfold[symmetric]
    by (cases "is_Fun l'") auto
  then show ?thesis using lhs_rhs_def by argo
qed

lemma is_Cu_Cu\<^sub>R:
  assumes "(l, r) \<in> Cu\<^sub>R \<R>"
  shows "is_Cu l" "is_Cu r"
proof -
  obtain l' r' where lr_def: "l = Cu l'" "r = Cu r'" "(l', r') \<in> \<R>"
    using assms unfolding Cu\<^sub>R_def by blast
  moreover have "funas_term l' \<subseteq> \<F>" "funas_term r' \<subseteq> \<F>"
    using lr_def(3) sigR \<F>_def 
    unfolding funas_trs_def funas_rule_def by force+
  ultimately show "is_Cu l" "is_Cu r" using is_Cu_intro by simp+
qed

lemma is_Cu'_n0:
  assumes "missing_args (mctxt_of_term t) n = 1"
  shows "is_Cu' t m \<longrightarrow> m = n"
using assms
proof (induction "mctxt_of_term t" n arbitrary: t m rule: missing_args.induct)
  case (2 x n)
  then show ?case by (cases t) auto
next
  case (3 f Cs n)
  then obtain ts where t_def: "t = Fun f ts" "Cs = map mctxt_of_term ts" by (cases t) simp+
  then show ?case
  proof (cases "f = Ap \<and> length Cs = 2")
    case True
    then obtain "is_Cu' (ts ! 0) (Suc m) \<longrightarrow> Suc m = Suc n"
      using 3(1)[OF True, of "ts ! 0" "Suc m"] 3(3) unfolding t_def by auto
    then show ?thesis using True unfolding t_def by (auto elim: is_Cu'.cases)
  next
    case False
    then show ?thesis using 3(2-) unfolding t_def by (auto elim: is_Cu'.cases simp: arity_def)
  qed
qed simp

lemma Cu_subst_in_ctxt:
  assumes "is_Cu' C\<langle>l \<cdot> \<sigma>\<rangle> n" "is_Cu l" "is_Fun l" "missing_args (mctxt_of_term (l \<cdot> \<sigma>)) 0 = 1"
  shows "C \<noteq> \<box> \<longrightarrow> is_Cu (l \<cdot> \<sigma>)"
using assms(1,4)
proof (induction C arbitrary: n)
  case (More f ss1 C' ss2)
  consider "\<exists>a. ss1 = [] \<and> ss2 = [a]" | "\<exists>a. ss2 = [] \<and> ss1 = [a]"
    using More(2) by (cases ss1; cases ss2) (auto elim: is_Cu'.cases)
  then show ?case
  proof cases
    case 1
    then show ?thesis using More is_Cu'_n0[OF More(3)] by (cases C') (auto elim: is_Cu'.cases)
  next
    case 2
    then obtain a where lists: "ss2 = [] \<and> ss1 = [a]" by blast
    then have "is_Cu' a (Suc n)" "is_Cu C'\<langle>l \<cdot> \<sigma>\<rangle>" using More by (auto elim: is_Cu'.cases)
    then show ?thesis using lists More by (cases C') auto
  qed
qed blast

lemma Cu_step_persists:
  assumes "(s, t) \<in> rstep (Cu\<^sub>R \<R>)" "is_Cu s"
  shows "is_Cu t"
proof -
  obtain l r p \<sigma> where step: "(s, t) \<in> rstep_r_p_s (Cu\<^sub>R \<R>) (l, r) p \<sigma>"
    using rstep_iff_rstep_r_p_s[of _ _ "Cu\<^sub>R \<R>"] assms(1) by blast
  obtain C where props: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "p = hole_pos C" "(l, r) \<in> Cu\<^sub>R \<R>"
    using hole_pos_ctxt_of_pos_term[of p s]
      Product_Type.Collect_case_prodD[OF step[unfolded rstep_r_p_s_def]]
    unfolding fst_conv snd_conv by metis
  then have nothing_missing: "missing_args (mctxt_of_term (l \<cdot> \<sigma>)) 0 = 1"
    using nothing_missing_lhs_Cu\<^sub>R by force
  have "is_Cu l" "is_Cu r" using is_Cu_Cu\<^sub>R[OF props(4)] by simp+
  then have "is_Cu (l \<cdot> \<sigma>)"
    using Cu_subst_in_ctxt[OF _ _ _ nothing_missing] assms(2) wf_Cu props(4)
    unfolding props(1) wf_trs_def by (cases C) (simp, blast)
  then have is_Cu_\<sigma>l: "\<forall>x. x \<in> vars_term l \<longrightarrow> is_Cu (Var x \<cdot> \<sigma>)"
    using vars_term_subst_Cu \<open>is_Cu l\<close> by blast
  then have is_Cu_\<sigma>r: "\<forall>x. x \<in> vars_term r \<longrightarrow> is_Cu (Var x \<cdot> \<sigma>)"
    using wf_Cu props(4) unfolding wf_trs_def by blast
  have "is_Cu (r \<cdot> \<sigma>)"
    using Cu_subst_Cu[OF \<open>is_Cu r\<close> is_Cu_\<sigma>r] .
  then show ?thesis using replace_in_Cu[OF _ \<open>is_Cu (l \<cdot> \<sigma>)\<close> \<open>is_Cu (r \<cdot> \<sigma>)\<close>, of C]
    props(1,2) assms(2) by blast
qed

lemma Cu_eq_NF_\<U>_eq':
  assumes "Cu s = Cu t" "funas_term s \<subseteq> \<F>"
  shows "NF_\<U> (Cu t) = s"
using assms(1) NF_\<U>_Cu[OF assms(2)] by simp

lemma Cu\<^sub>R_NF_\<U>_\<R>_steps:
  assumes "(Cu s, Cu t) \<in> (rstep (Cu\<^sub>R \<R>))\<^sup>*" "funas_term s \<subseteq> \<F>"
  shows "(s, NF_\<U> (Cu t)) \<in> (rstep \<R>)\<^sup>*"
proof -
  show ?thesis using assms
  proof (induction "Cu s" arbitrary: s rule: converse_rtrancl_induct)
    case base
    then show ?case using Cu_eq_NF_\<U>_eq'[of s t] by simp
  next
    case (step z)
    have "is_Cu (Cu s)" using is_Cu_intro[OF step(4)] .
    then obtain z' where is_Cu_z: "funas_term z' \<subseteq> \<F> \<and> z = Cu z'"
        using is_Cu_elim[OF Cu_step_persists[OF step(1)]] by blast
    then have "(s, z') \<in> (rstep \<R>)\<^sup>*"
      using Cu\<^sub>R_NF_\<U>_\<R>_step[of s z'] step(1,4) by fastforce
    then show ?case using step(3)[of z'] is_Cu_z by fastforce
  qed
qed

theorem main_result_sound:
  assumes "CR (rstep (Cu\<^sub>R \<R>))"
  shows "CR (rstep \<R>)"
proof -
  { fix a :: "('f, 'v) term"
    assume funas_a: "funas_term a \<subseteq> \<F>"
    { fix b c
      assume peak: "(a, b) \<in> (rstep \<R>)\<^sup>*" "(a, c) \<in> (rstep \<R>)\<^sup>*"
      then have funas: "funas_term b \<subseteq> \<F>" "funas_term c \<subseteq> \<F>"
        using rsteps_preserve_funas_terms[OF sigR funas_a[unfolded \<F>_def] _ wfR]
        unfolding \<F>_def by blast+
      then have NF_\<U>_Cu_bc: "NF_\<U> (Cu b) = b" "NF_\<U> (Cu c) = c" using NF_\<U>_Cu by auto
      have "(Cu a, Cu b) \<in> (rstep (Cu\<^sub>R \<R>))\<^sup>*" "(Cu a, Cu c) \<in> (rstep (Cu\<^sub>R \<R>))\<^sup>*"
        using peak rtrancl_map[OF g_prop1, of "rstep \<R>" id a] unfolding rtrancl_idemp by auto
      then obtain d' where join: "(Cu b, d') \<in> (rstep (Cu\<^sub>R \<R>))\<^sup>* \<and> (Cu c, d') \<in> (rstep (Cu\<^sub>R \<R>))\<^sup>*"
        using assms unfolding CR_defs by blast
      then have "d' \<in> \<T>\<^sub>C\<^sub>u" using funas_Cu[OF funas(1)]
        by simp (meson funas_Cu\<^sub>R rsteps_preserve_funas_terms wf_Cu)
      then have "Cu d' = d'" using \<T>\<^sub>C\<^sub>u_Cu_eq by blast
      have "(b, NF_\<U> d') \<in> (rstep \<R>)\<^sup>* \<and> (c, NF_\<U> d') \<in> (rstep \<R>)\<^sup>*"
        using Cu\<^sub>R_NF_\<U>_\<R>_steps[OF _ funas(1), of d'] Cu\<^sub>R_NF_\<U>_\<R>_steps[OF _ funas(2), of d'] join 
        unfolding \<open>Cu d' = d'\<close> by blast
      then have "(b, c) \<in> (rstep \<R>)\<^sup>\<down>" by blast
    }
    then have "CR_on (rstep \<R>) {a}" unfolding CR_defs by simp
  }
  then have "CR_on (rstep \<R>) { t. funas_term t \<subseteq> \<F> }" unfolding CR_on_def by auto
  then show ?thesis using CR_on_imp_CR[OF wfR sigR] unfolding \<F>_def by blast
qed

end

end
