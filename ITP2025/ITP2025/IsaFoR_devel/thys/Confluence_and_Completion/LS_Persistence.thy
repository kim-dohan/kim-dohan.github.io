(*
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Persistence of confluence\<close>

theory LS_Persistence
  imports LS_General
begin

text \<open>Here we instantiate the layer framework for persistence of confluence. 
      See {cite \<open>Section 5.5\<close> FMZvO15}.\<close>

locale many_sorted_terms =
  fixes sigF :: "('f \<times> nat) \<Rightarrow> ('t list \<times> 't) option" and sigV :: "'v \<Rightarrow> 't option"
  assumes arity: "sigF (f, n) = Some (tys, tr) \<Longrightarrow> length tys = n"
begin

definition \<F> where "\<F> = { fn . sigF fn \<noteq> None }"
definition \<V> where "\<V> = { v . sigV v \<noteq> None }"

inductive \<T>\<^sub>\<alpha> :: "'t \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  var  [intro]: "sigV x = Some \<alpha> \<Longrightarrow> \<T>\<^sub>\<alpha> \<alpha> (Var x)"
| funs [intro]: "sigF (f, length ts) = Some (tys, \<alpha>) \<Longrightarrow>
                 (\<forall> i < length ts. \<T>\<^sub>\<alpha> (tys ! i) (ts ! i)) \<Longrightarrow> \<T>\<^sub>\<alpha> \<alpha> (Fun f ts)"

lemma funas_\<T>\<^sub>\<alpha>:
  assumes "\<T>\<^sub>\<alpha> \<alpha> t" "fn \<in> funas_term t"
  shows "fn \<in> \<F>"
  using assms
proof (induction t)
  case (funs f ts tys \<alpha>)
  then have "fn \<in> {(f, length ts)} \<longrightarrow> fn \<in> \<F>" using \<F>_def by blast
  moreover have "fn \<in> \<Union>(set (map funas_term ts)) \<longrightarrow> fn \<in> \<F>"
    using funs(2) map_nth_eq_conv[OF length_map[of funas_term ts, symmetric]]
    by auto (metis in_set_idx)
  ultimately show ?thesis using funs(3) unfolding "funas_term.simps" by blast
qed auto

inductive needed_types :: "'t \<Rightarrow> 't \<Rightarrow> bool" where
  base_type [intro]: "needed_types \<alpha> \<alpha>"
| sub_types [intro]: "sigF (f, n) = Some (tys, \<alpha>) \<Longrightarrow>
                      ty \<in> set tys \<Longrightarrow> needed_types \<alpha> ty"
| trans     [intro]: "needed_types \<alpha> \<beta> \<Longrightarrow> needed_types \<beta> \<gamma> \<Longrightarrow> needed_types \<alpha> \<gamma>"

end

locale persistent_cr = many_sorted_terms sigF sigV for 
        sigF :: "('f \<times> nat) \<Rightarrow> ('t list \<times> 't) option" and
        sigV :: "'v :: infinite \<Rightarrow> 't option" +
  fixes \<R> :: "('f, 'v :: infinite) trs"
  assumes
    wf: "wf_trs \<R>" and
    R_def: "(l, r) \<in> \<R> \<Longrightarrow> \<exists>\<alpha> . \<T>\<^sub>\<alpha> \<alpha> l \<and> \<T>\<^sub>\<alpha> \<alpha> r"
begin

definition lhs_types :: "('f \<times> nat) \<Rightarrow> 't list" where
  "lhs_types \<equiv> \<lambda> fn. fst (the (sigF fn))"

fun rhs_type :: "('f, 'v) term \<Rightarrow> 't option" where
  "rhs_type (Var x) = sigV x"
| "rhs_type (Fun f ts) = (let fn = (f, length ts) in
    (if sigF fn = None then None else Some (snd (the (sigF fn)))))"

fun max_top_persistent :: "'t \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) mctxt" where
  "max_top_persistent \<alpha> (Var x) = MVar x"
| "max_top_persistent \<alpha> (Fun f ts) = (if (\<exists>tys. sigF (f, length ts) = Some (tys, \<alpha>))
        then MFun f (map (case_prod max_top_persistent) (zip (lhs_types (f, length ts)) ts))
        else MHole)"

(* The following definition is just an idea and not used yet. *)
inductive max_top_persistent' :: "'t \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> bool" where
  "max_top_persistent' \<alpha> (Var x) (MVar x)"
| "sigF (f, length ts) = Some (tys, \<alpha>) \<Longrightarrow> length ms = length ts \<Longrightarrow>
   i < length ts \<longrightarrow> max_top_persistent' (tys ! i) (ts ! i) (ms ! i) \<Longrightarrow> max_top_persistent' \<alpha> (Fun f ts) (MFun f ms)"
| "sigF (f, length ts) = None \<Longrightarrow> max_top_persistent' \<alpha> (Fun f ts) MHole"

inductive \<LL>\<^sub>\<alpha> :: "'t \<Rightarrow> ('f, 'v) mctxt \<Rightarrow> bool" where
  mhole [intro]: "\<LL>\<^sub>\<alpha> \<alpha> MHole"
| mvar  [intro]: "\<LL>\<^sub>\<alpha> \<alpha> (MVar x)"
| mfun  [intro]: "sigF (f, length Cs) = Some (tys, \<alpha>) \<Longrightarrow>
                  (\<forall> i < length Cs. \<LL>\<^sub>\<alpha> (tys ! i) (Cs ! i)) \<Longrightarrow> \<LL>\<^sub>\<alpha> \<alpha> (MFun f Cs)"

definition \<LL> :: "('f, 'v) mctxt set" where
  "\<LL> \<equiv> { C. \<exists>\<alpha>. \<LL>\<^sub>\<alpha> \<alpha> C }"

abbreviation \<R>\<^sub>\<alpha> where "\<R>\<^sub>\<alpha> \<alpha> \<equiv> { (l, r) \<in> \<R> . \<T>\<^sub>\<alpha> \<alpha> l \<and> \<T>\<^sub>\<alpha> \<alpha> r }"
abbreviation topsC_\<alpha> where "topsC_\<alpha> \<alpha> \<equiv> layer_system_sig.topsC { L . \<LL>\<^sub>\<alpha> \<alpha> L }"
abbreviation max_topC_\<alpha> where "max_topC_\<alpha> \<alpha> \<equiv> layer_system_sig.max_topC { L . \<LL>\<^sub>\<alpha> \<alpha> L }"

lemma \<R>\<^sub>\<alpha>_sub_\<R>: "\<R>\<^sub>\<alpha> \<alpha> \<subseteq> \<R>"
using R_def by blast

lemma \<R>\<^sub>\<alpha>_Union_\<R>: "(\<Union>\<alpha>. \<R>\<^sub>\<alpha> \<alpha>) \<subseteq> \<R>"
using R_def by blast

lemma \<T>\<^sub>\<alpha>_\<LL>\<^sub>\<alpha>:
  assumes "\<T>\<^sub>\<alpha> \<alpha> t"
  shows "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term t)"
using assms by (induction t) auto

lemma funas_\<LL>:
  assumes "L \<in> \<LL>"
  shows "funas_mctxt L \<subseteq> \<F>"
proof -
  obtain \<alpha> where "\<LL>\<^sub>\<alpha> \<alpha> L" using assms \<LL>_def by auto
  then show ?thesis using assms
  proof (induction rule: \<LL>\<^sub>\<alpha>.induct)
    case (mfun f Cs tys)
    {
      fix i
      assume "i < length Cs"
      then have "funas_mctxt (Cs ! i) \<subseteq> \<F>" using mfun \<LL>_def \<open>i < length Cs\<close> by blast
    } note funas_subts = this
    then have "(f, length Cs) \<in> \<F>" using mfun \<F>_def by simp
    then show ?case using funas_mctxt.simps(1) funas_subts in_set_conv_nth[of _ Cs] by fastforce
  qed auto
qed

lemma subm_at_sig:
  fixes L :: "('f, 'v) mctxt" and p :: pos and \<F> :: "('f \<times> nat) set"
  assumes "funas_mctxt L \<subseteq> \<F>" and "p \<in> all_poss_mctxt L"
  shows "funas_mctxt (subm_at L p) \<subseteq> \<F>"
using assms subt_at_imp_ctxt funas_term_ctxt_apply
  unfolding funas_term_mctxt_term_conv[symmetric] subm_at_subt_at_conv[OF assms(2)]
  mctxt_term_conv_inv poss_mctxt_term_conv[symmetric] by (metis le_sup_iff)

lemma fun_poss_subm_at:
  assumes "p \<in> fun_poss_mctxt C"
  shows "\<exists>f Cs. subm_at C p = MFun f Cs"
using assms by (induction C arbitrary: p) (auto simp: fun_poss_mctxt_def)

lemma fun_poss_all_poss_mctxt:
  assumes "p \<in> fun_poss_mctxt C"
  shows "p \<in> all_poss_mctxt C"
using assms by (induction C arbitrary: p) (auto simp: fun_poss_mctxt_def)

lemma subm_at_fun:
  assumes "i < length Cs"
  shows "subm_at (MFun f Cs) [i] = Cs ! i" and "[i] \<in> all_poss_mctxt (MFun f Cs)"
using assms by auto

lemma funas_sub_mctxt:
  fixes f :: 'f and Cs :: "('f, 'v) mctxt list"
  assumes "funas_mctxt (MFun f Cs) \<subseteq> \<F>"
          "i < length Cs"
  shows "funas_mctxt (Cs ! i) \<subseteq> \<F>"
using assms subm_at_fun[of i Cs f] subm_at_sig[of "MFun f Cs" \<F> "[i]"] by simp

lemma funas_sup_mctxt:
  fixes L N :: "('f, 'v) mctxt"
  assumes cmp: "(L, N) \<in> comp_mctxt" and
      funas_L: "funas_mctxt L \<subseteq> \<F>" and
      funas_N: "funas_mctxt N \<subseteq> \<F>"
  shows "funas_mctxt (L \<squnion> N) \<subseteq> \<F>"
proof -
  have "comp_mctxtp L N" using cmp by (auto simp: comp_mctxt_def)
  then show ?thesis using funas_L funas_N
  by (induction L N rule: comp_mctxtp.induct)
     (auto simp: funas_sub_mctxt set_zip, blast)
qed

lemma consistent_\<LL>\<^sub>\<alpha>:
  assumes "\<LL>\<^sub>\<alpha> \<alpha> (MFun f Cs)"
  shows "\<exists>tys. sigF (f, length Cs) = Some (tys, \<alpha>) \<and> (\<forall>i < length Cs. \<LL>\<^sub>\<alpha> (tys ! i) (Cs ! i))"
using \<LL>\<^sub>\<alpha>.cases[OF assms]
by (metis (no_types, lifting) mctxt.distinct(3) mctxt.distinct(5) mctxt.inject(2))

(* ??? maybe use only "L \<in> \<LL>" and "N \<in> \<LL>" as assms *)
lemma \<LL>\<^sub>\<alpha>_sup_mctxt:
  fixes L N :: "('f, 'v) mctxt"
  assumes cmp: "(L, N) \<in> comp_mctxt" and "\<LL>\<^sub>\<alpha> \<alpha> L" and "\<LL>\<^sub>\<alpha> \<alpha> N"
  shows "\<LL>\<^sub>\<alpha> \<alpha> (L \<squnion> N)"
proof -
  have "comp_mctxtp L N" using cmp by (auto simp: comp_mctxt_def)
  then show ?thesis using \<open>\<LL>\<^sub>\<alpha> \<alpha> L\<close> \<open>\<LL>\<^sub>\<alpha> \<alpha> N\<close>
  proof (induction L N arbitrary: \<alpha> rule: comp_mctxtp.induct)
    case (MFun f f' Cs Cs')
    then obtain tys where f_prop: "sigF (f, length Cs) = Some (tys, \<alpha>)"
      using consistent_\<LL>\<^sub>\<alpha> by blast
    let ?Cs = "map (\<lambda>(x, y). x \<squnion> y) (zip Cs Cs')"
    have lengths: "length ?Cs = length Cs" using \<open>length Cs = length Cs'\<close> by simp
    then have f_Ds_prop: "sigF (f, length ?Cs) = Some (tys, \<alpha>)" using f_prop by simp
    { fix i
      assume "i < length Cs"
      then have "\<LL>\<^sub>\<alpha> (tys ! i) (Cs ! i \<squnion> Cs' ! i)"
        using MFun f_prop consistent_\<LL>\<^sub>\<alpha> by (metis option.inject prod.inject) 
    }
    then show ?case using MFun f_Ds_prop lengths set_zip[of Cs Cs'] by auto
  qed auto
qed

lemma mreplace_at_\<LL>\<^sub>\<alpha>:
  assumes "\<LL>\<^sub>\<alpha> \<alpha> L" "\<LL>\<^sub>\<alpha> \<beta> N" "p \<in> fun_poss_mctxt L"
          "subm_at L p = MFun f Cs" "sigF (f, length Cs) = Some (tys, \<beta>)"
  shows "\<LL>\<^sub>\<alpha> \<alpha> (mreplace_at L p N)"
using assms
proof (induction L p N arbitrary: \<alpha> f Cs rule: mreplace_at.induct)
  case (1 L N) then show ?case using consistent_\<LL>\<^sub>\<alpha> subm_at.simps(1) by force
next
  case (2 f' Cs' i p N)
  have "i < length Cs'" using 2(4) fun_poss_mctxt_def by force
  then have p_in_fun_poss: "p \<in> fun_poss_mctxt (Cs' ! i)" using 2(4) unfolding fun_poss_mctxt_def by simp
  obtain tys' where f_props: "sigF (f', length Cs') = Some (tys', \<alpha>)"
      "\<forall>j<length Cs'. \<LL>\<^sub>\<alpha> (tys' ! j) (Cs' ! j)"
      "length Cs' = length tys'" "lhs_types (f', length Cs') = tys'"
    using consistent_\<LL>\<^sub>\<alpha>[OF 2(2)] arity lhs_types_def by fastforce
  then have ith: "\<LL>\<^sub>\<alpha> (tys' ! i) (Cs' ! i)" using \<open>i < length Cs'\<close> by force
  let ?Cs'' = "take i Cs' @ mreplace_at (Cs' ! i) p N # drop (i + 1) Cs'"
  have replace_ith: "\<LL>\<^sub>\<alpha> (tys' ! i) (mreplace_at (Cs' ! i) p N)"
    using 2(1)[OF ith 2(3) p_in_fun_poss _ 2(6)] 2(5) by fastforce
  moreover have "length ?Cs'' = length Cs'"
    using \<open>i < length Cs'\<close> by simp
  moreover have "\<forall>j<length ?Cs''. \<LL>\<^sub>\<alpha> (tys' ! j) (?Cs'' ! j)"
    using f_props(2) replace_ith \<open>i < length Cs'\<close> \<open>length ?Cs'' = length Cs'\<close>
    by (metis Suc_eq_plus1 nth_list_update_eq nth_list_update_neq upd_conv_take_nth_drop)
  ultimately show ?case using f_props \<open>i < length Cs'\<close> consistent_\<LL>\<^sub>\<alpha>[OF 2(2)] "\<LL>\<^sub>\<alpha>.simps"
    unfolding mreplace_at.simps by metis
qed (auto simp: fun_poss_mctxt_def consistent_\<LL>\<^sub>\<alpha>)

lemma \<LL>_subm:
  assumes "L \<in> \<LL>"
  shows "p \<in> all_poss_mctxt L \<Longrightarrow> subm_at L p \<in> \<LL>"
using assms
proof -
  assume p_prop: "p \<in> all_poss_mctxt L"
  then show ?thesis
  proof (cases L)
    case (MFun f Cs)
      then obtain \<alpha> where "\<LL>\<^sub>\<alpha> \<alpha> L" using assms \<LL>_def by blast
      then obtain tys where f_prop: "sigF (f, length Cs) = Some (tys, \<alpha>)" using consistent_\<LL>\<^sub>\<alpha> MFun by blast
      from \<open>\<LL>\<^sub>\<alpha> \<alpha> L\<close> p_prop show ?thesis using \<LL>_def
      proof (induction "L :: ('f, 'v) mctxt" p arbitrary: \<alpha> f Cs rule: subm_at.induct)
        case (2 f' Cs' i p)
        then have "\<exists>\<beta>. \<LL>\<^sub>\<alpha> \<beta> (Cs' ! i)" using consistent_\<LL>\<^sub>\<alpha> by (auto simp: fun_poss_mctxt_def) blast
        then show ?case using 2 by (auto simp: fun_poss_mctxt_def)
      qed (auto simp: fun_poss_mctxt_def)
  qed (auto simp: \<LL>_def)
qed

lemma \<LL>_sub: "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term C\<langle>t\<rangle>) \<Longrightarrow> \<exists>\<beta>. \<LL>\<^sub>\<alpha> \<beta> (mctxt_of_term t)"
proof (induction C arbitrary: \<alpha>)
  case (More f ss1 C' ss2)
  let ?ts = "map mctxt_of_term (ss1 @ C'\<langle>t\<rangle> # ss2)"
  obtain tys where "sigF (f, length ?ts) = Some (tys, \<alpha>)" using More(2) by (auto elim: \<LL>\<^sub>\<alpha>.cases)
  with More(2) have "\<forall>i<length ?ts. \<LL>\<^sub>\<alpha> (tys ! i) (?ts ! i)"
    by (auto elim: \<LL>\<^sub>\<alpha>.cases)
  then have "\<LL>\<^sub>\<alpha> (tys ! length ss1) (?ts ! length ss1)"
    by (metis length_map add_Suc_right length_Cons length_append less_add_Suc1)
  then show ?case using More(1)
    by (metis list.simps(9) length_map map_append nth_append_length)
qed auto

lemma leq_mctxt_\<LL>\<^sub>\<alpha>_mono:
  assumes "L \<le> N" "\<LL>\<^sub>\<alpha> \<alpha> L" "L = MFun f ts" "N \<in> \<LL>"
  shows "\<LL>\<^sub>\<alpha> \<alpha> N"
proof -
  obtain \<alpha>' where "\<LL>\<^sub>\<alpha> \<alpha>' N" using assms(4) \<LL>_def by auto
  moreover obtain ts' tys where props:
    "N = MFun f ts'" "length ts' = length ts" "sigF (f, length ts) = Some (tys, \<alpha>)"
    using assms less_eq_mctxt_MFunE1 by (metis consistent_\<LL>\<^sub>\<alpha>)
  moreover have "\<alpha>' = \<alpha>" using props assms(2,3) \<open>\<LL>\<^sub>\<alpha> \<alpha>' N\<close> consistent_\<LL>\<^sub>\<alpha> by force
  ultimately show ?thesis using \<LL>_def by auto
qed

(* important lemma for C2 *)
lemma mreplace_at_\<LL>\<^sub>\<alpha>':
  assumes "L \<le> N" "\<LL>\<^sub>\<alpha> \<alpha> L" "N \<in> \<LL>" "\<LL>\<^sub>\<alpha> \<beta> (subm_at L p)" "\<LL>\<^sub>\<alpha> \<beta> (subm_at N p)" 
          "p \<in> all_poss_mctxt L"
  shows "L = MHole \<or> (\<exists>x. L = MVar x) \<or> \<LL>\<^sub>\<alpha> \<alpha> (mreplace_at L p (subm_at N p))"
using assms
proof (induction L N arbitrary: \<alpha> \<beta> p rule: less_eq_mctxt_induct[consumes 0])
  case (4 Cs Ds f)
  then obtain tys where f_props: "sigF (f, length Cs) = Some (tys, \<alpha>)"
      "\<forall>j<length Cs. \<LL>\<^sub>\<alpha> (tys ! j) (Cs ! j)"
      "length Cs = length tys" "lhs_types (f, length Cs) = tys"
    using consistent_\<LL>\<^sub>\<alpha>[OF 4(5)] arity lhs_types_def by fastforce
  have "\<LL>\<^sub>\<alpha> \<alpha> (MFun f Ds)" using leq_mctxt_\<LL>\<^sub>\<alpha>_mono[OF 4(4) 4(5) _ 4(6), of f Cs] by simp
  have Ds_props: "\<forall>j<length Ds. \<LL>\<^sub>\<alpha> (tys ! j) (Ds ! j)"
    using 4(1) f_props(1) consistent_\<LL>\<^sub>\<alpha>[OF \<open>\<LL>\<^sub>\<alpha> \<alpha> (MFun f Ds)\<close>] by fastforce
  from 4 have "\<LL>\<^sub>\<alpha> \<alpha> (mreplace_at (MFun f Cs) p (subm_at (MFun f Ds) p))"
  proof (induction p)
    case Nil then show ?case by simp (metis consistent_\<LL>\<^sub>\<alpha> old.prod.inject option.sel)
  next
    case (Cons i p')
    have "i < length Cs" using Cons(2,10) by simp
    moreover have "Ds ! i \<in> \<LL>"
      using \<open>i < length Cs\<close> Cons(2,7) \<LL>_def Ds_props mem_Collect_eq by auto
    ultimately consider "Cs ! i = MHole \<or> (\<exists>x. Cs ! i = MVar x)" |
          "\<LL>\<^sub>\<alpha> (tys ! i) (mreplace_at (Cs ! i) p' (subm_at (Ds ! i) p'))"
      using Cons(4)[of i "tys ! i" \<beta> p'] Cons(2,3,8,9,10) f_props(2) by auto
    then show ?case
    proof (cases)
      case 1
      then have "p' = []" using Cons(10) by auto
      let ?Cs' = "take i Cs @ Ds ! i # drop (Suc i) Cs"
      have "\<LL>\<^sub>\<alpha> (tys ! i) (Ds ! i)" using Ds_props \<open>i < length Cs\<close> Cons(2) by simp
      have length_Cs': "length ?Cs' = length Cs" using \<open>i < length Cs\<close> by simp
      { fix j
        assume "j < length ?Cs'"
        then have "\<LL>\<^sub>\<alpha> (tys ! j) (?Cs' ! j)" using f_props(2,3) \<open>\<LL>\<^sub>\<alpha> (tys ! i) (Ds ! i)\<close> \<open>i < length Cs\<close>
          by (metis length_Cs' less_imp_le_nat nth_append_take nth_append_take_drop_is_nth_conv)
      }
      then have "\<LL>\<^sub>\<alpha> \<alpha> (MFun f ?Cs')" using f_props(1) 4(1) \<open>i < length Cs\<close> length_Cs'
        by (metis \<LL>\<^sub>\<alpha>.simps)
      then show ?thesis using \<open>p' = []\<close> by simp
    next
      case 2
      let ?Cs' = "take i Cs @ mreplace_at (Cs ! i) p' (subm_at (Ds ! i) p') # drop (Suc i) Cs"
      have length_Cs': "length ?Cs' = length Cs" using \<open>i < length Cs\<close> by simp
      { fix j
        assume "j < length ?Cs'"
        then have "\<LL>\<^sub>\<alpha> (tys ! j) (?Cs' ! j)" using f_props(2,3) 2 \<open>i < length Cs\<close>
          by (metis length_Cs' less_imp_le_nat nth_append_take nth_append_take_drop_is_nth_conv)
      }
     then have "\<LL>\<^sub>\<alpha> \<alpha> (MFun f ?Cs')" using f_props(1) 4(1) \<open>i < length Cs\<close> length_Cs'
        by (metis \<LL>\<^sub>\<alpha>.simps)
      then show ?thesis by simp
    qed
  qed
  then show ?case by blast
qed (auto simp: assms)

lemma mreplace_at_mhole:
  assumes "p \<in> all_poss_mctxt C" and "D \<noteq> MHole"
  shows "mreplace_at C p D \<noteq> MHole"
using assms
proof -
  have "p \<in> all_poss_mctxt (mreplace_at C p D)"
    by (simp add: all_poss_mctxt_mreplace_atI1 assms(1))
  then show ?thesis using \<open>D \<noteq> MHole\<close> by force
qed

lemma persistent_layer_system: "layer_system \<F> \<LL>"
proof
  show "\<LL> \<subseteq> layer_system_sig.\<C> \<F>"
  proof
    fix C :: "('f, 'v) mctxt"
    assume "C \<in> \<LL>"
    then show "C \<in> layer_system_sig.\<C> \<F>"
      using funas_\<LL> layer_system_sig.\<C>_def by blast
  qed
next (* L1 *)
  fix t :: "('f, 'v) term"
  assume funas_t: "funas_term t \<subseteq> \<F>"
  then show "\<exists>L\<in>\<LL> . L \<noteq> MHole \<and> L \<le> mctxt_of_term t"
  proof (cases t)
    case (Fun f ts)
    then obtain tys \<alpha> where f_in_\<F>: "sigF (f, length ts) = Some (tys, \<alpha>)"
      using funas_t \<F>_def by fastforce
    let ?top = "MFun f (replicate (List.length ts) MHole)"
    have cond: "?top \<noteq> MHole \<and> ?top \<le> mctxt_of_term t"
      using Fun by (auto simp: less_eq_mctxt_def o_def map_replicate_const)
    have "?top \<in> \<LL>" using \<LL>_def f_in_\<F> by fastforce
    then show ?thesis using cond by auto
  qed (auto simp: \<LL>_def)
next (* L2 *)
  fix C :: "('f, 'v) mctxt" and p :: pos and x :: 'v
  assume p_in_possC: "p \<in> poss_mctxt C"
  { fix \<alpha>
    have "\<LL>\<^sub>\<alpha> \<alpha> (mreplace_at C p (MVar x)) = \<LL>\<^sub>\<alpha> \<alpha> (mreplace_at C p MHole)" using p_in_possC
    proof (induction C p "MVar x :: ('f, 'v) mctxt" arbitrary: \<alpha> rule: mreplace_at.induct)
      case (2 f Cs i p)
      then have p_in_poss_mctxt: "p \<in> poss_mctxt (Cs ! i)" "i < length Cs" by simp+
      let ?Cs' = "take i Cs @ mreplace_at (Cs ! i) p (MVar x) # drop (Suc i) Cs"
      let ?Cs'' = "take i Cs @ mreplace_at (Cs ! i) p MHole # drop (Suc i) Cs"
      have lengths: "length ?Cs' = length Cs" "length ?Cs'' = length Cs"
        using \<open>i < length Cs\<close> by simp+
      then have length_Cs: "Suc (min (length Cs) i + (length Cs - Suc i)) = length Cs" by simp
      then show ?case using 2(1)[OF p_in_poss_mctxt(1)] lengths
        by (auto dest!: consistent_\<LL>\<^sub>\<alpha>)
           (metis lengths \<LL>\<^sub>\<alpha>.simps append_Cons_nth_not_middle nth_append_length)+
    qed auto
  }
  then show "(mreplace_at C p (MVar x) \<in> \<LL>) = (mreplace_at C p MHole \<in> \<LL>)" using \<LL>_def by force
next (* L3 *)
  fix L N :: "('f, 'v) mctxt" and p :: pos
  assume "L \<in> \<LL>" and "N \<in> \<LL>" and p_in_fun_poss: "p \<in> fun_poss_mctxt L" and 
         comp_context: "(subm_at L p, N) \<in> comp_mctxt"
  obtain \<alpha> where "\<LL>\<^sub>\<alpha> \<alpha> L" using \<open>L \<in> \<LL>\<close> \<LL>_def by auto
  then show "mreplace_at L p (subm_at L p \<squnion> N) \<in> \<LL>"
  proof -
    have L_p_in_\<F>: "funas_mctxt (subm_at L p) \<subseteq> \<F>"
      using p_in_fun_poss subm_at_sig fun_poss_all_poss_mctxt funas_\<LL>[OF \<open>L \<in> \<LL>\<close>] by blast
    obtain f Cs where subm_L_p: "subm_at L p = MFun f Cs" "comp_mctxtp (MFun f Cs) N"
      using \<open>p \<in> fun_poss_mctxt L\<close> fun_poss_subm_at comp_context
      by (metis comp_mctxtp_comp_mctxt_eq)
    then obtain \<beta> tys where root_in_\<F>\<^sub>\<beta>: "\<LL>\<^sub>\<alpha> \<beta> (MFun f Cs)" "sigF (f, length Cs) = Some (tys, \<beta>)"
      using \<LL>_def L_p_in_\<F> consistent_\<LL>\<^sub>\<alpha>
            \<LL>_subm[OF \<open>L \<in> \<LL>\<close> fun_poss_all_poss_mctxt[OF p_in_fun_poss]] by force
    then have "\<LL>\<^sub>\<alpha> \<beta> N"
    proof (cases N)
      case (MFun f' Cs')
      then have "f' = f \<and> length Cs' = length Cs"
        using subm_L_p comp_mctxtp.simps[of "subm_at L p" N] by auto
      then show ?thesis using MFun root_in_\<F>\<^sub>\<beta> \<LL>_def \<open>N \<in> \<LL>\<close> consistent_\<LL>\<^sub>\<alpha> by force
    qed auto
    have "\<LL>\<^sub>\<alpha> \<beta> (subm_at L p \<squnion> N)"
      using \<LL>\<^sub>\<alpha>_sup_mctxt[OF comp_context _ \<open>\<LL>\<^sub>\<alpha> \<beta> N\<close>] root_in_\<F>\<^sub>\<beta> subm_L_p by simp
    have "\<LL>\<^sub>\<alpha> \<alpha> (mreplace_at L p (subm_at L p \<squnion> N))"
      using mreplace_at_\<LL>\<^sub>\<alpha>[OF \<open>\<LL>\<^sub>\<alpha> \<alpha> L\<close> \<open>\<LL>\<^sub>\<alpha> \<beta> (subm_at L p \<squnion> N)\<close> p_in_fun_poss subm_L_p(1) root_in_\<F>\<^sub>\<beta>(2)] .
    then show ?thesis using \<LL>_def by auto
  qed
qed

sublocale layer_system "\<F>" "\<LL>" using persistent_layer_system .

context
begin

lemma max_top_persistent_in_layers: "\<LL>\<^sub>\<alpha> \<alpha> (max_top_persistent \<alpha> t)"
proof (induction t rule: max_top_persistent.induct)
  case (2 \<alpha> f ts) then show ?case
  proof (cases "max_top_persistent \<alpha> (Fun f ts)")
    case (MFun f' Cs)
    then obtain tys where f_prop: "sigF (f, length ts) = Some (tys, \<alpha>)" by fastforce
    then have "f' = f" using MFun max_top_persistent.simps(2) mctxt.distinct(5) mctxt.inject(2) by simp
    have lengths1: "length (zip (lhs_types (f, length ts)) ts) = length ts"
      using arity f_prop lhs_types_def by auto
    then have lengths: "length Cs = length ts"
      "Cs = (map (case_prod max_top_persistent) (zip (lhs_types (f, length ts)) ts))"
      using MFun max_top_persistent.simps(2) f_prop by auto
    then have f'_prop: "sigF (f', length Cs) = Some (tys, \<alpha>)" using MFun \<open>f' = f\<close> f_prop by simp
    have tys_def: "lhs_types (f, length ts) = tys" using f_prop lhs_types_def by simp
    { fix i
      assume "i < length Cs"
      then have "(tys ! i, ts ! i) \<in> set (zip (lhs_types (f, length ts)) ts)" using tys_def
        using in_set_conv_nth lengths1 lengths(1) nth_zip by fastforce 
      then have subts_in_layers: "\<LL>\<^sub>\<alpha> (tys ! i) (max_top_persistent (tys ! i) (ts ! i))"
        using f_prop 2 lhs_types_def by blast
      then have "max_top_persistent (tys ! i) (ts ! i) = Cs ! i"
        using tys_def lengths \<open>i < length Cs\<close> by simp
      then have "\<LL>\<^sub>\<alpha> (tys ! i) (Cs ! i)" using subts_in_layers by simp
    }
    then show ?thesis using MFun f'_prop lengths by auto
  qed auto
qed auto

lemma max_top_persistent_mfun:
  assumes "sigF (f, length ts) = Some (tys, \<alpha>)"
  shows "\<exists>Cs. Cs = (map (case_prod max_top_persistent) (zip tys ts)) \<and>
              max_top_persistent \<alpha> (Fun f ts) = MFun f Cs \<and> length Cs = length ts"
using assms arity lhs_types_def by simp

lemma top_less_eq: "max_top_persistent \<alpha> t \<le> mctxt_of_term t"
proof (induction t rule: max_top_persistent.induct)
  case (2 \<beta> f ts) then show ?case
  proof (cases "\<exists>tys. sigF (f, length ts) = Some (tys, \<beta>)")
    case True 
      then obtain tys where f_props: "sigF (f, length ts) = Some (tys, \<beta>)" 
                                     "length ts = length tys" "lhs_types (f, length ts) = tys"
        using arity lhs_types_def by fastforce
      have lengths: "length (zip (lhs_types (f, length ts)) ts) = length ts"
        using f_props by (metis (no_types) length_zip min_def)
      { fix i
        assume "i < length ts"
        then have "(tys ! i, ts ! i) \<in> set (zip (lhs_types (f, length ts)) ts)"
          using f_props in_set_conv_nth length_zip by fastforce
        then have "map (\<lambda>(x, y). max_top_persistent x y) (zip (lhs_types (f, length ts)) ts) ! i
               \<le> map mctxt_of_term ts ! i"
          using 2 \<open>i < length ts\<close> lhs_types_def f_props(1) arity by simp 
      } note inner = this
      then show ?thesis using lengths f_props(1)
        by (metis max_top_persistent.simps(2) mctxt_of_term.simps(2) length_map mfun_leq_mfunI)
  qed simp
qed simp

lemma max_top_var_\<alpha>: "max_topC_\<alpha> \<alpha> (mctxt_of_term (Var x)) = MVar x"
proof -
  have mvar_in_topsC: "MVar x \<in> topsC_\<alpha> \<alpha> (MVar x)"
    unfolding layer_system_sig.topsC_def by blast
  from max_top_not_hole[of "Var x"] have "max_top (Var x) \<noteq> MHole" by simp
  then show ?thesis
    using mvar_in_topsC unfolding layer_system_sig.max_topC_def 
          layer_system_sig.topsC_def by fastforce
qed


lemma max_top_unique_\<alpha>:
  shows "\<exists>!M. M \<in> topsC_\<alpha> \<alpha> C \<and> (\<forall>L \<in> topsC_\<alpha> \<alpha> C. L \<le> M)"
proof -
  let ?topsC' = "layer_system_sig.topsC { L . \<exists>\<alpha>. \<LL>\<^sub>\<alpha> \<alpha> L }" and
      ?topsC_\<alpha> = "topsC_\<alpha> \<alpha>"
  have mhole_in_tops_\<alpha>: "\<forall>C. MHole \<in> topsC_\<alpha> \<alpha> C"
    using layer_system_sig.topsC_def less_eq_mctxtI1(1) by blast
  have "topsC C = ?topsC' C"
    using topsC_def[of C] \<LL>_def layer_system_sig.topsC_def[of "{ L . \<exists>\<alpha>. \<LL>\<^sub>\<alpha> \<alpha> L }" C] by simp
  then have "\<exists>!M. M \<in> ?topsC' C \<and> (\<forall>L\<in>?topsC' C. L \<le> M)"
    using max_top_unique by (metis (no_types, lifting))
  then obtain M \<beta> where M_props: "M \<in> ?topsC' C" "\<forall>L\<in>?topsC' C. L \<le> M" "\<LL>\<^sub>\<alpha> \<beta> M"
      using layer_system_sig.topsC_def[of "{L. \<exists>\<alpha>. \<LL>\<^sub>\<alpha> \<alpha> L}" C] by auto
  then show ?thesis
  proof (cases "\<beta> = \<alpha>")
    case True
    then have "M \<in> topsC_\<alpha> \<alpha> C" using M_props by (simp add: layer_system_sig.topsC_def)
    moreover have "\<forall>L\<in>topsC_\<alpha> \<alpha> C. L \<le> M" using M_props(2)
      by (simp add: layer_system_sig.topsC_def) blast
    ultimately show ?thesis using dual_order.antisym by (simp add: layer_system_sig.topsC_def) blast
  next
    case \<beta>_neq_\<alpha>: False then show ?thesis
    proof (cases "M = MHole \<or> (\<exists>x. M = MVar x)")
      case True
      then have "M \<in> topsC_\<alpha> \<alpha> C" using M_props by (auto simp: layer_system_sig.topsC_def)
      moreover have "\<forall>L\<in>topsC_\<alpha> \<alpha> C. L \<le> M" using M_props(2)
        by (simp add: layer_system_sig.topsC_def) blast
      ultimately show ?thesis using dual_order.antisym by blast
    next
      case False
      then obtain f Cs where M_def: "M = MFun f Cs" using mctxt_neq_mholeE by blast
      then obtain tys where f_prop: "sigF (f, length Cs) = Some (tys, \<beta>)"
        using M_props \<LL>\<^sub>\<alpha>.simps by blast
      have "M \<le> C" using M_props layer_system_sig.topsC_def by blast
      then obtain Cs' where C_def: "C = MFun f Cs'" "length Cs' = length Cs"
        using M_def less_eq_mctxt_MFunE1 by metis
      { fix L :: "('f, 'v) mctxt"
        assume "L \<in> topsC_\<alpha> \<alpha> C"
        then have "L \<le> C" using M_props layer_system_sig.topsC_def by blast
        then have "L = MHole"
        proof (cases L)
          case MVar then show ?thesis using \<open>L \<le> C\<close> C_def by (meson less_eq_mctxt_MVarE1 mctxt.simps(6))
        next
          case (MFun f' Cs'')
          then have "f' = f \<and> length Cs'' = length Cs'"
            using \<open>L \<le> C\<close> C_def(1) less_eq_mctxt_MFunE1 mctxt.inject(2) by fastforce
          then have "\<not> (\<exists>tys. sigF (f', length Cs'') = Some (tys, \<alpha>))"
            using f_prop C_def(2) \<beta>_neq_\<alpha> by simp
          then show ?thesis using MFun \<open>L \<in> topsC_\<alpha> \<alpha> C\<close> layer_system_sig.topsC_def[of "{L. \<LL>\<^sub>\<alpha> \<alpha> L}" C]
            by (metis (no_types, lifting) consistent_\<LL>\<^sub>\<alpha> mem_Collect_eq)
        qed
      }
      then show ?thesis using mhole_in_tops_\<alpha> by blast
    qed
  qed
qed

lemma max_top_persist_mono:
  assumes "L \<le> mctxt_of_term t" and "\<LL>\<^sub>\<alpha> \<alpha> L"
  shows "L \<le> max_top_persistent \<alpha> t"
using assms
proof (induction L "mctxt_of_term t" arbitrary: t \<alpha> rule: less_eq_mctxt_induct)
  case (2 x)
  then show ?case by (metis eq_iff max_top_persistent.simps(1) term_of_mctxt.simps(1)
                 term_of_mctxt_mctxt_of_term_id)
next
  case (3 Cs Ds f)
  from 3(5) obtain tys where f_prop: "sigF (f, length Cs) = Some (tys, \<alpha>)" "length tys = length Cs"
    using consistent_\<LL>\<^sub>\<alpha> arity by blast
  obtain ts where t_def: "t = Fun f ts" "map mctxt_of_term ts = Ds" "length ts = length Ds"
    using 3(4) mctxt_of_term.simps(2)
    by (metis length_map mctxt.inject(2) term_of_mctxt.simps(2) term_of_mctxt_mctxt_of_term_id)
  then have unfolded_max_top_persist: "max_top_persistent \<alpha> t = MFun f (map (case_prod max_top_persistent)
          (zip tys ts))" using f_prop 3(1) max_top_persistent_mfun by force
  { fix i
    assume i_props: "i < length Cs" "Ds ! i = mctxt_of_term (ts ! i)"
    then have "Cs ! i \<le> Ds ! i" using 3 by fast
    moreover have "\<LL>\<^sub>\<alpha> (tys ! i) (Cs ! i)" using consistent_\<LL>\<^sub>\<alpha> f_prop i_props 3(5) by force
    ultimately have "Cs ! i \<le> max_top_persistent (tys ! i) (ts ! i)" using i_props 3(3) by simp
  }
  then show ?case using 3(1) 3(4) f_prop t_def unfolded_max_top_persist
                   mfun_leq_mfunI[of f f Cs "(map (\<lambda>(x, y). max_top_persistent x y) (zip tys ts))"]
    by (simp add: map_nth_eq_conv)
qed auto

lemma max_topC_props_\<alpha>[simp]:
  shows "max_topC_\<alpha> \<alpha> C \<in> topsC_\<alpha> \<alpha> C" and "\<And>L. L \<in> topsC_\<alpha> \<alpha> C \<Longrightarrow> L \<le> max_topC_\<alpha> \<alpha> C"
by (auto simp: theI'[OF max_top_unique_\<alpha>] layer_system_sig.max_topC_def)

lemma max_top_persistent_correct_\<alpha>:
  "max_top_persistent \<alpha> t = layer_system_sig.max_top { L . \<LL>\<^sub>\<alpha> \<alpha> L } t"
proof (induction t)
  case (Var x) then show ?case using max_top_var_\<alpha> by simp
next
  case (Fun f ts) then show ?case
  proof (cases "\<exists>tys. sigF (f, length ts) = Some (tys, \<alpha>)")
    case True
    then obtain tys where f_props: "sigF (f, length ts) = Some (tys, \<alpha>)"
                                   "length ts = length tys" "lhs_types (f, length ts) = tys"
      using arity lhs_types_def by fastforce
    let ?Cs = "map (case_prod max_top_persistent) (zip tys ts)"
    have unfold_max_top_persist: "max_top_persistent \<alpha> (Fun f ts) = MFun f ?Cs"
      using f_props by simp 
    { fix L
      assume L_props: "L \<le> MFun f (map mctxt_of_term ts)" "\<LL>\<^sub>\<alpha> \<alpha> L"
      then have "L \<le> MFun f ?Cs" using max_top_persist_mono[of L]
        by (metis mctxt_of_term.simps(2) unfold_max_top_persist)
    }                           
    then have less_than_max_top_persistent: "\<LL>\<^sub>\<alpha> \<alpha> L \<and> L \<le> MFun f (map mctxt_of_term ts)
                                      \<longrightarrow> L \<le> MFun f ?Cs" for L by auto
    then have in_\<LL>\<^sub>\<alpha>: "\<LL>\<^sub>\<alpha> \<alpha> (MFun f ?Cs)" using max_top_persistent_in_layers f_props by auto
    have is_top: "MFun f ?Cs \<le> MFun f (map mctxt_of_term ts)"
      using unfold_max_top_persist by (metis (full_types) mctxt_of_term.simps(2) top_less_eq)
    have max_top_lt_max_top_persist: "layer_system_sig.max_top { L . \<LL>\<^sub>\<alpha> \<alpha> L } (Fun f ts) \<le> MFun f ?Cs"
      using less_than_max_top_persistent max_topC_props_\<alpha>(1)
            layer_system_sig.topsC_def[of "{ L . \<LL>\<^sub>\<alpha> \<alpha> L }"]
      by (metis (no_types, lifting) mctxt_of_term.simps(2) mem_Collect_eq)
    have "MFun f ?Cs \<le> max_topC_\<alpha> \<alpha> (MFun f (map mctxt_of_term ts))"
      using is_top in_\<LL>\<^sub>\<alpha> layer_system_sig.topsC_def max_topC_props_\<alpha>(2) by blast
    then show ?thesis
      using max_top_lt_max_top_persist unfold_max_top_persist dual_order.antisym by auto
  next
    case False
    then have "length cs = length ts \<longrightarrow> \<not> \<LL>\<^sub>\<alpha> \<alpha> (MFun f cs)" for cs by (metis consistent_\<LL>\<^sub>\<alpha>)
    then have top_is_hole: "\<LL>\<^sub>\<alpha> \<alpha> L \<and> L \<le> MFun f (map mctxt_of_term ts) \<longrightarrow> L = MHole" for L 
      by (auto elim: less_eq_mctxt_MFunE2)
    { fix L
      assume "layer_system_sig.max_topC {L. \<LL>\<^sub>\<alpha> \<alpha> L} (mctxt_of_term (Fun f ts)) = L"
      then have L_props: "L \<in> layer_system_sig.topsC {L'. \<LL>\<^sub>\<alpha> \<alpha> L'} (mctxt_of_term (Fun f ts)) \<and>
            (\<forall>L'\<in>layer_system_sig.topsC {L'. \<LL>\<^sub>\<alpha> \<alpha> L'} (mctxt_of_term (Fun f ts)). L' \<le> L)"
        using layer_system_sig.max_topC_def[of "{L. \<LL>\<^sub>\<alpha> \<alpha> L}" "(mctxt_of_term (Fun f ts))"]
              max_top_unique_\<alpha>[of \<alpha> "(mctxt_of_term (Fun f ts))"] by (auto dest!: theI')
      then have "\<LL>\<^sub>\<alpha> \<alpha> L" using layer_system_sig.topsC_def[of "{L. \<LL>\<^sub>\<alpha> \<alpha> L}"] by blast
      have "L \<le> MFun f (map mctxt_of_term ts)" using layer_system_sig.topsC_def L_props by auto
      then have "L = MHole" using top_is_hole \<open>\<LL>\<^sub>\<alpha> \<alpha> L\<close> by simp
    }
    then have "layer_system_sig.max_topC {L. \<LL>\<^sub>\<alpha> \<alpha> L} (mctxt_of_term (Fun f ts)) = MHole" by blast
    then show ?thesis using False by simp
  qed
qed
end

lemma L_not_in_\<LL>\<^sub>\<beta>: 
  assumes f_in_\<F>\<^sub>\<alpha>: "sigF (f, length Cs) = Some (tys, \<alpha>)"
  shows "L \<in> \<LL> \<and> L \<le> MFun f Cs \<longleftrightarrow> \<LL>\<^sub>\<alpha> \<alpha> L \<and> L \<le> MFun f Cs"
proof (cases "L \<le> MFun f Cs")
  case True then show ?thesis
  proof (cases L)
    case (MFun f' Cs')
    then have "f' = f" "length Cs' = length Cs"
      using True less_eq_mctxt_MFunE2
      by (fastforce, metis mctxt.distinct(5) mctxt.inject(2))
    then have "\<alpha> \<noteq> \<beta> \<longrightarrow> \<not> \<LL>\<^sub>\<alpha> \<beta> L" for \<beta> using MFun f_in_\<F>\<^sub>\<alpha> \<LL>\<^sub>\<alpha>.cases by fastforce
    then show ?thesis using \<LL>_def by fast
  qed auto
qed simp

(* important *)
lemma max_top_persistent_correct_\<F>\<^sub>\<alpha>: "sigF (f, length ts) = Some (tys, \<alpha>) \<Longrightarrow>
      max_top_persistent \<alpha> (Fun f ts) = max_top (Fun f ts) \<and>
      (\<beta> \<noteq> \<alpha> \<longrightarrow> max_top_persistent \<beta> (Fun f ts) = MHole)"
using max_top_persistent_correct_\<alpha>[of \<alpha> "Fun f ts"] 
by (auto simp: layer_system_sig.max_topC_def layer_system_sig.topsC_def L_not_in_\<LL>\<^sub>\<beta>)

lemma max_top_MFun_\<alpha>:
  assumes "max_top t = MFun f Cs"
  shows "\<exists>\<alpha>. max_top t = max_top_persistent \<alpha> t"
using assms
proof (induction t arbitrary: f Cs)
  case Var then show ?case using max_top_var by auto
next
  case (Fun f' ts)
  have similar: "f = f' \<and> length Cs = length ts" using Fun(2) max_topC_props(1) unfolding topsC_def 
    by (metis (no_types, lifting) length_map less_eq_mctxt_MFunE1
        mctxt.inject(2) mctxt_of_term.simps(2) mem_Collect_eq)
  have "MFun f Cs \<in> \<LL>" using Fun max_topC_layer[of "MFun f' (map mctxt_of_term ts)"] by simp
  then obtain \<alpha> tys where "sigF (f, length Cs) = Some (tys, \<alpha>)"
    using \<LL>_def consistent_\<LL>\<^sub>\<alpha> by blast
  then have "max_top (Fun f' ts) = max_top_persistent \<alpha> (Fun f' ts)"
    using max_top_persistent_correct_\<F>\<^sub>\<alpha>[of f' ts tys \<alpha>] similar by auto
  then show ?case by blast
qed

lemma max_top_Fun_\<alpha>:
  shows "\<exists>\<alpha>. max_top (Fun f ts) = max_top_persistent \<alpha> (Fun f ts)"
using max_top_persistent_correct_\<F>\<^sub>\<alpha> max_top_MFun_\<alpha>
  by (metis less_eq_mctxtE2(3) max_top_persistent.simps(2) max_top_prefix mctxt_of_term.simps(2)) 

lemma max_top_var_weak1:
  "max_top t = MVar x \<longleftrightarrow> Var x = t"
by (metis (no_types, lifting) less_eq_mctxt_MVarE1 max_topC_props(1)  
    max_top_var mem_Collect_eq term_of_mctxt_mctxt_of_term_id topsC_def)

lemma mctxt_leq_\<LL>\<^sub>\<alpha>:
  assumes "L \<le> N" "\<LL>\<^sub>\<alpha> \<alpha> N"
  shows "\<LL>\<^sub>\<alpha> \<alpha> L"
using assms
proof (induction "L :: ('f, 'v) mctxt" N arbitrary: \<alpha> rule: less_eq_mctxt_induct)
  case (3 Cs Ds f \<alpha>)
  then obtain tys where f_prop: "sigF (f, length Ds) = Some (tys, \<alpha>)" using consistent_\<LL>\<^sub>\<alpha> by blast
  { fix i
    assume "i < length Cs"
    then have "\<LL>\<^sub>\<alpha> (tys ! i) (Ds ! i)" using f_prop 3 consistent_\<LL>\<^sub>\<alpha> by fastforce
    then have "\<LL>\<^sub>\<alpha> (tys ! i) (Cs ! i)" using \<open>i < length Cs\<close> 3(3) 3(4) by blast
  }
  then show ?case using 3(1) f_prop by auto
qed auto

lemma mctxt_leq_subm_at_\<LL>\<^sub>\<alpha>:
  assumes "L \<le> N" "p \<in> all_poss_mctxt L" "\<LL>\<^sub>\<alpha> \<alpha> (subm_at N p)"
  shows "\<LL>\<^sub>\<alpha> \<alpha> (subm_at L p)"
using mctxt_leq_\<LL>\<^sub>\<alpha>[OF less_eq_subm_at[OF assms(2) assms(1)], OF assms(3)] .

lemma max_max_top: "max_top_persistent \<alpha> t \<le> max_top t"
using max_top_persistent_correct_\<F>\<^sub>\<alpha>
by (induction \<alpha> t rule: "max_top_persistent.induct") auto

abbreviation mtp where "mtp \<equiv> \<lambda>\<alpha> x. mctxt_term_conv (max_top_persistent \<alpha> x)"
abbreviation push_in_ctxt where
  "push_in_ctxt s t C \<alpha> D \<beta> \<equiv> mtp \<alpha> C\<langle>s\<rangle> = D\<langle>mtp \<beta> s\<rangle> \<and> mtp \<alpha> C\<langle>t\<rangle> = D\<langle>mtp \<beta> t\<rangle> \<and>
                               hole_pos C = hole_pos D"

lemma push_mt_ctxt:
  assumes "p = hole_pos C" "p \<in> fun_poss_mctxt (max_top_persistent \<alpha> C\<langle>s\<rangle>)"
  shows "\<exists>D \<gamma>. push_in_ctxt s t C \<alpha> D \<gamma>"
using assms(2) unfolding assms(1)
proof (induction C arbitrary: \<alpha>)
  case Hole
  then have "push_in_ctxt s t \<box> \<alpha> \<box> \<alpha>" by simp
  then show ?case by blast
next
  case (More f ss1 C' ss2)
  let ?Cs = "ss1 @ C'\<langle>s\<rangle> # ss2"
  show ?case
  proof (cases "\<exists>tys. sigF (f, length ?Cs) = Some (tys, \<alpha>)")
    case True
    then obtain tys where f_props: "sigF (f, length ?Cs) = Some (tys, \<alpha>)"
                                   "length ?Cs = length tys" "lhs_types (f, length ?Cs) = tys"
      using arity lhs_types_def by fastforce
    let ?Ds = "map (\<lambda>(x, y). max_top_persistent x y) (zip (take (length ss1) tys) ss1) @
              max_top_persistent (tys ! length ss1) C'\<langle>s\<rangle> # 
              map (\<lambda>(x, y). max_top_persistent x y) (zip (drop (Suc (length ss1)) tys) ss2)"
    have "tys = (take (length ss1) tys) @ (tys ! length ss1) # (drop (Suc (length ss1)) tys)"
      using f_props(2) id_take_nth_drop[of "length ss1" tys] by fastforce
    then obtain tys1 ty tys2 where tys_def: "tys = tys1 @ ty # tys2" "length tys1 = length ss1"
      by fastforce
    have mt_unfold: "max_top_persistent \<alpha> (More f ss1 C' ss2)\<langle>s\<rangle> = MFun f ?Ds"
      using f_props tys_def(2) unfolding tys_def(1) by (auto simp: append_Cons_nth_middle)
    have "length (map (mctxt_term_conv \<circ> (\<lambda>(x, y). max_top_persistent x y)) (zip tys1 ss1)) = length ss1"
      using length_map length_zip tys_def(2) by force
    then have "hole_pos C' \<in> fun_poss_mctxt (max_top_persistent (tys ! length ss1) C'\<langle>s\<rangle>)"
      using f_props More(2) tys_def(2) nth_append_length
        [of "map (mctxt_term_conv \<circ> (\<lambda>(x, y). max_top_persistent x y)) (zip tys1 ss1)"]
      unfolding tys_def(1) mt_unfold by (auto simp: fun_poss_mctxt_def)
    then obtain D' \<beta>' where inner: "push_in_ctxt s t C' (tys ! length ss1) D' \<beta>'"
      using More(1) by fast
    let ?D = "More f (map (mctxt_term_conv \<circ> (\<lambda>(x, y). max_top_persistent x y)) (zip tys1 ss1)) D'
                     (map (mctxt_term_conv \<circ> (\<lambda>(x, y). max_top_persistent x y)) (zip tys2 ss2))"
    have "push_in_ctxt s t (More f ss1 C' ss2) \<alpha> ?D \<beta>'"
      using inner f_props tys_def(2) unfolding tys_def(1)
      by (simp add: append_Cons_nth_middle)
    then show ?thesis by blast
  next
    case False then show ?thesis using More(2) by (simp add: fun_poss_mctxt_def)
  qed
qed

lemma map_equiv:
  assumes "length ls2 = length ls1" "\<forall>i < length ls2. f (ls1 ! i, ls2 ! i) = g (ls2 ! i)"
  shows "map f (zip ls1 ls2) = map g ls2"
using assms
proof (induction ls2 arbitrary: ls1)
  case (Cons a ls2')
  then obtain b ls1' where "ls1 = b # ls1'" by (cases ls1) auto
  then show ?case using Cons by fastforce
qed simp

lemma push_mt_subst:
  assumes "\<T>\<^sub>\<alpha> \<alpha> t"
  shows "mtp \<alpha> (t \<cdot> \<sigma>) = t \<cdot> (\<lambda>x. mtp (the (sigV x)) (\<sigma> x))"
using assms
proof (induction t)
  case (funs f ts tys \<beta>)
  then have lengths: "length ts = length tys" using arity by simp
  let ?f = "mctxt_term_conv \<circ> (\<lambda>(x, y). max_top_persistent x (y \<cdot> \<sigma>))" and
      ?g = "\<lambda>t. t \<cdot> (\<lambda>x. mtp (the (sigV x)) (\<sigma> x))"
  have "map ?f (zip tys ts) = map ?g ts"
    using funs(2) map_equiv[OF lengths, of ?f ?g] unfolding map_zip_map2 by simp
  then show ?case using funs lhs_types_def by (auto simp: map_zip_map2)
qed simp

text \<open>main lemma for condition C_1 in proof of layered\<close>
lemma lemma_C\<^sub>1:
  fixes p :: pos and s t :: "('f, 'v) term" and r and \<sigma>
  assumes "s \<in> \<T>" and "t \<in> \<T>" and p_fun_poss: "p \<in> fun_poss_mctxt (max_top s)" and
          rstep_s_t: "(s, t) \<in> rstep_r_p_s' \<R> r p \<sigma>" and
          s_def_t_def: "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>" "r \<in> \<R>" and
          p_def: "p = hole_pos C" and
          root_s: "\<exists>f ts. s = Fun f ts \<and> sigF (f, length ts) = Some (tys, \<alpha>)"
  shows "\<exists>\<tau>. (mctxt_term_conv (max_top s), mctxt_term_conv (max_top t)) \<in> rstep_r_p_s' \<R> r p \<tau> \<or>
             (mctxt_term_conv (max_top s), mctxt_term_conv MHole) \<in> rstep_r_p_s' \<R> r p \<tau>"
proof -
  let ?M = "max_top s" and ?L = "max_top t"
  obtain f ts where s_def: "s = Fun f ts"
              and f_props: "sigF (f, length ts) = Some (tys, \<alpha>)" "length ts = length tys"
                           "lhs_types (f, length ts) = tys"
    using root_s arity lhs_types_def by fastforce
  then have mtp_eq: "max_top_persistent \<alpha> s = max_top s" 
    using max_top_persistent_correct_\<F>\<^sub>\<alpha> by blast
  have p_fun_poss_max_top: "p \<in> fun_poss_mctxt (max_top_persistent \<alpha> s)" 
    using mtp_eq \<open>p \<in> fun_poss_mctxt ?M\<close> by simp
  then have p_in_poss_max_top: "p \<in> all_poss_mctxt (max_top_persistent \<alpha> C\<langle>t\<rangle>)" for t
    unfolding s_def_t_def p_def
    using fun_poss_mctxt_subset_all_poss_mctxt[of "max_top_persistent \<alpha> t"]
          lhs_types_def
    proof (induction C arbitrary: \<alpha>)
      case More then show ?case using fun_poss_mctxt_def fun_poss_mctxt_subset_all_poss_mctxt
        by (auto simp: nth_append_length[of "map f xs" for f xs, unfolded length_map]
            fun_poss_mctxt_def split: if_splits) blast
    qed auto
  let ?\<sigma> = "\<lambda>x. mtp (the (sigV x)) (\<sigma> x)"
  have "\<exists>D \<beta>. push_in_ctxt (fst r \<cdot> \<sigma>) t C \<alpha> D \<beta>" for t
    using push_mt_ctxt[OF p_def p_fun_poss_max_top[unfolded s_def_t_def]] by simp
  then obtain D \<beta> where in_ctxt: "mtp \<alpha> C\<langle>(fst r \<cdot> \<sigma>)\<rangle> = D\<langle>mtp \<beta> (fst r \<cdot> \<sigma>)\<rangle> \<and>
                                  mtp \<alpha> C\<langle>(snd r \<cdot> \<sigma>)\<rangle> = D\<langle>mtp \<beta> (snd r \<cdot> \<sigma>)\<rangle>"
                                  "hole_pos C = hole_pos D" by blast
  obtain \<beta>' where rule_type: "\<T>\<^sub>\<alpha> \<beta>' (fst r)" "\<T>\<^sub>\<alpha> \<beta>' (snd r)"
    using \<open>r \<in> \<R>\<close> R_def[of "fst r" "snd r"] by auto
  { assume "\<beta>' \<noteq> \<beta>"
    obtain g ss where lhs_def: "fst r = Fun g ss"
      using wf \<open>r \<in> \<R>\<close> unfolding wf_trs_def by (metis prod.collapse)
    obtain tys' where "sigF (g, length ss) = Some (tys', \<beta>')"
      using rule_type(1) lhs_def by (metis \<T>\<^sub>\<alpha>.simps term.distinct(1) term.inject(2))
    then have "max_top_persistent \<beta> (fst r \<cdot> \<sigma>) = MHole"
      using max_top_persistent_correct_\<F>\<^sub>\<alpha> \<open>\<beta>' \<noteq> \<beta>\<close> lhs_def by simp
    moreover have "hole_pos D \<in> fun_poss D\<langle>mtp \<beta> (fst r \<cdot> \<sigma>)\<rangle>"
      using p_fun_poss_max_top in_ctxt
      unfolding s_def_t_def(1) fun_poss_mctxt_def p_def by argo
    ultimately have False by (induction D) auto
  }
  then have "\<beta>' = \<beta>" by blast
  then have part2: "mtp \<beta> ((fst r) \<cdot> \<sigma>) = (fst r) \<cdot> ?\<sigma>"
    and part3: "mtp \<beta> ((snd r) \<cdot> \<sigma>) = (snd r) \<cdot> ?\<sigma>"
    using push_mt_subst rule_type by simp+
  have first_half: "mctxt_term_conv (max_top s) = D\<langle>fst r \<cdot> ?\<sigma>\<rangle>"
    using mtp_eq in_ctxt part2 unfolding s_def_t_def(1) by simp
  moreover have second_half: "D\<langle>snd r \<cdot> ?\<sigma>\<rangle> = mtp \<alpha> (C\<langle>snd r \<cdot> \<sigma>\<rangle>)"
    using part3 in_ctxt by metis
  ultimately have "(mctxt_term_conv (max_top C\<langle>fst r \<cdot> \<sigma>\<rangle>), mtp \<alpha> (C\<langle>snd r \<cdot> \<sigma>\<rangle>))
                                                       \<in> rstep_r_p_s' \<R> r p ?\<sigma>" 
    using mtp_eq rstep_s_t \<open>r \<in> \<R>\<close> in_ctxt(2) p_def s_def_t_def(1)
    by (metis (no_types, lifting) rstep_r_p_s'.rstep_r_p_s')
  then have W: "\<exists> \<tau>. max_top_persistent \<alpha> (C\<langle>snd r \<cdot> \<sigma>\<rangle>) \<in> \<LL> \<and>
           (mctxt_term_conv ?M, mtp \<alpha> (C\<langle>snd r \<cdot> \<sigma>\<rangle>)) \<in> rstep_r_p_s' \<R> r p \<tau>"
    using max_top_persistent_in_layers \<LL>_def Un_iff s_def_t_def(1) [folded p_def] by blast
  then obtain \<tau> where step_to_L: "(mctxt_term_conv ?M, mtp \<alpha> (C\<langle>snd r \<cdot> \<sigma>\<rangle>)) \<in> rstep_r_p_s' \<R> r p \<tau>"
    by auto
  then show ?thesis
  proof (cases t)
    case (Var x)
    then show ?thesis using s_def_t_def(2) step_to_L by auto
  next
    case (Fun g ss)
    then show ?thesis using step_to_L s_def_t_def(2) max_top_persistent_correct_\<F>\<^sub>\<alpha>
      by (metis Fun max_top_persistent.simps(2)) 
  qed
qed

sublocale layered "\<F>" "\<LL>"
proof (* trs *)
  show "wf_trs \<R>" using wf .
next (* \<R>_sig *)
  show "funas_trs \<R> \<subseteq> \<F>"
  proof
    fix fn
    assume "fn \<in> funas_trs \<R>"
    then obtain l r :: "('f, 'v) term" where "fn \<in> funas_rule (l, r)" "(l, r) \<in> \<R>"
       unfolding funas_trs_def by fast
    then show "fn \<in> \<F>"
      using R_def[OF \<open>(l, r) \<in> \<R>\<close>] funas_\<T>\<^sub>\<alpha> 
      by (metis funas_rule_def Un_iff fst_conv snd_conv)
  qed
next (* C1 *)
  fix p :: pos and s t :: "('f, 'v) term" and r and \<sigma>
  let ?M = "max_top s" and ?L = "max_top t"
  assume assms: "s \<in> \<T>" "t \<in> \<T>" "p \<in> fun_poss_mctxt ?M" and
         rstep_s_t: "(s, t) \<in> rstep_r_p_s' \<R> r p \<sigma>"
  then obtain C where
    s_def_t_def: "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>" "r \<in> \<R>" and
    p_def: "p = hole_pos C"
    by auto
  show "\<exists>\<tau>. (mctxt_term_conv ?M, mctxt_term_conv ?L) \<in> rstep_r_p_s' \<R> r p \<tau> \<or>
            (mctxt_term_conv ?M, mctxt_term_conv MHole) \<in> rstep_r_p_s' \<R> r p \<tau>"
  proof -
    consider "\<exists>f ts. s = Fun f ts \<and> (f, length ts) \<in> \<F>"
           | "\<exists>x. s = Var x" using \<open>s \<in> \<T>\<close> \<T>_def by (cases s) auto
    then show ?thesis
    proof cases
      case 1
      then obtain f ts tys \<alpha> where "s = Fun f ts" "sigF (f, length ts) = Some (tys, \<alpha>)"
        unfolding \<F>_def by auto
      then show ?thesis using lemma_C\<^sub>1[OF assms rstep_s_t s_def_t_def p_def] by auto
    next
      case 2 then show ?thesis 
      using rstep_s_t wf NF_Var rstep_eq_rstep' rstep'_iff_rstep_r_p_s' prod.collapse
      by metis
    qed
  qed
next (* C2 *) (* this has to be changed to be similar to lemma mreplace_at_\<LL>\<^sub>\<alpha> *)
  fix L N :: "('f, 'v) mctxt" and p :: pos
  assume my_assms: "N \<in> \<LL>" "L \<in> \<LL>" "L \<le> N" "p \<in> hole_poss L"
  then show "mreplace_at L p (subm_at N p) \<in> \<LL>"
  proof -
    obtain \<alpha> where "\<LL>\<^sub>\<alpha> \<alpha> N" using \<open>N \<in> \<LL>\<close> \<LL>_def by auto
    then have "\<LL>\<^sub>\<alpha> \<alpha> L" using \<open>L \<in> \<LL>\<close> \<LL>_def \<open>L \<le> N\<close>
    proof (induction N rule: \<LL>\<^sub>\<alpha>.induct)
      case mhole then show ?case using mctxt_order_bot.bot.extremum_uniqueI by auto
    next
      case mvar then show ?case using less_eq_mctxtE2(2) \<LL>_def by (metis \<LL>\<^sub>\<alpha>.mvar mhole)
    next
      case (mfun f Cs tys \<beta>) then show ?case using L_not_in_\<LL>\<^sub>\<beta> by blast
    qed
    have "p \<in> all_poss_mctxt N"
      using \<open>p \<in> hole_poss L\<close> \<open>L \<le> N\<close> all_poss_mctxt_conv all_poss_mctxt_mono[of L N]
      by auto
    then obtain \<beta> where "\<LL>\<^sub>\<alpha> \<beta> (subm_at N p)" using \<LL>_subm[OF \<open>N \<in> \<LL>\<close>] \<LL>_def by auto
    then have "\<LL>\<^sub>\<alpha> \<beta> (subm_at L p)" using mctxt_leq_subm_at_\<LL>\<^sub>\<alpha>[OF \<open>L \<le> N\<close>, of p \<beta>] \<open>p \<in> hole_poss L\<close>
      by auto
    consider "(L = MHole \<or> (\<exists>x. L = MVar x))" | "\<LL>\<^sub>\<alpha> \<alpha> (mreplace_at L p (subm_at N p))"
      using mreplace_at_\<LL>\<^sub>\<alpha>'[OF my_assms(3) \<open>\<LL>\<^sub>\<alpha> \<alpha> L\<close> my_assms(1) \<open>\<LL>\<^sub>\<alpha> \<beta> (subm_at L p)\<close> \<open>\<LL>\<^sub>\<alpha> \<beta> (subm_at N p)\<close>] 
            my_assms(4) UnCI all_poss_mctxt_conv by fastforce 
    then show ?thesis
    proof (cases)
      case 1 then show ?thesis using \<open>p \<in> hole_poss L\<close> \<open>N \<in> \<LL>\<close> by fastforce
    next
      case 2 then show ?thesis using \<LL>_def by auto
    qed
  qed
qed

lemma conserv_subst:
  assumes "\<T>\<^sub>\<alpha> \<alpha> (t \<cdot> \<sigma>)" and "\<And>x \<beta>. (sigV x = Some \<beta> \<longleftrightarrow> \<T>\<^sub>\<alpha> \<beta> (Var x \<cdot> \<sigma>))"
  shows "\<T>\<^sub>\<alpha> \<alpha> t"
using assms(1)
proof (induction t arbitrary: \<alpha>)
  case (Var x \<beta>)
  then have "sigV x = Some \<beta>" using assms(2) by simp
  then show ?case by auto
next
  case (Fun f ts \<beta>)
  have "length (map (\<lambda>t. t \<cdot> \<sigma>) ts) = length ts" by simp
  then obtain tys where "sigF (f, length ts) = Some (tys, \<beta>)" "\<forall>i<length ts. \<T>\<^sub>\<alpha> (tys ! i) (ts ! i)"
    using Fun \<T>\<^sub>\<alpha>.cases[of \<beta> "Fun f ts \<cdot> \<sigma>"] eval_term.simps(2)[of Fun f ts \<sigma>] nth_map
    proof -
      assume a1: "\<And>tys. \<lbrakk>sigF (f, length ts) = Some (tys, \<beta>); \<forall>i<length ts. \<T>\<^sub>\<alpha> (tys ! i) (ts ! i)\<rbrakk> \<Longrightarrow> thesis"
      have "(\<exists>v t. \<beta> = t \<and> Fun f ts \<cdot> \<sigma> = Var v \<and> sigV v = Some t) \<or> (\<exists>fa tsa tsb t. \<beta> = t \<and> Fun f ts \<cdot> \<sigma> = Fun fa tsa \<and> sigF (fa, length tsa) = Some (tsb, t) \<and> (\<forall>n. \<not> n < length tsa \<or> \<T>\<^sub>\<alpha> (tsb ! n) (tsa ! n)))"
        by (meson Fun.prems \<open>\<And>P. \<lbrakk>\<T>\<^sub>\<alpha> \<beta> (Fun f ts \<cdot> \<sigma>); \<And>x \<alpha>. \<lbrakk>\<beta> = \<alpha>; Fun f ts \<cdot> \<sigma> = Var x; sigV x = Some \<alpha>\<rbrakk> \<Longrightarrow> P; \<And>fa tsa tys \<alpha>. \<lbrakk>\<beta> = \<alpha>; Fun f ts \<cdot> \<sigma> = Fun fa tsa; sigF (fa, length tsa) = Some (tys, \<alpha>); \<forall>i<length tsa. \<T>\<^sub>\<alpha> (tys ! i) (tsa ! i)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>)
      then show ?thesis
        using a1 Fun by auto
    qed
  then show ?case using Fun \<T>\<^sub>\<alpha>.cases by blast
qed

lemma \<T>\<^sub>\<alpha>_subt_at:
  assumes "\<T>\<^sub>\<alpha> \<alpha> C\<langle>t\<rangle>"
  shows "\<exists>\<beta>. \<T>\<^sub>\<alpha> \<beta> t"
using assms
proof (induction C arbitrary: \<alpha>)
  case (More f ss1 C' ss2)
  let ?ts = "ss1 @ C'\<langle>t\<rangle> # ss2"
  obtain tys where "sigF (f, length ?ts) = Some (tys, \<alpha>)" using More(2) by (auto elim: \<T>\<^sub>\<alpha>.cases)
  with More(2) have "\<forall>i<length ?ts. \<T>\<^sub>\<alpha> (tys ! i) (?ts ! i)"
    by (auto elim: \<T>\<^sub>\<alpha>.cases)
  then have "\<T>\<^sub>\<alpha> (tys ! length ss1) (?ts ! length ss1)"
    by (metis add_Suc_right length_Cons length_append less_add_Suc1)
  then show ?case using More(1) unfolding nth_append_length[of ss1 "C'\<langle>t\<rangle>" ss2] by blast
qed auto

lemma \<T>\<^sub>\<alpha>_subst: 
  assumes "\<T>\<^sub>\<alpha> \<alpha> t" "\<And>y \<gamma>. y \<in> vars_term t \<Longrightarrow> (sigV y = Some \<gamma> \<longrightarrow> \<T>\<^sub>\<alpha> \<gamma> (Var y \<cdot> \<sigma>))"
  shows "\<T>\<^sub>\<alpha> \<alpha> (t \<cdot> \<sigma>)"
using assms
proof (induction t)
  case (funs f ts tys \<alpha>)
  { fix i
    assume "i < length ts"
    then have "\<T>\<^sub>\<alpha> (tys ! i) (ts ! i \<cdot> \<sigma>)" using funs by fastforce
  }
  then show ?case using funs(1) by auto
qed simp

lemma \<LL>\<^sub>\<alpha>_subst: 
  assumes "\<T>\<^sub>\<alpha> \<alpha> t"
          "\<And>y \<gamma>. y \<in> vars_term t \<Longrightarrow> (sigV y = Some \<gamma> \<longrightarrow> \<LL>\<^sub>\<alpha> \<gamma> (mctxt_of_term (Var y \<cdot> \<sigma>)))"
  shows "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term (t \<cdot> \<sigma>))"
using assms
proof (induction t rule: \<T>\<^sub>\<alpha>.induct)
  case (funs f ts tys \<alpha>)
  { fix i
    assume "i < length ts"
    then have "\<LL>\<^sub>\<alpha> (tys ! i) (mctxt_of_term (ts ! i \<cdot> \<sigma>))" using funs by fastforce
  }
  then show ?case using funs(1) by auto
qed simp

lemma conserv_\<T>\<^sub>\<alpha>:
  assumes "\<T>\<^sub>\<alpha> \<alpha> s"
  shows "(s, t) \<in> rstep \<R> \<Longrightarrow> \<T>\<^sub>\<alpha> \<alpha> t"
proof -
  assume "(s, t) \<in> rstep \<R>"
  from this and assms show "\<T>\<^sub>\<alpha> \<alpha> t"
  proof (induction rule: rstep_induct_rule)
    case (IH C \<sigma> l r)
    then obtain \<beta> where type_l\<sigma>: "\<T>\<^sub>\<alpha> \<beta> (l \<cdot> \<sigma>)" using \<T>\<^sub>\<alpha>_subt_at by blast
    obtain \<beta>' where rule_type: "\<T>\<^sub>\<alpha> \<beta>' l" "\<T>\<^sub>\<alpha> \<beta>' r"
      using R_def[OF IH(1)] by auto
    have "is_Fun l" using IH wf unfolding wf_trs_def by blast
    then have "\<beta>' = \<beta>" using rule_type(1) type_l\<sigma> by (cases l) (auto elim!: \<T>\<^sub>\<alpha>.cases)
    have \<sigma>_types: "\<And>y \<gamma>. y \<in> vars_term l \<Longrightarrow> (sigV y = Some \<gamma> \<longrightarrow> \<T>\<^sub>\<alpha> \<gamma> (Var y \<cdot> \<sigma>))"
      using type_l\<sigma> rule_type(1) unfolding \<open>\<beta>' = \<beta>\<close>
      proof (induction l arbitrary: \<beta>)
        case (Fun f ts)
        obtain tys where type_f: "sigF (f, length ts) = Some (tys, \<beta>)"
          using Fun(3) by (auto elim: \<T>\<^sub>\<alpha>.cases)
        { fix t\<^sub>i
          assume asms: "t\<^sub>i \<in> set ts" "y \<in> vars_term t\<^sub>i"
          then obtain i where t\<^sub>i_def: "t\<^sub>i = ts ! i" "i < length ts" by (meson in_set_idx)
          then have "\<T>\<^sub>\<alpha> (tys ! i) t\<^sub>i" "\<T>\<^sub>\<alpha> (tys ! i) (t\<^sub>i \<cdot> \<sigma>)" using type_f Fun(3-) by (auto elim!: \<T>\<^sub>\<alpha>.cases)
          then have "(sigV y = Some \<gamma>) \<longrightarrow> \<T>\<^sub>\<alpha> \<gamma> (Var y \<cdot> \<sigma>)" using Fun(1)[OF asms, of "tys ! i" \<gamma>] by fast
        }
        then show ?case using Fun(2) by auto
      qed (auto elim!: \<T>\<^sub>\<alpha>.cases)
    have sub_vars: "vars_term r \<subseteq> vars_term l" using IH wf by (simp add: wf_trs_def)
    from IH(2) show ?case
    proof (induction C arbitrary: \<alpha>)
      case Hole
      then have "\<beta> = \<alpha>" using type_l\<sigma> by (auto elim!: \<T>\<^sub>\<alpha>.cases)
      then have "\<T>\<^sub>\<alpha> \<alpha> r" using rule_type \<open>\<beta>' = \<beta>\<close> by blast
      from \<T>\<^sub>\<alpha>_subst[OF this] show ?case using sub_vars \<sigma>_types by auto
    next
      case (More f ss1 C' ss2)
      let ?ts = "ss1 @ C'\<langle>l \<cdot> \<sigma>\<rangle> # ss2" and ?ts' = "ss1 @ C'\<langle>r \<cdot> \<sigma>\<rangle> # ss2"
      obtain tys where type_f: "sigF (f, length ?ts) = Some (tys, \<alpha>)"
        using More(2) by (auto elim: \<T>\<^sub>\<alpha>.cases)
      with More(2) have sub_typed: "\<forall>i<length ?ts. \<T>\<^sub>\<alpha> (tys ! i) (?ts ! i)"
        by (auto elim: \<T>\<^sub>\<alpha>.cases)
      then have "\<T>\<^sub>\<alpha> (tys ! length ss1) (?ts ! length ss1)"
        by (metis add_Suc_right length_Cons length_append less_add_Suc1)
      then have "\<T>\<^sub>\<alpha> (tys ! length ss1) (?ts' ! length ss1)"
        using More(1) by simp
      then have "\<forall>i<length ?ts'. \<T>\<^sub>\<alpha> (tys ! i) (?ts' ! i)"
        using arity sub_typed unfolding intp_actxt.simps
        by (metis append_Cons_nth_not_middle length_Cons length_append)
      then show ?case using type_f by auto
    qed
  qed
qed

lemma conserv_\<LL>\<^sub>\<alpha>:
  assumes "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term s)"
  shows "(s, t) \<in> rstep \<R> \<Longrightarrow> \<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term t)"
proof -
  assume "(s, t) \<in> rstep \<R>"
  from this and assms show "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term t)"
  proof (induction rule: rstep_induct_rule)
    case (IH C \<sigma> l r)
    then obtain \<beta> where type_l\<sigma>: "\<LL>\<^sub>\<alpha> \<beta> (mctxt_of_term (l \<cdot> \<sigma>))"
      using \<LL>_sub \<LL>_def by blast
    obtain \<beta>' where rule_type: "\<T>\<^sub>\<alpha> \<beta>' l" "\<T>\<^sub>\<alpha> \<beta>' r"
      using R_def[OF IH(1)] by auto
    have "is_Fun l" using IH wf unfolding wf_trs_def by blast
    then have "\<beta>' = \<beta>" using rule_type(1) type_l\<sigma> by (cases l) (auto elim!: \<T>\<^sub>\<alpha>.cases \<LL>\<^sub>\<alpha>.cases)
    have \<sigma>_types: "\<And>y \<gamma>. y \<in> vars_term l \<Longrightarrow>
                          (sigV y = Some \<gamma> \<longrightarrow> \<LL>\<^sub>\<alpha> \<gamma> (mctxt_of_term (Var y \<cdot> \<sigma>)))"
      using rule_type(1) type_l\<sigma> unfolding \<open>\<beta>' = \<beta>\<close>
      proof (induction \<beta> l rule: \<T>\<^sub>\<alpha>.induct)
        case (funs f ts tys \<alpha>)
        { fix t\<^sub>i
          assume asms: "t\<^sub>i \<in> set ts" "y \<in> vars_term t\<^sub>i"
          then obtain i where t\<^sub>i_def: "t\<^sub>i = ts ! i" "i < length ts" by (meson in_set_idx)
          then have "\<LL>\<^sub>\<alpha> (tys ! i) (mctxt_of_term t\<^sub>i)" using funs(2) \<T>\<^sub>\<alpha>_\<LL>\<^sub>\<alpha> by simp
          moreover have "\<LL>\<^sub>\<alpha> (tys ! i) (mctxt_of_term (t\<^sub>i \<cdot> \<sigma>))"
            using funs(1,4) t\<^sub>i_def by (auto elim: \<LL>\<^sub>\<alpha>.cases)
          ultimately have "(sigV y = Some \<gamma>) \<longrightarrow> \<LL>\<^sub>\<alpha> \<gamma> (mctxt_of_term (Var y \<cdot> \<sigma>))"
            using funs(2) asms t\<^sub>i_def by blast
        }
        then show ?case using funs(3) by auto
      qed auto
    have sub_vars: "vars_term r \<subseteq> vars_term l" using IH wf by (simp add: wf_trs_def)
    from IH(2) show ?case
    proof (induction C arbitrary: \<alpha>)
      case Hole
      then have "\<beta> = \<alpha>" using type_l\<sigma> \<open>is_Fun l\<close> by (auto elim!: \<LL>\<^sub>\<alpha>.cases)
      then have "\<T>\<^sub>\<alpha> \<alpha> r" using rule_type \<open>\<beta>' = \<beta>\<close> by blast
      from \<LL>\<^sub>\<alpha>_subst[OF this] show ?case using sub_vars \<sigma>_types by auto
    next
      case (More f ss1 C' ss2)
      let ?ts = "ss1 @ C'\<langle>l \<cdot> \<sigma>\<rangle> # ss2" and ?ts' = "ss1 @ C'\<langle>r \<cdot> \<sigma>\<rangle> # ss2"
      obtain tys where type_f: "sigF (f, length ?ts) = Some (tys, \<alpha>)"
        using More(2) by (auto elim: \<LL>\<^sub>\<alpha>.cases)
      with More(2) have sub_typed: "\<forall>i<length ?ts. \<LL>\<^sub>\<alpha> (tys ! i) (mctxt_of_term (?ts ! i))"
        by (auto elim!: \<LL>\<^sub>\<alpha>.cases)
           (metis (no_types, lifting) arity list.simps(9) map_append nth_map type_f)
      then have "\<LL>\<^sub>\<alpha> (tys ! length ss1) (mctxt_of_term (?ts ! length ss1))"
        by (metis add_Suc_right length_Cons length_append less_add_Suc1)
      then have "\<LL>\<^sub>\<alpha> (tys ! length ss1) (mctxt_of_term (?ts' ! length ss1))"
        using More(1) by simp
      then have "\<forall>i<length ?ts'. \<LL>\<^sub>\<alpha> (tys ! i) (mctxt_of_term (?ts' ! i))"
        using arity sub_typed unfolding intp_actxt.simps
        by (metis append_Cons_nth_not_middle length_Cons length_append)
      then show ?case using type_f arity nth_map[of _ "ss1 @ C'\<langle>r \<cdot> \<sigma>\<rangle> # ss2" mctxt_of_term]
        by (auto simp: map_nth_eq_conv)
    qed
  qed
qed

lemma conserv_star_\<T>\<^sub>\<alpha>:
  assumes "(s, t) \<in> (rstep \<R>)\<^sup>*" and "\<T>\<^sub>\<alpha> \<alpha> s"
  shows "\<T>\<^sub>\<alpha> \<alpha> t"
using assms conserv_\<T>\<^sub>\<alpha>
by (induction rule: converse_rtrancl_induct) auto

lemma conserv_star_\<LL>\<^sub>\<alpha>:
  assumes "(s, t) \<in> (rstep \<R>)\<^sup>*" and "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term s)"
  shows "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term t)"
using assms conserv_\<LL>\<^sub>\<alpha>
by (induction rule: converse_rtrancl_induct) auto

lemma needed_types_subt_at:
  assumes "\<T>\<^sub>\<alpha> \<alpha> C\<langle>t\<rangle>" "\<T>\<^sub>\<alpha> \<beta> t"
  shows "needed_types \<alpha> \<beta>"
using assms
proof (induction C arbitrary: \<alpha>)
  case Hole
  then have "\<beta> = \<alpha>" by (auto elim!: \<T>\<^sub>\<alpha>.cases)
  then show ?case by blast
next
  case (More f ss1 C' ss2)
  let ?ts = "ss1 @ C'\<langle>t\<rangle> # ss2"
  obtain tys where props: "sigF (f, length ?ts) = Some (tys, \<alpha>)" "\<forall>i<length ?ts. \<T>\<^sub>\<alpha> (tys ! i) (?ts ! i)"
    using More(2) by (auto elim: \<T>\<^sub>\<alpha>.cases)
  then have "needed_types \<alpha> (tys ! length ss1)" using arity by auto
  moreover have "\<T>\<^sub>\<alpha> (tys ! length ss1) C'\<langle>t\<rangle>" using props
    by (metis add_Suc_right length_Cons nth_append_length length_append less_add_Suc1)
  ultimately show ?case using More(1,3) by blast
qed

lemma needed_rules_\<T>\<^sub>\<alpha>:
  assumes "\<T>\<^sub>\<alpha> \<alpha> s" "(s, t) \<in> rstep (\<R>\<^sub>\<alpha> \<beta>)"
  shows "needed_types \<alpha> \<beta>"
using assms
proof (induction s arbitrary: t)
  case (var x \<alpha>)
  then show ?case using NF_Var[OF wf] by blast
next
  case (funs f ts tys \<alpha>)
  then obtain l r p \<sigma> where step: "(Fun f ts, t) \<in> rstep_r_p_s (\<R>\<^sub>\<alpha> \<beta>) (l, r) p \<sigma>"
    using rstep_iff_rstep_r_p_s[of "Fun f ts" t "\<R>\<^sub>\<alpha> \<beta>"] by blast
  obtain C where props: "Fun f ts = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "p = hole_pos C" "(l, r) \<in> \<R>\<^sub>\<alpha> \<beta>"
    using hole_pos_ctxt_of_pos_term Product_Type.Collect_case_prodD[OF step[unfolded rstep_r_p_s_def]]
    unfolding fst_conv snd_conv by metis
  then obtain g ss where l_def: "l = Fun g ss" using wf unfolding wf_trs_def by blast
  then obtain tys' where type_\<beta>: "sigF (g, length ss) = Some (tys', \<beta>)"
    using props(4) by (auto elim: \<T>\<^sub>\<alpha>.cases)
  obtain \<beta>' where "\<T>\<^sub>\<alpha> \<beta>' (l \<cdot> \<sigma>)" using \<T>\<^sub>\<alpha>_subt_at[of \<alpha> C "l \<cdot> \<sigma>"] props(1) funs(1,2) by auto
  then have "\<beta>' = \<beta>" using type_\<beta> l_def by (auto elim: \<T>\<^sub>\<alpha>.cases)
  then show ?case using \<open>\<T>\<^sub>\<alpha> \<beta>' (l \<cdot> \<sigma>)\<close> needed_types_subt_at[of \<alpha> C "l \<cdot> \<sigma>"]
    funs(1,2) props(1) by auto
qed

abbreviation \<R>\<^sub>n\<^sub>\<alpha> where "\<R>\<^sub>n\<^sub>\<alpha> \<equiv> \<lambda>\<alpha>. \<Union>{ \<R>\<^sub>\<alpha> \<beta> |\<beta>. needed_types \<alpha> \<beta>}"

lemma needed_rules_\<T>\<^sub>\<alpha>_single:
  assumes "(s, t) \<in> rstep \<R>" "\<T>\<^sub>\<alpha> \<alpha> s"
  shows "(s, t) \<in> rstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>)"
proof -
  obtain l r p \<sigma> where st_step: "(s, t) \<in> rstep_r_p_s \<R> (l, r) p \<sigma>"
    using rstep_iff_rstep_r_p_s[of s t \<R>] assms(1) by blast
  then obtain \<beta> where "\<T>\<^sub>\<alpha> \<beta> l" "\<T>\<^sub>\<alpha> \<beta> r" "(l, r) \<in> \<R>"
    using R_def Product_Type.Collect_case_prodD[OF st_step[unfolded rstep_r_p_s_def]] by meson
  then have "(s, t) \<in> rstep (\<R>\<^sub>\<alpha> \<beta>)"
    using st_step rstep_r_p_s_imp_rstep[of s t "(\<R>\<^sub>\<alpha> \<beta>)" "(l, r)" p \<sigma>]
    by (simp add: rstep_r_p_s_def)
  then show ?thesis
    using needed_rules_\<T>\<^sub>\<alpha>[OF assms(2), of t \<beta>] by blast
qed

lemma rstep_on_\<T>\<^sub>\<alpha>_iff_needed:
  "Restr (rstep \<R>) {t. \<T>\<^sub>\<alpha> \<alpha> t} = Restr (rstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>)) {t. \<T>\<^sub>\<alpha> \<alpha> t}"
  using needed_rules_\<T>\<^sub>\<alpha>_single by auto

lemma CR_on_\<T>\<^sub>\<alpha>_by_needed_rules:
  "CR_on (rstep \<R>) {t. \<T>\<^sub>\<alpha> \<alpha> t} \<longleftrightarrow> CR_on (rstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>)) {t. \<T>\<^sub>\<alpha> \<alpha> t}"
  by (subst (1 2) CR_on_iff_CR_Restr) (auto 0 3 intro: conserv_\<T>\<^sub>\<alpha> simp: rstep_on_\<T>\<^sub>\<alpha>_iff_needed)

lemma \<T>\<^sub>\<alpha>_\<T>: "{ t. \<T>\<^sub>\<alpha> \<alpha> t } \<subseteq> \<T>"
using funas_\<T>\<^sub>\<alpha> unfolding \<T>_def by blast                          

text \<open>The following lemma establishes the easy direction of persistence of confluence.\<close>
lemma CR_persist':
  assumes CR_union: "CR_on (rstep \<R>) \<T>"
  shows "CR_on (rstep \<R>) { t. \<T>\<^sub>\<alpha> \<alpha> t }"
using \<T>\<^sub>\<alpha>_\<T> assms unfolding CR_on_def by blast

end

locale persistent_cr_infinite_vars = persistent_cr sigF sigV \<R> for 
        sigF :: "('f \<times> nat) \<Rightarrow> ('t list \<times> 't) option" and
        sigV :: "'v :: infinite \<Rightarrow> 't option" and
        \<R> :: "('f, 'v :: infinite) trs" +
  assumes inf_vars: "\<And>\<alpha>. infinite { v \<in> \<V>. sigV v = Some \<alpha> }"
begin

fun add_types :: "('f, 'v) term \<Rightarrow> 't \<Rightarrow> ('f, 'v * 't) term" where
  "add_types (Var x) \<alpha> = Var (x, \<alpha>)"
| "add_types (Fun f ts) \<alpha> = (case sigF (f, length ts) of
     Some (tys, \<alpha>) \<Rightarrow> Fun f (map (\<lambda>(t,\<alpha>). add_types t \<alpha>) (zip ts tys))
   | None \<Rightarrow> Fun f (map (\<lambda>t. add_types t undefined) ts))"

lemma drop_take_nth: "n < length ls \<Longrightarrow> drop n (take (Suc n) ls) = [ls ! n]"
by (induction ls arbitrary: n) (simp, metis List.append_eq_append_conv
    Suc_eq_plus1 Suc_eq_plus1_left take_Suc_conv_app_nth take_add take_drop) 

lemma \<T>\<^sub>\<alpha>_add_types_subst:
  assumes "\<T>\<^sub>\<alpha> \<alpha> t"
  shows "add_types (t \<cdot> \<sigma>) \<alpha> = t \<cdot> (\<lambda>x. add_types (\<sigma> x) (the (sigV x)))"
using assms
proof (induction rule: \<T>\<^sub>\<alpha>.induct)
  case (funs f ts tys \<alpha>)
  then show ?case using arity[OF funs(1)]
    by (simp add: map_nth_eq_conv)
qed simp

lemma add_types_preserves_step:
  assumes "(s, t) \<in> rstep \<R>" "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term s)"
  shows "(add_types s \<alpha>, add_types t \<alpha>) \<in> rstep' \<R>"
using assms
proof (induction arbitrary: \<alpha>)
  case (IH C \<sigma> l r)
  obtain \<beta> where rule_type: "\<T>\<^sub>\<alpha> \<beta> l" "\<T>\<^sub>\<alpha> \<beta> r" using R_def[OF IH(1)] by blast
  then have "add_types (l \<cdot> \<sigma>) \<beta> = l \<cdot> (\<lambda>x. add_types (\<sigma> x) (the (sigV x)))"
        "add_types (r \<cdot> \<sigma>) \<beta> = r \<cdot> (\<lambda>x. add_types (\<sigma> x) (the (sigV x)))"
    using \<T>\<^sub>\<alpha>_add_types_subst by blast+
  then have step': "(add_types (l \<cdot> \<sigma>) \<beta>, add_types (r \<cdot> \<sigma>) \<beta>) \<in> rstep' \<R>"
    using rstep'[OF IH(1), of \<box>] by auto
  obtain f ts where l_def: "l = Fun f ts"
    using wf IH(1) unfolding wf_trs_def by blast
  then obtain tys where type_l: "sigF (f, length ts) = Some (tys, \<beta>)"
    using rule_type by (auto elim: \<T>\<^sub>\<alpha>.cases)
  show ?case using IH(2)
  proof (induction C arbitrary: \<alpha>)
    case Hole
    then have "\<alpha> = \<beta>" using type_l unfolding l_def by (auto elim: \<LL>\<^sub>\<alpha>.cases)
    then show ?case using step' by auto
  next
    case (More f ss1 C' ss2)
    then obtain tys where tys: "sigF (f, Suc (length ss1 + length ss2)) = Some (tys, \<alpha>)"
      by (auto elim!: \<LL>\<^sub>\<alpha>.cases)
    then have in_\<LL>\<^sub>\<alpha>: "\<LL>\<^sub>\<alpha> (tys ! length ss1) (mctxt_of_term C'\<langle>l \<cdot> \<sigma>\<rangle>)"
      using More(2) arity[OF tys] by (auto elim!: \<LL>\<^sub>\<alpha>.cases)
      (metis (no_types) length_map less_add_Suc1 nth_append_length)
    let ?C = "More f (map (\<lambda>(t,\<alpha>). add_types t \<alpha>) (zip ss1 (take (length ss1) tys))) \<box>
                     (map (\<lambda>(t,\<alpha>). add_types t \<alpha>) (zip ss2 (drop (Suc (length ss1)) tys)))"
    show ?case using tys rstep'_mono[OF More(1)[OF in_\<LL>\<^sub>\<alpha>], of ?C] arity[OF tys]
      by (simp add: zip_append1 zip_append1[of "[C'\<langle>_\<rangle>]" _ "drop (length ss1) tys",
          unfolded drop_drop[of _ "length ss1"], simplified]
          take_drop drop_take_nth[of "length ss1" tys])
  qed 
qed

lemma add_types_preserves_steps:
  assumes "(s, t) \<in> (rstep \<R>)\<^sup>*" "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term s)"
  shows "(add_types s \<alpha>, add_types t \<alpha>) \<in> (rstep' \<R>)\<^sup>*"
using assms
proof (induction rule: converse_rtrancl_induct)
  case (step y z)
  then have "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term z)" using conserv_star_\<LL>\<^sub>\<alpha> by blast
  moreover have "(add_types y \<alpha>, add_types z \<alpha>) \<in> rstep' \<R>"
    using add_types_preserves_step[OF step(1,4)] .
  ultimately show ?case using step(3) by simp
qed auto

lemma \<LL>\<^sub>\<alpha>_add_types_\<T>\<^sub>\<alpha>:
  assumes "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term s)"
  shows "\<exists>\<sigma> \<tau>. \<T>\<^sub>\<alpha> \<alpha> (add_types s \<alpha> \<cdot> \<sigma>) \<and> (add_types s \<alpha> \<cdot> \<sigma>) \<cdot> \<tau> = add_types s \<alpha>"
proof -
  let ?typed_vts = "\<lambda>s \<alpha> \<beta>. { (x, \<beta>) |x. (x, \<beta>) \<in> vars_term (add_types s \<alpha>) }"
  (* ?f maps a type \<alpha> to the set of variables (_, \<alpha>) in term t *)
  (* ?g maps a type to all variables of that type (wrt. sigV) *)
  let ?f = "?typed_vts s \<alpha>"
  let ?g = "\<lambda>\<beta>. { x \<in> \<V> . sigV x = Some \<beta> }"
  have fin: "finite (?f \<beta>)" for \<beta>
    by (auto intro: rev_finite_subset[OF finite_vars_term[of "add_types s \<alpha>"]])
  have inf: "infinite (?g \<beta>)" for \<beta> using inf_vars .
  have disj_f: "\<And>\<alpha>' \<beta>. ?f \<alpha>' \<inter> ?f \<beta> \<noteq> {} \<Longrightarrow> \<alpha>' = \<beta>" by auto
  have disj_g: "\<And>\<alpha> \<beta>. ?g \<alpha> \<inter> ?g \<beta> \<noteq> {} \<Longrightarrow> \<alpha> = \<beta>" by auto
  obtain h where h_inj: "inj_on h (\<Union>\<alpha>. ?f \<alpha>)" "(\<forall>\<alpha>. h ` ?f \<alpha> \<subseteq> ?g \<alpha>)"
    using finites_into_infinites[of ?f ?g, OF disj_f fin disj_g inf] by blast
  let ?\<sigma> = "Var \<circ> h" and ?\<tau> = "Var \<circ> (inv_into (\<Union>\<alpha>. ?f \<alpha>) h)"
  have "add_types s \<alpha> = add_types s \<alpha> \<cdot> Var" by simp
  have "(add_types s \<alpha> \<cdot> ?\<sigma>) \<cdot> ?\<tau> = add_types s \<alpha> \<cdot> Var" using h_inj(1)
    unfolding subst_subst_compose[symmetric] term_subst_eq_conv
    by (auto simp: subst_compose_def)
  moreover have "\<T>\<^sub>\<alpha> \<alpha> (add_types s \<alpha> \<cdot> ?\<sigma>)"
  using assms h_inj(2)
  proof (induction "mctxt_of_term s" arbitrary: s rule: \<LL>\<^sub>\<alpha>.induct)
    case (mhole \<alpha>)
    then show ?case by (cases s) auto
  next
    case (mvar \<beta> x)
    then have s_def: "s = Var x" by (cases s) auto
    then have "(x, \<alpha>) \<in> vars_term (add_types s \<alpha>)" by simp
    then show ?case using mvar(2) unfolding s_def by auto
  next
    case (mfun f Cs tys \<beta>)
    then obtain ts where s_def: "s = Fun f ts" "Cs = map mctxt_of_term ts" by (cases s) auto
    let ?ts = "map ((\<lambda>t. t \<cdot> (Var \<circ> h)) \<circ> (\<lambda>(x, y). add_types x y)) (zip ts tys)"
    have lengths: "length ?ts = length ts" using arity[OF mfun(1)] unfolding s_def by simp
    { fix i
      assume "i < length Cs"
      then have "map mctxt_of_term ts ! i = mctxt_of_term (ts ! i)" unfolding s_def by auto
      have subs: "?typed_vts (ts ! i) (tys ! i) \<gamma> \<subseteq> ?typed_vts (Fun f ts) \<beta> \<gamma>" for \<gamma>
        using mfun(1) \<open>i < length Cs\<close> arity[OF mfun(1)] nth_mem[of i "zip ts tys"]
        unfolding s_def by (auto split: if_splits prod.splits)
      have "\<forall>\<alpha>. h ` ?typed_vts (ts ! i) (tys ! i) \<alpha> \<subseteq> {x \<in> \<V>. sigV x = Some \<alpha>}"
        using mfun(4) image_mono[OF subs, of h] unfolding s_def by (meson subset_trans)
      then have "\<T>\<^sub>\<alpha> (tys ! i) (add_types (ts ! i) (tys ! i) \<cdot> ?\<sigma>)"
        using mfun \<open>i < length Cs\<close> unfolding s_def by fastforce
    }
    then show ?case using mfun(1) arity[OF mfun(1)] unfolding s_def
      by (auto simp: nth_mem[of _ "zip ts tys"] split: if_splits prod.splits)
  qed
  ultimately show ?thesis by auto
qed

lemma CR_on_union:
  assumes CR_\<alpha>: "\<forall>\<alpha>. CR_on (rstep \<R>) { t. \<T>\<^sub>\<alpha> \<alpha> t }"
  shows "CR_on (rstep \<R>) { t. mctxt_of_term t \<in> \<LL> }"
proof
  fix a b c
  assume a_in_L: "a \<in> { t. mctxt_of_term t \<in> \<LL> }"  and
         a_to_b: "(a, b) \<in> (rstep \<R>)\<^sup>*" and
         a_to_c: "(a, c) \<in> (rstep \<R>)\<^sup>*"
  obtain \<alpha> where a_in_\<LL>\<^sub>\<alpha>: "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term a)" using a_in_L \<LL>_def by blast
  then have b_in_\<LL>\<^sub>\<alpha>: "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term b)" and
        c_in_\<LL>\<^sub>\<alpha>: "\<LL>\<^sub>\<alpha> \<alpha> (mctxt_of_term c)" using conserv_star_\<LL>\<^sub>\<alpha> a_to_b a_to_c by blast+
  have a_to_b': "(add_types a \<alpha>, add_types b \<alpha>) \<in> (rstep' \<R>)\<^sup>*" and
       a_to_c': "(add_types a \<alpha>, add_types c \<alpha>) \<in> (rstep' \<R>)\<^sup>*"
    using a_in_\<LL>\<^sub>\<alpha> add_types_preserves_steps a_to_b a_to_c by blast+
  obtain \<sigma> \<tau> where in_\<T>\<^sub>\<alpha>: "\<T>\<^sub>\<alpha> \<alpha> (add_types a \<alpha> \<cdot> \<sigma>)" and
                   inv_\<tau>: "add_types a \<alpha> \<cdot> \<sigma> \<cdot> \<tau> = add_types a \<alpha>"
    using \<LL>\<^sub>\<alpha>_add_types_\<T>\<^sub>\<alpha>[OF a_in_\<LL>\<^sub>\<alpha>] by blast
  have a_to_b'': "(add_types a \<alpha> \<cdot> \<sigma>, add_types b \<alpha> \<cdot> \<sigma>) \<in> (rstep \<R>)\<^sup>*"
    using a_to_b'
    proof (induction rule: converse_rtrancl_induct)
      case (step y z)
      have "(y \<cdot> \<sigma>, z \<cdot> \<sigma>) \<in> (rstep \<R>)" using rstep'_stable[OF step(1)] rstep_eq_rstep' by auto
      then show ?case using step(3) by auto
    qed auto
  moreover have a_to_b'': "(add_types a \<alpha> \<cdot> \<sigma>, add_types c \<alpha> \<cdot> \<sigma>) \<in> (rstep \<R>)\<^sup>*"
    using a_to_c'
    proof (induction rule: converse_rtrancl_induct)
      case (step y z)
      have "(y \<cdot> \<sigma>, z \<cdot> \<sigma>) \<in> (rstep \<R>)" using rstep'_stable[OF step(1)] rstep_eq_rstep' by auto
      then show ?case using step(3) by auto
    qed auto
  ultimately have "(add_types b \<alpha> \<cdot> \<sigma>, add_types c \<alpha> \<cdot> \<sigma>) \<in> (rstep \<R>)\<^sup>\<down>"
    using CR_\<alpha> in_\<T>\<^sub>\<alpha> unfolding CR_on_def by auto
  then obtain d where join1: "(add_types b \<alpha> \<cdot> \<sigma>, d) \<in> (rstep \<R>)\<^sup>*" and
                      join2: "(add_types c \<alpha> \<cdot> \<sigma>, d) \<in> (rstep \<R>)\<^sup>*"
    using joinD by fastforce
  from join1 have join1': "(add_types b \<alpha> \<cdot> \<sigma> \<cdot> \<tau>, d \<cdot> \<tau>) \<in> (rstep' \<R>)\<^sup>*"
  proof (induction rule: converse_rtrancl_induct)
    case (step y z)
    then show ?case using rstep'_stable[of y z \<R> \<tau>] by fastforce
  qed auto
  from join2 have join2': "(add_types c \<alpha> \<cdot> \<sigma> \<cdot> \<tau>, d \<cdot> \<tau>) \<in> (rstep' \<R>)\<^sup>*"
  proof (induction rule: converse_rtrancl_induct)
    case (step y z)
    then show ?case using rstep'_stable[of y z \<R> \<tau>] by fastforce
  qed auto
  have remove_types: "add_types t \<alpha> \<cdot> (\<lambda>(x, \<alpha>). Var x) = t" for \<alpha> t
  proof (induction t \<alpha> rule: add_types.induct)
    case (2 f ts \<alpha>) then show ?case
    proof (cases "sigF (f, length ts)")
      case None
      then show ?thesis using 2(1)[OF None] by (simp add: map_idI)
    next
      case (Some a)
      then obtain \<beta> tys where types: "sigF (f, length ts) = Some (tys, \<beta>)" by force
      have l_zip: "length (zip ts tys) = length ts"
        using length_zip[of ts tys] arity[OF types] by auto
      { fix i
        assume "i < length ts"
        then have "(\<lambda>(t, \<alpha>). add_types t \<alpha> \<cdot> (\<lambda>(x, \<alpha>). Var x)) ((zip ts tys) ! i) = ts ! i"
          using 2(2)[OF types, of tys \<beta> "zip ts tys ! i" "ts ! i" "tys ! i"]
          by (auto split: prod.splits)
             (metis fst_conv snd_conv nth_mem nth_zip arity[OF types] l_zip)
      }
      then show ?thesis using types arity[OF types] zip_nth_conv
        by (simp add: map_nth_eq_conv)
    qed
  qed auto
  from join1' have join1'':
      "(add_types b \<alpha> \<cdot> \<sigma> \<cdot> \<tau> \<cdot> (\<lambda>(x, \<alpha>). Var x), d \<cdot> \<tau> \<cdot> (\<lambda>(x, \<alpha>). Var x)) \<in> (rstep \<R>)\<^sup>*"
  proof (induction rule: converse_rtrancl_induct)
    case (step y z)
    have "(y \<cdot> (\<lambda>(x, \<alpha>). Var x), z \<cdot> (\<lambda>(x, \<alpha>). Var x)) \<in> rstep \<R>"
      using rstep'_stable[OF step(1)] by (auto simp: rstep_eq_rstep')
    then show ?case using step(3) by fastforce
  qed auto
  from join2' have join2'':
      "(add_types c \<alpha> \<cdot> \<sigma> \<cdot> \<tau> \<cdot> (\<lambda>(x, \<alpha>). Var x), d \<cdot> \<tau> \<cdot> (\<lambda>(x, \<alpha>). Var x)) \<in> (rstep \<R>)\<^sup>*"
  proof (induction rule: converse_rtrancl_induct)
    case (step y z)
    have "(y \<cdot> (\<lambda>a. case a of (x, \<alpha>) \<Rightarrow> Var x), z \<cdot> (\<lambda>a. case a of (x, \<alpha>) \<Rightarrow> Var x)) \<in> rstep \<R>"
      using rstep'_stable[OF step(1)] by (auto simp: rstep_eq_rstep')
    then show ?case using step(3) by fastforce
  qed auto
  have "\<forall>x\<in>vars_term (add_types a \<alpha>). (\<sigma> \<circ>\<^sub>s \<tau>) x = Var x"
    using inv_\<tau> term_subst_eq_conv[of _ "\<sigma> \<circ>\<^sub>s \<tau>" Var] by simp
  then have "add_types b \<alpha> \<cdot> \<sigma> \<cdot> \<tau> = add_types b \<alpha>" "add_types c \<alpha> \<cdot> \<sigma> \<cdot> \<tau> = add_types c \<alpha>"
    using rstep'_sub_vars[OF _ wf] a_to_b' a_to_c' term_subst_eq_conv[of _ "\<sigma> \<circ>\<^sub>s \<tau>" Var] by auto
  then show "(b, c) \<in> (rstep \<R>)\<^sup>\<down>" using join1'' join2'' remove_types by auto
qed                                        

text \<open>The following lemma is the interesting direction of persistence of confluence {cite \<open>Theorem 5.13\<close> FMZvO15}.\<close>
lemma CR_persist:
  assumes "\<forall>\<alpha>. CR_on (rstep \<R>) { t. \<T>\<^sub>\<alpha> \<alpha> t}"
  shows "CR_on (rstep \<R>) \<T>"
  using assms by (rule CR[OF CR_on_union])

end

subsection \<open>Persistent decomposition\<close>

lemma (in persistent_cr) root_step_\<T>\<^sub>\<alpha>_in_\<R>\<^sub>\<alpha>:
  assumes "\<T>\<^sub>\<alpha> \<alpha> s" "(s, t) \<in> rrstep \<R>"
  shows "(s, t) \<in> rrstep (\<R>\<^sub>\<alpha> \<alpha>)"
proof -
  obtain l r \<sigma> where lr: "(l, r) \<in> \<R>" "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" using assms(2) by (auto elim: rrstepE)
  then obtain \<beta> where \<beta>: "\<T>\<^sub>\<alpha> \<beta> l" "\<T>\<^sub>\<alpha> \<beta> r" using R_def by blast
  have "\<beta> = \<alpha>" using assms(1) \<beta>(1) lr(1) trs unfolding lr(2)
    by (cases l) (auto simp: wf_trs_def elim!: \<T>\<^sub>\<alpha>.cases)
  then show ?thesis using \<beta> lr by auto
qed

context persistent_cr_infinite_vars
begin

interpretation persistent_n\<alpha>: persistent_cr_infinite_vars sigF sigV "\<R>\<^sub>n\<^sub>\<alpha> \<alpha>"
  using trs by (unfold_locales) (auto simp: wf_trs_def R_def inf_vars)

lemma nrrsteps_Fun_imp_arg_rsteps:
  "(Fun f ss, Fun f ts) \<in> (nrrstep R)\<^sup>* \<Longrightarrow> i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep R)\<^sup>*"
  apply (induct "Fun f ts" arbitrary: ts rule: rtrancl_induct)
   apply auto
  by (metis (no_types, opaque_lifting) nrrsteps_imp_arg_rsteps rtrancl.rtrancl_into_rtrancl term.sel(4))

lemma persistent_decomposition:
  assumes "\<And>\<beta>. \<R>\<^sub>n\<^sub>\<alpha> \<beta> = {} \<or> (\<exists>\<alpha> \<in> S. needed_types \<alpha> \<beta>)"
  shows "CR_on (rstep \<R>) \<T> \<longleftrightarrow> (\<forall>\<alpha> \<in> S. CR_on (rstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>)) \<T>)"
proof (intro iffI ballI, goal_cases L R)
  case (L \<alpha>) show ?case
  proof (intro persistent_n\<alpha>.CR_persist allI CR_onI, goal_cases peak)
    case (peak \<beta> s t u) then show ?case unfolding mem_Collect_eq
    proof (induct s arbitrary: \<beta> t u rule: wf_induct[OF SN_imp_wf[OF SN_supt]])
      case (1 s) show ?case
      proof (cases "needed_types \<alpha> \<beta>")
        case True
        then have *: "persistent_n\<alpha>.\<R>\<^sub>n\<^sub>\<alpha> \<alpha> \<beta> = \<R>\<^sub>n\<^sub>\<alpha> \<beta>" by auto
        have "CR_on (rstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>)) {a. \<T>\<^sub>\<alpha> \<beta> a}" using CR_persist'[OF L(1), of \<beta>]
          unfolding CR_on_\<T>\<^sub>\<alpha>_by_needed_rules persistent_n\<alpha>.CR_on_\<T>\<^sub>\<alpha>_by_needed_rules * .
        then show ?thesis using 1(2,3,4) by (simp add: CR_on_def)
      next
        case False
        have *: "persistent_n\<alpha>.\<R>\<^sub>\<alpha> \<alpha> \<beta> = {}" using False
          by auto (metis intp_actxt.simps(1) needed_types.trans needed_types_subt_at)
        have "(s, t) \<in> (rstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>))\<^sup>* \<Longrightarrow> \<T>\<^sub>\<alpha> \<beta> s \<Longrightarrow> (s, t) \<in> (nrrstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>))\<^sup>*" for s t
        proof (induct rule: converse_rtrancl_induct)
          case (step s s')
          have "(s, s') \<in> nrrstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>)" using step(1,4) persistent_n\<alpha>.root_step_\<T>\<^sub>\<alpha>_in_\<R>\<^sub>\<alpha>[of \<beta> s s' \<alpha>]
            unfolding * by (auto simp: rstep_iff_rrstep_or_nrrstep)
          moreover have "\<T>\<^sub>\<alpha> \<beta> s'" using step(1,4) conserv_\<T>\<^sub>\<alpha>[of \<beta> s s'] R_def by blast
          ultimately show ?case using step(2,3) by auto
        qed auto
        note nrpeak = this[OF 1(3,2)] this[OF 1(4,2)]
        show ?thesis using 1(2)
        proof (cases \<beta> s rule: \<T>\<^sub>\<alpha>.cases)
          case (var x)
          from NF_Var[OF persistent_n\<alpha>.wf, of x] show ?thesis using var(1) 1(3,4)
            by (auto elim: converse_rtranclE)
        next
          case (funs f ss tys)
          obtain ts where t: "t = Fun f ts" "length ts = length ss" "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>))\<^sup>*"
            using nrpeak(1) nrrsteps_preserve_root' nrrsteps_Fun_imp_arg_rsteps unfolding funs(1)
            by (metis (no_types, lifting))
          obtain us where u: "u = Fun f us" "length us = length ss" "\<And>i. i < length ss \<Longrightarrow> (ss ! i, us ! i) \<in> (rstep (\<R>\<^sub>n\<^sub>\<alpha> \<alpha>))\<^sup>*"
            using nrpeak(2) nrrsteps_preserve_root' nrrsteps_Fun_imp_arg_rsteps unfolding funs(1)
            by (metis (no_types, lifting))
          show ?thesis using 1(1)[rule_format, OF _ funs(3)[rule_format] t(3) u(3)]
            by (auto intro: args_joinable_imp_joinable simp: funs(1) t(1,2) u(1,2))
        qed
      qed
    qed
  qed
next
  case R note R = this[rule_format] show ?case
  proof (intro CR_persist[unfolded CR_on_\<T>\<^sub>\<alpha>_by_needed_rules] allI, goal_cases)
    case (1 \<beta>)
    consider (e) "\<R>\<^sub>n\<^sub>\<alpha> \<beta> = {}" | (n) \<alpha> where "\<alpha> \<in> S" "needed_types \<alpha> \<beta>"
      using assms(1)[of \<beta>] by blast
    then show ?case
    proof (cases)
      case e show ?thesis unfolding e by (auto simp: CR_on_def)
    next
      case n
      have *: "persistent_n\<alpha>.\<R>\<^sub>n\<^sub>\<alpha> \<alpha> \<beta> = \<R>\<^sub>n\<^sub>\<alpha> \<beta>" using n(2) by auto
      show ?thesis using persistent_n\<alpha>.CR_persist'[OF R[OF n(1)], of \<beta>]
        unfolding persistent_n\<alpha>.CR_on_\<T>\<^sub>\<alpha>_by_needed_rules * .
    qed
  qed
qed

end

end
