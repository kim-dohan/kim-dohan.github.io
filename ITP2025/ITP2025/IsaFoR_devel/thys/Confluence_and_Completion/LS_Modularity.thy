(*
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Modularity of confluence\<close>

theory LS_Modularity
  imports LS_General
begin

text \<open>Here we instantiate the layer framework for modularity of confluence. See {cite \<open>Section 5.1\<close> FMZvO15}.\<close>

fun max_top_modular :: "('f \<times> nat) set \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) mctxt" where
  "max_top_modular \<F> (Var x) = MVar x"
| "max_top_modular \<F> (Fun f ts) = (if (f, length ts) \<in> \<F>
    then MFun f (map (max_top_modular \<F>) ts)
    else MHole)"

locale modular_cr =
  fixes \<F>\<^sub>1 \<F>\<^sub>2 :: "('f \<times> nat) set" and \<R>\<^sub>1 \<R>\<^sub>2 :: "('f, 'v :: infinite) trs"
  assumes
    wf1: "wf_trs \<R>\<^sub>1" and wf2: "wf_trs \<R>\<^sub>2" and
    sig1: "funas_trs \<R>\<^sub>1 \<subseteq> \<F>\<^sub>1" and sig2: "funas_trs \<R>\<^sub>2 \<subseteq> \<F>\<^sub>2" and disjoint: "\<F>\<^sub>1 \<inter> \<F>\<^sub>2 = {}"
begin

definition \<LL>\<^sub>1 :: "('f, 'v) mctxt set" where
  "\<LL>\<^sub>1 \<equiv> { C. funas_mctxt C \<subseteq> \<F>\<^sub>1 }"
  
definition \<LL>\<^sub>2 :: "('f, 'v) mctxt set" where
  "\<LL>\<^sub>2 \<equiv> { C. funas_mctxt C \<subseteq> \<F>\<^sub>2 }"

abbreviation \<T>\<^sub>1 where "\<T>\<^sub>1 \<equiv> { t :: ('f, 'v) term. funas_term t \<subseteq> \<F>\<^sub>1 }"
abbreviation \<T>\<^sub>2 where "\<T>\<^sub>2 \<equiv> { t :: ('f, 'v) term. funas_term t \<subseteq> \<F>\<^sub>2 }"
abbreviation max_top_mod where "max_top_mod t \<equiv> max_top_modular \<F>\<^sub>1 t \<squnion> max_top_modular \<F>\<^sub>2 t"


lemma modular_cr_symmetric: "modular_cr \<F>\<^sub>2 \<F>\<^sub>1 \<R>\<^sub>2 \<R>\<^sub>1"
using disjoint
by (auto simp: modular_cr_def wf1 wf2 sig1 sig2 infinite_UNIV)

lemma wf_union_trs: "wf_trs (\<R>\<^sub>1 \<union> \<R>\<^sub>2)"
using wf1 wf2 by (auto simp: wf_trs_def)

lemma subm_at_sig:
  fixes L :: "('f, 'v) mctxt" and p :: pos and \<F> :: "('f \<times> nat) set"
  assumes "funas_mctxt L \<subseteq> \<F>" and "p \<in> all_poss_mctxt L"
  shows "funas_mctxt (subm_at L p) \<subseteq> \<F>"
proof
  fix f :: 'f and a :: nat 
  assume "(f, a) \<in> funas_mctxt (subm_at L p)"
  then show "(f, a) \<in> \<F>" using assms
  proof (induction "L :: ('f, 'v) mctxt" p rule: subm_at.induct)
    case (1 L) then show ?case by (induction L) auto
  next
    case (2 f' Cs i p)
    consider (i_valid) "i < List.length Cs" | (i_invalid) "i \<ge> List.length Cs" 
      using not_less by auto
    then show ?thesis
    proof cases
      case i_valid
      from \<open>funas_mctxt (MFun f' Cs) \<subseteq> \<F>\<close> have "funas_mctxt (Cs ! i) \<subseteq> \<F>"
        proof -
          have "(\<Union>x\<in>set Cs. funas_mctxt x) \<subseteq> \<F> \<Longrightarrow> i < List.length Cs \<Longrightarrow> 
                funas_mctxt (Cs ! i) \<subseteq> \<F>" using List.nth_mem by auto
          then show ?thesis using \<open>funas_mctxt (MFun f' Cs) \<subseteq> \<F>\<close> i_valid
            by (induction "Cs ! i" rule: funas_mctxt.induct) auto
        qed
      moreover have "p \<in> all_poss_mctxt (Cs ! i)" using 2 by simp
      ultimately show "(f, a) \<in> \<F>" using 2 by simp
    next
      case i_invalid then show ?thesis using 2 by auto
    qed
  next
    case ("3_1" x i p) then show ?case by simp
  next
    case ("3_2" i p) then show ?case by simp
  qed
qed

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

lemma modular_layer_system: "layer_system (\<F>\<^sub>1 \<union> \<F>\<^sub>2) (\<LL>\<^sub>1 \<union> \<LL>\<^sub>2)"
proof
  show "\<LL>\<^sub>1 \<union> \<LL>\<^sub>2 \<subseteq> layer_system_sig.\<C> (\<F>\<^sub>1 \<union> \<F>\<^sub>2)"
    by (auto simp: \<LL>\<^sub>1_def \<LL>\<^sub>2_def layer_system_sig.\<C>_def)
next (* L1 *)
  fix t :: "('f, 'v) term"
  assume funas_t: "funas_term t \<subseteq> \<F>\<^sub>1 \<union> \<F>\<^sub>2"
  then show "\<exists>L\<in>\<LL>\<^sub>1 \<union> \<LL>\<^sub>2. L \<noteq> MHole \<and> L \<le> mctxt_of_term t"
  proof (cases t)
    case (Var x)
    then have cond: "mctxt_of_term t \<noteq> MHole \<and> mctxt_of_term t \<le> mctxt_of_term t" by simp
    have "mctxt_of_term t \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2" using Var \<LL>\<^sub>1_def by simp
    then show ?thesis using cond by blast
  next
    case (Fun f Cs)
    let ?top = "MFun f (replicate (List.length Cs) MHole)"
    have cond: "?top \<noteq> MHole \<and> ?top \<le> mctxt_of_term t"
      using Fun by (auto simp: less_eq_mctxt_def o_def map_replicate_const)
    have "?top \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2" using Fun funas_t \<LL>\<^sub>1_def \<LL>\<^sub>2_def by simp
    then show ?thesis using cond by blast
  qed
next (* L2 *)
  fix C :: "('f, 'v) mctxt" and p :: pos and x :: 'v
  assume p_in_possC: "p \<in> poss_mctxt C"
  have "(mreplace_at C p (MVar x) \<in> \<LL>\<^sub>1) = (mreplace_at C p MHole \<in> \<LL>\<^sub>1)"
    using \<LL>\<^sub>1_def p_in_possC
    by (induction C p "MVar x :: ('f, 'v) mctxt" rule: mreplace_at.induct) auto
  moreover have "(mreplace_at C p (MVar x) \<in> \<LL>\<^sub>2) = (mreplace_at C p MHole \<in> \<LL>\<^sub>2)"
    using \<LL>\<^sub>2_def p_in_possC
    by (induction C p "MVar x :: ('f, 'v) mctxt" rule: mreplace_at.induct) auto
  ultimately show "(mreplace_at C p (MVar x) \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2) = (mreplace_at C p MHole \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2)" by auto
next (* L3 *)
  fix L N :: "('f, 'v) mctxt" and p :: pos
  assume L_in_\<LL>: "L \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2" and
         N_in_\<LL>: "N \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2" and 
         "p \<in> fun_poss_mctxt L" and 
         comp_context:"(subm_at L p, N) \<in> comp_mctxt"
  consider "L \<in> \<LL>\<^sub>1" | "L \<in> \<LL>\<^sub>2" using L_in_\<LL> by auto
  then show "mreplace_at L p (subm_at L p \<squnion> N) \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2"
  proof cases
    case 1
    then have root_in_\<F>\<^sub>1: "the (root_mctxt (subm_at L p)) \<in> \<F>\<^sub>1" 
      using \<open>p \<in> fun_poss_mctxt L\<close> fun_poss_subm_at[of p L] subm_at_sig[of L \<F>\<^sub>1 p]
            \<LL>\<^sub>1_def fun_poss_all_poss_mctxt[of p L]
      by auto
    from this obtain f :: 'f and Cs :: "('f, 'v) mctxt list"
    where "comp_mctxtp (MFun f Cs) N" and "(f, length Cs) \<in> \<F>\<^sub>1" 
      using comp_context fun_poss_subm_at[of p L] \<open>p \<in> fun_poss_mctxt L\<close>
      by (auto simp: comp_mctxt_def)
    then have "N \<in> \<LL>\<^sub>1" using \<LL>\<^sub>1_def N_in_\<LL>
    proof (induction "(MFun f Cs)" N arbitrary: f Cs rule: comp_mctxtp.induct)
      case (MHole2 f Cs) then show ?case by simp
    next
      case (MFun f g Cs Ds)
        then show ?case using MFun \<LL>\<^sub>2_def disjoint by auto
    qed
    then have "mreplace_at L p (subm_at L p \<squnion> N) \<in> \<LL>\<^sub>1" 
      using 1 \<LL>\<^sub>1_def \<open>p \<in> fun_poss_mctxt L\<close> fun_poss_all_poss_mctxt[of p L] 
            subm_at_sig[of L \<F>\<^sub>1 p] comp_context funas_sup_mctxt[of "subm_at L p" N \<F>\<^sub>1]
            funas_mctxt_mreplace_at[of p L "subm_at L p \<squnion> N"]
      by blast
    then show ?thesis by simp
  next
    case 2 (* analogously to case 1 *)
    then have root_in_\<F>\<^sub>2: "the (root_mctxt (subm_at L p)) \<in> \<F>\<^sub>2" 
      using \<open>p \<in> fun_poss_mctxt L\<close> fun_poss_subm_at[of p L] subm_at_sig[of L \<F>\<^sub>2 p]
            \<LL>\<^sub>2_def fun_poss_all_poss_mctxt[of p L]
      by auto
    from this obtain f :: 'f and Cs :: "('f, 'v) mctxt list"
    where "comp_mctxtp (MFun f Cs) N" and "(f, length Cs) \<in> \<F>\<^sub>2" 
      using comp_context fun_poss_subm_at[of p L] \<open>p \<in> fun_poss_mctxt L\<close>
      by (auto simp: comp_mctxt_def)
    then have "N \<in> \<LL>\<^sub>2" using \<LL>\<^sub>2_def N_in_\<LL>
    proof (induction "(MFun f Cs)" N arbitrary: f Cs rule: comp_mctxtp.induct)
      case (MHole2 f Cs) then show ?case by simp
    next
      case (MFun f g Cs Ds)
        then show ?case using MFun \<LL>\<^sub>1_def disjoint by auto
    qed
    then have "mreplace_at L p (subm_at L p \<squnion> N) \<in> \<LL>\<^sub>2" 
      using 2 \<LL>\<^sub>2_def \<open>p \<in> fun_poss_mctxt L\<close> fun_poss_all_poss_mctxt[of p L] 
            subm_at_sig[of L \<F>\<^sub>2 p] comp_context funas_sup_mctxt[of "subm_at L p" N \<F>\<^sub>2]
            funas_mctxt_mreplace_at[of p L "subm_at L p \<squnion> N"]
      by blast
    then show ?thesis by simp
  qed
qed

interpretation layer_system "\<F>\<^sub>1 \<union> \<F>\<^sub>2" "\<LL>\<^sub>1 \<union> \<LL>\<^sub>2" using modular_layer_system .

lemma sig_subset_layers: "F\<^sub>1 \<subseteq> F\<^sub>2 \<Longrightarrow> {C. funas_mctxt C = F\<^sub>1} \<subseteq> {C. funas_mctxt C \<subseteq> F\<^sub>2}"
by auto

context
begin

interpretation z : modular_cr \<F>\<^sub>1 "{}" "{}" "{} :: ('f, 'v) trs" 
  by standard (auto simp: infinite_UNIV wf_trs_def)

interpretation x : layer_system \<F>\<^sub>1 \<LL>\<^sub>1
  using z.modular_layer_system 
        Un_absorb2[of "{C :: ('f,'v) mctxt. funas_mctxt C = {}}" 
                      "{C. funas_mctxt C \<subseteq> \<F>\<^sub>1}", OF sig_subset_layers]
  unfolding z.\<LL>\<^sub>1_def z.\<LL>\<^sub>2_def by auto

lemma max_top_modular_in_layers1: "max_top_modular \<F>\<^sub>1 t \<in> z.\<LL>\<^sub>1"
using \<LL>\<^sub>1_def by (induction t) auto

lemma top_less_eq1: "max_top_modular \<F>\<^sub>1 t \<le> mctxt_of_term t"
proof (induction t)
  case (Var x) then show ?case by simp
next
  case (Fun f ts) then show ?case using less_eq_mctxt_intros(3)[of _ "(map mctxt_of_term ts)"] by simp
qed

lemma max_top_modular_correct1: "max_top_modular \<F>\<^sub>1 t = layer_system_sig.max_top \<LL>\<^sub>1 t"
proof (induction t)
  case (Var x) then show ?case using x.max_top_var by simp
next
  case (Fun f ts) then show ?case
  proof (cases "(f, length ts) \<in> \<F>\<^sub>1")
    case True
    { fix L
      assume "L \<in> z.\<LL>\<^sub>1" and "L \<le> MFun f (map mctxt_of_term ts)"
      then have "L \<le> MFun f (map (max_top_modular \<F>\<^sub>1) ts)"
        using Fun.IH x.max_topC_props(2) x.topsC_def z.funas_sub_mctxt
        by (cases L) (auto elim!: less_eq_mctxtE1 intro!: less_eq_mctxtI1 simp: z.\<LL>\<^sub>1_def)
    }
    then have less_than_max_top_modular: "L \<in> z.\<LL>\<^sub>1 \<and> L \<le> MFun f (map mctxt_of_term ts)
            \<longrightarrow> L \<le> MFun f (map (max_top_modular \<F>\<^sub>1) ts)" for L by auto
    have unfold_max_top_mod: "max_top_modular \<F>\<^sub>1 (Fun f ts) = MFun f (map (max_top_modular \<F>\<^sub>1) ts)"
      by (simp add: True)
    then have in_\<LL>\<^sub>1: "MFun f (map (max_top_modular \<F>\<^sub>1) ts) \<in> z.\<LL>\<^sub>1"
      by (metis (full_types) max_top_modular_in_layers1)
    have is_top: "MFun f (map (max_top_modular \<F>\<^sub>1) ts) \<le> MFun f (map mctxt_of_term ts)"
      using unfold_max_top_mod by (metis (full_types) mctxt_of_term.simps(2) top_less_eq1)
    have max_top_lt_max_top_mod: "(THE m. m \<in> x.tops (Fun f ts) \<and> 
         (\<forall>ma. ma \<in> x.tops (Fun f ts) \<longrightarrow> ma \<le> m)) \<le> MFun f (map (max_top_modular \<F>\<^sub>1) ts)"
      using less_than_max_top_modular x.max_topC_def x.max_topC_props(1) x.topsC_def by force
    have "MFun f (map (max_top_modular \<F>\<^sub>1) ts) \<le> x.max_topC (MFun f (map mctxt_of_term ts))"
      using is_top in_\<LL>\<^sub>1 by (simp add: x.topsC_def)
    then show ?thesis
      using max_top_lt_max_top_mod unfold_max_top_mod by (simp add: Ball_def_raw x.max_topC_def)
  next
    case False 
    then have "length cs = length ts \<longrightarrow> MFun f cs \<notin> z.\<LL>\<^sub>1" for cs using \<LL>\<^sub>1_def by simp
    then have "L \<in> z.\<LL>\<^sub>1 \<and> L \<le> MFun f (map mctxt_of_term ts) \<longrightarrow> L = MHole" for L 
      by (auto elim: less_eq_mctxt_MFunE2)
    then show ?thesis using Fun False x.max_topC_def x.topsC_def
      bot.extremum_uniqueI x.max_topC_props(1) by fastforce
  qed
qed
end

context
begin
interpretation z : modular_cr "{}" \<F>\<^sub>2 "{}" "{} :: ('f, 'v) trs" 
  by standard (auto simp: infinite_UNIV wf_trs_def)
interpretation x : layer_system \<F>\<^sub>2 \<LL>\<^sub>2
  using z.modular_layer_system 
        Un_absorb1[of "{C :: ('f,'v) mctxt. funas_mctxt C = {}}"
                      "{C. funas_mctxt C \<subseteq> \<F>\<^sub>2}", OF sig_subset_layers]
  unfolding z.\<LL>\<^sub>1_def z.\<LL>\<^sub>2_def by auto

lemma max_top_modular_in_layers2: "max_top_modular \<F>\<^sub>2 t \<in> z.\<LL>\<^sub>2"
using \<LL>\<^sub>2_def by (induction t) auto

lemma top_less_eq2: "max_top_modular \<F>\<^sub>2 t \<le> mctxt_of_term t"
proof (induction t)
  case (Var x) then show ?case by simp
next
  case (Fun f ts) then show ?case using less_eq_mctxt_intros(3)[of _ "(map mctxt_of_term ts)"] by simp
qed

lemma max_top_modular_correct2: "max_top_modular \<F>\<^sub>2 t = layer_system_sig.max_top \<LL>\<^sub>2 t"
proof (induction t)
  case (Var x) then show ?case using x.max_top_var by simp
next
  case (Fun f ts) then show ?case
  proof (cases "(f, length ts) \<in> \<F>\<^sub>2")
    case True
    then have less_than_max_top_modular: "L \<in> z.\<LL>\<^sub>2 \<and> L \<le> MFun f (map mctxt_of_term ts)
            \<longrightarrow> L \<le> MFun f (map (max_top_modular \<F>\<^sub>2) ts)" for L
      using Fun.IH x.max_top_props(2) x.topsC_def z.funas_sub_mctxt
      by (cases L) (auto elim!: less_eq_mctxtE1 intro!: less_eq_mctxtI1 simp: z.\<LL>\<^sub>2_def)
    then have unfold_max_top_mod: "max_top_modular \<F>\<^sub>2 (Fun f ts) = MFun f (map (max_top_modular \<F>\<^sub>2) ts)"
      by (simp add: True)
    then have in_\<LL>\<^sub>2: "MFun f (map (max_top_modular \<F>\<^sub>2) ts) \<in> z.\<LL>\<^sub>2"
      by (metis (full_types) max_top_modular_in_layers2)
    have is_top: "MFun f (map (max_top_modular \<F>\<^sub>2) ts) \<le> MFun f (map mctxt_of_term ts)"
      using unfold_max_top_mod by (metis (full_types) mctxt_of_term.simps(2) top_less_eq2)
    have max_top_lt_max_top_mod: "(THE m. m \<in> x.tops (Fun f ts) \<and> 
         (\<forall>ma. ma \<in> x.tops (Fun f ts) \<longrightarrow> ma \<le> m)) \<le> MFun f (map (max_top_modular \<F>\<^sub>2) ts)"
      using less_than_max_top_modular x.max_topC_def x.max_topC_props(1) x.topsC_def by force
    have "MFun f (map (max_top_modular \<F>\<^sub>2) ts) \<le> x.max_topC (MFun f (map mctxt_of_term ts))"
      using is_top in_\<LL>\<^sub>2 by (simp add: x.topsC_def)
    then show ?thesis
      using max_top_lt_max_top_mod unfold_max_top_mod by (simp add: Ball_def_raw x.max_topC_def)
  next
    case False 
    then have "length cs = length ts \<longrightarrow> MFun f cs \<notin> z.\<LL>\<^sub>2" for cs using \<LL>\<^sub>2_def by simp
    then have "L \<in> z.\<LL>\<^sub>2 \<and> L \<le> MFun f (map mctxt_of_term ts) \<longrightarrow> L = MHole" for L 
      by (auto elim: less_eq_mctxt_MFunE2)
    then show ?thesis using Fun False x.max_topC_def x.topsC_def
      bot.extremum_uniqueI x.max_topC_props(1) by fastforce
  qed
qed
end

lemma L_not_in_\<LL>\<^sub>2: 
  assumes f_in_\<F>\<^sub>1: "(f, length ts) \<in> \<F>\<^sub>1"
  shows "(L \<in> \<LL>\<^sub>1 \<or> L \<in> \<LL>\<^sub>2) \<and> L \<le> MFun f (map mctxt_of_term ts) 
            \<longleftrightarrow> L \<in> \<LL>\<^sub>1 \<and> L \<le> MFun f (map mctxt_of_term ts)"
proof (cases "L \<le> MFun f (map mctxt_of_term ts)")
  case True then show ?thesis
  proof (cases "L")
    case MVar then show ?thesis using \<LL>\<^sub>1_def by auto
  next
    case MHole then show ?thesis using \<LL>\<^sub>1_def by auto
  next
    case (MFun f' Cs) 
    then have "f' = f" using True less_eq_mctxt_MFunE2 by fastforce
    then have "length ts = length Cs" 
      using True MFun less_eq_mctxt_MFunE2 length_map mctxt.distinct(5) mctxt.inject(2)
      by metis
    then have "(f', length Cs) \<notin> \<F>\<^sub>2" using MFun f_in_\<F>\<^sub>1 disjoint \<open>f' = f\<close> by auto
    then have "L \<notin> \<LL>\<^sub>2" using MFun \<LL>\<^sub>2_def disjoint by auto
    then show ?thesis by simp
  qed
next
  case False then show ?thesis by simp
qed

lemma max_top_modular_correct_\<F>\<^sub>1: "(f, n) \<in> \<F>\<^sub>1 \<Longrightarrow> length ts = n \<Longrightarrow> 
      max_top_modular \<F>\<^sub>1 (Fun f ts) = max_top (Fun f ts) \<and> max_top_modular \<F>\<^sub>2 (Fun f ts) = MHole"
using max_top_modular_correct1[of "Fun f ts"] disjoint 
by (auto simp: layer_system_sig.max_topC_def layer_system_sig.topsC_def L_not_in_\<LL>\<^sub>2)

lemma L_not_in_\<LL>\<^sub>1: 
  assumes f_in_\<F>\<^sub>1: "(f, length ts) \<in> \<F>\<^sub>2"
  shows "(L \<in> \<LL>\<^sub>1 \<or> L \<in> \<LL>\<^sub>2) \<and> L \<le> MFun f (map mctxt_of_term ts) 
            \<longleftrightarrow> L \<in> \<LL>\<^sub>2 \<and> L \<le> MFun f (map mctxt_of_term ts)"
proof (cases "L \<le> MFun f (map mctxt_of_term ts)")
  case True then show ?thesis
  proof (cases "L")
    case MVar then show ?thesis using \<LL>\<^sub>2_def by auto
  next
    case MHole then show ?thesis using \<LL>\<^sub>2_def by auto
  next
    case (MFun f' Cs) 
    then have "f' = f" using True less_eq_mctxt_MFunE2 by fastforce
    then have "length ts = length Cs" 
      using True MFun less_eq_mctxt_MFunE2 length_map mctxt.distinct(5) mctxt.inject(2)
      by metis
    then have "(f', length Cs) \<notin> \<F>\<^sub>1" using MFun f_in_\<F>\<^sub>1 disjoint \<open>f' = f\<close> by auto
    then have "L \<notin> \<LL>\<^sub>1" using MFun \<LL>\<^sub>1_def disjoint by auto
    then show ?thesis by simp
  qed
next
  case False then show ?thesis by simp
qed

lemma max_top_modular_correct_\<F>\<^sub>2: "(f, n) \<in> \<F>\<^sub>2 \<Longrightarrow> length ts = n \<Longrightarrow> 
      max_top_modular \<F>\<^sub>2 (Fun f ts) = max_top (Fun f ts) \<and> max_top_modular \<F>\<^sub>1 (Fun f ts) = MHole"
using max_top_modular_correct2[of "Fun f ts"] disjoint 
by (auto simp: layer_system_sig.max_topC_def layer_system_sig.topsC_def L_not_in_\<LL>\<^sub>1)

lemma max_top_var_weak1:
  "max_top t = MVar x \<longleftrightarrow> Var x = t"
by (metis (no_types, lifting) less_eq_mctxt_MVarE1 max_topC_props(1)  
    max_top_var mem_Collect_eq term_of_mctxt_mctxt_of_term_id topsC_def)

(* important lemma *)
lemma max_top_modular_correct:
  shows "max_top t = max_top_mod t"
proof (cases t)
  case (Var x) then show ?thesis using max_top_var by simp
next
  case (Fun f ts)
  then show ?thesis 
  proof (cases "(f, length ts) \<in> (\<F>\<^sub>1 \<union> \<F>\<^sub>2)")
    case True then show ?thesis using max_top_modular_correct_\<F>\<^sub>1[of f "length ts"] disjoint
          max_top_modular_correct_\<F>\<^sub>2[of f "length ts"] sup_mctxt.simps(1) sup_mctxt_MHole
          Fun by auto
  next
    case False
    then have not_MVar: "\<forall>x. max_top t \<noteq> MVar x" 
      using Fun max_topC_def topsC_def \<LL>\<^sub>1_def \<LL>\<^sub>2_def max_top_var_weak1 term.simps(4) 
      by fastforce
    { fix Cs :: "('f, 'v) mctxt list"
      assume "length Cs = length ts"
      then have "(f, length Cs) \<notin> \<F>\<^sub>1 \<union> \<F>\<^sub>2" using False \<LL>\<^sub>1_def \<LL>\<^sub>2_def by simp
      then have "MFun f Cs \<notin> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2" using \<LL>\<^sub>1_def \<LL>\<^sub>2_def funas_mctxt.simps(1)[of f Cs] by blast
    }
    then have "max_top t = MHole" using False Fun not_MVar max_topC_def topsC_def 
          less_eq_mctxt_MFunE2 max_topC_props(1) length_map mctxt_of_term.simps(2) mem_Collect_eq
      by (metis (no_types, lifting))
    then show ?thesis using Fun False by auto
  qed
qed

lemma var_some_subst_correct:
  assumes "funas_term t \<subseteq> \<F>" 
  shows "mctxt_term_conv (max_top_modular \<F> t) = t \<cdot> (Var \<circ> Some)"
using assms by (induction t) auto

lemma subm_at_max_top_modular_consistent:
  assumes "subm_at (max_top_modular \<F>\<^sub>1 t) p = C" and
          "p \<in> poss_mctxt (max_top_modular \<F>\<^sub>1 t)"
  shows "max_top_modular \<F>\<^sub>1 (t |_ p) = C"
using assms
by (induct t p rule: subt_at.induct) auto

text \<open>main lemma for condition C_1 in proof of layered\<close>
lemma lemma_C\<^sub>1:
  fixes p :: pos and s t :: "('f, 'v) term" and r and \<sigma>
  assumes "s \<in> \<T>" and "t \<in> \<T>" and "p \<in> fun_poss_mctxt (max_top s)" and
          rstep_s_t: "(s, t) \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p \<sigma>" and
          s_def_t_def: "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>" "r \<in> \<R>\<^sub>1 \<union> \<R>\<^sub>2" and
          p_def: "p = hole_pos C" and
          root_s: "\<exists>f ts. s = Fun f ts \<and> (f, length ts) \<in> \<F>\<^sub>1"
  shows "\<exists>\<tau>. (mctxt_term_conv (max_top s), mctxt_term_conv (max_top t)) \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p \<tau> \<or>
             (mctxt_term_conv (max_top s), mctxt_term_conv MHole) \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p \<tau>"
proof -
  let ?M = "max_top s" and ?L = "max_top t"
  obtain f ts where "s = Fun f ts" and root_s: "root s = Some (f, length ts)"
                   and f_in_\<F>\<^sub>1: "(f, length ts) \<in> \<F>\<^sub>1" using root_s by auto
  then have max_top_mod_\<F>\<^sub>1: "max_top_modular \<F>\<^sub>1 s = max_top s" 
    using max_top_modular_correct_\<F>\<^sub>1 by blast
  let ?mtm = "\<lambda>t. mctxt_term_conv (max_top_modular \<F>\<^sub>1 t)"
  have p_fun_poss_max_top: "p \<in> fun_poss_mctxt (max_top_modular \<F>\<^sub>1 s)" 
    using max_top_mod_\<F>\<^sub>1 \<open>p \<in> fun_poss_mctxt ?M\<close> by simp
  then have p_in_poss_max_top: "p \<in> all_poss_mctxt (max_top_modular \<F>\<^sub>1 C\<langle>t\<rangle>)" for t
    unfolding s_def_t_def p_def using fun_poss_mctxt_subset_all_poss_mctxt[of "max_top_modular \<F>\<^sub>1 t"]
    by (induct C) (auto simp: fun_poss_mctxt_def 
        nth_append_length[of "map f xs" for f xs, unfolded length_map] split: if_splits)
  moreover have funas_max_top_\<F>\<^sub>1: "funas_term (?mtm C\<langle>t\<rangle>) \<subseteq> \<F>\<^sub>1" for t
    using \<LL>\<^sub>1_def max_top_modular_in_layers1 by simp
  ultimately have "\<exists>D. (\<forall>t. ?mtm C\<langle>t\<rangle> = D\<langle>?mtm t\<rangle>) \<and> hole_pos C = hole_pos D"
   unfolding s_def_t_def p_def
  proof (induction C)
    case Hole then show ?case by (metis intp_actxt.simps(1) hole_pos.simps(1))
  next
    case (More g ss1 C' ss2)
    from More(2)[of undefined] have "(g, Suc (length ss1 + length ss2)) \<in> \<F>\<^sub>1"
      by (auto split: if_splits)
    with More show ?case
      by (auto simp: fun_poss_mctxt_def 
          nth_append_length[of "map f xs" for f xs, unfolded length_map])
         (metis intp_actxt.simps(2) hole_pos.simps(2) length_map)
  qed
  then obtain D where D_assm: "\<forall>t. ?mtm C\<langle>t\<rangle> = D\<langle>?mtm t\<rangle>" and "hole_pos C = hole_pos D" by auto
  have push_in_subst: "funas_term t' \<subseteq> \<F>\<^sub>1 \<longrightarrow> ?mtm (t' \<cdot> \<sigma>) = t' \<cdot> (?mtm \<circ> \<sigma>)" for t'
  by (induction t') auto
  have funas_r_\<F>\<^sub>1:"funas_term (fst r) \<subseteq> \<F>\<^sub>1 \<and> funas_term (snd r) \<subseteq> \<F>\<^sub>1"
  proof (cases "r \<in> \<R>\<^sub>1")
    case True then show ?thesis
    using sig1 lhs_wf[of "fst r" "snd r"] rhs_wf[of "fst r" "snd r"] by simp
  next
    case False
    then have "r \<in> \<R>\<^sub>2" using \<open>r \<in> \<R>\<^sub>1 \<union> \<R>\<^sub>2\<close> by simp
    then obtain f' ts' where l_def: "fst r = Fun f' ts'" using wf2 wf_trs_def by (metis prod.collapse)
    then have f'_in_\<F>\<^sub>2: "(f', length ts') \<in> \<F>\<^sub>2" using sig2
      by (metis \<open>r \<in> \<R>\<^sub>2\<close> contra_subsetD defined_def defined_funas_trs prod.collapse root.simps(2))
    have p_in_poss: "p \<in> poss_mctxt ?M"
      using \<open>p \<in> fun_poss_mctxt ?M\<close> fun_poss_mctxt_subset_poss_mctxt by auto
    have max_top_MHole: "max_top_modular \<F>\<^sub>1 (fst r \<cdot> \<sigma>) = MHole"
      using max_top_modular_correct_\<F>\<^sub>2[OF f'_in_\<F>\<^sub>2] l_def by simp
    have "p \<notin> fun_poss_mctxt (max_top_modular \<F>\<^sub>1 s)"
    proof
      assume "p \<in> fun_poss_mctxt (max_top_modular \<F>\<^sub>1 s)"
      then obtain f' ts' where "subm_at (max_top_modular \<F>\<^sub>1 s) p = MFun f' ts'"
        using fun_poss_subm_at by blast
      then show False using max_top_MHole max_top_mod_\<F>\<^sub>1 p_def p_in_poss 
                       s_def_t_def(1) subm_at_max_top_modular_consistent by fastforce
    qed
    then show ?thesis using p_fun_poss_max_top by auto
  qed
  then have part2: "?mtm (fst r \<cdot> \<sigma>) = fst r \<cdot> (?mtm \<circ> \<sigma>)" using push_in_subst by simp
  have part3: "snd r \<cdot> (?mtm \<circ> \<sigma>) = ?mtm (snd r \<cdot> \<sigma>)"
    using push_in_subst funas_r_\<F>\<^sub>1 by simp
  have part4: "?mtm C\<langle>snd r \<cdot> \<sigma>\<rangle> = D\<langle>?mtm (snd r \<cdot> \<sigma>)\<rangle>" using D_assm by auto
  have first_half: "mctxt_term_conv (max_top s) = D\<langle>fst r \<cdot> (?mtm \<circ> \<sigma>)\<rangle>"
    using s_def_t_def(1) max_top_mod_\<F>\<^sub>1 D_assm part2 by metis
  have second_half: "D\<langle>snd r \<cdot> (?mtm \<circ> \<sigma>)\<rangle> = mctxt_term_conv (max_top_modular \<F>\<^sub>1 (C\<langle>snd r \<cdot> \<sigma>\<rangle>))"
    using part3 part4 D_assm by metis
  then have "(mctxt_term_conv (max_top C\<langle>fst r \<cdot> \<sigma>\<rangle>), 
                      mctxt_term_conv (max_top_modular \<F>\<^sub>1 (C\<langle>snd r \<cdot> \<sigma>\<rangle>))) 
                                 \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p (?mtm \<circ> \<sigma>)" 
    using max_top_mod_\<F>\<^sub>1 first_half rstep_s_t \<open>r \<in> (\<R>\<^sub>1 \<union> \<R>\<^sub>2)\<close> 
          \<open>hole_pos C = hole_pos D\<close> p_def
    by (metis rstep_r_p_s'.rstep_r_p_s' s_def_t_def(1))
  then have W: "\<exists> \<tau>. max_top_modular \<F>\<^sub>1 (C\<langle>snd r \<cdot> \<sigma>\<rangle>) \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2 \<and>
            (mctxt_term_conv ?M, mctxt_term_conv (max_top_modular \<F>\<^sub>1 (C\<langle>snd r \<cdot> \<sigma>\<rangle>))) \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p \<tau>"
    using max_top_modular_in_layers1 Un_iff s_def_t_def(1) [folded p_def] by blast
  then obtain \<tau> where step_to_L: "(mctxt_term_conv ?M, mctxt_term_conv 
                (max_top_modular \<F>\<^sub>1 (C\<langle>snd r \<cdot> \<sigma>\<rangle>))) \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p \<tau>" by auto
  then show ?thesis
  proof (cases "max_top_modular \<F>\<^sub>1 (C\<langle>snd r \<cdot> \<sigma>\<rangle>)")
    case MHole then show ?thesis using step_to_L by auto
  next
    case (MVar x)
    then have "p = []" using step_to_L all_poss_mctxt.simps(1) p_in_poss_max_top
      by (metis singletonD)
    then obtain y where "snd r = Var y" and "Var y \<cdot> \<tau> = Var (Some x)"
      using MVar step_to_L rstep_r_p_s'.cases subst_apply_eq_Var 
            ctxt_supteq supteq_var_imp_eq mctxt_term_conv.simps(2)
      by (metis (no_types, lifting))
    then have "max_top_modular \<F>\<^sub>1 (C\<langle>snd r \<cdot> \<sigma>\<rangle>) = max_top t"
    using s_def_t_def(2)
      by (metis less_eq_mctxt_MVarE1 local.MVar max_top_var mctxt_of_term.simps(1) top_less_eq1) 
    then show ?thesis using step_to_L by auto
  next
    case MFun
    then obtain f ts where t_def: "t = Fun f ts"
      using s_def_t_def(2) max_top_modular.simps by (cases t) auto
    then have "(f, length ts) \<in> \<F>\<^sub>1"
      using \<open>t \<in> \<T>\<close> \<T>_def disjoint max_top_modular_correct_\<F>\<^sub>2 MFun s_def_t_def(2)
      by auto
    then have "max_top_modular \<F>\<^sub>1 (C\<langle>snd r \<cdot> \<sigma>\<rangle>) = max_top t"
      using max_top_modular_correct_\<F>\<^sub>1 s_def_t_def(2) t_def by simp
    then show ?thesis using step_to_L by auto
  qed
qed


interpretation layered "\<F>\<^sub>1 \<union> \<F>\<^sub>2" "\<LL>\<^sub>1 \<union> \<LL>\<^sub>2" "\<R>\<^sub>1 \<union> \<R>\<^sub>2"
text \<open>done (Franziska)\<close>
proof (* trs *)
  show "wf_trs (\<R>\<^sub>1 \<union> \<R>\<^sub>2)" using wf1 wf2 by (auto simp: wf_trs_def)
next (* \<R>_sig *)
  show "funas_trs (\<R>\<^sub>1 \<union> \<R>\<^sub>2) \<subseteq> \<F>\<^sub>1 \<union> \<F>\<^sub>2" using sig1 sig2 by auto
next (* C1 *)
  fix p :: pos and s t :: "('f, 'v) term" and r and \<sigma>
  let ?M = "max_top s" and ?L = "max_top t"
  assume assms: "s \<in> \<T>" "t \<in> \<T>" "p \<in> fun_poss_mctxt ?M" and
         rstep_s_t: "(s, t) \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p \<sigma>"
  then obtain C where
    s_def_t_def: "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>" "r \<in> \<R>\<^sub>1 \<union> \<R>\<^sub>2" and
    p_def: "p = hole_pos C"
    by auto
  show "\<exists>\<tau>. (mctxt_term_conv ?M, mctxt_term_conv ?L) \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p \<tau> \<or>
            (mctxt_term_conv ?M, mctxt_term_conv MHole) \<in> rstep_r_p_s' (\<R>\<^sub>1 \<union> \<R>\<^sub>2) r p \<tau>"
  proof -
    consider "\<exists>f ts. s = Fun f ts \<and> (f, length ts) \<in> \<F>\<^sub>1" 
           | "\<exists>f ts. s = Fun f ts \<and> (f, length ts) \<in> \<F>\<^sub>2"
           | "\<exists>x. s = Var x" using \<open>s \<in> \<T>\<close> \<T>_def by (cases s) auto
    then show ?thesis
    proof cases
      case 1 then show ?thesis using lemma_C\<^sub>1 assms rstep_s_t s_def_t_def p_def by auto
    next
      case 2 then show ?thesis using modular_cr.lemma_C\<^sub>1[OF modular_cr_symmetric] assms
                                rstep_s_t s_def_t_def p_def
        by (metis inf_sup_aci(5) modular_cr.\<LL>\<^sub>1_def modular_cr.\<LL>\<^sub>2_def modular_cr_axioms modular_cr_symmetric)
    next
      case 3 then show ?thesis 
      using rstep_s_t wf_union_trs NF_Var[of "\<R>\<^sub>1 \<union> \<R>\<^sub>2"] rstep_eq_rstep' 
            rstep'_iff_rstep_r_p_s' prod.collapse
      by metis
    qed
  qed
next (* C2 *)
  fix L N :: "('f, 'v) mctxt" and p :: pos
  assume N_in_\<LL>: "N \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2" and
         L_in_\<LL>: "L \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2" and 
         "L \<le> N" and
         "p \<in> hole_poss L"
  consider "N \<in> \<LL>\<^sub>1" | "N \<in> \<LL>\<^sub>2" using N_in_\<LL> by auto
  then show "mreplace_at L p (subm_at N p) \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2"
  proof cases
    case 1
    then have "L \<in> \<LL>\<^sub>1" using \<open>L \<le> N\<close> \<LL>\<^sub>1_def by auto
    have "p \<in> all_poss_mctxt N"
      using \<open>p \<in> hole_poss L\<close> \<open>L \<le> N\<close> all_poss_mctxt_conv all_poss_mctxt_mono[of L N]
      by auto
    then have "mreplace_at L p (subm_at N p) \<in> \<LL>\<^sub>1"
      using 1 \<open>p \<in> hole_poss L\<close> \<open>L \<le> N\<close> \<open>L \<in> \<LL>\<^sub>1\<close> \<LL>\<^sub>1_def
      proof (induction "N :: ('f, 'v) mctxt" p rule: subm_at.induct)
        case (2 f Cs i p)
        then have "funas_mctxt (MFun f Cs) \<subseteq> \<F>\<^sub>1" by simp
        then have "funas_mctxt (subm_at (MFun f Cs) (i # p)) \<subseteq> \<F>\<^sub>1" 
          using subm_at_sig[of "MFun f Cs" \<F>\<^sub>1 "i # p"] 2 by simp
        then show ?case using 2
          proof (induction L "(i # p)" 
               "(subm_at (MFun f Cs) (i # p)) :: ('f, 'v) mctxt"
                rule: mreplace_at.induct)
            case (2 f' Cs') then show ?case 
            using funas_mctxt_mreplace_at_hole[of "i # p" "MFun f' Cs'" 
                                               "subm_at (MFun f Cs) (i # p)"] by auto
          qed auto
      qed auto
    then show ?thesis by simp
  next
    case 2 (* analogously to case 1 *)
    then have "L \<in> \<LL>\<^sub>2" using \<open>L \<le> N\<close> \<LL>\<^sub>2_def by auto
    have "p \<in> all_poss_mctxt N"
      using \<open>p \<in> hole_poss L\<close> \<open>L \<le> N\<close> all_poss_mctxt_conv all_poss_mctxt_mono[of L N]
      by auto
    then have "mreplace_at L p (subm_at N p) \<in> \<LL>\<^sub>2"
      using 2 \<open>p \<in> hole_poss L\<close> \<open>L \<le> N\<close> \<open>L \<in> \<LL>\<^sub>2\<close> \<LL>\<^sub>2_def
      proof (induction "N :: ('f, 'v) mctxt" p rule: subm_at.induct)
        case (2 f Cs i p)
        then have "funas_mctxt (MFun f Cs) \<subseteq> \<F>\<^sub>2" by simp
        then have "funas_mctxt (subm_at (MFun f Cs) (i # p)) \<subseteq> \<F>\<^sub>2" 
          using subm_at_sig[of "MFun f Cs" \<F>\<^sub>2 "i # p"] 2 by simp
        then show ?case using 2
          proof (induction L "(i # p)" 
               "(subm_at (MFun f Cs) (i # p)) :: ('f, 'v) mctxt"
                rule: mreplace_at.induct)
            case (2 f' Cs') then show ?case
            using funas_mctxt_mreplace_at_hole[of "i # p" "MFun f' Cs'" 
                                               "subm_at (MFun f Cs) (i # p)"] by auto
          qed auto
      qed auto
    then show ?thesis by simp
  qed
qed

lemma conserv_subst: "funas_term (t \<cdot> \<sigma>) \<subseteq> \<F> \<Longrightarrow> funas_term t \<subseteq> \<F>"
proof -
  assume "funas_term (t \<cdot> \<sigma>) \<subseteq> \<F>"
  from this show "funas_term t \<subseteq> \<F>"
  proof (induction t)
    case (Var x) then show ?case by simp
  next
    case (Fun f Cs) then show ?case using funas_term_subst by blast
  qed
qed

lemma conserv_T1:
  assumes "a \<in> \<T>\<^sub>1"
  shows "(a, b) \<in> rstep \<R>\<^sub>1 \<Longrightarrow> b \<in> \<T>\<^sub>1"
proof -
  assume "(a, b) \<in> rstep \<R>\<^sub>1"
  from this and assms show "b \<in> \<T>\<^sub>1"
  proof (induction)
    case (IH C \<sigma> l r)
    then have "funas_rule (l, r) \<subseteq> \<F>\<^sub>1" using sig1 by (auto simp: funas_trs_def)
    then have "funas_term r \<subseteq> \<F>\<^sub>1" by (auto simp: funas_rule_def)
    have "vars_term r \<subseteq> vars_term l" using IH and wf1 by (simp add: wf_trs_def)
    then show ?case using IH and \<open>funas_term r \<subseteq> \<F>\<^sub>1\<close> by (auto simp: funas_term_subst) blast
  qed
qed

lemma incomparable_T1R2:
  assumes a_in_T1: "a \<in> \<T>\<^sub>1"
  shows "(a, b) \<notin> rstep \<R>\<^sub>2"
proof
  assume "(a, b) \<in> rstep \<R>\<^sub>2"
  from this and assms show False
  proof (induction rule: rstep_induct)
    case (rule a b) 
      then have "a \<in> \<T>\<^sub>2" using sig2 funas_rule_def[of "(a, b)"] by (auto simp: funas_trs_def)
      then have is_var_a: "\<exists>v. a = Var v" using rule disjoint 
      proof (induction a)
        case (Var x) then show ?case by simp
      next
        case (Fun f Cs) 
          then have False by auto 
          then show ?case by simp
      qed
      then show ?case using rule is_var_a wf2 by (auto simp: wf_trs_def)
  next
    case (subst a b \<sigma>) then show ?case using conserv_subst[of a \<sigma> \<F>\<^sub>1] by simp
  next
    case ctxt then show ?case by simp
  qed
qed

thm rtrancl_induct
thm converse_rtrancl_induct

lemma conserv_star_T1:
  assumes "(a, b) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>*" and "a \<in> \<T>\<^sub>1"
  shows "b \<in> \<T>\<^sub>1"
using assms conserv_T1
by (induction rule: converse_rtrancl_induct) (auto simp: rstep_union incomparable_T1R2)

lemma unapplicable_T1R2:
  assumes "(a, b) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>*" and "a \<in> \<T>\<^sub>1"
  shows "(a, b) \<in> (rstep \<R>\<^sub>1)\<^sup>*"
using assms conserv_T1 incomparable_T1R2
by (induction rule: converse_rtrancl_induct) (auto simp: rstep_union)

lemma unapplicable_T2R1:
  assumes "(a, b) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>*" and "a \<in> \<T>\<^sub>2"
  shows "(a, b) \<in> (rstep \<R>\<^sub>2)\<^sup>*"
using assms modular_cr.unapplicable_T1R2[OF modular_cr_symmetric]
by (auto simp: ac_simps)

lemma rstep_union_sub: "(rstep \<R>\<^sub>1)\<^sup>* \<subseteq> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>* \<and> (rstep \<R>\<^sub>2)\<^sup>* \<subseteq> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>*"
 by (simp add: rstep_union rtrancl_mono)

lemma CR_on_union:
  assumes CR1: "CR_on (rstep \<R>\<^sub>1) \<T>\<^sub>1"
  and CR2: "CR_on (rstep \<R>\<^sub>2) \<T>\<^sub>2"
  shows "CR_on (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2)) { t. mctxt_of_term t \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2 }"
text \<open>done (Franziska)\<close>
proof
  fix a b c
  assume a_in_L1L2:"a \<in> {t. mctxt_of_term t \<in> \<LL>\<^sub>1 \<union> \<LL>\<^sub>2}" 
         and a_to_b: "(a, b) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>*"
         and a_to_c: "(a, c) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>*"
  then have "a \<in> {t. mctxt_of_term t \<in> \<LL>\<^sub>1} \<or> a \<in> {t. mctxt_of_term t \<in> \<LL>\<^sub>2}" by simp
  then consider "a \<in> {t. mctxt_of_term t \<in> \<LL>\<^sub>1}" | "a \<in> {t. mctxt_of_term t \<in> \<LL>\<^sub>2}" by rule
  then show "(b, c) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>\<down>"
  proof cases
      case 1
      then have "a \<in> \<T>\<^sub>1" using \<LL>\<^sub>1_def by simp
      then have a_to_b_R1:"(a, b) \<in> (rstep \<R>\<^sub>1)\<^sup>*" and a_to_c_R1:"(a, c) \<in> (rstep \<R>\<^sub>1)\<^sup>*" 
        using a_to_b a_to_c by (auto simp: unapplicable_T1R2)
      then have "(b, c) \<in> (rstep \<R>\<^sub>1)\<^sup>\<down>" 
        using CR1 \<open>a \<in> \<T>\<^sub>1\<close> CR_on_def[of "rstep \<R>\<^sub>1" \<T>\<^sub>1] by simp
      then show ?thesis using rstep_union_sub joinD[of b c "rstep \<R>\<^sub>1"] by auto
    next
      case 2
      then have "a \<in> \<T>\<^sub>2" using \<LL>\<^sub>2_def by simp
      then have a_to_b_R2:"(a, b) \<in> (rstep \<R>\<^sub>2)\<^sup>*" and a_to_c_R2:"(a, c) \<in> (rstep \<R>\<^sub>2)\<^sup>*"
        using a_to_b a_to_c by (auto simp: unapplicable_T2R1)
      then have "(b, c) \<in> (rstep \<R>\<^sub>2)\<^sup>\<down>" 
        using CR2 \<open>a \<in> \<T>\<^sub>2\<close> a_to_b_R2 a_to_c_R2 CR_on_def[of "rstep \<R>\<^sub>2" \<T>\<^sub>2] by simp
      then show ?thesis using rstep_union_sub joinD[of b c "rstep \<R>\<^sub>2"] by auto
  qed
qed                                                            

lemma CR_mod1:
  assumes CR_union: "CR_on (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2)) \<T>"
  shows "CR_on (rstep \<R>\<^sub>1) \<T>\<^sub>1"
proof -
  have "\<T>\<^sub>1 \<subseteq> \<T>" unfolding \<T>_def by auto
  then have "CR_on (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2)) \<T>\<^sub>1" unfolding CR_defs
        using CR_union CR_onI[of \<T>\<^sub>1 \<R>\<^sub>1] CR_defs[of "rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2)" \<T>] by auto
  have "(\<And>a b c. a \<in> \<T>\<^sub>1 \<Longrightarrow> (a, b) \<in> (rstep \<R>\<^sub>1)\<^sup>* \<Longrightarrow> (a, c) \<in> (rstep \<R>\<^sub>1)\<^sup>*
           \<Longrightarrow> (b, c) \<in> (rstep \<R>\<^sub>1)\<^sup>\<down>)"
  proof -
    fix a b c
    assume a_T1: "a \<in> \<T>\<^sub>1" and ab_R1: "(a, b) \<in> (rstep \<R>\<^sub>1)\<^sup>*" 
                          and ac_R1: "(a, c) \<in> (rstep \<R>\<^sub>1)\<^sup>*"
    then have "(b, c) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>\<down>" using \<open>CR_on (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2)) \<T>\<^sub>1\<close>
          by (meson CR_on_def rstep_union_sub subset_eq)
    then obtain d 
         where join_R1R2:"(b, d) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>* \<and> (c, d) \<in> (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2))\<^sup>*" 
         using joinD by auto
    have "b \<in> \<T>\<^sub>1" using a_T1 ab_R1 conserv_star_T1[of a b] rstep_union_sub by auto
    have "c \<in> \<T>\<^sub>1" using a_T1 ac_R1 conserv_star_T1[of a c] rstep_union_sub by auto
    show "(b, c) \<in> (rstep \<R>\<^sub>1)\<^sup>\<down>" 
      using join_R1R2 \<open>b \<in> \<T>\<^sub>1\<close> \<open>c \<in> \<T>\<^sub>1\<close> unapplicable_T1R2[of b d] 
            unapplicable_T1R2[of c d] rtrancl_converseD
      by auto
  qed
  then show ?thesis using CR_onI[of \<T>\<^sub>1 "(rstep \<R>\<^sub>1)"] by simp
qed

lemmas CR_mod2 = modular_cr.CR_mod1[OF modular_cr_symmetric]

text \<open>The following lemma establishes the easy direction of modularity of confluence.\<close>
lemma CR_mod':
  assumes CR_union: "CR_on (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2)) \<T>"
  shows "CR_on (rstep \<R>\<^sub>1) \<T>\<^sub>1" and "CR_on (rstep \<R>\<^sub>2) \<T>\<^sub>2"
  by (auto simp: assms CR_mod1 CR_mod2 sup_commute)

text \<open>The following lemma is the interesting direction of modularity of confluence {cite \<open>Theorem 5.1\<close> FMZvO15}.\<close>
lemma CR_mod:
  assumes "CR_on (rstep \<R>\<^sub>1) \<T>\<^sub>1"  "CR_on (rstep \<R>\<^sub>2) \<T>\<^sub>2"
  shows "CR_on (rstep (\<R>\<^sub>1 \<union> \<R>\<^sub>2)) \<T>"
  using assms by (rule CR[OF CR_on_union])

end

text \<open>As a test, we show that modularity implies signature extension.\<close>

lemma CR_on_imp_CR:
  fixes \<R> :: "('f, 'v :: infinite) trs"
  assumes "wf_trs \<R>" and "funas_trs \<R> \<subseteq> \<F>"
  and "CR_on (rstep \<R>) { t :: ('f, 'v) term. funas_term t \<subseteq> \<F> }"
  shows "CR (rstep \<R>)"
proof -
  define \<F>\<^sub>c where "\<F>\<^sub>c = { (f,n). (f,n) \<notin> \<F> }"
  then have disjoint_1: "\<F> \<inter> \<F>\<^sub>c = {}" by auto
  have *: "layer_system_sig.\<T> (\<F> \<union> \<F>\<^sub>c) = UNIV" by (auto simp: \<F>\<^sub>c_def layer_system_sig.\<T>_def)
  have mod_cr: "modular_cr \<F> \<F>\<^sub>c \<R> {}" using assms disjoint_1 wf_trs_def
    by (metis Int_lower2 empty_iff funas_empty modular_cr.intro)
  have CR_empty: "CR_on (rstep {}) { t :: ('f, 'v) term. funas_term t \<subseteq> \<F>\<^sub>c }" by fastforce
  then show ?thesis using modular_cr.CR_on_union[OF mod_cr assms(3) CR_empty] modular_cr.CR_mod
    by (metis * assms(3) mod_cr sup_bot.right_neutral)
qed

end
