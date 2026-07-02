(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Basic facts about layer systems\<close>

theory LS_Basics
  imports 
    LS_Prelude 
    TRS.Renaming_Interpretations
    Auxx.Multiset2
begin

context layer_system
begin

lemma mvar_layer [simp]:
  "MVar v \<in> \<LL>"
  using L\<^sub>1[of "Var v"] by (auto elim: less_eq_mctxtE2)

lemma mhole_layer [simp]:
  "MHole \<in> \<LL>"
  using L\<^sub>2[of "[]" "MVar _" _] by auto

lemma L\<^sub>3':
  assumes "L \<in> \<LL>" "N \<in> \<LL>" "p \<in> poss_mctxt L" "(subm_at L p, N) \<in> comp_mctxt"
  shows "mreplace_at L p (subm_at L p \<squnion> N) \<in> \<LL>"
proof (cases "p \<in> fun_poss_mctxt L")
  case True then show ?thesis using assms by (auto intro: L\<^sub>3)
next
  case False
  then obtain x where "subm_at L p = MVar x" using assms(3)
  proof (induct L arbitrary: p)
    case (MFun f Ls)
    then obtain i q where "p = i # q"  "q \<notin> fun_poss_mctxt (Ls ! i)"
      by (cases p) (auto simp: fun_poss_mctxt_def)
    then show ?thesis using MFun(2-) by (auto intro: MFun(1)[of "Ls ! i" q])
  qed auto
  then show ?thesis using assms(1,3,4) replace_at_subm_at[of p L]
    by (cases N) (auto elim: comp_mctxt.cases simp: all_poss_mctxt_conv)
qed

end (* layer_system *)

fun vars_to_holes :: "('f, 'v) mctxt \<Rightarrow> ('f, 'w) mctxt" where
  "vars_to_holes (MVar _)    = MHole"
| "vars_to_holes MHole       = MHole"
| "vars_to_holes (MFun f ts) = MFun f (map vars_to_holes ts)"

abbreviation vars_to_holes' :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v) mctxt" where
  "vars_to_holes' \<equiv> vars_to_holes"

lemma vars_to_holes_idem[simp]:
  "vars_to_holes (vars_to_holes C) = vars_to_holes C"
  by (induct C) auto

lemma vars_to_holes_prefix:
  "vars_to_holes C \<le> C"
  by (induct C) (auto simp add: less_eq_mctxt_def zip_map1 zip_same_conv_map)

lemma fun_poss_mctxt_vars_to_holes [simp]:
  "fun_poss_mctxt (vars_to_holes C) = fun_poss_mctxt C"
  by (induct C) (auto simp: fun_poss_mctxt_def)

lemma vars_to_holes_mreplace_at [simp]:
  "p \<in> poss_mctxt C \<Longrightarrow> vars_to_holes (mreplace_at C p D) = mreplace_at (vars_to_holes C) p (vars_to_holes D)"
  by (induct C p D rule: mreplace_at.induct) (auto simp: take_map drop_map)

lemma vars_to_holes_subm_at [simp]:
  "p \<in> poss_mctxt C \<Longrightarrow> vars_to_holes (subm_at C p) = subm_at (vars_to_holes C) p"
  by (induct C p rule: subm_at.induct) auto

lemma vars_to_holes_merge [simp]:
  "(C, D) \<in> comp_mctxt \<Longrightarrow> vars_to_holes (C \<squnion> D) = vars_to_holes C \<squnion> vars_to_holes D"
  by (induct C D rule: comp_mctxt.induct) (auto simp: zip_map1 zip_map2 in_set_conv_nth)

lemma vars_to_holes_comp_mctxt:
  "(C, D) \<in> comp_mctxt \<Longrightarrow> (vars_to_holes C, vars_to_holes D) \<in> comp_mctxt"
  by (induct C D rule: comp_mctxt.induct) (auto intro: comp_mctxt.intros)

lemma vars_to_holes_mono:
  "C \<le> D \<Longrightarrow> vars_to_holes C \<le> vars_to_holes D"
  unfolding less_eq_mctxt_prime
  by (induct C D rule: less_eq_mctxt'.induct) (auto intro: less_eq_mctxt'.intros)

lemma vars_to_holes'_mono: "C \<le> D \<Longrightarrow> vars_to_holes' C \<le> vars_to_holes' D"
  by (rule vars_to_holes_mono)

lemma mctxt_term_conv_vars_to_holes:
  "mctxt_term_conv (vars_to_holes C) = mctxt_term_conv C \<cdot> (\<lambda>_. Var None)"
  by (induct C) auto

lemma funas_term_vars_to_holes [simp]:
  "funas_mctxt (vars_to_holes C) = funas_mctxt C"
  by (induct C) auto

lemma vars_to_holes_map_vars_mctxt [simp]:
  "vars_to_holes (map_vars_mctxt f C) = vars_to_holes C"
   by (induct C) auto

lemma vars_to_holes_sup:
  "(C, D) \<in> comp_mctxt \<Longrightarrow> vars_to_holes (C \<squnion> D) = vars_to_holes C \<squnion> vars_to_holes D"
  by (induct C D rule: comp_mctxt.induct) (auto simp: comp_def zip_map1 zip_map2 set_conv_nth)

lemma (in layer_system) vars_to_holes_layer:
  "vars_to_holes C \<in> \<LL> \<longleftrightarrow> C \<in> \<LL>"
proof (induct "mctxt_syms C" arbitrary: C rule: less_induct)
  case (less C) show *: ?case
  proof (cases "\<exists>p v. p \<in> poss_mctxt C \<and> subm_at C p = MVar v")
    case True
    then obtain p v where p: "p \<in> poss_mctxt C" and C: "subm_at C p = MVar v" by blast
    {
      fix D :: "('f,'v) mctxt"
      assume "D = MHole"
      with p C have "vars_to_holes' (mreplace_at C p D) = vars_to_holes (mreplace_at C p (MVar v))"
        and "mctxt_syms (mreplace_at C p (MVar v)) > mctxt_syms (mreplace_at C p D)"
        and "mreplace_at C p (MVar v) = C"
      by (induct C p D rule: mreplace_at.induct) (auto dest: id_take_nth_drop)
    }
    then show ?thesis using less[of "mreplace_at C p MHole"] L\<^sub>2[OF p, of v] by auto
  next
    case False
    {
      assume "\<And>p v. p \<in> poss_mctxt C \<Longrightarrow> subm_at C p \<noteq> MVar v"
      then have "vars_to_holes C = C"
      proof (induct C)
        case (MFun f ts)
        {
          fix t p v
          assume "t \<in> set ts" and "p \<in> poss_mctxt t"
          then have "subm_at t p \<noteq> MVar v"
          using MFun(2)[of "Cons _ p"] in_set_conv_nth[of t ts] by auto
        }
        with MFun(1) show ?case using map_cong[of ts ts vars_to_holes id] by auto
      qed auto
    }
    with False show ?thesis by simp
  qed
qed

lemma (in layer_system) vars_to_holes'_layer:
  "vars_to_holes' C \<in> \<LL> \<longleftrightarrow> C \<in> \<LL>"
  by (rule local.vars_to_holes_layer)

lemma vars_to_holes_fill_holes:
  "num_holes C = length Cs \<Longrightarrow> set Cs \<subseteq> {MHole} \<union> MVar ` UNIV \<Longrightarrow> vars_to_holes (fill_holes_mctxt C Cs) = vars_to_holes C"
  apply (induct C Cs rule: fill_holes_induct)
  unfolding List.set_concat
  by (auto intro!: nth_equalityI simp: set_conv_nth[of "partition_holes _ _"]) blast

lemma vars_to_holes'_fill_holes:
  "num_holes C = length Cs \<Longrightarrow> set Cs \<subseteq> {MHole} \<union> MVar ` UNIV \<Longrightarrow> vars_to_holes' (fill_holes_mctxt C Cs) = vars_to_holes' C"
  by (rule vars_to_holes_fill_holes)

lemma (in layer_system) vars_to_holes_fill_holes_layer:
  assumes "num_holes C = length Cs" "set Cs \<subseteq> {MHole} \<union> MVar ` UNIV"
  shows "fill_holes_mctxt C Cs \<in> \<LL> \<longleftrightarrow> C \<in> \<LL>"
  by (metis assms vars_to_holes_fill_holes vars_to_holes_layer)

fun holes_to_var where
  "holes_to_var MHole = Var undefined"
| "holes_to_var (MVar x) = Var x"
| "holes_to_var (MFun f Cs) = Fun f (map holes_to_var Cs)"

abbreviation holes_to_var' where "holes_to_var' x \<equiv> mctxt_of_term (holes_to_var x)"

lemma vars_to_holes_holes_to_vars_conv [simp]:
  "vars_to_holes (holes_to_var' C) = vars_to_holes C"
  by (induct C) auto

lemma holes_to_var_subm [simp]:
  "C \<le> holes_to_var' C"
  by (induct C) (auto intro: less_eq_mctxtI1)

lemma funas_term_holes_to_var [simp]:
  "funas_term (holes_to_var C) = funas_mctxt C"
  by (induct C) auto

context layer_system
begin

lemma holes_to_var_layer:
  "holes_to_var' C \<in> \<LL> \<longleftrightarrow> C \<in> \<LL>"
  using vars_to_holes_layer[of C] vars_to_holes_layer[of "holes_to_var' C"] by simp

lemma mfun_layer [simp]:
  assumes fn: "(f, n) \<in> \<F>" shows "MFun f (replicate n MHole) \<in> \<LL>"
proof -
  from fn have *: "funas_term (holes_to_var (MFun f (replicate n (MHole)))) \<subseteq> \<F>" by auto
  obtain L where **: "L \<in> \<LL>" "L \<noteq> MHole" "L \<le> holes_to_var' (MFun f (replicate n (MHole)))"
    using L\<^sub>1[OF *] by blast
  then obtain Cs where "L = MFun f Cs" by (cases L) (auto elim: less_eq_mctxtE1)
  then have "vars_to_holes' L = MFun f (replicate n (MHole))" using vars_to_holes_mono[OF **(3)]
    by (cases L) (auto elim!: less_eq_mctxtE2 intro!: nth_equalityI)
  then show ?thesis using \<open>L \<in> \<LL>\<close> vars_to_holes_layer[of L] by simp
qed

lemma sup_mctxt_LL:
  "(L, N) \<in> comp_mctxt \<Longrightarrow> L \<in> \<LL> \<Longrightarrow> N \<in> \<LL> \<Longrightarrow> L \<squnion> N \<in> \<LL>"
  by (cases L N rule: comp_mctxt.cases) (insert L\<^sub>3[of L N "[]"], auto simp: fun_poss_mctxt_def)

lemma comp_MFunD:
  assumes "(MFun f Cs, MFun g Ds) \<in> comp_mctxt"
  shows "f = g \<and> length Cs = length Ds \<and> (\<forall>i < length Ds. (Cs ! i, Ds ! i) \<in> comp_mctxt)"
  using assms by (auto elim: comp_mctxt.cases)

lemma (in layer_system) map_vars_mctxt_layer [simp]:
  "map_vars_mctxt f C \<in> \<LL> \<longleftrightarrow> C \<in> \<LL>"
  using vars_to_holes_layer[of C] vars_to_holes_layer[of "map_vars_mctxt f C"] by simp

text \<open>{cite \<open>Lemma 3.5\<close> FMZvO15} part 1\<close>

lemma max_top_unique:
  shows "\<exists>!M. M \<in> topsC C \<and> (\<forall>L \<in> topsC C. L \<le> M)"
proof -
  let ?r = "{ (D, E). D > E } \<inter> topsC C \<times> topsC C"
  have "trans ?r" by (auto simp: trans_def)
  then have "wf ?r" by (intro finite_acyclic_wf) (auto simp: finite_pre_mctxt acyclic_irrefl irrefl_def topsC_def)
  have "MHole \<in> topsC C" by (simp add: topsC_def)
  then have "\<exists>L \<in> topsC C. \<forall>y. (y, L) \<in> ?r \<longrightarrow> y \<notin> topsC C"
  using \<open>wf ?r\<close>[unfolded wf_eq_minimal] by blast
  then obtain M where M: "M \<in> topsC C" and *: "\<And>L. L \<in> topsC C \<Longrightarrow> \<not> L > M" by auto
  {
    fix L
    assume L: "L \<in> topsC C"
    have c: "(L, M) \<in> comp_mctxt" using L M by (auto intro: prefix_comp_mctxt simp: topsC_def)
    have t: "L \<squnion> M \<in> topsC C" using L M by (auto intro: sup_mctxt_LL[OF c] prefix_mctxt_sup simp: topsC_def)
    have "L \<squnion> M \<ge> M" by (auto intro: sup_mctxt_ge2 simp: c)
    then have "L \<squnion> M = M" using *[OF t] by (auto simp: less_mctxt_def)
    also have "L \<le> L \<squnion> M" by (simp add: c)
    ultimately have "L \<le> M" by simp
  } note ** = this
  show ?thesis
  proof
    show "M \<in> topsC C \<and> (\<forall>L \<in> topsC C. L \<le> M)" by (simp add: M **)
  next
    fix M'
    assume "M' \<in> topsC C \<and> (\<forall>L \<in> topsC C. L \<le> M')"
    then show "M' = M" by (intro antisym) (auto simp: M **)
  qed
qed

lemma max_topCI:
  assumes "M \<in> topsC C" "\<And>L. L \<in> topsC C \<Longrightarrow> L \<le> M"
  shows "max_topC C = M"
  using assms max_top_unique[of C] by (auto simp: max_topC_def)

lemma max_topC_props [simp]:
  shows "max_topC C \<in> topsC C" and "\<And>L. L \<in> topsC C \<Longrightarrow> L \<le> max_topC C"
  by (auto simp: theI'[OF max_top_unique] max_topC_def)

lemmas max_top_props = max_topC_props[where C = "mctxt_of_term _"]

lemma max_topC_layer [simp]:
  "max_topC C \<in> \<LL>"
  using max_topC_props by (auto simp: topsC_def)

lemmas max_top_layer = max_topC_layer[of "mctxt_of_term _"]

lemma max_topC_prefix:
  "max_topC C \<le> C"
  using max_topC_props(1) unfolding topsC_def by blast

lemmas max_top_prefix = max_topC_prefix[of "mctxt_of_term _"]

lemma max_topC_mono:
  "C \<le> D \<Longrightarrow> max_topC C \<le> max_topC D"
  using max_topC_props(1)[of C] max_topC_props(2)[of "max_topC C" D] by (auto simp: topsC_def)

lemma max_topC_idem:
  "max_topC (max_topC C) = max_topC C"
  by (metis (lifting) dual_order.antisym max_topC_props mem_Collect_eq topsC_def)

text \<open>{cite \<open>Lemma 3.5\<close> FMZvO15} part 2\<close>

lemma non_empty_max_top_non_empty:
  assumes "C \<in> \<C>" "C \<noteq> MHole" shows "max_topC C \<noteq> MHole"
proof (cases C)
  case MHole then show ?thesis using assms by simp
next
  case (MVar v)
  then have "MVar v \<le> max_topC C" using assms by (simp add: topsC_def)
  then show ?thesis by (auto simp: less_eq_mctxt_def)
next
  case (MFun f ts)
  then have "MFun f (replicate (length ts) MHole) \<in> topsC C" using assms MFun
  by (simp add: topsC_def less_eq_mctxt_def comp_def map_replicate_const \<C>_def)
  then have "MFun f (replicate (length ts) MHole) \<le> max_topC C" by auto
  then show ?thesis by (auto simp: less_eq_mctxt_def)
qed

lemma funas_max_topC [simp]:
  "C \<in> \<C> \<Longrightarrow> fn \<in> funas_mctxt (max_topC C) \<Longrightarrow> fn \<in> funas_mctxt C"
  using max_topC_props[of C] by (auto simp: topsC_def)

lemma max_top_not_hole [simp]:
  "t \<in> \<T> \<Longrightarrow> max_top t \<noteq> MHole"
  by (intro non_empty_max_top_non_empty) (auto simp: \<T>_def \<C>_def)

lemma max_topC_mvar [simp]:
  "max_topC (MVar x) = MVar x"
proof -
  have "Var x \<in> \<T>" by (simp add: \<T>_def)
  from max_top_not_hole[OF this] have "max_top (Var x) \<noteq> MHole" .
  then show ?thesis
  using max_topC_props(1)[unfolded topsC_def, of "mctxt_of_term (Var x)"]
  by (cases "max_top (Var x)") (auto elim: less_eq_mctxtE1)
qed

lemma max_top_var [simp]:
  "max_top (Var x) = MVar x"
  by simp

lemma max_top_var_subst:
  "max_top (t \<cdot> (Var \<circ> f)) = map_vars_mctxt f (max_top t)"
  using max_topC_props(1)[of "mctxt_of_term t"] max_topC_props(2)[of _ "mctxt_of_term t"]
  by (intro max_topCI) (auto simp del: max_topC_props max_topC_layer simp: topsC_def mctxt_of_term_var_subst
    intro: map_vars_mctxt_mono elim!: map_vars_mctxt_less_eq_decomp)

lemma aliens_var_subst:
  "aliens (t \<cdot> (Var \<circ> f)) = map (\<lambda>t. t \<cdot> (Var \<circ> f)) (aliens t)"
  unfolding max_top_var_subst by (auto intro: max_topC_prefix unfill_holes_var_subst)

lemma funas_term_subt_at:
  "p \<in> poss t \<Longrightarrow> f \<in> funas_term (subt_at t p) \<Longrightarrow> f \<in> funas_term t"
  by (induct t arbitrary: p) force+

lemma \<T>_subt_at:
  "t \<in> \<T> \<Longrightarrow> p \<in> poss t \<Longrightarrow> subt_at t p \<in> \<T>"
  using funas_term_subt_at[of p t] by (auto simp: \<T>_def)

text \<open>{cite \<open>Definition 3.6\<close> FMZvO15}: decomposing terms into max-top and aliens\<close>

lemma unfill_holes_max_top_subt:
  assumes "t \<in> \<T>" and "t' \<in> set (aliens t)"
  shows "t' \<lhd> t"
proof (cases t)
  note * = max_top_not_hole[OF assms(1)]
  have **: "max_top t \<le> mctxt_of_term t" using max_topC_props(1) by (simp add: topsC_def)
  {
    case (Var v) then have "max_top t = MVar v" using assms * **
    by (cases "max_top t") (auto simp: less_eq_mctxt_def topsC_def split: if_splits)
    then show ?thesis using assms(2) by (auto simp: Var)
  next
    note * = max_top_not_hole[OF assms(1)]
    case (Fun f ts)
    obtain Cs where l: "length Cs = length ts" and mt: "max_top t = MFun f Cs" using assms * **
    by (cases "max_top t") (auto simp: less_eq_mctxt_def topsC_def Fun split: if_splits)
    then obtain i where i: "i < length Cs" and "t' \<in> set (unfill_holes (Cs ! i) (ts ! i))"
    using assms(2) ** by (auto simp: Fun split: if_splits dest!: in_set_idx[of _ "zip Cs ts"])
    then have "t' \<unlhd> ts ! i" using **[unfolded mt, unfolded Fun]
    by (auto intro!: unfill_holes_subt[of "Cs !i" "ts ! i" t'] simp: less_eq_mctxt_def
      split: if_splits elim!: nth_equalityE)
    then show ?thesis using Fun i l set_supteq_into_supt[of "ts ! i" ts t' f] by simp
  }
qed

lemma unfill_holes_max_top_smaller [simp]:
  "t \<in> \<T> \<Longrightarrow> t' \<in> set (aliens t) \<Longrightarrow> size t' < size t"
  by (simp only: supt_size unfill_holes_max_top_subt)

lemma aliens_not_varC:
  "MVar v \<notin> set (aliensC C)"
proof
  let ?Cs = "aliensC C"
  assume "MVar v \<in> set ?Cs"
  then obtain i where *: "i < length ?Cs" "?Cs ! i = MVar v" by (auto simp: set_conv_nth)
  let ?Ds = "list_update (replicate (length ?Cs) MHole) i (MVar v)"
  let ?M' = "fill_holes_mctxt (max_topC C) ?Ds"
  have l: "length ?Ds = num_holes (max_topC C)" "max_topC C \<le> C"
    using max_topC_props(1)[of C, unfolded topsC_def] by simp_all
  have "set ?Ds \<subseteq> {MVar v, MHole}" using set_update_subset_insert[of "replicate (length ?Cs) MHole" i "MVar v"] by auto
  also have "... \<subseteq> insert MHole (range MVar)" by auto
  finally have "?M' \<in> \<LL>" using vars_to_holes_fill_holes_layer[of "max_topC C" ?Ds] l by auto
  moreover
  have "j < num_holes (max_topC C) \<Longrightarrow> ?Ds ! j \<le> ?Cs ! j" for j
    using * l by (cases "j = i") auto
  then have "?M' \<le> C"
    using less_eq_fill_holesI[of "?Ds" "max_topC C" ?Cs] * l by (auto simp: fill_unfill_holes_mctxt)
  moreover have "max_topC C \<le> ?M'" using fill_holes_mctxt_suffix[of ?Ds "max_topC C"] l
    by (simp del: fill_holes_mctxt_suffix)
  moreover have "max_topC C \<noteq> ?M'" using fill_holes_mctxt_id[OF l(1)] l \<open>i < length ?Cs\<close>
    set_update_memI[of i "replicate (length ?Cs) MHole" "MVar v"] by auto
  ultimately show False
    using max_topC_props(2)[of ?M' C] by (simp add: topsC_def del: max_topC_props length_unfill_holes_mctxt)
qed

lemma aliens_not_var:
  "Var v \<notin> set (aliens t)"
proof
  assume "Var v \<in> set (aliens t)"
  from imageI[OF this, of mctxt_of_term] aliens_not_varC[of v "mctxt_of_term t"]
    max_topC_props(1)[of "mctxt_of_term t", unfolded topsC_def] unfill_holes_mctxt_mctxt_of_term[of "max_top t" t]
  show False by auto
qed

text \<open>{cite \<open>Definition 3.6\<close> FMZvO15}: rank\<close>

fun rank :: "('f, 'v) term \<Rightarrow> nat" where
  [simp del]: "rank t = (if t \<in> \<T> then 1 + max_list (map rank (aliens t)) else 0)"

lemma rank_var:
  "rank (Var v) = 1"
  using rank.simps[of "Var v"] by (auto simp: \<T>_def)

lemma rank_var_subst:
  "rank (t \<cdot> (Var \<circ> f)) = rank t"
proof (induct t rule: rank.induct)
  case (1 t)
  { assume "t \<in> \<T>" note map_ext[OF 1[unfolded atomize_imp, THEN mp], OF this, unfolded comp_def] }
  note [simp] = this aliens_var_subst[unfolded comp_def] rank.simps[of t] rank.simps[of "t \<cdot> (\<lambda>t. Var (f t))"]
  show ?case by (cases "t \<in> \<T>") (auto simp: comp_def \<T>_def funas_term_subst)
qed

lemma unfill_by_itselfI [simp]:
  "unfill_holes (mctxt_of_term t) t = []"
  by (induct t) auto

lemma unfill_by_itselfD:
  "C \<le> mctxt_of_term t \<Longrightarrow> unfill_holes C t = [] \<Longrightarrow> C = mctxt_of_term t"
  by (induct C "mctxt_of_term t" arbitrary: t rule: less_eq_mctxt_induct; case_tac t)
    (auto intro: nth_equalityI)

lemma rank_gt_0:
  "t \<in> \<T> \<Longrightarrow> rank t > 0"
  by (subst rank.simps) auto

lemma rank_1:
  "rank t = 1 \<longleftrightarrow> mctxt_of_term t \<in> \<LL>"
proof (standard, goal_cases)
  case 1
  then have "aliens t = []" using supt_imp_funas_term_subset[OF unfill_holes_max_top_subt[of t]]
    rank_gt_0[of "hd (aliens t)"]
    by (subst (asm) rank.simps, cases "aliens t") (fastforce split: if_splits simp: \<T>_def)+
  then have "aliens t = []" by (cases "aliens t") auto
  then show ?case using max_top_layer[of t]
    by (auto dest!: unfill_by_itselfD[OF max_topC_prefix] simp del: max_topC_layer)
next
  case 2 then have "max_top t = mctxt_of_term t"
    by (simp add: dual_order.antisym max_topC_prefix topsC_def)
  then show ?case using subsetD[OF \<LL>_sig max_top_layer[of t]]
    by (subst rank.simps) (auto simp del: max_topC_layer simp: \<T>_def \<C>_def)
qed

text \<open>{cite \<open>Lemma 3.8\<close> FMZvO15}\<close>

lemma rank_by_top':
  assumes "t \<in> \<T>" and "L \<le> max_top t"
  shows "rank t \<le> 1 + max_list (map rank (filter is_Fun (unfill_holes L t)))"
proof -
  let ?rank' = "\<lambda>t. if is_Var t then 0 else rank t"
  have [simp]: "map ?rank' (aliens t) = map rank (aliens t)" for t by (auto simp: aliens_not_var)
  have ml: "max_list (map rank (filter is_Fun ts)) = max_list (map ?rank' ts)" for ts
    by (induct ts) auto
  let ?r = "{ (C,D) . C > D } \<inter> {N. N \<le> max_top t} \<times> {N. N \<le> max_top t}"
  show ?thesis unfolding ml using assms
  proof (induct L rule: wf_induct[of ?r])
    have "finite ?r" by (simp add: finite_pre_mctxt[of "max_top t"])
    moreover have "trans ?r" by (auto simp: trans_def)
    ultimately show "wf ?r" by (auto simp: wf_iff_acyclic_if_finite acyclic_def)
  next
    case (2 C)
    {
      fix D assume "C \<le> D" "D \<le> mctxt_of_term t" "t \<in> \<T>"
      then have "C = D \<or> C < fill_holes_mctxt C (map max_top (unfill_holes C t)) \<sqinter> D"
      proof (induct C arbitrary: D t)
        case MHole
        moreover have "max_top t \<le> mctxt_of_term t"
          using max_topC_props[of "mctxt_of_term t"] by (auto simp: topsC_def)
        ultimately show ?case using max_top_not_hole[of t]
          by (cases D; cases "max_top t"; cases t, auto
            simp: less_mctxt_def mctxt_order_bot.bot_unique less_eq_mctxt_def split: if_splits)
      next
        case (MVar v) then show ?case by (cases D, auto simp: less_eq_mctxt_def split: if_splits)
      next
        case (MFun f Cs)
        obtain Ds where Ds: "D = MFun f Ds" "length Ds = length Cs"
          using MFun(2) by (cases D) (auto simp: less_eq_mctxt_def split: if_splits)
        obtain ts where ts: "t = Fun f ts" "length ts = length Cs"
          using MFun Ds by (cases t) (auto simp: less_eq_mctxt_def split: if_splits)
        {
          fix i assume i: "i < length Cs"
          thm MFun(1)[OF nth_mem, of n "Ds ! n" "ts ! n" for n]
          have *: "ts ! i \<in> \<T>" using MFun(4) nth_mem[OF i[unfolded ts(2)[symmetric]]]
            by (auto simp: ts \<T>_def dest!: subsetD)
          have "Cs ! i \<le> Ds ! i" "Ds ! i \<le> mctxt_of_term (ts ! i)"
            using i MFun(2,3) by (auto simp: Ds ts less_eq_mctxt_def elim!: nth_equalityE)
          then have **: "Cs ! i \<le> mctxt_of_term (ts ! i)" by simp
          have "Cs ! i = Ds ! i \<or> Cs ! i < fill_holes_mctxt (Cs ! i) (map max_top (unfill_holes (Cs ! i) (ts ! i))) \<sqinter> Ds ! i"
            "length (map max_top (unfill_holes (Cs ! i) (ts ! i))) = num_holes (Cs ! i)"
            using MFun(2-4) Ds ts i
            by (intro MFun(1))
               (auto simp: length_unfill_holes[OF **] \<T>_def set_conv_nth less_mctxt_def
                 dest!: subsetD elim!: nth_equalityE elim: less_eq_mctxtE1)
        } note * = this
        show ?case
          using * arg_cong[of _ _ "map (map max_top)", OF partition_by_concat_id[of "map (\<lambda>i. unfill_holes (Cs ! i) (ts ! i)) [0..<length Cs]" "map num_holes Cs"]]
          apply (auto simp: less_mctxt_def Ds ts map_map_partition_by map_concat intro!: nth_equalityI less_eq_mctxtI1 elim!: nth_equalityE elim: less_eq_mctxtE1)
          apply (metis preorder_class.eq_refl)
        done
      qed
    } note * = this
    let ?C' = "fill_holes_mctxt C (map max_top (unfill_holes C t)) \<sqinter> max_top t"
    have "C = max_top t \<or> C < ?C'"
    using 2(2-3) max_topC_props[of "mctxt_of_term t", unfolded topsC_def] by (intro *) (auto)
    moreover
    have leq: "C \<le> ?C'" using 2(3) max_topC_props[of "mctxt_of_term t", unfolded topsC_def]
      by (auto intro!: fill_holes_mctxt_suffix)
    have "C \<le> mctxt_of_term t" using \<open>C \<le> max_top t\<close> max_topC_props[of "mctxt_of_term t", unfolded topsC_def]
      by auto
    have "?C' \<le> mctxt_of_term t" using max_topC_props[of "mctxt_of_term t", unfolded topsC_def]
      by (auto intro: inf.coboundedI2)
    {
      fix i assume *: "i < num_holes C" define p where "p = hole_poss' C ! i"
      have "p \<in> all_poss_mctxt C"
        using * set_hole_poss'[of C] by (fastforce simp: all_poss_mctxt_conv p_def)
      then have **: "p \<in> all_poss_mctxt ?C'" using \<open>C \<le> ?C'\<close> all_poss_mctxt_mono[of C "?C'"] by auto
      have ***: "length (map max_top (unfill_holes C t)) = num_holes C" and
           ****: "length (unfill_holes C t) = num_holes C" using \<open>C \<le> mctxt_of_term t\<close> by auto
      have *****: "subm_at ?C' p = max_top (subt_at t p) \<sqinter> subm_at (max_top t) p"
        using inf_subm_at[OF **] * nth_map[of _ "unfill_holes C t"] **** \<open>C \<le> mctxt_of_term t\<close>
        by (simp add: p_def subm_at_fill_holes_mctxt[OF ***]) (simp add: unfill_holes_conv)
      have "p \<in> all_poss_mctxt (max_top t)" using \<open>p \<in> all_poss_mctxt C\<close> \<open>C \<le> max_top t\<close>
          all_poss_mctxt_mono[of C "max_top t"] by auto
      have urk: "p \<in> all_poss_mctxt (mreplace_at (max_top t) p (subm_at (max_top t) p \<squnion> max_top (t |_ p)))"
        using \<open>p \<in> all_poss_mctxt (max_top t)\<close> by (auto intro: all_poss_mctxt_mreplace_atI1)
      have "subm_at ?C' p = MHole \<or> subm_at ?C' p = max_top (subt_at t p)"
      proof (cases "p \<in> hole_poss (max_top t)")
        case True then show ?thesis unfolding ***** by auto
      next
        case False
        have pmt: "p \<in> poss_mctxt (max_top t)"
          using \<open>p \<in> all_poss_mctxt (max_top t)\<close> False by (auto simp: all_poss_mctxt_conv)
        have comp: "(subm_at (max_top t) p, max_top (subt_at t p)) \<in> comp_mctxt"
        proof (intro prefix_comp_mctxt[of _ "mctxt_of_term (subt_at t p)"])
          show "subm_at (max_top t) p \<le> mctxt_of_term (t |_ p)"
            apply (subst subm_at_mctxt_of_term[symmetric])
            using pmt max_topC_props[unfolded topsC_def] all_poss_mctxt_mono[of "max_top t" "mctxt_of_term t"]
            apply (auto intro: less_eq_subm_at simp: all_poss_mctxt_conv)
          done
        qed (insert max_topC_props[unfolded topsC_def], auto)
        then have "mreplace_at (max_top t) p (subm_at (max_top t) p \<squnion> max_top (t |_ p)) \<in> \<LL>"
          by (intro L\<^sub>3') (insert max_topC_props[unfolded topsC_def] pmt, auto)
        moreover have "mreplace_at (max_top t) p (subm_at (max_top t) p \<squnion> max_top (t |_ p)) \<le> mctxt_of_term t"
          using \<open>p \<in> all_poss_mctxt (max_top t)\<close> max_topC_props[unfolded topsC_def] all_poss_mctxt_mono[of "max_top t" "mctxt_of_term t"]
          apply (intro mreplace_at_leqI)
          subgoal by auto
          subgoal by auto
          subgoal apply (intro sup_mctxt_least[OF comp])
            subgoal by (auto intro: less_eq_subm_at)
            subgoal by (subst subm_at_mctxt_of_term[symmetric]) (auto simp: all_poss_mctxt_conv intro: less_eq_subm_at)
          done
        done
        ultimately have "mreplace_at (max_top t) p (subm_at (max_top t) p \<squnion> max_top (t |_ p)) \<le> max_top t"
          using max_topC_props[unfolded topsC_def] by auto
        from less_eq_subm_at[OF _ this, of p]
        have "max_top (t |_ p) \<sqinter> subm_at (max_top t) p = max_top (t |_ p)"
          unfolding subm_at_mreplace_at[OF \<open>p \<in> all_poss_mctxt (max_top t)\<close>] less_eq_mctxt_def[symmetric]
          using sup_mctxt_ge2[OF comp] urk by simp
        then show ?thesis unfolding ***** by simp
      qed
    } note x = this
    {
      fix i assume "i < num_holes C"
      then have "hole_poss' C ! i \<in> hole_poss C" using set_hole_poss'[of C]
        unfolding length_hole_poss'[symmetric] by force
      then have "hole_poss' C ! i \<in> all_poss_mctxt C" by (auto simp: all_poss_mctxt_conv)
      then have "hole_poss' C ! i \<in> poss t" using \<open>C \<le> mctxt_of_term t\<close>
         all_poss_mctxt_mono[of C "mctxt_of_term t"] by (auto simp: all_poss_mctxt_conv)
      then have "t |_ hole_poss' C ! i \<in> \<T>" using \<open>t \<in> \<T>\<close> by (simp add: \<T>_subt_at)
    } note y = this
    have "max_list (map ?rank' (unfill_holes ?C' t)) \<le> max_list (map ?rank' (unfill_holes C t))"
      unfolding unfill_holes_by_prefix[OF \<open>C \<le> ?C'\<close> \<open>?C' \<le> mctxt_of_term t\<close>] map_concat
      using \<open>C \<le> mctxt_of_term t\<close>
    apply (intro max_list_mono_concat1)
      subgoal by auto
      subgoal for i using x[of i] by (auto simp: unfill_holes_conv rank.simps y)
    done
    ultimately show ?case using spec[OF 2(1), of ?C'] 2(2) 2(3) by auto (auto simp: rank.simps)
  qed
qed

lemma rank_by_top:
  assumes "t \<in> \<T>" and "L \<le> max_top t"
  shows "rank t \<le> 1 + max_list (map rank (unfill_holes L t))"
proof -
  have "max_list (map rank (filter is_Fun (unfill_holes L t))) \<le> max_list (map rank (unfill_holes L t))"
    by (auto intro!: max_list_mono)
  then show ?thesis using rank_by_top'[OF assms] by simp
qed

end (* layer_system *)

text \<open>Layered TRSs are also weakly layered.\<close>

sublocale layered \<subseteq> weakly_layered
  by (unfold_locales) (fact trs, fact \<R>_sig, metis C\<^sub>1 max_topC_layer mhole_layer)

text \<open>{cite \<open>Lemma 3.9\<close> FMZvO15}\<close>

lemma (in weakly_layered) \<LL>_closed_under_\<R>:
  assumes "L \<in> \<LL>" and "(L, N) \<in> mrstep \<R>" shows "N \<in> \<LL>"
proof -
  let ?f = "\<lambda>t. holes_to_var (term_mctxt_conv t)" and ?sf = "case_option (Var undefined) Var"
  have sf: "?f t = t \<cdot> ?sf" for t by (induct t rule: term_mctxt_conv.induct) auto
  let ?g = "\<lambda>t. mctxt_term_conv (vars_to_holes' (term_mctxt_conv t))" and ?sg = "\<lambda>x. Var None"
  have sg: "?g t = t \<cdot> ?sg" for t by (induct t rule: term_mctxt_conv.induct) auto
  let ?h = "\<lambda>t. mctxt_term_conv (vars_to_holes' (mctxt_of_term t))" and ?sh = "\<lambda>x. Var None"
  have sh: "?h t = t \<cdot> ?sh" for t by (induct t) auto
  have "(?f (mctxt_term_conv L), ?f (mctxt_term_conv N)) \<in> rstep' \<R>"
    using assms(2) by (auto simp only: sf rstep'_stable mrstep.simps)
  then obtain r p \<sigma> where 2: "(?f (mctxt_term_conv L), ?f (mctxt_term_conv N)) \<in> rstep_r_p_s' \<R> r p \<sigma>"
    by (auto simp: rstep'_iff_rstep_r_p_s')
  then obtain C where "?f (mctxt_term_conv L) = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "p = hole_pos C" "r \<in> \<R>"
    using 2 by (auto simp: rstep_r_p_s'.simps)
  then have **: "p \<in> fun_poss_mctxt L" unfolding fun_poss_mctxt_def
  proof (induct C arbitrary: p L)
    case Hole then show ?case using trs by (cases r; cases L; force simp: wf_trs_def)
  next
    case (More f ss1 C ss2) then show ?case by (cases L) (auto elim: nth_equalityE)
  qed
  have fL: "funas_term (mctxt_term_conv L) \<subseteq> \<F>" using assms(1) \<LL>_sig by (auto simp: \<T>_def \<C>_def)
  from rstep'_preserves_funas_terms[OF \<R>_sig this] trs assms(2)[unfolded mrstep.simps]
  have fN: "funas_term (mctxt_term_conv N) \<subseteq> \<F>" by blast
  have "L \<in> tops (?f (mctxt_term_conv L))" using assms(1) by (simp add: topsC_def)
  then have Mbounds: "L \<le> max_top (?f (mctxt_term_conv L))"
    "max_top (?f (mctxt_term_conv L)) \<le> mctxt_of_term (?f (mctxt_term_conv L))"
    using max_topC_props by (auto simp: topsC_def)
  with ** have 1: "p \<in> fun_poss_mctxt (max_top (?f (mctxt_term_conv L)))" by (simp add: fun_poss_mctxt_mono)
  have "holes_to_var L \<in> \<T>" "holes_to_var N \<in> \<T>" using fL fN by (auto simp: \<T>_def)
  then obtain D \<tau> where "D \<in> \<LL>" "(mctxt_term_conv (max_top (?f (mctxt_term_conv L))), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> r p \<tau>"
    using W[OF _ _ 1 2] by auto
  then have "(?g (mctxt_term_conv (max_top (?f (mctxt_term_conv L)))), ?g (mctxt_term_conv D)) \<in> rstep_r_p_s' \<R> r p (\<tau> \<circ>\<^sub>s ?sg)"
    unfolding sg by (auto simp: rstep_r_p_s'.simps)
  moreover have "?g (mctxt_term_conv (max_top (?f (mctxt_term_conv L)))) = ?g (mctxt_term_conv L)"
    using vars_to_holes'_mono[OF Mbounds(1)] vars_to_holes'_mono[OF Mbounds(2)] by simp
  ultimately have 3: "(mctxt_term_conv (vars_to_holes L), mctxt_term_conv (vars_to_holes' D)) \<in> rstep_r_p_s' \<R> r p (\<tau> \<circ>\<^sub>s ?sg)"
    by simp
  have "(?h (holes_to_var (term_mctxt_conv (mctxt_term_conv L))), ?h (holes_to_var (term_mctxt_conv (mctxt_term_conv N)))) \<in> rstep_r_p_s' \<R> r p (\<sigma> \<circ>\<^sub>s ?sh)"
    using 2 unfolding sh by (auto simp: rstep_r_p_s'.simps)
  then have 4: "(mctxt_term_conv (vars_to_holes L), mctxt_term_conv (vars_to_holes' N)) \<in> rstep_r_p_s' \<R> r p (\<sigma> \<circ>\<^sub>s ?sh)"
    by simp
  show ?thesis using arg_cong[OF rstep_r_p_s'_deterministic[OF trs 3 4], of term_mctxt_conv] \<open>D \<in> \<LL>\<close>
    vars_to_holes_layer[of D] vars_to_holes_layer[of N] by simp
qed

lemma fresh_variables_for_holes:
  fixes C :: "('f, 'v :: infinite) mctxt"
  obtains xs where "num_holes C = length xs" "distinct xs" "set xs \<inter> vars_mctxt C = {}"
  using infinite_UNIV infinite_imp_many_elems[of "UNIV - vars_mctxt C" "num_holes C"]
    sym[of "length _" "num_holes C"] by auto

lemma represent_context_by_term:
  fixes C :: "('f, 'v :: infinite) mctxt"
  obtains c \<sigma> where
    "c \<cdot> \<sigma> = mctxt_term_conv C" "\<And>x. \<sigma> x \<in> {Var (Some x), Var None}"
    "\<And>D. C \<le> D \<Longrightarrow> \<exists>\<tau>. c \<cdot> \<tau> = mctxt_term_conv D \<and> (\<forall>x. \<sigma> x = Var None \<or> \<tau> x = Var (Some x))"
proof -
  obtain xs where *: "num_holes C = length xs" "distinct xs" "set xs \<inter> vars_mctxt C = {}"
    using fresh_variables_for_holes .
  define X where "X = set xs"
  let ?c = "fill_holes C (map Var xs)"
  let ?\<sigma> = "\<lambda>x. if x \<in> set xs then Var None else Var (Some x)"
  from *(1,3) have "?c \<cdot> ?\<sigma> = mctxt_term_conv C"
    unfolding X_def[symmetric] using equalityD2[OF X_def]
  proof (induct C xs rule: fill_holes_induct)
    case (MFun f Cs xs)
    have "i < length Cs \<Longrightarrow> X \<inter> vars_mctxt (Cs ! i) = {}" for i using MFun(3) by fastforce
    moreover have "i < length Cs \<Longrightarrow> set (partition_holes xs Cs ! i) \<subseteq> X" for i using MFun(4) by fastforce
    ultimately show ?case using MFun(1,2) by (auto simp: comp_def map_nth_eq_conv)
  qed auto
  moreover have "?\<sigma> x \<in> {Var (Some x), Var None}" for x by simp
  moreover from * have "C \<le> D \<Longrightarrow> \<exists>\<tau>. ?c \<cdot> \<tau> = mctxt_term_conv D \<and> (\<forall>x. x \<in> set xs \<and> ?\<sigma> x = Var None \<or> \<tau> x = Var (Some x))" for D
  proof (induct C xs arbitrary: D rule: fill_holes_induct)
    case (MHole x) then show ?case by (intro exI[of _ "(Var \<circ> Some) (x := mctxt_term_conv D)"]) auto
  next
    case (MVar x) then show ?case by (intro exI[of _ "Var \<circ> Some"]) (auto elim: less_eq_mctxtE1)
  next
    case (MFun f Cs xs)
    from MFun(3) obtain Ds where [simp]: "D = MFun f Ds" "length Ds = length Cs"
      and **: "\<And>i. i < length Cs \<Longrightarrow> Cs ! i \<le> Ds ! i"
      by (metis less_eq_mctxtE1(2))
    have x: "i < length Cs \<Longrightarrow> mset (partition_holes xs Cs ! i) \<subseteq># mset (concat (partition_holes xs Cs))" for i
      using nth_mem_mset[of i "partition_holes xs Cs"]
      by (auto simp: mset_concat_union in_mset_subset_Union)
    have distinct: "i < length Cs \<Longrightarrow> distinct (partition_holes xs Cs ! i)" for i using x MFun(4)
      by (auto simp: distinct_count_atmost_1' mset_concat_union) (meson dual_order.trans subseteq_mset_def)
    moreover have "i < length Cs \<Longrightarrow> set (partition_holes xs Cs ! i) \<inter> vars_mctxt (MFun f Cs) = {}" for i
      using x MFun(5) nth_mem[of i "partition_holes xs Cs"] by (auto simp del: nth_mem)
    then have disjoint: "i < length Cs \<Longrightarrow> set (partition_holes xs Cs ! i) \<inter> vars_mctxt (Cs ! i) = {}" for i
      using nth_mem[of i "Cs"] by (auto simp del: nth_mem)
    ultimately have "i < length Cs \<Longrightarrow>
       \<exists>\<tau>. fill_holes (Cs ! i) (map Var (partition_holes xs Cs ! i)) \<cdot> \<tau> = mctxt_term_conv (Ds ! i) \<and>
       (\<forall>x. x \<in> set (partition_holes xs Cs ! i) \<or> \<tau> x = Var (Some x))" for i
      using MFun(2)[OF _ **] by meson
    then obtain \<tau>s where \<tau>s: "\<And>i. i < length Cs \<Longrightarrow>
      fill_holes (Cs ! i) (map Var (partition_holes xs Cs ! i)) \<cdot> \<tau>s i = mctxt_term_conv (Ds ! i) \<and>
      (\<forall>x. x \<in> set (partition_holes xs Cs ! i) \<or> \<tau>s i x = Var (Some x))" by metis
    define \<tau> where "\<tau> \<equiv> \<lambda>x. (if x \<in> set xs then \<tau>s (THE i. i < length Cs \<and> x \<in> set (partition_holes xs Cs ! i)) x else Var (Some x))"
    have "i < length Cs \<Longrightarrow> \<forall>x. x \<in> vars_mctxt (Cs ! i) \<longrightarrow> \<tau> x = Var (Some x)" for i
      using set_mset_mono[OF x[of i]] MFun(1,5) nth_mem[of i "Cs"] by (auto simp: \<tau>_def simp del: nth_mem)
    note [simp] = subst_apply_mctxt_cong[OF this]
    have "i < length Cs \<Longrightarrow> \<forall>x. x \<in> vars_mctxt (Cs ! i) \<longrightarrow> \<tau>s i x = Var (Some x)" for i
      using set_mset_mono[OF x[of i]] MFun(1,5) nth_mem[of i "Cs"] \<tau>s by (auto simp del: nth_mem)
    note [simp] = subst_apply_mctxt_cong[OF this]
    have "i < length Cs \<Longrightarrow> x \<in> set (partition_holes xs Cs ! i) \<Longrightarrow>
      (THE i. i < length Cs \<and> x \<in> set (partition_holes xs Cs ! i)) = i" for i x
      using MFun(4) by (intro the_equality) (auto simp: distinct_concat_unique_index)
    then have "i < length Cs \<Longrightarrow> x \<in> set (partition_holes xs Cs ! i) \<Longrightarrow> \<tau> x = \<tau>s i x" for i x
      using set_mset_mono[OF x[of i]] MFun(1) by (auto simp add: \<tau>_def)
    then have [simp]: "i < length Cs \<Longrightarrow> partition_holes (map ((\<lambda>ti. ti \<cdot> \<tau>) \<circ> Var) xs) Cs ! i =
      partition_holes (map ((\<lambda>ti. ti \<cdot> \<tau>s i) \<circ> Var) xs) Cs ! i" for i
      unfolding map_map_partition_by[symmetric] nth_map[of _ "partition_holes xs Cs", unfolded length_map length_partition_by]
      by (intro map_cong) (auto simp: \<tau>_def)
    from MFun(1,3,4,5) \<tau>s show ?case
      by (intro exI[of _ \<tau>] conjI)
         (auto simp: distinct disjoint subst_apply_mctxt_fill_holes intro!: nth_equalityI, auto simp: \<tau>_def)
  qed
  then have "C \<le> D \<Longrightarrow> \<exists>\<tau>. ?c \<cdot> \<tau> = mctxt_term_conv D \<and> (\<forall>x. ?\<sigma> x = Var None \<or> \<tau> x = Var (Some x))" for D
     by blast
  ultimately show ?thesis ..
qed

text \<open>{cite \<open>Lemma 3.10\<close> FMZvO15}\<close>

lemma matched_mctxt_to_term:
  fixes C :: "('f, 'v :: infinite) mctxt" and l :: "('f, 'w) term"
  assumes "p \<in> all_poss_mctxt C" "l \<cdot> \<sigma> = mctxt_term_conv (subm_at C p)"
  obtains c :: "('f, 'v) term" and \<rho> \<rho>' where "mctxt_term_conv C = c \<cdot> \<rho>" "\<And>x. x \<in> vars_term c \<Longrightarrow> is_Var (\<rho> x)"
    "p \<in> poss c" "l \<cdot> \<rho>' = subt_at c p"
    "\<And>D \<tau>. C \<le> D \<Longrightarrow> l \<cdot> \<tau> = mctxt_term_conv (subm_at D p) \<Longrightarrow>
      \<exists>\<tau>'. (c \<cdot> \<tau>' = mctxt_term_conv D)"
proof -
  obtain w_to_v :: "'w \<Rightarrow> 'v" where *: "inj_on w_to_v (vars_term l)"
    using inj_on_iff_card_le[of "vars_term l"] infinite_arbitrarily_large[OF infinite_UNIV, of "card (vars_term l)"]
      by fastforce
  have [simp]: "l \<cdot> (Var \<circ> w_to_v) \<cdot> (\<sigma> \<circ> inv_into (vars_term l) w_to_v) = l \<cdot> \<sigma>" for \<sigma> using *
    by (auto simp del: subst_subst_compose simp: subst_subst subst_compose_def term_subst_eq_conv)
  let ?l = l and ?\<sigma> = \<sigma>
  define \<sigma> where "\<sigma> = ?\<sigma> \<circ> inv_into (vars_term l) w_to_v"
  define l where "l = ?l \<cdot> (Var \<circ> w_to_v)"
  have assms: "p \<in> all_poss_mctxt C" "l \<cdot> \<sigma> = mctxt_term_conv (subm_at C p)"
    using assms by (auto simp: l_def \<sigma>_def)
  from represent_context_by_term[of C]
  obtain c0 \<tau> where 1: "c0 \<cdot> \<tau> = mctxt_term_conv C" "\<And>x. \<tau> x \<in> {Var (Some x), Var None}"
    "\<And>D. C \<le> D \<Longrightarrow> \<exists>\<tau>'. c0 \<cdot> \<tau>' = mctxt_term_conv D \<and> (\<forall>x. \<tau> x = Var None \<or> \<tau>' x = Var (Some x))" by blast
  from 1(1,2) have p: "poss c0 = all_poss_mctxt C"
  proof (induct c0 arbitrary: C)
    case (Var x) show ?case using Var(2)[of x] Var(1) by (cases C) auto
  next
    case (Fun f cs) then show ?case by (cases C) (auto simp: map_eq_conv')
  qed
  from term_fs.rename_avoiding[unfolded supp_vars_term_eq, OF finite_vars_term]
  obtain \<pi> l' where 2: "l' = \<pi> \<bullet> l" "vars_term c0 \<inter> vars_term l' = {}" by (metis term_apply_subst_Var_Rep_perm)
  have l_sop: "l' = l \<cdot> sop \<pi>" using 2(1) by simp
  let ?d = "replace_at c0 p l'" and ?\<rho> = "\<lambda>x . if x \<in> vars_term l' then (\<sigma> \<circ> Rep_perm (- \<pi>)) x else \<tau> x"
  have C1: "mctxt_term_conv C = c0 \<cdot> ?\<rho>"
    unfolding 1(1)[symmetric] using 2(2) by (intro term_subst_eq) auto
  have l': "l' \<cdot> ?\<rho> = l \<cdot> \<sigma>" unfolding 2(1) permute_term_subst_apply_term using 2(2) Rep_perm_image[of "\<pi>" "vars_term l"]
    by (intro term_subst_eq) (auto simp: 2(1) eqvt fun_cong[OF Rep_perm_add[unfolded o_def, symmetric]] Rep_perm_0 image_def)
  have C2: "mctxt_term_conv C = replace_at c0 p l' \<cdot> ?\<rho>" unfolding 1(1)[symmetric]
    using cong[OF refl ctxt_supt_id[OF assms(1)[unfolded p[symmetric]]], of "\<lambda>x. x \<cdot> ?\<rho>", symmetric]
    by (auto simp: l' assms(2) 1(1) C1[symmetric] subt_at_mctxt_term_conv[OF assms(1)]
      subt_at_subst[symmetric, OF assms(1)[unfolded p[symmetric]]])
  have "c0 \<cdot> ?\<rho> \<circ>\<^sub>s (Var \<circ> from_option) = ?d \<cdot> ?\<rho> \<circ>\<^sub>s (Var \<circ> from_option)" using C2 by (auto simp: unifiers_def C1)
  note m = is_imgu_imp_is_mgu[OF the_mgu_is_imgu[OF this]] and t = the_mgu[OF this] and i = the_mgu_is_imgu[OF this]
  let ?\<mu> = "the_mgu c0 ?d"
  let ?c = "c0 \<cdot> ?\<mu>"
  from arg_cong[OF arg_cong[OF conjunct2[OF t,symmetric], of "\<lambda>\<sigma>. c0 \<cdot> \<sigma>", folded subst_subst, folded C1], of "\<lambda>t. t \<cdot> (Var \<circ> to_option)"]
    have ***: "mctxt_term_conv C = ?c \<cdot> ?\<rho>"
    by (simp del: subst_subst_compose add: subst_subst subst_compose_def)
  moreover {
    fix x assume "x \<in> vars_term ?c"
    then obtain z where "z \<in> vars_term c0" "x \<in> vars_term (?\<mu> z)" by (auto simp: vars_term_subst)
    then have "is_Var (?\<rho> x)"
    using bspec[OF 1(1)[unfolded *** subst_subst term_subst_eq_conv], of z] 1(2)[of z]
      by (cases "the_mgu c0 (ctxt_of_pos_term p c0)\<langle>l'\<rangle> z", auto simp: subst_compose_def)
  }
  moreover have "p \<in> poss ?c" using assms(1)[folded p] by simp
  moreover have "p \<in> poss ?d" using assms(1)[folded p] by (simp add: replace_at_below_poss)
  then have "l \<cdot> (sop \<pi> \<circ>\<^sub>s ?\<mu>) = subt_at ?c p" using l_sop[symmetric] assms(1)[folded p]
    by (simp only: conjunct1[OF t] subt_at_subst replace_at_subt_at) simp
  then have "?l \<cdot> ((sop \<pi> \<circ>\<^sub>s ?\<mu>) \<circ> w_to_v) = subt_at ?c p"
    by (auto simp del: subst_subst_compose simp: subst_subst subst_compose_def comp_def l_def)
  moreover {
    fix D \<tau>'' assume assms': "C \<le> D" "?l \<cdot> \<tau>'' = mctxt_term_conv (subm_at D p)"
    define \<tau>' where "\<tau>' = \<tau>'' \<circ> inv_into (vars_term ?l) w_to_v"
    have assms': "C \<le> D" "l \<cdot> \<tau>' = mctxt_term_conv (subm_at D p)"
      using assms' by (auto simp: l_def \<tau>'_def)
    from assms(1) assms'(1) have pp: "p \<in> all_poss_mctxt D" using all_poss_mctxt_mono by auto
    from 1(3)[OF assms'(1)] obtain \<tau>'' where 4: "c0 \<cdot> \<tau>'' = mctxt_term_conv D"
      "\<And>x. \<tau> x = Var None \<or> \<tau>'' x = Var (Some x)" by blast
    let ?\<tau> = "\<lambda>x . if x \<in> vars_term l' then (\<tau>' \<circ> Rep_perm (- \<pi>)) x else \<tau>'' x"
    have D1: "mctxt_term_conv D = c0 \<cdot> ?\<tau>"
      unfolding 4(1)[symmetric] using 2(2) by (intro term_subst_eq) auto
    have l': "l' \<cdot> ?\<tau> = l \<cdot> \<tau>'" unfolding 2(1) permute_term_subst_apply_term using 2(2) Rep_perm_image[of "\<pi>" "vars_term l"]
      by (intro term_subst_eq) (auto simp: 2(1) eqvt fun_cong[OF Rep_perm_add[unfolded o_def, symmetric]] Rep_perm_0 image_def)
    have D2: "mctxt_term_conv D = replace_at c0 p l' \<cdot> ?\<tau>" unfolding 4(1)[symmetric]
      using cong[OF refl ctxt_supt_id[OF assms(1)[unfolded p[symmetric]]], of "\<lambda>x. x \<cdot> ?\<tau>", symmetric]
      by (auto simp: l' assms'(2) 4 D1[symmetric] subt_at_mctxt_term_conv[OF pp]
        subt_at_subst[symmetric, OF assms(1)[unfolded p[symmetric]]])
    note * = trans[OF sym[OF D1] D2]
    obtain \<tau>2 where foo: "?\<tau> \<circ>\<^sub>s (Var \<circ> from_option) = ?\<mu> \<circ>\<^sub>s \<tau>2"
      using cong[OF refl *, of "\<lambda>t. t \<cdot> (Var \<circ> from_option)"] unfolding subst_subst by (blast dest: the_mgu)
    have bibi: "(Var \<circ> from_option) \<circ>\<^sub>s (Var \<circ> to_option) = (Var :: 'v option \<Rightarrow> ('f,'v option) term)"
      by (auto simp: subst_compose_def)
    then have "c0 \<cdot> ?\<tau> = c0 \<cdot> ?\<tau> \<cdot> (Var \<circ> from_option) \<circ>\<^sub>s (Var \<circ> to_option)" by simp
    then have "?c \<cdot> \<tau>2 \<circ>\<^sub>s (Var \<circ> to_option) = mctxt_term_conv D" by (metis (no_types, lifting) D1 foo subst_subst)
    then have "\<exists>\<tau>'. ?c \<cdot> \<tau>' = mctxt_term_conv D" by blast
  }
  ultimately show ?thesis ..
qed

lemma alien_set_by_substitution:
  fixes c :: "('f, 'v) term" and C :: "('f, 'v) mctxt"
  assumes "mctxt_term_conv C = c \<cdot> \<rho>" "\<And>x. x \<in> vars_term c \<Longrightarrow> is_Var (\<rho> x)"
    "num_holes C = length ts" "fill_holes C ts = c \<cdot> \<tau>"
  shows "set ts = { \<tau> x |x. x \<in> vars_term c \<and> \<rho> x = Var None }"
using assms(3,1,2,4)
proof (induct C ts arbitrary: c rule: fill_holes_induct)
  case (MHole t) then show ?case by (cases c) auto
next
  case (MVar x) then show ?case by (cases c) auto
next
  case (MFun f Cs ts)
  obtain cs where x[simp]: "length Cs = length cs" "c = Fun f cs"
    using MFun(3,4) by (cases c) (auto, metis length_map)
  have "i < length cs \<Longrightarrow> set (partition_holes ts Cs ! i) = {\<tau> x |x. x \<in> vars_term (cs ! i) \<and> \<rho> x = Var None}" for i
    using MFun(1,3-) by (intro MFun(2)) (auto simp: map_eq_conv' set_conv_nth)
  then show ?case unfolding set_concat unfolding x term.set(4)
    by (subst set_conv_nth)+ (simp, blast)
qed

lemma alien_map_by_substitution:
  fixes c :: "('f, 'v) term" and C :: "('f, 'v) mctxt"
  assumes "mctxt_term_conv C = c \<cdot> \<rho>" "\<And>x. x \<in> vars_term c \<Longrightarrow> is_Var (\<rho> x)"
    "num_holes C = length ts" "fill_holes C ts = c \<cdot> \<tau>"
  shows "fill_holes C (map f ts) = c \<cdot> (\<lambda>x. if \<rho> x = Var None then f (\<tau> x) else \<tau> x)"
  using assms(3,1,2,4)
proof (induct C ts arbitrary: c rule: fill_holes_induct)
  case (MHole t) then show ?case by (cases c) auto
next
  case (MVar x) then show ?case by (cases c) auto
next
  case (MFun g Cs ts)
  obtain cs where x[simp]: "length Cs = length cs" "c = Fun g cs"
    using MFun(3,4) by (cases c) (auto, metis length_map)
  have "i < length cs \<Longrightarrow> fill_holes (Cs ! i) (partition_holes (map f ts) Cs ! i) =
      cs ! i \<cdot> (\<lambda>x. if \<rho> x = Var None then f (\<tau> x) else \<tau> x)" for i
      using MFun(1,2,3,5) MFun(4)[unfolded x term.set, OF UN_I, of "cs ! i"] by (auto elim!: nth_equalityE)
  then show ?case using MFun(1) by (auto intro!: nth_equalityI)
qed

lemma leq_mctxt_subst:
  shows "term_mctxt_conv (c \<cdot> \<rho>) \<le> term_mctxt_conv (c \<cdot> \<tau>) \<longleftrightarrow>
    (\<forall>x. x \<in> vars_term c \<longrightarrow> term_mctxt_conv (\<rho> x) \<le> term_mctxt_conv (\<tau> x))"
  by (induct c) (auto elim!: less_eq_mctxtE1 intro!: less_eq_mctxtI1 simp: set_conv_nth, blast+)

lemma leq_mctxt_vars_term_subst:
  assumes "vars_term d \<subseteq> vars_term c" "term_mctxt_conv (c \<cdot> \<rho>) \<le> term_mctxt_conv (c \<cdot> \<tau>)"
  shows "term_mctxt_conv (d \<cdot> \<rho>) \<le> term_mctxt_conv (d \<cdot> \<tau>)"
  using assms unfolding leq_mctxt_subst by blast 

text \<open>{cite \<open>Lemma 3.11\<close> FMZvO15}\<close>

lemma rewrite_aliens:
  fixes C :: "('f, 'v :: infinite) mctxt" and l :: "('f, 'w) term"
  assumes "wf_trs R" "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep_r_p_s' R (l, r) p \<sigma>"
    "num_holes C = length ss" "l \<cdot> \<tau> = subt_at (fill_holes C ss) p"
  obtains ts where "num_holes D = length ts"
    "(fill_holes C ss, fill_holes D ts) \<in> rstep_r_p_s' R (l, r) p \<tau>" "set ts \<subseteq> set ss"
    "\<And>f. \<exists>\<tau>'. (fill_holes C (map f ss), fill_holes D (map f ts)) \<in> rstep_r_p_s' R (l, r) p \<tau>'"
proof -
  from assms(2) obtain E where 1: "mctxt_term_conv C = E\<langle>l \<cdot> \<sigma>\<rangle>" "mctxt_term_conv D = E\<langle>r \<cdot> \<sigma>\<rangle>"
    "p = hole_pos E" "(l, r) \<in> R" by (induct rule: rstep_r_p_s'.induct) simp
  from 1(4) assms(1) have rl: "vars_term r \<subseteq> vars_term l" by (auto simp: wf_trs_def)
  from 1(3) arg_cong[OF 1(1), of term_mctxt_conv] have 2: "p \<in> all_poss_mctxt C" "l \<cdot> \<sigma> = mctxt_term_conv (subm_at C p)"
    using subt_at_mctxt_term_conv[of p C, symmetric] by auto
  from matched_mctxt_to_term[OF this] obtain c :: "('f, 'v) term" and \<rho> \<rho>' where
    3: "mctxt_term_conv C = c \<cdot> \<rho>"  "\<And>x. x \<in> vars_term c \<Longrightarrow> is_Var (\<rho> x)" "p \<in> poss c" "l \<cdot> \<rho>' = c |_ p"
    "\<And>D \<tau>. C \<le> D \<Longrightarrow> l \<cdot> \<tau> = mctxt_term_conv (subm_at D p) \<Longrightarrow> \<exists>\<tau>'. c \<cdot> \<tau>' = mctxt_term_conv D"
    by metis
  let ?s = "mctxt_of_term (fill_holes C ss)" and ?\<tau> = "\<tau> \<circ>\<^sub>s (Var \<circ> Some)"
  have 4: "C \<le> ?s" "l \<cdot> ?\<tau> = mctxt_term_conv (subm_at ?s p)" "p \<in> all_poss_mctxt ?s"
    using assms(3,4) 2(1) subt_at_mctxt_term_conv[of p ?s, symmetric] subsetD[OF all_poss_mctxt_mono[of C ?s]]
      subt_at_subst[of p "fill_holes C ss" "Var \<circ> Some"] all_poss_mctxt_mctxt_of_term[of "fill_holes C ss", symmetric]
    by (auto simp del: subt_at_subst all_poss_mctxt_mctxt_of_term)
  from 3(5)[OF this(1,2)] obtain \<tau>' where 5: "c \<cdot> \<tau>' = mctxt_term_conv ?s" by blast
  let ?d = "replace_at c p (r \<cdot> \<rho>')"
  have 6: "(c, ?d) \<in> rstep_r_p_s' R (l, r) p \<rho>'"
    using 1(4) 3(3,4) by (auto intro!: rstep_r_p_s'I simp: ctxt_supt_id)
  from rstep_r_p_s'_deterministic[OF assms(1,2) rstep_r_p_s'_stable[OF this, of \<rho>, folded 3(1)]]
    have 7: "mctxt_term_conv D = ?d \<cdot> \<rho>" .
  obtain d where 8: "(fill_holes C ss, d) \<in> rstep_r_p_s' R (l,r) p \<tau>"
    using rstep_r_p_s'I[OF 1(4) _ refl refl, of p "ctxt_of_pos_term p (fill_holes C ss)" \<tau>] assms(4) 4(3)
    by (simp add: ctxt_supt_id)
  have "fill_holes C ss \<cdot> (Var \<circ> Some) \<cdot> (Var \<circ> the) = fill_holes C ss" unfolding subst_subst subst_compose_def by simp
  note rstep_r_p_s'_stable[OF 6, of "\<tau>' \<circ>\<^sub>s (Var \<circ> the)", unfolded subst_subst_compose 5 mctxt_term_conv_mctxt_of_term this]
  from rstep_r_p_s'_deterministic[OF assms(1) this 8] assms(4) 8
    have 9: "(fill_holes C ss, ?d \<cdot> (\<tau>' \<circ>\<^sub>s (Var \<circ> the))) \<in> rstep_r_p_s' R (l, r) p \<tau>" by simp
  have A: "vars_term ?d \<subseteq> vars_term c"
    using arg_cong[OF ctxt_supt_id[OF 3(3), folded 3(4)], of vars_term, symmetric] assms(1) 1(4)
    by (auto simp add: vars_term_ctxt_apply wf_trs_def vars_term_subst) blast
  from leq_mctxt_vars_term_subst[OF this, of \<rho> \<tau>'] have B: "D \<le> term_mctxt_conv (?d \<cdot> \<tau>')"
    using arg_cong[OF 7, of "term_mctxt_conv"]
      arg_cong[OF 3(1), of "\<lambda>C. term_mctxt_conv C"] 4(1) arg_cong[OF 5, of "\<lambda>C. term_mctxt_conv C"]
      arg_cong[OF mctxt_term_conv_mctxt_of_term, of "\<lambda>C. term_mctxt_conv C"]
    by (simp del: subst_apply_term_ctxt_apply_distrib mctxt_term_conv_mctxt_of_term)
  have X: "fill_holes C ss = c \<cdot> \<tau>' \<circ>\<^sub>s (Var \<circ> the)" using 5
    by (simp only: mctxt_term_conv_mctxt_of_term subst_subst_compose) (simp del: subst_subst_compose add: subst_subst subst_compose_def)
  have "(ctxt_of_pos_term p c)\<langle>r \<cdot> \<rho>'\<rangle> \<cdot> \<tau>' = mctxt_term_conv (mctxt_of_term ((ctxt_of_pos_term p c)\<langle>r \<cdot> \<rho>'\<rangle> \<cdot> \<tau>' \<circ>\<^sub>s (Var \<circ> the)))"
    using 5 A unfolding mctxt_term_conv_mctxt_of_term subst_subst X term_subst_eq_conv by blast
  from arg_cong[OF this, of term_mctxt_conv] have "D \<le> mctxt_of_term (?d \<cdot> \<tau>' \<circ>\<^sub>s (Var \<circ> the))" using B
    by (simp only: term_mctxt_conv_inv)
  note U = length_unfill_holes[OF this, symmetric] fill_unfill_holes[OF this]
  let ?ts = "unfill_holes D (?d \<cdot> \<tau>' \<circ>\<^sub>s (Var \<circ> the))"
  have W: "set ?ts \<subseteq> set ss"
    using A alien_set_by_substitution[OF 3(1,2) assms(3) X] alien_set_by_substitution[OF 7 3(2) U] by blast
  have Z: "(fill_holes C ss, fill_holes D ?ts) \<in> rstep_r_p_s' R (l, r) p \<tau>" using 9 unfolding U .
  { fix f
    let ?\<tau> = "\<lambda>x. if \<rho> x = Var None then f ((\<tau>' \<circ>\<^sub>s (Var \<circ> the)) x) else (\<tau>' \<circ>\<^sub>s (Var \<circ> the)) x"
    have "term_mctxt_conv t \<le> mctxt_of_term (t \<cdot> (Var \<circ> the))" for t :: "('f, 'v option) term"
      by (induct t; (case_tac "x :: _ option")?) (auto intro: less_eq_mctxtI1)
    from this[of "?d \<cdot> \<tau>'"]
    have "D \<le> mctxt_of_term (ctxt_of_pos_term p c \<cdot>\<^sub>c \<tau>' \<cdot>\<^sub>c (Var \<circ> the))\<langle>r \<cdot> \<rho>' \<cdot> \<tau>' \<cdot> (Var \<circ> the)\<rangle>"
      using B by auto
    then have "(fill_holes C (map f ss), fill_holes D (map f ?ts)) \<in> rstep_r_p_s' R (l, r) p (\<rho>' \<circ>\<^sub>s ?\<tau>)"
      apply (subst alien_map_by_substitution[OF 3(1) 3(2) assms(3) X], simp)
      apply (subst alien_map_by_substitution[OF 7, of _ "\<tau>' \<circ>\<^sub>s (Var \<circ> the)"])
      using 3(2) rstep'_sub_vars[OF r_into_rtrancl assms(1), of c ?d] 6 rstep_r_p_s'_stable[OF 6]
      by (auto simp: fill_unfill_holes rstep'_iff_rstep_r_p_s')
  }
  with that[OF U(1) Z W] show ?thesis by blast
qed

lemma rewrite_aliens_mctxt:
  fixes C :: "('f, 'v :: infinite) mctxt" and l :: "('f, 'w) term"
  assumes "wf_trs R" "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep_r_p_s' R (l, r) p \<sigma>"
    "num_holes C = length Cs" "l \<cdot> \<tau> = subt_at (mctxt_term_conv (fill_holes_mctxt C Cs)) p"
  obtains Ds where "num_holes D = length Ds"
    "(mctxt_term_conv (fill_holes_mctxt C Cs), mctxt_term_conv (fill_holes_mctxt D Ds)) \<in> rstep_r_p_s' R (l, r) p \<tau>"
    "set Ds \<subseteq> set Cs"
proof -
  have [simp]: "mctxt_term_conv C \<cdot> (Var \<circ> case_option None (Some \<circ> Some)) = mctxt_term_conv (map_vars_mctxt Some C)"
    for C by (induct C) auto
  obtain ts where
    "num_holes (map_vars_mctxt Some D) = length ts"
    "(fill_holes (map_vars_mctxt Some C) (map mctxt_term_conv Cs), fill_holes (map_vars_mctxt Some D) ts) \<in> rstep_r_p_s' R (l, r) p \<tau>"
    "set ts \<subseteq> set (map mctxt_term_conv Cs)"
    using assms rstep_r_p_s'_stable[OF assms(2), of "Var \<circ> case_option None (Some \<circ> Some)"]
    by (auto intro: rewrite_aliens[of R "map_vars_mctxt Some C" "map_vars_mctxt Some D" l r p
      "\<sigma> \<circ>\<^sub>s (Var \<circ> case_option None (Some \<circ> Some))" "map mctxt_term_conv Cs" \<tau>] simp: mctxt_term_conv_fill_holes_mctxt)
  then have "num_holes D = length (map term_mctxt_conv ts)"
    "(mctxt_term_conv (fill_holes_mctxt C Cs), mctxt_term_conv (fill_holes_mctxt D (map term_mctxt_conv ts))) \<in> rstep_r_p_s' R (l, r) p \<tau>"
    "set (map term_mctxt_conv ts) \<subseteq> set Cs" using assms(3)
    by (auto simp: mctxt_term_conv_fill_holes_mctxt comp_def)
  then show ?thesis ..
qed

lemma match_balanced_aliens:
  fixes C :: "('f, 'v :: infinite) mctxt" and l :: "('f, 'w) term"
  assumes "p \<in> all_poss_mctxt C"
    "l \<cdot> \<sigma> = mctxt_term_conv (subm_at C p)"
    "l \<cdot> \<tau> = subt_at (fill_holes C ss) p" "ss \<propto> ts" "num_holes C = length ss"
  obtains (\<tau>') \<tau>' where "l \<cdot> \<tau>' = subt_at (fill_holes C ts) p"
  using assms
proof (induct p arbitrary: C ss ts thesis)
  case Nil
  have [simp]: "s \<cdot> (\<lambda>x. Var (Some x)) = t \<cdot> (\<lambda>x. Var (Some x)) \<longleftrightarrow> s = t" for s t
    by (induct s arbitrary: t; case_tac t)
      (auto intro: list.inj_map_strong[of _ _ "\<lambda>t. t \<cdot> (\<lambda>x. Var (Some x))" "\<lambda>t. t \<cdot> (\<lambda>x. Var (Some x))"])
  obtain c :: "('f,'v) term" and \<rho> \<rho>' where \<rho>: "mctxt_term_conv C = c \<cdot> \<rho>"
    "\<And>x. x \<in> vars_term c \<Longrightarrow> is_Var (\<rho> x)" "[] \<in> poss c" "l \<cdot> \<rho>' = c |_ []" and
    *: "\<And>D \<tau>. C \<le> D \<Longrightarrow> l \<cdot> \<tau> = mctxt_term_conv (subm_at D []) \<Longrightarrow> \<exists>\<tau>'. c \<cdot> \<tau>' = mctxt_term_conv D"
    using matched_mctxt_to_term[OF Nil(2,3)] by blast
  from *[of "mctxt_of_term (fill_holes C ss)" "\<tau> \<circ>\<^sub>s (Var \<circ> Some)"] Nil(2,4,6)
  obtain \<sigma>' where \<sigma>': "c \<cdot> \<sigma>' = fill_holes C ss \<cdot> (Var \<circ> Some)" by auto
  define s2t where "s2t = (\<lambda>s. ts ! (SOME i. i < length ss \<and> ss ! i \<cdot> (Var \<circ> Some) = s))"
  let ?\<tau>' = "(\<lambda>x. if \<rho> x = Var None then s2t (\<sigma>' x) else \<sigma>' x \<cdot> (Var \<circ> the))"
  define ts' where "ts' = ts" define ss' where "ss' = ss"
  have "num_holes C = length ts" "num_holes C = length ss" using Nil(5,6) by (auto simp: refines_def)
  moreover have "set (zip ts ss) \<subseteq> set (zip ts' ss')" by (auto simp: ts'_def ss'_def)
  ultimately have "l \<cdot> \<rho>' \<circ>\<^sub>s (\<lambda>x. if \<rho> x = Var None then s2t (\<sigma>' x) else \<sigma>' x \<cdot> (Var \<circ> the)) = fill_holes C ts"
    using \<sigma>' \<rho>(1,2)
    unfolding subst_subst_compose \<rho>(4) subt_at.simps
  proof (induct C ts ss arbitrary: c rule: fill_holes_induct2)
    case (MHole x y)
    obtain i where [simp]: "x = ts ! i" "y = ss ! i" "i < length ss" "i < length ts"
      using MHole(1) by (auto simp: ss'_def ts'_def in_set_conv_nth)
    from this(3,4) have "ts ! (SOME j. j < length ss \<and> ss ! j = ss ! i) = ts ! i"
      using Nil(5) someI[of "\<lambda>j. j < length ss \<and> ss ! j = ss ! i" i] by (auto simp: refines_def)
    then show ?case
      using MHole(2,3) by (cases c, auto simp: s2t_def comp_def)
  next
    case (MVar v) then show ?case by (cases c) auto
  next
    case (MFun f Cs xs ys)
    then show ?case
    proof (cases c)
      case (Fun g cs) note [simp] = Fun
      have [simp]: "i < length Cs \<Longrightarrow> x \<in> vars_term (cs ! i) \<Longrightarrow> is_Var (\<rho> x)" for i x
        using MFun(6,7) by (auto) (metis length_map nth_mem)
      { fix i x y assume *: "i < length Cs" "(x, y) \<in> set (zip (partition_holes xs Cs ! i) (partition_holes ys Cs ! i))"
        have [simp]: "zip (partition_holes xs Cs ! i) (partition_holes ys Cs ! i) = partition_holes (zip xs ys) Cs ! i"
          "sum_list (map num_holes Cs) = length (zip xs ys)"
          using *(1) MFun(1,2) by (auto simp: partition_by_of_zip)
        from UN_set_partition_by[of "map num_holes Cs" "zip xs ys" "\<lambda>x. {x}"] * have "(x, y) \<in> set (zip xs ys)"
          by force
        then have "(x, y) \<in> set (zip ts' ss')" using MFun(1,2,4) by auto
      } note [simp] = this
      show ?thesis using MFun(1-2,4-) by (auto 0 0 simp: map_eq_conv' intro!: MFun(3))
    qed auto
  qed
  then show ?case by (auto intro: Nil(1)[of "\<rho>' \<circ>\<^sub>s ?\<tau>'"])
next
  case (Cons i p)
  obtain f Cs where [simp]: "C = MFun f Cs" using Cons(3) by (cases C) simp_all
  let ?ss = "partition_holes ss Cs ! i" and ?ts = "partition_holes ts Cs ! i"
  from Cons(3-) obtain \<tau>' where "l \<cdot> \<tau>' = fill_holes (Cs ! i) ?ts |_ p"
  proof (subst Cons(1)[of "Cs ! i" ?ts thesis ?ss], goal_cases)
    case 5 show ?case using Cons(3,6) by (auto simp: partition_by_nth intro: refines_take refines_drop)
  qed auto
  then show ?case using Cons(2)[of \<tau>'] Cons(3) by simp
qed

text \<open>{cite \<open>Lemma 4.14\<close> FMZvO15}\<close>

lemma rewrite_balanced_aliens:
  fixes C :: "('f, 'v :: infinite) mctxt" and l :: "('f, 'w) term"
  assumes "wf_trs R" "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep_r_p_s' R (l, r) p \<sigma>"
    "num_holes C = length ss" "l \<cdot> \<tau> = subt_at (fill_holes C ss) p" "ss \<propto> ts"
  obtains (ts') ts' \<tau>' where "num_holes D = length ts'"
    "(fill_holes C ts, fill_holes D ts') \<in> rstep_r_p_s' R (l, r) p \<tau>'" "set ts' \<subseteq> set ts"
proof -
  have "p \<in> all_poss_mctxt C" "l \<cdot> \<sigma> = mctxt_term_conv (subm_at C p)" using
    assms(2) by (auto simp del: poss_mctxt_term_conv simp: poss_mctxt_term_conv[symmetric] subt_at_mctxt_term_conv[symmetric])
  from match_balanced_aliens[OF this assms(4,5,3)]
  obtain \<tau>' where "l \<cdot> \<tau>' = fill_holes C ts |_ p" by metis
  from rewrite_aliens[OF assms(1-2) assms(3)[folded iffD1[OF refines_def, OF assms(5), THEN conjunct1]] this]
  obtain ts' where "num_holes D = length ts'" "set ts' \<subseteq> set ts"
    "(fill_holes C ts, fill_holes D ts') \<in> rstep_r_p_s' R (l, r) p \<tau>'" by metis
  then show ?thesis using ts'[of ts' \<tau>'] by simp
qed

lemma rewrite_balanced_aliens':
  fixes C :: "('f, 'v :: infinite) mctxt" and l :: "('f, 'w) term"
  assumes "wf_trs R" "length ss = num_holes C" "length ts = num_holes D"
    "(fill_holes C ss, fill_holes D ts) \<in> rstep_r_p_s' R (l, r) p \<sigma>"
    "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep_r_p_s' R (l, r) p \<tau>"
  obtains \<sigma>' where "(fill_holes C (map f ss), fill_holes D (map f ts)) \<in> rstep_r_p_s' R (l, r) p \<sigma>'"
proof -
  have p: "p \<in> all_poss_mctxt C" using wf_trs_implies_fun_poss[OF assms(1,5)]
    fun_poss_imp_poss poss_mctxt_term_conv by blast
  then have "l \<cdot> \<sigma> = fill_holes C ss |_ p" using assms(4) by auto
  from rewrite_aliens[OF assms(1,5) assms(2)[symmetric] this]
  obtain ts' where ts': "num_holes D = length ts'"
    "(fill_holes C ss, fill_holes D ts') \<in> rstep_r_p_s' R (l, r) p \<sigma>"
    "\<And>f. \<exists>\<tau>'. (fill_holes C (map f ss), fill_holes D (map f ts')) \<in> rstep_r_p_s' R (l, r) p \<tau>'"
    by metis
  have [simp]: "ts' = ts" using ts'(1) assms(3) rstep_r_p_s'_deterministic[OF assms(1,4) ts'(2)]
    by (auto simp: fill_holes_inj)
  show ?thesis using that ts'(3) by auto
qed

lemma rewrite_cases:
  assumes "num_holes C = length ss" "(fill_holes C ss, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  obtains (outer) "p \<in> poss_mctxt C" "(fill_holes C ss, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    | (inner) i ti where "i < length ss" "t = fill_holes C (ss[i := ti])"
      "(ss ! i, ti) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' C ! i)) \<sigma>"
      "hole_poss' C ! i \<le>\<^sub>p p"
  using assms
proof (induct C ss arbitrary: p t thesis rule: fill_holes_induct)
  case (MVar x)
  have "p \<in> poss_mctxt (MVar x)" using MVar by (elim rstep_r_p_s'E, case_tac C) auto
  then show ?case using MVar by auto
next
  case (MFun f Cs ss) show ?case
  proof (cases p)
    case Nil then show ?thesis using MFun(1,5) by (intro MFun(3)) auto
  next
    case (Cons i q)
    obtain g ts ti where
      *: "fill_holes (MFun f Cs) (concat (partition_holes ss Cs)) = Fun g ts" "i < length ts"
      "t = Fun g (ts[i := ti])" "(ts ! i, ti) \<in> rstep_r_p_s' \<R> (l, r) q \<sigma>" by (metis rstep_r_p_s'_argE[OF MFun(5)[unfolded Cons]])
    then have [simp]: "g = f" "length ts = length Cs" "ts ! i = fill_holes (Cs ! i) (partition_holes ss Cs ! i)"
      using MFun(1) by auto
    note * = *[unfolded this]
    consider "q \<in> poss_mctxt (Cs ! i)"
      "(fill_holes (Cs ! i) (partition_holes ss Cs ! i), ti) \<in> rstep_r_p_s' \<R> (l, r) q \<sigma>"
    | j tj where "j < length (partition_holes ss Cs ! i)" "ti = fill_holes (Cs ! i) ((partition_holes ss Cs ! i)[j := tj])"
      "(partition_holes ss Cs ! i ! j, tj) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff q (hole_poss' (Cs ! i) ! j)) \<sigma>"
      "hole_poss' (Cs ! i) ! j \<le>\<^sub>p q"
      using MFun(2)[OF *(2) _ _ *(4)] by metis
    then show ?thesis
    proof cases
      case 1 then show ?thesis using *(2) MFun(5) by (intro MFun(3)) (simp_all add: Cons *)
    next
      case 2 let ?k = "sum_list (take i (map num_holes Cs)) + j"
      have k: "?k < length ss" using MFun(1) *(2) 2(1)
        concat_nth_length[of i "partition_holes ss Cs" j] by (auto simp: take_map[symmetric])
      show ?thesis
      proof (intro MFun(4)[of ?k tj])
        show "?k < length (concat (partition_holes ss Cs))" using k MFun(1) by auto
      next
        have [simp]: "partition_holes (concat ((partition_holes ss Cs)[i := (partition_holes ss Cs ! i)[j := tj]])) Cs =
          (partition_holes ss Cs)[i := (partition_holes ss Cs ! i)[j := tj]]" using MFun(1)
        proof (intro partition_holes_concat_id)
          fix k assume "sum_list (map num_holes Cs) = length ss" "k < length Cs"
          then show "num_holes (Cs ! k) = length ((partition_holes ss Cs)[i := (partition_holes ss Cs ! i)[j := tj]] ! k)"
            using MFun(1) by (cases "i = k") auto
        qed simp
        have "k < length Cs \<Longrightarrow> ts[i := ti] ! k = fill_holes (Cs ! k) (partition_holes (ss[?k := tj]) Cs ! k)" for k
          using *(1,2) list_update_concat[of i "partition_holes ss Cs" j tj, symmetric] 2 MFun(1)
            by (subst nth_list_update) auto
        then show "t = fill_holes (MFun f Cs) ((concat (partition_holes ss Cs))[?k := tj])"
          unfolding * using *(2) k MFun(1) by (auto intro!: nth_equalityI)
      next
        have "hole_poss' (MFun f Cs) ! (sum_list (take i (map num_holes Cs)) + j) = i # hole_poss' (Cs ! i) ! j"
          using concat_nth[of i "map (\<lambda>i. map ((#) i) (hole_poss' (Cs ! i))) [0..<length Cs]" j ?k]
            MFun(1) *(2) 2(1) by (auto simp: take_map[symmetric] comp_def map_upt_len_conv)
        then show "(concat (partition_holes ss Cs) ! ?k, tj) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' (MFun f Cs) ! ?k)) \<sigma>"
          "hole_poss' (MFun f Cs) ! (sum_list (take i (map num_holes Cs)) + j) \<le>\<^sub>p p"
          using MFun(1) 2(3,4) concat_nth[of i "partition_holes ss Cs" j ?k] *(2) 2(1)
          by (auto simp: Cons take_map[symmetric])
      qed
    qed
  qed
qed auto

lemma rewrite_cases_mctxt:
  assumes "num_holes C = length Cs" "(mctxt_term_conv (fill_holes_mctxt C Cs), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  obtains (outer) "p \<in> poss_mctxt C" "(mctxt_term_conv (fill_holes_mctxt C Cs), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    | (inner) i Ci where "i < length Cs" "D = fill_holes_mctxt C (Cs[i := Ci])"
      "(mctxt_term_conv (Cs ! i), mctxt_term_conv Ci) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' C ! i)) \<sigma>"
proof -
  from assms rewrite_cases[of "map_vars_mctxt Some C" "map mctxt_term_conv Cs" "mctxt_term_conv D" \<R> l r p \<sigma>]
  consider
    (outer') "p \<in> poss_mctxt C"
      "(fill_holes (map_vars_mctxt Some C) (map mctxt_term_conv Cs), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  | (inner') i ti where "i < length Cs"
      "mctxt_term_conv D = fill_holes (map_vars_mctxt Some C) ((map mctxt_term_conv Cs)[i := ti])"
      "(map mctxt_term_conv Cs ! i, ti) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' (map_vars_mctxt Some C) ! i)) \<sigma>"
    by (simp add: mctxt_term_conv_fill_holes_mctxt) metis
  then show thesis
  proof cases
    case outer'
    moreover have "(mctxt_term_conv (fill_holes_mctxt C Cs), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
      using outer'(2) assms(1) by (simp add: mctxt_term_conv_fill_holes_mctxt)
    ultimately show ?thesis by (intro outer)
  next
    case (inner' i ti)
    moreover have "D = fill_holes_mctxt C (Cs[i := term_mctxt_conv ti])"
      using arg_cong[OF inner'(2), of "term_mctxt_conv"] assms(1)
        mctxt_term_conv_fill_holes_mctxt[of C "Cs[i := term_mctxt_conv ti]", symmetric]
      by (simp add: map_update)
    moreover have "(mctxt_term_conv (Cs ! i), mctxt_term_conv (term_mctxt_conv ti)) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' C ! i)) \<sigma>"
      using inner'(1,3) by simp
    ultimately show ?thesis by (intro inner)
  qed
qed

lemma rewrite_cases_wf:
  assumes "wf_trs \<R>" "num_holes C = length ss" "(fill_holes C ss, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  obtains (outer) "p \<in> fun_poss_mctxt C" "(fill_holes C ss, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  | (inner) i ti where "i < length ss" "t = fill_holes C (ss[i := ti])"
    "(ss ! i, ti) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' C ! i)) \<sigma>"
    "hole_poss' C ! i \<le>\<^sub>p p"
proof -
  consider (outer') "p \<in> poss_mctxt C" "(fill_holes C ss, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  | (inner') i ti where "i < length ss" "t = fill_holes C (ss[i := ti])"
    "(ss ! i, ti) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' C ! i)) \<sigma>"
    "hole_poss' C ! i \<le>\<^sub>p p"
  using assms rewrite_cases by blast
  then show ?thesis
  proof (cases)
    case outer' show ?thesis
    proof (cases rule: outer)
      case 1 show ?case using assms(2) outer'(1) wf_trs_implies_fun_poss[OF \<open>wf_trs \<R>\<close> outer'(2)]
        by (induct C ss arbitrary: p rule: fill_holes_induct) (auto simp: fun_poss_mctxt_def)
    qed fact
  qed fact
qed

lemma rewrite_cases_mctxt_wf:
  assumes "wf_trs \<R>" "num_holes C = length Cs" "(mctxt_term_conv (fill_holes_mctxt C Cs), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  obtains (outer) "p \<in> fun_poss_mctxt C" "(mctxt_term_conv (fill_holes_mctxt C Cs), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
    | (inner) i Ci where "i < length Cs" "D = fill_holes_mctxt C (Cs[i := Ci])"
      "(mctxt_term_conv (Cs ! i), mctxt_term_conv Ci) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' C ! i)) \<sigma>"
proof -
  consider (outer') "p \<in> poss_mctxt C" "(mctxt_term_conv (fill_holes_mctxt C Cs), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  | (inner') i Ci where "i < length Cs" "D = fill_holes_mctxt C (Cs[i := Ci])"
      "(mctxt_term_conv (Cs ! i), mctxt_term_conv Ci) \<in> rstep_r_p_s' \<R> (l, r) (pos_diff p (hole_poss' C ! i)) \<sigma>"
  using assms rewrite_cases_mctxt by blast
  then show ?thesis
  proof (cases)
    case outer' show ?thesis
    proof (cases rule: outer)
      case 1 show ?case using assms(2) outer'(1) wf_trs_implies_fun_poss[OF \<open>wf_trs \<R>\<close> outer'(2)]
        by (induct C Cs arbitrary: p rule: fill_holes_induct) (auto simp: fun_poss_mctxt_def)
    qed fact
  qed fact
qed

lemma (in weakly_layered) \<T>_preservation:
  assumes "s \<in> \<T>" "(s, t) \<in> rstep' \<R>" shows "t \<in> \<T>"
using assms \<R>_sig trs rstep_preserves_funas_terms unfolding rstep_eq_rstep'[symmetric] \<T>_def by blast

(* hence t \<in> \<T> in W follows from the other premises *)
lemma (in weakly_layered) W':
  assumes "s \<in> \<T>" "p \<in> fun_poss_mctxt (max_top s)" "(s, t) \<in> rstep_r_p_s' \<R> r p \<sigma>"
  shows "\<exists>D \<tau>. D \<in> \<LL> \<and> (mctxt_term_conv (max_top s), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> r p \<tau>"
  by (metis assms W rstep'_iff_rstep_r_p_s' \<T>_preservation surjective_pairing)

text \<open>{cite \<open>Lemma 3.12\<close> FMZvO15}\<close>

lemma (in weakly_layered) rank_preservation:
  assumes "s \<in> \<T>" "(s, t) \<in> rstep' \<R>" shows "rank t \<le> rank s"
  using assms
proof (induct s arbitrary: t rule: rank.induct)
  case (1 s)
  note t = \<T>_preservation[OF 1(2,3)]
  from 1(3) obtain l r p \<sigma> where rs: "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>" unfolding rstep'_iff_rstep_r_p_s' by blast
  have ms: "max_top s \<le> mctxt_of_term s" using max_topC_props(1) by (simp add: topsC_def)
  let ?ss = "aliens s"
  note ms' = length_unfill_holes[OF ms] fill_unfill_holes[OF ms]
  from 1(3) obtain l r p \<sigma> where rs: "(s, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>" unfolding rstep'_iff_rstep_r_p_s' by blast
  then have "(fill_holes (max_top s) ?ss, t) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>" unfolding ms' .
  from ms'(1)[symmetric] this show ?case
  proof (cases rule: rewrite_cases)
    case outer
    then obtain C where *: "p \<in> poss s" "p = hole_pos C" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l, r) \<in> \<R>"
      by (auto elim: rstep_r_p_s'E simp: ms')
    have "p \<in> fun_poss s" using *(2,3,5) trs hole_pos_in_filled_fun_poss[of "l \<cdot> \<sigma>" C Var] by (force simp: wf_trs_def)
    then have p: "p \<in> fun_poss_mctxt (max_top s)" using outer *(1) fun_poss_mctxt_compat[OF ms] by auto
    from W[OF \<open>s \<in> \<T>\<close> \<open>t \<in> \<T>\<close> p rs] obtain D \<tau> where w: "D \<in> \<LL>"
      "(mctxt_term_conv (max_top s), mctxt_term_conv D) \<in> rstep_r_p_s' \<R> (l, r) p \<tau>" by blast
    from rewrite_aliens[OF trs w(2) length_unfill_holes[OF ms, symmetric], unfolded fill_unfill_holes[OF ms], of \<sigma>]
    obtain ts where ts: "num_holes D = length ts" "set ts \<subseteq> set ?ss"
      "(s, fill_holes D ts) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>" using *(2,3) by (metis subt_at_hole_pos)
    have t': "t = fill_holes D ts" using rstep_r_p_s'_deterministic[OF trs rs ts(3)] .
    then have ts': "ts = unfill_holes D t" using unfill_fill_holes[OF ts(1)[symmetric]] by simp
    have D: "D \<le> max_top (fill_holes D ts)" using fill_holes_suffix[OF ts(1)] w(1) topsC_def max_topC_props(2) by blast
    have "max_list (map rank ts) \<le> max_list (map rank ?ss)" using ts(2)
      by (intro max_list_mono) auto
    then show ?thesis using rank_by_top[OF \<open>t \<in> \<T>\<close> D[folded t']] ts(2)
    using outer trs \<open>s \<in> \<T>\<close> unfolding ts'[symmetric] by (subst (2) rank.simps) auto
  next
    case (inner i ti)
    then have "rank ti \<le> rank (?ss ! i)"
      using funas_term_fill_holes_iff[OF ms'(1)[symmetric], unfolded ms'] 1(2)
      by (intro 1) (force simp: rstep'_iff_rstep_r_p_s' \<T>_def)+
    then have 3: "max_list (map rank (?ss[i := ti])) \<le> max_list (map rank ?ss)"
      unfolding map_update upd_conv_take_nth_drop[of i "map rank ?ss" "rank ti", unfolded length_map, OF inner(1)]
      apply (subst (3) id_take_nth_drop[of i "map rank ?ss", unfolded length_map, OF inner(1)])
      unfolding max_list_append max_list.simps nth_map[OF inner(1)] by linarith
    have 4: "max_top s \<le> max_top t" using inner(2) fill_holes_suffix[OF ms'(1)[symmetric], unfolded ms']
      by (auto simp: topsC_def)
    have [simp]: "unfill_holes (max_top s) (fill_holes (max_top s) ((unfill_holes (max_top s) s)[i := ti])) =
      (unfill_holes (max_top s) s)[i := ti]" by (intro unfill_fill_holes) (auto simp: ms')
    show ?thesis using 3 rank_by_top[OF \<open>t \<in> \<T>\<close> 4] inner(2) 1(2) by (subst (2) rank.simps) (auto simp: ms')
  qed
qed

lemma (in layer_system) max_top_mono1:
  assumes "\<LL>' \<subseteq> \<LL>"
  and "max_topC C \<in> \<LL>'"
  shows "layer_system_sig.max_topC \<LL>' C = max_topC C"
proof -
  let ?topsC' = "layer_system_sig.topsC \<LL>'"
  have 1: "\<And>L. L \<in> ?topsC' C \<Longrightarrow> L \<in> topsC C"
    "\<And>L. L \<in> topsC C \<Longrightarrow> L \<in> \<LL>' \<Longrightarrow> L \<in> ?topsC' C" using assms(1)
    unfolding layer_system_sig.topsC_def by blast+
  moreover {
    fix M assume *: "M \<in> ?topsC' C" "\<And>L. L \<in> ?topsC' C \<Longrightarrow> L \<le> M"
    have "M = max_topC C"
      using *(1) *(2)[of "max_topC C"] 1(2)[OF _ assms(2)] max_topC_props(2)[OF 1(1), of M] by auto
  }
  ultimately show ?thesis using assms(2)
    unfolding layer_system_sig.max_topC_def[of "\<LL>'"]
    by (intro the1_equality ex1I[of _ "max_topC C"]) auto
qed

lemma (in layer_system) ls_change_vars:
  "layer_system \<F> {L. vars_to_holes L \<in> \<LL>}"
proof (standard, goal_cases \<LL>_sig' L\<^sub>1' L\<^sub>2' L\<^sub>3')
  case \<LL>_sig' show ?case using \<LL>_sig
    apply (auto simp: layer_system_sig.\<C>_def) using funas_term_vars_to_holes by blast
next
  case (L\<^sub>1' t) show ?case
  proof (cases t)
    case (Var x) then show ?thesis by (auto intro: exI[of _ "MVar x"])
  next
    case (Fun f ts)
    have *: "vars_to_holes (mctxt_of_term (map_vars_term f t)) = vars_to_holes (mctxt_of_term t)" for f t
      by (induct t) auto
    have **: "L \<le> mctxt_of_term (map_vars_term f t) \<Longrightarrow> vars_to_holes L \<le> mctxt_of_term t" for L f t
      using order.trans[OF vars_to_holes_mono[of L "mctxt_of_term (map_vars_term f t)", unfolded *]
        vars_to_holes_prefix[of "mctxt_of_term t"]] .
    obtain L where "L \<in> \<LL>" "L \<le> mctxt_of_term (map_vars_term undefined t)" "L \<noteq> MHole"
      using L\<^sub>1[of "map_vars_term undefined t"] L\<^sub>1' by auto
    with Fun show ?thesis
    by (intro bexI[of _ "vars_to_holes L"], cases L)
      (auto elim: less_eq_mctxtE1(1) elim!: less_eq_mctxtE1(2) intro!: less_eq_mctxtI2(3) ** simp: vars_to_holes_layer)
  qed
next
  case (L\<^sub>2' p C x)
  then have [simp]: "vars_to_holes (mreplace_at C p (MVar x)) =  vars_to_holes (mreplace_at C p (MHole))"
    by (induct C p rule: subm_at.induct) auto
  show ?case by auto
next
  case (L\<^sub>3' L N p) then show ?case using L\<^sub>3[of "vars_to_holes L" "vars_to_holes N" p]
    vars_to_holes_comp_mctxt[OF L\<^sub>3'(4)] by (auto simp: subsetD[OF fun_poss_mctxt_subset_poss_mctxt])
qed

context layer_system
begin

lemma \<LL>_by_vars_to_holes:
  "{L. vars_to_holes L \<in> \<LL>} = \<LL>"
  by (auto simp: vars_to_holes_layer)

interpretation ls_change_vars: layer_system where \<F> = \<F> and \<LL> = "{L. vars_to_holes L \<in> \<LL>}"
  by (rule ls_change_vars)

lemma max_top_var_subst_change_vars:
  "ls_change_vars.max_top (t \<cdot> (Var \<circ> f)) = map_vars_mctxt f (max_top t)"
  using max_topC_props(1)[of "mctxt_of_term t"] max_topC_props(2)[of _ "mctxt_of_term t"]
  by (intro ls_change_vars.max_topCI) (auto simp: ls_change_vars.topsC_def topsC_def mctxt_of_term_var_subst
    vars_to_holes_layer intro: map_vars_mctxt_mono elim!: map_vars_mctxt_less_eq_decomp)

lemma rank_change_vars:
  "ls_change_vars.rank (t \<cdot> (Var \<circ> f)) = rank t"
proof (induct t rule: rank.induct)
  case (1 t) then show ?case
    using ls_change_vars.rank.simps[of "t \<cdot> (Var \<circ> f)"] rank.simps[of t] unfill_holes_var_subst[OF max_top_prefix, of f t]
    by (auto simp: max_top_var_subst_change_vars[unfolded comp_def] comp_def \<T>_def ls_change_vars.\<T>_def funas_term_subst intro!: arg_cong[of _ _ max_list] intro!: nth_equalityI)
qed

end (* layer_system *)

context layer_system
begin

interpretation ls_change_vars: layer_system where \<F> = \<F> and \<LL> = "{L. vars_to_holes L \<in> \<LL>}"
  by (rule ls_change_vars)

lemma rank_change_vars': "ls_change_vars.rank t = rank (t \<cdot> (Var \<circ> f))"
  using ls_change_vars.rank_change_vars[of t f] \<LL>_by_vars_to_holes by auto

lemmas rank_by_top_change_vars = ls_change_vars.rank_by_top

end (* layer_system *)

end
