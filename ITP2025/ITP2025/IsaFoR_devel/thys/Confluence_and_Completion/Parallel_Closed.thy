(*
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

theory Parallel_Closed
imports
  First_Order_Rewriting.Critical_Pairs
  First_Order_Rewriting.Parallel_Rewriting
  Auxx.Multiset2
  TRS.More_Abstract_Rewriting  
begin

subsection \<open>Measuring Overlap\<close>

fun overlap' :: "('f, 'v) mctxt \<times> ('f, 'v) term list \<Rightarrow> ('f, 'v) mctxt \<times> ('f, 'v) term list \<Rightarrow> ('f, 'v) term multiset"
where
  "overlap' (MHole, [l]) (C, ls) = mset ls"
| "overlap' (C, ls) (MHole, [l]) = mset ls"
| "overlap' (MFun f Cs, ls) (MFun g Ds, ls') =
   \<Sum>\<^sub># {# overlap' (Cs ! i, partition_holes ls Cs ! i) (Ds ! i, partition_holes ls' Ds ! i). i \<in># mset [0..<length Cs] #}"
| "overlap' (MVar x, []) (C, ls) = {#}"
| "overlap' (C, ls) (MVar x, []) = {#}"
| "overlap' _ _ = undefined"

lemma overlap'_symmetric:
  assumes "s =\<^sub>f (C, ls)"  and "s =\<^sub>f (D, ls')"
  shows "overlap' (C, ls) (D, ls') = overlap' (D, ls') (C, ls)"
using assms
proof (induct C arbitrary: D s ls ls')
  case (MVar x) note C = this
  then have [simp]: "ls = []" by (auto dest!: eqfE)
  show ?case
  proof (cases D)
    case (MVar y) with C show ?thesis by (auto dest!: eqfE)
  next
    case MHole with C show ?thesis  by (auto dest!: eqf_MHoleE)
  qed auto
next
  case MHole note C = this
  then obtain l where [simp]: "ls = [l]" by (auto dest!: eqf_MHoleE)
  show ?case
  proof (cases D)
    case (MVar y) with C show ?thesis by (auto dest!: eqfE)
  next
    case MHole with C show ?thesis  by (auto dest!: eqf_MHoleE)
  qed auto
next
  case (MFun f cs) note C = this
  then obtain ss lss where s:"s = Fun f ss"
    and  lcs:"length ss = length cs" and llss:"length lss = length cs"
    and lss:"ls = concat lss" and lsics:"\<And> i. i < length cs \<Longrightarrow> ss ! i =\<^sub>f (cs ! i, lss ! i)"
    using C by (auto elim: eqf_MFunE)
  show ?case
  proof (cases D)
    case (MVar x) with C show ?thesis by (auto dest!: eqfE)
  next
    case MHole with C show ?thesis  by (auto dest!: eqf_MHoleE)
  next
    case (MFun g ds)
    with C obtain ts lss' where "s = Fun g ts"
      and  lds:"length ts = length ds" and llss':"length lss' = length ds"
      and lss':"ls' = concat lss'" and ls'ids:"\<And> i. i < length ds \<Longrightarrow> ts ! i =\<^sub>f (ds ! i, lss' ! i)"
      using C by (auto elim: eqf_MFunE)
    with s have [simp]: "g = f" "ts = ss" by auto
    have [simp]: "partition_holes ls cs = lss" by (metis eqfE(2) llss lsics lss partition_holes_concat_id)
    have [simp]: "partition_holes ls' ds = lss'" by (metis eqfE(2) llss' ls'ids lss' partition_holes_concat_id)
    { fix i
      assume i:"i < length cs"
      then have "cs ! i \<in> set cs" by auto
      from C(1)[OF this lsics[OF i], of "ds ! i" "lss' ! i"] ls'ids i
      have "overlap' (cs ! i, lss ! i) (ds ! i, lss' ! i) = overlap' (ds ! i, lss' ! i) (cs ! i, lss ! i)"
        using lds lcs by auto
    } note ieq = this
    then have "(map (\<lambda>i. overlap' (cs ! i, lss ! i)  (ds ! i, lss' ! i)) [0..<length cs]) =
      (map (\<lambda>i. overlap' (ds ! i, lss' ! i) (cs ! i, lss ! i)) [0..<length ds])"
      using nth_equalityI lcs lds by auto
    then have "{#overlap' (cs ! i, lss ! i)  (ds ! i, lss' ! i). i \<in># mset [0..<length cs]#} =
      {#overlap' (ds ! i, lss' ! i) (cs ! i, lss ! i). i \<in># mset [0..<length ds]#}"
      using mset_map by (metis (no_types))
    with MFun show ?thesis by auto
  qed
qed

lemma overlap'_bounded:
  assumes "s =\<^sub>f (C, ls)" and "s =\<^sub>f (D, ls')"
  shows "(overlap' (C, ls) (D, ls'), mset ls) \<in> (mult {\<lhd>})\<^sup>="
proof -
  have trans: "trans {\<lhd>}" unfolding trans_def using supt_trans by auto
  show ?thesis
  using assms
  proof (induct C arbitrary: D ls ls' s)
    case (MVar x) note C = this
    then have [simp]: "ls = []" by (auto dest!: eqfE)
    show ?case
    proof (cases D)
      case (MVar y) with C show ?thesis by (auto dest!: eqfE)
    next
      case MHole with C show ?thesis  by (auto dest!: eqf_MHoleE)
    qed auto
  next
    case MHole note C = this
    then obtain l where [simp]: "ls = [l]" "s = l" by (auto dest!: eqf_MHoleE)
    show ?case
    proof (cases D)
      case (MVar y) with C show ?thesis by (auto dest!: eqfE simp: mult_def)
    next
      case MHole with C show ?thesis  by (auto dest!: eqf_MHoleE)
    next
      case (MFun g ds)
      from eqf_MFun_imp_strict_subt[OF C(2)[unfolded MFun]] have "\<And>t. t \<in> set ls' \<Longrightarrow> l \<rhd> t"
        by auto
      then have "(mset ls', {#l#}) \<in> mult {\<lhd>}"
        using one_step_implies_mult [of "{#l#}" "mset ls'" "{\<lhd>}" "{#}"] by auto
      with MFun show ?thesis by simp
    qed
  next
    case (MFun f cs) note C = this
    then obtain ss lss where s:"s = Fun f ss"
      and  lcs:"length ss = length cs" and llss:"length lss = length cs"
      and lss:"ls = concat lss" and lsics:"\<And> i. i < length cs \<Longrightarrow> ss ! i =\<^sub>f (cs ! i, lss ! i)"
      using C by (auto elim: eqf_MFunE)
    show ?case
    proof (cases D)
      case (MVar y)
      with C show ?thesis using non_empty_empty_mult[of "mset ls"] by (auto dest!: eqfE)
    next
      case MHole
      with C obtain l' where [simp]: "ls' = [l']" "s = l'" by (auto dest!: eqf_MHoleE)
      from eqf_MFun_imp_strict_subt[OF C(2)] have "\<And>t. t \<in> set ls \<Longrightarrow> l' \<rhd> t"
        by auto
      then have "(mset ls, {#l'#}) \<in> mult {\<lhd>}"
        using one_step_implies_mult[of "{#l'#}" "mset ls" "{\<lhd>}" "{#}"]  by auto
      with MHole show ?thesis by simp
    next
      case (MFun g ds)
      with C obtain ts lss' where "s = Fun g ts"
        and  lds:"length ts = length ds" and llss':"length lss' = length ds"
        and lss':"ls' = concat lss'" and ls'ids:"\<And> i. i < length ds \<Longrightarrow> ts ! i =\<^sub>f (ds ! i, lss' ! i)"
        using C by (auto elim: eqf_MFunE)
      with s have [simp]: "g = f" "ts = ss" by auto
      have partlscs: "partition_holes ls cs = lss"
        by (metis eqfE(2) llss lsics lss partition_holes_concat_id)
      have partlsds:"partition_holes ls' ds = lss'"
        by (metis eqfE(2) llss' ls'ids lss' partition_holes_concat_id)
      let ?ol = "\<lambda>i. overlap' (cs ! i, lss ! i) (ds ! i, lss' ! i)"
      { fix i
        assume i:"i < length cs"
        then have "cs ! i \<in> set cs" by auto
        from C(1)[OF this lsics[OF i]] ls'ids i lds lcs
        have "(?ol i,  mset (lss ! i)) \<in> (mult {\<lhd>})\<^sup>=" by auto
      } note IH = this
      then have "\<forall>i < length cs. (map ?ol [0..<length cs] ! i , map mset lss ! i) \<in> (mult {\<lhd>})\<^sup>="
        using llss by auto
      with pointwise_mult_imp_mult[OF _ _ trans]
      have "(\<Sum>\<^sub># (mset (map ?ol [0..<length cs])), \<Sum>\<^sub># (mset (map mset lss))) \<in> (mult {\<lhd>})\<^sup>="
        using length_map llss map_upt_len_conv by (metis (lifting))
      then show ?thesis unfolding lss mset_concat_union MFun overlap'.simps
        using lss mset_map partlscs partlsds by metis
    qed
  qed
qed


text \<open>lemma which tells us, that a parallel rewrite step of s \<cdot> \<sigma> is either inside s i.e., we
  can split of a critical pair, or we can do the step completely inside \<sigma>\<close>
lemma par_rstep_mctxt_linear_subst:
  assumes "linear_term s"
  and "(s \<cdot> \<sigma>, t) \<in> par_rstep_mctxt R C infos"
  shows "(\<exists> \<tau>. t = s \<cdot> \<tau> \<and> (\<forall> x \<in> vars_term s. (\<sigma> x, \<tau> x) \<in> par_rstep R) \<or>
           (\<exists> D s' l r j C'. s = D\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l, r) \<in> R \<and> (s' \<cdot> \<sigma> = l \<cdot> \<tau>)
             \<and> j < length infos \<and> hole_pos D \<in> hole_poss C
             \<and> (D \<cdot>\<^sub>c \<sigma>)\<langle>r \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j (par_lefts infos)) \<and> t =\<^sub>f (C', remove_nth j (par_rights infos))))"
using assms
proof (induction s arbitrary: t C infos)
  case (Var x)
  then show ?case
    by (auto intro!: exI[of _ "\<lambda>y. t"] simp add: par_rstep_par_rstep_mctxt_conv par_rstep_mctxt_def)
next
  case (Fun f ss' t C infos)
  then have s:"Fun f ss' \<cdot> \<sigma> =\<^sub>f (C, par_lefts infos)" and t: "t =\<^sub>f (C, par_rights infos)"
    and steps : "par_conds R infos"
    unfolding par_rstep_mctxt_def by auto
  let ?ss = "map (\<lambda> s. s \<cdot> \<sigma>) ss'"
  show ?case
  proof (cases C)
    case (MHole)
    with t obtain info where infos: "infos = [info]" by (auto dest: eqf_MHoleE)
    from steps[unfolded infos] par_cond_imp_rrstep obtain l r \<tau> where 
      rule: "(l,r) \<in> R" "par_left info = l \<cdot> \<tau>" "par_right info = r \<cdot> \<tau>" 
      by (force simp: rrstep_def')
    show ?thesis unfolding MHole
    proof (intro exI disjI2 conjI)
      show "Fun f ss' = \<box>\<langle>Fun f ss'\<rangle>" by simp
      show "(l,r) \<in> R" by fact
      show "0 < length infos" unfolding infos by simp
      show "Fun f ss' \<cdot> \<sigma> = l \<cdot> \<tau>" using rule eqfE[OF s] infos MHole by auto 
      show "(\<box> \<cdot>\<^sub>c \<sigma>)\<langle>r \<cdot> \<tau>\<rangle> =\<^sub>f (mctxt_of_term (r \<cdot> \<tau>), remove_nth 0 (par_lefts infos))" unfolding infos
        by (auto simp add: remove_nth_def)
      show "t =\<^sub>f (mctxt_of_term (r \<cdot> \<tau>), remove_nth 0 (par_rights infos))" using infos
        rule eqfE[OF t] MHole
        by (auto simp add: remove_nth_def)
    qed auto
  next
    case C: (MFun g Cs)  
    then have gf [simp]: "g = f" using s by (auto dest: eqfE)
    let ?lss = "par_lefts infos" 
    let ?n = "length Cs" 
    let ?is = "[0..<?n]" 
    from s have eq: "Fun f ?ss =\<^sub>f (C, ?lss)" by auto
    from eqfE[OF eq] have num: "num_holes C = length infos" by auto
    define Infos where "Infos = partition_holes infos Cs" 
    from num[unfolded C] have infos: "infos = concat Infos" unfolding Infos_def by simp
    from eqfE[OF eq, unfolded MFun] have len: "length Infos = ?n" unfolding Infos_def by simp
    have ss: "?ss = map (\<lambda>i. fill_holes (Cs ! i) (par_lefts (Infos ! i))) ?is"
      using eqfE[OF eq] by (simp add: C Infos_def)
    define ts where "ts = map (\<lambda>i. fill_holes (Cs ! i) (par_rights (Infos ! i))) ?is" 
    have t_ts: "t = Fun f ts"  
      unfolding Infos_def ts_def using eqfE[OF t] by (simp add: C Infos_def)
    from arg_cong[OF ss, of length] have len_ss': "length ss' = ?n" by simp
    let ?p1 = "\<lambda> \<tau> i. ts ! i = ss' ! i \<cdot> \<tau> \<and> (\<forall> x \<in> vars_term (ss' ! i). (\<sigma> x, \<tau> x) \<in> par_rstep R)"
    let ?p2 = "\<lambda> \<tau> i. (\<exists> D s' l r j C'. ss' ! i = D\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l, r) \<in> R \<and> s' \<cdot> \<sigma> = l \<cdot> \<tau> \<and>
               j < length (Infos ! i) \<and> hole_pos D \<in> hole_poss (Cs ! i) \<and>
               (D \<cdot>\<^sub>c \<sigma>)\<langle>r \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j (par_lefts (Infos ! i))) \<and>
               ts ! i  =\<^sub>f (C', remove_nth j (par_rights (Infos ! i))))"
    let ?p = "\<lambda> \<tau> i. ?p1 \<tau> i \<or> ?p2 \<tau> i"
    { 
      fix i
      assume i: "i < length ss'" 
      hence mem: "ss' ! i \<in> set ss'" by auto
      from i Fun(2) have lin: "linear_term (ss' ! i)" by auto
      from i len_ss' have i': "i < ?n" by auto
      have "(ss' ! i \<cdot> \<sigma>, ts ! i) \<in> par_rstep_mctxt R (Cs ! i) (Infos ! i)" 
      proof (intro par_rstep_mctxtI)
        show "ts ! i =\<^sub>f (Cs ! i, par_rights (Infos ! i))" 
          using t[unfolded t_ts C] i' unfolding Infos_def
          by (auto dest: eqf_Fun_MFun)
        show "ss' ! i \<cdot> \<sigma> =\<^sub>f (Cs ! i, par_lefts (Infos ! i))" 
          using eq len_ss' i' unfolding Infos_def C
          by (auto dest: eqf_Fun_MFun)
        show "par_conds R (Infos ! i)" using i' steps num unfolding C Infos_def
          by (metis in_set_conv_nth length_map length_partition_by_nth num_holes.simps(3) partition_by_nth_nth_elem)
      qed
      from Fun.IH[OF mem lin this] have "\<exists> \<tau>. ?p \<tau> i" .
    }
    then have "\<forall>i. \<exists>\<tau>. i < length ss' \<longrightarrow> ?p \<tau> i" by blast
    from choice[OF this] obtain \<tau>s where \<tau>s: "\<And> i. i < length ss' \<Longrightarrow> ?p (\<tau>s i) i" by blast
    have len_ts: "length ts = ?n" using t t_ts C by (auto dest: eqf_Fun_MFun)
    show ?thesis
    proof (cases "\<exists> i. i < length ss' \<and> ?p2 (\<tau>s i) i")
      case True
      then obtain i where iss': "i < length ss'" and p2: "?p2 (\<tau>s i) i" by blast+
      from iss' have its': "i < length ts" using len_ts len_ss' by auto
      from p2 obtain D s' l r j C' where ssi: "ss' ! i = D\<langle>s'\<rangle>" and "is_Fun s'" "(l, r) \<in> R"
        and s':"s' \<cdot> \<sigma> = l \<cdot> \<tau>s i" and j:"j < length (Infos ! i)" and hpos: "hole_pos D \<in> hole_poss (Cs ! i)"
        and D\<sigma>r:"(D \<cdot>\<^sub>c \<sigma>)\<langle>r \<cdot> \<tau>s i\<rangle> =\<^sub>f (C', remove_nth j (par_lefts (Infos ! i)))"
        and ts'i:"ts ! i  =\<^sub>f (C', remove_nth j (par_rights (Infos ! i)))"
        by blast
      define bef where "bef = take i ss'"
      define aft where "aft = drop (Suc i) ss'"
      from id_take_nth_drop[OF iss', unfolded ssi] have ss':"ss' = bef @ D \<langle>s'\<rangle> # aft"
        using aft_def bef_def by blast
      have i_bef: "i = length bef" unfolding bef_def using iss' by auto
      let ?D = "More f bef D aft"
      let ?r = "(D \<cdot>\<^sub>c \<sigma>)\<langle>r \<cdot> \<tau>s i\<rangle>"
      let ?\<sigma> = "map (\<lambda> s. s \<cdot> \<sigma>)"
      let ?Cs = "Cs[i := C']"
      have D: "(?D \<cdot>\<^sub>c \<sigma>)\<langle>r \<cdot> \<tau>s i\<rangle> = Fun f (?ss[i := ?r])" using i_bef unfolding ss' by (simp add: list_update_append)
      have D2: "(?D \<cdot>\<^sub>c \<sigma>)\<langle>l \<cdot> \<tau>s i\<rangle> = Fun f ?ss" by (simp add: ss' s')
      show ?thesis unfolding ss'
      proof (rule exI[of _ "\<tau>s i"], rule disjI2, rule exI[of _ ?D], intro exI conjI)
        show "is_Fun s'" by fact
        show "(l, r) \<in> R" by fact
        show "s' \<cdot> \<sigma> = l \<cdot> \<tau>s i" by fact
        show "Fun f (bef @ D\<langle>s'\<rangle> # aft) = (More f bef D aft)\<langle>s'\<rangle>" by auto
        have "min (length Cs) i = i" using iss' len_ss' by auto
        then show "hole_pos (More f bef D aft) \<in> hole_poss C" using hpos C bef_def iss' len_ss' by auto
        from bef_def iss' have "length bef = i" by auto
        have iCs: "i < length Cs" using len_ss' iss' by auto
        let ?k = "sum_list (map length (take i Infos)) + j"
        show k:"?k < length infos" using j iCs unfolding infos
          by (simp add: concat_nth_length len)
        {
          fix f :: "('a,'b)par_info \<Rightarrow> ('a,'b)term" 
          have "remove_nth ?k (map f infos) = map f (remove_nth ?k infos)" 
            using k unfolding remove_nth_def by (simp add: drop_map take_map)
          also have "remove_nth ?k infos = concat (take i Infos) @ remove_nth j (Infos ! i) @ concat (drop (Suc i) Infos)" 
            unfolding infos using iCs[folded len] j 
            using concat_remove_nth by fastforce
          also have "\<dots> = concat (Infos [ i := remove_nth j (Infos ! i)])" using iCs[folded len] 
            by (simp add: upd_conv_take_nth_drop)
          finally have "remove_nth ?k (map f infos) = map f (concat (Infos [ i := remove_nth j (Infos ! i)]))" 
            by auto
        } note remove = this
        have remove_j: "remove_nth j (map g (Infos ! i)) = map g (remove_nth j (Infos ! i))" for g :: "('a,'b)par_info \<Rightarrow> ('a,'b)term" 
          using iCs[folded len] j unfolding remove_nth_def by (auto simp: take_map drop_map)
        show "(?D \<cdot>\<^sub>c \<sigma>)\<langle>r \<cdot> \<tau>s i\<rangle> =\<^sub>f (MFun f ?Cs, remove_nth ?k (par_lefts infos))" 
          unfolding remove D map_concat
          apply (intro eqf_MFunI)
          subgoal using len iCs by auto
          subgoal using len iCs ss' len_ss' by auto
          subgoal for k proof goal_cases
            case 1
            show ?case
            proof (cases "k = i")
              case True
              thus ?thesis using iss' len_ss' len D\<sigma>r by (simp add: remove_j)
            next
              case False
              have "map (\<lambda>s. s \<cdot> \<sigma>) ss' ! k =\<^sub>f (Cs ! k, par_lefts (Infos ! k))" 
                using eqfE[OF eq] 1 num unfolding C Infos_def by auto
              with False show ?thesis using 1 len by simp
            qed
          qed
          done
        show "t =\<^sub>f (MFun f ?Cs, remove_nth ?k (par_rights infos))"
          unfolding remove D2 map_concat t_ts
          apply (intro eqf_MFunI)
          subgoal using len iCs by auto
          subgoal using len iCs ss' len_ss' len_ts by auto
          subgoal for k proof goal_cases
            case 1
            show ?case
            proof (cases "k = i")
              case True
              thus ?thesis using iss' len_ss' len ts'i by (simp add: remove_j)
            next
              case False
              have "ts ! k =\<^sub>f (Cs ! k, par_rights (Infos ! k))" 
                using eqfE[OF t] t_ts 1 num unfolding C Infos_def by auto
              thus ?thesis using 1 len len_ss' False by simp
            qed
          qed
          done
      qed
    next
      case False
      with \<tau>s have \<tau>s: "\<And> i. i < length ss' \<Longrightarrow> ?p1 (\<tau>s i) i" by blast
      from Fun(2) have "is_partition (map vars_term ss')" by simp
      from subst_merge[OF this, of \<tau>s] obtain \<tau>
        where \<tau>: "\<And>i x. i < length ss' \<Longrightarrow> x \<in> vars_term (ss' ! i) \<Longrightarrow> \<tau> x = \<tau>s i x" by auto
      { fix i
        assume i: "i < length ss'"
        then have mem: "ss' ! i \<in> set ss'" by auto
        from \<tau>s[OF i] have p1: "?p1 (\<tau>s i) i" .
        have id: "ss' ! i \<cdot> (\<tau>s i) = ss' ! i \<cdot> \<tau>" by (rule term_subst_eq, rule \<tau>[OF i, symmetric])
        have "?p1 \<tau> i"
        proof (rule conjI[OF _ ballI])
          fix x
          assume x: "x \<in> vars_term (ss' ! i)"
          with p1 have step: "(\<sigma> x, \<tau>s i x) \<in> par_rstep R" by auto
          with \<tau>[OF i x] show "(\<sigma> x, \<tau> x) \<in> par_rstep R" by simp
        qed (insert p1[unfolded id], auto)
      } note p1 = this
      have p1: "\<And> i. i < length ss' \<Longrightarrow> ?p1 \<tau> i" by (rule p1)
      let ?ss = "map (\<lambda> s. s \<cdot> \<tau>) ss'"
      show ?thesis
      proof (rule exI[of _ \<tau>], rule disjI1, rule conjI[OF _ ballI])
        have "ts = ?ss" 
          by (intro nth_equalityI, insert len_ts len_ss' p1, auto)
        then show "t = Fun f ss' \<cdot> \<tau>" unfolding t_ts by auto
      next
        fix x
        assume "x \<in> vars_term (Fun f ss')"
        then obtain s where s: "s \<in> set ss'" and x: "x \<in> vars_term s" by auto
        from s[unfolded set_conv_nth] obtain i where i: "i < length ss'" and s: "s = ss' ! i" by auto
        from p1[OF i] x[unfolded s]
        show "(\<sigma> x, \<tau> x) \<in> par_rstep R" by blast
      qed
    qed
  qed (insert s t, auto dest: eqfE)
qed

lemma step_in_subst_imp_par_diamond:
  assumes "t = r \<cdot> \<sigma>"
  and "u = l \<cdot> \<tau>"
  and "\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> par_rstep R2"
  and "(l, r) \<in> R1"
  shows "\<exists>v. (t, v) \<in> par_rstep R2 \<and> (u, v) \<in> par_rstep R1"
proof -
  define \<delta> where "\<delta> = (\<lambda>x. if x \<in> vars_term l then \<tau> x else \<sigma> x)"
  have "\<forall>x\<in>vars_term l. \<tau> x = \<delta> x" by (auto simp: \<delta>_def)
  then have "l \<cdot> \<tau> = l \<cdot> \<delta>" using term_subst_eq_conv by auto
  moreover have "(l \<cdot> \<delta>, r \<cdot> \<delta>) \<in> par_rstep R1" using assms rstep_par_rstep by blast
  ultimately have "(l \<cdot> \<tau>, r \<cdot> \<delta>) \<in> par_rstep R1"  by auto
  moreover have "(r \<cdot> \<sigma>, r \<cdot> \<delta>) \<in> par_rstep R2"
  proof (rule all_ctxt_closed_subst_step)
    fix x
    assume "x \<in> vars_term r"
    show "(\<sigma> x, \<delta> x) \<in> par_rstep R2" using assms by (cases "x \<in> vars_term l") (auto simp: \<delta>_def)
  qed auto
  ultimately show ?thesis using assms par_rstep_rsteps by auto
qed

lemma par_rstep_mctxt_Var_diamond:
  fixes u t :: "('f, 'v) term"
  assumes "(Var x, t) \<in> par_rstep_mctxt R\<^sub>1 C infos"
    and "(Var x, u) \<in> par_rstep_mctxt R\<^sub>2 D infos'"
    and left_lin: "left_linear_trs R\<^sub>1" "left_linear_trs R\<^sub>2"
  shows "\<exists>v. (t, v) \<in> par_rstep R\<^sub>2 \<and> (u, v) \<in> par_rstep R\<^sub>1"
proof -
  let ?ss = "par_lefts infos" 
  let ?ts = "par_rights infos" 
  let ?us = "par_lefts infos'" 
  let ?vs = "par_rights infos'" 
  from assms have s: "Var x =\<^sub>f (C, ?ss)" and t: "t =\<^sub>f (C , ?ts)"
    and s2: "Var x =\<^sub>f (D, ?us)" and u:"u =\<^sub>f (D, ?vs)"
    and conds: "par_conds R\<^sub>1 infos" "par_conds R\<^sub>2 infos'"
      unfolding par_rstep_mctxt_def by auto
  then have "Var x = fill_holes C ?ss" and "length infos = num_holes C" and "Var x = fill_holes D ?us"
    by (auto dest: eqfE)
  then consider (MVar1) "C = MVar x" | (MVar2) "D = MVar x"
    | (MHole) "C = MHole" and "?ss = [Var x]" and "D = MHole"
    by (cases C; cases D; cases ?ss, auto) 
  then show ?thesis
  proof (cases)
    case MVar1
    from eqfE[OF t[unfolded MVar1]] have "t = Var x" by auto
    with assms have "(t, u) \<in> par_rstep_mctxt R\<^sub>2 D infos'" by auto
    then show ?thesis using par_rstep_par_rstep_mctxt_conv by blast
  next
    case MVar2
    from eqfE[OF u[unfolded MVar2]] have "u = Var x" by auto
    with assms u have "(u, t) \<in> par_rstep_mctxt R\<^sub>1 C infos" by auto
    then show ?thesis using par_rstep_par_rstep_mctxt_conv by blast
  next
    case MHole
    moreover have "?ts = [t]" using t  MHole by (auto elim: eqf_MHoleE)
    ultimately obtain l r \<sigma> where lr: "(l, r) \<in> R\<^sub>1" and l:"Var x = l \<cdot> \<sigma>" and r:"t = r \<cdot> \<sigma>"
      using rrstep_imp_rule_subst[OF par_conds_imp_rrstep[OF conds(1), of _ 0]] by fastforce
    from lr left_lin have "linear_term l" by (auto simp: left_linear_trs_def)
    from par_rstep_mctxt_linear_subst[OF this assms(2)[unfolded l]]
    obtain \<tau> where \<tau>:"u = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> par_rstep R\<^sub>2) \<or>
          (\<exists>E s'. l = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> hole_pos E \<in> hole_poss D)"
      by blast
    then show ?thesis
    proof
      assume "u = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> par_rstep R\<^sub>2)"
      with step_in_subst_imp_par_diamond r lr show ?thesis using par_rstep_rsteps by fastforce
    next
      assume "\<exists>E s'. l = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> hole_pos E \<in> hole_poss D"
      then obtain E l'' where E:"l = E\<langle>l''\<rangle>" and l'':"is_Fun l''" and "hole_pos E \<in> hole_poss D" by auto
      with MHole have "E = \<box>" by (cases E) auto
      with E l'' l show ?thesis by auto
    qed
  qed
qed

lemma parallel_closed_strongly_commute:
  assumes closed_1:"\<And>p q b. (b, q, p) \<in> critical_pairs ren R2 R1 \<Longrightarrow> \<exists>v. (q, v) \<in> par_rstep R2 \<and> (p, v) \<in> (rstep R1)\<^sup>*"
    and closed_2: "\<And>p q. (False, q, p) \<in> critical_pairs ren R1 R2 \<Longrightarrow> (q, p) \<in> par_rstep R1"
    and left_lin: "left_linear_trs R1" "left_linear_trs R2"
  shows "strongly_commute (par_rstep R1) (par_rstep R2)"
proof (rule strongly_commuteI)
  fix s t u
  let ?pR1 = "par_rstep R1"
  let ?pR2 = "par_rstep R2"
  assume "(s, t) \<in> ?pR1" and "(s, u) \<in> ?pR2"
  with par_rstep_par_rstep_mctxt_conv obtain C infos and D infos'
    where "(s, t) \<in> par_rstep_mctxt R1 C infos" and "(s, u) \<in> par_rstep_mctxt R2 D infos'"
    by metis
  then have "\<exists>v. (t, v) \<in> ?pR2 \<and> (u, v) \<in> (rstep R1)\<^sup>*"
  proof (induct "overlap' (C,par_lefts infos) (D, par_lefts infos')" arbitrary: C D infos s t infos' u rule: wf_induct_rule[OF wf_mult[OF SN_imp_wf[OF SN_supt]]])
    case (1 C D infos infos' s t u)
    then show ?case
    proof (induct s arbitrary: C D infos infos' t u)
      case (Var x)
      with par_rstep_mctxt_Var_diamond left_lin par_rstep_rsteps show ?case by fast
    next
      case (Fun f ss' C D infos infos' t u)
      let ?ss = "par_lefts infos" 
      let ?ts = "par_rights infos" 
      let ?vs = "par_lefts infos'" 
      let ?us = "par_rights infos'" 
      from Fun have s: "Fun f ss' =\<^sub>f (C, ?ss)" and t: "t =\<^sub>f (C , ?ts)"
        and s2: "Fun f ss' =\<^sub>f (D, ?vs)" and u:"u =\<^sub>f (D, ?us)"
        and par_conds1: "par_conds R1 infos" 
        and par_conds2: "par_conds R2 infos'" 
        unfolding par_rstep_mctxt_def by auto
      from par_conds_imp_rrstep[OF par_conds1]
      have steps1: "\<forall>i<length ?ss. (?ss ! i, ?ts ! i) \<in> rrstep R1" by auto
      from par_conds_imp_rrstep[OF par_conds2]
      have steps2: "\<forall>i<length ?vs. (?vs ! i, ?us ! i) \<in> rrstep R2" by auto
      show ?case
      proof (cases C)
        case MHole
        then have ss:"?ss = [Fun f ss']" using s by (auto elim: eqf_MHoleE)
        moreover have "?ts = [t]" using t MHole by (auto elim: eqf_MHoleE)
        ultimately have "(Fun f ss', t) \<in> rrstep R1" using steps1 by auto
        then obtain l r \<sigma> where lr: "(l, r) \<in> R1" and l:"Fun f ss' = l \<cdot> \<sigma>" and r:" t = r \<cdot> \<sigma> "
          using rrstep_imp_rule_subst by fastforce
        from lr left_lin have linl:"linear_term l" by (auto simp: left_linear_trs_def)
        show ?thesis
        proof (cases D)
          case (MFun g Ds)
          then have [simp]: "g = f" using s2 by (auto dest: eqfE)
          obtain vss where lDs:"length ss' = length Ds" and lvss:"length vss = length Ds"
            and vss:"?vs = concat vss" and vs'iD:"\<And> i. i < length Ds \<Longrightarrow> ss' ! i =\<^sub>f (Ds ! i, vss ! i)"
            using MFun s2 by (auto elim: eqf_MFunE)
          from u MFun obtain us' where [simp]: "u = Fun f us'" by (auto elim: eqf_MFunE)
          obtain uss where lDs2:"length us' = length Ds" and luss:"length uss = length Ds"
            and uss:"?us = concat uss" and us'iD:"\<And> i. i < length Ds \<Longrightarrow> us' ! i =\<^sub>f (Ds ! i, uss ! i)"
          using MFun u by (auto elim: eqf_MFunE)
          { fix i
            assume i:"i < length vss"
            then have "ss' ! i =\<^sub>f (Ds ! i, vss ! i)" using lvss vs'iD by auto
            moreover have "us' ! i =\<^sub>f (Ds ! i, uss ! i)" using luss us'iD i lvss by auto
            ultimately have "length (vss ! i) = length (uss ! i)"  by (auto dest!: eqfE)
          } note lvssuss = this
          from par_rstep_mctxt_linear_subst[OF linl Fun(4)[unfolded l]]
          obtain \<tau> where \<tau>:"u = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR2) \<or>
            (\<exists>E s' l' r' j D'. l = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R2 \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
              \<and> hole_pos E \<in> hole_poss D \<and> j < length infos'
              \<and> (E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs) \<and> u =\<^sub>f (D', remove_nth j ?us))"
            by blast
          then show ?thesis
          proof
            assume "u = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR2)"
            with step_in_subst_imp_par_diamond r lr show ?thesis using par_rstep_rsteps by fastforce
          next
            assume "\<exists>E s' l' r' j D'. l = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R2 \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
              \<and> hole_pos E \<in> hole_poss D \<and> j < length infos'
              \<and> (E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs) \<and> u =\<^sub>f (D', remove_nth j ?us)"
            then obtain E l'' l' r' j D' where E:"l = E\<langle>l''\<rangle>" and l'':"is_Fun l''" and lr':"(l', r') \<in> R2"
              and unifiable:"l'' \<cdot> \<sigma> = l' \<cdot> \<tau>" and hpos:"hole_pos E \<in> hole_poss D" and j:"j < length ?vs"
              and E\<sigma>r:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (D', remove_nth j ?vs)"
              and uD:"u =\<^sub>f (D', remove_nth j ?us)"
              by auto
            obtain \<mu>1 \<mu>2 \<delta> where mgu:"mgu_vd ren l'' l' = Some (\<mu>1, \<mu>2)"
              and \<sigma>:"\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" and \<tau>:"\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" and \<mu>:"l'' \<cdot> \<mu>1 = l' \<cdot> \<mu>2"
              using mgu_vd_complete[OF unifiable, of ren] by auto
            have inner:"hole_pos E \<noteq> []" using hpos MFun by auto
            have "(False, (E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, r \<cdot> \<mu>1) \<in> critical_pairs ren R1 R2"
              using lr lr' E l'' mgu inner by (force intro: critical_pairsI)
            from closed_2[OF this] have closed:"((E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, r \<cdot> \<mu>1) \<in> par_rstep R1" by auto
            from closed have "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, r \<cdot> \<sigma>) \<in> par_rstep R1" unfolding \<sigma> \<tau>
              using subst_closed_par_rstep by fastforce
            from par_rstep_mctxtE[OF this] obtain F infos3 where EF:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (F, par_lefts infos3)" 
              and "r \<cdot> \<sigma> =\<^sub>f (F, par_rights infos3)"
              and "par_conds R1 infos3" by auto
            then have Er: "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, r \<cdot> \<sigma>) \<in> par_rstep_mctxt R1 F infos3"
              unfolding par_rstep_mctxt_def by auto
            let ?cs = "par_lefts infos3" 
            let ?ol' = "overlap' (F, ?cs) (D', remove_nth j ?vs)"
            have "(?ol', mset (remove_nth j ?vs)) \<in> (mult {\<lhd>})\<^sup>="
              using overlap'_bounded[OF E\<sigma>r EF] overlap'_symmetric[OF EF E\<sigma>r] by auto
            moreover have "(mset (remove_nth j ?vs), mset ?vs) \<in> mult {\<lhd>}"
              using remove_nth_mult j by blast
            moreover have "overlap' (C, ?ss) (D, ?vs) = mset ?vs" using MFun MHole ss by auto
            ultimately have ol:"(?ol', overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}"
              unfolding mult_def by simp
            have "set (remove_nth j infos') \<subseteq> set infos'" using j unfolding remove_nth_def
              by (simp add: set_drop_subset set_take_subset)
            hence "par_conds R2 (remove_nth j infos')" using par_conds2 by auto 
            from E\<sigma>r uD this have Eu:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, u) \<in> par_rstep_mctxt R2 D' (remove_nth j infos')"
              unfolding par_rstep_mctxt_def using j by (auto simp: remove_map)
            from j have j: "j < length infos'" by simp
            from Fun(2)[OF ol[unfolded remove_map[OF j]] Er Eu]
            show ?thesis using r by auto
          qed
        next
          case MHole
          then have "?vs = [Fun f ss']" using s2 by (auto elim: eqf_MHoleE)
          moreover have "?us = [u]" using u MHole by (auto elim: eqf_MHoleE)
          ultimately have "(Fun f ss', u) \<in> rrstep R2" using steps2 by auto
          then obtain l' r' \<sigma>' where lr': "(l', r') \<in> R2" and l':"Fun f ss' = l' \<cdot> \<sigma>'"
            and r':" u = r' \<cdot> \<sigma>'"
            using rrstep_imp_rule_subst by fastforce
          with l have eq:"l' \<cdot> \<sigma>' = l \<cdot> \<sigma>" by auto
          from lr' left_lin have "linear_term l'" by (auto simp: left_linear_trs_def)
          from par_rstep_mctxt_linear_subst[OF this Fun(3)[unfolded l']]
          obtain \<tau> where \<tau>:"t = l' \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l'. (\<sigma>' x, \<tau> x) \<in> par_rstep R1) \<or>
            (\<exists>E s'. l' = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> hole_pos E \<in> hole_poss C)"
            by blast
          then show ?thesis
          proof
            assume "t = l' \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l'. (\<sigma>' x, \<tau> x) \<in> par_rstep R1)"
            with step_in_subst_imp_par_diamond r' lr' show ?thesis using par_rstep_rsteps by fastforce
          next
            assume "\<exists>E s'. l' = E\<langle>s'\<rangle> \<and> is_Fun s' \<and> hole_pos E \<in> hole_poss C"
            then obtain E s' where "l' = E\<langle>s'\<rangle>" and "is_Fun s'" and "hole_pos E \<in> hole_poss C" by blast
            with \<open>C = MHole\<close> have isFun:"is_Fun l'" by (cases E) auto
            from mgu_vd_complete[OF eq, of ren] obtain \<mu>1 \<mu>2 \<delta>
              where unif:"mgu_vd ren l' l = Some (\<mu>1, \<mu>2)"
              and \<sigma>:"\<sigma>' = \<mu>1 \<circ>\<^sub>s \<delta>" and \<sigma>':"\<sigma> = \<mu>2 \<circ>\<^sub>s \<delta>"
              by auto
            from critical_pairsI[OF lr' lr _ _ unif] isFun
            have "(True, r \<cdot> \<mu>2, r' \<cdot> \<mu>1) \<in> critical_pairs ren R2 R1" by force
            from closed_1[OF this] obtain w
              where "(r \<cdot> \<mu>2, w) \<in> par_rstep R2" and "(r' \<cdot> \<mu>1, w) \<in> (rstep R1)\<^sup>*" by auto
            with \<sigma> \<sigma>' have "(r \<cdot> \<sigma>, w \<cdot> \<delta>) \<in> par_rstep R2" "(r' \<cdot> \<sigma>', w \<cdot> \<delta>) \<in> (rstep R1)\<^sup>*"
              by (auto simp: subst_closed_par_rstep rsteps_closed_subst)
            with r r' show ?thesis using par_rsteps_rsteps by auto
          qed
        qed (insert s2, auto dest: eqfE)
      next
        case (MFun g Cs) note C = this
        then have [simp]: "g = f" using s by (auto dest: eqfE)
        define Infos where "Infos = partition_holes infos Cs" 
        from eqfE[OF s, unfolded C, simplified]  
        have len_infos: "sum_list (map num_holes Cs) = length infos" 
          and ss'_id: "ss' = map (\<lambda>i. fill_holes (Cs ! i) (par_lefts (Infos ! i))) [0..<length Cs]" 
          and len_Infos: "length Infos = length Cs" 
          and infos: "infos = concat Infos" 
          and len_Csi: "\<And> i. i < length Cs \<Longrightarrow> num_holes (Cs ! i) = length (Infos ! i)" 
          by (auto simp: Infos_def)
        define sss where "sss = map par_lefts Infos" 
        have lCs:"length ss' = length Cs" and lsss:"length sss = length Cs"
          and sss:"?ss = concat sss" and ss'iC:"\<And> i. i < length Cs \<Longrightarrow> ss' ! i =\<^sub>f (Cs ! i, sss ! i)"
          unfolding ss'_id sss_def using len_infos len_Infos infos by (auto simp: map_concat len_Csi)
        from s have "Fun f ss' = fill_holes C ?ss" "num_holes C = length ?ss" by (auto dest: eqfE)
        define tss where "tss = map par_rights Infos" 
        from t C obtain ts' where [simp]: "t = Fun f ts'" by (auto elim: eqf_MFunE)
        from eqfE[OF t[unfolded C this], simplified]
        have ts'_id: "ts' = map (\<lambda>i. fill_holes (Cs ! i) (par_rights (Infos ! i))) [0..<length Cs]" 
          by (auto simp: Infos_def)
        have lCs2:"length ts' = length Cs" and ltss:"length tss = length Cs"
          and tss:"?ts = concat tss" and ts'iC:"\<And> i. i < length Cs \<Longrightarrow> ts' ! i =\<^sub>f (Cs ! i, tss ! i)"
          unfolding ts'_id tss_def using len_infos len_Infos infos by (auto simp: map_concat len_Csi)
        show ?thesis
        proof (cases D)
          case MHole
          then have vs:"?vs = [Fun f ss']" using s2 by (auto elim: eqf_MHoleE)
          moreover have "?us = [u]" using u MHole by (auto elim: eqf_MHoleE)
          ultimately have "(Fun f ss', u) \<in> rrstep R2" using steps2 by auto
          then obtain l r \<sigma> where lr: "(l, r) \<in> R2" and l:"Fun f ss' = l \<cdot> \<sigma>" and r: "u = r \<cdot> \<sigma>"
            using rrstep_imp_rule_subst by fastforce
          from lr left_lin have "linear_term l" by (auto simp: left_linear_trs_def)
          from par_rstep_mctxt_linear_subst[OF this Fun(3)[unfolded l]]
          obtain \<tau> where \<tau>:"t = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR1) \<or>
            (\<exists>D s' l' r' j C'. l = D\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R1 \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
              \<and> hole_pos D \<in> hole_poss C \<and> j < length infos
              \<and> (D \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss) \<and> t =\<^sub>f (C', remove_nth j ?ts))"
            by blast
          then show ?thesis
          proof
            assume *:"t = l \<cdot> \<tau> \<and> (\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> ?pR1)"
            with step_in_subst_imp_par_diamond r lr show ?thesis using par_rstep_rsteps by fastforce
          next
            assume "\<exists>D s' l' r' j C'. l = D\<langle>s'\<rangle> \<and> is_Fun s' \<and> (l', r') \<in> R1 \<and> s' \<cdot> \<sigma> = l' \<cdot> \<tau>
              \<and> hole_pos D \<in> hole_poss C \<and> j < length infos
              \<and> (D \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss) \<and> t =\<^sub>f (C', remove_nth j ?ts)"
            then obtain E l'' l' r' j C' where E:"l = E\<langle>l''\<rangle>" and l'':"is_Fun l''" and lr':"(l', r') \<in> R1"
              and unifiable:"l'' \<cdot> \<sigma> = l' \<cdot> \<tau>" and hpos:"hole_pos E \<in> hole_poss C" and j:"j < length infos"
              and E\<sigma>r:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (C', remove_nth j ?ss)" and tCtsj:"t =\<^sub>f (C', remove_nth j ?ts)"
              by auto
            obtain \<mu>1 \<mu>2 \<delta> where mgu:"mgu_vd ren l'' l' = Some (\<mu>1, \<mu>2)"
              and \<sigma>:"\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" and \<tau>:"\<tau> = \<mu>2 \<circ>\<^sub>s \<delta>" and \<mu>:"l'' \<cdot> \<mu>1 = l' \<cdot> \<mu>2"
              using mgu_vd_complete[OF unifiable, of ren] by auto
            have inner:"hole_pos E \<noteq> []" using hpos C by auto
            have "(False, (E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, r \<cdot> \<mu>1) \<in> critical_pairs ren R2 R1"
              using lr lr' E l'' mgu inner by (force intro: critical_pairsI)
            with closed_1[OF this] obtain v where closed1:"((E \<cdot>\<^sub>c \<mu>1)\<langle>r' \<cdot> \<mu>2\<rangle>, v) \<in> ?pR2"
              and closed2:"(r \<cdot> \<mu>1, v) \<in> (rstep R1)\<^sup>*" by auto
            from closed1 have "((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep R2" unfolding \<sigma> \<tau>
              using subst_closed_par_rstep by fastforce
            from par_rstep_mctxtE[OF this] obtain F infos3 where EF:"(E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle> =\<^sub>f (F, par_lefts infos3)" and 
              "v \<cdot> \<delta> =\<^sub>f (F, par_rights infos3)"
              and "par_conds R2 infos3" by auto
            then have Ev:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, v \<cdot> \<delta>) \<in> par_rstep_mctxt R2 F infos3"
              unfolding par_rstep_mctxt_def by auto
            let ?cs = "par_lefts infos3" 
            let ?ol' = "overlap' (C', remove_nth j ?ss) (F, ?cs)"
            have "(?ol', mset (remove_nth j ?ss)) \<in> (mult {\<lhd>})\<^sup>=" using overlap'_bounded[OF E\<sigma>r EF] by auto
            moreover have "(mset (remove_nth j ?ss), mset ?ss) \<in> mult {\<lhd>}" using remove_nth_mult j
              by (metis length_map)
            moreover have "overlap' (C, ?ss) (D, ?vs) = mset ?ss" using C MHole vs by auto
            ultimately have ol:"(?ol', overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}" unfolding mult_def by simp
            have "set (remove_nth j infos) \<subseteq> set infos" unfolding remove_nth_def
              by (simp add: set_drop_subset set_take_subset)
            hence "par_conds R1 (remove_nth j infos)" using par_conds1 by auto 
            from E\<sigma>r tCtsj this
            have Et:"((E \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, t) \<in> par_rstep_mctxt R1 C' (remove_nth j infos)"
              unfolding par_rstep_mctxt_def using j by (auto simp: remove_map)
            from Fun(2)[OF ol[unfolded remove_map[OF j]] Et Ev]
            show ?thesis using r rsteps_closed_subst[OF closed2, of \<delta>] unfolding \<sigma> by auto
          qed
        next
          case (MFun h Ds) note D = this
          then have [simp]: "h = f" using s2 by (auto dest: eqfE)
          define Infos' where "Infos' = partition_holes infos' Ds" 
          from eqfE[OF s2, unfolded D, simplified]  
          have len_infos': "sum_list (map num_holes Ds) = length infos'" 
            and ss'_id': "ss' = map (\<lambda>i. fill_holes (Ds ! i) (par_lefts (Infos' ! i))) [0..<length Ds]" 
            and len_Infos': "length Infos' = length Ds" 
            and infos': "infos' = concat Infos'" 
            and len_Dsi: "\<And> i. i < length Ds \<Longrightarrow> num_holes (Ds ! i) = length (Infos' ! i)" 
            by (auto simp: Infos'_def)
          define vss where "vss = map par_lefts Infos'" 
          have lDs:"length ss' = length Ds" and lvss:"length vss = length Ds"
            and vss:"?vs = concat vss" and vs'iD:"\<And> i. i < length Ds \<Longrightarrow> ss' ! i =\<^sub>f (Ds ! i, vss ! i)"
            unfolding ss'_id' vss_def using len_infos' len_Infos' infos' by (auto simp: map_concat len_Dsi)
          from s2 have "Fun f ss' = fill_holes D ?vs" "num_holes D = length ?vs" by (auto dest: eqfE)

          define uss where "uss = map par_rights Infos'" 
          from u D obtain us' where [simp]: "u = Fun f us'" by (auto elim: eqf_MFunE)
          from eqfE[OF u[unfolded D this], simplified]
          have us'_id: "us' = map (\<lambda>i. fill_holes (Ds ! i) (par_rights (Infos' ! i))) [0..<length Ds]" 
            by (auto simp: Infos'_def)
          have lDs2:"length us' = length Ds" and luss:"length uss = length Ds"
            and uss:"?us = concat uss" and us'iD:"\<And> i. i < length Ds \<Longrightarrow> us' ! i =\<^sub>f (Ds ! i, uss ! i)"
            unfolding us'_id uss_def using len_infos' len_Infos' infos' by (auto simp: map_concat len_Dsi)

          { fix i
            assume i:"i < length ss'"
            then have s: "ss' ! i \<in> set ss'" using nth_mem by blast
            from i ts'iC lCs lCs2 have ts'i:"ts' ! i =\<^sub>f (Cs ! i, tss ! i)" by auto
            from i us'iD lDs lDs2 have us'i:"us' ! i =\<^sub>f (Ds ! i, uss ! i)" by auto
            have "sss ! i = partition_holes ?ss Cs ! i"
              by (metis eqfE(2) lsss partition_holes_concat_id ss'iC sss)
            moreover have " vss ! i = partition_holes ?vs Ds ! i"
              by (metis eqfE(2) lvss partition_holes_concat_id vs'iD vss)
            ultimately have "overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i) \<in>#
              mset (map (\<lambda>i. overlap' (Cs ! i, partition_holes ?ss Cs ! i) (Ds ! i, partition_holes ?vs Ds ! i)) [0..<length Cs])"
              unfolding sss vss using i lCs by fastforce
            then have ol:"overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i) \<subseteq># overlap' (C, ?ss) (D, ?vs)"
              unfolding C MFun by (simp add: in_mset_subset_Union)
            { fix C' D' s' t' u' infos2 infos2'
              assume 1:"(overlap' (C', par_lefts infos2) (D', par_lefts infos2'), overlap' (Cs ! i, sss ! i) (Ds ! i, vss ! i)) \<in> mult {\<lhd>}"
              and 2: "(s', t') \<in> par_rstep_mctxt R1 C' infos2" "(s', u') \<in> par_rstep_mctxt R2 D' infos2'"
              have "trans {\<lhd>}" unfolding trans_def using supt_trans by auto
              with mult_subset_mult ol 1 have "(overlap' (C', par_lefts infos2) (D', par_lefts infos2'), overlap' (C, ?ss) (D, ?vs)) \<in> mult {\<lhd>}" by blast
              from Fun(2)[OF this 2]  have "\<exists>v. (t', v) \<in> ?pR2 \<and> (u', v) \<in> (rstep R1)\<^sup>*" .
            } note m = this

            from i have iI: "i < length Infos" using len_Infos lCs by auto
            have "Ball (set Infos) (par_conds R1)" using par_conds1 unfolding infos by auto
            with iI have parR1: "par_conds R1 (Infos ! i)" by auto
            have id: "par_lefts (Infos ! i) = map par_lefts Infos ! i \<and> par_rights (Infos ! i) = map par_rights Infos ! i"
              using iI by auto 
            with ss'iC i lCs ts'i parR1
            have ssts:"(ss' ! i, ts' ! i) \<in> par_rstep_mctxt R1 (Cs ! i) (Infos ! i)"
              by (intro par_rstep_mctxtI, auto simp: tss_def sss_def)

            from i have iI': "i < length Infos'" using len_Infos' lDs by auto
            have "Ball (set Infos') (par_conds R2)" using par_conds2 unfolding infos' by auto
            with iI' have parR2: "par_conds R2 (Infos' ! i)" by auto
            have id': "par_lefts (Infos' ! i) = map par_lefts Infos' ! i \<and> par_rights (Infos' ! i) = map par_rights Infos' ! i"
              using iI' by auto 
            with vs'iD i lDs us'i parR2
            have ssus:"(ss' ! i, us' ! i) \<in> par_rstep_mctxt R2 (Ds ! i) (Infos' ! i)"
              by (intro par_rstep_mctxtI, auto simp: uss_def vss_def) 

            have "\<exists>v. (ts' ! i, v) \<in> par_rstep R2 \<and> (us' ! i, v) \<in> (rstep R1)\<^sup>*" 
              by (rule Fun(1)[OF s _ ssts ssus], rule m, insert id id', auto simp: vss_def sss_def)
          }
          then obtain v
          where v: "\<And>i. i < length ts' \<Longrightarrow> (ts' ! i, v i) \<in> ?pR2 \<and> (us' ! i, v i) \<in> (rstep R1)\<^sup>*"
            using lCs lCs2 by metis
          let ?vs' = "map v [0..<length ts']"
          from v have v1:"(Fun f ts', Fun f ?vs') \<in> ?pR2" by auto
          from v have *:"\<And>i. i < length us' \<Longrightarrow> (us' ! i, v i) \<in> (rstep R1)\<^sup>*"
            using par_rsteps_rsteps lCs lCs2 lDs lDs2  by auto
          have "length us' = length ?vs'" using lCs lCs2 lDs lDs2 by auto
          with * args_rsteps_imp_rsteps[OF this] have v2:"(Fun f us', Fun f ?vs') \<in> (rstep R1)\<^sup>*"
            by auto
          from v1 v2 show ?thesis by auto
        qed (insert s2, auto dest: eqfE)
      qed (insert s, auto dest: eqfE)
    qed
  qed
  then show "\<exists>v. (t, v) \<in> ?pR2\<^sup>= \<and> (u, v) \<in> ?pR1\<^sup>*" by (auto simp: par_rsteps_rsteps)
qed

corollary parallel_closed_commute:
  assumes closed_1:"\<And>p q b. (b, q, p) \<in> critical_pairs ren R2 R1 \<Longrightarrow> \<exists>v. (q, v) \<in> par_rstep R2 \<and> (p, v) \<in> (rstep R1)\<^sup>*"
    and closed_2: "\<And>p q. (False, q, p) \<in> critical_pairs ren R1 R2 \<Longrightarrow> (q, p) \<in> par_rstep R1"
    and left_lin: "left_linear_trs R1" "left_linear_trs R2"
  shows "commute (rstep R1) (rstep R2)"
proof
  fix x y\<^sub>1 y\<^sub>2
  assume "(x, y\<^sub>1) \<in> (rstep R1)\<^sup>*" and "(x, y\<^sub>2) \<in> (rstep R2)\<^sup>*"
  then have "(x, y\<^sub>1) \<in> (par_rstep R1)\<^sup>*" and "(x, y\<^sub>2) \<in> (par_rstep R2)\<^sup>*"
    using rtrancl_mono[OF rstep_par_rstep] by auto
  from commuteE[OF strongly_commute_imp_commute[OF parallel_closed_strongly_commute[OF assms]] this]
  obtain z where "(y\<^sub>1, z) \<in> (par_rstep R2)\<^sup>* \<and> (y\<^sub>2, z) \<in> (par_rstep R1)\<^sup>*" by fast
  then show "\<exists>z. (y\<^sub>1, z) \<in> (rstep R2)\<^sup>* \<and> (y\<^sub>2, z) \<in> (rstep R1)\<^sup>*"
    using rtrancl_mono[OF par_rstep_rsteps] rtrancl_idemp by auto
qed

corollary parallel_closed_imp_CR:
  assumes "\<And>p q. (False, q, p) \<in> critical_pairs ren R R \<Longrightarrow> (q, p) \<in> par_rstep R"
    and "\<And>p q. (True, q, p) \<in> critical_pairs ren R R \<Longrightarrow> \<exists>v. (q, v) \<in> par_rstep R \<and> (p, v) \<in> (rstep R)\<^sup>*"
    and "left_linear_trs R"
  shows "CR (rstep R)"
proof -
  { fix p q b
    assume "(b, q, p) \<in> critical_pairs ren R R"
    then have "\<exists>v. (q, v) \<in> par_rstep R \<and> (p, v) \<in> (rstep R)\<^sup>*"
      using assms(1,2) by (cases b) auto
  } moreover
  { fix p q
    assume "(False, q, p) \<in> critical_pairs ren R R"
    with assms(1) have "(q, p) \<in> par_rstep R" by auto
  }
  ultimately have "commute (rstep R) (rstep R)"
    using parallel_closed_commute assms(3) by blast
  then show ?thesis using CR_iff_self_commute by auto
qed

end
