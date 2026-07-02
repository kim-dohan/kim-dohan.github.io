(*
Author:  Florian Meßner <florian.messner@outlook.com> (2020)
License: LGPL (see file COPYING.LESSER)
*)
theory Left_Inline_Conditions
  imports
    Conditional_Rewriting
begin

definition
  "left_inline i \<rho> =
      (let
        cs = conds \<rho>;
        (s, t) = cs ! i;
        \<sigma> = subst (the_Var s) t;
        cs' = take i cs @ drop (Suc i) cs
      in
      ((clhs \<rho> \<cdot> \<sigma>, crhs \<rho>), map (\<lambda>(s, t). (s, t \<cdot> \<sigma>)) cs'))"

lemma left_inline:
  assumes "i < length cs" and "cs ! i = (Var x, t)"
  shows "left_inline i ((l, r), cs) =
    ((l \<cdot> subst x t, r), map (\<lambda>(u, v). (u, v \<cdot> subst x t)) (take i cs @ drop (Suc i) cs))"
  using assms
  by (auto simp: left_inline_def Let_def)

definition "reachable_set R = {(u, v) . (\<exists>\<sigma>. (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*)}"

lemma linear_ctxt_subt:
  assumes "x \<in> vars_term t"
    and "x \<in> vars_ctxt C"
    and "linear_term (C\<langle>t\<rangle>)"
  shows "False"
  using assms
proof (induction C)
  case Hole
  then show ?case by auto
next
  case (More f xs C ys)
  have "linear_term C\<langle>t\<rangle>" using More by auto
  have x_in_Ct: "x \<in> vars_term C\<langle>t\<rangle>" using More
    by (simp add: vars_term_ctxt_apply)
  from More consider "\<exists>t \<in> set xs. x \<in> vars_term t" | "x \<in> (\<Union>t \<in> set ys. vars_term t)" | "x \<in> vars_ctxt C" by auto
  then show ?case
  proof (cases)
    case 1
    obtain i where "i < length xs" and "x \<in> vars_term (xs ! i)"
      using 1
      using in_set_idx by force
    moreover have "x \<in> vars_term ((xs @ [C\<langle>t\<rangle>] @ ys) ! i)"
      using calculation
      by (simp add: nth_append)
    moreover have "i < length (xs @ [C\<langle>t\<rangle>] @ ys)" using calculation by auto
    moreover obtain j where "i < j" and "j < length (xs @ [C\<langle>t\<rangle>] @ ys)" and "C\<langle>t\<rangle> = (xs @ [C\<langle>t\<rangle>] @ ys) ! j"
      using calculation
      using append.assoc by auto
    ultimately have "(j<length (map vars_term (xs @ [C\<langle>t\<rangle>] @ ys)) \<and>
           i<j \<and> map vars_term (xs @ [C\<langle>t\<rangle>] @ ys) ! i \<inter>
                 map vars_term (xs @ [C\<langle>t\<rangle>] @ ys) ! j \<noteq>
                 {})"
      using x_in_Ct \<open>i < length (xs @ [C\<langle>t\<rangle>] @ ys)\<close> \<open>j < length (xs @ [C\<langle>t\<rangle>] @ ys)\<close> nth_map
      by (metis IntI empty_iff length_map)
    then have "\<not> is_partition (map vars_term (xs @ [C\<langle>t\<rangle>] @ ys))"
       unfolding is_partition_def by blast
    then have "\<not> linear_term (More f xs C ys)\<langle>t\<rangle>"
      by simp
    then show ?thesis using More
      by auto
  next
    case 2
    obtain l where l: "l < length ys" and "x \<in> vars_term (( ys) ! l)"
      using 2 in_set_idx by force
    then have "x \<in> vars_term ((xs @ [C\<langle>t\<rangle>] @ ys) ! (length (xs @ [C\<langle>t\<rangle>]) + l))"
      by (metis append_assoc nth_append_length_plus)
    moreover have "length (xs @ [C\<langle>t\<rangle>]) \<le> (length (xs @ [C\<langle>t\<rangle>]) + l)"
      by simp
    moreover have "(length (xs @ [C\<langle>t\<rangle>]) + l) < length (xs @ [C\<langle>t\<rangle>] @ ys)"
      by (simp add: l)
    moreover obtain j where "j < length (xs @ [C\<langle>t\<rangle>]) + l" and "j < length (xs @ [C\<langle>t\<rangle>] @ ys)" and "C\<langle>t\<rangle> = (xs @ [C\<langle>t\<rangle>] @ ys) ! j"
      using calculation
      by (metis (no_types, opaque_lifting) add.commute add_Suc append_Cons le_add2 le_imp_less_Suc length_append length_append_singleton nth_append_length)
    ultimately have "((length (xs @ [C\<langle>t\<rangle>]) + l)<length (map vars_term (xs @ [C\<langle>t\<rangle>] @ ys)) \<and>
           j<(length (xs @ [C\<langle>t\<rangle>]) + l) \<and> map vars_term (xs @ [C\<langle>t\<rangle>] @ ys) ! j \<inter>
                 map vars_term (xs @ [C\<langle>t\<rangle>] @ ys) ! (length (xs @ [C\<langle>t\<rangle>]) + l) \<noteq>
                 {})"
      using x_in_Ct nth_map
      by (metis (no_types, opaque_lifting) IntI empty_iff length_map)
    then have "\<not> is_partition (map vars_term (xs @ [C\<langle>t\<rangle>] @ ys))"
       unfolding is_partition_def by blast
    then have "\<not> linear_term (More f xs C ys)\<langle>t\<rangle>"
      by simp
    then show ?thesis using More
      by auto
  next
    case 3
    then show ?thesis
      using More by auto
  qed
qed


lemma linear_ctxt:
  assumes "p \<in> poss s"
    and "s |_ p = Var x"
    and "linear_term s"
  shows "x \<notin> vars_ctxt (ctxt_of_pos_term p s)"
  using assms linear_ctxt_subt
  by (metis ctxt_supt_id term.set_intros(3))

lemma split_subst:
  fixes x::'v and \<sigma>::"'v \<Rightarrow> ('f,'v) term"
  assumes "\<sigma> x = t"
    and "p \<in> poss s"
    and "s |_ p = Var x"
    and "linear_term s"
  shows "\<exists>\<rho>. s \<cdot> \<sigma> = replace_at (s \<cdot> \<rho>) p (\<sigma> x)"
proof-
  obtain \<rho> where \<rho>: "\<rho> = (\<lambda>z. if z = x then Var x else \<sigma> z)"
    by auto
  then have \<rho>\<^sub>y: "\<forall>y \<noteq> x. Var y \<cdot> \<rho> = Var y \<cdot> \<sigma>"
    by auto
  have \<rho>\<^sub>x: "Var x \<cdot> \<rho> = Var x"
    using \<rho> by auto
  obtain \<tau> where \<tau>: "\<tau> = subst x t"
    by blast
  then have \<tau>\<^sub>y: "\<forall>y \<noteq> x. Var y \<cdot> \<tau> = Var y"
    unfolding subst_def by auto
  have \<tau>\<^sub>x: "Var x \<cdot> \<tau> = Var x \<cdot> \<sigma>"
    using assms \<tau> by auto
  then have rep: "s \<cdot> \<sigma> = replace_at (s \<cdot> \<sigma>) p (Var x \<cdot> \<sigma>)"
    using assms
    by (simp add: replace_at_ident)
  have "x \<notin> vars_ctxt (ctxt_of_pos_term p s)"
    using linear_ctxt[of p s x] assms by auto
  then have "ctxt_of_pos_term p (s \<cdot> \<sigma>) = ctxt_of_pos_term p (s \<cdot> \<rho>)"
    using assms
    by (metis \<rho> ctxt_of_pos_term_subst ctxt_subst_eq)
  then have "s \<cdot> \<sigma> = replace_at (s \<cdot> \<rho>) p (Var x \<cdot> \<sigma>)"
    using assms rep by auto
  then show ?thesis by auto
qed

lemma linear_term_subst_replace_at:
  assumes "linear_term s"
    and p: "p \<in> poss s"
    and p_Var: "s |_ p = Var x"
  shows "s \<cdot> (subst x t) = replace_at s p t"
proof-
  have "(ctxt_of_pos_term p s) \<cdot>\<^sub>c (subst x t) = ctxt_of_pos_term p s"
  using assms linear_ctxt[of p s x]
  by (metis Term.term.simps(17) ctxt_subst_eq ctxt_subst_id empty_iff insert_iff eval_term.simps(1) subst_ident)
  then show ?thesis
    using assms
    by (metis ctxt_supt_id eval_term.simps(1) subst_apply_term_ctxt_apply_distrib subst_simps(1))
qed


lemma csteps_n_ctxt:
  assumes "(s, t) \<in> (cstep_n R n)\<^sup>*"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (cstep_n R n)\<^sup>*"
  using assms
  by (meson cstep_n_ctxt rtrancl_map)

lemma csteps_n_subst:
  assumes "(s, t) \<in> (cstep_n R n)\<^sup>*"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
  using assms
  by (induction rule: rtrancl.induct)
    (auto simp: cstep_n_rstep_trs_n_conv rsteps_closed_subst rtrancl.rtrancl_into_rtrancl)

lemma csteps_n_Suc:
  assumes "(s, t) \<in> (cstep_n R n)\<^sup>*"
  shows "(s, t) \<in> (cstep_n R (Suc n))\<^sup>*"
  using assms
  by (metis cstep_n_Suc_mono rtrancl_eq_or_trancl trancl_mono)

lemma csteps_n_Fun_subst:
assumes "\<And> x. x \<in> set xs \<longrightarrow> (x, x \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
shows "(Fun f xs, Fun f xs \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
proof-
  have "Fun f xs \<cdot> \<sigma> = Fun f (map (\<lambda>x. x \<cdot> \<sigma>) xs)"
    by simp
  moreover have "(Fun f xs, Fun f (map (\<lambda>x. x \<cdot> \<sigma>) xs)) \<in> (cstep_n R n)\<^sup>*"
    using assms
    by (induction n arbitrary: xs)
      (auto simp: map_idI args_rsteps_imp_rsteps cstep_n_rstep_trs_n_conv)
  ultimately show ?thesis using assms
    by simp
qed

lemma csteps_n_Fun_subst_subst:
  fixes xs ::"('f, 'v) term list" and f:: "'f" and \<tau>::"'v \<Rightarrow> ('f, 'v) Term.term"
assumes "\<And> x. x \<in> set xs \<longrightarrow> (x \<cdot> \<tau>, x \<cdot> \<sigma> \<cdot> \<tau>) \<in> (cstep_n R n)\<^sup>*"
shows "(Fun f xs \<cdot> \<tau>, Fun f xs \<cdot> \<sigma> \<cdot> \<tau>) \<in> (cstep_n R n)\<^sup>*"
proof-
  have "Fun f xs \<cdot> \<sigma> = Fun f (map (\<lambda>x. x \<cdot> \<sigma>) xs)"
    by simp
  moreover have "(Fun f xs \<cdot> \<tau>, Fun f (map (\<lambda>x. x \<cdot> \<sigma>) xs) \<cdot> \<tau>) \<in> (cstep_n R n)\<^sup>*"
    using assms
    by (induction n arbitrary: xs)
      (auto simp: map_idI args_rsteps_imp_rsteps cstep_n_rstep_trs_n_conv)
  ultimately show ?thesis using assms
    by simp
qed

lemma left_inline_cond:
  fixes R :: "('f, 'v) ctrs"
  assumes cstep: "(u, v) \<in> (cstep_n R n)\<^sup>*"
    and "\<rho> \<in> R"
    and i: "i < length (conds \<rho>)" "conds \<rho> ! i = (Var x, t)"
    and lin: "linear_term (clhs \<rho>)"
    and vars: "x \<notin> vars_term (crhs \<rho>) \<union> vars_term t \<union>
      \<Union>(vars_term ` lhss (set (take i (conds \<rho>)))) \<union>
      \<Union>(vars_term ` lhss (set (drop (Suc i) (conds \<rho>))))"
  shows "(u, v) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) n)\<^sup>*"
  using assms
proof (induction n arbitrary: u v )
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc(2,3-7)  show ?case
  proof(induction rule: rtrancl.induct)
    case (rtrancl_refl a)
    then show ?case by auto
  next
    case (rtrancl_into_rtrancl a b c)
    then obtain C l r \<sigma> cs where
      b: "b = C\<langle>l \<cdot> \<sigma>\<rangle>"  and c: "c = C\<langle>r \<cdot> \<sigma>\<rangle>"
      and rl: "((l, r), cs) \<in> R"
      and cs: "(\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*)"
      using cstep_n_Suc[of R n]
      by auto
    then have cs_R': "(\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) n)\<^sup>*)"
      using Suc assms by auto
    consider "((l, r), cs) = \<rho>" | "((l, r), cs) \<in> (insert (left_inline i \<rho>) (R - {\<rho>}))"
      using rl by auto
    then show ?case
    proof (cases)
      case 1
      obtain l' r' cs' where inlined: "((l',r'),cs') = (left_inline i \<rho>)"
        by (metis crule_cases)
      have cs': "(\<forall> (s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) n)\<^sup>*)"
      proof
        fix s\<^sub>i t\<^sub>i
        have "(s\<^sub>i, t\<^sub>i) \<in> set cs' \<Longrightarrow> \<exists>(u,v)\<in>set cs. (s\<^sub>i, t\<^sub>i) = (u, v \<cdot> (subst x t))"
          using inlined 1 left_inline[of i cs x t l r]  using assms apply auto
          using fst_conv in_set_takeD snd_conv apply fastforce
          using case_prod_beta' in_set_dropD by fastforce
        then obtain u v where uv: "(s\<^sub>i, t\<^sub>i) \<in> set cs' \<Longrightarrow> (u,v)\<in>set cs \<and> (s\<^sub>i, t\<^sub>i) = (u, v \<cdot> (subst x t))" by blast
        then have "(s\<^sub>i, t\<^sub>i) \<in> set cs' \<Longrightarrow> (u \<cdot> \<sigma>, v \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) n)\<^sup>*"
          using cs_R' by auto
        moreover have "(s\<^sub>i, t\<^sub>i) \<in> set cs' \<Longrightarrow> (v \<cdot> \<sigma>, (v \<cdot> (subst x t)) \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) n)\<^sup>*"
        proof (induction v)
          case (Var y)
          then show ?case
          proof (cases "y = x")
            case True
            then show ?thesis
              by (metis (no_types, lifting) "1" Suc(4) case_prod_beta cs_R' fst_conv i(2) nth_mem prod.sel(2) eval_term.simps(1) subst_simps(1))
          next
            case False
            then show ?thesis
              by (metis Term.term.simps(17) empty_iff insert_iff rtrancl.rtrancl_refl subst_ident)
          qed
        next
          case (Fun f xs)
          then show ?case
            using csteps_n_Fun_subst_subst[of xs \<sigma> "subst x t" "insert (left_inline i \<rho>) (R - {\<rho>})" n f]
            by auto
        qed
        ultimately have "(s\<^sub>i, t\<^sub>i) \<in> set cs' \<Longrightarrow> (u \<cdot> \<sigma>, (v \<cdot> (subst x t)) \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) n)\<^sup>*"
          by auto
        then show "(s\<^sub>i, t\<^sub>i) \<in> set cs' \<Longrightarrow> (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) n)\<^sup>*"
          using uv by auto
      qed

      from 1 show ?thesis
      proof (cases  "\<exists>p \<in> poss l. l |_ p = Var x")
        case True
        then obtain p where p: "p \<in> poss l" and p_Var: "l |_ p = Var x"
          by blast
        then obtain \<sigma>' where  \<sigma>_split: "l \<cdot> \<sigma> = replace_at (l \<cdot> \<sigma>') p (Var x \<cdot> \<sigma>)"
          using split_subst[of \<sigma> x "\<sigma> x" p l ] assms "1"
          by auto

        have "(Var x, t) \<in> (set cs)"
          using assms 1
          using nth_mem by fastforce
        then have "(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) ( n))\<^sup>*"
          using cs_R' by auto
        then have "(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))\<^sup>*"
          using csteps_n_Suc by auto
        then have "(replace_at (l \<cdot> \<sigma>') p (Var x \<cdot> \<sigma>), replace_at (l \<cdot> \<sigma>') p (t \<cdot> \<sigma>)) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))\<^sup>*"
          by (simp add: csteps_n_ctxt)

        have "replace_at (l \<cdot> \<sigma>') p (t \<cdot> \<sigma>) = (replace_at l p t) \<cdot> \<sigma>"
          using p
          by (metis \<sigma>_split ctxt_of_pos_term_hole_pos ctxt_of_pos_term_subst hole_pos_ctxt_of_pos_term poss_imp_subst_poss subst_apply_term_ctxt_apply_distrib)

        from inlined have r': "r = r'" using left_inline
          by (smt "1" fst_conv left_inline_def old.prod.case rtrancl_into_rtrancl.prems snd_conv)
        from inlined have l': "l' = l \<cdot> (subst x t)" using left_inline[of i cs x t l r] rtrancl_into_rtrancl.prems 1
          by (metis fst_conv snd_conv)

        have "l \<cdot> (subst x t) = replace_at l p t"
          using linear_term_subst_replace_at[of l p x t]
            p p_Var lin rl 1
          by auto
        then have l_t_to_r: "(((ctxt_of_pos_term p l)\<langle>t\<rangle>, r), cs') \<in> insert (left_inline i \<rho>) (R - {\<rho>})"
          using inlined  l' r' by simp

        have "((replace_at l p t) \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))"
            using l_t_to_r p p_Var  r' inlined l' cs'
              cstep_n_SucI[of "replace_at l p t" r cs' "insert (left_inline i \<rho>) (R - {\<rho>})" \<sigma> n "(replace_at l p t) \<cdot> \<sigma>" \<box> "r \<cdot> \<sigma>"]
            by auto

        have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))\<^sup>*"
          by (metis (no_types, lifting)
              \<open>((ctxt_of_pos_term p (l \<cdot> \<sigma>'))\<langle>Var x \<cdot> \<sigma>\<rangle>, (ctxt_of_pos_term p (l \<cdot> \<sigma>'))\<langle>t \<cdot> \<sigma>\<rangle>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))\<^sup>*\<close>
              \<open>((ctxt_of_pos_term p l)\<langle>t\<rangle> \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n)\<close> \<open>(ctxt_of_pos_term p (l \<cdot> \<sigma>'))\<langle>t \<cdot> \<sigma>\<rangle> = (ctxt_of_pos_term p l)\<langle>t\<rangle> \<cdot> \<sigma>\<close> \<sigma>_split csteps_n_ctxt rtrancl.rtrancl_into_rtrancl)
        then have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))\<^sup>*"
          by (smt
              \<open>((ctxt_of_pos_term p (l \<cdot> \<sigma>'))\<langle>Var x \<cdot> \<sigma>\<rangle>, (ctxt_of_pos_term p (l \<cdot> \<sigma>'))\<langle>t \<cdot> \<sigma>\<rangle>) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))\<^sup>*\<close>
              \<open>((ctxt_of_pos_term p l)\<langle>t\<rangle> \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n)\<close> \<open>(ctxt_of_pos_term p (l \<cdot> \<sigma>'))\<langle>t \<cdot> \<sigma>\<rangle> = (ctxt_of_pos_term p l)\<langle>t\<rangle> \<cdot> \<sigma>\<close> \<sigma>_split cstep_n_rstep_trs_n_conv rsteps_closed_ctxt rtrancl.rtrancl_into_rtrancl subst_apply_term_ctxt_apply_distrib)
        then have "(b, c) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))\<^sup>*"
          using b c by simp
        moreover have "(a, b) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n))\<^sup>*"
          using rtrancl_into_rtrancl(3) assms
          using Suc.IH by blast
        ultimately show ?thesis
          by auto
      next
        case False
        then have no_x: "x \<notin> vars_term l"
          by (meson vars_term_poss_subt_at)
        from inlined have "l' = l" using left_inline[of i cs x t l r] 1 no_x
          using rtrancl_into_rtrancl.prems by auto
        moreover have "r' = r" using left_inline[of i cs x t l r] inlined 1
          using rtrancl_into_rtrancl.prems by auto
        ultimately have "(b, c) \<in> cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n)"
          using cstep_n_SucI[of l r cs' "insert (left_inline i \<rho>) (R - {\<rho>})" "\<sigma>" n "b" C "c"]
          using cs' b c inlined
          by blast
        then show ?thesis using Suc
          using rtrancl_into_rtrancl.IH by auto
      qed
    next
      case 2
      moreover have "b = C\<langle>l \<cdot>  \<sigma>\<rangle>" using b
        by simp
      moreover have "c = C\<langle>r \<cdot>  \<sigma>\<rangle>" using c
        by simp
      ultimately have "(b, c) \<in> cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) (Suc n)"
        using cstep_n_SucI[of l r cs "insert (left_inline i \<rho>) (R - {\<rho>})" "\<sigma>" n "b" C "c"]
          cs_R'
        by blast
      then show ?thesis
        using rtrancl_into_rtrancl by auto
    qed
  qed
qed

lemma left_inline_cond':
  fixes R :: "('f, 'v) ctrs"
  assumes "\<rho> \<in> R"
    and i: "i < length (conds \<rho>)" "conds \<rho> ! i = (Var x, t)"
    and lin: "linear_term (clhs \<rho>)"
    and vars: "x \<notin> vars_term (crhs \<rho>) \<union> vars_term t \<union>
      \<Union>(vars_term ` lhss (set (take i (conds \<rho>)))) \<union>
      \<Union>(vars_term ` lhss (set (drop (Suc i) (conds \<rho>))))"
  shows "(cstep R)\<^sup>* \<subseteq> (cstep (insert (left_inline i \<rho>) (R - {\<rho>})))\<^sup>*" (is "_ \<subseteq> (cstep ?R)\<^sup>*")
proof
  fix x y
  obtain n where "(x, y) \<in> (cstep R)\<^sup>* \<Longrightarrow> (x, y) \<in> (cstep_n R n)\<^sup>*"
    using csteps_imp_csteps_n by blast
  then have "(x, y) \<in> (cstep R)\<^sup>* \<Longrightarrow> (x, y) \<in> (cstep_n (insert (left_inline i \<rho>) (R - {\<rho>})) n)\<^sup>*"
    using assms left_inline_cond by simp
  then show "(x, y) \<in> (cstep R)\<^sup>* \<Longrightarrow> (x, y) \<in> (cstep (insert (left_inline i \<rho>) (R - {\<rho>})))\<^sup>*"
    using csteps_n_imp_csteps by blast
qed


end
