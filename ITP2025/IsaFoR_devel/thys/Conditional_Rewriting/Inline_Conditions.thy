(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Inline_Conditions
  imports 
    Conditional_Rewriting
begin

definition inline :: "_"
  where
    "inline i \<rho> =
      (let
        cs = conds \<rho>;
        (s, t) = cs ! i;
        \<sigma> = subst (the_Var t) s;
        cs' = take i cs @ drop (Suc i) cs
      in
      ((clhs \<rho>, crhs \<rho> \<cdot> \<sigma>), map (\<lambda>(s, t). (s \<cdot> \<sigma>, t)) cs'))"

lemma inline:
  assumes "i < length cs" and "cs ! i = (s, Var x)"
  shows "inline i ((l, r), cs) =
    ((l, r \<cdot> subst x s), map (\<lambda>(u, v). (u \<cdot> subst x s, v)) (take i cs @ drop (Suc i) cs))"
  using assms
  by (auto simp: inline_def Let_def)

lemma inline_cond:
  fixes R :: "('f, 'v) ctrs"
  assumes "\<rho> \<in> R"
    and i: "i < length (conds \<rho>)" "conds \<rho> ! i = (s, Var x)"
    and vars: "x \<notin> vars_term (clhs \<rho>) \<union> vars_term s \<union>
      \<Union>(vars_term ` rhss (set (take i (conds \<rho>)))) \<union>
      \<Union>(vars_term ` rhss (set (drop (Suc i) (conds \<rho>))))"
  shows "(cstep R)\<^sup>* = (cstep (insert (inline i \<rho>) (R - {\<rho>})))\<^sup>*" (is "_ = (cstep ?R)\<^sup>*")
proof -
  have "cstep_n R n \<subseteq> (cstep_n ?R n)\<^sup>*" for n \<comment> \<open>this direction doesn't need @{thm vars}\<close>
  proof (induct n)
    case (Suc n)
    then have IH: "(s, t) \<in> (cstep_n ?R n)\<^sup>*" if "(s, t) \<in> (cstep_n R n)\<^sup>*" for s t
      using rtrancl_idemp rtrancl_mono that by blast
    show ?case
    proof
      fix t u assume "(t, u) \<in> cstep_n R (Suc n)"
      then obtain l r cs C and \<sigma> :: "('f, 'v) subst"
        where rule: "((l, r), cs) \<in> R"
          and conds: "conds_n_sat R n cs \<sigma>" and t: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" and u: "u = C\<langle>r \<cdot> \<sigma>\<rangle>"
        by (elim cstep_n_SucE) (auto simp: conds_n_sat_iff)
      show "(t, u) \<in> (cstep_n ?R (Suc n))\<^sup>*"
      proof (cases "\<rho> = ((l, r), cs)")
        case False
        then have "((l, r), cs) \<in> ?R" using rule by simp
        moreover have "conds_n_sat ?R n cs \<sigma>" using conds and IH by (auto simp: conds_n_sat_iff)
        ultimately have "(t, u) \<in> cstep_n ?R (Suc n)"
          by (intro cstep_n_SucI) (auto simp: t u conds_n_sat_iff)
        then show ?thesis by auto
      next
        case [simp]: True
        have "cs = take i cs @ (s, Var x) # drop (Suc i) cs"
          using i and id_take_nth_drop by fastforce
        let ?cs = "conds (inline i \<rho>)"
        define \<tau> where "\<tau> y = (if y = x then s \<cdot> \<sigma> else \<sigma> y)" for y

        from \<open>conds \<rho> ! i = (s, Var x)\<close> and \<open>i < length (conds \<rho>)\<close> and conds
        have sx: "(s \<cdot> \<sigma>, \<sigma> x) \<in> (cstep_n ?R n)\<^sup>*"
          using IH apply (auto simp: conds_n_sat_iff)
          by (metis conds conds_n_satD nth_mem eval_term.simps(1))
        then have sx_Suc: "(s \<cdot> \<sigma>, \<sigma> x) \<in> (cstep_n ?R (Suc n))\<^sup>*"
          by (meson cstep_n_Suc_mono rtrancl_mono subsetCE)
        have cs: "?cs = map (\<lambda>(u, v). (u \<cdot> subst x s, v)) (take i cs @ drop (Suc i) cs)"
          using \<open>i < length (conds \<rho>)\<close> and \<open>conds \<rho> ! i = (s, Var x)\<close> and subst_list_append
          by (auto simp: inline_def Let_def)
        have "(fst (?cs ! j) \<cdot> \<sigma>, snd (?cs ! j) \<cdot> \<sigma>) \<in> (cstep_n ?R n)\<^sup>*" if "j < length ?cs" for j
        proof -
          define k where "k = (if j \<ge> i then Suc j else j)"
          have "k < length cs" and "k \<noteq> i"
            using i and that
            unfolding cs by (auto simp: k_def)
          then have eqs: "fst (?cs ! j) = fst (cs ! k) \<cdot> subst x s"
            "snd (?cs ! j) = snd (cs ! k)"
            unfolding cs by (auto simp: k_def nth_append min_absorb2 split: prod.splits)
          have "(fst (cs ! k) \<cdot> subst x s \<circ>\<^sub>s \<sigma>, fst (cs ! k) \<cdot> \<sigma>) \<in> (cstep_n ?R n)\<^sup>*"
            using sx by (intro all_ctxt_closed_subst_step) (auto simp: subst_def subst_compose)
          moreover have "(fst (cs ! k) \<cdot> \<sigma>, snd (cs ! k) \<cdot> \<sigma>) \<in> (cstep_n ?R n)\<^sup>*"
            using conds and IH and \<open>k < length cs\<close> apply (auto simp: conds_n_sat_iff)
            by (metis conds conds_n_satD nth_mem surjective_pairing)
          ultimately show ?thesis unfolding eqs by auto
      qed
      then have "conds_n_sat ?R n ?cs \<sigma>"
        by (auto simp: conds_n_sat_iff) (metis fst_conv in_set_idx snd_conv)
      moreover have "inline i \<rho> \<in> ?R" by simp
      ultimately have "(t, C\<langle>r \<cdot> \<tau>\<rangle>) \<in> cstep_n ?R (Suc n)"
        using i and term_subst_eq_conv [of r \<tau> "subst x s \<circ>\<^sub>s \<sigma>"]
        by (intro cstep_n_SucI [of l "r \<cdot> subst x s" "conds (inline i \<rho>)" ?R \<sigma> n t C])
          (auto simp: \<tau>_def subst_def subst_compose conds_n_sat_iff t inline)
      moreover have "(r \<cdot> \<tau>, r \<cdot> \<sigma>) \<in> (cstep_n ?R (Suc n))\<^sup>*"
        using sx_Suc by (intro all_ctxt_closed_subst_step) (auto simp: \<tau>_def)
      ultimately show ?thesis
        using rtrancl_map [where f = "ctxt_apply_term C", OF cstep_n_ctxt]
        unfolding u
        by (meson r_into_rtrancl rtrancl_trans)
    qed
  qed
  qed simp
  then have 1: "cstep R \<subseteq> (cstep ?R)\<^sup>*"
    by (meson cstep_iff csteps_n_subset_csteps subrelI subsetCE)
  have "cstep_n ?R n \<subseteq> cstep_n R n" for n
  proof (induct n)
    case (Suc n)
    then have IH: "(s, t) \<in> (cstep_n R n)\<^sup>*" if "(s, t) \<in> (cstep_n ?R n)\<^sup>*" for s t
      using rtrancl_idemp rtrancl_mono that by blast
    show ?case
    proof
      fix t and u assume "(t, u) \<in> cstep_n ?R (Suc n)"
      then obtain l r cs C and \<sigma> :: "('f, 'v) subst"
        where rule: "((l, r), cs) \<in> ?R"
          and conds: "conds_n_sat ?R n cs \<sigma>" and t: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" and u: "u = C\<langle>r \<cdot> \<sigma>\<rangle>"
        by (elim cstep_n_SucE) (auto simp: conds_n_sat_iff)
      show "(t, u) \<in> cstep_n R (Suc n)"
      proof (cases "inline i \<rho> = ((l, r), cs)")
        case False
        then have "((l, r), cs) \<in> R" using rule by auto
        moreover have "conds_n_sat R n cs \<sigma>" using conds and IH by (auto simp: conds_n_sat_iff)
        ultimately have "(t, u) \<in> cstep_n R (Suc n)"
          by (intro cstep_n_SucI) (auto simp: t u conds_n_sat_iff)
        then show ?thesis by auto
      next
        let ?cs = "conds \<rho>"
        case inline: True
        then have l: "l = clhs \<rho>" and r: "r = crhs \<rho> \<cdot> subst x s"
          and cs: "cs = map (\<lambda>(u, v). (u \<cdot> subst x s, v)) (take i ?cs @ drop (Suc i) ?cs)"
          by (cases \<rho> rule: crule_cases, auto simp: inline_def Let_def i case_prod_beta)
        define \<tau> where "\<tau> y = (if y = x then s \<cdot> \<sigma> else \<sigma> y)" for y

        have [simp]: "s \<cdot> \<tau> = s \<cdot> \<sigma>"
          using vars
          unfolding term_subst_eq_conv
          by (auto simp: \<tau>_def)

        have "clhs \<rho> \<cdot> \<sigma> = clhs \<rho> \<cdot> \<tau>"
          and "crhs \<rho> \<cdot> subst x s \<cdot> \<sigma> = crhs \<rho> \<cdot> \<tau>"
          using vars
          unfolding subst_subst
          unfolding term_subst_eq_conv
          by (auto simp: \<tau>_def subst_compose subst_def)
        then have t': "t = C\<langle>clhs \<rho> \<cdot> \<tau>\<rangle>" and u': "u = C\<langle>crhs \<rho> \<cdot> \<tau>\<rangle>"
          using inline
          by (auto simp: t u i inline_def Let_def)
        have "(fst (?cs ! j) \<cdot> \<tau>, snd (?cs ! j) \<cdot> \<tau>) \<in> (cstep_n R n)\<^sup>*" if "j < length ?cs" for j
        proof (cases "j = i")
          case True
          then show ?thesis by (auto simp: i \<tau>_def)
        next
          case False
          define k where "k = (if j < i then j else Suc j)"
          consider "j < i" | "j = i" | "j > i" by arith
          then show ?thesis
          proof (cases)
            case 1
            then have "?cs ! j \<in> set (take i ?cs)" using i and in_set_conv_nth by fastforce
            then have snd: "?cs ! j = (u, v) \<Longrightarrow> v \<cdot> \<tau> = v \<cdot> \<sigma>" for u v
              using vars
              unfolding term_subst_eq_conv by (auto simp: \<tau>_def)
            have "fst (?cs ! j) \<cdot> \<tau> = fst (cs ! j) \<cdot> \<sigma>"
              using i and vars and 1
              by (auto simp: cs nth_append subst_subst term_subst_eq_conv subst_compose subst_def \<tau>_def
                  simp del: subst_subst_compose split: prod.splits)
            moreover have "snd (?cs ! j) \<cdot> \<tau> = snd (cs ! j) \<cdot> \<sigma>"
              using vars and that and 1
              by (auto simp: cs nth_append term_subst_eq_conv \<tau>_def snd split: prod.splits)
            moreover have "j < length cs"
              using i and 1 by (auto simp: cs)
            ultimately show ?thesis using conds and IH
              by (auto simp: conds_n_sat_iff all_set_conv_all_nth)
          next
            case 2
            then show ?thesis by (auto simp: i \<tau>_def)
          next
            case 3
            then have len: "Suc i + (j - Suc i) \<le> length ?cs" using that by auto
            have len': "j - Suc i < length (drop (Suc i) ?cs)" using 3 and that by auto
            have *: "?cs ! j = drop (Suc i) ?cs ! (j - Suc i)" using i and 3 and that by auto
            then have "?cs ! j \<in> set (drop (Suc i) ?cs)" using 3 and that and i
              by (metis Suc_leI in_set_conv_nth length_drop less_diff_iff)
            then have snd: "?cs ! j = (u, v) \<Longrightarrow> v \<cdot> \<tau> = v \<cdot> \<sigma>" for u v
              using vars
              unfolding term_subst_eq_conv by (auto simp: \<tau>_def)
            have len'': "j - 1 < length (take i (conds \<rho>) @ drop (Suc i) (conds \<rho>))" 
              and len3: "Suc i \<le> length (conds \<rho>)"
              and id: "(j - 1 < i) = False" 
              and id': "length (take i (conds \<rho>)) = i" 
              and id'': "Suc i + (j - 1 - i) = j" 
              using 3 i that by (auto simp: min_def)
            have "fst (?cs ! j) \<cdot> \<tau> = fst (cs ! (j - 1)) \<cdot> \<sigma>"
              unfolding cs nth_map[OF len''] nth_append id id' if_False nth_drop[OF len3] id''
              using i and vars and 3
              by (auto split: prod.splits simp del: subst_subst_compose
                  simp: subst_subst term_subst_eq_conv subst_compose subst_def \<tau>_def) 
            moreover
            have "snd (?cs ! j) \<cdot> \<tau> = snd (cs ! (j - 1)) \<cdot> \<sigma>"
              using vars and that and 3
              by (auto simp: cs nth_append min_def term_subst_eq_conv snd \<tau>_def split: prod.splits)
            moreover have "j - 1 < length cs"
              using i and 3 and that by (auto simp: cs min_def)
            ultimately show ?thesis using conds and IH
              by (auto simp: conds_n_sat_iff all_set_conv_all_nth)
          qed
        qed
        then have "conds_n_sat R n (conds \<rho>) \<tau>"
          apply (auto simp: conds_n_sat_iff)
          by (metis fst_conv in_set_idx snd_conv)
        moreover have "((clhs \<rho>, crhs \<rho>), conds \<rho>) \<in> R" using \<open>\<rho> \<in> R\<close> by force
        ultimately show "(t, u) \<in> cstep_n R (Suc n)"
          by (intro cstep_n_SucI [OF _ _ t' u', where cs = "conds \<rho>"])
            (auto simp: conds_n_sat_iff)
      qed
    qed
  qed simp
  then have 2: "cstep ?R \<subseteq> cstep R"
    by (meson contra_subsetD cstep_iff subrelI)
  show ?thesis
    using 1 and 2 by (simp add: rtrancl_subset)
qed

end
