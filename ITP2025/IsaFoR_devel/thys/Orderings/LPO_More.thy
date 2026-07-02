(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  Guillaume Allais (2011)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory LPO_More
imports 
  RPO_More
  Efficient_Weighted_Path_Order.RPO_Mem_Impl
begin

section \<open>LPO Closures\<close>

locale lpo = rpo_with_assms prc prl " (\<lambda>_. Lex)" n for prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool" and prl n
begin

text \<open>The next definition forms a closure of a given relation gt with respect to a LPO
      (following Martin/Nipkow CADE 1990, where gt is instantiated by an order on variables.\<close>
fun lpo_closure' :: "('f, 'v) term rel \<Rightarrow> ('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<times> ('f \<times> nat \<Rightarrow> bool) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<times> bool" where
  "lpo_closure' gt prec s t = (
    if (s, t) \<in> gt then (True, True)
    else (
      case (s,t) of
        (Var x, Var y) \<Rightarrow> (False, x = y)
      | (Var x, Fun g ts) \<Rightarrow> (False, ts = [] \<and> (snd prec) (g,0))
      | (Fun f ss, Var y) \<Rightarrow> (let con = (\<exists> s \<in> set ss. snd (lpo_closure' gt prec s (Var y))) in (con,con))
      | (Fun f ss, Fun g ts) \<Rightarrow>
         if (\<exists> s \<in> set ss. snd (lpo_closure' gt prec s (Fun g ts)))
         then (True,True)
         else (case (fst prec) (f,length ss) (g,length ts) of (prs,prns) \<Rightarrow>
           if prns \<and> (\<forall> t \<in> set ts. fst (lpo_closure' gt prec (Fun f ss) t))
           then if prs
              then (True,True) 
              else lex_ext_unbounded (lpo_closure' gt prec) ss ts
           else (False,False)))
    )"

abbreviation S' where "S' p cs s t \<equiv> fst (rpo_unbounded p cs s t)"

abbreviation NS' where "NS' p cs s t \<equiv> snd (rpo_unbounded p cs s t)"

lemma lpo_lpo_closure':
  fixes prec :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<times> ('f \<times> nat \<Rightarrow> bool)"
  assumes lpo: "cs = (\<lambda>_. Lex)"
  shows "((S' prec cs (s :: ('f, 'v) term) t) \<longrightarrow> fst (lpo_closure' ord prec s t)) \<and>
    (NS' prec cs s t \<longrightarrow> snd (lpo_closure' ord prec s t))"
  using assms
proof (induct s t rule: rpo_unbounded.induct)
  case (3 prec cs f ss y)
  { assume "S' prec cs (Fun f ss) (Var y) \<or> NS' prec cs (Fun f ss) (Var y)"
    from this[simplified] obtain s where s:"s \<in> set ss" "NS' prec cs s (Var y)"
      unfolding Let_def by force
    from 3(1)[OF s(1) 3(2)] s have s:"\<exists>s \<in> set ss. snd (lpo_closure' ord prec s (Var y))" by blast
    let ?lc = "lpo_closure' ord prec (Fun f ss) (Var y)"
    have "fst ?lc \<and> snd ?lc" proof(cases "(Fun f ss, Var y) \<in> ord")
      case False
      hence no_ord:"(Fun f ss, Var y) \<in> ord = False" by auto
      from s False show ?thesis
        unfolding lpo_closure'.simps[of _ _ _ "Var y"] no_ord if_False by auto
    qed (auto)
  }
  thus ?case by fast
next
  case (4 prec cs f ss g ts)
  let ?lc = "lpo_closure' ord prec (Fun f ss) (Fun g ts)"
  note lc_simps = lpo_closure'.simps[of _ _ "Fun f ss" "Fun g ts", of ord prec]
  { assume S:"S' prec cs (Fun f ss) (Fun g ts)"
    have "fst ?lc" proof(cases "(Fun f ss, Fun g ts) \<in> ord")
      case False
      hence no_ord:"(Fun f ss, Fun g ts) \<in> ord = False" by auto
      note S = S[simplified]
      show ?thesis proof(cases "\<exists>s \<in> set ss. snd (lpo_closure' ord prec s (Fun g ts))")
        case True
        thus ?thesis unfolding lc_simps no_ord if_False Let_def by simp
      next
        case False
        note no_subtc = this
        with 4(1)[OF _ 4(5)] have no_subt:"\<not> (\<exists>s \<in> set ss. NS' prec cs s (Fun g ts))" by simp
        note S = S[unfolded False[unfolded eq_False[symmetric]] if_False]
        note lc_simps = lc_simps[unfolded no_ord if_False split_beta fst_conv snd_conv term.case]
        let ?prec = "fst prec (f, length ss) (g, length ts)"
        obtain pr prns where prec[simp]:"fst ?prec = pr" "snd ?prec = prns"
          by (cases "(fst prec (f, length ss) (g, length ts))", simp)
        show ?thesis proof(cases prns)
          case True
          note weak_prec = this
          show ?thesis proof(cases "\<forall>t\<in>set ts. S' prec cs (Fun f ss) t")
            case True
            with 4(2)[OF no_subt prod.collapse _ 4(5)]
            have all_ti_smaller:"\<forall>t\<in>set ts. fst (lpo_closure' ord prec (Fun f ss) t)"
              unfolding prec[symmetric] by simp
            show ?thesis proof(cases pr)
              case True
              from True False weak_prec all_ti_smaller show ?thesis unfolding lc_simps prec by simp
            next
              case False
              with lc_simps True no_subtc weak_prec all_ti_smaller
              have lc:"?lc = lex_ext_unbounded (lpo_closure' ord prec) ss ts" by simp
              from prec have prec':"fst prec (f, length ss) (g, length ts) = (pr, prns)"
                by (smt prod.collapse)
              from True False S no_subt have S:"fst (lex_ext_unbounded (rpo_unbounded prec cs) ss ts)"
                unfolding prec' prod.case 4(5) by (simp add: weak_prec)
              from weak_prec True have "prns \<and> (\<forall>t\<in>set ts. S' prec cs (Fun f ss) t)" by simp
              note IH = 4(4)[OF no_subt prod.collapse, unfolded prec, OF this False, unfolded 4(5)]
              note IH = IH[OF refl order_tag.distinct(1) _ _ refl]
              note lex_ext_mono = lex_ext_unbounded_mono[of ss ts "rpo_unbounded prec cs"]
              note lex_ext_mono = lex_ext_mono[of "lpo_closure' ord prec", unfolded 4(5)]
              from this IH S show ?thesis unfolding 4(5) unfolding lc by simp
            qed
        next
          case False
          with S no_subt lpo show ?thesis by auto
        qed
      next
        case False
          with S no_subt lpo show ?thesis by (simp add: prod.case_eq_if)
        qed
      qed
    qed (auto)
  } note S = this
  { assume NS:"NS' prec cs (Fun f ss) (Fun g ts)"
    have "snd ?lc" proof(cases "(Fun f ss, Fun g ts) \<in> ord")
      case False
      hence no_ord:"(Fun f ss, Fun g ts) \<in> ord = False" by auto
      note NS = NS[simplified]
      show ?thesis proof(cases "\<exists>s \<in> set ss. snd (lpo_closure' ord prec s (Fun g ts))")
        case True
        thus ?thesis unfolding lc_simps no_ord if_False Let_def by simp
      next
        case False
        note no_subtc = this
        with 4(1)[OF _ 4(5)] have no_subt:"\<not> (\<exists>s \<in> set ss. NS' prec cs s (Fun g ts))" by simp
        note NS = NS[unfolded False[unfolded eq_False[symmetric]] if_False]
        note lc_simps = lc_simps[unfolded no_ord if_False split_beta fst_conv snd_conv term.case]
        let ?prec = "fst prec (f, length ss) (g, length ts)"
        obtain pr prns where prec[simp]:"fst ?prec = pr" "snd ?prec = prns"
          by (cases "(fst prec (f, length ss) (g, length ts))", simp)
        show ?thesis proof(cases prns)
          case True
          note weak_prec = this
          show ?thesis proof(cases "\<forall>t\<in>set ts. S' prec cs (Fun f ss) t")
            case True
            with 4(2)[OF no_subt prod.collapse _ 4(5)]
            have all_ti_smaller:"\<forall>t\<in>set ts. fst (lpo_closure' ord prec (Fun f ss) t)"
              unfolding prec[symmetric] by simp
            show ?thesis proof(cases pr)
              case True
              from True False weak_prec all_ti_smaller show ?thesis unfolding lc_simps prec by simp
            next
              case False
              with lc_simps True no_subtc weak_prec all_ti_smaller
              have lc:"?lc = lex_ext_unbounded (lpo_closure' ord prec) ss ts" by simp
              from prec have prec':"fst prec (f, length ss) (g, length ts) = (pr, prns)"
                by (smt prod.collapse)
              from True False NS no_subt have NS:"snd (lex_ext_unbounded (rpo_unbounded prec cs) ss ts)"
                unfolding prec' prod.case 4(5) by (simp add: weak_prec)
              from weak_prec True have "prns \<and> (\<forall>t\<in>set ts. S' prec cs (Fun f ss) t)" by simp
              note IH = 4(4)[OF no_subt prod.collapse, unfolded prec, OF this False, unfolded 4(5)]
              note IH = IH[OF refl order_tag.distinct(1) _ _ refl]
              note lex_ext_mono = lex_ext_unbounded_mono[of ss ts "rpo_unbounded prec cs"]
              note lex_ext_mono = lex_ext_mono[of "lpo_closure' ord prec", unfolded 4(5)]
              from this IH NS show ?thesis unfolding 4(5) unfolding lc by simp
            qed
        next
          case False
          with NS no_subt lpo show ?thesis by auto
        qed
      next
        case False
          with NS no_subt lpo show ?thesis by (simp add: prod.case_eq_if)
        qed
      qed
    qed (auto)
  }
  with S show ?case by simp
qed auto

declare lpo_closure'.simps [simp del]

definition lpo_closure :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<times> bool"
 where
  "lpo_closure gt s t = lpo_closure' gt (prc, prl) s t"

abbreviation S where "S s t \<equiv> fst (rpo_unbounded (prc, prl) (\<lambda>_. Lex) (s :: ('f, 'v) term) t)"

abbreviation NS where "NS s t \<equiv> snd (rpo_unbounded (prc, prl) (\<lambda>_. Lex) (s :: ('f, 'v) term) t)"

lemma lpo_lpo_closure:
  "(S s t \<longrightarrow> fst (lpo_closure ord s t)) \<and> (NS s t \<longrightarrow> snd (lpo_closure ord s t))"
 using lpo_lpo_closure'[of "(\<lambda>_. Lex)" "(prc, prl)" s t ord]  unfolding lpo_closure_def by fastforce

end

locale lpo_closure = lpo prc prl n for prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool" and prl n
  and X :: "'v set" and vord :: "'v rel" (* and f :: "'f" *)
begin

abbreviation "ord \<equiv> {(Var x, Var y) | x y. (y, x) \<in> vord \<and> x \<noteq> y}"

context
  assumes total:"total_on X vord" and part_ord:"partial_order_on X vord" and
  wf:"wf (vord - Id)" and fin:"finite X" and non_empty:"vord \<noteq> {}" (* and f_least:"least f" *)
begin

lemma vord_X:"vord \<subseteq> X \<times> X"
  using part_ord unfolding partial_order_on_def preorder_on_def refl_on_def by auto

interpretation wo_rel vord
proof(unfold_locales)
  from part_ord have "vord \<subseteq> X \<times> X" unfolding partial_order_on_def preorder_on_def refl_on_def by auto
  with part_ord fin have fin:"finite vord" unfolding partial_order_on_def by (meson finite_SigmaI finite_subset)
  from total part_ord have "linear_order_on X vord"
    unfolding linear_order_on_def total_on_def Relation.total_on_def by auto
  with linear_order_on_well_order_on[OF fin] have wo:"well_order_on X vord" by auto
  show "Well_order vord" by (insert wo well_order_on_Well_order, auto)
qed

(* lemma for showing lpo_closure_SN *)
lemma lpo_lpo_var_closure:
  "\<exists>\<sigma> :: ('f, 'v) subst. (\<forall>s t.(fst (lpo_closure ord s t) \<longrightarrow> S (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)) \<and> (snd (lpo_closure ord s t) \<longrightarrow> NS (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)))"
  oops

(* NOTE: In theory this theorem guarantees termination of ordered rewriting,  *)
(* but there is not way to speak of this within Isabelle. So we don't have to prove this. *)
(* If we think about proving this *)
(* note that we don't have well-foundedness of LPO for free, so we have to switch to bounded comparison. *)
lemma lpo_closure_SN:"SN {(s, t) | s t. fst (lpo_closure ord s t)}"
  oops

end

abbreviation lpo_S where "lpo_S \<equiv> {(s,t). S (s :: ('f, 'v) term) t}"
abbreviation lpo_NS where "lpo_NS \<equiv> {(s,t). NS (s :: ('f, 'v) term) t}"

lemma lpo_closure_compatible:
  "(fst (lpo_closure lpo_S s t) \<longrightarrow> S s t) \<and> (snd (lpo_closure lpo_S s t) \<longrightarrow> NS s t)"
proof (induct "(s, t)" arbitrary: s t rule: wf_induct[OF wf_measure[of "\<lambda> (s, t). size s + size t"]])
  case (1 s t)
  then have IH: "size s' + size t' < size s + size t \<Longrightarrow>
    (fst (local.lpo_closure lpo_S s' t') \<longrightarrow> S s' t') \<and> (snd (local.lpo_closure lpo_S s' t') \<longrightarrow> NS s' t')"
    for s' t' by force
  have "(s, t) \<in> lpo_S \<or> (s, t) \<notin> lpo_S" by blast
  then show ?case
  proof (rule disjE, goal_cases)
    case 1
    then show ?case unfolding lpo_closure_def
      by (simp add: lpo_closure'.simps  RPO_More.rpo_unbounded_stri_imp_nstri) 
  next
    case 2
    then show ?case oops
(*
  qed
qed *)

lemma lpo_closure_mono:
  assumes "\<O> \<subseteq> \<O>'"
  shows "(fst (lpo_closure \<O> s t) \<longrightarrow> fst (lpo_closure \<O>' s t)) \<and>
  (snd (lpo_closure \<O> s t) \<longrightarrow> snd (lpo_closure \<O>' s t))"
  oops

lemma lpo_closure_subst:
 "(fst (lpo_closure \<O> s t) \<longrightarrow> fst (lpo_closure {(u \<cdot> \<sigma>', v \<cdot> \<sigma>') |u v. (u,v) \<in> \<O>} (s \<cdot> \<sigma>') (t \<cdot> (\<sigma>' :: ('f, 'v) subst)))) \<and>
  (snd (lpo_closure \<O> s t) \<longrightarrow> snd (lpo_closure {(u \<cdot> \<sigma>', v \<cdot> \<sigma>') |u v. (u,v) \<in> \<O>} (s \<cdot> \<sigma>') (t \<cdot> \<sigma>')))"
  oops

end

locale two_lpo_closures = lpo1: lpo_closure prc1 prl n + lpo2: lpo_closure prc2 prl n
  for prc1 prc2 and  prl :: "'f \<times> nat \<Rightarrow> bool" and n
begin

lemma lpo_closure_prec_mono: 
  assumes (* least_imp: "\<And>f::'f. least1 f \<Longrightarrow> least2 f" *)
        S_imp: "\<And>fn gm. fst (prc1 fn gm) \<Longrightarrow> fst (prc2 fn gm)"
    and W_imp: "\<And>fn gm. snd (prc1 fn gm) \<Longrightarrow> snd (prc2 fn gm)"
  shows "(fst (lpo1.lpo_closure \<O> s t) \<longrightarrow> fst (lpo2.lpo_closure \<O> s t)) \<and> 
               (snd (lpo1.lpo_closure \<O> s t) \<longrightarrow> snd (lpo2.lpo_closure \<O> s t))"
    (is "(?S \<O> s t \<longrightarrow> ?S' \<O> s t) \<and> (?N \<O> s t \<longrightarrow> ?N' \<O> s t)")
  oops

end

end
