(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Tcap
  imports
    First_Order_Rewriting.Trs
    Ground_Context
begin

no_notation Subterm_and_Context.Hole ("\<box>")
notation Ground_Context.GCHole ("\<box>")
notation Ground_Context.equiv_class ("[_]")

(* a semantic version of tcap which is not executable *)
fun tcap :: "('f, 'v) trs \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, 'v) gctxt" where
  "tcap _ (Var _)    = \<box>"
| "tcap R (Fun f ts) = (
    let h = GCFun f (map (tcap R) ts) in
    if (\<exists>r \<in> R. Ground_Context.match h (fst r)) then \<box> else h)"

lemma tcap_sound_main:
  assumes "(s \<cdot> \<sigma>, t) \<in> (rstep R)\<^sup>*" and p: "p \<in> pos_gctxt (tcap R s)" 
  shows "t \<in> [tcap R s] \<and> (s \<cdot> \<sigma> |_ p, t |_p) \<in> (rstep R)\<^sup>*"
using assms
proof (induct s arbitrary: t p rule: term.induct)
  case (Fun f ss)
  let ?h = "GCFun f (map (tcap R) ss)" 
  show ?case 
  proof (cases "tcap R (Fun f ss)")
    case (GCFun g hs)
    then have res: "tcap R (Fun f ss) = ?h"
      by (cases "\<exists> r \<in> R. Ground_Context.match ?h (fst r)", auto simp: Let_def)
    {
      fix u
      assume steps: "(Fun f ss \<cdot> \<sigma>, u) \<in> (nrrstep R)\<^sup>*"
      then have cond: "root (Fun f ss \<cdot> \<sigma>) = root u \<and> (\<forall>i<num_args (Fun f ss \<cdot> \<sigma>). (Fun f ss \<cdot> \<sigma> |_ [i], u |_ [i] ) \<in> (rstep R)\<^sup>*)"	
        by (rule nrrsteps_imp_eq_root_arg_rsteps)
      then have "root (Fun f ss) = root u" by simp
      then have "\<exists> us. u = Fun f us" by (cases u, auto)
      from this obtain us where u: "u = Fun f us" by force
      with cond have len: "length ss = length us" by simp
      {
        fix i p
        assume ilen: "i < length us" and p: "p \<in> pos_gctxt (tcap R (Fun f ss |_ [i]))"
        with len have "[i] \<in> poss (Fun f ss)" by simp
        then have "Fun f ss \<cdot> \<sigma>|_[i] = Fun f ss |_[i] \<cdot> \<sigma>" by simp
        with ilen len cond have one: "(Fun f ss |_[i] \<cdot> \<sigma>, u|_[i]) \<in> (rstep R)\<^sup>*" by simp	
        from ilen len have "Fun f ss |_[i] \<in> set ss" by simp
        from Fun(1)[OF this one p] u
        have "us ! i \<in> [tcap R (ss ! i)]" and "(ss ! i \<cdot> \<sigma> |_ p, us ! i |_ p) \<in> (rstep R)\<^sup>*" by auto
      } note IH = this
      from IH[OF _ pos_gctxt_epsilon] len
      have "Fun f us \<in> [?h]" by auto
      with u have uh: "u \<in> [?h]" by simp
      have "(Fun f ss \<cdot> \<sigma> |_ p, u |_p ) \<in> (rstep R)\<^sup>*"
      proof (cases p)
        case (Cons i q)
        from Fun(3) len have i: "i < length us" and "q \<in> pos_gctxt (tcap R (Fun f ss |_ [i]))" unfolding Cons
          by (auto simp: Let_def split: if_splits)
        from IH(2)[OF this] have "(ss ! i \<cdot> \<sigma> |_ q, us ! i |_ q) \<in> (rstep R)\<^sup>*" .
        then show ?thesis unfolding Cons u using i len by simp
      next
        case Nil
        from steps have "(Fun f ss \<cdot> \<sigma>, u) \<in> (rstep R)\<^sup>*" unfolding rstep_iff_rrstep_or_nrrstep by regexp
        with Nil show ?thesis by simp
      qed 
      note uh this
    } note nrr = this    
    have "rstep R = rrstep R \<union> nrrstep R" by (rule rstep_iff_rrstep_or_nrrstep)
    from this and \<open>(Fun f ss \<cdot> \<sigma>, t) \<in> (rstep R)\<^sup>*\<close>
    have  "(Fun f ss \<cdot> \<sigma>, t) \<in> (nrrstep R)\<^sup>* \<or> (Fun f ss \<cdot> \<sigma>, t) \<in> (nrrstep R)\<^sup>* O (rrstep R) O (rstep R)\<^sup>*" by (rule firstStep)
    then show ?thesis
    proof 
      assume "(Fun f ss \<cdot> \<sigma>, t) \<in> (nrrstep R)\<^sup>*"
      with nrr res show ?thesis by auto
    next
      assume "(Fun f ss \<cdot> \<sigma>, t) \<in> (nrrstep R)\<^sup>* O rrstep R O (rstep R)\<^sup>*"
      from this obtain u v where fu: "(Fun f ss \<cdot> \<sigma>, u) \<in> (nrrstep R)\<^sup>*" and uv: "(u,v) \<in> rrstep R" by force
      from fu nrr have uh: "u \<in> [?h]" by simp
      from uv have "\<exists> l r \<sigma>. (l,r) \<in> R \<and> l \<cdot> \<sigma> = u \<and> r \<cdot> \<sigma> = v" by (rule rrstep_imp_rule_subst)
      from this obtain l r \<sigma> where lrR: "(l, r) \<in> R" and match: "l \<cdot> \<sigma> = u" by force
      from uh and match  have "Ground_Context.match ?h l" by (unfold Ground_Context.match_def, auto)
      with lrR have tcap: "tcap R (Fun f ss) = \<box>" by (simp add: Let_def, force)
      with Fun(3) have p: "p = []" by simp
      from tcap p Fun(2) show ?thesis by simp
    qed
  qed (insert Fun, auto)
qed simp

lemma tcap_sound:
  assumes steps: "(s \<cdot> \<sigma>, t) \<in> (rstep R)\<^sup>*" shows "t \<in> [tcap R s]"
  using tcap_sound_main[OF steps pos_gctxt_epsilon] by simp

lemma tcap_instance_equiv_class[simp]: "s \<cdot> \<sigma> \<in> [tcap R s]"
  by (rule tcap_sound, auto)

lemma tcap_subterm_subst_rsteps:
  assumes steps: "(s \<cdot> \<sigma>, t) \<in> (rstep R)\<^sup>*" and p: "p \<in> pos_gctxt (tcap R s)" 
  shows "(s \<cdot> \<sigma> |_ p, t |_ p) \<in> (rstep R)\<^sup>*"
  using tcap_sound_main[OF steps p] by simp

lemma tcap_subterm_rsteps:
  assumes steps: "(s, t) \<in> (rstep R)\<^sup>*" and p: "p \<in> pos_gctxt (tcap R s)" 
  shows "(s |_ p, t |_ p) \<in> (rstep R)\<^sup>*"
  using tcap_subterm_subst_rsteps[OF _ p, of Var] steps by simp

lemma tcap_instance_subset: "[tcap R (t \<cdot> \<sigma>)] \<subseteq> [tcap R t]" 
proof (induct t, simp)
  case (Fun f ts)
  let ?h = "GCFun f (map (tcap R) ts)"
  let ?hs = "GCFun f (map (tcap R) (map (\<lambda> t. (t \<cdot> \<sigma>)) ts))"
  let ?hss = "GCFun f (map (\<lambda> t. tcap R (t \<cdot> \<sigma>)) ts)"
  show ?case 
  proof (cases "\<exists> r \<in> R. Ground_Context.match ?h (fst r)", simp)
    case False
    then have nMatch: "\<forall> r \<in> R. \<not> Ground_Context.match ?h (fst r)" by auto
    {
      fix l
      assume "Ground_Context.match ?hs l"
      from this obtain \<delta> where "l \<cdot> \<delta> \<in> [?hs]" unfolding Ground_Context.match_def by auto
      then have "Ground_Context.match ?h l" unfolding Ground_Context.match_def using Fun by force
    }
    with nMatch have "\<forall> r \<in> R. \<not> Ground_Context.match ?hs (fst r)" by auto
    with \<open>\<not> (\<exists> r \<in> R. Ground_Context.match ?h (fst r))\<close>
    have id: "tcap R (Fun f ts) = ?h \<and> tcap R (Fun f ts \<cdot> \<sigma>) = ?hss" by auto
    from Fun have "[?hss] \<subseteq> [?h]" by (force simp: nth_mem)
    with id show ?thesis by simp
  qed
qed

lemma tcap_refl: "t \<in> [tcap R t]"
  by  (rule tcap_sound[of _ Var], simp)

lemma tcap_lhs_var:
  assumes left_var: "\<exists>lr \<in> R. is_Var (fst lr)" 
  shows "tcap R s = \<box>"
proof -
  from left_var obtain x r where lr: "(Var x,r) \<in> R" by auto
  show ?thesis
  proof (induct s)
    case (Fun f ts)
    show ?case
      unfolding tcap.simps Let_def    
      by (clarsimp, rule bexI[OF _ lr], simp add: Ground_Context.match_def,
          rule exI[of _ "(\<lambda>_. Fun f ts)"], simp add: tcap_refl)
  qed auto
qed

lemma tcap_lhs:
  assumes "(l, r) \<in> R"
  shows "tcap R (l \<cdot> \<sigma>) = \<box>"
proof (cases l)
  case (Fun f ts)
  show ?thesis
  proof (unfold Fun, simp add: Let_def o_def, intro bexI[OF _ assms], simp add: Fun)
    show "Ground_Context.match (GCFun f (map (\<lambda> x. tcap R (x \<cdot> \<sigma>)) ts)) (Fun f ts)"
      by  (unfold Ground_Context.match_def, rule exI[of _ \<sigma>], unfold equiv_class.simps, simp add: tcap_refl)
  qed
next
  case (Var x)
  show ?thesis
    by (rule tcap_lhs_var, rule bexI[OF _ assms], auto simp: Var)
qed

lemma match_lhs_var:
  assumes left_var: "\<exists>lr \<in> R. is_Var (fst lr)" 
  shows "Ground_Context.match (tcap R s) t"
  unfolding tcap_lhs_var[OF left_var] Ground_Context.match_def by auto

abbreviation
  tcap_below :: "('f, 'v) trs \<Rightarrow> 'f \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) gctxt"
where
  "tcap_below R f ts \<equiv> GCFun f (map (tcap R) ts)"

fun match_tcap_below :: "('f, 'v) term \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "match_tcap_below l R (Fun f ts) = Ground_Context.match (tcap_below R f ts) l"
| "match_tcap_below l R (Var x) = False"

lemma match_below:
  assumes match: "Ground_Context.match (GCFun f (bef @ s # aft)) l" (is "Ground_Context.match ?s l")
    and subset: "[s] \<subseteq> [t]"
  shows "Ground_Context.match (GCFun f (bef @ t # aft)) l" (is "Ground_Context.match ?t l")
proof -
  from subset have "[?s] \<subseteq> [?t]" by (rule equiv_class_mono)
  with match show ?thesis unfolding Ground_Context.match_def by blast
qed

lemma tcap_rewrite:
  fixes t :: "('f, 'v) term"
  assumes "(t, s) \<in> rstep R"
  shows "[tcap R s] \<subseteq> [tcap R t]"
using assms
proof (induct)
  fix C \<sigma> l r assume "(l, r) \<in> R"
  then show "[tcap R C\<langle>r \<cdot> \<sigma>\<rangle>] \<subseteq> [tcap R C\<langle>l \<cdot> \<sigma>\<rangle>]"
  proof (induct C)
    case (More f bef D aft)
    then have ind: "[tcap R D\<langle>r \<cdot> \<sigma>\<rangle>] \<subseteq> [tcap R D\<langle>l \<cdot> \<sigma>\<rangle>]" by auto
    let ?h = "\<lambda>t. GCFun f (map (tcap R) bef @ tcap R D\<langle>t\<rangle> # map (tcap R) aft)"
    from ind have res: "\<And>t. Ground_Context.match (?h (r \<cdot> \<sigma>)) t \<Longrightarrow> Ground_Context.match (?h (l \<cdot> \<sigma>)) t"
      using match_below by force
    show ?case
    proof (cases "\<exists>lr\<in>R. Ground_Context.match (?h (l \<cdot> \<sigma>)) (fst lr)")
      case False 
      then have one: "\<not> (\<exists> lr \<in> R. Ground_Context.match (?h (r \<cdot> \<sigma>)) (fst lr))" using res by blast
      from ind have subset: "[?h (r \<cdot> \<sigma>)] \<subseteq> [?h (l \<cdot> \<sigma>)]" by (rule equiv_class_mono)
      with one show ?thesis by (auto simp: Let_def)
    qed simp
  next
    case Hole
    have "tcap R (l \<cdot> \<sigma>) = \<box>"
    proof (cases l)
      case (Var x)
      {
        fix h
        from equiv_class_nonempty obtain s :: "('f, 'v) term" where "s \<in> [h]" by auto
        with Var have "l \<cdot> subst x s \<in> [h]" unfolding subst_def by auto
        then have "Ground_Context.match h (fst (l,r))" unfolding Ground_Context.match_def by (simp, blast)
      }
      with \<open>(l, r) \<in> R\<close> show ?thesis by (cases "l \<cdot> \<sigma>", auto simp: Let_def, blast)
    next
      case (Fun f ll)
      then have one: "l \<cdot> \<sigma> = Fun f (map (\<lambda> u. u \<cdot> \<sigma>) ll)" (is "_ = Fun f ?ls") by auto
      {
        fix i 
        have "ll ! i \<cdot> \<sigma> \<in> [tcap R (ll ! i \<cdot> \<sigma>)]"
          using tcap_sound[OF rtrancl_refl, of "ll!i \<cdot> \<sigma>" "Var"] by simp
      }
      with one have "(fst (l,r)) \<cdot> \<sigma> \<in> [GCFun f (map (\<lambda>x. tcap R (x \<cdot> \<sigma>)) ll)]" by auto
      with one and \<open>(l, r) \<in> R\<close>
      show ?thesis by (auto simp: Let_def o_def, unfold Ground_Context.match_def, blast)
    qed
    then show "[tcap R Hole\<langle>r \<cdot> \<sigma>\<rangle>] \<subseteq> [tcap R Hole\<langle>l \<cdot> \<sigma>\<rangle>]" by simp
  qed
qed

lemma tcap_rewrites:
  assumes  "(s, t) \<in> (rstep R)\<^sup>*" 
  shows "[tcap R t] \<subseteq> [tcap R s]"
using assms
proof (induct)
  case (step t u)
  from step(3) tcap_rewrite[OF step(2)] show ?case by auto
qed simp

lemma match_tcap_sound: 
  assumes derivation: "(t \<cdot> \<delta>, s \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*"
  shows "Ground_Context.match (tcap R t) s"
proof -
  from derivation have "s \<cdot> \<sigma> \<in> [tcap R t]" by (rule tcap_sound)
  then show ?thesis by (unfold Ground_Context.match_def, auto)
qed

lemma match_tcap_inv_sound: 
  assumes derivation: "(t \<cdot> \<delta>, s \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*"
  shows "Ground_Context.match (tcap (R\<inverse>) s) t"
proof -
  have id: "((rstep R)\<^sup>*)\<inverse> = (rstep (R\<inverse>))\<^sup>*"
    unfolding rtrancl_converse [symmetric] and rstep_converse ..
  from derivation have "(s \<cdot> \<sigma>, t \<cdot> \<delta>) \<in> ((rstep R)\<^sup>*)\<inverse>" by auto
  from match_tcap_sound[OF this[unfolded id]]
  show "Ground_Context.match (tcap (R\<inverse>) s) t" .
qed

lemma join_imp_unifiable_tcaps:
  assumes "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>\<down>"
  shows "Ground_Context.unifiable (tcap R s) (tcap R t)"
proof -
  obtain u where "(s \<cdot> \<sigma>, u) \<in> (rstep R)\<^sup>*" and "(t \<cdot> \<tau>, u) \<in> (rstep R)\<^sup>*" using assms by auto
  then have "u \<in> [tcap R s]" and "u \<in> [tcap R t]" by (blast intro: tcap_sound)+
  then show ?thesis by (auto simp: Ground_Context.unifiable_def)
qed

lemma match_tcap_below: assumes steps: "(s, l \<cdot> \<sigma>) \<in> (nrrstep R)\<^sup>*"
  and l: "is_Fun l"
  shows "match_tcap_below l R s"
proof -
  from l obtain f ls where l: "l = Fun f ls" by (cases l, auto)
  note steps = nrrsteps_imp_eq_root_arg_rsteps[OF steps, unfolded l]
  from steps[THEN conjunct1] obtain ss where s: "s = Fun f ss" and len: "length ls = length ss" by (cases s, auto)
  {
    fix i
    assume "i < length ss"
    with steps[unfolded s] have steps: "(ss ! i, ls ! i \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*" by auto
    have "ls ! i \<cdot> \<sigma> \<in> [tcap R (ls ! i \<cdot> \<sigma>)]" by (rule tcap_refl)
    also have "[tcap R (ls ! i \<cdot> \<sigma>)] \<subseteq> [tcap R (ss ! i)]" using tcap_rewrites[OF steps] by auto
    finally have "ls ! i \<cdot> \<sigma> \<in> [tcap R (ss ! i)]" .
  }
  then show ?thesis unfolding l s
    by (auto simp: len Ground_Context.match_def intro!: exI[of _ \<sigma>])
qed

no_notation Ground_Context.GCHole ("\<box>")
no_notation Ground_Context.equiv_class ("[_]")
notation Subterm_and_Context.Hole ("\<box>")

end
