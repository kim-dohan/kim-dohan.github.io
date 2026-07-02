(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Rules_NJ_Unif
imports 
  TRS.Tcap
  TRS.Ground_Context_Impl
begin

text \<open>Def. 4.4, containment ordering\<close>
definition contains :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "contains U V \<equiv> V \<subseteq> rstep U"

lemma containsI[intro]: assumes "\<And> l r. (l,r) \<in> V \<Longrightarrow> (l,r) \<in> rstep U"
  shows "contains U V" unfolding contains_def using assms by force

lemma contains_rstep: assumes "(s,t) \<in> rstep V" and "contains U V"
  shows "(s,t) \<in> rstep U" 
  using assms unfolding contains_def using rstep_rstep[of U] by force

context
  fixes R U :: "('f,string)trs"
begin
inductive_set U0 :: "('f,string)term \<Rightarrow> ('f,string)trs" for s :: "('f,string)term" where
  match_non_var: "(l,r) \<in> R \<Longrightarrow> s \<unrhd> Fun f ts \<Longrightarrow> gc_matcher (tcap_below U f ts) l = Some \<sigma> \<Longrightarrow> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> U0 s"

definition usable_instantiation :: "('f,string)term \<Rightarrow> bool" where
  "usable_instantiation s \<equiv> contains U (U0 s) 
     \<and> (\<forall> r \<in> rhss U. contains U (U0 r))" 

definition "no_lhs_var \<equiv> \<forall> l r. (l,r) \<in> R \<longrightarrow> is_Fun l"

lemma U0_contains: assumes ground: "ground s \<or> no_lhs_var"
  shows "contains (U0 s) { (s,t) | t. (s,t) \<in> rstep R }" (is "contains ?L ?R")
proof
  fix s' t
  assume "(s',t) \<in> ?R" then have s': "s' = s" and st: "(s,t) \<in> rstep R" by auto
  from st obtain \<Theta> C l r where lr: "(l,r) \<in> R" and s: "s = C \<langle> l \<cdot> \<Theta> \<rangle>" and t: "t = C \<langle> r \<cdot> \<Theta> \<rangle>" by auto
  from ground[unfolded s no_lhs_var_def] lr obtain f ls where lt: "l \<cdot> \<Theta> = Fun f ls" by (cases l, auto, cases "l \<cdot> \<Theta>", auto)
  from s have "s \<unrhd> Fun f ls" unfolding lt by auto
  note match = match_non_var[OF lr this]
  have "l \<cdot> \<Theta> \<in> equiv_class (tcap_below U f ls)" unfolding lt by (auto simp: tcap_refl)
  from gc_matcher_complete[OF this] obtain \<sigma> \<delta>
    where mgu: "gc_matcher (tcap_below U f ls) l = Some \<sigma>" and theta: "\<Theta> = \<sigma> \<circ>\<^sub>s \<delta>" by auto
  let ?lr = "(l \<cdot> \<sigma>, r \<cdot> \<sigma>)"
  from match[OF mgu] have "?lr \<in> ?L" .
  from rstepI[OF this, of s C \<delta> t] theta s t 
  show "(s',t) \<in> rstep ?L" unfolding s' by auto
qed

context
  assumes wfU: "\<And> l r. (l,r) \<in> U \<Longrightarrow> vars_term r \<subseteq> vars_term l"
begin
lemma usable_instantiation_rstep: assumes step: "(s,t) \<in> rstep R"
  and ground: "ground s \<or> no_lhs_var"
  and U: "usable_instantiation s"
  shows "usable_instantiation t"
proof -
  note d = usable_instantiation_def
  note U0 = match_non_var
  from U have cs: "contains U (U0 s)"
    and crec: "\<And> r.  r \<in> rhss U \<Longrightarrow> contains U (U0 r)" 
    unfolding d by auto
  have "contains U (U0 t)" 
  proof
    fix ls rs 
    assume "(ls,rs) \<in> U0 t"
    then show "(ls,rs) \<in> rstep U"
    proof (cases)
      case (match_non_var l' r' f us \<sigma>)
      note lr' = match_non_var(3)
      note subt = match_non_var(4)
      note mgu = match_non_var(5)
      note ls_rs = match_non_var(1-2)
      let ?u = "Fun f us"
      from U0_contains[OF ground, unfolded contains_def] step have "(s,t) \<in> rstep (U0 s)" by auto
      from contains_rstep[OF this cs] obtain C l r \<Theta> where 
        lr: "(l,r) \<in> U" and s: "s = C \<langle> l \<cdot> \<Theta> \<rangle>" and t: "t = C \<langle> r \<cdot> \<Theta> \<rangle>" by auto
      {
        assume sub: "C \<langle> l \<cdot> \<Theta> \<rangle> \<unrhd> ?u"
        have "(ls,rs) \<in> U0 s" unfolding ls_rs
          by (rule U0[OF lr' _ mgu], insert sub, auto simp: s)
        with cs have ?thesis unfolding contains_def by auto
      } note subt_goal = this
      from lr have r: "r \<in> rhss U" by force
      note trans = subterm.dual_order.trans
      from subt[unfolded t]
      show ?thesis
      proof (cases rule: supteq_ctxt_cases)
        case in_ctxt (* case b *)
        show ?thesis by (rule subt_goal[OF supt_imp_supteq[OF suptc_imp_supt[OF in_ctxt]]])
      next
        case in_term
        then show ?thesis
        proof (cases rule: supteq_subst_cases)
          case (in_subst x) (* a *)
          from wfU[OF lr] in_subst have "x \<in> vars_term l" by auto
          then have "l \<unrhd> Var x" by auto
          from trans[OF supteq_subst[OF this, of \<Theta>], of ?u] in_subst have subt: "l \<cdot> \<Theta> \<unrhd> ?u" by simp
          show ?thesis by (rule subt_goal[OF trans[OF _ subt]], auto)
        next
          case (in_term v) (* c *)
          from in_term obtain vs where v: "v = Fun f vs" by (cases v, auto)
          let ?vs = "map (\<lambda> v. v \<cdot> \<Theta>) vs"
          from in_term(3) have us: "us = ?vs" unfolding v by simp
          note U0 = U0[OF lr' in_term(1)[unfolded v]]
          from gc_matcher_sound[OF mgu[unfolded us]] 
          have mem: "\<And> \<sigma>'. l' \<cdot> \<sigma> \<cdot> \<sigma>' \<in> equiv_class (tcap_below U f ?vs)" .
          have "equiv_class (tcap_below U f ?vs) \<subseteq> equiv_class (tcap_below U f vs)"
            by (rule equiv_class_GCFun_subset, insert tcap_instance_subset, auto)
          then have mem: "\<And> \<sigma>'. l' \<cdot> \<sigma> \<cdot> \<sigma>' \<in> equiv_class (tcap_below U f vs)" using mem by blast
          from mem[of Var] have "l' \<cdot> \<sigma> \<in> equiv_class (tcap_below U f vs)" by simp
          from gc_matcher_complete[OF this] obtain \<mu> \<delta> where
            match: "gc_matcher (tcap_below U f vs) l' = Some \<mu>" and \<sigma>: "\<sigma> = \<mu> \<circ>\<^sub>s \<delta>" by blast
          from U0[OF match] have mem: "(l' \<cdot> \<mu>, r' \<cdot> \<mu>) \<in> U0 r" by auto
          show ?thesis unfolding ls_rs \<sigma>
            by (rule contains_rstep[OF _ crec[OF r]], insert mem, auto)
        qed
      next
        case (sub_ctxt D C') (* d *)         
        then obtain bef D' aft where C': "C' = More f bef D' aft" by (cases C', auto)
        from sub_ctxt(2)[unfolded C'] have us: "us = bef @ D'\<langle>r \<cdot> \<Theta>\<rangle> # aft" by simp
        from gc_matcher_sound[OF mgu[unfolded us]]
        have mgu: "\<And> \<sigma>'. l' \<cdot> \<sigma> \<cdot> \<sigma>' \<in> equiv_class (tcap_below U f (bef @ D'\<langle>r \<cdot> \<Theta>\<rangle> # aft))" .
        from tcap_rewrite[OF rstepI[OF lr]]
        have "equiv_class (tcap U D'\<langle>r \<cdot> \<Theta>\<rangle>) \<subseteq> equiv_class (tcap U D'\<langle>l \<cdot> \<Theta>\<rangle>)" by auto
        from mgu[of Var] equiv_class_mono[OF this, of f "map (tcap U) bef" "map (tcap U) aft"] 
        have "l' \<cdot> \<sigma>  \<in> equiv_class (tcap_below U f (bef @ D'\<langle>l \<cdot> \<Theta>\<rangle> # aft))" by auto
        from gc_matcher_complete[OF this] obtain \<mu> \<delta> where 
          mgu: "gc_matcher (tcap_below U f (bef @ D'\<langle>l \<cdot> \<Theta>\<rangle> # aft)) l' = Some \<mu>" and \<sigma>: "\<sigma> = \<mu> \<circ>\<^sub>s \<delta>" by auto
        have step: "(l' \<cdot> \<mu>, r' \<cdot> \<mu>) \<in> U0 s" unfolding s C' sub_ctxt
          by (rule U0[OF lr' _ mgu], auto)
        show ?thesis unfolding ls_rs \<sigma> 
          using contains_rstep[OF rstepI[OF step, of _ Hole] cs] by auto
      qed
    qed
  qed
  with crec show ?thesis unfolding d by auto
qed

text \<open>lemma 4.9\<close>
lemma usable_instantiation_rsteps_main: assumes sU: "usable_instantiation s"
  and st: "(s,t) \<in> (rstep R)^*" and gs: "ground s \<or> no_lhs_var"
  shows "(s,t) \<in> (rstep U)^* \<and> usable_instantiation t \<and> (ground t \<or> no_lhs_var)"
using st
proof (induct)
  case (step t u)
  then have gt: "ground t \<or> no_lhs_var" by simp
  from usable_instantiation_rstep[OF step(2)] step(3) have 
    uu: "usable_instantiation u" and ut: "usable_instantiation t" by blast+
  from ut[unfolded usable_instantiation_def] have "contains U (U0 t)" ..
  from step(2) U0_contains[OF gt] contains_rstep[OF _ this, of t u] have tu: "(t,u) \<in> rstep U"
    unfolding contains_def by auto
  from tu gt wfU have "ground u \<or> no_lhs_var" by fastforce
  with tu uu step(3) show ?case by auto
qed (insert sU gs, auto)
end
end
end
