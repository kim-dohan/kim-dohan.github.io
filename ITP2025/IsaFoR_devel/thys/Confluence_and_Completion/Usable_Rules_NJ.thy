(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Rules_NJ
imports
  TRS.Tcap
begin

text \<open>Usable rules for reachability, formalization of Aoto's FroCoS'13 paper\<close>

locale usable_rules_reachability =
  fixes R :: "('f,'v)trs"
begin

inductive U0 :: "('f,'v)rule \<Rightarrow> ('f,'v)term \<Rightarrow> bool" where
  lvar: "(l,r) \<in> R \<Longrightarrow> is_Var l \<Longrightarrow> U0 (l,r) t"
| rec: "U0 (l,r) t \<Longrightarrow> U0 lr r \<Longrightarrow> U0 lr t"
| match: "(l,r) \<in> R \<Longrightarrow> match_tcap_below l R (Fun f ts) \<Longrightarrow> s \<unrhd> Fun f ts \<Longrightarrow> U0 (l,r) s"

lemma U0_R: "U0 lr t \<Longrightarrow> lr \<in> R"
  by (induct rule: U0.induct, auto)

definition "varcond \<equiv> \<lambda> (l,r). vars_term r \<subseteq> vars_term l"

definition "Ur t = (let U0t = {lr. U0 lr t} in if (\<forall> lr \<in> U0t. varcond lr) then U0t else R)"

lemma Ur_R: "Ur t \<subseteq> R" unfolding Ur_def Let_def using U0_R by auto

lemma Ur_1: assumes s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and lr: "(l,r) \<in> R"
  shows "U0 (l,r) s" 
proof (cases l)
  case (Var x)
  then have "is_Var l" by auto
  from lvar[OF lr this]
  show ?thesis .
next
  case (Fun f ls)
  let ?ls = "Fun f (map (\<lambda> l. l \<cdot> \<sigma>) ls)"
  from Fun have "l \<cdot> \<sigma> = ?ls" by simp
  then have subt: "s \<unrhd> ?ls" unfolding s by auto
  show ?thesis
    by (rule match[OF lr _ subt], unfold match_tcap_below.simps Ground_Context.match_def, rule exI[of _ \<sigma>],
      simp add: Fun tcap_refl)
qed
  
lemma Ur_2: assumes step: "(s,t) \<in> rstep R"
  shows "Ur t \<subseteq> Ur s"
proof -
  { 
    fix lr'
    assume "U0 lr' t" and "\<And> lr. U0 lr s \<Longrightarrow> varcond lr"
    then have "U0 lr' s" using step
    proof (induct arbitrary: s rule: U0.induct)
      case lvar
      from U0.lvar[OF this(1-2)] lvar show ?case by auto
    next
      case (rec l r t lr')
      show ?case
        by (rule U0.rec[OF rec(2)[OF rec(5) rec(6)] rec(3)])
    next
      case (match l' r' f ts t)
      define u where "u = Fun f ts"      
      note U = U0.match[OF match(1-2), folded u_def]
      from match(5) obtain C \<sigma> l r where lr: "(l,r) \<in> R" and s: "s = C \<langle> l \<cdot> \<sigma>\<rangle>" and t: "t = C \<langle>r \<cdot> \<sigma>\<rangle>" by blast
      from match(3)[folded u_def] have subt: "t \<unrhd> u" .
      note trans = subterm.dual_order.trans
      {
        assume u: "C\<langle>l \<cdot> \<sigma>\<rangle> \<unrhd> u"
        from U[OF this] have ?case unfolding s .
      } note subt_goal = this
      from subt[unfolded t]
      show ?case
      proof (cases rule: supteq_ctxt_cases)
        case (sub_ctxt D C') (* d *)
        then obtain g bef D' aft where C': "C' = More g bef D' aft" by (cases C', auto)
        from match(2)[folded u_def, unfolded sub_ctxt C']
        have "match_tcap_below l' R (Fun g (bef @ D'\<langle>r \<cdot> \<sigma>\<rangle> # aft))" by simp
        then have "match_tcap_below l' R (Fun g (bef @ D'\<langle>l \<cdot> \<sigma>\<rangle> # aft))" unfolding match_tcap_below.simps map_append list.map
          by (rule match_below[OF _ tcap_rewrite[OF rstepI[OF lr]]], auto)
        from U0.match[OF match(1) this, of s] show ?thesis
          unfolding s sub_ctxt C' by auto
      next
        case in_ctxt (* b *)
        from subt_goal[OF supt_imp_supteq[OF suptc_imp_supt[OF this]]]
        show ?thesis .
      next
        case in_term
        then show ?thesis
        proof (cases rule: supteq_subst_cases)
          case (in_subst x) (* a *)
          from Ur_1[OF s t lr] have U0lr: "U0 (l,r) s" .
          from match(4)[OF this, unfolded varcond_def] in_subst lr have "x \<in> vars_term l" by auto
          then have "l \<unrhd> Var x" by auto
          from trans[OF supteq_subst[OF this, of \<sigma>], of u] in_subst have subt: "l \<cdot> \<sigma> \<unrhd> u" by simp
          show ?thesis
            by (rule subt_goal[OF trans[OF _ subt]], auto)
        next
          case (in_term v) (* c *)
          from in_term u_def obtain vs where v: "v = Fun f vs" by auto
          let ?vs = "map (\<lambda> v. v \<cdot> \<sigma>) vs"
          from match(2)[folded u_def, unfolded in_term v] have "match_tcap_below l' R (Fun f ?vs)" by simp
          then have "match_tcap_below l' R (Fun f vs)" unfolding match_tcap_below.simps map_map o_def Ground_Context.match_def
            using tcap_instance_subset[of R _ \<sigma>] by force
          from U0.match[OF match(1) this in_term(1)[unfolded v]] have "U0 (l',r') r" .
          from U0.rec[OF Ur_1(1)[OF s refl lr] this] show ?thesis .
        qed
      qed
    qed
  } note main = this
  show ?thesis
    by (cases "\<forall> lr \<in> {lr. U0 lr s}. varcond lr", insert main Ur_R,
    auto simp: Ur_def Let_def)
qed

lemma Ur: "(s,t) \<in> (rstep R)^* \<Longrightarrow> (s,t) \<in> (rstep (Ur s))^*"
proof (induct rule: converse_rtrancl_induct)
  case (step s u)
  from Ur_2[OF step(1)] have subset: "Ur u \<subseteq> Ur s" by auto
  from step(1) obtain C \<sigma> l r where lr: "(l,r) \<in> R"
  and s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>" and u: "u = C \<langle> r \<cdot> \<sigma> \<rangle>" by blast
  from Ur_1[OF s u lr] lr have "(l,r) \<in> Ur s" unfolding Ur_def by auto
  from rstepI[OF this s u] rtrancl_mono[OF rstep_mono[OF subset]] step(3)
  show ?case by auto
qed simp
end

abbreviation usable_rules_reach where "usable_rules_reach \<equiv> usable_rules_reachability.Ur"

lemmas usable_rules_reach = usable_rules_reachability.Ur

lemma usable_rules_reach_nj: "\<not> (\<exists> u. (s,u) \<in> (rstep (usable_rules_reach Rs s))^* \<and> (t,u) \<in> (rstep (usable_rules_reach Rt t))^*) \<Longrightarrow>
  \<not> (\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep Rt)^*)"
  using usable_rules_reach by auto

lemma subterm_tcap_nj: assumes p: "p \<in> pos_gctxt (tcap Rs s)" "p \<in> pos_gctxt (tcap Rt t)"
  and nj: "\<not> (\<exists> u. (s |_ p, u) \<in> (rstep Rs)^* \<and> (t |_ p, u) \<in> (rstep Rt)^*)"
  shows "\<not> (\<exists> u. (s, u) \<in> (rstep Rs)^* \<and> (t, u) \<in> (rstep Rt)^*)"
  using tcap_subterm_rsteps[OF _ p(1)] 
    tcap_subterm_rsteps[OF _ p(2)] nj by blast
end
