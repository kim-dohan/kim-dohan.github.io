(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Nonloop
imports 
  First_Order_Rewriting.Trs
begin

(* This theory formalizes the results in [EEG12]
   Emmes, Enger, Giesl: Proving Non-Looping Non-Termination Automatically *)

(* clearly: do not model pattern terms as functions, but as triples *)
type_synonym ('f,'v)pat_term = "('f,'v)term \<times> ('f,'v)subst \<times> ('f,'v)subst"

(* to obtain the corresponding function of such a triple, we use pat_term *)
definition pat_term :: "('f,'v)pat_term \<Rightarrow> nat \<Rightarrow> ('f,'v)term"
  where "pat_term ps n \<equiv> case ps of (t,\<sigma>,\<tau>) \<Rightarrow> t \<cdot> (\<sigma>^^n) \<cdot> \<tau>"

(* pattern rules are more general than in [EEG12], where the boolean indicates
   whether we are allowed to rewrite with a set of dependency pairs P in addition to the 
   standard rules of the TRS R. *)
type_synonym ('f,'v)pat_rule = "('f,'v)pat_term \<times> ('f,'v)pat_term \<times> bool"


locale fixed_trs = 
  fixes R P :: "('f,'v)trs" (* R = TRS, P = DPs *)
begin

abbreviation Rs where "Rs \<equiv> (rstep R)^+"
abbreviation RPs where "RPs \<equiv> (rstep R \<union> rrstep P)^+"

inductive_set pat_rule 
  where pat_rule_I_R: "(l,r) \<in> R 
       \<Longrightarrow> ((l,Var,Var),(r,Var,Var),False) \<in> pat_rule"
     | pat_rule_I_P: "(l,r) \<in> P 
       \<Longrightarrow> ((l,Var,Var),(r,Var,Var),True) \<in> pat_rule"
     | pat_rule_II: "((s,Var,Var),(t,Var,Var),b) \<in> pat_rule \<Longrightarrow> s \<cdot> \<theta> = t \<cdot> \<sigma> \<Longrightarrow> \<theta> \<circ>\<^sub>s \<sigma> = \<sigma> \<circ>\<^sub>s \<theta> 
       \<Longrightarrow> ((s,\<sigma>,Var),(t,\<theta>,Var),b) \<in> pat_rule"
     | pat_rule_III: "((s,Var,Var),(t,Var,Var),False) \<in> pat_rule \<Longrightarrow> p \<in> poss t \<Longrightarrow> s = t |_ p \<cdot> \<sigma> \<Longrightarrow> z \<notin> vars_term s \<union> vars_term t \<union> vars_subst \<sigma> 
       \<Longrightarrow> ((s,\<sigma>,Var),(replace_at t p (Var z), (\<sigma> ( z := replace_at t p (Var z))), subst z (t |_ p) ),False) \<in> pat_rule" 
     | pat_rule_IV: "(s,t,b) \<in> pat_rule \<Longrightarrow> \<lbrakk>\<And> n. pat_term s n = pat_term s' n\<rbrakk> \<Longrightarrow> \<lbrakk>\<And> n. pat_term t n = pat_term t' n\<rbrakk> 
       \<Longrightarrow> (s',t',b) \<in> pat_rule"
     | pat_rule_V: "((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<in> pat_rule \<Longrightarrow> vars_subst \<rho> \<inter> (subst_domain \<sigma>s \<union> subst_domain \<mu>s \<union> subst_domain \<sigma>t \<union> subst_domain \<mu>t) = {} 
       \<Longrightarrow> ((s \<cdot> \<rho>, subst_compose' \<sigma>s \<rho>, subst_compose' \<mu>s \<rho>), (t \<cdot> \<rho>, subst_compose' \<sigma>t \<rho>, subst_compose' \<mu>t \<rho>),b) \<in> pat_rule" 
     | pat_rule_VI: "(q,(t,\<sigma>,\<mu>),b) \<in> pat_rule \<Longrightarrow> ((u,\<sigma>,\<mu>),(v,\<sigma>,\<mu>),b') \<in> pat_rule \<Longrightarrow> p \<in> poss t \<Longrightarrow> t |_ p = u \<Longrightarrow> \<lbrakk>b' \<Longrightarrow> p = []\<rbrakk> 
       \<Longrightarrow> (q,(replace_at t p v, \<sigma>, \<mu>),b \<or> b') \<in> pat_rule" \<comment> \<open>generalized q instead of (s,\<sigma>,\<mu>), added p \<in> poss t\<close>
     | pat_rule_VII: "((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<in> pat_rule \<Longrightarrow> \<sigma>s \<circ>\<^sub>s \<rho> = \<rho> \<circ>\<^sub>s \<sigma>s \<Longrightarrow> \<mu>s \<circ>\<^sub>s \<rho> = \<rho> \<circ>\<^sub>s \<mu>s \<Longrightarrow> \<sigma>t \<circ>\<^sub>s \<rho> = \<rho> \<circ>\<^sub>s \<sigma>t \<Longrightarrow> \<mu>t \<circ>\<^sub>s \<rho> = \<rho> \<circ>\<^sub>s \<mu>t 
       \<Longrightarrow> ((s, \<sigma>s \<circ>\<^sub>s \<rho>, \<mu>s), (t, \<sigma>t \<circ>\<^sub>s \<rho>, \<mu>t),b) \<in> pat_rule" 
     | pat_rule_VIII: "((s,\<sigma>s,\<mu>s),(t,\<sigma>t,\<mu>t),b) \<in> pat_rule 
       \<Longrightarrow> ((s, \<sigma>s, \<mu>s \<circ>\<^sub>s \<rho>), (t, \<sigma>t, \<mu>t \<circ>\<^sub>s \<rho>),b) \<in> pat_rule" 
     | pat_rule_IX: "(p,(t,\<sigma>,\<mu>),b) \<in> pat_rule \<Longrightarrow> (t,t') \<in> (rstep R)^* \<Longrightarrow> \<lbrakk>\<And> x. (\<sigma> x, \<sigma>' x) \<in> (rstep R)^*\<rbrakk> \<Longrightarrow> \<lbrakk>\<And> x. (\<mu> x, \<mu>' x) \<in> (rstep R)^*\<rbrakk> 
       \<Longrightarrow> (p,(t',\<sigma>',\<mu>'),b) \<in> pat_rule"
     | pat_rule_X: "((t,\<sigma>,\<mu>),(s,\<sigma>',\<mu>'),b) \<in> pat_rule \<comment> \<open>not in paper, but used in implementation\<close>
       \<Longrightarrow> ((t \<cdot> (\<sigma> ^^ k),\<sigma>,\<mu>),(s \<cdot> (\<sigma>' ^^ k),\<sigma>',\<mu>'),b) \<in> pat_rule" 

definition Rel where "Rel \<equiv> \<lambda> b. if b then RPs else Rs"
lemmas Rel = Rel_def

lemma rel_subst: assumes step: "(s,t) \<in> Rel b"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> Rel b"
proof (cases b)
  case False
  then have b: "b = False" by simp
  show ?thesis using step unfolding Rel b if_False
    by (rule rsteps_subst_closed)
next
  case True
  then have b: "b = True" by simp
  show ?thesis using step unfolding Rel b if_True
    using subst.closed_trancl[OF subst.closed_Un[OF subst_closed_rstep subst_closed_rrstep], of R P] unfolding subst.closed_def by auto
qed

lemma rel_subset: "Rel b \<subseteq> Rel True"
proof (cases b)
  case False 
  then have b: "b = False" by simp
  show ?thesis unfolding b Rel if_True if_False by regexp
qed auto

(* soundness proof for all inference rules, Theorem 7 *)
lemma pat_rule_steps_main: 
  assumes pat_rule: "(p,q,b) \<in> pat_rule"
  shows "(pat_term p n,pat_term q n) \<in> Rel b"
proof -
  note pt = pat_term_def
  from pat_rule show ?thesis
  proof (induct p q b arbitrary: n rule: pat_rule.induct)
    case (pat_rule_I_R l r)
    then have "(l \<cdot> Var ^^ n, r \<cdot> Var ^^ n) \<in> rstep R" by auto    
    then show ?case by (auto simp: pt Rel)
  next
    case (pat_rule_I_P l r)
    then have "(l \<cdot> Var ^^ n, r \<cdot> Var ^^ n) \<in> rrstep P" unfolding rrstep_def' by blast
    then show ?case by (auto simp: pt Rel)
  next
    case (pat_rule_II s t b \<theta> \<sigma>)
    show ?case unfolding pt split subst_apply_term_empty
    proof (induct n)
      case 0
      show ?case using pat_rule_II(2)[of 0] by (simp add: pt)
    next
      case (Suc n)
      from rel_subst[OF pat_rule_II(2)[of 0], of "\<sigma> ^^ Suc n"]
      have "(s \<cdot> \<sigma> ^^ Suc n, t \<cdot> \<sigma> \<cdot> \<sigma> ^^ n) \<in> Rel b" unfolding pt by simp
      also have "t \<cdot> \<sigma> \<cdot> \<sigma> ^^ n = s \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> ^^ n)" unfolding pat_rule_II(3)[symmetric] by simp
      also have "\<theta> \<circ>\<^sub>s \<sigma> ^^ n = \<sigma> ^^ n \<circ>\<^sub>s \<theta>" 
      proof (induct n)
        case 0 then show ?case by simp
      next
        case (Suc n) 
        have "\<theta> \<circ>\<^sub>s \<sigma> ^^ Suc n = (\<theta> \<circ>\<^sub>s \<sigma> ^^ n) \<circ>\<^sub>s \<sigma>" 
          unfolding subst_power_Suc  by (simp add: ac_simps)
        also have "... = \<sigma> ^^ n \<circ>\<^sub>s (\<theta> \<circ>\<^sub>s \<sigma>)" unfolding Suc by (simp add: ac_simps)
        finally show ?case unfolding pat_rule_II(4)
          unfolding subst_power_Suc by (simp add: ac_simps)
      qed
      also have "(s \<cdot> (\<sigma> ^^ n \<circ>\<^sub>s \<theta>), t \<cdot> \<theta> ^^ Suc n) \<in> Rel b" unfolding subst_power_Suc 
        using rel_subst[OF Suc, of \<theta>] by simp 
      finally
      show ?case unfolding Rel by (cases b, auto)
    qed
  next
    case (pat_rule_III s t p \<sigma> z n)
    then have p: "p \<in> poss t" by auto
    let ?tzp = "replace_at t p (Var z)"
    let ?tp = "t |_ p"
    let ?taut = "\<lambda> t. \<sigma> (z := t)"
    let ?tau = "?taut ?tzp"
    let ?sig = "subst z ?tp"
    let ?C = "ctxt_of_pos_term p t"
    have "?C \<cdot>\<^sub>c ?sig = ?C \<cdot>\<^sub>c (?sig |s {z})"
      by simp
    also have "... = ?C" 
      by (rule subst_apply_ctxt_id, insert vars_ctxt_pos_term[OF p] pat_rule_III(5), auto)
    finally have id: "?C \<cdot>\<^sub>c ?sig = ?C" .
    show ?case unfolding pt split
    proof (induct n)
      case 0
      have "(s,t) \<in> Rel False" using pat_rule_III(2)[of 0] unfolding pt by simp
      also have "t = replace_at t p (t |_ p)" using ctxt_supt_id[OF p] by auto
      also have "... = replace_at t p (Var z \<cdot> ?sig )" 
        by (simp add: subst_def)
      also have "... = ?tzp \<cdot> ?sig" using id
        by simp
      finally show ?case by simp
    next
      case (Suc n)
      have "s \<cdot> \<sigma> ^^ Suc n = s \<cdot> \<sigma> ^^ n \<cdot> \<sigma>" unfolding subst_power_Suc by simp
      also have "(s \<cdot> \<sigma> ^^ n \<cdot> \<sigma>, ?tzp \<cdot> ?tau ^^ n \<cdot> (?sig \<circ>\<^sub>s \<sigma>)) \<in> Rs" using rel_subst[OF Suc, of \<sigma>] unfolding Rel
        unfolding subst_subst_compose 
        by (metis subst_apply_term_empty)
      also have "?sig \<circ>\<^sub>s \<sigma> = ?taut (?tp \<cdot> \<sigma>)" unfolding subst_compose_def subst_def by auto
      also have "?taut (?tp \<cdot> \<sigma>) = ?taut s" unfolding pat_rule_III(4) ..
      also have "(?tzp \<cdot> ?tau ^^ n \<cdot> ?taut s, ?tzp \<cdot> ?tau ^^ n \<cdot> ?taut t) \<in> (rstep R)^*"
      proof (rule all_ctxt_closed_subst_step)
        fix x
        show "(?taut s x, ?taut t x) \<in> (rstep R)^*"
          by (cases "x = z", insert pat_rule_III(2), auto simp: Rel pt)
      qed auto
      also have "?taut t = ?tau \<circ>\<^sub>s ?sig" 
      proof
        fix x
        show "?taut t x = (?tau \<circ>\<^sub>s ?sig) x"
        proof (cases "x = z")
          case False
          have "?taut t x = \<sigma> x \<cdot> Var" using False by simp
          also have "... = \<sigma> x \<cdot> ?sig"
          proof (rule term_subst_eq)
            fix y
            assume y: "y \<in> vars_term (\<sigma> x)"
            then have "y \<in> vars_subst \<sigma> \<or> x = y" unfolding vars_subst_def subst_range.simps subst_domain_def
              by force
            with pat_rule_III(5) y False have "y \<noteq> z" by auto
            then show "Var y = ?sig y" by (simp add: subst_def)
          qed
          finally show ?thesis unfolding subst_compose_def using False by simp
        next
          case True
          have "?taut t x = t" using True by simp
          also have "... = ?C\<langle>?tp\<rangle>" using ctxt_supt_id[OF p] by simp
          also have "?C = ?C \<cdot>\<^sub>c ?sig" unfolding id ..
          also have "(?C \<cdot>\<^sub>c ?sig)\<langle>?tp\<rangle> = (?tau \<circ>\<^sub>s ?sig) x"
            unfolding subst_compose_def True by (simp add: subst_def)
          finally show ?thesis .
        qed
      qed
      finally show ?case unfolding subst_power_Suc Rel subst_subst by auto
    qed
  next
    case (pat_rule_IV s t s' t' n)
    show ?case using pat_rule_IV(2) 
      unfolding pat_rule_IV(3)
      unfolding pat_rule_IV(4) .
  next
    case (pat_rule_V s \<sigma>s \<mu>s t \<sigma>t \<mu>t b \<rho> n)
    note steps = rel_subst[OF pat_rule_V(2)[unfolded pt split], of n \<rho>]
    from pat_rule_V have "vars_subst \<rho> \<inter> subst_domain \<sigma>s = {}" by auto
    note \<sigma>s = vars_subst_compose'_pow[OF this, of n]
    from pat_rule_V have "vars_subst \<rho> \<inter> subst_domain \<mu>s = {}" by auto
    note \<mu>s = vars_subst_compose'[OF this]    
    have "s \<cdot> \<sigma>s ^^ n \<cdot> (\<mu>s \<circ>\<^sub>s \<rho>) = s \<cdot> (\<sigma>s ^^ n \<circ>\<^sub>s \<rho>) \<cdot> subst_compose' \<mu>s \<rho>"
      unfolding \<mu>s by simp
    also have "... = s \<cdot> \<rho> \<cdot> (subst_compose' \<sigma>s \<rho>)^^n \<cdot> subst_compose' \<mu>s \<rho>" (is "_ = ?s")
      unfolding \<sigma>s by simp
    finally have s: "s \<cdot> \<sigma>s ^^ n \<cdot> \<mu>s \<cdot> \<rho> = ?s" by simp
    from pat_rule_V have "vars_subst \<rho> \<inter> subst_domain \<sigma>t = {}" by auto
    note \<sigma>t = vars_subst_compose'_pow[OF this, of n]
    from pat_rule_V have "vars_subst \<rho> \<inter> subst_domain \<mu>t = {}" by auto
    note \<mu>t = vars_subst_compose'[OF this]    
    have "t \<cdot> \<sigma>t ^^ n \<cdot> (\<mu>t \<circ>\<^sub>s \<rho>) = t \<cdot> (\<sigma>t ^^ n \<circ>\<^sub>s \<rho>) \<cdot> subst_compose' \<mu>t \<rho>"
      unfolding \<mu>t by simp
    also have "... = t \<cdot> \<rho> \<cdot> (subst_compose' \<sigma>t \<rho>)^^n \<cdot> subst_compose' \<mu>t \<rho>" (is "_ = ?t")
      unfolding \<sigma>t by simp
    finally have t: "t \<cdot> \<sigma>t ^^ n \<cdot> \<mu>t \<cdot> \<rho> = ?t" by simp
    from steps
    show ?case unfolding pt split
      unfolding s t by auto      
  next
    case (pat_rule_VI q t \<sigma> \<mu> b u v b' p n)
    obtain \<tau> where tau: "\<tau> = \<sigma> ^^ n \<circ>\<^sub>s \<mu>" by auto
    let ?u\<tau> = "((ctxt_of_pos_term p t) \<cdot>\<^sub>c \<tau>) \<langle>u \<cdot> \<tau>\<rangle>"
    let ?t\<tau> = "replace_at t p v \<cdot> \<tau>"
    let ?Rel = "(if b' then (rstep R \<union> rrstep P) else (rstep R))^*"
    from pat_rule_VI(2) have steps: "(pat_term q n, t \<cdot> \<tau>) \<in> Rel b" unfolding pt tau by auto
    also have "t \<cdot> \<tau> = replace_at t p (t |_p) \<cdot> \<tau>" unfolding ctxt_supt_id[OF pat_rule_VI(5)] ..
    also have "... = replace_at t p u \<cdot> \<tau>" unfolding pat_rule_VI ..
    also have "... = ?u\<tau>" by simp
    finally have steps1: "(pat_term q n, ?u\<tau>) \<in> Rel b" .
    have "(?u\<tau>, ((ctxt_of_pos_term p t) \<cdot>\<^sub>c \<tau>) \<langle>v \<cdot> \<tau>\<rangle>) \<in> ?Rel"
    proof (cases b')
      case True
      from pat_rule_VI(7)[OF True] have p: "p = []" . 
      show ?thesis unfolding p tau using pat_rule_VI(4)[of n] unfolding pt Rel by auto
    next
      case False
      then have b': "b' = False" by simp
      have steps: "((ctxt_of_pos_term p t \<cdot>\<^sub>c \<tau>)\<langle>u \<cdot> \<tau>\<rangle>, (ctxt_of_pos_term p t \<cdot>\<^sub>c \<tau>)\<langle>v \<cdot> \<tau>\<rangle>) \<in> (rstep R)^*"
        by (rule rsteps_closed_ctxt, unfold tau, insert pat_rule_VI(4)[of n] b', simp add: pt Rel)
      then show ?thesis unfolding Rel b' if_False .
    qed
    also have "((ctxt_of_pos_term p t) \<cdot>\<^sub>c \<tau>) \<langle>v \<cdot> \<tau>\<rangle> = replace_at t p v \<cdot> \<tau>" by simp
    finally have "(?u\<tau>,?t\<tau>) \<in> ?Rel" by auto
    with steps1 have steps: "(pat_term q n, ?t\<tau>) \<in> Rel b O ?Rel" by auto
    have "(pat_term q n, ?t\<tau>) \<in> Rel (b \<or> b')"
    proof (rule set_mp[OF _ steps])
      show "Rel b O ?Rel \<subseteq> Rel (b \<or> b')" 
      proof (cases "b \<or> b'")
        case True
        have "Rel b O ?Rel \<subseteq> Rel True O ?Rel" using rel_subset by auto
        also have "... \<subseteq> Rel True"
        proof (cases b')
          case True
          then have b': "b' = True" by simp
          show ?thesis unfolding b' if_True Rel by regexp
        next
          case False
          then have b': "b' = False" by simp
          show ?thesis unfolding b' if_True if_False Rel by regexp
        qed
        finally show ?thesis using True by simp
      next
        case False
        then have b: "(b \<or> b') = False" "b = False" "b' = False" by auto
        show ?thesis unfolding b(1) unfolding Rel b if_False by regexp
      qed
    qed
    then show ?case unfolding pt tau split by simp
  next    
    case (pat_rule_VII s \<sigma>s \<mu>s t \<sigma>t \<mu>t b \<rho> n)
    note steps = rel_subst[OF pat_rule_VII(2)[unfolded pt split], of n "\<rho> ^^ n"]
    have "s \<cdot> \<sigma>s ^^ n \<cdot> \<mu>s \<cdot> \<rho> ^^ n = s \<cdot> \<sigma>s ^^ n \<cdot> (\<mu>s \<circ>\<^sub>s \<rho> ^^ n)" by simp
    also have "... = s \<cdot> (\<sigma>s ^^ n \<circ>\<^sub>s \<rho> ^^ n) \<cdot> \<mu>s" 
      unfolding subst_pow_commute[OF pat_rule_VII(4)] by simp
    also have "... = s \<cdot> (\<sigma>s \<circ>\<^sub>s \<rho>)^^n \<cdot> \<mu>s" 
      unfolding subst_power_commute[OF pat_rule_VII(3)] by simp
    finally have s: "s \<cdot> \<sigma>s ^^ n \<cdot> \<mu>s \<cdot> \<rho> ^^ n = s \<cdot> (\<sigma>s \<circ>\<^sub>s \<rho>)^^n \<cdot> \<mu>s" by simp
    have "t \<cdot> \<sigma>t ^^ n \<cdot> \<mu>t \<cdot> \<rho> ^^ n = t \<cdot> \<sigma>t ^^ n \<cdot> (\<mu>t \<circ>\<^sub>s \<rho> ^^ n)" by simp
    also have "... = t \<cdot> (\<sigma>t ^^ n \<circ>\<^sub>s \<rho> ^^ n) \<cdot> \<mu>t" 
      unfolding subst_pow_commute[OF pat_rule_VII(6)] by simp
    also have "... = t \<cdot> (\<sigma>t \<circ>\<^sub>s \<rho>)^^n \<cdot> \<mu>t" 
      unfolding subst_power_commute[OF pat_rule_VII(5)] by simp
    finally have t: "t \<cdot> \<sigma>t ^^ n \<cdot> \<mu>t \<cdot> \<rho> ^^ n = t \<cdot> (\<sigma>t \<circ>\<^sub>s \<rho>)^^n \<cdot> \<mu>t" by simp
    show ?case unfolding pt split using steps unfolding s t .
  next
    case (pat_rule_VIII s \<sigma>s \<mu>s t \<sigma>t \<mu>t b \<rho> n)
    from rel_subst[OF pat_rule_VIII(2)[unfolded pt split], of n \<rho>]
    show ?case unfolding pt split by simp
  next
    case (pat_rule_IX p t \<sigma> \<mu> b t' \<sigma>' \<mu>' n)
    let ?t = "t \<cdot> (\<sigma> ^^ n \<circ>\<^sub>s \<mu>)"
    let ?t' = "t' \<cdot> \<sigma>' ^^ n \<cdot> \<mu>'"
    from pat_rule_IX have "(pat_term p n, pat_term (t,\<sigma>,\<mu>) n) \<in> Rel b" by auto
    then have steps: "(pat_term p n, ?t) \<in> Rel b" unfolding pt by simp
    have "(?t, t' \<cdot> (\<sigma> ^^ n \<circ>\<^sub>s \<mu>)) \<in> (rstep R)^*" 
      using rsteps_closed_subst[OF pat_rule_IX(3)] .
    also have "t' \<cdot> (\<sigma> ^^ n \<circ>\<^sub>s \<mu>) = t' \<cdot> \<sigma> ^^ n \<cdot> \<mu>" by simp
    also have "(..., t' \<cdot> \<sigma> ^^ n \<cdot> \<mu>') \<in> (rstep R)^*"
      by (rule all_ctxt_closed_subst_step[OF _ pat_rule_IX(5)]) auto 
    also have "(t' \<cdot> \<sigma> ^^ n \<cdot> \<mu>', ?t') \<in> (rstep R)^*" 
    proof (induct n arbitrary: t')
      case 0 then show ?case by simp
    next
      case (Suc n)
      have "t' \<cdot> \<sigma> ^^ Suc n \<cdot> \<mu>' = t' \<cdot> \<sigma> \<cdot> \<sigma> ^^ n \<cdot> \<mu>'" by simp
      also have "(..., t' \<cdot> \<sigma> \<cdot> \<sigma>' ^^ n \<cdot> \<mu>') \<in> (rstep R)^*" by (rule Suc)
      also have "t' \<cdot> \<sigma> \<cdot> \<sigma>' ^^ n \<cdot> \<mu>' = t' \<cdot> (\<sigma> \<circ>\<^sub>s \<sigma>' ^^ n \<circ>\<^sub>s \<mu>')" by simp
      also have "(..., t' \<cdot> (\<sigma>' \<circ>\<^sub>s \<sigma>' ^^ n \<circ>\<^sub>s \<mu>')) \<in> (rstep R)^*" 
      proof (rule all_ctxt_closed_subst_step)
        fix x
        obtain \<gamma> where gamma: "\<gamma> = \<sigma>' ^^ n \<circ>\<^sub>s \<mu>'" by auto
        have "(\<sigma> \<circ>\<^sub>s \<sigma>' ^^ n \<circ>\<^sub>s \<mu>' ) x = (\<sigma> \<circ>\<^sub>s \<gamma>) x" unfolding gamma by (simp add: ac_simps)
        also have "... = \<sigma> x \<cdot> \<gamma>" unfolding subst_compose_def ..
        also have "(..., \<sigma>' x \<cdot> \<gamma>) \<in> (rstep R)^*"
          by (rule rsteps_closed_subst[OF pat_rule_IX(4)])
        also have "\<sigma>' x \<cdot> \<gamma> = (\<sigma>' \<circ>\<^sub>s \<gamma>) x" unfolding subst_compose_def ..
        finally show "((\<sigma> \<circ>\<^sub>s \<sigma>' ^^ n \<circ>\<^sub>s \<mu>') x, (\<sigma>' \<circ>\<^sub>s \<sigma>' ^^ n \<circ>\<^sub>s \<mu>') x) \<in> (rstep R)^*"
          unfolding gamma by (simp add: ac_simps)
      qed auto
      finally show ?case by simp
    qed
    finally have "(?t,?t') \<in> (rstep R)^*" by auto
    with steps have steps: "(pat_term p n, ?t') \<in> Rel b O (rstep R)^*" by auto    
    have "(pat_term p n, ?t') \<in> Rel b"
    proof (rule set_mp[OF _ steps])
      show "Rel b O (rstep R)^* \<subseteq> Rel b"
      proof (cases b)
        case True
        then have b: "b = True" by simp
        show ?thesis unfolding b if_True Rel by regexp
      next
        case False
        then have b: "b = False" by simp
        show ?thesis unfolding b if_True if_False Rel by regexp
      qed
    qed      
    then show ?case unfolding pt by simp
  next
    case (pat_rule_X t \<sigma> \<mu> t' \<sigma>' \<mu>' b k n)
    show ?case using pat_rule_X(2)[of "k + n"]
      unfolding pat_term_def split 
      by (metis (full_types) subst_subst subst_monoid_mult.mult_assoc subst_power_compose_distrib)
  qed
qed

lemma pat_rule_steps_Rs: 
  assumes pat_rule: "(p,q,False) \<in> pat_rule"
  shows "(pat_term p n,pat_term q n) \<in> Rs"
  using pat_rule_steps_main[OF pat_rule] unfolding Rel by auto

lemma pat_rule_steps_RPs: 
  assumes pat_rule: "(p,q,b) \<in> pat_rule"
  shows "(pat_term p n,pat_term q n) \<in> RPs"
  using pat_rule_steps_main[OF pat_rule] rel_subset[of b] unfolding Rel by auto
end

(* in the following we formalize the three conditions which ensure pattern equivalence *)

(* relevant variables, Def. 5 *)
inductive_set pat_rv for t \<sigma>
  where pat_rv_t: "x \<in> vars_term t \<Longrightarrow> x \<in> pat_rv t \<sigma>"
     |  pat_rv_\<sigma>: "x \<in> pat_rv t \<sigma> \<Longrightarrow> y \<in> vars_term (\<sigma> x) \<Longrightarrow> y \<in> pat_rv t \<sigma>"

lemma pat_rv: "x \<in> vars_term (t \<cdot> (\<sigma> ^^ n)) \<Longrightarrow> x \<in> pat_rv t \<sigma>"
proof (induct n arbitrary: x)
  case 0
  with pat_rv_t[of x t \<sigma>] show ?case by simp
next
  case (Suc n)
  from Suc(2)[unfolded subst_power_Suc]
  obtain y where y: "y \<in> vars_term (t \<cdot> \<sigma> ^^ n)" and x: "x \<in> vars_term (\<sigma> y)"
    using vars_term_subst[of "t \<cdot> \<sigma> ^^ n" \<sigma>] by auto
  from pat_rv_\<sigma>[OF Suc(1)[OF y], OF x] show ?case .
qed

lemma pat_rv_rev: "x \<in> pat_rv t \<sigma> \<Longrightarrow> \<exists> n. x \<in> vars_term (t \<cdot> (\<sigma> ^^ n))"
proof (induct rule: pat_rv.induct)
  case (pat_rv_t x)
  then show ?case
    by (intro exI[of _ 0], auto)
next
  case (pat_rv_\<sigma> x y)
  from pat_rv_\<sigma>(2) obtain n where x: "x \<in> vars_term (t \<cdot> \<sigma> ^^ n)" ..
  show ?case
    by (intro exI[of _ "Suc n"], unfold subst_power_Suc, insert x pat_rv_\<sigma>(3), auto simp: vars_term_subst)
qed

(* Lemma 6 *)
lemma pat_equivalence_lem_6: assumes \<sigma>: "\<And> x. x \<in> pat_rv t \<sigma> \<Longrightarrow> \<sigma> x = \<sigma>' x"
  and \<mu>: "\<And> x. x \<in> pat_rv t \<sigma> \<Longrightarrow> \<mu> x = \<mu>' x"
  shows "t \<cdot> \<sigma> ^^ n \<cdot> \<mu> = t \<cdot> \<sigma>' ^^ n \<cdot> \<mu>'"
proof -
  have id: "t \<cdot> \<sigma> ^^ n = t \<cdot> \<sigma>' ^^ n"
  proof (induct n)
    case 0 show ?case by simp
  next
    case (Suc n)
    have "t \<cdot> \<sigma> ^^ Suc n = t \<cdot> \<sigma> ^^ n \<cdot> \<sigma>" unfolding subst_power_Suc by simp
    also have "... = t \<cdot> \<sigma> ^^ n \<cdot> \<sigma>'" 
    proof (rule term_subst_eq)
      fix x
      assume "x \<in> vars_term (t \<cdot> \<sigma> ^^ n)"
      from \<sigma>[OF pat_rv[OF this]] show "\<sigma> x = \<sigma>' x" .
    qed
    also have "... = t \<cdot> \<sigma>' ^^ n \<cdot> \<sigma>'" unfolding Suc ..
    finally show ?case unfolding subst_power_Suc by simp
  qed
  have "t \<cdot> \<sigma> ^^ n \<cdot> \<mu> = t \<cdot> \<sigma> ^^ n \<cdot> \<mu>'"
  proof (rule term_subst_eq)
    fix x
    assume "x \<in> vars_term (t \<cdot> \<sigma> ^^ n)"
    from \<mu>[OF pat_rv[OF this]] show "\<mu> x = \<mu>' x" .
  qed
  then show ?thesis unfolding id .
qed

(* Lemma 9 in [EEG12] *)
lemma pat_equivalence_lem_9: assumes comm: "\<mu>1 \<circ>\<^sub>s \<sigma> = \<sigma> \<circ>\<^sub>s \<mu>1"
  shows "t \<cdot> \<sigma> ^^ n \<cdot> (\<mu>1 \<circ>\<^sub>s \<mu>2) = (t \<cdot> \<mu>1) \<cdot> \<sigma> ^^ n \<cdot> \<mu>2" (is "?l = ?r")
proof -
  have "?l = t \<cdot> (\<sigma> ^^ n \<circ>\<^sub>s \<mu>1) \<cdot> \<mu>2" by simp
  also have "\<sigma> ^^ n \<circ>\<^sub>s \<mu>1 = \<mu>1 \<circ>\<^sub>s \<sigma> ^^ n" using subst_pow_commute[OF comm, of n] by simp
  finally show ?thesis by simp
qed

(* towards domain renamings *)
definition pat_dv :: "('f,'v)pat_term \<Rightarrow> 'v set"
  where "pat_dv p \<equiv> case p of (t,\<sigma>,\<mu>) \<Rightarrow> subst_domain \<sigma> \<union> subst_domain \<mu>"

definition vars_pat_term :: "('f,'v)pat_term \<Rightarrow> 'v set"
  where "vars_pat_term p \<equiv> case p of (t,\<sigma>,\<mu>) \<Rightarrow> vars_term t \<union> vars_subst \<sigma> \<union> vars_subst \<mu>"


lemma pat_rv_vars_pat_term: "x \<in> pat_rv t \<sigma> \<Longrightarrow> x \<in> vars_pat_term (t,\<sigma>,\<mu>)" 
proof (induct rule: pat_rv.induct)
  case (pat_rv_t x)
  then show ?case unfolding vars_pat_term_def by simp
next
  case (pat_rv_\<sigma> x y)
  from pat_rv_\<sigma>(3)
  have "x \<in> subst_domain \<sigma> \<or> x = y" unfolding subst_domain_def by (cases "\<sigma> x", auto)
  with pat_rv_\<sigma>(2) pat_rv_\<sigma>(3)
  show ?case unfolding vars_pat_term_def split vars_subst_def subst_range.simps by auto
qed

(* Definition 3 *)
definition pat_dom_renaming :: "('f,'v)pat_term \<Rightarrow> ('f,'v)subst \<Rightarrow> bool"
  where "pat_dom_renaming p \<rho> \<equiv> is_renaming \<rho> \<and> subst_domain \<rho> \<subseteq> pat_dv p 
    \<and> subst_range \<rho> \<inter> Var ` vars_pat_term p = {}"

(* Lemma 4 *)
lemma pat_equivalence_lem_4: fixes \<rho> \<sigma> \<mu> :: "('f,'v)subst"
  defines \<rho>1: "\<rho>1 \<equiv> is_inverse_renaming \<rho>"
  defines \<sigma>': "\<sigma>' \<equiv> \<lambda> y. if Var y \<in> \<rho> ` subst_domain \<sigma>
                        then Var y \<cdot> \<rho>1 \<cdot> \<sigma> \<cdot> \<rho> else Var y"
  and     \<mu>': "\<mu>' \<equiv> (\<lambda> y. if Var y \<in> \<rho> ` subst_domain \<mu>
                        then Var y \<cdot> \<rho>1 \<cdot> \<mu> \<cdot> \<rho>1 else Var y \<cdot> \<rho>1)"
  assumes \<rho>: "pat_dom_renaming (t,\<sigma>,\<mu>) \<rho>"
  shows "t \<cdot> \<sigma> ^^ n \<cdot> \<mu> = (t \<cdot> \<rho>) \<cdot> \<sigma>' ^^ n \<cdot> \<mu>'" (is "?l = ?r")
proof -
  note \<rho> = \<rho>[unfolded pat_dom_renaming_def]
  then have ren: "is_renaming \<rho>" by simp
  then have var: "\<And> x. is_Var (\<rho> x)" unfolding is_renaming_def by auto
  note inv_dom = is_renaming_inverse_domain[OF ren, unfolded \<rho>1[symmetric]]
  note inv_ran = is_renaming_inverse_range[OF ren, unfolded \<rho>1[symmetric]]
  from ren[unfolded is_renaming_def] have inj: "inj_on \<rho> (subst_domain \<rho>)" by simp
  note inj = inj_onD[OF inj]
  {
    fix x
    assume x: "x \<in> vars_pat_term (t,\<sigma>,\<mu>)"
    with \<rho> have x: "Var x \<notin> subst_range \<rho>" by auto
    from inv_ran[OF x] have invx: "Var x \<cdot> \<rho> \<cdot> \<rho>1 = Var x" by auto
    obtain y where \<rho>x: "\<rho> x = Var y" using var[of x] by auto
    have "Var x \<cdot> \<rho> \<cdot> \<sigma>' = \<sigma> x \<cdot> \<rho>"
    proof (cases "x \<in> subst_domain \<sigma>")
      case True
      from True \<rho>x have "Var y \<in> \<rho> ` subst_domain \<sigma>" by force
      then have "\<sigma>' y = Var y \<cdot> \<rho>1 \<cdot> \<sigma> \<cdot> \<rho>" unfolding \<sigma>' by simp
      also have "... = Var x \<cdot> \<rho> \<cdot> \<rho>1 \<cdot> \<sigma> \<cdot> \<rho>" using \<rho>x by simp
      also have "Var x \<cdot> \<rho> \<cdot> \<rho>1 = Var x" unfolding invx ..
      finally show ?thesis using \<rho>x by simp
    next
      case False
      then have \<sigma>x: "\<sigma> x = Var x" unfolding subst_domain_def by auto
      have "Var y \<notin> \<rho> ` subst_domain \<sigma>" unfolding \<rho>x
      proof
        assume "Var y \<in> \<rho> ` subst_domain \<sigma>" 
        then obtain z where zy: "\<rho> z = Var y" and z: "z \<in> subst_domain \<sigma>" by auto
        then have "z \<in> vars_pat_term (t,\<sigma>,\<mu>)" unfolding vars_pat_term_def vars_subst_def by auto
        with \<rho> have zran: "Var z \<notin> subst_range \<rho>" by auto
        from zy have eq: "\<rho> x = \<rho> z" unfolding \<rho>x by simp
        then have "Var x \<cdot> \<rho> \<cdot> \<rho>1 = Var z \<cdot> \<rho> \<cdot> \<rho>1" by simp
        with invx inv_ran[OF zran] have "x = z" by simp
        with False z show False by auto
      qed
      then have "\<sigma>' y = Var y" unfolding \<sigma>' by simp
      then show ?thesis using \<rho>x \<sigma>x by simp
    qed
  } note 5 = this (* equation (5) in [EEG12] *)
  {
    fix x
    assume "x \<in> vars_pat_term (t,\<sigma>,\<mu>)"
    with \<rho> have x: "Var x \<notin> subst_range \<rho>" by auto
    from inv_ran[OF x] have invx: "Var x \<cdot> \<rho> \<cdot> \<rho>1 = Var x" by auto
    obtain y where \<rho>x: "\<rho> x = Var y" using var[of x] by auto
    have "Var x \<cdot> \<mu> = Var x \<cdot> \<rho> \<cdot> \<mu>'"
    proof (cases "x \<in> subst_domain \<mu>")
      case True
      from True \<rho>x have "Var y \<in> \<rho> ` subst_domain \<mu>" by force
      then have "\<mu>' y = Var y \<cdot> \<rho>1 \<cdot> \<mu> \<cdot> \<rho>1" unfolding \<mu>' by simp
      also have "... = Var x \<cdot> \<rho> \<cdot> \<rho>1 \<cdot> \<mu> \<cdot> \<rho>1" using \<rho>x by simp
      also have "... = Var x \<cdot> \<mu> \<cdot> \<rho>1" unfolding invx ..
      also have "... = Var x \<cdot> \<mu> \<cdot> Var" 
      proof (rule term_subst_eq)
        fix y
        assume "y \<in> vars_term (Var x \<cdot> \<mu>)"
        then have "y = x \<or> y \<in> vars_subst \<mu>" unfolding vars_subst_def subst_range.simps subst_domain_def by force
        then have "y = x \<or> y \<in> vars_pat_term (t,\<sigma>,\<mu>)" unfolding vars_pat_term_def by auto
        with x \<rho> have "Var y \<notin> subst_range \<rho>" by auto
        then show "\<rho>1 y = Var y" unfolding \<rho>1 is_inverse_renaming_def by simp
      qed
      finally show ?thesis using \<rho>x by simp
    next
      case False
      then have x\<mu>: "x \<notin> subst_domain \<mu>" and \<mu>x: "\<mu> x = Var x" unfolding subst_domain_def by auto
      have ydom: "Var y \<notin> \<rho> ` subst_domain \<mu>" 
      proof
        assume "Var y \<in> \<rho> ` subst_domain \<mu>"
        then obtain z where zy: "\<rho> z = Var y" and z: "z \<in> subst_domain \<mu>" by auto
        then have "z \<in> vars_pat_term (t,\<sigma>,\<mu>)" unfolding vars_pat_term_def vars_subst_def by auto
        with \<rho> have zran: "Var z \<notin> subst_range \<rho>" by auto
        from zy have eq: "\<rho> x = \<rho> z" using \<rho>x by simp
        then have "Var x \<cdot> \<rho> \<cdot> \<rho>1 = Var z \<cdot> \<rho> \<cdot> \<rho>1" by simp
        with invx inv_ran[OF zran] z x\<mu>
        show False by auto
      qed          
      from \<rho>x ydom have "Var x \<cdot> \<rho> \<cdot> \<mu>' = Var x \<cdot> \<rho> \<cdot> \<rho>1" unfolding \<mu>' by simp
      also have "... = Var x" by (rule invx)
      finally show ?thesis using \<mu>x by simp
    qed
  } note 6 = this (* equation (6) in [EEG12] *)
  have "t \<cdot> \<sigma> ^^ n \<cdot> \<mu> = t \<cdot> \<sigma> ^^ n \<cdot> (\<rho> \<circ>\<^sub>s \<mu>')"
  proof (rule term_subst_eq)
    fix x
    assume "x \<in> vars_term (t \<cdot> \<sigma> ^^ n)"
    from pat_rv_vars_pat_term[OF pat_rv[OF this]] have "x \<in> vars_pat_term (t,\<sigma>,\<mu>)" .
    from 6[OF this]
    show "\<mu> x = (\<rho> \<circ>\<^sub>s \<mu>') x" unfolding subst_compose_def by simp
  qed
  also have "... = t \<cdot> \<sigma> ^^ n \<cdot> \<rho> \<cdot> \<mu>'" by simp
  also have "t \<cdot> \<sigma> ^^ n \<cdot> \<rho> = t \<cdot> \<rho> \<cdot> \<sigma>' ^^ n" 
  proof (induct n)
    case 0 
    then show ?case by simp
  next
    case (Suc n)
    have "t \<cdot> \<sigma> ^^ Suc n \<cdot> \<rho> = t \<cdot> \<sigma> ^^ n \<cdot> (\<sigma> \<circ>\<^sub>s \<rho>)" 
      unfolding subst_power_Suc by simp
    also have "... = t \<cdot> \<sigma> ^^ n \<cdot> (\<rho> \<circ>\<^sub>s \<sigma>')"
    proof (rule term_subst_eq)
      fix x
      assume "x \<in> vars_term (t \<cdot> \<sigma> ^^ n)"
      from pat_rv_vars_pat_term[OF pat_rv[OF this]] have "x \<in> vars_pat_term (t,\<sigma>,\<mu>)" .
      from 5[OF this]
      show "(\<sigma> \<circ>\<^sub>s \<rho>) x = (\<rho> \<circ>\<^sub>s \<sigma>') x" unfolding subst_compose_def by simp
    qed
    also have "... = t \<cdot> \<sigma> ^^ n \<cdot> \<rho> \<cdot> \<sigma>'" by simp
    also have "... = t \<cdot> \<rho> \<cdot> \<sigma>' ^^ Suc n" unfolding Suc subst_power_Suc by simp
    finally show ?case .
  qed
  finally show ?thesis .
qed  

(* it remains to provide the criterion to conclude nontermination *)
context fixed_trs
begin
(* Theorem 8, generalized for both TRSs (b = False) and (TRS + DPs, b = True)) *)
lemma pat_rule_imp_non_term_main: assumes pat: "((s,\<sigma>,\<mu>), (t,\<sigma>t,\<mu>t),b') \<in> pat_rule"
  and \<sigma>t: "\<sigma>t = \<sigma> ^^ m \<circ>\<^sub>s \<sigma>'"
  and \<mu>t: "\<mu>t = \<mu> \<circ>\<^sub>s \<mu>'"
  and comm\<sigma>: "\<sigma>' \<circ>\<^sub>s \<sigma> = \<sigma> \<circ>\<^sub>s \<sigma>'"
  and comm\<mu>: "\<sigma>' \<circ>\<^sub>s \<mu> = \<mu> \<circ>\<^sub>s \<sigma>'"
  and p: "p \<in> poss t"
  and b: "s \<cdot> \<sigma> ^^ b = t |_ p"
  and b': "b' \<Longrightarrow> p = []"
  shows "\<not> SN (if b' then (rstep R \<union> rrstep P) else rstep R)"
proof -
  let ?R = "{\<rhd>} \<union> rstep R"
  let ?Rel = "if b' then Rel b' else ?R"
  let ?s = "\<lambda> n (\<tau> :: ('f,'v)subst). s \<cdot> \<sigma> ^^ n \<cdot> \<mu> \<cdot> \<tau>"
  {
    fix n and \<tau> :: "('f,'v)subst"
    obtain C where C: "C = ctxt_of_pos_term p t \<cdot>\<^sub>c \<sigma>t ^^ n \<cdot>\<^sub>c \<mu>t" by auto
    from b' have b': "b' \<Longrightarrow> C \<cdot>\<^sub>c \<tau> = \<box>" unfolding C by (cases b', auto)
    from rel_subst[OF pat_rule_steps_main[OF pat, of n], of \<tau>]
    have "(?s n \<tau>, t \<cdot> \<sigma>t ^^ n \<cdot> \<mu>t \<cdot> \<tau>) \<in> Rel b'" unfolding pat_term_def by simp
    also have "t = replace_at t p (t |_ p)" using ctxt_supt_id[OF p] by simp
    also have "replace_at t p (t |_ p) \<cdot> \<sigma>t ^^ n \<cdot> \<mu>t = C\<langle>t |_ p \<cdot> \<sigma>t ^^ n \<cdot> \<mu>t\<rangle>" 
      unfolding C by simp
    also have "t |_ p = s \<cdot> \<sigma> ^^ b" unfolding b ..
    also have "\<sigma>t = \<sigma> ^^ m \<circ>\<^sub>s \<sigma>'" unfolding \<sigma>t ..
    also have "\<mu>t = \<mu> \<circ>\<^sub>s \<mu>'" unfolding \<mu>t ..
    also have "(\<sigma> ^^ m \<circ>\<^sub>s \<sigma>') ^^ n = \<sigma> ^^ (m * n) \<circ>\<^sub>s \<sigma>' ^^ n" 
      unfolding subst_power_commute[OF subst_pow_commute[OF comm\<sigma>, symmetric], symmetric] subst_pow_mult ..
    also have "s \<cdot> \<sigma> ^^ b \<cdot> \<sigma> ^^ (m * n) \<circ>\<^sub>s \<sigma>' ^^ n = s \<cdot> \<sigma> ^^ (m * n + b) \<cdot> \<sigma>' ^^ n" 
      unfolding add.commute[of _ b]
      unfolding subst_power_compose_distrib by simp
    also have "C\<langle>s \<cdot> \<sigma> ^^ (m * n + b) \<cdot> \<sigma>' ^^ n \<cdot> \<mu> \<circ>\<^sub>s \<mu>'\<rangle> \<cdot> \<tau> = (C \<cdot>\<^sub>c \<tau>) \<langle>s \<cdot> \<sigma> ^^ (m * n + b) \<cdot> (\<mu> \<circ>\<^sub>s \<sigma>' ^^ n) \<cdot> (\<mu>' \<circ>\<^sub>s \<tau>)\<rangle>"     
      unfolding subst_pow_commute[OF comm\<mu>[symmetric]] by simp  
    also have "s \<cdot> \<sigma> ^^ (m * n + b) \<cdot> (\<mu> \<circ>\<^sub>s \<sigma>' ^^ n) \<cdot> (\<mu>' \<circ>\<^sub>s \<tau>) = s \<cdot> \<sigma> ^^ (m * n + b) \<cdot> \<mu> \<cdot> (\<sigma>' ^^ n \<circ>\<^sub>s \<mu>' \<circ>\<^sub>s \<tau>)" by simp
    finally obtain C \<tau>' k where steps: "(?s n \<tau>, C\<langle>?s k \<tau>'\<rangle>) \<in> Rel b'" (is "(?l,_\<langle>?r\<rangle>) \<in> _") and b': "b' \<Longrightarrow> C = \<box>"
      using b' by blast+
    have "(?s n \<tau>, ?s k \<tau>') \<in> ?Rel^+"
    proof (cases b')
      case True
      from steps b'[OF True] True show ?thesis by simp
    next
      case False
      with steps have "(?l,C\<langle>?r\<rangle>) \<in> Rs" unfolding Rel by auto
      with ctxt_supteq[OF refl, of C ?r] 
      have "(?l,?r) \<in> Rs O {\<unrhd>}" by auto
      with supteq_rtrancl_supt have "(?l,?r) \<in> ?R^+" by auto
      then show ?thesis using False by auto
    qed    
    then have "\<exists> k \<tau>'. (?s n \<tau>, ?s k \<tau>') \<in> ?Rel^+" by blast
  }
  then have steps: "\<forall> n \<tau>. \<exists> k t'. (?s n \<tau>, ?s k t') \<in> ?Rel^+" by auto
  obtain t where t: "t = (\<lambda> n\<tau>. ?s (fst n\<tau>) (snd n\<tau>))" by auto
  from steps have "\<forall> n\<tau>. \<exists> k\<tau>'. (t n\<tau>, t k\<tau>') \<in> ?Rel^+" unfolding t by auto
  from choice[OF this] obtain f where "\<And> x. (t x, t (f x)) \<in> ?Rel^+" by blast
  from steps_imp_not_SN[of t f, OF this] have nSN: "\<not> SN (?Rel^+)" by auto
  show ?thesis
  proof (cases b')
    case True
    then have b': "b' = True" by simp
    show ?thesis using nSN unfolding SN_trancl_SN_conv Rel b' if_True .
  next
    case False
    then have b': "b' = False" by simp
    from SN_supt_rstep_trancl[of R] nSN show ?thesis unfolding Rel b' if_False by blast
  qed
qed

lemma pat_rule_imp_non_term_R: assumes pat: "((s,\<sigma>,\<mu>), (t,\<sigma>t,\<mu>t),False) \<in> pat_rule"
  and \<sigma>t: "\<sigma>t = \<sigma> ^^ m \<circ>\<^sub>s \<sigma>'"
  and \<mu>t: "\<mu>t = \<mu> \<circ>\<^sub>s \<mu>'"
  and comm\<sigma>: "\<sigma>' \<circ>\<^sub>s \<sigma> = \<sigma> \<circ>\<^sub>s \<sigma>'"
  and comm\<mu>: "\<sigma>' \<circ>\<^sub>s \<mu> = \<mu> \<circ>\<^sub>s \<sigma>'"
  and p: "p \<in> poss t"
  and b: "s \<cdot> \<sigma> ^^ b = t |_ p"
  shows "\<not> SN (rstep R)"
  using pat_rule_imp_non_term_main[OF pat \<sigma>t \<mu>t comm\<sigma> comm\<mu> p b] by simp

lemma pat_rule_imp_non_term_PR: assumes pat: "((s,\<sigma>,\<mu>), (t,\<sigma>t,\<mu>t),b') \<in> pat_rule"
  and \<sigma>t: "\<sigma>t = \<sigma> ^^ m \<circ>\<^sub>s \<sigma>'"
  and \<mu>t: "\<mu>t = \<mu> \<circ>\<^sub>s \<mu>'"
  and comm\<sigma>: "\<sigma>' \<circ>\<^sub>s \<sigma> = \<sigma> \<circ>\<^sub>s \<sigma>'"
  and comm\<mu>: "\<sigma>' \<circ>\<^sub>s \<mu> = \<mu> \<circ>\<^sub>s \<sigma>'"
  and p: "p \<in> poss t"
  and b: "s \<cdot> \<sigma> ^^ b = t |_ p"
  and b': "b' \<Longrightarrow> p = []"
  shows "\<not> SN (rstep R \<union> rrstep P)"
proof -
  let ?P = "rstep R \<union> rrstep P"
  let ?RP = "if b' then ?P else rstep R"
  have subset: "?RP \<subseteq> ?P" by auto
  from pat_rule_imp_non_term_main[OF pat \<sigma>t \<mu>t comm\<sigma> comm\<mu> p b b'] 
  have "\<not> SN ?RP" by auto
  with SN_subset[OF _ subset]
  show ?thesis by auto
qed

end

end

