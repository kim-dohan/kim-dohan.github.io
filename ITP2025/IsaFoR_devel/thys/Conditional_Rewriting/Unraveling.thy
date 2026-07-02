(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2014, 2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)

theory Unraveling
  imports 
    Quasi_Decreasingness
    First_Order_Rewriting.Parallel_Rewriting
begin

text \<open>This formalization is described in an RTA 2015 submission, and certain lemma/theorem/... numbers
  refer to this paper.\<close>

text \<open>The locale for unraveling corresponds to generalized unravelings in the paper\<close>
locale unraveling =  
  fixes R :: "('f,'v)ctrs"
    and U :: "('f,'v)crule \<Rightarrow> nat \<Rightarrow> ('f,'v)ctxt"
    (* e.g., U ((l,r),s1 = t1, ... sn = tn) i = U_i(\<box>,vars(l) \<union> vars(t1) ... \<union> vars(t i-1) *)
begin

fun lhs_n :: "('f,'v)crule \<Rightarrow> nat \<Rightarrow> ('f,'v)term"
  where "lhs_n (lr,cs) 0 = fst lr"
  | "lhs_n (lr,cs) (Suc n) = (U (lr,cs) n) \<langle>snd (cs ! n)\<rangle>"

fun rhs_n :: "('f,'v)crule \<Rightarrow> nat \<Rightarrow> ('f,'v)term"
  where "rhs_n (lr,cs) n = (if n < length cs then 
         (U (lr,cs) n)\<langle>fst (cs ! n)\<rangle>
         else snd lr)"

definition rules :: "('f,'v)crule \<Rightarrow> ('f,'v)trs"
  where "rules crule \<equiv> (\<lambda> n. (lhs_n crule n, rhs_n crule n)) ` {n . n \<le> length (snd crule)}"

lemma finite_rule: "finite (rules crule)" unfolding rules_def by auto

definition UR :: "('f, 'v) trs" where
  "UR \<equiv> \<Union>(rules ` R)"

lemma finite_UR: "finite R \<Longrightarrow> finite UR" unfolding UR_def using finite_rule by auto

lemma rules_unconditional[simp]: "rules ((l,r),[]) = {(l,r)}"  unfolding rules_def by simp

lemma UR_simulation_main: assumes lr: "((l, r), cs) \<in> R"
  and i: "i \<le> length cs"
  and cs: "\<And> j. j < i \<Longrightarrow> (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*"
shows "(l \<cdot> \<sigma>, rhs_n ((l,r),cs) i \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>+"
proof -
  let ?lr = "((l,r),cs)"
  let ?n = "length cs"
  from lr have lr: "rules ?lr \<subseteq> UR" unfolding UR_def by auto
  then have lr: "\<And> i. i \<le> ?n \<Longrightarrow> (lhs_n ?lr i, rhs_n ?lr i) \<in> UR" unfolding rules_def
    by auto
  show ?thesis
  proof (rule rtrancl_into_trancl2)
    show "(l \<cdot> \<sigma>,rhs_n ?lr 0 \<cdot> \<sigma>) \<in> rstep UR"
      by (rule rstepI[OF lr[of 0], of _ Hole \<sigma>], auto)
    from i cs
    show "(rhs_n ?lr 0 \<cdot> \<sigma>, rhs_n ?lr i \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*"
    proof (induct i)
      case (Suc i)
      then have i: "i < ?n" and i': "i \<le> ?n" by auto
      let ?f = "U ?lr i"
      let ?U = "\<lambda> t. ?f \<langle> t \<rangle>"
      from Suc(1)[OF i' Suc(3)]
      have "(rhs_n ?lr 0 \<cdot> \<sigma>, rhs_n ?lr i \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*" by simp
      also have "rhs_n ?lr i = ?U (fst (cs ! i))"
        using i by simp
      also have "(?U (fst (cs ! i)) \<cdot> \<sigma>, ?U (snd (cs ! i)) \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*" 
      proof -
        obtain si ti where csi: "cs ! i = (si,ti)" by force
        from Suc(3)[of i, unfolded csi] have "(si \<cdot> \<sigma>, ti \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*" by simp
        from ctxt.closedD[OF ctxt.closed_rtrancl[OF ctxt_closed_rstep] this]
        have "\<And> C. (C\<langle>si \<cdot> \<sigma>\<rangle>, C\<langle>ti \<cdot> \<sigma>\<rangle>) \<in> (rstep UR)\<^sup>*" .
        from this[of "?f \<cdot>\<^sub>c \<sigma>"]
        show ?thesis unfolding csi by simp
      qed
      also have "?U (snd (cs ! i)) = lhs_n ?lr (Suc i)" 
        unfolding lhs_n.simps by simp
      also have "(lhs_n ?lr (Suc i) \<cdot> \<sigma>, rhs_n ?lr (Suc i) \<cdot> \<sigma>) \<in> (rstep UR)"
        by (rule rstepI[OF lr[OF Suc(2)], of _ Hole \<sigma>], auto)
      finally show ?case .
    qed simp
  qed
qed

lemma SN_quasi_reductive_order: assumes SN: "SN (rstep UR)"
  shows "quasi_reductive_order R ((rstep UR)\<^sup>+)"
proof -
  let ?S = "(rstep UR)\<^sup>+"
  let ?NS = "(rstep UR)\<^sup>*"
  have id: "?S^= = ?NS" by simp
  show ?thesis unfolding quasi_reductive_order_def id
  proof (intro conjI allI impI)
    show "SN ?S" by (rule SN_imp_SN_trancl[OF SN])
  next
    fix l r cs \<sigma>
    assume lr: "((l, r), cs) \<in> R"
      and cs: "\<forall>j<length cs. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*"
    from UR_simulation_main[OF lr, of "length cs" \<sigma>] cs
    show "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>+" by simp
  next
    fix l r cs \<sigma> i
    assume lr: "((l, r), cs) \<in> R"
      and i: "i < length cs"
      and cs: "\<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*"
    from UR_simulation_main[OF lr, of i \<sigma>] i cs
    have lm: "(l \<cdot> \<sigma>, rhs_n ((l, r), cs) i \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>+" (is "(?l,?m) \<in> _") by simp
    have mr: "?m \<unrhd> fst (cs ! i) \<cdot> \<sigma>" (is "_ \<unrhd> ?r")
      by (rule supteq_subst, insert i, auto)
    let ?R = "(rstep UR)\<^sup>+ \<union> {\<rhd>}"
    from mr have "(?m,?r) \<in> ({\<rhd>})^=" by auto
    then have mr: "(?m,?r) \<in> ?R\<^sup>*" by auto
    have lm: "(?l,?m) \<in> ?R\<^sup>+"
      by (rule trancl_mono[OF lm], auto)
    from lm mr show lr: "(?l,?r) \<in> ?R\<^sup>+" by auto
  qed auto
qed

lemma SN_quasi_reductive: "SN (rstep UR) \<Longrightarrow> quasi_reductive R"
  unfolding quasi_reductive_def
  by (rule exI, rule SN_quasi_reductive_order)


lemma completeness: assumes step: "(s,t) \<in> cstep R"
  shows "(s,t) \<in> (rstep UR)\<^sup>+"
proof -
  from step[unfolded cstep_def] obtain n where "(s,t) \<in> cstep_n R n" ..
  then show ?thesis
  proof (induct n arbitrary: s t)
    case 0 then show ?case by simp
  next
    case (Suc n) note IH = this
    from IH(2) obtain l r cs C \<sigma> where lr: "((l,r),cs) \<in> R" and
      cs: "\<And> si ti.  (si,ti) \<in> set cs \<Longrightarrow> (si \<cdot> \<sigma>, ti \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
      and s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>" and t: "t = C \<langle> r \<cdot> \<sigma> \<rangle>" by (blast elim: cstep_n_SucE)
    let ?lr = "((l,r),cs)"
    let ?n = "length cs"
    have rsig: "r \<cdot> \<sigma> = rhs_n ?lr ?n \<cdot> \<sigma>" by auto
    have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>+" unfolding rsig
    proof (rule UR_simulation_main[OF lr, of "length cs" \<sigma>])
      fix j
      assume j: "j < length cs"
      obtain sj tj where csj: "cs ! j = (sj,tj)" by force
      from j have "(sj,tj) \<in> set cs" unfolding csj[symmetric] set_conv_nth by auto
      from cs[OF this] have steps: "(sj \<cdot> \<sigma>, tj \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*" .
      {
        fix s t
        assume "(s,t) \<in> (cstep_n R n)\<^sup>*"
        then have "(s,t) \<in> (rstep UR)\<^sup>*"
        proof (induct)
          case (step t u)
          from step(3) IH(1)[OF step(2)] show ?case by auto
        qed simp
      }
      from this[OF steps]
      show "(fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*" 
        unfolding csj by auto
    qed simp
    from ctxt.closedD[OF ctxt.closed_trancl[OF ctxt_closed_rstep] this, of C]
    show ?case unfolding s t .
  qed
qed

definition Z_vars :: "(('f,'v)crule \<Rightarrow> nat \<Rightarrow> 'v list) \<Rightarrow> bool" where
  "Z_vars Z  = ((\<forall> \<rho> \<in> R. \<forall> i < length (snd \<rho>).
   set (Z \<rho> i) \<supseteq>  X_vars \<rho> i \<inter> Y_vars \<rho> i \<and> distinct (Z \<rho> i)))"

abbreviation ultra :: "(('f,'v) trs \<Rightarrow> bool) \<Rightarrow> bool" where "ultra P \<equiv> P (UR)"

abbreviation ultra_rule :: "(('f,'v) trs \<Rightarrow> bool) \<Rightarrow> ('f,'v) crule \<Rightarrow> bool" 
  where "ultra_rule P \<rho> \<equiv> P (rules \<rho>)"


(* The following two definitions capture properties of Z required by the soundness proof. They are 
   satisfied by both U_opt and U_seq. *)
definition Z_cond_0 :: "(('f,'v)crule \<Rightarrow> nat \<Rightarrow> 'v list) \<Rightarrow> bool"
  where"Z_cond_0 Z \<equiv> \<forall>\<rho>\<in>R. length (snd \<rho>) > 0 \<longrightarrow> (set (Z \<rho> 0) \<subseteq> vars_term (clhs \<rho>) \<and> (vars_term (snd (snd \<rho> ! 0)) \<inter> set (Z \<rho> 0)) = {})"

definition Z_cond_Suc :: "(('f,'v)crule \<Rightarrow> nat \<Rightarrow> 'v list) \<Rightarrow> bool"
  where"Z_cond_Suc Z \<equiv> \<forall>\<rho>\<in>R. \<forall>k. length (snd \<rho>) = Suc k \<longrightarrow> (\<forall>n < k. 
  set (Z \<rho> (Suc n)) \<subseteq> set (Z \<rho> n) \<union> vars_term (snd (snd \<rho> ! n)) \<and> vars_term (snd (snd \<rho> ! Suc n)) \<inter> set (Z \<rho> (Suc n)) = {})"
end

definition source_preserving :: "('f,'v)ctrs \<Rightarrow> (('f,'v)crule \<Rightarrow> nat \<Rightarrow> 'v list) \<Rightarrow> bool"
  where "source_preserving R Z \<equiv> (\<forall> \<rho> \<in> R. (\<forall> i < length (snd \<rho>). 
          (vars_term (clhs \<rho>) \<subseteq> set (Z \<rho> i))))" 

abbreviation si :: "('f,'v) crule \<Rightarrow> nat \<Rightarrow> ('f,'v) term" where "si \<rho> i \<equiv> fst ((snd \<rho>)!i)"
abbreviation ti :: "('f,'v) crule \<Rightarrow> nat \<Rightarrow> ('f,'v) term" where "ti \<rho> i \<equiv> snd ((snd \<rho>)!i)"

definition prefix_equivalent :: "('f,'v)crule \<Rightarrow> ('f,'v)crule \<Rightarrow> nat \<Rightarrow> bool"
  where "prefix_equivalent \<rho> \<rho>' m \<equiv> (
         m < length(snd \<rho>) \<and> m < length(snd \<rho>') \<and> 
         clhs \<rho> = clhs \<rho>' \<and> (\<forall>i < m. ti \<rho> i = ti \<rho>' i) \<and> (\<forall>i \<le> m. si \<rho> i = si \<rho>' i))"

definition "U_cond U R F Z \<equiv> \<forall> \<rho> n. \<rho> \<in> R \<longrightarrow> n < length (snd \<rho>) \<longrightarrow> (\<exists> f. 
   (U \<rho> n = (More f Nil Hole (map Var (Z \<rho> n)))  \<and> f \<notin> F \<and>
    (\<forall> \<rho>' n' g b c a.  (\<rho>' \<in> R \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a) \<longrightarrow> 
      f \<noteq> g \<or> (n = n' \<and> (\<forall>i \<le>n. U \<rho> i = U \<rho>' i) \<and> prefix_equivalent \<rho> \<rho>' n))))"

lemma U_condD: "U_cond U R F Z \<Longrightarrow> \<rho> \<in> R \<Longrightarrow> n < length (snd \<rho>) \<Longrightarrow> \<exists> f. 
   (U \<rho> n = (More f Nil Hole (map Var (Z \<rho> n)))  \<and> f \<notin> F \<and>
    (\<forall> \<rho>' n' g b c a.  (\<rho>' \<in> R \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a) \<longrightarrow> f \<noteq> g \<or> (n = n' \<and> (\<forall>i \<le>n. U \<rho> i = U \<rho>' i) \<and> prefix_equivalent \<rho> \<rho>' n)))"
  unfolding U_cond_def by blast

lemma U_condI: assumes "\<And> \<rho> n. \<rho> \<in> R \<Longrightarrow> n < length (snd \<rho>) \<Longrightarrow> \<exists> f. 
   (U \<rho> n = (More f Nil Hole (map Var (Z \<rho> n)))  \<and> f \<notin> F \<and>
    (\<forall> \<rho>' n' g b c a.  (\<rho>' \<in> R \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a) \<longrightarrow> f \<noteq> g \<or> (n = n' \<and> (\<forall>i \<le>n. U \<rho> i = U \<rho>' i) \<and> prefix_equivalent \<rho> \<rho>' n)))"
  shows "U_cond U R F Z" using assms unfolding U_cond_def by blast

text \<open>The locale for the normal unraveling transformation.
  This is Def. 6.1 (U_n) in \<open>Unravelings and Ultra-properties\<close> of Marchiori.\<close>
locale normal_unraveling =  
  fixes R :: "('f,'v)ctrs"
    and U :: "('f,'v)crule \<Rightarrow> ('f \<times> ('f,'v)term list) option"
    (* e.g., U ((l,r),s1 = t1, ... sn = tn) = Some (U_i, vars(l) or
             U ((l,r)) = None for unconditional rules,
       then U ((l,r),s1 = t1, ... sn = tn) = {
            l \<rightarrow> U_i(s1,...,sn, vars(l))
            U_i(t1,...,tn, vars(l)) \<rightarrow> r
         } *)
begin

definition rules :: "('f,'v)crule \<Rightarrow> ('f,'v)trs"
  where "rules crule = (case U crule of 
     None \<Rightarrow> {fst crule}
   | Some (f, ctxt) \<Rightarrow> let conds = snd crule; lr = fst crule in
       if conds = [] then { lr } else { (fst lr, Fun f (map fst conds @ ctxt)),
         (Fun f (map snd conds @ ctxt), snd lr)})"

lemma finite_rule: "finite (rules crule)" unfolding rules_def by (auto split: option.splits simp: Let_def)

definition UR :: "('f, 'v) trs" where
  "UR \<equiv> \<Union>(rules ` R)"

lemma finite_UR: "finite R \<Longrightarrow> finite UR" unfolding UR_def using finite_rule by auto

lemma rules_unconditional[simp]: "rules ((l,r),[]) = {(l,r)}"  unfolding rules_def 
  by (auto split: option.splits simp: Let_def)

lemma UR_simulation_main: assumes lr: "((l, r), cs) \<in> R"
  and cs: "\<And> j. j < length cs \<Longrightarrow> (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*"
shows "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>+"
proof -
  let ?lr = "((l,r),cs)"
  let ?n = "length cs"
  from lr have lr: "rules ?lr \<subseteq> UR" unfolding UR_def by auto
  show ?thesis 
  proof (cases "U ?lr = None \<or> cs = []")
    case True
    hence "(l,r) \<in> rules ?lr" unfolding rules_def Let_def by (auto split: option.splits)
    with lr have "(l,r) \<in> UR" by auto
    hence "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep UR" by auto
    thus ?thesis by blast
  next
    case False
    then obtain f ctxt where U: "U ?lr = Some (f, ctxt)" by (cases "U ?lr", auto)
    let ?r1 = "Fun f (map fst cs @ ctxt)" 
    let ?l2 = "Fun f (map snd cs @ ctxt)" 
    from U False
    have "{(l, ?r1), (?l2, r)} \<subseteq> rules ?lr"
      unfolding rules_def Let_def by (auto split: option.splits)
    with lr have lr: "{(l, ?r1), (?l2, r)} \<subseteq> UR" by auto
    from lr have "(l \<cdot> \<sigma>, ?r1 \<cdot> \<sigma>) \<in> rstep UR" by blast
    moreover have "(?r1 \<cdot> \<sigma>, ?l2 \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*" unfolding eval_term.simps
      apply (rule all_ctxt_closedD[OF all_ctxt_closed_rsteps[of UNIV]], force, force)
      subgoal for i using cs[of i] by (cases "i < length cs", auto simp: nth_append)
      by auto
    moreover have "(?l2 \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep UR" using lr by blast
    ultimately show "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>+" by simp
  qed
qed

lemma completeness: assumes step: "(s,t) \<in> cstep R"
  shows "(s,t) \<in> (rstep UR)\<^sup>+"
proof -
  from step[unfolded cstep_def] obtain n where "(s,t) \<in> cstep_n R n" ..
  then show ?thesis
  proof (induct n arbitrary: s t)
    case 0 then show ?case by simp
  next
    case (Suc n) note IH = this
    from IH(2) obtain l r cs C \<sigma> where lr: "((l,r),cs) \<in> R" and
      cs: "\<And> si ti.  (si,ti) \<in> set cs \<Longrightarrow> (si \<cdot> \<sigma>, ti \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
      and s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>" and t: "t = C \<langle> r \<cdot> \<sigma> \<rangle>" by (blast elim: cstep_n_SucE)
    let ?lr = "((l,r),cs)"
    let ?n = "length cs"
    have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>+" 
    proof (rule UR_simulation_main[OF lr])
      fix j
      assume j: "j < length cs"
      obtain sj tj where csj: "cs ! j = (sj,tj)" by force
      from j have "(sj,tj) \<in> set cs" unfolding csj[symmetric] set_conv_nth by auto
      from cs[OF this] have steps: "(sj \<cdot> \<sigma>, tj \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*" .
      {
        fix s t
        assume "(s,t) \<in> (cstep_n R n)\<^sup>*"
        then have "(s,t) \<in> (rstep UR)\<^sup>*"
        proof (induct)
          case (step t u)
          from step(3) IH(1)[OF step(2)] show ?case by auto
        qed simp
      }
      from this[OF steps]
      show "(fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (rstep UR)\<^sup>*" 
        unfolding csj by auto
    qed
    from ctxt.closedD[OF ctxt.closed_trancl[OF ctxt_closed_rstep] this, of C]
    show ?case unfolding s t .
  qed
qed

end

lemma infeasibility_via_normal_unravel:
  assumes
    "(s, t) \<in> set cs"
    "ground s" "ground t"
    "(s, t) \<notin> (rstep (normal_unraveling.UR R U))\<^sup>*" 
  shows "\<not> conds_sat R cs \<sigma>"
proof
  interpret normal_unraveling R U .
  from assms
  have st: "(s, t) \<in> set cs \<and> ground s \<and> ground t \<and> (s, t) \<notin> (rstep UR)\<^sup>*" by blast
  assume "conds_sat R cs \<sigma>"
  from this[unfolded conds_sat_iff] st ground_subst_apply[of s] ground_subst_apply[of t]
  have "(s, t) \<in> (cstep R)\<^sup>*" by auto
  also have "(cstep R)\<^sup>* \<subseteq> ((rstep UR)\<^sup>+)\<^sup>*" using completeness
    by (meson rtrancl_mono subrelI)
  also have "((rstep UR)\<^sup>+)\<^sup>* = (rstep UR)\<^sup>*" using rtrancl_trancl_absorb by simp
  finally have "(s, t) \<in> (rstep UR)\<^sup>*" by simp
  then show False using st by simp
qed

(* locale demanding conditions satisfied by U_opt, U_seq, and U_conf *)
locale standard_unraveling = unraveling R U 
  for R :: "('f,'v) ctrs" and U :: "('f,'v) crule \<Rightarrow> nat \<Rightarrow> ('f,'v) ctxt" +
  fixes F :: "'f set" and Z :: "('f,'v)crule \<Rightarrow> nat \<Rightarrow> 'v list"
  assumes F: "funs_ctrs R \<subseteq> F" and Ucond: "U_cond U R F Z"
    and Z:"Z_vars Z" 
    and dctrs:"dctrs R"
    and type3:"type3 R"
    and inf_var: "infinite (UNIV :: 'v set)"
begin

lemmas U_cond = U_condD[OF Ucond]    

definition "dvars n = (SOME xs. length xs = n \<and> distinct (xs :: 'v list))"

lemma distinct_vars: "length (dvars n) = n \<and> distinct (dvars n)"
  unfolding dvars_def
  by (rule someI_ex, insert infinite_imp_many_elems[OF inf_var, of n], auto)

abbreviation U_fun :: "('f,'v) crule \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> bool" 
  where "U_fun \<rho> k Uk \<equiv> (U \<rho> k = (More Uk Nil Hole (map Var (Z \<rho> k))))"


lemma funas_UR:"funas_trs UR = funas_ctrs R \<union> {(Uk, Suc (length (Z \<rho> k))) |\<rho> k Uk. \<rho> \<in> R \<and> k < length (snd \<rho>) \<and> U_fun \<rho> k Uk}"
proof(rule, rule)
  fix f n
  assume f:"(f, n) \<in> funas_trs UR"
  let ?Us = "{(Uk, Suc (length (Z \<rho> k))) |\<rho> k Uk. \<rho> \<in> R \<and> k < length (snd \<rho>) \<and> U_fun \<rho> k Uk}"
  let ?rhs = "funas_ctrs R \<union> ?Us"
  from f[unfolded UR_def funas_trs_def] rules_def obtain \<rho> i where rl:"(f,n) \<in> funas_rule (lhs_n \<rho> i, rhs_n \<rho> i)" "i \<le> length (snd \<rho>)" "\<rho> \<in> R" by auto
  obtain l r cs where rho:"\<rho> = ((l,r),cs)" by (cases \<rho>, auto)
  { assume fl:"(f,n) \<in> funas_term (lhs_n \<rho> i)"
    have "(f,n) \<in> ?rhs" proof (cases i)
      case 0 
      from fl[unfolded 0 rho lhs_n.simps] have "(f,n) \<in> funas_rule (fst \<rho>)" unfolding funas_rule_def rho by simp
      with rl(3) funas_crule_def show "(f,n) \<in> ?rhs" unfolding funas_ctrs_def by blast
    next
      case (Suc j)
      with rl have j:"j < length (snd \<rho>)" by auto
      from U_cond[OF rl(3) j] obtain g where g:"U \<rho> j = (More g Nil Hole (map Var (Z \<rho> j)))" by fast
      from fl[unfolded funas_term_conv] have or:"Some (f,n) = root (lhs_n \<rho> i) \<or> (f,n) \<in> funas_args_term (lhs_n \<rho> i)" by force
      { assume "Some (f,n) = root (lhs_n \<rho> i)" 
        from this[unfolded Suc rho  lhs_n.simps g[unfolded rho]]  have "f=g \<and> n = Suc (length (Z \<rho> j))" unfolding rho by simp
        from g this j rl(3) have "(f,n) \<in> ?Us" 
          unfolding mem_Collect_eq by blast
      } note A = this
      { assume "(f,n) \<in> funas_args_term (lhs_n \<rho> i)"
        from this[unfolded Suc rho lhs_n.simps g[unfolded rho] intp_actxt.simps funas_args_term_def] have "(f,n) \<in> funas_term (snd (cs ! j))" by simp
        with j funas_rule_def have "(f,n) \<in> funas_trs (set (snd \<rho>))" unfolding rho funas_trs_def set_conv_nth snd_conv by fast
        with rho rl funas_crule_def have "(f,n) \<in> funas_ctrs R" unfolding funas_ctrs_def by blast
      }
      with A or show "(f,n) \<in> ?rhs" by fast
    qed
  } note left = this
  { assume fr:"(f,n) \<in> funas_term (rhs_n \<rho> i)"
    have "(f,n) \<in> ?rhs" proof (cases "i = length (snd \<rho>)")
      case True
      from fr[unfolded True rho rhs_n.simps] have "(f,n) \<in> funas_rule (fst \<rho>)" unfolding funas_rule_def rho by simp
      with rl(3) funas_crule_def show "(f,n) \<in> ?rhs" unfolding funas_ctrs_def by blast
    next
      case False
      with rl rho have i:"i < length cs" by auto
      with U_cond[OF rl(3)] rho obtain g where g:"U \<rho> i = (More g Nil Hole (map Var (Z \<rho> i)))" by fastforce
      from fr[unfolded funas_term_conv] have or:"Some (f,n) = root (rhs_n \<rho> i) \<or> (f,n) \<in> funas_args_term (rhs_n \<rho> i)" by force
      { assume "Some (f,n) = root (rhs_n \<rho> i)"
        from this[unfolded rho rhs_n.simps g[unfolded rho]] i have "f=g \<and> n = Suc (length (Z \<rho> i))" unfolding rho by simp
        with g i rl(3) rho have "(f,n) \<in> ?Us" 
          unfolding mem_Collect_eq by auto
      } note A = this
      { assume "(f,n) \<in> funas_args_term (rhs_n \<rho> i)"
        from i this[unfolded rho rhs_n.simps g[unfolded rho] intp_actxt.simps funas_args_term_def] have "(f,n) \<in> funas_term (fst (cs ! i))" by simp
        with i funas_rule_def have "(f,n) \<in> funas_trs (set (snd \<rho>))" unfolding rho funas_trs_def set_conv_nth snd_conv by fast
        with rho rl funas_crule_def have "(f,n) \<in> funas_ctrs R" unfolding funas_ctrs_def by blast
      }
      with A or show "(f,n) \<in> ?rhs" by fast
    qed
  }
  with rl(1) left show "(f,n) \<in> ?rhs" unfolding rho funas_rule_def by auto
next
  { fix fn \<rho> i
    assume *:"\<rho> \<in> R" and i:"i \<le> length (snd \<rho>)" and f:"fn \<in> funas_term (rhs_n \<rho> i) \<or> fn \<in> funas_term (lhs_n \<rho> i)"
    obtain l r cs where rho:"\<rho> = ((l,r), cs)" by (cases \<rho>, auto)
    from f have "fn \<in> funas_rule (lhs_n \<rho> i, rhs_n \<rho> i)" unfolding funas_rule_def rho by auto
    with i have "fn \<in> funas_trs (rules \<rho>)" unfolding funas_trs_def rho rules_def by fast
    then have "fn \<in> funas_trs UR" unfolding UR_def funas_trs_def using * by blast
  } note aux = this
  { fix f n
    assume f:"(f,n) \<in> funas_ctrs R"
    from f[unfolded funas_ctrs_def] obtain \<rho> where *:"\<rho> \<in> R" "(f,n) \<in> funas_crule \<rho>" by blast
    from this[unfolded funas_crule_def] have *:"\<rho> \<in> R" "(f,n) \<in> funas_rule (fst \<rho>) \<or> (f,n) \<in> funas_trs (set (snd \<rho>))" by (blast, blast)
    obtain l r cs where rho:"\<rho> = ((l,r), cs)" by (cases \<rho>, auto)
    { assume "(f,n) \<in> funas_term l"
      then have "(f,n) \<in> funas_term (lhs_n \<rho> 0)" unfolding rho by auto
      from aux[OF *(1) le0] this have "(f,n) \<in> funas_trs UR" by blast
    } note A = this
    { assume "(f,n) \<in> funas_term r"
      then have "(f,n) \<in> funas_term (rhs_n \<rho> (length cs))" unfolding rho by auto
      from aux[OF *(1) le_refl] this have "(f,n) \<in> funas_trs UR" unfolding rho by simp
    } note B = this
    { assume "(f,n) \<in> funas_trs (set cs)"
      then obtain si ti where lr:"(f,n) \<in> funas_rule (si,ti)" "(si,ti) \<in> set cs" unfolding funas_trs_def by force
      from this(2)[unfolded set_conv_nth] obtain i where i:"i < length cs" "cs ! i = (si,ti)" by force
      from U_cond[OF *(1)] i obtain Ui where Ui:"U_fun \<rho> i Ui" unfolding rho by fastforce
      { assume fsi:"(f,n) \<in> funas_term si"
        from i Ui fsi have "(f,n) \<in> funas_term (rhs_n \<rho> i)" unfolding rho by simp
        from aux[OF *(1), of i] this i have "(f,n) \<in> funas_trs UR" unfolding rho by auto
      } note li = this
      { assume fti:"(f,n) \<in> funas_term ti"
        from i Ui fti have "(f,n) \<in> funas_term (lhs_n \<rho> (Suc i))" unfolding rho by simp
        from aux[OF *(1), of "Suc i"] this i have "(f,n) \<in> funas_trs UR" unfolding rho by auto
      } note ri = this
      from li ri lr have "(f,n) \<in> funas_trs UR" unfolding funas_rule_def by fastforce
    } 
    with *(2) A B funas_rule_def have "(f,n) \<in> funas_trs UR" unfolding rho by fastforce
  } note A = this
  let ?Us = "{(Uk, Suc (length (Z \<rho> k))) |\<rho> k Uk. \<rho> \<in> R \<and> k < length (snd \<rho>) \<and> U_fun \<rho> k Uk}"
  { fix f n
    assume "(f,n) \<in> ?Us"
    then obtain \<rho> k where *:"\<rho> \<in> R" "k < length (snd \<rho>)" "U_fun \<rho> k f" "n =  Suc (length (Z \<rho> k))" by auto
    obtain l r cs where rho:"\<rho> = ((l,r), cs)" by (cases \<rho>, auto)
    from * have "(f,n) \<in> funas_term (rhs_n \<rho> k)" unfolding rho by simp
    with aux[OF *(1), of k] *(2) have "(f,n) \<in> funas_trs UR" by auto
  } note B = this 
  from A Un_least B  show "funas_ctrs R \<union> ?Us \<subseteq> funas_trs UR" by fast
qed

lemma funs_UR:"funs_trs UR = funs_ctrs R \<union> {Uk |\<rho> k Uk. \<rho> \<in> R \<and> k < length (snd \<rho>) \<and> U_fun \<rho> k Uk}"
  unfolding funs_trs_funas_trs funas_UR funs_ctrs_funas_ctrs 
  by auto force

(* some properties of X, Y, Z variables *)
lemma X_vars_Suc :
  assumes inR:"\<rho> \<in> R" and il:"Suc i < length (snd \<rho>)" 
  shows "(X_vars \<rho> (Suc i)) = (X_vars \<rho> i) \<union> vars_term (snd (snd \<rho> ! i))"
proof-
  let ?v = "\<lambda> m. \<Union>(vars_term ` rhss (set (take m (snd \<rho>))))"
  from il have il':"i < length (snd \<rho>)" by auto 
  from il take_Suc_conv_app_nth[OF il'] have "set (take (Suc i) (snd \<rho>)) = set (take i (snd \<rho>)) \<union> {snd \<rho> ! i}" by force
  then show ?thesis unfolding X_vars_def by force
qed

lemma X_vars_mono :
  assumes inR:"\<rho> \<in> R" and il:"i < length (snd \<rho>)" and ji:"j \<le> i"
  shows "X_vars \<rho> j \<subseteq> X_vars \<rho> i"
proof(cases "j = i", simp)
  case False
  with ji have ji:"j < i" by auto
  let ?v = "\<lambda> m. \<Union>(vars_term ` rhss (set (take m (snd \<rho>))))"
  from il inR have si:"X_vars \<rho> i = (vars_term (clhs \<rho>) \<union> ?v i)"  unfolding X_vars_def by auto
  from xt1(10)[OF il ji] inR have sj:"X_vars \<rho> j = vars_term (clhs \<rho>) \<union> ?v j" unfolding X_vars_def by blast
  have "?v j \<subseteq> ?v i" by (rule Union_mono, rule image_mono, rule image_mono, 
        simp add:set_take_subset_set_take[OF less_imp_le[OF ji]]) 
  from Un_mono[OF subset_refl this] show ?thesis unfolding si sj by auto
qed

lemma l_vars_X_vars :
  assumes inR:"\<rho> \<in> R" and il:"i < length (snd \<rho>)" shows "vars_term (clhs \<rho>) \<subseteq> X_vars \<rho> i" 
  unfolding X_vars_def using X_vars_def il inR by blast

lemma l_vars_X0_vars :
  assumes inR:"\<rho> \<in> R" and il:"0 < length (snd \<rho>)" shows "vars_term (clhs \<rho>) = X_vars \<rho> 0" 
  unfolding X_vars_def using assms by simp


lemma Y_vars_mono: assumes i: "i < length (snd \<rho>)" and j: "j \<le> i"
  shows "Y_vars \<rho> j \<supseteq> Y_vars \<rho> i"
proof -
  from j have ij: "\<And> k. i < k \<Longrightarrow> j < k" "\<And>k. i \<le> k \<Longrightarrow> j \<le> k" by auto
  have cong: "\<And> a b c b' c'. b \<subseteq> b' \<Longrightarrow> c \<subseteq> c' \<Longrightarrow> a \<union> b \<union> c \<subseteq> a \<union> b' \<union> c'" by blast
  show ?thesis using i j 
  proof (unfold Y_vars_alt, subst Y_vars_alt, force, intro cong, insert ij)
    show "\<Union>{vars_term (si \<rho> j) |j. i < j \<and> j < length (snd \<rho>)}
    \<subseteq> \<Union>{vars_term (si \<rho> ja) |ja. j < ja \<and> ja < length (snd \<rho>)}" using ij by auto
    show "\<Union>{vars_term (ti \<rho> j) |j. i \<le> j \<and> j < length (snd \<rho>)}
    \<subseteq> \<Union>{vars_term (ti \<rho> ja) |ja. j \<le> ja \<and> ja < length (snd \<rho>)}" using ij by auto
  qed
qed    

lemma X_Y_imp_Z :
  assumes inR:"\<rho> \<in> R" and il:"i < length (snd \<rho>)" and x:"x \<in> X_vars \<rho> i" and y:"x \<in> Y_vars \<rho> i"
  shows "x \<in> set (Z \<rho> i)"
  using  Z[unfolded Z_vars_def, rule_format, OF inR il] x y by blast


lemma s_imp_Y :
  assumes inR:"\<rho> \<in> R" and il:"Suc i < length (snd \<rho>)" and x:"x \<in> vars_term (fst (snd \<rho> ! (Suc i)))"
  shows "x \<in> Y_vars \<rho> i" using assms
  by (subst Y_vars_alt, auto)

(* Theorem 3.9(1), => in NSS12 *)
lemma L3_9a :
  assumes inR:"\<rho> \<in> R" and ull:"ultra_rule left_linear_trs \<rho>"
  shows "linear_term (clhs \<rho>) \<and> (\<forall> i < length (snd \<rho>). linear_term ( snd(snd \<rho> ! i))) \<and>
      (\<forall> i < length (snd \<rho>). vars_term (snd ((snd \<rho>) ! i)) \<inter> X_vars \<rho> i = {})"
proof-
  obtain l r cs where rho:"\<rho> = ((l,r),cs)" by (cases \<rho>, auto)
  with ull have ll:"\<And> l' r'. (l',r') \<in> rules \<rho> \<Longrightarrow> linear_term l'" unfolding left_linear_trs_def by blast
  then have "linear_term (lhs_n \<rho> 0)"  unfolding rules_def by fast
  then have 1:"linear_term (clhs \<rho>)" unfolding rules_def using lhs_n.simps(1) prod.collapse by metis
  { fix i
    assume i:"i < length (snd \<rho>)"
    then have i':"Suc i \<le> length (snd \<rho>)" by auto
    let ?ti = "snd (snd \<rho> ! i)"
    from  ll[unfolded rules_def] i' have lin:"linear_term (lhs_n \<rho> (Suc i))" by blast
    from U_cond[OF inR i] obtain f where "U \<rho> i = More f [] \<box> (map Var (Z \<rho> i))" by fast
    from lin[unfolded rho lhs_n.simps(2) this[unfolded rho] intp_actxt.simps] rho have 
      "linear_term (Fun f ((snd (cs!i)) # (map Var (Z \<rho> i))))" by auto
    from this[unfolded linear_term.simps(2)] have 2:"linear_term ?ti" unfolding rho by force
    have "vars_term (snd ((snd \<rho>)!i)) \<inter> X_vars \<rho> i = {}"
    proof(rule ccontr)
      assume ne:"vars_term (snd (snd \<rho> ! i)) \<inter> X_vars \<rho> i \<noteq> {}"
      let ?ti = "(snd (snd \<rho> ! i))"
      let ?zs = "Z \<rho> i"
      have "vars_term ?ti \<subseteq> Y_vars \<rho> i" unfolding Y_vars_def using inR i by force
      with Z[unfolded Z_vars_def] ne have iz:"vars_term ?ti \<inter> set (Z \<rho> i) \<noteq> {}" using inR i by fast
      have zs:"\<Union> (set (map vars_term (map Var ?zs))) = set ?zs" unfolding map_map vars_term_Var_id by force
      from iz have p:"\<not> (is_partition (map vars_term (?ti # (map Var ?zs))))" 
        unfolding list.simps(9) is_partition_Cons zs by blast
      let ?t = "(U \<rho> i)\<langle>snd (snd \<rho> ! i)\<rangle>"
      from U_cond[OF inR i] obtain f where Uri:"U \<rho> i = More f [] \<box> (map Var (Z \<rho> i))" by fast
      from p have "\<not> linear_term ?t" unfolding Uri by simp
      then have l:"\<not> linear_term (lhs_n \<rho> (Suc i))" unfolding rho by auto
      have "linear_term (lhs_n \<rho> (Suc i))" by(rule ll[unfolded rules_def], insert i, auto)
      with l show False by auto
    qed 
    with 2 have "linear_term ?ti \<and> vars_term (snd ((snd \<rho>)!i)) \<inter> X_vars \<rho> i = {}" by auto
  }
  with 1 show ?thesis by auto
qed





lemma part_rev : assumes p:"is_partition xs" shows "is_partition (rev xs)"
  unfolding is_partition_def length_rev 
proof(rule,rule)
  fix j
  assume j:"j < length xs"
  show "\<forall>i<j. rev xs ! i \<inter> rev xs ! j = {}" proof(rule,rule)
    fix i
    assume i:"i < j"
    from j have 1:"length xs  - (Suc i) < length xs" by fastforce
    from i j have 2:"length xs  - (Suc j) < length xs  - (Suc i)"
      by (metis Suc_less_eq diff_less_mono2 less_trans_Suc)
    from p[unfolded is_partition_def] 1 2 
    show "rev xs ! i \<inter> rev xs ! j  = {}" unfolding rev_nth[OF j] rev_nth[OF order.strict_trans[OF i j]] by blast
  qed
qed

lemma is_partition_rev : "is_partition (rev xs) = is_partition xs "
  using part_rev rev_rev_ident by force

(* replace by all_ctxt_closed_subst_step? *)
lemma substs_rsteps':
  shows "(\<And>x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*) \<Longrightarrow> (t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (cstep R)\<^sup>*"
proof (induct t)
  case (Var y) 
  then show ?case by simp
next
  case (Fun f ts)
  have "\<And> s. s \<in> set ts \<Longrightarrow>  vars_term s \<subseteq> vars_term (Fun f ts)" by auto
  with Fun have "\<And> s. s \<in> set ts \<Longrightarrow> (s \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (cstep R)\<^sup>*" by blast
  then have "\<forall>i<length (map (\<lambda>t. t \<cdot> \<sigma>) ts).
    (map (\<lambda>t. t \<cdot> \<sigma> ) ts ! i, map (\<lambda>t. t \<cdot> \<tau>) ts ! i) \<in> (cstep R)\<^sup>*" by auto
  from args_steps_imp_steps[OF cstep_ctxt_closed _ this] show ?case by simp
qed

(* Lemma A.1 in NSS12 *)
(* partition of variable sets in substitution \<sigma> (different from paper *)
definition X_part :: "('f,'v) crule \<Rightarrow> 'v set list" where
  "X_part \<rho> \<equiv> ((X_vars \<rho> 0) # (map (\<lambda>i. X_vars \<rho> (Suc i) -  (X_vars \<rho> i)) [0..< (length (snd \<rho>) - 1)]) @
             [(vars_term (crhs \<rho>) \<union> (vars_term (ti \<rho> (length (snd \<rho>) - 1)))) - (X_vars \<rho> (length (snd \<rho>) - 1))])"


lemma X_part: assumes inR:"\<rho> \<in> R" 
  and l:"length (snd \<rho>) \<noteq> 0 "
shows "is_partition (X_part \<rho>)"
proof-
  let ?k = "length (snd \<rho>)"
  from not0_implies_Suc[OF l] obtain k' where k_suc:"?k = Suc k'" by auto
  let ?xk = "(vars_term (crhs \<rho>) \<union> (vars_term (ti \<rho> k'))) -  (X_vars \<rho> k')"
  let ?xs = "\<lambda> m. (X_vars \<rho> 0) # (map (\<lambda>i. X_vars \<rho> (Suc i) -  (X_vars \<rho> i)) [0..<m])"
  fix j
  have key:"\<forall>j. j < ?k \<longrightarrow> (is_partition (rev (?xs j)) \<and> \<Union>(set (?xs j)) \<subseteq> X_vars \<rho> j)" 
  proof(rule allI, rule)
    fix j 
    assume "j < ?k"
    then show "is_partition (rev (?xs j))  \<and> \<Union>(set (?xs j)) \<subseteq> X_vars \<rho> j" proof(induct j)
      case 0 
      have s:"?xs 0 = [X_vars \<rho> 0]" by auto
      then show ?case unfolding s using rev.simps is_partition_Cons is_partition_Nil by force
    next
      case (Suc j)
      assume lt:"Suc j < ?k"
      with Suc have p:"is_partition (rev (?xs j))" and ss:"\<Union>(set (?xs j)) \<subseteq> X_vars \<rho> j" by auto
      let ?xi = "\<lambda> j. X_vars \<rho> (Suc j) -  (X_vars \<rho> j)"
      have "?xs (Suc j) = (?xs j) @ [?xi j]" unfolding upt_Suc_append[OF le0] map_append by fastforce
      then have r:"rev (?xs (Suc j)) =  (?xi j) #  (rev (?xs j))" using rev_eq_Cons_iff[of "?xs (Suc j)"] by auto
      have "(?xi j) \<inter> X_vars \<rho> j = {}" by auto
      with ss have "(?xi j) \<inter> \<Union>(set (rev (?xs j))) = {}" by auto
      with Suc r have p:"is_partition (rev (?xs (Suc j)))" using is_partition_Cons[of "?xi j" "rev (?xs j)"] by fastforce
      from ss X_vars_mono[OF inR lt less_imp_le[OF lessI]] 
      have "\<Union>(set (?xs (Suc j))) \<subseteq> X_vars \<rho> (Suc j)" 
        unfolding  upt_Suc_append[OF le0] map_append list.set(2) set_append by auto
      with p show ?case by auto
    qed
  qed
  have lt:"k' < ?k" using k_suc by auto
  from key this have p:"is_partition (rev (?xs k'))" "\<Union>(set (?xs k')) \<subseteq> X_vars \<rho> k'" unfolding X_part_def by auto
  from p(2) have isc:"?xk \<inter> \<Union>(set (rev (?xs k'))) = {}" by auto
  from k_suc have kk:"?k - 1 = k'" by auto
  have aux:"rev (?xs k' @ [?xk]) = ?xk # rev (?xs k')"  using rev_eq_Cons_iff by fastforce
  with p isc have "is_partition (rev (?xs k' @ [?xk]))" unfolding aux is_partition_Cons by blast
  then show ?thesis using is_partition_rev unfolding X_part_def kk by force
qed


lemma Z_part: assumes inR:"\<rho> \<in> R" 
  and i:"i < length (snd \<rho>)"
shows "is_partition (map (\<lambda> z. {z}) (Z \<rho> i))"
proof-
  from Z[unfolded Z_vars_def] inR i have "distinct (Z \<rho> i)" by fast
  with distinct_conv_nth show ?thesis unfolding is_partition_def by force
qed

lemma ll_aux:
  assumes "\<rho> \<in> R"
    and "left_linear_trs UR"
  shows "left_linear_trs (rules \<rho>)" 
  using assms unfolding left_linear_trs_def UR_def by blast

lemma Z_ti_disjoint: 
  assumes inR:"\<rho> \<in> R" 
    and i:"i < length (snd \<rho>)"
    and ll:"left_linear_trs UR"
  shows "vars_term (ti \<rho> i) \<inter> set (Z \<rho> i) = {}"
proof-
  from i not0_implies_Suc obtain k where l:"length (snd \<rho>) = Suc k" by (metis less_nat_zero_code)
  from L3_9a[OF inR ll_aux[OF inR ll]] i have "vars_term (ti \<rho> i) \<inter> (X_vars \<rho> i) = {}" by auto
  obtain l r cs where rho:"\<rho> = ((l,r),cs)" by (cases \<rho>, auto)
  from U_cond[OF inR i] obtain Ui where Ui:"U_fun \<rho> i Ui" by auto
  from ll_aux[OF inR ll, unfolded rules_def left_linear_trs_def] i have "linear_term (lhs_n \<rho> (Suc i))" by auto
  from this[unfolded rho lhs_n.simps Ui[unfolded rho], simplified, unfolded is_partition_Cons]  
  have "vars_term (ti \<rho> i) \<inter> set (Z \<rho> i) = {}" unfolding rho by force
  with Z[unfolded Z_vars_def] inR i show "vars_term (ti \<rho> i) \<inter> set (Z \<rho> i) = {}" by auto
qed

lemma Z_part': assumes inR:"\<rho> \<in> R" 
  and i:"i < length (snd \<rho>)"
  and ll:"left_linear_trs UR"
shows "is_partition (vars_term (ti \<rho> i) # map (\<lambda> z. {z}) (Z \<rho> i))"
proof-
  from Z_part[OF inR i] have p:"is_partition (map (\<lambda> z. {z}) (Z \<rho> i))" by auto
  with Z_ti_disjoint[OF inR i ll] is_partition_Cons show ?thesis by fastforce
qed

lemma X_part_nth :
  assumes inR:"\<rho> \<in> R" 
    and l:"length (snd \<rho>) \<noteq> 0 "
    and jk:"Suc j < length (snd \<rho>)"
  shows " (X_part \<rho>) ! (Suc j) =  (X_vars \<rho> (Suc j)) - (X_vars \<rho> j)"
proof-
  let ?k = "length (snd \<rho>)"
  let ?f = "\<lambda>i. (X_vars \<rho> (Suc i)) - (X_vars \<rho> i)"
  from jk have x:"j < ?k - 1 - 0" by auto
  then have "map ?f [0..<?k - 1] ! j = (X_vars \<rho> (Suc j)) - (X_vars \<rho> j)" 
    unfolding nth_map[of j "[0..<?k - 1]", unfolded length_upt, OF x]  using nth_upt by force
  with nth_map[of j "[0..<?k - 1]", unfolded length_upt, OF x] show ?thesis unfolding X_part_def nth_Cons_Suc 
      nth_append[of "map ?f [0..<?k - 1]" _ j, unfolded length_map length_upt eqTrueI[OF x] if_True] by blast
qed

lemma X_part_last :
  assumes inR:"\<rho> \<in> R" 
    and l:"length (snd \<rho>) \<noteq> 0 "
  shows " (X_part \<rho>) ! (length (snd \<rho>)) = 
  (vars_term (crhs \<rho>) \<union> (vars_term (ti \<rho> (length (snd \<rho>) - 1)))) - (X_vars \<rho> (length (snd \<rho>) - 1))"
proof-
  let ?k = "length (snd \<rho>)" 
  let ?f = "\<lambda>i. (X_vars \<rho> (Suc i)) - (X_vars \<rho> i)"
  from l have kl:"?k = length ((X_vars \<rho> 0) # map ?f [0..<?k - 1])" unfolding length_Cons length_map length_upt by simp
  with nth_append_length show ?thesis unfolding X_part_def append_Cons[symmetric] by (metis (no_types, lifting))
qed

lemma vars_cs_vars_ti:
  assumes inR: "\<rho> \<in> R"
    and x:"x \<in> vars_trs (set (snd \<rho>))"
  shows "x \<in> vars_term (clhs \<rho>) \<or> (\<exists> j. j< (length (snd \<rho>)) \<and> x \<in> vars_term (ti \<rho> j))" 
proof-
  let ?k = "length (snd \<rho>)"
  from x[unfolded vars_trs_def set_conv_nth] have "\<exists> j. j< ?k \<and> (x \<in> vars_rule ((snd \<rho>) ! j))" by auto
  with vars_rule_def obtain j where j:"j< ?k""(x \<in> vars_term (ti \<rho> j) \<or> x \<in> vars_term (si \<rho> j))" by fast
  { assume "x \<in> vars_term (si \<rho> j)" 
    with dctrs[unfolded dctrs_def, rule_format, OF inR j(1)] X_vars_alt[OF  less_imp_le_nat[OF j(1)]] have 
      "x \<in> vars_term (clhs \<rho>) \<or> x \<in> \<Union>((\<lambda>j. vars_term (ti \<rho> j)) ` {ja. ja < j})" by blast
    with j(1) have ?thesis by force
  } 
  with j show ?thesis by blast
qed

abbreviation "XY \<rho> m \<equiv> (X_vars \<rho> m) \<inter> (Y_vars \<rho> m)"

lemma XYi_subset_ti_XY:
  assumes inR:"\<rho> \<in> R" and m:"Suc m < length (snd \<rho>)"
  shows "XY \<rho> (Suc m) \<subseteq> vars_term (ti \<rho> m) \<union> XY \<rho> m"
proof-
  {fix x
    assume x:"x \<in> XY \<rho> (Suc m)"
    with X_vars_Suc[OF inR m] have x':"x \<in> X_vars \<rho> m \<union> vars_term (ti \<rho> m)" by auto
    from x Y_vars_mono[OF m, of m] have y:"x \<in> Y_vars \<rho> m" by auto
    with x' y have "x \<in> vars_term (ti \<rho> m) \<union> XY \<rho> m" by auto
  }
  then show ?thesis by blast
qed

lemma vars_si_subset_ti_XY:
  assumes inR:"\<rho> \<in> R" and m:"Suc m < length (snd \<rho>)"
  shows "vars_term (si \<rho> (Suc m)) \<subseteq> vars_term (ti \<rho> m) \<union> XY \<rho> m"
proof-
  {fix x
    assume x:"x \<in> vars_term (si \<rho> (Suc m))"
    from m length_drop have "length (drop m (snd \<rho>)) > 1" by fastforce
    with x m have y:"x \<in> Y_vars \<rho> m"
      by (subst Y_vars_alt, auto)
    have " x \<in> vars_term (ti \<rho> m) \<union> XY \<rho> m" proof(cases "x \<in> vars_term (ti \<rho> m)", simp)
      assume x':"x \<notin> vars_term (ti \<rho> m)" 
      from dctrs[unfolded dctrs_def, rule_format, OF inR m] x X_vars_alt[OF less_imp_le_nat[OF m]]
      have xin:"x \<in> vars_term (clhs \<rho>) \<union> \<Union>((\<lambda>j. vars_term (ti \<rho> j)) ` {j. j < Suc m})" by blast
      have " {j. j < Suc m} = {j. j < m} \<union> {m}" by fastforce
      then have "\<Union>((\<lambda>j. vars_term (ti \<rho> j)) ` {j. j < Suc m}) = (\<Union>((\<lambda>j. vars_term (ti \<rho> j)) ` ({j. j < m} \<union> {m} ))) \<union> vars_term (ti \<rho> m)" by force
      then have "\<Union>((\<lambda>j. vars_term (ti \<rho> j)) ` {j. j < Suc m}) = (\<Union>((\<lambda>j. vars_term (ti \<rho> j)) ` {j. j < m})) \<union> vars_term (ti \<rho> m)" by auto
      with x' xin have xin:"x \<in> vars_term (clhs \<rho>) \<union> \<Union>((\<lambda>j. vars_term (ti \<rho> j)) ` {j. j < m})" by auto
      from m have len:"length (take m (snd \<rho>)) = m" by auto
      with nth_take[of _ m "snd \<rho>"] have "take m (snd \<rho>) = map (\<lambda>j. (snd \<rho> ! j)) [0..< m]"
        by (metis (poly_guards_query) Suc_lessD m take_upt_idx)
      with nth_take[of _ m "snd \<rho>"] len have "set (take m (snd \<rho>)) = (\<lambda>j. (snd \<rho> ! j)) ` {j. j < m}" by auto
      then have aux:"rhss (set (take m (snd \<rho>))) = (\<lambda>j. (ti \<rho> j)) ` {j. j < m}" by force
      from m xin aux have "x \<in> X_vars \<rho> m" unfolding X_vars_def by force
      with y  show ?thesis  by auto
    qed}
  then show ?thesis by blast
qed


abbreviation si :: "('f,'v) crule \<Rightarrow> nat =>  ('f,'v) term" where "si \<rho> i \<equiv> fst ((snd \<rho>)!i)"
abbreviation ti :: "('f,'v) crule \<Rightarrow> nat =>  ('f,'v) term" where "ti \<rho> i \<equiv> snd ((snd \<rho>)!i)"

lemma vars_r_subset_tk_Z:
  assumes inR:"((l,r),cs) \<in> R" (is "?\<rho> \<in> R")
    and lcs:"length cs > 0"
  shows  "vars_term r \<subseteq> XY ?\<rho> (length cs - 1) \<union> vars_term (ti ?\<rho> (length cs - 1))"
proof
  fix x
  assume xr:"x \<in> vars_term r"
  let ?k = "length cs - 1"
  let ?X = "\<lambda>k. \<Union>((\<lambda>j. vars_term (ti ?\<rho> j)) ` {j. j < k})"
  let ?Xk = "?X (length cs)" let ?Xk' = "?X ?k"
  from xr type3[unfolded type3_def, rule_format, OF inR] vars_cs_vars_ti[OF inR] have xx':"x \<in> vars_term l \<union> ?Xk" by auto
  from lcs have " {j. j < length cs} = {j. j < ?k} \<union> {?k}" by fastforce
  then have "?Xk = ?Xk' \<union> vars_term (ti ?\<rho> ?k)" by force
  from xx' this have xx':"x \<in> vars_term l \<union> ?Xk' \<union> vars_term (ti ?\<rho> ?k)" by auto
  have len:"length (take ?k (snd ?\<rho>)) = ?k" by auto
  with nth_take[of _ ?k "snd ?\<rho>"] have "take ?k (snd ?\<rho>) = map (\<lambda>j. (snd ?\<rho> ! j)) [0..< ?k]"
    by (metis diff_less lcs snd_conv take_upt_idx zero_less_one)
  then have aux:"rhss (set (take ?k (snd ?\<rho>))) = ((\<lambda>j. (ti ?\<rho> j)) ` {0..< ?k})" by auto
  from xx' have xx:"x \<in> X_vars ?\<rho> ?k \<union> vars_term (ti ?\<rho> ?k)" unfolding aux X_vars_def by force
  from lcs xr this have y:"x \<in> Y_vars ?\<rho> ?k" unfolding Y_vars_def by auto
  from xx y lcs show "x \<in> XY ?\<rho> ?k \<union> vars_term (ti ?\<rho> ?k)" by auto
qed

(* Lemma A.1 in NSS12 *)
lemma Lemma_17:
  assumes inR: "\<rho> \<in> R" 
    and ll: "left_linear_trs UR"
    and l: "length (snd \<rho>) \<noteq> 0 "
    and sl: "length (\<sigma> :: ('f, 'v) subst list) = Suc (length (snd \<rho>))"
    and st: "\<forall> i < length (snd \<rho>). (si \<rho> i \<cdot> (\<sigma> ! i), ti \<rho> i \<cdot> (\<sigma> ! Suc i) ) \<in> (cstep R)\<^sup>*"
    and zrew: "\<forall> i < length (snd \<rho>). \<forall> z \<in> set (Z \<rho> i). (Var z \<cdot> (\<sigma> ! i), Var z \<cdot> (\<sigma> ! Suc i)) \<in> (cstep R)\<^sup>*"
  shows "(clhs \<rho> \<cdot> (\<sigma> ! 0), crhs \<rho> \<cdot> (\<sigma>!(length (snd \<rho>)))) \<in> (cstep R)\<^sup>+"
proof-
  let ?k = "length (snd \<rho>)"
  let ?xs = "X_part \<rho>"
  let ?\<sigma> = "fun_merge \<sigma> ?xs"
  from not0_implies_Suc l obtain k' where k_suc:"?k = Suc k'" by auto
  have lx:"Suc ?k = length ?xs" unfolding X_part_def using k_suc by fastforce
  from X_part[OF inR l] have p:"is_partition ?xs" by fast
  { fix t :: "('f,'v) term" fix i
    assume x:"i < Suc ?k" and y:"vars_term t \<subseteq> ?xs!i"
    from y fun_merge_part[OF p] x[unfolded lx] have "\<And> x. x \<in> (vars_term t) \<Longrightarrow> ?\<sigma> x = (\<sigma>!i) x" by blast
    from term_subst_eq this have "t \<cdot> ?\<sigma> = t \<cdot> (\<sigma>!i)" by blast
  }
  note subst_fact = this
  let ?l = "clhs \<rho>" let ?r = "crhs \<rho>" let ?cs = "snd \<rho>"
  from inR have rho:"((?l,?r),?cs) \<in> R " by auto
  have "vars_term ?l \<subseteq> ?xs ! 0" using l_vars_X_vars[OF inR, OF l[unfolded neq0_conv]] unfolding X_part_def by auto
  from subst_fact[OF _ this] lx have lsigma:"?l \<cdot> ?\<sigma> = ?l \<cdot> (\<sigma>!0)" by fast
      (* next, show t_i \<sigma>_{i+1} = t_i \<sigma> *)
  note ull = ll_aux[OF inR ll]
  { fix i
    assume ik:"i < ?k" 
    from conjunct2[OF conjunct2[OF L3_9a[OF inR ull]], rule_format,OF ik] have ss':"vars_term (ti \<rho> i) \<inter> X_vars \<rho> i = {}" by auto
    have "vars_term (ti \<rho> i) \<subseteq> ?xs!Suc i"
    proof(cases "Suc i < ?k")
      case True
      from ik min_less_iff_conj nth_mem[of i "take (Suc i)(snd \<rho>)", unfolded length_take nth_take[OF lessI]] 
      have "ti \<rho> i \<in> rhss (set (take (Suc i)(snd \<rho>)))" by blast
      with subsetI image_eqI[OF refl] have "vars_term (ti \<rho> i) \<subseteq> \<Union>(vars_term ` rhss (set (take (Suc i) (snd \<rho>))))" by blast
      then have ss:"vars_term (ti \<rho> i) \<subseteq> X_vars \<rho> (Suc i)" unfolding X_vars_def by auto
      from X_part_nth[OF inR _ True] k_suc have "?xs ! Suc i = X_vars \<rho> (Suc i) - X_vars \<rho> i" by auto
      with ss ss' show "vars_term (ti \<rho> i) \<subseteq> ?xs ! Suc i" by blast
    next
      case False
      with ik have i:"i = ?k - 1" and ii: "Suc i = ?k" by auto
      have xk: "?xs ! (Suc i) = vars_term (crhs \<rho>) \<union> vars_term (ti \<rho> i) - X_vars \<rho> i" 
        unfolding X_part_def i k_suc
        using nth_append_length[of "(X_vars \<rho> 0) # map (\<lambda>i. X_vars \<rho> (Suc i) - X_vars \<rho> i) [0..<Suc k' - 1]", unfolded length_Cons length_map length_upt]
        unfolding length_Cons length_map length_upt by force
      with ss' show "vars_term (ti \<rho> i) \<subseteq> ?xs!Suc i" unfolding ii by blast
    qed
    from subst_fact[OF _ this] ik have "(ti \<rho> i) \<cdot> (\<sigma>! (Suc i)) = (ti \<rho> i) \<cdot> ?\<sigma>" by fastforce
  }
  note t_fact = this 
    (* attempt of more general auxiliary result for s_i and r case *)
  { fix j x
    assume y:"x \<in> Y_vars \<rho> j" 
      and lhs_or_ti:"x \<in> vars_term ?l \<or> (\<exists> k < Suc j. x \<in> vars_term (ti \<rho> k))"
      and ik:"Suc j \<le> ?k"
    from y Y_vars_mono Suc_le_lessD[OF ik] have y:"\<And> j'. j' \<le> j \<Longrightarrow> x \<in> Y_vars \<rho> j'" by blast
    have "(?\<sigma> x, (\<sigma>! (Suc j)) x) \<in> (cstep R)\<^sup>*" 
    proof(cases "x \<in> vars_term ?l")
      case True
      with l_vars_X_vars[OF inR] k_suc have "x \<in> ?xs!0"  unfolding X_part_def nth_Cons_0 by auto
      from fun_merge_part[OF p _ this, unfolded lx[symmetric] k_suc] have  sx0:"?\<sigma> x = (\<sigma>!0) x" by auto
      from l_vars_X_vars[OF inR] True k_suc X_vars_mono[OF inR _ le0] 
        order.strict_trans2[OF _ ik] have x:"\<And> j'. j' < Suc j \<Longrightarrow> x \<in> X_vars \<rho> j'" by blast
      from x y X_Y_imp_Z[OF inR] ik k_suc have z:"\<And> j'. j' < Suc j \<Longrightarrow> x \<in> set (Z \<rho> j')" by simp
      then have xZ0:"x \<in> set (Z \<rho> 0)" by auto
      from z ik have "((\<sigma> ! 0) x,  (\<sigma> ! (Suc j)) x) \<in> (cstep R)\<^sup>*" proof (induct j)
        case 0 from zrew[rule_format, of 0] k_suc xZ0 show ?case by simp
      next
        case (Suc k) 
        then have 1:"Suc k < ?k" and 2:"\<And> j. j < Suc k \<Longrightarrow> x \<in> set (Z \<rho> j)" by auto
        from zrew[rule_format, OF 1 Suc(2)] Suc(1) 2 1 show ?case by fastforce
      qed
      with sx0 show ?thesis by auto
    next 
      case False
      with lhs_or_ti obtain j' where ji:"j' < Suc j" and xj:"x \<in> vars_term (ti \<rho> j')" by auto
      from ji ik have 1:"Suc j' \<le> ?k" by auto
      from  L3_9a[OF inR ull] order.strict_trans2[OF ji ik] have x:"vars_term (ti \<rho> j') \<inter> X_vars \<rho> j' = {}" by fast
      from nth_take[OF lessI] nth_mem[of j' "take (Suc j') (snd \<rho>)", unfolded nth_take[OF lessI] length_take min_less_iff_conj]  
        order.strict_trans2[OF ji ik] image_iff[of "ti \<rho> j'" snd] lessI[of j']
      have "ti \<rho> j' \<in>  rhss (set (take (Suc j') ?cs))" by blast
      with xj image_iff have xu:"x \<in> \<Union>(vars_term ` rhss (set (take (Suc j') ?cs)))" unfolding Union_iff by blast
      from xu inR False have xsj: "Suc j' < ?k \<Longrightarrow> x \<in> X_vars \<rho> (Suc j')" unfolding X_vars_def by blast
      have "x \<in> ?xs!(Suc j')"
      proof(cases "Suc j' < ?k")
        case True
        from xsj[OF True] x xj X_part_nth[OF inR _ True] k_suc show ?thesis by auto
      next
        case False
        with 1 have sk:"?k = Suc j'" by auto
        with xj x show "x \<in> ?xs!(Suc j')" unfolding X_part_last[OF inR nat.discI[OF sk], unfolded sk] by auto
      qed
      from fun_merge_part[OF p _ this] lx 1 have sxSucj:"?\<sigma> x = (\<sigma>!Suc j') x" by auto
      { fix j''
        assume 1:"Suc j' \<le> j''" and 2:"j'' < Suc j"
        with ik have ltk:"Suc j' < ?k" by force
        have "x \<in> X_vars \<rho> j''" proof(cases "Suc j' = j''", insert xsj[OF ltk],simp)
          case False with 1 have "Suc j' < j''" by auto
          from xsj[OF ltk]  X_vars_mono[OF inR _ 1] 2 ik show "x \<in> X_vars \<rho> j''" by auto
        qed 
        from X_Y_imp_Z[OF inR _ this y[OF 2[unfolded less_Suc_eq_le]]] 2 ik have "x \<in> set (Z \<rho> j'')" by auto
      } note z = this
      have "((\<sigma> ! Suc j') x,  (\<sigma> ! (Suc j)) x) \<in> (cstep R)\<^sup>*"
      proof(cases "Suc j' = Suc j", insert ji, simp)
        case False 
        with ji have "Suc j' < Suc j" by auto
        with z ik show ?thesis proof (induct j,simp)
          case (Suc k) 
          from Suc have z:"\<And> j''. Suc j' \<le> j'' \<and> j'' < Suc k \<Longrightarrow> x \<in> set (Z \<rho> j'')" by auto
          show ?case proof(cases "Suc j'= Suc k")
            case False
            with Suc(4) Suc(3) have 0:"j' < Suc k" and 1:"Suc k < ?k" and 2:"Suc j' < Suc k" by auto
            from z Suc(1)[OF _ less_imp_le_nat[OF 1] 2] have "((\<sigma> ! Suc j') x, (\<sigma> ! Suc k) x) \<in> (cstep R)\<^sup>*" by blast
            with zrew[rule_format, OF 1] Suc(2)[of "Suc k", OF Suc_leI[OF 0] lessI] show ?thesis by force
          next
            case True
            from Suc have 0:"Suc j' < ?k" by auto
            from True zrew[rule_format, OF 0 Suc(2)[OF order.refl Suc(4)]] show ?thesis by simp
          qed
        qed
      qed
      with sxSucj show ?thesis by auto
    qed
  } note auxiliary2 = this
    (* case for s_i *)
  { fix i x
    assume ik:"i < ?k" 
    { fix x
      assume xs:"x \<in> vars_term (si \<rho> i)"
      have " (?\<sigma> x, (\<sigma>!i) x) \<in> (cstep R)\<^sup>*" proof(cases i) 
        case 0
        from xs[unfolded 0] dctrs[unfolded dctrs_def, rule_format, OF inR ik[unfolded 0]] 
          X_vars_alt have  "x \<in> vars_term ?l" by fast
        with l_vars_X_vars[OF inR] k_suc have "x \<in> ?xs!0"  unfolding X_part_def nth_Cons_0 by auto
        from fun_merge_part[OF p _ this, unfolded lx[symmetric] k_suc] have  "?\<sigma> x = (\<sigma>!0) x" by auto
        with 0 show ?thesis by auto
      next
        case (Suc j)
        from s_imp_Y[OF inR ik[unfolded Suc] xs[unfolded Suc]] ik have y:"x \<in> Y_vars \<rho> j" by blast
        from rev_subsetD[OF xs dctrs[unfolded dctrs_def, rule_format, OF inR ik], unfolded X_vars_alt[OF less_imp_le_nat[OF ik]]]
          auxiliary2[OF y] Suc ik show ?thesis by fastforce
      qed
    } 
    with ik substs_rsteps' have "((si \<rho> i) \<cdot> ?\<sigma>, (si \<rho> i) \<cdot> (\<sigma>!i)) \<in> (cstep R)\<^sup>*" by blast
  } note ss = this
    (* case for r *)
  { fix i x
    assume xr:"x \<in> vars_term (crhs \<rho>)"
    note alts = rev_subsetD[OF xr type3[unfolded type3_def, rule_format, OF inR], unfolded Un_iff[of x]]
    let ?goal = "x \<in> vars_term ?l \<or> (\<exists> j. j< ?k \<and> x \<in> vars_term (ti \<rho> j))"
    from alts vars_cs_vars_ti[OF inR] xr have disj:?goal by blast
    from xr have y:" x \<in> Y_vars \<rho> k'" unfolding k_suc Y_vars_def by simp
    from auxiliary2[OF y] disj k_suc have "(?\<sigma> x, (\<sigma>!?k) x) \<in> (cstep R)\<^sup>*"  by auto
  } note xr = this
  from xr substs_rsteps' have "(?r \<cdot> ?\<sigma>, ?r \<cdot> (\<sigma>!?k)) \<in> (cstep R)\<^sup>*" by blast 
  then obtain m where rsigma:"(?r \<cdot> ?\<sigma>, ?r \<cdot> (\<sigma>!?k)) \<in> (cstep_n R m)\<^sup>*" using csteps_imp_csteps_n by blast
      (* combine to final result *) 
  from ss st[rule_format] t_fact have "\<forall> i < ?k.((si \<rho> i) \<cdot> ?\<sigma>,(ti \<rho> i) \<cdot> ?\<sigma>) \<in> (cstep R)\<^sup>*" 
    using rtrancl_trans[of _ _ "cstep R"] nat_less_le by metis 
  from all_cstep_imp_cstep_n[of "length (snd \<rho>)", OF this] obtain n where "\<forall> i < ?k. ((si \<rho> i) \<cdot> ?\<sigma>,(ti \<rho> i) \<cdot> ?\<sigma>) \<in> (cstep_n R n)\<^sup>*" by blast
  then have "\<forall>(si, ti) \<in> set (snd \<rho>). (si \<cdot> ?\<sigma>, ti \<cdot> ?\<sigma>) \<in> (cstep_n R n)\<^sup>*"
    by (auto) (metis fst_conv in_set_idx snd_conv)
  from cstep_n_SucI [OF rho, of _ _ "?l \<cdot> ?\<sigma>" Hole "rhs_n \<rho> ?k \<cdot> ?\<sigma>", unfolded intp_actxt.simps(1), OF this, unfolded lsigma] rsigma rhs_n.simps k_suc
  have "(?l \<cdot> (\<sigma> ! 0), rhs_n \<rho> ?k \<cdot> ?\<sigma>) \<in> (cstep_n R (Suc n))\<^sup>+" by (metis less_not_refl prod.collapse r_into_trancl') 
  from this[unfolded rhs_n.simps[of "fst \<rho>" "snd \<rho>", unfolded prod.collapse] k_suc] have  "(?l \<cdot> (\<sigma> ! 0), ?r \<cdot> ?\<sigma>) \<in> (cstep_n R (Suc n))\<^sup>+" by force
  from cstep_n_mono [THEN trancl_mono_set, THEN set_mp, OF _ this, of "max (Suc n) m"]
    and cstep_n_mono [THEN rtrancl_mono, THEN set_mp, OF _ rsigma, of "max (Suc n) m"]
  obtain n where q:"(clhs \<rho> \<cdot> \<sigma> ! 0, crhs \<rho> \<cdot> \<sigma> ! length (snd \<rho>)) \<in> (cstep_n R n)\<^sup>+"
    by (auto intro: trancl_rtrancl_trancl)
  from trancl_mono_set[of "cstep_n R n" "\<Union>n. cstep_n R n"] q show ?thesis unfolding cstep_def by blast
qed

definition non_LV :: bool where "non_LV \<equiv> \<forall> (l,r) \<in> UR. \<not> is_Var l"
definition non_RV :: bool where "non_RV \<equiv> \<forall> (l,r) \<in> UR. \<not> is_Var r"

definition sig_F :: "('f,'v) term \<Rightarrow> bool" where "sig_F t \<equiv> (funs_term t \<subseteq> F)"

abbreviation sig_F_subst :: "('f,'v) subst \<Rightarrow> 'v set \<Rightarrow> bool" where 
  "sig_F_subst \<theta> V \<equiv> (\<forall> x \<in> V. sig_F (\<theta> x))"

lemma ur_step_exhaust_nlv:
  assumes step:"(Fun f us,v) \<in> rstep_r_p_s UR (l,r) [] \<sigma>" and nlv:"non_LV"
  shows "(\<exists> \<rho> \<in> R. ((l, r) = (lhs_n \<rho> 0, rhs_n \<rho> 0) \<and> f \<in> funs_ctrs R) \<or> 
        (\<exists> n < length (snd \<rho>).((l, r) = (lhs_n \<rho> (Suc n), rhs_n \<rho> (Suc n)) \<and> U \<rho> n = More f [] \<box> (map Var (Z \<rho> n)) \<and> f \<notin> funs_ctrs R)))"
proof-
  from step[unfolded rstep_r_p_s_def] have ur:"(l,r) \<in> UR" by auto
  from this[unfolded UR_def] rules_def obtain n \<rho> where n:"\<rho> \<in> R" "(l,r) = (lhs_n \<rho> n, rhs_n \<rho> n)""n \<le> length (snd \<rho>)" by blast 
  obtain s t cs where rho:"\<rho> = ((s,t), cs)" by (cases \<rho>, auto)
  from nlv[unfolded non_LV_def, rule_format, OF ur, unfolded split] obtain g ls where l:"l = Fun g ls" by blast
  with step[unfolded rstep_r_p_s_def ctxt_of_pos_term.simps(1) Let_def] have gf:"g = f" by simp
  show ?thesis proof (cases n)
    case 0
    from n(2)[unfolded 0 rho lhs_n.simps(1)] have ls:"s=l" by simp 
    from n(1)[unfolded rho ls l[unfolded gf]] funs_crule_def have "f \<in> funs_ctrs R" unfolding funs_ctrs_def funs_rule_def by force
    with n 0 show ?thesis by fast 
  next
    case (Suc m) 
    with lhs_n.elims[OF conjunct1[OF n(2)[unfolded prod.simps], symmetric]] rho have l':"l = (U \<rho> m)\<langle>snd (cs ! m)\<rangle>" by blast
    from Suc n(3) have m:"m < length (snd \<rho>)" by fastforce
    from U_cond[OF n(1) this] obtain h where u:"U \<rho> m = More h [] \<box> (map Var (Z \<rho> m)) \<and> h \<notin> F" by auto
    with l[unfolded gf] l' have "h = f" by simp
    from n(1) n(2)[unfolded Suc] u[unfolded this] m F show ?thesis by auto
  qed
qed

lemma ur_step_exhaust:
  assumes step:"(w,v) \<in> rstep_r_p_s UR (l,r) [] \<sigma>" 
  shows "(\<exists> \<rho> \<in> R. ((l, r) = (lhs_n \<rho> 0, rhs_n \<rho> 0)) \<or> 
        (\<exists> f us. w = Fun f us \<and> (\<exists> n. n < length (snd \<rho>) \<and> ((l, r) = (lhs_n \<rho> (Suc n), rhs_n \<rho> (Suc n)) 
          \<and> U_fun \<rho> n f \<and> f \<notin> F))))"
proof-
  from step[unfolded rstep_r_p_s_def] have ur:"(l,r) \<in> UR" by auto
  from this[unfolded UR_def] rules_def obtain n \<rho> where n:"\<rho> \<in> R" "(l,r) = (lhs_n \<rho> n, rhs_n \<rho> n)""n \<le> length (snd \<rho>)" by blast 
  obtain s t cs where rho:"\<rho> = ((s,t), cs)" by (cases \<rho>, auto)
  show ?thesis proof (cases n)
    case 0
    from n(2)[unfolded 0 rho lhs_n.simps(1)] have ls:"s=l" by simp 
    with n 0 show ?thesis by fast 
  next
    case (Suc m) 
    with lhs_n.elims[OF conjunct1[OF n(2)[unfolded prod.simps], symmetric]] rho have l':"l = (U \<rho> m)\<langle>snd (cs ! m)\<rangle>" by blast
    from Suc n(3) have m:"m < length (snd \<rho>)" by fastforce
    from U_cond[OF n(1) this] obtain h where u:"U_fun \<rho> m h" "h \<notin> F" by auto
    with step[unfolded rstep_r_p_s_def l'] obtain us where w:"w = Fun h us" by force 
    have "\<exists>n < length (snd \<rho>).(l, r) = (lhs_n \<rho> (Suc n), rhs_n \<rho> (Suc n)) \<and> U_fun \<rho> n h \<and> h \<notin> F" 
      by(rule exI[of _ "m"], insert n[unfolded Suc] u m, auto)
    with w n(1) show ?thesis by blast
  qed
qed


lemma same_U_same_rules:
  assumes inR:"\<rho> \<in> R" "\<rho>' \<in> R"
    and u:"U \<rho> n = U \<rho>' n"
    and pe:"prefix_equivalent \<rho> \<rho>' n"
  shows "\<forall>m \<le> n. (lhs_n \<rho> m, rhs_n \<rho> m) = (lhs_n \<rho>' m,rhs_n \<rho>' m)"
proof(rule,rule)
  fix m
  assume m:"m \<le> n"
  from pe have n:" n < length (snd \<rho>)" "n < length (snd \<rho>')" unfolding prefix_equivalent_def by auto
  note pe= pe[unfolded prefix_equivalent_def] 
  from U_cond[OF inR(1) n(1)] inR(2) n(2) u have *:"(\<forall>i\<le>n. U \<rho> i = U \<rho>' i)" by metis
  obtain l r cs where rho:"\<rho>=((l,r),cs)" by (cases \<rho>, auto)
  obtain l' r' cs' where rho':"\<rho>'=((l',r'),cs')" by (cases \<rho>', auto)
  from rhs_n.simps[of "(l,r)" cs m] m n have r:"rhs_n \<rho> m = (U \<rho> m)\<langle>si \<rho> m\<rangle>" unfolding rho by fastforce
  from rhs_n.simps[of "(l',r')" cs' m] m n have r':"rhs_n \<rho>' m = (U \<rho>' m)\<langle>si \<rho>' m\<rangle>" unfolding rho' by fastforce
  from pe n m have s:"si \<rho> m = si \<rho>' m" by auto
  from r r' have r: "rhs_n \<rho> m = rhs_n \<rho>' m" unfolding *[rule_format, OF m] s by presburger
  have "lhs_n \<rho> m = lhs_n \<rho>' m" proof(cases m)
    case 0
    from pe have "l=l'" unfolding rho rho' by auto
    then show ?thesis unfolding 0 lhs_n.simps rho rho' by auto
  next
    case (Suc k)
    note us = *[rule_format, of k, unfolded Suc]
    from lhs_n.simps(2)[of "(l,r)" cs k] have l:"lhs_n \<rho> m = (U \<rho> k)\<langle>ti \<rho> k\<rangle>" unfolding rho Suc by simp
    from lhs_n.simps(2)[of "(l',r')" cs' k] have l':"lhs_n \<rho>' m = (U \<rho>' k)\<langle>ti \<rho>' k\<rangle>" unfolding rho' Suc by simp
    from pe n m have t:"ti \<rho> k = ti \<rho>' k" unfolding Suc by auto
    from l l' *[rule_format, of k] m[unfolded Suc] show ?thesis unfolding  t by auto   
  qed
  with r show "(lhs_n \<rho> m, rhs_n \<rho> m) = (lhs_n \<rho>' m,rhs_n \<rho>' m)" by simp
qed

lemma prefix_equivalent_refl:
  assumes "n < length (snd \<rho>)"
  shows "prefix_equivalent \<rho> \<rho> n"
  using assms unfolding prefix_equivalent_def by auto

lemma ur_step_urule:
  assumes step:"(Fun f us,v) \<in> rstep_r_p_s UR (l,r) [] \<sigma>" 
    and rho:"\<rho> \<in> R" and n:"n < length (snd \<rho>)" 
    and u:"U \<rho> n = More f [] \<box> (map Var (Z \<rho> n))"
  shows "(f \<notin> F \<and> (\<exists>\<rho>'. \<rho>'\<in>R \<and> prefix_equivalent \<rho> \<rho>' n \<and> U \<rho> n = U \<rho>' n \<and> ((Fun f us,v) \<in> rstep_r_p_s UR (lhs_n \<rho>' (Suc n), rhs_n \<rho>' (Suc n)) [] \<sigma>))) 
  \<or> (\<exists>\<rho> \<in> R. (l,r) = (lhs_n \<rho> 0, rhs_n \<rho> 0))"
proof-
  from U_cond[OF rho n] u have "f \<notin> F" by force
  from ur_step_exhaust[OF step] obtain \<rho>' where 
    d: "\<rho>' \<in> R""(l, r) = (lhs_n \<rho>' 0, rhs_n \<rho>' 0) \<or> (
      (\<exists>n<length (snd \<rho>'). (l, r) = (lhs_n \<rho>' (Suc n), rhs_n \<rho>' (Suc n)) \<and> U_fun \<rho>' n f \<and> f \<notin> F))" 
    (is "?A \<or> ?B") by blast
  {assume ?A
    with d(1) have "\<exists>\<rho> \<in> R. (l,r) = (lhs_n \<rho> 0, rhs_n \<rho> 0)" by blast
  } note a = this
  {assume ?B
    then obtain m where m:"m<length (snd \<rho>')" "(l, r) = (lhs_n \<rho>' (Suc m), rhs_n \<rho>' (Suc m))" 
      "U_fun \<rho>' m f" "f \<notin> F" by blast
    from U_cond[OF rho n] u m d(1) have mn:"m = n" by fastforce
    have "\<exists>\<rho>'. \<rho>' \<in> R \<and> prefix_equivalent \<rho> \<rho>' n \<and> U \<rho> n = U \<rho>' n \<and> ((Fun f us,v) \<in> rstep_r_p_s UR (lhs_n \<rho>' (Suc n), rhs_n \<rho>' (Suc n)) [] \<sigma>)
         \<and> f \<notin> F" 
    proof (cases "\<rho> = \<rho>'")
      case True
      with m mn have lr:"((l, r) = (lhs_n \<rho> (Suc n), rhs_n \<rho> (Suc n)) \<and> f \<notin> F)" by meson
      show ?thesis by (rule exI[of _ \<rho>], insert step lr prefix_equivalent_refl[OF n] rho, auto)
    next
      case False
      from u U_cond[OF rho n] actxt.inject[of f "[]" "\<box>" "map Var (Z \<rho> n)"] have 
        "(\<forall>\<rho>' n' g b c a. \<rho>' \<in> R \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a \<longrightarrow> 
     f \<noteq> g \<or> n = n' \<and> (\<forall>i\<le>n. U \<rho> i = U \<rho>' i) \<and> prefix_equivalent \<rho> \<rho>' n)" by metis
      from this[rule_format, of \<rho>' m f] d(1) m(1) m(3) have us:"\<forall>i\<le>n. U \<rho> i = U \<rho>' i" "prefix_equivalent \<rho> \<rho>' n" by auto
      from us(1)[rule_format, of n] have u:"U \<rho> n = U \<rho>' n" by auto
      show ?thesis unfolding mn by(rule exI[of _ \<rho>'], insert step[unfolded m(2) mn] us(2) m(4) u d(1), auto)
    qed
  }
  with a d(2) show ?thesis by fast
qed


lemma Um_funs_R:
  assumes um:"U \<rho> m = (More Um Nil Hole (map Var (Z \<rho> m)))" and len:"m < length (snd \<rho>)"
    and rhoR:"\<rho> \<in> R"
  shows "Um \<notin> F"
  using U_cond[OF rhoR len] um by auto

definition par_urstep_below_root :: "(('f,'v) term \<times> ('f,'v) term) set" where
  "par_urstep_below_root  \<equiv> {(s,t). \<exists>ts ss f. s = Fun f ss \<and> t = Fun f ts \<and> 
     (\<forall>x<length ts. (ss ! x, ts ! x) \<in> par_rstep UR) \<and> length ss = length ts}"

lemma par_urstep_par_rstep:
  "par_urstep_below_root \<subseteq> par_rstep UR" 
  unfolding par_urstep_below_root_def by auto

lemma all_ctxt_closed_par_rsteps: "all_ctxt_closed UNIV ((par_rstep UR)^*)" 
  using all_ctxt_closed_par_rstep by (blast intro: trans_ctxt_imp_all_ctxt_closed refl_rtrancl trans_rtrancl)

lemma par_urstep_below_root_refl: "(Fun f us, Fun f us) \<in> par_urstep_below_root" 
  unfolding par_urstep_below_root_def by blast

lemma par_rstep_below_root_pow_same_root1:
  "(Fun f xs, t) \<in> par_urstep_below_root ^^ n \<Longrightarrow> \<exists> ys. t = Fun f ys"
  unfolding par_urstep_below_root_def by (induct n arbitrary: t, auto)

lemma par_rstep_below_root_pow_same_root2:
  "((t, Fun f xs) \<in> par_urstep_below_root ^^ n \<Longrightarrow> \<exists> ys. t = Fun f ys)"
proof (induct n arbitrary:t)
  case 0
  then show ?case unfolding par_urstep_below_root_def by auto 
next
  case (Suc i)
  from relpow_Suc_D2[OF Suc(2)] obtain t' where d:"(t, t') \<in> par_urstep_below_root" "(t', Fun f xs) \<in> par_urstep_below_root ^^ i" by blast
  from Suc(1) d(2) obtain zs where "t' = Fun f zs"  by auto
  from d(1)[unfolded this] show ?case  unfolding par_urstep_below_root_def by auto 
qed

lemma par_rstep_below_root_pow_same_length: (* currently unused *)
  "(Fun f xs, Fun f ys) \<in> par_urstep_below_root ^^ n \<Longrightarrow> length xs = length ys"
  unfolding par_urstep_below_root_def by (induct n arbitrary: ys, auto)

lemma linear_term_ti:
  assumes ll:"left_linear_trs UR"
    and rho:"\<rho> \<in> R"
    and i:"i < length (snd \<rho>)"
  shows "linear_term (ti \<rho> i)"
proof- 
  from i have "Suc i \<le> length (snd \<rho>)" by auto
  with rho rules_def have "(lhs_n \<rho> (Suc i), rhs_n \<rho> (Suc i)) \<in> UR" unfolding UR_def by blast
  with ll[unfolded left_linear_trs_def, rule_format, OF this] have lin:"linear_term (lhs_n \<rho> (Suc i))" by force
  from rho obtain lr cs where rho':"\<rho> = (lr,cs)" by fastforce
  with lin lhs_n.simps(2) have "linear_term (U \<rho> i)\<langle>ti \<rho> i\<rangle>" by auto
  with linear_term.elims(1) U_cond[OF rho i] show ?thesis by force
qed

lemma sig_F_ti:
  assumes rho:"\<rho> \<in> R"
    and i:"i < length (snd \<rho>)"
  shows "sig_F (ti \<rho> i)"
proof-  
  obtain lr cs where rho':"\<rho> = (lr, cs)" by fastforce
  with i have set:"(si \<rho> i, ti \<rho> i) \<in> set cs" by fastforce
  have 1:"funs_term (ti \<rho> i) \<subseteq> funs_rule (si \<rho> i, ti \<rho> i)" using funs_rule_def rho' by fastforce
  with set have 2:"funs_term (ti \<rho> i) \<subseteq> funs_trs (set cs)" unfolding funs_trs_def by blast
  then have "funs_term (ti \<rho> i) \<subseteq> funs_crule \<rho>" unfolding funs_crule_def rho' by force
  with rho F show ?thesis unfolding sig_F_def funs_ctrs_def  by force
qed

lemma sig_F_si:
  assumes rho:"\<rho> \<in> R"
    and i:"i < length (snd \<rho>)"
  shows "sig_F (si \<rho> i)"
proof-  
  obtain lr cs where rho':"\<rho> = (lr, cs)" by fastforce
  with i have set:"(si \<rho> i, ti \<rho> i) \<in> set cs" by fastforce
  have 1:"funs_term (si \<rho> i) \<subseteq> funs_rule (si \<rho> i, ti \<rho> i)" using funs_rule_def rho' by fastforce
  with set have 2:"funs_term (si \<rho> i) \<subseteq> funs_trs (set cs)" unfolding funs_trs_def by blast
  then have "funs_term (si \<rho> i) \<subseteq> funs_crule \<rho>" unfolding funs_crule_def rho' by force
  with rho F set show ?thesis unfolding sig_F_def funs_ctrs_def by force
qed

lemma sig_F_l: "\<rho> \<in> R \<Longrightarrow> sig_F (clhs \<rho>)" using F
  unfolding sig_F_def funs_ctrs_def using funs_crule_def[of \<rho>, unfolded funs_rule_def] by blast

lemma sig_F_r: "\<rho> \<in> R \<Longrightarrow> sig_F (crhs \<rho>)" using F
  unfolding sig_F_def funs_ctrs_def using funs_crule_def[of \<rho>, unfolded funs_rule_def] by blast

lemma sig_F_subst: 
  "\<forall>x\<in>vars_term l. sig_F (\<tau> x) \<Longrightarrow> sig_F l \<Longrightarrow> sig_F (l \<cdot> \<tau>)"
proof(induct l)
  case (Var x) 
  from Var(1)[rule_format, unfolded Var] term.simps(17) show ?case by auto
next
  case (Fun f ts)
  { fix t assume t:"t \<in> set ts"
    then have "vars_term t \<subseteq> vars_term (Fun f ts)" by auto
    with Fun(2) have v:"\<forall>x\<in>vars_term t. sig_F (\<tau> x)" by blast
    from Fun(3)[unfolded sig_F_def funs_ctrs_def term.simps(16)] t have "sig_F t" unfolding sig_F_def funs_ctrs_def by auto
    from Fun(1)[OF t v this] have "sig_F (t \<cdot> \<tau>)" by simp
  } note args = this
  from Fun(3)[unfolded sig_F_def funs_ctrs_def] have "f \<in> F"  unfolding sig_F_def funs_ctrs_def by force
  with args show ?case unfolding sig_F_def by auto
qed

abbreviation "cond_rule" :: "('f,'v) crule \<Rightarrow> bool"
  where "cond_rule \<rho> \<equiv> \<rho> \<in> R \<and> length (snd \<rho>) > 0"

definition "complete_R_step_simulation" :: "(nat \<Rightarrow> ('f,'v) term) \<Rightarrow> nat \<Rightarrow> ('f,'v) crule \<Rightarrow> bool"
  where "complete_R_step_simulation ui n \<rho> \<equiv> \<exists> j ni \<sigma>i.
  (\<forall>i. 0 \<le> i \<and> i \<le> length (snd \<rho>) \<longrightarrow> 
   j i < n \<and> (ui (j i), ui (Suc (j i))) \<in> (rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i))) \<and>
  (\<forall>i. 0 \<le> i \<and> i < length (snd \<rho>) \<longrightarrow> (ui (Suc (j i)), ui (j (Suc i))) \<in> par_urstep_below_root ^^ (ni i)) \<and>
  j 0 + sum_list (map (Suc \<circ> ni) [0..<length (snd \<rho>)]) = j (length (snd \<rho>))"

definition "partial_R_step_simulation" :: "(nat \<Rightarrow> ('f,'v) term) \<Rightarrow> nat \<Rightarrow> ('f,'v) crule \<Rightarrow>nat \<Rightarrow> bool"
  where "partial_R_step_simulation ui n \<rho> k \<equiv> \<exists> j ni nm \<sigma>i.
  k < length (snd \<rho>) \<and>
  (\<forall>i. 0 \<le> i \<and> i \<le> k \<longrightarrow> 
   j i < n \<and> (ui (j i), ui (Suc (j i))) \<in> (rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i))) \<and>
  (\<forall>i. 0 \<le> i \<and> i < k \<longrightarrow> (ui (Suc (j i)), ui (j (Suc i))) \<in> par_urstep_below_root ^^ (ni i)) \<and>
  (ui (Suc (j k)), ui n) \<in> par_urstep_below_root ^^ nm \<and>
  j 0 + sum_list (map (Suc \<circ> ni) [0..<k]) + Suc nm = n"


lemma extend_partial_R_step_sim:
  assumes sim:"partial_R_step_simulation ui m \<rho> k" and step:"(ui m, ui (Suc m)) \<in> par_urstep_below_root"
  shows "partial_R_step_simulation ui (Suc m) \<rho> k"
proof-
  let ?usteps = "\<lambda> m k j \<sigma>i. (\<forall>i. 0 \<le> i \<and> i \<le> k \<longrightarrow> j i < m \<and> (ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i))"
  let ?isteps = "\<lambda> k j ni. \<forall>i. 0 \<le> i \<and> i < k \<longrightarrow> (ui (Suc (j i)), ui (j (Suc i))) \<in> par_urstep_below_root ^^ ni i"
  let ?suffix = "\<lambda> m k j nm. (ui (Suc (j k)), ui m) \<in> par_urstep_below_root ^^ nm"
  let ?sum = "\<lambda> m k j ni nm. j 0 + sum_list (map (Suc \<circ> ni) [0..<k]) + Suc nm = m"
  from sim[unfolded partial_R_step_simulation_def] obtain j ni nm \<sigma>i where
    sim:"k < length (snd \<rho>)" "?usteps m k j \<sigma>i" "?isteps k j ni" "?suffix m k j nm" "?sum m k j ni nm" by force
  from sim(2) have 2:"?usteps (Suc m) k j \<sigma>i" by force
  from sim(4) step have 4:"?suffix (Suc m) k j (Suc nm)" by auto
  from sim(5) have 5:"?sum (Suc m) k j ni (Suc nm)" by simp
  from sim(1) 2 sim(3) 4 5 show ?thesis unfolding partial_R_step_simulation_def by blast
qed

lemma complete_partial_R_step_sim:
  assumes sim:"partial_R_step_simulation ui m \<rho> (length (snd \<rho>) - 1)"
    and step:"(ui m, ui (Suc m)) \<in> rstep_r_p_s UR (lhs_n \<rho> (length (snd \<rho>)), rhs_n \<rho> (length (snd \<rho>))) [] \<sigma>k"
    and lcs:"length (snd \<rho>) > 0"
  shows "complete_R_step_simulation ui (Suc m) \<rho>"
proof-
  let ?ustep = "\<lambda> m j \<sigma>i i. j i < m \<and> (ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i)"
  let ?istep  = "\<lambda> j ni i. (ui (Suc (j i)), ui (j (Suc i))) \<in> par_urstep_below_root ^^ ni i"
  let ?usteps = "\<lambda> m k j \<sigma>i. (\<forall>i. 0 \<le> i \<and> i \<le> k \<longrightarrow> ?ustep m j \<sigma>i i)"
  let ?isteps = "\<lambda> k j ni. \<forall>i. 0 \<le> i \<and> i < k \<longrightarrow> ?istep j ni i"
  let ?suffix = "\<lambda> m k j nm. (ui (Suc (j k)), ui m) \<in> par_urstep_below_root ^^ nm"
  let ?sum = "\<lambda> m k j ni nm. j 0 + sum_list (map (Suc \<circ> ni) [0..<k]) + Suc nm = m"
  let ?sum' = "\<lambda> j ni. j 0 + sum_list (map (Suc \<circ> ni) [0..<length (snd \<rho>)]) = j (length (snd \<rho>))"
  from lcs gr0_implies_Suc obtain k where lk:"length (snd \<rho>) = Suc k" by auto
  with sim[unfolded partial_R_step_simulation_def] obtain j ni nm \<sigma>i where
    sim:"k \<le> length (snd \<rho>)" "?usteps m k j \<sigma>i" "?isteps k j ni" "?suffix m k j nm" "?sum m k j ni nm" by force
  let ?ni = "\<lambda>i. if i < k then ni i else nm" 
  let ?j = "\<lambda>i. if i \<le> k then j i else m" 
  let ?\<sigma>i = "\<lambda>i. if i \<le> k then \<sigma>i i else \<sigma>k"
  { fix i
    assume a:"0 \<le> i" "i \<le> Suc k"
    have "?ustep (Suc m) ?j ?\<sigma>i i" unfolding lk by (cases "i = Suc k", insert sim(2)[rule_format, of i] step lk a, auto) 
  } note 1 = this
  { fix i
    assume a:"0 \<le> i" "i < Suc k" 
    have "?istep ?j ?ni i" unfolding lk by (cases "i = k", insert sim(3)[rule_format, of i] sim(4) lk a, auto) 
  } note 2 = this
  have l:"(map (Suc \<circ> ni) [0..<k]) @ [Suc nm] = map (Suc \<circ> ?ni) [0..<Suc k]" unfolding lk by (induct k, auto)
  have "sum_list (map (Suc \<circ> ni) [0..<k]) + Suc nm = sum_list ((map (Suc \<circ> ni) [0..<k]) @ [Suc nm])" by simp
  from this[unfolded l] sim(5) have 3:"?sum (Suc m) (Suc k) ?j ?ni 0" by force
  show ?thesis unfolding complete_R_step_simulation_def lk by (rule exI[of _ ?j], rule exI[of _ ?ni], rule exI[of _ ?\<sigma>i], insert 1 2 3 lk, auto)
qed


lemma extend_complete_R_step_sim:
  assumes sim:"complete_R_step_simulation ui m \<rho>" and step:"(ui m, ui (Suc m)) \<in> par_rstep UR"
  shows "complete_R_step_simulation ui (Suc m) \<rho>"
proof-
  let ?usteps = "\<lambda> m j \<sigma>i. (\<forall>i. 0 \<le> i \<and> i \<le> length (snd \<rho>) \<longrightarrow> 
  j i < m \<and> (ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i))"
  let ?isteps = "\<lambda> j ni. \<forall>i. 0 \<le> i \<and> i < length (snd \<rho>) \<longrightarrow> 
  (ui (Suc (j i)), ui (j (Suc i))) \<in> par_urstep_below_root ^^ ni i"
  let ?sum = "\<lambda> j ni. j 0 + sum_list (map (Suc \<circ> ni) [0..<length (snd \<rho>)]) = j (length (snd \<rho>))"
  from sim[unfolded complete_R_step_simulation_def] obtain j ni \<sigma>i where sim: "?usteps m j \<sigma>i" "?isteps j ni" "?sum j ni" by force
  from sim(1) have 1:"?usteps (Suc m) j \<sigma>i" by force
  with sim show ?thesis unfolding complete_R_step_simulation_def by blast
qed

lemma first_root_step:
  assumes ui:"\<forall>i< n. (ui i, ui (Suc i)) \<in> par_rstep UR"
    and root_step:"\<exists> i < n. \<exists> l r \<sigma>. ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR"
    and m0:"m0 = (LEAST i. i < n \<and>  (\<exists> l r \<sigma>. ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR))"
    and first:"sig_F (ui 0)"
  shows "\<exists> \<rho> \<in> R. (\<exists> \<sigma>. (ui m0, ui (Suc m0)) \<in> rstep_r_p_s UR (lhs_n \<rho> 0,rhs_n \<rho> 0) [] \<sigma>)"
proof-
  let ?root_step_at = "\<lambda>i. i < n \<and>  (\<exists> l r \<sigma>. ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR)"
  have m0':"m0 < n \<and>  (\<exists> l r \<sigma>. ui m0 = l \<cdot> \<sigma> \<and> (ui (Suc m0)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR)" unfolding m0
    by (rule LeastI_ex, insert root_step, auto)
  then obtain l r \<sigma> where m0':"m0 < n" "ui m0 = l \<cdot> \<sigma>" "ui (Suc m0) = r \<cdot> \<sigma>" "(l, r) \<in> UR" by auto
  then have step:"(ui m0, ui (Suc m0)) \<in> rstep_r_p_s UR (l,r) [] \<sigma>" unfolding rstep_r_p_s_def by auto
  { assume "is_Var (ui 0)"
    then obtain x where ui0:"ui 0 = Var x" by auto
    {fix i
      have "i \<le> m0 \<Longrightarrow> ui i = Var x" proof(induct i, simp add:ui0)
        case (Suc i)
        then have uii:"ui i = Var x" by auto
        from Suc have "i < m0" by auto
        from not_less_Least[OF this[unfolded m0]] have rs:"\<not> ?root_step_at i" by simp
        from Suc m0' have "i < n" by auto
        with ui[rule_format, OF this, unfolded par_rstep.simps[of "ui i"]] uii rs show ?case by force
      qed
      then have "i \<le> m0 \<Longrightarrow> is_Var (ui i)" by auto
    } note vars = this
    from vars[OF le_refl] ur_step_exhaust[OF step] step have ?thesis by auto
  } note var = this
  { assume "is_Fun (ui 0)"
    then obtain f us where ui0:"ui 0 = Fun f us" by auto
    { fix j
      assume "j \<le> m0"
      then have "\<exists> vs. ui j = Fun f vs" proof(induct j, simp add:ui0)
        case (Suc j)
        then obtain ws where uii:"ui j = Fun f ws" by auto 
        from Suc have "j < m0" by auto
        from not_less_Least[OF this[unfolded m0]] have rs:"\<not> ?root_step_at j" by simp
        from Suc m0' have "j < n" by auto
        with ui[rule_format, OF this, unfolded par_rstep.simps[of "ui j"]] uii rs show ?case by force
      qed
    }
    then have uim0:"\<exists> vs. ui m0 = Fun f vs" by simp
    from ui0 first[unfolded sig_F_def] have "f \<in> F" by auto
    with uim0 ur_step_exhaust[OF step] step have ?thesis by auto
  }
  with var show ?thesis by blast
qed

lemma Lemma_16:
  assumes ui:"\<forall>i< n. (ui i, ui (Suc i)) \<in> par_rstep UR"
    and root_step:"\<exists> i < n. \<exists> l r \<sigma>. ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR"
    and first:"sig_F (ui 0)"
  shows "\<exists> \<rho> k. \<rho> \<in> R \<and> (complete_R_step_simulation ui n \<rho> \<or> partial_R_step_simulation ui n \<rho> k)"
proof-
  let ?ucstep = "\<forall> i l r \<sigma>. i < n \<and> ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR \<longrightarrow> ((l, r), []) \<notin> R"
  show ?thesis proof(cases ?ucstep)
    case False
    then obtain i l r \<sigma> where *:"i < n \<and> ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR \<and> ((l, r), []) \<in> R" by blast
    then have **:"(ui i, ui (Suc i)) \<in> rstep_r_p_s UR (l, r) [] \<sigma>" unfolding rstep_r_p_s_def by simp
    have "complete_R_step_simulation ui n ((l, r), [])" unfolding complete_R_step_simulation_def
      by (rule exI[of _ "\<lambda>j. i"],  rule exI[of _"\<lambda>j. 0"],rule exI[of _ "\<lambda>j. \<sigma>"], insert * **, auto)
    with * show?thesis by blast
  next
    case True
    note root_step_not_R = this
    let ?root_step_at = "\<lambda>i. i < n \<and>  (\<exists> l r \<sigma>. ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR)"
    define n0 where "n0 = (LEAST i.?root_step_at i)"
    have "n0 < n \<and>  (\<exists> l r \<sigma>. ui n0 = l \<cdot> \<sigma> \<and> (ui (Suc n0)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR)" unfolding n0_def 
      by (rule LeastI_ex, insert root_step, auto)
    then have n0n:"n0 < n" by auto
    let ?rule0_step = "\<lambda>i. (n - i) < n \<and> (\<exists>\<rho>\<in>R. \<exists>\<sigma>. (ui (n-i), ui (Suc (n-i))) \<in> rstep_r_p_s UR (lhs_n \<rho> 0, rhs_n \<rho> 0) [] \<sigma>)"
    from first_root_step[OF ui root_step _ first] n0_def n0n have first_rule0_step:"?rule0_step (n - n0)" by auto
    define mm0 where "mm0 = (LEAST i. ?rule0_step i)"
    define m0 where "m0 = n - mm0"
    have " n - mm0 < n \<and> (\<exists>\<rho>\<in>R. \<exists>\<sigma>. (ui (n-mm0), ui (Suc (n-mm0))) \<in> rstep_r_p_s UR (lhs_n \<rho> 0, rhs_n \<rho> 0) [] \<sigma>)" unfolding mm0_def
      by (rule LeastI_ex, insert first_rule0_step, auto)
    then obtain \<rho>0 \<sigma>1 where rhoR:"\<rho>0 \<in> R" and x:"n -mm0 < n""(ui (n-mm0), ui (Suc (n-mm0))) \<in> rstep_r_p_s UR (lhs_n \<rho>0 0, rhs_n \<rho>0 0) [] \<sigma>1" by blast
    then have first_step:"(ui m0, ui (Suc m0)) \<in> rstep_r_p_s UR (lhs_n \<rho>0 0, rhs_n \<rho>0 0) [] \<sigma>1" unfolding m0_def by auto
    from x have m0n:" m0 < n" unfolding m0_def by auto
    { fix j
      assume a:"m0 < j" "j < n"
      with m0n have "n - j < mm0" unfolding m0_def by linarith
      from not_less_Least[of "n-j" ?rule0_step,OF this[unfolded mm0_def]] x(1) have "\<not>?rule0_step (n - j)" by blast
      with a have "\<forall>\<rho>\<in>R. \<forall>\<sigma>. (ui j, ui (Suc j)) \<notin> rstep_r_p_s UR (lhs_n \<rho> 0, rhs_n \<rho> 0) [] \<sigma>" by simp
    } note no_more_rule0 = this
    let ?l = "lhs_n \<rho>0 0" and ?r = "rhs_n \<rho>0 0"
    define l where "l = ?l"
    from first_step[unfolded rstep_r_p_s_def] have i:"ui m0 = ?l \<cdot> \<sigma>1" "ui (Suc m0) = ?r \<cdot> \<sigma>1" "(?l, ?r) \<in> UR" by auto
    with root_step_not_R[rule_format, of m0] m0n have notR:"((?l,?r),[]) \<notin> R" by blast
    with lhs_n.simps(1) obtain rr cs where rho:"\<rho>0 = ((l,rr),cs)" unfolding l_def by (metis prod.collapse)
    from notR[unfolded rhs_n.simps] rhoR rho have lcs:"0 < length cs" by fastforce
    from lcs rho rhs_n.simps have r:"?r = (U \<rho>0 0)\<langle>fst (cs ! 0)\<rangle>" by force
    from U_cond[OF rhoR] lcs obtain U0 where U0:"U_fun \<rho>0 0 U0" unfolding rho by fastforce
    with r i(2) obtain ts where uiSm0:"ui (Suc m0) = Fun U0 ts" by force
        (* internal lemma *)
    let ?uterm_at = "\<lambda>\<rho> n k. \<exists> Uk ts. ui n = Fun Uk ts \<and> U_fun \<rho> k Uk \<and> k < length (snd \<rho>)"
    let ?sim = "\<lambda>\<rho> n k. complete_R_step_simulation ui n \<rho> \<or> (partial_R_step_simulation ui n \<rho> k \<and> ?uterm_at \<rho> n k)"
    { fix m k Uk ts
      let ?ustep = "\<lambda> \<rho> m j \<sigma>i i. j i < m \<and> (ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i)"
      let ?usteps = "\<lambda> \<rho> m k j \<sigma>i. (\<forall>i. 0 \<le> i \<and> i \<le> k \<longrightarrow> ?ustep \<rho> m j \<sigma>i i)"
      let ?istep  = "\<lambda> j ni i. (ui (Suc (j i)), ui (j (Suc i))) \<in> par_urstep_below_root ^^ ni i"
      let ?isteps = "\<lambda> k j ni. \<forall>i. 0 \<le> i \<and> i < k \<longrightarrow> ?istep j ni i"
      let ?suffix = "\<lambda> m k j nm. (ui (Suc (j k)), ui m) \<in> par_urstep_below_root ^^ nm"
      let ?sum = "\<lambda> m k j ni nm. j 0 + sum_list (map (Suc \<circ> ni) [0..<k]) + Suc nm = m"
      assume "m0 < m" and "m \<le> n"
      then have "\<exists>\<rho> k. \<rho> \<in> R \<and> ?sim \<rho> m k" proof (induct m)
        case 0
        then show ?case unfolding sig_F_def by simp
      next 
        case (Suc m) note ih = this
        show ?case proof (cases "m = m0")
          case True
          from uiSm0 lcs U0 have uterm:"?uterm_at \<rho>0 (Suc m) 0" unfolding True rho by simp
          from first_step rhoR have 1:"?usteps \<rho>0 (Suc m) 0 (\<lambda>i. m) (\<lambda>i. \<sigma>1)" unfolding True by fastforce
          have "?suffix (Suc m) 0 (\<lambda>i. m) 0" by auto
          with 1 i(3)[unfolded r] lcs have "partial_R_step_simulation ui (Suc m) \<rho>0 0" unfolding partial_R_step_simulation_def True rho by fastforce
          with uterm rhoR show ?thesis by blast
        next
          case False
          with Suc have lt:"m0 < m" and mn':"m \<le>n" by auto
          with Suc(1)[OF lt mn'] Suc(3) obtain \<rho> k where rhoR:"\<rho> \<in> R" and k:"?sim \<rho> m k" by blast
          show ?thesis proof (cases "complete_R_step_simulation ui m \<rho>")
            case True
            from ui[rule_format, of m] Suc have "(ui m, ui (Suc m)) \<in> par_rstep UR" by auto
            with extend_complete_R_step_sim[OF True this] rhoR show ?thesis by blast
          next
            case False
            with k have part:"partial_R_step_simulation ui m \<rho> k" and uterm:"?uterm_at \<rho> m k" by auto
            from part[unfolded partial_R_step_simulation_def] obtain j ni nm \<sigma>i where 
              sim:"?usteps \<rho> m k j \<sigma>i" "?isteps k j ni" "?suffix m k j nm" "?sum m k j ni nm" by blast
            from uterm obtain Uk ts where Uk:"ui m = Fun Uk ts" "U_fun \<rho> k Uk" "k < length (snd \<rho>)" by auto
            show ?thesis proof (cases "(ui m, ui (Suc m)) \<in> par_urstep_below_root")
              case True
              from this[unfolded par_urstep_below_root_def] Uk have uterm:"?uterm_at \<rho> (Suc m) k" by force
              with extend_partial_R_step_sim[OF part True] rhoR show ?thesis by blast
            next
              case False 
              from ui[rule_format, of m] Suc have last_step:"(ui m, ui (Suc m)) \<in> par_rstep UR" by auto
              from this[unfolded par_rstep.simps[of "ui m"]] False[unfolded par_urstep_below_root_def] obtain l r \<sigma>k where
                last_step':"ui m = l \<cdot> \<sigma>k" "ui (Suc m) = r \<cdot> \<sigma>k" "(l, r) \<in> UR" unfolding Uk by blast
              then have last_step:"(ui m, ui (Suc m)) \<in> rstep_r_p_s UR (l,r) [] \<sigma>k" unfolding rstep_r_p_s_def by auto
              from Suc(3) have "m < n" by force
              from no_more_rule0[OF lt this] last_step' rhoR have "\<not>(\<exists>\<rho>\<in>R. (l, r) = (lhs_n \<rho> 0, rhs_n \<rho> 0))"
                unfolding rstep_r_p_s_def by auto
              with ur_step_urule[OF last_step[unfolded Uk] rhoR Uk(3) Uk(2)] have 
                "(\<exists>\<rho>'. \<rho>' \<in> R \<and> prefix_equivalent \<rho> \<rho>' k \<and> U \<rho> k = U \<rho>' k \<and> (Fun Uk ts, ui (Suc m)) \<in> rstep_r_p_s UR (lhs_n \<rho>' (Suc k), rhs_n \<rho>' (Suc k)) [] \<sigma>k)"
                by blast
              then obtain \<rho>' where rhoR':"\<rho>' \<in> R" and pe:"prefix_equivalent \<rho> \<rho>' k" and uks:"U \<rho> k = U \<rho>' k" and
                lstep:"(Fun Uk ts, ui (Suc m)) \<in> rstep_r_p_s UR (lhs_n \<rho>' (Suc k), rhs_n \<rho>' (Suc k)) [] \<sigma>k" by blast
              from pe have krho':"k < length (snd \<rho>')" unfolding prefix_equivalent_def  by blast
              let ?ni = "\<lambda>i. if i < k then ni i else nm" 
              let ?j = "\<lambda>i. if i \<le> k then j i else m" 
              let ?\<sigma>i = "\<lambda>i. if i \<le> k then \<sigma>i i else \<sigma>k" 
              { fix i
                assume a:"0 \<le> i" "i \<le> Suc k"
                have "?ustep \<rho>' (Suc m) ?j ?\<sigma>i i" 
                proof(cases "i=Suc k")
                  case True 
                  with lstep Uk(1) show ?thesis by auto
                next
                  case False
                  with a sim(1) have ji:"j i < m" "(ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i)" by auto
                  with same_U_same_rules[OF rhoR rhoR' uks pe, rule_format, of i] a(2) False
                  have "(ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho>' i, rhs_n \<rho>' i) [] (\<sigma>i i)" by force
                  with ji(1) a False show ?thesis by auto
                qed
              } note 1 = this
              { fix i
                assume a:"0 \<le> i" "i < Suc k" 
                have "?istep ?j ?ni i" by (cases "i = k", insert sim(2)[rule_format, of i] sim(3) a, auto) 
              } note 2 = this
              have l:"(map (Suc \<circ> ni) [0..<k]) @ [Suc nm] = map (Suc \<circ> ?ni) [0..<Suc k]" by (induct k, auto)
              have "sum_list (map (Suc \<circ> ni) [0..<k]) + Suc nm = sum_list ((map (Suc \<circ> ni) [0..<k]) @ [Suc nm])" by simp
              from this[unfolded l] sim(4) have 3:"?sum (Suc m) (Suc k) ?j ?ni 0" by force
              show ?thesis proof(cases "Suc k = length (snd \<rho>')")
                case True
                have "complete_R_step_simulation ui (Suc m) \<rho>'" unfolding complete_R_step_simulation_def
                  by (rule exI[of _ ?j], rule exI[of _ ?ni], rule exI[of _ ?\<sigma>i], insert 1 2 3 True krho', auto)
                with rhoR' show ?thesis by blast
              next
                case False
                with krho' have kcs:"Suc k < length (snd \<rho>')" unfolding rho by auto
                have 4:"?suffix (Suc m) (Suc k) ?j 0" by auto 
                from U_cond[OF rhoR'] kcs obtain Uk where Uk:"U_fun \<rho>' (Suc k) Uk" unfolding rho by fastforce
                obtain lr' cs' where rho':"\<rho>' = (lr', cs')" by (cases \<rho>', auto)
                from kcs Uk rhs_n.simps obtain ts' where r:"rhs_n \<rho>' (Suc k) = Fun Uk ts'" unfolding rho' by auto
                with lstep obtain ts'' where "ui (Suc m) = Fun Uk ts''" unfolding rstep_r_p_s_def by force
                with Uk kcs rho' have uterm:"?uterm_at \<rho>' (Suc m) (Suc k)" by simp
                have "partial_R_step_simulation ui (Suc m) \<rho>' (Suc k)" unfolding partial_R_step_simulation_def
                  by (rule exI[of _ ?j], rule exI[of _ ?ni], rule exI[of _ 0], rule exI[of _ ?\<sigma>i], insert 1 2 3 4 kcs rho, auto)
                with uterm rhoR' show ?thesis by blast
              qed
            qed
          qed
        qed
      qed
    } 
    from this[OF m0n]  show ?thesis by auto
  qed
qed

lemma par_rstep_pow_imp_args_par_rstep_pow: 
  "(Fun f xs, Fun f ys) \<in> par_urstep_below_root ^^ n = ((\<forall>i<length xs. (xs ! i, ys ! i) \<in> par_rstep UR ^^ n) \<and> length xs = length ys)"
proof
  assume "(Fun f xs, Fun f ys) \<in> par_urstep_below_root ^^ n"
  then show "((\<forall>i<length xs. (xs ! i, ys ! i) \<in> par_rstep UR ^^ n) \<and> length xs = length ys)"
  proof(induct n arbitrary:ys)
    case 0
    then show ?case unfolding par_urstep_below_root_def by auto
  next
    case (Suc n)
    from  relpow_Suc_E[OF Suc(2)] par_rstep_below_root_pow_same_root1 obtain zs where 
      steps:"(Fun f xs, Fun f zs) \<in> par_urstep_below_root ^^ n" "(Fun f zs, Fun f ys) \<in> par_urstep_below_root" by metis
    from steps(1) par_rstep_below_root_pow_same_length have len:"length xs = length zs" by auto
    from CollectD[OF steps(2)[unfolded par_urstep_below_root_def], unfolded split] have len':"length ys = length zs" by fastforce
    {fix i
      assume i:"i<length xs" 
      from Suc(1) steps(1) this have xs:"(xs ! i, zs ! i) \<in> par_rstep UR ^^ n" by auto
      from CollectD[OF steps(2)[unfolded par_urstep_below_root_def], unfolded split] i[unfolded len]
      have "(zs ! i, ys ! i)  \<in> par_rstep UR" by fastforce
      with xs have "(xs ! i, ys ! i) \<in> par_rstep UR ^^ (Suc n)" by auto
    } with len len' show ?case by auto
  qed
next
  assume "(\<forall>i<length xs. (xs ! i, ys ! i) \<in> par_rstep UR ^^ n) \<and> length xs = length ys"
  then show "(Fun f xs, Fun f ys) \<in> par_urstep_below_root ^^ n"
  proof(induct n arbitrary:ys)
    case 0 
    then have "\<forall>i<length xs. xs ! i = ys ! i" by simp 
    with 0 list_eq_iff_nth_eq have "xs = ys" by blast
    with 0 show ?case unfolding par_urstep_below_root_def by simp
  next
    case (Suc n)
    {fix i
      assume i:"i<length xs" 
      from conjunct1[OF Suc(2), rule_format, OF i] relpow_Suc_E have
        "\<exists>z. (xs ! i, z) \<in> par_rstep UR ^^ n \<and> (z, ys ! i) \<in> par_rstep UR" by auto
    }
    then obtain fz where fz:"(\<forall>i < length xs. (xs ! i, fz i) \<in> par_rstep UR ^^ n \<and> (fz i, ys ! i) \<in> par_rstep UR )" by metis
    let ?zs = "map fz [0..<length xs]"
    from Suc have len:"length ?zs = length ys" by simp
    from fz have zs:"(\<forall>i < length xs. (xs ! i, ?zs ! i) \<in> par_rstep UR ^^ n \<and> (?zs ! i, ys ! i) \<in> par_rstep UR)" by force
    with Suc have n:"(Fun f xs, Fun f ?zs) \<in> par_urstep_below_root ^^ n" by fastforce
    from zs len have "(Fun f ?zs, Fun f ys) \<in> par_urstep_below_root" unfolding par_urstep_below_root_def by force
    with n show ?case by auto
  qed
qed

lemma f_in_R_not_U_fun: "f \<in> F \<Longrightarrow> \<not>(\<exists> \<rho> i. \<rho> \<in> R \<and> i < length (snd \<rho>) \<and> U_fun \<rho> i f)"
proof
  assume fR:"f \<in> F" and  "\<exists> \<rho> i. \<rho> \<in> R \<and> i < length (snd \<rho>) \<and> U_fun \<rho> i f"
  then obtain \<rho> i where a:"\<rho> \<in> R" "i < length (snd \<rho>)" "U_fun \<rho> i f" by auto
  from U_cond[OF a(1-2)] a(3) have "f \<notin> F" by force
  with fR show False by auto
qed


abbreviation is_U_symbol :: "'f \<Rightarrow> bool"
  where "is_U_symbol f \<equiv> (\<exists> \<rho> \<in> R. \<exists> i < length (snd \<rho>). U_fun \<rho> i f)"

lemma sig_F_not_U:
  assumes sR:"sig_F t" shows "\<not>(\<exists> Ui zs.  is_U_symbol Ui \<and> (\<exists>zs. t = Fun Ui zs))"
proof (cases t, simp)
  case (Fun f us)
  from sR[unfolded sig_F_def Fun] have "f \<in> F" by auto
  from f_in_R_not_U_fun[OF this] Fun this show ?thesis by blast
qed

definition partial_aux :: "('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> (('f,'v) crule \<times> nat) \<Rightarrow> bool"
  where "partial_aux s t \<rho>k \<equiv> \<exists> \<sigma>i \<tau>1 \<tau>2.
  case \<rho>k of (\<rho>,k) \<Rightarrow>
  k < length (snd \<rho>) \<and>
  (s = (lhs_n \<rho> 0) \<cdot> \<tau>1) \<and> 
  (\<exists>ti Uk. t = Fun Uk (ti # (map \<tau>2 (Z \<rho> k))) \<and> U_fun \<rho> k Uk) \<and>
  (\<forall>x \<in> vars_term (lhs_n \<rho> 0). (\<tau>1 x,(\<sigma>i 0) x) \<in> (par_rstep UR) ^*) \<and>
  (\<forall>i. 0 \<le> i \<and> i < k \<longrightarrow> (\<forall>x \<in> set (Z \<rho> i). (\<sigma>i i x,(\<sigma>i (Suc i)) x) \<in> (par_rstep UR) ^*)) \<and>
  (\<forall>x \<in> set (Z \<rho> k). (\<sigma>i k x, \<tau>2 x) \<in> (par_rstep UR) ^*)"

(* The following Key Lemma corresponds to Lemma 4.2 in NSS12 *)
lemma soundness_key_lemma:
  assumes ll:"left_linear_trs UR"
    and s:"sig_F s"
    and t:"sig_F t" "linear_term t"
    and seq:"(s,t\<cdot>\<sigma>) \<in> (par_rstep UR) ^^ n"
  shows "\<exists> \<theta>. (s, t\<cdot>\<theta>) \<in> (cstep R)^* \<and> sig_F_subst \<theta> (vars_term t) \<and> 
 (\<forall> x \<in> vars_term t. (Var x\<cdot>\<theta>, Var x\<cdot>\<sigma>) \<in> (par_rstep UR) ^^ n) \<and> (sig_F (t\<cdot>\<sigma>) \<longrightarrow> t\<cdot>\<theta> = t\<cdot>\<sigma>) 
  \<and> (non_LV \<and> source_preserving R Z \<and> (\<exists> Ui zs. is_U_symbol Ui \<and> t\<cdot>\<sigma> = Fun Ui zs) \<longrightarrow>
      (\<exists> \<rho> \<tau>1 \<tau>2 k u. \<rho> \<in> R \<and> k < length (snd \<rho>) \<and> t\<cdot>\<theta> = (clhs \<rho>)\<cdot>\<tau>1 \<and> t\<cdot>\<sigma> = ((U \<rho> k) \<cdot>\<^sub>c \<tau>2)\<langle>u\<rangle> \<and> (\<forall>x \<in> vars_term (clhs \<rho>). (\<tau>1 x, \<tau>2 x) \<in> (par_rstep UR)^*)))"
proof-
  define t_U_cond where "t_U_cond = (\<lambda> t \<theta> \<sigma>. (non_LV \<and> source_preserving R Z \<and> (\<exists> Ui zs. is_U_symbol Ui \<and> (t ::('f,'v) term)\<cdot>\<sigma> = Fun Ui zs)) \<longrightarrow>
      (\<exists> \<rho> \<tau>1 \<tau>2 k u. \<rho> \<in> R \<and> k < length (snd \<rho>) \<and> t\<cdot>\<theta> = (clhs \<rho>)\<cdot>\<tau>1 \<and> t\<cdot>\<sigma> =((U \<rho> k) \<cdot>\<^sub>c \<tau>2)\<langle>u\<rangle> \<and> (\<forall>x \<in> vars_term (clhs \<rho>). (\<tau>1 x, \<tau>2 x) \<in> (par_rstep UR)^*)))"
  let ?A = "\<lambda> n s t \<sigma> .sig_F s \<and> sig_F t \<and> linear_term t \<and> (s,t \<cdot> \<sigma>) \<in> (par_rstep UR) ^^ n"
  let ?G = "\<lambda> n s t \<sigma> . \<exists> \<theta>. (s, t\<cdot>\<theta>) \<in> (cstep R)^* \<and> sig_F_subst \<theta> (vars_term t) \<and> 
  (\<forall> x \<in> vars_term t. (Var x\<cdot>\<theta>, Var x\<cdot>\<sigma>) \<in> (par_rstep UR) ^^ n) \<and> (sig_F (t\<cdot>\<sigma>) \<longrightarrow> t\<cdot>\<theta> = t\<cdot>\<sigma>) \<and> (t_U_cond t \<theta> \<sigma>)"
  let ?P = "\<lambda> (n,s). \<forall> t \<sigma>. (?A n s t \<sigma> \<longrightarrow> ?G  n s t \<sigma>)"
  from sig_F_not_U have sig_F_not_U:"\<And>t \<theta> \<sigma>. sig_F (t\<cdot>\<sigma>) \<Longrightarrow> t_U_cond t \<theta> \<sigma>" unfolding t_U_cond_def by fast
  have "?P (n,s)" proof(induct rule: wf_induct[OF wf_measures, of "[fst, size \<circ> snd]" ?P])
    case (1 nt) note ind = this
    obtain n s where ns: "nt = (n,s)" by force
    show ?case unfolding ns split proof(rule, rule, rule)
      fix t \<sigma>
      assume a:"sig_F s \<and> sig_F t \<and> linear_term t \<and> (s, t \<cdot> \<sigma>) \<in> par_rstep UR ^^ n"  
      then have sR:"sig_F s" and tR:"sig_F t" and lint:"linear_term t" and seq:"(s, t \<cdot> \<sigma>) \<in> par_rstep UR ^^ n" by auto
      { assume eq:"s = t\<cdot>\<sigma>"
        then have 0:"(s, t\<cdot>\<sigma>) \<in> (cstep R)^*" by auto
        from a have t:"sig_F t" and s:"sig_F s" by auto
        have 1:"sig_F_subst \<sigma> (vars_term t)" proof
          fix x
          assume xt:"x \<in> vars_term t"
          then have "t \<cdot> \<sigma>  \<unrhd> Var x \<cdot> \<sigma>" by (metis supteq_subst vars_term_supteq)
          from supteq_imp_funs_term_subset [OF this] s[unfolded eq] 
          show "sig_F (\<sigma> x)" unfolding sig_F_def aux by auto
        qed
        from par_rstep_refl relpow_refl_mono[OF _ le0 relpow_0_I] have 
          2:"\<forall> x \<in> vars_term t. (Var x\<cdot>\<sigma>, Var x\<cdot>\<sigma>) \<in> (par_rstep UR) ^^ n" by metis
        have "?G  n s t \<sigma>" by (rule exI[of _ \<sigma>], insert 0 1 2 sig_F_not_U[OF sR[unfolded eq]], auto)
      } note equal_terms = this
      show "?G n s t \<sigma>" proof (cases n)
        (* case 1: the sequence is empty *)
        case 0
        with a equal_terms show ?thesis by auto
      next
        (* case 2: the sequence is non-empty with length Suc m *)
        case (Suc m) note Suc_m = this
        from seq[unfolded Suc relpow_fun_conv] obtain ui where 
          ui:"ui 0 = s" "ui (Suc m) = t \<cdot> \<sigma>" "\<forall>i<Suc m. (ui i, ui (Suc i)) \<in> par_rstep UR" by blast
        show ?thesis proof(cases "\<exists> i < Suc m. \<exists> l r \<sigma>. ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR")
          (* case 2.1: the sequence contains no step at the root *)
          case False note no_root_step = this
          show ?thesis proof (cases "\<exists>x. s = Var x")
            (* case 2.1.1: s = t \<cdot> \<sigma> is a variable *)
            case True
            then obtain x where sx:"s = Var x" by blast
            {fix i
              have "i \<le>  Suc m \<Longrightarrow> ui i = Var x" proof(induct i, insert ui(1) sx, simp)
                case (Suc i)
                then have ix:"ui i = Var x" by auto
                from Suc have "i < Suc m" by auto
                with ix ui(3)[rule_format, OF this, unfolded par_rstep.simps[of "ui i"], unfolded ix] no_root_step 
                show "ui (Suc i) = Var x" by fastforce
              qed}
            from this[OF order_refl]  ui(2) sx have "s = t\<cdot>\<sigma>" by auto
            from equal_terms[OF this] show ?thesis by auto
          next
            (* case 2.1.2: s is not a variable *)
            case False note s_no_var = this 
            from  no_root_step ui(1) have "\<not> (\<exists> l r \<sigma>. s = l \<cdot> \<sigma> \<and> (ui (Suc 0)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR)" by auto
            with s_no_var ui(3)[rule_format, OF zero_less_Suc, unfolded ui(1) par_rstep.simps[of s]]
            obtain f ss where sf:"s = Fun f ss" by blast
            let ?k = "length ss"
            {fix i
              let ?ps = "\<lambda> ts i. \<forall>x<length ts.(ss ! x, ts ! x) \<in> par_rstep UR ^^ i"
              have "i \<le> Suc m \<Longrightarrow> \<exists> ts. ui i = Fun f ts \<and> ?ps ts i \<and> length ss = length ts" 
              proof(induct i)
                case 0
                from par_rstep_refl relpow_refl_mono[OF _ le0 relpow_0_I] have "?ps ss 0" by metis
                with ui(1)[unfolded sf] exI[of _ ss] show ?case by blast
              next
                case (Suc i)
                then have im:"i \<le> Suc m" "i < Suc m" by auto
                from Suc(1)[OF this(1)] obtain ts where ih:"ui i = Fun f ts" "?ps ts i" "?k = length ts" by blast
                from im no_root_step Suc have "\<not> (\<exists> l r \<sigma>. ui i = l \<cdot> \<sigma> \<and> (ui (Suc i)) = r \<cdot> \<sigma> \<and> (l, r) \<in> UR)" by blast
                with ih(1) ui(3)[rule_format, OF im(2), unfolded par_rstep.simps[of "ui i"]] s_no_var
                obtain ts' where x:"ui (Suc i) = Fun f ts' \<and> (\<forall>x<length ts'. (ts ! x, ts' ! x) \<in> par_rstep UR) \<and> length ts' = length ts" by force
                from conjunct1[OF conjunct2[OF this]] ih(2) have "?ps ts' (Suc i)" by (metis relpow_Suc_I x)
                with Suc ih(3) x show "\<exists>ts. ui (Suc i) = Fun f ts \<and> ?ps ts (Suc i) \<and> ?k = length ts" by force
              qed} note sequence_f_rooted = this
              (* some auxiliaries needed for both of the following cases *)
            from sequence_f_rooted[OF order_refl] ui(2) obtain tss where t\<sigma>:"t \<cdot> \<sigma> = Fun f tss" "length tss =?k" by auto
            from nth_mem supt.arg have ssj:"\<And> j. j < length ss \<Longrightarrow> s \<rhd> ss ! j" unfolding sf by fast
            from supt_size ssj have ms:"\<And> j. j < length ss \<Longrightarrow>((n,ss ! j), nt) \<in> measures [fst, size \<circ> snd]" unfolding ns sf by force
            show ?thesis proof (cases "\<exists> x. t = Var x")
              (* case 2.1.2.1: t is not a variable *)
              case False note t_no_var = this
              from t_no_var eval_term.elims[OF t\<sigma>(1)] t\<sigma>(2) term.inject(2)[of f tss] obtain ts where t:"t = Fun f ts""length ts =?k"
                by (metis length_map)
              with t\<sigma> have sub:"\<forall>x < ?k. tss ! x = ts ! x \<cdot> \<sigma>" by auto
              let ?\<theta>j_cond = "\<lambda> j \<theta>j. (ss ! j, (ts ! j)\<cdot>\<theta>j) \<in> (cstep R)^* \<and> sig_F_subst \<theta>j (vars_term (ts ! j)) \<and> 
            (\<forall> x \<in> vars_term (ts ! j). (Var x\<cdot>\<theta>j, Var x\<cdot>\<sigma>) \<in> (par_rstep UR) ^^ n) \<and> 
            (sig_F ((ts ! j) \<cdot>\<sigma>) \<longrightarrow> (ts ! j)\<cdot>\<theta>j = (ts ! j)\<cdot>\<sigma>) \<and> (non_LV \<longrightarrow> t_U_cond (ts ! j) \<theta>j \<sigma>)"
              let ?exj = "\<lambda> j. (\<exists> \<theta>j. ?\<theta>j_cond j \<theta>j)"
              have "\<forall>j<length ts. (?exj j)"
              proof(rule, rule)
                fix j
                assume j:"j < length ts"
                let ?tj = "ts ! j" and ?sj = "ss ! j"
                from nth_mem[OF j] supt.arg have ttj:"t \<rhd> ?tj" unfolding t by fast
                from j lint[unfolded t] have lin:"linear_term ?tj" by force
                from sR supteq_imp_funs_term_subset[OF supt_imp_supteq[OF ssj[OF j[unfolded t(2)]]]] 
                have sigs:"sig_F ?sj" unfolding sig_F_def by fast
                from tR supteq_imp_funs_term_subset[OF supt_imp_supteq[OF ttj]] 
                have sigt:"sig_F ?tj" unfolding sig_F_def by fast
                from sub sequence_f_rooted[OF order_refl] ui(2) term.inject(2)[of f tss] t(2) t\<sigma>(1) j
                have step:"(?sj, ?tj \<cdot> \<sigma>) \<in> par_rstep UR ^^ Suc m" by force
                from  ind[rule_format, OF ms[OF j[unfolded t(2)]], unfolded split, rule_format] sigs sigt lin step Suc 
                show "?exj j" by blast
              qed
              from this[unfolded choice_iff'] obtain \<theta>f where \<theta>cond:"\<forall>j<length ts. (?\<theta>j_cond j (\<theta>f j))" by fast
              let ?\<theta>s = "map \<theta>f [0..<length ts]" and ?vs = "map vars_term ts"
              from lint[unfolded t linear_term.simps(2)] have p:"is_partition ?vs" by auto
              let ?\<theta> = "fun_merge ?\<theta>s ?vs"  
              have xequiv:"\<And> j x . j < length ts \<Longrightarrow> x \<in> vars_term (ts ! j) \<Longrightarrow> ?\<theta> x = (\<theta>f j) x" unfolding length_upt
              proof-
                fix j x
                assume j:"j < length ts" and  x:"x \<in> vars_term (ts ! j)"
                with j have xt:"x \<in> vars_term t" unfolding t(1) by fastforce
                with fun_merge_part[OF p, unfolded length_map, OF j, unfolded nth_map[OF j], OF x, of ?\<theta>s, unfolded nth_map[OF j]
                    nth_map[of _ "[0..<length ts]", unfolded length_upt minus_nat.diff_0, OF j]
                    nth_upt[of 0 j, unfolded add_0, OF j] in_subst_restrict[OF x]]
                show "?\<theta> x = (\<theta>f j) x" unfolding in_subst_restrict[OF xt] by blast
              qed
              from term_subst_eq this have equiv:"\<And> j. j < length ts \<Longrightarrow> (ts ! j) \<cdot> ?\<theta> = (ts ! j) \<cdot> (\<theta>f j)" unfolding length_upt
              proof-
                fix j
                assume "j < length ts" 
                from term_subst_eq[of "ts ! j" ?\<theta> "\<theta>f j", OF xequiv[OF this]] show "(ts ! j) \<cdot> ?\<theta> = (ts ! j) \<cdot> (\<theta>f j)" by fast
              qed
              let ?\<theta>ts = "map (\<lambda> t. t\<cdot>?\<theta>) ts"
              from t(2) have len:"length ss = length ?\<theta>ts" unfolding length_map by auto
              have "\<forall>j<length ss. (ss ! j, ?\<theta>ts ! j) \<in> (cstep R)\<^sup>*"
              proof(rule,rule)
                fix j 
                assume j:"j < length ss"
                with t(2) have j:"j < length ts" by auto
                from \<theta>cond[rule_format, OF j] equiv[OF j] have "(ss ! j, ts ! j \<cdot> \<theta>f j) \<in> (cstep R)\<^sup>*" by blast
                with equiv[OF j] show "(ss ! j, ?\<theta>ts ! j) \<in> (cstep R)\<^sup>*" unfolding nth_map[OF j] by fastforce
              qed
              from args_steps_imp_steps[OF cstep_ctxt_closed len this]
              have 0:"(s, t\<cdot>?\<theta>) \<in> (cstep R)^*" unfolding sf t by force 
              have 12:"\<forall> x \<in> (vars_term t). (Var x\<cdot>?\<theta>, Var x\<cdot>\<sigma>) \<in> (par_rstep UR) ^^ n \<and> sig_F (?\<theta> x)"
              proof
                fix x
                assume xt:"x \<in> vars_term t"
                from var_imp_var_of_arg[OF this[unfolded t(1)]] obtain j where j:"j < length ts" "x \<in> vars_term (ts ! j)" by force
                from \<theta>cond[rule_format, OF j(1)] j(2) xequiv[OF j(1) j(2)] show "(Var x\<cdot>?\<theta>, Var x\<cdot>\<sigma>) \<in> (par_rstep UR) ^^ n \<and> sig_F (?\<theta> x)" by auto
              qed
              {assume tR:"sig_F (t \<cdot>\<sigma>)"
                { fix j 
                  assume j':"j < length ts"
                  with t\<sigma>(2) t(2) have j:"j < length tss" by auto
                  from tR[unfolded t\<sigma>] supteq_imp_funs_term_subset[OF supt_imp_supteq, OF supt.arg[OF nth_mem[OF j]]] have
                    "sig_F (tss ! j)" unfolding sig_F_def by fast
                  with \<theta>cond[rule_format, OF j'] sub[rule_format,OF j'[unfolded t(2)]]  equiv[OF j'] 
                  have "ts ! j \<cdot>?\<theta> = ts ! j \<cdot> \<sigma>" by presburger
                } 
                with nth_map_conv[OF refl, of ts] t(2) have "t\<cdot>?\<theta> = t\<cdot>\<sigma>" unfolding t(1) eval_term.simps(2) term.simps(2)
                  by (metis (poly_guards_query, lifting))
              } note 3 = this 
              from f_in_R_not_U_fun[of f] tR[unfolded sig_F_def t] t have 4:"t_U_cond t ?\<theta> \<sigma>" unfolding t_U_cond_def by force
              show ?thesis by (rule exI[of _ ?\<theta>], insert 0 12 3 4, auto)
            next
              (* case 2.1.2.2: t is a variable *)
              assume "\<exists>x. t = Var x"
              with t\<sigma> obtain x where x:"t = Var x""\<sigma> x = Fun f tss" by force 
              let ?xs = "dvars (length tss)"
              from distinct_vars[of "length tss"] have fresh:"distinct ?xs""length ?xs = length tss" by auto
              let ?\<tau> = "mk_subst Var (zip ?xs tss)"
              { fix j assume "j < length tss"
                with mk_subst_distinct[OF fresh(1)] fresh(2) have "?\<tau> (?xs ! j) = tss ! j" by auto
              } note \<tau>equiv = this
              with fresh(2) nth_map have 
                t\<sigma>':"t\<cdot>\<sigma> = Fun f (map ?\<tau> ?xs)" unfolding t\<sigma> term.inject(2)[of f tss] list_eq_iff_nth_eq length_map by simp
              let ?\<theta>j_cond = "\<lambda> j \<theta>j. (ss ! j, \<theta>j (?xs ! j)) \<in> (cstep R)^* \<and> sig_F_subst \<theta>j {?xs ! j} \<and> 
             (\<theta>j (?xs ! j), tss ! j) \<in> (par_rstep UR) ^^ n \<and> (sig_F (tss ! j) \<longrightarrow> \<theta>j (?xs ! j) = tss ! j) 
              \<and> (non_LV \<longrightarrow> t_U_cond (Var (?xs ! j)) \<theta>j ?\<tau>)"
              let ?exj = "\<lambda> j. (\<exists> \<theta>j. ?\<theta>j_cond j \<theta>j)" 
              { fix j 
                assume j:"j < length tss"
                let ?sj = "ss ! j"
                let ?x = "?xs ! j"
                from \<tau>equiv[OF j] sequence_f_rooted[OF order_refl, unfolded ui(2)] t\<sigma> term.inject(2)[of f tss] j have 
                  0:"(ss ! j,?\<tau> ?x) \<in> par_rstep UR ^^ Suc m" by simp
                have 1:"linear_term (Var ?x)" by simp
                from sR supteq_imp_funs_term_subset[OF supt_imp_supteq[OF ssj[OF j[unfolded t\<sigma>(2)]]]] 
                have 2:"sig_F ?sj""sig_F (Var ?x)" unfolding sig_F_def by auto
                from ind[rule_format, OF ms[OF j[unfolded t\<sigma>(2)]], unfolded split, rule_format, of "Var ?x" ?\<tau>] 0 1 2 have "?exj j" 
                  unfolding term.simps Ball_def singleton_iff simp_thms(41) eval_term.simps(1) Suc \<tau>equiv[OF j] by blast
              } 
              then have "\<forall> j < length tss. ?exj j" by auto
              from this[unfolded choice_iff'] obtain \<theta>f where \<theta>cond:"\<forall>j<length tss. (?\<theta>j_cond j (\<theta>f j))" by presburger
              let ?\<theta>s = "map \<theta>f [0..<length tss]" and ?vs = "map (\<lambda> x. {x}) ?xs"
              have p:"is_partition ?vs" unfolding is_partition_def length_map fresh(2) 
              proof(rule, rule, rule, rule)
                fix i j
                assume j:"j < length tss" and i:"i < j"
                then have i':"i < length tss" by auto
                from i fresh(1)[unfolded distinct_conv_nth, rule_format, unfolded fresh(2), OF j i'] have "?xs ! i \<noteq> ?xs ! j" by auto
                then show "map (\<lambda>x. {x}) ?xs ! i \<inter> map (\<lambda>x. {x}) ?xs ! j = {}" 
                  unfolding nth_map[of i ?xs, unfolded fresh(2), OF i'] nth_map[of j ?xs, unfolded fresh(2), OF j] by fast
              qed
              define \<theta>' where "\<theta>' = fun_merge ?\<theta>s ?vs"  
              have xequiv:"\<And> j. j < length tss \<Longrightarrow> \<theta>' (?xs ! j) = (\<theta>f j) (?xs ! j)"
              proof-
                fix j
                assume j:"j < length tss"
                from fun_merge_part[OF p, unfolded length_map fresh(2), OF j, unfolded nth_map[of _ ?xs, unfolded fresh(2), OF j] singleton_iff, of _ ?\<theta>s,
                    unfolded nth_map[of _ "[0..<length tss]", unfolded length_upt minus_nat.diff_0, OF j]] nth_upt[of 0 j, unfolded add_0, OF j]  
                show "\<theta>'(?xs ! j) = (\<theta>f j) (?xs ! j)" unfolding \<theta>'_def by auto
              qed
              let ?\<theta>ts = "map \<theta>' ?xs"
              from t\<sigma>(2) fresh(2) have len:"length ss = length ?\<theta>ts" unfolding length_map by auto
              have "\<forall>j<length ss. (ss ! j, ?\<theta>ts ! j) \<in> (cstep R)\<^sup>*"
              proof(rule,rule)
                fix j 
                assume "j < length ss"
                with t\<sigma>(2) have j:"j < length tss" by auto
                from \<theta>cond[rule_format, OF j, unfolded xequiv[OF j, symmetric]]
                show "(ss ! j, ?\<theta>ts ! j) \<in> (cstep R)\<^sup>*" unfolding  nth_map[of j ?xs, unfolded fresh(2), OF j]  by blast
              qed
              from args_steps_imp_steps[OF cstep_ctxt_closed len this]
              have 0:"(s, Fun f ?\<theta>ts) \<in> (cstep R)^*" unfolding sf t by force  
              let ?\<theta> = "subst x (Fun f ?\<theta>ts)"
              have z:"Var x \<cdot> ?\<theta> =  Fun f ?\<theta>ts" by auto
              from 0 have 0:"(s, Var x \<cdot> ?\<theta>) \<in> (cstep R)^*" by fastforce
              { fix j
                assume j:"j < length tss"
                with fresh(2)  have j':"j < length ?xs" by auto
                from \<theta>cond[rule_format, OF j] xequiv[OF j] 
                have "(?\<theta>ts ! j, tss ! j)  \<in> (par_rstep UR) ^^ n \<and> sig_F (?\<theta>ts ! j)" unfolding  nth_map[OF j'] by simp
              } note aux = this
              then have "\<forall> j < length tss.(?\<theta>ts ! j, tss ! j)  \<in> (par_rstep UR) ^^ n" by auto
              with args_par_rstep_pow_imp_par_rstep_pow[of ?\<theta>ts "map ?\<tau> ?xs", unfolded length_map fresh(2)]
              have 1:"(Var x\<cdot>?\<theta>, Var x\<cdot>\<sigma>) \<in> (par_rstep UR) ^^ n" unfolding z t\<sigma>'[unfolded x]
                by (metis term.inject(2) t\<sigma>' t\<sigma>(1)) 
              from a[unfolded sf sig_F_def] term.simps(16) have fR:"{f} \<subseteq> F " by fast
              from aux len t\<sigma>(2) have aux':"\<forall> j < length ?\<theta>ts.  sig_F (?\<theta>ts ! j)" by presburger
              from this[unfolded all_set_conv_all_nth[symmetric, of ?\<theta>ts sig_F]] fR
                sig_F_def have 2:"sig_F (Var x \<cdot> ?\<theta>)" unfolding subst_simps(2) z by auto
              {
                assume tR:"sig_F (\<sigma> x)"
                { fix j 
                  assume j:"j < length tss"
                  from tR[unfolded x[symmetric] t\<sigma>, unfolded t\<sigma>[unfolded x, unfolded eval_term.simps(1)]] 
                    supteq_imp_funs_term_subset[OF supt_imp_supteq, OF supt.arg[OF nth_mem[OF j]]] have
                    "sig_F (tss ! j)" unfolding sig_F_def by fast
                  with \<theta>cond[rule_format, OF j, unfolded \<tau>equiv[OF j]] xequiv[OF j] have "\<theta>' (?xs ! j) = tss ! j" by auto
                } 
                with fresh(2) have "(Fun f (map \<theta>' ?xs)) = t\<cdot>\<sigma>" 
                  unfolding t\<sigma>(1) eval_term.simps(2) term.simps(2) by (metis map_nth_eq_conv)
                with x have "(Fun f (map \<theta>' ?xs)) = Var x \<cdot>\<sigma>" by auto
              } note 3 = this 
              from f_in_R_not_U_fun[of f] x fR have 4:"t_U_cond (Var x) ?\<theta> \<sigma>" unfolding sig_F_def t_U_cond_def by force
              show ?thesis unfolding x term.simps(17) by (rule exI[of _ ?\<theta>], insert 0 1 2 3 4, simp)
            qed
          qed
        next
          (* case 2.2: the sequence contains a root step *)
          case True note there_is_root_step = this
          from all_ctxt_closed_relpow[OF all_ctxt_closed_par_rstep] have acc:"\<And> i. all_ctxt_closed UNIV (par_rstep UR ^^ i)" by auto
          from relpow_refl_mono[of "par_rstep UR"] par_rstep_refl have
            par_rstep_mono:"\<And> m n a b. m \<le> n \<Longrightarrow> (a, b) \<in> par_rstep UR ^^ m \<Longrightarrow> (a, b) \<in> par_rstep UR ^^ n" by blast
          from Lemma_16[OF ui(3) there_is_root_step sR[unfolded ui(1)[symmetric]]] 
          have "\<exists> \<rho> k. \<rho> \<in> R \<and> (complete_R_step_simulation ui (Suc m) \<rho> \<or> partial_R_step_simulation ui (Suc m) \<rho> k)" by auto
          then obtain \<rho> k where sim:"\<rho> \<in> R"
            "complete_R_step_simulation ui (Suc m) \<rho> \<or> partial_R_step_simulation ui (Suc m) \<rho> k" (is "?complete \<or> ?partial") by blast
          obtain l rr cs where rho:"\<rho> = ((l,rr), cs)" by (cases \<rho>, auto)
              (* some abbreviations *)
          let ?ustep = "\<lambda> s t k \<sigma> . (s, t) \<in> rstep_r_p_s UR (lhs_n \<rho> k, rhs_n \<rho> k) [] \<sigma>"
          let ?usteps' = "\<lambda> ji. (\<forall>x. \<exists>\<sigma>. 0 \<le> x \<and> x \<le> length cs \<longrightarrow> ?ustep (ui (ji x)) (ui (Suc (ji x))) x \<sigma>)"
          let ?usteps = "\<lambda> cs \<sigma>i ji. (\<forall>x. 0 \<le> x \<and> x \<le> length cs \<longrightarrow> ?ustep (ui (ji x)) (ui (Suc (ji x))) x (\<sigma>i x))"
          let ?isteps = "\<lambda> cs ji ni. \<forall>k. 0 \<le> k \<and> k < length cs \<longrightarrow> (ui (Suc (ji k)), ui (ji (Suc k))) \<in> par_urstep_below_root ^^ ni k"
          let ?domi = "\<lambda>i. case i of 0 \<Rightarrow> vars_term l | Suc j \<Rightarrow> vars_term (ti \<rho> j) \<union> XY \<rho> j"
          let ?result = "\<lambda> m0 \<sigma>1 \<theta>1. (s, l \<cdot> \<theta>1) \<in> (cstep R)\<^sup>* \<and> sig_F_subst \<theta>1 (vars_term l) \<and>
             (\<forall>x\<in>vars_term l \<union> set (Z \<rho> 0). (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0) \<and> (sig_F (l \<cdot> \<sigma>1) \<longrightarrow> l \<cdot> \<theta>1 = l \<cdot> \<sigma>1) \<and>
              sig_F_subst \<theta>1 (?domi 0) \<and> (non_LV \<longrightarrow> t_U_cond l \<theta>1 \<sigma>1)"
            (* \<theta>1 can be obtained independent of the below case distinction *) 
          { fix m0 r \<sigma>1
            assume i:"m0 < Suc m" "ui m0 = l \<cdot> \<sigma>1" "ui (Suc m0) = (rhs_n \<rho> 0) \<cdot> \<sigma>1" 
            from ui(3) i(1) have "\<forall> i' < m0. (ui i', ui (Suc i')) \<in> par_rstep UR" by auto
            with ui(1) i(2) have 1:"(s, l \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0" unfolding  relpow_fun_conv by blast
            from sim(1) rho rules_def have "\<exists>r'. (l,r') \<in> rules \<rho>" unfolding rules_def by force
            then obtain r' where " (l,r') \<in> rules \<rho>" by blast
            with ll[unfolded left_linear_trs_def, rule_format, of "(l,r')"]  sim(1) have 2:"linear_term l" 
              unfolding left_linear_trs_def rho UR_def by blast
            from sig_F_l[OF sim(1)] have 3:"sig_F l" unfolding rho by force
            from i(1) ns Suc_m have "((m0, s), nt) \<in> measures [fst, size \<circ> snd]" unfolding ns by auto
            from ind[rule_format, OF this, unfolded split, rule_format, of l \<sigma>1] 1 2 3 sR obtain \<theta>1 where
              theta1:"(s, l \<cdot> \<theta>1) \<in> (cstep R)\<^sup>*" "sig_F_subst \<theta>1 (vars_term l)" "(\<forall>x\<in>vars_term l. (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0)" 
              "(sig_F (l \<cdot> \<sigma>1) \<longrightarrow> l \<cdot> \<theta>1 = l \<cdot> \<sigma>1)" "non_LV \<longrightarrow> t_U_cond l \<theta>1 \<sigma>1"
              by blast
            let ?\<theta>1 = "\<lambda>x. if x \<in> vars_term l then \<theta>1 x else Var x \<cdot> \<sigma>1" 
            have l\<theta>:"\<forall>x\<in>vars_term l. ?\<theta>1 x = \<theta>1 x" by fastforce
            from theta1(2) l_vars_X0_vars[OF sim(1)] sim(2) rho have substR1:"sig_F_subst ?\<theta>1 (?domi 0)" by auto 
            from theta1(1) l\<theta>[unfolded term_subst_eq_conv[symmetric]] have 1:"(s, l \<cdot> ?\<theta>1) \<in> (cstep R)\<^sup>*" by simp
            from theta1(2) l\<theta> have 2:"sig_F_subst ?\<theta>1 (vars_term l)" by force
            { fix x assume "x \<in> vars_term l \<union> set (Z \<rho> 0)" 
              with theta1(3) l\<theta> par_rstep_mono[OF le0] have " (Var x \<cdot> ?\<theta>1, Var x \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0" by auto
            } note 4 = this 
            { assume nlv:non_LV 
              from rho lhs_n.simps(1) have "lhs_n \<rho> 0 = l" by force 
              with nlv[unfolded non_LV_def UR_def] rules_def sim(1)[unfolded rho] have "is_Fun l" by fastforce
              then obtain f zs where "l = Fun f zs" by auto
              with  f_in_R_not_U_fun[of f] 3[unfolded sig_F_def] have  "t_U_cond l ?\<theta>1 \<sigma>1" unfolding t_U_cond_def by force
            } note 5 = this
            note facts = theta1 l\<theta> l\<theta>[unfolded term_subst_eq_conv[symmetric]] 4 5
            have "\<exists> \<theta>1. ?result m0 \<sigma>1 \<theta>1" by (rule exI[of _ ?\<theta>1], insert facts, simp)
          } note prefix = this
          show ?thesis proof(cases "?complete")
            (* case 2.2.2.1: we consider a complete R-step simulation subsequence *)
            case True 
            note complete = this 
            let ?theta_prop_with = "\<lambda> \<sigma> m s t \<theta>' i. (s, t \<cdot> \<theta>') \<in> (cstep R)\<^sup>* \<and> (sig_F_subst \<theta>' (vars_term t \<inter> ?domi i)) \<and>
                  (\<forall>x\<in>vars_term t. (Var x \<cdot> \<theta>', Var x \<cdot> \<sigma>) \<in> par_rstep UR ^^ m)" 
            let ?theta_prop_with' = "\<lambda> \<sigma> m s t \<theta>' i. (s, t \<cdot> \<theta>') \<in> (cstep R)\<^sup>* \<and> (sig_F_subst \<theta>' (vars_term t)) \<and>
                  (\<forall>x\<in>vars_term t. (Var x \<cdot> \<theta>', Var x \<cdot> \<sigma>) \<in> par_rstep UR ^^ m) \<and> (sig_F (t \<cdot> \<sigma>) \<longrightarrow> t \<cdot> \<theta>' = t \<cdot> \<sigma>) \<and> t_U_cond t \<theta>' \<sigma>"
            have up2r:"\<exists>\<theta> j0. (s, rr \<cdot> \<theta>) \<in> (cstep R)\<^sup>+ \<and> sig_F (rr \<cdot> \<theta>) \<and> (rr \<cdot> \<theta>, ui (Suc j0)) \<in> par_rstep UR ^^ j0 \<and> j0 \<le> m"
            proof (cases "length cs = 0")  
              case True (* unconditional rule *)
              with complete[unfolded complete_R_step_simulation_def rho snd_conv] rho obtain j0 \<sigma>0 where 
                j0:"j0 < Suc m" "(ui j0, ui (Suc j0)) \<in> rstep_r_p_s UR (l, rr) [] \<sigma>0" by auto
              then have lr:"ui j0 = l \<cdot> \<sigma>0" "ui (Suc j0) = rr \<cdot> \<sigma>0" unfolding rstep_r_p_s_def by (simp,simp)
              from prefix[OF j0(1) lr(1), unfolded rho] rhs_n.simps True lr(2) obtain \<theta>1 where 
                cs:"(s, l \<cdot> \<theta>1) \<in> (cstep R)\<^sup>*" " sig_F_subst \<theta>1 (vars_term l)" "\<forall>x\<in>vars_term l. (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>0) \<in> par_rstep UR ^^ j0" by auto
              have "(l\<cdot>\<theta>1, rr\<cdot>\<theta>1) \<in> (cstep_n R (Suc 0))"
                by (rule cstep_n_SucI[of l rr "[]" _ _ _ _ Hole], insert True sim(1) rho, auto)
              from this cstep_iff rtrancl_into_trancl1[OF cs(1), of "rr\<cdot>\<theta>1"] have 1:"(s, rr \<cdot> \<theta>1) \<in> (cstep R)\<^sup>+" by fast
              from type3[unfolded type3_def, rule_format, OF sim(1)] True 
              have vs:"vars_term rr \<subseteq> vars_term l" unfolding vars_trs_def rho by auto
              with cs(3) have "\<forall>x\<in>vars_term rr. (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>0) \<in> par_rstep UR ^^ j0" by auto
              with all_ctxt_closed_subst_step[OF acc] lr(2) have 2:"(rr \<cdot> \<theta>1, ui (Suc j0)) \<in> par_rstep UR ^^ j0" by simp
              from cs(2) vs have "(\<forall>x\<in>vars_term rr. sig_F (\<theta>1 x))" by auto
              with sim(1) funs_crule_def[of \<rho>, unfolded funs_rule_def] F have 3:"sig_F (rr\<cdot>\<theta>1)" 
                unfolding sig_F_def funs_term_subst funs_ctrs_def rho by auto
              show ?thesis by (rule exI[of _ \<theta>1], insert 1 2 3 j0(1), auto)
            next
              case False (* conditional rule *)
              let ?sum = "\<lambda> cs j ni. j 0 + sum_list (map (Suc \<circ> ni) [0..< (length cs)]) = j (length (snd \<rho>))"
              let ?ji = "\<lambda> cs ji. (\<forall>x. 0 \<le> x \<and> x \<le> length cs \<longrightarrow> ji x < Suc m)" 
              let ?ustep' = "\<lambda> j \<sigma>i i. j i < Suc m \<and> (ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i)"
              let ?usteps' = "\<lambda> j \<sigma>i. (\<forall>i. 0 \<le> i \<and> i \<le> length cs \<longrightarrow> ?ustep' j \<sigma>i i)"
              from complete[unfolded complete_R_step_simulation_def] obtain ji ni \<sigma>i where 
                dec:"?usteps' ji \<sigma>i" "?isteps cs ji ni" "?sum cs ji ni" unfolding rho by force
              then have dec:"?ji cs ji" "?usteps cs \<sigma>i ji" "?isteps cs ji ni" "?sum cs ji ni" by (blast, auto)
              define m0 n0 \<sigma>1 where "m0 = ji 0" and "n0 = ni 0" and "\<sigma>1 = \<sigma>i 0"
              from dec(2)[rule_format, of 0] have step:"(ui m0, ui (Suc m0)) \<in> rstep_r_p_s UR (lhs_n \<rho> 0, rhs_n \<rho> 0) [] \<sigma>1" unfolding m0_def \<sigma>1_def by auto
              from this[unfolded rstep_r_p_s_def] have uim0:"ui m0 = l \<cdot> \<sigma>1" "ui (Suc m0) = (rhs_n \<rho> 0) \<cdot> \<sigma>1" unfolding rho lhs_n.simps(1) by (force,force)
              from uim0 False rho have u1:"ui (Suc m0) = (U \<rho> 0)\<langle>si \<rho> 0\<rangle> \<cdot> \<sigma>1" by auto
              from  U_cond[OF sim(1), of 0] False rho obtain U0 where U0:"U_fun \<rho> 0 U0" by auto
              from dec(1)[rule_format, of 0] have m0m:"m0 < Suc m" unfolding m0_def by simp
              from prefix[OF this uim0] obtain \<theta>1 where theta1:"?result m0 \<sigma>1 \<theta>1" by presburger
              from dctrs[unfolded dctrs_def, rule_format, OF sim(1), of 0] False rho l_vars_X0_vars[OF sim(1)] sim 
              have vs0:"vars_term (si \<rho> 0) \<subseteq> vars_term l" by simp
              with theta1 have "\<And> x. x \<in> vars_term (si \<rho> 0) \<Longrightarrow>  (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0" by auto
              with all_ctxt_closed_subst_step[OF acc] have sstep:"(si \<rho> 0 \<cdot> \<theta>1, si \<rho> 0 \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0" by fastforce
              from theta1 have  substR1:"sig_F_subst \<theta>1 (?domi 0)" by auto
              from theta1 have theta1:"(s, l \<cdot> \<theta>1) \<in> (cstep R)\<^sup>*" "sig_F_subst \<theta>1 (vars_term l)"
                "(\<forall>x\<in> set (Z \<rho> 0). (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0)" "(sig_F (l \<cdot> \<sigma>1) \<longrightarrow> l \<cdot> \<theta>1 = l \<cdot> \<sigma>1)" by (fast+)
              from dec(1) rho have j_last:"ji (length (snd \<rho>)) < Suc m" by auto
                  (* now the crucial internal lemma *)
              let ?mi = "\<lambda> i. ji 0 + sum_list (map ni [0..< i])"
              let ?\<theta>cond = "\<lambda> \<theta>s cs cs'. (length \<theta>s = Suc (length cs) \<and> (\<theta>s ! 0 = \<theta>1) \<and>(\<forall> i < Suc (length cs). sig_F_subst (\<theta>s ! i) (?domi i)) \<and>
                     (s, l \<cdot> (\<theta>s ! 0)) \<in> (cstep R)\<^sup>* \<and> 
                     (\<forall> i < length cs. (si \<rho> i \<cdot> (\<theta>s ! i), ti \<rho> i \<cdot> (\<theta>s ! (Suc i))) \<in> (cstep R)\<^sup>*) \<and> 
                     (\<forall> i < length cs. \<forall> j < length (Z \<rho> i) . (((\<theta>s ! i) (Z \<rho> i ! j), (\<theta>s ! Suc i) (Z \<rho> i ! j)) \<in> (cstep R)^*) \<and>
                                                              ((\<theta>s ! Suc i) (Z \<rho> i ! j), (\<sigma>i (Suc i))  (Z \<rho> i ! j)) \<in> par_rstep UR ^^ ?mi (Suc i)) \<and>
                     (\<forall> i < length cs. (\<forall>x\<in>vars_term (ti \<rho> i). ((\<theta>s ! Suc i) x, (\<sigma>i (Suc i)) x) \<in> par_rstep UR ^^ ?mi (Suc i))))"
              let ?theta_prop = "\<lambda> s t \<theta>' i. ?theta_prop_with (\<sigma>i i) (?mi i) s t \<theta>' i"
              { fix cs cs'
                assume "\<rho> = ((l,rr),cs @ cs')" "?ji cs ji" "?usteps cs \<sigma>i ji" "?isteps cs ji ni"
                  "?sum (cs @ cs') ji ni"
                then have "\<exists> \<theta>s. ?\<theta>cond \<theta>s cs cs'"
                proof(induct "length cs" arbitrary:cs cs')
                  case 0
                  from 0(1) 0(2) False rho have l:"length cs' > 0" by simp
                  show ?case by (rule exI[of _ "[\<theta>1]"], insert 0 l theta1, simp)
                next
                  case (Suc k)
                  note Suck=this
                  note U_cond = U_cond[OF sim(1), unfolded Suc(3) snd_conv]
                  note inR = sim(1) and rho = Suc(3)
                  from  Suc(2) Suc(3) have kl:"k < length cs" by auto
                  then have kl':"k < length (cs @ cs')" by auto
                  from U_cond[OF kl'] rho obtain Uk where Uk:"U_fun \<rho> k Uk" unfolding Suc(3) snd_conv by blast
                  let ?cs = "butlast cs" and ?cs' = "last cs # cs'"
                  from append_butlast_last_id[of cs] Suc(2) have app:"cs @ cs' = ?cs @ ?cs'" by fastforce
                  from length_butlast[of cs] Suc(2) have 0:"length ?cs = k" by auto
                  from Suc(3) app have 2:"\<rho> = ((l,rr), ?cs @ ?cs')" unfolding rho by force
                  from Suc(4) have 3:"?ji ?cs ji" by force
                  from Suc(5) have 4:"?usteps ?cs \<sigma>i ji" by force
                  from Suc(6) have 5:"?isteps ?cs ji ni" by force
                  from Suc(7) app have 6:"?sum (?cs @ ?cs') ji ni" by simp
                  from Suc(1)[OF 0[symmetric] 2 3 4 5 6] obtain \<theta>s' where \<theta>s':"?\<theta>cond \<theta>s' ?cs ?cs'" by auto
                  let ?k = "Suc k" 
                  let ?\<theta>k = "\<lambda> x. case k of 0 \<Rightarrow>  (\<theta>s' ! k) x | Suc m \<Rightarrow> if x \<in> ?domi k \<union> set (Z \<rho> m) then (\<theta>s' ! k) x else (\<sigma>i k) x"
                  note \<theta>1=conjunct1[OF conjunct2[OF \<theta>s']]
                  have thetak:"\<And>t m. k = Suc m \<Longrightarrow> vars_term t \<subseteq> ?domi k \<union> set (Z \<rho> m) \<Longrightarrow> t \<cdot> (\<theta>s' ! k) = t \<cdot> ?\<theta>k" 
                    by (cases k, insert term_subst_eq[of _ "\<theta>s' ! k" ?\<theta>k] nat.case(2), fastforce+)
                  from vars_si_subset_ti_XY[OF inR] rho Suc(2) have 
                    vs:"\<And>m. k = Suc m \<Longrightarrow> vars_term (si \<rho> k) \<subseteq> vars_term (ti \<rho> m) \<union> XY \<rho> m" by simp
                  from \<theta>s'  0 have vt:"\<And>m. k = Suc m \<Longrightarrow>\<forall>x\<in>vars_term (ti \<rho> m). (?\<theta>k x, \<sigma>i k x) \<in> par_rstep UR ^^ ?mi k" by auto
                  from \<theta>s'  0 have vz':"\<And>m. k = Suc m \<Longrightarrow> \<forall>j < length (Z \<rho> m). (?\<theta>k (Z \<rho> m ! j), \<sigma>i k (Z \<rho> m ! j)) \<in> par_rstep UR ^^ ?mi k" by auto
                  then have vz:"\<And>m. k = Suc m \<Longrightarrow> \<forall>z \<in> set (Z \<rho> m). (?\<theta>k z, \<sigma>i k z) \<in> par_rstep UR ^^ ?mi k" unfolding all_set_conv_all_nth by blast
                  from X_Y_imp_Z[OF inR] Suc(2) Suc(3) rho have xyz:"\<And>m. k = Suc m \<Longrightarrow> XY \<rho> m \<subseteq> set (Z \<rho> m)" by force
                  have si_k_steps:"((si \<rho> k) \<cdot> ?\<theta>k,(si \<rho> k) \<cdot> (\<sigma>i k)) \<in> par_rstep UR ^^ ?mi k"  (* #2 *)
                  proof (cases k)
                    case 0
                    from \<theta>1 sstep show ?thesis unfolding \<sigma>1_def 0 nat.case m0_def by simp
                  next
                    case (Suc m) note k = this
                    let  ?\<sigma>k = "\<sigma>i (Suc m)"
                    from vs[OF k] vt[OF k] vz[OF k] 0 xyz[OF k] have "\<forall>x\<in>vars_term (si \<rho> k). (?\<theta>k x, \<sigma>i k x) \<in> par_rstep UR ^^ ?mi k" unfolding k by fast
                    from this all_ctxt_closed_subst_step[OF acc] show ?thesis by fast
                  qed
                  from kl Suc(5)[rule_format, of k] have x:"(ui (ji k), ui (Suc (ji k))) \<in> rstep_r_p_s UR (lhs_n \<rho> k, rhs_n \<rho> k) [] (\<sigma>i k)" by auto
                  from rhs_n.simps[of _ "cs @ cs'" k] Suc(2) have "rhs_n \<rho> k = (U \<rho> k)\<langle>si \<rho> k\<rangle>" unfolding rho by simp 
                  with x[unfolded rho ] rho rstep_r_p_s_def Suc(2) have 
                    u1:"ui (Suc (ji k)) = (U \<rho> k)\<langle>si \<rho> k\<rangle> \<cdot> (\<sigma>i k)"  by force
                  from Suc(2) Suc(5)[rule_format, of "?k"] have 
                    "(ui (ji ?k), ui (Suc (ji ?k))) \<in> rstep_r_p_s UR (lhs_n \<rho> ?k, rhs_n \<rho> ?k) [] (\<sigma>i ?k)" by force
                  from this[unfolded rho lhs_n.simps(2)] rstep_r_p_s_def rho have
                    u2:" ui (ji ?k) = (U \<rho> k)\<langle>ti \<rho> k\<rangle> \<cdot> (\<sigma>i ?k)" by force
                  from u1 u2 kl Suc(6)[rule_format, of k] have 
                    u:"((U \<rho> k)\<langle>si \<rho> k\<rangle> \<cdot> (\<sigma>i k),(U \<rho> k)\<langle>ti \<rho> k\<rangle> \<cdot> (\<sigma>i ?k)) \<in> par_urstep_below_root ^^ ni k" by auto
                  from this[unfolded Uk intp_actxt.simps append_Nil] par_urstep_below_root_def par_rstep_pow_imp_args_par_rstep_pow
                  have si_k_steps':"(si \<rho> k \<cdot> (\<sigma>i k), ti \<rho> k \<cdot> (\<sigma>i ?k)) \<in> par_rstep UR ^^ ni k" by auto 
                  from kl  have sum:"?mi ?k = ?mi k + ni k" by simp
                  from si_k_steps si_k_steps' relpow_add have 
                    step:"((si \<rho> k) \<cdot> ?\<theta>k,  ti \<rho> k \<cdot> (\<sigma>i ?k)) \<in> par_rstep UR ^^ ?mi ?k" unfolding sum by fast (* #4 *)
                  from sig_F_si[OF inR] kl rho have sig_F:"sig_F (si \<rho> k)" by auto 
                  note sigRs = conjunct1[OF conjunct2[OF conjunct2[OF \<theta>s']]]
                  from vs have  1:"sig_F ((si \<rho> k) \<cdot> ?\<theta>k)" proof (cases k)
                    case 0
                    from  vs0 theta1(2) sig_F show ?thesis unfolding 0 nat.case \<theta>1 sig_F_def funs_term_subst by blast
                  next
                    case (Suc m)
                    from vs[OF Suc] have vs:"vars_term (si \<rho> k) \<subseteq> ?domi k" unfolding Suc by simp
                    from term_subst_eq[of _ "\<theta>s' ! k" ?\<theta>k] have thetak:"\<And>t. vars_term t \<subseteq> ?domi k \<union> set (Z \<rho> m) \<Longrightarrow> t \<cdot> (\<theta>s' ! k) = t \<cdot> ?\<theta>k" 
                      unfolding Suc nat.case(2) by fastforce
                    with sigRs[ rule_format, of k] vs have eq:"si \<rho> k \<cdot> \<theta>s' ! Suc m = si \<rho> (Suc m) \<cdot> ?\<theta>k" unfolding 0 Suc by blast 
                    from sigRs[ rule_format, of k] vs
                    have "\<And>x. x \<in> vars_term (si \<rho> k) \<Longrightarrow> sig_F ((\<theta>s' ! Suc m) x)" unfolding 0 Suc by blast
                    with vs sig_F show ?thesis unfolding sig_F_def funs_term_subst 0 Suc nat.case(2) by fastforce
                  qed 
                  from linear_term_ti[OF ll inR, unfolded rho, simplified] kl rho have 2:"linear_term (ti \<rho> k)" by simp
                  from sig_F_ti[OF inR] kl rho have 3:"sig_F (ti \<rho> k)"  by auto 
                  have "\<And>j. Suc 0 \<le> j \<and> j < Suc k \<Longrightarrow> ni j \<le> (Suc \<circ> ni) j" by force
                  have "sum_list (map ni [0..<Suc k]) < sum_list (map (Suc \<circ> ni) [0..<Suc k])" by (induct k, auto)
                  with Suc(7) have m':"?mi ?k < ji (length (snd \<rho>))" unfolding length_append Suc(2)[symmetric]
                      upt_add_eq_append[OF le0] map_append sum_list_append by linarith
                  with j_last have m:"((?mi ?k, si \<rho> k \<cdot> ?\<theta>k), nt) \<in> measures [fst, size \<circ> snd]" unfolding ns Suc_m by auto
                  from ind[rule_format, OF m, unfolded split, rule_format] 1 2 3 step obtain \<theta>' where
                    \<theta>':"?theta_prop (si \<rho> k \<cdot> ?\<theta>k) (ti \<rho> k) \<theta>' ?k" by blast
                  from X_Y_imp_Z[OF inR]  Suc(2) rho have xyz':"XY \<rho> k \<subseteq> set (Z \<rho> k)" by force
                      (* ... the case for Zs ... *) 
                  { fix j
                    assume jl:"j < length (Z \<rho> k)" 
                    let ?z = "(Z \<rho> k) ! j" 
                    from set_conv_nth jl have zZ:"?z \<in> set (Z \<rho> k)" by auto
                    from u[unfolded Uk intp_actxt.simps append_Nil eval_term.simps(2)] par_rstep_pow_imp_args_par_rstep_pow
                    have "(\<forall>i< length (Z \<rho> k). (map (\<sigma>i k) (Z \<rho> k) ! i, map (\<sigma>i ?k) (Z \<rho> k) ! i) \<in> par_rstep UR ^^ ni k)" by auto
                    from this[rule_format, OF jl] nth_map[of j] jl have z_step:"((\<sigma>i k) ?z, \<sigma>i ?k ?z) \<in> par_rstep UR ^^ ni k" by force
                    from m' j_last have m:"((?mi ?k, ?\<theta>k ?z), nt) \<in> measures [fst, size \<circ> snd]" unfolding ns Suc_m by auto
                    have  "\<exists> \<theta>z. ?theta_prop (?\<theta>k ?z) (Var ?z) \<theta>z ?k" proof (cases k)
                      case 0
                      from theta1(3)[rule_format, of ?z] jl have i:"(Var ?z \<cdot> \<theta>1, Var ?z \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0"
                        unfolding set_conv_nth 0 by blast
                      from Suc(6)[rule_format, of 0] Suc(2) 
                      have m0_step:"((U \<rho> 0)\<langle>si \<rho> 0\<rangle> \<cdot> \<sigma>1, (U \<rho> 0)\<langle>ti \<rho> 0\<rangle> \<cdot> (\<sigma>i (Suc 0))) \<in> par_urstep_below_root ^^ n0" 
                        unfolding 0 n0_def m0_def  u1[unfolded m0_def 0] u2[unfolded 0] \<sigma>1_def by fastforce
                      from m0_step[unfolded U0 intp_actxt.simps(2)] iffD1[OF par_rstep_pow_imp_args_par_rstep_pow] jl
                      have "(Var ?z \<cdot> \<sigma>1, Var ?z \<cdot> (\<sigma>i (Suc 0))) \<in> par_rstep UR ^^ n0" unfolding 0 by fastforce
                      with i have steps:"(Var ?z \<cdot> \<theta>1, Var ?z \<cdot> (\<sigma>i (Suc 0))) \<in> par_rstep UR ^^ (m0 + n0)"  unfolding relpow_add by blast (* #5 *)
                      show ?thesis  proof (cases "?z \<in> XY \<rho> 0" )
                        case True
                        with l_vars_X0_vars[OF inR] Suc(2) rho have "?z \<in> vars_term l" unfolding 0 by force
                        with jl theta1(2) have 1:"sig_F (\<theta>1 ?z)" unfolding sig_F_def funs_term_subst by force
                        have 2:"linear_term (Var ?z)" and 3:"sig_F (Var ?z)" unfolding sig_F_def by auto
                        have m0n0:"?mi (Suc 0) = m0 + n0" unfolding Suc(2)[symmetric] m0_def n0_def by simp
                        note m0 = m[unfolded 0 nat.case \<theta>1 m0n0]
                        from ind[rule_format, OF m, unfolded split, rule_format, of "Var ?z" "\<sigma>i (Suc 0)"] steps 1 2 3 
                        show ?thesis unfolding 0 nat.case m0n0 \<theta>1 by force (* #7 *)
                      next
                        case False 
                        from Z_ti_disjoint[OF inR _ ll, of 0] kl rho jl have "vars_term (ti \<rho> 0) \<inter> set (Z \<rho> 0) = {}" unfolding 0 by force
                        from this[unfolded set_conv_nth] jl have ti:"?z \<notin> vars_term (ti \<rho> 0)" unfolding 0 by blast
                        with False have ti:"Z \<rho> 0 ! j \<notin>  (vars_term (ti \<rho> 0) \<union> (X_vars \<rho> 0 \<inter> Y_vars \<rho> 0))" unfolding 0 by blast
                        show ?thesis unfolding 0 nat.case by (rule exI[of _ ?\<theta>k, unfolded 0 nat.case], insert steps[unfolded 0 m0_def n0_def] ti \<theta>1, auto)
                      qed 
                    next
                      case (Suc m) note k = this
                      with kl  have ml:"m < length cs + length cs'" by auto
                      show ?thesis proof(cases "?z \<in> vars_term (ti \<rho> m) \<union> XY \<rho> m")
                        case True
                        with xyz[OF Suc] vz[OF k] vt[OF k] have "(?\<theta>k ?z, \<sigma>i k ?z) \<in> par_rstep UR ^^ ?mi k" by blast
                        with z_step relpow_add have step:"(?\<theta>k ?z, \<sigma>i ?k ?z) \<in> par_rstep UR ^^ ?mi ?k" unfolding sum by fast (* #5 *)
                        have sig_F:"sig_F (Var ?z)" unfolding sig_F_def by simp
                        from U_cond[unfolded rho snd_conv length_append, OF ml] ml rho obtain Um where 
                          Um:"U_fun \<rho> m Um" unfolding k by blast
                        from True xyz have "?z \<in> vars_term (U \<rho> m)\<langle>ti \<rho> m\<rangle>" unfolding k Um intp_actxt.simps by auto
                        with sig_F sigRs[rule_format, of k] xyz True
                        have 1:"sig_F (?\<theta>k ?z)" unfolding sig_F_def funs_term_subst 0 k by simp
                        from m' j_last have m:"((?mi ?k, ?\<theta>k ?z), nt) \<in> measures [fst, size \<circ> snd]" unfolding ns Suc_m by auto
                        from ind[rule_format, OF m, unfolded split, rule_format, of "Var ?z" "\<sigma>i ?k"] 1 sig_F step show ?thesis by auto
                      next
                        case False note dom = this
                        with XYi_subset_ti_XY[OF inR, of m] k rho Suck(2) have mem:"?z \<notin> XY \<rho> (Suc m)" by auto
                        from Z_ti_disjoint[OF inR _ ll, of k] Suck(2) rho zZ have "?z \<notin> vars_term (ti \<rho> (Suc m))" unfolding k by auto
                        with mem have sig:"sig_F_subst ?\<theta>k ({?z} \<inter> ?domi (Suc k))" unfolding k by simp
                        show ?thesis proof (cases "?z \<in> set (Z \<rho> m)")
                          case True (* combine cases? *)
                          from vz[OF k, rule_format, OF True] have "(?\<theta>k ?z, \<sigma>i k ?z) \<in> par_rstep UR ^^ ?mi k" unfolding k by blast
                          with z_step relpow_add have steps:"(?\<theta>k ?z, \<sigma>i (Suc k) ?z) \<in> par_rstep UR ^^ ?mi ?k" unfolding sum by fast
                          show ?thesis by (rule exI[of _ ?\<theta>k], insert sig True steps, auto)
                        next
                          case False
                          with dom have eq:"?\<theta>k ?z = \<sigma>i k ?z" unfolding k nat.case(2) by auto 
                          with par_rstep_mono[of 0 "?mi k"] have steps:"(?\<theta>k ?z, \<sigma>i k ?z) \<in> par_rstep UR ^^ ?mi k" unfolding k by simp
                          with z_step relpow_add have steps:"(?\<theta>k ?z, \<sigma>i (Suc k) ?z) \<in> par_rstep UR ^^ ?mi ?k" unfolding sum by fast
                          from sig steps dom False eq k have " ?theta_prop (?\<theta>k ?z) (Var ?z) ?\<theta>k ?k" unfolding k nat.case(2) by auto
                          then show ?thesis unfolding k nat.case by blast
                        qed
                      qed
                    qed 
                  }  with choice[of "\<lambda> j \<theta>z. j < length (Z \<rho> k) \<longrightarrow>  ?theta_prop (?\<theta>k ((Z \<rho> k) ! j)) (Var ((Z \<rho> k) ! j)) \<theta>z ?k"] 
                  obtain \<theta>z where zsteps:"\<forall>j < length (Z \<rho> k). ?theta_prop (?\<theta>k ((Z \<rho> k) ! j)) (Var ((Z \<rho> k) ! j)) (\<theta>z j) ?k" by auto
                  let ?\<theta>s = "\<theta>' # map \<theta>z [0..<length (Z \<rho> k)]" and ?vs = "vars_term (ti \<rho> k) # map (\<lambda> z. {z}) (Z \<rho> k)"
                  from Z_part'[OF inR _ ll, of k] Suc(2) rho have p:"is_partition ?vs" by auto
                  have l0:"0 < length ?vs" by auto
                  define \<theta>Sk where "\<theta>Sk = fun_merge ?\<theta>s ?vs"
                  from fun_merge_part[OF p l0, of _ ?\<theta>s] have vt:"\<And>x. x \<in> vars_term (ti \<rho> k) \<Longrightarrow> \<theta>' x = \<theta>Sk x" unfolding \<theta>Sk_def by fastforce
                  with \<theta>' term_subst_eq[of "ti \<rho> k" \<theta>' \<theta>Sk, OF this] have st_prop:"?theta_prop (si \<rho> k \<cdot> ?\<theta>k) (ti \<rho> k) \<theta>Sk ?k" by simp (* #6 *)
                  { fix j 
                    let ?z = "(Z \<rho> k) ! j"
                    assume j:"j < length (Z \<rho> k)"
                    then have j':"Suc j < length ?vs" by auto 
                    with j have jth:"?vs ! (Suc j) = {?z}" by simp
                    from fun_merge_part[OF p j', unfolded jth, of _ ?\<theta>s] j have z:"\<theta>z j ?z = \<theta>Sk ?z" "Var ?z \<cdot> (\<theta>z j) = \<theta>Sk ?z" unfolding \<theta>Sk_def by auto
                    have aux:"\<And>P. \<forall>x\<in>{Z \<rho> 0 ! j}.P x = P (Z \<rho> 0 ! j)" by fast
                    have p:"?theta_prop (?\<theta>k ?z) (Var ?z) \<theta>Sk ?k" proof (cases k)
                      case 0 from zsteps[rule_format, OF j] z show ?thesis unfolding 0 nat.case eval_term.simps term.set z by force
                    next
                      case (Suc m) from zsteps[rule_format, OF j] z show ?thesis unfolding Suc nat.case eval_term.simps term.set z by force
                    qed
                  } note z_prop = this (* #7 *)
                  define \<theta>s where "\<theta>s = butlast \<theta>s' @ (?\<theta>k # [\<theta>Sk])"
                  from \<theta>s' 0 Suc(2) have f1:"length \<theta>s = Suc ?k" unfolding \<theta>s_def by auto
                  with 0 Suc(2) last_snoc last_conv_nth[of \<theta>s] have last:"\<theta>s ! ?k = \<theta>Sk" unfolding \<theta>s_def by fastforce 
                  from conjunct1[OF \<theta>s'] 0 nth_append_length have lb:"length (butlast \<theta>s') = k" by auto
                  from nth_append_length[of "butlast \<theta>s'"] have butlast:"\<theta>s ! k = ?\<theta>k" unfolding \<theta>s_def lb by blast
                  from nth_append[of "butlast \<theta>s'"] nth_butlast[of _ "\<theta>s'"] have nth:"\<And>i. i < k \<Longrightarrow> \<theta>s' ! i = \<theta>s ! i" unfolding \<theta>s_def lb by simp
                  from f1 0 have aux:"\<And>P. P ?\<theta>k \<theta>Sk k \<Longrightarrow> (\<forall> i < k. P (\<theta>s ! i) (\<theta>s ! Suc i) i) \<Longrightarrow> \<forall>i< ?k. P (\<theta>s ! i) (\<theta>s ! (Suc i)) i" 
                    unfolding butlast[symmetric] last[symmetric] by (metis less_Suc_eq)
                  from f1  0 have aux':"\<And>P m. k = Suc m \<Longrightarrow> P (\<theta>s ! m) ?\<theta>k m \<Longrightarrow> (\<forall> i < m. P (\<theta>s ! i) (\<theta>s ! Suc i) i) \<Longrightarrow> \<forall>i< k. P (\<theta>s ! i) (\<theta>s ! (Suc i)) i" 
                    unfolding butlast[symmetric] last[symmetric] by (metis less_Suc_eq)
                  with aux have aux':"\<And>P m. k = Suc m \<Longrightarrow> P ?\<theta>k \<theta>Sk k \<Longrightarrow> P (\<theta>s ! m) ?\<theta>k m \<Longrightarrow> (\<forall> i < m. P (\<theta>s ! i) (\<theta>s ! Suc i) i) \<Longrightarrow> \<forall>i< ?k. P (\<theta>s ! i) (\<theta>s ! (Suc i)) i" 
                    unfolding butlast[symmetric] last[symmetric] by metis
                  { fix i
                    assume i:"i < Suc ?k"
                    have a1:"vars_term ((U \<rho> k)\<langle>ti \<rho> k\<rangle>) = vars_term (ti \<rho> k) \<union> set (Z \<rho> k)" unfolding Uk by simp
                    from z_prop xyz' have "sig_F_subst \<theta>Sk (XY \<rho> k)" unfolding set_conv_nth[of "Z \<rho> k"] by auto
                    with st_prop a1 have 1:"sig_F_subst (\<theta>s ! ?k) (?domi ?k)" unfolding True last nat.case(2) by blast
                    from sigRs[rule_format, of k] vs0 have 2:"sig_F_subst (\<theta>s ! k) (?domi k)" 
                      unfolding butlast unfolding  nat.case(2) 0 by (cases k, auto)
                    { assume "i < k" 
                      with conjunct1[OF conjunct2[OF conjunct2[OF \<theta>s']], rule_format, unfolded 0, of i] nth
                      have "sig_F_subst (\<theta>s ! i) (?domi i)" by force
                    } note less = this
                    from i have "i < k \<or> i = k \<or> i = ?k" by linarith
                    with less 1 2 have "sig_F_subst (\<theta>s ! i) (?domi i)" by blast 
                  } note f2 = this 
                  from \<theta>s' have st:"\<forall>i<k. (si \<rho> i \<cdot> \<theta>s' ! i, ti \<rho> i \<cdot> \<theta>s' ! Suc i) \<in> (cstep R)\<^sup>*" unfolding 0  by auto
                  have f4:"\<forall>i < ?k. (si \<rho> i \<cdot> \<theta>s ! i, ti \<rho> i \<cdot> \<theta>s ! Suc i) \<in> (cstep R)\<^sup>*" proof(cases k)
                    case 0
                    from conjunct1[OF st_prop[unfolded 0 nat.case]] last butlast show ?thesis unfolding 0 by auto
                  next
                    case (Suc m) note k = this
                    from st[rule_format, of m, unfolded k, OF lessI] thetak[of m "ti \<rho> m"] have f41:"(si \<rho> m \<cdot> \<theta>s ! m, ti \<rho> m \<cdot> ?\<theta>k) \<in> (cstep R)\<^sup>*" 
                      unfolding 0 k nat.case unfolding nth[unfolded k, OF lessI] by fastforce
                    { fix i assume "i < m"
                      with st[rule_format, of i] nth have "(si \<rho> i \<cdot> \<theta>s ! i, ti \<rho> i \<cdot> \<theta>s ! Suc i) \<in> (cstep R)\<^sup>*" unfolding 0 k by simp
                    } note f43 = this
                    show ?thesis by (rule aux', insert f41 st_prop f43 k, auto)
                  qed
                  from \<theta>s' have "(s, l \<cdot> \<theta>s' ! 0) \<in> (cstep R)\<^sup>*" by auto
                  with nth[of 0] butlast have f3:"(s, l \<cdot> \<theta>s ! 0) \<in> (cstep R)\<^sup>*" by (cases k, auto)
                  { fix i j 
                    assume i:"i< ?k" and j:"j < length (Z \<rho> i)"
                    let ?z = "Z \<rho> i ! j"
                    have "(((\<theta>s ! i) ?z, (\<theta>s ! Suc i) ?z) \<in> (cstep R)\<^sup>* \<and>
                      ((\<theta>s ! Suc i) ?z, \<sigma>i (Suc i) ?z) \<in> par_rstep UR ^^ ?mi (Suc i))"
                    proof (cases "i = k") 
                      case True
                      from z_prop[OF j[unfolded True]] show ?thesis unfolding True last butlast by auto
                    next
                      case False note ltk = this 
                      with i not0_implies_Suc[of k] obtain m where k:"k=Suc m" by fastforce
                      show ?thesis proof (cases "i = m")
                        case False
                        with ltk i have im:"i < m" "Suc i < k" "i < k" unfolding k by auto
                        with \<theta>s' j i have "((\<theta>s' ! i) ?z, (\<theta>s' ! Suc i) ?z) \<in> (cstep R)\<^sup>* \<and> ((\<theta>s' ! Suc i) ?z, \<sigma>i (Suc i) ?z) \<in> par_rstep UR ^^ ?mi (Suc i)" unfolding 0 by auto
                        with conjunct1[OF \<theta>s', unfolded 0] nth[OF im(2)] nth[OF im(3)] show ?thesis unfolding k by simp
                      next
                        case True
                        with nth have x1:"\<theta>s' ! i = \<theta>s ! i" unfolding k by auto
                        from thetak[OF k, of "Var ?z"] j have x2:"Var ?z \<cdot> \<theta>s' ! k = Var ?z \<cdot> ?\<theta>k" unfolding set_conv_nth k True by fastforce
                        from \<theta>s' j i have "((\<theta>s' ! i) ?z, (\<theta>s' ! Suc i) ?z) \<in> (cstep R)\<^sup>* \<and> ((\<theta>s' ! Suc i) ?z, \<sigma>i (Suc i) ?z) \<in> par_rstep UR ^^ ?mi (Suc i)" unfolding 0 True k by auto
                        from this[unfolded x1] x2 j butlast show ?thesis unfolding True k by simp
                      qed
                    qed
                  } note f5 = this 
                  { fix i
                    assume i:"i < ?k"
                    have "\<forall>x\<in>vars_term (ti \<rho> i). ((\<theta>s ! Suc i) x, \<sigma>i (Suc i) x) \<in> par_rstep UR ^^ ?mi (Suc i)"
                    proof(cases "i = k")
                      case True
                      from st_prop last show ?thesis unfolding True by simp
                    next
                      case False note f1 = this
                      with i gr0_implies_Suc[of k] obtain m where k:"k = Suc m" by blast
                      show ?thesis proof(cases "i = m")
                        case True
                        from \<theta>s' have "\<forall>x\<in>vars_term (ti \<rho> m). ((\<theta>s' ! k) x, \<sigma>i k x) \<in> par_rstep UR ^^ ?mi k" unfolding 0 True k by blast
                        with butlast thetak show ?thesis unfolding k True by force
                      next
                        case False
                        with i f1 have im:"i < m" unfolding k by auto
                        with \<theta>s' have "\<forall>x\<in>vars_term (ti \<rho> i). ((\<theta>s' ! (Suc i)) x, \<sigma>i (Suc i) x) \<in> par_rstep UR ^^ ?mi (Suc i)" unfolding 0 True k by auto
                        with nth im show ?thesis unfolding k True by force
                      qed
                    qed
                  } note f6 = this
                  from \<theta>s' nth butlast have f7:"\<theta>s ! 0 = \<theta>1" by (cases k, auto)
                  from f1 f2 f3 f4 f5 f6 f7 have c:"?\<theta>cond \<theta>s cs cs'" unfolding Suc(2)[symmetric] by auto
                  show "\<exists> \<theta>s. ?\<theta>cond \<theta>s cs cs'" by (rule exI[of _ \<theta>s], insert c, auto)
                qed
              } note key = this(* end of crucial internal lemma *) 
              from False rho have lcs:"0 < length cs" by auto
              from key[of cs "[]", unfolded append_Nil2, OF rho dec(1) dec(2) dec(3) dec(4)] obtain \<theta>s where \<theta>s:"?\<theta>cond \<theta>s cs []" by presburger 
                  (* apply argument once more to r *)
              let ?k = "length (snd \<rho>)"
              from \<theta>s rho have 1:"\<forall>i < ?k. \<forall>z\<in>set (Z \<rho> i). (Var z \<cdot> \<theta>s ! i, Var z \<cdot> \<theta>s ! Suc i) \<in> (cstep R)\<^sup>*" unfolding all_set_conv_all_nth by auto
              with Lemma_17[OF sim(1) ll, of \<theta>s] lcs 1 rho \<theta>s have "(l \<cdot> \<theta>s ! 0, rr \<cdot> \<theta>s ! ?k) \<in> (cstep R)\<^sup>+" by auto
              with \<theta>s have ssteps:"(s, rr \<cdot> \<theta>s ! length (snd \<rho>)) \<in> (cstep R)\<^sup>+" by auto
              from lcs gr0_conv_Suc rho obtain k' where k:"?k = Suc k'""length cs = Suc k'" unfolding rho by auto
              from U_cond[unfolded rho snd_conv length_append, OF sim(1), of k'] rho lcs obtain Uk where 
                Uk:"U_fun \<rho> k' Uk" unfolding k by force 
              then have vs:"vars_term (U \<rho> k')\<langle>ti \<rho> k'\<rangle> = vars_term (ti \<rho> k') \<union>  set (Z \<rho> k')" by auto
              from sig_F_r[OF sim(1)] have sig_F_r:"sig_F rr" unfolding rho by force
              from X_Y_imp_Z[OF sim(1), of k'] k rho have xyz:"XY \<rho> k' \<subseteq> set (Z \<rho> k')" by force
              with vars_r_subset_tk_Z[OF sim(1)[unfolded rho] lcs] rho k have 
                vr:"vars_term rr \<subseteq> vars_term (ti \<rho> k') \<union>  set (Z \<rho> k')" by auto 
              from \<theta>s have z_steps:"\<forall>j<length (Z \<rho> k').  ((\<theta>s ! ?k) (Z \<rho> k' ! j), \<sigma>i ?k (Z \<rho> k' ! j)) \<in> par_rstep UR ^^ ?mi ?k" unfolding k by blast
              from \<theta>s have t_steps:"\<forall>x\<in>vars_term (ti \<rho> k'). ((\<theta>s ! ?k) x, \<sigma>i ?k x) \<in> par_rstep UR ^^ ?mi ?k" unfolding k by blast
              with vr z_steps have "\<forall>x\<in>vars_term rr. ((\<theta>s ! ?k) x, \<sigma>i ?k x) \<in> par_rstep UR ^^ ?mi ?k" unfolding set_conv_nth by blast
              with all_ctxt_closed_subst_step[OF acc] have rsteps:"(rr \<cdot> (\<theta>s ! ?k), rr \<cdot> (\<sigma>i ?k)) \<in> par_rstep UR ^^ ?mi ?k" by fast
              note sig_r = conjunct1[OF conjunct2[OF conjunct2[OF \<theta>s]]]
              from sig_r[ rule_format, of "length cs", OF lessI] lcs rho vars_r_subset_tk_Z[OF sim(1)[unfolded rho] lcs] Uk
              have "\<And>x. x \<in> vars_term rr \<Longrightarrow> sig_F ((\<theta>s ! ?k) x)" unfolding k by auto
              with sig_F_r have 11:"sig_F (rr \<cdot> \<theta>s ! ?k)" unfolding sig_F_def funs_term_subst by blast
              from dec(2)[rule_format, of ?k, unfolded k] rhs_n.simps[of "(l,rr)" cs "Suc k'"] have usq_r:"ui (Suc (ji (Suc k'))) = rr \<cdot> (\<sigma>i  ?k)" 
                unfolding k rho rstep_r_p_s_def ctxt_of_pos_term.simps Let_def intp_actxt.simps snd_conv by auto
              let ?j = "ji ?k"
              from dec(2)[rule_format, of ?k] have
                last_step:"(ui ?j, ui (Suc ?j)) \<in> rstep_r_p_s UR (lhs_n \<rho> ?k, rhs_n \<rho> ?k) [] (\<sigma>i ?k)" unfolding rho by fastforce
              from ui(3) j_last have aux:"\<forall>i<Suc m - Suc ?j. (ui (i + Suc ?j), ui (Suc i + Suc ?j)) \<in> par_rstep UR" by simp
              from last_step have usq_j:"ui (Suc ?j) = rr \<cdot> (\<sigma>i ?k)" unfolding rstep_r_p_s_def rho rhs_n.simps by simp
              have ls:"sum_list (map (Suc \<circ> ni) [0..<Suc k']) > sum_list (map ni [0..<Suc k'])" by (induct k', auto) 
              with dec(4) j_last k have m':"?mi ?k \<le> ?j" unfolding rho by simp
              from rsteps par_rstep_mono[OF this] usq_j have rsteps':"(rr \<cdot> (\<theta>s ! ?k), ui (Suc ?j)) \<in> par_rstep UR ^^ ?j" by auto
              from dec(1)[rule_format, of ?k] have jm:"?j \<le> m" unfolding rho by auto 
              show ?thesis by(rule exI[of _ "\<theta>s ! ?k"], rule exI[of _ "?j"], insert ssteps 11 rsteps' jm, auto)
            qed
            then obtain \<theta>' m' where up2r:"(s, rr \<cdot> \<theta>') \<in> (cstep R)\<^sup>+" "sig_F (rr \<cdot> \<theta>')" 
              "(rr \<cdot> \<theta>', ui (Suc m')) \<in> par_rstep UR ^^ m'" "m' \<le> m" by auto
            have "(ui (Suc m'), ui (Suc m)) \<in> par_rstep UR ^^ (Suc m - (Suc m'))" unfolding relpow_fun_conv 
              by (rule exI[of _ "\<lambda> i. ui (i + Suc m')"], insert up2r(4) ui(3), auto)
            with ui(2) have steps:"(ui (Suc m'), t \<cdot> \<sigma>) \<in> par_rstep UR ^^ (Suc m - Suc m')" by fastforce
            let ?m = "m' + (Suc m - Suc m')" 
            from steps up2r(3) have steps:"(rr \<cdot> \<theta>', t \<cdot> \<sigma>) \<in> par_rstep UR ^^ ?m" unfolding relpow_add by fastforce
            from up2r(4) have m':"?m = m" by linarith
            then have m:"((m, rr \<cdot> \<theta>'), nt) \<in> measures [fst, size \<circ> snd]" unfolding ns Suc_m by auto
            from up2r(2) tR lint steps ind[rule_format, OF m, unfolded split, rule_format, of t \<sigma>] obtain \<theta> where 
              \<theta>:"?theta_prop_with' \<sigma> ?m (rr \<cdot> \<theta>') t \<theta> ?k" unfolding m' by blast
            with m' par_rstep_mono[of ?m n] 
            have 1:"\<forall>x\<in>vars_term t. (Var x \<cdot> \<theta>, Var x \<cdot> \<sigma>) \<in> par_rstep UR ^^ n" unfolding Suc_m by simp
            from \<theta> up2r(1) have 2:"(s, t\<cdot> \<theta>) \<in> (cstep R)\<^sup>*" by force
            show ?thesis by (rule exI[of _ \<theta>], insert \<theta> 1 2, auto)
          next
            case False  (* case 2.2.2.2: we consider a partial R-step simulation subsequence *)
            with sim have part:"?partial" by auto
            let ?sum = "\<lambda> k j ni nm. j 0 + sum_list (map (Suc \<circ> ni) [0..< k]) + Suc nm = Suc m"
            let ?ji = "\<lambda> k ji. (\<forall>x. 0 \<le> x \<and> x \<le> k \<longrightarrow> ji x < Suc m)" 
            let ?ustep' = "\<lambda> j \<sigma>i i. j i < Suc m \<and> (ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i)"
            let ?usteps' = "\<lambda> k j \<sigma>i. (\<forall>i. 0 \<le> i \<and> i \<le> k \<longrightarrow> ?ustep' j \<sigma>i i)"
            let ?usteps = "\<lambda> k j \<sigma>i. \<forall>i. 0 \<le> i \<and> i \<le> k \<longrightarrow>  (ui (j i), ui (Suc (j i))) \<in> rstep_r_p_s UR (lhs_n \<rho> i, rhs_n \<rho> i) [] (\<sigma>i i)"
            let ?isteps = "\<lambda> k ji ni. \<forall>i. 0 \<le> i \<and> i < k \<longrightarrow> (ui (Suc (ji i)), ui (ji (Suc i))) \<in> par_urstep_below_root ^^ ni i"
            let ?suffix = "\<lambda> k j nm. (ui (Suc (j k)), ui (Suc m)) \<in> par_urstep_below_root ^^ nm"
            from part[unfolded partial_R_step_simulation_def] obtain ji ni \<sigma>i nm where 
              "k < length cs" "?usteps' k ji \<sigma>i" "?isteps k ji ni" "?suffix k ji nm" "?sum k ji ni nm" unfolding rho by force
            then have dec:"k < length cs" "?ji k ji" "?usteps k ji \<sigma>i" "?isteps k ji ni" "?suffix k ji nm" "?sum k ji ni nm" by (blast, auto)
            define m0 \<sigma>1 where "m0 = ji 0" and "\<sigma>1 = \<sigma>i 0"
            from dec(3)[rule_format, of 0] have uim0:"ui m0 = l \<cdot> \<sigma>1" "ui (Suc m0) = (rhs_n \<rho> 0) \<cdot> \<sigma>1" 
              unfolding  m0_def \<sigma>1_def rho rstep_r_p_s_def lhs_n.simps(1) by (force,force)
            from dec(2) have m0m:"m0 < Suc m" unfolding  m0_def by auto
            from prefix[OF this uim0] obtain \<theta>1 where theta1:"?result m0 \<sigma>1 \<theta>1" by presburger
            then have vars:"\<forall>x\<in>vars_term l \<union> set (Z \<rho> 0). (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0"
              and substR1:"sig_F_subst \<theta>1 (?domi 0)" by auto
            from dec(1) rho have lpos:"0 < length (snd \<rho>)" by auto
            from dctrs[unfolded dctrs_def, rule_format, OF sim(1) lpos] rho l_vars_X0_vars[OF sim(1) lpos] sim 
            have vs:"vars_term (si \<rho> 0) \<subseteq> vars_term l" by simp
            with vs vars have "\<And> x. x \<in> vars_term (si \<rho> 0) \<Longrightarrow>  (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0" by auto
            with all_ctxt_closed_subst_step[OF acc] have sstep:"(si \<rho> 0 \<cdot> \<theta>1, si \<rho> 0 \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0" by fastforce
            from theta1[unfolded nat.case(1)] have theta1:"(s, l \<cdot> \<theta>1) \<in> (cstep R)\<^sup>*" "sig_F_subst \<theta>1 (vars_term l)"
              "(\<forall>x\<in>vars_term l. (Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0)" "(sig_F (l \<cdot> \<sigma>1) \<longrightarrow> l \<cdot> \<theta>1 = l \<cdot> \<sigma>1)" by (fast+)
            from sig_F_l[OF sim(1)]  have 3:"sig_F l" unfolding rho by force
            from U_cond[OF sim(1), of k] dec(1) obtain Uk where Uk:"U_fun \<rho> k Uk" "Uk \<notin> F" unfolding rho by auto
            from dec(3)[rule_format, of k, unfolded rstep_r_p_s_def  rho rhs_n.simps] dec(1) Uk 
            obtain ts where Uk_last:"ui (Suc (ji k)) = Fun Uk ts" unfolding rho by force
            from dec(5)[unfolded this] par_rstep_below_root_pow_same_root1 obtain ys where Uk':"ui (Suc m) = Fun Uk ys" by blast
            from Uk(2) ui(2)[unfolded this] tR[unfolded sig_F_def] funs_term_subst[of t \<sigma>] obtain x where tx:"t = Var x" by (cases t, auto)
            with Uk Uk' ui(2) have 4:"\<not> sig_F (\<sigma> x)" unfolding sig_F_def by force
            let ?\<theta> = "\<lambda> x. l \<cdot> \<theta>1"     
            from theta1(3) all_ctxt_closed_subst_step[OF acc] have lsteps:"(l \<cdot> \<theta>1, l \<cdot> \<sigma>1) \<in> par_rstep UR ^^ m0" by simp
            have "(ui m0, ui (Suc m)) \<in> par_rstep UR ^^ (Suc m - m0)" unfolding relpow_fun_conv 
              by (rule exI[of _ "\<lambda> i. ui (i + m0)"], insert ui(3) m0m, auto)
            from this[unfolded uim0 ui(2) tx] have "(l \<cdot> \<sigma>1, \<sigma> x) \<in> par_rstep UR ^^ (Suc m - m0)" by force
            with lsteps m0m relpow_add[of m0 "Suc m - m0" "par_rstep UR"] 
            have steps:"(t \<cdot> ?\<theta>, \<sigma> x) \<in> par_rstep UR ^^ n" unfolding Suc tx by auto
            from theta1(1) tx have 1:"(s, t \<cdot> ?\<theta>) \<in> (cstep R)\<^sup>*" by force 
            from sig_F_subst[OF theta1(2) 3] have 2:"sig_F_subst ?\<theta> (vars_term t)" unfolding tx by blast
            { assume nlv:"non_LV" and zd:"source_preserving R Z" 
              have 1:"t\<cdot>?\<theta> = (clhs \<rho>)\<cdot>\<theta>1" unfolding tx rho by auto (* #1 *)
              define \<tau>2 where "\<tau>2 = mk_subst Var (zip (Z \<rho> k) (tl ys))"
              let ?v = "Fun Uk (si \<rho> k # (map Var (Z \<rho> k))) \<cdot> (\<sigma>i k)" 
              from dec(3)[rule_format, of k, unfolded rstep_r_p_s_def] a have t':"ui (Suc (ji k)) = rhs_n \<rho> k \<cdot> (\<sigma>i k)" by simp
              from Uk t'[unfolded rho rhs_n.simps] a rho dec(1) have t':"ui (Suc (ji k)) = ?v" by auto
              from Z[unfolded Z_vars_def] sim(1) dec(1) rho have d:"distinct (Z \<rho> k)" by force
              from dec(5)[unfolded t' Uk' eval_term.simps par_rstep_pow_imp_args_par_rstep_pow length_map] have
                "length (si \<rho> k # map Var (Z \<rho> k)) = length ys" by simp
              then have ll:"length (tl ys) = length (Z \<rho> k)" and lys: "length ys > 0" by auto
              with mk_subst_distinct[OF d, where ?ls="tl ys"] have tys:"tl ys = map (\<lambda>t. t \<cdot> \<tau>2) (map Var (Z \<rho> k))" 
                unfolding list_eq_iff_nth_eq \<tau>2_def by force 
              from tys lys have 2:"t\<cdot>\<sigma> =((U \<rho> k) \<cdot>\<^sub>c \<tau>2)\<langle>hd ys\<rangle>"  (* #2 *)
                unfolding Uk actxt.simps intp_actxt.simps Uk'[unfolded ui(2)] list.map append_Nil tys[symmetric] by auto
              have 3:"\<forall>x \<in> vars_term (clhs \<rho>). (\<theta>1 x, \<tau>2 x) \<in> (par_rstep UR)^*"
              proof
                fix x
                assume xl:"x \<in> vars_term (clhs \<rho>)"
                with rho have xl:"x \<in> vars_term l" by simp  
                with vars relpow_imp_rtrancl have s0:"(Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>1) \<in> (par_rstep UR) ^*" by blast
                { fix i
                  assume ik:"i \<le> k" 
                  then have "(Var x \<cdot> \<theta>1, Var x \<cdot> (\<sigma>i i)) \<in> (par_rstep UR) ^*" proof(induct i)
                    case 0
                    from s0 show ?case unfolding \<sigma>1_def by auto
                  next
                    case (Suc i) 
                    then have *:"(Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>i i) \<in> (par_rstep UR)\<^sup>*" by auto
                    from Suc have i:"Suc i < length cs" using dec(1) by auto 
                    from zd[unfolded source_preserving_def, rule_format, OF sim(1), of i] Suc(2) xl dec(1) have "x \<in> set (Z \<rho> i)" 
                      unfolding rho by force
                    from this[unfolded set_conv_nth] obtain j where xj:"x = (Z \<rho> i) ! j" "j < length (Z \<rho> i)" by blast
                    from U_cond[OF sim(1), of i] i obtain Ui where Ui:"U_fun \<rho> i Ui" unfolding rho by auto
                    from U_cond[OF sim(1), of "Suc i"] i obtain USi where USi:"U_fun \<rho> (Suc i) USi" unfolding rho by auto
                    from dec(3)[rule_format, of "i", unfolded rho  rhs_n.simps] dec(1) Suc(2) have 
                      u1:"ui (Suc (ji i)) = (U \<rho> i)\<langle>si \<rho> i\<rangle> \<cdot> \<sigma>i i" unfolding rho rstep_r_p_s_def ctxt_of_pos_term.simps(1)
                        Let_def intp_actxt.simps i by simp
                    from dec(3)[rule_format, of "Suc i", unfolded rho  lhs_n.simps] dec(1) Suc(2) have 
                      u2:"ui (ji (Suc i)) = (U \<rho> i)\<langle>ti \<rho> i\<rangle> \<cdot> \<sigma>i (Suc i)" unfolding rho rstep_r_p_s_def ctxt_of_pos_term.simps(1)
                        Let_def intp_actxt.simps i by simp
                    let ?zs = "map Var (Z \<rho> i)"
                    let ?ss = "map (\<lambda>t. t \<cdot> \<sigma>i i) (si \<rho> i # ?zs)"
                    let ?ts = "map (\<lambda>t. t \<cdot> \<sigma>i (Suc i)) (ti \<rho> i # ?zs)"
                    from dec(4)[rule_format, of i, unfolded rho u1 u2 Ui[unfolded rho] intp_actxt.simps append_Nil] Suc(2) rho have
                      "(Fun Ui (si \<rho> i # map Var (Z \<rho> i)) \<cdot> \<sigma>i i, Fun Ui (ti \<rho> i # map Var (Z \<rho> i)) \<cdot> \<sigma>i (Suc i)) \<in> par_urstep_below_root ^^ ni i" 
                      by simp
                    from this[unfolded eval_term.simps par_rstep_pow_imp_args_par_rstep_pow length_map] Suc(2) 
                    have "\<forall>x<length (si \<rho> i # ?zs). (?ss ! x,  ?ts ! x) \<in> par_rstep UR ^^ ni i" by blast
                    from this[rule_format, of "Suc j"] xj(2) have "(?ss ! (Suc j),  ?ts ! (Suc j)) \<in> par_rstep UR ^^ ni i" by fastforce
                    from xj this[unfolded list.map(2) nth_Cons_Suc map_map] have "(\<sigma>i i x, \<sigma>i (Suc i) x) \<in> par_rstep UR ^^ ni i" by simp
                    with relpow_imp_rtrancl have "(\<sigma>i i x, \<sigma>i (Suc i) x) \<in> (par_rstep UR)^*" by blast
                    with * show ?case by simp
                  qed
                } then have k:"(Var x \<cdot> \<theta>1, Var x \<cdot> \<sigma>i k) \<in> (par_rstep UR)\<^sup>*" by auto 
                let ?ss = "map (\<lambda>t. t \<cdot> \<sigma>i k) (local.si \<rho> k # map Var (Z \<rho> k))" 
                from dec(5)[unfolded t' Uk' eval_term.simps par_rstep_pow_imp_args_par_rstep_pow] have
                  ss:"(\<forall>i<length ?ss. (?ss ! i, ys ! i) \<in> par_rstep UR ^^ nm)" by blast
                from zd[unfolded source_preserving_def, rule_format, OF sim(1), of k] dec(1) xl dec(1) have "x \<in> set (Z \<rho> k)" 
                  unfolding rho by force
                from this[unfolded set_conv_nth] obtain j where xj:"x = (Z \<rho> k) ! j" "j < length (Z \<rho> k)" by blast  
                from ss[rule_format, unfolded length_map list.map(2) nth_Cons_Suc , of "Suc j"] xj have
                  "(\<sigma>i k x, ys ! (Suc j)) \<in> par_rstep UR ^^ nm" by auto
                with relpow_imp_rtrancl have  "(\<sigma>i k x, ys ! (Suc j)) \<in> (par_rstep UR)^*" by auto
                with nth_tl[of j ys, unfolded ll, OF xj(2)] have *:"(\<sigma>i k x, tl ys ! j) \<in> (par_rstep UR)^*" by auto
                from tys  xj have "tl ys ! j = \<tau>2 x" by force
                with k * show "(\<theta>1 x, \<tau>2 x) \<in> (par_rstep UR)\<^sup>*" by simp
              qed
              have "\<exists> \<rho> \<tau>1 \<tau>2 k u. \<rho> \<in> R \<and> k < length (snd \<rho>) \<and> t \<cdot> (\<lambda>x. l \<cdot> \<theta>1) = clhs \<rho> \<cdot> \<tau>1 \<and> t \<cdot> \<sigma> = ((U \<rho> k) \<cdot>\<^sub>c \<tau>2)\<langle>u\<rangle> \<and> 
                    (\<forall>x \<in> vars_term (clhs \<rho>). (\<tau>1 x, \<tau>2 x) \<in> (par_rstep UR)^*)" unfolding rho 
                by (rule exI[of _ \<rho>],rule exI[of _ \<theta>1], rule exI[of _ \<tau>2],rule exI[of _ k], insert 1 2 3 sim(1) dec(1) rho, auto)
            }
            then have 5:"t_U_cond t ?\<theta> \<sigma>" unfolding t_U_cond_def tx by fast
            show ?thesis by (rule exI[of _ ?\<theta>], insert 1 2 steps 4 5, simp add: tx)
          qed
        qed
      qed
    qed
  qed
  from this[unfolded split, rule_format] s t seq show ?thesis unfolding t_U_cond_def split by presburger
qed

(* Theorem 4.3 in NSS12 *)
lemma soundness:
  assumes ll:"left_linear_trs UR"
    and sig_F_s:"sig_F s"
    and sig_F_t:"sig_F t" 
    and seq:"(s,t) \<in> (rstep UR)^*"
  shows "(s, t) \<in> (cstep R)^*"
proof- 
  fix x :: 'v
  have sig_F_x:"sig_F (Var x)" unfolding sig_F_def by simp
  have lin:"linear_term (Var x)" by simp 
  from seq rtrancl_mono[OF rstep_par_rstep] have "(s, t) \<in> (par_rstep UR)\<^sup>*" by blast
  with rtrancl_imp_relpow obtain n where "(s,Var x \<cdot> (\<lambda>y. t)) \<in> (par_rstep UR) ^^ n" by auto
  from soundness_key_lemma[OF ll sig_F_s sig_F_x lin this] sig_F_t show ?thesis by force
qed


lemma join_cstep: 
  assumes sseq:"(s,u) \<in> (rstep UR)^*"
    and tseq:"(t,u) \<in> (rstep UR)^*"
    and u:"funs_term u \<subseteq> funs_trs UR \<union> F" (is "_ \<subseteq> ?FUR")
    and sp:"source_preserving R Z"
    and nlv:"non_LV"
    and ll:"left_linear_trs UR"
    and s:"sig_F s"
    and t:"sig_F t"
  shows "(s,t) \<in> (cstep R)\<^sup>\<down>"
proof- 
  have "\<And>s t. (s,u) \<in> (rstep UR)^* \<Longrightarrow> (t,u) \<in> (rstep UR)^* \<Longrightarrow> sig_F s \<Longrightarrow> sig_F t \<Longrightarrow> funs_term u \<subseteq> ?FUR \<Longrightarrow> (s,t) \<in> (cstep R)\<^sup>\<down>" 
  proof(induct u rule:term.induct)
    case (Var x)
    then have x:"sig_F (Var x)" unfolding sig_F_def by simp
    from soundness[OF ll Var(3) x Var(1)] have *:"(s, Var x) \<in> (cstep R)\<^sup>*" by auto
    from soundness[OF ll Var(4) x Var(2)] have "(t, Var x) \<in> (cstep R)\<^sup>*" by auto
    with * show ?case by blast
  next
    case (Fun f us) 
    from rtrancl_imp_relpow[OF Fun(2)[unfolded par_rsteps_rsteps[symmetric]]] obtain m 
      where sseq':"(s, Fun f us) \<in> par_rstep UR ^^ m" by blast
    from rtrancl_imp_relpow[OF Fun(3)[unfolded par_rsteps_rsteps[symmetric]]] obtain n 
      where tseq':"(t, Fun f us) \<in> par_rstep UR ^^ n"  by blast
    { assume fR:"f \<in> F"
      let ?xs = "dvars (length us)"
      from distinct_vars[of "length us"] have fresh:"distinct ?xs""length ?xs = length us" by auto
      let ?u = "Fun f (map Var ?xs)" 
      from fR have u1:"sig_F ?u" unfolding sig_F_def by auto
      let ?vs = "map (\<lambda> x. {x}) ?xs"
      have "?vs = map vars_term (map Var ?xs)" by auto
      have p:"is_partition ?vs" unfolding is_partition_def length_map fresh(2) 
      proof(rule, rule, rule, rule)
        fix i j
        assume j:"j < length us" and i:"i < j"
        then have i':"i < length us" by auto
        from i fresh(1)[unfolded distinct_conv_nth, rule_format, unfolded fresh(2), OF j i'] have "?xs ! i \<noteq> ?xs ! j" by auto
        then show "map (\<lambda>x. {x}) ?xs ! i \<inter> map (\<lambda>x. {x}) ?xs ! j = {}" 
          unfolding nth_map[of i ?xs, unfolded fresh(2), OF i'] nth_map[of j ?xs, unfolded fresh(2), OF j] by fast
      qed
      have ls:"\<And>x. x \<in> set (map Var ?xs) \<Longrightarrow> linear_term x" by auto
      have "map (\<lambda>x. {x}) (dvars (length us)) = map vars_term (map Var (dvars (length us)))" unfolding map_map by auto
          (* finally: it's linear *)
      with ls fresh p have lin:"linear_term ?u" unfolding linear_term.simps(2)[of f "map Var ?xs"] unfolding map_map by metis
      let ?\<sigma> = "mk_subst Var (zip ?xs us)"
      { fix j assume "j < length us"                              
        with mk_subst_distinct[OF fresh(1)] fresh(2) have "?\<sigma> (?xs ! j) = us ! j" by auto
      } note \<sigma>equiv = this 
      with fresh(2) nth_map[of] have us\<sigma>:"us = map ?\<sigma> ?xs" unfolding  list_eq_iff_nth_eq length_map by simp
      then have u\<sigma>:"Fun f us = ?u \<cdot> ?\<sigma>" unfolding eval_term.simps(2)
          term.inject(2)[of f us]  list_eq_iff_nth_eq by simp
          (* obtain \<theta>s *)
      from soundness_key_lemma[OF ll Fun(4) u1, unfolded u\<sigma>[symmetric], OF lin] sseq'[unfolded u\<sigma>] obtain \<theta>s where
        sseq:"(s, ?u \<cdot> \<theta>s) \<in> (cstep R)\<^sup>*""sig_F_subst \<theta>s (vars_term ?u)"
        "\<forall>x\<in>vars_term ?u. (Var x \<cdot> \<theta>s, Var x \<cdot> ?\<sigma>) \<in> par_rstep UR ^^ m" by meson
      from soundness_key_lemma[OF ll Fun(5) u1, unfolded u\<sigma>[symmetric], OF lin] tseq'[unfolded u\<sigma>] obtain \<theta>t where
        tseq:"(t, ?u \<cdot> \<theta>t) \<in> (cstep R)\<^sup>*""sig_F_subst \<theta>t (vars_term ?u)"
        "\<forall>x\<in>vars_term ?u. (Var x \<cdot> \<theta>t, Var x \<cdot> ?\<sigma>) \<in> par_rstep UR ^^ n" by meson
          (* combine *)
      let ?t = "(Fun f (map Var ?xs)) \<cdot> \<theta>t" let ?s = "(Fun f (map Var ?xs)) \<cdot> \<theta>s" 
      { fix j
        assume j: "j < length us"
        let ?x = "?xs ! j" 
        from  j have xv:"?x \<in> vars_term ?u" unfolding term.simps(18)
          using dvars_def distinct_vars by auto
        from sseq(3)[rule_format, OF xv] relpow_imp_rtrancl par_rsteps_rsteps have m:"(Var ?x \<cdot> \<theta>s, Var ?x \<cdot> ?\<sigma>) \<in> (rstep UR)^*" by blast
        from tseq(3)[rule_format, OF xv] relpow_imp_rtrancl par_rsteps_rsteps have n:"(Var ?x \<cdot> \<theta>t, Var ?x \<cdot> ?\<sigma>) \<in> (rstep UR)^*" by blast
        from j xv have "Var ?x \<cdot> ?\<sigma> \<in> set (map ?\<sigma> ?xs)" by force
        with us\<sigma> have xus:"Var ?x \<cdot> ?\<sigma> \<in> set us" by force 
        with us\<sigma> Fun(6) term.set(2) have funs: "funs_term (Var ?x \<cdot> ?\<sigma>) \<subseteq> ?FUR" by auto
        from xv sseq(2) have sigs:"sig_F (\<theta>s ?x)" by blast
        from xv tseq(2) have sigt:"sig_F (\<theta>t ?x)" by blast
        from Fun(1)[OF xus m n] sigs sigt funs have "(\<theta>s ?x, \<theta>t ?x) \<in>  (cstep R)\<^sup>\<down>" by auto
      } note xsteps = this
      have "(?u \<cdot> \<theta>s, ?u \<cdot> \<theta>t) \<in> (cstep R)\<^sup>\<down>" unfolding eval_term.simps 
        by (rule all_ctxt_closedD, insert xsteps join_csteps_all_ctxt_closed fresh(2), auto)
      from join_rtrancl_join[OF rtrancl_join_join tseq(1), OF sseq(1) this] have "(s, t) \<in> (cstep R)\<^sup>\<down>" by auto
    } note case1 = this 
      (* case of U symbol *)
    { assume fR:"\<exists> \<rho> i. \<rho> \<in> R \<and> i < length (snd \<rho>) \<and> U_fun \<rho> i f"
      then obtain \<rho> i where *:"\<rho> \<in> R" "i < length (snd \<rho>)" "U_fun \<rho> i f"  by auto
      fix x :: 'v
      obtain l r cs where rho:"\<rho> = ((l,r),cs)" by (cases \<rho>, auto)
      have u:"Fun f us = (Var x) \<cdot> (\<lambda>x. Fun f us)" by simp
      have x:"sig_F (Var x)" "linear_term (Var x)" unfolding sig_F_def by auto
      let ?rseq = "\<lambda>u \<theta>u. (u, (Var x) \<cdot> \<theta>u) \<in> (cstep R)\<^sup>*"
      let ?vars = "\<lambda>\<theta>u n. (Var x \<cdot> \<theta>u, Fun f us) \<in> par_rstep UR ^^ n"
      let ?cond = "non_LV \<and> source_preserving R Z \<and> (\<exists>Ui zs. (\<exists>\<rho>\<in>R. \<exists>i<length (snd \<rho>). U_fun \<rho> i Ui) \<and> Fun f us = Fun Ui zs)"
      let ?cons = "\<lambda>\<theta>. (\<exists>\<rho> \<tau>1 \<tau>2 k u. \<rho> \<in> R \<and> k < length (snd \<rho>) \<and> Var x \<cdot> \<theta> = clhs \<rho> \<cdot> \<tau>1 \<and> Fun f us = ((U \<rho> k) \<cdot>\<^sub>c \<tau>2)\<langle>u\<rangle> \<and>
            (\<forall>x\<in>vars_term (clhs \<rho>). (\<tau>1 x, \<tau>2 x) \<in> (par_rstep UR)\<^sup>*))" 
      from nlv assms(4) fR have c:"?cond" by blast
      from soundness_key_lemma[OF ll Fun(5) x, of "\<lambda>x. Fun f us", unfolded u[symmetric],OF tseq'] obtain \<theta>t where
        tseq:"?rseq t \<theta>t \<and> sig_F (\<theta>t x) \<and> ?vars \<theta>t n \<and> (?cond\<longrightarrow> ?cons \<theta>t)" by force
      with c have tseq:"?rseq t \<theta>t" "sig_F (\<theta>t x)" "?vars \<theta>t n" "?cons \<theta>t" by auto
      from soundness_key_lemma[OF ll Fun(4) x, of "\<lambda>x. Fun f us", unfolded u[symmetric],OF sseq'] obtain \<theta>s where
        sseq:"?rseq s \<theta>s \<and> sig_F (\<theta>s x) \<and> ?vars \<theta>s m \<and> (?cond\<longrightarrow> ?cons \<theta>s)" by force
      with c have sseq:"?rseq s \<theta>s" "sig_F (\<theta>s x)" "?vars \<theta>s m" "?cons \<theta>s" by auto
      from sseq(4) obtain \<rho>s \<sigma>f \<sigma>l ks u_s where ps:"\<rho>s \<in> R" "ks < length (snd \<rho>s)""Var x \<cdot> \<theta>s = clhs \<rho>s \<cdot> \<sigma>f" "Fun f us = ((U \<rho>s ks) \<cdot>\<^sub>c \<sigma>l)\<langle>u_s\<rangle>"
        "\<forall>x\<in>vars_term (clhs \<rho>s). (\<sigma>f x, \<sigma>l x) \<in> (par_rstep UR)\<^sup>*" by blast
      from tseq(4) obtain \<rho>t \<tau>f \<tau>l kt u_t where pt:"\<rho>t \<in> R" "kt < length (snd \<rho>t)" "Var x \<cdot> \<theta>t = clhs \<rho>t \<cdot> \<tau>f" "Fun f us = ((U \<rho>t kt) \<cdot>\<^sub>c \<tau>l)\<langle>u_t\<rangle>"
        "\<forall>x\<in>vars_term (clhs \<rho>t). (\<tau>f x, \<tau>l x) \<in> (par_rstep UR)\<^sup>*" by blast
      from U_cond[OF ps(1-2)] ps(4) have fs:"U_fun \<rho>s ks f" by fastforce
      from U_cond[OF pt(1-2)] pt(4) have ft:"U_fun \<rho>t kt f" by fastforce
      from U_cond[OF ps(1-2)] obtain f' where
        pe:"U_fun \<rho>s ks f' \<and> (\<forall>\<rho>' n' g b c a. \<rho>' \<in> R \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a \<longrightarrow>
            f' \<noteq> g \<or> ks = n' \<and> (\<forall>i\<le>ks. U \<rho>s i = U \<rho>' i) \<and> prefix_equivalent \<rho>s \<rho>' ks)" by blast
      with fs have "f' = f" by simp
      from pe[unfolded this] ft pt(1) pt(2) have pe:"ks = kt \<and> (\<forall>i\<le>ks. U \<rho>s i = U \<rho>t i) \<and> prefix_equivalent \<rho>s \<rho>t ks" by blast
      from this[unfolded prefix_equivalent_def] have ll':"clhs \<rho>s = clhs \<rho>t" by blast
      from U_cond[OF ps(1-2)] * fs actxt.inject[of f "[]" \<box>] 
      have "prefix_equivalent \<rho>s \<rho> ks" by metis
      from this[unfolded prefix_equivalent_def] have ll:"clhs \<rho>s = l" unfolding rho by simp
      from ps(4) pt(4) have u:" ((U \<rho>s ks) \<cdot>\<^sub>c \<sigma>l)\<langle>u_s\<rangle> = ((U \<rho>t kt) \<cdot>\<^sub>c \<tau>l)\<langle>u_t\<rangle>" by auto 
      have aux:"\<And>\<sigma>.((\<lambda>t. t \<cdot> \<sigma>) \<circ> Var) = \<sigma>" by force
      from conjunct2[OF u[unfolded fs ft  actxt.simps intp_actxt.simps term.simps(2)  append_Nil list.map(2) map_map]]
      have zs:"map \<sigma>l (Z \<rho>s ks) = map \<tau>l (Z \<rho>t kt)" unfolding aux by simp 
      note acc = all_ctxt_closed_subst_step[OF all_ctxt_closed_par_rsteps]
      from ps(5) ll acc have "(l\<cdot>\<sigma>f, l\<cdot>\<sigma>l) \<in> (par_rstep UR)\<^sup>*" by simp
      from pt(5) ll ll' acc have "(l\<cdot>\<tau>f, l\<cdot>\<tau>l) \<in> (par_rstep UR)\<^sup>*" by simp
      from pe have uu:"U \<rho>s ks = U \<rho>t kt" by auto 
      from term.inject(1) inj_on_def have "inj Var" by auto
      from uu[unfolded fs ft actxt.inject, simplified]  inj_map_eq_map[OF this] have zzz:"Z \<rho>s ks = Z \<rho>t kt" by blast
      note vlz = sp[unfolded source_preserving_def, rule_format, OF pt(1-2)]
      { fix x 
        assume "x \<in> vars_term l"
        with vlz ll ll' have vlk:"x \<in> set (Z \<rho>t kt)" by auto
        from this[unfolded set_conv_nth] obtain j where j:"j < length (Z \<rho>t kt)" "x = (Z \<rho>t kt) ! j" by auto
        from j(1) zs[unfolded list_eq_iff_nth_eq] have "\<sigma>l x = \<tau>l x" unfolding j(2) zzz by simp
      } note vl = this
      have eq:"l\<cdot> \<sigma>l = l \<cdot> \<tau>l" by (rule term_subst_eq, insert zs[unfolded zzz] vl, auto)
      from ps(4)[unfolded fs] have useq:"us \<noteq> []" "tl us = map \<sigma>l (Z \<rho>s ks)" by (simp,simp)
      { fix z 
        assume z:"z \<in> vars_term l" 
        with vlz have zz:"z \<in> set (Z \<rho>t kt)" using ll' ll by auto
        from this[unfolded set_conv_nth] obtain j where j:"j < length (Z \<rho>t kt)" "z = (Z \<rho>t kt) ! j" by blast
        from vl z have xeq:"\<sigma>l z = \<tau>l z" by simp 
        with useq[unfolded zzz] j have xtl:"\<sigma>l z \<in> set (tl us)" by (metis length_map nth_map nth_mem) 
        from sig_F_l[OF *(1)] have sigl:"sig_F l" unfolding rho by fastforce
        from sseq(2)[unfolded ps(3)[unfolded eval_term.simps(1)] ll] z funs_term_subst 
        have sR1:"sig_F (\<sigma>f z)" unfolding sig_F_def by fast
        from tseq(2)[unfolded pt(3)[unfolded eval_term.simps(1)] ll'[symmetric] ll]  z funs_term_subst 
        have tR1:"sig_F (\<tau>f z)" unfolding sig_F_def by fast
        with list.set_sel(2)[OF useq(1) xtl] Fun(6) term.set(2) have funs: "funs_term (\<tau>l z) \<subseteq> ?FUR" unfolding xeq by auto
        note steps = ps(5)[rule_format, unfolded ll, OF z] pt(5)[rule_format, unfolded ll'[symmetric] ll, OF z]
        from steps vl[OF z] have steps:"(\<sigma>f z, \<sigma>l z) \<in> (rstep UR)\<^sup>*" "(\<tau>f z, \<sigma>l z) \<in> (rstep UR)\<^sup>*" unfolding  par_rsteps_rsteps by auto
        from Fun(1)[OF list.set_sel(2)[OF useq(1) xtl] steps sR1 tR1] funs vl[OF z] have "(\<sigma>f z, \<tau>f z) \<in> (cstep R)\<^sup>\<down>" by auto
      } 
      with all_ctxt_closed_subst_step[OF join_csteps_all_ctxt_closed] have "(l \<cdot> \<sigma>f, l \<cdot> \<tau>f) \<in> (cstep R)\<^sup>\<down>" by blast
      with join_rtrancl_join[OF rtrancl_join_join sseq(1), OF tseq(1)]  ps(3) pt(3) ll ll' have "(s, t) \<in> (cstep R)\<^sup>\<down>" by auto
    } note case2 = this
    from Fun(6) funs_UR F
    have "f \<in> F \<or> (\<exists> \<rho> i. \<rho> \<in> R \<and> i < length (snd \<rho>) \<and> U_fun \<rho> i f)" by auto
    with case1 case2 show "(s, t) \<in> (cstep R)\<^sup>\<down>" by auto
  qed
  from this[OF sseq tseq s t u] show ?thesis by simp
qed

lemma wf_ctrs_non_LV: "wf_ctrs R \<Longrightarrow> non_LV" unfolding non_LV_def
proof
  fix l r
  assume wf:"wf_ctrs R" and lr:"(l,r) \<in> UR"
  from lr[unfolded UR_def] rules_def obtain n \<rho> where n:"\<rho> \<in> R" "(l,r) = (lhs_n \<rho> n, rhs_n \<rho> n)" "n \<le> length (snd \<rho>)" by blast
  obtain l' r' cs where rho:"\<rho> = ((l',r'), cs)" by (cases \<rho>, auto)
  from wf[unfolded wf_ctrs_def, rule_format] n(1)[unfolded rho] have l':"is_Fun l'" by fast
  show "is_Fun l" proof (cases n)
    case 0
    from n(2)[unfolded rho 0 lhs_n.simps] l' show ?thesis by auto
  next
    case (Suc k)
    from n(3) Suc have k:"k < length (snd \<rho>)" by auto
    from  U_cond[OF n(1) k] obtain f where U:"U_fun \<rho> k f" by fast
    from n(2)[unfolded Suc rho lhs_n.simps U[unfolded rho] intp_actxt.simps] show "is_Fun l" by fast
  qed
qed

lemma CR_imp_CR_on: 
  assumes sp:"source_preserving R Z"
    and ll:"left_linear_trs UR"
    and cr:"CR (rstep UR)"
    and wf:"wf_ctrs R"
  shows "CR_on (cstep R) {t. funs_term t \<subseteq> F}"
proof (cases "R = {}")
  case False 
  then obtain \<rho> where "\<rho> \<in> R" by auto
  then obtain l r cs where lr: "((l,r),cs) \<in> R" by (cases \<rho>) auto
  with wf[unfolded wf_ctrs_def] obtain g ls where "l = Fun g ls" by (cases l) auto
  with lr have "g \<in> funs_ctrs R" 
    unfolding funs_ctrs_def funs_crule_def[abs_def] funs_rule_def by force
  with funs_UR have g: "g \<in> funs_trs UR" by simp
  show ?thesis
  proof
    fix u :: "('f,'v) term" 
    fix s t
    assume u:"u \<in> {t. funs_term t \<subseteq> F}"
    assume usc:"(u, s) \<in> (cstep R)\<^sup>*"
    assume utc:"(u, t) \<in> (cstep R)\<^sup>*"
    from u have u:"funs_term u \<subseteq> F" by auto
    from completeness have *:"cstep R \<subseteq> (rstep UR)\<^sup>+" by auto
    from rtrancl_mono[OF *, unfolded trancl_rtrancl_absorb] usc have us:"(u, s) \<in> (rstep UR)\<^sup>*" by blast
    from rtrancl_mono[OF *, unfolded trancl_rtrancl_absorb] utc have ut:"(u, t) \<in> (rstep UR)\<^sup>*" by blast
    from cr[unfolded CR_defs] us ut have "(s, t) \<in> (rstep UR)\<^sup>\<down>" by auto
    then obtain v where v:"(s, v) \<in> (rstep UR)\<^sup>*" "(t, v) \<in> (rstep UR)\<^sup>*" by blast
    from funs_term_funas_term have funs_rule:"\<And> rl.  funs_rule rl = fst ` funas_rule rl" 
      unfolding funs_rule_def funas_rule_def image_Un by metis
    note unf = sig_F_def funs_term_funas_term funs_ctrs_funas_ctrs
    let ?F = "funas_trs UR \<union> F \<times> UNIV"
    let ?h = "\<lambda> f. if f \<in> funs_trs UR \<union> F then f else g"
    let ?ren = "map_funs_term ?h"
    from wf_ctrs_steps_preserves_funs[OF wf u F usc] have sR: "sig_F s" and sR': "funas_term s \<subseteq> ?F" 
      unfolding sig_F_def funs_term_funas_term by auto
    from wf_ctrs_steps_preserves_funs[OF wf u F utc] have tR: "sig_F t" unfolding sig_F_def .
    {
      fix s
      assume "sig_F s"
      then have "?ren s = s" unfolding sig_F_def
        by (intro funs_term_map_funs_term_id, auto)
    } note id = this
    from us v(1) have uv:"(u, v) \<in> (rstep UR)\<^sup>*" by auto
    note map = rtrancl_map[of "rstep UR" ?ren, OF rstep_map_funs_term[of UR ?h]]
    have "(?ren s, ?ren v) \<in> (rstep UR)^*"
      by (rule map[OF _ _ v(1)], auto)
    then have sv: "(s, ?ren v) \<in> (rstep UR)^*" unfolding id[OF sR] .
    have "(?ren t, ?ren v) \<in> (rstep UR)^*"
      by (rule map[OF _ _ v(2)], auto)
    then have tv: "(t, ?ren v) \<in> (rstep UR)^*" unfolding id[OF tR] .
    have "funs_term (?ren v) \<subseteq> funs_trs UR \<union> F"
      using funs_term_map_funs_term[of ?h v] g by auto
    from join_cstep[OF sv tv this sp wf_ctrs_non_LV[OF wf] ll sR tR]
    show "(s, t) \<in> (cstep R)\<^sup>\<down>" .
  qed
qed (simp add: CR_on_def join_def)

end
hide_const si ti

lemma (in unraveling) CR_imp_CR: 
  assumes U_cond: "U_cond U R (funs_ctrs R) Z"   
    and Z:"Z_vars Z" 
    and dctrs:"dctrs R"
    and type3:"type3 R"
    and inf_var: "infinite (UNIV :: 'v set)"
    and inf_fun: "infinite (UNIV :: 'f set)"
    and sp: "source_preserving R Z"
    and ll:"left_linear_trs UR"
    and fin: "finite R"
    and cr:"CR (rstep UR)"
    and wf:"wf_ctrs R"
  shows "CR (cstep R)"
proof 
  fix s t u
  assume ts: "(t, s) \<in> (cstep R)\<^sup>*" and tu: "(t, u) \<in> (cstep R)\<^sup>*"
  define FU where "FU = funs_trs UR"
  from finite_funas_trs[OF finite_UR[OF fin]] have "finite (funs_trs UR)" 
    unfolding funs_trs_funas_trs by auto
  then have FU: "finite FU" unfolding FU_def funs_term_funas_term using finite_funas_term by auto
  from infinite_inj_on_finite_remove_finite[OF inf_fun _ FU, of id UNIV]
  obtain h where inj: "inj (h :: 'f \<Rightarrow> 'f)" and disj: "range h \<inter> FU = {}" by auto
  define g where "g = (\<lambda> f. if f \<in> funs_ctrs R then f else h f)"
  define g' where "g' = (\<lambda> f. if f \<in> funs_ctrs R then f else (the_inv h f))"
  let ?ren = "map_funs_term g"
  let ?ren' = "map_funs_term g'"
  let ?t = "?ren t"
  let ?FR = "funs_ctrs R"
  have g: "\<And> f. f \<in> funs_ctrs R \<Longrightarrow> g f = f" unfolding g_def by auto
  have g': "\<And> f. f \<in> funs_ctrs R \<Longrightarrow> g' f = f" unfolding g'_def by auto
  have ts: "(?ren t, ?ren s) \<in> (cstep R)\<^sup>*" 
    by (rule rtrancl_map[OF cstep_map_funs_term[OF g] ts])
  have tu: "(?ren t, ?ren u) \<in> (cstep R)\<^sup>*" 
    by (rule rtrancl_map[OF cstep_map_funs_term[OF g] tu])
  define F where "F = funs_ctrs R \<union> funs_term ?t"
  let ?cond = "\<lambda> \<rho> n f. (\<forall> \<rho>' n' g b c a.  (\<rho>' \<in> R \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a) \<longrightarrow> f \<noteq> g \<or> (n = n' \<and> (\<forall>i \<le>n. U \<rho> i = U \<rho>' i) \<and> prefix_equivalent \<rho> \<rho>' n))"
  interpret opt: standard_unraveling R U "funs_ctrs R" Z
    by (unfold_locales, rule subset_refl, rule U_cond,
        insert F_def Z dctrs inf_var type3, auto)
  have U_cond: "U_cond U R F Z"
  proof (rule U_condI)
    fix \<rho> n
    assume rho: "\<rho> \<in> R" and n: "n < length (snd \<rho>)"
    from opt.U_cond[OF this] obtain f where U: "U \<rho> n = More f [] \<box> (map Var (Z \<rho> n))" 
      and f: "f \<notin> funs_ctrs R" and cond: "?cond \<rho> n f" by auto
    obtain l r cs where rule: "\<rho> = ((l,r),cs)" by (cases \<rho>, auto)
    have f: "f \<notin> F" 
    proof
      assume "f \<in> F"
      with f have "f \<in> funs_term (?ren t)" unfolding F_def by auto
      with funs_term_map_funs_term[of g] have "f \<in> range g" by auto
      with disj f have "f \<notin> FU" unfolding g_def by auto
      from this[unfolded FU_def opt.funs_UR] rho rule U n show False 
        by auto
    qed
    show "\<exists> f. (U \<rho> n = (More f Nil Hole (map Var (Z \<rho> n)))  \<and> f \<notin> F \<and> ?cond \<rho> n f)"
      by (intro exI conjI, rule U, rule f, rule cond)
  qed
  interpret standard_unraveling R U F Z
    by (unfold_locales, insert U_cond F_def Z dctrs inf_var type3, auto)
  from CR_onD[OF CR_imp_CR_on[OF sp ll cr wf] _ ts tu]
  have "(?ren s, ?ren u) \<in> (cstep R)\<^sup>\<down>" unfolding F_def by auto
  then obtain v where sv: "(?ren s, v) \<in> (cstep R)^*" and uv: "(?ren u, v) \<in> (cstep R)^*" by auto
  have sv: "(?ren' (?ren s), ?ren' v) \<in> (cstep R)\<^sup>*" 
    by (rule rtrancl_map[OF cstep_map_funs_term[OF g'] sv])
  have uv: "(?ren' (?ren u), ?ren' v) \<in> (cstep R)\<^sup>*" 
    by (rule rtrancl_map[OF cstep_map_funs_term[OF g'] uv])
  from sv uv have su: "(?ren' (?ren s), ?ren' (?ren u)) \<in> (cstep R)\<^sup>\<down>" by auto
  {
    fix t :: "('f,'v)term"
    have "?ren' (?ren t) = map_funs_term (g' o g) t" by (rule map_funs_term_comp)
    also have "g' o g = id" 
    proof - 
      {
        fix f
        have "g' (g f) = f"
        proof (cases "f \<in> funs_ctrs R")
          case True
          then show ?thesis unfolding g'_def g_def by auto
        next
          case False
          then have "g f = h f" unfolding g_def by simp
          moreover have "h f \<notin> funs_ctrs R" using disj
            unfolding FU_def funs_UR by auto
          ultimately have "g' (g f) = the_inv h (h f)" unfolding g'_def by auto
          with the_inv_f_f[OF inj] show ?thesis by simp
        qed
      }
      then show ?thesis by auto
    qed
    also have "map_funs_term id t = t" by simp
    finally have "?ren' (?ren t) = t" .
  } note ren_ren = this
  from su 
  show "(s, u) \<in> (cstep R)\<^sup>\<down>" unfolding ren_ren .
qed

end
